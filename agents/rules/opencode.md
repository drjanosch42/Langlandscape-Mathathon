# Rule: launching opencode

**Not used as implementers (stage-1 study, OVERVIEW §5.1); Q&A only.**

opencode (v2.3.0 on Fabian's node) provides two models we use at the **bottom of the agent tree**:

| Model | opencode id | Default use |
|---|---|---|
| Muse Spark Open | `openmathos/meta/muse-spark-open` | mathematical leaf tasks: lemma/proof drafts, Lean tactic attempts, case checks |
| Mistral Large 4 | `openmathos/mistralai/mistral-large-4-0` | code/text leaf tasks: Python/CAS scripts, LaTeX boilerplate, summaries, translations |

(Initial assignment — recalibrate from experience; record findings under *Calibration* below.
Verify ids with `opencode models | grep -E 'muse|mistral'`.)

## When to use
- Only for **well-specified, self-contained** tasks with a mechanically checkable result
  (compiles, test passes, output matches). Never for decisions, audits or merges.
- A Claude agent (usually the worker that launched it) **always verifies** the output.
- Good fit: fan-out (try N tactic variants / N parameter sets), first drafts, bulk edits.

## How to launch (non-interactive)
```bash
opencode run --model openmathos/meta/muse-spark-open \
  --auto --archived --title "<task-id>" --format json \
  --file <context-file> "<self-contained prompt>" \
  < /dev/null > agents/logs/opencode/<task-id>.json 2>&1
```
- **Always `< /dev/null`** (avoids hanging on stdin). `--standalone` was **not** needed (see below).
- `--auto` is only needed when the model must write files / run tools; plain Q&A does not need it.
- `--auto` auto-approves tool permissions: therefore run file-writing tasks in an **isolated
  git worktree** (`--worktree <task-id>` or `git worktree add`), never in the master's checkout.
- `--archived` keeps scripted sessions out of the session list; `--title` = task id.
- The prompt must contain: goal, exact files, acceptance check, output location, "do not touch
  anything else". Attach context with `--file` instead of pasting.
- Always wrap with `timeout` (default `timeout 30m`); kill stray processes after completion
  (`pkill -f "opencode run.*<task-id>"`), remove worktrees after harvesting.
- Logs in `agents/logs/opencode/` are not committed (gitignored).

## Tested invocation (2026-11-14)
Tested on Fabian's node, opencode v2.3.0, with the background `opencode serve --service` running
(`opencode run` attaches to it by default; **no `--standalone` needed, service is not a problem**).
Run from a scratch dir, always `timeout N ... < /dev/null`:
```bash
cd /tmp/<scratch> && timeout 300 opencode run --model openmathos/meta/muse-spark-open \
  --archived --title t1 "What is 17*23? Answer with the number only." < /dev/null     # -> 391, 2.6 s
timeout 300 opencode run --model openmathos/meta/muse-spark-open --archived --title t3 --auto \
  --file claim.txt "Audit the attached claim; write the audit to audit.md in the cwd. Touch nothing else." < /dev/null
```
- Plain stdout: ANSI reset + `> build · <model>` header line, then the answer (strip the first 2 lines when parsing).
- `--format json`: JSON lines `step_start`, `text` (`.part.text`), `step_finish` (`.part.tokens`
  = `{input,output,reasoning,cache:{read,write}}`, `.part.cost`); tool use adds further event types. Extract:
  `jq -rs '[.[]|select(.type=="text")|.part.text]|join("")' out.json` and
  `jq -c 'select(.type=="step_finish")|.part.tokens' out.json`.
- Timings: trivial prompt 2.6 s (Muse), 3.2 s (Mistral Large 4, also correct); file attach + `--auto` audit
  writing audit.md: 27 s. Peak RSS of the `opencode run` client ≈ 87 MB (server separately ≈ 310 MB).
- `--auto` + write worked: only `audit.md` created in cwd, nothing else touched. Quality: correct verdict and
  counterexample ((-1,-1/Q) ramified at {2,∞}), but with a mathematical slip (claimed (-1,5/Q) ramified at {5,∞}; it is
  actually split everywhere) — hence **always verify**.
- Cleanup: tool-using runs spawn an `opencode-pty daemon` process that outlives the run; kill it
  by PID, and only the ones your job started: record `pgrep -f opencode-pty` before and after the job and
  kill the difference. Never use a blanket `pkill`, because parallel jobs share the machine. **Never kill `opencode serve --service`.**
- Pitfalls: output is one-shot (no streaming progress); the model emits much reasoning (133 tokens for a
  trivial answer); run in a scratch dir/worktree since `--auto` writes relative to cwd.

## Node specs and parallelism
Lean/Mathlib builds dominate memory (~4–8 GB per parallel `lake build`). Limit concurrent
opencode jobs per node by the table below; when a task builds Lean, count it double.

| Node | CPU | RAM | OS | Max parallel opencode jobs |
|---|---|---|---|---|
| fabian | 32 threads | 82 GB | Linux (WSL2) | 6 |
| abhijit | _fill in_ | _fill in_ | _fill in_ | default rule: `min(6, cores/4, RAM_GB/12)` |

Each node's master detects its specs at session start (`nproc`, `free -g`) and updates this
table if it changed (commit on `main`).

## Calibration
<!-- append: date, model, task type, success/failure, remark -->

## Calibration log
- 2026-11-14 muse-spark-open, toy audit (flawed quaternion claim): correct verdict and counterexample, but one false side claim ((-1,5/Q) is split, not ramified at {5,∞}). Audit output must be verified.
