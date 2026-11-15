# EXPERIMENT_PROTOCOL — model-comparison strands in stage 01

Status: P3 plan, *proposed*; revised per the Fable audit (`audits/stage-01-fable.md`: C1, C3, M1, M12–M14, m1, m5, m10).
Owner while running: the stage-01 master (Opus). Overrides: `OVERVIEW.md` wins where they differ.
Purpose: an **observational** model comparison that is **part of productive stage-1 work**. For a few stage-1 WPs, the
same WP is implemented in 2 (E1: 3) parallel **strands** by different models. Every strand is audited by Opus, fixed
until it passes, and timed. One strand per WP is merged; the measurements give **priors** for the model assignment of
stages 02–06 (§9). It is not a controlled benchmark: n is tiny (one WP per cell), and §9 says how much the data can bear.

Terms. *Strand* = one model's attempt at one WP, in its own worktree/branch. *Reference strand* = the strand run by the
model that `stage-01.md` assigns to the WP (the production path). *Challenger* = any further strand.
*Cell* = (track, difficulty, model pair). Times are UTC ISO 8601 (`date -u +%FT%TZ`); minutes are wall minutes.

## 1. Strand selection

### 1.1 Selection criteria (applied to `stage-01.md` § Strand candidates)
A WP gets strands only if all hold:
1. **Mechanical acceptance check** exists (`lfile.sh` ok + no `sorry`; `latexmk` exit 0 + label checks; `pytest` pass).
   Without one, quality would rest on the audit alone and the comparison is too noisy.
2. **Self-contained brief**: inputs are stage-tex labels and already-merged files; no decision is delegated.
3. **Off the critical path**, or the challenger is cheap and unblocking rules (§1.5) keep it off the critical path.
4. **Size**: estimated agent wall 10–60 min. Smaller WPs give a timing signal dominated by overhead (≈ audit time);
   larger ones burn the budget and risk the cap.
5. **Coverage**: the selected set covers mechanical / routine / hard, Lean and LaTeX, and at most one code WP. Each
   cheap model appears in ≥ 2 strands (so that one bad run does not decide its fate).

### 1.2 Model pairs (rationale)
| Pair | Question it answers | Where |
|---|---|---|
| haiku vs sonnet | can Haiku take mechanical work (facades, boilerplate, tables)? | mechanical Lean |
| mistral vs haiku | can opencode (free Claude slot) take mechanical housekeeping from Haiku? | mechanical Lean infra, mechanical LaTeX |
| muse vs sonnet | can Muse (+ Lean feedback loop / LaTeX check) replace Sonnet on routine maths and Lean? | routine LaTeX proof write-ups, routine Lean |
| mistral vs sonnet | can Mistral Large 4 replace Sonnet for scripts/tests? | one code WP |
| muse vs opus | does a cheap model with a build loop reach an Opus result on hard Lean, and at what wall? | one hard Lean WP |
| sonnet vs opus | can Sonnet take hard Lean from Opus (largest cost and wall effect in stages 02–06; Fable M14)? | the same hard Lean WP |
P1 data (`plan/staged/METRICS.md`): Muse is fast (≈ 1 min per audit) but unreliable (59 % of findings rejected; wrong
fixes). The hypothesis to test is therefore not "Muse is as good" but "Muse + mechanical checks + Opus audit + fixes is
faster or cheaper end to end". Haiku is known to be weak at conceptual maths: no Haiku strand on a conceptual or hard WP.

### 1.3 Selected strands (from the 10 candidates of `stage-01.md` § Strand candidates)
7 WPs, 15 strands: 7 reference strands (production) and 8 challengers, of which 5 are opencode and 3 are Claude
(E1 sonnet, E5 haiku, E8 sonnet). E7 is dropped (Fable M14(b)). "Cap" follows §4.3. "Prio" is the drop order if the
budget gets tight (8 is dropped first).
| # | WP | track / diff. | ref. (production) | challenger | cell | CP? | est / cap (min) | prio |
|---|---|---|---|---|---|---|---|---|
| E1 | S01-L9 `N_{U_p}` coset decomposition | Lean / hard (Mathlib only) | opus | **sonnet**; **muse** + Lean loop (MAX_IT 10) | Lean-hard sonnet/opus, muse/opus | no; slack 90 (sched. 170) via L10 | 60 / 120 | 1 |
| E2 | S01-L5a Lemma stab (a),(c) | Lean / routine | sonnet | **muse** + Lean loop (MAX_IT 6) | Lean-routine muse/sonnet | no | 40 / 100 | 2 |
| E3 | S01-C1 class sets + mass via PARI | code / routine | sonnet | **mistral** + pytest loop | code-routine mistral/sonnet | no | 60 / 120 | 3 |
| E4 | S01-M2 mass-formula section | LaTeX / routine | sonnet | **muse** + tex loop | LaTeX-routine muse/sonnet | no | 40 / 100 | 4 |
| E5 | S01-L13 targets as `Prop`s | Lean / mechanical | sonnet | **haiku** | Lean-mech haiku/sonnet | **yes, zero slack** (Fable M4); only under the §4.4 rule | 30 / 90 | 5 |
| E6 | S01-X3 vendor Stacks Skolem–Noether | Lean infra / mechanical | haiku | **mistral** (file ops) | mech mistral/haiku | no | 30 / 90 | 6 |
| ~~E7~~ | S01-M0 — **dropped** (Fable M14(b)): runs reference-only at t = 0 | — | — | — | — | — | — | — |
| E8 | S01-M4 `N_{U_p}` section, full proofs | LaTeX / hard | opus | **sonnet** | LaTeX-hard sonnet/opus | no (math track) | 60 / 120 | 8 |
Why these:
- **Coverage**: mechanical (E5, E6), routine (E2–E4), hard (E1, E8); Lean 4 (incl. infra), LaTeX 2, code 1. Muse in 3
  strands (Lean hard, Lean routine, LaTeX routine), Mistral in 2 (code, mechanical infra), Haiku in 2 (one challenger,
  one reference), Sonnet as challenger twice (hard Lean E1, hard LaTeX E8). No pooled cell (E7 dropped).
- **E1 as a three-strand cell** (Fable M14(a)): stages 02–06 are dominated by hard and routine Lean; muse vs opus alone
  would likely end "Opus keeps the class" and say nothing about **Sonnet vs Opus on hard Lean**, the assignment with the
  largest cost and wall effect. The sonnet strand uses the experiment Claude slot while the opus reference runs (stage-01 §9: ≈ 50–110), when that slot is otherwise idle. Mathlib-only, exact statement (`relIndex_K1_succ` with `(hs : 1 ≤ s)`,
  Fable M5), 90 min of dependency-only slack through L10 (170 min in the stage-01 §9 schedule).
- **E1 rather than L5b/L2 for hard Lean**: L9 is pure 2×2 matrix algebra over `ℤ_[p]`/`ℚ_[p]` with a statement fixed
  exactly by `lem:s01-Up`(a),(c). A wrong proof cannot pass, and statement faithfulness is checked by the audit against
  the brief, so the cell is clean. It is the stage's highest-risk item
  (R1), so a second independent attempt has production value too. L5b and L2 would need a **Sonnet** challenger for
  ~60 min, which costs a Claude slot each. They are not selected.
- **E8 is the only expensive challenger** (Sonnet, ~60 min of the experiment Claude slot). It answers the most valuable
  question for stages 02–06, which hold many hard LaTeX WPs: can Sonnet replace Opus there? It is the first strand dropped
  if the slot is contended (prio 8). E8's audit must check the proofs against the C5 numerics and the L9 statement.
- **Not selected**: S01-L5b and S01-L2 (above). S01-M0 (former E7): dropped; it forced M0 behind X5, which delays the
  whole math track once the M sub-coordinator exists (OVERVIEW §8 F3). M0 returns to t = 0, reference only.
- **Critical path**: E1 touches it only through L10 (slack 90 min dependency-only, 170 min in the stage-01 §9 schedule). **E5 lies on a zero-slack path** after
  Fable M4: its deps are now **L1, L7, L3c, L11a** (L11 is split into L11a `Tl Sl Ul diamond` +
  `heckeT_comm_of_disjoint` and L11b `PiEll`, `PiEll_indep`, `rightTranslate`; new WP S01-L17 "corollaries", deps L5a,
  L7, L8b, L10, L11a, L11b). E5 is kept **only** under the §4.4 rule (reference mergeable at mechanical acceptance).
  Under that rule no strand of any WP delays a downstream WP; the Muse strands cost no Claude slot, and all
  experiment lfile checks are limited by the experiment lock (§1.5).
- **Overhead estimate**: Claude-slot overhead ≈ E1 sonnet 60 + E5 haiku 30 + E8 sonnet 60 + 8 challenger audits ×
  ~1.5 rounds × ~7 min ≈ 235 slot-min, plus the **7 reference audits** (≈ 7 × 10–20 min) that are now off the production
  path (§4.4) but use the same slot; spread over the stage on one slot per team (§1.5); stage-01 §9 must show them.
  opencode: ≤ 3 jobs at once. Lean: ≤ 1 experiment lfile at a time.

### 1.4 Experiment setup WP (prerequisite; to be listed in `stage-01.md`)
**S01-X5** | X | write `experiments/briefs/<wp>.md` for E1–E6, E8 (verbatim WP block from `stage-01.md` §2–§7 +
acceptance command), `briefs/audit-template.md`, the two fixed preambles (incl. the read-isolation sentence of §10),
`plan/implementation/tools/exp_lean_loop.sh`, `exp_tex_loop.sh`, `exp_py_loop.sh`, **`plan/implementation/tools/exp_event.sh`** (appends
one event to the single `events.tsv`, §5) and **`exp_prepare_audit.sh`** (patch, stage-tex excerpt, check output,
`shuf` label → audit scratch dir, §2.3), so that each transition is one command for the stage master (≈ 130 events;
Fable m10), the `events.tsv` header; fetch the E6 inputs once into `.exp/inputs/` (§7.1); run the §7.3 pre-flight |
inputs: this file, `stage-01.md` | acceptance: the pre-flight loop passes on a 3-line Lean file, a 1-page tex file and
a 1-test pytest file; `exp_event.sh` appends under `flock` to the absolute path; `shellcheck` clean |
routine | sonnet | 30 min | build 3 min | deps X1a (Lean loop needs the project's `lfile.sh` copy, created by S01-X1a;
tex/pytest loops do not).

### 1.5 Wall-time and resource budget
Limits (`agents/rules/{orchestration,resources,opencode}.md`): ≤ 3 Claude subagents per coordinator (Fable alone in its
team, OVERVIEW §8 F4);
≤ 6 opencode jobs (Lean-building ones count double); Lean: ≤ 2 local slots (`SLOTS=2`, `BUILD_MEMORY_MAX=8G`),
≤ 3 TITAN slots (global master only; TITAN pushes only `titan/<job-id>`).
Rules for experiments:
- **The reference strand is the production run**: it costs nothing extra. Only challengers and their audits are overhead.
- **Claude-slot budget**: at most **1** Claude slot per team that hosts strands (stage master's X/L team: E1, E2, E5,
  E6; M sub-coordinator's team: E4, E8; C/T team: E3; OVERVIEW §8 F3) is used by experiment overhead at any time (a
  Claude challenger, or an Opus audit of any strand). The stage master owns all events, audit preparation and
  decisions. Audits are short (est. 5–10 min) and interleave.
- **opencode budget**: ≤ 3 experiment opencode jobs at once; a Muse Lean loop counts double (so ≤ 1 Lean loop + 1 other).
- **Lean slots**: at most **1 local slot** is used by experiment `lfile.sh` checks at a time (the other stays with
  production). This is enforced by an extra lock: experiment checks run under `flock ~/.cache/gl2tf/exp.lock`, and
  only then call `lfile.sh`/`lbuild.sh`, which take a node-wide slot. Our project's `lbuild.sh` takes lean.lock
  *shared* plus a per-checkout lock after S01-X1b (OVERVIEW §3.4; before X1b an `lbuild` is exclusive), so a
  strand-local `lbuild` of its own targets is allowed, under exp.lock. **Lock acquisition order** (OVERVIEW §3.4,
  Fable C3), everywhere: (1) `exp.lock` (experiment checks only), (2) `lean.lock`, (3) the per-checkout lock (`lbuild`
  exclusive, `lfile` shared), (4) a node slot, (5) the memory wait. Nothing waits for exp.lock while it holds a wrapper
  lock, no script waits for (3) while holding (4), and experiment checks never take lean.lock exclusively after X1b,
  so the locks cannot deadlock (X1b's deadlock test). A strand's acceptance is `lfile.sh` on every target file plus an `#print axioms` check file (E6:
  `lbuild LanglandscapeVendorStacks` + sha256). The OVERVIEW §2 merge gate re-runs the check on the merged result.
- **Worktrees**: ≤ 3 experiment WPs live at once (6 worktrees), counted towards the node's ≤ 12. The reference strand
  of a selected WP runs on `exp/s01-<wp>-<ref>` *instead of* `impl/s01-<wp>` (OVERVIEW alias `S01-<wp>@<model>`). A
  fresh strand worktree is seeded from the `impl` worktree (`cp -a --reflink=auto`, never hard links; OVERVIEW §2); the
  seeding (and under V the first build) is logged as `seed` and excluded from `wall`/`active`. All strands of a WP pay
  it equally. While a Lean experiment runs, the stage master asks the global master to send production full builds
  (`lbuild.sh`, import-dependent builds) to TITAN. Challenger strands never use TITAN (feedback loops need low latency).
- **Critical path**: no strand blocks a downstream WP. The **reference strand is mergeable at mechanical acceptance**
  (§4.4, Fable M12(b)); downstream WPs start then. Strands on zero-slack WPs (E5) are allowed only when the challenger
  is an opencode model (no Claude slot) or Haiku; a Claude challenger (E1 sonnet, E8 sonnet) only on WPs with slack ≥
  its cap.
- **Cap per strand** (§4.3): a challenger that has not passed by its cap is stopped; it never extends the stage.
- **Stage-level stop**: if `/mnt/c` < 50 GB, RAM available < 12 GB, or a production WP waits > 10 min for a slot
  because of experiments, the stage master pauses new challengers (running ones may finish) and notes it in LOG.md.

## 2. Strand life cycle

### 2.1 Setup (stage master; same minute for all strands of a WP)
```bash
base=$(git -C /home/janosch/dev/Langlandscape-wt/impl rev-parse wip-implementation)
for m in <model1> <model2> [<model3>]; do
  git worktree add -b exp/s01-<wp>-$m /home/janosch/dev/Langlandscape-wt/exp-s01-<wp>-$m $base
done
sha256sum plan/implementation/experiments/briefs/<wp>.md     # recorded via exp_event.sh setup (brief_sha)
```
Lean strands: run the project's `link_deps.sh` copy in each strand worktree. It shares the frozen Mathlib farm, with
no `lake update`. Then **seed** `.lake/build` from the `impl` worktree exactly as `new_wp.sh` does (OVERVIEW §2, Fable
M1(a)): `cp -a --reflink=auto` under the `impl` checkout's lock held shared; **never hard links**. If
`DECISION-PV.md` puts lanes (c) in force instead, strand worktrees are still fresh (one per strand) and are seeded the
same way, since a strand cannot reuse a production lane. Deps: E2 needs L1 and the import, **E5 needs L1, L7, L3c,
L11a** (Fable M4), E1 needs Mathlib only. Seeding time is logged as event `seed` and not counted in `wall`/`active`.

### 2.2 Implementation
- Claude strands: one subagent (`model` = haiku/sonnet/opus) with the WP brief and the fixed Claude preamble (incl. the
  read-isolation sentence, §10), cwd = its strand worktree; it commits on its branch and never pushes. Neutral commit messages (`<area>: <summary>`; the standard Co-Authored-By trailer is
  allowed since the auditor never sees commit metadata, §10).
- opencode strands: §7. The wrapper commits the result on the strand branch.
- Implementation ends with the first commit the implementer declares done (`impl_end`) — for opencode, when the
  wrapper loop exits.

### 2.3 Individual Opus audit
Each strand gets its own Opus audit (fresh subagent, never shared between strands of a WP; order of audits randomised
by `shuf`). Input to the auditor, prepared by the stage master in a scratch dir with one command,
`plan/implementation/tools/exp_prepare_audit.sh <strand> <r>` (S01-X5, Fable m10):
`strand-<X>.patch` (= `git diff $base..HEAD` of the strand, no commit metadata), the WP brief, the cited stage-tex
excerpt, and the output of the acceptance check run by the stage master (not by the implementer).
Stages 02–06 (no local Lean): for a Lean strand `check.txt` is made with `EXP_NO_CHECK=1`, and the stage master appends the
strand's TITAN `summary.txt` (job `sNN-<wp>-<a|b>-<n>`) verbatim. Briefs are `experiments/briefs/sNN-<wp>.md`.
**Audit brief template** (`plan/implementation/experiments/briefs/audit-template.md`, filled per strand):
```
You audit strand <X> of work package <WP-id> (track <T>, difficulty <d>). You are not told who wrote it.
Files: strand-<X>.patch (the full change), brief.md (the task), stage-excerpt.tex (the statements), check.txt
(acceptance-check output, run independently). <Round r ≥ 1: prior-findings.md — verify each prior finding as
RESOLVED / OPEN / REGRESSED, then audit the new diff.>
Report ONLY defects. For each: id A<r>.<n>, severity, file:line, problem, required fix. Severities:
  critical = wrong mathematics/statement, acceptance check failing, sorry/axiom/admit, interface name or signature
             different from the brief, edits outside the track directory or of frozen files;
  major    = missing required output, unproven claim in LaTeX, proof that only works by accident (e.g. heartbeats
             raised without reason), deviation from the stage-tex statement that is documented but unjustified;
  minor    = style, naming inside the file, docstring/reference gaps, readability.
Then score with the rubric (integers): correctness 0-4, completeness 0-2, interface fidelity 0-2, maintainability 0-2;
give one line of justification per criterion. End with: VERDICT: PASS | FAIL, and W = 3*crit + 2*major + minor.
Write audit-<X>-r<r>.md. Do not edit any other file. Do not guess the author.
```
**Rubric anchors** (Q = sum, 0–10):
| Criterion | top | middle | 0 |
|---|---|---|---|
| correctness (0–4) | 4: every statement and step checks; matches stage tex exactly | 2: local errors, fixable without redesign | 0: does not build / wrong main statement |
| completeness (0–2) | 2: all outputs of the brief, no `sorry`, all labels | 1: one output missing or stubbed | 0: most missing |
| interface fidelity (0–2) | 2: names, signatures, labels exactly as brief/stage tex | 1: deviations, documented | 0: undocumented deviations |
| maintainability (0–2) | 2: Mathlib/LaTeX/pytest conventions, docstring refs to `mathematics/`, robust proofs | 1: works but brittle/verbose | 0: unreadable / dead code |
Correctness 3 = correct with one non-trivial imprecision; 1 = a wrong statement or proof step that needs redesign.

### 2.4 Pass, fix rounds, escalation ladder
- **Audit passes** iff: acceptance check green (rerun by the stage master on the audited sha) **and** crit = 0 **and**
  major = 0 **and** minor ≤ 3. Remaining minors go to the notes column (debt; fixed at merge if trivial).
- After a failing audit round r with weighted findings **W_r = 3·crit + 2·major + 1·minor** (a red acceptance check
  counts as one critical):
  - **same-model fix** if crit = 0 and W_r ≤ 5 and (r = 0 or W_r < W_{r−1});
  - otherwise **escalate one rung** (the "too many problems" threshold: any critical, or W_r ≥ 6, or no progress).
- **Ladder** (fixes run in the same worktree, on the same branch):
  `muse → sonnet → opus`, `mistral → sonnet → opus`, `haiku → sonnet → opus`, `sonnet → opus`, `opus → (fail)`.
  Fable is not on the ladder (Fable runs alone; global master decision only). Once escalated, the strand stays at
  the higher rung (no de-escalation).
- Each fix round is followed by a **delta audit** (fresh Opus, with `prior-findings.md`), round r+1.
- **Max 3 fix rounds.** A strand that fails audit round 3 or hits its cap is `failed`.
- **E8 override (stages 03/05, OVERVIEW §5.2; replan brief B).** For E8 (S03-M2) and a conditional E8′ the ladder above does
  not apply: the opus reference gets **exactly one planned opus fix round regardless of W0**, then a delta audit; it is
  `failed` if r1 fails (max 1 fix round). The fable challenger has no fix round (r0 fail = `failed`).
- Every escalation is recorded (`escalated=<from>→<to>@r<k>` in LOG.md); the strand's final quality is credited to
  the strand, its cost to all models used (§3).

## 3. Measured quantities (per strand)
| Quantity | Definition | Source |
|---|---|---|
| **`active`** | **`impl_min + audit_min + fix_min`** (implementation + Opus audit + fixes; the decision metric, Fable M12(a)) | events.tsv |
| `wall` | t_pass − t_impl_start (min), incl. audits, fixes and all waiting; for failed strands: t_stop − t_impl_start; reported beside `active` | events.tsv |
| `impl_min`, `audit_min`, `fix_min` | sums per phase | events.tsv |
| `build_min` | total wall inside `lfile.sh`/`lbuild.sh`/`latexmk`/`pytest` calls of the strand | wrapper log |
| `queue_min` | part of build_min spent waiting for locks/slots/memory (lfile slot wait, `MemAvailable` wait) | wrapper log (§10) |
| `rounds` | number of fix rounds (0 = passed first audit) | |
| `escalated` | none, or the rungs with round | |
| `W0`, `crit/maj/min@0` | findings of the first audit (raw quality of the model) | audit r0 |
| `Q0`, `Qf` | rubric score at first audit / at pass | audits |
| `cost_idx` | Σ over phases of weight × agent minutes; weights **muse 1, haiku 2, mistral 3**, sonnet 4, opus 10, fable 20 (nominal relative price per wall minute, strictly following the cost order muse < haiku < mistral < sonnet; Fable m1; audits included) | events |
| `cost_class` | A: cost_idx < 40, B: < 150, C: ≥ 150 | |
| `tokens` | opencode: sum of **all** `step_finish` `.part.tokens` (not only the last; P1 understated) and `.part.cost`; Claude: `total_tokens` from the task notification | logs |
The Opus audit is common to all strands but its rounds differ in number, so audits are included in `active`, `wall` and
`cost_idx`. `wall` additionally contains the wait for the experiment Claude slot (audit queue), for the stage master and
for Lean slots, which differs systematically between reference and challenger; therefore the decision uses `active`,
and `wall` and `queue_min` are reported beside it.

## 4. Decision rule (per WP)
### 4.1 Speed first
Among passing strands, let A be the one with the smallest `active`. Tolerance **τ = max(0.15 · active_A, 5 min)**.
- If every other passing strand has `active > active_A + τ`: **A wins**.
- Otherwise, among the strands within τ of A that are **quality-equivalent** to A, the one with the **lowest
  `cost_idx` wins** (cost_idx within 20 % counts as equal → the faster one wins).
### 4.2 Quality equivalence
Two passing strands are quality-equivalent iff |Qf_A − Qf_B| ≤ 1 **and** correctness scores at pass are equal
**and** neither carries a minor debt that the other's auditor flagged as major in an earlier round and that is
still open. Lean strands additionally need equal outcome of the mechanical check (both ok, no `sorry`, no new axiom:
`#print axioms` of the WP's main declarations shows only the standard three).
### 4.3 Failures, timeouts, ties
- **Cap per strand**: `cap = min(3 · est_wall, est_wall + 60 min)`, at least 30 min, at most 150 min, where est_wall is
  the WP's agent wall from `stage-01.md`. A strand not passing by its cap is stopped: outcome `timeout`.
- Exactly one passing strand → it wins. No passing strand → outcome `all-fail`; the WP reverts to the normal pipeline
  (Opus, starting from the best-scored strand's branch at the stage master's discretion) and the cell is scored
  "no winner".
- Exact tie (within τ, quality-equivalent, cost equal): higher Q0 wins; then the cheaper model in the cost order; then
  the reference strand.
### 4.4 Merge timing
**A reference strand is mergeable at mechanical acceptance** (the OVERVIEW §2 gate), like any `impl/` WP; downstream
WPs start then (Fable M12(b)). Its audit and fix rounds continue on the `exp/` branch for timing and are merged as a
follow-up (`merged-first`, then `follow-up sha=` in LOG.md). A challenger is merged only if it wins (§4.1) and no
downstream WP has built on the reference yet; otherwise LOG.md records `winner=<it>, merged=<ref>` — the experiment
outcome and the merged artefact are kept apart. The stage master never waits for a challenger before merging.

## 5. Logging
Raw events: **exactly one file**, addressed by absolute path in the `impl` worktree,
`EV=/home/janosch/dev/Langlandscape-wt/impl/plan/implementation/experiments/events.tsv` (append-only; Fable M13).
It is appended only under `flock`, through `plan/implementation/tools/exp_event.sh <strand> <event> <k=v;…>`, and
**committed only by the stage master** (on `wip-implementation`). Strand worktrees never write their own copy (it
would pollute `strand-<X>.patch` and trip the "change outside the WP's files" check of §7.2). One line per event:
```bash
# body of exp_event.sh
( flock 8; printf '%s\t%s\t%s\t%s\n' "$(date -u +%FT%TZ)" "$1" "$2" "$3" >> "$EV" ) 8>"$EV.lock"
```
events: `setup` (base, brief_sha), `impl_start`, `impl_end` (sha), `audit_start r=<r>`, `audit_end r=<r>;W=;Q=;c=;M=;m=`,
`fix_start r=<r>;model=`, `fix_end r=<r>;sha=`, `escalate from=;to=;r=`, `seed s=<sec>`, `build s=<sec>;queue=<sec>`, `pass sha=`,
`stop reason=timeout|fail|pause|deadline`, `tokens model=;in=;out=;reasoning=;cache_r=;cache_w=;cost=`.
`stop reason=…` also takes `frozen|violation|contaminated` (§7.2, §10). `deadline` = a reference strand merged into
production at a stage plan's deadline (stage-02 §5, D); metrics frozen there. From stage 02 every TITAN wait of a strand
is logged as `build s=<relay→report sec>;queue=<sec before TITAN start>;job=<job-id>` (agent-active excludes it, §3).
Who: the stage master appends events itself (`exp_event.sh`, one command, no agent needed) at each transition; opencode
wrappers append their own `impl_*`, `build` and `tokens` events through the same script (absolute path, so from a
strand worktree they write the `impl` file, never a strand copy). **LOG.md rows** are rendered from events.tsv by a **Haiku logger**
spawned by the stage master when a WP's decision is made (one row per strand), and once more at stage end; the logger
also writes the ≤ 200 KB loser patches (§6; not for E6). LOG.md format: see the header of `experiments/LOG.md` (exact columns).

**Run metrics for all WPs** (`plan/implementation/runs/sNN.md`, the format OVERVIEW §2 delegates here; stage master,
one row appended at each WP merge, every stage; strands of a selected WP appear here only as their merged strand):
`| WP | model(s) incl. escalations | start | merged | wall min | build min | queue min | audit rounds | final W | sha | notes |`
Times are ISO UTC. This is the data source for re-estimating wall times in §8 rule 5 from stage 2 onwards.

## 6. Merge and discard
- **Winner** (or `merged-first` strand): the stage master merges `exp/s01-<wp>-<model>` into `wip-implementation`
  (`git merge --no-ff`, message `impl: merge S01-<wp> (strand <model>)`; **from stage 02 neutral:** `<area>: merge SNN-<wp>
  (strand <letter>)`, model names only in `LOG.md`; a Lean reference imported into an integration branch before its
  decision is one squashed commit `lean: import SNN-<wp> draft (stacking)`), then removes its worktree.
- **Losers**: (1) record final sha in LOG.md; (2) save `git diff $base..<sha>` to
  `plan/implementation/experiments/patches/<strand>.patch` (committed; it is the durable record, since tags are not
  pushed). **Exception E6** (Fable m5): no loser patch — it would duplicate Apache-licensed files under `plan/` away
  from their LICENSE; record the loser's file list with `git hash-object` blob shas and sha256 in LOG.md instead; (3) `git tag exp-archive/s01-<wp>-<model> <sha>` (local only, **never pushed**; deleted after the stage-06
  merge); (4) `git worktree remove /home/janosch/dev/Langlandscape-wt/exp-s01-<wp>-<model>` right after the decision
  (frees the worktree budget); (5) `git branch -D exp/…` only after `SUMMARY.md` is committed (OVERVIEW §2: experiment
  branches are kept until the stage report is written; the tag keeps the sha reachable afterwards).
- **Where the records live**: the stage master commits `experiments/{events.tsv,LOG.md,patches/,SUMMARY.md}` on
  `wip-implementation`. OVERVIEW §2 grants this exception explicitly for `plan/implementation/experiments/**`
  (together with `runs/sNN.md` and the S01-X5 outputs).
- **No `exp/*` branch or `exp-archive/*` tag is ever pushed** (the repo goes public with its history).
- opencode-pty cleanup per job: PID set before/after, kill the difference only; never kill `opencode serve --service`.
- Lean strand worktrees: remove their `.lake/` build dirs with the worktree (never touch the shared frozen farm).

## 7. opencode strands
### 7.1 Invocation (from `agents/rules/opencode.md`, tested 2026-11-14)
```bash
cd /home/janosch/dev/Langlandscape-wt/exp-s01-<wp>-<model> && before=$(pgrep -f opencode-pty | sort)
timeout 30m opencode run --model openmathos/meta/muse-spark-open --auto --archived \
  --title "exp-s01-<wp>-<model>-i<k>" --format json --file brief.md --file <inputs…> "<prompt>" \
  < /dev/null > /home/janosch/dev/Langlandscape/agents/logs/opencode/exp-s01-<wp>-<model>-i<k>.json 2>&1
after=$(pgrep -f opencode-pty | sort); for p in $(comm -13 <(echo "$before") <(echo "$after")); do kill $p; done
```
(Mistral: `openmathos/mistralai/mistral-large-4-0`.) `--auto` **only** with cwd = the strand's own worktree; brief and
inputs are copied into `.exp/` inside the worktree (git-ignored via `.git/info/exclude`) so relative writes stay there.
**E6 inputs** (Fable M13): the opencode prompt forbids network commands, so S01-X5 (or the stage master) fetches the 8
Stacks blobs and `LICENSE` **once** at rev `c496df0d9beea9deaeabcea8492605f9a0a2313b` into `.exp/inputs/` (raw accept
header `Accept: application/vnd.github.raw`, never base64 pasted by a model) and records their git blob shas
(`git hash-object`) in events.tsv (`setup … inputs=<sha list>`); both E6 strands start from these files.
The prompt ends with the fixed opencode preamble: "Write only <files>. Do not run lake, elan, git, the tools/ wrappers or
any network command. Do not touch any other file. Read nothing outside your worktree except the frozen import, Mathlib
and the brief inputs." This is stricter than OVERVIEW §4 on purpose: the loop wrapper runs all checks, so that timing and slots stay under control.
### 7.2 Verification
The opencode output is never trusted: the mechanical check is run by the wrapper and again by the stage master, and the
**Opus audit is the verifier** (§2.3). After each opencode run and **before any `lfile.sh`** (Fable C1) the wrapper checks
`git status --porcelain` and the pin guard (`sha256sum -c --quiet tools/pins.sha256`, no `.lake/package-overrides.json`;
OVERVIEW §3.4): any change outside the WP's output files is reverted and logged (`violation`); any change to
`lakefile*`, `lake-manifest.json` (incl. its deletion), `lean-toolchain` or the frozen trees (`check_frozen.sh`), or a
failed pin check, **stops the strand** (`stop reason=frozen`) without any Lean process having started, and alerts the
stage master.
### 7.3 Lean feedback loop (`plan/implementation/tools/exp_lean_loop.sh`, built in the experiment-setup WP)
```
exp_lean_loop.sh <worktree> <model> <brief> <target.lean…>   # MAX_IT=6 routine / 10 hard; per-iteration timeout
                                                              # 15m; total ≤ cap − 25m (leaves room for audit + fix)
i=1; errors=none
loop: opencode run (§7.1) with brief + current target files + .exp/errors-<i-1>.txt
      → git status --porcelain + pin check (§7.2); violation: revert, log; frozen/pin failure: stop reason=frozen, exit 2
      → for each target: flock exp.lock; our project's lfile.sh <target> (logs build/queue seconds) ; grep -nE '\bsorry\b|admit|^axiom'
      → ok and no sorry: commit "lean: S01-<wp> iteration <i>", event impl_end, exit 0
      → else: first 150 lines of errors (+ the 20 lines of source around each error) → .exp/errors-<i>.txt; i++
      → i > MAX_IT or no change in the error set for 2 iterations: commit the best iteration (fewest errors), exit 1
```
The prompt of iteration i ≥ 2 says: "The Lean checker reported the errors in errors.txt. Fix them; keep declaration names
and signatures from the brief unchanged." The loop's own exit is `impl_end`; the strand then goes to the Opus audit even
if red (red check = critical, which escalates per §2.4). LaTeX analogue `exp_tex_loop.sh`: `latexmk` + label check,
MAX_IT=4. Code: `pytest -q`, MAX_IT=4.
Pre-flight (experiment-setup WP, before any strand): (a) one trivial Muse Lean loop on a 3-line file, to confirm lfile
works from a strand worktree and that tool runs happen in the worktree under `opencode serve --service` attach mode;
(b) confirm whether bash tool calls run with the client's or the server's environment (if the server's: a `lake` PATH
shim in the client is useless and the post-hoc frozen check of §7.2 is the only guard — acceptable).

## 8. Feedback into stages 02–06
After the last stage-1 strand is decided, a Sonnet writer produces `plan/implementation/experiments/SUMMARY.md`:
per-strand table (from LOG.md), per-cell verdict, and a model-assignment table *class (track, difficulty) → model*
with confidence (§9). Revision rules, applied by the stage-02…06 masters when they finalise their WP tables:
1. **Decided cell**, cheap model won → assign the cheap model to every WP of that class, with the same verifier
   (Opus audit) and the same escalation ladder pre-declared. If the cheap winner needed an escalation, assign
   "cheap + pre-declared one-rung escalation" and budget its wall from the measured strand wall, not from the estimate.
2. **Decided cell**, expensive model won → keep/assign the expensive model; drop the cheap model for that class.
3. **Undecided cell** → keep the `stage-0N.md` assignment.
4. Never extrapolate down in difficulty-to-cheaper or up across tracks: a Muse win on routine Lean says nothing about
   hard or conceptual Lean or about LaTeX. Conceptual WPs keep Opus/Fable irrespective of stage-1 data.
5. Re-estimate wall times: for each class, replace the estimate by the median measured `wall` of winning strands
   (if ≥ 2) or estimate × (measured/estimated ratio of the one strand).
The global master approves the revised assignments; changes are logged in each stage file ("model revised per
experiments/SUMMARY.md, cell <c>").

## 9. Stop criteria
- A cell is **decided** when either (a) ≥ 2 strand comparisons in the cell have the same winner, or (b) one comparison
  has a decisive margin: winner's `active` ≤ 0.67 × loser's `active` **and** winner's Qf ≥ loser's Qf, or the loser failed
  / timed out while the winner passed without escalation. Anything else is *undecided*; one comparison is weak evidence
  and SUMMARY.md says so.
- **Every verdict from one comparison is a prior**, to be revised from the `runs/sNN.md` data of stages 02–06 (Fable
  M14(d)), **not a decision**; SUMMARY.md and §8 assignments carry it as such.
- Experimenting stops at the end of stage 1. **After stage 1 no duplicate strands**, unless all of:
  (i) the cell is undecided or contradictory, **and** it covers ≥ 20 % of the estimated agent wall of the remaining
  stages, or a cheap model would replace an expensive one on ≥ 3 WPs; (ii) the WP meets §1.1; (iii) it fits the §1.5
  budget without lengthening the critical path; (iv) the global master approves, with the justification written in LOG.md.
- Mid-stage-1 abort: if two consecutive challengers of the same model end `frozen`/`violation`, that model's remaining
  strands are cancelled (cell scored "failed: unsafe").

## 10. Fairness and confounds
- **Same brief**: byte-identical `experiments/briefs/<wp>.md` for all strands (sha256 recorded at setup). Only the
  model-specific preamble differs (Claude agent instructions vs. opencode prompt line of §7.1); both preambles are
  fixed texts committed next to the briefs.
- **Read isolation** (Fable M13): sibling worktree paths are predictable and all `exp/*` branches are in the shared
  repository; a merged reference is visible in `wip-implementation`. Both fixed preambles contain: "Read nothing outside
  your worktree except the frozen import, Mathlib and the brief inputs; no `git` command other than `add`/`commit`."
  **Post-hoc check** by the stage master at `impl_end` and after each fix round: grep the opencode JSON tool events /
  the agent transcript for sibling paths (`Langlandscape-wt/exp-`, `Langlandscape-wt/impl`, other strands' branch
  names) and `git (show|log|branch|worktree|checkout|diff)`; a hit marks the strand `contaminated`
  (`stop reason=contaminated`) and removes it from the decision (it may still be merged if it is the reference).
- **Same inputs, same start**: all strands branch from the same `wip-implementation` sha; impl_start of all strands
  within **5 min** of each other (offset recorded; > 5 min = note "late start").
- **Build contention**: `build_min` and `queue_min` are recorded separately; our project's `lfile.sh`/`lbuild.sh` copies
  print `slot acquired <ts>` / `mem ok <ts>` to stderr so the wrapper can split queue wait from compile time. The decision
  uses `active` (§3), which excludes waits between phases; a strand whose `queue_min` (inside its phases) exceeds the
  other's by more than τ is flagged `contended` and its `active − queue_min` is reported too; for a `contended`
  decision the stage master may rule with the queue-corrected value (documented).
- **Audit blinding**: the auditor sees `strand-<X>.patch` (a letter, not a model), no commit metadata, no branch names, no
  logs; the letter→strand map is held in events.tsv (`setup … label=X`). Auditor prompts never mention models.
  Residual confounds (written into SUMMARY.md): style fingerprints; Opus auditing an Opus strand (self-preference);
  different interaction modes (agent with tools vs. opencode + external check loop) — the latter is intended, since
  we compare the pipelines we would actually run.
- **Same verifier strength**: every audit is a fresh Opus at the same effort; the same audit template for all strands.
- **Order effects**: audits of strands of one WP are started in random order; the second audit never sees the first.

## 11. Open questions
- O1 *(resolved: stage-01.md lists S01-X5 and the `exp/` branches; its §8/§9 confirm the slacks.)* `stage-01.md` must list S01-X5 (§1.4) and the `exp/` branches of E1–E6, E8 in place of their `impl/` branches.
  Its §9 must confirm L10's slack ≥ 60 min (E1; three strands now) and place the 7 reference audits (§1.3). (E7 dropped.)
- O2 *(resolved in OVERVIEW §2.)* OVERVIEW §2: extend the plan-file exception to `plan/implementation/experiments/**` (§6).
- O3 The pre-flight (§7.3) must settle whether `--auto` tool calls under `opencode serve --service` run in the client
  cwd/env. If they do not, Lean strands need `--standalone` (untested) or the post-hoc frozen check is the only guard.
- O4 The cost weights (§3) are nominal. If openmathos reports real `.part.cost`, SUMMARY.md also reports real cost.
- O5 *(resolved: stage-01 §9 keeps L9 off the zero-slack path, schedule slack ≈ 170 min, dependency-only 90 min.)* Stage-01 §9 is not written yet. If it moves S01-L9 onto a zero-slack path, E1 is still allowed (opencode
  challenger, §1.5), but L10 must then start on the Opus strand without waiting.
