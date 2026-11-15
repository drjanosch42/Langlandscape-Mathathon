# Brief: re-planning of stages 02–06 after stage 1 (all drafters, auditors, revisers)

Worktree `/home/janosch/dev/Langlandscape-wt/plan`, branch `wip-plan` (= main 7ce2a3e, includes all of stage 1).
Commit only your own files: `git add <files> && git commit -m "plan: ..." -- <files>`. If `index.lock` exists, wait
10 s and retry, because other agents commit in the same worktree. **Never push.** Do not edit `plan/seed/`, `plan/staged/`,
`lean/`, `mathematics/`, `code/`, `talk/` or `agents/`. Do not build Lean (read-only). `plan/implementation/briefs/common.md`
still applies; **this brief overrides it where they differ**.

## Read (all agents)
- `CLAUDE.md`; `agents/rules/{resources,orchestration,lean,frozen,mathematics,code,talk,messages,git}.md`.
- `plan/implementation/OVERVIEW.md` (the current one; it is being revised in parallel — the conventions below are binding
  and will appear in the new OVERVIEW under the section names given here).
- `plan/implementation/experiments/SUMMARY.md` (+ `LOG.md`), `plan/implementation/runs/s01.md`,
  `plan/implementation/outbox/20261114T174651Z_milestone-closure-s01.md`, examples of TITAN job specs in
  `plan/implementation/outbox/*titan-s01-*.md`, `lean/Langlandscape/tools/titan_batch.sh`, `agents/status/master_log.md`
  (lines 40–100: stage-1 timeline and incidents), `agents/status/abhijit_candidates.md`.
- The current Lean project `lean/Langlandscape/` (what exists after stage 1: `Langlandscape/**`, `HYPOTHESES.md`,
  `SORRIES.md`, `Audit/`, `audits/2026-11-14_s01.md`); the stage-1 chapter `mathematics/chapters/s01*`.
- Your stage: `plan/implementation/stage-NN.md` (the coarse plan to revise), `plan/staged/stage-NN-*.tex`,
  `plan/implementation/audits/stage-NN-{muse,resolution}.md`, `plan/staged/SPLIT.md`.
- Literature (read-only; never copy text): `/home/janosch/dev/Langlandscape/literature/`.

## Binding conventions (new OVERVIEW sections in brackets)

### A. Model assignment [OVERVIEW §5]
| class | model | fix round |
|---|---|---|
| mechanical copy / vendoring (Lean or other) | haiku | ladder haiku → sonnet |
| Lean mechanical-with-meaning (new Props/defs against existing API, incl. stacked on unverified drafts), Lean routine | sonnet | one budgeted opus fix round (~2–5 min) |
| code routine (pytest loop, PARI), LaTeX routine | sonnet | one budgeted opus fix round (~2 min; expect 6–8 minors at r0) |
| Lean hard, LaTeX hard (full proofs) | opus | one planned opus fix round |
| conceptual (design, interfaces, normalisations, audits of concept) | opus or fable | — |
| audits | Lean audit `agents/roles/lean_audit.md` and chapter audit `agents/roles/mathematics_chapter_audit.md` = **fable**, run in parallel; WP-level audits = opus (alternate with fable for adversarial audits) |
**muse and mistral are dropped as implementers** (no opencode WPs). Every WP row names model + fix-round budget.

### B. Experiment strands [OVERVIEW §5.2, EXPERIMENT_PROTOCOL]
Only for cells that SUMMARY leaves undecided or confounded; **at most 1–2 strands per stage**. Allocation (binding):
- **S02**: E1 Lean-hard (opus vs sonnet, both under the same batched-TITAN regime: each strand gets one TITAN slot per
  integration round, so latency is equal; record agent-active minutes separately from TITAN wait) on one hard S02 L WP;
  E4 LaTeX-routine (sonnet + budgeted opus fix vs opus single-shot) on one routine S02 M WP.
- **S03**: E8 LaTeX-hard (opus + planned opus fix round vs fable single-shot) on one hard S03 M WP.
- **S04–S06**: none planned; each of these stages names **one conditional strand** ("only if the S02/S03 result leaves
  cell X undecided; global master approves per EXPERIMENT_PROTOCOL §9").
Strand WPs always run locally (not remote-eligible) so that measurement is comparable. **No fix hints in relays**: the
stage master and global master relay TITAN results to strands verbatim (errors only), never with suggestions.

### C. Remote-only Lean workflow [OVERVIEW §4.3 "TITAN"]
- No local Lean. Every Lean check runs on TITAN (≤ 3 concurrent builds) via the **file outbox**: the stage master writes
  `plan/implementation/outbox/<UTC>_titan-sNN-<job>-<n>.md` and commits it; the global master pushes the branch and relays.
- Writers **stack on unverified drafts**: a WP whose upstream is drafted but not yet green starts immediately against
  the draft's declared signatures; the stage master merges drafts into an integration branch `impl/sNN-int<k>` and sends
  **one integration build per round** (`int1`, `int2a`, `int2b`, …; letter = re-run of the same round after fixes).
  Expect 3–6 rounds per stage; one round trip ≈ 3–8 min (stage 1: int1 → int2f in ~25 min).
- Job-spec file format = `tools/titan_batch.sh` spec: lines `<WP-id> <file.lean> [...]` and `AXIOMS <.titan/x.lean>`;
  the outbox file gives: job id, priority, branch + full sha, the command (`bash tools/titan_batch.sh .titan/spec-<job>.txt`),
  what to report (summary.txt in full; `error:` lines ≤ 200 per failing WP; FAIL lines of check_wp; non-standard axiom lines),
  and the result branch `titan/<job-id>`. Experiment strands: neutral ref `titan-in/<job>`, deleted after fetch, no model names.
- `.titan/` spec and axiom scratch files are **not** committed on WP branches (stage-1 finding A0.1); they live only on the
  integration branch.

### D. Stage-1 lessons (each must appear as concrete gate/step in every stage plan) [OVERVIEW §9]
1. **Early full gates**: run the full stage gate (all targets + PrintAxioms + forbidden-token grep + check_frozen) as soon as
   the core Lean WPs are green (≈ mid-stage), not only at the end; final gate from scratch.
2. **Axiom scratch files**: fully qualified names (`Langlandscape.…`), every needed import listed, and the wrapped-line join
   (`#print axioms` output wraps; count non-standard after joining, as `titan_batch.sh` does). Generate the list mechanically
   from the declared outputs; a haiku WP may do it.
3. **Docstring gates**: every public declaration has a docstring; main theorems reference their `mathematics/` label
   (`check_wp.sh` docstring check must pass in the integration round, not be fixed by the stage master afterwards).
4. **Stale strand bases**: when an upstream fix lands, rebase open strands/WP branches onto the fixed integration tree before
   their next TITAN round.
5. **Per-coordinator outbox, never SendMessage-only**: every job spec, status and closure goes to
   `plan/implementation/outbox/` (committed); SendMessage is only a notification.
6. **No fix hints in experiment relays** (see B).

### E. Remote-eligible WPs (possible node "Abhijit") [OVERVIEW §6.1]
Tag `remote-eligible` on: all M (maths chapter) WPs, literature WPs, and second-reader/review WPs of stages 02–06 — except
experiment-strand WPs and chapter audits by Fable. Conditions: self-contained; inputs are only the stage tex + merged
`mathematics/` + `literature/`; **new files only** (`mathematics/chapters/sNN/*.tex`, `mathematics/bib/sNN.bib`,
`mathematics/standalone-sNN.tex`, `mathematics/chapters/sNN/NOTES.md`, `mathematics/litnotes/*`); its own branch
`abhijit/<wp-id-lowercase>` off `wip-implementation`; aggregator lines (`main.tex` `\input`, `references.bib`) are returned
in the WP report and applied by the stage master. Acceptance: `latexmk -pdf standalone-sNN.tex` exit 0, no undefined
refs/cites. Each stage plan has a table "Remote-eligible WPs" and states: **the stage is launchable without Abhijit**; the
default executor is local, and the global master decides per WP at stage launch.

### F. Wall-time calibration [OVERVIEW §4.4]
Stage 1 took 2.2 h against an 8.8 h plan (factor ≈ 0.25). Calibrated values (runs/s01.md): local short WPs 3–17 min;
Lean WPs under TITAN 33–80 min wall (dominated by integration rounds; agent-active 10–20 min); a TITAN round ≈ 3–8 min;
M track 52 min for 10 WPs; C/T 28 min; Fable Lean audit ~6 min; audit fix WPs 2–13 min; final gate ~5 min.
Estimate each WP with these, give the critical path as summed wall, and give a stage wall estimate with a ±range.

## Stage-plan file structure (every stage-NN.md)
0. Scope, fixed decisions, what stage 1 delivered that this stage uses (exact Lean declaration names/files where needed),
   carried-over items (from closure "open issues" and runs/s01.md coverage updates).
1. WP table, schema of common.md plus columns `model (+fix)`, `remote-eligible`, `TITAN round`.
2. DAG: edge list + Mermaid + waves + critical path with summed wall + stage wall estimate.
3. TITAN plan: integration rounds (which WPs in which `int<k>`), early full gate, final gate, axiom scratch file WP.
4. Gates and audits: per-WP acceptance, early gate, Fable Lean audit ∥ Fable chapter audit, fix WPs, final from-scratch gate,
   milestone closure.
5. Experiment strands (per B).
6. Remote-eligible WPs (per E).
7. Risks, open questions for Fabian.
Stage 02 must be **ready to launch**: an X1 kickoff WP (worktrees, `impl/s02-*` branches, X1 stubs/aggregators, HYPOTHESES/
SORRIES rows, the int1 spec file), every WP with concrete files and declaration names, the first two TITAN batches written out
as spec lines. Stages 03–06: same structure, WPs concrete, TITAN rounds sketched (they get a final pass before launch).
