<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

All times PST (UTC−8). Source logs: all machines on Berlin time (CET, UTC+1), report sources in UTC; converted.

# Model-vs-task study

Goal: for each task class (track × difficulty), find the cheapest model that does not lengthen the stage's wall time.
Protocol: `plan/implementation/EXPERIMENT_PROTOCOL.md` (PROT). Data: `…-wt/impl/plan/implementation/experiments/{LOG.md,
SUMMARY.md,events.tsv}`. Resulting policy: [`agents/rules/model-selection.md`](../../agents/rules/model-selection.md).

## 1. Design
- **Strands.** For a selected WP, two (stage 1: up to three) models implement the same brief at the same minute, from the same
  base sha, each in its own worktree on `exp/sNN-<wp>-<model>` (PROT §2.1). Everything a build node or auditor sees is
  **neutral** (`a`/`b` job ids, `titan-in/*` refs, no model names); model names appear only in LOG.md.
- **Blind audits.** Each strand gets its own fresh auditor (order randomised), fed only the diff without commit metadata, the
  brief, the stage-tex excerpt and an independently run acceptance check. The auditor lists defects (critical/major/minor) and
  scores a rubric Q = correctness 0–4 + completeness 0–2 + interface fidelity 0–2 + maintainability 0–2 (PROT §2.3).
- **Pass** = acceptance green, 0 critical, 0 major, ≤ 3 minor. Weighted findings **W = 3·crit + 2·maj + min**. A failing strand
  gets a same-model fix if W ≤ 5 and improving, otherwise escalates one rung (haiku/muse/mistral → sonnet → opus → fail);
  at most 3 fix rounds (PROT §2.4). Stage 3 (E8) override: exactly one planned opus fix round for the opus reference, none for
  the fable challenger.
- **Scoring** (PROT §3): `active` = implementation + audit + fix minutes (decision metric; build waits excluded);
  `wall` reported beside it; `cost_idx` = Σ weight × agent minutes with weights muse 1, haiku 2, mistral 3, sonnet 4, opus 10,
  fable 20; classes A < 40, B < 150, C ≥ 150.
- **Decision rule** (PROT §4): speed first: the passing strand with the smallest `active` wins unless another passing strand is
  within **τ = max(15 % of best active, 5 min)** and quality-equivalent (|ΔQf| ≤ 1, equal correctness); then lower `cost_idx`
  wins. **Tie rule:** higher Q0, then the cheaper model, then the reference strand. Exactly one passing strand wins; none →
  `all-fail`. A reference strand may be merged at mechanical acceptance (`merged-first`) so downstream work is not blocked.
- **Budget:** at most 1–2 strands per stage after stage 1, only for undecided or confounded cells (OVERVIEW §5.2).

## 2. Results per cell
| Cell | Stage / WP | Models | Result (active min, W0, Q) | Verdict |
|---|---|---|---|---|
| Lean mechanical (vendoring) | S01 E6 / X3 | haiku vs mistral | haiku 4.8, W 4, Q 10; mistral 9.2, W 2, Q 10 (both pass) | **haiku** (cheaper, faster) |
| Lean routine | S01 E2 / L5a | sonnet vs muse | sonnet 4.0, W 3, Q 9; muse 13.0, W 10 (2 crit), Q 3, failed | **sonnet** |
| Lean hard | S01 E1 / L9 | opus vs sonnet (muse cancelled) | opus ≈ 16 agent min, 1 TITAN round, pass; sonnet ≈ 12, 4 TITAN rounds, 4 minors, no pass | opus, **confounded** (remote latency penalises iterative models; opus audited opus) |
| Lean hard | S02 E1 / L1 | opus vs sonnet | sonnet 26.6, W 5, Qf 9; opus 36.2, W 6, Qf 10; both pass after 1 round | sonnet by τ (merged: opus, since downstream had built on it); challenger off-regime in round 1 |
| Lean mechanical-with-meaning (stacked) | S01 E5 / L13 | sonnet vs haiku | sonnet W 1, Q 10, pass; haiku W 5 (major signature deviation), Q 8 | **sonnet** (agent time not recorded) |
| code routine | S01 E3 / C1 | sonnet vs mistral | sonnet 10.8 (1 opus fix); mistral 46.0, opencode timed out twice, passed only after sonnet → opus | **sonnet** |
| LaTeX routine | S01 E4 / M2 | sonnet vs muse | sonnet 7.7 (1 opus fix), Q 10; muse W 19 (2 crit, 5 maj), failed | sonnet |
| LaTeX routine | S02 E4 / M1 | sonnet + opus fix vs opus single shot | sonnet 8.05, pass at r1; opus 7.8, failed on minor 6 > 3 | **sonnet + opus fix** |
| LaTeX hard | S01 E8 / M4 | opus vs sonnet | opus 14.3, W 6, failed at top rung; sonnet W 10, escalated, no result logged | all-fail (proposed) |
| LaTeX hard | S03 E8 / M2 | opus + planned fix vs fable single shot | opus 22.2, pass at r1, Qf 9; fable 20.1, W 4, Q0 10, failed on minor 4 > 3 | **opus + fix** (opus audited opus) |
| Lean hard | S04 E1′ / L6 | sonnet (+ opus fix) vs opus, both strands on TITAN, pair jobs | opus: active ~26.3 min, r0 W 4 (protocol FAIL on minors 4 > 3), after fix W 2, Q 9, cost 313/C; sonnet: active ~18.1, r0 W 6, opus fix, W 3, Q 10, cost 145/B; both passed after one fix | **sonnet + 1 opus fix** (prior); the opus head was merged first (production green 14:14 PST) so merged ≠ winner; confounds: production rescue writer loaded the queue, n = 1, no tokens (`runs/s04.md`) |
| Lean mechanical-with-meaning | S05 E5′ / L4 (non-vacuity instances, CONCEPTD, same seed) | sonnet + 1 opus fix vs opus + same-model fix | sonnet 16.8 min, blind Fable W 3 (0/0/3), Q 6; opus 27.5, W 2 (0/0/2), Q 7; τ = 5 | **sonnet + 1 opus fix**, confirms the stage-1 prior; merged = winner (`model-selection.md` §2, `runs/s05.md` lesson 4) |
| Muse as auditor | P1, P3 | Muse Spark Open | P1: 7/70 findings confirmed, 22 partial, 41 rejected; P3: 15/89 confirmed, 43 partial, 31 rejected; 12 "critical" in P3, 0 after verification | first-pass checklist only |

Sources: LOG.md, SUMMARY.md, `plan/staged/METRICS.md`, `plan/implementation/METRICS.md`. All verdicts are **priors** from 1–2
comparisons per cell.

## 3. Resulting policy (summary of `agents/rules/model-selection.md` §1)
| Task class | Model | Fix-round budget |
|---|---|---|
| Lean mechanical copy/vendoring | haiku | none; red → sonnet |
| Lean routine, mechanical-with-meaning | sonnet | 1 opus fix |
| Lean hard on the critical path / remote-only | opus (right first time) | 1 planned opus fix |
| Lean hard off the critical path, equal regime | sonnet first, opus fix | 1 opus fix |
| LaTeX / code routine | sonnet | 1 opus fix (expect 6–8 minors at r0) |
| LaTeX hard | opus | 1 planned opus fix, always |
| conceptual / delicate | opus or fable | — |
| Lean and chapter audits | fable, in parallel | — |
| coordination | opus | — |
| logging, polling, mechanical edits | haiku | — |
| opencode (Muse, Mistral) | not as implementers; Q&A and first-pass checks behind a verifier | — |

Observations that shaped it: remote-only Lean penalises iterative models, so batched rounds and right-first-time models on the
critical path matter; a stronger single shot does not remove the fix round (opus on routine LaTeX, fable on hard LaTeX both
failed on the minor count alone); relays to strands must carry no fix hints.

## 3a. Stages 4–6 additions
- Two further cells were decided as priors (S04 E1′, S05 E5′); both favour **Sonnet first + one Opus fix** over Opus single-handed when the build
  regime is equal. Strand branches `exp/s04-l6-{opus,sonnet}` and `exp/s05-l4-{a,b}` exist locally (25 `exp/*` branches in all; never pushed);
  the LOG has 35 table rows.
- The experiment budget was cut to 1–2 strands per stage after stage 1; no `exp/s06-*` branch exists and the HACS lanes had no strands because of the deadline: Fabian's directive of 2026-11-14 16:45 PST (`agents/status/STATE.md`, "Decisions by Fabian") put
  implementation progress first, and the model policy for those task cells had already been decided by S04-E1′ and S05-E5′
  (`agents/rules/model-selection.md`), so further experiments had no decision value.
- Practice evidence, not strands: **Fable** found what Opus audits missed: the vacuous `Hyp.RamNrdSurj` instance (S02), `Hyp.FreeRankTwo` being
  equivalent to the conclusion of its use (S06 part 2), wrong "non-vacuity reasons", and the M > 1 error in the S06 chapter (part 2 FAIL); it also
  corrected a second reader's error. Opus WP audits of Opus work carry a self-preference confound (named in LOG).
- **Opus** stayed coordinator, hard-writer and rescue-writer; **Sonnet** wrote most Lean/LaTeX/code drafts; **Haiku** logged and generated axiom lists;
  Muse/Mistral stayed Q&A only. In HACS Lane B 3 of 4 implementers were Opus and the two fresh reviewers Opus; fix rounds again followed the
  "r0 fails, planned fix passes" pattern (all Lane A WPs except HJ-A2 failed audit r0 and passed after fixes).
- The model-policy file `agents/rules/model-selection.md` was last updated 2026-11-14 16:33 PST (stage 5). Token/cost totals per model: not recorded in the repo.

## 4. Confounds (SUMMARY §4, LOG deviations)
Remote build latency after local Lean was switched off; strands stacked on unverified upstream drafts (S01 E5: 3 of 4 rounds
blocked upstream); Opus auditing Opus strands; S02 E1 challenger sent alone in round 1; missing agent times (E5) and some
missing fix/audit events (S01 E8 sonnet); one audit per strand; n = 1–2 per cell.
