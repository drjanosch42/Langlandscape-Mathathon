# Model selection (consolidated policy + evidence)

Status: **current as of 2026-11-14 (after stages 1–3)**. Every verdict below is a *prior* from 1–2 comparisons per cell
(EXPERIMENT_PROTOCOL §9); the global master approves changes. Supersedes nothing silently: where it differs from
OVERVIEW §5.1 (`/home/janosch/dev/Langlandscape-wt/impl/plan/implementation/OVERVIEW.md`) the difference is marked **Δ**.
Sources: `…/plan/implementation/experiments/{LOG.md,SUMMARY.md,events.tsv}` (cited as LOG/SUMMARY, row = stage-WP strand),
`EXPERIMENT_PROTOCOL.md` (PROT), `runs/s0N.md`, `outbox/*milestone-closure*`, `plan/{staged,implementation}/METRICS.md`.

## 1. Decision table (apply now)
Fix-round budget = one planned fix round run *before* declaring the WP failed; a fix that does not reach green escalates one rung
(haiku→sonnet→opus; opus → stage master: split / re-scope / fable). Fable is never on a ladder (global-master decision).

| Task class | Model | Fix-round budget | Escalate when |
|---|---|---|---|
| Lean mechanical (copy/vendoring, no new statements) | haiku | none | any red check → sonnet |
| Lean mechanical-with-meaning (new Props/defs vs existing API, stacked on unverified drafts) | sonnet | 1 opus fix (~2–5 min) | crit, or W ≥ 6, or no progress → opus. Haiku must not write `.lean` beyond copying; it returns text, a sonnet/master writes files |
| Lean routine (local API, short statements) | sonnet | 1 opus fix | as above |
| Lean hard, critical path / remote-only Lean | opus (right first time, 1 remote round) | 1 planned opus fix | still red after fix → stage master (split / fable) |
| **Δ** Lean hard, off critical path, equal build regime | sonnet first, opus fix | 1 opus fix | red after fix → opus rewrite. Decided (prior) by s04-E1′/L6: sonnet+1 opus fix won on time and cost (see §2) |
| LaTeX routine | sonnet | 1 opus fix (~1.5–2 min; expect 6–8 minors at r0) | crit / W ≥ 6 → opus. Never opus single shot (fails minor > 3) |
| LaTeX hard (full proofs) | opus | **1 planned opus fix, always** (PROT E8 override) | still failing → fable / stage master. **Δ** Fable single shot is not better than opus + fix |
| code routine (pytest, PARI) | sonnet | 1 opus fix | as above |
| conceptual / delicate (design, interfaces, normalisations) | opus or fable | — | opus failed or likely insufficient → fable |
| audits: WP audit | opus (alternate with fable for adversarial) | — | — |
| audits: chapter audit, Lean audit (`agents/roles/mathematics_chapter_audit.md`, `lean_audit.md`), adversarial | **fable**, parallel | — | — |
| coordination: milestone / stage master | opus | — | — |
| logging, reporting, file moves, formatting, inbox polling, mechanical edits | haiku | — | — |
| anything via opencode (muse, mistral) | **not as implementer**; Q&A and cheap first-pass checklists only, behind a verifier | — | — |

## 2. Evidence table
Minutes = `active` (impl + audit + fix, PROT §3) unless "agent"; W = 3·crit+2·maj+1·min at r0; "rnd" = fix rounds.
Pass = acceptance green, no crit/maj, ≤ 3 minor (PROT §2.4). Decision: τ = max(15 % of best active, 5 min), cheaper wins on tie (PROT §4.1, §4.3).

| Cell | Comparisons (stage-WP; models; active; rnd; quality; outcome) | Status | Conf. |
|---|---|---|---|
| Lean mechanical (vendoring) | s01-E6/X3: haiku 4.8 min, W 4, Q 10/10, rnd 0, **win**; mistral 9.2, W 2, Q 10/10, passed (LOG) | decided (b), prior | medium |
| Lean mech.-with-meaning | s01-E5/L13 (remote, stacked): sonnet W 1, Q 10, passed r0, **win**; haiku W 5 (1 major, signature deviation), Q 8, stopped. Agent time not recorded (LOG, SUMMARY). **s05-E5′/L4** (non-vacuity instances, CONCEPTD, same seed): sonnet + 1 opus fix 16.8 min, blind Fable W 3 (0/0/3), Q 6, **win**; opus + same-model fix 27.5 min, W 2 (0/0/2), Q 7; τ = 5; merged = winner | decided (prior), confirmed | medium |
| Lean routine | s01-E2/L5a: sonnet 4.0, W 3, Q 9, **win**; muse 13.0, W 10 (2 crit), Q 3, failed (LOG) | decided (b), prior | medium-high |
| Lean hard | s01-E1/L9: opus agent ~16 (+2.2 audit), 1 TITAN round, W 4 (adj 2), Q 9, **win**; sonnet agent ~12, 4 TITAN rounds, W 6 (adj 4, 4 minors > 3), not a pass. Confounded by remote latency; opus audited opus (LOG, SUMMARY). **s02-E1/L1** (TITAN): sonnet 26.6 (A), W 5, Q 9/9, rnd 1, **win**; opus 36.2, W 6, Q 9/10, rnd 1 planned fix, both passed (LOG). Challenger sent alone in round 1 = off-regime. **s04-E1′/L6** (TITAN, same seed per round, pair jobs): sonnet strand escalated to opus at r1, active 18.1 min, Qf 10, cost 145 (B), **win**; opus strand 26.3 min, Qf 9, cost 313 (C); both failed audit r0 only on the minor count; τ = 5; merged = opus head (LOG 907d940c) | **decided (prior): sonnet first + 1 opus fix off the critical path; opus on it** | medium |
| LaTeX routine | s01-E4/M2: sonnet 7.7, W 8, Q 10/10, rnd 1 (opus fix), **win**; muse W 19 (2 crit, 5 maj), Q 2, failed. **s02-E4/M1**: sonnet + opus fix 8.05 (W 6, rnd 1), **win**; opus single shot 7.8, W 6 → failed (minor 6 > 3) (LOG) | decided (two comparisons agree on sonnet) | medium |
| LaTeX hard | s01-E8/M4: opus 14.3, W 6 (0/1/4) failed at top rung; sonnet W 10, Q 7, escalated, result not logged → all-fail (proposed). **s03-E8/M2**: opus 22.2 (impl+2 audits+planned fix), W0 5, rnd 1, Qf 9, pass → **win**; fable single shot 20.1, W 4, Q0 10, failed only on minor 4 > 3 (LOG; external-check.md added to audit inputs; Opus audited opus) | decided for opus+fix, prior | medium |
| code routine | s01-E3/C1: sonnet 10.8, W 6, rnd 1 (opus fix), Q 9/10, **win**; mistral 46.0, rc 124 twice, empty patch, passed only after sonnet→opus (LOG) | decided (b), prior | medium |
| Audits (Fable) | s02-L12 Lean audit found the vacuous RamNrdSurj instance (D=1 lemma removed in L13a) (→ Hyp.RamNrdSurj, L13a); s02 chapter audit M6 R1–R3, s01 L15/M7 R1–R11 fixed (closure reports); s03 chapter audits found errors in remote maths (reported by the global master; no log source) | decided (practice) | medium-high |
| Muse as auditor | `plan/staged/METRICS.md`, `plan/implementation/METRICS.md`: fast; 17 % findings fully confirmed, 48 % partial, 35 % rejected; severity inflation; wrong suggested fixes (stage-01 F8: all five Lean points wrong) | decided: first-pass only | medium |
| Conceptual / delicate | no strand run; PROT §8.4: keep opus/fable irrespective of stage-1 data | prior | — |

## 3. Rules of thumb (observed)
- Remote-only Lean (TITAN, round trips of minutes): iterative models are penalised (s01-E1 sonnet 4 rounds vs opus 1). Stack WPs
  and send **one batched integration round per cycle**; a stale base gives false failures (s01-E5 rounds 1–3 failed on unverified upstream L11a).
- Opus pays off when a hard Lean proof must be right first time on the critical path; Sonnet is faster and cheaper on most other Lean
  (s01-E2, s02-E1) — when the regime is equal, prefer sonnet + opus fix.
- Haiku only for mechanical copy/vendoring, logging, polling; not for `.lean` text with new statements, never for proofs (s01-E5).
- Muse/Mistral: not implementers (Muse failed r0 on E2/E4; Mistral timed out on E3, 46 vs 11 min). Q&A and cheap first-pass checks only.
- Sonnet LaTeX/code regularly returns 6–8 minors at r0: budget one cheap opus fix (~2 min) rather than a stronger first shot.
- A stronger single shot does not remove the fix round: opus on routine LaTeX (s02-E4) and fable on hard LaTeX (s03-E8) both failed on minor count alone.
- Fable: audits and cases where opus fails; weight 20 vs opus 10 vs sonnet 4 in cost_idx (PROT §3). Not worth it as a hard-LaTeX implementer (s03-E8).
- Relays to workers/auditors: give the **file path of the build log**, not a paraphrase; **no fix hints** in experiment relays (s01-E1 hints were stripped).
- Opus audit of an Opus strand has a self-preference confound (s01-E1/E8, s03-E8); name it in the log or use fable/blind labels.
- Do not extrapolate across tracks or down in difficulty (PROT §8.4).

## 4. Keeping this file current
- Run a new strand **only** for cells *undecided or confounded* (now: LaTeX hard single-comparison; Lean mech.-with-meaning), at most **1–2 per stage**,
  and only per PROT §9 conditions (cell ≥ 20 % of remaining agent wall, WP meets §1.1, fits the agent limit; run pairs in the **same regime**, started together).
- Record: LOG.md row (events.tsv → Haiku logger, rows never edited except `notes`), then update the §2 row here (minutes, rounds, W, Q, outcome, status);
  if the verdict changes, update §1 and append a dated line below; if it differs from OVERVIEW §5.1, tell the global master (who approves).
- Dated changes:
  - 2026-11-14: file created from stages 1–3 (LOG.md s01/s02/s03). Δ vs OVERVIEW §5.1: Lean hard has a sonnet-first option off the critical path; fable not used as hard-LaTeX implementer.

## 5. Pointers
`plan/implementation/EXPERIMENT_PROTOCOL.md`; `plan/implementation/experiments/LOG.md`, `SUMMARY.md`, `events.tsv`; OVERVIEW §5.1–5.2
(all under `/home/janosch/dev/Langlandscape-wt/impl/`); `agents/rules/opencode.md`; `agents/roles/global_master.md` (Model selection).
  - 2026-11-14 (stage 4): Lean-hard cell decided (prior) by s04-E1′/L6; removed from the undecided list.
  - 2026-11-15 (stage 5): Lean mech.-with-meaning cell confirmed by s05-E5′/L4 (sonnet + 1 opus fix wins on time).
