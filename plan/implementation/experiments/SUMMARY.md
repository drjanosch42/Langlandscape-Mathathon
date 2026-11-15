# Stage 01 experiment summary (EXPERIMENT_PROTOCOL §8)

Source: `LOG.md` (rows), `events.tsv`, audits, track reports; 2026-11-14, stage 01. Status of everything below:
**computed from one comparison per strand pair, i.e. a PRIOR (§9), not a decision.** Global master approves any
assignment change. Times in minutes; `active` = impl + audits + fixes (§3), `wall` incl. waiting.

## 1. Per-strand table

| WP | strand | outcome | active | wall | W0 (crit/maj/min) | Q0/Qf | rounds / escalation | cost |
|---|---|---|---|---|---|---|---|---|
| E6 X3 | haiku | winner | 4.8 | 14.6 | 4 (0/0/4) | 10/10 | 0 / none | 32/A |
| E6 X3 | mistral | loser (passed) | 9.2 | 14.5 | 2 (0/0/2) | 10/10 | 0 / none | 46/B |
| E2 L5a | sonnet | winner | 4.0 | 17.1 | 3 (0/0/3) | 9/9 | 0 / none | 28/A |
| E2 L5a | muse | failed | 13.0 | 17.2 | 10 (2/0/4) | 3/- | 0 / (r0 stop) | 31/A |
| E1 L9 | opus | winner | ~18 (16 agent + 2.2 audit) | 79.3 | 4; adj 2 (0/1/2) | 9/9 | 0 / none, 1 TITAN round | 182/C |
| E1 L9 | sonnet | loser | ~15 (12 + 2.6) | 79.8 | 6; adj 4 (0/1/4) | 9/- | 0 / none, 4 TITAN rounds | 74/B |
| E1 L9 | muse | cancelled | - | 77.0 | - | - | no local Lean | - |
| E5 L13 | sonnet | winner | n/a (draft 0.8 + 4 TITAN rounds) | 54.7 | 1 (0/0/1) | 10/10 | 0 / none | n/a |
| E5 L13 | haiku | loser | n/a (draft 2.7 + 3 TITAN rounds) | 55.0 | 5 (0/1/3) | 8/- | 0 / none (stopped) | n/a |
| E3 C1 | sonnet | winner | 10.8 | 11.6 | 6 (0/0/6) | 9/10 | 1 / sonnet->opus@r0 | 86/B |
| E3 C1 | mistral | loser (passed) | 46.0 | 46.3 | 14 (4/1/0) | 0/10 | 2 / mistral->sonnet->opus | 221/C |
| E4 M2 | sonnet | winner | 7.7 | 8.3 | 8 (0/0/8) | 10/10 | 1 / sonnet->opus@r0 | 64/B |
| E4 M2 | muse | failed | 4.3 (to r0) | 12.9 | 19 (2/5/3) | 2/- | 0 / ->sonnet (not run) | 27/A |
| E8 M4 | opus | failed (top rung) | 14.3 | 14.4 | 6 (0/1/4) | 9/9 | 0 / none | 143/B |
| E8 M4 | sonnet | stopped | 10.2 (to r0) | 20.1 | 10 (0/2/6) | 7/- | ->opus@r0, no result logged | 69/B |

Notes: E1 times use the stage master's agent-time estimate (opus ~16, sonnet ~12), cost from the same; the raw impl
window (77 min) is dominated by TITAN waits. E1 adj = finding A0.1 (committed `.titan` scratch) discounted as an
artefact of stage-master instructions. E5 agent time was not recorded; wall is mostly TITAN waits.
Auditor verdict PASS at r0 for E3-sonnet and E4-sonnet, but the protocol rule (minor <= 3) failed them, so both used
one opus fix round.

## 2. Per-cell verdicts (§9)

| Cell | Comparison | Winner | Verdict | Reason |
|---|---|---|---|---|
| Lean infra / mechanical (E6) | haiku vs mistral | haiku | decided (b), prior | both pass, Qf equal, active 4.8 <= 0.67 x 9.2; haiku also cheaper |
| Lean / routine (E2) | sonnet vs muse | sonnet | decided (b), prior | muse failed (2 critical, Q 3), sonnet passed without escalation |
| Lean / hard (E1) | opus vs sonnet (muse cancelled in S01); repeated S02-L1, S04-L6 | sonnet (+ planned opus fix) in 2 of 3; S01 opus | decided (a) §9, prior; contradictory with S01 | S01-L9: opus won (sonnet no pass, remote latency confound, opus audited opus). S02-L1: sonnet won (active 26.6 vs 36.2, both passed). **S04-L6 (E1′): sonnet won (active 18.1 vs 26.3, tau 5, Qf 10 vs 9; sonnet escalated sonnet->opus at r0 on W=6, cost 145/B vs 313/C; both 3 remote rounds, Fable audits, same regime); merged = opus strand a289461 (merged before decision).** Two comparisons (S02, S04) with the same winner satisfy §9(a); S01 contradicts it and is confounded. Sonnet-first with one opus fix is the supported assignment off the critical path; critical-path / remote-only Lean keeps opus (S01) |
| Lean / mechanical, stacked (E5) | sonnet vs haiku | sonnet | decided (b), prior | haiku major finding (Q 8), sonnet passed r0, no escalation |
| code / routine (E3) | sonnet vs mistral | sonnet | decided (b), prior | active 10.8 <= 0.67 x 46, Qf equal; mistral timed out twice, empty patch |
| LaTeX / routine (E4) | sonnet vs muse | sonnet | undecided (weak) | muse failed r0 (W 19) but sonnet needed an escalation, so the "failed vs clean pass" clause does not apply; margin rule not met (muse active stops at r0) |
| LaTeX / hard (E8) | opus vs sonnet | none | undecided; PROPOSED all-fail (stage master to confirm) | no strand passed under §2.4: opus failed at top rung (W0 6 > 5), sonnet W0 10, Q 7, fix result not logged |

Both E6 and E5 concern Lean mechanical work but of different kind (vendoring files vs writing new Props against
unverified APIs); they are kept as separate cells and give different winners.

## 3. Recommended model assignment for stages 02-06 (priors; §8 rules 1-5)

| Class (track, difficulty) | Model | Confidence | Pre-declared ladder | Measured wall (use instead of estimate, rule 5) |
|---|---|---|---|---|
| Lean infra, mechanical copy/vendoring | haiku | medium | haiku -> sonnet -> opus | impl 2.0 / active 4.8 (n=1) |
| Lean, routine (local API, short statements) | sonnet | medium-high | sonnet -> opus | active 4.0, wall 17 (n=1) |
| Lean, hard (L9/L1/L6-like algebra, Mathlib only) | sonnet first, one pre-declared opus fix (off the critical path); opus when right-first-time on the critical path | medium (S02-L1, S04-L6 sonnet wins, 2 of 3; S01 opus, confounded) | sonnet -> opus (expect an opus fix after r0: minor 6 > 3) | S04-L6: sonnet active 18.1 (impl 9.5), wall 62 under TITAN; opus 26.3 (impl 15.3); S02-L1: 26.6 / 36.2 (n=3) |
| Lean, mechanical but stacked on unverified drafts | sonnet | low-medium | sonnet -> opus | wall 55 under TITAN (n=1), agent time unknown |
| code, routine (pytest loop, PARI) | sonnet | medium | sonnet -> opus (expect 1 fix round) | active 10.8, wall 11.6 (n=1) |
| LaTeX, routine | sonnet (cheap-first muse not supported) | low | sonnet -> opus (expect 1 fix round for minors) | active 7.7, wall 8.3 (n=1) |
| LaTeX, hard (full proofs) | opus | low (no winner); keep stage-0N assignment | opus -> fail; plan an Opus fix round | active 14.3 + production fix (n=1) |
| Conceptual / any track | Opus or Fable | rule 4 | as in stage files | unchanged |

Rules that follow: muse is dropped for Lean-routine and LaTeX-routine; mistral is dropped for code-routine (it only
passes after two escalations, cost 221/C versus 86/B); haiku is kept only for mechanical copy/vendoring. Every
verdict is from a single comparison; stage-02..06 `runs/sNN.md` data must revise them (§9, Fable M14(d)).
Do not extrapolate across tracks or down in difficulty (§8.4). Do not re-run duplicate strands (§9) unless the
global master approves per the §9 conditions.

Other expectation: sonnet strands on LaTeX/code routine regularly return 6-8 minors at r0 (protocol: minor > 3 fails
the pass), so budget one cheap opus fix round (about 1.5-2 min) per such WP.

## 4. Confounds and deviations

- Concurrency: more than one experiment Claude slot ran at once (8-agent limit deviation).
- From about 15:52Z no local Lean: all Lean checks ran on TITAN with round trips of minutes; strands stacked on
  unverified upstream drafts. This penalises iterative models (E1 sonnet, E5) and makes wall/queue values meaningless
  for Lean; stage-master estimates for E1 agent time, nothing recorded for E5.
- Fable ran in parallel (late directive); no Fable strand was compared.
- Opus audits audited Opus strands (E1 opus, E8 opus): self-preference confound; style fingerprints residual.
- L13 strand patches were restricted to own files (upstream fixes merged in by the stage master): reduces strand
  independence.
- Global master's fix hints were stripped from relays (E1 sonnet r2/r3): intended, no contamination.
- E1 finding A0.1 discounted as a stage-master artefact (adjusted W).
- Decisive stops skipped fix rounds (E2 muse, E1 sonnet, E5 haiku, E4 muse): losers' final quality `Qf` is unknown,
  so margins use `active` to r0 and failure at r0 only.
- Missing data: E5 agent times; E8 sonnet fix round and r1 audit; patch files for `s01-m2-muse` and `s01-m4-sonnet`;
  Claude token counts; E1 muse produced only a partial i1 file.
- The one-per-cell sample size, different audit-W scales between LaTeX and Lean, and a single audit per strand
  (no repeat) mean verdicts are priors.

## 5. Addendum E1′ (S04-L6, 2026-11-14)

New evidence for the Lean-hard cell (details: `LOG.md`, Stage 04 block; `audits-s04-l6/`). Winner sonnet (active 18.09 vs 26.32 min, tau 5.00, Q 10 vs 9, cost 145/B vs 313/C), merged opus strand a289461 (merged before the decision). Active minutes are estimates from event timestamps; production rescue writer in parallel is a wall/latency confound only; auditors were Fable (no Opus self-preference). The cell is now decided under §9(a) (two comparisons with the same sonnet winner) as a prior; the S01 opus result is the contradicting, confounded case. The assignment is revised to sonnet-first with one opus fix off the critical path; opus stays for critical-path / right-first-time Lean.
