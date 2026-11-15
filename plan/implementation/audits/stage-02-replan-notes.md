# Stage 02 re-plan notes (revision 2, 2026-11-14)

## What changed and why
- **Remote-only Lean (F10).** Every L acceptance is now CHK = the WP's `titan_batch.sh` spec line green in an
  integration round. Local lbuild/lfile batching and the slot plan are removed. int1 and int2a spec lines are written
  out (§3.3); later rounds are sketched; there is an early gate-1, a final from-scratch gate, and the axiom generator X2.
- **Models per OVERVIEW §5.1.** No muse/mistral/TBD. Every row names its model and fix budget. L4b and L7 drop from
  hard/opus to routine/sonnet: S01 already has `levelMap`, `translateMap`, `pushforward`, `trace` and
  `heckeT_comm_rightTranslate_localEmbed`, which is the core step of `prop:s02-quot`(c).
- **Merges and splits.** Rev.-1 L1 and L2 are merged into **L1**, which is the E1 strand. It has only verified upstream
  (S01 + Mathlib), so there is no stacking confound, and the merge removes one hop from the critical path. L4a is split
  into `Admissible.lean` (S01 only) and `Action.lean` (needs L1), so int1 does not hinge on the L1 draft. `Hyp.BTtree`
  moves to L5b, its only user. Rev.-1 L10 (the BG certificate under a new `Hyp.BGData`) is dropped. The new **L10** is
  the carried-over `lem:s01-nrd`. Rev.-1 L11 (integration) is replaced by the gates L11 and L14 and by the fix WPs L13a/b.
- **Kept:** rev.-1 WP ids (stage 03 cites S02-L4b/L6/L7/L8/L9), coset tree, SA-free core, Muse items F1–F3/F5/F7/F8/R1/R3.
- **New WPs.** X1 widens `check_wp.sh` from `s01-` to `s[0-9][0-9]-` (coordinator finding, sonnet). X2 is the axiom-list
  generator (haiku). X3 is the S01 hygiene WP (F17). X4 is the closure. M8 is literature notes (remote-eligible).
- **Strands.** E1 runs on S02-L1 (opus reference vs sonnet). E4 runs on S02-M1 (sonnet + opus fix vs opus single
  shot). Both run locally with Fable blind WP audits, neutral a/b TITAN jobs, one slot each per round, and no fix hints.
- **Remote table** (§6): M2, M3, M5 (optional) and M8. M4 is not eligible (its input is a code result) and neither is M7
  (it edits existing files). The stage is launchable without Abhijit. Wall: critical path 140 min, stage 2.5 h ± 0.7.

## Assumptions about the new OVERVIEW (3d7faf8, read after drafting began)
- I used §4.3 (job ids, the strand variant via `titan-in/`, `.titan/` only on `impl/sNN-int<k>`), §5.1/§5.2 (strand
  audits by fable), §6.1 (table columns: WP | branch | files | fallback) and §9 (lessons 1–6) as committed.
- F3 (M and C/T sub-coordinators) and F12 (≤ 8 subagents per coordinator) remain in force, and Fable may run in
  parallel (F4 superseded).
- Strand job commits get their `.titan/` spec as a stage-master scratch commit on top of the strand head. This is my
  reading of "spec on the strand commit, never merged", chosen so the reference strand can be merged first without
  `.titan/` content.
- The M chapter uses `\InputIfFileExists` stubs (X1), so remote M WPs write new files only. Bib entries and NOTES lines
  come back in the WP reports (no `bib/s02.bib` file).

## Open questions for Fabian (defaults in the plan)
1. Should E1 run on the critical-path WP L1 (reference merged first), or on the off-path L9? [L1]
2. Is it fine to use trivial coefficients only for the two-term complex in stage 02 and bring V-coefficients in with
   stages 04–06? [yes]
3. Should `Hyp.BTtree` use the full (q+1)-regular-tree shape, even though only connectivity is used? [full shape]
4. Which M WPs go to Abhijit (M2, M3, M5, M8), given that scout Q2/Q5–Q7 are open? [all local until confirmed]
5. Is it fine to drop the rev.-1 BG certificate WP (and `Hyp.BGData`)? [dropped]
