# Stage 05 re-plan notes (drafter, Opus, 2026-11-14)

## Changes and reasons
- Structure follows `briefs/replan-s02-06.md` §0–§7. Cross-stage references now use labels only (`if:s06-lemD`,
  `if:s04-ekills`, `if:s03-graph`); old S01-/S04-/S06- WP ids are removed, and stage-1 inputs are exact declaration names (main 7ce2a3e).
- Remote-only Lean: all L WPs draft against declared signatures and are checked in integration rounds int1/int2*/int3. There is
  an early full gate G1 at mid-stage, a final from-scratch gate G2, and an axiom-scratch WP X2 (haiku, fully qualified).
- Models per brief A. Muse/mistral are dropped. C1 is now sonnet (was mistral), L4 sonnet (was muse candidate), L5 sonnet (plumbing
  of existing `Tl_adjoint'`/`diamond_adjoint`/`PiEll_adjoint`/`normMap_pushforward_two`) instead of opus.
- New WPs: X2 (axioms), R1 (independent second reader of the normalisation chain; remote-eligible), L2b (DR bridge split off
  L2), L11 (audit fixes). L9 (integration) becomes the stage-master steps G1/G2. L6a becomes fallback L6F.
- `if:s06-lemD` seam is made explicit in §0: owner, expected names, three states (merged / stub on int branch only / fallback),
  and the seam conditions (A local, field-free `c` via a lemma `splitting_to_c` in L6).
- Stage-1 carried-over items are made concrete in L1: no `U_ℓ` for ℓ ∣ M, no product diamond. L1 has a decision rule.
- Wall recalibrated (factor ≈ 0.25 vs coarse plan): critical path ≈ 120 min, stage ≈ 2.0 h (1.5–3.0 h). The coarse plan had 7.2 h.
- C2 pairs fixed to informative ones ((13,5), (11,7)). C2 builds on stage-1 `levels.py` `U_1(N)` class sets; the `U_1(N)` Hecke/Π_q action is new code.
- Conditional strand E8′ (LaTeX hard) on M3. It runs only if stage 03's E8 stays undecided.

## Assumptions
- Stage 05 starts after stage 04 is merged (or exports `if:s04-ekills` in Lean) and runs in parallel with stage 06.
- Stage-06 Lemma D names (`NewOldData`, `ann_a/ann_b`, `bEquivDualQuot`, `IsGorensteinWith`) and stage-04 names (`ordPart`,
  `ordProj`) are taken from the current plans. X1 reconfirms them.
- M WPs write per-WP bib files `bib/s05-<wp>.bib` (merged into `bib/s05.bib` by M9). X1 creates `\InputIfFileExists`-guarded
  drivers so that remote WPs create new files only. This deviates slightly from the brief's single `bib/sNN.bib`.
- Concurrency of about 17 W1 writers assumes the 8-subagent limit with M and C/T sub-coordinators. Fable audits run in parallel (Fabian 18:22).
- H1 stays unscheduled (`code/hacs/` empty, OVERVIEW F8).

## Open questions for Fabian
1. FD1: μ_N-model + Picard for Hyp.X (tex `\provisional` F1/D1), so `Frob_q = qU_q` and Frobenius permutation `Π_q⁻¹`.
   Needed before L3 merges.
2. FD2: Hsieh's `JL(U_q) = −U_q` treated as an erratum (tex `\provisional` F6/D3). Also: write to the author?
3. If L1's rule triggers, may `HeckeSym`/`Hyp.X.char` omit `U_ℓ` (ℓ ∣ M), or should the Lean statement be restricted to M = 1?
4. May stage 05 close with L6 (Lean `if:s05-subquot`) carried into stage 06 if Lemma D is late, instead of fallback L6F?
