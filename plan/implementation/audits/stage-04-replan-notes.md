# Stage 04 re-plan notes (drafter, Opus, 2026-11-14)

## What changed and why
- Structure follows `briefs/replan-s02-06.md`: new columns `model (+fix)`, `remote-eligible`, `TITAN round`; calibrated
  times (agent-active / wall); TITAN rounds int1–int5 + gate-1 + final; Fable Lean audit (L16) parallel to Fable chapter
  audit (M9); remote-eligible table; one conditional strand. 33 → 40 WPs, plan wall 10.2 h → 2.8 h (range 2.0–3.8 h).
- Models: muse/mistral removed (old L2, L4, C3, X2 options); classes per brief §A.
- **Design of `e` fixed in the plan** (D-e: `ordPart`/`nilPart`/`HasOrdDecomp`), no longer a conceptual L1. Split into
  L1 (formal part), L2 (finite length via Mathlib Fitting) and L3 (f.g. `ℤ_[p]`), with fallback F-e (`ZMod (p^m)` for all m)
  so that the hard p-adic step does not block the critical path.
- **Weil vendoring dropped** (D-lim): Hida control gives surjective transition maps, so `lim` exactness is elementary;
  limits are compatible-family submodules. Saves a vendoring WP, a lakefile change and a licence item.
- **η-principle Lean (old L10) moved to stage 06** (D-eta): it would have stubbed stage-06 definitions on our branch.
- **Carry-overs from stage 1** (closure "open issues"): L5 = `U'_p`, `U_p^* = ⟨p⟩_M U'_p`, the trace half of
  `lem:s01-Up`(c) and the product diamond `diamondM`; L15a/L15b = Hecke operators with coefficients and `V_k`
  (ext, consumer `Hyp.HidaControl`); L9 = `U_p` at levels other than `Utower` (`K'_s`, `U0q`). C3 checks L5 numerically.
- New WPs: X2 axiom scratch files (lesson D2), X3 early gate (D1), X4 final gate, M5 literature, M8 second reader of the
  Hsieh dictionary (normalisation risk R1), L17 audit fixes. The old L11 integration WP is replaced by the X3/X4 gates.
- Found during reading: `tools/check_wp.sh` accepts a docstring only if it contains `s01-`; X1 generalises it to
  `s0[1-6]-` (unless the stage-02 kickoff already did). Stage-1 `Up` exists only at `Utower` (`Brandt/Up.lean`).
- Upstream couplings only through `if:s02-quot`, `if:s02-indef`, `if:s03-graph`, `if:s03-ribet` (no S02/S03 WP ids).

## Assumptions
- Stages run in sequence, so stage 03 is merged before S04-X1; otherwise X1 writes signature stubs on `impl/s04-int1` only.
- Stage-03 Ribet sequence is available with arbitrary coefficient ring (or over ℤ plus base change), and `if:s02-quot`(c)
  gives `U_p`-equivariance of `s0_*`, `s1_*` for `p ≠ q` (otherwise L12 grows by about one round).
- Mathlib v4.35 has `LinearMap.eventually_isCompl_ker_pow_range_pow` and `Module.free_of_flat_of_isLocalRing` (names to be
  checked in round int1). It has no `IsLocalRing (MonoidAlgebra …)` and no Iwasawa algebra.
- The 8-subagent limit and sub-coordinators for M and C/T (OVERVIEW F3) still apply; several Fable agents may run at once
  (Fabian, 18:22).
- HACS stays empty (F8): H1 is optional.

## Open questions for Fabian (defaults in brackets; stage-04.md §7)
- Q1 `Hyp.MordLambdaFree` with no Λ in Lean, L13's compatible bases being the strongest proved form? [yes]
- Q2 η-principle Lean to stage 06? [yes]  Q3 Hecke-with-coefficients in stage 04 as ext (L15a/b)? [yes, schematic fallback]
- Q4 F-e fallback (`ZMod (p^m)` instead of `ℤ_[p]`) acceptable? [yes]  Q5 drop Weil vendoring? [yes]
- Q6 `prop:s04-ekillsVk` (M7) optional or drop? [optional]
- For the cross-stage check: stage 06 must accept ownership of the η-principle Lean (D-eta), and stage 05 must read `Mord`/`Xord` as
  compatible-family submodules.
