---
id: 20261114-212308Z_abhijit_c3-xr-s01-report
from: abhijit/c3-xr-s01
to: fabian/global_master
type: report
re: 20261114-210238Z_fabian_batch4
priority: normal
---
C3 (cross-account review of the stage-01 chapter at BASE 864d104) is done and pushed.

- Branch `abhijit/xr-s01`, head `76cdae95de07d3a2b32cd08cacf7033504c4f947`.
- `git diff --name-only 864d104...HEAD`: `mathematics/audits/2026-11-14_s01-xacct.md` (only this file).
- Verdict line: `verdict: FIX LIST`, `W = 3·crit + 2·maj + min = 3·0 + 2·1 + 10 = 12`.
- Counts: crit 0, maj 1, min 10, note 6.
- Comparison with our audit: NEW 16, KNOWN 0, KNOWN-BUT-UNFIXED 1 (X9, residual of M7.21).
- Method: the review was done blind first. Two sub-agents (Sonnet, Opus) checked citations in the PDFs. No PDF is missing.
- Lean names: all 51 `Langlandscape.*` names and all quoted import names exist on BASE.

## crit / maj findings (inline)

- **X1 (maj, consistency), `6-targets.tex:48–50`, `thm:s01-lambdaJL`, plus `if:s01-targets` and Lean `Langlandscape.Hyp.LambdaJL` (field `∀ d, φ (genGL (.dia d)) = genB (.dia d)`).**
  - The exported Λ-adic JL target is stated in the seed's normalisation, and it sends "diamonds to diamonds".
  - The chapter itself proves that the seed's adelic ⟨d⟩ is the classical ⟨d⟩⁻¹ (`rem:s01-diamond`, `lem:s01-Upconv`(a),(b),(d)).
  - It also proves that LV's ⟨n⟩ = T(n,n) is the seed's ⟨n⟩⁻¹. So LV Prop 6.1 (p.27) sends classical ⟨d⟩ to seed ⟨d⟩⁻¹.
  - As written, the generator matching is false for the seed's diamonds, and the Lean hypothesis encodes the same matching. The "Caveat" paragraph points to the flag, but the statement and the Lean field contradict it.
  - Fix: write "classical ⟨d⟩ ↦ seed ⟨d⟩⁻¹" in the theorem, the interface and `Hyp.LambdaJL`, or define `genB (.dia d)` as the inverse diamond.
  - Consumers: stages 04 and 05.

## min findings (one line each)

- X2: Voight Prop 41.3.1 (p.770) is cited for the Hecke recursion. The recursion is Prop 41.3.6 / (41.3.8), p.771.
- X3: the N = 0 remark says "ℓ^{v_ℓ(0)} = 0, i.e. no congruence condition", which is self-contradictory.
- X4: `thm:s01-JLclassical` assumes "k even", but its Γ₁ clause says k ≥ 3; (N,D) = 1 is missing there.
- X5: JL Thm 16.1 "p.494" cannot be checked in our copy, which is a retypeset edition with the theorem on p.250. The S01-M6 "verified p.494" sentence needs correcting.
- X6: `lem:s01-Upconv`(c) says Hsieh's σ_d is the seed's ⟨d̃⟩. That holds only for trivial coefficients: in weight k, σ_d = ω(d)^{-n}⟨d̃⟩. Hsieh's forms also carry a central-character condition.
- X7: the LV §2.1 p.8 locator for class sets should be §6.1 p.25 (Pic X̃_m).
- X8: Voight Thm 9.4.9 is cited without a page; it is p.145.
- X9: the statuses for the w-variant of thm:s01-mass(b) and the second half of (d) are `\stproved`/`\stpmc`. The Lean declarations `massW_level_change(_two)` and `card_XB_Utower` exist, and the interface says `\stformal`.
- X10: R_g / ρ_g use the level g⁻¹Ug, which is not contained in Ô^×. Def. classset only allows U ⊆ Ô^×.
- X11: `lem:s01-dictionary`(b) says "(m,DM) = 1 ⇒ seed's T_m", but the seed's T_n needs (n,DMp) = 1.

Notes X12–X17 are wording and notation items; details are in the file.

## Node resources (at send time)

- `free -m`: Mem total 15665 MB, available 7525 MB; Swap total 2047 MB, used 1389 MB.
- `uptime` load averages: 1.97, 2.49, 2.25.
