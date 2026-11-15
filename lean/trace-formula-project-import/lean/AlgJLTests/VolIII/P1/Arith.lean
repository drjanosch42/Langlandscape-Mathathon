import AlgJL.VolIII.P1.Arith

/-!
# Tests for `GL2TF.VolIII.P1.Arith`

Kernel-checked values (`decide +kernel`; no `native_decide`, plan trap 11) of `ψ`, `𝓕(t, n)`, `h(Δ)` and `P_k`.
-/

namespace GL2TFTests

open GL2TF.Explicit

/-- `ψ(6) = 12` and `ψ(0) = 0`. -/
theorem dedekindPsi_six_zero : dedekindPsi 6 = 12 ∧ dedekindPsi 0 = 0 := by
  decide +kernel

/-- `𝓕(0, 4) = {1, 2}` (`t² − 4n = −16`: `Δ_1 = −16`, `Δ_2 = −4`; `f = 4` gives `−1`, not a discriminant). -/
theorem orderIndexSet_zero_four : orderIndexSet 0 4 = {1, 2} := by
  decide +kernel

/-- `h(−3) = 1`, `h(−4) = 1`, `h(−12) = 1` (primitive forms only), `h(−20) = 2`, `h(−23) = 3`, and `h(5) = 0` (junk). -/
theorem classNumberForms_values :
    classNumberForms (-3) = 1 ∧ classNumberForms (-4) = 1 ∧ classNumberForms (-12) = 1 ∧
      classNumberForms (-20) = 2 ∧ classNumberForms (-23) = 3 ∧ classNumberForms 5 = 0 := by
  decide +kernel

/-- `P_12(1, 2) = 23` and `P_4(3, 2) = 7`. -/
theorem heckePoly_values : heckePoly 12 1 2 = 23 ∧ heckePoly 4 3 2 = 7 := by
  decide +kernel

end GL2TFTests
