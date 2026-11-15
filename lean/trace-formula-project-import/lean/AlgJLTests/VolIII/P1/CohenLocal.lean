import AlgJL.VolIII.P1.CohenLocal

/-!
# Tests for `GL2TF.VolIII.P1.CohenLocal`

`CohenLocal` has no definitions. One concrete instance of item 20's case split, checked by the kernel, so the hypotheses
`f ∈ 𝓕(t, n)` and the two cases are met by real data (the F-D2 example `N = 3`, `t = −1`, `n = 7` of plan trap 12).
-/

namespace GL2TFTests

open GL2TF.Explicit

/-- `𝓕(−1, 7) = {1, 3}` (`t² − 4n = −27`), with `μ_3(−1, 1, 7) = 1 + χ_{−27}(3) = 1` (`3 ∤ 1`) and `μ_3(−1, 3, 7) = 4`
(`3 ∣ 3`). -/
theorem cohenMu_three_neg_one_seven :
    orderIndexSet (-1) 7 = {1, 3} ∧ cohenMu 3 (-1) 1 7 = 1 + (kroneckerPrime (-27) 3 : ℚ) ∧
      cohenMu 3 (-1) 3 7 = 4 := by
  decide +kernel

end GL2TFTests
