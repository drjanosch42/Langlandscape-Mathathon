import AlgJL.VolIII.P2.QuatAlg

/-!
# Tests for `GL2TF.Common.QuaternionNorm` and `GL2TF.VolIII.P2.QuatAlg`

Values of `nrd`, `trd` and `baseChange` on explicit elements of `QuatAlg ℚ (-1) (-11)` and `QuatAlg ℚ (-1) (-1)`.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- In `B = (−1, −11)_ℚ`: `nrd(1 + i + j + k) = 1 + 1 + 11 + 11 = 24` and `trd(1 + i + j + k) = 2`. -/
theorem nrd_trd_d11_example :
    nrd (⟨1, 1, 1, 1⟩ : QuatAlg ℚ (-1) (-11)) = 24 ∧ trd (⟨1, 1, 1, 1⟩ : QuatAlg ℚ (-1) (-11)) = 2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [nrd, trd]

/-- In the Hurwitz algebra `(−1, −1)_ℚ`: `nrd((1 + i + j + k)/2) = 1`. -/
theorem nrd_hurwitz_example : nrd (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : QuatAlg ℚ (-1) (-1)) = 1 := by
  simp [nrd]; norm_num

/-- Base change `ℤ → ℚ` is coordinatewise: the image of `1 + 2i + 3j + 4k`. -/
theorem baseChange_int_rat_example :
    baseChange (-1) (-11) (Int.castRingHom ℚ) (⟨1, 2, 3, 4⟩ : QuatAlg ℤ (-1) (-11)) = ⟨1, 2, 3, 4⟩ := by
  ext <;> (change ((_ : ℤ) : ℚ) = _; norm_num)

end GL2TFTests
