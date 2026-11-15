import AlgJL.VolIII.P2.Ramification

/-!
# Tests for `GL2TF.Common.QuaternionHilbert` and `GL2TF.VolIII.P2.Ramification`

`hilbertSymbol` at two values over `ℚ` (by isotropy, directly from the definition), and a negative instance of
`RamifiedExactly`.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `(1, b)_F = 1` for every field `F` and every `b`: `(x, y, z) = (1, 0, 1)`. -/
theorem hilbertSymbol_one_left (F : Type*) [Field F] (b : F) : hilbertSymbol F 1 b = 1 := by
  unfold hilbertSymbol
  split_ifs with h
  · rfl
  · exact absurd ⟨1, 0, 1, by simp, by ring⟩ h

/-- `(−1, −1)_ℚ = −1`: `z² = −x² − y²` has only the trivial rational solution. -/
theorem hilbertSymbol_rat_neg_one_neg_one : hilbertSymbol ℚ (-1) (-1) = -1 := by
  unfold hilbertSymbol
  split_ifs with h'
  · exfalso
    obtain ⟨x, y, z, hne, h⟩ := h'
    apply hne
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    simp [hx, hy, hz]
  · rfl

/-- `RamifiedExactly` requires a definite algebra: `(1, −1)` is never `RamifiedExactly`. -/
theorem not_ramifiedExactly_one_neg_one (D : ℕ) : ¬ RamifiedExactly 1 (-1) D := by
  intro h
  exact absurd h.1 (by norm_num)

end GL2TFTests
