import AlgJL.VolIII.P2.Orders

/-!
# Tests for `GL2TF.VolIII.P2.Orders`

Named test declarations for the tagged definitions of Q2 items 21, 22, 25, 27, 30, 31, 33 (plan §1.2) and their B-only
plumbing (`standardSubalgebra`, `MaxOrder`, `eichlerSubalgebra`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `i ∈ ℤ⟨1, i, j, k⟩` (the standard order of any `(a, b)`). -/
theorem standardOrder_mem_i (a b : ℤ) :
    (⟨0, 1, 0, 0⟩ : QuatAlg ℚ a b) ∈ (standardOrder a b).toSubalgebra :=
  ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩⟩

/-- `1/2 ∉ ℤ⟨1, i, j, k⟩` for `(a, b) = (−1, −1)` (the standard subalgebra is not all of `B`). -/
theorem half_not_mem_standardSubalgebra :
    (⟨1 / 2, 0, 0, 0⟩ : QuatAlg ℚ (-1) (-1)) ∉ standardSubalgebra (-1) (-1) := by
  rintro ⟨⟨n, hn⟩, -⟩
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [← hn]; norm_num
  have h3 : 2 * n = 1 := by exact_mod_cast h2
  omega

/-- The discriminant is the Gram determinant `det(trd(e_i ē_j))` of the basis chosen by `Module.Free.chooseBasis`
(definitional unfolding; the value `d(ℤ⟨1, i, j, k⟩) = 16 a² b²` is a W3 proof target). -/
theorem discriminant_eq_gram_det {a b : ℤ} (O : QOrder a b) :
    discriminant O =
      letI : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
      letI : Module.Finite ℤ (Subalgebra.toSubmodule O.toSubalgebra) := Module.Finite.iff_fg.mpr O.fg
      (Matrix.of fun i j : Module.Free.ChooseBasisIndex ℤ (Subalgebra.toSubmodule O.toSubalgebra) =>
        trd ((Module.Free.chooseBasis ℤ (Subalgebra.toSubmodule O.toSubalgebra) i : QuatAlg ℚ a b) *
          star (Module.Free.chooseBasis ℤ (Subalgebra.toSubmodule O.toSubalgebra) j : QuatAlg ℚ a b))).det :=
  rfl

/-- The second component of a maximal order is its maximality. -/
theorem maxOrder_isMaximalOrder {a b : ℤ} (O : MaxOrder a b) : IsMaximalOrder O.1 :=
  O.2

/-- A maximal order contains no strictly larger order. -/
theorem isMaximalOrder_eq_of_le {a b : ℤ} {O O' : QOrder a b} (hO : IsMaximalOrder O)
    (h : O.toSubalgebra ≤ O'.toSubalgebra) : O'.toSubalgebra = O.toSubalgebra :=
  hO O' h

/-- The ring hom of a level structure is surjective. -/
theorem levelStructure_surjective {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    Function.Surjective φ.toRingHom :=
  φ.surjective

/-- `O(M; φ) ⊆ O` (via the underlying subalgebra). -/
theorem eichlerSubalgebra_le_order {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M)
    {x : QuatAlg ℚ a b} (hx : x ∈ eichlerSubalgebra φ) : x ∈ O.toSubalgebra :=
  hx.1

/-- `M O ⊆ O(M; φ)`. -/
theorem zsmul_mem_eichlerOrder {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M)
    {x : QuatAlg ℚ a b} (hx : x ∈ O.toSubalgebra) : ((M : ℤ) • x) ∈ (eichlerOrder φ).toSubalgebra :=
  zsmul_mem_eichlerSubalgebra φ hx

/-- `−1 ∈ O^×` for every order. -/
theorem neg_one_mem_unitGroup {a b : ℤ} (O : QOrder a b) : (-1 : (QuatAlg ℚ a b)ˣ) ∈ unitGroup O :=
  ⟨by simpa using O.toSubalgebra.neg_mem O.toSubalgebra.one_mem,
    by simpa using O.toSubalgebra.neg_mem O.toSubalgebra.one_mem⟩

end GL2TFTests
