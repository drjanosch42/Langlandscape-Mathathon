/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Local levels in `GL₂(ℚ_ℓ)` (S01-L3a)

Tex label `def:s01-levels`.  The compact open subgroups `GL2Zl ℓ = GL₂(ℤ_ℓ)`, `K0 ℓ e`
(`ℓ^e ∣ c`), `K1 ℓ e` (`ℓ^e ∣ c` and `d ≡ 1 mod ℓ^e`) of `GL (Fin 2) ℚ_[ℓ]`, and the Iwahori
`Iw ℓ = K0 ℓ 1`.  The lower-left entry is the congruence entry (convention of `def:s01-levels`).

Valuation conditions `v(x) ≥ e` are phrased as `‖x‖ ≤ ℓ ^ (-e : ℤ)`; `mem_K0_iff_exists` and
`mem_K1_iff_exists` give the divisibility form over `ℤ_[ℓ]`.  Everything is by entries.
-/

open Matrix

namespace Langlandscape.Local

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Entry-by-entry unpacking of the matrix of a `GL₂` element. -/
local notation "𝔪" g => (Units.val g : Matrix (Fin 2) (Fin 2) ℚ_[ℓ])

section Aux

/-- Auxiliary lemma `norm_add_le_of_le` for the local levels (`def:s01-levels`). -/
lemma norm_add_le_of_le {x y : ℚ_[ℓ]} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/-- Auxiliary lemma `norm_mul_le_of_le` for the local levels (`def:s01-levels`). -/
lemma norm_mul_le_of_le {x y : ℚ_[ℓ]} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ r := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans hx

/-- Auxiliary lemma `norm_mul_le_of_le'` for the local levels (`def:s01-levels`). -/
lemma norm_mul_le_of_le' {x y : ℚ_[ℓ]} {r : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ r) : ‖x * y‖ ≤ r := by
  rw [mul_comm]; exact norm_mul_le_of_le hy hx

/-- Auxiliary lemma `norm_mul_le_one` for the local levels (`def:s01-levels`). -/
lemma norm_mul_le_one {x y : ℚ_[ℓ]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 :=
  norm_mul_le_of_le hx hy

/-- Auxiliary lemma `norm_sub_le_of_le` for the local levels (`def:s01-levels`). -/
lemma norm_sub_le_of_le {x y : ℚ_[ℓ]} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x - y‖ ≤ r := by
  rw [sub_eq_add_neg]; exact norm_add_le_of_le hx (by rwa [norm_neg])

/-- Auxiliary lemma `zpow_neg_le_one` for the local levels (`def:s01-levels`). -/
lemma zpow_neg_le_one (e : ℕ) : (ℓ : ℝ) ^ (-(e : ℤ)) ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le) (by simp)

end Aux

/-- The `(2,2)` matrix-product entries, unfolded (`def:s01-levels`). -/
lemma mul_val_apply (g h : GL (Fin 2) ℚ_[ℓ]) (i j : Fin 2) :
    (Units.val (g * h)) i j = (Units.val g) i 0 * (Units.val h) 0 j
      + (Units.val g) i 1 * (Units.val h) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Entries of the inverse: `g⁻¹ = det⁻¹ • adjugate` (`def:s01-levels`). -/
lemma inv_val_eq (g : GL (Fin 2) ℚ_[ℓ]) :
    Units.val g⁻¹ = (Matrix.det (Units.val g))⁻¹ • (Units.val g).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def]
  simp

/-- Auxiliary lemma `inv_val_apply_00` for the local levels (`def:s01-levels`). -/
@[simp] lemma inv_val_apply_00 (g : GL (Fin 2) ℚ_[ℓ]) :
    (Units.val g⁻¹) 0 0 = (Units.val g) 1 1 / (Units.val g).det := by
  rw [inv_val_eq]; simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

/-- Auxiliary lemma `inv_val_apply_01` for the local levels (`def:s01-levels`). -/
@[simp] lemma inv_val_apply_01 (g : GL (Fin 2) ℚ_[ℓ]) :
    (Units.val g⁻¹) 0 1 = -(Units.val g) 0 1 / (Units.val g).det := by
  rw [inv_val_eq]; simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

/-- Auxiliary lemma `inv_val_apply_10` for the local levels (`def:s01-levels`). -/
@[simp] lemma inv_val_apply_10 (g : GL (Fin 2) ℚ_[ℓ]) :
    (Units.val g⁻¹) 1 0 = -(Units.val g) 1 0 / (Units.val g).det := by
  rw [inv_val_eq]; simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

/-- Auxiliary lemma `inv_val_apply_11` for the local levels (`def:s01-levels`). -/
@[simp] lemma inv_val_apply_11 (g : GL (Fin 2) ℚ_[ℓ]) :
    (Units.val g⁻¹) 1 1 = (Units.val g) 0 0 / (Units.val g).det := by
  rw [inv_val_eq]; simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

/-- Auxiliary lemma `det_ne_zero` for the local levels (`def:s01-levels`). -/
lemma det_ne_zero (g : GL (Fin 2) ℚ_[ℓ]) : (Units.val g).det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero

variable (ℓ) in
/-- `GL₂(ℤ_ℓ)` inside `GL₂(ℚ_ℓ)`: all entries of `g` and of `g⁻¹` lie in `ℤ_ℓ`
(`def:s01-levels`). -/
def GL2Zl : Subgroup (GL (Fin 2) ℚ_[ℓ]) where
  carrier := {g | (∀ i j, ‖(Units.val g) i j‖ ≤ 1) ∧ ∀ i j, ‖(Units.val g⁻¹) i j‖ ≤ 1}
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [mul_val_apply]
      exact norm_add_le_of_le (norm_mul_le_one (hg _ _) (hh _ _)) (norm_mul_le_one (hg _ _) (hh _ _))
    · rw [_root_.mul_inv_rev, mul_val_apply]
      exact norm_add_le_of_le (norm_mul_le_one (hh' _ _) (hg' _ _)) (norm_mul_le_one (hh' _ _) (hg' _ _))
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨hg', by simpa using hg⟩

/-- Membership in `GL2Zl ℓ`, unfolded (`def:s01-levels`). -/
lemma mem_GL2Zl_def {g : GL (Fin 2) ℚ_[ℓ]} :
    g ∈ GL2Zl ℓ ↔ (∀ i j, ‖(Units.val g) i j‖ ≤ 1) ∧ ∀ i j, ‖(Units.val g⁻¹) i j‖ ≤ 1 := Iff.rfl

/-- Auxiliary lemma `norm_det_mul_inv` for the local levels (`def:s01-levels`). -/
lemma norm_det_mul_inv (g : GL (Fin 2) ℚ_[ℓ]) :
    ‖(Units.val g).det‖ * ‖(Units.val g⁻¹).det‖ = 1 := by
  rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one,
    norm_one]

/-- Auxiliary lemma `norm_det_le_one` for the local levels (`def:s01-levels`). -/
lemma norm_det_le_one {M : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]} (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two]
  exact norm_sub_le_of_le (norm_mul_le_one (h _ _) (h _ _)) (norm_mul_le_one (h _ _) (h _ _))

/-- Characterisation of `GL₂(ℤ_ℓ)`: integral entries and a determinant of norm `1`
(`def:s01-levels`). -/
lemma mem_GL2Zl_iff {g : GL (Fin 2) ℚ_[ℓ]} :
    g ∈ GL2Zl ℓ ↔ (∀ i j, ‖(Units.val g) i j‖ ≤ 1) ∧ ‖(Units.val g).det‖ = 1 := by
  constructor
  · rintro ⟨hg, hg'⟩
    refine ⟨hg, le_antisymm (norm_det_le_one hg) ?_⟩
    have h1 := norm_det_mul_inv g
    have h2 := norm_det_le_one hg'
    have h3 : 0 ≤ ‖(Units.val g⁻¹).det‖ := norm_nonneg _
    nlinarith [norm_nonneg (Units.val g).det]
  · rintro ⟨hg, hd⟩
    refine ⟨hg, fun i j => ?_⟩
    have hd' : ‖(Units.val g).det‖⁻¹ = 1 := by rw [hd]; simp
    fin_cases i <;> fin_cases j <;>
      simp [norm_div, hd] <;> simpa using hg _ _

/-- `det` of an element of `GL₂(ℤ_ℓ)` is a `ℤ_ℓ`-unit (`def:s01-levels`). -/
lemma det_isUnit_of_mem_GL2Zl {g : GL (Fin 2) ℚ_[ℓ]} (hg : g ∈ GL2Zl ℓ) :
    ∃ x : ℤ_[ℓ], IsUnit x ∧ (x : ℚ_[ℓ]) = (Units.val g).det := by
  obtain ⟨h1, h2⟩ := mem_GL2Zl_iff.1 hg
  refine ⟨⟨_, show (Units.val g).det ∈ PadicInt.subring ℓ from h2.le⟩, ?_, rfl⟩
  exact PadicInt.isUnit_iff.2 h2

/-! ### Explicit matrices -/

/-- The element of `GL₂(ℚ_ℓ)` with matrix `!![a, b; c, d]`, given `a d - b c ≠ 0`. -/
noncomputable def matGL (a b c d : ℚ_[ℓ]) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℚ_[ℓ] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [Matrix.det_fin_two] using h)

/-- Auxiliary lemma `matGL_val` for the local levels (`def:s01-levels`). -/
@[simp] lemma matGL_val (a b c d : ℚ_[ℓ]) (h : a * d - b * c ≠ 0) :
    Units.val (matGL a b c d h) = !![a, b; c, d] := rfl

/-- The diagonal element `diag(a, d)` of `GL₂(ℚ_ℓ)`. -/
noncomputable def diagGL (a d : ℚ_[ℓ]ˣ) : GL (Fin 2) ℚ_[ℓ] :=
  matGL a 0 0 d (by simp)

/-- Auxiliary lemma `diagGL_val` for the local levels (`def:s01-levels`). -/
@[simp] lemma diagGL_val (a d : ℚ_[ℓ]ˣ) :
    Units.val (diagGL a d) = !![(a : ℚ_[ℓ]), 0; 0, d] := rfl

/-- The unit of `ℚ_ℓ` underlying a unit of `ℤ_ℓ`. -/
noncomputable def intUnit (u : ℤ_[ℓ]ˣ) : ℚ_[ℓ]ˣ := Units.map (PadicInt.Coe.ringHom (p := ℓ)).toMonoidHom u

/-- Auxiliary lemma `coe_intUnit` for the local levels (`def:s01-levels`). -/
@[simp] lemma coe_intUnit (u : ℤ_[ℓ]ˣ) : ((intUnit u : ℚ_[ℓ]ˣ) : ℚ_[ℓ]) = ((u : ℤ_[ℓ]) : ℚ_[ℓ]) := rfl

/-- Auxiliary lemma `norm_intUnit` for the local levels (`def:s01-levels`). -/
@[simp] lemma norm_intUnit (u : ℤ_[ℓ]ˣ) : ‖((intUnit u : ℚ_[ℓ]ˣ) : ℚ_[ℓ])‖ = 1 :=
  PadicInt.isUnit_iff.1 u.isUnit

/-- `matGL` is in `GL₂(ℤ_ℓ)` iff its entries are integral and the determinant has norm `1`
(`def:s01-levels`). -/
lemma matGL_mem_GL2Zl_iff (a b c d : ℚ_[ℓ]) (h : a * d - b * c ≠ 0) :
    matGL a b c d h ∈ GL2Zl ℓ ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 ∧ ‖d‖ ≤ 1 ∧ ‖a * d - b * c‖ = 1 := by
  rw [mem_GL2Zl_iff]
  simp only [matGL_val, Matrix.det_fin_two_of]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using h1 0 0, by simpa using h1 0 1, by simpa using h1 1 0,
      by simpa using h1 1 1, h2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨fun i j => by fin_cases i <;> fin_cases j <;> simpa, h5⟩

/-! ### The levels -/

variable (ℓ)

/-- `K0 ℓ e`: matrices in `GL₂(ℤ_ℓ)` with lower-left entry `c` satisfying `v(c) ≥ e`
(`def:s01-levels`, `U_{0,ℓ}` at level `ℓ^e`). -/
def K0 (e : ℕ) : Subgroup (GL (Fin 2) ℚ_[ℓ]) where
  carrier := {g | g ∈ GL2Zl ℓ ∧ ‖(Units.val g) 1 0‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ))}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg1⟩ ⟨hh, hh1⟩
    refine ⟨mul_mem hg hh, ?_⟩
    rw [mul_val_apply]
    exact norm_add_le_of_le (norm_mul_le_of_le hg1 ((mem_GL2Zl_iff.1 hh).1 _ _))
      (norm_mul_le_of_le' ((mem_GL2Zl_iff.1 hg).1 _ _) hh1)
  inv_mem' := by
    rintro g ⟨hg, hg1⟩
    refine ⟨inv_mem hg, ?_⟩
    rw [inv_val_apply_10, norm_div, norm_neg, (mem_GL2Zl_iff.1 hg).2, div_one]
    exact hg1

/-- `K1 ℓ e`: `K0 ℓ e` together with `v(d - 1) ≥ e` (`def:s01-levels`, `U_{1,ℓ}` at level `ℓ^e`). -/
def K1 (e : ℕ) : Subgroup (GL (Fin 2) ℚ_[ℓ]) where
  carrier := {g | g ∈ K0 ℓ e ∧ ‖(Units.val g) 1 1 - 1‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ))}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg1⟩ ⟨hh, hh1⟩
    refine ⟨mul_mem hg hh, ?_⟩
    have e1 : (Units.val (g * h)) 1 1 - 1 =
        (Units.val g) 1 0 * (Units.val h) 0 1 + ((Units.val g) 1 1 - 1) * (Units.val h) 1 1
          + ((Units.val h) 1 1 - 1) := by
      rw [mul_val_apply]; ring
    rw [e1]
    exact norm_add_le_of_le (norm_add_le_of_le
      (norm_mul_le_of_le hg.2 ((mem_GL2Zl_iff.1 hh.1).1 _ _))
      (norm_mul_le_of_le hg1 ((mem_GL2Zl_iff.1 hh.1).1 _ _))) hh1
  inv_mem' := by
    rintro g ⟨hg, hg1⟩
    refine ⟨inv_mem hg, ?_⟩
    have hd := (mem_GL2Zl_iff.1 hg.1).2
    have hdne := det_ne_zero g
    have e1 : (Units.val g⁻¹) 1 1 - 1 =
        ((Units.val g) 0 0 * (1 - (Units.val g) 1 1) + (Units.val g) 0 1 * (Units.val g) 1 0)
          / (Units.val g).det := by
      rw [inv_val_apply_11, div_sub_one hdne]
      simp only [Matrix.det_fin_two]
      congr 1; ring
    rw [e1, norm_div, hd, div_one]
    have hi := (mem_GL2Zl_iff.1 hg.1).1
    refine norm_add_le_of_le (norm_mul_le_of_le' (hi 0 0) ?_) (norm_mul_le_of_le' (hi 0 1) hg.2)
    rwa [norm_sub_rev]

/-- The Iwahori subgroup `Iw ℓ = K0 ℓ 1` (`def:s01-levels`). -/
abbrev Iw : Subgroup (GL (Fin 2) ℚ_[ℓ]) := K0 ℓ 1

variable {ℓ}

/-- Auxiliary lemma `mem_K0_iff` for the local levels (`def:s01-levels`). -/
lemma mem_K0_iff {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} :
    g ∈ K0 ℓ e ↔ g ∈ GL2Zl ℓ ∧ ‖(Units.val g) 1 0‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := Iff.rfl

/-- Auxiliary lemma `mem_K1_iff` for the local levels (`def:s01-levels`). -/
lemma mem_K1_iff {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} :
    g ∈ K1 ℓ e ↔ g ∈ K0 ℓ e ∧ ‖(Units.val g) 1 1 - 1‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := Iff.rfl

/-- Auxiliary lemma `K1_le_K0` for the local levels (`def:s01-levels`). -/
lemma K1_le_K0 (e : ℕ) : K1 ℓ e ≤ K0 ℓ e := fun _ h => h.1

/-- Auxiliary lemma `K0_le_GL2Zl` for the local levels (`def:s01-levels`). -/
lemma K0_le_GL2Zl (e : ℕ) : K0 ℓ e ≤ GL2Zl ℓ := fun _ h => h.1

/-- Auxiliary lemma `K1_le_GL2Zl` for the local levels (`def:s01-levels`). -/
lemma K1_le_GL2Zl (e : ℕ) : K1 ℓ e ≤ GL2Zl ℓ := (K1_le_K0 e).trans (K0_le_GL2Zl e)

/-- `K0 ℓ 0 = GL₂(ℤ_ℓ)` (`def:s01-levels`, level `1`). -/
lemma K0_zero : K0 ℓ 0 = GL2Zl ℓ := by
  refine le_antisymm (K0_le_GL2Zl 0) fun g hg => ⟨hg, ?_⟩
  simpa using (mem_GL2Zl_iff.1 hg).1 1 0

/-- `K1 ℓ 0 = GL₂(ℤ_ℓ)` (`def:s01-levels`, level `1`). -/
lemma K1_zero : K1 ℓ 0 = GL2Zl ℓ := by
  refine le_antisymm (K1_le_GL2Zl (ℓ := ℓ) 0) fun g hg => ?_
  have := (mem_GL2Zl_iff.1 hg).1
  exact ⟨⟨hg, by simpa using this 1 0⟩,
    by simpa using norm_sub_le_of_le (this 1 1) (by simp : ‖(1 : ℚ_[ℓ])‖ ≤ 1)⟩

/-- Auxiliary lemma `zpow_neg_anti` for the local levels (`def:s01-levels`). -/
lemma zpow_neg_anti {e e' : ℕ} (h : e ≤ e') : (ℓ : ℝ) ^ (-(e' : ℤ)) ≤ (ℓ : ℝ) ^ (-(e : ℤ)) :=
  zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le) (by simpa using h)

/-- The tower `K0 ℓ e` is antitone in `e` (`def:s01-levels`). -/
lemma K0_anti {e e' : ℕ} (h : e ≤ e') : K0 ℓ e' ≤ K0 ℓ e :=
  fun _ hg => ⟨hg.1, hg.2.trans (zpow_neg_anti h)⟩

/-- The tower `K1 ℓ e` is antitone in `e` (`def:s01-levels`). -/
lemma K1_anti {e e' : ℕ} (h : e ≤ e') : K1 ℓ e' ≤ K1 ℓ e :=
  fun _ hg => ⟨K0_anti h hg.1, hg.2.trans (zpow_neg_anti h)⟩

/-- Auxiliary lemma `K0_succ_le` for the local levels (`def:s01-levels`). -/
lemma K0_succ_le (e : ℕ) : K0 ℓ (e + 1) ≤ K0 ℓ e := K0_anti (Nat.le_succ e)

/-- Auxiliary lemma `K1_succ_le` for the local levels (`def:s01-levels`). -/
lemma K1_succ_le (e : ℕ) : K1 ℓ (e + 1) ≤ K1 ℓ e := K1_anti (Nat.le_succ e)

/-- Divisibility form of the valuation condition (`def:s01-levels`). -/
lemma norm_le_zpow_iff {x : ℚ_[ℓ]} (hx : ‖x‖ ≤ 1) (e : ℕ) :
    ‖x‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) ↔ ∃ c : ℤ_[ℓ], x = (ℓ : ℚ_[ℓ]) ^ e * c := by
  obtain ⟨y, rfl⟩ : ∃ y : ℤ_[ℓ], (y : ℚ_[ℓ]) = x := ⟨⟨x, hx⟩, rfl⟩
  have := PadicInt.norm_le_pow_iff_mem_span_pow y e
  change ‖(y : ℚ_[ℓ])‖ ≤ _ ↔ _ at this ⊢
  rw [this, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have := congrArg (fun z : ℤ_[ℓ] => (z : ℚ_[ℓ])) hc
    simp at this
    rw [← this]; ring
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [mul_comm] using hc.symm

/-- Entries of an element of `GL₂(ℤ_ℓ)` as `ℤ_ℓ`-elements: the characterisation behind
`mem_K0_iff_exists` (`def:s01-levels`). -/
lemma mem_GL2Zl_iff_exists {g : GL (Fin 2) ℚ_[ℓ]} :
    g ∈ GL2Zl ℓ ↔ ∃ a b c d : ℤ_[ℓ], Units.val g = !![(a : ℚ_[ℓ]), b; c, d] ∧
      IsUnit (a * d - b * c) := by
  rw [mem_GL2Zl_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨_, h1 0 0⟩, ⟨_, h1 0 1⟩, ⟨_, h1 1 0⟩, ⟨_, h1 1 1⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · apply PadicInt.isUnit_iff.2
      rw [← h2, Matrix.det_fin_two]
      rfl
  · rintro ⟨a, b, c, d, hM, hu⟩
    have hdet : (Units.val g).det = ((a * d - b * c : ℤ_[ℓ]) : ℚ_[ℓ]) := by
      rw [hM]; simp [Matrix.det_fin_two]
    refine ⟨fun i j => ?_, by rw [hdet]; exact PadicInt.isUnit_iff.1 hu⟩
    rw [hM]
    fin_cases i <;> fin_cases j <;> simpa using PadicInt.norm_le_one _

/-- Membership in `K0 ℓ e` by entries (`def:s01-levels`). -/
lemma mem_K0_iff_exists {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} :
    g ∈ K0 ℓ e ↔ ∃ a b c d : ℤ_[ℓ], Units.val g = !![(a : ℚ_[ℓ]), b; c, d] ∧
      IsUnit (a * d - b * c) ∧ (ℓ : ℤ_[ℓ]) ^ e ∣ c := by
  constructor
  · rintro ⟨hg, hc⟩
    obtain ⟨a, b, c, d, hM, hu⟩ := mem_GL2Zl_iff_exists.1 hg
    refine ⟨a, b, c, d, hM, hu, ?_⟩
    have hc' : ‖(c : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by simpa [hM] using hc
    obtain ⟨c', hc'⟩ := (norm_le_zpow_iff (PadicInt.norm_le_one c) e).1 hc'
    refine ⟨c', ?_⟩
    apply Subtype.ext
    simpa using hc'
  · rintro ⟨a, b, c, d, hM, hu, ⟨c', hc'⟩⟩
    refine ⟨mem_GL2Zl_iff_exists.2 ⟨a, b, c, d, hM, hu⟩, ?_⟩
    have : (c : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) ^ e * c' := by rw [hc']; simp
    have h2 := (norm_le_zpow_iff (PadicInt.norm_le_one c) e).2 ⟨c', this⟩
    simpa [hM] using h2

/-- Membership in `K1 ℓ e` by entries (`def:s01-levels`). -/
lemma mem_K1_iff_exists {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} :
    g ∈ K1 ℓ e ↔ ∃ a b c d : ℤ_[ℓ], Units.val g = !![(a : ℚ_[ℓ]), b; c, d] ∧
      IsUnit (a * d - b * c) ∧ (ℓ : ℤ_[ℓ]) ^ e ∣ c ∧ (ℓ : ℤ_[ℓ]) ^ e ∣ d - 1 := by
  constructor
  · rintro ⟨hg, hd⟩
    obtain ⟨a, b, c, d, hM, hu, hc⟩ := mem_K0_iff_exists.1 hg
    refine ⟨a, b, c, d, hM, hu, hc, ?_⟩
    have hd' : ‖((d - 1 : ℤ_[ℓ]) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by simpa [hM] using hd
    obtain ⟨c', hc'⟩ := (norm_le_zpow_iff (PadicInt.norm_le_one _) e).1 hd'
    refine ⟨c', ?_⟩
    apply Subtype.ext
    simpa using hc'
  · rintro ⟨a, b, c, d, hM, hu, hc, ⟨c', hc'⟩⟩
    refine ⟨mem_K0_iff_exists.2 ⟨a, b, c, d, hM, hu, hc⟩, ?_⟩
    have : ((d - 1 : ℤ_[ℓ]) : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) ^ e * c' := by rw [hc']; simp
    have h2 := (norm_le_zpow_iff (PadicInt.norm_le_one _) e).2 ⟨c', this⟩
    simpa [hM] using h2

/-- Explicit entries of an element of `K1` (`def:s01-levels`). -/
lemma mem_K0_of_entries {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} (a b c d : ℤ_[ℓ])
    (hM : Units.val g = !![(a : ℚ_[ℓ]), b; c, d]) (hu : IsUnit (a * d - b * c))
    (hc : (ℓ : ℤ_[ℓ]) ^ e ∣ c) : g ∈ K0 ℓ e :=
  mem_K0_iff_exists.2 ⟨a, b, c, d, hM, hu, hc⟩

/-- Auxiliary lemma `mem_K1_of_entries` for the local levels (`def:s01-levels`). -/
lemma mem_K1_of_entries {g : GL (Fin 2) ℚ_[ℓ]} {e : ℕ} (a b c d : ℤ_[ℓ])
    (hM : Units.val g = !![(a : ℚ_[ℓ]), b; c, d]) (hu : IsUnit (a * d - b * c))
    (hc : (ℓ : ℤ_[ℓ]) ^ e ∣ c) (hd : (ℓ : ℤ_[ℓ]) ^ e ∣ d - 1) : g ∈ K1 ℓ e :=
  mem_K1_iff_exists.2 ⟨a, b, c, d, hM, hu, hc, hd⟩

/-- Auxiliary lemma `mem_GL2Zl_of_entries` for the local levels (`def:s01-levels`). -/
lemma mem_GL2Zl_of_entries {g : GL (Fin 2) ℚ_[ℓ]} (a b c d : ℤ_[ℓ])
    (hM : Units.val g = !![(a : ℚ_[ℓ]), b; c, d]) (hu : IsUnit (a * d - b * c)) :
    g ∈ GL2Zl ℓ :=
  mem_GL2Zl_iff_exists.2 ⟨a, b, c, d, hM, hu⟩

/-! ### Diagonal elements -/

/-- `diag(u, 1) ∈ K0 ℓ e` for a `ℤ_ℓ`-unit `u` (`def:s01-levels`). -/
lemma diag_one_mem_K0 (u : ℤ_[ℓ]ˣ) (e : ℕ) : diagGL (intUnit u) 1 ∈ K0 ℓ e := by
  refine mem_K0_of_entries u 0 0 1 (by simp) (by simp) ?_
  exact dvd_zero _

/-- `diag(1, u) ∈ K0 ℓ e` for a `ℤ_ℓ`-unit `u` (`def:s01-levels`). -/
lemma one_diag_mem_K0 (u : ℤ_[ℓ]ˣ) (e : ℕ) : diagGL 1 (intUnit u) ∈ K0 ℓ e := by
  refine mem_K0_of_entries 1 0 0 u (by simp) (by simp) ?_
  exact dvd_zero _

/-- `diag(u, 1) ∈ K1 ℓ e` for every `ℤ_ℓ`-unit `u` (`def:s01-levels`). -/
lemma diag_one_mem_K1 (u : ℤ_[ℓ]ˣ) (e : ℕ) : diagGL (intUnit u) 1 ∈ K1 ℓ e := by
  refine mem_K1_of_entries u 0 0 1 (by simp) (by simp) (dvd_zero _) ?_
  simp

/-- `diag(1, u) ∈ K1 ℓ e` iff `u ≡ 1 mod ℓ^e` (`def:s01-levels`). -/
lemma one_diag_mem_K1_iff (u : ℤ_[ℓ]ˣ) (e : ℕ) :
    diagGL 1 (intUnit u) ∈ K1 ℓ e ↔ (ℓ : ℤ_[ℓ]) ^ e ∣ (u : ℤ_[ℓ]) - 1 := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, hM, -, -, hd⟩ := mem_K1_iff_exists.1 h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[ℓ] => M 1 1) hM
    simp at h11
    have : d = u := by apply Subtype.ext; simpa using h11.symm
    rwa [this] at hd
  · intro h
    exact mem_K1_of_entries 1 0 0 u (by simp) (by simp) (dvd_zero _) h

/-- Deprecated misleading alias of `one_diag_mem_K1_iff` (about `diag(1, u)`, not `diag(u, 1)`; compare
`diag_one_mem_K0`, `diag_one_mem_K1`, which are about `diag(u, 1)`). -/
@[deprecated one_diag_mem_K1_iff (since := "2026-11-14")]
lemma diag_one_mem_K1_iff (u : ℤ_[ℓ]ˣ) (e : ℕ) :
    diagGL 1 (intUnit u) ∈ K1 ℓ e ↔ (ℓ : ℤ_[ℓ]) ^ e ∣ (u : ℤ_[ℓ]) - 1 :=
  one_diag_mem_K1_iff u e

end Langlandscape.Local
