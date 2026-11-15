/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.GL2Levels
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The `N_{U_p}` coset decomposition (S01-L9)

Tex labels `def:s01-NUp` and `lem:s01-Up` (a), (c).  With `ϖ = diag(p, 1)` and
`ϖ_j = !![p, j; 0, 1]` (`0 ≤ j < p`) we prove, for `s ≥ 1`,

* `K1 p s * {ϖ} * K1 p s = ⋃ j, ϖ_j • K1 p s` and the same for `K0 p s`
  (`K1_mul_varpi_mul_K1`, `K0_mul_varpi_mul_K0`);
* the cosets `ϖ_j K1 p s` are pairwise distinct (`varpi_inv_mul_not_mem`, any `s`);
* the same `ϖ_j` represent the levels `s` and `s + 1` (`reps_indep`);
* for `diag(1, p)` the representatives `!![1, 0; p^s j, p]` depend on `s` (`diag1p_reps`);
* `[K1 p s : K1 p (s + 1)] = p ^ 2` (`relIndex_K1_succ`).

Everything is explicit `2 × 2` matrix algebra over `ℤ_[p]`.  Membership of a quotient
`g⁻¹ * h` in a level is proved by exhibiting its integral entries `M` with `g * M = h`
(`inv_mul_mem_K0`, `inv_mul_mem_K1`), so no inverse is ever computed entrywise.
-/

open Matrix Pointwise

namespace Langlandscape.Local

variable {p : ℕ} [Fact p.Prime]

/-! ### Arithmetic in `ℤ_[p]` -/

/-- `p ∣ x` iff `x` reduces to `0` in `ZMod p` (auxiliary, `lem:s01-Up`). -/
lemma dvd_iff_toZMod_eq_zero (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]

/-- A `p`-adic integer is a unit iff it is not divisible by `p` (auxiliary, `lem:s01-Up`). -/
lemma isUnit_iff_not_dvd (x : ℤ_[p]) : IsUnit x ↔ ¬ (p : ℤ_[p]) ∣ x := by
  rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.not_isUnit_iff, not_not]

/-- Two residues `x, y < p` that are congruent mod `p` in `ℤ_[p]` are equal
(auxiliary, `lem:s01-Up`). -/
lemma fin_eq_of_dvd {x y : Fin p}
    (h : (p : ℤ_[p]) ∣ ((x : ℕ) : ℤ_[p]) - ((y : ℕ) : ℤ_[p])) : x = y := by
  rw [dvd_iff_toZMod_eq_zero] at h
  simp only [map_sub, map_natCast] at h
  rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt x.isLt,
    Nat.mod_eq_of_lt y.isLt] at h
  exact Fin.ext h

/-- For a unit `u` and any `b` there is a residue `j < p` with `b ≡ j u mod p`
(auxiliary, `lem:s01-Up`). -/
lemma exists_fin_dvd (u b : ℤ_[p]) (hu : IsUnit u) :
    ∃ j : Fin p, (p : ℤ_[p]) ∣ b - ((j : ℕ) : ℤ_[p]) * u := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hu' : PadicInt.toZMod u ≠ 0 := fun h =>
    (isUnit_iff_not_dvd u).1 hu ((dvd_iff_toZMod_eq_zero u).2 h)
  refine ⟨⟨(PadicInt.toZMod b * (PadicInt.toZMod u)⁻¹).val, ZMod.val_lt _⟩, ?_⟩
  rw [dvd_iff_toZMod_eq_zero]
  simp only [map_sub, map_mul, map_natCast, ZMod.natCast_zmod_val]
  rw [inv_mul_cancel_right₀ hu', sub_self]

/-! ### Matrix helpers -/

/-- Entrywise equality of `2 × 2` matrix literals (auxiliary, `lem:s01-Up`). -/
lemma mat_eq {R : Type*} {a b c d a' b' c' d' : R} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

/-- If `g * M = h` then `g⁻¹ * h` has matrix `M` (auxiliary, `lem:s01-Up`). -/
lemma val_inv_mul_eq {g h : GL (Fin 2) ℚ_[p]} {M : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (H : Units.val g * M = Units.val h) : Units.val (g⁻¹ * h) = M := by
  rw [Units.val_mul, ← H, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- If `g * M = h` with `M` integral and `‖det g‖ = ‖det h‖`, then `det M` is a unit
(auxiliary, `lem:s01-Up`). -/
lemma isUnit_of_mul_eq {g h : GL (Fin 2) ℚ_[p]} {a b c d : ℤ_[p]}
    (H : Units.val g * !![(a : ℚ_[p]), b; c, d] = Units.val h)
    (hdet : ‖(Units.val g).det‖ = ‖(Units.val h).det‖) : IsUnit (a * d - b * c) := by
  have h1 := congrArg Matrix.det H
  rw [Matrix.det_mul, Matrix.det_fin_two_of] at h1
  have h2 : ‖(Units.val h).det‖ * ‖(a : ℚ_[p]) * d - b * c‖ = ‖(Units.val h).det‖ * 1 := by
    rw [mul_one, ← hdet, ← norm_mul, h1, hdet]
  have h3 := mul_left_cancel₀ (norm_ne_zero_iff.2 (det_ne_zero h)) h2
  rw [PadicInt.isUnit_iff, PadicInt.norm_def]
  push_cast
  exact h3

/-- `g⁻¹ * h ∈ K0 p e` from integral entries `M` with `g * M = h` (auxiliary, `lem:s01-Up`). -/
lemma inv_mul_mem_K0 {g h : GL (Fin 2) ℚ_[p]} {e : ℕ} (a b c d : ℤ_[p])
    (H : Units.val g * !![(a : ℚ_[p]), b; c, d] = Units.val h)
    (hdet : ‖(Units.val g).det‖ = ‖(Units.val h).det‖) (hc : (p : ℤ_[p]) ^ e ∣ c) :
    g⁻¹ * h ∈ K0 p e :=
  mem_K0_of_entries a b c d (val_inv_mul_eq H) (isUnit_of_mul_eq H hdet) hc

/-- `g⁻¹ * h ∈ K1 p e` from integral entries `M` with `g * M = h` (auxiliary, `lem:s01-Up`). -/
lemma inv_mul_mem_K1 {g h : GL (Fin 2) ℚ_[p]} {e : ℕ} (a b c d : ℤ_[p])
    (H : Units.val g * !![(a : ℚ_[p]), b; c, d] = Units.val h)
    (hdet : ‖(Units.val g).det‖ = ‖(Units.val h).det‖) (hc : (p : ℤ_[p]) ^ e ∣ c)
    (hd : (p : ℤ_[p]) ^ e ∣ d - 1) : g⁻¹ * h ∈ K1 p e :=
  mem_K1_of_entries a b c d (val_inv_mul_eq H) (isUnit_of_mul_eq H hdet) hc hd

/-- Membership in `K1 p e` from integral entries and `‖det‖ = 1` (auxiliary, `lem:s01-Up`). -/
lemma mem_K1_of_val {g : GL (Fin 2) ℚ_[p]} {e : ℕ} (a b c d : ℤ_[p])
    (hM : Units.val g = !![(a : ℚ_[p]), b; c, d]) (hdet : ‖(Units.val g).det‖ = 1)
    (hc : (p : ℤ_[p]) ^ e ∣ c) (hd : (p : ℤ_[p]) ^ e ∣ d - 1) : g ∈ K1 p e := by
  refine mem_K1_of_entries a b c d hM ?_ hc hd
  rw [hM, Matrix.det_fin_two_of] at hdet
  rw [PadicInt.isUnit_iff, PadicInt.norm_def]
  push_cast
  exact hdet

/-! ### The matrices -/

variable (p) in
/-- `ϖ = diag(p, 1)`, the element defining `U_p` in the normalisation `N_{U_p}`
(`def:s01-NUp`). -/
noncomputable def varpiDiag : GL (Fin 2) ℚ_[p] :=
  matGL (p : ℚ_[p]) 0 0 1 (by simp [(Fact.out : p.Prime).ne_zero])

variable (p) in
/-- The coset representatives `ϖ_j = !![p, j; 0, 1]`, `0 ≤ j < p`, of `def:s01-NUp`. -/
noncomputable def varpi (j : Fin p) : GL (Fin 2) ℚ_[p] :=
  matGL (p : ℚ_[p]) ((j : ℕ) : ℚ_[p]) 0 1 (by simp [(Fact.out : p.Prime).ne_zero])

variable (p) in
/-- The unipotent `!![1, j; 0, 1]` with `ϖ_j = !![1, j; 0, 1] * ϖ` (auxiliary, `lem:s01-Up`). -/
noncomputable def unipUpper (j : Fin p) : GL (Fin 2) ℚ_[p] :=
  matGL 1 ((j : ℕ) : ℚ_[p]) 0 1 (by simp)

variable (p) in
/-- `diag(1, p)`, the element of the seed's literal operator `U'_p` (`lem:s01-Up`(c)). -/
noncomputable def diagOneP : GL (Fin 2) ℚ_[p] :=
  matGL 1 0 0 (p : ℚ_[p]) (by simp [(Fact.out : p.Prime).ne_zero])

variable (p) in
/-- The representatives `!![1, 0; p^s j, p]` of `K1 p s * diag(1, p) * K1 p s`
(`lem:s01-Up`(c)). -/
noncomputable def varpiPrime (s : ℕ) (j : Fin p) : GL (Fin 2) ℚ_[p] :=
  matGL 1 0 ((p : ℚ_[p]) ^ s * ((j : ℕ) : ℚ_[p])) (p : ℚ_[p])
    (by simp [(Fact.out : p.Prime).ne_zero])

variable (p) in
/-- The unipotent `!![1, 0; p^s j, 1]` (auxiliary, `lem:s01-Up`(c)). -/
noncomputable def unipLower (s : ℕ) (j : Fin p) : GL (Fin 2) ℚ_[p] :=
  matGL 1 0 ((p : ℚ_[p]) ^ s * ((j : ℕ) : ℚ_[p])) 1 (by simp)

variable (p) in
/-- `!![1, 0; p^s x, 1 + p^s y]`; their inverses represent `K1 p s / K1 p (s + 1)`
(auxiliary, `lem:s01-Up`). -/
noncomputable def sigmaRep (s : ℕ) (x y : Fin p) : GL (Fin 2) ℚ_[p] :=
  matGL 1 0 ((p : ℚ_[p]) ^ s * ((x : ℕ) : ℚ_[p])) (1 + (p : ℚ_[p]) ^ s * ((y : ℕ) : ℚ_[p])) (by
    have h : ((p ^ s * (y : ℕ) + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] at h
    rw [one_mul, zero_mul, sub_zero, add_comm]
    exact h)

/-- `ϖ_j = !![1, j; 0, 1] * diag(p, 1)` (`def:s01-NUp`). -/
lemma varpi_eq (j : Fin p) : varpi p j = unipUpper p j * varpiDiag p := by
  apply Units.ext
  simp [varpi, unipUpper, varpiDiag]

/-- `!![1, 0; p^s j, p] = !![1, 0; p^s j, 1] * diag(1, p)` (`lem:s01-Up`(c)). -/
lemma varpiPrime_eq (s : ℕ) (j : Fin p) : varpiPrime p s j = unipLower p s j * diagOneP p := by
  apply Units.ext
  simp [varpiPrime, unipLower, diagOneP]

/-- `!![1, j; 0, 1] ∈ K1 p s` (auxiliary, `lem:s01-Up`). -/
lemma unipUpper_mem {s : ℕ} (j : Fin p) : unipUpper p j ∈ K1 p s :=
  mem_K1_of_entries 1 ((j : ℕ) : ℤ_[p]) 0 1 (by simp [unipUpper]) (by simp) (dvd_zero _)
    (by simp)

/-- `!![1, 0; p^s j, 1] ∈ K1 p s` (auxiliary, `lem:s01-Up`(c)). -/
lemma unipLower_mem {s : ℕ} (j : Fin p) : unipLower p s j ∈ K1 p s :=
  mem_K1_of_entries 1 0 ((p : ℤ_[p]) ^ s * ((j : ℕ) : ℤ_[p])) 1 (by simp [unipLower]) (by simp)
    (dvd_mul_right _ _) (by simp)

/-! ### `K s ϖ K s = ⊔ ϖ_j K s` -/

/-- Core of `lem:s01-Up`(a): for `k ∈ K0 p s` (`s ≥ 1`) there is `j` with
`ϖ_j⁻¹ k ϖ ∈ K0 p s`, and in `K1 p s` if `k ∈ K1 p s`. -/
lemma exists_varpi_inv_mul {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K0 p s) :
    ∃ j : Fin p, (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K0 p s ∧
      (k ∈ K1 p s → (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K1 p s) := by
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 (K0_le_GL2Zl s hk)).2
  obtain ⟨a, b, c, d, hM, hu, hc⟩ := mem_K0_iff_exists.1 hk
  have hpc : (p : ℤ_[p]) ∣ c := (dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans hc
  have hd : IsUnit d := by
    rw [isUnit_iff_not_dvd] at hu ⊢
    exact fun h => hu (dvd_sub (dvd_mul_of_dvd_right h a) (dvd_mul_of_dvd_right hpc b))
  obtain ⟨j, β, hβ⟩ := exists_fin_dvd d b hd
  have hb : b = (p : ℤ_[p]) * β + ((j : ℕ) : ℤ_[p]) * d := by linear_combination hβ
  subst hb
  have H : Units.val (varpi p j) *
      !![((a - ((j : ℕ) : ℤ_[p]) * c : ℤ_[p]) : ℚ_[p]), (β : ℚ_[p]);
        (((p : ℤ_[p]) * c : ℤ_[p]) : ℚ_[p]), (d : ℚ_[p])] = Units.val (k * varpiDiag p) := by
    rw [Units.val_mul, hM]
    simp only [varpi, varpiDiag, matGL_val, Matrix.mul_fin_two]
    refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
  have hdet : ‖(Units.val (varpi p j)).det‖ = ‖(Units.val (k * varpiDiag p)).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, hkdet, one_mul]
    simp [varpi, varpiDiag, Matrix.det_fin_two_of]
  have h0 : (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K0 p s :=
    inv_mul_mem_K0 _ _ _ _ H hdet (dvd_mul_of_dvd_right hc _)
  refine ⟨j, h0, fun hk1 => mem_K1_iff.2 ⟨h0, ?_⟩⟩
  have h11 := (mem_K1_iff.1 hk1).2
  rw [val_inv_mul_eq H]
  rw [hM] at h11
  simpa using h11

/-- `lem:s01-Up`(a) at level `K0`: `K0 p s * {ϖ} * K0 p s = ⋃ j, ϖ_j • K0 p s` for `s ≥ 1`
(`def:s01-NUp`). -/
theorem K0_mul_varpi_mul_K0 {s : ℕ} (hs : 1 ≤ s) :
    (K0 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K0 p s =
      ⋃ j : Fin p, varpi p j • (K0 p s : Set (GL (Fin 2) ℚ_[p])) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, k', hk', rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨j, hj, -⟩ := exists_varpi_inv_mul hs (SetLike.mem_coe.1 hk)
    refine Set.mem_iUnion.2 ⟨j, Set.mem_smul_set.2
      ⟨_, SetLike.mem_coe.2 (mul_mem hj (SetLike.mem_coe.1 hk')), ?_⟩⟩
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hj
    rw [smul_eq_mul, varpi_eq]
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (SetLike.mem_coe.2 (K1_le_K0 s (unipUpper_mem j))) (Set.mem_singleton _)) hy

/-- `lem:s01-Up`(a), `def:s01-NUp`: `K1 p s * {ϖ} * K1 p s = ⋃ j, ϖ_j • K1 p s` for `s ≥ 1`. -/
theorem K1_mul_varpi_mul_K1 {s : ℕ} (hs : 1 ≤ s) :
    (K1 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p s =
      ⋃ j : Fin p, varpi p j • (K1 p s : Set (GL (Fin 2) ℚ_[p])) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, k', hk', rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hk1 : k ∈ K1 p s := SetLike.mem_coe.1 hk
    obtain ⟨j, -, hj⟩ := exists_varpi_inv_mul hs (K1_le_K0 s hk1)
    refine Set.mem_iUnion.2 ⟨j, Set.mem_smul_set.2
      ⟨_, SetLike.mem_coe.2 (mul_mem (hj hk1) (SetLike.mem_coe.1 hk')), ?_⟩⟩
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hj
    rw [smul_eq_mul, varpi_eq]
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (SetLike.mem_coe.2 (unipUpper_mem j)) (Set.mem_singleton _)) hy

/-- `def:s01-NUp`: the cosets `ϖ_j K1 p s` are pairwise distinct, since
`ϖ_j⁻¹ ϖ_{j'} = !![1, (j' - j)/p; 0, 1]` (for every `s`). -/
theorem varpi_inv_mul_not_mem {s : ℕ} {j j' : Fin p} (hjj' : j ≠ j') :
    (varpi p j)⁻¹ * varpi p j' ∉ K1 p s := by
  intro h
  obtain ⟨a, b, c, d, hM, -⟩ := mem_GL2Zl_iff_exists.1 (K1_le_GL2Zl s h)
  have H : Units.val (varpi p j') = Units.val (varpi p j) * !![(a : ℚ_[p]), b; c, d] := by
    rw [← hM, ← Units.val_mul, mul_inv_cancel_left]
  simp only [varpi, matGL_val, Matrix.mul_fin_two] at H
  have h01 : ((j' : ℕ) : ℚ_[p]) = (p : ℚ_[p]) * b + ((j : ℕ) : ℚ_[p]) * d :=
    congrFun (congrFun H 0) 1
  have h11 : (1 : ℚ_[p]) = 0 * b + 1 * d := congrFun (congrFun H 1) 1
  have hZ : ((j' : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * b := by
    apply PadicInt.ext
    push_cast
    linear_combination h01 - ((j : ℕ) : ℚ_[p]) * h11
  exact hjj' (fin_eq_of_dvd ⟨b, hZ⟩).symm

/-- `lem:s01-Up`(a): the representatives `ϖ_j` are the same at the levels `s` and `s + 1`
(`s ≥ 1`), for `K1` and for `K0` (`def:s01-NUp`). -/
theorem reps_indep {s : ℕ} (hs : 1 ≤ s) :
    ((K1 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p s =
        ⋃ j : Fin p, varpi p j • (K1 p s : Set (GL (Fin 2) ℚ_[p]))) ∧
      ((K1 p (s + 1) : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p (s + 1) =
        ⋃ j : Fin p, varpi p j • (K1 p (s + 1) : Set (GL (Fin 2) ℚ_[p]))) ∧
      ((K0 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K0 p s =
        ⋃ j : Fin p, varpi p j • (K0 p s : Set (GL (Fin 2) ℚ_[p]))) ∧
      ((K0 p (s + 1) : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K0 p (s + 1) =
        ⋃ j : Fin p, varpi p j • (K0 p (s + 1) : Set (GL (Fin 2) ℚ_[p]))) :=
  ⟨K1_mul_varpi_mul_K1 hs, K1_mul_varpi_mul_K1 (by omega), K0_mul_varpi_mul_K0 hs,
    K0_mul_varpi_mul_K0 (by omega)⟩

/-! ### `U'_p`: the representatives for `diag(1, p)` -/

/-- Core of `lem:s01-Up`(c): for `k ∈ K1 p s` (`s ≥ 1`) there is `j` with
`!![1, 0; p^s j, p]⁻¹ k diag(1, p) ∈ K1 p s`. -/
lemma exists_varpiPrime_inv_mul {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ K1 p s) : ∃ j : Fin p, (varpiPrime p s j)⁻¹ * (k * diagOneP p) ∈ K1 p s := by
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 (K1_le_GL2Zl s hk)).2
  obtain ⟨a, b, c, d, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hk
  have hpc : (p : ℤ_[p]) ∣ c := (dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans hc
  have ha : IsUnit a := by
    rw [isUnit_iff_not_dvd] at hu ⊢
    exact fun h => hu (dvd_sub (dvd_mul_of_dvd_left h d) (dvd_mul_of_dvd_right hpc b))
  obtain ⟨γ, hγ⟩ := hc
  subst hγ
  obtain ⟨j, η, hη⟩ := exists_fin_dvd a γ ha
  have hγ' : γ = ((j : ℕ) : ℤ_[p]) * a + (p : ℤ_[p]) * η := by linear_combination hη
  subst hγ'
  have H : Units.val (varpiPrime p s j) *
      !![(a : ℚ_[p]), (((p : ℤ_[p]) * b : ℤ_[p]) : ℚ_[p]);
        (((p : ℤ_[p]) ^ s * η : ℤ_[p]) : ℚ_[p]),
        ((d - (p : ℤ_[p]) ^ s * ((j : ℕ) : ℤ_[p]) * b : ℤ_[p]) : ℚ_[p])] =
      Units.val (k * diagOneP p) := by
    rw [Units.val_mul, hM]
    simp only [varpiPrime, diagOneP, matGL_val, Matrix.mul_fin_two]
    refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
  have hdet : ‖(Units.val (varpiPrime p s j)).det‖ = ‖(Units.val (k * diagOneP p)).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, hkdet, one_mul]
    simp [varpiPrime, diagOneP, Matrix.det_fin_two_of]
  refine ⟨j, inv_mul_mem_K1 _ _ _ _ H hdet (dvd_mul_right _ _) ?_⟩
  have e : d - (p : ℤ_[p]) ^ s * ((j : ℕ) : ℤ_[p]) * b - 1 =
      (d - 1) - (p : ℤ_[p]) ^ s * (((j : ℕ) : ℤ_[p]) * b) := by ring
  rw [e]
  exact dvd_sub hd (dvd_mul_right _ _)

/-- `lem:s01-Up`(c): `K1 p s * {diag(1, p)} * K1 p s = ⋃ j, !![1, 0; p^s j, p] • K1 p s`
for `s ≥ 1`; these representatives depend on `s`. -/
theorem diag1p_reps {s : ℕ} (hs : 1 ≤ s) :
    (K1 p s : Set (GL (Fin 2) ℚ_[p])) * {diagOneP p} * K1 p s =
      ⋃ j : Fin p, varpiPrime p s j • (K1 p s : Set (GL (Fin 2) ℚ_[p])) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, k', hk', rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨j, hj⟩ := exists_varpiPrime_inv_mul hs (SetLike.mem_coe.1 hk)
    refine Set.mem_iUnion.2 ⟨j, Set.mem_smul_set.2
      ⟨_, SetLike.mem_coe.2 (mul_mem hj (SetLike.mem_coe.1 hk')), ?_⟩⟩
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hj
    rw [smul_eq_mul, varpiPrime_eq]
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (SetLike.mem_coe.2 (unipLower_mem j)) (Set.mem_singleton _)) hy

/-! ### The index `[K1 p s : K1 p (s + 1)] = p ^ 2` -/

/-- `1 + p^s y` is a unit of `ℤ_[p]` for `s ≥ 1` (auxiliary, `lem:s01-Up`). -/
lemma isUnit_one_add {s : ℕ} (hs : 1 ≤ s) (y : Fin p) :
    IsUnit ((1 : ℤ_[p]) + (p : ℤ_[p]) ^ s * ((y : ℕ) : ℤ_[p])) := by
  rw [isUnit_iff_not_dvd]
  intro h
  have h1 : (p : ℤ_[p]) ∣ (p : ℤ_[p]) ^ s * ((y : ℕ) : ℤ_[p]) :=
    dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have h2 : (p : ℤ_[p]) ∣ 1 := (dvd_add_left h1).1 h
  exact (isUnit_iff_not_dvd (p : ℤ_[p])).1 (isUnit_of_dvd_one h2) (dvd_refl _)

/-- `‖det (sigmaRep p s x y)‖ = 1` for `s ≥ 1` (auxiliary, `lem:s01-Up`). -/
lemma norm_det_sigmaRep {s : ℕ} (hs : 1 ≤ s) (x y : Fin p) :
    ‖(Units.val (sigmaRep p s x y)).det‖ = 1 := by
  have h := isUnit_one_add (p := p) hs y
  rw [PadicInt.isUnit_iff, PadicInt.norm_def] at h
  push_cast at h
  simp only [sigmaRep, matGL_val, Matrix.det_fin_two_of, one_mul, zero_mul, sub_zero]
  exact h

/-- `sigmaRep p s x y ∈ K1 p s` for `s ≥ 1` (auxiliary, `lem:s01-Up`). -/
lemma sigmaRep_mem {s : ℕ} (hs : 1 ≤ s) (x y : Fin p) : sigmaRep p s x y ∈ K1 p s :=
  mem_K1_of_val 1 0 ((p : ℤ_[p]) ^ s * ((x : ℕ) : ℤ_[p]))
    (1 + (p : ℤ_[p]) ^ s * ((y : ℕ) : ℤ_[p])) (by simp [sigmaRep]) (norm_det_sigmaRep hs x y)
    (dvd_mul_right _ _) (by rw [add_sub_cancel_left]; exact dvd_mul_right _ _)

/-- The map `(x, y) ↦ (sigmaRep p s x y)⁻¹ K1 p (s + 1)` onto `K1 p s / K1 p (s + 1)`
(auxiliary, `lem:s01-Up`). -/
noncomputable def cosetMap {s : ℕ} (hs : 1 ≤ s) (q : Fin p × Fin p) :
    K1 p s ⧸ (K1 p (s + 1)).subgroupOf (K1 p s) :=
  ((⟨(sigmaRep p s q.1 q.2)⁻¹, inv_mem (sigmaRep_mem hs q.1 q.2)⟩ : K1 p s) :
    K1 p s ⧸ (K1 p (s + 1)).subgroupOf (K1 p s))

/-- `cosetMap` is injective (auxiliary, `lem:s01-Up`). -/
lemma cosetMap_injective {s : ℕ} (hs : 1 ≤ s) : Function.Injective (cosetMap (p := p) hs) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  unfold cosetMap at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have hw : sigmaRep p s x y * (sigmaRep p s x' y')⁻¹ ∈ K1 p (s + 1) := by
    have h' : (sigmaRep p s x y)⁻¹⁻¹ * (sigmaRep p s x' y')⁻¹ ∈ K1 p (s + 1) := h
    rwa [inv_inv] at h'
  obtain ⟨a, b, c, d, hMw, -, hc, hd⟩ := mem_K1_iff_exists.1 hw
  have E : Units.val (sigmaRep p s x y) =
      Units.val (sigmaRep p s x y * (sigmaRep p s x' y')⁻¹) *
        Units.val (sigmaRep p s x' y') := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  rw [hMw] at E
  simp only [sigmaRep, matGL_val, Matrix.mul_fin_two] at E
  have E10 : (p : ℚ_[p]) ^ s * ((x : ℕ) : ℚ_[p]) =
      (c : ℚ_[p]) * 1 + (d : ℚ_[p]) * ((p : ℚ_[p]) ^ s * ((x' : ℕ) : ℚ_[p])) :=
    congrFun (congrFun E 1) 0
  have E11 : (1 : ℚ_[p]) + (p : ℚ_[p]) ^ s * ((y : ℕ) : ℚ_[p]) =
      (c : ℚ_[p]) * 0 + (d : ℚ_[p]) * (1 + (p : ℚ_[p]) ^ s * ((y' : ℕ) : ℚ_[p])) :=
    congrFun (congrFun E 1) 1
  obtain ⟨γ, hγ⟩ := hc
  obtain ⟨δ, hδ⟩ := hd
  have hd' : d = 1 + (p : ℤ_[p]) ^ (s + 1) * δ := by linear_combination hδ
  subst hγ hd'
  push_cast at E10 E11
  have hps : (p : ℚ_[p]) ^ s ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hx0 : (p : ℚ_[p]) ^ s * (((x : ℕ) : ℚ_[p]) - ((x' : ℕ) : ℚ_[p]) -
      (p : ℚ_[p]) * ((γ : ℚ_[p]) + (δ : ℚ_[p]) * (p : ℚ_[p]) ^ s * ((x' : ℕ) : ℚ_[p]))) =
      (p : ℚ_[p]) ^ s * 0 := by
    linear_combination E10
  have hy0 : (p : ℚ_[p]) ^ s * (((y : ℕ) : ℚ_[p]) - ((y' : ℕ) : ℚ_[p]) -
      (p : ℚ_[p]) * ((δ : ℚ_[p]) * (1 + (p : ℚ_[p]) ^ s * ((y' : ℕ) : ℚ_[p])))) =
      (p : ℚ_[p]) ^ s * 0 := by
    linear_combination E11
  have hx1 := mul_left_cancel₀ hps hx0
  have hy1 := mul_left_cancel₀ hps hy0
  have hxZ : ((x : ℕ) : ℤ_[p]) - ((x' : ℕ) : ℤ_[p]) =
      (p : ℤ_[p]) * (γ + δ * (p : ℤ_[p]) ^ s * ((x' : ℕ) : ℤ_[p])) := by
    apply PadicInt.ext
    push_cast
    linear_combination hx1
  have hyZ : ((y : ℕ) : ℤ_[p]) - ((y' : ℕ) : ℤ_[p]) =
      (p : ℤ_[p]) * (δ * (1 + (p : ℤ_[p]) ^ s * ((y' : ℕ) : ℤ_[p]))) := by
    apply PadicInt.ext
    push_cast
    linear_combination hy1
  exact Prod.ext (fin_eq_of_dvd ⟨_, hxZ⟩) (fin_eq_of_dvd ⟨_, hyZ⟩)

/-- `cosetMap` is surjective (auxiliary, `lem:s01-Up`). -/
lemma cosetMap_surjective {s : ℕ} (hs : 1 ≤ s) :
    Function.Surjective (cosetMap (p := p) hs) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  intro q
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 (K1_le_GL2Zl _ hk)).2
  obtain ⟨a, b, c, d, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hk
  have hpc : (p : ℤ_[p]) ∣ c := (dvd_pow_self (p : ℤ_[p]) (Nat.succ_ne_zero t)).trans hc
  have ha : IsUnit a := by
    rw [isUnit_iff_not_dvd] at hu ⊢
    exact fun h => hu (dvd_sub (dvd_mul_of_dvd_left h d) (dvd_mul_of_dvd_right hpc b))
  obtain ⟨γ, hγ⟩ := hc
  subst hγ
  obtain ⟨δ, hδ⟩ := hd
  have hd' : d = 1 + (p : ℤ_[p]) ^ (t + 1) * δ := by linear_combination hδ
  subst hd'
  obtain ⟨x, ξ, hξ⟩ := exists_fin_dvd a (-γ) ha
  obtain ⟨y, ζ, hζ⟩ := exists_fin_dvd 1 (-(((x : ℕ) : ℤ_[p]) * b + δ)) isUnit_one
  have hγ' : γ = -(((x : ℕ) : ℤ_[p]) * a) - (p : ℤ_[p]) * ξ := by linear_combination -hξ
  have hδ' : δ = -(((x : ℕ) : ℤ_[p]) * b) - ((y : ℕ) : ℤ_[p]) - (p : ℤ_[p]) * ζ := by
    linear_combination -hζ
  refine ⟨(x, y), ?_⟩
  unfold cosetMap
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show (sigmaRep p (t + 1) x y)⁻¹⁻¹ * k ∈ K1 p (t + 1 + 1)
  rw [inv_inv]
  refine mem_K1_of_val a b
    ((p : ℤ_[p]) ^ (t + 1) * ((x : ℕ) : ℤ_[p]) * a +
      (1 + (p : ℤ_[p]) ^ (t + 1) * ((y : ℕ) : ℤ_[p])) * ((p : ℤ_[p]) ^ (t + 1) * γ))
    ((p : ℤ_[p]) ^ (t + 1) * ((x : ℕ) : ℤ_[p]) * b +
      (1 + (p : ℤ_[p]) ^ (t + 1) * ((y : ℕ) : ℤ_[p])) * (1 + (p : ℤ_[p]) ^ (t + 1) * δ))
    ?_ ?_ ?_ ?_
  · rw [Units.val_mul, hM]
    simp only [sigmaRep, matGL_val, Matrix.mul_fin_two]
    refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, norm_det_sigmaRep hs, hkdet, one_mul]
  · exact ⟨-ξ + (p : ℤ_[p]) ^ t * ((y : ℕ) : ℤ_[p]) * γ,
      by linear_combination (p : ℤ_[p]) ^ (t + 1) * hγ'⟩
  · exact ⟨-ζ + (p : ℤ_[p]) ^ t * ((y : ℕ) : ℤ_[p]) * δ,
      by linear_combination (p : ℤ_[p]) ^ (t + 1) * hδ'⟩

/-- `lem:s01-Up` (proof of (c)): `[K1 p s : K1 p (s + 1)] = p ^ 2` for `s ≥ 1` (`c` and `d`
each lose one power of `p`).  The hypothesis is needed: `K1 p 0 = GL2Zl p`. -/
theorem relIndex_K1_succ {s : ℕ} (hs : 1 ≤ s) : (K1 p (s + 1)).relIndex (K1 p s) = p ^ 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.ofBijective _
      ⟨cosetMap_injective (p := p) hs, cosetMap_surjective (p := p) hs⟩),
    Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, sq]

end Langlandscape.Local
