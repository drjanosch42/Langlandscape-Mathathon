/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.UpCosets
import Mathlib.Data.ZMod.Units

/-!
# Hida's lemma, local part (S04-L6)

Tex label `lem:s04-hida` (a), (b) of `mathematics/chapters/s04/control.tex`
(staged source: `plan/staged/stage-04-lambda-adic.tex`).  The intermediate level
`Kpp p s = K1 p s ⊓ K0 p (s + 1)` (the tex's `K'_s`) and, with `ϖ = diag(p, 1)` and
`ϖ_j = !![p, j; 0, 1]` (`def:s01-NUp`):

* `Kpp_mul_varpi_mul_Kpp`: `Kpp p s * {ϖ} * Kpp p s = ⋃ j, ϖ_j • Kpp p s` for `s ≥ 1`, with the same
  `ϖ_j` as for `K1 p s` and `K1 p (s + 1)` (`reps_indep_Kpp`); the cosets are distinct
  (`varpi_inv_mul_not_mem_Kpp`);
* `exists_varpi_conj`: for `u ∈ K1 p s` and each `j` there are `i` and `u_j ∈ Kpp p s` with
  `u ϖ_j = ϖ_i u_j` (`lem:s04-hida`(b));
* `relIndex_Kpp`: `[K1 p s : Kpp p s] = p` for `s ≥ 1`;
* `kppQuotEquiv`: `Kpp p s / K1 p (s + 1) ≃ ker((ℤ/p^{s+1})ˣ → (ℤ/p^s)ˣ)` for `s ≥ 1`, induced by the
  `(2,2)` entry `d ↦ d mod p^{s+1}` (the group hom `dModHom`; proof of `lem:s04-hida`(c), second claim).

Status: *formalized*.  Everything is explicit `2 × 2` matrix algebra over `ℤ_[p]`, as in
`Langlandscape.Local.UpCosets`.  The group-isomorphism form of the quotient statement is
`kppQuotMulEquiv` (quotient by `ker dModHom`, which equals `(K1 p (s + 1)).subgroupOf (Kpp p s)` by
`ker_dModHom`; normality: `subgroupOf_K1_succ_normal`).

Maintenance notes: `exists_varpi_inv_mul_mem_Kpp` adapts the proof of stage-1 `exists_varpi_inv_mul`
(only the lower-left divisibility changes; stage-1 files are not edited by this package).  The helpers
`entZ`, `coe_entZ`, `entZ_one`, `entZ_mul`, `toZModPow_eq_zero_iff_norm`, `toZModPow_eq_one_iff_norm` are
not specific to Hida's lemma and are candidates for `Langlandscape.Local.GL2Levels`.
-/

open Matrix Pointwise

namespace Langlandscape.Local

variable {p : ℕ} [Fact p.Prime]

/-! ### The level `Kpp` -/

variable (p) in
/-- The level `K'_s = K1 p s ⊓ K0 p (s + 1)` of `lem:s04-hida` (`s04-hida`): elements of `GL₂(ℤ_p)` with
`c ≡ 0 mod p^{s+1}` and `d ≡ 1 mod p^s`. -/
noncomputable def Kpp (s : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) := K1 p s ⊓ K0 p (s + 1)

/-- Membership in `Kpp p s`, unfolded (`lem:s04-hida`, `s04-hida`). -/
lemma mem_Kpp_iff {s : ℕ} {g : GL (Fin 2) ℚ_[p]} : g ∈ Kpp p s ↔ g ∈ K1 p s ∧ g ∈ K0 p (s + 1) :=
  Subgroup.mem_inf

/-- `Kpp p s ≤ K1 p s` (`lem:s04-hida`, `s04-hida`). -/
lemma Kpp_le_K1 (s : ℕ) : Kpp p s ≤ K1 p s := fun _ h => (mem_Kpp_iff.1 h).1

/-- `Kpp p s ≤ K0 p (s + 1)` (`lem:s04-hida`, `s04-hida`). -/
lemma Kpp_le_K0 (s : ℕ) : Kpp p s ≤ K0 p (s + 1) := fun _ h => (mem_Kpp_iff.1 h).2

/-- `Kpp p s ≤ GL₂(ℤ_p)` (`lem:s04-hida`, `s04-hida`). -/
lemma Kpp_le_GL2Zl (s : ℕ) : Kpp p s ≤ GL2Zl p := (Kpp_le_K1 s).trans (K1_le_GL2Zl s)

/-- `K1 p (s + 1) ≤ Kpp p s` (`lem:s04-hida`(c), `s04-hida`). -/
lemma K1_succ_le_Kpp (s : ℕ) : K1 p (s + 1) ≤ Kpp p s :=
  fun _ h => mem_Kpp_iff.2 ⟨K1_succ_le s h, K1_le_K0 (s + 1) h⟩

/-- `!![1, j; 0, 1] ∈ Kpp p s` (auxiliary, `lem:s04-hida`(a), `s04-hida`). -/
lemma unipUpper_mem_Kpp {s : ℕ} (j : Fin p) : unipUpper p j ∈ Kpp p s :=
  mem_Kpp_iff.2 ⟨unipUpper_mem j, K1_le_K0 (s + 1) (unipUpper_mem j)⟩

/-! ### (a), (b): `ϖ_i⁻¹ k ϖ ∈ Kpp p s` -/

/-- Core of `lem:s04-hida`(a),(b) (`s04-hida`): for `k ∈ K1 p s` (`s ≥ 1`) there is `j` with
`ϖ_j⁻¹ k ϖ ∈ Kpp p s`.  Writing `k = !![a, b; c, d]` and `b = p β + j d`, the quotient is
`!![a - j c, β; p c, d]`, whose lower-left entry `p c` lies in `p^{s+1} ℤ_p`. -/
lemma exists_varpi_inv_mul_mem_Kpp {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K1 p s) :
    ∃ j : Fin p, (varpi p j)⁻¹ * (k * varpiDiag p) ∈ Kpp p s := by
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 (K1_le_GL2Zl s hk)).2
  obtain ⟨a, b, c, d, hM, hu, hc, hd1⟩ := mem_K1_iff_exists.1 hk
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
  have h1 : (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K1 p s :=
    inv_mul_mem_K1 _ _ _ _ H hdet (dvd_mul_of_dvd_right hc _) hd1
  have h0 : (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K0 p (s + 1) :=
    inv_mul_mem_K0 _ _ _ _ H hdet (by rw [pow_succ']; exact mul_dvd_mul_left _ hc)
  exact ⟨j, mem_Kpp_iff.2 ⟨h1, h0⟩⟩

/-- `lem:s04-hida`(a) (`s04-hida`), `def:s01-NUp`: `Kpp p s * {ϖ} * Kpp p s = ⋃ j, ϖ_j • Kpp p s` for
`s ≥ 1`, with the same representatives `ϖ_j = varpi p j` as `K1_mul_varpi_mul_K1`. -/
theorem Kpp_mul_varpi_mul_Kpp {s : ℕ} (hs : 1 ≤ s) :
    (Kpp p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * Kpp p s =
      ⋃ j : Fin p, varpi p j • (Kpp p s : Set (GL (Fin 2) ℚ_[p])) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, k', hk', rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hkK : k ∈ Kpp p s := SetLike.mem_coe.1 hk
    obtain ⟨j, hj⟩ := exists_varpi_inv_mul_mem_Kpp hs (Kpp_le_K1 s hkK)
    refine Set.mem_iUnion.2 ⟨j, Set.mem_smul_set.2
      ⟨_, SetLike.mem_coe.2 (mul_mem hj (SetLike.mem_coe.1 hk')), ?_⟩⟩
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hj
    rw [smul_eq_mul, varpi_eq]
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (SetLike.mem_coe.2 (unipUpper_mem_Kpp j)) (Set.mem_singleton _)) hy

/-- `lem:s04-hida`(a) (`s04-hida`): the cosets `ϖ_j Kpp p s` are pairwise distinct (for every `s`). -/
theorem varpi_inv_mul_not_mem_Kpp {s : ℕ} {j j' : Fin p} (hjj' : j ≠ j') :
    (varpi p j)⁻¹ * varpi p j' ∉ Kpp p s :=
  fun h => varpi_inv_mul_not_mem hjj' (Kpp_le_K1 s h)

/-- `lem:s04-hida`(a) (`s04-hida`): the same `ϖ_j` represent `K ϖ K / K` at the three levels
`K1 p s`, `Kpp p s`, `K1 p (s + 1)` (`s ≥ 1`), so `U_p` is defined compatibly on `X_s`, `X'_s`,
`X_{s+1}`. -/
theorem reps_indep_Kpp {s : ℕ} (hs : 1 ≤ s) :
    ((K1 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p s =
        ⋃ j : Fin p, varpi p j • (K1 p s : Set (GL (Fin 2) ℚ_[p]))) ∧
      ((Kpp p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * Kpp p s =
        ⋃ j : Fin p, varpi p j • (Kpp p s : Set (GL (Fin 2) ℚ_[p]))) ∧
      ((K1 p (s + 1) : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p (s + 1) =
        ⋃ j : Fin p, varpi p j • (K1 p (s + 1) : Set (GL (Fin 2) ℚ_[p]))) :=
  ⟨K1_mul_varpi_mul_K1 hs, Kpp_mul_varpi_mul_Kpp hs, K1_mul_varpi_mul_K1 (by omega)⟩

/-- `lem:s04-hida`(b) (`s04-hida`): for `u ∈ K1 p s` (`s ≥ 1`) and each `j` there are `i` and
`u_j ∈ Kpp p s` with `u ϖ_j = ϖ_i u_j`. -/
theorem exists_varpi_conj {s : ℕ} (hs : 1 ≤ s) :
    ∀ u ∈ K1 p s, ∀ j : Fin p, ∃ i : Fin p, ∃ uj ∈ Kpp p s, u * varpi p j = varpi p i * uj := by
  intro u hu j
  obtain ⟨i, hi⟩ := exists_varpi_inv_mul_mem_Kpp hs (mul_mem hu (unipUpper_mem j))
  refine ⟨i, _, hi, ?_⟩
  rw [mul_inv_cancel_left, varpi_eq, mul_assoc]

/-! ### The index `[K1 p s : Kpp p s] = p` -/

variable (p) in
/-- The map `x ↦ !![1, 0; p^s x, 1] Kpp p s` onto `K1 p s / Kpp p s` (auxiliary, `lem:s04-hida`,
`s04-hida`). -/
noncomputable def kppCosetMap (s : ℕ) (x : Fin p) : K1 p s ⧸ (Kpp p s).subgroupOf (K1 p s) :=
  ((⟨unipLower p s x, unipLower_mem x⟩ : K1 p s) : K1 p s ⧸ (Kpp p s).subgroupOf (K1 p s))

/-- `kppCosetMap` is injective (auxiliary, `lem:s04-hida`, `s04-hida`). -/
lemma kppCosetMap_injective (s : ℕ) : Function.Injective (kppCosetMap p s) := by
  intro x x' h
  unfold kppCosetMap at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have hw : (unipLower p s x)⁻¹ * unipLower p s x' ∈ Kpp p s := h
  obtain ⟨a, b, c, d, hMw, -, hc⟩ := mem_K0_iff_exists.1 (Kpp_le_K0 s hw)
  have E : Units.val (unipLower p s x') =
      Units.val (unipLower p s x) * Units.val ((unipLower p s x)⁻¹ * unipLower p s x') := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [hMw] at E
  simp only [unipLower, matGL_val, Matrix.mul_fin_two] at E
  have E00 : (1 : ℚ_[p]) = 1 * (a : ℚ_[p]) + 0 * (c : ℚ_[p]) := congrFun (congrFun E 0) 0
  have E10 : (p : ℚ_[p]) ^ s * ((x' : ℕ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ s * ((x : ℕ) : ℚ_[p]) * (a : ℚ_[p]) + 1 * (c : ℚ_[p]) :=
    congrFun (congrFun E 1) 0
  obtain ⟨γ, hγ⟩ := hc
  subst hγ
  push_cast at E00 E10
  have hps : (p : ℚ_[p]) ^ s ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hx0 : (p : ℚ_[p]) ^ s * (((x' : ℕ) : ℚ_[p]) - ((x : ℕ) : ℚ_[p]) - (p : ℚ_[p]) * (γ : ℚ_[p])) =
      (p : ℚ_[p]) ^ s * 0 := by
    linear_combination E10 - (p : ℚ_[p]) ^ s * ((x : ℕ) : ℚ_[p]) * E00
  have hx1 := mul_left_cancel₀ hps hx0
  have hxZ : ((x' : ℕ) : ℤ_[p]) - ((x : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * γ := by
    apply PadicInt.ext
    push_cast
    linear_combination hx1
  exact (fin_eq_of_dvd ⟨γ, hxZ⟩).symm

/-- `kppCosetMap` is surjective for `s ≥ 1` (auxiliary, `lem:s04-hida`, `s04-hida`). -/
lemma kppCosetMap_surjective {s : ℕ} (hs : 1 ≤ s) : Function.Surjective (kppCosetMap p s) := by
  intro q
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 (K1_le_GL2Zl _ hk)).2
  obtain ⟨a, b, c, d, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hk
  have hpc : (p : ℤ_[p]) ∣ c := (dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans hc
  have ha : IsUnit a := by
    rw [isUnit_iff_not_dvd] at hu ⊢
    exact fun h => hu (dvd_sub (dvd_mul_of_dvd_left h d) (dvd_mul_of_dvd_right hpc b))
  obtain ⟨γ, hγ⟩ := hc
  subst hγ
  obtain ⟨x, η, hη⟩ := exists_fin_dvd a γ ha
  refine ⟨x, ?_⟩
  unfold kppCosetMap
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show (unipLower p s x)⁻¹ * k ∈ Kpp p s
  have H : Units.val (unipLower p s x) *
      !![(a : ℚ_[p]), (b : ℚ_[p]);
        (((p : ℤ_[p]) ^ s * γ - (p : ℤ_[p]) ^ s * ((x : ℕ) : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]),
        ((d - (p : ℤ_[p]) ^ s * ((x : ℕ) : ℤ_[p]) * b : ℤ_[p]) : ℚ_[p])] = Units.val k := by
    rw [hM]
    simp only [unipLower, matGL_val, Matrix.mul_fin_two]
    refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
  have hdet : ‖(Units.val (unipLower p s x)).det‖ = ‖(Units.val k).det‖ := by
    rw [hkdet]
    simp [unipLower, Matrix.det_fin_two_of]
  have h1 : (unipLower p s x)⁻¹ * k ∈ K1 p s := by
    refine inv_mul_mem_K1 _ _ _ _ H hdet
      (dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) ?_
    have e : d - (p : ℤ_[p]) ^ s * ((x : ℕ) : ℤ_[p]) * b - 1 =
        (d - 1) - (p : ℤ_[p]) ^ s * (((x : ℕ) : ℤ_[p]) * b) := by ring
    rw [e]
    exact dvd_sub hd (dvd_mul_right _ _)
  have h0 : (unipLower p s x)⁻¹ * k ∈ K0 p (s + 1) :=
    inv_mul_mem_K0 _ _ _ _ H hdet ⟨η, by linear_combination (p : ℤ_[p]) ^ s * hη⟩
  exact mem_Kpp_iff.2 ⟨h1, h0⟩

/-- `lem:s04-hida` (`s04-hida`): `[K1 p s : Kpp p s] = p` for `s ≥ 1` (the tex's `[K_s : K'_s] = p`;
only the lower-left entry loses one power of `p`).  The hypothesis is needed: `K1 p 0 = GL2Zl p`. -/
theorem relIndex_Kpp {s : ℕ} (hs : 1 ≤ s) : (Kpp p s).relIndex (K1 p s) = p := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.ofBijective _
      ⟨kppCosetMap_injective (p := p) s, kppCosetMap_surjective (p := p) hs⟩),
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### `Kpp p s / K1 p (s + 1) ≃ ker((ℤ/p^{s+1})ˣ → (ℤ/p^s)ˣ)` -/

/-- The entry `g i j` of `g ∈ GL₂(ℤ_p)` as an element of `ℤ_[p]` (auxiliary, `lem:s04-hida`(c),
`s04-hida`). -/
noncomputable def entZ (g : GL (Fin 2) ℚ_[p]) (hg : g ∈ GL2Zl p) (i j : Fin 2) : ℤ_[p] :=
  ⟨(Units.val g) i j, (mem_GL2Zl_def.1 hg).1 i j⟩

/-- `entZ` coerces to the matrix entry (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma coe_entZ (g : GL (Fin 2) ℚ_[p]) (hg : g ∈ GL2Zl p) (i j : Fin 2) :
    ((entZ g hg i j : ℤ_[p]) : ℚ_[p]) = (Units.val g) i j := rfl

/-- The `(2,2)` entry of `1` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma entZ_one (h : (1 : GL (Fin 2) ℚ_[p]) ∈ GL2Zl p) : entZ (1 : GL (Fin 2) ℚ_[p]) h 1 1 = 1 := by
  apply PadicInt.ext
  show (Units.val (1 : GL (Fin 2) ℚ_[p])) 1 1 = ((1 : ℤ_[p]) : ℚ_[p])
  simp

/-- The `(2,2)` entry of a product, `c b' + d d'` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma entZ_mul (g h : GL (Fin 2) ℚ_[p]) (hg : g ∈ GL2Zl p) (hh : h ∈ GL2Zl p)
    (hgh : g * h ∈ GL2Zl p) :
    entZ (g * h) hgh 1 1 = entZ g hg 1 0 * entZ h hh 0 1 + entZ g hg 1 1 * entZ h hh 1 1 :=
  PadicInt.ext (mul_val_apply g h 1 1)

/-- `x ↦ x mod p^n` vanishes iff `v(x) ≥ n` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma toZModPow_eq_zero_iff_norm (x : ℤ_[p]) (n : ℕ) :
    PadicInt.toZModPow n x = 0 ↔ ‖(x : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have h := PadicInt.norm_le_pow_iff_mem_span_pow x n
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker] at h
  exact h.symm

/-- `x ≡ 1 mod p^n` iff `v(x - 1) ≥ n` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma toZModPow_eq_one_iff_norm (x : ℤ_[p]) (n : ℕ) :
    PadicInt.toZModPow n x = 1 ↔ ‖(x : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have h := toZModPow_eq_zero_iff_norm (x - 1) n
  rw [map_sub, map_one, sub_eq_zero, PadicInt.coe_sub, PadicInt.coe_one] at h
  exact h

/-- The lower-left entry of `k ∈ Kpp p s` vanishes mod `p^{s+1}` (auxiliary, `lem:s04-hida`(c),
`s04-hida`). -/
lemma toZModPow_entZ_10 {s : ℕ} {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ Kpp p s) (hg : k ∈ GL2Zl p) :
    PadicInt.toZModPow (s + 1) (entZ k hg 1 0) = 0 :=
  (toZModPow_eq_zero_iff_norm _ _).2 (mem_K0_iff.1 (Kpp_le_K0 s hk)).2

/-- Multiplicativity of `d mod p^{s+1}` on `Kpp p s` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma toZModPow_entZ_mul {s : ℕ} (k k' : Kpp p s) :
    PadicInt.toZModPow (s + 1)
        (entZ ((k : GL (Fin 2) ℚ_[p]) * (k' : GL (Fin 2) ℚ_[p])) (Kpp_le_GL2Zl s (k * k').2) 1 1) =
      PadicInt.toZModPow (s + 1) (entZ (k : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k.2) 1 1) *
        PadicInt.toZModPow (s + 1) (entZ (k' : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k'.2) 1 1) := by
  rw [entZ_mul (k : GL (Fin 2) ℚ_[p]) (k' : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k.2)
      (Kpp_le_GL2Zl s k'.2) (Kpp_le_GL2Zl s (k * k').2), map_add, map_mul, map_mul,
    toZModPow_entZ_10 k.2 (Kpp_le_GL2Zl s k.2), zero_mul, zero_add]

/-- `d mod p^{s+1}` of `1` (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma toZModPow_entZ_one (s : ℕ) :
    PadicInt.toZModPow (s + 1)
      (entZ (1 : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s (1 : Kpp p s).2) 1 1) = 1 := by
  rw [entZ_one, map_one]

variable (p) in
/-- `Kpp p s → ℤ/p^{s+1}`, `!![a, b; c, d] ↦ d mod p^{s+1}`, a monoid hom because `c ≡ 0 mod p^{s+1}`
(proof of `lem:s04-hida`(c), second claim, `s04-hida`). -/
noncomputable def dModHom (s : ℕ) : Kpp p s →* ZMod (p ^ (s + 1)) where
  toFun k := PadicInt.toZModPow (s + 1) (entZ (k : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k.2) 1 1)
  map_one' := toZModPow_entZ_one s
  map_mul' k k' := toZModPow_entZ_mul k k'

/-- `dModHom`, unfolded (auxiliary, `lem:s04-hida`(c), `s04-hida`). -/
lemma dModHom_apply (s : ℕ) (k : Kpp p s) :
    dModHom p s k =
      PadicInt.toZModPow (s + 1) (entZ (k : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k.2) 1 1) := rfl

/-- `lem:s04-hida`(c) (`s04-hida`): the kernel of `d ↦ d mod p^{s+1}` on `Kpp p s` is `K1 p (s + 1)`. -/
theorem ker_dModHom (s : ℕ) :
    (dModHom p s).toHomUnits.ker = (K1 p (s + 1)).subgroupOf (Kpp p s) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff, MonoidHom.coe_toHomUnits,
    Units.val_one, dModHom_apply, toZModPow_eq_one_iff_norm, mem_K1_iff]
  exact ⟨fun h => ⟨Kpp_le_K0 s k.2, h⟩, fun h => h.2⟩

/-- `lem:s04-hida`(c) (`s04-hida`): for `s ≥ 1` the image of `d ↦ d mod p^{s+1}` on `Kpp p s` is
`ker((ℤ/p^{s+1})ˣ → (ℤ/p^s)ˣ)` (surjectivity via `diag(1, d)`). -/
theorem range_dModHom {s : ℕ} (hs : 1 ≤ s) :
    (dModHom p s).toHomUnits.range = (ZMod.unitsMap (pow_dvd_pow p (Nat.le_add_right s 1))).ker := by
  ext u
  constructor
  · intro hu
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hu
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, MonoidHom.coe_toHomUnits,
      Units.val_one, dModHom_apply, PadicInt.cast_toZModPow s (s + 1) (Nat.le_add_right s 1),
      toZModPow_eq_one_iff_norm]
    exact (mem_K1_iff.1 (Kpp_le_K1 s k.2)).2
  · intro hu
    have hu1 : (ZMod.cast (u : ZMod (p ^ (s + 1))) : ZMod (p ^ s)) = 1 := by
      have h := congrArg Units.val (MonoidHom.mem_ker.1 hu)
      rwa [ZMod.unitsMap_val, Units.val_one] at h
    haveI : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨t, htz⟩ : ∃ t : ℤ_[p], PadicInt.toZModPow (s + 1) t = (u : ZMod (p ^ (s + 1))) :=
      ⟨(((u : ZMod (p ^ (s + 1))).val : ℕ) : ℤ_[p]), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
    have hts : PadicInt.toZModPow s t = 1 := by
      rw [← PadicInt.cast_toZModPow s (s + 1) (Nat.le_add_right s 1), htz]
      exact hu1
    have ht1 : (p : ℤ_[p]) ^ s ∣ t - 1 := by
      have h : t - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := p) s) := by
        rw [RingHom.mem_ker, map_sub, map_one, hts, sub_self]
      rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
    have htu : IsUnit t := by
      rw [isUnit_iff_not_dvd]
      intro h
      have h1 : (p : ℤ_[p]) ∣ t - 1 := (dvd_pow_self _ (by omega : s ≠ 0)).trans ht1
      have h2 : (p : ℤ_[p]) ∣ t - (t - 1) := dvd_sub h h1
      rw [sub_sub_cancel] at h2
      exact (isUnit_iff_not_dvd (p : ℤ_[p])).1 (isUnit_of_dvd_one h2) (dvd_refl _)
    have hk : diagGL 1 (intUnit htu.unit) ∈ Kpp p s :=
      mem_Kpp_iff.2 ⟨(one_diag_mem_K1_iff _ s).2 (by rw [IsUnit.unit_spec]; exact ht1),
        one_diag_mem_K0 _ (s + 1)⟩
    refine MonoidHom.mem_range.2 ⟨(⟨_, hk⟩ : Kpp p s), Units.ext ?_⟩
    rw [MonoidHom.coe_toHomUnits, dModHom_apply, ← htz]
    exact congrArg (fun y : ℤ_[p] => PadicInt.toZModPow (s + 1) y)
      (PadicInt.ext (by simp [coe_entZ, diagGL_val, coe_intUnit, IsUnit.unit_spec]))

/-- `lem:s04-hida`(c) (`s04-hida`): `(K1 p (s + 1)).subgroupOf (Kpp p s)` is normal in `Kpp p s` (it is
the kernel of `dModHom`). -/
theorem subgroupOf_K1_succ_normal (s : ℕ) : ((K1 p (s + 1)).subgroupOf (Kpp p s)).Normal := by
  rw [← ker_dModHom]
  exact MonoidHom.normal_ker _

/-- `lem:s04-hida`(c), second claim (`s04-hida`), group-isomorphism form: for `s ≥ 1`,
`Kpp p s / ker dModHom ≃* ker((ℤ/p^{s+1})ˣ → (ℤ/p^s)ˣ)` (first isomorphism theorem for `dModHom`; the
kernel is `(K1 p (s + 1)).subgroupOf (Kpp p s)` by `ker_dModHom`). -/
noncomputable def kppQuotMulEquiv {s : ℕ} (hs : 1 ≤ s) :
    Kpp p s ⧸ (dModHom p s).toHomUnits.ker ≃*
      (ZMod.unitsMap (pow_dvd_pow p (Nat.le_add_right s 1))).ker :=
  (QuotientGroup.quotientKerEquivRange (dModHom p s).toHomUnits).trans
    (MulEquiv.subgroupCongr (range_dModHom (p := p) hs))

/-- `lem:s04-hida`(c) (`s04-hida`): `kppQuotMulEquiv` sends the class of `k` to `dModHom p s k`. -/
theorem kppQuotMulEquiv_mk {s : ℕ} (hs : 1 ≤ s) (k : Kpp p s) :
    ((kppQuotMulEquiv hs (k : Kpp p s ⧸ (dModHom p s).toHomUnits.ker) :
        (ZMod (p ^ (s + 1)))ˣ) : ZMod (p ^ (s + 1))) = dModHom p s k := by
  first
    | (rw [kppQuotMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
        QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply, QuotientGroup.rangeKerLift,
        QuotientGroup.lift_mk, MonoidHom.coe_rangeRestrict, MonoidHom.coe_toHomUnits]; done)
    | rfl

/-- `lem:s04-hida`(c), second claim (`s04-hida`): for `s ≥ 1`,
`Kpp p s / K1 p (s + 1) ≃ ker(Δ_{s+1} → Δ_s)`, with `Δ_s` stated as `(ZMod (p ^ s))ˣ` and the reduction
`ZMod.unitsMap`.  The quotient is taken in the form `Kpp p s ⧸ (K1 p (s + 1)).subgroupOf (Kpp p s)`;
the map is induced by the `(2,2)` entry, `!![a, b; c, d] ↦ d mod p^{s+1}` (`kppQuotEquiv_mk`).  It is
the underlying equivalence of the group isomorphism `kppQuotMulEquiv`, transported along `ker_dModHom`. -/
noncomputable def kppQuotEquiv {s : ℕ} (hs : 1 ≤ s) :
    Kpp p s ⧸ (K1 p (s + 1)).subgroupOf (Kpp p s) ≃
      (ZMod.unitsMap (pow_dvd_pow p (Nat.le_add_right s 1))).ker :=
  (Subgroup.quotientEquivOfEq (ker_dModHom (p := p) s).symm).trans (kppQuotMulEquiv hs).toEquiv

/-- `lem:s04-hida`(c) (`s04-hida`): `kppQuotEquiv` sends the class of `!![a, b; c, d]` to `d mod p^{s+1}`. -/
theorem kppQuotEquiv_mk {s : ℕ} (hs : 1 ≤ s) (k : Kpp p s) :
    ((kppQuotEquiv hs (k : Kpp p s ⧸ (K1 p (s + 1)).subgroupOf (Kpp p s)) :
        (ZMod (p ^ (s + 1)))ˣ) : ZMod (p ^ (s + 1))) =
      PadicInt.toZModPow (s + 1) (entZ (k : GL (Fin 2) ℚ_[p]) (Kpp_le_GL2Zl s k.2) 1 1) := by
  first
    | (rw [kppQuotEquiv, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk, MulEquiv.toEquiv_eq_coe,
        MulEquiv.coe_toEquiv, kppQuotMulEquiv_mk, dModHom_apply]; done)
    | rfl

end Langlandscape.Local
