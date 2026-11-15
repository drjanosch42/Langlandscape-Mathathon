/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.UpCosets

/-!
# Local layer at q — S02-L1 (built, gate1 green)

Tex labels: def:s02-tree, lem:s02-tree, rem:s02-treeconv.
-/

/-!
## Contents

With `α = diag(1, q)` (`alphaq`, the seed's `α`, = S01 `diagOneP`; Serre's and Casselman's
base edge, `rem:s02-treeconv`):

* `SLq`, `SL2Zq`, `Kalpha = α GL₂(ℤ_q) α⁻¹`, `K1q = SL₂ ∩ Kalpha`, `IwSL = SL₂ ∩ Iw`;
* `vdet g = v_q(det g) mod 2` and `vdet_mul`;
* `lem:s02-tree`(d): `GL2Zl_inf_Kalpha`, `alphaq_inv_conj_mem_GL2Zl`;
* the determinant-fixing representatives `exists_SL2Zq_inv_mul_mem_Iw`, `exists_K1q_inv_mul_mem_Iw`
  (`k = s · diag(1, det k)` with `diag(1, u) ∈ Iw`);
* `relIndex_Iw : [GL₂(ℤ_q) : Iw_q] = q + 1` (representatives `!![j, 1; 1, 0]`, `j < q`, and `1`).

Auxiliary declarations: `qcast_ne_zero`, `det_conj_GL`, `det_diagGL`, `diagGL_mem_Iw` and the
`vdet`/membership helpers are general facts about `GL₂(ℚ_q)`, public only because `Tree/Coset.lean`
uses them; they are not part of the S02-L1 interface and are intended for a later move to
`Langlandscape.Local`.  `rIw`, `cosetIw` and their lemmas only serve `relIndex_Iw`.

Status: *formalized*.
-/

open Matrix

namespace Langlandscape.Tree

open Langlandscape.Local (GL2Zl Iw)

noncomputable section

variable (q : ℕ) [Fact q.Prime]

/-! ### The groups -/

/-- `α = diag(1, q)`, the seed's `α` (`def:s02-tree`, `rem:s02-treeconv`); equal to S01
`diagOneP`. -/
def alphaq : GL (Fin 2) ℚ_[q] := Local.diagOneP q

/-- `SL₂(ℚ_q)` as the kernel of the determinant (`lem:s02-tree`). -/
def SLq : Subgroup (GL (Fin 2) ℚ_[q]) := (Matrix.GeneralLinearGroup.det).ker

/-- `SL₂(ℤ_q) = SL₂(ℚ_q) ∩ GL₂(ℤ_q)`, the stabiliser of `v₀` (`lem:s02-tree`(c)). -/
def SL2Zq : Subgroup (GL (Fin 2) ℚ_[q]) := SLq q ⊓ GL2Zl q

/-- `α GL₂(ℤ_q) α⁻¹` (`lem:s02-tree`(c),(d)). -/
def Kalpha : Subgroup (GL (Fin 2) ℚ_[q]) :=
  (GL2Zl q).map (MulAut.conj (alphaq q)).toMonoidHom

/-- `SL₂(ℚ_q) ∩ α GL₂(ℤ_q) α⁻¹`, the stabiliser of `v₁` (`lem:s02-tree`(c)). -/
def K1q : Subgroup (GL (Fin 2) ℚ_[q]) := SLq q ⊓ Kalpha q

/-- `SL₂(ℚ_q) ∩ Iw_q`, the stabiliser of `e₀` (`lem:s02-tree`(c)). -/
def IwSL : Subgroup (GL (Fin 2) ℚ_[q]) := SLq q ⊓ Iw q

/-- The parity `v_q(det g) mod 2` (`def:s02-tree`: the type of `g v₀`). -/
def vdet (g : GL (Fin 2) ℚ_[q]) : ZMod 2 := ((Padic.valuation (Units.val g).det : ℤ) : ZMod 2)

/-! ### Membership lemmas -/

/-- `(q : ℚ_q) ≠ 0` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem qcast_ne_zero : (q : ℚ_[q]) ≠ 0 :=
  Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero

variable {q}

/-- Membership in `SLq` (`lem:s02-tree`, `s02-tree`). -/
theorem mem_SLq_iff {g : GL (Fin 2) ℚ_[q]} : g ∈ SLq q ↔ (Units.val g).det = 1 := by
  rw [SLq, MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_one]

/-- Membership in `SL2Zq` (`lem:s02-tree`(c), `s02-tree`). -/
theorem mem_SL2Zq_iff {g : GL (Fin 2) ℚ_[q]} : g ∈ SL2Zq q ↔ g ∈ SLq q ∧ g ∈ GL2Zl q := Iff.rfl

/-- Membership in `K1q` (`lem:s02-tree`(c), `s02-tree`). -/
theorem mem_K1q_iff {g : GL (Fin 2) ℚ_[q]} : g ∈ K1q q ↔ g ∈ SLq q ∧ g ∈ Kalpha q := Iff.rfl

/-- Membership in `IwSL` (`lem:s02-tree`(c), `s02-tree`). -/
theorem mem_IwSL_iff {g : GL (Fin 2) ℚ_[q]} : g ∈ IwSL q ↔ g ∈ SLq q ∧ g ∈ Iw q := Iff.rfl

/-- Membership in `Kalpha`: `x ∈ α GL₂(ℤ_q) α⁻¹ ↔ α⁻¹ x α ∈ GL₂(ℤ_q)` (`lem:s02-tree`(d),
`s02-tree`). -/
theorem mem_Kalpha_iff {x : GL (Fin 2) ℚ_[q]} :
    x ∈ Kalpha q ↔ (alphaq q)⁻¹ * x * alphaq q ∈ GL2Zl q := by
  rw [Kalpha, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hkx⟩
    subst hkx
    have e : (alphaq q)⁻¹ * ((MulAut.conj (alphaq q)).toMonoidHom k) * alphaq q = k := by
      show (alphaq q)⁻¹ * (alphaq q * k * (alphaq q)⁻¹) * alphaq q = k
      group
    rw [e]
    exact hk
  · intro h
    refine ⟨_, h, ?_⟩
    show alphaq q * ((alphaq q)⁻¹ * x * alphaq q) * (alphaq q)⁻¹ = x
    group

/-- `det (g⁻¹ x g) = det x` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem det_conj_GL (g x : GL (Fin 2) ℚ_[q]) :
    (Units.val (g⁻¹ * x * g)).det = (Units.val x).det := by
  have h1 : (Units.val g⁻¹).det * (Units.val g).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (Units.val x).det * h1

/-- `det diag(a, d) = a d` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem det_diagGL (a d : ℚ_[q]ˣ) : (Units.val (Local.diagGL a d)).det = (a : ℚ_[q]) * d := by
  rw [Local.diagGL_val, Matrix.det_fin_two_of]
  ring

/-- `diag(a, a) ∈ Iw_q` for a unit `a` of norm `1` (auxiliary, `lem:s02-tree`(c), `s02-tree`). -/
theorem diagGL_mem_Iw {a : ℚ_[q]ˣ} (ha : ‖(a : ℚ_[q])‖ = 1) : Local.diagGL a a ∈ Iw q := by
  have hz : Local.matGL (a : ℚ_[q]) 0 0 a (by simp) ∈ GL2Zl q := by
    refine (Local.matGL_mem_GL2Zl_iff _ _ _ _ _).2 ⟨ha.le, by simp, by simp, ha.le, ?_⟩
    rw [mul_zero, sub_zero, norm_mul, ha, mul_one]
  refine Local.mem_K0_iff.2 ⟨hz, ?_⟩
  show ‖(0 : ℚ_[q])‖ ≤ _
  rw [norm_zero]
  exact zpow_nonneg (Nat.cast_nonneg _) _

/-! ### The parity `vdet` -/

/-- `‖x‖ = 1 → v_q(x) = 0` (auxiliary, `def:s02-tree`, `s02-tree`). -/
private theorem valuation_eq_zero_of_norm {x : ℚ_[q]} (hx : ‖x‖ = 1) : Padic.valuation x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hp_pos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hp_ne_one : (q : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : q.Prime).ne_one
  rw [Padic.norm_eq_zpow_neg_valuation hx0, ← zpow_zero (q : ℝ),
    zpow_right_inj₀ hp_pos hp_ne_one, neg_eq_zero] at hx
  exact hx

/-- `vdet` is additive: `v_q(det gh) = v_q(det g) + v_q(det h)` (`def:s02-tree`, `s02-tree`). -/
theorem vdet_mul (g h : GL (Fin 2) ℚ_[q]) : vdet q (g * h) = vdet q g + vdet q h := by
  simp only [vdet, Units.val_mul, Matrix.det_mul]
  rw [Padic.valuation_mul (Local.det_ne_zero g) (Local.det_ne_zero h), Int.cast_add]

variable (q) in
/-- `vdet 1 = 0` (`def:s02-tree`, `s02-tree`). -/
theorem vdet_one : vdet q 1 = 0 := by
  simp only [vdet, Units.val_one, Matrix.det_one, Padic.valuation_one, Int.cast_zero]

variable (q) in
/-- `vdet α = 1`: `v₁ = α v₀` has type `1` (`def:s02-tree`, `s02-tree`). -/
theorem vdet_alphaq : vdet q (alphaq q) = 1 := by
  simp only [vdet, alphaq, Local.diagOneP, Local.matGL_val, Matrix.det_fin_two_of]
  rw [show (1 : ℚ_[q]) * q - 0 * 0 = q by ring, Padic.valuation_p, Int.cast_one]

/-- Elements of `GL₂(ℤ_q)` have even determinant valuation (`def:s02-tree`, `s02-tree`). -/
theorem vdet_of_mem_GL2Zl {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ GL2Zl q) : vdet q k = 0 := by
  rw [vdet, valuation_eq_zero_of_norm (Local.mem_GL2Zl_iff.1 hk).2, Int.cast_zero]

/-- Elements of `SL₂(ℚ_q)` have `vdet = 0` (`lem:s02-tree`(b), `s02-tree`). -/
theorem vdet_of_mem_SLq {s : GL (Fin 2) ℚ_[q]} (hs : s ∈ SLq q) : vdet q s = 0 := by
  rw [vdet, mem_SLq_iff.1 hs, Padic.valuation_one, Int.cast_zero]

/-- Elements of `SL₂(ℚ_q)` have determinant of norm `1` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem norm_det_of_mem_SLq {s : GL (Fin 2) ℚ_[q]} (hs : s ∈ SLq q) :
    ‖(Units.val s).det‖ = 1 := by
  rw [mem_SLq_iff.1 hs, norm_one]

/-! ### `lem:s02-tree`(d) -/

/-- Conjugation by `α`: `α⁻¹ !![a, b; c, d] α = !![a, q b; c / q, d]` (proof of `lem:s02-tree`(d),
`s02-tree`). -/
private theorem conj_val {x : GL (Fin 2) ℚ_[q]} {a b c d : ℚ_[q]}
    (hx : Units.val x = !![a, b; c, d]) :
    Units.val ((alphaq q)⁻¹ * x * alphaq q) =
      !![a, (q : ℚ_[q]) * b; (q : ℚ_[q])⁻¹ * c, d] := by
  rw [mul_assoc]
  apply Local.val_inv_mul_eq
  rw [Units.val_mul, hx]
  simp only [alphaq, Local.diagOneP, Local.matGL_val, Matrix.mul_fin_two]
  refine Local.mat_eq ?_ ?_ ?_ ?_
  · ring
  · ring
  · linear_combination c * mul_inv_cancel₀ (qcast_ne_zero q)
  · ring

/-- `lem:s02-tree`(d) (`s02-tree`): `α⁻¹ Iw_q α ⊆ GL₂(ℤ_q)`. -/
theorem alphaq_inv_conj_mem_GL2Zl {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ Iw q) :
    (alphaq q)⁻¹ * k * alphaq q ∈ GL2Zl q := by
  obtain ⟨a, b, c, d, hM, hu, c', hc'⟩ := Local.mem_K0_iff_exists.1 hk
  subst hc'
  refine Local.mem_GL2Zl_of_entries a ((q : ℤ_[q]) * b) c' d ?_ ?_
  · rw [conj_val hM]
    refine Local.mat_eq rfl ?_ ?_ rfl
    · rw [PadicInt.coe_mul, PadicInt.coe_natCast]
    · rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
      linear_combination (c' : ℚ_[q]) * mul_inv_cancel₀ (qcast_ne_zero q)
  · have e : a * d - (q : ℤ_[q]) * b * c' = a * d - b * ((q : ℤ_[q]) ^ 1 * c') := by ring
    rw [e]
    exact hu

variable (q) in
/-- `Iw_q ⊆ α GL₂(ℤ_q) α⁻¹` (`lem:s02-tree`(d), `s02-tree`). -/
theorem Iw_le_Kalpha : Iw q ≤ Kalpha q :=
  fun _ hx => mem_Kalpha_iff.2 (alphaq_inv_conj_mem_GL2Zl hx)

variable (q) in
/-- `lem:s02-tree`(d) (`s02-tree`): `GL₂(ℤ_q) ∩ α GL₂(ℤ_q) α⁻¹ = Iw_q`. -/
theorem GL2Zl_inf_Kalpha : GL2Zl q ⊓ Kalpha q = Iw q := by
  ext x
  rw [Subgroup.mem_inf, mem_Kalpha_iff]
  constructor
  · rintro ⟨hx, hx'⟩
    obtain ⟨a, b, c, d, hM, hu⟩ := Local.mem_GL2Zl_iff_exists.1 hx
    obtain ⟨a', b', c', d', hM', -⟩ := Local.mem_GL2Zl_iff_exists.1 hx'
    rw [conj_val hM] at hM'
    have E : (q : ℚ_[q])⁻¹ * (c : ℚ_[q]) = (c' : ℚ_[q]) := congrFun (congrFun hM' 1) 0
    refine Local.mem_K0_of_entries a b c d hM hu ⟨c', ?_⟩
    apply PadicInt.ext
    push_cast
    linear_combination (q : ℚ_[q]) * E - (c : ℚ_[q]) * mul_inv_cancel₀ (qcast_ne_zero q)
  · intro hx
    exact ⟨Local.K0_le_GL2Zl 1 hx, alphaq_inv_conj_mem_GL2Zl hx⟩

/-! ### Representatives with determinant fixed by `diag(1, u)` -/

/-- If `det k` is a `ℤ_q`-unit, then `D = diag(1, det k) ∈ Iw_q` has `k D⁻¹ ∈ SL₂`
(auxiliary, proof of `lem:s02-tree`(c), `s02-tree`). -/
theorem exists_Iw_det {k : GL (Fin 2) ℚ_[q]}
    (hk : ∃ x : ℤ_[q], IsUnit x ∧ (x : ℚ_[q]) = (Units.val k).det) :
    ∃ D ∈ Iw q, k * D⁻¹ ∈ SLq q ∧ (k * D⁻¹)⁻¹ * k = D := by
  obtain ⟨x, hx, hxk⟩ := hk
  set D : GL (Fin 2) ℚ_[q] := Local.diagGL 1 (Local.intUnit hx.unit) with hDdef
  have hD : D ∈ Iw q := by
    rw [hDdef]
    exact Local.one_diag_mem_K0 hx.unit 1
  have h2 : (Units.val D).det = (Units.val k).det := by
    rw [hDdef, ← hxk, det_diagGL, Units.val_one, one_mul, Local.coe_intUnit, IsUnit.unit_spec]
  refine ⟨D, hD, ?_, by group⟩
  rw [mem_SLq_iff]
  have h1 : (Units.val (k * D⁻¹)).det * (Units.val D).det = (Units.val k).det := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]
  exact mul_right_cancel₀ (Local.det_ne_zero D) (by rw [h1, h2, one_mul])

/-- Every `k ∈ GL₂(ℤ_q)` is `s · i` with `s ∈ SL₂(ℤ_q)`, `i ∈ Iw_q` (proof of `lem:s02-tree`(c),
`s02-tree`). -/
theorem exists_SL2Zq_inv_mul_mem_Iw {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ GL2Zl q) :
    ∃ s ∈ SL2Zq q, s⁻¹ * k ∈ Iw q := by
  obtain ⟨D, hD, hSL, hDk⟩ := exists_Iw_det (Local.det_isUnit_of_mem_GL2Zl hk)
  refine ⟨k * D⁻¹, mem_SL2Zq_iff.2 ⟨hSL, mul_mem hk (inv_mem (Local.K0_le_GL2Zl 1 hD))⟩, ?_⟩
  rw [hDk]
  exact hD

/-- Every `k ∈ α GL₂(ℤ_q) α⁻¹` is `s · i` with `s ∈ K1q`, `i ∈ Iw_q` (proof of `lem:s02-tree`(c),
`s02-tree`). -/
theorem exists_K1q_inv_mul_mem_Iw {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ Kalpha q) :
    ∃ s ∈ K1q q, s⁻¹ * k ∈ Iw q := by
  have hk' := mem_Kalpha_iff.1 hk
  obtain ⟨x, hx, hxk⟩ := Local.det_isUnit_of_mem_GL2Zl hk'
  rw [det_conj_GL] at hxk
  obtain ⟨D, hD, hSL, hDk⟩ := exists_Iw_det ⟨x, hx, hxk⟩
  refine ⟨k * D⁻¹, mem_K1q_iff.2 ⟨hSL, mul_mem hk (inv_mem (Iw_le_Kalpha q hD))⟩, ?_⟩
  rw [hDk]
  exact hD

/-! ### `[GL₂(ℤ_q) : Iw_q] = q + 1` -/

variable (q) in
/-- Representatives of `GL₂(ℤ_q) / Iw_q`: `some j ↦ !![j, 1; 1, 0]`, `none ↦ 1`
(the points `[j : 1]` and `[1 : 0]` of `ℙ¹(𝔽_q)`, `lem:s02-tree`(a)). -/
def rIw : Option (Fin q) → GL (Fin 2) ℚ_[q]
  | none => 1
  | some j => Local.matGL ((j : ℕ) : ℚ_[q]) 1 1 0 (by simp)

variable (q) in
/-- The representatives lie in `GL₂(ℤ_q)` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem rIw_mem (j : Option (Fin q)) : rIw q j ∈ GL2Zl q := by
  cases j with
  | none => exact one_mem _
  | some j =>
    refine Local.mem_GL2Zl_of_entries ((j : ℕ) : ℤ_[q]) 1 1 0 (by simp [rIw]) ?_
    rw [mul_zero, one_mul, zero_sub]
    exact isUnit_one.neg

/-- `!![j, 1; 1, 0] ∉ Iw_q` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem rIw_some_not_mem (j : Fin q) : rIw q (some j) ∉ Iw q := by
  intro h
  obtain ⟨a, b, c, d, hM, -, hc⟩ := Local.mem_K0_iff_exists.1 h
  have E : (1 : ℚ_[q]) = (c : ℚ_[q]) := congrFun (congrFun hM 1) 0
  have hc1 : c = 1 := PadicInt.ext (by simpa using E.symm)
  rw [hc1, pow_one] at hc
  exact (Local.isUnit_iff_not_dvd (1 : ℤ_[q])).1 isUnit_one hc

/-- Every `k ∈ GL₂(ℤ_q)` lies in some `r_j Iw_q` (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem exists_rIw_inv_mul {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ GL2Zl q) :
    ∃ j, (rIw q j)⁻¹ * k ∈ Iw q := by
  have hkdet : ‖(Units.val k).det‖ = 1 := (Local.mem_GL2Zl_iff.1 hk).2
  obtain ⟨a, b, c, d, hM, hu⟩ := Local.mem_GL2Zl_iff_exists.1 hk
  by_cases hc : IsUnit c
  · obtain ⟨j, β, hβ⟩ := Local.exists_fin_dvd c a hc
    have ha : a = (q : ℤ_[q]) * β + ((j : ℕ) : ℤ_[q]) * c := by linear_combination hβ
    subst ha
    refine ⟨some j, Local.inv_mul_mem_K0 c d ((q : ℤ_[q]) * β) (b - ((j : ℕ) : ℤ_[q]) * d)
      ?_ ?_ ?_⟩
    · rw [hM]
      simp only [rIw, Local.matGL_val, Matrix.mul_fin_two]
      refine Local.mat_eq ?_ ?_ ?_ ?_
      all_goals
        simp only [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_natCast]
        ring
    · rw [hkdet]
      simp [rIw, Matrix.det_fin_two_of]
    · exact ⟨β, by ring⟩
  · have hpc : (q : ℤ_[q]) ∣ c := by
      by_contra h
      exact hc ((Local.isUnit_iff_not_dvd c).2 h)
    refine ⟨none, ?_⟩
    show (1 : GL (Fin 2) ℚ_[q])⁻¹ * k ∈ Iw q
    rw [inv_one, one_mul]
    exact Local.mem_K0_of_entries a b c d hM hu (by rw [pow_one]; exact hpc)

variable (q) in
/-- The map `Option (Fin q) → GL₂(ℤ_q) / Iw_q`, `j ↦ r_j Iw_q` (auxiliary, `lem:s02-tree`,
`s02-tree`). -/
def cosetIw (j : Option (Fin q)) : GL2Zl q ⧸ (Iw q).subgroupOf (GL2Zl q) :=
  ((⟨rIw q j, rIw_mem q j⟩ : GL2Zl q) : GL2Zl q ⧸ (Iw q).subgroupOf (GL2Zl q))

variable (q) in
/-- `cosetIw` is injective (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem cosetIw_injective : Function.Injective (cosetIw q) := by
  intro i j h
  unfold cosetIw at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have h' : (rIw q i)⁻¹ * rIw q j ∈ Iw q := h
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · exfalso
    have h2 : (1 : GL (Fin 2) ℚ_[q])⁻¹ * rIw q (some j) ∈ Iw q := h'
    rw [inv_one, one_mul] at h2
    exact rIw_some_not_mem j h2
  · exfalso
    have h2 : (rIw q (some i))⁻¹ * 1 ∈ Iw q := h'
    rw [mul_one] at h2
    exact rIw_some_not_mem i (inv_mem_iff.1 h2)
  · have hV : Units.val ((rIw q (some i))⁻¹ * rIw q (some j)) =
        !![1, 0; ((j : ℕ) : ℚ_[q]) - ((i : ℕ) : ℚ_[q]), 1] := by
      apply Local.val_inv_mul_eq
      simp only [rIw, Local.matGL_val, Matrix.mul_fin_two]
      refine Local.mat_eq ?_ ?_ ?_ ?_ <;> ring
    obtain ⟨a, b, c, d, hM, -, γ, hγ⟩ := Local.mem_K0_iff_exists.1 h'
    rw [hV] at hM
    have E : ((j : ℕ) : ℚ_[q]) - ((i : ℕ) : ℚ_[q]) = (c : ℚ_[q]) := congrFun (congrFun hM 1) 0
    have hγ' : (c : ℚ_[q]) = (q : ℚ_[q]) * γ := by
      rw [hγ, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, pow_one]
    have hdvd : (q : ℤ_[q]) ∣ ((j : ℕ) : ℤ_[q]) - ((i : ℕ) : ℤ_[q]) :=
      ⟨γ, PadicInt.ext (by push_cast; linear_combination E + hγ')⟩
    exact congrArg some (Local.fin_eq_of_dvd hdvd).symm

variable (q) in
/-- `cosetIw` is surjective (auxiliary, `lem:s02-tree`, `s02-tree`). -/
theorem cosetIw_surjective : Function.Surjective (cosetIw q) := by
  intro x
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨j, hj⟩ := exists_rIw_inv_mul hk
  refine ⟨j, ?_⟩
  unfold cosetIw
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact hj

variable (q) in
/-- Index `[GL₂(ℤ_q) : Iw_q] = q + 1` (`s02-tree`; input to `lem:s02-tree`(a), which is cited; the
identification with the neighbours of `v₀` is not formalized here). -/
theorem relIndex_Iw : (Iw q).relIndex (GL2Zl q) = q + 1 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.ofBijective _ ⟨cosetIw_injective q, cosetIw_surjective q⟩),
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

end

end Langlandscape.Tree
