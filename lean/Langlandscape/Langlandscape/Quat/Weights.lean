/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic
import AlgJL.VolIII.P2.Mass

/-!
# Finiteness and weights (S01-L6)

Level change for the class sets `X_B(U)` and the weights `w_x`
(`plan/staged/stage-01-quaternion-foundations.tex`, `prop:s01-finite`, `thm:s01-mass`(b), `def:s01-classset`).

* `XB_finite_of_relIndex` : `X_B(U')` is finite when `X_B(U)` is and `[U : U'] < ∞`.
* `mem_Gam_iff`, `Gam_translate`, `wx_translate` : behaviour of `Γ_x(U)` and `w_x` under `x ↦ γ x u`.
* `negOne` : the element `-1 ∈ B̂^×`; `two_mul_wx`, `wx_eq_card` : `|Γ_x| = 2 w_x` iff `-1 ∈ U`.
* `massW U = ∑ 1/w_x`; `massW_level_change` (`-1 ∈ U'` or `-1 ∉ U`: factor `[U : U']`) and
  `massW_level_change_two` (`-1 ∈ U ∖ U'`: `2 · massW U' = [U : U'] · massW U`).

Status: *formalized* (orbit counting from the import's `mass_orbit_count`).
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

variable {a b : ℤ}

/-- Proof helper: the diagonal embedding `B^× → B̂^×`. -/
noncomputable abbrev iotaU (a b : ℤ) :
    (GL2TF.Quat.QuatAlg ℚ a b)ˣ →* (GL2TF.Quat.BHat a b)ˣ :=
  Units.map (GL2TF.Quat.finEmbed a b).toMonoidHom

/-- `prop:s01-finite` (level change): if `U' ≤ U` has finite relative index and `X_B(U)` is finite then so is
`X_B(U')` (`s01-finite`). -/
theorem XB_finite_of_relIndex {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (_hle : U' ≤ U)
    (h : U'.relIndex U ≠ 0) [Finite (XB U)] : Finite (XB U') := by
  classical
  set W := U'.subgroupOf U with hW
  have : W.FiniteIndex := ⟨h⟩
  have hXfin : Finite (↥U ⧸ W) := Subgroup.finite_quotient_of_finiteIndex
  let Φ : XB U × (↥U ⧸ W) → XB U' :=
    fun z => DoubleCoset.mk (globalUnits a b) U'
      (Quotient.out z.1 * ((Quotient.out z.2 : U) : (GL2TF.Quat.BHat a b)ˣ))
  have hΦ : Function.Surjective Φ := by
    intro d
    induction d using Quotient.inductionOn' with
    | h y =>
      obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U y
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W (⟨k, hk⟩ : U)⁻¹
      refine ⟨(DoubleCoset.mk (globalUnits a b) U y, QuotientGroup.mk (⟨k, hk⟩ : U)⁻¹), ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ y
      rw [DoubleCoset.eq]
      refine ⟨h⁻¹, (globalUnits a b).inv_mem hh, ((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹,
        U'.inv_mem (Subgroup.mem_subgroupOf.mp w.2), ?_⟩
      rw [hw, he]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
  exact Finite.of_surjective Φ hΦ

/-! ### The element `-1` and stabilisers -/

/-- `-1 ∈ B̂^×` (`def:s01-classset`); it is the image of `-1 ∈ B^×`. -/
noncomputable def negOne : (GL2TF.Quat.BHat a b)ˣ := -1

/-- `def:s01-classset`: `ι(-1) = -1` (`s01-classset`). -/
theorem iotaU_neg_one : iotaU a b (-1) = (negOne : (GL2TF.Quat.BHat a b)ˣ) := by
  ext; simp [iotaU, negOne]

/-- `def:s01-classset`: `-1` is central in `B̂^×` (`s01-classset`). -/
theorem negOne_comm (x : (GL2TF.Quat.BHat a b)ˣ) : x * negOne = negOne * x := by
  ext; simp [negOne]

/-- Membership in `Γ_x(U)` (`def:s01-classset`): `γ ∈ Γ_x(U) ↔ x⁻¹ γ x ∈ U`. -/
theorem mem_Gam_iff (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ)
    (δ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) : δ ∈ Gam U x ↔ x⁻¹ * iotaU a b δ * x ∈ U := by
  simp only [Gam, GL2TF.Quat.classStabilizer, Subgroup.mem_comap, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, hδ⟩
    have : x⁻¹ * iotaU a b δ * x = v := by rw [← hδ]; group
    rwa [this]
  · intro h
    exact ⟨_, h, by group⟩

/-- `def:s01-classset` (translation): for `u ∈ U`, `Γ_{γ x u}(U) = γ Γ_x(U) γ⁻¹` (`s01-classset`; imp
`stabilizer_units`(b) for general `U`). -/
theorem Gam_translate (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ)
    (x u : (GL2TF.Quat.BHat a b)ˣ) (hu : u ∈ U) :
    Gam U (iotaU a b γ * x * u) = (Gam U x).map (MulAut.conj γ).toMonoidHom := by
  ext δ
  rw [mem_Gam_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨γ⁻¹ * δ * γ, (mem_Gam_iff U x _).2 ?_, by
      show γ * (γ⁻¹ * δ * γ) * γ⁻¹ = δ
      group⟩
    have : x⁻¹ * iotaU a b (γ⁻¹ * δ * γ) * x = u * (((iotaU a b γ * x * u)⁻¹ * iotaU a b δ *
        (iotaU a b γ * x * u))) * u⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [this]
    exact U.mul_mem (U.mul_mem hu h) (U.inv_mem hu)
  · rintro ⟨ε, hε, rfl⟩
    have h := (mem_Gam_iff U x ε).1 hε
    have : (iotaU a b γ * x * u)⁻¹ * iotaU a b ((MulAut.conj γ).toMonoidHom ε) *
        (iotaU a b γ * x * u) = u⁻¹ * (x⁻¹ * iotaU a b ε * x) * u := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]; group
    rw [this]
    exact U.mul_mem (U.mul_mem (U.inv_mem hu) h) hu

/-- `-1 ∈ Γ_x(U) ↔ -1 ∈ U` (`def:s01-classset`; `-1` is central). -/
theorem neg_one_mem_Gam_iff (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    (-1 : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ Gam U x ↔ (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U := by
  rw [mem_Gam_iff, iotaU_neg_one]
  have : x⁻¹ * negOne * x = negOne := by
    rw [mul_assoc, ← negOne_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]

/-- `def:s01-classset`: `z ∈ {±1} ↔ z = 1 ∨ z = -1` (`s01-classset`). -/
theorem mem_pmOne_iff (z : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) : z ∈ (pmOne : Subgroup _) ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd n with h | h
    · left; exact h.neg_one_zpow
    · right; exact h.neg_one_zpow
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

/-- `def:s01-classset`: `-1 ≠ 1` in `B^×` (`s01-classset`). -/
theorem neg_one_ne_one_B : (-1 : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ≠ 1 := by
  intro h
  have := congrArg (fun z : (GL2TF.Quat.QuatAlg ℚ a b)ˣ => (z : GL2TF.Quat.QuatAlg ℚ a b).re) h
  simp at this
  norm_num at this

/-- `|{±1}| = 2` (`def:s01-classset`). -/
theorem card_pmOne : Nat.card (pmOne : Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pmOne, Nat.card_zpowers]
  exact orderOf_eq_prime (by simp) neg_one_ne_one_B

/-- `lem:s01-stab`/`def:s01-classset`: if `-1 ∈ U`, then `|Γ_x| = 2 w_x` (`s01-classset`). -/
theorem two_mul_wx {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (h : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U)
    (x : (GL2TF.Quat.BHat a b)ˣ) : 2 * wx U x = Nat.card (Gam U x) := by
  have hle : (pmOne : Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ≤ Gam U x := by
    intro z hz
    rcases (mem_pmOne_iff z).1 hz with rfl | rfl
    · exact one_mem _
    · exact (neg_one_mem_Gam_iff U x).2 h
  have hinf : Gam U x ⊓ pmOne = pmOne := inf_eq_right.2 hle
  have hdvd : Nat.card (pmOne : Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∣ Nat.card (Gam U x) := by
    have := Subgroup.card_dvd_of_le hle
    simpa using this
  rw [wx, hinf, card_pmOne]
  rw [card_pmOne] at hdvd
  exact Nat.mul_div_cancel' hdvd

/-- `def:s01-classset`: if `-1 ∉ U`, then `w_x = |Γ_x|` (`s01-classset`). -/
theorem wx_eq_card {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (h : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U)
    (x : (GL2TF.Quat.BHat a b)ˣ) : wx U x = Nat.card (Gam U x) := by
  have hinf : Gam U x ⊓ pmOne = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rcases (mem_pmOne_iff z).1 hz2 with rfl | rfl
    · exact one_mem _
    · exact absurd ((neg_one_mem_Gam_iff U x).1 hz1) h
  rw [wx, hinf]
  simp

/-- `def:s01-classset`: conjugation preserves `{±1}` (`s01-classset`). -/
theorem map_conj_pmOne (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) :
    (pmOne : Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ).map (MulAut.conj γ).toMonoidHom = pmOne := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases (mem_pmOne_iff w).1 hw with rfl | rfl
    · simp [one_mem]
    · have : (MulAut.conj γ).toMonoidHom (-1) = -1 := by
        show γ * (-1) * γ⁻¹ = -1
        simp
      rw [this]; exact (mem_pmOne_iff _).2 (Or.inr rfl)
  · intro hz
    refine ⟨γ⁻¹ * z * γ, ?_, by show γ * (γ⁻¹ * z * γ) * γ⁻¹ = z; group⟩
    rcases (mem_pmOne_iff z).1 hz with rfl | rfl
    · simp [one_mem]
    · have : γ⁻¹ * (-1 : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) * γ = -1 := by simp
      rw [this]; exact (mem_pmOne_iff _).2 (Or.inr rfl)

/-- `def:s01-classset` (translation): `w_{γ x u} = w_x` for `u ∈ U` (`s01-classset`). -/
theorem wx_translate (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ)
    (x u : (GL2TF.Quat.BHat a b)ˣ) (hu : u ∈ U) : wx U (iotaU a b γ * x * u) = wx U x := by
  have hT := Gam_translate U γ x u hu
  have hinj := (MulAut.conj γ).injective
  have hc : Nat.card (Gam U (iotaU a b γ * x * u)) = Nat.card (Gam U x) := by
    rw [hT]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj γ).toMonoidHom hinj).toEquiv.symm
  have hp : Nat.card ↥(Gam U (iotaU a b γ * x * u) ⊓ pmOne) = Nat.card ↥(Gam U x ⊓ pmOne) := by
    have : Gam U (iotaU a b γ * x * u) ⊓ pmOne =
        (Gam U x ⊓ pmOne).map (MulAut.conj γ).toMonoidHom := by
      rw [hT, Subgroup.map_inf_eq _ _ _ hinj, map_conj_pmOne]
    rw [this]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj γ).toMonoidHom hinj).toEquiv.symm
  rw [wx, wx, hc, hp]

/-- `def:s01-classset`: `w` is constant on double cosets, so `wx U c.out = wx U x` for `c = [x]` (`s01-classset`). -/
theorem wx_out (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    wx U (Quotient.out (DoubleCoset.mk (globalUnits a b) U x : XB U)) = wx U x := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
  rw [he]
  exact wx_translate U k x v hv

/-! ### Weighted mass -/

/-- `thm:s01-mass`: the weighted mass `∑_{c ∈ X_B(U)} 1/w_{x_c}` (representatives `c.out`; `s01-mass`). -/
noncomputable def massW (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) : ℚ :=
  ∑ᶠ c : XB U, (1 : ℚ) / (wx U (Quotient.out c) : ℚ)

/-- `thm:s01-mass`: `massFull U` against `massW U` (`s01-mass`): `massFull = massW / 2` if `-1 ∈ U`. -/
theorem massFull_eq_massW_of_mem {U : Subgroup (GL2TF.Quat.BHat a b)ˣ}
    (h : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) [Finite (XB U)] : massFull U = massW U / 2 := by
  classical
  have : Fintype (XB U) := Fintype.ofFinite _
  rw [massFull, massW, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← two_mul_wx h]
  push_cast
  rw [one_div, one_div, mul_inv, div_eq_mul_inv, mul_comm]

/-- `thm:s01-mass`: `massFull U = massW U` if `-1 ∉ U` (`s01-mass`). -/
theorem massFull_eq_massW_of_not_mem {U : Subgroup (GL2TF.Quat.BHat a b)ˣ}
    (h : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U) : massFull U = massW U := by
  rw [massFull, massW]
  refine finsum_congr fun c => ?_
  rw [wx_eq_card h]

/-- `thm:s01-mass`(b), `w`-variant (`s01-mass`): if `-1 ∈ U'` or `-1 ∉ U` then
`massW U' = [U : U'] · massW U`. -/
theorem massW_level_change {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    (h : U'.relIndex U ≠ 0) [Finite (XB U)]
    (hneg : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U' ∨ (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U) :
    massW U' = (U'.relIndex U : ℚ) * massW U := by
  have hfin' : Finite (XB U') := XB_finite_of_relIndex hle h
  have key := GL2TF.Quat.mass_orbit_count U' U hle h ‹Finite (XB U)›
  change massFull U' = (U'.relIndex U : ℚ) * massFull U at key
  rcases hneg with h1 | h1
  · rw [massFull_eq_massW_of_mem h1, massFull_eq_massW_of_mem (hle h1)] at key
    linarith
  · have h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U' := fun hh => h1 (hle hh)
    rw [massFull_eq_massW_of_not_mem h2, massFull_eq_massW_of_not_mem h1] at key
    exact key

/-- `thm:s01-mass`(b), the factor-2 case (`s01-mass`): if `-1 ∈ U ∖ U'` then
`2 · massW U' = [U : U'] · massW U`. -/
theorem massW_level_change_two {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    (h : U'.relIndex U ≠ 0) [Finite (XB U)]
    (h1 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) (h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U') :
    2 * massW U' = (U'.relIndex U : ℚ) * massW U := by
  have key := GL2TF.Quat.mass_orbit_count U' U hle h ‹Finite (XB U)›
  change massFull U' = (U'.relIndex U : ℚ) * massFull U at key
  rw [massFull_eq_massW_of_not_mem h2, massFull_eq_massW_of_mem h1] at key
  linarith

end Langlandscape.Quat
