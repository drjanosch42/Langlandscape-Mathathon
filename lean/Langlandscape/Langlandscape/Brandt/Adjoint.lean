/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.DoubleCoset

/-!
# Adjoints of double-coset operators and equivariance of the norm map (S01-L8b)

`plan/staged/stage-01-quaternion-foundations.tex`, `prop:s01-adjoint` (a)–(c), trivial coefficients.

* `natCard_eq_mul_of_fibers` : orbit counting, `|E| = |Q| · |Γ|` for a surjection `E → Q` whose fibres are the
  left cosets of `Γ`.
* `heckeCount U g x y` : the number of cosets `hU ⊆ U g U` with `x h ∈ B^× y U`, so that
  `(T_g 1_{[y]})([x]) = heckeCount U g x y` (`heckeT_single_apply`);
  `heckeCount_mul_wx` : `heckeCount U g x y · w_y = heckeCount U g⁻¹ y x · w_x` (Gross, Prop. 6.9).
* `normMap_heckeT` : `ν ∘ T_g = T_{g⁻¹} ∘ ν` (`prop:s01-adjoint`(b));
  `brandtPairing_heckeTHom` : `⟨T_g a, b⟩ = ⟨a, T_{g⁻¹} b⟩` (`prop:s01-adjoint`(a)).
* `levelMap`, `pushforward U' U R : R[X'] → R[X]` (`π_*`) and `trace U' U R hrel : R^{X'} → R^X`
  (`tr f (x) = ∑_{u ∈ U/U'} f(x u)`) for `U' ≤ U`;
  `normMap_pushforward` : `ν ∘ π_* = tr ∘ ν'` if `-1 ∈ U'` or `-1 ∉ U`, and
  `normMap_pushforward_two` : `tr ∘ ν' = 2 · ν ∘ π_*` if `-1 ∈ U ∖ U'` (`prop:s01-adjoint`(c)).

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

variable {a b : ℤ}

section Counting

/-- `prop:s01-adjoint` (`s01-adjoint`), orbit counting: if `φ : E → Q` is surjective, `E ⊆ H` is stable under right
multiplication by `Γ` and the fibres of `φ` are exactly the classes `γ Γ`, then `|E| = |Q| · |Γ|` (as `Nat.card`). -/
theorem natCard_eq_mul_of_fibers {H : Type*} [Group H] (P : H → Prop) (Γ : Subgroup H) {Q : Type*}
    (φ : {γ // P γ} → Q) (hsurj : Function.Surjective φ)
    (hmul : ∀ γ δ : H, P γ → δ ∈ Γ → P (γ * δ))
    (hfib : ∀ γ γ' : {γ // P γ}, φ γ = φ γ' ↔ (γ : H)⁻¹ * (γ' : H) ∈ Γ) :
    Nat.card {γ // P γ} = Nat.card Q * Nat.card Γ := by
  let s := Function.surjInv hsurj
  have hs : ∀ q, φ (s q) = q := Function.surjInv_eq hsurj
  let e : {γ // P γ} ≃ Q × Γ :=
    { toFun := fun γ => (φ γ, ⟨((s (φ γ) : H))⁻¹ * (γ : H), (hfib _ _).1 (hs (φ γ))⟩)
      invFun := fun p => ⟨(s p.1 : H) * (p.2 : H), hmul _ _ (s p.1).2 p.2.2⟩
      left_inv := by
        intro γ
        apply Subtype.ext
        show (s (φ γ) : H) * ((s (φ γ) : H)⁻¹ * (γ : H)) = γ
        exact mul_inv_cancel_left _ _
      right_inv := by
        rintro ⟨q, δ⟩
        have h1 : φ ⟨(s q : H) * (δ : H), hmul _ _ (s q).2 δ.2⟩ = q := by
          refine ((hfib _ _).2 ?_).trans (hs q)
          show ((s q : H) * (δ : H))⁻¹ * (s q : H) ∈ Γ
          rw [mul_inv_rev, inv_mul_cancel_right]
          exact Γ.inv_mem δ.2
        refine Prod.ext h1 (Subtype.ext ?_)
        show ((s (φ ⟨(s q : H) * (δ : H), hmul _ _ (s q).2 δ.2⟩) : H))⁻¹ * ((s q : H) * (δ : H)) = δ
        rw [h1, inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_prod]

/-- `prop:s01-adjoint` (`s01-adjoint`), helper: a `finsum` of a `0/1`-valued function with finite support set
`{q | P q}` is `Nat.card {q // P q}`. -/
theorem finsum_eq_natCard {α R : Type*} [CommRing R] (f : α → R) (P : α → Prop) (hP : {q | P q}.Finite)
    (h1 : ∀ q, P q → f q = 1) (h0 : ∀ q, ¬ P q → f q = 0) :
    ∑ᶠ q, f q = (Nat.card {q // P q} : R) := by
  have hsupp : Function.support f ⊆ ↑hP.toFinset := by
    intro q hq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    exact hq (h0 q hn)
  rw [finsum_eq_sum_of_support_subset f hsupp]
  calc ∑ q ∈ hP.toFinset, f q = ∑ _q ∈ hP.toFinset, (1 : R) :=
        Finset.sum_congr rfl fun q hq => h1 q ((Set.Finite.mem_toFinset hP).1 hq)
    _ = (hP.toFinset.card : R) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (Nat.card {q // P q} : R) := by rw [← Nat.card_eq_card_finite_toFinset hP]; rfl

end Counting

section HeckeCount

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)

/-- `prop:s01-adjoint` (`s01-adjoint`): `(U g U)⁻¹ = U g⁻¹ U`. -/
theorem inv_mem_dcSet_inv {y : (GL2TF.Quat.BHat a b)ˣ} (h : y ∈ dcSet U g) : y⁻¹ ∈ dcSet U g⁻¹ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U g).1 h
  exact (mem_dcSet U g⁻¹).2 ⟨v⁻¹, U.inv_mem hv, u⁻¹, U.inv_mem hu, by group⟩

/-- `prop:s01-adjoint` (`s01-adjoint`): `(U g⁻¹ U)⁻¹ = U g U`. -/
theorem inv_mem_dcSet_of_inv {y : (GL2TF.Quat.BHat a b)ˣ} (h : y ∈ dcSet U g⁻¹) : y⁻¹ ∈ dcSet U g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U g⁻¹).1 h
  exact (mem_dcSet U g).2 ⟨v⁻¹, U.inv_mem hv, u⁻¹, U.inv_mem hu, by group⟩

/-- `prop:s01-adjoint` (`s01-adjoint`): the number of left cosets `hU ⊆ U g U` with `B^× x h U = B^× y U`;
it is the entry `(T_g 1_{[y]})([x])` of the Brandt matrix (`heckeT_single_apply_mk`). -/
noncomputable def heckeCount (x y : (GL2TF.Quat.BHat a b)ˣ) : ℕ :=
  Nat.card {q : (GL2TF.Quat.BHat a b)ˣ ⧸ U // Quotient.out q ∈ dcSet U g ∧
    DoubleCoset.mk (globalUnits a b) U (x * Quotient.out q) = DoubleCoset.mk (globalUnits a b) U y}

/-- `prop:s01-adjoint` (`s01-adjoint`), helper: representatives of cosets in `U g U` lie in `U g U`. -/
theorem out_mk_mem_dcSet {h : (GL2TF.Quat.BHat a b)ˣ} (hh : h ∈ dcSet U g) :
    Quotient.out (QuotientGroup.mk h : (GL2TF.Quat.BHat a b)ˣ ⧸ U) ∈ dcSet U g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U h
  rw [hu]
  exact (mul_mem_dcSet_iff_right U g u.2).2 hh

/-- `prop:s01-adjoint` (`s01-adjoint`), helper: `B^× x (x⁻¹ γ y u) U = B^× y U`. -/
theorem mk_mul_out_mk (x y : (GL2TF.Quat.BHat a b)ˣ) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) :
    DoubleCoset.mk (globalUnits a b) U
        (x * Quotient.out (QuotientGroup.mk (x⁻¹ * iotaU a b γ * y) : (GL2TF.Quat.BHat a b)ˣ ⧸ U)) =
      DoubleCoset.mk (globalUnits a b) U y := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (x⁻¹ * iotaU a b γ * y)
  rw [hu, DoubleCoset.eq]
  refine ⟨(iotaU a b γ)⁻¹, (globalUnits a b).inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩),
    ((u : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹, U.inv_mem u.2, ?_⟩
  group

/-- `prop:s01-adjoint` (`s01-adjoint`): the map `γ ↦ x⁻¹ γ y U` from `{γ ∈ B^× | x⁻¹ γ y ∈ U g U}` to the cosets
counted by `heckeCount U g x y`. -/
noncomputable def heckeCountMap (x y : (GL2TF.Quat.BHat a b)ˣ)
    (γ : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ dcSet U g}) :
    {q : (GL2TF.Quat.BHat a b)ˣ ⧸ U // Quotient.out q ∈ dcSet U g ∧
      DoubleCoset.mk (globalUnits a b) U (x * Quotient.out q) = DoubleCoset.mk (globalUnits a b) U y} :=
  ⟨QuotientGroup.mk (x⁻¹ * iotaU a b γ.1 * y), out_mk_mem_dcSet U g γ.2, mk_mul_out_mk U x y γ.1⟩

/-- `prop:s01-adjoint` (`s01-adjoint`), orbit counting:
`|{γ ∈ B^× | x⁻¹ γ y ∈ U g U}| = heckeCount U g x y · |Γ_y|`. -/
theorem natCard_heckeSet (x y : (GL2TF.Quat.BHat a b)ˣ) :
    Nat.card {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ dcSet U g} =
      heckeCount U g x y * Nat.card (Gam U y) := by
  have hsurj : Function.Surjective (heckeCountMap U g x y) := by
    rintro ⟨q, hq1, hq2⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, he⟩ := DoubleCoset.eq.1 hq2
    change y = iotaU a b γ * (x * Quotient.out q) * k at he
    have e1 : x⁻¹ * iotaU a b γ⁻¹ * y = Quotient.out q * k := by
      rw [he, map_inv]
      group
    have hmem : x⁻¹ * iotaU a b γ⁻¹ * y ∈ dcSet U g := by
      rw [e1]
      exact (mul_mem_dcSet_iff_right U g hk).2 hq1
    refine ⟨⟨γ⁻¹, hmem⟩, Subtype.ext ?_⟩
    show (QuotientGroup.mk (x⁻¹ * iotaU a b γ⁻¹ * y) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = q
    rw [e1, QuotientGroup.mk_mul_of_mem _ hk, QuotientGroup.out_eq']
  have hmul : ∀ γ δ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ, x⁻¹ * iotaU a b γ * y ∈ dcSet U g →
      δ ∈ Gam U y → x⁻¹ * iotaU a b (γ * δ) * y ∈ dcSet U g := by
    intro γ δ hγ hδ
    have e : x⁻¹ * iotaU a b (γ * δ) * y = (x⁻¹ * iotaU a b γ * y) * (y⁻¹ * iotaU a b δ * y) := by
      rw [map_mul]
      group
    rw [e]
    exact (mul_mem_dcSet_iff_right U g ((mem_Gam_iff U y δ).1 hδ)).2 hγ
  have hfib : ∀ γ γ' : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ dcSet U g},
      heckeCountMap U g x y γ = heckeCountMap U g x y γ' ↔
        ((γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ))⁻¹ * (γ' : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ Gam U y := by
    intro γ γ'
    refine Subtype.ext_iff.trans ?_
    show (QuotientGroup.mk (x⁻¹ * iotaU a b γ.1 * y) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) =
        QuotientGroup.mk (x⁻¹ * iotaU a b γ'.1 * y) ↔ γ.1⁻¹ * γ'.1 ∈ Gam U y
    rw [QuotientGroup.eq, mem_Gam_iff]
    have e : (x⁻¹ * iotaU a b γ.1 * y)⁻¹ * (x⁻¹ * iotaU a b γ'.1 * y) =
        y⁻¹ * iotaU a b (γ.1⁻¹ * γ'.1) * y := by
      rw [map_mul, map_inv]
      group
    rw [e]
  exact natCard_eq_mul_of_fibers (fun γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ => x⁻¹ * iotaU a b γ * y ∈ dcSet U g)
    (Gam U y) (heckeCountMap U g x y) hsurj hmul hfib

/-- `prop:s01-adjoint`(a) (`s01-adjoint`), orbit counting (Gross, Prop. 6.9, trivial coefficients):
`heckeCount U g x y · |Γ_y| = heckeCount U g⁻¹ y x · |Γ_x|`. -/
theorem heckeCount_mul_card (x y : (GL2TF.Quat.BHat a b)ˣ) :
    heckeCount U g x y * Nat.card (Gam U y) = heckeCount U g⁻¹ y x * Nat.card (Gam U x) := by
  have e : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ dcSet U g} ≃
      {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // y⁻¹ * iotaU a b γ * x ∈ dcSet U g⁻¹} :=
    { toFun := fun γ => ⟨γ.1⁻¹, by
        have h := inv_mem_dcSet_inv U g γ.2
        have e1 : (x⁻¹ * iotaU a b γ.1 * y)⁻¹ = y⁻¹ * iotaU a b γ.1⁻¹ * x := by
          rw [map_inv]
          group
        rwa [e1] at h⟩
      invFun := fun γ => ⟨γ.1⁻¹, by
        have h := inv_mem_dcSet_of_inv U g γ.2
        have e1 : (y⁻¹ * iotaU a b γ.1 * x)⁻¹ = x⁻¹ * iotaU a b γ.1⁻¹ * y := by
          rw [map_inv]
          group
        rwa [e1] at h⟩
      left_inv := fun γ => Subtype.ext (inv_inv _)
      right_inv := fun γ => Subtype.ext (inv_inv _) }
  rw [← natCard_heckeSet U g x y, ← natCard_heckeSet U g⁻¹ y x]
  exact Nat.card_congr e

/-- `prop:s01-adjoint`(a),(b) (`s01-adjoint`): the weighted symmetry of the Brandt matrix,
`heckeCount U g x y · w_y = heckeCount U g⁻¹ y x · w_x` (both when `-1 ∈ U` and when `-1 ∉ U`). -/
theorem heckeCount_mul_wx (x y : (GL2TF.Quat.BHat a b)ˣ) :
    heckeCount U g x y * wx U y = heckeCount U g⁻¹ y x * wx U x := by
  have hcard := heckeCount_mul_card U g x y
  by_cases h : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U
  · rw [← two_mul_wx h y, ← two_mul_wx h x] at hcard
    have h2 : 2 * (heckeCount U g x y * wx U y) = 2 * (heckeCount U g⁻¹ y x * wx U x) := by
      calc 2 * (heckeCount U g x y * wx U y) = heckeCount U g x y * (2 * wx U y) := by ring
        _ = heckeCount U g⁻¹ y x * (2 * wx U x) := hcard
        _ = 2 * (heckeCount U g⁻¹ y x * wx U x) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  · rw [wx_eq_card h y, wx_eq_card h x]
    exact hcard

variable (R : Type*) [CommRing R] (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)

/-- `prop:s01-adjoint` (`s01-adjoint`): `(T_g 1_c')([x]) = heckeCount U g x c'.out`. -/
theorem heckeT_single_apply_mk (c' : XB U) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeT U g R hfin (Pi.single c' (1 : R)) (DoubleCoset.mk (globalUnits a b) U x) =
      (heckeCount U g x (Quotient.out c') : R) := by
  rw [heckeT_apply_mk]
  simp only [GL2TF.HeckeModule.heckeAct, heckeCount]
  refine finsum_eq_natCard _ _ ?_ ?_ ?_
  · refine (finite_cosets_dcSet U g hfin).subset ?_
    intro q hq
    exact ⟨Quotient.out q, hq.1, QuotientGroup.out_eq' q⟩
  · intro q hq
    rw [coe_heckeFun, heckeCoeff_of_mem U g R hq.1, one_smul]
    simp only [liftFun]
    rw [hq.2, DoubleCoset.out_eq', Pi.single_eq_same]
  · intro q hq
    by_cases h1 : Quotient.out q ∈ dcSet U g
    · have h2 : DoubleCoset.mk (globalUnits a b) U (x * Quotient.out q) ≠ c' :=
        fun h => hq ⟨h1, h.trans (DoubleCoset.out_eq' c').symm⟩
      rw [coe_heckeFun, heckeCoeff_of_mem U g R h1, one_smul]
      simp only [liftFun]
      exact Pi.single_eq_of_ne h2 1
    · rw [coe_heckeFun, heckeCoeff_of_notMem U g R h1, zero_smul]

/-- `prop:s01-adjoint` (`s01-adjoint`): the Brandt matrix entry `(T_g 1_{c'})(c) = heckeCount U g c.out c'.out`. -/
theorem heckeT_single_apply (c c' : XB U) :
    heckeT U g R hfin (Pi.single c' (1 : R)) c = (heckeCount U g (Quotient.out c) (Quotient.out c') : R) := by
  have h := heckeT_single_apply_mk U g R hfin c' (Quotient.out c)
  rwa [DoubleCoset.out_eq'] at h

end HeckeCount

section Adjoint

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): the norm map intertwines `T_g` on `R[X]` with `T_{g⁻¹}` on `R^X`,
`ν ∘ T_g = T_{g⁻¹} ∘ ν` (trivial coefficients, finite `X`). -/
theorem normMap_heckeT [Finite (XB U)] (hfin' : (U ⊓ conjSub U g⁻¹).relIndex U ≠ 0) (x : ZX U R) :
    normMap U R (heckeTHom U g R hfin x) = heckeT U g⁻¹ R hfin' (normMap U R x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single c r =>
    funext c'
    rw [normMap_apply, heckeTHom_single_apply, normMap_single, map_smul, Pi.smul_apply, smul_eq_mul,
      heckeT_single_apply, heckeT_single_apply]
    have key : (heckeCount U g (Quotient.out c) (Quotient.out c') : R) * (wx U (Quotient.out c') : R) =
        (heckeCount U g⁻¹ (Quotient.out c') (Quotient.out c) : R) * (wx U (Quotient.out c) : R) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, heckeCount_mul_wx U g (Quotient.out c) (Quotient.out c')]
    linear_combination r * key

/-- `prop:s01-adjoint`(a) (`s01-adjoint`): the adjoint of `T_g` on `R[X]` for the Brandt pairing is `T_{g⁻¹}`,
`⟨T_g a, b⟩ = ⟨a, T_{g⁻¹} b⟩` (trivial coefficients, finite `X`; Gross, Prop. 6.9). -/
theorem brandtPairing_heckeTHom [Finite (XB U)] (hfin' : (U ⊓ conjSub U g⁻¹).relIndex U ≠ 0)
    (x y : ZX U R) :
    brandtPairing U R (heckeTHom U g R hfin x) y = brandtPairing U R x (heckeTHom U g⁻¹ R hfin' y) := by
  rw [brandtPairing_eq_evalPairing_normMap, brandtPairing_eq_evalPairing_normMap,
    normMap_heckeT U g R hfin hfin', heckeTHom_transpose]

end Adjoint

section Pushforward

variable (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ)

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `[U : U'] < ∞` makes `U / U'` finite. -/
theorem finite_quotient_of_relIndex (hrel : U'.relIndex U ≠ 0) : Finite (↥U ⧸ U'.subgroupOf U) := by
  have : (U'.subgroupOf U).FiniteIndex := ⟨hrel⟩
  exact Subgroup.finite_quotient_of_finiteIndex

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): for `U' ≤ U`, `B^× x U' = B^× y U'` implies `B^× x U = B^× y U`. -/
theorem mk_eq_mk_of_le {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U' x = DoubleCoset.mk (globalUnits a b) U' y) :
    DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y := by
  obtain ⟨h1, hh1, k, hk, e⟩ := DoubleCoset.eq.1 h
  exact DoubleCoset.eq.2 ⟨h1, hh1, k, hle hk, e⟩

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the projection `π : X_B(U') → X_B(U)`, `[x]' ↦ [x]`
(meaningful for `U' ≤ U`, see `levelMap_mk`). -/
noncomputable def levelMap : XB U' → XB U :=
  fun c => DoubleCoset.mk (globalUnits a b) U (Quotient.out c)

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `π [x]' = [x]` for `U' ≤ U`. -/
theorem levelMap_mk {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) (x : (GL2TF.Quat.BHat a b)ˣ) :
    levelMap U' U (DoubleCoset.mk (globalUnits a b) U' x) = DoubleCoset.mk (globalUnits a b) U x := by
  obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U' x
  show DoubleCoset.mk (globalUnits a b) U (Quotient.out (DoubleCoset.mk (globalUnits a b) U' x)) = _
  rw [he, DoubleCoset.eq]
  exact ⟨h⁻¹, (globalUnits a b).inv_mem hh, k⁻¹, U.inv_mem (hle hk), by group⟩

variable (R : Type*) [CommRing R]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the pushforward `π_* : R[X_B(U')] → R[X_B(U)]`, `[x]' ↦ [x]`. -/
noncomputable def pushforward : ZX U' R →ₗ[R] ZX U R :=
  Finsupp.lmapDomain R R (levelMap U' U)

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `π_* (r [c']) = r [π c']`. -/
theorem pushforward_single (c' : XB U') (r : R) :
    pushforward U' U R (Finsupp.single c' r) = Finsupp.single (levelMap U' U c') r := by
  simp [pushforward]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the trace on lifts, `x ↦ ∑_{u ∈ U/U'} f([x u]')`. -/
noncomputable def traceRaw (f : ZXdual U' R) (x : (GL2TF.Quat.BHat a b)ˣ) : R :=
  ∑ᶠ q : ↥U ⧸ U'.subgroupOf U,
    f (DoubleCoset.mk (globalUnits a b) U' (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)))

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `traceRaw f` is invariant under right translation by `U`. -/
theorem traceRaw_mul_right (f : ZXdual U' R) (x : (GL2TF.Quat.BHat a b)ˣ) {u : (GL2TF.Quat.BHat a b)ˣ}
    (hu : u ∈ U) : traceRaw U' U R f (x * u) = traceRaw U' U R f x := by
  have hτ : ∀ (w : U), ∀ v ∈ U'.subgroupOf U,
      f (DoubleCoset.mk (globalUnits a b) U' (x * ((w * v : U) : (GL2TF.Quat.BHat a b)ˣ))) =
        f (DoubleCoset.mk (globalUnits a b) U' (x * ((w : U) : (GL2TF.Quat.BHat a b)ˣ))) := by
    intro w v hv
    congr 1
    rw [DoubleCoset.eq]
    refine ⟨1, one_mem _, ((v : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹,
      U'.inv_mem (Subgroup.mem_subgroupOf.mp hv), ?_⟩
    show x * ((w : U) : (GL2TF.Quat.BHat a b)ˣ) =
      1 * (x * (((w : U) : (GL2TF.Quat.BHat a b)ˣ) * ((v : U) : (GL2TF.Quat.BHat a b)ˣ))) *
        ((v : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹
    group
  have h := GL2TF.HeckeModule.coset_finsum_translate (U := U'.subgroupOf U)
    (τ := fun w : U =>
      f (DoubleCoset.mk (globalUnits a b) U' (x * ((w : U) : (GL2TF.Quat.BHat a b)ˣ)))) hτ ⟨u, hu⟩
  simp only [traceRaw]
  refine Eq.trans ?_ h
  refine finsum_congr fun q => ?_
  simp only [Subgroup.coe_mul, mul_assoc]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `traceRaw f` is invariant under left translation by `B^×`. -/
theorem traceRaw_left (f : ZXdual U' R) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    traceRaw U' U R f (iotaU a b γ * x) = traceRaw U' U R f x := by
  simp only [traceRaw]
  refine finsum_congr fun q => ?_
  congr 1
  rw [DoubleCoset.eq]
  exact ⟨(iotaU a b γ)⁻¹, (globalUnits a b).inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩), 1, one_mem _,
    by group⟩

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the trace `tr : R^{X_B(U')} → R^{X_B(U)}`,
`tr f ([x]) = ∑_{u ∈ U/U'} f([x u]')`, for `[U : U'] < ∞`. -/
noncomputable def trace (hrel : U'.relIndex U ≠ 0) : ZXdual U' R →ₗ[R] ZXdual U R where
  toFun f := fun c => traceRaw U' U R f (Quotient.out c)
  map_add' f f' := by
    have := finite_quotient_of_relIndex U' U hrel
    have := Fintype.ofFinite (↥U ⧸ U'.subgroupOf U)
    funext c
    simp only [traceRaw, finsum_eq_sum_of_fintype, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    have := finite_quotient_of_relIndex U' U hrel
    have := Fintype.ofFinite (↥U ⧸ U'.subgroupOf U)
    funext c
    simp only [traceRaw, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]

variable (hrel : U'.relIndex U ≠ 0)

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `tr f ([x]) = ∑_{u ∈ U/U'} f([x u]')` for every representative `x`. -/
theorem trace_apply_mk (f : ZXdual U' R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    trace U' U R hrel f (DoubleCoset.mk (globalUnits a b) U x) = traceRaw U' U R f x := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
  show traceRaw U' U R f (Quotient.out (DoubleCoset.mk (globalUnits a b) U x)) = _
  rw [he]
  exact (traceRaw_mul_right U' U R f _ hv).trans (traceRaw_left U' U R f k x)

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the number of `u ∈ U/U'` with `B^× x u U' = B^× y U'`. -/
noncomputable def traceCount (x y : (GL2TF.Quat.BHat a b)ˣ) : ℕ :=
  Nat.card {q : ↥U ⧸ U'.subgroupOf U //
    DoubleCoset.mk (globalUnits a b) U' (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)) =
      DoubleCoset.mk (globalUnits a b) U' y}

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `(tr 1_{c'})(c) = traceCount U' U c.out c'.out`. -/
theorem trace_single_apply (c : XB U) (c' : XB U') :
    trace U' U R hrel (Pi.single c' (1 : R)) c =
      (traceCount U' U (Quotient.out c) (Quotient.out c') : R) := by
  have := finite_quotient_of_relIndex U' U hrel
  show traceRaw U' U R (Pi.single c' (1 : R)) (Quotient.out c) = _
  simp only [traceRaw, traceCount]
  refine finsum_eq_natCard _ _ (Set.toFinite _) ?_ ?_
  · intro q hq
    rw [hq, DoubleCoset.out_eq', Pi.single_eq_same]
  · intro q hq
    exact Pi.single_eq_of_ne (fun h => hq (h.trans (DoubleCoset.out_eq' c').symm)) 1

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the map `γ ↦ x⁻¹ γ y U'` from `{γ ∈ B^× | x⁻¹ γ y ∈ U}` to the classes
counted by `traceCount U' U x y`. -/
theorem traceCountMap_aux (x y : (GL2TF.Quat.BHat a b)ˣ) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ)
    (hγ : x⁻¹ * iotaU a b γ * y ∈ U) :
    DoubleCoset.mk (globalUnits a b) U' (x * ((Quotient.out (QuotientGroup.mk (⟨x⁻¹ * iotaU a b γ * y, hγ⟩ : U) :
      ↥U ⧸ U'.subgroupOf U) : U) : (GL2TF.Quat.BHat a b)ˣ)) = DoubleCoset.mk (globalUnits a b) U' y := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨x⁻¹ * iotaU a b γ * y, hγ⟩ : U)
  rw [hw, DoubleCoset.eq]
  refine ⟨(iotaU a b γ)⁻¹, (globalUnits a b).inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩),
    (((w : U) : (GL2TF.Quat.BHat a b)ˣ))⁻¹, U'.inv_mem (Subgroup.mem_subgroupOf.mp w.2), ?_⟩
  show y = (iotaU a b γ)⁻¹ * (x * ((x⁻¹ * iotaU a b γ * y) * ((w : U) : (GL2TF.Quat.BHat a b)ˣ))) *
    ((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹
  group

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): the map underlying the orbit count for the trace. -/
noncomputable def traceCountMap (x y : (GL2TF.Quat.BHat a b)ˣ)
    (γ : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U}) :
    {q : ↥U ⧸ U'.subgroupOf U //
      DoubleCoset.mk (globalUnits a b) U' (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)) =
        DoubleCoset.mk (globalUnits a b) U' y} :=
  ⟨QuotientGroup.mk (⟨x⁻¹ * iotaU a b γ.1 * y, γ.2⟩ : U), traceCountMap_aux U' U x y γ.1 γ.2⟩

/-- `prop:s01-adjoint`(c) (`s01-adjoint`), orbit counting:
`|{γ ∈ B^× | x⁻¹ γ y ∈ U}| = traceCount U' U x y · |Γ_y(U')|` for `U' ≤ U`. -/
theorem natCard_traceSet {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) (x y : (GL2TF.Quat.BHat a b)ˣ) :
    Nat.card {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U} =
      traceCount U' U x y * Nat.card (Gam U' y) := by
  have hsurj : Function.Surjective (traceCountMap U' U x y) := by
    rintro ⟨q, hq⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, he⟩ := DoubleCoset.eq.1 hq
    change y = iotaU a b γ * (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)) * k at he
    have e1 : x⁻¹ * iotaU a b γ⁻¹ * y = ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ) * k := by
      rw [he, map_inv]
      group
    have hmem : x⁻¹ * iotaU a b γ⁻¹ * y ∈ U := by
      rw [e1]
      exact U.mul_mem (Quotient.out q).2 (hle hk)
    refine ⟨⟨γ⁻¹, hmem⟩, Subtype.ext ?_⟩
    show (QuotientGroup.mk (⟨x⁻¹ * iotaU a b γ⁻¹ * y, hmem⟩ : U) : ↥U ⧸ U'.subgroupOf U) = q
    have e2 : (⟨x⁻¹ * iotaU a b γ⁻¹ * y, hmem⟩ : U) = Quotient.out q * ⟨k, hle hk⟩ := Subtype.ext e1
    rw [e2, QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.mpr hk), QuotientGroup.out_eq']
  have hmul : ∀ γ δ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ, x⁻¹ * iotaU a b γ * y ∈ U →
      δ ∈ Gam U' y → x⁻¹ * iotaU a b (γ * δ) * y ∈ U := by
    intro γ δ hγ hδ
    have e : x⁻¹ * iotaU a b (γ * δ) * y = (x⁻¹ * iotaU a b γ * y) * (y⁻¹ * iotaU a b δ * y) := by
      rw [map_mul]
      group
    rw [e]
    exact U.mul_mem hγ (hle ((mem_Gam_iff U' y δ).1 hδ))
  have hfib : ∀ γ γ' : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U},
      traceCountMap U' U x y γ = traceCountMap U' U x y γ' ↔
        ((γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ))⁻¹ * (γ' : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ Gam U' y := by
    intro γ γ'
    refine Subtype.ext_iff.trans ?_
    show (QuotientGroup.mk (⟨x⁻¹ * iotaU a b γ.1 * y, γ.2⟩ : U) : ↥U ⧸ U'.subgroupOf U) =
        QuotientGroup.mk (⟨x⁻¹ * iotaU a b γ'.1 * y, γ'.2⟩ : U) ↔ γ.1⁻¹ * γ'.1 ∈ Gam U' y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_Gam_iff]
    show (x⁻¹ * iotaU a b γ.1 * y)⁻¹ * (x⁻¹ * iotaU a b γ'.1 * y) ∈ U' ↔ _
    have e : (x⁻¹ * iotaU a b γ.1 * y)⁻¹ * (x⁻¹ * iotaU a b γ'.1 * y) =
        y⁻¹ * iotaU a b (γ.1⁻¹ * γ'.1) * y := by
      rw [map_mul, map_inv]
      group
    rw [e]
  exact natCard_eq_mul_of_fibers (fun γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ => x⁻¹ * iotaU a b γ * y ∈ U)
    (Gam U' y) (traceCountMap U' U x y) hsurj hmul hfib

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): if `B^× x U = B^× y U` then `|{γ ∈ B^× | x⁻¹ γ y ∈ U}| = |Γ_y(U)|`. -/
theorem natCard_traceSet_of_mk {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y) :
    Nat.card {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U} = Nat.card (Gam U y) := by
  obtain ⟨h0, ⟨γ0, rfl⟩, k, hk, he⟩ := DoubleCoset.eq.1 h
  change y = iotaU a b γ0 * x * k at he
  have e0 : x⁻¹ * iotaU a b γ0⁻¹ * y = k := by
    rw [he, map_inv]
    group
  have hmem : x⁻¹ * iotaU a b γ0⁻¹ * y ∈ U := by
    rw [e0]
    exact hk
  have hsurj : Function.Surjective
      (fun _ : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U} => ()) :=
    fun _ => ⟨⟨γ0⁻¹, hmem⟩, rfl⟩
  have hmul : ∀ γ δ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ, x⁻¹ * iotaU a b γ * y ∈ U →
      δ ∈ Gam U y → x⁻¹ * iotaU a b (γ * δ) * y ∈ U := by
    intro γ δ hγ hδ
    have e : x⁻¹ * iotaU a b (γ * δ) * y = (x⁻¹ * iotaU a b γ * y) * (y⁻¹ * iotaU a b δ * y) := by
      rw [map_mul]
      group
    rw [e]
    exact U.mul_mem hγ ((mem_Gam_iff U y δ).1 hδ)
  have hfib : ∀ γ γ' : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U},
      (fun _ : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U} => ()) γ =
          (fun _ : {γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ // x⁻¹ * iotaU a b γ * y ∈ U} => ()) γ' ↔
        ((γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ))⁻¹ * (γ' : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ Gam U y := by
    intro γ γ'
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rw [mem_Gam_iff]
    have e : y⁻¹ * iotaU a b (γ.1⁻¹ * γ'.1) * y =
        (x⁻¹ * iotaU a b γ.1 * y)⁻¹ * (x⁻¹ * iotaU a b γ'.1 * y) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact U.mul_mem (U.inv_mem γ.2) γ'.2
  have := natCard_eq_mul_of_fibers (fun γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ => x⁻¹ * iotaU a b γ * y ∈ U)
    (Gam U y) _ hsurj hmul hfib
  rw [this, Nat.card_unique, one_mul]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `traceCount U' U x y = 0` unless `B^× x U = B^× y U`. -/
theorem traceCount_eq_zero {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x ≠ DoubleCoset.mk (globalUnits a b) U y) :
    traceCount U' U x y = 0 := by
  have hE : IsEmpty {q : ↥U ⧸ U'.subgroupOf U //
      DoubleCoset.mk (globalUnits a b) U' (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)) =
        DoubleCoset.mk (globalUnits a b) U' y} := by
    refine ⟨fun q => h ?_⟩
    refine Eq.trans ?_ (mk_eq_mk_of_le hle q.2)
    rw [DoubleCoset.eq]
    exact ⟨1, one_mem _, ((Quotient.out q.1 : U) : (GL2TF.Quat.BHat a b)ˣ), (Quotient.out q.1).2,
      by group⟩
  simp only [traceCount]
  exact @Nat.card_of_isEmpty _ hE

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): if `B^× x U = B^× y U`, then
`traceCount U' U x y · |Γ_y(U')| = |Γ_x(U)|`. -/
theorem traceCount_mul_card {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y) :
    traceCount U' U x y * Nat.card (Gam U' y) = Nat.card (Gam U y) := by
  rw [← natCard_traceSet hle x y, natCard_traceSet_of_mk h]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): `w` is constant on `U`-classes. -/
theorem wx_eq_of_mk {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y) : wx U x = wx U y := by
  rw [← wx_out U x, h, wx_out U y]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): if `B^× x U = B^× y U` and (`-1 ∈ U'` or `-1 ∉ U`), then
`traceCount U' U x y · w'_y = w_x`. -/
theorem traceCount_mul_wx {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    (hneg : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U' ∨ (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U)
    {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y) :
    traceCount U' U x y * wx U' y = wx U x := by
  have hc := traceCount_mul_card hle h
  rw [wx_eq_of_mk h]
  rcases hneg with h1 | h1
  · rw [← two_mul_wx h1 y, ← two_mul_wx (hle h1) y] at hc
    have h2 : 2 * (traceCount U' U x y * wx U' y) = 2 * wx U y := by
      calc 2 * (traceCount U' U x y * wx U' y) = traceCount U' U x y * (2 * wx U' y) := by ring
        _ = 2 * wx U y := hc
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  · have h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U' := fun hh => h1 (hle hh)
    rw [wx_eq_card h2 y, wx_eq_card h1 y]
    exact hc

/-- `prop:s01-adjoint`(c) (`s01-adjoint`), the factor-2 case: if `B^× x U = B^× y U` and `-1 ∈ U ∖ U'`, then
`traceCount U' U x y · w'_y = 2 w_x`. -/
theorem traceCount_mul_wx_two {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U)
    (h1 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) (h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U')
    {x y : (GL2TF.Quat.BHat a b)ˣ}
    (h : DoubleCoset.mk (globalUnits a b) U x = DoubleCoset.mk (globalUnits a b) U y) :
    traceCount U' U x y * wx U' y = 2 * wx U x := by
  have hc := traceCount_mul_card hle h
  rw [wx_eq_of_mk h, two_mul_wx h1 y, ← hc, wx_eq_card h2 y]

/-- `prop:s01-adjoint`(c) (`s01-adjoint`): for `U' ≤ U` with `[U : U'] < ∞`, assuming `-1 ∈ U'` or `-1 ∉ U`,
the norm maps intertwine pushforward and trace: `ν ∘ π_* = tr ∘ ν'`. -/
theorem normMap_pushforward (hle : U' ≤ U)
    (hneg : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U' ∨ (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U) (x : ZX U' R) :
    normMap U R (pushforward U' U R x) = trace U' U R hrel (normMap U' R x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single c' r =>
    funext c
    rw [normMap_apply, pushforward_single, normMap_single, map_smul, Pi.smul_apply, smul_eq_mul,
      trace_single_apply]
    by_cases h : DoubleCoset.mk (globalUnits a b) U (Quotient.out c) =
        DoubleCoset.mk (globalUnits a b) U (Quotient.out c')
    · have hc : levelMap U' U c' = c :=
        (show levelMap U' U c' = DoubleCoset.mk (globalUnits a b) U (Quotient.out c') from rfl).trans
          (h.symm.trans (DoubleCoset.out_eq' c))
      rw [hc, Finsupp.single_eq_same]
      have key : (traceCount U' U (Quotient.out c) (Quotient.out c') : R) * (wx U' (Quotient.out c') : R) =
          (wx U (Quotient.out c) : R) := by
        rw [← Nat.cast_mul, traceCount_mul_wx hle hneg h]
      linear_combination (-r) * key
    · have hc : levelMap U' U c' ≠ c := fun e =>
        h ((DoubleCoset.out_eq' c).trans (e.symm.trans rfl))
      rw [Finsupp.single_eq_of_ne' hc, traceCount_eq_zero hle h]
      simp

/-- `prop:s01-adjoint`(c) (`s01-adjoint`), the factor-2 case: if `-1 ∈ U ∖ U'` (e.g. `U = Ô^×`, `U' = U_1(N)`,
`N ≥ 3`), then `tr ∘ ν' = 2 · ν ∘ π_*`. -/
theorem normMap_pushforward_two (hle : U' ≤ U)
    (h1 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) (h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U') (x : ZX U' R) :
    trace U' U R hrel (normMap U' R x) = (2 : R) • normMap U R (pushforward U' U R x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, smul_add, h₁, h₂]
  | single c' r =>
    funext c
    rw [Pi.smul_apply, smul_eq_mul, normMap_apply, pushforward_single, normMap_single, map_smul,
      Pi.smul_apply, smul_eq_mul, trace_single_apply]
    by_cases h : DoubleCoset.mk (globalUnits a b) U (Quotient.out c) =
        DoubleCoset.mk (globalUnits a b) U (Quotient.out c')
    · have hc : levelMap U' U c' = c :=
        (show levelMap U' U c' = DoubleCoset.mk (globalUnits a b) U (Quotient.out c') from rfl).trans
          (h.symm.trans (DoubleCoset.out_eq' c))
      rw [hc, Finsupp.single_eq_same]
      have key : (traceCount U' U (Quotient.out c) (Quotient.out c') : R) * (wx U' (Quotient.out c') : R) =
          2 * (wx U (Quotient.out c) : R) := by
        rw [← Nat.cast_mul, traceCount_mul_wx_two hle h1 h2 h, Nat.cast_mul, Nat.cast_two]
      linear_combination r * key
    · have hc : levelMap U' U c' ≠ c := fun e =>
        h ((DoubleCoset.out_eq' c).trans (e.symm.trans rfl))
      rw [Finsupp.single_eq_of_ne' hc, traceCount_eq_zero hle h]
      simp

end Pushforward

end Langlandscape.Brandt
