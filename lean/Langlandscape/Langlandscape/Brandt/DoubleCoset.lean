/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Module
import AlgJL.Common.HeckeModule

/-!
# Double-coset operators on `R^X` and `R[X]` (S01-L8a)

`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-hecke` (trivial coefficients).

For `g ∈ B̂^×` with `[U : U ∩ g U g⁻¹] < ∞` write `U g U = ⊔ᵢ gᵢ U`.

* `dcSet U g` : the double coset `U g U` as a set; `conjSub U g` : the subgroup `g U g⁻¹`.
* `heckeT U R g hfin : R^X →ₗ[R] R^X`, `(T_g f)(x) = ∑ᵢ f(x gᵢ)`; it is the import's
  `GL2TF.HeckeModule.heckeAct` of the indicator function of `U g U` on the lift `x ↦ f(B^× x U)`.
* `heckeT_apply_reps` : the value is computed by any system of coset representatives.
* `heckeTHom U R g hfin : R[X] →ₗ[R] R[X]` (for finite `X`) : the transpose, `[x] ↦ ∑ᵢ [x gᵢ]`;
  `heckeTHom_transpose`.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

variable {a b : ℤ}

section DoubleCoset

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-hecke` (`s01-hecke`): the double coset `U g U` as a subset of `B̂^×`. -/
def dcSet : Set (GL2TF.Quat.BHat a b)ˣ :=
  {y | ∃ u ∈ U, ∃ v ∈ U, y = u * g * v}

/-- `def:s01-hecke` (`s01-hecke`): membership in `U g U`. -/
theorem mem_dcSet {y : (GL2TF.Quat.BHat a b)ˣ} :
    y ∈ dcSet U g ↔ ∃ u ∈ U, ∃ v ∈ U, y = u * g * v := Iff.rfl

/-- `def:s01-hecke` (`s01-hecke`): the conjugate subgroup `g U g⁻¹ = {x | g⁻¹ x g ∈ U}`. -/
def conjSub : Subgroup (GL2TF.Quat.BHat a b)ˣ where
  carrier := {x | g⁻¹ * x * g ∈ U}
  mul_mem' := by
    intro x y hx hy
    show g⁻¹ * (x * y) * g ∈ U
    have e : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
    rw [e]
    exact U.mul_mem hx hy
  one_mem' := by
    show g⁻¹ * 1 * g ∈ U
    rw [mul_one, inv_mul_cancel]
    exact U.one_mem
  inv_mem' := by
    intro x hx
    show g⁻¹ * x⁻¹ * g ∈ U
    have e : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
    rw [e]
    exact U.inv_mem hx

/-- `def:s01-hecke` (`s01-hecke`): `x ∈ g U g⁻¹ ↔ g⁻¹ x g ∈ U`. -/
theorem mem_conjSub {x : (GL2TF.Quat.BHat a b)ˣ} : x ∈ conjSub U g ↔ g⁻¹ * x * g ∈ U := Iff.rfl

/-- `def:s01-hecke` (`s01-hecke`): `U g U` is stable under left multiplication by `U`. -/
theorem mul_mem_dcSet_iff_left {u x : (GL2TF.Quat.BHat a b)ˣ} (hu : u ∈ U) :
    u * x ∈ dcSet U g ↔ x ∈ dcSet U g := by
  constructor
  · intro h
    obtain ⟨u1, hu1, v, hv, e⟩ := (mem_dcSet U g).1 h
    refine (mem_dcSet U g).2 ⟨u⁻¹ * u1, U.mul_mem (U.inv_mem hu) hu1, v, hv, ?_⟩
    calc x = u⁻¹ * (u * x) := by group
      _ = u⁻¹ * (u1 * g * v) := by rw [e]
      _ = u⁻¹ * u1 * g * v := by group
  · intro h
    obtain ⟨u1, hu1, v, hv, e⟩ := (mem_dcSet U g).1 h
    refine (mem_dcSet U g).2 ⟨u * u1, U.mul_mem hu hu1, v, hv, ?_⟩
    rw [e]
    group

/-- `def:s01-hecke` (`s01-hecke`): `U g U` is stable under right multiplication by `U`. -/
theorem mul_mem_dcSet_iff_right {u x : (GL2TF.Quat.BHat a b)ˣ} (hu : u ∈ U) :
    x * u ∈ dcSet U g ↔ x ∈ dcSet U g := by
  constructor
  · intro h
    obtain ⟨u1, hu1, v, hv, e⟩ := (mem_dcSet U g).1 h
    refine (mem_dcSet U g).2 ⟨u1, hu1, v * u⁻¹, U.mul_mem hv (U.inv_mem hu), ?_⟩
    calc x = x * u * u⁻¹ := by group
      _ = u1 * g * v * u⁻¹ := by rw [e]
      _ = u1 * g * (v * u⁻¹) := by group
  · intro h
    obtain ⟨u1, hu1, v, hv, e⟩ := (mem_dcSet U g).1 h
    refine (mem_dcSet U g).2 ⟨u1, hu1, v * u, U.mul_mem hv hu, ?_⟩
    rw [e]
    group

/-- `def:s01-hecke` (`s01-hecke`): the left cosets `yU` met by `U g U` are finitely many
when `[U : U ∩ g U g⁻¹] < ∞`. -/
theorem finite_cosets_dcSet (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    ((QuotientGroup.mk '' (dcSet U g) : Set ((GL2TF.Quat.BHat a b)ˣ ⧸ U))).Finite := by
  classical
  set W := (U ⊓ conjSub U g).subgroupOf U with hW
  have : W.FiniteIndex := ⟨hfin⟩
  have hXfin : Finite (↥U ⧸ W) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range
    (fun q : ↥U ⧸ W => (QuotientGroup.mk (((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ) * g) :
      (GL2TF.Quat.BHat a b)ˣ ⧸ U))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U g).1 hy
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W (⟨u, hu⟩ : U)
  refine ⟨QuotientGroup.mk (⟨u, hu⟩ : U), ?_⟩
  show (QuotientGroup.mk
      ((((QuotientGroup.mk (⟨u, hu⟩ : U) : ↥U ⧸ W).out : U) : (GL2TF.Quat.BHat a b)ˣ) * g) :
      (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk (u * g * v)
  rw [hw, QuotientGroup.eq]
  have hwc : g⁻¹ * ((w : U) : (GL2TF.Quat.BHat a b)ˣ) * g ∈ U :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp w.2)).2
  have e : ((((⟨u, hu⟩ : U) * (w : U) : U) : (GL2TF.Quat.BHat a b)ˣ) * g)⁻¹ * (u * g * v) =
      (g⁻¹ * ((w : U) : (GL2TF.Quat.BHat a b)ˣ) * g)⁻¹ * v := by
    have h1 : ((((⟨u, hu⟩ : U) * (w : U) : U) : (GL2TF.Quat.BHat a b)ˣ)) =
        u * ((w : U) : (GL2TF.Quat.BHat a b)ˣ) := rfl
    rw [h1]
    group
  have hmem := U.mul_mem (U.inv_mem hwc) hv
  rw [← e] at hmem
  exact hmem

variable (R : Type*) [CommRing R]

/-- `def:s01-hecke` (`s01-hecke`): the indicator function of `U g U`, with values in `R`. -/
noncomputable def heckeCoeff : (GL2TF.Quat.BHat a b)ˣ → R :=
  (dcSet U g).indicator (fun _ => (1 : R))

/-- `def:s01-hecke` (`s01-hecke`): the indicator is `1` on `U g U`. -/
theorem heckeCoeff_of_mem {y : (GL2TF.Quat.BHat a b)ˣ} (h : y ∈ dcSet U g) :
    heckeCoeff U g R y = 1 :=
  Set.indicator_of_mem h (fun _ => (1 : R))

/-- `def:s01-hecke` (`s01-hecke`): the indicator is `0` off `U g U`. -/
theorem heckeCoeff_of_notMem {y : (GL2TF.Quat.BHat a b)ˣ} (h : y ∉ dcSet U g) :
    heckeCoeff U g R y = 0 :=
  Set.indicator_of_notMem h (fun _ => (1 : R))

/-- `def:s01-hecke` (`s01-hecke`): the indicator of `U g U` is a Hecke function for `U` (bi-`U`-invariant
with finite support modulo `U`) when `[U : U ∩ g U g⁻¹] < ∞`. -/
noncomputable def heckeFun (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    HeckePair.HeckeAlgebra U R :=
  ⟨heckeCoeff U g R, HeckePair.mem_heckeSubmodule_iff.2
    ⟨fun u hu x => by
        by_cases hx : x ∈ dcSet U g
        · rw [heckeCoeff_of_mem U g R ((mul_mem_dcSet_iff_left U g hu).2 hx), heckeCoeff_of_mem U g R hx]
        · rw [heckeCoeff_of_notMem U g R (fun h => hx ((mul_mem_dcSet_iff_left U g hu).1 h)),
            heckeCoeff_of_notMem U g R hx],
      fun u hu x => by
        by_cases hx : x ∈ dcSet U g
        · rw [heckeCoeff_of_mem U g R ((mul_mem_dcSet_iff_right U g hu).2 hx), heckeCoeff_of_mem U g R hx]
        · rw [heckeCoeff_of_notMem U g R (fun h => hx ((mul_mem_dcSet_iff_right U g hu).1 h)),
            heckeCoeff_of_notMem U g R hx],
      (finite_cosets_dcSet U g hfin).subset (Set.image_mono (by
        intro y hy
        by_contra hn
        exact (Function.mem_support.mp hy) (heckeCoeff_of_notMem U g R hn)))⟩⟩

/-- `def:s01-hecke` (`s01-hecke`): the underlying function of `heckeFun` is `heckeCoeff`. -/
theorem coe_heckeFun (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) : (GL2TF.Quat.BHat a b)ˣ → R) =
      heckeCoeff U g R := rfl

/-- `def:s01-hecke` (`s01-hecke`): the lift `x ↦ f(B^× x U)` of `f : R^X` to a function on `B̂^×`. -/
noncomputable def liftFun (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) : R :=
  f (DoubleCoset.mk (globalUnits a b) U x)

omit [CommRing R] in
/-- `def:s01-hecke` (`s01-hecke`): lifts are invariant under right translation by `U`. -/
theorem liftFun_mul_right (f : ZXdual U R) (y : (GL2TF.Quat.BHat a b)ˣ) {u : (GL2TF.Quat.BHat a b)ˣ}
    (hu : u ∈ U) : liftFun U R f (y * u) = liftFun U R f y := by
  show f (DoubleCoset.mk (globalUnits a b) U (y * u)) = f (DoubleCoset.mk (globalUnits a b) U y)
  congr 1
  rw [DoubleCoset.eq]
  exact ⟨1, (globalUnits a b).one_mem, u⁻¹, U.inv_mem hu, by group⟩

omit [CommRing R] in
/-- `def:s01-hecke` (`s01-hecke`): lifts are invariant under left translation by `B^×`. -/
theorem liftFun_left (f : ZXdual U R) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (y : (GL2TF.Quat.BHat a b)ˣ) :
    liftFun U R f (iotaU a b γ * y) = liftFun U R f y := by
  show f (DoubleCoset.mk (globalUnits a b) U (iotaU a b γ * y)) =
    f (DoubleCoset.mk (globalUnits a b) U y)
  congr 1
  rw [DoubleCoset.eq]
  exact ⟨(iotaU a b γ)⁻¹, (globalUnits a b).inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩), 1, U.one_mem,
    by group⟩

variable (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)

/-- `def:s01-hecke` (`s01-hecke`): the operator on functions `B̂^× → R` through the import's `heckeAct`:
`(T_g F)(x) = ∑_{yU ⊆ U g U} F(x y)`. -/
noncomputable def heckeRaw (f : ZXdual U R) : (GL2TF.Quat.BHat a b)ˣ → R :=
  GL2TF.HeckeModule.heckeAct (U := U) ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) :
    (GL2TF.Quat.BHat a b)ˣ → R) (liftFun U R f)

/-- Finiteness of the support of the terms of `heckeRaw` (`def:s01-hecke`). -/
theorem heckeRaw_support_finite (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    (Function.support fun c : (GL2TF.Quat.BHat a b)ˣ ⧸ U =>
      ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) : (GL2TF.Quat.BHat a b)ˣ → R) (Quotient.out c) •
        liftFun U R f (x * Quotient.out c)).Finite :=
  GL2TF.HeckeModule.heckeAct_support_finite (U := U) (heckeFun U g R hfin) (liftFun U R f) x

/-- `def:s01-hecke` (`s01-hecke`): `heckeRaw f` is invariant under right translation by `U`. -/
theorem heckeRaw_mul_right (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) {u : (GL2TF.Quat.BHat a b)ˣ}
    (hu : u ∈ U) : heckeRaw U g R hfin f (x * u) = heckeRaw U g R hfin f x :=
  GL2TF.HeckeModule.heckeAct_mul_right (U := U) (heckeFun U g R hfin) (f := liftFun U R f)
    (fun y _ hv => liftFun_mul_right U R f y hv) x u hu

/-- `def:s01-hecke` (`s01-hecke`): `heckeRaw f` is invariant under left translation by `B^×`. -/
theorem heckeRaw_left (f : ZXdual U R) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeRaw U g R hfin f (iotaU a b γ * x) = heckeRaw U g R hfin f x := by
  simp only [heckeRaw, GL2TF.HeckeModule.heckeAct]
  refine finsum_congr fun c => ?_
  rw [mul_assoc, liftFun_left U R f γ]

/-- `def:s01-hecke` (`s01-hecke`): additivity of `heckeRaw`. -/
theorem heckeRaw_add (f f' : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeRaw U g R hfin (f + f') x = heckeRaw U g R hfin f x + heckeRaw U g R hfin f' x := by
  have h := finsum_add_distrib (heckeRaw_support_finite U g R hfin f x)
    (heckeRaw_support_finite U g R hfin f' x)
  simp only [heckeRaw, GL2TF.HeckeModule.heckeAct]
  rw [← h]
  refine finsum_congr fun c => ?_
  simp only [liftFun, Pi.add_apply, smul_add]

/-- `def:s01-hecke` (`s01-hecke`): `R`-homogeneity of `heckeRaw`. -/
theorem heckeRaw_smul (r : R) (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeRaw U g R hfin (r • f) x = r • heckeRaw U g R hfin f x := by
  have h := smul_finsum' r (heckeRaw_support_finite U g R hfin f x)
  simp only [heckeRaw, GL2TF.HeckeModule.heckeAct]
  rw [h]
  refine finsum_congr fun c => ?_
  simp only [liftFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- `def:s01-hecke` (`s01-hecke`): `heckeRaw f` descended to `X = B^× \ B̂^× / U`, via `c ↦ heckeRaw f (c.out)`. -/
noncomputable def heckeTFun (f : ZXdual U R) : ZXdual U R :=
  fun c => heckeRaw U g R hfin f (Quotient.out c)

/-- `def:s01-hecke` (`s01-hecke`): `heckeTFun f` at the class of `x` is `heckeRaw f x`. -/
theorem heckeTFun_mk (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeTFun U g R hfin f (DoubleCoset.mk (globalUnits a b) U x) = heckeRaw U g R hfin f x := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
  show heckeRaw U g R hfin f (Quotient.out (DoubleCoset.mk (globalUnits a b) U x)) = _
  rw [he]
  exact (heckeRaw_mul_right U g R hfin f _ hv).trans (heckeRaw_left U g R hfin f k x)

/-- `def:s01-hecke` (`s01-hecke`): the Hecke operator `T_g = [U g U]` on `R^X`,
`(T_g f)(x) = ∑ᵢ f(x gᵢ)` for `U g U = ⊔ᵢ gᵢ U`; it needs `[U : U ∩ g U g⁻¹] < ∞`. -/
noncomputable def heckeT : ZXdual U R →ₗ[R] ZXdual U R where
  toFun := heckeTFun U g R hfin
  map_add' f f' := by
    funext c
    exact heckeRaw_add U g R hfin f f' _
  map_smul' r f := by
    funext c
    exact heckeRaw_smul U g R hfin r f _

/-- `def:s01-hecke` (`s01-hecke`): `heckeT f` at the class of `x` is `heckeRaw f x`
(the import's `heckeAct` of the indicator of `U g U` on the lift of `f`). -/
theorem heckeT_apply_mk (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeT U g R hfin f (DoubleCoset.mk (globalUnits a b) U x) =
      GL2TF.HeckeModule.heckeAct (U := U) ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) :
        (GL2TF.Quat.BHat a b)ˣ → R) (liftFun U R f) x :=
  heckeTFun_mk U g R hfin f x

/-- `def:s01-hecke` (`s01-hecke`): `(T_g f)(x) = ∑_{s ∈ S} f(x s)` for any set `S` of representatives of the
left cosets `yU ⊆ U g U` (`S ⊆ U g U`, meeting every coset exactly once): independent of the choice. -/
theorem heckeT_apply_reps (S : Finset (GL2TF.Quat.BHat a b)ˣ)
    (hS : ∀ s ∈ S, s ∈ dcSet U g)
    (hcov : ∀ y ∈ dcSet U g, ∃ s ∈ S,
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s)
    (hinj : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S)
    (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeT U g R hfin f (DoubleCoset.mk (globalUnits a b) U x) =
      ∑ s ∈ S, f (DoubleCoset.mk (globalUnits a b) U (x * s)) := by
  rw [heckeT_apply_mk]
  simp only [GL2TF.HeckeModule.heckeAct]
  have hsupp : Function.support (fun c : (GL2TF.Quat.BHat a b)ˣ ⧸ U =>
      ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) : (GL2TF.Quat.BHat a b)ˣ → R) (Quotient.out c) •
        liftFun U R f (x * Quotient.out c)) ⊆
      ↑(S.image (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U)) := by
    intro c hc
    have hc' : ((heckeFun U g R hfin : HeckePair.HeckeAlgebra U R) : (GL2TF.Quat.BHat a b)ˣ → R)
        (Quotient.out c) • liftFun U R f (x * Quotient.out c) ≠ 0 := hc
    have hmem : (Quotient.out c : (GL2TF.Quat.BHat a b)ˣ) ∈ dcSet U g := by
      by_contra hn
      apply hc'
      rw [coe_heckeFun, heckeCoeff_of_notMem U g R hn, zero_smul]
    obtain ⟨s, hs, hsc⟩ := hcov _ hmem
    rw [QuotientGroup.out_eq'] at hsc
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨s, hs, hsc.symm⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U s
  rw [hh, coe_heckeFun, heckeCoeff_of_mem U g R
    ((mul_mem_dcSet_iff_right U g h.2).2 (hS s hs)), one_smul, ← mul_assoc]
  exact liftFun_mul_right U R f (x * s) h.2

end DoubleCoset

section Transpose

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)

/-- `def:s01-hecke` (`s01-hecke`): the transpose `T_g^t` of `T_g` on `R[X]` (for finite `X`),
`[c] ↦ ∑_{c'} (T_g 1_{c'})(c) [c']`, i.e. `[x] ↦ ∑ᵢ [x gᵢ]`. -/
noncomputable def heckeTHom [Finite (XB U)] : ZX U R →ₗ[R] ZX U R :=
  Finsupp.lift (ZX U R) R (XB U)
    (fun c => Finsupp.equivFunOnFinite.symm (fun c' => heckeT U g R hfin (Pi.single c' (1 : R)) c))

/-- `def:s01-hecke` (`s01-hecke`): `T_g^t [c] = ∑_{c'} (T_g 1_{c'})(c) [c']`, coefficientwise. -/
theorem heckeTHom_single_apply [Finite (XB U)] (c c' : XB U) (r : R) :
    heckeTHom U g R hfin (Finsupp.single c r) c' = r * heckeT U g R hfin (Pi.single c' (1 : R)) c := by
  simp only [heckeTHom, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul]
  simp [Finsupp.smul_apply]

/-- `def:s01-hecke` (`s01-hecke`): the transpose identity `⟨T_g^t a, f⟩ = ⟨a, T_g f⟩` for the evaluation
pairing `R[X] × R^X → R`, for finite `X`. -/
theorem heckeTHom_transpose [Finite (XB U)] (x : ZX U R) (f : ZXdual U R) :
    evalPairing U R (heckeTHom U g R hfin x) f = evalPairing U R x (heckeT U g R hfin f) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single c r =>
    have key : (evalPairing U R (heckeTHom U g R hfin (Finsupp.single c (1 : R)))) =
        (LinearMap.proj c : ZXdual U R →ₗ[R] R) ∘ₗ heckeT U g R hfin := by
      apply LinearMap.pi_ext
      intro c' s
      have hs : (Pi.single c' s : ZXdual U R) = s • (Pi.single c' (1 : R) : ZXdual U R) := by
        funext j
        by_cases h : j = c'
        · subst h
          simp
        · simp [h]
      simp only [hs, map_smul, LinearMap.comp_apply]
      rw [evalPairing_pi_single, heckeTHom_single_apply]
      simp
    have hsing : (Finsupp.single c r : ZX U R) = r • Finsupp.single c (1 : R) := by simp
    simp only [hsing, map_smul, LinearMap.smul_apply]
    rw [key]
    simp [evalPairing_single]

end Transpose

end Langlandscape.Brandt
