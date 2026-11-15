/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Weights

/-!
# Brandt modules, pairings and the norm map (S01-L7)

`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-brandt`, `def:s01-pairing`.

* `brandtModule U R V ρ` : functions `f : B̂^× → V` with `f(γ x u) = (ρ u)⁻¹ (f x)` (seed convention).
* `ZX U R = R[X]` (finitely supported, pushforward side), `ZXdual U R = R^X` (functions, pullback side).
* `evalPairing` : the naive evaluation `R[X] × R^X → R`, perfect for finite `X`.
* `brandtModuleTrivEquiv` : `brandtModule U R R 1 ≃ₗ R^X`.
* `brandtPairing` : `⟨[c],[c']⟩ = w_c δ_{cc'}`; `normMap` : `[c] ↦ w_c 1_c`; bijective when all `w_c` are units.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

variable {a b : ℤ}

section Module

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (V : Type*) [AddCommGroup V] [Module R V]

/-- `def:s01-brandt` (`s01-brandt`): the Brandt module
`{f : B̂^× → V | f(γ x u) = (ρ u)⁻¹ (f x)}` for `γ ∈ B^×`, `u ∈ U`. -/
def brandtModule (ρ : U →* (V ≃ₗ[R] V)) : Submodule R ((GL2TF.Quat.BHat a b)ˣ → V) where
  carrier := {f | ∀ (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) (u : U),
    f (iotaU a b γ * x * u) = ((ρ u)⁻¹ : V ≃ₗ[R] V) (f x)}
  add_mem' := by
    intro f g hf hg γ x u
    simp [hf γ x u, hg γ x u]
  zero_mem' := by
    intro γ x u
    simp
  smul_mem' := by
    intro r f hf γ x u
    simp [hf γ x u]

/-- `def:s01-brandt` (`s01-brandt`): membership in the Brandt module. -/
theorem mem_brandtModule {ρ : U →* (V ≃ₗ[R] V)} {f : (GL2TF.Quat.BHat a b)ˣ → V} :
    f ∈ brandtModule U R V ρ ↔ ∀ (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) (u : U),
      f (iotaU a b γ * x * u) = ((ρ u)⁻¹ : V ≃ₗ[R] V) (f x) := Iff.rfl

end Module

section Classes

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `def:s01-brandt` (`s01-brandt`): `R[X]`, the free module on `X = X_B(U)` (pushforward side). -/
abbrev ZX : Type _ := XB U →₀ R

/-- `def:s01-brandt` (`s01-brandt`): `R^X`, functions on `X = X_B(U)` (pullback side). -/
abbrev ZXdual : Type _ := XB U → R

/-- `def:s01-brandt` (`s01-brandt`): naive evaluation `R[X] × R^X → R`, `([c], f) ↦ f c`. -/
noncomputable def evalPairing : ZX U R →ₗ[R] ZXdual U R →ₗ[R] R :=
  Finsupp.lift (ZXdual U R →ₗ[R] R) R (XB U) (fun c => LinearMap.proj c)

/-- `def:s01-brandt` (`s01-brandt`): `evalPairing (r [c]) f = r f(c)`. -/
theorem evalPairing_single (c : XB U) (r : R) (f : ZXdual U R) :
    evalPairing U R (Finsupp.single c r) f = r * f c := by
  simp [evalPairing]

/-- `def:s01-brandt` (`s01-brandt`): `evalPairing a f = ∑ᶠ c, a c · f c` for finite `X`. -/
theorem evalPairing_apply [Finite (XB U)] (x : ZX U R) (f : ZXdual U R) :
    evalPairing U R x f = ∑ᶠ c, x c * f c := by
  classical
  have : Fintype (XB U) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp [hg, hh, add_mul, Finset.sum_add_distrib]
  | single c r =>
    rw [evalPairing_single]
    simp [Finsupp.single_apply]

/-- `def:s01-brandt` (`s01-brandt`): evaluating against the indicator function `1_c` reads off the coefficient. -/
theorem evalPairing_pi_single (x : ZX U R) (c : XB U) :
    evalPairing U R x (Pi.single c (1 : R)) = x c := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp [hg, hh]
  | single c' r =>
    rw [evalPairing_single]
    by_cases h : c' = c
    · subst h; simp
    · simp [h, Ne.symm h]

/-- `def:s01-pairing`/`def:s01-brandt` (`s01-brandt`): the evaluation pairing is perfect when `X` is finite:
both `R^X → Hom(R[X], R)` and `R[X] → Hom(R^X, R)` are bijective. -/
theorem evalPairing_perfect [Finite (XB U)] :
    Function.Bijective (evalPairing U R).flip ∧ Function.Bijective (evalPairing U R) := by
  classical
  have : Fintype (XB U) := Fintype.ofFinite _
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro f g h
    funext c
    have := congrArg (fun φ => φ (Finsupp.single c (1 : R))) h
    simpa [evalPairing_single] using this
  · intro φ
    refine ⟨fun c => φ (Finsupp.single c 1), ?_⟩
    apply Finsupp.lhom_ext
    intro c r
    simp only [LinearMap.flip_apply, evalPairing_single]
    have : Finsupp.single c r = r • Finsupp.single c (1 : R) := by simp
    rw [this, map_smul]
    simp
  · intro x y h
    ext c
    have := congrArg (fun φ => φ (Pi.single c (1 : R))) h
    simpa [evalPairing_pi_single] using this
  · intro ψ
    refine ⟨∑ c, Finsupp.single c (ψ (Pi.single c 1)), ?_⟩
    apply LinearMap.ext
    intro f
    rw [map_sum, LinearMap.sum_apply]
    simp only [evalPairing_single]
    conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ ψ f]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : (fun j => if c = j then (1 : R) else 0) = Pi.single c 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    simp [e, mul_comm]

/-- `def:s01-brandt` (`s01-brandt`): for trivial coefficients `V = R`, `ρ = 1`, the Brandt module is the space
of functions on `X_B(U)`, via `f ↦ (f c.out)_c`. -/
noncomputable def brandtModuleTrivEquiv :
    brandtModule U R R (1 : U →* (R ≃ₗ[R] R)) ≃ₗ[R] ZXdual U R where
  toFun f := fun c => f.1 (Quotient.out c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun x => g (DoubleCoset.mk (globalUnits a b) U x), by
    intro γ x u
    have : DoubleCoset.mk (globalUnits a b) U (iotaU a b γ * x * u) = DoubleCoset.mk (globalUnits a b) U x := by
      rw [DoubleCoset.eq]
      exact ⟨(iotaU a b γ)⁻¹, (globalUnits a b).inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩),
        (u : (GL2TF.Quat.BHat a b)ˣ)⁻¹, U.inv_mem u.2, by group⟩
    simp [this]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
    show f.1 (Quotient.out (DoubleCoset.mk (globalUnits a b) U x)) = f.1 x
    rw [he]
    have h2 := f.2 k x ⟨v, hv⟩
    simp at h2
    exact h2
  right_inv g := by
    funext c
    show g (DoubleCoset.mk (globalUnits a b) U (Quotient.out c)) = g c
    congr 1
    exact Quotient.out_eq c

/-- `def:s01-brandt` (`s01-brandt`): `brandtModuleTrivEquiv f c = f (c.out)`. -/
theorem brandtModuleTrivEquiv_apply (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R))) (c : XB U) :
    brandtModuleTrivEquiv U R f c = f.1 (Quotient.out c) := rfl

end Classes

section Pairing

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `def:s01-pairing` (`s01-pairing`): the Brandt pairing on `R[X]`, `⟨[c],[c']⟩ = w_c δ_{cc'}`. -/
noncomputable def brandtPairing : ZX U R →ₗ[R] ZX U R →ₗ[R] R :=
  Finsupp.lift (ZX U R →ₗ[R] R) R (XB U)
    (fun c => (wx U (Quotient.out c) : R) • Finsupp.lapply c)

/-- `def:s01-pairing` (`s01-pairing`): `⟨r[c], s[c']⟩ = r w_c s δ_{cc'}`. -/
theorem brandtPairing_single_single (c c' : XB U) (r s : R) :
    brandtPairing U R (Finsupp.single c r) (Finsupp.single c' s) =
      if c = c' then r * (wx U (Quotient.out c) : R) * s else 0 := by
  classical
  simp only [brandtPairing, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul]
  by_cases h : c = c'
  · subst h; simp; ring
  · simp [h]

/-- `def:s01-pairing` (`s01-pairing`): the norm map `ν : R[X] → R^X`, `[c] ↦ w_c 1_c`. -/
noncomputable def normMap : ZX U R →ₗ[R] ZXdual U R :=
  Finsupp.lift (ZXdual U R) R (XB U) (fun c => (wx U (Quotient.out c) : R) • Pi.single c (1 : R))

/-- `def:s01-pairing` (`s01-pairing`): `ν(r[c]) = r w_c 1_c`. -/
theorem normMap_single (c : XB U) (r : R) :
    normMap U R (Finsupp.single c r) = (r * (wx U (Quotient.out c) : R)) • Pi.single c (1 : R) := by
  simp [normMap, smul_smul]

/-- `def:s01-pairing` (`s01-pairing`): `(ν a)(c) = w_c · a(c)`. -/
theorem normMap_apply (x : ZX U R) (c : XB U) :
    normMap U R x c = (wx U (Quotient.out c) : R) * x c := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single c' r =>
    rw [normMap_single]
    by_cases h : c' = c
    · subst h; simp [mul_comm]
    · simp [Ne.symm h]

/-- `def:s01-pairing` (`s01-pairing`): `ν a = ⟨a, ·⟩`, i.e. `⟨a, b⟩ = ev(b, ν a)`. -/
theorem brandtPairing_eq_evalPairing_normMap [Finite (XB U)] (x y : ZX U R) :
    brandtPairing U R x y = evalPairing U R y (normMap U R x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single c r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [hf, hg]
    | single c' s =>
      rw [brandtPairing_single_single, evalPairing_single, normMap_apply]
      by_cases h : c = c'
      · subst h; simp; ring
      · simp [h]

/-- `def:s01-pairing` (`s01-pairing`): `ν` is bijective over `R` when every `w_c` is a unit in `R`
(e.g. `R = ℤ_p`, `p ≥ 5`; see `lem:s01-stab`(c)), for finite `X`. -/
theorem normMap_bijective [Finite (XB U)] (h : ∀ c : XB U, IsUnit (wx U (Quotient.out c) : R)) :
    Function.Bijective (normMap U R) := by
  classical
  constructor
  · intro x y hxy
    ext c
    have := congrFun hxy c
    rw [normMap_apply, normMap_apply] at this
    exact (h c).mul_right_injective this
  · intro g
    have : Fintype (XB U) := Fintype.ofFinite _
    refine ⟨Finsupp.equivFunOnFinite.symm (fun c => ((h c).unit⁻¹ : Rˣ) * g c), ?_⟩
    funext c
    rw [normMap_apply]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← mul_assoc]
    have := (h c).unit.mul_inv
    simp only [IsUnit.unit_spec] at this
    rw [this, one_mul]

end Pairing

end Langlandscape.Brandt
