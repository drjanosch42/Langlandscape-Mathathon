/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.GroupRing
public import Langlandscape.Ordinary.Projector
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Abstract control (S04-L8)

Abstract part of Hida's lemma `lem:s04-hida`(c),(d) (`mathematics/chapters/s04/control.tex`).

* **Permutation modules.** For a group `H` acting on a set `Y` and a map `π : Y → Z` whose fibres
  are exactly the `H`-orbits, `π_*` induces `R[Y]_H ≃ R[Z]` (`coinvEquivOfFibres`); in particular
  `R[Y]_H ≃ R[Y⧸H]` (`coinvEquivOrbits`). This is the coinvariant form of
  `R[Y] ⊗_{R[G]} R[G⧸H] ≃ R[Y⧸H]` (`R[Y] ⊗_{R[G]} R[G⧸H] = R[Y] ⊗_{R[H]} R = R[Y]_H`); freeness
  of the action is not needed for this step (it enters only `prop:s04-freeA`, S04-L7).
* **Complementary pairs along surjections.** If `f : M → N` is surjective, `A ⊔ B = ⊤`,
  `Disjoint A' B'`, `f A ≤ A'`, `f B ≤ B'`, then `f A = A'`, `f B = B'`, `f` commutes with the
  projections, and if moreover `ker f ≤ B` then `f : A ≃ A'`.
* **Ordinary parts.** Specialisation to `ordPart`/`nilPart` (D-e, S04-L1): surjective
  `T`-equivariant maps carry ordinary parts onto ordinary parts (`ordProj` commutes with them by
  S04-L1 `ordProj_map`); if `T (ker f) = 0` then
  `f : ordPart T ≃ ordPart T'` (`lem:s04-hida`(c), first claim); the ordinary projector commutes
  with passing to `H`-coinvariants (`lem:s04-hida`(d), `e M ⊗ R[Δ_s] = e (M ⊗ R[Δ_s])`), and
  `controlEquiv` is the composite of (d).
* **Rank.** Ranks of free modules are constant along a tower of base changes
  (`finrank_const_of_baseChange`, the rank half of `lem:s04-hida`(d)).

All statements assume `HasOrdDecomp` on both sides as ordinary arguments (D-e).
-/

@[expose] public section

open scoped Pointwise TensorProduct

namespace Langlandscape.Ordinary

noncomputable section

open Representation

/-! ### Permutation modules and their coinvariants -/

section Permutation

variable (R : Type*) [CommRing R] (H : Type*) [Group H] (Y : Type*) [MulAction H Y]

/-- `lem:s04-hida`(c) (`s04-hida`): the permutation representation of `H` on `R[Y] = Y →₀ R`,
`h · [y] = [h • y]` (the `ZX`-typed form, `Finsupp.lmapDomain`). -/
def permRep : Representation R H (Y →₀ R) where
  toFun h := Finsupp.lmapDomain R R (fun y : Y => h • y)
  map_one' := by
    refine Finsupp.lhom_ext fun y r => ?_
    simp
  map_mul' g h := by
    refine Finsupp.lhom_ext fun y r => ?_
    simp [mul_smul]

/-- `lem:s04-hida`(c) (`s04-hida`): `permRep` on basis vectors. -/
theorem permRep_single (h : H) (y : Y) (r : R) :
    permRep R H Y h (Finsupp.single y r) = Finsupp.single (h • y) r := by
  simp [permRep]

variable {R H Y}
variable {Z : Type*}

/-- `lem:s04-hida`(c) (`s04-hida`): an `H`-invariant map `π : Y → Z` induces
`π_* : R[Y]_H → R[Z]`. -/
def coinvToFinsupp (π : Y → Z) (hinv : ∀ (h : H) (y : Y), π (h • y) = π y) :
    (permRep R H Y).Coinvariants →ₗ[R] (Z →₀ R) :=
  Coinvariants.lift (permRep R H Y) (Finsupp.lmapDomain R R π) fun h =>
    Finsupp.lhom_ext fun y r => by
      simp only [LinearMap.coe_comp, Function.comp_apply, permRep_single,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hinv]

/-- `lem:s04-hida`(c) (`s04-hida`): `π_*` on the class of a basis vector. -/
theorem coinvToFinsupp_mk_single (π : Y → Z) (hinv : ∀ (h : H) (y : Y), π (h • y) = π y)
    (y : Y) (r : R) :
    coinvToFinsupp π hinv (Coinvariants.mk (permRep R H Y) (Finsupp.single y r)) =
      Finsupp.single (π y) r := by
  simp only [coinvToFinsupp, Coinvariants.lift_mk, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- `lem:s04-hida`(c) (`s04-hida`): a section `R[Z] → R[Y]_H` of `π_*`, `[z] ↦ [y]` for any
`y ∈ π⁻¹ z`. -/
def finsuppToCoinv (π : Y → Z) (hπ : Function.Surjective π) :
    (Z →₀ R) →ₗ[R] (permRep R H Y).Coinvariants :=
  Finsupp.linearCombination R fun z =>
    Coinvariants.mk (permRep R H Y) (Finsupp.single (Function.surjInv hπ z) (1 : R))

/-- `lem:s04-hida`(c) (`s04-hida`): fibres of `π` that are `H`-orbits make `π` `H`-invariant. -/
theorem inv_of_fibres {π : Y → Z} (hfib : ∀ y y' : Y, π y = π y' ↔ ∃ h : H, h • y = y')
    (h : H) (y : Y) : π (h • y) = π y :=
  (hfib (h • y) y).2 ⟨h⁻¹, inv_smul_smul h y⟩

/-- `lem:s04-hida`(c), second claim (`s04-hida`): if `π : Y → Z` is surjective and its fibres are
exactly the `H`-orbits, then `π_*` induces `R[Y]_H ≃ R[Z]` (permutation modules have
`R[Y]_H = R[Y⧸H]`). Generic commutative `R`; the action need not be free. -/
def coinvEquivOfFibres (π : Y → Z) (hπ : Function.Surjective π)
    (hfib : ∀ y y' : Y, π y = π y' ↔ ∃ h : H, h • y = y') :
    (permRep R H Y).Coinvariants ≃ₗ[R] (Z →₀ R) :=
  LinearEquiv.ofLinearMap (coinvToFinsupp π (inv_of_fibres hfib)) (finsuppToCoinv π hπ)
    (Finsupp.lhom_ext fun z r => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply, finsuppToCoinv,
        Finsupp.linearCombination_single, map_smul, coinvToFinsupp_mk_single,
        Function.surjInv_eq hπ, Finsupp.smul_single_one])
    (Coinvariants.hom_ext (Finsupp.lhom_ext fun y r => by
      obtain ⟨h, hh⟩ := (hfib y (Function.surjInv hπ (π y))).1 (Function.surjInv_eq hπ (π y)).symm
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
        coinvToFinsupp_mk_single, finsuppToCoinv, Finsupp.linearCombination_single]
      rw [← hh, ← permRep_single R H Y h y 1, Coinvariants.mk_self_apply,
        ← Finsupp.smul_single_one y r, map_smul]))

/-- `lem:s04-hida`(c) (`s04-hida`): `coinvEquivOfFibres` on basis vectors is `π_*`. -/
theorem coinvEquivOfFibres_mk_single (π : Y → Z) (hπ : Function.Surjective π)
    (hfib : ∀ y y' : Y, π y = π y' ↔ ∃ h : H, h • y = y') (y : Y) (r : R) :
    coinvEquivOfFibres π hπ hfib (Coinvariants.mk (permRep R H Y) (Finsupp.single y r)) =
      Finsupp.single (π y) r :=
  coinvToFinsupp_mk_single π (inv_of_fibres hfib) y r

/-- `lem:s04-hida`(c) (`s04-hida`): the fibres of `Y → Y⧸H` are the `H`-orbits. -/
theorem orbit_fibres (y y' : Y) :
    (Quotient.mk (MulAction.orbitRel H Y) y = Quotient.mk (MulAction.orbitRel H Y) y') ↔
      ∃ h : H, h • y = y' := by
  constructor
  · intro hq
    have hmem : y' ∈ MulAction.orbit H y := Quotient.eq.1 hq.symm
    exact MulAction.mem_orbit_iff.1 hmem
  · rintro ⟨g, rfl⟩
    have hmem : g • y ∈ MulAction.orbit H y := MulAction.mem_orbit y g
    exact ((Quotient.eq (r := MulAction.orbitRel H Y)).2 hmem).symm

variable (R H Y) in
/-- `lem:s04-hida`(c) (`s04-hida`): `R[Y]_H ≃ R[Y⧸H]` (coinvariant form of
`R[Y] ⊗_{R[G]} R[G⧸H] ≃ R[Y⧸H]`). -/
def coinvEquivOrbits :
    (permRep R H Y).Coinvariants ≃ₗ[R] (MulAction.orbitRel.Quotient H Y →₀ R) :=
  coinvEquivOfFibres (Quotient.mk (MulAction.orbitRel H Y)) Quotient.mk_surjective orbit_fibres

end Permutation

/-! ### Complementary pairs along surjections -/

section Compl

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- `lem:s04-hida`(c),(d) (`s04-hida`): if `f` is surjective, `A ⊔ B = ⊤`, `A' ⊓ B' = ⊥` and
`f A ≤ A'`, `f B ≤ B'`, then `f A = A'`. -/
theorem map_eq_of_sup_eq_top_of_disjoint (f : M →ₗ[R] N) (hf : Function.Surjective f)
    {A B : Submodule R M} {A' B' : Submodule R N} (hAB : A ⊔ B = ⊤) (hAB' : Disjoint A' B')
    (hA : A.map f ≤ A') (hB : B.map f ≤ B') : A.map f = A' := by
  refine le_antisymm hA fun x hx => ?_
  obtain ⟨m, rfl⟩ := hf x
  have hm : m ∈ A ⊔ B := by rw [hAB]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hm
  have hfa : f a ∈ A' := hA (Submodule.mem_map_of_mem ha)
  have hfb : f b ∈ B' := hB (Submodule.mem_map_of_mem hb)
  have hfb' : f b ∈ A' := by
    have hsub : f b = f (a + b) - f a := by rw [map_add, add_sub_cancel_left]
    rw [hsub]
    exact A'.sub_mem hx hfa
  have h0 : f b = 0 := Submodule.disjoint_def.1 hAB' _ hfb' hfb
  rw [map_add, h0, add_zero]
  exact Submodule.mem_map_of_mem ha

/-- `lem:s04-hida`(c),(d) (`s04-hida`): the projections of two complementary pairs commute with
`f` as soon as `f A ≤ A'` and `f B ≤ B'` (no surjectivity needed). -/
theorem map_projection_of_le (f : M →ₗ[R] N) {A B : Submodule R M} {A' B' : Submodule R N}
    (h : IsCompl A B) (h' : IsCompl A' B') (hA : A.map f ≤ A') (hB : B.map f ≤ B') (x : M) :
    f (A.projection B h x) = A'.projection B' h' (f x) := by
  have h1 : A'.projection B' h' (f (A.projection B h x)) = f (A.projection B h x) :=
    Submodule.projection_apply_of_mem_left h'
      (hA (Submodule.mem_map_of_mem (Submodule.projection_apply_mem h x)))
  have h2 : A'.projection B' h' (f (B.projection A h.symm x)) = 0 :=
    Submodule.projection_apply_of_mem_right h'
      (hB (Submodule.mem_map_of_mem (Submodule.projection_apply_mem h.symm x)))
  calc f (A.projection B h x)
      = A'.projection B' h' (f (A.projection B h x)) +
          A'.projection B' h' (f (B.projection A h.symm x)) := by rw [h1, h2, add_zero]
    _ = A'.projection B' h' (f x) := by
          rw [← map_add, ← map_add, Submodule.projection_add_projection_eq_self h x]

/-- `lem:s04-hida`(c) (`s04-hida`): under the hypotheses of `map_eq_of_sup_eq_top_of_disjoint`
and `ker f ≤ B`, `f` restricts to an isomorphism `A ≃ A'`. -/
def complEquivOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    {A B : Submodule R M} {A' B' : Submodule R N} (h : IsCompl A B) (h' : IsCompl A' B')
    (hA : A.map f ≤ A') (hB : B.map f ≤ B') (hker : LinearMap.ker f ≤ B) : A ≃ₗ[R] A' :=
  LinearEquiv.ofBijective (f.restrict fun x hx => hA (Submodule.mem_map_of_mem hx))
    ⟨by
      refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
      have hx0 : f x = 0 := by
        have := congrArg Subtype.val hx
        simpa only [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using this
      exact Submodule.coe_eq_zero.1
        (Submodule.disjoint_def.1 h.disjoint _ x.2 (hker (LinearMap.mem_ker.2 hx0))),
    by
      rintro ⟨y, hy⟩
      have hy' : y ∈ A.map f := by
        rw [map_eq_of_sup_eq_top_of_disjoint f hf h.sup_eq_top h'.disjoint hA hB]
        exact hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy'
      exact ⟨⟨x, hx⟩, rfl⟩⟩

/-- `lem:s04-hida`(c) (`s04-hida`): `complEquivOfSurjective` is `f`. -/
theorem complEquivOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    {A B : Submodule R M} {A' B' : Submodule R N} (h : IsCompl A B) (h' : IsCompl A' B')
    (hA : A.map f ≤ A') (hB : B.map f ≤ B') (hker : LinearMap.ker f ≤ B) (x : A) :
    (complEquivOfSurjective f hf h h' hA hB hker x : N) = f x :=
  rfl

end Compl

/-! ### Ordinary parts along equivariant maps -/

section Ordinary

variable {R : Type*} [CommRing R] (p : R)
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {T : Module.End R M} {T' : Module.End R N}

/-- `def:s04-e` (`s04-e`), functoriality (`ordPart_map`, image form): an equivariant map sends
`ordPart T` into `ordPart T'`. -/
theorem map_ordPart_le (f : M →ₗ[R] N) (hfT : f ∘ₗ T = T' ∘ₗ f) :
    (ordPart T).map f ≤ ordPart T' :=
  Submodule.map_le_iff_le_comap.2 (ordPart_map f hfT)

/-- `def:s04-e` (`s04-e`), functoriality (`nilPart_map`, image form): an equivariant map sends
`nilPart p T` into `nilPart p T'`. -/
theorem map_nilPart_le (f : M →ₗ[R] N) (hfT : f ∘ₗ T = T' ∘ₗ f) :
    (nilPart p T).map f ≤ nilPart p T' :=
  Submodule.map_le_iff_le_comap.2 (nilPart_map p f hfT)

/-- `lem:s04-hida`(c) (`s04-hida`): vectors killed by `T` lie in `nilPart p T`. -/
theorem mem_nilPart_of_apply_eq_zero {x : M} (hx : T x = 0) : x ∈ nilPart p T :=
  mem_nilPart.2 fun _ => ⟨1, by rw [pow_one, hx]; exact Submodule.zero_mem _⟩

/-- `lem:s04-hida`(c),(d) (`s04-hida`): a surjective `T`-equivariant map carries `ordPart T` onto
`ordPart T'` (both sides with `HasOrdDecomp`). -/
theorem map_ordPart_eq_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hfT : f ∘ₗ T = T' ∘ₗ f) (h : HasOrdDecomp p T) (h' : HasOrdDecomp p T') :
    (ordPart T).map f = ordPart T' :=
  map_eq_of_sup_eq_top_of_disjoint f hf (IsCompl.sup_eq_top h) (IsCompl.disjoint h')
    (map_ordPart_le f hfT) (map_nilPart_le p f hfT)

/-- `lem:s04-hida`(c),(d) (`s04-hida`): a surjective `T`-equivariant map carries `nilPart T` onto
`nilPart T'` (both sides with `HasOrdDecomp`). -/
theorem map_nilPart_eq_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hfT : f ∘ₗ T = T' ∘ₗ f) (h : HasOrdDecomp p T) (h' : HasOrdDecomp p T') :
    (nilPart p T).map f = nilPart p T' :=
  map_eq_of_sup_eq_top_of_disjoint f hf
    ((sup_comm _ _).trans (IsCompl.sup_eq_top h)) (IsCompl.disjoint h').symm
    (map_nilPart_le p f hfT) (map_ordPart_le f hfT)

/-- `lem:s04-hida`(c), first claim (`s04-hida`): if `f : M → N` is surjective and
`T`-equivariant and `T (ker f) = 0` (homologically `U_p (ker π'_*) = 0`), then `f` restricts to an
isomorphism `ordPart T ≃ ordPart T'` (`e π'_* : e R[X'_s] ≃ e R[X_s]`). -/
def ordPartEquivOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hfT : f ∘ₗ T = T' ∘ₗ f) (hker : ∀ x, f x = 0 → T x = 0) (h : HasOrdDecomp p T)
    (h' : HasOrdDecomp p T') : ordPart T ≃ₗ[R] ordPart T' :=
  complEquivOfSurjective f hf h h' (map_ordPart_le f hfT) (map_nilPart_le p f hfT)
    fun x hx => mem_nilPart_of_apply_eq_zero p (hker x (LinearMap.mem_ker.1 hx))

/-- `lem:s04-hida`(c) (`s04-hida`): `ordPartEquivOfSurjective` is `f`. -/
theorem ordPartEquivOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hfT : f ∘ₗ T = T' ∘ₗ f) (hker : ∀ x, f x = 0 → T x = 0) (h : HasOrdDecomp p T)
    (h' : HasOrdDecomp p T') (x : ordPart T) :
    (ordPartEquivOfSurjective p f hf hfT hker h h' x : N) = f x :=
  rfl

end Ordinary

/-! ### Base change to coinvariants (`lem:s04-hida`(d)) -/

section Coinv

variable {R : Type*} [CommRing R] (p : R) {H : Type*} [Group H]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `lem:s04-hida`(d) (`s04-hida`): an endomorphism commuting with a representation `ρ` of `H`
induces an endomorphism of the coinvariants `M_H = M ⊗_{R[G]} R[G⧸H]`. -/
def coinvEnd (ρ : Representation R H M) (T : Module.End R M)
    (hT : ∀ (h : H) (x : M), T (ρ h x) = ρ h (T x)) : Module.End R ρ.Coinvariants :=
  Coinvariants.lift ρ (Coinvariants.mk ρ ∘ₗ T) fun h => LinearMap.ext fun x => by
    simp only [LinearMap.coe_comp, Function.comp_apply, hT, Coinvariants.mk_self_apply]

/-- `lem:s04-hida`(d) (`s04-hida`): `coinvEnd` on classes. -/
theorem coinvEnd_mk (ρ : Representation R H M) (T : Module.End R M)
    (hT : ∀ (h : H) (x : M), T (ρ h x) = ρ h (T x)) (x : M) :
    coinvEnd ρ T hT (Coinvariants.mk ρ x) = Coinvariants.mk ρ (T x) :=
  rfl

/-- `lem:s04-hida`(d) (`s04-hida`): the quotient map `M → M_H` is equivariant. -/
theorem mk_comp_eq_coinvEnd_comp (ρ : Representation R H M) (T : Module.End R M)
    (hT : ∀ (h : H) (x : M), T (ρ h x) = ρ h (T x)) :
    Coinvariants.mk ρ ∘ₗ T = coinvEnd ρ T hT ∘ₗ Coinvariants.mk ρ :=
  rfl

variable (ρ : Representation R H M) (T : Module.End R M)
  (hT : ∀ (h : H) (x : M), T (ρ h x) = ρ h (T x))

/-- `lem:s04-hida`(d) (`s04-hida`): `e (M_H) = (e M)_H` as submodules: the image of `ordPart T`
in `M_H` is `ordPart` of the induced endomorphism. -/
theorem map_ordPart_coinv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT)) :
    (ordPart T).map (Coinvariants.mk ρ) = ordPart (coinvEnd ρ T hT) :=
  map_ordPart_eq_of_surjective p _ (Coinvariants.mk_surjective ρ)
    (mk_comp_eq_coinvEnd_comp ρ T hT) h h'

/-- `lem:s04-hida`(d) (`s04-hida`): the ordinary projector commutes with the base change
`M ↦ M_H`. -/
theorem ordProj_coinv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT)) (x : M) :
    Coinvariants.mk ρ (ordProj p T h x) = ordProj p (coinvEnd ρ T hT) h' (Coinvariants.mk ρ x) :=
  LinearMap.congr_fun (ordProj_map _ (mk_comp_eq_coinvEnd_comp ρ T hT) h h') x

/-- `lem:s04-hida`(d) (`s04-hida`): `M ↠ M_H` restricted to the ordinary parts. -/
def ordPartToCoinv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT)) :
    ordPart T →ₗ[R] ordPart (coinvEnd ρ T hT) :=
  (Coinvariants.mk ρ).restrict fun x hx => by
    rw [← map_ordPart_coinv p ρ T hT h h']
    exact Submodule.mem_map_of_mem hx

/-- `lem:s04-hida`(d) (`s04-hida`): `ordPartToCoinv` is surjective. -/
theorem ordPartToCoinv_surjective (h : HasOrdDecomp p T)
    (h' : HasOrdDecomp p (coinvEnd ρ T hT)) :
    Function.Surjective (ordPartToCoinv p ρ T hT h h') := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ (ordPart T).map (Coinvariants.mk ρ) := by
    rw [map_ordPart_coinv p ρ T hT h h']
    exact hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy'
  exact ⟨⟨x, hx⟩, rfl⟩

/-- `lem:s04-hida`(d) (`s04-hida`): the kernel of `ordPartToCoinv` is `ordPart T ∩ ker(M → M_H)`. -/
theorem ker_ordPartToCoinv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT)) :
    (Coinvariants.ker ρ).comap (ordPart T).subtype =
      LinearMap.ker (ordPartToCoinv p ρ T hT h h') := by
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker,
    ← Submodule.coe_eq_zero, ordPartToCoinv, LinearMap.coe_restrict_apply,
    Coinvariants.mk_eq_zero]

/-- `lem:s04-hida`(d) (`s04-hida`): `e M ⊗_{R[G]} R[G⧸H] ≃ e (M ⊗_{R[G]} R[G⧸H])` in coinvariant
form: `(ordPart T) ⧸ (ordPart T ∩ ker(M → M_H)) ≃ ordPart (T on M_H)`. -/
def ordCoinvEquiv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT)) :
    ((ordPart T) ⧸ (Coinvariants.ker ρ).comap (ordPart T).subtype) ≃ₗ[R]
      ordPart (coinvEnd ρ T hT) :=
  (Submodule.quotEquivOfEq _ _ (ker_ordPartToCoinv p ρ T hT h h')).trans
    (LinearMap.quotKerEquivOfSurjective _ (ordPartToCoinv_surjective p ρ T hT h h'))

/-- `lem:s04-hida`(d) (`s04-hida`): the control isomorphism, abstract form. Given the base change
`M ↦ M_H` (here `M = R[X_{s+1}]`, `H = ker(Δ_{s+1} → Δ_s)`) and a surjective equivariant
`g : M_H → N` (here `π'_* ∘ (R[X_{s+1}]_H ≃ R[X'_s])`) with `T' (ker g) = 0`, the composite
`(e M)_H ≃ e (M_H) ≃ e N` (`e R[X_{s+1}] ⊗ R[Δ_s] ≃ e R[X_s]`). -/
def controlEquiv (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT))
    {TN : Module.End R N} (g : ρ.Coinvariants →ₗ[R] N) (hg : Function.Surjective g)
    (hgT : g ∘ₗ coinvEnd ρ T hT = TN ∘ₗ g) (hker : ∀ x, g x = 0 → coinvEnd ρ T hT x = 0)
    (hN : HasOrdDecomp p TN) :
    ((ordPart T) ⧸ (Coinvariants.ker ρ).comap (ordPart T).subtype) ≃ₗ[R] ordPart TN :=
  (ordCoinvEquiv p ρ T hT h h').trans (ordPartEquivOfSurjective p g hg hgT hker h' hN)

/-- `lem:s04-hida`(d) (`s04-hida`): `controlEquiv` is induced by `g ∘ (M → M_H)`. -/
theorem controlEquiv_mk (h : HasOrdDecomp p T) (h' : HasOrdDecomp p (coinvEnd ρ T hT))
    {TN : Module.End R N} (g : ρ.Coinvariants →ₗ[R] N) (hg : Function.Surjective g)
    (hgT : g ∘ₗ coinvEnd ρ T hT = TN ∘ₗ g) (hker : ∀ x, g x = 0 → coinvEnd ρ T hT x = 0)
    (hN : HasOrdDecomp p TN) (x : ordPart T) :
    (controlEquiv p ρ T hT h h' g hg hgT hker hN (Submodule.Quotient.mk x) : N) =
      g (Coinvariants.mk ρ (x : M)) :=
  rfl

end Coinv

/-! ### Rank constancy -/

section Rank

/-- `lem:s04-hida`(d), rank (`s04-hida`): a base change `B ⊗_A M ≃ N` of a free module preserves
the rank (`A`, `B` nonzero commutative rings). -/
theorem finrank_eq_of_baseChange {A B M N : Type*} [CommRing A] [CommRing B] [Nontrivial A]
    [Nontrivial B] [Algebra A B] [AddCommGroup M] [Module A M] [Module.Free A M]
    [AddCommGroup N] [Module B N] (e : B ⊗[A] M ≃ₗ[B] N) :
    Module.finrank B N = Module.finrank A M := by
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- `lem:s04-hida`(d), rank (`s04-hida`): along a tower `A s ⊗_{A (s+1)} M (s+1) ≃ M s` of free
modules (`A s = ℤ_p[Δ_{s+1}]`, `M s = e ℤ_p[X_{s+1}]` after reindexing), the rank is constant. -/
theorem finrank_const_of_baseChange {A : ℕ → Type*} [∀ s, CommRing (A s)]
    [∀ s, Nontrivial (A s)] [∀ s, Algebra (A (s + 1)) (A s)] {M : ℕ → Type*}
    [∀ s, AddCommGroup (M s)] [∀ s, Module (A s) (M s)] [∀ s, Module.Free (A s) (M s)]
    (e : ∀ s, A s ⊗[A (s + 1)] M (s + 1) ≃ₗ[A s] M s) :
    ∀ s, Module.finrank (A s) (M s) = Module.finrank (A 0) (M 0)
  | 0 => rfl
  | s + 1 => by
    rw [← finrank_eq_of_baseChange (e s)]
    exact finrank_const_of_baseChange e s

end Rank

end

end Langlandscape.Ordinary
