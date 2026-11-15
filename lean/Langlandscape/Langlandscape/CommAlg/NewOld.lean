/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# New/old duality: Lemma D (S06-L3)

`mathematics/chapters/s06/s06-m1.tex`, `lem:s06-D` (new/old duality, seed Lemma D, corrected);
interface `if:s06-lemD` (fixed
signature). Secondary reference: `plan/staged/stage-06-integral-defect.tex`,
`plan/implementation/stage-06.md` §0. For `D : NewOldData A S`:

* (a) `NewOldData.ann_a`, `NewOldData.ann_b`: `Ann_S(𝔞) = 𝔟` and `Ann_S(𝔟) = 𝔞` (no Gorenstein
  hypothesis).
* (b) for a trace `ℓ` (`hℓ : IsGorensteinWith A S ℓ`): `NewOldData.bEquivDualQuot : 𝔟 ≃ₗ[A] (S/𝔞)^∨`
  and `NewOldData.aEquivDualQuot : 𝔞 ≃ₗ[A] (S/𝔟)^∨`, `β ↦ ℓ(β ·)`. Mathlib has no `S`-module
  structure on `Module.Dual A _`, so the tex's `S`-isomorphisms are these `A`-linear isomorphisms
  together with the `S`-equivariance lemmas `_smul` (and the explicit formula `_apply`).
* (c) if moreover `S/𝔟` is `A`-free (`hb`): `NewOldData.isComplemented_b` (`𝔟` is an `A`-direct
  summand of `S`), `NewOldData.free_b`, `NewOldData.quotAEquivDualB : S/𝔞 ≃ₗ[A] 𝔟^∨`
  (`s ↦ ℓ(s ·)|_𝔟`) and `NewOldData.free_quot_a`.

Not formalized: the tex's remark that all of this commutes with base change (Lemma D applied to
base-changed data satisfying the hypotheses); only the trace itself base-changes
(`IsGorensteinWith.baseChange`, S06-L13, which formalizes Lemma S only).
-/

@[expose] public section

set_option autoImplicit false
-- The fixed `if:s06-lemD` signature carries `[IsNoetherianRing A] [IsLocalRing A]` on every
-- declaration (stage-06.md §0 variable block), also where a proof does not use them.
set_option linter.unusedSectionVars false

namespace Langlandscape.CommAlg

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- `lem:s06-D` (`s06-D`)(a), general form: if `I ⊓ J = ⊥`, `S/J` is `A`-torsion-free and some
nonzero `c ∈ A` lies in `I + J`, then `Ann_S(I) = J`. -/
theorem ann_eq_of_inf_eq_bot [IsDomain A] {I J : Ideal S} (htf : Module.IsTorsionFree A (S ⧸ J))
    (hIJ : I ⊓ J = ⊥) {c : A} (hc : c ≠ 0) (hcm : algebraMap A S c ∈ I ⊔ J) : ann I = J := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hcm
    have hmem : algebraMap A S c * x ∈ J := by
      rw [← hyz, add_mul, mul_comm y x, mem_ann.1 hx y hy, zero_add]
      exact J.mul_mem_right x hz
    have h1 : c • Ideal.Quotient.mk J x = c • (0 : S ⧸ J) := by
      rw [smul_zero, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    have h2 := htf.isSMulRegular (isRegular_iff_ne_zero.2 hc) h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  · intro x hx
    refine mem_ann.2 fun y hy => ?_
    have h : x * y ∈ I ⊓ J := ⟨I.mul_mem_left x hy, J.mul_mem_right y hx⟩
    rw [hIJ] at h
    exact h

/-- `lem:s06-D` (`s06-D`): the `A`-linear map `S/I → M` induced by an `A`-linear map `g : S → M`
vanishing on the ideal `I`. -/
noncomputable def quotLift {M : Type*} [AddCommGroup M] [Module A M] (I : Ideal S) (g : S →ₗ[A] M)
    (h : ∀ y ∈ I, g y = 0) : (S ⧸ I) →ₗ[A] M :=
  (I.restrictScalars A).liftQ g (fun y hy => LinearMap.mem_ker.2 (h y hy)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A I).symm.toLinearMap

/-- `lem:s06-D` (`s06-D`): `quotLift I g h (s mod I) = g s`. -/
theorem quotLift_mk {M : Type*} [AddCommGroup M] [Module A M] (I : Ideal S) (g : S →ₗ[A] M)
    (h : ∀ y ∈ I, g y = 0) (s : S) : quotLift I g h (Ideal.Quotient.mk I s) = g s := rfl

/-- `lem:s06-D` (`s06-D`): the inclusion of an ideal `I ⊆ S` as an `A`-linear map. -/
def idealSubtype (I : Ideal S) : I →ₗ[A] S where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `lem:s06-D` (`s06-D`): `idealSubtype I b = b`. -/
theorem idealSubtype_apply (I : Ideal S) (b : I) : idealSubtype (A := A) I b = (b : S) := rfl

/-- `lem:s06-D` (`s06-D`)(b), general form: for `J ≤ Ann_S(I)`, the `A`-linear map
`J → (S/I)^∨`, `β ↦ ℓ(β ·)`. -/
noncomputable def dualQuot (ℓ : Module.Dual A S) (I J : Ideal S) (hJ : J ≤ ann I) :
    J →ₗ[A] Module.Dual A (S ⧸ I) where
  toFun b := quotLift I (mulDual ℓ b) (fun y hy => by
    rw [mulDual_apply_apply, mem_ann.1 (hJ b.2) y hy, map_zero])
  map_add' b c := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [quotLift_mk, mulDual_apply_apply, LinearMap.add_apply, Submodule.coe_add, map_add]
  map_smul' a b := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [quotLift_mk, mulDual_apply_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower,
      map_smul, RingHom.id_apply]

/-- `lem:s06-D` (`s06-D`)(b), general form: `dualQuot ℓ I J hJ β (s mod I) = ℓ (β s)`. -/
theorem dualQuot_apply (ℓ : Module.Dual A S) (I J : Ideal S) (hJ : J ≤ ann I) (b : J) (s : S) :
    dualQuot ℓ I J hJ b (Ideal.Quotient.mk I s) = ℓ ((b : S) * s) := rfl

/-- `lem:s06-D` (`s06-D`)(b), general form: if `ℓ` is a trace and `Ann_S(I) = J`, then
`β ↦ ℓ(β ·)` is a bijection `J → (S/I)^∨`. -/
theorem dualQuot_bijective {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) {I J : Ideal S}
    (h : ann I = J) : Function.Bijective (dualQuot ℓ I J h.ge) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    apply Subtype.ext
    refine hℓ.eq_zero_of_forall fun x => ?_
    have hx := LinearMap.congr_fun hb (Ideal.Quotient.mk I x)
    rw [dualQuot_apply] at hx
    exact hx
  · intro φ
    obtain ⟨s, hs⟩ := hℓ.exists_eq (φ ∘ₗ (Ideal.Quotient.mkₐ A I).toLinearMap)
    have hsJ : s ∈ J := by
      rw [← h]
      refine mem_ann.2 fun y hy => hℓ.eq_zero_of_forall fun x => ?_
      rw [mul_assoc, ← hs, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 (I.mul_mem_right x hy), map_zero]
    refine ⟨⟨s, hsJ⟩, LinearMap.ext fun q => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [dualQuot_apply, ← hs, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk]

namespace NewOldData

variable [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (D : NewOldData A S)

/-- `lem:s06-D` (`s06-D`)(a): `Ann_S(𝔞) = 𝔟`. No Gorenstein hypothesis is needed. -/
theorem ann_a : ann D.𝔞 = D.𝔟 := by
  obtain ⟨c, hc, hcm⟩ := D.split
  exact ann_eq_of_inf_eq_bot D.tf_b D.inf_eq_bot hc hcm

/-- `lem:s06-D` (`s06-D`)(a): `Ann_S(𝔟) = 𝔞`. No Gorenstein hypothesis is needed. -/
theorem ann_b : ann D.𝔟 = D.𝔞 := by
  obtain ⟨c, hc, hcm⟩ := D.split
  exact ann_eq_of_inf_eq_bot D.tf_a (by rw [inf_comm]; exact D.inf_eq_bot) hc
    (by rw [sup_comm]; exact hcm)

/-- `lem:s06-D` (`s06-D`)(b): `β ↦ ℓ(β ·)` is an isomorphism `𝔟 ≅ (S/𝔞)^∨`. The tex's
`S`-isomorphism = this `A`-linear iso + `bEquivDualQuot_smul` (Mathlib has no `S`-module structure
on `Module.Dual A (S ⧸ 𝔞)`); the explicit formula is `bEquivDualQuot_apply`. -/
noncomputable def bEquivDualQuot {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) :
    D.𝔟 ≃ₗ[A] Module.Dual A (S ⧸ D.𝔞) :=
  LinearEquiv.ofBijective (dualQuot ℓ D.𝔞 D.𝔟 D.ann_a.ge) (dualQuot_bijective hℓ D.ann_a)

/-- `lem:s06-D` (`s06-D`)(b): `bEquivDualQuot hℓ β (s mod 𝔞) = ℓ (β s)`. -/
theorem bEquivDualQuot_apply {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (b : D.𝔟) (s : S) :
    D.bEquivDualQuot hℓ b (Ideal.Quotient.mk D.𝔞 s) = ℓ ((b : S) * s) := rfl

/-- `lem:s06-D` (`s06-D`)(b): `S`-equivariance of `bEquivDualQuot`: `s • β ↦ ℓ(β ·) ∘ (s ·)`. -/
theorem bEquivDualQuot_smul {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (s : S) (b : D.𝔟) :
    D.bEquivDualQuot hℓ (s • b) =
      D.bEquivDualQuot hℓ b ∘ₗ LinearMap.mulLeft A (Ideal.Quotient.mk D.𝔞 s) := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← map_mul, bEquivDualQuot_apply,
    bEquivDualQuot_apply, Submodule.coe_smul, smul_eq_mul, mul_assoc, mul_left_comm]

/-- `lem:s06-D` (`s06-D`)(b): `α ↦ ℓ(α ·)` is an isomorphism `𝔞 ≅ (S/𝔟)^∨`. The tex's
`S`-isomorphism = this `A`-linear iso + `aEquivDualQuot_smul`. -/
noncomputable def aEquivDualQuot {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) :
    D.𝔞 ≃ₗ[A] Module.Dual A (S ⧸ D.𝔟) :=
  LinearEquiv.ofBijective (dualQuot ℓ D.𝔟 D.𝔞 D.ann_b.ge) (dualQuot_bijective hℓ D.ann_b)

/-- `lem:s06-D` (`s06-D`)(b): `aEquivDualQuot hℓ α (s mod 𝔟) = ℓ (α s)`. -/
theorem aEquivDualQuot_apply {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (a : D.𝔞) (s : S) :
    D.aEquivDualQuot hℓ a (Ideal.Quotient.mk D.𝔟 s) = ℓ ((a : S) * s) := rfl

/-- `lem:s06-D` (`s06-D`)(b): `S`-equivariance of `aEquivDualQuot`. -/
theorem aEquivDualQuot_smul {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (s : S) (a : D.𝔞) :
    D.aEquivDualQuot hℓ (s • a) =
      D.aEquivDualQuot hℓ a ∘ₗ LinearMap.mulLeft A (Ideal.Quotient.mk D.𝔟 s) := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← map_mul, aEquivDualQuot_apply,
    aEquivDualQuot_apply, Submodule.coe_smul, smul_eq_mul, mul_assoc, mul_left_comm]

/-- `lem:s06-D` (`s06-D`)(c): if `S/𝔟` is `A`-free, the projection `S → S/𝔟` has an `A`-linear
section. -/
theorem exists_section_b (hb : Module.Free A (S ⧸ D.𝔟)) :
    ∃ σ : (S ⧸ D.𝔟) →ₗ[A] S, ∀ q, Ideal.Quotient.mk D.𝔟 (σ q) = q := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Ideal.Quotient.mkₐ A D.𝔟).toLinearMap
    LinearMap.id (Ideal.Quotient.mkₐ_surjective A D.𝔟)
  exact ⟨σ, fun q => by simpa using LinearMap.congr_fun hσ q⟩

/-- `lem:s06-D` (`s06-D`)(c): if `S/𝔟` is `A`-free, `𝔟` is an `A`-direct summand of `S`. -/
theorem isComplemented_b (hb : Module.Free A (S ⧸ D.𝔟)) :
    IsComplemented (D.𝔟.restrictScalars A) := by
  obtain ⟨σ, hσ⟩ := D.exists_section_b hb
  refine ⟨LinearMap.range σ, ⟨?_, ?_⟩⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hσ q]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - σ (Ideal.Quotient.mk D.𝔟 x), ?_, σ (Ideal.Quotient.mk D.𝔟 x),
      ⟨_, rfl⟩, sub_add_cancel _ _⟩
    show x - σ (Ideal.Quotient.mk D.𝔟 x) ∈ D.𝔟
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hσ, sub_self]

/-- `lem:s06-D` (`s06-D`)(c): if `S/𝔟` is `A`-free, there is an `A`-linear retraction `S → 𝔟`. -/
theorem exists_retraction_b (hb : Module.Free A (S ⧸ D.𝔟)) :
    ∃ r : S →ₗ[A] D.𝔟, ∀ b : D.𝔟, r b = b := by
  obtain ⟨σ, hσ⟩ := D.exists_section_b hb
  let p : S →ₗ[A] S := σ ∘ₗ (Ideal.Quotient.mkₐ A D.𝔟).toLinearMap
  have hp : ∀ x, x - p x ∈ D.𝔟 := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    simp [p, hσ]
  refine ⟨{ toFun := fun x => ⟨x - p x, hp x⟩
            map_add' := fun x y => Subtype.ext (by
              simp only [map_add, Submodule.coe_add]
              abel)
            map_smul' := fun a x => Subtype.ext (by
              simp only [map_smul, Submodule.coe_smul_of_tower, RingHom.id_apply, smul_sub]) },
    fun b => Subtype.ext ?_⟩
  show (b : S) - p b = b
  have : p b = 0 := by
    simp [p, Ideal.Quotient.eq_zero_iff_mem.2 b.2]
  rw [this, sub_zero]

/-- `lem:s06-D` (`s06-D`)(c): if `S/𝔟` is `A`-free, then `𝔟` is `A`-free (a direct summand of the
finite free `S`, projective and finite over the local ring `A`). -/
theorem free_b (hb : Module.Free A (S ⧸ D.𝔟)) : Module.Free A D.𝔟 := by
  obtain ⟨r, hr⟩ := D.exists_retraction_b hb
  have := D.free
  have := D.finite
  have : Module.Projective A D.𝔟 :=
    Module.Projective.of_split (idealSubtype D.𝔟) r (LinearMap.ext fun b => hr b)
  have : Module.Finite A D.𝔟 := Module.Finite.of_surjective r fun b => ⟨b, hr b⟩
  exact Module.free_of_flat_of_isLocalRing

/-- `lem:s06-D` (`s06-D`)(c): the `A`-linear map `S → 𝔟^∨`, `s ↦ ℓ(s ·)|_𝔟`. -/
noncomputable def toDualB (ℓ : Module.Dual A S) : S →ₗ[A] Module.Dual A D.𝔟 :=
  (idealSubtype D.𝔟).dualMap ∘ₗ mulDual ℓ

/-- `lem:s06-D` (`s06-D`)(c): `toDualB ℓ s b = ℓ (s b)`. -/
theorem toDualB_apply (ℓ : Module.Dual A S) (s : S) (b : D.𝔟) :
    D.toDualB ℓ s b = ℓ (s * (b : S)) := rfl

/-- `lem:s06-D` (`s06-D`)(c): `toDualB ℓ` vanishes on `𝔞` (as `𝔞 𝔟 = 0`). -/
theorem toDualB_eq_zero (ℓ : Module.Dual A S) (y : S) (hy : y ∈ D.𝔞) : D.toDualB ℓ y = 0 := by
  refine LinearMap.ext fun b => ?_
  rw [toDualB_apply, mem_ann.1 (D.ann_b.ge hy) b b.2, map_zero, LinearMap.zero_apply]

/-- `lem:s06-D` (`s06-D`)(c): under `hℓ` and `hb`, `s ↦ ℓ(s ·)|_𝔟` induces `S/𝔞 ≅ 𝔟^∨` (kernel
`Ann_S(𝔟) = 𝔞`; surjective because `𝔟` is a direct summand). -/
noncomputable def quotAEquivDualB {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)
    (hb : Module.Free A (S ⧸ D.𝔟)) : (S ⧸ D.𝔞) ≃ₗ[A] Module.Dual A D.𝔟 :=
  LinearEquiv.ofBijective (quotLift D.𝔞 (D.toDualB ℓ) (D.toDualB_eq_zero ℓ)) <| by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [quotLift_mk] at hq
      rw [Ideal.Quotient.eq_zero_iff_mem, ← D.ann_b]
      refine mem_ann.2 fun b hb' => hℓ.eq_zero_of_forall fun x => ?_
      have h := LinearMap.congr_fun hq ⟨b * x, D.𝔟.mul_mem_right x hb'⟩
      rw [toDualB_apply, LinearMap.zero_apply] at h
      rw [mul_assoc]
      exact h
    · intro ψ
      obtain ⟨r, hr⟩ := D.exists_retraction_b hb
      obtain ⟨s, hs⟩ := hℓ.exists_eq (ψ ∘ₗ r)
      refine ⟨Ideal.Quotient.mk D.𝔞 s, LinearMap.ext fun b => ?_⟩
      rw [quotLift_mk, toDualB_apply, ← hs, LinearMap.comp_apply, hr]

/-- `lem:s06-D` (`s06-D`)(c): `quotAEquivDualB hℓ hb (s mod 𝔞) β = ℓ (s β)`. -/
theorem quotAEquivDualB_mk {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)
    (hb : Module.Free A (S ⧸ D.𝔟)) (s : S) (b : D.𝔟) :
    D.quotAEquivDualB hℓ hb (Ideal.Quotient.mk D.𝔞 s) b = ℓ (s * (b : S)) := rfl

/-- `lem:s06-D` (`s06-D`)(c): under `hℓ` and `hb`, `S/𝔞 ≅ 𝔟^∨` is `A`-free. -/
theorem free_quot_a {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)
    (hb : Module.Free A (S ⧸ D.𝔟)) : Module.Free A (S ⧸ D.𝔞) := by
  have := D.free_b hb
  obtain ⟨r, hr⟩ := D.exists_retraction_b hb
  have := D.finite
  have : Module.Finite A D.𝔟 := Module.Finite.of_surjective r fun b => ⟨b, hr b⟩
  exact Module.Free.of_equiv (D.quotAEquivDualB hℓ hb).symm

end NewOldData

end Langlandscape.CommAlg
