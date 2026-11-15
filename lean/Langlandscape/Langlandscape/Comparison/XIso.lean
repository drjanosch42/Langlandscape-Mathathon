/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.CommAlg.SubQuot
public import Langlandscape.CommAlg.NewOld

/-!
# The algebraic half of `Hyp.X^iso` (S05-L8a)

`mathematics/chapters/s05/subquot.tex`, `prop:s05-Xiso` (for `def:s05-Xiso`, hypotheses (i)–(iii)):
if `H` is free of rank one over `T`, `T` is `A`-Gorenstein and `T' = T/𝔞` is `A`-Gorenstein, then
`H[𝔞] ≃ T'` as `T`-modules, non-canonically.

Proof, as in the tex: `prop:s05-subquot` (`subquot_kernel`, S05-L6) gives `H[𝔞] ≃ 𝔟`; Lemma D(b)
(`NewOldData.bEquivDualQuot`, `A`-linear, with the `T`-equivariance `bEquivDualQuot_smul`;
interface `if:s06-lemD`) gives `𝔟 ≃ Hom_A(T', A)`; the trace `ℓ'` of `T'` gives
`T' ≃ Hom_A(T', A)`, `s ↦ ℓ'(s ·)` (`mulDual`), which is `T`-equivariant as well. The composite
`𝔟 → T'` is therefore `T`-linear (`bEquivQuotOfGorenstein`).

Only the algebraic half is here; the registered hypothesis `Hyp.X.iso` is added by stage 05
(it needs `Hyp/HypX.lean`).

Edge cases: `𝔞 = ⊥` forces `𝔟 = ⊤` (`subquot_b_eq_top_of_a_eq_bot`) and the statement reads
`H ≃ T`; `𝔟 = ⊥` forces `𝔞 = ⊤`, `T' = 0` and `H[⊤] = 0`. Both are covered without a case split.
`T` local is part of the seam shape (`stage-05.md` §0); it enters only through `subquot_kernel`
(`Nontrivial T`, for `finrank`).
-/

@[expose] public section

set_option autoImplicit false
-- The seam shape carries `[IsNoetherianRing A] [IsLocalRing A] [IsLocalRing T]` on every
-- headline declaration, also where a proof does not use them.
set_option linter.unusedSectionVars false

namespace Langlandscape.Comparison

open scoped TensorProduct
open Langlandscape.CommAlg Submodule

variable {A T : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing T] [Algebra A T]

/-- `prop:s05-Xiso` (`s05-Xiso`): for a trace `ℓ'` of `T' = T/I`, the inverse of
`s ↦ ℓ'(s ·)` turns `φ ∘ (t ·)` into `t · (inverse of φ)`. -/
theorem mulDual_symm_comp_mulLeft {I : Ideal T} {ℓ' : Module.Dual A (T ⧸ I)}
    (hℓ' : IsGorensteinWith A (T ⧸ I) ℓ') (φ : Module.Dual A (T ⧸ I)) (x : T ⧸ I) :
    (LinearEquiv.ofBijective (mulDual ℓ') hℓ'.bijective).symm (φ ∘ₗ LinearMap.mulLeft A x) =
      x * (LinearEquiv.ofBijective (mulDual ℓ') hℓ'.bijective).symm φ := by
  set e := LinearEquiv.ofBijective (mulDual ℓ') hℓ'.bijective
  apply e.injective
  rw [e.apply_symm_apply]
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  conv_lhs => rw [← e.apply_symm_apply φ]
  change ℓ' (e.symm φ * (x * y)) = ℓ' (x * e.symm φ * y)
  congr 1
  ring

/-- `prop:s05-Xiso` (`s05-Xiso`): for `D : NewOldData A T` with `T` Gorenstein (trace `ℓ`) and
`T' = T/𝔞` Gorenstein (trace `ℓ'`), the `T`-linear isomorphism `𝔟 ≃ T'` obtained from Lemma D(b),
`𝔟 ≃ Hom_A(T', A)` (`bEquivDualQuot`), and `T' ≃ Hom_A(T', A)`, `s ↦ ℓ'(s ·)`. -/
noncomputable def bEquivQuotOfGorenstein (D : NewOldData A T) {ℓ : Module.Dual A T}
    (hℓ : IsGorensteinWith A T ℓ) {ℓ' : Module.Dual A (T ⧸ D.𝔞)}
    (hℓ' : IsGorensteinWith A (T ⧸ D.𝔞) ℓ') : D.𝔟 ≃ₗ[T] T ⧸ D.𝔞 :=
  let e := LinearEquiv.ofBijective (mulDual ℓ') hℓ'.bijective
  { toFun := fun b => e.symm (D.bEquivDualQuot hℓ b)
    invFun := fun x => (D.bEquivDualQuot hℓ).symm (e x)
    left_inv := fun b => by simp
    right_inv := fun x => by simp
    map_add' := fun b c => by simp
    map_smul' := fun t b => by
      rw [RingHom.id_apply, NewOldData.bEquivDualQuot_smul, mulDual_symm_comp_mulLeft hℓ',
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq] }

/-- `prop:s05-Xiso` (`s05-Xiso`): `bEquivQuotOfGorenstein` is characterised by
`ℓ'(φ(β) · s) = ℓ(β s)` for `β ∈ 𝔟`, `s ∈ T`. -/
theorem bEquivQuotOfGorenstein_spec (D : NewOldData A T) {ℓ : Module.Dual A T}
    (hℓ : IsGorensteinWith A T ℓ) {ℓ' : Module.Dual A (T ⧸ D.𝔞)}
    (hℓ' : IsGorensteinWith A (T ⧸ D.𝔞) ℓ') (b : D.𝔟) (s : T) :
    ℓ' (bEquivQuotOfGorenstein D hℓ hℓ' b * Ideal.Quotient.mk D.𝔞 s) = ℓ ((b : T) * s) := by
  set e := LinearEquiv.ofBijective (mulDual ℓ') hℓ'.bijective
  have h : e (bEquivQuotOfGorenstein D hℓ hℓ' b) = D.bEquivDualQuot hℓ b :=
    e.apply_symm_apply _
  rw [← D.bEquivDualQuot_apply hℓ, ← h]
  rfl

/-- `prop:s05-Xiso` (`s05-Xiso`), algebraic half of `def:s05-Xiso`: let `A` be a Noetherian local
domain, `T` a local `A`-algebra which is `A`-Gorenstein with trace `ℓ` (in particular finite free),
`𝔞 𝔟` ideals as in `prop:s05-subquot` (`T/𝔞`, `T/𝔟` torsion-free, `𝔞 ⊓ 𝔟 = ⊥`, splitting over
`Frac A`), and `T' = T/𝔞` `A`-Gorenstein. If `H` is free of rank one over `T`, then
`H[𝔞] ≃ₗ[T] T'` (non-canonically: the iso depends on a basis of `H`). -/
theorem xiso_of_gorenstein [IsLocalRing T] {𝔞 𝔟 : Ideal T} {ℓ : Module.Dual A T}
    (hℓ : IsGorensteinWith A T ℓ)
    (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞)) (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟))
    (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hT' : IsGorenstein A (T ⧸ 𝔞))
    {H : Type*} [AddCommGroup H] [Module T H] [Module.Free T H] [Module.Finite T H]
    (hrank : Module.finrank T H = 1) :
    Nonempty (torsionBySet T H 𝔞 ≃ₗ[T] T ⧸ 𝔞) := by
  have : Module.Free A T := hℓ.1
  have : Module.Finite A T := hℓ.2.1
  obtain ⟨ℓ', hℓ'⟩ := hT'
  obtain ⟨-, ⟨e₁⟩⟩ := subquot_kernel htf_a htf_b hinf hsplit (H := H) hrank
  let D := subquotData 𝔞 𝔟 htf_a htf_b hinf hsplit
  exact ⟨(e₁.trans (LinearEquiv.funUnique (Fin 1) T 𝔟)).trans
    (bEquivQuotOfGorenstein D hℓ (ℓ' := ℓ') hℓ')⟩

end Langlandscape.Comparison
