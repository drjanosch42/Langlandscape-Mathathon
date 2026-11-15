/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.CommAlg.NewOld

/-!
# The `q`-new sub- versus quotient lattice (S05-L6)

`mathematics/chapters/s05/subquot.tex`, `prop:s05-subquot` (interface `if:s05-subquot`); it uses
stage 06's Lemma D(a) through the interface `if:s06-lemD` (`NewOldData.ann_a`) and builds the
`NewOldData` from the splitting `T_K = (T/𝔞)_K × (T/𝔟)_K` with `NewOldData.split_iff`.

Setting: `A` a Noetherian local domain, `T` a local, finite free `A`-algebra, `𝔞 𝔟 : Ideal T` with
`T/𝔞`, `T/𝔟` `A`-torsion-free, `𝔞 ⊓ 𝔟 = ⊥`, and `(𝔞 ⊔ 𝔟)` generating the unit ideal of
`K ⊗_A T`, `K = Frac A`. Let `H` be free of rank `r` over `T`, and write
`H[𝔞] = Submodule.torsionBySet T H 𝔞` and `𝔞H = 𝔞 • ⊤`. Then:

* `subquot_kernel`: `H[𝔞] = 𝔟 • H` and `H[𝔞] ≃ₗ[T] 𝔟^r`;
* `subquot_quot`: `H/𝔞H ≃ₗ[T] (T/𝔞)^r` (needs only `H` free);
* `subquot_injective`: the natural map `subquotMap 𝔞 H : H[𝔞] → H/𝔞H` is injective;
* `subquot_coker`: its cokernel is `≃ₗ[T] (T/(𝔞 ⊔ 𝔟))^r`;
* `subquot_coker_smul_eq_zero`: the cokernel is killed by `𝔞 ⊔ 𝔟` (so by the `c` of `split`).

The reduction to `r = 1` of the tex is done through coordinates in a basis `Fin r → T`
(`mem_smul_top_iff_basis`, `mem_torsionBySet_iff_basis`); the general forms only use
`ann 𝔞 = 𝔟` (and `𝔞 ⊓ 𝔟 = ⊥` for injectivity).

Edge cases (tex, after `prop:s05-subquot`):
* `r = 0`: every module above is `0` (`Fin 0 → _` is trivial); the statements hold as stated.
* `𝔞 = ⊥` or `𝔟 = ⊥` are allowed by `NewOldData`, and force the other ideal to be `⊤`
  (`subquot_b_eq_top_of_a_eq_bot`, `subquot_a_eq_top_of_b_eq_bot`): then `H[0] = H` with cokernel
  `0`, resp. `H[⊤] = 0 = H/H`. No case split is needed in the proofs.
* `𝔞 ⊔ 𝔟 = ⊤` (e.g. `A` a field): the cokernel is `0` (`subquot_coker_subsingleton`).
* `T` local is part of the seam shape (`stage-05.md` §0); the proofs use it only for `Nontrivial T`
  (needed for `finrank` and `Module.finBasisOfFinrankEq`; `T = 0` would be free over `A`).
-/

@[expose] public section

set_option autoImplicit false
-- The seam shape (`stage-05.md` §0) carries `[IsNoetherianRing A] [IsLocalRing A] [IsLocalRing T]`
-- on every headline declaration, also where a proof does not use them.
set_option linter.unusedSectionVars false

namespace Langlandscape.CommAlg

open scoped TensorProduct
open Submodule

section General

variable {T H : Type*} [CommRing T] [AddCommGroup H] [Module T H]

/-- `prop:s05-subquot` (`s05-subquot`): the natural map `H[𝔞] → H/𝔞H`, `h ↦ h mod 𝔞H`, where
`H[𝔞] = torsionBySet T H 𝔞` and `𝔞H = 𝔞 • ⊤`. -/
def subquotMap (𝔞 : Ideal T) (H : Type*) [AddCommGroup H] [Module T H] :
    torsionBySet T H 𝔞 →ₗ[T] H ⧸ 𝔞 • (⊤ : Submodule T H) :=
  (𝔞 • (⊤ : Submodule T H)).mkQ ∘ₗ (torsionBySet T H 𝔞).subtype

/-- `prop:s05-subquot` (`s05-subquot`): `subquotMap 𝔞 H h = h mod 𝔞H`. -/
theorem subquotMap_apply (𝔞 : Ideal T) (h : torsionBySet T H 𝔞) :
    subquotMap 𝔞 H h = Submodule.Quotient.mk (h : H) := rfl

variable {r : ℕ}

/-- `prop:s05-subquot` (`s05-subquot`), coordinates: for a basis `b` of `H`, `h ∈ I • H` iff every
coordinate of `h` lies in `I`. -/
theorem mem_smul_top_iff_basis (b : Module.Basis (Fin r) T H) (I : Ideal T) (h : H) :
    h ∈ I • (⊤ : Submodule T H) ↔ ∀ i, b.repr h i ∈ I := by
  constructor
  · intro hh
    refine Submodule.smul_induction_on (p := fun h => ∀ i, b.repr h i ∈ I) hh ?_ ?_
    · intro t ht n _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ ht
    · intro x y hx hy i
      rw [map_add, Finsupp.add_apply]
      exact I.add_mem (hx i) (hy i)
  · intro hh
    rw [← b.sum_repr h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hh i) Submodule.mem_top

/-- `prop:s05-subquot` (`s05-subquot`), coordinates: for a basis `b` of `H`, `h ∈ H[I]` iff every
coordinate of `h` lies in `Ann_T(I)`. -/
theorem mem_torsionBySet_iff_basis (b : Module.Basis (Fin r) T H) (I : Ideal T) (h : H) :
    h ∈ torsionBySet T H I ↔ ∀ i, b.repr h i ∈ ann I := by
  rw [Submodule.mem_torsionBySet_iff]
  constructor
  · intro hh i
    refine mem_ann.2 fun y hy => ?_
    have h1 := congrArg (fun x => b.repr x i) (hh ⟨y, hy⟩)
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [mul_comm]
    exact h1
  · rintro hh ⟨y, hy⟩
    apply b.repr.injective
    ext i
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    rw [mul_comm]
    exact mem_ann.1 (hh i) y hy

/-- `prop:s05-subquot` (`s05-subquot`), coordinates: `h ↦ (b.repr h i mod I)ᵢ`, `H → (T/I)^r`. -/
noncomputable def coordQuot (b : Module.Basis (Fin r) T H) (I : Ideal T) :
    H →ₗ[T] (Fin r → T ⧸ I) :=
  LinearMap.pi fun i => (Ideal.Quotient.mkₐ T I).toLinearMap ∘ₗ Finsupp.lapply i ∘ₗ
    b.repr.toLinearMap

/-- `prop:s05-subquot` (`s05-subquot`): `coordQuot b I h i = b.repr h i mod I`. -/
theorem coordQuot_apply (b : Module.Basis (Fin r) T H) (I : Ideal T) (h : H) (i : Fin r) :
    coordQuot b I h i = Ideal.Quotient.mk I (b.repr h i) := rfl

/-- `prop:s05-subquot` (`s05-subquot`): `coordQuot b I` is surjective. -/
theorem coordQuot_surjective (b : Module.Basis (Fin r) T H) (I : Ideal T) :
    Function.Surjective (coordQuot b I) := by
  intro v
  refine ⟨b.equivFun.symm fun i => (Ideal.Quotient.mk_surjective (v i)).choose, ?_⟩
  funext i
  rw [coordQuot_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]
  exact (Ideal.Quotient.mk_surjective (v i)).choose_spec

/-- `prop:s05-subquot` (`s05-subquot`): the kernel of `coordQuot b I` is `I • H`. -/
theorem ker_coordQuot (b : Module.Basis (Fin r) T H) (I : Ideal T) :
    LinearMap.ker (coordQuot b I) = I • (⊤ : Submodule T H) := by
  ext h
  rw [LinearMap.mem_ker, mem_smul_top_iff_basis b, funext_iff]
  simp only [coordQuot_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

/-- `prop:s05-subquot` (`s05-subquot`), general form: if `Ann_T(𝔞) = 𝔟` then `H[𝔞] = 𝔟 • H` for
`H` with a finite basis. -/
theorem torsionBySet_eq_smul_top {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟)
    (b : Module.Basis (Fin r) T H) : torsionBySet T H 𝔞 = 𝔟 • (⊤ : Submodule T H) := by
  ext h
  rw [mem_torsionBySet_iff_basis b, mem_smul_top_iff_basis b, hann]

/-- `prop:s05-subquot` (`s05-subquot`): if `Ann_T(𝔞) = 𝔟`, the coordinate map `H[𝔞] → 𝔟^r`,
`h ↦ (b.repr h i)ᵢ`. -/
noncomputable def torsionBySetToPi {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟)
    (b : Module.Basis (Fin r) T H) : torsionBySet T H 𝔞 →ₗ[T] (Fin r → 𝔟) :=
  LinearMap.pi fun i => LinearMap.codRestrict 𝔟
    (Finsupp.lapply i ∘ₗ b.repr.toLinearMap ∘ₗ (torsionBySet T H 𝔞).subtype)
    (fun x => by
      rw [← hann]
      exact (mem_torsionBySet_iff_basis b 𝔞 x).1 x.2 i)

/-- `prop:s05-subquot` (`s05-subquot`): `torsionBySetToPi hann b x i = b.repr x i`. -/
theorem torsionBySetToPi_apply {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟)
    (b : Module.Basis (Fin r) T H) (x : torsionBySet T H 𝔞) (i : Fin r) :
    (torsionBySetToPi hann b x i : T) = b.repr x i := rfl

/-- `prop:s05-subquot` (`s05-subquot`), general form: if `Ann_T(𝔞) = 𝔟` then `H[𝔞] ≃ 𝔟^r` for
`H` with a basis indexed by `Fin r`. -/
noncomputable def torsionBySetEquiv {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟)
    (b : Module.Basis (Fin r) T H) : torsionBySet T H 𝔞 ≃ₗ[T] (Fin r → 𝔟) :=
  LinearEquiv.ofBijective (torsionBySetToPi hann b) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply b.repr.injective
      ext i
      have := congrArg Subtype.val (congrFun hxy i)
      rwa [torsionBySetToPi_apply, torsionBySetToPi_apply] at this
    · intro f
      have hrepr : ∀ i, b.repr (b.equivFun.symm fun j => (f j : T)) i = f i := fun i => by
        rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]
      refine ⟨⟨b.equivFun.symm fun j => (f j : T), ?_⟩, ?_⟩
      · rw [mem_torsionBySet_iff_basis b, hann]
        intro i
        rw [hrepr]
        exact (f i).2
      · funext i
        apply Subtype.ext
        rw [torsionBySetToPi_apply]
        exact hrepr i)

/-- `prop:s05-subquot` (`s05-subquot`), general form: `H/IH ≃ (T/I)^r` for `H` with a basis
indexed by `Fin r`. -/
noncomputable def quotSmulTopEquiv (I : Ideal T) (b : Module.Basis (Fin r) T H) :
    (H ⧸ I • (⊤ : Submodule T H)) ≃ₗ[T] (Fin r → T ⧸ I) :=
  (Submodule.quotEquivOfEq _ _ (ker_coordQuot b I).symm).trans
    ((coordQuot b I).quotKerEquivOfSurjective (coordQuot_surjective b I))

/-- `prop:s05-subquot` (`s05-subquot`), general form: if `𝔞 ⊓ 𝔟 = ⊥` and `Ann_T(𝔞) = 𝔟`, then
`H[𝔞] → H/𝔞H` is injective. -/
theorem subquotMap_injective {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (b : Module.Basis (Fin r) T H) : Function.Injective (subquotMap 𝔞 H) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, subquotMap_apply, Submodule.Quotient.mk_eq_zero,
    mem_smul_top_iff_basis b] at hx
  have hx' := (mem_torsionBySet_iff_basis b 𝔞 x).1 x.2
  rw [hann] at hx'
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply b.repr.injective
  ext i
  have h : b.repr x i ∈ 𝔞 ⊓ 𝔟 := ⟨hx i, hx' i⟩
  rw [hinf, Ideal.mem_bot] at h
  simpa using h

/-- `prop:s05-subquot` (`s05-subquot`): the map `H/𝔞H → (T/(𝔞 ⊔ 𝔟))^r` induced by the
coordinates; its kernel is the image of `H[𝔞]` (`ker_cokerMap`). -/
noncomputable def cokerMap (𝔞 𝔟 : Ideal T) (b : Module.Basis (Fin r) T H) :
    (H ⧸ 𝔞 • (⊤ : Submodule T H)) →ₗ[T] (Fin r → T ⧸ (𝔞 ⊔ 𝔟)) :=
  (𝔞 • (⊤ : Submodule T H)).liftQ (coordQuot b (𝔞 ⊔ 𝔟)) (by
    rw [ker_coordQuot]
    exact Submodule.smul_mono_left le_sup_left)

/-- `prop:s05-subquot` (`s05-subquot`): `cokerMap` is surjective. -/
theorem cokerMap_surjective (𝔞 𝔟 : Ideal T) (b : Module.Basis (Fin r) T H) :
    Function.Surjective (cokerMap 𝔞 𝔟 b) := by
  intro v
  obtain ⟨h, rfl⟩ := coordQuot_surjective b (𝔞 ⊔ 𝔟) v
  exact ⟨Submodule.Quotient.mk h, rfl⟩

/-- `prop:s05-subquot` (`s05-subquot`), general form: if `Ann_T(𝔞) = 𝔟`, the kernel of `cokerMap`
is the image of `H[𝔞] → H/𝔞H`. -/
theorem ker_cokerMap {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟) (b : Module.Basis (Fin r) T H) :
    LinearMap.ker (cokerMap 𝔞 𝔟 b) = LinearMap.range (subquotMap 𝔞 H) := by
  rw [cokerMap, Submodule.ker_liftQ, ker_coordQuot, Submodule.sup_smul, Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq, subquotMap, LinearMap.range_comp,
    Submodule.range_subtype, torsionBySet_eq_smul_top hann b]

/-- `prop:s05-subquot` (`s05-subquot`), general form: if `Ann_T(𝔞) = 𝔟`, the cokernel of
`H[𝔞] → H/𝔞H` is `(T/(𝔞 ⊔ 𝔟))^r`. -/
noncomputable def cokerEquiv {𝔞 𝔟 : Ideal T} (hann : ann 𝔞 = 𝔟) (b : Module.Basis (Fin r) T H) :
    ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) ≃ₗ[T]
      (Fin r → T ⧸ (𝔞 ⊔ 𝔟)) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerMap hann b).symm).trans
    ((cokerMap 𝔞 𝔟 b).quotKerEquivOfSurjective (cokerMap_surjective 𝔞 𝔟 b))

/-- `prop:s05-subquot` (`s05-subquot`): an element of `I` acts as `0` on `(T/I)^r`. -/
theorem smul_eq_zero_of_mem_quot {I : Ideal T} {t : T} (ht : t ∈ I) (v : Fin r → T ⧸ I) :
    t • v = 0 := by
  funext i
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (v i)
  rw [Pi.smul_apply, ← hs, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact I.mul_mem_right s ht

end General

section NewOld

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

/-- `prop:s05-subquot` (`s05-subquot`), edge case: in a `NewOldData`, `𝔞 = ⊥` forces `𝔟 = ⊤`
(by `NewOldData.ann_a`, `if:s06-lemD`(a)); `NewOldData` allows this case. -/
theorem subquot_b_eq_top_of_a_eq_bot (D : NewOldData A S) (h : D.𝔞 = ⊥) : D.𝔟 = ⊤ := by
  rw [← D.ann_a, h, eq_top_iff]
  intro x _
  refine mem_ann.2 fun y hy => ?_
  rw [Ideal.mem_bot.1 hy, mul_zero]

/-- `prop:s05-subquot` (`s05-subquot`), edge case: in a `NewOldData`, `𝔟 = ⊥` forces `𝔞 = ⊤`
(by `NewOldData.ann_b`, `if:s06-lemD`(a)); `NewOldData` allows this case. -/
theorem subquot_a_eq_top_of_b_eq_bot (D : NewOldData A S) (h : D.𝔟 = ⊥) : D.𝔞 = ⊤ := by
  rw [← D.ann_b, h, eq_top_iff]
  intro x _
  refine mem_ann.2 fun y hy => ?_
  rw [Ideal.mem_bot.1 hy, mul_zero]

end NewOld

section Headline

variable {A T : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Free A T] [Module.Finite A T]
  {𝔞 𝔟 : Ideal T}
  {H : Type*} [AddCommGroup H] [Module T H] [Module.Free T H] [Module.Finite T H] {r : ℕ}

/-- `prop:s05-subquot` (`s05-subquot`): the `NewOldData A T` of the subquot setting, built from the
splitting `T_K = (T/𝔞)_K × (T/𝔟)_K` (in the form `(𝔞 ⊔ 𝔟) K⊗T = ⊤`) by stage 06's
`NewOldData.split_iff` (`if:s06-lemD`). -/
def subquotData (𝔞 𝔟 : Ideal T) (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤) :
    NewOldData A T where
  𝔞 := 𝔞
  𝔟 := 𝔟
  free := inferInstance
  finite := inferInstance
  tf_a := htf_a
  tf_b := htf_b
  inf_eq_bot := hinf
  split := (NewOldData.split_iff 𝔞 𝔟).2 hsplit

/-- `prop:s05-subquot` (`s05-subquot`), kernel: for `H` free of rank `r` over `T`,
`H[𝔞] = 𝔟 • H` and `H[𝔞] ≃ₗ[T] 𝔟^r`. Uses `NewOldData.ann_a` (`if:s06-lemD`(a)) on
`subquotData`. For `r = 0` both sides are `0`. -/
theorem subquot_kernel (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    torsionBySet T H 𝔞 = 𝔟 • (⊤ : Submodule T H) ∧
      Nonempty (torsionBySet T H 𝔞 ≃ₗ[T] (Fin r → 𝔟)) := by
  have hann : ann 𝔞 = 𝔟 := (subquotData 𝔞 𝔟 htf_a htf_b hinf hsplit).ann_a
  let b := Module.finBasisOfFinrankEq T H hr
  exact ⟨torsionBySet_eq_smul_top hann b, ⟨torsionBySetEquiv hann b⟩⟩

/-- `prop:s05-subquot` (`s05-subquot`), quotient: for `H` free of rank `r` over `T`,
`H/𝔞H ≃ₗ[T] (T/𝔞)^r`. Needs only that `H` is free of rank `r`. -/
theorem subquot_quot (𝔞 : Ideal T) (hr : Module.finrank T H = r) :
    Nonempty ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ≃ₗ[T] (Fin r → T ⧸ 𝔞)) :=
  ⟨quotSmulTopEquiv 𝔞 (Module.finBasisOfFinrankEq T H hr)⟩

/-- `prop:s05-subquot` (`s05-subquot`), injectivity: for `H` free of finite rank over `T`, the
natural map `H[𝔞] → H/𝔞H` is injective (its kernel is `𝔟H ∩ 𝔞H = (𝔞 ⊓ 𝔟)H = 0`). -/
theorem subquot_injective (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤) :
    Function.Injective (subquotMap 𝔞 H) :=
  subquotMap_injective (subquotData 𝔞 𝔟 htf_a htf_b hinf hsplit).ann_a hinf
    (Module.finBasisOfFinrankEq T H rfl)

/-- `prop:s05-subquot` (`s05-subquot`), cokernel: for `H` free of rank `r` over `T`, the cokernel
of `H[𝔞] → H/𝔞H` is `≃ₗ[T] (T/(𝔞 ⊔ 𝔟))^r`. For `r = 0` it is `0`. -/
theorem subquot_coker (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    Nonempty (((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) ≃ₗ[T]
      (Fin r → T ⧸ (𝔞 ⊔ 𝔟))) :=
  ⟨cokerEquiv (subquotData 𝔞 𝔟 htf_a htf_b hinf hsplit).ann_a
    (Module.finBasisOfFinrankEq T H hr)⟩

/-- `prop:s05-subquot` (`s05-subquot`): the cokernel of `H[𝔞] → H/𝔞H` is killed by every
`t ∈ 𝔞 ⊔ 𝔟`, in particular by the image of the `c ≠ 0` of `NewOldData.split`. -/
theorem subquot_coker_smul_eq_zero (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    {t : T} (ht : t ∈ 𝔞 ⊔ 𝔟)
    (x : (H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) : t • x = 0 := by
  have hann : ann 𝔞 = 𝔟 := (subquotData 𝔞 𝔟 htf_a htf_b hinf hsplit).ann_a
  let e := cokerEquiv hann (Module.finBasisOfFinrankEq T H rfl)
  apply e.injective
  rw [map_smul, map_zero]
  exact smul_eq_zero_of_mem_quot ht _

/-- `prop:s05-subquot` (`s05-subquot`), edge case `𝔞 ⊔ 𝔟 = ⊤` (e.g. `A` a field): the cokernel of
`H[𝔞] → H/𝔞H` is `0`. -/
theorem subquot_coker_subsingleton (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (htop : 𝔞 ⊔ 𝔟 = ⊤) :
    Subsingleton ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) := by
  refine ⟨fun x y => ?_⟩
  have h1 : ∀ z : (H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H), z = 0 :=
    fun z => by
      rw [← one_smul T z]
      exact subquot_coker_smul_eq_zero htf_a htf_b hinf hsplit (by rw [htop]; exact Submodule.mem_top) z
  rw [h1 x, h1 y]

end Headline

end Langlandscape.CommAlg
