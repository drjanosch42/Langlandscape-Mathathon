import AlgJL.Meta.Tag
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Sets.Compacts

-- algebraic_jl fork (L-A, 2026-11-14): trimmed copy of lean/GL2TF/Common/RestrictedProduct.lean @84818d0.
-- Dropped (analytic): resProdMeasure, resProdAddMeasure, the namespaces ResProd/ResProdAdd (splitting measures),
-- resProdMeasure_isHaarMeasure_box, resProdMeasure_unique, resProdMeasure_factorization and their additive copies;
-- the measure-theory imports. Kept declarations are byte-identical.

/-!
# Restricted products: second countability and the restricted-product Haar measure (M3, unit U8)

Lean counterpart of the `X.topgrp`/`X.haar` restricted-product items typeset in `vol1/ch-0-06-haar.tex`
(D-RESPROD, `docs/notes/M3-resprod-spike.md`). Owner: L1.

Design (D-RESPROD, lead decisions 2026-10-18):
* `Πʳ i, [G i, K i]` is Mathlib's restricted product for the cofinite filter, with `K i` a `Subgroup`
  (an `AddSubgroup` in the additive copies). Openness of the `K i` is an explicit binder `hK`; the `Fact` that
  Mathlib's instances (`IsTopologicalGroup`, local compactness) need is installed locally inside the values.
* `resProdMeasure K hK μ := (∏ᶠ i, μ i (K i)) • haarMeasure (resProdBox K hK)`. The `finprod` needs no finiteness
  proof; the hypothesis `μ i (K i) = 1` for all but finitely many `i` lives in the theorems.
* The additive copies (for `𝔸_f`, A1 request 2026-10-18) are written by hand, not with `to_additive`: the value
  `∏ᶠ i, μ i (K i)` is a product of measures in both cases and must not be translated to a sum.
-/

open Filter Set TopologicalSpace MeasureTheory Measure
open scoped RestrictedProduct ENNReal NNReal

namespace GL2TF

/-! ### Second countability and the Borel σ-algebra -/

/-- A restricted product `Πʳ i, [X i, A i]` (cofinite filter) over a countable index set of second countable spaces
with open subsets `A i` is second countable. -/
@[tf_id "X.topgrp.thm:restricted-product-second-countable"]
theorem resProd_secondCountableTopology {ι : Type*} [Countable ι] (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)] [∀ i, SecondCountableTopology (X i)] (A : (i : ι) → Set (X i))
    (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [X i, A i]) := by
  have hS : ∀ F : Finset ι, Filter.cofinite ≤ 𝓟 ((F : Set ι)ᶜ) := fun F ↦ by
    rw [le_principal_iff, Filter.mem_cofinite, compl_compl]; exact F.finite_toSet
  let U : Finset ι → Set (Πʳ i, [X i, A i]) := fun F ↦ range (RestrictedProduct.inclusion X A (hS F))
  have hU : ∀ F, IsOpen (U F) := fun F ↦
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS F)).isOpen_range
  have hsc : ∀ F, SecondCountableTopology (U F) := fun F ↦ by
    have e := (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS F)).toIsEmbedding.toHomeomorph
    have : SecondCountableTopology (Πʳ i, [X i, A i]_[𝓟 ((F : Set ι)ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact e.symm.secondCountableTopology
  refine secondCountableTopology_of_countable_cover hU ?_
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ i ∉ F, x i ∈ A i := by
    have hx : {i | x i ∉ A i}.Finite := x.2
    exact ⟨hx.toFinset, fun i hi ↦ by simpa using hi⟩
  obtain ⟨y, hy⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually X A (hS F)
    (x := x) (eventually_principal.mpr fun i hi ↦ hF i hi)
  exact mem_iUnion.mpr ⟨F, y, hy⟩

/-- Second countability of `Πʳ i, [X i, A i]` as an instance, for the openness given as a `Fact` (the form Mathlib's
restricted-product instances use). -/
@[tf_aux "X.topgrp.lem:restricted-product-second-countable-instance"]
instance resProd_secondCountableTopology_inst {ι : Type*} [Countable ι] (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)] [∀ i, SecondCountableTopology (X i)] (A : (i : ι) → Set (X i))
    [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [X i, A i]) :=
  resProd_secondCountableTopology X A hA.out

/-- The Borel σ-algebra on a restricted product `Πʳ i, [X i, A i]_[𝓕]`. -/
@[tf_aux "X.topgrp.def:restricted-product-measurable-space"]
instance resProd_measurableSpace {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (A : (i : ι) → Set (X i)) (𝓕 : Filter ι) :
    MeasurableSpace (Πʳ i, [X i, A i]_[𝓕]) :=
  _root_.borel _

/-- The σ-algebra of `Πʳ i, [X i, A i]_[𝓕]` is the Borel σ-algebra. -/
@[tf_aux "X.topgrp.lem:restricted-product-borel-space"]
instance resProd_borelSpace {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (A : (i : ι) → Set (X i)) (𝓕 : Filter ι) :
    BorelSpace (Πʳ i, [X i, A i]_[𝓕]) :=
  ⟨rfl⟩

/-! ### The box `Π K_i` -/

section Mul

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- The box `Π K_i ⊆ Πʳ i, [G i, K i]` is compact if every `K i` is compact. -/
@[tf_aux "X.haar.lem:restricted-product-box-compact"]
theorem resProd_box_isCompact (K : ∀ i, Subgroup (G i)) [∀ i, CompactSpace (K i)] :
    IsCompact {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} := by
  have h : {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} =
      range (RestrictedProduct.structureMap G (fun i ↦ (K i : Set (G i))) Filter.cofinite) :=
    (RestrictedProduct.range_structureMap _ _).symm
  rw [h]
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

/-- The box `Π K_i ⊆ Πʳ i, [G i, K i]` is open if every `K i` is open. -/
@[tf_aux "X.haar.lem:restricted-product-box-open"]
theorem resProd_box_isOpen (K : ∀ i, Subgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) :
    IsOpen {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} :=
  RestrictedProduct.isOpen_forall_mem hK

/-- The box `Π K_i` has nonempty interior if every `K i` is open. -/
@[tf_aux "X.haar.lem:restricted-product-box-interior-nonempty"]
theorem resProd_box_interior_nonempty (K : ∀ i, Subgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) :
    (interior {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i}).Nonempty := by
  rw [(resProd_box_isOpen K hK).interior_eq]
  exact ⟨1, fun i ↦ (K i).one_mem⟩

/-- The box `Π K_i` as a compact set with nonempty interior in `Πʳ i, [G i, K i]`. -/
@[tf_aux "X.haar.def:restricted-product-box"]
def resProdBox (K : ∀ i, Subgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) [∀ i, CompactSpace (K i)] :
    PositiveCompacts (Πʳ i, [G i, K i]) where
  carrier := {x | ∀ i, x i ∈ K i}
  isCompact' := resProd_box_isCompact K
  interior_nonempty' := resProd_box_interior_nonempty K hK

end Mul

/-! ### Additive copies (for `𝔸_f`) -/

section Add

variable {ι : Type*} {G : ι → Type*} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]

/-- The box `Π K_i ⊆ Πʳ i, [G i, K i]` (additive) is compact if every `K i` is compact. -/
@[tf_aux "X.haar.lem:restricted-product-add-box-compact"]
theorem resProdAdd_box_isCompact (K : ∀ i, AddSubgroup (G i)) [∀ i, CompactSpace (K i)] :
    IsCompact {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} := by
  have h : {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} =
      range (RestrictedProduct.structureMap G (fun i ↦ (K i : Set (G i))) Filter.cofinite) :=
    (RestrictedProduct.range_structureMap _ _).symm
  rw [h]
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

/-- The box `Π K_i ⊆ Πʳ i, [G i, K i]` (additive) has nonempty interior if every `K i` is open. -/
@[tf_aux "X.haar.lem:restricted-product-add-box-interior-nonempty"]
theorem resProdAdd_box_interior_nonempty (K : ∀ i, AddSubgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) :
    (interior {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i}).Nonempty := by
  have ho : IsOpen {x : Πʳ i, [G i, K i] | ∀ i, x i ∈ K i} := RestrictedProduct.isOpen_forall_mem hK
  rw [ho.interior_eq]
  exact ⟨0, fun i ↦ (K i).zero_mem⟩

/-- The box `Π K_i` as a compact set with nonempty interior in `Πʳ i, [G i, K i]` (additive). -/
@[tf_aux "X.haar.def:restricted-product-add-box"]
def resProdAddBox (K : ∀ i, AddSubgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) [∀ i, CompactSpace (K i)] :
    PositiveCompacts (Πʳ i, [G i, K i]) where
  carrier := {x | ∀ i, x i ∈ K i}
  isCompact' := resProdAdd_box_isCompact K
  interior_nonempty' := resProdAdd_box_interior_nonempty K hK


end Add

end GL2TF
