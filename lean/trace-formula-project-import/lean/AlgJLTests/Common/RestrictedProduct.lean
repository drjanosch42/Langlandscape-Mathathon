import AlgJL.Common.RestrictedProduct

/-!
# Tests for `GL2TF.Common.RestrictedProduct`

Unfolding tests for the tagged definitions (M3 W1a, statement level). The non-vacuity test of D13 (a box with one
non-normalized factor) arrives with the proofs (W3a).
-/

open Filter Set MeasureTheory Measure
open scoped RestrictedProduct

namespace GL2TFTests

/-- The σ-algebra of a restricted product is the Borel σ-algebra. -/
theorem resProd_measurableSpace_eq_borel {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (A : (i : ι) → Set (X i)) (𝓕 : Filter ι) :
    GL2TF.resProd_measurableSpace X A 𝓕 = borel _ :=
  rfl

/-- The carrier of the box `Π K_i`. -/
theorem resProdBox_coe {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (K : ∀ i, Subgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) [∀ i, CompactSpace (K i)] :
    (GL2TF.resProdBox K hK : Set (Πʳ i, [G i, K i])) = {x | ∀ i, x i ∈ K i} :=
  rfl

/-- The carrier of the additive box `Π K_i`. -/
theorem resProdAddBox_coe {ι : Type*} {G : ι → Type*} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    (K : ∀ i, AddSubgroup (G i)) (hK : ∀ i, IsOpen (K i : Set (G i))) [∀ i, CompactSpace (K i)] :
    (GL2TF.resProdAddBox K hK : Set (Πʳ i, [G i, K i])) = {x | ∀ i, x i ∈ K i} :=
  rfl

end GL2TFTests
