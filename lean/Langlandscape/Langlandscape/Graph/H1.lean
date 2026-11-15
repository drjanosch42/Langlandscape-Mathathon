/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Bipartite
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Finiteness.Prod

/-!
# First homology of bipartite multigraphs — S02-L8

`boundary`, `H1 = ker boundary`, the augmentation `aug`, and for connected graphs
`range boundary = ker aug` (any commutative ring) and the rank formula
`rank H1 + |V₀| + |V₁| = |E| + 1` (commutative domains, covering `ℤ` and fields).

Tex labels: `def:s02-indef`, `prop:s02-free`(b).

Status: formalized (Mathlib only).
-/

namespace Langlandscape.Graph

open Finsupp

variable (G : BipMultigraph) (R : Type*) [CommRing R]

/-- The boundary map `e ↦ (−[s0 e], [s1 e])` (`def:s02-indef`). -/
noncomputable def boundary : (G.E →₀ R) →ₗ[R] (G.V0 →₀ R) × (G.V1 →₀ R) :=
  Finsupp.linearCombination R fun e => (-(Finsupp.single (G.s0 e) (1 : R)), Finsupp.single (G.s1 e) (1 : R))

/-- First homology `H_1(G, R) = ker ∂` (`def:s02-indef`). -/
noncomputable def H1 : Submodule R (G.E →₀ R) := LinearMap.ker (boundary G R)

/-- Augmentation: the sum of all coefficients. -/
noncomputable def aug : (G.V0 →₀ R) × (G.V1 →₀ R) →ₗ[R] R :=
  (Finsupp.linearCombination R fun _ : G.V0 => (1 : R)).coprod
    (Finsupp.linearCombination R fun _ : G.V1 => (1 : R))

/-- The vertex basis vectors in the chain module. -/
noncomputable def vertexVec : G.V0 ⊕ G.V1 → (G.V0 →₀ R) × (G.V1 →₀ R) :=
  Sum.elim (fun x => (Finsupp.single x (1 : R), 0)) (fun y => (0, Finsupp.single y (1 : R)))

variable {G R}

/-- Boundary of a single edge (`def:s02-indef`, `s02-indef`). -/
theorem boundary_single (e : G.E) (r : R) :
    boundary G R (Finsupp.single e r) =
      (-(Finsupp.single (G.s0 e) r), Finsupp.single (G.s1 e) r) := by
  simp [boundary, Finsupp.linearCombination_single, Finsupp.smul_single]

/-- Augmentation of a vertex vector (`def:s02-indef`, `s02-indef`). -/
theorem aug_vertexVec (u : G.V0 ⊕ G.V1) : aug G R (vertexVec G R u) = 1 := by
  cases u <;> simp [aug, vertexVec, Finsupp.linearCombination_single]

/-- The augmentation kills boundaries (`def:s02-indef`, `s02-indef`). -/
theorem aug_boundary_single (e : G.E) (r : R) :
    aug G R (boundary G R (Finsupp.single e r)) = 0 := by
  rw [boundary_single]
  simp [aug, Finsupp.linearCombination_single]

/-- Boundary of the unit edge as a difference of vertex vectors (`def:s02-indef`, `s02-indef`). -/
theorem vertexVec_sub_eq_neg_boundary (e : G.E) :
    vertexVec G R (Sum.inl (G.s0 e)) - vertexVec G R (Sum.inr (G.s1 e)) =
      -boundary G R (Finsupp.single e 1) := by
  rw [boundary_single]
  refine Prod.ext ?_ ?_ <;> simp [vertexVec]

/-- Adjacent vertices differ by an element of the range of the boundary
(`def:s02-indef`, `s02-indef`). -/
theorem vertexVec_sub_mem_range_of_adj {u v : G.V0 ⊕ G.V1} (h : G.toSimpleGraph.Adj u v) :
    vertexVec G R u - vertexVec G R v ∈ LinearMap.range (boundary G R) := by
  obtain ⟨_, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := h
  · rw [vertexVec_sub_eq_neg_boundary]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self _ _)
  · rw [← neg_sub, vertexVec_sub_eq_neg_boundary, neg_neg]
    exact LinearMap.mem_range_self _ _

/-- Reachable vertices differ by an element of the range of the boundary
(`def:s02-indef`, `s02-indef`). -/
theorem vertexVec_sub_mem_range_of_reachable {u v : G.V0 ⊕ G.V1}
    (h : G.toSimpleGraph.Reachable u v) :
    vertexVec G R u - vertexVec G R v ∈ LinearMap.range (boundary G R) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => simp
  | tail _ ha ih =>
    have := Submodule.add_mem _ ih (vertexVec_sub_mem_range_of_adj (R := R) ha)
    simpa using this

/-- For connected `G`, over any commutative ring, the image of the boundary is the kernel of the
augmentation (`prop:s02-free`(b), `s02-free`). -/
theorem range_boundary_of_connected [Finite G.V0] [Finite G.V1] (hc : G.Connected) :
    LinearMap.range (boundary G R) = LinearMap.ker (aug G R) := by
  have hc' : G.toSimpleGraph.Connected := hc
  obtain ⟨u0⟩ := hc'.nonempty
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    have h : (aug G R).comp (boundary G R) = 0 :=
      Finsupp.lhom_ext fun e r => by simpa using aug_boundary_single e r
    exact LinearMap.congr_fun h c
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    let L : (G.V0 →₀ R) × (G.V1 →₀ R) →ₗ[R] (G.V0 →₀ R) × (G.V1 →₀ R) :=
      LinearMap.id - (aug G R).smulRight (vertexVec G R u0)
    have hLapp : ∀ w, L w = w - aug G R w • vertexVec G R u0 := fun w => by simp [L]
    have hL : ∀ u, L (vertexVec G R u) ∈ LinearMap.range (boundary G R) := by
      intro u
      rw [hLapp, aug_vertexVec, one_smul]
      exact vertexVec_sub_mem_range_of_reachable (hc'.preconnected u u0)
    have h1 : ∀ a : G.V0 →₀ R, L (a, 0) ∈ LinearMap.range (boundary G R) := by
      intro a
      induction a using Finsupp.induction_linear with
      | zero =>
        have h0 : L (0, 0) = 0 := map_zero L
        rw [h0]
        exact Submodule.zero_mem _
      | add f g hf hg =>
        have : ((f + g, (0 : G.V1 →₀ R)) : (G.V0 →₀ R) × (G.V1 →₀ R)) = (f, 0) + (g, 0) := by
          simp
        rw [this, map_add]
        exact Submodule.add_mem _ hf hg
      | single x r =>
        have : ((Finsupp.single x r, (0 : G.V1 →₀ R)) : (G.V0 →₀ R) × (G.V1 →₀ R)) =
            r • vertexVec G R (Sum.inl x) := by
          simp [vertexVec]
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (hL _)
    have h2 : ∀ b : G.V1 →₀ R, L (0, b) ∈ LinearMap.range (boundary G R) := by
      intro b
      induction b using Finsupp.induction_linear with
      | zero =>
        have h0 : L (0, 0) = 0 := map_zero L
        rw [h0]
        exact Submodule.zero_mem _
      | add f g hf hg =>
        have : (((0 : G.V0 →₀ R), f + g) : (G.V0 →₀ R) × (G.V1 →₀ R)) = (0, f) + (0, g) := by
          simp
        rw [this, map_add]
        exact Submodule.add_mem _ hf hg
      | single y r =>
        have : (((0 : G.V0 →₀ R), Finsupp.single y r) : (G.V0 →₀ R) × (G.V1 →₀ R)) =
            r • vertexVec G R (Sum.inr y) := by
          simp [vertexVec]
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (hL _)
    have hz' : L z ∈ LinearMap.range (boundary G R) := by
      have : z = (z.1, 0) + (0, z.2) := by simp
      rw [this, map_add]
      exact Submodule.add_mem _ (h1 _) (h2 _)
    rw [hLapp, hz, zero_smul, sub_zero] at hz'
    exact hz'

/-- Rank formula for connected `G` over a commutative domain (covers `ℤ` and fields):
`rank H₁ + |V₀| + |V₁| = |E| + 1` (`prop:s02-free`(b), `s02-free`). -/
theorem finrank_H1_of_connected [IsDomain R] [Finite G.V0] [Finite G.V1] [Finite G.E]
    (hc : G.Connected) :
    Module.finrank R (H1 G R) + Nat.card G.V0 + Nat.card G.V1 = Nat.card G.E + 1 := by
  have := Fintype.ofFinite G.V0
  have := Fintype.ofFinite G.V1
  have := Fintype.ofFinite G.E
  have hc' : G.toSimpleGraph.Connected := hc
  obtain ⟨u0⟩ := hc'.nonempty
  have hP : Module.finrank R ((G.V0 →₀ R) × (G.V1 →₀ R)) = Nat.card G.V0 + Nat.card G.V1 := by
    rw [Module.finrank_prod, Module.finrank_finsupp_self, Module.finrank_finsupp_self,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hM : Module.finrank R (G.E →₀ R) = Nat.card G.E := by
    rw [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective (aug G R) := fun r =>
    ⟨r • vertexVec G R u0, by rw [map_smul, aug_vertexVec, smul_eq_mul, mul_one]⟩
  have h1 := (LinearMap.ker (aug G R)).finrank_quotient_add_finrank
  have hq : Module.finrank R (((G.V0 →₀ R) × (G.V1 →₀ R)) ⧸ LinearMap.ker (aug G R)) = 1 := by
    rw [(LinearMap.quotKerEquivOfSurjective _ hsurj).finrank_eq]
    exact Module.finrank_self R
  have h2 := (LinearMap.ker (boundary G R)).finrank_quotient_add_finrank
  have hq2 : Module.finrank R ((G.E →₀ R) ⧸ LinearMap.ker (boundary G R)) =
      Module.finrank R (LinearMap.ker (aug G R)) := by
    rw [(LinearMap.quotKerEquivRange _).finrank_eq, range_boundary_of_connected hc]
  show Module.finrank R (LinearMap.ker (boundary G R)) + _ + _ = _
  omega
