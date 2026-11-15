/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.H1

/-!
# Weighted graphs — S03-L1

Weighted graphs `E ⇉ V` with weights `w : E → ℕ` (`0 < w e`), the lattice `X(G) = ker ∂`,
the weighted pairing `⟨e, e'⟩_w = w_e δ_{ee'}`, the combinatorial component group
`Φ^comb = coker (X → X^∨)`, and the passage from a bipartite multigraph (`ofBip`, with the sign
sign statement `boundary_ofBip`) and its two-vertex collapse (`collapse2`).

Tex labels: `def:s03-graph`, `def:s03-DR`, `lem:s03-bip`(c).

Status: formalized (Mathlib + stage-02 `Graph.boundary`). Never `open Graph` (clash with
`_root_.Graph`).
-/

namespace Langlandscape.Graph

open Finsupp

/-- A weighted graph (`def:s03-graph`): incidence data `E ⇉ V` with positive integer weights. -/
structure WGraph where
  /-- vertices -/
  V : Type
  /-- edges -/
  E : Type
  /-- source of an edge -/
  src : E → V
  /-- target of an edge -/
  tgt : E → V
  /-- weight of an edge -/
  w : E → ℕ
  /-- weights are positive -/
  hw : ∀ e, 0 < w e

namespace WGraph

variable (G : WGraph) (R : Type*) [CommRing R]

/-- Boundary `∂ e = [tgt e] − [src e]` of the chain complex `R[E] → R[V]` (`def:s03-graph`). -/
noncomputable def boundary : (G.E →₀ R) →ₗ[R] (G.V →₀ R) :=
  Finsupp.linearCombination R fun e => Finsupp.single (G.tgt e) (1 : R) - Finsupp.single (G.src e) 1

variable {G R}

/-- Boundary of a single edge (`def:s03-graph`, `s03-graph`). -/
theorem boundary_single (e : G.E) (r : R) :
    boundary G R (Finsupp.single e r) = Finsupp.single (G.tgt e) r - Finsupp.single (G.src e) r := by
  simp [boundary, Finsupp.linearCombination_single, Finsupp.smul_single, smul_sub]

variable (G)

/-- The lattice `X(G) = H₁(G, ℤ) = ker ∂` (`def:s03-graph`). -/
noncomputable def X : Submodule ℤ (G.E →₀ ℤ) := LinearMap.ker (boundary G ℤ)

end WGraph

/-- Alias (stage-05 name) for `WGraph.X`. -/
noncomputable abbrev X (G : WGraph) : Submodule ℤ (G.E →₀ ℤ) := G.X

/-- Degree-zero chains `R[E]⁰ = ker (sum of coefficients)`. -/
noncomputable def deg0 (E : Type*) (R : Type*) [CommRing R] : Submodule R (E →₀ R) :=
  LinearMap.ker (Finsupp.linearCombination R fun _ : E => (1 : R))

/-- The weighted pairing `⟨x, y⟩_w = Σ_e w_e x_e y_e` on `ℤ[E]` (`def:s03-graph`). -/
noncomputable def wPairing {E : Type*} (w : E → ℕ) :
    (E →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun e =>
    (w e : ℤ) • (Finsupp.lapply e : (E →₀ ℤ) →ₗ[ℤ] ℤ)

/-- The pairing of a basis vector with `y` (`def:s03-graph`, `s03-graph`). -/
theorem wPairing_single {E : Type*} (w : E → ℕ) (e : E) (a : ℤ) (y : E →₀ ℤ) :
    wPairing w (Finsupp.single e a) y = a * ((w e : ℤ) * y e) := by
  simp [wPairing, Finsupp.linearCombination_single, smul_eq_mul]

/-- The map `X → X^∨`, `x ↦ ⟨x, ·⟩_w`, for a sublattice `X` of `ℤ[E]`. -/
noncomputable def wDualMap {E : Type*} (w : E → ℕ) (X : Submodule ℤ (E →₀ ℤ)) :
    X →ₗ[ℤ] Module.Dual ℤ X :=
  LinearMap.compl₁₂ (wPairing w) X.subtype X.subtype

/-- The combinatorial component group `Φ^comb = coker (X → Hom(X, ℤ))`
(`def:s03-graph`). -/
abbrev phiComb {E : Type*} (w : E → ℕ) (X : Submodule ℤ (E →₀ ℤ)) :=
  Module.Dual ℤ X ⧸ LinearMap.range (wDualMap w X)

/-- `Φ^comb(G)` of a weighted graph (`def:s03-graph`). -/
abbrev WGraph.PhiComb (G : WGraph) := phiComb G.w G.X

/-- Alias (stage-04 export name, plan §0.2.7 and §4) for `WGraph.PhiComb`: `Φ^comb(G)` of a weighted graph
(`def:s03-graph`). Same pattern as the alias `Graph.X`. -/
abbrev PhiComb (G : WGraph) := G.PhiComb

/-- A bipartite multigraph as a weighted graph on `V₀ ⊕ V₁` with all weights `1`,
edges oriented `0 → 1` (`lem:s03-bip`). -/
@[reducible] def ofBip (G : BipMultigraph) : WGraph where
  V := G.V0 ⊕ G.V1
  E := G.E
  src e := Sum.inl (G.s0 e)
  tgt e := Sum.inr (G.s1 e)
  w _ := 1
  hw _ := Nat.one_pos

/-- The two-vertex collapse `G → G^{(2)}`: same edges, vertices `false` (type 0) and `true`
(type 1), all weights `1` (`lem:s03-bip`(c)). -/
@[reducible] def collapse2 (G : BipMultigraph) : WGraph where
  V := Bool
  E := G.E
  src _ := false
  tgt _ := true
  w _ := 1
  hw _ := Nat.one_pos

/-- Sign convention (C1): the boundary of `ofBip G`, transported along
`R[V₀ ⊕ V₁] ≃ R[V₀] × R[V₁]`, is stage 02's `boundary = (−s₀*, s₁*)`
(`lem:s03-bip`, `s03-bip`). -/
theorem boundary_ofBip (G : BipMultigraph) (R : Type*) [CommRing R] :
    (Finsupp.sumFinsuppLEquivProdFinsupp R).toLinearMap ∘ₗ WGraph.boundary (ofBip G) R =
      boundary G R := by
  refine Finsupp.lhom_ext fun e r => ?_
  rw [LinearMap.comp_apply, WGraph.boundary_single, boundary_single]
  refine Prod.ext ?_ ?_
  · refine Finsupp.ext fun x => ?_
    simp [ofBip, Finsupp.single_apply_left (Sum.inl_injective (α := G.V0) (β := G.V1))]
  · refine Finsupp.ext fun x => ?_
    simp [ofBip, Finsupp.single_apply_left (Sum.inr_injective (α := G.V0) (β := G.V1))]

/-- Pointwise form of `boundary_ofBip` (`lem:s03-bip`, `s03-bip`). -/
theorem boundary_ofBip_apply (G : BipMultigraph) (R : Type*) [CommRing R] (c : G.E →₀ R) :
    Finsupp.sumFinsuppLEquivProdFinsupp R (WGraph.boundary (ofBip G) R c) = boundary G R c :=
  congrArg (fun f => f c) (boundary_ofBip G R)

end Langlandscape.Graph
