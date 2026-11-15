/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Bipartite multigraphs — S02-L8

Finite bipartite multigraphs `E ⇉ V₀ ⊔ V₁` (loops/multi-edges allowed), their underlying
simple graph on `V₀ ⊕ V₁`, and connectivity.

Tex labels: `def:s02-indef`, `prop:s02-free`.

Status: formalized (Mathlib only). Never `open Graph` (clash with `_root_.Graph`).
-/

namespace Langlandscape.Graph

/-- A bipartite multigraph: edge set `E` with source map `s0` to the type-0 vertices and
target map `s1` to the type-1 vertices (`def:s02-indef`). -/
structure BipMultigraph where
  /-- vertices of type 0 -/
  V0 : Type
  /-- vertices of type 1 -/
  V1 : Type
  /-- edges -/
  E : Type
  /-- the type-0 endpoint of an edge -/
  s0 : E → V0
  /-- the type-1 endpoint of an edge -/
  s1 : E → V1

namespace BipMultigraph

variable (G : BipMultigraph)

/-- The underlying simple graph on `V₀ ⊕ V₁`: `inl x ~ inr y` iff some edge joins them. -/
def toSimpleGraph : SimpleGraph (G.V0 ⊕ G.V1) :=
  SimpleGraph.fromRel fun x y => ∃ e, x = Sum.inl (G.s0 e) ∧ y = Sum.inr (G.s1 e)

/-- Connectivity of a bipartite multigraph: connectivity of the underlying simple graph. -/
def Connected : Prop := G.toSimpleGraph.Connected

/-- Adjacency of an `inl`/`inr` pair (`def:s02-indef`, `s02-indef`). -/
theorem adj_inl_inr_iff (x : G.V0) (y : G.V1) :
    G.toSimpleGraph.Adj (Sum.inl x) (Sum.inr y) ↔ ∃ e, G.s0 e = x ∧ G.s1 e = y := by
  constructor
  · rintro ⟨_, ⟨e, h1, h2⟩ | ⟨e, h1, _⟩⟩
    · exact ⟨e, (Sum.inl.inj h1).symm, (Sum.inr.inj h2).symm⟩
    · cases h1
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨Sum.inl_ne_inr, Or.inl ⟨e, rfl, rfl⟩⟩

/-- Adjacency in the underlying simple graph of a finite bipartite multigraph is decidable. -/
instance instDecidableRelAdjToSimpleGraph [Fintype G.V0] [Fintype G.V1] [Fintype G.E] [DecidableEq G.V0]
    [DecidableEq G.V1] : DecidableRel G.toSimpleGraph.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧
    ((∃ e, x = Sum.inl (G.s0 e) ∧ y = Sum.inr (G.s1 e)) ∨
      (∃ e, y = Sum.inl (G.s0 e) ∧ x = Sum.inr (G.s1 e)))))

/-- Connectivity of a finite bipartite multigraph is decidable. -/
instance instDecidableConnected [Fintype G.V0] [Fintype G.V1] [Fintype G.E] [DecidableEq G.V0]
    [DecidableEq G.V1] : Decidable G.Connected :=
  inferInstanceAs (Decidable G.toSimpleGraph.Connected)

end BipMultigraph

end Langlandscape.Graph
