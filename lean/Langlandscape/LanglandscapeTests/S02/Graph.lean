/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.H1
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for S02 Graph — S02-L8

Tex labels: `def:s02-indef`, `prop:s02-free`.
-/

namespace LanglandscapeTests.S02.Graph

open Langlandscape.Graph (BipMultigraph H1 finrank_H1_of_connected)

/-- The shape `B₂` at `q = 7`: one vertex of each type, two edges. -/
abbrev B2 : BipMultigraph where
  V0 := Unit
  V1 := Unit
  E := Bool
  s0 := fun _ => ()
  s1 := fun _ => ()

/-- `B₂` is connected (`def:s02-indef`, `s02-indef`). -/
theorem B2_connected : B2.Connected := by
  show B2.toSimpleGraph.Connected
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl (), ?_⟩
  rintro (⟨⟩ | ⟨⟩)
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((B2.adj_inl_inr_iff () ()).2 ⟨true, rfl, rfl⟩)

/-- `rank H₁(B₂) = 1` over any commutative domain (`prop:s02-free`, `s02-free`). -/
theorem B2_finrank (R : Type) [CommRing R] [IsDomain R] : Module.finrank R (H1 B2 R) = 1 := by
  have h := finrank_H1_of_connected (G := B2) (R := R) B2_connected
  have h0 : Nat.card B2.V0 = 1 := by
    show Nat.card Unit = 1
    simp
  have h1 : Nat.card B2.V1 = 1 := by
    show Nat.card Unit = 1
    simp
  have h2 : Nat.card B2.E = 2 := by
    show Nat.card Bool = 2
    simp
  omega

/-- `rank H₁(B₂) = 1` over `ℚ` (`prop:s02-free`, `s02-free`). -/
theorem B2_finrank_rat : Module.finrank ℚ (H1 B2 ℚ) = 1 := B2_finrank ℚ

/-- `rank H₁(B₂) = 1` over `ℤ` (`prop:s02-free`, `s02-free`). -/
theorem B2_finrank_int : Module.finrank ℤ (H1 B2 ℤ) = 1 := B2_finrank ℤ

/-- `rank H₁(B₂) = 1` over `ZMod 5` (`prop:s02-free`, `s02-free`). -/
theorem B2_finrank_zmod5 : Module.finrank (ZMod 5) (H1 B2 (ZMod 5)) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact B2_finrank (ZMod 5)

/-- A 2+2-vertex path-shaped example with three edges. -/
abbrev P22 : BipMultigraph where
  V0 := Fin 2
  V1 := Fin 2
  E := Fin 3
  s0 := ![0, 0, 1]
  s1 := ![0, 1, 1]

/-- Connectivity of the 2+2 example, by an explicit walk (`def:s02-indef`, `s02-indef`). -/
theorem P22_connected : P22.Connected := by
  show P22.toSimpleGraph.Connected
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have a0 : P22.toSimpleGraph.Adj (Sum.inl 0) (Sum.inr 0) :=
    (P22.adj_inl_inr_iff 0 0).2 ⟨0, by decide, by decide⟩
  have a1 : P22.toSimpleGraph.Adj (Sum.inl 0) (Sum.inr 1) :=
    (P22.adj_inl_inr_iff 0 1).2 ⟨1, by decide, by decide⟩
  have a2 : P22.toSimpleGraph.Adj (Sum.inl 1) (Sum.inr 1) :=
    (P22.adj_inl_inr_iff 1 1).2 ⟨2, by decide, by decide⟩
  refine ⟨Sum.inl 0, ?_⟩
  rintro (x | y)
  · fin_cases x
    · exact SimpleGraph.Reachable.refl _
    · exact a1.reachable.trans a2.symm.reachable
  · fin_cases y
    · exact a0.reachable
    · exact a1.reachable

end LanglandscapeTests.S02.Graph
