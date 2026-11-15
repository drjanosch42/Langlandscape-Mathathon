/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted

/-!
# Tests for `Graph/Weighted.lean` — S03-L1
-/

namespace LanglandscapeTests.S03.Weighted



/-- A two-vertex, one-edge weighted graph (`def:s03-graph`, `s03-graph`). -/
def G1 : Langlandscape.Graph.WGraph where
  V := Bool
  E := Unit
  src _ := false
  tgt _ := true
  w _ := 2
  hw _ := by decide

/-- The alias `Langlandscape.Graph.X` agrees with `WGraph.X` (`def:s03-graph`, `s03-graph`). -/
theorem X_alias : Langlandscape.Graph.X G1 = G1.X := rfl

/-- The alias `Langlandscape.Graph.PhiComb` agrees with `WGraph.PhiComb` (`def:s03-graph`, `s03-graph`;
audit S03-L12, R3). -/
theorem PhiComb_alias : Langlandscape.Graph.PhiComb G1 = G1.PhiComb := rfl

/-- Boundary of the edge of `G1` (`def:s03-graph`, `s03-graph`). -/
theorem G1_boundary (r : ℤ) :
    Langlandscape.Graph.WGraph.boundary G1 ℤ (Finsupp.single () r) =
      Finsupp.single true r - Finsupp.single false r :=
  Langlandscape.Graph.WGraph.boundary_single (G := G1) () r

/-- `Φ^comb` of `G1` unfolds to the generic definition (`def:s03-graph`, `s03-graph`). -/
example : G1.PhiComb = Langlandscape.Graph.phiComb G1.w G1.X := rfl

/-- The sign lemma applies to any bipartite multigraph (`lem:s03-bip`, `s03-bip`). -/
theorem sign_lemma (B : Langlandscape.Graph.BipMultigraph) (c : B.E →₀ ℤ) :
    Finsupp.sumFinsuppLEquivProdFinsupp ℤ
        (Langlandscape.Graph.WGraph.boundary (Langlandscape.Graph.ofBip B) ℤ c) = Langlandscape.Graph.boundary B ℤ c :=
  Langlandscape.Graph.boundary_ofBip_apply B ℤ c

end LanglandscapeTests.S03.Weighted
