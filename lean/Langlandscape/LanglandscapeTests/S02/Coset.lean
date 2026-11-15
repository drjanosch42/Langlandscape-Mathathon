/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Coset

/-!
# Tests for S02 Coset — S02-L1 (stub; owner fills it)

Tex labels: def:s02-tree.
-/

/-!
Non-vacuity examples for `q = 2`: the base edge `e₀` runs from `v₀` to `v₁`, `v₁` has type `1`, and
`v₀ ~ v₁` in the tree graph.
-/

open Langlandscape.Tree

/-- `def:s02-tree` (`s02-tree`): `o e₀ = v₀` at `q = 2`. -/
example : oO 2 (e0 2) = v0 2 := oO_e0 2

/-- `def:s02-tree` (`s02-tree`): `t e₀ = v₁` at `q = 2`. -/
example : tO 2 (e0 2) = v1 2 := tO_e0 2

/-- `def:s02-tree` (`s02-tree`): `τ(v₁) = 1` at `q = 2`. -/
example : vtype 2 (v1 2) = 1 := vtype_v1 2

/-- `def:s02-tree` (`s02-tree`): `v₀ ~ v₁` in the tree at `q = 2`. -/
example : (graph 2).Adj (v0 2) (v1 2) := graph_adj_v0_v1 2

/-- `def:s02-tree` (`s02-tree`): `τ(v₀) = 0` at `q = 2`. -/
example : vtype 2 (v0 2) = 0 := vtype_v0 2

/-- Index `[GL₂(ℤ_2) : Iw_2] = 3` (`s02-tree`; input to the cited `lem:s02-tree`(a), the
identification with the neighbours of `v₀` is not formalized). -/
example : (Langlandscape.Local.Iw 2).relIndex (Langlandscape.Local.GL2Zl 2) = 3 := relIndex_Iw 2
