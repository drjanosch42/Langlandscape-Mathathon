/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Coset
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Hypothesis `BTtree`: the coset model is the `(q+1)`-regular tree (S02-L5b)

`mathematics/chapters/s02/1-tree.tex`: `lem:s02-tree`(a), `if:s02-tree`.
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

`Tree.graph q` is the simple graph on `Vert q = GL₂(ℚ_q) ⧸ (Z · GL₂(ℤ_q))` of S02-L1 (`v ~ w` iff some edge
`e : EdgeO q` has `{o e, t e} = {v, w}`). The statement is: it is a tree, and every vertex has `q + 1` neighbours.

Used only by `Tree.BGConnected_of_surj` and `Tree.BGConnected_of_SA_HS` (the step (i) ⇒ (iii) of `prop:s02-BG`);
all other results of `Tree/QuotientCore.lean` are tree-free.

Status: *cited* (Serre, *Trees*, Ch. II.1.1, Thm. 1; Ludwig–Merten `BTtree`); not formalized
(discharge plan: port of the Ludwig–Merten formalization, v4.19 → v4.35, post-hackathon).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- `lem:s02-tree`(a), `if:s02-tree`: the coset-model graph `Tree.graph q` is a tree in which every vertex has
exactly `q + 1` neighbours (the Bruhat–Tits tree of `PGL₂(ℚ_q)`). Source: Serre, *Trees*, Ch. II.1.1, Thm. 1;
Ludwig–Merten `BTtree`. Only connectedness is consumed downstream (the `q + 1` regularity is not used). Cited; discharge plan: port of
L–M, post-hackathon. -/
def BTtree (q : ℕ) [Fact q.Prime] : Prop :=
  (Tree.graph q).IsTree ∧ ∀ v : Tree.Vert q, Nat.card ((Tree.graph q).neighborSet v) = q + 1

end Langlandscape.Hyp
