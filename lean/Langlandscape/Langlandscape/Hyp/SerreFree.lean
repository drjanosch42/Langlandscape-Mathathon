/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.TwoTerm
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Hypothesis `SerreFree`: `Γ_U` is free when all stabilisers are trivial (S02-L3)

`mathematics/chapters/s02/3-cohomology.tex`, `prop:s02-free`(a).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance).
Registered in `HYPOTHESES.md` (used by: — (statement only)).

Status: *cited* (Serre, *Trees*, Ch. I §3.3, Thm. 4 and 4'; Ch. II §1.5, Thm. 4; Bass, *Covering theory for graphs of groups*, 3.6); not formalized.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `prop:s02-free`(a): if `BG(U, q)` is connected and every `Γ_x(U)` is trivial, then `Γ_U` is free of finite rank
`(q - 1) |X(U)| + 1`. The hypothesis `hconn` is carried as an argument (as in the tex statement) although it
does not occur in the body. Note that `hfree` at level `U` implies trivial stabilisers at `U_0(q)U`, since
`Γ_x(U_0(q)U) ≤ Γ_x(U)`. Cited; not formalized. -/
def SerreFree (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : Tree.IsQLevel d q hq U) (hconn : Tree.BGConnected d q hq U hU)
    (hfree : ∀ x : (BHat d.a d.b)ˣ, Gam U x = ⊥) : Prop :=
  ∃ (ι : Type) (_ : Finite ι), Nat.card ι = (q - 1) * Nat.card (XB U) + 1 ∧
    Nonempty (FreeGroupBasis ι (Tree.GammaU d q hq U))

end Langlandscape.Hyp
