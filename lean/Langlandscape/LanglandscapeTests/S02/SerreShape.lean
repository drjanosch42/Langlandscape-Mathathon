/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.SerreCoh
import Langlandscape.Hyp.SerreFree

/-!
# Tests for S02 SerreShape (S02-L3)

Tex labels: prop:s02-coh, prop:s02-free. Both hypothesis shapes typecheck for a variable level.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `prop:s02-coh` (`s02-coh`): `Hyp.SerreCoh` is a `Prop` for a variable level. -/
example (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : Tree.IsQLevel d q hq U) (hconn : Tree.BGConnected d q hq U hU) (R : Type) [CommRing R] :
    Prop := SerreCoh d q hq U hU hconn R

/-- `prop:s02-free` (`s02-free`): `Hyp.SerreFree` is a `Prop` for a variable level. -/
example (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : Tree.IsQLevel d q hq U) (hconn : Tree.BGConnected d q hq U hU)
    (hfree : ∀ x : (BHat d.a d.b)ˣ, Gam U x = ⊥) : Prop := SerreFree d q hq U hU hconn hfree

end Langlandscape.Hyp
