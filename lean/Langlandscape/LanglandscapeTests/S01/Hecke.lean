/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Hecke

/-! Non-vacuity tests for `Langlandscape.Brandt.Hecke` (S01-L11a). -/

namespace LanglandscapeTests.S01.Hecke

open Langlandscape.Quat Langlandscape.Brandt

/-- `U_ℓ` and `T_ℓ` are the same double-coset operator. -/
example (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D) (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0) :
    Ul d U ℓ hℓ ℤ hfin = Tl d U ℓ hℓ ℤ hfin := rfl

/-- `U_0(N)` splits at every prime dividing `N`. -/
example (d : DefiniteData) (N p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (hN : N.Coprime d.D)
    (hpN : p ∈ N.primeFactors) : SplitAt (d.U0 N hN) p := splitAt_U0 hpN hp

/-- `Ô^×` splits at every split prime. -/
example (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) : SplitAt d.Ohat p :=
  splitAt_of_isInvariantAt (hp := hp) (isInvariantAt_Ohat (hp := hp)) fun _ hu => localComponent_mem_GL2Zl (hℓ := hp) hu

end LanglandscapeTests.S01.Hecke
