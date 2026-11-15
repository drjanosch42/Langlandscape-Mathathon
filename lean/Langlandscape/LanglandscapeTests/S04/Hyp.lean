/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.HidaControl
import Langlandscape.Hyp.HsiehCR

/-! Non-vacuity test for `Hyp.HsiehCR` (S04-L14a): toy residual data. `HidaControl` has no instance (schematic). -/

set_option autoImplicit false

namespace LanglandscapeTests.S04.Hyp

open Langlandscape.Hyp

/-- `hyp:s04-CR` (`s04-CR`), non-vacuity: `p = 5`, `D = 3` (the only prime divisor `3` is not `≡ 1 mod 5`), trivial group,
group index `Bool`, `chiPlus = 0`, `chiMinus = 1`. -/
theorem hsiehCR_toy :
    HsiehCR 5 3 Bool True (fun _ => 0) (fun _ => 1) (fun _ => False) := by
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    have h01 : (0 : ZMod 5) = 1 := congrFun h true
    exact absurd h01 (by decide)
  · intro ℓ hℓ hd hmod
    have h3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd
    subst h3
    exact absurd hmod (by decide)

end LanglandscapeTests.S04.Hyp
