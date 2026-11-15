/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.PadicDecomp

/-! Non-vacuity tests for `Langlandscape.Ordinary.PadicDecomp` (S04-L3): the f.g. `ℤ_[p]` ordinary decomposition. -/

@[expose] public section

set_option autoImplicit false

namespace LanglandscapeTests.S04.PadicDecomp

open Langlandscape.Ordinary

/-- `def:s04-e` (`s04-e`), test: `T = p` on `ℤ_[p]` has an ordinary decomposition (here `ordPart T = ⊥`). -/
theorem test_hasOrdDecomp_smul_p (p : ℕ) [Fact p.Prime] :
    HasOrdDecomp (p : ℤ_[p]) ((p : ℤ_[p]) • (LinearMap.id : Module.End ℤ_[p] ℤ_[p])) :=
  hasOrdDecomp_padic _

/-- `def:s04-e` (`s04-e`), test: a `2 × 2` matrix `diag(1, p)` on `ℤ_[p] ^ 2` has an ordinary decomposition. -/
theorem test_hasOrdDecomp_diag (p : ℕ) [Fact p.Prime] :
    HasOrdDecomp (p : ℤ_[p]) (Matrix.toLin' !![(1 : ℤ_[p]), 0; 0, (p : ℤ_[p])]) :=
  hasOrdDecomp_padic _

/-- `def:s04-e` (`s04-e`), test: `Hyp.PadicOrdDecomp 2` holds (a concrete instance of the discharged hypothesis). -/
theorem test_padicOrdDecomp_two : Langlandscape.Hyp.PadicOrdDecomp 2 :=
  padicOrdDecomp_holds 2

end LanglandscapeTests.S04.PadicDecomp
