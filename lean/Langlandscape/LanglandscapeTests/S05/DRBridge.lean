/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.DRBridge

/-!
# Tests for `Langlandscape.Comparison.DRBridge` (S05-L2b)

Shape tests for the bridge `degZero_equiv_graphX` and its isometry property.
-/

set_option autoImplicit false

namespace Langlandscape.Comparison.Tests

open Langlandscape.Quat Langlandscape.Brandt

section Bridge

variable (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D)

/-- `def:s05-theta` (`s05-theta`), test: `degZero` and `X(G_s)` coincide as submodules. -/
theorem test_degZero_eq_graphX :
    degZero (d.Utower M p s hN) ℤ = (DRgraphS d M p s hN).X :=
  degZero_eq_graphX d M p s hN

/-- `def:s05-theta` (`s05-theta`), test: the bridge is the identity on underlying chains. -/
theorem test_degZero_equiv_graphX_apply (x : degZero (d.Utower M p s hN) ℤ) :
    (((degZero_equiv_graphX d M p s hN x : (DRgraphS d M p s hN).X)) :
      (DRgraphS d M p s hN).E →₀ ℤ) = (x : ZX (d.Utower M p s hN) ℤ) :=
  degZero_equiv_graphX_apply d M p s hN x

/-- `def:s05-theta` (`s05-theta`), test: the bridge is an isometry. -/
theorem test_degZero_equiv_graphX_isometry (x y : degZero (d.Utower M p s hN) ℤ) :
    Langlandscape.Graph.wPairing (DRgraphS d M p s hN).w
        (degZero_equiv_graphX d M p s hN x : (DRgraphS d M p s hN).E →₀ ℤ)
        (degZero_equiv_graphX d M p s hN y : (DRgraphS d M p s hN).E →₀ ℤ) =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ) (y : ZX (d.Utower M p s hN) ℤ) :=
  degZero_equiv_graphX_isometry d M p s hN x y

/-- `def:s05-theta` (`s05-theta`), test: the bridge is a bijection (round trip). -/
theorem test_degZero_equiv_graphX_symm (x : degZero (d.Utower M p s hN) ℤ) :
    (degZero_equiv_graphX d M p s hN).symm (degZero_equiv_graphX d M p s hN x) = x :=
  (degZero_equiv_graphX d M p s hN).symm_apply_apply x

end Bridge

end Langlandscape.Comparison.Tests
