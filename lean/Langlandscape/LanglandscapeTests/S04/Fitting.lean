/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.Fitting

/-! Non-vacuity tests for `Langlandscape.Ordinary.Fitting` (S04-L2): a `2 × 2` matrix over `ZMod 25`. -/

@[expose] public section

set_option autoImplicit false

namespace LanglandscapeTests.S04.Fitting

open Langlandscape.Ordinary

/-- `def:s04-e` (`s04-e`), test data: `diag(1, 5)` acting on `(ZMod (5 ^ 2)) ^ 2`. -/
noncomputable def T : Module.End (ZMod (5 ^ 2)) (Fin 2 → ZMod (5 ^ 2)) :=
  Matrix.toLin' !![(1 : ZMod (5 ^ 2)), 0; 0, 5]

/-- `def:s04-e` (`s04-e`), test: the ordinary decomposition exists for the `2 × 2` example over `ZMod 25`. -/
theorem test_hasOrdDecomp : HasOrdDecomp ((5 : ℕ) : ZMod (5 ^ 2)) T :=
  hasOrdDecomp_zmodPow 5 2 T

/-- `def:s04-e` (`s04-e`), test: the projector of the example is a positive power of `T`. -/
theorem test_ordProj_pow : ∃ n : ℕ, 0 < n ∧ ordProj ((5 : ℕ) : ZMod (5 ^ 2)) T test_hasOrdDecomp = T ^ n :=
  ordProj_eq_pow_zmodPow 5 2 T

/-- `def:s04-e` (`s04-e`), test: the projector of the example is idempotent. -/
theorem test_ordProj_idem :
    ordProj ((5 : ℕ) : ZMod (5 ^ 2)) T test_hasOrdDecomp * ordProj ((5 : ℕ) : ZMod (5 ^ 2)) T test_hasOrdDecomp =
      ordProj ((5 : ℕ) : ZMod (5 ^ 2)) T test_hasOrdDecomp :=
  ordProj_idem test_hasOrdDecomp

end LanglandscapeTests.S04.Fitting
