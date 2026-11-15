/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelIndex

/-! Non-vacuity checks for S01-L4a. -/

open Langlandscape.Quat

example (a b : ℤ) (O : GL2TF.Quat.QOrder a b) (N : ℕ) [NeZero N] (φ : GL2TF.Quat.LevelStructure O N) :
    (((U1Psi O φ).relIndex (GL2TF.Quat.orderCompletionUnits O) : ℕ) : ℚ) =
      GL2TF.Explicit.dedekindPsi N * (Nat.totient N : ℚ) := relIndex_U1Psi O φ
example : (borel1 5).relIndex (GL2TF.borel (ZMod 5)) = 4 := by
  rw [index_borel1_borel]; decide +kernel
