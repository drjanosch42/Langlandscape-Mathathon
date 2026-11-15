/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelBridge
import LanglandscapeTests.S01.Levels

/-! Non-vacuity checks for S01-L4b (`Quat/LevelBridge.lean`). -/

open Langlandscape.Quat

/-- The bridge at the Hurwitz order, `N = 3` (`s01-levels`). -/
example : hurwitzData.U1 3 cop3 = U1Psi hurwitzData.O.1 (hurwitzData.levelStructureOfIota 3 cop3) :=
  hurwitzData.U1_eq_U1Psi 3 cop3

/-- `U_0(3) = U0Psi` at the Hurwitz order (`s01-levels`). -/
example : hurwitzData.U0 3 cop3 = U0Psi hurwitzData.O.1 (hurwitzData.levelStructureOfIota 3 cop3) :=
  hurwitzData.U0_eq_U0Psi 3 cop3

/-- `[Ô^× : U_1(3)] = ψ(3) φ(3)` at the Hurwitz order (`s01-mass`). -/
example : (((hurwitzData.U1 3 cop3).relIndex hurwitzData.Ohat : ℕ) : ℚ) =
    GL2TF.Explicit.dedekindPsi 3 * (Nat.totient 3 : ℚ) :=
  hurwitzData.relIndex_U1 3 cop3

/-- General form (`s01-levels`). -/
example (d : DefiniteData) (N : ℕ) [NeZero N] (hN : N.Coprime d.D) :
    (((d.U0 N hN).relIndex d.Ohat : ℕ) : ℚ) = GL2TF.Explicit.dedekindPsi N :=
  d.relIndex_U0 N hN
