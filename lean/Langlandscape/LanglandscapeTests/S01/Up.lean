/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Up
import Langlandscape.Quat.LevelFinite
import LanglandscapeTests.S01.LocalComponent

/-! Non-vacuity checks for S01-L10 (`Brandt/Up.lean`), Hurwitz data `D = 2`, `M = 1`, `p = 3`. -/

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

/-- `gcd(1 · 3, 2) = 1` (test data, `s01-NUp`). -/
lemma cop13 : (1 * 3 ^ 1).Coprime hurwitzData.D := by decide
/-- `gcd(1 · 3², 2) = 1` (test data, `s01-NUp`). -/
lemma cop19 : (1 * 3 ^ (1 + 1)).Coprime hurwitzData.D := by decide
/-- `3 ∤ 1` (test data, `s01-NUp`). -/
lemma three_ndvd_one : ¬ 3 ∣ 1 := by decide

/-- `U_3` at level `U_1(3)` is the sum over the three cosets `ϖ_j U`, `j = 0, 1, 2`. -/
example (f : ZXdual (hurwitzData.Utower 1 3 1 cop13) ℤ) (x : (GL2TF.Quat.BHat hurwitzData.a hurwitzData.b)ˣ) :
    Up hurwitzData 1 3 1 cop13 three_ndvd one_ne_zero three_ndvd_one le_rfl ℤ f
        (DoubleCoset.mk (globalUnits _ _) _ x) =
      ∑ j : Fin 3, f (DoubleCoset.mk (globalUnits _ _) (hurwitzData.Utower 1 3 1 cop13)
        (x * localEmbedGL hurwitzData 3 three_ndvd (varpi 3 j))) :=
  Up_apply one_ne_zero three_ndvd_one le_rfl f x

/-- `U_3 ∘ π^* = π^* ∘ U_3` from level `U_1(3)` to `U_1(9)`. -/
example :
    Up hurwitzData 1 3 (1 + 1) cop19 three_ndvd one_ne_zero three_ndvd_one (Nat.le_add_left 1 1) ℚ ∘ₗ
        towerPull hurwitzData 1 3 1 cop13 cop19 ℚ =
      towerPull hurwitzData 1 3 1 cop13 cop19 ℚ ∘ₗ
        Up hurwitzData 1 3 1 cop13 three_ndvd one_ne_zero three_ndvd_one le_rfl ℚ :=
  Up_comm_pull one_ne_zero three_ndvd_one le_rfl

/-- `π_* ∘ U_3 = U_3 ∘ π_*` from level `U_1(9)` to `U_1(3)` (finiteness of the class sets from the instances
`DefiniteData.finite_XB_Utower`). -/
example :
    towerPush hurwitzData 1 3 1 cop13 cop19 ℤ ∘ₗ
        UpHom hurwitzData 1 3 (1 + 1) cop19 three_ndvd one_ne_zero three_ndvd_one (Nat.le_add_left 1 1) ℤ =
      UpHom hurwitzData 1 3 1 cop13 three_ndvd one_ne_zero three_ndvd_one le_rfl ℤ ∘ₗ
        towerPush hurwitzData 1 3 1 cop13 cop19 ℤ :=
  Up_comm_push one_ne_zero three_ndvd_one le_rfl
