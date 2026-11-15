/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Stab
import LanglandscapeTests.S01.Levels

/-! Non-vacuity checks for S01-L5b (`Quat/Stab.lean`, section `Free`). -/

open Langlandscape.Quat

/-- `gcd(5, 2) = 1` (test data, `s01-stab`). -/
lemma cop5 : (5 : ℕ).Coprime hurwitzData.D := by decide

/-- Hurwitz order, level `U_1(5)`: every stabiliser is trivial (`s01-stab` (b)). -/
example (x : (BHat (-1) (-1))ˣ) : Gam (hurwitzData.U1 5 cop5) x = ⊥ :=
  Gam_eq_bot_of_le_U1 hurwitzData (by norm_num) le_rfl cop5 le_rfl x

/-- Level `U_1(15) ≤ U_1(5)`: stabilisers trivial as well (`s01-stab` (b)). -/
example (x : (BHat (-1) (-1))ˣ) : Gam (hurwitzData.U1 15 cop15) x = ⊥ :=
  Gam_eq_bot_of_le_U1 hurwitzData (by norm_num) le_rfl cop5
    (hurwitzData.U1_anti (by norm_num) (by norm_num) cop5 cop15) x

/-- The tower `U_s = U_1(3 · 5^s)`, `s ≥ 1`, at `p = 5` (`s01-stab` (b), the case used by L5c/L4c). -/
example (s : ℕ) (hs : 1 ≤ s) (h : (3 * 5 ^ s).Coprime hurwitzData.D) (x : (BHat (-1) (-1))ˣ) :
    Gam (hurwitzData.Utower 3 5 s h) x = ⊥ :=
  Gam_eq_bot_of_le_U1 hurwitzData (by norm_num) le_rfl cop5
    (hurwitzData.Utower_le_U1p hs (by norm_num) (by norm_num) h cop5) x
