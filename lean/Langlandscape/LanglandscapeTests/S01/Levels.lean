/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Levels
import LanglandscapeTests.S01.LocalComponent

/-! Non-vacuity checks for S01-L3c (`Quat/Levels.lean`). -/

open Langlandscape.Quat

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `gcd(3, 2) = 1` (test data, `s01-levels`). -/
lemma cop3 : (3 : ℕ).Coprime hurwitzData.D := by decide
/-- `gcd(15, 2) = 1` (test data, `s01-levels`). -/
lemma cop15 : (15 : ℕ).Coprime hurwitzData.D := by decide

/-- `1 ∈ U_1(3)`. -/
example : (1 : (BHat (-1) (-1))ˣ) ∈ hurwitzData.U1 3 cop3 := Subgroup.one_mem _

/-- The chain `U_1(15) ≤ U_1(3) ≤ U_0(3) ≤ Ô^×`. -/
example : hurwitzData.U1 15 cop15 ≤ hurwitzData.Ohat :=
  (hurwitzData.U1_anti (by norm_num) (by norm_num) cop3 cop15).trans
    ((hurwitzData.U1_le_U0 3 cop3).trans (hurwitzData.U0_le_units 3 cop3))

/-- Level `1` is everything. -/
example : hurwitzData.U0 1 (Nat.coprime_one_left _) = hurwitzData.Ohat :=
  hurwitzData.U0_one

/-- Membership unfolds to the local condition at `3` (`3 ∈ primeFactors 3`). -/
example (u : (BHat (-1) (-1))ˣ) (hu : u ∈ hurwitzData.U1 3 cop3) :
    localComponent hurwitzData 3 three_ndvd u ∈ Langlandscape.Local.K1 3 ((3 : ℕ).factorization 3) :=
  (hurwitzData.mem_U1_iff.1 hu).2 3 (Nat.mem_primeFactors.2 ⟨Nat.prime_three, dvd_rfl, by norm_num⟩) three_ndvd
