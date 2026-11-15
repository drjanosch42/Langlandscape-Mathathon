/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalEmbed
import LanglandscapeTests.S01.Levels

/-! Non-vacuity checks for S01-L3d (`Quat/LocalEmbed.lean`), Hurwitz data `D = 2`. -/

open Langlandscape.Quat Langlandscape.Local

/-- `localEmbed` at the ramified prime `2 ∣ D` is defined and has `2`-component `x`. -/
example (x : (QuatAlg ℚ_[2] (-1) (-1))ˣ) : localProjUnits (-1) (-1) 2 (localEmbed (-1) (-1) 2 x) = x :=
  localProjUnits_localEmbed x

/-- `2` is ramified for the Hurwitz data. -/
example : 2 ∣ hurwitzData.D := dvd_refl 2

/-- Local embeddings at `2` and `3` commute. -/
example (x : (QuatAlg ℚ_[2] (-1) (-1))ˣ) (y : (QuatAlg ℚ_[3] (-1) (-1))ˣ) :
    Commute (localEmbed (-1) (-1) 2 x) (localEmbed (-1) (-1) 3 y) :=
  localEmbed_comm (by decide) x y

/-- `localComponent 3 ∘ localEmbedGL 3 = id`. -/
example (g : GL (Fin 2) ℚ_[3]) :
    localComponent hurwitzData 3 three_ndvd (localEmbedGL hurwitzData 3 three_ndvd g) = g :=
  localComponent_localEmbedGL g

/-- `localEmbedGL 3 1 ∈ Ô^×`. -/
example : localEmbedGL hurwitzData 3 three_ndvd 1 ∈ hurwitzData.Ohat :=
  localEmbedGL_mem_Ohat (one_mem _)

/-- Factorisation of `U_1(3)` at `3`. -/
example (u : (BHat hurwitzData.a hurwitzData.b)ˣ) :
    u ∈ hurwitzData.U1 3 cop3 ↔
      u * localEmbedGL hurwitzData 3 three_ndvd (localComponent hurwitzData 3 three_ndvd u)⁻¹ ∈
          hurwitzData.U1 3 cop3 ∧
        localComponent hurwitzData 3 three_ndvd u ∈ K1 3 ((3 : ℕ).factorization 3) :=
  mem_U1_iff_factor_at (Nat.mem_primeFactors.2 ⟨Nat.prime_three, dvd_refl 3, by norm_num⟩) u

/-- Factorisation of the tower level `U_1 = U_1(1 · 3¹)` at `3`. -/
example (u : (BHat hurwitzData.a hurwitzData.b)ˣ) :
    u ∈ hurwitzData.Utower 1 3 1 (by decide) ↔
      u * localEmbedGL hurwitzData 3 three_ndvd (localComponent hurwitzData 3 three_ndvd u)⁻¹ ∈
          hurwitzData.Utower 1 3 1 (by decide) ∧
        localComponent hurwitzData 3 three_ndvd u ∈ K1 3 1 :=
  mem_Utower_iff_factor_at one_ne_zero (by decide : ¬ 3 ∣ 1) le_rfl u
