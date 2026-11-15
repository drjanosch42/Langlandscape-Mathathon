/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Corollaries
import LanglandscapeTests.S01.Levels

/-! Non-vacuity checks for S01-L16b (audit R3/R4/R6): the diamond operators (`Brandt/Hecke.lean` section
`Diamond`, `Quat/Stab.lean` section `Delta`, `Brandt/Corollaries.lean` `Up_comm_diamond*`).
Hurwitz data `D = 2`; tower `U_s = U_1(3 · 5^s)`, `p = 5`, `M = 3`. -/

namespace LanglandscapeTests.S01.Diamond

open Langlandscape.Quat Langlandscape.Brandt

/-- `5 ∤ D = 2` (test data, `s01-hecke`). -/
theorem five_ndvd : ¬ 5 ∣ hurwitzData.D := by decide

/-- `5 ∈ primeFactors 15` (test data, `s01-hecke`). -/
theorem five_mem_15 : 5 ∈ (15 : ℕ).primeFactors :=
  Nat.mem_primeFactors.2 ⟨by norm_num, by norm_num, by norm_num⟩

/-- `3 ∈ primeFactors (3 · 5^s)` (test data, `s01-hecke`): `3 ∣ M`. -/
theorem three_mem_tower (s : ℕ) : 3 ∈ (3 * 5 ^ s).primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.prime_three, dvd_mul_right 3 _, by positivity⟩

/-- `hn` of `diamond` at `U_1(15)`, `ℓ = 5 ∣ 15`. -/
example (t : ℤ_[5]ˣ) :
    ∀ x ∈ hurwitzData.U1 15 cop15,
      (diamondElt hurwitzData 5 five_ndvd t)⁻¹ * x * diamondElt hurwitzData 5 five_ndvd t ∈
        hurwitzData.U1 15 cop15 :=
  diamondElt_inv_normalizes_U1 five_mem_15 t

/-- On `U_0(15)` the diamond operator at `3` is the identity (`δ_t ∈ U_0(15)`). -/
example (t : ℤ_[3]ˣ) :
    diamond hurwitzData (hurwitzData.U0 15 cop15) 3 three_ndvd ℤ t (diamondElt_inv_normalizes_U0 t) =
      LinearMap.id :=
  diamond_eq_id_of_mem ℤ _ t _ (deltaElt_mem_U0 t)

/-- `U_5` commutes with the diamond operator at `3 ∣ M` on `U_1(3 · 5^s)` (no hypothesis left). -/
example (s : ℕ) (hs : 1 ≤ s) (h : (3 * 5 ^ s).Coprime hurwitzData.D) (t : ℤ_[3]ˣ) :
    Up hurwitzData 3 5 s h five_ndvd (by norm_num) (by norm_num) hs ℤ ∘ₗ
        diamond hurwitzData (hurwitzData.Utower 3 5 s h) 3 three_ndvd ℤ t
          (diamondElt_inv_normalizes_U1 (three_mem_tower s) t) =
      diamond hurwitzData (hurwitzData.Utower 3 5 s h) 3 three_ndvd ℤ t
          (diamondElt_inv_normalizes_U1 (three_mem_tower s) t) ∘ₗ
        Up hurwitzData 3 5 s h five_ndvd (by norm_num) (by norm_num) hs ℤ :=
  Up_comm_diamond ℤ three_ndvd (by norm_num) (by norm_num) (by norm_num) hs t _

/-- `U_5` commutes with the diamond operator at `p = 5` itself on `U_1(3 · 5^s)`. -/
example (s : ℕ) (hs : 1 ≤ s) (h : (3 * 5 ^ s).Coprime hurwitzData.D) (t : ℤ_[5]ˣ) :
    Up hurwitzData 3 5 s h five_ndvd (by norm_num) (by norm_num) hs ℤ ∘ₗ
        diamond hurwitzData (hurwitzData.Utower 3 5 s h) 5 five_ndvd ℤ t
          (diamondElt_inv_normalizes_Utower (by norm_num) (by norm_num) hs t) =
      diamond hurwitzData (hurwitzData.Utower 3 5 s h) 5 five_ndvd ℤ t
          (diamondElt_inv_normalizes_Utower (by norm_num) (by norm_num) hs t) ∘ₗ
        Up hurwitzData 3 5 s h five_ndvd (by norm_num) (by norm_num) hs ℤ :=
  Up_comm_diamond_self ℤ (by norm_num) (by norm_num) hs t _

/-- `diamondAct` is multiplicative and `⟨1⟩ = 1` (`t ≡ 1 mod 5^s`) on `X_B(U_1(3 · 5^s))`. -/
example (s : ℕ) (hs : 1 ≤ s) (h : (3 * 5 ^ s).Coprime hurwitzData.D) (t t' : ℤ_[5]ˣ) :
    diamondAct (hp := five_ndvd) (hN := h) (by norm_num) (by norm_num) hs (t * t') =
        diamondAct (hp := five_ndvd) (hN := h) (by norm_num) (by norm_num) hs t *
          diamondAct (hp := five_ndvd) (hN := h) (by norm_num) (by norm_num) hs t' ∧
      diamondAct (hp := five_ndvd) (hN := h) (by norm_num) (by norm_num) hs 1 = 1 :=
  ⟨diamondAct_mul _ _ hs t t', diamondAct_eq_one _ _ hs 1 (by simp)⟩

/-- The diamond operator at `p = 5` is the pull-back along `diamondAct`. -/
example (s : ℕ) (hs : 1 ≤ s) (h : (3 * 5 ^ s).Coprime hurwitzData.D) (t : ℤ_[5]ˣ)
    (f : ZXdual (hurwitzData.Utower 3 5 s h) ℤ) (c : XB (hurwitzData.Utower 3 5 s h)) :
    diamond hurwitzData (hurwitzData.Utower 3 5 s h) 5 five_ndvd ℤ t
        (diamondElt_inv_normalizes_Utower (by norm_num) (by norm_num) hs t) f c =
      f (diamondAct (hp := five_ndvd) (by norm_num) (by norm_num) hs t c) :=
  diamond_apply_eq_diamondAct ℤ _ _ hs t _ f c

end LanglandscapeTests.S01.Diamond
