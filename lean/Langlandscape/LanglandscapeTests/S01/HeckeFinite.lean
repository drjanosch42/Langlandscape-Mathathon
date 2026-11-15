/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.HeckeFinite
import LanglandscapeTests.S01.LocalComponent

/-! Non-vacuity checks for S01-L16a (`Brandt/HeckeFinite.lean`, `Quat/LevelFinite.lean`), Hurwitz data `D = 2`. -/

namespace LanglandscapeTests.S01.HeckeFinite

open Langlandscape.Quat Langlandscape.Brandt

/-- `5` is prime (test data). -/
instance instFactPrimeFiveHF : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `5 ∤ D = 2` (test data, `s01-hecke`). -/
lemma five_ndvd : ¬ 5 ∣ hurwitzData.D := by decide

/-- `gcd(5, 2) = 1` (test data, `s01-levels`). -/
lemma cop5 : (5 : ℕ).Coprime hurwitzData.D := by decide

/-- `gcd(1 · 3, 2) = 1` (test data, `s01-levels`). -/
lemma cop13' : (1 * 3 ^ 1).Coprime hurwitzData.D := by decide

/-- `[Ô^× : Ô^× ∩ ϖ_3 Ô^× ϖ_3⁻¹] ≠ 0` for the Hurwitz order, unconditionally. -/
example : (hurwitzData.Ohat ⊓ conjSub hurwitzData.Ohat (elemT hurwitzData 3 three_ndvd)).relIndex
    hurwitzData.Ohat ≠ 0 :=
  relIndex_elemT_ne_zero_Ohat hurwitzData 3 three_ndvd

/-- The same for `ϖ_3⁻¹`. -/
example : (hurwitzData.Ohat ⊓ conjSub hurwitzData.Ohat (elemT hurwitzData 3 three_ndvd)⁻¹).relIndex
    hurwitzData.Ohat ≠ 0 :=
  relIndex_elemT_inv_ne_zero_Ohat hurwitzData 3 three_ndvd

/-- `T_3` on `ℤ^X`, `X = X_B(Ô^×)`, without any hypothesis. -/
noncomputable example : ZXdual hurwitzData.Ohat ℤ →ₗ[ℤ] ZXdual hurwitzData.Ohat ℤ :=
  Tl hurwitzData hurwitzData.Ohat 3 three_ndvd ℤ (relIndex_elemT_ne_zero_Ohat hurwitzData 3 three_ndvd)

/-- `T_3` is self-adjoint at `Ô^×` over `ℚ` for the Hurwitz order, no free hypothesis. -/
example (x y : ZX hurwitzData.Ohat ℚ) :
    brandtPairing hurwitzData.Ohat ℚ
        (heckeTHom hurwitzData.Ohat (elemT hurwitzData 3 three_ndvd) ℚ
          (relIndex_elemT_ne_zero_Ohat hurwitzData 3 three_ndvd) x) y =
      brandtPairing hurwitzData.Ohat ℚ x
        (heckeTHom hurwitzData.Ohat (elemT hurwitzData 3 three_ndvd) ℚ
          (relIndex_elemT_ne_zero_Ohat hurwitzData 3 three_ndvd) y) :=
  Tl_selfAdjoint_units' hurwitzData 3 three_ndvd ℚ x y

/-- `T_3` is self-adjoint at `U_0(5)` over `ℚ` (`3 ∤ 2 · 5`), no free hypothesis. -/
example (x y : ZX (hurwitzData.U0 5 cop5) ℚ) :
    brandtPairing (hurwitzData.U0 5 cop5) ℚ
        (heckeTHom (hurwitzData.U0 5 cop5) (elemT hurwitzData 3 three_ndvd) ℚ
          (relIndex_elemT_ne_zero_U0 hurwitzData 3 three_ndvd (by decide)) x) y =
      brandtPairing (hurwitzData.U0 5 cop5) ℚ x
        (heckeTHom (hurwitzData.U0 5 cop5) (elemT hurwitzData 3 three_ndvd) ℚ
          (relIndex_elemT_ne_zero_U0 hurwitzData 3 three_ndvd (by decide)) y) :=
  Tl_selfAdjoint_U0' hurwitzData cop5 3 (by decide) ℚ x y

/-- The finiteness for `ϖ_5` and `ϖ_5⁻¹` at the tower level `U_1(1 · 3)`. -/
example : (hurwitzData.Utower 1 3 1 cop13' ⊓ conjSub (hurwitzData.Utower 1 3 1 cop13')
      (elemT hurwitzData 5 five_ndvd)).relIndex (hurwitzData.Utower 1 3 1 cop13') ≠ 0 ∧
    (hurwitzData.Utower 1 3 1 cop13' ⊓ conjSub (hurwitzData.Utower 1 3 1 cop13')
      (elemT hurwitzData 5 five_ndvd)⁻¹).relIndex (hurwitzData.Utower 1 3 1 cop13') ≠ 0 :=
  ⟨relIndex_elemT_ne_zero_Utower hurwitzData 5 five_ndvd (by decide) (by decide),
    relIndex_elemT_inv_ne_zero_Utower hurwitzData 5 five_ndvd (by decide) (by decide)⟩

/-- `U_3 ∘ T_5 = T_5 ∘ U_3` at level `U_1(3)`, no free hypothesis. -/
example :
    Up hurwitzData 1 3 1 cop13' three_ndvd one_ne_zero (by decide) le_rfl ℤ ∘ₗ
        Tl hurwitzData (hurwitzData.Utower 1 3 1 cop13') 5 five_ndvd ℤ
          (relIndex_elemT_ne_zero_Utower hurwitzData 5 five_ndvd (by decide) (by decide)) =
      Tl hurwitzData (hurwitzData.Utower 1 3 1 cop13') 5 five_ndvd ℤ
          (relIndex_elemT_ne_zero_Utower hurwitzData 5 five_ndvd (by decide) (by decide)) ∘ₗ
        Up hurwitzData 1 3 1 cop13' three_ndvd one_ne_zero (by decide) le_rfl ℤ :=
  Up_comm_Tl' ℤ five_ndvd (by decide) (by decide) one_ne_zero (by decide) le_rfl

/-- `X_B` is finite at `U_0(5)`, `U_1(5)`, `U_1(3)` (instances of `Quat/LevelFinite.lean`). -/
example : Finite (XB (hurwitzData.U0 5 cop5)) ∧ Finite (XB (hurwitzData.U1 5 cop5)) ∧
    Finite (XB (hurwitzData.Utower 1 3 1 cop13')) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end LanglandscapeTests.S01.HeckeFinite
