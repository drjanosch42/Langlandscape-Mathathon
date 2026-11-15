/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.RightTranslate
import LanglandscapeTests.S01.Levels

/-! Non-vacuity checks for S01-L11b (`Brandt/RightTranslate.lean`), Hurwitz data `D = 2`, `ℓ = 2`, `q = 3`. -/

open Langlandscape.Quat Langlandscape.Brandt

/-- `Ô^×` is maximal at the ramified prime `2`. -/
example : IsMaximalAt hurwitzData 2 hurwitzData.Ohat :=
  isMaximalAt_Ohat (dvd_refl 2)

/-- `U_1(3)` is maximal at the ramified prime `2`. -/
example : IsMaximalAt hurwitzData 2 (hurwitzData.U1 3 cop3) :=
  isMaximalAt_U1 (dvd_refl 2)

/-- `𝒪_2 = {nrd ∈ ℤ_2}` for the Hurwitz order. -/
example (z : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b) :
    z ∈ localOrder hurwitzData 2 ↔ GL2TF.Quat.nrd z ∈ PadicInt.subring 2 :=
  mem_localOrder_iff_nrd (dvd_refl 2) z

/-- `Π 𝒪_2 Π⁻¹ = 𝒪_2`. -/
example (P : (QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)ˣ) (z : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b) :
    (P : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b) * z *
        ((P⁻¹ : (QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)ˣ) : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b) ∈
      localOrder hurwitzData 2 ↔ z ∈ localOrder hurwitzData 2 :=
  PiEll_normalizes (dvd_refl 2) P z

/-- `Π_2` at level `U_1(3)`: `(Π_2 f)[x] = f[x Π]`. -/
example (P : (QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)ˣ) (f : ZXdual (hurwitzData.U1 3 cop3) ℤ)
    (x : (BHat hurwitzData.a hurwitzData.b)ˣ) :
    PiEll ℤ hurwitzData (hurwitzData.U1 3 cop3) 2 (dvd_refl 2) P f
        (DoubleCoset.mk (globalUnits hurwitzData.a hurwitzData.b) (hurwitzData.U1 3 cop3) x) =
      f (DoubleCoset.mk (globalUnits hurwitzData.a hurwitzData.b) (hurwitzData.U1 3 cop3)
        (x * localEmbed hurwitzData.a hurwitzData.b 2 P)) :=
  PiEll_apply ℤ (dvd_refl 2) (isMaximalAt_U1 (dvd_refl 2)) P f x

/-- `Π_2` does not depend on the choice of `Π` (same `‖nrd‖`). -/
example (P P' : (QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)ˣ)
    (h : ‖GL2TF.Quat.nrd (P : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)‖ =
      ‖GL2TF.Quat.nrd (P' : QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)‖) :
    PiEll ℤ hurwitzData hurwitzData.Ohat 2 (dvd_refl 2) P = PiEll ℤ hurwitzData hurwitzData.Ohat 2 (dvd_refl 2) P' :=
  PiEll_indep ℤ (dvd_refl 2) (isMaximalAt_Ohat (dvd_refl 2)) P P' h

/-- Right translation by `B_3^×` on class sets. -/
example (y : (QuatAlg ℚ_[3] hurwitzData.a hurwitzData.b)ˣ) (x : (BHat hurwitzData.a hurwitzData.b)ˣ) :
    rightTranslate hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 3 y)
        (DoubleCoset.mk (globalUnits hurwitzData.a hurwitzData.b) hurwitzData.Ohat x) =
      DoubleCoset.mk (globalUnits hurwitzData.a hurwitzData.b)
        (rightConj hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 3 y))
        (x * localEmbed hurwitzData.a hurwitzData.b 3 y) :=
  rightTranslate_mk _ _ x

/-- An operator supported at `2` commutes with right translation by `B_3^×` (the commutation hypothesis is
discharged by `localEmbed_comm`). -/
example (y : (QuatAlg ℚ_[3] hurwitzData.a hurwitzData.b)ˣ) (P : (QuatAlg ℚ_[2] hurwitzData.a hurwitzData.b)ˣ)
    (hfin : (hurwitzData.Ohat ⊓ conjSub hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 2 P)).relIndex
      hurwitzData.Ohat ≠ 0) :
    (heckeT hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 2 P) ℤ hfin).comp
        (rightTranslateLin ℤ hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 3 y)) =
      (rightTranslateLin ℤ hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 3 y)).comp
        (heckeT (rightConj hurwitzData.Ohat (localEmbed hurwitzData.a hurwitzData.b 3 y))
          (localEmbed hurwitzData.a hurwitzData.b 2 P) ℤ
          (relIndex_rightConj_ne_zero _ _ _ (localEmbed_comm (by decide) y P) hfin)) :=
  heckeT_comm_rightTranslate ℤ _ _ _ (localEmbed_comm (by decide) y P) hfin
