/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.BrandtGraph

/-!
# Tests for S02 BrandtGraph — S02-L4b

Tex labels: def:s02-BG. Non-vacuity at the maximal level `Ô^×` for a split prime `q ∤ D`.
-/

namespace LanglandscapeTests.S02.BrandtGraph

open Langlandscape.Quat Langlandscape.Tree

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)

/-- `def:s02-BG` (`s02-BG`): `[Ô^× : U_0(q)Ô^×] = q + 1`. -/
theorem relIndex_U0q_Ohat :
    (d.U0q q (coprime_of_not_dvd hq) d.Ohat).relIndex d.Ohat = q + 1 :=
  relIndex_U0q (isQLevel_Ohat (hq := hq))

/-- `def:s02-BG` (`s02-BG`): `X_B(U_0(q)Ô^×)` is finite. -/
theorem finite_XB_U0q_Ohat : Finite (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :=
  finite_XB_U0q (isQLevel_Ohat (hq := hq))

/-- `def:s02-BG` (`s02-BG`): `[Ô^× : α⁻¹ (U_0(q)Ô^×) α] ≠ 0`. -/
theorem relIndex_s1Level_Ohat : (s1Level d q hq d.Ohat).relIndex d.Ohat ≠ 0 :=
  relIndex_s1Level_ne_zero (isQLevel_Ohat (hq := hq))

/-- `def:s02-BG` (`s02-BG`): the edges of `BG(Ô^×, q)` are `X_B(U_0(q)Ô^×)` and the vertices `X_B(Ô^×)`. -/
theorem BG_Ohat_shape :
    (BG d q hq d.Ohat isQLevel_Ohat).E = XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat) ∧
      (BG d q hq d.Ohat isQLevel_Ohat).V0 = XB d.Ohat ∧ (BG d q hq d.Ohat isQLevel_Ohat).V1 = XB d.Ohat :=
  ⟨rfl, rfl, rfl⟩

/-- `def:s02-BG` (`s02-BG`): the endpoints of the edge `[1]` of `BG(Ô^×, q)` are `[1]` and `[α]`. -/
theorem s0_s1_one :
    s0 d q hq d.Ohat (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) d.Ohat) 1) =
        DoubleCoset.mk (globalUnits d.a d.b) d.Ohat 1 ∧
      s1 d q hq d.Ohat (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) d.Ohat) 1) =
        DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (alphaElt d q hq) := by
  refine ⟨s0_mk 1, ?_⟩
  rw [s1_mk isQLevel_Ohat, one_mul]

/-- `def:s02-BG` (`s02-BG`): `s_{0*}` and `s_{1*}` on a basis vector, over `ℤ`. -/
theorem push_single (e : XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :
    s0Push d q hq d.Ohat ℤ (Finsupp.single e 1) = Finsupp.single (s0 d q hq d.Ohat e) 1 ∧
      s1Push d q hq d.Ohat ℤ (Finsupp.single e 1) = Finsupp.single (s1 d q hq d.Ohat e) 1 :=
  ⟨s0Push_single e 1, s1Push_single e 1⟩

/-- `def:s02-BG` (`s02-BG`): `s_0^*` of a constant function is constant. -/
theorem s0Pull_const (e : XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :
    s0Pull d q hq d.Ohat ℤ (fun _ => 1) e = 1 :=
  rfl

/-- `def:s02-BG` (`s02-BG`): `α⁻¹ u α ∈ Ô^×` for `u ∈ U_0(q)Ô^×`. -/
theorem alphaElt_inv_conj_mem_Ohat {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.U0q q (coprime_of_not_dvd hq) d.Ohat) :
    (alphaElt d q hq)⁻¹ * u * alphaElt d q hq ∈ d.Ohat :=
  alphaElt_inv_conj_mem isQLevel_Ohat hu

/-- `def:s02-BG` (`s02-BG`): `α⁻¹ (U_0(q)Ô^×) α ≤ Ô^×`. -/
theorem s1Level_le_Ohat : s1Level d q hq d.Ohat ≤ d.Ohat :=
  s1Level_le isQLevel_Ohat

/-- `def:s02-BG` (`s02-BG`): `s_1^* f [1] = f [α]` at level `Ô^×`. -/
theorem s1Pull_one (f : Langlandscape.Brandt.ZXdual d.Ohat ℤ) :
    s1Pull d q hq d.Ohat ℤ f
        (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) d.Ohat) 1) =
      f (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (alphaElt d q hq)) := by
  rw [s1Pull_apply, s1_mk isQLevel_Ohat, one_mul]

end LanglandscapeTests.S02.BrandtGraph
