/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Indef

/-! Non-vacuity tests for `Langlandscape.Tree.TwoTerm` and `Langlandscape.Tree.Indef` (S02-L9). -/

set_option autoImplicit false

namespace LanglandscapeTests.S02.TwoTerm

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (R : Type) [CommRing R]

/-- `def:s02-Mhom`, `if:s02-coh` (`s02-Mhom`), test: the sign of `∂` on a basis edge at level `Ô^×`. -/
theorem test_partialHom_single (e : XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :
    partialHom d q hq d.Ohat R (Finsupp.single e 1) =
      (-(Finsupp.single (s0 d q hq d.Ohat e) 1), Finsupp.single (s1 d q hq d.Ohat e) 1) :=
  partialHom_single e 1

/-- `def:s02-Mhom`, `def:s02-indef` (`s02-Mhom`), test: at level `Ô^×`, `∂` is the boundary of `BG(Ô^×, q)`. -/
theorem test_partialHom_eq_boundary :
    partialHom d q hq d.Ohat R = Langlandscape.Graph.boundary (BG d q hq d.Ohat isQLevel_Ohat) R :=
  partialHom_eq_boundary isQLevel_Ohat

/-- `def:s02-Mhom`, `if:s02-coh` (`s02-Mhom`), test: the sign of `δ` at an edge. -/
theorem test_deltaCoh (f0 f1 : ZXdual d.Ohat R) (e : XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :
    deltaCoh d q hq d.Ohat R (f0, f1) e = f1 (s1 d q hq d.Ohat e) - f0 (s0 d q hq d.Ohat e) :=
  deltaCoh_apply_apply (f0, f1) e

/-- `prop:s02-harm` (`s02-harm`), test: `0` is `q`-new. -/
theorem test_zero_mem_qNew : (0 : ZXdual (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R) ∈
    qNew d q hq d.Ohat R isQLevel_Ohat :=
  zero_mem _

/-- `def:s02-Mhom`(iv) (`s02-Mhom`), test: the trace formula for `tr_1` at level `Ô^×`. -/
theorem test_s1Tr_apply_mk (f : ZXdual (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R) (x : (BHat d.a d.b)ˣ) :
    s1Tr d q hq d.Ohat R isQLevel_Ohat f (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat x) =
      ∑ᶠ u : ↥d.Ohat ⧸ (s1Level d q hq d.Ohat).subgroupOf d.Ohat,
        f (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) d.Ohat)
          (x * ((Quotient.out u : d.Ohat) : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)) :=
  s1Tr_apply_mk isQLevel_Ohat f x

/-- `prop:s02-Mhomprops`(d) (`s02-Mhom`), test: `ν ∘ s_{1*} = tr_1 ∘ ν'` at level `Ô^×`. -/
theorem test_normMap_comp_s1Push :
    normMap d.Ohat R ∘ₗ s1Push d q hq d.Ohat R =
      s1Tr d q hq d.Ohat R isQLevel_Ohat ∘ₗ normMap (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R :=
  normMap_comp_s1Push isQLevel_Ohat

/-- `prop:s02-harm`, `def:s02-indef` (`s02-Mhom`), test: the comparison `ker ∂ ≃ q-new` exists when all weights at
level `Ô^×` are units. -/
theorem test_qNewEquivKerPartial (hw : ∀ c : XB d.Ohat, IsUnit ((wx d.Ohat (Quotient.out c) : ℕ) : R)) :
    Nonempty (XindefR d q hq d.Ohat R ≃ₗ[R] qNew d q hq d.Ohat R isQLevel_Ohat) :=
  ⟨qNewEquivKerPartial isQLevel_Ohat hw⟩

/-- `def:s02-indef`, `if:s02-indef` (`s02-indef`), test: the rank formula at level `Ô^×` for connected `BG`. -/
theorem test_finrank_Xindef (hc : BGConnected d q hq d.Ohat isQLevel_Ohat) :
    Module.finrank ℤ (Xindef d q hq d.Ohat isQLevel_Ohat) + 2 * Nat.card (XB d.Ohat) =
      Nat.card (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) + 1 :=
  finrank_Xindef_of_connected isQLevel_Ohat hc

/-- `def:s02-Mhom`(iv) (`s02-Mhom`), test: the trace formula for `tr_0` at level `Ô^×`. -/
theorem test_s0Tr_apply_mk (f : ZXdual (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R) (x : (BHat d.a d.b)ˣ) :
    s0Tr d q hq d.Ohat R isQLevel_Ohat f (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat x) =
      ∑ᶠ u : ↥d.Ohat ⧸ (d.U0q q (coprime_of_not_dvd hq) d.Ohat).subgroupOf d.Ohat,
        f (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) d.Ohat)
          (x * ((Quotient.out u : d.Ohat) : (BHat d.a d.b)ˣ))) :=
  s0Tr_apply_mk isQLevel_Ohat f x

/-- `prop:s02-Mhomprops`(d) (`s02-Mhom`), test: `ν ∘ s_{0*} = tr_0 ∘ ν'` at level `Ô^×`. -/
theorem test_normMap_comp_s0Push :
    normMap d.Ohat R ∘ₗ s0Push d q hq d.Ohat R =
      s0Tr d q hq d.Ohat R isQLevel_Ohat ∘ₗ normMap (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R :=
  normMap_comp_s0Push isQLevel_Ohat

/-- `lem:s01-stab`(c), `def:s02-Mhom` (`s02-Mhom`), test: over `ℚ` every weight `w_x ≥ 1` at level `Ô^×` is a
unit. -/
theorem test_hw_rat (c : XB d.Ohat) : IsUnit ((wx d.Ohat (Quotient.out c) : ℕ) : ℚ) := by
  rw [isUnit_iff_ne_zero]
  have h24 := card_Gam_dvd_24 d.ha d.hb d.O.1 (le_refl d.Ohat) (Quotient.out c)
  have h0 : 0 < Nat.card (Gam d.Ohat (Quotient.out c)) :=
    Nat.pos_of_dvd_of_pos h24 (by norm_num)
  have : Finite (Gam d.Ohat (Quotient.out c)) := Nat.finite_of_card_ne_zero h0.ne'
  have : Finite ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left (b := pmOne))) (Subgroup.inclusion_injective _)
  have hpos : 0 < wx d.Ohat (Quotient.out c) :=
    Nat.div_pos (Nat.le_of_dvd h0 (Subgroup.card_dvd_of_le (inf_le_left (b := pmOne)))) Nat.card_pos
  exact_mod_cast hpos.ne'

/-- `prop:s02-harm`, `def:s02-indef` (`s02-Mhom`), test: over `R = ℚ` the comparison `ker ∂ ≃ q-new` holds
unconditionally at level `Ô^×`. -/
theorem test_qNewEquivKerPartial_rat :
    Nonempty (XindefR d q hq d.Ohat ℚ ≃ₗ[ℚ] qNew d q hq d.Ohat ℚ isQLevel_Ohat) :=
  ⟨qNewEquivKerPartial isQLevel_Ohat (test_hw_rat d)⟩

end LanglandscapeTests.S02.TwoTerm
