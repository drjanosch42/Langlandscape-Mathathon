/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Module
import Langlandscape.Quat.Stab

/-! Non-vacuity tests for `Langlandscape.Brandt.Module` (S01-L7). -/

namespace LanglandscapeTests.S01.Brandt

open Langlandscape.Quat Langlandscape.Brandt

/-- The norm map at level `Ô^×` over `ℚ` is bijective (all weights are nonzero rationals). -/
example (d : DefiniteData) : Function.Bijective (normMap d.Ohat ℚ) := by
  have := XB_finite d le_rfl d.Ohat_isOpen
  refine normMap_bijective _ _ fun c => ?_
  rw [isUnit_iff_ne_zero]
  have h24 := card_Gam_dvd_24 d.ha d.hb d.O.1 (le_refl d.Ohat) (Quotient.out c)
  have h0 : 0 < Nat.card (Gam d.Ohat (Quotient.out c)) :=
    Nat.pos_of_dvd_of_pos h24 (by norm_num)
  haveI : Finite (Gam d.Ohat (Quotient.out c)) := Nat.finite_of_card_ne_zero h0.ne'
  haveI : Finite ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left (b := pmOne))) (Subgroup.inclusion_injective _)
  have hpos : 0 < wx d.Ohat (Quotient.out c) :=
    Nat.div_pos (Nat.le_of_dvd h0 (Subgroup.card_dvd_of_le (inf_le_left (b := pmOne)))) (Nat.card_pos)
  exact_mod_cast hpos.ne'

example (d : DefiniteData) : Function.Bijective (evalPairing d.Ohat ℤ).flip := by
  have := XB_finite d le_rfl d.Ohat_isOpen
  exact (evalPairing_perfect _ _).1

example (d : DefiniteData) : (brandtModule d.Ohat ℤ ℤ 1) = brandtModule d.Ohat ℤ ℤ 1 := rfl

end LanglandscapeTests.S01.Brandt
