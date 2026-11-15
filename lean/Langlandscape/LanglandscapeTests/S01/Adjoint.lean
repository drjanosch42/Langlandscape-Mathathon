/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Adjoint

/-! Non-vacuity tests for `Langlandscape.Brandt.Adjoint` (S01-L8b). -/

namespace LanglandscapeTests.S01.Adjoint

open Langlandscape.Quat Langlandscape.Brandt

/-- `prop:s01-adjoint` (`s01-adjoint`), test helper: `[U : U ∩ g U g⁻¹] < ∞` holds for `g = 1`. -/
theorem relIndex_conjSub_one (d : DefiniteData) (g : (GL2TF.Quat.BHat d.a d.b)ˣ) (hg : g = 1) :
    (d.Ohat ⊓ conjSub d.Ohat g).relIndex d.Ohat ≠ 0 := by
  subst hg
  rw [Subgroup.relIndex_eq_one.2]
  · exact one_ne_zero
  · intro z hz
    refine Subgroup.mem_inf.2 ⟨hz, (mem_conjSub _ _).2 ?_⟩
    simpa using hz

/-- The adjoint identity at level `Ô^×` for `g = 1`, with both finiteness hypotheses discharged. -/
example (d : DefiniteData) (x y : ZX d.Ohat ℤ) :
    haveI := XB_finite d le_rfl d.Ohat_isOpen
    brandtPairing d.Ohat ℤ (heckeTHom d.Ohat 1 ℤ (relIndex_conjSub_one d 1 rfl) x) y =
      brandtPairing d.Ohat ℤ x (heckeTHom d.Ohat 1⁻¹ ℤ (relIndex_conjSub_one d 1⁻¹ inv_one) y) :=
  haveI := XB_finite d le_rfl d.Ohat_isOpen
  brandtPairing_heckeTHom _ _ _ _ _ x y

/-- `ν ∘ T_1 = T_1 ∘ ν` at level `Ô^×`. -/
example (d : DefiniteData) (x : ZX d.Ohat ℚ) :
    haveI := XB_finite d le_rfl d.Ohat_isOpen
    normMap d.Ohat ℚ (heckeTHom d.Ohat 1 ℚ (relIndex_conjSub_one d 1 rfl) x) =
      heckeT d.Ohat 1⁻¹ ℚ (relIndex_conjSub_one d 1⁻¹ inv_one) (normMap d.Ohat ℚ x) :=
  haveI := XB_finite d le_rfl d.Ohat_isOpen
  normMap_heckeT _ _ _ _ _ x

/-- `ν ∘ π_* = tr ∘ ν'` for `U' = U = Ô^×` (the sign hypothesis is decidable either way). -/
example (d : DefiniteData) (x : ZX d.Ohat ℤ) :
    normMap d.Ohat ℤ (pushforward d.Ohat d.Ohat ℤ x) =
      trace d.Ohat d.Ohat ℤ (by rw [Subgroup.relIndex_self]; exact one_ne_zero) (normMap d.Ohat ℤ x) :=
  normMap_pushforward _ _ _ _ le_rfl (em _) x

end LanglandscapeTests.S01.Adjoint
