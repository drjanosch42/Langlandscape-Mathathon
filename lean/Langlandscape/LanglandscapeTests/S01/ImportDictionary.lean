/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.ImportDictionary

/-! Non-vacuity tests for `Langlandscape.Brandt.ImportDictionary` (S01-L12). -/

namespace LanglandscapeTests.S01.ImportDictionary

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

/-- `ϖ_ℓ` lies in the import's `Ô_ℓ`, for every split prime `ℓ`. -/
example (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) :
    elemT d ℓ hℓ ∈ GL2TF.Quat.normNSet d.O.1 ℓ := by
  rw [← dcSet_elemT_eq_normNSet d ℓ hℓ]
  exact (mem_dcSet _ _).2 ⟨1, d.Ohat.one_mem, 1, d.Ohat.one_mem, by simp⟩

/-- The matrix of `T_ℓ` over `ℤ` is the import's Brandt matrix. -/
example (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)
    (hfin : (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)).relIndex d.Ohat ≠ 0) (c c' : XB d.Ohat) :
    Tl d d.Ohat ℓ hℓ ℤ hfin (Pi.single c' 1) c = (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : ℤ) :=
  Tl_matrix_eq_brandtMatrix d ℓ hℓ ℤ hfin c c'

/-- Self-adjointness of `T_ℓ` over `ℚ` at level `Ô^×`. -/
example (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)
    (hfin : (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)).relIndex d.Ohat ≠ 0) (x y : ZX d.Ohat ℚ) :
    have := finite_XB_Ohat d
    brandtPairing d.Ohat ℚ (heckeTHom d.Ohat (elemT d ℓ hℓ) ℚ hfin x) y =
      brandtPairing d.Ohat ℚ x (heckeTHom d.Ohat (elemT d ℓ hℓ) ℚ hfin y) :=
  have := finite_XB_Ohat d
  Tl_selfAdjoint_units d ℓ hℓ ℚ hfin x y

end LanglandscapeTests.S01.ImportDictionary
