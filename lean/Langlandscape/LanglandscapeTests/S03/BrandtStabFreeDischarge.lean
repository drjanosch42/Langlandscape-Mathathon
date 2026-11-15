/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.BrandtStabFreeDischarge
import Langlandscape.Ribet.PhiEis

/-!
# Tests for the discharge of `Hyp.BrandtStabFree`

Tex labels: lem:s03-stabfree, prop:s03-phieis. `Hyp.BrandtStabFree d ℓ` is available as a theorem
(`Hyp.brandtStabFree_holds`), and the step-(1) consumer `Ribet.brandtZ_dvd` holds without the hypothesis argument.
-/

set_option autoImplicit false

open GL2TF Langlandscape.Quat

/-- `s03-stabfree`: the hypothesis `Hyp.BrandtStabFree d ℓ` is a theorem. -/
example (d : DefiniteData) (ℓ : ℕ) : Langlandscape.Hyp.BrandtStabFree d ℓ :=
  Langlandscape.Hyp.brandtStabFree_holds d ℓ

/-- `s03-phieis`: step (1) of `prop:s03-phieis` off the diagonal, `w_c ∣ B(c,c')` for `c ≠ c'`, unconditionally
(`Ribet.brandtZ_dvd` with the discharged hypothesis). -/
theorem test_brandtZ_dvd_holds (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hq : d.D.Prime)
    (c c' : XB d.Ohat) (hne : c ≠ c') :
    (Langlandscape.Ribet.ohatWeight d c : ℤ) ∣ Langlandscape.Ribet.brandtZ d ℓ c c' :=
  Langlandscape.Ribet.brandtZ_dvd d ℓ hℓ hq (Langlandscape.Hyp.brandtStabFree_holds d ℓ) c c' hne
