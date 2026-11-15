/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.SA
import Langlandscape.Hyp.HS

/-! Non-vacuity tests for `Langlandscape.Tree.Admissible`, `Langlandscape.Hyp.SA`, `Langlandscape.Hyp.HS` (S02-L4a). -/

set_option autoImplicit false

namespace LanglandscapeTests.S02.Admissible

open Langlandscape.Quat Langlandscape.Tree

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)

/-- `def:s02-GU` (`s02-GU`), test: `Ô^×` is a `q`-level. -/
theorem test_isQLevel_Ohat : IsQLevel d q hq d.Ohat :=
  isQLevel_Ohat

/-- `def:s02-GU` (`s02-GU`), test: `1 ∈ Γ_U` for every `U`. -/
theorem test_one_mem_GammaU (U : Subgroup (BHat d.a d.b)ˣ) : (1 : (QuatAlg ℚ d.a d.b)ˣ) ∈ GammaU d q hq U :=
  one_mem _

/-- `def:s02-GU` (`s02-GU`), test: `1 ∈ Γ_U` through the membership criterion. -/
theorem test_one_mem_GammaU' : (1 : (QuatAlg ℚ d.a d.b)ˣ) ∈ GammaU d q hq d.Ohat := by
  rw [mem_GammaU_iff]
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]
    exact GL2TF.Quat.nrdHom_one_aux
  · rw [map_one, awayAt_one]
    exact one_mem _

/-- `def:s02-GU` (`s02-GU`), test: `U_0(N)` is a `q`-level for `q ∤ N`. -/
theorem test_isQLevel_U0 (N : ℕ) (hN : N.Coprime d.D) (hqN : ¬ q ∣ N) : IsQLevel d q hq (d.U0 N hN) :=
  isQLevel_U0 hqN

/-- `def:s02-GU` (`s02-GU`), test: `U_1(N)` is a `q`-level for `q ∤ N`. -/
theorem test_isQLevel_U1 (N : ℕ) (hN : N.Coprime d.D) (hqN : ¬ q ∣ N) : IsQLevel d q hq (d.U1 N hN) :=
  isQLevel_U1 hqN

/-- `def:s02-GU` (`s02-GU`), test: the edge level `U_0(q)Ô^×` has the Iwahori factor at `q`. -/
theorem test_hasFactorAt_U0q_Ohat :
    HasFactorAt d q hq (Langlandscape.Local.Iw q) (d.U0q q (coprime_of_not_dvd hq) d.Ohat) :=
  hasFactorAt_U0q isQLevel_Ohat

/-- `def:s02-GU` (`s02-GU`), test: `det ι_q(1) = nrd 1 = 1`. -/
theorem test_det_one :
    ((Matrix.GeneralLinearGroup.det (localComponent d q hq (iotaU d.a d.b 1)) : ℚ_[q]ˣ) : ℚ_[q]) = 1 := by
  rw [det_localComponent_finEmbed, Units.val_one, GL2TF.Quat.nrdHom_one_aux, Rat.cast_one]

/-- `def:s02-GU` (`s02-GU`), test: the four standard levels are `q`-admissible, modulo `Hyp.RamNrdSurj d`. -/
theorem test_isQAdmissible_levels (hram : Langlandscape.Hyp.RamNrdSurj d) (N M p s : ℕ) (hN : N.Coprime d.D)
    (hMps : (M * p ^ s).Coprime d.D) (hqN : ¬ q ∣ N) (hqM : ¬ q ∣ M * p ^ s) :
    IsQAdmissible d q hq d.Ohat ∧ IsQAdmissible d q hq (d.U0 N hN) ∧ IsQAdmissible d q hq (d.U1 N hN) ∧
      IsQAdmissible d q hq (d.Utower M p s hMps) :=
  ⟨isQAdmissible_Ohat hram, isQAdmissible_U0 hram hqN, isQAdmissible_U1 hram hqN, isQAdmissible_Utower hram hqM⟩

/-- `thm:s02-SA` (`s02-SA`), test: `Hyp.SA` applies at `U_0(N)` given `Hyp.RamNrdSurj d`. -/
theorem test_SA_U0 (hSA : Langlandscape.Hyp.SA d q hq) (hram : Langlandscape.Hyp.RamNrdSurj d) (N : ℕ)
    (hN : N.Coprime d.D) (hqN : ¬ q ∣ N) : SAat d q hq (d.U0 N hN) :=
  hSA _ (isQAdmissible_U0 hram hqN)

/-- `thm:s02-SA` (`s02-SA`), test: the shapes of `Hyp.SA` and `Hyp.HS` typecheck, and `Hyp.SA` specialises to
`SAat` at a `q`-admissible level. -/
theorem test_SA_apply (hSA : Langlandscape.Hyp.SA d q hq) (_hHS : Langlandscape.Hyp.HS d)
    (U : Subgroup (BHat d.a d.b)ˣ) (hU : IsQAdmissible d q hq U) : SAat d q hq U :=
  hSA U hU

end LanglandscapeTests.S02.Admissible
