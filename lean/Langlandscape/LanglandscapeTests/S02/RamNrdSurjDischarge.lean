/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.RamNrdSurjDischarge
import Langlandscape.Quat.LevelNrd

/-!
# Tests for the discharge of `Hyp.RamNrdSurj`

Tex labels: lem:s01-nrd. `Hyp.RamNrdSurj d` is available as a theorem (`Hyp.ramNrdSurj_holds`), and the consumers
of `Quat/LevelNrd.lean` hold unconditionally once it is supplied.
-/

set_option autoImplicit false

open GL2TF Langlandscape.Quat

/-- `s01-nrd`: the hypothesis `Hyp.RamNrdSurj d` is a theorem. -/
example (d : DefiniteData) : Langlandscape.Hyp.RamNrdSurj d := Langlandscape.Hyp.ramNrdSurj_holds d

/-- `s01-nrd`: `nrd(Ô^×) ⊇ Ẑ^×` unconditionally (`nrdSurj_Ohat` with the discharged hypothesis). -/
theorem test_nrdSurj_Ohat_holds (d : DefiniteData) : NrdSurj d d.Ohat :=
  nrdSurj_Ohat (Langlandscape.Hyp.ramNrdSurj_holds d)

/-- `s01-nrd`: the level statements `nrdSurj_U0`, `nrdSurj_U1`, `nrdSurj_Utower` hold unconditionally. -/
theorem test_nrdSurj_levels_holds (d : DefiniteData) (N M p s : ℕ) (hN : N.Coprime d.D)
    (hMps : (M * p ^ s).Coprime d.D) :
    NrdSurj d (d.U0 N hN) ∧ NrdSurj d (d.U1 N hN) ∧ NrdSurj d (d.Utower M p s hMps) :=
  ⟨nrdSurj_U0 (Langlandscape.Hyp.ramNrdSurj_holds d) N hN, nrdSurj_U1 (Langlandscape.Hyp.ramNrdSurj_holds d) N hN,
    nrdSurj_Utower (Langlandscape.Hyp.ramNrdSurj_holds d) M p s hMps⟩
