/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelNrd

/-!
# Tests for S02 LevelNrd — S02-L10

Tex labels: lem:s01-nrd.
-/

open GL2TF Langlandscape.Quat

/-- Shape test (`s01-nrd`): `nrdHat` and `NrdSurj` typecheck for variable data. -/
example (d : DefiniteData) (U : Subgroup (BHat d.a d.b)ˣ) : Prop := NrdSurj d U

noncomputable example (a b : ℤ) : (BHat a b)ˣ →* FinAdeleˣ := nrdHat a b

/-- `s01-nrd`: `det_iota` for a variable `d`, prime `ℓ` and `x`. -/
theorem test_det_iota (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)
    (x : QuatAlg ℚ_[ℓ] d.a d.b) : (d.iota ℓ hℓ x).det = GL2TF.Quat.nrd x :=
  det_iota x

/-- `s01-nrd`: `NrdSurj` for `Ô^×`, modulo `Hyp.RamNrdSurj d` (needed for every definite algebra: `D > 1`). -/
theorem test_nrdSurj_Ohat (d : DefiniteData) (hram : Langlandscape.Hyp.RamNrdSurj d) : NrdSurj d d.Ohat :=
  nrdSurj_Ohat hram

/-- `s01-nrd`: the four level statements have the expected shape. -/
theorem test_nrdSurj_levels (d : DefiniteData) (hram : Langlandscape.Hyp.RamNrdSurj d) (N M p s : ℕ)
    (hN : N.Coprime d.D) (hMps : (M * p ^ s).Coprime d.D) :
    NrdSurj d (d.U0 N hN) ∧ NrdSurj d (d.U1 N hN) ∧ NrdSurj d (d.Utower M p s hMps) :=
  ⟨nrdSurj_U0 hram N hN, nrdSurj_U1 hram N hN, nrdSurj_Utower hram M p s hMps⟩
