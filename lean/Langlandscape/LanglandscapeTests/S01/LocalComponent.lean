/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalComponent
import AlgJL.VolIII.P2.Instances

/-! Non-vacuity checks for S01-L3b (`Quat/LocalComponent.lean`). -/

open Langlandscape.Quat

/-- The Hurwitz data `D = 2`, `B = (-1,-1)_ℚ`, `O` = Hurwitz order. -/
noncomputable def hurwitzData : DefiniteData where
  a := -1
  b := -1
  D := 2
  O := ⟨GL2TF.Quat.hurwitzOrder, GL2TF.Quat.Inst.isMaximal_hurwitz⟩
  hD := GL2TF.Quat.pizer_algebras.1

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- `3 ∤ D = 2` (test data for `def:s01-B`, `s01-B`). -/
lemma three_ndvd : ¬ 3 ∣ hurwitzData.D := by decide

/-- `ι_3` exists for the Hurwitz order and is the import's choice term. -/
noncomputable example : GL2TF.Quat.QuatAlg ℚ_[3] (-1) (-1) ≃ₐ[ℚ_[3]] Matrix (Fin 2) (Fin 2) ℚ_[3] :=
  hurwitzData.iota 3 three_ndvd

example : hurwitzData.iota 3 three_ndvd =
    Classical.choose (GL2TF.Quat.maximalOrder_local_split hurwitzData.O hurwitzData.hD 3 three_ndvd) := rfl

/-- `localComponent` at `3` sends `Ô^×` into integral matrices (both `g` and `g⁻¹`). -/
example (u : (BHat (-1) (-1))ˣ) (hu : u ∈ orderCompletionUnits hurwitzData.O.1) (i j : Fin 2) :
    ‖((localComponent hurwitzData 3 three_ndvd u : GL (Fin 2) ℚ_[3]) : Matrix (Fin 2) (Fin 2) ℚ_[3]) i j‖ ≤ 1 ∧
    ‖(((localComponent hurwitzData 3 three_ndvd u)⁻¹ : GL (Fin 2) ℚ_[3]) :
      Matrix (Fin 2) (Fin 2) ℚ_[3]) i j‖ ≤ 1 :=
  ⟨localComponent_integral hu i j, localComponent_inv_integral hu i j⟩

/-- `1 ∈ Ô^×` is a non-vacuous instance of the hypothesis. -/
example (i j : Fin 2) :
    ‖((localComponent hurwitzData 3 three_ndvd 1 : GL (Fin 2) ℚ_[3]) : Matrix (Fin 2) (Fin 2) ℚ_[3]) i j‖ ≤ 1 :=
  localComponent_integral (Subgroup.one_mem _) i j

/-- On global units the local component is the import's `ellAdicSplitting`. -/
example (γ : (GL2TF.Quat.QuatAlg ℚ (-1) (-1))ˣ) :
    ((localComponent hurwitzData 3 three_ndvd (Units.map (finEmbed (-1) (-1)).toMonoidHom γ) : GL (Fin 2) ℚ_[3]) :
      Matrix (Fin 2) (Fin 2) ℚ_[3]) =
    GL2TF.Quat.ellAdicSplitting hurwitzData.O hurwitzData.hD 3 three_ndvd (γ : GL2TF.Quat.QuatAlg ℚ (-1) (-1)) :=
  localComponent_finEmbed_eq_ellAdicSplitting (d := hurwitzData) (hℓ := three_ndvd) γ

/-- `localProj` is defined at the ramified prime `2` too. -/
noncomputable example : (BHat (-1) (-1))ˣ →* (GL2TF.Quat.QuatAlg ℚ_[2] (-1) (-1))ˣ :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  localProjUnits (-1) (-1) 2

/-- `Ô^×` lands in `GL₂(ℤ₃)` for the Hurwitz data. -/
example : hurwitzData.Ohat ≤ (Langlandscape.Local.GL2Zl 3).comap (localComponent hurwitzData 3 three_ndvd) :=
  Ohat_le_comap_GL2Zl
