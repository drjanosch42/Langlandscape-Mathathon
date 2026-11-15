/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Weights

/-! Non-vacuity tests for `Langlandscape.Quat.Weights` (S01-L6). -/

namespace LanglandscapeTests.S01.Weights

open Langlandscape.Quat

example : Nat.card (pmOne : Subgroup (GL2TF.Quat.QuatAlg ℚ (-1) (-1))ˣ) = 2 := card_pmOne

/-- Level change at `U' = U = Ô^×` is the trivial instance of `XB_finite_of_relIndex` and `massW_level_change`. -/
example (d : DefiniteData) : Finite (XB d.Ohat) := by
  have := XB_finite d le_rfl d.Ohat_isOpen
  exact XB_finite_of_relIndex (le_refl d.Ohat) (by simp [Subgroup.relIndex_self]) (U := d.Ohat)

example (d : DefiniteData) (hn : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) ∈ d.Ohat) :
    massW d.Ohat = (d.Ohat.relIndex d.Ohat : ℚ) * massW d.Ohat := by
  have := XB_finite d le_rfl d.Ohat_isOpen
  exact massW_level_change le_rfl (by simp) (Or.inl hn)

example (d : DefiniteData) (x : (GL2TF.Quat.BHat d.a d.b)ˣ)
    (hn : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) ∈ d.Ohat) : 2 * wx d.Ohat x = Nat.card (Gam d.Ohat x) :=
  two_mul_wx hn x

end LanglandscapeTests.S01.Weights
