/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.NormOne

/-! Tests for `Langlandscape.Tree.NormOne` (S02-L5a): `lem:s02-normone`. -/

namespace LanglandscapeTests.S02.NormOne

open Langlandscape Langlandscape.Quat Langlandscape.Tree

/-- `lem:s02-normone`(a) (`s02-normone`), test: injectivity at the maximal level `Ô^×`. -/
theorem injective_Ohat (d : DefiniteData) : Function.Injective (XBone.toXB d d.Ohat) :=
  XBone_toXB_injective le_rfl

/-- `lem:s02-normone`(b) (`s02-normone`), test: bijectivity at level `U`, with all hypotheses as explicit
arguments. -/
theorem bijective_of_hyp (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (hHS : Hyp.HS d)
    (hN : NrdSurj d U) (hU : U ≤ d.Ohat) : Function.Bijective (XBone.toXB d U) :=
  XBone_toXB_bijective hHS hN hU

/-- `lem:s02-normone`(a) (`s02-normone`), test: `Γ_1 = B^1 ∩ Ô^{1}` at `x = 1`, level `Ô^×`. -/
theorem GammaOne_Ohat_one (d : DefiniteData) :
    {γ : (QuatAlg ℚ d.a d.b)ˣ | GL2TF.Quat.nrd (γ : QuatAlg ℚ d.a d.b) = 1 ∧
        (1 : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹ * iotaU d.a d.b γ * 1 ∈ d.Ohat ⊓ BHatOne d} =
      (Gam d.Ohat (1 : (GL2TF.Quat.BHat d.a d.b)ˣ) : Set (QuatAlg ℚ d.a d.b)ˣ) :=
  GammaOne_eq_Gam le_rfl (one_mem _)

end LanglandscapeTests.S02.NormOne
