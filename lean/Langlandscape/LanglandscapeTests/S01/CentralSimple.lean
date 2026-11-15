/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.CentralSimple
import AlgJL.VolIII.P2.Instances
import Mathlib.Algebra.CharP.Algebra

/-! Non-vacuity checks for S01-L2 (`Quat/CentralSimple.lean`). -/

open Langlandscape.Quat
/-- `-1 < 0` (test data). -/
instance instFactNegOneLtZeroL2 : Fact ((-1 : ℤ) < 0) := ⟨by norm_num⟩

/-- `3` is prime (test data). -/
instance instFactPrimeThreeL2 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The instances for `B = (-1,-1)_ℚ` are found. -/
noncomputable example : DivisionRing (GL2TF.Quat.QuatAlg ℚ (-1) (-1)) := inferInstance
example : IsSimpleRing (GL2TF.Quat.QuatAlg ℚ (-1) (-1)) := inferInstance
example : Algebra.IsCentral ℚ (GL2TF.Quat.QuatAlg ℚ (-1) (-1)) := inferInstance

/-- No `Algebra ℚ` diamond: the division ring's `ℚ`-algebra is the quaternion one (`CharZero` kept local so
that the other tests see only the quaternion `Algebra ℚ`). -/
example :
    letI : CharZero (GL2TF.Quat.QuatAlg ℚ (-1) (-1)) :=
      charZero_of_injective_algebraMap (R := ℚ) QuaternionAlgebra.algebraMap_injective
    (DivisionRing.toRatAlgebra : Algebra ℚ (GL2TF.Quat.QuatAlg ℚ (-1) (-1))) = QuaternionAlgebra.instAlgebra :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- The inverse of the division ring is a genuine inverse. -/
example (x : GL2TF.Quat.QuatAlg ℚ (-1) (-1)) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

/-- Centrality over `ℚ_ℓ` (no definiteness needed). -/
example : Algebra.IsCentral ℚ_[3] (GL2TF.Quat.QuatAlg ℚ_[3] (-1) (-1)) :=
  QuatAlg.isCentral (by norm_num) (by norm_num)

/-- Skolem–Noether: every automorphism of `(-1,-1)_ℚ` is inner. -/
example (e : GL2TF.Quat.QuatAlg ℚ (-1) (-1) ≃ₐ[ℚ] GL2TF.Quat.QuatAlg ℚ (-1) (-1)) :
    ∃ x : (GL2TF.Quat.QuatAlg ℚ (-1) (-1))ˣ, ∀ y, e y = x * y * x⁻¹ :=
  QuatAlg.algEquiv_inner e

/-- Skolem–Noether for maps from a field into `(-1,-1)_ℚ`. -/
example {L : Type} [Field L] [Algebra ℚ L] (f g : L →ₐ[ℚ] GL2TF.Quat.QuatAlg ℚ (-1) (-1)) :
    ∃ x : (GL2TF.Quat.QuatAlg ℚ (-1) (-1))ˣ, ∀ y, g y = x * f y * x⁻¹ :=
  QuatAlg.algHom_conj f g

/-- The Hurwitz data `D = 2`, `B = (-1,-1)_ℚ`. -/
noncomputable def hurwitzDataL2 : DefiniteData where
  a := -1
  b := -1
  D := 2
  O := ⟨GL2TF.Quat.hurwitzOrder, GL2TF.Quat.Inst.isMaximal_hurwitz⟩
  hD := GL2TF.Quat.pizer_algebras.1

/-- `ι_3` for the Hurwitz order is unique up to `GL₂(ℚ_3)`-conjugation. -/
example (ι' : GL2TF.Quat.QuatAlg ℚ_[3] (-1) (-1) ≃ₐ[ℚ_[3]] Matrix (Fin 2) (Fin 2) ℚ_[3]) :
    ∃ g : GL (Fin 2) ℚ_[3], ∀ y, ι' y = g * hurwitzDataL2.iota 3 (by decide) y * g⁻¹ :=
  hurwitzDataL2.iota_conj 3 (by decide) ι'

/-- The conjugating matrix for `ι_3` against itself exists (sanity). -/
example : ∃ g : GL (Fin 2) ℚ_[3], ∀ y,
    hurwitzDataL2.iota 3 (by decide) y = g * hurwitzDataL2.iota 3 (by decide) y * g⁻¹ :=
  localSplitting_conj _ _
