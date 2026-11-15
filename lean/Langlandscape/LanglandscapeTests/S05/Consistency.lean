/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Consistency

/-!
# Tests for `Langlandscape.Comparison.Consistency` (S05-L5)

Shape tests for `theta_adjoint_T_degZero`, `theta_adjoint_Uq_degZero`, `projection_formula_two`,
`Up_comm_pushforward_degZero`.
-/

set_option autoImplicit false

namespace Langlandscape.Comparison.Tests

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

section Adjoint

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `lem:s05-consistency`(b) (`s05-consistency`), test: the adjoint of `θ(T_ℓ)` on `degZero`. -/
theorem test_theta_adjoint_T_degZero (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ M * p * q)
    (x y : degZero (d.Utower M p s hN) ℤ) :
    brandtPairingDeg (d.Utower M p s hN) ℤ
        (theta d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) x) y =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ)
        (SlInvHom d (d.Utower M p s hN) ℓ (not_dvd_D_of_T d M p q hD hℓN) ℤ
          (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) (y : ZX (d.Utower M p s hN) ℤ))) :=
  theta_adjoint_T_degZero d M p q s hN hp hM hpM hD Pq hPq ℓ hℓN x y

/-- `lem:s05-consistency`(b) (`s05-consistency`), test: the adjoint of `θ(U_q)` on `degZero`. -/
theorem test_theta_adjoint_Uq_degZero (x y : degZero (d.Utower M p s hN) ℤ) :
    brandtPairingDeg (d.Utower M p s hN) ℤ
        (theta d M p q s hN hp hM hpM hD Pq hPq .Uq x) y =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ)
        (PiEllHom ℤ d q hPq.dvd Pq⁻¹ (d.Utower M p s hN) (y : ZX (d.Utower M p s hN) ℤ)) :=
  theta_adjoint_Uq_degZero d M p q s hN hp hM hpM hD Pq hPq x y

end Adjoint

section Projection

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `lem:s05-consistency`(c) (`s05-consistency`), test: the projection formula with the factor 2. -/
theorem test_projection_formula_two [Finite (XB U)] (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (h1 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) (h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U')
    (x : ZX U' R) (y : ZX U R) :
    (2 : R) * brandtPairing U R (pushforward U' U R x) y =
      evalPairing U R y (trace U' U R hrel (normMap U' R x)) :=
  projection_formula_two U' U R hle hrel h1 h2 x y

/-- `lem:s05-consistency`(d) (`s05-consistency`), test: `π_*` preserves the degree. -/
theorem test_deg_pushforward (x : ZX U' R) :
    Ordinary.deg (XB U) R (pushforward U' U R x) = Ordinary.deg (XB U') R x :=
  deg_pushforward U' U R x

end Projection

section UpComm

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hN' : (M * p ^ (s + 1)).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `lem:s05-consistency`(d) (`s05-consistency`), test: `π_* ∘ θ(U_p) = θ(U_p) ∘ π_*` on `degZero`. -/
theorem test_Up_comm_pushforward_degZero (hs : 1 ≤ s) :
    pushDegZero (d.Utower M p (s + 1) hN') (d.Utower M p s hN) ℤ ∘ₗ
        theta d M p q (s + 1) hN' hp hM hpM hD Pq hPq (.Up (Nat.le_add_left 1 s)) =
      theta d M p q s hN hp hM hpM hD Pq hPq (.Up hs) ∘ₗ
        pushDegZero (d.Utower M p (s + 1) hN') (d.Utower M p s hN) ℤ :=
  Up_comm_pushforward_degZero d M p q s hN hN' hp hM hpM hD Pq hPq hs

end UpComm

end Langlandscape.Comparison.Tests
