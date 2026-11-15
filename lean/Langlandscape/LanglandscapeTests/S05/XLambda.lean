/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.XLambda

/-!
# Tests for `Langlandscape.Comparison.XLambda` (S05-L7)

Shape tests for `xlambda_finite_iso` and `xlambda_finite`, applied to a given `Hyp.X.char` hypothesis.
-/

set_option autoImplicit false

namespace Langlandscape.Comparison.Tests

open Langlandscape.Quat Langlandscape.Brandt
open scoped TensorProduct Classical

section Main

variable (d : DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
  (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
  (hD : d.D = q) (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)
  (G : Langlandscape.Hyp.X.CharGroupData M q p)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), test: `xlambda_finite_iso` applied to a hypothesis `Hyp.X.char`. -/
theorem test_xlambda_finite_iso
    (hX : Langlandscape.Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) (s : ℕ) (hs : 1 ≤ s) :
    ∃ Ψ : ℤ_[p] ⊗[ℤ] G.X s ≃ₗ[ℤ_[p]] degZero (d.Utower M p s (hN s)) ℤ_[p],
      ∀ t : ℤ_[p] ⊗[ℤ] G.X s,
        ((Ψ ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p] t) :
            degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
          UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]
            ((Ψ t : degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) :=
  xlambda_finite_iso d M p q hN hp hM hpM hD Pq hPq G hX s hs

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), test: `xlambda_finite` applied to a hypothesis `Hyp.X.char`. -/
theorem test_xlambda_finite
    (hX : Langlandscape.Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) (s : ℕ) (hs : 1 ≤ s) :
    Nonempty (Ordinary.ordPart ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p]) ≃ₗ[ℤ_[p]]
      Ordinary.ordPart (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p])) :=
  xlambda_finite d M p q hN hp hM hpM hD Pq hPq G hX s hs

end Main

end Langlandscape.Comparison.Tests
