/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.ControlAbstract

/-! Non-vacuity and shape tests for `Langlandscape.Ordinary.ControlAbstract` (S04-L8). -/

@[expose] public section

set_option autoImplicit false

namespace LanglandscapeTests.S04.ControlAbstract

open Langlandscape.Ordinary Representation

/-- `5` is prime (test data, `s04-hida`). -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `lem:s04-hida`(c) (`s04-hida`), use case `R = ℤ_[p]`: `R[Y]_H ≃ R[Y⧸H]` sends the class of
`[y]` to `[H y]`. -/
theorem coinvEquivOrbits_padic (H Y : Type) [Group H] [MulAction H Y] (y : Y) :
    coinvEquivOrbits ℤ_[5] H Y (Coinvariants.mk (permRep ℤ_[5] H Y) (Finsupp.single y 1)) =
      Finsupp.single (Quotient.mk (MulAction.orbitRel H Y) y) 1 :=
  coinvEquivOfFibres_mk_single _ _ _ y 1

/-- `lem:s04-hida`(c) (`s04-hida`), sanity check: the identity map is a surjective equivariant map
whose kernel is killed by `T`, and the induced isomorphism of ordinary parts is the identity. -/
theorem ordPartEquivOfSurjective_id {M : Type} [AddCommGroup M] [Module ℤ_[5] M]
    (T : Module.End ℤ_[5] M) (h : HasOrdDecomp (5 : ℤ_[5]) T) (x : ordPart T) :
    (ordPartEquivOfSurjective (5 : ℤ_[5]) LinearMap.id Function.surjective_id
        (by rw [LinearMap.id_comp, LinearMap.comp_id])
        (fun x hx => by rw [show x = 0 from hx, map_zero]) h h x : M) = x :=
  rfl

/-- `lem:s04-hida`(d), rank (`s04-hida`), sanity check on the trivial base change
`ℤ_[p] ⊗_{ℤ_[p]} ℤ_[p]² ≃ ℤ_[p]²`. -/
theorem finrank_eq_of_baseChange_lid :
    Module.finrank ℤ_[5] (Fin 2 → ℤ_[5]) = Module.finrank ℤ_[5] (Fin 2 → ℤ_[5]) :=
  finrank_eq_of_baseChange (TensorProduct.lid ℤ_[5] (Fin 2 → ℤ_[5]))

/-- `lem:s04-hida`(d) (`s04-hida`), shape: for a constant tower the rank is constant. -/
theorem finrank_const_of_baseChange_const (s : ℕ) :
    Module.finrank ℤ_[5] (Fin 2 → ℤ_[5]) = Module.finrank ℤ_[5] (Fin 2 → ℤ_[5]) :=
  finrank_const_of_baseChange (A := fun _ => ℤ_[5]) (M := fun _ => Fin 2 → ℤ_[5])
    (fun _ => TensorProduct.lid ℤ_[5] (Fin 2 → ℤ_[5])) s

end LanglandscapeTests.S04.ControlAbstract
