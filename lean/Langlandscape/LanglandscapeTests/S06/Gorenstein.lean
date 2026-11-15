/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein

/-! Non-vacuity tests for `Langlandscape.CommAlg.Gorenstein` (S06-L1): `A` is Gorenstein over
itself with trace `id`, and `η(A, id) = A`. -/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

/-- `ss:s06-ca` (`s06-ca`), test: `A` is `A`-Gorenstein, with trace `ℓ = id`. -/
theorem isGorenstein_self (A : Type*) [CommRing A] : IsGorenstein A A := by
  refine ⟨LinearMap.id, Module.Free.self A, Module.Finite.self A, ?_, ?_⟩
  · intro s t hst
    have h1 := LinearMap.congr_fun hst 1
    simpa using h1
  · intro φ
    refine ⟨φ 1, LinearMap.ext_ring ?_⟩
    simp

/-- `lem:s06-S` (`s06-S`), test: the congruence ideal of the identity `A → A` is the unit ideal. -/
theorem congruenceIdeal_id (A : Type*) [CommRing A] : congruenceIdeal (AlgHom.id A A) = ⊤ := by
  have hker : RingHom.ker (AlgHom.id A A) = ⊥ := by
    ext x
    simp [RingHom.mem_ker]
  have hann : ann (⊥ : Ideal A) = ⊤ := by
    ext x
    simp [mem_ann]
  unfold congruenceIdeal
  rw [hker, hann]
  exact Ideal.map_top _

end Langlandscape.CommAlg
