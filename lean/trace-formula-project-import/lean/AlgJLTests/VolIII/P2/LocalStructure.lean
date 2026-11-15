import AlgJL.VolIII.P2.LocalStructure

/-!
# Tests for `GL2TF.VolIII.P2.LocalStructure`

`localLattice` of the zero submodule.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- The completion of the zero submodule is zero: `(0)_p = 0` in `B_p`. -/
theorem localLattice_bot (a b : ℤ) (p : ℕ) [Fact p.Prime] :
    localLattice (a := a) (b := b) p ⊥ = ⊥ := by
  simp [localLattice]

end GL2TFTests
