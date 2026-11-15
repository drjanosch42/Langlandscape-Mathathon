import AlgJL.VolIII.P2.Mass

/-!
# Tests for `GL2TF.VolIII.P2.Mass`

Mass.lean has no definitions (items 52–54, 56 are theorems); a named use of item 53 at `M = 1`.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat GL2TF.Explicit

/-- Item 53 at `M = 1`: `[GL₂(ℤ/1) : B₀(ℤ/1)] = ψ(1)`. -/
theorem gl2_borel_index_one : ((borel (ZMod 1)).index : ℚ) = dedekindPsi 1 :=
  gl2_borel_index 1 le_rfl

end GL2TFTests
