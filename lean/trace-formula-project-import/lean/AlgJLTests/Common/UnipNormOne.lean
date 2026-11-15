import AlgJL.Common.UnipNormOne

/-!
# Tests for `GL2TF.Common.UnipNormOne`

algebraic_jl fork (L-A, 2026-11-14): the test `unipNormOne_zero` is copied verbatim from
`lean/GL2TFTests/VolII/Geometric.lean` @84818d0 (that module is not part of the fork).
-/

open GL2TF

namespace GL2TFTests

/-- `n(0) = 1`. -/
theorem unipNormOne_zero : unipNormOne 0 = 1 := Subtype.ext (AddChar.map_zero_eq_one _)

end GL2TFTests
