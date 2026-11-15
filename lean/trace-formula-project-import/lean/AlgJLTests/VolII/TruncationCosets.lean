import AlgJL.VolII.TruncationCosets

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolII/TruncationCosets.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolII.TruncationCosets` (M9a, U0–U1)

`B(ℚ) ∩ G(𝔸)^1` contains `1`; in `borelCosets` the class of `βδ` is the class of `δ` for `β ∈ B(ℚ)` (the cosets are the right
cosets `B(ℚ)δ`).
-/

open GL2TF

namespace GL2TFTests

/-- `1 ∈ B(ℚ)` as a subgroup of `G(𝔸)^1`. -/
theorem one_mem_borelRatNormOne : (1 : normOneGroup) ∈ borelRatNormOne :=
  borelRatNormOne.one_mem

/-- `B(ℚ)βδ = B(ℚ)δ` for `β ∈ B(ℚ)`: the classes of `borelCosets` are right cosets. -/
theorem borelCosets_mk_borel_mul (β δ : gl2RatNormOne) (hβ : β ∈ borelRatNormOne.subgroupOf gl2RatNormOne) :
    (Quotient.mk _ (β * δ) : borelCosets) = Quotient.mk _ δ :=
  Quotient.sound ⟨⟨β, hβ⟩, rfl⟩

end GL2TFTests
