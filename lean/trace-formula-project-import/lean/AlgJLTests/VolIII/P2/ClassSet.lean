import AlgJL.VolIII.P2.ClassSet

/-!
# Tests for `GL2TF.VolIII.P2.ClassSet`

Named test declarations for the tagged definitions of Q2 items 42 (`classSet`) and 49 (`classStabilizer`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- The class set is nonempty: it contains the class `[1]`. -/
theorem classSet_nonempty {a b : ℤ} (O : QOrder a b) : Nonempty (classSet O) :=
  ⟨DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) 1⟩

/-- `1 ∈ Γ_x(U)` for every subgroup `U ≤ B̂^×` and every `x ∈ B̂^×`. -/
theorem one_mem_classStabilizer {a b : ℤ} (U : Subgroup (BHat a b)ˣ) (x : (BHat a b)ˣ) :
    (1 : (QuatAlg ℚ a b)ˣ) ∈ classStabilizer U x :=
  Subgroup.one_mem _

/-- `Γ_1(Ô^×) = ι⁻¹(Ô^×)`: for `x = 1` the conjugation is trivial, so `γ ∈ Γ_1` iff `ι(γ) ∈ Ô^×`. -/
theorem mem_classStabilizer_one {a b : ℤ} (O : QOrder a b) (γ : (QuatAlg ℚ a b)ˣ) :
    γ ∈ classStabilizer (orderCompletionUnits O) 1 ↔
      Units.map (finEmbed a b).toMonoidHom γ ∈ orderCompletionUnits O := by
  simp [classStabilizer]

end GL2TFTests
