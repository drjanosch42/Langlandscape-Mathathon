import AlgJL.VolIII.P2.Compact

/-!
# Tests for `GL2TF.VolIII.P2.Compact`

Named test declarations for the tagged definitions of Q2 item 57 (`AdelicQuat`) and its B-only plumbing
(`QuatInf`, the ring and topology instances, `adelicEmbed`, `nrdHom`, `adelicNrd`, `adelicNormOne`, `adelicDiagonal`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat

/-- The ring and topology of `B_𝔸`: `x * 1 = x` and the identity is continuous. -/
theorem adelicQuat_ring_topology (a b : ℤ) :
    (∀ x : AdelicQuat a b, x * 1 = x) ∧ Continuous (id : AdelicQuat a b → AdelicQuat a b) :=
  ⟨mul_one, continuous_id⟩

/-- The ring and topology of `B_∞`: `x * 1 = x` and the identity is continuous. -/
theorem quatInf_ring_topology (a b : ℤ) :
    (∀ x : QuatInf a b, x * 1 = x) ∧ Continuous (id : QuatInf a b → QuatInf a b) :=
  ⟨mul_one, continuous_id⟩

/-- `nrd(i) = −a` in `B_ℚ`, through `nrdHom`. -/
theorem nrdHom_i (a b : ℤ) : nrdHom ℚ a b ⟨0, 1, 0, 0⟩ = -(a : ℚ) := by
  simp [nrdHom, nrd]

/-- `ι_𝔸(1) = 1` and `nrd(1) = 1` on `B_𝔸^×`. -/
theorem adelicEmbed_adelicNrd_one (a b : ℤ) : adelicEmbed a b 1 = 1 ∧ adelicNrd a b 1 = 1 :=
  ⟨map_one _, map_one _⟩

/-- `1 ∈ B_𝔸^1` and `1 ∈ Γ_B`. -/
theorem one_mem_adelicNormOne_diagonal (a b : ℤ) :
    (1 : (AdelicQuat a b)ˣ) ∈ adelicNormOne a b ∧ (1 : adelicNormOne a b) ∈ adelicDiagonal a b :=
  ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

end GL2TFTests
