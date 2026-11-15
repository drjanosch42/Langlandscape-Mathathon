import AlgJL.Common.HeckeModule

/-!
# Tests for `GL2TF.Common.HeckeModule`

Named test declarations for the tagged definitions of Q3 items 21, 21a (`X.hmod`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.HeckeModule

/-- The zero function is equivariant. -/
theorem zero_mem_equivariantFunctions {G Γ : Type*} [Group G] [Group Γ] (R : Type*) [CommRing R] {V : Type*}
    [AddCommGroup V] [Module R V] (ι : Γ →* G) (U : Subgroup G) (ρ : Γ → Module.End R V) :
    (0 : G → V) ∈ equivariantFunctions R ι U ρ :=
  Submodule.zero_mem _

/-- The zero function acts by zero. -/
theorem heckeAct_zero_left {G : Type*} [Group G] (U : Subgroup G) {R₀ : Type*} [CommRing R₀] {V : Type*}
    [AddCommGroup V] [Module R₀ V] (f : G → V) :
    heckeAct (U := U) (0 : G → R₀) f = 0 := by
  funext x
  simp [heckeAct]

end GL2TFTests
