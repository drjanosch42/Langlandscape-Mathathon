import AlgJL.VolI.P0.Decompositions

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P0/Decompositions.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolI.P0.Decompositions`

Non-vacuity examples and proved instances (PLAN.md §2.3).
-/

open GL2TF.Local

namespace GL2TFTests

/-- `t_{0,0} = 1`: the Cartan element is the expected diagonal matrix in the simplest case. -/
theorem cartanElement_zero_zero (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F] :
    cartanElement F 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartanElement]

/-- The Cartan element over `ℚ_[p]` (the definition is instantiated at the model NALF). -/
example (p : ℕ) [Fact p.Prime] : cartanElement ℚ_[p] 0 0 = 1 := cartanElement_zero_zero ℚ_[p]

/-- The height map unfolds to `(log|det g|_𝔸 − log‖e₂ g‖_𝔸, log‖e₂ g‖_𝔸)`. -/
theorem heightMap_eq (g : GL (Fin 2) GL2TF.Adele) :
    GL2TF.heightMap g = ![Real.log (GL2TF.ideleNorm (Matrix.GeneralLinearGroup.det g)) -
        Real.log (GL2TF.bottomRowNorm g), Real.log (GL2TF.bottomRowNorm g)] :=
  rfl

end GL2TFTests
