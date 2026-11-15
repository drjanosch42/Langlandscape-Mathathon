import AlgJL.Common.MatrixCalculus

/-!
# Tests for `GL2TF.Common.MatrixCalculus`

Non-vacuity examples and proved instances (PLAN.md §2.3).
-/

open GL2TF

namespace GL2TFTests

/-- The identity matrix lies in `{det ≠ 0}` (in the Pi-type matrix space `MatPi`). -/
theorem matToPi_one_mem_detNeZeroSet : matToPi (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ detNeZeroSet := by
  simp [detNeZeroSet, matToPi]

/-- `glExt f` restricts to `f` at the identity. -/
theorem glExt_matToPi_one (f : GL (Fin 2) ℝ → ℂ) :
    glExt f (matToPi ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = f 1 := by
  have h : IsUnit (Matrix.of (matToPi ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := (1 : GL (Fin 2) ℝ).isUnit
  rw [glExt, dite_eq_left h]
  congr 1
  ext : 1
  rfl

end GL2TFTests
