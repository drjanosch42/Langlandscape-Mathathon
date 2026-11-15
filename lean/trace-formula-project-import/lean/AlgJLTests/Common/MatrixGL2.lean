import AlgJL.Common.MatrixGL2

/-!
# Tests for `GL2TF.Common.MatrixGL2`

Non-vacuity examples (PLAN.md §2.3): the product σ-algebra on matrices makes the coordinates measurable, and
`GL n F` gets Mathlib's units σ-algebra from it.
-/

namespace GL2TFTests

/-- Each matrix entry is measurable for the product σ-algebra. -/
theorem measurable_matrix_entry {m n α : Type*} [MeasurableSpace α] (i : m) (j : n) :
    Measurable (fun X : Matrix m n α ↦ X i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- `Units.val : GL n F → Matrix n n F` is measurable. -/
theorem measurable_gl_val (n F : Type*) [Fintype n] [DecidableEq n] [Field F] [MeasurableSpace F] :
    Measurable (Units.val : GL n F → Matrix n n F) :=
  fun _ hs ↦ ⟨_, hs, rfl⟩
