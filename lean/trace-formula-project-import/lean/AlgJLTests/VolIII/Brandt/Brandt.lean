import AlgJL.VolIII.Brandt.Brandt

/-!
# Tests for `GL2TF.VolIII.Brandt.Brandt`

Named test declaration for the tagged definition of Q3 item 38.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- The entries of `B(n)` are coset counts (definitional unfolding). -/
theorem brandtMatrix_apply {a b : ℤ} (O : QOrder a b) (n : ℕ) (c c' : classSet O) :
    brandtMatrix O n c c' = Nat.card {q : (BHat a b)ˣ ⧸ orderCompletionUnits O //
      ∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = q ∧
        classOf O (Quotient.out c * y) = c'} := rfl

end GL2TFTests
