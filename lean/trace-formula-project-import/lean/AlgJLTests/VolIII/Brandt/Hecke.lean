import AlgJL.VolIII.Brandt.Hecke

/-!
# Tests for `GL2TF.VolIII.Brandt.Hecke`

Named test declarations for the tagged definitions of Q3 items 19, 23.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `1 ∈ Ô_1`. -/
theorem one_mem_normNSet_one {a b : ℤ} (O : QOrder a b) : (1 : (BHat a b)ˣ) ∈ normNSet O 1 := by
  refine ⟨one_mem_orderCompletion O, 1, ?_⟩
  show nrd (1 : QuatAlg GL2TF.FinAdele a b) = _
  simp [nrd]

/-- `T_n` sends the zero function to zero. -/
theorem heckeOperator_zero_fun {a b : ℤ} (O : QOrder a b) (n : ℕ) {V : Type*} [AddCommGroup V] :
    heckeOperator O n (0 : (BHat a b)ˣ → V) = 0 := by
  funext x
  simp [heckeOperator, GL2TF.HeckeModule.heckeAct]

end GL2TFTests
