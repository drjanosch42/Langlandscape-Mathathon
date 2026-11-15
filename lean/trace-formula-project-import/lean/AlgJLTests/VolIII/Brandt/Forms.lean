import AlgJL.VolIII.Brandt.Forms

/-!
# Tests for `GL2TF.VolIII.Brandt.Forms`

Named test declarations for the tagged definitions of Q3 items 11, 14 and the B-only `classOf`.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `classOf` is Mathlib's double-coset map. -/
theorem classOf_eq {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) :
    classOf O x = DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x := rfl

/-- The zero function is a quaternionic form. -/
theorem zero_mem_quatForms {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (k : ℕ) : (0 : (BHat a b)ˣ → symPowerModule K (k - 2)) ∈ quatForms O s k :=
  Submodule.zero_mem _

/-- The constant form takes the value `1`. -/
theorem constantForm_apply {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (x : (BHat a b)ˣ) :
    (((constantForm O s : (BHat a b)ˣ → symPowerModule K (2 - 2)) x : symPowerModule K (2 - 2)) :
      MvPolynomial (Fin 2) K) = 1 := rfl

end GL2TFTests
