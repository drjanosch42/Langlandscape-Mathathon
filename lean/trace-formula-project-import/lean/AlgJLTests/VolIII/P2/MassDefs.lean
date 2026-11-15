import AlgJL.VolIII.P2.MassDefs

/-!
# Tests for `GL2TF.VolIII.P2.MassDefs`

Named test declaration for the tagged definition of Q2 item 51 (`mass`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `Mass(O)` unfolds to the finite sum of `1/|Γ_{x_c}|` over the class set (full stabilizers, row N4). -/
theorem mass_eq_finsum {a b : ℤ} (O : QOrder a b) :
    mass O = ∑ᶠ c : classSet O,
      (1 : ℚ) / (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : ℚ) :=
  rfl

end GL2TFTests
