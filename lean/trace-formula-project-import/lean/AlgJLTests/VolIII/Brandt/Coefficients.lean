import AlgJL.VolIII.Brandt.Coefficients

/-!
# Tests for `GL2TF.VolIII.Brandt.Coefficients`

Named test declarations for the tagged definitions of Q3 items 7, 7a, 9, 10 and their B-only plumbing.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- A splitting sends `1` to the identity matrix. -/
theorem splitting_map_one {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b) : s 1 = 1 :=
  map_one s

/-- `ρ_k^s(γ) = ρ_{k−2}(s(γ))` (definitional unfolding). -/
theorem splitRep_eq {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b) (k : ℕ) (γ : QuatAlg ℚ a b) :
    splitRep s k γ = symPowerAction K (k - 2) (s γ) := rfl

/-- The image of `i` in model (c) is `diag(s₀, −s₀)`. -/
theorem standardSplittingBasis_i (K : Type*) [Field K] [CharZero K] (a b : ℤ) (s₀ : K) (hs₀ : s₀ ^ 2 = (a : K)) :
    (standardSplittingBasis K a b s₀ hs₀).i = !![s₀, 0; 0, -s₀] := rfl

/-- Model (c) is unital. -/
theorem standardSplitting_one (K : Type*) [Field K] [CharZero K] (a b : ℤ) (s₀ : K) (hs₀ : s₀ ^ 2 = (a : K)) :
    standardSplitting K a b s₀ hs₀ 1 = 1 :=
  map_one _

/-- Model (a) is unital. -/
theorem ellAdicSplitting_one {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hD : RamifiedExactly a b D) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓD : ¬ ℓ ∣ D) : ellAdicSplitting O hD ℓ hℓD 1 = 1 :=
  map_one _

end GL2TFTests
