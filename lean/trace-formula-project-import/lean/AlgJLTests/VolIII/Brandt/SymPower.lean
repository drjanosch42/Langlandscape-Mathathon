import AlgJL.VolIII.Brandt.SymPower

/-!
# Tests for `GL2TF.VolIII.Brandt.SymPower`

Named test declarations for the tagged definitions of Q3 items 1, 2, 4a, 5 and their B-only plumbing.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat MvPolynomial

/-- `P_2 = 1` over any commutative ring. -/
theorem heckePolyRing_two {R : Type*} [CommRing R] (t n : R) : heckePolyRing 2 t n = 1 := rfl

/-- `P_3(t, n) = t` over any commutative ring. -/
theorem heckePolyRing_three {R : Type*} [CommRing R] (t n : R) : heckePolyRing 3 t n = t := by
  simp [heckePolyRing]

/-- The constant `1` lies in `V_0(K)`. -/
theorem one_mem_symPowerModule_zero (K : Type*) [Field K] : (1 : MvPolynomial (Fin 2) K) ∈ symPowerModule K 0 :=
  isHomogeneous_one _ _

/-- The substitution of the identity matrix sends `x` to `x`. -/
theorem linSubst_one_zero (K : Type*) [Field K] : linSubst (1 : Matrix (Fin 2) (Fin 2) K) 0 = X 0 := by
  simp [linSubst]

/-- `ρ_m(A)` is the restriction of the substitution `aeval (linSubst A)`. -/
theorem symPowerAction_apply (K : Type*) [Field K] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (v : symPowerModule K m) :
    (symPowerAction K m A v : MvPolynomial (Fin 2) K) = aeval (linSubst A) (v : MvPolynomial (Fin 2) K) := rfl

/-- The exponent of `u_0 = x^m`. -/
theorem symExp_zero (m : ℕ) : symExp m 0 = Finsupp.single 0 m := by
  simp [symExp]

/-- `β_m(0, w) = 0`. -/
theorem symPowerPairing_zero_left (K : Type*) [Field K] (m : ℕ) (w : symPowerModule K m) :
    symPowerPairing K m 0 w = 0 := by
  simp

end GL2TFTests
