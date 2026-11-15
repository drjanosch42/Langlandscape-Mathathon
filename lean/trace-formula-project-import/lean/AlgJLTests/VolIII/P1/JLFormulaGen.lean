import AlgJL.VolIII.P1.JLFormulaGen

/-!
# Tests for `GL2TF.VolIII.P1.JLFormulaGen`

Kernel-checked values (`decide +kernel`; no `native_decide`) of the five general expressions of unit JLG, at the
golden data of item 41 (`D = 11`, `k = 2`, `n = 1`): the trivial parameters `F ≡ 1`, `β ≡ 1`, `κ = c = 1` reproduce
`Λ^{ES}(1, 2, 1; 1) = 1` and `E^𝔹(11, 1, 2, 1; 1) = 2`.
-/

namespace GL2TFTests

open GL2TF.Explicit

/-- `A₂^E(2, 1; 1) = −½(h_w(−4) + 2 h_w(−3)) = −7/12`. -/
theorem eichlerEllipticGen_value : eichlerEllipticGen 2 1 (fun _ _ _ ↦ 1) = -7 / 12 := by
  decide +kernel

/-- `A₃^β(2, 2) = −½(1 + 1) = −1` and `A₃^β(2, 1) = −½` for `β ≡ 1`. -/
theorem cohenA3Gen_value : cohenA3Gen 2 2 (fun _ _ ↦ 1) = -1 ∧ cohenA3Gen 2 1 (fun _ _ ↦ 1) = -1 / 2 := by
  decide +kernel

/-- `Ẽis^β(2, 2) = σ₁(2) = 3` for `β ≡ 1`, and `Ẽis^β(2, 2) = 2 + 2·1 = 4` for `β(a, a') = a`. -/
theorem eisensteinCorrectedGen_value :
    eisensteinCorrectedGen 2 2 (fun _ _ ↦ 1) = 3 ∧ eisensteinCorrectedGen 2 2 (fun a _ ↦ (a : ℚ)) = 4 := by
  decide +kernel

/-- `Λ^{ES}(2, 1; 1, 1, 1) = Λ^{ES}(1, 2, 1; 1) = 1` (item 41). -/
theorem lefschetzESGen_value : lefschetzESGen 2 1 1 (fun _ _ _ ↦ 1) (fun _ _ ↦ 1) = 1 := by
  decide +kernel

/-- `E^𝔹(11, 2, 1; 1, 1) = E^𝔹(11, 1, 2, 1; 1) = 2` (item 41), and the central term alone at `c = 0`, `F ≡ 0` is `0`. -/
theorem eichlerBGen_value :
    eichlerBGen 11 2 1 1 (fun _ _ _ ↦ 1) = 2 ∧ eichlerBGen 11 2 1 0 (fun _ _ _ ↦ 0) = 0 := by
  decide +kernel

/-! ### G1 finding m-4: the `(t, f)` slots of `F` are pinned

`jlgTestF t f Δ = [t = 1] + 10·[f = 2] + 100·[Δ = −12]` separates the three slots. At `n = 3` (`k = 2`, `P_2 = 1`) the pairs are
`(0, 1; −12)`, `(0, 2; −3)`, `(±1, 1; −11)`, `(±2, 1; −8)`, `(±3, 1; −3)` with `h_w = 1, 1/3, 1, 1, 1/3`, so only `(1, 1)`, `(0, 2)` and
`(0, 1)` contribute. A permutation of the slots changes every value below. -/

/-- The closed test parameter of finding m-4. -/
def jlgTestF : ℤ → ℕ → ℤ → ℚ := fun t f Δ ↦
  (if t = 1 then 1 else 0) + 10 * (if f = 2 then 1 else 0) + 100 * (if Δ = -12 then 1 else 0)

/-- `A₂^E(2, 3; jlgTestF) = −½(1·1 + 10·⅓ + 100·1) = −313/6`. -/
theorem eichlerEllipticGen_slots : eichlerEllipticGen 2 3 jlgTestF = -313 / 6 := by
  decide +kernel

/-- `Λ^{ES}(2, 3; 0, jlgTestF, 0) = σ₁(3) − 2(−313/6 + σ₁(3)) + σ₁(3) = 313/3`. -/
theorem lefschetzESGen_slots : lefschetzESGen 2 3 0 jlgTestF (fun _ _ ↦ 0) = 313 / 3 := by
  decide +kernel

/-- `E^𝔹(11, 2, 3; 0, jlgTestF) = ½·1·1 + ⅙·2·10 + ½·2·100 = 623/6` (`m^D_{11}(−11) = 1`, `m^D_{11}(−3) = m^D_{11}(−12) = 2`). -/
theorem eichlerBGen_slots : eichlerBGen 11 2 3 0 jlgTestF = 623 / 6 := by
  decide +kernel

/-- A fully applied instance of `III.ef.thm:jl-formula-identity-general` (`D = 11`, `k = 2`, `n = 3`, `c = 0`, `F = jlgTestF`,
`G ≡ 1`). -/
theorem jl_formula_identity_general_d11 :
    eichlerBGen 11 2 3 0 jlgTestF =
      -(1 / 2 : ℚ) * ∑ d ∈ (11 : ℕ).divisors, (-2 : ℚ) ^ ArithmeticFunction.cardDistinctFactors (11 / d) *
        lefschetzESGen 2 3 (dedekindPsi d * 0)
          (fun t f Δ ↦ jlgTestF t f Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ))
          (fun a a' ↦ (2 : ℚ) ^ ArithmeticFunction.cardDistinctFactors d * (fun _ _ ↦ (1 : ℚ)) a a') :=
  jl_formula_identity_general 11 2 3 0 jlgTestF (fun _ _ ↦ 1) (by decide : Nat.Prime 11).squarefree
    (by rw [ArithmeticFunction.cardDistinctFactors_apply_prime (by decide : Nat.Prime 11)]; decide)

end GL2TFTests
