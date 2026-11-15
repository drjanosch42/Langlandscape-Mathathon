import AlgJL.VolIII.P1.Boundary

/-!
# Tests for `GL2TF.VolIII.P1.Boundary`

`Boundary` has no tagged definition. Value lemma for the exit `III.ef.thm:boundary-local-factor` (plan §2.2 trap 12: exit 26
at `p = 2`, `e = 4`, a concrete `m`): `c_{16}(4) = 6`, against which the right side of item 26(a) gives `1 + 1 + 2 + 1 + 1`.
-/

open GL2TF.Explicit
open scoped ArithmeticFunction.omega

namespace GL2TFTests

/-- `c_{16}(4) = 6`: the divisors `τ = 1, 2, 4, 8, 16` give `gcd(τ, 16/τ) = 1, 2, 4, 2, 1`, all dividing `4`. -/
theorem boundaryDivisorSum_sixteen_four : boundaryDivisorSum 16 4 = 6 := by
  decide

/-- `c_{16}(2) = 4`: the divisor `τ = 4` drops out (`4 ∤ 2`). -/
theorem boundaryDivisorSum_sixteen_two : boundaryDivisorSum 16 2 = 4 := by
  decide

/-- Witness datum of exit 26: the argument `m = 4` (even, and divisible by `4`, so the terms with `min(j, e − j) = 1`
and `= 2` both count at `p = 2`, `e = 4`). -/
def boundaryWitnessM : ℤ := 4

/-- Exit 26 at `m = boundaryWitnessM`: its whole conclusion, and clause (a) specialised at `p = 2`, `e = 4`
(`c_{16}(4) = 6 = 1 + 1 + 2 + 1 + 1`, `boundaryDivisorSum_sixteen_four`). -/
theorem boundary_local_factor_witness :
    ((∀ p e : ℕ, p.Prime →
      boundaryDivisorSum (p ^ e) boundaryWitnessM =
        ∑ j ∈ Finset.range (e + 1),
          if ((p ^ min j (e - j) : ℕ) : ℤ) ∣ boundaryWitnessM then Nat.totient (p ^ min j (e - j)) else 0) ∧
      (∀ p : ℕ, p.Prime → boundaryDivisorSum p boundaryWitnessM = 2) ∧
      (∀ N : ℕ, Squarefree N → boundaryDivisorSum N boundaryWitnessM = 2 ^ ω N)) ∧
    boundaryDivisorSum (2 ^ 4) boundaryWitnessM =
      ∑ j ∈ Finset.range (4 + 1),
        if ((2 ^ min j (4 - j) : ℕ) : ℤ) ∣ boundaryWitnessM then Nat.totient (2 ^ min j (4 - j)) else 0 :=
  ⟨boundary_local_factor boundaryWitnessM, (boundary_local_factor boundaryWitnessM).1 2 4 Nat.prime_two⟩

/-- The datum is non-degenerate for clause (a) at `p = 2`, `e = 4`: both sides equal `6`, and the term
`j = 2` (`min = 2`, `φ(4) = 2`) counts. -/
theorem boundary_local_factor_witness_value :
    boundaryDivisorSum (2 ^ 4) boundaryWitnessM = 6 ∧
      (∑ j ∈ Finset.range (4 + 1),
        if ((2 ^ min j (4 - j) : ℕ) : ℤ) ∣ boundaryWitnessM then Nat.totient (2 ^ min j (4 - j)) else 0) = 6 := by
  decide

end GL2TFTests
