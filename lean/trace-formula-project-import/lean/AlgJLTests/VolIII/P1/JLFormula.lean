import AlgJL.VolIII.P1.JLFormula
import AlgJL.VolIII.P1.CohenLocal

/-!
# Tests for `GL2TF.VolIII.P1.JLFormula`

Witness for the B-only definition `d2WeightH0` (item 43): `H₀(Δ) = 0` for `Δ ≥ 0` (no decomposition `Δ = Δ₀m²` with
`Δ₀ < 0`, `m ≥ 1`), in particular `H₀(0) = 0`. Its nonzero values (`H₀(−3) = 1`) are part of item 43 itself.
-/

open GL2TF.Explicit
open scoped ArithmeticFunction.omega

namespace GL2TFTests

/-- `H₀(Δ) = 0` for `Δ ≥ 0`. -/
theorem d2WeightH0_of_nonneg (Δ : ℤ) (hΔ : 0 ≤ Δ) : d2WeightH0 Δ = 0 := by
  unfold d2WeightH0
  split_ifs with h
  · exfalso
    obtain ⟨Δ₀, m, h0, -, -, hm, rfl⟩ := h
    have : (0 : ℤ) < (m : ℤ) ^ 2 := pow_pos (by exact_mod_cast hm) 2
    nlinarith
  · rfl

/-- `H₀(0) = 0`. -/
theorem d2WeightH0_zero : d2WeightH0 0 = 0 :=
  d2WeightH0_of_nonneg 0 le_rfl

/-- Shape guard: `III.ef.thm:d2-sum-form` applied to `H = H₀`, its hypothesis discharged by item 43 verbatim. -/
theorem d2_sum_form_d2WeightH0 {N : ℕ} (hN : Squarefree N) {t : ℤ} {n : ℕ} (htn : t ^ 2 < 4 * (n : ℤ)) :
    ∑ f ∈ orderIndexSet t n, d2WeightH0 ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * cohenMu N t f n =
      ∑ f ∈ orderIndexSet t n,
        d2WeightH0 ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) *
          ∏ p ∈ N.primeFactors, (localFactorEichler p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) :=
  d2_sum_form hN htn d2WeightH0 d2_weight_instance.1

/-! ### R2d witnesses for the exits `III.ef.thm:d2-sum-form` (23) and `III.ef.thm:jl-formula-identity` (39) -/

/-- Witness datum of exit 23: the closed weight `H₀` (item 43), as a Tests definition. -/
noncomputable def d2WitnessH : ℤ → ℚ := fun Δ ↦ d2WeightH0 Δ

/-- Exit 23 at `N = 3`, `t = −1`, `n = 7`, `H = d2WitnessH` (`𝓕(−1, 7) = {1, 3}`, `Δ_1 = −27`, `Δ_3 = −3`); the
hypothesis on `H` is item 43's first clause. Both sides equal `7` (`d2_sum_form_witness_value`). -/
theorem d2_sum_form_witness :
    ∑ f ∈ orderIndexSet (-1) 7, d2WitnessH (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) * cohenMu 3 (-1) f 7 =
      ∑ f ∈ orderIndexSet (-1) 7,
        d2WitnessH (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) *
          ∏ p ∈ (3 : ℕ).primeFactors,
            (localFactorEichler p (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) : ℚ) :=
  d2_sum_form (N := 3) Nat.prime_three.squarefree (t := -1) (n := 7) (by norm_num) d2WitnessH
    d2_weight_instance.1

/-- Uniqueness of the decomposition `−27 = Δ₀ m²` with `Δ₀ < 0` fundamental, `m ≥ 1`: `Δ₀ = −3`, `m = 3`. -/
theorem d2WeightH0_decomp_neg_27 (Δ₀ : ℤ) (m : ℕ) (h0 : Δ₀ < 0)
    (hc : ∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) (hm : 1 ≤ m) (he : (-27 : ℤ) = Δ₀ * (m : ℤ) ^ 2) :
    Δ₀ = -3 ∧ m = 3 := by
  have hm5 : m ≤ 5 := by
    by_contra h
    have : (36 : ℤ) ≤ (m : ℤ) ^ 2 := by nlinarith [(show (6 : ℤ) ≤ m by omega)]
    nlinarith
  interval_cases m <;> norm_num at he
  · have : Δ₀ = -27 := by omega
    subst this
    exact absurd (hc 3 Nat.prime_three) (by decide)
  · omega
  · exact ⟨by omega, rfl⟩
  · omega
  · omega

/-- Uniqueness of the decomposition `−3 = Δ₀ m²` with `Δ₀ < 0`, `m ≥ 1`: `Δ₀ = −3`, `m = 1`. -/
theorem d2WeightH0_decomp_neg_3 (Δ₀ : ℤ) (m : ℕ) (h0 : Δ₀ < 0) (hm : 1 ≤ m)
    (he : (-3 : ℤ) = Δ₀ * (m : ℤ) ^ 2) : Δ₀ = -3 ∧ m = 1 := by
  have hm1 : m ≤ 1 := by
    by_contra h
    have : (4 : ℤ) ≤ (m : ℤ) ^ 2 := by nlinarith [(show (2 : ℤ) ≤ m by omega)]
    nlinarith
  obtain rfl : m = 1 := by omega
  norm_num at he
  exact ⟨by omega, rfl⟩

/-- `H₀(−27) = 3` (`−27 = −3 · 3²`, `3⁰ · (3 − χ_{−3}(3)) = 3`), without item 43. -/
theorem d2WitnessH_neg_27 : d2WitnessH (-27) = 3 := by
  show d2WeightH0 (-27) = 3
  unfold d2WeightH0
  have hex : ∃ Δ₀ : ℤ, ∃ m : ℕ, Δ₀ < 0 ∧ (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) ∧ 1 ≤ m ∧ (-27 : ℤ) = Δ₀ * (m : ℤ) ^ 2 := by
    refine ⟨-3, 3, by norm_num, by decide, fun p hp => ?_, le_of_lt (by norm_num), by norm_num⟩
    unfold dividesConductor
    simp only [decide_eq_false_iff_not, not_and]
    intro h
    have h3 : (p : ℤ) ∣ 3 := (dvd_neg.mp (dvd_trans (dvd_pow_self _ two_ne_zero) h))
    have hp3 : p ∣ 3 := by exact_mod_cast h3
    have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst this
    exact absurd h (by decide)
  split_ifs
  obtain ⟨h0, -, hc, hm, he⟩ := hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := d2WeightH0_decomp_neg_27 _ _ h0 hc hm he
  rw [e2, e1, Nat.Prime.primeFactors Nat.prime_three, Finset.prod_singleton,
    Nat.Prime.factorization_self Nat.prime_three]
  have : kroneckerPrime (-3) 3 = 0 := by decide +kernel
  rw [this]
  norm_num

/-- `H₀(−3) = 1`, without item 43. -/
theorem d2WitnessH_neg_3 : d2WitnessH (-3) = 1 := by
  show d2WeightH0 (-3) = 1
  unfold d2WeightH0
  have hex : ∃ Δ₀ : ℤ, ∃ m : ℕ, Δ₀ < 0 ∧ (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) ∧ 1 ≤ m ∧ (-3 : ℤ) = Δ₀ * (m : ℤ) ^ 2 := by
    refine ⟨-3, 1, by norm_num, by decide, fun p hp => ?_, le_rfl, by norm_num⟩
    unfold dividesConductor
    simp only [decide_eq_false_iff_not, not_and]
    intro h
    have h3 : (p : ℤ) ∣ 3 := (dvd_neg.mp (dvd_trans (dvd_pow_self _ two_ne_zero) h))
    have hp3 : p ∣ 3 := by exact_mod_cast h3
    have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst this
    exact absurd h (by decide)
  split_ifs
  obtain ⟨h0, -, -, hm, he⟩ := hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := d2WeightH0_decomp_neg_3 _ _ h0 hm he
  rw [e2]
  simp

/-- Exit 23's witness data are non-degenerate: both sides equal `7`, termwise different
(`3 · 1 + 1 · 4` against `3 · 2 + 1 · 1`). Proved without item 43 or exit 23. -/
theorem d2_sum_form_witness_value :
    ∑ f ∈ orderIndexSet (-1) 7, d2WitnessH (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) * cohenMu 3 (-1) f 7 = 7 ∧
      ∑ f ∈ orderIndexSet (-1) 7,
        d2WitnessH (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) *
          ∏ p ∈ (3 : ℕ).primeFactors,
            (localFactorEichler p (((-1) ^ 2 - 4 * ((7 : ℕ) : ℤ)) / (f : ℤ) ^ 2) : ℚ) = 7 := by
  have hI : orderIndexSet (-1) 7 = {1, 3} := by decide +kernel
  have hμ1 : cohenMu 3 (-1) 1 7 = 1 := by decide +kernel
  have hμ3 : cohenMu 3 (-1) 3 7 = 4 := by decide +kernel
  have hl27 : localFactorEichler 3 (-27) = 2 := by decide +kernel
  have hl3 : localFactorEichler 3 (-3) = 1 := by decide +kernel
  rw [hI, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num),
    Nat.Prime.primeFactors Nat.prime_three]
  norm_num [Finset.prod_singleton, hμ1, hμ3, hl27, hl3, d2WitnessH_neg_27, d2WitnessH_neg_3]

/-- Witness datum of exit 39: the parameter `F(Δ) = Δ` (not constant, so the `F`-content of the elliptic terms is
exercised; the case `F = 1` is item 41). -/
def jlWitnessF : ℤ → ℚ := fun Δ ↦ (Δ : ℚ)

/-- Exit 39 at `D = 11`, `M = 1`, the even weight `k = 2` (at odd `k` the elliptic sums vanish for every `F`, G1 m-3),
`n = 3`, `F = jlWitnessF`. -/
theorem jl_formula_identity_witness :
    eichlerB 11 1 2 3 jlWitnessF =
      -(1 / 2 : ℚ) * ∑ d ∈ (11 : ℕ).divisors, (-2 : ℚ) ^ ω (11 / d) *
        lefschetzES (d * 1) 2 3 (fun Δ ↦ jlWitnessF Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) :=
  jl_formula_identity 11 1 2 3 jlWitnessF (Nat.prime_eleven.squarefree)
    (by rw [ArithmeticFunction.cardDistinctFactors_apply_prime Nat.prime_eleven]; decide)
    (Nat.coprime_one_right 11) (by norm_num) (by norm_num)

/-- Exit 39's witness datum is non-degenerate: the left side at `F = jlWitnessF` differs from its value `3`
at `F = 1` (golden value `eichlerB_golden`, item 41), so the `F`-content matters. Proved without exit 39. -/
theorem jl_formula_identity_witness_F_matters :
    eichlerB 11 1 2 3 jlWitnessF ≠ eichlerB 11 1 2 3 (fun _ => 1) := by
  decide +kernel

/-- Value support of exit 39 (G1 F2 R-1): the left side at the witness datum is `−26` (the elliptic sum alone, `n = 3`
not a square: `Δ = −12, −3` at `t = 0`, `−11` at `t = ±1`, `−8` at `t = ±2` with ramified factor `0`, `−3` at `t = ±3`).
Kernel computation, proved without exit 39. -/
theorem jl_formula_identity_witness_value : eichlerB 11 1 2 3 jlWitnessF = -26 := by
  decide +kernel

/-- The right side of exit 39 at the witness datum is also `−26`, computed without exit 39. -/
theorem jl_formula_identity_witness_value_rhs :
    -(1 / 2 : ℚ) * ∑ d ∈ (11 : ℕ).divisors, (-2 : ℚ) ^ ω (11 / d) *
        lefschetzES (d * 1) 2 3 (fun Δ ↦ jlWitnessF Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) =
      -26 := by
  decide +kernel

end GL2TFTests
