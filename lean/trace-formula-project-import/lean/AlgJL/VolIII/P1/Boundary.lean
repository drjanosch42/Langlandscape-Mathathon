import AlgJL.Meta.Tag
import AlgJL.VolIII.P1.Normalization
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.NatDivisors

/-!
# Boundary sums (D3) and the Eisenstein expression (Q1, unit U4, items 25, 26, 29)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §5 (`sec:ef-boundary`). Owner: L2. Plan `docs/sprints/Q1-plan.md` §1.2 §5.

* Item 25 `boundary_multiplicative`: `c_{N₁N₂}(m) = c_{N₁}(m) c_{N₂}(m)` for coprime `N₁, N₂`.
* Item 26 `boundary_local_factor` (**exit**, P04 D3): `c_{p^e}(m)` as a sum over `j ≤ e`; `c_p(m) = 2`; `c_N(m) = 2^{ω(N)}` for squarefree `N`.
* Item 29 `eisenstein_doubling`: `Ẽis(pN, k, n) = 2 Ẽis(N, k, n)` and `Eis(pN, 2, n) = 2 Eis(N, 2, n) + σ₁(n)` for `p ∤ N`.

The definitions `boundaryDivisorSum` (item 24), `eisensteinCorrected` (27) and `eisensteinExpr` (28) live in `Normalization`.
-/

open scoped ArithmeticFunction.omega ArithmeticFunction.sigma

namespace GL2TF.Explicit

private theorem boundaryDivisorSum_eq_sum_ite (N : ℕ) (m : ℤ) :
    boundaryDivisorSum N m = ∑ τ ∈ N.divisors,
      if ((Nat.gcd τ (N / τ) : ℕ) : ℤ) ∣ m then Nat.totient (Nat.gcd τ (N / τ)) else 0 := by
  unfold boundaryDivisorSum
  rw [Finset.sum_filter]

private theorem gcd_mul_mul_of_coprime {a b c d : ℕ} (hac : Nat.Coprime a d) (hbc : Nat.Coprime b c)
    (hcd : Nat.Coprime c d) :
    Nat.gcd (a * b) (c * d) = Nat.gcd a c * Nat.gcd b d := by
  rw [Nat.Coprime.gcd_mul _ hcd]
  rw [Nat.Coprime.gcd_mul_right_cancel a (Nat.Coprime.symm hbc).symm]
  rw [mul_comm a b, Nat.Coprime.gcd_mul_right_cancel b (Nat.Coprime.symm hac).symm]


/-- Item 25: the boundary divisor sum is multiplicative in the level. -/
@[tf_id "III.ef.thm:boundary-multiplicative"]
theorem boundary_multiplicative (N₁ N₂ : ℕ) (h : N₁.Coprime N₂) (m : ℤ) :
    boundaryDivisorSum (N₁ * N₂) m = boundaryDivisorSum N₁ m * boundaryDivisorSum N₂ m := by
  simp only [boundaryDivisorSum_eq_sum_ite]
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image (fun x hx y hy hxy =>
    Nat.Coprime.mul_injOn_divisors h hx hy hxy), Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [Nat.mem_divisors] at ha hb
  obtain ⟨⟨a', rfl⟩, h1⟩ := ha
  obtain ⟨⟨b', rfl⟩, h2⟩ := hb
  have ha0 : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul h1)
  have hb0 : 0 < b := Nat.pos_of_ne_zero (left_ne_zero_of_mul h2)
  have hq : a * a' * (b * b') / (a * b) = a' * b' := by
    rw [show a * a' * (b * b') = (a * b) * (a' * b') by ring]
    exact Nat.mul_div_cancel_left _ (Nat.mul_pos ha0 hb0)
  rw [hq, Nat.mul_div_cancel_left _ ha0, Nat.mul_div_cancel_left _ hb0]
  have hab' : Nat.Coprime a b' := Nat.Coprime.coprime_dvd_left (dvd_mul_right a a')
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left b' b) h)
  have hba' : Nat.Coprime b a' := (Nat.Coprime.coprime_dvd_left (dvd_mul_left a' a)
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right b b') h)).symm
  have ha'b' : Nat.Coprime a' b' := Nat.Coprime.coprime_dvd_left (dvd_mul_left a' a)
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left b' b) h)
  rw [gcd_mul_mul_of_coprime hab' hba' ha'b']
  have hg : Nat.Coprime (Nat.gcd a a') (Nat.gcd b b') :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a a') (Nat.Coprime.coprime_dvd_right
      (Nat.gcd_dvd_left b b') (Nat.Coprime.coprime_dvd_left (dvd_mul_right a a')
        (Nat.Coprime.coprime_dvd_right (dvd_mul_right b b') h)))
  rw [Nat.totient_mul hg]
  have hdvd : ((Nat.gcd a a' * Nat.gcd b b' : ℕ) : ℤ) ∣ m ↔
      ((Nat.gcd a a' : ℕ) : ℤ) ∣ m ∧ ((Nat.gcd b b' : ℕ) : ℤ) ∣ m := by
    simp only [Int.natCast_dvd]
    exact ⟨fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩,
      fun h => hg.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  rw [if_congr hdvd rfl rfl, ite_zero_mul_ite_zero]

private theorem gcd_pow_pow_min (p a b : ℕ) : Nat.gcd (p ^ a) (p ^ b) = p ^ min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]

private theorem boundaryDivisorSum_prime_pow (m : ℤ) (p e : ℕ) (hp : p.Prime) :
      boundaryDivisorSum (p ^ e) m =
        ∑ j ∈ Finset.range (e + 1),
          if ((p ^ min j (e - j) : ℕ) : ℤ) ∣ m then Nat.totient (p ^ min j (e - j)) else 0 := by
  unfold boundaryDivisorSum
  rw [Finset.sum_filter, Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div hje hp.pos, gcd_pow_pow_min]

private theorem boundaryDivisorSum_prime (m : ℤ) (p : ℕ) (hp : p.Prime) : boundaryDivisorSum p m = 2 := by
  have := boundaryDivisorSum_prime_pow m p 1 hp
  rw [pow_one] at this
  rw [this]
  simp [Finset.sum_range_succ]

private theorem boundaryDivisorSum_squarefree (m : ℤ) (N : ℕ) (hN : Squarefree N) : boundaryDivisorSum N m = 2 ^ ω N := by
  rw [← Nat.prod_primeFactors_of_squarefree hN]
  have hpr : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  generalize N.primeFactors = s at hpr ⊢
  induction s using Finset.induction_on with
  | empty => simp [boundaryDivisorSum, Finset.filter_singleton]
  | insert a s ha ih =>
    have ha' : a.Prime := hpr a (Finset.mem_insert_self a s)
    have ih' := ih fun p hp => hpr p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes ha' (hpr q (Finset.mem_insert_of_mem hq))).2 (fun h => ha (h ▸ hq))
    rw [Finset.prod_insert ha, boundary_multiplicative _ _ hcop, ih', boundaryDivisorSum_prime m a ha',
      ArithmeticFunction.cardDistinctFactors_mul hcop,
      ArithmeticFunction.cardDistinctFactors_apply_prime ha', pow_add, pow_one]


/-- Item 26 (exit, P04 D3): the local factor of the boundary divisor sum.
(a) `c_{p^e}(m) = Σ_{j=0}^{e} [p^{min(j,e−j)} ∣ m] φ(p^{min(j,e−j)})`; (b) `c_p(m) = 2`; (c) `c_N(m) = 2^{ω(N)}` for squarefree `N`. -/
@[tf_id "III.ef.thm:boundary-local-factor"]
theorem boundary_local_factor (m : ℤ) :
    (∀ p e : ℕ, p.Prime →
      boundaryDivisorSum (p ^ e) m =
        ∑ j ∈ Finset.range (e + 1),
          if ((p ^ min j (e - j) : ℕ) : ℤ) ∣ m then Nat.totient (p ^ min j (e - j)) else 0) ∧
    (∀ p : ℕ, p.Prime → boundaryDivisorSum p m = 2) ∧
    (∀ N : ℕ, Squarefree N → boundaryDivisorSum N m = 2 ^ ω N) := by
  exact ⟨fun p e hp => boundaryDivisorSum_prime_pow m p e hp, fun p hp => boundaryDivisorSum_prime m p hp,
    fun N hN => boundaryDivisorSum_squarefree m N hN⟩

/-- Item 29: Eisenstein doubling. Adding a prime `p ∤ N` to the level doubles `Ẽis`; for `Eis` at `k = 2` the
correction `σ₁(n)` appears (P04 D4's "each system doubles" holds for `Ẽis`, row N10). -/
@[tf_id "III.ef.thm:eisenstein-doubling"]
theorem eisenstein_doubling (N k n p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    eisensteinCorrected (p * N) k n = 2 * eisensteinCorrected N k n ∧
      eisensteinExpr (p * N) 2 n = 2 * eisensteinExpr N 2 n + (σ 1 n : ℚ) := by
  have hcop : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hE : ∀ k, eisensteinCorrected (p * N) k n = 2 * eisensteinCorrected N k n := by
    intro k
    unfold eisensteinCorrected
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [boundary_multiplicative p N hcop, boundaryDivisorSum_prime _ p hp]
    push_cast
    ring
  refine ⟨hE k, ?_⟩
  unfold eisensteinExpr
  rw [hE 2]
  simp only [ite_true]
  ring

end GL2TF.Explicit
