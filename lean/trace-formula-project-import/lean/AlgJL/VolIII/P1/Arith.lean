import AlgJL.Meta.Tag
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Field.Rat

/-!
# Arithmetic functions, signed divisor sums, class numbers of forms, `P_k` (Q1 U1)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §§1–2 (items 1–7, 10, 11 of `docs/sprints/Q1-plan.md` §1.2):
the Dedekind function `ψ`, the signed divisor sums, the index set `𝓕(t, n)`, the class number `h(Δ)` of primitive
positive definite binary quadratic forms (counted by reduced triples), and the Hecke polynomials `P_k(t, n)`.

All definitions are computable (plan trap 11): no `Classical` in their bodies, bounded search ranges only.
Junk conventions as in the snippets (A1 notes item 5): `ψ(0) = 0`, `h(Δ) = 0` for `Δ ≥ 0`, `P_0 = P_1 = 0`.
Owner: L1 (Q1).
-/

open scoped ArithmeticFunction.omega

namespace GL2TF.Explicit

/-! ## §1 The Dedekind function and signed divisor sums -/

/-- The Dedekind function `ψ(N) = N ∏_{p ∣ N} (1 + 1/p) ∈ ℚ`; `ψ(0) = 0` (empty product, factor `0`). -/
@[tf_id "III.ef.def:dedekind-psi"]
def dedekindPsi (N : ℕ) : ℚ :=
  (N : ℚ) * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ))

/-- Proof helper: `ω n` is the number of prime factors. -/
private theorem omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- Proof helper: `ψ(N) = (N / rad N) ∏_{p ∣ N} (p + 1)`. -/
private theorem dedekindPsi_eq_div_mul (N : ℕ) :
    dedekindPsi N = ((N / ∏ p ∈ N.primeFactors, p : ℕ) : ℚ) * ∏ p ∈ N.primeFactors, ((p : ℚ) + 1) := by
  obtain ⟨q, hq⟩ := Nat.prod_primeFactors_dvd N
  have hpos : 0 < ∏ p ∈ N.primeFactors, p := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hdiv : N / ∏ p ∈ N.primeFactors, p = q := Nat.div_eq_of_eq_mul_left hpos (hq.trans (mul_comm _ _))
  have hN : (N : ℚ) = (∏ p ∈ N.primeFactors, (p : ℚ)) * q := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, ← hq]
  rw [hdiv, dedekindPsi, hN]
  rw [mul_comm (∏ p ∈ N.primeFactors, (p : ℚ)) (q : ℚ), mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [mul_add, mul_one, mul_one_div_cancel this]

/-- Proof helper: for squarefree `d`, `ψ(d) = ∏_{p ∣ d} (p + 1)`. -/
private theorem dedekindPsi_of_squarefree {d : ℕ} (hd : Squarefree d) :
    dedekindPsi d = ∏ p ∈ d.primeFactors, ((p : ℚ) + 1) := by
  rw [dedekindPsi_eq_div_mul, Nat.prod_primeFactors_of_squarefree hd, Nat.div_self hd.ne_zero.bot_lt]
  simp

/-- Proof helper: `ψ` is multiplicative on coprime arguments. -/
private theorem dedekindPsi_mul_of_coprime {N₁ N₂ : ℕ} (h : Nat.Coprime N₁ N₂) :
    dedekindPsi (N₁ * N₂) = dedekindPsi N₁ * dedekindPsi N₂ := by
  unfold dedekindPsi
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  push_cast
  ring

/-- (a) `ψ(N)` is a natural number; (b) `ψ` is multiplicative on coprime arguments; (c) `ψ(p) = p + 1`. -/
@[tf_id "III.ef.lem:dedekind-psi-multiplicative"]
theorem dedekindPsi_nat_mul_prime :
    (∀ N : ℕ, ∃ m : ℕ, dedekindPsi N = m) ∧
    (∀ N₁ N₂ : ℕ, Nat.Coprime N₁ N₂ → dedekindPsi (N₁ * N₂) = dedekindPsi N₁ * dedekindPsi N₂) ∧
    (∀ p : ℕ, p.Prime → dedekindPsi p = p + 1) := by
  refine ⟨fun N => ?_, fun N₁ N₂ h => dedekindPsi_mul_of_coprime h, fun p hp => ?_⟩
  · refine ⟨(N / ∏ p ∈ N.primeFactors, p) * ∏ p ∈ N.primeFactors, (p + 1), ?_⟩
    rw [dedekindPsi_eq_div_mul]
    push_cast
    rfl
  · rw [dedekindPsi_of_squarefree hp.squarefree, hp.primeFactors, Finset.prod_singleton]

/-- The signed divisor sum: for squarefree `D` and `a, b : ℕ → R`,
`∑_{d ∣ D} ∏_{p ∣ D/d} b(p) ∏_{p ∣ d} a(p) = ∏_{p ∣ D} (a(p) + b(p))`. -/
@[tf_id "III.ef.lem:signed-divisor-sum"]
theorem sum_divisors_prod_eq_prod_add {R : Type*} [CommRing R] (a b : ℕ → R) {D : ℕ}
    (hD : Squarefree D) :
    ∑ d ∈ D.divisors, (∏ p ∈ (D / d).primeFactors, b p) * ∏ p ∈ d.primeFactors, a p =
      ∏ p ∈ D.primeFactors, (a p + b p) := by
  have hD0 : D ≠ 0 := hD.ne_zero
  rw [Finset.prod_add]
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun s => ∏ p ∈ s, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hD0
  · intro s hs
    rw [Finset.mem_powerset] at hs
    rw [Nat.mem_divisors]
    refine ⟨?_, hD0⟩
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hD]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hs
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (hD.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro s hs
    rw [Finset.mem_powerset] at hs
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (hs hp)
  · intro d hd
    have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hdD
    have hg : D.gcd d = d := Nat.gcd_eq_right hdD
    have hpf : (D / d).primeFactors = D.primeFactors \ d.primeFactors := by
      rw [← Nat.primeFactors_div_gcd hD hd0, hg]
    rw [hpf, mul_comm]

/-- The constants `s_d = (-2)^{ω(D/d)}` for squarefree `D`: (a) `∑_{d ∣ D} s_d = (-1)^{ω(D)}`;
(b) `∑_{d ∣ D} s_d 2^{ω(d)} = 0` if `D > 1`; (c) `∑_{d ∣ D} s_d ψ(dM) = ψ(M) ∏_{p ∣ D} (p − 1)` if `gcd(D, M) = 1`. -/
@[tf_id "III.ef.cor:signed-divisor-sum-constants"]
theorem signedDivisorSum_constants {D : ℕ} (hD : Squarefree D) :
    (∑ d ∈ D.divisors, (-2 : ℤ) ^ ω (D / d) = (-1) ^ ω D) ∧
    (1 < D → ∑ d ∈ D.divisors, (-2 : ℤ) ^ ω (D / d) * 2 ^ ω d = 0) ∧
    (∀ M : ℕ, Nat.Coprime D M →
      ∑ d ∈ D.divisors, ((-2 : ℚ) ^ ω (D / d)) * dedekindPsi (d * M) =
        dedekindPsi M * ∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) := by
  have hpow : ∀ {R : Type} [CommRing R] (c : R) (m : ℕ), c ^ ω m = ∏ _p ∈ m.primeFactors, c := by
    intro R _ c m
    rw [Finset.prod_const, omega_eq_card]
  refine ⟨?_, fun hD1 => ?_, fun M hDM => ?_⟩
  · have := sum_divisors_prod_eq_prod_add (fun _ => (1 : ℤ)) (fun _ => (-2 : ℤ)) hD
    simp only [Finset.prod_const_one, mul_one] at this
    simp_rw [hpow]
    rw [this]
    norm_num
  · have := sum_divisors_prod_eq_prod_add (fun _ => (2 : ℤ)) (fun _ => (-2 : ℤ)) hD
    simp_rw [hpow]
    rw [this]
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hD1
    exact Finset.prod_eq_zero hp (by norm_num)
  · have := sum_divisors_prod_eq_prod_add (fun p => (p : ℚ) + 1) (fun _ => (-2 : ℚ)) hD
    have hsum : ∀ d ∈ D.divisors, ((-2 : ℚ) ^ ω (D / d)) * dedekindPsi (d * M) =
        dedekindPsi M * ((∏ _p ∈ (D / d).primeFactors, (-2 : ℚ)) * ∏ p ∈ d.primeFactors, ((p : ℚ) + 1)) := by
      intro d hd
      have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
      rw [dedekindPsi_mul_of_coprime (Nat.Coprime.coprime_dvd_left hdD hDM),
        dedekindPsi_of_squarefree (hD.squarefree_of_dvd hdD), hpow]
      ring
    rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, this]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    ring

/-! ## §2 Discriminants, class numbers of forms, `P_k` -/

/-- The index set `𝓕(t, n)`: all `f ∈ ℕ` with `1 ≤ f ≤ |t² − 4n|`, `f² ∣ t² − 4n` and `(t² − 4n)/f² ≡ 0, 1 (mod 4)`. -/
@[tf_id "III.ef.def:order-index-set"]
def orderIndexSet (t : ℤ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (t ^ 2 - 4 * n).natAbs).filter fun f =>
    (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n ∧
      ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 0 ∨ (t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 1)

/-- The class number `h(Δ)` of primitive positive definite forms: for `Δ < 0` the number of triples `(a, b, c) ∈ ℤ³`
with `b² − 4ac = Δ`, `|b| ≤ a ≤ c`, `b ≥ 0` if `|b| = a` or `a = c`, and `gcd(a, b, c) = 1`; `h(Δ) = 0` for `Δ ≥ 0`.

The triples are searched in the box `[1, |Δ|] × [−|Δ|, |Δ|] × [1, |Δ|]`, which contains every solution
(`3a² ≤ 4ac − b² = |Δ|`, so `1 ≤ a ≤ |Δ|`, `|b| ≤ a`, and `c = (b² + |Δ|)/(4a) ≤ |Δ|`; B fidelity note). -/
@[tf_id "III.ef.def:class-number-forms"]
def classNumberForms (Δ : ℤ) : ℕ :=
  if Δ < 0 then
    ((Finset.Icc (1 : ℤ) Δ.natAbs ×ˢ Finset.Icc (-(Δ.natAbs : ℤ)) Δ.natAbs ×ˢ Finset.Icc (1 : ℤ) Δ.natAbs).filter
      fun x : ℤ × ℤ × ℤ =>
        x.2.1 ^ 2 - 4 * x.1 * x.2.2 = Δ ∧ |x.2.1| ≤ x.1 ∧ x.1 ≤ x.2.2 ∧
          ((|x.2.1| = x.1 ∨ x.1 = x.2.2) → 0 ≤ x.2.1) ∧
          Int.gcd (Int.gcd x.1 x.2.1 : ℤ) x.2.2 = 1).card
  else 0

/-- The Hecke polynomials `P_k(t, n) ∈ ℤ`: `P_0 = P_1 = 0`, `P_2 = 1`, `P_{k+1} = t P_k − n P_{k−1}` (`k ≥ 2`). -/
@[tf_id "III.ef.def:hecke-polynomial"]
def heckePoly : ℕ → ℤ → ℕ → ℤ
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, _, _ => 1
  | k + 3, t, n => t * heckePoly (k + 2) t n - (n : ℤ) * heckePoly (k + 1) t n

/-- Proof helper for item 11, indexed by `k + 1`. -/
private theorem heckePoly_mul_sub_aux {R : Type*} [CommRing R] (t : ℤ) (n : ℕ) (ρ ρ' : R)
    (hsum : ρ + ρ' = (t : R)) (hprod : ρ * ρ' = (n : R)) :
    ∀ k : ℕ, (ρ - ρ') * (heckePoly (k + 1) t n : R) = ρ ^ k - ρ' ^ k
  | 0 => by simp [heckePoly]
  | 1 => by simp [heckePoly]
  | k + 2 => by
    have h1 := heckePoly_mul_sub_aux t n ρ ρ' hsum hprod (k + 1)
    have h0 := heckePoly_mul_sub_aux t n ρ ρ' hsum hprod k
    rw [show k + 2 + 1 = k + 3 from rfl, heckePoly]
    push_cast
    rw [← hsum, ← hprod]
    calc (ρ - ρ') * ((ρ + ρ') * (heckePoly (k + 2) t n : R) - ρ * ρ' * (heckePoly (k + 1) t n : R))
        = (ρ + ρ') * ((ρ - ρ') * (heckePoly (k + 1 + 1) t n : R)) -
            ρ * ρ' * ((ρ - ρ') * (heckePoly (k + 1) t n : R)) := by ring
      _ = (ρ + ρ') * (ρ ^ (k + 1) - ρ' ^ (k + 1)) - ρ * ρ' * (ρ ^ k - ρ' ^ k) := by rw [h1, h0]
      _ = ρ ^ (k + 2) - ρ' ^ (k + 2) := by ring

/-- If `ρ + ρ̄ = t` and `ρρ̄ = n` in a commutative ring, then `(ρ − ρ̄) P_k(t, n) = ρ^{k−1} − ρ̄^{k−1}` for `k ≥ 1`. -/
@[tf_id "III.ef.lem:hecke-polynomial-roots"]
theorem heckePoly_mul_sub {R : Type*} [CommRing R] (t : ℤ) (n : ℕ) (ρ ρ' : R)
    (hsum : ρ + ρ' = (t : R)) (hprod : ρ * ρ' = (n : R)) (k : ℕ) (hk : 1 ≤ k) :
    (ρ - ρ') * (heckePoly k t n : R) = ρ ^ (k - 1) - ρ' ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa using heckePoly_mul_sub_aux t n ρ ρ' hsum hprod j

end GL2TF.Explicit
