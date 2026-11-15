import AlgJL.Common.QuaternionHilbert
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Ramification: `RamifiedExactly` and Pizer's algebras (Q2 U2, items 14–16)

Lean counterpart of `vol3/ch-iii-06-quatalg.tex` §2, second half (items 14–16 of `docs/sprints/Q2-plan.md` §1.2).

`RamifiedExactly a b D` is a data predicate (a Prop-valued project constant that reaches binders; its
`registry/assumptions.yaml` row is written at G1, plan trap 1). It records `a, b < 0`, `D` squarefree and the finite
ramification set `{p : (a, b)_p = −1} = {p ∣ D}`; Hilbert reciprocity (ω(D) odd) is not claimed (plan §1.2, "Not in Q2").
The values of `(a, b)_p` used by item 15 come from items 11–13 (plan trap 2). Item 16 is optional.
Owner: L1T (Q2).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-- `RamifiedExactly a b D` :⇔ `a < 0`, `b < 0`, `D` squarefree, and for every prime `p`, `(a, b)_p = −1 ↔ p ∣ D`. -/
@[tf_id "III.qalg.def:ramified-exactly"]
def RamifiedExactly (a b : ℤ) (D : ℕ) : Prop :=
  a < 0 ∧ b < 0 ∧ Squarefree D ∧
    ∀ (p : ℕ) [Fact p.Prime], hilbertSymbol ℚ_[p] a b = -1 ↔ p ∣ D

private theorem not_dvd_of_prime_ne {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (h : q ≠ p) :
    ¬ (q : ℤ) ∣ p := by
  intro hd
  exact h ((Nat.prime_dvd_prime_iff_eq hq hp).1 (by exact_mod_cast hd))

private theorem unram_aux (q : ℕ) [Fact q.Prime] (a b : ℤ) (h : ¬ (q : ℤ) ∣ 2 * a * b) (D : ℕ)
    (hD : ¬ q ∣ D) : hilbertSymbol ℚ_[q] a b = -1 ↔ q ∣ D := by
  rw [hilbertSymbol_unramified q a b h]
  exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' hD⟩

/-- Pizer's algebras: `(−1, −1)` is ramified exactly at `2`; `(−1, −p)` exactly at `p` for primes `p ≡ 3 (mod 4)`;
`(−2, −p)` exactly at `p` for primes `p ≡ 5 (mod 8)`. -/
@[tf_id "III.qalg.thm:pizer-algebras"]
theorem pizer_algebras :
    RamifiedExactly (-1) (-1) 2 ∧
    (∀ p : ℕ, p.Prime → p % 4 = 3 → RamifiedExactly (-1) (-(p : ℤ)) p) ∧
    (∀ p : ℕ, p.Prime → p % 8 = 5 → RamifiedExactly (-2) (-(p : ℤ)) p) := by
  refine ⟨⟨by norm_num, by norm_num, Nat.prime_two.prime.squarefree, fun q _ => ?_⟩,
    fun p hp hp4 => ⟨by norm_num, by have := hp.two_le; omega, hp.prime.squarefree, fun q _ => ?_⟩,
    fun p hp hp8 => ⟨by norm_num, by have := hp.two_le; omega, hp.prime.squarefree, fun q _ => ?_⟩⟩
  · -- (-1, -1)
    have hq : q.Prime := Fact.out
    by_cases hq2 : q = 2
    · subst hq2
      rw [(hilbertSymbol_two (-1) (-1) (by decide) (by decide)).1]
      norm_num
    · refine unram_aux q _ _ ?_ 2 (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h))
      intro h
      have h' : (q : ℤ) ∣ 2 := by simpa using h
      have : q ∣ 2 := by exact_mod_cast h'
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  · -- (-1, -p), p ≡ 3 mod 4
    have hq : q.Prime := Fact.out
    have hp2 : p ≠ 2 := by omega
    by_cases hq2 : q = 2
    · subst hq2
      rw [(hilbertSymbol_two (-1) (-(p : ℤ)) (by decide) (by
        rw [Int.odd_iff]; omega)).1]
      have hev : Even ((-1 - 1) / 2 * ((-(p : ℤ) - 1) / 2)) := by
        rw [Int.even_iff]; norm_num; omega
      rw [Even.neg_one_pow (Int.natAbs_even.2 hev)]
      constructor
      · intro h; norm_num at h
      · intro h; omega
    by_cases hqp : q = p
    · subst hqp
      have e := hilbertSymbol_odd q hp2 0 1 (-1) (-1) (by
        rw [Int.dvd_neg]; exact fun h => hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))
        (by
        rw [Int.dvd_neg]; exact fun h => hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))
      norm_num at e
      rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp4] at e
      push_cast
      rw [e]; simp
    · refine unram_aux q _ _ ?_ p (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h))
      intro h
      have h' : (q : ℤ) ∣ 2 * p := by
        have : 2 * (-1) * (-(p : ℤ)) = 2 * p := by ring
        rwa [this] at h
      rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd h' with h'' | h''
      · have : q ∣ 2 := by exact_mod_cast h''
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
      · exact not_dvd_of_prime_ne hq hp hqp h''
  · -- (-2, -p), p ≡ 5 mod 8
    have hq : q.Prime := Fact.out
    have hp2 : p ≠ 2 := by omega
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [hilbertSymbol_symm]
      have e : ((-2 : ℤ) : ℚ_[2]) = ((2 * (-1) : ℤ) : ℚ_[2]) := by norm_num
      rw [e, (hilbertSymbol_two (-(p : ℤ)) (-1) (by rw [Int.odd_iff]; omega) (by decide)).2]
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (p : ℤ) = 8 * k + 5 := ⟨(p : ℤ) / 8, by omega⟩
      have e2 : (-(p : ℤ)) ^ 2 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by rw [hk]; ring
      have hev : Even ((-(p : ℤ) - 1) / 2 * ((-1 - 1) / 2) + ((-(p : ℤ)) ^ 2 - 1) / 8) := by
        rw [e2, Int.mul_ediv_cancel_left _ (by norm_num), Int.even_iff]
        generalize k ^ 2 = K
        norm_num
        omega
      rw [Even.neg_one_pow (Int.natAbs_even.2 hev)]
      constructor
      · intro h; norm_num at h
      · intro h; omega
    have hq2' : ¬ (q : ℤ) ∣ 2 := by
      intro h
      have : q ∣ 2 := by exact_mod_cast h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
    by_cases hqp : q = p
    · subst hqp
      have hm2 : ¬ (q : ℤ) ∣ -2 := by rw [Int.dvd_neg]; exact hq2'
      have hm1 : ¬ (q : ℤ) ∣ -1 := by
        rw [Int.dvd_neg]; exact fun h => hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
      have e := hilbertSymbol_odd q hp2 0 1 (-2) (-1) hm2 hm1
      have L2 : legendreSym q (-2) = -1 := by
        rw [show (-2 : ℤ) = (-1) * 2 by norm_num, legendreSym.mul, legendreSym.at_neg_one hp2,
          legendreSym.at_two hp2, ZMod.χ₄_nat_one_mod_four (by omega), ZMod.χ₈_nat_eq_if_mod_eight,
          ite_eq_right (by omega), ite_eq_right (by omega)]
        norm_num
      norm_num at e
      rw [L2] at e
      push_cast
      rw [e]; simp
    · refine unram_aux q _ _ ?_ p (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h))
      intro h
      have h' : (q : ℤ) ∣ 2 * (2 * p) := by
        have : 2 * (-2) * (-(p : ℤ)) = 2 * (2 * p) := by ring
        rwa [this] at h
      rcases hqZ.dvd_or_dvd h' with h'' | h''
      · exact hq2' h''
      rcases hqZ.dvd_or_dvd h'' with h'' | h''
      · exact hq2' h''
      · exact not_dvd_of_prime_ne hq hp hqp h''


private theorem not_dvd_neg_one' (q : ℕ) (hq : q.Prime) : ¬ (q : ℤ) ∣ -1 := by
  rw [Int.dvd_neg]
  exact fun h => hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)

/-- (Optional.) For a prime `p ≡ 1 (mod 8)` and a prime `q ≡ 3 (mod 4)` with `(p/q) = −1`: `(−p, −q)` is ramified
exactly at `p`. -/
@[tf_id "III.qalg.thm:pizer-algebras-one-mod-eight"]
theorem pizer_algebras_one_mod_eight (p q : ℕ) [Fact q.Prime] (hp : p.Prime) (hp8 : p % 8 = 1)
    (hq4 : q % 4 = 3) (hpq : legendreSym q p = -1) :
    RamifiedExactly (-(p : ℤ)) (-(q : ℤ)) p := by
  have hq : q.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hqp : q ≠ p := by omega
  refine ⟨by have := hp.two_le; omega, by have := hq.two_le; omega, hp.prime.squarefree, fun r _ => ?_⟩
  have hr : r.Prime := Fact.out
  have hrZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  by_cases hr2 : r = 2
  · subst hr2
    rw [(hilbertSymbol_two (-(p : ℤ)) (-(q : ℤ)) (by rw [Int.odd_iff]; omega)
      (by rw [Int.odd_iff]; omega)).1]
    have hB : Even ((-(q : ℤ) - 1) / 2) := by rw [Int.even_iff]; omega
    rw [Even.neg_one_pow (Int.natAbs_even.2 (hB.mul_left _))]
    constructor
    · intro h; norm_num at h
    · intro h; omega
  have hr2' : ¬ (r : ℤ) ∣ 2 := by
    intro h
    have : r ∣ 2 := by exact_mod_cast h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  by_cases hrp : r = p
  · subst hrp
    have e := hilbertSymbol_odd r hr2 1 0 (-1) (-(q : ℤ)) (not_dvd_neg_one' r hr)
      (by rw [Int.dvd_neg]; exact not_dvd_of_prime_ne hr hq (Ne.symm hqp))
    have L : legendreSym r (-(q : ℤ)) = -1 := by
      rw [legendreSym.at_neg hr2, ZMod.χ₄_nat_one_mod_four (by omega),
        ← legendreSym.quadratic_reciprocity_one_mod_four (by omega) hq2, hpq]
      norm_num
    norm_num at e
    rw [L] at e
    push_cast
    rw [e]; simp
  by_cases hrq : r = q
  · subst hrq
    have e := hilbertSymbol_odd r hr2 0 1 (-(p : ℤ)) (-1)
      (by rw [Int.dvd_neg]; exact not_dvd_of_prime_ne hr hp hqp) (not_dvd_neg_one' r hr)
    have L : legendreSym r (-(p : ℤ)) = 1 := by
      rw [legendreSym.at_neg hr2, ZMod.χ₄_nat_three_mod_four hq4, hpq]
      norm_num
    norm_num at e
    rw [L] at e
    push_cast
    rw [e]
    constructor
    · intro h; norm_num at h
    · intro h; exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h) hqp
  · rw [hilbertSymbol_unramified r _ _ (by
      intro h
      have h' : (r : ℤ) ∣ 2 * (p * q) := by
        have : 2 * (-(p : ℤ)) * (-(q : ℤ)) = 2 * (p * q) := by ring
        rwa [this] at h
      rcases hrZ.dvd_or_dvd h' with h'' | h''
      · exact hr2' h''
      rcases hrZ.dvd_or_dvd h'' with h'' | h''
      · exact not_dvd_of_prime_ne hr hp hrp h''
      · exact not_dvd_of_prime_ne hr hq hrq h'')]
    constructor
    · intro h; norm_num at h
    · intro h; exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h) hrp


end GL2TF.Quat
