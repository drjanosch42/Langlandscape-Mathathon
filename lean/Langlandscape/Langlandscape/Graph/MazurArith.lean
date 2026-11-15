/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Ring

/-!
# Mazur arithmetic (pure) — S03-L5

For a finite family of weights `w i ∈ {1,2,3}` in which `2` occurs `n₂ = [q ≡ 3 mod 4]` times and
`3` occurs `n₃ = [q ≡ 2 mod 3]` times, and whose inverse weights sum to `(q-1)/12` (`q ≥ 5` prime):
`∏ w · Σ w⁻¹ = num ((q-1)/12)`, and the weights are pairwise coprime.

Deviation from the planning row: `n₂, n₃` are stated through `q % 4`, `q % 3` (equivalent to
`(1 - χ₄ q)/2`, `(1 - χ₃ q)/2`); the translation from `legendreSym` is done by the caller (S03-L6).

Tex labels: `prop:s03-mazur` (`s03-mazur`). Status: formalized (Mathlib only, hypothesis-free).
-/

set_option autoImplicit false

namespace Langlandscape.Graph

/-- The numerator of `(q-1)/12` (the Mazur number), `prop:s03-mazur` (`s03-mazur`). -/
def mazurNum (q : ℕ) : ℤ := (((q : ℚ) - 1) / 12).num

/-- `prop:s03-mazur` (`s03-mazur`): numerator of a reduced fraction of naturals. -/
private lemma s03_mazur_num_nat_div (a b : ℕ) (hb : 0 < b) (hc : a.Coprime b) :
    (((a : ℚ) / b).num) = (a : ℤ) := by
  have := Rat.num_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ))
    (by exact_mod_cast hb) (by simpa using hc)
  simpa using this

/-- `prop:s03-mazur` (`s03-mazur`): one residue case, `P = b` and `(q-1)/12 = a/b` reduced. -/
private lemma s03_mazur_case (q a b P : ℕ) (hb : 0 < b) (hc : a.Coprime b)
    (hq : ((q : ℚ) - 1) / 12 = (a : ℚ) / b) (hP : P = b) :
    (P : ℚ) * (((q : ℚ) - 1) / 12) = (mazurNum q : ℚ) := by
  unfold mazurNum
  rw [hq, s03_mazur_num_nat_div a b hb hc, hP]
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  push_cast
  field_simp

/-- `prop:s03-mazur` (`s03-mazur`): residues of a prime `q ≥ 5` modulo `12`. -/
private lemma s03_mazur_mod12 (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) :
    q % 12 = 1 ∨ q % 12 = 5 ∨ q % 12 = 7 ∨ q % 12 = 11 := by
  have h2 : ¬ 2 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h
    omega
  have h3 : ¬ 3 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h
    omega
  omega

/-- `prop:s03-mazur` (`s03-mazur`): the product of the weights is `2^{n₂} 3^{n₃}`. -/
private lemma s03_mazur_prod {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (hw : ∀ i, w i = 1 ∨ w i = 2 ∨ w i = 3) :
    ∏ i, w i = 2 ^ (Finset.univ.filter (fun i => w i = 2)).card *
      3 ^ (Finset.univ.filter (fun i => w i = 3)).card := by
  have key : ∀ i, w i = 2 ^ (if w i = 2 then 1 else 0) * 3 ^ (if w i = 3 then 1 else 0) := by
    intro i
    rcases hw i with h | h | h <;> simp [h]
  calc ∏ i, w i
      = ∏ i, (2 ^ (if w i = 2 then 1 else 0) * 3 ^ (if w i = 3 then 1 else 0)) :=
        Finset.prod_congr rfl (fun i _ => key i)
    _ = (∏ i, 2 ^ (if w i = 2 then 1 else 0)) * ∏ i, 3 ^ (if w i = 3 then 1 else 0) :=
        Finset.prod_mul_distrib
    _ = _ := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
          ← Finset.card_filter, ← Finset.card_filter]

/-- `prop:s03-mazur` (`s03-mazur`): for a prime `q ≥ 5` and weights in `{1,2,3}` with
`#{w = 2} = [q ≡ 3 (4)]`, `#{w = 3} = [q ≡ 2 (3)]` and `Σ w⁻¹ = (q-1)/12`:
`∏ w · Σ w⁻¹ = num ((q-1)/12)`. -/
theorem mazur_prod_mul_sum {ι : Type*} [Fintype ι] (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q)
    (w : ι → ℕ) (hw : ∀ i, w i = 1 ∨ w i = 2 ∨ w i = 3)
    (h2 : (Finset.univ.filter (fun i => w i = 2)).card = if q % 4 = 3 then 1 else 0)
    (h3 : (Finset.univ.filter (fun i => w i = 3)).card = if q % 3 = 2 then 1 else 0)
    (hsum : ∑ i, (1 : ℚ) / (w i : ℚ) = ((q : ℚ) - 1) / 12) :
    ((∏ i, w i : ℕ) : ℚ) * ∑ i, (1 : ℚ) / (w i : ℚ) = (mazurNum q : ℚ) := by
  rw [hsum]
  have hP := s03_mazur_prod w hw
  rw [h2, h3] at hP
  rcases s03_mazur_mod12 q hq h5 with h | h | h | h
  · obtain ⟨k, hk⟩ : ∃ k, q = 12 * k + 1 := ⟨q / 12, by omega⟩
    have e4 : q % 4 = 1 := by omega
    have e3 : q % 3 = 1 := by omega
    rw [e4, e3] at hP
    simp at hP
    have hqc : (q : ℚ) = 12 * k + 1 := by exact_mod_cast hk
    exact s03_mazur_case q k 1 _ one_pos (Nat.coprime_one_right _)
      (by rw [hqc]; push_cast; ring) (by simpa using hP)
  · obtain ⟨k, hk⟩ : ∃ k, q = 12 * k + 5 := ⟨q / 12, by omega⟩
    have e4 : q % 4 = 1 := by omega
    have e3 : q % 3 = 2 := by omega
    rw [e4, e3] at hP
    simp at hP
    have hqc : (q : ℚ) = 12 * k + 5 := by exact_mod_cast hk
    exact s03_mazur_case q (3 * k + 1) 3 _ (by norm_num)
      ((Nat.coprime_mul_left_add_left 1 3 k).2 (by norm_num))
      (by rw [hqc]; push_cast; ring) (by simpa using hP)
  · obtain ⟨k, hk⟩ : ∃ k, q = 12 * k + 7 := ⟨q / 12, by omega⟩
    have e4 : q % 4 = 3 := by omega
    have e3 : q % 3 = 1 := by omega
    rw [e4, e3] at hP
    simp at hP
    have hqc : (q : ℚ) = 12 * k + 7 := by exact_mod_cast hk
    exact s03_mazur_case q (2 * k + 1) 2 _ (by norm_num)
      ((Nat.coprime_mul_left_add_left 1 2 k).2 (by norm_num))
      (by rw [hqc]; push_cast; ring) (by simpa using hP)
  · obtain ⟨k, hk⟩ : ∃ k, q = 12 * k + 11 := ⟨q / 12, by omega⟩
    have e4 : q % 4 = 3 := by omega
    have e3 : q % 3 = 2 := by omega
    rw [e4, e3] at hP
    simp at hP
    have hqc : (q : ℚ) = 12 * k + 11 := by exact_mod_cast hk
    exact s03_mazur_case q (6 * k + 5) 6 _ (by norm_num)
      ((Nat.coprime_mul_left_add_left 5 6 k).2 (by norm_num))
      (by rw [hqc]; push_cast; ring) (by simpa using hP)

/-- `prop:s03-mazur` (`s03-mazur`): weights in `{1,2,3}`, with `2` and `3` each occurring at most
once, are pairwise coprime. -/
theorem mazur_weights_pairwise_coprime {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (hw : ∀ i, w i = 1 ∨ w i = 2 ∨ w i = 3)
    (h2 : (Finset.univ.filter (fun i => w i = 2)).card ≤ 1)
    (h3 : (Finset.univ.filter (fun i => w i = 3)).card ≤ 1) :
    ∀ i j, i ≠ j → Nat.Coprime (w i) (w j) := by
  intro i j hij
  have h2' : ∀ i j, w i = 2 → w j = 2 → i = j := fun i j a b =>
    Finset.card_le_one.mp h2 i (by simp [a]) j (by simp [b])
  have h3' : ∀ i j, w i = 3 → w j = 3 → i = j := fun i j a b =>
    Finset.card_le_one.mp h3 i (by simp [a]) j (by simp [b])
  rcases hw i with a | a | a <;> rcases hw j with b | b | b <;>
    first
    | exact absurd (h2' i j a b) hij
    | exact absurd (h3' i j a b) hij
    | (rw [a, b]; first | decide | norm_num)

end Langlandscape.Graph
