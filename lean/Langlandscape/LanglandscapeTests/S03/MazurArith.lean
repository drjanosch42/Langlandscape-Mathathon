/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.MazurArith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases

/-! Tests for `Langlandscape.Graph.MazurArith` (S03-L5): `prop:s03-mazur`, `ex:s03-mazur`. -/

set_option autoImplicit false

namespace LanglandscapeTests.S03.MazurArith

open Langlandscape.Graph

/-- `ex:s03-mazur` (`s03-mazur`), test: `q = 11` gives `num ((q-1)/12) = 5`. -/
theorem test_mazur_11 : mazurNum 11 = 5 := by
  have hs : ∑ i : Fin 2, (1 : ℚ) / (![2,3] i : ℕ) = ((11 : ℕ) - 1 : ℚ) / 12 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have h := mazur_prod_mul_sum (ι := Fin 2) 11 (by norm_num) (by norm_num) ![2,3]
    (by intro i; fin_cases i <;> simp)
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ])
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ]) hs
  have hp : (∏ i : Fin 2, (![2,3] i : ℕ)) = 6 := by
    simp [Fin.prod_univ_succ]
  rw [hp, hs] at h
  have h' : ((mazurNum 11 : ℤ) : ℚ) = 5 := by
    rw [← h]; norm_num
  exact_mod_cast h'

/-- `ex:s03-mazur` (`s03-mazur`), test: `q = 23` gives `num ((q-1)/12) = 11`. -/
theorem test_mazur_23 : mazurNum 23 = 11 := by
  have hs : ∑ i : Fin 3, (1 : ℚ) / (![1,2,3] i : ℕ) = ((23 : ℕ) - 1 : ℚ) / 12 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have h := mazur_prod_mul_sum (ι := Fin 3) 23 (by norm_num) (by norm_num) ![1,2,3]
    (by intro i; fin_cases i <;> simp)
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ])
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ]) hs
  have hp : (∏ i : Fin 3, (![1,2,3] i : ℕ)) = 6 := by
    simp [Fin.prod_univ_succ]
  rw [hp, hs] at h
  have h' : ((mazurNum 23 : ℤ) : ℚ) = 11 := by
    rw [← h]; norm_num
  exact_mod_cast h'

/-- `ex:s03-mazur` (`s03-mazur`), test: `q = 37` gives `num ((q-1)/12) = 3`. -/
theorem test_mazur_37 : mazurNum 37 = 3 := by
  have hs : ∑ i : Fin 3, (1 : ℚ) / (![1,1,1] i : ℕ) = ((37 : ℕ) - 1 : ℚ) / 12 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have h := mazur_prod_mul_sum (ι := Fin 3) 37 (by norm_num) (by norm_num) ![1,1,1]
    (by intro i; fin_cases i <;> simp)
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ])
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ]) hs
  have hp : (∏ i : Fin 3, (![1,1,1] i : ℕ)) = 1 := by
    simp [Fin.prod_univ_succ]
  rw [hp, hs] at h
  have h' : ((mazurNum 37 : ℤ) : ℚ) = 3 := by
    rw [← h]; norm_num
  exact_mod_cast h'

/-- `ex:s03-mazur` (`s03-mazur`), test: `q = 101` gives `num ((q-1)/12) = 25`. -/
theorem test_mazur_101 : mazurNum 101 = 25 := by
  have hs : ∑ i : Fin 9, (1 : ℚ) / (![1,1,1,1,1,1,1,1,3] i : ℕ) = ((101 : ℕ) - 1 : ℚ) / 12 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have h := mazur_prod_mul_sum (ι := Fin 9) 101 (by norm_num) (by norm_num) ![1,1,1,1,1,1,1,1,3]
    (by intro i; fin_cases i <;> simp)
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ])
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ]) hs
  have hp : (∏ i : Fin 9, (![1,1,1,1,1,1,1,1,3] i : ℕ)) = 3 := by
    simp [Fin.prod_univ_succ]
  rw [hp, hs] at h
  have h' : ((mazurNum 101 : ℤ) : ℚ) = 25 := by
    rw [← h]; norm_num
  exact_mod_cast h'

/-- `ex:s03-mazur` (`s03-mazur`), test: `q = 131` gives `num ((q-1)/12) = 65`. -/
theorem test_mazur_131 : mazurNum 131 = 65 := by
  have hs : ∑ i : Fin 12, (1 : ℚ) / (![1,1,1,1,1,1,1,1,1,1,2,3] i : ℕ) = ((131 : ℕ) - 1 : ℚ) / 12 := by
    simp [Fin.sum_univ_succ]
    norm_num
  have h := mazur_prod_mul_sum (ι := Fin 12) 131 (by norm_num) (by norm_num) ![1,1,1,1,1,1,1,1,1,1,2,3]
    (by intro i; fin_cases i <;> simp)
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ])
    (by first | decide | simp [Finset.card_filter, Fin.sum_univ_succ]) hs
  have hp : (∏ i : Fin 12, (![1,1,1,1,1,1,1,1,1,1,2,3] i : ℕ)) = 6 := by
    simp [Fin.prod_univ_succ]
  rw [hp, hs] at h
  have h' : ((mazurNum 131 : ℤ) : ℚ) = 65 := by
    rw [← h]; norm_num
  exact_mod_cast h'

/-- `prop:s03-mazur` (`s03-mazur`), test: weights `(2,3)` (`q = 11`) are pairwise coprime. -/
theorem test_coprime_11 : ∀ i j : Fin 2, i ≠ j → Nat.Coprime (![2, 3] i) (![2, 3] j) :=
  mazur_weights_pairwise_coprime (ι := Fin 2) ![2, 3]
    (by intro i; fin_cases i <;> simp) (by decide) (by decide)

end LanglandscapeTests.S03.MazurArith
