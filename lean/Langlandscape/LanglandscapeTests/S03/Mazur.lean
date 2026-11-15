/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ribet.Mazur

/-! Tests for `Langlandscape.Ribet.Mazur` (S03-L6): `prop:s03-mazur`, the cases `q = 2, 3`, and the shape of
`Ribet.mazur_check`. -/

set_option autoImplicit false

namespace LanglandscapeTests.S03.Mazur

open Langlandscape.Graph Langlandscape.Quat

/-- `prop:s03-mazur` (`s03-mazur`), test: `num ((2-1)/12) = 1`. -/
theorem test_mazurNum_two : mazurNum 2 = 1 := by
  have h : (((2 : ℕ) : ℚ) - 1) / 12 = ((1 : ℤ) : ℚ) / ((12 : ℤ) : ℚ) := by norm_num
  unfold mazurNum
  rw [h]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by first | decide | norm_num)

/-- `prop:s03-mazur` (`s03-mazur`), test: `num ((3-1)/12) = 1`. -/
theorem test_mazurNum_three : mazurNum 3 = 1 := by
  have h : (((3 : ℕ) : ℚ) - 1) / 12 = ((1 : ℤ) : ℚ) / ((6 : ℤ) : ℚ) := by norm_num
  unfold mazurNum
  rw [h]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by first | decide | norm_num)

/-- `prop:s03-mazur` (`s03-mazur`), shape test: `Ribet.mazur_check` for a prime `q = d.D`. -/
theorem test_mazur_check_shape (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hE : Langlandscape.Hyp.EllipticCount d) (q : ℕ) (hq : q.Prime) (hD : d.D = q) :
    Nonempty ((Langlandscape.Ribet.DRgraph d).PhiComb ≃+ ZMod (mazurNum q).natAbs) :=
  ⟨Langlandscape.Ribet.mazur_check d hM hE q hq hD⟩

/-- `prop:s03-mazur` (`s03-mazur`), test `q = 2`: `Φ^comb ≃+ ZMod 1` (trivial). -/
theorem test_mazur_check_two (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hE : Langlandscape.Hyp.EllipticCount d) (hD : d.D = 2) :
    Nonempty ((Langlandscape.Ribet.DRgraph d).PhiComb ≃+ ZMod 1) := by
  have h := Langlandscape.Ribet.mazur_check d hM hE 2 Nat.prime_two hD
  rw [test_mazurNum_two] at h
  exact ⟨h⟩

/-- `prop:s03-mazur` (`s03-mazur`), test `q = 3`: `Φ^comb ≃+ ZMod 1` (trivial). -/
theorem test_mazur_check_three (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hE : Langlandscape.Hyp.EllipticCount d) (hD : d.D = 3) :
    Nonempty ((Langlandscape.Ribet.DRgraph d).PhiComb ≃+ ZMod 1) := by
  have h := Langlandscape.Ribet.mazur_check d hM hE 3 Nat.prime_three hD
  rw [test_mazurNum_three] at h
  exact ⟨h⟩

/-- `ex:s03-mazur` (`s03-mazur`), shape test: the weighted mass sum of `Ribet.sum_inv_wx_Ohat`. -/
theorem test_sum_inv_wx_shape (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (q : ℕ) (hq : q.Prime) (hD : d.D = q) [Fintype (XB d.Ohat)] :
    ∑ c : XB d.Ohat, (1 : ℚ) / (wx d.Ohat (Quotient.out c) : ℚ) = ((q : ℚ) - 1) / 12 :=
  Langlandscape.Ribet.sum_inv_wx_Ohat d hM q hq hD

end LanglandscapeTests.S03.Mazur
