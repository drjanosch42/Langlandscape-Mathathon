/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.GL2Levels

/-!
# Non-vacuity tests for `Langlandscape.Local.GL2Levels` (S01-L3a)
-/

open Langlandscape.Local

section
variable (ℓ : ℕ) [Fact ℓ.Prime]

example : (1 : GL (Fin 2) ℚ_[ℓ]) ∈ K1 ℓ 3 := one_mem _

/-- The standard unipotent `!![1, 1; 0, 1]` lies in `K1 ℓ e` for every `e`. -/
example (e : ℕ) : matGL (1 : ℚ_[ℓ]) 1 0 1 (by simp) ∈ K1 ℓ e :=
  mem_K1_of_entries 1 1 0 1 (by simp) (by simp) (dvd_zero _) (by simp)

/-- The lower unipotent `!![1, 0; ℓ, 1]` is in `Iw ℓ` but not in `K0 ℓ 2`. -/
example : matGL (1 : ℚ_[ℓ]) 0 (ℓ : ℚ_[ℓ]) 1 (by simp) ∈ Iw ℓ :=
  mem_K0_of_entries 1 0 (ℓ : ℤ_[ℓ]) 1 (by simp) (by simp) (by simp)

example : matGL (1 : ℚ_[ℓ]) 0 (ℓ : ℚ_[ℓ]) 1 (by simp) ∉ K0 ℓ 2 := by
  intro h
  obtain ⟨a, b, c, d, hM, -, ⟨k, hk⟩⟩ := mem_K0_iff_exists.1 h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[ℓ] => M 1 0) hM
  simp at h10
  have hc : c = (ℓ : ℤ_[ℓ]) := by apply Subtype.ext; simpa using h10.symm
  subst hc
  have hℓ : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have : (1 : ℤ_[ℓ]) = ℓ * k := by
    apply mul_left_cancel₀ hℓ; rw [pow_two] at hk; linear_combination hk
  have h1 := congrArg (fun z : ℤ_[ℓ] => ‖z‖) this
  have hk1 := PadicInt.norm_le_one k
  simp only [norm_one, norm_mul, PadicInt.norm_p] at h1
  have hp : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)
  have := mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg ℓ : (0:ℝ) ≤ ℓ)) hk1
  linarith

/-- Level `0` is the full `GL₂(ℤ_ℓ)`. -/
example : K0 ℓ 0 = GL2Zl ℓ := K0_zero
example : K1 ℓ 2 ≤ Iw ℓ := (K1_le_K0 2).trans (K0_succ_le 1)
example (u : ℤ_[ℓ]ˣ) : diagGL (intUnit u) 1 ∈ K1 ℓ 5 := diag_one_mem_K1 u 5
end
