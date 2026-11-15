/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import AlgJL.VolIII.P2.LocalStructure
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Reduced norms of `2`-adic units (RamNrdSurj discharge, part 2)

`mathematics/chapters/s01/1-classsets.tex`, `lem:s01-nrd` (the `ℓ ∣ D` ingredient, `ℓ = 2`).

* `exists_nrd_eq_unit_two` : for `a, b ≠ 0`, every `w ∈ ℤ_2^×` is the reduced norm `nrd x` of some
  `x ∈ QuatAlg ℚ_2 a b` (no ramification hypothesis).

Proof: write `a = 2^α a'`, `b = 2^β b'` with `a', b'` odd and scale the coordinates `x₁, x₂, x₃` by
`2^⌊α/2⌋`, `2^⌊β/2⌋`, `2^⌊(α+β)/2⌋`; the rescaled coefficients `A, B, D` are `≢ 0, 4 (mod 8)`, and a finite check
in `ZMod 8` (`decide`) solves `1 - A x₁² - B x₂² + D x₃² ≡ w (mod 8)`; Hensel's lemma (`hensels_lemma`, via
`PadicInt.toZModPow 3`) then lifts `x₀ = 1` to an exact solution.

Status: *formalized* (proof drafted by mistral-large-4-0 via opencode; see `Hyp/RamNrdSurjDischarge.lean`).
-/

set_option autoImplicit false

namespace Langlandscape.Local

open GL2TF.Quat

/-- `s01-nrd` (auxiliary), finite mod-8 fact: if `A, B, D ∈ ZMod 8` are neither `0` nor `4`, then the form
`1 - A x₁² - B x₂² + D x₃²` represents every unit of `ZMod 8`. -/
private theorem zmod8_cover : ∀ (A B D W : ZMod 8),
    A ≠ 0 → A ≠ 4 → B ≠ 0 → B ≠ 4 → D ≠ 0 → D ≠ 4 → IsUnit W →
    ∃ x1 x2 x3 : ZMod 8, 1 - A * x1 ^ 2 - B * x2 ^ 2 + D * x3 ^ 2 = W := by
  decide

/-- `s01-nrd` (auxiliary): if `A = a'` or `A = 2 a'` with `a'` odd, then `A` is neither `0` nor `4` mod 8. -/
private theorem zmod8_ne_zero_four {A a' : ℤ} (hA : A = a' ∨ A = 2 * a')
    (hodd : ¬ (2:ℤ) ∣ a') : (A : ZMod 8) ≠ 0 ∧ (A : ZMod 8) ≠ 4 := by
  have key : ∀ c : ℤ, (c : ZMod 8) = 0 ↔ (8:ℤ) ∣ c :=
    fun c => ZMod.intCast_zmod_eq_zero_iff_dvd c 8
  have cast4 : ∀ c : ℤ, (c : ZMod 8) - 4 = ((c - 4 : ℤ) : ZMod 8) := by
    intro c; push_cast; ring
  constructor
  · intro h
    rw [key A] at h
    rcases hA with hh | hh <;> rw [hh] at h
    · exact hodd ((by norm_num : (2:ℤ) ∣ 8).trans h)
    · have h4 : (4:ℤ) ∣ a' := by
        rw [show (8:ℤ) = 2 * 4 by norm_num] at h
        exact (Int.mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).1 h
      exact hodd ((by norm_num : (2:ℤ) ∣ 4).trans h4)
  · intro h
    have h0 : ((A - 4 : ℤ) : ZMod 8) = 0 := by
      rw [← cast4 A, h]; ring
    rw [key (A - 4)] at h0
    rcases hA with hh | hh <;> rw [hh] at h0
    · have h2d : (2:ℤ) ∣ a' - 4 := (by norm_num : (2:ℤ) ∣ 8).trans h0
      have h2 : (2:ℤ) ∣ (a' - 4) + 4 := Int.dvd_add h2d (by norm_num)
      rw [Int.sub_add_cancel] at h2
      exact hodd h2
    · rw [show (2:ℤ) * a' - 4 = 2 * (a' - 2) by ring] at h0
      rw [show (8:ℤ) = 2 * 4 by norm_num] at h0
      have h4 : (4:ℤ) ∣ a' - 2 := (Int.mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).1 h0
      have h2 : (2:ℤ) ∣ a' - 2 := (by norm_num : (2:ℤ) ∣ 4).trans h4
      have h3 : (2:ℤ) ∣ (a' - 2) + 2 := Int.dvd_add h2 (by norm_num)
      rw [Int.sub_add_cancel] at h3
      exact hodd h3

/-- `s01-nrd` (auxiliary), scaling identity over a field: `a * (x / 2^e)² = A * x²` when `a = 2^(2e) * A`. -/
private theorem div_sq_eq {K : Type*} [Field K] {a A x : K} {e : ℕ}
    (h : a = (2:K) ^ (2*e) * A) (h2 : (2:K) ≠ 0) :
    a * (x / (2:K)^e)^2 = A * x^2 := by
  have h2e : (2:K)^(2*e) ≠ 0 := pow_ne_zero _ h2
  rw [div_pow, ← pow_mul, mul_comm e 2, ← mul_div_assoc, h, mul_assoc, mul_div_cancel_left₀ _ h2e]

/-- `lem:s01-nrd` (`s01-nrd`), local input at `2`: for `a, b ≠ 0`, the reduced norm on `QuatAlg ℚ_[2] a b` hits
every unit of `ℤ_[2]`. -/
theorem exists_nrd_eq_unit_two {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (w : ℤ_[2]ˣ) :
    ∃ x : QuatAlg ℚ_[2] a b, nrd x = ((w : ℤ_[2]) : ℚ_[2]) := by
  -- valuations and odd parts
  set α := padicValInt 2 a with hαdef
  set β := padicValInt 2 b with hβdef
  have h1 : (2:ℤ) ^ α ∣ a := by exact_mod_cast padicValInt_dvd a
  have h1b : (2:ℤ) ^ β ∣ b := by exact_mod_cast padicValInt_dvd b
  have h2 : ¬ (2:ℤ) ^ (α + 1) ∣ a := by
    intro h
    have h' : ((2:ℕ):ℤ) ^ (α + 1) ∣ a := by simpa using h
    rw [padicValInt_dvd_iff_of_ne_one (by norm_num : (2:ℕ) ≠ 1)] at h'
    rcases h' with h0 | hle
    · exact ha h0
    · rw [hαdef] at hle; omega
  have h2b : ¬ (2:ℤ) ^ (β + 1) ∣ b := by
    intro h
    have h' : ((2:ℕ):ℤ) ^ (β + 1) ∣ b := by simpa using h
    rw [padicValInt_dvd_iff_of_ne_one (by norm_num : (2:ℕ) ≠ 1)] at h'
    rcases h' with h0 | hle
    · exact hb h0
    · rw [hβdef] at hle; omega
  set a' := a / (2:ℤ) ^ α with ha'def
  set b' := b / (2:ℤ) ^ β with hb'def
  have ha' : (2:ℤ) ^ α * a' = a := Int.mul_ediv_cancel' h1
  have hb' : (2:ℤ) ^ β * b' = b := Int.mul_ediv_cancel' h1b
  have ha'odd : ¬ (2:ℤ) ∣ a' := by
    intro h
    apply h2
    rw [← ha', pow_succ]
    exact mul_dvd_mul_left _ h
  have hb'odd : ¬ (2:ℤ) ∣ b' := by
    intro h
    apply h2b
    rw [← hb', pow_succ]
    exact mul_dvd_mul_left _ h
  have hab'odd : ¬ (2:ℤ) ∣ a' * b' := by
    intro h
    rcases Int.prime_two.dvd_mul.mp h with h' | h'
    · exact ha'odd h'
    · exact hb'odd h'
  -- scaled coefficients
  set eI := α / 2 with heIdef
  set eJ := β / 2 with heJdef
  set eK := (α + β) / 2 with heKdef
  set A := if α % 2 = 0 then a' else 2 * a' with hAdef
  set B := if β % 2 = 0 then b' else 2 * b' with hBdef
  set D := if (α + β) % 2 = 0 then a' * b' else 2 * (a' * b') with hDdef
  have hAform : A = a' ∨ A = 2 * a' := by
    rw [hAdef]; split <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hBform : B = b' ∨ B = 2 * b' := by
    rw [hBdef]; split <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hDform : D = a' * b' ∨ D = 2 * (a' * b') := by
    rw [hDdef]; split <;> [exact Or.inl rfl; exact Or.inr rfl]
  have keyA : ((2:ℤ)) ^ (2 * eI) * A = a := by
    rcases Nat.mod_two_eq_zero_or_one α with h | h
    · rw [hAdef, ite_eq_left h, heIdef]
      have h2e : 2 * (α / 2) = α := by omega
      rw [h2e]; exact ha'
    · rw [hAdef, ite_eq_right (by omega), heIdef]
      have h2e : 2 * (α / 2) = α - 1 := by omega
      rw [h2e]
      have hpow : ((2:ℤ)) ^ (α - 1) * (2 * a') = ((2:ℤ)) ^ α * a' := by
        have hα1 : α - 1 + 1 = α := by omega
        rw [← mul_assoc, ← pow_succ, hα1]
      rw [hpow]; exact ha'
  have keyB : ((2:ℤ)) ^ (2 * eJ) * B = b := by
    rcases Nat.mod_two_eq_zero_or_one β with h | h
    · rw [hBdef, ite_eq_left h, heJdef]
      have h2e : 2 * (β / 2) = β := by omega
      rw [h2e]; exact hb'
    · rw [hBdef, ite_eq_right (by omega), heJdef]
      have h2e : 2 * (β / 2) = β - 1 := by omega
      rw [h2e]
      have hpow : ((2:ℤ)) ^ (β - 1) * (2 * b') = ((2:ℤ)) ^ β * b' := by
        have hβ1 : β - 1 + 1 = β := by omega
        rw [← mul_assoc, ← pow_succ, hβ1]
      rw [hpow]; exact hb'
  have keyD : ((2:ℤ)) ^ (2 * eK) * D = a * b := by
    rcases Nat.mod_two_eq_zero_or_one (α + β) with h | h
    · rw [hDdef, ite_eq_left h, heKdef]
      have h2e : 2 * ((α + β) / 2) = α + β := by omega
      rw [h2e, pow_add, ← ha', ← hb']
      ring
    · rw [hDdef, ite_eq_right (by omega), heKdef]
      have h2e : 2 * ((α + β) / 2) = α + β - 1 := by omega
      rw [h2e]
      have hpow : ((2:ℤ)) ^ (α + β - 1) * (2 * (a' * b')) =
          ((2:ℤ)) ^ (α + β) * (a' * b') := by
        have hα1 : α + β - 1 + 1 = α + β := by omega
        rw [← mul_assoc, ← pow_succ, hα1]
      rw [hpow, pow_add, ← ha', ← hb']
      ring
  -- mod-8 data
  have hAzmod := zmod8_ne_zero_four hAform ha'odd
  have hBzmod := zmod8_ne_zero_four hBform hb'odd
  have hDzmod := zmod8_ne_zero_four hDform hab'odd
  have hW'unit : IsUnit (PadicInt.toZModPow 3 (w : ℤ_[2])) := w.isUnit.map _
  obtain ⟨x1', x2', x3', hEq⟩ := zmod8_cover (A : ZMod 8) (B : ZMod 8) (D : ZMod 8)
    (PadicInt.toZModPow 3 (w : ℤ_[2])) hAzmod.1 hAzmod.2 hBzmod.1 hBzmod.2 hDzmod.1 hDzmod.2
    hW'unit
  -- the equation, viewed in `ZMod (2^3)`
  have hEq' : 1 - (A : ZMod (2^3)) * x1' ^ 2 - (B : ZMod (2^3)) * x2' ^ 2 +
      (D : ZMod (2^3)) * x3' ^ 2 = PadicInt.toZModPow 3 (w : ℤ_[2]) := hEq
  -- lifts to ℤ_[2]
  set x1t : ℤ_[2] := ((x1'.val : ℕ) : ℤ_[2]) with hx1tdef
  set x2t : ℤ_[2] := ((x2'.val : ℕ) : ℤ_[2]) with hx2tdef
  set x3t : ℤ_[2] := ((x3'.val : ℕ) : ℤ_[2]) with hx3tdef
  have hc1 : PadicInt.toZModPow 3 x1t = x1' := by
    rw [hx1tdef, map_natCast]; exact ZMod.natCast_zmod_val x1'
  have hc2 : PadicInt.toZModPow 3 x2t = x2' := by
    rw [hx2tdef, map_natCast]; exact ZMod.natCast_zmod_val x2'
  have hc3 : PadicInt.toZModPow 3 x3t = x3' := by
    rw [hx3tdef, map_natCast]; exact ZMod.natCast_zmod_val x3'
  -- Hensel setup
  set c : ℤ_[2] := (A : ℤ_[2]) * x1t ^ 2 + (B : ℤ_[2]) * x2t ^ 2 - (D : ℤ_[2]) * x3t ^ 2 +
    (w : ℤ_[2]) with hcdef
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C c with hFdef
  have hF1 : F.aeval (1 : ℤ_[2]) = 1 - c := by simp [hFdef]
  have hcong : (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2^3)) (F.aeval (1 : ℤ_[2])) = 0 := by
    rw [hF1, map_sub, map_one, hcdef]
    simp only [map_add, map_mul, map_pow, map_sub, map_intCast]
    rw [hc1, hc2, hc3]
    linear_combination hEq'
  have hmem : F.aeval (1 : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2^3)) := by
    rw [RingHom.mem_ker]; exact hcong
  rw [PadicInt.ker_toZModPow] at hmem
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ ≤ (2:ℝ) ^ (-3:ℤ) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ 3).2 hmem
  have hderiv : F.derivative.aeval (1 : ℤ_[2]) = 2 := by simp [hFdef]; norm_num
  have hderiv_norm : ‖F.derivative.aeval (1 : ℤ_[2])‖ = (2:ℝ)⁻¹ := by
    rw [hderiv]
    exact_mod_cast PadicInt.norm_p (p := 2)
  have hlt : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hderiv_norm]
    refine lt_of_le_of_lt hnorm ?_
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  have hz' : z ^ 2 - c = 0 := by simpa [hFdef] using hz
  have hz2 : z ^ 2 = c := sub_eq_zero.mp hz'
  -- assemble the quaternion
  have hAq : (a : ℚ_[2]) = ((2:ℚ_[2]) ^ (2 * eI)) * (A : ℚ_[2]) := by exact_mod_cast keyA.symm
  have hBq : (b : ℚ_[2]) = ((2:ℚ_[2]) ^ (2 * eJ)) * (B : ℚ_[2]) := by exact_mod_cast keyB.symm
  have hDq : (a : ℚ_[2]) * (b : ℚ_[2]) = ((2:ℚ_[2]) ^ (2 * eK)) * (D : ℚ_[2]) := by
    exact_mod_cast keyD.symm
  have h2q : (2:ℚ_[2]) ≠ 0 := by norm_num
  have hdiv1 : (a : ℚ_[2]) * (((x1t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eI) ^ 2 =
      (A : ℚ_[2]) * ((x1t : ℤ_[2]) : ℚ_[2]) ^ 2 :=
    div_sq_eq hAq h2q
  have hdiv2 : (b : ℚ_[2]) * (((x2t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eJ) ^ 2 =
      (B : ℚ_[2]) * ((x2t : ℤ_[2]) : ℚ_[2]) ^ 2 :=
    div_sq_eq hBq h2q
  have hdiv3 : (a : ℚ_[2]) * (b : ℚ_[2]) * (((x3t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eK) ^ 2 =
      (D : ℚ_[2]) * ((x3t : ℤ_[2]) : ℚ_[2]) ^ 2 :=
    div_sq_eq hDq h2q
  have hz2q : ((z ^ 2 : ℤ_[2]) : ℚ_[2]) = ((c : ℤ_[2]) : ℚ_[2]) :=
    congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz2
  refine ⟨⟨(z : ℚ_[2]), ((x1t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eI,
    ((x2t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eJ, ((x3t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eK⟩, ?_⟩
  have hnrd : nrd (⟨(z : ℚ_[2]), ((x1t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eI,
      ((x2t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eJ, ((x3t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eK⟩ :
      QuatAlg ℚ_[2] a b) =
      (z : ℚ_[2]) ^ 2 - (a : ℚ_[2]) * (((x1t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eI) ^ 2 -
        (b : ℚ_[2]) * (((x2t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eJ) ^ 2 +
          (a : ℚ_[2]) * (b : ℚ_[2]) * (((x3t : ℤ_[2]) : ℚ_[2]) / (2:ℚ_[2]) ^ eK) ^ 2 := rfl
  rw [hnrd, hdiv1, hdiv2, hdiv3]
  push_cast at hz2q
  rw [hcdef] at hz2q
  push_cast at hz2q
  linear_combination hz2q

end Langlandscape.Local
