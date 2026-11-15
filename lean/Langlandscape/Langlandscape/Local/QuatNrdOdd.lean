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
# Reduced norms of `p`-adic units at odd primes (RamNrdSurj discharge, part 1)

`mathematics/chapters/s01/1-classsets.tex`, `lem:s01-nrd` (the `ℓ ∣ D` ingredient, odd `ℓ`).

* `exists_nrd_eq_unit_of_ne_two` : for an odd prime `p` and `a, b ≠ 0`, every `w ∈ ℤ_p^×` is the reduced norm
  `nrd x` of some `x ∈ QuatAlg ℚ_p a b` (no ramification hypothesis).

Proof: among the three "planes" spanned by `1` and `i`, `j`, `k` (reduced norms `X² - a Y²`, `X² - b Y²`,
`X² + ab Y²`) one has a coefficient `c ∈ {-a, -b, ab}` of even `p`-adic valuation; rescaling reduces to a unit
coefficient, and the binary form `x² - c y²` represents every unit: mod `p` by counting squares in `ZMod p`,
then exactly by Hensel's lemma (`hensels_lemma`).

Status: *formalized* (proof drafted by mistral-large-4-0 via opencode; see `Hyp/RamNrdSurjDischarge.lean`).
-/

set_option autoImplicit false

namespace Langlandscape.Local

open GL2TF.Quat

/-! ### Small `ℤ_[p]` facts -/

/-- `s01-nrd` (auxiliary): an element of `ℤ_[p]` reducing to `0` in `ZMod p` has norm `< 1`. -/
private theorem norm_lt_one_of_toZMod_eq_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (h : PadicInt.toZMod x = 0) : ‖x‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd]
  have h1 : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := RingHom.mem_ker.mpr h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  exact h1

/-- `s01-nrd` (auxiliary): an element of `ℤ_[p]` with nonzero reduction in `ZMod p` is a unit. -/
private theorem isUnit_of_toZMod_ne_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  have hle : ‖x‖ ≤ 1 := PadicInt.norm_le_one x
  by_contra hne
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne hle hne
  obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
  apply h
  rw [hy, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- `s01-nrd` (auxiliary): `2` is a unit of `ℤ_[p]` for `p ≠ 2`. -/
private theorem isUnit_two_of_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  apply isUnit_of_toZMod_ne_zero
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have e : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by norm_num
    rw [← e, ZMod.natCast_eq_zero_iff] at h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  have h3 : PadicInt.toZMod (2 : ℤ_[p]) = (2 : ZMod p) := by
    have e : (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) := by norm_num
    rw [e, map_intCast]
    norm_num
  rw [h3]
  exact h2

/-! ### The mod-`p` counting argument -/

/-- `s01-nrd` (auxiliary): over `ZMod p` with `p` odd, `α² - c β² = w` has a solution with `(α, β) ≠ (0, 0)`. -/
private theorem exists_sq_sub_mul_sq_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c w : ZMod p)
    (hc : c ≠ 0) (hw : w ≠ 0) :
    ∃ α β : ZMod p, α ^ 2 - c * β ^ 2 = w ∧ (α ≠ 0 ∨ β ≠ 0) := by
  classical
  have : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  set S := (Finset.univ : Finset (ZMod p)).image (fun x => x ^ 2) with hS
  have hfib : ∀ b ∈ S, (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)).card =
      if b = 0 then 1 else 2 := by
    intro b hb
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hb
    have hr' : r ^ 2 = b := hr
    by_cases hb0 : b = 0
    · rw [ite_eq_left hb0]
      have h1 : (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)) = {0} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [hb0]
        exact pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)
      rw [h1, Finset.card_singleton]
    · rw [ite_eq_right hb0]
      have hr0 : r ≠ 0 := by
        intro h
        apply hb0
        rw [← hr', h, zero_pow (by omega : (2 : ℕ) ≠ 0)]
      have hne : r ≠ -r := fun h =>
        hr0 ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp h.symm)
      have h1 : (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)) = {r, -r} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rw [← hr']
        exact sq_eq_sq_iff_eq_or_eq_neg
      rw [h1, Finset.card_pair hne]
  have hsum : p = ∑ b ∈ S, (Finset.univ.filter (fun a : ZMod p => a ^ 2 = b)).card := by
    have h := Finset.card_eq_sum_card_image (fun x : ZMod p => x ^ 2)
      (Finset.univ : Finset (ZMod p))
    rw [Finset.card_univ, hcard] at h
    exact h
  have hS2 : 2 * S.card = p + 1 := by
    have h0 : (0 : ZMod p) ∈ S := by
      rw [hS, Finset.mem_image]
      exact ⟨0, Finset.mem_univ 0, by simp⟩
    have hsum' : p = ∑ b ∈ S, (if b = 0 then (1 : ℕ) else 2) :=
      hsum.trans (Finset.sum_congr rfl (fun b hb => hfib b hb))
    rw [← Finset.insert_erase h0, Finset.sum_insert (Finset.notMem_erase 0 S)] at hsum'
    rw [ite_eq_left rfl] at hsum'
    have h2 : ∑ b ∈ S.erase 0, (if b = 0 then (1 : ℕ) else 2) = 2 * (S.erase 0).card := by
      have h3 : ∀ b ∈ S.erase 0, (if b = 0 then (1 : ℕ) else 2) = 2 :=
        fun b hb => ite_eq_right (Finset.ne_of_mem_erase hb)
      rw [Finset.sum_congr rfl h3, Finset.sum_const]
      simp [mul_comm]
    rw [h2, Finset.card_erase_of_mem h0] at hsum'
    have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, h0⟩
    omega
  set T := S.image (fun z => w + c * z) with hT
  have hcardT : T.card = S.card := by
    refine Finset.card_image_of_injOn (fun z1 _ z2 _ h => ?_)
    have h2 : c * (z1 - z2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc
    · exact sub_eq_zero.mp h
  have hne : ∃ z, z ∈ S ∧ z ∈ T := by
    by_contra hcon
    push Not at hcon
    have hempty : S ∩ T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun z hz =>
      hcon z (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2
    have hdisj : Disjoint S T := Finset.disjoint_iff_inter_eq_empty.mpr hempty
    have hunion : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
    have hle : (S ∪ T).card ≤ p := by
      have h3 := Finset.card_le_univ (S ∪ T)
      rwa [hcard] at h3
    rw [hunion, hcardT] at hle
    omega
  obtain ⟨z, hzS, hzT⟩ := hne
  obtain ⟨α, -, hα⟩ := Finset.mem_image.mp hzS
  obtain ⟨u, huS, hu⟩ := Finset.mem_image.mp hzT
  obtain ⟨β, -, hβ⟩ := Finset.mem_image.mp huS
  have hα' : α ^ 2 = z := hα
  have hu' : w + c * u = z := hu
  have hβ' : β ^ 2 = u := hβ
  refine ⟨α, β, ?_, ?_⟩
  · rw [hα', ← hu', hβ']; ring
  · by_contra h
    push Not at h
    obtain ⟨hα0, hβ0⟩ := h
    have hz0 : z = 0 := by rw [← hα', hα0, zero_pow (by omega : (2 : ℕ) ≠ 0)]
    have hu0 : u = 0 := by rw [← hβ', hβ0, zero_pow (by omega : (2 : ℕ) ≠ 0)]
    rw [hz0, hu0] at hu'
    simp only [mul_zero, add_zero] at hu'
    exact hw hu'

/-! ### The binary quadratic form over `ℤ_[p]`, `p` odd -/

/-- `s01-nrd` (auxiliary): for odd `p`, the binary form `x² - c y²` over `ℤ_[p]` represents every unit. -/
private theorem exists_sq_sub_mul_sq_eq_unit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c w : ℤ_[p]ˣ) :
    ∃ x y : ℤ_[p], x ^ 2 - (c : ℤ_[p]) * y ^ 2 = (w : ℤ_[p]) := by
  classical
  have h2u : IsUnit (2 : ℤ_[p]) := isUnit_two_of_ne_two hp
  have h2n : ‖(2 : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp h2u
  have hc' : PadicInt.toZMod (c : ℤ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(c : ℤ_[p])‖ < 1 := norm_lt_one_of_toZMod_eq_zero h
    rw [PadicInt.norm_units c] at h1
    exact lt_irrefl 1 h1
  have hw' : PadicInt.toZMod (w : ℤ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(w : ℤ_[p])‖ < 1 := norm_lt_one_of_toZMod_eq_zero h
    rw [PadicInt.norm_units w] at h1
    exact lt_irrefl 1 h1
  obtain ⟨α, β, heq, hne⟩ := exists_sq_sub_mul_sq_zmod p hp _ _ hc' hw'
  have hlift : ∀ γ : ZMod p, PadicInt.toZMod (γ.val : ℤ_[p]) = γ := by
    intro γ
    simp
  by_cases hα0 : α = 0
  · -- `α = 0`, so `β ≠ 0`; solve `c y² + w = 0` for `y` by Hensel
    have hβ0 : β ≠ 0 := by
      rcases hne with h | h
      · exact absurd hα0 h
      · exact h
    have hbtu : IsUnit (β.val : ℤ_[p]) := isUnit_of_toZMod_ne_zero (by rw [hlift]; exact hβ0)
    have hbtn : ‖(β.val : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hbtu
    have hcn : ‖(c : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp c.isUnit
    set G : Polynomial ℤ_[p] := Polynomial.C (c : ℤ_[p]) * Polynomial.X ^ 2 +
      Polynomial.C (w : ℤ_[p]) with hG
    have hGe : ∀ y : ℤ_[p], G.aeval y = (c : ℤ_[p]) * y ^ 2 + (w : ℤ_[p]) := by
      intro y
      simp [hG]
    have hGd : G.derivative.aeval (β.val : ℤ_[p]) = (c : ℤ_[p]) * 2 * (β.val : ℤ_[p]) := by
      have hder : G.derivative = Polynomial.C ((c : ℤ_[p]) * 2) * Polynomial.X := by
        rw [hG, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_sq,
          Polynomial.derivative_C, add_zero]
      rw [hder]
      simp
    have hG0 : PadicInt.toZMod (G.aeval (β.val : ℤ_[p])) = 0 := by
      rw [hGe]
      simp only [map_add, map_mul, map_pow, hlift]
      rw [hα0] at heq
      linear_combination -heq
    have hlt : ‖G.aeval (β.val : ℤ_[p])‖ < 1 := norm_lt_one_of_toZMod_eq_zero hG0
    have hGdN : ‖G.derivative.aeval (β.val : ℤ_[p])‖ = 1 := by
      rw [hGd, norm_mul, norm_mul, hcn, h2n, hbtn]
      simp
    have hnorm : ‖G.aeval (β.val : ℤ_[p])‖ < ‖G.derivative.aeval (β.val : ℤ_[p])‖ ^ 2 := by
      rw [hGdN, one_pow]
      exact hlt
    obtain ⟨y, hy, _⟩ := hensels_lemma hnorm
    refine ⟨0, y, ?_⟩
    rw [hGe] at hy
    linear_combination -hy
  · -- `α ≠ 0`; solve `x² = c β̃² + w` for `x` by Hensel
    have hαu : IsUnit (α.val : ℤ_[p]) := isUnit_of_toZMod_ne_zero (by rw [hlift]; exact hα0)
    have hαn : ‖(α.val : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hαu
    set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 -
      Polynomial.C ((c : ℤ_[p]) * (β.val : ℤ_[p]) ^ 2 + (w : ℤ_[p])) with hF
    have hFe : ∀ x : ℤ_[p], F.aeval x =
        x ^ 2 - ((c : ℤ_[p]) * (β.val : ℤ_[p]) ^ 2 + (w : ℤ_[p])) := by
      intro x
      simp [hF]
    have hFd : F.derivative.aeval (α.val : ℤ_[p]) = 2 * (α.val : ℤ_[p]) := by
      have hder : F.derivative = Polynomial.C (2 : ℤ_[p]) * Polynomial.X := by
        rw [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero]
        simp
      rw [hder]
      simp
    have hF0 : PadicInt.toZMod (F.aeval (α.val : ℤ_[p])) = 0 := by
      rw [hFe]
      simp only [map_sub, map_pow, map_mul, map_add, hlift]
      linear_combination heq
    have hlt : ‖F.aeval (α.val : ℤ_[p])‖ < 1 := norm_lt_one_of_toZMod_eq_zero hF0
    have hFdN : ‖F.derivative.aeval (α.val : ℤ_[p])‖ = 1 := by
      rw [hFd, norm_mul, h2n, hαn, mul_one]
    have hnorm : ‖F.aeval (α.val : ℤ_[p])‖ < ‖F.derivative.aeval (α.val : ℤ_[p])‖ ^ 2 := by
      rw [hFdN, one_pow]
      exact hlt
    obtain ⟨x, hx, _⟩ := hensels_lemma hnorm
    refine ⟨x, (β.val : ℤ_[p]), ?_⟩
    rw [hFe] at hx
    linear_combination hx

/-! ### Assembly -/

/-- `s01-nrd` (auxiliary): given `d ≠ 0` with even `p`-adic valuation and a "plane" `mk` whose reduced norm is
`X² + d Y²`, every unit is a reduced norm. -/
private theorem exists_nrd_eq_unit_of_plane {a b : ℤ} (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (w : ℤ_[p]ˣ)
    (d : ℤ) (hd : d ≠ 0) (heven : Even (padicValInt p d))
    (mk : ℚ_[p] → ℚ_[p] → QuatAlg ℚ_[p] a b)
    (hnrd : ∀ X Y : ℚ_[p], nrd (mk X Y) = X ^ 2 + (d : ℚ_[p]) * Y ^ 2) :
    ∃ x : QuatAlg ℚ_[p] a b, nrd x = ((w : ℤ_[p]) : ℚ_[p]) := by
  classical
  obtain ⟨m, hm⟩ := heven
  have hv2 : padicValInt p d = 2 * m := by rw [hm, two_mul]
  obtain ⟨d₀, hd₀⟩ := padicValInt_dvd (p := p) d
  rw [hv2] at hd₀
  have hd₀ne : d₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd₀
    exact hd hd₀
  have hnotdvd : ¬ (p : ℤ) ∣ d₀ := by
    intro h
    have h1 : (p : ℤ) ^ (2 * m + 1) ∣ d := by
      rw [hd₀, pow_succ]
      exact mul_dvd_mul_left _ h
    rcases (padicValInt_dvd_iff (2 * m + 1) d).mp h1 with h0 | hle
    · exact hd h0
    · rw [hv2] at hle; omega
  have hd₀u : IsUnit ((d₀ : ℤ_[p])) := by
    apply isUnit_of_toZMod_ne_zero
    intro h
    rw [map_intCast] at h
    exact hnotdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd d₀ p).mp h)
  obtain ⟨u, hu⟩ := hd₀u
  obtain ⟨x₀, y, hbin⟩ := exists_sq_sub_mul_sq_eq_unit p hp (-u) w
  have hneg : ((-u : ℤ_[p]ˣ) : ℤ_[p]) = -(u : ℤ_[p]) := Units.val_neg u
  have hbin' : x₀ ^ 2 + (d₀ : ℤ_[p]) * y ^ 2 = (w : ℤ_[p]) := by
    rw [hneg, hu] at hbin
    linear_combination hbin
  have hpne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  set P := (p : ℚ_[p]) ^ m with hP
  have hPn : P ≠ 0 := pow_ne_zero _ hpne
  have hP2 : P ^ 2 = (p : ℚ_[p]) ^ (2 * m) := by
    rw [hP, ← pow_mul, mul_comm m 2]
  have hd_cast : (d : ℚ_[p]) = (p : ℚ_[p]) ^ (2 * m) * (d₀ : ℚ_[p]) := by
    have h := congrArg (Int.cast : ℤ → ℚ_[p]) hd₀
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h
    exact h
  have hbin_cast : ((x₀ : ℤ_[p]) : ℚ_[p]) ^ 2 + (d₀ : ℚ_[p]) * ((y : ℤ_[p]) : ℚ_[p]) ^ 2
      = ((w : ℤ_[p]) : ℚ_[p]) := by
    have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hbin'
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_intCast] at h
    exact h
  refine ⟨mk ((x₀ : ℤ_[p]) : ℚ_[p]) (((y : ℤ_[p]) : ℚ_[p]) / P), ?_⟩
  rw [hnrd, hd_cast, ← hP2]
  have hkey : (P ^ 2 * (d₀ : ℚ_[p])) * (((y : ℤ_[p]) : ℚ_[p]) / P) ^ 2
      = (d₀ : ℚ_[p]) * ((y : ℤ_[p]) : ℚ_[p]) ^ 2 := by
    rw [div_pow, ← mul_div_assoc, mul_assoc (P ^ 2) (d₀ : ℚ_[p])]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hPn)
  rw [hkey]
  exact hbin_cast

/-- `lem:s01-nrd` (`s01-nrd`), local input at odd primes: for an odd prime `p` and `a, b ≠ 0`, the reduced norm on
`QuatAlg ℚ_[p] a b` hits every unit of `ℤ_[p]`. -/
theorem exists_nrd_eq_unit_of_ne_two {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (w : ℤ_[p]ˣ) :
    ∃ x : QuatAlg ℚ_[p] a b, nrd x = ((w : ℤ_[p]) : ℚ_[p]) := by
  classical
  by_cases haE : Even (padicValInt p a)
  · have hv : padicValInt p (-a) = padicValInt p a := by
      simp [padicValInt, Int.natAbs_neg]
    exact exists_nrd_eq_unit_of_plane p hp w (-a) (neg_ne_zero.mpr ha) (by rwa [hv])
      (fun X Y => (⟨X, Y, 0, 0⟩ : QuatAlg ℚ_[p] a b))
      (fun X Y => by
        have h1 : nrd (⟨X, Y, 0, 0⟩ : QuatAlg ℚ_[p] a b) = X ^ 2 - (a : ℚ_[p]) * Y ^ 2 := by
          simp [nrd]
        rw [h1]
        have h2 : (((-a : ℤ) : ℚ_[p])) = -(a : ℚ_[p]) := by simp
        rw [h2]
        ring)
  · by_cases hbE : Even (padicValInt p b)
    · have hv : padicValInt p (-b) = padicValInt p b := by
        simp [padicValInt, Int.natAbs_neg]
      exact exists_nrd_eq_unit_of_plane p hp w (-b) (neg_ne_zero.mpr hb) (by rwa [hv])
        (fun X Y => (⟨X, 0, Y, 0⟩ : QuatAlg ℚ_[p] a b))
        (fun X Y => by
          have h1 : nrd (⟨X, 0, Y, 0⟩ : QuatAlg ℚ_[p] a b) = X ^ 2 - (b : ℚ_[p]) * Y ^ 2 := by
            simp [nrd]
          rw [h1]
          have h2 : (((-b : ℤ) : ℚ_[p])) = -(b : ℚ_[p]) := by simp
          rw [h2]
          ring)
    · have hv : padicValInt p (a * b) = padicValInt p a + padicValInt p b :=
        padicValInt.mul ha hb
      have heven : Even (padicValInt p a + padicValInt p b) := by
        obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp haE
        obtain ⟨n, hn⟩ := Nat.not_even_iff_odd.mp hbE
        exact ⟨m + n + 1, by rw [hm, hn]; ring⟩
      exact exists_nrd_eq_unit_of_plane p hp w (a * b) (mul_ne_zero ha hb) (by rwa [hv])
        (fun X Y => (⟨X, 0, 0, Y⟩ : QuatAlg ℚ_[p] a b))
        (fun X Y => by
          have h1 : nrd (⟨X, 0, 0, Y⟩ : QuatAlg ℚ_[p] a b) =
              X ^ 2 + (a : ℚ_[p]) * (b : ℚ_[p]) * Y ^ 2 := by
            simp [nrd]
          rw [h1]
          push_cast
          ring)

end Langlandscape.Local
