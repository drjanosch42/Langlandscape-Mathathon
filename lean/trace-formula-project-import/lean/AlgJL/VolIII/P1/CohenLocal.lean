import AlgJL.VolIII.P1.Normalization
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.NatDivisors

/-!
# Cohen's `μ` locally, and Eichler's sum form of D2 (Q1 U3)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §4 (items 18–23 of `docs/sprints/Q1-plan.md` §1.2) plus the B-only
item 6 (the divisor structure of `𝓕(t, n)`), which the plan lists under `Arith`; it lives here because it is stated
with the conductor test of `Normalization` (item 13) and is used only by item 23.

B-only items (`tf_aux`, plan §1.2 candidates 6, 18, 22): `III.ef.lem:order-index-set-divisors`,
`III.ef.lem:cohen-mu-averaged`, `III.ef.lem:conductor-relation-iterate`. A carries their content as prose
(A1 notes item 1).

"Fundamental discriminant" is spelled as in A (item 43): `Δ₀ ≡ 0, 1 (mod 4)` and no prime divides the conductor of `Δ₀`.
Item 23's weight hypothesis is an inline `∀`-binder about the variable function `H` (plan Q1-B, trap 1); it mentions
only the `ℤ`-valued `kroneckerPrime`. Owner: L1 (Q1).
-/

namespace GL2TF.Explicit

/-- Proof helper: a discriminant times a square is a discriminant. -/
private theorem disc_mul_sq {Δ : ℤ} (hd : Δ % 4 = 0 ∨ Δ % 4 = 1) (m : ℤ) :
    (Δ * m ^ 2) % 4 = 0 ∨ (Δ * m ^ 2) % 4 = 1 := by
  have h4 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rw [pow_two, Int.mul_emod]
    rcases this with h | h | h | h <;> rw [h] <;> norm_num
  rw [Int.mul_emod]
  rcases hd with h | h <;> rcases h4 with h' | h' <;> rw [h, h'] <;> norm_num

/-- Proof helper: membership in `𝓕(t, n)` without the search bound (`t² − 4n ≠ 0`). -/
private theorem mem_orderIndexSet_iff {t : ℤ} {n f : ℕ} (hΔ : t ^ 2 - 4 * (n : ℤ) ≠ 0) :
    f ∈ orderIndexSet t n ↔ 1 ≤ f ∧ (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n ∧
      ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 0 ∨ (t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 1) := by
  unfold orderIndexSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    have h2' : f ^ 2 ∣ (t ^ 2 - 4 * (n : ℤ)).natAbs := by
      rw [← Int.ofNat_dvd_left]
      exact_mod_cast h2
    exact le_trans (Nat.le_self_pow two_ne_zero f) (Nat.le_of_dvd (Int.natAbs_pos.mpr hΔ) h2')

/-- Proof helper: the index condition passes to divisors. -/
private theorem idx_of_dvd {Δ : ℤ} {f d : ℕ} (hf0 : f ≠ 0) (hf : (f : ℤ) ^ 2 ∣ Δ)
    (hfd : Δ / (f : ℤ) ^ 2 % 4 = 0 ∨ Δ / (f : ℤ) ^ 2 % 4 = 1) (hdf : d ∣ f) :
    (d : ℤ) ^ 2 ∣ Δ ∧ (Δ / (d : ℤ) ^ 2 % 4 = 0 ∨ Δ / (d : ℤ) ^ 2 % 4 = 1) := by
  obtain ⟨e, rfl⟩ := hdf
  obtain ⟨D, rfl⟩ := hf
  have hd0 : d ≠ 0 := by rintro rfl; simp at hf0
  have he0 : e ≠ 0 := by rintro rfl; simp at hf0
  have hf2 : ((d * e : ℕ) : ℤ) ^ 2 ≠ 0 := by positivity
  have hd2 : (d : ℤ) ^ 2 ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ hf2] at hfd
  have heq : ((d * e : ℕ) : ℤ) ^ 2 * D = (d : ℤ) ^ 2 * (D * (e : ℤ) ^ 2) := by push_cast; ring
  rw [heq, Int.mul_ediv_cancel_left _ hd2]
  exact ⟨Dvd.intro _ rfl, disc_mul_sq hfd _⟩

/-- Proof helper: the index condition is preserved under multiplication by an odd `m`. -/
private theorem idx_mul_odd {Δ : ℤ} {f m : ℕ} (hf0 : f ≠ 0)
    (hfd : Δ / (f : ℤ) ^ 2 % 4 = 0 ∨ Δ / (f : ℤ) ^ 2 % 4 = 1) (hm : ¬ 2 ∣ m)
    (hfm : ((f * m : ℕ) : ℤ) ^ 2 ∣ Δ) :
    Δ / ((f * m : ℕ) : ℤ) ^ 2 % 4 = 0 ∨ Δ / ((f * m : ℕ) : ℤ) ^ 2 % 4 = 1 := by
  obtain ⟨E, rfl⟩ := hfm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hfm2 : ((f * m : ℕ) : ℤ) ^ 2 ≠ 0 := by positivity
  have hf2 : (f : ℤ) ^ 2 ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ hfm2]
  have heq : ((f * m : ℕ) : ℤ) ^ 2 * E = (f : ℤ) ^ 2 * ((m : ℤ) ^ 2 * E) := by push_cast; ring
  rw [heq, Int.mul_ediv_cancel_left _ hf2] at hfd
  have hm4 : (m : ℤ) ^ 2 % 4 = 1 := by
    have : (m : ℤ) % 4 = 1 ∨ (m : ℤ) % 4 = 3 := by omega
    rw [pow_two, Int.mul_emod]
    rcases this with h | h <;> rw [h] <;> norm_num
  rw [Int.mul_emod, hm4, one_mul, Int.emod_emod_of_dvd _ (dvd_refl _)] at hfd
  exact hfd

/-- Proof helper: the index condition is closed under `lcm`. -/
private theorem idx_lcm {Δ : ℤ} {f g : ℕ} (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : (f : ℤ) ^ 2 ∣ Δ)
    (hfd : Δ / (f : ℤ) ^ 2 % 4 = 0 ∨ Δ / (f : ℤ) ^ 2 % 4 = 1) (hg : (g : ℤ) ^ 2 ∣ Δ)
    (hgd : Δ / (g : ℤ) ^ 2 % 4 = 0 ∨ Δ / (g : ℤ) ^ 2 % 4 = 1) :
    ((Nat.lcm f g : ℕ) : ℤ) ^ 2 ∣ Δ ∧
      (Δ / ((Nat.lcm f g : ℕ) : ℤ) ^ 2 % 4 = 0 ∨ Δ / ((Nat.lcm f g : ℕ) : ℤ) ^ 2 % 4 = 1) := by
  have hl : ((Nat.lcm f g : ℕ) : ℤ) ^ 2 ∣ Δ := by
    have hf' : f ^ 2 ∣ Δ.natAbs := by rw [← Int.ofNat_dvd_left]; exact_mod_cast hf
    have hg' : g ^ 2 ∣ Δ.natAbs := by rw [← Int.ofNat_dvd_left]; exact_mod_cast hg
    have := Nat.lcm_dvd hf' hg'
    rw [Nat.pow_lcm_pow, ← Int.ofNat_dvd_left] at this
    exact_mod_cast this
  refine ⟨hl, ?_⟩
  have hgpos : 0 < Nat.gcd f g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hf0)
  have hcop := Nat.coprime_div_gcd_div_gcd hgpos
  have hlf : Nat.lcm f g = f * (g / Nat.gcd f g) := by
    rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right f g)]
  have hlg : Nat.lcm f g = g * (f / Nat.gcd f g) := by
    rw [Nat.lcm, mul_comm f g, Nat.mul_div_assoc _ (Nat.gcd_dvd_left f g)]
  by_cases h2 : 2 ∣ g / Nat.gcd f g
  · have h2' : ¬ 2 ∣ f / Nat.gcd f g := by
      intro h
      have := Nat.dvd_gcd h h2
      rw [hcop] at this
      omega
    rw [hlg] at hl ⊢
    exact idx_mul_odd hg0 hgd h2' hl
  · rw [hlf] at hl ⊢
    exact idx_mul_odd hf0 hfd h2 hl

/-- Proof helper: the conductor test at `Δ_f` is the index condition at `p f`. -/
private theorem dividesConductor_iff_idx {Δ : ℤ} {f p : ℕ} (hf0 : f ≠ 0) (hf : (f : ℤ) ^ 2 ∣ Δ) :
    dividesConductor p (Δ / (f : ℤ) ^ 2) = true ↔
      ((p * f : ℕ) : ℤ) ^ 2 ∣ Δ ∧ (Δ / ((p * f : ℕ) : ℤ) ^ 2 % 4 = 0 ∨ Δ / ((p * f : ℕ) : ℤ) ^ 2 % 4 = 1) := by
  obtain ⟨X, rfl⟩ := hf
  have hf2 : (f : ℤ) ^ 2 ≠ 0 := by positivity
  have hf2p : 0 < (f : ℤ) ^ 2 := by positivity
  have hpf : ((p * f : ℕ) : ℤ) ^ 2 = (f : ℤ) ^ 2 * (p : ℤ) ^ 2 := by push_cast; ring
  rw [Int.mul_ediv_cancel_left _ hf2, hpf, Int.mul_ediv_mul_of_pos _ _ hf2p, mul_dvd_mul_iff_left hf2]
  simp only [dividesConductor, decide_eq_true_eq]

/-- B-only (plan item 6): for `t² < 4n` there is `c ≥ 1` with `𝓕(t, n) = divisors(c)` such that
`Δ₀ = (t² − 4n)/c²` is a negative fundamental discriminant, and for `f ∣ c` and a prime `p`,
`p ∣ cond Δ_f ⟺ p ∣ c/f`, where `Δ_f = (t² − 4n)/f²`. -/
@[tf_aux "III.ef.lem:order-index-set-divisors"]
theorem orderIndexSet_eq_divisors {t : ℤ} {n : ℕ} (htn : t ^ 2 < 4 * (n : ℤ)) :
    ∃ c : ℕ, 1 ≤ c ∧ orderIndexSet t n = c.divisors ∧
      (t ^ 2 - 4 * n) / (c : ℤ) ^ 2 < 0 ∧
      ((t ^ 2 - 4 * n) / (c : ℤ) ^ 2 % 4 = 0 ∨ (t ^ 2 - 4 * n) / (c : ℤ) ^ 2 % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p ((t ^ 2 - 4 * n) / (c : ℤ) ^ 2) = false) ∧
      ∀ f ∈ c.divisors, ∀ p : ℕ, p.Prime →
        (dividesConductor p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) = true ↔ p ∣ c / f) := by
  have hΔ : t ^ 2 - 4 * (n : ℤ) < 0 := by linarith
  have hΔ0 : t ^ 2 - 4 * (n : ℤ) ≠ 0 := hΔ.ne
  have h1 : 1 ∈ orderIndexSet t n := by
    rw [mem_orderIndexSet_iff hΔ0]
    refine ⟨le_refl 1, by simp, ?_⟩
    have := disc_mul_sq (Δ := 1) (by norm_num) t
    simp only [Nat.cast_one, one_pow, Int.ediv_one, one_mul] at this ⊢
    omega
  set S := orderIndexSet t n with hSdef
  have hmem : ∀ f, f ∈ S ↔ 1 ≤ f ∧ (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n ∧
      ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 0 ∨ (t ^ 2 - 4 * n) / (f : ℤ) ^ 2 % 4 = 1) :=
    fun f => mem_orderIndexSet_iff hΔ0
  set c := S.max' ⟨1, h1⟩ with hcdef
  have hc : c ∈ S := Finset.max'_mem _ _
  obtain ⟨hc1, hcd, hcdisc⟩ := (hmem c).mp hc
  have hc0 : c ≠ 0 := by omega
  have hdivc : ∀ f ∈ S, f ∣ c := by
    intro f hf
    obtain ⟨hf1, hfd, hfdisc⟩ := (hmem f).mp hf
    have hf0 : f ≠ 0 := by omega
    obtain ⟨hl, hldisc⟩ := idx_lcm hf0 hc0 hfd hfdisc hcd hcdisc
    have hlpos : 0 < Nat.lcm f c := Nat.lcm_pos (Nat.pos_of_ne_zero hf0) (Nat.pos_of_ne_zero hc0)
    have hlS : Nat.lcm f c ∈ S := (hmem _).mpr ⟨hlpos, hl, hldisc⟩
    have hle : Nat.lcm f c ≤ c := Finset.le_max' _ _ hlS
    have hge : c ≤ Nat.lcm f c := Nat.le_of_dvd hlpos (Nat.dvd_lcm_right f c)
    have heq : Nat.lcm f c = c := le_antisymm hle hge
    rw [← heq]
    exact Nat.dvd_lcm_left f c
  have hS : S = c.divisors := by
    ext f
    rw [Nat.mem_divisors]
    constructor
    · intro hf
      exact ⟨hdivc f hf, hc0⟩
    · rintro ⟨hfc, -⟩
      have hf0 : f ≠ 0 := by rintro rfl; simp at hfc; exact hc0 hfc
      obtain ⟨h1', h2'⟩ := idx_of_dvd hc0 hcd hcdisc hfc
      exact (hmem f).mpr ⟨Nat.one_le_iff_ne_zero.mpr hf0, h1', h2'⟩
  have hcond : ∀ f ∈ S, ∀ p : ℕ, p.Prime →
      (dividesConductor p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) = true ↔ p * f ∣ c) := by
    intro f hf p hp
    obtain ⟨hf1, hfd, -⟩ := (hmem f).mp hf
    rw [dividesConductor_iff_idx (by omega) hfd]
    constructor
    · rintro ⟨h1', h2'⟩
      exact hdivc _ ((hmem _).mpr ⟨Nat.mul_pos hp.pos hf1, h1', h2'⟩)
    · intro h
      have : p * f ∈ S := by rw [hS]; exact Nat.mem_divisors.mpr ⟨h, hc0⟩
      exact ((hmem _).mp this).2
  refine ⟨c, hc1, hS, ?_, hcdisc, ?_, ?_⟩
  · obtain ⟨D, hD⟩ := hcd
    have hc2 : ((c : ℕ) : ℤ) ^ 2 ≠ 0 := by positivity
    rw [hD, Int.mul_ediv_cancel_left _ hc2]
    rw [hD] at hΔ
    by_contra h
    have := mul_nonneg (sq_nonneg (c : ℤ)) (not_lt.mp h)
    linarith
  · intro p hp
    rw [Bool.eq_false_iff]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) ((hcond c hc p hp).mp h)
    have := hp.two_le
    nlinarith
  · intro f hf p hp
    rw [← hS] at hf
    rw [hcond f hf p hp, Nat.dvd_div_iff_mul_dvd (hdivc f hf), mul_comm]

/-- Proof helper for item 18: with `g² ∣ t² − 4n` and `g ∣ N`, the solutions of `x² − tx + n ≡ 0 (mod N g)` are
invariant under `x ↦ x + N i`. -/
private theorem roots_shift {N g : ℕ} {t : ℤ} {n : ℕ} (hg : (g : ℤ) ^ 2 ∣ t ^ 2 - 4 * n) (hgN : g ∣ N) (x i : ℤ)
    (hx : ((N * g : ℕ) : ℤ) ∣ x ^ 2 - t * x + n) :
    ((N * g : ℕ) : ℤ) ∣ (x + N * i) ^ 2 - t * (x + N * i) + n := by
  obtain ⟨k, hk⟩ := hgN
  have hkz : (N : ℤ) = g * k := by exact_mod_cast hk
  have h2 : (g : ℤ) ∣ 2 * x - t := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    have hQ : (g : ℤ) ^ 2 ∣ 4 * (x ^ 2 - t * x + n) := by
      refine Dvd.dvd.mul_left (dvd_trans ?_ hx) 4
      rw [Nat.cast_mul, hkz]
      exact ⟨k, by ring⟩
    have : (2 * x - t) ^ 2 = (t ^ 2 - 4 * n) + 4 * (x ^ 2 - t * x + n) := by ring
    rw [this]
    exact dvd_add hg hQ
  obtain ⟨a, ha⟩ := h2
  have : (x + N * i) ^ 2 - t * (x + N * i) + n =
      (x ^ 2 - t * x + n) + ((N * g : ℕ) : ℤ) * (i * (a + k * i)) := by
    push_cast
    linear_combination (↑N * i) * ha + (↑N * i ^ 2) * hkz
  rw [this]
  exact dvd_add hx (dvd_mul_right _ _)

/-- B-only (plan item 18): for `N ≥ 1`, `f ≥ 1` with `f² ∣ t² − 4n` and `N_f = gcd(N, f)`, the number of roots of
`x² − tx + n` in `ℤ/N N_f` is `N_f` times the number of `x ∈ {0, …, N − 1}` with `N N_f ∣ x² − tx + n`. -/
@[tf_aux "III.ef.lem:cohen-mu-averaged"]
theorem card_roots_zmod_eq {N f : ℕ} {t : ℤ} {n : ℕ} (hN : 1 ≤ N) (hf : 1 ≤ f)
    (hft : (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n) :
    Nat.card {x : ZMod (N * Nat.gcd N f) //
        x ^ 2 - (t : ZMod (N * Nat.gcd N f)) * x + (n : ZMod (N * Nat.gcd N f)) = 0} =
      Nat.gcd N f *
        ((Finset.range N).filter fun x : ℕ =>
          ((N * Nat.gcd N f : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card := by
  have hg0 : 0 < Nat.gcd N f := Nat.gcd_pos_of_pos_left _ hN
  have hgN : Nat.gcd N f ∣ N := Nat.gcd_dvd_left N f
  have hgsq : ((Nat.gcd N f : ℕ) : ℤ) ^ 2 ∣ t ^ 2 - 4 * n :=
    dvd_trans (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right N f)) 2) hft
  set g := Nat.gcd N f with hgdef
  set M := N * g with hMdef
  have hM0 : 0 < M := Nat.mul_pos hN hg0
  have : NeZero M := ⟨hM0.ne'⟩
  have hA : Nat.card {x : ZMod M // x ^ 2 - (t : ZMod M) * x + (n : ZMod M) = 0} =
      ((Finset.range M).filter fun x : ℕ => (M : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine Finset.card_nbij' (fun x => x.val) (fun x => (x : ZMod M)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hx
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hx.2
      push_cast at this
      exact this
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
      exact ZMod.val_cast_of_lt hx.1
  have hB : ((Finset.range M).filter fun x : ℕ => (M : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card =
      g * ((Finset.range N).filter fun x : ℕ => (M : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card := by
    rw [← Finset.card_range g, ← Finset.card_product]
    symm
    refine Finset.card_nbij' (fun q => q.2 + N * q.1) (fun x => (x / N, x % N)) ?_ ?_ ?_ ?_
    · rintro ⟨i, r⟩ h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at h ⊢
      refine ⟨?_, ?_⟩
      · calc r + N * i < N + N * i := by omega
          _ = N * (i + 1) := by ring
          _ ≤ N * g := Nat.mul_le_mul_left _ h.1
      · have := roots_shift hgsq hgN (r : ℤ) (i : ℤ) h.2.2
        push_cast
        exact this
    · intro x h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at h ⊢
      refine ⟨Nat.div_lt_of_lt_mul h.1, Nat.mod_lt _ hN, ?_⟩
      have := roots_shift hgsq hgN (x : ℤ) (-((x / N : ℕ) : ℤ)) h.2
      have h' : ((x % N : ℕ) : ℤ) + N * ((x / N : ℕ) : ℤ) = x := by exact_mod_cast Nat.mod_add_div x N
      have hx : (x : ℤ) + N * (-((x / N : ℕ) : ℤ)) = ((x % N : ℕ) : ℤ) := by linarith
      rw [hx] at this
      exact this
    · rintro ⟨i, r⟩ h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at h
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt h.2.1, zero_add]
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.2.1]
    · intro x _
      exact Nat.mod_add_div x N
  rw [hA, hB]

/-- Proof helper for item 19: the root count of `x² − tx + n` in `ZMod M` is multiplicative (CRT). -/
private theorem card_roots_mul_of_eq {M a b : ℕ} (hM : M = a * b) (h : Nat.Coprime a b) (t : ℤ) (n : ℕ) :
    Nat.card {x : ZMod M // x ^ 2 - (t : ZMod M) * x + (n : ZMod M) = 0} =
      Nat.card {x : ZMod a // x ^ 2 - (t : ZMod a) * x + (n : ZMod a) = 0} *
        Nat.card {x : ZMod b // x ^ 2 - (t : ZMod b) * x + (n : ZMod b) = 0} := by
  subst hM
  let e := ZMod.chineseRemainder h
  have e1 : {x : ZMod (a * b) // x ^ 2 - (t : ZMod (a * b)) * x + (n : ZMod (a * b)) = 0} ≃
      {y : ZMod a × ZMod b // y ^ 2 - (t : ZMod a × ZMod b) * y + (n : ZMod a × ZMod b) = 0} :=
    e.toEquiv.subtypeEquiv fun x => by
      have hx : e (x ^ 2 - (t : ZMod (a * b)) * x + (n : ZMod (a * b))) =
          (e x) ^ 2 - (t : ZMod a × ZMod b) * (e x) + (n : ZMod a × ZMod b) := by
        simp [map_sub, map_add, map_mul, map_pow]
      change _ ↔ (e x) ^ 2 - (t : ZMod a × ZMod b) * (e x) + (n : ZMod a × ZMod b) = 0
      rw [← hx, map_eq_zero_iff _ e.injective]
  have e2 : {y : ZMod a × ZMod b // y ^ 2 - (t : ZMod a × ZMod b) * y + (n : ZMod a × ZMod b) = 0} ≃
      {x : ZMod a // x ^ 2 - (t : ZMod a) * x + (n : ZMod a) = 0} ×
        {x : ZMod b // x ^ 2 - (t : ZMod b) * x + (n : ZMod b) = 0} :=
    (Equiv.subtypeEquivRight fun y => by simp [Prod.ext_iff]).trans Equiv.subtypeProdEquivProd
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod]

/-- Cohen's `μ` is multiplicative in the level: `μ_{N₁N₂}(t, f, n) = μ_{N₁}(t, f, n) μ_{N₂}(t, f, n)` for
`f ∈ 𝓕(t, n)` and coprime `N₁, N₂ ≥ 1`. -/
@[tf_id "III.ef.thm:cohen-mu-multiplicative"]
theorem cohenMu_mul {t : ℤ} {n f : ℕ} (hf : f ∈ orderIndexSet t n) {N₁ N₂ : ℕ} (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hcop : Nat.Coprime N₁ N₂) :
    cohenMu (N₁ * N₂) t f n = cohenMu N₁ t f n * cohenMu N₂ t f n := by
  have hf' := Finset.mem_filter.mp hf
  have hf0 : 1 ≤ f := (Finset.mem_Icc.mp hf'.1).1
  have hft : (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n := hf'.2.1
  have h18 := fun (N : ℕ) (hN : 1 ≤ N) => card_roots_zmod_eq (t := t) (n := n) hN hf0 hft
  have hg1 : Nat.gcd N₁ f ∣ N₁ := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd N₂ f ∣ N₂ := Nat.gcd_dvd_left _ _
  have hg : Nat.gcd (N₁ * N₂) f = Nat.gcd N₁ f * Nat.gcd N₂ f := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul f hcop, Nat.gcd_comm f, Nat.gcd_comm f]
  have hcop' : Nat.Coprime (N₁ * Nat.gcd N₁ f) (N₂ * Nat.gcd N₂ f) :=
    Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_right.mpr ⟨hcop, hcop.coprime_dvd_right hg2⟩,
      Nat.coprime_mul_iff_right.mpr ⟨hcop.coprime_dvd_left hg1, (hcop.coprime_dvd_left hg1).coprime_dvd_right hg2⟩⟩
  have hR := card_roots_mul_of_eq (M := N₁ * N₂ * Nat.gcd (N₁ * N₂) f) (by rw [hg]; ring) hcop' t n
  have hg1p : 0 < Nat.gcd N₁ f := Nat.gcd_pos_of_pos_left _ hN₁
  have hg2p : 0 < Nat.gcd N₂ f := Nat.gcd_pos_of_pos_left _ hN₂
  have hcount : ((Finset.range (N₁ * N₂)).filter fun x : ℕ =>
        ((N₁ * N₂ * Nat.gcd (N₁ * N₂) f : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card =
      ((Finset.range N₁).filter fun x : ℕ =>
        ((N₁ * Nat.gcd N₁ f : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card *
      ((Finset.range N₂).filter fun x : ℕ =>
        ((N₂ * Nat.gcd N₂ f : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg1p hg2p) ?_
    rw [← hg, ← h18 (N₁ * N₂) (Nat.mul_le_mul hN₁ hN₂), hR, h18 N₁ hN₁, h18 N₂ hN₂, hg]
    ring
  have hpsi := dedekindPsi_nat_mul_prime.2.1 N₁ N₂ hcop
  have hdiv : N₁ * N₂ / Nat.gcd (N₁ * N₂) f = (N₁ / Nat.gcd N₁ f) * (N₂ / Nat.gcd N₂ f) := by
    rw [hg, Nat.div_mul_div_comm hg1 hg2]
  have hcopd : Nat.Coprime (N₁ / Nat.gcd N₁ f) (N₂ / Nat.gcd N₂ f) :=
    Nat.Coprime.coprime_div_left (Nat.Coprime.coprime_div_right hcop hg2) hg1
  have h0 : N₁ * N₂ ≠ 0 := by positivity
  have h1 : N₁ ≠ 0 := by omega
  have h2 : N₂ ≠ 0 := by omega
  simp only [cohenMu, h0, h1, h2, ↓reduceIte]
  rw [hcount, hpsi, hdiv, dedekindPsi_nat_mul_prime.2.1 _ _ hcopd]
  push_cast
  ring

/-- Proof helper (`p = 2` cases): `t² mod 16` in terms of `t mod 16`. -/
private theorem sq_mod_sixteen (t : ℤ) :
    (t % 16 = 0 ∧ t ^ 2 % 16 = 0) ∨
      (t % 16 = 1 ∧ t ^ 2 % 16 = 1) ∨
      (t % 16 = 2 ∧ t ^ 2 % 16 = 4) ∨
      (t % 16 = 3 ∧ t ^ 2 % 16 = 9) ∨
      (t % 16 = 4 ∧ t ^ 2 % 16 = 0) ∨
      (t % 16 = 5 ∧ t ^ 2 % 16 = 9) ∨
      (t % 16 = 6 ∧ t ^ 2 % 16 = 4) ∨
      (t % 16 = 7 ∧ t ^ 2 % 16 = 1) ∨
      (t % 16 = 8 ∧ t ^ 2 % 16 = 0) ∨
      (t % 16 = 9 ∧ t ^ 2 % 16 = 1) ∨
      (t % 16 = 10 ∧ t ^ 2 % 16 = 4) ∨
      (t % 16 = 11 ∧ t ^ 2 % 16 = 9) ∨
      (t % 16 = 12 ∧ t ^ 2 % 16 = 0) ∨
      (t % 16 = 13 ∧ t ^ 2 % 16 = 9) ∨
      (t % 16 = 14 ∧ t ^ 2 % 16 = 4) ∨
      (t % 16 = 15 ∧ t ^ 2 % 16 = 1) := by
  have h : t % 16 = 0 ∨ t % 16 = 1 ∨ t % 16 = 2 ∨ t % 16 = 3 ∨ t % 16 = 4 ∨ t % 16 = 5 ∨ t % 16 = 6 ∨ t % 16 = 7 ∨ t % 16 = 8 ∨ t % 16 = 9 ∨ t % 16 = 10 ∨ t % 16 = 11 ∨ t % 16 = 12 ∨ t % 16 = 13 ∨ t % 16 = 14 ∨ t % 16 = 15 := by omega
  have hsq : t ^ 2 % 16 = (t % 16) * (t % 16) % 16 := by rw [pow_two, Int.mul_emod]
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, Int.reduceMul, Int.reduceMod] at hsq <;> simp only [h, hsq] <;> decide

/-- Proof helper: the root count over `{0, …, p − 1}` modulo an odd prime `p` is `1 + (Δ/p)`. -/
private theorem count_roots_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : ℤ) (n : ℕ) :
    ((((Finset.range p).filter fun x : ℕ => (p : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card : ℕ) : ℤ) =
      1 + jacobiSym (t ^ 2 - 4 * n) p := by
  have := Fact.mk hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [← jacobiSym.legendreSym.to_jacobiSym, add_comm, ← legendreSym.card_sqrts p hp2]
  congr 1
  refine Finset.card_nbij' (fun x => 2 * (x : ZMod p) - t) (fun y => ((y + t) / 2).val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_ofPred_eq]
    have hq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hx.2
    push_cast at hq ⊢
    linear_combination 4 * hq
  · intro y hy
    simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_ofPred_eq] at hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hy ⊢
    rw [ZMod.natCast_zmod_val]
    set z := (y + (t : ZMod p)) / 2
    have h2z : 2 * z = y + t := mul_div_cancel₀ _ h2
    have h4q : (4 : ZMod p) * (z ^ 2 - t * z + n) = 0 := by
      linear_combination (2 * z + y - t) * h2z + hy
    exact (mul_eq_zero.mp h4q).resolve_left h4
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    simp only [sub_add_cancel]
    rw [mul_div_cancel_left₀ _ h2, ZMod.val_cast_of_lt hx.1]
  · intro y _
    simp only
    rw [ZMod.natCast_zmod_val, mul_div_cancel₀ _ h2, add_sub_cancel_right]

/-- Proof helper: for an odd prime `p` with `p² ∣ t² − 4n`, exactly one `x ∈ {0, …, p − 1}` has `p² ∣ x² − tx + n`. -/
private theorem count_roots_odd_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : ℤ) (n : ℕ)
    (hΔ : (p : ℤ) ^ 2 ∣ t ^ 2 - 4 * n) :
    ((Finset.range p).filter fun x : ℕ => ((p * p : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card = 1 := by
  have := Fact.mk hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hgcd : Int.gcd ((p : ℤ) ^ 2) 4 = 1 := by
    have : Nat.Coprime (p ^ 2) (2 ^ 2) :=
      Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    rw [show (4 : ℤ) = ((2 ^ 2 : ℕ) : ℤ) by norm_num, show (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring,
      Int.gcd_natCast_natCast]
    exact this
  have key : ∀ x : ℤ, (p : ℤ) ^ 2 ∣ x ^ 2 - t * x + n ↔ (p : ℤ) ∣ 2 * x - t := by
    intro x
    have h4 : (2 * x - t) ^ 2 = 4 * (x ^ 2 - t * x + n) + (t ^ 2 - 4 * n) := by ring
    constructor
    · intro h
      rw [← Int.pow_dvd_pow_iff two_ne_zero, h4]
      exact dvd_add (Dvd.dvd.mul_left h 4) hΔ
    · intro h
      have h' : (p : ℤ) ^ 2 ∣ (2 * x - t) ^ 2 := pow_dvd_pow_of_dvd h 2
      rw [h4] at h'
      have h'' : (p : ℤ) ^ 2 ∣ 4 * (x ^ 2 - t * x + n) := by
        have := dvd_sub h' hΔ
        simpa using this
      exact Int.dvd_of_dvd_mul_right_of_gcd_one h'' hgcd
  rw [Finset.card_eq_one]
  refine ⟨((t : ZMod p) / 2).val, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  rw [show ((p * p : ℕ) : ℤ) = (p : ℤ) ^ 2 by push_cast; ring, key, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor
  · rintro ⟨hx, h⟩
    have : (x : ZMod p) = t / 2 := by
      rw [eq_div_iff h2]
      linear_combination h
    rw [← this, ZMod.val_cast_of_lt hx]
  · rintro rfl
    refine ⟨ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val, mul_div_cancel₀ _ h2, sub_self]

/-- Cohen's `μ` at a prime: for `f ∈ 𝓕(t, n)`, `μ_p(t, f, n) = 1 + χ_{t² − 4n}(p)` if `p ∤ f`, and `p + 1` if `p ∣ f`. -/
@[tf_id "III.ef.prop:cohen-mu-local-prime"]
theorem cohenMu_prime {t : ℤ} {n f : ℕ} (hf : f ∈ orderIndexSet t n) {p : ℕ} (hp : p.Prime) :
    (¬ p ∣ f → cohenMu p t f n = 1 + (kroneckerPrime (t ^ 2 - 4 * n) p : ℚ)) ∧
    (p ∣ f → cohenMu p t f n = (p : ℚ) + 1) := by
  have hf' := Finset.mem_filter.mp hf
  have hf0 : 1 ≤ f := (Finset.mem_Icc.mp hf'.1).1
  have hft : (f : ℤ) ^ 2 ∣ t ^ 2 - 4 * n := hf'.2.1
  have hdisc := hf'.2.2
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpsi_p : dedekindPsi p = p + 1 := dedekindPsi_nat_mul_prime.2.2 p hp
  have h16 := sq_mod_sixteen t
  constructor
  · intro hpf
    have hg : Nat.gcd p f = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpf
    simp only [cohenMu, hp0, ↓reduceIte, hg, Nat.div_one, Nat.mul_one]
    rw [div_self (by rw [hpsi_p]; positivity), one_mul]
    by_cases hp2 : p = 2
    · subst hp2
      have hc : ((((Finset.range 2).filter fun x : ℕ => ((2 : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card : ℕ) : ℤ) =
          1 + kroneckerPrime (t ^ 2 - 4 * n) 2 := by
        rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp only [kroneckerPrime, ↓reduceIte]
        push_cast
        norm_num
        generalize t ^ 2 = T at *
        split_ifs <;> omega
      exact_mod_cast hc
    · have hc := count_roots_odd_prime hp hp2 t n
      simp only [kroneckerPrime, hp2, ↓reduceIte]
      exact_mod_cast hc
  · intro hpf
    have hg : Nat.gcd p f = p := Nat.gcd_eq_left hpf
    simp only [cohenMu, hp0, ↓reduceIte, hg, Nat.div_self hp.pos]
    have hpsi1 : dedekindPsi 1 = 1 := by simp [dedekindPsi]
    rw [hpsi_p, hpsi1, div_one]
    suffices hc : ((Finset.range p).filter fun x : ℕ => ((p * p : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card = 1 by
      rw [hc]
      push_cast
      ring
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨f', rfl⟩ := hpf
      obtain ⟨D, hD⟩ := hft
      have hne : ((2 * f' : ℕ) : ℤ) ^ 2 ≠ 0 := by
        have : (2 * f' : ℕ) ≠ 0 := by omega
        positivity
      have hD' : (t ^ 2 - 4 * n) / ((2 * f' : ℕ) : ℤ) ^ 2 = D := by
        rw [hD, Int.mul_ediv_cancel_left _ hne]
      rw [hD'] at hdisc
      have hE := disc_mul_sq hdisc (f' : ℤ)
      have h4 : t ^ 2 - 4 * n = 4 * (D * (f' : ℤ) ^ 2) := by
        rw [hD]
        push_cast
        ring
      have hc : ((((Finset.range 2).filter fun x : ℕ =>
          ((2 * 2 : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card : ℕ) : ℤ) = 1 := by
        rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        push_cast
        norm_num
        generalize D * (f' : ℤ) ^ 2 = E at *
        generalize t ^ 2 = T at *
        split_ifs <;> omega
      exact_mod_cast hc
    · exact count_roots_odd_prime_sq hp hp2 t n
        (dvd_trans (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr hpf) 2) hft)

/-- The local identity behind D2 at a prime `p`: with `g(0) = 1`, `g(j) = p^{j−1}(p − χ)` (`j ≥ 1`),
`X(0) = 1 + χ` if `ν = 0` and `1` if `ν ≥ 1`, `X(a) = p + 1` (`a ≥ 1`), `Y(0) = 1 + χ`, `Y(j) = 2` (`j ≥ 1`):
`∑_{a=0}^{ν} g(ν − a) X(a) = ∑_{a=0}^{ν} g(ν − a) Y(ν − a)`. The functions are given by their defining equations. -/
@[tf_id "III.ef.lem:d2-local-identity"]
theorem d2_local_identity {p : ℕ} (hp : p.Prime) (χ : ℤ) (ν : ℕ) (g X Y : ℕ → ℤ)
    (hg₀ : g 0 = 1) (hg : ∀ j, 1 ≤ j → g j = (p : ℤ) ^ (j - 1) * ((p : ℤ) - χ))
    (hX₀ : X 0 = if ν = 0 then 1 + χ else 1) (hX : ∀ a, 1 ≤ a → X a = (p : ℤ) + 1)
    (hY₀ : Y 0 = 1 + χ) (hY : ∀ j, 1 ≤ j → Y j = 2) :
    ∑ a ∈ Finset.range (ν + 1), g (ν - a) * X a = ∑ a ∈ Finset.range (ν + 1), g (ν - a) * Y (ν - a) := by
  have hgs : ∀ j, g (j + 1) = (p : ℤ) ^ j * ((p : ℤ) - χ) := fun j => by simpa using hg (j + 1) (by omega)
  rcases ν with _ | m
  · simp [hg₀, hX₀, hY₀]
  · have hT : ∀ m : ℕ, ((p : ℤ) - 1) * ∑ j ∈ Finset.range (m + 1), g j = g (m + 1) - 1 + χ := by
      intro m
      induction m with
      | zero => simp [hg₀, hgs]; ring
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih, hgs, hgs, pow_succ]
        ring
    have hr : ∑ i ∈ Finset.range (m + 1), g (m - i) = ∑ i ∈ Finset.range (m + 1), g i := by
      simpa using Finset.sum_range_reflect g (m + 1)
    have hr2 : ∑ a ∈ Finset.range (m + 1 + 1), g (m + 1 - a) * Y (m + 1 - a) =
        ∑ j ∈ Finset.range (m + 1 + 1), g j * Y j := by
      simpa using Finset.sum_range_reflect (fun j => g j * Y j) (m + 1 + 1)
    have hL : ∑ a ∈ Finset.range (m + 1 + 1), g (m + 1 - a) * X a =
        g (m + 1) + ((p : ℤ) + 1) * ∑ j ∈ Finset.range (m + 1), g j := by
      rw [Finset.sum_range_succ', ← hr, Finset.mul_sum]
      have : ∀ i ∈ Finset.range (m + 1), g (m + 1 - (i + 1)) * X (i + 1) = ((p : ℤ) + 1) * g (m - i) := by
        intro i _
        rw [hX (i + 1) (by omega), show m + 1 - (i + 1) = m - i by omega, mul_comm]
      rw [Finset.sum_congr rfl this, hX₀]
      simp only [Nat.add_one_ne_zero, ite_false, Nat.sub_zero, mul_one]
      ring
    have hR : ∑ j ∈ Finset.range (m + 1 + 1), g j * Y j =
        (1 + χ) + 2 * (∑ j ∈ Finset.range (m + 1), g j - 1 + g (m + 1)) := by
      rw [Finset.sum_range_succ']
      have : ∀ i ∈ Finset.range (m + 1), g (i + 1) * Y (i + 1) = 2 * g (i + 1) := by
        intro i _
        rw [hY (i + 1) (by omega), mul_comm]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hg₀, hY₀]
      have hs : ∑ i ∈ Finset.range (m + 1), g (i + 1) = ∑ j ∈ Finset.range (m + 1), g j - 1 + g (m + 1) := by
        have h1 := Finset.sum_range_succ' g (m + 1)
        have h2 := Finset.sum_range_succ g (m + 1)
        rw [hg₀] at h1
        linarith
      rw [hs]
      ring
    rw [hL, hr2, hR]
    linarith [hT m]

/-- Proof helper: `χ_{Δ m²}(p) = 0` if `p ∣ m`. -/
private theorem kroneckerPrime_mul_sq_of_dvd (Δ : ℤ) {p m : ℕ} (hp : p.Prime) (h : p ∣ m) :
    kroneckerPrime (Δ * (m : ℤ) ^ 2) p = 0 := by
  have hdvd : (p : ℤ) ∣ Δ * (m : ℤ) ^ 2 :=
    Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr h) two_ne_zero) Δ
  by_cases hp2 : p = 2
  · subst hp2
    have h0 : Δ * (m : ℤ) ^ 2 % 2 = 0 := by exact_mod_cast Int.emod_eq_zero_of_dvd hdvd
    simp [kroneckerPrime, h0]
  · simp only [kroneckerPrime, hp2, ↓reduceIte]
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
    have : jacobiSym (m : ℤ) p = 0 := by
      rw [jacobiSym.eq_zero_iff]
      refine ⟨hp.ne_zero, ?_⟩
      rw [Int.gcd_natCast_natCast, Nat.gcd_eq_right h]
      exact hp.one_lt.ne'
    rw [this]
    ring

/-- Proof helper: `χ_{Δ m²}(p) = χ_Δ(p)` if `p ∤ m`. -/
private theorem kroneckerPrime_mul_sq_of_not_dvd (Δ : ℤ) {p m : ℕ} (hp : p.Prime) (h : ¬ p ∣ m) :
    kroneckerPrime (Δ * (m : ℤ) ^ 2) p = kroneckerPrime Δ p := by
  by_cases hp2 : p = 2
  · subst hp2
    have hm : (m : ℤ) % 2 = 1 := by omega
    have hm8 : (m : ℤ) ^ 2 % 8 = 1 := by
      have : (m : ℤ) % 8 = 1 ∨ (m : ℤ) % 8 = 3 ∨ (m : ℤ) % 8 = 5 ∨ (m : ℤ) % 8 = 7 := by omega
      rw [pow_two, Int.mul_emod]
      rcases this with h | h | h | h <;> rw [h] <;> norm_num
    have h8 : (Δ * (m : ℤ) ^ 2) % 8 = Δ % 8 := by
      rw [Int.mul_emod, hm8, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
    have h2 : (Δ * (m : ℤ) ^ 2) % 2 = Δ % 2 := by omega
    simp only [kroneckerPrime, ↓reduceIte]
    rw [h2, h8]
  · simp only [kroneckerPrime, hp2, ↓reduceIte]
    rw [jacobiSym.mul_left, jacobiSym.sq_one', mul_one]
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))

/-- Proof helper for item 22: the product `G(m) = ∏_{p ∣ m} p^{v_p(m) − 1}(p − χ(p))` under `m ↦ p m`. -/
private theorem condProd_prime_mul (Δ₀ : ℤ) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    ∏ q ∈ (p * m).primeFactors,
        (q : ℚ) ^ ((p * m).factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) =
      (∏ q ∈ m.primeFactors,
        (q : ℚ) ^ (m.factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ))) *
        ((p : ℚ) - (kroneckerPrime (Δ₀ * (m : ℤ) ^ 2) p : ℚ)) := by
  have hpf : (p * m).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors, Finset.insert_eq]
  have hfac : ∀ q, (p * m).factorization q = (if p = q then 1 else 0) + m.factorization q := by
    intro q
    rw [Nat.factorization_mul hp.ne_zero hm, hp.factorization, Finsupp.add_apply, Finsupp.single_apply]
  have hrest : ∀ q ∈ m.primeFactors, q ≠ p →
      (q : ℚ) ^ ((p * m).factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) =
        (q : ℚ) ^ (m.factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) := by
    intro q _ hq
    rw [hfac]
    simp [Ne.symm hq]
  have hself : (p * m).factorization p = 1 + m.factorization p := by
    rw [hfac]
    simp
  by_cases hd : p ∣ m
  · have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩
    rw [hpf, Finset.insert_eq_of_mem hpm, ← Finset.mul_prod_erase _ _ hpm, ← Finset.mul_prod_erase _ _ hpm,
      kroneckerPrime_mul_sq_of_dvd Δ₀ hp hd,
      Finset.prod_congr rfl fun q hq => hrest q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq),
      hself]
    have hv : 1 ≤ m.factorization p := hp.factorization_pos_of_dvd hm hd
    rw [show 1 + m.factorization p - 1 = (m.factorization p - 1) + 1 by omega, pow_succ]
    push_cast
    ring
  · have hpm : p ∉ m.primeFactors := fun h => hd (Nat.dvd_of_mem_primeFactors h)
    rw [hpf, Finset.prod_insert hpm, kroneckerPrime_mul_sq_of_not_dvd Δ₀ hp hd,
      Finset.prod_congr rfl fun q hq => hrest q hq (fun h => hpm (h ▸ hq)),
      hself, Nat.factorization_eq_zero_of_not_dvd hd]
    simp only [add_zero, Nat.sub_self, pow_zero, one_mul]
    ring

/-- B-only (plan item 22): if `H : ℤ → ℚ` satisfies the conductor relation `H(p²Δ) = (p − χ_Δ(p)) H(Δ)` for all
discriminants `Δ < 0` and primes `p`, then for a fundamental discriminant `Δ₀ < 0` and `m ≥ 1`,
`H(Δ₀ m²) = H(Δ₀) ∏_{p ∣ m} p^{v_p(m) − 1} (p − χ_{Δ₀}(p))`. -/
@[tf_aux "III.ef.lem:conductor-relation-iterate"]
theorem conductor_relation_iterate (H : ℤ → ℚ)
    (hH : ∀ (Δ : ℤ) (p : ℕ), Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) → p.Prime →
      H ((p : ℤ) ^ 2 * Δ) = ((p : ℚ) - (kroneckerPrime Δ p : ℚ)) * H Δ)
    {Δ₀ : ℤ} (hneg : Δ₀ < 0) (hdisc : Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1)
    (hfund : ∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) {m : ℕ} (hm : 1 ≤ m) :
    H (Δ₀ * (m : ℤ) ^ 2) =
      H Δ₀ * ∏ p ∈ m.primeFactors, (p : ℚ) ^ (m.factorization p - 1) * ((p : ℚ) - (kroneckerPrime Δ₀ p : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · set p := m.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime (by omega)
      obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
      have hm'0 : m' ≠ 0 := by rintro rfl; omega
      have hlt : m' < m := by
        rw [hm']
        exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hp.one_lt
      have ih' := ih m' hlt (Nat.one_le_iff_ne_zero.mpr hm'0)
      have hneg' : Δ₀ * (m' : ℤ) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos hneg (by positivity)
      have hrel := hH (Δ₀ * (m' : ℤ) ^ 2) p hneg' (disc_mul_sq hdisc _) hp
      rw [hm', condProd_prime_mul Δ₀ hp hm'0]
      have : Δ₀ * ((p * m' : ℕ) : ℤ) ^ 2 = (p : ℤ) ^ 2 * (Δ₀ * (m' : ℤ) ^ 2) := by push_cast; ring
      rw [this, hrel, ih']
      ring
    · have : m = 1 := by omega
      subst this
      simp

/-- Proof helper for item 23: a sum over the divisors of a coprime product. -/
private theorem sum_divisors_coprime_mul {u w : ℕ} (h : Nat.Coprime u w) (F : ℕ → ℚ) :
    ∑ f ∈ (u * w).divisors, F f = ∑ a ∈ u.divisors, ∑ b ∈ w.divisors, F (a * b) := by
  rw [h.divisors_mul, Finset.sum_map]
  have := Finset.sum_attach (u.divisors ×ˢ w.divisors) (fun x => F (x.1 * x.2))
  exact this.trans (Finset.sum_product _ _ (fun x : ℕ × ℕ => F (x.1 * x.2)))

/-- Proof helper for item 23: a sum over the divisors of `c` of a product of local factors (one per prime, depending
on the exponent) is the product of the local sums. -/
private theorem sum_divisors_prod_local (φ : ℕ → ℕ → ℚ) (P : Finset ℕ) :
    (∀ p ∈ P, p.Prime) → ∀ c : ℕ, c ≠ 0 → c.primeFactors ⊆ P →
      ∑ f ∈ c.divisors, ∏ p ∈ P, φ p (f.factorization p) =
        ∏ p ∈ P, ∑ a ∈ Finset.range (c.factorization p + 1), φ p a := by
  refine Finset.induction_on P ?_ ?_
  · intro _ c hc hsub
    have h1 : c = 1 := by
      have := Finset.subset_empty.mp hsub
      rw [Nat.primeFactors_eq_empty] at this
      omega
    subst h1
    simp
  · intro q P' hq ih hP c hc hsub
    have hqp := hP q (Finset.mem_insert_self _ _)
    have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcm : q ^ c.factorization q * (c / q ^ c.factorization q) = c := Nat.ordProj_mul_ordCompl_eq_self c q
    have hm0 : c / q ^ c.factorization q ≠ 0 := (Nat.ordCompl_pos q hc).ne'
    have hqm : ¬ q ∣ c / q ^ c.factorization q := Nat.not_dvd_ordCompl hqp hc
    have hcop : Nat.Coprime (q ^ c.factorization q) (c / q ^ c.factorization q) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hqp hc)
    have hmfac : ∀ p, p ≠ q → (c / q ^ c.factorization q).factorization p = c.factorization p := by
      intro p hp
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne hp]
    have hmsub : (c / q ^ c.factorization q).primeFactors ⊆ P' := by
      intro p hp
      have hpc : p ∈ c.primeFactors := Nat.primeFactors_mono (Nat.ordCompl_dvd c q) hc hp
      have hpq : p ≠ q := by
        rintro rfl
        exact hqm (Nat.dvd_of_mem_primeFactors hp)
      rcases Finset.mem_insert.mp (hsub hpc) with h | h
      · exact absurd h hpq
      · exact h
    have hterm : ∀ i, ∀ b ∈ (c / q ^ c.factorization q).divisors,
        ∏ p ∈ insert q P', φ p ((q ^ i * b).factorization p) = φ q i * ∏ p ∈ P', φ p (b.factorization p) := by
      intro i b hb
      have hb0 : b ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hb)
      have hqb : ¬ q ∣ b := fun h => hqm (dvd_trans h (Nat.dvd_of_mem_divisors hb))
      have hfac : ∀ p, (q ^ i * b).factorization p = (if q = p then i else 0) + b.factorization p := by
        intro p
        rw [Nat.factorization_mul (pow_ne_zero _ hqp.ne_zero) hb0, hqp.factorization_pow, Finsupp.add_apply,
          Finsupp.single_apply]
      rw [Finset.prod_insert hq, hfac]
      simp only [↓reduceIte, Nat.factorization_eq_zero_of_not_dvd hqb, add_zero]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have : q ≠ p := fun h => hq (h ▸ hp)
      rw [hfac]
      simp [this]
    conv_lhs => rw [← hcm]
    rw [sum_divisors_coprime_mul hcop, Nat.sum_divisors_prime_pow hqp]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hterm i)]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ih hP' _ hm0 hmsub, Finset.prod_insert hq]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hmfac p (fun h => hq (h ▸ hp))]

/-- Proof helper for item 23: `μ` at a product of distinct primes is the product of the `μ_p` (item 19). -/
private theorem cohenMu_prod_primes {t : ℤ} {n f : ℕ} (hf : f ∈ orderIndexSet t n) (Q : Finset ℕ) :
    (∀ p ∈ Q, p.Prime) → cohenMu (∏ p ∈ Q, p) t f n = ∏ p ∈ Q, cohenMu p t f n := by
  refine Finset.induction_on Q ?_ ?_
  · intro _
    simp [cohenMu, dedekindPsi]
  · intro q Q' hq ih hQ
    have hqp := hQ q (Finset.mem_insert_self _ _)
    have hQ' : ∀ p ∈ Q', p.Prime := fun p hp => hQ p (Finset.mem_insert_of_mem hp)
    have hpos : 1 ≤ ∏ p ∈ Q', p := Finset.prod_pos fun p hp => (hQ' p hp).pos
    have hcop : Nat.Coprime q (∏ p ∈ Q', p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hqp (hQ' p hp)).mpr fun h => hq (h ▸ hp)
    rw [Finset.prod_insert hq, Finset.prod_insert hq, cohenMu_mul hf hqp.one_lt.le hpos hcop, ih hQ']

/-- **D2 in Eichler's sum form** (exit). For squarefree `N`, `t² < 4n` and a weight `H : ℤ → ℚ` satisfying the
conductor relation `H(p²Δ) = (p − χ_Δ(p)) H(Δ)` for all discriminants `Δ < 0` and primes `p`:
`∑_{f ∈ 𝓕(t, n)} H(Δ_f) μ_N(t, f, n) = ∑_{f ∈ 𝓕(t, n)} H(Δ_f) ∏_{p ∣ N} m^{(1)}_p(Δ_f)`, `Δ_f = (t² − 4n)/f²`. -/
@[tf_id "III.ef.thm:d2-sum-form"]
theorem d2_sum_form {N : ℕ} (hN : Squarefree N) {t : ℤ} {n : ℕ} (htn : t ^ 2 < 4 * (n : ℤ)) (H : ℤ → ℚ)
    (hH : ∀ (Δ : ℤ) (p : ℕ), Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) → p.Prime →
      H ((p : ℤ) ^ 2 * Δ) = ((p : ℚ) - (kroneckerPrime Δ p : ℚ)) * H Δ) :
    ∑ f ∈ orderIndexSet t n, H ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * cohenMu N t f n =
      ∑ f ∈ orderIndexSet t n,
        H ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) *
          ∏ p ∈ N.primeFactors, (localFactorEichler p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) := by
  obtain ⟨c, hc1, hS, hneg0, hdisc0, hfund0, hcond⟩ := orderIndexSet_eq_divisors htn
  have hc0 : c ≠ 0 := by omega
  have hcS : c ∈ orderIndexSet t n := by rw [hS]; exact Nat.mem_divisors_self c hc0
  set Δ₀ := (t ^ 2 - 4 * (n : ℤ)) / (c : ℤ) ^ 2 with hΔ₀def
  have hΔ : t ^ 2 - 4 * (n : ℤ) = Δ₀ * (c : ℤ) ^ 2 := (Int.ediv_mul_cancel (Finset.mem_filter.mp hcS).2.1).symm
  -- `Δ_f = Δ₀ (c/f)²`
  have hΔf : ∀ f ∈ c.divisors, (t ^ 2 - 4 * (n : ℤ)) / (f : ℤ) ^ 2 = Δ₀ * ((c / f : ℕ) : ℤ) ^ 2 := by
    intro f hf
    have hfc := Nat.dvd_of_mem_divisors hf
    have hf0 : f ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hf)
    have hf2 : (f : ℤ) ^ 2 ≠ 0 := by positivity
    have hcf : (c : ℤ) = f * ((c / f : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hfc).symm
    rw [hΔ, hcf, show Δ₀ * ((f : ℤ) * ((c / f : ℕ) : ℤ)) ^ 2 = (f : ℤ) ^ 2 * (Δ₀ * ((c / f : ℕ) : ℤ) ^ 2) by ring,
      Int.mul_ediv_cancel_left _ hf2]
  set P := c.primeFactors ∪ N.primeFactors with hPdef
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_of_mem_primeFactors h
  set χ₀ : ℕ → ℤ := fun p => kroneckerPrime Δ₀ p with hχ₀
  set gl : ℕ → ℕ → ℤ := fun p j => if j = 0 then 1 else (p : ℤ) ^ (j - 1) * ((p : ℤ) - χ₀ p) with hgl
  set XP : ℕ → ℕ → ℤ := fun p a =>
    if p ∈ N.primeFactors then (if a = 0 then 1 + kroneckerPrime (t ^ 2 - 4 * n) p else (p : ℤ) + 1) else 1
    with hXP
  set YP : ℕ → ℕ → ℤ := fun p j => if p ∈ N.primeFactors then (if j = 0 then 1 + χ₀ p else 2) else 1 with hYP
  -- the weight
  have hG : ∀ e : ℕ, e ≠ 0 → e.primeFactors ⊆ P →
      ∏ p ∈ e.primeFactors, (p : ℚ) ^ (e.factorization p - 1) * ((p : ℚ) - (kroneckerPrime Δ₀ p : ℚ)) =
        ∏ p ∈ P, (gl p (e.factorization p) : ℚ) := by
    intro e he hsub
    refine Finset.prod_subset_one_on_sdiff hsub ?_ ?_
    · intro p hp
      rw [Finset.mem_sdiff] at hp
      have hp' : ¬ p ∣ e := fun h => hp.2 (Nat.mem_primeFactors.mpr ⟨hPprime p hp.1, h, he⟩)
      simp [hgl, Nat.factorization_eq_zero_of_not_dvd hp']
    · intro p hp
      have hv : e.factorization p ≠ 0 :=
        (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd he (Nat.dvd_of_mem_primeFactors hp) |>.ne'
      simp [hgl, hv, hχ₀]
  -- Cohen's `μ` as a product of local factors
  have hμ : ∀ f ∈ c.divisors, cohenMu N t f n = ∏ p ∈ P, (XP p (f.factorization p) : ℚ) := by
    intro f hf
    have hfS : f ∈ orderIndexSet t n := by rw [hS]; exact hf
    have hf0 : f ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hf)
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hN]
    rw [cohenMu_prod_primes hfS _ fun p hp => Nat.prime_of_mem_primeFactors hp]
    simp only [hXP]
    push_cast
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hpf : p ∣ f
    · have hv : f.factorization p ≠ 0 := (hpp.factorization_pos_of_dvd hf0 hpf).ne'
      rw [(cohenMu_prime hfS hpp).2 hpf]
      simp [hv]
    · rw [(cohenMu_prime hfS hpp).1 hpf]
      simp [Nat.factorization_eq_zero_of_not_dvd hpf]
  -- the Eichler local factors
  have hm1 : ∀ f ∈ c.divisors, ∏ p ∈ N.primeFactors, (localFactorEichler p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) =
      ∏ p ∈ P, (YP p ((c / f).factorization p) : ℚ) := by
    intro f hf
    have hcf0 : c / f ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hf))
      (Nat.pos_of_mem_divisors hf)).ne'
    simp only [hYP]
    push_cast
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hc := hcond f hf p hpp
    simp only [localFactorEichler, eichlerSymbol]
    by_cases hpd : p ∣ c / f
    · have hv : (c / f).factorization p ≠ 0 := (hpp.factorization_pos_of_dvd hcf0 hpd).ne'
      rw [hc.mpr hpd]
      simp [hv]
    · have hfalse : dividesConductor p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) = false := by
        rw [Bool.eq_false_iff]
        exact fun h => hpd (hc.mp h)
      rw [hfalse, hΔf f hf, kroneckerPrime_mul_sq_of_not_dvd Δ₀ hpp hpd]
      simp [Nat.factorization_eq_zero_of_not_dvd hpd, hχ₀]
  -- rewrite both sums
  have hsub : ∀ f ∈ c.divisors, (c / f).primeFactors ⊆ P := fun f hf =>
    (Nat.primeFactors_mono (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hf)) hc0).trans Finset.subset_union_left
  have hvdiv : ∀ f ∈ c.divisors, ∀ p, (c / f).factorization p = c.factorization p - f.factorization p := by
    intro f hf p
    rw [Nat.factorization_div (Nat.dvd_of_mem_divisors hf), Finsupp.tsub_apply]
  have hHf : ∀ f ∈ c.divisors, H ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) =
      H Δ₀ * ∏ p ∈ P, (gl p (c.factorization p - f.factorization p) : ℚ) := by
    intro f hf
    have hcf0 : c / f ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hf))
      (Nat.pos_of_mem_divisors hf)).ne'
    rw [hΔf f hf, conductor_relation_iterate H hH hneg0 hdisc0 hfund0 (Nat.one_le_iff_ne_zero.mpr hcf0),
      hG _ hcf0 (hsub f hf)]
    simp only [hvdiv f hf]
  have hL : ∀ f ∈ c.divisors, H ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * cohenMu N t f n =
      H Δ₀ * ∏ p ∈ P, ((gl p (c.factorization p - f.factorization p) : ℚ) * (XP p (f.factorization p) : ℚ)) := by
    intro f hf
    rw [hHf f hf, hμ f hf, Finset.prod_mul_distrib, mul_assoc]
  have hR : ∀ f ∈ c.divisors, H ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) *
      ∏ p ∈ N.primeFactors, (localFactorEichler p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) =
      H Δ₀ * ∏ p ∈ P, ((gl p (c.factorization p - f.factorization p) : ℚ) *
        (YP p (c.factorization p - f.factorization p) : ℚ)) := by
    intro f hf
    rw [hHf f hf, hm1 f hf, Finset.prod_mul_distrib, mul_assoc]
    simp only [hvdiv f hf]
  rw [hS, Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_divisors_prod_local (fun p a => (gl p (c.factorization p - a) : ℚ) * (XP p a : ℚ)) P hPprime c hc0
      Finset.subset_union_left,
    sum_divisors_prod_local (fun p a => (gl p (c.factorization p - a) : ℚ) * (YP p (c.factorization p - a) : ℚ))
      P hPprime c hc0 Finset.subset_union_left]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := hPprime p hp
  by_cases hpN : p ∈ N.primeFactors
  · -- the local identity (item 21)
    have hX0 : (1 + kroneckerPrime (t ^ 2 - 4 * n) p) =
        if c.factorization p = 0 then 1 + χ₀ p else 1 := by
      rw [hΔ]
      by_cases hpc : p ∣ c
      · have hv : c.factorization p ≠ 0 := (hpp.factorization_pos_of_dvd hc0 hpc).ne'
        rw [kroneckerPrime_mul_sq_of_dvd Δ₀ hpp hpc]
        simp [hv]
      · rw [kroneckerPrime_mul_sq_of_not_dvd Δ₀ hpp hpc]
        simp [Nat.factorization_eq_zero_of_not_dvd hpc, hχ₀]
    have key := d2_local_identity hpp (χ₀ p) (c.factorization p) (gl p) (XP p) (YP p)
      (by simp [hgl]) (fun j hj => by simp [hgl, show j ≠ 0 by omega])
      (by simp only [hXP, hpN, ↓reduceIte]; exact hX0)
      (fun a ha => by simp only [hXP, hpN, show a ≠ 0 by omega, ↓reduceIte])
      (by simp only [hYP, hpN, ↓reduceIte]) (fun j hj => by simp only [hYP, hpN, show j ≠ 0 by omega, ↓reduceIte])
    exact_mod_cast key
  · simp only [hXP, hYP, hpN, ↓reduceIte, Int.cast_one, mul_one]

end GL2TF.Explicit
