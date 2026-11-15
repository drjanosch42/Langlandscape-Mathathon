import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.Forms

/-!
# Hecke operators `T_n` on quaternionic forms (Q3 U3, items 19, 20, 23, 24, 26, 27)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §3, first half (items 19, 20, 23, 24, 26, 27 of
`docs/sprints/Q3-plan.md` §1.2).

Design (plan §1.1 item 3, user decision Q3-U5):
* `Ô_n := {y ∈ Ô ∩ B̂^× : nrd(y) ∈ n Ẑ^×}` for every order and every `n`;
* `T_n := 1_{Ô_n} · (−)` with the generic action `heckeAct` of `GL2TF.Common.HeckeModule`, the indicator being
  `ℤ`-valued: `(T_n f)(x) = Σ_{yÔ^× ⊆ Ô_n} f(xy)`. `T_n` is defined on **all** functions `B̂^× → V` (no proof
  obligation, no splitting, no local data); that it preserves `M_k(O; s)` is part of the theorems;
* the set `S_{cc'}(n) = {γ ∈ B^× : x_c⁻¹ ι(γ) x_{c'} ∈ Ô_n}` is written inline.

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF.HeckeModule

/-- `Ô_n := {y ∈ Ô ∩ B̂^× : nrd(y) ∈ n Ẑ^×}` (as a subset of `B̂^×`), for `n ∈ ℕ`. -/
@[tf_id "III.brandt.def:norm-n-set"]
def normNSet {a b : ℤ} (O : QOrder a b) (n : ℕ) : Set (BHat a b)ˣ :=
  {y | (y : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ∧
    ∃ u : Zhatˣ, nrd ((y : BHat a b) : QuatAlg FinAdele a b) = (n : FinAdele) * ((u : Zhat) : FinAdele)}

/-! ### Proof helpers for `normNSet_basic` (private copies of the `Ô`-integrality helpers of Pairing.lean, which
`lfile` cannot see from here; a later cleanup can de-duplicate). -/

private theorem nn_trd_add {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) :
    trd (x + y) = trd x + trd y := by
  simp [trd]; ring

private theorem nn_nrd_add {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) :
    nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  simp [nrd, trd]; ring

private theorem nn_nrd_smul {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    nrd (c • x) = c ^ 2 * nrd x := by
  simp [nrd]; ring

private theorem nn_trd_smul {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    trd (c • x) = c * trd x := by
  simp [trd]; ring

private theorem nn_zhat_smul {a b : ℤ} (c : Zhat) (x : BHat a b) :
    (show QuatAlg FinAdele a b from c • x) = (c : FinAdele) • (show QuatAlg FinAdele a b from x) := rfl

private theorem nn_trd_mem {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    trd (show QuatAlg FinAdele a b from y) ∈ Zhat := by
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨⟨n, hn⟩, -⟩ := trd_nrd_int_of_mem O hz
    have h := ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) z).2
    rw [show (show QuatAlg FinAdele a b from finEmbed a b z) = baseChange a b (algebraMap ℚ FinAdele) z from rfl, h,
      hn, map_intCast]
    exact intCast_mem Zhat n
  | zero =>
    show trd (0 : QuatAlg FinAdele a b) ∈ Zhat
    simp [trd]
  | add x z _ _ hx hz =>
    rw [show (show QuatAlg FinAdele a b from x + z) =
      (show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z) from rfl, nn_trd_add]
    exact Zhat.add_mem hx hz
  | smul c x _ hx =>
    rw [nn_zhat_smul, nn_trd_smul]
    exact Zhat.mul_mem c.2 hx

private theorem nn_star_smul {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    c • star x = star (c • x) := by
  ext <;> simp

private theorem nn_star_mem {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    ∃ z : BHat a b, (show QuatAlg FinAdele a b from z) = star (show QuatAlg FinAdele a b from y) ∧
      z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨finEmbed a b (star z), ?_, Submodule.subset_span ⟨star z, star_mem_order O hz, rfl⟩⟩
    show baseChange a b (algebraMap ℚ FinAdele) (star z) = star (baseChange a b (algebraMap ℚ FinAdele) z)
    ext <;> simp [baseChange]
  | zero =>
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    show (0 : QuatAlg FinAdele a b) = star (0 : QuatAlg FinAdele a b)
    rw [star_zero]
  | add x z _ _ hx hz =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    obtain ⟨z', hz'1, hz'2⟩ := hz
    refine ⟨x' + z', ?_, Submodule.add_mem _ hx'2 hz'2⟩
    show (show QuatAlg FinAdele a b from x') + (show QuatAlg FinAdele a b from z') =
      star ((show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z))
    rw [star_add, hx'1, hz'1]
  | smul c x _ hx =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    refine ⟨c • x', ?_, Submodule.smul_mem _ c hx'2⟩
    rw [nn_zhat_smul, nn_zhat_smul, hx'1, nn_star_smul]

private theorem nn_nrd_mem {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    nrd (show QuatAlg FinAdele a b from y) ∈ Zhat := by
  have hy' := hy
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨-, ⟨n, hn⟩⟩ := trd_nrd_int_of_mem O hz
    have h := ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) z).1
    rw [show (show QuatAlg FinAdele a b from finEmbed a b z) = baseChange a b (algebraMap ℚ FinAdele) z from rfl, h,
      hn, map_intCast]
    exact intCast_mem Zhat n
  | zero =>
    show nrd (0 : QuatAlg FinAdele a b) ∈ Zhat
    simp [nrd]
  | add x z hxm hzm hx hz =>
    rw [← latticeCompletion] at hxm hzm
    rw [show (show QuatAlg FinAdele a b from x + z) =
      (show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z) from rfl, nn_nrd_add]
    refine Zhat.add_mem (Zhat.add_mem (hx hxm) (hz hzm)) ?_
    obtain ⟨z', hz'1, hz'2⟩ := nn_star_mem O hzm
    have h := nn_trd_mem O (mul_mem_orderCompletion O hxm hz'2)
    rwa [show (show QuatAlg FinAdele a b from x * z') =
      (show QuatAlg FinAdele a b from x) * (show QuatAlg FinAdele a b from z') from rfl, hz'1] at h
  | smul c x hxm hx =>
    rw [← latticeCompletion] at hxm
    rw [nn_zhat_smul, nn_nrd_smul]
    exact Zhat.mul_mem (Zhat.pow_mem c.2 2) (hx hxm)

private theorem nn_nrd_mul {a b : ℤ} (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from x * y) =
      nrd (show QuatAlg FinAdele a b from x) * nrd (show QuatAlg FinAdele a b from y) :=
  (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1 x y

private theorem nn_nrd_star {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) : nrd (star x) = nrd x := by
  simp [nrd]

/-- `nrd(u) ∈ Ẑ^×` for `u ∈ Ô^×`. -/
private theorem nn_nrd_unit {a b : ℤ} (O : QOrder a b) {u : (BHat a b)ˣ} (hu : u ∈ orderCompletionUnits O) :
    ∃ v : Zhatˣ, nrd (show QuatAlg FinAdele a b from (u : BHat a b)) = ((v : Zhat) : FinAdele) := by
  have h1 := nn_nrd_mem O hu.1
  have h2 := nn_nrd_mem O hu.2
  have h12 : nrd (show QuatAlg FinAdele a b from (u : BHat a b)) *
      nrd (show QuatAlg FinAdele a b from ((u⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
    rw [← nn_nrd_mul, Units.mul_inv]
    show nrd (1 : QuatAlg FinAdele a b) = 1
    simp [nrd]
  refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext h12, Subtype.ext ((mul_comm _ _).trans h12)⟩, rfl⟩

private theorem nn_zhat_unit_inv_mul (w : Zhatˣ) : (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((w : Zhat) : FinAdele) = 1 := by
  have := congrArg (fun z : Zhat => (z : FinAdele)) w.inv_mul
  simpa only [Subring.coe_mul, Subring.coe_one] using this

/-- For `y ∈ Ô_n`: `n y⁻¹ ∈ Ô` (as `n y⁻¹ = ȳ · n/nrd(y)`). -/
private theorem nn_nsmul_inv_mem {a b : ℤ} (O : QOrder a b) (n : ℕ) {y : (BHat a b)ˣ} (hy : y ∈ normNSet O n) :
    (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨hyO, w, hw⟩ := hy
  obtain ⟨S, hS, hSO⟩ := nn_star_mem O hyO
  have hyS : (y : BHat a b) * S = algebraMap FinAdele (BHat a b) (nrd (show QuatAlg FinAdele a b from (y : BHat a b))) := by
    show (show QuatAlg FinAdele a b from (y : BHat a b)) * (show QuatAlg FinAdele a b from S) = _
    rw [hS]
    exact ((nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).1 _).1
  have key : (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
    have h1 : (y : BHat a b) * ((((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S) = algebraMap FinAdele (BHat a b) (n : FinAdele) := by
      rw [mul_smul_comm, hyS, hw, Algebra.smul_def, ← map_mul]
      congr 1
      rw [mul_left_comm, nn_zhat_unit_inv_mul, mul_one]
    calc (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b)
        = ((y⁻¹ : (BHat a b)ˣ) : BHat a b) * algebraMap FinAdele (BHat a b) (n : FinAdele) := by
          rw [Algebra.smul_def, Algebra.commutes]
      _ = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
          rw [← h1, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact smul_mem_latticeCompletion _ ((w⁻¹ : Zhatˣ) : Zhat).2 hSO

/-- `Ẑ = ℤ + nẐ`, with the integer in `[0, n)`. -/
private theorem nn_zhat_residue (n : ℕ) (hn : 0 < n) (c : FinAdele) (hc : c ∈ Zhat) :
    ∃ m : Fin n, algebraMap ℚ FinAdele ((n : ℚ)⁻¹) * (c - ((m : ℕ) : FinAdele)) ∈ Zhat := by
  set r : FinAdele := algebraMap ℚ FinAdele ((n : ℚ)⁻¹) with hr
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrn : r * (n : FinAdele) = 1 := by
    rw [hr, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul, inv_mul_cancel₀ hn', map_one]
  obtain ⟨q, hq⟩ := finAdele_exists_sub_mem_zhat (r * c)
  have hnq : algebraMap ℚ FinAdele ((n : ℚ) * q) ∈ Zhat := by
    have : algebraMap ℚ FinAdele ((n : ℚ) * q) = c - (n : FinAdele) * (r * c - algebraMap ℚ FinAdele q) := by
      rw [map_mul, map_natCast]
      linear_combination c * hrn
    rw [this]
    exact Zhat.sub_mem hc (Zhat.mul_mem (natCast_mem Zhat n) hq)
  obtain ⟨k, hk⟩ := rat_isInt_of_mem_zhat _ hnq
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk0 : 0 ≤ k % (n : ℤ) := Int.emod_nonneg _ hn0
  have hkn : k % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
  refine ⟨⟨(k % (n : ℤ)).toNat, by omega⟩, ?_⟩
  show r * (c - (((k % (n : ℤ)).toNat : ℕ) : FinAdele)) ∈ Zhat
  have hm : (((k % (n : ℤ)).toNat : ℕ) : FinAdele) = ((k % (n : ℤ) : ℤ) : FinAdele) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  have hq' : algebraMap ℚ FinAdele q = r * (k : FinAdele) := by
    have : q = (n : ℚ)⁻¹ * (k : ℚ) := by rw [← hk]; field_simp
    rw [this, map_mul, map_intCast]
  have hk' : ((k % (n : ℤ) : ℤ) : FinAdele) = (k : FinAdele) - (n : FinAdele) * ((k / (n : ℤ) : ℤ) : FinAdele) := by
    have h := Int.emod_add_mul_ediv k n
    have h' : (((k % (n : ℤ) + (n : ℤ) * (k / (n : ℤ)) : ℤ)) : FinAdele) = (k : FinAdele) := by rw [h]
    push_cast at h'
    linear_combination h'
  have hdecomp : r * (c - (((k % (n : ℤ)).toNat : ℕ) : FinAdele)) =
      (r * c - algebraMap ℚ FinAdele q) + ((k / (n : ℤ) : ℤ) : FinAdele) := by
    rw [hm, hq', hk']
    linear_combination ((k / (n : ℤ) : ℤ) : FinAdele) * hrn
  rw [hdecomp]
  exact Zhat.add_mem hq (intCast_mem Zhat _)

/-- Two elements of `Ô_n` congruent mod `nÔ` have the same coset `yÔ^×`. -/
private theorem nn_coset_eq {a b : ℤ} (O : QOrder a b) (n : ℕ) (hn : 0 < n) {y y' : (BHat a b)ˣ}
    (hy : y ∈ normNSet O n) (hy' : y' ∈ normNSet O n)
    (h : algebraMap ℚ FinAdele ((n : ℚ)⁻¹) • ((y' : BHat a b) - (y : BHat a b)) ∈
      latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    ((y : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = (y' : (BHat a b)ˣ) := by
  set r : FinAdele := algebraMap ℚ FinAdele ((n : ℚ)⁻¹) with hr
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrn : (n : FinAdele) * r = 1 := by
    rw [hr, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hn', map_one]
  -- general step: `z⁻¹ z' ∈ Ô` when `r (z' − z) ∈ Ô`
  have step : ∀ z z' : (BHat a b)ˣ, z ∈ normNSet O n →
      r • ((z' : BHat a b) - (z : BHat a b)) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) →
      ((z⁻¹ * z' : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro z z' hz ht
    set t := r • ((z' : BHat a b) - (z : BHat a b))
    have hz' : (z' : BHat a b) = (z : BHat a b) + (n : FinAdele) • t := by
      rw [smul_smul, hrn, one_smul]; abel
    have : ((z⁻¹ * z' : (BHat a b)ˣ) : BHat a b) =
        1 + ((n : FinAdele) • ((z⁻¹ : (BHat a b)ˣ) : BHat a b)) * t := by
      rw [Units.val_mul, hz', mul_add, Units.inv_mul, smul_mul_assoc, mul_smul_comm]
    rw [this]
    exact Submodule.add_mem _ (one_mem_orderCompletion O)
      (mul_mem_orderCompletion O (nn_nsmul_inv_mem O n hz) ht)
  rw [QuotientGroup.eq]
  refine ⟨step y y' hy h, ?_⟩
  rw [mul_inv_rev, inv_inv]
  refine step y' y hy' ?_
  have : r • ((y : BHat a b) - (y' : BHat a b)) = -(r • ((y' : BHat a b) - (y : BHat a b))) := by
    rw [← smul_neg, neg_sub]
  rw [this]
  exact Submodule.neg_mem _ h

/-- For `n ≥ 1`: `Ô^× Ô_n Ô^× = Ô_n`; `ȳ ∈ Ô_n` for `y ∈ Ô_n`; `Ô_1 = Ô^×`; `Ô_n` is a finite union of cosets `yÔ^×`;
hence `1_{Ô_n} ∈ H(B̂^×, Ô^×; R₀)` for every commutative ring `R₀`. -/
@[tf_id "III.brandt.lem:norm-n-set-basic"]
theorem normNSet_basic {a b : ℤ} (O : QOrder a b) (n : ℕ) (hn : 0 < n) :
    (∀ y ∈ normNSet O n, ∀ u ∈ orderCompletionUnits O, ∀ v ∈ orderCompletionUnits O, u * y * v ∈ normNSet O n) ∧
    (∀ y ∈ normNSet O n, ∃ y' ∈ normNSet O n,
      (show QuatAlg FinAdele a b from (y' : BHat a b)) = star (show QuatAlg FinAdele a b from (y : BHat a b))) ∧
    normNSet O 1 = (orderCompletionUnits O : Set (BHat a b)ˣ) ∧
    (QuotientGroup.mk '' normNSet O n : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)).Finite ∧
    (∀ (R₀ : Type) [CommRing R₀],
      HeckePair.IsHeckeFun (U := orderCompletionUnits O) ((normNSet O n).indicator (1 : (BHat a b)ˣ → R₀))) := by
  have hA : ∀ y ∈ normNSet O n, ∀ u ∈ orderCompletionUnits O, ∀ v ∈ orderCompletionUnits O,
      u * y * v ∈ normNSet O n := by
    rintro y ⟨hyO, w, hw⟩ u hu v hv
    obtain ⟨wu, hwu⟩ := nn_nrd_unit O hu
    obtain ⟨wv, hwv⟩ := nn_nrd_unit O hv
    refine ⟨?_, wu * w * wv, ?_⟩
    · rw [Units.val_mul, Units.val_mul]
      exact mul_mem_orderCompletion O (mul_mem_orderCompletion O hu.1 hyO) hv.1
    · rw [Units.val_mul, Units.val_mul, nn_nrd_mul, nn_nrd_mul, hwu, hw, hwv]
      simp only [Units.val_mul, Subring.coe_mul]
      ring
  have hB : ∀ y ∈ normNSet O n, ∃ y' ∈ normNSet O n,
      (show QuatAlg FinAdele a b from (y' : BHat a b)) = star (show QuatAlg FinAdele a b from (y : BHat a b)) := by
    rintro y ⟨hyO, w, hw⟩
    obtain ⟨S, hS, hSO⟩ := nn_star_mem O hyO
    let S' : BHat a b := (star (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) :
      QuatAlg FinAdele a b)
    have h1 : S * S' = 1 := by
      show (show QuatAlg FinAdele a b from S) *
        star (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) = (1 : QuatAlg FinAdele a b)
      rw [hS, ← star_mul]
      have : (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) *
          (show QuatAlg FinAdele a b from (y : BHat a b)) = 1 := Units.inv_mul y
      rw [this, star_one]
    have h2 : S' * S = 1 := by
      show star (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) *
        (show QuatAlg FinAdele a b from S) = (1 : QuatAlg FinAdele a b)
      rw [hS, ← star_mul]
      have : (show QuatAlg FinAdele a b from (y : BHat a b)) *
          (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := Units.mul_inv y
      rw [this, star_one]
    refine ⟨⟨S, S', h1, h2⟩, ⟨hSO, w, ?_⟩, hS⟩
    show nrd (show QuatAlg FinAdele a b from S) = _
    rw [hS, nn_nrd_star, hw]
  have hC : normNSet O 1 = (orderCompletionUnits O : Set (BHat a b)ˣ) := by
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, ?_⟩
      have := nn_nsmul_inv_mem O 1 hy
      rwa [Nat.cast_one, one_smul] at this
    · intro hy
      obtain ⟨v, hv⟩ := nn_nrd_unit O hy
      exact ⟨hy.1, v, by rw [hv, Nat.cast_one, one_mul]⟩
  have hD : (QuotientGroup.mk '' normNSet O n : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)).Finite := by
    obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
    obtain ⟨F, -, -, hF3⟩ := exists_bhat_basis e f hf
    set r : FinAdele := algebraMap ℚ FinAdele ((n : ℚ)⁻¹) with hr
    let x : (Fin 4 → Fin n) → BHat a b := fun m => ∑ i, (((m i : ℕ) : FinAdele)) • F i
    let T : (Fin 4 → Fin n) → Set ((BHat a b)ˣ ⧸ orderCompletionUnits O) := fun m =>
      {C | ∃ y ∈ normNSet O n, C = QuotientGroup.mk y ∧
        r • ((y : BHat a b) - x m) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)}
    have hsub : (QuotientGroup.mk '' normNSet O n : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) ⊆ ⋃ m, T m := by
      rintro _ ⟨y, hy, rfl⟩
      have hc : ∀ i, F.repr (y : BHat a b) i ∈ Zhat := (hF3 _).mp hy.1
      choose m hm using fun i => nn_zhat_residue n hn _ (hc i)
      refine Set.mem_iUnion.mpr ⟨m, y, hy, rfl, ?_⟩
      rw [hF3]
      intro i
      rw [map_smul, map_sub]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
      rw [show F.repr (x m) i = ((m i : ℕ) : FinAdele) from
        congrFun (F.repr_sum_self (fun i => ((m i : ℕ) : FinAdele))) i]
      exact hm i
    have hT : ∀ m, (T m).Subsingleton := by
      rintro m _ ⟨y, hy, rfl, h1⟩ _ ⟨y', hy', rfl, h2⟩
      apply nn_coset_eq O n hn hy hy'
      have : r • ((y' : BHat a b) - (y : BHat a b)) =
          r • ((y' : BHat a b) - x m) - r • ((y : BHat a b) - x m) := by
        rw [← smul_sub]; congr 1; abel
      rw [this]
      exact Submodule.sub_mem _ h2 h1
    exact (Set.finite_iUnion fun m => (hT m).finite).subset hsub
  have hiff : ∀ x u, u ∈ orderCompletionUnits O → ∀ v, v ∈ orderCompletionUnits O →
      (u * x * v ∈ normNSet O n ↔ x ∈ normNSet O n) := by
    intro x u hu v hv
    refine ⟨fun h => ?_, fun h => hA x h u hu v hv⟩
    have := hA _ h u⁻¹ (inv_mem hu) v⁻¹ (inv_mem hv)
    rwa [show u⁻¹ * (u * x * v) * v⁻¹ = x by group] at this
  refine ⟨hA, hB, hC, hD, fun R₀ _ => ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩⟩
  · have h := hiff x u hu 1 (one_mem _)
    rw [mul_one] at h
    by_cases hx : x ∈ normNSet O n
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (h.mpr hx), Pi.one_apply]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (h.mp h'))]
  · have h := hiff x 1 (one_mem _) u hu
    rw [one_mul] at h
    by_cases hx : x ∈ normNSet O n
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (h.mpr hx), Pi.one_apply]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (h.mp h'))]
  · exact hD.subset (Set.image_mono Set.support_indicator_subset)

/-! ### Proof helpers for `normNSet_product`: the idempotent `e = 1_{p ∣ m}` of `Ẑ` splits `B̂` into the
components at the primes dividing `m` and the others. -/

private theorem nn_idem (m n : ℕ) (hmn : Nat.Coprime m n) :
    ∃ e : FinAdele, e ∈ Zhat ∧ e * e = e ∧ e * algebraMap ℚ FinAdele ((n : ℚ)⁻¹) ∈ Zhat ∧
      (1 - e) * algebraMap ℚ FinAdele ((m : ℚ)⁻¹) ∈ Zhat := by
  let e : FinAdele := ⟨fun p => if (p : ℕ) ∣ m then (1 : ℚ_[p]) else 0,
    Filter.Eventually.of_forall fun p => by
      dsimp only
      split_ifs
      · exact one_mem (PadicInt.subring p)
      · exact zero_mem (PadicInt.subring p)⟩
  have he : ∀ p : Nat.Primes, e p = if (p : ℕ) ∣ m then (1 : ℚ_[p]) else 0 := fun p => rfl
  refine ⟨e, mem_zhat.mpr fun p => ?_, ?_, mem_zhat.mpr fun p => ?_, mem_zhat.mpr fun p => ?_⟩
  · rw [he]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · ext p
    rw [RestrictedProduct.mul_apply, he]
    split_ifs <;> simp
  · rw [PadicInt.mem_subring_iff, RestrictedProduct.mul_apply, he]
    show ‖(if (p : ℕ) ∣ m then (1 : ℚ_[p]) else 0) * (((n : ℚ)⁻¹ : ℚ) : ℚ_[p])‖ ≤ 1
    split_ifs with h
    · have hc : Nat.Coprime (p : ℕ) n := Nat.Coprime.coprime_dvd_left h hmn
      rw [one_mul, Rat.cast_inv, norm_inv, Rat.cast_natCast, Padic.norm_natCast_eq_one_iff.mpr hc, inv_one]
    · simp
  · rw [PadicInt.mem_subring_iff, RestrictedProduct.mul_apply, RestrictedProduct.sub_apply,
      RestrictedProduct.one_apply, he]
    show ‖(1 - if (p : ℕ) ∣ m then (1 : ℚ_[p]) else 0) * (((m : ℚ)⁻¹ : ℚ) : ℚ_[p])‖ ≤ 1
    split_ifs with h
    · simp
    · have hc : Nat.Coprime (p : ℕ) m := (Nat.Prime.coprime_iff_not_dvd p.2).mpr h
      rw [sub_zero, one_mul, Rat.cast_inv, norm_inv, Rat.cast_natCast, Padic.norm_natCast_eq_one_iff.mpr hc,
        inv_one]

private theorem nn_mixs {e : FinAdele} (he : e * e = e) (A A' B B' : FinAdele) :
    (e * A + (1 - e) * B) * (e * A' + (1 - e) * B') = e * (A * A') + (1 - e) * (B * B') := by
  linear_combination (A * A' - A * B' - B * A' + B * B') * he

private theorem nn_zhat_unit {c c' : FinAdele} (hc : c ∈ Zhat) (hc' : c' ∈ Zhat) (h : c * c' = 1) :
    ∃ v : Zhatˣ, ((v : Zhat) : FinAdele) = c :=
  ⟨⟨⟨c, hc⟩, ⟨c', hc'⟩, Subtype.ext h, Subtype.ext ((mul_comm _ _).trans h)⟩, rfl⟩

private theorem nn_mix_mul {a b : ℤ} {e : FinAdele} (he : e * e = e) (x x' y y' : BHat a b) :
    (e • x + (1 - e) • y) * (e • x' + (1 - e) • y') = e • (x * x') + (1 - e) • (y * y') := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]

private theorem nn_mix_smul {a b : ℤ} {e : FinAdele} (he : e * e = e) (x y : BHat a b) :
    e • (e • x + (1 - e) • y) = e • x ∧ (1 - e) • (e • x + (1 - e) • y) = (1 - e) • y := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  constructor <;> simp only [smul_add, smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add]

private theorem nn_split {a b : ℤ} (e : FinAdele) (x : BHat a b) : e • x + (1 - e) • x = x := by
  rw [← add_smul, add_sub_cancel, one_smul]

private theorem nn_mixU {a b : ℤ} {e : FinAdele} (he : e * e = e) (y z : (BHat a b)ˣ) :
    ∃ W : (BHat a b)ˣ, (W : BHat a b) = e • (y : BHat a b) + (1 - e) • (z : BHat a b) ∧
      ((W⁻¹ : (BHat a b)ˣ) : BHat a b) =
        e • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) + (1 - e) • ((z⁻¹ : (BHat a b)ˣ) : BHat a b) :=
  ⟨⟨_, _, by rw [nn_mix_mul he, Units.mul_inv, Units.mul_inv, nn_split],
    by rw [nn_mix_mul he, Units.inv_mul, Units.inv_mul, nn_split]⟩, rfl, rfl⟩

private theorem nn_mix_mem {a b : ℤ} (O : QOrder a b) {e : FinAdele} (he : e ∈ Zhat) {x y : BHat a b}
    (hx : x ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra))
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    e • x + (1 - e) • y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) :=
  Submodule.add_mem _ (smul_mem_latticeCompletion _ he hx)
    (smul_mem_latticeCompletion _ (Zhat.sub_mem (one_mem _) he) hy)

private theorem nn_nrd_mix {a b : ℤ} {e : FinAdele} (he : e * e = e) (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from e • x + (1 - e) • y) =
      e * nrd (show QuatAlg FinAdele a b from x) + (1 - e) * nrd (show QuatAlg FinAdele a b from y) := by
  obtain ⟨h1, h2⟩ := nn_mix_smul he x y
  have k1 : e ^ 2 * nrd (show QuatAlg FinAdele a b from e • x + (1 - e) • y) =
      e ^ 2 * nrd (show QuatAlg FinAdele a b from x) := by
    rw [← nn_nrd_smul, ← nn_nrd_smul]
    exact congrArg (fun w : BHat a b => nrd (show QuatAlg FinAdele a b from w)) h1
  have k2 : (1 - e) ^ 2 * nrd (show QuatAlg FinAdele a b from e • x + (1 - e) • y) =
      (1 - e) ^ 2 * nrd (show QuatAlg FinAdele a b from y) := by
    rw [← nn_nrd_smul, ← nn_nrd_smul]
    exact congrArg (fun w : BHat a b => nrd (show QuatAlg FinAdele a b from w)) h2
  have he2 : e ^ 2 = e := by rw [sq, he]
  have he3 : (1 - e) ^ 2 = 1 - e := by linear_combination he
  rw [he2] at k1
  rw [he3] at k2
  linear_combination k1 + k2

/-- The Hecke operator `T_n := 1_{Ô_n} · (−)`: `(T_n f)(x) = Σ_{yÔ^× ⊆ Ô_n} f(xy)` for `f : B̂^× → V`. -/
@[tf_id "III.brandt.def:hecke-operator"]
noncomputable def heckeOperator {a b : ℤ} (O : QOrder a b) (n : ℕ) {V : Type*} [AddCommGroup V]
    (f : (BHat a b)ˣ → V) : (BHat a b)ˣ → V :=
  heckeAct (U := orderCompletionUnits O) ((normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ)) f

/-- For `a, b < 0`, `n ≥ 1` and class representatives `(x_c)`: with `S_{cc'}(n) = {γ ∈ B^× : x_c⁻¹ ι(γ) x_{c'} ∈ Ô_n}`
(a finite set, stable under right multiplication by `Γ_{x_{c'}}`),
`(T_n f)(x_c) = Σ_{c'} |Γ_{x_{c'}}|⁻¹ Σ_{γ ∈ S_{cc'}(n)} ρ_k^s(γ) f(x_{c'})` for every `f ∈ M_k(O; s)`. -/
@[tf_id "III.brandt.lem:hecke-matrix-formula"]
theorem hecke_matrix_formula {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k n : ℕ) (hn : 0 < n) (r : classSet O → (BHat a b)ˣ)
    (hr : ∀ c, classOf O (r c) = c) :
    (∀ c c' : classSet O,
      {γ : (QuatAlg ℚ a b)ˣ | (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n}.Finite ∧
      ∀ γ : (QuatAlg ℚ a b)ˣ, (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n →
        ∀ δ ∈ classStabilizer (orderCompletionUnits O) (r c'),
          (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom (γ * δ) * r c' ∈ normNSet O n) ∧
    ∀ f ∈ quatForms O s k, ∀ c : classSet O,
      heckeOperator O n f (r c) =
        ∑ᶠ c' : classSet O, ((Nat.card (classStabilizer (orderCompletionUnits O) (r c')) : K)⁻¹ •
          ∑ᶠ (γ : (QuatAlg ℚ a b)ˣ)
            (_ : (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n),
            splitRep s k (γ : QuatAlg ℚ a b) (f (r c'))) := by
  classical
  have hNb := normNSet_basic O n hn
  have hfin := hNb.2.2.2.1
  have hNright : ∀ y ∈ normNSet O n, ∀ u ∈ orderCompletionUnits O, y * u ∈ normNSet O n := by
    intro y hy u hu
    have := hNb.1 y hy 1 (one_mem _) u hu
    rwa [one_mul] at this
  have hstab : ∀ (x : (BHat a b)ˣ) (δ : (QuatAlg ℚ a b)ˣ), δ ∈ classStabilizer (orderCompletionUnits O) x ↔
      x⁻¹ * Units.map (finEmbed a b).toMonoidHom δ * x ∈ orderCompletionUnits O := by
    intro x δ
    rw [classStabilizer, Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, h⟩
      rw [← h]
      convert hu using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · intro h
      refine ⟨_, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hfib : ∀ (c c' : classSet O) (γ γ' : (QuatAlg ℚ a b)ˣ),
      (QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c') :
          (BHat a b)ˣ ⧸ orderCompletionUnits O) =
        QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ' * r c') ↔
      γ⁻¹ * γ' ∈ classStabilizer (orderCompletionUnits O) (r c') := by
    intro c c' γ γ'
    rw [QuotientGroup.eq, hstab, map_mul, map_inv]
    constructor <;> intro h <;> convert h using 1 <;> group
  have hmemS : ∀ (c c' : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n ↔
      (QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c') :
          (BHat a b)ˣ ⧸ orderCompletionUnits O) ∈ hfin.toFinset := by
    intro c c' γ
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hyq⟩
      rw [QuotientGroup.eq] at hyq
      have := hNright y hy _ hyq
      rwa [mul_inv_cancel_left] at this
  have hfinS : ∀ c c' : classSet O,
      {γ : (QuatAlg ℚ a b)ˣ | (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n}.Finite := by
    intro c c'
    have : Finite (classStabilizer (orderCompletionUnits O) (r c')) :=
      ((stabilizer_units O (r c')).2.2 ha hb).1
    let Φ : (QuatAlg ℚ a b)ˣ → (BHat a b)ˣ ⧸ orderCompletionUnits O :=
      fun γ => QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c')
    have ht : ∀ q, {γ | Φ γ = q}.Finite := by
      intro q
      rcases Set.eq_empty_or_nonempty {γ | Φ γ = q} with h | ⟨γ₀, hγ₀⟩
      · rw [h]
        exact Set.finite_empty
      · refine (Set.finite_range (fun δ : classStabilizer (orderCompletionUnits O) (r c') =>
          γ₀ * (δ : (QuatAlg ℚ a b)ˣ))).subset ?_
        intro γ hγ
        have hγ₀' : Φ γ₀ = q := hγ₀
        have hγ' : Φ γ = q := hγ
        refine ⟨⟨γ₀⁻¹ * γ, (hfib c c' γ₀ γ).mp (hγ₀'.trans hγ'.symm)⟩, ?_⟩
        simp only [mul_inv_cancel_left]
    refine (Set.Finite.biUnion hfin.toFinset.finite_toSet fun q _ => ht q).subset ?_
    intro γ hγ
    exact Set.mem_biUnion (Finset.mem_coe.mpr ((hmemS c c' γ).mp hγ)) rfl
  refine ⟨fun c c' => ⟨hfinS c c', fun γ hγ δ hδ => ?_⟩, ?_⟩
  · have := hNright _ hγ _ ((hstab _ _).mp hδ)
    rwa [show (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' *
        ((r c')⁻¹ * Units.map (finEmbed a b).toMonoidHom δ * r c') =
        (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom (γ * δ) * r c' by rw [map_mul]; group] at this
  intro f hf c
  have hcls : ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      classOf O (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf O x := by
    intro γ x u hu
    refine DoubleCoset.eq.mpr ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, ?_, u⁻¹, inv_mem hu, by group⟩
    exact inv_mem ⟨γ, rfl⟩
  let h : (BHat a b)ˣ ⧸ orderCompletionUnits O → symPowerModule K (k - 2) := fun q => f (r c * Quotient.out q)
  let g : (BHat a b)ˣ ⧸ orderCompletionUnits O → classSet O := fun q => classOf O (r c * Quotient.out q)
  have hL : heckeOperator O n f (r c) = ∑ q ∈ hfin.toFinset, h q := by
    unfold heckeOperator heckeAct
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    · refine Finset.sum_congr rfl fun q hq => ?_
      have hqo : Quotient.out q ∈ normNSet O n := by
        obtain ⟨y, hy, rfl⟩ := (Set.Finite.mem_toFinset hfin).mp hq
        obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) y
        rw [hu]
        exact hNright y hy u u.2
      rw [Set.indicator_of_mem hqo, Pi.one_apply, one_smul]
    · intro q hq
      rw [Function.mem_support] at hq
      by_contra hq'
      apply hq
      rw [Set.indicator_of_notMem, zero_smul]
      intro hqo
      exact hq' (Finset.mem_coe.mpr ((Set.Finite.mem_toFinset hfin).mpr ⟨_, hqo, QuotientGroup.out_eq' q⟩))
  have hc' : ∀ c' : classSet O,
      (Nat.card (classStabilizer (orderCompletionUnits O) (r c')) : K)⁻¹ •
        ∑ᶠ (γ : (QuatAlg ℚ a b)ˣ)
          (_ : (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n),
          splitRep s k (γ : QuatAlg ℚ a b) (f (r c')) =
      ∑ q ∈ hfin.toFinset.filter (fun q => g q = c'), h q := by
    intro c'
    have : Finite (classStabilizer (orderCompletionUnits O) (r c')) :=
      ((stabilizer_units O (r c')).2.2 ha hb).1
    let Φ : (QuatAlg ℚ a b)ˣ → (BHat a b)ˣ ⧸ orderCompletionUnits O :=
      fun γ => QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c')
    have hSfin := hfinS c c'
    have hval : ∀ γ : (QuatAlg ℚ a b)ˣ, splitRep s k (γ : QuatAlg ℚ a b) (f (r c')) = h (Φ γ) := by
      intro γ
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O)
        ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c')
      show _ = f (r c * Quotient.out (Φ γ))
      rw [show Quotient.out (Φ γ) = _ from hu,
        show r c * ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' * (u : (BHat a b)ˣ)) =
          Units.map (finEmbed a b).toMonoidHom γ * r c' * (u : (BHat a b)ˣ) by group,
        hf γ (r c') u u.2]
    have hmaps : ∀ γ ∈ hSfin.toFinset, Φ γ ∈ hfin.toFinset.filter (fun q => g q = c') := by
      intro γ hγ
      rw [Set.Finite.mem_toFinset] at hγ
      rw [Finset.mem_filter]
      refine ⟨(hmemS c c' γ).mp hγ, ?_⟩
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O)
        ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c')
      show classOf O (r c * Quotient.out (Φ γ)) = c'
      rw [show Quotient.out (Φ γ) = _ from hu,
        show r c * ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' * (u : (BHat a b)ˣ)) =
          Units.map (finEmbed a b).toMonoidHom γ * r c' * (u : (BHat a b)ˣ) by group,
        hcls γ (r c') u u.2, hr c']
    have hcard : ∀ q ∈ hfin.toFinset.filter (fun q => g q = c'),
        (hSfin.toFinset.filter (fun γ => Φ γ = q)).card =
          Nat.card (classStabilizer (orderCompletionUnits O) (r c')) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hcl : classOf O (r c') = classOf O (r c * Quotient.out q) := (hr c').trans hq.2.symm
      obtain ⟨hh, ⟨γ₀, rfl⟩, kk, hkk, hrel⟩ := DoubleCoset.eq.mp hcl
      have hγ₀ : Φ γ₀ = q := by
        have h1 : (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ₀ * r c' = Quotient.out q * kk⁻¹ := by
          have h2 : Units.map (finEmbed a b).toMonoidHom γ₀ * r c' = r c * Quotient.out q * kk⁻¹ :=
            eq_mul_inv_of_mul_eq hrel.symm
          rw [mul_assoc, h2]
          group
        show QuotientGroup.mk ((r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ₀ * r c') = q
        rw [h1, QuotientGroup.mk_mul_of_mem _ (inv_mem hkk), QuotientGroup.out_eq']
      have hto : ∀ δ : classStabilizer (orderCompletionUnits O) (r c'),
          γ₀ * (δ : (QuatAlg ℚ a b)ˣ) ∈ hSfin.toFinset.filter (fun γ => Φ γ = q) := by
        intro δ
        have hΦ : Φ (γ₀ * δ) = q :=
          ((hfib c c' γ₀ (γ₀ * δ)).mpr (by rw [inv_mul_cancel_left]; exact δ.2)).symm.trans hγ₀
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨(hmemS c c' _).mpr ?_, hΦ⟩
        show Φ (γ₀ * δ) ∈ hfin.toFinset
        rw [hΦ]
        exact hq.1
      have hinv : ∀ γ ∈ hSfin.toFinset.filter (fun γ => Φ γ = q),
          γ₀⁻¹ * γ ∈ classStabilizer (orderCompletionUnits O) (r c') := by
        intro γ hγ
        exact (hfib c c' γ₀ γ).mp (hγ₀.trans (Finset.mem_filter.mp hγ).2.symm)
      rw [← Nat.card_eq_finsetCard]
      exact (Nat.card_congr ⟨fun δ => ⟨γ₀ * (δ : (QuatAlg ℚ a b)ˣ), hto δ⟩,
        fun γ => ⟨γ₀⁻¹ * (γ : (QuatAlg ℚ a b)ˣ), hinv γ γ.2⟩,
        fun δ => Subtype.ext (inv_mul_cancel_left γ₀ (δ : (QuatAlg ℚ a b)ˣ)),
        fun γ => Subtype.ext (mul_inv_cancel_left γ₀ (γ : (QuatAlg ℚ a b)ˣ))⟩).symm
    have hsum : ∑ᶠ (γ : (QuatAlg ℚ a b)ˣ)
          (_ : (r c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * r c' ∈ normNSet O n),
          splitRep s k (γ : QuatAlg ℚ a b) (f (r c')) = ∑ γ ∈ hSfin.toFinset, h (Φ γ) := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hSfin]
      exact finsum_congr fun γ => finsum_congr fun _ => hval γ
    have hne : (Nat.card (classStabilizer (orderCompletionUnits O) (r c')) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to' hmaps h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_const, hcard q hq, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hL, finsum_congr hc', finsum_eq_sum_of_support_subset _ (s := hfin.toFinset.image g) ?_]
  · exact (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem g hq) h).symm
  · intro c' hc''
    rw [Function.mem_support] at hc''
    by_contra hn'
    apply hc''
    refine Finset.sum_eq_zero fun q hq => ?_
    exfalso
    apply hn'
    rw [Finset.mem_filter] at hq
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, hq.1, hq.2⟩)

/-- For coprime `m, n ≥ 1`: `Ô_m Ô_n ⊆ Ô_{mn}`; every `w ∈ Ô_{mn}` is a product `yz` with `y ∈ Ô_m`, `z ∈ Ô_n`;
`yzÔ^× = y'z'Ô^×` (`y, y' ∈ Ô_m`, `z, z' ∈ Ô_n`) implies `yÔ^× = y'Ô^×` (the first factor's coset is determined; the second's
is not, SCR-Q3-1); and `|Ô_{mn}/Ô^×| = |Ô_m/Ô^×| · |Ô_n/Ô^×|` (numbers of cosets `yÔ^×` contained in `Ô_n`). -/
@[tf_id "III.brandt.lem:norm-n-set-product"]
theorem normNSet_product {a b : ℤ} (O : QOrder a b) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    (∀ y ∈ normNSet O m, ∀ z ∈ normNSet O n, y * z ∈ normNSet O (m * n)) ∧
    (∀ w ∈ normNSet O (m * n), ∃ y ∈ normNSet O m, ∃ z ∈ normNSet O n, w = y * z) ∧
    (∀ y ∈ normNSet O m, ∀ y' ∈ normNSet O m, ∀ z ∈ normNSet O n, ∀ z' ∈ normNSet O n,
      ((y * z : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = ((y' * z' : (BHat a b)ˣ) : _) →
        ((y : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = (y' : (BHat a b)ˣ)) ∧
    Nat.card (QuotientGroup.mk '' normNSet O (m * n) : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) =
      Nat.card (QuotientGroup.mk '' normNSet O m : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) *
        Nat.card (QuotientGroup.mk '' normNSet O n : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) := by
  obtain ⟨e, heZ, he, heN, heM⟩ := nn_idem m n hmn
  have he' : (1 - e) ∈ Zhat := Zhat.sub_mem (one_mem _) heZ
  set rm : FinAdele := algebraMap ℚ FinAdele ((m : ℚ)⁻¹) with hrm_def
  set rn : FinAdele := algebraMap ℚ FinAdele ((n : ℚ)⁻¹) with hrn_def
  have hrm : rm * (m : FinAdele) = 1 := by
    rw [hrm_def, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hm.ne'), map_one]
  have hrn : rn * (n : FinAdele) = 1 := by
    rw [hrn_def, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), map_one]
  choose Mix hMix hMixInv using fun (y z : (BHat a b)ˣ) => nn_mixU he y z
  have hinvm : ∀ y ∈ normNSet O m, (1 - e) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) ∈
      latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro y hy
    have h := nn_nsmul_inv_mem O m hy
    have : (1 - e) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) =
        ((1 - e) * rm) • ((m : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) := by
      rw [smul_smul, mul_assoc, hrm, mul_one]
    rw [this]
    exact smul_mem_latticeCompletion _ heM h
  have hinvn : ∀ z ∈ normNSet O n, e • ((z⁻¹ : (BHat a b)ˣ) : BHat a b) ∈
      latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro z hz
    have h := nn_nsmul_inv_mem O n hz
    have : e • ((z⁻¹ : (BHat a b)ˣ) : BHat a b) =
        (e * rn) • ((n : FinAdele) • ((z⁻¹ : (BHat a b)ˣ) : BHat a b)) := by
      rw [smul_smul, mul_assoc, hrn, mul_one]
    rw [this]
    exact smul_mem_latticeCompletion _ heN h
  have hnrd1 : nrd (show QuatAlg FinAdele a b from (1 : BHat a b)) = 1 := by
    show nrd (1 : QuatAlg FinAdele a b) = 1
    simp [nrd]
  -- (a)
  have hA : ∀ y ∈ normNSet O m, ∀ z ∈ normNSet O n, y * z ∈ normNSet O (m * n) := by
    rintro y ⟨hyO, wy, hwy⟩ z ⟨hzO, wz, hwz⟩
    refine ⟨by rw [Units.val_mul]; exact mul_mem_orderCompletion O hyO hzO, wy * wz, ?_⟩
    rw [Units.val_mul, nn_nrd_mul, hwy, hwz]
    simp only [Units.val_mul, Subring.coe_mul, Nat.cast_mul]
    ring
  -- (b)
  have hY : ∀ w ∈ normNSet O (m * n), Mix w 1 ∈ normNSet O m := by
    rintro w ⟨hwO, u, hu⟩
    refine ⟨by rw [hMix, Units.val_one]; exact nn_mix_mem O heZ hwO (one_mem_orderCompletion O), ?_⟩
    have hu1 := nn_zhat_unit_inv_mul u
    obtain ⟨v, hv⟩ := nn_zhat_unit (c := e * ((n : FinAdele) * ((u : Zhat) : FinAdele)) + (1 - e) * rm)
      (c' := e * (rn * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele)) + (1 - e) * (m : FinAdele))
      (Zhat.add_mem (Zhat.mul_mem heZ (Zhat.mul_mem (natCast_mem _ _) (u : Zhat).2)) heM)
      (Zhat.add_mem (by rw [← mul_assoc]; exact Zhat.mul_mem heN ((u⁻¹ : Zhatˣ) : Zhat).2)
        (Zhat.mul_mem he' (natCast_mem _ _)))
      (by
        rw [nn_mixs he]
        linear_combination e * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((u : Zhat) : FinAdele) * hrn + e * hu1 +
          (1 - e) * hrm)
    refine ⟨v, ?_⟩
    rw [hMix, Units.val_one, nn_nrd_mix he, hu, hnrd1, hv]
    push_cast
    linear_combination (-(1 - e)) * hrm
  have hZ : ∀ w ∈ normNSet O (m * n), Mix 1 w ∈ normNSet O n := by
    rintro w ⟨hwO, u, hu⟩
    refine ⟨by rw [hMix, Units.val_one]; exact nn_mix_mem O heZ (one_mem_orderCompletion O) hwO, ?_⟩
    have hu1 := nn_zhat_unit_inv_mul u
    obtain ⟨v, hv⟩ := nn_zhat_unit (c := e * rn + (1 - e) * ((m : FinAdele) * ((u : Zhat) : FinAdele)))
      (c' := e * (n : FinAdele) + (1 - e) * (rm * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele)))
      (Zhat.add_mem heN (Zhat.mul_mem he' (Zhat.mul_mem (natCast_mem _ _) (u : Zhat).2)))
      (Zhat.add_mem (Zhat.mul_mem heZ (natCast_mem _ _))
        (by rw [← mul_assoc]; exact Zhat.mul_mem heM ((u⁻¹ : Zhatˣ) : Zhat).2))
      (by
        rw [nn_mixs he]
        linear_combination e * hrn + (1 - e) * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((u : Zhat) : FinAdele) * hrm +
          (1 - e) * hu1)
    refine ⟨v, ?_⟩
    rw [hMix, Units.val_one, nn_nrd_mix he, hu, hnrd1, hv]
    push_cast
    linear_combination (-e) * hrn
  have hYZ : ∀ w : (BHat a b)ˣ, Mix w 1 * Mix 1 w = w := by
    intro w
    ext
    rw [Units.val_mul, hMix, hMix, Units.val_one, nn_mix_mul he, mul_one, one_mul, nn_split]
  have hB : ∀ w ∈ normNSet O (m * n), ∃ y ∈ normNSet O m, ∃ z ∈ normNSet O n, w = y * z :=
    fun w hw => ⟨Mix w 1, hY w hw, Mix 1 w, hZ w hw, (hYZ w).symm⟩
  -- (c)
  have hL : ∀ y ∈ normNSet O m, ∀ y' ∈ normNSet O m, ∀ z ∈ normNSet O n, ∀ z' ∈ normNSet O n,
      ∀ g ∈ orderCompletionUnits O, y' * z' = y * z * g →
        ((y⁻¹ * y' : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro y hy y' hy' z hz z' hz' g hg hyz
    have hx : y⁻¹ * y' = z * g * z'⁻¹ := by
      calc y⁻¹ * y' = y⁻¹ * (y' * z') * z'⁻¹ := by group
        _ = y⁻¹ * (y * z * g) * z'⁻¹ := by rw [hyz]
        _ = z * g * z'⁻¹ := by group
    rw [← nn_split e ((y⁻¹ * y' : (BHat a b)ˣ) : BHat a b)]
    refine Submodule.add_mem _ ?_ ?_
    · rw [hx, Units.val_mul, ← mul_smul_comm]
      exact mul_mem_orderCompletion O (by rw [Units.val_mul]; exact mul_mem_orderCompletion O hz.1 hg.1)
        (hinvn z' hz')
    · rw [Units.val_mul, ← smul_mul_assoc]
      exact mul_mem_orderCompletion O (hinvm y hy) hy'.1
  have hC : ∀ y ∈ normNSet O m, ∀ y' ∈ normNSet O m, ∀ z ∈ normNSet O n, ∀ z' ∈ normNSet O n,
      ((y * z : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = ((y' * z' : (BHat a b)ˣ) : _) →
        ((y : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = (y' : (BHat a b)ˣ) := by
    intro y hy y' hy' z hz z' hz' h
    rw [QuotientGroup.eq] at h ⊢
    have heq : y' * z' = y * z * ((y * z)⁻¹ * (y' * z')) := by rw [mul_inv_cancel_left]
    refine ⟨hL y hy y' hy' z hz z' hz' _ h heq, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact hL y' hy' y hy z' hz' z hz _ (inv_mem h) (by rw [heq]; group)
  -- (d)
  have hUmix : ∀ g ∈ orderCompletionUnits O,
      Mix g 1 ∈ orderCompletionUnits O ∧ Mix 1 g ∈ orderCompletionUnits O := by
    intro g hg
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hMix, Units.val_one]; exact nn_mix_mem O heZ hg.1 (one_mem_orderCompletion O)
    · rw [hMixInv, inv_one, Units.val_one]; exact nn_mix_mem O heZ hg.2 (one_mem_orderCompletion O)
    · rw [hMix, Units.val_one]; exact nn_mix_mem O heZ (one_mem_orderCompletion O) hg.1
    · rw [hMixInv, inv_one, Units.val_one]; exact nn_mix_mem O heZ (one_mem_orderCompletion O) hg.2
  have hYmul : ∀ w g : (BHat a b)ˣ, Mix (w * g) 1 = Mix w 1 * Mix g 1 := by
    intro w g
    ext
    rw [Units.val_mul, hMix, hMix, hMix, Units.val_one, nn_mix_mul he, mul_one, Units.val_mul]
  have hZmul : ∀ w g : (BHat a b)ˣ, Mix 1 (w * g) = Mix 1 w * Mix 1 g := by
    intro w g
    ext
    rw [Units.val_mul, hMix, hMix, hMix, Units.val_one, nn_mix_mul he, mul_one, Units.val_mul]
  have hMixY : ∀ y z : (BHat a b)ˣ, Mix (Mix y z) 1 = Mix y 1 := by
    intro y z
    ext
    rw [hMix, hMix, hMix, (nn_mix_smul he _ _).1]
  have hMixZ : ∀ y z : (BHat a b)ˣ, Mix 1 (Mix y z) = Mix 1 z := by
    intro y z
    ext
    rw [hMix, hMix, hMix, (nn_mix_smul he _ _).2]
  have hYy : ∀ y ∈ normNSet O m,
      (QuotientGroup.mk (Mix y 1) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk y := by
    intro y hy
    rw [QuotientGroup.eq]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, hMixInv, inv_one, Units.val_one, add_mul, smul_mul_assoc, smul_mul_assoc, Units.inv_mul,
        one_mul]
      exact nn_mix_mem O heZ (one_mem_orderCompletion O) hy.1
    · rw [mul_inv_rev, inv_inv, Units.val_mul, hMix, Units.val_one, mul_add, mul_smul_comm, mul_smul_comm,
        Units.inv_mul, mul_one]
      exact Submodule.add_mem _ (smul_mem_latticeCompletion _ heZ (one_mem_orderCompletion O)) (hinvm y hy)
  have hZz : ∀ z ∈ normNSet O n,
      (QuotientGroup.mk (Mix 1 z) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk z := by
    intro z hz
    rw [QuotientGroup.eq]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, hMixInv, inv_one, Units.val_one, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
        Units.inv_mul]
      exact nn_mix_mem O heZ hz.1 (one_mem_orderCompletion O)
    · rw [mul_inv_rev, inv_inv, Units.val_mul, hMix, Units.val_one, mul_add, mul_smul_comm, mul_smul_comm,
        mul_one, Units.inv_mul]
      exact Submodule.add_mem _ (hinvn z hz) (smul_mem_latticeCompletion _ he' (one_mem_orderCompletion O))
  have hYinv : ∀ w w' : (BHat a b)ˣ, (Mix w 1)⁻¹ * Mix w' 1 = Mix (w⁻¹ * w') 1 := by
    intro w w'
    ext
    rw [Units.val_mul, hMixInv, hMix, hMix, inv_one, Units.val_one, nn_mix_mul he, mul_one, Units.val_mul]
  have hZinv : ∀ w w' : (BHat a b)ˣ, (Mix 1 w)⁻¹ * Mix 1 w' = Mix 1 (w⁻¹ * w') := by
    intro w w'
    ext
    rw [Units.val_mul, hMixInv, hMix, hMix, inv_one, Units.val_one, nn_mix_mul he, mul_one, Units.val_mul]
  have hUcomb : ∀ X : (BHat a b)ˣ, Mix X 1 ∈ orderCompletionUnits O → Mix 1 X ∈ orderCompletionUnits O →
      X ∈ orderCompletionUnits O := by
    intro X h1 h2
    refine ⟨?_, ?_⟩
    · have hc : (X : BHat a b) = e • ((Mix X 1 : (BHat a b)ˣ) : BHat a b) + (1 - e) • ((Mix 1 X : (BHat a b)ˣ) : BHat a b) := by
        rw [hMix, hMix, (nn_mix_smul he _ _).1, (nn_mix_smul he _ _).2, nn_split]
      rw [hc]
      exact nn_mix_mem O heZ h1.1 h2.1
    · have hc : ((X⁻¹ : (BHat a b)ˣ) : BHat a b) = e • (((Mix X 1)⁻¹ : (BHat a b)ˣ) : BHat a b) +
          (1 - e) • (((Mix 1 X)⁻¹ : (BHat a b)ˣ) : BHat a b) := by
        rw [hMixInv, hMixInv, (nn_mix_smul he _ _).1, (nn_mix_smul he _ _).2, nn_split]
      rw [hc]
      exact nn_mix_mem O heZ h1.2 h2.2
  have hmn0 : 0 < m * n := Nat.mul_pos hm hn
  have hrep : ∀ C ∈ (QuotientGroup.mk '' normNSet O (m * n) : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)),
      Quotient.out C ∈ normNSet O (m * n) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) w
    rw [hg]
    have := (normNSet_basic O (m * n) hmn0).1 w hw 1 (one_mem _) g g.2
    rwa [one_mul] at this
  let F : (QuotientGroup.mk '' normNSet O (m * n) : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) →
      (QuotientGroup.mk '' normNSet O m : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) ×
        (QuotientGroup.mk '' normNSet O n : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) :=
    fun C => (⟨QuotientGroup.mk (Mix (Quotient.out C.1) 1), _, hY _ (hrep C.1 C.2), rfl⟩,
      ⟨QuotientGroup.mk (Mix 1 (Quotient.out C.1)), _, hZ _ (hrep C.1 C.2), rfl⟩)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
      have h1 := congrArg (fun p => (p.1 : (BHat a b)ˣ ⧸ orderCompletionUnits O)) h
      have h2 := congrArg (fun p => (p.2 : (BHat a b)ˣ ⧸ orderCompletionUnits O)) h
      change (QuotientGroup.mk (Mix (Quotient.out C) 1) : (BHat a b)ˣ ⧸ orderCompletionUnits O) =
        QuotientGroup.mk (Mix (Quotient.out C') 1) at h1
      change (QuotientGroup.mk (Mix 1 (Quotient.out C)) : (BHat a b)ˣ ⧸ orderCompletionUnits O) =
        QuotientGroup.mk (Mix 1 (Quotient.out C')) at h2
      apply Subtype.ext
      show C = C'
      rw [← QuotientGroup.out_eq' C, ← QuotientGroup.out_eq' C']
      rw [QuotientGroup.eq] at h1 h2 ⊢
      rw [hYinv] at h1
      rw [hZinv] at h2
      exact hUcomb _ h1 h2
    · rintro ⟨⟨A, y, hy, rfl⟩, ⟨B, z, hz, rfl⟩⟩
      obtain ⟨hyO, uy, huy⟩ := hy
      obtain ⟨hzO, uz, huz⟩ := hz
      have hW : Mix y z ∈ normNSet O (m * n) := by
        refine ⟨by rw [hMix]; exact nn_mix_mem O heZ hyO hzO, ?_⟩
        have huy1 := nn_zhat_unit_inv_mul uy
        have huz1 := nn_zhat_unit_inv_mul uz
        obtain ⟨v, hv⟩ := nn_zhat_unit
          (c := e * (rn * ((uy : Zhat) : FinAdele)) + (1 - e) * (rm * ((uz : Zhat) : FinAdele)))
          (c' := e * ((n : FinAdele) * (((uy⁻¹ : Zhatˣ) : Zhat) : FinAdele)) +
            (1 - e) * ((m : FinAdele) * (((uz⁻¹ : Zhatˣ) : Zhat) : FinAdele)))
          (Zhat.add_mem (by rw [← mul_assoc]; exact Zhat.mul_mem heN (uy : Zhat).2)
            (by rw [← mul_assoc]; exact Zhat.mul_mem heM (uz : Zhat).2))
          (Zhat.add_mem (Zhat.mul_mem heZ (Zhat.mul_mem (natCast_mem _ _) ((uy⁻¹ : Zhatˣ) : Zhat).2))
            (Zhat.mul_mem he' (Zhat.mul_mem (natCast_mem _ _) ((uz⁻¹ : Zhatˣ) : Zhat).2)))
          (by
            rw [nn_mixs he]
            linear_combination e * (((uy⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((uy : Zhat) : FinAdele) * hrn +
              e * huy1 + (1 - e) * (((uz⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((uz : Zhat) : FinAdele) * hrm +
              (1 - e) * huz1)
        refine ⟨v, ?_⟩
        rw [hMix, nn_nrd_mix he, huy, huz, hv]
        push_cast
        linear_combination (-(e * (m : FinAdele) * ((uy : Zhat) : FinAdele))) * hrn -
          ((1 - e) * (n : FinAdele) * ((uz : Zhat) : FinAdele)) * hrm
      refine ⟨⟨QuotientGroup.mk (Mix y z), Mix y z, hW, rfl⟩, ?_⟩
      obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) (Mix y z)
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (QuotientGroup.mk (Mix (Quotient.out (QuotientGroup.mk (Mix y z) :
          (BHat a b)ˣ ⧸ orderCompletionUnits O)) 1) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk y
        rw [hg, hYmul, QuotientGroup.mk_mul_of_mem _ (hUmix g g.2).1, hMixY, hYy y ⟨hyO, uy, huy⟩]
      · show (QuotientGroup.mk (Mix 1 (Quotient.out (QuotientGroup.mk (Mix y z) :
          (BHat a b)ˣ ⧸ orderCompletionUnits O))) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk z
        rw [hg, hZmul, QuotientGroup.mk_mul_of_mem _ (hUmix g g.2).2, hMixZ, hZz z ⟨hzO, uz, huz⟩]
  refine ⟨hA, hB, hC, ?_⟩
  rw [Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

/-- For every order and coprime `m, n ≥ 1`: `1_{Ô_m} ∗ 1_{Ô_n} = 1_{Ô_{mn}}` in `H(B̂^×, Ô^×; ℤ)`; hence
`T_m T_n = T_{mn} = T_n T_m` on `M_k(O; s)`. -/
@[tf_id "III.brandt.thm:hecke-multiplicative"]
theorem hecke_multiplicative {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    (∃ (h₁ : HeckePair.IsHeckeFun (U := orderCompletionUnits O) ((normNSet O m).indicator (1 : (BHat a b)ˣ → ℤ)))
      (h₂ : HeckePair.IsHeckeFun (U := orderCompletionUnits O) ((normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ)))
      (h₃ : HeckePair.IsHeckeFun (U := orderCompletionUnits O)
        ((normNSet O (m * n)).indicator (1 : (BHat a b)ˣ → ℤ))),
      (⟨_, h₁⟩ * ⟨_, h₂⟩ : HeckePair.HeckeAlgebra (orderCompletionUnits O) ℤ) = ⟨_, h₃⟩) ∧
    ∀ f ∈ quatForms O s k,
      heckeOperator O m (heckeOperator O n f) = heckeOperator O (m * n) f ∧
      heckeOperator O n (heckeOperator O m f) = heckeOperator O (m * n) f := by
  have hH : ∀ k : ℕ, 0 < k → HeckePair.IsHeckeFun (U := orderCompletionUnits O)
      ((normNSet O k).indicator (1 : (BHat a b)ˣ → ℤ)) := fun k hk => (normNSet_basic O k hk).2.2.2.2 ℤ
  have key : ∀ m n : ℕ, ∀ (hm : 0 < m) (hn : 0 < n), Nat.Coprime m n →
      (⟨_, hH m hm⟩ * ⟨_, hH n hn⟩ : HeckePair.HeckeAlgebra (orderCompletionUnits O) ℤ) =
        ⟨_, hH (m * n) (Nat.mul_pos hm hn)⟩ := by
    intro m n hm hn hmn
    obtain ⟨hA, hB, hC, -⟩ := normNSet_product O m n hm hn hmn
    ext x
    rw [HeckePair.mul_apply]
    show _ = (normNSet O (m * n)).indicator (1 : (BHat a b)ˣ → ℤ) x
    by_cases hx : x ∈ normNSet O (m * n)
    · obtain ⟨y₀, hy₀, z₀, hz₀, rfl⟩ := hB x hx
      rw [Set.indicator_of_mem hx,
        finsum_eq_single _ (QuotientGroup.mk y₀ : (BHat a b)ˣ ⧸ orderCompletionUnits O)]
      · rw [HeckePair.convTerm_mk]
        show (normNSet O m).indicator (1 : (BHat a b)ˣ → ℤ) y₀ *
          (normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ) (y₀⁻¹ * (y₀ * z₀)) = _
        simp only [inv_mul_cancel_left, Set.indicator_of_mem hy₀, Set.indicator_of_mem hz₀, Pi.one_apply,
          mul_one]
      · intro c hc
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
        rw [HeckePair.convTerm_mk]
        show (normNSet O m).indicator (1 : (BHat a b)ˣ → ℤ) y *
          (normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ) (y⁻¹ * (y₀ * z₀)) = 0
        by_cases hy : y ∈ normNSet O m
        · by_cases hz : y⁻¹ * (y₀ * z₀) ∈ normNSet O n
          · exfalso
            apply hc
            apply hC y hy y₀ hy₀ (y⁻¹ * (y₀ * z₀)) hz z₀ hz₀
            rw [mul_inv_cancel_left]
          · rw [Set.indicator_of_notMem hz, mul_zero]
        · rw [Set.indicator_of_notMem hy, zero_mul]
    · rw [Set.indicator_of_notMem hx]
      refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
      rw [HeckePair.convTerm_mk]
      show (normNSet O m).indicator (1 : (BHat a b)ˣ → ℤ) y *
        (normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ) (y⁻¹ * x) = 0
      by_cases hy : y ∈ normNSet O m
      · by_cases hz : y⁻¹ * x ∈ normNSet O n
        · exfalso
          apply hx
          have := hA y hy _ hz
          rwa [mul_inv_cancel_left] at this
        · rw [Set.indicator_of_notMem hz, mul_zero]
      · rw [Set.indicator_of_notMem hy, zero_mul]
  refine ⟨⟨hH m hm, hH n hn, hH (m * n) (Nat.mul_pos hm hn), key m n hm hn hmn⟩, fun f hf => ?_⟩
  have hmod := heckeAct_module K (R₀ := ℤ) (Units.map (finEmbed a b).toMonoidHom) (orderCompletionUnits O)
    (fun γ => splitRep s k (γ : QuatAlg ℚ a b))
    (by
      show splitRep s k ((1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1
      rw [Units.val_one, splitRep, map_one, (symPower_basic K (k - 2)).2.2.2.1])
    (fun γ r v => map_zsmul _ r v)
  have h1 := hmod.2.2.1 ⟨_, hH m hm⟩ ⟨_, hH n hn⟩ f hf
  have h2 := hmod.2.2.1 ⟨_, hH n hn⟩ ⟨_, hH m hm⟩ f hf
  rw [key m n hm hn hmn] at h1
  rw [key n m hn hm hmn.symm] at h2
  refine ⟨h1.symm, ?_⟩
  rw [mul_comm m n]
  exact h2.symm

end GL2TF.Quat
