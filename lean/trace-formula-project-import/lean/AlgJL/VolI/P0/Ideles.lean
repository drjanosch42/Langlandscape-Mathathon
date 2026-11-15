import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Adeles
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.SpecialFunctions.Pow.Complex


-- algebraic_jl fork (L-A, 2026-11-14): trimmed copy of lean/GL2TF/VolI/P0/Ideles.lean @84818d0. Kept declarations are
-- byte-identical. Dropped (analytic): Borel/measurability instances and lemmas (zhatUnits_borelSpace, ideles_borelSpace,
-- ...), realUnitsHaar, ideleHaar (+ _spec), adele_haar_scaling, fourier_dilation, zhatUnitsHaar, normOneClassGroupHaar
-- (+ _spec), DirichletPair, l2_norm_one_quotient, l2_torus_quotient, hecke_character_classification and their untagged
-- helpers; the L²/integration imports. The definition `HeckeCharacter` is kept.

/-!
# Ideles of ℚ, Ẑ^× and Hecke characters (M3, unit U4)

Lean counterpart of `vol1/ch-0-03-adeles.tex` §§3–4, and of the adelic Fourier dilation lemma of §2 (it needs the
idele norm, so it lives here; D-TATE). Owner: L2.

Design: `𝔸^× = Adeleˣ` with Mathlib's units topology (`x ↦ (x, x⁻¹)`). The idele norm is a monoid hom whose
multiplicativity fields are named lemmas. The decomposition `𝔸^× ≅ ℚ^× × ℝ_{>0} × Ẑ^×` and the iso
`Ẑ^× ≅ 𝔸^1/ℚ^×` are theorems (existence of a topological iso with the stated formula); consumers that need the
coordinates `u(x)` or the inverse `Θ` take such an iso as an explicit argument together with its defining formula, which
determines it uniquely. Characters of `Ẑ^×` are `ContinuousMonoidHom Zhatˣ ℂˣ` (D-DIRPAIR).
-/

open RestrictedProduct Filter Topology MeasureTheory
open scoped Pointwise ENNReal NNReal

namespace GL2TF

/-! ### Ideles and the idele norm -/

/-- The idele group `𝔸^×`: the units of `𝔸` with the units topology. -/
@[tf_id "I.adele.def:ideles"]
abbrev Idele : Type := Adeleˣ

/-- The identification `𝔸^× = ℝ^× × Πʳ_p (ℚ_p^×, ℤ_p^×)`, componentwise (Mathlib's `MulEquiv.prodUnits` and
`RestrictedProduct.unitsEquiv`) (B-only plumbing). -/
@[tf_aux "I.adele.def:ideles-restricted-product-equiv"]
noncomputable def ideleEquiv :
    Idele ≃* (ℝˣ × Πʳ (p : Nat.Primes), [ℚ_[p]ˣ, (Submonoid.ofClass (PadicInt.subring p)).units]) :=
  MulEquiv.prodUnits.trans (MulEquiv.prodCongr (MulEquiv.refl ℝˣ) (RestrictedProduct.unitsEquiv fun p : Nat.Primes ↦ ℚ_[p]))

/-- The idele norm on the underlying function level (proof plumbing for `ideleNorm`). -/
@[tf_aux "I.adele.def:idele-norm-fun"]
noncomputable def ideleNormFun (x : Idele) : ℝ :=
  |(x : Adele).1| * ∏ᶠ p : Nat.Primes, Local.normAbs ℚ_[p] ((x : Adele).2 p)

/-- `x_p x⁻¹_p = 1` for an idele `x` (proof plumbing). -/
theorem idele_comp_mul_inv (x : Idele) (p : Nat.Primes) :
    (x : Adele).2 p * ((x⁻¹ : Idele) : Adele).2 p = 1 := by
  have h := congrArg (fun z : Adele ↦ z.2 p) x.mul_inv
  simpa only [Prod.snd_mul, Prod.snd_one, RestrictedProduct.mul_apply, RestrictedProduct.one_apply] using h

/-- The finite components of an idele are non-zero (proof plumbing). -/
theorem idele_comp_ne_zero (x : Idele) (p : Nat.Primes) : (x : Adele).2 p ≠ 0 :=
  left_ne_zero_of_mul_eq_one (idele_comp_mul_inv x p)

/-- `x ∈ 𝔸` is a unit iff `x_∞ ≠ 0`, `x_p ≠ 0` for all `p`, and `x_p ∈ ℤ_p^×` for almost all `p` (B-only companion
of `I.adele.def:ideles`). -/
@[tf_aux "I.adele.lem:ideles-explicit"]
theorem isUnit_adele_iff (x : Adele) :
    IsUnit x ↔ x.1 ≠ 0 ∧ (∀ p : Nat.Primes, x.2 p ≠ 0) ∧
      ∀ᶠ p : Nat.Primes in cofinite, ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = x.2 p := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : (u : Adele).1 * ((u⁻¹ : Adeleˣ) : Adele).1 = 1 := congrArg Prod.fst u.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h1, idele_comp_ne_zero u, ?_⟩
    filter_upwards [(u : Adele).2.2, ((u⁻¹ : Adeleˣ) : Adele).2.2] with p ha hb
    have hab := idele_comp_mul_inv u p
    exact ⟨⟨⟨_, ha⟩, ⟨_, hb⟩, Subtype.ext hab, Subtype.ext ((mul_comm _ _).trans hab)⟩, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    let y : FinAdele := ⟨fun p ↦ (x.2 p)⁻¹, by
      filter_upwards [h3] with p ⟨v, hv⟩
      show (x.2 p)⁻¹ ∈ (PadicInt.subring p : Set ℚ_[p])
      have hinv : (x.2 p)⁻¹ = (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
        rw [← hv]
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
      rw [hinv]; exact ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]).2⟩
    refine IsUnit.of_mul_eq_one (x.1⁻¹, y) (Prod.ext (mul_inv_cancel₀ h1) ?_)
    ext p
    exact mul_inv_cancel₀ (h2 p)

/-- `|x_p|_{ℚ_p} = 1` for almost all `p` (proof plumbing for `ideleNorm`). -/
theorem idele_normAbs_eventually_one (x : Idele) :
    (Function.mulSupport fun p : Nat.Primes ↦ Local.normAbs ℚ_[p] ((x : Adele).2 p)).Finite := by
  have h1 := (x : Adele).2.2
  have h2 := ((x⁻¹ : Idele) : Adele).2.2
  refine (h1.and h2).subset fun p hp ↦ ?_
  by_contra hc
  obtain ⟨ha, hb⟩ := not_not.mp hc
  apply hp
  have hab := idele_comp_mul_inv x p
  let v : ℤ_[p]ˣ := ⟨⟨_, ha⟩, ⟨_, hb⟩, Subtype.ext hab, Subtype.ext ((mul_comm _ _).trans hab)⟩
  exact Local.normAbs_padicInt_unit v

/-- `|1|_𝔸 = 1` (proof plumbing for `ideleNorm`). -/
theorem ideleNormFun_one : ideleNormFun 1 = 1 := by
  simp [ideleNormFun, Local.normAbs_one]

/-- `|xy|_𝔸 = |x|_𝔸 |y|_𝔸` (proof plumbing for `ideleNorm`). -/
theorem ideleNormFun_mul (x y : Idele) : ideleNormFun (x * y) = ideleNormFun x * ideleNormFun y := by
  have hmul : ∀ p : Nat.Primes, Local.normAbs ℚ_[p] (((x * y : Idele) : Adele).2 p) =
      Local.normAbs ℚ_[p] ((x : Adele).2 p) * Local.normAbs ℚ_[p] ((y : Adele).2 p) := fun p ↦ by
    rw [Units.val_mul]
    exact Local.normAbs_mul_of_ne_zero _ (idele_comp_ne_zero x p) (idele_comp_ne_zero y p)
  unfold ideleNormFun
  rw [finprod_congr hmul, finprod_mul_distrib (idele_normAbs_eventually_one x) (idele_normAbs_eventually_one y),
    Units.val_mul, Prod.fst_mul, abs_mul]
  ring

/-- The idele norm `|x|_𝔸 = |x_∞| ∏_p |x_p|_{ℚ_p}` (a finite product), a group homomorphism `𝔸^× → ℝ`. -/
@[tf_id "I.adele.def:idele-norm"]
noncomputable def ideleNorm : Idele →* ℝ where
  toFun := ideleNormFun
  map_one' := ideleNormFun_one
  map_mul' := ideleNormFun_mul

/-- `𝔸^1 = {x ∈ 𝔸^× : |x|_𝔸 = 1}`, the kernel of the idele norm (B-only plumbing for `I.adele.def:idele-norm`). -/
@[tf_aux "I.adele.def:norm-one-ideles"]
noncomputable def ideleNormOne : Subgroup Idele := ideleNorm.ker

/-- The diagonal embedding `ℚ^× → 𝔸^×` (B-only plumbing). -/
@[tf_aux "I.adele.def:rat-ideles-embedding"]
noncomputable def ratIdele : ℚˣ →* Idele := Units.map (algebraMap ℚ Adele).toMonoidHom

/-- `ℚ^×` as a subgroup of `𝔸^×` (B-only plumbing). -/
@[tf_aux "I.adele.def:rat-ideles"]
noncomputable def ratIdeles : Subgroup Idele := ratIdele.range

/-- Product formula: `|q|_𝔸 = 1` for `q ∈ ℚ^×`, i.e. `ℚ^× ⊆ 𝔸^1`. -/
@[tf_id "I.adele.thm:product-formula"]
theorem product_formula (q : ℚˣ) : ideleNorm (ratIdele q) = 1 := by
  let φ : ℚˣ →* ℝ := ideleNorm.comp ratIdele
  change φ q = 1
  have hφ : ∀ u : ℚˣ, φ u = |((u : ℚ) : ℝ)| * ∏ᶠ p : Nat.Primes, ‖((u : ℚ) : ℚ_[p])‖ := fun u ↦
    congrArg (_ * ·) (finprod_congr fun p ↦ Local.normAbs_padic _)
  have hneg : φ (-1) = 1 := by
    rw [hφ]
    simp
  have hprime : ∀ p : ℕ, (hp : p.Prime) → φ (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) = 1 := by
    intro p hp
    have hs := finprod_eq_single (fun ℓ : Nat.Primes ↦ ‖((p : ℚ) : ℚ_[ℓ])‖) (⟨p, hp⟩ : Nat.Primes)
      fun ℓ hℓ ↦ by
        simp only [Rat.cast_natCast]
        rw [Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes ℓ.2 hp).mpr fun h ↦ hℓ (Subtype.ext h)
    rw [hφ, Units.val_mk0, hs, Rat.cast_natCast, Nat.abs_cast]
    have : Fact p.Prime := ⟨hp⟩
    change (p : ℝ) * ‖((p : ℚ) : ℚ_[p])‖ = 1
    rw [Rat.cast_natCast, Padic.norm_p, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
  have hnat : ∀ n : ℕ, (hn : n ≠ 0) → φ (Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn)) = 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _; rw [show Units.mk0 ((1 : ℕ) : ℚ) _ = 1 from Units.ext (by simp), map_one]
    | prime p hp => intro _; exact hprime p hp
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
      rw [show Units.mk0 ((a * b : ℕ) : ℚ) _ = Units.mk0 (a : ℚ) (Nat.cast_ne_zero.mpr ha0) *
          Units.mk0 (b : ℚ) (Nat.cast_ne_zero.mpr hb0) from Units.ext (by simp), map_mul, ha ha0, hb hb0,
        one_mul]
  have hint : ∀ n : ℤ, (hn : n ≠ 0) → φ (Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)) = 1 := by
    intro n hn
    rcases Int.natAbs_eq n with h | h
    · have h0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
      rw [show Units.mk0 (n : ℚ) _ = Units.mk0 (n.natAbs : ℚ) (Nat.cast_ne_zero.mpr h0) from
        Units.ext (by
          simp only [Units.val_mk0]
          rw [show (n : ℚ) = ((n.natAbs : ℤ) : ℚ) by rw [← h], Int.cast_natCast])]
      exact hnat _ h0
    · have h0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
      rw [show Units.mk0 (n : ℚ) _ = -1 * Units.mk0 (n.natAbs : ℚ) (Nat.cast_ne_zero.mpr h0) from
        Units.ext (by
          simp only [Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one]
          rw [show (n : ℚ) = ((-(n.natAbs : ℤ) : ℤ) : ℚ) by rw [← h], Int.cast_neg, Int.cast_natCast]
          ring), map_mul, hneg, hnat _ h0, one_mul]
  have hq : q = Units.mk0 ((q : ℚ).num : ℚ) (Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr q.ne_zero)) *
      (Units.mk0 ((q : ℚ).den : ℚ) (Nat.cast_ne_zero.mpr (q : ℚ).den_nz))⁻¹ :=
    Units.ext (by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [← div_eq_mul_inv, Rat.num_div_den])
  rw [hq, map_mul, map_inv, hint _ (Rat.num_ne_zero.mpr q.ne_zero), hnat _ (q : ℚ).den_nz, inv_one, one_mul]

/-- The idele `(r, u)` with component `r` at `∞` and `u_p` at `p` (for `r ≠ 0`, `u ∈ Ẑ^×`; the value at `r = 0`
is the junk value `(1, u)`) (B-only plumbing). -/
@[tf_aux "I.adele.def:idele-inf-fin"]
noncomputable def ideleInfFin (r : ℝ) (u : Zhatˣ) : Idele :=
  haveI := Classical.propDecidable (r = 0)
  MulEquiv.prodUnits.symm
    (if h : r = 0 then 1 else Units.mk0 r h, Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom u)

/-- The underlying adele of `ideleInfFin r u` for `r ≠ 0` (proof helper). -/
theorem ideleInfFin_val {r : ℝ} (hr : r ≠ 0) (u : Zhatˣ) :
    ((ideleInfFin r u : Idele) : Adele) = (r, ((u : Zhat) : FinAdele)) := by
  simp only [ideleInfFin, hr, dite_false]
  rfl

/-- `|u_p|_p = 1` for `u ∈ Ẑ^×` (proof helper). -/
theorem norm_zhatUnit_apply (u : Zhatˣ) (p : Nat.Primes) : ‖((u : Zhat) : FinAdele) p‖ = 1 := by
  obtain ⟨v, hv⟩ := (zhat_units_explicit _).mp ⟨u, rfl⟩ p
  rw [← hv, ← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.mp v.isUnit

/-- `|(r, u)|_𝔸 = |r|` for `r ≠ 0` (proof helper). -/
theorem ideleNorm_ideleInfFin {r : ℝ} (hr : r ≠ 0) (u : Zhatˣ) : ideleNorm (ideleInfFin r u) = |r| := by
  change ideleNormFun _ = _
  have hv : ∀ p : Nat.Primes, Local.normAbs ℚ_[p] (((ideleInfFin r u : Idele) : Adele).2 p) = 1 := fun p ↦ by
    rw [ideleInfFin_val hr, Local.normAbs_padic]
    exact norm_zhatUnit_apply u p
  rw [ideleNormFun, finprod_congr hv, finprod_one, ideleInfFin_val hr, mul_one]

/-- A rational number with `|q|_p = 1` for every `p` is `±1` (proof helper). -/
theorem rat_eq_one_or_neg_one (q : ℚ) (h : ∀ p : Nat.Primes, ‖(q : ℚ_[p])‖ = 1) : q = 1 ∨ q = -1 := by
  have hcast : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (q : ℚ_[ℓ]) = (q.num : ℚ_[ℓ]) / (q.den : ℚ_[ℓ]) := fun ℓ _ ↦ by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : q.den = 1 := by
    by_contra hd
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have h1 : ‖(q.den : ℚ_[ℓ])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hℓd
    have h2 : ‖(q.num : ℚ_[ℓ])‖ = 1 := by
      rw [Padic.norm_intCast_eq_one_iff, Int.isCoprime_iff_gcd_eq_one]
      exact Nat.Coprime.coprime_dvd_right hℓd q.reduced
    have h3 : ‖(q : ℚ_[ℓ])‖ = 1 := h ⟨ℓ, hℓ⟩
    rw [hcast ℓ, norm_div, h2] at h3
    have h4 : 0 < ‖(q.den : ℚ_[ℓ])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
    rw [div_eq_one_iff_eq h4.ne'] at h3
    exact h1.ne h3.symm
  have hnum : q.num.natAbs = 1 := by
    by_contra hn
    obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have h1 : ‖(q.num : ℚ_[ℓ])‖ < 1 := Padic.norm_intCast_lt_one_iff.mpr (Int.natCast_dvd.mpr hℓn)
    have h3 : ‖(q : ℚ_[ℓ])‖ = 1 := h ⟨ℓ, hℓ⟩
    rw [hcast ℓ, hden, Nat.cast_one, div_one] at h3
    exact h1.ne h3
  rcases Int.natAbs_eq_iff.mp hnum with h1 | h1
  · left; rw [← Rat.num_div_den q, h1, hden]; simp
  · right; rw [← Rat.num_div_den q, h1, hden]; simp

/-- The underlying adele of `ratIdele q` (proof helper). -/
theorem ratIdele_val (q : ℚˣ) : ((ratIdele q : Idele) : Adele) = algebraMap ℚ Adele q := rfl

/-- `(r, u)(r', u') = (rr', uu')` (proof helper). -/
theorem ideleInfFin_mul {r r' : ℝ} (hr : r ≠ 0) (hr' : r' ≠ 0) (u u' : Zhatˣ) :
    ideleInfFin (r * r') (u * u') = ideleInfFin r u * ideleInfFin r' u' := by
  apply Units.ext
  rw [Units.val_mul, ideleInfFin_val (mul_ne_zero hr hr'), ideleInfFin_val hr, ideleInfFin_val hr']
  rfl

/-- Kernel of `(q, r, u) ↦ q·(r, u)` (proof helper for `idele_decomposition`). -/
theorem ratIdele_mul_ideleInfFin_eq_one {q : ℚˣ} {r : ℝ} (hr : 0 < r) {u : Zhatˣ}
    (h : ratIdele q * ideleInfFin r u = 1) : q = 1 ∧ r = 1 ∧ u = 1 := by
  have hv := congrArg (fun x : Idele ↦ (x : Adele)) h
  simp only [Units.val_mul, Units.val_one, ratIdele_val, ideleInfFin_val hr.ne'] at hv
  have h1 : ((q : ℚ) : ℝ) * r = 1 := congrArg Prod.fst hv
  have h2 : ∀ p : Nat.Primes, ((q : ℚ) : ℚ_[p]) * ((u : Zhat) : FinAdele) p = 1 := fun p ↦ by
    have := congrArg (fun z : Adele ↦ z.2 p) hv
    simp only [Prod.snd_mul, Prod.snd_one, RestrictedProduct.mul_apply, RestrictedProduct.one_apply] at this
    exact this
  have hq1 : ∀ p : Nat.Primes, ‖((q : ℚ) : ℚ_[p])‖ = 1 := fun p ↦ by
    have := congrArg norm (h2 p)
    rwa [norm_mul, norm_zhatUnit_apply, mul_one, norm_one] at this
  have hqpos : (0 : ℝ) < (q : ℚ) := by
    by_contra hneg
    push Not at hneg
    have : ((q : ℚ) : ℝ) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hr.le
    linarith
  have hq : (q : ℚ) = 1 := by
    rcases rat_eq_one_or_neg_one _ hq1 with h | h
    · exact h
    · rw [h] at hqpos; norm_num at hqpos
  refine ⟨Units.ext hq, by rw [hq, Rat.cast_one, one_mul] at h1; exact h1, ?_⟩
  apply Units.ext
  apply Subtype.ext
  ext p
  have := h2 p
  rw [hq, Rat.cast_one, one_mul] at this
  exact this

/-- Every idele is `q·(r, u)` with `q ∈ ℚ^×`, `r > 0`, `u ∈ Ẑ^×` (proof helper for `idele_decomposition`). -/
theorem exists_ratIdele_mul_ideleInfFin (x : Idele) :
    ∃ (q : ℚˣ) (r : ℝ) (u : Zhatˣ), 0 < r ∧ x = ratIdele q * ideleInfFin r u := by
  classical
  have hS := idele_normAbs_eventually_one x
  set S := hS.toFinset
  have hx0 : ∀ p : Nat.Primes, (x : Adele).2 p ≠ 0 := idele_comp_ne_zero x
  -- `q₀ = ∏_{p ∈ S} p^{v_p(x_p)}`
  set q₀ : ℚ := ∏ p ∈ S, ((p : ℕ) : ℚ) ^ ((x : Adele).2 p).valuation
  have hq₀pos : 0 < q₀ := Finset.prod_pos fun p _ ↦ zpow_pos (by exact_mod_cast p.2.pos) _
  have hnorm : ∀ ℓ : Nat.Primes, ‖((q₀ : ℚ) : ℚ_[ℓ])‖ = ‖(x : Adele).2 ℓ‖ := by
    intro ℓ
    simp only [q₀, Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast, norm_prod, norm_zpow]
    by_cases hℓ : ℓ ∈ S
    · rw [Finset.prod_eq_single ℓ]
      · rw [Padic.norm_p, inv_zpow', Padic.norm_eq_zpow_neg_valuation (hx0 ℓ)]
      · intro p _ hp
        rw [Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes ℓ.2 p.2).mpr fun h ↦ hp (Subtype.ext h).symm),
          one_zpow]
      · intro h; exact absurd hℓ h
    · rw [Finset.prod_eq_one]
      · have : Local.normAbs ℚ_[ℓ] ((x : Adele).2 ℓ) = 1 := by
          by_contra hne
          exact hℓ ((Set.Finite.mem_toFinset hS).mpr hne)
        rw [Local.normAbs_padic] at this
        exact this.symm
      · intro p hp
        have hpℓ : p ≠ ℓ := fun h ↦ hℓ (h ▸ hp)
        rw [Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes ℓ.2 p.2).mpr fun h ↦ hpℓ (Subtype.ext h).symm),
          one_zpow]
  -- the sign
  set ε : ℚ := if 0 < (x : Adele).1 then 1 else -1
  have hε : ε ≠ 0 := by simp only [ε]; split_ifs <;> norm_num
  have hεabs : |ε| = 1 := by simp only [ε]; split_ifs <;> norm_num
  set q : ℚ := ε * q₀
  have hq0 : q ≠ 0 := mul_ne_zero hε hq₀pos.ne'
  have hx1 : (x : Adele).1 ≠ 0 := by
    intro h
    have := congrArg Prod.fst x.mul_inv
    simp only [Prod.fst_mul, h, zero_mul, Prod.fst_one] at this
    exact zero_ne_one this
  have hεx : ((ε : ℚ) : ℝ) * |(x : Adele).1| = (x : Adele).1 := by
    simp only [ε]
    split_ifs with h
    · rw [Rat.cast_one, one_mul, abs_of_pos h]
    · push Not at h
      rw [abs_of_neg (lt_of_le_of_ne h hx1), Rat.cast_neg, Rat.cast_one]; ring
  set r : ℝ := |(x : Adele).1| / (q₀ : ℝ)
  have hr : 0 < r := div_pos (abs_pos.mpr hx1) (by exact_mod_cast hq₀pos)
  -- the unit part
  obtain ⟨u, hu⟩ := (zhat_units_explicit ((x : Adele).2 * algebraMap ℚ FinAdele q⁻¹)).mpr fun ℓ ↦ by
    have h1 : ‖(x : Adele).2 ℓ * ((q⁻¹ : ℚ) : ℚ_[ℓ])‖ = 1 := by
      rw [norm_mul, Rat.cast_inv, norm_inv, ← hnorm ℓ]
      simp only [q, Rat.cast_mul, norm_mul]
      have hε1 : ‖((ε : ℚ) : ℚ_[ℓ])‖ = 1 := by
        simp only [ε]; split_ifs <;> simp
      rw [hε1, one_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (by exact_mod_cast hq₀pos.ne'))]
    exact ⟨PadicInt.mkUnits h1, rfl⟩
  refine ⟨Units.mk0 q hq0, r, u, hr, ?_⟩
  apply Units.ext
  rw [Units.val_mul, ratIdele_val, ideleInfFin_val hr.ne', hu]
  refine Prod.ext ?_ ?_
  · change (x : Adele).1 = ((q : ℚ) : ℝ) * r
    have hq₀R : (q₀ : ℝ) ≠ 0 := by exact_mod_cast hq₀pos.ne'
    have : ((ε * q₀ : ℚ) : ℝ) * (|(x : Adele).1| / (q₀ : ℝ)) = ((ε : ℚ) : ℝ) * |(x : Adele).1| := by
      rw [Rat.cast_mul]; field_simp
    rw [this, hεx]
  · ext ℓ
    change (x : Adele).2 ℓ = ((q : ℚ) : ℚ_[ℓ]) * ((x : Adele).2 ℓ * ((q⁻¹ : ℚ) : ℚ_[ℓ]))
    rw [Rat.cast_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hq0), mul_one]

/-- `Ẑ` is open in `𝔸_f` (proof helper). -/
theorem isOpen_zhat : IsOpen (Zhat : Set FinAdele) := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun p : Nat.Primes ↦ ℚ_[p])
    (A := fun p ↦ (PadicInt.subring p : Set ℚ_[p])) isOpen_padicSubring
  convert h using 1
  ext x
  exact mem_zhat

/-- `(1, 1) = 1` (proof helper). -/
theorem ideleInfFin_one_one : ideleInfFin 1 1 = 1 := by
  apply Units.ext
  rw [ideleInfFin_val one_ne_zero]
  rfl

/-- `(r, u)⁻¹ = (r⁻¹, u⁻¹)` (proof helper). -/
theorem ideleInfFin_inv {r : ℝ} (hr : r ≠ 0) (u : Zhatˣ) : (ideleInfFin r u)⁻¹ = ideleInfFin r⁻¹ u⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← ideleInfFin_mul hr (inv_ne_zero hr), mul_inv_cancel₀ hr, mul_inv_cancel, ideleInfFin_one_one]

/-- `(r, u) ↦ (r, u)` is continuous on `ℝ_{>0} × Ẑ^×` (proof helper). -/
theorem continuous_ideleInfFin :
    Continuous fun ru : Units.posSubgroup ℝ × Zhatˣ ↦ ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2 := by
  have hr : ∀ ru : Units.posSubgroup ℝ × Zhatˣ, ((ru.1 : ℝˣ) : ℝ) ≠ 0 := fun ru ↦ (ru.1 : ℝˣ).ne_zero
  rw [Units.continuous_iff]
  constructor
  · refine Continuous.congr (f := fun ru : Units.posSubgroup ℝ × Zhatˣ ↦
      (((ru.1 : ℝˣ) : ℝ), (((ru.2 : Zhatˣ) : Zhat) : FinAdele))) ?_ fun ru ↦ (ideleInfFin_val (hr ru) _).symm
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).prodMk
      ((continuous_subtype_val.comp Units.continuous_val).comp continuous_snd)
  · refine Continuous.congr (f := fun ru : Units.posSubgroup ℝ × Zhatˣ ↦
      ((((ru.1 : ℝˣ)⁻¹ : ℝˣ) : ℝ), ((((ru.2)⁻¹ : Zhatˣ) : Zhat) : FinAdele))) ?_ fun ru ↦ ?_
    · exact ((Units.continuous_coe_inv.comp continuous_subtype_val).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp Units.continuous_coe_inv).comp continuous_snd)
    · rw [ideleInfFin_inv (hr ru), ideleInfFin_val (inv_ne_zero (hr ru)), Units.val_inv_eq_inv_val]

/-- `(r, u) ↦ (r, u)` is an open map `ℝ_{>0} × Ẑ^× → 𝔸^×` (proof helper). -/
theorem isOpenMap_ideleInfFin :
    IsOpenMap fun ru : Units.posSubgroup ℝ × Zhatˣ ↦ ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2 := by
  set U0 : Set Idele := {x | 0 < (x : Adele).1 ∧ (x : Adele).2 ∈ Zhat ∧ ((x⁻¹ : Idele) : Adele).2 ∈ Zhat}
  have hU0 : IsOpen U0 :=
    (isOpen_lt continuous_const (continuous_fst.comp Units.continuous_val)).inter
      ((isOpen_zhat.preimage (continuous_snd.comp Units.continuous_val)).inter
        (isOpen_zhat.preimage (continuous_snd.comp Units.continuous_coe_inv)))
  have hmi : ∀ x : Idele, (x : Adele) * ((x⁻¹ : Idele) : Adele) = 1 := fun x ↦ x.mul_inv
  have hfst : ∀ x : Idele, (x : Adele).1 * ((x⁻¹ : Idele) : Adele).1 = 1 := fun x ↦ congrArg Prod.fst (hmi x)
  have hsnd : ∀ x : Idele, (x : Adele).2 * ((x⁻¹ : Idele) : Adele).2 = 1 := fun x ↦ congrArg Prod.snd (hmi x)
  let κr : U0 → ℝˣ := fun x ↦ Units.mk0 (x.1 : Adele).1 x.2.1.ne'
  have hκr : Continuous κr := by
    rw [Units.continuous_iff]
    refine ⟨(continuous_fst.comp Units.continuous_val).comp continuous_subtype_val, ?_⟩
    refine Continuous.congr (f := fun x : U0 ↦ ((x.1⁻¹ : Idele) : Adele).1)
      ((continuous_fst.comp Units.continuous_coe_inv).comp continuous_subtype_val) fun x ↦ ?_
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right (hfst x.1)
  let κu : U0 → Zhatˣ := fun x ↦ ⟨⟨(x.1 : Adele).2, x.2.2.1⟩, ⟨((x.1⁻¹ : Idele) : Adele).2, x.2.2.2⟩,
    Subtype.ext (hsnd x.1), Subtype.ext ((mul_comm _ _).trans (hsnd x.1))⟩
  have hκu : Continuous κu := by
    rw [Units.continuous_iff]
    exact ⟨((continuous_snd.comp Units.continuous_val).comp continuous_subtype_val).subtype_mk _,
      ((continuous_snd.comp Units.continuous_coe_inv).comp continuous_subtype_val).subtype_mk _⟩
  let κ : U0 → Units.posSubgroup ℝ × Zhatˣ := fun x ↦
    (⟨κr x, (Units.mem_posSubgroup _).mpr x.2.1⟩, κu x)
  have hκ : Continuous κ := (hκr.subtype_mk _).prodMk hκu
  intro A hA
  have hEq : (fun ru : Units.posSubgroup ℝ × Zhatˣ ↦ ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2) '' A =
      Subtype.val '' (κ ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨ru, hru, rfl⟩
      have hr : (0 : ℝ) < ((ru.1 : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).mp ru.1.2
      have hmem : ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2 ∈ U0 := by
        refine ⟨?_, ?_, ?_⟩
        · rw [ideleInfFin_val hr.ne']; exact hr
        · rw [ideleInfFin_val hr.ne']; exact (ru.2 : Zhat).2
        · rw [ideleInfFin_inv hr.ne', ideleInfFin_val (inv_ne_zero hr.ne')]; exact ((ru.2⁻¹ : Zhatˣ) : Zhat).2
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      have : κ ⟨_, hmem⟩ = ru := by
        refine Prod.ext (Subtype.ext (Units.ext ?_)) (Units.ext (Subtype.ext ?_))
        · change ((ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2 : Idele) : Adele).1 = ((ru.1 : ℝˣ) : ℝ)
          rw [ideleInfFin_val hr.ne']
        · change ((ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2 : Idele) : Adele).2 = ((ru.2 : Zhat) : FinAdele)
          rw [ideleInfFin_val hr.ne']
      rw [Set.mem_preimage, this]
      exact hru
    · rintro ⟨y, hy, rfl⟩
      refine ⟨κ y, hy, Units.ext ?_⟩
      change ((ideleInfFin (κr y : ℝ) (κu y) : Idele) : Adele) = _
      rw [ideleInfFin_val (κr y).ne_zero]
      rfl
  rw [hEq]
  exact hU0.isOpenMap_subtype_val _ (hA.preimage hκ)

/-- `𝔸^× ≅ ℚ^× × ℝ_{>0} × Ẑ^×`, `(q, r, u) ↦ q·(r, u)`, as topological groups (`ℚ^×` discrete); the norm of
`q·(r, u)` is `r`. -/
@[tf_id "I.adele.thm:idele-decomposition"]
theorem idele_decomposition :
    letI : TopologicalSpace ℚˣ := ⊥
    ∃ e : ContinuousMulEquiv (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) Idele,
      (∀ (q : ℚˣ) (r : Units.posSubgroup ℝ) (u : Zhatˣ),
        e (q, r, u) = ratIdele q * ideleInfFin ((r : ℝˣ) : ℝ) u) ∧
      ∀ x : Idele, ideleNorm x = (((e.symm x).2.1 : ℝˣ) : ℝ) := by
  let : TopologicalSpace ℚˣ := ⊥
  have : DiscreteTopology ℚˣ := ⟨rfl⟩
  have hr0 : ∀ r : Units.posSubgroup ℝ, ((r : ℝˣ) : ℝ) ≠ 0 := fun r ↦ (r : ℝˣ).ne_zero
  let E : ℚˣ × Units.posSubgroup ℝ × Zhatˣ →* Idele :=
    { toFun := fun x ↦ ratIdele x.1 * ideleInfFin ((x.2.1 : ℝˣ) : ℝ) x.2.2
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul, OneMemClass.coe_one, Units.val_one]
        exact ideleInfFin_one_one
      map_mul' := fun x y ↦ by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul, Units.val_mul]
        rw [ideleInfFin_mul (hr0 x.2.1) (hr0 y.2.1)]
        exact mul_mul_mul_comm _ _ _ _ }
  have hE : ∀ x, E x = ratIdele x.1 * ideleInfFin ((x.2.1 : ℝˣ) : ℝ) x.2.2 := fun _ ↦ rfl
  have hinj : Function.Injective E := by
    rw [injective_iff_map_eq_one]
    rintro ⟨q, r, u⟩ h
    have hr : (0 : ℝ) < ((r : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).mp r.2
    obtain ⟨h1, h2, h3⟩ := ratIdele_mul_ideleInfFin_eq_one hr h
    refine Prod.ext h1 (Prod.ext (Subtype.ext (Units.ext h2)) h3)
  have hsurj : Function.Surjective E := by
    intro x
    obtain ⟨q, r, u, hr, rfl⟩ := exists_ratIdele_mul_ideleInfFin x
    exact ⟨(q, ⟨Units.mk0 r hr.ne', (Units.mem_posSubgroup _).mpr hr⟩, u), rfl⟩
  let e0 : (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) ≃* Idele := MulEquiv.ofBijective E ⟨hinj, hsurj⟩
  have hcont : Continuous e0 :=
    (continuous_of_discreteTopology.comp continuous_fst).mul (continuous_ideleInfFin.comp continuous_snd)
  have hopen : IsOpenMap e0 := by
    intro A hA
    have : e0 '' A = ⋃ q : ℚˣ, (fun y ↦ ratIdele q * y) ''
        ((fun ru : Units.posSubgroup ℝ × Zhatˣ ↦ ideleInfFin ((ru.1 : ℝˣ) : ℝ) ru.2) '' (Prod.mk q ⁻¹' A)) := by
      ext x
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨⟨q, ru⟩, h, rfl⟩
        exact ⟨q, _, ⟨ru, h, rfl⟩, rfl⟩
      · rintro ⟨q, _, ⟨ru, h, rfl⟩, rfl⟩
        exact ⟨(q, ru), h, rfl⟩
    rw [this]
    exact isOpen_iUnion fun q ↦ isOpenMap_mul_left (ratIdele q) _
      (isOpenMap_ideleInfFin _ (hA.preimage (Continuous.prodMk_right q)))
  let h := Equiv.toHomeomorphOfContinuousOpen e0.toEquiv hcont hopen
  refine ⟨{ e0 with continuous_toFun := hcont, continuous_invFun := h.continuous_symm }, fun q r u ↦ rfl, ?_⟩
  intro x
  set y := e0.symm x
  have hx : x = e0 y := (e0.apply_symm_apply x).symm
  have hy : (0 : ℝ) < ((y.2.1 : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).mp y.2.1.2
  change ideleNorm x = ((y.2.1 : ℝˣ) : ℝ)
  rw [hx]
  change ideleNorm (ratIdele y.1 * ideleInfFin ((y.2.1 : ℝˣ) : ℝ) y.2.2) = _
  rw [map_mul, product_formula, one_mul, ideleNorm_ideleInfFin hy.ne', abs_of_pos hy]

/-- The idele norm is continuous, positive, and its non-trivial factors are finitely many (B-only companion of
`I.adele.def:idele-norm`). -/
@[tf_aux "I.adele.lem:idele-norm-spec"]
theorem ideleNorm_spec :
    Continuous ideleNorm ∧ (∀ x : Idele, 0 < ideleNorm x) ∧
      ∀ x : Idele, {p : Nat.Primes | Local.normAbs ℚ_[p] ((x : Adele).2 p) ≠ 1}.Finite := by
  let : TopologicalSpace ℚˣ := ⊥
  obtain ⟨e, -, hnorm⟩ := idele_decomposition
  have hfun : (ideleNorm : Idele → ℝ) = fun x ↦ (((e.symm x).2.1 : ℝˣ) : ℝ) := funext hnorm
  refine ⟨?_, fun x ↦ ?_, fun x ↦ idele_normAbs_eventually_one x⟩
  · rw [hfun]
    exact Units.continuous_val.comp (continuous_subtype_val.comp
      (continuous_fst.comp (continuous_snd.comp e.symm.continuous)))
  · rw [hnorm]; exact (Units.mem_posSubgroup _).mp (e.symm x).2.1.2

/-- The norm-one idele class group `C = 𝔸^1/ℚ^×` (B-only plumbing). -/
@[tf_aux "I.adele.def:norm-one-class-group"]
abbrev NormOneClassGroup : Type := ideleNormOne ⧸ ratIdeles.subgroupOf ideleNormOne

/-- `(1, u) ∈ 𝔸^1` for `u ∈ Ẑ^×` (proof plumbing for `zhatToNormOneClass`). -/
theorem ideleInfFin_one_mem (u : Zhatˣ) : ideleInfFin 1 u ∈ ideleNormOne := by
  have hc : ((ideleInfFin 1 u : Idele) : Adele) = (1, ((u : Zhat) : FinAdele)) := by
    simp only [ideleInfFin, one_ne_zero, dite_false]
    rfl
  have hv : ∀ p : Nat.Primes, Local.normAbs ℚ_[p] (((ideleInfFin 1 u : Idele) : Adele).2 p) = 1 := by
    intro p
    have h1 := mem_zhat.mp (u : Zhat).2 p
    have h2 := mem_zhat.mp ((u⁻¹ : Zhatˣ) : Zhat).2 p
    have hmul : ((u : Zhat) : FinAdele) p * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) p = 1 := by
      have := congrArg (fun z : Zhat ↦ (z : FinAdele) p) u.mul_inv
      simpa only [Subring.coe_mul, Subring.coe_one, RestrictedProduct.mul_apply,
        RestrictedProduct.one_apply] using this
    let v : ℤ_[p]ˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext hmul, Subtype.ext ((mul_comm _ _).trans hmul)⟩
    rw [hc]
    exact Local.normAbs_padicInt_unit v
  rw [ideleNormOne, MonoidHom.mem_ker]
  change ideleNormFun _ = 1
  rw [ideleNormFun, finprod_congr hv, finprod_one, hc, abs_one, one_mul]

/-- `Ẑ^× → 𝔸^1/ℚ^×`, `u ↦ (1, u)ℚ^×` (B-only plumbing). -/
@[tf_aux "I.adele.def:zhat-to-norm-one-class"]
noncomputable def zhatToNormOneClass (u : Zhatˣ) : NormOneClassGroup :=
  (QuotientGroup.mk ⟨ideleInfFin 1 u, ideleInfFin_one_mem u⟩ : NormOneClassGroup)

/-- `Ẑ^× → 𝔸^1/ℚ^×`, `u ↦ (1, u)ℚ^×`, is an isomorphism of topological groups; in particular `𝔸^1/ℚ^×` is
compact. -/
@[tf_id "I.adele.thm:norm-one-quotient"]
theorem norm_one_quotient :
    (∃ e : ContinuousMulEquiv Zhatˣ NormOneClassGroup,
      ∀ u : Zhatˣ, e u = zhatToNormOneClass u) ∧
      CompactSpace NormOneClassGroup := by
  let : TopologicalSpace ℚˣ := ⊥
  obtain ⟨e, he, hnorm⟩ := idele_decomposition
  let N : Subgroup ideleNormOne := ratIdeles.subgroupOf ideleNormOne
  -- `Θ : 𝔸^1 → Ẑ^×`, the `Ẑ^×`-coordinate
  let Θ : ideleNormOne →* Zhatˣ :=
    (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (e.symm.toMulEquiv.toMonoidHom.comp ideleNormOne.subtype))
  have hΘ : ∀ x : ideleNormOne, Θ x = (e.symm x).2.2 := fun _ ↦ rfl
  have hΘc : Continuous Θ :=
    continuous_snd.comp (continuous_snd.comp (e.symm.continuous.comp continuous_subtype_val))
  have he1 : ∀ u : Zhatˣ, e.symm (ideleInfFin 1 u) = (1, 1, u) := fun u ↦ by
    rw [e.symm_apply_eq, he, map_one, one_mul]; rfl
  have hle : N ≤ Θ.ker := by
    rintro ⟨x, hx1⟩ hx
    obtain ⟨q, hq⟩ := Subgroup.mem_subgroupOf.mp hx
    rw [MonoidHom.mem_ker, hΘ]
    change (e.symm x).2.2 = 1
    have hq' : ratIdele q = x := hq
    have h2 : e (q, 1, 1) = ratIdele q := by
      rw [he]
      change ratIdele q * ideleInfFin 1 1 = _
      rw [ideleInfFin_one_one, mul_one]
    rw [← hq', ← h2, ContinuousMulEquiv.symm_apply_apply]
  let Θbar : NormOneClassGroup →* Zhatˣ := QuotientGroup.lift N Θ hle
  have hΘbarc : Continuous Θbar := continuous_coinduced_dom.mpr hΘc
  -- `φ : Ẑ^× → C`, `u ↦ (1, u)ℚ^×`
  have h1u : ∀ u : Zhatˣ, ideleInfFin 1 u = ideleInfFin ((1 : Units.posSubgroup ℝ) : ℝˣ) u := fun u ↦ rfl
  have hcont1 : Continuous fun u : Zhatˣ ↦ ideleInfFin 1 u :=
    continuous_ideleInfFin.comp
      (continuous_const.prodMk continuous_id : Continuous fun u : Zhatˣ ↦ ((1 : Units.posSubgroup ℝ), u))
  let φ : Zhatˣ →* NormOneClassGroup :=
    { toFun := zhatToNormOneClass
      map_one' := by
        change (QuotientGroup.mk _ : NormOneClassGroup) = 1
        rw [← QuotientGroup.mk_one]
        congr 1
        exact Subtype.ext ideleInfFin_one_one
      map_mul' := fun u v ↦ by
        change (QuotientGroup.mk _ : NormOneClassGroup) = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        change ideleInfFin 1 (u * v) = ideleInfFin 1 u * ideleInfFin 1 v
        rw [← ideleInfFin_mul one_ne_zero one_ne_zero, one_mul] }
  have hφc : Continuous φ :=
    continuous_quot_mk.comp (hcont1.subtype_mk _)
  have hleft : ∀ u, Θbar (φ u) = u := fun u ↦ by
    change Θ ⟨ideleInfFin 1 u, ideleInfFin_one_mem u⟩ = u
    rw [hΘ]
    change (e.symm (ideleInfFin 1 u)).2.2 = u
    rw [he1]
  have hright : ∀ c, φ (Θbar c) = c := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H x =>
      change zhatToNormOneClass (Θ x) = QuotientGroup.mk x
      rw [hΘ]
      set y := e.symm x
      have hr : y.2.1 = 1 := by
        have h := hnorm x
        rw [show ideleNorm x = 1 from x.2] at h
        exact Subtype.ext (Units.ext h.symm)
      have hx : (x : Idele) = ratIdele y.1 * ideleInfFin 1 y.2.2 := by
        have := (e.apply_symm_apply (x : Idele)).symm
        rw [show e.symm x = (y.1, 1, y.2.2) from Prod.ext rfl (Prod.ext hr rfl), he] at this
        exact this
      refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ⟨y.1, ?_⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hx]
      change _ = (ideleInfFin 1 y.2.2)⁻¹ * (ratIdele y.1 * ideleInfFin 1 y.2.2)
      rw [mul_left_comm, inv_mul_cancel, mul_one]
  let E : Zhatˣ ≃* NormOneClassGroup :=
    { φ with invFun := Θbar, left_inv := hleft, right_inv := hright }
  let E' : ContinuousMulEquiv Zhatˣ NormOneClassGroup :=
    { E with continuous_toFun := hφc, continuous_invFun := hΘbarc }
  exact ⟨⟨E', fun u ↦ rfl⟩, E'.toHomeomorph.compactSpace⟩

/-- `𝔸^×` is locally compact, Hausdorff and second countable. -/
@[tf_id "I.adele.thm:ideles-second-countable"]
theorem ideles_locallyCompact_secondCountable :
    LocallyCompactSpace Idele ∧ T2Space Idele ∧ SecondCountableTopology Idele := by
  let : TopologicalSpace ℚˣ := ⊥
  have : DiscreteTopology ℚˣ := ⟨rfl⟩
  obtain ⟨e, -, -⟩ := idele_decomposition
  have hR : Topology.IsOpenEmbedding (fun u : ℝˣ ↦ (u : ℝ)) :=
    ⟨Units.isEmbedding_val₀, by
      have : Set.range (fun u : ℝˣ ↦ (u : ℝ)) = {0}ᶜ := by
        ext x; exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
      rw [this]; exact isOpen_compl_singleton⟩
  have : LocallyCompactSpace ℝˣ := hR.locallyCompactSpace
  have hP : IsOpen (Units.posSubgroup ℝ : Set ℝˣ) := by
    have : (Units.posSubgroup ℝ : Set ℝˣ) = (fun u : ℝˣ ↦ (u : ℝ)) ⁻¹' Set.Ioi 0 := by
      ext u; exact Units.mem_posSubgroup u
    rw [this]; exact isOpen_Ioi.preimage Units.continuous_val
  have : LocallyCompactSpace (Units.posSubgroup ℝ) := hP.locallyCompactSpace
  have : LocallyCompactSpace (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) := inferInstance
  have : SecondCountableTopology Adeleᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨e.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace, inferInstance,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

/-! ### `ℤ_p^×` and the unit box of `𝔸^×` -/

/-- `ℤ_p^×` is open in `ℚ_p^×` (proof helper for `ideleHaar`). -/
theorem isOpen_padicUnits (p : Nat.Primes) :
    IsOpen ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ) := by
  have hB : IsOpen (Metric.closedBall (0 : ℚ_[p]) 1) := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have : ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ) =
      (Units.val ⁻¹' Metric.closedBall 0 1) ∩ ((fun u : ℚ_[p]ˣ ↦ ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) ⁻¹'
        Metric.closedBall 0 1) := by
    ext u
    simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right, Units.val_inv_eq_inv_val]
    exact Iff.rfl
  rw [this]
  exact (hB.preimage Units.continuous_val).inter (hB.preimage Units.continuous_coe_inv)

/-- `ℤ_p^×` is compact (B-only plumbing for `I.adele.def:idele-haar`). -/
@[tf_aux "I.adele.lem:padic-units-compact"]
theorem padicUnits_compactSpace (p : Nat.Primes) :
    CompactSpace ((Submonoid.ofClass (PadicInt.subring p)).units) := by
  refine isCompact_iff_compactSpace.mp ?_
  have : ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ) =
      Units.val ⁻¹' Metric.sphere 0 1 := by
    ext u
    simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_preimage, mem_sphere_iff_norm, sub_zero,
      Units.val_inv_eq_inv_val]
    change ‖(u : ℚ_[p])‖ ≤ 1 ∧ ‖(u : ℚ_[p])⁻¹‖ ≤ 1 ↔ _
    have h0 : 0 < ‖(u : ℚ_[p])‖ := norm_pos_iff.mpr u.ne_zero
    rw [norm_inv, inv_le_one₀ h0]
    exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩
  rw [this, Units.isEmbedding_val₀.isCompact_preimage_iff]
  · exact isCompact_sphere 0 1
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hx; exact zero_ne_one hx
    exact ⟨Units.mk0 x hx0, rfl⟩

/-- `ℤ_p^×` is compact, as an instance (B-only plumbing). -/
@[tf_aux "I.adele.lem:padic-units-compact-instance"]
instance padicUnits_compactSpace_inst (p : Nat.Primes) :
    CompactSpace ((Submonoid.ofClass (PadicInt.subring p)).units) :=
  padicUnits_compactSpace p

/-- `ideleEquiv` is a homeomorphism (for the units topology on `𝔸^×` and the restricted-product topology), with the
componentwise formula (B-only). -/
@[tf_aux "I.adele.lem:ideles-restricted-product"]
theorem ideles_restricted_product :
    IsHomeomorph ideleEquiv ∧ ∀ x : Idele, (((ideleEquiv x).1 : ℝ) = (x : Adele).1 ∧
      ∀ p : Nat.Primes, (((ideleEquiv x).2 p : ℚ_[p]ˣ) : ℚ_[p]) = (x : Adele).2 p) := by
  refine ⟨?_, fun x ↦ ⟨rfl, fun p ↦ rfl⟩⟩
  set T := ℝˣ × Πʳ (p : Nat.Primes), [ℚ_[p]ˣ, (Submonoid.ofClass (PadicInt.subring p)).units]
  have : Fact (∀ p : Nat.Primes, IsOpen ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ)) :=
    ⟨isOpen_padicUnits⟩
  have hR : Topology.IsOpenEmbedding (fun u : ℝˣ ↦ (u : ℝ)) :=
    ⟨Units.isEmbedding_val₀, by
      have : Set.range (fun u : ℝˣ ↦ (u : ℝ)) = {0}ᶜ := by
        ext x; exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
      rw [this]; exact isOpen_compl_singleton⟩
  have : LocallyCompactSpace ℝˣ := hR.locallyCompactSpace
  have : SecondCountableTopology ℝˣ := hR.isEmbedding.secondCountableTopology
  have : ∀ p : Nat.Primes, SecondCountableTopology ℚ_[p]ˣ := fun p ↦
    (Topology.IsOpenEmbedding.isEmbedding (f := fun u : ℚ_[p]ˣ ↦ (u : ℚ_[p]))
      ⟨Units.isEmbedding_val₀, by
        have : Set.range (fun u : ℚ_[p]ˣ ↦ (u : ℚ_[p])) = {0}ᶜ := by
          ext x; exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
        rw [this]; exact isOpen_compl_singleton⟩).secondCountableTopology
  have : SecondCountableTopology (Πʳ (p : Nat.Primes), [ℚ_[p]ˣ, (Submonoid.ofClass (PadicInt.subring p)).units]) :=
    resProd_secondCountableTopology _ _ isOpen_padicUnits
  have : LocallyCompactSpace T := inferInstance
  have : SigmaCompactSpace T := inferInstance
  have : LocallyCompactSpace Idele := ideles_locallyCompact_secondCountable.1
  have : BaireSpace Idele := BaireSpace.of_t2Space_locallyCompactSpace
  -- the inverse map is continuous
  let g : T →* Idele := ideleEquiv.symm.toMonoidHom
  have hmaps : ∀ p : Nat.Primes, Set.MapsTo (fun u : ℚ_[p]ˣ ↦ (u : ℚ_[p]))
      ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ) (PadicInt.subring p : Set ℚ_[p]) :=
    fun p u hu ↦ hu.1
  have hmaps' : ∀ p : Nat.Primes, Set.MapsTo (fun u : ℚ_[p]ˣ ↦ ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))
      ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ) (PadicInt.subring p : Set ℚ_[p]) :=
    fun p u hu ↦ hu.2
  have hW := mapAlong_continuous (A₁ := fun p : Nat.Primes ↦ ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ))
    (A₂ := fun p : Nat.Primes ↦ (PadicInt.subring p : Set ℚ_[p])) (𝓕₁ := cofinite) (𝓕₂ := cofinite) (fun p : Nat.Primes ↦ ℚ_[p]ˣ) (fun p : Nat.Primes ↦ ℚ_[p]) id tendsto_id
    (fun p (u : ℚ_[p]ˣ) ↦ (u : ℚ_[p])) (Eventually.of_forall hmaps) fun p ↦ Units.continuous_val
  have hW' := mapAlong_continuous (A₁ := fun p : Nat.Primes ↦ ((Submonoid.ofClass (PadicInt.subring p)).units : Set ℚ_[p]ˣ))
    (A₂ := fun p : Nat.Primes ↦ (PadicInt.subring p : Set ℚ_[p])) (𝓕₁ := cofinite) (𝓕₂ := cofinite) (fun p : Nat.Primes ↦ ℚ_[p]ˣ) (fun p : Nat.Primes ↦ ℚ_[p]) id tendsto_id
    (fun p (u : ℚ_[p]ˣ) ↦ ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) (Eventually.of_forall hmaps') fun p ↦ Units.continuous_coe_inv
  have hg : Continuous g := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp continuous_fst).prodMk (hW.comp continuous_snd)
    · exact (Units.continuous_coe_inv.comp continuous_fst).prodMk (hW'.comp continuous_snd)
  have hopen : IsOpenMap g := g.isOpenMap_of_sigmaCompact ideleEquiv.symm.surjective hg
  exact (ideleEquiv.symm.toEquiv.toHomeomorphOfContinuousOpen hg hopen).symm.isHomeomorph

/-- The box `{x ∈ 𝔸^× : x_∞ ∈ [1, e), x_p ∈ ℤ_p^× for all p}` (`= [1, e) × Ẑ^×`) (B-only plumbing). -/
@[tf_aux "I.adele.def:idele-unit-box"]
def ideleUnitBox : Set Idele :=
  {x | (x : Adele).1 ∈ Set.Ico 1 (Real.exp 1) ∧
    ∀ p : Nat.Primes, ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = (x : Adele).2 p}

/-! ### `Ẑ^×`, its reductions and characters -/

/-- The component `Ẑ → ℤ_p`, `x ↦ x_p` (proof plumbing for `zhatReduction`). -/
@[tf_aux "I.adele.def:zhat-to-padic-int"]
noncomputable def zhatToPadicInt (p : Nat.Primes) : Zhat →+* ℤ_[p] where
  toFun x := ⟨(x : FinAdele) p, mem_zhat.mp x.2 p⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `∏_{p ∣ N} p^{v_p(N)} = N` (proof plumbing for `zhatReduction`). -/
theorem prod_primeFactors_pow_factorization (N : ℕ+) :
    ∏ p : (N : ℕ).primeFactors, (p : ℕ) ^ (N : ℕ).factorization p = N := by
  rw [Finset.prod_coe_sort (N : ℕ).primeFactors (fun p ↦ p ^ (N : ℕ).factorization p)]
  exact Nat.prod_factorization_pow_eq_self N.ne_zero

/-- The prime powers `p^{v_p(N)}`, `p ∣ N`, are pairwise coprime (proof plumbing for `zhatReduction`). -/
theorem pairwise_coprime_primeFactors_pow (N : ℕ+) :
    Pairwise (Function.onFun Nat.Coprime fun p : (N : ℕ).primeFactors ↦ (p : ℕ) ^ (N : ℕ).factorization p) := by
  intro p q hpq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).2 fun h ↦ hpq (Subtype.ext h))

/-- The reduction `red_N : Ẑ → ℤ/N` (`N ≥ 1`): the ring hom with kernel `NẐ` extending `ℤ → ℤ/N`, built by the
Chinese remainder theorem from the reductions `ℤ_p → ℤ/p^{v_p(N)}`, `p ∣ N` (B-only plumbing for
`I.adele.thm:zhat-characters-finite-order`). -/
@[tf_aux "I.adele.def:zhat-reduction"]
noncomputable def zhatReduction (N : ℕ+) : Zhat →+* ZMod N :=
  (ZMod.ringEquivCongr (prod_primeFactors_pow_factorization N)).toRingHom.comp
    ((ZMod.prodEquivPi _ (pairwise_coprime_primeFactors_pow N)).symm.toRingHom.comp
      (RingHom.pi fun p : (N : ℕ).primeFactors ↦
        haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        (PadicInt.toZModPow ((N : ℕ).factorization p)).comp
          (zhatToPadicInt ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)))

/-- No small subgroups in `ℂ` (proof helper): if `‖z^(2^k) - 1‖ < 1/2` for all `k`, then `z = 1`. -/
theorem eq_one_of_forall_pow_two_pow_near_one (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hfac : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * ((z ^ (2 ^ k) - 1) + 2) := by
        rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖(z ^ (2 ^ k) - 1) + 2‖ := by
        have := norm_sub_norm_le (2 : ℂ) (-(z ^ (2 ^ k) - 1))
        rw [norm_neg, sub_neg_eq_add, add_comm] at this
        have h22 : ‖(2 : ℂ)‖ = 2 := by simp
        linarith [h k]
      rw [hfac, norm_mul, pow_succ]
      calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
        _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖(z ^ (2 ^ k) - 1) + 2‖ :=
          mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).eventually_ge_atTop
    (1 / 2 / ‖z - 1‖) |>.exists
  have := (key k).trans_lt (h k)
  rw [div_le_iff₀ hpos] at hk
  linarith

/-- An element of `Ẑ` divisible by every `N ≥ 1` vanishes (proof helper). -/
theorem zhat_eq_zero_of_forall_dvd (x : Zhat)
    (h : ∀ N : ℕ+, ∃ y : Zhat, x = ((N : ℕ) : Zhat) * y) : x = 0 := by
  apply Subtype.ext
  ext p
  change (x : FinAdele) p = 0
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  have hp : (1 : ℝ) < p.1 := mod_cast p.2.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  obtain ⟨y, hy⟩ := h ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  have hxp : (x : FinAdele) p = ((p.1 : ℚ_[p]) ^ k) * (y : FinAdele) p := by
    have := congrArg (fun z : Zhat ↦ (z : FinAdele) p) hy
    simp only [Subring.coe_mul, Subring.coe_natCast, RestrictedProduct.mul_apply,
      finAdele_natCast_apply] at this
    rw [this, PNat.mk_coe, Nat.cast_pow]
  have hy1 : ‖(y : FinAdele) p‖ ≤ 1 := by
    have := mem_zhat.mp y.2 p
    simpa [PadicInt.mem_subring_iff] using this
  rw [hxp, norm_mul, norm_pow, Padic.norm_p]
  calc (p.1 : ℝ)⁻¹ ^ k * ‖(y : FinAdele) p‖ ≤ (p.1 : ℝ)⁻¹ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hy1 (by positivity)
    _ ≤ ε := by rw [mul_one]; exact hk.le

/-- The ideals `NẐ` form a neighbourhood base of `0` in `Ẑ` (proof helper; compactness of `Ẑ`). -/
theorem zhat_exists_dvd_subset (O : Set Zhat) (hO : O ∈ 𝓝 0) :
    ∃ N : ℕ+, ∀ y : Zhat, ((N : ℕ) : Zhat) * y ∈ O := by
  obtain ⟨U, hUO, hUo, hU0⟩ := mem_nhds_iff.mp hO
  let t : ℕ+ → Set Zhat := fun N ↦ Set.range fun y : Zhat ↦ ((N : ℕ) : Zhat) * y
  have htc : ∀ N, IsClosed (t N) := fun N ↦
    (isCompact_range (continuous_const.mul continuous_id)).isClosed
  have hst : (Uᶜ ∩ ⋂ N, t N) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hxU, hxt⟩ ↦ hxU ?_
    have hx0 : x = 0 := zhat_eq_zero_of_forall_dvd x fun N ↦ by
      obtain ⟨y, hy⟩ := Set.mem_iInter.mp hxt N
      exact ⟨y, hy.symm⟩
    exact hx0 ▸ hU0
  have hdt : Directed (· ⊇ ·) t := fun N M ↦ ⟨N * M, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hUo.isClosed_compl.isCompact.elim_directed_family_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst) hdt
    refine ⟨N, fun y ↦ hUO ?_⟩
    by_contra h
    have hm : ((N : ℕ) : Zhat) * y ∈ Uᶜ ∩ t N := ⟨h, y, rfl⟩
    exact Set.disjoint_left.mp hN hm.1 hm.2
  · rintro _ ⟨y, rfl⟩
    exact ⟨(M : ℕ) * y, by simp only [PNat.mul_coe, Nat.cast_mul]; ring⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(N : ℕ) * y, by simp only [PNat.mul_coe, Nat.cast_mul]; ring⟩

/-- `red_N` has kernel `NẐ` and extends `ℤ → ℤ/N` (B-only companion of `I.adele.def:zhat-reduction`). -/
@[tf_aux "I.adele.lem:zhat-reduction-spec"]
theorem zhatReduction_spec (N : ℕ+) :
    RingHom.ker (zhatReduction N) = Ideal.span {(N : Zhat)} ∧ ∀ n : ℤ, zhatReduction N n = n := by
  refine ⟨?_, fun n ↦ map_intCast _ n⟩
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hx
    simp only [zhatReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ (RingEquiv.injective _)] at hx
    rw [funext_iff] at hx
    have hdiv : ∀ p : Nat.Primes, ∃ z : ℤ_[p], (x : FinAdele) p = (N : ℚ_[p]) * z := by
      intro p
      set v := (N : ℕ).factorization p
      have hw : ∃ w : ℤ_[p], zhatToPadicInt p x = (p : ℤ_[p]) ^ v * w := by
        by_cases hp : (p : ℕ) ∈ (N : ℕ).primeFactors
        · have h1 := hx ⟨p, hp⟩
          have hk : zhatToPadicInt p x ∈ RingHom.ker (PadicInt.toZModPow (p := p) v) := h1
          rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
          exact hk
        · have hv : v = 0 := Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
          exact ⟨zhatToPadicInt p x, by rw [hv, pow_zero, one_mul]⟩
      obtain ⟨w, hw⟩ := hw
      have hm : ‖(((N : ℕ) / (p : ℕ) ^ v : ℕ) : ℤ_[p])‖ = 1 :=
        PadicInt.norm_natCast_eq_one_iff.mpr
          ((Nat.Prime.coprime_iff_not_dvd p.2).mpr (Nat.not_dvd_ordCompl p.2 N.ne_zero))
      set m : ℤ_[p]ˣ := (PadicInt.isUnit_iff.mpr hm).unit with hmdef
      have hmv : ((m : ℤ_[p]) : ℚ_[p]) = (((N : ℕ) / (p : ℕ) ^ v : ℕ) : ℚ_[p]) := by
        rw [hmdef, IsUnit.unit_spec, PadicInt.coe_natCast]
      refine ⟨w * ↑m⁻¹, ?_⟩
      have hN : (N : ℚ_[p]) = (p : ℚ_[p]) ^ v * (((N : ℕ) / (p : ℕ) ^ v : ℕ) : ℚ_[p]) := by
        exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self (N : ℕ) p).symm
      have hinv : ((m : ℤ_[p]) : ℚ_[p]) * ((↑m⁻¹ : ℤ_[p]) : ℚ_[p]) = 1 := by
        rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
      have hxp : (x : FinAdele) p = ((zhatToPadicInt p x : ℤ_[p]) : ℚ_[p]) := rfl
      rw [hxp, hw, hN, ← hmv, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
      linear_combination (-((p : ℚ_[p]) ^ v * (w : ℚ_[p]))) * hinv
    choose z hz using hdiv
    let y : FinAdele := ⟨fun p ↦ ((z p : ℤ_[p]) : ℚ_[p]), Filter.Eventually.of_forall fun p ↦
      (z p).2⟩
    refine ⟨⟨y, mem_zhat.mpr fun p ↦ (z p).2⟩, ?_⟩
    apply Subtype.ext
    ext p
    simp only [Subring.coe_mul, Subring.coe_natCast, RestrictedProduct.mul_apply, finAdele_natCast_apply]
    rw [hz p, mul_comm]
    rfl
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, mul_zero]

/-- `red_N x` depends only on the components `x_p`, `p ∣ N` (proof helper). -/
theorem zhatReduction_congr (N : ℕ+) (x y : Zhat)
    (h : ∀ p : Nat.Primes, (p : ℕ) ∣ N → (x : FinAdele) p = (y : FinAdele) p) :
    zhatReduction N x = zhatReduction N y := by
  simp only [zhatReduction, RingHom.comp_apply]
  congr 2
  funext q
  simp only [RingHom.pi_apply, RingHom.comp_apply]
  congr 1
  exact Subtype.ext (h _ (Nat.dvd_of_mem_primeFactors q.2))

/-- The subgroups `U_N = ker(red_N) ∩ Ẑ^×` form a neighbourhood base of `1` in `Ẑ^×` (proof helper). -/
theorem zhatUnits_exists_ker_subset (W : Set Zhatˣ) (hW : W ∈ 𝓝 1) :
    ∃ N : ℕ+, ∀ u : Zhatˣ, zhatReduction N (u : Zhat) = 1 → u ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨t, ht, htW⟩ := hW
  let g : Zhat × Zhat → Zhat × Zhatᵐᵒᵖ := fun ab ↦ (1 + ab.1, MulOpposite.op (1 + ab.2))
  have hg : Continuous g :=
    (continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))
  have hg0 : g (0, 0) = Units.embedProduct Zhat 1 := by simp [g]
  have hgt : g ⁻¹' t ∈ 𝓝 ((0 : Zhat), (0 : Zhat)) := hg.continuousAt.preimage_mem_nhds (hg0 ▸ ht)
  obtain ⟨O1, hO1, O2, hO2, hO⟩ := mem_nhds_prod_iff.mp hgt
  obtain ⟨N, hN⟩ := zhat_exists_dvd_subset (O1 ∩ O2) (Filter.inter_mem hO1 hO2)
  refine ⟨N, fun u hu ↦ htW ?_⟩
  have hk : (u : Zhat) - 1 ∈ RingHom.ker (zhatReduction N) := by
    rw [RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  rw [(zhatReduction_spec N).1, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  have h1 : (u : Zhat) - 1 ∈ O1 := by rw [← hy, mul_comm]; exact (hN y).1
  have h2 : ((u⁻¹ : Zhatˣ) : Zhat) - 1 ∈ O2 := by
    have : ((u⁻¹ : Zhatˣ) : Zhat) - 1 = ((N : ℕ) : Zhat) * (-(((u⁻¹ : Zhatˣ) : Zhat) * y)) := by
      have hu1 : ((u⁻¹ : Zhatˣ) : Zhat) * (u : Zhat) = 1 := u.inv_mul
      linear_combination (((u⁻¹ : Zhatˣ) : Zhat)) * hy + hu1
    rw [this]; exact (hN _).2
  have := hO (Set.mk_mem_prod h1 h2)
  simpa [g] using this

/-- `red_N : Ẑ^× → (ℤ/N)^×` is surjective (proof helper). -/
theorem zhatReduction_units_surjective (N : ℕ+) :
    Function.Surjective (Units.map (zhatReduction N).toMonoidHom) := by
  intro a
  classical
  set m : ℕ := (a : ZMod N).val
  have hm : Nat.Coprime m N := ZMod.val_coe_unit_coprime a
  let x : FinAdele := ⟨fun p ↦ if (p : ℕ) ∣ N then (m : ℚ_[p]) else 1, Filter.Eventually.of_forall fun p ↦ by
    show (if (p : ℕ) ∣ N then (m : ℚ_[p]) else 1) ∈ _
    split_ifs
    · exact (m : ℤ_[p]).2
    · exact (1 : ℤ_[p]).2⟩
  obtain ⟨u, hu⟩ := (zhat_units_explicit x).mpr fun p ↦ by
    by_cases hp : (p : ℕ) ∣ N
    · have h1 : ‖(m : ℤ_[p])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr
        (hm.coprime_dvd_right hp).symm
      refine ⟨(PadicInt.isUnit_iff.mpr h1).unit, ?_⟩
      rw [IsUnit.unit_spec, PadicInt.coe_natCast]
      change _ = if (p : ℕ) ∣ N then (m : ℚ_[p]) else 1
      rw [ite_eq_left hp]
    · refine ⟨1, ?_⟩
      change _ = if (p : ℕ) ∣ N then (m : ℚ_[p]) else 1
      rw [ite_eq_right hp]; rfl
  refine ⟨u, Units.ext ?_⟩
  change zhatReduction N (u : Zhat) = (a : ZMod N)
  rw [zhatReduction_congr N (u : Zhat) (m : Zhat) fun p hp ↦ ?_, map_natCast, ZMod.natCast_zmod_val]
  rw [hu, Subring.coe_natCast, finAdele_natCast_apply]
  change (if (p : ℕ) ∣ N then (m : ℚ_[p]) else 1) = _
  rw [ite_eq_left hp]

/-- Every continuous hom `χ : Ẑ^× → ℂ^×` is `χ_N ∘ red_N` for some `N ≥ 1` and a Dirichlet character `χ_N` mod `N`;
in particular `χ` has finite order. -/
@[tf_id "I.adele.thm:zhat-characters-finite-order"]
theorem zhat_characters_finite_order (χ : ContinuousMonoidHom Zhatˣ ℂˣ) :
    (∃ (N : ℕ+) (χN : DirichletCharacter ℂ N), ∀ u : Zhatˣ,
        ((χ u : ℂˣ) : ℂ) = χN (zhatReduction N (u : Zhat))) ∧
      ∃ n : ℕ, 1 ≤ n ∧ ∀ u : Zhatˣ, χ u ^ n = 1 := by
  -- an open neighbourhood of `1` in `ℂ^×` without non-trivial subgroups
  let V : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hVo : IsOpen V := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const))
    continuous_const
  have hW : χ ⁻¹' V ∈ 𝓝 1 :=
    χ.continuous.continuousAt.preimage_mem_nhds (hVo.mem_nhds (by simp [V]))
  obtain ⟨N, hN⟩ := zhatUnits_exists_ker_subset _ hW
  let f0 : Zhatˣ →* (ZMod N)ˣ := Units.map (zhatReduction N).toMonoidHom
  have hker : f0.ker ≤ (χ : Zhatˣ →* ℂˣ).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hred : ∀ k : ℕ, zhatReduction N ((u ^ (2 ^ k) : Zhatˣ) : Zhat) = 1 := fun k ↦ by
      have : f0 (u ^ (2 ^ k)) = 1 := by rw [map_pow, hu, one_pow]
      exact congrArg Units.val this
    apply Units.ext
    refine eq_one_of_forall_pow_two_pow_near_one _ fun k ↦ ?_
    have := hN _ (hred k)
    simpa [V] using this
  have hsurj := zhatReduction_units_surjective N
  let sec := Function.surjInv hsurj
  have hsec : Function.RightInverse sec f0 := Function.rightInverse_surjInv hsurj
  let g : (ZMod N)ˣ →* ℂˣ := MonoidHom.liftOfRightInverse f0 sec hsec ⟨χ, hker⟩
  have hg : ∀ u, g (f0 u) = χ u := fun u ↦
    MonoidHom.liftOfRightInverse_comp_apply f0 sec hsec ⟨(χ : Zhatˣ →* ℂˣ), hker⟩ u
  refine ⟨⟨N, MulChar.ofUnitHom g, fun u ↦ ?_⟩, ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, fun u ↦ ?_⟩⟩
  · have : zhatReduction N (u : Zhat) = ((f0 u : (ZMod N)ˣ) : ZMod N) := rfl
    rw [this, MulChar.ofUnitHom_coe, hg]
  · rw [← hg, ← map_pow, pow_card_eq_one, map_one]

/-- The kernel `NẐ` of `red_N` is open in `Ẑ` (proof helper). -/
theorem isOpen_ker_zhatReduction (N : ℕ+) : IsOpen (RingHom.ker (zhatReduction N) : Set Zhat) := by
  let K : AddSubgroup Zhat := (RingHom.ker (zhatReduction N)).toAddSubgroup
  change IsOpen (K : Set Zhat)
  set U : Set Zhat := ⋂ p : (N : ℕ).primeFactors,
    {x : Zhat | ‖(x : FinAdele) ⟨p, Nat.prime_of_mem_primeFactors p.2⟩‖ ≤
      ((p : ℕ) : ℝ) ^ (-(((N : ℕ).factorization p : ℕ) : ℤ))}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun p ↦ ?_
    have hp : ((p : ℕ) : ℝ) ^ (-(((N : ℕ).factorization p : ℕ) : ℤ)) ≠ 0 := by
      have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors p.2).pos
      positivity
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have := (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[(p : ℕ)]) hp).preimage
      ((RestrictedProduct.continuous_eval (R := fun q : Nat.Primes ↦ ℚ_[q])
        (A := fun q : Nat.Primes ↦ (PadicInt.subring q : Set ℚ_[q]))
        (⟨p, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)).comp
        (continuous_subtype_val (p := fun x : FinAdele ↦ x ∈ Zhat)))
    simpa [Metric.closedBall, dist_zero_right] using this
  have hUK : U ⊆ K := by
    intro x hx
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq] at hx
    change zhatReduction N x = 0
    have hpi : (RingHom.pi fun p : (N : ℕ).primeFactors ↦
        haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        (PadicInt.toZModPow ((N : ℕ).factorization p)).comp
          (zhatToPadicInt ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)) x = 0 := by
      funext p
      have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      change PadicInt.toZModPow _ (zhatToPadicInt ⟨p, Nat.prime_of_mem_primeFactors p.2⟩ x) = 0
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact hx p
    simp only [zhatReduction, RingHom.comp_apply, hpi, map_zero]
  refine K.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds ?_) hUK)
  simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
  intro p
  rw [show ((0 : Zhat) : FinAdele) ⟨p, Nat.prime_of_mem_primeFactors p.2⟩ = 0 from rfl, norm_zero]
  positivity

/-! ### Hecke characters -/

/-- A Hecke character of `ℚ`: a continuous homomorphism `χ : 𝔸^× → ℂ^×` with `χ(q) = 1` for `q ∈ ℚ^×`. -/
@[tf_id "I.adele.def:hecke-character"]
abbrev HeckeCharacter : Type := {χ : ContinuousMonoidHom Idele ℂˣ // ∀ q : ℚˣ, χ (ratIdele q) = 1}

end GL2TF
