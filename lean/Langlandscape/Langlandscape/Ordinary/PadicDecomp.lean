/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Langlandscape.Hyp.PadicOrdDecomp
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# The ordinary decomposition for f.g. `ℤ_[p]`-modules (S04-L3)

`mathematics/chapters/s04/ordinary.tex`, `def:s04-e` (f.g. `ℤ_p` form, Steps 3 and 5; design D-e).

**Route (Hensel factorisation of an annihilating polynomial).** Let `M` be a finitely generated `ℤ_[p]`-module and
`T : Module.End ℤ_[p] M`.
1. Cayley–Hamilton for f.g. modules (`LinearMap.exists_monic_and_aeval_eq_zero`): a monic `f` with `f(T) = 0`.
2. Weierstrass preparation over the complete local ring `ℤ_[p]` (`PowerSeries.exists_isWeierstrassFactorization`):
   `f = h · U` with `h` distinguished (`h ≡ X ^ a mod p`) and `U` a unit power series; uniqueness of Weierstrass division
   shows `U = f /ₘ h` is a polynomial `u` with `u(0)` a unit.
3. `h` and `u` are coprime in `ℤ_[p][X]`: the resultant reduces mod `p` to `Res(X ^ a, ū) = ū(0) ^ a ≠ 0`
   (`Polynomial.isUnit_resultant_iff_isCoprime`).
4. Abstract part (any commutative ring `R`, any `p : R`, `hasOrdDecomp_of_factorization`): if `h(T) u(T) = 0` with
   `h, u` coprime, `h = X ^ a + p · s` and `u(0)` a unit, and `M` is `p`-adically separated, then
   `nilPart p T = ker h(T)` and `ordPart T = ker u(T)`, so `HasOrdDecomp p T`. Separation is Krull's
   intersection theorem (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`).

Main results: `hasOrdDecomp_padic`, `padicOrdDecomp_holds : Hyp.PadicOrdDecomp p` (discharges the hypothesis).
Status: *formalized*, unconditional.
-/

@[expose] public section

set_option autoImplicit false

open scoped Pointwise

namespace Langlandscape.Ordinary

noncomputable section

/-! ### Abstract part: a coprime factorisation of an annihilating polynomial -/

section Abstract

open Polynomial

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- `def:s04-e` (`s04-e`), auxiliary: polynomials in `T` commute. -/
theorem aeval_apply_comm (T : Module.End R M) (q r : R[X]) (m : M) :
    aeval T q (aeval T r m) = aeval T r (aeval T q m) := by
  calc aeval T q (aeval T r m) = (aeval T q * aeval T r) m := rfl
    _ = aeval T (q * r) m := by rw [map_mul]
    _ = aeval T (r * q) m := by rw [mul_comm]
    _ = (aeval T r * aeval T q) m := by rw [map_mul]
    _ = aeval T r (aeval T q m) := rfl

/-- `def:s04-e` (`s04-e`), auxiliary: `ker q(T)` is stable under every polynomial `r(T)`. -/
theorem aeval_mem_ker_aeval (T : Module.End R M) {q : R[X]} (r : R[X]) {m : M}
    (hm : m ∈ LinearMap.ker (aeval T q)) : aeval T r m ∈ LinearMap.ker (aeval T q) := by
  rw [LinearMap.mem_ker] at hm ⊢
  rw [aeval_apply_comm, hm, map_zero]

/-- `def:s04-e` (`s04-e`), auxiliary: `ker q(T)` is stable under `T ^ n`. -/
theorem pow_apply_mem_ker_aeval (T : Module.End R M) {q : R[X]} (n : ℕ) {m : M}
    (hm : m ∈ LinearMap.ker (aeval T q)) : (T ^ n) m ∈ LinearMap.ker (aeval T q) := by
  have h := aeval_mem_ker_aeval T (X ^ n) hm
  rwa [map_pow, aeval_X] at h

/-- `def:s04-e` (`s04-e`), auxiliary (Krull form): in a `p`-adically separated module, an element of every `pᵏ M` is
zero. -/
theorem eq_zero_of_forall_mem_smul_top {p : R}
    (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) = ⊥) {y : M}
    (hy : ∀ k : ℕ, y ∈ (p ^ k : R) • (⊤ : Submodule R M)) : y = 0 := by
  have h : y ∈ ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) := (Submodule.mem_iInf _).2 hy
  rw [hsep] at h
  exact (Submodule.mem_bot R).1 h

/-- `def:s04-e` (`s04-e`), Step 5: for coprime `h, u` with `h(T) u(T) = 0`, `M = ker h(T) ⊕ ker u(T)`. -/
theorem isCompl_ker_aeval {T : Module.End R M} {h u : R[X]} (hcop : IsCoprime h u)
    (hT : aeval T (h * u) = 0) :
    IsCompl (LinearMap.ker (aeval T h)) (LinearMap.ker (aeval T u)) := by
  refine ⟨Polynomial.disjoint_ker_aeval_of_isCoprime T hcop, ?_⟩
  rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop, hT,
    LinearMap.ker_zero]

/-- `def:s04-e` (`s04-e`), Step 5: if `h = X ^ a + p · s`, then `(T ^ a) ^ k` maps `ker h(T)` into `pᵏ M`. -/
theorem pow_pow_apply_eq_smul_of_mem_ker (p : R) (T : Module.End R M) {h s : R[X]} {a : ℕ}
    (hh : h = X ^ a + C p * s) :
    ∀ k : ℕ, ∀ m ∈ LinearMap.ker (aeval T h), ∃ y : M, ((T ^ a) ^ k) m = (p ^ k : R) • y := by
  have hstep : ∀ m ∈ LinearMap.ker (aeval T h), (T ^ a) m = p • (-(aeval T s m)) := by
    intro m hm
    have h0 : aeval T h m = 0 := LinearMap.mem_ker.1 hm
    rw [hh, map_add, map_mul, map_pow, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply] at h0
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    exact h0
  intro k
  induction k with
  | zero =>
    intro m _
    exact ⟨m, by rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]⟩
  | succ k ih =>
    intro m hm
    have hneg : -(aeval T s m) ∈ LinearMap.ker (aeval T h) := neg_mem (aeval_mem_ker_aeval T s hm)
    obtain ⟨y, hy⟩ := ih _ hneg
    refine ⟨y, ?_⟩
    rw [pow_succ (T ^ a) k, Module.End.mul_apply, hstep m hm, map_smul, hy, smul_smul, ← pow_succ' p k]

/-- `def:s04-e` (`s04-e`), Step 5: if `h = X ^ a + p · s`, then `ker h(T) ⊆ nilPart p T`. -/
theorem ker_aeval_le_nilPart (p : R) (T : Module.End R M) {h s : R[X]} {a : ℕ}
    (hh : h = X ^ a + C p * s) : LinearMap.ker (aeval T h) ≤ nilPart p T := by
  intro m hm
  rw [mem_nilPart]
  intro k
  obtain ⟨y, hy⟩ := pow_pow_apply_eq_smul_of_mem_ker p T hh k m hm
  refine ⟨a * k, ?_⟩
  rw [pow_mul, hy]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), Step 5: if `u(0)` is a unit, then `T` has a polynomial right inverse `v(T)` on
`ker u(T)`. -/
theorem exists_inv_on_ker_aeval (T : Module.End R M) {u : R[X]} (hu : IsUnit (u.coeff 0)) :
    ∃ v : R[X], ∀ m ∈ LinearMap.ker (aeval T u), T (aeval T v m) = m := by
  obtain ⟨w, hw⟩ : X ∣ u - C (u.coeff 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, sub_self]
  obtain ⟨d, hd⟩ : ∃ d : R, d * u.coeff 0 = -1 :=
    ⟨-(↑hu.unit⁻¹ : R), by rw [neg_mul, hu.val_inv_mul]⟩
  have hXv : X * (C d * w) = C d * u + 1 := by
    calc X * (C d * w) = C d * (X * w) := by ring
      _ = C d * (u - C (u.coeff 0)) := by rw [hw]
      _ = C d * u - C (d * u.coeff 0) := by rw [C_mul]; ring
      _ = C d * u + 1 := by rw [hd, C_neg, C_1]; ring
  refine ⟨C d * w, fun m hm => ?_⟩
  have h1 : aeval T (X * (C d * w)) m = aeval T (C d * u + 1) m := by rw [hXv]
  rw [map_mul, aeval_X, Module.End.mul_apply] at h1
  rw [h1, map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.mem_ker.1 hm, map_zero, zero_add, Module.End.one_apply]

/-- `def:s04-e` (`s04-e`), Step 5: if `T` has a polynomial right inverse on `ker u(T)`, then `ker u(T) ⊆ ordPart T`. -/
theorem ker_aeval_le_ordPart (T : Module.End R M) {u v : R[X]}
    (hv : ∀ m ∈ LinearMap.ker (aeval T u), T (aeval T v m) = m) :
    LinearMap.ker (aeval T u) ≤ ordPart T := by
  have key : ∀ n : ℕ, ∀ m ∈ LinearMap.ker (aeval T u), ∃ y : M, (T ^ n) y = m := by
    intro n
    induction n with
    | zero =>
      intro m _
      exact ⟨m, by rw [pow_zero, Module.End.one_apply]⟩
    | succ n ih =>
      intro m hm
      obtain ⟨y, hy⟩ := ih (aeval T v m) (aeval_mem_ker_aeval T v hm)
      exact ⟨y, by rw [pow_succ' T n, Module.End.mul_apply, hy, hv m hm]⟩
  intro m hm
  exact mem_ordPart.2 fun n => key n m hm

/-- `def:s04-e` (`s04-e`), Step 5 (`T` invertible on `e_T M`): `ker u(T) ∩ nilPart p T = 0` when `T` has a polynomial
inverse on `ker u(T)` and `M` is `p`-adically separated. -/
theorem eq_zero_of_mem_ker_aeval_of_mem_nilPart (p : R) (T : Module.End R M) {u v : R[X]}
    (hv : ∀ m ∈ LinearMap.ker (aeval T u), T (aeval T v m) = m)
    (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) = ⊥) {y : M}
    (hy : y ∈ LinearMap.ker (aeval T u)) (hy' : y ∈ nilPart p T) : y = 0 := by
  have hVT : ∀ m ∈ LinearMap.ker (aeval T u), aeval T v (T m) = m := by
    intro m hm
    have hc := aeval_apply_comm T v X m
    rw [aeval_X] at hc
    rw [hc, hv m hm]
  have hpow : ∀ n : ℕ, ∀ m ∈ LinearMap.ker (aeval T u), (aeval T v ^ n) ((T ^ n) m) = m := by
    intro n
    induction n with
    | zero =>
      intro m _
      rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ n ih =>
      intro m hm
      rw [pow_succ (aeval T v) n, pow_succ' T n, Module.End.mul_apply, Module.End.mul_apply,
        hVT _ (pow_apply_mem_ker_aeval T n hm), ih m hm]
  refine eq_zero_of_forall_mem_smul_top hsep fun k => ?_
  obtain ⟨n, hn⟩ := mem_nilPart.1 hy' k
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hn
  rw [← hpow n y hy, ← hz, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), Step 5: `ker h(T) ∩ ordPart T = 0` when `h = X ^ a + p · s`, `M = ker h(T) ⊕ ker u(T)` and
`M` is `p`-adically separated. -/
theorem eq_zero_of_mem_ker_aeval_of_mem_ordPart (p : R) (T : Module.End R M) {h u s : R[X]} {a : ℕ}
    (hcompl : IsCompl (LinearMap.ker (aeval T h)) (LinearMap.ker (aeval T u)))
    (hh : h = X ^ a + C p * s) (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) = ⊥) {y : M}
    (hy : y ∈ LinearMap.ker (aeval T h)) (hy' : y ∈ ordPart T) : y = 0 := by
  refine eq_zero_of_forall_mem_smul_top hsep fun k => ?_
  obtain ⟨z, hz⟩ := mem_ordPart.1 hy' (a * k)
  have hz' : z ∈ LinearMap.ker (aeval T h) ⊔ LinearMap.ker (aeval T u) := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hz'
  have h2 : (T ^ (a * k)) z₂ = 0 := by
    refine Submodule.disjoint_def.1 hcompl.disjoint _ ?_ (pow_apply_mem_ker_aeval T _ hz₂)
    have hsub := sub_mem hy (pow_apply_mem_ker_aeval T (a * k) hz₁)
    rwa [← hz, map_add, add_sub_cancel_left] at hsub
  obtain ⟨w, hw⟩ := pow_pow_apply_eq_smul_of_mem_ker p T hh k z₁ hz₁
  rw [← hz, map_add, h2, add_zero, pow_mul, hw]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), Step 5, abstract form: let `h, u ∈ R[X]` be coprime with `h(T) u(T) = 0`,
`h = X ^ a + p · s` and `u(0)` a unit, and let `M` be `p`-adically separated. Then `nilPart p T = ker h(T)`,
`ordPart T = ker u(T)`, and `T` has an ordinary decomposition. -/
theorem hasOrdDecomp_of_factorization (p : R) (T : Module.End R M) {h u s : R[X]} {a : ℕ}
    (hcop : IsCoprime h u) (hT : aeval T (h * u) = 0) (hh : h = X ^ a + C p * s)
    (hu : IsUnit (u.coeff 0)) (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) = ⊥) :
    HasOrdDecomp p T := by
  have hcompl := isCompl_ker_aeval hcop hT
  obtain ⟨v, hv⟩ := exists_inv_on_ker_aeval T hu
  have hnil : nilPart p T = LinearMap.ker (aeval T h) := by
    refine le_antisymm (fun m hm => ?_) (ker_aeval_le_nilPart p T hh)
    have hm' : m ∈ LinearMap.ker (aeval T h) ⊔ LinearMap.ker (aeval T u) := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.1 hm'
    have h2 : m₂ = 0 := by
      refine eq_zero_of_mem_ker_aeval_of_mem_nilPart p T hv hsep hm₂ ?_
      have hsub := sub_mem hm (ker_aeval_le_nilPart p T hh hm₁)
      rwa [add_sub_cancel_left] at hsub
    rw [h2, add_zero]
    exact hm₁
  have hord : ordPart T = LinearMap.ker (aeval T u) := by
    refine le_antisymm (fun m hm => ?_) (ker_aeval_le_ordPart T hv)
    have hm' : m ∈ LinearMap.ker (aeval T h) ⊔ LinearMap.ker (aeval T u) := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.1 hm'
    have h1 : m₁ = 0 := by
      refine eq_zero_of_mem_ker_aeval_of_mem_ordPart p T hcompl hh hsep hm₁ ?_
      have hsub := sub_mem hm (ker_aeval_le_ordPart T hv hm₂)
      rwa [add_sub_cancel_right] at hsub
    rw [h1, zero_add]
    exact hm₂
  unfold HasOrdDecomp
  rw [hord, hnil]
  exact hcompl.symm

end Abstract

/-! ### The `ℤ_[p]` instance -/

section Padic

open Polynomial
open scoped PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- `def:s04-e` (`s04-e`), auxiliary: `p` lies in the maximal ideal of `ℤ_[p]`. -/
theorem natCast_mem_maximalIdeal_padicInt : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.mem_span_singleton_self _

/-- `def:s04-e` (`s04-e`), Step 5 (Krull): a f.g. `ℤ_[p]`-module is `p`-adically separated, `⋂ₖ pᵏ M = 0`. -/
theorem iInf_pow_smul_top_eq_bot_padic (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    ⨅ k : ℕ, ((p : ℤ_[p]) ^ k : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M) = ⊥ := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (IsLocalRing.maximalIdeal ℤ_[p])
    (Ideal.IsMaximal.ne_top inferInstance)
  rw [PadicInt.maximalIdeal_eq_span_p] at h
  simpa only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] using h

/-- `def:s04-e` (`s04-e`), Step 5 (Hensel factorisation via Weierstrass preparation): a monic `f ∈ ℤ_[p][X]` factors
as `f = h · u` with `h, u` coprime, `h = X ^ a + p · s` (`h ≡ X ^ a mod p`) and `u(0)` a unit. -/
theorem exists_factorization_padic {f : ℤ_[p][X]} (hf : f.Monic) :
    ∃ (h u s : ℤ_[p][X]) (a : ℕ), f = h * u ∧ IsCoprime h u ∧ h = X ^ a + C (p : ℤ_[p]) * s ∧
      IsUnit (u.coeff 0) := by
  have hg : (f : ℤ_[p]⟦X⟧).map (IsLocalRing.residue ℤ_[p]) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, ne_eq, Polynomial.coe_eq_zero_iff]
    exact (hf.map _).ne_zero
  obtain ⟨h, U, H⟩ := PowerSeries.exists_isWeierstrassFactorization hg
  have hd : h.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) := H.isDistinguishedAt
  have hmon : h.Monic := hd.monic
  -- uniqueness of Weierstrass division by `h`: `U = f /ₘ h` and `f %ₘ h = 0`
  have hW : (h : ℤ_[p]⟦X⟧).IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal ℤ_[p]) :=
    hd.isWeierstrassDivisorAt'
  have hord : ((h : ℤ_[p]⟦X⟧).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p]))).order.toNat = h.natDegree := by
    have hnot : PowerSeries.constantCoeff (1 : ℤ_[p]⟦X⟧) ∉ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [map_one]
      exact IsLocalRing.notMem_maximalIdeal.2 isUnit_one
    have hc := hd.coe_natDegree_eq_order_map (h : ℤ_[p]⟦X⟧) 1 hnot (mul_one _).symm
    exact (congrArg ENat.toNat hc).symm.trans (ENat.toNat_natCast _)
  have hdeg : (f %ₘ h).degree < ((h : ℤ_[p]⟦X⟧).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p]))).order.toNat := by
    rw [hord, ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt f hmon
  have hdiv : f %ₘ h + h * (f /ₘ h) = f := modByMonic_add_div f h
  have heq : (h : ℤ_[p]⟦X⟧) * (U - ((f /ₘ h : ℤ_[p][X]) : ℤ_[p]⟦X⟧)) =
      ((f %ₘ h : ℤ_[p][X]) : ℤ_[p]⟦X⟧) := by
    have e1 : ((f %ₘ h : ℤ_[p][X]) : ℤ_[p]⟦X⟧) + (h : ℤ_[p]⟦X⟧) * ((f /ₘ h : ℤ_[p][X]) : ℤ_[p]⟦X⟧) =
        (f : ℤ_[p]⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, hdiv]
    rw [mul_sub, ← H.eq_mul, ← e1]
    ring
  obtain ⟨hq, hr⟩ := hW.eq_zero_of_mul_eq hdeg heq
  have hU : U = ((f /ₘ h : ℤ_[p][X]) : ℤ_[p]⟦X⟧) := sub_eq_zero.1 hq
  rw [hr, zero_add] at hdiv
  have hu0 : IsUnit ((f /ₘ h).coeff 0) := by
    have h1 := PowerSeries.isUnit_iff_constantCoeff.1 H.isUnit
    rwa [hU, Polynomial.constantCoeff_coe] at h1
  -- `h ≡ X ^ m` modulo `p`
  have hmem : h - X ^ h.natDegree ∈
      Ideal.map (C : ℤ_[p] →+* ℤ_[p][X]) (Ideal.span {(p : ℤ_[p])}) := by
    rw [Ideal.mem_map_C_iff, ← PadicInt.maximalIdeal_eq_span_p]
    intro n
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy n h.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact hd.mem hn
    · rw [if_pos hn, hn, hmon.coeff_natDegree, sub_self]
      exact zero_mem _
    · rw [if_neg hn.ne', sub_zero, coeff_eq_zero_of_natDegree_lt hn]
      exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hhs : h = X ^ h.natDegree + C (p : ℤ_[p]) * s := sub_eq_iff_eq_add'.1 hs
  -- coprimality via the resultant: `Res(h, u) ≡ Res(X ^ m, ū) = ū(0) ^ m ≢ 0 mod p`
  have hres : IsLocalRing.residue ℤ_[p] (p : ℤ_[p]) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 natCast_mem_maximalIdeal_padicInt
  have hX : h.map (IsLocalRing.residue ℤ_[p]) = X ^ h.natDegree := by
    calc h.map (IsLocalRing.residue ℤ_[p])
        = (X ^ h.natDegree + C (p : ℤ_[p]) * s).map (IsLocalRing.residue ℤ_[p]) :=
          congrArg (Polynomial.map (IsLocalRing.residue ℤ_[p])) hhs
      _ = X ^ h.natDegree := by
          rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
            Polynomial.map_C, hres, C_0, zero_mul, add_zero]
  have hcop : IsCoprime h (f /ₘ h) := by
    rw [← Polynomial.isUnit_resultant_iff_isCoprime hmon, ← IsLocalRing.residue_ne_zero_iff_isUnit,
      ← Polynomial.resultant_map_map, hX,
      Polynomial.resultant_X_pow_left ((f /ₘ h).map (IsLocalRing.residue ℤ_[p])) h.natDegree
        (f /ₘ h).natDegree natDegree_map_le, coeff_map]
    exact pow_ne_zero _ ((IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu0)
  exact ⟨h, f /ₘ h, s, h.natDegree, hdiv.symm, hcop, hhs, hu0⟩

/-- `def:s04-e` (`s04-e`), f.g. `ℤ_p` form (Step 5): every endomorphism `T` of a finitely generated `ℤ_[p]`-module has
an ordinary decomposition `M = ordPart T ⊕ nilPart p T`. -/
theorem hasOrdDecomp_padic {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (T : Module.End ℤ_[p] M) : HasOrdDecomp (p : ℤ_[p]) T := by
  obtain ⟨f, hf, hfT⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ_[p] T
  obtain ⟨h, u, s, a, hfhu, hcop, hhs, hu⟩ := exists_factorization_padic hf
  rw [hfhu] at hfT
  exact hasOrdDecomp_of_factorization (p : ℤ_[p]) T hcop hfT hhs hu
    (iInf_pow_smul_top_eq_bot_padic M)

end Padic

/-- `def:s04-e` (`s04-e`), f.g. `ℤ_p` form: the hypothesis `Hyp.PadicOrdDecomp p` holds (discharged, D-e / F-e). -/
theorem padicOrdDecomp_holds (p : ℕ) [Fact p.Prime] : Hyp.PadicOrdDecomp p := by
  unfold Hyp.PadicOrdDecomp
  intro M _ _ _ T
  exact hasOrdDecomp_padic T

end

end Langlandscape.Ordinary
