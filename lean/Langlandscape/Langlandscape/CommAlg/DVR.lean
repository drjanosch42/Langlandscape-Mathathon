/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.ThmE
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Theorem E (iii), DVR half (S06-L5a)

`mathematics/chapters/s06/s06-m1.tex`, `thm:s06-E`(iii): the identity `η(S, λ) = c_q · η(S', λ')`
holds whenever the coefficient
ring is a DVR, with **no** hypothesis on `S' = S ⧸ 𝔞`; (Gor_S) is an explicit argument. Secondary
reference: `plan/staged/stage-06-integral-defect.tex`.

Not formalized: the clause of `thm:s06-E`(iii) for `A` normal (reduction to height-one primes /
localization to DVRs); only the DVR case is proved here.

Setting as in `ThmE` (S06-L4): `𝒪` a discrete valuation ring, `D : NewOldData 𝒪 S`,
`lam' : S' →ₐ[𝒪] 𝒪`, `λ = ThmE.lam D lam'`.

* `ThmE.exists_unimodular_of_dvr`: under (Gor_S), `S'[λ'] = Ann_{S'}(ker λ')` is `𝒪 θ'` with `θ'`
  unimodular in `S'` (the hypothesis of `thm:s06-E`(ii)).
* `ThmE.eta_eq_c_mul_of_dvr`: hence `η(S, λ) = c_q · η(S', λ')`.

Proof of the first item. `S'` is finite and torsion-free over the PID `𝒪`, hence free.
*Rank at most one* (the chapter argues via `S_K`; here): write `c = a₀ + b₀` with `c ≠ 0`,
`a₀ ∈ 𝔞`, `b₀ ∈ 𝔟` (field `split`). For `n = t mod 𝔞 ∈ S'[λ']`, `b₀ t ∈ S[λ] = 𝒪 θ`
(`lem:s06-S`), so `b₀ t = ℓ(b₀ t) θ`, and `c n = b₀ t mod 𝔞`. Hence `ψ = ℓ(b₀ ·)` is injective on
`S'[λ']`, which therefore is isomorphic to an ideal of `𝒪`, hence `= 𝒪 θ'` (`𝒪` is a PID).
*Unimodularity* (the tex: saturated, hence a summand): the order ideal of `θ'` is `(e)`; all
coordinates of `θ'` in a basis of `S'` lie in `(e)`, so `θ' = e u`; `S'[λ']` is saturated (an
annihilator in a torsion-free module), so `u ∈ 𝒪 θ'`, `u = a e u`, and `a e = 1` because `u ≠ 0`
(`θ' ≠ 0`, since `θ mod 𝔞 ≠ 0`).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

namespace ThmE

variable {𝒪 S : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CommRing S]
  [Algebra 𝒪 S]

/-- `thm:s06-E` (`s06-E`)(iii), DVR half, first step: under (Gor_S) with trace `ℓ`, over a DVR `𝒪`,
`S'[λ'] = Ann_{S'}(ker λ')` is free of rank one, `= 𝒪 θ'`, with `θ'` unimodular in `S' = S ⧸ 𝔞`
(some `ψ ∈ S'^∨` has `ψ θ' = 1`). No hypothesis on `S'`: it is free since it is finite and
torsion-free over a PID; rank one comes from (Gor_S) and `split` (via `ψ = ℓ(b₀ ·)`), and
unimodularity from the saturation of `S'[λ']`. -/
theorem exists_unimodular_of_dvr (D : NewOldData 𝒪 S) {ℓ : Module.Dual 𝒪 S}
    (hℓ : IsGorensteinWith 𝒪 S ℓ) (lam' : S ⧸ D.𝔞 →ₐ[𝒪] 𝒪) :
    ∃ θ' : S ⧸ D.𝔞, (ann (RingHom.ker lam')).restrictScalars 𝒪 = Submodule.span 𝒪 {θ'} ∧
      ∃ ψ : Module.Dual 𝒪 (S ⧸ D.𝔞), ψ θ' = 1 := by
  set N : Submodule 𝒪 (S ⧸ D.𝔞) := (ann (RingHom.ker lam')).restrictScalars 𝒪 with hN
  set θ := LemmaS.theta hℓ (lam D lam') with hθ
  have htf := D.tf_a
  -- torsion-freeness of `S'` in the form used below
  have hcancel : ∀ {r : 𝒪} {m : S ⧸ D.𝔞}, r ≠ 0 → r • m = 0 → m = 0 := by
    intro r m hr hm
    have h1 : r • m = r • (0 : S ⧸ D.𝔞) := by rw [hm, smul_zero]
    exact htf.isSMulRegular (isRegular_iff_ne_zero.2 hr) h1
  have hmemN : ∀ m : S ⧸ D.𝔞, m ∈ N ↔ ∀ y ∈ RingHom.ker lam', m * y = 0 := fun m => mem_ann
  -- `x = θ mod 𝔞` is a nonzero element of `N`
  have hxN : Ideal.Quotient.mk D.𝔞 θ ∈ N := mk_theta_mem_ann D hℓ lam'
  have hx0 : Ideal.Quotient.mk D.𝔞 θ ≠ 0 := by
    intro h0
    have hθa : θ ∈ D.𝔞 := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have hθb : θ ∈ D.𝔟 := theta_mem_b D hℓ lam'
    have hθ0 : θ = 0 := by
      have : θ ∈ D.𝔞 ⊓ D.𝔟 := ⟨hθa, hθb⟩
      rw [D.inf_eq_bot] at this
      exact this
    have h1 := LemmaS.trace_theta hℓ (lam D lam')
    rw [← hθ, hθ0, map_zero] at h1
    exact zero_ne_one h1
  -- the splitting `c = a₀ + b₀`
  obtain ⟨c, hc, hcm⟩ := D.split
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := Submodule.mem_sup.1 hcm
  let ψ : Module.Dual 𝒪 (S ⧸ D.𝔞) := D.bEquivDualQuot hℓ ⟨b₀, hb₀⟩
  have hψ : ∀ t : S, ψ (Ideal.Quotient.mk D.𝔞 t) = ℓ (b₀ * t) := fun t =>
    NewOldData.bEquivDualQuot_apply D hℓ ⟨b₀, hb₀⟩ t
  -- `ψ` is injective on `N`
  have hψinj : ∀ n ∈ N, ψ n = 0 → n = 0 := by
    intro n hn hψn
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective n
    have hbt : b₀ * t ∈ ann (RingHom.ker (lam D lam')) := by
      refine mem_ann.2 fun y hy => ?_
      have hy' : Ideal.Quotient.mk D.𝔞 y ∈ RingHom.ker lam' := hy
      have hty : t * y ∈ D.𝔞 := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
        exact (hmemN _).1 hn _ hy'
      have : b₀ * (t * y) ∈ D.𝔞 ⊓ D.𝔟 :=
        ⟨D.𝔞.mul_mem_left b₀ hty, D.𝔟.mul_mem_right _ hb₀⟩
      rw [D.inf_eq_bot] at this
      rw [mul_assoc]
      exact this
    have hbt0 : b₀ * t = 0 := by
      rw [LemmaS.eq_smul_theta_of_mem hℓ (lam D lam') hbt, ← hψ, hψn, zero_smul]
    apply hcancel hc
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← hab, add_mul, map_add,
      hbt0, map_zero, add_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact D.𝔞.mul_mem_right t ha₀
  -- `ψ(N)` is a principal ideal `(d)`, `d = ψ θ'`, and `N = 𝒪 θ'`
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (N.map ψ)).principal
  have hdmem : d ∈ N.map ψ := by rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨θ', hθ'N, hθ'd⟩ := Submodule.mem_map.1 hdmem
  have hNspan : N = Submodule.span 𝒪 {θ'} := by
    apply le_antisymm
    · intro n hn
      have hψn : ψ n ∈ N.map ψ := Submodule.mem_map_of_mem hn
      rw [hd, Submodule.mem_span_singleton] at hψn
      obtain ⟨a, ha⟩ := hψn
      have : n - a • θ' = 0 := by
        apply hψinj _ (N.sub_mem hn (N.smul_mem a hθ'N))
        rw [map_sub, map_smul, hθ'd, ha, sub_self]
      rw [sub_eq_zero] at this
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self θ')
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hθ'N
  have hθ'0 : θ' ≠ 0 := by
    intro h0
    have := hxN
    rw [hNspan, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
    exact hx0 this
  refine ⟨θ', hNspan, ?_⟩
  -- unimodularity of `θ'`
  have : Module.Finite 𝒪 (S ⧸ D.𝔞) := by
    have := D.finite
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 D.𝔞).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 D.𝔞)
  have : Module.Free 𝒪 (S ⧸ D.𝔞) := Module.free_of_finite_type_torsion_free'
  let J : Ideal 𝒪 := LinearMap.range (Module.Dual.eval 𝒪 (S ⧸ D.𝔞) θ')
  obtain ⟨e, he⟩ := (IsPrincipalIdealRing.principal J).principal
  have hemem : e ∈ J := by rw [he]; exact Submodule.mem_span_singleton_self e
  obtain ⟨φ₀, hφ₀⟩ := hemem
  rw [Module.Dual.eval_apply] at hφ₀
  let b := Module.Free.chooseBasis 𝒪 (S ⧸ D.𝔞)
  have hcoord : ∀ i, ∃ ci : 𝒪, ci * e = b.repr θ' i := by
    intro i
    have : b.coord i θ' ∈ J := ⟨b.coord i, rfl⟩
    rw [he, Ideal.mem_span_singleton'] at this
    simpa [Module.Basis.coord_apply] using this
  choose ci hci using hcoord
  set u : S ⧸ D.𝔞 := ∑ i, ci i • b i with hu
  have heu : e • u = θ' := by
    rw [hu, Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr θ']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm, hci]
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_smul] at heu
    exact hθ'0 heu.symm
  have hu0 : u ≠ 0 := by
    rintro h0
    rw [h0, smul_zero] at heu
    exact hθ'0 heu.symm
  -- saturation: `u ∈ N`
  have huN : u ∈ N := by
    refine (hmemN u).2 fun y hy => hcancel he0 ?_
    rw [← smul_mul_assoc, heu]
    exact (hmemN θ').1 hθ'N y hy
  rw [hNspan, Submodule.mem_span_singleton] at huN
  obtain ⟨a, ha⟩ := huN
  have hae : a * e = 1 := by
    have h1 : (a * e - 1) • u = 0 := by
      rw [sub_smul, mul_smul, heu, ha, one_smul, sub_self]
    by_contra hne
    exact hu0 (hcancel (sub_ne_zero.2 hne) h1)
  exact ⟨a • φ₀, by rw [LinearMap.smul_apply, hφ₀, smul_eq_mul, hae]⟩

/-- `thm:s06-E` (`s06-E`)(iii), DVR half: let `𝒪` be a discrete valuation ring,
`D : NewOldData 𝒪 S` (so `S` is finite free over `𝒪`, `S' = S ⧸ 𝔞`), `λ' : S' →ₐ[𝒪] 𝒪` and
`λ = λ' ∘ (S → S')` (`ThmE.lam`). Under (Gor_S) (`hS`, explicit), `η(S, λ) = c_q · η(S', λ')` with
`c_q = λ(𝔟)`. No hypothesis on `S'`: over a DVR, `S'[λ'] = Ann_{S'}(ker λ')` is free of rank one
with a unimodular generator (`ThmE.exists_unimodular_of_dvr`), and
`ThmE.eta_eq_c_mul_of_unimodular` (S06-L4) applies. -/
theorem eta_eq_c_mul_of_dvr (D : NewOldData 𝒪 S) (hS : IsGorenstein 𝒪 S)
    (lam' : S ⧸ D.𝔞 →ₐ[𝒪] 𝒪) :
    congruenceIdeal (lam D lam') = D.𝔟.map (lam D lam') * congruenceIdeal lam' := by
  obtain ⟨_, hℓ⟩ := hS
  obtain ⟨θ', hθ', hu⟩ := exists_unimodular_of_dvr D hℓ lam'
  exact eta_eq_c_mul_of_unimodular D hℓ lam' θ' hθ' hu

end ThmE

end Langlandscape.CommAlg
