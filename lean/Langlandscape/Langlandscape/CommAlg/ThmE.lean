/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.LemmaS
public import Langlandscape.CommAlg.NewOld

/-!
# Theorem E: the combinatorial half of the defect formula (S06-L4)

`mathematics/chapters/s06/s06-m1.tex`, `thm:s06-E` (seed Thm E, hypotheses explicit), parts (i),
(ii), (iv) and the Gorenstein
half of (iii). The DVR half of (iii) is S06-L5a (`CommAlg/DVR.lean`). Secondary reference:
`plan/staged/stage-06-integral-defect.tex`.

Not formalized: the clause of `thm:s06-E`(iii) for `A` normal (height-one primes, localization to
DVRs); only the Gorenstein half and, in `DVR.lean`, the case of a DVR coefficient ring are proved.

Setting: `D : NewOldData A S` (the hypotheses of `lem:s06-D`), `S' = S ⧸ D.𝔞`, and
`λ = ThmE.lam D lam' : S → A` the composite of `S → S'` with `lam' : S' →ₐ[A] A`. Under (Gor_S),
`hℓ : IsGorensteinWith A S ℓ`, let `θ = LemmaS.theta hℓ λ` generate `S[λ]` and `x = θ mod 𝔞`.

* (i) `ThmE.theta_mem_b`: `θ ∈ 𝔟`; `ThmE.mk_theta_mem_ann`: `x ∈ S'[λ']`;
  `ThmE.eta_eq_span_lambda'`: `η(S, λ) = (λ'(x))`; `ThmE.c_eq_orderIdeal`: `c_q := λ(𝔟)` is the
  order ideal `{ψ(x) : ψ ∈ S'^∨}` of `x`.
* (ii) `ThmE.eta_eq_c_mul_of_unimodular`: if `S'[λ'] = A θ'` with `θ'` unimodular in `S'`, then
  `η(S, λ) = c_q · η(S', λ')`.
* (iii), Gorenstein half: `ThmE.unimodular_of_isGorenstein`: under (Gor_{S'}) the hypothesis of (ii)
  holds; `ThmE.eta_eq_c_mul_of_isGorenstein`: hence `η(S, λ) = c_q · η(S', λ')`.
* (iv) `ThmE.c_principal_iff_isGorenstein`: for `S'` free over `A`, `c = im(𝔟 → S')` is a principal
  ideal of `S'` iff (Gor_{S'}).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

namespace ThmE

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] (D : NewOldData A S)

/-- `thm:s06-E` (`s06-E`): `λ : S → A`, the composite of `S → S' = S ⧸ 𝔞` with `λ' : S' → A`. -/
def lam (lam' : S ⧸ D.𝔞 →ₐ[A] A) : S →ₐ[A] A :=
  lam'.comp (Ideal.Quotient.mkₐ A D.𝔞)

/-- `thm:s06-E` (`s06-E`): `λ s = λ' (s mod 𝔞)`. -/
theorem lam_apply (lam' : S ⧸ D.𝔞 →ₐ[A] A) (s : S) :
    lam D lam' s = lam' (Ideal.Quotient.mk D.𝔞 s) := rfl

variable [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (lam' : S ⧸ D.𝔞 →ₐ[A] A)

/-- `thm:s06-E` (`s06-E`)(i): the generator `θ` of `S[λ]` lies in `𝔟` (since `𝔞 ⊆ ker λ` and
`Ann_S(𝔞) = 𝔟` by `lem:s06-D`(a)). -/
theorem theta_mem_b : LemmaS.theta hℓ (lam D lam') ∈ D.𝔟 := by
  rw [← D.ann_a]
  refine ann_anti (fun y hy => ?_) (LemmaS.theta_mem_ann_ker hℓ (lam D lam'))
  rw [RingHom.mem_ker, lam_apply, Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] in
/-- `thm:s06-E` (`s06-E`)(i): the image `x = θ mod 𝔞` lies in `S'[λ'] = Ann_{S'}(ker λ')`. -/
theorem mk_theta_mem_ann :
    Ideal.Quotient.mk D.𝔞 (LemmaS.theta hℓ (lam D lam')) ∈ ann (RingHom.ker lam') := by
  refine mem_ann.2 fun y hy => ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht : t ∈ RingHom.ker (lam D lam') := hy
  rw [← map_mul, mem_ann.1 (LemmaS.theta_mem_ann_ker hℓ (lam D lam')) t ht, map_zero]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] in
/-- `thm:s06-E` (`s06-E`)(i): `η(S, λ) = (λ'(x))`, `x = θ mod 𝔞`. -/
theorem eta_eq_span_lambda' :
    congruenceIdeal (lam D lam') =
      Ideal.span {lam' (Ideal.Quotient.mk D.𝔞 (LemmaS.theta hℓ (lam D lam')))} :=
  LemmaS.congruenceIdeal_eq_span hℓ (lam D lam')

/-- `thm:s06-E` (`s06-E`)(i): `c_q := λ(𝔟)` is the order ideal of `x = θ mod 𝔞`:
`λ(𝔟) = {ψ(x) : ψ ∈ S'^∨}`, the range of evaluation at `x` on `S'^∨`. (For `β ∈ 𝔟`,
`λ(β) = ℓ(β θ) = ψ_β(x)` with `ψ_β = ℓ(β ·)`, and `ψ_β` runs through `S'^∨` by `lem:s06-D`(b).) -/
theorem c_eq_orderIdeal :
    D.𝔟.map (lam D lam') = LinearMap.range
      (Module.Dual.eval A (S ⧸ D.𝔞) (Ideal.Quotient.mk D.𝔞 (LemmaS.theta hℓ (lam D lam')))) := by
  set θ := LemmaS.theta hℓ (lam D lam')
  have key : ∀ b : D.𝔟, lam D lam' b = D.bEquivDualQuot hℓ b (Ideal.Quotient.mk D.𝔞 θ) := by
    intro b
    rw [NewOldData.bEquivDualQuot_apply, mul_comm, LemmaS.trace_theta_mul]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro β hβ
    rw [Ideal.mem_comap, key ⟨β, hβ⟩]
    exact ⟨D.bEquivDualQuot hℓ ⟨β, hβ⟩, rfl⟩
  · rintro _ ⟨ψ, rfl⟩
    obtain ⟨b, rfl⟩ := (D.bEquivDualQuot hℓ).surjective ψ
    rw [Module.Dual.eval_apply, ← key]
    exact Ideal.mem_map_of_mem _ b.2

include hℓ in
/-- `thm:s06-E` (`s06-E`)(ii): if `S'[λ'] = A θ'` (free of rank one) with `θ'` unimodular in `S'`
(some `ψ ∈ S'^∨` has `ψ θ' = 1`, i.e. `A θ'` is an `A`-direct summand of `S'`), then
`η(S, λ) = c_q · η(S', λ')`, `c_q = λ(𝔟)`. -/
theorem eta_eq_c_mul_of_unimodular (θ' : S ⧸ D.𝔞)
    (hθ' : (ann (RingHom.ker lam')).restrictScalars A = Submodule.span A {θ'})
    (hu : ∃ ψ : Module.Dual A (S ⧸ D.𝔞), ψ θ' = 1) :
    congruenceIdeal (lam D lam') = D.𝔟.map (lam D lam') * congruenceIdeal lam' := by
  have hx : Ideal.Quotient.mk D.𝔞 (LemmaS.theta hℓ (lam D lam')) ∈
      (ann (RingHom.ker lam')).restrictScalars A := mk_theta_mem_ann D hℓ lam'
  rw [hθ', Submodule.mem_span_singleton] at hx
  obtain ⟨h, hh⟩ := hx
  -- `c_q = (h)`
  have hc : D.𝔟.map (lam D lam') = Ideal.span {h} := by
    rw [c_eq_orderIdeal D hℓ lam']
    apply le_antisymm
    · rintro _ ⟨ψ, rfl⟩
      rw [Module.Dual.eval_apply, ← hh, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨ψ, hψ⟩ := hu
      refine ⟨ψ, ?_⟩
      rw [Module.Dual.eval_apply, ← hh, map_smul, hψ, smul_eq_mul, mul_one]
  -- `η(S', λ') = (λ' θ')`
  have hη' : congruenceIdeal lam' = Ideal.span {lam' θ'} := by
    unfold congruenceIdeal
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have hy' : y ∈ (ann (RingHom.ker lam')).restrictScalars A := hy
      rw [hθ', Submodule.mem_span_singleton] at hy'
      obtain ⟨a, rfl⟩ := hy'
      rw [Ideal.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hθ'mem : θ' ∈ (ann (RingHom.ker lam')).restrictScalars A := by
        rw [hθ']; exact Submodule.mem_span_singleton_self θ'
      exact Ideal.mem_map_of_mem _ hθ'mem
  rw [eta_eq_span_lambda' D hℓ lam', hc, hη', Ideal.span_singleton_mul_span_singleton, ← hh,
    map_smul, smul_eq_mul]

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] in
/-- `thm:s06-E` (`s06-E`)(iii), Gorenstein half: under (Gor_{S'}) (`S'` finite free and
`A`-Gorenstein with trace `ℓ'`), `S'[λ']` is free of rank one with a unimodular generator
(the generator `θ'` of `lem:s06-S` has `ℓ'(θ') = 1`). -/
theorem unimodular_of_isGorenstein {ℓ' : Module.Dual A (S ⧸ D.𝔞)}
    (hℓ' : IsGorensteinWith A (S ⧸ D.𝔞) ℓ') :
    ∃ θ' : S ⧸ D.𝔞, (ann (RingHom.ker lam')).restrictScalars A = Submodule.span A {θ'} ∧
      ∃ ψ : Module.Dual A (S ⧸ D.𝔞), ψ θ' = 1 :=
  ⟨LemmaS.theta hℓ' lam', LemmaS.ann_ker_restrictScalars_eq_span hℓ' lam', ℓ',
    LemmaS.trace_theta hℓ' lam'⟩

include hℓ in
/-- `thm:s06-E` (`s06-E`)(ii)+(iii), Gorenstein half: under (Gor_S) and (Gor_{S'}),
`η(S, λ) = c_q · η(S', λ')`. -/
theorem eta_eq_c_mul_of_isGorenstein (hS' : IsGorenstein A (S ⧸ D.𝔞)) :
    congruenceIdeal (lam D lam') = D.𝔟.map (lam D lam') * congruenceIdeal lam' := by
  obtain ⟨_, hℓ'⟩ := hS'
  obtain ⟨θ', hθ', hu⟩ := unimodular_of_isGorenstein D lam' hℓ'
  exact eta_eq_c_mul_of_unimodular D hℓ lam' θ' hθ' hu

include hℓ in
/-- `thm:s06-E` (`s06-E`)(iv): under (Gor_S), `c = im(𝔟 → S') ≅ 𝔟 ≅ S'^∨` (`lem:s06-D`(b) and
`𝔞 ∩ 𝔟 = 0`), so for `S'` free over `A` the ideal `c` of `S'` is principal iff (Gor_{S'}). -/
theorem c_principal_iff_isGorenstein (hfree : Module.Free A (S ⧸ D.𝔞)) :
    (D.𝔟.map (Ideal.Quotient.mk D.𝔞)).IsPrincipal ↔ IsGorenstein A (S ⧸ D.𝔞) := by
  -- `s • g = β` in `𝔟` as soon as the duals agree
  have hinj : ∀ (s : S) (g β : D.𝔟), D.bEquivDualQuot hℓ β =
      D.bEquivDualQuot hℓ g ∘ₗ LinearMap.mulLeft A (Ideal.Quotient.mk D.𝔞 s) → β = s • g := by
    intro s g β h
    rw [← NewOldData.bEquivDualQuot_smul] at h
    exact (D.bEquivDualQuot hℓ).injective h
  constructor
  · rintro ⟨y, hy⟩
    have hymem : y ∈ D.𝔟.map (Ideal.Quotient.mk D.𝔞) := by
      rw [hy]; exact Submodule.mem_span_singleton_self y
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hymem
    have := D.finite
    have hfin : Module.Finite A (S ⧸ D.𝔞) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ A D.𝔞).toLinearMap
        (Ideal.Quotient.mkₐ_surjective A D.𝔞)
    refine isGorenstein_iff_cyclic.2 ⟨hfree, hfin, D.bEquivDualQuot hℓ ⟨g, hg⟩, fun φ => ?_⟩
    obtain ⟨β, rfl⟩ := (D.bEquivDualQuot hℓ).surjective φ
    have hβ : Ideal.Quotient.mk D.𝔞 (β : S) ∈ D.𝔟.map (Ideal.Quotient.mk D.𝔞) :=
      Ideal.mem_map_of_mem _ β.2
    rw [hy, Submodule.mem_span_singleton] at hβ
    obtain ⟨r, hr⟩ := hβ
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨Ideal.Quotient.mk D.𝔞 s, ?_⟩
    have hβeq : β = s • (⟨g, hg⟩ : D.𝔟) := by
      apply Subtype.ext
      have hdiff : (β : S) - s * g ∈ D.𝔞 ⊓ D.𝔟 := by
        refine ⟨?_, D.𝔟.sub_mem β.2 (D.𝔟.mul_mem_left s hg)⟩
        show (β : S) - s * g ∈ D.𝔞
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hr, smul_eq_mul, map_mul, sub_self]
      rw [D.inf_eq_bot, Ideal.mem_bot, sub_eq_zero] at hdiff
      rw [hdiff, Submodule.coe_smul, smul_eq_mul]
    rw [hβeq, NewOldData.bEquivDualQuot_smul]
  · rintro ⟨ℓ', hℓ'⟩
    obtain ⟨g, hg⟩ := (D.bEquivDualQuot hℓ).surjective ℓ'
    refine ⟨⟨Ideal.Quotient.mk D.𝔞 (g : S), le_antisymm ?_ ?_⟩⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro β hβ
      obtain ⟨t', ht'⟩ := hℓ'.exists_eq (D.bEquivDualQuot hℓ ⟨β, hβ⟩)
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t'
      have h := hinj s g ⟨β, hβ⟩ (by
        refine LinearMap.ext fun q => ?_
        rw [ht', hg, LinearMap.comp_apply, LinearMap.mulLeft_apply])
      rw [Ideal.mem_comap, Submodule.mem_span_singleton]
      refine ⟨Ideal.Quotient.mk D.𝔞 s, ?_⟩
      have h' := congrArg Subtype.val h
      rw [Submodule.coe_smul, smul_eq_mul] at h'
      rw [smul_eq_mul, ← map_mul, ← h']
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ g.2

end ThmE

end Langlandscape.CommAlg
