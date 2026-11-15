/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.LemmaS

/-!
# The η-principle: congruence ideal = self-pairing of an eigenvector (S06-L17)

`mathematics/chapters/s04/etaprinciple.tex`, `prop:s04-etaprinciple` (with `thm:s04-etaB`; cf. Hsieh
Rem. 7.3) and `mathematics/chapters/s06/s06-m1.tex`, `lem:s06-S`. Secondary references:
`plan/staged/stage-04-lambda-adic.tex` (`thm:s04-etaB` and the paragraph after it),
`plan/staged/stage-06-integral-defect.tex`.

Let `S` be finite free over `A`, `M` an `S`-module with `e : M ≃ₗ[S] S` (free of rank one), and
`B : M →ₗ[A] M →ₗ[A] A` a perfect pairing (`B` bijective onto `Hom_A(M, A)`) that is
`S`-equivariant,
`B (s • m) n = B m (s • n)`. Then

* `EtaPrinciple.isGorensteinWith_of_pairing`: `S` is `A`-Gorenstein with trace
  `EtaPrinciple.traceOfPairing e B = B (e⁻¹ 1) (e⁻¹ ·)`;
* `EtaPrinciple.congruenceIdeal_eq_span_pairing`: for `μ : S →ₐ[A] A` and `m₀` generating the
  eigenline of `μ` in `M`, the congruence ideal is `η(S, μ) = (B m₀ m₀)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

namespace EtaPrinciple

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S]
  [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]

/-- `thm:s04-etaB`, `lem:s06-S` (`s04-etaB`, `s06-S`): the trace `ℓ = B (e⁻¹ 1) (e⁻¹ ·)` of `S`
induced by an `S`-module isomorphism `e : M ≃ S` and a pairing `B` on `M`. -/
noncomputable def traceOfPairing (e : M ≃ₗ[S] S) (B : M →ₗ[A] M →ₗ[A] A) : Module.Dual A S :=
  B (e.symm 1) ∘ₗ (e.symm.restrictScalars A).toLinearMap

/-- `thm:s04-etaB`, `lem:s06-S` (`s04-etaB`, `s06-S`):
`traceOfPairing e B x = B (e⁻¹ 1) (e⁻¹ x)`. -/
theorem traceOfPairing_apply (e : M ≃ₗ[S] S) (B : M →ₗ[A] M →ₗ[A] A) (x : S) :
    traceOfPairing e B x = B (e.symm 1) (e.symm x) := rfl

/-- `thm:s04-etaB`, `lem:s06-S` (`s04-etaB`, `s06-S`): for an `S`-equivariant pairing,
`B (e⁻¹ s) (e⁻¹ t) = ℓ (s t)` with `ℓ = traceOfPairing e B`. -/
theorem pairing_symm_symm (e : M ≃ₗ[S] S) (B : M →ₗ[A] M →ₗ[A] A)
    (hBs : ∀ (s : S) (m n : M), B (s • m) n = B m (s • n)) (s t : S) :
    B (e.symm s) (e.symm t) = traceOfPairing e B (s * t) := by
  rw [traceOfPairing_apply, ← smul_eq_mul, map_smul, ← hBs, ← map_smul, smul_eq_mul, mul_one]

/-- `thm:s04-etaB`, `lem:s06-S` (`s04-etaB`, `s06-S`): if `S` is finite free over `A`,
`e : M ≃ₗ[S] S`, and `B : M →ₗ[A] M →ₗ[A] A` is bijective with `B (s • m) n = B m (s • n)`, then `S`
is `A`-Gorenstein with trace `traceOfPairing e B`. -/
theorem isGorensteinWith_of_pairing [Module.Free A S] [Module.Finite A S] (e : M ≃ₗ[S] S)
    (B : M →ₗ[A] M →ₗ[A] A) (hB : Function.Bijective B)
    (hBs : ∀ (s : S) (m n : M), B (s • m) n = B m (s • n)) :
    IsGorensteinWith A S (traceOfPairing e B) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let e' : M ≃ₗ[A] S := e.restrictScalars A
  let P : Module.Dual A M → Module.Dual A S := fun φ => φ ∘ₗ e'.symm.toLinearMap
  have hP : Function.Bijective P := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ ∘ₗ e'.toLinearMap, ?_, ?_⟩
    · intro φ; ext x; simp [P]
    · intro ψ; ext x; simp [P]
  have hfun : (fun s : S => traceOfPairing e B ∘ₗ LinearMap.mulLeft A s) =
      P ∘ B ∘ e.symm := by
    funext s
    ext t
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, P]
    rw [← pairing_symm_symm e B hBs]
    rfl
  rw [hfun]
  exact (hP.comp hB).comp e.symm.bijective

/-- `thm:s04-etaB`, `lem:s06-S` (`s04-etaB`, `s06-S`). η-principle: `S` finite free over `A`,
`e : M ≃ₗ[S] S`, `B : M →ₗ[A] M →ₗ[A] A` bijective, `B (s • m) n = B m (s • n)`, `μ : S →ₐ[A] A`,
`m₀` generating the eigenline `{m | ∀ s, s • m = μ s • m}` ⇒ `congruenceIdeal μ = span {B m₀ m₀}`.
(Reference statement for S04-M6, the general principle of the paragraph after `thm:s04-etaB`;
cf. Hsieh Rem. 7.3. Proof: `S` is Gorenstein with trace `B (e⁻¹ 1) (e⁻¹ ·)`; by `lem:s06-S`,
`η(S, μ) = (μ θ)` and `e⁻¹ θ` generates the eigenline, with `B (e⁻¹ θ) (e⁻¹ θ) = μ θ`.) -/
theorem congruenceIdeal_eq_span_pairing [Module.Free A S] [Module.Finite A S] (e : M ≃ₗ[S] S)
    (B : M →ₗ[A] M →ₗ[A] A) (hB : Function.Bijective B)
    (hBs : ∀ (s : S) (m n : M), B (s • m) n = B m (s • n)) (μ : S →ₐ[A] A) (m₀ : M)
    (hm₀ : ∀ m : M, (∀ s : S, s • m = μ s • m) ↔ m ∈ Submodule.span A {m₀}) :
    congruenceIdeal μ = Ideal.span {B m₀ m₀} := by
  have hℓ := isGorensteinWith_of_pairing e B hB hBs
  have hsymm : ∀ (a : A) (x : S), e.symm (a • x) = a • e.symm x := fun a x =>
    (e.symm.restrictScalars A).map_smul a x
  have he : ∀ (a : A) (m : M), e (a • m) = a • e m := fun a m => (e.restrictScalars A).map_smul a m
  set ℓ := traceOfPairing e B
  set θ := LemmaS.theta hℓ μ
  -- `e m₀ ∈ S[μ]`, so `e m₀ = c • θ`
  have hm₀mem : ∀ s : S, s • m₀ = μ s • m₀ := (hm₀ m₀).2 (Submodule.mem_span_singleton_self m₀)
  have hem₀ : e m₀ ∈ ann (RingHom.ker μ) := by
    refine mem_ann.2 fun k hk => ?_
    rw [mul_comm, ← smul_eq_mul, ← e.map_smul, hm₀mem, RingHom.mem_ker.1 hk, zero_smul,
      map_zero]
  set c := ℓ (e m₀)
  have hc : e m₀ = c • θ := LemmaS.eq_smul_theta_of_mem hℓ μ hem₀
  -- `e⁻¹ θ` lies on the eigenline, so `e⁻¹ θ = a • m₀`
  have hθ : ∀ s : S, s • e.symm θ = μ s • e.symm θ := by
    intro s
    have hs : s * θ = μ s • θ := by
      have hk : s - algebraMap A S (μ s) ∈ RingHom.ker μ := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
          sub_self]
      have h0 : θ * (s - algebraMap A S (μ s)) = 0 :=
        mem_ann.1 (LemmaS.theta_mem_ann_ker hℓ μ) _ hk
      rw [mul_sub, sub_eq_zero] at h0
      rw [mul_comm, h0, Algebra.smul_def, mul_comm]
    rw [← e.symm.map_smul, smul_eq_mul, hs, hsymm]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 ((hm₀ (e.symm θ)).1 hθ)
  -- `a c = 1`
  have hac : (a * c) • θ = (1 : A) • θ := by
    rw [one_smul, mul_smul, ← hc, ← he, ha, LinearEquiv.apply_symm_apply]
  have hunit : IsUnit c :=
    IsUnit.of_mul_eq_one_right a (LemmaS.smul_theta_injective hℓ μ hac)
  -- `B m₀ m₀ = c² μ θ`
  have hm₀eq : m₀ = c • e.symm θ := by
    rw [← hsymm, ← hc, LinearEquiv.symm_apply_apply]
  have hB₀ : B m₀ m₀ = (c * c) * μ θ := by
    rw [hm₀eq, map_smul, map_smul, LinearMap.smul_apply, pairing_symm_symm e B hBs,
      LemmaS.trace_theta_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  rw [LemmaS.congruenceIdeal_eq_span hℓ μ, hB₀,
    Ideal.span_singleton_mul_left_unit (hunit.mul hunit)]

end EtaPrinciple

end Langlandscape.CommAlg
