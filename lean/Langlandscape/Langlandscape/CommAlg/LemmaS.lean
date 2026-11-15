/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein

/-!
# Lemma S without base change (S06-L2)

`mathematics/chapters/s06/s06-m1.tex`, `lem:s06-S` (seed Lemma S), the part without base change
(the base-change part is S06-L13).
Secondary reference: `plan/staged/stage-06-integral-defect.tex`. Let `S` be `A`-Gorenstein with
trace `ℓ` and `μ : S → A` an `A`-algebra map. Then

* `LemmaS.theta hℓ μ` is the unique `θ ∈ S` with `ℓ (θ * x) = μ x` for all `x`
  (`LemmaS.trace_theta_mul`);
* `LemmaS.ann_ker_eq_span`: `S[μ] = Ann_S(ker μ) = (θ)`, and
  `LemmaS.ann_ker_restrictScalars_eq_span`: as an `A`-module it is `A θ`, free of rank one
  (`LemmaS.smul_theta_injective`);
* `LemmaS.congruenceIdeal_eq_span`: `η(S, μ) = (μ θ)` is principal.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

namespace LemmaS

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (μ : S →ₐ[A] A)

/-- `lem:s06-S` (`s06-S`): the generator `θ` of `S[μ] = Ann_S(ker μ)`, defined as the unique
`θ ∈ S` with `ℓ (θ ·) = μ` (it exists and is unique because `ℓ` is a trace). -/
noncomputable def theta : S := (hℓ.bijective.2 (μ : S →ₗ[A] A)).choose

/-- `lem:s06-S` (`s06-S`): `ℓ (θ x) = μ x` for all `x ∈ S`. -/
theorem trace_theta_mul (x : S) : ℓ (theta hℓ μ * x) = μ x := by
  have h := LinearMap.congr_fun (hℓ.bijective.2 (μ : S →ₗ[A] A)).choose_spec x
  rw [mulDual_apply_apply] at h
  exact h

/-- `lem:s06-S` (`s06-S`): `θ` is the unique element with `ℓ (θ ·) = μ`. -/
theorem theta_unique {t : S} (ht : ∀ x, ℓ (t * x) = μ x) : t = theta hℓ μ := by
  apply hℓ.bijective.1
  ext x
  rw [mulDual_apply_apply, mulDual_apply_apply, ht, trace_theta_mul]

/-- `lem:s06-S` (`s06-S`): `θ ∈ Ann_S(ker μ)`. -/
theorem theta_mem_ann_ker : theta hℓ μ ∈ ann (RingHom.ker μ) := by
  refine mem_ann.2 fun k hk => hℓ.eq_zero_of_forall fun x => ?_
  rw [mul_assoc, trace_theta_mul, map_mul, RingHom.mem_ker.1 hk, zero_mul]

/-- `lem:s06-S` (`s06-S`): every `x ∈ Ann_S(ker μ)` is `ℓ(x) θ`. -/
theorem eq_smul_theta_of_mem {x : S} (hx : x ∈ ann (RingHom.ker μ)) : x = ℓ x • theta hℓ μ := by
  apply hℓ.bijective.1
  ext y
  rw [mulDual_apply_apply, mulDual_apply_apply, smul_mul_assoc, map_smul, trace_theta_mul,
    smul_eq_mul]
  have hk : y - algebraMap A S (μ y) ∈ RingHom.ker μ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have h0 : x * (y - algebraMap A S (μ y)) = 0 := mem_ann.1 hx _ hk
  have hxy : x * y = μ y • x := by
    rw [mul_sub, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def, mul_comm]
  rw [hxy, map_smul, smul_eq_mul, mul_comm]

/-- `lem:s06-S` (`s06-S`): `S[μ] := Ann_S(ker μ)` is the principal ideal `(θ)`. -/
theorem ann_ker_eq_span : ann (RingHom.ker μ) = Ideal.span {theta hℓ μ} := by
  apply le_antisymm
  · intro x hx
    rw [eq_smul_theta_of_mem hℓ μ hx, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.span_le.2 (Set.singleton_subset_iff.2 (theta_mem_ann_ker hℓ μ))

/-- `lem:s06-S` (`s06-S`): as an `A`-module, `S[μ] = A θ`. -/
theorem ann_ker_restrictScalars_eq_span :
    (ann (RingHom.ker μ)).restrictScalars A = Submodule.span A {theta hℓ μ} := by
  apply le_antisymm
  · intro x hx
    rw [eq_smul_theta_of_mem hℓ μ hx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (theta_mem_ann_ker hℓ μ))

/-- `lem:s06-S` (`s06-S`): `ℓ θ = 1`. -/
theorem trace_theta : ℓ (theta hℓ μ) = 1 := by
  simpa using trace_theta_mul hℓ μ 1

/-- `lem:s06-S` (`s06-S`): `S[μ] = A θ` is free of rank one: `a ↦ a θ` is injective
(indeed `ℓ (a θ) = a`). -/
theorem smul_theta_injective : Function.Injective (fun a : A => a • theta hℓ μ) := by
  intro a b hab
  have h := congrArg ℓ hab
  simpa only [map_smul, trace_theta hℓ μ, smul_eq_mul, mul_one] using h

/-- `lem:s06-S` (`s06-S`): the congruence ideal is principal, `η(S, μ) = (μ θ)`. -/
theorem congruenceIdeal_eq_span : congruenceIdeal μ = Ideal.span {μ (theta hℓ μ)} := by
  unfold congruenceIdeal
  rw [ann_ker_eq_span hℓ μ, Ideal.map_span, Set.image_singleton]

end LemmaS

end Langlandscape.CommAlg
