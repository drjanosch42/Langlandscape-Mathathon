/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.LemmaS
public import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Base change of Gorenstein algebras and of congruence ideals (S06-L13)

`mathematics/chapters/s06/s06-m1.tex`, `lem:s06-S` (seed Lemma S), the base-change part: for `φ : A
→ A'`, `A' ⊗_A S` is
`A'`-Gorenstein and `η(A' ⊗_A S, μ ⊗ A') = φ(η(S, μ)) A'`. Secondary reference:
`plan/staged/stage-06-integral-defect.tex`.

`IsGorensteinWith.of_surjective` (Orzech property; `lem:s06-cyclic`) lives in `Gorenstein.lean`.
* `IsGorensteinWith.baseChange`: the base change `Module.Dual.baseChange A' ℓ` of a trace is a
  trace.
* `IsGorenstein.baseChange`: `A' ⊗_A S` is `A'`-Gorenstein.
* `LemmaS.theta_baseChange`: the generator `θ` of `S[μ]` base-changes to `1 ⊗ θ`.
* `LemmaS.congruenceIdeal_baseChange`: the congruence ideal commutes with base change. The
  Gorenstein hypothesis is needed: `Ann` does not commute with non-flat base change in general.
  No locality hypothesis on `algebraMap A A'` is needed (the chapter's `φ : A → A'` local is not
  used by the proof), so the statement also covers non-local maps such as `A → A_𝔭`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

open scoped TensorProduct

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

variable (A' : Type*) [CommRing A'] [Algebra A A']

/-- `lem:s06-S` (`s06-S`), base-change part: the base-changed functional
`ℓ' = Module.Dual.baseChange A' ℓ` satisfies `ℓ' ((a ⊗ s) (1 ⊗ t)) = ℓ (s t) • a`. -/
theorem baseChange_trace_mul_tmul (ℓ : Module.Dual A S) (a : A') (s t : S) :
    Module.Dual.baseChange A' ℓ ((a ⊗ₜ[A] s) * (1 ⊗ₜ[A] t)) = ℓ (s * t) • a := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Module.Dual.baseChange_apply_tmul]

/-- `lem:s06-S` (`s06-S`), base-change part: if `ℓ` is a trace of `S` over `A`, then its base change
`Module.Dual.baseChange A' ℓ` is a trace of `A' ⊗_A S` over `A'`. -/
theorem IsGorensteinWith.baseChange {ℓ : Module.Dual A S} (h : IsGorensteinWith A S ℓ) :
    IsGorensteinWith A' (A' ⊗[A] S) (Module.Dual.baseChange A' ℓ) := by
  have := h.1
  have := h.2.1
  apply IsGorensteinWith.of_surjective
  intro φ
  let b := Module.Free.chooseBasis A S
  -- `t i` with `ℓ (t i * x) = b.coord i x`
  have ht : ∀ i, ∃ t : S, ∀ x, b.coord i x = ℓ (t * x) := fun i => h.exists_eq (b.coord i)
  choose t ht using ht
  refine ⟨∑ i, φ (1 ⊗ₜ[A] b i) • (1 ⊗ₜ[A] t i), ?_⟩
  apply (b.baseChange A').ext
  intro j
  rw [Module.Basis.baseChange_apply, mulDual_apply_apply, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_smul, baseChange_trace_mul_tmul, ← ht, Module.Basis.coord_apply,
    Module.Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- `lem:s06-S` (`s06-S`), base-change part: if `S` is finite free and `A`-Gorenstein, then
`A' ⊗_A S` is finite free and `A'`-Gorenstein, for any `A`-algebra `A'`. -/
theorem IsGorenstein.baseChange (h : IsGorenstein A S) : IsGorenstein A' (A' ⊗[A] S) :=
  let ⟨_, hℓ⟩ := h
  ⟨_, hℓ.baseChange A'⟩

namespace LemmaS

variable {A'} {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (μ : S →ₐ[A] A)

/-- `lem:s06-S` (`s06-S`), base-change part: the base change
`μ ⊗ A' : A' ⊗_A S → A'` of `μ` satisfies `(μ ⊗ A') (a ⊗ s) = a φ(μ s)`. -/
theorem liftEquiv_tmul_apply (a : A') (s : S) :
    AlgHom.liftEquiv A A' S A' ((Algebra.ofId A A').comp μ) (a ⊗ₜ[A] s) =
      a * algebraMap A A' (μ s) := by
  rw [AlgHom.liftEquiv_tmul, smul_eq_mul, AlgHom.comp_apply, Algebra.ofId_apply]

/-- `lem:s06-S` (`s06-S`), base-change part: the generator of `(A' ⊗_A S)[μ ⊗ A']` for the
base-changed trace is `1 ⊗ θ`. -/
theorem theta_baseChange :
    theta (hℓ.baseChange A') (AlgHom.liftEquiv A A' S A' ((Algebra.ofId A A').comp μ)) =
      1 ⊗ₜ[A] theta hℓ μ := by
  symm
  apply theta_unique
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul a s =>
    rw [mul_comm, baseChange_trace_mul_tmul, mul_comm s, trace_theta_mul, liftEquiv_tmul_apply,
      Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add]

/-- `lem:s06-S` (`s06-S`), base-change part: for `S` finite free and `A`-Gorenstein with trace `ℓ`
and an `A`-algebra `A'`, the congruence ideal commutes with base change:
`η(A' ⊗_A S, μ ⊗ A') = φ(η(S, μ)) A'`. The Gorenstein hypothesis is required (`Ann` does not
commute with non-flat base change in general). No locality of `φ = algebraMap A A'` is assumed
(`lem:s06-S` states `φ : A → A'` local, but the proof does not use it). -/
theorem congruenceIdeal_baseChange (hℓ : IsGorensteinWith A S ℓ) (μ : S →ₐ[A] A) :
    congruenceIdeal (AlgHom.liftEquiv A A' S A' ((Algebra.ofId A A').comp μ)) =
      (congruenceIdeal μ).map (algebraMap A A') := by
  rw [congruenceIdeal_eq_span (hℓ.baseChange A'), congruenceIdeal_eq_span hℓ, theta_baseChange,
    liftEquiv_tmul_apply, one_mul, Ideal.map_span, Set.image_singleton]

end LemmaS

end Langlandscape.CommAlg
