/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Lemma G: Gorenstein from one fibre (S06-L5b)

`mathematics/chapters/s06/s06-m1.tex`, `lem:s06-G` (`s06-G`).

Let `A` be a local ring, `S` finite free over `A`, and `I ⊆ 𝔪_A` an ideal. If `S ⧸ I S` is
`A ⧸ I`-Gorenstein, then `S` is `A`-Gorenstein.

* `isGorenstein_of_isGorenstein_quotient`: the statement. The `A ⧸ I`-algebra structure on
  `S ⧸ I S` is Mathlib's canonical one, `Ideal.Quotient.algebraQuotientMapQuotient`, with
  `IsScalarTower A (A ⧸ I) (S ⧸ I S)` from `Ideal.Quotient.tower_quotient_map_quotient`.
  `I S` is spelled `I.map (algebraMap A S)` throughout, so that these instances apply.

The proof lifts a trace `ℓ̄` of `S ⧸ I S` to `ℓ ∈ S^∨` (`S` is free, hence projective), shows
`S^∨ = S ℓ + I S^∨` and concludes `S^∨ = S ℓ` by Nakayama over `A` (`S^∨` is a finite
`A`-module), then `isGorenstein_iff_cyclic`. Nakayama over `A` suffices, so no statement about `𝔪_A S ≤ jacobson ⊥`
in `S` is needed, and `A` need not be Noetherian.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- `lem:s06-G` (`s06-G`): over a free finite module `S`, a functional `ψ ∈ S^∨` with values in `I`
lies in `I • S^∨`. -/
theorem mem_smul_top_dual_of_forall_mem [Module.Free A S] [Module.Finite A S] (I : Ideal A)
    (ψ : Module.Dual A S) (hψ : ∀ x, ψ x ∈ I) :
    ψ ∈ I • (⊤ : Submodule A (Module.Dual A S)) := by
  classical
  let b := Module.Free.chooseBasis A S
  have hsum : ψ = ∑ i, ψ (b i) • b.dualBasis i := by
    have := Module.Basis.sum_repr b.dualBasis ψ
    simp only [Module.Basis.dualBasis_repr] at this
    exact this.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hψ _) Submodule.mem_top

/-- `lem:s06-G` (`s06-G`), Lemma G: `A` local, `S` finite free over `A`, `I ⊆ 𝔪_A`. If
`S ⧸ I S` is `A ⧸ I`-Gorenstein, then `S` is `A`-Gorenstein. -/
theorem isGorenstein_of_isGorenstein_quotient [IsLocalRing A] [Module.Free A S]
    [Module.Finite A S] (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (h : IsGorenstein (A ⧸ I) (S ⧸ I.map (algebraMap A S))) : IsGorenstein A S := by
  obtain ⟨-, -, ℓbar, hℓbar⟩ := isGorenstein_iff_cyclic.1 h
  -- lift the trace
  let π : A →ₗ[A] A ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let q : S →ₗ[A] S ⧸ I.map (algebraMap A S) :=
    (Ideal.Quotient.mkₐ A (I.map (algebraMap A S))).toLinearMap
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨a, rfl⟩
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property π ((ℓbar.restrictScalars A) ∘ₗ q) hπ
  have hℓx : ∀ x,
      Ideal.Quotient.mk I (ℓ x) = ℓbar (Ideal.Quotient.mk (I.map (algebraMap A S)) x) :=
    fun x => LinearMap.congr_fun hℓ x
  have hfin : Module.Finite A (Module.Dual A S) :=
    Module.Finite.equiv (Module.Free.chooseBasis A S).toDualEquiv
  -- Nakayama
  have hTop : (⊤ : Submodule A (Module.Dual A S)) ≤ LinearMap.range (mulDual ℓ) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) Module.Finite.fg_top
      (hI.trans (IsLocalRing.maximalIdeal_le_jacobson _)) ?_
    intro φ _
    -- `φ` descends to `S ⧸ I S`
    have hker : ∀ y ∈ I.map (algebraMap A S), φ y ∈ I := by
      intro y hy
      have hy' : y ∈ I • (⊤ : Submodule A S) := by
        rw [Ideal.smul_top_eq_map]
        exact hy
      refine Submodule.smul_induction_on (p := fun y => φ y ∈ I) hy' ?_ ?_
      · intro a ha m _
        rw [map_smul, smul_eq_mul]
        exact I.mul_mem_right _ ha
      · intro x y hx hy
        rw [map_add]
        exact I.add_mem hx hy
    let f₀ : S →ₗ[A] A ⧸ I := π ∘ₗ φ
    have hle : (I.map (algebraMap A S)).restrictScalars A ≤ LinearMap.ker f₀ := by
      intro y hy
      exact LinearMap.mem_ker.2 (Ideal.Quotient.eq_zero_iff_mem.2 (hker y hy))
    let f₂ : S ⧸ I.map (algebraMap A S) →ₗ[A] A ⧸ I :=
      ((I.map (algebraMap A S)).restrictScalars A).liftQ f₀ hle ∘ₗ
        (Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A S))).symm.toLinearMap
    let φbar : Module.Dual (A ⧸ I) (S ⧸ I.map (algebraMap A S)) :=
      { toFun := f₂
        map_add' := f₂.map_add
        map_smul' := by
          intro c x
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
          have e1 : (Ideal.Quotient.mk I a) • x = a • x := algebraMap_smul (A ⧸ I) a x
          simp only [RingHom.id_apply]
          rw [e1, f₂.map_smul]
          exact (algebraMap_smul (A ⧸ I) a (f₂ x)).symm }
    have h1 : ∀ x,
        Ideal.Quotient.mk I (φ x) = φbar (Ideal.Quotient.mk (I.map (algebraMap A S)) x) :=
      fun x => rfl
    obtain ⟨sbar, hsbar⟩ := hℓbar φbar
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sbar
    have key : ∀ x, φ x - ℓ (s * x) ∈ I := by
      intro x
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, hℓx, map_mul]
      have h2 : φbar (Ideal.Quotient.mk (I.map (algebraMap A S)) x) =
          ℓbar (Ideal.Quotient.mk (I.map (algebraMap A S)) s *
            Ideal.Quotient.mk (I.map (algebraMap A S)) x) :=
        LinearMap.congr_fun hsbar _
      rw [h2, sub_self]
    have hψ : φ - mulDual ℓ s ∈ I • (⊤ : Submodule A (Module.Dual A S)) :=
      mem_smul_top_dual_of_forall_mem I _ fun x => by
        rw [LinearMap.sub_apply, mulDual_apply_apply]
        exact key x
    exact Submodule.mem_sup.2 ⟨mulDual ℓ s, LinearMap.mem_range_self _ s, φ - mulDual ℓ s, hψ,
      by abel⟩
  refine isGorenstein_iff_cyclic.2 ⟨inferInstance, inferInstance, ℓ, fun φ => ?_⟩
  obtain ⟨s, hs⟩ := hTop (Submodule.mem_top : φ ∈ ⊤)
  exact ⟨s, by rw [← hs]; rfl⟩

end Langlandscape.CommAlg
