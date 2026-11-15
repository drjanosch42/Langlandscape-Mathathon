/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted

/-!
# Definite level raising: weighted adjoints and `α α†` — S03-L10

Abstract core of `prop:s03-LRdef`. Data: a finite edge type `E` (the set `X_B(U')`), a vertex
type `V` (the set `X_B(U)`), the two degeneracy maps `s₀ s₁ : E → V`, and the index weights
`a₀ a₁ : E → ℤ` (`a_j e = [Γ_{s_j e} : Γ_e]`, taken as *data*; integral because `Γ_e ⊆ Γ_x`).

* `alphaMap s₀ s₁ = (−s₀*, s₁*)` (`ℤ[E] → ℤ[V]²`, sign convention (C1)), equal to stage 02's
  `Graph.boundary` (`alphaMap_eq_boundary`) and to the transported `WGraph.boundary` of `ofBip`.
* `dagger s a [x] = Σ_{e : s e = x} a e • [e]` (the weighted adjoint `s_j†`).
* `alphaDagger = (−s₀†, s₁†)`, `levelT = s₁* ∘ s₀†` (the Brandt operator `T_q`).

Hypotheses (explicit, no instances): fibre sums `Σ_{s_j e = x} a_j e = q + 1` (the degree of the
`q+1`-regular tree quotient) and symmetry `s₀* s₁† = s₁* s₀†` (self-adjointness of `T_q`).

Tex label: `prop:s03-LRdef`. Status: formalized (abstract statement; Mathlib + L1). Never
`open Graph`.
-/

namespace Langlandscape.Graph

open Finsupp

section Core

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- The weighted adjoint `s†` of the pushforward along `s : E → V` with index weights `a`:
`[x] ↦ Σ_{e : s e = x} a e • [e]` (`prop:s03-LRdef`). -/
noncomputable def dagger (s : E → V) (a : E → ℤ) : (V →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun x =>
    ∑ e ∈ Finset.univ.filter (fun e => s e = x), a e • Finsupp.single e (1 : ℤ)

/-- `α = (−s₀*, s₁*) : ℤ[E] → ℤ[V] × ℤ[V]` (sign convention (C1), `prop:s03-LRdef`). -/
noncomputable def alphaMap (s0 s1 : E → V) : (E →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ) × (V →₀ ℤ) :=
  (-(Finsupp.lmapDomain ℤ ℤ s0)).prod (Finsupp.lmapDomain ℤ ℤ s1)

/-- `α† = (−s₀†, s₁†) : ℤ[V]² → ℤ[E]` with index weights `a₀, a₁` as data
(`prop:s03-LRdef`). -/
noncomputable def alphaDagger (s0 s1 : E → V) (a0 a1 : E → ℤ) :
    (V →₀ ℤ) × (V →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) :=
  (-(dagger s0 a0)).coprod (dagger s1 a1)

/-- The Brandt operator `T_q = s₁* ∘ s₀†` on `ℤ[V]` (`prop:s03-LRdef`). -/
noncomputable def levelT (s0 s1 : E → V) (a0 : E → ℤ) : (V →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ s1) ∘ₗ dagger s0 a0

/-- The degree (sum of coefficients) on `ℤ[V]` (`prop:s03-LRdef`). -/
noncomputable def levelDeg (V : Type*) : (V →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ : V => (1 : ℤ)

/-- `prop:s03-LRdef` (`s03-LRdef`): `dagger` on a basis vector. -/
theorem dagger_single (s : E → V) (a : E → ℤ) (x : V) (r : ℤ) :
    dagger s a (Finsupp.single x r) =
      r • ∑ e ∈ Finset.univ.filter (fun e => s e = x), a e • Finsupp.single e (1 : ℤ) := by
  rw [dagger, Finsupp.linearCombination_single]

/-- `prop:s03-LRdef` (`s03-LRdef`): `s_* s† = c` on a basis vector, given fibre sums `c`. -/
theorem push_dagger_single (s : E → V) (a : E → ℤ) (c : ℤ)
    (hf : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s e = x), a e = c) (x : V) (r : ℤ) :
    Finsupp.lmapDomain ℤ ℤ s (dagger s a (Finsupp.single x r)) = c • Finsupp.single x r := by
  rw [dagger_single, map_smul, map_sum]
  have h : ∀ e ∈ Finset.univ.filter (fun e => s e = x),
      Finsupp.lmapDomain ℤ ℤ s (a e • Finsupp.single e (1 : ℤ)) = a e • Finsupp.single x (1 : ℤ) := by
    intro e he
    have hx : s e = x := (Finset.mem_filter.1 he).2
    rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hx]
  rw [Finset.sum_congr rfl h, ← Finset.sum_smul, hf x, smul_comm]
  congr 1
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `prop:s03-LRdef` (`s03-LRdef`): `s_* ∘ s† = c • id` given fibre sums `c`. -/
theorem push_dagger_comp (s : E → V) (a : E → ℤ) (c : ℤ)
    (hf : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s e = x), a e = c) :
    (Finsupp.lmapDomain ℤ ℤ s) ∘ₗ dagger s a = c • (LinearMap.id : (V →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ)) := by
  refine Finsupp.lhom_ext fun x r => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  exact push_dagger_single s a c hf x r

omit [Fintype E] [DecidableEq V] in
/-- `prop:s03-LRdef` (`s03-LRdef`): the degree of a basis vector. -/
theorem levelDeg_single (x : V) (r : ℤ) : levelDeg V (Finsupp.single x r) = r := by
  simp [levelDeg, Finsupp.linearCombination_single]

/-- `prop:s03-LRdef` (`s03-LRdef`): `deg ∘ s† = c • deg` given fibre sums `c`. -/
theorem levelDeg_dagger (s : E → V) (a : E → ℤ) (c : ℤ)
    (hf : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s e = x), a e = c) (v : V →₀ ℤ) :
    levelDeg E (dagger s a v) = c * levelDeg V v := by
  have key : (levelDeg E) ∘ₗ dagger s a = c • levelDeg V := by
    refine Finsupp.lhom_ext fun x r => ?_
    have h1 : ∀ e : E, levelDeg E (a e • Finsupp.single e (1 : ℤ)) = a e := by
      intro e; rw [map_smul, levelDeg_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [dagger_single, map_smul, map_sum, Finset.sum_congr rfl (fun e _ => h1 e), hf x,
      levelDeg_single, smul_eq_mul, smul_eq_mul, mul_comm]
  have := LinearMap.congr_fun key v
  simpa using this

/-- `prop:s03-LRdef` (`s03-LRdef`): symmetry on basis vectors extends to all of `ℤ[V]`. -/
theorem cross_comm (s0 s1 : E → V) (a0 a1 : E → ℤ)
    (hsym : ∀ x, Finsupp.lmapDomain ℤ ℤ s0 (dagger s1 a1 (Finsupp.single x 1)) =
      Finsupp.lmapDomain ℤ ℤ s1 (dagger s0 a0 (Finsupp.single x 1))) (u : V →₀ ℤ) :
    Finsupp.lmapDomain ℤ ℤ s0 (dagger s1 a1 u) = levelT s0 s1 a0 u := by
  have key : (Finsupp.lmapDomain ℤ ℤ s0) ∘ₗ dagger s1 a1 = levelT s0 s1 a0 := by
    refine Finsupp.lhom_ext fun x r => ?_
    have h : (Finsupp.single x r : V →₀ ℤ) = r • Finsupp.single x 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [levelT, LinearMap.comp_apply]
    rw [h]
    simp only [map_smul, hsym x]
  exact LinearMap.congr_fun key u

/-- `prop:s03-LRdef` (`s03-LRdef`): `α†` maps `(ℤ[V]⁰)²` into `ℤ[E]⁰`, given the fibre sums
`Σ_{s_j e = x} a_j e = q + 1` (so `deg ∘ s_j† = (q+1) deg`). -/
theorem alphaDagger_deg0 (s0 s1 : E → V) (a0 a1 : E → ℤ) (q : ℤ)
    (hf0 : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s0 e = x), a0 e = q + 1)
    (hf1 : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s1 e = x), a1 e = q + 1)
    (v : (V →₀ ℤ) × (V →₀ ℤ)) (h1 : levelDeg V v.1 = 0) (h2 : levelDeg V v.2 = 0) :
    levelDeg E (alphaDagger s0 s1 a0 a1 v) = 0 := by
  have hA : alphaDagger s0 s1 a0 a1 v = -(dagger s0 a0 v.1) + dagger s1 a1 v.2 := by
    simp [alphaDagger, LinearMap.coprod_apply]
  rw [hA, map_add, map_neg, levelDeg_dagger s0 a0 _ hf0, levelDeg_dagger s1 a1 _ hf1, h1, h2]
  simp

/-- `prop:s03-LRdef` (`s03-LRdef`): `α α† = [[q+1, −T], [−T, q+1]]` on `ℤ[V]²`, where
`T = s₁* ∘ s₀†`; hypotheses: fibre sums `q + 1` for `j = 0, 1` and symmetry
`s₀* s₁† = s₁* s₀†` of `T` (on basis vectors). `hsym` is needed because the two off-diagonal
entries are `s₀* s₁†` and `s₁* s₀†`; they agree iff `T_q = s₁* s₀†` is self-adjoint. This is not
provable in the abstract Graph layer; it is discharged at the quaternionic instantiation. -/
theorem alpha_alphaDagger_eq (s0 s1 : E → V) (a0 a1 : E → ℤ) (q : ℤ)
    (hf0 : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s0 e = x), a0 e = q + 1)
    (hf1 : ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s1 e = x), a1 e = q + 1)
    (hsym : ∀ x, Finsupp.lmapDomain ℤ ℤ s0 (dagger s1 a1 (Finsupp.single x 1)) =
      Finsupp.lmapDomain ℤ ℤ s1 (dagger s0 a0 (Finsupp.single x 1)))
    (v : (V →₀ ℤ) × (V →₀ ℤ)) :
    alphaMap s0 s1 (alphaDagger s0 s1 a0 a1 v) =
      ((q + 1) • v.1 - levelT s0 s1 a0 v.2, (q + 1) • v.2 - levelT s0 s1 a0 v.1) := by
  have hA : alphaDagger s0 s1 a0 a1 v = -(dagger s0 a0 v.1) + dagger s1 a1 v.2 := by
    simp [alphaDagger, LinearMap.coprod_apply]
  have hM : ∀ w, alphaMap s0 s1 w =
      (-(Finsupp.lmapDomain ℤ ℤ s0 w), Finsupp.lmapDomain ℤ ℤ s1 w) := by
    intro w; simp [alphaMap]
  have h00 : ∀ u, Finsupp.lmapDomain ℤ ℤ s0 (dagger s0 a0 u) = (q + 1) • u := fun u => by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (push_dagger_comp s0 a0 (q + 1) hf0) u
  have h11 : ∀ u, Finsupp.lmapDomain ℤ ℤ s1 (dagger s1 a1 u) = (q + 1) • u := fun u => by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (push_dagger_comp s1 a1 (q + 1) hf1) u
  have hx := cross_comm s0 s1 a0 a1 hsym
  have h10 : ∀ u, Finsupp.lmapDomain ℤ ℤ s1 (dagger s0 a0 u) = levelT s0 s1 a0 u := fun u => rfl
  rw [hM, hA]
  refine Prod.ext ?_ ?_
  · simp only [map_add, map_neg, h00, hx]
    abel
  · simp only [map_add, map_neg, h10, h11]
    abel

end Core

/-- `prop:s03-LRdef` (`s03-LRdef`): `alphaMap` is stage 02's boundary `(−s₀*, s₁*)` of the
bipartite multigraph with both vertex types `V` (sign convention (C1)). -/
theorem alphaMap_eq_boundary {V E : Type} (s0 s1 : E → V) :
    alphaMap s0 s1 = boundary (⟨V, V, E, s0, s1⟩ : BipMultigraph) ℤ := by
  refine Finsupp.lhom_ext fun e r => ?_
  rw [boundary_single]
  simp [alphaMap]

/-- `prop:s03-LRdef` (`s03-LRdef`): `alphaMap` is the transported `WGraph.boundary` of
`ofBip` (via `boundary_ofBip`). -/
theorem alphaMap_eq_wboundary {V E : Type} (s0 s1 : E → V) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).toLinearMap ∘ₗ
        WGraph.boundary (ofBip (⟨V, V, E, s0, s1⟩ : BipMultigraph)) ℤ = alphaMap s0 s1 :=
  (boundary_ofBip (⟨V, V, E, s0, s1⟩ : BipMultigraph) ℤ).trans (alphaMap_eq_boundary s0 s1).symm

end Langlandscape.Graph
