/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted

/-!
# `Φ^comb` is Eisenstein — S03-L7

Abstract core of `prop:s03-phieis` (steps (2)–(4)): for the two-vertex lattice `X = ℤ[E]⁰`
(`deg0 E ℤ`) and a matrix `B` with row sums `ℓ + 1`, `w_e ∣ B e e'` off the diagonal and
`w_{e'} B e e' = w_e B e' e`, the operator `T = Bᵗ` (homological convention
`[e] ↦ Σ_{e'} B e e' [e']`) acts on `Φ^comb = X^∨ / wDualMap X` and `T − (ℓ+1)` is zero there.

Status: formalized, hypothesis-free (no `Hyp.*`). Never `open Graph`.
-/

namespace Langlandscape.Graph

section Eisenstein

variable {E : Type*} [Fintype E]

/-- The Brandt/Hecke operator on `ℤ[E]`: `(T x) e' = Σ_e x_e B e e'`, i.e.
`[e] ↦ Σ_{e'} B e e' [e']` (`prop:s03-phieis`, `s03-phieis`). -/
noncomputable def heckeMat (B : E → E → ℤ) : (E →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm fun e' => ∑ e, x e * B e e'
  map_add' x y := by
    ext e'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext e'
    simp [Finset.mul_sum, mul_assoc]

/-- Coordinates of `heckeMat` (`prop:s03-phieis`, `s03-phieis`). -/
theorem heckeMat_apply (B : E → E → ℤ) (x : E →₀ ℤ) (e' : E) :
    heckeMat B x e' = ∑ e, x e * B e e' := by
  simp [heckeMat]

/-- Membership in `ℤ[E]⁰` as vanishing of the coordinate sum (`prop:s03-phieis`, `s03-phieis`). -/
theorem eis_mem_deg0_iff (x : E →₀ ℤ) : x ∈ deg0 E ℤ ↔ ∑ e, x e = 0 := by
  unfold deg0
  rw [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · simp
  · intro i
    simp

/-- Coordinates of the weighted pairing (`prop:s03-phieis`, `s03-phieis`). -/
theorem wPairing_apply (w : E → ℕ) (x y : E →₀ ℤ) :
    wPairing w x y = ∑ e, (w e : ℤ) * (x e * y e) := by
  rw [wPairing, Finsupp.linearCombination_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
    ring
  · intro i
    simp

/-- With row sums `c`, `T` preserves `ℤ[E]⁰` (step (3) of `prop:s03-phieis`, `s03-phieis`). -/
theorem heckeMat_mem_deg0 (B : E → E → ℤ) (c : ℤ) (hrow : ∀ e, ∑ e', B e e' = c)
    {x : E →₀ ℤ} (hx : x ∈ deg0 E ℤ) : heckeMat B x ∈ deg0 E ℤ := by
  rw [eis_mem_deg0_iff] at hx ⊢
  simp only [heckeMat_apply]
  have h : ∑ e', ∑ e, x e * B e e' = ∑ e, x e * ∑ e', B e e' := by
    rw [Finset.sum_comm]
    simp [Finset.mul_sum]
  rw [h]
  simp only [hrow]
  rw [← Finset.sum_mul, hx, zero_mul]

/-- The action of `T` on `X^∨ = Dual ℤ (ℤ[E]⁰)`, by precomposition with `T|_X`
(step (3) of `prop:s03-phieis`, `s03-phieis`). -/
noncomputable def heckeDual (B : E → E → ℤ) (c : ℤ) (hrow : ∀ e, ∑ e', B e e' = c) :
    Module.Dual ℤ (deg0 E ℤ) →ₗ[ℤ] Module.Dual ℤ (deg0 E ℤ) :=
  ((heckeMat B).restrict fun _ hx => heckeMat_mem_deg0 B c hrow hx).dualMap

/-- Every functional on `ℤ[E]⁰` is given by a function `ψ : E → ℤ`
(step (3) of `prop:s03-phieis`, `s03-phieis`). -/
theorem dual_deg0_eq_sum (φ : Module.Dual ℤ (deg0 E ℤ)) :
    ∃ ψ : E → ℤ, ∀ y : deg0 E ℤ, φ y = ∑ e, y.1 e * ψ e := by
  by_cases hE : Nonempty E
  · obtain ⟨e0⟩ := hE
    obtain ⟨π, hπ⟩ : ∃ π : (E →₀ ℤ) →ₗ[ℤ] deg0 E ℤ, ∀ y : deg0 E ℤ, π y.1 = y := by
      refine ⟨LinearMap.codRestrict (deg0 E ℤ)
        (LinearMap.id - (Finsupp.linearCombination ℤ fun _ : E => (1 : ℤ)).smulRight
          (Finsupp.single e0 (1 : ℤ))) ?_, ?_⟩
      · intro x
        refine LinearMap.mem_ker.mpr ?_
        simp [Finsupp.linearCombination_single]
      · intro y
        apply Subtype.ext
        have hy : Finsupp.linearCombination ℤ (fun _ : E => (1 : ℤ)) y.1 = 0 := y.2
        show y.1 - (Finsupp.linearCombination ℤ fun _ : E => (1 : ℤ)) y.1 •
          Finsupp.single e0 (1 : ℤ) = y.1
        rw [hy, zero_smul, sub_zero]
    have hsum : ∀ x : E →₀ ℤ, φ (π x) = ∑ e, x e * φ (π (Finsupp.single e 1)) := by
      intro x
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
        simp only [map_add, hf, hg, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
      | single e a =>
        have h : (Finsupp.single e a : E →₀ ℤ) = a • Finsupp.single e 1 := by simp
        have h1 : φ (π (Finsupp.single e a)) = a * φ (π (Finsupp.single e 1)) := by
          rw [h, map_smul, map_smul, smul_eq_mul]
        rw [h1, Finset.sum_eq_single e]
        · simp
        · intro b _ hb
          simp [Finsupp.single_apply, Ne.symm hb]
        · intro hne
          exact absurd (Finset.mem_univ e) hne
    refine ⟨fun e => φ (π (Finsupp.single e 1)), fun y => ?_⟩
    rw [← hsum y.1, hπ]
  · have hE' : IsEmpty E := not_nonempty_iff.mp hE
    refine ⟨fun _ => 0, fun y => ?_⟩
    have h : y = 0 := Subtype.ext (Finsupp.ext fun e => isEmptyElim e)
    simp [h]

variable [DecidableEq E]

/-- Key computation (steps (2)–(4) of `prop:s03-phieis`, `s03-phieis`): for every
`φ ∈ X^∨`, `(T − c) φ` lies in the image of `X → X^∨`. -/
theorem heckeDual_sub_smul_mem_range (w : E → ℕ) (hw : ∀ e, 0 < w e) (B : E → E → ℤ)
    (c : ℤ) (hrow : ∀ e, ∑ e', B e e' = c)
    (hdiv : ∀ e e', e ≠ e' → (w e : ℤ) ∣ B e e')
    (hsym : ∀ e e', (w e' : ℤ) * B e e' = w e * B e' e)
    (φ : Module.Dual ℤ (deg0 E ℤ)) :
    heckeDual B c hrow φ - c • φ ∈ LinearMap.range (wDualMap w (deg0 E ℤ)) := by
  obtain ⟨ψ, hψ⟩ := dual_deg0_eq_sum φ
  -- the quotients `S = B / w` (step (1)/(2))
  obtain ⟨S, hS, hSsym⟩ : ∃ S : E → E → ℤ, (∀ e e', e ≠ e' → (w e : ℤ) * S e e' = B e e') ∧
      (∀ e e', S e e' = S e' e) := by
    refine ⟨fun e e' => if e = e' then 0 else B e e' / w e, ?_, ?_⟩
    · intro e e' hne
      simp only [if_neg hne]
      exact Int.mul_ediv_cancel' (hdiv e e' hne)
    · intro e e'
      by_cases h : e = e'
      · subst h; rfl
      · have h' : e' ≠ e := Ne.symm h
        simp only [if_neg h, if_neg h']
        have h1 := Int.mul_ediv_cancel' (hdiv e e' h)
        have h2 := Int.mul_ediv_cancel' (hdiv e' e h')
        have hpe : (w e : ℤ) ≠ 0 := by exact_mod_cast (hw e).ne'
        have hpe' : (w e' : ℤ) ≠ 0 := by exact_mod_cast (hw e').ne'
        apply mul_left_cancel₀ (mul_ne_zero hpe hpe')
        calc (w e : ℤ) * w e' * (B e e' / w e) = w e' * (w e * (B e e' / w e)) := by ring
          _ = w e' * B e e' := by rw [h1]
          _ = w e * B e' e := hsym e e'
          _ = w e * (w e' * (B e' e / w e')) := by rw [h2]
          _ = (w e : ℤ) * w e' * (B e' e / w e') := by ring
  have hB' : ∀ e e', (w e : ℤ) * (S e e' * (ψ e' - ψ e)) = B e e' * (ψ e' - ψ e) := by
    intro e e'
    by_cases h : e = e'
    · subst h; simp
    · rw [← mul_assoc, hS e e' h]
  -- the preimage `x_e = Σ_{e'} S(e,e') (ψ(e') − ψ(e))`
  obtain ⟨xv, hxv⟩ : ∃ xv : E →₀ ℤ, ∀ e, xv e = ∑ e', S e e' * (ψ e' - ψ e) :=
    ⟨Finsupp.equivFunOnFinite.symm fun e => ∑ e', S e e' * (ψ e' - ψ e), fun e => by simp⟩
  have hxmem : xv ∈ deg0 E ℤ := by
    rw [eis_mem_deg0_iff]
    simp only [hxv]
    have h1 : ∑ e, ∑ e', S e e' * (ψ e' - ψ e) = ∑ e, ∑ e', S e' e * (ψ e - ψ e') :=
      Finset.sum_comm
    have h2 : ∑ e, ∑ e', S e' e * (ψ e - ψ e') = - ∑ e, ∑ e', S e e' * (ψ e' - ψ e) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [hSsym e' e]
      ring
    linarith
  have hT : ∀ y : deg0 E ℤ,
      heckeDual B c hrow φ y = ∑ e', (heckeMat B y.1) e' * ψ e' := by
    intro y
    rw [heckeDual, LinearMap.dualMap_apply]
    exact hψ _
  have hR : ∀ y : deg0 E ℤ, wDualMap w (deg0 E ℤ) ⟨xv, hxmem⟩ y =
      ∑ e, y.1 e * ∑ e', B e e' * (ψ e' - ψ e) := by
    intro y
    have h0 : wDualMap w (deg0 E ℤ) ⟨xv, hxmem⟩ y = wPairing w xv y.1 := rfl
    rw [h0, wPairing_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h3 : (w e : ℤ) * xv e = ∑ e', B e e' * (ψ e' - ψ e) := by
      rw [hxv, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e' _ => hB' e e'
    calc (w e : ℤ) * (xv e * y.1 e) = y.1 e * ((w e : ℤ) * xv e) := by ring
      _ = y.1 e * ∑ e', B e e' * (ψ e' - ψ e) := by rw [h3]
  have hL : ∀ y : deg0 E ℤ, (heckeDual B c hrow φ - c • φ) y =
      ∑ e, y.1 e * ∑ e', B e e' * (ψ e' - ψ e) := by
    intro y
    have e1 : ∑ e', (∑ e, y.1 e * B e e') * ψ e' = ∑ e, y.1 e * ∑ e', B e e' * ψ e' :=
      calc ∑ e', (∑ e, y.1 e * B e e') * ψ e' = ∑ e', ∑ e, y.1 e * B e e' * ψ e' := by
            simp only [Finset.sum_mul]
        _ = ∑ e, ∑ e', y.1 e * B e e' * ψ e' := Finset.sum_comm
        _ = ∑ e, y.1 e * ∑ e', B e e' * ψ e' := by simp only [Finset.mul_sum, mul_assoc]
    have e2 : c * ∑ e, y.1 e * ψ e = ∑ e, y.1 e * ∑ e', B e e' * ψ e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_mul, hrow e]
      ring
    have e3 : ∀ e, ∑ e', B e e' * (ψ e' - ψ e) =
        ∑ e', B e e' * ψ e' - ∑ e', B e e' * ψ e := fun e => by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hT y, hψ y, smul_eq_mul]
    simp only [heckeMat_apply]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [e3, mul_sub]
  exact ⟨⟨xv, hxmem⟩, (LinearMap.ext fun y => (hR y).trans (hL y).symm)⟩

/-- `T` preserves the image of `X → X^∨` (step (3) of `prop:s03-phieis`, `s03-phieis`). -/
theorem heckeDual_mem_range (w : E → ℕ) (hw : ∀ e, 0 < w e) (B : E → E → ℤ)
    (c : ℤ) (hrow : ∀ e, ∑ e', B e e' = c)
    (hdiv : ∀ e e', e ≠ e' → (w e : ℤ) ∣ B e e')
    (hsym : ∀ e e', (w e' : ℤ) * B e e' = w e * B e' e)
    {φ : Module.Dual ℤ (deg0 E ℤ)} (hφ : φ ∈ LinearMap.range (wDualMap w (deg0 E ℤ))) :
    heckeDual B c hrow φ ∈ LinearMap.range (wDualMap w (deg0 E ℤ)) := by
  have h := heckeDual_sub_smul_mem_range w hw B c hrow hdiv hsym φ
  rw [← sub_add_cancel (heckeDual B c hrow φ) (c • φ)]
  exact add_mem h (Submodule.smul_mem _ c hφ)

/-- The operator `T` on `Φ^comb = X^∨ / wDualMap X` of the two-vertex lattice
(step (3) of `prop:s03-phieis`, `s03-phieis`). -/
noncomputable def heckeQ (w : E → ℕ) (hw : ∀ e, 0 < w e) (B : E → E → ℤ) (c : ℤ)
    (hrow : ∀ e, ∑ e', B e e' = c)
    (hdiv : ∀ e e', e ≠ e' → (w e : ℤ) ∣ B e e')
    (hsym : ∀ e e', (w e' : ℤ) * B e e' = w e * B e' e) :
    phiComb w (deg0 E ℤ) →ₗ[ℤ] phiComb w (deg0 E ℤ) :=
  Submodule.mapQ _ _ (heckeDual B c hrow)
    (fun _ hφ => heckeDual_mem_range w hw B c hrow hdiv hsym hφ)

/-- `prop:s03-phieis` (abstract, pointwise): `T` acts on `Φ^comb` of the two-vertex graph as
multiplication by `ℓ + 1`. Hypotheses: row sums `ℓ + 1`, `w_e ∣ B e e'` off the diagonal,
`w_{e'} B e e' = w_e B e' e`, `w_e > 0`. -/
theorem phiComb_eisenstein_apply (ℓ : ℕ) (w : E → ℕ) (hw : ∀ e, 0 < w e) (B : E → E → ℤ)
    (hrow : ∀ e, ∑ e', B e e' = (ℓ : ℤ) + 1)
    (hdiv : ∀ e e', e ≠ e' → (w e : ℤ) ∣ B e e')
    (hsym : ∀ e e', (w e' : ℤ) * B e e' = w e * B e' e) (q : phiComb w (deg0 E ℤ)) :
    heckeQ w hw B ((ℓ : ℤ) + 1) hrow hdiv hsym q = ((ℓ : ℤ) + 1) • q := by
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [heckeQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact heckeDual_sub_smul_mem_range w hw B _ hrow hdiv hsym φ

/-- `prop:s03-phieis` (abstract): `T − (ℓ + 1) = 0` on `Φ^comb` of the two-vertex graph
(`E → ℤ` lattice `ℤ[E]⁰`, weights `w`). Hypothesis-free apart from the arithmetic conditions on `B`. -/
theorem phiComb_eisenstein (ℓ : ℕ) (w : E → ℕ) (hw : ∀ e, 0 < w e) (B : E → E → ℤ)
    (hrow : ∀ e, ∑ e', B e e' = (ℓ : ℤ) + 1)
    (hdiv : ∀ e e', e ≠ e' → (w e : ℤ) ∣ B e e')
    (hsym : ∀ e e', (w e' : ℤ) * B e e' = w e * B e' e) :
    heckeQ w hw B ((ℓ : ℤ) + 1) hrow hdiv hsym - ((ℓ : ℤ) + 1) • LinearMap.id = 0 :=
  LinearMap.ext fun q => by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      phiComb_eisenstein_apply ℓ w hw B hrow hdiv hsym q, sub_self]
    simp

end Eisenstein

end Langlandscape.Graph
