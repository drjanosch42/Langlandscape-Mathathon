/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Two-vertex weighted graphs — S03-L3

For a weighted graph with two vertices and every edge oriented `v₀ → v₁`
(`prop:s03-phi`, `mathematics/chapters/s03/1-graphs.tex`):

* `twoVertex_X_eq_deg0`: `X(G) = ℤ[E]⁰`;
* `phiComb_twoVertex_equiv`: `Φ^comb(G) ≃ ℤ^E ⧸ (W·ℤ[E]⁰ + ℤ𝟏)` (`twoVertexRel`);
* `card_phiComb_twoVertex`: `|Φ^comb(G)| = Σ_e ∏_{e' ≠ e} w_{e'}`;
* `phiComb_twoVertex_unit`: for all `w_e = 1`, `Φ^comb(G) ≃ ℤ/|E|`.

The order is computed with an explicit injective endomorphism `twoVertexMap` of `ℤ^E` whose
range is `W·ℤ[E]⁰ + ℤ𝟏` (the parametrisation `y ↦ (y − (Σy)𝟏_{e₀}, Σy)` of `ℤ[E]⁰ × ℤ`),
`Submodule.natAbs_det_basis_change` (the submodule form of `AddSubgroup.index_eq_natAbs_det`,
`Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean`), and the matrix determinant lemma
over `ℚ` (its matrix is `diag(w) + u 𝟏ᵀ`).

Status: formalized (Mathlib + S03-L1). Edges are nonempty (`[Nonempty E]`), as in the tex proof.
-/

namespace Langlandscape.Graph

open Finsupp

section Linear

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Membership in `ℤ[E]⁰` (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertex_mem_deg0_iff (x : E →₀ ℤ) : x ∈ deg0 E ℤ ↔ ∑ e, x e = 0 := by
  rw [deg0, LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · simp only [smul_eq_mul, mul_one]
  · intro _
    exact zero_smul _ _

/-- `𝟏_e − 𝟏_{e₀}` has degree zero (`prop:s03-phi`, `s03-phi`). -/
theorem single_sub_single_mem_deg0 (e e₀ : E) :
    (Finsupp.single e (1 : ℤ) - Finsupp.single e₀ 1) ∈ deg0 E ℤ := by
  rw [twoVertex_mem_deg0_iff]
  simp [Finsupp.single_apply, Finset.sum_sub_distrib]

/-- Multiplication by `W = diag(w_e)`, chains to cochains: `(W x)_e = w_e x_e`. -/
noncomputable def wMul (w : E → ℕ) : (E →₀ ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun x e := (w e : ℤ) * x e
  map_add' x y := by
    funext e
    simp only [Finsupp.coe_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    funext e
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Value of `W x` (`prop:s03-phi`, `s03-phi`). -/
theorem wMul_apply (w : E → ℕ) (x : E →₀ ℤ) (e : E) : wMul w x e = (w e : ℤ) * x e := rfl

/-- The relation lattice `W·ℤ[E]⁰ + ℤ𝟏 ⊆ ℤ^E` of `prop:s03-phi`. -/
noncomputable def twoVertexRel (w : E → ℕ) : Submodule ℤ (E → ℤ) :=
  (deg0 E ℤ).map (wMul w) ⊔ Submodule.span ℤ {(1 : E → ℤ)}

/-- The evaluation pairing `ℤ^E × ℤ[E] → ℤ`, `(φ, x) ↦ Σ_e φ_e x_e`. -/
noncomputable def cochainPairing : (E → ℤ) →ₗ[ℤ] (E →₀ ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun φ x => ∑ e, φ e * x e)
    (fun φ ψ x => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c φ x => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun φ x y => by simp only [Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c φ x => by
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

/-- Restriction `ℤ^E = Hom(ℤ[E], ℤ) → Hom(X, ℤ)` of cochains to a sublattice `X`. -/
noncomputable def twoVertexRestr (X : Submodule ℤ (E →₀ ℤ)) : (E → ℤ) →ₗ[ℤ] Module.Dual ℤ X :=
  cochainPairing.compl₂ X.subtype

/-- Value of the restriction (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexRestr_apply (X : Submodule ℤ (E →₀ ℤ)) (φ : E → ℤ) (x : X) :
    twoVertexRestr X φ x = ∑ e, φ e * (x : E →₀ ℤ) e := rfl

/-- The weighted pairing in coordinates (`def:s03-graph`, `s03-graph`). -/
theorem wPairing_apply_eq_sum (w : E → ℕ) (x y : E →₀ ℤ) :
    wPairing w x y = ∑ e, (w e : ℤ) * x e * y e := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply, hf, hg, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [Finsupp.add_apply]; ring
  | single a b =>
    rw [wPairing_single]
    simp [Finsupp.single_apply, mul_ite, ite_mul] <;> ring

/-- `x ↦ ⟨x, ·⟩_w` is restriction of `W x` (`prop:s03-phi`, `s03-phi`). -/
theorem wDualMap_eq_restr (w : E → ℕ) (X : Submodule ℤ (E →₀ ℤ)) (x : X) :
    wDualMap w X x = twoVertexRestr X (wMul w x) := by
  refine LinearMap.ext fun y => ?_
  rw [twoVertexRestr_apply]
  simp only [wDualMap, LinearMap.compl₁₂_apply, Submodule.subtype_apply]
  rw [wPairing_apply_eq_sum]
  rfl

/-- Restriction `ℤ^E → Hom(ℤ[E]⁰, ℤ)` is onto (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexRestr_surjective [Nonempty E] :
    Function.Surjective (twoVertexRestr (deg0 E ℤ)) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  intro ψ
  refine ⟨fun e => ψ ⟨_, single_sub_single_mem_deg0 e e₀⟩, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [twoVertexRestr_apply]
  have hx0 : ∑ e, (x : E →₀ ℤ) e = 0 := (twoVertex_mem_deg0_iff _).mp x.2
  have hx : x = ∑ e, (x : E →₀ ℤ) e •
      (⟨_, single_sub_single_mem_deg0 e e₀⟩ : deg0 E ℤ) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, Submodule.coe_mk, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hx0, zero_smul, sub_zero]
    simp only [Finsupp.smul_single_one, Finsupp.univ_sum_single]
  conv_rhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The kernel of restriction to `ℤ[E]⁰` is `ℤ𝟏` (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexRestr_eq_zero_iff [Nonempty E] (φ : E → ℤ) :
    twoVertexRestr (deg0 E ℤ) φ = 0 ↔ φ ∈ Submodule.span ℤ {(1 : E → ℤ)} := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  constructor
  · intro h
    have h' : ∀ e, φ e - φ e₀ = 0 := by
      intro e
      have := LinearMap.congr_fun h ⟨_, single_sub_single_mem_deg0 e e₀⟩
      rw [twoVertexRestr_apply, LinearMap.zero_apply] at this
      simpa [Finsupp.single_apply, mul_sub, mul_ite, Finset.sum_sub_distrib] using this
    refine Submodule.mem_span_singleton.mpr ⟨φ e₀, funext fun e => ?_⟩
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact (sub_eq_zero.mp (h' e)).symm
  · intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    refine LinearMap.ext fun x => ?_
    rw [twoVertexRestr_apply, LinearMap.zero_apply]
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← Finset.mul_sum, (twoVertex_mem_deg0_iff _).mp x.2, mul_zero]

/-- The composite `ℤ^E → Hom(ℤ[E]⁰, ℤ) → Φ^comb`. -/
noncomputable def twoVertexProj (w : E → ℕ) : (E → ℤ) →ₗ[ℤ] phiComb w (deg0 E ℤ) :=
  (LinearMap.range (wDualMap w (deg0 E ℤ))).mkQ ∘ₗ twoVertexRestr (deg0 E ℤ)

/-- `ℤ^E → Φ^comb` is onto (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexProj_surjective [Nonempty E] (w : E → ℕ) :
    Function.Surjective (twoVertexProj w) :=
  (Submodule.mkQ_surjective _).comp twoVertexRestr_surjective

/-- The kernel of `ℤ^E → Φ^comb` is `W·ℤ[E]⁰ + ℤ𝟏` (`prop:s03-phi`, `s03-phi`). -/
theorem ker_twoVertexProj [Nonempty E] (w : E → ℕ) :
    LinearMap.ker (twoVertexProj w) = twoVertexRel w := by
  ext φ
  rw [LinearMap.mem_ker, twoVertexProj, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, twoVertexRel, Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    rw [wDualMap_eq_restr] at hx
    have h0 : twoVertexRestr (deg0 E ℤ) (φ - wMul w x) = 0 := by rw [map_sub, hx, sub_self]
    exact ⟨wMul w x, Submodule.mem_map_of_mem x.2, φ - wMul w x,
      (twoVertexRestr_eq_zero_iff _).mp h0, by abel⟩
  · rintro ⟨a, ha, z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [wDualMap_eq_restr, map_add, (twoVertexRestr_eq_zero_iff z).mpr hz, add_zero]

/-- `Φ^comb(ℤ[E]⁰) ≃ ℤ^E ⧸ (W·ℤ[E]⁰ + ℤ𝟏)` (`prop:s03-phi`). -/
noncomputable def phiCombDeg0Equiv [Nonempty E] (w : E → ℕ) :
    phiComb w (deg0 E ℤ) ≃ₗ[ℤ] (E → ℤ) ⧸ twoVertexRel w :=
  (LinearMap.quotKerEquivOfSurjective _ (twoVertexProj_surjective w)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_twoVertexProj w))

/-! ### The order: an explicit injective endomorphism with range `W·ℤ[E]⁰ + ℤ𝟏` -/

/-- `y ↦ W (y − (Σ y) 𝟏_{e₀}) + (Σ y) 𝟏`: a bijection `ℤ^E → W·ℤ[E]⁰ + ℤ𝟏`. -/
noncomputable def twoVertexMap (w : E → ℕ) (e₀ : E) : (E → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun y e := (w e : ℤ) * (y e - if e = e₀ then ∑ k, y k else 0) + ∑ k, y k
  map_add' y z := by
    funext e
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' c y := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    split_ifs <;> ring

/-- Value of `twoVertexMap` (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexMap_apply (w : E → ℕ) (e₀ : E) (y : E → ℤ) (e : E) :
    twoVertexMap w e₀ y e = (w e : ℤ) * (y e - if e = e₀ then ∑ k, y k else 0) + ∑ k, y k := rfl

/-- The range of `twoVertexMap` is `W·ℤ[E]⁰ + ℤ𝟏` (`prop:s03-phi`, `s03-phi`). -/
theorem range_twoVertexMap (w : E → ℕ) (e₀ : E) :
    LinearMap.range (twoVertexMap w e₀) = twoVertexRel w := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    rw [twoVertexRel, Submodule.mem_sup]
    let x : E →₀ ℤ :=
      Finsupp.equivFunOnFinite.symm (fun e => y e - if e = e₀ then ∑ k, y k else 0)
    have hx : x ∈ deg0 E ℤ := by
      rw [twoVertex_mem_deg0_iff]
      simp [x, Finset.sum_sub_distrib]
    refine ⟨wMul w x, Submodule.mem_map_of_mem hx, (∑ k, y k) • (1 : E → ℤ),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    funext e
    simp only [Pi.add_apply, wMul_apply, x, Finsupp.coe_equivFunOnFinite_symm, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one, twoVertexMap_apply]
  · rw [twoVertexRel, sup_le_iff]
    constructor
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      refine LinearMap.mem_range.mpr ⟨(x : E → ℤ), funext fun e => ?_⟩
      rw [twoVertexMap_apply, (twoVertex_mem_deg0_iff x).mp hx]
      simp [wMul_apply]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine LinearMap.mem_range.mpr ⟨Pi.single e₀ 1, funext fun e => ?_⟩
      rw [twoVertexMap_apply]
      simp [Pi.single_apply]

/-- Cardinality of `ℤ^E ⧸ f(ℤ^E)` is `|det f|`, via `Submodule.natAbs_det_basis_change`
(`prop:s03-phi`, `s03-phi`). -/
theorem natCard_quot_range (f : (E → ℤ) →ₗ[ℤ] (E → ℤ)) (hf : Function.Injective f) :
    Nat.card ((E → ℤ) ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
  let b := Pi.basisFun ℤ E
  let bN : Module.Basis E ℤ (LinearMap.range f) := b.map (LinearEquiv.ofInjective f hf)
  rw [← Submodule.natAbs_det_basis_change b (LinearMap.range f) bN]
  congr 1
  rw [← mul_one (LinearMap.det f), ← b.det_self, ← Module.Basis.det_comp]
  congr 1

/-- Matrix determinant lemma for `diag(d) + u vᵀ` over a field (`prop:s03-phi`, `s03-phi`). -/
theorem det_diagonal_add_vecMulVec {K : Type*} [Field K] (d u v : E → K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).det =
      (∏ i, d i) * (1 + ∑ i, v i * u i / d i) := by
  have h : Matrix.diagonal d + Matrix.vecMulVec u v =
      Matrix.diagonal d * (1 + Matrix.vecMulVec (fun i => u i / d i) v) := by
    ext i j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_mul,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ (hd i)]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct]
  simp only [mul_div_assoc]

/-- The matrix of `twoVertexMap` over `ℚ` is `diag(w) + u 𝟏ᵀ`, `u = 𝟏 − w_{e₀} 𝟏_{e₀}`
(`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexMap_matrix_cast (w : E → ℕ) (e₀ : E) :
    (LinearMap.toMatrix' (twoVertexMap w e₀)).map (fun x : ℤ => (x : ℚ)) =
      Matrix.diagonal (fun i => (w i : ℚ)) +
        Matrix.vecMulVec (fun i => 1 - if i = e₀ then (w i : ℚ) else 0) (fun _ => 1) := by
  have hsum : ∀ j : E, ∑ k, (Pi.single j (1 : ℤ) : E → ℤ) k = 1 := fun j => by simp
  ext i j
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, twoVertexMap_apply, hsum]
  simp only [Pi.single_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  split_ifs <;> push_cast <;> ring

/-- The rational identity `∏ w · (1 + Σ (1 − [i = e₀] w_i)/w_i) = Σ_e ∏_{e' ≠ e} w_{e'}`
(`prop:s03-phi`, `s03-phi`). -/
theorem twoVertex_det_identity (w : E → ℕ) (hw : ∀ e, 0 < w e) (e₀ : E) :
    (∏ i, (w i : ℚ)) * (1 + ∑ i, (1 : ℚ) * (1 - if i = e₀ then (w i : ℚ) else 0) / (w i : ℚ)) =
      ((∑ e, ∏ e' ∈ Finset.univ.erase e, (w e' : ℤ) : ℤ) : ℚ) := by
  have hwq : ∀ i, (w i : ℚ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (hw i).ne'
  have hterm : ∀ i, (1 : ℚ) * (1 - if i = e₀ then (w i : ℚ) else 0) / (w i : ℚ) =
      1 / (w i : ℚ) - if i = e₀ then 1 else 0 := by
    intro i
    split_ifs
    · rw [one_mul, sub_div, div_self (hwq i)]
    · simp
  have h1 : (1 : ℚ) + ∑ i, (1 : ℚ) * (1 - if i = e₀ then (w i : ℚ) else 0) / (w i : ℚ) =
      ∑ i, 1 / (w i : ℚ) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    ring
  rw [h1, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hp : (w e : ℚ) * ∏ x ∈ Finset.univ.erase e, (w x : ℚ) = ∏ x, (w x : ℚ) :=
    Finset.mul_prod_erase Finset.univ (fun x => (w x : ℚ)) (Finset.mem_univ e)
  rw [← hp, mul_comm (w e : ℚ), mul_assoc, mul_one_div_cancel (hwq e), mul_one]

/-- `det (twoVertexMap) = Σ_e ∏_{e' ≠ e} w_{e'}` (`prop:s03-phi`, `s03-phi`). -/
theorem det_twoVertexMap (w : E → ℕ) (hw : ∀ e, 0 < w e) (e₀ : E) :
    LinearMap.det (twoVertexMap w e₀) = ∑ e, ∏ e' ∈ Finset.univ.erase e, (w e' : ℤ) := by
  have hwq : ∀ i, (w i : ℚ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (hw i).ne'
  rw [← LinearMap.det_toMatrix']
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_det, twoVertexMap_matrix_cast, det_diagonal_add_vecMulVec _ _ _ hwq]
  exact twoVertex_det_identity w hw e₀

/-- `twoVertexMap` is injective (`prop:s03-phi`, `s03-phi`). -/
theorem twoVertexMap_injective [Nonempty E] (w : E → ℕ) (hw : ∀ e, 0 < w e) (e₀ : E) :
    Function.Injective (twoVertexMap w e₀) := by
  have hdet : (LinearMap.toMatrix' (twoVertexMap w e₀)).det ≠ 0 := by
    rw [LinearMap.det_toMatrix', det_twoVertexMap w hw e₀]
    have : 0 < ∑ e, ∏ e' ∈ Finset.univ.erase e, (w e' : ℤ) :=
      Finset.sum_pos (fun e _ => Finset.prod_pos fun e' _ => by exact_mod_cast hw e')
        Finset.univ_nonempty
    exact this.ne'
  intro y z h
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact h

/-- `|ℤ^E ⧸ (W·ℤ[E]⁰ + ℤ𝟏)| = Σ_e ∏_{e' ≠ e} w_{e'}` (`prop:s03-phi`, `s03-phi`). -/
theorem card_quot_twoVertexRel [Nonempty E] (w : E → ℕ) (hw : ∀ e, 0 < w e) :
    Nat.card ((E → ℤ) ⧸ twoVertexRel w) = ∑ e, ∏ e' ∈ Finset.univ.erase e, w e' := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  rw [← range_twoVertexMap w e₀, natCard_quot_range _ (twoVertexMap_injective w hw e₀),
    det_twoVertexMap w hw e₀]
  have : (∑ e, ∏ e' ∈ Finset.univ.erase e, (w e' : ℤ)) =
      ((∑ e, ∏ e' ∈ Finset.univ.erase e, w e' : ℕ) : ℤ) := by
    simp [Nat.cast_sum, Nat.cast_prod]
  rw [this, Int.natAbs_natCast]

/-! ### Unit weights -/

/-- The sum map `ℤ^E → ℤ/n`, `y ↦ Σ_e y_e mod n`. -/
noncomputable def sumZMod (n : ℕ) : (E → ℤ) →ₗ[ℤ] ZMod n where
  toFun y := ((∑ k, y k : ℤ) : ZMod n)
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum]

/-- Value of `sumZMod` (`prop:s03-phi`, `s03-phi`). -/
theorem sumZMod_apply (n : ℕ) (y : E → ℤ) :
    sumZMod n y = ((∑ k, y k : ℤ) : ZMod n) := rfl

/-- `sumZMod` is onto (`prop:s03-phi`, `s03-phi`). -/
theorem sumZMod_surjective [Nonempty E] (n : ℕ) :
    Function.Surjective (sumZMod (E := E) n) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  intro k
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
  exact ⟨Pi.single e₀ m, by rw [sumZMod_apply]; simp⟩

/-- For unit weights, `ker (Σ mod |E|) = ℤ[E]⁰ + ℤ𝟏` (`prop:s03-phi`, `s03-phi`). -/
theorem ker_sumZMod (w : E → ℕ) (hw1 : ∀ e, w e = 1) :
    LinearMap.ker (sumZMod (E := E) (Fintype.card E)) = twoVertexRel w := by
  ext y
  rw [LinearMap.mem_ker, twoVertexRel, Submodule.mem_sup]
  constructor
  · intro h
    rw [sumZMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨c, hc⟩ := h
    let x : E →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun e => y e - c)
    have hx : x ∈ deg0 E ℤ := by
      rw [twoVertex_mem_deg0_iff]
      simp [x, Finset.sum_sub_distrib, hc]
    refine ⟨wMul w x, Submodule.mem_map_of_mem hx, c • (1 : E → ℤ),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    funext e
    simp [wMul_apply, x, hw1]
  · rintro ⟨a, ha, z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [sumZMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨c, ?_⟩
    simp only [Pi.add_apply, wMul_apply, hw1, Nat.cast_one, one_mul, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [(twoVertex_mem_deg0_iff x).mp hx, zero_add]

end Linear

/-! ### Two-vertex weighted graphs -/

/-- Transport of `Φ^comb` along an equality of lattices. -/
noncomputable def phiCombCongr {E : Type*} (w : E → ℕ) {X X' : Submodule ℤ (E →₀ ℤ)}
    (h : X = X') : phiComb w X ≃ₗ[ℤ] phiComb w X' := by
  subst h
  exact LinearEquiv.refl ℤ _

/-- `prop:s03-phi`: for a graph whose edges all run `v₀ → v₁` (`v₀ ≠ v₁`), `X(G) = ℤ[E]⁰`
(`s03-phi`). -/
theorem twoVertex_X_eq_deg0 (G : WGraph) [Fintype G.E] {v₀ v₁ : G.V} (hv : v₀ ≠ v₁)
    (hsrc : ∀ e, G.src e = v₀) (htgt : ∀ e, G.tgt e = v₁) :
    G.X = deg0 G.E ℤ := by
  classical
  have hb : ∀ x : G.E →₀ ℤ, WGraph.boundary G ℤ x =
      (∑ e, x e) • (Finsupp.single v₁ (1 : ℤ) - Finsupp.single v₀ 1) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add, hf, hg, ← add_smul]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    | single a b =>
      rw [WGraph.boundary_single, hsrc, htgt]
      have hs : ∑ e, (Finsupp.single a b : G.E →₀ ℤ) e = b := by simp [Finsupp.single_apply]
      rw [hs, smul_sub, Finsupp.smul_single_one, Finsupp.smul_single_one]
  ext x
  rw [WGraph.X, LinearMap.mem_ker, hb, twoVertex_mem_deg0_iff]
  constructor
  · intro h
    have := congrArg (fun f => f v₁) h
    simpa [Finsupp.single_apply, hv] using this
  · intro h
    rw [h, zero_smul]

/-- `prop:s03-phi`: `Φ^comb(G) ≃ ℤ^E ⧸ (W·ℤ[E]⁰ + ℤ𝟏)` for a two-vertex graph with all edges
`v₀ → v₁`. -/
noncomputable def phiComb_twoVertex_equiv (G : WGraph) [Fintype G.E] [DecidableEq G.E]
    [Nonempty G.E] {v₀ v₁ : G.V} (hv : v₀ ≠ v₁) (hsrc : ∀ e, G.src e = v₀)
    (htgt : ∀ e, G.tgt e = v₁) :
    G.PhiComb ≃ₗ[ℤ] (G.E → ℤ) ⧸ twoVertexRel G.w :=
  (phiCombCongr G.w (twoVertex_X_eq_deg0 G hv hsrc htgt)).trans (phiCombDeg0Equiv G.w)

/-- `prop:s03-phi`: `|Φ^comb(G)| = Σ_e ∏_{e' ≠ e} w_{e'}` for a two-vertex graph with all edges
`v₀ → v₁` (`s03-phi`). -/
theorem card_phiComb_twoVertex (G : WGraph) [Fintype G.E] [DecidableEq G.E] [Nonempty G.E]
    {v₀ v₁ : G.V} (hv : v₀ ≠ v₁) (hsrc : ∀ e, G.src e = v₀) (htgt : ∀ e, G.tgt e = v₁) :
    Nat.card G.PhiComb = ∑ e, ∏ e' ∈ Finset.univ.erase e, G.w e' := by
  rw [Nat.card_congr (phiComb_twoVertex_equiv G hv hsrc htgt).toEquiv,
    card_quot_twoVertexRel G.w G.hw]

/-- `prop:s03-phi`: for unit weights, `Φ^comb(G) ≃ ℤ/|E|` (two-vertex graph, edges `v₀ → v₁`). -/
noncomputable def phiComb_twoVertex_unit (G : WGraph) [Fintype G.E] [DecidableEq G.E]
    [Nonempty G.E] {v₀ v₁ : G.V} (hv : v₀ ≠ v₁) (hsrc : ∀ e, G.src e = v₀)
    (htgt : ∀ e, G.tgt e = v₁) (h1 : ∀ e, G.w e = 1) :
    G.PhiComb ≃+ ZMod (Fintype.card G.E) :=
  ((phiComb_twoVertex_equiv G hv hsrc htgt).trans
    ((Submodule.quotEquivOfEq _ _ (ker_sumZMod G.w h1).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (sumZMod_surjective _)))).toAddEquiv

end Langlandscape.Graph
