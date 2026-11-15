/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.TwoVertex

/-!
# Tests for `Graph/TwoVertex.lean` — S03-L3

`prop:s03-phi`: `w = (2,2,2)` gives `|Φ^comb| = 12` and `Φ^comb` is not cyclic (`ℤ/2 × ℤ/6`);
`w = (2,3)` gives `|Φ^comb| = 5`. No native-code evaluation.
-/

namespace LanglandscapeTests.S03.TwoVertex

/-- Two vertices, three edges `false → true`, all weights `2` (`prop:s03-phi`). -/
abbrev G222 : Langlandscape.Graph.WGraph where
  V := Bool
  E := Fin 3
  src _ := false
  tgt _ := true
  w _ := 2
  hw _ := by decide

/-- Two vertices, two edges `false → true`, weights `(2, 3)` (`prop:s03-phi`). -/
abbrev G23 : Langlandscape.Graph.WGraph where
  V := Bool
  E := Fin 2
  src _ := false
  tgt _ := true
  w := ![2, 3]
  hw := by decide

/-- `prop:s03-phi` (`s03-phi`): `X(G) = ℤ[E]⁰` for `w = (2,2,2)`. -/
theorem X_G222 : G222.X = Langlandscape.Graph.deg0 (Fin 3) ℤ :=
  Langlandscape.Graph.twoVertex_X_eq_deg0 G222 (v₀ := false) (v₁ := true) Bool.false_ne_true
    (fun _ => rfl) (fun _ => rfl)

/-- `prop:s03-phi` (`s03-phi`): `|Φ^comb| = 12` for `w = (2,2,2)`. -/
theorem card_G222 : Nat.card G222.PhiComb = 12 := by
  rw [Langlandscape.Graph.card_phiComb_twoVertex G222 (v₀ := false) (v₁ := true)
    Bool.false_ne_true (fun _ => rfl) (fun _ => rfl)]
  decide

/-- `prop:s03-phi` (`s03-phi`): `|Φ^comb| = 5` for `w = (2,3)`. -/
theorem card_G23 : Nat.card G23.PhiComb = 5 := by
  rw [Langlandscape.Graph.card_phiComb_twoVertex G23 (v₀ := false) (v₁ := true)
    Bool.false_ne_true (fun _ => rfl) (fun _ => rfl)]
  decide

/-- `prop:s03-phi` (`s03-phi`): for `w = (2,2,2)`, `6 y ∈ W·ℤ[E]⁰ + ℤ𝟏`
(`6 y = 2 (3 y − (Σ y) 𝟏) + 2 (Σ y) 𝟏`). -/
theorem six_nsmul_mem (y : Fin 3 → ℤ) :
    (6 : ℕ) • y ∈ Langlandscape.Graph.twoVertexRel (fun _ : Fin 3 => 2) := by
  rw [Langlandscape.Graph.twoVertexRel, Submodule.mem_sup]
  let x : Fin 3 →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun e => 3 * y e - ∑ k, y k)
  have hx : x ∈ Langlandscape.Graph.deg0 (Fin 3) ℤ := by
    rw [Langlandscape.Graph.twoVertex_mem_deg0_iff]
    simp only [x, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_three]
    ring
  refine ⟨Langlandscape.Graph.wMul (fun _ : Fin 3 => 2) x, Submodule.mem_map_of_mem hx,
    (2 * ∑ k, y k) • (1 : Fin 3 → ℤ),
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
  funext e
  simp only [Pi.add_apply, Langlandscape.Graph.wMul_apply, x, Finsupp.coe_equivFunOnFinite_symm,
    Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, nsmul_eq_mul, Fin.sum_univ_three]
  push_cast
  ring

/-- `prop:s03-phi` (`s03-phi`): every element of `Φ^comb` for `w = (2,2,2)` is killed by `6`. -/
theorem six_nsmul_eq_zero (x : G222.PhiComb) : (6 : ℕ) • x = 0 := by
  let e := Langlandscape.Graph.phiComb_twoVertex_equiv G222 (v₀ := false) (v₁ := true)
    Bool.false_ne_true (fun _ => rfl) (fun _ => rfl)
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ (e x)
  have h : e ((6 : ℕ) • x) = 0 := by
    rw [map_nsmul, ← hy, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact six_nsmul_mem y
  exact e.injective (h.trans (map_zero e).symm)

/-- `prop:s03-phi` (`s03-phi`): for `w = (2,2,2)`, `Φ^comb` (of order 12, exponent dividing 6)
is not cyclic. -/
theorem not_isAddCyclic_G222 : ¬ IsAddCyclic G222.PhiComb := by
  intro hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := G222.PhiComb)
  have hord : addOrderOf g = 12 := by
    rw [addOrderOf_eq_card_of_forall_mem_zmultiples hg, card_G222]
  have hdvd : addOrderOf g ∣ 6 := addOrderOf_dvd_of_nsmul_eq_zero (six_nsmul_eq_zero g)
  rw [hord] at hdvd
  exact absurd hdvd (by decide)

/-- `prop:s03-phi` (`s03-phi`): the unit-weight equivalence typechecks (one edge, `ℤ/1`). -/
noncomputable example :
    (Langlandscape.Graph.collapse2 ⟨Unit, Unit, Unit, fun _ => (), fun _ => ()⟩).PhiComb ≃+
      ZMod (Fintype.card Unit) :=
  Langlandscape.Graph.phiComb_twoVertex_unit _ (v₀ := false) (v₁ := true) Bool.false_ne_true
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end LanglandscapeTests.S03.TwoVertex
