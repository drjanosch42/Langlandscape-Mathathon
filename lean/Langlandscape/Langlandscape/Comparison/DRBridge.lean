/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Dictionary
import Langlandscape.Graph.Weighted
import Langlandscape.Quat.Stab
import Langlandscape.Quat.Weights

/-!
# The Deligne-Rapoport bridge for `degZero` (S05-L2b)

Tex: `def:s05-theta`, `def:s03-DR` (`plan/staged/stage-05-comparison-hypothesis.tex`).
Status: *formalized* (a bridge lemma, no new object).

* `DRgraphS d M p s hN`: the two-vertex weighted graph `Graph.WGraph` with edges `X_B(U_s)`, all oriented
  `false → true`, weights `w_x` (the pattern of `Ribet.DRgraph`, which exists only at `Ô^×`).
* `degZero_equiv_graphX : degZero (U_s) ℤ ≃ₗ[ℤ] (DRgraphS ..).X`: both are the sublattice of degree-zero
  chains of `ℤ[X_B(U_s)]` (the boundary of a chain is `deg x · ([true] - [false])`); the equivalence is the identity
  (`degZero_equiv_graphX_apply`).
* `brandtPairing_eq_wPairing`: the Brandt pairing is the weighted pairing of the graph.
-/

open Langlandscape.Quat Langlandscape.Brandt

set_option autoImplicit false

namespace Langlandscape.Comparison

noncomputable section

section Weights

variable (d : DefiniteData)

/-- `def:s05-theta` (`s05-theta`), helper: `w_x ≥ 1` at every level `U ≤ Ô^×` (`-1 ∈ U`: `2 w_x = |Γ_x|`;
`-1 ∉ U`: `w_x = |Γ_x|`; `|Γ_x|` divides `24`). -/
theorem wx_pos_of_le_Ohat {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : U ≤ d.Ohat)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : 0 < wx U x := by
  have hdvd := card_Gam_dvd_24 d.ha d.hb d.O.1 hU x
  have hpos : 0 < Nat.card (Gam U x) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  by_cases h : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) ∈ U
  · have h2 := two_mul_wx h x
    omega
  · rw [wx_eq_card h x]
    exact hpos

end Weights

section Bridge

variable (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D)

/-- `def:s05-theta` (`s05-theta`): the Deligne-Rapoport graph `G_s` at level `U_s = U_1(M p^s)`, as a weighted
graph with two vertices (`false`, `true`), edges `X_B(U_s)` all oriented `false → true`, and weights `w_x`
(`def:s03-DR`; the pattern of `Ribet.DRgraph`, there at `Ô^×` only). -/
@[reducible] def DRgraphS : Langlandscape.Graph.WGraph where
  V := Bool
  E := XB (d.Utower M p s hN)
  src _ := false
  tgt _ := true
  w c := wx (d.Utower M p s hN) (Quotient.out c)
  hw c := wx_pos_of_le_Ohat d (DefiniteData.U1_le_units (d := d) (M * p ^ s) hN) _

/-- `def:s05-theta` (`s05-theta`), helper: the boundary of a chain of `G_s` is `deg x · ([true] - [false])`. -/
theorem boundary_DRgraphS (x : ZX (d.Utower M p s hN) ℤ) :
    Langlandscape.Graph.WGraph.boundary (DRgraphS d M p s hN) ℤ x =
      Ordinary.deg (XB (d.Utower M p s hN)) ℤ x •
        (Finsupp.single (true : Bool) (1 : ℤ) - Finsupp.single (false : Bool) (1 : ℤ)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, add_smul]
  | single c r =>
    rw [Langlandscape.Graph.WGraph.boundary_single]
    simp [smul_sub, Finsupp.smul_single]

/-- `def:s05-theta` (`s05-theta`): the sublattices `degZero (U_s)` and `X(G_s) = ker ∂` of `ℤ[X_B(U_s)]` coincide. -/
theorem degZero_eq_graphX :
    degZero (d.Utower M p s hN) ℤ = (DRgraphS d M p s hN).X := by
  ext x
  rw [mem_degZero, Langlandscape.Graph.WGraph.X, LinearMap.mem_ker, boundary_DRgraphS]
  constructor
  · intro h
    rw [h, zero_smul]
  · intro h
    rcases smul_eq_zero.1 h with h0 | h0
    · exact h0
    · have h1 := congrArg (fun f : Bool →₀ ℤ => f true) h0
      simp at h1

/-- `def:s05-theta` (`s05-theta`): the bridge `degZero (U_s) ≃ₗ[ℤ] X(G_s)` with `X = Graph.WGraph.X` of the
two-vertex Deligne-Rapoport graph (a bridge lemma, not a new object). -/
def degZero_equiv_graphX :
    degZero (d.Utower M p s hN) ℤ ≃ₗ[ℤ] (DRgraphS d M p s hN).X :=
  LinearEquiv.ofEq _ _ (degZero_eq_graphX d M p s hN)

/-- `def:s05-theta` (`s05-theta`): the bridge is the identity on underlying chains. -/
@[simp] theorem degZero_equiv_graphX_apply (x : degZero (d.Utower M p s hN) ℤ) :
    (((degZero_equiv_graphX d M p s hN x : (DRgraphS d M p s hN).X)) :
      (DRgraphS d M p s hN).E →₀ ℤ) = (x : ZX (d.Utower M p s hN) ℤ) :=
  rfl

/-- `def:s05-theta` (`s05-theta`): the Brandt pairing on `ℤ[X_B(U_s)]` is the weighted pairing `Σ_e w_e x_e y_e`
of the graph `G_s`, so the bridge is an isometry. -/
theorem brandtPairing_eq_wPairing (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ x y =
      Langlandscape.Graph.wPairing (DRgraphS d M p s hN).w x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | single c r =>
    rw [Langlandscape.Graph.wPairing_single]
    simp [brandtPairing, Finsupp.lift_apply, Finsupp.sum_single_index, DRgraphS] <;> ring

/-- `def:s05-theta` (`s05-theta`): the bridge is an isometry for the Brandt pairing and the weighted pairing of
`G_s`. -/
theorem degZero_equiv_graphX_isometry (x y : degZero (d.Utower M p s hN) ℤ) :
    Langlandscape.Graph.wPairing (DRgraphS d M p s hN).w
        (degZero_equiv_graphX d M p s hN x : (DRgraphS d M p s hN).E →₀ ℤ)
        (degZero_equiv_graphX d M p s hN y : (DRgraphS d M p s hN).E →₀ ℤ) =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ) (y : ZX (d.Utower M p s hN) ℤ) :=
  (brandtPairing_eq_wPairing d M p s hN _ _).symm

end Bridge

end

end Langlandscape.Comparison
