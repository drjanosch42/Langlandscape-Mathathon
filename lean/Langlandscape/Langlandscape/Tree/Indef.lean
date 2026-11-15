/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.TwoTerm

/-!
# The tree model of the indefinite stage (S02-L9)

`plan/staged/stage-02-tree-quotients.tex`: `def:s02-indef`, `if:s02-indef` (deviation D1);
`mathematics/chapters/s02/3-cohomology.tex`.

* `Xindef d q hq U hU := H_1(BG(U, q), ℤ)`, the `ℤ`-model `𝒳^{(q)}_{Dq}(U)` of `if:s02-indef` (D1: over `ℤ` the
  graph homology, not `H_1(Γ_U, ℤ)`, which may have torsion).
* `XindefR d q hq U R := ker ∂ ⊆ R[X(U_0(q)U)]` (trivial coefficients `R`, no `q`-level hypothesis);
  `XindefR_eq_H1` : it is `H_1(BG(U, q), R)`.
* `finrank_Xindef_of_connected` : for connected `BG(U, q)`,
  `rk 𝒳^{(q)}_{Dq}(U) + 2 |X_B(U)| = |X_B(U_0(q)U)| + 1` (`def:s02-indef`, "Ranks").

Status: *formalized* (the rank formula from `Graph.finrank_H1_of_connected`, S02-L8).
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Brandt

/-- `def:s02-indef`, `if:s02-indef` (D1): the `ℤ`-model of the indefinite stage,
`𝒳^{(q)}_{Dq}(U) := H_1(BG(U, q), ℤ)`, a `ℤ`-submodule of `ℤ[X_B(U_0(q)U)]`. -/
noncomputable def Xindef (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (hU : IsQLevel d q hq U) :=
  Langlandscape.Graph.H1 (BG d q hq U hU) ℤ

/-- `def:s02-indef`, `if:s02-indef`: the trivial-coefficient model `ker (∂ = (−s_{0*}, s_{1*})) ⊆ R[X(U_0(q)U)]`
(= `H_1(Γ_U, R)` under (iii) of `prop:s02-BG`, `prop:s02-coh`(b), when the `|Γ_x|` are units in `R`; over `ℤ`,
`H_1(Γ_U, ℤ)` may have torsion and the model is `Xindef`, D1). -/
noncomputable def XindefR (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] :
    Submodule R (ZX (d.U0q q (coprime_of_not_dvd hq) U) R) :=
  LinearMap.ker (partialHom d q hq U R)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-indef` (`s02-indef`): `ker ∂ = H_1(BG(U, q), R)`. -/
theorem XindefR_eq_H1 (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) :
    XindefR d q hq U R = Langlandscape.Graph.H1 (BG d q hq U hU) R :=
  congrArg LinearMap.ker (partialHom_eq_boundary (R := R) hU)

/-- `def:s02-indef` (`s02-indef`): over `ℤ`, `XindefR` is `Xindef`. -/
theorem XindefR_int_eq_Xindef (hU : IsQLevel d q hq U) : XindefR d q hq U ℤ = Xindef d q hq U hU :=
  XindefR_eq_H1 ℤ hU

/-- `def:s02-indef`, `if:s02-indef` (`s02-indef`): for connected `BG(U, q)`,
`rk 𝒳^{(q)}_{Dq}(U) + 2 |X_B(U)| = |X_B(U_0(q)U)| + 1`, i.e. `rk = |X_B(U_0(q)U)| − 2|X_B(U)| + 1`. -/
theorem finrank_Xindef_of_connected (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    Module.finrank ℤ (Xindef d q hq U hU) + 2 * Nat.card (XB U) =
      Nat.card (XB (d.U0q q (coprime_of_not_dvd hq) U)) + 1 := by
  haveI : Finite (BG d q hq U hU).V0 := finite_XB_of_isQLevel hU
  haveI : Finite (BG d q hq U hU).V1 := finite_XB_of_isQLevel hU
  haveI : Finite (BG d q hq U hU).E := finite_XB_U0q hU
  have h := Langlandscape.Graph.finrank_H1_of_connected (G := BG d q hq U hU) (R := ℤ) hc
  have h' : Module.finrank ℤ (Xindef d q hq U hU) + Nat.card (XB U) + Nat.card (XB U) =
      Nat.card (XB (d.U0q q (coprime_of_not_dvd hq) U)) + 1 := h
  omega

end Langlandscape.Tree
