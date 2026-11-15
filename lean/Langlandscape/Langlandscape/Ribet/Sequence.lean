/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.BipCollapse
import Langlandscape.Tree.Hecke
import Langlandscape.Tree.QuotientCore

/-!
# The definite Ribet sequence on the Brandt graph — S03-L9

`thm:s03-ribet`(a), (c) and `cor:s03-ihara`(i), (ii) for stage 02's `Tree.BG d q hq U hU`, over any
commutative ring `R` (rank over `ℤ`), as specialisations of S03-L2 (`Graph.BipCollapse`):

* `ribet_exact` : `0 → H₁(BG, R) → R[X(U₀(q)U)]⁰ → R[X(U)]⁰ × R[X(U)]⁰ → 0` is exact, where the
  right-hand map is `α = (−s₀*, s₁*)` (`boundary_BG_eq`);
* `ihara_surj` (i) : `α` is surjective on degree-zero parts;
* `ihara_ker_const` (ii) : for every abelian group `A`, `ker α^∨` is the line of constants;
* `ribet_rank` (c) : `rk H₁ = |X(U₀(q)U)| − 2 |X(U)| + 1`;
* `ribet_hecke_equivariant` : `α` commutes with the transposed Hecke operators `T_t^t` for `t`
  supported away from `q` (stage 02 `heckeTHom_comm_s*Push`; no connectivity needed).

Each of the first four is stated under `Tree.BGConnected d q hq U hU`, plus a version
`…_of_SA_HS` under `Hyp.SA`, `Hyp.HS`, `Hyp.BTtree` (stage 02 `Tree.BGConnected_of_SA_HS`).

Tex labels: `thm:s03-ribet`, `cor:s03-ihara`. Status: formalized (given connectivity).
Never `open Graph` (clash with `_root_.Graph`).
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

section

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `thm:s03-ribet`(a) (`s03-ribet`): the boundary of `BG` is `α = (−s₀*, s₁*)`. -/
theorem boundary_BG_eq (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) :
    Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R =
      (-(Tree.s0Push d q hq U R)).prod (Tree.s1Push d q hq U R) := by
  refine Finsupp.lhom_ext fun e r => ?_
  rw [Langlandscape.Graph.boundary_single]
  refine Prod.ext ?_ ?_
  · exact congrArg Neg.neg (Tree.s0Push_single (R := R) e r).symm
  · exact (Tree.s1Push_single (R := R) e r).symm

/-- `thm:s03-ribet`(a) (`s03-ribet`): pointwise form of `boundary_BG_eq`,
`∂ y = (−s₀* y, s₁* y)`. -/
theorem boundary_BG_apply (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (y : (Tree.BG d q hq U hU).E →₀ R) :
    Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R y =
      (-(Tree.s0Push d q hq U R y), Tree.s1Push d q hq U R y) := by
  have h := LinearMap.congr_fun (boundary_BG_eq R hU) y
  first
  | exact h
  | exact h.trans rfl
  | exact h.trans (Prod.ext rfl rfl)

/-- `thm:s03-ribet`(a) (`s03-ribet`): finiteness of the vertex type `V₀` of `BG`. -/
theorem finite_BG_V0 (hU : Tree.IsQLevel d q hq U) : Finite (Tree.BG d q hq U hU).V0 :=
  Tree.finite_XB_of_isQLevel hU

/-- `thm:s03-ribet`(a) (`s03-ribet`): finiteness of the vertex type `V₁` of `BG`. -/
theorem finite_BG_V1 (hU : Tree.IsQLevel d q hq U) : Finite (Tree.BG d q hq U hU).V1 :=
  Tree.finite_XB_of_isQLevel hU

/-- `thm:s03-ribet`(a) (`s03-ribet`): finiteness of the edge type `E` of `BG`. -/
theorem finite_BG_E (hU : Tree.IsQLevel d q hq U) : Finite (Tree.BG d q hq U hU).E :=
  Tree.finite_XB_U0q hU

/-- `thm:s03-ribet`(a) (`s03-ribet`), over any commutative ring `R`, given connectivity:
`0 → H₁(BG, R) → R[X(U₀(q)U)]⁰ → R[X(U)]⁰ × R[X(U)]⁰ → 0` is exact (`α = ∂`, see `boundary_BG_eq`). -/
theorem ribet_exact (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) :
    Function.Injective (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) R) ∧
      Function.Exact (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) R)
        (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) R) ∧
      Function.Surjective (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) R) := by
  haveI := finite_BG_V0 hU
  haveI := finite_BG_V1 hU
  exact Langlandscape.Graph.bip_exact hc

/-- `cor:s03-ihara`(i) (`s03-ihara`), over any commutative ring `R` (in particular `ℤ`), given
connectivity: `α : R[X(U₀(q)U)]⁰ → R[X(U)]⁰ × R[X(U)]⁰` is surjective. -/
theorem ihara_surj (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) :
    Function.Surjective (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) R) :=
  (ribet_exact R hU hc).2.2

/-- `cor:s03-ihara`(ii) (`s03-ihara`), for every abelian group `A`, given connectivity:
`s₁^* f₁ − s₀^* f₀ = 0` iff `(f₀, f₁)` is a pair of equal constants. -/
theorem ihara_ker_const (A : Type*) [AddCommGroup A] (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (f : (XB U → A) × (XB U → A)) :
    Langlandscape.Graph.boundaryDual (Tree.BG d q hq U hU) A f = 0 ↔
      ∃ c : A, f = (fun _ => c, fun _ => c) :=
  Langlandscape.Graph.bip_ker_dual A hc f

/-- `cor:s03-ihara`(ii) (`s03-ihara`): `∂^∨` is `(f₀, f₁) ↦ s₁^* f₁ − s₀^* f₀` for the stage-02 pullbacks. -/
theorem boundaryDual_BG_eq_pull (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (f : (XB U → R) × (XB U → R)) :
    Langlandscape.Graph.boundaryDual (Tree.BG d q hq U hU) R f =
      Tree.s1Pull d q hq U R f.2 - Tree.s0Pull d q hq U R f.1 := by
  funext e
  exact rfl

/-- `thm:s03-ribet`(c) (`s03-ribet`), over `ℤ`, given connectivity:
`rk H₁(BG, ℤ) = |X(U₀(q)U)| − 2 |X(U)| + 1`. -/
theorem ribet_rank (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU) :
    (Module.finrank ℤ (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ) : ℤ) =
      Nat.card (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U)) - 2 * Nat.card (XB U) + 1 := by
  haveI := finite_BG_V0 hU
  haveI := finite_BG_V1 hU
  haveI := finite_BG_E hU
  have h : (Module.finrank ℤ (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ) : ℤ) =
      Nat.card (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U)) - Nat.card (XB U) - Nat.card (XB U) + 1 :=
    Langlandscape.Graph.bip_rank hc
  omega

/-- `thm:s03-ribet`(a) (`s03-ribet`): `α = (−s₀*, s₁*)` is equivariant for the transposed Hecke
operators `T_t^t` with `t` supported away from `q` (no connectivity needed). -/
theorem ribet_hecke_equivariant (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (t : (BHat d.a d.b)ˣ) (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (Tree.coprime_of_not_dvd hq) U ⊓
      conjSub (d.U0q q (Tree.coprime_of_not_dvd hq) U) t).relIndex (d.U0q q (Tree.coprime_of_not_dvd hq) U) ≠ 0)
    [Finite (XB U)] [Finite (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U))] :
    (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R).comp
        (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin') =
      ((heckeTHom U t R hfin).prodMap (heckeTHom U t R hfin)).comp
        (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R) := by
  refine LinearMap.ext fun y => ?_
  have h0 : Tree.s0Push d q hq U R (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y) =
      heckeTHom U t R hfin (Tree.s0Push d q hq U R y) :=
    LinearMap.congr_fun (Tree.heckeTHom_comm_s0Push R hU t ht hfin hfin') y
  have h1 : Tree.s1Push d q hq U R (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y) =
      heckeTHom U t R hfin (Tree.s1Push d q hq U R y) :=
    LinearMap.congr_fun (Tree.heckeTHom_comm_s1Push R hU t ht hfin hfin') y
  have hn : -(Tree.s0Push d q hq U R (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y)) =
      heckeTHom U t R hfin (-(Tree.s0Push d q hq U R y)) :=
    (congrArg Neg.neg h0).trans (map_neg (heckeTHom U t R hfin) (Tree.s0Push d q hq U R y)).symm
  have key : ((-(Tree.s0Push d q hq U R (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y)),
        Tree.s1Push d q hq U R (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y)) :
          ZX U R × ZX U R) =
      ((heckeTHom U t R hfin).prodMap (heckeTHom U t R hfin))
        (-(Tree.s0Push d q hq U R y), Tree.s1Push d q hq U R y) := by
    first
    | exact Prod.ext hn h1
    | (rw [LinearMap.prodMap_apply]; exact Prod.ext hn h1)
  have b1 := boundary_BG_apply R hU (heckeTHom (d.U0q q (Tree.coprime_of_not_dvd hq) U) t R hfin' y)
  have b2 := boundary_BG_apply R hU y
  exact b1.trans (key.trans (congrArg ((heckeTHom U t R hfin).prodMap (heckeTHom U t R hfin)) b2).symm)

end

section SAHS

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `thm:s03-ribet`(a) (`s03-ribet`), stage-02 hypotheses version: `Hyp.SA ∧ Hyp.HS ∧ Hyp.BTtree`
give the exact sequence at every `q`-admissible level. -/
theorem ribet_exact_of_SA_HS (R : Type*) [CommRing R] (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hBT : Langlandscape.Hyp.BTtree q)
    (hU : Tree.IsQAdmissible d q hq U) :
    Function.Injective (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU.1) R) ∧
      Function.Exact (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU.1) R)
        (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU.1) R) ∧
      Function.Surjective (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU.1) R) :=
  ribet_exact R hU.1 (Tree.BGConnected_of_SA_HS hSA hHS hBT hU)

/-- `cor:s03-ihara`(i) (`s03-ihara`), stage-02 hypotheses version. -/
theorem ihara_surj_of_SA_HS (R : Type*) [CommRing R] (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hBT : Langlandscape.Hyp.BTtree q)
    (hU : Tree.IsQAdmissible d q hq U) :
    Function.Surjective (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU.1) R) :=
  ihara_surj R hU.1 (Tree.BGConnected_of_SA_HS hSA hHS hBT hU)

/-- `cor:s03-ihara`(ii) (`s03-ihara`), stage-02 hypotheses version. -/
theorem ihara_ker_const_of_SA_HS (A : Type*) [AddCommGroup A] (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hBT : Langlandscape.Hyp.BTtree q)
    (hU : Tree.IsQAdmissible d q hq U) (f : (XB U → A) × (XB U → A)) :
    Langlandscape.Graph.boundaryDual (Tree.BG d q hq U hU.1) A f = 0 ↔
      ∃ c : A, f = (fun _ => c, fun _ => c) :=
  ihara_ker_const A hU.1 (Tree.BGConnected_of_SA_HS hSA hHS hBT hU) f

/-- `thm:s03-ribet`(c) (`s03-ribet`), stage-02 hypotheses version. -/
theorem ribet_rank_of_SA_HS (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hBT : Langlandscape.Hyp.BTtree q)
    (hU : Tree.IsQAdmissible d q hq U) :
    (Module.finrank ℤ (Langlandscape.Graph.H1 (Tree.BG d q hq U hU.1) ℤ) : ℤ) =
      Nat.card (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U)) - 2 * Nat.card (XB U) + 1 :=
  ribet_rank hU.1 (Tree.BGConnected_of_SA_HS hSA hHS hBT hU)

end SAHS

end Langlandscape.Ribet
