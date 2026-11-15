/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.PadicOrdDecomp
import Langlandscape.Ordinary.KppTower
import Langlandscape.Ribet.Sequence

/-!
# The ordinary Ribet sequence at finite level `s` — S04-L12

`mathematics/chapters/s04/lambdaribet.tex`, `thm:s04-lambdaribet`(a), (c) at level `s`, for `E = ℚ_p` (`𝒪_E = ℤ_p`);
upstream `if:s03-ribet` (`Ribet.ribet_exact`), `if:s02-quot` (`Tree.heckeTHom_comm_s{0,1}Push`).

## Main results

* `ribet_exact_Zp` : stage 03's `Ribet.ribet_exact` at `R = ℤ_[p]` (no base change needed);
* `UpAt_comm_s0`, `UpAt_comm_s1`, `boundary_comm_UpAt` : `U_p` (S04-L9 `UpAt`, i.e. `[U ϖ U]`) commutes with
  `s_{0*}`, `s_{1*}` and `α = (−s_{0*}, s_{1*})` (stage-02 commutation at `g = ϖ`, `p ≠ q`);
* `UpBGE`, `UpBGV0`, `UpBGV1`, `boundary_comm_UpBG` : `U_p` transported once to the `Tree.BG`-typed chain modules
  (pattern of S03-L9 `Ribet.boundary_BG_eq`);
* `UpH1`, `UpDeg0E`, `UpDeg0Prod` : the induced `U_p` on `H₁`, `ℤ_p[X(U₀(q)U)]⁰`, `ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰`
  (restrictions; `H1toDeg0` and `boundaryDeg0` are equivariant: `H1toDeg0_comm_Up`, `boundaryDeg0_comm_Up`);
* `alpha_comm_rightMulXB`, `alpha_comm_diamond` : on full chain modules, `∂ ∘ R_{δ_t} = (⟨t⟩ × ⟨t⟩) ∘ ∂` for the
  diamond action `[x] ↦ [x δ_t]` at `p` (the left side is the bare right multiplication `rightMulXB` on
  `X(U₀(q)U_s)`). **Not stated:** a diamond operator on `X(U₀(q)U_s)` as a permutation, its commutation with `U_p` at
  `U₀(q)U_s` (`lem:s01-Up`(e) at that level), hence no `Δ_s`-action on the terms of the ordinary sequence and no
  `Δ_s`-linearity of `ordAlpha`;
* `ordH1toDeg0`, `ordAlpha` : the maps of the ordinary sequence (`ordRestrict`);
* `ordRibet_exact`, `ordRibet_exact_Utower` : `0 → e H₁ → e ℤ_p[X(U₀(q)U_s)]⁰ → e (ℤ_p[X_s]⁰)² → 0` is exact,
  under connectivity of `BG(U_s, q)` (explicit argument) and `Hyp.PadicOrdDecomp p`. The middle and right terms are
  the ordinary parts of the **degree-zero** chain modules; their identification with the full ordinary parts
  `e ℤ_p[X(U₀(q)U_s)]` and `e ℤ_p[X_s] × e ℤ_p[X_s]` (`lem:s04-ekills`(a)) is in `Ordinary/RibetFiniteFull.lean`
  (`map_ordPart_UpDeg0E`, `map_ordPart_UpDeg0Prod`, `ordDeg0EEquiv`, `ordDeg0ProdEquiv`);
* `alpha_comm_pushforward`, `boundary_comm_pushBG`, `pushforward_mem_H1`, `pushforward_mem_deg0`,
  `pushforward_mem_ordPart` : chain-level compatibility with `π_*` (`U' ≤ U`): `∂ ∘ π_* = (π_* × π_*) ∘ ∂` on full
  chains, `π_*` preserves `H₁`, `R[X]⁰` (`XB`-typed) and `ordPart (UpAt …)` on full chains. **Not stated here:** the
  restrictions of `π_*` to the three terms `e H₁`, `e ℤ_p[X(U₀(q)U)]⁰`, `e (ℤ_p[X(U)]⁰)²`, the transition maps between
  them and the commuting squares with `ordH1toDeg0`, `ordAlpha` (planned in S04-L13b, `Ordinary/Limit.lean`);
* `rank_ordRibet` : (c) in the form of cardinal rank–nullity on degree-zero parts,
  `rk e ℤ_p[X(U₀(q)U)]⁰ = rk e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) + rk e H₁` (`Module.rank`); it carries no information beyond
  `ordRibet_exact`. **Not formalized:** the first formula of (c), `rk H₁(Γ, ℤ_p) = (q − 1)|X_s| + 1`, and the
  `finrank` form `rk e H₁ = rk e ℤ_p[X^{(q)}_s] − 2 rk e ℤ_p[X_s]`.

## Status

*formalized*, with the connectivity of `BG(U_s, q)` an explicit argument; the `hdec : Hyp.PadicOrdDecomp p` argument
of the ordinary-part theorems is discharged in `Ordinary/TowerUncond.lean` (by `padicOrdDecomp_holds`). The scope is
as listed above (degree-zero terms; chain-level `π_*` and diamond compatibilities; cardinal rank–nullity).
Never `open Graph` (clash with `_root_.Graph`).
-/

set_option autoImplicit false

namespace Langlandscape.Ordinary

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

/-! ### Stage 03's Ribet sequence over `ℤ_p` -/

section Zp

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `thm:s04-lambdaribet`(a) at level `s`, `if:s03-ribet` (`s04-lambdaribet`): stage 03's `Ribet.ribet_exact` at
`R = ℤ_[p]`: `0 → H₁(BG, ℤ_p) → ℤ_p[X(U₀(q)U)]⁰ → ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰ → 0` is exact (given connectivity). -/
theorem ribet_exact_Zp (p : ℕ) [Fact p.Prime] (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) :
    Function.Injective (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p]) ∧
      Function.Exact (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p])
        (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p]) ∧
      Function.Surjective (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p]) :=
  Langlandscape.Ribet.ribet_exact ℤ_[p] hU hc

end Zp

/-! ### `U_p`-equivariance of `s_{0*}`, `s_{1*}`, `α` -/

section Up

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}
  {U : Subgroup (BHat d.a d.b)ˣ} {K K' : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `thm:s04-lambdaribet`(a), `prop:s02-quot`(c) (`s04-lambdaribet`): `ϖ = ι_p(diag(p, 1))` has trivial
`q`-component for `p ≠ q`. -/
theorem localProjUnits_varpi (hpq : p ≠ q) :
    localProjUnits d.a d.b q (localEmbedGL d p hp (varpiDiag p)) = 1 :=
  localProjUnits_localEmbedGL_of_ne (d := d) (p := p) (hp := hp) _ hpq.symm

/-- `thm:s04-lambdaribet`(a), `prop:s02-quot`(c) (`s04-lambdaribet`): `U_p ∘ s_{0*} = s_{0*} ∘ U_p`
(`s_{0*} : ℤ[X(U₀(q)U)] → ℤ[X(U)]`, `p ≠ q`; stage-02 `heckeTHom_comm_s0Push` at `t = ϖ`). -/
theorem UpAt_comm_s0 (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q)
    (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K')
    [Finite (XB U)] [Finite (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U))] :
    (Tree.s0Push d q hq U R).comp (UpAt (d.U0q q (Tree.coprime_of_not_dvd hq) U) hUp0 R) =
      (UpAt U hUp R).comp (Tree.s0Push d q hq U R) :=
  Tree.heckeTHom_comm_s0Push R hU (localEmbedGL d p hp (varpiDiag p)) (localProjUnits_varpi hpq)
    hUp.relIndex_ne_zero hUp0.relIndex_ne_zero

/-- `thm:s04-lambdaribet`(a), `prop:s02-quot`(c) (`s04-lambdaribet`): `U_p ∘ s_{1*} = s_{1*} ∘ U_p`
(`p ≠ q`; stage-02 `heckeTHom_comm_s1Push` at `t = ϖ`). -/
theorem UpAt_comm_s1 (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q)
    (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K')
    [Finite (XB U)] [Finite (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U))] :
    (Tree.s1Push d q hq U R).comp (UpAt (d.U0q q (Tree.coprime_of_not_dvd hq) U) hUp0 R) =
      (UpAt U hUp R).comp (Tree.s1Push d q hq U R) :=
  Tree.heckeTHom_comm_s1Push R hU (localEmbedGL d p hp (varpiDiag p)) (localProjUnits_varpi hpq)
    hUp.relIndex_ne_zero hUp0.relIndex_ne_zero

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `α ∘ U_p = (U_p × U_p) ∘ α` for `α = ∂ = (−s_{0*}, s_{1*})`
(stage 03 `ribet_hecke_equivariant` at `t = ϖ`). -/
theorem boundary_comm_UpAt (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q)
    (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K')
    [Finite (XB U)] [Finite (XB (d.U0q q (Tree.coprime_of_not_dvd hq) U))] :
    (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R).comp
        (UpAt (d.U0q q (Tree.coprime_of_not_dvd hq) U) hUp0 R) =
      ((UpAt U hUp R).prodMap (UpAt U hUp R)).comp (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R) :=
  Langlandscape.Ribet.ribet_hecke_equivariant R hU (localEmbedGL d p hp (varpiDiag p))
    (localProjUnits_varpi hpq) hUp.relIndex_ne_zero hUp0.relIndex_ne_zero

/-- `thm:s04-lambdaribet`(a), `lem:s04-ekills`(a) (`s04-lambdaribet`): `deg (U_p x) = p · deg x` on `R[X_B(U)]`
(`U_p [x] = ∑_{j < p} [x ϖ_j]`). -/
theorem aug_UpAt (R : Type*) [CommRing R] (hUp : IsUpLevel d p hp U K) [Finite (XB U)] (x : ZX U R) :
    Finsupp.linearCombination R (fun _ : XB U => (1 : R)) (UpAt U hUp R x) =
      (p : R) * Finsupp.linearCombination R (fun _ : XB U => (1 : R)) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | single c r =>
    rw [← DoubleCoset.out_eq' c, UpAt_single, map_sum]
    simp only [Finsupp.linearCombination_single, smul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` preserves the degree-zero part `R[X_B(U)]⁰`. -/
theorem UpAt_mem_deg0 {R : Type*} [CommRing R] (hUp : IsUpLevel d p hp U K) [Finite (XB U)] {x : ZX U R}
    (hx : x ∈ Langlandscape.Graph.deg0 (XB U) R) :
    UpAt U hUp R x ∈ Langlandscape.Graph.deg0 (XB U) R := by
  have h : Finsupp.linearCombination R (fun _ : XB U => (1 : R)) x = 0 := LinearMap.mem_ker.1 hx
  exact LinearMap.mem_ker.2 (by rw [aug_UpAt R hUp x, h, mul_zero])

/-! #### `U_p` on the `BG`-typed chain modules

`Tree.BG`-typed modules (`(Tree.BG …).E →₀ R`, `(Tree.BG …).V0 →₀ R`, …) are not syntactically `ZX …`; following
S03-L9 (`Ribet.boundary_BG_eq`), `U_p` is transported once to the `BG` side (`UpBGE`, `UpBGV0`, `UpBGV1`) and all
later statements are on that side. -/

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` on the edge chains `R[E(BG)] = R[X(U₀(q)U)]`, `BG`-typed. -/
noncomputable def UpBGE (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Module.End R ((Tree.BG d q hq U hU).E →₀ R) :=
  haveI := Tree.finite_XB_U0q hU
  UpAt (d.U0q q (Tree.coprime_of_not_dvd hq) U) hUp0 R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` on the type-0 vertex chains `R[V₀(BG)] = R[X(U)]`. -/
noncomputable def UpBGV0 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R] :
    Module.End R ((Tree.BG d q hq U hU).V0 →₀ R) :=
  haveI := Tree.finite_XB_of_isQLevel hU
  UpAt U hUp R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` on the type-1 vertex chains `R[V₁(BG)] = R[X(U)]`. -/
noncomputable def UpBGV1 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R] :
    Module.End R ((Tree.BG d q hq U hU).V1 →₀ R) :=
  haveI := Tree.finite_XB_of_isQLevel hU
  UpAt U hUp R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `∂ ∘ U_p = (U_p × U_p) ∘ ∂` on the `BG` side (bridge from
`boundary_comm_UpAt`). -/
theorem boundary_comm_UpBG (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R ∘ₗ UpBGE hU hUp0 R =
      ((UpBGV0 hU hUp R).prodMap (UpBGV1 hU hUp R)) ∘ₗ Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R := by
  have := Tree.finite_XB_of_isQLevel hU
  have := Tree.finite_XB_U0q hU
  exact boundary_comm_UpAt R hU hpq hUp hUp0

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` preserves `R[X(U₀(q)U)]⁰` (`BG` side). -/
theorem UpBGE_mem_deg0 (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R]
    {x : (Tree.BG d q hq U hU).E →₀ R} (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E R) :
    UpBGE hU hUp0 R x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E R := by
  have := Tree.finite_XB_U0q hU
  exact UpAt_mem_deg0 hUp0 hx

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` preserves `R[V₀(BG)]⁰`. -/
theorem UpBGV0_mem_deg0 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R]
    {x : (Tree.BG d q hq U hU).V0 →₀ R} (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).V0 R) :
    UpBGV0 hU hUp R x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).V0 R := by
  have := Tree.finite_XB_of_isQLevel hU
  exact UpAt_mem_deg0 hUp hx

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` preserves `R[V₁(BG)]⁰`. -/
theorem UpBGV1_mem_deg0 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R]
    {x : (Tree.BG d q hq U hU).V1 →₀ R} (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).V1 R) :
    UpBGV1 hU hUp R x ∈ Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).V1 R := by
  have := Tree.finite_XB_of_isQLevel hU
  exact UpAt_mem_deg0 hUp hx

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` (on `R[X(U₀(q)U)]`) preserves `H₁(BG, R) = ker α`. -/
theorem UpBGE_mem_H1 (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R]
    {x : (Tree.BG d q hq U hU).E →₀ R} (hx : x ∈ Langlandscape.Graph.H1 (Tree.BG d q hq U hU) R) :
    UpBGE hU hUp0 R x ∈ Langlandscape.Graph.H1 (Tree.BG d q hq U hU) R := by
  have h : Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R (UpBGE hU hUp0 R x) =
      ((UpBGV0 hU hUp R).prodMap (UpBGV1 hU hUp R)) (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R x) :=
    LinearMap.congr_fun (boundary_comm_UpBG hU hpq hUp hUp0 R) x
  have h0 : Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R x = 0 := LinearMap.mem_ker.1 hx
  rw [h0, map_zero] at h
  exact LinearMap.mem_ker.2 h

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` on `H₁(BG(U, q), R) ⊆ R[X(U₀(q)U)]⁰`, the restriction of
`U_p` on `R[X(U₀(q)U)]` (`H1toDeg0` is injective with `U_p`-stable image). -/
noncomputable def UpH1 (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Module.End R (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) R) :=
  (UpBGE hU hUp0 R).restrict fun _ hx => UpBGE_mem_H1 hU hpq hUp hUp0 R hx

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p` on `R[X(U₀(q)U)]⁰` (restriction). -/
noncomputable def UpDeg0E (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Module.End R (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E R) :=
  (UpBGE hU hUp0 R).restrict fun _ hx => UpBGE_mem_deg0 hU hUp0 R hx

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U_p × U_p` on `R[X(U)]⁰ × R[X(U)]⁰` (restriction). -/
noncomputable def UpDeg0Prod (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R] :
    Module.End R (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) R) :=
  ((UpBGV0 hU hUp R).prodMap (UpBGV1 hU hUp R)).restrict fun _ hx =>
    Submodule.mem_prod.2 ⟨UpBGV0_mem_deg0 hU hUp R (Submodule.mem_prod.1 hx).1,
      UpBGV1_mem_deg0 hU hUp R (Submodule.mem_prod.1 hx).2⟩

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `H1toDeg0 : H₁ → R[X(U₀(q)U)]⁰` is `U_p`-equivariant. -/
theorem H1toDeg0_comm_Up (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) R ∘ₗ UpH1 hU hpq hUp hUp0 R =
      UpDeg0E hU hUp0 R ∘ₗ Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) R :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `α = boundaryDeg0 : R[X(U₀(q)U)]⁰ → R[X(U)]⁰ × R[X(U)]⁰` is
`U_p`-equivariant. -/
theorem boundaryDeg0_comm_Up (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R] :
    Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) R ∘ₗ UpDeg0E hU hUp0 R =
      UpDeg0Prod hU hUp R ∘ₗ Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) R :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (boundary_comm_UpBG hU hpq hUp hUp0 R) x.1)

end Up

/-! ### Diamond equivariance of `α` -/

section Diamond

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `thm:s04-lambdaribet`(a), `prop:s02-quot`(c) (`s04-lambdaribet`): `α_q = ι_q(diag(1, q))` commutes with every
`g` of trivial `q`-component (re-proof of the private stage-02 lemma). -/
theorem commute_alphaElt_of_away {g : (BHat d.a d.b)ˣ} (hg : localProjUnits d.a d.b q g = 1) :
    Commute (Tree.alphaElt d q hq) g := by
  unfold Tree.alphaElt
  rw [localEmbedGL_apply]
  exact commute_localEmbed_of_commute _ (by rw [hg]; exact Commute.one_right _)

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s₀ [y g] = [y g]`, i.e. `s₀` commutes with right
multiplication by `g` normalising both levels. -/
theorem s0_rightMulXB {g : (BHat d.a d.b)ˣ}
    (hg0 : ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U, g⁻¹ * u * g ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) (c : XB (d.U0q q (Tree.coprime_of_not_dvd hq) U)) :
    Tree.s0 d q hq U (rightMulXB _ g c) = rightMulXB U g (Tree.s0 d q hq U c) := by
  rw [← DoubleCoset.out_eq' c, rightMulXB_mk _ g hg0, Tree.s0_mk, Tree.s0_mk, rightMulXB_mk U g hg]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s₁ [y g] = [y g α] = [y α g]` for `g` of trivial
`q`-component normalising both levels. -/
theorem s1_rightMulXB (hU : Tree.IsQLevel d q hq U) {g : (BHat d.a d.b)ˣ}
    (hgq : localProjUnits d.a d.b q g = 1)
    (hg0 : ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U, g⁻¹ * u * g ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) (c : XB (d.U0q q (Tree.coprime_of_not_dvd hq) U)) :
    Tree.s1 d q hq U (rightMulXB _ g c) = rightMulXB U g (Tree.s1 d q hq U c) := by
  rw [← DoubleCoset.out_eq' c, rightMulXB_mk _ g hg0, Tree.s1_mk hU, Tree.s1_mk hU, rightMulXB_mk U g hg,
    mul_assoc, mul_assoc, (commute_alphaElt_of_away (hq := hq) hgq).eq]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s_{0*} ∘ R_g = R_g ∘ s_{0*}` on chains. -/
theorem s0Push_comm_rightMulXB (R : Type*) [CommRing R] {g : (BHat d.a d.b)ˣ}
    (hg0 : ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U, g⁻¹ * u * g ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    (Tree.s0Push d q hq U R).comp (Finsupp.lmapDomain R R (rightMulXB (d.U0q q (Tree.coprime_of_not_dvd hq) U) g)) =
      (Finsupp.lmapDomain R R (rightMulXB U g)).comp (Tree.s0Push d q hq U R) := by
  unfold Tree.s0Push
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  exact congrArg (Finsupp.lmapDomain R R) (funext fun c => s0_rightMulXB (hq := hq) hg0 hg c)

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s_{1*} ∘ R_g = R_g ∘ s_{1*}` on chains. -/
theorem s1Push_comm_rightMulXB (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) {g : (BHat d.a d.b)ˣ}
    (hgq : localProjUnits d.a d.b q g = 1)
    (hg0 : ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U, g⁻¹ * u * g ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    (Tree.s1Push d q hq U R).comp (Finsupp.lmapDomain R R (rightMulXB (d.U0q q (Tree.coprime_of_not_dvd hq) U) g)) =
      (Finsupp.lmapDomain R R (rightMulXB U g)).comp (Tree.s1Push d q hq U R) := by
  unfold Tree.s1Push
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  exact congrArg (Finsupp.lmapDomain R R) (funext fun c => s1_rightMulXB (hq := hq) hU hgq hg0 hg c)

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): if `f₀`, `f` intertwine `s_{0*}` and `s_{1*}` (from level `U'`
to level `U`), then `∂_U ∘ f₀ = (f × f) ∘ ∂_{U'}` (pointwise, via `Ribet.boundary_BG_apply`). -/
theorem boundary_comm_of_comm (R : Type*) [CommRing R] {U' : Subgroup (BHat d.a d.b)ˣ}
    (hU : Tree.IsQLevel d q hq U) (hU' : Tree.IsQLevel d q hq U')
    (f0 : ZX (d.U0q q (Tree.coprime_of_not_dvd hq) U') R →ₗ[R] ZX (d.U0q q (Tree.coprime_of_not_dvd hq) U) R)
    (f : ZX U' R →ₗ[R] ZX U R)
    (h0 : (Tree.s0Push d q hq U R).comp f0 = f.comp (Tree.s0Push d q hq U' R))
    (h1 : (Tree.s1Push d q hq U R).comp f0 = f.comp (Tree.s1Push d q hq U' R)) :
    (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R).comp f0 =
      (f.prodMap f).comp (Langlandscape.Graph.boundary (Tree.BG d q hq U' hU') R) := by
  refine LinearMap.ext fun y => ?_
  have e0 : Tree.s0Push d q hq U R (f0 y) = f (Tree.s0Push d q hq U' R y) := LinearMap.congr_fun h0 y
  have e1 : Tree.s1Push d q hq U R (f0 y) = f (Tree.s1Push d q hq U' R y) := LinearMap.congr_fun h1 y
  have hn : -(Tree.s0Push d q hq U R (f0 y)) = f (-(Tree.s0Push d q hq U' R y)) :=
    (congrArg Neg.neg e0).trans (map_neg f (Tree.s0Push d q hq U' R y)).symm
  have key : ((-(Tree.s0Push d q hq U R (f0 y)), Tree.s1Push d q hq U R (f0 y)) : ZX U R × ZX U R) =
      (f.prodMap f) (-(Tree.s0Push d q hq U' R y), Tree.s1Push d q hq U' R y) := by
    exact Prod.ext hn e1
  have b1 := Langlandscape.Ribet.boundary_BG_apply R hU (f0 y)
  have b2 := Langlandscape.Ribet.boundary_BG_apply R hU' y
  exact b1.trans (key.trans (congrArg (f.prodMap f) b2).symm)

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `α = (−s_{0*}, s_{1*})` commutes with right multiplication
`R_g` by any `g` of trivial `q`-component normalising `U` and `U₀(q)U`. -/
theorem alpha_comm_rightMulXB (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U) {g : (BHat d.a d.b)ˣ}
    (hgq : localProjUnits d.a d.b q g = 1)
    (hg0 : ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U, g⁻¹ * u * g ∈ d.U0q q (Tree.coprime_of_not_dvd hq) U)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R).comp
        (Finsupp.lmapDomain R R (rightMulXB (d.U0q q (Tree.coprime_of_not_dvd hq) U) g)) =
      ((Finsupp.lmapDomain R R (rightMulXB U g)).prodMap (Finsupp.lmapDomain R R (rightMulXB U g))).comp
        (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R) :=
  boundary_comm_of_comm R hU hU _ _ (s0Push_comm_rightMulXB (hq := hq) R hg0 hg)
    (s1Push_comm_rightMulXB (hq := hq) R hU hgq hg0 hg)

variable {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

omit [Fact p.Prime] in
/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `q ∤ M p^s`, `s ≥ 1` force `p ≠ q`. -/
theorem ne_of_not_dvd_tower {M s : ℕ} (hs : 1 ≤ s) (hqN : ¬ q ∣ M * p ^ s) : p ≠ q := by
  rintro rfl
  exact hqN (Dvd.dvd.mul_left (dvd_pow_self p (by omega)) M)

omit [Fact p.Prime] in
/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `p ≠ q` (`q` prime) gives `p ∉ q.primeFactors`. -/
theorem not_mem_primeFactors_of_ne (hpq : p ≠ q) : p ∉ q.primeFactors := by
  rw [Nat.Prime.primeFactors (Fact.out : q.Prime), Finset.mem_singleton]
  exact hpq

/-- `thm:s04-lambdaribet`(a), `lem:s01-stab`(b) (`s04-lambdaribet`): `δ_t⁻¹` normalises `U₀(q) U_s`. -/
theorem deltaElt_inv_normalizes_U0q {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t : ℤ_[p]ˣ) :
    ∀ u ∈ d.U0q q (Tree.coprime_of_not_dvd hq) (d.Utower M p s hN),
      (deltaElt d p hp t)⁻¹ * u * deltaElt d p hp t ∈ d.U0q q (Tree.coprime_of_not_dvd hq) (d.Utower M p s hN) :=
  fun _ hu => Subgroup.mem_inf.2
    ⟨deltaElt_inv_normalizes (hp := hp) hM hpM hs t (Subgroup.mem_inf.1 hu).1,
      deltaElt_inv_normalizes_U0 (hp := hp) t (Subgroup.mem_inf.1 hu).2⟩

/-- `thm:s04-lambdaribet`(a), `alpha_comm_diamond` (`s04-lambdaribet`): on full chain modules,
`∂ ∘ R_{δ_t} = (⟨t⟩ × ⟨t⟩) ∘ ∂` for `t ∈ ℤ_p^×`, where `R_{δ_t}` is the bare right multiplication `rightMulXB` by
`δ_t` on `X(U₀(q)U_s)` and `⟨t⟩ = diamondAct` on `X(U_s)` (`q ∤ M p^s`, `s ≥ 1`). This is a chain-level statement:
no diamond operator on `X(U₀(q)U_s)`, no commutation of it with `U_p`, and no `Δ_s`-linearity of `ordAlpha` are
stated. -/
theorem alpha_comm_diamond (R : Type*) [CommRing R] {M s : ℕ} {hN : (M * p ^ s).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (hqN : ¬ q ∣ M * p ^ s) (t : ℤ_[p]ˣ) :
    (Langlandscape.Graph.boundary (Tree.BG d q hq (d.Utower M p s hN) (Tree.isQLevel_Utower hqN)) R).comp
        (Finsupp.lmapDomain R R
          (rightMulXB (d.U0q q (Tree.coprime_of_not_dvd hq) (d.Utower M p s hN)) (deltaElt d p hp t))) =
      ((Finsupp.lmapDomain R R ⇑(diamondAct (hp := hp) (hN := hN) hM hpM hs t)).prodMap
          (Finsupp.lmapDomain R R ⇑(diamondAct (hp := hp) (hN := hN) hM hpM hs t))).comp
        (Langlandscape.Graph.boundary (Tree.BG d q hq (d.Utower M p s hN) (Tree.isQLevel_Utower hqN)) R) :=
  alpha_comm_rightMulXB (hq := hq) R (Tree.isQLevel_Utower hqN)
    (localProjUnits_localEmbedGL_of_ne (d := d) (p := p) (hp := hp) _ (ne_of_not_dvd_tower hs hqN).symm)
    (deltaElt_inv_normalizes_U0q (hq := hq) hM hpM hs t) (fun _ hu => deltaElt_inv_normalizes hM hpM hs t hu)

end Diamond

/-! ### Ordinary parts of submodules of finite `ℤ_p`-modules (generic layer)

Stated for abstract submodules `S₁, S₂, S₃` of finite `ℤ_[p]`-modules, so that no unfolding of the concrete
`Tree.BG`-typed modules happens while `ordPart_exact` and `Hyp.PadicOrdDecomp` are applied. -/

section OrdGeneric

variable {p : ℕ} [Fact p.Prime]

/-- `def:s04-e`, `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `Hyp.PadicOrdDecomp` applies to every endomorphism of
a submodule of a finite `ℤ_[p]`-module (`ℤ_[p]` is noetherian). -/
theorem hasOrdDecomp_submodule (hdec : Langlandscape.Hyp.PadicOrdDecomp p) {N : Type} [AddCommGroup N]
    [Module ℤ_[p] N] [Module.Finite ℤ_[p] N] (S : Submodule ℤ_[p] N) (T : Module.End ℤ_[p] S) :
    HasOrdDecomp (p : ℤ_[p]) T := by
  have : IsNoetherian ℤ_[p] N := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] N
  exact hdec S T

/-- `def:s04-e`, `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), generic form: a short exact sequence of
`T`-equivariant maps between submodules of finite `ℤ_[p]`-modules stays exact on ordinary parts (modulo
`Hyp.PadicOrdDecomp`; `ordPart_exact`). -/
theorem ordPart_exact_submodule (hdec : Langlandscape.Hyp.PadicOrdDecomp p) {N₁ N₂ N₃ : Type}
    [AddCommGroup N₁] [Module ℤ_[p] N₁] [Module.Finite ℤ_[p] N₁]
    [AddCommGroup N₂] [Module ℤ_[p] N₂] [Module.Finite ℤ_[p] N₂]
    [AddCommGroup N₃] [Module ℤ_[p] N₃] [Module.Finite ℤ_[p] N₃]
    (S₁ : Submodule ℤ_[p] N₁) (S₂ : Submodule ℤ_[p] N₂) (S₃ : Submodule ℤ_[p] N₃)
    (T₁ : Module.End ℤ_[p] S₁) (T₂ : Module.End ℤ_[p] S₂) (T₃ : Module.End ℤ_[p] S₃)
    (f : S₁ →ₗ[ℤ_[p]] S₂) (g : S₂ →ₗ[ℤ_[p]] S₃) (hf : f ∘ₗ T₁ = T₂ ∘ₗ f) (hg : g ∘ₗ T₂ = T₃ ∘ₗ g)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    Function.Injective (ordRestrict f hf) ∧ Function.Exact (ordRestrict f hf) (ordRestrict g hg) ∧
      Function.Surjective (ordRestrict g hg) :=
  ordPart_exact f g hf hg (hasOrdDecomp_submodule hdec S₁ T₁) (hasOrdDecomp_submodule hdec S₂ T₂)
    (hasOrdDecomp_submodule hdec S₃ T₃) hinj hex hsurj

/-- `thm:s04-lambdaribet`(c) (`s04-lambdaribet`), abstract form: for a short exact sequence `0 → A → B → C → 0` over
a domain, `rk B = rk C + rk A` (rank–nullity). -/
theorem rank_eq_add_of_exact {R : Type*} [CommRing R] [IsDomain R] {A B C : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f) (hex : Function.Exact f g)
    (hg : Function.Surjective g) :
    Module.rank R B = Module.rank R C + Module.rank R A := by
  rw [LinearMap.rank_eq_of_surjective hg, LinearMap.exact_iff.1 hex, rank_range_of_injective f hf]

/-- `thm:s04-lambdaribet`(c) (`s04-lambdaribet`), generic form: in the situation of `ordPart_exact_submodule`,
`rk e S₂ = rk e S₃ + rk e S₁`. -/
theorem rank_ordPart_submodule (hdec : Langlandscape.Hyp.PadicOrdDecomp p) {N₁ N₂ N₃ : Type}
    [AddCommGroup N₁] [Module ℤ_[p] N₁] [Module.Finite ℤ_[p] N₁]
    [AddCommGroup N₂] [Module ℤ_[p] N₂] [Module.Finite ℤ_[p] N₂]
    [AddCommGroup N₃] [Module ℤ_[p] N₃] [Module.Finite ℤ_[p] N₃]
    (S₁ : Submodule ℤ_[p] N₁) (S₂ : Submodule ℤ_[p] N₂) (S₃ : Submodule ℤ_[p] N₃)
    (T₁ : Module.End ℤ_[p] S₁) (T₂ : Module.End ℤ_[p] S₂) (T₃ : Module.End ℤ_[p] S₃)
    (f : S₁ →ₗ[ℤ_[p]] S₂) (g : S₂ →ₗ[ℤ_[p]] S₃) (hf : f ∘ₗ T₁ = T₂ ∘ₗ f) (hg : g ∘ₗ T₂ = T₃ ∘ₗ g)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    Module.rank ℤ_[p] (ordPart T₂) = Module.rank ℤ_[p] (ordPart T₃) + Module.rank ℤ_[p] (ordPart T₁) := by
  obtain ⟨h1, h2, h3⟩ := ordPart_exact_submodule hdec S₁ S₂ S₃ T₁ T₂ T₃ f g hf hg hinj hex hsurj
  exact rank_eq_add_of_exact (A := ↥(ordPart T₁)) (B := ↥(ordPart T₂)) (C := ↥(ordPart T₃))
    (ordRestrict f hf) (ordRestrict g hg) h1 h2 h3

end OrdGeneric

/-! ### The ordinary Ribet sequence -/

section Ord

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}
  {U : Subgroup (BHat d.a d.b)ˣ} {K K' : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `e H₁ → e ℤ_p[X(U₀(q)U)]⁰`, the restriction of `H1toDeg0` to the
ordinary parts (`ordRestrict`). -/
noncomputable def ordH1toDeg0 (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    ordPart (R := ℤ_[p])
        (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p]) →ₗ[ℤ_[p]]
      ordPart (R := ℤ_[p])
        (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])) (UpDeg0E hU hUp0 ℤ_[p]) :=
  ordRestrict (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p]))
    (N := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
    (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p]) (H1toDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p])

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `α : e ℤ_p[X(U₀(q)U)]⁰ → e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰)`, the
restriction of `boundaryDeg0` to the ordinary parts (`ordRestrict`). -/
noncomputable def ordAlpha (hU : Tree.IsQLevel d q hq U) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    ordPart (R := ℤ_[p])
        (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])) (UpDeg0E hU hUp0 ℤ_[p]) →ₗ[ℤ_[p]]
      ordPart (R := ℤ_[p])
        (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])) (UpDeg0Prod hU hUp ℤ_[p]) :=
  ordRestrict (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
    (N := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]))
    (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p]) (boundaryDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p])

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), formalized modulo `Hyp.PadicOrdDecomp`:
`e H₁ → e ℤ_p[X(U₀(q)U)]⁰` is injective. -/
theorem ordRibet_injective (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Injective (ordH1toDeg0 hU hpq hUp hUp0) := by
  have := Langlandscape.Ribet.finite_BG_E hU
  have := Langlandscape.Ribet.finite_BG_V0 hU
  have := Langlandscape.Ribet.finite_BG_V1 hU
  obtain ⟨h1, h2, h3⟩ := Langlandscape.Ribet.ribet_exact ℤ_[p] hU hc
  exact (ordPart_exact_submodule hdec (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])
    (UpH1 hU hpq hUp hUp0 ℤ_[p]) (UpDeg0E hU hUp0 ℤ_[p]) (UpDeg0Prod hU hUp ℤ_[p])
    (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (H1toDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) (boundaryDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) h1 h2 h3).1

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), formalized modulo `Hyp.PadicOrdDecomp`:
`e H₁ → e ℤ_p[X(U₀(q)U)]⁰ → e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰)` is exact in the middle. -/
theorem ordRibet_exact_mid (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Exact (ordH1toDeg0 hU hpq hUp hUp0) (ordAlpha hU hpq hUp hUp0) := by
  have := Langlandscape.Ribet.finite_BG_E hU
  have := Langlandscape.Ribet.finite_BG_V0 hU
  have := Langlandscape.Ribet.finite_BG_V1 hU
  obtain ⟨h1, h2, h3⟩ := Langlandscape.Ribet.ribet_exact ℤ_[p] hU hc
  exact (ordPart_exact_submodule hdec (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])
    (UpH1 hU hpq hUp hUp0 ℤ_[p]) (UpDeg0E hU hUp0 ℤ_[p]) (UpDeg0Prod hU hUp ℤ_[p])
    (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (H1toDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) (boundaryDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) h1 h2 h3).2.1

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), formalized modulo `Hyp.PadicOrdDecomp`:
`α : e ℤ_p[X(U₀(q)U)]⁰ → e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰)` is surjective. -/
theorem ordRibet_surjective (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Surjective (ordAlpha hU hpq hUp hUp0) := by
  have := Langlandscape.Ribet.finite_BG_E hU
  have := Langlandscape.Ribet.finite_BG_V0 hU
  have := Langlandscape.Ribet.finite_BG_V1 hU
  obtain ⟨h1, h2, h3⟩ := Langlandscape.Ribet.ribet_exact ℤ_[p] hU hc
  exact (ordPart_exact_submodule hdec (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])
    (UpH1 hU hpq hUp hUp0 ℤ_[p]) (UpDeg0E hU hUp0 ℤ_[p]) (UpDeg0Prod hU hUp ℤ_[p])
    (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (H1toDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) (boundaryDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) h1 h2 h3).2.2

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), for `E = ℚ_p`, formalized modulo
`Hyp.PadicOrdDecomp`: given connectivity of `BG(U, q)`, `p ≠ q` and levels `U`, `U₀(q)U` carrying `U_p`
(`IsUpLevel`), the ordinary parts form a short exact sequence
`0 → e H₁(BG, ℤ_p) → e ℤ_p[X(U₀(q)U)]⁰ → e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) → 0` (`e` for `U_p`; via `ordPart_exact`). -/
theorem ordRibet_exact (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Injective (ordH1toDeg0 hU hpq hUp hUp0) ∧
      Function.Exact (ordH1toDeg0 hU hpq hUp hUp0) (ordAlpha hU hpq hUp hUp0) ∧
      Function.Surjective (ordAlpha hU hpq hUp hUp0) :=
  ⟨ordRibet_injective hdec hU hc hpq hUp hUp0, ordRibet_exact_mid hdec hU hc hpq hUp hUp0,
    ordRibet_surjective hdec hU hc hpq hUp hUp0⟩

/-- `thm:s04-lambdaribet`(a) at every level `s ≥ 1` (`s04-lambdaribet`), for `E = ℚ_p`, formalized modulo
`Hyp.PadicOrdDecomp`: with `U_s = U_1(M p^s)` (`p ∤ M`, `q ∤ M p^s`) and the connectivity of `BG(U_s, q)` for all
`s ≥ 1` as an explicit argument, `0 → e H₁ → e ℤ_p[X(U₀(q)U_s)]⁰ → e (ℤ_p[X_s]⁰)² → 0` is exact. -/
theorem ordRibet_exact_Utower {M : ℕ} (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hN : ∀ s, (M * p ^ s).Coprime d.D) (hqN : ∀ s, ¬ q ∣ M * p ^ s)
    (hconn : ∀ s, 1 ≤ s → Tree.BGConnected d q hq (d.Utower M p s (hN s)) (Tree.isQLevel_Utower (hqN s)))
    (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (ordH1toDeg0 (hq := hq) (Tree.isQLevel_Utower (hqN s)) (ne_of_not_dvd_tower hs (hqN s))
          (isUpLevel_Utower (hp := hp) (hN := hN s) hM hpM hs)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN s) hM hpM hs (Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs (hqN s))))) ∧
      Function.Exact (ordH1toDeg0 (hq := hq) (Tree.isQLevel_Utower (hqN s)) (ne_of_not_dvd_tower hs (hqN s))
          (isUpLevel_Utower (hp := hp) (hN := hN s) hM hpM hs)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN s) hM hpM hs (Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs (hqN s)))))
        (ordAlpha (hq := hq) (Tree.isQLevel_Utower (hqN s)) (ne_of_not_dvd_tower hs (hqN s))
          (isUpLevel_Utower (hp := hp) (hN := hN s) hM hpM hs)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN s) hM hpM hs (Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs (hqN s))))) ∧
      Function.Surjective (ordAlpha (hq := hq) (Tree.isQLevel_Utower (hqN s)) (ne_of_not_dvd_tower hs (hqN s))
          (isUpLevel_Utower (hp := hp) (hN := hN s) hM hpM hs)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN s) hM hpM hs (Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs (hqN s))))) :=
  ordRibet_exact hdec (Tree.isQLevel_Utower (hqN s)) (hconn s hs) (ne_of_not_dvd_tower hs (hqN s))
    (isUpLevel_Utower (hp := hp) (hN := hN s) hM hpM hs)
    (isUpLevel_U0q_Utower (hp := hp) (hN := hN s) hM hpM hs (Tree.coprime_of_not_dvd hq)
      (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs (hqN s))))

/-! #### Rank formula (c) -/

/-- `thm:s04-lambdaribet`(c) at level `s` (`s04-lambdaribet`), formalized modulo `Hyp.PadicOrdDecomp`, in the
form of cardinal rank–nullity on degree-zero parts: `rk e ℤ_p[X(U₀(q)U)]⁰ = rk e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) + rk e H₁`
(`Module.rank` over `ℤ_p`; no subtraction, the `C`-term is not split as `2 · rk e ℤ_p[X(U)]`). The first formula of
(c), `rk H₁ = (q − 1)|X| + 1`, is not formalized. Full-ordinary-part version: `rank_ordRibet_full`
(`Ordinary/RibetFiniteFull.lean`). -/
theorem rank_ordRibet (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])) (UpDeg0E hU hUp0 ℤ_[p])) =
      Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])) (UpDeg0Prod hU hUp ℤ_[p])) +
        Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p])) := by
  have := Langlandscape.Ribet.finite_BG_E hU
  have := Langlandscape.Ribet.finite_BG_V0 hU
  have := Langlandscape.Ribet.finite_BG_V1 hU
  obtain ⟨h1, h2, h3⟩ := Langlandscape.Ribet.ribet_exact ℤ_[p] hU hc
  exact rank_ordPart_submodule hdec (Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])
    (UpH1 hU hpq hUp hUp0 ℤ_[p]) (UpDeg0E hU hUp0 ℤ_[p]) (UpDeg0Prod hU hUp ℤ_[p])
    (Langlandscape.Graph.H1toDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (Langlandscape.Graph.boundaryDeg0 (Tree.BG d q hq U hU) ℤ_[p])
    (H1toDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) (boundaryDeg0_comm_Up hU hpq hUp hUp0 ℤ_[p]) h1 h2 h3

end Ord

/-! ### Compatibility with `π_*` -/

section Push

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U' U : Subgroup (BHat d.a d.b)ˣ}

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `U' ≤ U` gives `U₀(q)U' ≤ U₀(q)U`. -/
theorem U0q_mono (hle : U' ≤ U) :
    d.U0q q (Tree.coprime_of_not_dvd hq) U' ≤ d.U0q q (Tree.coprime_of_not_dvd hq) U :=
  fun _ hx => Subgroup.mem_inf.2 ⟨hle (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s₀ ∘ π = π ∘ s₀` (`[y] ↦ [y]`). -/
theorem s0_levelMap (hle : U' ≤ U) (c : XB (d.U0q q (Tree.coprime_of_not_dvd hq) U')) :
    Tree.s0 d q hq U (levelMap _ (d.U0q q (Tree.coprime_of_not_dvd hq) U) c) =
      levelMap U' U (Tree.s0 d q hq U' c) := by
  rw [← DoubleCoset.out_eq' c, levelMap_mk (U0q_mono (hq := hq) hle), Tree.s0_mk, Tree.s0_mk, levelMap_mk hle]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `s₁ ∘ π = π ∘ s₁` (`[y] ↦ [y α]`) for `q`-levels `U' ≤ U`. -/
theorem s1_levelMap (hU : Tree.IsQLevel d q hq U) (hU' : Tree.IsQLevel d q hq U') (hle : U' ≤ U)
    (c : XB (d.U0q q (Tree.coprime_of_not_dvd hq) U')) :
    Tree.s1 d q hq U (levelMap _ (d.U0q q (Tree.coprime_of_not_dvd hq) U) c) =
      levelMap U' U (Tree.s1 d q hq U' c) := by
  rw [← DoubleCoset.out_eq' c, levelMap_mk (U0q_mono (hq := hq) hle), Tree.s1_mk hU, Tree.s1_mk hU', levelMap_mk hle]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `α_U ∘ π_* = (π_* × π_*) ∘ α_{U'}` for `q`-levels `U' ≤ U`
(the transition maps of the Ribet systems). -/
theorem alpha_comm_pushforward (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (hU' : Tree.IsQLevel d q hq U') (hle : U' ≤ U) :
    (Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R).comp
        (pushforward (d.U0q q (Tree.coprime_of_not_dvd hq) U') (d.U0q q (Tree.coprime_of_not_dvd hq) U) R) =
      ((pushforward U' U R).prodMap (pushforward U' U R)).comp
        (Langlandscape.Graph.boundary (Tree.BG d q hq U' hU') R) := by
  have h0 : (Tree.s0Push d q hq U R).comp
      (pushforward (d.U0q q (Tree.coprime_of_not_dvd hq) U') (d.U0q q (Tree.coprime_of_not_dvd hq) U) R) =
      (pushforward U' U R).comp (Tree.s0Push d q hq U' R) := by
    unfold Tree.s0Push pushforward
    rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
    exact congrArg (Finsupp.lmapDomain R R) (funext fun c => s0_levelMap (hq := hq) hle c)
  have h1 : (Tree.s1Push d q hq U R).comp
      (pushforward (d.U0q q (Tree.coprime_of_not_dvd hq) U') (d.U0q q (Tree.coprime_of_not_dvd hq) U) R) =
      (pushforward U' U R).comp (Tree.s1Push d q hq U' R) := by
    unfold Tree.s1Push pushforward
    rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
    exact congrArg (Finsupp.lmapDomain R R) (funext fun c => s1_levelMap (hq := hq) hU hU' hle c)
  exact boundary_comm_of_comm R hU hU' _ _ h0 h1

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` preserves degrees, `deg (π_* x) = deg x`. -/
theorem aug_pushforward (R : Type*) [CommRing R] (x : ZX U' R) :
    Finsupp.linearCombination R (fun _ : XB U => (1 : R)) (pushforward U' U R x) =
      Finsupp.linearCombination R (fun _ : XB U' => (1 : R)) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single c r => rw [pushforward_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` maps `R[X(U')]⁰` into `R[X(U)]⁰`. -/
theorem pushforward_mem_deg0 {R : Type*} [CommRing R] {x : ZX U' R}
    (hx : x ∈ Langlandscape.Graph.deg0 (XB U') R) :
    pushforward U' U R x ∈ Langlandscape.Graph.deg0 (XB U) R := by
  have h : Finsupp.linearCombination R (fun _ : XB U' => (1 : R)) x = 0 := LinearMap.mem_ker.1 hx
  exact LinearMap.mem_ker.2 (by rw [aug_pushforward R x, h])

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` on edge chains, `BG`-typed. -/
noncomputable def pushBGE (hU : Tree.IsQLevel d q hq U) (hU' : Tree.IsQLevel d q hq U') (R : Type*) [CommRing R] :
    ((Tree.BG d q hq U' hU').E →₀ R) →ₗ[R] ((Tree.BG d q hq U hU).E →₀ R) :=
  pushforward (d.U0q q (Tree.coprime_of_not_dvd hq) U') (d.U0q q (Tree.coprime_of_not_dvd hq) U) R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` on type-0 vertex chains, `BG`-typed. -/
noncomputable def pushBGV0 (hU : Tree.IsQLevel d q hq U) (hU' : Tree.IsQLevel d q hq U') (R : Type*) [CommRing R] :
    ((Tree.BG d q hq U' hU').V0 →₀ R) →ₗ[R] ((Tree.BG d q hq U hU).V0 →₀ R) :=
  pushforward U' U R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` on type-1 vertex chains, `BG`-typed. -/
noncomputable def pushBGV1 (hU : Tree.IsQLevel d q hq U) (hU' : Tree.IsQLevel d q hq U') (R : Type*) [CommRing R] :
    ((Tree.BG d q hq U' hU').V1 →₀ R) →ₗ[R] ((Tree.BG d q hq U hU).V1 →₀ R) :=
  pushforward U' U R

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `∂ ∘ π_* = (π_* × π_*) ∘ ∂` on the `BG` side (bridge from
`alpha_comm_pushforward`). -/
theorem boundary_comm_pushBG (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (hU' : Tree.IsQLevel d q hq U') (hle : U' ≤ U) :
    Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R ∘ₗ pushBGE hU hU' R =
      ((pushBGV0 hU hU' R).prodMap (pushBGV1 hU hU' R)) ∘ₗ Langlandscape.Graph.boundary (Tree.BG d q hq U' hU') R :=
  alpha_comm_pushforward R hU hU' hle

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` (corestriction) maps `H₁(BG(U', q))` into `H₁(BG(U, q))`. -/
theorem pushforward_mem_H1 (R : Type*) [CommRing R] (hU : Tree.IsQLevel d q hq U)
    (hU' : Tree.IsQLevel d q hq U') (hle : U' ≤ U) {x : (Tree.BG d q hq U' hU').E →₀ R}
    (hx : x ∈ Langlandscape.Graph.H1 (Tree.BG d q hq U' hU') R) :
    pushBGE hU hU' R x ∈ Langlandscape.Graph.H1 (Tree.BG d q hq U hU) R := by
  have h : Langlandscape.Graph.boundary (Tree.BG d q hq U hU) R (pushBGE hU hU' R x) =
      ((pushBGV0 hU hU' R).prodMap (pushBGV1 hU hU' R)) (Langlandscape.Graph.boundary (Tree.BG d q hq U' hU') R x) :=
    LinearMap.congr_fun (boundary_comm_pushBG R hU hU' hle) x
  have h0 : Langlandscape.Graph.boundary (Tree.BG d q hq U' hU') R x = 0 := LinearMap.mem_ker.1 hx
  rw [h0, map_zero] at h
  exact LinearMap.mem_ker.2 h

variable {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D} {K K' : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `π_*` maps the ordinary part `e R[X(U')]` of the full chain
module into `e R[X(U)]` (it commutes with `U_p`, S04-L9 `UpAt_comm_pushforward`). This is a statement about
`ordPart (UpAt …) ⊆ ZX U' R`, not about the three terms of `ordRibet_exact` (which are `ordPart` of `UpH1`,
`UpDeg0E`, `UpDeg0Prod`); the restricted transition maps are planned in S04-L13b. -/
theorem pushforward_mem_ordPart {R : Type*} [CommRing R] (hUp' : IsUpLevel d p hp U' K')
    (hUp : IsUpLevel d p hp U K) (hle : U' ≤ U) [Finite (XB U')] [Finite (XB U)] {x : ZX U' R}
    (hx : x ∈ ordPart (UpAt U' hUp' R)) : pushforward U' U R x ∈ ordPart (UpAt U hUp R) :=
  ordPart_map _ (UpAt_comm_pushforward hUp' hUp hle) hx

end Push

end Langlandscape.Ordinary
