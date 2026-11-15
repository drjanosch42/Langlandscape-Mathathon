/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.EKills
import Langlandscape.Ordinary.RibetFinite

/-!
# Degree-zero versus full ordinary parts in the ordinary Ribet sequence — S04-L17b (audit item R6)

`mathematics/chapters/s04/lambdaribet.tex`, `lem:s04-ribetfinite`, proof step "`e ℤ_p[Y]⁰ = e ℤ_p[Y]`", which is
`lem:s04-ekills`(a) (`mathematics/chapters/s04/ordinary.tex`) instantiated at the Brandt levels of S04-L12.

`Ordinary/RibetFinite.lean` (S04-L12) states the ordinary Ribet sequence on the degree-zero chain modules:
the terms are `ordPart (UpDeg0E …)` on `ℤ_p[X(U₀(q)U)]⁰` and `ordPart (UpDeg0Prod …)` on `ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰`.
This file identifies them with the full ordinary parts `e ℤ_p[X(U₀(q)U)]` and `e ℤ_p[X(U)] × e ℤ_p[X(U)]`.

## Main results

* `deg_eq_linearCombination` : the two spellings of the augmentation agree (`Ordinary.deg` of S04-L4 and the
  `Finsupp.linearCombination R (fun _ => 1)` of `Graph.deg0`);
* `ordPart_prodMap` : `e (T × S) = e T × e S` (any ring, no hypothesis);
* `map_subtype_ordPart_deg0_eq`, `map_subtype_ordPart_prod_eq` : generic forms of `lem:s04-ekills`(a) for a
  `deg0`-stable endomorphism and for a product;
* `map_ordPart_UpDeg0E` : `ι (e ℤ_p[X(U₀(q)U)]⁰) = e ℤ_p[X(U₀(q)U)]` inside `ℤ_p[X(U₀(q)U)]`;
* `map_ordPart_UpDeg0Prod` : `ι (e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰)) = e ℤ_p[X(U)] × e ℤ_p[X(U)]`;
* `ordDeg0EEquiv`, `ordDeg0ProdEquiv` : the corresponding linear equivalences;
* `rank_ordRibet_full` : the cardinal rank–nullity identity of `rank_ordRibet` with the middle and right terms
  replaced by the full ordinary parts.

All ℤ_[p] statements take `hdec : Hyp.PadicOrdDecomp p` (D-e); `TowerUncond.lean` discharges it.

## Status

*formalized* modulo `Hyp.PadicOrdDecomp` (discharged in `Ordinary/TowerUncond.lean`). The identification is of
submodules of the chain modules; the `π_*`- and `Δ_s`-compatibility of these identifications is not stated here.
Never `open Graph` (clash with `_root_.Graph`).
-/

set_option autoImplicit false

namespace Langlandscape.Ordinary

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

/-! ### Generic layer -/

section Generic

variable {R : Type*} [CommRing R]

variable (R) in
/-- `lem:s04-ekills`(a) (`s04-ekills`), bridge: `Ordinary.deg X R` (S04-L4) is the augmentation
`Finsupp.linearCombination R (fun _ => 1)` used by `Graph.deg0`. -/
theorem deg_eq_linearCombination (X : Type*) :
    deg X R = Finsupp.linearCombination R (fun _ : X => (1 : R)) := by
  refine Finsupp.lhom_ext fun x r => ?_
  simp only [deg_single, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

/-- `def:s04-e` (`s04-e`), auxiliary for `lem:s04-ekills`(a): `(T × S)ⁿ = Tⁿ × Sⁿ`. -/
theorem prodMap_pow_eq {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : Module.End R M) (S : Module.End R N) (n : ℕ) :
    (T.prodMap S) ^ n = (T ^ n).prodMap (S ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, LinearMap.prodMap_one]
  | succ n ih => rw [pow_succ (T.prodMap S), ih, pow_succ T, pow_succ S, LinearMap.prodMap_mul]

/-- `def:s04-e` (`s04-e`), used for `lem:s04-ribetfinite`: the ordinary part of a product endomorphism is the
product of the ordinary parts, `e (T × S) = e T × e S` (no hypothesis). -/
theorem ordPart_prodMap {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : Module.End R M) (S : Module.End R N) :
    ordPart (T.prodMap S) = (ordPart T).prod (ordPart S) := by
  ext x
  rw [Submodule.mem_prod, mem_ordPart, mem_ordPart, mem_ordPart]
  constructor
  · intro h
    refine ⟨fun n => ?_, fun n => ?_⟩
    · obtain ⟨y, hy⟩ := h n
      refine ⟨y.1, ?_⟩
      have h1 := congrArg Prod.fst hy
      rw [prodMap_pow_eq, LinearMap.prodMap_apply] at h1
      exact h1
    · obtain ⟨y, hy⟩ := h n
      refine ⟨y.2, ?_⟩
      have h2 := congrArg Prod.snd hy
      rw [prodMap_pow_eq, LinearMap.prodMap_apply] at h2
      exact h2
  · rintro ⟨h1, h2⟩ n
    obtain ⟨y1, hy1⟩ := h1 n
    obtain ⟨y2, hy2⟩ := h2 n
    refine ⟨(y1, y2), ?_⟩
    rw [prodMap_pow_eq, LinearMap.prodMap_apply]
    exact Prod.ext hy1 hy2

/-- `lem:s04-ekills`(a) (`s04-ekills`), `Graph.deg0` form: if `deg ∘ T = p · deg` and `p` has an ordinary
decomposition on `R`, then `e T ⊆ R[X]⁰`. -/
theorem ordPart_le_deg0_of_aug {X : Type*} (T : Module.End R (X →₀ R)) (p : R)
    (hT : ∀ x, Finsupp.linearCombination R (fun _ : X => (1 : R)) (T x) =
      p * Finsupp.linearCombination R (fun _ : X => (1 : R)) x)
    (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    ordPart T ≤ Langlandscape.Graph.deg0 X R := by
  have hUp : (deg X R).comp T = p • deg X R := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.smul_apply, deg_eq_linearCombination, hT, smul_eq_mul]
  have h := ordPart_le_ker_deg T p hUp hdecR
  rw [deg_eq_linearCombination] at h
  intro x hx
  exact h hx

/-- `lem:s04-ekills`(a) (`s04-ekills`), `Graph.deg0` form: for `T` with `deg ∘ T = p · deg`, the ordinary part of
`T|_{R[X]⁰}` maps onto the ordinary part of `T`: `e R[X]⁰ = e R[X]` (given the ordinary decompositions of `T` and of
`p` on `R`). -/
theorem map_subtype_ordPart_deg0_eq {X : Type*} (T : Module.End R (X →₀ R)) (p : R)
    (hT : ∀ x, Finsupp.linearCombination R (fun _ : X => (1 : R)) (T x) =
      p * Finsupp.linearCombination R (fun _ : X => (1 : R)) x)
    (hK : ∀ x ∈ Langlandscape.Graph.deg0 X R, T x ∈ Langlandscape.Graph.deg0 X R)
    (hdecT : HasOrdDecomp p T) (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    Submodule.map (Langlandscape.Graph.deg0 X R).subtype
        (ordPart (R := R) (M := ↥(Langlandscape.Graph.deg0 X R)) (T.restrict hK)) = ordPart T :=
  le_antisymm (map_subtype_ordPart_restrict_le _ T hK)
    (ordPart_le_map_subtype_ordPart_restrict p _ T hK (ordPart_le_deg0_of_aug T p hT hdecR) hdecT)

/-- `lem:s04-ekills`(a) (`s04-ekills`), product form: for `T₀`, `T₁` with `deg ∘ Tᵢ = p · deg` and a
`T₀ × T₁`-stable submodule `K ⊇ R[X₀]⁰ × R[X₁]⁰`, the ordinary part of `(T₀ × T₁)|_K` maps onto `e T₀ × e T₁`. -/
theorem map_subtype_ordPart_prod_eq {X₀ X₁ : Type*} (T₀ : Module.End R (X₀ →₀ R))
    (T₁ : Module.End R (X₁ →₀ R)) (p : R)
    (hT₀ : ∀ x, Finsupp.linearCombination R (fun _ : X₀ => (1 : R)) (T₀ x) =
      p * Finsupp.linearCombination R (fun _ : X₀ => (1 : R)) x)
    (hT₁ : ∀ x, Finsupp.linearCombination R (fun _ : X₁ => (1 : R)) (T₁ x) =
      p * Finsupp.linearCombination R (fun _ : X₁ => (1 : R)) x)
    (K : Submodule R ((X₀ →₀ R) × (X₁ →₀ R))) (hK : ∀ x ∈ K, T₀.prodMap T₁ x ∈ K)
    (hK0 : ∀ x : (X₀ →₀ R) × (X₁ →₀ R),
      x.1 ∈ Langlandscape.Graph.deg0 X₀ R → x.2 ∈ Langlandscape.Graph.deg0 X₁ R → x ∈ K)
    (hdec : HasOrdDecomp p (T₀.prodMap T₁)) (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    Submodule.map K.subtype (ordPart (R := R) (M := ↥K) ((T₀.prodMap T₁).restrict hK)) =
      (ordPart T₀).prod (ordPart T₁) := by
  have hle : ordPart (T₀.prodMap T₁) ≤ K := by
    intro x hx
    rw [ordPart_prodMap, Submodule.mem_prod] at hx
    exact hK0 x (ordPart_le_deg0_of_aug T₀ p hT₀ hdecR hx.1) (ordPart_le_deg0_of_aug T₁ p hT₁ hdecR hx.2)
  rw [← ordPart_prodMap]
  exact le_antisymm (map_subtype_ordPart_restrict_le K _ hK)
    (ordPart_le_map_subtype_ordPart_restrict p K _ hK hle hdec)

end Generic

/-! ### The Brandt instances -/

section Brandt

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}
  {U : Subgroup (BHat d.a d.b)ˣ} {K K' : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`): `deg (U_p x) = p · deg x` on the edge chains
`R[E(BG)] = R[X(U₀(q)U)]` (`BG` side of `aug_UpAt`). -/
theorem aug_UpBGE (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') (R : Type*) [CommRing R]
    (x : (Tree.BG d q hq U hU).E →₀ R) :
    Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).E => (1 : R)) (UpBGE hU hUp0 R x) =
      (p : R) * Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).E => (1 : R)) x := by
  have := Tree.finite_XB_U0q hU
  exact aug_UpAt R hUp0 x

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`): `deg (U_p x) = p · deg x` on `R[V₀(BG)]`. -/
theorem aug_UpBGV0 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R]
    (x : (Tree.BG d q hq U hU).V0 →₀ R) :
    Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).V0 => (1 : R)) (UpBGV0 hU hUp R x) =
      (p : R) * Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).V0 => (1 : R)) x := by
  have := Tree.finite_XB_of_isQLevel hU
  exact aug_UpAt R hUp x

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`): `deg (U_p x) = p · deg x` on `R[V₁(BG)]`. -/
theorem aug_UpBGV1 (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) (R : Type*) [CommRing R]
    (x : (Tree.BG d q hq U hU).V1 →₀ R) :
    Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).V1 => (1 : R)) (UpBGV1 hU hUp R x) =
      (p : R) * Finsupp.linearCombination R (fun _ : (Tree.BG d q hq U hU).V1 => (1 : R)) x := by
  have := Tree.finite_XB_of_isQLevel hU
  exact aug_UpAt R hUp x

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`), middle term, formalized modulo
`Hyp.PadicOrdDecomp`: inside `ℤ_p[X(U₀(q)U)]`, the image of `e ℤ_p[X(U₀(q)U)]⁰` (the middle term of
`ordRibet_exact`) is the full ordinary part `e ℤ_p[X(U₀(q)U)] = ordPart (UpBGE …)` (`UpBGE` is `UpAt` at
`U₀(q)U`). -/
theorem map_ordPart_UpDeg0E (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Submodule.map (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
          (UpDeg0E hU hUp0 ℤ_[p])) =
      ordPart (UpBGE hU hUp0 ℤ_[p]) := by
  have := Langlandscape.Ribet.finite_BG_E hU
  exact map_subtype_ordPart_deg0_eq (UpBGE hU hUp0 ℤ_[p]) (p : ℤ_[p]) (aug_UpBGE hU hUp0 ℤ_[p])
    (fun _ hx => UpBGE_mem_deg0 hU hUp0 ℤ_[p] hx) (hdec _ (UpBGE hU hUp0 ℤ_[p]))
    (hdec ℤ_[p] (LinearMap.lsmul ℤ_[p] ℤ_[p] (p : ℤ_[p])))

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`), right term, formalized modulo
`Hyp.PadicOrdDecomp`: inside `ℤ_p[X(U)] × ℤ_p[X(U)]`, the image of `e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰)` (the right term of
`ordRibet_exact`) is `e ℤ_p[X(U)] × e ℤ_p[X(U)] = ordPart (UpBGV0 …) × ordPart (UpBGV1 …)`. -/
theorem map_ordPart_UpDeg0Prod (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hUp : IsUpLevel d p hp U K) :
    Submodule.map (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]))
          (UpDeg0Prod hU hUp ℤ_[p])) =
      (ordPart (UpBGV0 hU hUp ℤ_[p])).prod (ordPart (UpBGV1 hU hUp ℤ_[p])) := by
  have := Langlandscape.Ribet.finite_BG_V0 hU
  have := Langlandscape.Ribet.finite_BG_V1 hU
  exact map_subtype_ordPart_prod_eq (UpBGV0 hU hUp ℤ_[p]) (UpBGV1 hU hUp ℤ_[p]) (p : ℤ_[p])
    (aug_UpBGV0 hU hUp ℤ_[p]) (aug_UpBGV1 hU hUp ℤ_[p])
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])
    (fun _ hx => Submodule.mem_prod.2 ⟨UpBGV0_mem_deg0 hU hUp ℤ_[p] (Submodule.mem_prod.1 hx).1,
      UpBGV1_mem_deg0 hU hUp ℤ_[p] (Submodule.mem_prod.1 hx).2⟩)
    (fun _ h0 h1 => Submodule.mem_prod.2 ⟨h0, h1⟩)
    (hdec _ ((UpBGV0 hU hUp ℤ_[p]).prodMap (UpBGV1 hU hUp ℤ_[p])))
    (hdec ℤ_[p] (LinearMap.lsmul ℤ_[p] ℤ_[p] (p : ℤ_[p])))

/-- `lem:s04-ribetfinite` (`s04-ribetfinite`), formalized modulo `Hyp.PadicOrdDecomp`: the linear equivalence
`e ℤ_p[X(U₀(q)U)]⁰ ≃ e ℤ_p[X(U₀(q)U)]` induced by the inclusion (`map_ordPart_UpDeg0E`). -/
noncomputable def ordDeg0EEquiv (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
        (UpDeg0E hU hUp0 ℤ_[p]) ≃ₗ[ℤ_[p]] ordPart (UpBGE hU hUp0 ℤ_[p]) :=
  (Submodule.equivMapOfInjective _ (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]).injective_subtype
    (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
      (UpDeg0E hU hUp0 ℤ_[p]))).trans (LinearEquiv.ofEq _ _ (map_ordPart_UpDeg0E hdec hU hUp0))

/-- `lem:s04-ribetfinite` (`s04-ribetfinite`), formalized modulo `Hyp.PadicOrdDecomp`: the linear equivalence
`e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) ≃ e ℤ_p[X(U)] × e ℤ_p[X(U)]` induced by the inclusion (`map_ordPart_UpDeg0Prod`). -/
noncomputable def ordDeg0ProdEquiv (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hUp : IsUpLevel d p hp U K) :
    ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]))
        (UpDeg0Prod hU hUp ℤ_[p]) ≃ₗ[ℤ_[p]]
      ↥((ordPart (UpBGV0 hU hUp ℤ_[p])).prod (ordPart (UpBGV1 hU hUp ℤ_[p]))) :=
  (Submodule.equivMapOfInjective _
    (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]).injective_subtype
    (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]))
      (UpDeg0Prod hU hUp ℤ_[p]))).trans
    (LinearEquiv.ofEq _ _ (map_ordPart_UpDeg0Prod hdec hU hUp))

/-- `thm:s04-lambdaribet`(c) at level `s`, `lem:s04-ribetfinite` (`s04-lambdaribet`), formalized modulo
`Hyp.PadicOrdDecomp`: cardinal rank–nullity for the ordinary Ribet sequence with the full ordinary parts,
`rk e ℤ_p[X(U₀(q)U)] = rk (e ℤ_p[X(U)] × e ℤ_p[X(U)]) + rk e H₁` (`Module.rank`, from `rank_ordRibet` and the
equivalences `ordDeg0EEquiv`, `ordDeg0ProdEquiv`). Neither the `finrank` form with subtraction nor the formula
`rk H₁ = (q − 1)|X| + 1` is stated. -/
theorem rank_ordRibet_full (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hU : Tree.IsQLevel d q hq U)
    (hc : Tree.BGConnected d q hq U hU) (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Module.rank ℤ_[p] (ordPart (UpBGE hU hUp0 ℤ_[p])) =
      Module.rank ℤ_[p] ↥((ordPart (UpBGV0 hU hUp ℤ_[p])).prod (ordPart (UpBGV1 hU hUp ℤ_[p]))) +
        Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p])) := by
  have e1 := (ordDeg0EEquiv hdec hU hUp0).rank_eq
  have e2 := (ordDeg0ProdEquiv hdec hU hUp).rank_eq
  have h := rank_ordRibet hdec hU hc hpq hUp hUp0
  exact e1.symm.trans (h.trans (congrArg (fun c => c + Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p]))) e2))

end Brandt

end Langlandscape.Ordinary
