/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.PadicDecomp
import Langlandscape.Ordinary.RibetFiniteFull
import Langlandscape.Ordinary.Tower
import Langlandscape.Ordinary.TowerRank
import Langlandscape.Ordinary.Limit

/-!
# Unconditional forms of the `ℤ_[p]` tower theorems (S04-L3, second part; written in S04-L17b)

Design D-e (`plan/implementation/stage-04.md` §0.2): every `ℤ_[p]` tower theorem takes
`hdec : Hyp.PadicOrdDecomp p` as an explicit argument; `Ordinary.padicOrdDecomp_holds p` (S04-L3,
`Ordinary/PadicDecomp.lean`) proves it. This file specialises the merged `hdec`-taking theorems with it.

Covered:
* `Ordinary/RibetFinite.lean` (S04-L12, `thm:s04-lambdaribet`(a), (c) at level `s`): `ordRibet_injective`,
  `ordRibet_exact_mid`, `ordRibet_surjective`, `ordRibet_exact`, `ordRibet_exact_Utower`, `rank_ordRibet`;
* `Ordinary/RibetFiniteFull.lean` (S04-L17b, `lem:s04-ribetfinite`): `map_ordPart_UpDeg0E`,
  `map_ordPart_UpDeg0Prod`, `rank_ordRibet_full`;
* `Ordinary/Tower.lean` (S04-L10, `lem:s04-ekills`(a),(d), `thm:s04-control`(a) finite part): `ekillsA_tower` (the
  stage-05 export), `perfect_ordPart_pairing_tower_padic`, `ord_control_finite`, `ord_control_finite_U0q`;
* `Ordinary/TowerRank.lean` (S04-L10b, `prop:s04-freeA`): `ordFree_finite`;
* `Ordinary/Limit.lean` (S04-L13b, `def:s04-Mord`, `thm:s04-lambdaribet`(a)): `TowerHyp.mordTrans_surjective`,
  `Mord.proj_surjective`, `RibetHyp.ribet_level_exact`, `lim_exact_ribet` (the latter keeps its argument `hA`,
  i.e. it is formalized modulo the surjectivity of the `A`-transitions, `Hyp.InvLimExact`).

Each declaration is named `<name>_uncond`.

## Status

*formalized*, unconditional (S04-L3): no `Hyp.*` argument remains; connectivity of `BG(U_s, q)` stays an explicit
argument where the original theorem has it, and `lim_exact_ribet_uncond` keeps `hA`. Never `open Graph` (clash with `_root_.Graph`).
-/

set_option autoImplicit false

namespace Langlandscape.Ordinary

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

section RibetFinite

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}
  {U : Subgroup (BHat d.a d.b)ˣ} {K K' : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), unconditional (S04-L3): `ordRibet_injective` with
`padicOrdDecomp_holds`. -/
theorem ordRibet_injective_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Injective (ordH1toDeg0 hU hpq hUp hUp0) :=
  ordRibet_injective (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), unconditional (S04-L3): `ordRibet_exact_mid` with
`padicOrdDecomp_holds`. -/
theorem ordRibet_exact_mid_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Exact (ordH1toDeg0 hU hpq hUp hUp0) (ordAlpha hU hpq hUp hUp0) :=
  ordRibet_exact_mid (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), unconditional (S04-L3): `ordRibet_surjective` with
`padicOrdDecomp_holds`. -/
theorem ordRibet_surjective_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Surjective (ordAlpha hU hpq hUp hUp0) :=
  ordRibet_surjective (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

/-- `thm:s04-lambdaribet`(a) at level `s` (`s04-lambdaribet`), unconditional (S04-L3): `ordRibet_exact` with
`padicOrdDecomp_holds`: `0 → e H₁ → e ℤ_p[X(U₀(q)U)]⁰ → e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) → 0` is exact, given
connectivity of `BG(U, q)`. -/
theorem ordRibet_exact_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Function.Injective (ordH1toDeg0 hU hpq hUp hUp0) ∧
      Function.Exact (ordH1toDeg0 hU hpq hUp hUp0) (ordAlpha hU hpq hUp hUp0) ∧
      Function.Surjective (ordAlpha hU hpq hUp hUp0) :=
  ordRibet_exact (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

/-- `thm:s04-lambdaribet`(a) at every level `s ≥ 1` (`s04-lambdaribet`), unconditional (S04-L3):
`ordRibet_exact_Utower` with `padicOrdDecomp_holds`; the connectivity of `BG(U_s, q)` stays explicit (`hconn`). -/
theorem ordRibet_exact_Utower_uncond {M : ℕ} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
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
  ordRibet_exact_Utower (hp := hp) (padicOrdDecomp_holds p) hM hpM hN hqN hconn s hs

/-- `thm:s04-lambdaribet`(c) at level `s` (`s04-lambdaribet`), unconditional (S04-L3): `rank_ordRibet` with
`padicOrdDecomp_holds` (cardinal rank–nullity on degree-zero parts). -/
theorem rank_ordRibet_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p])) (UpDeg0E hU hUp0 ℤ_[p])) =
      Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p])) (UpDeg0Prod hU hUp ℤ_[p])) +
        Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p])) :=
  rank_ordRibet (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`), unconditional (S04-L3): `map_ordPart_UpDeg0E`
with `padicOrdDecomp_holds`: `e ℤ_p[X(U₀(q)U)]⁰ = e ℤ_p[X(U₀(q)U)]` inside `ℤ_p[X(U₀(q)U)]`. -/
theorem map_ordPart_UpDeg0E_uncond (hU : Tree.IsQLevel d q hq U)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Submodule.map (Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q hq U hU).E ℤ_[p]))
          (UpDeg0E hU hUp0 ℤ_[p])) =
      ordPart (UpBGE hU hUp0 ℤ_[p]) :=
  map_ordPart_UpDeg0E (padicOrdDecomp_holds p) hU hUp0

/-- `lem:s04-ribetfinite`, `lem:s04-ekills`(a) (`s04-ribetfinite`), unconditional (S04-L3):
`map_ordPart_UpDeg0Prod` with `padicOrdDecomp_holds`: `e (ℤ_p[X(U)]⁰ × ℤ_p[X(U)]⁰) = e ℤ_p[X(U)] × e ℤ_p[X(U)]`. -/
theorem map_ordPart_UpDeg0Prod_uncond (hU : Tree.IsQLevel d q hq U) (hUp : IsUpLevel d p hp U K) :
    Submodule.map (Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q hq U hU) ℤ_[p]))
          (UpDeg0Prod hU hUp ℤ_[p])) =
      (ordPart (UpBGV0 hU hUp ℤ_[p])).prod (ordPart (UpBGV1 hU hUp ℤ_[p])) :=
  map_ordPart_UpDeg0Prod (padicOrdDecomp_holds p) hU hUp

/-- `thm:s04-lambdaribet`(c) at level `s`, `lem:s04-ribetfinite` (`s04-lambdaribet`), unconditional (S04-L3):
`rank_ordRibet_full` with `padicOrdDecomp_holds` (cardinal rank–nullity with the full ordinary parts). -/
theorem rank_ordRibet_full_uncond (hU : Tree.IsQLevel d q hq U) (hc : Tree.BGConnected d q hq U hU)
    (hpq : p ≠ q) (hUp : IsUpLevel d p hp U K)
    (hUp0 : IsUpLevel d p hp (d.U0q q (Tree.coprime_of_not_dvd hq) U) K') :
    Module.rank ℤ_[p] (ordPart (UpBGE hU hUp0 ℤ_[p])) =
      Module.rank ℤ_[p] ↥((ordPart (UpBGV0 hU hUp ℤ_[p])).prod (ordPart (UpBGV1 hU hUp ℤ_[p]))) +
        Module.rank ℤ_[p] (ordPart (R := ℤ_[p])
          (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q hq U hU) ℤ_[p])) (UpH1 hU hpq hUp hUp0 ℤ_[p])) :=
  rank_ordRibet_full (padicOrdDecomp_holds p) hU hc hpq hUp hUp0

end RibetFinite

/-! ### The Brandt tower (S04-L10) -/

section Tower

open scoped Classical

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s04-ekills`(a) (`s04-ekills`), **stage-05 export**, unconditional (S04-L3): `ekillsA_tower` with
`padicOrdDecomp_holds`: for `s ≥ 1`, `e ℤ_[p][X_s]⁰ = e ℤ_[p][X_s]`. -/
theorem ekillsA_tower_uncond (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])))
          (UpKer (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (p : ℤ_[p]) (deg_comp_UpHom ℤ_[p] hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]) :=
  ekillsA_tower (d := d) (hN := hN) (hp := hp) (padicOrdDecomp_holds p) hM hpM hs

/-- `lem:s04-ekills`(d) (`s04-ekills`), unconditional (S04-L3): `perfect_ordPart_pairing_tower_padic` with
`padicOrdDecomp_holds`: for `s ≥ 1`, `p ≥ 5`, `e ℤ_[p][X_s] × e* ℤ_[p][X_s] → ℤ_[p]` is perfect. -/
theorem perfect_ordPart_pairing_tower_padic_uncond (h5 : 5 ≤ p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ((deltaPairing (Xs d M p s hN) ℤ_[p]).domRestrict₁₂ (ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]))
      (ordPart (UpStar d M p s hN hp hM hpM hs ℤ_[p]))).IsPerfPair :=
  perfect_ordPart_pairing_tower_padic (d := d) (hN := hN) (hp := hp) (padicOrdDecomp_holds p) h5 hM hpM hs

end Tower

section TowerControl

open scoped Classical

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), unconditional (S04-L3): `ord_control_finite`
with `padicOrdDecomp_holds`: `π_* : e ℤ_[p][X_{s+1}] → e ℤ_[p][X_s]` is surjective with kernel `e ∩ ker π''_*`. -/
theorem ord_control_finite_uncond {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Function.Surjective (ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
        (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) ℤ_[p]) ∧
      ∀ x, ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
          (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) ℤ_[p] x = 0 ↔
        piPP_push d M p s hN hN' hp ℤ_[p] (x : ZX (d.Utower M p (s + 1) hN') ℤ_[p]) = 0 :=
  ord_control_finite (hp := hp) (hN := hN) (hN' := hN') (padicOrdDecomp_holds p) hM hpM hs

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), at `U_0(q) UU_s`, unconditional (S04-L3):
`ord_control_finite_U0q` with `padicOrdDecomp_holds`. -/
theorem ord_control_finite_U0q_uncond {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {q : ℕ}
    (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors)
    [Finite (XB (d.U0q q hq (d.Utower M p (s + 1) hN')))] [Finite (XB (d.U0q q hq (UtowerP d M p s hN hp)))]
    [Finite (XB (d.U0q q hq (d.Utower M p s hN)))] :
    Function.Surjective (ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
        (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
        (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) ℤ_[p]) ∧
      ∀ x, ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
          (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) ℤ_[p] x = 0 ↔
        pushforward (d.U0q q hq (d.Utower M p (s + 1) hN')) (d.U0q q hq (UtowerP d M p s hN hp)) ℤ_[p]
          (x : ZX (d.U0q q hq (d.Utower M p (s + 1) hN')) ℤ_[p]) = 0 :=
  ord_control_finite_U0q (hp := hp) (hN := hN) (hN' := hN') (padicOrdDecomp_holds p) hM hpM hs hq hpq

end TowerControl

/-! ### Freeness over `ℤ_p[Δ_s]` (S04-L10b) -/

section TowerRank

open scoped Classical

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `prop:s04-freeA` (`s04-freeA`), unconditional (S04-L3): `ordFree_finite` with `padicOrdDecomp_holds`: for `s ≥ 1`,
`p ≥ 5`, `e ℤ_p[X_s]` is a finite free `ℤ_p[Δ_s]`-module. -/
theorem ordFree_finite_uncond (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra ℤ_[p] (DeltaS p s)) (ordPartTower d M p s hN hp ℤ_[p] hM hpM hs) ∧
      Module.Finite (MonoidAlgebra ℤ_[p] (DeltaS p s)) (ordPartTower d M p s hN hp ℤ_[p] hM hpM hs) :=
  ordFree_finite (d := d) (hN := hN) (hp := hp) (padicOrdDecomp_holds p) hM hpM hs h5

end TowerRank

/-! ### Inverse limits (S04-L13b) -/

section Limit

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`, `s04-control`), unconditional (S04-L3):
`TowerHyp.mordTrans_surjective` with `padicOrdDecomp_holds`: the transitions `e ℤ_p[X_{s+1}] → e ℤ_p[X_s]` are
surjective. -/
theorem TowerHyp.mordTrans_surjective_uncond {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p)
    (n : ℕ) : Function.Surjective (T.mordTrans n) :=
  TowerHyp.mordTrans_surjective T (padicOrdDecomp_holds p) n

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`), unconditional (S04-L3): `Mord.proj_surjective` with
`padicOrdDecomp_holds`: every projection `M_ord(U) → e ℤ_p[X_s]` is surjective. -/
theorem Mord.proj_surjective_uncond {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p) (n : ℕ) :
    Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans n) :=
  Mord.proj_surjective T (padicOrdDecomp_holds p) n

/-- `thm:s04-lambdaribet`(a) at level `n + 1` (`s04-lambdaribet`), unconditional (S04-L3):
`RibetHyp.ribet_level_exact` with `padicOrdDecomp_holds`; connectivity stays explicit (`hconn`). -/
theorem RibetHyp.ribet_level_exact_uncond {d : DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (H : RibetHyp d q M p)
    (hconn : ∀ s ≥ 1, Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s)) (Tree.isQLevel_Utower (H.hqN s)))
    (n : ℕ) :
    Function.Injective (H.ribI n) ∧ Function.Exact (H.ribI n) (H.ribAlpha n) ∧
      Function.Surjective (H.ribAlpha n) :=
  RibetHyp.ribet_level_exact H (padicOrdDecomp_holds p) hconn n

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), unconditional (S04-L3) in `hdec`: `lim_exact_ribet` with
`padicOrdDecomp_holds`. Still conditional on the connectivity `hconn` and on the surjectivity `hA` of the
`A`-transitions (`Hyp.InvLimExact`); `ℤ_p`-linear, degree-zero form (see `lim_exact_ribet`). -/
theorem lim_exact_ribet_uncond {d : DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (H : RibetHyp d q M p)
    (hconn : ∀ s ≥ 1, Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s)) (Tree.isQLevel_Utower (H.hqN s)))
    (hA : ∀ n, Function.Surjective (H.transA n)) :
    Function.Injective (xordToLimB H) ∧ Function.Exact (xordToLimB H) (alphaLim H) ∧
      Function.Surjective (alphaLim H) :=
  lim_exact_ribet H (padicOrdDecomp_holds p) hconn hA

end Limit

end Langlandscape.Ordinary
