/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.RibetFinite

/-!
# Tests for `Langlandscape.Ordinary.RibetFinite` (S04-L12, `thm:s04-lambdaribet`(a), (c) at level `s`)

* the tower form `ordRibet_exact_Utower` at `s = 1` and its three components;
* `UpAt_comm_s0/s1` and `alpha_comm_diamond` at the tower levels `U_s`, `U₀(q) U_s`;
* the arithmetic side conditions at `p = 5`, `q = 7`;
* the abstract rank formula on `0 → ℤ → ℤ × ℤ → ℤ → 0`.
-/

set_option autoImplicit false

namespace LanglandscapeTests.S04.RibetFinite

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt Langlandscape.Ordinary

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: `5 ∉ primeFactors 7` from `5 ≠ 7`. -/
theorem five_not_mem_primeFactors_seven : (5 : ℕ) ∉ (7 : ℕ).primeFactors := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact not_mem_primeFactors_of_ne (p := 5) (q := 7) (by decide)

/-- `thm:s04-lambdaribet`(c) (`s04-lambdaribet`), test: the rank formula on `0 → ℤ → ℤ × ℤ → ℤ → 0`. -/
theorem rank_test :
    Module.rank ℤ (ℤ × ℤ) = Module.rank ℤ ℤ + Module.rank ℤ ℤ :=
  rank_eq_add_of_exact (LinearMap.inl ℤ ℤ ℤ) (LinearMap.snd ℤ ℤ ℤ) LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective

section Tower

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D} {M : ℕ}

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: the ordinary Ribet sequence at level `s = 1` is exact in the
middle (instance of `ordRibet_exact_Utower`). -/
theorem ordRibet_exact_one (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hN : ∀ s, (M * p ^ s).Coprime d.D) (hqN : ∀ s, ¬ q ∣ M * p ^ s)
    (hconn : ∀ s, 1 ≤ s → Langlandscape.Tree.BGConnected d q hq (d.Utower M p s (hN s))
      (Langlandscape.Tree.isQLevel_Utower (hqN s))) :
    Function.Exact (ordH1toDeg0 (hq := hq) (Langlandscape.Tree.isQLevel_Utower (hqN 1))
          (ne_of_not_dvd_tower le_rfl (hqN 1))
          (isUpLevel_Utower (hp := hp) (hN := hN 1) hM hpM le_rfl)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN 1) hM hpM le_rfl (Langlandscape.Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower le_rfl (hqN 1)))))
      (ordAlpha (hq := hq) (Langlandscape.Tree.isQLevel_Utower (hqN 1)) (ne_of_not_dvd_tower le_rfl (hqN 1))
          (isUpLevel_Utower (hp := hp) (hN := hN 1) hM hpM le_rfl)
          (isUpLevel_U0q_Utower (hp := hp) (hN := hN 1) hM hpM le_rfl (Langlandscape.Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower le_rfl (hqN 1))))) :=
  (ordRibet_exact_Utower hdec hM hpM hN hqN hconn 1 le_rfl).2.1

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: `U_p` commutes with `s_{0*}` at `U_s`, `U₀(q) U_s`. -/
theorem UpAt_comm_s0_tower (R : Type*) [CommRing R] {s : ℕ} {hN : (M * p ^ s).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (hqN : ¬ q ∣ M * p ^ s)
    [Finite (XB (d.Utower M p s hN))]
    [Finite (XB (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN)))] :
    (Langlandscape.Tree.s0Push d q hq (d.Utower M p s hN) R).comp
        (UpAt (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN))
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs (Langlandscape.Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs hqN))) R) =
      (UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R).comp
        (Langlandscape.Tree.s0Push d q hq (d.Utower M p s hN) R) :=
  UpAt_comm_s0 (hq := hq) R (Langlandscape.Tree.isQLevel_Utower hqN) (ne_of_not_dvd_tower hs hqN) _ _

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: `U_p` commutes with `s_{1*}` at `U_s`, `U₀(q) U_s`. -/
theorem UpAt_comm_s1_tower (R : Type*) [CommRing R] {s : ℕ} {hN : (M * p ^ s).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (hqN : ¬ q ∣ M * p ^ s)
    [Finite (XB (d.Utower M p s hN))]
    [Finite (XB (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN)))] :
    (Langlandscape.Tree.s1Push d q hq (d.Utower M p s hN) R).comp
        (UpAt (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN))
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs (Langlandscape.Tree.coprime_of_not_dvd hq)
            (not_mem_primeFactors_of_ne (ne_of_not_dvd_tower hs hqN))) R) =
      (UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R).comp
        (Langlandscape.Tree.s1Push d q hq (d.Utower M p s hN) R) :=
  UpAt_comm_s1 (hq := hq) R (Langlandscape.Tree.isQLevel_Utower hqN) (ne_of_not_dvd_tower hs hqN) _ _

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: pointwise form of `alpha_comm_diamond`,
`α(⟨t⟩ y) = (⟨t⟩ × ⟨t⟩)(α y)`. -/
theorem alpha_comm_diamond_apply (R : Type*) [CommRing R] {s : ℕ} {hN : (M * p ^ s).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (hqN : ¬ q ∣ M * p ^ s) (t : ℤ_[p]ˣ)
    (y : ZX (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN)) R) :
    Langlandscape.Graph.boundary
      (Langlandscape.Tree.BG d q hq (d.Utower M p s hN) (Langlandscape.Tree.isQLevel_Utower hqN)) R
        (Finsupp.lmapDomain R R
          (rightMulXB (d.U0q q (Langlandscape.Tree.coprime_of_not_dvd hq) (d.Utower M p s hN)) (deltaElt d p hp t)) y) =
      ((Finsupp.lmapDomain R R ⇑(diamondAct (hp := hp) (hN := hN) hM hpM hs t)).prodMap
          (Finsupp.lmapDomain R R ⇑(diamondAct (hp := hp) (hN := hN) hM hpM hs t)))
        (Langlandscape.Graph.boundary
      (Langlandscape.Tree.BG d q hq (d.Utower M p s hN) (Langlandscape.Tree.isQLevel_Utower hqN)) R y) :=
  LinearMap.congr_fun (alpha_comm_diamond (hq := hq) (hp := hp) (hN := hN) R hM hpM hs hqN t) y

end Tower

end LanglandscapeTests.S04.RibetFinite
