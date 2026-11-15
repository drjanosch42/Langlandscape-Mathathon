/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Langlandscape.Hyp.OldDecomp
public import Langlandscape.Hyp.HsiehGorFull
public import Langlandscape.Hyp.HsiehGor
public import Langlandscape.Hyp.LambdaJL
public import Langlandscape.Hyp.FreeRankTwo
public import Langlandscape.Hyp.ResidualBurnside
public import Langlandscape.Hyp.TamSpec
public import Langlandscape.Hyp.HidaControlGL2
public import Langlandscape.Hyp.KimOta
public import Langlandscape.Hyp.KimOtaRT
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Langlandscape.CommAlg.ThmE
import Langlandscape.CommAlg.Squeeze
import Langlandscape.Defect.Galois
import Langlandscape.Defect.Gorenstein
import Langlandscape.Defect.Fixed
import Mathlib.RingTheory.Ideal.Maps

/-!
# The Λ-adic integral defect formula (S06-L9a)

`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-defect` (proof steps (1)–(5)) and the interface `if:s06-defect`:
under (H0), (H1), (H2), (P) and "(H0⁻) or (Lev_M)", `(h_F) = 𝔠_q(F) = 𝔱_q(F)` as principal ideals of `I_F`, and
`η_F = (h_F) · η^B_F`. Over the abstract data `Defect.Setting`, every input is an explicit `Hyp.*` argument:

* step (1): (Gor_R) = `Hyp.HsiehGorFull` and (Gor_{R′}) (from `Hyp.HsiehGor` and `Hyp.LambdaJL` by `Setting.gor_new`) are
  **separate** arguments; with `Hyp.OldDecomp`, `thm:s06-E`(iii) gives `η_F = 𝔠_q(F) η^B_F` and `𝔠_q(F)` principal;
* step (2): `Defect.galois` (`Hyp.FreeRankTwo`, `Hyp.ResidualBurnside`): `𝔱_q(F) ⊆ 𝔠_q(F)`;
* step (3): `Setting.map_cq` (formal on the abstract data): `P(𝔠_q(F)) 𝒪 = 𝔠_q(f)`;
* step (4): under (H0⁻), `Defect.cor_fixed` (`Hyp.KimOta`, `Hyp.HidaControlGL2`); under (Lev_M), `Hyp.KimOtaRT`
  (**inclusion only**): `𝔠_q(f) ⊆ 𝔪^t`;
* step (5): `CommAlg.squeeze` with the local homomorphism `P` (`Setting.isLocalHom_P`) and `Hyp.TamSpec`.

Status: *formalized* modulo the registered hypotheses, **including the Galois half** (`Hyp.FreeRankTwo`, equivalent to
`𝔱_q ≤ 𝔠_q`; see `Defect.freeRankTwo_of_le`). (H1), (H2), (P) and (Lev_M) are not Lean arguments (not representable on
the abstract data): they are the conditions under which the cited `Hyp.*` are asserted (see their docstrings).

`defect_formula_of_le` is the core with the step-(4) output `𝔠_q(f) ≤ 𝔪^t` as hypothesis (it needs neither the DVR
property of `𝒪` nor control); `defect_formula` is `thm:s06-defect`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

open scoped TensorProduct

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]
  (D : Setting Λ I T 𝒪 G)

/-- `thm:s06-defect` (`s06-defect`), step (1), principality: under (Gor_S) and (Gor_{S′}), `c_q = λ(𝔟)` is a principal
ideal of `A` (`thm:s06-E`(i)–(iii): `c_q` is the order ideal of `x = θ mod 𝔞 = h θ′` with `θ′` unimodular, so
`c_q = (h)`). -/
private theorem exists_map_b_eq_span_s06 {A S : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [CommRing S] [Algebra A S] (N : CommAlg.NewOldData A S) {ℓ : Module.Dual A S}
    (hℓ : CommAlg.IsGorensteinWith A S ℓ) (lam' : (S ⧸ N.𝔞) →ₐ[A] A)
    (hS' : CommAlg.IsGorenstein A (S ⧸ N.𝔞)) :
    ∃ h : A, N.𝔟.map (CommAlg.ThmE.lam N lam') = Ideal.span {h} := by
  obtain ⟨_, hℓ'⟩ := hS'
  obtain ⟨θ', hθ', ψ, hψ⟩ := CommAlg.ThmE.unimodular_of_isGorenstein N lam' hℓ'
  have hx : Ideal.Quotient.mk N.𝔞 (CommAlg.LemmaS.theta hℓ (CommAlg.ThmE.lam N lam')) ∈
      (CommAlg.ann (RingHom.ker lam')).restrictScalars A :=
    CommAlg.ThmE.mk_theta_mem_ann N hℓ lam'
  rw [hθ', Submodule.mem_span_singleton] at hx
  obtain ⟨h, hh⟩ := hx
  refine ⟨h, ?_⟩
  rw [CommAlg.ThmE.c_eq_orderIdeal N hℓ lam']
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    rw [Module.Dual.eval_apply, ← hh, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨ψ, ?_⟩
    rw [Module.Dual.eval_apply, ← hh, map_smul, hψ, smul_eq_mul, mul_one]

/-- `thm:s06-defect` (`s06-defect`), steps (1)–(3) and (5), with the output of step (4) as the hypothesis
`hle : 𝔠_q(f) ≤ 𝔪^t` (`mathematics/chapters/s06/s06-m3.tex`). (Gor_R) (`hGor`) and (Gor_{R′}) (`hGor'`) are separate.
Conclusion: `η_F = (h) η^B_F`, `(h) = 𝔠_q(F)` and `𝔠_q(F) = 𝔱_q(F)`. -/
theorem defect_formula_of_le (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hGor' : CommAlg.IsGorenstein I (D.R ⧸ D.𝔞))
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (hle : D.cqk ≤ IsLocalRing.maximalIdeal 𝒪 ^ D.t) :
    ∃ h : I, CommAlg.congruenceIdeal D.lam = Ideal.span {h} * CommAlg.congruenceIdeal (A := I)
        (S := D.R ⧸ D.𝔞) D.lam' ∧
      Ideal.span {h} = D.cq ∧ D.cq = D.tq := by
  obtain ⟨ℓ, hℓ⟩ : CommAlg.IsGorenstein I D.R := hGor
  -- step (1): `η_F = 𝔠_q(F) η^B_F`, and `𝔠_q(F) = (h)`
  have hE : CommAlg.congruenceIdeal D.lam = D.cq * CommAlg.congruenceIdeal (A := I)
      (S := D.R ⧸ D.𝔞) D.lam' :=
    CommAlg.ThmE.eta_eq_c_mul_of_isGorenstein (D.newOld hdec) hℓ D.lam' hGor'
  obtain ⟨h, hh⟩ : ∃ h : I, D.cq = Ideal.span {h} :=
    exists_map_b_eq_span_s06 (D.newOld hdec) hℓ D.lam' hGor'
  -- step (2): `𝔱_q(F) ⊆ 𝔠_q(F)`
  have hgal : D.tq ≤ D.cq := galois D hfr hbur
  -- steps (3), (4): `P(𝔠_q(F)) 𝒪 = 𝔠_q(f) ⊆ 𝔪^t = P(𝔱_q(F)) 𝒪`
  obtain ⟨-, -, htmap, htne⟩ := htam
  have hcq_le : D.cq.map D.P ≤ D.tq.map D.P := by
    rw [D.map_cq, htmap]
    exact hle
  -- step (5): the squeeze
  have := D.isLocalHom_P
  have hPh : D.P h ≠ 0 := by
    intro hzero
    apply htne
    rw [← htmap, eq_bot_iff]
    calc D.tq.map D.P ≤ D.cq.map D.P := Ideal.map_mono hgal
      _ = ⊥ := by
        rw [hh, Ideal.map_span, Set.image_singleton, hzero]
        exact Ideal.span_singleton_eq_bot.2 rfl
  have hP : Ideal.span {D.P h} ≤ Ideal.span (D.P '' D.tq) := by
    calc Ideal.span {D.P h} = D.cq.map D.P := by rw [hh, Ideal.map_span, Set.image_singleton]
      _ ≤ D.tq.map D.P := hcq_le
      _ = Ideal.span (D.P '' D.tq) := rfl
  have hsq : D.tq = Ideal.span {h} := CommAlg.squeeze D.P (hgal.trans hh.le) hPh hP
  exact ⟨h, by rw [hE, hh], hh.symm, hh.trans hsq.symm⟩

-- `[IsDomain 𝒪]` and `[IsLocalRing 𝒪]` are both required by `Defect.Setting`; the overlap (`Nontrivial`) is inherent.
set_option linter.overlappingInstances false in
/-- **The Λ-adic integral defect formula**, `thm:s06-defect` (`s06-defect`) of `mathematics/chapters/s06/s06-m3.tex`
(interface `if:s06-defect`): `η_F = (h) · η^B_F` with `(h) = 𝔠_q(F) = 𝔱_q(F)`.
Status: *formalized* modulo registered hypotheses, including the Galois half (`Hyp.FreeRankTwo`, equivalent to `𝔱_q ≤ 𝔠_q`
by `freeRankTwo_of_le`). Hypotheses, all explicit as Lean arguments except (H1), (H2), (P) and (Lev_M) (not representable on
the abstract data, not arguments: they are the conditions under which the cited `Hyp.*` are asserted, see their
docstrings; likewise "`f = F_P` is a `q`-new newform of weight `2 ≤ k ≤ p − 1`"): (H0) (`h0`, guard); step (1): `Hyp.OldDecomp` (`lem:s06-decomp`), (Gor_R) `Hyp.HsiehGorFull`
and, **separately**, (Gor_{R′}) from `Hyp.HsiehGor` (Hsieh Thm 4.5) transported by `Hyp.LambdaJL` (`Setting.gor_new`);
step (2): `Hyp.FreeRankTwo`, `Hyp.ResidualBurnside` (`prop:s06-galois`); step (3): formal (`Setting.map_cq`);
step (4): either (H0⁻) with `Hyp.KimOta` (`thm:s06-KO`, through `cor:s06-fixed`, which uses `Hyp.HidaControlGL2` and the
DVR `𝒪 = 𝒪̃_P`, the explicit argument `h𝒪`), or `Hyp.KimOtaRT` (`prop:s06-levM`, (Lev_M) route, inclusion `𝔠_q(f) ⊆ 𝔪^t` only); step (5):
`Hyp.TamSpec` (`lem:s06-tam`) and the squeeze with the local `P`. -/
theorem defect_formula {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M] [Module TB M]
    (h𝒪 : IsDiscreteValuationRing 𝒪)
    (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB)
    (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ) (hGor' : Hyp.HsiehGor Λ TB M)
    (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (h0 : H0 p Dq Mq) (hctl : Hyp.HidaControlGL2 D p Dq Mq)
    (h4 : (D.H0minus p Dq ∧ Hyp.KimOta D p Dq Mq) ∨ Hyp.KimOtaRT D p Dq Mq) :
    ∃ h : I, CommAlg.congruenceIdeal D.lam = Ideal.span {h} * CommAlg.congruenceIdeal (A := I)
        (S := D.R ⧸ D.𝔞) D.lam' ∧
      Ideal.span {h} = D.cq ∧ D.cq = D.tq := by
  refine defect_formula_of_le D hdec hGor (D.gor_new Dq Mq p genGL genB hJL hGor') hfr hbur htam ?_
  rcases h4 with ⟨h0m, hKO⟩ | hRT
  · exact (cor_fixed D h𝒪 h0 h0m hGor hctl hKO).le
  · exact hRT h0

end Langlandscape.Defect
