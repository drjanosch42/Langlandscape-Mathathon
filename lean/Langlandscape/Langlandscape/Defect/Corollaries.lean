/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Main
import Langlandscape.Defect.Fixed
public import Langlandscape.Hyp.TamSpec
import Langlandscape.CommAlg.BaseChange
import Langlandscape.CommAlg.DVR

/-!
# All weights of the branch (S06-L9b, part 2)

`mathematics/chapters/s06/s06-m3.tex`, `cor:s06-allweights`, on the abstract data `Defect.Setting`. Under the
hypotheses of the defect formula (`thm:s06-defect`, `Defect.defect_formula`), let `P′ = algebraMap I 𝒪′` be another
arithmetic point (weight `k′ ≥ 3`, trivial character, `q`-new `f′ = F_{P′}`; not representable on the abstract data),
`𝒪′ = 𝒪̃_{P′}` a DVR, `t′ = t_{f′}(q)`, and `D′ = D.withPoint 𝒪′ hP′ t′` the same data at `P′`. Then

* `𝔠_q(f′) = 𝔪′^{t′} = (ϖ_{P′}^{t_{f′}(q)})`;
* `η_{f′}(N) = 𝔪′^{t′} · η_{f′}(M, q)` (ring-theoretic congruence ideals of `R_{k′}` and its `q`-new quotient; taking
  `ord_ϖ` gives the chapter's formula once both are non-zero, which is the newform condition at `P′`);
* `η_{f′}(N) = P′(η(R, λ)) 𝒪′` (Lemma S: the congruence ideal specialises along `P′`).

The only inputs at `P′` are Hida control (`Hyp.HidaControlGL2` at `D′`) and `lem:s06-tam` (`Hyp.TamSpec` at `D′`); no
`R = 𝐓` theorem is used at `P′`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

open scoped TensorProduct

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `lem:s06-control` (`s06-control`), `cor:s06-allweights` (`s06-allweights`): `λ_f : 𝒪 ⊗[I] R → 𝒪` is the base
change `λ ⊗ 𝒪` of `λ : R → I_F` along `P` (the form in which `CommAlg.LemmaS.congruenceIdeal_baseChange` applies). -/
theorem Setting.lamk_eq_liftEquiv (D : Setting Λ I T 𝒪 G) :
    D.lamk = AlgHom.liftEquiv I 𝒪 D.R 𝒪 ((Algebra.ofId I 𝒪).comp D.lam) := by
  refine Algebra.TensorProduct.ext_ring (AlgHom.ext fun x => ?_)
  show D.lamk ((1 : 𝒪) ⊗ₜ[I] x) = AlgHom.liftEquiv I 𝒪 D.R 𝒪 ((Algebra.ofId I 𝒪).comp D.lam) ((1 : 𝒪) ⊗ₜ[I] x)
  rw [D.lamk_one_tmul, AlgHom.liftEquiv_tmul, one_smul, AlgHom.comp_apply, Algebra.ofId_apply]

-- `[IsDomain 𝒪]` and `[IsLocalRing 𝒪]` are both required by `Defect.Setting`; the overlap (`Nontrivial`) is inherent.
set_option linter.overlappingInstances false in
/-- `cor:s06-allweights` (`s06-allweights`), `mathematics/chapters/s06/s06-m3.tex`: all weights of the branch. Under
the hypotheses of `thm:s06-defect` (those of `Defect.defect_formula`), let `P′ = algebraMap I 𝒪′` be any arithmetic
point of weight `k′ ≥ 3` with trivial character (including `k′ ≥ p`) and `q`-new `f′ = F_{P′}`, `𝒪′ = 𝒪̃_{P′}` a DVR,
`t′ = t_{f′}(q)`, with `lem:s06-tam` (`htam'`) and Hida control (`hctl'`) at `P′`. Then `𝔠_q(f′) = 𝔪′^{t′}`,
`η(R_{k′}, λ_{f′}) = 𝔪′^{t′} η(R_{k′} ⧸ 𝔞_{k′}, λ′_{f′})`, and `η(R_{k′}, λ_{f′}) = P′(η(R, λ)) 𝒪′`.

These are identities of ideals; no newform or non-vanishing hypothesis at `P′` is assumed. The chapter's
`ord_ϖ η_{f′}(N) − ord_ϖ η_{f′}(M, q) = t_{f′}(q)` additionally needs `𝔠 ≠ 0` at both points (the newform condition
at `P′`), which is not assumed and not proved here. The arithmetic conditions on `P′` (weight `k′ ≥ 3`, trivial
character, `q`-new `f′`) are not arguments: they are the meaning of `htam'`, `hctl'`. As for `defect_formula`,
(H1), (H2), (P) and (Lev_M) are not Lean arguments (see there). The DVR properties of `𝒪` and `𝒪′` are the explicit
arguments `h𝒪`, `h𝒪′`.

Proof (chapter): `defect_formula` gives `𝔠_q(F) = 𝔱_q(F)`; `Setting.map_cq` at `P′` (`lem:s06-control`(b)) and
`Hyp.TamSpec` at `P′` (`lem:s06-tam`(b)) give `𝔠_q(f′) = P′(𝔱_q(F)) 𝒪′ = 𝔪′^{t′}`; Thm E(iii) over the DVR `𝒪′`
(`CommAlg.ThmE.eta_eq_c_mul_of_dvr`, with (Gor) from (Gor_R) by `IsGorenstein.baseChange` and the weight-`k′` new/old
data from `hctl'`) gives the second identity; `CommAlg.LemmaS.congruenceIdeal_baseChange` gives the third. -/
theorem cor_allweights (D : Setting Λ I T 𝒪 G) {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M]
    [Module TB M] (h𝒪 : IsDiscreteValuationRing 𝒪) (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T)
    (genB : Hyp.LambdaJLGen → TB) (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ)
    (hGor' : Hyp.HsiehGor Λ TB M) (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (h0 : H0 p Dq Mq) (hctl : Hyp.HidaControlGL2 D p Dq Mq)
    (h4 : (D.H0minus p Dq ∧ Hyp.KimOta D p Dq Mq) ∨ Hyp.KimOtaRT D p Dq Mq)
    {𝒪' : Type*} [CommRing 𝒪'] [IsDomain 𝒪'] [IsLocalRing 𝒪'] [Algebra I 𝒪']
    (h𝒪' : IsDiscreteValuationRing 𝒪') (hP' : IsLocalHom (algebraMap I 𝒪')) (t' : ℕ)
    (htam' : Hyp.TamSpec (D.withPoint 𝒪' hP' t'))
    (hctl' : Hyp.HidaControlGL2 (D.withPoint 𝒪' hP' t') p Dq Mq) :
    (D.withPoint 𝒪' hP' t').cqk = IsLocalRing.maximalIdeal 𝒪' ^ t' ∧
      CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lamk =
        IsLocalRing.maximalIdeal 𝒪' ^ t' * CommAlg.congruenceIdeal (A := 𝒪')
            (S := (D.withPoint 𝒪' hP' t').Rk ⧸ (D.withPoint 𝒪' hP' t').𝔞k) (D.withPoint 𝒪' hP' t').lam'k ∧
      CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lamk =
        (CommAlg.congruenceIdeal D.lam).map (algebraMap I 𝒪') := by
  have := h𝒪'
  obtain ⟨_, _, _, hcqtq⟩ :=
    defect_formula D h𝒪 Dq Mq p genGL genB hJL hGor' hdec hGor hfr hbur htam h0 hctl h4
  -- `𝔠_q(f′) = P′(𝔠_q(F)) 𝒪′ = P′(𝔱_q(F)) 𝒪′ = 𝔪′^{t′}`
  have h1 : (D.withPoint 𝒪' hP' t').cqk = IsLocalRing.maximalIdeal 𝒪' ^ t' := by
    rw [← Setting.map_cq (D.withPoint 𝒪' hP' t')]
    change D.cq.map (algebraMap I 𝒪') = _
    rw [hcqtq]
    obtain ⟨-, -, htmap', -⟩ := htam'
    exact htmap'
  -- Thm E(iii) over the DVR `𝒪′`
  have hG : CommAlg.IsGorenstein I D.R := hGor
  have hS : CommAlg.IsGorenstein 𝒪' (D.withPoint 𝒪' hP' t').Rk := CommAlg.IsGorenstein.baseChange 𝒪' hG
  have key : CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lamk =
      (D.withPoint 𝒪' hP' t').cqk * CommAlg.congruenceIdeal (A := 𝒪')
          (S := (D.withPoint 𝒪' hP' t').Rk ⧸ (D.withPoint 𝒪' hP' t').𝔞k) (D.withPoint 𝒪' hP' t').lam'k :=
    CommAlg.ThmE.eta_eq_c_mul_of_dvr ((D.withPoint 𝒪' hP' t').newOldAt h0 hctl') hS
      (D.withPoint 𝒪' hP' t').lam'k
  -- Lemma S: the congruence ideal specialises along `P′`
  obtain ⟨ℓ, hℓ⟩ := hG
  -- instance for `congruenceIdeal_baseChange` (unused there, part-1 R4)
  have _hP'loc : IsLocalHom (algebraMap I 𝒪') := hP'
  have hbc : CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lamk =
      (CommAlg.congruenceIdeal D.lam).map (algebraMap I 𝒪') := by
    rw [Setting.lamk_eq_liftEquiv]
    exact CommAlg.LemmaS.congruenceIdeal_baseChange (A' := 𝒪') hℓ D.lam
  refine ⟨h1, ?_, hbc⟩
  rw [← h1]
  exact key

end Langlandscape.Defect
