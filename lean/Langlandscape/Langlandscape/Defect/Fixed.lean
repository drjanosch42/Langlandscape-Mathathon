/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Langlandscape.Hyp.HsiehGorFull
public import Langlandscape.Hyp.HidaControlGL2
public import Langlandscape.Hyp.KimOta
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Langlandscape.CommAlg.BaseChange
import Langlandscape.CommAlg.DVR
import Mathlib.RingTheory.Ideal.Operations

/-!
# Control of `𝔠_q` and the fixed-weight corollary (S06-L9a, file plan of the L8a notes)

`mathematics/chapters/s06/s06-m3.tex`: `lem:s06-control`(b) (the formal half: `P(𝔠_q(F)) 𝒪̃_P = 𝔠_q(f)` on the abstract
data) and `cor:s06-fixed` (`𝔠_q(f) = (ϖ^{t_f(q)})` under (H0), (H0⁻)). This file is separate from
`Defect/Corollaries.lean` because `Defect.defect_formula` (`Defect/Main.lean`) uses `cor_fixed`, while
`cor_allweights` (`Defect/Corollaries.lean`) uses `defect_formula` (no import cycle).

* `Setting.lamk_one_tmul`: `λ_f (1 ⊗ x) = P (λ x)`;
* `Setting.map_cq`: `P(𝔠_q(F)) 𝒪 = 𝔠_q(f)` (formal: `𝔟_k` is the extension of `𝔟`, `λ_f` the base change of `λ`);
* `cor_fixed`: `𝔠_q(f) = 𝔪^t` from `ThmE.eta_eq_c_mul_of_dvr` on `R_k = 𝒪 ⊗[I] R` (whose (Gor) is the base change of
  (Gor_R), `Hyp.HsiehGorFull`, along `P`; no extra hypothesis) and Kim–Ota (`Hyp.KimOta`), cancelling `η(λ′_f) ≠ 0`.
  The DVR property of `𝒪 = 𝒪̃_P` is an explicit argument `h𝒪` (made an instance inside the proof).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

open scoped TensorProduct

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]
  (D : Setting Λ I T 𝒪 G)

namespace Setting

/-- `lem:s06-control` (`s06-control`): the base change `λ_f` of `λ` along `P` satisfies `λ_f (1 ⊗ x) = P (λ x)`. -/
theorem lamk_one_tmul (x : D.R) : D.lamk ((1 : 𝒪) ⊗ₜ[I] x) = D.P (D.lam x) := by
  have h : D.lamk ((1 : 𝒪) ⊗ₜ[I] x) = (1 : 𝒪) * D.P (D.lam x) := rfl
  rw [h, one_mul]

/-- `lem:s06-control` (`s06-control`)(b), formal half (step (3) of `thm:s06-defect`): `P(𝔠_q(F)) 𝒪̃_P = 𝔠_q(f)`,
with `𝔠_q(f) = λ_f(𝔟_k)` computed on `R_k = 𝒪 ⊗[I] R`. -/
theorem map_cq : D.cq.map D.P = D.cqk := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Setting.cq, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, ← D.lamk_one_tmul]
    have hx' : (Algebra.TensorProduct.includeRight : D.R →ₐ[I] 𝒪 ⊗[I] D.R) x ∈ D.𝔟k :=
      Ideal.mem_map_of_mem _ hx
    rw [Algebra.TensorProduct.includeRight_apply] at hx'
    exact Ideal.mem_map_of_mem _ hx'
  · rw [Setting.cqk, Setting.𝔟k, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, D.lamk_one_tmul]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

end Setting

/-- `cor:s06-fixed` (`s06-fixed`), auxiliary: in a principal ideal domain, `J K ≤ J′ K` with `K ≠ 0` gives `J ≤ J′`. -/
private theorem le_of_mul_le_mul_right_s06 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {J J' K : Ideal R} (hK : K ≠ ⊥) (h : J * K ≤ J' * K) : J ≤ J' := by
  obtain ⟨y, rfl⟩ := Submodule.IsPrincipal.principal K
  change J * Ideal.span {y} ≤ J' * Ideal.span {y} at h
  have hy : y ≠ 0 := by
    rintro rfl
    exact hK (Ideal.span_singleton_eq_bot.2 rfl)
  intro x hx
  obtain ⟨z, hz, hzx⟩ := Ideal.mem_mul_span_singleton.1
    (h (Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self y)))
  rwa [mul_right_cancel₀ hy hzx] at hz

-- `[IsDomain 𝒪]` and `[IsLocalRing 𝒪]` are both required by `Defect.Setting`; the overlap (`Nontrivial`) is inherent.
set_option linter.overlappingInstances false in
/-- `cor:s06-fixed` (`s06-fixed`), `mathematics/chapters/s06/s06-m3.tex`: under (H0) and (H0⁻) (explicit guards), (Gor_R)
(`Hyp.HsiehGorFull`, base-changed along `P`), control at `P` (`Hyp.HidaControlGL2`) and Kim–Ota (`Hyp.KimOta`), with
`𝒪 = 𝒪̃_P` a DVR (explicit argument `h𝒪`), `𝔠_q(f) = (ϖ^{t_f(q)})` (written `𝔪^t`). (H1), (H2), (P) and (Lev_M) are not Lean
arguments (not representable on the abstract data; they are the conditions under which the cited `Hyp.*` are asserted). Proof: `thm:s06-E`(iii), DVR half,
on `R_k` gives `η(λ_f) = 𝔠_q(f) η(λ′_f)`; Kim–Ota gives `η(λ_f) = 𝔪^t η(λ′_f)`; cancel `η(λ′_f) ≠ 0`. -/
theorem cor_fixed (h𝒪 : IsDiscreteValuationRing 𝒪) {p q M : ℕ} (h0 : H0 p q M) (h0m : D.H0minus p q)
    (hGor : Hyp.HsiehGorFull D) (hctl : Hyp.HidaControlGL2 D p q M) (hKO : Hyp.KimOta D p q M) :
    D.cqk = IsLocalRing.maximalIdeal 𝒪 ^ D.t := by
  have := h𝒪
  have hG : CommAlg.IsGorenstein I D.R := hGor
  have hE : CommAlg.congruenceIdeal D.lamk = D.cqk * CommAlg.congruenceIdeal (A := 𝒪)
      (S := D.Rk ⧸ D.𝔞k) D.lam'k :=
    CommAlg.ThmE.eta_eq_c_mul_of_dvr (D.newOldAt h0 hctl) (CommAlg.IsGorenstein.baseChange 𝒪 hG) D.lam'k
  obtain ⟨hKO1, hne⟩ := hKO h0 h0m
  have heq : D.cqk * CommAlg.congruenceIdeal (A := 𝒪) (S := D.Rk ⧸ D.𝔞k) D.lam'k =
      IsLocalRing.maximalIdeal 𝒪 ^ D.t * CommAlg.congruenceIdeal (A := 𝒪)
          (S := D.Rk ⧸ D.𝔞k) D.lam'k :=
    hE.symm.trans hKO1
  exact le_antisymm (le_of_mul_le_mul_right_s06 hne heq.le) (le_of_mul_le_mul_right_s06 hne heq.ge)

end Langlandscape.Defect
