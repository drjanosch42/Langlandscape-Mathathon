/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Group.Units.Hom

/-!
# The abstract setting of the integral Jacquet–Langlands defect (S06-L8a)

`mathematics/chapters/s06/s06-m2.tex`: `ss:s06-setting`, `hyp:s06-H`, `def:s06-rings`, `def:s06-ctam`, `def:s06-tam`;
`s06-m3.tex`: `lem:s06-control`, `thm:s06-defect`. Shape fixed by `plan/implementation/stage-06.md` §0 (rev. 2) as amended by
`plan/implementation/stage-06-launch.md` A4 (instance `[Algebra I 𝒪]` with `P := algebraMap I 𝒪`; `λ_F` given on the
`q`-new quotient `T ⧸ 𝔞Λ`) and by the chapter's audit fix R1 (M10a): `𝒪 = 𝒪̃_P` is the *normalisation* of `I_F/P` (a DVR,
`s06-m2.tex`, remark after the proof of `lem:s06-tam`), so `P : I_F → 𝒪̃_P` is local but in general **not surjective**;
the structural field is `P_local`, not `P_surj`.

`Setting` holds **data only** (plus the structural `P_local`): every mathematical input is a `Hyp.*` argument visible in the
signature of the theorems that use it. No Brandt, Hida or GL₂ Hecke API occurs: `T` is an abstract `Λ`-algebra standing for
Hida's ordinary Hecke algebra `𝐓` (GL₂ side, classical diamonds, `P_k = ker([u] ↦ u^{k-2})`), `I` for `I_F`, `𝒪` for
`𝒪̃_P` (normalisation of `I_F/P`), `G` for `G_ℚ` with the inertia subgroup `Iq` at `q`.

* `Setting.R = I ⊗[Λ] T`, the ideals `𝔞 = 𝔞Λ R`, `𝔟 = 𝔟Λ R`, `lam' : R ⧸ 𝔞 → I`, `lam = lam' ∘ (R → R ⧸ 𝔞)`;
* `Setting.cq = λ(𝔟) = 𝔠_q(F)` (`def:s06-ctam`), `Setting.tq = 𝔱_q(F)` (`def:s06-tam`);
* `Setting.isLocalHom_P`: `P` is local (the field `P_local`; used by the squeeze, step (5) of `thm:s06-defect`);
* fixed-weight data at `P` (`lem:s06-control`): `Rk = 𝒪 ⊗[I] R`, `𝔞k`, `𝔟k`, `lam'k`, `lamk`, `cqk = 𝔠_q(f)`;
* `Setting.withPoint`: the same data at another arithmetic point `P′` (`cor:s06-allweights`);
* `H0`, `Setting.H0minus`: the arithmetic guards (H0), (H0⁻) of `hyp:s06-H`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

open scoped TensorProduct

/-- `def:s06-rings`, `hyp:s06-H` (`s06-rings`): the data of the integral defect formula for `D = q`.
`T` is Hida's ordinary Hecke algebra over `Λ` (GL₂ side), `𝔞Λ = ker(𝐓 → 𝐓′)` (`q`-new quotient), `𝔟Λ = ker(𝐓 → 𝐓″)`
(`q`-old quotient), `lamΛ' : 𝐓′ → I_F` the eigensystem of the `q`-new branch `F` (so `λ_F = lamΛ' ∘ (𝐓 → 𝐓′)`: `F` is
`q`-new), `Iq ≤ G` the inertia group at `q`, `ρ = ρ_F : G → GL₂(I_F)`, `𝒪 = 𝒪̃_P` the normalisation of `I_F/P` with the
arithmetic specialisation `P = algebraMap I 𝒪 : I_F → I_F/P ⊆ 𝒪̃_P` (a local homomorphism, in general not surjective;
`thm:s06-defect` step (5), remark after `lem:s06-tam`), and `t = t_f(q)` the Tamagawa exponent of `f = F_P`. -/
structure Setting (Λ I T 𝒪 G : Type*) [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I]
    [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [Algebra I 𝒪] [Group G] where
  /-- `𝔞 = ker(𝐓 → 𝐓′)`, the kernel of the `q`-new quotient -/
  𝔞Λ : Ideal T
  /-- `𝔟 = ker(𝐓 → 𝐓″)`, the kernel of the `q`-old quotient -/
  𝔟Λ : Ideal T
  /-- `λ′_F : 𝐓′ → I_F`, the eigensystem of the `q`-new branch `F` on the new quotient -/
  lamΛ' : (T ⧸ 𝔞Λ) →ₐ[Λ] I
  /-- the inertia subgroup `I_q` -/
  Iq : Subgroup G
  /-- `ρ_F : G_ℚ → GL₂(I_F)` on `𝒯_F = H ⊗_{𝐓,λ_F} I_F` (`def:s06-tam`) -/
  ρ : G →* GL (Fin 2) I
  /-- structural: `P = algebraMap I 𝒪 : I_F → 𝒪̃_P` is a local homomorphism (integral extension of `I_F/P`) -/
  P_local : IsLocalHom (algebraMap I 𝒪)
  /-- `t = t_f(q)`, the Tamagawa exponent of `f = F_P` ([KO, Def. 2.12]) -/
  t : ℕ

/-- `hyp:s06-H` (`s06-H`), (H0): `p ≥ 5`, `p`, `q` prime, `q ≠ p`, `(M, pq) = 1`, `p ∤ φ(N)` with `N = qM` (hence
`q ≢ 1 mod p`). A decidable arithmetic guard, not a hypothesis on the data. -/
def H0 (p q M : ℕ) : Prop :=
  5 ≤ p ∧ p.Prime ∧ q.Prime ∧ q ≠ p ∧ Nat.Coprime M (p * q) ∧ ¬ p ∣ Nat.totient (q * M)

namespace Setting

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `ss:s06-setting` (`s06-setting`): the arithmetic specialisation `P : I_F → 𝒪̃_P`. -/
abbrev P (_D : Setting Λ I T 𝒪 G) : I →+* 𝒪 := algebraMap I 𝒪

/-- `def:s06-rings` (`s06-rings`): `R := 𝐓 ⊗_Λ I_F` (written `I ⊗[Λ] T`, an `I`-algebra on the left). -/
abbrev R (_D : Setting Λ I T 𝒪 G) : Type _ := I ⊗[Λ] T

/-- `def:s06-rings` (`s06-rings`): `𝔞 R`, the extension of `𝔞Λ` to `R` ("keep the names `𝔞`, `𝔟`"). -/
noncomputable def 𝔞 (D : Setting Λ I T 𝒪 G) : Ideal D.R := D.𝔞Λ.map (Algebra.TensorProduct.includeRight : T →ₐ[Λ] I ⊗[Λ] T)

/-- `def:s06-rings` (`s06-rings`): `𝔟 R`, the extension of `𝔟Λ` to `R`. -/
noncomputable def 𝔟 (D : Setting Λ I T 𝒪 G) : Ideal D.R := D.𝔟Λ.map (Algebra.TensorProduct.includeRight : T →ₐ[Λ] I ⊗[Λ] T)

/-- `def:s06-rings` (`s06-rings`): `R′ = R ⧸ 𝔞 ≅ I_F ⊗_Λ 𝐓′` (right exactness of `⊗`), as `I`-algebras. -/
noncomputable def quotient_baseChange (D : Setting Λ I T 𝒪 G) : (D.R ⧸ D.𝔞) ≃ₐ[I] I ⊗[Λ] (T ⧸ D.𝔞Λ) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := Λ) I T I D.𝔞Λ).symm

/-- `def:s06-rings` (`s06-rings`): `λ′ : R′ → I_F`, the `I_F`-linear extension of `λ′_F`. -/
noncomputable def lam' (D : Setting Λ I T 𝒪 G) : D.R ⧸ D.𝔞 →ₐ[I] I :=
  (AlgHom.liftEquiv Λ I (T ⧸ D.𝔞Λ) I D.lamΛ').comp D.quotient_baseChange.toAlgHom

/-- `def:s06-rings` (`s06-rings`): `λ = λ′ ∘ (R → R′) : R → I_F`; by construction `λ` factors through the `q`-new
quotient (`F` is `q`-new), and `λ = ThmE.lam _ D.lam'` definitionally. -/
noncomputable def lam (D : Setting Λ I T 𝒪 G) : D.R →ₐ[I] I := D.lam'.comp (Ideal.Quotient.mkₐ I D.𝔞)

/-- `def:s06-ctam` (`s06-ctam`): the combinatorial Tamagawa ideal `𝔠_q(F) = λ(𝔟) ⊆ I_F`. -/
noncomputable def cq (D : Setting Λ I T 𝒪 G) : Ideal I := D.𝔟.map D.lam

/-- `def:s06-tam` (`s06-tam`): the Tamagawa ideal `𝔱_q(F) ⊆ I_F`, generated by the entries of `ρ_F(σ) - 1`, `σ ∈ I_q`. -/
noncomputable def tq (D : Setting Λ I T 𝒪 G) : Ideal I :=
  Ideal.span {x | ∃ σ ∈ D.Iq, ∃ i j : Fin 2, ((D.ρ σ : Matrix (Fin 2) (Fin 2) I) - 1) i j = x}

/-- `hyp:s06-H` (`s06-H`), (H0⁻): `q ≢ -1 mod p`, or `ρ̄_𝔪` is ramified at `q`. The second alternative is stated as
`𝔱_q(F) = I_F` (some entry of `ρ_F(σ) - 1`, `σ ∈ I_q`, is a unit, i.e. `ρ̄|_{I_q} ≠ 1`). -/
def H0minus (D : Setting Λ I T 𝒪 G) (p q : ℕ) : Prop := ¬ p ∣ q + 1 ∨ D.tq = ⊤

/-- `thm:s06-defect` (`s06-defect`), step (5): the specialisation `P : I_F → 𝒪̃_P` is a local homomorphism (the
structural field `P_local`; `I_F/P ⊆ 𝒪̃_P` is integral). Without locality the squeeze is false (`ℤ_(p) → ℚ`). Use
`haveI := D.isLocalHom_P` before `CommAlg.squeeze`. -/
theorem isLocalHom_P (D : Setting Λ I T 𝒪 G) : IsLocalHom D.P :=
  D.P_local

/-! ### Fixed-weight data at `P` (`lem:s06-control`) -/

/-- `lem:s06-control` (`s06-control`): the fixed-weight algebra `R ⊗_{I_F,P} 𝒪̃_P = 𝒪 ⊗[I] R`; by control
(`Hyp.HidaControlGL2`) it is `𝐓_k(N)_𝔪 ⊗_𝒪 𝒪̃_P`. -/
abbrev Rk (D : Setting Λ I T 𝒪 G) : Type _ := 𝒪 ⊗[I] D.R

/-- `lem:s06-control` (`s06-control`): `𝔞_k`, the extension of `𝔞` to `𝒪 ⊗[I] R`. -/
noncomputable def 𝔞k (D : Setting Λ I T 𝒪 G) : Ideal D.Rk := D.𝔞.map (Algebra.TensorProduct.includeRight : D.R →ₐ[I] 𝒪 ⊗[I] D.R)

/-- `lem:s06-control` (`s06-control`): `𝔟_k`, the extension of `𝔟` to `𝒪 ⊗[I] R`. -/
noncomputable def 𝔟k (D : Setting Λ I T 𝒪 G) : Ideal D.Rk := D.𝔟.map (Algebra.TensorProduct.includeRight : D.R →ₐ[I] 𝒪 ⊗[I] D.R)

/-- `lem:s06-control` (`s06-control`): `λ′_f : 𝒪 ⊗[I] R ⧸ 𝔞_k → 𝒪`, the base change of `λ′` along `P`
(through `𝒪 ⊗[I] (R ⧸ 𝔞) ≅ (𝒪 ⊗[I] R) ⧸ 𝔞_k`). -/
noncomputable def lam'k (D : Setting Λ I T 𝒪 G) : D.Rk ⧸ D.𝔞k →ₐ[𝒪] 𝒪 :=
  (AlgHom.liftEquiv I 𝒪 (D.R ⧸ D.𝔞) 𝒪 ((Algebra.ofId I 𝒪).comp D.lam')).comp
    (Algebra.TensorProduct.tensorQuotientEquiv (R := I) 𝒪 D.R 𝒪 D.𝔞).symm.toAlgHom

/-- `lem:s06-control` (`s06-control`): `λ_f = λ′_f ∘ (R_k → R_k ⧸ 𝔞_k)`, the base change of `λ` along `P`. -/
noncomputable def lamk (D : Setting Λ I T 𝒪 G) : D.Rk →ₐ[𝒪] 𝒪 := D.lam'k.comp (Ideal.Quotient.mkₐ 𝒪 D.𝔞k)

/-- `def:s06-ctam` (`s06-ctam`), fixed weight: `𝔠_q(f) = λ_f(𝔟_k) ⊆ 𝒪̃_P`. -/
noncomputable def cqk (D : Setting Λ I T 𝒪 G) : Ideal 𝒪 := D.𝔟k.map D.lamk

/-- `cor:s06-allweights` (`s06-allweights`): the same data `𝔞Λ, 𝔟Λ, λ′_F, I_q, ρ_F` at another arithmetic point
`P′ = algebraMap I 𝒪′` (local, `𝒪′ = 𝒪̃_{P′}`) with Tamagawa exponent `t′ = t_{f′}(q)`. -/
def withPoint (D : Setting Λ I T 𝒪 G) (𝒪' : Type*) [CommRing 𝒪'] [IsDomain 𝒪'] [IsLocalRing 𝒪'] [Algebra I 𝒪']
    (hP' : IsLocalHom (algebraMap I 𝒪')) (t' : ℕ) : Setting Λ I T 𝒪' G where
  𝔞Λ := D.𝔞Λ
  𝔟Λ := D.𝔟Λ
  lamΛ' := D.lamΛ'
  Iq := D.Iq
  ρ := D.ρ
  P_local := hP'
  t := t'

/-- `cor:s06-allweights` (`s06-allweights`): moving the point does not change `𝔠_q(F)`. -/
theorem withPoint_cq (D : Setting Λ I T 𝒪 G) (𝒪' : Type*) [CommRing 𝒪'] [IsDomain 𝒪'] [IsLocalRing 𝒪'] [Algebra I 𝒪']
    (hP' : IsLocalHom (algebraMap I 𝒪')) (t' : ℕ) : (D.withPoint 𝒪' hP' t').cq = D.cq := rfl

/-- `cor:s06-allweights` (`s06-allweights`): moving the point does not change `𝔱_q(F)`. -/
theorem withPoint_tq (D : Setting Λ I T 𝒪 G) (𝒪' : Type*) [CommRing 𝒪'] [IsDomain 𝒪'] [IsLocalRing 𝒪'] [Algebra I 𝒪']
    (hP' : IsLocalHom (algebraMap I 𝒪')) (t' : ℕ) : (D.withPoint 𝒪' hP' t').tq = D.tq := rfl

end Setting

end Langlandscape.Defect
