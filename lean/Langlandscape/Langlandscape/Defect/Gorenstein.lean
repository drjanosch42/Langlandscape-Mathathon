/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Langlandscape.Hyp.LambdaJL
public import Langlandscape.Hyp.HsiehGor
import Langlandscape.CommAlg.BaseChange

/-!
# (Gor_{R′}) for the `q`-new quotient (S06-L8c)

`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-defect` step (1): the `q`-new quotient `R′ = R ⧸ 𝔞` is
`I_F`-Gorenstein. Route (`s06-m1.tex`, `lem:s06-S`, base-change part):

* `Hyp.LambdaJL` (instantiated with `TGL := T`, `newIdeal := 𝔞Λ`) gives a surjection `φ : T → TB` of `Λ`-algebras with
  kernel `𝔞Λ`, hence `T ⧸ 𝔞Λ ≃ₐ[Λ] TB` (first isomorphism theorem);
* `Hyp.HsiehGor Λ TB M` gives `IsGorenstein Λ TB`, transported to `IsGorenstein Λ (T ⧸ 𝔞Λ)`;
* `CommAlg.IsGorenstein.baseChange` gives `IsGorenstein I (I ⊗[Λ] (T ⧸ 𝔞Λ))`, and `Setting.quotient_baseChange`
  identifies this with `R ⧸ 𝔞`.

Only the surjectivity and the kernel clause of `Hyp.LambdaJL` are used (not the generator matching), and only the first
component of `Hyp.HsiehGor` (not `M ≅ TB`). Both hypotheses are explicit arguments.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

namespace Setting

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]
  (D : Setting Λ I T 𝒪 G)

/-- `thm:s06-defect` (`s06-defect`), step (1), (Gor_{R′}): the `q`-new quotient `R′ = R ⧸ 𝔞 ≅ I_F ⊗_Λ 𝐓′` is
`I_F`-Gorenstein. From (Gor) of the definite ordinary Hecke algebra `TB` over `Λ` (`Hyp.HsiehGor`, Hsieh Thm 4.5), the
`Λ`-adic Jacquet–Langlands surjection `𝐓 → TB` with kernel `𝔞Λ` (`Hyp.LambdaJL`, `thm:s01-lambdaJL`; schematic, see its
caveat), and base change of Gorenstein algebras (`lem:s06-S`, `CommAlg.IsGorenstein.baseChange`).
Seam with `thm:s04-Gor`: that theorem is over `𝕀 = I_F` (see `gor_new_of_I`, the literal entry point); the instantiation
`A := Λ` used here is the `Λ`-form (Hsieh's theorem for the `Λ`-algebra, or descent along `Λ → 𝕀`; not formalized). The
`[Algebra Λ TB]` structure is the one for which `φ` is `Λ`-linear, i.e. the definite side's adelic structure composed
with `[u] ↦ [u]⁻¹` (chapter step (1)); the Gorenstein property does not depend on this twist. -/
theorem gor_new {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M] [Module TB M]
    (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB)
    (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ) (hGor' : Hyp.HsiehGor Λ TB M) :
    CommAlg.IsGorenstein I (D.R ⧸ D.𝔞) := by
  obtain ⟨φ, ⟨hsurj, -⟩, hker⟩ := hJL
  obtain ⟨hTB, -⟩ := hGor'
  have hker' : RingHom.ker φ = D.𝔞Λ := hker
  let e : (T ⧸ D.𝔞Λ) ≃ₐ[Λ] TB :=
    (Ideal.quotientEquivAlgOfEq Λ hker'.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hΛ : CommAlg.IsGorenstein Λ (T ⧸ D.𝔞Λ) := CommAlg.IsGorenstein.of_algEquiv hTB e.symm
  exact CommAlg.IsGorenstein.of_algEquiv (CommAlg.IsGorenstein.baseChange I hΛ) D.quotient_baseChange.symm

/-- `thm:s06-defect` (`s06-defect`), step (1), (Gor_{R′}), `𝕀`-form: `thm:s04-Gor` is stated over `𝕀 = I_F`, so with
`A := I_F` and `TB := R ⧸ 𝔞 ≅ 𝐓^D(N, χ, 𝕀)_{𝔪_F}` it gives (Gor_{R′}) directly (feeds `defect_formula_of_le`). The
`Λ`-form `gor_new` additionally needs descent along `Λ → 𝕀` (not formalized). -/
theorem gor_new_of_I {M : Type*} [AddCommGroup M] [Module (D.R ⧸ D.𝔞) M]
    (h : Hyp.HsiehGor I (D.R ⧸ D.𝔞) M) : CommAlg.IsGorenstein I (D.R ⧸ D.𝔞) :=
  h.1

end Setting

end Langlandscape.Defect
