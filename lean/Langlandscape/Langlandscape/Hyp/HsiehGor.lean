/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein

/-!
# Hypothesis `HsiehGor`: (Gor_{R′}) on the definite side (S06-L8a)

`mathematics/chapters/s04/hsieh.tex`, `thm:s04-Gor` (`if:s04-Mord`, second half); used in
`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-defect` step (1) ((Gor_{R′})), and `s06-m1.tex`, `rem:s06-gor-uses`.
Fixed signature (`plan/implementation/stage-06.md` §0, rev. 2; stage 04 quotes it verbatim).

Source: Hsieh, *Hida families and p-adic triple product L-functions* (2017), Thm 4.5 and its proof, p. 34, under
(CR, Σ) (§1.4, p. 4); the identification of `T^D` with the `N⁻`-new quotient is Rem. 7.8, p. 71.
Status: *cited*, not discharged (post-hackathon). Owner of the statement: S06-L8a; consumer: `Defect.Setting.gor_new`
(S06-L8c) → `Defect.defect_formula` (S06-L9a). A hypothesis is a `Prop`-valued definition taken as an explicit argument
(never an axiom, never an instance; OVERVIEW §3.6), registered in `HYPOTHESES.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- `thm:s04-Gor` (`s04-Gor`): Hsieh Thm 4.5 + proof. Cited, not discharged. `thm:s04-Gor` is over `𝕀`: instantiate
`A := I_F`, `TB := 𝐓^D(N, χ, 𝕀)_{𝔪_F} ≅ R ⧸ 𝔞` (`Defect.Setting.gor_new_of_I`). The instantiation `A := Λ`,
`TB :=` the definite ordinary Hecke algebra `T ⧸ 𝔞Λ` (via `Hyp.LambdaJL`), `M := M^ord_𝔪`, used by
`Defect.Setting.gor_new`, is the `Λ`-form (Hsieh's theorem for the `Λ`-algebra, or descent along `Λ → 𝕀`; not
formalized), under `p ∤ φ(M)` ((H0)) for the full algebra. -/
def HsiehGor (A TB M : Type*) [CommRing A] [CommRing TB] [Algebra A TB]
    [AddCommGroup M] [Module TB M] : Prop :=
  CommAlg.IsGorenstein A TB ∧ Nonempty (M ≃ₗ[TB] TB)

end Langlandscape.Hyp
