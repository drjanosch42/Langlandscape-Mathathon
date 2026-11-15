/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Hypothesis `ResidualBurnside`: `I_F[G] ↠ M₂(I_F)` (S06-L8a)

`mathematics/chapters/s06/s06-m4.tex`, `prop:s06-galois` step 5 and `lem:s06-burnside`: since `ρ̄_𝔪` is absolutely
irreducible ((H2)), the algebra map `I_F[G_ℚ] → M₂(I_F)` induced by `ρ_F` is surjective (Burnside modulo `𝔪`, then
Nakayama). Stated literally in the surjectivity form of `CommAlg.eq_one_of_trace_mul_eq` (`CommAlg/TraceForm.lean`) and
of the conclusion of `CommAlg.surjective_groupAlgebra_of_absIrred` (`CommAlg/Burnside.lean`) with `A = I`.

Status: *proved modulo (H2)* by `Hyp.residualBurnside_of_absIrred` (`Hyp/ResidualBurnsideDischarge.lean`).
Owner: S06-L8a (statement), S06-L6c (discharge). Consumer: `Defect.galois` (S06-L8b).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `lem:s06-burnside` (`s06-burnside`), used in `prop:s06-galois`: the algebra map `I_F[G] → M₂(I_F)` induced by
`ρ_F` is surjective. Source: tex proof of `prop:s06-galois` ((H2) + Burnside + Nakayama). Discharge: S06-L6c
(from absolute irreducibility of the residual representation, `CommAlg.surjective_groupAlgebra_of_absIrred`).
Owner: S06-L8a. -/
def ResidualBurnside (D : Defect.Setting Λ I T 𝒪 G) : Prop :=
  Function.Surjective (MonoidAlgebra.lift I (Matrix (Fin 2) (Fin 2) I) G
    ((Units.coeHom (Matrix (Fin 2) (Fin 2) I)).comp D.ρ))

end Langlandscape.Hyp
