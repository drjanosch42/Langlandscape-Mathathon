/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Hyp.ResidualBurnside
public import Langlandscape.CommAlg.Burnside
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Discharge of `Hyp.ResidualBurnside` from absolute irreducibility (S06-L8b / L6c)

`mathematics/chapters/s06/s06-m4.tex`, `lem:s06-burnside`: `Hyp.ResidualBurnside D` is exactly the conclusion of
`CommAlg.surjective_groupAlgebra_of_absIrred` for `A = I`, `ρ = D.ρ`. Status: *proved* modulo (H2) (the irreducibility
hypothesis `hirr`).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- `lem:s06-burnside` (`s06-burnside`): if `ρ̄ ⊗ K` is irreducible for a local homomorphism `f : I_F → K` into an
algebraically closed field, then `Hyp.ResidualBurnside D` holds. -/
theorem residualBurnside_of_absIrred {Λ I T 𝒪 G K : Type*} [CommRing Λ] [CommRing I] [IsDomain I]
    [IsNoetherianRing I] [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪]
    [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G] [Field K] [IsAlgClosed K]
    (D : Defect.Setting Λ I T 𝒪 G) (f : I →+* K) [IsLocalHom f]
    (hirr : (CommAlg.residualRep f D.ρ).IsIrreducible) : ResidualBurnside D :=
  CommAlg.surjective_groupAlgebra_of_absIrred f D.ρ hirr

end Langlandscape.Hyp
