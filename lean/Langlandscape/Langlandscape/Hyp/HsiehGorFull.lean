/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.Defect.Setting

/-!
# Hypothesis `HsiehGorFull`: (Gor_R) (S06-L8a)

`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-defect` step (1); `s06-m1.tex`, `thm:s06-E` ((Gor_S) with `S = R`),
`rem:s06-gor-uses`. The full algebra `R = I_F ⊗_Λ 𝐓` is `I_F`-Gorenstein. Stated over `I` (stage-06 plan §0 table); the
chapter derives it from (Gor_𝐓) over `Λ` by Lemma S (base change), which is the form of the source.

Source: Hsieh (2017) §3.3, p. 17–18, and §7.2, p. 68, under (CR) (implied by (H0), (H2): `rem:s06-CR`), resting on
Wiles (1995) Thm 2.1 / Cor. 2, p. 482, Mazur–Wiles (1986) §9 Prop. 2, Helm (2004) Cor. 8.11, p. 31.
Status: *cited*, not discharged. Owner: S06-L8a. Consumers: `Defect.defect_formula` (S06-L9a), `Defect.cor_fixed`,
`Defect.cor_allweights` (S06-L9b; fixed-weight Gorenstein derived by `CommAlg.IsGorenstein.baseChange` along `P`).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `thm:s06-defect` (`s06-defect`), step (1), (Gor_R): `R = I_F ⊗_Λ 𝐓` is finite free and `I_F`-Gorenstein.
Source: [Hs, §3.3, p. 17–18; §7.2, p. 68] (with [Wi95, Cor. 2, p. 482], [MW86, §9 Prop. 2], [Hel, Cor. 8.11, p. 31]),
under (CR,{q}) (`rem:s06-CR`). Discharge: *cited*. Owner: S06-L8a. Kept separate from (Gor_{R′}) (`Hyp.HsiehGor`). -/
def HsiehGorFull (D : Defect.Setting Λ I T 𝒪 G) : Prop :=
  CommAlg.IsGorenstein I D.R

end Langlandscape.Hyp
