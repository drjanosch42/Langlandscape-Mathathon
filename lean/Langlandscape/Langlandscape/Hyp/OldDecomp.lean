/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.Defect.Setting

/-!
# Hypothesis `OldDecomp`: the old/new decomposition over `I_F` (S06-L8a)

`mathematics/chapters/s06/s06-m2.tex`, `lem:s06-decomp` (a)–(c) (corrected: `𝐓″ ≅ 𝐓(M)_𝔪` is `Λ`-free), read through
(c): `(R, 𝔞, 𝔟)` satisfies the hypotheses of `lem:s06-D` over `A = I_F`, and `R″ = R ⧸ 𝔟` is `I_F`-free.

Source: Hida, *Iwasawa modules attached to congruences of cusp forms*, Ann. Sci. ÉNS 19 (1986) [Hi86b], Thm 3.1 and
Cor. 3.2, p. 250 (freeness, control); Hensel factorisation of `X² - T_q X + qS_q` over `𝐓(M)_𝔪`; local–global
compatibility at `q` (Carayol, Th. (A); DDT Thm 3.1). Status: *proved modulo cited* in the chapter (M2), not formalized.
Owner: S06-L8a. Consumers: `Defect.Setting.newOld`, `Defect.defect_formula` (S06-L9a).

The statement is the plain conjunction of the `NewOldData` fields for `D.𝔞`, `D.𝔟` plus `Module.Free I (D.R ⧸ D.𝔟)`
(launch note A4.3), so that `Setting.newOld` has `𝔞 = D.𝔞`, `𝔟 = D.𝔟` definitionally (no quotient casts).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape

open scoped TensorProduct

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

namespace Hyp

/-- `lem:s06-decomp` (`s06-decomp`), (a)–(c) over `A = I_F`: `R = I_F ⊗_Λ 𝐓` is finite free over `I_F`; `R ⧸ 𝔞` and
`R ⧸ 𝔟` are `I_F`-torsion-free; `𝔞 ∩ 𝔟 = 0`; some `c ≠ 0` of `I_F` lies in `𝔞 + 𝔟` (the field-free form of
`R_K = R′_K × R″_K`, `CommAlg.NewOldData.split_iff`); and `R″ = R ⧸ 𝔟 ≅ 𝐓(M)_𝔪 ⊗_Λ I_F` is `I_F`-free.
Source: [Hi86b, Thm 3.1, Cor. 3.2, p. 250] + Hensel + local–global compatibility at `q` (chapter M2).
Discharge: *maths only* (proved modulo cited in `lem:s06-decomp`), not formalized. Owner: S06-L8a. -/
def OldDecomp (D : Defect.Setting Λ I T 𝒪 G) : Prop :=
  Module.Free I D.R ∧ Module.Finite I D.R ∧ Module.IsTorsionFree I (D.R ⧸ D.𝔞) ∧
    Module.IsTorsionFree I (D.R ⧸ D.𝔟) ∧ D.𝔞 ⊓ D.𝔟 = ⊥ ∧
    (∃ c : I, c ≠ 0 ∧ algebraMap I D.R c ∈ D.𝔞 ⊔ D.𝔟) ∧ Module.Free I (D.R ⧸ D.𝔟)

end Hyp

namespace Defect.Setting

/-- `lem:s06-decomp` (`s06-decomp`)(c): the new/old data `(R, 𝔞, 𝔟)` over `I_F` given by `Hyp.OldDecomp`; its ideals
are `D.𝔞`, `D.𝔟` definitionally. -/
noncomputable def newOld (D : Defect.Setting Λ I T 𝒪 G) (h : Hyp.OldDecomp D) : CommAlg.NewOldData I D.R where
  𝔞 := D.𝔞
  𝔟 := D.𝔟
  free := h.1
  finite := h.2.1
  tf_a := h.2.2.1
  tf_b := h.2.2.2.1
  inf_eq_bot := h.2.2.2.2.1
  split := h.2.2.2.2.2.1

/-- `lem:s06-decomp` (`s06-decomp`): the new kernel of `Setting.newOld` is `D.𝔞`. -/
@[simp]
theorem newOld_𝔞 (D : Defect.Setting Λ I T 𝒪 G) (h : Hyp.OldDecomp D) : (D.newOld h).𝔞 = D.𝔞 := rfl

/-- `lem:s06-decomp` (`s06-decomp`): the old kernel of `Setting.newOld` is `D.𝔟`. -/
@[simp]
theorem newOld_𝔟 (D : Defect.Setting Λ I T 𝒪 G) (h : Hyp.OldDecomp D) : (D.newOld h).𝔟 = D.𝔟 := rfl

/-- `lem:s06-decomp` (`s06-decomp`)(c): the old quotient `R″ = R ⧸ 𝔟` is `I_F`-free (the hypothesis `hb` of
`lem:s06-D`(c)). -/
theorem free_quot_b (D : Defect.Setting Λ I T 𝒪 G) (h : Hyp.OldDecomp D) :
    Module.Free I (D.R ⧸ (D.newOld h).𝔟) :=
  h.2.2.2.2.2.2

end Defect.Setting

end Langlandscape
