/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.QuotientCore

/-!
# Tests for S02 QuotientCore — S02-L5b

Tex labels: prop:s02-BG. Shape checks for a variable `DefiniteData`, prime `q ∤ D` and `q`-level `U`.
-/

set_option autoImplicit false

namespace LanglandscapeTests.S02.QuotientCore

open Langlandscape Langlandscape.Quat Langlandscape.Tree

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG` (`s02-BG`): the base vertex `Γ_U v₀` maps to `([1], 0)`. -/
theorem phiV_v0 (hU : IsQLevel d q hq U) :
    phiV d q hq U (Quotient.mk'' (v0 q)) =
      Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((1 : SLq q) : GL (Fin 2) ℚ_[q]))) := by
  have h := phiV_type0 hU (1 : SLq q)
  rwa [one_smul] at h

/-- `prop:s02-BG` (`s02-BG`): the base edge `Γ_U e₀` has ends `([1], 0)` and `([α], 1)` (Step 3). -/
theorem phiV_e0_ends (hU : IsQLevel d q hq U) :
    phiV d q hq U (Quotient.mk'' (oO q (e0 q))) =
        Sum.inl (s0 d q hq U (phiE d q hq U (Quotient.mk'' (e0 q)))) ∧
      phiV d q hq U (Quotient.mk'' (tO q (e0 q))) =
        Sum.inr (s1 d q hq U (phiE d q hq U (Quotient.mk'' (e0 q)))) :=
  ⟨phiV_oO hU (e0 q), phiV_tO hU (e0 q)⟩

/-- `prop:s02-BG` (`s02-BG`): (iii) ⇒ bijections, with no `Hyp.*` argument. -/
theorem bij_of_conn (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    Function.Bijective (phiV d q hq U) ∧ Function.Bijective (phiE d q hq U) :=
  bijective_of_BGConnected hU hc

/-- `prop:s02-BG` (`s02-BG`): (iii) ⇒ (i) ⇒ (ii), tree-free. -/
theorem SA_of_conn (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    SAat d q hq U ∧ Function.Surjective (XBone.toXB d U) :=
  SA_of_surj hU (surjType0_of_BGConnected hU hc)

/-- `prop:s02-BG` (`s02-BG`): (i) ⇔ (iii) given the tree hypothesis. -/
theorem conn_iff_surj (hBT : Hyp.BTtree q) (hU : IsQLevel d q hq U) :
    BGConnected d q hq U hU ↔ surjType0 d q hq U :=
  ⟨surjType0_of_BGConnected hU, BGConnected_of_surj hBT hU⟩

/-- `prop:s02-BG` (`s02-BG`): the export shape used by S03-L9. -/
theorem conn_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hBT : Hyp.BTtree q)
    (hU : IsQAdmissible d q hq U) : BGConnected d q hq U hU.1 :=
  BGConnected_of_SA_HS hSA hHS hBT hU

end LanglandscapeTests.S02.QuotientCore
