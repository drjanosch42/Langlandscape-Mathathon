/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Quotient

/-!
# Tests for S02 Quotient — S02-L6

Tex labels: prop:s02-quot, prop:s02-free. Instances at the maximal level `Ô^×` for a split prime `q ∤ D`.
-/

set_option autoImplicit false

namespace LanglandscapeTests.S02.Quotient

open Langlandscape.Quat Langlandscape.Tree

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ}(v₀) = Γ_1(Ô^×)` (unconditional). -/
theorem stab_v0_Ohat :
    (MulAction.stabilizer (GammaU d q hq d.Ohat) ((1 : SLq q) • v0 q)).map (GammaU d q hq d.Ohat).subtype =
      Gam d.Ohat (localEmbedGL d q hq ((1 : SLq q) : GL (Fin 2) ℚ_[q])) :=
  stab_gv0_eq_Gam (isQLevel_Ohat (hq := hq)) 1

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ}(v₁) = Γ_α(Ô^×)`. -/
theorem stab_v1_Ohat :
    (MulAction.stabilizer (GammaU d q hq d.Ohat) ((1 : SLq q) • v1 q)).map (GammaU d q hq d.Ohat).subtype =
      Gam d.Ohat (localEmbedGL d q hq (((1 : SLq q) : GL (Fin 2) ℚ_[q]) * alphaq q)) :=
  stab_gav0_eq_Gam (isQLevel_Ohat (hq := hq)) 1

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ}(e₀) = Γ_1(U_0(q)Ô^×)`. -/
theorem stab_e0_Ohat :
    (MulAction.stabilizer (GammaU d q hq d.Ohat) ((1 : SLq q) • e0 q)).map (GammaU d q hq d.Ohat).subtype =
      Gam (d.U0q q (coprime_of_not_dvd hq) d.Ohat) (localEmbedGL d q hq ((1 : SLq q) : GL (Fin 2) ℚ_[q])) :=
  stab_ge0_eq_Gam (isQLevel_Ohat (hq := hq)) 1

/-- `prop:s02-quot`(a) (`s02-quot`): under (iii) at `Ô^×`, the class of `v₀` goes to `inl [1]`. -/
theorem quotVEquiv_v0_Ohat (hc : BGConnected d q hq d.Ohat (isQLevel_Ohat (hq := hq))) :
    quotVEquiv (isQLevel_Ohat (hq := hq)) hc (Quotient.mk'' ((1 : SLq q) • v0 q)) =
      Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat
        (localEmbedGL d q hq ((1 : SLq q) : GL (Fin 2) ℚ_[q]))) :=
  phiV_type0 (isQLevel_Ohat (hq := hq)) 1

/-- `prop:s02-quot`(a) (`s02-quot`): under (iii) at `Ô^×`, origins of edges become `s₀`. -/
theorem quotEquiv_oO_Ohat (hc : BGConnected d q hq d.Ohat (isQLevel_Ohat (hq := hq))) (e : EdgeO q) :
    quotVEquiv (isQLevel_Ohat (hq := hq)) hc (Quotient.mk'' (oO q e)) =
      Sum.inl (s0 d q hq d.Ohat (quotEEquiv (isQLevel_Ohat (hq := hq)) hc (Quotient.mk'' e))) :=
  quotEquiv_oO (isQLevel_Ohat (hq := hq)) hc e

/-- `prop:s02-free`(b) (`s02-free`): at a free `q`-level, `|X_B(U_0(q)U)| = (q + 1) |X_B(U)|`. -/
theorem card_free {U : Subgroup (BHat d.a d.b)ˣ} (hU : IsQLevel d q hq U) (hfree : ∀ x, Gam U x = ⊥) :
    Nat.card (XB (d.U0q q (coprime_of_not_dvd hq) U)) = (q + 1) * Nat.card (XB U) :=
  card_XB_U0q_of_free hU hfree

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ}(g e₀) = Γ_g(U')` at a variable `g ∈ SL₂(ℚ_q)` and `q`-level `U`. -/
theorem stab_ge0_var {U : Subgroup (BHat d.a d.b)ˣ} (hU : IsQLevel d q hq U) (g : SLq q) :
    (MulAction.stabilizer (GammaU d q hq U) (g • e0 q)).map (GammaU d q hq U).subtype =
      Gam (d.U0q q (coprime_of_not_dvd hq) U) (localEmbedGL d q hq (g : GL (Fin 2) ℚ_[q])) :=
  stab_ge0_eq_Gam hU g

/-- `prop:s02-quot`(a) (`s02-quot`): the vertex equivalence from strong approximation and Hasse--Schilling at a
variable `q`-admissible level (the hypotheses `hSA`, `hHS` are explicit arguments). -/
noncomputable def quotV_test {U : Subgroup (BHat d.a d.b)ˣ} (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hU : IsQAdmissible d q hq U) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q) ≃ XB U ⊕ XB U :=
  quotVEquiv_of_SA_HS hSA hHS hU

/-- `prop:s02-quot`(a) (`s02-quot`): the edge equivalence from strong approximation and Hasse--Schilling at a
variable `q`-admissible level. -/
noncomputable def quotE_test {U : Subgroup (BHat d.a d.b)ˣ} (hSA : Langlandscape.Hyp.SA d q hq)
    (hHS : Langlandscape.Hyp.HS d) (hU : IsQAdmissible d q hq U) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q) ≃ XB (d.U0q q (coprime_of_not_dvd hq) U) :=
  quotEEquiv_of_SA_HS hSA hHS hU

end LanglandscapeTests.S02.Quotient
