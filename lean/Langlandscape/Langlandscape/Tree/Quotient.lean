/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.QuotientCore

/-!
# Quotient graph and stabilisers — S02-L6

`plan/staged/stage-02-tree-quotients.tex` and `mathematics/chapters/s02/2-quotient.tex`: `prop:s02-quot`(a),(b);
`mathematics/chapters/s02/3-cohomology.tex`: `prop:s02-free`(b) (the count).

Fix a prime `q ∤ D` and a `q`-level `U` (`IsQLevel d q hq U`), `U' = U_0(q)U`.

* (a) packaged as equivalences: `quotVEquiv : Γ_U \ V(𝒯_q) ≃ X_B(U) ⊕ X_B(U)` and
  `quotEEquiv : Γ_U \ E(𝒯_q) ≃ X_B(U')` under (iii) of `prop:s02-BG` (`BGConnected`), with the endpoint maps
  becoming `s₀`, `s₁` (`quotEquiv_oO`, `quotEquiv_tO`); the same equivalences from `Hyp.SA ∧ Hyp.HS` at a
  `q`-admissible level (`quotVEquiv_of_SA_HS`, `quotEEquiv_of_SA_HS`; via (ii) ⇒ (i) ⇒ bijections, **no
  `Hyp.BTtree`**). All are `Equiv.ofBijective` of S02-L5b's `phiV`, `phiE`.
* (b) `Stab_{Γ_U}(g v₀) = Γ_g(U)`, `Stab_{Γ_U}(g α v₀) = Γ_{gα}(U)`, `Stab_{Γ_U}(g e₀) = Γ_g(U')` for every
  `g ∈ SL₂(ℚ_q)` (`stab_gv0_eq_Gam`, `stab_gav0_eq_Gam`, `stab_ge0_eq_Gam`; unconditional, as in the chapter's
  refinement). Note `g α v₀ = g v₁` in the coset model.
* `prop:s02-free`(b), count: if all `Γ_x(U)` are trivial, `|X_B(U')| = (q + 1) |X_B(U)|`
  (`card_XB_U0q_of_free`; from the mass formula `mass_orbit_count` with `[U : U'] = q + 1`, no tree input).

Status: *formalized* (modulo `Hyp.SA`, `Hyp.HS` in the `…_of_SA_HS` versions).
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local
open GL2TF.Quat (nrd)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-! ### (a): the quotient graph -/

section Equiv

/-- `prop:s02-quot`(a): under (iii) (`BG(U,q)` connected), `Γ_U \ V(𝒯_q) ≃ X_B(U) ⊕ X_B(U)`,
`Γ_U s v₀ ↦ inl [s]`, `Γ_U s v₁ ↦ inr [s α]` (the map `phiV` of `prop:s02-BG`). -/
noncomputable def quotVEquiv (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q) ≃ XB U ⊕ XB U :=
  Equiv.ofBijective (phiV d q hq U) (bijective_of_BGConnected hU hc).1

/-- `prop:s02-quot`(a): under (iii), `Γ_U \ E(𝒯_q) ≃ X_B(U_0(q)U)`, `Γ_U s e₀ ↦ [s]` (the map `phiE`). -/
noncomputable def quotEEquiv (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q) ≃ XB (d.U0q q (coprime_of_not_dvd hq) U) :=
  Equiv.ofBijective (phiE d q hq U) (bijective_of_BGConnected hU hc).2

/-- `prop:s02-quot`(a) (`s02-quot`): `quotVEquiv` is `phiV`. -/
theorem quotVEquiv_apply (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU)
    (o : MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q)) :
    quotVEquiv hU hc o = phiV d q hq U o :=
  rfl

/-- `prop:s02-quot`(a) (`s02-quot`): `quotEEquiv` is `phiE`. -/
theorem quotEEquiv_apply (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU)
    (o : MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q)) :
    quotEEquiv hU hc o = phiE d q hq U o :=
  rfl

/-- `prop:s02-quot`(a) (`s02-quot`): under the equivalences the origin map `o` becomes `s₀`:
`quotVEquiv (Γ_U o(e)) = inl (s₀ (quotEEquiv (Γ_U e)))`. -/
theorem quotEquiv_oO (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) (e : EdgeO q) :
    quotVEquiv hU hc (Quotient.mk'' (oO q e)) =
      Sum.inl (s0 d q hq U (quotEEquiv hU hc (Quotient.mk'' e))) :=
  phiV_oO hU e

/-- `prop:s02-quot`(a) (`s02-quot`): under the equivalences the terminus map `t` becomes `s₁`:
`quotVEquiv (Γ_U t(e)) = inr (s₁ (quotEEquiv (Γ_U e)))`. -/
theorem quotEquiv_tO (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) (e : EdgeO q) :
    quotVEquiv hU hc (Quotient.mk'' (tO q e)) =
      Sum.inr (s1 d q hq U (quotEEquiv hU hc (Quotient.mk'' e))) :=
  phiV_tO hU e

/-- `prop:s02-quot`(a), `prop:s02-BG` (ii) ⇒ (i) (`s02-quot`): `Hyp.SA` and `Hyp.HS` give (i) at every
`q`-admissible level (no tree input). -/
theorem surjType0_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hU : IsQAdmissible d q hq U) :
    surjType0 d q hq U :=
  surj_of_SA hU.1 (hSA U hU) (XBone_toXB_bijective hHS hU.2 hU.1.1).2

/-- `prop:s02-quot`(a): `Γ_U \ V(𝒯_q) ≃ X_B(U) ⊕ X_B(U)` from strong approximation and Hasse–Schilling at a
`q`-admissible level, via (ii) ⇒ (i) ⇒ bijections (`bijective_of_surjType0`); **no `Hyp.BTtree`**. -/
noncomputable def quotVEquiv_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hU : IsQAdmissible d q hq U) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q) ≃ XB U ⊕ XB U :=
  Equiv.ofBijective (phiV d q hq U) (bijective_of_surjType0 hU.1 (surjType0_of_SA_HS hSA hHS hU)).1

/-- `prop:s02-quot`(a): `Γ_U \ E(𝒯_q) ≃ X_B(U_0(q)U)` from strong approximation and Hasse–Schilling at a
`q`-admissible level; **no `Hyp.BTtree`**. -/
noncomputable def quotEEquiv_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hU : IsQAdmissible d q hq U) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q) ≃ XB (d.U0q q (coprime_of_not_dvd hq) U) :=
  Equiv.ofBijective (phiE d q hq U) (bijective_of_surjType0 hU.1 (surjType0_of_SA_HS hSA hHS hU)).2

/-- `prop:s02-quot`(a) (`s02-quot`): the origin map becomes `s₀` for the `…_of_SA_HS` equivalences. -/
theorem quotEquiv_oO_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hU : IsQAdmissible d q hq U)
    (e : EdgeO q) :
    quotVEquiv_of_SA_HS hSA hHS hU (Quotient.mk'' (oO q e)) =
      Sum.inl (s0 d q hq U (quotEEquiv_of_SA_HS hSA hHS hU (Quotient.mk'' e))) :=
  phiV_oO hU.1 e

/-- `prop:s02-quot`(a) (`s02-quot`): the terminus map becomes `s₁` for the `…_of_SA_HS` equivalences. -/
theorem quotEquiv_tO_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hU : IsQAdmissible d q hq U)
    (e : EdgeO q) :
    quotVEquiv_of_SA_HS hSA hHS hU (Quotient.mk'' (tO q e)) =
      Sum.inr (s1 d q hq U (quotEEquiv_of_SA_HS hSA hHS hU (Quotient.mk'' e))) :=
  phiV_tO hU.1 e

end Equiv

/-! ### (b): stabilisers -/

section Stab

/-- `prop:s02-quot`(b) (`s02-quot`): `(ι_q^{-1} h)⁻¹ y (ι_q^{-1} h)` has `q`-component `h⁻¹ y_q h`. -/
private theorem localComponent_invConj (h : GL (Fin 2) ℚ_[q]) (y : (BHat d.a d.b)ˣ) :
    localComponent d q hq ((localEmbedGL d q hq h)⁻¹ * y * localEmbedGL d q hq h) =
      h⁻¹ * localComponent d q hq y * h := by
  rw [map_mul, map_mul, map_inv, localComponent_localEmbedGL]

/-- `prop:s02-quot`(b) (`s02-quot`): conjugation by `ι_q^{-1} h` does not change the part away from `q`. -/
private theorem awayAt_invConj (h : GL (Fin 2) ℚ_[q]) (y : (BHat d.a d.b)ˣ) :
    awayAt d q hq ((localEmbedGL d q hq h)⁻¹ * y * localEmbedGL d q hq h) = awayAt d q hq y := by
  rw [awayAt_mul, awayAt_mul, awayAt_inv, awayAt_localEmbedGL, inv_one, one_mul, mul_one]

/-- `prop:s02-quot`(b) (`s02-quot`): for a `q`-level `U`, `u ∈ U ↔ u_q ∈ GL₂(ℤ_q) ∧ u^{(q)} ∈ U`. -/
private theorem mem_U_iff_split (hU : IsQLevel d q hq U) (u : (BHat d.a d.b)ˣ) :
    u ∈ U ↔ localComponent d q hq u ∈ GL2Zl q ∧ awayAt d q hq u ∈ U := by
  constructor
  · intro hu
    exact ⟨localComponent_mem_of_isQLevel hU hu, awayAt_mem_of_isQLevel hU hu⟩
  · rintro ⟨h1, h2⟩
    have e : u = localEmbedGL d q hq (localComponent d q hq u) * awayAt d q hq u :=
      eq_localEmbedGL_mul_awayAt u
    rw [e]
    exact mul_mem (localEmbedGL_mem_of_isQLevel hU h1) h2

/-- `prop:s02-quot`(b) (`s02-quot`): for a `q`-level `U`, `u ∈ U_0(q)U ↔ u_q ∈ Iw_q ∧ u^{(q)} ∈ U`. -/
private theorem mem_U0q_iff_split (hU : IsQLevel d q hq U) (u : (BHat d.a d.b)ˣ) :
    u ∈ d.U0q q (coprime_of_not_dvd hq) U ↔ localComponent d q hq u ∈ Iw q ∧ awayAt d q hq u ∈ U := by
  rw [mem_U0q_iff_of_isQLevel hU]
  constructor
  · rintro ⟨hu, hI⟩
    exact ⟨hI, awayAt_mem_of_isQLevel hU hu⟩
  · rintro ⟨hI, hA⟩
    exact ⟨(mem_U_iff_split hU u).2 ⟨Local.K0_le_GL2Zl 1 hI, hA⟩, hI⟩

/-- `prop:s02-quot`(b) (`s02-quot`): for a level `W ≤ U` of the form `W = ι_q^{-1}(K) × U^{(q)}`,
`δ ∈ Γ_{ι_q^{-1} h}(W) ↔ δ ∈ Γ_U ∧ h⁻¹ δ_q h ∈ K` (the norm condition comes from `nrd_eq_one_of_mem_Gam`). -/
private theorem mem_Gam_localEmbedGL_iff (hU : IsQLevel d q hq U) {W : Subgroup (BHat d.a d.b)ˣ}
    (hWU : W ≤ U) {K : Subgroup (GL (Fin 2) ℚ_[q])}
    (hW : ∀ u, u ∈ W ↔ localComponent d q hq u ∈ K ∧ awayAt d q hq u ∈ U)
    (h : GL (Fin 2) ℚ_[q]) (δ : (QuatAlg ℚ d.a d.b)ˣ) :
    δ ∈ Gam W (localEmbedGL d q hq h) ↔
      δ ∈ GammaU d q hq U ∧ h⁻¹ * localComponent d q hq (iotaU d.a d.b δ) * h ∈ K := by
  constructor
  · intro hδ
    have hn : nrd (δ : QuatAlg ℚ d.a d.b) = 1 :=
      nrd_eq_one_of_mem_Gam d.ha d.hb d.O.1 (fun u hu => hU.1 (hWU hu)) hδ
    have h2 := (hW _).1 ((mem_Gam_iff W (localEmbedGL d q hq h) δ).1 hδ)
    rw [localComponent_invConj, awayAt_invConj] at h2
    exact ⟨mem_GammaU_iff.2 ⟨hn, h2.2⟩, h2.1⟩
  · rintro ⟨hδ, hK⟩
    refine (mem_Gam_iff W (localEmbedGL d q hq h) δ).2 ((hW _).2 ?_)
    rw [localComponent_invConj, awayAt_invConj]
    exact ⟨hK, awayAt_mem_of_mem_GammaU hδ⟩

/-- `prop:s02-quot`(b) (`s02-quot`): `(s g) c = g c ↔ (g⁻¹ s g) c = c` for an `SL₂(ℚ_q)`-action. -/
private theorem smul_fix_iff {X : Type*} [MulAction (SLq q) X] (g s : SLq q) (c : X) :
    (s * g) • c = g • c ↔ (g⁻¹ * s * g) • c = c := by
  rw [mul_assoc g⁻¹ s g, mul_smul g⁻¹ (s * g) c, inv_smul_eq_iff]

/-- `prop:s02-quot`(b) (`s02-quot`): `g⁻¹ ι_q(γ) g` in `GL₂(ℚ_q)`. -/
private theorem coe_conj_gammaQ (g : SLq q) (γ : GammaU d q hq U) :
    ((g⁻¹ * gammaQ d q hq U γ * g : SLq q) : GL (Fin 2) ℚ_[q]) =
      (g : GL (Fin 2) ℚ_[q])⁻¹ * localComponent d q hq (iotaU d.a d.b (γ : (QuatAlg ℚ d.a d.b)ˣ)) *
        (g : GL (Fin 2) ℚ_[q]) :=
  rfl

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ_U}(g v₀) = Γ_g(U)` for `g ∈ SL₂(ℚ_q)` (as subgroups of `B^×`). -/
theorem stab_gv0_eq_Gam (hU : IsQLevel d q hq U) (g : SLq q) :
    (MulAction.stabilizer (GammaU d q hq U) (g • v0 q)).map (GammaU d q hq U).subtype =
      Gam U (localEmbedGL d q hq (g : GL (Fin 2) ℚ_[q])) := by
  ext δ
  rw [Subgroup.mem_map]
  refine Iff.trans ?_ (mem_Gam_localEmbedGL_iff (W := U) hU le_rfl (mem_U_iff_split hU) _ δ).symm
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγ' : γ • (g • v0 q) = g • v0 q := MulAction.mem_stabilizer_iff.1 hγ
    rw [gammaU_smul_SLq_smul_vert] at hγ'
    have h1 := mem_GL2Zl_of_smul_v0 ((smul_fix_iff g (gammaQ d q hq U γ) (v0 q)).1 hγ')
    rw [coe_conj_gammaQ] at h1
    exact ⟨γ.2, h1⟩
  · rintro ⟨hδ, hK⟩
    refine ⟨⟨δ, hδ⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, gammaU_smul_SLq_smul_vert]
    refine (smul_fix_iff g (gammaQ d q hq U ⟨δ, hδ⟩) (v0 q)).2 (smul_v0_of_mem ?_)
    rw [coe_conj_gammaQ]
    exact hK

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ_U}(g α v₀) = Γ_{gα}(U)` for `g ∈ SL₂(ℚ_q)`; in the coset model
`g α v₀ = g v₁`. -/
theorem stab_gav0_eq_Gam (hU : IsQLevel d q hq U) (g : SLq q) :
    (MulAction.stabilizer (GammaU d q hq U) (g • v1 q)).map (GammaU d q hq U).subtype =
      Gam U (localEmbedGL d q hq ((g : GL (Fin 2) ℚ_[q]) * alphaq q)) := by
  have e : ∀ x : GL (Fin 2) ℚ_[q], ((g : GL (Fin 2) ℚ_[q]) * alphaq q)⁻¹ * x * ((g : GL (Fin 2) ℚ_[q]) * alphaq q) =
      (alphaq q)⁻¹ * ((g : GL (Fin 2) ℚ_[q])⁻¹ * x * (g : GL (Fin 2) ℚ_[q])) * alphaq q := fun x => by group
  ext δ
  rw [Subgroup.mem_map]
  refine Iff.trans ?_ (mem_Gam_localEmbedGL_iff (W := U) hU le_rfl (mem_U_iff_split hU) _ δ).symm
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγ' : γ • (g • v1 q) = g • v1 q := MulAction.mem_stabilizer_iff.1 hγ
    rw [gammaU_smul_SLq_smul_vert] at hγ'
    have h1 := conj_mem_GL2Zl_of_smul_v1 ((smul_fix_iff g (gammaQ d q hq U γ) (v1 q)).1 hγ')
    rw [coe_conj_gammaQ] at h1
    refine ⟨γ.2, ?_⟩
    rw [e]
    exact h1
  · rintro ⟨hδ, hK⟩
    refine ⟨⟨δ, hδ⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, gammaU_smul_SLq_smul_vert]
    refine (smul_fix_iff g (gammaQ d q hq U ⟨δ, hδ⟩) (v1 q)).2 (smul_v1_of_mem ?_)
    refine mem_K1q_iff.2 ⟨Subtype.prop _, mem_Kalpha_iff.2 ?_⟩
    rw [coe_conj_gammaQ, ← e]
    exact hK

/-- `prop:s02-quot`(b) (`s02-quot`): `Stab_{Γ_U}(g e₀) = Γ_g(U_0(q)U)` for `g ∈ SL₂(ℚ_q)`. -/
theorem stab_ge0_eq_Gam (hU : IsQLevel d q hq U) (g : SLq q) :
    (MulAction.stabilizer (GammaU d q hq U) (g • e0 q)).map (GammaU d q hq U).subtype =
      Gam (d.U0q q (coprime_of_not_dvd hq) U) (localEmbedGL d q hq (g : GL (Fin 2) ℚ_[q])) := by
  ext δ
  rw [Subgroup.mem_map]
  refine Iff.trans ?_ (mem_Gam_localEmbedGL_iff hU (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U)
    (mem_U0q_iff_split hU) _ δ).symm
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγ' : γ • (g • e0 q) = g • e0 q := MulAction.mem_stabilizer_iff.1 hγ
    rw [gammaU_smul_SLq_smul_edgeO] at hγ'
    have h1 := mem_Iw_of_smul_e0 ((smul_fix_iff g (gammaQ d q hq U γ) (e0 q)).1 hγ')
    rw [coe_conj_gammaQ] at h1
    exact ⟨γ.2, h1⟩
  · rintro ⟨hδ, hK⟩
    refine ⟨⟨δ, hδ⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, gammaU_smul_SLq_smul_edgeO]
    refine (smul_fix_iff g (gammaQ d q hq U ⟨δ, hδ⟩) (e0 q)).2 (smul_e0_of_mem ?_)
    rw [coe_conj_gammaQ]
    exact hK

end Stab

/-! ### `prop:s02-free`(b): the edge count at a free level -/

section Free

/-- `prop:s02-free`(b) (`s02-free`): if all stabilisers `Γ_x(W)` are trivial, the full mass is `|X_B(W)|`. -/
private theorem massFull_eq_card_of_free (W : Subgroup (BHat d.a d.b)ˣ) [Finite (XB W)]
    (hfree : ∀ x, Gam W x = ⊥) : massFull W = (Nat.card (XB W) : ℚ) := by
  classical
  haveI : Fintype (XB W) := Fintype.ofFinite _
  have hc : ∀ c : XB W, (1 : ℚ) / (Nat.card (Gam W (Quotient.out c)) : ℚ) = 1 := fun c => by
    rw [hfree, Subgroup.card_bot, Nat.cast_one, div_one]
  rw [massFull, finsum_congr hc, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- `prop:s02-free`(b), count (`s02-free`): at a `q`-level `U` with all `Γ_x(U)` trivial,
`|X_B(U_0(q)U)| = (q + 1) |X_B(U)|` (mass formula with `[U : U_0(q)U] = q + 1`; the stabilisers at level
`U_0(q)U` are then trivial too). -/
theorem card_XB_U0q_of_free (hU : IsQLevel d q hq U) (hfree : ∀ x, Gam U x = ⊥) :
    Nat.card (XB (d.U0q q (coprime_of_not_dvd hq) U)) = (q + 1) * Nat.card (XB U) := by
  have hle : d.U0q q (coprime_of_not_dvd hq) U ≤ U := DefiniteData.U0q_le q (coprime_of_not_dvd hq) U
  haveI hfinU : Finite (XB U) := finite_XB_of_isQLevel hU
  haveI : Finite (XB (d.U0q q (coprime_of_not_dvd hq) U)) := finite_XB_U0q hU
  have hfree' : ∀ x, Gam (d.U0q q (coprime_of_not_dvd hq) U) x = ⊥ := fun x =>
    eq_bot_iff.2 ((Gam_mono hle x).trans (hfree x).le)
  have key := GL2TF.Quat.mass_orbit_count (d.U0q q (coprime_of_not_dvd hq) U) U hle
    (relIndex_U0q_ne_zero hU) hfinU
  change massFull (d.U0q q (coprime_of_not_dvd hq) U) =
    ((d.U0q q (coprime_of_not_dvd hq) U).relIndex U : ℚ) * massFull U at key
  rw [massFull_eq_card_of_free _ hfree', massFull_eq_card_of_free _ hfree, relIndex_U0q hU] at key
  exact_mod_cast key

end Free

end Langlandscape.Tree
