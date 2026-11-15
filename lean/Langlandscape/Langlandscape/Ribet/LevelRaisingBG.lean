/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.LevelRaising
import Langlandscape.Tree.TwoTerm
import Langlandscape.Tree.Hecke

/-!
# Level raising on the Brandt graph: the hypotheses of `alpha_alphaDagger_eq` — S03-L10b

Tex label: `prop:s03-LRdef`. We instantiate the abstract `Langlandscape.Graph.alpha_alphaDagger_eq`
(S03-L10) on stage 02's Brandt graph `BG(U, q)` (`Tree.BG`): `V = X_B(U)`, `E = X_B(U')`,
`U' = U_0(q)U`, `s₀ = π`, `s₁ = [y] ↦ [y α]`, `α = ι_q⁻¹ diag(1, q)`. Note
`(BG d q hq U hU).s0 = s0 d q hq U` and `(BG d q hq U hU).s1 = s1 d q hq U` by `rfl`.

* `lrWeight0`, `lrWeight1` : the natural index weights `a_j e = [Γ_{s_j e} : Γ_e]`, as the coset
  counts `traceCount` (`lrWeight0_mul_wx`, `lrWeight1_mul_wx` : `a_j e · w_e = w_{s_j e}`).
* `s0Tr_single_apply`, `s1Tr_single_apply` : `(tr_j 1_e)(x) = a_j e` if `s_j e = x`, else `0`; hence
  `s_j†` is the transpose of `tr_j` (`evalPairing_dagger`).
* `levelRaising_hf0`, `levelRaising_hf1` : the fibre sums `Σ_{s_j e = x} a_j e = q + 1`.
* Coset step (`trace_translateLin_eq_heckeT`): for `H = U ∩ g U g⁻¹`, `tr_{H→U} ∘ R_g = T_g`
  (`U g U = ⊔_{u ∈ U/H} u g U`). Hence `tr_0 ∘ s_1^* = T_α = T_{ϖ_q}` (`s0Tr_comp_s1Pull_elemT`; `α` and
  `ϖ_q = ι_q⁻¹ diag(q, 1)` are Weyl-conjugate) and `tr_1 ∘ s_0^* = T_{α⁻¹} = T_{z_q⁻¹} T_{ϖ_q}`
  (`heckeT_alphaElt_inv_eq_comp`).
* `levelT_eq_heckeTHom` : `T = s₁* s₀† = T_q` (`heckeTHom U ϖ_q`), for every `q`-level `U`.
* `levelRaising_hsym` : `s₀* s₁† = s₁* s₀†`, given `e_q = ι(q) z_q⁻¹ ∈ U` (so `T_{z_q⁻¹} = 1`);
  `levelRaising_hsym_Ohat`, `levelRaising_hsym_U0` (`q ∤ M`).
* `alpha_alphaDagger_eq_BG`, `alpha_alphaDagger_eq_Ohat`, `alpha_alphaDagger_eq_U0` :
  `α α† = [[q+1, −T_q], [−T_q, q+1]]` on `ℤ[X_B(U)]²`.

Status: formalized (no new hypotheses); the `Graph` namespace is never opened.
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt Langlandscape.Tree
open scoped Classical

/-! ### The coset step `U g U = ⊔_{u ∈ U/H} u g U` -/

section Coset

variable {a b : ℤ}

/-- `prop:s03-LRdef`: the representative `u g` of the left coset `u g U ⊆ U g U` attached to `u ∈ U/H`. -/
private noncomputable def cosetRep (U H : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (u : ↥U ⧸ H.subgroupOf U) : (GL2TF.Quat.BHat a b)ˣ :=
  ((Quotient.out u : U) : (GL2TF.Quat.BHat a b)ˣ) * g

/-- `prop:s03-LRdef` (`s03-LRdef`): if `H ≤ U` and `H = {u ∈ U | g⁻¹ u g ∈ U}`, then
`U ⊓ g U g⁻¹ = H`. -/
theorem inf_conjSub_eq {U H : Subgroup (GL2TF.Quat.BHat a b)ˣ} {g : (GL2TF.Quat.BHat a b)ˣ} (hHU : H ≤ U)
    (hH : ∀ u ∈ U, u ∈ H ↔ g⁻¹ * u * g ∈ U) : U ⊓ Brandt.conjSub U g = H := by
  ext x
  rw [Subgroup.mem_inf, Brandt.mem_conjSub]
  exact ⟨fun h => (hH x h.1).2 h.2, fun h => ⟨hHU h, (hH x (hHU h)).1 h⟩⟩

/-- `prop:s03-LRdef` (`s03-LRdef`), the coset step: if `H ≤ U` and `H = U ∩ g U g⁻¹` (in the form
`u ∈ H ↔ g⁻¹ u g ∈ U` for `u ∈ U`), then `U g U = ⊔_{u ∈ U/H} u g U`, hence
`tr_{H→U} ∘ R_g = T_g`: `Σ_{u ∈ U/H} f[x u g] = (T_g f)[x]`. -/
theorem trace_translateLin_eq_heckeT (U H : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (R : Type*) [CommRing R] (hHU : H ≤ U) (hH : ∀ u ∈ U, u ∈ H ↔ g⁻¹ * u * g ∈ U)
    (hrel : H.relIndex U ≠ 0) (hfin : (U ⊓ Brandt.conjSub U g).relIndex U ≠ 0) :
    (Brandt.trace H U R hrel).comp (Brandt.translateLin R H U g) = Brandt.heckeT U g R hfin := by
  have hg : ∀ h ∈ H, g⁻¹ * h * g ∈ U := fun h hh => (hH h (hHU hh)).1 hh
  have := Brandt.finite_quotient_of_relIndex H U hrel
  letI : Fintype (↥U ⧸ H.subgroupOf U) := Fintype.ofFinite _
  have hinj0 : ∀ u₁ u₂ : ↥U ⧸ H.subgroupOf U,
      (QuotientGroup.mk (cosetRep U H g u₁) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) =
        QuotientGroup.mk (cosetRep U H g u₂) → u₁ = u₂ := by
    intro u₁ u₂ e
    rw [QuotientGroup.eq] at e
    have hc : g⁻¹ * (((Quotient.out u₁)⁻¹ * Quotient.out u₂ : U) : (GL2TF.Quat.BHat a b)ˣ) * g =
        (cosetRep U H g u₁)⁻¹ * cosetRep U H g u₂ := by
      simp only [cosetRep, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hk' : g⁻¹ * (((Quotient.out u₁)⁻¹ * Quotient.out u₂ : U) : (GL2TF.Quat.BHat a b)ˣ) * g ∈ U := by
      rw [hc]
      exact e
    have hk := (hH _ ((Quotient.out u₁)⁻¹ * Quotient.out u₂ : U).2).2 hk'
    rw [← QuotientGroup.out_eq' u₁, ← QuotientGroup.out_eq' u₂, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.2 hk
  have hS : ∀ s ∈ Finset.univ.image (cosetRep U H g), s ∈ Brandt.dcSet U g := by
    intro s hs
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hs
    exact (Brandt.mem_dcSet U g).2 ⟨_, (Quotient.out u).2, 1, U.one_mem, by rw [cosetRep, mul_one]⟩
  have hcov : ∀ y ∈ Brandt.dcSet U g, ∃ s ∈ Finset.univ.image (cosetRep U H g),
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := (Brandt.mem_dcSet U g).1 hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf U) (⟨u, hu⟩ : U)
    refine ⟨cosetRep U H g (QuotientGroup.mk ⟨u, hu⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hhH : ((h : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ H := Subgroup.mem_subgroupOf.1 h.2
    rw [QuotientGroup.eq, cosetRep, hh]
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    convert U.mul_mem (U.inv_mem hv) (hg _ hhH) using 1
    group
  have hinj : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U)
      ↑(Finset.univ.image (cosetRep U H g)) := by
    intro s1 hs1 s2 hs2 e
    obtain ⟨u1, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs1)
    obtain ⟨u2, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs2)
    rw [hinj0 u1 u2 e]
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, Brandt.trace_apply_mk, Brandt.heckeT_apply_reps U g R hfin _ hS hcov hinj f x,
    Finset.sum_image (fun u₁ _ u₂ _ h => hinj0 u₁ u₂ (by rw [h]))]
  simp only [Brandt.traceRaw, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Brandt.translateLin_mk R hg, cosetRep, mul_assoc]

end Coset

/-! ### Transposes of the weighted adjoints -/

section Transpose

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) [Fintype (XB U')]

/-- `prop:s03-LRdef` (`s03-LRdef`): `Pi.single e r = r • Pi.single e 1`. -/
private theorem pi_single_eq_smul {ι : Type*} [DecidableEq ι] (e : ι) (r : ℤ) :
    (Pi.single e r : ι → ℤ) = r • Pi.single e 1 := by
  funext y
  by_cases h : y = e
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

/-- `prop:s03-LRdef` (`s03-LRdef`): if `T 1_e = a_e [s e]` (coefficientwise), then
`(T g)(c) = Σ_{s e = c} a_e g(e)`. -/
theorem apply_eq_sum_of_single (s : XB U' → XB U) (w : XB U' → ℤ) (T : ZXdual U' ℤ →ₗ[ℤ] ZXdual U ℤ)
    (hT : ∀ e c, T (Pi.single e 1) c = if s e = c then w e else 0) (g : ZXdual U' ℤ) (c : XB U) :
    T g c = ∑ e ∈ Finset.univ.filter (fun e => s e = c), w e * g e := by
  conv_lhs => rw [← Finset.univ_sum_single g]
  rw [map_sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pi_single_eq_smul, map_smul, Pi.smul_apply, hT, smul_eq_mul]
  split_ifs <;> ring

/-- `prop:s03-LRdef` (`s03-LRdef`): the weighted adjoint `s†` (weights `a`) is the transpose of `T` for the
evaluation pairings, when `T 1_e = a_e [s e]`: `⟨s† v, g⟩ = ⟨v, T g⟩`. -/
theorem evalPairing_dagger (s : XB U' → XB U) (w : XB U' → ℤ) (T : ZXdual U' ℤ →ₗ[ℤ] ZXdual U ℤ)
    (hT : ∀ e c, T (Pi.single e 1) c = if s e = c then w e else 0) (v : ZX U ℤ) (g : ZXdual U' ℤ) :
    evalPairing U' ℤ (Langlandscape.Graph.dagger s w v) g = evalPairing U ℤ v (T g) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]
  | single c r =>
    simp only [Langlandscape.Graph.dagger_single, map_smul, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply, evalPairing_single, smul_eq_mul, one_mul,
      apply_eq_sum_of_single U' U s w T hT g c]

end Transpose

/-! ### The Brandt graph: the elements `α`, `ϖ_q`, `z_q` -/

section Elements

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s03-LRdef` (`s03-LRdef`): `diag(1, q) · diag(q, 1) = diag(q, q)`. -/
private theorem alphaq_mul_diag' :
    alphaq q * diagGL (Brandt.padicUnit q) 1 = diagGL (Brandt.padicUnit q) (Brandt.padicUnit q) := by
  apply Units.ext
  rw [Units.val_mul]
  show Units.val (diagOneP q) * _ = _
  simp [diagOneP, Brandt.padicUnit]

/-- `prop:s03-LRdef` (`s03-LRdef`): `α ϖ_q = z_q`. -/
theorem alphaElt_mul_elemT_eq_elemS : alphaElt d q hq * Brandt.elemT d q hq = Brandt.elemS d q hq := by
  unfold alphaElt Brandt.elemT Brandt.elemS
  rw [← alphaq_mul_diag', map_mul]

/-- `prop:s03-LRdef` (`s03-LRdef`): `α = w ϖ_q w⁻¹` (`w` the Weyl element at `q`). -/
theorem alphaElt_eq_weyl_conj :
    alphaElt d q hq = localEmbedGL d q hq (Brandt.weylGL q) * Brandt.elemT d q hq *
      (localEmbedGL d q hq (Brandt.weylGL q))⁻¹ := by
  have h2 : alphaElt d q hq = Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹ :=
    eq_mul_inv_of_mul_eq alphaElt_mul_elemT_eq_elemS
  rw [h2, Brandt.elemT_inv_eq d q hq]
  group

/-- `prop:s03-LRdef` (`s03-LRdef`): `α⁻¹ = z_q⁻¹ ϖ_q`. -/
theorem alphaElt_inv_eq : (alphaElt d q hq)⁻¹ = (Brandt.elemS d q hq)⁻¹ * Brandt.elemT d q hq := by
  have h1 : (alphaElt d q hq)⁻¹ = Brandt.elemT d q hq * (Brandt.elemS d q hq)⁻¹ := by
    rw [← alphaElt_mul_elemT_eq_elemS (d := d) (q := q) (hq := hq)]
    group
  rw [h1]
  exact ((Brandt.elemS_commute d q hq (Brandt.elemT d q hq)).inv_left).eq.symm

/-- `prop:s03-LRdef` (`s03-LRdef`): `U α U = U ϖ_q U` for a `q`-level `U`. -/
theorem dcSet_alphaElt_eq (hU : IsQLevel d q hq U) :
    Brandt.dcSet U (alphaElt d q hq) = Brandt.dcSet U (Brandt.elemT d q hq) := by
  have hW : localEmbedGL d q hq (Brandt.weylGL q) ∈ U := localEmbedGL_mem_of_isQLevel hU Brandt.weylGL_mem
  rw [alphaElt_eq_weyl_conj]
  exact Brandt.dcSet_conj_eq U _ _ _ hW (U.inv_mem hW)

/-- `prop:s03-LRdef` (`s03-LRdef`): for `u ∈ U`, `u ∈ U_0(q)U ↔ α⁻¹ u α ∈ U`
(`GL₂(ℤ_q) ∩ α GL₂(ℤ_q) α⁻¹ = Iw_q`). -/
theorem mem_U0q_iff_alphaConj (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U) :
    u ∈ d.U0q q (coprime_of_not_dvd hq) U ↔ (alphaElt d q hq)⁻¹ * u * alphaElt d q hq ∈ U := by
  refine ⟨fun h => alphaElt_inv_conj_mem hU h, fun h => ?_⟩
  refine (mem_U0q_iff_of_isQLevel hU).2 ⟨hu, ?_⟩
  have h1 := localComponent_mem_of_isQLevel hU hu
  have h2 := localComponent_mem_of_isQLevel hU h
  have hα : localComponent d q hq (alphaElt d q hq) = alphaq q := localComponent_localEmbedGL _
  rw [map_mul, map_mul, map_inv, hα] at h2
  rw [← GL2Zl_inf_Kalpha q]
  exact Subgroup.mem_inf.2 ⟨h1, mem_Kalpha_iff.2 h2⟩

/-- `prop:s03-LRdef` (`s03-LRdef`): for `u ∈ U`, `u ∈ α⁻¹ (U_0(q)U) α ↔ α u α⁻¹ ∈ U`. -/
theorem mem_s1Level_iff_alphaConj (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U) :
    u ∈ s1Level d q hq U ↔ (alphaElt d q hq)⁻¹⁻¹ * u * (alphaElt d q hq)⁻¹ ∈ U := by
  rw [inv_inv]
  have hm : u ∈ s1Level d q hq U ↔
      alphaElt d q hq * u * (alphaElt d q hq)⁻¹ ∈ d.U0q q (coprime_of_not_dvd hq) U :=
    Brandt.mem_rightConj _ _
  rw [hm]
  constructor
  · intro h
    exact DefiniteData.U0q_le q (coprime_of_not_dvd hq) U h
  · intro h
    refine (mem_U0q_iff_alphaConj hU h).2 ?_
    have e : (alphaElt d q hq)⁻¹ * (alphaElt d q hq * u * (alphaElt d q hq)⁻¹) * alphaElt d q hq = u := by
      group
    rw [e]
    exact hu

/-- `prop:s03-LRdef` (`s03-LRdef`): `[U : U ∩ α U α⁻¹] ≠ 0` (it is `U_0(q)U`). -/
theorem relIndex_alphaElt_ne_zero (hU : IsQLevel d q hq U) :
    (U ⊓ Brandt.conjSub U (alphaElt d q hq)).relIndex U ≠ 0 := by
  rw [inf_conjSub_eq (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U)
    (fun u hu => mem_U0q_iff_alphaConj hU hu)]
  exact relIndex_U0q_ne_zero hU

/-- `prop:s03-LRdef` (`s03-LRdef`): `[U : U ∩ α⁻¹ U α] ≠ 0` (it is `α⁻¹ (U_0(q)U) α`). -/
theorem relIndex_alphaElt_inv_ne_zero (hU : IsQLevel d q hq U) :
    (U ⊓ Brandt.conjSub U (alphaElt d q hq)⁻¹).relIndex U ≠ 0 := by
  rw [inf_conjSub_eq (s1Level_le hU) (fun u hu => mem_s1Level_iff_alphaConj hU hu)]
  exact relIndex_s1Level_ne_zero hU

/-- `prop:s03-LRdef` (`s03-LRdef`): `[U : U ∩ ϖ_q U ϖ_q⁻¹] ≠ 0` for a `q`-level `U` (stage 1). -/
theorem relIndex_elemT_ne_zero_of_isQLevel (hU : IsQLevel d q hq U) :
    (U ⊓ Brandt.conjSub U (Brandt.elemT d q hq)).relIndex U ≠ 0 :=
  Brandt.relIndex_elemT_ne_zero d U q hq (isInvariantAt_of_isQLevel hU) hU.1

/-- `prop:s03-LRdef` (`s03-LRdef`): `z_q⁻¹` is central, so `[U : U ∩ z_q⁻¹ U z_q] ≠ 0`. -/
theorem relIndex_elemS_inv_ne_zero :
    (U ⊓ Brandt.conjSub U (Brandt.elemS d q hq)⁻¹).relIndex U ≠ 0 :=
  Brandt.relIndex_ne_zero_of_commute U _ fun x => (Brandt.elemS_commute d q hq x).inv_left

end Elements

/-! ### `tr_0 ∘ s_1^* = T_q` and `tr_1 ∘ s_0^* = T_{z_q⁻¹} T_q` -/

section Hecke

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s03-LRdef` (`s03-LRdef`): `tr_0 ∘ s_1^* = T_α` (`U α U = ⊔_{u ∈ U/U_0(q)U} u α U`). -/
theorem s0Tr_comp_s1Pull (hU : IsQLevel d q hq U) (R : Type*) [CommRing R] :
    s0Tr d q hq U R hU ∘ₗ s1Pull d q hq U R =
      Brandt.heckeT U (alphaElt d q hq) R (relIndex_alphaElt_ne_zero hU) :=
  trace_translateLin_eq_heckeT U _ (alphaElt d q hq) R (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U)
    (fun _ hu => mem_U0q_iff_alphaConj hU hu) (relIndex_U0q_ne_zero hU) (relIndex_alphaElt_ne_zero hU)

/-- `prop:s03-LRdef` (`s03-LRdef`): `T_α = T_{ϖ_q}` (`U α U = U ϖ_q U`). -/
theorem heckeT_alphaElt_eq (hU : IsQLevel d q hq U) (R : Type*) [CommRing R] :
    Brandt.heckeT U (alphaElt d q hq) R (relIndex_alphaElt_ne_zero hU) =
      Brandt.heckeT U (Brandt.elemT d q hq) R (relIndex_elemT_ne_zero_of_isQLevel hU) :=
  Brandt.heckeT_congr_dcSet U R (dcSet_alphaElt_eq hU) _ _

/-- `prop:s03-LRdef` (`s03-LRdef`): `tr_0 ∘ s_1^* = T_q = T_{ϖ_q}` on `R^{X(U)}`. -/
theorem s0Tr_comp_s1Pull_elemT (hU : IsQLevel d q hq U) (R : Type*) [CommRing R] :
    s0Tr d q hq U R hU ∘ₗ s1Pull d q hq U R =
      Brandt.heckeT U (Brandt.elemT d q hq) R (relIndex_elemT_ne_zero_of_isQLevel hU) :=
  (s0Tr_comp_s1Pull hU R).trans (heckeT_alphaElt_eq hU R)

/-- `prop:s03-LRdef` (`s03-LRdef`): `tr_1 ∘ s_0^* = T_{α⁻¹}`
(`U α⁻¹ U = ⊔_{u ∈ U/α⁻¹(U_0(q)U)α} u α⁻¹ U`). -/
theorem s1Tr_comp_s0Pull (hU : IsQLevel d q hq U) (R : Type*) [CommRing R] :
    s1Tr d q hq U R hU ∘ₗ s0Pull d q hq U R =
      Brandt.heckeT U (alphaElt d q hq)⁻¹ R (relIndex_alphaElt_inv_ne_zero hU) := by
  have hV : ∀ v ∈ s1Level d q hq U,
      (alphaElt d q hq)⁻¹⁻¹ * v * (alphaElt d q hq)⁻¹ ∈ d.U0q q (coprime_of_not_dvd hq) U := by
    intro v hv
    rw [inv_inv]
    exact Brandt.conj_mem_of_mem_rightConj _ _ v hv
  have hV' : ∀ v ∈ s1Level d q hq U, (alphaElt d q hq)⁻¹⁻¹ * v * (alphaElt d q hq)⁻¹ ∈ U :=
    fun v hv => DefiniteData.U0q_le q (coprime_of_not_dvd hq) U (hV v hv)
  have hT : Brandt.translateLin R (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹ ∘ₗ
      s0Pull d q hq U R = Brandt.translateLin R (s1Level d q hq U) U (alphaElt d q hq)⁻¹ := by
    refine LinearMap.ext fun f => funext fun c => ?_
    obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (s1Level d q hq U) x = c :=
      ⟨_, DoubleCoset.out_eq' c⟩
    rw [LinearMap.comp_apply, Brandt.translateLin_mk R hV, Brandt.translateLin_mk R hV', s0Pull_apply, s0_mk]
  have hG := trace_translateLin_eq_heckeT U (s1Level d q hq U) (alphaElt d q hq)⁻¹ R (s1Level_le hU)
    (fun _ hu => mem_s1Level_iff_alphaConj hU hu) (relIndex_s1Level_ne_zero hU)
    (relIndex_alphaElt_inv_ne_zero hU)
  rw [← hG, ← hT]
  exact LinearMap.ext fun _ => rfl

/-- `prop:s03-LRdef` (`s03-LRdef`): `T_{α⁻¹} = T_{z_q⁻¹} ∘ T_{ϖ_q}` (`α⁻¹ = z_q⁻¹ ϖ_q`, `z_q` central). -/
theorem heckeT_alphaElt_inv_eq_comp (hU : IsQLevel d q hq U) (R : Type*) [CommRing R] :
    Brandt.heckeT U (alphaElt d q hq)⁻¹ R (relIndex_alphaElt_inv_ne_zero hU) =
      Brandt.heckeT U (Brandt.elemS d q hq)⁻¹ R relIndex_elemS_inv_ne_zero ∘ₗ
        Brandt.heckeT U (Brandt.elemT d q hq) R (relIndex_elemT_ne_zero_of_isQLevel hU) := by
  have hzi : ∀ x, Commute (Brandt.elemS d q hq)⁻¹ x := fun x => (Brandt.elemS_commute d q hq x).inv_left
  have hfinzT : (U ⊓ Brandt.conjSub U ((Brandt.elemS d q hq)⁻¹ * Brandt.elemT d q hq)).relIndex U ≠ 0 := by
    rw [Brandt.conjSub_mul_central U _ _ hzi]
    exact relIndex_elemT_ne_zero_of_isQLevel hU
  have hdc : Brandt.dcSet U (alphaElt d q hq)⁻¹ =
      Brandt.dcSet U ((Brandt.elemS d q hq)⁻¹ * Brandt.elemT d q hq) := by
    rw [alphaElt_inv_eq]
  rw [Brandt.heckeT_congr_dcSet U R hdc (relIndex_alphaElt_inv_ne_zero hU) hfinzT]
  exact Brandt.heckeT_central_mul U R _ _ hzi (relIndex_elemT_ne_zero_of_isQLevel hU)
    relIndex_elemS_inv_ne_zero hfinzT

/-- `prop:s03-LRdef` (`s03-LRdef`): if `e_q = ι(q) z_q⁻¹ ∈ U`, then `T_{z_q⁻¹} = 1` on `R^{X(U)}`. -/
theorem heckeT_elemS_inv_eq_id (hS : Brandt.scalarE d q hq ∈ U) (R : Type*) [CommRing R] :
    Brandt.heckeT U (Brandt.elemS d q hq)⁻¹ R relIndex_elemS_inv_ne_zero = LinearMap.id :=
  Brandt.heckeT_eq_id_of_global_central U R _ (iotaU d.a d.b (Brandt.scalarUnit d.a d.b (Brandt.ellUnit q)))⁻¹
    (fun x => (Brandt.elemS_commute d q hq x).inv_left)
    (fun x => (Brandt.commute_iotaU_scalar _ x).inv_left)
    ((globalUnits d.a d.b).inv_mem (MonoidHom.mem_range.2 ⟨_, rfl⟩))
    (by rw [inv_inv]; exact hS) relIndex_elemS_inv_ne_zero

/-- `prop:s03-LRdef` (`s03-LRdef`): if `e_q ∈ U`, then `tr_1 ∘ s_0^* = T_q = T_{ϖ_q}` on `R^{X(U)}`. -/
theorem s1Tr_comp_s0Pull_elemT (hU : IsQLevel d q hq U) (hS : Brandt.scalarE d q hq ∈ U)
    (R : Type*) [CommRing R] :
    s1Tr d q hq U R hU ∘ₗ s0Pull d q hq U R =
      Brandt.heckeT U (Brandt.elemT d q hq) R (relIndex_elemT_ne_zero_of_isQLevel hU) := by
  rw [s1Tr_comp_s0Pull hU R, heckeT_alphaElt_inv_eq_comp hU R, heckeT_elemS_inv_eq_id hS R,
    LinearMap.id_comp]

end Hecke

/-! ### The index weights -/

section Weights

/-- `prop:s03-LRdef`: right translation `[y] ↦ [y α]`, `X(U_0(q)U) ≃ X(α⁻¹(U_0(q)U)α)`, typed with codomain
`XB (s1Level d q hq U)` (`Brandt.rightTranslate` lands in the definitionally equal `XB (rightConj _ _)`). -/
noncomputable def edgeTranslate (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) : XB (d.U0q q (coprime_of_not_dvd hq) U) ≃ XB (s1Level d q hq U) :=
  Brandt.rightTranslate (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)

/-- `prop:s03-LRdef`: the index weight `a_0 e = [Γ_{s_0 e} : Γ_e]`, as the number of `u ∈ U/U_0(q)U` with
`[x u] = e` (`x = (s_0 e).out`); `lrWeight0_mul_wx`. -/
noncomputable def lrWeight0 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) : ℤ :=
  (Brandt.traceCount (d.U0q q (coprime_of_not_dvd hq) U) U (Quotient.out (s0 d q hq U e))
    (Quotient.out e) : ℤ)

/-- `prop:s03-LRdef`: the index weight `a_1 e = [Γ_{s_1 e} : Γ_e]`, as the number of
`u ∈ U/α⁻¹(U_0(q)U)α` with `[x u] = [e α]` (`x = (s_1 e).out`); `lrWeight1_mul_wx`. -/
noncomputable def lrWeight1 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) : ℤ :=
  (Brandt.traceCount (s1Level d q hq U) U (Quotient.out (s1 d q hq U e))
    (Quotient.out (edgeTranslate d q hq U e)) : ℤ)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s03-LRdef` (`s03-LRdef`): `[(e α).out] = s_1 e` in `X(U)`. -/
theorem mk_out_rightTranslate (hU : IsQLevel d q hq U) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    DoubleCoset.mk (globalUnits d.a d.b) U
        (Quotient.out (edgeTranslate d q hq U e)) =
      s1 d q hq U e := by
  have h2 : DoubleCoset.mk (globalUnits d.a d.b) (s1Level d q hq U)
        (Quotient.out (edgeTranslate d q hq U e)) =
      DoubleCoset.mk (globalUnits d.a d.b) (s1Level d q hq U) (Quotient.out e * alphaElt d q hq) :=
    (DoubleCoset.out_eq' (edgeTranslate d q hq U e)).trans rfl
  exact Brandt.mk_eq_mk_of_le (s1Level_le hU) h2

/-- `prop:s03-LRdef` (`s03-LRdef`): `a_0 e · w_e = w_{s_0 e}`. -/
theorem lrWeight0_mul_wx (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    lrWeight0 d q hq U e * (wx (d.U0q q (coprime_of_not_dvd hq) U) (Quotient.out e) : ℤ) =
      (wx U (Quotient.out (s0 d q hq U e)) : ℤ) := by
  have h : DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out (s0 d q hq U e)) =
      DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out e) :=
    DoubleCoset.out_eq' _
  rw [lrWeight0, ← Nat.cast_mul,
    Brandt.traceCount_mul_wx (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) (negOne_mem_U0q_or hq) h]

/-- `prop:s03-LRdef` (`s03-LRdef`): `a_1 e · w_e = w_{s_1 e}`. -/
theorem lrWeight1_mul_wx (hU : IsQLevel d q hq U) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    lrWeight1 d q hq U e * (wx (d.U0q q (coprime_of_not_dvd hq) U) (Quotient.out e) : ℤ) =
      (wx U (Quotient.out (s1 d q hq U e)) : ℤ) := by
  have h : DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out (s1 d q hq U e)) =
      DoubleCoset.mk (globalUnits d.a d.b) U
        (Quotient.out (edgeTranslate d q hq U e)) :=
    (DoubleCoset.out_eq' _).trans (mk_out_rightTranslate hU e).symm
  have hw : wx (s1Level d q hq U)
        (Quotient.out (edgeTranslate d q hq U e)) =
      wx (d.U0q q (coprime_of_not_dvd hq) U) (Quotient.out e) :=
    wx_out_rightTranslate _ _ e
  rw [lrWeight1, ← hw, ← Nat.cast_mul,
    Brandt.traceCount_mul_wx (s1Level_le hU) negOne_mem_s1Level_or h]

/-- `prop:s03-LRdef` (`s03-LRdef`): `(tr_0 1_e)(x) = a_0 e` if `s_0 e = x`, else `0`. -/
theorem s0Tr_single_apply (hU : IsQLevel d q hq U) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) (x : XB U) :
    s0Tr d q hq U ℤ hU (Pi.single e 1) x = if s0 d q hq U e = x then lrWeight0 d q hq U e else 0 := by
  rw [s0Tr, Brandt.trace_single_apply]
  split_ifs with h
  · rw [← h]
    exact rfl
  · have h' : DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out x) ≠
        DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out e) := by
      rw [DoubleCoset.out_eq']
      exact fun h'' => h h''.symm
    rw [Brandt.traceCount_eq_zero (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) h', Nat.cast_zero]

/-- `prop:s03-LRdef` (`s03-LRdef`): `(tr_1 1_e)(x) = a_1 e` if `s_1 e = x`, else `0`. -/
theorem s1Tr_single_apply (hU : IsQLevel d q hq U) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) (x : XB U) :
    s1Tr d q hq U ℤ hU (Pi.single e 1) x = if s1 d q hq U e = x then lrWeight1 d q hq U e else 0 := by
  obtain ⟨c', hc'⟩ : ∃ c' : XB (s1Level d q hq U),
      c' = edgeTranslate d q hq U e := ⟨_, rfl⟩
  have hT : Brandt.translateLin ℤ (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹
      (Pi.single e 1) = Pi.single c' 1 := by
    funext y
    obtain ⟨z, rfl⟩ := (edgeTranslate d q hq U).surjective y
    have hz : Brandt.translateMap (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹
        (edgeTranslate d q hq U z) = z :=
      (edgeTranslate d q hq U).symm_apply_apply z
    show (Pi.single e (1 : ℤ) : XB (d.U0q q (coprime_of_not_dvd hq) U) → ℤ)
        (Brandt.translateMap (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U)
          (alphaElt d q hq)⁻¹ (edgeTranslate d q hq U z)) =
      (Pi.single c' (1 : ℤ) : XB (s1Level d q hq U) → ℤ) (edgeTranslate d q hq U z)
    rw [hz]
    by_cases hze : z = e
    · subst hze
      rw [hc']
      simp
    · rw [Pi.single_eq_of_ne hze, Pi.single_eq_of_ne (fun h => hze
        ((edgeTranslate d q hq U).injective (h.trans hc')))]
  rw [s1Tr, LinearMap.comp_apply, hT, Brandt.trace_single_apply]
  split_ifs with h
  · rw [← h, hc']
    exact rfl
  · have hc1 : DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out c') = s1 d q hq U e := by
      rw [hc']
      exact mk_out_rightTranslate hU e
    have h' : DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out x) ≠
        DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out c') := by
      rw [hc1, DoubleCoset.out_eq']
      exact fun h'' => h h''.symm
    rw [Brandt.traceCount_eq_zero (s1Level_le hU) h', Nat.cast_zero]

/-- `prop:s03-LRdef` (`s03-LRdef`): `tr_0 1 = (q + 1) · 1` (`[U : U_0(q)U] = q + 1`). -/
theorem s0Tr_one (hU : IsQLevel d q hq U) (c : XB U) :
    s0Tr d q hq U ℤ hU (fun _ => 1) c = (q : ℤ) + 1 := by
  have := Brandt.finite_quotient_of_relIndex _ U (relIndex_U0q_ne_zero hU)
  letI : Fintype (↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U) := Fintype.ofFinite _
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk (globalUnits d.a d.b) U y = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [s0Tr_apply_mk hU]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card]
  have h3 : Nat.card (↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U) = q + 1 := relIndex_U0q hU
  rw [h3, Nat.cast_add, Nat.cast_one]

/-- `prop:s03-LRdef` (`s03-LRdef`): `tr_1 1 = (q + 1) · 1` (`tr_1 s_0^* = T_{z_q⁻¹} T_{ϖ_q}` and
`T_{ϖ_q} 1 = tr_0 s_1^* 1 = (q + 1) · 1`). -/
theorem s1Tr_one (hU : IsQLevel d q hq U) (c : XB U) :
    s1Tr d q hq U ℤ hU (fun _ => 1) c = (q : ℤ) + 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk (globalUnits d.a d.b) U y = c := ⟨_, DoubleCoset.out_eq' c⟩
  have hzi : ∀ x, Commute (Brandt.elemS d q hq)⁻¹ x := fun x => (Brandt.elemS_commute d q hq x).inv_left
  have h : s1Tr d q hq U ℤ hU (fun _ => 1) =
      Brandt.heckeT U (alphaElt d q hq)⁻¹ ℤ (relIndex_alphaElt_inv_ne_zero hU) (fun _ => 1) :=
    LinearMap.congr_fun (s1Tr_comp_s0Pull hU ℤ) (fun _ => 1)
  have h2 : Brandt.heckeT U (Brandt.elemT d q hq) ℤ (relIndex_elemT_ne_zero_of_isQLevel hU) (fun _ => 1) =
      s0Tr d q hq U ℤ hU (s1Pull d q hq U ℤ (fun _ => 1)) :=
    (LinearMap.congr_fun (s0Tr_comp_s1Pull_elemT hU ℤ) (fun _ => 1)).symm
  rw [h, heckeT_alphaElt_inv_eq_comp hU ℤ, LinearMap.comp_apply,
    Brandt.heckeT_central_apply U ℤ _ hzi relIndex_elemS_inv_ne_zero _ y, h2]
  exact s0Tr_one hU _

variable [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) U))]

/-- `prop:s03-LRdef` (`s03-LRdef`): the fibre sums `Σ_{s_0 e = x} a_0 e = q + 1` on `BG(U, q)`
(hypothesis `hf0` of `alpha_alphaDagger_eq`). -/
theorem levelRaising_hf0 (hU : IsQLevel d q hq U) :
    ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s0 d q hq U e = x), lrWeight0 d q hq U e = (q : ℤ) + 1 := by
  intro x
  have h := apply_eq_sum_of_single _ U (s0 d q hq U) (lrWeight0 d q hq U) (s0Tr d q hq U ℤ hU)
    (s0Tr_single_apply hU) (fun _ => 1) x
  simp only [mul_one] at h
  exact h.symm.trans (s0Tr_one hU x)

/-- `prop:s03-LRdef` (`s03-LRdef`): the fibre sums `Σ_{s_1 e = x} a_1 e = q + 1` on `BG(U, q)`
(hypothesis `hf1` of `alpha_alphaDagger_eq`). -/
theorem levelRaising_hf1 (hU : IsQLevel d q hq U) :
    ∀ x, ∑ e ∈ Finset.univ.filter (fun e => s1 d q hq U e = x), lrWeight1 d q hq U e = (q : ℤ) + 1 := by
  intro x
  have h := apply_eq_sum_of_single _ U (s1 d q hq U) (lrWeight1 d q hq U) (s1Tr d q hq U ℤ hU)
    (s1Tr_single_apply hU) (fun _ => 1) x
  simp only [mul_one] at h
  exact h.symm.trans (s1Tr_one hU x)

omit [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) U))] in
/-- `prop:s03-LRdef` (`s03-LRdef`): `⟨s_{0*} a, f⟩ = ⟨a, s_0^* f⟩`. -/
private theorem evalPairing_lmapDomain_s0 (w : ZX (d.U0q q (coprime_of_not_dvd hq) U) ℤ) (f : ZXdual U ℤ) :
    evalPairing U ℤ (Finsupp.lmapDomain ℤ ℤ (s0 d q hq U) w) f =
      evalPairing (d.U0q q (coprime_of_not_dvd hq) U) ℤ w (s0Pull d q hq U ℤ f) :=
  Tree.evalPairing_pushforward (R := ℤ) w f

omit [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) U))] in
/-- `prop:s03-LRdef` (`s03-LRdef`): `⟨s_{1*} a, f⟩ = ⟨a, s_1^* f⟩`. -/
private theorem evalPairing_lmapDomain_s1 (w : ZX (d.U0q q (coprime_of_not_dvd hq) U) ℤ) (f : ZXdual U ℤ) :
    evalPairing U ℤ (Finsupp.lmapDomain ℤ ℤ (s1 d q hq U) w) f =
      evalPairing (d.U0q q (coprime_of_not_dvd hq) U) ℤ w (s1Pull d q hq U ℤ f) :=
  Tree.evalPairing_s1Push ℤ w f

/-- `prop:s03-LRdef` (`s03-LRdef`), the bridge: on `BG(U, q)` the operator `T = s₁* s₀†` of S03-L10 is the
Brandt operator `T_q = [U ϖ_q U]` (`heckeTHom`, `ϖ_q = ι_q⁻¹ diag(q, 1)`), for every `q`-level `U`. -/
theorem levelT_eq_heckeTHom (hU : IsQLevel d q hq U) [Finite (XB U)] :
    Langlandscape.Graph.levelT (s0 d q hq U) (s1 d q hq U) (lrWeight0 d q hq U) =
      Brandt.heckeTHom U (Brandt.elemT d q hq) ℤ (relIndex_elemT_ne_zero_of_isQLevel hU) := by
  refine LinearMap.ext fun v => Brandt.zx_ext_of_evalPairing U ℤ fun f => ?_
  rw [Brandt.heckeTHom_transpose, Langlandscape.Graph.levelT, LinearMap.comp_apply,
    evalPairing_lmapDomain_s1, evalPairing_dagger _ U _ _ _ (s0Tr_single_apply hU)]
  exact congrArg (evalPairing U ℤ v) (LinearMap.congr_fun (s0Tr_comp_s1Pull_elemT hU ℤ) f)

/-- `prop:s03-LRdef` (`s03-LRdef`): the symmetry `s₀* s₁† = s₁* s₀†` on `BG(U, q)` (hypothesis `hsym` of
`alpha_alphaDagger_eq`), for a `q`-level `U` containing `e_q = ι(q) z_q⁻¹`: both sides are transposes of
`T_q` (`tr_1 s_0^* = T_{z_q⁻¹} T_q = T_q = tr_0 s_1^*`). -/
theorem levelRaising_hsym (hU : IsQLevel d q hq U) (hS : Brandt.scalarE d q hq ∈ U) :
    ∀ x : XB U, Finsupp.lmapDomain ℤ ℤ (s0 d q hq U)
        (Langlandscape.Graph.dagger (s1 d q hq U) (lrWeight1 d q hq U) (Finsupp.single x 1)) =
      Finsupp.lmapDomain ℤ ℤ (s1 d q hq U)
        (Langlandscape.Graph.dagger (s0 d q hq U) (lrWeight0 d q hq U) (Finsupp.single x 1)) := by
  intro x
  refine Brandt.zx_ext_of_evalPairing U ℤ fun f => ?_
  rw [evalPairing_lmapDomain_s0, evalPairing_dagger _ U _ _ _ (s1Tr_single_apply hU),
    evalPairing_lmapDomain_s1, evalPairing_dagger _ U _ _ _ (s0Tr_single_apply hU)]
  have h1 := LinearMap.congr_fun (s1Tr_comp_s0Pull_elemT hU hS ℤ) f
  have h0 := LinearMap.congr_fun (s0Tr_comp_s1Pull_elemT hU ℤ) f
  exact congrArg (evalPairing U ℤ (Finsupp.single x 1)) (h1.trans h0.symm)

/-- `prop:s03-LRdef` (`s03-LRdef`): `α α† = [[q+1, −T_q], [−T_q, q+1]]` on `ℤ[X_B(U)]²` for the Brandt graph
`BG(U, q)` with the natural index weights, `U` a `q`-level containing `e_q`. -/
theorem alpha_alphaDagger_eq_BG (hU : IsQLevel d q hq U) (hS : Brandt.scalarE d q hq ∈ U) [Finite (XB U)]
    (v : ZX U ℤ × ZX U ℤ) :
    Langlandscape.Graph.alphaMap (s0 d q hq U) (s1 d q hq U)
        (Langlandscape.Graph.alphaDagger (s0 d q hq U) (s1 d q hq U) (lrWeight0 d q hq U)
          (lrWeight1 d q hq U) v) =
      (((q : ℤ) + 1) • v.1 -
          Brandt.heckeTHom U (Brandt.elemT d q hq) ℤ (relIndex_elemT_ne_zero_of_isQLevel hU) v.2,
        ((q : ℤ) + 1) • v.2 -
          Brandt.heckeTHom U (Brandt.elemT d q hq) ℤ (relIndex_elemT_ne_zero_of_isQLevel hU) v.1) := by
  rw [Langlandscape.Graph.alpha_alphaDagger_eq _ _ _ _ (q : ℤ) (levelRaising_hf0 hU) (levelRaising_hf1 hU)
    (levelRaising_hsym hU hS) v, levelT_eq_heckeTHom hU]

end Weights

/-! ### The levels `Ô^×` and `U_0(M)` -/

section Levels

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}

/-- `prop:s03-LRdef` (`s03-LRdef`): `hsym` on `BG(Ô^×, q)`. -/
theorem levelRaising_hsym_Ohat [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat))] :
    ∀ x : XB d.Ohat, Finsupp.lmapDomain ℤ ℤ (s0 d q hq d.Ohat)
        (Langlandscape.Graph.dagger (s1 d q hq d.Ohat) (lrWeight1 d q hq d.Ohat) (Finsupp.single x 1)) =
      Finsupp.lmapDomain ℤ ℤ (s1 d q hq d.Ohat)
        (Langlandscape.Graph.dagger (s0 d q hq d.Ohat) (lrWeight0 d q hq d.Ohat) (Finsupp.single x 1)) :=
  levelRaising_hsym isQLevel_Ohat (Brandt.scalarE_mem_Ohat d q hq)

/-- `prop:s03-LRdef` (`s03-LRdef`): `hsym` on `BG(U_0(M), q)` for `q ∤ D M`. -/
theorem levelRaising_hsym_U0 {M : ℕ} (hM : M.Coprime d.D) (hqM : ¬ q ∣ M)
    [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) (d.U0 M hM)))] :
    ∀ x : XB (d.U0 M hM), Finsupp.lmapDomain ℤ ℤ (s0 d q hq (d.U0 M hM))
        (Langlandscape.Graph.dagger (s1 d q hq (d.U0 M hM)) (lrWeight1 d q hq (d.U0 M hM))
          (Finsupp.single x 1)) =
      Finsupp.lmapDomain ℤ ℤ (s1 d q hq (d.U0 M hM))
        (Langlandscape.Graph.dagger (s0 d q hq (d.U0 M hM)) (lrWeight0 d q hq (d.U0 M hM))
          (Finsupp.single x 1)) :=
  levelRaising_hsym (isQLevel_U0 hqM) (Brandt.scalarE_mem_U0 d hM q hq hqM)

/-- `prop:s03-LRdef` (`s03-LRdef`): `α α† = [[q+1, −T_q], [−T_q, q+1]]` on `ℤ[X_B(Ô^×)]²`. -/
theorem alpha_alphaDagger_eq_Ohat [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat))] [Finite (XB d.Ohat)]
    (v : ZX d.Ohat ℤ × ZX d.Ohat ℤ) :
    Langlandscape.Graph.alphaMap (s0 d q hq d.Ohat) (s1 d q hq d.Ohat)
        (Langlandscape.Graph.alphaDagger (s0 d q hq d.Ohat) (s1 d q hq d.Ohat) (lrWeight0 d q hq d.Ohat)
          (lrWeight1 d q hq d.Ohat) v) =
      (((q : ℤ) + 1) • v.1 - Brandt.heckeTHom d.Ohat (Brandt.elemT d q hq) ℤ
          (relIndex_elemT_ne_zero_of_isQLevel isQLevel_Ohat) v.2,
        ((q : ℤ) + 1) • v.2 - Brandt.heckeTHom d.Ohat (Brandt.elemT d q hq) ℤ
          (relIndex_elemT_ne_zero_of_isQLevel isQLevel_Ohat) v.1) :=
  alpha_alphaDagger_eq_BG isQLevel_Ohat (Brandt.scalarE_mem_Ohat d q hq) v

/-- `prop:s03-LRdef` (`s03-LRdef`): `α α† = [[q+1, −T_q], [−T_q, q+1]]` on `ℤ[X_B(U_0(M))]²` for `q ∤ D M`. -/
theorem alpha_alphaDagger_eq_U0 {M : ℕ} (hM : M.Coprime d.D) (hqM : ¬ q ∣ M)
    [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) (d.U0 M hM)))] [Finite (XB (d.U0 M hM))]
    (v : ZX (d.U0 M hM) ℤ × ZX (d.U0 M hM) ℤ) :
    Langlandscape.Graph.alphaMap (s0 d q hq (d.U0 M hM)) (s1 d q hq (d.U0 M hM))
        (Langlandscape.Graph.alphaDagger (s0 d q hq (d.U0 M hM)) (s1 d q hq (d.U0 M hM))
          (lrWeight0 d q hq (d.U0 M hM)) (lrWeight1 d q hq (d.U0 M hM)) v) =
      (((q : ℤ) + 1) • v.1 - Brandt.heckeTHom (d.U0 M hM) (Brandt.elemT d q hq) ℤ
          (relIndex_elemT_ne_zero_of_isQLevel (isQLevel_U0 hqM)) v.2,
        ((q : ℤ) + 1) • v.2 - Brandt.heckeTHom (d.U0 M hM) (Brandt.elemT d q hq) ℤ
          (relIndex_elemT_ne_zero_of_isQLevel (isQLevel_U0 hqM)) v.1) :=
  alpha_alphaDagger_eq_BG (isQLevel_U0 hqM) (Brandt.scalarE_mem_U0 d hM q hq hqM) v

end Levels

end Langlandscape.Ribet
