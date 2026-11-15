/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Action
import Langlandscape.Tree.BrandtGraph
import Langlandscape.Tree.NormOne
import Langlandscape.Hyp.BTtree
import Langlandscape.Hyp.SA

/-!
# Core of the quotient proposition `prop:s02-BG` (S02-L5b)

`plan/staged/stage-02-tree-quotients.tex` and `mathematics/chapters/s02/2-quotient.tex`: `prop:s02-BG`
("SA for one level as a finite check"), `if:s02-tree`.

Fix a prime `q ∤ D` and a `q`-level `U` (`IsQLevel d q hq U`), `U' = U_0(q)U`, `α = diag(1, q)`. The group
`Γ_U` acts on the tree `𝒯_q` (coset model of S02-L1) through `ι_q` (S02-L4a). We define

* `phiV : Γ_U \ V(𝒯_q) → X_B(U) ⊕ X_B(U)`, `Γ_U (s v₀) ↦ inl [s]`, `Γ_U (s v₁) ↦ inr [s α]` (`s ∈ SL₂(ℚ_q)`);
* `phiE : Γ_U \ E(𝒯_q) → X_B(U')`, `Γ_U (s e₀) ↦ [s]`

(`phiV_type0`, `phiV_type1`, `phiE_type`; the definitions use a choice of representatives, the formulas need the
`q`-level hypothesis), and prove:

* Step 1 (well defined) and Step 0 (`Γ_U`-invariance): `vertMap_type0`, `vertMap_type1`, `edgeMap_type`,
  `vertMap_smul`, `edgeMap_smul`;
* Step 2 (the norm argument): `phiV_injective`, `phiE_injective`;
* Step 3 (graph morphism): `phiV_oO`, `phiV_tO` (endpoints become `inl ∘ s₀`, `inr ∘ s₁`);
* Step 4 (local surjectivity): `phi_locSurj_type0`, `phi_locSurj_type1`;
* (i) `surjType0` (`φ₀` surjective; `surjType0_iff`); (a) `bijective_of_surjType0` ((i) ⇒ bijections, tree-free);
  (iii) ⇒ (i) and (iii) ⇒ bijections `bijective_of_BGConnected` (tree-free); (ii) ⇒ (i) `surj_of_SA`;
  (i) ⇒ (ii) `SA_of_surj`; (i) ⇒ (iii) `BGConnected_of_surj` (**the only use of `Hyp.BTtree`**);
  export `BGConnected_of_SA_HS` (`Hyp.SA ∧ Hyp.HS ∧ Hyp.BTtree ⇒ (iii)` at every `q`-admissible level).

`bijective_of_BGConnected` and `bijective_of_surjType0` take no `Hyp.*` argument.

Status: *formalized* (modulo `Hyp.BTtree` in `BGConnected_of_surj`, and `Hyp.SA`, `Hyp.HS`, `Hyp.BTtree` in
`BGConnected_of_SA_HS`).
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local
open GL2TF.Quat (nrd)

/-! ### Generalities -/

section General

/-- `prop:s02-BG` (`s02-BG`): the representative chosen by `Quotient.out` of an orbit class lies in the orbit. -/
private theorem exists_out_eq_smul {G X : Type*} [Group G] [MulAction G X] (x : X) :
    ∃ g : G, Quotient.out (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = g • x := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' x : MulAction.orbitRel.Quotient G X)) :
      MulAction.orbitRel.Quotient G X) = Quotient.mk'' x := Quotient.out_eq' _
  have h2 : Quotient.out (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) ∈ MulAction.orbit G x :=
    Quotient.eq''.1 h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h2
  exact ⟨g, hg.symm⟩

/-- `prop:s02-BG` (`s02-BG`): an element of `ZMod 2` different from `0` is `1`. -/
private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  first
  | (revert h; revert x; decide)
  | (fin_cases x <;> simp_all)

end General

/-! ### Local and adelic auxiliaries -/

section Aux

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG` (`s02-BG`): elements of `SL₂(ℚ_q)` have determinant `1`. -/
private theorem det_SLq (s : SLq q) : Matrix.GeneralLinearGroup.det (s : GL (Fin 2) ℚ_[q]) = 1 :=
  MonoidHom.mem_ker.1 s.2

/-- `prop:s02-BG` (`s02-BG`): elements of `SL₂(ℚ_q)` preserve the type of a vertex. -/
theorem vtype_smul_SLq (s : SLq q) (v : Vert q) : vtype q (s • v) = vtype q v := by
  show vtype q ((s : GL (Fin 2) ℚ_[q]) • v) = vtype q v
  rw [vtype_smul, vdet_of_mem_SLq s.2, zero_add]

/-- `prop:s02-BG` (`s02-BG`): every vertex of `𝒯_q` is `s v₀` or `s v₁` with `s ∈ SL₂(ℚ_q)`
(`lem:s02-tree`(c)). -/
private theorem vert_cases (v : Vert q) : (∃ s : SLq q, s • v0 q = v) ∨ ∃ s : SLq q, s • v1 q = v := by
  by_cases h : vtype q v = 0
  · exact Or.inl (SLq_transitive_type0 h)
  · exact Or.inr (SLq_transitive_type1 (zmod2_eq_one_of_ne_zero h))

/-- `prop:s02-BG` (`s02-BG`): `Nrd(ι_q^{-1} g) = 1` in `𝔸_f^×` for `g ∈ SL₂(ℚ_q)`
(`det ∘ ι_q = nrd`, `det_iota`, componentwise). -/
theorem nrdHat_localEmbedGL {g : GL (Fin 2) ℚ_[q]} (hg : Matrix.GeneralLinearGroup.det g = 1) :
    nrdHat d.a d.b (localEmbedGL d q hq g) = 1 := by
  have hx : nrd (((d.iotaGL q hq).symm g : (QuatAlg ℚ_[q] d.a d.b)ˣ) : QuatAlg ℚ_[q] d.a d.b) = 1 := by
    rw [DefiniteData.iotaGL_symm_val, ← det_iota (d := d) (ℓ := q) (hℓ := hq), AlgEquiv.apply_symm_apply,
      ← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
  refine Units.ext ?_
  ext p
  show adeleProj (p : ℕ) (nrd ((localEmbedGL d q hq g : (BHat d.a d.b)ˣ) : BHat d.a d.b)) =
    adeleProj (p : ℕ) 1
  rw [← nrd_localProj, map_one, localEmbedGL_apply, localEmbed_val, localProj_localEmbedHom]
  by_cases hp : p = primeIdx q
  · subst hp
    rw [singleFam_self]
    exact hx
  · rw [singleFam_of_ne _ _ _ _ hp]
    exact GL2TF.Quat.nrdHom_one_aux

/-- `prop:s02-BG` (`s02-BG`): if `Nrd u = 1` then `det ι_q(u_q) = 1`. -/
theorem det_localComponent_of_nrdHat {u : (BHat d.a d.b)ˣ} (hu : nrdHat d.a d.b u = 1) :
    Matrix.GeneralLinearGroup.det (localComponent d q hq u) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, localComponent_val, det_iota, nrd_localProj, Units.val_one]
  have h : nrd ((u : BHat d.a d.b) : QuatAlg GL2TF.FinAdele d.a d.b) = 1 := congrArg Units.val hu
  rw [h, map_one]

/-- `prop:s02-BG` (`s02-BG`): `[g u] = [g]` in `X_B(W)` for `u ∈ W`. -/
private theorem mk_mul_right_mem {W : Subgroup (BHat d.a d.b)ˣ} {g u : (BHat d.a d.b)ˣ} (hu : u ∈ W) :
    DoubleCoset.mk (globalUnits d.a d.b) W (g * u) = DoubleCoset.mk (globalUnits d.a d.b) W g :=
  (DoubleCoset.eq.2 ⟨1, one_mem _, u, hu, by rw [one_mul]⟩).symm

/-- `prop:s02-BG` (`s02-BG`): `[x g] = [g]` in `X_B(W)` for `x ∈ B^×`. -/
private theorem mk_global_mul {W : Subgroup (BHat d.a d.b)ˣ} {x g : (BHat d.a d.b)ˣ} (hx : x ∈ globalUnits d.a d.b) :
    DoubleCoset.mk (globalUnits d.a d.b) W (x * g) = DoubleCoset.mk (globalUnits d.a d.b) W g :=
  (DoubleCoset.eq.2 ⟨x, hx, 1, one_mem _, by rw [mul_one]⟩).symm

/-- `prop:s02-BG` (`s02-BG`): `awayAt q (ι_q^{-1} g) = 1`. -/
theorem awayAt_localEmbedGL (g : GL (Fin 2) ℚ_[q]) : awayAt d q hq (localEmbedGL d q hq g) = 1 := by
  unfold awayAt
  rw [localComponent_localEmbedGL, map_inv, mul_inv_cancel]

/-- `prop:s02-BG` (`s02-BG`): `u = ι_q^{-1}(u_q) · u^{(q)}`. -/
theorem eq_localEmbedGL_mul_awayAt (u : (BHat d.a d.b)ˣ) :
    u = localEmbedGL d q hq (localComponent d q hq u) * awayAt d q hq u := by
  rw [← (commute_awayAt_localEmbedGL (hp := hq) u (localComponent d q hq u)).eq, awayAt_mul_localEmbedGL]

/-- `prop:s02-BG`, Step 0 (`s02-BG`): for `x ∈ B^×` with `x^{(q)} ∈ W` and `h ∈ GL₂(ℚ_q)`,
`[ι_q^{-1}(x_q h)] = [ι_q^{-1} h]` in `X_B(W)`. -/
theorem mk_localComponent_mul {W : Subgroup (BHat d.a d.b)ˣ} {x : (BHat d.a d.b)ˣ}
    (hx : x ∈ globalUnits d.a d.b) (hxW : awayAt d q hq x ∈ W) (h : GL (Fin 2) ℚ_[q]) :
    DoubleCoset.mk (globalUnits d.a d.b) W (localEmbedGL d q hq (localComponent d q hq x * h)) =
      DoubleCoset.mk (globalUnits d.a d.b) W (localEmbedGL d q hq h) := by
  have hc : Commute (awayAt d q hq x) (localEmbedGL d q hq (localComponent d q hq x * h)) :=
    commute_awayAt_localEmbedGL x _
  have e : localEmbedGL d q hq (localComponent d q hq x * h) =
      x * localEmbedGL d q hq h * (awayAt d q hq x)⁻¹ := by
    calc localEmbedGL d q hq (localComponent d q hq x * h)
        = awayAt d q hq x * localEmbedGL d q hq (localComponent d q hq x * h) * (awayAt d q hq x)⁻¹ := by
          rw [hc.eq, mul_inv_cancel_right]
      _ = x * localEmbedGL d q hq h * (awayAt d q hq x)⁻¹ := by
          rw [map_mul (localEmbedGL d q hq), ← mul_assoc, awayAt_mul_localEmbedGL]
  rw [e]
  exact (DoubleCoset.eq.2 ⟨x, hx, (awayAt d q hq x)⁻¹, inv_mem hxW, rfl⟩).symm

/-- `prop:s02-BG` (`s02-BG`): for a `q`-level `U`, an element of `U` with `q`-component `1` lies in `U_0(q)U`. -/
theorem mem_U0q_of_localComponent_eq_one (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U)
    (h1 : localComponent d q hq u = 1) : u ∈ d.U0q q (coprime_of_not_dvd hq) U :=
  (mem_U0q_iff_of_isQLevel hU).2 ⟨hu, by rw [h1]; exact one_mem _⟩

/-- `prop:s02-BG` (`s02-BG`): `ι_q^{-1}(Iw_q) ⊆ U_0(q)U` for a `q`-level `U`. -/
theorem localEmbedGL_mem_U0q (hU : IsQLevel d q hq U) {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ Iw q) :
    localEmbedGL d q hq k ∈ d.U0q q (coprime_of_not_dvd hq) U :=
  (mem_U0q_iff_of_isQLevel hU).2
    ⟨localEmbedGL_mem_of_isQLevel hU (K0_le_GL2Zl 1 hk), by rw [localComponent_localEmbedGL]; exact hk⟩

/-- `prop:s02-BG` (`s02-BG`): `u^{(q)} ∈ U_0(q)U` for `u ∈ U`, `U` a `q`-level. -/
theorem awayAt_mem_U0q (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U) :
    awayAt d q hq u ∈ d.U0q q (coprime_of_not_dvd hq) U :=
  mem_U0q_of_localComponent_eq_one hU (awayAt_mem_of_isQLevel hU hu) (localComponent_awayAt u)

/-- `prop:s02-BG`, the norm argument of Step 2 (`s02-BG`): if `ι_q^{-1}(s' a) = β · ι_q^{-1}(s a) · u` with
`det s = det s' = 1`, `β ∈ B^×` and `u ∈ W ≤ U ≤ Ô^×`, then `Nrd β = 1` and `Nrd u = 1`. -/
theorem nrd_eq_one_of_localEmbedGL_eq (hU : IsQLevel d q hq U) {W : Subgroup (BHat d.a d.b)ˣ} (hW : W ≤ U)
    {s s' a : GL (Fin 2) ℚ_[q]} (hs : Matrix.GeneralLinearGroup.det s = 1)
    (hs' : Matrix.GeneralLinearGroup.det s' = 1) {β : (QuatAlg ℚ d.a d.b)ˣ} {u : (BHat d.a d.b)ˣ}
    (hu : u ∈ W) (h : localEmbedGL d q hq (s' * a) = iotaU d.a d.b β * localEmbedGL d q hq (s * a) * u) :
    nrd (β : QuatAlg ℚ d.a d.b) = 1 ∧ nrdHat d.a d.b u = 1 := by
  have h1 := congrArg (nrdHat d.a d.b) h
  simp only [map_mul, nrdHat_localEmbedGL (d := d) (hq := hq) hs, nrdHat_localEmbedGL (d := d) (hq := hq) hs',
    one_mul] at h1
  have h2 : nrdHat d.a d.b (iotaU d.a d.b β) * nrdHat d.a d.b u = 1 := by
    refine mul_left_cancel (a := nrdHat d.a d.b (localEmbedGL d q hq a)) ?_
    calc nrdHat d.a d.b (localEmbedGL d q hq a) * (nrdHat d.a d.b (iotaU d.a d.b β) * nrdHat d.a d.b u)
        = nrdHat d.a d.b (iotaU d.a d.b β) * nrdHat d.a d.b (localEmbedGL d q hq a) * nrdHat d.a d.b u := by
          rw [← mul_assoc, mul_comm (nrdHat d.a d.b (localEmbedGL d q hq a))]
      _ = nrdHat d.a d.b (localEmbedGL d q hq a) := h1.symm
      _ = nrdHat d.a d.b (localEmbedGL d q hq a) * 1 := (mul_one _).symm
  exact nrd_eq_one_of_nrdHat_mul_eq_one d.ha d.hb d.O.1
    (hU.1 (hW hu) : u ∈ GL2TF.Quat.orderCompletionUnits d.O.1) β h2

/-- `prop:s02-BG`, Step 2 (`s02-BG`): if `[ι_q^{-1}(s a)] = [ι_q^{-1}(s' a)]` in `X_B(W)` (`W ≤ U`,
`s, s' ∈ SL₂(ℚ_q)`), then `s' a = γ_q (s a) u_q` for some `γ ∈ Γ_U` and `u ∈ W`. -/
theorem exists_gammaU_of_mk_eq (hU : IsQLevel d q hq U) {W : Subgroup (BHat d.a d.b)ˣ} (hW : W ≤ U)
    {s s' a : GL (Fin 2) ℚ_[q]} (hs : Matrix.GeneralLinearGroup.det s = 1)
    (hs' : Matrix.GeneralLinearGroup.det s' = 1)
    (h : DoubleCoset.mk (globalUnits d.a d.b) W (localEmbedGL d q hq (s * a)) =
      DoubleCoset.mk (globalUnits d.a d.b) W (localEmbedGL d q hq (s' * a))) :
    ∃ γ : GammaU d q hq U, ∃ u ∈ W,
      s' * a = gammaQGL d q hq U γ * (s * a) * localComponent d q hq u := by
  obtain ⟨x, hx, u, hu, heq⟩ := DoubleCoset.eq.1 h
  obtain ⟨β, rfl⟩ := hx
  have heq' : localEmbedGL d q hq (s' * a) = iotaU d.a d.b β * localEmbedGL d q hq (s * a) * u := heq
  obtain ⟨hβ1, -⟩ := nrd_eq_one_of_localEmbedGL_eq hU hW hs hs' hu heq'
  have haway : awayAt d q hq (iotaU d.a d.b β) ∈ U := by
    have h2 := congrArg (awayAt d q hq) heq'
    rw [awayAt_mul, awayAt_mul, awayAt_localEmbedGL, awayAt_localEmbedGL, mul_one] at h2
    have h3 : awayAt d q hq (iotaU d.a d.b β) = (awayAt d q hq u)⁻¹ := eq_inv_of_mul_eq_one_left h2.symm
    rw [h3]
    exact inv_mem (awayAt_mem_of_isQLevel hU (hW hu))
  refine ⟨⟨β, mem_GammaU_iff.2 ⟨hβ1, haway⟩⟩, u, hu, ?_⟩
  have h4 := congrArg (localComponent d q hq) heq'
  rw [map_mul (localComponent d q hq), map_mul (localComponent d q hq), localComponent_localEmbedGL,
    localComponent_localEmbedGL] at h4
  exact h4

end Aux

/-! ### Stabilisers and the action -/

section Stab

variable {q : ℕ} [Fact q.Prime]

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r v₀ = v₀` gives `r ∈ GL₂(ℤ_q)`. -/
theorem mem_GL2Zl_of_smul_v0 {r : SLq q} (hr : r • v0 q = v0 q) : (r : GL (Fin 2) ℚ_[q]) ∈ GL2Zl q := by
  have h1 : r ∈ MulAction.stabilizer (SLq q) (v0 q) := hr
  rw [stabilizer_v0 q, Subgroup.mem_subgroupOf, mem_SL2Zq_iff] at h1
  exact h1.2

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r ∈ GL₂(ℤ_q)` fixes `v₀`. -/
theorem smul_v0_of_mem {r : SLq q} (hr : (r : GL (Fin 2) ℚ_[q]) ∈ GL2Zl q) : r • v0 q = v0 q := by
  have h1 : r ∈ (SL2Zq q).subgroupOf (SLq q) := Subgroup.mem_subgroupOf.2 (mem_SL2Zq_iff.2 ⟨r.2, hr⟩)
  rw [← stabilizer_v0 q] at h1
  exact h1

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r v₁ = v₁` gives `α⁻¹ r α ∈ GL₂(ℤ_q)`. -/
theorem conj_mem_GL2Zl_of_smul_v1 {r : SLq q} (hr : r • v1 q = v1 q) :
    (alphaq q)⁻¹ * (r : GL (Fin 2) ℚ_[q]) * alphaq q ∈ GL2Zl q := by
  have h1 : r ∈ MulAction.stabilizer (SLq q) (v1 q) := hr
  rw [stabilizer_v1 q, Subgroup.mem_subgroupOf, mem_K1q_iff] at h1
  exact mem_Kalpha_iff.1 h1.2

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r ∈ K1q = SL₂ ∩ α GL₂(ℤ_q) α⁻¹` fixes `v₁`. -/
theorem smul_v1_of_mem {r : SLq q} (hr : (r : GL (Fin 2) ℚ_[q]) ∈ K1q q) : r • v1 q = v1 q := by
  have h1 : r ∈ (K1q q).subgroupOf (SLq q) := Subgroup.mem_subgroupOf.2 hr
  rw [← stabilizer_v1 q] at h1
  exact h1

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r e₀ = e₀` gives `r ∈ Iw_q`. -/
theorem mem_Iw_of_smul_e0 {r : SLq q} (hr : r • e0 q = e0 q) : (r : GL (Fin 2) ℚ_[q]) ∈ Iw q := by
  have h1 : r ∈ MulAction.stabilizer (SLq q) (e0 q) := hr
  rw [stabilizer_e0 q, Subgroup.mem_subgroupOf, mem_IwSL_iff] at h1
  exact h1.2

/-- `prop:s02-BG`, `lem:s02-tree`(c) (`s02-BG`): `r ∈ Iw_q` fixes `e₀`. -/
theorem smul_e0_of_mem {r : SLq q} (hr : (r : GL (Fin 2) ℚ_[q]) ∈ Iw q) : r • e0 q = e0 q := by
  have h1 : r ∈ (IwSL q).subgroupOf (SLq q) := Subgroup.mem_subgroupOf.2 (mem_IwSL_iff.2 ⟨r.2, hr⟩)
  rw [← stabilizer_e0 q] at h1
  exact h1

/-- `prop:s02-BG` (`s02-BG`): if `g⁻¹ s` fixes `c`, then `g c = s c`. -/
private theorem smul_eq_of_inv_mul_smul {X : Type*} [MulAction (SLq q) X] {c : X} {g s : SLq q}
    (h : (g⁻¹ * s) • c = c) : g • c = s • c :=
  calc g • c = g • ((g⁻¹ * s) • c) := by rw [h]
    _ = s • c := by rw [← mul_smul, mul_inv_cancel_left]

variable {d : DefiniteData} {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG` (`s02-BG`): `γ (s v) = (γ_q s) v` on vertices. -/
theorem gammaU_smul_SLq_smul_vert (γ : GammaU d q hq U) (s : SLq q) (v : Vert q) :
    γ • (s • v) = (gammaQ d q hq U γ * s) • v :=
  (mul_smul (gammaQ d q hq U γ) s v).symm

/-- `prop:s02-BG` (`s02-BG`): `γ (s e) = (γ_q s) e` on `EdgeO q`. -/
theorem gammaU_smul_SLq_smul_edgeO (γ : GammaU d q hq U) (s : SLq q) (e : EdgeO q) :
    γ • (s • e) = (gammaQ d q hq U γ * s) • e :=
  (mul_smul (gammaQ d q hq U γ) s e).symm

/-- `prop:s02-BG` (`s02-BG`): `(γ_q s) = ι_q(γ) s` in `GL₂(ℚ_q)`. -/
private theorem coe_gammaQ_mul (γ : GammaU d q hq U) (s : SLq q) :
    ((gammaQ d q hq U γ * s : SLq q) : GL (Fin 2) ℚ_[q]) =
      localComponent d q hq (iotaU d.a d.b (γ : (QuatAlg ℚ d.a d.b)ˣ)) * (s : GL (Fin 2) ℚ_[q]) :=
  rfl

/-- `prop:s02-BG` (`s02-BG`): if `s' a = γ_q (s a) k`, then `(γ_q s)⁻¹ s' = a k a⁻¹`. -/
private theorem coe_inv_mul_eq {γ : GammaU d q hq U} {s s' : SLq q} {a k : GL (Fin 2) ℚ_[q]}
    (h : (s' : GL (Fin 2) ℚ_[q]) * a = gammaQGL d q hq U γ * ((s : GL (Fin 2) ℚ_[q]) * a) * k) :
    (((gammaQ d q hq U γ * s)⁻¹ * s' : SLq q) : GL (Fin 2) ℚ_[q]) = a * k * a⁻¹ := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_gammaQ]
  have h' : (s' : GL (Fin 2) ℚ_[q]) = gammaQGL d q hq U γ * ((s : GL (Fin 2) ℚ_[q]) * a) * k * a⁻¹ :=
    eq_mul_inv_of_mul_eq h
  rw [h']
  group

end Stab

/-! ### Step 1: the cell maps are well defined -/

section Cells

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `t v₀ = s v₀` implies `[t] = [s]` in `X_B(U)`. -/
theorem mk_eq_of_smul_v0 (hU : IsQLevel d q hq U) {t s : SLq q} (h : t • v0 q = s • v0 q) :
    DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (t : GL (Fin 2) ℚ_[q])) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) := by
  have hr : (s⁻¹ * t) • v0 q = v0 q := by rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have e : (t : GL (Fin 2) ℚ_[q]) = (s : GL (Fin 2) ℚ_[q]) * ((s⁻¹ * t : SLq q) : GL (Fin 2) ℚ_[q]) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e, map_mul]
  exact mk_mul_right_mem (localEmbedGL_mem_of_isQLevel hU (mem_GL2Zl_of_smul_v0 hr))

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `t v₁ = s v₁` implies `[t α] = [s α]` in `X_B(U)`. -/
theorem mk_eq_of_smul_v1 (hU : IsQLevel d q hq U) {t s : SLq q} (h : t • v1 q = s • v1 q) :
    DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((t : GL (Fin 2) ℚ_[q]) * alphaq q)) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) := by
  have hr : (s⁻¹ * t) • v1 q = v1 q := by rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have e : (t : GL (Fin 2) ℚ_[q]) * alphaq q = (s : GL (Fin 2) ℚ_[q]) * alphaq q *
      ((alphaq q)⁻¹ * ((s⁻¹ * t : SLq q) : GL (Fin 2) ℚ_[q]) * alphaq q) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, map_mul]
  exact mk_mul_right_mem (localEmbedGL_mem_of_isQLevel hU (conj_mem_GL2Zl_of_smul_v1 hr))

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `t e₀ = s e₀` implies `[t] = [s]` in `X_B(U_0(q)U)`. -/
theorem mk_eq_of_smul_e0 (hU : IsQLevel d q hq U) {t s : SLq q} (h : t • e0 q = s • e0 q) :
    DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq (t : GL (Fin 2) ℚ_[q])) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) := by
  have hr : (s⁻¹ * t) • e0 q = e0 q := by rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have e : (t : GL (Fin 2) ℚ_[q]) = (s : GL (Fin 2) ℚ_[q]) * ((s⁻¹ * t : SLq q) : GL (Fin 2) ℚ_[q]) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e, map_mul]
  exact mk_mul_right_mem (localEmbedGL_mem_U0q hU (mem_Iw_of_smul_e0 hr))

end Cells

/-! ### The maps `phiV`, `phiE` -/

section Maps

/-- `prop:s02-BG`: the vertex map on `𝒯_q`: a type-`0` vertex `s v₀` goes to `inl [s]`, a type-`1` vertex `s v₁`
goes to `inr [s α]` (`s ∈ SL₂(ℚ_q)` chosen by `SLq_transitive_type0/1`; independent of the choice for a `q`-level,
`vertMap_type0`, `vertMap_type1`). -/
noncomputable def vertMap (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (v : Vert q) : XB U ⊕ XB U :=
  if h : vtype q v = 0 then
    Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((Classical.choose (SLq_transitive_type0 h) : SLq q) : GL (Fin 2) ℚ_[q])))
  else
    Sum.inr (DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq (((Classical.choose (SLq_transitive_type1 (zmod2_eq_one_of_ne_zero h)) : SLq q) :
        GL (Fin 2) ℚ_[q]) * alphaq q)))

/-- `prop:s02-BG`: the edge map on `𝒯_q`: an edge `s e₀` goes to `[s] ∈ X_B(U_0(q)U)` (`s` chosen by
`SLq_transitive_edge`; independent of the choice for a `q`-level, `edgeMap_type`). -/
noncomputable def edgeMap (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (e : EdgeO q) : XB (d.U0q q (coprime_of_not_dvd hq) U) :=
  DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
    (localEmbedGL d q hq ((Classical.choose (SLq_transitive_edge e) : SLq q) : GL (Fin 2) ℚ_[q]))

/-- `prop:s02-BG`: `φ = (φ₀, φ₁) : Γ_U \ V(𝒯_q) → X_B(U) ⊕ X_B(U)`, `Γ_U s v₀ ↦ inl [s]`, `Γ_U s v₁ ↦ inr [s α]`
(via a representative of the orbit; see `phiV_type0`, `phiV_type1`). The value is unspecified unless `IsQLevel`. -/
noncomputable def phiV (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q) → XB U ⊕ XB U :=
  fun o => vertMap d q hq U (Quotient.out o)

/-- `prop:s02-BG`: `φ_E : Γ_U \ E(𝒯_q) → X_B(U_0(q)U)`, `Γ_U s e₀ ↦ [s]` (via a representative; see
`phiE_type`). The value is unspecified unless `IsQLevel`. -/
noncomputable def phiE (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) :
    MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q) → XB (d.U0q q (coprime_of_not_dvd hq) U) :=
  fun o => edgeMap d q hq U (Quotient.out o)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `vertMap (s v₀) = inl [s]`. -/
theorem vertMap_type0 (hU : IsQLevel d q hq U) (s : SLq q) :
    vertMap d q hq U (s • v0 q) =
      Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]))) := by
  have h0 : vtype q (s • v0 q) = 0 := by rw [vtype_smul_SLq, vtype_v0]
  first
  | rw [vertMap, dif_pos h0]
  | (unfold vertMap; rw [dif_pos h0])
  congr 1
  exact mk_eq_of_smul_v0 hU (Classical.choose_spec (SLq_transitive_type0 h0))

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `vertMap (s v₁) = inr [s α]`. -/
theorem vertMap_type1 (hU : IsQLevel d q hq U) (s : SLq q) :
    vertMap d q hq U (s • v1 q) = Sum.inr (DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q))) := by
  have h1 : ¬ vtype q (s • v1 q) = 0 := by
    rw [vtype_smul_SLq, vtype_v1]
    decide
  first
  | rw [vertMap, dif_neg h1]
  | (unfold vertMap; rw [dif_neg h1])
  congr 1
  exact mk_eq_of_smul_v1 hU (Classical.choose_spec (SLq_transitive_type1 (zmod2_eq_one_of_ne_zero h1)))

/-- `prop:s02-BG`, Step 1 (`s02-BG`): `edgeMap (s e₀) = [s]`. -/
theorem edgeMap_type (hU : IsQLevel d q hq U) (s : SLq q) :
    edgeMap d q hq U (s • e0 q) = DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
      (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) :=
  mk_eq_of_smul_e0 hU (Classical.choose_spec (SLq_transitive_edge (s • e0 q)))

/-- `prop:s02-BG`, Step 0 (`s02-BG`): `vertMap` is `Γ_U`-invariant. -/
theorem vertMap_smul (hU : IsQLevel d q hq U) (γ : GammaU d q hq U) (v : Vert q) :
    vertMap d q hq U (γ • v) = vertMap d q hq U v := by
  have hx : iotaU d.a d.b (γ : (QuatAlg ℚ d.a d.b)ˣ) ∈ globalUnits d.a d.b := ⟨(γ : (QuatAlg ℚ d.a d.b)ˣ), rfl⟩
  rcases vert_cases v with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [gammaU_smul_SLq_smul_vert, vertMap_type0 hU, vertMap_type0 hU, coe_gammaQ_mul]
    congr 1
    exact mk_localComponent_mul hx (awayAt_mem_of_mem_GammaU γ.2) _
  · rw [gammaU_smul_SLq_smul_vert, vertMap_type1 hU, vertMap_type1 hU, coe_gammaQ_mul, mul_assoc]
    congr 1
    exact mk_localComponent_mul hx (awayAt_mem_of_mem_GammaU γ.2) _

/-- `prop:s02-BG`, Step 0 (`s02-BG`): `edgeMap` is `Γ_U`-invariant. -/
theorem edgeMap_smul (hU : IsQLevel d q hq U) (γ : GammaU d q hq U) (e : EdgeO q) :
    edgeMap d q hq U (γ • e) = edgeMap d q hq U e := by
  have hx : iotaU d.a d.b (γ : (QuatAlg ℚ d.a d.b)ˣ) ∈ globalUnits d.a d.b := ⟨(γ : (QuatAlg ℚ d.a d.b)ˣ), rfl⟩
  obtain ⟨s, rfl⟩ := SLq_transitive_edge e
  rw [gammaU_smul_SLq_smul_edgeO, edgeMap_type hU, edgeMap_type hU, coe_gammaQ_mul]
  exact mk_localComponent_mul hx
    (mem_U0q_of_localComponent_eq_one hU (awayAt_mem_of_mem_GammaU γ.2) (localComponent_awayAt _)) _

/-- `prop:s02-BG` (`s02-BG`): `φ(Γ_U v) = vertMap v` for every vertex `v`. -/
theorem phiV_mk (hU : IsQLevel d q hq U) (v : Vert q) :
    phiV d q hq U (Quotient.mk'' v) = vertMap d q hq U v := by
  obtain ⟨γ, hγ⟩ := exists_out_eq_smul (G := GammaU d q hq U) v
  show vertMap d q hq U (Quotient.out (Quotient.mk'' v : MulAction.orbitRel.Quotient (GammaU d q hq U) (Vert q))) =
    vertMap d q hq U v
  rw [hγ, vertMap_smul hU]

/-- `prop:s02-BG` (`s02-BG`): `φ_E(Γ_U e) = edgeMap e` for every edge `e`. -/
theorem phiE_mk (hU : IsQLevel d q hq U) (e : EdgeO q) :
    phiE d q hq U (Quotient.mk'' e) = edgeMap d q hq U e := by
  obtain ⟨γ, hγ⟩ := exists_out_eq_smul (G := GammaU d q hq U) e
  show edgeMap d q hq U (Quotient.out (Quotient.mk'' e : MulAction.orbitRel.Quotient (GammaU d q hq U) (EdgeO q))) =
    edgeMap d q hq U e
  rw [hγ, edgeMap_smul hU]

/-- `prop:s02-BG` (`s02-BG`): `φ₀(Γ_U s v₀) = [s]`. -/
theorem phiV_type0 (hU : IsQLevel d q hq U) (s : SLq q) :
    phiV d q hq U (Quotient.mk'' (s • v0 q)) =
      Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]))) :=
  (phiV_mk hU _).trans (vertMap_type0 hU s)

/-- `prop:s02-BG` (`s02-BG`): `φ₁(Γ_U s v₁) = [s α]`. -/
theorem phiV_type1 (hU : IsQLevel d q hq U) (s : SLq q) :
    phiV d q hq U (Quotient.mk'' (s • v1 q)) = Sum.inr (DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q))) :=
  (phiV_mk hU _).trans (vertMap_type1 hU s)

/-- `prop:s02-BG` (`s02-BG`): `φ_E(Γ_U s e₀) = [s]`. -/
theorem phiE_type (hU : IsQLevel d q hq U) (s : SLq q) :
    phiE d q hq U (Quotient.mk'' (s • e0 q)) = DoubleCoset.mk (globalUnits d.a d.b)
      (d.U0q q (coprime_of_not_dvd hq) U) (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) :=
  (phiE_mk hU _).trans (edgeMap_type hU s)

/-- `prop:s02-BG`, Step 3 (`s02-BG`): `φ` commutes with the origin: `φ(Γ_U o(e)) = inl (s₀ (φ_E (Γ_U e)))`. -/
theorem phiV_oO (hU : IsQLevel d q hq U) (e : EdgeO q) :
    phiV d q hq U (Quotient.mk'' (oO q e)) = Sum.inl (s0 d q hq U (phiE d q hq U (Quotient.mk'' e))) := by
  obtain ⟨s, rfl⟩ := SLq_transitive_edge e
  rw [oO_smul, oO_e0, phiV_type0 hU, phiE_type hU, s0_mk]

/-- `prop:s02-BG`, Step 3 (`s02-BG`): `φ` commutes with the terminus: `φ(Γ_U t(e)) = inr (s₁ (φ_E (Γ_U e)))`. -/
theorem phiV_tO (hU : IsQLevel d q hq U) (e : EdgeO q) :
    phiV d q hq U (Quotient.mk'' (tO q e)) = Sum.inr (s1 d q hq U (phiE d q hq U (Quotient.mk'' e))) := by
  obtain ⟨s, rfl⟩ := SLq_transitive_edge e
  have hα : alphaElt d q hq = localEmbedGL d q hq (alphaq q) := rfl
  rw [tO_smul, tO_e0, phiV_type1 hU, phiE_type hU, s1_mk hU, hα, ← map_mul]

end Maps

/-! ### Step 2: injectivity -/

section Injective

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG`, Step 2 (`s02-BG`): `[s] = [s']` in `X_B(U)` implies `s' v₀ ∈ Γ_U s v₀`. -/
theorem exists_gammaU_smul_v0 (hU : IsQLevel d q hq U) {s s' : SLq q}
    (h : DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s' : GL (Fin 2) ℚ_[q]))) :
    ∃ γ : GammaU d q hq U, γ • (s • v0 q) = s' • v0 q := by
  have h' : DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * 1)) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s' : GL (Fin 2) ℚ_[q]) * 1)) := by
    rw [mul_one, mul_one]
    exact h
  obtain ⟨γ, u, hu, heq⟩ := exists_gammaU_of_mk_eq hU le_rfl (det_SLq s) (det_SLq s') h'
  refine ⟨γ, ?_⟩
  rw [gammaU_smul_SLq_smul_vert]
  refine smul_eq_of_inv_mul_smul (smul_v0_of_mem ?_)
  rw [coe_inv_mul_eq heq, one_mul, inv_one, mul_one]
  exact localComponent_mem_of_isQLevel hU hu

/-- `prop:s02-BG`, Step 2 (`s02-BG`): `[s α] = [s' α]` in `X_B(U)` implies `s' v₁ ∈ Γ_U s v₁`. -/
theorem exists_gammaU_smul_v1 (hU : IsQLevel d q hq U) {s s' : SLq q}
    (h : DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s' : GL (Fin 2) ℚ_[q]) * alphaq q))) :
    ∃ γ : GammaU d q hq U, γ • (s • v1 q) = s' • v1 q := by
  obtain ⟨γ, u, hu, heq⟩ := exists_gammaU_of_mk_eq hU le_rfl (det_SLq s) (det_SLq s') h
  refine ⟨γ, ?_⟩
  rw [gammaU_smul_SLq_smul_vert]
  refine smul_eq_of_inv_mul_smul (smul_v1_of_mem ?_)
  refine mem_K1q_iff.2 ⟨Subtype.prop _, ?_⟩
  rw [coe_inv_mul_eq heq]
  refine mem_Kalpha_iff.2 ?_
  have e : (alphaq q)⁻¹ * (alphaq q * localComponent d q hq u * (alphaq q)⁻¹) * alphaq q =
      localComponent d q hq u := by group
  rw [e]
  exact localComponent_mem_of_isQLevel hU hu

/-- `prop:s02-BG`, Step 2 (`s02-BG`): `[s] = [s']` in `X_B(U_0(q)U)` implies `s' e₀ ∈ Γ_U s e₀`. -/
theorem exists_gammaU_smul_e0 (hU : IsQLevel d q hq U) {s s' : SLq q}
    (h : DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq (s' : GL (Fin 2) ℚ_[q]))) :
    ∃ γ : GammaU d q hq U, γ • (s • e0 q) = s' • e0 q := by
  have h' : DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * 1)) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq ((s' : GL (Fin 2) ℚ_[q]) * 1)) := by
    rw [mul_one, mul_one]
    exact h
  obtain ⟨γ, u, hu, heq⟩ := exists_gammaU_of_mk_eq hU (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U)
    (det_SLq s) (det_SLq s') h'
  refine ⟨γ, ?_⟩
  rw [gammaU_smul_SLq_smul_edgeO]
  refine smul_eq_of_inv_mul_smul (smul_e0_of_mem ?_)
  rw [coe_inv_mul_eq heq, one_mul, inv_one, mul_one]
  exact ((mem_U0q_iff_of_isQLevel hU).1 hu).2

/-- `prop:s02-BG`, Step 2 (`s02-BG`): `φ = (φ₀, φ₁)` is injective (the norm argument; no strong approximation). -/
theorem phiV_injective (hU : IsQLevel d q hq U) : Function.Injective (phiV d q hq U) := by
  intro o1 o2 h12
  obtain ⟨w1, rfl⟩ := Quotient.mk''_surjective o1
  obtain ⟨w2, rfl⟩ := Quotient.mk''_surjective o2
  refine Quotient.eq''.2 (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ?_))
  rcases vert_cases w1 with ⟨s1, rfl⟩ | ⟨s1, rfl⟩ <;> rcases vert_cases w2 with ⟨s2, rfl⟩ | ⟨s2, rfl⟩
  · rw [phiV_type0 hU, phiV_type0 hU] at h12
    exact exists_gammaU_smul_v0 hU (Sum.inl.inj h12).symm
  · rw [phiV_type0 hU, phiV_type1 hU] at h12
    exact absurd h12 Sum.inl_ne_inr
  · rw [phiV_type1 hU, phiV_type0 hU] at h12
    exact absurd h12 Sum.inr_ne_inl
  · rw [phiV_type1 hU, phiV_type1 hU] at h12
    exact exists_gammaU_smul_v1 hU (Sum.inr.inj h12).symm

/-- `prop:s02-BG`, Step 2 (`s02-BG`): `φ_E` is injective. -/
theorem phiE_injective (hU : IsQLevel d q hq U) : Function.Injective (phiE d q hq U) := by
  intro o1 o2 h12
  obtain ⟨e1, rfl⟩ := Quotient.mk''_surjective o1
  obtain ⟨e2, rfl⟩ := Quotient.mk''_surjective o2
  refine Quotient.eq''.2 (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ?_))
  obtain ⟨s1, rfl⟩ := SLq_transitive_edge e1
  obtain ⟨s2, rfl⟩ := SLq_transitive_edge e2
  rw [phiE_type hU, phiE_type hU] at h12
  exact exists_gammaU_smul_e0 hU h12.symm

end Injective

/-! ### Step 4: local surjectivity -/

section LocSurj

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG`, Step 4, type `0` (`s02-BG`): an edge `y` of `BG(U,q)` at `([s], 0)` is `[s t]` with
`t ∈ SL₂(ℤ_q)` (so `s t e₀` has origin `s v₀`). -/
theorem exists_edge_rep_type0 (hU : IsQLevel d q hq U) (s : SLq q) {y : XB (d.U0q q (coprime_of_not_dvd hq) U)}
    (hy : s0 d q hq U y = DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]))) :
    ∃ t : SLq q, t • v0 q = v0 q ∧
      DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * (t : GL (Fin 2) ℚ_[q]))) = y := by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective y
  have hz : DoubleCoset.mk (globalUnits d.a d.b) U z =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) :=
    (s0_mk z).symm.trans hy
  obtain ⟨x, hx, u, hu, hzu⟩ := DoubleCoset.eq.1 hz.symm
  obtain ⟨k, hk, hkI⟩ := exists_SL2Zq_inv_mul_mem_Iw (localComponent_mem_of_isQLevel hU hu)
  have hkSL : k ∈ SLq q := (mem_SL2Zq_iff.1 hk).1
  refine ⟨⟨k, hkSL⟩, smul_v0_of_mem (mem_SL2Zq_iff.1 hk).2, ?_⟩
  subst hzu
  show DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * k)) =
    DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
      (x * localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]) * u)
  have e : x * localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]) * u =
      x * (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * k) *
        (localEmbedGL d q hq (k⁻¹ * localComponent d q hq u) * awayAt d q hq u)) := by
    conv_lhs => rw [eq_localEmbedGL_mul_awayAt (hq := hq) u]
    simp only [map_mul, map_inv]
    group
  rw [e, mk_global_mul hx, mk_mul_right_mem (mul_mem (localEmbedGL_mem_U0q hU hkI) (awayAt_mem_U0q hU hu))]

/-- `prop:s02-BG`, Step 4, type `1` (`s02-BG`): an edge `y` of `BG(U,q)` at `([s α], 1)` is `[s t]` with
`t ∈ K1q = SL₂ ∩ α GL₂(ℤ_q) α⁻¹` (so `s t e₀` has terminus `s v₁`). -/
theorem exists_edge_rep_type1 (hU : IsQLevel d q hq U) (s : SLq q) {y : XB (d.U0q q (coprime_of_not_dvd hq) U)}
    (hy : s1 d q hq U y = DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q))) :
    ∃ t : SLq q, t • v1 q = v1 q ∧
      DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
        (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * (t : GL (Fin 2) ℚ_[q]))) = y := by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective y
  have hz : DoubleCoset.mk (globalUnits d.a d.b) U (z * alphaElt d q hq) =
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) :=
    (s1_mk hU z).symm.trans hy
  obtain ⟨x, hx, u, hu, hzu⟩ := DoubleCoset.eq.1 hz.symm
  have hK : alphaq q * localComponent d q hq u * (alphaq q)⁻¹ ∈ Kalpha q := by
    refine mem_Kalpha_iff.2 ?_
    have e : (alphaq q)⁻¹ * (alphaq q * localComponent d q hq u * (alphaq q)⁻¹) * alphaq q =
        localComponent d q hq u := by group
    rw [e]
    exact localComponent_mem_of_isQLevel hU hu
  obtain ⟨k, hk, hkI⟩ := exists_K1q_inv_mul_mem_Iw hK
  have hkSL : k ∈ SLq q := (mem_K1q_iff.1 hk).1
  refine ⟨⟨k, hkSL⟩, smul_v1_of_mem hk, ?_⟩
  have hz' : z = x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) * u * (alphaElt d q hq)⁻¹ :=
    eq_mul_inv_of_mul_eq hzu
  subst hz'
  show DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * k)) =
    DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
      (x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) * u * (alphaElt d q hq)⁻¹)
  have hα : alphaElt d q hq = localEmbedGL d q hq (alphaq q) := rfl
  have hc := (commute_awayAt_localEmbedGL (hp := hq) u (alphaq q)⁻¹).eq
  have e : x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) * u * (alphaElt d q hq)⁻¹ =
      x * (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * k) *
        (localEmbedGL d q hq (k⁻¹ * (alphaq q * localComponent d q hq u * (alphaq q)⁻¹)) *
          awayAt d q hq u)) := by
    calc x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) * u * (alphaElt d q hq)⁻¹
        = x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) *
            localEmbedGL d q hq (localComponent d q hq u) *
              (awayAt d q hq u * localEmbedGL d q hq (alphaq q)⁻¹) := by
          rw [hα, ← map_inv]
          conv_lhs => rw [eq_localEmbedGL_mul_awayAt (hq := hq) u]
          simp only [mul_assoc]
      _ = x * localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q) *
            localEmbedGL d q hq (localComponent d q hq u) *
              (localEmbedGL d q hq (alphaq q)⁻¹ * awayAt d q hq u) := by rw [hc]
      _ = _ := by
          simp only [map_mul, map_inv]
          group
  rw [e, mk_global_mul hx, mk_mul_right_mem (mul_mem (localEmbedGL_mem_U0q hU hkI) (awayAt_mem_U0q hU hu))]

/-- `prop:s02-BG`, Step 4 (`s02-BG`): local surjectivity at type-`0` vertices: every edge `y` of `BG(U,q)` at
`φ₀(Γ_U s v₀) = [s]` is `φ_E(Γ_U e)` for an edge `e` of `𝒯_q` with origin `s v₀`. -/
theorem phi_locSurj_type0 (hU : IsQLevel d q hq U) (s : SLq q) (y : XB (d.U0q q (coprime_of_not_dvd hq) U))
    (hy : s0 d q hq U y = DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]))) :
    ∃ e : EdgeO q, oO q e = s • v0 q ∧ phiE d q hq U (Quotient.mk'' e) = y := by
  obtain ⟨t, ht, hty⟩ := exists_edge_rep_type0 hU s hy
  refine ⟨(s * t) • e0 q, ?_, ?_⟩
  · rw [oO_smul, oO_e0, mul_smul, ht]
  · rw [phiE_type hU]
    exact hty

/-- `prop:s02-BG`, Step 4 (`s02-BG`): local surjectivity at type-`1` vertices: every edge `y` of `BG(U,q)` at
`φ₁(Γ_U s v₁) = [s α]` is `φ_E(Γ_U e)` for an edge `e` of `𝒯_q` with terminus `s v₁`. -/
theorem phi_locSurj_type1 (hU : IsQLevel d q hq U) (s : SLq q) (y : XB (d.U0q q (coprime_of_not_dvd hq) U))
    (hy : s1 d q hq U y = DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q))) :
    ∃ e : EdgeO q, tO q e = s • v1 q ∧ phiE d q hq U (Quotient.mk'' e) = y := by
  obtain ⟨t, ht, hty⟩ := exists_edge_rep_type1 hU s hy
  refine ⟨(s * t) • e0 q, ?_, ?_⟩
  · rw [tO_smul, tO_e0, mul_smul, ht]
  · rw [phiE_type hU]
    exact hty

end LocSurj

/-! ### The equivalences of `prop:s02-BG` -/

section Main

/-- `prop:s02-BG`(i): `φ₀` is surjective, i.e. every class of `X_B(U)` is `[s]` with `s ∈ SL₂(ℚ_q) = B^1_q`
(see `surjType0_iff`). -/
def surjType0 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    Prop :=
  ∀ x : XB U, ∃ s : SLq q,
    DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) = x

/-- `prop:s02-BG`: the image predicate on the vertices of `BG(U,q)`: `([x], 0)` with `x = [s]`, `([x], 1)` with
`x = [s α]` (`s ∈ SL₂(ℚ_q)`). -/
private def bgImg (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    XB U ⊕ XB U → Prop
  | Sum.inl x => ∃ s : SLq q,
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) = x
  | Sum.inr x => ∃ s : SLq q,
      DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) = x

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-BG`(i) (`s02-BG`): `surjType0` is the surjectivity of `φ₀`. -/
theorem surjType0_iff (hU : IsQLevel d q hq U) :
    surjType0 d q hq U ↔ ∀ x : XB U, ∃ o, phiV d q hq U o = Sum.inl x := by
  constructor
  · intro h x
    obtain ⟨s, rfl⟩ := h x
    exact ⟨Quotient.mk'' (s • v0 q), phiV_type0 hU s⟩
  · intro h x
    obtain ⟨o, ho⟩ := h x
    obtain ⟨w, rfl⟩ := Quotient.mk''_surjective o
    rcases vert_cases w with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [phiV_type0 hU] at ho
      exact ⟨s, Sum.inl.inj ho⟩
    · rw [phiV_type1 hU] at ho
      exact absurd ho Sum.inr_ne_inl

/-- `prop:s02-BG`(a) (`s02-BG`): (i) implies that `φ = (φ₀, φ₁)` and `φ_E` are bijective. Tree-free and SA-free:
no `Hyp.*` argument. -/
theorem bijective_of_surjType0 (hU : IsQLevel d q hq U) (h : surjType0 d q hq U) :
    Function.Bijective (phiV d q hq U) ∧ Function.Bijective (phiE d q hq U) := by
  refine ⟨⟨phiV_injective hU, ?_⟩, ⟨phiE_injective hU, ?_⟩⟩
  · rintro (x | x)
    · obtain ⟨s, rfl⟩ := h x
      exact ⟨Quotient.mk'' (s • v0 q), phiV_type0 hU s⟩
    · obtain ⟨y, rfl⟩ := Quotient.mk''_surjective x
      obtain ⟨s, hs⟩ := h (DoubleCoset.mk (globalUnits d.a d.b) U (y * (alphaElt d q hq)⁻¹))
      obtain ⟨e, -, he⟩ := phi_locSurj_type0 hU s
        (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) (y * (alphaElt d q hq)⁻¹))
        (by rw [s0_mk]; exact hs.symm)
      refine ⟨Quotient.mk'' (tO q e), ?_⟩
      rw [phiV_tO hU, he, s1_mk hU, inv_mul_cancel_right]
  · intro y
    obtain ⟨z, rfl⟩ := Quotient.mk''_surjective y
    obtain ⟨s, hs⟩ := h (DoubleCoset.mk (globalUnits d.a d.b) U z)
    obtain ⟨e, -, he⟩ := phi_locSurj_type0 hU s
      (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) z)
      (by rw [s0_mk]; exact hs.symm)
    exact ⟨_, he⟩

/-- `prop:s02-BG`, Step 5(1) (`s02-BG`): the image of `φ` is closed under adjacency in `BG(U,q)`. -/
private theorem bgImg_of_adj (hU : IsQLevel d q hq U)
    (w w' : (BG d q hq U hU).V0 ⊕ (BG d q hq U hU).V1)
    (hadj : (BG d q hq U hU).toSimpleGraph.Adj w w') (hw : bgImg d q hq U w) : bgImg d q hq U w' := by
  rw [Langlandscape.Graph.BipMultigraph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨-, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩
  · obtain ⟨s, hs⟩ := hw
    have hs' : s0 d q hq U e =
        DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) := hs.symm
    obtain ⟨t, -, hte⟩ := exists_edge_rep_type0 hU s hs'
    have hα : alphaElt d q hq = localEmbedGL d q hq (alphaq q) := rfl
    show ∃ s : SLq q, DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) = s1 d q hq U e
    refine ⟨s * t, ?_⟩
    rw [Subgroup.coe_mul, ← hte, s1_mk hU, hα, ← map_mul]
  · obtain ⟨s, hs⟩ := hw
    have hs' : s1 d q hq U e = DoubleCoset.mk (globalUnits d.a d.b) U
        (localEmbedGL d q hq ((s : GL (Fin 2) ℚ_[q]) * alphaq q)) := hs.symm
    obtain ⟨t, -, hte⟩ := exists_edge_rep_type1 hU s hs'
    show ∃ s : SLq q, DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q])) = s0 d q hq U e
    refine ⟨s * t, ?_⟩
    rw [Subgroup.coe_mul, ← hte, s0_mk]

/-- `prop:s02-BG`, (iii) ⇒ (i) (`s02-BG`): if `BG(U,q)` is connected, then `φ₀` is surjective (tree-free). -/
theorem surjType0_of_BGConnected (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    surjType0 d q hq U := by
  have key : ∀ w w' : (BG d q hq U hU).V0 ⊕ (BG d q hq U hU).V1,
      (BG d q hq U hU).toSimpleGraph.Reachable w w' →
      bgImg d q hq U w → bgImg d q hq U w' := by
    intro w w' hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hw => ih (bgImg_of_adj hU _ _ hadj hw)
  have h1 : bgImg d q hq U (Sum.inl (DoubleCoset.mk (globalUnits d.a d.b) U
      (localEmbedGL d q hq ((1 : SLq q) : GL (Fin 2) ℚ_[q])))) := by
    show ∃ s : SLq q, _ = _
    exact ⟨1, rfl⟩
  intro x
  have hc' : (BG d q hq U hU).toSimpleGraph.Connected := hc
  exact key _ (Sum.inl x) (hc'.preconnected _ (Sum.inl x)) h1

/-- `prop:s02-BG`, (iii) ⇒ the bijections (`s02-BG`): if `BG(U,q)` is connected, then `φ = (φ₀, φ₁)` and `φ_E`
are bijective, i.e. `Γ_U \ 𝒯_q ≅ BG(U,q)`. SA-free and tree-free: no `Hyp.*` argument. -/
theorem bijective_of_BGConnected (hU : IsQLevel d q hq U) (hc : BGConnected d q hq U hU) :
    Function.Bijective (phiV d q hq U) ∧ Function.Bijective (phiE d q hq U) :=
  bijective_of_surjType0 hU (surjType0_of_BGConnected hU hc)

/-- `prop:s02-BG`, (ii) ⇒ (i) (`s02-BG`): (SA_U) and the surjectivity of `X^1(U) → X_B(U)` give (i). -/
theorem surj_of_SA (hU : IsQLevel d q hq U) (hSA : SAat d q hq U)
    (hX : Function.Surjective (XBone.toXB d U)) : surjType0 d q hq U := by
  intro x
  obtain ⟨c, rfl⟩ := hX x
  obtain ⟨y, rfl⟩ := Quotient.mk''_surjective c
  obtain ⟨β, -, g, hg, u, hu, -, hy⟩ := hSA (y : (BHat d.a d.b)ˣ) y.2
  refine ⟨⟨g, MonoidHom.mem_ker.2 hg⟩, ?_⟩
  show DoubleCoset.mk (globalUnits d.a d.b) U (localEmbedGL d q hq g) = _
  rw [XBone.toXB_mk, hy, mk_mul_right_mem (Subgroup.mem_inf.1 hu).1, mk_global_mul (x := iotaU d.a d.b β) ⟨β, rfl⟩]

/-- `prop:s02-BG`, (i) ⇒ (ii) (`s02-BG`): (i) gives (SA_U) at the level `U` and the surjectivity of
`X^1(U) → X_B(U)` (tree-free). -/
theorem SA_of_surj (hU : IsQLevel d q hq U) (h : surjType0 d q hq U) :
    SAat d q hq U ∧ Function.Surjective (XBone.toXB d U) := by
  refine ⟨fun y hy => ?_, fun x => ?_⟩
  · have hy1 : nrdHat d.a d.b y = 1 := hy
    obtain ⟨s, hs⟩ := h (DoubleCoset.mk (globalUnits d.a d.b) U y)
    obtain ⟨x, hx, u, hu, hyu⟩ := DoubleCoset.eq.1 hs
    obtain ⟨β, rfl⟩ := hx
    have hyu' : y = iotaU d.a d.b β * localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]) * u := hyu
    have hn : nrdHat d.a d.b (iotaU d.a d.b β) * nrdHat d.a d.b u = 1 := by
      have h1 := congrArg (nrdHat d.a d.b) hyu'
      rw [map_mul, map_mul, nrdHat_localEmbedGL (d := d) (hq := hq) (det_SLq s), mul_one] at h1
      exact h1.symm.trans hy1
    obtain ⟨hβ1, hu1⟩ := nrd_eq_one_of_nrdHat_mul_eq_one d.ha d.hb d.O.1
      (hU.1 hu : u ∈ GL2TF.Quat.orderCompletionUnits d.O.1) β hn
    have hdet : Matrix.GeneralLinearGroup.det (localComponent d q hq u) = 1 :=
      det_localComponent_of_nrdHat hu1
    refine ⟨β, hβ1, (s : GL (Fin 2) ℚ_[q]) * localComponent d q hq u, ?_, awayAt d q hq u,
      Subgroup.mem_inf.2 ⟨awayAt_mem_of_isQLevel hU hu, ?_⟩, localComponent_awayAt u, ?_⟩
    · rw [map_mul, det_SLq s, hdet, one_mul]
    · show nrdHat d.a d.b (awayAt d q hq u) = 1
      unfold awayAt
      rw [map_mul, hu1, nrdHat_localEmbedGL (g := (localComponent d q hq u)⁻¹) (by rw [map_inv, hdet, inv_one]),
        one_mul]
    · rw [hyu', map_mul (localEmbedGL d q hq)]
      simp only [mul_assoc]
      rw [← eq_localEmbedGL_mul_awayAt]
  · obtain ⟨s, rfl⟩ := h x
    refine ⟨DoubleCoset.mk ((globalUnits d.a d.b).subgroupOf (BHatOne d)) (U.subgroupOf (BHatOne d))
      ⟨localEmbedGL d q hq (s : GL (Fin 2) ℚ_[q]), nrdHat_localEmbedGL (d := d) (hq := hq) (det_SLq s)⟩, ?_⟩
    exact XBone.toXB_mk _

/-- `prop:s02-BG`, (i) ⇒ (iii) (`s02-BG`): (i) implies that `BG(U,q)` is connected. **The only place where the
tree property enters** (`Hyp.BTtree q`: the connected tree maps onto `BG(U,q)` by (a), so `BG(U,q)` is connected). -/
theorem BGConnected_of_surj (hBT : Hyp.BTtree q) (hU : IsQLevel d q hq U) (h : surjType0 d q hq U) :
    BGConnected d q hq U hU := by
  have hsurj := (bijective_of_surjType0 hU h).1.2
  have hstep : ∀ v w : Vert q, (graph q).Adj v w →
      (BG d q hq U hU).toSimpleGraph.Adj (phiV d q hq U (Quotient.mk'' v)) (phiV d q hq U (Quotient.mk'' w)) := by
    intro v w hvw
    obtain ⟨e, he⟩ := graph_adj_iff.1 hvw
    have hadj : (BG d q hq U hU).toSimpleGraph.Adj (phiV d q hq U (Quotient.mk'' (oO q e)))
        (phiV d q hq U (Quotient.mk'' (tO q e))) := by
      rw [phiV_oO hU, phiV_tO hU]
      exact (Langlandscape.Graph.BipMultigraph.adj_inl_inr_iff (BG d q hq U hU) _ _).2
        ⟨phiE d q hq U (Quotient.mk'' e), rfl, rfl⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact hadj
    · subst h1 h2
      exact hadj.symm
  have hreach : ∀ v w : Vert q, (graph q).Reachable v w →
      (BG d q hq U hU).toSimpleGraph.Reachable (phiV d q hq U (Quotient.mk'' (v0 q)))
        (phiV d q hq U (Quotient.mk'' v)) →
      (BG d q hq U hU).toSimpleGraph.Reachable (phiV d q hq U (Quotient.mk'' (v0 q)))
        (phiV d q hq U (Quotient.mk'' w)) := by
    intro v w hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hv => ih (hv.trans (hstep _ _ hadj).reachable)
  have hall : ∀ w : (BG d q hq U hU).V0 ⊕ (BG d q hq U hU).V1,
      (BG d q hq U hU).toSimpleGraph.Reachable (phiV d q hq U (Quotient.mk'' (v0 q))) w := by
    intro w
    obtain ⟨o, ho⟩ := hsurj w
    obtain ⟨v, rfl⟩ := Quotient.mk''_surjective o
    subst ho
    exact hreach (v0 q) v (hBT.1.connected.preconnected (v0 q) v) (SimpleGraph.Reachable.refl _)
  have : Nonempty ((BG d q hq U hU).V0 ⊕ (BG d q hq U hU).V1) :=
    ⟨phiV d q hq U (Quotient.mk'' (v0 q))⟩
  show (BG d q hq U hU).toSimpleGraph.Connected
  exact SimpleGraph.Connected.mk (fun u w => (hall u).symm.trans (hall w))

/-- `prop:s02-BG`, "in particular" (`s02-BG`; export for S03-L9): strong approximation (`Hyp.SA`), Hasse–Schilling
(`Hyp.HS`) and the tree property (`Hyp.BTtree`) give the connectivity of `BG(U,q)` at every `q`-admissible level. -/
theorem BGConnected_of_SA_HS (hSA : Hyp.SA d q hq) (hHS : Hyp.HS d) (hBT : Hyp.BTtree q)
    (hU : IsQAdmissible d q hq U) : BGConnected d q hq U hU.1 :=
  BGConnected_of_surj hBT hU.1
    (surj_of_SA hU.1 (hSA U hU) (XBone_toXB_bijective hHS hU.2 hU.1.1).2)

end Main

end Langlandscape.Tree
