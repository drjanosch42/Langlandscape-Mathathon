import AlgJL.Meta.Tag
import AlgJL.Common.DiscreteQuotient
import AlgJL.VolI.P0.Haar

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P0/Quotient.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (58): `adele_D_unique`, `adele_map_mul`, `automorphicQuotientMeasure`, `automorphicQuotientMeasure_invariant`, `automorphicQuotient_borelSpace`, `automorphicRightAction_spec`, `borelCoord_injective`, `borelCoord_inv`, `borelCoord_inv_mul`, `borelCoord_one`, `borelFD`, `borelFD_unique`, `borelRatB`, `borelRatB_discrete`, `borelRat_discrete`, `borelRat_le`, `borelRat_le_borel`, `borel_adele_topology`, `continuous_normHomA`, `diag_mem_borelRat`, `idelePosUnits_mul_inv`, `idele_norm_inv_comp`, `idele_posUnits_unique`, `integration_borel_quotient`, `integration_unipotent_torus_quotient`, `l2Automorphic`, `l2Automorphic_separable`, `lintegral_D_scale`, `lintegral_D_translate`, `measurableSet_borelFD`, `measurableSet_idelePosUnits`, `measurable_borelCoord_mul_quot`, `mem_borelFD`, `mem_idelePosUnits_iff`, `mem_unipotentRat_iff`, `normHomA`, `padic_unit_iff`, `ratB`, `ratB_injective`, `ratB_mem`, `ratB_surjective`, `ratIdele_eq_one_of_mem`, `ratIdele_injective`, `setLIntegral_periodic`, `torus_inv_mem`, `tsum_indicator_fd`, `unipHomeo`, `unipHomeo_add`, `unipHomeo_apply`, `unipHomeo_mem`, `unipotentMeasure_eq`, `unipotentMeasure_isHaar`, `unipotentRat_discrete`, `unipotent_fd`, `unipotent_quotient_volume`, `unipotent_topology`, `upperRight_entry`, `ur_mem_borelRat`.
Dropped tagged IDs: `I.quot.def:automorphic-quotient-measure`, `I.quot.def:l2-automorphic`, `I.quot.lem:automorphic-quotient-borel-instance`, `I.quot.lem:automorphic-quotient-invariant-instance`, `I.quot.lem:automorphic-right-action-spec`, `I.quot.thm:integration-borel-quotient`, `I.quot.thm:integration-unipotent-torus-quotient`, `I.quot.thm:l2-separable`, `I.quot.thm:unipotent-quotient-volume`. -/

/-!
# Discrete quotients of G(𝔸), unfolding and L² (M3, unit U9)

Lean counterpart of `vol1/ch-0-07-quotient.tex` §§1–4 (D-QUOT). Owner: L1. Quotients by discrete subgroups are
`MulAction.orbitRel.Quotient Γ G` with the quotient measure `GL2TF.quotientMeasure` of `Common/DiscreteQuotient`.
-/

open MeasureTheory Matrix.GeneralLinearGroup
open scoped ENNReal

namespace GL2TF

/-! ### `N(ℚ)\N(𝔸)` -/

/-- `N(ℚ) = {n(q) : q ∈ ℚ}` as a subgroup of `N(𝔸)`. -/
@[tf_aux "I.quot.def:unipotent-rat"]
noncomputable def unipotentRat : Subgroup (unipotent Adele) :=
  ((unipotent ℚ).map (gl2Map (algebraMap ℚ Adele))).subgroupOf (unipotent Adele)

section Unip

/-- `n : 𝔸 → N(𝔸)` as an isomorphism of topological groups. -/
noncomputable def unipotentEquiv (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Multiplicative R ≃ₜ* unipotent R where
  toFun x := ⟨upperRightHom x.toAdd, x.toAdd, rfl⟩
  invFun n := Multiplicative.ofAdd (((n : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1)
  left_inv x := by simp
  right_inv n := by
    obtain ⟨_, y, rfl⟩ := n
    exact Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [toAdd_mul, AddChar.map_add_eq_mul])
  continuous_toFun := (continuous_upperRightHom_adelic.comp continuous_toAdd).subtype_mk _
  continuous_invFun := continuous_ofAdd.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 1)

theorem unipotentEquiv_apply (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (x : R) :
    ((unipotentEquiv R (Multiplicative.ofAdd x) : unipotent R) : GL (Fin 2) R) = upperRightHom x := rfl

end Unip

/-! ### `T(ℚ)\T(𝔸)^1` -/

/-- `T(ℚ) = {diag(q₁, q₂) : q₁, q₂ ∈ ℚ^×}` as a subgroup of `T(𝔸)^1`. -/
@[tf_aux "I.quot.def:torus-rat"]
noncomputable def torusRat : Subgroup torusNormOne :=
  ((ratIdeles.prod ratIdeles).map (diagHom Adele)).subgroupOf torusNormOne

section TorusCoord

variable {R : Type*} [CommRing R]

/-- The `i`-th diagonal entry of `g ∈ T(R)`, as a unit. -/
def torusEntry (i : Fin 2) (g : torus R) : Rˣ where
  val := ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i i
  inv := (((g⁻¹ : torus R) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i i
  val_inv := by
    have h := congrArg (fun m : torus R ↦ ((m : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i i) (mul_inv_cancel g)
    have h1 := g.2
    have h2 := (g⁻¹).2
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Subgroup.coe_one,
      Units.val_one] at h
    fin_cases i <;> simp_all [torus]
  inv_val := by
    have h := congrArg (fun m : torus R ↦ ((m : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i i) (inv_mul_cancel g)
    have h1 := g.2
    have h2 := (g⁻¹).2
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Subgroup.coe_one,
      Units.val_one] at h
    fin_cases i <;> simp_all [torus]

theorem torus_ext {g h : GL (Fin 2) R} (hg : g ∈ torus R) (hh : h ∈ torus R)
    (h0 : (g : Matrix (Fin 2) (Fin 2) R) 0 0 = (h : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) R) 1 1 = (h : Matrix (Fin 2) (Fin 2) R) 1 1) : g = h := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j
  · exact h0
  · simp [hg.1, hh.1]
  · simp [hg.2, hh.2]
  · exact h1

theorem diagElt_injective {t₁ t₂ s₁ s₂ : Rˣ} (h : diagElt t₁ t₂ = diagElt s₁ s₂) : t₁ = s₁ ∧ t₂ = s₂ := by
  have h0 := congrArg (fun m : GL (Fin 2) R ↦ (m : Matrix (Fin 2) (Fin 2) R) 0 0) h
  have h1 := congrArg (fun m : GL (Fin 2) R ↦ (m : Matrix (Fin 2) (Fin 2) R) 1 1) h
  exact ⟨Units.ext (by simpa [diagElt] using h0), Units.ext (by simpa [diagElt] using h1)⟩

theorem diagElt_torusEntry (g : torus R) :
    diagElt (torusEntry 0 g) (torusEntry 1 g) = (g : GL (Fin 2) R) :=
  torus_ext (diagElt_mem_torus _ _) g.2 (by simp [diagElt, torusEntry]) (by simp [diagElt, torusEntry])

theorem torusEntry_diagElt (t₁ t₂ : Rˣ) :
    torusEntry 0 ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ = t₁ ∧
      torusEntry 1 ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ = t₂ :=
  ⟨Units.ext (by simp [diagElt, torusEntry]), Units.ext (by simp [diagElt, torusEntry])⟩

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_torusEntry (i : Fin 2) : Continuous (torusEntry (R := R) i) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i i
  · exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_inv (G := torus R)))).matrix_elem i i

end TorusCoord

section TorusNormOne

theorem torusNormOne_le : torusNormOne ≤ torus Adele := by
  rintro _ ⟨t, -, rfl⟩
  exact diagElt_mem_torus t.1 t.2

theorem torusNormOne_entry_mem (g : torusNormOne) (i : Fin 2) :
    torusEntry i ⟨g, torusNormOne_le g.2⟩ ∈ ideleNormOne := by
  obtain ⟨g, ⟨t₁, t₂⟩, ⟨h₁, h₂⟩, rfl⟩ := g
  have := torusEntry_diagElt t₁ t₂
  fin_cases i
  · show torusEntry 0 ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ ∈ _
    rw [this.1]; exact h₁
  · show torusEntry 1 ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ ∈ _
    rw [this.2]; exact h₂

/-- `T(𝔸)^1 ≅ 𝔸^1 × 𝔸^1`. -/
noncomputable def torusNormOneEquiv : ideleNormOne × ideleNormOne ≃ₜ* torusNormOne where
  toFun t := ⟨diagElt (t.1 : Idele) (t.2 : Idele), ((t.1 : Idele), (t.2 : Idele)), ⟨t.1.2, t.2.2⟩, rfl⟩
  invFun g := (⟨_, torusNormOne_entry_mem g 0⟩, ⟨_, torusNormOne_entry_mem g 1⟩)
  left_inv t := by
    obtain ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ := t
    have := torusEntry_diagElt t₁ t₂
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  right_inv g := Subtype.ext (diagElt_torusEntry ⟨g, torusNormOne_le g.2⟩)
  map_mul' s t := Subtype.ext (diagElt_hom.2 _ _ _ _)
  continuous_toFun := (continuous_diagElt.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  continuous_invFun :=
    (((continuous_torusEntry 0).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _).prodMk
      (((continuous_torusEntry 1).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _)

theorem torusNormOneEquiv_apply (t : ideleNormOne × ideleNormOne) :
    (torusNormOneEquiv t : GL (Fin 2) Adele) = diagElt (t.1 : Idele) (t.2 : Idele) := rfl

theorem torusNormOneEquiv_mem_iff (t : ideleNormOne × ideleNormOne) :
    torusNormOneEquiv t ∈ torusRat ↔ (t.1 : Idele) ∈ ratIdeles ∧ (t.2 : Idele) ∈ ratIdeles := by
  simp only [torusRat, Subgroup.mem_subgroupOf, torusNormOneEquiv_apply, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    obtain ⟨h1, h2⟩ := diagElt_injective hst
    exact ⟨h1 ▸ hs.1, h2 ▸ hs.2⟩
  · intro h; exact ⟨((t.1 : Idele), (t.2 : Idele)), h, rfl⟩

theorem torusRat_discrete : DiscreteTopology torusRat := by
  have := gl2Rat_discrete.2.2
  have hmem : ∀ x : torusRat, ((x : torusNormOne) : GL (Fin 2) Adele) ∈ gl2RatAdelic := by
    rintro ⟨x, hx⟩
    rw [torusRat, Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
    obtain ⟨⟨s₁, s₂⟩, ⟨⟨q₁, rfl⟩, ⟨q₂, rfl⟩⟩, hs⟩ := hx
    exact ⟨diagElt q₁ q₂, by rw [gl2Map_diagElt, ← hs]; rfl⟩
  refine DiscreteTopology.of_continuous_injective (f := fun x : torusRat ↦ (⟨x.1.1, hmem x⟩ : gl2RatAdelic))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
  intro x y h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem normOneClass_eq (e : (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) ≃* Idele)
    (he : ∀ (q : ℚˣ) (r : Units.posSubgroup ℝ) (u : Zhatˣ), e (q, r, u) = ratIdele q * ideleInfFin ((r : ℝˣ) : ℝ) u)
    (t : ideleNormOne) :
    (QuotientGroup.mk t : NormOneClassGroup) = zhatToNormOneClass (e.symm t).2.2 := by
  set x := e.symm (t : Idele) with hx
  have ht : (t : Idele) = ratIdele x.1 * ideleInfFin ((x.2.1 : ℝˣ) : ℝ) x.2.2 := by
    rw [← he, hx, MulEquiv.apply_symm_apply]
  have hpos : (0 : ℝ) < ((x.2.1 : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).mp x.2.1.2
  have hr : ((x.2.1 : ℝˣ) : ℝ) = 1 := by
    have hn : ideleNorm (t : Idele) = 1 := t.2
    rw [ht, map_mul, product_formula, one_mul, ideleNorm_ideleInfFin hpos.ne', abs_of_pos hpos] at hn
    exact hn
  unfold zhatToNormOneClass
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [ht, hr, mul_inv_rev, mul_comm (ideleInfFin 1 x.2.2)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  exact ⟨x.1⁻¹, map_inv _ _⟩

variable (e₁ : Zhatˣ ≃ₜ* NormOneClassGroup)

/-- `T(𝔸)^1 → Ẑ^× × Ẑ^×`, `diag(t₁, t₂) ↦ (u(t₁), u(t₂))`. -/
noncomputable def torusUnitsHom : torusNormOne →* Zhatˣ × Zhatˣ :=
  ((e₁.symm.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' (ratIdeles.subgroupOf ideleNormOne))).prodMap
    (e₁.symm.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' (ratIdeles.subgroupOf ideleNormOne)))).comp
    torusNormOneEquiv.symm.toMulEquiv.toMonoidHom

theorem torusUnitsHom_apply (g : torusNormOne) :
    torusUnitsHom e₁ g = (e₁.symm (QuotientGroup.mk (torusNormOneEquiv.symm g).1),
      e₁.symm (QuotientGroup.mk (torusNormOneEquiv.symm g).2)) := rfl

theorem continuous_torusUnitsHom : Continuous (torusUnitsHom e₁) := by
  have hq : Continuous (QuotientGroup.mk : ideleNormOne → NormOneClassGroup) := continuous_quot_mk
  exact (((e₁.symm.continuous.comp hq).comp continuous_fst).prodMk
    ((e₁.symm.continuous.comp hq).comp continuous_snd)).comp torusNormOneEquiv.symm.continuous

theorem isOpenMap_torusUnitsHom : IsOpenMap (torusUnitsHom e₁) := by
  have hq : IsOpenMap (QuotientGroup.mk : ideleNormOne → NormOneClassGroup) := QuotientGroup.isOpenMap_coe
  have h1 : IsOpenMap (fun x : ideleNormOne ↦ e₁.symm (QuotientGroup.mk x)) :=
    e₁.symm.toHomeomorph.isOpenMap.comp hq
  exact (h1.prodMap h1).comp torusNormOneEquiv.symm.toHomeomorph.isOpenMap

theorem surjective_torusUnitsHom : Function.Surjective (torusUnitsHom e₁) := by
  intro ⟨u₁, u₂⟩
  obtain ⟨t₁, ht₁⟩ := QuotientGroup.mk_surjective (e₁ u₁)
  obtain ⟨t₂, ht₂⟩ := QuotientGroup.mk_surjective (e₁ u₂)
  refine ⟨torusNormOneEquiv (t₁, t₂), ?_⟩
  rw [torusUnitsHom_apply, ContinuousMulEquiv.symm_apply_apply]
  simp only [ht₁, ht₂, ContinuousMulEquiv.symm_apply_apply]

theorem ker_torusUnitsHom : (torusUnitsHom e₁).ker = torusRat := by
  ext g
  obtain ⟨t, rfl⟩ := torusNormOneEquiv.surjective g
  rw [MonoidHom.mem_ker, torusUnitsHom_apply, ContinuousMulEquiv.symm_apply_apply, torusNormOneEquiv_mem_iff,
    Prod.mk_eq_one, map_eq_one_iff _ e₁.symm.injective, map_eq_one_iff _ e₁.symm.injective,
    QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]

end TorusNormOne

/-- `T(ℚ)` is a discrete subgroup of `T(𝔸)^1`; `diag(t₁, t₂) ↦ (t₁, t₂)` is an isomorphism of topological groups
`T(𝔸)^1 ≅ 𝔸^1 × 𝔸^1` carrying `T(ℚ)` onto `ℚ^× × ℚ^×`; for the decomposition `e` of
`I.adele.thm:idele-decomposition`, `diag(t₁, t₂) ↦ (u(t₁), u(t₂))` induces a homeomorphism
`T(ℚ)\T(𝔸)^1 ≅ Ẑ^× × Ẑ^×` (multiplicative by its formula); in particular `T(ℚ)\T(𝔸)^1` is compact. -/
@[tf_id "I.quot.thm:torus-quotient-compact"]
theorem torus_quotient_compact (e : (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) ≃* Idele)
    (he : ∀ (q : ℚˣ) (r : Units.posSubgroup ℝ) (u : Zhatˣ),
      e (q, r, u) = ratIdele q * ideleInfFin ((r : ℝˣ) : ℝ) u) :
    DiscreteTopology torusRat ∧
      (∃ φ : ideleNormOne × ideleNormOne ≃ₜ* torusNormOne,
        (∀ t, (φ t : GL (Fin 2) Adele) = diagElt (t.1 : Idele) (t.2 : Idele)) ∧
          ∀ t, φ t ∈ torusRat ↔ (t.1 : Idele) ∈ ratIdeles ∧ (t.2 : Idele) ∈ ratIdeles) ∧
      (∃ ψ : MulAction.orbitRel.Quotient torusRat torusNormOne ≃ₜ Zhatˣ × Zhatˣ,
        ∀ (t₁ t₂ : Idele) (h : diagElt t₁ t₂ ∈ torusNormOne),
          ψ (Quotient.mk _ ⟨diagElt t₁ t₂, h⟩) = ((e.symm t₁).2.2, (e.symm t₂).2.2)) ∧
      CompactSpace (MulAction.orbitRel.Quotient torusRat torusNormOne) := by
  obtain ⟨⟨e₁, he₁⟩, hcpt⟩ := norm_one_quotient
  have hdisc := torusRat_discrete
  have hfib : ∀ a b : torusNormOne, torusUnitsHom e₁ a = torusUnitsHom e₁ b ↔
      Quotient.mk (MulAction.orbitRel torusRat torusNormOne) a = Quotient.mk _ b := by
    intro a b
    rw [quot_mk_eq_iff']
    constructor
    · intro h
      refine ⟨⟨a * b⁻¹, ?_⟩, by simp⟩
      rw [← ker_torusUnitsHom e₁, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    · rintro ⟨γ, rfl⟩
      have hγ : (γ : torusNormOne) ∈ (torusUnitsHom e₁).ker := by rw [ker_torusUnitsHom]; exact γ.2
      rw [map_mul, MonoidHom.mem_ker.mp hγ, one_mul]
  let ψ₀ : MulAction.orbitRel.Quotient torusRat torusNormOne → Zhatˣ × Zhatˣ :=
    Quotient.lift (torusUnitsHom e₁) fun a b hab ↦ (hfib a b).mpr (Quotient.sound hab)
  have hinj : Function.Injective ψ₀ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective y
    exact (hfib a b).mp hxy
  have hsurj : Function.Surjective ψ₀ := fun u ↦ by
    obtain ⟨g, hg⟩ := surjective_torusUnitsHom e₁ u
    exact ⟨Quotient.mk _ g, hg⟩
  have hcont : Continuous ψ₀ := (continuous_torusUnitsHom e₁).quotient_lift _
  have hopen : IsOpenMap ψ₀ := fun U hU ↦ by
    have : ψ₀ '' U = torusUnitsHom e₁ '' (Quotient.mk _ ⁻¹' U) := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
        exact ⟨g, hx, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, rfl⟩
    rw [this]
    exact isOpenMap_torusUnitsHom e₁ _ (hU.preimage continuous_quot_mk)
  let ψ := (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen
  have hZ : CompactSpace Zhatˣ := e₁.toHomeomorph.symm.compactSpace
  refine ⟨hdisc, ⟨torusNormOneEquiv, torusNormOneEquiv_apply, torusNormOneEquiv_mem_iff⟩, ⟨ψ, ?_⟩,
    ψ.symm.compactSpace⟩
  intro t₁ t₂ h
  obtain ⟨s, ⟨hs₁, hs₂⟩, hs⟩ := h
  obtain ⟨h1, h2⟩ := diagElt_injective hs
  have hg : (⟨diagElt t₁ t₂, ⟨s, ⟨hs₁, hs₂⟩, hs⟩⟩ : torusNormOne) =
      torusNormOneEquiv (⟨t₁, h1 ▸ hs₁⟩, ⟨t₂, h2 ▸ hs₂⟩) := Subtype.ext rfl
  show torusUnitsHom e₁ _ = _
  rw [hg, torusUnitsHom_apply, ContinuousMulEquiv.symm_apply_apply]
  simp only
  rw [normOneClass_eq e he, normOneClass_eq e he, ← he₁, ← he₁, ContinuousMulEquiv.symm_apply_apply,
    ContinuousMulEquiv.symm_apply_apply]

/-! ### `B(ℚ)\G(𝔸)` -/

/-- `B(ℚ) ≤ G(𝔸)`, the image of `B(ℚ) ≤ GL₂(ℚ)`. -/
@[tf_aux "I.quot.def:borel-rat"]
noncomputable def borelRat : Subgroup (GL (Fin 2) Adele) :=
  (borel ℚ).map (gl2Map (algebraMap ℚ Adele))

/-- `ℝ_{>0} × Ẑ^× = {x ∈ 𝔸^× : x_∞ > 0, x_p ∈ ℤ_p^× for all p}`. -/
@[tf_aux "I.quot.def:idele-pos-units"]
def idelePosUnits : Set Idele :=
  {x | 0 < (x : Adele).1 ∧ ∀ p : Nat.Primes, ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = (x : Adele).2 p}

/-! ### Proof infrastructure for `I.quot.thm:integration-borel-quotient` (untagged) -/

section L1BorelQuot

open Set Topology
open scoped NNReal

theorem borelRat_eq : borelRat = borel Adele ⊓ gl2RatAdelic := by
  ext g
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨?_, γ, rfl⟩
    show ((gl2Map (algebraMap ℚ Adele) γ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 0 = 0
    have : ((γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := hγ
    simp [gl2Map, Matrix.GeneralLinearGroup.map, this]
  · rintro ⟨hb, γ, rfl⟩
    refine ⟨γ, ?_, rfl⟩
    have hb' : ((gl2Map (algebraMap ℚ Adele) γ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 0 = 0 := hb
    simp only [gl2Map, Matrix.GeneralLinearGroup.map_apply] at hb'
    show ((γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
    exact algebraMap_adele_diagonal.1 (by rw [hb', map_zero])

end L1BorelQuot

/-! ### `G(ℚ)\G(𝔸)^1` -/

/-- `G(ℚ)` as a subgroup of `G(𝔸)^1`. -/
@[tf_aux "I.quot.def:gl2-rat-norm-one"]
noncomputable def gl2RatNormOne : Subgroup normOneGroup :=
  gl2RatAdelic.subgroupOf normOneGroup

/-- The quotient of a locally compact, Hausdorff, second countable group by a discrete subgroup is locally compact,
Hausdorff and second countable. -/
theorem orbitQuotient_topology {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] :
    LocallyCompactSpace (MulAction.orbitRel.Quotient Γ G) ∧ T2Space (MulAction.orbitRel.Quotient Γ G) ∧
      SecondCountableTopology (MulAction.orbitRel.Quotient Γ G) := by
  have : ProperlyDiscontinuousSMul Γ G :=
    Γ.properlyDiscontinuousSMul_of_tendsto_cofinite (tendsto_cofinite_of_discrete Γ)
  exact ⟨MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace, inferInstance,
    ContinuousConstSMul.secondCountableTopology⟩

theorem normOneGroup_topology :
    LocallyCompactSpace normOneGroup ∧ T2Space normOneGroup ∧ SecondCountableTopology normOneGroup := by
  have := gl2Adelic_locallyCompact.1.2.2
  exact ⟨normOneGroup_closed_normal.1.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance,
    TopologicalSpace.Subtype.secondCountableTopology _⟩

/-- `G(ℚ)` is a discrete subgroup of `G(𝔸)^1` (B-only claim of `I.quot.def:automorphic-quotient-measure`). -/
@[tf_aux "I.quot.lem:gl2-rat-norm-one-discrete"]
theorem gl2RatNormOne_discrete : DiscreteTopology gl2RatNormOne := by
  have := gl2Rat_discrete.2.2
  refine DiscreteTopology.of_continuous_injective (f := fun x : gl2RatNormOne ↦ (⟨x.1.1, x.2⟩ : gl2RatAdelic))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
  intro x y h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

/-- `G(ℚ)\G(𝔸)^1` is locally compact, Hausdorff and second countable. -/
@[tf_id "I.quot.thm:automorphic-quotient-second-countable"]
theorem automorphicQuotient_secondCountable :
    LocallyCompactSpace (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) ∧
      T2Space (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) ∧
      SecondCountableTopology (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  have := gl2RatNormOne_discrete
  exact orbitQuotient_topology gl2RatNormOne

/-! ### The right action of `G(𝔸)^1` on `G(ℚ)\G(𝔸)^1` (M4, unit U8) -/

/-- `G(ℚ)x ↦ G(ℚ)xg` respects `G(ℚ)`-orbits (proof plumbing). -/
theorem automorphicRightAction_wd (g : normOneGroup) (x y : normOneGroup)
    (h : MulAction.orbitRel gl2RatNormOne normOneGroup x y) :
    MulAction.orbitRel gl2RatNormOne normOneGroup (x * g) (y * g) := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ, ?_⟩
  rw [← hγ]
  show (γ : normOneGroup) * (y * g) = (γ : normOneGroup) * y * g
  rw [mul_assoc]

/-- The right action `(G(ℚ)x)·g = G(ℚ)xg` of `G(𝔸)^1` on `G(ℚ)\G(𝔸)^1`, written as a left action of
`(G(𝔸)^1)ᵐᵒᵖ`. -/
@[tf_id "I.quot.def:automorphic-right-action"]
noncomputable instance automorphicRightAction :
    MulAction normOneGroupᵐᵒᵖ (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) where
  smul g := Quotient.map' (· * g.unop) (automorphicRightAction_wd g.unop)
  one_smul q := Quotient.inductionOn' q fun x ↦ by
    show Quotient.mk'' (x * 1) = Quotient.mk'' x
    rw [mul_one]
  mul_smul g h q := Quotient.inductionOn' q fun x ↦ by
    show Quotient.mk'' (x * (h.unop * g.unop)) = Quotient.mk'' (x * h.unop * g.unop)
    rw [mul_assoc]


/-- The right action is continuous, as an instance (B-only plumbing for `I.quot.def:automorphic-right-action`).
Fork note: the parent proves this as `automorphicRightAction_spec.2.1`; the spec (which also contains the measure
invariance) is dropped, so its measure-free continuity argument is inlined here verbatim. -/
@[tf_aux "I.quot.lem:automorphic-right-action-continuous-instance"]
instance automorphicRightAction_continuousSMul :
    ContinuousSMul normOneGroupᵐᵒᵖ (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  have := gl2RatNormOne_discrete
  refine ⟨?_⟩
  have hq : IsOpenQuotientMap (Prod.map (id : normOneGroupᵐᵒᵖ → normOneGroupᵐᵒᵖ)
      (Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup))) :=
    IsOpenQuotientMap.id.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [hq.isQuotientMap.continuous_iff]
  show Continuous fun p : normOneGroupᵐᵒᵖ × normOneGroup ↦
    Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) (p.2 * p.1.unop)
  exact continuous_quotient_mk'.comp (continuous_snd.mul (MulOpposite.continuous_unop.comp continuous_fst))

end GL2TF
