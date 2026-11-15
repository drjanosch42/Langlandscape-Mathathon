import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Reduction
import AlgJL.VolII.Parabolic
import AlgJL.Common.QuotientTower

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolII/TruncationCosets.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (0): none.
Dropped tagged IDs: none. -/

/-!
# Truncation, §§1–2: `T₀`, the chamber functions and the coset sums over `B(ℚ)\G(ℚ)` (M9a, units U0, U1)

Lean counterpart of `vol2/ch-06-truncation.tex` §§1–2 (items 1–6 of `docs/sprints/M9a-plan.md` §1.2). Owner: L2.

Coset type (lead, W0; D-REP). `B(ℚ)\G(ℚ)` is `borelCosets`, the quotient of `G(ℚ)` (as the subgroup `gl2RatNormOne` of
`G(𝔸)^1`; `G(ℚ) ⊆ G(𝔸)^1` by the product formula) by the left action of `B(ℚ)`, i.e. the type that
`X.quot.thm:unfolding-subgroup` produces for `Γ = G(ℚ)`, `Γ′ = B(ℚ)`. Its elements are the right cosets `B(ℚ)δ`; a
coset `d` is evaluated at its representative `Quotient.out d`. Statements about single `δ ∈ G(ℚ)` keep the M4 form
`δ : GL₂(ℚ)` acting through `ι = gl2Map (algebraMap ℚ 𝔸)`.

Item 6 is proved from M7a's `ParAux.continuous_heightMap` (W0 spike `docs/notes/M9a-decay-spike.md` §3): locally, `ht` is
squeezed between one continuous `α(H_B(δ₀x))` and a maximum of finitely many of them (finiteness from 4 (b), in the
auxiliary `GL₂(ℚ)`-coset form `TruncAux.QCosets`).
-/

open Matrix.GeneralLinearGroup Topology Filter

namespace GL2TF

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### The coset type -/

/-- `B(ℚ)` as a subgroup of `G(𝔸)^1`. -/
@[tf_aux "II.trunc.def:borel-rat-norm-one"]
noncomputable def borelRatNormOne : Subgroup normOneGroup :=
  borelRat.subgroupOf normOneGroup

theorem borelRatNormOne_le : borelRatNormOne ≤ gl2RatNormOne := by
  intro x hx
  have h : ((x : normOneGroup) : GL (Fin 2) Adele) ∈ borelRat := Subgroup.mem_subgroupOf.mp hx
  rw [borelRat_eq] at h
  exact Subgroup.mem_subgroupOf.mpr h.2

/-- `B(ℚ)` is discrete in `G(𝔸)^1` (it lies in the discrete `G(ℚ)`). -/
@[tf_aux "II.trunc.lem:borel-rat-norm-one-discrete"]
theorem borelRatNormOne_discrete : DiscreteTopology borelRatNormOne := by
  have := gl2RatNormOne_discrete
  exact discreteTopology_of_le borelRatNormOne_le

/-- `B(ℚ)\G(ℚ)`: the right cosets `B(ℚ)δ`, `δ ∈ G(ℚ)`, as the orbit quotient of `G(ℚ) ≤ G(𝔸)^1` under left
multiplication by `B(ℚ)` (the type of `X.quot.thm:unfolding-subgroup`). -/
@[tf_aux "II.trunc.def:borel-cosets"]
abbrev borelCosets : Type :=
  MulAction.orbitRel.Quotient (borelRatNormOne.subgroupOf gl2RatNormOne) gl2RatNormOne

/-- `H_B(δx)` depends only on the coset `B(ℚ)δ` (`I.decomp.thm:height-map-equivariance`). -/
@[tf_aux "II.trunc.lem:coset-height"]
theorem coset_height (x : GL (Fin 2) Adele) (δ δ' : gl2RatNormOne)
    (h : (Quotient.mk _ δ : borelCosets) = Quotient.mk _ δ') :
    heightMap (((δ : normOneGroup) : GL (Fin 2) Adele) * x) =
      heightMap (((δ' : normOneGroup) : GL (Fin 2) Adele) * x) := by
  obtain ⟨⟨β, hβ⟩, hβδ⟩ := Quotient.exact h
  have hβ' : ((β : normOneGroup) : GL (Fin 2) Adele) ∈ (borel ℚ).map (gl2Map (algebraMap ℚ Adele)) :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hβ)
  rw [← hβδ]
  show heightMap ((((β * δ' : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x) = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc, (heightMap_equivariance.2 _ hβ' _).1]

/-! ### §1 `T₀` and the chamber functions (U0) -/

namespace TruncAux

theorem heightMap_of_mem_K (k : GL (Fin 2) Adele) (hk : k ∈ maxCompactAdelic) : heightMap k = 0 := by
  simpa [ParAux.heightMap_one] using
    heightMap_equivariance.1 1 (unipotent Adele).one_mem 1 (torus Adele).one_mem 1 k hk

end TruncAux

/-- **Item 1.** The Weyl element `w ∈ G(ℚ)` and `w⁻¹` lie in `K`, and `H_B(w) = H_B(w⁻¹) = 0`. -/
@[tf_id "II.trunc.lem:weyl-height-zero"]
theorem weyl_height_zero :
    ι (weylElement ℚ) ∈ maxCompactAdelic ∧ (ι (weylElement ℚ))⁻¹ ∈ maxCompactAdelic ∧
      heightMap (ι (weylElement ℚ)) = 0 ∧ heightMap (ι (weylElement ℚ))⁻¹ = 0 := by
  have hι : ι (weylElement ℚ) = weylElement Adele := by
    apply Units.ext; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [gl2Map, weylElement, Prod.ext_iff]
  have hw := ParAux.weyl_mem_maxCompact
  rw [hι]
  exact ⟨hw, maxCompactAdelic.inv_mem hw, TruncAux.heightMap_of_mem_K _ hw,
    TruncAux.heightMap_of_mem_K _ (maxCompactAdelic.inv_mem hw)⟩

/-- **Item 2.** `T₀ ∈ 𝔞_B^G` with `H_B(w⁻¹) = T₀ − s⁻¹T₀` (`s⁻¹ = s = weylAct`) exists, is unique and is `0`. -/
@[tf_id "II.trunc.thm:t-zero"]
theorem t_zero :
    ∀ T₀ : SpaceAB, (T₀ ∈ spaceABG ∧ heightMap (ι (weylElement ℚ))⁻¹ = T₀ - weylAct T₀) ↔ T₀ = 0 := by
  intro T₀
  rw [weyl_height_zero.2.2.2]
  constructor
  · rintro ⟨hG, hw⟩
    have hs : T₀ 0 + T₀ 1 = 0 := by simpa [spaceABG] using hG
    have h0 := congrFun hw 0
    simp [weylAct] at h0
    funext i; fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨spaceABG.zero_mem, ?_⟩
    funext i; fin_cases i <;> simp [weylAct]

/-- **Item 3.** `τ_B = τ̂_B = 1_{α > 0}` on `𝔞_B`; in particular `τ_B(H − T) = τ̂_B(H − T) = 1_{α(H) > α(T)}`. -/
@[tf_id "II.trunc.lem:chamber-functions-rank-one"]
theorem chamber_functions_rank_one :
    (∀ h : SpaceAB, tauB h = tauHatB h ∧ tauB h = if 0 < simpleRoot h then 1 else 0) ∧
      ∀ H T : SpaceAB, tauB (H - T) = tauHatB (H - T) ∧
        tauB (H - T) = if simpleRoot T < simpleRoot H then 1 else 0 := by
  have h1 : ∀ h : SpaceAB, tauB h = tauHatB h ∧ tauB h = if 0 < simpleRoot h then 1 else 0 := fun h ↦ by
    by_cases hp : 0 < simpleRoot h
    · simp [tauB, tauHatB, Set.indicator, hp]
    · simp [tauB, tauHatB, Set.indicator, hp]
  refine ⟨h1, fun H T ↦ ⟨(h1 _).1, ?_⟩⟩
  simp only [(h1 _).2, map_sub, sub_pos]

/-! ### §2 Coset sums (U1) -/

/-! #### Proof plumbing for items 4–6 (untagged; the W0 spike's `GL₂(ℚ)`-coset form) -/

namespace TruncAux

/-- `B(ℚ)\GL₂(ℚ)` as the `rightRel` quotient inside `GL₂(ℚ)` (proof plumbing). -/
abbrev QCosets : Type := Quotient (QuotientGroup.rightRel (borel ℚ))

/-- `α(H_B(δx))` for one `δ ∈ GL₂(ℚ)`. -/
noncomputable def rootAt (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) : ℝ := simpleRoot (heightMap (ι δ * x))

theorem rootAt_eq (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) :
    rootAt x δ = Real.log (ideleNorm (Matrix.GeneralLinearGroup.det x)) - 2 * Real.log (bottomRowNorm (ι δ * x)) := by
  rw [rootAt, simpleRoot_heightMap, ideleNorm_det_rat_mul]

theorem rootAt_borel_mul (x : GL (Fin 2) Adele) (β δ : GL (Fin 2) ℚ) (hβ : β ∈ borel ℚ) :
    rootAt x (β * δ) = rootAt x δ := by
  rw [rootAt_eq, rootAt_eq, map_mul, mul_assoc, bottomRowNorm_borel_mul β hβ]

/-- `α(H_B(δx))` on `QCosets`. -/
noncomputable def cosetRoot (x : GL (Fin 2) Adele) : QCosets → ℝ :=
  Quotient.lift (rootAt x) fun a b (h : QuotientGroup.rightRel (borel ℚ) a b) ↦ by
    rw [QuotientGroup.rightRel_apply] at h
    have : b = (b * a⁻¹) * a := by group
    rw [this, rootAt_borel_mul x _ _ h]

theorem cosetRoot_eq_out (x : GL (Fin 2) Adele) (d : QCosets) : cosetRoot x d = rootAt x d.out := by
  conv_lhs => rw [← Quotient.out_eq d]
  rfl

theorem continuous_rootAt (δ : GL (Fin 2) ℚ) : Continuous fun x ↦ rootAt x δ :=
  simpleRoot.continuous_of_finiteDimensional.comp (ParAux.continuous_heightMap.comp (continuous_const.mul continuous_id))

theorem continuous_cosetRoot (d : QCosets) : Continuous fun x ↦ cosetRoot x d := by
  simp only [cosetRoot_eq_out]; exact continuous_rootAt _

theorem mk_eq_of_mul_inv_mem {δ δ₀ : GL (Fin 2) ℚ} (h : δ * δ₀⁻¹ ∈ borel ℚ) :
    (Quotient.mk _ δ : QCosets) = Quotient.mk _ δ₀ := by
  refine Quotient.sound ?_
  show QuotientGroup.rightRel (borel ℚ) δ δ₀
  rw [QuotientGroup.rightRel_apply]
  have : δ₀ * δ⁻¹ = (δ * δ₀⁻¹)⁻¹ := by group
  rw [this]; exact (borel ℚ).inv_mem h

theorem finite_cosets_norm_le (x : GL (Fin 2) Adele) (C : ℝ) (hC : 0 < C) :
    {d : QCosets | ∃ δ, Quotient.mk _ δ = d ∧ bottomRowNorm (ι δ * x) ≤ C}.Finite := by
  obtain ⟨F, hF⟩ := primitive_vector_finiteness x C hC
  refine ((F.finite_toSet).image (fun δ ↦ (Quotient.mk _ δ : QCosets))).subset ?_
  rintro _ ⟨δ, rfl, hδ⟩
  have : δ ∈ {δ : GL (Fin 2) ℚ | bottomRowNorm (ι δ * x) ≤ C} := hδ
  rw [hF] at this
  obtain ⟨δ₀, hδ₀, hm⟩ := Set.mem_iUnion₂.mp this
  exact ⟨δ₀, hδ₀, (mk_eq_of_mul_inv_mem hm).symm⟩

theorem norm_le_of_lt_rootAt (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) (c : ℝ) (h : c < rootAt x δ) :
    bottomRowNorm (ι δ * x) ≤ Real.exp ((Real.log (ideleNorm (Matrix.GeneralLinearGroup.det x)) - c) / 2) := by
  rw [rootAt_eq] at h
  rw [← Real.exp_log (bottomRowNorm_pos (ι δ * x))]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Item 4 (b) on `QCosets`. -/
theorem qcosets_finite_compact (Ω : Set (GL (Fin 2) Adele)) (hΩ : IsCompact Ω) (c : ℝ) :
    {d : QCosets | ∃ x ∈ Ω, c < cosetRoot x d}.Finite := by
  have hdet : Continuous fun x : GL (Fin 2) Adele ↦
      Real.exp ((Real.log (ideleNorm (Matrix.GeneralLinearGroup.det x)) - c) / 2) :=
    Real.continuous_exp.comp (((Continuous.log (ideleNorm_spec.1.comp continuous_det_gl)
      fun g ↦ (ideleNorm_spec.2.1 _).ne').sub continuous_const).div_const 2)
  have hN : Continuous fun x : GL (Fin 2) Adele ↦ adelicEntryNorm x⁻¹ :=
    continuous_adelicEntryNorm.comp continuous_inv
  obtain ⟨A, hA⟩ := (hΩ.image hdet).bddAbove
  obtain ⟨B, hB⟩ := (hΩ.image hN).bddAbove
  refine (finite_cosets_norm_le 1 (max B 1 * max A 1) (by positivity)).subset ?_
  rintro d ⟨x, hx, hd⟩
  induction d using Quotient.inductionOn with
  | h δ =>
    refine ⟨δ, rfl, ?_⟩
    have h1 := norm_le_of_lt_rootAt x δ c hd
    have h2 := bottomRowNorm_mul_le (ι δ * x) x⁻¹
    rw [mul_inv_cancel_right] at h2
    rw [mul_one]
    calc bottomRowNorm (ι δ) ≤ adelicEntryNorm x⁻¹ * bottomRowNorm (ι δ * x) := h2
      _ ≤ max B 1 * max A 1 :=
        mul_le_mul ((hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)) (h1.trans ((hA ⟨x, hx, rfl⟩).trans (le_max_left _ _)))
          (bottomRowNorm_pos _).le (by positivity)

/-- A rational matrix representing `δ ∈ G(ℚ) ≤ G(𝔸)^1`. -/
noncomputable def ratRep (δ : gl2RatNormOne) : GL (Fin 2) ℚ :=
  (Subgroup.mem_subgroupOf.mp δ.2 : ((δ : normOneGroup) : GL (Fin 2) Adele) ∈ gl2RatAdelic).choose

theorem ι_ratRep (δ : gl2RatNormOne) : ι (ratRep δ) = ((δ : normOneGroup) : GL (Fin 2) Adele) :=
  (Subgroup.mem_subgroupOf.mp δ.2 : ((δ : normOneGroup) : GL (Fin 2) Adele) ∈ gl2RatAdelic).choose_spec

/-- `G(ℚ) ≤ G(𝔸)^1` (product formula), as an element of `gl2RatNormOne`. -/
noncomputable def ratElt (δ : GL (Fin 2) ℚ) : gl2RatNormOne :=
  ⟨⟨ι δ, by
    show ideleNorm (Matrix.GeneralLinearGroup.det (ι δ)) = 1
    simpa using ideleNorm_det_rat_mul δ 1⟩, Subgroup.mem_subgroupOf.mpr ⟨δ, rfl⟩⟩

theorem ratElt_coe (δ : GL (Fin 2) ℚ) : (((ratElt δ : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) = ι δ := rfl

/-- Two elements of `G(ℚ)` with `δ'δ⁻¹ ∈ B(ℚ)` (on rational representatives) have the same coset. -/
theorem mk_eq_of_rat {δ δ' : gl2RatNormOne} {q q' : GL (Fin 2) ℚ}
    (hq : ι q = ((δ : normOneGroup) : GL (Fin 2) Adele)) (hq' : ι q' = ((δ' : normOneGroup) : GL (Fin 2) Adele))
    (h : q' * q⁻¹ ∈ borel ℚ) : (Quotient.mk _ δ : borelCosets) = Quotient.mk _ δ' := by
  refine Quotient.sound ⟨⟨δ * δ'⁻¹, ?_⟩, ?_⟩
  · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ⟨q * q'⁻¹, ?_, ?_⟩)
    · have : q * q'⁻¹ = (q' * q⁻¹)⁻¹ := by group
      rw [this]; exact (borel ℚ).inv_mem h
    · rw [map_mul, map_inv, hq, hq']; rfl
  · show δ * δ'⁻¹ * δ' = δ
    group

/-- `B(ℚ)\G(ℚ) → QCosets`, `B(ℚ)δ ↦ B(ℚ)q(δ)`. -/
noncomputable def toQ (d : borelCosets) : QCosets := Quotient.mk _ (ratRep (Quotient.out d))

theorem toQ_injective : Function.Injective toQ := by
  intro d d' h
  have h' : QuotientGroup.rightRel (borel ℚ) (ratRep (Quotient.out d)) (ratRep (Quotient.out d')) := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h'
  rw [← Quotient.out_eq d, ← Quotient.out_eq d']
  exact mk_eq_of_rat (ι_ratRep _) (ι_ratRep _) h'

theorem root_out (x : GL (Fin 2) Adele) (d : borelCosets) :
    simpleRoot (heightMap ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x)) =
      cosetRoot x (toQ d) := by
  rw [toQ, ← ι_ratRep]; rfl

theorem continuous_height : Continuous height := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨Ω, hΩc, hΩn⟩ := exists_compact_mem_nhds x₀
  have hx₀Ω : x₀ ∈ Ω := mem_of_mem_nhds hΩn
  obtain ⟨-, ⟨δ₀, hδ₀⟩, h3, -⟩ := height_attained x₀
  have hx₀ : height x₀ = cosetRoot x₀ (Quotient.mk _ δ₀) := (h3 δ₀ hδ₀).1
  have hmax : ∀ x d, cosetRoot x d ≤ height x := fun x d ↦ by
    obtain ⟨-, ⟨δ₁, hδ₁⟩, h3', -⟩ := height_attained x
    rw [cosetRoot_eq_out]
    exact (h3' δ₁ hδ₁).2.2 ⟨d.out, rfl⟩
  have hfin := qcosets_finite_compact Ω hΩc (height x₀ - 1)
  obtain ⟨S, hS⟩ : ∃ S : Finset QCosets, ∀ d, d ∈ S ↔ ∃ x ∈ Ω, height x₀ - 1 < cosetRoot x d :=
    ⟨hfin.toFinset, fun d ↦ hfin.mem_toFinset⟩
  have hne : S.Nonempty := ⟨Quotient.mk _ δ₀, (hS _).2 ⟨x₀, hx₀Ω, by rw [← hx₀]; linarith⟩⟩
  have hg : Continuous fun x ↦ max (height x₀ - 1) (S.sup' hne fun d ↦ cosetRoot x d) :=
    continuous_const.max (Continuous.finset_sup'_apply hne fun d _ ↦ continuous_cosetRoot d)
  have hup : ∀ x ∈ Ω, height x ≤ max (height x₀ - 1) (S.sup' hne fun d ↦ cosetRoot x d) := fun x hx ↦ by
    obtain ⟨-, ⟨δ₁, hδ₁⟩, h3', -⟩ := height_attained x
    have he : height x = cosetRoot x (Quotient.mk _ δ₁) := (h3' δ₁ hδ₁).1
    by_cases h : height x₀ - 1 < cosetRoot x (Quotient.mk _ δ₁)
    · exact le_max_of_le_right (he ▸ Finset.le_sup' (fun d ↦ cosetRoot x d) ((hS _).2 ⟨x, hx, h⟩))
    · exact le_max_of_le_left (he ▸ not_lt.mp h)
  have hg₀ : max (height x₀ - 1) (S.sup' hne fun d ↦ cosetRoot x₀ d) = height x₀ :=
    le_antisymm (max_le (by linarith) (Finset.sup'_le _ _ fun d _ ↦ hmax x₀ d)) (hup x₀ hx₀Ω)
  have hlo : Tendsto (fun x ↦ cosetRoot x (Quotient.mk _ δ₀)) (𝓝 x₀) (𝓝 (height x₀)) :=
    hx₀ ▸ (continuous_cosetRoot _).tendsto x₀
  have hhi : Tendsto (fun x ↦ max (height x₀ - 1) (S.sup' hne fun d ↦ cosetRoot x d)) (𝓝 x₀) (𝓝 (height x₀)) :=
    by have := hg.tendsto x₀; rwa [hg₀] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (Eventually.of_forall fun x ↦ hmax x _)
    (eventually_of_mem hΩn hup)

end TruncAux

/-- **Item 4.** `α(H_B(δx))` depends only on `B(ℚ)δ`; (a) for each `x ∈ G(𝔸)` only finitely many cosets have
`α(H_B(δx)) > c`; (b) the same uniformly for `x` in a compact `Ω ⊆ G(𝔸)`. -/
@[tf_id "II.trunc.thm:coset-sum-finite"]
theorem coset_sum_finite (c : ℝ) :
    (∀ (x : GL (Fin 2) Adele) (δ δ' : gl2RatNormOne), (Quotient.mk _ δ : borelCosets) = Quotient.mk _ δ' →
      simpleRoot (heightMap (((δ : normOneGroup) : GL (Fin 2) Adele) * x)) =
        simpleRoot (heightMap (((δ' : normOneGroup) : GL (Fin 2) Adele) * x))) ∧
    (∀ x : GL (Fin 2) Adele,
      {d : borelCosets | c < simpleRoot (heightMap
        ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x))}.Finite) ∧
    ∀ Ω : Set (GL (Fin 2) Adele), IsCompact Ω →
      {d : borelCosets | ∃ x ∈ Ω, c < simpleRoot (heightMap
        ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x))}.Finite := by
  have hb : ∀ Ω : Set (GL (Fin 2) Adele), IsCompact Ω →
      {d : borelCosets | ∃ x ∈ Ω, c < simpleRoot (heightMap
        ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x))}.Finite := fun Ω hΩ ↦ by
    refine ((TruncAux.qcosets_finite_compact Ω hΩ c).preimage TruncAux.toQ_injective.injOn).subset ?_
    rintro d ⟨x, hx, hd⟩
    exact ⟨x, hx, (TruncAux.root_out x d) ▸ hd⟩
  refine ⟨fun x δ δ' h ↦ by rw [coset_height x δ δ' h], fun x ↦ ?_, hb⟩
  refine (hb {x} isCompact_singleton).subset fun d hd ↦ ⟨x, rfl, hd⟩

/-- **Item 5.** For `x ∈ G(𝔸)^1`, `c ≥ 0` and `δ₀` with `α(H_B(δ₀x)) = ht(x)`: (a) if `ht(x) > c`, then
`α(H_B(δx)) > c ↔ δδ₀⁻¹ ∈ B(ℚ)`; (b) if `ht(x) ≤ c`, then `α(H_B(δx)) ≤ c` for all `δ`; in particular at most one
coset has `α(H_B(δx)) > c`, and one does iff `ht(x) > c`. -/
@[tf_id "II.trunc.thm:coset-sum-at-most-one"]
theorem coset_sum_at_most_one (x : normOneGroup) (c : ℝ) (hc : 0 ≤ c) (δ₀ : GL (Fin 2) ℚ)
    (hδ₀ : simpleRoot (heightMap (ι δ₀ * x)) = height x) :
    (c < height x → ∀ δ : GL (Fin 2) ℚ, c < simpleRoot (heightMap (ι δ * x)) ↔ δ * δ₀⁻¹ ∈ borel ℚ) ∧
    (height x ≤ c → ∀ δ : GL (Fin 2) ℚ, simpleRoot (heightMap (ι δ * x)) ≤ c) ∧
    {d : borelCosets | c < simpleRoot (heightMap
      ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x))}.Subsingleton ∧
    ({d : borelCosets | c < simpleRoot (heightMap
      ((((Quotient.out d : gl2RatNormOne) : normOneGroup) : GL (Fin 2) Adele) * x))}.Nonempty ↔ c < height x) := by
  have hle : ∀ δ : GL (Fin 2) ℚ, simpleRoot (heightMap (ι δ * x)) ≤ height x := fun δ ↦ by
    obtain ⟨-, ⟨δ₁, hδ₁⟩, h3, -⟩ := height_attained (x : GL (Fin 2) Adele)
    exact (h3 δ₁ hδ₁).2.2 ⟨δ, rfl⟩
  have hlog : Real.log (Real.exp c) = c := Real.log_exp c
  have hone : 1 ≤ Real.exp c := Real.one_le_exp hc
  have hlem : ∀ δ δ' : GL (Fin 2) ℚ, c < simpleRoot (heightMap (ι δ * x)) →
      c < simpleRoot (heightMap (ι δ' * x)) → δ' * δ⁻¹ ∈ borel ℚ := fun δ δ' h h' ↦
    height_lemma x x.2 _ hone δ δ' (hlog.symm ▸ h) (hlog.symm ▸ h')
  refine ⟨fun hcx δ ↦ ⟨fun h ↦ hlem δ₀ δ (hδ₀ ▸ hcx) h, fun h ↦ ?_⟩,
    fun hxc δ ↦ (hle δ).trans hxc, ?_, ⟨?_, fun hcx ↦ ?_⟩⟩
  · have : δ = (δ * δ₀⁻¹) * δ₀ := by group
    have h' := TruncAux.rootAt_borel_mul x (δ * δ₀⁻¹) δ₀ h
    rw [← this] at h'
    show c < TruncAux.rootAt x δ
    rw [h']; show c < simpleRoot (heightMap (ι δ₀ * x)); rw [hδ₀]; exact hcx
  · intro d hd d' hd'
    simp only [Set.mem_ofPred_eq, ← TruncAux.ι_ratRep] at hd hd'
    rw [← Quotient.out_eq d, ← Quotient.out_eq d']
    exact TruncAux.mk_eq_of_rat (TruncAux.ι_ratRep _) (TruncAux.ι_ratRep _) (hlem _ _ hd hd')
  · rintro ⟨d, hd⟩
    simp only [Set.mem_ofPred_eq, ← TruncAux.ι_ratRep] at hd
    exact hd.trans_le (hle _)
  · refine ⟨Quotient.mk _ (TruncAux.ratElt δ₀), ?_⟩
    show c < _
    rw [coset_height _ _ (TruncAux.ratElt δ₀) (Quotient.out_eq _), TruncAux.ratElt_coe, hδ₀]
    exact hcx

/-- **Item 6.** `ht : G(𝔸) → ℝ` is continuous; in particular so is its restriction to `G(𝔸)^1`. -/
@[tf_id "II.trunc.thm:height-continuous"]
theorem height_continuous :
    Continuous height ∧ Continuous fun x : normOneGroup ↦ height (x : GL (Fin 2) Adele) :=
  ⟨TruncAux.continuous_height, TruncAux.continuous_height.comp continuous_subtype_val⟩

end GL2TF
