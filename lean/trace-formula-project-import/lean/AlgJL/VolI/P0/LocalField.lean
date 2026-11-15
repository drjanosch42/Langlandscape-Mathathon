import AlgJL.Meta.Tag
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Units


-- algebraic_jl fork (L-A, 2026-11-14): trimmed copy of lean/GL2TF/VolI/P0/LocalField.lean @84818d0. Kept declarations are
-- byte-identical. Dropped (analytic: Haar measures, standard character, Schwartz–Bruhat, Fourier): fracPart (+ helpers),
-- stdCharPadic (+ _eq_one_iff, _isHom, _conductor), normAddHaar (+ _spec), haar_scaling, vol_ideal_power,
-- haar_modulus_linear, normMulHaar (+ _isHaarMeasure), vol_units, schwartzBruhat (+ _span), fourierLocal,
-- fourier_indicator, fourier_inversion and their untagged helpers. The normalized absolute value `normAbs` keeps its
-- definition through Mathlib's `distribHaarChar` (lead decision D-d), with its measure-theoretic proof helpers.

/-!
# The non-archimedean local field interface and ℚ_p (M1, unit U2)

Lean counterpart of `vol1/ch-0-02-local-field.tex` §1 ("The interface"). Decision D12 (alias route, after the spike
`docs/notes/M1-nalf-spike.md`): the interface is Mathlib's `IsNonarchimedeanLocalField` over unbundled
`[Field F] [ValuativeRel F] [TopologicalSpace F]`, behind the tagged alias `IsNALF`. The ring of integers, its
maximal ideal and the residue field are Mathlib's `𝒪[F]`, `𝓂[F]`, `𝓀[F]`. Owner: L1 (M1); M3 (§§2–3, U2): L2.

M3 additions (U2): the normalized absolute value `|·|_F` (D-ABS: Mathlib's `distribHaarChar` of `x ↦ ax`), additive
and multiplicative Haar measures (D13: theorems for an arbitrary Haar measure μ, the normalized measures are named
special cases), the `p`-adic fractional part, the standard character `ψ_p` and the local Fourier transform. Characters
are plain functions `F → ℂ` (their homomorphism and continuity properties are separate theorems), so that no tagged
definition value contains a proof.
-/

open Filter Topology ValuativeRel MeasureTheory
open scoped Pointwise ENNReal NNReal

namespace GL2TF.Local

/-- A non-archimedean local field: a field with a topology and a valuative relation (a valuation up to
equivalence) such that the topology is the valuation topology, the valuation is non-trivial, and the field is
locally compact. A reducible alias of Mathlib's `IsNonarchimedeanLocalField`. -/
@[tf_id "I.lf.def:nalf"]
abbrev IsNALF (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] : Prop :=
  IsNonarchimedeanLocalField F

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- `mulValuation` and the norm induce the same strict order on `ℚ_[p]` (proof helper). -/
theorem padic_mulValuation_lt_iff (x y : ℚ_[p]) :
    Padic.mulValuation x < Padic.mulValuation y ↔ ‖x‖ < ‖y‖ := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  by_cases hy : y = 0
  · simp [hy]
  by_cases hx : x = 0
  · simp [hx, hy]
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_lt_zpow_iff_right₀ hp]
  classical
  change (if x = 0 then 0 else WithZero.exp (-x.valuation)) <
    (if y = 0 then 0 else WithZero.exp (-y.valuation)) ↔ _
  rw [ite_eq_right hx, ite_eq_right hy, WithZero.exp_lt_exp]

/-- The metric topology of `ℚ_[p]` is the topology of its valuative relation. -/
@[tf_aux "I.lf.lem:padic-valuative-topology"]
instance padic_isValuativeTopology : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle (Padic.mulValuation (p := p)) fun {s} ↦ ?_
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hs⟩
    have hp1 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    have h0 : Padic.mulValuation.restrict ((p : ℚ_[p]) ^ n) ≠ 0 := by
      simp [(Fact.out : p.Prime).ne_zero]
    refine ⟨Units.mk0 _ h0, fun z hz ↦ hs ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff,
      padic_mulValuation_lt_iff, norm_pow] at hz
    simpa using hz.trans hn
  · rintro ⟨γ, hγ⟩
    obtain ⟨r, t, hr, ht, hrt⟩ := Padic.mulValuation.exists_div_eq_of_unit γ
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht
    refine ⟨‖r / t‖, by simp [hr0, ht0], fun z hz ↦ hγ ?_⟩
    simp only [Metric.mem_ball, dist_zero_right] at hz
    rw [Set.mem_ofPred_eq, ← hrt, ← map_div₀, Valuation.restrict_lt_iff, padic_mulValuation_lt_iff]
    exact hz

/-- `ℚ_[p]`, with the valuative relation of the `p`-adic valuation and its metric topology, is a
non-archimedean local field. -/
@[tf_id "I.lf.def:padic-nalf-instance"]
instance padic_isNALF : IsNALF ℚ_[p] where

/-- The Borel σ-algebra of `ℚ_[p]` (B-only plumbing; Mathlib has no measurable structure on `ℚ_[p]`). -/
@[tf_aux "I.lf.def:padic-measurable-space"]
noncomputable instance padic_measurableSpace : MeasurableSpace ℚ_[p] := borel ℚ_[p]

/-- The σ-algebra of `ℚ_[p]` is Borel (B-only plumbing). -/
@[tf_aux "I.lf.lem:padic-borel-space"]
instance padic_borelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

end Padic

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- The fixed uniformizer `ϖ_F`: an element of `𝒪[F]` generating the maximal ideal `𝓂[F]`. -/
@[tf_id "I.lf.def:uniformizer"]
noncomputable def unif : 𝒪[F] :=
  Classical.choose (show ∃ ϖ : 𝒪[F], 𝓂[F] = Ideal.span {ϖ} from
    let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    ⟨ϖ, hϖ.maximalIdeal_eq⟩)

/-- The fixed uniformizer is an irreducible element of the DVR `𝒪[F]` (proof helper). -/
theorem irreducible_unif : Irreducible (unif F) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (Classical.choose_spec (p := fun ϖ : 𝒪[F] ↦ 𝓂[F] = Ideal.span {ϖ}) _)

/-- The residue cardinality `q_F = #𝓀[F]`. -/
@[tf_id "I.lf.def:residue-cardinality"]
noncomputable def q : ℕ := Nat.card 𝓀[F]

/-- Every non-archimedean local field is second countable. -/
@[tf_id "I.lf.thm:nalf-second-countable"]
instance secondCountableTopology : SecondCountableTopology F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact secondCountable_of_proper

/-- Every non-archimedean local field is Hausdorff (B-only; same route as second countability). -/
@[tf_aux "I.lf.lem:nalf-t2"]
instance t2Space : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  exact inferInstance

/-- Every `x ∈ Fˣ` is `u ϖ^n` for exactly one pair `(u, n) ∈ 𝒪[F]ˣ × ℤ`. -/
@[tf_id "I.lf.thm:unit-uniformizer-decomposition"]
theorem unit_uniformizer_decomposition (x : F) (hx : x ≠ 0) :
    ∃! un : 𝒪[F]ˣ × ℤ, x = ((un.1 : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ un.2 := by
  have hϖ := irreducible_unif F
  have hv := Valuation.integer.integers (valuation F)
  set ϖ : 𝒪[F] := unif F
  have hϖ0 : (ϖ : F) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases Valuation.val_le_one_or_val_inv_le_one (valuation F) x with h | h
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨x, h⟩ : 𝒪[F])) (fun h0 ↦ hx (congrArg Subtype.val h0)) hϖ
      refine ⟨(u, n), ?_⟩
      simpa using congrArg Subtype.val hu
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨x⁻¹, h⟩ : 𝒪[F])) (fun h0 ↦ hx (inv_eq_zero.mp (congrArg Subtype.val h0))) hϖ
      refine ⟨(u⁻¹, -(n : ℤ)), ?_⟩
      have h' : x⁻¹ = ((u : 𝒪[F]) : F) * (ϖ : F) ^ n := by simpa using congrArg Subtype.val hu
      rw [← inv_inv x, h', mul_inv, zpow_neg, zpow_natCast]
      congr 1
      exact (eq_inv_of_mul_eq_one_left
        (by exact_mod_cast congrArg Subtype.val u.inv_mul)).symm
  · rintro ⟨u, n⟩ ⟨u', m⟩ h1 h2
    have hvu : ∀ w : 𝒪[F]ˣ, valuation F ((w : 𝒪[F]) : F) = 1 := hv.valuation_unit
    have hnm : n = m := by
      have := congrArg (valuation F) (h1.symm.trans h2)
      simp only [map_mul, map_zpow₀, hvu, one_mul] at this
      exact zpow_right_injective₀ (hv.valuation_irreducible_pos hϖ)
        (hv.valuation_irreducible_lt_one hϖ).ne this
    subst hnm
    have h3 := h1.symm.trans h2
    have h4 : ((u : 𝒪[F]) : F) = ((u' : 𝒪[F]) : F) :=
      mul_right_cancel₀ (zpow_ne_zero n hϖ0) h3
    exact Prod.ext (Units.ext (Subtype.ext h4)) rfl

/-! ### The normalized absolute value (M3, U2) -/

/-- The normalized absolute value `|a|_F`: for `a ≠ 0` the modulus of `x ↦ ax` on the additive group of `F`
(Mathlib's `distribHaarChar`, the unique `c > 0` with `μ(aE) = c μ(E)` for every additive Haar measure μ), and
`|0|_F = 0`. -/
@[tf_id "I.lf.def:normalized-abs"]
noncomputable def normAbs (a : F) : ℝ :=
  haveI := Classical.propDecidable (a = 0)
  if h : a = 0 then 0 else (distribHaarChar F (Units.mk0 a h) : ℝ)

/-- `|1|_F = 1` (proof helper). -/
theorem normAbs_one : normAbs F 1 = 1 := by
  rw [normAbs, dite_eq_right one_ne_zero, Units.mk0_one, map_one, NNReal.coe_one]

/-- `|ab|_F = |a|_F |b|_F` for `a, b ≠ 0` (proof helper). -/
theorem normAbs_mul_of_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    normAbs F (a * b) = normAbs F a * normAbs F b := by
  rw [normAbs, normAbs, normAbs, dite_eq_right (mul_ne_zero ha hb), dite_eq_right ha, dite_eq_right hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl,
    map_mul, NNReal.coe_mul]

/-- `𝒪_F` is compact (proof helper for `normAddHaar`). -/
theorem isCompact_integer : IsCompact (𝒪[F] : Set F) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

/-- `𝒪_F` has non-empty interior (proof helper for `normAddHaar`). -/
theorem interior_integer_nonempty : (interior (𝒪[F] : Set F)).Nonempty := by
  have h : IsOpen (𝒪[F] : Set F) := Valuation.isOpen_integer
  rw [h.interior_eq]
  exact ⟨0, Subring.zero_mem _⟩

/-- `𝒪_F` is open (proof helper). -/
theorem isOpen_integer : IsOpen (𝒪[F] : Set F) := Valuation.isOpen_integer

/-- `μ(aE) = |a|_F μ(E)` for every additive Haar measure and every set `E` (proof helper). -/
theorem measure_smul_normAbs [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    {a : F} (ha : a ≠ 0) (E : Set F) : μ (a • E) = ENNReal.ofReal (normAbs F a) * μ E := by
  rw [normAbs, dite_eq_right ha, ENNReal.ofReal_coe_nnreal, distribHaarChar_mul μ (Units.mk0 a ha) E]
  rfl

/-- `μ(𝒪_F) = q μ(ϖ𝒪_F)` (proof helper; `𝒪_F` is the disjoint union of `q` cosets of `ϖ𝒪_F`). -/
theorem measure_integer_eq_q_mul [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (𝒪[F] : Set F) = q F * μ (((unif F : 𝒪[F]) : F) • (𝒪[F] : Set F)) := by
  classical
  set ϖ : F := ((unif F : 𝒪[F]) : F)
  have hm : 𝓂[F] = Ideal.span {unif F} := (irreducible_unif F).maximalIdeal_eq
  set H : Set F := ϖ • (𝒪[F] : Set F)
  have hH : ∀ x : 𝒪[F], (x : F) ∈ H ↔ x ∈ 𝓂[F] := by
    intro x
    rw [hm, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp only [Subring.coe_mul]; rw [mul_comm]; exact hyx)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp only [smul_eq_mul, Subring.coe_mul, ϖ]; ring⟩
  have hHsub : H ⊆ (𝒪[F] : Set F) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subring.mul_mem _ (unif F).2 hy
  let Q := 𝓀[F]
  let mk : 𝒪[F] → Q := IsLocalRing.residue 𝒪[F]
  have hmk : Function.Surjective mk := IsLocalRing.residue_surjective
  let s : Q → 𝒪[F] := Function.surjInv hmk
  have hs : ∀ c, mk (s c) = c := Function.rightInverse_surjInv hmk
  have hmk_eq : ∀ x y : 𝒪[F], mk x = mk y ↔ x - y ∈ 𝓂[F] := fun x y ↦ by
    rw [← sub_eq_zero, ← map_sub]
    exact IsLocalRing.residue_eq_zero_iff _
  have hcover : (𝒪[F] : Set F) = ⋃ c : Q, ((s c : 𝒪[F]) : F) +ᵥ H := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · intro hx
      refine ⟨mk ⟨x, hx⟩, ((⟨x, hx⟩ - s (mk ⟨x, hx⟩) : 𝒪[F]) : F), ?_, ?_⟩
      · rw [hH, ← hmk_eq, hs]
      · simp
    · rintro ⟨c, h, hh, rfl⟩
      exact Subring.add_mem _ (s c).2 (hHsub hh)
  have hdisj : Pairwise (Function.onFun Disjoint fun c : Q ↦ ((s c : 𝒪[F]) : F) +ᵥ H) := by
    intro c c' hcc
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨h, hh, rfl⟩ ⟨h', hh', he⟩
    apply hcc
    have hh0 : h ∈ (𝒪[F] : Set F) := hHsub hh
    have hh0' : h' ∈ (𝒪[F] : Set F) := hHsub hh'
    rw [← hs c, ← hs c', hmk_eq]
    have : ((s c - s c' : 𝒪[F]) : F) = ((⟨h', hh0'⟩ - ⟨h, hh0⟩ : 𝒪[F]) : F) := by
      simp only [vadd_eq_add] at he
      push_cast
      linear_combination he.symm
    rw [Subtype.ext this, ← hH]
    push_cast
    obtain ⟨y, hy, rfl⟩ := hh
    obtain ⟨y', hy', rfl⟩ := hh'
    exact ⟨y' - y, Subring.sub_mem _ hy' hy, by simp only [smul_eq_mul]; ring⟩
  have hHm : MeasurableSet H := by
    have hϖ0 : ϖ ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
    exact ((isOpen_integer F).smul₀ hϖ0).measurableSet
  have : Fintype Q := Fintype.ofFinite Q
  rw [hcover, measure_iUnion hdisj fun c ↦ hHm.const_vadd _]
  simp only [measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [q, Nat.card_eq_fintype_card]

/-- `q_F ≥ 2` (proof helper). -/
theorem one_lt_q : 1 < q F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance

/-- `|·|_F` on `F^×` as the composite of `distribHaarChar` (proof helper). -/
theorem normAbs_eq_distribHaarChar {a : F} (ha : a ≠ 0) :
    normAbs F a = (distribHaarChar F (Units.mk0 a ha) : ℝ) := by
  rw [normAbs, dite_eq_right ha]

/-- `distribHaarChar` commutes with integer powers (proof helper). -/
theorem distribHaarChar_zpow (g : Fˣ) (n : ℤ) :
    (distribHaarChar F (g ^ n) : ℝ) = (distribHaarChar F g : ℝ) ^ n := by
  have hinv : ∀ g : Fˣ, distribHaarChar F g⁻¹ = (distribHaarChar F g)⁻¹ := fun g ↦
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  rw [map_zpow' _ hinv, NNReal.coe_zpow]

/-- `|u|_F = 1` for `u ∈ 𝒪_F^×` and `|ϖ|_F = q⁻¹` (proof helper). -/
theorem normAbs_unit_unif :
    (∀ u : 𝒪[F]ˣ, normAbs F ((u : 𝒪[F]) : F) = 1) ∧
      normAbs F ((unif F : 𝒪[F]) : F) = ((q F : ℝ))⁻¹ := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  set μ : Measure F := Measure.addHaar
  have h0 : μ (𝒪[F] : Set F) ≠ 0 :=
    ((isOpen_integer F).measure_pos μ ⟨0, Subring.zero_mem _⟩).ne'
  have hfin : μ (𝒪[F] : Set F) ≠ ⊤ := (isCompact_integer F).measure_lt_top.ne
  constructor
  · intro u
    have hu0 : ((u : 𝒪[F]) : F) ≠ 0 := fun h ↦ u.ne_zero (Subtype.ext h)
    have hset : ((u : 𝒪[F]) : F) • (𝒪[F] : Set F) = 𝒪[F] := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subring.mul_mem _ (u : 𝒪[F]).2 hy
      · intro hx
        refine ⟨((u⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * x, Subring.mul_mem _ (u⁻¹ : 𝒪[F]ˣ).1.2 hx, ?_⟩
        simp only [smul_eq_mul]
        rw [← mul_assoc]
        have : ((u : 𝒪[F]) : F) * (((u⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1 := by
          rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
        rw [this, one_mul]
    have := measure_smul_normAbs F μ hu0 (𝒪[F] : Set F)
    rw [hset] at this
    have h1 : ENNReal.ofReal (normAbs F ((u : 𝒪[F]) : F)) = 1 := by
      have := (ENNReal.mul_eq_right h0 hfin).mp this.symm
      exact this
    have hnn : 0 ≤ normAbs F ((u : 𝒪[F]) : F) := by
      rw [normAbs_eq_distribHaarChar F hu0]; exact NNReal.coe_nonneg _
    rw [← ENNReal.ofReal_one] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff hnn zero_le_one).mp h1
  · have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
    have hq0 : (q F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_q F).ne_bot
    have hqt : (q F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have h1 := measure_integer_eq_q_mul F μ
    rw [measure_smul_normAbs F μ hϖ0] at h1
    have h2 : ENNReal.ofReal (normAbs F ((unif F : 𝒪[F]) : F)) = (q F : ℝ≥0∞)⁻¹ := by
      have : (q F : ℝ≥0∞) * ENNReal.ofReal (normAbs F ((unif F : 𝒪[F]) : F)) = 1 := by
        have := (ENNReal.mul_eq_right h0 hfin).mp (h1.trans (mul_assoc _ _ _).symm).symm
        exact this
      exact (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this))
    have hnn : 0 ≤ normAbs F ((unif F : 𝒪[F]) : F) := by
      rw [normAbs_eq_distribHaarChar F hϖ0]; exact NNReal.coe_nonneg _
    have := congrArg ENNReal.toReal h2
    rwa [ENNReal.toReal_ofReal hnn, ENNReal.toReal_inv, ENNReal.toReal_natCast] at this

/-- `|uϖ^n|_F = q^{-n}` (proof helper). -/
theorem normAbs_unit_mul_unif_zpow (u : 𝒪[F]ˣ) (n : ℤ) :
    normAbs F (((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n) = (q F : ℝ) ^ (-n) := by
  have hu0 : ((u : 𝒪[F]) : F) ≠ 0 := fun h ↦ u.ne_zero (Subtype.ext h)
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  have hx0 : ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n ≠ 0 := mul_ne_zero hu0 (zpow_ne_zero _ hϖ0)
  have hsplit : Units.mk0 _ hx0 = Units.mk0 _ hu0 * Units.mk0 _ hϖ0 ^ n := Units.ext (by simp)
  obtain ⟨h1, h2⟩ := normAbs_unit_unif F
  rw [normAbs_eq_distribHaarChar F hx0, hsplit, map_mul, NNReal.coe_mul, distribHaarChar_zpow,
    ← normAbs_eq_distribHaarChar F hu0, ← normAbs_eq_distribHaarChar F hϖ0, h1 u, h2, one_mul, inv_zpow']

/-- `uϖ^n ∈ 𝒪_F ↔ n ≥ 0` (proof helper). -/
theorem unit_mul_unif_zpow_mem_integer_iff (u : 𝒪[F]ˣ) (n : ℤ) :
    ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n ∈ 𝒪[F] ↔ 0 ≤ n := by
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    -- then `ϖ⁻¹ = u⁻¹ (uϖ^n) ϖ^{-n-1} ∈ 𝒪`, so `ϖ` is a unit of `𝒪`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -n - 1 = k := ⟨(-n - 1).toNat, by omega⟩
    have hinv : ((unif F : 𝒪[F]) : F)⁻¹ ∈ 𝒪[F] := by
      have : ((unif F : 𝒪[F]) : F)⁻¹ = (((u⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) *
          (((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n) * ((unif F : 𝒪[F]) : F) ^ k := by
        have hu : (((u⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
          rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
        rw [← mul_assoc, hu, one_mul, ← zpow_natCast, ← hk, ← zpow_add₀ hϖ0]
        rw [show n + (-n - 1) = -1 by ring, zpow_neg_one]
      rw [this]
      exact Subring.mul_mem _ (Subring.mul_mem _ (u⁻¹ : 𝒪[F]ˣ).1.2 hx) (Subring.pow_mem _ (unif F).2 k)
    apply (irreducible_unif F).not_isUnit
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : 𝒪[F]) (Subtype.ext ?_)
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hϖ0
  · intro hn
    lift n to ℕ using hn
    rw [zpow_natCast]
    exact Subring.mul_mem _ (u : 𝒪[F]).2 (Subring.pow_mem _ (unif F).2 n)

/-- `|ϖ|_F = q⁻¹` and `|u|_F = 1` for `u ∈ 𝒪_F^×`; hence `|uϖ^n|_F = q^{-n}`, `|x|_F ≤ 1 ↔ x ∈ 𝒪_F` and
`|x|_F = 1 ↔ x ∈ 𝒪_F^×`. -/
@[tf_id "I.lf.thm:abs-uniformizer"]
theorem normAbs_uniformizer :
    normAbs F ((unif F : 𝒪[F]) : F) = ((q F : ℝ))⁻¹ ∧
      (∀ u : 𝒪[F]ˣ, normAbs F ((u : 𝒪[F]) : F) = 1) ∧
      (∀ (u : 𝒪[F]ˣ) (n : ℤ),
        normAbs F (((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n) = (q F : ℝ) ^ (-n)) ∧
      (∀ x : F, normAbs F x ≤ 1 ↔ x ∈ 𝒪[F]) ∧
      (∀ x : F, normAbs F x = 1 ↔ ∃ u : 𝒪[F]ˣ, ((u : 𝒪[F]) : F) = x) := by
  obtain ⟨h1, h2⟩ := normAbs_unit_unif F
  have hq : (1 : ℝ) < q F := mod_cast one_lt_q F
  refine ⟨h2, h1, normAbs_unit_mul_unif_zpow F, fun x ↦ ?_, fun x ↦ ?_⟩
  · by_cases hx : x = 0
    · simp only [hx, normAbs, dite_true, zero_le_one, true_iff]; exact Subring.zero_mem _
    obtain ⟨⟨u, n⟩, rfl, -⟩ := unit_uniformizer_decomposition F x hx
    rw [normAbs_unit_mul_unif_zpow, unit_mul_unif_zpow_mem_integer_iff, zpow_le_one_iff_right₀ hq]
    omega
  · by_cases hx : x = 0
    · simp only [hx, normAbs, dite_true, zero_ne_one, false_iff, not_exists]
      intro u hu
      exact u.ne_zero (Subtype.ext hu)
    obtain ⟨⟨u, n⟩, hxu, huniq⟩ := unit_uniformizer_decomposition F x hx
    rw [hxu, normAbs_unit_mul_unif_zpow, zpow_eq_one_iff_right₀ (by positivity) hq.ne', neg_eq_zero]
    constructor
    · rintro rfl
      exact ⟨u, by simp⟩
    · rintro ⟨v, hv⟩
      have := huniq (v, 0) (by
        show x = ((v : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ (0 : ℤ)
        rw [zpow_zero, mul_one, hv]; exact hxu)
      exact (congrArg Prod.snd this).symm

/-- `|·|_F ≥ 0` (proof helper). -/
theorem normAbs_nonneg (a : F) : 0 ≤ normAbs F a := by
  by_cases ha : a = 0
  · rw [ha, normAbs, dite_eq_left rfl]
  · rw [normAbs_eq_distribHaarChar F ha]; exact NNReal.coe_nonneg _

/-- `|uϖ^m + u'ϖ^k|_F ≤ q^{-m}` for `m ≤ k` (proof helper for the ultrametric inequality). -/
theorem normAbs_add_le_of_le (u u' : 𝒪[F]ˣ) {m k : ℤ} (hmk : m ≤ k) :
    normAbs F (((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ m + ((u' : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ k) ≤
      (q F : ℝ) ^ (-m) := by
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  set w : F := ((u : 𝒪[F]) : F) + ((u' : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ (k - m)
  have hw : w ∈ 𝒪[F] := by
    refine Subring.add_mem _ (u : 𝒪[F]).2 ?_
    have := (unit_mul_unif_zpow_mem_integer_iff F u' (k - m)).mpr (by omega)
    exact this
  have hsum : ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ m + ((u' : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ k =
      ((unif F : 𝒪[F]) : F) ^ m * w := by
    simp only [w]
    rw [mul_add, show k = m + (k - m) by ring, zpow_add₀ hϖ0, show m + (k - m) - m = k - m by ring]
    ring
  rw [hsum]
  by_cases hw0 : w = 0
  · rw [hw0, mul_zero, normAbs, dite_eq_left rfl]; positivity
  have hm : normAbs F (((unif F : 𝒪[F]) : F) ^ m) = (q F : ℝ) ^ (-m) := by
    have := normAbs_unit_mul_unif_zpow F 1 m
    simpa using this
  rw [normAbs_mul_of_ne_zero F (zpow_ne_zero _ hϖ0) hw0, hm]
  have hw1 : normAbs F w ≤ 1 := ((normAbs_uniformizer F).2.2.2.1 w).mpr hw
  calc (q F : ℝ) ^ (-m) * normAbs F w ≤ (q F : ℝ) ^ (-m) * 1 :=
        mul_le_mul_of_nonneg_left hw1 (by positivity)
    _ = _ := mul_one _

/-- `|·|_F` is multiplicative, vanishes exactly at `0`, and is ultrametric. -/
@[tf_id "I.lf.thm:abs-multiplicative"]
theorem normAbs_multiplicative (a b : F) :
    normAbs F (a * b) = normAbs F a * normAbs F b ∧ (normAbs F a = 0 ↔ a = 0) ∧
      normAbs F (a + b) ≤ max (normAbs F a) (normAbs F b) := by
  have h0 : normAbs F 0 = 0 := by rw [normAbs, dite_eq_left rfl]
  refine ⟨?_, ?_, ?_⟩
  · by_cases ha : a = 0
    · rw [ha, zero_mul, h0, zero_mul]
    by_cases hb : b = 0
    · rw [hb, mul_zero, h0, mul_zero]
    exact normAbs_mul_of_ne_zero F ha hb
  · constructor
    · intro h
      by_contra ha
      rw [normAbs_eq_distribHaarChar F ha] at h
      exact (distribHaarChar_pos (A := F) (g := Units.mk0 a ha)).ne' (NNReal.coe_eq_zero.mp h)
    · rintro rfl; exact h0
  · by_cases ha : a = 0
    · rw [ha, zero_add]; exact le_max_right _ _
    by_cases hb : b = 0
    · rw [hb, add_zero]; exact le_max_left _ _
    obtain ⟨⟨u, m⟩, rfl, -⟩ := unit_uniformizer_decomposition F a ha
    obtain ⟨⟨u', k⟩, rfl, -⟩ := unit_uniformizer_decomposition F b hb
    simp only [normAbs_unit_mul_unif_zpow]
    rcases le_total m k with hmk | hkm
    · exact (normAbs_add_le_of_le F u u' hmk).trans (le_max_left _ _)
    · rw [add_comm]
      exact (normAbs_add_le_of_le F u' u hkm).trans (le_max_right _ _)

/-- `|x|_F ≤ q^{-m} ↔ x ∈ ϖ^m 𝒪_F` (proof helper). -/
theorem normAbs_le_iff_mem (m : ℤ) (x : F) :
    normAbs F x ≤ (q F : ℝ) ^ (-m) ↔ x ∈ (((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F) := by
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  have hϖm : normAbs F (((unif F : 𝒪[F]) : F) ^ m) = (q F : ℝ) ^ (-m) := by
    simpa using normAbs_unit_mul_unif_zpow F 1 m
  have hqm : (0 : ℝ) < (q F : ℝ) ^ (-m) := zpow_pos (by exact_mod_cast (zero_lt_one.trans (one_lt_q F))) _
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (zpow_ne_zero m hϖ0), smul_eq_mul, SetLike.mem_coe,
    ← (normAbs_uniformizer F).2.2.2.1, (normAbs_multiplicative F _ _).1, ← hϖm]
  rw [show normAbs F (((unif F : 𝒪[F]) : F) ^ m)⁻¹ = (normAbs F (((unif F : 𝒪[F]) : F) ^ m))⁻¹ from by
    have := (normAbs_multiplicative F (((unif F : 𝒪[F]) : F) ^ m) (((unif F : 𝒪[F]) : F) ^ m)⁻¹).1
    rw [mul_inv_cancel₀ (zpow_ne_zero m hϖ0), normAbs_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm, hϖm, inv_mul_le_iff₀ hqm, mul_one]

/-- `|·|_F` is continuous (proof helper; it is locally constant on `F^×`). -/
theorem continuous_normAbs : Continuous (normAbs F) := by
  have hq1 : (1 : ℝ) < q F := mod_cast one_lt_q F
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  have hball : ∀ m : ℤ, {x : F | normAbs F x ≤ (q F : ℝ) ^ (-m)} ∈ 𝓝 (0 : F) := fun m ↦ by
    have : {x : F | normAbs F x ≤ (q F : ℝ) ^ (-m)} = (((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F) := by
      ext x; exact normAbs_le_iff_mem F m x
    rw [this]
    exact ((isOpen_integer F).smul₀ (zpow_ne_zero m hϖ0)).mem_nhds
      ⟨0, Subring.zero_mem _, by simp⟩
  rw [continuous_iff_continuousAt]
  intro x0
  by_cases hx0 : x0 = 0
  · subst hx0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (q F : ℝ) ^ (-(m : ℤ)) < ε := by
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq1)
      exact ⟨m, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩
    filter_upwards [hball m] with x hx
    have h0 : normAbs F 0 = 0 := by rw [normAbs, dite_eq_left rfl]
    rw [h0, Real.dist_eq, sub_zero, abs_of_nonneg (normAbs_nonneg F x)]
    exact hx.trans_lt hm
  · obtain ⟨⟨u, n⟩, rfl, -⟩ := unit_uniformizer_decomposition F x0 hx0
    set x0 := ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n
    have hx0n : normAbs F x0 = (q F : ℝ) ^ (-n) := normAbs_unit_mul_unif_zpow F u n
    have hlt : (q F : ℝ) ^ (-(n + 1)) < (q F : ℝ) ^ (-n) := zpow_lt_zpow_right₀ hq1 (by omega)
    have hev : ∀ᶠ y in 𝓝 x0, normAbs F y = normAbs F x0 := by
      have := (continuous_sub_right x0).continuousAt.preimage_mem_nhds (x := x0)
        (by show _ ∈ 𝓝 (x0 - x0); rw [sub_self]; exact hball (n + 1))
      filter_upwards [this] with y hy
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
      have hneg : normAbs F (x0 - y) = normAbs F (y - x0) := by
        rw [← neg_sub, show -(y - x0) = (-1) * (y - x0) by ring, (normAbs_multiplicative F _ _).1]
        have : normAbs F (-1 : F) = 1 := by
          have h := (normAbs_multiplicative F (-1) (-1)).1
          rw [neg_one_mul, neg_neg, normAbs_one] at h
          nlinarith [normAbs_nonneg F (-1 : F)]
        rw [this, one_mul]
      apply le_antisymm
      · calc normAbs F y = normAbs F (x0 + (y - x0)) := by ring_nf
          _ ≤ max (normAbs F x0) (normAbs F (y - x0)) := (normAbs_multiplicative F _ _).2.2
          _ = normAbs F x0 := max_eq_left (by rw [hx0n]; exact hy.trans hlt.le)
      · have := (normAbs_multiplicative F y (x0 - y)).2.2
        rw [add_sub_cancel, hneg] at this
        rcases le_max_iff.mp this with h | h
        · exact h
        · exfalso; rw [hx0n] at h; exact absurd (h.trans hy) (not_le.mpr hlt)
    exact (continuousAt_congr hev).mpr continuousAt_const

/-- `ϖ^m 𝒪_F` is compact and open (proof helper). -/
theorem unif_zpow_smul_integer_isCompact_isOpen (m : ℤ) :
    IsCompact ((((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F)) ∧
      IsOpen ((((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F)) := by
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  exact ⟨(isCompact_integer F).smul _, (isOpen_integer F).smul₀ (zpow_ne_zero m hϖ0)⟩

/-- The `ϖ^m 𝒪_F`, `m ≥ 0`, form a neighbourhood base of `0` (proof helper). -/
theorem exists_unif_pow_smul_integer_subset (U : Set F) (hU : U ∈ 𝓝 (0 : F)) :
    ∃ m : ℕ, (((unif F : 𝒪[F]) : F) ^ (m : ℤ)) • (𝒪[F] : Set F) ⊆ U := by
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.mp hU
  let t : ℕ → Set F := fun m ↦ (((unif F : 𝒪[F]) : F) ^ (m : ℤ)) • (𝒪[F] : Set F)
  have htc : ∀ m, IsClosed (t m) := fun m ↦ (unif_zpow_smul_integer_isCompact_isOpen F m).1.isClosed
  have hst : ((𝒪[F] : Set F) ∩ Vᶜ) ∩ ⋂ m, t m = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨⟨_, hxV⟩, hxt⟩ ↦ hxV ?_
    have hx0 : x = 0 := by
      have hle : ∀ m : ℕ, normAbs F x ≤ (q F : ℝ) ^ (-(m : ℤ)) := fun m ↦
        (normAbs_le_iff_mem F m x).mpr (Set.mem_iInter.mp hxt m)
      have hq1 : (1 : ℝ) < q F := mod_cast one_lt_q F
      by_contra hne
      have hpos : 0 < normAbs F x := by
        rcases (normAbs_nonneg F x).lt_or_eq with h | h
        · exact h
        · exact absurd ((normAbs_multiplicative F x x).2.1.mp h.symm) hne
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hq1)
      have := hle m
      rw [zpow_neg, zpow_natCast, ← inv_pow] at this
      linarith
    exact hx0 ▸ hV0
  have hdt : Directed (· ⊇ ·) t := by
    intro a b
    have hq : (1 : ℝ) ≤ q F := by exact_mod_cast (one_lt_q F).le
    refine ⟨max a b, ?_, ?_⟩ <;> intro x hx
    · exact (normAbs_le_iff_mem F a x).mp (((normAbs_le_iff_mem F _ x).mpr hx).trans
        (zpow_le_zpow_right₀ hq (by have := le_max_left a b; omega)))
    · exact (normAbs_le_iff_mem F b x).mp (((normAbs_le_iff_mem F _ x).mpr hx).trans
        (zpow_le_zpow_right₀ hq (by have := le_max_right a b; omega)))
  have hcpt : IsCompact ((𝒪[F] : Set F) ∩ Vᶜ) := (isCompact_integer F).inter_right hVo.isClosed_compl
  obtain ⟨m, hm⟩ := hcpt.elim_directed_family_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst) hdt
  refine ⟨m, fun x hx ↦ hVU ?_⟩
  by_contra hxV
  have hxO : x ∈ (𝒪[F] : Set F) := by
    have := (normAbs_le_iff_mem F m x).mpr hx
    exact ((normAbs_uniformizer F).2.2.2.1 x).mp (this.trans (zpow_le_one_of_nonpos₀
      (mod_cast (one_lt_q F).le) (by simp)))
  have : x ∈ ((𝒪[F] : Set F) ∩ Vᶜ) ∩ t m := ⟨⟨hxO, hxV⟩, hx⟩
  exact Set.disjoint_left.mp hm this.1 this.2

/-- `ϖ^k 𝒪_F` as the ball `|x| ≤ q^{-k}`: closed under addition, and decreasing in `k` (proof helper). -/
theorem unif_zpow_ball_add_mem {k : ℤ} {x y : F}
    (hx : x ∈ (((unif F : 𝒪[F]) : F) ^ k) • (𝒪[F] : Set F))
    (hy : y ∈ (((unif F : 𝒪[F]) : F) ^ k) • (𝒪[F] : Set F)) :
    x + y ∈ (((unif F : 𝒪[F]) : F) ^ k) • (𝒪[F] : Set F) := by
  rw [← normAbs_le_iff_mem] at hx hy ⊢
  exact ((normAbs_multiplicative F x y).2.2).trans (max_le hx hy)

theorem unif_zpow_ball_mono {k l : ℤ} (hkl : k ≤ l) {x : F}
    (hx : x ∈ (((unif F : 𝒪[F]) : F) ^ l) • (𝒪[F] : Set F)) :
    x ∈ (((unif F : 𝒪[F]) : F) ^ k) • (𝒪[F] : Set F) := by
  rw [← normAbs_le_iff_mem] at hx ⊢
  exact hx.trans (zpow_le_zpow_right₀ (by exact_mod_cast (one_lt_q F).le) (by omega))

section PadicAnalysis

variable {p : ℕ} [Fact p.Prime]

/-- `|v|_{ℚ_p} = 1` for a unit `v` of `ℤ_p` (proof helper). -/
theorem normAbs_padicInt_unit (v : ℤ_[p]ˣ) : normAbs ℚ_[p] ((v : ℤ_[p]) : ℚ_[p]) = 1 := by
  have hn : ‖((v : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.isUnit_iff.mp v.isUnit
  have hv0 : ((v : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [normAbs, dite_eq_right hv0]
  set B : Set ℚ_[p] := Metric.closedBall 0 1
  have hset : Units.mk0 _ hv0 • B = B := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [B, Units.smul_def, Metric.mem_closedBall, dist_zero_right, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul, norm_mul, norm_inv, hn, inv_one, one_mul]
  have hopen : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have h0 : (Measure.addHaar : Measure ℚ_[p]) B ≠ 0 :=
    (hopen.measure_pos _ ⟨0, by simp [B]⟩).ne'
  have hfin : (Measure.addHaar : Measure ℚ_[p]) B ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := (Measure.addHaar : Measure ℚ_[p]))
    (g := Units.mk0 _ hv0) h0 hfin (r := 1) (by rw [hset, ENNReal.coe_one, one_mul])
  rw [this, NNReal.coe_one]

/-- `ℤ_p` is the disjoint union of the `p` cosets `a + pℤ_p`, `0 ≤ a < p`, so `dx(ℤ_p) = p · dx(pℤ_p)` for every additive
Haar measure (proof helper for `normAbs_padic`). -/
theorem padic_measure_closedBall_one (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] :
    μ (Metric.closedBall 0 1) = p * μ (Metric.closedBall 0 (p : ℝ)⁻¹) := by
  set H : Set ℚ_[p] := Metric.closedBall 0 (p : ℝ)⁻¹
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
  have hcover : Metric.closedBall (0 : ℚ_[p]) 1 = ⋃ a : Fin p, ((a : ℕ) : ℚ_[p]) +ᵥ H := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add, H]
    constructor
    · intro hx
      let z : ℤ_[p] := ⟨x, hx⟩
      have hlt : ‖z - (PadicInt.zmodRepr z : ℤ_[p])‖ < 1 :=
        PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp (PadicInt.sub_zmodRepr_mem z))
      have hle : ‖z - (PadicInt.zmodRepr z : ℤ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
        rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using hlt
      refine ⟨⟨_, PadicInt.zmodRepr_lt_p z⟩, x - (PadicInt.zmodRepr z : ℚ_[p]), ?_, by ring⟩
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hle
      simpa using hle
    · rintro ⟨a, h, hh, rfl⟩
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (hh.trans hp1.le))
      exact (PadicInt.norm_le_one (a : ℤ_[p])).trans_eq' (by rw [PadicInt.norm_def, PadicInt.coe_natCast])
  have hdisj : Pairwise (Function.onFun Disjoint fun a : Fin p ↦ ((a : ℕ) : ℚ_[p]) +ᵥ H) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨h, hh, rfl⟩ ⟨h', hh', he⟩
    apply hab
    simp only [vadd_eq_add, Metric.mem_closedBall, dist_zero_right, H] at hh hh' he
    have hd : ‖(((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) : ℤ) • (1 : ℚ_[p])‖ < 1 := by
      have : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) : ℤ) • (1 : ℚ_[p]) = h' + -h := by
        rw [zsmul_eq_mul, mul_one]; push_cast; linear_combination (-1 : ℚ_[p]) * he
      rw [this]
      exact ((Padic.nonarchimedean _ _).trans (max_le hh' (by rwa [norm_neg]))).trans_lt hp1
    rw [zsmul_eq_mul, mul_one, Padic.norm_intCast_lt_one_iff] at hd
    have ha := a.2
    have hb := b.2
    apply Fin.ext
    have := Int.eq_zero_of_abs_lt_dvd hd (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
    omega
  have hHm : MeasurableSet H := Metric.isClosed_closedBall.measurableSet
  rw [hcover, measure_iUnion hdisj fun a ↦ hHm.const_vadd _]
  simp only [measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|p|_{ℚ_p} = p⁻¹` (proof helper for `normAbs_padic`). -/
theorem normAbs_padic_p : normAbs ℚ_[p] (p : ℚ_[p]) = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [normAbs, dite_eq_right hp0]
  set B : Set ℚ_[p] := Metric.closedBall 0 1
  set H : Set ℚ_[p] := Metric.closedBall 0 (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  have hset : Units.mk0 _ hp0 • B = H := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [B, H, Units.smul_def, Metric.mem_closedBall, dist_zero_right, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul, norm_mul, norm_inv, Padic.norm_p, inv_inv]
    rw [← le_div_iff₀' hpR, one_div]
  have hopen : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have h0 : (Measure.addHaar : Measure ℚ_[p]) B ≠ 0 :=
    (hopen.measure_pos _ ⟨0, by simp [B]⟩).ne'
  have hfin : (Measure.addHaar : Measure ℚ_[p]) B ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
  have hB := padic_measure_closedBall_one (p := p) (Measure.addHaar : Measure ℚ_[p])
  have hHfin : (Measure.addHaar : Measure ℚ_[p]) H ≠ ⊤ :=
    (isCompact_closedBall (0 : ℚ_[p]) _).measure_lt_top.ne
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := (Measure.addHaar : Measure ℚ_[p]))
    (g := Units.mk0 _ hp0) h0 hfin (r := (p : NNReal)⁻¹) (by
      rw [hset, hB, ENNReal.coe_inv (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), ENNReal.coe_natCast,
        ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
          (ENNReal.natCast_ne_top p), one_mul])
  rw [this, NNReal.coe_inv, NNReal.coe_natCast]

/-- On `ℚ_[p]`, the normalized absolute value is the `p`-adic norm. -/
@[tf_id "I.lf.thm:abs-padic-eq"]
theorem normAbs_padic (x : ℚ_[p]) : normAbs ℚ_[p] x = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, norm_zero, normAbs, dite_eq_left rfl]
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set v := x.valuation
  set u : ℚ_[p] := x * (p : ℚ_[p]) ^ (-v)
  have hu : ‖u‖ = 1 := by
    rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, neg_neg,
      ← zpow_add₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), neg_add_cancel, zpow_zero]
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hU : (distribHaarChar ℚ_[p] (Units.mk0 u hu0) : ℝ) = 1 := by
    have := normAbs_padicInt_unit (PadicInt.mkUnits hu)
    rwa [PadicInt.mkUnits_eq, normAbs, dite_eq_right hu0] at this
  have hP : (distribHaarChar ℚ_[p] (Units.mk0 _ hp0) : ℝ) = (p : ℝ)⁻¹ := by
    have := normAbs_padic_p (p := p)
    rwa [normAbs, dite_eq_right hp0] at this
  have hxu : Units.mk0 x hx = Units.mk0 _ hp0 ^ v * Units.mk0 u hu0 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, u]
    rw [mul_comm, mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
  have hinv : ∀ g : ℚ_[p]ˣ, distribHaarChar ℚ_[p] g⁻¹ = (distribHaarChar ℚ_[p] g)⁻¹ := fun g ↦
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  rw [normAbs, dite_eq_right hx, hxu, map_mul, map_zpow' _ hinv, NNReal.coe_mul, NNReal.coe_zpow, hU, hP, mul_one,
    Padic.norm_eq_zpow_neg_valuation hx, inv_zpow']

/-- `𝒪[ℚ_p] = ℤ_p` (proof helper). -/
theorem padic_integer_eq : (𝒪[ℚ_[p]] : Set ℚ_[p]) = PadicInt.subring p := by
  ext x
  change valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← map_one (valuation ℚ_[p]), (isEquiv (valuation ℚ_[p]) Padic.mulValuation).le_iff_le]
  rw [← not_lt, ← not_lt, padic_mulValuation_lt_iff, norm_one]

/-- `q_{ℚ_p} = p` (proof helper). -/
theorem q_padic : q ℚ_[p] = p := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hp1 : (1 : ℝ) < p := mod_cast hpp.one_lt
  set ϖ : ℚ_[p] := ((unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p])
  have hϖ0 : ϖ ≠ 0 := fun h ↦ (irreducible_unif ℚ_[p]).ne_zero (Subtype.ext h)
  have hq : ((q ℚ_[p] : ℕ) : ℝ)⁻¹ = (p : ℝ) ^ (-ϖ.valuation) := by
    rw [← (normAbs_uniformizer ℚ_[p]).1, normAbs_padic, Padic.norm_eq_zpow_neg_valuation hϖ0]
  obtain ⟨⟨u, k⟩, hpk, -⟩ := unit_uniformizer_decomposition ℚ_[p] (p : ℚ_[p]) hp0
  have h2 : (p : ℝ)⁻¹ = ((q ℚ_[p] : ℕ) : ℝ) ^ (-k) := by
    rw [← Padic.norm_p, ← normAbs_padic, hpk, normAbs_unit_mul_unif_zpow]
  have hqv : ((q ℚ_[p] : ℕ) : ℝ) = (p : ℝ) ^ ϖ.valuation := by
    rw [← inv_inv ((q ℚ_[p] : ℕ) : ℝ), hq, zpow_neg, inv_inv]
  rw [hqv, ← zpow_mul, ← zpow_neg_one] at h2
  have hvk : -1 = ϖ.valuation * -k := zpow_right_injective₀ (zero_lt_one.trans hp1) hp1.ne' h2
  have hv : 1 ≤ ϖ.valuation := by
    have hq2 : (1 : ℝ) < q ℚ_[p] := mod_cast one_lt_q ℚ_[p]
    rw [hqv] at hq2
    by_contra h
    push Not at h
    exact absurd hq2 (not_lt.mpr (zpow_le_one_of_nonpos₀ hp1.le (by omega)))
  have : ϖ.valuation = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hvk.symm with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rw [this, zpow_one] at hqv
  exact_mod_cast hqv

/-- `ϖ^n 𝒪 = p^n ℤ_p` in `ℚ_p` (proof helper). -/
theorem padic_unif_zpow_smul_integer (n : ℤ) :
    (((unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) ^ n) • (𝒪[ℚ_[p]] : Set ℚ_[p]) =
      (p : ℚ_[p]) ^ n • (PadicInt.subring p : Set ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  ext x
  rw [← normAbs_le_iff_mem, normAbs_padic, q_padic, Set.mem_smul_set_iff_inv_smul_mem₀ (zpow_ne_zero n hp0),
    smul_eq_mul]
  change _ ↔ ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-n) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [norm_mul, norm_inv, Padic.norm_p_zpow, inv_mul_le_iff₀ hpos, mul_one]

end PadicAnalysis

end GL2TF.Local
