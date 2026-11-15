import AlgJL.VolII.Centralizer
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolII/Centralizer.lean` at commit 84818d0. Dropped tests of stripped declarations (5): `gammaI_volume_finite`, `gammaSqrt2_volume_finite`, `compact_quotient_volume_gammaSqrt2`, `compact_quotient_volume_intReal`, `quotientMeasure_intReal_univ`. -/


/-!
# Tests for `GL2TF.VolII.Centralizer`

Witnesses for the tagged definitions and the exit witnesses of `II.orb.thm:elliptic-centralizer-compact` and
`II.orb.thm:elliptic-volume-finite` (M3e W1, statement level). Non-degenerate parameters (M4-SC-2 lesson):
`γ_i = (0 −1; 1 0)` (`E = ℚ(i)`, finite unit group) and `γ_√2 = (0 2; 1 0)` (`E = ℚ(√2)`, infinite unit group);
negative control `diag(2, 1)` (not elliptic).
-/

open GL2TF MeasureTheory Polynomial
open scoped ENNReal

namespace GL2TFTests

/-- `γ_i = (0 −1; 1 0) ∈ GL₂(ℚ)`, characteristic polynomial `X² + 1`. -/
def gammaI : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by norm_num [Matrix.det_fin_two])

/-- `γ_√2 = (0 2; 1 0) ∈ GL₂(ℚ)`, characteristic polynomial `X² − 2`. -/
def gammaSqrt2 : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 2; 1, 0] (by norm_num [Matrix.det_fin_two])

/-- `diag(2, 1) ∈ GL₂(ℚ)`, characteristic polynomial `(X − 2)(X − 1)`. -/
def diagTwoOne : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 0; 0, 1] (by norm_num [Matrix.det_fin_two])

/-- The characteristic polynomial of a `2 × 2` matrix has degree `2`. -/
theorem charpoly_natDegree_two (γ : GL (Fin 2) ℚ) :
    (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) ℚ)).natDegree ∈ Finset.Icc 1 3 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; decide

/-- `P_γ(x) = x² − tr(γ) x + det γ`. -/
theorem charpoly_eval_two (γ : GL (Fin 2) ℚ) (x : ℚ) :
    (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) ℚ)).eval x =
      x ^ 2 - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℚ) * x + Matrix.det (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [Matrix.charpoly_fin_two]; simp

/-- `γ_i` is elliptic (`X² + 1` has no rational root). -/
theorem gammaI_isElliptic : IsElliptic gammaI := by
  refine irreducible_of_degree_le_three_of_not_isRoot (charpoly_natDegree_two _) fun x hx ↦ ?_
  rw [IsRoot, charpoly_eval_two] at hx
  simp [gammaI, Matrix.trace_fin_two, Matrix.det_fin_two] at hx
  nlinarith [sq_nonneg x]

/-- `γ_√2` is elliptic (`X² − 2` has no rational root, `√2` is irrational). -/
theorem gammaSqrt2_isElliptic : IsElliptic gammaSqrt2 := by
  refine irreducible_of_degree_le_three_of_not_isRoot (charpoly_natDegree_two _) fun x hx ↦ ?_
  rw [IsRoot, charpoly_eval_two] at hx
  have hx2 : x ^ 2 = 2 := by
    simp [gammaSqrt2, Matrix.trace_fin_two, Matrix.det_fin_two] at hx
    linarith
  have hx' : ((x : ℝ)) ^ 2 = 2 := by exact_mod_cast hx2
  refine irrational_sqrt_two ⟨|x|, ?_⟩
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, hx']

/-- Negative control: `diag(2, 1)` is not elliptic (`1` is a root of `P`). -/
theorem diagTwoOne_not_isElliptic : ¬ IsElliptic diagTwoOne := by
  intro h
  have hroot : (Matrix.charpoly (diagTwoOne : Matrix (Fin 2) (Fin 2) ℚ)).IsRoot 1 := by
    rw [IsRoot, charpoly_eval_two]
    norm_num [diagTwoOne, Matrix.trace_fin_two, Matrix.det_fin_two]
  have hdeg : (Matrix.charpoly (diagTwoOne : Matrix (Fin 2) (Fin 2) ℚ)).natDegree ≠ 1 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; decide
  exact Irreducible.not_isRoot_of_natDegree_ne_one h hdeg hroot

/-! ### Witnesses for the tagged definitions -/

/-- `γ_i ∈ G(ℚ) ⊆ G(𝔸)^1`. -/
theorem gammaI_mem_normOneGroup : gl2Map (algebraMap ℚ Adele) gammaI ∈ normOneGroup :=
  norm_one_splitting.2 ⟨gammaI, rfl⟩

/-- `ι(γ_i) ∈ G_{γ_i}(𝔸)`. -/
theorem gammaI_mem_centralizerGL : gl2Map (algebraMap ℚ Adele) gammaI ∈ centralizerGL Adele gammaI :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

/-- `ι(γ_i)` is not central in `G(𝔸)` (so `G_{γ_i}(𝔸) ≠ G(𝔸)` contains a non-central element). -/
theorem gammaI_adelic_not_mem_center : gl2Map (algebraMap ℚ Adele) gammaI ∉ center Adele := by
  rintro ⟨z, hz⟩
  have h := congrArg (fun g : GL (Fin 2) Adele ↦ (g : Matrix (Fin 2) (Fin 2) Adele) 0 1) hz
  simp [gammaI, gl2Map, Matrix.GeneralLinearGroup.map] at h
  have h1 := congrArg Prod.fst h
  norm_num at h1

/-- `ι(γ_i) ∈ G_{γ_i}(𝔸)^1`. -/
theorem gammaI_mem_centralizerNormOne :
    (⟨gl2Map (algebraMap ℚ Adele) gammaI, gammaI_mem_normOneGroup⟩ : normOneGroup) ∈ centralizerNormOne gammaI :=
  Subgroup.mem_subgroupOf.mpr gammaI_mem_centralizerGL

/-- `ι(γ_i) ∈ G_{γ_i}(ℚ) ⊆ G_{γ_i}(𝔸)^1`. -/
theorem gammaI_mem_centralizerRatNormOne :
    (⟨⟨gl2Map (algebraMap ℚ Adele) gammaI, gammaI_mem_normOneGroup⟩, gammaI_mem_centralizerNormOne⟩ :
      centralizerNormOne gammaI) ∈ centralizerRatNormOne gammaI :=
  Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ⟨gammaI, rfl⟩)

/-! ### Exit witnesses (fully applied) -/

/-- `II.orb.thm:elliptic-centralizer-compact` for `γ_i`. -/
theorem gammaI_centralizer_compact :
    CompactSpace (MulAction.orbitRel.Quotient (centralizerRatNormOne gammaI) (centralizerNormOne gammaI)) :=
  elliptic_centralizer_compact gammaI gammaI_isElliptic

/-- `II.orb.thm:elliptic-centralizer-compact` for `γ_√2` (infinite unit group). -/
theorem gammaSqrt2_centralizer_compact :
    CompactSpace (MulAction.orbitRel.Quotient (centralizerRatNormOne gammaSqrt2) (centralizerNormOne gammaSqrt2)) :=
  elliptic_centralizer_compact gammaSqrt2 gammaSqrt2_isElliptic

section SplitControl

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### Negative control: the split element `diag(2, 1)` (G1 follow-up m2/m4) -/

/-- `x_t = (diag(t, t⁻¹), 1) ∈ G(𝔸)^1`, `t > 0`. -/
noncomputable def diagTwoOneTorus (t : ℝ) : GL (Fin 2) Adele :=
  diagElt (ideleInfFin t 1) (ideleInfFin t⁻¹ 1)

theorem diagTwoOneTorus_mem_normOneGroup (t : ℝ) (ht : 0 < t) : diagTwoOneTorus t ∈ normOneGroup := by
  show ideleNorm (Matrix.GeneralLinearGroup.det (diagTwoOneTorus t)) = 1
  have : Matrix.GeneralLinearGroup.det (diagTwoOneTorus t) = ideleInfFin t 1 * ideleInfFin t⁻¹ 1 := by
    apply Units.ext
    simp [diagTwoOneTorus, diagElt, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rw [this, map_mul, ideleNorm_ideleInfFin ht.ne' 1, ideleNorm_ideleInfFin (inv_ne_zero ht.ne') 1,
    abs_of_pos ht, abs_of_pos (inv_pos.mpr ht), mul_inv_cancel₀ ht.ne']

theorem diagTwoOneTorus_height (t : ℝ) (ht : 0 < t) : simpleRoot (heightMap (diagTwoOneTorus t)) = 2 * Real.log t := by
  rw [diagTwoOneTorus, heightMap_diag, ideleNorm_ideleInfFin ht.ne' 1, ideleNorm_ideleInfFin (inv_ne_zero ht.ne') 1,
    abs_of_pos ht, abs_of_pos (inv_pos.mpr ht), Real.log_inv]
  simp [simpleRoot]; ring

theorem diagTwoOneTorus_comm (t : ℝ) : diagTwoOneTorus t * ι diagTwoOne = ι diagTwoOne * diagTwoOneTorus t := by
  apply Units.ext
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagTwoOneTorus, diagElt, diagTwoOne, gl2Map, Matrix.GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (rw [Prod.mk_zero_zero, mul_zero, zero_mul]) | ring

/-- `II.orb.lem:elliptic-height-bound` fails for the split `diag(2, 1)` and `Ω = {diag(2, 1)}`: the ellipticity
hypothesis is needed (kernel-checked negative control). -/
theorem height_bound_fails_diagTwoOne :
    ¬ ∃ c : ℝ, ∀ δ : GL (Fin 2) ℚ, ∀ x : normOneGroup,
      (x : GL (Fin 2) Adele)⁻¹ * ι diagTwoOne * x ∈ ({ι diagTwoOne} : Set (GL (Fin 2) Adele)) →
        simpleRoot (heightMap (ι δ * x)) ≤ c := by
  rintro ⟨c, hc⟩
  have ht : 0 < Real.exp (|c| + 1) := Real.exp_pos _
  have h := hc 1 ⟨diagTwoOneTorus _, diagTwoOneTorus_mem_normOneGroup _ ht⟩ (by
    show (diagTwoOneTorus _)⁻¹ * ι diagTwoOne * diagTwoOneTorus _ = ι diagTwoOne
    rw [mul_assoc, ← diagTwoOneTorus_comm, ← mul_assoc, inv_mul_cancel, one_mul])
  simp only [map_one, one_mul] at h
  rw [diagTwoOneTorus_height _ ht, Real.log_exp] at h
  linarith [le_abs_self c, abs_nonneg c]

/-- `II.orb.cor:centralizer-height-bound` fails for `diag(2, 1)`. -/
theorem centralizer_height_bound_fails_diagTwoOne :
    ¬ ∃ c : ℝ, ∀ x : centralizerNormOne diagTwoOne, ∀ δ : GL (Fin 2) ℚ,
      simpleRoot (heightMap (ι δ * ((x : normOneGroup) : GL (Fin 2) Adele))) ≤ c := by
  rintro ⟨c, hc⟩
  have ht : 0 < Real.exp (|c| + 1) := Real.exp_pos _
  have hmem : (⟨diagTwoOneTorus _, diagTwoOneTorus_mem_normOneGroup _ ht⟩ : normOneGroup) ∈ centralizerNormOne diagTwoOne :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (diagTwoOneTorus_comm _))
  have h := hc ⟨_, hmem⟩ 1
  simp only [map_one, one_mul] at h
  rw [diagTwoOneTorus_height _ ht, Real.log_exp] at h
  linarith [le_abs_self c, abs_nonneg c]

set_option synthInstance.maxHeartbeats 200000 in
/-- For every `γ`, compactness of `G_γ(ℚ)\G_γ(𝔸)^1` forces the height bound on `G_γ(𝔸)^1` (via the compactness
criterion `I.red.thm:compactness-criterion`). -/
theorem height_bound_of_compact (γ : GL (Fin 2) ℚ)
    (h : CompactSpace (MulAction.orbitRel.Quotient (centralizerRatNormOne γ) (centralizerNormOne γ))) :
    ∃ c : ℝ, ∀ x : centralizerNormOne γ, ∀ δ : GL (Fin 2) ℚ,
      simpleRoot (heightMap (ι δ * ((x : normOneGroup) : GL (Fin 2) Adele))) ≤ c := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  obtain ⟨-, hT2, -⟩ := automorphicQuotient_secondCountable
  have hopen : IsOpenMap (Quotient.mk (MulAction.orbitRel (centralizerRatNormOne γ) (centralizerNormOne γ))) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨C', hC', hcov⟩ := exists_compact_image_superset hopen Quotient.mk_surjective isCompact_univ
  set Ω := Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) '' (Subtype.val '' C')
  have hΩ : IsCompact Ω := (hC'.image continuous_subtype_val).image continuous_quotient_mk'
  obtain ⟨c, hc⟩ := (compactness_criterion Ω).mp (by rwa [hΩ.isClosed.closure_eq])
  refine ⟨c, fun x δ ↦ hc _ ?_ δ⟩
  obtain ⟨w, hw, hwx⟩ := hcov (Set.mem_univ (Quotient.mk _ x))
  obtain ⟨σ, hσ⟩ := (quot_mk_eq_iff' _).mp hwx.symm
  refine ⟨(w : normOneGroup), ⟨w, hw, rfl⟩, ((quot_mk_eq_iff' gl2RatNormOne).mpr
    ⟨⟨(σ : centralizerNormOne γ), Subgroup.mem_subgroupOf.mp σ.2⟩, ?_⟩).symm⟩
  rw [← hσ]; rfl

/-- Negative control for `II.orb.thm:elliptic-centralizer-compact`: for the split `γ = diag(2, 1)`,
`G_γ(ℚ)\G_γ(𝔸)^1` is **not** compact. -/
theorem diagTwoOne_centralizer_not_compact :
    ¬ CompactSpace (MulAction.orbitRel.Quotient (centralizerRatNormOne diagTwoOne) (centralizerNormOne diagTwoOne)) :=
  fun h ↦ centralizer_height_bound_fails_diagTwoOne (height_bound_of_compact diagTwoOne h)

end SplitControl

section IntReal

/-! ### `ℤ ⊂ ℝ`: a witness of `X.quot.thm:compact-quotient-volume` independent of M3e (G1 follow-up m4) -/

/-- The Borel σ-algebra of `ℝ` on `Multiplicative ℝ` (the multiplicative notation for the additive group `ℝ`). -/
@[reducible] noncomputable def multRealMeasurableSpace : MeasurableSpace (Multiplicative ℝ) :=
  (inferInstance : MeasurableSpace ℝ)

attribute [local instance] multRealMeasurableSpace

theorem multReal_borelSpace : BorelSpace (Multiplicative ℝ) := inferInstanceAs (BorelSpace ℝ)

attribute [local instance] multReal_borelSpace

theorem multReal_secondCountable : SecondCountableTopology (Multiplicative ℝ) :=
  inferInstanceAs (SecondCountableTopology ℝ)

attribute [local instance] multReal_secondCountable

theorem measurable_multReal_ofAdd : Measurable (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) := fun _ hs ↦ hs

/-- Lebesgue measure on `Multiplicative ℝ`. -/
noncomputable def multRealVolume : Measure (Multiplicative ℝ) := Measure.map Multiplicative.ofAdd volume

theorem multRealVolume_apply (s : Set (Multiplicative ℝ)) (hs : MeasurableSet s) :
    multRealVolume s = volume (Multiplicative.ofAdd ⁻¹' s) :=
  Measure.map_apply measurable_multReal_ofAdd hs

theorem multRealVolume_isHaarMeasure : multRealVolume.IsHaarMeasure where
  lt_top_of_isCompact K hK := by
    rw [multRealVolume_apply K hK.measurableSet]
    have : Multiplicative.ofAdd ⁻¹' K = Multiplicative.toAdd '' K := by
      ext x; simp
    rw [this]
    exact (hK.image continuous_toAdd).measure_lt_top
  map_mul_left_eq_self g := by
    rw [multRealVolume, Measure.map_map (continuous_const_mul g).measurable measurable_multReal_ofAdd]
    have : (fun x ↦ g * x) ∘ Multiplicative.ofAdd =
        Multiplicative.ofAdd ∘ (fun x : ℝ ↦ Multiplicative.toAdd g + x) := rfl
    rw [this, ← Measure.map_map measurable_multReal_ofAdd (measurable_const_add _),
      Measure.IsAddLeftInvariant.map_add_left_eq_self]
  open_pos U hU hne := by
    rw [multRealVolume_apply U hU.measurableSet]
    exact (hU.preimage continuous_ofAdd).measure_ne_zero volume (hne.preimage Multiplicative.ofAdd.surjective)

attribute [local instance] multRealVolume_isHaarMeasure

/-- `ℤ = ⟨ofAdd 1⟩ ≤ Multiplicative ℝ`. -/
noncomputable def intMultReal : Subgroup (Multiplicative ℝ) := Subgroup.zpowers (Multiplicative.ofAdd 1)

theorem mem_intMultReal (x : Multiplicative ℝ) : x ∈ intMultReal ↔ ∃ n : ℤ, Multiplicative.toAdd x = n := by
  simp only [intMultReal, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by apply Multiplicative.toAdd.injective; simp [hn]⟩

theorem intMultReal_discrete : DiscreteTopology intMultReal := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine ⟨Multiplicative.toAdd ⁻¹' Set.Ioo (-1 / 2 : ℝ) (1 / 2), isOpen_Ioo.preimage continuous_toAdd, ?_⟩
  ext ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (mem_intMultReal x).mp hx
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (-1 / 2 : ℝ) < n := by rw [← hn]; exact h1
    have h2' : (n : ℝ) < 1 / 2 := by rw [← hn]; exact h2
    have : n = 0 := by
      have : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
      have : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
      omega
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd x = 0
    rw [hn, this, Int.cast_zero]
  · intro h
    have : x = 1 := congrArg Subtype.val h
    subst this
    show (-1 / 2 : ℝ) < Multiplicative.toAdd 1 ∧ Multiplicative.toAdd (1 : Multiplicative ℝ) < 1 / 2
    rw [toAdd_one]; constructor <;> norm_num

attribute [local instance] intMultReal_discrete

/-- `[0, 1)` is a Borel fundamental domain of `ℤ` in `ℝ`. -/
theorem intMultReal_fd :
    MeasurableSet (Multiplicative.toAdd ⁻¹' Set.Ico (0 : ℝ) 1) ∧
      ∀ g : Multiplicative ℝ, ∃! γ : intMultReal, (γ : Multiplicative ℝ)⁻¹ * g ∈ (Multiplicative.toAdd ⁻¹' Set.Ico (0 : ℝ) 1) := by
  refine ⟨measurableSet_Ico (a := (0 : ℝ)) (b := 1), fun g ↦ ?_⟩
  set r := Multiplicative.toAdd g
  have hmem : ∀ n : ℤ, Multiplicative.ofAdd (n : ℝ) ∈ intMultReal := fun n ↦ (mem_intMultReal _).mpr ⟨n, rfl⟩
  have hval : ∀ n : ℤ, ((Multiplicative.ofAdd (n : ℝ))⁻¹ * g ∈ (Multiplicative.toAdd ⁻¹' Set.Ico (0 : ℝ) 1)) ↔
      0 ≤ r - n ∧ r - n < 1 := fun n ↦ by
    simp [r, neg_add_eq_sub]
  refine ⟨⟨_, hmem ⌊r⌋⟩, (hval ⌊r⌋).mpr ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩, ?_⟩
  rintro ⟨γ, hγ⟩ h
  obtain ⟨n, hn⟩ := (mem_intMultReal γ).mp hγ
  have hγ' : γ = Multiplicative.ofAdd (n : ℝ) := by rw [← hn]; rfl
  subst hγ'
  rw [hval] at h
  apply Subtype.ext
  show Multiplicative.ofAdd (n : ℝ) = Multiplicative.ofAdd (⌊r⌋ : ℝ)
  congr 2
  rw [eq_comm, Int.floor_eq_iff]
  constructor <;> linarith [h.1, h.2]

theorem intMultReal_compact : CompactSpace (MulAction.orbitRel.Quotient intMultReal (Multiplicative ℝ)) := by
  refine ⟨(((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image continuous_ofAdd).image
    continuous_quotient_mk').of_isClosed_subset isClosed_univ fun q _ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective q
  obtain ⟨⟨γ, hγ⟩, hD, -⟩ := intMultReal_fd.2 g
  refine ⟨(γ : Multiplicative ℝ)⁻¹ * g, ⟨_, Set.Ico_subset_Icc_self hD, rfl⟩, ?_⟩
  exact (quot_mk_eq_iff' intMultReal).mpr ⟨⟨γ, hγ⟩⁻¹, rfl⟩

end IntReal

end GL2TFTests
