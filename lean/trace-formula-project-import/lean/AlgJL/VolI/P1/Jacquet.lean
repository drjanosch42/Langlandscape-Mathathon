import AlgJL.VolI.P1.PrincipalSeries
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/Jacquet.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (33): `bruhat`, `congrNbhd`, `congrNbhd_mem_nhds`, `deltaHalf_of_norm_one`, `eq_one_of_pow_near_one`, `exists_good_subgroup`, `exists_lambda_ne_zero`, `exists_ps_one_ne_zero`, `exists_test_f1`, `finrank_eq_two_of_exact`, `gl2_totallyDisconnected`, `integrable_S`, `intertwining_transform`, `kOf_eq_diag_mul`, `lambda_eq_zero_of_mem_ker`, `lambda_smul`, `lambda_sub`, `lambda_sum`, `lambda_torus`, `lambda_translate`, `mem_ker_of_lambda_eq_zero`, `normAbs_add_ge`, `normAbs_add_le'`, `normAbs_mul_le`, `normAbs_one_add`, `one_sub_re_le`, `principal_series_jacquet`, `psChar_eq_one_of_near`, `ps_weyl_support`, `quasiChar_trivial_near_one`, `re_sq_of_norm_one`, `toSpanSingleton_comm`, `weyl_conj_entries`.
Dropped tagged IDs: `I.smooth.thm:principal-series-jacquet`. -/

/-!
# The Jacquet module and Frobenius reciprocity (M5a, unit U3)

Lean counterpart of `vol1/ch-1-02-smooth.tex` §3 (items 28–33 of `docs/sprints/M5a-plan.md`). Owner: L2.

D-JAC (`docs/notes/M5a-jacquet-spike.md` §3): `V_N` is Mathlib's `Representation.Coinvariants` of `π|_{N(F)}`, so
`V(N) = Coinvariants.ker` is literally `span{π(n)v − v}`; the `T(F)`-action is Mathlib's `Representation.quotient`
of `π|_{T(F)}` (`T(F)` normalizes `N(F)`, `I.conv.lem:torus-normalizes-unipotent`). The action is unnormalized.
`G`-maps are Mathlib's `Representation.IntertwiningMap`.
-/

open Matrix Matrix.GeneralLinearGroup ValuativeRel GL2TF GL2TF.Local MeasureTheory Topology Filter
open scoped Pointwise

universe u v w

namespace GL2TF.Local

/-! ### No small subgroups in `ℂ^×` -/

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

section Jacquet

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The Jacquet module `V_N = V / V(N)`, `V(N) = span{π(n)v − v : n ∈ N(F), v ∈ V}`: Mathlib's coinvariants of
`π|_{N(F)}`. -/
@[tf_id "I.smooth.def:jacquet-module"]
abbrev jacquetModule (π : Representation ℂ (GL (Fin 2) F) V) : Type u :=
  Representation.Coinvariants (π.comp (unipotent F).subtype)

/-- The (unnormalized) action `π_N(t)(v + V(N)) = π(t)v + V(N)` of `T(F)` on `V_N` (B-only). It is well defined
because `t (π(n)v − v) = π(tnt⁻¹)(π(t)v) − π(t)v` with `tnt⁻¹ ∈ N(F)`. -/
@[tf_aux "I.smooth.def:jacquet-torus-action"]
noncomputable def jacquetTorus (π : Representation ℂ (GL (Fin 2) F) V) :
    Representation ℂ (torus F) (jacquetModule π) :=
  Representation.quotient (π.comp (torus F).subtype) _ (fun t ↦ by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨n, v⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, map_sub]
    have hn : (t : GL (Fin 2) F) * n * (t : GL (Fin 2) F)⁻¹ ∈ unipotent F := by
      obtain ⟨n, hn⟩ := n
      show (t : GL (Fin 2) F) * n * (t : GL (Fin 2) F)⁻¹ ∈ unipotent F
      rw [← (torus_normalizes_unipotent F).2 t t.2]
      exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
    refine Representation.Coinvariants.mem_ker_of_eq (⟨_, hn⟩ : unipotent F) (π t v) _ ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc])

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem jacquetTorus_mk (π : Representation ℂ (GL (Fin 2) F) V) (t : torus F) (v : V) :
    jacquetTorus π t (Representation.Coinvariants.mk _ v) = Representation.Coinvariants.mk _ (π t v) := rfl

/-- The map `φ_N : V_N → W_N`, `φ_N(v + V(N)) = φ(v) + W(N)`, induced by a `G`-map `φ` (B-only): Mathlib's
`Coinvariants.map` of the restriction of `φ` to an `N(F)`-map. -/
@[tf_aux "I.smooth.def:jacquet-induced-map"]
noncomputable def jacquetMap {W : Type v} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin 2) F) V)
    (σ : Representation ℂ (GL (Fin 2) F) W) (φ : Representation.IntertwiningMap π σ) :
    jacquetModule π →ₗ[ℂ] jacquetModule σ :=
  Representation.Coinvariants.map _ _
    (φ.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun n v ↦ LinearMap.congr_fun (φ.isIntertwining' (n : GL (Fin 2) F)) v))

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem jacquetMap_mk {W : Type v} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin 2) F) V)
    (σ : Representation ℂ (GL (Fin 2) F) W) (φ : Representation.IntertwiningMap π σ) (v : V) :
    jacquetMap π σ φ (Representation.Coinvariants.mk _ v) = Representation.Coinvariants.mk _ (φ v) := rfl

/-! ### Proof helpers for Jacquet's lemma: `N(F)` and the balls `N_m = n(ϖ^m 𝒪)` -/

/-- The upper right entry of `n ∈ N(F)` (proof helper). -/
def unipEntry (n : unipotent F) : F := ((n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipotent_eq (n : unipotent F) : (n : GL (Fin 2) F) = upperRightHom (unipEntry n) := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := n
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipEntry_mul (a b : unipotent F) : unipEntry (a * b) = unipEntry a + unipEntry b := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := a
  obtain ⟨_, ⟨y, rfl⟩⟩ := b
  show ((upperRightHom x * upperRightHom y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = x + y
  rw [← AddChar.map_add_eq_mul]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipEntry_inv (a : unipotent F) : unipEntry a⁻¹ = -unipEntry a := by
  have h := unipEntry_mul a⁻¹ a
  rw [inv_mul_cancel] at h
  have h1 : unipEntry (1 : unipotent F) = 0 := by simp [unipEntry]
  rw [h1] at h
  linear_combination -h

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- `N(F)` is abelian (proof helper). -/
theorem unipotent_comm (a b : unipotent F) : a * b = b * a := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, unipotent_eq a, unipotent_eq b, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul, add_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
instance subgroupOf_normal_unip (N₀ N₁ : Subgroup (unipotent F)) : (N₁.subgroupOf N₀).Normal :=
  ⟨fun n hn g ↦ by rwa [show g * n * g⁻¹ = n from by
    apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [unipotent_comm (g : unipotent F), mul_inv_cancel_right]]⟩

theorem normAbs_neg' (x : F) : normAbs F (-x) = normAbs F x := by
  have h1 : normAbs F (-1 : F) = 1 := by
    have h := (normAbs_multiplicative F (-1) (-1)).1
    rw [neg_one_mul, neg_neg, normAbs_one] at h
    nlinarith [normAbs_nonneg F (-1 : F)]
  rw [show -x = (-1) * x by ring, (normAbs_multiplicative F _ _).1, h1, one_mul]

/-- `N_m = {n(x) : |x| ≤ q^{-m}}` (proof helper). -/
def unipBall (m : ℤ) : Subgroup (unipotent F) where
  carrier := {n | normAbs F (unipEntry n) ≤ (q F : ℝ) ^ (-m)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, unipEntry_mul] at *
    exact ((normAbs_multiplicative F _ _).2.2).trans (max_le ha hb)
  one_mem' := by
    simp only [Set.mem_ofPred_eq, unipEntry, OneMemClass.coe_one, Units.val_one, Matrix.one_apply_ne
      (show (0 : Fin 2) ≠ 1 by decide)]
    rw [(normAbs_multiplicative F 0 0).2.1.mpr rfl]
    positivity
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, unipEntry_inv, normAbs_neg'] at *
    exact ha

omit [ValuativeRel F] [IsNALF F] in
theorem continuous_unipEntry : Continuous (unipEntry (F := F)) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 1

/-- `x ↦ n(x)` into `N(F)` (proof helper). -/
def unipOf (x : F) : unipotent F := ⟨upperRightHom x, x, rfl⟩

theorem continuous_unipOf : Continuous (unipOf (F := F)) :=
  continuous_upperRightHom_adelic.subtype_mk _

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipOf_entry (n : unipotent F) : unipOf (unipEntry n) = n :=
  Subtype.ext (unipotent_eq n).symm

theorem unipBall_isCompact_isOpen (m : ℤ) :
    IsCompact (unipBall (F := F) m : Set (unipotent F)) ∧ IsOpen (unipBall (F := F) m : Set (unipotent F)) := by
  have hset : (unipBall (F := F) m : Set (unipotent F)) = unipEntry ⁻¹' ((((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F)) := by
    ext n; exact normAbs_le_iff_mem F m _
  refine ⟨?_, ?_⟩
  · have : (unipBall (F := F) m : Set (unipotent F)) = unipOf '' ((((unif F : 𝒪[F]) : F) ^ m) • (𝒪[F] : Set F)) := by
      rw [hset]
      ext n
      constructor
      · intro hn; exact ⟨_, hn, unipOf_entry n⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [this]
    exact (unif_zpow_smul_integer_isCompact_isOpen F m).1.image continuous_unipOf
  · rw [hset]
    exact (unif_zpow_smul_integer_isCompact_isOpen F m).2.preimage continuous_unipEntry

theorem unipBall_anti {a b : ℤ} (h : b ≤ a) : unipBall a ≤ unipBall (F := F) b := fun n hn ↦
  le_trans hn (zpow_le_zpow_right₀ (by exact_mod_cast (one_lt_q F).le : (1 : ℝ) ≤ q F) (by omega))

/-- Every neighbourhood of `1` in `N(F)` contains some `N_m` (proof helper). -/
theorem exists_unipBall_subset {U : Set (unipotent F)} (hU : U ∈ nhds (1 : unipotent F)) :
    ∃ m : ℤ, (unipBall (F := F) m : Set (unipotent F)) ⊆ U := by
  have h0 : unipOf (0 : F) = 1 := Subtype.ext (AddChar.map_zero_eq_one _)
  have : unipOf ⁻¹' U ∈ nhds (0 : F) := continuous_unipOf.continuousAt.preimage_mem_nhds (by rwa [h0])
  obtain ⟨m, hm⟩ := exists_unif_pow_smul_integer_subset F _ this
  refine ⟨m, fun n hn ↦ ?_⟩
  have : unipEntry n ∈ unipOf ⁻¹' U := hm ((normAbs_le_iff_mem F m _).mp hn)
  rwa [Set.mem_preimage, unipOf_entry] at this

/-- Every `n ∈ N(F)` lies in `N_b` for all small `b` (proof helper). -/
theorem exists_mem_unipBall (n : unipotent F) : ∃ b₀ : ℤ, ∀ b ≤ b₀, n ∈ unipBall b := by
  by_cases h : unipEntry n = 0
  · refine ⟨0, fun b _ ↦ ?_⟩
    show normAbs F (unipEntry n) ≤ _
    rw [h, (normAbs_multiplicative F 0 0).2.1.mpr rfl]; positivity
  · refine ⟨ordU (Units.mk0 _ h), fun b hb ↦ ?_⟩
    show normAbs F (unipEntry n) ≤ _
    have := normAbs_units_val (Units.mk0 _ h)
    rw [Units.val_mk0] at this
    rw [this]
    exact zpow_le_zpow_right₀ (by exact_mod_cast (one_lt_q F).le : (1 : ℝ) ≤ q F) (by omega)

/-- `N₀/N₁` is finite for compact `N₀` and open `N₁` (proof helper). -/
theorem finite_unip_quot (N₀ N₁ : Subgroup (unipotent F)) (h₀ : IsCompact (N₀ : Set (unipotent F)))
    (h₁ : IsOpen (N₁ : Set (unipotent F))) : Finite (N₀ ⧸ N₁.subgroupOf N₀) := by
  have : CompactSpace N₀ := isCompact_iff_compactSpace.mp h₀
  exact Subgroup.quotient_finite_of_isOpen _ (h₁.preimage continuous_subtype_val)

/-- The averaging sum `Σ_{nN₁ ∈ N₀/N₁} π(n)w` (proof helper). -/
noncomputable def unipAvg (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F)) (w : V) : V :=
  ∑ᶠ c : N₀ ⧸ N₁.subgroupOf N₀, π ((c.out : N₀) : GL (Fin 2) F) w

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipAvg_add (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (v w : V) :
    unipAvg π N₀ N₁ (v + w) = unipAvg π N₀ N₁ v + unipAvg π N₀ N₁ w := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  simp only [unipAvg, finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib]

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem unipAvg_smul (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (c : ℂ) (v : V) :
    unipAvg π N₀ N₁ (c • v) = c • unipAvg π N₀ N₁ v := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  simp only [unipAvg, finsum_eq_sum_of_fintype, map_smul, Finset.smul_sum]

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- Translation invariance: `Σ π(n) π(m) w = Σ π(n) w` for `m ∈ N₀` and `N₁`-fixed `w` (proof helper). -/
theorem unipAvg_translate (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (w : V) (hw : ∀ n ∈ N₁, π (n : GL (Fin 2) F) w = w)
    (m : unipotent F) (hm : m ∈ N₀) : unipAvg π N₀ N₁ (π (m : GL (Fin 2) F) w) = unipAvg π N₀ N₁ w := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  set m' : N₀ := ⟨m, hm⟩
  -- the summand at `c · m` is `π(out(c) m) w`
  have key : ∀ c : N₀ ⧸ N₁.subgroupOf N₀, π (((c * (m' : N₀ ⧸ N₁.subgroupOf N₀)).out : N₀) : GL (Fin 2) F) w =
      π ((c.out : N₀) : GL (Fin 2) F) (π (m : GL (Fin 2) F) w) := by
    intro c
    have hc : c * (m' : N₀ ⧸ N₁.subgroupOf N₀) = ((c.out * m' : N₀) : N₀ ⧸ N₁.subgroupOf N₀) := by
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    obtain ⟨h, he⟩ := QuotientGroup.mk_out_eq_mul (N₁.subgroupOf N₀) (c.out * m')
    rw [hc, he]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [hw ((h : N₀) : unipotent F) (Subgroup.mem_subgroupOf.mp h.2)]
  simp only [unipAvg, finsum_eq_sum_of_fintype]
  calc ∑ c : N₀ ⧸ N₁.subgroupOf N₀, π ((c.out : N₀) : GL (Fin 2) F) (π (m : GL (Fin 2) F) w)
      = ∑ c : N₀ ⧸ N₁.subgroupOf N₀, π (((c * (m' : N₀ ⧸ N₁.subgroupOf N₀)).out : N₀) : GL (Fin 2) F) w :=
        Finset.sum_congr rfl fun c _ ↦ (key c).symm
    _ = ∑ c : N₀ ⧸ N₁.subgroupOf N₀, π ((c.out : N₀) : GL (Fin 2) F) w :=
        Fintype.sum_equiv (Equiv.mulRight (m' : N₀ ⧸ N₁.subgroupOf N₀)) _ _ (fun c ↦ rfl)

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- The (ii) ⇒ (i) direction of Jacquet's lemma (proof helper). -/
theorem mem_ker_of_unipAvg (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (v : V) (h : unipAvg π N₀ N₁ v = 0) :
    v ∈ Representation.Coinvariants.ker (π.comp (unipotent F).subtype) := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  set d := Fintype.card (N₀ ⧸ N₁.subgroupOf N₀)
  have hd : (d : ℂ) ≠ 0 := by
    have : 0 < d := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ c : N₀ ⧸ N₁.subgroupOf N₀, (π ((c.out : N₀) : GL (Fin 2) F) v - v) = -((d : ℂ) • v) := by
    rw [Finset.sum_sub_distrib, ← finsum_eq_sum_of_fintype]
    change unipAvg π N₀ N₁ v - _ = _
    rw [h, Finset.sum_const, Finset.card_univ, zero_sub, Nat.cast_smul_eq_nsmul]
  have hmem : ∑ c : N₀ ⧸ N₁.subgroupOf N₀, (π ((c.out : N₀) : GL (Fin 2) F) v - v) ∈
      Representation.Coinvariants.ker (π.comp (unipotent F).subtype) :=
    Submodule.sum_mem _ fun c _ ↦ Representation.Coinvariants.sub_mem_ker (c.out : unipotent F) v
  rw [hsum] at hmem
  have := Submodule.smul_mem _ (-(d : ℂ)⁻¹) hmem
  rwa [smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hd, one_smul] at this

/-- Jacquet's lemma in the chain form: `v ∈ V(N)` gives `a₀, b₀` such that for all `a ≥ a₀` and `b ≤ min(a, b₀)`,
`N_a` fixes `v` and the average of `v` over `N_b/N_a` vanishes (proof helper). -/
theorem jacquet_chain (π : Representation ℂ (GL (Fin 2) F) V) (hπ : IsSmoothRep π) (v : V)
    (hv : v ∈ Representation.Coinvariants.ker (π.comp (unipotent F).subtype)) :
    ∃ a₀ b₀ : ℤ, ∀ a b : ℤ, a₀ ≤ a → b ≤ b₀ → b ≤ a →
      (∀ n ∈ unipBall (F := F) a, π (n : GL (Fin 2) F) v = v) ∧ unipAvg π (unipBall b) (unipBall a) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨n, w⟩, rfl⟩ := hx
    -- `N_{a₀}` fixes `w` (smoothness), and `n ∈ N_{b₀}`
    have hopen : IsOpen {m : unipotent F | π (m : GL (Fin 2) F) w = w} := (hπ w).preimage continuous_subtype_val
    obtain ⟨a₀, ha₀⟩ := exists_unipBall_subset (hopen.mem_nhds (by simp))
    obtain ⟨b₀, hb₀⟩ := exists_mem_unipBall n
    refine ⟨a₀, b₀, fun a b ha hb hba ↦ ?_⟩
    have hfix : ∀ m ∈ unipBall (F := F) a, π (m : GL (Fin 2) F) w = w := fun m hm ↦ ha₀ (unipBall_anti ha hm)
    have : Finite (unipBall (F := F) b ⧸ (unipBall a).subgroupOf (unipBall b)) :=
      finite_unip_quot _ _ (unipBall_isCompact_isOpen b).1 (unipBall_isCompact_isOpen a).2
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine ⟨fun m hm ↦ ?_, ?_⟩
    · rw [map_sub, hfix m hm, ← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, unipotent_comm,
        Subgroup.coe_mul, map_mul, Module.End.mul_apply, hfix m hm]
    · rw [sub_eq_add_neg, unipAvg_add, ← neg_one_smul ℂ w, unipAvg_smul,
        unipAvg_translate π _ _ w hfix n (hb₀ b hb), neg_one_smul, add_neg_cancel]
  | zero =>
    refine ⟨0, 0, fun a b _ _ _ ↦ ⟨fun m _ ↦ map_zero _, ?_⟩⟩
    have : Finite (unipBall (F := F) b ⧸ (unipBall a).subgroupOf (unipBall b)) :=
      finite_unip_quot _ _ (unipBall_isCompact_isOpen b).1 (unipBall_isCompact_isOpen a).2
    have := Fintype.ofFinite (unipBall (F := F) b ⧸ (unipBall a).subgroupOf (unipBall b))
    simp [unipAvg]
  | add x y _ _ hx hy =>
    obtain ⟨a₁, b₁, h₁⟩ := hx
    obtain ⟨a₂, b₂, h₂⟩ := hy
    refine ⟨max a₁ a₂, min b₁ b₂, fun a b ha hb hba ↦ ?_⟩
    obtain ⟨f₁, s₁⟩ := h₁ a b (le_of_max_le_left ha) (le_trans hb (min_le_left _ _)) hba
    obtain ⟨f₂, s₂⟩ := h₂ a b (le_of_max_le_right ha) (le_trans hb (min_le_right _ _)) hba
    have : Finite (unipBall (F := F) b ⧸ (unipBall a).subgroupOf (unipBall b)) :=
      finite_unip_quot _ _ (unipBall_isCompact_isOpen b).1 (unipBall_isCompact_isOpen a).2
    exact ⟨fun m hm ↦ by rw [map_add, f₁ m hm, f₂ m hm], by rw [unipAvg_add, s₁, s₂, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨a₀, b₀, h₀⟩ := hx
    refine ⟨a₀, b₀, fun a b ha hb hba ↦ ?_⟩
    obtain ⟨f₀, s₀⟩ := h₀ a b ha hb hba
    have : Finite (unipBall (F := F) b ⧸ (unipBall a).subgroupOf (unipBall b)) :=
      finite_unip_quot _ _ (unipBall_isCompact_isOpen b).1 (unipBall_isCompact_isOpen a).2
    exact ⟨fun m hm ↦ by rw [map_smul, f₀ m hm], by rw [unipAvg_smul, s₀, smul_zero]⟩

/-- Jacquet's lemma: for smooth `π`, `v ∈ V(N)` iff there are compact open subgroups `N₁ ≤ N₀` of `N(F)` with
`π(n)v = v` on `N₁` and `Σ_{nN₁ ∈ N₀/N₁} π(n)v = 0` (the summand depends only on `nN₁`; Lean sums over the chosen
representatives `Quotient.out`). -/
@[tf_id "I.smooth.lem:jacquet-kernel"]
theorem jacquet_kernel (π : Representation ℂ (GL (Fin 2) F) V) (hπ : IsSmoothRep π) (v : V) :
    v ∈ Representation.Coinvariants.ker (π.comp (unipotent F).subtype) ↔
      ∃ N₀ N₁ : Subgroup (unipotent F), IsCompact (N₀ : Set (unipotent F)) ∧ IsOpen (N₀ : Set (unipotent F)) ∧
        IsCompact (N₁ : Set (unipotent F)) ∧ IsOpen (N₁ : Set (unipotent F)) ∧ N₁ ≤ N₀ ∧
        (∀ n ∈ N₁, π (n : GL (Fin 2) F) v = v) ∧
        ∑ᶠ c : N₀ ⧸ N₁.subgroupOf N₀, π ((c.out : N₀) : GL (Fin 2) F) v = 0 := by
  constructor
  · intro hv
    obtain ⟨a₀, b₀, hP⟩ := jacquet_chain π hπ v hv
    obtain ⟨h1, h2⟩ := hP (max a₀ b₀) b₀ (le_max_left _ _) le_rfl (le_max_right _ _)
    exact ⟨unipBall b₀, unipBall (max a₀ b₀), (unipBall_isCompact_isOpen b₀).1, (unipBall_isCompact_isOpen b₀).2,
      (unipBall_isCompact_isOpen _).1, (unipBall_isCompact_isOpen _).2, unipBall_anti (le_max_right _ _), h1, h2⟩
  · rintro ⟨N₀, N₁, h₀c, -, -, h₁o, -, -, hsum⟩
    have := finite_unip_quot N₀ N₁ h₀c h₁o
    exact mem_ker_of_unipAvg π N₀ N₁ v hsum

/-- Functoriality: a `G`-map `φ : V → W` maps `V(N)` into `W(N)`; the induced `φ_N` satisfies
`φ_N(v + V(N)) = φ(v) + W(N)`, is `T(F)`-equivariant, `(id_V)_N = id`, and `(ψ ∘ φ)_N = ψ_N ∘ φ_N`. -/
@[tf_id "I.smooth.thm:jacquet-functorial"]
theorem jacquet_functorial {W : Type v} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin 2) F) V)
    (σ : Representation ℂ (GL (Fin 2) F) W) (φ : Representation.IntertwiningMap π σ) :
    Representation.Coinvariants.ker (π.comp (unipotent F).subtype) ≤
        (Representation.Coinvariants.ker (σ.comp (unipotent F).subtype)).comap φ.toLinearMap ∧
      (∀ v : V, jacquetMap π σ φ (Representation.Coinvariants.mk _ v) = Representation.Coinvariants.mk _ (φ v)) ∧
      (∀ (t : torus F) (ξ : jacquetModule π),
        jacquetMap π σ φ (jacquetTorus π t ξ) = jacquetTorus σ t (jacquetMap π σ φ ξ)) ∧
      jacquetMap π π (Representation.IntertwiningMap.id π) = LinearMap.id ∧
      ∀ (W' : Type w) [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ (GL (Fin 2) F) W')
        (ψ : Representation.IntertwiningMap σ τ),
        jacquetMap π τ (ψ.comp φ) = (jacquetMap σ τ ψ).comp (jacquetMap π σ φ) := by
  refine ⟨?_, fun v ↦ rfl, fun t ξ ↦ ?_, ?_, fun W' _ _ τ ψ ↦ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨n, v⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    refine Representation.Coinvariants.mem_ker_of_eq n (φ v) _ ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, map_sub,
      Representation.IntertwiningMap.coe_toLinearMap, φ.isIntertwining]
  · induction ξ using Representation.Coinvariants.induction_on with
    | h v =>
      rw [jacquetTorus_mk, jacquetMap_mk, jacquetMap_mk, jacquetTorus_mk, φ.isIntertwining]
  · exact Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ rfl)
  · exact Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ rfl)

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- `v − d⁻¹ Σ_{N₀/N₁} π(n)v ∈ V(N)`, `d = [N₀ : N₁]` (proof helper). -/
theorem sub_unipAvg_mem_ker (π : Representation ℂ (GL (Fin 2) F) V) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (v : V) :
    v - (Nat.card (N₀ ⧸ N₁.subgroupOf N₀) : ℂ)⁻¹ • unipAvg π N₀ N₁ v ∈
      Representation.Coinvariants.ker (π.comp (unipotent F).subtype) := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  rw [Nat.card_eq_fintype_card]
  set d := Fintype.card (N₀ ⧸ N₁.subgroupOf N₀)
  have hd : (d : ℂ) ≠ 0 := by
    have : 0 < d := Fintype.card_pos
    exact_mod_cast this.ne'
  have hmem : ∑ c : N₀ ⧸ N₁.subgroupOf N₀, (π ((c.out : N₀) : GL (Fin 2) F) v - v) ∈
      Representation.Coinvariants.ker (π.comp (unipotent F).subtype) :=
    Submodule.sum_mem _ fun c _ ↦ Representation.Coinvariants.sub_mem_ker (c.out : unipotent F) v
  have hsum : ∑ c : N₀ ⧸ N₁.subgroupOf N₀, (π ((c.out : N₀) : GL (Fin 2) F) v - v) =
      unipAvg π N₀ N₁ v - (d : ℂ) • v := by
    rw [Finset.sum_sub_distrib, unipAvg, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  rw [hsum] at hmem
  have := Submodule.smul_mem _ (-(d : ℂ)⁻¹) hmem
  convert this using 1
  rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hd, neg_one_smul, sub_neg_eq_add, neg_smul]
  abel

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- `G`-maps commute with the averaging sums (proof helper). -/
theorem unipAvg_map {W : Type v} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin 2) F) V)
    (σ : Representation ℂ (GL (Fin 2) F) W) (φ : Representation.IntertwiningMap π σ) (N₀ N₁ : Subgroup (unipotent F))
    [Finite (N₀ ⧸ N₁.subgroupOf N₀)] (v : V) : φ (unipAvg π N₀ N₁ v) = unipAvg σ N₀ N₁ (φ v) := by
  have := Fintype.ofFinite (N₀ ⧸ N₁.subgroupOf N₀)
  simp only [unipAvg, finsum_eq_sum_of_fintype, map_sum, φ.isIntertwining]

/-- Exactness of `V ↦ V_N` on smooth representations: if `im α = ker β` then `im α_N = ker β_N`; `α` injective
implies `α_N` injective, `β` surjective implies `β_N` surjective. -/
@[tf_id "I.smooth.thm:jacquet-exact"]
theorem jacquet_exact {U : Type u} {W : Type w} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin 2) F) U) (π : Representation ℂ (GL (Fin 2) F) V)
    (σ : Representation ℂ (GL (Fin 2) F) W) (hρ : IsSmoothRep ρ) (hπ : IsSmoothRep π) (hσ : IsSmoothRep σ)
    (α : Representation.IntertwiningMap ρ π) (β : Representation.IntertwiningMap π σ)
    (hαβ : LinearMap.range α.toLinearMap = LinearMap.ker β.toLinearMap) :
    LinearMap.range (jacquetMap ρ π α) = LinearMap.ker (jacquetMap π σ β) ∧
      (Function.Injective α → Function.Injective (jacquetMap ρ π α)) ∧
      (Function.Surjective β → Function.Surjective (jacquetMap π σ β)) := by
  have hβα : ∀ u, β (α u) = 0 := fun u ↦ by
    have : α.toLinearMap u ∈ LinearMap.ker β.toLinearMap := hαβ ▸ LinearMap.mem_range_self _ u
    exact this
  refine ⟨le_antisymm ?_ ?_, fun hα ↦ ?_, fun hβ ξ ↦ ?_⟩
  · rintro _ ⟨ξ, rfl⟩
    induction ξ using Representation.Coinvariants.induction_on with
    | h u =>
      show jacquetMap π σ β (jacquetMap ρ π α _) = 0
      rw [jacquetMap_mk, jacquetMap_mk, hβα, map_zero]
  · intro ξ hξ
    induction ξ using Representation.Coinvariants.induction_on with
    | h v =>
      have hv : β v ∈ Representation.Coinvariants.ker (σ.comp (unipotent F).subtype) := by
        rw [← Representation.Coinvariants.mk_eq_zero]
        rw [LinearMap.mem_ker, jacquetMap_mk] at hξ
        exact hξ
      obtain ⟨a₀, b₀, hP⟩ := jacquet_chain σ hσ _ hv
      obtain ⟨-, h2⟩ := hP a₀ (min a₀ b₀) le_rfl (min_le_right _ _) (min_le_left _ _)
      have : Finite (unipBall (F := F) (min a₀ b₀) ⧸ (unipBall a₀).subgroupOf (unipBall (min a₀ b₀))) :=
        finite_unip_quot _ _ (unipBall_isCompact_isOpen _).1 (unipBall_isCompact_isOpen _).2
      have hker : unipAvg π (unipBall (min a₀ b₀)) (unipBall a₀) v ∈ LinearMap.ker β.toLinearMap := by
        rw [LinearMap.mem_ker, Representation.IntertwiningMap.coe_toLinearMap, unipAvg_map, h2]
      rw [← hαβ] at hker
      obtain ⟨u, hu⟩ := hker
      refine ⟨Representation.Coinvariants.mk _
        ((Nat.card (unipBall (F := F) (min a₀ b₀) ⧸ (unipBall a₀).subgroupOf (unipBall (min a₀ b₀))) : ℂ)⁻¹ • u), ?_⟩
      rw [jacquetMap_mk, map_smul]
      rw [Representation.IntertwiningMap.coe_toLinearMap] at hu
      rw [hu, eq_comm, Representation.Coinvariants.mk_eq_iff]
      exact sub_unipAvg_mem_ker π _ _ v
  · refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
    induction ξ using Representation.Coinvariants.induction_on with
    | h u =>
      rw [jacquetMap_mk, Representation.Coinvariants.mk_eq_zero] at hξ
      obtain ⟨a₀, b₀, hP⟩ := jacquet_chain π hπ _ hξ
      obtain ⟨h1, h2⟩ := hP a₀ (min a₀ b₀) le_rfl (min_le_right _ _) (min_le_left _ _)
      have : Finite (unipBall (F := F) (min a₀ b₀) ⧸ (unipBall a₀).subgroupOf (unipBall (min a₀ b₀))) :=
        finite_unip_quot _ _ (unipBall_isCompact_isOpen _).1 (unipBall_isCompact_isOpen _).2
      rw [Representation.Coinvariants.mk_eq_zero]
      refine mem_ker_of_unipAvg ρ (unipBall (min a₀ b₀)) (unipBall a₀) u (hα ?_)
      rw [unipAvg_map, h2, map_zero]
  · obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ ξ
    obtain ⟨v, rfl⟩ := hβ w
    exact ⟨Representation.Coinvariants.mk _ v, jacquetMap_mk π σ β v⟩

end Jacquet

/-! ## Frobenius reciprocity -/

section Frobenius

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- `f(n(x)) = f(1)` for `f ∈ I(χ)` (proof helper). -/
theorem ps_eval_unipotent (χ₁ χ₂ : QuasiChar F) (f : padicPrincipalSeries χ₁ χ₂) (x : F) :
    f.1 (upperRightHom x) = f.1 1 := by
  have := f.2.2 x 1 1 1
  have hd : diagElt (1 : Fˣ) 1 = 1 := (diagElt_hom (R := F)).1
  simpa [hd, deltaHalf, normAbs_one, map_one] using this

/-- The Frobenius map `Φ ↦ Φ^♭`, `Φ^♭(v + V(N)) = Φ(v)(1)`, from `Hom_G(V, I(χ₁, χ₂))` to the linear forms on `V_N`
(B-only). It is well defined because `Φ(π(n)v)(1) = Φ(v)(n) = Φ(v)(1)` for `n ∈ N(F)`. -/
@[tf_aux "I.smooth.def:frobenius-map"]
noncomputable def frobeniusFlat (π : Representation ℂ (GL (Fin 2) F) V) (χ₁ χ₂ : QuasiChar F) :
    Representation.IntertwiningMap π (psRep χ₁ χ₂) →ₗ[ℂ] (jacquetModule π →ₗ[ℂ] ℂ) where
  toFun Φ := Representation.Coinvariants.lift _
    ((LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin 2) F ↦ ℂ) 1).comp
      ((padicPrincipalSeries χ₁ χ₂).subtype.comp Φ.toLinearMap))
    (fun n ↦ by
      ext v
      obtain ⟨_, ⟨x, rfl⟩⟩ := n
      have hΦ := LinearMap.congr_fun (Φ.isIntertwining' (upperRightHom x)) v
      simp only [LinearMap.coe_comp, Function.comp_apply] at hΦ
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, Subgroup.coe_subtype,
        Submodule.coe_subtype, LinearMap.coe_proj, Function.eval, hΦ, psRep_apply, one_mul]
      exact ps_eval_unipotent χ₁ χ₂ (Φ v) x)
  map_add' _ _ := Representation.Coinvariants.hom_ext (LinearMap.ext fun _ ↦ rfl)
  map_smul' _ _ := Representation.Coinvariants.hom_ext (LinearMap.ext fun _ ↦ rfl)

theorem frobeniusFlat_mk (π : Representation ℂ (GL (Fin 2) F) V) (χ₁ χ₂ : QuasiChar F)
    (Φ : Representation.IntertwiningMap π (psRep χ₁ χ₂)) (v : V) :
    frobeniusFlat π χ₁ χ₂ Φ (Representation.Coinvariants.mk _ v) = (Φ v).1 1 := rfl

/-- `Φ(v)(g) = Φ^♭(π(g)v + V(N))` (proof helper). -/
theorem frobenius_eval (π : Representation ℂ (GL (Fin 2) F) V) (χ₁ χ₂ : QuasiChar F)
    (Φ : Representation.IntertwiningMap π (psRep χ₁ χ₂)) (v : V) (g : GL (Fin 2) F) :
    (Φ v).1 g = frobeniusFlat π χ₁ χ₂ Φ (Representation.Coinvariants.mk _ (π g v)) := by
  rw [frobeniusFlat_mk, Φ.isIntertwining, psRep_apply, one_mul]

/-- The stabilizer of `v` as a subgroup (proof helper). -/
def stabSubgroup (π : Representation ℂ (GL (Fin 2) F) V) (v : V) : Subgroup (GL (Fin 2) F) where
  carrier := {g | π g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The inverse Frobenius map `λ ↦ Φ_λ`, `Φ_λ(v)(g) = λ(π(g)v + V(N))` (proof helper). -/
noncomputable def frobeniusInv (π : Representation ℂ (GL (Fin 2) F) V) (hπ : IsSmoothRep π) (χ₁ χ₂ : QuasiChar F)
    (l : jacquetModule π →ₗ[ℂ] ℂ)
    (hl : ∀ (t₁ t₂ : Fˣ) (ξ : jacquetModule π),
      l (jacquetTorus π ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ ξ) = χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ * l ξ) :
    Representation.IntertwiningMap π (psRep χ₁ χ₂) where
  toFun v := ⟨fun g ↦ l (Representation.Coinvariants.mk _ (π g v)), by
    refine ⟨?_, fun x t₁ t₂ g ↦ ?_⟩
    · have hKc := maxCompact_isCompact_isOpen F
      have hH : IsOpen (stabSubgroup π v : Set (GL (Fin 2) F)) := hπ v
      refine ⟨stabSubgroup π v ⊓ 𝐊[F], ?_, ?_, fun g k hk ↦ ?_⟩
      · rw [Subgroup.coe_inf]
        exact hKc.1.inter_left (Subgroup.isClosed_of_isOpen _ hH)
      · rw [Subgroup.coe_inf]; exact hH.inter hKc.2
      · have hk' : π k v = v := hk.1
        beta_reduce
        rw [map_mul, Module.End.mul_apply, hk']
    · beta_reduce
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have h1 : Representation.Coinvariants.mk (π.comp (unipotent F).subtype)
          (π (upperRightHom x) (π (diagElt t₁ t₂) (π g v))) =
          Representation.Coinvariants.mk (π.comp (unipotent F).subtype) (π (diagElt t₁ t₂) (π g v)) :=
        Representation.Coinvariants.mk_self_apply (π.comp (unipotent F).subtype) ⟨_, ⟨x, rfl⟩⟩ _
      rw [h1, ← hl t₁ t₂]
      rfl⟩
  map_add' v w := Subtype.ext (funext fun g ↦ by simp)
  map_smul' c v := Subtype.ext (funext fun g ↦ by simp)
  isIntertwining' h := LinearMap.ext fun v ↦ Subtype.ext (funext fun g ↦ by
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, psRep_apply, map_mul,
      Module.End.mul_apply])

/-- Frobenius reciprocity. (a) `Φ^♭(v + V(N)) = Φ(v)(1)` and `Φ^♭` is `T(F)`-equivariant for
`ψ(diag(t₁, t₂)) = χ₁(t₁) χ₂(t₂) |t₁/t₂|^{1/2}`; (b) `Φ ↦ Φ^♭` is injective and every `T(F)`-equivariant
`λ : V_N → ℂ` is some `Φ^♭` (with (a): a linear bijection onto `Hom_{T(F)}(V_N, ψ)`); (c) naturality in `V`:
`(Φ ∘ u)^♭ = Φ^♭ ∘ u_N` for every `G`-map `u : V′ → V` from a smooth `V′`. -/
@[tf_id "I.smooth.thm:frobenius-reciprocity"]
theorem frobenius_reciprocity (π : Representation ℂ (GL (Fin 2) F) V) (hπ : IsSmoothRep π) (χ₁ χ₂ : QuasiChar F) :
    (∀ Φ : Representation.IntertwiningMap π (psRep χ₁ χ₂),
      (∀ v : V, frobeniusFlat π χ₁ χ₂ Φ (Representation.Coinvariants.mk _ v) = (Φ v).1 1) ∧
        ∀ (t₁ t₂ : Fˣ) (ξ : jacquetModule π),
          frobeniusFlat π χ₁ χ₂ Φ (jacquetTorus π ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ ξ) =
            χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ * frobeniusFlat π χ₁ χ₂ Φ ξ) ∧
      Function.Injective (frobeniusFlat π χ₁ χ₂) ∧
      (∀ l : jacquetModule π →ₗ[ℂ] ℂ,
        (∀ (t₁ t₂ : Fˣ) (ξ : jacquetModule π),
          l (jacquetTorus π ⟨diagElt t₁ t₂, diagElt_mem_torus t₁ t₂⟩ ξ) = χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ * l ξ) →
        ∃ Φ, frobeniusFlat π χ₁ χ₂ Φ = l) ∧
      ∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin 2) F) V'),
        IsSmoothRep π' → ∀ (u : Representation.IntertwiningMap π' π) (Φ : Representation.IntertwiningMap π (psRep χ₁ χ₂)),
          frobeniusFlat π' χ₁ χ₂ (Φ.comp u) = (frobeniusFlat π χ₁ χ₂ Φ).comp (jacquetMap π' π u) := by
  refine ⟨fun Φ ↦ ⟨fun v ↦ rfl, fun t₁ t₂ ξ ↦ ?_⟩, fun Φ Φ' h ↦ ?_, fun l hl ↦ ⟨frobeniusInv π hπ χ₁ χ₂ l hl, ?_⟩,
    fun V' _ _ π' _ u Φ ↦ Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ rfl)⟩
  · induction ξ using Representation.Coinvariants.induction_on with
    | h v =>
      rw [jacquetTorus_mk, frobeniusFlat_mk, frobeniusFlat_mk, Φ.isIntertwining, psRep_apply, one_mul]
      have := (Φ v).2.2 0 t₁ t₂ 1
      rwa [AddChar.map_zero_eq_one, one_mul, mul_one] at this
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v ↦ Subtype.ext (funext fun g ↦ ?_))
    simp only [Representation.IntertwiningMap.coe_toLinearMap]
    rw [frobenius_eval, frobenius_eval, h]
  · refine Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, frobeniusFlat_mk]
    show l (Representation.Coinvariants.mk _ (π 1 v)) = _
    rw [map_one, Module.End.one_apply]

end Frobenius

end GL2TF.Local
