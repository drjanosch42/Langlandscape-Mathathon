import AlgJL.Meta.Tag
import AlgJL.VolII.Centralizer
import AlgJL.Common.UnipNormOne

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolII/KernelClasses.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (42): `classConstTermKernel`, `classConstTermKernel_eq_tsum`, `classKernel`, `classKernel_eq_sum`, `class_decomposition`, `class_kernel_unfolding`, `cls`, `conjEquiv`, `constTermKernel`, `constTermKernel_eq_tsum`, `constTerm_support`, `constant_term_class_decomposition`, `constant_term_kernel_properties`, `continuous_term`, `continuous_unipNormOne`, `det_ne_zero_rat`, `fibreEquiv`, `fibreEquiv_apply`, `finite_classes`, `finite_classes_kernel`, `finite_rat_support`, `finitely_many_classes`, `integrable_term`, `integral_scale_shift`, `integral_tsum_of_finite`, `iota_unip_entries`, `kernel_eq_tsum_rat`, `mem_classFibre_iff`, `orbitRel_conj`, `orbitRel_of_conj`, `ratEquiv`, `ratNormOne_mem`, `rat_inter_compact_finite`, `summable_of_support_finite`, `torusFibreEquiv`, `torus_entries_ne_zero`, `tq`, `tq_ne_zero`, `trace_det_conj`, `unipNormOne_add`, `unipNormOne_inv`, `unip_mul_rat`.
Dropped tagged IDs: `II.kernel.def:class-constant-term-kernel`, `II.kernel.def:class-kernel`, `II.kernel.def:constant-term-kernel`, `II.kernel.thm:class-decomposition`, `II.kernel.thm:class-kernel-unfolding`, `II.kernel.thm:constant-term-class-decomposition`, `II.kernel.thm:constant-term-kernel-properties`, `II.kernel.thm:finitely-many-classes`. -/

/-!
# Geometric classes and the kernels `K_𝒪`, `K_B` (M7a, unit U5, items 36–48)

Lean counterpart of `vol2/ch-03-kernel.tex` §§2–3 (after the M4 §1 in `VolII.Kernel`): geometric classes
`𝒪 = (t, d) ∈ ℚ × ℚ^×` and their fibres in `GL₂(ℚ)`, the class types, the class kernels `K_𝒪`, the finiteness of the
classes meeting a compact set (exit `II.kernel.thm:finitely-many-classes`), the constant-term kernel `K_B` (integral over
`𝔸` against an explicit additive Haar measure, D13) and its class parts `K_{B,𝒪}`. Owner: L2.

Design: a geometric class is a pair `c = (t, d) : ℚ × ℚˣ` (A: identified with `X² − tX + d`); `classFibre c ⊆ GL₂(ℚ)`.
Elements of `G(ℚ)` and `N(𝔸)` act on `G(𝔸)^1` through the B-only maps `ratNormOne`, `unipNormOne`. The three class types
are one predicate `HasClassType c τ` indexed by a tagged inductive `ClassType` (one `assumptions.yaml` entry, D-HYP).
-/

open MeasureTheory Polynomial Filter Topology Matrix.GeneralLinearGroup

namespace GL2TF

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### Plumbing: `G(ℚ) → G(𝔸)^1` and `n(u) ∈ G(𝔸)^1` -/

/-- `G(ℚ) → G(𝔸)^1`, `γ ↦ ι(γ)` (B-only plumbing; its image is `gl2RatNormOne`). -/
@[tf_aux "II.kernel.def:rat-norm-one"]
noncomputable def ratNormOne : GL (Fin 2) ℚ →* normOneGroup :=
  (ι).codRestrict normOneGroup fun γ ↦ norm_one_splitting.2 ⟨γ, rfl⟩

-- `u ↦ n(u) ∈ G(𝔸)^1` (`unipNormOne`, `II.kernel.def:unip-norm-one`) moved unchanged to `GL2TF.Common.UnipNormOne`
-- (M8, CuspDefs split, G0-U1).

/-! ### §2 Geometric classes (items 36–42) -/

/-- The fibre `𝒪 = {γ ∈ GL₂(ℚ) : tr γ = t, det γ = d}` of the geometric class `𝒪 = (t, d) ∈ ℚ × ℚ^×` (the class of `γ` is
`(tr γ, det γ)`, i.e. its characteristic polynomial `X² − tX + d`). -/
@[tf_id "II.kernel.def:geometric-class"]
def classFibre (c : ℚ × ℚˣ) : Set (GL (Fin 2) ℚ) :=
  {γ | Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℚ) = c.1 ∧ Matrix.det (γ : Matrix (Fin 2) (Fin 2) ℚ) = c.2}

/-- The polynomial `X² − tX + d` of the class `(t, d)` (B-only plumbing). -/
@[tf_aux "II.kernel.def:class-polynomial"]
noncomputable def classPoly (c : ℚ × ℚˣ) : ℚ[X] := X ^ 2 - C c.1 * X + C (c.2 : ℚ)

/-- The three class types (B-only index for `II.kernel.def:class-types`). -/
@[tf_aux "II.kernel.def:class-type-index"]
inductive ClassType
  | centralUnipotent
  | hyperbolic
  | elliptic
  deriving DecidableEq

/-- `𝒪` is central-unipotent (`P = (X − z)²`, `z ∈ ℚ^×`), hyperbolic (`P = (X − a)(X − b)`, `a ≠ b ∈ ℚ^×`) or elliptic
(`P` irreducible). -/
@[tf_id "II.kernel.def:class-types"]
def HasClassType (c : ℚ × ℚˣ) : ClassType → Prop
  | .centralUnipotent => ∃ z : ℚˣ, classPoly c = (X - C (z : ℚ)) ^ 2
  | .hyperbolic => ∃ a b : ℚˣ, a ≠ b ∧ classPoly c = (X - C (a : ℚ)) * (X - C (b : ℚ))
  | .elliptic => Irreducible (classPoly c)

namespace KerAux

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℚ

theorem classPoly_eval (c : ℚ × ℚˣ) (x : ℚ) : (classPoly c).eval x = x ^ 2 - c.1 * x + c.2 := by
  simp [classPoly]

theorem classPoly_natDegree (c : ℚ × ℚˣ) : (classPoly c).natDegree = 2 := by
  unfold classPoly; compute_degree!

theorem classPoly_monic (c : ℚ × ℚˣ) : (classPoly c).Monic := by
  unfold classPoly; monicity!

theorem classPoly_eq_charpoly (c : ℚ × ℚˣ) (γ : GL (Fin 2) ℚ) (hγ : γ ∈ classFibre c) :
    classPoly c = Matrix.charpoly (γ : M₂) := by
  rw [Matrix.charpoly_fin_two, classPoly, hγ.1, hγ.2]

theorem not_irreducible_of_root (c : ℚ × ℚˣ) (x : ℚ) (hx : (classPoly c).IsRoot x) :
    ¬ Irreducible (classPoly c) := by
  intro h
  have h1 := degree_eq_one_of_irreducible_of_root h hx
  rw [degree_eq_natDegree (classPoly_monic c).ne_zero, classPoly_natDegree] at h1
  exact absurd h1 (by decide)

theorem root_of_type (c : ℚ × ℚˣ) (τ : ClassType) (h : HasClassType c τ) (hτ : τ ≠ .elliptic) :
    ∃ x, (classPoly c).IsRoot x := by
  cases τ with
  | centralUnipotent => obtain ⟨z, hz⟩ := h; exact ⟨z, by rw [IsRoot, hz]; simp⟩
  | hyperbolic => obtain ⟨a, b, -, hab⟩ := h; exact ⟨a, by rw [IsRoot, hab]; simp⟩
  | elliptic => exact absurd rfl hτ

theorem type_unique (c : ℚ × ℚˣ) (τ τ' : ClassType) (h : HasClassType c τ) (h' : HasClassType c τ') :
    τ = τ' := by
  have key : ¬ (HasClassType c .centralUnipotent ∧ HasClassType c .hyperbolic) := by
    rintro ⟨⟨z, hz⟩, ⟨a, b, hab, he⟩⟩
    have ha : ((X - C (z : ℚ)) ^ 2).eval (a : ℚ) = 0 := by rw [← hz, he]; simp
    have hb : ((X - C (z : ℚ)) ^ 2).eval (b : ℚ) = 0 := by rw [← hz, he]; simp
    simp only [eval_pow, eval_sub, eval_X, eval_C, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, sub_eq_zero] at ha hb
    exact hab (Units.ext (ha.trans hb.symm))
  have hell : ∀ σ : ClassType, σ ≠ .elliptic → HasClassType c σ → ¬ HasClassType c .elliptic :=
    fun σ hσ hs he ↦ by
      obtain ⟨x, hx⟩ := root_of_type c σ hs hσ
      exact not_irreducible_of_root c x hx he
  cases τ <;> cases τ' <;> first
    | rfl
    | (exfalso; exact key ⟨h, h'⟩)
    | (exfalso; exact key ⟨h', h⟩)
    | (exfalso; exact hell _ (by decide) h h')
    | (exfalso; exact hell _ (by decide) h' h)

theorem type_exists (c : ℚ × ℚˣ) : ∃ τ, HasClassType c τ := by
  by_cases hr : ∃ x, (classPoly c).IsRoot x
  · obtain ⟨a, ha⟩ := hr
    have ha' : a ^ 2 - c.1 * a + c.2 = 0 := by rw [← classPoly_eval]; exact ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha'
    set b := c.1 - a with hbdef
    have hab : a * b = c.2 := by rw [hbdef]; linear_combination -ha'
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb, mul_zero] at hab; exact c.2.ne_zero hab.symm
    have hpoly : classPoly c = (X - C a) * (X - C b) := by
      have h1 : c.1 = a + b := by rw [hbdef]; ring
      simp only [classPoly]
      rw [← hab, h1, C_add, C_mul]; ring
    by_cases hab' : a = b
    · refine ⟨.centralUnipotent, Units.mk0 a ha0, ?_⟩
      rw [hpoly, ← hab', Units.val_mk0]; ring
    · exact ⟨.hyperbolic, Units.mk0 a ha0, Units.mk0 b hb0, fun h ↦ hab' (congrArg Units.val h),
        by simpa using hpoly⟩
  · push Not at hr
    exact ⟨.elliptic, irreducible_of_degree_le_three_of_not_isRoot
      (by rw [classPoly_natDegree]; decide) hr⟩

theorem conj_trace_det (γ δ : GL (Fin 2) ℚ) :
    Matrix.trace ((δ⁻¹ * γ * δ : GL (Fin 2) ℚ) : M₂) = Matrix.trace (γ : M₂) ∧
      Matrix.det ((δ⁻¹ * γ * δ : GL (Fin 2) ℚ) : M₂) = Matrix.det (γ : M₂) := by
  have hinv : (δ : M₂) * ((δ⁻¹ : GL (Fin 2) ℚ) : M₂) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, hinv, Matrix.one_mul]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      hinv, Matrix.det_one, one_mul]

theorem fibre_conj (c : ℚ × ℚˣ) (γ : GL (Fin 2) ℚ) (hγ : γ ∈ classFibre c) (δ : GL (Fin 2) ℚ) :
    δ⁻¹ * γ * δ ∈ classFibre c :=
  ⟨(conj_trace_det γ δ).1.trans hγ.1, (conj_trace_det γ δ).2.trans hγ.2⟩

/-- `γ` is a scalar matrix. -/
def IsScalarQ (γ : GL (Fin 2) ℚ) : Prop :=
  (γ : M₂) 0 1 = 0 ∧ (γ : M₂) 1 0 = 0 ∧ (γ : M₂) 0 0 = (γ : M₂) 1 1

theorem conj_companion (γ : GL (Fin 2) ℚ) (hγ : ¬ IsScalarQ γ) :
    ∃ δ : GL (Fin 2) ℚ, ((δ * γ * δ⁻¹ : GL (Fin 2) ℚ) : M₂) =
      !![0, 1; -Matrix.det (γ : M₂), Matrix.trace (γ : M₂)] := by
  have key : ∀ v0 v1 : ℚ, v0 ^ 2 * (γ : M₂) 0 1 + v0 * v1 * ((γ : M₂) 1 1 - (γ : M₂) 0 0) -
      v1 ^ 2 * (γ : M₂) 1 0 ≠ 0 → ∃ δ : GL (Fin 2) ℚ, ((δ * γ * δ⁻¹ : GL (Fin 2) ℚ) : M₂) =
        !![0, 1; -Matrix.det (γ : M₂), Matrix.trace (γ : M₂)] := by
    intro v0 v1 hdet
    set A : M₂ := !![v0, v1; v0 * (γ : M₂) 0 0 + v1 * (γ : M₂) 1 0, v0 * (γ : M₂) 0 1 + v1 * (γ : M₂) 1 1]
      with hAdef
    have hA : A.det ≠ 0 := by
      rw [hAdef, Matrix.det_fin_two_of]
      intro h; apply hdet; linear_combination h
    set δ := mkOfDetNeZero A hA
    have hδ : (δ : M₂) = A := rfl
    have hmul : (δ : M₂) * (γ : M₂) = !![0, 1; -Matrix.det (γ : M₂), Matrix.trace (γ : M₂)] * (δ : M₂) := by
      rw [hδ, hAdef]
      refine Matrix.ext fun i j ↦ ?_
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
    refine ⟨δ, ?_⟩
    rw [Units.val_mul, Units.val_mul, hmul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  by_cases h01 : (γ : M₂) 0 1 ≠ 0
  · exact key 1 0 (by simpa using h01)
  by_cases h10 : (γ : M₂) 1 0 ≠ 0
  · exact key 0 1 (by simpa using h10)
  push Not at h01 h10
  have hne : (γ : M₂) 0 0 ≠ (γ : M₂) 1 1 := fun h ↦ hγ ⟨h01, h10, h⟩
  refine key 1 1 ?_
  rw [h01, h10]
  intro h; apply hne; linarith

theorem conj_of_same (γ γ' : GL (Fin 2) ℚ) (hγ : ¬ IsScalarQ γ) (hγ' : ¬ IsScalarQ γ')
    (ht : Matrix.trace (γ : M₂) = Matrix.trace (γ' : M₂)) (hd : Matrix.det (γ : M₂) = Matrix.det (γ' : M₂)) :
    ∃ δ : GL (Fin 2) ℚ, γ' = δ⁻¹ * γ * δ := by
  obtain ⟨δ, hδ⟩ := conj_companion γ hγ
  obtain ⟨δ', hδ'⟩ := conj_companion γ' hγ'
  rw [ht, hd, ← hδ'] at hδ
  have heq : δ * γ * δ⁻¹ = δ' * γ' * δ'⁻¹ := Units.ext hδ
  refine ⟨δ⁻¹ * δ', ?_⟩
  calc γ' = δ'⁻¹ * (δ' * γ' * δ'⁻¹) * δ' := by group
    _ = δ'⁻¹ * (δ * γ * δ⁻¹) * δ' := by rw [heq]
    _ = (δ⁻¹ * δ')⁻¹ * γ * (δ⁻¹ * δ') := by group

theorem scalar_centralUnipotent (c : ℚ × ℚˣ) (γ : GL (Fin 2) ℚ) (hγ : γ ∈ classFibre c) (hs : IsScalarQ γ) :
    HasClassType c .centralUnipotent := by
  obtain ⟨h01, h10, h00⟩ := hs
  have hd := hγ.2
  have ht := hγ.1
  rw [Matrix.det_fin_two, h01, h10, h00] at hd
  rw [Matrix.trace_fin_two, h00] at ht
  have hz : (γ : M₂) 1 1 ≠ 0 := by
    intro h0; rw [h0] at hd; exact c.2.ne_zero (by rw [← hd]; ring)
  refine ⟨Units.mk0 _ hz, ?_⟩
  rw [classPoly, ← ht, ← hd, Units.val_mk0]
  simp only [C_add, C_mul, C_sub, C_0]
  ring

theorem nonscalar_of_hyp_ell (c : ℚ × ℚˣ) (hc : HasClassType c .hyperbolic ∨ HasClassType c .elliptic)
    (γ : GL (Fin 2) ℚ) (hγ : γ ∈ classFibre c) : ¬ IsScalarQ γ := by
  intro hs
  have h1 := scalar_centralUnipotent c γ hγ hs
  rcases hc with h | h
  · exact absurd (type_unique c _ _ h1 h) (by decide)
  · exact absurd (type_unique c _ _ h1 h) (by decide)

theorem poly_coeffs (c : ℚ × ℚˣ) (a b : ℚ) (h : classPoly c = (X - C a) * (X - C b)) :
    c.1 = a + b ∧ (c.2 : ℚ) = a * b := by
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp [classPoly] at e0 e1
  refine ⟨?_, e0⟩
  linear_combination -e1 + e0

end KerAux

/-- Every class has exactly one type, and `γ ∈ 𝒪` is elliptic iff `𝒪` is. -/
@[tf_id "II.kernel.thm:class-trichotomy"]
theorem class_trichotomy :
    (∀ c : ℚ × ℚˣ, ∃! τ : ClassType, HasClassType c τ) ∧
      ∀ (c : ℚ × ℚˣ) (γ : GL (Fin 2) ℚ), γ ∈ classFibre c → (IsElliptic γ ↔ HasClassType c .elliptic) := by
  refine ⟨fun c ↦ ?_, fun c γ hγ ↦ ?_⟩
  · obtain ⟨τ, hτ⟩ := KerAux.type_exists c
    exact ⟨τ, hτ, fun τ' h' ↦ (KerAux.type_unique c τ τ' hτ h').symm⟩
  · show Irreducible _ ↔ Irreducible (classPoly c)
    rw [KerAux.classPoly_eq_charpoly c γ hγ]

/-- (a) A hyperbolic or elliptic class is one conjugacy class; (b) `𝒪_{a,b} ∩ T(ℚ) = {diag(a, b), diag(b, a)}`;
(c) `𝒪 ∩ B(ℚ) = ∅` for `𝒪` elliptic; (d) `𝒪_z = {z} ∪ {δ⁻¹ z n(1) δ}`. -/
@[tf_id "II.kernel.thm:semisimple-class-conjugacy"]
theorem semisimple_class_conjugacy :
    (∀ c : ℚ × ℚˣ, HasClassType c .hyperbolic ∨ HasClassType c .elliptic → ∀ γ ∈ classFibre c,
      classFibre c = {γ' | ∃ δ : GL (Fin 2) ℚ, γ' = δ⁻¹ * γ * δ}) ∧
    (∀ (c : ℚ × ℚˣ) (a b : ℚˣ), a ≠ b → classPoly c = (X - C (a : ℚ)) * (X - C (b : ℚ)) →
      classFibre c ∩ (torus ℚ : Set (GL (Fin 2) ℚ)) = {diagElt a b, diagElt b a}) ∧
    (∀ c : ℚ × ℚˣ, HasClassType c .elliptic → classFibre c ∩ (borel ℚ : Set (GL (Fin 2) ℚ)) = ∅) ∧
    ∀ (c : ℚ × ℚˣ) (z : ℚˣ), classPoly c = (X - C (z : ℚ)) ^ 2 →
      classFibre c = {diagElt z z} ∪ {γ' | ∃ δ : GL (Fin 2) ℚ, γ' = δ⁻¹ * (diagElt z z * upperRightHom 1) * δ} := by
  refine ⟨fun c hc γ hγ ↦ ?_, fun c a b hab hpoly ↦ ?_, fun c hc ↦ ?_, fun c z hz ↦ ?_⟩
  · ext γ'
    constructor
    · intro hγ'
      exact KerAux.conj_of_same γ γ' (KerAux.nonscalar_of_hyp_ell c hc γ hγ) (KerAux.nonscalar_of_hyp_ell c hc γ' hγ')
        (hγ.1.trans hγ'.1.symm) (hγ.2.trans hγ'.2.symm)
    · rintro ⟨δ, rfl⟩
      exact KerAux.fibre_conj c γ hγ δ
  · obtain ⟨ht, hd⟩ := KerAux.poly_coeffs c a b hpoly
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨h1, h2⟩, h01, h10⟩
      rw [Matrix.trace_fin_two, ht] at h1
      rw [Matrix.det_fin_two, hd, h01, h10] at h2
      have hq : ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0 - a) * ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0 - b) = 0 := by
        linear_combination ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * h1 - h2
      rcases mul_eq_zero.mp hq with h | h
      · left
        apply Units.ext; refine Matrix.ext fun i j ↦ ?_
        fin_cases i <;> fin_cases j <;> simp [diagElt, h01, h10] <;> linarith
      · right
        apply Units.ext; refine Matrix.ext fun i j ↦ ?_
        fin_cases i <;> fin_cases j <;> simp [diagElt, h01, h10] <;> linarith
    · rintro (rfl | rfl)
      · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [diagElt, Matrix.trace_fin_two, Matrix.det_fin_two, ht, hd]
      · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [diagElt, Matrix.trace_fin_two, Matrix.det_fin_two, ht, hd] <;> ring
  · ext γ
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
    intro hγ hB
    have h10 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := hB
    refine KerAux.not_irreducible_of_root c ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) ?_ hc
    rw [IsRoot, KerAux.classPoly_eval, ← hγ.1, ← hγ.2, Matrix.trace_fin_two, Matrix.det_fin_two, h10]
    ring
  · obtain ⟨ht, hd⟩ := KerAux.poly_coeffs c z z (by rw [hz]; ring)
    have hzn : diagElt z z * upperRightHom 1 ∈ classFibre c := by
      refine ⟨?_, ?_⟩ <;>
        simp [diagElt, Matrix.trace_fin_two, Matrix.det_fin_two, ht, hd]
    have hzs : ¬ KerAux.IsScalarQ (diagElt z z * upperRightHom 1) := by
      rintro ⟨h01, -, -⟩
      simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two] at h01
    ext γ
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hγ
      by_cases hs : KerAux.IsScalarQ γ
      · left
        obtain ⟨h01, h10, h00⟩ := hs
        have h1 := hγ.1
        rw [Matrix.trace_fin_two, ht, h00] at h1
        apply Units.ext; refine Matrix.ext fun i j ↦ ?_
        fin_cases i <;> fin_cases j <;> simp [diagElt, h01, h10, h00] <;> linarith
      · right
        exact KerAux.conj_of_same _ γ hzs hs (hzn.1.trans hγ.1.symm) (hzn.2.trans hγ.2.symm)
    · rintro (rfl | ⟨δ, rfl⟩)
      · refine ⟨?_, ?_⟩ <;> simp [diagElt, Matrix.trace_fin_two, Matrix.det_fin_two, ht, hd]
      · exact KerAux.fibre_conj c _ hzn δ

namespace KerAux

end KerAux

namespace KerAux

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℚ

end KerAux

namespace KerAux

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℚ

end KerAux

/-! ### §3 The constant-term kernel (items 43–47) -/

namespace KerAux

end KerAux

namespace KerAux

end KerAux

end GL2TF
