import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Quotient
import Mathlib.NumberTheory.Modular

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P0/Reduction.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (48): `automorphicQuotientMeasure_isFinite`, `central_infEmb_diag`, `compFin_upperRight_diag`, `compInf_upperRight_diag`, `countable_gl2Rat`, `diagElt_inv`, `diag_inv_upperRight_diag`, `finite_volume`, `haarNormOne_siegelSet`, `ideleNorm_split'`, `isCompact_omegaOf`, `isCompact_zhatThicken`, `lam_box_pos`, `lam_omegaZero`, `lintegral_realUnits_abs`, `lintegral_shell`, `lintegral_siegelTorusSet`, `lintegral_tail`, `lintegral_torusF`, `lintegral_unitsF_mul`, `measurableSet_siegelSet`, `measurableSet_siegelThick`, `measurable_fundamental_domain`, `measurable_split`, `measurable_split_symm`, `measurable_torusF`, `mem_siegelSet_iff_exp`, `mem_siegelThick_iff`, `realIdele`, `realIdele_inv_val`, `realIdele_val`, `shell_eq`, `siegelOmegaZero_eq`, `siegelSet_volume`, `siegelSet_volume_a`, `siegelSet_volume_b`, `siegelSet_volume_omegaZero`, `siegelThick`, `siegelThick_eq`, `siegelTorusSet`, `split_fst_val`, `split_realIdele_mul`, `split_snd_val`, `torusF`, `upperRight_diag_mem_K`, `upperRight_diag_mem_O2`, `upperRight_diag_val`, `zhatThicken`.
Dropped tagged IDs: `I.red.lem:automorphic-quotient-finite-instance`, `I.red.thm:finite-volume`, `I.red.thm:measurable-fundamental-domain`, `I.red.thm:siegel-set-volume`. -/

/-!
# Reduction theory for GL(2) over ℚ (M4, units U1–U3)

Lean counterpart of `vol1/ch-0-08-reduction.tex` §§1–3: Siegel sets and the covering, finite volume and the
fundamental domain, the height lemma and the compactness criterion (D-SIEGEL, D-HEIGHT). Owner: L1.
-/

open MeasureTheory Matrix.GeneralLinearGroup
open scoped ENNReal

namespace GL2TF

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### §1 Siegel sets and the covering (U1) -/

/-- The Siegel set `𝔖(ω, t₀) = {n a k : n ∈ ω, a ∈ A(t₀), k ∈ K}` for `ω ⊆ N(𝔸)`, where `A(t₀)` consists of the
`a ∈ T(𝔸)` with `a_∞ = diag(a₁, a₂)`, `a₁, a₂ > 0`, `a₁a₂ = 1`, `a₁/a₂ ≥ t₀`, and `a_p = 1` for every `p`. -/
@[tf_id "I.red.def:siegel-set"]
noncomputable def siegelSet (ω : Set (unipotent Adele)) (t₀ : ℝ) : Set (GL (Fin 2) Adele) :=
  {g | ∃ n ∈ ω, ∃ a₁ a₂ : ℝˣ, 0 < (a₁ : ℝ) ∧ 0 < (a₂ : ℝ) ∧ (a₁ : ℝ) * a₂ = 1 ∧ t₀ ≤ (a₁ : ℝ) / a₂ ∧
    ∃ k ∈ maxCompactAdelic, g = (n : GL (Fin 2) Adele) * infEmb (diagElt a₁ a₂) * k}

theorem ideleNorm_det_infEmb_real (a : GL (Fin 2) ℝ) :
    ideleNorm (Matrix.GeneralLinearGroup.det (infEmb a)) = |((Matrix.GeneralLinearGroup.det a : ℝˣ) : ℝ)| := by
  show ideleNormFun _ = _
  rw [ideleNormFun, det_adele_val, compInf_infEmb, compFin_infEmb, map_one, Units.val_one]
  simp [Local.normAbs_padic]

/-- `𝔖(ω, t₀) ⊆ G(𝔸)^1` (the claim of `I.red.def:siegel-set`). -/
@[tf_aux "I.red.lem:siegel-set-norm-one"]
theorem siegelSet_subset_normOneGroup (ω : Set (unipotent Adele)) (t₀ : ℝ) :
    siegelSet ω t₀ ⊆ (normOneGroup : Set (GL (Fin 2) Adele)) := by
  rintro g ⟨⟨_, y, rfl⟩, -, a₁, a₂, h1, h2, h12, -, k, hk, rfl⟩
  show ideleNorm (Matrix.GeneralLinearGroup.det _) = 1
  have hn : Matrix.GeneralLinearGroup.det (upperRightHom y) = 1 := by
    apply Units.ext; simp [Matrix.GeneralLinearGroup.det]
  rw [map_mul, map_mul, map_mul, map_mul, hn, map_one, one_mul, ideleNorm_det_K k hk, mul_one,
    ideleNorm_det_infEmb_real]
  have : ((Matrix.GeneralLinearGroup.det (diagElt a₁ a₂) : ℝˣ) : ℝ) = (a₁ : ℝ) * a₂ := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, diagElt, Matrix.det_fin_two]
  rw [this, h12, abs_one]

/-- `ω₀ = {n(u) : u ∈ 𝔸, u_∞ ∈ [−½, ½], u_p = 0 for every p}` (B-only plumbing for
`I.red.thm:siegel-covering`). -/
@[tf_aux "I.red.def:siegel-omega-zero"]
noncomputable def siegelOmegaZero : Set (unipotent Adele) :=
  {n | ∃ u : ℝ, u ∈ Set.Icc (-(1 / 2)) (1 / 2) ∧ (n : GL (Fin 2) Adele) = upperRightHom ((u, 0) : Adele)}

/-- `λ(x) = inf_{δ ∈ G(ℚ)} ‖e₂ δ x‖_𝔸` (B-only plumbing for `I.red.def:height-primitive`). -/
@[tf_aux "I.red.def:primitive-norm"]
noncomputable def primitiveNorm (x : GL (Fin 2) Adele) : ℝ :=
  sInf (Set.range fun δ : GL (Fin 2) ℚ ↦ bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ * x))

/-- The height `ht(x) = log|det x|_𝔸 − 2 log λ(x)` (with `log 0 = 0`). -/
@[tf_id "I.red.def:height-primitive"]
noncomputable def height (x : GL (Fin 2) Adele) : ℝ :=
  Real.log (ideleNorm (Matrix.GeneralLinearGroup.det x)) - 2 * Real.log (primitiveNorm x)

/-- `α(H_B(g)) = log|det g|_𝔸 − 2 log ‖e₂ g‖_𝔸` (B-only plumbing). -/
@[tf_aux "I.red.lem:simple-root-height-map"]
theorem simpleRoot_heightMap (g : GL (Fin 2) Adele) :
    simpleRoot (heightMap g) = Real.log (ideleNorm (Matrix.GeneralLinearGroup.det g)) -
      2 * Real.log (bottomRowNorm g) := by
  simp [simpleRoot, heightMap]; ring

/-! #### Row norms and the local Hadamard inequalities (proof plumbing, untagged) -/

/-- `‖e_i g‖_𝔸` for the row `i` of `g` (`bottomRowNorm = rowNorm 1`). -/
noncomputable def rowNorm (i : Fin 2) (g : GL (Fin 2) Adele) : ℝ :=
  Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) i 0).1 ^ 2 + ((g : Matrix (Fin 2) (Fin 2) Adele) i 1).1 ^ 2) *
    ∏ᶠ p : Nat.Primes, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 0).2 p))
      (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 1).2 p))

theorem rowNorm_one (g : GL (Fin 2) Adele) : rowNorm 1 g = bottomRowNorm g := rfl

/-- The row norm depends only on the row. -/
theorem rowNorm_congr {i i' : Fin 2} {g g' : GL (Fin 2) Adele}
    (h : ∀ j, (g : Matrix (Fin 2) (Fin 2) Adele) i j = (g' : Matrix (Fin 2) (Fin 2) Adele) i' j) :
    rowNorm i g = rowNorm i' g' := by
  simp only [rowNorm, h]

/-- Hadamard at `∞`. -/
theorem hadamard_real (a b c d : ℝ) : |a * d - b * c| ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (a * c + b * d)]

/-- Hadamard at `p` (ultrametric). -/
theorem hadamard_padic (p : Nat.Primes) (a b c d : ℚ_[p]) :
    ‖a * d - b * c‖ ≤ max ‖a‖ ‖b‖ * max ‖c‖ ‖d‖ := by
  rw [sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) ((norm_nonneg _).trans (le_max_left _ _))

theorem entry_place (g : GL (Fin 2) Adele) (p : Nat.Primes) (i j : Fin 2) :
    ((compPlace p g : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j =
      ((g : Matrix (Fin 2) (Fin 2) Adele) i j).2 p := rfl

theorem det_place (g : GL (Fin 2) Adele) (p : Nat.Primes) :
    ((Matrix.GeneralLinearGroup.det g : Idele) : Adele).2 p =
      ((compPlace p g : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det := by
  rw [det_adele_val]
  exact RingHom.map_det (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p)
    ((compFin g : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele)

/-- The local factors of the three adelic quantities at `p`. -/
theorem local_factors (g : GL (Fin 2) Adele) (p : Nat.Primes) :
    Local.normAbs ℚ_[p] (((Matrix.GeneralLinearGroup.det g : Idele) : Adele).2 p) ≤
      max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 0).2 p))
          (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 1).2 p)) *
        max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
          (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) := by
  simp only [Local.normAbs_padic, det_place, Matrix.det_fin_two, ← entry_place]
  exact hadamard_padic p _ _ _ _

/-- At a place with `g_p ∈ K_p` all three local factors are `1`. -/
theorem local_factors_K (g : GL (Fin 2) Adele) (p : Nat.Primes) (hK : compPlace p g ∈ 𝐊[ℚ_[p]]) :
    Local.normAbs ℚ_[p] (((Matrix.GeneralLinearGroup.det g : Idele) : Adele).2 p) = 1 ∧
      ∀ i : Fin 2, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 0).2 p))
        (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 1).2 p)) = 1 := by
  have hd : Local.normAbs ℚ_[p] (((Matrix.GeneralLinearGroup.det g : Idele) : Adele).2 p) = 1 := by
    rw [Local.normAbs_padic, det_place]; exact Kp_det_norm p _ hK
  have he := (mem_Kp_iff p _).mp hK
  have hle : ∀ i, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 0).2 p))
      (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 1).2 p)) ≤ 1 := fun i ↦ by
    simp only [Local.normAbs_padic, ← entry_place]
    exact max_le ((PadicInt.mem_subring_iff (p : ℕ)).mp (he i 0).1)
      ((PadicInt.mem_subring_iff (p : ℕ)).mp (he i 1).1)
  have hf := local_factors g p
  rw [hd] at hf
  have h0 := hle 0
  have h1 := hle 1
  have hn0 : 0 ≤ max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 0).2 p))
      (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 1).2 p)) := by
    simp only [Local.normAbs_padic]; exact (norm_nonneg _).trans (le_max_left _ _)
  have hn1 : 0 ≤ max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
      (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) := by
    simp only [Local.normAbs_padic]; exact (norm_nonneg _).trans (le_max_left _ _)
  have e0 := le_antisymm h0 (by nlinarith)
  have e1 := le_antisymm h1 (by nlinarith)
  refine ⟨hd, fun i ↦ ?_⟩
  fin_cases i
  exacts [e0, e1]

/-- Adelic Hadamard for the two rows (proof plumbing): `‖e₁ g‖_𝔸 ‖e₂ g‖_𝔸 ≥ |det g|_𝔸` for every `g ∈ G(𝔸)`. -/
theorem adelic_hadamard_rows (g : GL (Fin 2) Adele) :
    ideleNorm (Matrix.GeneralLinearGroup.det g) ≤ rowNorm 0 g * rowNorm 1 g := by
  obtain ⟨S, hS⟩ : ∃ S : Finset Nat.Primes, ∀ p ∉ S, compPlace p g ∈ 𝐊[ℚ_[p]] :=
    ⟨(Filter.eventually_cofinite.mp (gl2Fin_eventually_mem (compFin g))).toFinset, fun p hp ↦ by
      simpa [compPlace] using hp⟩
  have hsub : ∀ f : Nat.Primes → ℝ, (∀ p ∉ S, f p = 1) → Function.mulSupport f ⊆ S := fun f hf p hp ↦ by
    by_contra h; exact hp (hf p h)
  have hD := finprod_eq_prod_of_mulSupport_subset _
    (hsub (fun p ↦ Local.normAbs ℚ_[p] (((Matrix.GeneralLinearGroup.det g : Idele) : Adele).2 p))
      fun p hp ↦ (local_factors_K g p (hS p hp)).1)
  have hR : ∀ i : Fin 2, _ := fun i ↦ finprod_eq_prod_of_mulSupport_subset _
    (hsub (fun p ↦ max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 0).2 p))
      (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) i 1).2 p)))
      fun p hp ↦ (local_factors_K g p (hS p hp)).2 i)
  show ideleNormFun _ ≤ _
  rw [ideleNormFun, rowNorm, rowNorm, hD, hR 0, hR 1, det_adele_val]
  have hinf : |((Matrix.GeneralLinearGroup.det (compInf g) : ℝˣ) : ℝ)| ≤
      Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) 0 0).1 ^ 2 + ((g : Matrix (Fin 2) (Fin 2) Adele) 0 1).1 ^ 2) *
      Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ^ 2 + ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 ^ 2) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact hadamard_real _ _ _ _
  have hfin : ∏ p ∈ S, Local.normAbs ℚ_[p] ((((Matrix.GeneralLinearGroup.det g : Idele) : Adele)).2 p) ≤
      (∏ p ∈ S, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 0).2 p))
        (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 0 1).2 p))) *
      ∏ p ∈ S, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun p _ ↦ by rw [Local.normAbs_padic]; exact norm_nonneg _)
      fun p _ ↦ local_factors g p
  rw [det_adele_val] at hfin
  have h0 : 0 ≤ ∏ p ∈ S, Local.normAbs ℚ_[p] (((Matrix.GeneralLinearGroup.det (compFin g) : FinAdeleˣ) :
      FinAdele) p) :=
    Finset.prod_nonneg fun p _ ↦ by rw [Local.normAbs_padic]; exact norm_nonneg _
  calc _ ≤ _ := mul_le_mul hinf hfin h0 (by positivity)
    _ = _ := by ring

theorem rowNorm_pos (i : Fin 2) (g : GL (Fin 2) Adele) : 0 < rowNorm i g := by
  have hd : 0 < ideleNorm (Matrix.GeneralLinearGroup.det g) := ideleNorm_spec.2.1 _
  have hH := adelic_hadamard_rows g
  have hnn : ∀ i, 0 ≤ rowNorm i g := fun i ↦ by
    unfold rowNorm
    refine mul_nonneg (Real.sqrt_nonneg _) (finprod_nonneg fun p ↦ ?_)
    rw [Local.normAbs_padic]; exact (norm_nonneg _).trans (le_max_left _ _)
  rcases (hnn i).lt_or_eq with h | h
  · exact h
  · exfalso
    fin_cases i
    · simp only [Fin.zero_eta] at h; rw [← h, zero_mul] at hH; linarith
    · simp only [Fin.mk_one] at h; rw [← h, mul_zero] at hH; linarith

theorem ideleNorm_det_rat_mul (γ : GL (Fin 2) ℚ) (g : GL (Fin 2) Adele) :
    ideleNorm (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ * g)) = ideleNorm (Matrix.GeneralLinearGroup.det g) := by
  have : Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ) = ratIdele (Matrix.GeneralLinearGroup.det γ) := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.det, gl2Map, ratIdele, RingHom.map_det]
  rw [map_mul, map_mul, this, product_formula, one_mul]

/-- Adelic Hadamard for the rows of `γx` (proof plumbing): for `x ∈ G(𝔸)` and `γ ∈ G(ℚ)` (rows `v`, `w`, linearly independent),
`‖v x‖_𝔸 ‖w x‖_𝔸 ≥ |det x|_𝔸`. -/
theorem adelic_hadamard_rat (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) Adele) :
    ideleNorm (Matrix.GeneralLinearGroup.det x) ≤ rowNorm 0 (gl2Map (algebraMap ℚ Adele) γ * x) * rowNorm 1 (gl2Map (algebraMap ℚ Adele) γ * x) := by
  rw [← ideleNorm_det_rat_mul γ]; exact adelic_hadamard_rows _

theorem rat_mul_entry (γ : GL (Fin 2) ℚ) (g : GL (Fin 2) Adele) (i j : Fin 2) :
    ((gl2Map (algebraMap ℚ Adele) γ * g : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j =
      algebraMap ℚ Adele ((γ : Matrix (Fin 2) (Fin 2) ℚ) i 0) * (g : Matrix (Fin 2) (Fin 2) Adele) 0 j +
      algebraMap ℚ Adele ((γ : Matrix (Fin 2) (Fin 2) ℚ) i 1) * (g : Matrix (Fin 2) (Fin 2) Adele) 1 j := by
  simp [gl2Map, Matrix.mul_apply, Fin.sum_univ_two]

/-! #### Adelic entry norms and primitive vectors (proof plumbing, untagged) -/

/-- `max_{i,j} ‖y_{ij}‖_p`. -/
noncomputable def entryNormP (p : Nat.Primes) (y : GL (Fin 2) Adele) : ℝ :=
  max (max ‖((y : Matrix (Fin 2) (Fin 2) Adele) 0 0).2 p‖ ‖((y : Matrix (Fin 2) (Fin 2) Adele) 0 1).2 p‖)
    (max ‖((y : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p‖ ‖((y : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p‖)

/-- `Σ_{i,j} |y_{ij,∞}|`. -/
noncomputable def entryNormInf (y : GL (Fin 2) Adele) : ℝ :=
  |((y : Matrix (Fin 2) (Fin 2) Adele) 0 0).1| + |((y : Matrix (Fin 2) (Fin 2) Adele) 0 1).1| +
    |((y : Matrix (Fin 2) (Fin 2) Adele) 1 0).1| + |((y : Matrix (Fin 2) (Fin 2) Adele) 1 1).1|

/-- `𝒩(y) = (Σ |y_{ij,∞}|) ∏_p max ‖y_{ij}‖_p`. -/
noncomputable def adelicEntryNorm (y : GL (Fin 2) Adele) : ℝ :=
  entryNormInf y * ∏ᶠ p : Nat.Primes, entryNormP p y

theorem entryNormP_nonneg (p : Nat.Primes) (y : GL (Fin 2) Adele) : 0 ≤ entryNormP p y :=
  (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem entryNormP_K (p : Nat.Primes) (y : GL (Fin 2) Adele) (hK : compPlace p y ∈ 𝐊[ℚ_[p]]) :
    entryNormP p y = 1 := by
  have he := (mem_Kp_iff p _).mp hK
  have hle : ∀ i j, ‖((y : Matrix (Fin 2) (Fin 2) Adele) i j).2 p‖ ≤ 1 := fun i j ↦
    (PadicInt.mem_subring_iff (p : ℕ)).mp (he i j).1
  have hb := Kp_bottom_max p _ hK
  simp only [← entry_place] at hle
  rw [entryNormP]
  simp only [← entry_place]
  refine le_antisymm (max_le (max_le (hle 0 0) (hle 0 1)) (max_le (hle 1 0) (hle 1 1))) ?_
  rw [← hb]; exact le_max_right _ _

theorem entryNormInf_nonneg (y : GL (Fin 2) Adele) : 0 ≤ entryNormInf y := by
  unfold entryNormInf; positivity

theorem exists_finset_K (g : GL (Fin 2) Adele) : ∃ S : Finset Nat.Primes, ∀ p ∉ S, compPlace p g ∈ 𝐊[ℚ_[p]] :=
  ⟨(Filter.eventually_cofinite.mp (gl2Fin_eventually_mem (compFin g))).toFinset, fun p hp ↦ by
    simpa [compPlace] using hp⟩

theorem mul_entry (g y : GL (Fin 2) Adele) (i j : Fin 2) :
    ((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j =
      (g : Matrix (Fin 2) (Fin 2) Adele) i 0 * (y : Matrix (Fin 2) (Fin 2) Adele) 0 j +
      (g : Matrix (Fin 2) (Fin 2) Adele) i 1 * (y : Matrix (Fin 2) (Fin 2) Adele) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Archimedean operator bound for the bottom row. -/
theorem inf_row_bound (u0 u1 y00 y01 y10 y11 : ℝ) :
    Real.sqrt ((u0 * y00 + u1 * y10) ^ 2 + (u0 * y01 + u1 * y11) ^ 2) ≤
      (|y00| + |y01| + |y10| + |y11|) * Real.sqrt (u0 ^ 2 + u1 ^ 2) := by
  have hm : max |u0| |u1| ≤ Real.sqrt (u0 ^ 2 + u1 ^ 2) := by
    apply max_le <;> apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_abs u0, sq_abs u1, sq_nonneg u0, sq_nonneg u1]
  have h1 : Real.sqrt ((u0 * y00 + u1 * y10) ^ 2 + (u0 * y01 + u1 * y11) ^ 2) ≤
      |u0 * y00 + u1 * y10| + |u0 * y01 + u1 * y11| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs (u0 * y00 + u1 * y10), sq_abs (u0 * y01 + u1 * y11), abs_nonneg (u0 * y00 + u1 * y10),
      abs_nonneg (u0 * y01 + u1 * y11)]
  have hu0 : |u0| ≤ max |u0| |u1| := le_max_left _ _
  have hu1 : |u1| ≤ max |u0| |u1| := le_max_right _ _
  have h2 : |u0 * y00 + u1 * y10| + |u0 * y01 + u1 * y11| ≤ (|y00| + |y01| + |y10| + |y11|) * max |u0| |u1| := by
    have a1 := abs_add_le (u0 * y00) (u1 * y10)
    have a2 := abs_add_le (u0 * y01) (u1 * y11)
    rw [abs_mul, abs_mul] at a1 a2
    nlinarith [abs_nonneg y00, abs_nonneg y01, abs_nonneg y10, abs_nonneg y11, abs_nonneg u0, abs_nonneg u1]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-- `p`-adic operator bound for the bottom row. -/
theorem padic_row_bound (p : Nat.Primes) (u0 u1 y00 y01 y10 y11 : ℚ_[p]) :
    max ‖u0 * y00 + u1 * y10‖ ‖u0 * y01 + u1 * y11‖ ≤
      max (max ‖y00‖ ‖y01‖) (max ‖y10‖ ‖y11‖) * max ‖u0‖ ‖u1‖ := by
  set N := max (max ‖y00‖ ‖y01‖) (max ‖y10‖ ‖y11‖)
  set U := max ‖u0‖ ‖u1‖
  have hN : 0 ≤ N := (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hU : 0 ≤ U := (norm_nonneg _).trans (le_max_left _ _)
  have b : ∀ (a : ℚ_[p]) (y : ℚ_[p]), ‖a‖ ≤ U → ‖y‖ ≤ N → ‖a * y‖ ≤ N * U := fun a y ha hy ↦ by
    rw [norm_mul, mul_comm]; exact mul_le_mul hy ha (norm_nonneg _) hN
  have h0 : ‖u0‖ ≤ U := le_max_left _ _
  have h1 : ‖u1‖ ≤ U := le_max_right _ _
  have n00 : ‖y00‖ ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have n01 : ‖y01‖ ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have n10 : ‖y10‖ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have n11 : ‖y11‖ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  exact max_le ((Padic.nonarchimedean _ _).trans (max_le (b _ _ h0 n00) (b _ _ h1 n10)))
    ((Padic.nonarchimedean _ _).trans (max_le (b _ _ h0 n01) (b _ _ h1 n11)))

/-- `‖e₂ g y‖_𝔸 ≤ 𝒩(y) ‖e₂ g‖_𝔸`. -/
theorem bottomRowNorm_mul_le (g y : GL (Fin 2) Adele) :
    bottomRowNorm (g * y) ≤ adelicEntryNorm y * bottomRowNorm g := by
  obtain ⟨S₁, hS₁⟩ := exists_finset_K g
  obtain ⟨S₂, hS₂⟩ := exists_finset_K y
  set S := S₁ ∪ S₂
  have hK : ∀ p ∉ S, compPlace p g ∈ 𝐊[ℚ_[p]] ∧ compPlace p y ∈ 𝐊[ℚ_[p]] ∧ compPlace p (g * y) ∈ 𝐊[ℚ_[p]] :=
    fun p hp ↦ by
      have h1 := hS₁ p fun h ↦ hp (Finset.mem_union_left _ h)
      have h2 := hS₂ p fun h ↦ hp (Finset.mem_union_right _ h)
      exact ⟨h1, h2, by rw [map_mul]; exact Subgroup.mul_mem _ h1 h2⟩
  have hsub : ∀ f : Nat.Primes → ℝ, (∀ p ∉ S, f p = 1) → Function.mulSupport f ⊆ S := fun f hf p hp ↦ by
    by_contra h; exact hp (hf p h)
  have hrow : ∀ (h : GL (Fin 2) Adele) (p : Nat.Primes), compPlace p h ∈ 𝐊[ℚ_[p]] →
      max (Local.normAbs ℚ_[p] (((h : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] (((h : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) = 1 := fun h p hp ↦ by
    simp only [Local.normAbs_padic, ← entry_place]; exact Kp_bottom_max p _ hp
  rw [bottomRowNorm, bottomRowNorm, adelicEntryNorm,
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun p hp ↦ hrow _ p (hK p hp).2.2),
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun p hp ↦ entryNormP_K p y (hK p hp).2.1),
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun p hp ↦ hrow _ p (hK p hp).1)]
  have hinf := inf_row_bound ((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1
    ((y : Matrix (Fin 2) (Fin 2) Adele) 0 0).1 ((y : Matrix (Fin 2) (Fin 2) Adele) 0 1).1
    ((y : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ((y : Matrix (Fin 2) (Fin 2) Adele) 1 1).1
  have hfin : ∏ p ∈ S, max (Local.normAbs ℚ_[p] ((((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] ((((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) ≤
      (∏ p ∈ S, entryNormP p y) * ∏ p ∈ S, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun p _ ↦ by
      rw [Local.normAbs_padic]; exact (norm_nonneg _).trans (le_max_left _ _)) fun p _ ↦ ?_
    simp only [Local.normAbs_padic, mul_entry, Prod.snd_add, Prod.snd_mul, RestrictedProduct.add_apply,
      RestrictedProduct.mul_apply, entryNormP]
    exact padic_row_bound p _ _ _ _ _ _
  have hent : ∀ j, (((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 j).1 =
      ((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 * ((y : Matrix (Fin 2) (Fin 2) Adele) 0 j).1 +
      ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 * ((y : Matrix (Fin 2) (Fin 2) Adele) 1 j).1 := fun j ↦ by
    rw [mul_entry]; rfl
  rw [hent, hent]
  have h0 : 0 ≤ ∏ p ∈ S, max (Local.normAbs ℚ_[p] ((((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] ((((g * y : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) :=
    Finset.prod_nonneg fun p _ ↦ by rw [Local.normAbs_padic]; exact (norm_nonneg _).trans (le_max_left _ _)
  calc _ ≤ ((|((y : Matrix (Fin 2) (Fin 2) Adele) 0 0).1| + |((y : Matrix (Fin 2) (Fin 2) Adele) 0 1).1| +
        |((y : Matrix (Fin 2) (Fin 2) Adele) 1 0).1| + |((y : Matrix (Fin 2) (Fin 2) Adele) 1 1).1|) *
        Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ^ 2 + ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 ^ 2)) *
        ((∏ p ∈ S, entryNormP p y) * ∏ p ∈ S, max (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] (((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p))) :=
        mul_le_mul hinf hfin h0 (by positivity)
    _ = _ := by rw [entryNormInf]; ring

theorem borel_entry_ne (β : GL (Fin 2) ℚ) (hβ : β ∈ borel ℚ) : (β : Matrix (Fin 2) (Fin 2) ℚ) 1 1 ≠ 0 := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := hβ
  have hd : (β : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp β.isUnit).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hd
  exact right_ne_zero_of_mul hd

/-- Scaling the bottom row by `q ∈ ℚ^×` does not change `‖e₂ g‖_𝔸` (homogeneity (i), product formula). -/
theorem bottomRowNorm_scale (q : ℚ) (hq : q ≠ 0) (g h : GL (Fin 2) Adele)
    (hgh : ∀ j, ((h : Matrix (Fin 2) (Fin 2) Adele) 1 j) = algebraMap ℚ Adele q * (g : Matrix (Fin 2) (Fin 2) Adele) 1 j) :
    bottomRowNorm h = bottomRowNorm g := by
  set u : ℚˣ := Units.mk0 q hq
  have hu := product_formula u
  have hn : ideleNorm (ratIdele u) = |(q : ℝ)| * ∏ᶠ p : Nat.Primes, ‖(q : ℚ_[p])‖ := by
    show ideleNormFun _ = _
    rw [ideleNormFun]
    simp only [Local.normAbs_padic]
    rfl
  have hfin1 : (Function.mulSupport fun p : Nat.Primes ↦ ‖(q : ℚ_[p])‖).Finite := by
    have := ideleNorm_spec.2.2 (ratIdele u)
    simp only [Local.normAbs_padic] at this
    exact this
  have hfin2 := (bottomRowNorm_spec g).2.2
  rw [bottomRowNorm, bottomRowNorm, hgh, hgh]
  have e1 : ∀ j, (algebraMap ℚ Adele q * (g : Matrix (Fin 2) (Fin 2) Adele) 1 j).1 =
      (q : ℝ) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 j).1 := fun j ↦ rfl
  have e2 : ∀ j (p : Nat.Primes), (algebraMap ℚ Adele q * (g : Matrix (Fin 2) (Fin 2) Adele) 1 j).2 p =
      (q : ℚ_[p]) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 j).2 p := fun j p ↦ rfl
  simp only [e1, e2, Local.normAbs_padic, norm_mul]
  have hmax : ∀ p : Nat.Primes, max (‖(q : ℚ_[p])‖ * ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p‖)
      (‖(q : ℚ_[p])‖ * ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p‖) =
      ‖(q : ℚ_[p])‖ * max ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p‖ ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p‖ :=
    fun p ↦ (mul_max_of_nonneg _ _ (norm_nonneg _)).symm
  simp only [hmax]
  simp only [Local.normAbs_padic] at hfin2
  rw [finprod_mul_distrib hfin1 hfin2]
  have hsq : Real.sqrt (((q : ℝ) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1) ^ 2 +
      ((q : ℝ) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1) ^ 2) =
      |(q : ℝ)| * Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ^ 2 +
        ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 ^ 2) := by
    rw [show ((q : ℝ) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1) ^ 2 +
        ((q : ℝ) * ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1) ^ 2 =
        (q : ℝ) ^ 2 * (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ^ 2 +
        ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [hsq]
  have : |(q : ℝ)| * ∏ᶠ p : Nat.Primes, ‖(q : ℚ_[p])‖ = 1 := by rw [← hn, hu]
  calc _ = (|(q : ℝ)| * ∏ᶠ p : Nat.Primes, ‖(q : ℚ_[p])‖) * (Real.sqrt (((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).1 ^ 2 +
        ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).1 ^ 2) * ∏ᶠ p : Nat.Primes,
        max ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p‖ ‖((g : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p‖) := by ring
    _ = _ := by rw [this, one_mul]

/-- `‖e₂ β g‖_𝔸 = ‖e₂ g‖_𝔸` for `β ∈ B(ℚ)`. -/
theorem bottomRowNorm_borel_mul (β : GL (Fin 2) ℚ) (hβ : β ∈ borel ℚ) (g : GL (Fin 2) Adele) :
    bottomRowNorm (ι β * g) = bottomRowNorm g := by
  have h10 : (β : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := hβ
  refine bottomRowNorm_scale _ (borel_entry_ne β hβ) g _ fun j ↦ ?_
  rw [rat_mul_entry, h10, map_zero, zero_mul, zero_add]

theorem padic_norm_intCast_lt_one_iff (p : Nat.Primes) (k : ℤ) : ‖(k : ℚ_[p])‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← PadicInt.coe_intCast, ← PadicInt.norm_def, PadicInt.norm_int_lt_one_iff_dvd]

theorem padic_max_coprime (p : Nat.Primes) (m n : ℤ) (h : Int.gcd m n = 1) :
    max ‖(m : ℚ_[p])‖ ‖(n : ℚ_[p])‖ = 1 := by
  refine le_antisymm (max_le (Padic.norm_int_le_one m) (Padic.norm_int_le_one n)) ?_
  by_contra hlt
  push Not at hlt
  have hm := (padic_norm_intCast_lt_one_iff p m).mp ((le_max_left _ _).trans_lt hlt)
  have hn := (padic_norm_intCast_lt_one_iff p n).mp ((le_max_right _ _).trans_lt hlt)
  have hd : (p : ℤ) ∣ (Int.gcd m n : ℤ) := Int.dvd_coe_gcd hm hn
  rw [h, Nat.cast_one] at hd
  have := Int.eq_one_of_dvd_one (by positivity) hd
  have h2 := p.2.two_le
  omega

/-- For `δ` with bottom row `(m, n)`, `m, n` coprime integers: `‖e₂ δ‖_𝔸 = (m² + n²)^{1/2}`. -/
theorem bottomRowNorm_primitive (δ : GL (Fin 2) ℚ) (m n : ℤ) (hmn : Int.gcd m n = 1)
    (hm : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = m) (hn : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = n) :
    bottomRowNorm (ι δ) = Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
  have e : ∀ j, ((ι δ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 j =
      algebraMap ℚ Adele ((δ : Matrix (Fin 2) (Fin 2) ℚ) 1 j) := fun j ↦ rfl
  rw [bottomRowNorm, e, e, hm, hn]
  have e1 : ∀ k : ℤ, (algebraMap ℚ Adele (k : ℚ)).1 = (k : ℝ) := fun k ↦ by simp
  have e2 : ∀ (k : ℤ) (p : Nat.Primes), (algebraMap ℚ Adele (k : ℚ)).2 p = (k : ℚ_[p]) := fun k p ↦ by
    rw [map_intCast, Prod.snd_intCast, finAdele_intCast_apply]
  simp only [e1, e2, Local.normAbs_padic, padic_max_coprime _ m n hmn, finprod_one, mul_one]

/-- Every line `ℚ(a, b)` contains a primitive integral vector. -/
theorem exists_primitive (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ m n : ℤ, Int.gcd m n = 1 ∧ q * a = m ∧ q * b = n := by
  set A : ℤ := a.num * b.den
  set B : ℤ := b.num * a.den
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    rcases hab with h | h
    · left; simp [A, Rat.num_ne_zero.mpr h, b.den_nz]
    · right; simp [B, Rat.num_ne_zero.mpr h, a.den_nz]
  have hg : 0 < Int.gcd A B := Int.gcd_pos_iff.mpr hAB
  refine ⟨((a.den * b.den : ℕ) : ℚ) / (Int.gcd A B : ℚ), by positivity, A / Int.gcd A B, B / Int.gcd A B,
    Int.gcd_div_gcd_div_gcd hg, ?_, ?_⟩
  · rw [Int.cast_div (Int.gcd_dvd_left A B) (by exact_mod_cast hg.ne')]
    simp only [A, Int.cast_mul, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num a]
    push_cast
    field_simp
  · rw [Int.cast_div (Int.gcd_dvd_right A B) (by exact_mod_cast hg.ne')]
    simp only [B, Int.cast_mul, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num b]
    push_cast
    field_simp

/-- Every `δ ∈ G(ℚ)` has `βδ`, `β ∈ B(ℚ)`, with coprime integral bottom row. -/
theorem exists_borel_primitive (δ : GL (Fin 2) ℚ) :
    ∃ β ∈ borel ℚ, ∃ m n : ℤ, Int.gcd m n = 1 ∧ ((β * δ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = m ∧
      ((β * δ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = n := by
  have hab : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ≠ 0 ∨ (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hd : (δ : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit).ne_zero
    rw [Matrix.det_fin_two, h.1, h.2] at hd
    simp at hd
  obtain ⟨q, hq, m, n, hmn, h1, h2⟩ := exists_primitive _ _ hab
  let β : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, q] (by simpa using hq)
  have hβ : (β : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, q] := rfl
  refine ⟨β, by show (β : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0; rw [hβ]; simp, m, n, hmn, ?_, ?_⟩
  · rw [Units.val_mul, hβ, Matrix.mul_apply, Fin.sum_univ_two]; simpa using h1
  · rw [Units.val_mul, hβ, Matrix.mul_apply, Fin.sum_univ_two]; simpa using h2

/-- Same bottom row ⇒ same coset `B(ℚ)δ`. -/
theorem mul_inv_mem_borel_of_bottom (δ δ' : GL (Fin 2) ℚ)
    (h0 : (δ' : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0)
    (h1 : (δ' : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) : δ' * δ⁻¹ ∈ borel ℚ := by
  show ((δ' * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
  have h : ((δ * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  rw [h0, h1]; exact h

theorem adelicEntryNorm_nonneg (y : GL (Fin 2) Adele) : 0 ≤ adelicEntryNorm y :=
  mul_nonneg (entryNormInf_nonneg y) (finprod_nonneg fun p ↦ entryNormP_nonneg p y)

/-- `(m² + n²)^{1/2} ≤ 𝒩(x⁻¹) ‖e₂ δ x‖_𝔸` for coprime integral bottom row `(m, n)` of `δ`. -/
theorem primitive_le (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) (m n : ℤ) (hmn : Int.gcd m n = 1)
    (hm : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = m) (hn : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = n) :
    Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ adelicEntryNorm x⁻¹ * bottomRowNorm (ι δ * x) := by
  rw [← bottomRowNorm_primitive δ m n hmn hm hn]
  have := bottomRowNorm_mul_le (ι δ * x) x⁻¹
  rwa [mul_inv_cancel_right] at this

theorem one_le_sqrt_coprime (m n : ℤ) (hmn : Int.gcd m n = 1) : 1 ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
  have h : m ≠ 0 ∨ n ≠ 0 := by
    by_contra h; push Not at h; rw [h.1, h.2] at hmn; simp at hmn
  rw [Real.one_le_sqrt]
  rcases h with h | h
  · have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_nonneg m, Int.one_le_abs h, sq_abs m]
      exact_mod_cast this
    nlinarith [sq_nonneg (n : ℝ)]
  · have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [sq_nonneg n, Int.one_le_abs h, sq_abs n]
      exact_mod_cast this
    nlinarith [sq_nonneg (m : ℝ)]

/-- `‖e₂ δ x‖_𝔸 ≥ 𝒩(x⁻¹)⁻¹`, in the form `1 ≤ 𝒩(x⁻¹) ‖e₂ δ x‖_𝔸`. -/
theorem one_le_entryNorm_mul (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) :
    1 ≤ adelicEntryNorm x⁻¹ * bottomRowNorm (ι δ * x) := by
  obtain ⟨β, hβ, m, n, hmn, hm, hn⟩ := exists_borel_primitive δ
  have h := primitive_le x (β * δ) m n hmn hm hn
  rw [map_mul, mul_assoc, bottomRowNorm_borel_mul β hβ] at h
  exact (one_le_sqrt_coprime m n hmn).trans h

/-- For `x ∈ G(𝔸)` and `C > 0`, `{δ ∈ G(ℚ) : ‖e₂ δ x‖_𝔸 ≤ C}` is the union of finitely many cosets `B(ℚ)δ₀`. -/
@[tf_id "I.red.lem:primitive-vector-finiteness"]
theorem primitive_vector_finiteness (x : GL (Fin 2) Adele) (C : ℝ) (hC : 0 < C) :
    ∃ F : Finset (GL (Fin 2) ℚ),
      {δ : GL (Fin 2) ℚ | bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ * x) ≤ C} =
        ⋃ δ₀ ∈ F, {δ : GL (Fin 2) ℚ | δ * δ₀⁻¹ ∈ borel ℚ} := by
  classical
  have _ := hC -- `C > 0` is not needed (for `C ≤ 0` the set is empty)
  set N : ℤ := ⌈adelicEntryNorm x⁻¹ * C⌉
  let P : ℤ × ℤ → Prop := fun v ↦ ∃ δ : GL (Fin 2) ℚ, bottomRowNorm (ι δ * x) ≤ C ∧
    (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = v.1 ∧ (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = v.2
  let rep : ℤ × ℤ → GL (Fin 2) ℚ := fun v ↦ if h : P v then Classical.choose h else 1
  have hrep : ∀ v, P v → bottomRowNorm (ι (rep v) * x) ≤ C ∧
      ((rep v : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = v.1 ∧
      ((rep v : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = v.2 := fun v hv ↦ by
    simp only [rep, dite_eq_left hv]; exact Classical.choose_spec hv
  refine ⟨((Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N).filter P).image rep, ?_⟩
  ext δ
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_image, Finset.mem_filter, exists_prop]
  constructor
  · intro hδ
    obtain ⟨β, hβ, m, n, hmn, hm, hn⟩ := exists_borel_primitive δ
    have hb : bottomRowNorm (ι (β * δ) * x) ≤ C := by
      rw [map_mul, mul_assoc, bottomRowNorm_borel_mul β hβ]; exact hδ
    have hs := primitive_le x (β * δ) m n hmn hm hn
    have hR : Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ adelicEntryNorm x⁻¹ * C :=
      hs.trans (mul_le_mul_of_nonneg_left hb (adelicEntryNorm_nonneg _))
    have hbox : ∀ k : ℤ, |(k : ℝ)| ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) → k ∈ Finset.Icc (-N) N := by
      intro k hk
      have h1 : |(k : ℝ)| ≤ (N : ℝ) := (hk.trans hR).trans (Int.le_ceil _)
      have h2 : |k| ≤ N := by exact_mod_cast h1
      rw [Finset.mem_Icc]; exact abs_le.mp h2
    have hm' : |(m : ℝ)| ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])
    have hn' : |(n : ℝ)| ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (m : ℝ)])
    have hP : P (m, n) := ⟨β * δ, hb, hm, hn⟩
    refine ⟨rep (m, n), ⟨(m, n), ⟨Finset.mem_product.mpr ⟨hbox m hm', hbox n hn'⟩, hP⟩, rfl⟩, ?_⟩
    obtain ⟨-, h0, h1⟩ := hrep (m, n) hP
    have hB : (β * δ) * (rep (m, n))⁻¹ ∈ borel ℚ :=
      mul_inv_mem_borel_of_bottom _ _ (by rw [h0, hm]) (by rw [h1, hn])
    have : δ * (rep (m, n))⁻¹ = β⁻¹ * ((β * δ) * (rep (m, n))⁻¹) := by group
    rw [this]
    exact (borel ℚ).mul_mem ((borel ℚ).inv_mem hβ) hB
  · rintro ⟨δ₀, ⟨v, ⟨-, hv⟩, rfl⟩, hδ⟩
    obtain ⟨hb, -, -⟩ := hrep v hv
    have : ι δ * x = ι (δ * (rep v)⁻¹) * (ι (rep v) * x) := by
      rw [map_mul, map_inv]; group
    rw [this, bottomRowNorm_borel_mul _ hδ]
    exact hb

theorem bottomRowNorm_pos (g : GL (Fin 2) Adele) : 0 < bottomRowNorm g := by
  have := rowNorm_pos 1 g; rwa [rowNorm_one] at this

/-- `‖e₂ g k‖_𝔸 = ‖e₂ g‖_𝔸` for `k ∈ K` (from M3's `heightMap_equivariance`). -/
theorem bottomRowNorm_mul_K (g k : GL (Fin 2) Adele) (hk : k ∈ maxCompactAdelic) :
    bottomRowNorm (g * k) = bottomRowNorm g := by
  have h1 : heightMap (1 : GL (Fin 2) Adele) = 0 :=
    (heightMap_equivariance.2 1 (Subgroup.one_mem _) 1).2
  have h := heightMap_equivariance.1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) g k hk
  rw [one_mul, one_mul, h1, zero_add] at h
  have h' := congrFun h 1
  simp only [heightMap, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h'
  exact Real.log_injOn_pos (bottomRowNorm_pos _) (bottomRowNorm_pos _) h'

theorem primitiveNorm_bddBelow (x : GL (Fin 2) Adele) :
    BddBelow (Set.range fun δ : GL (Fin 2) ℚ ↦ bottomRowNorm (ι δ * x)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact (bottomRowNorm_pos _).le⟩

theorem primitiveNorm_le' (x : GL (Fin 2) Adele) (δ : GL (Fin 2) ℚ) :
    primitiveNorm x ≤ bottomRowNorm (ι δ * x) :=
  csInf_le (primitiveNorm_bddBelow x) ⟨δ, rfl⟩

/-- The infimum `λ(x)` is attained. -/
theorem exists_primitiveNorm_eq (x : GL (Fin 2) Adele) :
    ∃ δ₀ : GL (Fin 2) ℚ, bottomRowNorm (ι δ₀ * x) = primitiveNorm x := by
  obtain ⟨F, hF⟩ := primitive_vector_finiteness x (bottomRowNorm (ι 1 * x)) (bottomRowNorm_pos _)
  have h1 : (1 : GL (Fin 2) ℚ) ∈ {δ : GL (Fin 2) ℚ | bottomRowNorm (ι δ * x) ≤ bottomRowNorm (ι 1 * x)} := by simp
  rw [hF] at h1
  obtain ⟨δ₁, hδ₁F, -⟩ := Set.mem_iUnion₂.mp h1
  obtain ⟨δ₀, hδ₀F, hmin⟩ := F.exists_min_image (fun δ ↦ bottomRowNorm (ι δ * x)) ⟨δ₁, hδ₁F⟩
  have hmem : ∀ δ ∈ F, bottomRowNorm (ι δ * x) ≤ bottomRowNorm (ι 1 * x) := fun δ hδ ↦ by
    have : δ ∈ ⋃ δ₀ ∈ F, {δ : GL (Fin 2) ℚ | δ * δ₀⁻¹ ∈ borel ℚ} :=
      Set.mem_iUnion₂.mpr ⟨δ, hδ, by simp⟩
    rw [← hF] at this; exact this
  refine ⟨δ₀, le_antisymm ?_ (primitiveNorm_le' x δ₀)⟩
  refine le_csInf ⟨_, ⟨1, rfl⟩⟩ ?_
  rintro _ ⟨δ, rfl⟩
  show bottomRowNorm (ι δ₀ * x) ≤ bottomRowNorm (ι δ * x)
  by_cases hδ : bottomRowNorm (ι δ * x) ≤ bottomRowNorm (ι 1 * x)
  · have : δ ∈ {δ : GL (Fin 2) ℚ | bottomRowNorm (ι δ * x) ≤ bottomRowNorm (ι 1 * x)} := hδ
    rw [hF] at this
    obtain ⟨δ₂, hδ₂F, hδ₂⟩ := Set.mem_iUnion₂.mp this
    have he : ι δ * x = ι (δ * δ₂⁻¹) * (ι δ₂ * x) := by rw [map_mul, map_inv]; group
    rw [he, bottomRowNorm_borel_mul _ hδ₂]
    exact hmin δ₂ hδ₂F
  · push Not at hδ
    exact (hmem δ₀ hδ₀F).trans hδ.le

/-- `λ(x) > 0` and the infimum is attained at some `δ₀`; for every such `δ₀`,
`ht(x) = α(H_B(δ₀x)) = max_{δ ∈ G(ℚ)} α(H_B(δx))`; and `ht(γxk) = ht(x)` for `γ ∈ G(ℚ)`, `k ∈ K`. -/
@[tf_id "I.red.thm:height-attained"]
theorem height_attained (x : GL (Fin 2) Adele) :
    0 < primitiveNorm x ∧
      (∃ δ₀ : GL (Fin 2) ℚ, bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ₀ * x) = primitiveNorm x) ∧
      (∀ δ₀ : GL (Fin 2) ℚ, bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ₀ * x) = primitiveNorm x →
        height x = simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ₀ * x)) ∧
        IsGreatest (Set.range fun δ : GL (Fin 2) ℚ ↦ simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ * x)))
          (height x)) ∧
      ∀ γ : GL (Fin 2) ℚ, ∀ k ∈ maxCompactAdelic, height (gl2Map (algebraMap ℚ Adele) γ * x * k) = height x := by
  obtain ⟨δ₀, hδ₀⟩ := exists_primitiveNorm_eq x
  have hpos : 0 < primitiveNorm x := hδ₀ ▸ bottomRowNorm_pos _
  refine ⟨hpos, ⟨δ₀, hδ₀⟩, fun δ₁ hδ₁ ↦ ?_, fun γ k hk ↦ ?_⟩
  · have heq : height x = simpleRoot (heightMap (ι δ₁ * x)) := by
      rw [simpleRoot_heightMap, ideleNorm_det_rat_mul, hδ₁, height]
    refine ⟨heq, ⟨δ₁, heq.symm⟩, ?_⟩
    rintro _ ⟨δ, rfl⟩
    show simpleRoot (heightMap (ι δ * x)) ≤ height x
    rw [simpleRoot_heightMap, ideleNorm_det_rat_mul, height]
    have := Real.log_le_log hpos (primitiveNorm_le' x δ)
    linarith
  · have hdet : ideleNorm (Matrix.GeneralLinearGroup.det (ι γ * x * k)) =
        ideleNorm (Matrix.GeneralLinearGroup.det x) := by
      rw [map_mul, map_mul (ideleNorm), ideleNorm_det_K k hk, mul_one, ideleNorm_det_rat_mul]
    have hlam : primitiveNorm (ι γ * x * k) = primitiveNorm x := by
      unfold primitiveNorm
      congr 1
      ext r
      simp only [Set.mem_range]
      constructor
      · rintro ⟨δ, rfl⟩
        refine ⟨δ * γ, ?_⟩
        rw [← mul_assoc, ← mul_assoc, ← map_mul, bottomRowNorm_mul_K _ k hk]
      · rintro ⟨δ, rfl⟩
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [← mul_assoc, ← mul_assoc, ← map_mul, bottomRowNorm_mul_K _ k hk, inv_mul_cancel_right]
    rw [height, height, hdet, hlam]

section SiegelBridge

open UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular

/-! ### The bridge -/

/-- For `g = (a b; c d)` with `det g > 0`: `Re(g·i) = (ac + bd)/(c² + d²)` and `Im(g·i) = det g/(c² + d²)`, i.e.
the Iwasawa coordinates `x` and `t₁/t₂` of `I.decomp.thm:iwasawa-real`. -/
theorem smul_I_re_im (g : GL (Fin 2) ℝ) (hg : 0 < (g.det : ℝ)) :
    (g • I).re = ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 +
        (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) /
        ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2) ∧
      (g • I).im = (g.det : ℝ) /
        ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2) := by
  have hns : Complex.normSq (denom g I) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
    simp [denom, Complex.normSq_apply]; ring
  refine ⟨?_, ?_⟩
  · rw [UpperHalfPlane.re, coe_smul_of_det_pos hg, Complex.div_re, hns]
    simp [num, denom]; ring
  · rw [UpperHalfPlane.im_smul_eq_div_normSq, hns, abs_of_pos hg, I_im, mul_one]

/-! ### `SL₂(ℤ) ⊆ G(ℚ)` and its image in `K_f` -/

/-- `σ ↦ σ` as an element of `GL₂(ℚ)`. -/
noncomputable def slRat (σ : SL(2, ℤ)) : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ σ

theorem compInf_slRat (σ : SL(2, ℤ)) :
    compInf (ι (slRat σ)) = Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  rw [compInf_rat]
  apply Units.ext; ext i j
  simp [slRat, gl2Map, Matrix.GeneralLinearGroup.map]

theorem slRat_place_mem (σ : SL(2, ℤ)) (p : Nat.Primes) :
    compFinPlace p (compFin (ι (slRat σ))) ∈ 𝐊[ℚ_[p]] := by
  have hent : ∀ (τ : SL(2, ℤ)) (i j : Fin 2),
      ((compFinPlace p (compFin (ι (slRat τ))) : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j =
        ((τ i j : ℤ) : ℚ_[p]) := fun τ i j ↦ by
    have e1 : ((ι (slRat τ) : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j = ((τ i j : ℤ) : Adele) := by
      simp [slRat, gl2Map, Matrix.GeneralLinearGroup.map]
    show (((ι (slRat τ) : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j).2 p = _
    rw [e1, Prod.snd_intCast, finAdele_intCast_apply]
  rw [mem_Kp_iff]
  intro i j
  have hinv : (compFinPlace p (compFin (ι (slRat σ))))⁻¹ = compFinPlace p (compFin (ι (slRat σ⁻¹))) := by
    simp [slRat, map_inv]
  rw [hinv, hent, hent, PadicInt.mem_subring_iff, PadicInt.mem_subring_iff]
  exact ⟨Padic.norm_int_le_one _, Padic.norm_int_le_one _⟩

theorem slRat_fin_mem (σ : SL(2, ℤ)) : compFin (ι (slRat σ)) ∈ maxCompactFin := by
  simp only [maxCompactFin, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact slRat_place_mem σ

/-! ### The covering for `x = (h, k)`, `h ∈ SL₂(ℝ)`, `k ∈ K_f` (core of item 5) -/

theorem sqrt3_le_im_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : Real.sqrt 3 / 2 ≤ τ.im := by
  have h3 := three_le_four_mul_im_sq_of_mem_fd h
  have hpos := τ.im_pos
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [show τ.im * 2 = Real.sqrt ((τ.im * 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem siegel_cover_core (h : GL (Fin 2) ℝ) (hdet : (h.det : ℝ) = 1) (k : GL (Fin 2) FinAdele)
    (hk : k ∈ maxCompactFin) :
    ∃ γ : GL (Fin 2) ℚ, ι γ * (infEmb h * finEmb k) ∈ siegelSet siegelOmegaZero (Real.sqrt 3 / 2) := by
  obtain ⟨σ, hσ⟩ := exists_smul_mem_fd (h • I)
  set σR : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ σ
  set g := σR * h with hg_def
  have hσdet : (σR.det : ℝ) = 1 := by
    simp [σR]
  have hgdet : (g.det : ℝ) = 1 := by
    rw [hg_def, map_mul, Units.val_mul, hσdet, hdet, one_mul]
  have hgI : g • I = σ • (h • I) := by
    rw [hg_def, mul_smul]; rfl
  obtain ⟨hre, him⟩ := smul_I_re_im g (by rw [hgdet]; norm_num)
  rw [hgI] at hre him
  obtain ⟨⟨q, ⟨hq2, hgq⟩, -⟩, hform⟩ := iwasawa_real g
  obtain ⟨ht₂, ht₁, hx, -⟩ := hform q hq2 hgq
  set c := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    have := him ▸ (σ • (h • I)).im_pos
    rw [hgdet] at this
    exact (one_div_pos.mp (by simpa using this))
  have ht₂sq : (q.2.2.1 : ℝ) ^ 2 = c ^ 2 + d ^ 2 := by
    rw [ht₂, ← Real.sqrt_eq_rpow, Real.sq_sqrt hcd.le]
  have ht₁' : (q.2.1 : ℝ) = 1 / q.2.2.1 := by
    rw [ht₁, ← Matrix.GeneralLinearGroup.val_det_apply, hgdet]
  have ht₁pos : 0 < (q.2.1 : ℝ) := by rw [ht₁']; exact one_div_pos.mpr hq2
  have hprod : (q.2.1 : ℝ) * q.2.2.1 = 1 := by rw [ht₁']; field_simp
  have hratio : (q.2.1 : ℝ) / q.2.2.1 = (σ • (h • I)).im := by
    rw [him, hgdet, ← ht₂sq, ht₁']; field_simp
  have hre' : q.1 = (σ • (h • I)).re := by rw [hx, hre]
  -- the decomposition in G(𝔸)
  refine ⟨slRat σ, ⟨upperRightHom ((q.1, 0) : Adele), ⟨(q.1, 0), rfl⟩⟩, ⟨q.1, ?_, rfl⟩, q.2.1, q.2.2.1,
    ht₁pos, hq2, hprod, ?_, infEmb (q.2.2.2 : GL (Fin 2) ℝ) * finEmb (compFin (ι (slRat σ)) * k), ?_, ?_⟩
  · rw [Set.mem_Icc, ← abs_le, hre']; exact hσ.2
  · rw [hratio]; exact sqrt3_le_im_of_mem_fd hσ
  · rw [mem_maxCompactAdelic_iff]
    simp only [map_mul, compInf_infEmb, compInf_finEmb, compFin_infEmb, compFin_finEmb, mul_one, one_mul]
    exact ⟨q.2.2.2.2.1, maxCompactFin.mul_mem (slRat_fin_mem σ) hk⟩
  · apply gl_adele_ext
    · simp only [map_mul, compInf_infEmb, compInf_finEmb, mul_one, compInf_slRat]
      rw [compInf, gl2Map_upperRightHom]
      exact hgq
    · simp only [map_mul, compFin_infEmb, compFin_finEmb, mul_one, one_mul]
      rw [compFin, gl2Map_upperRightHom]
      simp

end SiegelBridge

theorem zhat_unit_mem (u : Zhatˣ) (p : Nat.Primes) : ((u : Zhat) : FinAdele) p ∈ PadicInt.subring p := by
  have h := (u : Zhat).2
  simp only [Zhat, Subring.mem_iInf, Subring.mem_comap] at h
  exact h p

theorem zhat_unit_norm (u : Zhatˣ) (p : Nat.Primes) : ‖((u : Zhat) : FinAdele) p‖ ≤ 1 :=
  (PadicInt.mem_subring_iff (p : ℕ)).mp (zhat_unit_mem u p)

theorem diagZhat_mem (u : Zhatˣ) : diagZhat u ∈ maxCompactFin := by
  simp only [maxCompactFin, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro p
  rw [mem_Kp_iff, ← map_inv, ← map_inv]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagZhat, diagHom, diagElt, compFinPlace, gl2Map, Matrix.GeneralLinearGroup.map,
      zhat_unit_norm]

theorem finEmb_mem_K (m : GL (Fin 2) FinAdele) (hm : m ∈ maxCompactFin) : finEmb m ∈ maxCompactAdelic := by
  rw [mem_maxCompactAdelic_iff, compInf_finEmb, compFin_finEmb]
  exact ⟨maxCompactReal.one_mem, hm⟩

theorem det_mem_Zhat (k : GL (Fin 2) FinAdele) (hk : k ∈ maxCompactFin) :
    ((Matrix.GeneralLinearGroup.det k : FinAdeleˣ) : FinAdele) ∈ Zhat := by
  simp only [Zhat, Subring.mem_iInf, Subring.mem_comap]
  intro p
  have hK := (mem_maxCompactFin_iff k).mp hk p
  have he := (mem_Kp_iff p _).mp hK
  have : (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p)
      ((Matrix.GeneralLinearGroup.det k : FinAdeleˣ) : FinAdele) =
      ((compFinPlace p k : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det :=
    RingHom.map_det (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p)
      ((k : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele)
  rw [this, Matrix.det_fin_two]
  exact Subring.sub_mem _ (Subring.mul_mem _ (he 0 0).1 (he 1 1).1) (Subring.mul_mem _ (he 0 1).1 (he 1 0).1)

/-- `det K_f = Ẑ^×` (B-only plumbing for `I.red.thm:siegel-covering`: the hypothesis of
`I.topgrp.thm:strong-approximation` for `K' = K_f`). -/
@[tf_aux "I.red.lem:det-max-compact-fin"]
theorem det_maxCompactFin :
    maxCompactFin.map Matrix.GeneralLinearGroup.det =
      (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom).range := by
  ext d
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h1 := det_mem_Zhat k hk
    have h2 := det_mem_Zhat k⁻¹ (maxCompactFin.inv_mem hk)
    let w : Zhatˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩,
      Subtype.ext (show ((Matrix.GeneralLinearGroup.det k : FinAdeleˣ) : FinAdele) *
        ((Matrix.GeneralLinearGroup.det k⁻¹ : FinAdeleˣ) : FinAdele) = 1 by rw [map_inv, Units.mul_inv]),
      Subtype.ext (show ((Matrix.GeneralLinearGroup.det k⁻¹ : FinAdeleˣ) : FinAdele) *
        ((Matrix.GeneralLinearGroup.det k : FinAdeleˣ) : FinAdele) = 1 by rw [map_inv, Units.inv_mul])⟩
    exact ⟨w, Units.ext rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨diagZhat u, diagZhat_mem u, det_diagZhat u⟩

/-- `G(𝔸)^1 = G(ℚ) 𝔖(ω, t₀)` for every `ω ⊇ ω₀` and every `0 < t₀ ≤ √3/2`. -/
@[tf_id "I.red.thm:siegel-covering"]
theorem siegel_covering (ω : Set (unipotent Adele)) (hω : siegelOmegaZero ⊆ ω) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (ht₀' : t₀ ≤ Real.sqrt 3 / 2) :
    (normOneGroup : Set (GL (Fin 2) Adele)) =
      {x | ∃ γ : GL (Fin 2) ℚ, ∃ s ∈ siegelSet ω t₀, x = gl2Map (algebraMap ℚ Adele) γ * s} := by
  have _ := ht₀ -- `t₀ > 0` is not needed for the covering
  have hmono : siegelSet siegelOmegaZero (Real.sqrt 3 / 2) ⊆ siegelSet ω t₀ := by
    rintro g ⟨n, hn, a₁, a₂, h1, h2, h12, hr, k, hk, rfl⟩
    exact ⟨n, hω hn, a₁, a₂, h1, h2, h12, ht₀'.trans hr, k, hk, rfl⟩
  ext x
  constructor
  · intro hx
    obtain ⟨γ, h, k, hh, hh1, hk1, hkK, hg⟩ := strong_approximation maxCompactFin le_rfl
      maxCompactAdelic_compact.2.1 det_maxCompactFin x
    have hh' : h = infEmb (compInf h) := gl_adele_ext (by rw [compInf_infEmb]) (by rw [compFin_infEmb, hh1])
    have hk' : k = finEmb (compFin k) := gl_adele_ext (by rw [compInf_finEmb, hk1]) (by rw [compFin_finEmb])
    have hx1 : ideleNorm (Matrix.GeneralLinearGroup.det x) = 1 := hx
    have hdet : ((Matrix.GeneralLinearGroup.det (compInf h) : ℝˣ) : ℝ) = 1 := by
      rw [hg, hh', hk', map_mul, map_mul, map_mul, map_mul, ideleNorm_det_K _ (finEmb_mem_K _ hkK), mul_one,
        ideleNorm_det_infEmb_real] at hx1
      have hγ : ideleNorm (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ)) = 1 := by
        simpa using ideleNorm_det_rat_mul γ 1
      rw [hγ, one_mul] at hx1
      have hpos : 0 < ((Matrix.GeneralLinearGroup.det (compInf h) : ℝˣ) : ℝ) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hh
      rwa [abs_of_pos hpos] at hx1
    obtain ⟨γ', hγ'⟩ := siegel_cover_core (compInf h) hdet (compFin k) hkK
    refine ⟨γ * γ'⁻¹, _, hmono hγ', ?_⟩
    have e : x = gl2Map (algebraMap ℚ Adele) γ * (infEmb (compInf h) * finEmb (compFin k)) := by
      rw [← hh', ← hk', hg, mul_assoc]
    rw [e, map_mul, map_inv]
    group
  · rintro ⟨γ, s, hs, rfl⟩
    have h1 : ideleNorm (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ * s)) = 1 := by
      rw [ideleNorm_det_rat_mul]; exact siegelSet_subset_normOneGroup ω t₀ hs
    exact h1

/-! ### §2 Finite volume and the fundamental domain (U2) -/

/-! #### Split torus coordinates (proof plumbing, untagged) -/

/-- `e^r` as a unit. -/
noncomputable def splitExpUnit (r : ℝ) : ℝˣ := Units.mk0 (Real.exp r) (Real.exp_pos r).ne'

/-- `a(r) = diag(e^r, e^{-r})` at `∞`, `1` at every `p`. -/
noncomputable def splitTorus (r : ℝ) : GL (Fin 2) Adele := infEmb (diagElt (splitExpUnit r) (splitExpUnit r)⁻¹)

theorem continuous_infEmb : Continuous infEmb :=
  (glProdEquiv (R := ℝ) (S := FinAdele)).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem continuous_splitTorus : Continuous splitTorus := by
  refine continuous_infEmb.comp ?_
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagElt, splitExpUnit] <;> first | fun_prop | exact Real.continuous_exp.inv₀ fun x ↦ (Real.exp_pos x).ne'
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagElt, splitExpUnit, Units.inv_mk] <;> first | fun_prop | exact Real.continuous_exp.inv₀ fun x ↦ (Real.exp_pos x).ne'

theorem bottomRowNorm_unipotent_mul (n : unipotent Adele) (g : GL (Fin 2) Adele) :
    bottomRowNorm ((n : GL (Fin 2) Adele) * g) = bottomRowNorm g := by
  obtain ⟨_, y, rfl⟩ := n
  have e : ∀ j, ((upperRightHom y * g : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 j =
      (g : Matrix (Fin 2) (Fin 2) Adele) 1 j := fun j ↦ by
    simp [upperRightHom, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [bottomRowNorm, e]

/-- `α(H_B(n · infEmb(diag(a₁, a₂)) · k)) = log(a₁/a₂)` for `a₁, a₂ > 0`. -/
theorem simpleRoot_siegel (n : unipotent Adele) (a₁ a₂ : ℝˣ) (h1 : 0 < (a₁ : ℝ)) (h2 : 0 < (a₂ : ℝ))
    (k : GL (Fin 2) Adele) (hk : k ∈ maxCompactAdelic) :
    simpleRoot (heightMap ((n : GL (Fin 2) Adele) * infEmb (diagElt a₁ a₂) * k)) = Real.log ((a₁ : ℝ) / a₂) := by
  have hn : ideleNorm (Matrix.GeneralLinearGroup.det (n : GL (Fin 2) Adele)) = 1 := by
    obtain ⟨_, y, rfl⟩ := n
    have : Matrix.GeneralLinearGroup.det (upperRightHom y) = 1 := by
      apply Units.ext; simp [Matrix.GeneralLinearGroup.det]
    rw [this, map_one]
  have hb : bottomRowNorm (infEmb (diagElt a₁ a₂)) = a₂ := by
    have ei : ∀ i j, ((infEmb (diagElt a₁ a₂) : Matrix (Fin 2) (Fin 2) Adele) i j).1 =
        ((diagElt a₁ a₂ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j ↦ by
      show ((compInf (infEmb (diagElt a₁ a₂)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
      rw [compInf_infEmb]
    have ef : ∀ i j (p : Nat.Primes), ((infEmb (diagElt a₁ a₂) : Matrix (Fin 2) (Fin 2) Adele) i j).2 p =
        (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := fun i j p ↦ by
      show ((compFinPlace p (compFin (infEmb (diagElt a₁ a₂))) : GL (Fin 2) ℚ_[p]) :
        Matrix (Fin 2) (Fin 2) ℚ_[p]) i j = _
      rw [compFin_infEmb, map_one, Units.val_one]
    rw [bottomRowNorm]
    simp only [ei, ef]
    simp [diagElt, Local.normAbs_padic, Real.sqrt_sq h2.le]
  rw [simpleRoot_heightMap, map_mul, map_mul, map_mul, map_mul, hn, one_mul, ideleNorm_det_K k hk, mul_one,
    ideleNorm_det_infEmb_real, mul_assoc, bottomRowNorm_unipotent_mul, bottomRowNorm_mul_K _ k hk, hb]
  have : ((Matrix.GeneralLinearGroup.det (diagElt a₁ a₂) : ℝˣ) : ℝ) = (a₁ : ℝ) * a₂ := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, diagElt, Matrix.det_fin_two]
  rw [this, abs_of_pos (mul_pos h1 h2), Real.log_mul h1.ne' h2.ne', Real.log_div h1.ne' h2.ne']
  ring

theorem isCompact_siegelOmegaZero : IsCompact siegelOmegaZero := by
  have hc : Continuous fun u : ℝ ↦ unipotentEquiv Adele (Multiplicative.ofAdd ((u, 0) : Adele)) :=
    (unipotentEquiv Adele).continuous.comp (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))
  convert (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).image hc using 1
  ext n
  constructor
  · rintro ⟨u, hu, hn⟩
    exact ⟨u, hu, Subtype.ext (by rw [unipotentEquiv_apply, hn])⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, unipotentEquiv_apply Adele _⟩

/-- Compact subsets of the target of an open surjection from a locally compact space lift to compact sets. -/
theorem exists_compact_image_superset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f) (hs : Function.Surjective f) {K : Set Y}
    (hK : IsCompact K) : ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose x hx using hs
  choose N hN hNx using fun y ↦ exists_compact_mem_nhds (x y)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y ↦ f '' interior (N y)) (fun y ↦ hf _ isOpen_interior)
    fun y _ ↦ Set.mem_iUnion.mpr ⟨y, x y, mem_interior_iff_mem_nhds.mpr (hNx y), hx y⟩
  refine ⟨⋃ y ∈ t, N y, t.isCompact_biUnion fun y _ ↦ hN y, ht.trans ?_⟩
  refine Set.iUnion₂_subset fun y hy ↦ ?_
  exact Set.image_mono (interior_subset.trans (Set.subset_biUnion_of_mem hy))

theorem gl2RatNormOne_rat (γ : gl2RatNormOne) : ∃ γ₀ : GL (Fin 2) ℚ, ι γ₀ = ((γ : normOneGroup) : GL (Fin 2) Adele) := by
  have h : ((γ : normOneGroup) : GL (Fin 2) Adele) ∈ gl2RatAdelic := Subgroup.mem_subgroupOf.mp γ.2
  obtain ⟨γ₀, h₀⟩ := h
  exact ⟨γ₀, h₀⟩

/-! ### §3 The height lemma and the compactness criterion (U3) -/

/-- Adelic Hadamard inequality: for `x ∈ G(𝔸)` and `δ, δ' ∈ G(ℚ)` with `δ'δ⁻¹ ∉ B(ℚ)`,
`‖e₂δx‖_𝔸 ‖e₂δ'x‖_𝔸 ≥ |det x|_𝔸`. -/
@[tf_id "I.red.lem:adelic-hadamard"]
theorem adelic_hadamard (x : GL (Fin 2) Adele) (δ δ' : GL (Fin 2) ℚ) (h : δ' * δ⁻¹ ∉ borel ℚ) :
    ideleNorm (Matrix.GeneralLinearGroup.det x) ≤
      bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ * x) * bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ' * x) := by
  set η := δ' * δ⁻¹
  have hη0 : (η : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ≠ 0 := h
  let M : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(η : Matrix (Fin 2) (Fin 2) ℚ) 1 0, (η : Matrix (Fin 2) (Fin 2) ℚ) 1 1; 0, 1] (by simpa using hη0)
  have hM : (M : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(η : Matrix (Fin 2) (Fin 2) ℚ) 1 0, (η : Matrix (Fin 2) (Fin 2) ℚ) 1 1; 0, 1] := rfl
  have hH := adelic_hadamard_rat M (gl2Map (algebraMap ℚ Adele) δ * x)
  rw [ideleNorm_det_rat_mul] at hH
  have hδ' : gl2Map (algebraMap ℚ Adele) δ' * x = gl2Map (algebraMap ℚ Adele) η * (gl2Map (algebraMap ℚ Adele) δ * x) := by
    simp only [η, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  rw [hδ']
  generalize gl2Map (algebraMap ℚ Adele) δ * x = g at hH ⊢
  have hr1 : rowNorm 1 (gl2Map (algebraMap ℚ Adele) M * g) = bottomRowNorm g :=
    rowNorm_congr fun j ↦ by rw [rat_mul_entry, hM]; simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hr0 : rowNorm 0 (gl2Map (algebraMap ℚ Adele) M * g) = bottomRowNorm (gl2Map (algebraMap ℚ Adele) η * g) := by
    rw [← rowNorm_one]
    exact rowNorm_congr fun j ↦ by rw [rat_mul_entry, rat_mul_entry, hM]; simp
  rw [hr0, hr1, mul_comm] at hH
  exact hH

/-- Height lemma: for `x ∈ G(𝔸)^1`, `t₀ ≥ 1` and `δ, δ' ∈ G(ℚ)` with `α(H_B(δx)) > log t₀` and
`α(H_B(δ'x)) > log t₀`, one has `δ'δ⁻¹ ∈ B(ℚ)`. -/
@[tf_id "I.red.thm:height-lemma"]
theorem height_lemma (x : GL (Fin 2) Adele) (hx : x ∈ normOneGroup) (t₀ : ℝ) (ht₀ : 1 ≤ t₀)
    (δ δ' : GL (Fin 2) ℚ) (h : Real.log t₀ < simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ * x)))
    (h' : Real.log t₀ < simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ' * x))) :
    δ' * δ⁻¹ ∈ borel ℚ := by
  have hx1 : ideleNorm (Matrix.GeneralLinearGroup.det x) = 1 := hx
  have hl : 0 ≤ Real.log t₀ := Real.log_nonneg ht₀
  have hlt : ∀ γ : GL (Fin 2) ℚ, Real.log t₀ < simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) γ * x)) →
      bottomRowNorm (gl2Map (algebraMap ℚ Adele) γ * x) < 1 := fun γ hγ ↦ by
    rw [simpleRoot_heightMap, ideleNorm_det_rat_mul, hx1, Real.log_one, zero_sub] at hγ
    have hpos := rowNorm_pos 1 (gl2Map (algebraMap ℚ Adele) γ * x)
    rw [rowNorm_one] at hpos
    have : Real.log (bottomRowNorm (gl2Map (algebraMap ℚ Adele) γ * x)) < 0 := by linarith
    exact (Real.log_neg_iff hpos).mp this
  have hb := hlt δ h
  have hb' := hlt δ' h'
  by_contra hη
  have hH := adelic_hadamard x δ δ' hη
  rw [hx1] at hH
  have hp := rowNorm_pos 1 (gl2Map (algebraMap ℚ Adele) δ * x)
  rw [rowNorm_one] at hp
  nlinarith

/-- For compact `ω ⊆ N(𝔸)`, `t₀ > 0` and `c ∈ ℝ`, `{x ∈ 𝔖(ω, t₀) : α(H_B(x)) ≤ c}` is compact. -/
@[tf_id "I.red.thm:siegel-truncation-compact"]
theorem siegel_truncation_compact (ω : Set (unipotent Adele)) (hω : IsCompact ω) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (c : ℝ) : IsCompact {x | x ∈ siegelSet ω t₀ ∧ simpleRoot (heightMap x) ≤ c} := by
  set F : unipotent Adele × ℝ × GL (Fin 2) Adele → GL (Fin 2) Adele :=
    fun p ↦ (p.1 : GL (Fin 2) Adele) * splitTorus p.2.1 * p.2.2
  have hF : Continuous F :=
    ((continuous_subtype_val.comp continuous_fst).mul (continuous_splitTorus.comp (continuous_fst.comp
      continuous_snd))).mul (continuous_snd.comp continuous_snd)
  have hK := maxCompactAdelic_compact.2.2.1
  have hcpt := (hω.prod ((isCompact_Icc (a := Real.log t₀ / 2) (b := c / 2)).prod hK)).image hF
  convert hcpt using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, SetLike.mem_coe, Prod.exists]
  constructor
  · rintro ⟨⟨n, hn, a₁, a₂, h1, h2, h12, hr, k, hk, rfl⟩, hc⟩
    rw [simpleRoot_siegel n a₁ a₂ h1 h2 k hk] at hc
    set r := Real.log (a₁ : ℝ)
    have ha₁ : (a₁ : ℝ) = Real.exp r := (Real.exp_log h1).symm
    have ha₂ : (a₂ : ℝ) = (Real.exp r)⁻¹ := by rw [← ha₁]; field_simp; linarith
    have hratio : (a₁ : ℝ) / a₂ = Real.exp (2 * r) := by
      rw [ha₁, ha₂, div_inv_eq_mul, ← Real.exp_add]; ring_nf
    have hdiag : diagElt a₁ a₂ = diagElt (splitExpUnit r) (splitExpUnit r)⁻¹ := by
      congr 1
      · exact Units.ext ha₁
      · exact Units.ext (by rw [ha₂]; rfl)
    refine ⟨n, r, k, ⟨hn, ⟨?_, ?_⟩, hk⟩, by rw [hdiag]; rfl⟩
    · rw [hratio] at hr
      have := Real.log_le_log ht₀ hr
      rw [Real.log_exp] at this; linarith
    · rw [hratio, Real.log_exp] at hc; linarith
  · rintro ⟨n, r, k, ⟨hn, ⟨hr1, hr2⟩, hk⟩, rfl⟩
    have h1 : 0 < ((splitExpUnit r : ℝˣ) : ℝ) := Real.exp_pos r
    have h2 : 0 < (((splitExpUnit r)⁻¹ : ℝˣ) : ℝ) := by
      rw [Units.val_inv_eq_inv_val]; exact inv_pos.mpr h1
    have hratio : ((splitExpUnit r : ℝˣ) : ℝ) / (((splitExpUnit r)⁻¹ : ℝˣ) : ℝ) = Real.exp (2 * r) := by
      rw [Units.val_inv_eq_inv_val, div_inv_eq_mul]
      show Real.exp r * Real.exp r = _
      rw [← Real.exp_add]; ring_nf
    refine ⟨⟨n, hn, splitExpUnit r, (splitExpUnit r)⁻¹, h1, h2, by simp, ?_, k, hk, rfl⟩, ?_⟩
    · rw [hratio]
      calc t₀ = Real.exp (Real.log t₀) := (Real.exp_log ht₀).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · show simpleRoot (heightMap ((n : GL (Fin 2) Adele) * infEmb (diagElt (splitExpUnit r) (splitExpUnit r)⁻¹) * k)) ≤ c
      rw [simpleRoot_siegel n _ _ h1 h2 k hk, hratio, Real.log_exp]; linarith

theorem entryNormP_mul_le (p : Nat.Primes) (g u : GL (Fin 2) Adele) :
    entryNormP p (g * u) ≤ entryNormP p g * entryNormP p u := by
  have hg : ∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) Adele) i j).2 p‖ ≤ entryNormP p g := fun i j ↦ by
    unfold entryNormP; fin_cases i <;> fin_cases j <;> simp
  have hu : ∀ i j, ‖((u : Matrix (Fin 2) (Fin 2) Adele) i j).2 p‖ ≤ entryNormP p u := fun i j ↦ by
    unfold entryNormP; fin_cases i <;> fin_cases j <;> simp
  have hgn := entryNormP_nonneg p g
  have he : ∀ i j, ‖(((g * u : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j).2 p‖ ≤
      entryNormP p g * entryNormP p u := fun i j ↦ by
    rw [mul_entry]
    simp only [Prod.snd_add, Prod.snd_mul, RestrictedProduct.add_apply, RestrictedProduct.mul_apply]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul (hg _ _) (hu _ _) (norm_nonneg _) hgn
  unfold entryNormP
  exact max_le (max_le (he 0 0) (he 0 1)) (max_le (he 1 0) (he 1 1))

/-- The open subgroup `U = {g : g_f ∈ K_f}` of `G(𝔸)`. -/
theorem isOpen_compFin_preimage : IsOpen {g : GL (Fin 2) Adele | compFin g ∈ maxCompactFin} :=
  maxCompactAdelic_compact.2.1.preimage (continuous_gl2Map _ continuous_snd)

theorem entryNormP_mul_U (p : Nat.Primes) (g u : GL (Fin 2) Adele) (hu : compFin u ∈ maxCompactFin) :
    entryNormP p (g * u) = entryNormP p g := by
  have hK : ∀ v : GL (Fin 2) Adele, compFin v ∈ maxCompactFin → entryNormP p v = 1 := fun v hv ↦
    entryNormP_K p v ((mem_maxCompactFin_iff _).mp hv p)
  have hu' : compFin u⁻¹ ∈ maxCompactFin := by rw [map_inv]; exact maxCompactFin.inv_mem hu
  refine le_antisymm ?_ ?_
  · have := entryNormP_mul_le p g u; rwa [hK u hu, mul_one] at this
  · have := entryNormP_mul_le p (g * u) u⁻¹; rwa [mul_inv_cancel_right, hK _ hu', mul_one] at this

theorem continuous_adelicEntryNorm : Continuous adelicEntryNorm := by
  have hent : ∀ i j, Continuous fun y : GL (Fin 2) Adele ↦ ((y : Matrix (Fin 2) (Fin 2) Adele) i j).1 :=
    fun i j ↦ continuous_fst.comp ((Units.continuous_val.matrix_elem i j))
  have hinf : Continuous entryNormInf := by
    unfold entryNormInf
    exact (((hent 0 0).abs.add (hent 0 1).abs).add (hent 1 0).abs).add (hent 1 1).abs
  have hfin : Continuous fun y : GL (Fin 2) Adele ↦ ∏ᶠ p : Nat.Primes, entryNormP p y := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    have hmem : {g : GL (Fin 2) Adele | compFin (y⁻¹ * g) ∈ maxCompactFin} ∈ nhds y := by
      refine (isOpen_compFin_preimage.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
      show compFin (y⁻¹ * y) ∈ maxCompactFin
      rw [inv_mul_cancel, map_one]
      exact maxCompactFin.one_mem
    refine (continuousAt_const (y := ∏ᶠ p : Nat.Primes, entryNormP p y)).congr ?_
    filter_upwards [hmem] with g hg
    have : g = y * (y⁻¹ * g) := by group
    rw [this]
    exact (finprod_congr fun p ↦ entryNormP_mul_U p y _ hg).symm
  exact hinf.mul hfin

/-- For every compact `C ⊆ G(𝔸)^1` there is `c` with `ht(x) ≤ c` for all `x ∈ C`. -/
@[tf_id "I.red.lem:height-locally-bounded"]
theorem height_locally_bounded (C : Set normOneGroup) (hC : IsCompact C) :
    ∃ c : ℝ, ∀ x ∈ C, height (x : GL (Fin 2) Adele) ≤ c := by
  have hc : Continuous fun x : normOneGroup ↦ adelicEntryNorm ((x : GL (Fin 2) Adele)⁻¹) :=
    continuous_adelicEntryNorm.comp (continuous_inv.comp continuous_subtype_val)
  obtain ⟨M, hM⟩ := (hC.image hc).bddAbove
  refine ⟨2 * Real.log M, fun x hx ↦ ?_⟩
  have hxM : adelicEntryNorm ((x : GL (Fin 2) Adele)⁻¹) ≤ M := hM ⟨x, hx, rfl⟩
  obtain ⟨hpos, ⟨δ₀, hδ₀⟩, -, -⟩ := height_attained (x : GL (Fin 2) Adele)
  have h1 := one_le_entryNorm_mul (x : GL (Fin 2) Adele) δ₀
  rw [hδ₀] at h1
  have hN : 0 < adelicEntryNorm ((x : GL (Fin 2) Adele)⁻¹) := by
    by_contra h; push Not at h; nlinarith
  have hx1 : ideleNorm (Matrix.GeneralLinearGroup.det (x : GL (Fin 2) Adele)) = 1 := x.2
  rw [height, hx1, Real.log_one, zero_sub]
  have h2 : 0 ≤ Real.log (adelicEntryNorm ((x : GL (Fin 2) Adele)⁻¹)) + Real.log (primitiveNorm x) := by
    rw [← Real.log_mul hN.ne' hpos.ne']; exact Real.log_nonneg h1
  have h3 := Real.log_le_log hN hxM
  linarith

/-- Compactness criterion: `Ω ⊆ G(ℚ)\G(𝔸)^1` has compact closure iff there is `c` with `α(H_B(δx)) ≤ c` for all
`x ∈ p⁻¹(Ω)` and all `δ ∈ G(ℚ)`. -/
@[tf_id "I.red.thm:compactness-criterion"]
theorem compactness_criterion (Ω : Set (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup)) :
    IsCompact (closure Ω) ↔
      ∃ c : ℝ, ∀ x : normOneGroup, Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) x ∈ Ω →
        ∀ δ : GL (Fin 2) ℚ, simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ * x)) ≤ c := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  have := gl2RatNormOne_discrete
  obtain ⟨-, hT2, -⟩ := automorphicQuotient_secondCountable
  have hopen : IsOpenMap (Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup)) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  constructor
  · intro hc
    obtain ⟨C, hC, hsub⟩ := exists_compact_image_superset hopen Quotient.mk_surjective hc
    obtain ⟨c, hcC⟩ := height_locally_bounded C hC
    refine ⟨c, fun x hx δ ↦ ?_⟩
    obtain ⟨y, hy, hyx⟩ := hsub (subset_closure hx)
    obtain ⟨γ, hγ⟩ := (quot_mk_eq_iff' gl2RatNormOne).mp hyx.symm
    obtain ⟨γ₀, hγ₀⟩ := gl2RatNormOne_rat γ
    have hx' : ((x : normOneGroup) : GL (Fin 2) Adele) = ι γ₀ * y := by
      rw [hγ₀, ← hγ]; simp
    obtain ⟨-, ⟨δ₀, hδ₀⟩, hmax, -⟩ := height_attained (y : GL (Fin 2) Adele)
    have hle := (hmax δ₀ hδ₀).2.2 ⟨δ * γ₀, rfl⟩
    rw [hx', ← mul_assoc, ← map_mul]
    exact hle.trans (hcC y hy)
  · rintro ⟨c, hc⟩
    set S := {s | s ∈ siegelSet siegelOmegaZero (Real.sqrt 3 / 2) ∧ simpleRoot (heightMap s) ≤ c}
    have hS : IsCompact S := siegel_truncation_compact _ isCompact_siegelOmegaZero _ (by positivity) c
    have hT : IsCompact (Subtype.val ⁻¹' S : Set normOneGroup) :=
      normOneGroup_closed_normal.1.isClosedEmbedding_subtypeVal.isCompact_preimage hS
    have hP := hT.image (continuous_quotient_mk' (s := MulAction.orbitRel gl2RatNormOne normOneGroup))
    refine hP.of_isClosed_subset isClosed_closure (closure_minimal ?_ hP.isClosed)
    intro q hq
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    have hcov := (siegel_covering siegelOmegaZero le_rfl (Real.sqrt 3 / 2) (by positivity) le_rfl).le x.2
    obtain ⟨γ, s, hs, hxs⟩ := hcov
    have hsN : s ∈ normOneGroup := siegelSet_subset_normOneGroup _ _ hs
    have hγN : ι γ ∈ normOneGroup := by
      show ideleNorm (Matrix.GeneralLinearGroup.det (ι γ)) = 1
      simpa using ideleNorm_det_rat_mul γ 1
    have hα : simpleRoot (heightMap s) ≤ c := by
      have := hc x hq γ⁻¹
      rwa [hxs, map_inv, inv_mul_cancel_left] at this
    refine ⟨⟨s, hsN⟩, ⟨hs, hα⟩, ?_⟩
    refine ((quot_mk_eq_iff' gl2RatNormOne).mpr ⟨⟨⟨ι γ, hγN⟩, Subgroup.mem_subgroupOf.mpr ⟨γ, rfl⟩⟩, ?_⟩).symm
    exact Subtype.ext hxs.symm

end GL2TF
