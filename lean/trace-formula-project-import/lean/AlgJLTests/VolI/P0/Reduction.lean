import AlgJL.VolI.P0.Reduction

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P0/Reduction.lean` at commit 84818d0. Dropped tests of stripped declarations (1): `reduction_instances`. -/


/-!
# Tests for `GL2TF.VolI.P0.Reduction`

Unfolding tests and the exit witness of `I.red.thm:height-lemma` (M4 W1a, statement level).
-/

open GL2TF MeasureTheory Matrix.GeneralLinearGroup

namespace GL2TFTests

/-- Unfolding of `𝔖(ω, t₀)`, `ω₀`, `λ` and `ht`. -/
theorem reduction_defs_eq (ω : Set (unipotent Adele)) (t₀ : ℝ) (x : GL (Fin 2) Adele) :
    siegelSet ω t₀ = {g | ∃ n ∈ ω, ∃ a₁ a₂ : ℝˣ, 0 < (a₁ : ℝ) ∧ 0 < (a₂ : ℝ) ∧ (a₁ : ℝ) * a₂ = 1 ∧
        t₀ ≤ (a₁ : ℝ) / a₂ ∧ ∃ k ∈ maxCompactAdelic, g = (n : GL (Fin 2) Adele) * infEmb (diagElt a₁ a₂) * k} ∧
      siegelOmegaZero = {n : unipotent Adele | ∃ u : ℝ, u ∈ Set.Icc (-(1 / 2)) (1 / 2) ∧
        (n : GL (Fin 2) Adele) = upperRightHom ((u, 0) : Adele)} ∧
      primitiveNorm x = sInf (Set.range fun δ : GL (Fin 2) ℚ ↦ bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ * x)) ∧
      height x = Real.log (ideleNorm (Matrix.GeneralLinearGroup.det x)) - 2 * Real.log (primitiveNorm x) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The Siegel set is non-empty: `1 = n(0) · diag(1, 1) · 1 ∈ 𝔖(ω₀, t₀)` for `t₀ ≤ 1`. -/
theorem one_mem_siegelSet (t₀ : ℝ) (ht₀ : t₀ ≤ 1) : (1 : GL (Fin 2) Adele) ∈ siegelSet siegelOmegaZero t₀ := by
  refine ⟨1, ⟨0, by norm_num, by rw [Prod.mk_zero_zero, AddChar.map_zero_eq_one]; rfl⟩, 1, 1, by norm_num, by norm_num, by norm_num, by simpa using ht₀, 1,
    maxCompactAdelic.one_mem, ?_⟩
  have : diagElt (1 : ℝˣ) 1 = 1 := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagElt]
  rw [this, map_one, OneMemClass.coe_one, one_mul, one_mul]

/-- The right action of `G(𝔸)^1` on `G(ℚ)\G(𝔸)^1` on representatives: `(G(ℚ)x)·g = G(ℚ)xg` by definition. -/
theorem automorphicRightAction_mk (x g : normOneGroup) :
    MulOpposite.op g • (Quotient.mk _ x : MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) =
      Quotient.mk _ (x * g) :=
  rfl

/-! ### Exit witness for `I.red.thm:height-lemma` -/

/-- `x₀ = diag(2, ½)` at `∞`, `1` at every `p`. -/
noncomputable def witnessX : GL (Fin 2) Adele := infEmb (diagElt (Units.mk0 (2 : ℝ) two_ne_zero) (Units.mk0 (2 : ℝ) two_ne_zero)⁻¹)

/-- `n(1) ∈ B(ℚ)`, the second element of the coset `B(ℚ)·1`. -/
noncomputable def witnessDelta : GL (Fin 2) ℚ := upperRightHom (1 : ℚ)

theorem witnessX_entry_inf (i j : Fin 2) :
    ((witnessX : Matrix (Fin 2) (Fin 2) Adele) i j).1 =
      ((diagElt (Units.mk0 (2 : ℝ) two_ne_zero) (Units.mk0 (2 : ℝ) two_ne_zero)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  show ((compInf witnessX : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [witnessX, compInf_infEmb]

theorem witnessX_entry_fin (i j : Fin 2) (p : Nat.Primes) :
    ((witnessX : Matrix (Fin 2) (Fin 2) Adele) i j).2 p = (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
  show ((compFinPlace p (compFin witnessX) : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j = _
  rw [witnessX, compFin_infEmb, map_one, Units.val_one]

theorem witnessX_bottomRowNorm : bottomRowNorm witnessX = 1 / 2 := by
  rw [bottomRowNorm]
  simp only [witnessX_entry_inf, witnessX_entry_fin]
  simp [diagElt, Local.normAbs_padic]

theorem witnessX_det : ideleNorm (Matrix.GeneralLinearGroup.det witnessX) = 1 := by
  show ideleNormFun _ = 1
  rw [ideleNormFun, det_adele_val, witnessX, compInf_infEmb, compFin_infEmb, map_one, Units.val_one]
  simp [diagElt, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Local.normAbs_padic]

theorem witness_bottom_row (δ : GL (Fin 2) ℚ) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0)
    (hδ' : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1) :
    bottomRowNorm (gl2Map (algebraMap ℚ Adele) δ * witnessX) = bottomRowNorm witnessX := by
  have e : ∀ j, ((gl2Map (algebraMap ℚ Adele) δ * witnessX : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 j =
      (witnessX : Matrix (Fin 2) (Fin 2) Adele) 1 j := fun j ↦ by
    simp [gl2Map, Matrix.GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_two, hδ, hδ', Prod.mk_zero_zero,
      Prod.mk_one_one]
  simp only [bottomRowNorm, e]

/-- `α(H_B(δx₀)) = log 4` for `δ = 1` and `δ = n(1)`. -/
theorem witness_simpleRoot (δ : GL (Fin 2) ℚ) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0)
    (hδ' : (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1) :
    simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ * witnessX)) = Real.log 4 := by
  rw [simpleRoot_heightMap, witness_bottom_row δ hδ hδ', witnessX_bottomRowNorm]
  have hdet : ideleNorm (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) δ * witnessX)) = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) δ) =
        ratIdele (Matrix.GeneralLinearGroup.det δ) := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.det, gl2Map, ratIdele, RingHom.map_det]
    rw [map_mul, map_mul, h1, product_formula, one_mul, witnessX_det]
  rw [hdet, Real.log_one, show (4 : ℝ) = (1 / 2)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
  push_cast; ring

/-- The hypotheses of `I.red.thm:height-lemma` hold non-degenerately for `x₀ = diag(2, ½)_∞`, `t₀ = 1`, `δ = 1`,
`δ' = n(1)`: `x₀ ∈ G(𝔸)^1` and `α(H_B(δx₀)) = α(H_B(δ'x₀)) = log 4 > 0 = log 1`. -/
theorem height_lemma_witness_hyps :
    witnessX ∈ normOneGroup ∧
      Real.log 1 < simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) 1 * witnessX)) ∧
      Real.log 1 < simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) witnessDelta * witnessX)) := by
  have h4 : Real.log 1 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨witnessX_det, ?_, ?_⟩
  · rw [witness_simpleRoot 1 (by simp) (by simp)]; exact h4
  · rw [witness_simpleRoot witnessDelta (by simp [witnessDelta, upperRightHom])
      (by simp [witnessDelta, upperRightHom])]; exact h4

/-- Exit witness: `I.red.thm:height-lemma` fully applied to `x₀`, `t₀ = 1`, `δ = 1`, `δ' = n(1)`. -/
theorem height_lemma_witness : witnessDelta * 1⁻¹ ∈ GL2TF.borel ℚ :=
  height_lemma witnessX height_lemma_witness_hyps.1 1 le_rfl 1 witnessDelta height_lemma_witness_hyps.2.1
    height_lemma_witness_hyps.2.2

/-! ### Exit witness for `I.red.thm:compactness-criterion` (G1 falsifier W1) -/

/-- `x_s = diag(s, s⁻¹)` at `∞`, `1` at every `p`. -/
noncomputable def splitDiag (s : ℝ) (hs : s ≠ 0) : GL (Fin 2) Adele :=
  infEmb (diagElt (Units.mk0 s hs) (Units.mk0 s hs)⁻¹)

theorem splitDiag_entry_inf (s : ℝ) (hs : s ≠ 0) (i j : Fin 2) :
    ((splitDiag s hs : Matrix (Fin 2) (Fin 2) Adele) i j).1 =
      ((diagElt (Units.mk0 s hs) (Units.mk0 s hs)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  show ((compInf (splitDiag s hs) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [splitDiag, compInf_infEmb]

theorem splitDiag_entry_fin (s : ℝ) (hs : s ≠ 0) (i j : Fin 2) (p : Nat.Primes) :
    ((splitDiag s hs : Matrix (Fin 2) (Fin 2) Adele) i j).2 p = (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
  show ((compFinPlace p (compFin (splitDiag s hs)) : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j = _
  rw [splitDiag, compFin_infEmb, map_one, Units.val_one]

theorem splitDiag_bottomRowNorm (s : ℝ) (hs : s ≠ 0) : bottomRowNorm (splitDiag s hs) = |s⁻¹| := by
  rw [bottomRowNorm]
  simp only [splitDiag_entry_inf, splitDiag_entry_fin]
  simp [diagElt, Local.normAbs_padic, Real.sqrt_sq_eq_abs]

theorem splitDiag_det (s : ℝ) (hs : s ≠ 0) : ideleNorm (Matrix.GeneralLinearGroup.det (splitDiag s hs)) = 1 := by
  show ideleNormFun _ = 1
  rw [ideleNormFun, det_adele_val, splitDiag, compInf_infEmb, compFin_infEmb, map_one, Units.val_one]
  simp [diagElt, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Local.normAbs_padic, hs]

/-- `α(H_B(diag(s, s⁻¹)_∞)) = 2 log s`. -/
theorem splitDiag_simpleRoot (s : ℝ) (hs : 0 < s) :
    simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) 1 * splitDiag s hs.ne')) = 2 * Real.log s := by
  rw [map_one, one_mul, simpleRoot_heightMap, splitDiag_det, splitDiag_bottomRowNorm, Real.log_one, abs_inv,
    abs_of_pos hs, Real.log_inv]
  ring

/-- The right side of the compactness criterion fails for `Ω = G(ℚ)\G(𝔸)^1`: heights are unbounded on `G(𝔸)^1`. -/
theorem heights_unbounded :
    ¬ ∃ c : ℝ, ∀ x : normOneGroup, Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) x ∈ Set.univ →
        ∀ δ : GL (Fin 2) ℚ, simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) δ * x)) ≤ c := by
  rintro ⟨c, hc⟩
  set s := Real.exp (|c| + 1) with hsdef
  have hs : 0 < s := Real.exp_pos _
  have hmem : splitDiag s hs.ne' ∈ normOneGroup := splitDiag_det s hs.ne'
  have := hc ⟨splitDiag s hs.ne', hmem⟩ (Set.mem_univ _) 1
  rw [show ((⟨splitDiag s hs.ne', hmem⟩ : normOneGroup) : GL (Fin 2) Adele) = splitDiag s hs.ne' from rfl,
    splitDiag_simpleRoot s hs, hsdef, Real.log_exp] at this
  linarith [le_abs_self c, abs_nonneg c]

/-- Exit witness: `I.red.thm:compactness-criterion` fully applied to `Ω = G(ℚ)\G(𝔸)^1` gives that
`G(ℚ)\G(𝔸)^1` is not compact (its right side fails by `heights_unbounded`). -/
theorem compactness_criterion_witness :
    ¬ IsCompact (closure (Set.univ : Set (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup))) :=
  fun h ↦ heights_unbounded ((compactness_criterion Set.univ).1 h)

/-! ### Exit witness for `I.red.thm:compactness-criterion`, direction (⇐) (G3 falsifier) -/

theorem simpleRoot_rat_primitive (γ : GL (Fin 2) ℚ) (m n : ℤ) (hmn : Int.gcd m n = 1)
    (hm : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = m) (hn : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = n) :
    simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) γ * 1)) =
      -2 * Real.log (Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) := by
  rw [simpleRoot_heightMap, ideleNorm_det_rat_mul, mul_one, bottomRowNorm_primitive γ m n hmn hm hn, map_one,
    map_one, Real.log_one]
  ring

theorem simpleRoot_borel_mul (β : GL (Fin 2) ℚ) (hβ : β ∈ GL2TF.borel ℚ) (g : GL (Fin 2) Adele) :
    simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) β * g)) = simpleRoot (heightMap g) := by
  rw [simpleRoot_heightMap, simpleRoot_heightMap, ideleNorm_det_rat_mul, bottomRowNorm_borel_mul β hβ]

theorem simpleRoot_rat_le_zero (γ : GL (Fin 2) ℚ) :
    simpleRoot (heightMap (gl2Map (algebraMap ℚ Adele) γ * 1)) ≤ 0 := by
  obtain ⟨β, hβ, m, n, hmn, hm, hn⟩ := exists_borel_primitive γ
  have e : gl2Map (algebraMap ℚ Adele) γ * 1 =
      gl2Map (algebraMap ℚ Adele) β⁻¹ * (gl2Map (algebraMap ℚ Adele) (β * γ) * 1) := by
    rw [map_mul, map_inv]; group
  rw [e, simpleRoot_borel_mul β⁻¹ (Subgroup.inv_mem _ hβ), simpleRoot_rat_primitive _ m n hmn hm hn]
  have := one_le_sqrt_coprime m n hmn
  have : 0 ≤ Real.log (Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) := Real.log_nonneg this
  linarith

/-- Exit witness: (⇐) of `I.red.thm:compactness-criterion` fully applied to `Ω = {G(ℚ)·1}` with `c = 0`, proved by
hand for all `δ ∈ G(ℚ)`. -/
theorem singleton_compact_witness :
    IsCompact (closure ({Quotient.mk _ (1 : normOneGroup)} :
      Set (MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup))) := by
  rw [compactness_criterion]
  refine ⟨0, fun x hx δ ↦ ?_⟩
  have hx' : (Quotient.mk _ x : MulAction.orbitRel.Quotient gl2RatNormOne normOneGroup) = Quotient.mk _ 1 := hx
  obtain ⟨γ, hγ⟩ := Quotient.exact hx'
  obtain ⟨γ₀, hγ₀⟩ := gl2RatNormOne_rat γ
  have e1 : (x : normOneGroup) = (γ : normOneGroup) := by rw [← hγ]; exact mul_one _
  have e : ((x : normOneGroup) : GL (Fin 2) Adele) = gl2Map (algebraMap ℚ Adele) γ₀ := by rw [e1, hγ₀]
  rw [e, ← map_mul, ← mul_one (gl2Map (algebraMap ℚ Adele) (δ * γ₀))]
  exact simpleRoot_rat_le_zero _

end GL2TFTests
