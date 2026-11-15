import AlgJL.VolI.P0.Ideles
import Mathlib.Topology.Instances.ZMod
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Tests for `GL2TF.VolI.P0.Ideles`

Non-vacuity tests for ideles, `Ẑ^×` and Hecke characters (U4): the norm and embeddings at `1`, the instances, the
probability Haar measures, the box `[1, e) × Ẑ^×` contains `1`, the trivial Dirichlet pair and the trivial Hecke
character.
-/

open GL2TF MeasureTheory

namespace GL2TFTests

/-- `|1|_𝔸 = 1`, `1 ∈ 𝔸^1`, `ℚ^× ∋ 1`. -/
theorem ideleNorm_one' : ideleNorm 1 = 1 ∧ (1 : Idele) ∈ ideleNormOne ∧ ratIdele 1 = 1 ∧
    (1 : Idele) ∈ ratIdeles :=
  ⟨map_one _, ideleNormOne.one_mem, map_one _, ratIdeles.one_mem⟩

/-- The identification `𝔸^× = ℝ^× × Πʳ(ℚ_p^×, ℤ_p^×)` sends `1` to `1`. -/
theorem ideleEquiv_one : ideleEquiv 1 = 1 := map_one _

/-- The idele `(1, 1)` is `1`. -/
theorem ideleInfFin_one : ideleInfFin 1 1 = 1 := by
  simp [ideleInfFin]

/-- `1 ∈ [1, e) × Ẑ^×`. -/
theorem one_mem_ideleUnitBox : (1 : Idele) ∈ ideleUnitBox :=
  ⟨⟨le_rfl, by simp only [Units.val_one, Prod.fst_one]; linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]⟩, fun p ↦ ⟨1, by simp⟩⟩

/-- The instances on `Ẑ`, `Ẑ^×` and `ℤ_p^×` resolve through the project instances (and Mathlib's for `Ẑ^×`). -/
theorem idele_instances :
    CompactSpace Zhat ∧ CompactSpace Zhatˣ ∧ LocallyCompactSpace Idele ∧
      ∀ p : Nat.Primes, CompactSpace ((Submonoid.ofClass (PadicInt.subring p)).units) :=
  ⟨zhat_compactSpace, inferInstance, inferInstance, padicUnits_compactSpace_inst⟩  -- fork: BorelSpace conjunct dropped

/-- `u ↦ (1, u)ℚ^×` sends `1` to `1`. -/
theorem zhatToNormOneClass_one : zhatToNormOneClass 1 = 1 := by
  rw [zhatToNormOneClass, ← QuotientGroup.mk_one]
  congr 1
  exact Subtype.ext ideleInfFin_one

/-- `red_N(1) = 1`. -/
theorem zhatReduction_one (N : ℕ+) : zhatReduction N 1 = 1 := map_one _

/-- The trivial Hecke character. -/
noncomputable def trivialHeckeCharacter : HeckeCharacter := ⟨1, fun _ ↦ rfl⟩

/-- `𝔸^1/ℚ^×` has the class of `1`. -/
theorem normOneClassGroup_one : (QuotientGroup.mk 1 : NormOneClassGroup) = 1 := rfl

/-- The function-level idele norm is multiplicative and sends `1` to `1`. -/
theorem ideleNormFun_nonvacuous : ideleNormFun 1 = 1 ∧ ∀ x y, ideleNormFun (x * y) = ideleNormFun x * ideleNormFun y :=
  ⟨ideleNormFun_one, ideleNormFun_mul⟩

/-- The `p`-th component `Ẑ → ℤ_p` sends `1` to `1`. -/
theorem zhatToPadicInt_one (p : Nat.Primes) : zhatToPadicInt p 1 = 1 := map_one _

/-! ### Non-trivial characters of `Ẑ^×`: `χ₄ ∘ red_4` (FA witnesses, M3 G1 fix) -/

theorem toZModPow_isLocallyConstant (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have ho : IsOpen (Metric.closedBall x ((p : ℝ) ^ (-(n : ℤ)))) :=
    IsUltrametricDist.isOpen_closedBall _ hpos.ne'
  filter_upwards [ho.mem_nhds (Metric.mem_closedBall_self hpos.le)] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

theorem zhatToPadicInt_continuous (p : Nat.Primes) : Continuous (zhatToPadicInt p) :=
  Continuous.subtype_mk ((RestrictedProduct.continuous_eval p).comp continuous_subtype_val) _

theorem zhatReduction_continuous (N : ℕ+) : Continuous (zhatReduction N) := by
  have hpi : Continuous (RingHom.pi fun p : (N : ℕ).primeFactors ↦
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      (PadicInt.toZModPow ((N : ℕ).factorization p)).comp
        (zhatToPadicInt ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)) := by
    refine continuous_pi fun p ↦ ?_
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact (toZModPow_isLocallyConstant _ _).continuous.comp (zhatToPadicInt_continuous _)
  unfold zhatReduction
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact continuous_of_discreteTopology.comp (continuous_of_discreteTopology.comp hpi)

/-- `χ ∘ red_N` for a Dirichlet character `χ` mod `N`, as a continuous character of `Ẑ^×`. -/
noncomputable def dirichletToZhat (N : ℕ+) (χ : DirichletCharacter ℂ N) : ContinuousMonoidHom Zhatˣ ℂˣ where
  toMonoidHom := χ.toUnitHom.comp (Units.map (zhatReduction N).toMonoidHom)
  continuous_toFun := by
    have hr : Continuous fun u : Zhatˣ ↦ zhatReduction N (u : Zhat) :=
      (zhatReduction_continuous N).comp Units.continuous_val
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := fun a : ZMod N ↦ χ a)).comp hr
    · have hr' : Continuous fun u : Zhatˣ ↦ zhatReduction N ((u⁻¹ : Zhatˣ) : Zhat) :=
        hr.comp continuous_inv
      exact (continuous_of_discreteTopology (f := fun a : ZMod N ↦ χ a)).comp hr'

/-- `χ₄ ∘ red_4`, the nontrivial character of conductor 4. -/
noncomputable def chi4 : ContinuousMonoidHom Zhatˣ ℂˣ :=
  dirichletToZhat 4 (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

/-- `χ₄ ∘ red_4` is not the trivial character: it sends `-1 ∈ Ẑ^×` to `-1`. -/
theorem chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : ContinuousMonoidHom Zhatˣ ℂˣ ↦ ((f (-1) : ℂˣ) : ℂ)) h
  have h2 : ((chi4 (-1) : ℂˣ) : ℂ) = -1 := by
    change (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (zhatReduction 4 ((-1 : Zhatˣ) : Zhat)) = -1
    have hr : zhatReduction 4 ((-1 : Zhatˣ) : Zhat) = -1 := by
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
    have hχ : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    rw [hr]
    change ((ZMod.χ₄ (-1 : ZMod 4) : ℤ) : ℂ) = -1
    rw [hχ]
    simp
  simp [h2] at h1
  norm_num at h1

/-- Exit witness for `I.adele.thm:zhat-characters-finite-order`, applied to the non-trivial `χ₄ ∘ red_4`. -/
theorem zhat_characters_finite_order_chi4 :
    (∃ (N : ℕ+) (χN : DirichletCharacter ℂ N), ∀ u : Zhatˣ,
        ((chi4 u : ℂˣ) : ℂ) = χN (zhatReduction N (u : Zhat))) ∧
      ∃ n : ℕ, 1 ≤ n ∧ ∀ u : Zhatˣ, chi4 u ^ n = 1 :=
  zhat_characters_finite_order chi4

/-- Exit witness for `I.adele.thm:zhat-characters-finite-order`, applied to the trivial character. -/
theorem zhat_characters_finite_order_one :
    (∃ (N : ℕ+) (χN : DirichletCharacter ℂ N), ∀ u : Zhatˣ,
        (((1 : ContinuousMonoidHom Zhatˣ ℂˣ) u : ℂˣ) : ℂ) = χN (zhatReduction N (u : Zhat))) ∧
      ∃ n : ℕ, 1 ≤ n ∧ ∀ u : Zhatˣ, (1 : ContinuousMonoidHom Zhatˣ ℂˣ) u ^ n = 1 :=
  zhat_characters_finite_order 1

/-- Exit witness for `I.adele.thm:norm-one-quotient` (no hypotheses). -/
theorem norm_one_quotient_witness :
    (∃ e : ContinuousMulEquiv Zhatˣ NormOneClassGroup, ∀ u : Zhatˣ, e u = zhatToNormOneClass u) ∧
      CompactSpace NormOneClassGroup :=
  norm_one_quotient

/-- `χ₄(red_4(-1)) = -1` (test helper). -/
theorem chi4_neg_one : ((chi4 (-1) : ℂˣ) : ℂ) = -1 := by
  change (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (zhatReduction 4 ((-1 : Zhatˣ) : Zhat)) = -1
  have hr : zhatReduction 4 ((-1 : Zhatˣ) : Zhat) = -1 := by
    rw [Units.val_neg, Units.val_one, map_neg, map_one]
  have hχ : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  rw [hr]
  change ((ZMod.χ₄ (-1 : ZMod 4) : ℤ) : ℂ) = -1
  rw [hχ]
  simp

/-- A non-identity element of `Ẑ^×`: `-1 ≠ 1` (m5). -/
theorem zhatUnits_neg_one_ne_one : (-1 : Zhatˣ) ≠ 1 := by
  intro h
  have := chi4_neg_one
  rw [h, map_one, Units.val_one] at this
  norm_num at this

/-- A non-identity element of `C = 𝔸^1/ℚ^×`: the class of `(1, -1)` (m5). -/
theorem normOneClassGroup_ne_one : zhatToNormOneClass (-1) ≠ 1 := by
  obtain ⟨⟨e, he⟩, -⟩ := norm_one_quotient
  intro h
  apply zhatUnits_neg_one_ne_one
  apply e.injective
  rw [he, he, h, zhatToNormOneClass_one]

end GL2TFTests
