import AlgJL.VolI.P1.HeckeBasis

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/HeckeBasis.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolI.P1.HeckeBasis`

Named tests of the tagged definitions of M5a U0 (PLAN.md §2.3), at `F = ℚ_p`.
-/

open ValuativeRel GL2TF GL2TF.Local
open scoped Pointwise

namespace GL2TFTests

theorem cartanElement_padic_zero_zero (p : ℕ) [Fact p.Prime] : cartanElement ℚ_[p] 0 0 = 1 := by
  apply Units.ext
  rw [cartanElement_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `I.satake.def:hecke-basis`: `c_{0,0} = 1_K` is the unit of `H(GL₂(ℚ_p), K)`. -/
theorem heckeBasis_padic_zero_zero (p : ℕ) [Fact p.Prime] : heckeBasis ℚ_[p] 0 0 = 1 :=
  HeckePair.heckeIndicator_of_mem (by rw [cartanElement_padic_zero_zero]; exact one_mem _) _

/-- `I.satake.def:hecke-basis`: `c_{a,b}(t_{a,b}) = 1`. -/
theorem heckeBasis_padic_apply_cartan (p : ℕ) [Fact p.Prime] (a b : ℤ) :
    ((heckeBasis ℚ_[p] a b : sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ) (cartanElement ℚ_[p] a b) = 1 :=
  heckeBasis_apply_of_mem (DoubleCoset.mem_doubleCoset_self _ _ _)

/-- `X.hpair.def:double-coset`: the vendored double coset `U g U` is Mathlib's `DoubleCoset.doubleCoset g U U`. -/
theorem heckePair_doubleCoset_padic (p : ℕ) [Fact p.Prime] (g : GL (Fin 2) ℚ_[p]) :
    HeckePair.doubleCoset 𝐊[ℚ_[p]] g = DoubleCoset.doubleCoset g 𝐊[ℚ_[p]] 𝐊[ℚ_[p]] := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

/-- `X.hpair.def:hecke-indicator`: the indicator of `K · 1 · K = K` is the unit `1_K`. -/
theorem heckeIndicator_padic_one (p : ℕ) [Fact p.Prime]
    (hfin : (QuotientGroup.mk '' ((𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p])) * {1}) :
      Set (GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]])).Finite) :
    HeckePair.heckeIndicator ℂ (1 : GL (Fin 2) ℚ_[p]) hfin = (1 : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) :=
  HeckePair.heckeIndicator_of_mem (one_mem _) hfin

/-- `I.satake.def:upper-coset-matrix`: `h(i, j, x) = (ϖ^i x; 0 ϖ^j)` over `ℚ_p`. -/
theorem hmat_padic_val (p : ℕ) [Fact p.Prime] (i j : ℤ) (x : ℚ_[p]) :
    ((hmat i j x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![((unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) ^ i, x; 0, ((unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) ^ j] :=
  hmat_val i j x

/-- `I.satake.def:hecke-comm-ring`: `H(GL₂(ℚ_p), K)` is a commutative ring (the multiplication of the instance is the
convolution). -/
theorem sphericalHeckeAlgebra_padic_commRing_mul (p : ℕ) [Fact p.Prime] (f₁ f₂ : sphericalHeckeAlgebra ℚ_[p]) :
    @HMul.hMul _ _ _ (@instHMul _ (sphericalHeckeAlgebra_commRing ℚ_[p]).toMul) f₁ f₂ = f₂ * f₁ :=
  mul_comm f₁ f₂

/-- `I.satake.ex:hecke-t-squared` at `ℚ_p`: `T_p² = c_{2,0} + (p + 1) R_p`. -/
theorem hecke_t_squared_padic (p : ℕ) [Fact p.Prime] :
    heckeBasis ℚ_[p] 1 0 * heckeBasis ℚ_[p] 1 0 = heckeBasis ℚ_[p] 2 0 + ((p : ℂ) + 1) • heckeBasis ℚ_[p] 1 1 := by
  rw [hecke_t_squared, q_padic]

/-! Closed instance (M5a FB i-2) of the hypothesis `hR` of `I.satake.lem:left-coset-representatives`: a family of
representative sets exists for every NALF (here `ℚ_[3]`, and then used to apply the lemma). -/

section HRInstance

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- Probe 3: the hypothesis `hR` of `left_coset_representatives` is satisfiable (sets of representatives of
`F / ϖ^i 𝒪`, from `Quotient.out`). -/
theorem left_coset_representatives_hR_satisfiable : ∃ R : ℤ → Set F, ∀ i : ℤ, ∀ x : F, ∃! r : F,
    r ∈ R i ∧ valuation F (x - r) ≤ valuation F (((unif F : 𝒪[F]) : F) ^ i) := by
  classical
  let A : ℤ → AddSubgroup F := fun i =>
    { carrier := {x | valuation F x ≤ valuation F (((unif F : 𝒪[F]) : F) ^ i)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        exact le_trans (Valuation.map_add _ a b) (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [Valuation.map_neg] using ha }
  have key : ∀ i (c : F ⧸ A i) (x : F), x - c.out ∈ A i ↔ c = (x : F ⧸ A i) := by
    intro i c x
    conv_rhs => rw [← QuotientAddGroup.out_eq' c]
    rw [QuotientAddGroup.eq, sub_eq_neg_add]
  refine ⟨fun i => Set.range (fun c : F ⧸ A i => c.out), fun i x => ⟨((x : F ⧸ A i)).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact (key i _ x).2 rfl
  · rintro r ⟨⟨c, rfl⟩, hc⟩
    exact congrArg Quotient.out ((key i c x).1 hc)

end HRInstance

/-- The lemma `left_coset_representatives` applied at `ℚ_[3]` with the representatives of `hR_satisfiable`. -/
theorem left_coset_representatives_padic_three :
    ∃ R : ℤ → Set ℚ_[3], ∀ g : GL (Fin 2) ℚ_[3], ∃! p : ℤ × ℤ × ℚ_[3], p.2.2 ∈ R p.1 ∧
        (g : GL (Fin 2) ℚ_[3] ⧸ 𝐊[ℚ_[3]]) = (hmat p.1 p.2.1 p.2.2 : GL (Fin 2) ℚ_[3] ⧸ 𝐊[ℚ_[3]]) := by
  obtain ⟨R, hR⟩ := left_coset_representatives_hR_satisfiable (F := ℚ_[3])
  exact ⟨R, (left_coset_representatives ℚ_[3] R hR).1⟩

end GL2TFTests
