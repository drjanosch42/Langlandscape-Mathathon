import AlgJL.VolI.P1.Satake

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/Satake.lean` at commit 84818d0. Dropped tests of stripped declarations (1): `satake_t_squared_value`. -/


/-!
# Tests for `GL2TF.VolI.P1.Satake`

Named tests of the tagged definitions of M5a U1 and the R2d witness of the exit `I.satake.thm:satake-isomorphism`
(PLAN.md §2.3, `docs/specs/r2d_exit_witness.md`). Witness datum: the field `satakeField = ℚ₂` (the only data argument
of the exit); `heckeT2 = T_ϖ ∈ H(GL₂(ℚ₂), K)` is the datum of the supports.
-/

open ValuativeRel GL2TF GL2TF.Local AddMonoidAlgebra
open scoped Pointwise

namespace GL2TFTests

/-- `I.satake.def:laurent-swap`: `s(X) = Y`. -/
theorem laurentSwap_X : laurentSwap (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ)) = single (0, 1) 1 :=
  laurentSwap_single 1 0 1

/-- `I.satake.def:laurent-weyl-invariants`: `X + Y` is invariant, `X` is not. -/
theorem weylInvariants_X_add_Y :
    (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ) + single (0, 1) 1 : AddMonoidAlgebra ℂ (ℤ × ℤ)) ∈ weylInvariants ∧
      (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℤ × ℤ)) ∉ weylInvariants := by
  refine ⟨?_, fun h => ?_⟩
  · rw [mem_weylInvariants, map_add, laurentSwap_single, laurentSwap_single, add_comm]
  · rw [mem_weylInvariants, laurentSwap_single] at h
    have := congrArg (fun P : AddMonoidAlgebra ℂ (ℤ × ℤ) => P.coeff (1, 0)) h
    simp at this

/-- `I.satake.def:coset-transform`: the coset transform of `1_K` for the constant weight `1` is `1`. -/
theorem cosetTransform_padic_one (p : ℕ) [Fact p.Prime] :
    cosetTransform (fun _ : GL (Fin 2) ℚ_[p] => (1 : ℂ)) (1 : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) = 1 :=
  cosetTransform_one _ (fun _ _ _ => rfl) rfl

/-- `I.satake.def:iwasawa-exponent`: the exponent of `h(i, j, x)K` is `(i, j)`. -/
theorem iwasawaExponent_padic_hmat (p : ℕ) [Fact p.Prime] (i j : ℤ) (x : ℚ_[p]) :
    iwasawaExponent (hmat i j x : GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]]) = (i, j) :=
  iwasawaExponent_hmat i j x

/-- `I.satake.def:satake-weight`: `μ(1) = 1`. -/
theorem satakeWeight_padic_one (p : ℕ) [Fact p.Prime] : satakeWeight (1 : GL (Fin 2) ℚ_[p]) = 1 :=
  satakeWeight_one

/-- `I.satake.def:satake-transform`: `𝒮(R_p) = XY` over `ℚ_p`. -/
theorem satake_padic_R (p : ℕ) [Fact p.Prime] :
    satake ℚ_[p] (heckeBasis ℚ_[p] 1 1) = single ((1 : ℤ), (1 : ℤ)) (1 : ℂ) :=
  satake_heckeBasis_diag 1

/-- `I.satake.def:laurent-eval`: `X(α, β) = α`. -/
theorem laurentEval_X (α β : ℂˣ) : laurentEval α β (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ)) = α := by
  simp [laurentEval]

/-! ### The R2d witness of `I.satake.thm:satake-isomorphism` -/

/-- The witness field `ℚ₂` (datum of the exit witness). -/
abbrev satakeField : Type := ℚ_[2]

/-- `T_ϖ = c_{1,0} ∈ H(GL₂(ℚ₂), K)` (datum of the supports). -/
noncomputable def heckeT2 : sphericalHeckeAlgebra satakeField := heckeBasis satakeField 1 0

/-- Exit witness: the Satake isomorphism `H(GL₂(ℚ₂), K) ≅ ℂ[X^{±1}, Y^{±1}]^{S₂}`, `e(f) = 𝒮f`. -/
theorem satake_isomorphism_witness :
    ∃ e : sphericalHeckeAlgebra satakeField ≃ₐ[ℂ] weylInvariants,
      ∀ f : sphericalHeckeAlgebra satakeField, (e f : AddMonoidAlgebra ℂ (ℤ × ℤ)) = satake satakeField f :=
  satake_isomorphism satakeField

/-- Support: `𝒮(T_ϖ) ≠ 𝒮(R_ϖ)` and `𝒮(T_ϖ) ≠ 0` at `ℚ₂` (the transform separates the generators). -/
theorem satake_hecke_basis_ne :
    satake satakeField heckeT2 ≠ satake satakeField (heckeBasis satakeField 1 1) ∧
      satake satakeField heckeT2 ≠ 0 := by
  obtain ⟨hT, hR, -⟩ := satake_generators satakeField
  have hs : ((Real.sqrt (q satakeField : ℝ) : ℝ) : ℂ) ≠ 0 := sqrtq_ne_zero
  have hc : (satake satakeField heckeT2).coeff (1, 0) = ((Real.sqrt (q satakeField : ℝ) : ℝ) : ℂ) := by
    rw [heckeT2, hT]; simp
  refine ⟨fun h => hs ?_, fun h => hs ?_⟩
  · rw [← hc, h, hR, single_mul_single]; simp
  · rw [← hc, h]; simp

end GL2TFTests
