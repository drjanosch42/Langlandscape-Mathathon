import AlgJL.VolII.KernelClasses
import AlgJLTests.VolII.Centralizer

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolII/KernelClasses.lean` at commit 84818d0. Dropped tests of stripped declarations (20): `classKernel_defs_eq`, `constTermKernel_eq_N`, `witnessOmega`, `witnessOmega_isCompact`, `finitely_many_classes_witness`, `exists_isolating_nhds`, `isoV`, `isoV_spec`, `exists_isoBump`, `isoBump`, `isoBump_spec`, `isoF`, `isoF_continuous`, `isoF_hasCompactSupport`, `isoF_one`, `isoF_eq_zero`, `classKernel_values`, `isoF_unip_integrand`, `integral_isoF_unip_ne_zero`, `constTermKernel_values`. -/


/-!
# Tests for `GL2TF.VolII.KernelClasses`

Witnesses for the tagged definitions of M7a U5 (W1, statement level) and the exit witness of
`II.kernel.thm:finitely-many-classes`. Non-degenerate data: the elliptic `γ_i = (0 −1; 1 0)` (class `(0, 1)`), the
hyperbolic `diag(2, 1/2)` (class `(5/2, 1)`) and `1` (class `(2, 1)`, central-unipotent); `f` the nonzero bump of the M4
tests.
-/

open GL2TF MeasureTheory Polynomial Matrix.GeneralLinearGroup

namespace GL2TFTests

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-- `diag(2, 1/2) ∈ GL₂(ℚ)`. -/
def diagTwoHalf : GL (Fin 2) ℚ := diagElt (Units.mk0 2 two_ne_zero) (Units.mk0 (1 / 2) (by norm_num))

/-- `ratNormOne γ = ι(γ)` and `unipNormOne u = n(u)` in `G(𝔸)`. -/
theorem ratNormOne_unipNormOne_val (γ : GL (Fin 2) ℚ) (u : Adele) :
    ((ratNormOne γ : normOneGroup) : GL (Fin 2) Adele) = ι γ ∧
      ((unipNormOne u : normOneGroup) : GL (Fin 2) Adele) = upperRightHom u :=
  ⟨rfl, rfl⟩

/-- Class fibres: `γ_i ∈ 𝒪_{(0,1)}`, `diag(2, 1/2) ∈ 𝒪_{(5/2,1)}`, `1 ∈ 𝒪_{(2,1)}`, `γ_i ∉ 𝒪_{(2,1)}`. -/
theorem classFibre_examples :
    gammaI ∈ classFibre ((0 : ℚ), 1) ∧ diagTwoHalf ∈ classFibre ((5 / 2 : ℚ), 1) ∧ (1 : GL (Fin 2) ℚ) ∈ classFibre ((2 : ℚ), 1) ∧
      gammaI ∉ classFibre ((2 : ℚ), 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> simp [gammaI, Matrix.trace_fin_two, Matrix.det_fin_two]
  · constructor <;> norm_num [diagTwoHalf, diagElt, Matrix.trace_fin_two, Matrix.det_fin_two]
  · constructor <;> norm_num [Matrix.trace_fin_two]
  · rintro ⟨h, -⟩
    simp [gammaI, Matrix.trace_fin_two] at h

/-- `P_{(t,d)}` is the characteristic polynomial of any `γ ∈ 𝒪_{(t,d)}`. -/
theorem classPoly_eq_charpoly (c : ℚ × ℚˣ) (γ : GL (Fin 2) ℚ) (hγ : γ ∈ classFibre c) :
    classPoly c = Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [Matrix.charpoly_fin_two, classPoly, hγ.1, hγ.2]

/-- One class of each type: `(2, 1)` central-unipotent (`z = 1`), `(5/2, 1)` hyperbolic (`a = 2`, `b = 1/2`), `(0, 1)`
elliptic (`X² + 1`). -/
theorem classType_examples :
    HasClassType ((2 : ℚ), 1) .centralUnipotent ∧ HasClassType ((5 / 2 : ℚ), 1) .hyperbolic ∧
      HasClassType ((0 : ℚ), 1) .elliptic := by
  refine ⟨⟨1, ?_⟩, ⟨Units.mk0 2 two_ne_zero, Units.mk0 (1 / 2) (by norm_num), ?_, ?_⟩, ?_⟩
  · simp only [classPoly, Units.val_one, map_one]
    rw [show (C (2 : ℚ)) = 2 from map_ofNat C 2]
    ring
  · intro h
    have := congrArg Units.val h
    norm_num at this
  · have h1 : C (5 / 2 : ℚ) = C 2 + C (1 / 2) := by rw [← C_add]; norm_num
    have h2 : C ((1 : ℚˣ) : ℚ) = C 2 * C (1 / 2) := by rw [← C_mul]; norm_num
    simp only [classPoly, Units.val_mk0]
    rw [h1, h2]
    ring
  · show Irreducible (classPoly ((0 : ℚ), 1))
    rw [classPoly_eq_charpoly _ _ classFibre_examples.1]
    exact gammaI_isElliptic

theorem unipotent_le_normOne {n : GL (Fin 2) Adele} (hn : n ∈ unipotent Adele) : n ∈ normOneGroup := by
  obtain ⟨u, rfl⟩ := hn; exact (unipNormOne u).2

/-! ### Exit witness for `II.kernel.thm:finitely-many-classes` -/

/-! ### `ClassType` and non-degenerate values of `K_𝒪`, `K_B`, `K_{B,𝒪}` (G1-a m-2, m-3, m-4) -/

/-- The type index `ClassType` has exactly the three constructors, and the class `(5/2, 1)` has exactly one type
(the hyperbolic one). -/
theorem classType_cases_unique :
    (∀ τ : ClassType, τ = .centralUnipotent ∨ τ = .hyperbolic ∨ τ = .elliptic) ∧
      ClassType.centralUnipotent ≠ ClassType.elliptic ∧
      ∃! τ : ClassType, HasClassType ((5 / 2 : ℚ), 1) τ := by
  refine ⟨fun τ ↦ by cases τ <;> simp, by decide, ?_⟩
  obtain ⟨τ, hτ, huniq⟩ := class_trichotomy.1 ((5 / 2 : ℚ), 1)
  exact ⟨τ, hτ, huniq⟩

end GL2TFTests
