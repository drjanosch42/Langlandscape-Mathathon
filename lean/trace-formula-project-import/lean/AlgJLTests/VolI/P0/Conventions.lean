import AlgJL.VolI.P0.Conventions

/-!
# Tests for `GL2TF.VolI.P0.Conventions`

Non-vacuity examples (PLAN.md §2.3) for `K(R)`, `B`, `T`, `N`, `w`, `K_∞`, `SO(2)`, `k_θ`.
-/

namespace GL2TFTests

/-- `K(R)` contains the image of every element of `GL₂(R)`. -/
theorem map_mem_maxCompact {R F : Type*} [CommRing R] [Field F] (ι : R →+* F) (A : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map ι A ∈ GL2TF.maxCompact ι :=
  ⟨A, rfl⟩

open GL2TF Matrix Matrix.GeneralLinearGroup

/-- `diag(t₁, t₂) ∈ T(R)`. -/
theorem diagElt_mem_torus {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) : diagElt t₁ t₂ ∈ torus R := by
  simp [torus, diagElt]

/-- `T(R) ≤ B(R)` on an element: `diag(t₁, t₂) ∈ B(R)`. -/
theorem diagElt_mem_borel {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) : diagElt t₁ t₂ ∈ borel R := by
  simp [borel, diagElt]

/-- `n(x) ∈ N(R)` and `n(x) ∈ B(R)`. -/
theorem upperRightHom_mem_unipotent_borel {R : Type*} [CommRing R] (x : R) :
    upperRightHom x ∈ unipotent R ∧ upperRightHom x ∈ borel R :=
  ⟨⟨x, rfl⟩, by simp [borel]⟩

/-- `w ∉ B(ℚ)`, and `w² = −1`. -/
theorem weylElement_not_mem_borel_sq :
    weylElement ℚ ∉ borel ℚ ∧
      ((weylElement ℚ * weylElement ℚ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = -1 := by
  refine ⟨by simp [borel, weylElement], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [weylElement]

/-- `k_0 = 1` lies in `SO(2)`, and `−1 ∈ SO(2)` (so `SO(2) ∩ B(ℝ) ∋ ±1`). -/
theorem rotation_zero_neg_one_mem_specialOrthogonalReal :
    rotation 0 = 1 ∧ (-1 : GL (Fin 2) ℝ) ∈ specialOrthogonalReal := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [rotation_val], ?_, ?_⟩
  · show ((-1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * _ = 1
    simp
  · simp [Units.ext_iff, det_fin_two]

/-- `k_θ ∈ K_∞` (named test of `maxCompactReal` and `rotation`). -/
theorem rotation_mem_maxCompactReal' (θ : ℝ) : rotation θ ∈ maxCompactReal :=
  rotation_mem_maxCompactReal θ

/-! ### M3 U1: structure of `GL₂`, `𝔞_B` -/

/-- `f_*` is Mathlib's entrywise map. -/
theorem gl2Map_eq {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') :
    gl2Map f = Matrix.GeneralLinearGroup.map f :=
  rfl

/-- The scalar matrix `u · 1` lies in `Z(R)` for every unit `u`. -/
theorem scalar_mem_center {R : Type*} [CommRing R] (u : Rˣ) :
    Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom u ∈ center R :=
  ⟨u, rfl⟩

/-- `n̄(x) ∈ N̄(R)`, `n̄(x) ∈ B̄(R)`, and `n̄(1) ∉ B(ℚ)`; `w ∉ B̄(ℚ)`. -/
theorem oppositeUnipotent_mem {R : Type*} [CommRing R] (x : R) :
    oppositeUnipotentHom x ∈ oppositeUnipotent R ∧ oppositeUnipotentElt x ∈ oppositeBorel R ∧
      oppositeUnipotentElt (1 : ℚ) ∉ borel ℚ ∧ weylElement ℚ ∉ oppositeBorel ℚ := by
  refine ⟨⟨Multiplicative.ofAdd x, rfl⟩, ?_, ?_, ?_⟩
  · show !![(1 : R), 0; x, 1] 0 1 = 0
    simp
  · show ¬ !![(1 : ℚ), 0; 1, 1] 1 0 = 0
    simp
  · show ¬ !![(0 : ℚ), 1; -1, 0] 0 1 = 0
    simp

/-- `α(1, 0) = 1`, `ρ(1, 0) = 1/2`, `τ_B(1, 0) = 1`, `τ̂_B(0, 1) = 0`, `(1, −1) ∈ 𝔞_B^G`, and
`(1, 0)_B^G = (1/2, −1/2)`. -/
theorem rootData_values :
    simpleRoot (![1, 0] : SpaceAB) = 1 ∧ rho (![1, 0] : SpaceAB) = 1 / 2 ∧ tauB ![1, 0] = 1 ∧
      tauHatB ![0, 1] = 0 ∧ (![1, -1] : SpaceAB) ∈ spaceABG ∧
      projABG ![1, 0] = ![1 / 2, -1 / 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [simpleRoot]
  · simp [rho, simpleRoot]
  · simp [tauB, simpleRoot, Set.indicator]
  · simp [tauHatB, simpleRoot, Set.indicator]
  · simp [spaceABG]
  · ext i; fin_cases i <;> norm_num [projABG, simpleRoot]

/-- `diagHom` is `(t₁, t₂) ↦ diag(t₁, t₂)`. -/
theorem diagHom_apply {R : Type*} [CommRing R] (t : Rˣ × Rˣ) : diagHom R t = diagElt t.1 t.2 :=
  rfl

end GL2TFTests
