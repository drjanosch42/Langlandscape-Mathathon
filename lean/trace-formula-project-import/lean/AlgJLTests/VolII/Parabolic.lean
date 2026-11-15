import AlgJL.VolII.Parabolic

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolII/Parabolic.lean` at commit 84818d0. Dropped tests of stripped declarations (3): `gtValue_linear`, `not_isGTFamily_const`, `weight_one`. -/


/-!
# Tests for `GL2TF.VolII.Parabolic`

Witnesses for the tagged definitions of M7a U4 (W1, statement level): the index sets and subgroups, `w` on `𝔞_B`,
`H_P` at `x = 1` and `x = w`, `Y_P`, `α^∨`, `Λ_λ`, `θ_P`, a `(G,T)`-family with value `1` and a non-family, and the weight
at `x = 1` for `T = (1, 0)` (`α(T) = 1 ≠ 0`).
-/

open GL2TF Filter Topology

namespace GL2TFTests

/-- `𝒫(T)` has two elements; `B̄ ↦ B̄(ℚ)`, `G ↦ GL₂(ℚ)`, both `B`s map to `B(ℚ)`. -/
theorem parabolic_values :
    Fintype.card ParT = 2 ∧ parabolic ℚ (.inr .Bbar) = oppositeBorel ℚ ∧ parabolic ℚ (.inl ParStd.G) = ⊤ ∧
      parabolic ℚ (.inl ParStd.B) = parabolic ℚ (.inr ParT.B) ∧ ParStd.B ≠ ParStd.G ∧ ParT.B ≠ ParT.Bbar :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- `w(1, 2) = (2, 1)`, `α^∨ = (1, −1)`, `Λ_λ(α^∨) = λ` at `λ = 3`, `θ_B̄(2) = −2`. -/
theorem weylAct_coroot_lamForm_theta :
    weylAct ![1, 2] = ![2, 1] ∧ simpleRoot coroot = 2 ∧ lamForm 3 coroot = 3 ∧ theta .Bbar 2 = -2 ∧ theta .B 2 = 2 := by
  refine ⟨?_, ?_, (lamForm_spec 3).1, rfl, rfl⟩
  · ext i; fin_cases i <;> rfl
  · simp [simpleRoot, coroot]; norm_num

/-- `H_B(1) = 0`. -/
theorem heightMap_one : heightMap 1 = 0 := by
  have h := (heightMap_equivariance.2 1 (Subgroup.one_mem _) 1)
  simpa using h.2

/-- `H_B(1) = 0` and `H_B̄(w) = w·H_B(1) = 0`. -/
theorem heightP_one_weyl : heightP .B 1 = 0 ∧ heightP .Bbar (weylElement Adele) = 0 := by
  refine ⟨heightMap_one, ?_⟩
  show weylAct (heightMap ((weylElement Adele)⁻¹ * weylElement Adele)) = 0
  rw [inv_mul_cancel, heightMap_one]
  ext i; fin_cases i <;> rfl

/-- `Y_B(1, T) = T_B^G`. -/
theorem yVec_one (T : SpaceAB) : yVec .B 1 T = projABG T := by
  show projABG (T - heightMap 1) = projABG T
  rw [heightMap_one, sub_zero]

end GL2TFTests
