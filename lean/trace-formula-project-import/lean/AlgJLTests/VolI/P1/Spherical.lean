import AlgJL.VolI.P1.Spherical

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/Spherical.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolI.P1.Spherical`

Non-vacuity examples and proved instances (PLAN.md §2.3).
-/

open GL2TF GL2TF.Local

namespace GL2TFTests

/-- The spherical Hecke algebra of `ℚ_[p]` has its unit `1_K` (the type is inhabited by the vendored `One`). -/
noncomputable example (p : ℕ) [Fact p.Prime] : sphericalHeckeAlgebra ℚ_[p] := 1

/-- `transposeGL` is the matrix transpose on the underlying matrices. -/
theorem transposeGL_val {F : Type*} [Field F] (g : GL (Fin 2) F) :
    ((transposeGL g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F).transpose :=
  rfl

/-- `1_K` is a left unit of `H(GL₂(ℚ_p), K)` (named test of `sphericalHeckeAlgebra`). -/
theorem sphericalHeckeAlgebra_padic_one_mul (p : ℕ) [Fact p.Prime] (f : sphericalHeckeAlgebra ℚ_[p]) :
    1 * f = f :=
  one_mul f

/-- `H(GL₂(ℚ_p), K)` is commutative: the exit theorem at the model NALF. -/
theorem sphericalHeckeAlgebra_padic_mul_comm (p : ℕ) [Fact p.Prime] (f₁ f₂ : sphericalHeckeAlgebra ℚ_[p]) :
    f₁ * f₂ = f₂ * f₁ :=
  hecke_commutative ℚ_[p] f₁ f₂

/-! ### Named tests of the vendored B-only `X.hpair.*` plumbing, at `(GL₂(ℚ_p), K)` -/

/-- `X.hpair.def:is-hecke-fun`, `X.hpair.def:hecke-algebra`: every element of `H(GL₂(ℚ_p), K)` is a Hecke function. -/
theorem heckeAlgebra_padic_isHeckeFun (p : ℕ) [Fact p.Prime] (f : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) :
    HeckePair.IsHeckeFun (U := 𝐊[ℚ_[p]]) (f : GL (Fin 2) ℚ_[p] → ℂ) :=
  HeckePair.isHeckeFun f

/-- `X.hpair.def:hecke-submodule`: membership in the Hecke submodule is being a Hecke function. -/
theorem heckeSubmodule_padic_mem_iff (p : ℕ) [Fact p.Prime] (f : GL (Fin 2) ℚ_[p] → ℂ) :
    f ∈ HeckePair.heckeSubmodule 𝐊[ℚ_[p]] ℂ ↔ HeckePair.IsHeckeFun (U := 𝐊[ℚ_[p]]) f :=
  HeckePair.mem_heckeSubmodule_iff

/-- `X.hpair.def:hecke-one`: the unit `1_K` is the indicator function of `K`. -/
theorem heckeOne_padic_coe (p : ℕ) [Fact p.Prime] :
    ((HeckePair.heckeOne 𝐊[ℚ_[p]] ℂ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) : GL (Fin 2) ℚ_[p] → ℂ) =
      Set.indicator (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p])) 1 :=
  rfl

/-- `X.hpair.def:conv-term`: the summand of the convolution at the coset `yK` is `f₁(y) f₂(y⁻¹x)`. -/
theorem convTerm_padic_mk (p : ℕ) [Fact p.Prime] (f₁ f₂ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ)
    (x y : GL (Fin 2) ℚ_[p]) :
    HeckePair.convTerm f₁ f₂ x (QuotientGroup.mk y) =
      (f₁ : GL (Fin 2) ℚ_[p] → ℂ) y * (f₂ : GL (Fin 2) ℚ_[p] → ℂ) (y⁻¹ * x) :=
  rfl

/-- `X.hpair.def:conv`: convolution with the unit `1_K` on the left is the identity. -/
theorem conv_padic_one_left (p : ℕ) [Fact p.Prime] (f : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) :
    HeckePair.conv (HeckePair.heckeOne 𝐊[ℚ_[p]] ℂ) f = (f : GL (Fin 2) ℚ_[p] → ℂ) := by
  rw [← HeckePair.coe_mul]
  exact congrArg Subtype.val (one_mul f)

/-- `X.hpair.def:algebra-instance`: the structure map `ℂ → H(GL₂(ℚ_p), K)` sends `c` to `c • 1_K`. -/
theorem heckeAlgebra_padic_algebraMap (p : ℕ) [Fact p.Prime] (c : ℂ) :
    algebraMap ℂ (HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) c = c • 1 :=
  Algebra.algebraMap_eq_smul_one c

end GL2TFTests
