import AlgJL.VolI.P1.SphericalEigen

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/SphericalEigen.lean` at commit 84818d0. Dropped tests of stripped declarations (1): `sphericalHeckeAction_trivial_one`. Added (fork): `sphericalHeckeAction_trivial_fixed`. -/


/-!
# Tests for `GL2TF.VolI.P1.SphericalEigen`

Named tests of the tagged definitions of M5a items 26–27 (PLAN.md §2.3), at `F = ℚ_p`.
-/

open ValuativeRel GL2TF GL2TF.Local
open scoped Pointwise

namespace GL2TFTests

/-- `I.smooth.def:spherical-hecke-action` (fork replacement of `sphericalHeckeAction_trivial_one`): on the trivial
representation `ℂ`, `f ∗ 1` is `K`-fixed (`sphericalHeckeAction_spec` (c)). -/
theorem sphericalHeckeAction_trivial_fixed (p : ℕ) [Fact p.Prime] (f : sphericalHeckeAlgebra ℚ_[p]) :
    sphericalHeckeAction (Representation.trivial ℂ (GL (Fin 2) ℚ_[p]) ℂ) f (1 : ℂ) ∈
      fixedVectors (Representation.trivial ℂ (GL (Fin 2) ℚ_[p]) ℂ) 𝐊[ℚ_[p]] :=
  ((sphericalHeckeAction_spec _) 1 (fun _ _ => rfl)).2.2.1 f

/-- `I.smooth.def:spherical-vector-element`: `f°_χ(1) = 1`. -/
theorem sphericalVectorPS_padic_one (p : ℕ) [Fact p.Prime] (χ₁ χ₂ : QuasiChar ℚ_[p]) (h₁ : χ₁.IsUnramified)
    (h₂ : χ₂.IsUnramified) : (sphericalVectorPS χ₁ χ₂ h₁ h₂ : GL (Fin 2) ℚ_[p] → ℂ) 1 = 1 :=
  ((principal_series_spherical χ₁ χ₂).1 h₁ h₂).2.2.1

end GL2TFTests
