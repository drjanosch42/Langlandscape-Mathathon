import AlgJL.Common.QuaternionNorm
import Mathlib.Basic.Real.Basic

/-!
# Definite quaternion algebras over ℚ and ℝ (Q2 U1, items 7–8)

Lean counterpart of `vol3/ch-iii-06-quatalg.tex` §1, end (items 7, 8 of `docs/sprints/Q2-plan.md` §1.2).
"Definite" is `a < 0 ∧ b < 0` (in `ℤ`), written inline in the binders, never a project Prop (plan §1.2, trap 1).
Owner: L1T (Q2).
-/

set_option autoImplicit false

namespace GL2TF.Quat

private theorem nrd_definite_aux {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : ℤ} (ha : a < 0) (hb : b < 0) (x : QuatAlg R a b) :
    x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 ≤ nrd x ∧ (nrd x = 0 ↔ x = 0) := by
  have ha' : (a : R) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
  have hb' : (b : R) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
  have hab : (1 : R) ≤ (a : R) * (b : R) := by
    have : (1 : ℤ) ≤ a * b := by nlinarith
    exact_mod_cast this
  have h0 := sq_nonneg x.re
  have h1 := sq_nonneg x.imI
  have h2 := sq_nonneg x.imJ
  have h3 := sq_nonneg x.imK
  have hle : x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 ≤ nrd x := by
    unfold nrd
    nlinarith [mul_nonneg (show (0 : R) ≤ -1 - a by linarith) h1,
      mul_nonneg (show (0 : R) ≤ -1 - b by linarith) h2,
      mul_nonneg (show (0 : R) ≤ a * b - 1 by linarith) h3]
  refine ⟨hle, fun h => ?_, fun h => by subst h; simp [nrd]⟩
  have e0 : x.re ^ 2 = 0 := by linarith
  have e1 : x.imI ^ 2 = 0 := by linarith
  have e2 : x.imJ ^ 2 = 0 := by linarith
  have e3 : x.imK ^ 2 = 0 := by linarith
  ext <;> simp_all

/-- For `a, b < 0` (in `ℤ`) and `R ∈ {ℚ, ℝ}`: `nrd(x) ≥ x₀² + x₁² + x₂² + x₃²`; in particular `nrd(x) = 0 ⇔ x = 0`. -/
@[tf_id "III.qalg.lem:reduced-norm-definite"]
theorem nrd_definite {a b : ℤ} (ha : a < 0) (hb : b < 0) :
    (∀ x : QuatAlg ℚ a b,
      x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 ≤ nrd x ∧ (nrd x = 0 ↔ x = 0)) ∧
    (∀ x : QuatAlg ℝ a b,
      x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 ≤ nrd x ∧ (nrd x = 0 ↔ x = 0)) :=
  ⟨nrd_definite_aux ha hb, nrd_definite_aux ha hb⟩

/-- For `a, b < 0`: every nonzero element of `B = B_ℚ` and every nonzero element of `B_ℝ` is a unit. -/
@[tf_id "III.qalg.thm:definite-division"]
theorem definite_division {a b : ℤ} (ha : a < 0) (hb : b < 0) :
    (∀ x : QuatAlg ℚ a b, x ≠ 0 → IsUnit x) ∧ (∀ x : QuatAlg ℝ a b, x ≠ 0 → IsUnit x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact (isUnit_iff_isUnit_nrd.1 x).2
      (isUnit_iff_ne_zero.2 fun h => hx ((nrd_definite_aux ha hb x).2.1 h))
  · exact (isUnit_iff_isUnit_nrd.1 x).2
      (isUnit_iff_ne_zero.2 fun h => hx ((nrd_definite_aux ha hb x).2.1 h))

end GL2TF.Quat
