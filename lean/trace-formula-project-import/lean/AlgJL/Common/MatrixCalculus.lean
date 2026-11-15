import AlgJL.Meta.Tag
import AlgJL.Common.MatrixGL2
import Mathlib.Topology.Instances.Matrix
import Mathlib.Basic.Complex.Basic


-- algebraic_jl fork (L-A, 2026-11-14): trimmed copy of lean/GL2TF/Common/MatrixCalculus.lean @84818d0. Kept declarations
-- are byte-identical. Dropped (analytic): lieDerivReal (I.mcalc.def:real-lie-derivative), expGL (I.mcalc.def:exp-gl);
-- the calculus/exponential imports.

/-!
# Calculus on the matrix space of GL₂(ℝ) (M2, unit U5)

B-only plumbing (`tf_aux`) for smoothness and derivatives on GL₂(ℝ) through the Pi-type transport of
`Matrix (Fin 2) (Fin 2) ℝ` (M2.md §2 D-SMOOTH), rendered in B `vol1/ch-0-10-reps.tex` §3.
Mathlib has no global norm on `Matrix`; the Pi type `Fin 2 → Fin 2 → ℝ` carries the global sup-norm instances, and
smoothness does not depend on the norm (finite dimension). Smoothness is `C^∞` (`∞`, under `open scoped ContDiff`),
never `⊤ = ω` (analytic).
Owner: L2 (scaffolded by L1 in M2 W0).
-/

namespace GL2TF

/-- The matrix space `M₂(ℝ)` as the Pi type `Fin 2 → Fin 2 → ℝ` (global normed-space instances). -/
@[tf_aux "I.mcalc.def:matrix-pi"]
abbrev MatPi : Type := Fin 2 → Fin 2 → ℝ

/-- The linear identification `M₂(ℝ) ≃ₗ[ℝ] (Fin 2 → Fin 2 → ℝ)`. -/
@[tf_aux "I.mcalc.def:to-pi"]
noncomputable def matToPi : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] MatPi := (Matrix.ofLinearEquiv ℝ).symm

/-- The open set `{X | det X ≠ 0}` of the Pi-type matrix space (the image of `GL₂(ℝ)`). -/
@[tf_aux "I.mcalc.def:det-ne-zero-set"]
def detNeZeroSet : Set MatPi := {X | (Matrix.of X).det ≠ 0}

/-- The extension of `f : GL₂(ℝ) → ℂ` to the matrix space: `f` on `{det ≠ 0}`, `0` elsewhere. -/
@[tf_aux "I.mcalc.def:gl-extension"]
noncomputable def glExt (f : GL (Fin 2) ℝ → ℂ) (X : MatPi) : ℂ :=
  open Classical in if h : IsUnit (Matrix.of X) then f h.unit else 0

theorem mem_detNeZeroSet_iff (X : MatPi) : X ∈ detNeZeroSet ↔ IsUnit (Matrix.of X) := by
  simp [detNeZeroSet, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem glExt_of_mem (f : GL (Fin 2) ℝ → ℂ) {X : MatPi} (hX : X ∈ detNeZeroSet) :
    glExt f X = f ((mem_detNeZeroSet_iff X).1 hX).unit := by
  rw [glExt, dite_eq_left ((mem_detNeZeroSet_iff X).1 hX)]

theorem glExt_add (f f' : GL (Fin 2) ℝ → ℂ) : glExt (f + f') = glExt f + glExt f' := by
  funext X
  by_cases h : IsUnit (Matrix.of X) <;> simp [glExt, h]

theorem glExt_mul (f f' : GL (Fin 2) ℝ → ℂ) : glExt (f * f') = glExt f * glExt f' := by
  funext X
  by_cases h : IsUnit (Matrix.of X) <;> simp [glExt, h]

theorem glExt_smul (c : ℂ) (f : GL (Fin 2) ℝ → ℂ) : glExt (c • f) = c • glExt f := by
  funext X
  by_cases h : IsUnit (Matrix.of X) <;> simp [glExt, h]

theorem glExt_zero : glExt (0 : GL (Fin 2) ℝ → ℂ) = 0 := by
  funext X
  simp [glExt]

theorem glExt_const_eqOn (c : ℂ) : Set.EqOn (glExt fun _ => c) (fun _ => c) detNeZeroSet := by
  intro X hX
  rw [glExt_of_mem _ hX]

end GL2TF
