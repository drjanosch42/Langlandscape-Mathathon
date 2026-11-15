/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination

/-!
# Cokernel of a 2 × 2 matrix with a unit corner (S06-L14)

`mathematics/chapters/s06/s06-m7.tex`, `lem:s06-twobytwo` (`prop:s06-betti`(a), linear-algebra
step; secondary reference: `plan/staged/stage-06-integral-defect.tex`): since `q + 1` is a unit, the
cokernel of `[[q+1, *], [*, q+1]]` on `T²` is `T ⧸ (det)`.

Scope: this proves the case `H = T` of `lem:s06-twobytwo` (the cokernel on `T²`); the general case
of an arbitrary `T`-module `H` (by `⊗_T H`) is not formalized.

For a commutative ring `T` and `M = [[u, b], [c, d]] ∈ M₂(T)` with `u` a unit, the `T`-linear map
`T² → T, (x, y) ↦ u y - c x` is surjective with kernel exactly the image of `M`, so
`coker M = T² ⧸ M T² ≃ T ⧸ (det M)`, where `det M = u d - b c`.

* `TwoByTwo.cokerEquiv`: the general statement (only `M 0 0` a unit), with `cokerEquiv_mk`.
* `TwoByTwo.cokerEquivOfIsUnit`: the row's shape `[[u, b], [c, u]]`, with
  `det [[u, b], [c, u]] = u * u - b * c` (`TwoByTwo.det_of`).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg.TwoByTwo

open Matrix

variable {T : Type*} [CommRing T]

/-- The `T`-linear form `(x, y) ↦ u y - c x` on `T²` attached to `M = [[u, b], [c, d]]`
(`prop:s06-betti`(a); it induces `coker M ≃ T ⧸ (det M)`). -/
def form (M : Matrix (Fin 2) (Fin 2) T) : (Fin 2 → T) →ₗ[T] T :=
  M 0 0 • LinearMap.proj 1 - M 1 0 • LinearMap.proj 0

/-- `form M v = u * v 1 - c * v 0` (`prop:s06-betti`(a)). -/
theorem form_apply (M : Matrix (Fin 2) (Fin 2) T) (v : Fin 2 → T) :
    form M v = M 0 0 * v 1 - M 1 0 * v 0 := by
  simp [form]

/-- The image of `M` is the kernel of `v ↦ [form M v] ∈ T ⧸ (det M)` when `M 0 0` is a unit
(`prop:s06-betti`(a), linear algebra). -/
theorem range_eq_ker (M : Matrix (Fin 2) (Fin 2) T) (hu : IsUnit (M 0 0)) :
    LinearMap.range M.mulVecLin = LinearMap.ker ((Ideal.span {M.det}).mkQ ∘ₗ form M) := by
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, form_apply, det_fin_two]
  constructor
  · rintro ⟨w, rfl⟩
    refine Ideal.mem_span_singleton'.2 ⟨w 1, ?_⟩
    simp only [mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · intro hv
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hv
    obtain ⟨u, hu'⟩ := hu
    have hui : (u : T) * ↑u⁻¹ = 1 := Units.mul_inv u
    refine ⟨![↑u⁻¹ * (v 0 - M 0 1 * s), s], ?_⟩
    ext i
    fin_cases i
    · simp only [mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hu']
      linear_combination (v 0 - M 0 1 * s) * hui
    · simp only [mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hu'] at hs
      linear_combination (↑u⁻¹ : T) * hs + (v 1 - M 1 1 * s) * hui

/-- `v ↦ [form M v]` is surjective onto `T ⧸ (det M)` when `M 0 0` is a unit
(`prop:s06-betti`(a)). -/
theorem surjective_mkQ_comp_form (M : Matrix (Fin 2) (Fin 2) T) (hu : IsUnit (M 0 0)) :
    Function.Surjective ((Ideal.span {M.det}).mkQ ∘ₗ form M) := by
  intro x
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨u, hu'⟩ := hu
  refine ⟨![0, ↑u⁻¹ * t], ?_⟩
  rw [LinearMap.comp_apply, form_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero]
  rw [← hu', ← mul_assoc, Units.mul_inv, one_mul]

/-- **`lem:s06-twobytwo`, case `H = T`** (`prop:s06-betti`(a), linear algebra; stage-06 row S06-L14,
general form; the general `T`-module `H` is not formalized). For
`M = [[u, b], [c, d]] ∈ M₂(T)` with `u = M 0 0` a unit,
`coker (M : T² → T²) ≃ T ⧸ (det M)` as `T`-modules, via `[v] ↦ [u v₁ - c v₀]`. -/
noncomputable def cokerEquiv (M : Matrix (Fin 2) (Fin 2) T) (hu : IsUnit (M 0 0)) :
    ((Fin 2 → T) ⧸ LinearMap.range M.mulVecLin) ≃ₗ[T] T ⧸ Ideal.span {M.det} :=
  (Submodule.quotEquivOfEq _ _ (range_eq_ker M hu)).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_mkQ_comp_form M hu))

/-- `cokerEquiv M hu [v] = [u v₁ - c v₀]` (`prop:s06-betti`(a)). -/
theorem cokerEquiv_mk (M : Matrix (Fin 2) (Fin 2) T) (hu : IsUnit (M 0 0)) (v : Fin 2 → T) :
    cokerEquiv M hu (Submodule.Quotient.mk v) =
      Ideal.Quotient.mk (Ideal.span {M.det}) (M 0 0 * v 1 - M 1 0 * v 0) := by
  simp [cokerEquiv, form_apply]

/-- `det [[u, b], [c, u]] = u * u - b * c` (`prop:s06-betti`(a): `δ = (q+1)² - …`). -/
theorem det_of (u b c : T) : (!![u, b; c, u]).det = u * u - b * c := by
  rw [det_fin_two_of]

/-- **`lem:s06-twobytwo`, case `H = T`** (`prop:s06-betti`(a); stage-06 row S06-L14, the row's
shape):
for `u` a unit, `coker [[u, b], [c, u]] ≃ T ⧸ (det)` as `T`-modules, with
`det = u * u - b * c` (`det_of`). In the tex `u = q + 1` and the cokernel of `Ψ^*Ψ` is the
direct sum of two copies of this after `⊗_T H^1_𝔪 ≅ T²`. -/
noncomputable def cokerEquivOfIsUnit (u b c : T) (hu : IsUnit u) :
    ((Fin 2 → T) ⧸ LinearMap.range (!![u, b; c, u]).mulVecLin) ≃ₗ[T]
      T ⧸ Ideal.span {(!![u, b; c, u]).det} :=
  cokerEquiv _ (by simpa using hu)

end Langlandscape.CommAlg.TwoByTwo
