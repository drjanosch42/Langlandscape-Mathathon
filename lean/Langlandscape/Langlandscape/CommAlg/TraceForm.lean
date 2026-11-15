/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# The trace-form core of the Galois comparison (S06-L6)

`mathematics/chapters/s06/s06-m4.tex`, `lem:s06-traceform` (`prop:s06-galois`, last step of the
proof; secondary reference: `plan/staged/stage-06-integral-defect.tex`): if `A` is a commutative
ring, `A[G] → M₂(A)` is surjective and `tr ρ(gσ) = tr ρ(g)` for all `g`, then `ρ(σ) = 1`, because
the trace form on `M₂(A)` is perfect (matrix units).

* `matrix_eq_one_of_trace_mul_eq`: for `X ∈ Mₙ(A)` with `tr(Y X) = tr Y` for all `Y`, `X = 1`
  (test against the matrix units `E_{ji}`).
* `eq_one_of_trace_mul_eq`: the statement of the row, for `ρ : G →* GL (Fin 2) A` (the shape of
  `Defect.Setting.ρ`), with the surjectivity of `A[G] → M₂(A)` expressed by
  `MonoidAlgebra.lift`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

open Matrix

/-- Perfectness of the trace form on `Mₙ(A)` (`prop:s06-galois`, proof, last step): if
`tr (Y * X) = tr Y` for every matrix `Y`, then `X = 1`. Test against the matrix units:
`tr (E_{ji} * X) = X i j` and `tr E_{ji} = δ_{ij}`. -/
theorem matrix_eq_one_of_trace_mul_eq {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n]
    (X : Matrix n n A) (hX : ∀ Y : Matrix n n A, trace (Y * X) = trace Y) : X = 1 := by
  ext i j
  have h := hX (single j i 1)
  rw [trace_single_mul, one_smul] at h
  rw [h, one_apply]
  by_cases hij : i = j
  · subst hij
    rw [trace_single_eq_same]
    simp
  · rw [trace_single_eq_of_ne (h := Ne.symm hij)]
    simp [hij]

/-- **Trace-form core** (`lem:s06-traceform`, `prop:s06-galois`; stage-06 row S06-L6). Let `A` be a
commutative ring,
`ρ : G →* GL₂(A)` such that the induced algebra map `A[G] → M₂(A)` is surjective, and let `σ ∈ G`
with `tr ρ(g σ) = tr ρ(g)` for all `g ∈ G`. Then `ρ σ = 1`.

Proof: by linearity `tr (Y ρ(σ)) = tr Y` for `Y` in the image of `A[G]`, i.e. for every
`Y ∈ M₂(A)`; conclude by `matrix_eq_one_of_trace_mul_eq` (matrix units). No locality of `A` is
needed (in the application `A = I_F / 𝔠_q(F)` is local and the surjectivity comes from Burnside
modulo `𝔪_A` plus Nakayama, see `surjective_groupAlgebra_of_absIrred`). `G` may be any monoid. -/
theorem eq_one_of_trace_mul_eq {A G : Type*} [CommRing A] [Monoid G]
    (ρ : G →* GL (Fin 2) A)
    (hsurj : Function.Surjective
      (MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
        ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ)))
    (σ : G)
    (htr : ∀ g : G, trace ((ρ (g * σ) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      trace ((ρ g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) :
    ρ σ = 1 := by
  set F := MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
    ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ) with hF
  have hall : ∀ x : MonoidAlgebra A G,
      trace (F x * ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) = trace (F x) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      rw [hF, MonoidAlgebra.lift_of]
      simpa [map_mul, Units.val_mul] using htr g
    | add x y hx hy => rw [map_add, add_mul, trace_add, trace_add, hx, hy]
    | smul r x hx => rw [map_smul, smul_mul_assoc, trace_smul, trace_smul, hx]
  have h1 : ((ρ σ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = 1 :=
    matrix_eq_one_of_trace_mul_eq _ fun Y => by
      obtain ⟨x, rfl⟩ := hsurj Y
      exact hall x
  exact Units.ext h1

end Langlandscape.CommAlg
