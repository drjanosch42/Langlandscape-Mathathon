/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Burnside's theorem for residually absolutely irreducible `GL₂` representations (S06-L6b)

`mathematics/chapters/s06/s06-m4.tex`, `lem:s06-burnside` (`prop:s06-galois`, proof; secondary
reference: `plan/staged/stage-06-integral-defect.tex`): "By (H2), `A[G_ℚ] → M₂(A)` is surjective
(Burnside modulo `𝔪_A`, then Nakayama)."

Let `A` be a local ring, `ρ : G →* GL₂(A)` and `f : A →+* K` a local homomorphism to an
algebraically closed field `K` (so `ker f = 𝔪_A` and `f` factors through an embedding of the
residue field `k` into `K`). *Absolute irreducibility of the residual representation*
`ρ̄ = ρ mod 𝔪_A` is expressed as the irreducibility of `ρ̄ ⊗_k K = residualRep f ρ` on `K²`
(Mathlib's `Representation.IsIrreducible`).

* `asAlgebraHom_surjective_of_isIrreducible`: Burnside over an algebraically closed field: for
  an irreducible finite-dimensional representation `σ` of `G` over `K`, `K[G] → End_K(V)` is
  surjective (Schur's lemma + Jacobson density, both in Mathlib, in place of Wedderburn–Artin).
* `surjective_groupAlgebra_of_absIrred`: the lift to `A`. Instead of Nakayama we use the
  determinant: Burnside over `K` gives `g₁, …, g₄ ∈ G` whose images form a `K`-basis of `M₂(K)`;
  the `4 × 4` determinant `d ∈ A` of `ρ(g₁), …, ρ(g₄)` (in the standard basis) satisfies
  `f d ≠ 0`, so `d` is a unit (`f` is local) and `ρ(g₁), …, ρ(g₄)` is an `A`-basis of `M₂(A)`.

Usage: for `ρ̄` absolutely irreducible over the residue field `k`, take
`K = AlgebraicClosure (IsLocalRing.ResidueField A)` and
`f = (algebraMap _ K).comp (IsLocalRing.residue A)`; its `IsLocalHom` instance comes from
`RingHom.isLocalHom_comp` (a theorem, so `haveI` it).

No `Hyp` import: the discharge of `Hyp.ResidualBurnside` is S06-L6c.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

open Matrix

section Field

variable {K G V : Type*} [Field K] [IsAlgClosed K] [Monoid G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Burnside's theorem** over an algebraically closed field (`prop:s06-galois`, proof:
"Burnside modulo `𝔪_A`"). For an irreducible finite-dimensional representation `σ` of a monoid
`G` over an algebraically closed field `K`, the algebra map `K[G] → End_K(V)` is surjective.
Proof: `End_{K[G]}(V) = K` (Schur), and the Jacobson density theorem for the module `V`, finite
over `End_{K[G]}(V)`. -/
theorem asAlgebraHom_surjective_of_isIrreducible (σ : Representation K G V)
    [σ.IsIrreducible] : Function.Surjective σ.asAlgebraHom := by
  intro X
  have hS := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (A := MonoidAlgebra K G) (V := σ.asModule) K
  have : Module.Finite (Module.End (MonoidAlgebra K G) σ.asModule) σ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  let φ : Module.End (Module.End (MonoidAlgebra K G) σ.asModule) σ.asModule :=
    { toFun := fun v => σ.asModuleEquiv.symm (X (σ.asModuleEquiv v))
      map_add' := by intro v w; simp
      map_smul' := by
        intro e v
        obtain ⟨c, rfl⟩ := hS.2 e
        simp only [Module.End.smul_def, Module.algebraMap_end_apply, RingHom.id_apply,
          LinearEquiv.map_smul, LinearMap.map_smul] }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective
    (R := MonoidAlgebra K G) (M := σ.asModule) φ
  refine ⟨r, LinearMap.ext fun v => ?_⟩
  have h := congr(σ.asModuleEquiv ($hr (σ.asModuleEquiv.symm v)))
  simpa [φ, Representation.asModuleEquiv_map_smul] using h

end Field

section Local

variable {A G K : Type*} [CommRing A] [Monoid G] [Field K]

/-- The representation `ρ̄ ⊗ K` of `G` on `K²`, `g ↦ f(ρ g)`, for `f : A →+* K`
(`prop:s06-galois`: the residual representation `ρ̄`, extended to the algebraically closed
field `K`; `f` is local, so it factors through the residue field of `A`). -/
noncomputable def residualRep (f : A →+* K) (ρ : G →* GL (Fin 2) A) :
    Representation K G (Fin 2 → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) K ≃ₐ[K] Module.End K (Fin 2 → K)).toRingEquiv
    |>.toMonoidHom.comp ((f.mapMatrix : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) K)
      |>.toMonoidHom.comp ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ))

/-- `residualRep f ρ g = toLin' (f (ρ g))` (`prop:s06-galois`). -/
theorem residualRep_apply (f : A →+* K) (ρ : G →* GL (Fin 2) A) (g : G) :
    residualRep f ρ g =
      Matrix.toLin' ((ρ g : Matrix (Fin 2) (Fin 2) A).map f) := rfl

/-- **Burnside + lift for `GL₂`** (`lem:s06-burnside`, `prop:s06-galois`; stage-06 row S06-L6b).
Let `A` be a
local ring, `ρ : G →* GL₂(A)`, and `f : A →+* K` a local homomorphism to an algebraically closed
field `K` such that `ρ̄ ⊗ K = residualRep f ρ` is irreducible (`ρ̄` absolutely irreducible). Then
the algebra map `A[G] → M₂(A)` induced by `ρ` is surjective.

The surjectivity is stated in the same form as the hypothesis of `eq_one_of_trace_mul_eq`
(S06-L6). Edge cases: the trivial monoid `G` is allowed (then `residualRep` is trivial, hence not
irreducible on `K²`, and the statement is vacuous); `A` may be a field (`f` then injective). -/
theorem surjective_groupAlgebra_of_absIrred [IsLocalRing A] [IsAlgClosed K]
    (f : A →+* K) [IsLocalHom f] (ρ : G →* GL (Fin 2) A)
    (hirr : (residualRep f ρ).IsIrreducible) :
    Function.Surjective
      (MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
        ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ)) := by
  classical
  set FA := MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
    ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ) with hFA
  -- matrices over `A` and over `K`
  let ρA : G → Matrix (Fin 2) (Fin 2) A := fun g => (ρ g : Matrix (Fin 2) (Fin 2) A)
  let ρK : G → Matrix (Fin 2) (Fin 2) K := fun g => (ρA g).map f
  -- Step 1: the `ρK g` span `M₂(K)` (Burnside over `K`).
  have hspanK : Submodule.span K (Set.range ρK) = ⊤ := by
    have := hirr
    have hsurj := asAlgebraHom_surjective_of_isIrreducible (residualRep f ρ)
    have hmem : ∀ r : MonoidAlgebra K G,
        Matrix.toLin'.symm ((residualRep f ρ).asAlgebraHom r) ∈
          Submodule.span K (Set.range ρK) := by
      intro r
      induction r using MonoidAlgebra.induction_on with
      | of g =>
        rw [Representation.asAlgebraHom_of, residualRep_apply, LinearEquiv.symm_apply_apply]
        exact Submodule.subset_span ⟨g, rfl⟩
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | smul c x hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hx
    refine eq_top_iff.2 fun Y _ => ?_
    obtain ⟨r, hr⟩ := hsurj (Matrix.toLin' Y)
    have := hmem r
    rwa [hr, LinearEquiv.symm_apply_apply] at this
  -- Step 2: extract a `K`-basis `ρK (w p)`, `p : Fin 2 × Fin 2`.
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent K (Set.range ρK)
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Matrix (Fin 2) (Fin 2) K)) := by
    rw [Subtype.range_coe, hbspan, hspanK]
  let B' := Module.Basis.mk hli hsp
  let BK := Matrix.stdBasis K (Fin 2) (Fin 2)
  let e : b ≃ Fin 2 × Fin 2 := B'.indexEquiv BK
  let w : Fin 2 × Fin 2 → G := fun p => (hbs (e.symm p).2).choose
  have hw : ∀ p, ρK (w p) = (B'.reindex e) p := by
    intro p
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact (hbs (e.symm p).2).choose_spec
  -- Step 3: the determinant over `A` maps to a nonzero determinant over `K`.
  let BA := Matrix.stdBasis A (Fin 2) (Fin 2)
  have hdet : f (BA.det (fun p => ρA (w p))) = BK.det (fun p => ρK (w p)) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
  have hK : IsUnit (BK.det (fun p => ρK (w p))) := by
    have : (fun p => ρK (w p)) = ⇑(B'.reindex e) := funext hw
    rw [this]
    exact BK.isUnit_det _
  have hA : IsUnit (BA.det (fun p => ρA (w p))) := by
    rw [← isUnit_map_iff f, hdet]
    exact hK
  have hspanA : Submodule.span A (Set.range fun p => ρA (w p)) = ⊤ :=
    (BA.is_basis_iff_det.2 hA).2
  -- Step 4: the image of `A[G]` contains this span.
  intro Y
  have hY : Y ∈ Submodule.span A (Set.range fun p => ρA (w p)) := by rw [hspanA]; trivial
  have hle : Submodule.span A (Set.range fun p => ρA (w p)) ≤
      LinearMap.range FA.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact ⟨MonoidAlgebra.of A G (w p), by simp [hFA, ρA]⟩
  obtain ⟨x, hx⟩ := hle hY
  exact ⟨x, hx⟩

end Local

end Langlandscape.CommAlg
