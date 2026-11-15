import AlgJL.Meta.Tag
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# GL₂ (and GLₙ) over a topological field as a topological group (M1, unit U1)

Lean counterpart of the `X.topgrp.*` items typeset in `vol1/ch-0-04-top-groups.tex` §1. Topology: Mathlib's
product topology on matrices and its units topology on `GL n F` (D-TOP: no competing instance). σ-algebra: the
product σ-algebra on matrices (a project instance, kept although Mathlib v4.35 now has its own instance with the
same body in `Mathlib/Analysis/Matrix/MeasurableSpace.lean`) and Mathlib's
`Units.instMeasurableSpace` (comap along `Units.val`) on `GL n F`. Owner: L1.
-/

open Topology

namespace GL2TF

/-- The product σ-algebra on `Matrix m n α = m → n → α` (B-only plumbing; Mathlib v4.35 has its own instance with
the same body in `Mathlib/Analysis/Matrix/MeasurableSpace.lean`; the project instance is kept). -/
@[tf_aux "X.topgrp.def:matrix-measurable-space"]
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- `GLₙ` version of `gl2_units_isOpenEmbedding` (B-only). -/
@[tf_aux "X.topgrp.lem:gln-units-open-embedding"]
theorem gln_units_isOpenEmbedding (n : Type*) [Fintype n] [DecidableEq n] (F : Type*) [Field F]
    [TopologicalSpace F] [ContinuousAdd F] [ContinuousMul F] [ContinuousInv₀ F] [T1Space F] :
    IsOpenEmbedding (Units.val : GL n F → Matrix n n F) ∧
      Set.range (Units.val : GL n F → Matrix n n F) = {X | X.det ≠ 0} := by
  have : ContinuousNeg F := ⟨by simpa using continuous_const_mul (-1 : F)⟩
  have : IsTopologicalRing F := {}
  have hrange : Set.range (Units.val : GL n F → Matrix n n F) = {X | X.det ≠ 0} := by
    ext X
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit |>.ne_zero
    · intro h
      exact ⟨((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h)).unit, rfl⟩
  have hemb : Topology.IsEmbedding (Units.val : GL n F → Matrix n n F) := by
    refine Units.isEmbedding_val_mk' (f := Inv.inv) (fun X hX ↦ ?_) fun u ↦ (Matrix.coe_units_inv u).symm
    have hdet : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
    refine (continuousAt_matrix_inv X ?_).continuousWithinAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  refine ⟨⟨hemb, ?_⟩, hrange⟩
  rw [hrange]
  exact (isOpen_compl_singleton (x := (0 : F))).preimage continuous_id.matrix_det

/-- For a field `F` with a topology in which addition and multiplication are continuous, inversion is continuous
on `Fˣ` and points are closed, the inclusion `GL₂(F) → M₂(F)` (units topology, product topology) is an open
embedding with image `{X | det X ≠ 0}`. -/
@[tf_id "X.topgrp.thm:gl2-units-open-embedding"]
theorem gl2_units_isOpenEmbedding (F : Type*) [Field F] [TopologicalSpace F] [ContinuousAdd F]
    [ContinuousMul F] [ContinuousInv₀ F] [T1Space F] :
    IsOpenEmbedding (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) ∧
      Set.range (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) = {X | X.det ≠ 0} :=
  gln_units_isOpenEmbedding (Fin 2) F

/-- The units topology on `GL₂(F)` equals the topology induced by the inclusion into `M₂(F)`. -/
@[tf_id "X.topgrp.thm:gl2-units-topology-eq-subspace"]
theorem gl2_units_topology_eq_induced (F : Type*) [Field F] [TopologicalSpace F] [ContinuousAdd F]
    [ContinuousMul F] [ContinuousInv₀ F] [T1Space F] :
    (inferInstance : TopologicalSpace (GL (Fin 2) F)) =
      TopologicalSpace.induced (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) inferInstance :=
  (gl2_units_isOpenEmbedding F).1.isInducing.eq_induced

/-- For `F` as above, second countable, with its Borel σ-algebra: the σ-algebra on `GL₂(F)` induced by the
inclusion into `M₂(F)` (product σ-algebra) is the Borel σ-algebra of the units topology. -/
@[tf_id "X.topgrp.thm:gl2-borel-measurable"]
theorem gl2_borelSpace (F : Type*) [Field F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousMul F]
    [ContinuousInv₀ F] [T1Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] :
    BorelSpace (GL (Fin 2) F) := by
  have hM : BorelSpace (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → F))
  refine ⟨?_⟩
  change MeasurableSpace.comap Units.val _ = _
  rw [hM.measurable_eq, ← borel_comap]
  exact congrArg (@borel (GL (Fin 2) F)) (gl2_units_topology_eq_induced F).symm

end GL2TF
