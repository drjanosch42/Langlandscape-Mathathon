import AlgJL.VolI.P0.Reps

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P0/Reps.lean` at commit 84818d0. Dropped tests of stripped declarations (26): `glExt_zero`, `stdKappaMat`, `stdKappaMat_val`, `continuous_stdKappaMat_val`, `measureCoeff_empty'`, `lieDerivReal_zero`, `lieAction_zero`, `casimir_zero`, `centralOp_zero`, `leftTranslate_one`, `rightTranslate_one`, `exists_diracSequence_gl2Real`, `hasWeight_zero_const`, `kFinite_const`, `zero_mem_archTestFunctions`, `trivialGKModule`, `trivialGKModule_isAdmissible`, `trivialGKModule_casimirOp`, `stdGKModule`, `stdGKModule_act_one`, `zero_mem_smoothDual`, `contragredient_trivial_isAdmissibleRep`, `smoothHeckeAction_zero`, `trivial_isNondegenerateModule`, `isStronglyContinuous_one`, `integratedRep_zero`, `rightRegular_one`. -/


/-!
# Tests for `GL2TF.VolI.P0.Reps`

Non-vacuity examples and proved instances (PLAN.md §2.3).
-/

open GL2TF

namespace GL2TFTests

section TrivialRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The trivial representation of `G` on `ℂ` is smooth. -/
theorem trivial_isSmoothRep : IsSmoothRep (Representation.trivial ℂ G ℂ) := by
  intro v
  simp

omit [IsTopologicalGroup G] in
/-- The trivial representation of `G` on `ℂ` is admissible. -/
theorem trivial_isAdmissibleRep : IsAdmissibleRep (Representation.trivial ℂ G ℂ) :=
  ⟨trivial_isSmoothRep, fun _ _ _ => inferInstance⟩

/-- The trivial representation of `G` on `ℂ` is irreducible (the hypothesis of `schur_lemma`). -/
theorem trivial_irreducible (W : Submodule ℂ ℂ) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top W

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `ℂ^{K′} = ℂ` for the trivial representation. -/
theorem fixedVectors_trivial (K' : Subgroup G) : fixedVectors (Representation.trivial ℂ G ℂ) K' = ⊤ := by
  ext v
  simp [fixedVectors]

end TrivialRep


end GL2TFTests
