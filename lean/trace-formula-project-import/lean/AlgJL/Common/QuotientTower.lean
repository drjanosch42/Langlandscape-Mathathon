import AlgJL.Meta.Tag
import Mathlib.Topology.Algebra.Group.Basic
/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/Common/QuotientTower.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (23): `IsWeilMeasure`, `discreteTopology_subgroupOf`, `exists_out_rightCosetHomeomorph_symm`, `integrable_rightCoset_of`, `integral_rightCoset_eq`, `isInvInvariant_of_isUnimodular`, `isMulRightInvariant_of_isUnimodular`, `leftRel_inv_rightRel`, `lintegral_rightCoset_eq`, `measurable_out_comp`, `out_mk_invariant`, `quotient_tower`, `rightCosetHomeomorph`, `rightCosetHomeomorph_symm_apply`, `rightCoset_quotient_borel`, `rightCoset_quotient_topology`, `rightRel_inv_leftRel`, `rightRel_mul_right`, `tsum_indicator_fdChoice`, `unfold_reindex`, `unfolding_subgroup`, `weil_measure_discrete`, `weil_quotient_formula_right`.
Dropped tagged IDs: `X.quot.def:weil-measure`, `X.quot.lem:right-coset-quotient-borel`, `X.quot.lem:right-coset-quotient-locally-compact-instance`, `X.quot.thm:quotient-tower`, `X.quot.thm:unfolding-subgroup`, `X.quot.thm:weil-measure-discrete`, `X.quot.thm:weil-quotient-formula-right`. -/

/-!
# Quotient towers (algebraic/topological remnant)

Only `discreteTopology_of_le` of `GL2TF/Common/QuotientTower.lean` is used by the fork (`TruncationCosets`).
-/

namespace GL2TF

section UnfoldPlumbing

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A subgroup of a discrete subgroup is discrete. -/
theorem discreteTopology_of_le {Γ Γ' : Subgroup G} [DiscreteTopology Γ] (h : Γ' ≤ Γ) : DiscreteTopology Γ' :=
  DiscreteTopology.of_continuous_injective (f := fun x : Γ' ↦ (⟨(x : G), h x.2⟩ : Γ))
    (continuous_subtype_val.subtype_mk _) fun a b hab ↦ Subtype.ext (congrArg Subtype.val hab :)

end UnfoldPlumbing

end GL2TF
