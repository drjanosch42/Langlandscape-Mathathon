import AlgJL.Meta.Tag
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/Common/DiscreteQuotient.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (21): `countable_of_discrete`, `exists_fd`, `exists_fundamental_domain`, `exists_open_mul_inv_inter`, `fdChoice`, `fdChoice_spec`, `fd_unique_point`, `isFD_of`, `lintegral_unfold`, `measurable_indicator_tsum`, `measurable_quot_mk`, `polishSpace_of_lcsc`, `quot_mk_smul`, `quotientMeasure`, `quotientMeasure_apply_of`, `quotientMeasure_finite`, `quotientMeasure_invariant`, `quotientMeasure_spec`, `quotient_borelSpace`, `tsum_reindex_mul`, `unfolding_discrete`.
Dropped tagged IDs: `X.quot.def:quotient-measure`, `X.quot.lem:quotient-measure-spec`, `X.quot.thm:exists-fundamental-domain`, `X.quot.thm:quotient-measure-invariant`, `X.quot.thm:unfolding-discrete`. -/

/-!
# Quotients by discrete subgroups (algebraic/topological remnant)

The two topological lemmas of `GL2TF/Common/DiscreteQuotient.lean` used by the fork (`Quotient`, `Reduction`,
`Centralizer`). Fundamental domains, the quotient measure and unfolding are not part of the fork.
-/

open Topology Filter Set

namespace GL2TF

section FD

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem tendsto_cofinite_of_discrete [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] :
    Tendsto Γ.subtype cofinite (cocompact G) := by
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  have hc : IsCompact (Subtype.val ⁻¹' K : Set Γ) :=
    (Subgroup.isClosed_of_discreteTopology (U := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  rw [Filter.eventually_cofinite]
  convert hc.finite_of_discrete using 1
  ext x; simp

end FD

section Spec

variable {G : Type*} [Group G] (Γ : Subgroup G)

theorem quot_mk_eq_iff' {x y : G} :
    (Quotient.mk (MulAction.orbitRel Γ G) x = Quotient.mk _ y) ↔ ∃ γ : Γ, (γ : G) * y = x := by
  rw [Quotient.eq]
  rfl

end Spec

end GL2TF
