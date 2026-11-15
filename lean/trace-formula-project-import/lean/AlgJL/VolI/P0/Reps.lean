import AlgJL.Meta.Tag
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Basic.Complex.Basic

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P0/Reps.lean` at commit 84818d0, reduced to §1's
definitions of fixed vectors, smooth and admissible representations (`fixedVectors` with its three closure lemmas,
`IsSmoothRep`, `IsAdmissibleRep`), verbatim. Everything else (Hecke modules via Haar convolution, contragredient,
unitary and right regular representations, Lie/Casimir calculus, (𝔤, K)-modules, 208 declarations) is dropped. -/

namespace GL2TF

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fixedVectors_add_mem (π : Representation ℂ G V) (K' : Subgroup G) {v w : V}
    (hv : ∀ k ∈ K', π k v = v) (hw : ∀ k ∈ K', π k w = w) : ∀ k ∈ K', π k (v + w) = v + w :=
  fun k hk => by rw [map_add, hv k hk, hw k hk]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fixedVectors_zero_mem (π : Representation ℂ G V) (K' : Subgroup G) : ∀ k ∈ K', π k 0 = 0 :=
  fun _ _ => map_zero _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fixedVectors_smul_mem (π : Representation ℂ G V) (K' : Subgroup G) (c : ℂ) {v : V}
    (hv : ∀ k ∈ K', π k v = v) : ∀ k ∈ K', π k (c • v) = c • v :=
  fun k hk => by rw [map_smul, hv k hk]

/-- The `K′`-fixed vectors `V^{K′} = {v : π(k)v = v for all k ∈ K′}` of a representation (B-only). -/
@[tf_aux "I.rep.def:fixed-vectors"]
def fixedVectors (π : Representation ℂ G V) (K' : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ k ∈ K', π k v = v}
  add_mem' hv hw := fixedVectors_add_mem π K' hv hw
  zero_mem' := fixedVectors_zero_mem π K'
  smul_mem' c _ hv := fixedVectors_smul_mem π K' c hv

/-- A representation `π` of a topological group `G` on a complex vector space is smooth if every stabilizer
`{g : π(g)v = v}` is open. -/
@[tf_id "I.rep.def:smooth-rep"]
def IsSmoothRep (π : Representation ℂ G V) : Prop :=
  ∀ v : V, IsOpen {g : G | π g v = v}

/-- `π` is admissible if it is smooth and `V^{K′}` is finite-dimensional for every compact open subgroup `K′`. -/
@[tf_id "I.rep.def:admissible-rep"]
def IsAdmissibleRep (π : Representation ℂ G V) : Prop :=
  IsSmoothRep π ∧
    ∀ K' : Subgroup G, IsCompact (K' : Set G) → IsOpen (K' : Set G) → FiniteDimensional ℂ (fixedVectors π K')

end Smooth

end GL2TF
