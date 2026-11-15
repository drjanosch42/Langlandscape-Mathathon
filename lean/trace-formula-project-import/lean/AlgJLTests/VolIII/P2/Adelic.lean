import AlgJL.VolIII.P2.Adelic

/-!
# Tests for `GL2TF.VolIII.P2.Adelic`

Named test declarations for the tagged definitions of Q2 items 37, 39 (plan §1.2) and their B-only plumbing
(the instances on `BHat`, `finEmbed`, `orderCompletionUnits`, `finiteIdeleLattice`).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat

/-- `ι(1) = 1` in `B̂` (ring structure of `BHat` and the embedding `finEmbed`). -/
theorem finEmbed_one (a b : ℤ) : finEmbed a b 1 = (1 : BHat a b) :=
  map_one _

/-- The `𝔸_f`-algebra structure of `B̂` is unital. -/
theorem algebraMap_finAdele_bHat_one (a b : ℤ) : algebraMap FinAdele (BHat a b) 1 = 1 :=
  map_one _

/-- The coordinate map `B̂ → 𝔸_f⁴` is continuous (it defines the topology of `B̂`). -/
theorem continuous_bHat_coords (a b : ℤ) :
    Continuous (fun x : BHat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x) :=
  continuous_induced_dom

/-- `ι(L) ⊆ L̂`. -/
theorem finEmbed_mem_latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) {z : QuatAlg ℚ a b}
    (hz : z ∈ L) : finEmbed a b z ∈ latticeCompletion L :=
  Submodule.subset_span ⟨z, hz, rfl⟩

/-- `−1 ∈ Ô^×`. -/
theorem neg_one_mem_orderCompletionUnits {a b : ℤ} (O : QOrder a b) :
    (-1 : (BHat a b)ˣ) ∈ orderCompletionUnits O := by
  have h : (-1 : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) :=
    Submodule.neg_mem _ (one_mem_orderCompletion O)
  exact ⟨by simpa using h, by simpa using h⟩

/-- `O ⊆ L_1 = ι⁻¹(Ô)`. -/
theorem order_le_finiteIdeleLattice_one {a b : ℤ} (O : QOrder a b) :
    Subalgebra.toSubmodule O.toSubalgebra ≤ finiteIdeleLattice O 1 := fun z hz =>
  ⟨finEmbed a b z, Submodule.subset_span ⟨z, hz, rfl⟩, by simp⟩

end GL2TFTests
