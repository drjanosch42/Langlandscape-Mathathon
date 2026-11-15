import AlgJL.VolI.P0.Quotient

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P0/Quotient.lean` at commit 84818d0. Dropped tests of stripped declarations (4): `quotient_defs_eq`, `haarStd_haar`, `unfolding_discrete_gl2`, `unipotent_quotient_volume_standard`. Added (fork): `quotient_defs_eq_alg`. -/


/-!
# Tests for `GL2TF.VolI.P0.Quotient`

Unfolding tests (M3 W1, statement level).
-/

open GL2TF MeasureTheory
open scoped ENNReal

namespace GL2TFTests

/-- `N(ℚ)` is the image of `N(ℚ) ≤ GL₂(ℚ)` in `N(𝔸)`. -/
theorem unipotentRat_eq :
    unipotentRat = ((unipotent ℚ).map (gl2Map (algebraMap ℚ Adele))).subgroupOf (unipotent Adele) :=
  rfl

/-- Unfolding of `T(ℚ)`, `B(ℚ)`, `ℝ_{>0} × Ẑ^×` and `G(ℚ) ≤ G(𝔸)^1` (fork: the measure and `L²` conjuncts of the
parent's `quotient_defs_eq` are dropped). -/
theorem quotient_defs_eq_alg :
    torusRat = ((ratIdeles.prod ratIdeles).map (diagHom Adele)).subgroupOf torusNormOne ∧
      borelRat = (GL2TF.borel ℚ).map (gl2Map (algebraMap ℚ Adele)) ∧
      idelePosUnits = {x : Idele | 0 < (x : Adele).1 ∧
        ∀ p : Nat.Primes, ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = (x : Adele).2 p} ∧
      gl2RatNormOne = gl2RatAdelic.subgroupOf normOneGroup :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### M3 G1 witnesses: exits `X.quot.thm:unfolding-discrete` and `I.quot.thm:unipotent-quotient-volume` -/

instance gl2Adele_t2 : T2Space (GL (Fin 2) Adele) := gl2Adelic_locallyCompact.1.2.1
instance gl2Adele_sc : SecondCountableTopology (GL (Fin 2) Adele) := gl2Adelic_locallyCompact.1.2.2
instance gl2RatAdelic_discrete : DiscreteTopology gl2RatAdelic := gl2Rat_discrete.2.2
end GL2TFTests
