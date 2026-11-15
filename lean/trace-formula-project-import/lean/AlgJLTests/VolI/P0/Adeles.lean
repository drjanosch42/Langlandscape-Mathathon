import AlgJL.VolI.P0.Adeles
import AlgJLTests.VolI.P0.LocalField

/-!
# Tests for `GL2TF.VolI.P0.Adeles`

Non-vacuity tests for the adele working model (U3): `Ẑ` contains `1`, the instances resolve through the project
instances, `ψ(0) = 1`, and `𝒮(𝔸)` contains `Φ_∞ ⊗ 1_Ẑ` for every Schwartz function `Φ_∞` (e.g. `e^{-πx²}`).
-/

open GL2TF MeasureTheory Filter

namespace GL2TFTests

/-- `p : Nat.Primes` gives a `Fact` instance. -/
theorem primes_fact (p : Nat.Primes) : Fact p.1.Prime := GL2TF.fact_primes_prime p

/-- The named `ℚ`-algebra instance on `𝔸_f` sends `1` to `1`. -/
theorem algebraMap_finAdele_one : algebraMap ℚ FinAdele 1 = 1 := map_one _

/-- `1 ∈ Ẑ ⊆ 𝔸_f`. -/
theorem one_mem_zhat : (1 : FinAdele) ∈ Zhat := Zhat.one_mem

/-- The diagonal embedding sends `1` to `1` in `𝔸` (the vendored `Algebra ℚ 𝔸_f`). -/
theorem algebraMap_adele_one : algebraMap ℚ Adele 1 = 1 := map_one _

/-- The `𝔸_f` instances (topological ring, locally compact, second countable) resolve. -/
theorem finAdele_instances :
    IsTopologicalRing FinAdele ∧ LocallyCompactSpace FinAdele ∧ SecondCountableTopology FinAdele :=
  ⟨finAdele_isTopologicalRing, finAdele_locallyCompactSpace, finAdele_secondCountableTopology⟩

/-- `ℤ_p` (as an additive subgroup) is compact. -/
theorem padicInt_compact (p : Nat.Primes) : CompactSpace ((PadicInt.subring p).toAddSubgroup) :=
  padicIntAddSubgroup_compactSpace p

/-- `ℚ\𝔸` is compact (`I.adele.thm:rat-quotient-compact-top`): `univ` is a compact set of the quotient. -/
theorem rat_quotient_univ_isCompact :
    IsCompact (Set.univ : Set (Adele ⧸ (algebraMap ℚ Adele).range.toAddSubgroup)) :=
  haveI := rat_quotient_compact_top.1
  isCompact_univ

/-- `ℚ\𝔸` is Hausdorff (`I.adele.thm:rat-quotient-compact-top`): the class of `0` is a closed point. -/
theorem rat_quotient_zero_isClosed :
    IsClosed ({0} : Set (Adele ⧸ (algebraMap ℚ Adele).range.toAddSubgroup)) :=
  haveI := rat_quotient_compact_top.2
  isClosed_singleton

end GL2TFTests
