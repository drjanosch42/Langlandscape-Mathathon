import AlgJL.VolI.P0.LocalField

/-!
# Tests for `GL2TF.VolI.P0.LocalField`

Non-vacuity examples (PLAN.md §2.3): the interface is inhabited by `ℚ_[p]`, the alias provides Mathlib's derived
instances, and the defined objects `unif`, `q` behave as specified.
-/

open ValuativeRel GL2TF.Local MeasureTheory

namespace GL2TFTests

/-- `ℚ_[p]` is a non-archimedean local field. -/
theorem padic_isNALF (p : ℕ) [Fact p.Prime] : IsNALF ℚ_[p] := GL2TF.Local.padic_isNALF

/-- The alias provides Mathlib's derived instances. -/
theorem isNALF_dvr (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F] :
    IsDiscreteValuationRing 𝒪[F] ∧ Finite 𝓀[F] ∧ CompactSpace 𝒪[F] :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The fixed uniformizer generates the maximal ideal. -/
theorem unif_spec (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F] :
    𝓂[F] = Ideal.span {unif F} :=
  Classical.choose_spec (p := fun ϖ : 𝒪[F] ↦ 𝓂[F] = Ideal.span {ϖ}) _

/-- The residue cardinality is positive. -/
theorem q_pos (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F] : 0 < q F :=
  Nat.card_pos

/-- Second countability at `ℚ_[p]`, through the project instance. -/
theorem padic_secondCountable (p : ℕ) [Fact p.Prime] : SecondCountableTopology ℚ_[p] :=
  GL2TF.Local.secondCountableTopology ℚ_[p]

/-! ### M3 (U2) -/

/-- The Borel σ-algebra of `ℚ_[p]` and its `BorelSpace` instance, through the project instances. -/
theorem padic_borelSpace' (p : ℕ) [Fact p.Prime] :
    @BorelSpace ℚ_[p] _ GL2TF.Local.padic_measurableSpace :=
  GL2TF.Local.padic_borelSpace

/-- `|0|_F = 0` and `|1|_F = 1`. -/
theorem normAbs_zero_one (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F] :
    normAbs F 0 = 0 ∧ normAbs F 1 = 1 :=
  ⟨by simp [normAbs], normAbs_one F⟩

end GL2TFTests
