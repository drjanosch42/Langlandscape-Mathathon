import AlgJL.VolI.P1.Jacquet

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/Jacquet.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolI.P1.Jacquet`

Named tests at `F = ℚ_[3]` (PLAN.md §2.3): the Jacquet module of the trivial representation is `ℂ`; the defining
formulas of `π_N`, `φ_N` and `Φ^♭`.
-/

open Matrix Matrix.GeneralLinearGroup ValuativeRel GL2TF GL2TF.Local

namespace GL2TFTests

/-- The Jacquet module of the trivial representation of `GL₂(ℚ₃)` on `ℂ` is one-dimensional (`V(N) = 0`). -/
theorem jacquetModule_trivial_finrank :
    Module.finrank ℂ (jacquetModule (Representation.trivial ℂ (GL (Fin 2) ℚ_[3]) ℂ)) = 1 := by
  have hker : Representation.Coinvariants.ker
      ((Representation.trivial ℂ (GL (Fin 2) ℚ_[3]) ℂ).comp (unipotent ℚ_[3]).subtype) = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨⟨n, v⟩, rfl⟩
    simp
  exact ((Submodule.quotEquivOfEqBot _ hker).finrank_eq).trans (Module.finrank_self ℂ)

/-- `π_N(t)(v + V(N)) = π(t)v + V(N)`. -/
theorem jacquetTorus_padic_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin 2) ℚ_[3]) V) (t : torus ℚ_[3]) (v : V) :
    jacquetTorus π t (Representation.Coinvariants.mk _ v) = Representation.Coinvariants.mk _ (π t v) :=
  rfl

/-- `φ_N(v + V(N)) = φ(v) + W(N)`. -/
theorem jacquetMap_padic_mk {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin 2) ℚ_[3]) V) (σ : Representation ℂ (GL (Fin 2) ℚ_[3]) W)
    (φ : Representation.IntertwiningMap π σ) (v : V) :
    jacquetMap π σ φ (Representation.Coinvariants.mk _ v) = Representation.Coinvariants.mk _ (φ v) :=
  rfl

/-- `Φ^♭(v + V(N)) = Φ(v)(1)`. -/
theorem frobeniusFlat_padic_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin 2) ℚ_[3]) V) (χ₁ χ₂ : QuasiChar ℚ_[3])
    (Φ : Representation.IntertwiningMap π (psRep χ₁ χ₂)) (v : V) :
    frobeniusFlat π χ₁ χ₂ Φ (Representation.Coinvariants.mk _ v) = (Φ v).1 1 :=
  rfl

end GL2TFTests
