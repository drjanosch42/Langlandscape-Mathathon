import AlgJL.VolIII.Brandt.HeckeLocal

/-!
# Tests for `GL2TF.VolIII.Brandt.HeckeLocal`

Named test declaration for the tagged definition of Q3 item 28.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `Θ_p(0) = 0`. -/
theorem localHeckeEmbedding_zero {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (p : Nat.Primes) (hpD : ¬ (p : ℕ) ∣ D) :
    localHeckeEmbedding O₀ hD φ p hpD 0 = 0 := by
  funext x
  simp [localHeckeEmbedding]

end GL2TFTests
