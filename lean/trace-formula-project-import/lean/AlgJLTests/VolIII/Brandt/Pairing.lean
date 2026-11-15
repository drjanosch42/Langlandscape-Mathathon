import AlgJL.VolIII.Brandt.Pairing

/-!
# Tests for `GL2TF.VolIII.Brandt.Pairing`

Named test declarations for the tagged definitions of Q3 items 15, 17.
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF.Quat

/-- `ν(1) = 1`. -/
theorem normWeight_one {a b : ℤ} : normWeight (1 : (BHat a b)ˣ) = 1 := by
  have h : nrd (show QuatAlg GL2TF.FinAdele a b from ((1 : (BHat a b)ˣ) : BHat a b)) = 1 := by
    show nrd (1 : QuatAlg GL2TF.FinAdele a b) = 1
    simp [nrd]
  have h' : ∀ p : Nat.Primes, RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p
      (nrd (show QuatAlg GL2TF.FinAdele a b from ((1 : (BHat a b)ˣ) : BHat a b))) = 1 := fun p => by
    rw [h]; exact map_one _
  unfold normWeight
  simp only [h', Padic.valuation_one, neg_zero, zpow_zero, finprod_one]

/-- `⟨0, g⟩ = 0`. -/
theorem weightedPairing_zero_left {K : Type*} [Field K] {a b : ℤ} (O : QOrder a b) (k : ℕ)
    (g : (BHat a b)ˣ → symPowerModule K (k - 2)) : weightedPairing O k 0 g = 0 := by
  simp [weightedPairing]

end GL2TFTests
