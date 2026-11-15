/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Stab
import Langlandscape.Quat.LevelFinite

/-!
# The mass of the `p`-tower `|S_s|` (S01-L4c)

Tex label `thm:s01-mass`(c),(d).  For `p ≥ 5` and `s ≥ 1` all stabilisers `Γ_x(U_s)` are trivial (S01-L5b), so
`|S_s| = |X_B(U_s)| = massFull U_s`, and the level change `[Ô^× : U_s] = ψ(M p^s) φ(M p^s)` (S01-L4b) together with
Eichler's mass formula (the import's `GL2TF.Hyp.EichlerMass`, an explicit hypothesis) gives
`|S_s| = φ(D)/24 · ψ(M p^s) φ(M p^s)`.

Status: *formalized* (modulo the hypothesis `Hyp.EichlerMass`).
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

/-- `thm:s01-mass`(d) helper: for squarefree `D`, `φ(D) = ∏_{p ∣ D} (p - 1)` in `ℚ` (`s01-mass`). -/
theorem totient_cast_eq_prod_of_squarefree {D : ℕ} (hsq : Squarefree D) :
    (Nat.totient D : ℚ) = ∏ p ∈ D.primeFactors, ((p : ℚ) - 1) := by
  have hD0 : D ≠ 0 := hsq.ne_zero
  rw [Nat.totient_eq_prod_factorization hD0, Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : D.factorization p = 1 :=
    le_antisymm (hsq.natFactorization_le_one p)
      (hpp.factorization_pos_of_dvd hD0 (Nat.dvd_of_mem_primeFactors hp))
  have h1 : 1 ≤ p := hpp.one_lt.le
  rw [hk, Nat.cast_mul, Nat.cast_sub h1]
  simp

/-- `thm:s01-mass`(c),(d): `|S_s| = |X_B(U_s)| = φ(D)/24 · ψ(M p^s) φ(M p^s)` in `ℚ`, for `p ≥ 5` prime,
`s ≥ 1`, under Eichler's mass formula `hM` (`s01-mass`). -/
theorem card_XB_Utower (d : DefiniteData) {M p s : ℕ} (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hpp : p.Prime) (hp : 5 ≤ p) (hs : 1 ≤ s) (hM0 : M ≠ 0) (hpD : p.Coprime d.D)
    (hN : (M * p ^ s).Coprime d.D) :
    (Nat.card (XB (d.Utower M p s hN)) : ℚ) =
      (Nat.totient d.D : ℚ) / 24 *
        (GL2TF.Explicit.dedekindPsi (M * p ^ s) * (Nat.totient (M * p ^ s) : ℚ)) := by
  classical
  have : NeZero (M * p ^ s) := ⟨mul_ne_zero hM0 (pow_ne_zero _ hpp.ne_zero)⟩
  have hle : d.Utower M p s hN ≤ d.Ohat := DefiniteData.U1_le_units _ hN
  have hgam : ∀ x, Gam (d.Utower M p s hN) x = ⊥ := fun x =>
    Gam_eq_bot_of_le_U1 d hpp hp hpD (DefiniteData.Utower_le_U1p hs hM0 hpp.ne_zero hN hpD) x
  have hrel : (((d.Utower M p s hN).relIndex d.Ohat : ℕ) : ℚ) =
      GL2TF.Explicit.dedekindPsi (M * p ^ s) * (Nat.totient (M * p ^ s) : ℚ) :=
    d.relIndex_U1 (M * p ^ s) hN
  have hne : (d.Utower M p s hN).relIndex d.Ohat ≠ 0 := d.relIndex_U1_ne_zero (M * p ^ s) hN
  have key := GL2TF.Quat.mass_orbit_count (d.Utower M p s hN) d.Ohat hle hne (d.instFiniteXBOhat)
  change massFull (d.Utower M p s hN) = _ * massFull d.Ohat at key
  have h0 : massFull d.Ohat = 1 / 24 * ∏ q ∈ d.D.primeFactors, ((q : ℚ) - 1) :=
    (massFull_units_eq_mass d.O.1).trans (hM d.hD)
  have h1 : ∀ c : XB (d.Utower M p s hN),
      (1 : ℚ) / (Nat.card (Gam (d.Utower M p s hN) (Quotient.out c)) : ℚ) = 1 := fun c => by
    rw [hgam, Subgroup.card_bot]; simp
  have hcard : massFull (d.Utower M p s hN) = (Nat.card (XB (d.Utower M p s hN)) : ℚ) := by
    have := Fintype.ofFinite (XB (d.Utower M p s hN))
    rw [massFull, finsum_congr h1, finsum_eq_sum_of_fintype]
    simp [Nat.card_eq_fintype_card]
  rw [← hcard, key, hrel, h0, ← totient_cast_eq_prod_of_squarefree d.squarefree]
  ring

end Langlandscape.Quat
