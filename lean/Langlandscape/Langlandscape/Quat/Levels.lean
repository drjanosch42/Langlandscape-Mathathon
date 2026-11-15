/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalComponent

/-!
# Global levels `U_0(N)`, `U_1(N)`, the `p`-tower and `U_0(q)U` (S01-L3c)

Tex label `def:s01-levels`.  For `(N, D) = 1` the subgroup of `B̂^×` cut out inside `Ô^×` by the
local conditions `ι_ℓ(u_ℓ) ∈ K• ℓ (v_ℓ N)` at the primes `ℓ ∣ N` (and nothing at `ℓ ∤ N`).
The lower row of `U_1(N)` is `≡ (0, 1)`.

* `levelAt d N hN K`: the generic construction (`K` a family of local levels).
* `U0 d N hN`, `U1 d N hN`, `Utower d M p s hN := U1 d (M * p ^ s) hN`, `U0q d q hq U := U ⊓ U0 d q hq`.
* Inclusions: `U1_le_U0`, `U0_le_units`, `U0_one`, `U1_anti`, `Utower_antitone`, `Utower_le_U1p`.

Divisibility antitonicity needs `N' ≠ 0` (for `N' = 0` there are no local conditions).
-/

open GL2TF Langlandscape.Local

namespace Langlandscape.Quat

namespace DefiniteData

variable (d : DefiniteData)

/-- A prime factor of `N`, `N` coprime to `D`, does not divide `D` (`def:s01-levels`). -/
theorem not_dvd_D_of_mem_primeFactors {N : ℕ} (hN : N.Coprime d.D) {ℓ : ℕ}
    (hℓ : ℓ ∈ N.primeFactors) : ¬ ℓ ∣ d.D := by
  intro h
  have h1 := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓ) h
  rw [hN] at h1
  exact (Nat.prime_of_mem_primeFactors hℓ).one_lt.ne' (Nat.dvd_one.1 h1)

/-- Generic global level: `Ô^×` cut down by `ι_ℓ(u_ℓ) ∈ K ℓ (v_ℓ N)` for `ℓ ∣ N`
(`def:s01-levels`, tex label `s01-levels`). -/
noncomputable def levelAt (N : ℕ) (hN : N.Coprime d.D)
    (K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])) :
    Subgroup (BHat d.a d.b)ˣ :=
  d.Ohat ⊓ ⨅ ℓ : N.primeFactors,
    haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
    (K ℓ (N.factorization ℓ)).comap
      (localComponent d ℓ (d.not_dvd_D_of_mem_primeFactors hN ℓ.2))

/-- `U_0(N)` (`def:s01-levels`, tex label `s01-levels`). -/
noncomputable def U0 (N : ℕ) (hN : N.Coprime d.D) : Subgroup (BHat d.a d.b)ˣ :=
  d.levelAt N hN (fun ℓ _ e => K0 ℓ e)

/-- `U_1(N)`, lower row `≡ (0, 1)` (`def:s01-levels`, tex label `s01-levels`). -/
noncomputable def U1 (N : ℕ) (hN : N.Coprime d.D) : Subgroup (BHat d.a d.b)ˣ :=
  d.levelAt N hN (fun ℓ _ e => K1 ℓ e)

/-- The tower `U_s = U_1(M p^s)` (`def:s01-levels`, tex label `s01-levels`). -/
noncomputable def Utower (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D) :
    Subgroup (BHat d.a d.b)ˣ :=
  d.U1 (M * p ^ s) hN

/-- `U_0(q) U := U ∩ U_0(q)` (`def:s01-levels`, tex label `s01-levels`); meant for `U_q = O_q^×`. -/
noncomputable def U0q (q : ℕ) (hq : q.Coprime d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    Subgroup (BHat d.a d.b)ˣ :=
  U ⊓ d.U0 q hq

variable {d}

/-- Membership in a generic level (`def:s01-levels`, tex label `s01-levels`). -/
theorem mem_levelAt_iff {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])}
    {u : (BHat d.a d.b)ˣ} :
    u ∈ d.levelAt N hN K ↔ u ∈ d.Ohat ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors)
      (hD : ¬ ℓ ∣ d.D), localComponent d ℓ hD u ∈ K ℓ (N.factorization ℓ) := by
  simp only [levelAt, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine and_congr_right fun _ => ⟨fun h ℓ _ hℓ hD => h ⟨ℓ, hℓ⟩, fun h ℓ =>
    haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
    h ℓ ℓ.2 _⟩

/-- Membership in `U_0(N)` (`def:s01-levels`, tex label `s01-levels`). -/
theorem mem_U0_iff {N : ℕ} {hN : N.Coprime d.D} {u : (BHat d.a d.b)ˣ} :
    u ∈ d.U0 N hN ↔ u ∈ d.Ohat ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors)
      (hD : ¬ ℓ ∣ d.D), localComponent d ℓ hD u ∈ K0 ℓ (N.factorization ℓ) :=
  mem_levelAt_iff

/-- Membership in `U_1(N)` (`def:s01-levels`, tex label `s01-levels`). -/
theorem mem_U1_iff {N : ℕ} {hN : N.Coprime d.D} {u : (BHat d.a d.b)ˣ} :
    u ∈ d.U1 N hN ↔ u ∈ d.Ohat ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors)
      (hD : ¬ ℓ ∣ d.D), localComponent d ℓ hD u ∈ K1 ℓ (N.factorization ℓ) :=
  mem_levelAt_iff

/-- Membership in `U_0(q) U` (`def:s01-levels`, tex label `s01-levels`). -/
theorem mem_U0q_iff {q : ℕ} {hq : q.Coprime d.D} {U : Subgroup (BHat d.a d.b)ˣ}
    {u : (BHat d.a d.b)ˣ} : u ∈ d.U0q q hq U ↔ u ∈ U ∧ u ∈ d.U0 q hq := Iff.rfl

/-- `U_1(N) ≤ U_0(N)` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U1_le_U0 (N : ℕ) (hN : N.Coprime d.D) : d.U1 N hN ≤ d.U0 N hN := fun _ hu =>
  mem_U0_iff.2 ⟨(mem_U1_iff.1 hu).1, fun ℓ _ hℓ hD => (K1_le_K0 _) ((mem_U1_iff.1 hu).2 ℓ hℓ hD)⟩

/-- `U_0(N) ≤ Ô^×` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U0_le_units (N : ℕ) (hN : N.Coprime d.D) : d.U0 N hN ≤ d.Ohat := fun _ hu =>
  (mem_U0_iff.1 hu).1

/-- `U_1(N) ≤ Ô^×` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U1_le_units (N : ℕ) (hN : N.Coprime d.D) : d.U1 N hN ≤ d.Ohat :=
  (U1_le_U0 N hN).trans (U0_le_units N hN)

/-- `U_0(1) = Ô^×` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U0_one (h : (1 : ℕ).Coprime d.D := Nat.coprime_one_left _) : d.U0 1 h = d.Ohat := by
  refine le_antisymm (U0_le_units 1 h) fun u hu => mem_U0_iff.2 ⟨hu, fun ℓ _ hℓ => ?_⟩
  simp at hℓ

/-- `U_1(1) = Ô^×` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U1_one (h : (1 : ℕ).Coprime d.D := Nat.coprime_one_left _) : d.U1 1 h = d.Ohat := by
  refine le_antisymm (U1_le_units 1 h) fun u hu => mem_U1_iff.2 ⟨hu, fun ℓ _ hℓ => ?_⟩
  simp at hℓ

/-- Antitonicity of `U_0` under divisibility (`def:s01-levels`, tex label `s01-levels`). -/
theorem U0_anti {N N' : ℕ} (h : N ∣ N') (hN' : N' ≠ 0) (hN : N.Coprime d.D)
    (hN'' : N'.Coprime d.D) : d.U0 N' hN'' ≤ d.U0 N hN := fun u hu => by
  refine mem_U0_iff.2 ⟨(mem_U0_iff.1 hu).1, fun ℓ _ hℓ hD => ?_⟩
  have hℓ' : ℓ ∈ N'.primeFactors := Nat.primeFactors_mono h hN' hℓ
  exact K0_anti ((Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hN' h) hN').2 h ℓ)
    ((mem_U0_iff.1 hu).2 ℓ hℓ' hD)

/-- Antitonicity of `U_1` under divisibility (`def:s01-levels`, tex label `s01-levels`). -/
theorem U1_anti {N N' : ℕ} (h : N ∣ N') (hN' : N' ≠ 0) (hN : N.Coprime d.D)
    (hN'' : N'.Coprime d.D) : d.U1 N' hN'' ≤ d.U1 N hN := fun u hu => by
  refine mem_U1_iff.2 ⟨(mem_U1_iff.1 hu).1, fun ℓ _ hℓ hD => ?_⟩
  have hℓ' : ℓ ∈ N'.primeFactors := Nat.primeFactors_mono h hN' hℓ
  exact K1_anti ((Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hN' h) hN').2 h ℓ)
    ((mem_U1_iff.1 hu).2 ℓ hℓ' hD)

/-- The tower `U_s` is antitone in `s` (`def:s01-levels`, tex label `s01-levels`). -/
theorem Utower_antitone {M p s s' : ℕ} (hs : s ≤ s') (hM : M ≠ 0) (hp : p ≠ 0)
    (h : (M * p ^ s).Coprime d.D) (h' : (M * p ^ s').Coprime d.D) :
    d.Utower M p s' h' ≤ d.Utower M p s h :=
  U1_anti (mul_dvd_mul_left M (pow_dvd_pow p hs)) (mul_ne_zero hM (pow_ne_zero _ hp)) h h'

/-- `U_s ≤ U_1(p)` for `s ≥ 1` (`def:s01-levels`, tex label `s01-levels`). -/
theorem Utower_le_U1p {M p s : ℕ} (hs : 1 ≤ s) (hM : M ≠ 0) (hp : p ≠ 0)
    (h : (M * p ^ s).Coprime d.D) (hpD : p.Coprime d.D) :
    d.Utower M p s h ≤ d.U1 p hpD :=
  U1_anti ((dvd_pow_self p (by omega)).trans (dvd_mul_left _ _))
    (mul_ne_zero hM (pow_ne_zero _ hp)) hpD h

/-- `U_0(q) U ≤ U` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U0q_le (q : ℕ) (hq : q.Coprime d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    d.U0q q hq U ≤ U := inf_le_left

/-- `U_0(q) U ≤ U_0(q)` (`def:s01-levels`, tex label `s01-levels`). -/
theorem U0q_le_U0 (q : ℕ) (hq : q.Coprime d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    d.U0q q hq U ≤ d.U0 q hq := inf_le_right

end DefiniteData

end Langlandscape.Quat
