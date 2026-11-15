/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelBridge
import Langlandscape.Quat.Weights

/-!
# Finiteness of `X_B` at the standard levels (S01-L16a, audit fix R2)

Tex labels `prop:s01-finite`, `thm:s01-mass`(c).  `X_B(U)` is finite for `U = Ô^×` (the import's
`classSet_finite_of_open`), hence for every `U ≤ Ô^×` of finite index (`XB_finite_of_relIndex`), in particular for
`U_0(N)`, `U_1(N)` (`[Ô^× : U_0(N)] = ψ(N)`, `[Ô^× : U_1(N)] = ψ(N) φ(N)`, S01-L4b) and the tower `U_s`.

* `dedekindPsi_pos` : `ψ(N) > 0` for `N ≠ 0`.
* `DefiniteData.levelAt_zero` : `levelAt 0 = Ô^×` (no local conditions).
* `DefiniteData.relIndex_U0_ne_zero`, `DefiniteData.relIndex_U1_ne_zero` (`N ≠ 0`).
* Instances `DefiniteData.instFiniteXBOhat`, `DefiniteData.finite_XB_U0`, `DefiniteData.finite_XB_U1`,
  `DefiniteData.finite_XB_Utower` (every `N`, also `N = 0`).

Status: *formalized*.
-/

namespace Langlandscape.Quat

open GL2TF

/-- `thm:s01-mass`(c) helper: `ψ(N) > 0` for `N ≠ 0` (`s01-mass`). -/
theorem dedekindPsi_pos {N : ℕ} (hN : N ≠ 0) : 0 < GL2TF.Explicit.dedekindPsi N := by
  unfold GL2TF.Explicit.dedekindPsi
  refine mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) (Finset.prod_pos fun q _ => ?_)
  positivity

namespace DefiniteData

variable (d : DefiniteData)

/-- `def:s01-levels`: at `N = 0` there are no local conditions, `levelAt 0 = Ô^×` (`s01-levels`). -/
theorem levelAt_zero (hN : (0 : ℕ).Coprime d.D)
    (K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])) :
    d.levelAt 0 hN K = d.Ohat := by
  refine le_antisymm (fun u hu => (mem_levelAt_iff.1 hu).1) fun u hu => mem_levelAt_iff.2 ⟨hu, fun ℓ _ hℓ => ?_⟩
  simp at hℓ

/-- `thm:s01-mass`(c): `[Ô^× : U_0(N)] ≠ 0` for `N ≠ 0` (`s01-mass`). -/
theorem relIndex_U0_ne_zero (N : ℕ) [NeZero N] (hN : N.Coprime d.D) :
    (d.U0 N hN).relIndex d.Ohat ≠ 0 := by
  intro h0
  have h := d.relIndex_U0 N hN
  rw [h0, Nat.cast_zero] at h
  exact (dedekindPsi_pos (NeZero.ne N)).ne h

/-- `thm:s01-mass`(c): `[Ô^× : U_1(N)] ≠ 0` for `N ≠ 0` (`s01-mass`). -/
theorem relIndex_U1_ne_zero (N : ℕ) [NeZero N] (hN : N.Coprime d.D) :
    (d.U1 N hN).relIndex d.Ohat ≠ 0 := by
  intro h0
  have h := d.relIndex_U1 N hN
  rw [h0, Nat.cast_zero] at h
  have htot : (0 : ℚ) < (Nat.totient N : ℚ) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  exact (mul_pos (dedekindPsi_pos (NeZero.ne N)) htot).ne h

/-- `prop:s01-finite`: `X_B(Ô^×)` is finite (instance form). -/
instance instFiniteXBOhat : Finite (XB d.Ohat) :=
  XB_finite d le_rfl d.Ohat_isOpen

/-- `prop:s01-finite`: `X_B(U_0(N))` is finite, for every `N` (`U_0(0) = Ô^×`). -/
instance finite_XB_U0 (N : ℕ) (hN : N.Coprime d.D) : Finite (XB (d.U0 N hN)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · rw [U0, levelAt_zero]
    exact d.instFiniteXBOhat
  · have : NeZero N := ⟨hpos.ne'⟩
    exact XB_finite_of_relIndex (U0_le_units N hN) (d.relIndex_U0_ne_zero N hN)

/-- `prop:s01-finite`: `X_B(U_1(N))` is finite, for every `N` (`U_1(0) = Ô^×`). -/
instance finite_XB_U1 (N : ℕ) (hN : N.Coprime d.D) : Finite (XB (d.U1 N hN)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · rw [U1, levelAt_zero]
    exact d.instFiniteXBOhat
  · have : NeZero N := ⟨hpos.ne'⟩
    exact XB_finite_of_relIndex (U1_le_units N hN) (d.relIndex_U1_ne_zero N hN)

/-- `prop:s01-finite`: `X_B(U_s)` is finite for the tower `U_s = U_1(M p^s)`. -/
instance finite_XB_Utower (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D) :
    Finite (XB (d.Utower M p s hN)) :=
  d.finite_XB_U1 (M * p ^ s) hN

end DefiniteData

end Langlandscape.Quat
