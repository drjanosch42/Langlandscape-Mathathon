/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.EKills

/-! Non-vacuity checks for S04-L4 (`Ordinary/EKills.lean`, `lem:s04-ekills`(a),(d)), over `ℚ` with
`p = 0` and `X = Fin 2`. -/

@[expose] public section

open Langlandscape.Ordinary

namespace Langlandscape.S04Tests.EKills

noncomputable section

/-- If `T = 0` then `ordPart T = ⊥` and `nilPart 0 T = ⊤`, so `T` has an ordinary decomposition
(`s04-ekills`, test helper). -/
lemma hasOrdDecomp_of_zero {M : Type*} [AddCommGroup M] [Module ℚ M] (T : Module.End ℚ M)
    (hT : ∀ m, T m = 0) : HasOrdDecomp (0 : ℚ) T := by
  have h1 : ordPart T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := mem_ordPart.1 hx 1
    rw [pow_one, hT] at hy
    rw [Submodule.mem_bot]
    exact hy.symm
  have h2 : nilPart (0 : ℚ) T = ⊤ := by
    rw [eq_top_iff]
    intro m _
    refine mem_nilPart.2 fun k => ⟨1, ?_⟩
    rw [pow_one, hT]
    exact Submodule.zero_mem _
  unfold HasOrdDecomp
  rw [h1, h2]
  exact isCompl_bot_top

/-- `deg` of a sum of two basis vectors (`s04-ekills`). -/
lemma deg_two (x y : Fin 2) : deg (Fin 2) ℤ (Finsupp.single x 1 + Finsupp.single y 2) = 3 := by
  norm_num [deg_single]

/-- `U = p = 0` on `ℚ`: `ordPart = ⊥` (`lem:s04-ekills`(a), `s04-ekills`). -/
lemma ordPart_zero_scalar : ordPart (LinearMap.lsmul ℚ ℚ (0 : ℚ)) = ⊥ :=
  ordPart_deg_eq_bot (0 : ℚ)
    (hasOrdDecomp_of_zero _ (fun m => by simp))

/-- `Up = 0`, `p = 0` satisfies `deg ∘ Up = p • deg` (`s04-ekills`). -/
lemma deg_comp_zero : (deg (Fin 2) ℚ).comp (0 : Module.End ℚ (Fin 2 →₀ ℚ)) = (0 : ℚ) • deg (Fin 2) ℚ := by
  ext; simp

/-- `e (ker deg) = e ⊤` for `Up = 0` (`lem:s04-ekills`(a), `s04-ekills`). -/
lemma ordPart_ker_deg_zero :
    Submodule.map (LinearMap.ker (deg (Fin 2) ℚ)).subtype
      (ordPart (R := ℚ) (M := ↥(LinearMap.ker (deg (Fin 2) ℚ)))
        (UpKer (0 : Module.End ℚ (Fin 2 →₀ ℚ)) (0 : ℚ) deg_comp_zero)) =
      ordPart (0 : Module.End ℚ (Fin 2 →₀ ℚ)) :=
  ordPart_ker_deg _ _ deg_comp_zero (hasOrdDecomp_of_zero _ (fun m => by simp))
    (hasOrdDecomp_of_zero _ (fun m => by simp))

/-- `perfect_ordPart_pairing` for `Up = Upt = 0` (`lem:s04-ekills`(d), `s04-ekills`). -/
lemma perfect_zero :
    ((deltaPairing (Fin 2) ℚ).domRestrict₁₂ (ordPart (0 : Module.End ℚ (Fin 2 →₀ ℚ)))
      (ordPart (0 : Module.End ℚ (Fin 2 →₀ ℚ)))).IsPerfPair :=
  perfect_ordPart_pairing (0 : ℚ)
    (fun r h => by
      obtain ⟨s, hs⟩ := h 1
      simpa using hs)
    0 0 (fun x y => by simp) (hasOrdDecomp_of_zero _ (fun m => by simp))
    (hasOrdDecomp_of_zero _ (fun m => by simp))

/-! ### `e ≠ e*`: a non-self-adjoint idempotent `Up` -/

/-- `Up (a, b) = (a + b, 0)`, an idempotent that is not self-adjoint for `δ` (`s04-ekills`). -/
def Up : Module.End ℚ (Fin 2 →₀ ℚ) :=
  Finsupp.lsum ℚ (fun _ : Fin 2 =>
    LinearMap.toSpanSingleton ℚ (Fin 2 →₀ ℚ) (Finsupp.single 0 1))

/-- The `δ`-adjoint of `Up`: `Upt (a, b) = (a, a)` (`s04-ekills`). -/
def Upt : Module.End ℚ (Fin 2 →₀ ℚ) :=
  Finsupp.lsum ℚ (fun i : Fin 2 =>
    if i = 0 then
      LinearMap.toSpanSingleton ℚ (Fin 2 →₀ ℚ) (Finsupp.single 0 1 + Finsupp.single 1 1)
    else 0)

/-- `Up [i] r = [0] r` (`s04-ekills`). -/
lemma Up_single (i : Fin 2) (r : ℚ) : Up (Finsupp.single i r) = Finsupp.single 0 r := by
  unfold Up
  rw [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul,
    mul_one]

/-- `Upt [0] r = [0] r + [1] r`, `Upt [1] r = 0` (`s04-ekills`). -/
lemma Upt_single (i : Fin 2) (r : ℚ) :
    Upt (Finsupp.single i r) = if i = 0 then Finsupp.single 0 r + Finsupp.single 1 r else 0 := by
  by_cases h : i = 0
  · subst h
    unfold Upt
    rw [Finsupp.lsum_single, if_pos rfl, if_pos rfl, LinearMap.toSpanSingleton_apply, smul_add,
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  · unfold Upt
    rw [Finsupp.lsum_single, if_neg h, if_neg h, LinearMap.zero_apply]

/-- `Upt` is `δ`-adjoint to `Up` (`s04-ekills`). -/
lemma Up_adj (x y : Fin 2 →₀ ℚ) :
    deltaPairing (Fin 2) ℚ (Up x) y = deltaPairing (Fin 2) ℚ x (Upt y) := by
  have key : (deltaPairing (Fin 2) ℚ).compl₁₂ Up LinearMap.id
      = (deltaPairing (Fin 2) ℚ).compl₂ Upt := by
    refine Finsupp.lhom_ext fun i r => ?_
    refine Finsupp.lhom_ext fun j s => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Up_single, Upt_single, deltaPairing_single_left, Finsupp.single_apply]
  exact LinearMap.congr_fun₂ key x y

/-- `(Upt y) k = y 0` (`s04-ekills`). -/
lemma Upt_apply (y : Fin 2 →₀ ℚ) : ∀ k : Fin 2, Upt y k = y 0 := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => intro k; simp [ha k, hb k]
  | single i r =>
    intro k
    fin_cases i <;> fin_cases k <;> simp [Upt_single, Finsupp.single_apply]

/-- `e ≠ e*`: the ordinary parts of `Up` and of its `δ`-adjoint `Upt` differ
(`lem:s04-ekills`(d), `s04-ekills`). -/
theorem ordPart_ne_ordPart_adjoint : ordPart Up ≠ ordPart Upt := by
  intro h
  have hmem : (Finsupp.single (0 : Fin 2) (1 : ℚ)) ∈ ordPart Up := by
    refine mem_ordPart.2 fun n => ⟨Finsupp.single 0 1, ?_⟩
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, Up_single]
  rw [h] at hmem
  obtain ⟨y, hy⟩ := mem_ordPart.1 hmem 1
  have h0 := congrArg (fun f : Fin 2 →₀ ℚ => f 0) hy
  have h1 := congrArg (fun f : Fin 2 →₀ ℚ => f 1) hy
  simp only [pow_one, Upt_apply] at h0 h1
  simp [Finsupp.single_apply] at h0 h1
  exact one_ne_zero (h0.symm.trans h1)

end

end Langlandscape.S04Tests.EKills
