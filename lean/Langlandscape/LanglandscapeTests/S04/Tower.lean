/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.Tower

/-!
# Tests for S04-L10 (`Ordinary/Tower.lean`)

Smoke tests: the separatedness inputs, `deg ∘ U_p = p • deg` on the tower, and the shapes of the stage-05 export
`ekillsA_tower` and of the control statements.
-/

set_option autoImplicit false

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Ordinary

namespace LanglandscapeTests.S04.Tower

/-- `lem:s04-ekills`(d) (`s04-ekills`), test: `ℤ_[p]` is `p`-adically separated. -/
theorem test_padicInt_sep (p : ℕ) [Fact p.Prime] (r : ℤ_[p])
    (h : ∀ k : ℕ, ∃ c : ℤ_[p], r = (p : ℤ_[p]) ^ k * c) : r = 0 :=
  padicInt_sep p r h

/-- `lem:s04-ekills`(d) (`s04-ekills`), test: `ZMod 25` is `5`-adically separated. -/
theorem test_zmodPow_sep (r : ZMod (5 ^ 2))
    (h : ∀ k : ℕ, ∃ c : ZMod (5 ^ 2), r = ((5 : ℕ) : ZMod (5 ^ 2)) ^ k * c) : r = 0 :=
  zmodPow_sep 5 2 r h

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s04-ekills`(a) (`s04-ekills`), test: `deg (U_p x) = p · deg x` on `ℤ_[p][X_s]`. -/
theorem test_deg_UpHom (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (x : ZX (d.Utower M p s hN) ℤ_[p]) :
    deg (Xs d M p s hN) ℤ_[p] (UpHom d M p s hN hp hM hpM hs ℤ_[p] x) =
      (p : ℤ_[p]) * deg (Xs d M p s hN) ℤ_[p] x :=
  deg_Up_apply _ _ (deg_comp_UpHom ℤ_[p] hM hpM hs) x

/-- `lem:s04-ekills`(a) (`s04-ekills`), test: the stage-05 export `ekillsA_tower`, every ordinary vector of
`ℤ_[p][X_s]` has degree `0` (formalized modulo `Hyp.PadicOrdDecomp`). -/
theorem test_ekillsA_tower (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) {x : ZX (d.Utower M p s hN) ℤ_[p]} (hx : x ∈ ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p])) :
    x ∈ LinearMap.ker (deg (Xs d M p s hN) ℤ_[p]) := by
  rw [← ekillsA_tower (hp := hp) hdec hM hpM hs] at hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hx
  exact y.2

/-- `lem:s04-hida`(d), `thm:s04-control`(a) (`s04-control`), test: unconditional surjectivity of
`π_* : e (ℤ/p^m)[X_{s+1}] → e (ℤ/p^m)[X_s]`. -/
theorem test_ord_control_finite_zmod (m : ℕ) {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Function.Surjective (ordPush (isUpLevel_Utower (hp := hp) (hN := hN') hM hpM (Nat.le_add_left 1 s))
      (isUpLevel_Utower (hp := hp) (hN := hN) hM hpM hs) (Utower_succ_le hN hN' hM) (ZMod (p ^ m))) :=
  (ord_control_finite_zmod m hM hpM hs).1

end LanglandscapeTests.S04.Tower
