/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.KppTower

/-! Shape and non-vacuity tests for `Langlandscape.Ordinary.KppTower` (S04-L9). -/

set_option autoImplicit false

namespace LanglandscapeTests.S04.KppTower

open Langlandscape.Local Langlandscape.Quat Langlandscape.Brandt Langlandscape.Ordinary

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

include hp in
/-- `lem:s04-hida` (`s04-hida`), test: the chain of levels `U_{s+1} ≤ U'_s ≤ U_s`. -/
theorem levels_chain (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) : d.Utower M p (s + 1) hN' ≤ d.Utower M p s hN :=
  (Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM).trans (UtowerP_le_Utower (hp := hp) hN)

/-- `lem:s04-hida`(a) (`s04-hida`), test: `UpAt` is defined at `U_0(q) U_s` (`p ∤ q`) and is `[x] ↦ ∑_j [x ϖ_j]`. -/
theorem UpAt_U0q_single {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    {q : ℕ} (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors)
    [Finite (XB (d.U0q q hq (d.Utower M p s hN)))] (x : (GL2TF.Quat.BHat d.a d.b)ˣ) (r : ℤ) :
    UpAt (d.U0q q hq (d.Utower M p s hN)) (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq) ℤ
        (Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q hq (d.Utower M p s hN)) x) r) =
      ∑ j : Fin p, Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q hq (d.Utower M p s hN))
        (x * localEmbedGL d p hp (varpi p j))) r :=
  UpAt_single _ x r

/-- `lem:s04-hida`(a) (`s04-hida`), test: at `U_s`, `UpAt` agrees with the stage-1 `UpHom` over `ℤ_[p]`. -/
theorem UpAt_Utower_Zp {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    [Finite (XB (d.Utower M p s hN))] :
    UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) ℤ_[p] =
      UpHom d M p s hN hp hM hpM hs ℤ_[p] :=
  UpAt_Utower_eq hM hpM hs ℤ_[p]

/-- `lem:s04-hida`(b) (`s04-hida`), test: global Hida (b) over `ℤ_[p]`. -/
theorem hida_b_Zp {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    [Finite (XB (d.Utower M p s hN))] [Finite (XB (UtowerP d M p s hN hp))]
    (a : ZX (UtowerP d M p s hN hp) ℤ_[p]) (ha : piP_push d M p s hN hp ℤ_[p] a = 0) :
    UpAt (UtowerP d M p s hN hp) (isUpLevel_UtowerP hM hpM hs) ℤ_[p] a = 0 :=
  Up_ker_push_eq_zero hM hpM hs ℤ_[p] a ha

/-- `lem:s04-hida`(c) (`s04-hida`), test (non-vacuity of `piPP_eq_iff`): `t = 1 ∈ 1 + p^s ℤ_p` gives
`π'' c = π'' c`. -/
theorem piPP_refl {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (c : XB (d.Utower M p (s + 1) hN')) :
    piPP d M p s hN hN' hp c = piPP d M p s hN hN' hp c :=
  (piPP_eq_iff hM hpM hs c c).2 ⟨1, by simp, by
    rw [diamondAct_eq_one hM hpM (Nat.le_add_left 1 s) 1 (by simp)]
    rfl⟩

end LanglandscapeTests.S04.KppTower
