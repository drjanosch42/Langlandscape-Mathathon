/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.TowerRank

/-!
# Tests for S04-L10b (`Ordinary/TowerRank.lean`)

Smoke tests: `Δ_s` is a finite `p`-group, its action on `X_s` is free, `U_p` commutes with it, and the shapes of the
freeness statements `ordFree_finite` (`ℤ_[p]`, modulo `Hyp.PadicOrdDecomp`) and `ordFree_finite_zmod`.
-/

set_option autoImplicit false

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Ordinary

open scoped Classical

namespace LanglandscapeTests.S04.TowerRank

/-- `prop:s04-freeA` (`s04-freeA`), test: `Δ_3` is a `p`-group. -/
theorem test_isPGroup_deltaS (p : ℕ) [Fact p.Prime] : IsPGroup p (DeltaS p 3) :=
  isPGroup_deltaS p 3

/-- `prop:s04-freeA` (`s04-freeA`), test: `t ↦ 1` in `(ℤ/p^s)^×` iff `t ≡ 1 mod p^s`. -/
theorem test_redHom_eq_one_iff (p : ℕ) [Fact p.Prime] (s : ℕ) (t : unitsCong p 1) :
    redHom p s t = 1 ↔ (p : ℤ_[p]) ^ s ∣ ((t : ℤ_[p]ˣ) : ℤ_[p]) - 1 :=
  redHom_eq_one_iff p s t

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `prop:s04-freeA`, `lem:s01-stab` (b′) (`s04-freeA`), test: a class of `Δ_s` fixing a point of `X_s` is trivial
(`p ≥ 5`). -/
theorem test_deltaAct_free (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) (g : DeltaS p s)
    (c : XB (d.Utower M p s hN)) (hc : deltaAct (hp := hp) hM hpM hs g c = c) : g = 1 :=
  deltaAct_free hM hpM hs h5 g c hc

/-- `prop:s04-freeA`, `lem:s01-Up`(e) (`s04-freeA`), test: `U_p` commutes with the diamond action on `ℤ_[p][X_s]`
(as linear maps). -/
theorem test_UpHom_comm_diamondAct (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : ℤ_[p]ˣ) :
    UpHom d M p s hN hp hM hpM hs ℤ_[p] ∘ₗ
        Finsupp.lmapDomain ℤ_[p] ℤ_[p] (diamondAct (hp := hp) (hN := hN) hM hpM hs t) =
      Finsupp.lmapDomain ℤ_[p] ℤ_[p] (diamondAct (hp := hp) (hN := hN) hM hpM hs t) ∘ₗ
        UpHom d M p s hN hp hM hpM hs ℤ_[p] :=
  UpHom_comm_diamondAct (hN := hN) (hp := hp) ℤ_[p] hM hpM hs t

/-- `prop:s04-freeA` (`s04-freeA`), test: `ℤ_[p][X_s]` is free over `ℤ_[p][Δ_s]`. -/
theorem test_towerMod_free (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra ℤ_[p] (DeltaS p s)) (TowerMod d M p s hN hp ℤ_[p] hM hpM hs) :=
  (towerMod_free (hN := hN) (hp := hp) ℤ_[p] hM hpM hs h5).1

/-- `prop:s04-freeA` (`s04-freeA`), test: `e ℤ_p[X_s]` is free over `ℤ_p[Δ_s]` (modulo `Hyp.PadicOrdDecomp`). -/
theorem test_ordFree_finite (hdec : Langlandscape.Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra ℤ_[p] (DeltaS p s)) (ordPartTower d M p s hN hp ℤ_[p] hM hpM hs) :=
  (ordFree_finite (hN := hN) (hp := hp) hdec hM hpM hs h5).1

/-- `prop:s04-freeA` (`s04-freeA`), test: `e (ℤ/p^2)[X_s]` is free over `(ℤ/p^2)[Δ_s]`, unconditionally. -/
theorem test_ordFree_finite_zmod (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra (ZMod (p ^ 2)) (DeltaS p s))
      (ordPartTower d M p s hN hp (ZMod (p ^ 2)) hM hpM hs) :=
  (ordFree_finite_zmod (hN := hN) (hp := hp) 2 (by decide) hM hpM hs h5).1

end LanglandscapeTests.S04.TowerRank
