/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.TowerUncond
import Langlandscape.Hyp.InvLimExact

/-!
# Tests for `Ordinary/TowerUncond.lean` (S04-L3, S04-L17b, S04-L17c)

The unconditional (`hdec`-free) forms are applied: the stage-05 export `ekillsA_tower_uncond` (every ordinary vector
of `ℤ_[p][X_s]` has degree `0`), the surjectivity of the `M_ord` transitions and projections, and the limit Ribet
sequence with only `hconn` and `hA` left.
-/

set_option autoImplicit false

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Ordinary

namespace LanglandscapeTests.S04.TowerUncond

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s04-ekills`(a) (`s04-ekills`), test: by `ekillsA_tower_uncond`, with no hypothesis, every ordinary vector of
`ℤ_[p][X_s]` has degree `0`. -/
theorem test_ekillsA_tower_uncond (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {x : ZX (d.Utower M p s hN) ℤ_[p]}
    (hx : x ∈ ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p])) :
    x ∈ LinearMap.ker (deg (Xs d M p s hN) ℤ_[p]) := by
  rw [← ekillsA_tower_uncond (d := d) (hN := hN) (hp := hp) hM hpM hs] at hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hx
  exact y.2

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`), test: every element of `e ℤ_p[X_{n+1}]` lifts along
`π_*` to `e ℤ_p[X_{n+2}]`, unconditionally. -/
theorem test_mordTrans_surjective_uncond (T : TowerHyp d M p) (n : ℕ) (y : T.MordLevel n) :
    ∃ x : T.MordLevel (n + 1), T.mordTrans n x = y :=
  TowerHyp.mordTrans_surjective_uncond T n y

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`), test: every element of `e ℤ_p[X_{n+1}]` is the level-`n`
component of a compatible family in `M_ord(U)`, unconditionally. -/
theorem test_mord_proj_surjective_uncond (T : TowerHyp d M p) (n : ℕ) (y : T.MordLevel n) :
    ∃ x : ↥(Mord T), Compat.proj (M := T.MordLevel) T.mordTrans n x = y :=
  Mord.proj_surjective_uncond T n y

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), test: with `hdec` discharged, the limit map `α` is surjective
given only connectivity and the `A`-surjectivity (`Hyp.InvLimExact` applied to `hconn`). -/
theorem test_alphaLim_surjective_uncond {q : ℕ} [Fact q.Prime] (H : RibetHyp d q M p)
    (hconn : ∀ s ≥ 1, Langlandscape.Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s))
      (Langlandscape.Tree.isQLevel_Utower (H.hqN s)))
    (hI : Langlandscape.Hyp.InvLimExact H) :
    Function.Surjective (alphaLim H) :=
  (lim_exact_ribet_uncond H hconn (hI hconn)).2.2

end LanglandscapeTests.S04.TowerUncond
