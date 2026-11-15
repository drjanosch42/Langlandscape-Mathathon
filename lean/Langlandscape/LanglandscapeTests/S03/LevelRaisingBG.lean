/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ribet.LevelRaisingBG

/-!
# Tests for S03 LevelRaisingBG — S03-L10b

Tex label: `prop:s03-LRdef`. Usability of the discharged hypotheses and the bridge at level `Ô^×`.
-/

set_option autoImplicit false

namespace LanglandscapeTests.S03.LevelRaisingBG

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree Langlandscape.Ribet
open scoped Classical

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)

/-- `prop:s03-LRdef` (`s03-LRdef`), test: the fibre sums `q + 1` at level `Ô^×`. -/
theorem test_hf0_Ohat [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat))] (x : XB d.Ohat) :
    ∑ e ∈ Finset.univ.filter (fun e => s0 d q hq d.Ohat e = x), lrWeight0 d q hq d.Ohat e = (q : ℤ) + 1 :=
  levelRaising_hf0 isQLevel_Ohat x

/-- `prop:s03-LRdef` (`s03-LRdef`), test: the bridge `T = T_q` at level `Ô^×`. -/
theorem test_levelT_Ohat [Fintype (XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat))] [Finite (XB d.Ohat)] :
    Langlandscape.Graph.levelT (s0 d q hq d.Ohat) (s1 d q hq d.Ohat) (lrWeight0 d q hq d.Ohat) =
      heckeTHom d.Ohat (elemT d q hq) ℤ (relIndex_elemT_ne_zero_of_isQLevel isQLevel_Ohat) :=
  levelT_eq_heckeTHom isQLevel_Ohat

/-- `prop:s03-LRdef` (`s03-LRdef`), test: `a_1 e · w_e = w_{s_1 e}` at level `Ô^×`. -/
theorem test_lrWeight1_mul_wx (e : XB (d.U0q q (coprime_of_not_dvd hq) d.Ohat)) :
    lrWeight1 d q hq d.Ohat e * (wx (d.U0q q (coprime_of_not_dvd hq) d.Ohat) (Quotient.out e) : ℤ) =
      (wx d.Ohat (Quotient.out (s1 d q hq d.Ohat e)) : ℤ) :=
  lrWeight1_mul_wx isQLevel_Ohat e

end LanglandscapeTests.S03.LevelRaisingBG
