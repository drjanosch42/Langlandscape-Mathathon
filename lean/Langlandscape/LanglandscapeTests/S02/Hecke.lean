/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Hecke

/-!
# Tests for S02 Hecke — S02-L7b

Tex labels: prop:s02-quot.

Non-vacuity: the commutation statements have the expected shape and are usable as rewriting equations.
-/

open Langlandscape.Tree Langlandscape.Quat Langlandscape.Brandt

section

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-quot`(c) (`s02-quot`): `T_t s_1^* f = s_1^* T_t f` pointwise (usability of `heckeT_comm_s1Pull`). -/
theorem s02_test_s1Pull_pointwise (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1) (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) (f : ZXdual U R) :
    heckeT (d.U0q q (coprime_of_not_dvd hq) U) t R hfin' (s1Pull d q hq U R f) =
      s1Pull d q hq U R (heckeT U t R hfin f) :=
  LinearMap.congr_fun (heckeT_comm_s1Pull R hU t ht hfin hfin') f

/-- `prop:s02-quot`(c) (`s02-quot`): same for `s_0^*` (usability of `heckeT_comm_s0Pull`). -/
theorem s02_test_s0Pull_pointwise (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1) (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) (f : ZXdual U R) :
    heckeT (d.U0q q (coprime_of_not_dvd hq) U) t R hfin' (s0Pull d q hq U R f) =
      s0Pull d q hq U R (heckeT U t R hfin f) :=
  LinearMap.congr_fun (heckeT_comm_s0Pull R hU t ht hfin hfin') f

end
