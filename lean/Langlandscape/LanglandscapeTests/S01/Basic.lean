/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic

/-! Non-vacuity checks for S01-L1. -/

open Langlandscape.Quat

example (d : DefiniteData) : d.a < 0 := d.ha
example (d : DefiniteData) : d.b < 0 := d.hb
example (d : DefiniteData) : Finite (XB d.Ohat) :=
  XB_finite d le_rfl d.Ohat_isOpen
example (a b : ℤ) : (1 : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ (pmOne : Subgroup _) := Subgroup.one_mem _
example (a b : ℤ) : (-1 : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) ∈ (pmOne : Subgroup _) := Subgroup.mem_zpowers _
