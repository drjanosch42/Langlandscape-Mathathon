/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import AlgJL.VolIII.Brandt.Pairing
import AlgJL.Hyp.EichlerMass
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Smoke test of the frozen setup (S01-X1a)

Regression test of the Lake setup of `lean/Langlandscape/` (plan/implementation/OVERVIEW.md §3.5): this module imports
the built import (package `GL2TF`, modules `AlgJL.*`, read in place through `.lake/GL2TF`) and Mathlib, and must build
as the only module of `tools/lbuild.sh +Langlandscape.Smoke`, with every `AlgJL.*` module up to date (never rebuilt).
It contains no mathematics of its own.
-/

namespace Langlandscape.Smoke

/-- Smoke theorem: the reused hypothesis `GL2TF.Hyp.EichlerMass` unfolds to Eichler's mass formula for `GL2TF.Quat.mass`.
Mentions both import names so that a missing or stale import olean fails here. -/
theorem eichlerMass_apply (a b : ℤ) (D : ℕ) (O : GL2TF.Quat.MaxOrder a b)
    (h : GL2TF.Hyp.EichlerMass a b D O) (hD : GL2TF.Quat.RamifiedExactly a b D) :
    GL2TF.Quat.mass O.1 = (1 / 24 : ℚ) * ∏ p ∈ D.primeFactors, ((p : ℚ) - 1) :=
  h hD

end Langlandscape.Smoke
