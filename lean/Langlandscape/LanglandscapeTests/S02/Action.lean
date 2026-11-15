/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Action

/-! Non-vacuity tests for `Langlandscape.Tree.Action` (S02-L4a, spec line `L4a-act`). -/

set_option autoImplicit false

namespace LanglandscapeTests.S02.Action

open Langlandscape.Quat Langlandscape.Tree

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)

/-- `def:s02-GU` (`s02-GU`), test: `1 ∈ Γ_U` fixes the base vertex `v_0`. -/
theorem test_one_smul_v0 : (1 : GammaU d q hq U) • v0 q = v0 q :=
  one_smul _ _

/-- `def:s02-GU` (`s02-GU`), test: `ι_q(1) = 1`. -/
theorem test_gammaQGL_one : gammaQGL d q hq U 1 = 1 :=
  map_one _

/-- `def:s02-GU`, `lem:s02-tree`(b) (`s02-GU`), test: `Γ_U` preserves the type of `v_0`. -/
theorem test_vtype_smul_v0 (γ : GammaU d q hq U) : vtype q (γ • v0 q) = vtype q (v0 q) :=
  gammaU_smul_vtype γ (v0 q)

end LanglandscapeTests.S02.Action
