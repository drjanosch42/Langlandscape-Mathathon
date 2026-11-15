/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.EKillsGraph

/-! Shape and non-vacuity tests for `Langlandscape.Ordinary.EKillsGraph` (S04-L11). -/

set_option autoImplicit false

namespace LanglandscapeTests.S04.EKillsGraph

open Langlandscape.Ordinary

/-- `lem:s04-ekills`(b) (`s04-ekills`), test: `p` acting on the vertex module `ι →₀ ℤ_[p]` has `ordPart = ⊥`. -/
theorem test_vertex_bot (p : ℕ) [Fact p.Prime] (ι : Type) :
    ordPart (LinearMap.lsmul ℤ_[p] (ι →₀ ℤ_[p]) (p : ℤ_[p])) = ⊥ :=
  ordPart_lsmul_eq_bot _ (iInf_pow_smul_top_padic p)

/-- `lem:s04-ekills`(c) (`s04-ekills`), test: `p` on a `ℤ_[p]`-module killed by `p ^ 2` has `ordPart = ⊥`. -/
theorem test_nilpotent_bot (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[p] N]
    (h : ∀ x : N, ((p : ℤ_[p]) ^ 2) • x = 0) :
    ordPart (LinearMap.lsmul ℤ_[p] N (p : ℤ_[p])) = ⊥ :=
  ordPart_lsmul_eq_bot_of_nilpotent _ h

/-- `lem:s04-ekills`(c) (`s04-ekills`), non-vacuity of the mass arithmetic: `p = 5`, `s = 2`, `D = 1`, `c = 25`,
`m = 600 = 5^2 · 24`. -/
theorem test_pow_dvd_card : 5 ^ (2 * 2 - 2) ∣ (25 : ℕ) :=
  pow_dvd_card_of_mass (p := 5) (D := 1) (s := 2) (k := 24) (m := 600) Nat.prime_five le_rfl
    (by norm_num [Nat.totient_one]) (by norm_num)

end LanglandscapeTests.S04.EKillsGraph
