/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.MassTower

/-! Non-vacuity checks for S01-L4c: `D = 2`, `M = 1`, `p = 5`, `s = 1` gives `|S_1| = 1`
(under the Eichler mass hypothesis, as an explicit argument).

Caveat (audit R5): this is *not* a closed instance. It quantifies over an abstract `d : DefiniteData` with
`d.D = 2` and takes `EichlerMass` as a hypothesis; it only checks the arithmetic (`= 1`). The import has proved
`EichlerMass` instances in its own test library, but they are not importable here. -/

open Langlandscape.Quat

example (d : DefiniteData) (hD : d.D = 2) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hpD : (5 : ℕ).Coprime d.D) (hN : (1 * 5 ^ 1 : ℕ).Coprime d.D) :
    (Nat.card (XB (d.Utower 1 5 1 hN)) : ℚ) = 1 := by
  have h := card_XB_Utower d hM Nat.prime_five le_rfl le_rfl one_ne_zero hpD hN
  rw [h, hD]
  have h5 : Nat.totient 5 = 4 := Nat.totient_prime Nat.prime_five
  have h2 : Nat.totient 2 = 1 := Nat.totient_prime Nat.prime_two
  have h5' : (Nat.primeFactors 5) = {5} := Nat.Prime.primeFactors Nat.prime_five
  norm_num [GL2TF.Explicit.dedekindPsi, h5, h2, h5']
