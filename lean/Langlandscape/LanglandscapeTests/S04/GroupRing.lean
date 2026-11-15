/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.GroupRing

/-!
# Tests for `Langlandscape.Ordinary.GroupRing` (S04-L7, `prop:s04-freeA`)

Instances of the row: `G` cyclic of order `p ^ n` (`Multiplicative (ZMod (p ^ n))`), over `ℤ_p` and
over `ZMod (p ^ m)`; the edge cases `n = 0` (trivial group `Unit`) and `m = 0` (`ZMod 1` is not
local);
freeness of finite projective modules and of direct summands.
-/

@[expose] public section

namespace Langlandscape.Ordinary.Tests

open Langlandscape.Ordinary

/-- `prop:s04-freeA` (s04-freeA), cyclic case over `ℤ_p`: `ℤ_p[ℤ ⧸ p ^ n]` is local. -/
theorem isLocalRing_padicInt_cyclic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsLocalRing (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n)))) :=
  isLocalRing_monoidAlgebra_padicInt p (n := n) (by simp)

/-- `prop:s04-freeA` (s04-freeA), cyclic case over `ZMod (p ^ m)`, `0 < m`. -/
theorem isLocalRing_zmod_cyclic (p : ℕ) [Fact p.Prime] (m n : ℕ) (hm : 0 < m) :
    IsLocalRing (MonoidAlgebra (ZMod (p ^ m)) (Multiplicative (ZMod (p ^ n)))) :=
  isLocalRing_monoidAlgebra_zmod p hm (n := n) (by simp)

/-- `prop:s04-freeA` (s04-freeA), test instance: `5` is prime. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `prop:s04-freeA` (s04-freeA), concrete instance: `ℤ_5[ℤ ⧸ 5 ^ 2]` is local. -/
theorem isLocalRing_padicInt_five :
    IsLocalRing (MonoidAlgebra ℤ_[5] (Multiplicative (ZMod (5 ^ 2)))) :=
  isLocalRing_monoidAlgebra_padicInt 5 (n := 2) (by simp)

/-- `prop:s04-freeA` (s04-freeA), edge case `n = 0`: the trivial group, `ℤ_p[1]` is local. -/
theorem isLocalRing_padicInt_trivial (p : ℕ) [Fact p.Prime] :
    IsLocalRing (MonoidAlgebra ℤ_[p] Unit) :=
  isLocalRing_monoidAlgebra_padicInt p (n := 0) (by simp)

/-- `prop:s04-freeA` (s04-freeA), edge case `n = 0` over `ZMod (p ^ m)`. -/
theorem isLocalRing_zmod_trivial (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 0 < m) :
    IsLocalRing (MonoidAlgebra (ZMod (p ^ m)) Unit) :=
  isLocalRing_monoidAlgebra_zmod p hm (n := 0) (by simp)

/-- `prop:s04-freeA` (s04-freeA), edge case `m = 0`: `ZMod (p ^ 0) = ZMod 1` is the zero ring, which
is not local; so the hypothesis `0 < m` of `isLocalRing_monoidAlgebra_zmod` cannot be dropped. -/
theorem not_isLocalRing_zmod_pow_zero (p : ℕ) : ¬ IsLocalRing (ZMod (p ^ 0)) := by
  intro h
  have : Nontrivial (ZMod (p ^ 0)) := h.toNontrivial
  rw [pow_zero] at this
  exact not_nontrivial (ZMod 1) this

/-- `prop:s04-freeA` (s04-freeA), edge case `m = 0` at group-ring level: `(ZMod 1)[G]` is not
local. -/
theorem not_isLocalRing_monoidAlgebra_zmod_pow_zero (p : ℕ) (G : Type*) [CommGroup G] :
    ¬ IsLocalRing (MonoidAlgebra (ZMod (p ^ 0)) G) := by
  intro h
  have : Nontrivial (MonoidAlgebra (ZMod (p ^ 0)) G) := h.toNontrivial
  obtain ⟨x, y, hxy⟩ := this
  apply hxy
  ext g
  have hs : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
  exact Subsingleton.elim _ _

/-- `prop:s04-freeA` (s04-freeA): a finite projective `ℤ_p[ℤ ⧸ p ^ n]`-module is free. -/
theorem free_projective_padicInt_cyclic (p : ℕ) [Fact p.Prime] (n : ℕ)
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n)))) P]
    [Module.Finite (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n)))) P]
    [Module.Projective (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n)))) P] :
    Module.Free (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n)))) P :=
  free_of_projective_padicInt p (n := n) (by simp)

/-- `prop:s04-freeA` (s04-freeA): a direct summand of `A ^ r`, `A = (ZMod (p ^ m))[ℤ ⧸ p ^ n]`,
is free (`0 < m`). -/
theorem free_isCompl_zmod_cyclic (p : ℕ) [Fact p.Prime] (m n r : ℕ) (hm : 0 < m)
    {P Q : Submodule (MonoidAlgebra (ZMod (p ^ m)) (Multiplicative (ZMod (p ^ n))))
      (Fin r → MonoidAlgebra (ZMod (p ^ m)) (Multiplicative (ZMod (p ^ n))))}
    (h : IsCompl P Q) :
    Module.Free (MonoidAlgebra (ZMod (p ^ m)) (Multiplicative (ZMod (p ^ n)))) P :=
  free_of_isCompl_zmod p hm (n := n) (by simp) h

/-- `prop:s04-freeA` (s04-freeA), rank `0`: the zero submodule is a direct summand of `A ^ 0` and
is free. -/
theorem free_isCompl_rank_zero (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.Free (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n))))
      (⊥ : Submodule (MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n))))
        (Fin 0 → MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n))))) :=
  free_of_isCompl_padicInt p (n := n) (by simp) isCompl_bot_top

end Langlandscape.Ordinary.Tests
