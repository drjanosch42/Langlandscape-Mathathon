/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Data.ZMod.Basic

/-!
# Hypothesis `HsiehCR`: Hsieh's residual condition (CR, supp D) (S04-L14a)

`mathematics/chapters/s04/hsieh.tex`, `hyp:s04-CR`. A hypothesis is a `Prop`-valued definition, taken as an explicit
argument (never an axiom, never an instance; OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Status: *cited* (Hsieh §1.4, Hypothesis (CR,Σ), p. 4); a **condition** on a residual representation, not to be discharged.
Schematic (F6): the residual representation is abstract data (`absIrred`, `ram`, `chiPlus`, `chiMinus`).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- `hyp:s04-CR` (`s04-CR`), on abstract residual data: `G` indexes the decomposition group at `p`, `chiPlus`, `chiMinus` are the characters
of `ρ̄|_{G_{ℚ_p}}^ss = χ⁺ ⊕ χ⁻` (valued in `ZMod p`), `ram ℓ` says that `ρ̄` is ramified at `ℓ`.
(CR_D): (i) `ρ̄` absolutely irreducible (abstract proposition `absIrred`);
(ii) `p`-distinguished: `chiPlus ≠ chiMinus`; (iii) `ram ℓ` for every prime `ℓ ∣ D` with `ℓ ≡ 1 (mod p)`.
Abstracted: the actual `G_ℚ`-representation attached to a maximal ideal (`if:s01-targets`); the predicates `absIrred`,
`ram` are data. Source: Hsieh §1.4 (cited). Not discharged: a condition. Owner: S04-L14a. -/
def HsiehCR (p D : ℕ) (G : Type) (absIrred : Prop) (chiPlus chiMinus : G → ZMod p)
    (ram : ℕ → Prop) : Prop :=
  absIrred ∧ chiPlus ≠ chiMinus ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ D → ℓ % p = 1 % p → ram ℓ

end Langlandscape.Hyp
