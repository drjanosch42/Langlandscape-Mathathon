/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.TwoTerm
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

/-!
# Hypothesis `SerreCoh`: `H_*(Γ_U, R)` via the Brandt graph (S02-L3)

`mathematics/chapters/s02/3-cohomology.tex`, `prop:s02-coh`(b), `if:s02-coh`.
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance).
Registered in `HYPOTHESES.md` (used by: — (statement only)).

Statement: for a `q`-level `U` with `BG(U, q)` connected and `R` a commutative ring in which every stabiliser order
`|Γ_x|` is a unit, `H_1(Γ_U, R) ≅ ker ∂` and `H_0(Γ_U, R) ≅ coker ∂` (`R`-linearly), with `∂ = partialHom` of
`Tree/TwoTerm.lean`. The `R`-module structure is that of `groupHomology (Rep.trivial R Γ_U R) n : ModuleCat R`.

Deviation (Risk 3 / universes): Mathlib's `groupHomology` needs `R` and `Γ_U` in the same universe, and `Γ_U : Type`,
so `R : Type` here (not `Type*`).

Status: *cited* (Serre, *Trees*, Ch. II §2.8, Prop. 13 and Remark 1; Brown, *Cohomology of Groups*, VII.7); not formalized.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat Langlandscape.Brandt

/-- `prop:s02-coh`(b), `if:s02-coh`: Serre's computation of the homology of `Γ_U` with trivial coefficients `R` from
the quotient graph `BG(U, q)` (connected by `hconn`): if all `|Γ_x|` are units in `R`, then
`H_1(Γ_U, R) ≃ ker ∂` and `H_0(Γ_U, R) ≃ coker ∂`. The hypothesis `hconn` is carried as an argument (as in the
tex statement) although it does not occur in the body. The statement is more general than the tex in `R`, and
the isomorphisms are abstract (no compatibility with `∂` or the augmentation is asserted). Cited; not formalized. -/
def SerreCoh (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : Tree.IsQLevel d q hq U) (hconn : Tree.BGConnected d q hq U hU) (R : Type) [CommRing R] : Prop :=
  (∀ x : (BHat d.a d.b)ˣ, IsUnit ((Nat.card (Gam U x) : ℕ) : R)) →
    Nonempty (groupHomology (Rep.trivial R (Tree.GammaU d q hq U) R) 1 ≃ₗ[R]
        LinearMap.ker (Tree.partialHom d q hq U R)) ∧
    Nonempty (groupHomology (Rep.trivial R (Tree.GammaU d q hq U) R) 0 ≃ₗ[R]
        ((ZX U R × ZX U R) ⧸ LinearMap.range (Tree.partialHom d q hq U R)))

end Langlandscape.Hyp
