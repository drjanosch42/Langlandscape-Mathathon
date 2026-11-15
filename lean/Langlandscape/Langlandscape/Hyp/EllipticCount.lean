/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic

/-!
# Hypothesis `EllipticCount`: elliptic classes of the maximal order (S03-L6)

`mathematics/chapters/s03/1-graphs.tex`, `lem:s03-elliptic` (and the `q ∈ {2,3}` part of `prop:s03-mazur`).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

For definite quaternion data `d` with `D = d.D = q` prime and level `U = Ô^×`:

* if `q ≥ 5`: every class has `w_x ∈ {1,2,3}`, exactly `n₂ = [q ≡ 3 mod 4]` classes have `w_x = 2` and exactly
  `n₃ = [q ≡ 2 mod 3]` classes have `w_x = 3` (`n₂ = (1 - (-4/q))/2`, `n₃ = (1 - (-3/q))/2`, restated through the
  residues of `q`, as in the tex: "`n₂ = 1` iff `q ≡ 3 mod 4`, `n₃ = 1` iff `q ≡ 2 mod 3`");
* if `q ∈ {2, 3}`: `|X_B(Ô^×)| = 1`.

The weights are those of `Langlandscape.Quat.wx` on the representatives `Quotient.out c`, as in `massW`.
Faithfulness: the statement is a consequence of the Eichler class number formula (Voight Thm 30.1.5) together with
the classification of unit groups of maximal orders (Voight Thm 11.5.14), and is true for every `d` with `d.D = q`
prime (it is vacuous only for `d.D` not prime; no definite algebra has `D = 1`). It is therefore non-vacuous.
No closed instance is available (the class number formula is absent from the import and Mathlib).

Status: *cited* (Voight, Thm 11.5.14, Thm 25.1.1, Thm 30.1.5; Mazur, Eisenstein ideal, App. Thm 1.1(d)); not formalized.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `lem:s03-elliptic` (`s03-elliptic`): for `d.D = q` prime, `q ≥ 5` gives `w_x ∈ {1,2,3}` with `n₂ = [q ≡ 3 (4)]`
classes of weight `2` and `n₃ = [q ≡ 2 (3)]` classes of weight `3`; and `q ∈ {2,3}` gives `|X_B(Ô^×)| = 1`.
Source: Voight, *Quaternion algebras*, Thm 11.5.14, Thm 25.1.1, Thm 30.1.5. Cited; discharge plan post-hackathon. -/
def EllipticCount (d : DefiniteData) : Prop :=
  d.D.Prime →
    (5 ≤ d.D →
      (∀ c : XB d.Ohat, wx d.Ohat (Quotient.out c) = 1 ∨ wx d.Ohat (Quotient.out c) = 2 ∨
        wx d.Ohat (Quotient.out c) = 3) ∧
      Nat.card {c : XB d.Ohat // wx d.Ohat (Quotient.out c) = 2} = (if d.D % 4 = 3 then 1 else 0) ∧
      Nat.card {c : XB d.Ohat // wx d.Ohat (Quotient.out c) = 3} = (if d.D % 3 = 2 then 1 else 0)) ∧
    (d.D ≤ 3 → Nat.card (XB d.Ohat) = 1)

end Langlandscape.Hyp
