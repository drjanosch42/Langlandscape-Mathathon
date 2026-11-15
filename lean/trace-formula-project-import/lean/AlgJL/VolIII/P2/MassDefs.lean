import AlgJL.Meta.Tag
import AlgJL.VolIII.P2.ClassSet
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The mass of an order (Q2 U6, item 51; definition only)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §5, first definition (item 51 of `docs/sprints/Q2-plan.md` §1.2).
Split from `Mass.lean` so that `Hyp/EichlerMass.lean` can import the definition of `mass` without the theorems of
§5 (plan §1.3 "MassDefs", TITAN packet P2 §6 item 1).

`mass O = Σᶠ_{c ∈ X(O)} 1/|Γ_{x_c}|` with full stabilizers (conventions row N4) and the representative
`x_c = Quotient.out c`. Junk conventions (snippet 51, plan trap 5): `finsum` is `0` on an infinite class set and
`Nat.card` is `0` on an infinite group (`1/0 = 0` in `ℚ`); neither happens for `a, b < 0` (items 47, 50).
Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF

/-- The mass `Mass(O) = Σ_{c ∈ X(O)} 1/|Γ_{x_c}| ∈ ℚ` of an order `O`, with the full stabilizers `Γ_{x_c} = Γ_{x_c}(Ô^×)`
(row N4) of the representatives `x_c = c.out`. -/
@[tf_id "III.qcls.def:mass"]
noncomputable def mass {a b : ℤ} (O : QOrder a b) : ℚ :=
  ∑ᶠ c : classSet O, (1 : ℚ) / (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : ℚ)

end GL2TF.Quat
