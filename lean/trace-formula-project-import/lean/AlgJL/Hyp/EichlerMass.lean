import AlgJL.Meta.Tag
import AlgJL.VolIII.P2.Ramification
import AlgJL.VolIII.P2.MassDefs

/-!
# The hypothesis H-EM `EichlerMass` (Q2, unit U6, item 55)

`III.qcls.hyp:eichler-mass` (D4, user approval 2026-11-11 at Q2 G0; registry entry in `tex/shared/hypotheses.tex`;
`docs/sprints/Q2-plan.md` §4). Eichler's mass formula for a maximal order `O` of `B = (a, b)_ℚ` with full unit groups
(conventions row N4): if `RamifiedExactly a b D`, then `Mass(O) = (1/24) ∏_{p ∣ D} (p − 1)`. The ramification datum is
an antecedent inside the body, so the family is true at every index (vacuous unless `a, b < 0` and `D` is the
squarefree product of the ramified primes).

Vocabulary (`registry/hyp_imports.yaml`): `GL2TF.VolIII.P2.MassDefs` (`mass`, item 51, through `ClassSet`, `Adelic`,
`Orders`) and `GL2TF.VolIII.P2.Ramification` (`RamifiedExactly`, item 14). This file never imports
`GL2TF.VolIII.P2.Mass` (packet P2 §6 item 1). Proved closed instances: `GL2TFTests.eichlerMass_d11` (exit
`III.qcls.ex:eichler-mass-instance-d11`) and `GL2TFTests.eichlerMass_d2` (`III.qcls.ex:hurwitz-order-mass`).
Discharge: Q8 (Ch III.13) or later. Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

namespace GL2TF.Hyp

/-- **H-EM** (Eichler's mass formula), for `a b : ℤ`, `D : ℕ` and a maximal order `O` of `B = (a, b)_ℚ`: if
`RamifiedExactly a b D`, then `Mass(O) = (1/24) ∏_{p ∣ D} (p − 1)`, with `Mass` of `III.qcls.def:mass` (full unit
groups, row N4). [Shz] (20)–(21), p. 180 (`e_μ = |O_μ^×|/2` there, hence `1/12`); [Piz] P0.5 (`e_j = |O_j^×|`, `1/24`).
Registry entry: `tex/shared/hypotheses.tex`; discharge Q8 (Ch III.13) or later. -/
@[tf_id "III.qcls.hyp:eichler-mass"]
def EichlerMass (a b : ℤ) (D : ℕ) (O : GL2TF.Quat.MaxOrder a b) : Prop :=
  GL2TF.Quat.RamifiedExactly a b D →
    GL2TF.Quat.mass O.1 = (1 / 24 : ℚ) * ∏ p ∈ D.primeFactors, ((p : ℚ) - 1)

end GL2TF.Hyp
