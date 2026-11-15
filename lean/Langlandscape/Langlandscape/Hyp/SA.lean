/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Admissible

/-!
# Hypothesis `SA`: strong approximation for `B^1` at `S = {∞, q}` (S02-L4a)

`mathematics/chapters/s02/2-quotient.tex`, `thm:s02-SA` (consequence (SA_U)), `if:s02-SA`.
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Faithfulness: `Tree.IsQAdmissible` uses "`U ≤ Ô^×` of finite index" in place of "compact open" (A18). (SA_U) only
involves `U^1 = U ∩ B̂^1`, with `[Ô^1 : U^1] ≤ [Ô^× : U] < ∞`. `Ô^1 ≅ SL₂(Ẑ^{(D)}) × ∏_{ℓ ∣ D} 𝒪_ℓ^1` is topologically
finitely generated (`SL₂(ℤ) ↠ SL₂(ℤ/N)`; finitely many compact `ℓ`-adic analytic factors), so by Nikolov–Segal
(Ann. of Math. 165 (2007), Thm. 1.1) `U^1` is open in `Ô^1`. Then `U^{1,(q)} = U^1 ∩ Ô^{1,(q)}` is open in the closed
subgroup `Ô^{1,(q)} = {u ∈ Ô^1 : u_q = 1}`, which is open in `B̂^{1,(q)}`; this openness of `U^{1,(q)}` in `B̂^{1,(q)}`
is what the proof of (SA_U) uses. So the statement below is still a consequence of the cited theorem, now also
resting on Nikolov–Segal (which uses the classification of finite simple groups); for the project's levels `Ô^×`,
`U_0(N)`, `U_1(N)`, `U_s` (open) it is not needed. See the docstring of `Langlandscape/Tree/Admissible.lean`.

Status: *cited* (Voight, Main Thm. 28.5.3 with Cor. 28.5.12; Vignéras III.4.3); not formalized.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `thm:s02-SA`, `if:s02-SA`: strong approximation for `B^1` at `S = {∞, q}` in the shape (SA_U):
for every `q`-admissible level `U`, `B̂^1 = B^1 (B^1_q × U^{1,(q)})` (`Tree.SAat`).
Source: Voight, *Quaternion algebras*, Main Thm. 28.5.3 (with `R = ℤ[1/q]`) and Cor. 28.5.12; Vignéras, Ch. III,
Thm. 4.3. Cited; discharge plan L02.SA (post-hackathon). -/
def SA (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) : Prop :=
  ∀ U : Subgroup (BHat d.a d.b)ˣ, Tree.IsQAdmissible d q hq U → Tree.SAat d q hq U

end Langlandscape.Hyp
