/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalEmbed
import AlgJL.VolIII.P2.Compact

/-!
# Hypothesis `RamNrdSurj`: `Nrd(𝒪_ℓ^×) = ℤ_ℓ^×` at the ramified primes `ℓ ∣ D` (S02-L10)

`mathematics/chapters/s01/1-classsets.tex`, `lem:s01-nrd` (the `ℓ ∣ D` ingredient).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`. Used by `Quat.exists_Ohat_nrd_eq`, `Quat.nrdSurj_*`
(`Quat/LevelNrd.lean`) and `Tree.isQAdmissible_*` (`Tree/Admissible.lean`).

It has no instance: every definite `B` has `D > 1` (an odd number of ramified finite primes, by the product formula;
not proved in Lean), so the hypothesis is needed for every `DefiniteData`.

Status: *formalized*: discharged by `Langlandscape.Hyp.ramNrdSurj_holds` (`Hyp/RamNrdSurjDischarge.lean`), so a
consumer supplies the argument as `ramNrdSurj_holds d`. Cited: Voight, Lemma 13.4.9; Vignéras II.1.5; proved on paper
in `lem:s01-nrd` from the cited local structure of `B_ℓ` (Voight Thm 13.3.11).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open GL2TF Langlandscape.Quat

/-- `s01-nrd`: **hypothesis** `RamNrdSurj d`: at every ramified prime `ℓ ∣ D` the reduced norm maps the units of
the local maximal order onto `ℤ_ℓ^×` (every `w ∈ ℤ_ℓ^×` is `nrd x` for `x ∈ B_ℓ^×` with `x, x⁻¹ ∈ 𝒪_ℓ`). This is
the `ℓ ∣ D` ingredient of `lem:s01-nrd` ("`Nrd(𝒪_ℓ^×) = ℤ_ℓ^×` for `ℓ ∣ D`", seed §2.3); it is not available
from the import and is taken as an explicit hypothesis (cited, Voight Lemma 13.4.9 / Vignéras II.1.5). It is needed
for every definite algebra: `D > 1` always (product formula), so there are always ramified primes. -/
def RamNrdSurj (d : DefiniteData) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ d.D → ∀ w : ℤ_[ℓ]ˣ, ∃ x : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ,
    localEmbed d.a d.b ℓ x ∈ d.Ohat ∧ GL2TF.Quat.nrd (x : QuatAlg ℚ_[ℓ] d.a d.b) = ((w : ℤ_[ℓ]) : ℚ_[ℓ])

end Langlandscape.Hyp
