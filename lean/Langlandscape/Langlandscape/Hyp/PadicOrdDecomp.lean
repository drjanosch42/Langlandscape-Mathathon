/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.Projector
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Hypothesis `PadicOrdDecomp`: ordinary decomposition of f.g. `ℤ_[p]`-modules (S04-L1, design D-e)

`mathematics/chapters/s04/ordinary.tex`, `def:s04-e` (f.g. `ℤ_p` form, Steps 3 and 5).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Status: **true**, *proved* in the tex (`def:s04-e`, Step 5) and *formalized*: discharged by
`Ordinary.padicOrdDecomp_holds` (S04-L3, `Ordinary/PadicDecomp.lean`). Every `ℤ_[p]` tower theorem takes
`(hdec : Hyp.PadicOrdDecomp p)` explicitly (fallback F-e of the stage plan); supply `Ordinary.padicOrdDecomp_holds p`.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- `def:s04-e` (`s04-e`), f.g. `ℤ_p` form: every endomorphism `T` of a finitely generated `ℤ_[p]`-module `M` has an
ordinary decomposition `M = ordPart T ⊕ nilPart p T` (`Ordinary.HasOrdDecomp` with `p := (p : ℤ_[p])`). True; discharged by
`Ordinary.padicOrdDecomp_holds` (S04-L3). -/
def PadicOrdDecomp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] (T : Module.End ℤ_[p] M),
    Ordinary.HasOrdDecomp (p : ℤ_[p]) T

end Langlandscape.Hyp
