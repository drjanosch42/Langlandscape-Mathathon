/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.Limit

/-!
# Hypothesis `InvLimExact`: surjective A-transitions of the ordinary Ribet system (S04-L14b, design D-lim)

`mathematics/chapters/s04`, `thm:s04-lambdaribet`(a). A hypothesis is a `Prop`-valued definition, taken as an explicit
argument (never an axiom, never an instance; OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Status: **true and provable under connectivity** (tex, D-lim route); conditional fallback of S04-L13b (`lim_exact_ribet` takes it as its argument `hA`).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): if `BG(UU_s, q)` is connected for all `s ≥ 1` (the standing
hypothesis of `thm:s04-lambdaribet`, same shape as `hconn` of `Ordinary.lim_exact_ribet`), the transitions of the
A-system of the ordinary Ribet sequence, `e H₁(Γ_{UU_{s+1}}) → e H₁(Γ_{UU_s})` (`RibetHyp.transA`), are all
surjective. Proved in the tex by the D-lim route (control at both levels, `Δ`-linearity of `α`, snake lemma), under
connectivity; the compactness proof of `thm:s04-lambdaribet`(a) gives `lim_exact_ribet` directly but not this
statement. The D-lim snake route on the concrete Ribet systems is **not formalized** (only the abstract snake step
`Ordinary.surjective_of_snake`; its inputs, the control kernel `ker = I·B` and the `Δ`-equivariance of `α`, are
missing). Undischarged. Used by `Ordinary.lim_exact_ribet` (as `hA := h hconn`). Owner S04-L14b. -/
def InvLimExact {d : DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (H : Ordinary.RibetHyp d q M p) : Prop :=
  (∀ s ≥ 1, Langlandscape.Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s))
      (Langlandscape.Tree.isQLevel_Utower (H.hqN s))) →
    ∀ n, Function.Surjective (H.transA n)

end Langlandscape.Hyp
