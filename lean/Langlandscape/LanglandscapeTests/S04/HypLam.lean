/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.MordLambdaFree
import Langlandscape.Hyp.InvLimExact

/-!
# Tests for `Hyp.MordLambdaFree`, `Hyp.InvLimExact` (S04-L14b)

The statements elaborate, and their components are consumed: `InvLimExact`, applied to the connectivity
`hconn`, is exactly the `hA` of `lim_exact_ribet`; the surjectivity clause of `MordLambdaFree` agrees with the proved `Mord.proj_surjective`.
No instance of either hypothesis is asserted (none is available; see `HYPOTHESES.md`).
-/

namespace Langlandscape.Ordinary.Tests

open Langlandscape.Ordinary

variable {d : Langlandscape.Quat.DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `Hyp.InvLimExact` feeds `lim_exact_ribet`. -/
theorem invLimExact_feeds_limExact (H : RibetHyp d q M p) (hdec : Langlandscape.Hyp.PadicOrdDecomp p)
    (hconn : ∀ s ≥ 1, Langlandscape.Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s))
      (Langlandscape.Tree.isQLevel_Utower (H.hqN s)))
    (hI : Langlandscape.Hyp.InvLimExact H) :
    Function.Surjective (alphaLim H) :=
  (lim_exact_ribet H hdec hconn (hI hconn)).2.2

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): under connectivity, `Hyp.InvLimExact` unfolds to surjectivity
of `transA n`. -/
theorem invLimExact_unfold (H : RibetHyp d q M p)
    (hconn : ∀ s ≥ 1, Langlandscape.Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s))
      (Langlandscape.Tree.isQLevel_Utower (H.hqN s)))
    (hI : Langlandscape.Hyp.InvLimExact H) (n : ℕ) :
    Function.Surjective (H.transA n) :=
  hI hconn n

/-- `thm:s04-control`(a) (`s04-control`): the control-surjectivity clause of `Hyp.MordLambdaFree` is the proved
`Mord.proj_surjective` (under `Hyp.PadicOrdDecomp`), so only freeness and the kernel clause are hypothetical. -/
theorem mordLambdaFree_proj_clause (T : TowerHyp d M p) (hdec : Langlandscape.Hyp.PadicOrdDecomp p)
    {G : ℕ → Type} [∀ n, CommGroup (G n)] (π : ∀ n, G (n + 1) →* G n)
    (ρ : ∀ n, G n →* Module.End ℤ_[p] (T.MordLevel n))
    (hρ : ∀ n (x : G (n + 1)), (T.mordTrans n).comp (ρ (n + 1) x) = (ρ n (π n x)).comp (T.mordTrans n))
    (_h : Langlandscape.Hyp.MordLambdaFree T π ρ hρ) (n : ℕ) :
    Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans n) :=
  Mord.proj_surjective T hdec n

/-- `thm:s04-control`(a) (`s04-control`): the finite-rank freeness clause can be read off a proof of
`Hyp.MordLambdaFree` (the `Lam`-module structure is `Mord.lamModule`). -/
theorem mordLambdaFree_rank (T : TowerHyp d M p)
    {G : ℕ → Type} [∀ n, CommGroup (G n)] (π : ∀ n, G (n + 1) →* G n)
    (ρ : ∀ n, G n →* Module.End ℤ_[p] (T.MordLevel n))
    (hρ : ∀ n (x : G (n + 1)), (T.mordTrans n).comp (ρ (n + 1) x) = (ρ n (π n x)).comp (T.mordTrans n))
    (h : Langlandscape.Hyp.MordLambdaFree T π ρ hρ) (n : ℕ) :
    Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans n) :=
  (h.2 n).1

end Langlandscape.Ordinary.Tests
