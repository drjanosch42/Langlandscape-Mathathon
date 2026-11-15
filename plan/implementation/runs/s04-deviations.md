<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Stage 04 deviations (running list; folded into runs/s04.md at closure)

1. **Production L6 rescue writer outside the E1′ experiment** (global master 2026-11-14 ~22:03Z): L9, L10, L12 were blocked on L6 while
   both strands were red after round 1 (10 / 2 errors). A fresh Opus writer (impl/s04-l6, worktree s04-l6) starts from the stage-04 row and
   brief only (no strand code read), so the experiment stays uncontaminated; whichever green L6 arrives first (strand or rescue) unblocks
   L9/L10/L12. The strands continue under the protocol; at most one strand is merged.
2. **Agent cap exceeded once** (10 for ~2 min, L2/L4 fix rounds; corrected; fixes queued since).
3. **New WPs at execution:** S04-E1M/E1L (cross-account errata lane), S04-L10b (rank/freeness split from L10), S04-MOD (module conversion).
4. **Lean licence/header changes mid-stage:** GPL → Apache-2.0 (main 992d755), then the Mathlib-style header (main a218d64), applied to all
   Lean files in e1cb226 (one commit) and to new WP files at each integration commit.
5. **E1′ merged ≠ winner**: the L6 strand D head (a289461, opus strand, green) is merged as production L6 before the E1′ decision (both strands failed audit r0 on the minor count only); the decision follows the ladder (precedent S02-E1).
6. **L12 parallel rescue writer** (impl/s04-l12r, Opus) started at L12 round 2 (16 errors; critical path), per the S03 lesson; first green wins.
7. **`transA_surjective_of_snake` dropped (S04-L13b)** (agreed with the global master): its `whnf` timeouts persisted over two rounds; it is optional — `lim_exact_ribet` takes the A-surjectivity as `hA : Hyp.InvLimExact`. Consequences: the stage-04 L13b row marks it optional; the chapter keeps `thm:s04-lambdaribet`(a) at *proved* (no `\stformal` upgrade of the A-surjectivity in M10b); the `Hyp.InvLimExact` HYPOTHESES row says it stays undischarged.
8. **Not formalized (recorded per L16 R17):** `ordRank_const` (S04-L10b; only the freeness `ordFree_finite` is formalized); the control quotient isomorphism `e ⧸ (e ∩ ker π''_*) ≃ e R[X_s]` and its tensor form (S04-L10 round 4 dropped `ordControlEquiv` after a persistent `HasQuotient` failure; control = surjectivity + `ker_ordPush`); `diamondM` is defined via the central idele `e_p`, its identification with the product of the one-prime `diamond`s is not formalized (S04-L5).
