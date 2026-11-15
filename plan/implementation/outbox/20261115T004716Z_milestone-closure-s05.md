<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
MILESTONE CLOSED: S05 stage-05 implementation (comparison hypothesis Hyp.X, dictionary, sub/quot, simplicial shape)
branch/commit: wip-implementation; Lean tree = 9ddd83ea (final gate), records after it (PDFs 1b1ae92a, runs/s05.md, this file); base fafd7837 (main stage-4 merge)

delivered:
- Lean (lean/Langlandscape/, 0 sorry; PrintAxioms 598 -> 747 rows, 111 + 8 + 30 new stage-05 declarations; coverage 9 library + 6 test modules):
  * Comparison hypothesis (Hyp/HypX.lean, Hyp/HypXGal.lean): `CharGroupData`, `Hyp.X.char` ((X1)-(X3), one family phi for all s), `Hyp.X.iso`
    (def:s05-Xiso, level-wise), `TateModuleData`, `wPairingZp`, `Hyp.X.gal` ((X4), takes phi as argument, FD1 clause marked provisional). All three registered
    open in HYPOTHESES.md; Hyp.X is never called known.
  * Dictionary (Comparison/Dictionary.lean, L1, 28/28): `degZero` (= ker of Ordinary.deg, reused from stage 4), `HeckeSym`, `diaZX`, `theta`, `Tp`/`thetaZX`.
    Consistency (L5, 18/18; lem:s05-consistency (a)-(d), theta adjoints, projection formula, Up_comm on degZero). DR bridge `degZero_equiv_graphX` (L2b, 8/8).
    `ThetaAdj` (L4g, 30/30): `thetaAdj` + spec, `thetaUqEquiv` (theta(U_q) invertible), `theta_comm_Uq`, all unconditional.
  * Sub/quot: `CommAlg/SubQuot.lean` (prop:s05-subquot: `subquot_kernel`, `subquot_coker`, L6, 28/28) and `Comparison/XIso.lean` (prop:s05-Xiso algebraic half,
    `xiso_of_gorenstein`, L8a, 4/4), done remotely by Abhijit (acc-b5-1) and merged at X1.
  * Lambda-adic comparison, finite level: `Comparison/XLambda.lean` (L7, 21/21 -> 47/47 with L11b): `xlambda_finite` unconditional via `ekillsA_tower_uncond`,
    `xlambdaPsi`/`xlambdaOrd` (common Psi, induced iso), `xlambda_equivariant` for one Psi, `theta_adjoint_Tp` (audit R2-1..R2-3).
  * Non-vacuity instances (LanglandscapeTests/Hyp/S05.lean, L4 + L11c, 39/39): `canonicalCharData_char` (phi = id), `toyXIso_holds` (T = Z, a = (5), L = H = ZMod 5),
    `toyTate_gal_uncond` for all s (direct-sum model, middle piece omitted; built from L4g). Test modules LanglandscapeTests/S05/{Consistency,DRBridge,Dictionary,SubQuot,XLambda} (LT, 21/21).
  * Errata lane E1 (18 items from the hypotheses report, 598/598, +6 S02 Hyp rows); S04-IMP-old lane (28 old GL2TF/AlgJL-dependent files, import lines only; imp-old-3 green).
- Mathematics: chapter s05 (Abhijit's M1-M7, R1, lit-b4/b5/b6 merged at X1; sign epsilon = +1, e = delta = +1, Frobenius table, Gamma_1-level status, geometric route (G1)-(G5),
  Hyp.X (X1)-(X4), sub- versus quotient lattice, simplicial shape / zig-zag); M10 ((c2) of prop:s05-Xlambda downgraded to open with rem:s05-c2open, lem:s05-normtwist proved,
  explicit FD1/FD2 `\provisional` markers); M8 Fable chapter audit (PASS WITH REMARKS, 0/3/11; plan/implementation/audits/s05-m8-chapter-audit.md) fixed in M9a; M8b follow-up (PASS, 0/0/8;
  s05-m8b-chapter-audit.md) fixed in M9c; M9b (C1-C3 verdicts into sign.tex, pair criterion q^2 != +-1 mod N). Milestone PDF mathematics/main.pdf 140 pp (commit 1b1ae92a).
- Code: code/ stage-5 comparison subpackage, results/s05/T05-1..3: T05-1 U_q = +Pi_q on 144/144 eigenlines (16 (q,k) pairs, 0 minus); T05-2 Gamma_1 dictionary (delta,e) = (+1,+1) confirmed at
  (13,5), (11,7), (23,5), (23,7), no contradiction; T05-3 Mazur check (q-1)/12 pointer. pytest 419 passed / 3 skipped.
- Talk: slides s05 two-part zig-zag (T2) and geometric-route cost slide with the T05-1 count (T1); talk/main.pdf 13 pp (commit 1b1ae92a).
- Experiment E5' (S05-L4, Lean mechanical-with-meaning, blind Fable audit): winner = sonnet draft + one opus fix (active 16.8 vs 27.5 min, tau = 5, W 3 / Q 6 vs W 2 / Q 7), both strands
  passed; merged = strand B (first green head 37228dcf), so merged = winner. Cell decided (prior): sonnet first + 1 opus fix (LOG.md 3c926260; model-selection.md evidence row added on main by the global master).
- Lean Fable audit L10 in three parts (lean/Langlandscape/audits/2026-11-15_s05.md): part 1 PASS WITH REMARKS (2 required, 9 optional), part 2 PASS WITH REMARKS (6 required R2-1..R2-6, 9 optional),
  part 3 PASS WITH REMARKS (3 required R3-1..R3-3, 9 optional); fixes L11a, L11b, L11c merged in-stage; all required items closed.

verification:
- s05-gate1-1 (TITAN, 5641534e): PASS all six steps, 709/709 standard (nonstandard 0, 15 strict subsets), unseeded from scratch 279 s (seeded 223 s, 4154 jobs); warnings 191 / 71.
- s05-int4c-1 (CONCEPTD, aba2667): L11c 39/39, full build rc 0 (4160 jobs), PrintAxioms 747/747 nonstandard 0, forbidden grep empty, sorry = the import only; warnings Langlandscape/ 183 (126 non-import).
- s05-final-1 (TITAN, from scratch, 9ddd83ea): PASS all six steps, 747/747 standard (17 strict subsets), 273 s, 4160 jobs (expected 747/747; steps (a) Langlandscape + Tests, (b) VendorStacks, (c) PrintAxioms, (d) forbidden grep, (e) sorry count, (f) check_frozen, check_wp on all stage-05 files; coverage 9 library + 6 test modules; warnings 183 / 71).
  CONCEPTD cross-check s05-final-1x (fresh unseeded checkout, 9ddd83ea): PASS all six steps, 747/747 standard, 4:22 from scratch.
- Audits: Fable chapter M8 + M8b (closed in M9a/M9c); Fable Lean L10 parts 1-3 (closed in L11a/L11b/L11c); E1 opus review; E5' blind Fable strand audits.
- latexmk mathematics/main.tex rc 0 (140 pp), talk/main.tex rc 0 (13 pp); pytest code/python 419 passed / 3 skipped.

open issues (follow-ups):
- prop:s05-Xlambda(c2) is open (`\stconj`/`\stopen`): rem:s05-c2open lists 6 missing steps (i)-(vi); no proof is given; (d2)'s Hom_Lambda form and rem:s05-BN are flagged.
- FD1 and FD2 are provisional (Fabian decisions): FD1 markers in sign.tex, hypX.tex, FD2 at geometric.tex; Hyp.X.gal docstring carries "provisional (FD1)".
- The hybrid dictionary is excluded only modulo cited results (T05-2 is at s = 0 and cannot exclude it; sign.tex: excluded modulo JL incl. U_p + strong multiplicity one, at levels with a non-real a_p, `\stpmc`).
- The pointer to Jacquet-Langlands Thm 14.4 and the SGA 7 pointers (IX numbers, Thm 2.4 form) are unchecked (marked as such in M9c; SGA 7 not in literature/).
- Lean instance context: no closed Lean term inhabits the Hyp.X instance context (d, M, p, q, hN, hp, hM, hpM, hD, Pq, hPq): there is no IsUniformiserElt witness in the tree, only `hurwitzData`;
  non-vacuity is relative to that context (audit R3-1, documented).
- Hyp.X.iso is level-wise (one level, no compatibility in s with pi_* / trace); a tower version needs Lambda-adic freeness (Hyp.MordLambdaFree, open).
- `HeckeSym` has no U_l for l | M (K1-level finiteness not in the tree): (X1) is weaker than the chapter's for M > 1 (documented in HypX, Dictionary, HYPOTHESES).
- Hyp.X.gal toy model leaves tau / TI / the top and middle Frobenius unconstrained (tau = id, N != 0 admissible, TI only ker pi_X, no transport to H^1_par, p >= 5 not assumed); the instance is unconditional
  (L4g) but non-faithful as a model of (X4).
- No statement theta(h)^* = theta(h^Ros) is formalized (only the adjoints of theta(T_l), theta(T_p), theta(U_q)); L7 beta-compatibility and the ZMod form of the equivariance are omitted (R2-7).
- L10 optional items deferred: part 1 O2-O8 (O5 imports, O6 pushforward location, O7/O8 docstrings, O3 U_l), part 2 R2-9..R2-15 (s' = s+1 only, not-a-module notes, `baseChange_apply_eq` duplicate,
  generic lemmas in the theorem file, `open scoped Classical`), part 3 O-2, O-3, O-5, O-7, O-8, O-9 (duplicate `pushDegZero`, general lemmas in a test file, no XIso test, namespace scheme).
- Lint: duplicated namespace `Hyp.X.CharGroupData.X` (rename changes the L4-facing signature); `haveI` lints (12 in Tests/Hyp/S05, 4 in ThetaAdj), deprecated `push_neg` at Tests/Hyp/S05:99, unused section
  variable `[Fact (Nat.Prime p)]` in `PiEllHom_commute_diaZX`, Consistency 64:69, 207:35, XLambda 379:4; warnings 183 / 71 (down from 191 / 71 at gate-1 only in part).
- The production L4 writer (impl/s05-l4, char + iso only, green in int3b 9/9) is not merged (superseded by strand B).
- Branches/worktrees to clean: impl/s05-* (l1, l2, l3, l5, l7, l2b, ct, m10, e1, l4, l4g, l11a-c, lt, int3b, int4a-c), exp/s05-l4-a and exp/s05-l4-b (exp never merged except strand B), `titan-in/s05-e5-D-1`,
  worktrees in ../Langlandscape-wt/s05-*; impl worktree must stay on wip-implementation (scratch worktree s05-int for pushes).
- Incident 00:19Z: `git push origin HEAD:wip-implementation` from the impl worktree while it was on the strand-D line put 2 strand-D commits on origin/wip; repaired by the global master by
  force-with-lease to 7e82aca2; process fix: all scratch branches (impl/s05-int*, titan-in/*) are prepared in the detached worktree s05-int.
- Stage wall: t0 23:40Z; gate-1 sent 00:17:10Z (t = 37), gate-1 PASS 00:23:11Z (t = 43 min, plan ~80 min); final gate sent 00:40:26Z (t = 60); final gate PASS 00:46:24Z (t = 66 min ≈ 1.1 h). Plan ~2.1 h (range 1.5-3.2 h).

request: merge wip-implementation into main (Lean tree 9ddd83ea) (final gate s05-final-1 PASS); mirror mathematics/main.pdf (140 pp) and talk/main.pdf (13 pp); then stage 06
(exports: Comparison.degZero/theta/HeckeSym/thetaAdj, Hyp.X.{char,iso,gal} with the three instances, Comparison.xlambda_finite/xlambdaOrd, subquot_kernel/coker, xiso_of_gorenstein; HYPOTHESES rows).
