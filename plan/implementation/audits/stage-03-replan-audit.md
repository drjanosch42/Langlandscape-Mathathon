# Stage-03 re-plan audit (adversarial, Opus, 2026-11-14)

Subject: `plan/implementation/stage-03.md` (66b221d, notes 46beb8b), checked against the brief `briefs/replan-s02-06.md`
(A–F + structure), OVERVIEW rev. 2 (§4.3, §4.4, §5, §6.1, §9), the staged tex `stage-03-ribet-ihara.tex`, SPLIT §03, the
coarse plan (7ce2a3e) with its Muse audit and resolution, `runs/s01.md`, `experiments/SUMMARY.md`, EXPERIMENT_PROTOCOL, and
the Lean tree at 7ce2a3e. **Stage 02 was rewritten** (8420e70, "revision 2, ready to launch"), so the stage-02 interfaces
are compared against that file, not only against the tex.

**Verified (no finding):** all 31 `…:s03-…` labels cited by the plan exist in the tex. Every stage-1 declaration in §0.3
exists (`Tl_selfAdjoint_U0'` in `Brandt/HeckeFinite.lean:329`, `brandtMatrix_mul_wx`, `trivialLevel`,
`relIndex_elemT_ne_zero_Ohat`, `massFull_eq_massW_of_mem`, …). So do the import's `brandtMatrix`, `brandt_row_sums`
(row sum `σ₁(n)`, on `eichlerOrder φ`), `brandt_weighted_symmetry` and `normWeight` (`Pairing.lean:30`), and Mathlib's
`AddSubgroup.index_eq_natAbs_det` (`CardQuotient.lean:98`). The sign of α is consistent with (C1) everywhere:
`α = (−s₀*, s₁*)`, `αα† = [[q+1, −T],[−T, q+1]]`, `T = s₁*s₀†`, the B₁₁/q = 2 check `det [[3,2],[2,3]] = 5`, and the
stage-02 rev. 2 boundary `e ↦ (−[s0 e], [s1 e])`. The numbers in the tests and tables check out: Mazur 5, 11, 3, 25, 65;
h = 2, 3, 3, 9, 12; (2,2,2) gives 12 = 2·6. The critical-path sum is arithmetically 141. The cap is
min(3·25, 25+60) = 75. The structure has sections 0–7 as required.

## Findings

### A1 (crit) §0.4, S03-L11: Ihara (iii) binds to a coefficient complex that stage 02 does not deliver
- **Problem.** Stage 02 rev. 2 §0.1 delivers the two-term complex **with trivial coefficients only**. Its `partialHom` is
  `ZX (U0q U) R →ₗ[R] ZX U R × ZX U R`, and the V-coefficient version is explicitly deferred to stages 04–06. Its
  `XindefV` is renamed `XindefR … R := ker partialHom`. Stage 03 §0.4 assumes "`partialHom`, `XindefV` on Brandt modules
  with coefficients". `Hyp.IharaH0` (V a f.g. ℤ_p-module with continuous U_p-action, exported to 04/06, "shape
  load-bearing") therefore has no `α` to refer to, and nobody owns the V-coefficient α.
- **Fix.** Choose one option and write it into §0.2/§0.4:
  - (a) L11 defines `Ribet.alphaV` on `Brandt.brandtModule ρ` itself (from S01 `pushforward`/`trace` and the C3
    traces), and is re-classed conceptual+hard: opus (+1 planned fix), 60–80 min wall, on the critical path (see A5).
  - (b) `Hyp.IharaH0` is stated for trivial action over `R = ZMod (p^m)`/ℤ_p on stage 02's `partialHom`. The
    V-coefficient shape is recorded as a stage-04 item, and stage-04/06 consumers are notified (outbox).

  The L11 shape test (`V = ℤ_p`) must state which option it uses.

### A2 (maj) §4 exports and cross-stage seams: the Ribet sequence is over ℤ only, and the export names do not match 04/05
- **Problem.**
  - `stage-04.md:73–74, 140` (S04-L12) needs `if:s03-ribet` "over ℤ **and with coefficients**" (`e ℤ_p[X]⁰`), but
    L2(a)/L9 are over ℤ only.
  - `stage-05.md:89, 145` needs `Graph.WGraph`, **`Graph.X`** and the DR graph, but the plan names `WGraph.X` and
    `Ribet.DRgraph`.
  - The export list in §4 (`phiComb`, `ribet_exact`, `ihara_ker_const`, `Hyp.IharaH0`, `epsilon`) omits `WGraph`, `X`,
    `PhiComb` and `DRgraph`.
- **Fix.**
  - State L2(a) and L9 for any `CommRing R`. Stage 02's `boundary G R` is already R-linear, and the connectivity proof is
    the same.
  - Fix one name for `X` (`Graph.WGraph.X`, with stage-05 rebinding) and list all of `WGraph`, `WGraph.X`, `PhiComb`,
    `DRgraph` and `ribet_exact` (R-version) as exports.

### A3 (maj) §0.4: the stage-02 binding can be fixed now
- **Problem.** Stage 02 rev. 2 differs from the plan's assumptions in several places:
  - `BG d q hq U hU` (not `BG U q`), `s0 U`, `s1 hU`, `BGConnected … := (BG …).Connected`.
  - The rank lemma `finrank_H1_of_connected` holds **over a field K only**. L2's `bip_rank` over ℤ cannot "use the
    stage-02 rank formula" and must come from exactness plus `finrank` of deg⁰. `range_boundary_of_connected` exists
    and should feed L2(a).
  - The Hecke names are `heckeT_comm_s{0,1}{Pull,Push}`, `Tl_comm_s1Pull`, ….
  - The code modules are `langlandscape/tree.py` and `langlandscape/twoterm.py`, not `tree/{quotient,twoterm}.py`
    (C3, C4).
  - S02-X1 already widens `check_wp.sh` to `s[0-9][0-9]-`.
  - S02-X2 ships `tools/gen_axioms.py`, but S03-X2 re-invents a "tools-free one-liner".
- **Fix.** Rebind §0.4 to these names now. Drop the X1 regex contingency. X2 runs `gen_axioms.py`. L2 lists
  `range_boundary_of_connected` as input and proves the ℤ-rank itself (raise its wall, A5).

### A4 (maj) §2 DAG: L3 starts before its upstream exists, and edges are missing
- **Problem.**
  - The edge list has L1→L3, yet W1 (t ≈ 8) contains L3, int1 (t ≈ 30) contains L3's first draft, and the critical path
    goes X1 (8) → L3 with no L1 time. Under brief C a WP stacks on a **drafted** upstream, and L1's draft takes ≈ 10 min.
  - Missing edges: L1→L2 (`bip_collapse_connecting` needs the collapse/`phiComb` of L1) and L1→L9, L1→L10/L11 where
    they use `boundary_ofBip`. §0.2.4 says "every later WP uses that lemma".
- **Fix.** Either declare the L1 row's signatures binding at X1, so that L1 and L3 start in the same minute and L3
  stacks on the plan's signatures (state this explicitly as a deviation from "drafted upstream"), or add L1's draft time
  (≈ 10) to the path. Add the missing edges in the edge list and in Mermaid. Also add X2→int2b/gate-1 in both.

### A5 (maj) §1, §2: walls are not calibrated per §4.4, and the timeline contradicts itself
- **Problem.**
  - §4.4 says to take the upper half for hard/conceptual WPs. Instead L2 (hard) is planned at 40 wall/15 active, L11
    (conceptual) at 45, and L3 at 60.
  - The stage-1 hardest Lean WP, L3d (opus), took 78 min and 3 rounds, with far more reuse.
  - The coarse L2/L3 estimates were 150 agent each; × 0.25 ≈ 38 active, against 15/20 planned. That is a deviation over
    50 % with no explanation, and dropping Stacks (A16) makes L2/L10 *more* work.
  - With L2 ≈ 70, the chain X1 → L2 → L9 → gate-1 (≈ 113) overtakes the L3 chain (90).
  - The timeline is internally inconsistent: §3.2 has gate-1 at ≈ 80, int3 at ≈ 105 and final at ≈ 115, while the
    critical-path sum puts gate-1 at 100 and the final gate at 136.
  - X1 is counted as 8 (agent) instead of 10 (wall).
- **Fix.** Re-estimate with the upper half: L2 ≈ 65–75, L3 ≈ 75–80, L11 ≈ 60–80 (more under A1(a)). Recompute the path
  (expected ≈ 160–175 min, stage ≈ 2.8 h, range 2.2–3.6 h, in line with OVERVIEW §7's 3.0 ± 0.8) and align the t-column
  of §3.2 with the sum.

### A6 (maj) §3, S03-X2: AXIOMS only from int2b blocks every merge before int2b
- **Problem.** Green = `CHECK_WP … 0 FAIL` **and** `AXIOMS … rc=0 nonstandard=0` (OVERVIEW §1, §4.3), and LCHK requires
  the headline names in the round's AXIOMS file. With X2 only at int2b, no WP of int1 or int2a can be green or merged.
  That contradicts the §3.3 fallback "merge the green WPs now" and lesson D1's early gate. A single combined
  `axioms-s03.lean` also turns every WP red (`rc=1`) when one name is missing (s01-int3).
- **Fix.** Move X2 to W1 (deps X1). The names are already fixed in §1/§3.4. Use one axiom file per WP,
  `.titan/s03_<wp>_axioms.lean` (OVERVIEW §4.3, as in S02), with an `AXIOMS` line per WP from int1 on.

### A7 (maj) §4, §1: WP-level audits and fix budgets are missing
- **Problem.**
  - OVERVIEW §5.3 requires an opus WP audit before merge for every hard/conceptual WP. §4 audits only L2, L3, L11, C4 and
    the strands. M3, M4, M5 (hard, "+ planned opus fix") and M7 (conceptual) get none, so their planned fix round has no
    input.
  - Brief A says every WP names a fix budget. L11 ("opus"), L13 ("sonnet / opus") and H1 ("sonnet") have none.
- **Fix.**
  - Add an opus WP audit to M3, M4 and M5 (for M5 a Fable adversarial audit, because the normalisation is exported, A8).
    The audit result feeds the planned fix round.
  - L11: opus (+1 planned opus fix).
  - L13: sonnet (+1 opus fix ≤ 5) per Lean item, opus (+1 planned fix) for hard items.
  - H1: sonnet (+1 opus fix ≤ 2).

### A8 (maj) S03-M5, C5, H1: the `prop:s03-PsiPsi` normalisation is delegated, not fixed, and nothing checks it
- **Problem.** The tex M5 item requires proving Ψ*Ψ "in one fixed normalisation, and record which entry carries
  `q^{2−k}`". The plan leaves the choice to the M5 writer. C5 and H1 check only `det`, which the tex says is
  normalisation-independent, so no WP can detect an inconsistent or wrong off-diagonal assignment. Without HACS there is
  no computation at all.
- **Fix.** Fix the normalisation in §0.2, as a conceptual decision taken now: V = Sym^{k−2} of the standard column
  representation, Ψ* as in the tex. The operator acting through α'^{-1} = q^{-1}α'^ι carries `q^{2−k}`, and the other is
  the classical integral T_q. Record that `[[q+1, −T_q],[−q^{2−k}T_q, q+1]]` is (or is not) this choice, after the M5
  proof. Extend M7's scope (or add a second reader) to M5's normalisation table, and require H1 to record the same
  table. State that stage 06 uses only `det`/`coker` (tex D4).

### A9 (maj) §5 E8 mechanics conflict with EXPERIMENT_PROTOCOL
- **Problem.**
  - (a) Protocol §2.4 allows a same-model opus fix only if crit = 0 and W ≤ 5; otherwise `opus → (fail)`. That is
    exactly how S01 E8 opus failed (W0 = 6). The plan says the fix round "runs iff r0 does not pass" but does not state
    that it overrides §2.4, nor how many fix rounds are allowed (1 + delta audit?).
  - (b) "Relays … audit outputs … errors only, no fix hints" conflicts with the audit template, whose findings carry a
    "required fix". A fix round without them is meaningless, and stripping them is not defined.
  - (c) M2's escape hatch ("if step (1) fails: status → cited") lets a strand pass by downgrading. That rewards not
    proving and confounds the cell.
  - (d) The protocol cap uses "est_wall = agent wall" (15 → 45 min), but the plan uses 25 → 75.
  - (e) Neutral commit messages on strand branches (§5.2) are not restated.
- **Fix.**
  - (a) State "brief B overrides protocol §2.4 for E8: exactly one opus fix round regardless of W0, then a delta audit;
    fail if r1 fails".
  - (b) Audits are passed to the strand unedited (the protocol artefact). Only stage-/global-master commentary is
    forbidden.
  - (c) For strands, a downgrade must name the failing step with a counterexample or gap, and the auditor judges it as
    a finding (≥ major unless justified).
  - (d) Pick one cap and justify it.
  - (e) Restate the neutral commit messages.

### A10 (maj) §5, Q2: "a winning Fable strand becomes the merged section" is sound only with a production rule
- **Problem.**
  - The copied §4.4 rule ("@fable merged only if it wins and M8 has not started") is right for the experiment, but it
    leaves a hole: the opus reference is merged at TEXCHK. If it then fails its audit (ladder exhausted) while @fable
    passes, the chapter keeps a failed-audit §2.
  - Timing makes the Fable merge nearly moot. M8 starts at t ≈ 48 (after M4 → M7), while the opus strand needs
    r0 + audit + fix + delta audit ≈ 45–55 min before a winner can be declared.
  - A merged Fable section is then audited by the Fable chapter audit: a self-preference confound on the production
    gate.
- **Fix.** Answer Q2 with a rule:
  - The merged artefact is the protocol-passing strand.
  - If the reference fails and the challenger passes, the challenger replaces §2 even if M8 has started; M8 delta-reads
    §2, and LOG records `winner=fable, merged=fable (replace)`.
  - If both fail, the normal pipeline runs (opus from the best-scored branch) before M8 closes.
  - M8 notes the author-model confound for §2.

### A11 (maj) S03-X1, TEXCHK, §6: the standalone build will report undefined refs/cites
- **Problem.**
  - `mathematics/` has no `standalone-s01.tex` and no `bib/` directory. Stage 1 used `main.tex` + `references.bib`.
  - M1, M3 and M4 cite s01/s02 labels (`thm:s01-mass`, `prop:s01-adjoint`, `if:s02-*`). In `standalone-s03.tex` these are
    undefined, so TEXCHK ("no undefined refs") fails for every remote WP.
  - "loads `bib/s03-*.bib` with `\IfFileExists`" is not possible as a glob.
  - §6.1 names a single `bib/sNN.bib`.
- **Fix.** X1's standalone loads `references.bib` plus the five `bib/s03-<sec>.bib` by name, each guarded. Cross-stage
  references go through `xr-hyper` against the merged `main.aux`, or are restated as `\texttt{if:s02-…}` as the staged tex
  does (A-S03M says "restate"). Record the deviation to five bib files against §6.1, or use one `bib/s03.bib` with
  per-WP entries returned as report lines.

### A12 (maj) §1 Track M: the interface labels are not assigned
- **Problem.** `if:s03-{graph,ribet,ihara,amalgam}` are the exports to 04/05/06 and are listed in "Stage 03 done", but no
  M WP has them as outputs. The tex deviations D1–D4 and `ss:s03-conv` (M4 by implication) are not assigned either.
- **Fix.**
  - `if:s03-graph` → M1, `if:s03-ribet` → M3, `if:s03-ihara` → M4, `if:s03-amalgam` → M5.
  - D1–D4 → M4.
  - Add them to the acceptance labels.

### A13 (min) §6: the remote table is incomplete, and M7's output is not a permitted file
- **Problem.**
  - The table lacks the OVERVIEW §6.1 column "local fallback model" and the "re-run locally if not delivered when the
    first consumer is ready" rule.
  - M7 writes `mathematics/audits/s03-exponent-review.md`, which is outside the §6.1 new-files list.
  - M3 and M4 need the merged s02 chapter, so the remote base sha must be after the stage-02 merge.
  - Launchable without Abhijit: yes, as stated.
- **Fix.** Add the column (M1 sonnet+fix, M3–M5 opus+planned fix, M6 sonnet, M7 opus) and the rule. Move M7's output to
  `chapters/s03/NOTES.md` (or keep M7 local). State the base condition.

### A14 (min) §3: TITAN naming
- **Problem.** New WP sets enter in int2a (L4, L7, L9) and int2b (L6, L8). By §4.3 that calls for new numbers
  (int2, int3); letters are re-runs. The spec file is named `.titan/spec-s03-int<k>.txt`, but OVERVIEW and S02 use
  `spec-int<k>.txt`. §3.1 omits the template's "supersedes", seeding and goal-state fields.
- **Fix.** Renumber, or note the stage-1 precedent explicitly. Use the OVERVIEW file name. Reference the OVERVIEW §4.3
  template verbatim.

### A15 (min) §1: model choice for X1
- **Problem.** S03-X1 (worktrees, branches, drivers, spec file, registry lines) is kickoff infrastructure, not "copy /
  vendoring". The coarse plan recorded that Haiku stalled on long shell work.
- **Fix.** Use sonnet (+1 opus fix ≤ 2), as for S02-X1, or split off a haiku-only part.

### A16 (min) §0.2.1, Q1: the Stacks drop is justified, but the rationale is imprecise and has no fallback
- **Problem.** The drop is justified: the code is AI-written and unreviewed, the go/no-go goes away, the Mathlib route
  is verified, and stage 02 supplies `H1`/`boundary`. But the pin-guard argument is only half right. The existing glob
  `StacksCore.+` already covers the two Tactic files; only the `StacksFrontier.+` modules would need a lakefile edit. The
  plan also lists the drop as a "fixed decision" while Q1 is still open, gives no fallback if Fabian declines, and does
  not show the extra own-code cost in the L2/L10 walls (A5).
- **Fix.** Correct the sentence. Add "if Q1 = keep: an off-critical-path vendoring WP in stage 04". Reflect the cost in
  L2/L10.

### A17 (min) §0.2.3: namespace clash risk with Mathlib's `Graph`
- **Problem.** Mathlib has `structure _root_.Graph` (`Mathlib/Combinatorics/Graph/Basic.lean:90`, imported by
  `Mathlib`).
- **Fix.** Tell writers never to `open Graph` and to write fully qualified `Langlandscape.Graph.…` in axiom files and
  tests.

### A18 (min) §3.4, §0.2.6: incomplete headline list and docstring checks
- **Problem.**
  - The headline list is not "all declared outputs" (lesson D2). It omits `bip_ker_le_deg0`, `bip_surj_deg0`,
    `twoVertex_X_eq_deg0`, `phiComb_twoVertex_equiv`, `lambdaBar_surjective_iff`, `alphaDagger_deg0`, `DRgraph`, `tau`
    and the three `Hyp` defs.
  - Docstrings of public `def`/`structure` (not checked by `check_wp`) have no named reviewer (OVERVIEW §4.3).
- **Fix.** Generate the list with `gen_axioms.py` from the files. Assign the def-docstring review to the WP audits and
  L12.

### A19 (min) L6, L5, Track C: small gaps in the Mazur and code rows
- **Problem.**
  - L5 covers weights {1,2,3} (q ≥ 5), but L6 claims all primes. q ∈ {2,3} (w = 12, 6; num = 1) needs its own case, and
    L6 lacks the hypothesis `d.D = q` prime.
  - C2, C3 and C5 list JSON outputs only. `code.md` provenance needs scripts.
- **Fix.** Add the q ∈ {2,3} case and the `d.D = q` hypothesis. Name `ribet/mazur.py`, `ribet/collapse.py` and
  `ribet/betti.py`.

### A20 (min) Duplicate ownership and wording
- **Problem.**
  - HYPOTHESES rows are delivered both by X1 and by L6/L8/L11.
  - M2's acceptance says "TEXCHK; protocol pass", but §5 says the reference is mergeable at TEXCHK.
  - M2's goal calls the strand a "second reader".
- **Fix.** One owner per row (the L WP that registers the hypothesis). Acceptance = TEXCHK for the merge, protocol pass
  for the experiment record. Reword M2's goal.

**File collisions:** none found among the WPs. The new Lean files differ from stage 02's `Graph/{Bipartite,H1}.lean`,
the aggregators are stage-master-only, and the strands live on separate `exp/` branches.

## Verdict
**FAIL for the pre-launch final pass; PASS WITH REQUIRED CHANGES as a concrete draft.** Findings: 1 critical, 11 major,
8 minor.
- **Required before launch:** A1 (V-coefficient α / `Hyp.IharaH0` shape), A2–A3 (rebind to stage-02 rev. 2, R-coefficient
  Ribet, exports), A4–A6 (DAG edges, recalibrated critical path ≈ 160–175 min, AXIOMS from int1), A7 (WP audits and fix
  budgets), A8 (fixed Ψ*Ψ normalisation), A9–A10 (E8 override of protocol §2.4 and the merge rule), A11–A12 (standalone
  refs/bib, `if:s03-*` owners).
- **Sound as planned:** the E8 choice of S03-M2 (proof writing with a real correctness test, off the critical path),
  dropping the Stacks vendoring (justified, wording per A16), and the "launchable without Abhijit" claim.
