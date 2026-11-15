# Adversarial audit of the stage-02 replan (revision 2, 8420e70)

Auditor: Opus, 2026-11-14. I read `stage-02.md` against brief `replan-s02-06.md` (conventions A–F and the required
structure), OVERVIEW rev. 2 (§2, §3.6, §4.3, §4.4, §5, §6.1, §9), the stage tex, SPLIT, rev. 1 (7ce2a3e) with the
Muse audit and its resolution, `stage-03.md`, `runs/s01.md`, `experiments/{SUMMARY,LOG}.md`, EXPERIMENT_PROTOCOL and
`plan/implementation/tools/exp_*.sh`. I also checked the Lean tree `lean/Langlandscape/` (= main; no Lean changes since
7ce2a3e) and the import, including `tools/{titan_batch,check_wp,new_wp,lfile}.sh`.

**What I verified as correct:**
- Every S01 declaration in §0.4 exists under the stated name and file. Spot checks of the signatures: `U0q` (takes
  `q.Coprime d.D`), `Iw := K0 ℓ 1`, `translateMap`, `heckeT_comm_translate` and `heckeT_comm_rightTranslate_localEmbed`.
- Every stage-tex label used in the plan exists, and so do the `s01` labels in `mathematics/chapters/s01/`.
- The int1, int2 and strand spec lines are syntactically valid for `titan_batch.sh`.
- The mathematics of L1 (d), `s1`, `relIndex_Iw` and the C3/T1/L8 numbers is right: rank = |E| − |V₀| − |V₁| + 1 in every
  case, and the free rank is (q−1)(k−1)|X|.
- The critical-path sum is right: 5+17+13+20+39+8+8+10+8+7+5 = 140.
- The structure follows §0–§7, and the sentence "launchable without Abhijit" is present.
- E4 on M1 is sound: it is routine, off-path, local, needs no TITAN, gets a blind Fable audit, and has a 45-min cap.

## Findings

### A1 — crit — §3.1 steps 1–2 (launch order; E1 contamination)
**Problem.** Step 1 creates all wave-A worktrees, including both E1 strands (`exp/…` at "the same base sha"), and the
workers start then. Step 2 widens `check_wp.sh` only afterwards. Strand jobs build the strand commit, not the
integration tree. So `titan_batch.sh` → `check_wp.sh` still requires `s01-` in every docstring there. Every L1 theorem
with an `s02-` docstring then FAILs. These spurious FAILs are relayed verbatim to both strands, which is an implicit
hint to write `s01-`. That costs at least one round on the critical-path WP and contaminates E1. The M lane has the same
problem: branches created before step 3 lack `chapters/s02.tex` and `standalone-s02.tex`, so TEX(...) cannot run.
**Fix.** Reorder X1:
1. Do the `check_wp.sh` widening and the chapter/standalone stubs first and commit them on `wip-implementation`
   (≈ 5 min).
2. Record that sha as `BASE_S02`.
3. Create every WP, strand and lane branch from `BASE_S02`.

Acceptance: `git merge-base --is-ancestor <X1 sha> <branch>` holds for each `exp/s02-*` and `impl/s02-*` branch.

### A2 — maj — §1 L11, §3.4, §4 (root aggregators and `PrintAxioms` are never fed)
**Problem.** No WP or step adds the new modules to `Langlandscape.lean` or `LanglandscapeTests.lean`. Rev.-1 L11 had
"root imports"; rev. 2 turned L11 into a gate only. Those modules are `Tree.{Local,Coset,Admissible,Action,BrandtGraph,
NormOne,QuotientCore,Quotient,Hecke,TwoTerm,Indef}`, `Graph.{Bipartite,H1}`, `Hyp.{SA,HS,BTtree,SerreCoh,SerreFree}`,
`Quat.LevelNrd`, plus the tests `LanglandscapeTests.S02.*`. Gate step (a) builds the `lean_lib` roots only, and
`Audit/PrintAxioms.lean` imports only `Langlandscape`. So gate-1 either passes vacuously (S02 modules never built) or
fails at (c) with unknown constants. In addition, §3.4 "after gate-1 input: … appends the headline subset" is ambiguous:
the lines must be in `PrintAxioms.lean` *before* gate-1 runs.
**Fix.** Write in L11 (and per merge, OVERVIEW §1 aggregator rule): the stage master adds the 19 library and ≈ 10 test
import lines (list them) and the §3.4 headline `#print axioms` lines before `s02-gate-1`. Add a gate-1 acceptance check:
`grep -c 'Langlandscape\.\(Tree\|Graph\)' a-build.log` ≥ 13 built modules, and every headline name printed.

### A3 — maj — §1 rows vs §3.3 spec lines (file names, missing AXIOMS lines)
**Problem.** The rows for L4b, L5a, L5b, L6, L7, L9 and L10 say only "tests". The spec lines invent the names
(`BrandtGraph.lean`, `NormOne.lean`, `LevelNrd.lean`, `TwoTerm.lean`, …). A worker who picks another name breaks the
round:
- `check_wp.sh` exits 1 with "no such file", which contains no FAIL token, so the summary shows `rc=1 0 FAIL lines`.
- The one `lbuild` over all `+modules` very likely fails target resolution for the whole round, so every WP of the
  round is lost.

Other gaps:
- `L4a-act` has no `AXIOMS` line, so CHK(L4a-act) as defined in §1 is undefined. If its decls go into
  `s02_l4a_axioms.lean`, a red `Action.lean` turns L4a red too.
- X3 has no AXIOMS line.
- The strand spec file is unnamed (OVERVIEW: `.titan/spec-<wp>.txt`).

**Fix.**
- Put the exact test path in every row.
- Add `AXIOMS .titan/s02_l4a-act_axioms.lean`.
- Name the strand spec `.titan/spec-l1.txt`.
- Define CHK(X3) without an AXIOMS line.
- Add a pre-flight to the stage master's `.titan/` commit:
  `awk '!/^#/ && $1!="AXIOMS"{for(i=2;i<=NF;i++)print $i}' spec | xargs -n1 test -f`, and likewise for each AXIOMS
  path.

### A4 — maj — §0.2 / L3 (`Hyp.SerreCoh`, `Hyp.SerreFree` are false as sketched)
**Problem.** `Hyp.SerreCoh d q hq U hU R` leaves `hU` unspecified. Serre's identification holds only for the quotient
`Γ_U\T`, which equals `BG(U,q)` only under (iii) (tex `prop:s02-coh` "assume (iii)"). At a q-level where BG is
disconnected, `H_0(Γ_U,R) = R` but `coker partialHom = R^{#components}`. The Prop is then false, and every theorem using
it is vacuous there. The same holds for `SerreFree`: tex `prop:s02-free` assumes (iii) and triviality at U **and** at
`U0q U`.
**Fix.** State both with `(hconn : BGConnected d q hq U hU)`, and `SerreFree` with `(hfree : ∀ x, Gam U x = ⊥)`. Make
these an explicit item of the L12 faithfulness check.

### A5 — maj — L6 `card_XB_U0q_of_free` (wrong hypothesis)
**Problem.** The hypothesis is `∀ x, Gam (U0q U) x = ⊥`. The mass identity Σ_y 1/|Γ_y| = (q+1)·Σ_x 1/|Γ_x| shows
that `|X(U0q U)| = (q+1)|X(U)|` is **false** whenever some `Γ_x` at level U is nontrivial. The tex requires triviality
at both levels.
**Fix.** Use `(hfree : ∀ x, Gam U x = ⊥)` (this implies triviality at `U0q U`), with docstring `prop:s02-free`(b).

### A6 — maj — L5b/L6 (`…_of_SA_HS` cannot be proved from the declared L5b outputs; export for stage 03)
**Problem.** L6 promises `…_of_SA_HS (hSA) (hHS) (hU)` without `Hyp.BTtree`. L5b exports only:
- (iii) ⇒ bijections;
- (ii) ⇒ (i), i.e. `surj_of_SA`;
- (i) ⇒ (iii) under `hBT`.

Without BTtree, the route from SA ∧ HS to the bijections needs a lemma "(i) ⇒ bijections". That lemma is true and
tree-free: type-0 surjectivity plus local surjectivity gives the edges, and `s1` is onto. But it is not declared.
Separately, stage-03 §0.4 (S03-L9) asks for "a lemma deriving `BGConnected` from `Hyp.SA`, `Hyp.HS`, `Hyp.BTtree`". It
is not named either.
**Fix.** Add to L5b `bijective_of_surjType0` (tree-free) and `BGConnected_of_SA_HS (hSA) (hHS) (hBT)`. Then L6's
`_of_SA_HS` versions use the first.

### A7 — maj — L7 (understated; missing S01 API; ill-typed corollary)
**Problem.**
- S01 has no `heckeT` commutation with level-change pullback or trace for general `U' ≤ U`. There is only `Up_comm_pull`
  for towers, proved by explicit representatives.
- `heckeT_comm_translate` needs `g⁻¹Ug ⊆ V` **and** `gVg⁻¹ ⊆ U`. The second fails for `α` between `U0q U` and `U`.
  `heckeT_comm_rightTranslate_localEmbed` covers only the translation factor of `s1` = (level change) ∘ (right
  translation), and `s0` is pure level change.
- The push versions live on `ZX`, so they need `heckeTHom` (transpose), not `heckeT`.
- `Up_comm_s1Pull` is ill-typed: `Up` is defined only at `Utower` levels, and `U0q (Utower …)` is not one.

**Fix.**
- Add named outputs `heckeT_comm_levelPull` and `heckeTHom_comm_levelPush`, with hypotheses: `U' ≤ U` equal away from
  q, `localProjUnits … q t = 1`, and `hfin` at both levels.
- Restate the Up corollary as `heckeT` of `localEmbedGL d p hp (varpiDiag p)` at both levels.
- Reclassify L7 as hard (opus + planned fix), or split it into L7a (level-change lemmas, opus) and L7b (corollaries,
  sonnet). Re-estimate int3.

### A8 — maj — L4a (missing `det ∘ ι_q = nrd`; on the critical path)
**Problem.** `gammaQ_mem_SLq` and `gammaU_smul_vtype` need `det (localComponent … u) = nrd (u_q)`. Neither S01 nor the
import exports this: the import has only the *private* `hl_det_eq_nrd` (HeckeLocal.lean:230). Because `ι_q` is a
`Classical.choose` (F7), the proof needs a characteristic-polynomial argument (or Skolem–Noether). This is real work
hidden in a 17-min critical-path draft.
**Fix.** Make `det_localComponent` (or `det_gammaQ`) a named output. Put it in L10 (off-path, wave A) or a small
opus-run WP in wave A that L4a stacks on, and adjust the estimate.

### A9 — maj — L1 inputs (E1 brief incomplete)
**Problem.** `lem:s02-tree`(c), transitivity of `SL₂(ℚ_q)`, is the hard part. Tex L02.1 names its reuse: the import's
`GL2TF.Local.iwasawa_local`, `cartan_exists` and `cartanElement` (`AlgJL/VolI/P0/Decompositions.lean`), together with
S01's bridge `mem_K_iff_GL2Zl` (`Brandt/ImportDictionary.lean`). The L1 inputs omit all of them. Both strands get the
same weak brief, which inflates the measured cost of hard Lean and the critical-path time.
**Fix.** Add these inputs to the L1 row and the strand brief.

### A10 — maj — §3.2 / §5 (E1 neutrality and blindness)
**Problem.** The reference strand's commits are merged into `impl/s02-int<k>`, which is pushed to origin and built by
TITAN. The default merge message "Merge branch 'exp/s02-l1-opus' …" leaks a model name (OVERVIEW §5.2: neutral naming,
and `exp/*` stays local). The int tree also reveals which letter is the reference, and §5 states reference = opus. So a
"blind" Fable auditor who reads the plan or the int history can deduce the model.
**Fix.**
- Import the reference as one squashed commit with a neutral message (`git merge --squash` →
  `lean: import L1 draft (stacking)`).
- The Fable strand auditor gets only the `exp_prepare_audit.sh` scratch directory. The plan, `events.tsv` and git
  access are excluded from the auditor brief.

### A11 — maj — §5 (experiment tooling and briefs are missing for stage 02)
**Problem.** `plan/implementation/tools/exp_prepare_audit.sh` is hard-coded to s01:
- `wp="${strand#s01-}"`;
- the label grep is `:s01-` only, so the stage excerpt for s02 labels comes out empty;
- the fingerprint grep is `exp/s01`.

`exp_make_briefs.sh` is s01-specific too, and `experiments/briefs/` has no `l1.md` or `m1.md`. The plan's events
`titan_send` and `titan_result` are not in the protocol §5 vocabulary. No WP owns any of this, so E1/E4 cannot be set up
"from this file".
**Fix.** Add an X1 step, or an X5-like WP (sonnet, ≈ 10 min, before the strands start):
- generalise the scripts to `s[0-9][0-9]-`;
- write `experiments/briefs/{l1,m1}.md` from the rows and record `brief_sha` in `setup`;
- define `titan_send` and `titan_result`, or map them to `build s=;queue=`.

### A12 — maj — §2 critical path / risk 5 (E1 has no deadline)
**Problem.**
- L1 is not on the stated critical path, although L4a-act, L4b, L5b and L6 (the solid edge `L1→L6`) depend on it.
- The E1 cap is 105 min, which exceeds the slack before gate-1.
- Risk 5 gives only "+20–30 min" and no trigger.

**Fix.**
- Add a decision rule: if the reference is not CHK-green in its strand job of the int2b round (≈ t+50), the stage master
  moves L1 into the production pipeline (opus fix or split). The challenger continues as off-path data until its cap.
- Show the L1 branch in the critical-path calculation (X1 5 → L1 draft 20 → 2 strand rounds ≈ 25 → green ≈ t+50).

### A13 — maj — cross-stage interface (stage-03 §0.4 vs stage-02 outputs)
**Problem.** Stage 03 consumes:
- `XindefV` "on Brandt modules with coefficients" (S03-L11). Stage 02 delivers trivial coefficients only (`XindefR`,
  default of Q2).
- `Tree.BG U q` and `Tree.BGConnected U q`, whereas stage 02 declares `BG d q hq U hU`.
- `langlandscape/tree/{quotient,twoterm}.py`, whereas stage 02 writes `tree.py` and `twoterm.py`.

**Fix.**
- Add an "Exports to stage 03" table to §4 with full names and signatures: `Langlandscape.Graph.{BipMultigraph,
  boundary, H1, Connected}`, `Langlandscape.Tree.{BG, BGConnected, s0, s1, s0Pull, …, partialHom, Xindef}`, and the
  Hecke lemmas of A7.
- File an outbox note so the stage-03 final pass re-binds (S03-L11 is reduced to trivial coefficients or deferred).
- Align the code paths.

### A14 — maj — §3.2 int3 / X3 (hygiene WP inside a critical-path round)
**Problem.** X3 edits S01 files that every S02 module imports, in int3, the round of L6/L7/L3. A red X3 breaks every
CHK of int3a and forces a full rebuild. Risk 8 ("dropped") comes after that round is already lost. Also, the acceptance
"warnings < 20 in int3" is not part of `titan_batch.sh`'s summary.
**Fix.**
- Send X3 as a single-WP job `s02-x3-1` (priority 3) on its own branch off `wip-implementation`, and merge it after
  gate-1 so that it is covered by the final gate.
- Add a report item: `grep -c '^warning: Langlandscape/' .titan/out/build.log`.

### A15 — min — §3.2 vs §2 (timeline inconsistent)
**Problem.**
- The rounds table puts int2b at +50, but L5b is drafted only at t+55.
- int2c is at +65, but "L5b green in int2c ≈ t+75".
- gate-1 is at +88 and final-1 at +115, whereas the summed path gives gate-1 at t+102, L14 done at t+135 and X4 at
  t+140.

**Fix.** Re-time the table from the path: int3a +78, int3b +94, gate-1 +102, int4 +128, final +135. Re-check the
remote fallback trigger ("M6 ready ≈ t+45").

### A16 — min — §3.2/§3.3 (job-id rules)
**Problem.** L5b entering in a letter round contradicts OVERVIEW §4.3 ("new number when a new set of WPs enters"). Also,
`.titan/spec-int2.txt` does not match the template `spec-int<k><x>.txt` (`spec-int2a.txt`, job `s02-int2a-1`).
**Fix.** Use `spec-int2a.txt`. Either give L5b its own number, or record the deviation explicitly. Stage 1 also ran
int2a–f with new drafts.

### A17 — min — §3.1 step 1 (worktrees)
**Problem.** "12 worktrees with impl and main: the limit" is wrong on two counts:
- The count is 5+4+1+2 = 12 *plus* impl, main and plan, i.e. 15.
- `agents/rules` have no 12-limit; it came from the S01 protocol.

`tools/new_wp.sh` hard-codes `s01-` and seeds `.lake`, and the plan does not say not to use it. Stage-03 X1 does use it.
**Fix.** Write "plain `git worktree add -b impl/s02-<wp> …-wt/s02-<wp> $BASE_S02`; no `new_wp.sh`". Either widen
`new_wp.sh` in X1, or tell stage 03.

### A18 — min — L4a/L4b/L9 (finiteness plumbing)
**Problem.** `IsQLevel` lacks the "compact open" condition of the tex (finite index). Several outputs need lemmas that no
WP names:
- `trace` (`s0Tr`/`s1Tr`) needs `hrel : (U0q U).relIndex U ≠ 0`;
- L6 counts and L9 finranks need `Finite (XB U)`.

**Fix.** Add `U.relIndex d.Ohat ≠ 0` to `IsQLevel`, and add `relIndex_U0q_ne_zero` and `finite_XB_of_isQLevel` to L4b.

### A19 — min — §0.3 (docstring gate claim)
**Problem.** §0.3 implies that `check_wp.sh` checks docstrings of public `def`/`structure`. It checks `theorem`/`lemma`
only (OVERVIEW §4.3).
**Fix.** Either X1 adds a presence-only check for `def|abbrev|structure|instance` (S02 files only), or the plan assigns
this review explicitly to every WP review and to L12.

### A20 — min — §0.2 / X1 (HYPOTHESES rows)
**Problem.** The §0.2 table gives 6 of the 8 `HYPOTHESES.md` columns. "used by", "instances" and "discharge plan" are
missing as separate columns.
**Fix.** X1 fills all 8 columns. "used by" is filled from the WP rows (e.g. `BGConnected_of_surj` for BTtree).

### A21 — min — L8 acceptance (`decide`)
**Problem.** Kernel `decide` on Mathlib's `Connected` instance (walk enumeration via `Reachable`) may time out, and
`native_decide` is forbidden.
**Fix.** Allow `decide +kernel` or an explicit walk proof. The F8 intent (a connectivity example) is kept.

### A22 — min — X2 acceptance
**Problem.** The reference file is given without a path: it lives at
`origin/impl/s01-int2f:lean/Langlandscape/.titan/l17_l4c_axioms.lean`. It lists 7 chosen names, so "listed or found"
cannot be "equal modulo order".
**Fix.** Input = the name list of the two files. Expected output = that file, modulo order.

### A23 — min — §6 (remote acceptance and bibliography)
**Problem.** Abhijit's acceptance requires "no undefined cites", but bib entries are only returned in the report.
**Fix.** Remote WPs cite only existing `references.bib` keys (`Se`, `Vo`, `Br`, `Bass1993`, `Vig80`, `LM`,
`Kneser1969`, `PlatonovRapinchuk1994`, `Casselman2014`, `DT` are present). Alternatively they create
`mathematics/bib/s02.bib` (allowed by E), and the standalone loads it with `\IfFileExists`.

### A24 — min — §2 Mermaid
**Problem.** The Mermaid diagram lacks `L10→L6`, `C2/C3/T2→X4` and `L1→L5b` as drawn in the edge list.
**Fix.** Sync the diagram with the edge list.

### A25 — min — §3.2 (TITAN contention)
**Problem.** The two E1 strand jobs take 2 of the 3 slots every round until E1 is decided (≤ 105 min). That leaves no
slot for the single-WP jobs of A14 or for early stage-03 starts (S03 Q4).
**Fix.** Give a priority order: int > E1 strands > single-WP > stage-03.

### A26 — min — L4b model
**Problem.** L4b is on the critical path, stacked on three unverified drafts (the E1 reference, L4a, L8) plus adelic
plumbing (`alphaElt_inv_conj_mem`). S01 data for stacked sonnet work: 3–4 rounds. OVERVIEW §5.1 says to use the
cheapest model that does not lengthen the wall.
**Fix.** Use opus (+ planned fix), or keep sonnet and justify it in the row.

## Counts and verdict
crit 1 (A1) · maj 13 (A2–A14) · min 12 (A15–A26).

**Verdict: GO WITH FIXES.**
- **Before X1 is launched:** A1, A2, A3, A10, A11, A12. These are edits to §3.1, §3.3, §4 and §5 plus two tooling steps,
  ≈ 30 min for a reviser.
- **Before the corresponding WP briefs are issued:** A4–A9, A13 and A14 (statement shapes of L3, L4a, L5b, L6, L7 and
  the stage-03 export table).

The DAG, the calibration, the gate sequence (early gate-1, Fable Lean ∥ chapter audit, from-scratch final), the model
table and the remote section are otherwise sound.
