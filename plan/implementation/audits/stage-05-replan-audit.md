# Adversarial audit of the revised `stage-05.md` (Opus auditor, 2026-11-14)

Subject: `plan/implementation/stage-05.md` (revised) and `audits/stage-05-replan-notes.md`. Checked against
`briefs/replan-s02-06.md` (A–F, structure §0–§7), `OVERVIEW.md` rev. 2 (§3.6, §4.3, §4.4, §5, §6.1, §9),
`plan/staged/stage-05-comparison-hypothesis.tex`, `SPLIT.md`, the coarse plan `7ce2a3e:plan/implementation/stage-05.md` with
`audits/stage-05-{muse,resolution}.md`, `stage-06.md` (revised, early lane), `stage-03.md`/`stage-04.md` (names quoted by 05),
`experiments/SUMMARY.md`, `agents/rules/lean.md`, `tools/{titan_batch,check_wp}.sh`, and the Lean tree `lean/Langlandscape/`
(read-only).

**What was verified and holds.**
- Structure §0–§7 is present; all 30 `s05` labels the plan cites exist in the tex; every cross-stage label it cites exists in its stage tex
  (`if:s06-lemD`, `lem:s06-D`, `if:s04-{ekills,Mord}`, `if:s03-{graph,amalgam,ribet}`, `if:s02-{quot,coh,indef}`,
  `if:s01-*`, `prop:s01-relations`).
- Every stage-1 declaration listed in §0 exists (grep in `Langlandscape/`): `Utower`, `Utower_antitone`, `U0`, `U1`,
  `finite_XB_Utower`, `ZX`, `ZXdual`, `brandtPairing`, `normMap`, `heckeTHom` (args `U g R hfin`), `UpHom` (args `d M p s hN hp hM hpM hs R`), `PiEllHom`
  (args `R d ℓ hℓ P U`), `diamondElt`, `elemT`, `relIndex_elemT_ne_zero_Utower`, `Tl_adjoint`, `Tl_adjoint'`,
  `diamond_adjoint`, `PiEll_adjoint` (needs `IsMaximalAt`, available as `isMaximalAt_Utower`), `brandtPairing_translateHom`,
  `pushforward`, `trace`, `normMap_pushforward(_two)`, `towerPush`, `towerPush_eq_pushforward`, `Up_comm_push`,
  `Up_comm_PiEll`, `Up_comm_Tl'`, `Up_comm_rightTranslate`, `Up_comm_Sl`, `Up_relIndex_ne_zero`. The carried-over items
  "product diamond not assembled" and "`U_ℓ`, ℓ ∣ M missing" are confirmed by the `diamond` docstring and by grep. The new files
  (`Comparison/`, `CommAlg/SubQuot.lean`, `Hyp/HypX*.lean`, `LanglandscapeTests/Hyp/S05.lean`) collide with no existing file
  and no stage-06 file.
- FD1/FD2 are marked provisional in §0, M1, M3, M5, M8, L3, L10 and Q1/Q2, and the WPs that a reversal would change are named.
- The critical-path sum is correct: 12+20+5+7+8+7+8+7+6+10+10+7+8+5 = 120 min. The stage wall (2.0 h, 1.5–3.0 h) is within
  OVERVIEW §7 (2.5 ± 0.8 h) and the cross-check against the coarse plan (7.2 h × 0.25–0.35 = 1.8–2.5 h). The Lean WP walls
  (35–50 min) and the rounds (int1, int2a, int2b, int3 = 4) are in the calibrated ranges of §4.4.
- Models follow §5.1 (no muse or mistral; haiku only for X2 and C3). There is one conditional strand with the right trigger
  and approval. The remote rows are M, literature and review WPs only, and the plan states "launchable without Abhijit".
- The `sorry` stub plan is **legal** under `agents/rules/lean.md` l. 17 and OVERVIEW §3.6: `sorry` is allowed on `impl/*`
  for declared stubs, and the stub never reaches `wip-implementation`. Its *mechanics* are broken, however (A1).
- C2's pairs are informative: ord(13 mod 5) = 4, ord(11 mod 7) = 3, ord(23 mod 5) = 4, so characters with χ(q) ≠ ±1
  exist.

## Findings

**A1 (maj) §0 seam rule, L6 row, §3 int1/G1: L6 cannot go green against the stub, and G1 cannot contain it.**
`titan_batch.sh` builds all modules first. `check_wp.sh` then re-runs `lbuild`, and Lake replays the cached logs of
dependencies. So `checkwp-S05-L6.log` contains the stub's `declaration uses 'sorry'`, which is a FAIL. Also,
`#print axioms CommAlg.subquot_*` shows `sorryAx`, so the AXIOMS line has nonstandard ≥ 1. TCHK(S05-L6) is therefore
unreachable while the stub exists. Moreover G1 is run on `wip-implementation` (OVERVIEW §4.3 gate variant), where the stub is
not allowed, but §3 requires "L1–L7 green" before G1, L6 included. The plan contradicts itself: L6 is in int1 "against the
stub", G1 waits for L6, and L6 "merges only after `if:s06-lemD` is merged".
*Fix:* define a separate acceptance for L6 while it is stubbed: "compiles: BUILD ok for `CommAlg/SubQuot.lean`; the
CHECK_WP FAILs are exactly the stub's sorry lines; the axioms are standard + `sorryAx` only". Remove L6 from G1's precondition
unless Lemma D is merged. Then add L6 to int3/G2, or carry it (Q4).

**A2 (maj) §0, §2, §7 risk 4: the plan ignores the timing of stage 06's early lane.**
`stage-06.md` §0/§3.1 puts S06-L1 (`Gorenstein.lean`) and S06-L3(a) (`NewOld.lean`, `ann_a/ann_b`) in a Mathlib-only
early lane (`eint1`, priority 3). That lane may run during stages 02–05, ends with `s06-egate-1` and a handover merge into
`wip-implementation`, and announces "`if:s06-lemD` green" to the stage-05 master by outbox. (b),(c) follow in `eint2`. So in
the default scenario A, Lemma D(a) is **merged before stage 05 starts**, and the stub is the exception. Stage 05 says
"05 ∥ 06" and plans the stub as the normal case. It never names the early lane, `s06-egate-1`, the outbox announcement, or the
open stage-06 Q1 (who merges the early lane).
*Fix:* in §0, list the states as (1) early lane merged (expected; X1 step 4 checks for the outbox announcement); (2) in-stage
scenario B of stage 06 (L3(a) in `s06-int1`, so L6 waits about 1–2 rounds of stage 06); (3) stub; (4) L6F. Put the stage-06
dependency into §2 (edge `s06-egate-1 or S06-L3(a) merged → L6 merge`) and into the wall range.

**A3 (maj) §0 seam, L6/L6F rows: the stub's file scope and the shape disagree with stage-06 §0.**
Stage 06 puts `structure NewOldData A S`, `ann`, `IsGorensteinWith` and `IsGorenstein` in `CommAlg/Gorenstein.lean`, with
**sole owner S06-L1**. Only the lemmas are in `CommAlg/NewOld.lean`. Stage 05 stubs only `CommAlg/NewOld.lean` and lists
`NewOldData` as if it lived there, so a stub of exactly the declared signatures would not elaborate. L6F ("writes
`CommAlg/NewOld.lean`") would also need `Gorenstein.lean`, which conflicts with the sole ownership. There are smaller drifts
too: stage 05 says "`S` finite free **local**", but stage 06 has fields `free`, `finite` and no locality of `S`. The fields
`tf_a`, `tf_b`, `inf_eq_bot`, `split` and the namespace `Langlandscape.CommAlg` are not quoted.
*Fix:* quote stage-06 §0 verbatim (fields, both files, namespace, instance arguments on `A`). The stub (and L6F) covers both
files, on `impl/s05-int<k>` only. L6F needs stage-06's written agreement for `Gorenstein.lean` as well. Drop "local" for `S`.

**A4 (maj) §3 int1 spec, X2: one axiom scratch file for all WPs makes a single failing WP block every WP.**
`AXIOMS .titan/axioms-s05.lean` imports all six modules. If any draft fails to build (expected in int1), `lfile` of the whole
file fails, so the line reads rc ≠ 0. Since "green iff CHECK_WP ok **and** its AXIOMS line rc=0 nonstandard=0" (OVERVIEW
§4.3), no WP can turn green in that round. OVERVIEW §4.3 prescribes per-WP files `.titan/<wp>_axioms.lean` (stage 1:
`s01_l16a_axioms.lean`).
*Fix:* X2 generates one axiom file per WP line, plus one combined file for G1/G2 (`Audit/PrintAxioms.lean` rows). Spec:
`AXIOMS .titan/s05_l1_axioms.lean` … .

**A5 (maj) L2 `CharGroupData`, L4: the "relations of `lem:s05-consistency`(a)" field cannot be stated, or it makes L4 a hard
proof.**
Lemma (a) needs `T_ℓ² − T_{ℓ²} = ℓ⟨ℓ⟩` and `U_q² = ⟨q⟩`. `HeckeSym` has no `T_{ℓ²}` symbol, so the first relation cannot
be written. For the canonical instance (L4, "mechanical-with-meaning, sonnet, 10 min active"), the field requires a proof
that the square of right translation by `Π_q` equals `theta (dia q)` on `degZero`. This is a global–local idele argument
(`Π_q² ∈ q·O_q^×`, q ∈ ℚ^× acting trivially), and no stage-1 lemma covers it. The tex places (a) "on the image in
End X_q(J_s) ⊗ ℚ"; it is a consequence, not data.
*Fix:* drop the relations field. They follow from (X1) for any G and can be stated as a theorem later. Alternatively, keep
only `U_q² = ⟨q⟩`, add a lemma `PiEllHom_sq` to L1 (opus), and re-rate L4.

**A6 (maj) L3 `Hyp.X.gal` interface: the FD1 clause is type-ambiguous, and φ is not an argument.**
In (X4), the bottom piece (`T_t`) is `Hom(Z[S_s]⁰, ℤ_p(1))` with the **transpose** action, and N maps top → bottom. So
"`Frob = q • theta Uq` on the bottom piece" must be `q • (theta Uq).dualMap` (the transpose) on the Hom-piece. Read
literally as an endomorphism of `degZero`, it would typecheck only if a writer places the formula on the top piece, which is
the wrong piece. That is exactly the "a wrong choice still builds" risk (§7 R1). The tex says `Hyp.X.gal` "presupposes the
φ_s", but the plan does not say that `Hyp.X.gal` takes the family `φ` (or `G` together with `Hyp.X.char`'s witness) as an
argument. Finally, `toyTate_gal` is "at one level", while the Prop is ∀ s, so it would not witness non-vacuity of the
exported Prop.
*Fix:* write the L3 signature in the plan, `Hyp.X.gal (G) (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (S s)) (T : ∀ s, TateModuleData …)`,
with the pieces typed and the Frobenius clause stated as the transpose. L10 checklist: "Frob clause on the Hom-piece,
transpose". L4: a toy family for all s (e.g. constant / trivial filtration), or state why not.

**A7 (maj) X1 step 6 against L1–L3: a sonnet kickoff fixes the signatures of the opus/conceptual design WPs, and those
signatures are not in the plan.**
The plan does not fully declare the types of `CharGroupData`, `TateModuleData`, `HeckeSym` or `theta` (argument list
`theta d M p q s hN (Pq) hPq`, the type of `Pq`, the `hPq` predicate, `degZero` as `Submodule` or type). So X1 would
*design* them. That pre-empts the conceptual L2/L3 (opus, "design decisions whose errors are invisible to the build") with a
sonnet stub, and the stackers then depend on it. X1's acceptance "the stubs elaborate in int1" is also unobservable, because
int1 builds the drafts that replace them.
*Fix:* either write the L1–L3 signatures out in §1 (as stage 06 §0 does for `if:s06-lemD`), or replace X1 step 6 by
"L1/L2/L3 owners commit their signature skeletons first (≈ 5 min), the others stack on those". Drop or re-word the X1
acceptance.

**A8 (maj) §4 against OVERVIEW §5.3: the WP-level audits are missing.**
§5.3 requires an opus WP-level audit before merge for every `hard`/`conceptual` WP (fable for adversarial and strand audits).
Stage 05 has many such WPs: L1, L2, L3, L7, L6F, L8, M1, M2, M3, R1, C2. The plan has none (R1 covers only the
normalisation chain, and L10/M8 are milestone audits). Stage 03 does list them (`stage-03.md` "WP-level audits").
*Fix:* add a "WP-level audits" item to §4: one blind opus audit each for L2+L3 (joint, statement vs tex), L1, L7, C2 and M1/M3
(fable if E8′ runs, see A9), ~5–8 min each, off the critical path except L1–L3, which run in parallel with int1/int2.

**A9 (maj) §5 E8′: the auditor regime breaks comparability with S03's E8 and OVERVIEW §5.2.**
E8′ has "opus audits fable, fable audits opus". W0 (crit/maj/min) would then be measured by two different auditors, so the
strand comparison is confounded by auditor strictness. OVERVIEW §5.2 fixes E8 → one opus audit for both strands with the
confound noted, and `stage-03.md` l. 247 audits both E8 strands with one blind opus auditor. A conditional repeat must use the
same protocol, or the data cannot be pooled with S03. Also, "mergeable at mechanical acceptance (§4.4 rule)" points to
EXPERIMENT_PROTOCOL §4.4, not OVERVIEW §4.4.
*Fix:* use the same auditor for both strands, exactly as in S03's E8 (one blind opus, confound in LOG.md; optionally a second,
fable, for both). Cite EXPERIMENT_PROTOCOL §4.4.

**A10 (maj) TEXCHK and §6 against cross-chapter references: "no undefined refs" conflicts with the required `\ref`s, and M4 is
not self-contained.**
The M WPs must refer to `prop:s01-relations` (M1), `if:s04-ekills`/`Mord` (M3), `if:s02-*`/`if:s03-amalgam` (M7) and
`lem:s06-D` (M4). `standalone-s05.tex` loads only chapter s05, so these refs are undefined. Stage 06 runs in parallel, so
`lem:s06-D` is still undefined in `main.tex` when s05 merges, unless s06/M1 merged first. Remote WPs may use "only the stage
tex + merged mathematics + literature", but M4 needs the statement of `lem:s06-D`, which is in the **stage-06** tex.
*Fix:* `standalone-s05.tex` `\input`s the merged chapters s01–s04 (or uses `xr` against `main.aux`). References to stage-06
labels are written as text with the interface name (`if:s06-lemD`, statement quoted) until s06 is merged, and then M9
converts them. Add `plan/staged/stage-06-integral-defect.tex` (§ Lemma D only) to M4's inputs, and note it as an allowed
deviation in §6.

**A11 (min) §6 table against OVERVIEW §6.1: columns and start condition.**
OVERVIEW §6.1 requires the columns "WP id | branch | files | local fallback model". The table lacks branch
(`abhijit/s05-m1` …) and fallback model. It also does not state that remote WPs can start only after X1's drivers are merged
**and pushed** to `origin/wip-implementation` (base sha in the request), so stage-05 M WPs cannot run "stages ahead"
(OVERVIEW §7). Stage 06 lets the first remote WP create the standalone.
*Fix:* add both columns and the start condition, or adopt stage 06's rule.

**A12 (min) Per-WP bib files (notes "Assumptions" 3): acceptable, with fixes.**
The deviation from the brief's single `bib/s05.bib` is **acceptable**: it is the only way to keep 8 concurrent remote WPs
new-files-only, and stage 03 uses the same pattern. Two fixes are needed. The project uses biblatex
(`preamble.tex: \addbibresource{references.bib}`), so the guard must be
`\IfFileExists{bib/s05-m1.bib}{\addbibresource{bib/s05-m1.bib}}{}`, not `\bibliography`. M9 must de-duplicate keys
across the files when it writes `bib/s05.bib` and the `references.bib` lines.
*Fix:* as stated. The global master should record `bib/sNN-<wp>.bib` as allowed in OVERVIEW §6.1 (stages 03 and 05 use it;
stage 06 does not).

**A13 (min) §3 G1/G2 against the OVERVIEW §4.3 gate variant.**
Steps (b) `lbuild LanglandscapeVendorStacks` and (e) the `declaration uses 'sorry'` count are missing. The job ids
`s05-gate-1`/`s05-final-1` are not used. G1 is defined on `wip-implementation`, so the green WPs must be merged first, and
that merge step (~3 min) is missing from the critical path.
*Fix:* cite the §4.3 (a)–(f) list, use the job ids, and add a merge step (+3 min; path ≈ 123 min).

**A14 (min) §1 X1 against §3: file names.**
X1 writes `.titan/spec-int1.txt`, while §3 uses `.titan/spec-s05-int1.txt`. The axiom file name differs from the
`.titan/<wp>_axioms.lean` convention (see A4).
*Fix:* use one name.

**A15 (min) C2 stop rule against the L3 timing.**
C2 (35 min) ends at t ≈ 47, but L3 enters int1 at t ≈ 35. "Stops … L3 merges" can therefore only mean the merge into
`wip-implementation` or G1, not the int merge. There is no edge C2 → G1.
*Fix:* say so, and add `C2 → L3 (merge to wip-implementation)` to §2.

**A16 (min) §0 stage-1 API and cross-stage names.**
- `wx` and `negOne` are in `Langlandscape.Quat` (Quat/Basic.lean, Quat/Weights.lean), not `Brandt`.
- No `deg` exists in stage 1, so L1 must define and name it.
- Stage 04 (S04-L4, `Ordinary/EKills.lean`) also works with `deg ∘ Up = p • deg` and `ker deg` (`ordPart_ker_deg`), so a
  second `deg`/`degZero` in `Comparison` needs a bridge lemma for L7. The ekills(a) theorem name is `ordPart_ker_deg`; quote it.
- Stage 03 exports `Graph.WGraph` and `WGraph.X`, not `Graph.X`.

*Fix:* correct the names, and let L1 reuse stage 04's `deg` if it is merged.

**A17 (min) Missing declaration names.**
L2b's bridge lemma and L4's toy `Hyp.X.iso` have no names, and neither is in the headline list (the brief requires concrete
declaration names). L6's `splitting_to_c` duplicates stage-06's `NewOldData.split_iff` (S06-L1).
*Fix:* name them, and use `split_iff` instead of re-proving it.

**A18 (min) L3 Weil decision.**
`stage-04.md` l. 165 says "Dropped vs. coarse: Weil vendoring", so the "toy unless stage 04 vendored Weil" branch is moot.
*Fix:* fix it to the toy model.

**A19 (min) Fix budgets of L2, L3, M2, R1 (opus, "conceptual").**
§5.1 gives conceptual WPs no fix round, but L2 and L3 must turn green in TITAN rounds.
*Fix:* state "opus, fixes by the author in rounds, escalation to the stage master after 2 failed rounds" (§5.1 escalation
rule).

**A20 (min) Parallel-stage collisions (05 ∥ 06).**
Both stages edit `Audit/PrintAxioms.lean`, `HYPOTHESES.md`, `SORRIES.md`, `Langlandscape.lean`/`LanglandscapeTests.lean`,
`mathematics/main.tex` and `references.bib`. The plan gives no rule for the merge order or for rebasing on the other stage's
merges. TITAN load in the worst case is the 05 int round + 06 int round + 2 slots of stage 06's conditional E1′ + the
stage-06 early lane, more than 3 builds; "≤ 3 shared" holds only with ordering by the global master.
*Fix:* add this to §7 risk 5, with the global master's ordering rule.

**A21 (min) GL2TF-free rule for `CommAlg/`.**
Stage 06 enforces `grep -nP '^import (GL2TF|Langlandscape\.(?!CommAlg))'` on `CommAlg/`. Stage 05's `CommAlg/SubQuot.lean`
falls under that gate, and the plan does not say so.
*Fix:* state in §0 that the file imports Mathlib + `CommAlg.*` only. Optionally offer L6 to the early lane, since it is
Mathlib-only.

**A22 (min) `Hyp.X.char` quantifier order.**
The plan's `∃ φ : ∀ s, …` (one family) is correct, because (X3) links φ_s and φ_{s'}. It deviates from the tex Lean-track
text `∀ s, ∃ φ`, though.
*Fix:* record it as a deliberate deviation in the L2 docstring, in M3 and in the HYPOTHESES row, so that L10 does not flag it.
The L3 docstring should mark the FD1 clause "provisional (FD1)".

**A23 (min) SORRIES row placement.**
X1 step 5 ("SORRIES row for the Lemma-D stub if needed") does not say on which branch. §0 says the row is on the integration
branch only.
*Fix:* say "on `impl/s05-int<k>` only", and require no stage-05 SORRIES row on `wip-implementation`.

**A24 (min) DAG edges.**
The edge list lacks M3 → L10 (input), X2 → int1 (present in the Mermaid only), L1 → L4 (input), and the precondition
"stage 04 merged" → X1.
*Fix:* add them.

**A25 (min) Docstring gate.**
TCHK includes the check_wp docstring check with `s05-` labels, but `check_wp.sh` still hard-codes `s01-` (l. 87). The fix is
S02-X1's (OVERVIEW §4.3), and stage 05 does not verify it. The check covers only `theorem`/`lemma`, while most stage-05
outputs are `def`/`structure` (`Hyp.X.*`, `CharGroupData`, `theta`).
*Fix:* X1 step 4 greps `check_wp.sh` for the generalised regex. L10's checklist adds "def/structure docstrings with labels".

## Counts and verdict
crit 0 · maj 10 (A1–A10) · min 15 (A11–A25).

**Verdict: PASS WITH REQUIRED FIXES (revise before launch).** The plan conforms to A–F and the brief's structure. Its
labels and its stage-1 API claims are sound, and its critical-path arithmetic and calibration are correct. The defects are in
the seam mechanics and the Lean interfaces, which are exactly the places where "a wrong choice still builds":
- the stub makes L6/G1 unreachable (A1), ignores stage 06's early lane (A2) and stubs the wrong file set (A3);
- the combined axiom file blocks rounds (A4);
- the `CharGroupData` relation field (A5) and the (X4) Frobenius typing (A6) are wrong or underspecified;
- the L1–L3 signatures are left to a sonnet kickoff (A7).

The WP-level audits (A8), the E8′ auditor regime (A9) and the cross-chapter TEXCHK (A10) also need fixes. A1–A10 are
required for the final pre-launch pass. The minors may be folded into that pass.
