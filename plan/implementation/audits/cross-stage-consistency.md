# Cross-stage consistency pass (stages 02–06, after all replan audits were resolved)

Integrator: Opus, 2026-11-14, worktree `…-wt/plan`, branch `wip-plan` (base 2b666d2). Inputs: `briefs/replan-s02-06.md`,
`OVERVIEW.md`, `stage-02..06.md`, `audits/{overview,stage-0N}-replan-{notes,audit,resolution}.md` (every "Cross-stage items" /
"Actions outside plan/" list), `EXPERIMENT_PROTOCOL.md`, `tools/`. Binding re-planning master decisions applied as given in the
task (S02 trivial coefficients / S03-L14; S06 owns `congruenceIdeal`/`IsGorenstein`, S06-L17, S06-L8a, no `Hyp.HsiehEta`; one
E1′ per project, S04 first; `if:s06-lemD` = `stage-06.md` §0 rev. 2; S06 early lane by stage 03, merged by the global master at a
stage boundary before the stage-05 kickoff; S02-X1 does all tool fixes). Nothing outside `plan/implementation/` was edited; no
Lean was built. Status: **done** = edited here; **ok** = checked, no change needed; **flag** = left open (see the last column).

## Edits and checks
| # | item | files | change made | status |
|---|---|---|---|---|
| 1 | S02→S03 re-bind (S02 res. item 1) | `stage-03.md` §0.4, header | `Tree.s0/s1 d q hq U`, `s0_mk/s1_mk`, `BGConnected d q hq U hU`, `BGConnected_of_SA_HS (hSA) (hHS) (hBT) (hU : IsQAdmissible)`, `heckeTHom_comm_s{0,1}Push`, `varpi_comm_s1Pull`, `finrank_H1_of_connected` any `[IsDomain R]`, `range_boundary_of_connected` any `CommRing R` (`= ker aug`), `BipMultigraph.Connected`, `EdgeO q`, `XindefR` without `hU`, partial-export timing; bound to S02 rev. 3 §4.1 | done |
| 2 | S03-L2 inputs | `stage-03.md` L2 | uses stage 02's `range_boundary_of_connected` and `finrank_H1_of_connected` (own proof only as fallback) | done |
| 3 | S03-L9 SA version | `stage-03.md` L9 | `…_of_SA_HS` via the exported `Tree.BGConnected_of_SA_HS` (no longer "if exported") | done |
| 4 | S03-L14 inputs | `stage-03.md` L14 | + `s1Level`, `relIndex_U0q_ne_zero`, `relIndex_s1Level_ne_zero`, `finite_XB_U0q`, `alphaElt_inv_conj_mem`, `s0Tr_apply_mk`, `s1Tr_apply_mk`, the `s1Tr` definition | done |
| 5 | S03-X1 worktrees (S02 res. item 2) | `stage-03.md` X1 | plain `git worktree add … $BASE_S03`, no `new_wp.sh` | done |
| 6 | TITAN job ids (O16) | `stage-03.md` §3.2; `stage-04.md` X3, §4; `stage-05.md` §3 | `s03-gate1-1`, `s03-final-1`; `s04-gate-1` → `s04-gate1-1`; `s05-gate-1` → `s05-gate1-1`; S02/S06 already conform | done |
| 7 | E8 brief name / protocol note | `stage-03.md` §5.1, §5.2 | brief `experiments/briefs/s03-m2.md` (`m2.md` is S01-M2's); protocol §2.4 line applied | done |
| 8 | S03→S04 Ribet (S03 res. item 3, S04 A10) | `stage-04.md` §0.3, L12, risk 4 | `Ribet.ribet_exact (R)` is over any `CommRing R`: L12 instantiates `R = ℤ_[p]`, `ribet_exact_baseChange` only as fallback; names `Graph.WGraph`, `WGraph.X` (alias `Graph.X`), `Graph.PhiComb`, `Ribet.DRgraph`, `Ribet.alphaV`/`CoeffData` bound | done |
| 9 | S02→S04 connectivity (S04 A9) | `stage-04.md` §0.2, L12; `stage-02.md` §4.1 | stage 02 **does** export `BGConnected_of_SA_HS` (with `hBT`); L12/L13b argument `∀ s ≥ 1, Tree.BGConnected … (Tree.isQLevel_Utower hqN)`; new S02 export row `isQLevel_Utower`, `NrdSurj`, `nrdSurj_Utower` (consumer S04); Hecke row consumer + S04-L12 | done |
| 10 | S03→S04-L15a (S03 res. item 4) | `stage-04.md` L15a | input `Ribet.CoeffData`/`alphaV` (same `brandtModule U R V ρ`); optional clause (b) of `thm:s03-iharaH0` | done |
| 11 | S04→S05 `deg`, `ordPart_ker_deg`, `ekillsA_tower`, `hdec` (S04 A11, S05 item 5) | `stage-04.md` L4; `stage-05.md` §0 | S04-L4 declares `Ordinary.deg X R : (X →₀ R) →ₗ[R] R`; S05 seam: `ordPart_ker_deg` (`EKills.lean`), `Ordinary.ekillsA_tower` (`Tower.lean`, int3), `hdec : Hyp.PadicOrdDecomp` caveat, `Mord` needs S04-int4 | done |
| 12 | `Hyp.HsiehGor` text | `stage-04.md` §0.4 vs `stage-06.md` §0 | byte-identical signature; no `Hyp/HsiehGor.lean`/`HsiehEta` in any S04 spec line; no S04 file imports `CommAlg.*` | ok |
| 13 | S06→S05 `if:s06-lemD` (S06 X-1a,b,c,e) | `stage-05.md` §0, L6F, L8 | seam block replaced by the rev.-2 content: `≃ₗ[A]` + `_apply`/`_smul`, exact `split_iff` signature (no `tf_*`), (c) names, `S` not local; L6F writes the full block; L8 uses `_smul` for T-equivariance | done |
| 14 | S06→S05 job names, hand-over (S06 X-1d, S05 item 4) | `stage-05.md` §0 states 1–2, DAG, Mermaid, risk 4, Q4; `stage-06.md` X0, §3.1, Q1 | `s06-eint1`/`s06-egate-1` → `s06-int1…int4`/`s06-gate1-1`; global master merges `impl/s06-early` at a stage boundary, at the latest before S05-X1; outbox `<UTC>_s06-early-handover.md`; S06 X0 "start by stage 03"; S06 Q1 answered | done |
| 15 | S06 int5 spec | `stage-06.md` §3.2 | missing `AXIOMS .titan/s06_l8a_axioms.lean` added (L8a registers 9 `Hyp` defs + `Setting`) | done |
| 16 | S03→S06 Betti (S03 res. item 7) | `stage-06.md` M7 | `if:s03-amalgam`: only `det(Ψ*Ψ)` and `coker(Ψ*Ψ)_𝔪`, assignment per S03 §0.2.8 | done |
| 17 | Tools only in S02-X1 | `stage-04.md` X1, §0.5; `stage-05.md` TCHK, X1 step 4 | S04/S05 no longer edit `check_wp.sh` (`s0[1-6]-` → S02's `s[0-9][0-9]-`, grep and report only); S03/S06 already check-only | done |
| 18 | Axiom files one per WP (O15) | `stage-04.md` X2, §3 table; `stage-05.md` TCHK, X2 | S04 per-round `axioms-s04-int<k>.lean` → `.titan/s04_<wp>_axioms.lean` via `gen_axioms.py`; haiku X2 of S04/S05 return text, the stage master writes the files (§9.2) | done |
| 19 | Spec-file name | `stage-05.md` X1, §3 | `.titan/spec-s05-int<k>.txt` → `.titan/spec-int<k>.txt` (OVERVIEW template, S02/S03/S06) | done |
| 20 | Rebase rule (O5) | `stage-04.md` §3 | "rebase onto the current integration tree" → fixed upstream heads or `impl/s04-int<k>~1`, never the `.titan/` commit | done |
| 21 | Model column vs §5.1 | `stage-04.md` X1 | kickoff haiku → sonnet (+1 opus fix ≤ 2), as S02/S03/S05/S06 (haiku = copy/vendoring only) | done |
| 22 | Remote tables vs §6.1 O13 | `stage-04.md` §6, M8; `stage-05.md` §6 | per-WP `abhijit/s0N-mK` → package `abhijit/s04-math`, `abhijit/s05-math` (single-WP: S04-M5, M8; S05-R1); S04-M8 output `mathematics/audits/…` → `mathematics/litnotes/s04-m4-second-reader.md` (allowed new file) | done |
| 23 | Per-WP bib files (S03 item 8, S05 item 1) | `OVERVIEW.md` §6.1 | allowed variant `bib/sNN-<wp>.bib`, loaded by name, merged by the M closure WP | done |
| 24 | Tool items timing (S02 item 5) | `OVERVIEW.md` §4.3 | S02-X1 step 1 commits on `wip-implementation` before any S02 branch; `int1` verifies live; later stages never edit tools; counter in `tools/axcount.sh`, counts `does not depend on any axioms` | done |
| 25 | Merge order early lane / parallel stages (S05 item 2, S06 X-4b) | `OVERVIEW.md` §4.3 | new bullet: priority 3 early lane; global master merges at a stage boundary before S05-X1; next `int1` = merge gate; parallel stages: priority 1 first, merge order = order of green gates, later stage rebases, aggregator lines only | done |
| 26 | Strands (S04 A12, S06 X-4d, S03 item 2) | `OVERVIEW.md` §5.2 | rows S04 E1′ (L6), S05 E8′ (M3), S06 E1′ (L5b); one-E1′ rule; E8/E8′ override of protocol §2.4; E1 deadline | done |
| 27 | §7 table (all stages) | `OVERVIEW.md` §7, header, §2 | final WP counts, critical paths and walls of all stages; "provisional" removed; worktree-cap note (Q6) | done |
| 28 | Protocol §2.4 (S03 item 2) | `EXPERIMENT_PROTOCOL.md` | E8 override: one planned opus fix regardless of W0, `failed` if r1 fails; fable no fix | done |
| 29 | Protocol §2.3, §5, §6 (S02 item 4) | `EXPERIMENT_PROTOCOL.md` | Lean `check.txt` = `EXP_NO_CHECK=1` + strand `summary.txt`; briefs `sNN-<wp>.md`; `stop reason=deadline`; TITAN wait as `build s=;queue=;job=`; neutral merge message `<area>: merge SNN-<wp> (strand <letter>)`, squashed stacking import | done |
| 30 | `exp_prepare_audit.sh` (S02 item 3) | `tools/exp_prepare_audit.sh`, `tools/exp_lib.sh` | all eight `s01` edits of the S02 resolution; **beyond it**: case list keyed on `$st-$wp` (S03-M2 would otherwise be typed as S01-M2 "LaTeX routine"), rows s02-l1, s02-m1, s03-m2, s04-l6, s05-m3, s06-l5b; brief path `briefs/$st-$wp.md` with fallback `briefs/$wp.md`; `bash -n` ok | done |
| 31 | S02 brief names / exports note | `stage-02.md` X1 step 3, step 5, §4.1 | briefs `s02-l1.md`, `s02-m1.md`; outbox note `…_s02-exports-for-s03.md` at X1 step 5; "names bound by S03/S04, keep stable" | done |
| 32 | S05-L2b DR graph level | `stage-05.md` L2b | `Ribet.DRgraph d` exists only at `d.Ohat` (S03 §0.2.5) but L2b needs level `S s`: L2b builds the two-vertex `WGraph` on `XB (S s)` itself or restricts to `d.Ohat` | flag (decide at S05 final pass) |
| 33 | S05 L1–L3 fix budget | `stage-05.md` L1–L3 | "fixes by the author in rounds, escalation after 2 failed rounds" vs §5.1 "+1 planned opus fix"; accepted in S05 res. A19 (two rounds are already costed in the critical path) | ok (recorded deviation) |
| 34 | Single-WP remote branches writing `NOTES.md` | `stage-03.md` M7, `stage-05.md` R1 | §6.1 names `litnotes/*` for single-WP branches; both WPs are the sole writer of `chapters/sNN/NOTES.md`; deviation recorded in the stage plans | ok (recorded deviation) |
| 35 | Gates per stage | all stage files | early gate (S02 L11, S03 gate-1, S04 X3, S05 G1, S06 gate1 early + gate2), Fable Lean ∥ chapter audit (S02 L12∥M6, S03 L12∥M8, S04 L16∥M9, S05 L10∥M8, S06 L18 early, L12∥M9), final from scratch (L14, final-1, X4, G2, L16) | ok |
| 36 | Remote tables vs §6.1 exclusions | all stage files | no strand, Fable audit, audit-fix or code-input M WP is tagged; every stage states "launchable without Abhijit" | ok |
| 37 | S04 header "upstream by label only" | `stage-04.md` header | now also cites S02/S03 WP ids for re-bound names; harmless (plans are final) | ok |

Count: **30 edit items** (status *done*) touching 9 files (`OVERVIEW.md`, `EXPERIMENT_PROTOCOL.md`, `stage-02..06.md`,
`tools/exp_prepare_audit.sh`, `tools/exp_lib.sh`); 6 checks without change (rows 12, 33–37); 1 flag (row 32).

## Actions outside plan/ for the global master
1. **F18 rule edits on `main` (launch condition of S02):** (1) `agents/rules/resources.md` TEMPORARY job flow → file outbox,
   plus the Abhijit node row and 16 GB budget (≤ 4 agents, ≥ 3 GB free); (2) `agents/rules/git.md`: area `plan`, branch
   `wip-implementation`, families `impl/ exp/ titan-in/ titan/ abhijit/`; (3) opencode/muse/mistral marked "not used as
   implementer" in `agents/roles/global_master.md`, `agents/roles/coordinator.md`, `CLAUDE.md` (Tooling line); (4)
   `agents/rules/lean.md` l. 22: docstring rule of OVERVIEW §3.6 (every theorem/lemma incl. private and tests, label `s<NN>-…`);
   (5, optional) `briefs/common.md` l. 31 note "superseded by OVERVIEW header".
2. **Tool items (S02-X1 step 1, `lean/Langlandscape/tools/`, committed on `wip-implementation` before any S02 branch):**
   `check_wp.sh` `s[0-9][0-9]-` (tests not exempt); new `axcount.sh` + `titan_batch.sh` AXIOMS line (printed/expected/
   nonstandard, `does not depend on any axioms` counted); vendor path mapping (`Vendor/AxiomStacks/`). S02-X2:
   `tools/gen_axioms.py`. Optional: widen `tools/new_wp.sh` (stage argument, no seeding without `.lake/build`); no plan needs it.
3. **Merge `wip-plan` → `main`** before S02 launch (it now carries the generalised `exp_prepare_audit.sh` and the protocol
   edits = S02 launch checklist item 3); fast-forward `…-wt/impl`; remove the `plan` worktree (≤ 3 live worktrees at launch).
4. **S06 early lane:** give the OK for S06-X0 no later than the stage-03 kickoff; merge `impl/s06-early` at a stage boundary
   (after `s06-gate1-1` + L18 PASS), at the latest before S05-X1, aggregator lines in the merge commit.
5. **Outbox note to stage 03** (`plan/implementation/outbox/<UTC>_s02-exports-for-s03.md`, written by the S02 stage master at
   X1 step 5): points to `stage-02.md` §4.1 and to the re-bound `stage-03.md` §0.4 (row 1 above).
6. **Stage 03/04/05/06 final passes before their launch:** S05-L2b level decision (row 32); write the int1/int2 spec files out;
   reconfirm names against the merged tree.
7. Abhijit (`agents/messages/`): no WP is remote until Q5 (transport of `abhijit/*`) and Q2 (literature) of the scout are
   settled; package branches are `abhijit/sNN-math`.

## Open questions for Fabian (deduplicated; defaults in brackets; every stage launches on the defaults)
- **Q-A (FD1, S05-Q1; needed before S05-L3 merges):** μ_N-model with Picard functoriality for Hyp.X (`Frob_q = qU_q`)? [yes]
- **Q-B (FD2, S05-Q2):** Hsieh's `JL(U_q) = −U_q` an erratum, not imported; write to the author? [erratum; no letter for now]
- **Q-C (remote node; S02-Q4, S03-Q5, S06-Q2, S06-Q4, OVERVIEW §6.1 O12c):** transport of `abhijit/*` and literature copy;
  packages per stage; S06-M6 on Abhijit's node; code WPs stay local. [all local until settled; then packages `abhijit/sNN-math`,
  S06-M6 remote preferred, code excluded]
- **Q-D (strands; S02-Q1, S03-Q2, S06-Q5):** E1 on S02-L1 with deadline D; E8 merge rule (passing strand merged, Fable may
  replace §2); one E1′ per project (S04-L6 first, S06-L5b only if undecided). [all yes]
- **Q-E (no new vendoring; S03-Q1, S04-Q5):** drop Stacks Frontier and Weil vendoring. [drop]
- **Q-F ("formalized modulo"; S04-Q1, S04-Q4, S05-Q3, S05-Q4, S06-Q3):** `Hyp.MordLambdaFree`; ℤ_p tower modulo
  `Hyp.PadicOrdDecomp`; `HeckeSym` without `U_ℓ` (ℓ ∣ M) if needed; S05-L6 may carry into stage 06; Gorenstein base change
  L13 required. [all yes]
- **Q-G (scope; S03-Q3, S03-Q6, S04-Q3, S04-Q6, S02-Q3, S02-Q5):** level-1 Eisenstein only; L14 coefficient scope without
  Hecke; L15a/b as ext with schematic `HidaControl` fallback; S04-M7 optional; full `Hyp.BTtree` shape; no `BGConnected`
  certificate. [all as stated]
- **Q-H (infra; S02-Q6, S03-Q4):** raise the worktree cap to 16 for `.lake`-free worktrees; stage-03 Mathlib-only graph WPs
  early during stage 02. [keep 12; no S03 early start (TITAN slots are full with the E1 pair)]
- **Q-I (F5):** licence choice (`THIRD-PARTY-NOTICES.draft.md`). [open, not blocking]
