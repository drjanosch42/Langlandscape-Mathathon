# Abhijit node: candidate work packages (scout report, DRAFT for the global master)

Author: abhijit-scout (Opus, read-only), 2026-11-14. Not committed; the global master reviews and commits.
Sources read: CLAUDE.md; `agents/rules/{orchestration,messages,git,mathematics,lean,code,talk,resources}.md`;
`plan/staged/SPLIT.md` (stage tex files by label only); `plan/implementation/{OVERVIEW,stage-02..06}.md` (WP tables);
`agents/status/master_log.md` (tail, to 18:18); `literature/MISSING_LITERATURE.md`;
`plan/staged/audits/global-fable-seam.md` ("Items for Fabian"); the impl worktree (`mathematics/`, `code/python/`, `talk/`).

## 1. Summary
- Stage 1 is almost done on Fabian's node: the L14 gate is pending, the L15 Fable audit comes next, and the M and C/T tracks are merged into `wip-implementation`.
  Stages 02–06 have only coarse plans, and none of their WPs has started. Their **M (maths) WPs depend only on the stage-tex statements**
  (and on each stage's X1 stub). Our rules let the maths run ahead of Lean, so these are the ideal remote packages.
- Recommended: Abhijit's node writes the **stage 02–06 mathematics chapters** (one Opus agent per chapter). It also does
  **literature verification**, since it may have library access that we lack, and **light PARI computations** for stages 05/06, which keep our CPU free for HACS.
  It acts as an **independent second reader** on the q ≡ −1 step (an open decision for Fabian).
- No Lean builds there. Mathlib-only Lean drafting (S06 CommAlg, S02/S03 graph layer) becomes possible **only if** a Mathlib at
  our pinned rev can run on his node. That is open question Q1. Until then, Lean stays on our side, or the compile check runs on TITAN.
- Collisions are avoided by construction: one branch `abhijit/<pkg>` per package, branched from `origin/wip-implementation`. Each package
  writes **new files only**: chapter dirs `mathematics/chapters/sNN/`, a standalone driver, a per-stage `.bib` file, new Python subpackages and
  new result dirs. The aggregator lines (main.tex, references.bib, INDEX.md, talk/main.tex) come back as report lines.
- Blocking prerequisite: **literature/** is git-ignored and 1013 MB in 383 files. It cannot travel over git, so it needs an out-of-band copy (Q2).

## 2. Ranked candidates

Legend for models: O = Opus, S = Sonnet. "agent-h" = Claude agent wall hours (estimate, from the stage plans' minutes plus
self-check overhead). Branch base for all: `origin/wip-implementation` at the sha given in the message. "Ours" = Fabian's node.

| # | id | title | track | stage refs | inputs | outputs (files) | branch | acceptance check | est. agent-h | models | deps / blockers | collision risk |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | A-S06M | Stage-06 chapter: comm. algebra, setting, defect, Galois half | M | S06-M1, M2, M3, M4, M7; tex `stage-06-integral-defect.tex`; `if:s06-lemD`, `if:s06-defect` | stage tex 06 + SPLIT §06; imported `if:s01-targets`, `if:s01-hecke`, `if:s03-amalgam`, `if:s04-Mord`, `if:s04-etaB` (restate verbatim); literature (KO, Hs, Dia89, Hi86b, PW) | `mathematics/chapters/s06.tex` (\input list), `mathematics/chapters/s06/{commalg,setting,defect,galois,betti}.tex`, `mathematics/bib/s06.bib`, `mathematics/standalone-s06.tex`, `mathematics/chapters/s06/NOTES.md` (deviations, missing lit, open points) | `abhijit/s06-math` | `cd mathematics && latexmk -pdf standalone-s06.tex` exit 0, no undefined refs/cites; all labels of S06-M1..M4, M7 present; every result has a status tag; every `\stcited` has `\lit{file}{Thm/§/p.}`; then our Fable chapter audit (S06-M9) | 5–7 | O (S for drafting sub-parts) | literature copy; Lemma D (a)–(c) **must** keep the `if:s06-lemD` statement shape (05 imports it); Thm E needs R Gorenstein made explicit (seam #6) | none (stage 06 not started; new dir) |
| 2 | A-S03M | Stage-03 chapter: weighted graphs, Mazur, Ribet, Ihara, amalgam | M | S03-M1..M5; `if:s03-{graph,ribet,ihara,amalgam}` | stage tex 03; `if:s01-*`, `if:s02-{tree,quot,coh,indef}` (restate); Ri90, RS01, Mazur77, Serre Trees, Brown | `mathematics/chapters/s03.tex`, `s03/{graphs,eisenstein,ribet,ihara,amalgam}.tex`, `bib/s03.bib`, `standalone-s03.tex`, `s03/NOTES.md` | `abhijit/s03-math` | as #1 (labels of S03-M1..M5; `prop:s03-PsiPsi` in **one** fixed normalisation; sign of α = (−s_{0*}, s_{1*}) as SPLIT) | 5–6 | O | literature; S03-M2 (`prop:s03-phieis`, q ∈ {2,3}) is "hard": a second reading is required; Ri84 missing (lib access helps) | none |
| 3 | A-S02M | Stage-02 chapter: tree, SA (cited), BG graph, quotient, (co)homology | M | S02-M1..M4 (M4 as *sketch* until S02-C4); `if:s02-*` | stage tex 02; `if:s01-{classset,brandt,hecke}`; Serre Trees II.1–2, Voight Ch. 28 | `mathematics/chapters/s02.tex`, `s02/{tree,quotient,cohomology,remarks}.tex`, `bib/s02.bib`, `standalone-s02.tex`, `s02/NOTES.md` | `abhijit/s02-math` | as #1; sign table matches `if:s02-coh`; Voight 28.5.3/28.5.12 re-verified with page | 4–5 | O | literature; it is the critical next stage for our Lean track, so we may want it **first** | low: our S02-X1 must then skip the maths stubs (stage-02 plan edit by us) |
| 4 | A-S04M | Stage-04 chapter: ordinary projector, control, Λ-adic Ribet, Hsieh dictionary, η-principle | M | S04-M1..M5 (M6 optional) | stage tex 04; `if:s01-*`, `if:s03-*`; Hi86b, Hs, LV, Hida 1988 | `mathematics/chapters/s04.tex`, `s04/{ordinary,control,lambdaribet,hsieh,etaprinciple}.tex`, `bib/s04.bib`, `standalone-s04.tex`, `s04/NOTES.md` | `abhijit/s04-math` | as #1; Hsieh's residual condition (CR, supp N⁻) stated explicitly (mis-citation #15); factor-2 paragraph against |Γ_x| (not w_x) | 5–6 | O | literature (Helm 2007 and MW86 are missing and wanted); M5 statement must match S06-L1/S04-L10 (coordinate via NOTES) | none |
| 5 | A-S05M | Stage-05 chapter: sign/consistency, Hyp.X, subquot, no-chain, simplicial shape | M | S05-M1, M3, M4, M7 (M2, M5, M6 → #7) | stage tex 05; `if:s06-lemD` (from #1 or stage tex); Ri90, RS01, PW, Kohel | `mathematics/chapters/s05.tex`, `s05/{sign,hypX,subquot,simplicial}.tex`, `bib/s05.bib`, `standalone-s05.tex`, `s05/NOTES.md` | `abhijit/s05-math` | as #1; `hyp:s05-X` with the full data list of seed Hyp 8.1; ε convention as *provisional* (Fabian decision 1) | 4–5 | O | Fabian decision 1 (Hyp.X model) is open: write it with the recommended Ribet–Stein convention, marked `\provisional` | none |
| 6 | A-LIT | Literature acquisition + citation verification (library access) | lit | MISSING_LITERATURE high/medium items 1–21; unusable items 1–5 | `literature/MISSING_LITERATURE.md` | `mathematics/litnotes/<bibkey>.md` (exact bib data, DOI, theorem/page of every statement we cite, ≤ 15-line paraphrases, no copied text), `mathematics/litnotes/INDEX.md`; PDFs **only** in Abhijit's local git-ignored `literature/` | `abhijit/lit` | every note gives source + Thm/§/page for each use listed in MISSING_LITERATURE "Why"; bib entries compile in a `.bib` (biber check); our master spot-checks 3 notes | 3–5 (+ human time for library) | O for reading, S for bib | library access (Q3); copyright: no PDFs/scans/long quotes in git (repo goes public) | none |
| 7 | A-S06R | Independent second reader: q ≡ −1 / (Lev_M), Kim–Ota §3 Thm 3.14 | M/review | S06-M5 + S06-M6 (second-reader half); seam "Decisions" 2 and 6 | stage tex 06 `prop:s06-levM`, `rem:s06-minus1`; KO, BKM, PW | `mathematics/chapters/s06/minus1.tex` (S06-M5) and `mathematics/audits/s06-levM-abhijit.md` (verdict CONFIRMED / GAP + exact step) | `abhijit/s06-levm` | verdict per step (1)–(5) with KO page/thm; the tex compiles with the standalone driver of #1 | 3–4 | O (a different account from ours = truly independent reading) | literature (KO, BKM); Fabian decision 2 | low (`minus1.tex` belongs to #1's dir: #1 must **not** write it) |
| 8 | A-C06 | Stage-06 congruence computations (PARI): toolkit, C4(i) regression, T4 Hecke side, T5 GL₂ side | C | S06-C1, C2, C3, C4 (C5–C7 later) | stage-06 plan rows; `code/python/langlandscape/` (stage-1 package, read-only use); cypari2 | new subpackage `code/python/langlandscape/defect/` (`congruence.py`, …), `code/python/tests/test_defect_*.py`, `code/results/s06/{C4i,T4_hecke,T5_gl2}.json` (+ provenance per `code.md`) | `abhijit/s06-code` | `pytest code/python/tests/test_defect_*.py` pass; JSON with script + commit + params + date + runtime; C4(i) reproduces the seed's `v(h) = v(𝔠_q)` on the subset; T4 `length T(1)_m/(δ)` table | 4–6 | S (O for the toolkit design) | cypari2 + PARI ≥ 2.15 with `mf` on his node (Q4); RAM: level-1 k ≤ 124 and qM ≤ 70 are fine at 16 GB | low: no edits to existing modules or `__init__.py`; INDEX.md lines go in the report |
| 9 | A-C05 | Stage-05 sign/exponent checks (PARI): T05-1 (ε), T05-2 (exponent, diamonds) | C | S05-C1, S05-C2; Fabian decisions 1 and 3 (Hsieh sign) | stage-1 Brandt code (`brandt.py`, `pi_ell.py`, `up.py`), S01-C7 results (`pi_sign.json`) | `code/python/langlandscape/sign/` , tests, `code/results/s05/{T05-1,T05-2}.json` | `abhijit/s05-code` | pytest pass; T05-1: Π_q eigenvalue = +a_q pattern for q ∈ {11,23,37,43}, k ≤ 8 (or a documented counterexample); T05-2 settles `U_q ↦ +Π_q`, `⟨d⟩ ↦ ⟨d⟩⁻¹` | 3–5 | S | Q4; depends on stage-1 code API (read-only); `U_1(N)` Brandt code may not exist yet → T05-2 may need a small level extension (new module) | low |
| 10 | A-S02SA | Blueprint of strong approximation for B¹ over ℚ, S = {∞, q} | M | S02-M5 (optional); SPLIT gap; seam item 1 | Voight §28.5–28.7, Miyake 5.2.9–10 (missing → #6), Kneser, P–R Ch. 7 | `mathematics/chapters/s02/appendix-SA.tex` (steps (a)–(f), each classed finite / elementary / deep, with the Mathlib gaps named) | `abhijit/s02-sa` | compiles with the standalone driver of #3; each step cites page; our reviewer M6 | 2–3 | O | Miyake (library); conflicts with no-one; feeds post-hackathon L02.SA | low (file in #3's dir, so #3 must not write it) |
| 11 | A-TALK | Talk slides for stages 03/06 (Mazur, Ribet collapse picture, Thm E, defect numbers) | T | S03-T2, S06-T1 (S03-T1/S06-T2 once results exist) | stage tex; later the merged chapters #1, #2 and results #8 | `talk/slides/{s03-mazur,s06-thmE}.tex` (new files) | `abhijit/talk` | `latexmk` of talk/main.tex with the slide temporarily \input (or a standalone frame file) exit 0; each claim cites a label or result file | 1–2 | S | traceability: claims must point to `mathematics/` labels, so start after #1/#2 drafts; talk/main.tex `\input` line goes in the report | low |
| 12 | A-REV1 | Cross-account review of the stage-01 chapter (`mathematics/chapters/s01/*`) | review | S01 M track (merged); `def:s01-NUp` weight-2 fix (log 18:11) | `mathematics/chapters/s01/*.tex` @ base sha | `mathematics/audits/s01-abhijit.md` (findings crit/maj/min with label + line) | `abhijit/s01-review` | report lists each finding with label and a proposed fix; no edits to s01 files | 1–2 | O | s01 may still change (M7/M8 fix in progress) → review the base sha only | none (report only) |
| 13 | A-LEAN06 | *Conditional on Q1*: Mathlib-only comm. algebra in Lean (S06-L1 defs, L2 Lemma S, L3 Lemma D, L7 squeeze, L14 2×2 coker) | L | S06-L1, L2, L3, L7, L14 | stage-06 plan §0 (declaration names, `NewOldData`), Mathlib at rev `56a005855ea1…` | `lean/Langlandscape/Langlandscape/CommAlg/{Gorenstein,LemmaS,NewOld,Squeeze,TwoByTwo}.lean` (Mathlib imports only) | `abhijit/s06-lean` | his side: `lake env lean F` OK per file, no sorry/axiom; ours (gate): `tools/lbuild.sh` on TITAN | 4–6 | O | **only** if a Mathlib at our pin builds on his node (≈ 5 GB disk, 3–6 GB RAM per file); S06-L1 owns `congruenceIdeal`/`IsGorenstein` (S04-L10 imports them) | low (stage 06 not started); our stage-06 master then merges and edits the aggregators |
| 14 | A-LEANG | *Conditional on Q1*: Mathlib-only graph layer (S02-L8 bipartite multigraphs, S03-L3 two-vertex Φ, S03-L4 cyclicity) | L | S02-L8, S03-L3, S03-L4 | stage-02/03 plans | `lean/Langlandscape/Langlandscape/Graph/{BipMultigraph,TwoVertex,Cyclic}.lean` | `abhijit/graph-lean` | as #13 | 4–5 | O | Q1; S03-L1 (`Graph.WGraph`) on our side first or included here | medium: our stage-02 Lean track starts with these files → assign either here or there, never both |

Not recommended for Abhijit: anything in `lean/` that imports `AlgJL.*` / GL2TF (needs the built import, 339 MB oleans + frozen farm);
HACS work (`code/hacs/`, on Fabian's node CPU/GPU by decision); chapter audits that the plan gives to Fable (`mathematics_chapter_audit.md`,
"never two Fable agents at once anywhere"); all aggregator files; `plan/` and `agents/` (except his messages to `agents/messages/fabian/`).

## 3. Proposed first batch (starts immediately, all in parallel, 6 Opus agents + his master)
| slot | package | why first |
|---|---|---|
| 1 | **A-S02M** Stage-02 chapter | next stage of our Lean track; its statements then exist in `mathematics/` before we formalize |
| 2 | **A-S03M** Stage-03 chapter | central talk content (Ribet collapse, Mazur); independent of 02 at the tex level (restated `if:` items) |
| 3 | **A-S06M** Stage-06 chapter | largest chapter, holds the talk's punchline; Lemma D gates 05 |
| 4 | **A-S04M** Stage-04 chapter | needs the most literature care (Hsieh, Hida 1988); long |
| 5 | **A-LIT** Literature + citation notes | unblocks the M items that cite missing refs (Ri84, Hi86a, MW86, Helm 2007, Miyake, Böckle) |
| 6 | **A-S06R** Second reader, q ≡ −1 | input to Fabian decision 2 before the talk claims it; independence from our account is the point |
Second batch (as slots free up): A-S05M (after A-S06M has fixed the Lemma D shape, or directly from the stage tex), A-C06, A-C05 (if PARI is
available), A-S02SA, A-REV1, A-TALK; A-LEAN06/A-LEANG only after Q1 is answered yes.
If PARI/cypari2 is ready on his node at t = 0, swap A-S04M ↔ A-C06: A-C06 offloads CPU from our node, which is reserved for HACS.

## 4. Protocol notes
- **Base and branches.** Each package: `git fetch origin && git switch -c abhijit/<pkg> origin/wip-implementation` (sha fixed in the
  message), one worktree per package on his node, one writer per file. He **pushes only `abhijit/*` branches** (like `titan/*`),
  never `main`, `wip-*`, `impl/*`. Messages: `main`, `agents/messages/fabian/`, per `agents/rules/messages.md`.
- **New files only.** No edits to `mathematics/{main.tex,preamble.tex,references.bib}`, `code/python/langlandscape/__init__.py` or other
  existing modules, `code/results/INDEX.md`, `talk/main.tex`, `lean/**` (besides #13/#14), `plan/`, `agents/` (besides messages).
  Compile check via `mathematics/standalone-sNN.tex`: `\input{preamble}`, `\addbibresource{bib/sNN.bib}`, `\input{chapters/s01}` (for
  `if:s01-*` refs), `\input{chapters/sNN}`, `\printbibliography`. Macros missing from the preamble: `\providecommand` at the top of
  `chapters/sNN.tex` and listed in `NOTES.md` (our stage master moves them to the preamble).
- **Label discipline.** Labels prefixed `…:sNN-…`, exactly as in the stage tex (the Lean WPs cite them). Cross-stage references only
  via `if:` labels; when the exporting chapter does not exist yet, restate the interface with `\status{imported from stage NN}`
  (SPLIT convention). Seed notation unchanged; disagreements with the stage tex go to `NOTES.md`, never silent fixes.
- **Report.** On completion of a package: push `abhijit/<pkg>`, then a `type: report` message: branch + head sha, files, acceptance
  output (latexmk/pytest tail), the aggregator lines to add (main.tex `\input`, bib merge, INDEX.md, talk \input), open points.
- **Review and merge on our side.** The global master fetches `abhijit/*` and checks the acceptance itself (latexmk/pytest). It hands the
  branch to the stage-NN master when stage NN starts, or merges early into `wip-implementation` if the stage is idle. That master
  applies the aggregator lines and runs the plan's chapter audit (Muse pre-pass + Fable, S0N-M6/M7/M8/M9). Audit fixes go back to
  Abhijit as a `request`, or are applied by us if he is busy (state which in the request). Our stage-02..06 plans must mark these M WPs
  as "delivered remotely", and S0N-X1 must skip the maths stubs. **This plan edit is ours, on wip-plan.**
- **Lean.** No Lean builds on his node unless Q1 = yes. All compile checks for Lean files from him run on our side (TITAN via the global
  master, batched). Mathlib-only files are the only allowed Lean deliverables. Frozen rules apply: no `lake update`, no manifest edits, never
  `lake` against `lean/Langlandscape/` (its wrappers need our farm).
- **Cadence.** His master polls `agents/messages/abhijit/` at session start, after each package report, and at least every 30–60 min. A
  Haiku poller is allowed. Ours does the same for `agents/messages/fabian/` at every heartbeat (30 min). Batch requests (one message per
  batch, not per package), because round trips take minutes to hours. High-priority messages (e.g. a convention change that affects his
  drafts) get `priority: high`, and he checks those first.
- **Conventions changes.** If stage-1 work changes an `if:s01-*` statement or a convention (N_Up, w_x, sign of α), our master sends an
  `info` with the commit sha. He rebases or merges `origin/wip-implementation` into the affected `abhijit/*` branches (merge, no force-push).
- **Quota.** At most 6 concurrent Opus workers + his master (within his 5–8). Fable is not used on his node (Fable audits stay ours; rule
  "never two Fable agents at once anywhere").

## 5. Open questions
For **Fabian**:
- Q2 **Literature transfer**: the 383 PDFs (1013 MB) cannot go through git (git-ignored, copyright, public repo). Options: (a) a private
  Google Drive folder shared with Abhijit, which would be a new rclone use outside `gdrive:dev/Langlandscape/` and needs your OK; (b) Abhijit
  fetches through his own library access by filename list; (c) a minimal subset per package (≈ 15–25 files each). Recommendation: (c) via
  (a), or (b) if he has full library access.
- Q5 Approve that remote branches `abhijit/*` may be pushed to `origin` by Abhijit's master (analogous to `titan/*`), and that stage
  02–06 M WPs are re-assigned "remote" in the stage plans (S0N-X1 skips the maths stubs).
- Q6 May his drafts adopt the **provisional** recommendations for your open decisions (Hyp.X with Ribet–Stein conventions; q ≡ −1 under
  (Lev_M) with M = 1 proved; Hsieh's sign as erratum; keep (Im))? Proposed: yes, marked `\provisional`, as in the stage tex.
- Q7 Do you want A-S02M first (our Lean critical path) even though it partially overlaps the planned S02-X1 kickoff?
For **Abhijit**:
- Q1 Can your node host Mathlib at our pin (`leanprover/lean4:v4.35.0`, mathlib rev `56a005855ea1…`; ≈ 5 GB disk, 3–6 GB RAM for
  single files)? If yes, packages A-LEAN06 / A-LEANG become possible; the setup is done by you (a human), not by agents.
- Q3 Which libraries/databases can you reach (MathSciNet, SpringerLink, AMS Memoirs, Numdam, Astérisque, LNM)? Priority list:
  MISSING_LITERATURE items 1–7 (Casselman 1973, HPS 1989, Miyake 1989, Ribet ICM 1984, Hida 1986a, SGA 7 IX, Helm 2007), then 15, 21
  (Mazur–Wiles 1986, Böckle 2007).
- Q4 Do you have TeX Live with biblatex + biber (needed for every M package) and Python ≥ 3.10 with cypari2 / PARI ≥ 2.15 incl. `mf`
  (needed for A-C05/A-C06)?
- Q8 Do you want to take any of the open mathematical decisions jointly (seam "Decisions that are yours" 1–6)? A-S06R is designed to
  feed decision 2.

## 6. DRAFT first message to Abhijit's inbox
File: `agents/messages/abhijit/20261114-HHMMSSZ_fabian_kickoff-batch1.md` (fill the time and `<BASE_SHA>` on sending; first push
`wip-implementation` so that `origin/wip-implementation` = `<BASE_SHA>`).

```markdown
---
id: 20261114-HHMMSSZ_fabian_kickoff-batch1
from: fabian/global_master
to: abhijit/global_master
type: request
re:
priority: high
---
Welcome to Langlandscape (Jacquet–Langlands over ℚ: definite quaternion algebras, trees, Ribet, Λ-adic, integral defect).
Fabian's node runs stage 1 (Lean nearly complete). Please take the **mathematics chapters of stages 02–06** plus literature
work, all in parallel with us. No Lean builds on your node (see Q1).

READ FIRST (in this order): `CLAUDE.md`; `agents/roles/global_master.md`; `agents/rules/{messages,git,orchestration,mathematics,
code,talk,frozen}.md`; `plan/staged/SPLIT.md` (conventions, notation, interfaces: binding); `plan/implementation/OVERVIEW.md`
§1, §6; the stage plan rows of your packages in `plan/implementation/stage-0N.md` (M rows); the stage statements in
`plan/staged/stage-0N-*.tex` (binding: labels, statements, status tags); `plan/staged/audits/global-fable-seam.md`
(section "Items for Fabian"); `literature/MISSING_LITERATURE.md`; as a style model the merged stage-01 chapter
`mathematics/chapters/s01.tex` + `mathematics/chapters/s01/*.tex` on `origin/wip-implementation`.

BASE: every package branches from `origin/wip-implementation` @ <BASE_SHA>:
`git fetch origin && git switch -c abhijit/<pkg> <BASE_SHA>`, one worktree per package. Push **only** `abhijit/*` branches.
Messages to us: `agents/messages/fabian/` on `main` (procedure in messages.md).

RULES FOR ALL PACKAGES
- New files only. Never edit `mathematics/{main.tex,preamble.tex,references.bib}`, `talk/main.tex`, `code/results/INDEX.md`,
  existing Python modules, `lean/`, `plan/`, `agents/` (except your messages). Aggregator lines go into your report.
- Maths compile check: `mathematics/standalone-sNN.tex` = `\documentclass[11pt]{amsart}\input{preamble}
  \addbibresource{bib/sNN.bib}\begin{document}\input{chapters/s01}\input{chapters/sNN}\printbibliography\end{document}`;
  `cd mathematics && latexmk -pdf standalone-sNN.tex` exit 0, no undefined references or citations; `latexmk -c`; commit no PDFs or aux files.
- Labels exactly as in the stage tex (`…:sNN-…`); cross-stage refs only via `if:` labels (restate imports with
  `\status{imported from stage NN}`). Seed/SPLIT notation unchanged. Disagreements go to `mathematics/chapters/sNN/NOTES.md`
  (and Risks), never silent fixes. Every result has a status tag; every `\stcited`/`\stknown` carries `\lit{<file-stem>}{Thm/§/p.}`,
  verified in the PDF. Missing macros: `\providecommand` at the top of `chapters/sNN.tex`, listed in NOTES.md.
- Fabian's open decisions: use the PROVISIONAL recommendations of the seam audit (Ribet–Stein conventions for Hyp.X; q ≡ −1 only
  under (Lev_M), M = 1 the proved case; Hsieh's sign as erratum; keep (Im)), marked `\provisional`.
- Copyright: no PDFs, scans or long quotations in git (the repository goes public with history). Literature stays in your local,
  git-ignored `literature/`.
- No Fable on your node (our Fable audits the chapters afterwards). ≤ 6 concurrent Opus workers.

BATCH 1 (parallel; details and acceptance in agents/status/abhijit_candidates.md §2 on main)
1. `abhijit/s02-math`: stage-02 chapter = S02-M1..M4 (M4 `rem:s02-torsion` as *sketch*). Files `mathematics/chapters/s02.tex`,
   `mathematics/chapters/s02/{tree,quotient,cohomology,remarks}.tex`, `mathematics/bib/s02.bib`, `mathematics/standalone-s02.tex`, `NOTES.md`.
   Do not write `s02/appendix-SA.tex` (reserved for a later package).
2. `abhijit/s03-math`: stage-03 chapter = S03-M1..M5; `s03/{graphs,eisenstein,ribet,ihara,amalgam}.tex` (same pattern). `prop:s03-PsiPsi`
   in one fixed normalisation; S03-M2 needs a careful second pass.
3. `abhijit/s06-math`: stage-06 chapter = S06-M1..M4, M7; `s06/{commalg,setting,defect,galois,betti}.tex`. Lemma D (a)–(c) keeps the
   `if:s06-lemD` shape (stage 05 imports it); make "R Gorenstein" explicit in Thm E. Do not write `s06/minus1.tex` (package 6).
4. `abhijit/s04-math`: stage-04 chapter = S04-M1..M5; `s04/{ordinary,control,lambdaribet,hsieh,etaprinciple}.tex`. State Hsieh's residual
   condition (CR, supp N⁻) explicitly; factor 2 is relative to |Γ_x|, not w_x.
5. `abhijit/lit`: literature acquisition + citation notes for MISSING_LITERATURE items 1–7, then 15, 21, then "unusable" 1–5:
   `mathematics/litnotes/<bibkey>.md` (exact bib data, DOI, and the theorem/page for every use in that list's "Why", short paraphrase)
   + `mathematics/litnotes/INDEX.md`. PDFs stay local only.
6. `abhijit/s06-levm`: independent second reader of the q ≡ −1 argument: write S06-M5 (`s06/minus1.tex`: `prop:s06-levM` in 5 steps,
   `rem:s06-minus1`, which M > 1 satisfy (Lev_M)), and audit step (4) against Kim–Ota §3, Thm 3.14 (level N⁺_{ρ,Σ⁺}N⁻, P_ρ̄, U_ℓ vs
   anemic algebra) in `mathematics/audits/s06-levM-abhijit.md`: verdict CONFIRMED / GAP per step with KO page and theorem number.

REPORT per package: push the branch, then a `type: report` to `agents/messages/fabian/` with branch + head sha, the file list, the
latexmk tail, aggregator lines (`\input{chapters/sNN}` for main.tex; the bib entries to merge), and open points. We fetch the branch,
re-run the check, merge into wip-implementation and run our chapter audit, and send fixes back as a `request`.

PLEASE ANSWER FIRST (type: answer, re: this id): Q1 can your node host Mathlib at our pin (lean4 v4.35.0, mathlib 56a005855ea1…)?
Q3 which libraries can you reach? Q4 TeX Live with biblatex+biber, and Python + cypari2/PARI ≥ 2.15 with `mf`? Literature: we will
send <TRANSFER METHOD, see Q2> for the files each package needs. Check this inbox at least every 30–60 min.
```
