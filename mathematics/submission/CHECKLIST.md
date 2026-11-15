<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Submission rules checklist

Source: the submission brief of the global master (2026-11-15). Run from `mathematics/submission/`.
`AUTO` items are computed by `python3 tools/flatten.py --check report.tex [--build]` (id in brackets); `MANUAL` ones need eyes.
Status: `[ ]` open, `[x]` verified (initial and date when ticking).

## A. Report (one self-contained `report.tex` + `report.pdf`)
| # | Requirement | How to check | Status |
|---|---|---|---|
| A1 AUTO | Single file: no `\input`, `\include`, `\subfile`, `\addbibresource`, `\bibliography`, `\printbibliography`, `\includepdf`, `\includegraphics`, biblatex, pdfpages | `python3 tools/flatten.py --check report.tex` (A1); by hand: `grep -nE '\\(input\|include\|addbibresource\|bibliography\|includepdf\|includegraphics)\b' report.tex` must be empty | [ ] |
| A2 AUTO | Bibliography inside as `\begin{thebibliography}`; no `.bib` | `--check` (A2); `grep -c 'begin{thebibliography}' report.tex` = 1 | [ ] |
| A3 AUTO | One `\documentclass`, one `\begin{document}` | `--check` (A3) | [ ] |
| A4 AUTO+MANUAL | No images; every figure/tikzpicture described in words (caption >= 12 words or adjacent paragraph) | `--check` (A4); `python3 tools/flatten.py src/report-src.tex` lists every figure on stderr; read each | [ ] |
| A5 AUTO | Title block (title to `\maketitle`): both authors, affiliations, repository link, FULL 40-hex commit hash, no placeholders | `--check` (A5); `sed -n '/\\title/,/\\maketitle/p' report.tex` | [ ] |
| A6 AUTO | Nothing identifying outside the title block: names (Fabian, Januszewski, Abhijit), node names (TITAN, CONCEPTD), GitHub users, e-mails, affiliations (Paderborn, ...) | `--check` (A6, word list in `flatten.py` `IDENT_WORDS`, extend with `--idword`); also `pdftotext report.pdf - \| grep -inE 'fabian\|janusz\|abhijit\|titan\|conceptd\|github'`; note the NVIDIA/DFG acknowledgment wording names Fabian (decision needed from the master) | [ ] |
| A6b MANUAL | PDF metadata and hyperref `pdfauthor` empty/neutral | `pdfinfo report.pdf`; `grep -n 'pdfauthor\|hypersetup' report.tex` | [ ] |
| A7 AUTO | Sections 1-13 present in order: 1 Abstract, 2 Introduction+motivation, 3 Setup+definitions, 4 Our question (the integral Hecke-equivariant map (a)-(e), why a map beats a trace identity), 5 Why the BT-tree route, 6 Proof outline stage by stage, 7 Main results with support status, 8 Lean, 9 Computations (what, over what range), 10 Work in the 40-hour event vs prior work, 11 AI use, 12 Sources+acknowledgements, 13 Limitations+next steps | `--check` (A7: heading keywords; edit `SECTION_PATTERNS` if headings are renamed); `grep -n '\\section' report.tex` | [ ] |
| A8 AUTO | Scope statement: JL holds for every inner form of GL(2) over every number field (also GL(n)); we do only Q and only DEFINITE quaternion algebras (not "anisotropic") | `--check` (A8); `grep -n -i 'inner form\|number field' report.tex` | [ ] |
| A9 AUTO+MANUAL | Each main claim carries its status: proved / Lean-verified / Lean-conditional on named hypotheses / computed (range) / cited / conjectural; no upgrades | `--check` (A9 counts markers); MANUAL: compare every claim in section 7 with `mathematics/chapters` and the Lean table | [ ] |
| A10 AUTO | Problem text quoted VERBATIM in the introduction, with both references (JL LNM 114, doi:10.1007/BFb0058988; Bergeron Ch. 8, doi:10.1007/978-3-319-27666-3_8) | `--check` (A10, letter-level comparison); eyeball the typography | [ ] |
| A11 AUTO | No unresolved placeholders: `\TODOFACT{...}` (section 10 facts from Fabian), TODO, FIXME, `\provisional`, `???`; commit hash filled by the master last | `--check` (A11); `grep -n 'TODOFACT\|TODO\|provisional' report.tex` | [ ] |
| A12 MANUAL | (a)-(e) each mapped to stage, status, and what is open (b: Chenevier only cited/remarked, rem:s05-O7) | read section 4 | [ ] |
| A13 MANUAL | AI-use section: tools actually used (Claude Code Opus/Sonnet/Haiku/Fable; opencode Mistral Large 4, Muse Spark Open, Q&A plus the one disclosed RamNrdSurj draft; PARI/GP, SageMath?), what for, how checked | compare with `docs/agentic-process/` and `agents/rules/model-selection.md` | [ ] |
| A14 MANUAL | Acknowledgment wording exactly as `mathematics/acknowledgments.tex`; HACS v0.2.1, hacs-data v0.2.0, trace-formula project (~170k lines, ~30k imported), Stacks/Mathlib vendored code named | `grep -n -i 'hacs\|stacks\|NVIDIA' report.tex` | [ ] |
| A15 AUTO | Compiles from `report.tex` ALONE: pdflatex x2, no errors, undefined references/citations, multiply defined labels, missing files | `python3 tools/flatten.py src/report-src.tex` (S1, done automatically); or `--check report.tex --build` | [ ] |
| A16 AUTO | No `??` in the PDF text | `--check report.tex` (S2); `pdftotext report.pdf - \| grep -c '??'` | [ ] |
| A17 MANUAL | `report.pdf` is built from the committed `report.tex`; both committed on the submission branch; PDF size sane | `ls -l report.tex report.pdf; git status` | [ ] |

## B. Lean section
| # | Requirement | How to check | Status |
|---|---|---|---|
| B1 AUTO+MANUAL | Complete table: declaration, file:line, claim (chapter label), "Lean-verified" or "Lean-verified conditional on Hyp.A, Hyp.B", differences (special cases, abstract setting); every report-relied declaration listed | `--check` (B1 counts distinct `Langlandscape.*` names); MANUAL: diff the table against `lean/Langlandscape/Audit/PrintAxioms.lean` output and the `\lean{}` uses: `grep -o '\\lean{[^}]*}' $(...)`, `diff` with names in report | [ ] |
| B2 AUTO | Table has conditional entries and a differences column | `--check` (B2) | [ ] |
| B3 AUTO | Hypothesis-discipline paragraph: Prop-valued definitions as explicit arguments, so each theorem is sorry-free with standard axioms and its type shows the hypotheses used | `--check` (B3) | [ ] |
| B4 AUTO | Final gate cited: 840/840 PrintAxioms, TITAN ramnrd-final-2 at 2323a252 (node name only in the Lean-gate wording the master allows, see A6!), and the frozen-import sorry (not in any audited declaration) | `--check` (B4); reconcile with A6 (the node name must not appear outside the title block: say "an independent from-scratch build") | [ ] |
| B5 MANUAL | Counts match the gate: 29 hypotheses, 2 discharged, 1 conditionally discharged | `lean/Langlandscape/HYPOTHESES.md`; `grep -n '29\|discharged' report.tex` | [ ] |

## C. Mathematics document
| # | Requirement | How to check | Status |
|---|---|---|---|
| C1 AUTO | Introductory chapter s00 is in `mathematics/main.tex` (motivation, setup, route, outline); report reuses its text | `--check --repo .` (C1); `grep -n s00 mathematics/main.tex`; build `main.pdf` | [ ] |

## D. Talk
| # | Requirement | How to check | Status |
|---|---|---|---|
| D1 AUTO | 14-21 frames before \appendix (backup frames after it not counted), <= 20 minutes (team decision 13:20Z, extended to 19 frames at 14:30Z and to 21 frames at 18:40Z for the two elementary intro frames: the official rule is ≤ 20 min, not a frame count; Fabian accepts a small overshoot pending rehearsal) | `--check` with repo (D1) = `\begin{frame}` count of the flattened `talk/main.tex`; rehearse the time | [ ] |
| D2 MANUAL | Structure follows the philosophy: congruences transported quaternionic to GL2; converse fails for the automorphic and the Galois/deformation reason; climax thm:s06-defect; integral comparison in D = q (Ribet, BT tree), component group Phi = Z/num((q-1)/12) | read the slides | [ ] |
| D3 MANUAL | Every claim on a slide occurs in the report with the same status | slide-by-slide against report.tex | [ ] |

## E. Audits
| # | Requirement | How to check | Status |
|---|---|---|---|
| E1 MANUAL | Fable audit of the FLATTENED report: statuses vs chapters/Lean/JSON; completeness vs this checklist | `mathematics/audits/` (new file dated); open findings resolved or listed | [ ] |
| E2 MANUAL | Fable pass on the talk | `mathematics/audits/` or `talk/` | [ ] |
| E3 MANUAL | Cross-account review by Abhijit's node, findings handled | `agents/messages/` | [ ] |
| E4 MANUAL | Last step: commit hash filled in the title block, report re-flattened, `python3 tools/flatten.py --check report.tex --build` shows 0 FAIL | rerun after the final commit | [ ] |
