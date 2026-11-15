<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Submission-report audit (2026-11-15)

Object: `mathematics/submission/report.tex` (+ `report.pdf`, 169 pp.) at `28c1066f` (branch `final/audit-sub`),
flattened from `mathematics/submission/src/report-src.tex`. Auditor: Fable 5.2, independent, read-only (this file is
the only change). No new mathematics was checked; the question is whether the report says exactly what the sources
support and complies with the submission rules.

Line numbers `L…` are lines of `report.tex`. Fixes go into the SOURCE named in each finding (`src/*.tex`, a chapter
file, a `.bib` file or a generator), never into `report.tex`; re-flatten afterwards.

## Verdict

**FAIL as it stands: 5 blockers (B1–B5).** All five are text corrections of one to four lines each; no mathematical
statement is wrong, no Lean claim is false, and no computational result is wrong. After B1–B5 and the majors M1–M5
are applied: **PASS WITH REMARKS**.

Counts: blocker 5, major 5, minor 14, plus 3 decision items for the master (D1–D3).

Intentional and not counted: A5/A11 FAIL (commit hash and bundle-gate placeholders `\TODOFACT`, L214, L7547), A7 WARN
(section order follows the binding narrative order).

## Checker run

`python3 -I tools/flatten.py --check report.tex --build`: 3 FAIL, 2 WARN, 16 PASS.

| id | result | comment |
|---|---|---|
| A5, A11 | FAIL | intentional placeholders (commit hash in the title block, bundle gate in the commit appendix) |
| D1 | FAIL | talk has 22 frames (limit 14–17); not part of the report, for the talk audit |
| A7 | WARN | intentional (binding narrative order); all 13 required sections are present, plus "Agentic setup" |
| A12 | WARN | one external-only reference, L4046 `[chapters, Rem 18.33]`: see m9 |
| S1, S2, X1 | PASS | compiles alone (pdflatex ×2), no `??`, no unresolved reference |
| A1–A4, A6, A8–A10, B1–B4, C1 | PASS | |

## Findings

### Blockers

**B1. Status upgrade in the claims table: Thm 10.2 loses "given connectivity", and (c) is upgraded.**
- Where: L4145; source `src/results.tex` l. 74, column "status on paper".
- Now: `(a) proved; (b) (coefficients) proved modulo cited; (c) proved`.
- Truth: `chapters/s03/3-ribet.tex` l. 106–108 (status line of `thm:s03-ribet`): given (iii), (a) and the first two
  sentences of (c) are proved; (b) and the last sentence of (c) are proved modulo cited; without (iii) everything is
  proved modulo cited. Connectivity (iii) is not a hypothesis of the theorem's statement, so the row is stronger than
  the chapter. The quoted box and the s00 text are correct.
- Replacement cell:
  `given connectivity of $\BG(U,q)$ (condition (iii)): (a) and the first two sentences of (c) proved; (b) (coefficients) and the last sentence of (c) proved modulo cited; without assuming (iii): proved modulo cited (Thm 7.7, Hasse--Schilling, connectedness of the tree)`

**B2. "Unconditional" is used for theorems that keep explicit hypotheses (binding wording rule).**
Theorems freed of the discharged `Hyp.PadicOrdDecomp` / `Hyp.RamNrdSurj` still take connectivity
(`2323a252:lean/Langlandscape/Langlandscape/Ordinary/TowerUncond.lean:88,112`: `hconn`, `hc : Tree.BGConnected …`).
- L4304–4306; source `src/lean-discipline.tex` l. 22–24. Replace
  `and each such theorem is unconditional once the discharge lemma is supplied (for \texttt{PadicOrdDecomp} the library also contains the \texttt{\_uncond} versions)` by
  `and supplying the discharge lemma removes only that argument: each such theorem is then free of that registered hypothesis but keeps its other explicit hypotheses, such as the connectivity \texttt{Tree.BGConnected} of the Brandt graph (for \texttt{PadicOrdDecomp} the library also contains versions with the suffix \texttt{\_uncond}, which likewise keep those hypotheses)`
- L4772; source `tools/lean_table.py` l. 128 (regenerate the table). Replace
  `formalized (unconditional \texttt{\_uncond} versions)` by
  `formalized (the \texttt{\_uncond} versions: free of \texttt{Hyp.PadicOrdDecomp}, with the connectivity of $\mathrm{BG}(UU_s,q)$ as an explicit argument)`
- L4749; source `tools/lean_table.py` l. 125. Replace `\texttt{hdec} discharged, so unconditional` by
  `\texttt{hdec} discharged, so free of registered hypotheses`
- L5800–5801; source `src/appendix-hyp-body.tex` l. 82–83. Replace the two status-word lines by
  `\emph{formalized} = no registered hypothesis in the type (other explicit hypotheses of the statement, e.g.\ connectivity, remain); \emph{discharged} = a closed Lean proof of \lname{Hyp.X} exists (so every consumer has a form without that argument).`
- L1014; source `chapters/s00/achieved.tex` l. 8. Replace
  `are built integrally and unconditionally (up to cited inputs and the connectivity condition (iii))` by
  `are built integrally, given the cited inputs and the connectivity condition (iii)`

**B3. The binding wording for the 104 cited-but-unaudited declarations is missing; three places claim more.**
The phrase "exists in the code, not in the axiom audit, not claimed as Lean-verified" occurs nowhere. Two claims are
supported only by such declarations: `prop:s02-Mhomprops` (Prop. 7.14) and `prop:s02-duality` (Prop. 7.16), which
carry a `formalized` marker at L1644, L4205, L4206 (`generated/lean-table.json`: 0 audited rows for both labels).
- L4898; source `tools/lean_table.py` l. 781 (preface of Table L2). Replace the sentence
  "Those that exist in the gated tree compile … not by \texttt{\#print axioms}." by
  `Each of them exists in the code of the gated tree (102 in the library, 2 in the test library) and compiles in the from-scratch build, but it is not in the axiom audit and is not claimed as Lean-verified; the gate's \texttt{sorry} count and forbidden-token grep cover these files, \texttt{\#print axioms} does not. Two claims are supported by such declarations only: \texttt{prop:s02-Mhomprops} (Prop.~7.14) and \texttt{prop:s02-duality} (Prop.~7.16); where the chapters mark them \emph{formalized}, read: exists in the code, not in the axiom audit, not claimed as Lean-verified.`
- L4333–4335; source `src/lean-discipline.tex` l. 51–53. Replace
  `are covered by the from-scratch build, the \texttt{sorry} count and the forbidden-token grep, not by \texttt{\#print axioms}` by
  `exist in the code and compile in the from-scratch build, but are not in the axiom audit and are not claimed as Lean-verified (only the \texttt{sorry} count and the forbidden-token grep cover them)`
- L4344–4345; source `src/lean.tex` l. 13–14. Replace
  `(checked by \texttt{\#print axioms} for the \GateAudited{} headline declarations; for the other declarations named in the chapters by the \texttt{sorry} count and the forbidden-token grep)` by
  `(checked by \texttt{\#print axioms} for the \GateAudited{} audited declarations; the other declarations named in the chapters exist in the code, are not in the axiom audit and are not claimed as Lean-verified)`
- L4294; source `src/lean-discipline.tex` l. ≈13. Replace `every theorem of the library is sorry-free and depends only on` by
  `every audited theorem is sorry-free (the library itself contains no \texttt{sorry}) and depends only on`

**B4. Wrong numbers in "AI use": 17 % / 48 % / 35 % are not the staged-plan figures.**
- Where: L5203–5204; source `src/aiuse.tex` l. 16–17. The text says Muse Spark Open audited "the staged plan (17\% of
  its findings fully confirmed, 48\% partly, 35\% rejected)".
- Truth: `docs/agentic-process/model-study.md` l. 45: staged plan (P1) 7/70 confirmed, 22 partial, 41 rejected
  (10 % / 31 % / 59 %); implementation plans (P3) 15/89, 43, 31 (17 % / 48 % / 35 %). The section "Agentic setup"
  (L5366–5368) gives the P1 counts correctly, so the two sections contradict each other.
- Replace `was a first-pass auditor of the staged plan (17\% of its findings fully confirmed, 48\% partly, 35\% rejected)` by
  `was a first-pass auditor of the plans (staged plan: 7 of 70 findings fully confirmed, 22 partly, 41 rejected; implementation plans: 15 of 89 fully confirmed, 43 partly, 31 rejected)`

**B5. Every page number quoted for `main.pdf` is wrong for the committed file (off by 13).**
- The committed `mathematics/main.pdf` has 184 pages (chapter s00 was prepended); the report's pages are those of the
  170-page build. Example: Thm 21.5 is quoted "p. 146" and is on p. 159. Theorem numbers are all correct.
- Affected: the page argument of all 62 quoted boxes, Table `tab:allresults` (L4189 ff.), the stage ranges at L1222,
  1605, 2047, 2465, 2929, 3374, and "170 pp." at L5676 and L5162. L5676 states "all theorem and page numbers quoted in
  this report refer to it", which is false for the pages.
- Preferred fix: regenerate the page arguments from the current `main.aux` and re-flatten.
- Cheapest fix (two edits):
  - `src/report-own.bib` l. 38 ff. (entry `LLmain`; same in `src/report.bib`, then rebuild the bibliography). Replace the note by
    `\texttt{mathematics/main.pdf} of the submission repository (184 pp.\ including the introductory chapter). All theorem numbers quoted in this report refer to it; the page numbers quoted are those of the build without the introductory chapter (170 pp.): add 13 to obtain the page in the current file`
  - `src/event.tex` l. 24. Replace `the six chapters (\mainpdf, 170 pp.) and the introductory chapter` by
    `the six chapters and the introductory chapter (\mainpdf, 184 pp.; the six stage chapters alone are 170 pp.)`

### Major

**M1. Claims table, Cor 10.5: "given connectivity" dropped.**
- L4146; `src/results.tex` l. 75. Now `proved / proved modulo cited`.
- Truth: `chapters/s03/3-ribet.tex`, status of `cor:s03-ihara`: (i), (ii) proved given (iii); (ii′) proved modulo cited.
- Replacement cell: `(i), (ii) proved given connectivity (condition (iii)); (ii$'$) proved modulo cited (given (iii); the tree property is cited)`

**M2. Prop 18.25 is called Lean-verified ("Table L1 records no difference"), but there is a small difference.**
- Lean takes the splitting hypothesis as `(𝔞 ⊔ 𝔟).map includeRight = ⊤`; its equivalence with the product
  decomposition (CRT step) is declared not formalized (header of `CommAlg/Gorenstein.lean` at 2323a252; the report's
  own limitations list, L5653). The three-point check otherwise passes.
- L4164; `src/results.tex` l. 93. Replace the Lean cell by
  `\textbf{Lean-verified} (\texttt{CommAlg.subquot\_kernel}, \texttt{subquot\_coker}), with the splitting hypothesis in the equivalent form $(\fa+\fb)\T_K=\T_K$ (the CRT equivalence with $\T_K=(\T/\fa)_K\times(\T/\fb)_K$ is not formalized)`
- L4807; `tools/lean_table.py` l. 134. Replace `none recorded in the chapter's Lean note` by
  `statement as in the chapter, except that the splitting hypothesis is taken in the form $(\mathfrak a+\mathfrak b)T_K=T_K$; its CRT equivalence with the product decomposition is not formalized`

**M3. Claims table, Thm 14.4: "Λ-adic half cond. on Hyp.MordLambdaFree" overstates.**
- No declaration at 2323a252 takes `Hyp.MordLambdaFree` as an argument (`git grep` finds it only under `Hyp/`);
  Table L1 itself says "only stated, as the open hypothesis".
- L4153; `src/results.tex` l. 82. Replace `$\Lambda$-adic half cond.\ on \texttt{Hyp.MordLambdaFree}` by
  `the $\Lambda$-adic half is the open hypothesis \texttt{Hyp.MordLambdaFree} (stated only; no Lean theorem uses it)`

**M4. The abstract gives an incomplete list of hypotheses as if complete, and an incomplete open region.**
- L227–231; `src/abstract.tex` l. 12–17. Thm 21.5 (`chapters/s06/s06-m3.tex`, `thm:s06-defect`) assumes (H0), (H1),
  (H2), (P) and (H0⁻) or (Lev); the abstract omits (P), $p\nmid\varphi(qM)$ and $p$-distinguishedness, and names only
  $N(\bar\rho)>1$ as open (the chapter also leaves non-squarefree $M$ open; this is finding X3 of the cross-account
  review, reappearing here). The Lean sentence omits the non-registered premises (connectivity, abstract settings).
- Replace `under explicit standing hypotheses ($p\ge5$, non-Eisenstein, residually absolutely irreducible, and either $q\not\equiv-1\bmod p$ or one of the level conditions (Lev)); the remaining case $q\equiv-1\bmod p$ with $N(\bar\rho)>1$ is open.` by
  `under the explicit standing hypotheses of \S\ref{ss:s00-H} (among them $p\ge5$, $p\nmid\varphi(qM)$, a non-Eisenstein maximal ideal, residual absolute irreducibility and $p$-distinguishedness, the existence of a suitable arithmetic point, and either $q\not\equiv-1\bmod p$, or $\bar\rho$ ramified at $q$, or one of the level conditions (Lev)); for $q\equiv-1\bmod p$ outside (Lev) ($N(\bar\rho)>1$, or non-squarefree $M$) it is open.`
- Replace `every mathematical input not proved in Lean is one of \NumHypRegistered{} registered hypotheses passed as an explicit argument, of which \NumHypDischarged{} are discharged` by
  `every cited or not yet formalized input is an explicit argument: one of \NumHypRegistered{} registered hypotheses, of which \NumHypDischarged{} are discharged, or a stated premise such as the connectivity of the Brandt graph; several statements are about abstract data`

**M5. Identifying information outside the title block: the team name as author of three bibliography entries.**
- L5674–5676; `src/report-own.bib` l. 35, 42, 49 (and `src/report.bib` l. 31, 38, 45): `author = {{The Langlandscape team}}`.
  The checker's word list does not contain the team name, so A6 passes.
- Replace each by `author = {{The authors of this report}}` and rebuild the bibliography. (The namespace
  `Langlandscape.*` and the path `lean/Langlandscape/` cannot be avoided; see D1.)

### Minor

- **m1. Thm 15.1, "proved" without the connectivity hypothesis.** L4154 (`src/results.tex` l. 83): replace `proved` by
  `proved, given connectivity of $\BG(UU_s,q)$ for all $s\ge1$ (a hypothesis of the theorem)`; in the same row replace
  `inverse limit cond.\ on \texttt{Hyp.InvLimExact}` by
  `inverse limit formalized given connectivity and the surjectivity of the $A$-transitions as explicit arguments (the latter is the conclusion of the open \texttt{Hyp.InvLimExact})`
  (`Ordinary/Limit.lean:502` takes `hA`, not the hypothesis). L1072 (`chapters/s00/achieved.tex` l. 66): replace
  `Thm.~\ref{thm:s04-lambdaribet}(a) (\stproved)` by `Thm.~\ref{thm:s04-lambdaribet}(a) (\stproved{}; the latter given connectivity of $\BG(UU_s,q)$ for all $s$)`.
- **m2. Thm 21.5 outline, squeeze step.** L3729 (`src/stage06.tex` l. 370): the chapter prints no marker on step (5),
  which also uses Lemma 20.7(b),(c) (proved modulo cited). Replace `\stproved{} (given (1)--(4))` by
  `\stproved{} as commutative algebra, given (1)--(4) and Lemma~20.7(b),(c) (\stpmc).`
- **m3. Prop 24.1(b) outline.** L3912 (`src/stage06.tex`): replace `(\stknown, no source located in the project literature; open point N5)` by
  `(\stknown{} as standard, but no source located in the project literature: open point N5; (b) is \stpmc{} modulo this unsourced input as well)`
  (`chapters/s06/s06-m7.tex` l. 69).
- **m4. Stage-05 intro describes notes that are no longer printed.** L2931 (`src/stage05.tex` l. 19–20) speaks of
  "[provisional: …]" notes. Replace the first sentence by
  `\emph{On the revision notes.} The quoted boxes reproduce, verbatim, the chapter's notes on changes made after internal audits, printed here as \textup{[revision note: \dots]}; they record what changed and the previous wording.`
- **m5. HACS full-run statement is stale (an understatement).** The Lane B closure §7
  (`plan/hacs/outbox/20261115T0150Z_laneB-closure.md` l. 89–97) records the run. `src/computations.tex` l. 117–118:
  replace `one full run is due after the merge;` by
  `the one full run was done after the merge (\texttt{--all} in 4 shards 248/248, \texttt{GOLDEN\_STRICT} tier A 12154/0, tier B 6231/0; still not run: the digests, \texttt{LABEL\_CENSUS}, \texttt{--all-full}, the device lane);`.
  `src/limitations.tex` l. 67: replace `one full validation row after the merge (\texttt{--all} sharded, \texttt{GOLDEN\_STRICT}, digests, \texttt{LABEL\_CENSUS})` by
  `the remaining validation steps (digests, \texttt{LABEL\_CENSUS}, \texttt{--all-full}, the device lane; \texttt{--all} 248/248 and \texttt{GOLDEN\_STRICT} were run after the merge)`.
  `chapters/s00/newknown.tex` (L4073): `a full HACS validation row` → `the remaining HACS validation steps`.
- **m6. Lean file count.** L5163 (`src/event.tex` l. 25): "about 38\,000 lines in 195 non-vendored files" is the
  02:10Z figure of `metrics.md`; the tree now has 199 non-vendored `.lean` files with 37 861 lines. Replace
  `195 non-vendored files` by `about 200 non-vendored files`.
- **m7. Time zone.** L5169 ff. (`src/event.tex` l. 29–48): the timeline is in "local time CET", all other sections in
  UTC; the local zone is also a (weak) location hint. Convert the table to UTC (subtract 1 h) and replace the
  paragraph head by `Timeline (from the git history and the process log; UTC, 14--15 November 2026).`
- **m8. Self-containedness of the quoted boxes.** Internal identifiers (`if:s02-quot`, "stage tex", S04-M9, F7,
  "batch 6 (E3)", (R4)) are never explained. Add to `src/outline-intro.tex`, end of the "Statements" item:
  `The quoted text also contains internal identifiers of our working documents: \texttt{if:sNN-\dots} names an interface (the statement a later stage is allowed to use), ``stage tex'' and ``seed'' are earlier planning documents, and codes such as S04-M9, F7, D3, ``batch 6 (E3)'' or (R4) are work-package, audit-finding and remark numbers; none of them is needed to read the statements.`
- **m9. The one A12 external-only reference (Rem 18.33, L4046).** Its content (verdict, status, decision FD2) is in
  §`ss:hsieh`. In `chapters/s00/newknown.tex` replace `[chapters, Rem~18.33]` (the `\ref{rem:s05-hsieh}` there) by
  `\S\ref{ss:hsieh}`; or add `\label{rpt:rem:s05-hsieh}` after the `\subsection` line of `src/hsieh.tex`.
- **m10. Chapter inconsistency on FD1 (main.pdf only).** `chapters/s05/status.tex` l. 73 (Rem 18.34): replace
  `it stays conditional on the open decision FD1` by
  `it is conditional on the model decision FD1, taken on 2026-11-15: $\mu_N$-model, Picard functoriality`. The report says "decided" consistently.
- **m11. Duplicate citations and Helm key.** Where a chapter has a typed citation and a `\lit` pointer, both are
  printed (L2251, Thm 21.5, Lemma 20.7). In `src/stage06.tex`, Thm 21.5, the arXiv page pointer "Cor. 8.11, p. 31"
  should use the key `Hel04` (as in Thm 16.6 and Prop 18.24), not `Hel`. No status impact.
- **m12. Bibliography.** Ri90 (`src/report.bib` l. 498): delete `number = {1},` (the issue number is uncertain; DOI,
  volume, year, pages are right). Bad08: optional `note = {With an appendix by Neven Grbac}`. Series volumes are
  dropped by `tools/build_bib.py` (e.g. JL prints "Lecture Notes in Math." without 114; the in-text reference at L252
  has it, so A10 holds). Koh01 prints year and pages twice.
- **m13. Table L1 per-row notes.** Rows `Ribet.ihara_surj`, `ihara_ker_const` and the `_uncond` rows take
  `hc`/`hconn` without a per-row note (the claim-level Difference line covers it); the Difference lines of
  `thm:s06-defect`, `cor:s06-fixed` do not mention the plain arguments (DVR, `H0`, `H0minus`). Optional.
- **m14. Prop 7.10(a) "or cond. on Hyp.SA, Hyp.HS"** (L4138) rests on the unaudited `Tree.quotVEquiv_of_SA_HS`,
  `quotEEquiv_of_SA_HS` (Table L2). With B3 applied the wording is covered; optionally add "(unaudited declarations, Table L2)".

### Decision items for the master

- **D1. Indirect identification.** The body calls HACS and the GL(2) trace-formula project the team's own prior work
  and prints the HACS Zenodo DOIs (L1178–1179, L5512–5513, bibitems L5672–5673); the DOI record names its author. The
  brief requires both the disclosure and the versions, so this is unavoidable unless the DOIs are moved to the title
  block. Likewise the repository/namespace name `Langlandscape`. No change proposed; decide knowingly.
- **D2. Hardware descriptions** (L5247–5250: thread counts, RAM, "under WSL", "notebook") are not names; keep or
  shorten to "two build machines and a second team member's machine".
- **D3. Talk**: 22 frames against the 14–17 rule (checker D1). Outside this audit.

## Handed-over items (check 7)

| item | verdict |
|---|---|
| Thm 7.7 (cited) vs Thm 7.34 (proved modulo cited, Hasse–Minkowski) | OK: box, s00 and table row say both |
| FD1: Rem 18.34 "open decision" vs Rem 18.10/18.33 "decided" | report consistent ("decided"); chapter line to fix: m10 |
| Prop 18.6(a), Γ₁ part | OK: "proved modulo cited given (X1) and FD1", verbatim |
| Thm 14.4(b) | OK on paper (cited for U₁(M), integral if p∤φ(M), otherwise sketched; general level expected); Lean cell: M3 |
| Thm 16.7 | OK: cited |
| Prop 18.1 | OK: "to prove" in box, outline and table; nothing uses it as proved |
| Thm 11.3(b) | OK: proved modulo cited overall |
| Lem 8.7 | OK: proved modulo cited (Voight list cited); Lean `Hyp.EllipticCount` |
| Thm 10.2(c) | box and outline OK; table row wrong: B1 |
| Prop 24.1(b) | fix text: m3 |
| Thm 21.5 squeeze step | fix text: m2 |
| Prop 23.2 step (4), (F0)/(F1) | OK, verbatim; the chapters name two sources for M = 1 (KO Thm 3.14 in step (4), KO Thm 2.9 + Lemma 2.4 in Thm 21.5), both reproduced, no status effect |
| Rem 18.41, Chenevier unmarked | OK: a located citation; Thm 6.2 carries the cited status; table row says "sketched on the ordinary locus; open beyond" |
| "about 30 000 imported lines" | OK: L5154–5156 gives both figures; `wc -l` over the `.lean` files of `lean/trace-formula-project-import` = 36 353 confirmed |
| A12 external-only ref (Rem 18.33) | content is inside (§`ss:hsieh`); pointer fix: m9 |
| 36 lower-confidence Lean mappings | 22 checked against chapter lines and Lean docstrings: no wrong mapping |

## What was checked and found correct

- **Rules.** Single file, inlined bibliography, three figures each with a caption describing it in words, problem text
  verbatim with both references, scope statement ("definite", not "anisotropic"; all inner forms / number fields /
  GL(n) cited), all required sections including "Agentic setup" and the event/prior split. PDF metadata: author empty.
  Body after `\maketitle`: no hit for the names, node names, GitHub user, affiliation, e-mail or home paths, including
  the verbatim statements, the tables, the hypotheses appendix and the commit appendix (M5 and D1 are the exceptions).
  Title block: names, titles, affiliation, track, repository link and `\thanks` acknowledgments as decided.
- **Verbatim stage statements.** All 62 quoted blocks diffed word by word against the chapters: the only differences
  are `\ref` → number, `\lit` → `\cite` (right key and locator, except the Helm key in m11), `\provisional` →
  `\revnote` (12 notes, exact text, none hides a status) and anonymisation. No status macro added, removed or changed.
  All 38 entries of `src/defs.tex`: no status absent from the chapter.
- **Lean.** Axiom log: 840 entries, all standard (815 full triple, 23 subsets, 2 without axioms), no `sorryAx`; gate
  summary 4198 jobs, 321 s, empty forbidden-token grep, one `sorry` in the built tree
  (`AlgJL/VolIII/P2/Instances.lean`), outside every audited declaration. Three-point check passes for the five
  Lean-verified rows (Prop 17.1, Prop 18.25 with the caveat M2, Lem 19.2, 19.3, 19.4): present at 2323a252, standard
  axioms, no `Hyp.*` argument, statement matches. 14 conditional rows match their signatures. All 840 rows of the
  appendix table re-derived from the gated source; no row labelled plain Lean-verified has a `Hyp.*` binder. Counts
  29 / 2 / 1 / 26, 48 + 3 conditional, 18 with only discharged hypotheses, 104 unaudited. 15 Difference lines of
  Table L1 faithful (apart from B2, M2).
- **Numbers.** Every computational number checked against `code/results/*.json` and the HACS closures with errata:
  109/109 (π(600) = 109) at ℓ ≥ 5; first 80 primes, q ≤ 409, capped; 60 cells k > 2, 26 non-zero, |C| = 37 at
  (13, 8); 64.7 s / 0.02 s; 69/69; T4, T5 (7/7 and 4/7), H3, C2 131/319 with 225/225 in-scope rows; stages 01–05
  (66/66, 240/240, 121, 144/144 with the 70/74 split). Earlier findings B1–B3, X1, X2, X5, X10, X11 of the two earlier
  audits have not reappeared (X3 reappears in the abstract only: M4).
- **Bibliography.** 71 bibitems, 71 cited keys, none unresolved or uncited. Ri90, RT97, Bad08, BR10, Bergeron16, CH15:
  DOI present, metadata plausible (m12). Ribet's locators (Prop 2.2, Thm 2.3, Prop 3.1, 3.3, 3.8, Thm 3.12, 3.15,
  Rem 3.18, Thm 3.19, Thm 4.1, Cor 4.2, Thm 4.3), RT97 Thm 1, Mazur Appendix Thm A.1(b), Bad08 Thm 5.1, BR10 Thm 18.1
  and others checked against local copies.
- **Known/ours.** The claims-table legend and the section "What is new and what is known" hedge every novelty
  attribution ("we did not find this in the literature we checked"; "not the result of a systematic search"); no
  unhedged novelty claim found. Ribet's Rem. 3.18 (graph-connectivity proof) is credited where the definite Ihara
  lemma is listed as ours in form.
- **Event / AI / agentic sections.** Event window, first commit f7d8fd70 at 05:52Z, the prepared/imported list (seed,
  trace-formula import, HACS snapshot) and the event-work list match the binding facts. AI tools are exactly Claude
  Code (Opus 5.5, Sonnet 5.5, Haiku 5.5, Fable 5.2) and opencode (Mistral Large 4, Muse Spark Open; Q&A plus the
  disclosed `RamNrdSurj` draft); computational tools PARI/GP via cypari2, Python, HACS; no other tool is named. The
  agentic numbers agree with `docs/agentic-process/` (except B4).
- **Commit appendix.** All 23 hashes resolve; the dates (UTC) and descriptions match `git log`; all listed merges lie
  on the first-parent history of `main`.

## Method notes

Three parallel sub-audits (stage statements and chapter items; Lean; numbers and bibliography) ran under the same
model and their findings were merged here; B1, B2, B5 were re-verified by the lead auditor. Issue numbers and some
locators in the bibliography were judged from memory where no local copy exists (stated in m12). The `main.aux` used
for the number check came from a sibling worktree, not from a fresh build at 28c1066f.
