<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# Independent audit of the last fix round, 2026-11-15

Auditor: independent Fable pass. Audited tree: branch `final/fixround-audit` at `4d87afa6` (= `wip-submission`).
Scope: `git diff 17b4e47b..4d87afa6` restricted to `mathematics/chapters/s00/`, `mathematics/submission/src/`, `talk/`,
`supplementary/agent-logs/README.md` (generated files, Lean tables and the transcripts themselves excluded).
Sources of truth: the chapters `mathematics/chapters/s01`--`s06`, the local literature copies (read only, not quoted),
Crossref for the DOI, `supplementary/agent-logs/<node>/manifest.json` and `redacted/`, `tools/redact_logs.py`,
the earlier talk audit `2026-11-15_talk-audit.md`.

## Verdict

**PASS WITH FIXES: 0 critical, 3 major (all applied), 6 minor (not applied).** No wrong number, no status upgrade.
The new subsection `ss:s00-oneway` is mathematically sound after the fixes; part (ii) is labelled heuristic in its
heading and closes with an explicit disclaimer. After the fixes `main.pdf` has the same page count, the stage starts
(20, 43, 69, 101, 119, 152) and the first page of all 224 numbered statements are unchanged; only pp. 4--9 (s00)
reflowed. `flatten.py --draft`: 0 FAIL, 3 WARN (A5, A7, A11, all pre-existing), 19 PASS; A6, A13, X1, A12 PASS.

## 1. Findings

### Major

**F1. `chapters/s00/question.tex`, (i): "a representation of $B_\ell^\times$ with an $\cO_\ell^\times$-fixed vector factors
through ... and is a character"; locator `[JL, Ch. III, Thm. 15.1]`. APPLIED.**
- The restriction to the levels used is right, but the sentence needs "irreducible": for an irreducible smooth
  representation the $\cO_\ell^\times$-fixed vectors form a non-zero subrepresentation ($\cO_\ell^\times$ is normal, being the
  unit group of the unique maximal order), so the representation is trivial on $\cO_\ell^\times$, factors through
  $B_\ell^\times/\cO_\ell^\times\cong\Z$ (valuation of $\Nrd$), is one-dimensional, and equals $\chi\circ\Nrd$ with $\chi$
  unramified. Without "irreducible" the statement is false, and "unramified" was missing.
- Local JL: $\chi\circ\Nrd\mapsto\sigma(\chi|\cdot|^{1/2},\chi|\cdot|^{-1/2})=(\chi\circ\det)\otimes\St$. Checked in the local copy
  of [JL]: Thm 15.1 (Ch. III, §15) only says that the local map is injective with image the special and absolutely
  cuspidal representations; the explicit image of the one-dimensional representations is in the paragraph after
  Lemma 15.4 (and in Thm 4.2(iii)). `chapters/s05/higherweight.tex`, Step 2, already gives this two-part locator.
- Replacement (applied): "an irreducible smooth representation of $B_\ell^\times$ with an $\cO_\ell^\times$-fixed vector is trivial
  on the normal subgroup $\cO_\ell^\times$, so it factors through $B_\ell^\times/\cO_\ell^\times\cong\Z$ (valuation of $\Nrd$) and is a
  character $\chi\circ\Nrd$ with $\chi$ unramified; under the local correspondence it corresponds to the twisted Steinberg
  representation $\chi\otimes\St$ of $\GL_2(\Q_\ell)$ `\cite[Ch.~III, Thm.~15.1 and the paragraph after Lemma~15.4]{JL}`".

**F2. `chapters/s00/question.tex`, (ii): "context only, not used in our proofs" / "None of the statements in (ii) about
deformation rings is proved or used here". APPLIED.**
True for the statements of (ii) themselves (the surjection $R_{\GL_2}\twoheadrightarrow R_B$, the cotangent module, the
numerical criterion: none occurs in a proof). But $R=\T$ theorems and a deformation ring do enter the chapters as cited
inputs: inside the proof of [KO, Thm 1.1] (remark after `cor:s06-fixed`) and directly, as [KO, Thm 3.14], in step (4) of
the proof of `prop:s06-levM` (which constructs a point of the deformation ring of [KO, Def. 3.9]). A reader who meets that
step after the blanket sentence sees a contradiction. Replacement (applied), appended to the last sentence:
"; $R=\T$ theorems enter our results only as cited inputs: inside the proof of [KO, Thm. 1.1] (Thm. `thm:s06-KO`) and, as
[KO, Thm. 3.14], in the proof of Prop. `prop:s06-levM`."
The companion sentence in `src/stage06.tex` ("our proofs do not use Wiles' numerical criterion or Ribet--Takahashi; they
appear only as heuristic context in §...") is correct as it stands: [Wi95] is otherwise cited only for the Gorenstein
property (Ch. 2, Cor. 1, 2, p. 482), [RT97] only in s00.

**F3. `submission/src/aiuse.tex`, "Session transcripts": coverage overstated. APPLIED.**
The paragraph says the redacted transcripts of the agent sessions are published, one directory per machine. The README
lists four machines, the fourth (the second team member's) as "pending" with no directory. Replacement (applied):
"the README there lists the machines covered with their session counts (a machine whose export is not yet in the
repository is marked as pending there) and the redaction policy". If the fourth export lands before submission the
sentence stays true.

### Minor (not applied)

**m1. `question.tex`, (i), `\cite{Ri84}` has no locator**, and [Ri84] is the one source of the subsection that could
not be text-verified (the local copy is a scan without text layer; the bib note still says "NOT in literature/").
Suggested: `level raising \cite{Ri84}, \cite[Thm.~1.1]{Ri90}` only if someone checks the locator; otherwise leave.

**m2. `question.tex`, (i): "the Ihara lemma Cor. 10.5" carries no status.** Chapter: (i), (ii) proved given
connectivity, (ii') proved modulo cited. Suggested: "(Cor. 10.5, \stproved{} given connectivity)".

**m3. `question.tex`, (ii): "$\cc_q(F)=\tq_q(F)$ (Thm. 21.5, proved modulo cited)" without "under its hypotheses".**
Status word as in the chapter; the theorem is open outside (H0$^-$)/(Lev). Suggested: "under the hypotheses of
Thm. 21.5". Likewise "(Thm. 19.8(iii), proved, applied in Thm. 21.5, proved modulo cited)" is accurate: the
specialisation to the Hecke rings needs the cited Gorenstein inputs, and the text attributes it to Thm. 21.5.

**m4. `question.tex`, first sentence: "every system of Hecke eigenvalues on the definite side occurs on the $\GL_2$
side".** At $k=2$ the line of functions factoring through $\Nrd$ is Eisenstein (Thm. 6.1); it occurs on the $\GL_2$ side
as an Eisenstein series, not in $S_k$. Suggested: "every non-Eisenstein system".

**m5. Talk, `f06-converse.tex` line 12: "(cited: JL, Thm 15.1)"** has the locator issue of F1. Suggested:
"JL, §15 (Thm 15.1 and after Lemma 15.4)". The frame is full; not applied, `talk/main.pdf` not rebuilt. In the footnote
line "heuristic / context; cited, not used in our proofs" the word "cited" belongs to Wiles and Ribet--Takahashi, not to
the surjection $R_{\GL_2}\twoheadrightarrow R_B$; "heuristic" is said first, acceptable.

**m6. `supplementary/agent-logs/README.md`:** "e-mail addresses (except institutional Paderborn ones)": the tool also
keeps `noreply@anthropic.com` (commit trailers). Suggested: add "and the commit-trailer address of the model vendor".
Pre-existing, outside the round: `main.pdf` p. 18 has one unresolved `\ref{app:hyp}` (s00/plan.tex:38; the appendix
exists only in the report, where the reference resolves).

## 2. What was checked and found correct

| item | result |
|---|---|
| Thm 6.1 (`thm:s01-JLclassical`) cited | as in the chapter (cited; $D$-new part, plus the $\Nrd$ line at $k=2$) |
| Prop 9.7 (`prop:s03-LRdef`) proved | as in the chapter |
| Cor 10.5 (`cor:s03-ihara`) | number correct; status see m2 |
| Thm 19.8(iii) (`thm:s06-E`) proved; $\eta=\cc_q\cdot\eta'$ | as in the chapter |
| Thm 21.5 (`thm:s06-defect`) proved modulo cited | as in the chapter (under (H0$^-$), or (Lev) in the listed cases) |
| Cor 21.2 (`cor:s06-fixed`) proved modulo cited, $\cc_q(f)=(\varpi^{t_f(q)})$; its proof identifies [KO, Def. 2.11] with $\eta(\T'_k,\lambda'_f)$ | as in the chapter; Def. 2.11 confirmed in the local copy ($N^-$-new congruence ideal; Def. 2.12 is the Tamagawa exponent) |
| Thm 21.1 (`thm:s06-KO`) cited, [KO, Thm 1.1] | as in the chapter |
| [Hs, Rem. 7.8] | local copy: the quaternionic Hecke algebra is isomorphic to the $N^-$-new quotient; supports $\T\twoheadrightarrow\T'\cong\T_B^{\ord}$ (cited) |
| [Wi95, Appendix] | local copy: Appendix, Prop. 2 (criterion comparing the length of $\mathfrak p/\mathfrak p^2$ with that of $\cO/\eta$) |
| [RT97, Thm. 1] | local copy: degrees of the two parametrisations differ by the product of two local component-group orders up to an error term |
| (ii) heuristic | heading says "heuristic; context only, not used in our proofs"; the only status-bearing statements are on the Hecke side and are labelled cited / proved modulo cited; the deformation-ring sentences are in the conditional reading ("Read through $R=\T$ theorems", "In this reading") and disclaimed at the end |
| `s00/outline.tex` R1 | 950/950, gate commit `dc61af50`, tree `28d2b091`, previous `2323a252` 840/840: agree with `src/counts.tex`, `lean.tex`, `commits.tex`, `event.tex`, `agentic.tex`; `28d2b091` is the merge of the bundle `dc61af50` |
| `src/stage06.tex` | sentence correct (see F2); page numbers in the stage files agree with the rebuilt `main.pdf` |
| `src/agentic.tex` pointer | `\ref{sec:ai}` resolves; anonymous |
| `references.bib`, `report.bib` Wi95 DOI | Crossref: 10.2307/2118559 = Wiles, Ann. of Math. 141 (3), 1995, first page 443 |
| talk order and count | 17 frames; converse frame after the $\Lambda$-adic frame (frame 9) as required by M5 |
| talk audit fixes | B1 (alternative taken: the sentence now exists in the report, `ss:s00-oneway`, and the slide marks it heuristic, not used), M1--M8, m1--m8 present and correct in `f02`, `f03-want`, `f05`, `f06-converse`, `f07`, `f08`, `f10`, `f11`, `f12`, `f14`, `f15`, `f16` |
| converse frame vs report | (i) as `ss:s00-oneway` (i) and `prop:s06-betti`(b) (proved modulo cited; $p>k\ge4$, $q\not\equiv-1$ on the slide); (ii) Kim--Ota with condition (6) |
| Lean frame | 950/950 via `counts.tex`, tree `28d2b091`, 29 / 2 / 1 hypotheses: as in the report |
| process frame | the disclosed external draft is on the slide (M8) |
| agent-logs README table | `localhost` 538 = 40 / 464 / 34, `titan` 1 = 1 / 0 / 0, `conceptd` 88 = 2 / 86 / 0: equal to the rows of each `manifest.json` and to the files in each `redacted/` |
| redaction policy vs `tools/redact_logs.py` | limits 500 / 300 / 15 lines / 5 MB, thinking not exported, literature and `pdftotext` results removed, masks for e-mail, keys, rclone lines, phone numbers, home paths, session URLs: as stated. Spot check of the exported files: no home path, only the allowed addresses. No secret in the README |

## 3. Builds after the fixes

- `latexmk -pdf main.tex`: 191 pages before and after; stage starts 20, 43, 69, 101, 119, 152 unchanged; first pages of all
  224 numbered statements unchanged; text changed only on pp. 4--9. No page number in the report needs redoing.
- `build_bib.py`: 102 entries (unchanged). `flatten.py src/report-src.tex --draft`: 0 FAIL, 3 WARN, 19 PASS.
- `talk/`: not changed, not rebuilt.
