<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Audit: sentences changed by the JL first-case decision (2026-11-15)

Independent read (Fable) of `git diff 4e42dd21..bba4f714` in the s00 files (`abstract-short`, `whycited`, `achieved`,
`newknown`, `motivation`, `prior`, `plan`), `article/mainresults.tex`, `submission/src/{summary,limitations}.tex`,
`lean/Langlandscape/HYPOTHESES.md`, `report/hypotheses.tex`, `talk/slides/{f05b-jlproof,f02-jl,f12-question,f16-new-known}.tex`.
Scope: consistency and no overclaim only. Reference: the team decision (first case = *proved modulo cited geometry*; in
general *invokes JL*; route 1 planned / timing uncertain; route 2 new mathematics, unclear, open) and the binding
correction (the first-case proof is Ribet's, known; ours = its tree / Brandt-graph incarnation and the integral/defect
extension).

## Verdict

**PASS after fixes.** The decision is implemented consistently in all 15 files. No place calls the first-case proof new or
ours; every body sentence carries "modulo (the) cited geometry". Three headings/labels used a bare "reprove(d)" and were
fixed (F1--F3, applied). Two points need a team decision and are NOT applied (N1, N2); four minor points are listed with
replacement text (m1--m4, not applied except where stated).

## Checks

| check | result |
|---|---|
| first case = "proved modulo cited geometry", never bare "proved" | body text: OK everywhere. Headings: 3 bare "reprove(d)" (F1--F3), fixed |
| in general "invokes JL"; Hyp.X literature proof uses JL; [RS, §3.10.1] locator | OK: whycited, achieved, mainresults, plan, hypotheses.tex, HYPOTHESES.md (rows `Hyp.X.char`, `.gal`, `.iso`), f05b. Locator kept in whycited and f05b |
| route 1 (trace formula; planned, timing uncertain) / route 2 (geometric, without JL; new mathematics, unclear, open) | consistent. Full wording in whycited, plan, f05b; abbreviated "route 1 (trace formula, planned) or route 2 (geometric, open)" in achieved and mainresults (m2) |
| no "ours"/"new" on the first-case proof | OK. whycited, newknown, summary, achieved, mainresults, f05b, f16 all attribute the argument to Ribet (with Deligne--Rapoport, Deuring) and say what is ours |
| chapter statuses | Thm `s05-G` cited, Prop `s05-sign`(a) pmc, Thm `s03-ribet`(a) and Cor `s03-ihara` proved given (iii), Hyp `s05-X` hyp: quoted with these statuses in whycited, achieved, f05b. One tension with `rem:s05-Xstatus`: N1 |
| abstract ≤ 150 words | 149 with each formula counted as one word (source). A whitespace count of the rendered PDF text gives 158 ("D = q", "q ≡ −1 mod p" split into several tokens): m1 |
| anonymity | `flatten.py --check report.tex`: A6 PASS, A13 PASS. "Fabian"/"Januszewski"/"Abhijit" in `report.tex` only in lines 211--213 (title block: `\author`, acknowledgment `\thanks`) |

## Findings applied

**F1 (major, APPLIED) `chapters/s00/whycited.tex`, subsection title.** "Classical JL: reproved in the first case, cited in
general" has a bare "reproved" (it also appears as the heading in `report.tex`). Replaced by
`\subsection{Classical JL: first case modulo cited geometry; cited in general}`.

**F2 (major, APPLIED) `talk/slides/f02-jl.tex`, block title.** "first case reproved: frame 6" is a bare "reproved" on the
first content slide. Replaced by `first case: frame 6` (the long form "reproved mod. cited geometry" gave an overfull
vbox of 12.5pt). In the same line the quote attribution had lost "problem text" (the quoted sentence is the problem
text, not a sentence of JL or Bergeron); restored: `\hfill[problem text; JL, LNM 114; Bergeron, Ch.~8]`.

**F3 (major, APPLIED) `talk/slides/f05b-jlproof.tex`, frame title.** "Why classical JL is cited --- and where we reprove
it" replaced by `Classical JL: first case modulo cited geometry; cited in general` (same as F1).

**F4 (minor, APPLIED) `talk/slides/f16-new-known.tex`, open column.** "JL in general (routes 1, 2)" reads as if JL itself
were open. Replaced by `removing the JL input (routes 1, 2)`.

## Findings NOT applied (team decision needed)

**N1 (major for consistency, NOT applied: the decision is binding and chapter s05 is outside this diff).**
`chapters/s05/sign.tex`, Remark `rem:s05-Xstatus` says that at Γ₁(Mp^s)∩Γ₀(q)-level "(X1)--(X4) are expected by the same
proofs" (status expected), i.e. by the Deligne--Rapoport/Deuring geometry of the Γ₀ case, which whycited says "does not
pass through JL". The new s00 text says "the current literature proof of its content uses JL" and calls a JL-free
discharge "new mathematics, whether possible is unclear". No s05 chapter states that the literature proof of Hyp.X uses
JL (s05/status.tex lists the literature search and does not mention it), and [RS, §3.10.1] is cited only in whycited. A
reader of both places sees: expected by the JL-free geometric proofs (s05) versus JL-free discharge unclear (s00).
Suggested reconciliation, to be decided by the team, in `rem:s05-Xstatus` after "expected by the same proofs \stexp":
`(we have not carried this out; the literature route to the content of $\HypX$ that we know passes through JL, see \S\ref{ss:s00-whycited})`.
This changes a chapter that the report quotes, so it was not applied.

**N2 (moderate, NOT applied: it is the decision's own wording).** Route 1: "would discharge `Hyp.JLClassical` and with it
the JL input to the current proof of Hyp.X" (whycited, plan, hypotheses.tex, HYPOTHESES.md, f05b). `Hyp.JLClassical` /
Thm `s01-JLclassical` is JL for the *definite* algebra in Brandt form; the JL that enters at the Shimura curve of
discriminant pq [RS, §3.10.1] is for an *indefinite* algebra. Discharging the registered hypothesis as stated does not
by itself give that input; the trace-formula comparison would have to cover that algebra as well. All sentences are
conditional ("would", "planned; timing uncertain"), so nothing is claimed as done. Suggested addition in whycited after
"the JL input to the current proof of $\HypX$": `(provided the comparison is carried out for the quaternion algebra occurring there)`.

## Minor, NOT applied

**m1 abstract length.** 149 words with formulas as single words; 158 by a whitespace count of the PDF text. If the
organisers count mechanically, trim e.g. "(open for $q\equiv-1\bmod p$ outside the level conditions (Lev))" to
"(open in one residual case)" and "Computations: Python/PARI and HACS." to "Computations: PARI, HACS." (about −9 tokens).

**m2 `achieved.tex` item (a), `article/mainresults.tex` item (a).** Route statuses abbreviated. For full agreement with the
decision: `route~1 (trace formula; planned, timing uncertain) or route~2 (geometric, without JL; new mathematics, \stopen)`.

**m3 `achieved.tex`, table row (a).** "classical JL for $D=q$, weight~$2$ (proved modulo cited geometry)" stands in the
column "main result" without attribution (the item text above has it). Replacement:
`classical JL for $D=q$, weight~$2$ (Ribet's argument; \status{proved modulo cited geometry})`.

**m4 scope tag and one unresolved reference.** (i) abstract, summary, limitations, prior, newknown and the achieved table
say "($D=q$, weight~$2$)" without "$\Gamma_0$-type level" (the decision's own abstract sentence does the same;
whycited, achieved text, motivation, mainresults and f05b have the full tag). (ii) `article.pdf` shows "§??" in
whycited, route 1 (`\ref{ss:stage2-hyp}`; `plan.tex` is not part of the article). This predates the decision commit.
Fix, if wanted, in `whycited.tex`: replace `(\S\ref{ss:stage2-hyp})` by `(the stage-2 plan)`; this needs a new
page-shift check.

Not checked: the mathematics of the claim itself (that Ribet's argument with Deligne--Rapoport and Deuring yields the
module isomorphism of Thm `s01-JLclassical` for $D=q$, $k=2$, including multiplicities), the literature claim that the
proof of Hyp.X uses JL, and `mathematics/final-report/` (not rebuilt; it does not input whycited).

## Rebuilds

- `mathematics/main.pdf`: rebuilt (latexmk, fresh dir), 192 pages before and after. Page-by-page `pdftotext` compare with
  the committed PDF: only page 3 differs (the new subsection title and the reflow of its paragraph); first and last
  words of every page unchanged. **Pages did not shift.**
- `mathematics/submission/report.tex`/`report.pdf`: re-flattened (`flatten.py src/report-src.tex --draft --external-aux`
  with the fresh `main.aux`): 0 FAIL, 3 WARN (A5 title-block hash/placeholders, A7 section order, A11 placeholders), 19
  PASS; 317 refs redirected, 0 external-only; self-test compile OK; 187 pages before and after, only page 4 differs.
  The `report.tex` diff is the one heading line.
- `mathematics/article.pdf`: rebuilt in a fresh dir, 187 pages before and after; one "§??" (m4(ii), as before).
- `talk/main.pdf`: rebuilt, 18 pages, 0 overfull boxes.
