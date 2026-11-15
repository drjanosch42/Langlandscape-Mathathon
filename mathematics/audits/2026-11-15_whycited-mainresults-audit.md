<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Audit: `chapters/s00/whycited.tex` and `article/mainresults.tex` against the chapters

Date 2026-11-15. Branch `final/audit-why` (from `wip-submission` 12efd6f2). Independent read; no new mathematics.
Method: every `\ref` in the two texts was resolved to its label in `chapters/`, and the status printed next to the
reference was compared with the status line of the labelled statement (and, for `mainresults.tex`, also with
`chapters/s00/achieved.tex`). The [RS, §3.10.1] claim was checked against the local copy of Ribet–Stein (not quoted
here). The Lean paragraph was compared with `chapters/s00/plan.tex`, `lean/Langlandscape/HYPOTHESES.md`, the
hypotheses appendix and a grep of `lean/Langlandscape/` for consumers of `Hyp.JLClassical`.

## Verdict

**PASS after fixes.** No status is upgraded in either text. Three major findings (two wrong factual statements in
`whycited.tex`, one claim beyond the chapters in the "Route" paragraph of `mainresults.tex`) were found and
**applied**. Six minor findings are listed with replacement text and **not applied**. No critical finding.

## 1. `whycited.tex`: reference and status table

| Reference in the text | Number in `main.pdf` | Status in the text | Status at the label | OK |
|---|---|---|---|---|
| `thm:s01-JLclassical` | Thm 6.1 | cited | cited (JL Thm 16.1 and others) | yes |
| `thm:s05-G` | Thm 18.30 | cited | every clause (i)–(v) cited | yes |
| `prop:s05-sign`(a) | Prop 18.6(a) | proved modulo cited | (a), Γ0-level weight 2: proved modulo cited | yes |
| `thm:s03-ribet`(a) | Thm 10.2(a) | proved given (iii) | "Given (iii): (a) … proved" | yes |
| `cor:s03-ihara`(i),(ii) | Cor 10.5 | proved given (iii) | "proved for (i), (ii) given (iii)" | yes |
| `hyp:s05-X` | Hyp 18.15 | hypothesis | hypothesis ("never an axiom") | yes |
| `rem:s02-CD` | Rem 7.24 | cited, never used | cited; "The tree route never uses this remark" | yes |
| `conj:s06-several` | Conj 25.2 | conjectural | conjectural | yes |
| `prop:s05-nochain`(b) | Prop 18.28(b) | proved | proved (induction on the construction) | yes |
| `prop:s05-Xlambda`(a) | Prop 18.20(a) | proved given Hyp.X.char | proposition assumes Hyp.X.char; (a) "proved given if:s04-ekills(a)" | yes (see m6) |
| `thm:s01-chenevier`, `thm:s01-lambdaJL` | Thm 6.2, 6.3 | cited | cited | yes |
| `ss:s00-hope`, `ss:s00-why`, `ss:s00-map`, `ss:s00-route`, `ss:stage2-hyp` | sections | — | exist, content matches the use | yes |

Other checks:

- **Problem text.** The quoted desired outcome ("a new approach to the construction of the Jacquet–Langlands functorial
  transfer and the characterization of its image") and the paraphrase "a new approach or, failing that, a Lean
  formalization of the trace-formula proof" agree with the verbatim text in `chapters/s00/motivation.tex` (the
  quotation lower-cases the initial "A" and typesets the hyphen in "Jacquet-Langlands" as an en dash). OK.
- **[RS, §3.10.1].** In the local copy, §3.10.1 ("Shimura curves", preprint p. 47) introduces the Shimura curve of
  the indefinite algebra of discriminant pq and invokes the work of Eichler, Jacquet–Langlands and Shimura (with
  Faltings) for the map between the two Jacobians; the semistable-reduction sequence (3.1) and Lemma 3.17 of §3.9 are
  attributed there to Raynaud and Deligne–Rapoport, without JL. The sentence "JL enters Ribet's programme for the
  Shimura-curve comparison at discriminant pq" is supported. The text does not say "only", and it should not: the
  source does not make an exclusivity statement. OK as written.
- **Disclaimer.** "We have not checked the whole chain of cited geometric results for an implicit use of JL, so
  *we do not claim* that this is a proof of JL modulo the geometry" is present. OK.
- **Čerednik–Drinfeld** "cited, never used" agrees with the title and last sentence of Remark 7.24 and with
  `route.tex`. OK.
- **Lean paragraph.** "formalized only as a schematic interface" agrees with the Lean status after Thm 6.1 and with
  HYPOTHESES.md ("open (schematic)"). "Status: planned; timing uncertain" is verbatim the status of group (C) in
  `plan.tex`. The planned route (completion of the prior GL(2) trace-formula formalization, the comparison with the
  quaternionic side, a non-schematic statement) agrees with `plan.tex` (C). One wrong clause: M2 below.
- **Closing sentence.** Not an upgrade (both parts are qualified), but imprecise: m1 below.

## 2. `mainresults.tex`: items (a)–(e)

Each status was compared with `achieved.tex` and with the label.

| Item | Reference | Status in the text | `achieved.tex` | Label | OK |
|---|---|---|---|---|---|
| (a) | `thm:s05-G` | cited | cited | cited | yes |
| (a) | `prop:s05-sign`(a) | pmc | pmc | pmc | yes |
| (a) | `thm:s03-ribet`(a) | proved given (iii) | same | same | yes |
| (a) | `cor:s03-ihara`(i),(ii) | proved given (iii) | same | same | yes |
| (a) | `hyp:s05-X` | hypothesis; open as a whole | same | hypothesis | yes |
| (a) | `prop:s05-Xiso` | pmc, "at good m" | same | pmc under assumptions (i)–(iii) | yes |
| (a) | `conj:s05-O2` | conjectural, open | same | conjectural; open | yes |
| (a) | `rem:s05-degree` | sketched | sketched | sketched (degree count only) | yes |
| (a) | `thm:s01-JLclassical` | cited | cited | cited | yes |
| (b) | `thm:s01-chenevier` | cited | cited | cited | yes |
| (b) | `rem:s05-O7` | sketched; beyond ordinary: open | same | sketched; O7 open | yes |
| (c) | `thm:s04-control`(a) | proved | proved | (a) proved | yes |
| (c) | `thm:s04-lambdaribet`(a) | proved given connectivity for all s | same | same (plus stage-03/04 inputs) | yes |
| (c) | `prop:s05-Xlambda`(a) | proved given Hyp.X.char | same | see m6 | yes |
| (c) | `thm:s01-lambdaJL` | cited | cited | cited | yes |
| (c) | (c2) | open | open | open | yes |
| (d) | `thm:s06-defect` | pmc under the standing hypotheses; open for q ≡ −1 mod p outside (Lev) | longer form | pmc under (H0⁻); under (Lev) pmc in (F0), (F1), (F1′); open outside | yes (see m3) |
| (d) | `thm:s06-E` | proved; formalized in abstract form, (i)–(iv), with exceptions | same (table row) | proved; formalized with the listed exceptions | yes |
| (d) | `prop:s06-galois` | pmc | pmc | pmc | yes |
| (d) | `prop:s05-subquot` | proved, formalized | same | proved; formalized (sorry-free) | yes |
| (d) | `prop:s03-mazur` | pmc | pmc | pmc | yes |
| (d) | `prop:s03-phieis` | proved | proved | proved | yes |
| (d) | `conj:s06-several` | conjectural | conjectural | conjectural | yes |
| (e) | `def:s02-BG`; computations | computed | computed (itemised) | definition; well-definedness proved | yes (see m4) |

"Stages." paragraph: agrees with the first sentence of `outline.tex` (01→02→03→04, then 05 and 06; stage 06 does not
use Hyp.X). No claim beyond the chapters. OK.

"Route." paragraph: M3 below.

## 3. Findings

### Critical
None.

### Major (all APPLIED)

**M1 (`whycited.tex`, line 5): wrong seed item.** The text said "item (i) of the seed". In
`plan/seed/towards_simplicial_jl.tex` the list is (i) maps in both directions, (ii) integral, (iii) "it specialises to
the classical (semisimple) JL over C". Classical JL over C is item (iii).
- old: `item (i) of the seed`
- new: `item (iii) of the seed`

**M2 (`whycited.tex`, Lean paragraph): "passed as an explicit argument" is not true of `Hyp.JLClassical`.**
HYPOTHESES.md lists no consumer ("— (target statement; schematic interface …)"), the hypotheses appendix says "No Lean
consumer; it is a target statement", and in `lean/Langlandscape/` the name occurs only in its own file, the root
import and `Audit/PrintAxioms.lean`. The old wording suggested that Lean theorems are proved under classical JL.
- old: `\texttt{Hyp.JLClassical}, passed as an explicit argument; it is`
- new: `\texttt{Hyp.JLClassical}, a target statement with no Lean consumer; it is`

**M3 (`mainresults.tex`, "Route."): claim beyond the chapters.** "All results above are obtained on the definite
side" contradicts `achieved.tex`, which says that (d) is proved "by commutative algebra and Galois theory on the GL_2
side", and item (a) itself, whose Γ0 comparison is the cited geometric Thm 18.30. Also "its finite quotient BG(U,q)
(Prop 7.9, proved)" dropped the condition (iii) that `route.tex` states ("given the connectivity condition (iii)"),
and Hyp.X was missing from the places where bad reduction enters (`route.tex`: "a genuinely geometric input").
- new paragraph:
  `\paragraph{Route.}\label{ss:s00-route} The definite-side results above are obtained from the action of the`
  `$\{q\}$-arithmetic group $\GU$ on the Bruhat--Tits tree $\cT_q$, whose quotient is, given (iii), the finite Brandt graph`
  `$\BG(U,q)$ (Prop.~\ref{prop:s02-BG}, \stproved), instead of from bad reduction of modular and Shimura curves; the latter`
  `enters only through cited results such as Thm.~\ref{thm:s05-G} and through the hypothesis $\HypX$. The defect formula of`
  `item~(d) is obtained by commutative algebra and Galois theory on the $\GL_2$ side, modulo cited results.`

### Minor (NOT applied)

**m1 (`whycited.tex`, closing sentence).** "The first case" is defined two paragraphs earlier as D = q, weight 2,
level Γ0(qM); the Γ1(Mp^s)-level is not part of it, and "answered relative to Hyp.X" means conditionally on an open
hypothesis. Suggested:
`So item (a) is answered only for $D=q$: in weight~$2$ at $\Gamma_0$-type level relative to the cited geometry, and at`
`$\Gamma_1(Mp^s)$-level conditionally on the open hypothesis $\HypX$; it is not answered in general.`

**m2 (`whycited.tex`, line 14–15).** The level is written Γ0(qM) and then J_0(qM′), U_0(M′). Suggested: `level
$\Gamma_0(qM')$`.

**m3 (`mainresults.tex`, (d)).** "open for q ≡ −1 mod p outside (Lev)" omits "with ρ̄ unramified at q" (if ρ̄ is
ramified at q, (H0⁻) holds and the theorem is proved modulo cited). This understates, it does not upgrade. Suggested:
`\stopen{} for $q\equiv-1\bmod p$ with $\bar\rho$ unramified at $q$ outside (Lev)`.

**m4 (`mainresults.tex`, (e)).** "and they were computed" reads as "all were computed"; `achieved.tex` lists the
computations and records that regression C2 is partial (131 of 319 cases). Suggested: `and they were computed in the
cases listed in the chapters (\stcomp; result files under \texttt{code/results/}; regression C2 partial).`

**m5 (`whycited.tex`, Lean paragraph).** The parenthesis `(lean/trace-formula-project-import/)` after "our prior GL(2)
trace-formula formalization" suggests that this directory is the prior project; `plan.tex` says about 170k lines, of
which about 30k are imported here. Suggested: `(about 30k of its lines are imported in
\texttt{lean/trace-formula-project-import/})`. Related: the "discharge plan" column of HYPOTHESES.md for
`Hyp.JLClassical` reads "not to be discharged in this project (cited)", while `plan.tex` (C) and this paragraph plan a
discharge in stage 2. The two can be read consistently (the event versus the two months after it), but the registry
should say so; `lean/` was not to be edited in this audit.

**m6 (both texts, Prop 18.20(a)).** The label prints "proved given if:s04-ekills(a)" under the standing assumption
Hyp.X.char; both texts (and `achieved.tex`) write "proved given Hyp.X.char". The stage-04 lemma is a result of the
chapters, so this is not an upgrade; a remark only. Similarly, Prop 7.9 is "proved" with the connectedness of the tree
cited for one direction, as `outline.tex` records.

## 4. Builds

- `main.pdf` rebuilt (`latexmk -pdf main.tex`, no undefined references). Page-by-page `pdftotext -layout` comparison
  with the committed `main.pdf`: 192 pages before and after; only page 3 differs (the two edited sentences); no page
  boundary moved. **Pages did not shift.**
- Report re-flattened (`python3 -I tools/flatten.py src/report-src.tex --draft`): 0 FAIL, 3 WARN (A5 title-block
  commit hash/placeholders, A7 section order, A11 placeholders; none of the three concerns the edited sentences; they were not compared with
  an earlier flatten run), 19 PASS. `report.tex` differs in 2 lines; `report.pdf` 187 pages before and
  after, only page 4 differs.
- Article rebuilt in a fresh scratch directory and copied to `mathematics/article.pdf`: 187 pages before and after;
  pages 2–7 reflow by two lines (the longer "Route." paragraph), pages 8–187 are identical.
