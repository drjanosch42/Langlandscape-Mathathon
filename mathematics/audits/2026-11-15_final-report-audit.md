<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Final-report consistency audit (2026-11-15)

Object: `mathematics/final-report/` (`final-report.tex`, `sections/*.tex`, `generated/*.tex`, `final-report.pdf`, 52 pp.)
on branch `final/report` at 170347b1. Independent audit; no new mathematics, no edits outside this file, no Lean build.

Sources used, in priority order: (1) `mathematics/chapters/s0{1..6}`; (2) `code/results/**/*.json`; (3) the gated Lean
tree 4405815 (`git show` / `git grep`) and `origin/titan/s06-final-1:lean/Langlandscape/.titan/out/` (`c-axioms.log`,
`summary.txt`); (4) the six milestone closures, `runs/s0*.md`, the two HACS lane closures, `agents/status/STATE.md`;
(5) `mathematics/notes/hsieh-sign.tex`.

Paths below are relative to `mathematics/final-report/` unless they start with a top-level directory.

## Verdict

**FAIL as it stands: 3 blockers (B1–B3).** All three are one-line text corrections; nothing mathematical is wrong and no
box statement is altered. With B1–B3 applied the verdict is **PASS with remarks** (6 major, 14 minor).

Counts: blocker 3, major 6, minor 14. Section F: 2 stale `\leanplanned`-type labels in chapters s01–s05 (plus 5 in s06,
outside the requested range, listed for completeness).

## What was checked and found correct

- **Extraction (A).** `tools/extract_statements.py` was re-run into a scratch directory against an independent `main.aux`
  (worktree `impl`): all 32 box bodies and all 88 table rows are byte-identical to the committed `generated/*.tex` apart
  from seven page numbers (the scratch aux is from an older build). So every box body is the chapter text; no status
  marker inside a statement is changed, upgraded or dropped. The remaining problems under A are of a different kind
  (M1: statuses that the chapter prints *after* the environment; m1–m3: page numbers).
- **Gates (B).** `c-axioms.log`: 836 lines, 836 distinct declarations, `printed=836 expected=836 nonstandard=0`; 811 lines
  with the full triple (8 of them wrapped over several lines), 23 with a subset (19 × `[propext, Quot.sound]`,
  4 × `[propext]`), 2 "does not depend on any axioms"; no `sorryAx`, `ofReduceBool`,
  `trustCompiler`. `summary.txt`: 4194 jobs, rc 0, 319 s, 4 530 228 kB; warnings 181 / 71, 0 in the stage-06 files;
  `check_wp` 32 files; one `sorry` (`AlgJL/VolIII/P2/Instances.lean:1815`). The second import `sorry`
  (`BrandtInstances.lean:783/794`, `hecke_d11_weight4`, not imported) is as stated. The per-stage gate table
  (161; 195; 519; 592; 747; 836 and the tree shas) agrees with the six closures.
- **Hypotheses (B).** `HYPOTHESES.md` at 4405815: 28 rows `Langlandscape.Hyp.*` + `GL2TF.Hyp.EichlerMass` + one alias
  row = 29 registered hypotheses. All 29 rows of Table `tab:hyps` agree with the registry in name, stage, status and
  instance name; `PadicOrdDecomp` discharged, `ResidualBurnside` conditionally discharged, 27 open. The 13 test
  instances behind the table (the four named ones and the nine stage-06 toys) exist at 4405815. (Exception: the wording on closedness, M4.)
- **S06 Lean claims (B).** Checked against the source at 4405815 and the axiom log, each with (i) existence, (ii) axiom
  line, (iii) statement:
  `isGorenstein_iff_cyclic`; `NewOldData.split_iff` (second equivalence only, as the report says);
  `isGorenstein_of_isGorenstein_quotient`; `ThmE.theta_mem_b`, `mk_theta_mem_ann`, `eta_eq_span_lambda'`,
  `c_eq_orderIdeal` (i); `eta_eq_c_mul_of_unimodular` (ii); `unimodular_of_isGorenstein`,
  `eta_eq_c_mul_of_isGorenstein`, `eta_eq_c_mul_of_dvr`, `exists_unimodular_of_dvr` (iii, both halves);
  `c_principal_iff_isGorenstein` (iv, for `Module.Free A (S ⧸ 𝔞)`); `EtaPrinciple.isGorensteinWith_of_pairing`,
  `congruenceIdeal_eq_span_pairing`; `Defect.defect_formula`, `defect_formula_of_le`, `cor_fixed`, `cor_allweights`,
  `galois`, `freeRankTwo_of_le`, `freeRankTwo_iff_le`; `Hyp.residualBurnside_of_absIrred`. All exist, all have the
  standard triple, and the report's per-part description of Thm E, Lemma D, the splitting lemma, the Galois half and
  the `ResidualBurnside` discharge is accurate. The three "not formalized" items of Thm E are indeed absent from the tree.
  The disclosure sentence is verbatim in chapter (`prop:s06-galois`), registry and docstring.
- **Computations (C).** Every number of `sections/computations.tex` was recomputed from the JSON files (or, for the two
  items the report assigns to the Lane B closure, read there). Correct: `symn` 66/66; `pi_sign` 8 cells all plus;
  `levels` 2, 50, 1250; `validation` 240 all pass; `torsion` ℤ/3; `T1` h = 2,3,3,9,12 and 5,11,3,25,65; `betti_det` 121
  cases, none vanishing; `C3_rerun` 14/14; `H6_sign`; `C2` rank 1; `T05-1` 144/144, 0 minus, 0 unmatched, 70 + 74 lines;
  `T05-2` four pairs; `T4_hecke` lengths 1,1,1,1,2 and dim 1,2,3,5,10; xcheck lengths 1,1,1,1,2; `T4_betti` (ℤ/17)² at
  k = 12, 28, 44, 60, `expected` tags at k ≥ 17, k = 124 not reachable, off-route (ℤ/17²)²; `T5` seven triples, 7/7 at
  weight k with ord η = ord c = t = 1, ord η^new = 0, v_p(η^B) = 0, 4/7 at k + p − 1, rank 1 of 2; `C4i` 131/319, 225/225,
  396/396 DVR rows, 5 of 46 non-DVR rows at p = 2, 3; `C1`; `H3` four vacuous M = 1 triples, eight M > 1 cases, all
  differences 0, exactly five cases with t = 2; `definite_local` 14 cells; `gl2_dnew` 152/204, 52 skipped, 1283.9 s =
  21.4 min; Lane B: 14 exact Mazur agreements (recomputed from the per-orbit orders, 2- and 3-parts included), the
  D = 13, k = 8 module of order 37 between `x − 10` and `x² + 19x + 6`, 69/69 orbit Smith lists, 30.7 s + 30.3 s; from the
  closure: 64.7 s vs 0.02 s, 61 s vs 0.025 s, 109/109 in 178 s, 80/80 for q ≤ 479, 404 primes in 19.6 min, 1229 primes,
  deviations D1–D8. (Exception: B3.)
- **Hsieh section (D).** Agrees with the note: [Hs] prints `JL(U_q) = (−1)U_q`, the corrected relation is `+U_q`,
  Prop. 2.1 and Lemma 2.3 are the right numbers, 144 lines with 70/74, the three independent checks, the list of
  consequences, the "our reading, not a complete audit" caveat, the conjectural origin. The report does not repeat the
  S06 closure's misprint ("prints JL(U_q) = +U_q").
- **Open items (E).** Every item of `sections/open.tex` is in a closure or a chapter, and nothing that a closure lists as
  open is presented as done. Decisions FD1, FD2 and the lift of (F1), (F1′) agree with `STATE.md` lines 53 and 56.

## Findings

### Blockers

**B1. `xlambda_finite` is called "(unconditional)"; it is formalized modulo `Hyp.X.char`.**
Report: `sections/lean.tex:61–62`.
Source: `lean/Langlandscape/Langlandscape/Comparison/XLambda.lean:402` at 4405815,
`theorem xlambda_finite (hX : Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) (s : ℕ) (hs : 1 ≤ s) : Nonempty (…)`,
docstring "Status: *formalized* under `Hyp.X.char`"; chapter `mathematics/chapters/s05/hypX.tex:320`
("\stformal{} *conditional on* Hyp.X.char …, for an abstract `CharGroupData` G and not for X_q(J_s) itself … only an
existence (rank-level) statement"). The S05 closure's "unconditional via `ekillsA_tower_uncond`" means unconditional in
`Hyp.PadicOrdDecomp` only.
Fix: replace `the finite-level $\Lambda$-adic comparison \texttt{xlambda\_finite} (unconditional).` by
`the finite-level $\Lambda$-adic comparison \texttt{xlambda\_finite}, \emph{formalized modulo \texttt{Hyp.X.char}}, for an abstract \texttt{CharGroupData} (not for $X_q(J_s)$ itself) and as an existence statement only; it no longer depends on \texttt{Hyp.PadicOrdDecomp}.`

**B2. "the ordinary Ribet sequence and its inverse limit" is listed as formalized; the limit is formalized only modulo the surjectivity of the A-transitions.**
Report: `sections/lean.tex:58`.
Source: chapter box `thm:s04-lambdaribet` (`generated/statements-s04.tex`, "The limit statement of (a) is *formalized
modulo `Hyp.InvLimExact`* (and the connectivity argument) … This A-surjectivity is *not* formalized … (a) stays
\stproved{} (tex) and is not upgraded"); Lean `Ordinary/Limit.lean:502`,
`lim_exact_ribet (H) (hdec) (hconn : ∀ s ≥ 1, Tree.BGConnected …) (hA : ∀ n, Function.Surjective (H.transA n))`; S04
closure, open issues ("A-surjectivity on the concrete Ribet systems"). `sections/open.tex:33` already lists the gap, so
the report contradicts itself.
Fix: replace `control at finite level, the ordinary Ribet sequence and its inverse limit, Hecke operators with coefficients.` by
`control at finite level, the ordinary Ribet sequence at every finite level $s\ge1$ (connectivity of $\BG(UU_s,q)$ an explicit argument), its inverse limit \emph{formalized modulo \texttt{Hyp.InvLimExact}} (the surjectivity of the $A$-transitions is an argument and is not formalized), Hecke operators with coefficients.`

**B3. "among 32 integral Sym^n cells": the cited JSON gives 26 (of 60).**
Report: `sections/computations.tex:88`.
Source: `code/results/laneB/congruence_k.json` (`data.jl_cong`): 74 cells, 14 with k = 2 and 60 with k > 2; of the 60,
34 have `status: rank0` and 26 have `status: ok`. `code/results/laneB/py_reference.json` agrees (`cells_total 74`,
`cells_rank_gt0 40` = 14 + 26). The number 32 occurs only in the Lane B closure §2.2 and I could not derive it from
any field of either file (30 = even-k cells with k > 2; 26 = non-zero ones). The claim itself (one non-trivial module,
D = 13, k = 8, order 37) is confirmed by the JSON.
Fix: replace `among 32 integral $\Sym^n$ cells` by
`among the 26 non-zero integral $\Sym^n$ cells with $k>2$ (60 cells, 34 of rank~$0$; \res{laneB/congruence_k.json}; the lane closure prints 32)`.

### Major

**M1. Statuses that the chapters print after the environment are missing from five boxes and twelve table rows.**
Report: `sections/results.tex:5–12` ("including its status markers"), `final-report.tex` abstract ("with their status
exactly as in the chapters"); boxes `generated/statements-s02.tex:5, 14, 37, 64`, `generated/statements-s04.tex:115`;
`generated/results-table.tex:19–27, 47, 48, 50`.
Source: in `chapters/s02/2-quotient.tex`, `s02/3-cohomology.tex`, `s04/hsieh.tex`, `s04/vk.tex` the status paragraph
follows `\end{theorem}` / `\end{proposition}`, and the extractor stops at the `\end`. Consequences:

| label | shown in the report | chapter status (after the environment) |
|---|---|---|
| `thm:s02-SA` (box, table) | none / "--" | \stcited (Voight, Main Thm 28.5.3) |
| `prop:s02-BG` (box, table) | none / "--" | \stproved; connectedness of the tree (\stcited) enters in (i)⇒(iii) and the last clause of (b) |
| `prop:s02-quot` (box, table) | only the inner \stcited | (a) \stproved given (iii), \stpmc via Thm 7.7 and Hasse–Schilling; (b), (c) \stproved |
| `prop:s02-harm` (box, table) | none / "--" | kernel description \stproved given (iii); iso with H_1 \stpmc given (iii) (`Hyp.SerreCoh`) |
| `prop:s02-Mhomprops` (table) | "--" | \stproved |
| `prop:s02-duality` (table) | only \stformal | \stproved (and \stformal) |
| `prop:s02-coh` (table) | "--" | (a) \stcited, (b) \stpmc given (iii) |
| `prop:s02-free` (table) | "--" | (a) \stpmc, (b) \stproved given (iii) |
| `prop:s02-indefprops` (table) | "--" | (a) \stpmc, (b) \stpmc given (iii), (c) \stproved given (iii), (d) \stpmc given (iii) |
| `thm:s04-Gor` (box, table) | only \stexp | (i)–(iii) \stcited ([Hs, Thm 4.5 and proof, p. 34]); (iv) \stproved from (ii); Lean: `Hyp.HsiehGor`, cited, not discharged |
| `thm:s04-etaB` (table) | "--" | \stcited |
| `prop:s04-ekillsVk` (table) | "--" | **\sttoprove** (the transfer step is not written) |

No status is upgraded in print, but a cited theorem (SA, Hsieh's Gorenstein theorem) appears with no marker and an
unproved proposition appears as "--". Fix, either (a) in the tool: compute the body as the environment plus the
following text up to the next `\begin{proof}`, `\begin{remark|lemma|theorem|proposition|definition|interface}` or
sectioning command when that text starts with `\noindent`, `\begin{sloppypar}\noindent` and contains a status marker
(this reproduces the table above), and regenerate; or (b) by hand, adding to `sections/results.tex`:

- after line 19 (stage 02): `In this chapter the status paragraph follows each statement and is therefore not inside the box: Thm~7.7 \stcited{} (Voight, Main Thm.~28.5.3); Prop.~7.9 \stproved{} (the connectedness of $\cT_q$, \stcited, is used in (i)$\Rightarrow$(iii) and in the last clause of (b)); Prop.~7.10 (a) \stproved{} given (iii) and \stpmc{} via Thm~7.7 and Hasse--Schilling, (b), (c) \stproved; Prop.~7.19: the description as a kernel \stproved{} given (iii), the isomorphism with $H_1(\GU,V)$ \stpmc{} given (iii) (\texttt{Hyp.SerreCoh}).`
- after line 27 (stage 04): `Thm~16.6: (i)--(iii) \stcited{} \cite[Thm~4.5 and its proof, p.~34]{Hs}, (iv) \stproved{} from (ii); in Lean it is the registered hypothesis \texttt{Hyp.HsiehGor} (cited, not discharged). Prop.~18.1 is \sttoprove{} (the transfer step is not written); Thm~16.7 is \stcited.`
- in the caption of Table `tab:allresults` (tool, `cap`): append `A ``--'' means that the statement carries no marker, not that the result is proved: in stages 02 and 04 the status follows the statement (Thm~7.7 and Thm~16.7 are \stcited, Prop.~18.1 is \sttoprove).`

**M2. `sections/lean.tex` "What is formalized" lists stage 02–04 items without the qualifiers the chapters carry.**
Report: `sections/lean.tex:50–58`. The section defines *formalized* = compiles, standard axioms, no hypothesis.
Sources and fixes (replace the phrase on the left by the one on the right):

| line | report | source | replacement |
|---|---|---|---|
| 51 | `\texttt{prop:s02-quot}(a),(b),(c)` | `chapters/s02/2-quotient.tex`, Lean status after `prop:s02-quot`: (a) "\stformal given (iii)" / modulo SA, HS; (c) "for trivial coefficients … Not formalised: the traces, general V, Π_ℓ" | `\texttt{prop:s02-quot}(a) given connectivity (iii) (or modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}), (b), and (c) for trivial coefficients and the pull/push maps (not the traces)` |
| 51 | `graph homology and rank formula` | `Tree.finrank_Xindef_of_connected` takes `BGConnected` | `graph homology and the rank formula (given connectivity)` |
| 53 | `$\Phicomb$ Eisenstein` | box `prop:s03-phieis`: abstract core \stformal; `Ribet.phiComb_eisenstein_Ohat (hyp : Hyp.BrandtStabFree d ℓ)` | `$\Phicomb$ Eisenstein (abstract core; the instance at $\hat\cO^\times$ modulo \texttt{Hyp.BrandtStabFree})` |
| 53 | `the Mazur arithmetic` | box `prop:s03-mazur`: `Ribet.mazur_check` modulo `Hyp.EllipticCount`, `Hyp.EichlerMass` | `the Mazur arithmetic (the check on the DR graph modulo \texttt{Hyp.EllipticCount} and \texttt{Hyp.EichlerMass})` |
| 54–55 | `the definite Ribet sequence (a),(c) and Ihara (i),(ii) over any ring` | box `thm:s03-ribet`: "\stformal for (a) and the rank in (c)", "under `Tree.BGConnected`, or under SA∧HS∧BTtree"; `Ribet/Sequence.lean:77, 89, 96, 112` all take `hc : Tree.BGConnected …` | `the definite Ribet sequence (a) and the rank in (c), and Ihara (i),(ii), over any ring, given connectivity (\texttt{Tree.BGConnected}, or modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}, \texttt{Hyp.BTtree})` |
| 57 | `$e$ kills degree, vertex and component terms` | box `lem:s04-ekills`: (a) degree part \stformal; "(b), (c) only the abstract parts … with the graph inputs and Φ^comb ≅ ℤ/\|X_s\| as hypotheses"; not formalized: the H_0 clause | `$e$ kills the degree term; for the vertex and component terms the abstract forms only (graph inputs as hypotheses; the $H_0$ clause is not formalized)` |

**M3. The overview says "proves" where the boxes say \stpmc, \stcited, \stexp or \stopen.**
Report: `sections/overview.tex:25–26` (stage 02), `30–31` (03), `34–36` (04), `42–46` (06). The wording of stages 03, 04,
06 is taken verbatim from the chapter introductions `chapters/s0N.tex`, so it is faithful to that text; the sentence on
stage 02 ("proves that strong approximation at one level is equivalent to the connectivity") is the report's own. The
statuses are weaker: Prop. 7.9 uses the cited connectedness of the tree in (i)⇒(iii) and (ii) also contains the
surjectivity of X¹(U)→X_B(U); Thm 10.2(b) and Thm 11.3 are \stpmc; Thm 14.4(b) is \stcited / \stexp / \stsketch;
Thm 21.5 is \stpmc under Hyp. 20.1 and \stopen for q ≡ −1 mod p outside (Lev).
Fix: insert after `\end{description}` (`sections/overview.tex:47`):
`\noindent In these summaries ``proves'' is the wording of the chapter introductions. The status of each result is the one printed in \S\ref{sec:results} and is in several cases weaker: Prop.~7.9 uses the cited connectedness of the tree in one direction; Thm~10.2(b) and Thm~11.3 (Ihara (iii)) are \stpmc; Thm~14.4(b) (control at weights) is \stcited, in part \stexp; Thm~21.5 is \stpmc{} under the hypotheses of Hyp.~20.1 and \stopen{} for $q\equiv-1\bmod p$ outside (Lev); Prop.~18.20(c2) is \stopen.`

**M4. "Instance" is defined as a closed Lean term; for `X.char` and `X.gal` it is not.**
Report: `sections/lean.tex:102`, rows `125`, `127`; also `59` ("with non-vacuity instances").
Source: `HYPOTHESES.md` at 4405815, row `X.char`: "instance quantified over the context (d, …, Pq, hPq); not inhabited by
a closed term yet, audit R3-1" and "vacuity documented"; row `X.gal`: "no closed Lean term inhabits that context yet
(only `hurwitzData` exists, no `IsUniformiserElt` witness)". `sections/open.tex:37` says the same, so the report is
inconsistent with itself.
Fix: in line 102 replace `means a closed Lean term in the tests showing` by `means a Lean term in the tests showing`
and append `For \texttt{X.char} and \texttt{X.gal} the instance is a theorem quantified over a context $(d,\dots,P_q,h_{P_q})$ that no closed Lean term inhabits yet, so non-vacuity is relative to that context.`
In line 59 replace `with non-vacuity instances` by `with non-vacuity instances (for \texttt{X.char}, \texttt{X.gal} relative to an uninhabited context, see Table~\ref{tab:hyps})`.

**M5. `Defect.defect_formula` is a statement about an abstract `Defect.Setting`; (H1), (H2), (P), (Lev) are not Lean arguments.**
Report: `sections/lean.tex:77–79, 82–96` (and the abstract). For the commutative-algebra layer the report says that the
specialisation to Hecke rings is not formalized; for the Defect layer it does not.
Source: docstring of `Defect.defect_formula`, `Defect/Main.lean:131–141` at 4405815: "Hypotheses, all explicit as Lean
arguments except (H1), (H2), (P) and (Lev_M) (not representable on the abstract data, not arguments: they are the
conditions under which the cited `Hyp.*` are asserted …; likewise 'f = F_P is a q-new newform of weight 2 ≤ k ≤ p − 1')";
signature: `(D : Defect.Setting Λ I T 𝒪 G)` with arbitrary rings and a group `G`; `defect_formula_of_le` additionally
takes the literal inclusion `hle` and `hGor' : IsGorenstein I (D.R ⧸ D.𝔞)`, which are not registered `Hyp.*`.
Fix: append after the sentence ending `it is not an unconditional theorem.}` (`sections/lean.tex:84`):
`The Lean statement is about an abstract \texttt{Defect.Setting} (rings $\Lambda$, $I$, $T$, $\mathcal O$, a group $G$ and $\rho:G\to\GL_2(I)$); Hida's Hecke algebra and the Galois representation are not constructed in Lean, and (H1), (H2), (P) and (Lev) are not Lean arguments: they are the conditions under which the cited \texttt{Hyp.*} are asserted. \texttt{defect\_formula\_of\_le} takes in addition the inclusion $\cc_q(f)\subseteq\m^t$ and (Gor$_{R'}$) as plain arguments.`

**M6. The stage-04 box of the η-principle says the Lean file "does not exist yet"; the Lean section lists it as formalized.**
Report: `generated/statements-s04.tex:136–153` (box `prop:s04-etaprinciple`, \leanplanned) against `sections/lean.tex:75`
and `generated/results-table.tex:46`. Source: Section F, row 4 (the declarations exist at 4405815, are in the axiom
log and match (a), (b) in full). The box is a faithful copy of a stale chapter label; the chapter is not to be edited here.
Fix: add to `sections/results.tex` after line 27:
`The Lean note in the box of Prop.~17.1 is out of date: \texttt{CommAlg/EtaPrinciple.lean} exists in the gated tree 4405815 and both declarations named there are among the 836 audited ones (\S\ref{sec:lean}).`

### Minor

**m1. Page ranges of the stages and of the bibliography are off by one.** Report: `sections/pointers.tex:7–8`,
`sections/results.tex:15, 19, 23, 27, 31, 38`. Source: `mathematics/main.pdf` (`pdftotext`): stage headings on pp. 1, 24,
50, 82, 101, 134; stage 06 ends on p. 162 (Conjecture 25.2, as the box header itself says); "References" starts on
p. 163. Fix: `stage 01 pp.~1--24, 02 pp.~24--50, 03 pp.~50--82, 04 pp.~82--101, 05 pp.~101--134, 06 pp.~134--162; bibliography pp.~163--170`,
and the same ranges in `results.tex`.

**m2. Three box/table headers give the page before the statement.** `thm:s01-lambdaJL` p. 23 (is 24), `prop:s02-quot`
p. 31 (is 32), `prop:s05-Xlambda` p. 118 (is 119): `generated/statements-s01.tex:43`, `-s02.tex:37`, `-s05.tex:119` and
the three table rows. Cause: the `\label` whatsit is shipped on the previous page. The other 85 of 88 page numbers
are right. Fix: correct by hand after generation, or state in `results.tex:10` `(the page is that of the label; in three cases the statement starts on the next page)`.

**m3. `main.pdf` is called "the build of 4405815".** Report: `sections/results.tex:8`, `final-report.bib` (`LLmain`, note).
Source: `git log -- mathematics/main.pdf`: last rebuilt in b1c9abda ("update S06 chapter M1 Lean labels"), after
4405815; `chapters/s06/s06-m1.tex` differs from 4405815 (the boxes quote the new text). Fix: `(the build of b1c9abda: chapters as on this branch, Lean tree 4405815; 170 pp)`.

**m4. "`SORRIES.md` is empty".** Report: `sections/lean.tex:37`. Source: the file has an empty table for
`lean/Langlandscape/` and a second section with the two import `sorry`s. Fix: `(the table of \texttt{SORRIES.md} for \texttt{lean/Langlandscape/} is empty; its second section lists the two \texttt{sorry}s of the import)`.

**m5. "the nine stage-06 rows" among the 27 open hypotheses.** Report: `sections/open.tex:28–30`. Stage 06 has nine rows,
one of which (`ResidualBurnside`) is conditionally discharged and is not among the 27. Fix: `and eight of the nine stage-06 rows (\texttt{ResidualBurnside} is conditionally discharged)`.

**m6. `code/hacs/` "is code-identical to v0.2.1".** Report: `sections/overview.tex:64–65`. Source: Lane B closure §3 and
`code/hacs/CHANGES.md`: `Registry/JL/`, `cmake/jl/JL.cmake`, two marked hook lines (`CMakeLists.txt:1413`,
`ValidationRegistry.cpp`), regenerated CLI manual tables. Fix: `is code-identical to v0.2.1 apart from the Lane~B additions (the JL module, two marked one-line hooks and the regenerated CLI tables, all listed in \texttt{code/hacs/CHANGES.md})`.

**m7. Examples q = 101, 131 sit under "the 14 levels of the v2 records".** Report: `sections/computations.tex:82–84`.
The 14 levels are the primes ≤ 43; 101 and 131 come from the Python reference only, which records the order (25, 65)
and the valuations, not the group. Fix: `e.g.\ $q=11,23,37$: $\Z/5$, $\Z/11$, $\Z/3$; the Python reference (\res{laneB/py_reference.json}) gives in addition orders $25$ and $65=5\cdot13$ at $q=101,131$.`

**m8. T4 Betti side: which numbers come from HACS.** Report: `sections/computations.tex:38–41`. Source:
`s06/T4_betti.json`, `routes`: the gating Betti route is `amalgam.py` ("no HACS data"); the HACS route `module_Z()` is
"NOT RUN"; HACS `descent` supplies the Hecke side; `acceptance.pending_crosscheck: "S06-C3"`. (The S06 closure still
lists "T4 Betti side open"; the Lane A closure and the JSON supersede it.) Fix: after `(gating route: amalgam)` add
`; the cokernel is computed by the amalgam route, HACS supplies the Hecke side $\T(1)_\m/\delta$ through \texttt{descent}, and the HACS \texttt{module\_Z} route was not run`.

**m9. Index.** Report: `sections/computations.tex:3–5` ("index: `code/results/INDEX.md`"). `INDEX.md` has no row for
`laneB/congruence_k.json`, `laneB/py_reference.json`, `s04/C2.json`, and its row for `s06/brandt_free_block_z` says
`langlandscape_brandt/v1` (the files say v2, as the report does). Fix: add `(three files used below, \texttt{laneB/*.json} and \texttt{s04/C2.json}, are not yet in the index)`, or add the rows.

**m10. Hsieh correction: the non-trivial character case is a proof sketch.** Report: `sections/hsieh.tex:13`. Source:
note, after Prop. 2.1: "\st{proved} modulo \st{cited} inputs for trivial character …; for an unramified non-trivial
central character at q the same argument applies verbatim (proof sketch)". Fix: after `\cite[Prop.~2.1]{LLhsieh}` add
`; written out for trivial character, a proof sketch for a non-trivial character unramified at $q$`.

**m11. Declarations cited as formalized that are not among the 836 audited ones.** Report: `sections/lean.tex:5`
(definition of *formalized*), box `lem:s04-ekills`. Of the `\lean{}` names in the chapters, 9 (s01), 69 (s02), 5 (s03),
20 (s04) are not in `c-axioms.log`, among them the theorems `Ordinary.deg_comp_UpHom`,
`Ordinary.brandtPairing_eq_deltaPairing`, `Ordinary.ordPart_le_ker_of_vertex`,
`Ordinary.ordPart_tensor_phiComb_eq_bot`. All of them exist at 4405815 and compile; their axioms follow only indirectly
(steps (d) and (e) of the gate). No name cited in s05 or s06 library code is missing from the log. Fix: after
`standard axioms only;` in line 5 add `(checked by \texttt{\#print axioms} for the 836 headline declarations; for the other declarations named in the chapters by the \texttt{sorry} count and the forbidden-token grep)`.

**m12. T4 Hecke side: status of the prediction.** Report: `sections/computations.tex:34–36`. `INDEX.md` and
`T4_betti.json` mark the prediction 1,1,1,1,2 as *expected* for k ≥ 17, not gating. Fix: `equal to the prediction (expected for $k\ge17$)`.

**m13. Lane A golden tiers.** Report: `sections/computations.tex:74`. Closure: "run once at build time". Fix:
`passes the strict golden tiers (A 12154/0, B 6231/0; run once, at build time)`.

**m14. Table order.** `generated/results-table.tex:46–50, 52–60`: rows of stages 04 and 05 are in file order, not in
numerical order (17.1 before 16.6; 18.30 before 18.13). Cosmetic. Fix in the tool: sort the rows of a stage by the
number from `main.aux`.

## F. Stale Lean labels in the chapters (report only; nothing edited)

Columns: (i) declaration exists at 4405815; (ii) in `c-axioms.log` with the standard triple; (iii) statement matches.

| # | chapter location | label, text | Lean at 4405815 | (i) | (ii) | (iii) | stale? |
|---|---|---|---|---|---|---|---|
| 1 | `s01/4-hecke.tex:239–240` | `prop:s01-relations`: "Planned in Lean: … all \stformal" | `Brandt.PiEll_indep`, `heckeT_comm_of_disjoint`, `rightTranslate`, `heckeT_comm_rightTranslate` | yes | yes | not re-read | **wording stale** ("Planned in Lean" should read "Lean") |
| 2 | `s03/3-ribet.tex:116` | `thm:s03-ribet`(b), exactness with coefficients V, \leanplanned | `Ribet/Coeff.lean` has definitions and compatibilities only; no exactness theorem | no | – | – | not stale |
| 3 | `s03/4-ihara.tex:191` | `thm:s03-iharaH0`(b), \leanplanned, "it needs Hecke operators with coefficients, S04-L15a" | clause (b) is not stated; `Brandt/HeckeCoeff.lean` (`heckeTV`) exists | no | – | – | status not stale; the **reason is stale** (registry: "they exist now … clause (b) could now be stated; not done") |
| 4 | `s03/4-ihara.tex:307` | `cor:s03-eis`, `Ribet.eis_support_of_IharaH0`, \leanplanned | absent | no | – | – | not stale |
| 5 | `s04/etaprinciple.tex:35–36` | `prop:s04-etaprinciple`, \leanplanned, "this file does not exist yet" | `CommAlg/EtaPrinciple.lean`: `EtaPrinciple.isGorensteinWith_of_pairing`, `EtaPrinciple.congruenceIdeal_eq_span_pairing` | yes | yes | yes, (a) and (b) in full | **stale** → \stformalized |
| 6 | `s05/hypX.tex:320` | `prop:s05-Xlambda`: inverse limit, (b)–(d), Galois and monodromy, \leanplanned | `Comparison/XLambda.lean` has no limit statement | no | – | – | not stale |
| 7 | `s06/s06-m4.tex:24` | `lem:s06-burnside`, "stretch, \leanplanned" | `CommAlg.surjective_groupAlgebra_of_absIrred` | yes | yes | yes (absolute irreducibility as irreducibility over an algebraically closed K) | **stale** |
| 8 | `s06/s06-m4.tex:39` | `lem:s06-traceform`, \leanplanned | `CommAlg.eq_one_of_trace_mul_eq` | yes | yes | yes | **stale** |
| 9 | `s06/s06-m7.tex:35` | `lem:s06-twobytwo`, "optional S06-L14, \leanplanned" | `CommAlg.TwoByTwo.cokerEquiv`, `cokerEquivOfIsUnit` | yes | yes | part: the case H = T only | **stale**, with the qualifier "case H = T" |
| 10 | `s06/s06-m3.tex:190, 198` | "none is formalized yet"; "the Defect layer is to be formalized in `Defect/`" | `Defect/*.lean`, `Hyp/*.lean` | yes | yes | – | **wording stale** |

Rows 7–10 are outside the requested range s01–s05. The task's examples `thm:s03-ribet`, `thm:s03-iharaH0`,
`cor:s03-eis` are **not** stale: the gated tree does not contain these statements.

## Method notes

- Extraction: the tool was imported with `HERE` redirected to a scratch directory; `diff -r` against `generated/`.
- Axiom log: names parsed from `'…' depends on axioms` / `does not depend on any axioms`; every `\lean{}` name of the
  chapters and every `\texttt{}` declaration name of `sections/lean.tex` was looked up there and in
  `git grep` at 4405815.
- JSON: each file was loaded and the summary numbers recomputed from the rows where the file has rows
  (T05-1 sign split, `C4i` summary, Lane B per-orbit orders, H3 per-form differences).
- Not checked: the mathematics of any proof; the bibliography entries; the appended 20-page hypotheses report (it is
  reproduced unchanged and the report says that it is partly superseded); the talk; the literature.
