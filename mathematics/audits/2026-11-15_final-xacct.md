<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
verdict: FIX LIST; W = 3·crit + 2·maj + min = 3·0 + 2·7 + 18 = 32 (combined: Part G1 final report W = 14 [0 crit, 2 maj, 10 min, 7 note]; Part G2 talk W = 18 [0 crit, 5 maj, 8 min, 5 note])

# Batch 8: cross-account review of the final report and the talk

Request: `agents/messages/abhijit/archive/20261115-021557Z_fabian_batch8.md`. Object: `origin/wip-final` @ `170347b1`
(read-only detached worktree). Severity and row format as in batch 4, C2–C4: crit / maj / min / note,
W = 3·crit + 2·maj + min.

## Part G1: final report

Reviewer G1 (Opus, fresh, Abhijit's account). I wrote the findings **blind**: I read no audit of the final report under
`mathematics/audits/` or `plan/` before the findings table was finished. A Sonnet sub-agent checked the numbers against the JSON files
under the same blind rule. I re-checked its two non-matches myself.

**Sources checked at 170347b.** The six chapters (`mathematics/chapters/`) and `mathematics/main.pdf` (170 pp). The note
`mathematics/notes/hsieh-sign.tex`. All files under `code/results/**` that §4/§5 cite. The HACS lane closures
`plan/hacs/outbox/20261115T01{37,50}Z_lane{A,B}-closure.md`. The milestone closures S01–S06
(`plan/implementation/outbox/*milestone-closure-s0*.md`). `lean/Langlandscape/HYPOTHESES.md` and `Audit/PrintAxioms.lean` (836
`#print axioms` lines). The Lean sources under `lean/Langlandscape/` and the import. Lean is unchanged between 4405815 and 170347b
(`git diff --stat 4405815 170347b -- lean` is empty).

**What is clean.**
- **(i) §2 boxes are verbatim.** All 32 quoted boxes match the chapter environments at 170347b, after removing `\label` and
  mapping `\ref` to numbers (script check, 32/32 OK). The numbers and pages I sampled match main.pdf: Thm 19.8 p. 138,
  Thm 21.5 p. 146, Prop. 22.1/23.2, Rem. 23.8 p. 156, Prop. 24.1 p. 159, Conj. 25.2 p. 162, Prop. 17.1 p. 98, Conj. 12.10 p. 82.
- **(ii) Gate table (§3).** It matches the six closures: 161, 195/195, 519/519, 592/592, 747/747, 836/836; the shas; the sorry
  column. The final-gate details also match: 4194 jobs, 319 s, 4.53 GB, CONCEPTD 5:21, warnings 181/71, check_wp on 32 files.
- **(iii) Lean names (§3).** Every Lean name quoted in §3 exists, and every headline has a `#print axioms` line. The toy and
  non-vacuity instances exist in the tests.
- **(iv) Sorry locations.** `Instances.lean:1815` and `BrandtInstances.lean:783` are the declaration lines. The test-file importers
  are the two S01 test files, as stated.
- **(v) Hypothesis table.** The 29 hypotheses = 28 `Langlandscape.Hyp.*` rows + `GL2TF.Hyp.EichlerMass`; 27 are open. The
  statuses and instance columns agree with `HYPOTHESES.md`.
- **(vi) FreeRankTwo disclosure.** The sentence is verbatim identical in §3, in the box of Prop. 22.1 and in the appendix (p. 3).
  The binding wording "formalized modulo the registered Hyp.*, including the Galois half" is present.
- **(vii) Numbers (§4/§5).** 48 of the 50 checked numbers match (sub-agent table, condensed below). The two exceptions are X2 and
  X10.
- **(viii) Hsieh-sign location.** The note's numbering (§1 = statement, Prop. 2.1, Lemma 2.3, §4 = consequences) matches the
  pointers in §5.

### Per-section verdict

| section | verdict | findings |
|---|---|---|
| Abstract / §1 (outside the requested range; one item only) | FIX | X12 |
| §2 Results | FIX | X3, X4, X5, X6 |
| §3 Lean | FIX | X7 (also N1) |
| §4 Computations and HACS | FIX | X2, X10, X11 (also N3, N4, N6, N7) |
| §5 Hsieh sign | FIX | X1 |
| §6 Open items | FIX | X3, X8, X9 |
| §7 Pointers | FIX | X5 |
| Appendix (hypotheses report) vs §3 | OK | N2 |

Counts: crit 0, maj 2, min 10, note 7.

### Findings

| # | sev | location | cat | finding | evidence | exact replacement text |
|---|---|---|---|---|---|---|
| X1 | maj | `sections/hsieh.tex:127–131` (pdf §5, "The correction") | (a) | **The status is upgraded.** The report labels the corrected relation \stpmc for $\pi_q=(\mu\circ\det)\otimes\St$ with an arbitrary unramified $\mu$. The source proves it modulo cited inputs **only for trivial character**. For an unramified non-trivial central character it gives only a proof sketch. Hsieh's Λ-adic setting carries characters, so the general correction rests on the sketch. | `notes/hsieh-sign.tex:95–97`: "\st{proved} modulo \st{cited} inputs for trivial character (written out in our stage-05 chapter, Prop. sign (e)); for an unramified non-trivial central character at $q$ the same argument applies verbatim (proof sketch)." | Replace l. 127 `\paragraph{The correction} (\stpmc, i.e.\ \stproved{} modulo \stcited{} inputs; \cite[Prop.~2.1]{LLhsieh}).` by: `\paragraph{The correction} (\stpmc{} for trivial central character at $q$, i.e.\ \stproved{} modulo \stcited{} inputs; for an unramified non-trivial central character at $q$ the same argument is a \stsketch; \cite[Prop.~2.1]{LLhsieh}).` |
| X2 | maj | `sections/computations.tex:86–87` (§4.3 Lane B, "Census read") | (b),(c) | **The coverage claim is false as stated.** The text says "exactly … for every prime $q\le479$ (80/80 …)". There are $\pi(479)=92$ primes up to 479, so 80 levels cannot be all of them; the 80th prime is 409. The report copies the closure's wording, which has the same inconsistency. The run was stopped by the cap, so this is a partial coverage presented as complete. (The ℓ ≥ 5 claim, 109/109 levels = $\pi(600)$, is consistent.) | Lane B closure l. 83: "stopped by the 15-min cap after 80 complete cells (all primes q ≤ 479) … 80/80". Arithmetic: $\pi(479)=92$, $p_{80}=409$. | Replace `and exactly ($2$- and $3$-parts included) for every prime $q\le479$ (80/80, exact $\Z$ route; stopped by the 15\,min cap).` by: `and exactly ($2$- and $3$-parts included) on the 80 levels completed by the exact $\Z$ route before the 15\,min cap stopped it (80/80; all with $q\le479$, but not all primes up to $479$, since there are $92$ of them; partial).` (If the log shows which 80 primes were run, name the range instead.) |
| X3 | min | `sections/results.tex:139–141`; `sections/open.tex:158`; `sections/open.tex:201–202` | (c) | **Part of the q ≡ −1 open region is missing from the prose.** The prose names only $N(\bar\rho)>1$ as open. The chapter also leaves non-squarefree $M_0$ open ($\ell^2\mid M$ at a prime where $\bar\rho$ is unramified). The boxes say so (Hyp. 20.1, Thm 21.5), but the open-items list and the decisions line omit it, so a judge reading §6 alone would assume full coverage of the unramified case. | Box Hyp. 20.1: "Not included: $N(\bar\rho)>1$ and non-squarefree $M_0$, which are \stopen{} (Remark 23.8)". Box Thm 21.5: "outside (Lev) ($N(\bar\rho)>1$, or $\ell^2\mid M$ …) the theorem is \stopen". Remark 25.1(i) of main.pdf. | results.tex l. 140–141: replace `$N(\bar\rho)>1$ is \stopen{} and is not claimed` by `$N(\bar\rho)>1$ and non-squarefree $M$ ($\ell^2\mid M$ at a prime where $\bar\rho$ is unramified) are \stopen{} and are not claimed`. open.tex l. 158: replace `\item \textbf{$q\equiv-1\bmod p$, $N(\bar\rho)>1$}: \stopen{} (Remark~23.9 of \mainpdf;` by `\item \textbf{$q\equiv-1\bmod p$ outside (Lev)}: $N(\bar\rho)>1$, and non-squarefree $M$ with $\ell^2\mid M$ at a prime where $\bar\rho$ is unramified, are \stopen{} (Remarks~23.9 and 25.1(i) of \mainpdf;`. open.tex l. 202: replace `\stpmc; $N(\bar\rho)>1$ \stopen.` by `\stpmc; $N(\bar\rho)>1$ and non-squarefree $M$ \stopen.` |
| X4 | min | `sections/results.tex:109` | (b) | **The main.pdf build is misattributed.** The report says the box numbers are those of "the build of 4405815". The main.pdf at 170347b was rebuilt in b1c9abda, after s06-m1 was edited (its Lean labels changed to formalized with qualifiers). The boxes quote that later chapter text. Pages and numbers are unchanged (spot-checked). | `git log -- mathematics/main.pdf`: last commit b1c9abda. `git diff 4405815 170347b -- mathematics/chapters`: s06-m1.tex only. | Replace `(the build of 4405815, 170 pp)` by `(the build at b1c9abda, 170 pp; Lean tree 4405815)`. |
| X5 | min | `sections/results.tex:116,120,124,128,131,139`; `sections/pointers.tex:209–210` | (b),(d) | **Stage page ranges are off by one page at the shared boundaries.** Stage 02 ends on p. 50, 03 on p. 82, 04 on p. 101 and 06 on p. 162. Example: Conj. 12.10 (stage 03) is boxed as "p. 82" under the heading "pp. 50–81". Likewise Conj. 25.2 is on p. 162, outside "pp. 134–161". | main.pdf: the "Stage 03" heading is mid-p. 50, "Stage 04" mid-p. 82, "Stage 05" mid-p. 101; "References" starts on p. 162 after Conj. 25.2. | results.tex: `pp.~24--49` → `pp.~24--50`; `pp.~50--81` → `pp.~50--82`; `pp.~82--100` → `pp.~82--101`; `pp.~134--161` → `pp.~134--162`. pointers.tex l. 209–210: `stage 01 pp.~1--23, 02 pp.~24--50, 03 pp.~50--82, 04 pp.~82--101, 05 pp.~101--133, 06 pp.~134--162; bibliography from p.~162`. |
| X6 | min | `generated/statements-s04.tex:151–152` (box Prop. 17.1, `prop:s04-etaprinciple`) vs `sections/lean.tex:75` | (d) | **The η-principle box contradicts §3.** The verbatim box still says "\leanplanned … this file does not exist yet … the Lean names quoted above remain planned". §3 lists `CommAlg.EtaPrinciple` as formalized, and the gate agrees: closure S06 L17 is formalized, and PrintAxioms has 5 EtaPrinciple lines. The chapter is stale, not the Lean (no status upgrade). A judge sees the contradiction. | `chapters/s04/etaprinciple.tex:35–36`; `lean/Langlandscape/Langlandscape/CommAlg/EtaPrinciple.lean` exists; closure S06 "L17 `EtaPrinciple` … *formalized*". | Do not edit the generated box. After `\input{generated/statements-s04}` (results.tex l. 129), add: `\noindent\emph{Note.} The Lean remark in the box of Prop.~17.1 dates from stage~04. \texttt{CommAlg/EtaPrinciple.lean} was added in stage~06 (S06-L17) and is formalized (standard axioms; milestone closure S06, \texttt{PrintAxioms} at 4405815), see \S\ref{sec:lean}.` (Better: fix `etaprinciple.tex:35–36` and regenerate.) |
| X7 | min | `sections/lean.tex:72–74` | (c) | **Two qualifiers on Thm E are dropped.** The report has (iv) formalized without the chapter's qualifier "for $S'$ $A$-free". It also drops "under the hypotheses of Lemma 19.5 as the structure `NewOldData` (same qualifiers as there)". | Box Thm 19.8 (chapter s06-m1): "\stformalized{} for (i), (ii), (iii) (both halves) and (iv) for $S'$ $A$-free, under the hypotheses of Lemma 19.5 as the structure \texttt{NewOldData} (same qualifiers as there)." | Replace `\item Theorem~E (Thm~19.8): (i), (ii), (iii) (both the Gorenstein half and the DVR half) and (iv) formalized, as abstract` by `\item Theorem~E (Thm~19.8): (i), (ii), (iii) (both the Gorenstein half and the DVR half) and (iv) (for $S'$ $A$-free) formalized, under the hypotheses of Lemma~D as the structure \texttt{NewOldData} (with the qualifiers of Lemma~D), as abstract`. |
| X8 | min | `sections/open.tex:167` | (d) | **Ihara (iii)(b) is filed under the wrong status.** Under "Mathematics", it is grouped with the $\GL_2$ Betti-form Ihara lemma as \stexp. In the chapter, Thm 11.3 (Ihara (iii), including (b)) is \stpmc. Only its *Lean* side is open: (a) is the hypothesis `Hyp.IharaH0` and (b) is \leanplanned. Only Conj. 12.10 is \stexp. This mislabels a proved clause (a downgrade, but a wrong status). | Box Thm 11.3: "\emph{Status.} \stpmc{} … clause (b) is maths only here (it needs Hecke operators with coefficients, S04-L15a), \leanplanned". Box Conj. 12.10: \stexp. | Replace `\item Stage-03 items: Ihara (iii) clause (b) and the $\GL_2$ Ihara lemma in Betti form (\stexp);` by `\item Stage-03 items: the $\GL_2$ Ihara lemma in Betti form (Conj.~12.10, \stexp); Ihara (iii) (Thm~11.3) is \stpmc{} on paper, but in Lean clause (a) is the hypothesis \texttt{Hyp.IharaH0} and clause (b) is not formalized;`. |
| X9 | min | `sections/open.tex:175` | (d) | **The open-hypothesis list counts ResidualBurnside.** "27 of the 29 … are open; in particular … the nine stage-06 rows". One of the nine stage-06 rows is `ResidualBurnside`, which §3 calls *conditionally discharged* and excludes from the 27. | §3, `lean.tex:101`: "one is conditionally discharged (ResidualBurnside)". Table 2 has 9 stage-06 rows. | Replace `the three \texttt{Hyp.X.*} (stage 05) and the nine stage-06 rows.` by `the three \texttt{Hyp.X.*} (stage 05) and the eight stage-06 rows other than \texttt{ResidualBurnside} (conditionally discharged).` |
| X10 | min | `sections/computations.tex:88` | (b) | **The "32" cannot be checked from git.** "Among 32 integral $\Sym^n$ cells": the number is not derivable from `laneB/congruence_k.json`. That file has 74 cells: 14 at $k=2$ and 60 at $k>2$, of which 26 are `ok` (44 orbit lines) and 34 are rank 0. The number appears only in the Lane B closure §2. The rest of the bullet matches the JSON: $D=13$, $k=8$, $|C|=37$, the orbits $x-10$ and $x^2+19x+6$, and Res $=296=2^3\cdot37$ (recomputed). | Sub-agent check of `congruence_k.json` (`jl_cong`); Lane B closure l. 32: "(32 integral Sym^n cells)". | Replace `among 32 integral $\Sym^n$ cells` by `among the integral $\Sym^n$ cells at $k>2$ of the Lane~B run (32 cells per closure \S2; \res{laneB/congruence_k.json} records 60 cells at $k>2$, 26 of positive rank)`. Or reconcile the count with the JSON. |
| X11 | min | `sections/computations.tex:49–50` (C2 paragraph) | (c) | **"Observed, not proved" is dropped.** The text says "it fails in 5 of the 46 non-DVR rows (at $p=2,3$; there $S_\m$ is not Gorenstein)". That reads as an established fact; the chapter marks the non-Gorenstein statement "(observed, not proved)". The units (131 *cases* run, 882 *rows*) are also never explained, so "225/225 rows" next to "131 of 319 cases" puzzles a judge. | `chapters/s06/s06-m5.tex:325–326`: "fails in 5 of the 46 rows with $\cO_v$ not a DVR (at $p=2,3$), all with $S_\m$ not Gorenstein (observed, not proved)". C4i.json: 131 cases → 882 rows (orbit × prime) = 225 in-scope + 215 out-of-scope non-Eisenstein + 442 Eisenstein. | Replace `rows (at $p=2,3$; there $S_\m$ is not Gorenstein).` by `rows (at $p=2,3$; in all five $S_\m$ is not Gorenstein, observed, not proved).`. After `the PARI stack).` insert `A row is one (case, Galois orbit, prime) record; the 131 cases give 882 rows.` |
| X12 | min | `final-report.tex:44–47` (abstract); `sections/overview.tex:42–45` | (d) | **The abstract states the headline without status or scope.** It gives "the integral defect $(h_F)=\cc_q(F)=\tq_q(F)$ for $D=q$" as a stage result. It omits that the result is proved modulo cited results under (H0)–(H2), (P), (H0$^-$) or (Lev), and that $N(\bar\rho)>1$ is open. §1 says "proves". This is outside §2–§6, but it is the first thing a judge reads. | Box Thm 21.5: \stpmc{} under (H0$^-$), or under (Lev) in the cases (F0), (F1), (F1$'$); \stopen{} outside. | abstract: replace `the integral defect $(h_F)=\cc_q(F)=\tq_q(F)$ for $D=q$)` by `the integral defect $(h_F)=\cc_q(F)=\tq_q(F)$ for $D=q$, proved modulo cited results under explicit hypotheses)`. overview.tex l. 42: replace `\item[Stage 06: the integral Jacquet--Langlands defect] proves,` by `\item[Stage 06: the integral Jacquet--Langlands defect] proves (modulo cited results, under the standing hypotheses; \S\ref{sec:results}),`. |
| N1 | note | `sections/lean.tex:51` vs `sections/open.tex:176` | (d) | `prop:s02-quot`(a),(b),(c) is listed as formalized in §3, while §6 says "\texttt{prop:s02-quot}(c) for the traces" is not formalized. Both are true, but read side by side they seem to contradict. | — | lean.tex l. 51: `\texttt{prop:s02-quot}(a),(b),(c)` → `\texttt{prop:s02-quot}(a),(b),(c) (for (c) not the trace maps)`. |
| N2 | note | Appendix, hypotheses report p. 4 (Table 1, row `Hyp.ResidualBurnside`: "DIS … discharged") | (d) | The appendix table shows ResidualBurnside as plainly "discharged". Its own p. 3 text and §3 of the report say it is discharged only given absolute irreducibility. The appendix preface (`appendix.tex`) does not mention this. Otherwise the appendix agrees with §3: 29 hypotheses, 26 table rows, the FreeRankTwo sentence, KimOtaRT/(Lev), and $N(\bar\rho)>1$ open. | `standalone-hypotheses.pdf` p. 3 vs Table 1. | appendix.tex: after `29 registered hypotheses).` add ` In its Table~1, ``discharged'' for \texttt{ResidualBurnside} means discharged given absolute irreducibility, (H2).` |
| N3 | note | `sections/computations.tex:14` | (d) | `pi_sign.json`: 8/8 cells pass, but cell $(D,k)=(13,2)$ has no newforms (only the Eisenstein line), so 7 cells are non-vacuous. | `s01/pi_sign.json` grid. | Optional: add `(7 non-vacuous cells; $(13,2)$ has no newforms)`. |
| N4 | note | `sections/computations.tex:22` | (b) | "the ordinary $3$-new form 15a": the label 15a is not in `s04/C2.json`, which records only level 15, dim 1. The identification is plausible ($S_2(\Gamma_0(15))$ is one-dimensional). | `s04/C2.json` `A_rank_s1`. | Optional: `matching the unique newform of level 15 (15a)`. |
| N5 | note | `sections/results.tex:120` | (d) | "72 \lean markers (closure S02)" is the closure's count. The chapter at 170347b has 109 `\lean{` occurrences in `chapters/s02/`. | `grep -o '\\lean{' chapters/s02/*.tex \| wc -l` = 109. | Optional: `72 \verb|\lean| markers at the S02 closure`. |
| N6 | note | `sections/computations.tex:47–50` | (d) | Readability of the cases/rows units: see X11. | — | — |
| N7 | note | `code/results/INDEX.md` (referred to in §4 l. 4–5 as the index) | (d) | INDEX.md has no rows for `laneB/*.json`, although §4 cites them. Some provenance fields have no PARI version: `C3_rerun.json` is a HACS run, and `laneB/py_reference.json` has none. | Sub-agent check. | Optional: add the laneB rows to INDEX.md. |

**Numbers checked and matching** (sub-agent, quoted JSON values; condensed):
- **Stages 01–05.** `symn` 66/66; `pi_sign` 8 cells; `levels` 2/50/1250; `up_mf` R1_ok at $s=1,2$; `validation` 240/240; `torsion` $\Z/3$;
  `T1` $h$, $|\Phi|$, cyclic, Eisenstein; `betti_det` 121, never 0; `C3_rerun` 14/14; `H6_sign` $+1$; `C2` rank 1; `T05-1` 144/0/0, with
  the sign split 70/74 recomputed from the orbits; `T05-2` 4 pairs, $\varepsilon=-1$ fails.
- **T4 and T5.** `T4_hecke` lengths and dimensions, plus the xcheck; `T4_betti` $[1,1]$ at 12/28/44/60, "expected" at 28/44/60,
  124 unreachable, off-route $[2,2]$. T5: the seven triples, $v_p(\eta^B)=0$, the weight-$k$ 7/7 identities, the $k+p-1$ 4/7 with the
  three level-13 cases missing, and rank 1 vs 2.
- **C4i, C1, H3, definite_local.** `C4i` 131/319 (96/69/23 skipped), 225/225, 396 DVR, 5/46. `C1` toy and seed. `H3`: the four
  vacuous $M=1$ triples, the eight tuples, $\ord\cc-t^{\rm an}=0$, and $t=2$ exactly in the five named. $N(\bar\rho)>1$ for these five
  is supported by Remark 23.8(iii) of main.pdf. `definite_local` 14/14.
- **Lane A.** 66/66, 8/8, 152/204, 52 skipped, 8 ambiguous; 74 v2 records; golden tiers 12154/0 and 6231/0; 21.4 min.
- **Lane B.** 14/14 Mazur; the $\Z/5,\Z/11,\Z/3,\Z/25,\Z/5\oplus\Z/13$ examples; 109/109 (178 s); 69/69; 64.7 s vs 0.02 s; 404 and
  1229 (closure); self-test 8084/0.

**Status words: checked, no further finding.**
- The §2 prose on stages 05 and 06 (FD1/FD2; F1/F1′ lifted to \stpmc; F1′ "our reading R4") matches Remark 23.8 and the closure S06.
- In §6, the following match the chapters: (c2) \stconj/\stopen with six missing steps (Rem. 18.22 (i)–(vi)); Thm 18.30 \stcited;
  the hybrid dictionary \stpmc; Conj. 25.2 \stconj; Conj. 18.40 \stconj/\stopen; the (L3) route "not carried out"; $q=1741$ / $2311$;
  the off-diagonal slot $q^{2-k}$ untested (`s03/5-amalgam.tex:250`); `cor:s06-allweights` needs $\cc\ne0$.
- §4 states that the HACS numbers are computed and nothing is "certified", and it discloses the Lane A/B deviations D1–D8. The
  T4 Betti "expected" tags at $k\ge\ell$ match Prop. 24.1's range $p>k$.
- No upgrade was found in §3. Every "formalized" claim there is backed by the gate. The Defect layer is always "formalized modulo
  registered hypotheses".

## Comparison

I searched after the findings were written. No audit of the final report exists: at 170347b, `git grep -l final-report`
over `mathematics/audits/` and `plan/` finds nothing, and the same search at the current `origin/wip-final` head d32002c6 also
finds nothing. So **every finding X1–X12 and N1–N7 is NEW**, with none KNOWN or KNOWN-BUT-UNFIXED.

**`wip-final` has moved on.** After the pinned sha it went 170347b → d32002c6 (author line, count macros, regenerated statements).
This review stays on 170347b. A quick diff of the newer head shows:
- **X6 is resolved at d32002c6.** `chapters/s04/etaprinciple.tex` now says \stformal{} for Prop. 17.1, and the box is regenerated.
- **X8 is still open.** The chapter now notes that clause (b) of Ihara (iii) is not stated in Lean, but `open.tex:167` still files
  Ihara (iii)(b) as \stexp.
- **Everything else is untouched.** I found no change to `hsieh.tex`, `computations.tex`, `results.tex` or `pointers.tex`, so the
  remaining findings still apply to the new head.

## Part G2: talk (talk/main.pdf, 22 pp)

**Verdict: FIX (0 crit, 5 maj, 8 min; plus notes).** W = 3·0 + 2·5 + 8 = **18**.
No false headline claim found. Every number I could trace (mass table and all 17 Brandt char-polys, Phi_comb orders and weights for q = 11, 23, 37, 101, 131, Eisenstein check l <= 13, H7/T3 orders and ranks, T6 cases, sign 144/144, T4 lengths, T5 triples, C4(i) 225/225, 396, 5/46, 131/319, H3 5 cases, HACS 14/14, 69, 32 cells, 296 = 2^3*37, 64.7 s vs 0.02 s, 404 primes, 1229 primes, 836/836, 29 hyps, DOIs) matches the report/JSON. The `main.pdf` text of `2^3*37` extracts as "23 · 37"; the source is `2^3\cdot 37`, so that is NOT an error. Issues are one wrong prime bound, missing scope or caveat wording on a few slides, one ambiguous "read ~10^3x", and an overstated "sign error in [Hs]".

Checks not done: no LaTeX log exists (talk/ has no .log), so overfull boxes were judged from source line lengths and from rendering p. 10 and p. 18 at 70 dpi (both fit; deleted). The other pages were not rendered. Slides 9, 10, 16, 17, 19 use shrink and have very small type (note N1).

### Per-slide table
| slide (page) | file | verdict |
|---|---|---|
| 1 title | main.tex | OK (note N3: `\date{\today}`) |
| 2 outline | s00-outline | FIX (T9) |
| 3 What JL says, D = 11 | s01-what-jl-says | FIX (T10) |
| 4 backup mass table | s01-mass-table | OK (all 17 rows verified vs classsets.json and brandt_w2.json) |
| 5 BG(U1(5),2) for B3 | s02-graph | OK |
| 6 quotient Gamma_U\T_q | s02-slogan | OK |
| 7 collapse / Ribet | s03-collapse | OK |
| 8 Mazur check | s03-mazur | OK |
| 9 HACS check | s06-hacs | FIX (T1, T6) |
| 10 HACS beyond Mazur | s06-hacs | FIX (T3) |
| 11 Ihara / cokernel | s03-ihara | FIX (T7) |
| 12 non-ordinary | s04-nonord | FIX (T5) |
| 13 Hida tower | s04-tower | OK |
| 14 zig-zag | s05-zigzag | OK |
| 15 cost / sign | s05-cost | OK |
| 16 K1 Thm E | s06-thmE | OK |
| 17 K2 defect = Tamagawa | s06-defect | FIX (T2, T11) |
| 18 K3 caveats | s06-caveats | FIX (T4, T8) |
| 19 summary | s07-summary | FIX (T1, T5, T12) |
| 20 agentic process | s07-process | FIX (T13, min) |
| 21 software | s07-releases | OK (note N2) |
| 22 acknowledgments | acknowledgments | OK (note N4) |

### Findings
| id | severity | slide (page) + file:line | finding | evidence | exact replacement text |
|---|---|---|---|---|---|
| T1 | maj | s9 `slides/s06-hacs.tex:24`; s19 `slides/s07-summary.tex:16` (also report `sections/computations.tex:87`) | "exactly ... for every prime q <= 479 (80/80)" is numerically inconsistent: there are 92 primes q <= 479, and 80/80 cells are the first 80 primes, i.e. q <= 409 (the 80th prime is 409). The census closure says "80 complete cells (all primes q <= 479)", which is the same slip. | `plan/hacs/outbox/20261115T0150Z_laneB-closure.md` §6 line 83 (80 cells, stopped by 15-min cap). Primes counted: pi(479) = 92, pi(600) = 109 (ok), prime #80 = 409. | s9: "... and exactly (2- and 3-parts included) for every prime $q\le 409$ (80/80, exact $\mathbb Z$ route; stopped by a 15-min cap)". s19 HACS row: "exact for $q\le 409$". Fix the report line `computations.tex:87` the same way (or recount the cells and keep 479 only if the count is 92). |
| T2 | maj | s17 (K2) `slides/s06-defect.tex:9-13` | The defect formula (h_F) = c_q = t_q is stated with no scope on the slide that states it. The scope (H0), (H1), (H2), (P) and (H0^-) or (Lev); (Lev) only for M = 1, (F1), (F1'); N(rho-bar) > 1 open; trivial primes excluded) appears only on the next slide (K3) and in the footer of the summary slide. The status line "proved modulo cited results" reads as unconditional. | Report thm 21.5 (`generated/statements-s06.tex:68-73`): pmc under (H0^-); under (Lev) pmc for M = 1, (F1), (F1'); N(rho-bar) > 1 open. | Add after the Status line on K2: "\emph{Scope:} under (H0)--(H2), (P) and (H0$^-$) or (Lev); for $q\equiv-1 \bmod p$ only $M=1$ and (F1), (F1$'$) ($N(\bar\rho)=1$) are covered; $N(\bar\rho)>1$ is \emph{open} (see K3)." |
| T3 | maj | s10 `slides/s06-hacs.tex:48` | "(≈ 3 x 10^3; read ~10^3×, not an exact factor ...)" - the stray word "read" is directly under the bullet "Reading is milliseconds in both: no read-side speed claim" and can be read as a read-side speed claim. Report/closure wording: factor ≈ 3 x 10^3, "~10^3x is the honest statement". | Closure §2.4 and `computations.tex:~100`. | "(a factor of about $3\times10^3$; ``$\sim10^3\times$'' is the honest statement, not an exact factor; a first measurement on a loaded node gave 61 s vs 0.025 s)". |
| T4 | maj | s18 (K3) `slides/s06-caveats.tex:8` | "we identified a literature correction (a sign error in [Hs])" states an error in a published paper as fact. The report calls it "as we read it, a sign should be corrected", status proved modulo cited, "treated as an erratum", Fabian to contact the author. | `sections/hsieh.tex:3-7, 13`; `open.tex:55`. | "Minor: in our reading, a sign in [Hs] ($\mathrm{JL}(U_q)=-U_q$) should be $+U_q$ (\emph{proved} modulo cited inputs; checked on 144/144 eigenlines; to be communicated to the author)." |
| T5 | maj | s19 `slides/s07-summary.tex:13` (and s12 `slides/s04-nonord.tex:14`) | S04 row says "$\Lambda$-adic Ribet proved" with no caveat. Thm 15.1 is proved only under the assumption that BG(U U_s, q) is connected for all s, which comes from the cited Hyp.SA and Hyp.HS (in Lean also Hyp.BTtree) and "is not a finite check". The S02 row shows the SA caveat, but the S04 row hides it. | `generated/statements-s04.tex:84-88` (the connectivity hypothesis; the F7 note makes it explicit). | S04 row, math column: "$e$ kills the Eisenstein part; control (a) \emph{proved}; $\Lambda$-adic Ribet \emph{proved given connectivity} (from cited SA, HS)". On s12 add "(given connectivity of BG, i.e. SA/HS)" after "thm. s04-lambdaribet". |
| T6 | min | s9 `slides/s06-hacs.tex:22-25` | The census bullet attributes the exact (2- and 3-part) result to "HACS's integral engine" but that route uses our own BigInt Smith/HNF (deviation D4: HACS routes are mod l^K only, and ReadLocal cannot do l = 2); the cap-stop is omitted. | Closure §4 D3, D4, §6. | After "exactly (2- and 3-parts included) ...": "(own exact BigInt Smith route inside the HACS build, deviation D4)". |
| T7 | min | s11 `slides/s03-ihara.tex` (bullet 2, and status line :34) | "proved modulo (iii) and density of Gamma_U in U_p^1, as labelled in the tex" is garbled (a theorem cannot be proved modulo itself), and "(iii) per tex labels" is vague. Report: Thm 11.3 is "pmc (proof below)", Lean: Hyp.IharaH0. | `generated/statements-s03.tex:70-87`. | Replace "proved modulo (iii) and density ..." with "(iii) \emph{proved modulo cited results} (incl. density of $\Gamma_U$ in $U_p^1$)" and the status line with "Maths: (i),(ii) \emph{proved}; (iii) \emph{proved modulo cited results}." |
| T8 | min | s18 (K3) `slides/s06-caveats.tex:9` | Garbled first clause: "q ≡ −1 mod p: q ≡ −1 for M = 1, and for ..." and the scope is not tied to rho-bar unramified at q. Also does not name the three cases. | `s06-m5.tex` (F0), (F1), (F1'); `results.tex:39-43`. | "\textbf{$q\equiv-1\bmod p$} (with $\bar\rho$ unramified at $q$): covered for $M=1$ and for squarefree $M$ with $\bar\rho$ unramified at all $\ell\mid M$, i.e. $N(\bar\rho)=1$ (cases F0, F1, F1$'$); \emph{open} for $N(\bar\rho)>1$. Status: \emph{proved modulo cited results}; ..." (rest unchanged). |
| T9 | min | s2 `slides/s00-outline.tex:19` | "formalized (Lean 4, standard axioms only)" can be read as unconditional. The report's rule is "formalized modulo registered hypotheses" where a Hyp.* is consumed (27 of 29 open). | `sections/overview.tex:89`; `lean.tex:97-103`. | "\emph{formalized} (Lean 4, standard axioms only; \emph{modulo registered hypotheses} where stated)". |
| T10 | min | s3 `slides/s01-what-jl-says.tex` | Slide that states "the correspondence is between Hecke eigensystems" has no status or source line, although the outline promises "every claim carries its status"; JL itself is cited (Hyp.JLClassical). | `lean.tex:100`, summary S01 row says "JL cited". | Add footer: "{\tiny Status: \emph{computed} (Brandt $T_2$, Weil curve 11a1); the JL correspondence itself is \emph{cited}.}" |
| T11 | min | s17 (K2) `slides/s06-defect.tex:18` | "At weight k+(p-1): 4 of 7 computed" does not say what: the 4 are GL2-side only (ord eta, ord c, eta^new); eta^B is not computed at k+(p-1) in any of the 7. | `code/results/s06/T5.json` (k+p-1: status "not computed", reason "eta^B not computed"; gl2_side computed for 4). | "At weight $k+(p-1)$: $\mathrm{ord}\,\eta=\mathrm{ord}\,\mathfrak c=1$ on the $\mathrm{GL}_2$ side for 4 of 7 (the 3 of level 13 not computed, runtime); $\eta^B$ not computed there." |
| T12 | min | s19 `slides/s07-summary.tex:22` | "0 sorry in our code (1 in the frozen import only)": the report says the build reports one sorry (in the import, in a module used only by two test files) and the import has a second one in a module that is never built. | `sections/lean.tex:37-42`. | "$0$ \texttt{sorry} in our code (the build reports $1$, in the frozen import; a second sits in a never-built import module; none in the 836 audited axiom lists)". |
| T13 | min | s20 `slides/s07-process.tex` (table row S06) | Plan for S06 shown as "2.2 h"; timeline gives 2.2–2.6 h (the 2.2 is the lower end). | `docs/agentic-process/timeline.md:21`, also "≈ 2.4 h" at :28. | "2.2--2.6 h" (or "≈ 2.4 h"). |

### Notes (no points)
- N1: slides 9, 10, 16, 17, 19 are in `shrink` with ~6–8 pt type; fine for the PDF, poor for a projector. Consider moving the 5-line sketch on K1 or the C4(i) bullet to backup.
- N2: s21 and s10 footers cite HACS v0.2.1 (DOI 10.5281/zenodo.24231446). The JL module is a standalone build, "not registered in hacs", merge pending (closure D6); a judge may assume the JL module is in that release. One clause "(JL module merged after the release)" would remove the ambiguity, if true.
- N3: `main.tex` uses `\date{\today}`; a rebuild on another day changes the title date (15 Nov 2026 now). Fix to a literal date.
- N4: the acknowledgment says GPUs were "used for the HACS computations"; Lane A/B closures say no GPU arm/CPU-only builds for the JL work. The wording is mandated verbatim by `agents/rules/licensing.md`; leave it, but be ready for the question.
- N5: s12 "Honest note (audit M7.1)" and s11 "audit PASS with remarks, fixed" are internal-process references; fine, but a judge cannot resolve them.
- Verified OK and notable: HACS speed line has the "~10^3×"/"no read-side speed claim" wording on s10 apart from T3; q ≡ −1 scope, N(rho-bar) > 1 open, H3 evidence "not a test of M = 1", trivial primes, and FreeRankTwo/ResidualBurnside wording are all present on s18 and match the report; Lean "modulo registered hypotheses incl. Hyp.FreeRankTwo" appears on s17, s18, s19; "Hyp.X: a hypothesis, not formalised" on s14, s15, s19; Mazur check "proved modulo cited" and Hyp.EllipticCount/EichlerMass on s8.
