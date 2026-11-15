<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Submission report, audit 2: the new sections (independent Fable audit, 2026-11-15)

Audited: `mathematics/submission/report.tex` at `final/audit-sub2` = `wip-submission` cfc49cd2 (180 pp PDF).
Scope: only the sections added after `2026-11-15_submission-report-audit.md`: "Our HACS contributions" (`src/hacs.tex`),
"Stage 2 of the Mathathon: next steps" (`chapters/s00/plan.tex`), "Prior work and acknowledgements" (`chapters/s00/prior.tex`),
"Human contributions and responsibility" (`src/aiuse.tex`, summary in `src/event.tex`, wording in `src/agentic.tex`),
the s00 additions `ribet.tex`, `achieved.tex`, `newknown.tex`, and the global anonymity check.
Line numbers are those of `report.tex`; fixes go into the named source file, then re-flatten.

## Verdict

**PASS WITH FIXES. No content blocker.** Every number of the HACS section agrees with the JSON files and the two lane
closures (errata included); the plan section claims no result; all Ribet locators and all checked quotations are correct;
all nine dated decision examples agree with the process log. Four major findings (two numerical/internal contradictions, one
overclaim about reference verification, one omission in the human-role statement) and six minor ones, each with replacement text.
Three placeholders remain open and are the master's to close before submission (P1 to P3).

## What was checked, and how

- **HACS numbers** (recomputed from `code/results/`, not copied from the closures):
  - `laneB/congruence_k.json`: 74 cells = 14 (k = 2) + 60 (k > 2); 34 of rank 0, so 26 non-zero; the only k > 2 orbits with
    non-trivial lattice module are D = 13, k = 8, orbits `x - 10` and `x^2 + 19x + 6`, Smith (37) each; quartic orbit trivial;
    ring modules 2·13²·37, 2²·13⁴·37, index 2³·13⁶. D = 11, k = 2: both orbits Smith (5), ring Z/5, Gram 5/6 and 5,
    T_p factors as in the table, `ReadLocal` `5^1_exact` and `7^0_exact`, `gl2_compare` resultant ±5. The 14 k = 2 cells are
    the primes q ≤ 43 and all equal num((q−1)/12), 2- and 3-parts included.
  - Resultants recomputed with sympy: Res(x−10, x²+19x+6) = 296 = 2³·37; Res(x−10, quartic) = 13520 = 2⁴·5·13²;
    Res(x²+19x+6, quartic) = 911210144 = 2⁵·13⁴·997. The product of the three factors equals the T₂ characteristic
    polynomial of `s01/symn.json`, cell (13,8) (Brandt = newform side, rank 7, h = 1, |Γ| = 2).
  - `s05/gl2_dnew.json`: cell (13,8) U₁₃ signs +, +, −, s = 2197, `unique`; acceptance 66/66, 8/8, 152/204, 52 skipped,
    8 ambiguous; runtime 1283.9 s = 21.4 min.
  - `laneB/py_reference.json`: h = 2, 3, 3, 9, 12 and orders 5, 11, 3, 25, 65; 69/69 orbits, 0 mismatches; 30.7 s + 30.3 s; h(997) = 83.
  - `s01/brandt_w2.json` T1: T₂ = [[1,2],[3,0]], units 4 and 6, mass 5/12.
  - `s06/T4_betti.json`, `T4_hecke.json`: (Z/17)² at k = 12, 28, 44, 60 on the amalgam route; `expected` tag for k ≥ 17;
    k = 124 `not_reachable`, off route valuations [2,2]; dim T = 1, 2, 3, 5, 10; lengths 1, 1, 1, 1, 2; −24 ≡ 10, 252 ≡ 14 mod 17.
  - `s06/brandt_free_block_z/`: 74 records + index. `s06/definite_local.json`: D = 11, ℓ = 5 non-étale, Gorenstein.
  - Counting: 109 primes ≤ 600; the 80th prime is 409; 404 primes ≤ 2777; 1229 primes < 10⁴.
  - Closures: self-test 8084/0, tier A 12154/0, tier B 6231/0, 248/248 = 246 + 2, 294 upstream names, 178 s, 19.6 min,
    64.7 s vs 0.02 s; D1 to D8 agree with Lane B closure §4; both errata are applied. No "certified" in the section;
    "no read-side speed claim" is present.
- **Plan section** against `lean/Langlandscape/HYPOTHESES.md` (29 rows without the alias; 2 discharged; 1 conditional),
  the hypotheses appendix of the report, the milestone closures and `plan/hacs/HACS-JL-PLAN.md` (HJ-3, 4, 5a, 7, 8, 9, 10, 11, 12).
- **Prior work**: 18 DOIs resolved through Crossref and compared with the bib entries (Gel75, Shz72, HK91, KM86, IP23, Hi81,
  DiaPNAS97, TW95, DiaInv97, RT97, Ih66, SL96, Eme02, LM, Bad08, BR10, Lean4, Mathlib20; Hi88a by a bibliographic query):
  all agree. Quotations and locators read in the local copies: IP16 ("extending the work of Shimizu", before Theorem 1),
  HK91 ("can be realized, as in the work of Shimizu, as a theta correspondence"), Hi88b (Thm 2.1, "a result of Jacquet,
  Langlands and Shimizu"), IP23 (Theorem 1, the condition on the infinite places, §1.2.3), CV12 (abstract), BKM (Thm 1.1,
  "nor is it Gorenstein"), Koh01 (Thms 4.2, 4.3).
- **Ribet 1990** (OCR of the local scan, journal pages): Prop 2.2 and Thm 2.3 p. 436; Prop 3.1 p. 439; Prop 3.3 and
  Variant 3.4 p. 440; Prop 3.7 p. 445; Prop 3.8 p. 446; Thm 3.12 p. 449; Thm 3.15 p. 451 ("derived from results of
  Eichler concerning the arithmetic of Eichler orders"); Remark 3.18 and Thm 3.19 p. 452; "geometrical realizations of the
  Jacquet-Langlands correspondence" p. 456; Thm 4.1, Cor 4.2, the trace-identity sentence and Thm 4.3 p. 457. All correct.
- **Human contributions**: `agents/status/master_log.md` (local time = UTC+1) and git commit times. Apache-2.0 22:33 → 21:33 UTC;
  frozen tree kept 23:16 → 22:16; q ≡ −1 option 2 02:00 → 01:00; FD1/FD2 02:03 → 01:03; lift (F1), (F1′) 02:32 → 01:32;
  HACS 01:45, 01:50, 01:53 → 00:45, 00:50, 00:53; Q4 02:46 → 01:46; FreeRankTwo commit 44058153 at 01:50 UTC;
  RamNrdSurj 03:22 → 02:22 and 04:03 → 03:03. All nine agree. First commit f7d8fd70 at 05:52Z. The seed
  (`plan/seed/towards_simplicial_jl.tex`, 672 lines) contains the requirements and the tree route. The disclaimer
  "not a novel idea per se ... preliminary work, prepared before the event" is present.
  grep of `report.tex` for "autonom", "agents decided", "Claude decided": no hit.
- **Anonymity**: `flatten.py --check`: A6 PASS; manual grep of the body after `\maketitle` for names, node names, paths, PC2,
  Paderborn, GitHub: no hit. PDF metadata: author empty. Remaining FAIL/WARN are the intentional ones (A5, A11, A7, D1).

## Placeholders to close (master; intentional at this commit)

- **P1** L214 (title block): `\TODOFACT{full commit hash}`.
- **P2** L5385 (`src/hacs.tex` l. 197): `\TODOFACT{Lane C results}`. No Lane C closure exists in `plan/hacs/outbox/` on main
  (branches `impl/hacs-laneC*` only). If no closure arrives, replace the last sentence by:
  `At the time of submission Lane~C has no closure; nothing from it is claimed in this report.`
  and keep the intro sentence of the section (L5202 to L5203) and `plan.tex` l. 64 ("as far as the overnight lane
  (Lane~C) leaves them open") as they are: both remain true.
- **P3** L7949 (`src/commits.tex`): `\TODOFACT{bundle gate hash}`.

## Findings

### Major

**M1. The count "27" contradicts "26 open" two pages earlier.** L5908 (`chapters/s00/plan.tex` l. 16): "The remaining 27 fall
into five groups". The report says 26 open everywhere else (`\NumHypOpen` = 29 − 2 − 1, e.g. L5831, L5864). The groups
hold 5 + 2 + 2 + 16 + 1 = 26 open hypotheses; the 27th is the conditionally discharged `ResidualBurnside`, mentioned in (E).
Source of truth: `HYPOTHESES.md`, `src/counts.tex`. Replace the sentence by:
> The 26 open hypotheses fall into five groups (\texttt{LambdaJL} is counted in (D)); the reasons are those recorded in the registry and the milestone closures. Group (E) also names the condition behind the conditionally discharged \texttt{ResidualBurnside}.

**M2. "Next steps" (4) and (5) contradict the new plan section and the HACS section.** L5837 to L5839 (`src/limitations.tex`
ll. 16 to 18): "(4) In Lean: discharge the cited hypotheses that are within reach of Mathlib (strong approximation, the tree,
Serre's results on groups acting on trees, the Eichler class number formula)"; "(5) HACS: one full validation run". The plan
(L5933 onwards) puts `SA`, `SerreCoh`, `SerreFree` under "Deep literature; cited, not reproved in stage 2", and the full
`--all` run was made (248/248, L5246; Lane B closure §7). Replace (4) and (5) by:
> (4) In Lean: the discharges planned in \S\ref{ss:stage2-hyp} (\texttt{BrandtStabFree}, the port of the tree, the Eichler class number formula for $D$ prime, \texttt{InvLimExact}, \texttt{MordLambdaFree}) and the specialisation of Thm~E to Hecke rings; strong approximation and Serre's results on groups acting on trees stay cited. (5) HACS: the remaining validation rows (digests, \texttt{LABEL\_CENSUS}, the slow tier, the device lane), canonical lattices at $k>2$, and the large census.

**M3. Overclaim about how the references were verified.** L4085 to L4086 (`chapters/s00/prior.tex` ll. 10 to 11): "are kept to
what we checked in the source; the bibliography entries record how each reference was verified". In the judged file the
inlined bibliography has no verification notes (they are the `note` fields of `mathematics/references.bib`), and three cited
entries are recorded there as not checked against the paper: `Ih75` ("bibliographic data not checked against the paper"),
`Ri84` ("NOT in literature/"), `Piz80` ("scan, no text layer: not verified"); `KM86`, `DKV84`, `Len95`, `Mes86`, `DiaInv97`
are bibliographic data plus a secondary description. Replace the sentence by:
> Statements about other work are \stcited{} and are kept to what we checked; the file \texttt{mathematics/references.bib} records for each entry how it was verified (Crossref, a local copy with the page, or a secondary source). Three entries, \cite{Ih75}, \cite{Ri84} and \cite{Piz80}, were not checked against the papers themselves and are cited for their standard content only; \cite{KM86}, \cite{DKV84}, \cite{Len95}, \cite{Mes86} and \cite{DiaInv97} are described through the sources named next to them.

**M4. The human-role statement omits that parts of the run were unattended.** L5507 (`src/aiuse.tex` l. 69: "Real-time
steering and critical decisions were made by the two team members") and `src/agentic.tex` l. 26 ("under its real-time
steering"). The process log records, at 10:09 UTC on 14 November (11:09 local): "signed off; continue autonomously through
planning + implementation"; `STATE.md` lists "Stage-6 defaults (proceeding unless ... objects)" and "Provisional decisions:
6 math, 9 impl (PROVISIONAL global master)". The report mentions the provisional mechanism once (agentic, L5543) but
nowhere that no team member was present for stretches. This is not a contradiction, and no decision example is wrong, but
without it the statement reads as continuous supervision. Add, at the end of item (4) of `ss:human` (after the list of examples):
> Steering was not continuous. For parts of the run (for example most of the planning phase, after 10:09\,UTC on 14 November; process log) no team member was present, and the coordinating agent continued within the standing instructions. Decisions reserved for the team that came up meanwhile were applied provisionally, marked as such and listed for the team in \texttt{agents/status/STATE.md}; the examples above are those the team then took.

and in `src/agentic.tex` l. 26 replace "under its real-time steering" by "under its steering (continuous at the critical
decisions, not at every hour; \S\ref{ss:human})".

### Minor

**m1.** L5350 (`src/hacs.tex` ll. 162 to 163): "37 is the prime common to both modules". The primes 2 and 13 are common to
both as well (orders 2·13²·37 and 2²·13⁴·37). Replace "and $37$ is the prime common to both modules" by:
> and $37$ is the only prime dividing both ring modules that does not divide this index

**m2.** L5266 to L5271 (`src/hacs.tex` ll. 78 to 83), Lane A deviations: three items of the closure's list are missing
(3c, 4b, 6a). After "(adding $T_\ell$ changes nothing at $k=2$, checked)" insert:
> and its comparison with the stage-06 check C1 is replaced by an independent Python check; the $U_D$ signs are computed for prime $D$, $M=1$ only; the export format v1 was superseded by v2 within the lane (its class order depended on the process)

**m3.** L5933 onwards (`plan.tex` ll. 41 to 48), group (D) "Deep literature; cited": the hypotheses appendix classifies
`IharaH0` and `FreeRankTwo` as "proved on paper in this project" (table at L6261, L6272), and the chapters mark
Thm s03-iharaH0 and Prop s06-galois as proved modulo cited. Replace "\texttt{IharaH0} (Ihara's lemma; it also needs
\texttt{SA})" by:
> \texttt{IharaH0} (the cited inclusion in Thm.~\ref{thm:s03-iharaH0}, which is proved modulo cited inputs in the chapter; it also needs \texttt{SA})

and "\texttt{FreeRankTwo} (the Galois half of \texttt{prop:s06-galois})" by:
> \texttt{FreeRankTwo} (the cited steps of \texttt{prop:s06-galois}, itself proved modulo cited inputs)

**m4.** L5929 to L5932 (`plan.tex` ll. 37 to 40), group (C): the appendix entry of `Hyp.JLClassical` (L6527 to L6529) says the
discharge needs, beyond the trace formula, its comparison with the quaternionic side and Hecke operators on
$S_2(\Gamma_0(N))$ in Mathlib, and that the Lean statement is schematic. Replace "and its completion is the main route to
discharge \texttt{JLClassical} ourselves, and possibly the classical input of \texttt{LambdaJL}" by:
> and its completion, together with the comparison with the quaternionic side and a non-schematic statement on $S_2(\Gamma_0(N))$ (Appendix~\ref{app:hyp}, entry \texttt{Hyp.JLClassical}), is the main route to discharge \texttt{JLClassical} ourselves, and possibly the classical input of \texttt{LambdaJL}

"Status: planned; timing uncertain." is present and stays.

**m5.** L4105 (`prior.tex` l. 30): the first sentence on Kudla and Millson ("constructed theta lifts with values in
cohomology for orthogonal groups of signature $(p,q)$") is stated without the hedge, although the bib note says
"bibliographic data only". Replace "In cohomological form, Kudla and Millson constructed ... \cite{KM86}. As we understand it
(from the paper's scope, not from a statement we located in it: \cite{KM86} is not among our local copies), for signature" by:
> In cohomological form there is the work of Kudla and Millson \cite{KM86}. As we understand it (from the paper's scope and from the use made of it in \cite[\S1.2.3]{IP23}, not from a statement we located in it: \cite{KM86} is not among our local copies), they construct theta lifts with values in cohomology for orthogonal groups of signature $(p,q)$; for signature

**m6.** L5440 (`src/event.tex` l. 57): "the main branch has 2194 commits"; main has 2198 now. Update with the final hash (P1).

## Checked and found correct (no action)

- `ribet.tex`: every locator and the three paraphrases of proofs and attributions (see above).
- `achieved.tex`, `newknown.tex`: statuses match the chapters' labels as printed in the report; novelty is hedged
  ("we did not find this ... in the literature we checked") at each of the five places; "eight of the nine stage-06 Lean
  hypotheses are open" agrees with the registry; the HACS lines carry the corrected census ("first 80 primes q ≤ 409",
  "among the non-zero cells").
- `plan.tex`: no result is claimed; HJ work packages agree with `HACS-JL-PLAN.md`; the 10⁵ census figures are those of
  Lane B closure §5; no node or site name.
- Hsieh's sign: "treated as an erratum" (L1158, L2940, L4051, L5895) and "ask whether the difference is one of
  normalisation" (plan) are compatible with §`ss:hsieh` ("as we read it").
- Team-statement items (a)–(e), route idea with disclaimer, orchestration "designed by the two team members ... augmented
  by Claude in real time", responsibility with the team members: present in `ss:human`, in the summary in `src/event.tex`
  and in `src/agentic.tex`, without contradiction between the three.

## Not checked

- The team statement itself was not available as a separate file; faithfulness was judged against the items listed in
  the audit brief and the commit message of 0323d7a5.
- Locators in `prior.tex` whose sources are marked verified in `references.bib` and were not re-read here: Gel75 §10,
  Bergeron's preface, Bad08 Thm 5.1, BR10 Thm 18.1, Ch Thm 3, LV Prop 6.1, Hs Thms 4.2/4.5, Hi81 §0, Ri83, Dia89, Wi95
  Appendix, RT97 Thm 1, PW Thm 6.8, KO Thm 1.1, Ih66, Se, Gro87, SL96, Eme02 (abstract).
- The census log of Lane B closure §6 is outside git; the 109/109, 80/80 and 178 s figures rest on the closure and its erratum.
- No rebuild of the PDF.
