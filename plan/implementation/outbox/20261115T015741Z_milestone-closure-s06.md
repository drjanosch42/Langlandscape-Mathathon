<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Milestone closure S06 (S06-X3)

MILESTONE CLOSED: S06 stage-06 implementation (integral defect: commutative-algebra layer, Defect layer with `Defect.defect_formula`, chapter s06)
branch/commit: wip-implementation; Lean tree = 4405815 (final-gate sha, 44058153); base 63e86606 (S05 closure merge)

Status words: *formalized* = compiles, standard axioms only; *formalized modulo H* = compiles with the hypotheses H as explicit arguments; *proved* / *computed* / *conjectural* / *cited* as in CLAUDE.md.

delivered:
- Lean, commutative-algebra layer (`lean/Langlandscape/CommAlg/`, all modules, 0 sorry): L1 `Gorenstein` (`IsGorensteinWith`, `congruenceIdeal`, `NewOldData`, `split_iff`, `isGorenstein_iff_cyclic`),
  L2 `LemmaS`, L3 `NewOld` (Lemma D), L4 `ThmE` (Thm E (i), (ii), (iv), Gorenstein half of (iii)), L5a `DVR` (`eta_eq_c_mul_of_dvr`: Thm E(iii) DVR half formalized), L5b `LemmaG`
  (`isGorenstein_of_isGorenstein_quotient`), L6 `TraceForm`, L6b `Burnside`, L7 `Squeeze`, L10a `LanglandscapeTests/S06/Toy`, L13 `BaseChange`, L14 `TwoByTwo`, L17 `EtaPrinciple`.
  Status: *formalized* (axioms [propext, Classical.choice, Quot.sound]); L1-L3 merged before the stage (s03-int1-1), L4-L17 as modules (s06-int1-1/int1b-1), L5b int2c-1.
- Lean, Defect layer (`Defect/`, `Hyp/`): L8a `Defect.Setting` (instance `[Algebra I 𝒪]`, `lamΛ'`, `newOld`/`newOldAt`; `Setting.isLocalHom_P`), L8b `Defect.galois` + `Hyp.residualBurnside_of_absIrred`, L8c `Setting.gor_new`,
  L9a `Defect.defect_formula`, `defect_formula_of_le`, `Defect/Fixed.lean` (`cor_fixed`, `map_cq`), L9b `cor_allweights` (`Defect/Corollaries.lean`), L10b `LanglandscapeTests/S06/Hyp.lean` (5 toy instances), MODH (`Hyp/LambdaJL` as module).
  Status: **`Defect.defect_formula` is formalized modulo the registered `Hyp.*`, including the Galois half (`Hyp.FreeRankTwo`)**; it is not an unconditional theorem. 11 headline axiom rows standard (int3f-1), 833/833 at gate1.
  L15b (Sonnet + an Opus fix round for the tests): `Defect.freeRankTwo_iff_le` (given ResidualBurnside; with `freeRankTwo_of_le`), `gor_new_of_I`, the exact FreeRankTwo disclosure sentence everywhere (Fabian), toy consistency instances; int4a-1 core/hyp PASS with 6 test errors, Opus fix 9e292096, int4b-1 left 1 goal, fixed explicitly e69a6369, int4c-1 (CONCEPTD) PASS, 0 errors, 0 warnings.
- Hypothesis registry (nine new rows + `ResidualBurnsideDischarge`; see below).
- Mathematics: chapter s06 (`mathematics/chapters/s06/s06-m{1,2,3,4,5,7,8}.tex`, Abhijit's M1-M4, M7, M8, M11, M6 notes merged at X1; M5 local).
  Statuses: Thm E (i)-(iv) proved (iii DVR half also formalized); Lemma S/D/G proved; `thm:s06-defect` proved modulo cited results (Hida control, Hsieh, Kim-Ota) and registered hypotheses;
  `prop:s06-galois` proved modulo `FreeRankTwo`; `prop:s06-levM` (q = -1): M = 1 *proved modulo cited* (`\stpmc`, M6 CONFIRMED, F2 part A, A5 fills the T_p gap);
  M > 1: F1 and F1' lifted by Fabian's decision (stpmc under the stated hypotheses, level (Lev), wording B2/B5 binding in s06-m5), **N(rhobar) > 1 open (`\stopen`, rem:s06-levM-open)**; `cor:s06-fixed`, `cor:s06-allweights`
  (needs `c != 0` at both points, newform condition, not assumed) as in the chapter; `O_P` is *not* claimed to be a DVR (normalisation `O~_P`, audit R1).
  Fable chapter audits: part 1 PASS WITH REMARKS 0/2/12 (fixed in M10a), part 2 FAIL for the M > 1 layer as written (1 crit, 3 maj), addendum on the restricted text PASS WITH REMARKS 0/2/4 (fixed in M10b), part 3 0/0/7 with (gamma) empty CONFIRMED by an independent reader (applied in M10c).
  `mathematics/notes/hsieh-sign.{tex,pdf}`: [Hs] arXiv v5 section 4.5 p. 34 prints JL(U_q) = +U_q; as printed, Thm 4.5 is vacuous (FD2). S05FIX: 15 cross-account audit fixes (X1-X15) applied to the s05 chapter (X5 kept stpmc with p-new hypothesis + Casselman citation, X16 skipped).
  Milestone PDF `mathematics/main.pdf`: 170 pp (pdfinfo; commit 44058153).
- Code (`code/python/langlandscape/defect/`, `code/results/s06/`): C1 congruence toolkit (33 tests; toy eta = c = p^t; seed q = 3, p = 17, k = 12, 28 `ord c = 1`; *computed*), C2 C4(i) regression `C4i.json`
  (*computed*, **partial: 131/319 cases run**, 225/225 in scope v(h) = v(c_q); Eisenstein (h) contains c_q on all 396 DVR rows, fails in 5/46 non-DVR rows at p = 2, 3), C3 T4 Hecke side `T4_hecke.json` (lengths 1,1,1,1,2 at k = 12, 28, 44, 60, 124 = prediction, *computed*),
  C5 definite Gram side `T5_def.json` (7 triples, v_p(eta^B) = 0, positive control (13,8,37) v_p = 1; 10 tests). C4/C6 (`T5_gl2.json`, `T5.json`; *computed*): weight k 7/7 (ord eta = ord c = t_f(q) = 1, eta^new = 0, eta^B = eta_f(1,q), eta_f(q) = c_q eta^B); k+(p-1) 4/7 (3 level-13 cases not computed); the plan item `rk T'_m >= 2` is false (rank 1; the full algebra has rank 2). C7: covered by Abhijit's F4 cross-check
  (`code/cas/s06-xcheck`, `results/s06-xcheck/{T4_hecke,H3}.json`: T4 lengths 1,1,1,1,2; H3 supplement at M > 1: 5 non-vacuous t = 2 cases with ord c - t^an = 0, all N(rhobar) > 1); no local C7 run. pytest: 57 defect tests pass.
- Talk: T1 K1 slide (`talk/slides/s06-thmE.tex`; Thm E(iii) DVR half marked formalized), T3 K3 caveats slide (`s06-caveats.tex`: q = -1 exact statement, H3 honest caveat, BKM, Galois-half disclosure, [Hs] sign line),
  T-HACS slide (`s06-hacs.tex`: final numbers per HJ-6b ACCEPT 6322a7d, honest timing lines; k = 2 exact, 37 confirmed via the GL2 resultant 296 = 2^3 * 37, ring-module primes; resultants = "consistent", not confirmation), T2 K2 (`s06-defect.tex`, merged). `talk/main.pdf`: 17 pp (pdfinfo, 4405815).
  Binding wording used: the defect formula is "formalized modulo registered hypotheses, including the Galois half (`Hyp.FreeRankTwo`)"; q = -1 for M = 1, and for squarefree M with rhobar unramified at all l | M; open for N(rhobar) > 1.
- Other: S05FIX (s05 chapter), FD1/FD2 recorded as decided in s05 maths, Lean docstrings, talk; L14 import fix; `Hyp/LambdaJL` module conversion.

verification:
- s06-int1-1 / int1b-1: 9 CommAlg WPs PASS (8/8 after the L14 import fix); s06-modh-1 PASS; s06-int2c-1 L5b 2/2; s06-int2d-1 L15a 14 files; s06-int3g-1 (TITAN) `defect_formula` PASS 5/5 standard; s06-int3f-1 (CONCEPTD) all 7 Defect WPs PASS, 11/11 standard.
- **s06-gate1-1 (TITAN, 7447d96e): PASS all six steps.** (a) `lbuild Langlandscape LanglandscapeTests` rc 0, seeded 20 s, **from scratch (unseeded) rc 0, 304 s, 4.52 GB, 4194 jobs, 0 errors**; (b) VendorStacks rc 0, 1955 jobs, 0 warnings;
  (c) PrintAxioms **833/833** (nonstandard 0; 23 subset lines, all within the standard triple; the 47 new rows full standard triple; no sorryAx/ofReduceBool/trustCompiler); (d) forbidden grep empty; (e) sorry = the import's 1 only;
  (f) check_frozen clean; check_wp on 32 files (6 Defect, 10 new Hyp, CommAlg, Tests/S06) 0 FAIL; GL2TF-free grep empty. Warnings 527 (185 Langlandscape/, 76 Tests/), S06-specific 9 (3 overlapping instance parameters in `cor_fixed`, `defect_formula`, `cor_allweights`; haveI "Try this" Main 109, Tests/S06/Hyp 83-86; unused tactic Tests/S06/Hyp 314:8) -> L15b.
  Early pregate (s06-pregate-1): 786/786 without the Defect layer.
- Audits: Fable Lean part 1 (CommAlg) PASS WITH REMARKS 0/0/9 (fixed in L15a); part 2 (Defect layer + Hyp) PASS WITH REMARKS 0/2/11 (+7 optional; `lean/Langlandscape/audits/2026-11-15_s06-part2.md`; fixes L15b; R9-R11 open); part 3 not run (covered by the final gate and int4c-1).
  Fable chapter audits: part 1 0/2/12, part 2 FAIL (M > 1) then PASS WITH REMARKS 0/2/4 on the restricted text; part 3 0/0/7. Cross-account: F1 (s05 blind audit, W = 14), F2 parts A and B (s06-m5 second reader), F4 (xcheck). Notes PDF `mathematics/notes/hsieh-sign.pdf` 4 pp.
- FINAL GATE (s06-final-1 TITAN from scratch + s06-final-1x CONCEPTD fresh, sha 4405815, expected 836/836): PASS: s06-final-1 (TITAN, from scratch, 4405815; result titan/s06-final-1 = ce6d4c2): (a) 4194 jobs rc 0, 319 s, 4.53 GB; (b) VendorStacks rc 0; (c) PrintAxioms 836/836, nonstandard 0; (d) forbidden grep empty; (e) sorry = the import's 1; (f) check_frozen clean; check_wp 32 files OK; GL2TF-free grep empty; 0 S06 warnings (181 Langlandscape / 71 Tests overall). s06-final-1x (CONCEPTD, fresh, 4405815; conceptd/s06-final-1x = 0b691a3): 4194 jobs rc 0, 5:21, 4.3 GiB; PrintAxioms 836/836, nonstandard 0; grep empty; sorry = import's 1; check_frozen clean; 0 S06 warnings. BOTH FINAL GATES GREEN
- latexmk rc 0 for mathematics main (170 pp), standalone-s06 and report at M10c; talk rc 0 (17 pp); PDFs in 4405815.
- int4c-1 (CONCEPTD, sha e69a636, seed s06int4b): lbuild of +Tests.S06.Hyp +Defect.{Galois,Main,Fixed,Corollaries} rc 0, 31 s, 1.5 GiB, 2550 jobs; check_wp Tests/S06/Hyp OK; 0 errors, 0 warnings, no sorry; result branch conceptd/s06-int4c-1 = ad7c093.

hypothesis registry summary (HYPOTHESES.md rows c08c5b76; `report/hypotheses.tex` table regenerated 763bb402; all open unless stated; no instance is called "evidence"):
| `Hyp.*` | content | status | instance in tests |
|---|---|---|---|
| `HsiehGor Λ TB M` | `thm:s04-Gor`: `IsGorenstein A TB ∧ M ≃ TB`, byte-identical with the stage-04 quote | open, cited (Hs Thm 4.5; printed sign issue, FD2) | toy |
| `OldDecomp D` | `lem:s06-decomp`: `NewOldData` fields + `Free (R ⧸ 𝔟)` | open, maths | toy |
| `HsiehGorFull D` | (Gor_R) `IsGorenstein I D.R` | open, cited | toy |
| `FreeRankTwo D` | output of Galois steps 1-3; **equivalent to the conclusion `tq ≤ cq`** (Fable L12 R1; `Defect.freeRankTwo_iff_le`); this is the Galois half of the theorem | open, cited; exact disclosure sentence in docstring, chapter, HYPOTHESES, talk | toy consistency instance (L15b) |
| `ResidualBurnside D` | `I[G] ↠ M₂(I)` | **conditionally discharged** by `Hyp.residualBurnside_of_absIrred` from absolute irreducibility (L6b + L8b) | toy |
| `TamSpec D` | `lem:s06-tam` (a)-(c) | open, maths | toy |
| `HidaControlGL2 D p q M` | control + p-stabilisation + (P2) at weight k (differs from stage-04 `Hyp.HidaControl`; HACS `HidaEns32` not a substitute; docstring pins the normalisation) | open, cited (Hi86b) | toy consistency instance (L15b) |
| `KimOta D p q M` | `thm:s06-KO` at P (N⁻ = q, N⁺ = M) | open, cited (KO Thm 1.1) | toy consistency instance (L15b) |
| `KimOtaRT D p q M` | `D.cqk ≤ 𝔪^t`, inclusion only; q = -1: M = 1 confirmed, M > 1 per F1/(Lev) | open, cited (KO Thm 3.14) | toy consistency instance (L15b) |
Overlaps stated in the rows: `HsiehGor`/`Hyp.X.iso` (Hsieh 4.5, bridge `xiso_of_gorenstein`), `HsiehGorFull`/`Hyp.X.iso` (Helm Cor 8.11), `OldDecomp`/`HidaControlGL2` with HACS `HidaEns31/32`. `Hyp.LambdaJL` used-by updated to `gor_new`, `defect_formula`.
Hypothesis counts at 4405815: 29 registered hypotheses (registry rows, method: `grep -c '^| `Langlandscape.Hyp\.' lean/Langlandscape/HYPOTHESES.md` = 28, plus the reused `GL2TF.Hyp.EichlerMass`); 26 in the report table (rows of `generated/hyp-table.tex`; the 3 stage-5 `Hyp.X.*` are registered but described separately in the planned section), 27 lines mentioning open. `Hyp.X` (stage 05) remains open; FD1/FD2 recorded as decided.

open issues (follow-ups):
- Lean audit part 2 minors R9-R11 are open Lean minors (deliberately not done), as are the optional items of parts 1 and 2.
- **C2 partial:** `C4i.json` covers 131/319 cases (96 dim > 60, 69 over budget, 23 PARI stack); provenance commit field is a dirty-tree sha; the Eisenstein claim needs `O_v` a DVR / `S_m` Gorenstein (fails in 5/46 non-DVR rows at p = 2, 3; chapter caveat added).
- **F1 is numerically untested** (the H3 supplement only has N(rhobar) > 1 cases); **N(rhobar) > 1 is open** (`\stopen`, B2 counterexample refutes only step (4)).
- **(gamma):** the case (gamma) is empty (chapter audit part 3, CONFIRMED by an independent reader, 0/0/7; applied in M10c); proved modulo cited, not formalized.
- Not checkable on this node: Böckle 2007, Dimitrov 2009, EPW06, Edixhoven 1992, Wiles 1988 (scan, no text) — citations at these points are unverified. Hida `P_k` vs HACS `P_{k+2}` normalisation: settled by chapter audit part 2 section 6 (non-substitution), docstring sentence in `HidaControlGL2`.
- H1 dropped: T4 Betti side open (HACS has no Betti-side `coker(Psi*Psi)` computation); `cor:s06-allweights` ord-formula needs `c != 0` at both points (not assumed).
- Toy instances of `HidaControlGL2`/`KimOta`/`KimOtaRT` show consistency (non-vacuity) only; no Lean term discharges any cited hypothesis.
- Warnings: 527 at gate1 (185/76); S06 files 0 warnings at int4b-1/int4c-1. **Lint hygiene deviation:** `linter.overlappingInstances` suppressed locally on 3 headlines (`cor_fixed`, `defect_formula`, `cor_allweights`); the overlap is inherent in `Defect.Setting`'s `IsDomain` + `IsLocalRing` binders; post-Mathathon fix: restructure the Setting binders. `s06-int3c-1` unrecorded.
- Branches/worktrees to clean: impl/s06-* (int1 ... int4a, l5b, l8a-c, l9a, l9b, l10b, l15a, l15b, m5, m5d, m9, m9b, m9c, m10a, m10b, c1, c23, c4, c5, fd, hs, s05fix, t3, thacs, thacs2, x3), `titan/*` and `conceptd/*` result branches; worktrees `../Langlandscape-wt/s06-*`.
- Deferred optional items of L12 parts 1 and 2: not done (with R9-R11).

request: merge wip-implementation into main (Lean tree 4405815) after the final gate PASS; mirror mathematics/main.pdf and talk/main.pdf; then stage 07 (exports: `CommAlg.{IsGorenstein,congruenceIdeal,NewOldData,ThmE,LemmaS,LemmaG,BaseChange,EtaPrinciple}`,
`Defect.{Setting,defect_formula,cor_fixed,cor_allweights,galois,freeRankTwo_iff_le}`, the nine `Hyp.*` with HYPOTHESES rows). Fabian lifted F1 and F1' (F1' under our reading R4); N(rhobar) > 1 is `\stopen`; the fallback revert was dropped. PrintAxioms 836.

## Erratum (global master, 2026-11-15 ~02:15Z)
- Line 26: the sentence on [Hs] is wrong. Correct, as in `mathematics/notes/hsieh-sign.tex`: [Hs] (arXiv v5, §4.5, p. 34) prints JL(U_q) = (−1)·U_q for q | N⁻. With Hsieh's normalisations the correct relation is JL(U_q) = +U_q. Read literally, the printed sign would make the module in Thm 4.5 zero (the theorem would fail); with + it holds. One sentence; no main result of [Hs] depends on it.
