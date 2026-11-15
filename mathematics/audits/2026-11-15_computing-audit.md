<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Audit: `mathematics/chapters/s00/computing.tex` ("How the route makes JL computable, and how we implemented it in HACS")

- **Audited state:** branch `final/audit-computing` at 8a4a258e (= wip-submission). Independent read, one reader, about 30 min.
- **Compared with:** `code/hacs/CHANGES.md`, `code/hacs/README.md`, `code/hacs/PROVENANCE.md`, `plan/hacs/REPORT.md`,
  the Lane A/B/C closures in `plan/hacs/outbox/` (Lane B with its erratum; Lane C summary and closure),
  `code/results/laneC/hj4_congruence.json`, `mathematics/submission/src/hacs.tex`, `lean-discipline.tex`, `lean.tex`,
  `mathematics/chapters/s00/achieved.tex` (e), `ribet.tex`, `lean/Langlandscape/HYPOTHESES.md`.
- **Builds:** `article.tex` and `main.tex` compile after the fixes (latexmk, rc 0, no undefined or multiply defined
  references), in `/home/janosch/data/scratch/render.CcQJ`. The flattened `report.tex` was not rebuilt (later step).

## Verdict: PASS after fixes (0 critical, 3 major APPLIED, 6 minor: 5 APPLIED, 1 NOT applied)

No "certified" (the word occurs only in the disclaimer "none is called certified"), no status upgrade, no names, machines,
URLs or DOIs in the section. All numbers of the writer's table agree with the sources (list at the end).

## Major (all APPLIED in `computing.tex`)

**M1. "none is recorded in our sources" (three-strands paragraph) is false.** Old text: "A disagreement between two strands
would be a bug in one of them; none is recorded in our sources (in Lane C: no computed block disagrees)." The report itself
records disagreements between strands: the computed counterexample B2 refutes proof step (4) of the stage-06 case
N(rho-bar) > 1 (`stage06.tex`, `limitations.tex`, `aiuse.tex`), and the planned check "rk T'_m >= 2" is false, the rank is 1
(`computations.tex`). Replacement applied:
> A disagreement between two strands points to an error in one of them. Where one occurred it is recorded and the text was
> corrected: for instance, a computed counterexample refuted one step of a stage-06 proof outside the hypotheses now stated
> (that case is marked open), and one planned stage-06 check turned out to be false as posed. In the comparisons reported
> above no computed cell or block disagrees with its reference.

**M2. "over a field, where all the cokernels above vanish" is mathematically wrong.** The paragraph just before speaks of
"the free rank of the cokernel", and the Ihara cokernel has free rank dim S_k(Gamma_0(Dq))^new (Lane C, 210/210); only the
finite groups vanish over a field. Replacement applied: "where the finite groups above (the congruence modules and the
torsion of the cokernels) all vanish."

**M3. Ribet map written as `alpha = (-s_0^*, s_1^*)`, against the chapters and against `s00/ribet.tex`.** The introduction
(`ribet.tex`, l. 60) and stages 02/03 define alpha = (-s_{0*}, s_{1*}) (push-forward, Z[E] -> Z[X]^2); the upper-star form is
its transpose (`s03/3-ribet.tex`, l. 26). As written, alpha and iota differed only by a global sign, which a non-expert must
read as "the same map". Replacement applied:
> The Ribet map alpha = (-s_{0*}, s_{1*}), which sends an edge to its two endpoints (with signs), and the Ihara map
> iota = (s_0^*, -s_1^*), which pulls functions on the vertices back to the edges, are built from the two ways s_0, s_1 in
> which an edge of the graph meets its endpoints; both are explicit integer matrices.

## Minor

- **m1 (APPLIED).** "two generator-regenerated count tables of the manual": the files are `counts.tex` and `validations.tex`
  (CHANGES.md); now "two generator-regenerated tables of the manual".
- **m2 (APPLIED).** Census bounds "with the stated exclusions": the exclusions are stated only in the report's HACS section,
  not in the article or main.tex. Now explicit: "q <= 50 prime, even k <= 20, primes k < p < 200 with p >= 5, p != q,
  p does not divide q^2 - 1" (Lane C closure §2).
- **m3 (APPLIED).** Validation: "one full battery" while the slow tier was not run; and `LABEL_CENSUS` was missing from the
  not-run list (closure §3). Now "one battery ... the slow tier, the digests, the label census and the device lane were not run".
- **m4 (APPLIED, readability).** The D = 13, k = 8 sentence of Lane B had the lattice caveat nested in the middle; split
  into three sentences, same content, with a pointer to Lane C.
- **m5 (APPLIED).** Lean paragraph: "the statement compiles ... contains no gap" now "the statement and its proof compile ...
  the proof contains no gap ... depends on no axiom beyond the three standard ones" (23 audited declarations use only
  `propext`, 3 none; `lean-discipline.tex`).
- **m6 (NOT applied, outside this file).** `mathematics/submission/src/hacs.tex`, HJ-7a item, has the same upper-star
  notation `alpha = (-s_0^*, s_1^*): Z[E] -> Z[X]^2` (copied from the Lane C summary, "alpha = d"). Recommended:
  `\alpha=(-s_{0*},\,s_{1*}):\Z[E]\to\Z[X]^2`, as in the chapters. Left for the owner of that (already audited) file.

## Checked and found correct (no change)

- **HACS description:** name, C++ with AVX-512/CUDA, no external test framework, `--list`, `--all` (fast + standard tiers),
  golden reference in tiers A and B under the strict regression: `code/hacs/README.md`. v0.2.1 code-identical to the
  snapshot: `plan/hacs/REPORT.md` item 8. Seed imported with only the documented path scrub; three hook lines (one
  `include` in `CMakeLists.txt`, declaration and call of `RegisterJL()`); upstream 294 names in order, ours after:
  `CHANGES.md`, Lane C closure §3/§4. Python drivers outside the binary with provenance (commit, params, binary sha256):
  Lane C closure §1. All paths named exist.
- **Lane A:** 66/66, 8/8, D = 11 non-etale and Gorenstein at 5 with clean controls, 74 records (`hacs.tex`, Lane A closure).
- **Lane B:** 69/69 orbits; 109/109 levels q <= 600 at l >= 5; first 80 primes, q <= 409, capped (erratum respected, not 479);
  D = 13, k = 8: Z/37, Z/37, 0 on the Hecke-stable lattice; resultant wording "consistent with, not a confirmation".
- **Lane C:** 66/66 and 374/374; indices 74 = 2·37, 148 = 2^2·37, 8 = 2^3 read from `hj4_congruence.json`; invariance for
  p not dividing D only; 288/288; 210/210; rank 1 for s = 1..5; T5 7/7 at weight k; H3 9/9; census 5869, 5/5, 44 of 50
  (6 not run), 120 not determined, no computed block disagrees; PARI sign in 3 cells, 30/30; 253/253; golden 0 failures.
- **"Why computable":** finite class sets, free Z-modules (invariants in a lattice are free), integer matrices, Smith form,
  index = |det|, Gram determinant: correct. Item (e): same status as `achieved.tex` (finite objects, computed, the GL_2 map
  at Gamma_1-level open and needing Hyp.X, GL_2 data computed independently and compared).
- **Lean paragraph:** 950 audited declarations, from-scratch build, three standard axioms, hypotheses as explicit `Prop`
  arguments, 29 registered / 2 discharged / 1 conditionally (`HYPOTHESES.md`, `lean-discipline.tex`); abstract data and
  schematic JL interfaces are said; nothing claims that the theory as a whole is formalized.
- **Bibliography:** `HACS021` and `HACSdata020` in `mathematics/references.bib` are identical to
  `mathematics/submission/src/report-own.bib` (author "The HACS authors").
- **Cross-references:** `ss:s00-map`, `ss:s00-hope`, `ss:s00-question` resolve in article and main; `sec:hacs`, `sec:lean`
  exist in the report sources and are used only under `\ifdefined\sOOsummary`.
