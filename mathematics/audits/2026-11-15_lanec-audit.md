<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Spot-check of the HACS Lane C numbers in the submission (2026-11-15)

Auditor: an independent Fable agent. Base: `final/audit-lanec` at 43310726. Sources of truth:
`plan/hacs/outbox/20261115T0830Z_laneC-summary.md`, `plan/hacs/outbox/20261115T1347Z_laneC-closure.md`,
`code/results/laneC/*.json`, `code/results/s06/T5*.json`, `code/hacs/CHANGES.md`.
Files checked: `mathematics/submission/src/{hacs,limitations,computations,results}.tex`,
`mathematics/chapters/s00/{plan,newknown}.tex`, `talk/slides/{f14-computations,f12-question}.tex`.

## Verdict

**PASS after fixes.** No wrong count, bound or status word was found. Two statements were wider than the sources allow
(F1, F2, both major, applied). Four minor points; three are applied, one is not.

## What was recomputed from the JSON files (not copied from the summaries)

| Claim in the report | Source | Result |
|---|---|---|
| Ihara cokernel: 210 cells, D ∈ {2,3,5,7,11,13}, q ≤ 13, q ≠ D, even k ≤ 14 | `laneC/hj7_ihara_k.json`, `ihara_exact_NEW` | 210 rows, 30 pairs (D,q) × k = 2,…,14; free rank = JL dimension in 210/210 |
| Torsion prime to 6Dq only at (k,ℓ) ∈ {(8,5),(10,7),(14,5),(14,11)}, always ℤ/ℓ | same, `parts.prime_to_6Dq` | exactly these four pairs, 20 cells each, exponent list `[1]` each time; 68 cells with such torsion, 52 torsion-free cells |
| B₁₁, q = 2 examples of the summary | same | k = 4: ℤ³ ⊕ ℤ/11; k = 8: ℤ⁵ ⊕ (ℤ/2)³ ⊕ ℤ/660; k = 14 as in the summary |
| W_D traces against PARI 38/38 | same, `W_D_pari_check` | 38 of 42 rows carry a trace check, all true |
| rk_Δ e ℤ_p[S_s] = 1, s = 1,…,5 | `laneC/hj9_lambda.json` | 1,1,1,1,1; 7/7 cells, 215/215 fields |
| Census bounds | `laneC/hj8_def_native.json`, `census.bounds`, and the loop in `quat/tools/jl_eta_def.cpp` l. 1227–1240 | "q prime, 2 ≤ q ≤ 50; k even, 2 ≤ k ≤ 20; p prime, k < p < 200, p ≥ 5, p ≠ q, p ∤ q²−1": as in the report |
| 5869 cells, 5538 trivial | same, `census.params` | 5869 / 5538 / 166 emitted cells; see F4 |
| 5 genuine congruences, 50 old-congruent, 120 blocks not determined | same, `classification_counts`, and a recount over the blocks | 5 / 50 / 120 (the 120 blocks lie in 114 cells) |
| GL₂ side: 44/44 agree, 6 not run, no disagreement | `laneC/defect_census.json`, `summary` | 55 cells, 49 blocks computed (5 + 44), 49 agree, `blocks_disagree` empty, 6 cells not run, the six named in the summary |
| T5 at weight k+(p−1): 4 computed by Lane C, 3 open | `laneC/T5_hacs.json`, `acceptance` | computed: (13,12,31), (13,18,19), (5,16,31), (5,18,23); open: (13,16,101), (3,18,53), (3,18,61) |
| T5 recount, 6 of 7 | `s06/T5.json` | stage 06 has the GL₂ side with `thm_E_identity` true for (5,18,23), (5,16,31), (3,18,53), (3,18,61) and "not computed" for the three level-13 triples. Lane C adds (13,18,19) and (13,12,31). Only (13,16,101) is open. The count 6/7 in `results.tex` and the text of `computations.tex` are correct |
| D = 13, k = 8 on the intrinsic lattice | `laneC/hj4_congruence.json` | indices 74 = 2·37, 148 = 2²·37, 8 = 2³ for the orbits x−10, x²+19x+6, quartic; see F2 |

The number of triples inside the stated census bounds was also counted independently: 6041. The tool skips modules of
rank 0, and 6041 − 5869 = 172 = 44 + 44 + 43 + 41 is the number of triples at (q,k) = (2,4), (2,6), (2,12), (3,4), where the
module is zero. This identification is an inference from the count and the code, not a logged list.

Status words: no Lane C number is called "certified" in any checked file (the word occurs only in "none is certified" and
"nothing certified"). `flatten.py --check report.tex`: A6 PASS, A13 PASS; A11 lists only the commit-hash placeholder of
the title block (and the definition of its macro); A5 fails for the same hash.

## Findings

**F1 (major, scope) — APPLIED.** Four places said that on the intrinsic lattice "the congruence modules at k > 2 are
invariants", without the restriction to p ∤ D. The summary says: invariants "at every p ∤ D", and "the D-parts depend on
the lattice choice at D". The restriction was present only in the HJ-4a item of `hacs.tex`.
- `hacs.tex`, lattice caveat: now "the $p$-parts of the modules at $k>2$ are invariants for every $p\nmid D$ (the $D$-part
  still depends on a choice)".
- `limitations.tex`: now "makes their $p$-parts invariants for $p\nmid D$".
- `chapters/s00/plan.tex`: now "so that the $p$-parts of the congruence modules at $k>2$ are invariants for $p\nmid D$".
- `chapters/s00/newknown.tex`: now "where such modules are invariants away from $D$".

**F2 (major, number) — APPLIED.** "The congruence 37 at D = 13, k = 8 reappears" is correct for the prime 37, but the
module is not the Lane B module: on the intrinsic lattice the recorded indices are 2·37, 2²·37 and 2³, against 37, 37
and 1 on the Lane B lattice. The slide read "|C| = 37 … (also on Lane C's intrinsic lattice", which states the wrong
order there.
- `hacs.tex`, lattice caveat: "the factor $37$ … reappears there: the indices recorded for the three orbits are
  $2\cdot37$, $2^2\cdot37$ and $2^3$ (\res{laneC/hj4_congruence.json}), not $37$, $37$, $1$."
- `hacs.tex`, HJ-4a item: "the factor $37$ at $D=13$, $k=8$ reappears on it (indices $2\cdot37$ and $2^2\cdot37$ for the
  two congruent orbits, $2^3$ for the quartic one)."
- `newknown.tex`: "its factor $37$ reappears on Lane~C's intrinsic lattice".
- `talk/slides/f14-computations.tex`: "($37$ also on Lane~C's intrinsic lattice; …".
- Not changed: `newknown.tex` and the slide still say that |C| = 37 is the only non-trivial lattice congruence module
  among the cells with k > 2. That is a statement about the Lane B lattice (74 cells) and is true there; on the intrinsic
  lattice the quartic orbit has index 2³.

**F3 (minor, clarity) — APPLIED.** `hacs.tex` said "3 remain open" at weight k+(p−1), and `results.tex` says 6 of 7 are
computed. Both are right, on different routes. `hacs.tex` now says "3 remain open on this route (…, their $\GL_2$ side was
computed in stage~06, \S\ref{sec:comp}; …)", and `plan.tex` says "the three T5 cells at weight $k+p-1$ still open on the
HACS route".

**F4 (minor, scope of a count) — APPLIED.** 5869 is the number of cells with a non-zero module; the stated bounds
contain 6041 triples (see above). `hacs.tex` now says "5869 cells with a non-zero module".

**F5 (minor, stale number) — APPLIED.** `limitations.tex` gave only the Lane A/B battery (248/248). It now reads
"\texttt{--all}, 248/248 after the Lane~A/B merge and 253/253 at the Lane~C closure, and \texttt{GOLDEN\_STRICT} were run".

**F6 (minor) — NOT APPLIED.** Slide f14 says "defect census, 0 disagreements". Proposed text: "defect census, $0$
disagreements among computed blocks". It makes the frame overfull (7.4pt), so the slide is unchanged; the six cells not
run and the 120 blocks not determined are in the report and behind "HACS census leftovers" on frame 12.

**F7 (note) — NOT APPLIED.** `hacs.tex` writes αα† with −T_q and −T_q^T off the diagonal; the summary writes −H′ and
−Hᵀ for the weighted case. No number depends on it.

## Builds

- `report.tex` and `report.pdf` re-flattened (`--draft`, with the fresh `main.aux`): 0 FAIL, 191 pages as before; the
  diff of `report.tex` is exactly the edits above (11 lines).
- `main.pdf` rebuilt: 195 pages as before, **no page shift** (text differs on pages 19, 23, 24 only; all page breaks
  are unchanged). A first, longer wording of the `newknown.tex` edit did shift the pages by one from page 19 on; it was
  shortened for that reason.
- `article.pdf` rebuilt from a fresh directory: 191 pages, text differs on page 17 only.
- `talk/main.pdf` rebuilt: 18 frames, 0 overfull boxes.
- Not rebuilt: `mathematics/submission/src/report-src.pdf`.
- Renders are kept in `/home/janosch/data/scratch/render.OapW`.
