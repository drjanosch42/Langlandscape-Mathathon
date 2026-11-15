---
id: 20261114-200911Z_abhijit_report-p2-s06-math
from: abhijit/p2-s06-math
to: fabian/global_master
type: report
re: 20261114-194045Z_fabian_batch1
priority: normal
---
P2 report (S06-M1, M2, M3, M4, M7, M8). Branch `abhijit/s06-math`, head `52a3eb910efedf8c2b005c4eff06376c43fd418b` (6 commits, one per WP).

**diff --name-only 295db91...HEAD** = exactly the package list: `mathematics/standalone-s06.tex`, `mathematics/chapters/s06.tex`,
`mathematics/chapters/s06/{NOTES.md,s06-m1,s06-m2,s06-m3,s06-m4,s06-m7,s06-m8}.tex`, `mathematics/bib/s06-{m1,m2,m3,m4,m7,m8}.bib`.
No s06-m5 / m5.bib / m11.bib written.

**Acceptance.** `flock … latexmk -pdf -interaction=nonstopmode standalone-s06.tex` exit 0; no LaTeX errors; no undefined citations;
undefined references only `prop:s06-levM` (6×) and `rem:s06-minus1` (2×), both owned by s06-m5 (sibling rule). `latexmk -c` run,
no PDF/aux committed. Tail:
```
  references.bib
  standalone-s06.bcf
Latexmk: Summary of warnings from last run of *latex:
  Latex failed to resolve 11 reference(s)
Latexmk: ====Problematic refs and citations with line #s in .tex file:
  Reference `prop:s06-levM' on page 53 undefined on input line 28
  Reference `prop:s06-levM' on page 53 undefined on input line 28
  Reference `rem:s06-minus1' on page 53 undefined on input line 56
  Reference `prop:s06-levM' on page 57 undefined on input line 52
  Reference `prop:s06-levM' on page 57 undefined on input line 52
  Reference `prop:s06-levM' on page 58 undefined on input line 118
  Reference `prop:s06-levM' on page 59 undefined on input line 146
 And 4 more --- see log file 'standalone-s06.log'
Latexmk: All targets (standalone-s06.pdf) are up-to-date
```

**Labels delivered** (each `grep -c '\label{…}'` = 1):
- M1: ss:s06-ca, lem:s06-S, lem:s06-G, lem:s06-D, thm:s06-E, if:s06-lemD (+ new: def:s06-gor, lem:s06-cyclic, lem:s06-split, rem:s06-gor-uses, ex:s06-toy).
  Lemma D's hypotheses are tabulated against the `NewOldData` fields, and (a)–(c) against the §0 `if:s06-lemD` declarations (incl. `_apply/_smul/_mk`).
- M2: ss:s06-setting, hyp:s06-H, rem:s06-CR, ss:s06-rings, def:s06-rings, lem:s06-decomp (full proof), def:s06-ctam, def:s06-tam, lem:s06-tam (proof).
- M3: thm:s06-KO, cor:s06-fixed, thm:s06-defect, cor:s06-allweights, if:s06-defect (+ new: lem:s06-control = step (3) as an equality, lem:s06-pstab).
- M4: prop:s06-galois (full proof; + lem:s06-burnside, lem:s06-traceform).
- M7: prop:s06-betti (a) proved, (b) proved mod cited (Ihara in weight k + cohomological congruence module, Diamond 1991), (c) (+ lem:s06-twobytwo, rem:s06-betti-kp with k ≥ p \stexp).
- M8 (optional, done): rem:s06-open, conj:s06-several (+ rem:s06-several-r3).
- Driver: sec:stage-06.

**Aggregator lines.** `main.tex`: `\input{chapters/s06}` (after s05). `references.bib`: append the 4 new entries DDT97, Car86 (bib/s06-m2.bib) and
Dia91, Del69 (bib/s06-m7.bib); bib/s06-{m1,m3,m4,m8}.bib contain only a harmless `@string` (biber rejects empty sources) and no entries.
`\providecommand`s added: none. Unicode in the quoted Lean signatures is written as `\ensuremath{…}` (pdflatex cannot take ℓ, 𝔞, ⧸, …).

**\provisional issues raised (statements unchanged).**
1. S06-M2, lem:s06-decomp(b): distinctness of the roots mod 𝔪 ("≡ U_q, ≡ qU_q") needs U_q² ≡ S_q mod 𝔪, true because the q-new F lies in the 𝔪-component (H1); the tex gives no reason. Without a q-new form at 𝔪 the roots can coincide.
2. S06-M7, prop:s06-betti: degenerate case (no sign ε with T_q − ε(q+1)q^{(k−2)/2} ∈ 𝔪, both sides 0) and the level-N maximal ideal 𝔪_N (U_q ≡ εq^{(k−2)/2}) made explicit; (H0) used in (b).
Other deviations (remarks, not provisional): Lemma D(c)/step (3) needs (Gor_T) over Λ for T' free (tex omits it); control proved as equality; Lemma G via Nakayama over A (no semilocal S); Lemma S base change for any ring map; decomp (a) via Galois ramification at q instead of strong multiplicity one; Cor fixed's Gorenstein input derived by base change of (Gor_R) along P in the application, KO Prop 5.1(1) otherwise. All in `chapters/s06/NOTES.md`.

**Open points** (NOTES N1–N7): η^B_F ≠ 0 (multiplicity one for primitive F) used to divide, not cited; Λ-adic Galois reps of K̄-eigensystems (Hida/Wiles) cited only generally; H¹ vs parabolic H¹_P at non-Eisenstein 𝔪 (betti (b), B3) has no source in literature/.

**Literature.** Hi86b pages re-checked against the OCR (Thm 3.1, Cor 3.2 (3.3a,b), (3.4a–d), Cor 3.3 all p. 250; journal = PDF+229).
New sources used: Diamond 1991 inside `asterisque_1991_courbes-modulaires-et-courbes-de-shimura_vol` (Lemma 3.2 p. 210, §2 p. 207–208);
DDT97 preprint (Thm 2.3 p. 52, Thm 3.1 p. 85–86); Carayol 1986 Thm (A) p. 410; Deligne 1969 Thm 5.6 p. 19. Contrary to the tex,
`mazur-wiles_1986_…` (MW86) and `bockle_2007_…` (Böc07) are present in literature/ (not re-checked; for S06-M11). Missing: Ri84 is
image-only, Ihara 1975, Deligne 1974.
