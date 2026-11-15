<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# Independent audit of the talk (17 frames), 2026-11-15

Auditor: independent Fable pass. Audited tree: branch `final/audit-talk` at `c6e4703f` (= `wip-submission`).
Audited files: `talk/main.tex`, `talk/slides/*.tex` (not `backup/`), `talk/main.pdf` (17 pages, current with the sources).
Sources of truth: `mathematics/submission/report.tex` (line numbers below are of this file), `mathematics/chapters/s00`--`s06`,
`code/results/*.json`, the gate log `origin/titan/subl-gate-1:lean/Langlandscape/.titan/out/c-axioms.log`,
`lean/Langlandscape/HYPOTHESES.md`, `mathematics/acknowledgments.tex`, the earlier audits in this directory.
Renders: `/home/janosch/data/scratch/render.Qwp5` (70 dpi), `/home/janosch/data/scratch/render.EjDw` (110 dpi).
Not done: no LaTeX rebuild (overfull boxes were judged from the rendered pages only); no external check of the DOIs or of
the HACS GitHub URL (compared with the report only).

## Verdict

**PASS WITH FIXES: 1 blocker, 9 major, 9 minor.** No wrong number was found, and no status is upgraded on frames 2--5,
9--13, 16, 17. The blocker is the deformation-ring sentence of frame 6, which the report does not contain and in one place
explicitly disclaims. All fixes are text replacements that fit the frames; frame 6 and frame 8 have free vertical space.

Severity: blocker = status upgrade, claim not in the report, or wrong number; major = misleading or missing hedge, binding
order, disclosed fact omitted; minor = precision.

## 1. Findings

### Blocker

**B1. Frame 6, `talk/slides/f06-converse.tex:18-20`: deformation rings, cotangent module, numerical criterion.**
The slide claims "and likewise $R_{\GL_2}\twoheadrightarrow R_B$ ... The missing directions live in the cotangent module
$\mathfrak p/\mathfrak p^2$, which congruence ideals measure (Wiles' numerical criterion, Ribet--Takahashi)".
- The report has no deformation ring $R_{\GL_2}$ or $R_B$, no surjection between them, and no statement about a cotangent
  module of our objects (grep: "deformation ring" occurs only at 4146 and in the bibliography).
- The report disclaims it: 3774--3775, "The chapter makes no further comparison; in particular it does not invoke Wiles'
  numerical criterion or Ribet--Takahashi, and none is claimed here."
- What the report does have, as cited context: 3980--3982 (s00/newknown, the known framework) and 4145--4152 (s00/prior):
  "Wiles' numerical criterion compares the congruence ideal $\eta$ of a Hecke algebra with the cotangent space of a
  deformation ring", with Ribet--Takahashi, Pollack--Weston, Kim--Ota, BKM as "the closest results".
- The slide's own comment (line 7) says the wording is "the framing of the talk philosophy; theorems are on Hecke algebras".
  A framing that is not in the report is a claim not in the report.

Replacement for lines 18--22 (keeps the philosophy as cited context, states only what the report states, and adds the
missing condition of M1):

```latex
  \textbf{(ii) Hecke algebras.} $\T\twoheadrightarrow\T'\cong\T_B$ ($\Lambda$-adic Hecke JL, \stcited): the $B$ side is a
  \emph{quotient}, cut out by the stricter condition at $q$ ($q$-new, i.e.\ Steinberg). Eigensystems pull back from $\T_B$
  to $\T$, not conversely. What is lost is measured by congruence ideals, and its size is local:
  \[\operatorname{ord}\eta_f(N)=\operatorname{ord}\eta_f(M,q)+t_f(q)\qquad(2\le k\le p-1,\ \bar\rho\ \text{ramified at $q$ if }q\equiv\pm1\bmod p;\ \text{\stcited: Kim--Ota, Thm~1.1}),\]
  $t_f(q)$ the Tamagawa exponent, $\Lambda$-adically the ideal $\tq_q(F)$ of the entries of $\rho_F(I_q)-1$ (lem.\ s06-tam, \stpmc).\\[1pt]
  {\footnotesize Context (\stcited, not used in our proofs): Wiles' numerical criterion compares $\eta$ with the cotangent space
  of a deformation ring; Ribet--Takahashi, Pollack--Weston and Kim--Ota are the closest results.}
```

Also change the comment line 7 to: `% Deformation rings appear only as cited context (report, Prior work); theorems are on Hecke algebras.`

Alternative, only if the team wants the deformation-ring sentence on the slide: it must first enter the report (s00/motivation,
(M2)) as a statement with status *known, not used* and a reference. I do not recommend this at this stage.

### Major

**M1. Frame 6, `f06-converse.tex:21`: Kim--Ota's formula without their condition (6).**
The slide gives the formula with "(2 ≤ k ≤ p−1; cited: Kim--Ota, Thm 1.1)". Report 3651--3657 (thm:s06-KO) and 3982--3984:
condition (6), $\bar\rho$ ramified at every $q\mid N^-$ with $q\equiv\pm1\bmod p$. Dropping it removes exactly the case the
team extends ((Lev), frame 10). Fixed in the replacement of B1.

**M2. Frame 8, `f08-cokernel.tex:19-20`: "torsion enters only for $p=2,3$ and with non-trivial coefficients".**
Double-check item (4): **not supported as written.** The chapters say: stabiliser orders divide 24 (prop:s01-finite); the
torsion of $H_1(\Gamma_U,\ZZ)$ is killed by 24 and occurs with *trivial* coefficients (rem:s02-torsion, $\ZZ/3$ at $D=2$,
tree prime 3, computed; report 563, 759); for $p\ge5$ the sequence holds *with* coefficients (thm:s03-ribet(b), pmc) and
$H_1(\Gamma_U,\ZZ_p)=H_1(|\mathcal G|,\ZZ)\otimes\ZZ_p$ ((c), last sentence, pmc). Nothing says that non-trivial
coefficients bring torsion in. lem:s03-elliptic gives $w_x\in\{1,2,3\}$ for $q\ge5$ at maximal level only.
Replacement for lines 19--20:

```latex
    \item \textbf{Why $p\ge5$.} The weights $w_e\in\{1,2,3\}$ are half the stabiliser orders (elliptic classes; lem.\ s03-elliptic),
      and all stabiliser orders divide $24$: the torsion of $H_1(\Gamma_U,\ZZ)$ is killed by $24$ (e.g.\ $\ZZ/3$ for $B_2$ at the tree
      prime $3$, \stcomp), so only $p=2,3$ are affected. For $p\ge5$, $H_1(\Gamma_U,\ZZ_p)=H_1(|\mathcal G|,\ZZ)\otimes\ZZ_p$, also with
      coefficients (thm.\ s03-ribet(b),(c), \stpmc).
```

**M3. Frame 8, `f08-cokernel.tex:11`: "The cokernel of Ribet's sequence".**
On frame 7 "Ribet sequence" is $0\to H_1(\mathrm{BG})\to\ZZ[X_B(U')]^0\to(\ZZ[X_B(U)]^0)^2\to0$, which has no cokernel. The
cokernel meant is that of the monodromy sequence $0\to\mathcal X_q\to\mathcal X_q^\vee\to\Phi_q\to0$ of frame 5 (report (R1),
346--352, versus (R3), 364--370). Replacement for line 11, first clause:

```latex
    \item The cokernel of the monodromy sequence $0\to\mathcal X_q\to\mathcal X_q^\vee\to\Phi_q\to0$ (frame 5), combinatorially: for a weighted graph ($\langle e,e'\rangle_w=w_e\delta_{ee'}$):
```

**M4. Frame 7, `f07-tree.tex:10-13`: the letter $q$ changes its meaning inside the frame.**
Lines 10--11: $q$ is the ramified prime ($X_{B_q}(U)$, as on frame 5). Line 13: "the tree $\mathcal T_q$ of $\GL_2(\QQ_q)$,
$q\nmid D$": $q$ is now the tree prime and $D$ the discriminant. The report states the switch explicitly (383--384: "the
chapters' $D$ and $q$ play the roles of Ribet's $q$ and $p$") and that there is no tree at a ramified prime (1102--1103).
Without one clause the audience reads "the tree at the ramified prime". Replacement for line 13:

```latex
    \item \textbf{Tree} (Ihara, Serre). From here $B=B_D$, and $q\nmid D$ is a \emph{second} prime ($D$, $q$ play Ribet's $q$, $p$):
      $\Gamma_U=\mathcal O_U[1/q]^1$ acts on the tree $\mathcal T_q$ of $\GL_2(\QQ_q)$;
```

**M5. `talk/main.tex:61`: binding order.** The binding order is classical JL → what we want → Ribet → BT tree → our
extension. Frame 6 (converse) stands between Ribet (5) and the tree (7), and it already uses the stage-06 objects
($\T\twoheadrightarrow\T'$, $\cc$, $\tq_q(F)$) before stages 04--06 are introduced. Fix: move `\input{slides/f06-converse}`
from line 61 to after `\input{slides/f09-lambda}` (line 63). The order becomes 2 JL, 3 want, 4 setup, 5 Ribet, 7 tree,
8 cokernel, 9 $\Lambda$/Hyp.X, 6 converse, 10--11 defect. Then frame 5's last line ("geometric (bad reduction)") is followed
by frame 7's first ("Replace bad reduction by a group acting on a tree"), and the converse leads directly into the climax.
After the move, the reference "(frame 5)" of M3 stays correct.

**M6. Frame 2, `f02-jl.tex:23`: "A sign error in [Hs] ... (erratum; ...)".** This is finding T4 of
`2026-11-15_final-xacct.md` coming back in weaker form. Report 4371--4402: "as we read it, a sign should be corrected";
"treated as an erratum (team decision FD2)"; the authors intend to contact the author. Replacement for line 23:

```latex
  {\footnotesize In our reading, a sign in [Hs] should be corrected: $\mathrm{JL}(U_q)=-U_q$ to $+U_q$ (\stpmc{} for trivial central
  character at $q$; treated as an erratum by a team decision; to be sent to the author).}
```

**M7. Frame 14, `f14-computations.tex:11` and `:16`: two missing hedges.**
(a) Line 11 lists "the defect data T4, T5, C4(i)" with no word that C4(i) (= C2) is partial; report 1066--1067, 5171--5174,
5913: "C2 partial (131 of 319 cases)". (b) Line 16 calls $|C|=37$ "one cusp--cusp congruence beyond Mazur"; report
5318--5349 and 4077--4079: it is a *lattice* congruence module on a Hecke-stable, non-canonical lattice, on which $C_f$
depends on the choice, and the $\GL_2$ resultant is "consistent with, not a confirmation of" a congruence. Replacements:

```latex
% line 11, end of the Python/PARI bullet:
      $\Phicomb$ and the Mazur check; Ihara's $H_0$; ordinary ranks up the tower; the sign $144/144$; the defect data T4, T5, and C4(i) (partial: $131$ of $319$ cases).
% lines 15-16:
    \item Results (\stcomp): Mazur's $\ZZ/\operatorname{num}\frac{q-1}{12}$ for all primes $q\le600$ at $\ell\ge5$, exactly for the first $80$ primes ($q\le409$; capped run);
      beyond Mazur, one non-trivial lattice congruence module at $k>2$: $|C|=37$ at $D=13$, $k=8$ (non-canonical lattice; consistent with the $T_2$-resultant $2^3\cdot37$); two
      independent exact implementations agree on all $69$ orbit modules.
```

If the frame overflows, drop "(Harder Arithmetic Cohomology System; " to "(" in line 12; the name is in the Releases block
of the report, not needed twice.

**M8. Frame 15, `f15-process.tex:9`: "opencode models: questions and answers only".** The report discloses one exception
(4666, 5475--5478, 5547): the discharge of `Hyp.RamNrdSurj` was drafted by Mistral Large 4 through opencode, outside the
agent process, then audited and gated. Frame 13 counts this discharge among the two. Replacement for the last sentence of
line 9:

```latex
      agents (Haiku, Sonnet, Opus; Fable for audits). opencode models: questions and answers only, plus one disclosed external
      draft (the \texttt{RamNrdSurj} discharge; audited and gated from scratch).
```

**M9. Timing.** 15 content frames with 156--223 words each (frames 6, 8, 9, 11 above 200). A realistic budget is
0:20 + 1:30 + 1:15 + 1:00 + 1:30 + 1:30 + 1:30 + 1:30 + 1:45 + 2:00 + 1:30 + 1:00 + 1:00 + 1:00 + 0:45 + 1:15 + 0:10
= 20:30 (frames 1, 2, 3, 4, 5, 7, 8, 9, 6, 10, 11, 12, 13, 14, 15, 16, 17). There is no slack. To be safely under 20 min:
frames 13, 14, 15 at 40 s each (say only the first bullet and the status line), and frame 4 at 45 s. Frame count 17 is within
14--17. No frame needs to be cut if this budget is rehearsed.

### Minor

**m1. Frame 5, `f05-ribet.tex:12`.** Block title "An integral, Hecke-equivariant exact sequence". thm:s05-G gives
equivariance of (G2) for $T_\ell$, $\ell\nmid N$, only, and (G3) has no Hecke clause; the report calls the *comparison*
Hecke-equivariant (338--341) and $\Phi$ Eisenstein (Ribet, Thm 3.12). Double-check item (5): acceptable with the scope
stated. Replacement: `\begin{block}{An integral exact sequence, equivariant for $T_\ell$, $\ell\nmid qM$}`.

**m2. Frame 7, `f07-tree.tex:11`.** "(identification: Deligne--Rapoport, cited; along the tower: Hyp.X)". Double-check
item (6): correct in substance; the identification of the edge set with the class set is Deuring and Ribet, Props 3.1, 3.3,
not Deligne--Rapoport alone (thm:s05-G(i),(ii); report 353--358). Replacement:
`(identification at $\Gamma_0$-level: Deligne--Rapoport, Deuring, Ribet, \stcited; along the tower: Hyp.X).`

**m3. Frame 10, `f10-defect.tex:17-18`.** "$\ell^2\mid M$" should be "$\ell^2\mid M$ at a prime $\ell$ where $\bar\rho$ is
unramified" (report 3710); "Hecke algebra not Gorenstein" should be "the quaternionic Hecke algebra is not Gorenstein"
(rem:s06-open(iii)). Replacement for the two clauses: `($N(\bar\rho)>1$, or $\ell^2\mid M$ with $\bar\rho$ unramified at $\ell$).`
and `Excluded: trivial primes (quaternionic Hecke algebra not Gorenstein; \stcited: B\"ockle--Khare--Manning).`

**m4. Frame 11, `f11-defect-why.tex:17` and `:21-23`.** (a) "Kim--Ota Thm 1.1 at one point" covers only (H0$^-$); under
(Lev) the input is prop:s06-levM (report 3716--3718). Replacement: `Kim--Ota Thm~1.1 at one point under (H0$^-$), prop.\ s06-levM under (Lev)
(fixed weight; in the line of Wiles' numerical criterion and Ribet--Takahashi).` The phrase "in the line of" is covered by
report 4145--4152 and may stay. (b) prop:s06-betti needs $p>k\ge4$ and $q\not\equiv-1\bmod p$; add `($p>k\ge4$, $q\not\equiv-1\bmod p$)`
after "on the Betti side". (The slide's "pmc" for all of it is a downgrade of (a), which is proved; fine.) (c) Line 27:
`Thm~E (i)--(iv) \emph{formalized} (abstract; exceptions as listed in the report).`

**m5. Frame 12, `f12-question.tex:13, 17, 21-22`.** (a) Line 13: "\emph{formalized}" alone can be read as unconditional
(finding T9 of the cross-account audit); replace by `\emph{formalized} given \texttt{Tree.BGConnected}`. (b) Line 17:
"control" should be "finite-level control" (thm:s04-control(a) is proved; (b) is cited or a sketch). (c) Line 21: the report's
open column for (e) has "C2 partial" (1077); replacement for lines 21--22:
`Brandt modules, $\Phicomb$, ordinary ranks, defects ($7/7$ triples; regression partial, $131/319$); Mazur through HACS, $q\le600$ (\stcomp) & canonical lattices at $k>2$; full census to $q=2777$\\\bottomrule`.
Double-check item (7): "canonical lattices at $k>2$" and "full census to $q=2777$" are both in the report as open items
(5914--5916, 4080). Lane C is not merged in the audited tree (no Lane C result files), so the wording is correct now. **If
Lane C is merged before the talk**, change to `canonical lattices at $k>2$ (Lane~C's intrinsic lattice addresses this)`,
as in report 5345--5346 and 5916.

**m6. Frame 16, `f16-new-known.tex:14, 20`.** Line 14: "quotient $\Leftrightarrow$ connectivity (SA-free)" is garbled;
prop:s02-BG says strong approximation at one level is equivalent to the connectivity of $\mathrm{BG}(U,q)$. Replacement:
`the integral framework assembled; SA at one level $\Leftrightarrow$ connectivity of $\mathrm{BG}$ (a finite check); Ribet sequence, Ihara on the tree (given connectivity; method: Ribet, Livn\'e, Edixhoven) &`.
Line 20: add the hedge of s00/newknown for (F1$'$): `(F1$'$, in our reading of [KO, Thm~3.14])`. Double-check item (8): with
these two changes the "ours" column agrees with s00/newknown (3986--3992, 4063--4068), and the footnote line 27 carries the
novelty hedge.

**m7. Frame 14, `f14-computations.tex:21`.** The URL `github.com/drjanosch42/hacs` is not in the report (the report gives the
DOIs only). The three DOIs agree with the report (5194--5195, 5834) and with the task: v0.2.1 `10.5281/zenodo.24231446`, all
versions `10.5281/zenodo.24118841`, data `10.5281/zenodo.24147012`. Keep the URL only if the master confirms it. The JL module
is in our repository (`code/hacs/`), not in the v0.2.1 release (note N2 of the cross-account audit); suggested addition at
the end of line 21: `The JL module is in our repository, not in this release.`

**m8. Frame 3, `f03-want.tex:9`.** The arrow $H^0(\text{quaternionic})_\m\to H^1(\GL_2)_\m$ fixes a direction; the report's
question (298--310) says "maps" between degree 0 and degree 1 without a direction. Either keep and say "in either direction",
or write `H^0(\text{quaternionic})_\m\ \longleftrightarrow\ H^1(\GL_2)_\m`.

**m9. Readability.** No overfull or cut text on any page. Frames 12 and 16 (`\footnotesize` tables) and the `\footnotesize`
lines of frames 2, 10, 11 are legible at 16:9. On frame 16 the `\scriptsize` line sits directly under the bottom rule; add
`\smallskip` before line 27. Frames 6, 8, 11 are text blocks of 216--223 words: readable, but nobody reads them during a
talk; they are speaker notes on a slide. No change required.

## 2. The talk writer's double-check list

| # | item | verdict |
|---|---|---|
| 1 | frame 6: $R_{\GL_2}\twoheadrightarrow R_B$, cotangent $\mathfrak p/\mathfrak p^2$, "Wiles' numerical criterion, Ribet--Takahashi" | **Not in the report** as a claim; s06 disclaims it (3774--3775). Only the cited context sentence of s00/prior (4145--4152) and s00/newknown (3980--3982) exists. Blocker B1. |
| 2 | frames 10, 16: $\eta_f(M,q)$ = quaternionic $\eta^B_f$ | OK. Report 3379--3380 and 3764--3766: "$\eta_f(M,q)$ is the congruence ideal of the $q$-new quotient, i.e. of the definite side via JL"; cor:s06-fixed step (2): literally [KO, Def. 2.11] for $N^-=q$. |
| 3 | frames 10, 16: "including $k\ge p$", "all weights $k\ge3$" | OK. cor:s06-allweights (3747--3761): every arithmetic point of weight $k'\ge3$, trivial character, including $k'\ge p$; "goes beyond [KO]". |
| 4 | frame 8: torsion "only for $p=2,3$ and with non-trivial coefficients" | **Not supported**; downgraded in M2. |
| 5 | frame 5: Hecke-equivariant sequence $0\to X\to X^\vee\to\Phi\to0$ | OK with the scope "$T_\ell$, $\ell\nmid qM$" (m1). Sequence: thm:s05-G(G3), report (R1); isomorphism and equivariance: (G2), Ribet Prop. 3.1; Mazur at $M=1$: (R2). |
| 6 | frame 7: two-vertex graph = dual graph (DR cited; tower Hyp.X) | OK in substance; attribution completed in m2. Report 1102--1106. |
| 7 | frame 12: "full census to $q=2777$", "canonical lattices at $k>2$", C2 131/319 | The two open items are in the report (5914--5916). C2 partial is missing on frames 12 and 14: m5(c), M7(a). Lane C condition: m5. |
| 8 | frame 16 "ours" column vs s00/newknown | OK after m6 (one garbled entry, one missing hedge). |
| 9 | frame 16: 26 open hypotheses | OK. 29 − 2 − 1 = 26; report 4611--4614, 5862, 5892, 5936; `HYPOTHESES.md` has 29 rows `Langlandscape.Hyp.*` (28 + the reused `GL2TF.Hyp.EichlerMass`, the alias row not counted, as the report explains). |
| 10 | frame 13: 950/950, tree 28d2b091, two machines, 4199 jobs | OK. Gate log: 950 lines, 0 with `sorryAx`. Report 4436--4452, 4523--4525. One sorry in the built import, a second in a never-built module: as on the slide. |
| 11 | frame 2: "proofs via the trace formula" | OK. Report 4091--4093 ("by comparing the Selberg trace formulas"), 4098--4099. |

## 3. Frame by frame

| frame | file | result |
|---|---|---|
| 1 title | `main.tex` | OK. Literal date. |
| 2 | `f02-jl.tex` | Statement = thm:s01-JLclassical (cited). $U_\ell\mapsto+\Pi_\ell$: prop:s05-sign(a), pmc at $\Gamma_0$, weight 2. `T05-1.json`: 144 eigenlines, 144 plus, 0 minus, 0 unmatched. `brandt_w2.json`: $T_2=[[1,2],[3,0]]$, eigenvalues 3, −2, $a_2(11a1)=-2$. M6. |
| 3 | `f03-want.tex` | (a)--(e) as in report 298--310; scope as in 419--432. m8. |
| 4 | `f03-setup.tex` | OK against report 445--572 and hyp:s06-H. |
| 5 | `f05-ribet.tex` | OK; m1. |
| 6 | `f06-converse.tex` | B1, M1. (i) is supported: report (M2) 281--285, 3105 (local JL, [JL, Thm 15.1]), def:s06-ctam, prop:s06-betti(b) (pmc; its range $p>k\ge4$, $q\not\equiv-1$ is not on the slide: say it). |
| 7 | `f07-tree.tex` | Statuses correct (thm:s03-ribet(a), cor:s03-ihara(i),(ii), prop:s02-BG; Lean wording as in the report). M4, m2. |
| 8 | `f08-cokernel.tex` | prop:s03-phi, prop:s03-mazur (pmc), census 109/109 and the first 80 primes $q\le409$ (capped, own exact route): as in report 5300--5316. $\pi(600)=109$, 80th prime = 409. M2, M3. |
| 9 | `f09-lambda.tex` | OK. `H7.json`: orders 10, 250, $U_p^*=5$, $e=0$ on $\Phi\otimes\ZZ_5$. lem:s04-ekills(a), thm:s04-control(a) proved; thm:s04-lambdaribet given connectivity; Hyp.X open; (c2) open. |
| 10 | `f10-defect.tex` | Statement and status = thm:s06-defect, cor:s06-allweights. m3. |
| 11 | `f11-defect-why.tex` | thm:s06-E, prop:s06-galois, squeeze, Lean wording: as in the report. m4. |
| 12 | `f12-question.tex` | Agrees with report 1014--1079. m5. |
| 13 | `f13-lean.tex` | OK (item 10). |
| 14 | `f14-computations.tex` | Numbers OK (69 orbits, 64.7 s vs 0.02 s, D1--D8, DOIs). M7, m7. |
| 15 | `f15-process.tex` | Wall times = report table 5745--5750. M8. |
| 16 | `f16-new-known.tex` | m6, m9. |
| 17 | `acknowledgments.tex` | Wording identical to `mathematics/acknowledgments.tex`. |

Earlier audit findings checked for regressions: T1 ($q\le479$ versus 409) fixed and still fixed; T2 (scope on the defect
frame) fixed; T5 ($\Lambda$-adic Ribet "given connectivity") fixed; T6 (own exact route, cap) fixed on frame 8; T12
(sorry wording) fixed; T4 (Hsieh's sign) partly back, M6; T9 ("formalized" unqualified) back on frame 12, m5(a).

## 4. Outside the talk (for the master; not counted above)

- **R1. The report still calls the previous gate "the final gate" in one place.** `mathematics/chapters/s00/outline.tex:66`
  → `report.tex:1181-1184`: "The final gate built the tree from scratch at commit `2323a252` and checked $840/840$
  declarations". Everywhere else the report, and the talk, say 950/950 at tree `28d2b091`. Replacement:
  `The final gate built the tree from scratch (gate commit \texttt{dc61af50}, Lean tree of \texttt{28d2b091}) and checked $950/950$ declarations against the standard axioms`.
  The earlier report audits predate the regeneration and did not see this.
- R2. Two `\TODOFACT` placeholders remain in `report.tex`: line 214 (full commit hash; expected until the end) and line 5400
  ("Lane C closure numbers").
