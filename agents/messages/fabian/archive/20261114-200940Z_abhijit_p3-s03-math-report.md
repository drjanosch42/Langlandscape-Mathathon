---
id: 20261114-200940Z_abhijit_p3-s03-math-report
from: abhijit/p3-s03-math
to: fabian/global_master
type: report
re: 20261114-194045Z_fabian_batch1
priority: normal
---
P3 (S03-M1, M3, M4, M5): stage-03 maths chapter, final push.

**Branch** `abhijit/s03-math` @ 055e12c (4 commits on BASE 295db91; one per WP).
**git diff --name-only 295db91...HEAD** = exactly the P3 list:
mathematics/{standalone-s03.tex, chapters/s03.tex, chapters/s03/{1-graphs,3-ribet,4-ihara,5-amalgam}.tex, bib/s03-m{1,3,4,5}.bib}.

**Acceptance** `cd mathematics && flock .../.lls-heavy.lock latexmk -pdf -interaction=nonstopmode standalone-s03.tex`: rc=0;
0 "LaTeX Warning" lines (no undefined refs/cites, no multiply-defined labels), biber clean; 66 pp (s01+s02+s03).
Log tail: "Output written on standalone-s03.pdf (66 pages, 1037460 bytes)". latexmk -c run, no PDF/aux committed.
Sibling labels (prop:s03-phieis, prop:s03-LRdef) are written as \texttt{...} text, not \ref, so nothing is undefined even without 2-eisenstein.tex.

**Labels delivered** (each grep -c = 1):
- M1 (1-graphs): def:s03-graph, rem:s03-grothendieck, prop:s03-phi, lem:s03-cyclic, rem:s03-kirchhoff, def:s03-DR, lem:s03-elliptic,
  prop:s03-mazur, rem:s03-mazur, ex:s03-mazur (table stays \stsketch), if:s03-graph.
- M3 (3-ribet): lem:s03-bip (any comm. ring R; (b) any A), thm:s03-ribet, cor:s03-ihara (new proof of (ii') from C5), if:s03-ribet;
  sign table (C1) stated once, row-by-row = s02 "Sign and index table"; (R4) dependence table.
- M4 (4-ihara): ss:s03-conv (C1)-(C6), each with a check against merged s01/s02; (R1)-(R4); thm:s03-iharaH0 (a)-(c) full proof incl.
  unfolding identity, well-definedness of epsilon, ker eps = im alpha via Pontryagin duality + (ii'); rem:s03-pm; exponent table stated once
  (+1 cohomological, -1 normative homological); cor:s03-eis; rem:s03-T6 (a),(b) proved; if:s03-ihara; (D1)-(D4).
- M5 (5-amalgam): ss:s03-amalgam, prop:s03-amalgam, prop:s03-MV, prop:s03-PsiPsi, def:s03-LR, conj:s03-iharaGL2, if:s03-amalgam.
- New labels (not in stage tex): ss:s03-graphs, ss:s03-ribet, ss:s03-ihara, ss:s03-deviations, rem:s03-torsion (tex's unlabelled remark),
  lem:s03-unfold, lem:s03-adjoint, lem:s03-groups, lem:s03-dcoset.

**Normalisation §0.2.8: CONFIRMED, no correction.** With V = Sym^{k-2}(standard column rep), c = c_{alpha'^{-1}},
T'_q = cor∘res∘c = T_{alpha'^{-1}} = q^{2-k} T_q (the (1,2) entry carries q^{2-k}), T''_q = c^{-1}∘cor'∘res = T_{alpha'} = T_q
(Gamma alpha' Gamma = Gamma alpha'^iota Gamma with explicit gamma_1, gamma_2; T_{lambda g} = lambda^{k-2} T_g). Seed matrix = swapping alpha'<->alpha'^{-1}.
Caveat: the identification "T_{alpha'} = classical T_q (eigenvalue a_q)" is argued (integral lattice, Hecke relation) and cited to Hida 1993 §6.3
pp.175-177 / Stein 2007 §8.3, but translating their right-action (adjugate) conventions into c_g is \stsketch; C5/H1 should confirm.

**Aggregator lines**: main.tex: `\input{chapters/s03}` after `\input{chapters/s02}`. references.bib: no new entries (all four bib files
contain only comments; sources via \lit). Suggested note fixes in references.bib: Ri84 is now in literature/ (ribet_1984_..._scan, image-only;
(2.2) p.506, Prop 3.3 + matrix p.509; weight 2 only); Vo Thm 28.2.3 is p.481 (not 479).
**\providecommand added**: none.

**\provisional issues raised** (statement kept, note in text):
1. def:s03-LR: Ri83 attribution fixed (Ri83 Thm (1.4) p.195 = congruence primes vs cohomological index, not level raising; Ri84 cited with pages).
2. conj:s03-iharaGL2: the "Equivalently, Psi⊗F_l injective" needs in addition (ker Psi)_m = H^1(G,V)_m = 0 (expected, not proved).
The stage tex's F9 \provisional notes are carried over unchanged.

**Deviations / open points**
- Status upgrades with proofs: lem:s03-cyclic, rem:s03-kirchhoff (Cauchy-Binet), lem:s03-bip → \stproved; thm:s03-iharaH0, cor:s03-eis,
  rem:s03-T6(a),(b) → \stpmc (inputs: (iii), density/SA, cited tree lemma); prop:s03-PsiPsi → \stproved in the fixed normalisation.
- Added explicit hypotheses: U factorisable at p for (ii')/(C6)/Thm iharaH0; l ∤ M in prop:s03-MV; -1 acting trivially (V^- vanishes).
- (D) for the amalgam proved elementarily (unipotents dense) instead of via Vo 28.2.3; Serre II.1.4 Thm 3 p.79 cited.
- MV with coefficients: Brown III.6 Exercise p.74 (Cor 7.7 p.51 is trivial coefficients only).
- Ri90 Thm 3.12 does not use the word "Eisenstein" (annihilated by T_r-(1+r)); DT Eisenstein = T_q-2, S_q-1 in m for q≡1 mod d (our cor:s03-eis implies it, d=p).
- Missing literature: SGA7, Ih75, Ed91 (unchanged). Not checked: Diamond-Im 1995 (image-only), Ri84 pp.512-514.
- No unimodularity reference in Voight; lem:s03-adjoint(d) proves it (modular function via det).
