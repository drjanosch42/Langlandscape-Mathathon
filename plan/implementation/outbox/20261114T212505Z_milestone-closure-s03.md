MILESTONE CLOSED: S03 stage-03 implementation (weighted graphs, Ribet sequence, Ihara lemma)
branch/commit: wip-implementation; Lean tree = 5aa765a (final gate), records after it (runs/s03.md b5850a2, this file)

delivered:
- Lean (lean/Langlandscape/, 13 library + 3 Hyp + 8 test modules, all filled, 0 sorry): weighted graphs, X, Φ^comb, sign lemma
  boundary_ofBip (Graph/Weighted, alias Graph.X, Graph.PhiComb); lem:s03-bip (a)–(c) over any CommRing R, rank over ℤ (Graph/BipCollapse);
  prop:s03-phi two-vertex Φ^comb (Graph/TwoVertex); lem:s03-cyclic (Graph/Cyclic); Mazur arithmetic (Graph/MazurArith); prop:s03-phieis abstract
  (Graph/Eisenstein); prop:s03-LRdef abstract (Graph/LevelRaising) + NEW WP L10b: its hsym/hf0/hf1 discharged on Tree.BG at Ô^× and U₀(M)
  (Ribet/LevelRaisingBG, no new Hyp); thm:s03-ribet (a),(c), cor:s03-ihara (i),(ii) on BG over any R + _of_SA_HS (Ribet/Sequence);
  Ribet.mazur_check (Ribet/Mazur); phiComb_eisenstein_Ohat / _DR (Ribet/PhiEis); coefficient two-term complex CoeffData (+ ofLocal), alphaV,
  alphaVee, *_triv (Ribet/Coeff); Ihara (iii) statement layer Ribet.{tau, epsilon, diamond} (Ribet/IharaH0). Exports to 04/05/06 (plan §4) all exist.
  NEW registered hypotheses (explicit Prop args): Hyp.EllipticCount, Hyp.BrandtStabFree, Hyp.IharaH0 (rows in HYPOTHESES.md; instances: none, reasons given).
- S06 early lane (abhijit/s06-l1/l2/l3: CommAlg/{Gorenstein,LemmaS,NewOld}) merged, green (S06-L18 Fable audit still due in stage 6).
- Mathematics: chapter s03 (1-graphs, 2-eisenstein, 3-ribet, 4-ihara, 5-amalgam; NOTES.md; litnotes s03), in main.tex; mathematics/main.pdf (87 pp).
  M1, M3, M4, M5 + drivers from Abhijit's node (abhijit/s03-math); Ψ*Ψ normalisation §0.2.8 confirmed (proved modulo cited, lem:s03-Tclassical).
- Code: ribet/{graphs,mazur,collapse,ihara,betti}.py; results/s03/{T1,T2,T6,betti_det,C3_rerun}.json; pytest 371 passed; H1 on HACS 0.2.1
  (built locally, 8.6 min; code/hacs/jl/s03_h1_rerun.py: det + Ψ*Ψ table = C5 on 14 cases).
- Talk: slides s03-collapse, s03-mazur, s03-ihara; talk/main.pdf (9 pp).
- Experiment E8 (S03-M2, LaTeX hard): winner = opus, merged = opus (opus r0 W=5 → planned fix → r1 PASS W=3; fable single-shot r0 W=4 failed
  on minor > 3); active 21.3 vs 11.0 min, cost 213 vs 184 (LOG.md, events.tsv). Deviation: C3 note given to both blind audits (logged).

verification:
- s03-final-1 (TITAN, from scratch, 5aa765a): (a) Langlandscape+Tests rc 0, 180 s (b) VendorStacks rc 0 (c) 519/519 axiom lines standard
  (d) forbidden-token grep empty (e) only the import's Instances.lean:1815 sorry (f) check_frozen clean; coverage 13/3/8; warnings 171 / 42.
  gate-1 (f6354d1) PASS likewise (516/516; unseeded (a) also green). CONCEPTD cross-check s03-final-1x (from scratch, 5aa765a): PASS, 519/519 standard, 3:16.
- Audits: Fable Lean audit L12 PASS WITH REMARKS (lean/Langlandscape/audits/2026-11-14_s03.md; R1–R3 fixed in L13, green in int12a);
  Fable chapter audit M8 PASS WITH REMARKS (mathematics/audits/2026-11-14_s03.md; M8.1–M8.8 closed in M9); WP audits: opus L2, L3, L14, C4, M3;
  Fable L11 (adversarial), M5 (adversarial); M7 second reader; E8 blind opus strand audits. Reports in plan/implementation/audits/ and experiments/.
- latexmk main.tex rc 0 (87 pp), standalone-s03 rc 0 (80 pp), 0 undefined; talk/main.tex rc 0.

open issues (follow-ups):
- Hypotheses open: EllipticCount (needs the Eichler class number formula), BrandtStabFree (tex proof is elementary; Lean needs lem:s03-nbr +
  ℤ[i]/ℤ[ω] arithmetic, est. 500–1500 lines; its D-prime premise is unused by the tex — flag for Fabian), IharaH0 (needs SA, if:s02-coh;
  clause (b) needs heckeTV, S04-L15a).
- Not in Lean: thm:s03-ribet(b) with coefficients V; cor:s03-eis (eis_support_of_IharaH0); U₀(M) version of phiComb_eisenstein (optional ext).
- L12 hygiene (16 items, carried): unused snake-diagram lemmas in BipCollapse (298–371), triplicated deg0 helpers, two encodings of "two-vertex",
  lambdaBar_bijective_of_pairwise_coprime still takes hcard, file-wide open scoped Classical (LevelRaisingBG, PhiEis), first|… alternations in
  Sequence, lint/long lines; warnings 84 → 171 in Langlandscape/.
- Interface note for 02/04/06 (M7.3): normative homological convention S_ℓ = ℓ^{2−k}.
- Code/maths: JSON provenance commits marked -dirty; Ψ*Ψ off-diagonal slot of q^{2−k} not independently confirmed (PARI/HACS give magnitude);
  bib page notes (Hida, Brown, Serre, Voight) not added to references.bib; M8 optional O3, O11, O12 not done; litnotes MISSING: SGA7, Ih75.
- Deviations: see runs/s03.md (int1 = S06 lane + L1; single-WP jobs and parallel letters on two nodes; L10b added; L2 5 rounds + rescue writer;
  L8/L9 opus fixers; L6/L8 cherry-picked; L4 writer's stray commit in the main checkout (undone, verified) → worktree-only rule; L12 started
  before gate-1; licensing rule mid-stage).
- Stage wall: t0 20:16:53Z → final gate 21:20Z ≈ 1.1 h (plan 2.85 h, range 2.2–3.6 h).
- Branches/worktrees: impl/s03-* and exp/s03-m2-* local (exp never pushed; delete after SUMMARY.md); worktrees left: impl, plan.

request: merge wip-implementation into main (Lean tree 5aa765a); mirror mathematics/main.pdf and talk/main.pdf; then stage 04 X1
(exports: stage-03 §4 + Graph.PhiComb alias, Ribet.phiComb_eisenstein_DR, Ribet.CoeffData.ofLocal, Ribet.diamond).
