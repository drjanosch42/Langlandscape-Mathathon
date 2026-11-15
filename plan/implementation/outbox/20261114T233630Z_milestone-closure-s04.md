<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
MILESTONE CLOSED: S04 stage-04 implementation (ordinary projector, Hida control, Λ-adic Ribet sequence)
branch/commit: wip-implementation; Lean tree = 71576d1c (final gate), records after it (runs/s04.md 2c10480c, this file)

delivered:
- Lean (lean/Langlandscape/; 20 library + 5 Hyp + 20 test modules, 0 sorry):
  ordinary projector D-e (Ordinary/Projector: ordPart, nilPart, HasOrdDecomp, ordProj, ordPart_exact), finite-length/ZMod(p^m) instance
  (Fitting), **f.g. ℤ_[p] instance padicOrdDecomp_holds — Hyp.PadicOrdDecomp DISCHARGED (F-e: L3 green)** (PadicDecomp, Weierstrass route);
  group-ring locality + freeness (GroupRing, Abhijit), inverse-limit layer Compat/lim_exact/Lam + mapLam (InvLimit, Abhijit);
  lem:s04-ekills (a),(d) (EKills: deg, ordPart_ker_deg, perfect_ordPart_pairing), (b),(c) abstract + v_p|X_s| ≥ 2s−2 (EKillsGraph);
  U'_p, U_p^*, diamondM, U_p^* = ⟨p⟩_M U'_p (Brandt/UpAdjoint; sign +1 pinned by C3a), Kpp level (Local/HidaLocal = E1′ opus strand,
  audit-fixed), abstract control (ControlAbstract), UpAt at general levels + Hida (b) + π'' fibres/freeness (KppTower);
  Brandt towers: **ekillsA_tower (stage-05 export)**, control for UU_s and U0q q UU_s (surjectivity + ker_ordPush), pairing (Tower);
  ordFree_finite (TowerRank); ordinary Ribet sequence at level s, BG↔ZX bridge (RibetFinite, RibetFiniteFull); Mord, Xord,
  lim_exact_ribet (Limit); unconditional forms *_uncond (TowerUncond); Hecke with coefficients heckeTV (HeckeCoeff), V_k + UpV + ev (Quat/Vk, UpCoeff).
  Hypotheses (rows in HYPOTHESES.md): PadicOrdDecomp (discharged), HidaControl (schematic; U_1(M), p ∤ φ(M)), HsiehCR (+ toy instance),
  MordLambdaFree (open), InvLimExact (open; connectivity premise). Errata: Hyp.LambdaJL diamond clause classical ⟨d⟩ ↦ seed ⟨d⟩⁻¹ (d prime to Mp).
  Module system: 19 Mathlib-only files converted (S04-MOD); minimised imports of the new s04 files (S04-IMP) + abhijit/min-imports merged.
- Mathematics: chapter s04 (Abhijit's package + M8 second reader + M9 Fable audit + M10a/b/c fixes, xacct s04 X1/X2 fixed); errata lane for the
  s01/s02/s03 cross-account reviews (E1M); mathematics/main.pdf 106 pp (latexmk rc 0).
- Code: ordinary/{proj,tower,sign_pin,phicomb,e_vs_estar,t3}.py; results/s04/{H6_sign,T3,H6,C2,H7,M95_e_vs_estar}.json; pytest 397 passed.
  Key numbers: rk_Δ e = 1 (s = 1,2,3, B_3, p = 5); C2 matches the ordinary 3-new form 15a, diamonds = P^ad_k (nebentypus inverted);
  U_p^* = ⟨p⟩_M U'_p exact (sign +1); e = 0 on Φ^comb (q = 11, 23).
- Talk: slides s04-nonord, s04-tower; talk/main.pdf 11 pp.
- Experiment E1′ (S04-L6, Lean hard): winner = sonnet strand (escalated to opus at r1), merged = opus strand; Lean-hard cell now decided (prior):
  sonnet first + 1 opus fix off the critical path, opus on it (LOG.md, SUMMARY.md, model-selection.md on main 90eba49).

verification:
- s04-final-1 (TITAN, from scratch, 71576d1c): (a) Langlandscape+Tests rc 0, 251 s (b) VendorStacks rc 0 (c) PrintAxioms 592/592 standard
  (d) forbidden grep empty (e) sorry = the import's Instances.lean:1815 only (f) check_frozen clean; coverage 20/20/5; warnings 169 / 47.
  CONCEPTD cross-check s04-final-1x (fresh unseeded checkout, 71576d1c): PASS all six steps, 592/592, 3:50.
  gate-1 (e7285a99) PASS likewise (558/558; unseeded from-scratch also green).
- Audits: Fable Lean audit L16 parts 1, 2a, 2b (lean/Langlandscape/audits/2026-11-14_s04.md; 17 required, all closed by L17a/b/c, green in
  int7b/int12c/int15); Fable chapter audit M9 + M8 second reader (closed in M10a); cross-account s04 review (closed in M10c); E1′ blind Fable strand audits.
- latexmk mathematics/main.tex rc 0 (106 pp), talk/main.tex rc 0 (11 pp); pytest code/python 397 passed.

open issues (follow-ups):
- Not formalized (deviations 7, 8): A-surjectivity on the concrete Ribet systems (Hyp.InvLimExact open; the snake theorem was dropped),
  ordRank_const, the control quotient iso e/(e ∩ ker π''_*) ≃ e R[X_s] and its tensor form, diamondM = ∏ one-prime diamonds, the Λ-module
  structure from concrete diamonds (Hyp.MordLambdaFree open), thm:s04-control(b) (Hyp.HidaControl schematic), lem:s04-hida (c) isos, (b) cohomological.
- S04-IMP-old (82 old GL2TF-dependent files): moved to the stage boundary (global master).
- Public/private import split (S04-MOD step b): not done.
- Warnings 169 in Langlandscape/ (largest: Graph/Cyclic, Ribet/Sequence, Tree/QuotientCore, Graph/TwoVertex).
- η-principle Lean (CommAlg.EtaPrinciple) is stage 06 (S06-L17); the chapter keeps it \leanplanned.
- Stage wall: t0 21:24Z → gate-1 PASS 23:21:55Z (1.97 h) → final gate PASS 23:35:38Z ≈ 2.2 h (plan 3.0 h, range 2.6–3.8 h).
- Branches/worktrees: impl/s04-* and exp/s04-l6-* local (exp never pushed); worktrees left: impl, plan (+ s04 WP worktrees, removable).

request: merge wip-implementation into main (Lean tree 71576d1c); mirror mathematics/main.pdf (106 pp) and talk/main.pdf (11 pp); then stage 05
(exports: Ordinary.ekillsA_tower + ekillsA_tower_uncond, Ordinary.deg, ordPart_ker_deg, Mord/Xord/Lam, lim_exact_ribet; HYPOTHESES rows).
