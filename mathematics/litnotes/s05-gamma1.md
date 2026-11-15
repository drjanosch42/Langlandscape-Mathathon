<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S05-M6 literature note: Gamma_1-level Deligne–Rapoport / Deuring / character groups

- WP: S05-M6 (batch 3, B2). Question: which parts of Hyp.X (`hyp:s05-X`, (X1)–(X4)) are stated in the literature at level
  Gamma_1(Mp^s) ∩ Gamma_0(q), with U_p, diamonds and naturality in s. Text: `chapters/s05/status.tex` (`ss:s05-status`).
- Searched statements: **S1** semistable model / two copies of X_1(N) crossing at supersingular points (DR at Gamma_1);
  **S2** X_q(J) = Z[class set at U_1(N)]^0 with T_l, U_p, diamonds (Deuring at Gamma_1); **S3** monodromy pairing
  w_e δ and Φ = X^∨/X at Gamma_1; **S4** Frobenius / U_q on the torus with nebentypus, model and functoriality conventions;
  plus naturality in the level.
- Pages: printed page, PDF page in brackets. Paraphrases only. Image-only scans were read on rendered page images.
  Offsets: DR printed = PDF + 142 (page number at top); Ribet–Stein = PDF − 4; Helm 2007 = PDF + 60; Astérisque 196–197
  = PDF − 5; Diamond–Im scan is 2-up (PDF k = pp. 2k+36, 2k+37); CSS volume ≈ PDF − 18; Ribet 1988 Exposé p. 6-0k = PDF k+1.

## Verdict per source

1. **deligne-rapoport_1973_les-schemas-de-modules-de-courbes-elliptiques** — S1 HIT (general level H).
   Ch. VI, Thm. 6.9, pp. 286–287 [PDF 144–145]: for H ⊂ GL(2, Z/n), p ∤ n, the coarse level-H-with-Gamma_0(p) scheme over
   Z[1/n] is smooth outside the supersingular points in characteristic p; its fibre at p is two copies of the level-H curve
   crossing transversally at the supersingular points, the point x of the second copy glued to x^(p) of the first; at a
   supersingular point the singularity is of type A_{k−1}, k = |Aut(E,α)| or half of it when −1 is an automorphism.
   Ch. V, Thm. 1.16 p. 243 [PDF 101], Var. 1.17 pp. 243–244, Var. 1.18 p. 245 [PDF 103], 1.20 p. 245: fine-moduli versions.
   Gamma_1 is not named, but H = the Gamma_1(n) group is allowed. No S2–S4.
2. **diamond-im_1995_modular-forms-and-modular-curves_scan** — S1 HIT (explicit Gamma_1(N) ∩ Gamma_0(p), N > 3); S4 partial.
   Thm. 8.3.1, p. 72 [PDF 18]: the moduli problem of triples (E, P, C), P a point of order N (naive model), C of order p, is
   representable by a regular scheme over Z[1/N] (a consequence of DR V.1.20 and Katz–Mazur). §8.4, pp. 72–74 [PDF 18–19]:
   maps i_F (Frobenius) and i_V (Verschiebung) from Y_1(N)_Fp are closed immersions whose images are the two components,
   meeting at the supersingular points; (8.4.1), p. 73: the composites of the two degeneracy maps with i_F, i_V are ⟨p⟩, Φ,
   Φ, id (absolute Frobenius Φ). So the diamond ⟨p⟩ enters the gluing in the naive model. Rem. 10.2.1–10.2.2, p. 84
   [PDF 24]: T_n^* = ⟨n⟩^* T_n on J_1(N); w_p^2 = ⟨p⟩ for the Atkin–Lehner involution of the Gamma_1(N,p) Jacobian;
   w_N ⟨d⟩ w_N = ⟨d⟩^*. No character-group statement (S2, S3) on the pages read (pp. 72–75, 84–85).
3. **helm_2007_maps-between-modular-jacobians-and-jacobians-of-shimura-curves** — S1 HIT (Shimura and modular curves,
   any Gamma_H(N)); S2 partial.
   Def. 2.1, p. 65 [PDF 5]: Gamma_H(N) for H ⊂ (Z/N)^×, so Gamma_1(N) is included. Appendix Thm. 10.2 (Buzzard; level inside
   Gamma_1(r), r > 3), p. 113 [PDF 53], Thm. 10.3 (arbitrary Gamma; regularity away from supersingular points; Frob and Ver
   closed immersions onto the two components meeting transversally; local ring W[[X,Y]]/(XY − p^k)), p. 114 [PDF 54].
   Thm. 5.4, p. 84 [PDF 24]: Ribet's exact sequence of character groups at level Gamma, T^D-equivariant; for D = 1 the
   proof refers to Ribet 1990 Thm. 4.1 (which is written for Eichler orders, Ribet p. 456), the extension being asserted.
   No identification X_q(J) = Z[class set]^0 with U_p and diamonds; Lemma 5.5 (p. 85) is the diamond-twisted polarisation.
4. **ribet-stein_2001_lectures-on-serres-conjectures_preprint** (incl. Conrad's appendix) — S1 cited, S2 sketch, S4 partial.
   §2.3.1.1, pp. 28–29 [PDF 32–33]: X_1(N) as the μ_N-model, T_p by Picard functoriality; their T_p differs from Gross's
   (T_p)_* by a diamond; the Z/N model is mentioned as an alternative. §3.9, Fig. 3, (3.1), p. 45 [PDF 49]: reduction of the
   DR model of X_1(M,p) and the toric exact sequence (cited to DR and Raynaud). Lemma 3.17, p. 46 [PDF 50]: Frob_p acts as
   pT_p on the torus (no diamond factor written). (3.2), p. 48: Ribet's sequence, sketch. Conrad, Thm. 5.8, p. 69 [PDF 73]:
   adjoint of T_p is ⟨p⟩^{-1}T_p, of ⟨n⟩ is ⟨n⟩^{-1}, and the ( )_* / ( )^* actions are swapped by adjunction; Thm. 5.16,
   p. 74 [PDF 78]: Eichler–Shimura (T_p)_* = F + ⟨p⟩_* F^∨ at good reduction. No statement at the bad prime with nebentypus.
5. **ribet_1990_modular-representations-of-gal-qbar-q-arising-from-modular-forms** (image scan) — Gamma_0 only.
   Prop. 3.1, p. 439 (S2 at Gamma_0); Rem. 3.5(b), p. 441; Props. 3.7–3.8, pp. 445–446 (S4 at Gamma_0); §4, p. 456
   (Shimura curves of Eichler level M, Gamma_0-type). No Gamma_1 statement.
6. **ribet_1988_component-groups-and-the-shimura-subgroup-of-j0-n_scan** (Bordeaux 1987–88, Exp. 6; image scan) — Gamma_0.
   §3, pp. 6-06–6-07 [PDF 7–8]: monodromy pairing on Z^S with weights #Aut(E, C_M)/2, S the supersingular pairs at Gamma_0(M)
   (S3 at Gamma_0). X_1 appears only for the Shimura subgroup at good primes. No Gamma_1 S2/S3 statement.
7. **asterisque_1991_courbes-modulaires-et-courbes-de-shimura_vol** — no Gamma_1 statement.
   Raynaud pp. 9–25 (Thm. 5 p. 17, Cor. 6 p. 18: any semistable curve, so S3 follows once S1/S2 are known); Illusie
   pp. 27–44; Boutot–Carayol pp. 45–158 (Thm. 5.2 pp. 140–141, Čerednik–Drinfeld, arbitrary small level away from p);
   Edixhoven pp. 159–170 (Gamma_0(N)); Mazur–Ribet pp. 215–255 (Gamma_0). No DR/Deuring statement at Gamma_1.
8. **cornell-silverman-stevens-eds_1997_modular-forms-and-fermats-last-theorem_vol** — Gamma_0 only.
   Edixhoven's chapter, §3.2, (3.2.2)–(3.2.3), p. 225 [PDF 243]: X_0(N) at l is two copies of X_0(M) crossing at supersingular
   points; character group of the torus = degree-zero divisors supported at supersingular points (S1, S2 at Gamma_0).
9. **ribet-takahashi_1997_parametrizations-...** — Gamma_0 / Shimura X_0^D(M) only: Prop. 1, p. 11112 [PDF 3]. No statement found at Gamma_1.
10. **jordan-livne_1985_local-diophantine-properties-of-shimura-curves** — maximal order, no level (they say so, p. 238); Čerednik–
    Drinfeld Thms. 4.3–4.5, pp. 245–246. No statement found at Gamma_1.
11. **carayol_1986_sur-la-mauvaise-reduction-des-courbes-de-shimura** and **carayol_1986_sur-les-representations-l-adiques-...** —
    totally real F ≠ Q, Drinfeld level at p, arbitrary level H away from p; congruence relation (Compositio Prop. 10.3, p. 211).
    No character-group statement at Gamma_1 over Q. No statement found.
12. **mazur_1977_modular-curves-and-the-eisenstein-ideal** — Gamma_0(N) only (Appendix Thm. (A.1), p. 173; §3, p. 183).
13. **grothendieck_1972_sga-7-1-...\_scan** (now present, image scan) — general theory: Exp. IX Thm. 11.5, p. 455 [PDF 460]
    (component group = cokernel of the monodromy pairing, ℓ-part); applies at any level once the model is semistable.

## Summary
- S1 at Gamma_1(N) ∩ Gamma_0(q): **cited** (DR VI 6.9; Diamond–Im 8.3.1/8.4; Helm Thm. 10.3).
- S2 (Deuring at Gamma_1 with U_p, diamonds): **no statement found**. Closest: Helm Thm. 5.4 (Ribet's sequence at level Gamma_H).
- S3 at Gamma_1: no explicit statement; follows from S1 + S2 by Raynaud Thm. 5 / SGA7 IX 11.5 (inference, not a citation).
- S4 (Frobenius with nebentypus, μ_N vs naive): **no statement found**; anchors only at good reduction (Conrad 5.8, 5.16;
  Diamond–Im Rem. 10.2.1–2) or Gamma_0 (Ribet 3.7–3.8, Mazur A.1). Diamond–Im (8.4.1) shows ⟨p⟩ in the naive-model gluing.
- Naturality in s (X3): no statement found.
- Still missing from `literature/`: Buzzard 1997 (Duke 87), Takahashi 2001 (JNT 90), Bushnell–Henniart 2006, Hida 1986a is
  present (`hida_1986_galois-representations-into-gl2-zp-x-...`), MP99 is present (`moerdijk-pronk_1999_...`), Li 1975 is present.
