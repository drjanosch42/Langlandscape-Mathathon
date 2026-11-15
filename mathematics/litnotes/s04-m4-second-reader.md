<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S04-M8: independent second reading of the Hsieh dictionary (`mathematics/chapters/s04/hsieh.tex`, S04-M4)

verdict: FIX LIST (0 crit, 2 maj, 7 min). The core normalisations are right. Two R1 points are missing or cited too broadly: the
e vs e* bridge (item 1) and the scope of the Gorenstein/freeness citation (item 2). No item changes a formula in the chapter.

Reader: S04-M8 (opus, Fabian's node; M4 was written on Abhijit's account). Inputs: `hsieh.tex` at `6acc2ab`; the rest of
`chapters/s04/*.tex`; `s01/4-hecke.tex` (`def:s01-NUp`, `lem:s01-Up`, `rem:s01-diamond`), `s01/5-conventions.tex`
(`rem:s01-Upconv`, `lem:s01-Upconv`), `s01/6-targets.tex` (`thm:s01-lambdaJL`, corrected: classical <d> -> seed <d>^{-1});
`s03/4-ihara.tex` (homological S_l = l^{2-k}); litnotes `hsieh2017.md`, `lv2011.md`, `hida1988.md`; C3a
`impl/s04-ct:code/results/s04/H6_sign.json` (U_p^* = <p>_M U'_p, sign +1). I checked the PDFs with `pdftotext -layout` and one page
image (Hsieh p. 31). The literature folder of the worktree is empty, so I read the main checkout's `literature/` without changing it.
Hsieh's arXiv file numbers its PDF pages the same way as its printed pages, so the chapter's line-3 comment is correct.

## A. Normalisations confirmed independently (no action)

- **P_k vs P^ad_k** (`def:s04-Pk`, l.16-48). I re-derived the computation. ev(gP) = P(c,d) ≡ d^n ev(P) mod c, and f(x delta_d) =
  d^{-n} f(x) for d ≡ 1 mod p. So the adelic diamond acts on the weight-k piece by u^{-(k-2)}, and that piece is killed by
  P^ad_k = ker([u] -> u^{2-k}). With classical <u> = adelic <u>^{-1} (`rem:s01-diamond`, `thm:s01-lambdaJL` as corrected), the
  classical ideal is P_k = iota(P^ad_k). Hsieh cross-check: Hsieh p. 2 (§1.1) gives Q = x^k eps on Gamma, and Def. 4.1 (p. 31) gives
  f(xz) = f(x) z^2 [z]^{-1}. So the quaternionic (= seed adelic, see the next point) <z> specialises to z^{2-k}, i.e. the classical
  <z>^{-1}. The same holds for chi_I (p. 32: chi(z) <eps>^{-2} <eps>_I), and it agrees with the GL_2 side through JL(sigma_d) = sigma_d
  (p. 34). Consistent everywhere.
- **Hsieh's <z>_Lambda.** The page image of p. 31 shows x·diag(z,z) (central), not diag(z,1). The chapter's step
  diag(z,z) = delta_z · diag(z,1) with diag(z,1) ∈ K_s (bottom row (0,1)) is correct, so <z>_Lambda = the adelic <z> (l.23, l.46-47).
- **Remark `rem:s04-iota2`** (l.90-97). Correct. The printed iota_2(T) = (1+T)^{-2}(1+p)^2 - 1 (p. 31, after (4.6)) contradicts Def. 4.1
  on the same page. Since [z] -> z^2[z]^{-1} is an involution, Def. 4.1 forces the exponent -1 whichever direction iota_2 is read in,
  and only the exponent -1 gives Q∘iota_2 = z^{2-k}.
- **N_{U_p} vs Hsieh's U_p.** Homological: p. 31, sum_b x(p b; 0 1), equals `def:s01-NUp`. On forms: p. 30, sum_b rho_kappa(p b; 0 1)
  f(x(p b; 0 1)), which is the cohomological N_{U_p} on Brandt(V_k). The idele varpi_p is p at p and 1 elsewhere, which matches
  varpi_j = iota_p^{-1}(p j; 0 1). Proof step (iii), ev(varpi_j P) = P(0,1), is correct.
- **Specialisation pairing** (l.71-73). <X^i Y^{k-i}, X^j Y^{k-j}>_k is non-zero only for i + j = k (p. 29). Pairing with X^k
  therefore picks the coefficient of Y^k with factor 1, which is P(0,1) = ev(P). Correct.
- **#Gamma = w_x and the factor 2** (l.121-127). Hsieh (4.1), p. 29: #Gamma_{N,x} = #((D^x ∩ x R^_N^x x^{-1}) Q^x / Q^x). With
  Gamma_x ∩ Q^x = {±1} this is |Gamma_x|/2 = w_x (`def:s01-pairing`, w_x = |Gamma_x|/eps). The factor 2 is relative to |Gamma_x|
  (the `Nat.card` of the import), not relative to w_x. Correct.
- **Character at p** (Rem. `rem:s04-controlb`(v)). Hsieh's chi-piece has sigma_d = chi^{-1}(d) (p. 31). The specialisation has
  character chi·omega^{2-k} (Thm. 4.2(2), p. 32). Its p-part is trivial iff mu_{p-1} acts on the Mord-piece by omega^{-(k-2)}. This
  matches `def:s04-Pk`, proof (ii), last sentence. Correct.
- **Compatibility with S03 (S_l^hom = l^{2-k}).** No conflict, but this needs care: Mord ⊗ Lambda/P^ad_k is the O-dual of the forms
  space, so S_l acts on it as the transpose of the cohomological l^{k-2}<l>^{-1}. It is not the S03 homological V_k-module, on which
  S_l = l^{2-k}. See item 9.
- **Citations verified against the PDFs (all match):** Hsieh §4.1 p. 29 (U_1(N), (4.1), rho_kappa, <,>_kappa); §4.2 pp. 29-30
  (forms, U_p, "Inner products", tau^D_N); §4.4 p. 31 (Def. 4.1, (4.6), <z>_Lambda, sigma_d, homological U_q); Thm. 4.2(1)(2) and proof
  p. 32 (V^ord(N), eS^D = Hom_Lambda(V^ord, Lambda) ⊗_{iota_2} Lambda, [Hid88b, Thm. 9.4]); "A perfect pairing" and B_{N,alpha} p. 32;
  Def. 4.3 and Lemma 4.4 (sign (-1)^{k_Q}) p. 33; §4.5 and Thm. 4.5 with proof p. 34; Def. 4.12 p. 43; Rem. 7.3 p. 67; Rem. 7.8 p. 71;
  §1.4 Hypothesis (CR, Sigma) p. 4 (ℓ ≡ 1, not ±1). LV11 Thm. 3.7 and Prop. 3.6 p. 28. PW Prop. 6.4 p. 19, Prop. 6.5 p. 20. Wiles 1995
  Thm. 2.1 and Cor. 2 both on p. 482. Hida 1988b Thm. 9.4 p. 369 (OCR only). Exceptions: items 6 and 7.

## B. Fix list

1. **maj** — `hsieh.tex:115-127` (Translation after `def:s04-BN`); also l.11 and l.55-61. **Problem:** R1 lists "e vs e*". The
   section never says which ordinary projector Hsieh's forms carry. Hsieh's forms are acted on by t f(x) = f(tx) (p. 31, after (4.6)),
   with the cohomological U_p of p. 30. Through the evaluation pairing this is the transpose of our e on Mord; this direction is fine,
   and it is what (4.6) uses. Through the Brandt/norm identification nu (weights (#Gamma)^{-1}, as in B_{N,alpha}), however, the
   forms-side e becomes e* on Z_p[X] (`lem:s04-ekills`(d); U_p^* = <p>_M U'_p, `lem:s01-Up`(d); C3a H6 sign +1). The twist
   U_p^{-alpha}[tau^D_{Np^alpha}] in B_{N,alpha} is exactly what turns the (e, e*) duality into a pairing on eS^D × eS^D. A reader who
   transports B_N to Z_p[X_s] with the naive delta_{xy} pairing pairs e with e and gets a degenerate or wrong pairing. **Page refs:**
   Hsieh pp. 30-33. **Proposed fix:** add a clause (v) to the Translation: "Hsieh's eS^D is the e-part for the cohomological U_p. Under
   nu it is e*Z_p[X_alpha], not eZ_p[X_alpha] (Lemma `lem:s04-ekills`(d)). The Atkin-Lehner twist [tau^D_{Np^alpha}] together with
   U_p^{-alpha} intertwines U_p with U_p^* = <p>_M U'_p, which is why B_N pairs e with e." Add the same half-sentence to l.11 ("agree
   on U_p": as operators on homology and on forms, but the forms-side e is e* under nu).

2. **maj** — `hsieh.tex:143-148` (`thm:s04-Gor`, first sentence) and l.194-195 (`if:s04-Mord`). **Problem:** the theorem claims
   freeness of rank one and the Gorenstein property for every maximal ideal m of T^ord_B(Uone M) that satisfies (CR_D). Hsieh's
   statement and proof (p. 34) cover only the m that contains ker lambda^D_f for a primitive family f of tame conductor N = N^+N^-.
   That means N^+ = M is the exact tame conductor and supp N^- ⊂ Sigma^0_f, i.e. f is D-new. For other m (old at M, or of smaller
   conductor) the source does not apply as cited. Wiles Thm. 2.1 and Helm Cor. 8.11 may well extend to them, but the chapter does
   not check this. **Page refs:** Hsieh Thm. 4.5 and proof, p. 34; §4.5, p. 34 (definition of lambda^D_f). **Proposed fix:** either add
   the hypothesis "m = m_F for a primitive I-adic family F of tame conductor MD" (the only case used by `thm:s04-etaB` and stage 06),
   or keep general m and mark that extension \stexp{} with a pointer to [Wil95, Thm. 2.1], [Hel07, Cor. 8.11]. Make the same change in
   `if:s04-Mord` l.194-195 ("Under Hyp. CR ... T_m is Gorenstein").

3. **min** — `hsieh.tex:144-145` (and l.11 "agree on Lambda"). **Problem:** "Mord_m ⊗_Lambda I (equivalently Hsieh's eS^D(N,I)_m, its
   Lambda-dual)" leaves out the twist. By (4.6) and the proof of Thm. 4.2 (pp. 31-32), eS^D(N,Lambda) = Hom_Lambda(V^ord, Lambda)
   ⊗_{Lambda,iota_2} Lambda, so the Lambda-structure on forms is the iota_2-twist of the one on homology. "Agree on Lambda" holds on
   homology only. Freeness of rank one does not depend on this, but the I-structure, and hence the specialisations, does. **Proposed
   fix:** write "Hsieh's eS^D(N,I)_m is the Lambda-dual of Mord_m twisted by iota_2 (Remark `rem:s04-iota2`)". On l.11 write "agree on
   U_p and on the Lambda-action on homology; on forms Hsieh's Lambda-structure is the iota_2-twist".

4. **min** — `hsieh.tex:57-58` (Rem. `rem:s04-controlb`(i)). **Problem:** "his diamond sigma_d is right translation by a central idele,
   which is our <d> at p" is incomplete. The idele d~ also has components at q | M: there diag(d_2, d_2) = diag(1, d_2)·diag(d_2, 1)
   with diag(d_2, 1) ∈ U_1(M)_q, so sigma_d is our adelic <d~> with d~ = (omega(d_1), d_2). On V_k-valued forms sigma_d is
   omega(d)^{-n}<d~> (`lem:s01-Upconv`(c)), and the chapter does not point there. **Page refs:** Hsieh p. 31 (sigma_d).
   **Proposed fix:** "his sigma_d is our adelic <d~>, d~ = (omega(d_1), d_2) ∈ (Z/p)^x × (Z/M)^x, on O[X_alpha]; on weight-k forms it
   is omega(d)^{-(k-2)}<d~> (Lemma `lem:s01-Upconv`(c))". In (iv) also cite `lem:s01-Upconv`(c) for "Hsieh's forms-side U_p = N_{U_p}
   on Brandt(V_k)" (p. 30), so that the two dictionaries do not drift apart.

5. **min** — `hsieh.tex:11-12`. **Problem:** "differ ... on U_q for q | D (Hsieh's sign for U_q, q | D, is not imported)". Hsieh's
   quaternionic U_q, f -> f(x varpi_{D_q}) (p. 30) or x -> x varpi_{D_q} (p. 31), is our Pi_q with no sign. The -1 is in his JL map,
   JL(U_q) = (-1)U_q (§4.5, p. 34). **Proposed fix:** "agree on U_q = Pi_q (q | D); they differ in the JL matching, where Hsieh's
   JL(U_q) = -U_q is not imported (`thm:s01-lambdaJL`, `ex:s01-Pi11`)".

6. **min** — `hsieh.tex:139-141`. **Problem:** the text says that Hsieh p. 4 cites "[Wil95, Thm. 2.1 and Cor. 2, p. 482]". On p. 4 he
   cites only [Wil95, Cor. 2, p. 482] (with [MW86, Prop. 2, §9]). Thm. 2.1 is cited in the proof of Thm. 4.5 (p. 34). Both results are
   on Wiles p. 482 (verified). **Proposed fix:** "citing [MW86, §9, Prop. 2] and \lit{wiles...}{Cor. 2, p. 482}". Thm. 2.1 is already
   given at l.150.

7. **min** — `hsieh.tex:150-151` (`\lit{helm_2007...}{Cor. 8.11 and Rem. 8.12, p. 110}`). **Problem:** on this node `literature/` has
   only `helm_2004_..._arxiv.pdf`, where Cor. 8.11 and Rem. 8.12 are on p. 31 (verified; Cor. 8.11 continues on p. 32). The journal
   page 110 cannot be checked here. `bib/s04.bib` l.11 says the 2007 file "is now in literature/", while `references.bib` (Hel note)
   points to the 2004 preprint. **Proposed fix:** sync `helm_2007_...pdf` to all nodes, or cite
   `\lit{helm_2004_..._arxiv}{Cor. 8.11 and Rem. 8.12, p. 31}` with the journal page in parentheses as "(journal p. 110, unchecked on
   node F)".

8. **min** — `hsieh.tex:121, 126`. **Problem:** notation. In l.121 the order in the formula should be R^_{Np^alpha}, not R^. In l.126
   "level \Uzero{Np^alpha}" mixes Hsieh's N = MD with our level notation. The level is our \Uzero{Mp^alpha} (maximal at D), i.e.
   Hsieh's Eichler order R_{Np^alpha} of level N^+p^alpha (p. 32, X_0(Np^alpha)). It is also worth recording that w_x ∈ {1,2,3} at
   this level, so (#Gamma)^{-1} is p-integral for p > 3. **Proposed fix:** make the three edits.

9. **min** — `hsieh.tex:62-69` (Rem. `rem:s04-controlb`(ii)-(iii)), interaction with S03. **Problem:** the remark identifies
   Mord ⊗ Lambda/P^ad_k with the O-dual of eS^D_k. It does not warn that this dual is *not* the S03 homological module Z_p[X] ⊗ V_k
   (on which S_l^hom = l^{2-k}, `s03/4-ihara.tex` l.94, l.266). On the dual of forms, S_l acts as the transpose of
   l^{k-2}<l>^{-1}, i.e. with eigenvalue l^{k-2} on the trivial-nebentypus piece. Stages 05 and 06 compare Mord with the S03 Ribet
   sequence, so the two "homological weight-k" objects must not be conflated. They differ by V_k vs V_k^vee ≅ V_k ⊗ det^{-(k-2)}.
   **Proposed fix:** add one sentence after (iii): "Mord ⊗ Lambda/P^ad_k is Hom_O(eBrandt(V_k), O). It is not the S03 homological
   Z_p[X] ⊗ V_k (S_l = l^{2-k} there, l^{k-2} here); the two differ by V_k vs V_k^vee."
