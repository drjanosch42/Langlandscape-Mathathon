<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# lit-b4: literature gaps (work batch 4, package C5)

Node: Abhijit. BASE `864d104`. Date of retrieval: 2026-11-14 (Caltech network). All paraphrases are our own; status of every
citation is *cited*. PDFs live in `literature/` (git-ignored, never committed); filenames follow the convention
`author_year_short-title[_scan|_arxiv|_preprint|_vol].pdf`.

Page convention. "p." is the printed page of the source; "[PDF n]" is the page of the file. For SGA 7 I: printed = PDF - 5
(Exp. IX = LNM 288 pp. 313-523; PDF 318 = title page of Exp. IX). The Exposé also carries its own running number "- k -"
at the top of each page, with printed page = 318 + k.

## 0. Summary table

| # | item | status | file / source | note |
|---|---|---|---|---|
| 1a | Ihara 1975 (Bombay 1973) | **obtained** | `ihara_1975_on-modular-curves-over-finite-fields_vol.pdf` (whole volume, TIFR SM 7) | official TIFR posting; pages differ from the OUP print, see 1.1 |
| 1b | SGA 7 I, Exp. IX | present; pages located | `grothendieck_1972_sga-7-1-...-i_scan.pdf` | see 1.2 |
| 2.1 | Gelbart 1975 (Ann. Math. Stud. 83) | manual download needed | -- | book, Princeton UP |
| 2.2 | Eichler 1973 (LNM 320, 75-152) | manual download needed | Springer chapter DOI 10.1007/978-3-540-38509-7_4 | site gives a bot challenge to curl; Caltech library by browser |
| 2.3 | Pizer 1976 (JMSJ 28) | **obtained** | `pizer_1976_on-the-arithmetic-of-quaternion-algebras-ii.pdf` (J-STAGE, published pagination) | see 2.3 |
| 2.4 | Kneser 1966 (PSPM 9, 187-196) | manual download needed | AMS, DOI 10.1090/pspum/009/0213361 | AMS bot challenge; see 2.4 |
| 2.5 | Swan 1980 (Dekker) | not obtainable here | -- | print only; library/ILL |
| 2.6 | Li 1975 | already present (verified) | `li_1975_newforms-and-functional-equations.pdf` | see 2.6 |
| 2.7 | Emerton 2002 (JAMS 15) | **obtained as author preprint** | `emerton_2002_supersingular-...-modular-forms_preprint.pdf` (44 pp., Emerton's Chicago page) | preprint pagination, not JAMS; JAMS version manual |
| 2.8 | Takahashi 2001 (JNT 90) | manual download needed | DOI 10.1006/jnth.2000.2614 (ScienceDirect) | bot challenge |
| 2.9 | Buzzard 1997 (Duke 87) | **obtained as author preprint** | `buzzard_1996_integral-models-of-certain-shimura-curves_preprint.pdf` (21 pp.; v. 13/5/1996, typos fixed 14/6/2002) | Duke version manual (Project Euclid challenge), DOI 10.1215/S0012-7094-97-08719-6 |
| 2.10 | Brzezinski 1990 (Crelle 403) | **obtained** | `brzezinski_1990_on-automorphisms-of-quaternion-orders_scan.pdf` (GDZ, image scan, 22 pp.) | see 2.10 |
| 2.11 | Kurihara 1979 | manual download needed | U-Tokyo repository (JAIRO Cloud) | repository was in maintenance (HTTP 503) at retrieval time |
| 2.12 | Moerdijk-Pronk 1999 | already present (verified) | `moerdijk-pronk_1999_simplicial-cohomology-of-orbifolds.pdf` | see 2.12 |
| 2.13 | Ribet 1988 (Bordeaux Exp. 6) | already present | `ribet_1988_component-groups-...-scan.pdf` | image-only; identical to the copy on Ribet's homepage |
| 2.14 | Bushnell-Henniart 2006 §56 | manual download needed | Springer; chapter 13 "The Jacquet-Langlands Correspondence", pp. 325-337, DOI 10.1007/3-540-31511-x_13 | §56 not verified (book not available) |
| 2.15 | OCR copies Shimizu 1965, Pizer 1980, Hida 1988 | partly | see 2.15 | no OCR engine on this node |
| 2.16 | Longo-Vigni bibliographic data | **resolved** | Crossref | two different papers, see 2.16 |
| 2.17 | HPS 1989 (Mem. AMS 82, no. 418) | manual download needed | AMS Memoirs | deferred on our side; only if Caltech has it |

Counts. New PDFs saved: 5 (Ihara 1975 volume, Pizer 1976, Brzezinski 1990, Emerton 2002 preprint, Buzzard 1996 preprint). Already
present and verified: 4 (SGA 7 I, Li, Moerdijk-Pronk, Ribet 1988). Manual download needed: 8 (Gelbart, Eichler 1973, Kneser 1966,
Takahashi, Kurihara 1979, Bushnell-Henniart, HPS 1989, plus the published versions of Emerton and Buzzard). Not obtainable: 1 (Swan).

## 1. Item 1: stage-3 M6 gaps

### 1.1 Ihara 1975

Bibliographic data (verified in the PDF). Y. Ihara, "On modular curves over finite fields", in: *Discrete Subgroups of Lie Groups and
Applications to Moduli*, Papers presented at the Bombay Colloquium 1973 (Tata Institute Studies in Mathematics 7), Oxford University
Press, Bombay, 1975. File: the full volume SM_07.pdf from `mathweb.tifr.res.in/Documents/Publications/Studies/` (the Tata Institute's own
posting, 379 PDF pages, 2.7 MB; title page and contents checked). The TIFR re-typeset reprint has Ihara's paper on **pp. 171-215**
(PDF 178-222); the margin of the reprint carries the page breaks of the original print, which are **pp. 161-202**, the pagination quoted
in Ribet 1984 ref. [6] and in our batch message. Both are consistent: the reprint page = original page + 10 at the start (171 = 161),
the offset grows because the reprint is typeset more loosely. Below: "TIFR p." is the reprint page, "orig. p." the original page
(from the margin marks; the mark sits at the line where that page begins, so orig. pages are accurate to a few lines).

What Ihara 1975 contains, and what it is not. It is *not* a paper stating a cohomological "Ihara lemma". Its Main Theorem (TIFR p. 171,
orig. 161) says that there is no non-trivial unramified extension of K_n in which all supersingular prime divisors split completely
(K_n the field of modular functions of level n over F_{p^2}, prime to p). The input from characteristic 0 is a purely group-theoretic
statement, and this is what the later literature calls Ihara's lemma:
- **Lemma 3.2** (TIFR p. 187, orig. 176): for n prime to p the system of compact Riemann surfaces R_n <- R_n^0 -> R'_n (levels Delta_n,
  Delta'_n = diag(p,1)^{-1} Delta_n diag(p,1), Delta_n^0 = Delta_n ∩ Delta'_n) is simply connected (has no unramified covering of degree > 1 in
  the sense of Def. in 3.1, TIFR p. 186).
- The proof (§3.3, TIFR pp. 188-189, orig. 177-178) uses two properties of Gamma_n = principal congruence subgroup of level n in
  PSL_2(Z[1/p]): **(A)** Gamma_n is the free product of Delta_n and Delta'_n amalgamated along Delta_n^0 (from Ihara's earlier work [8], I, Ch. 2,
  §28, p. 111, and Serre's Trees); **(B)** Gamma_n is normally generated by (1 n; 0 1), hence generated by parabolic elements
  (Mennicke, Serre: the congruence subgroup property). The parabolic elements of Gamma lie in the subgroup generated by the covering
  data because gamma^{p^k} is integral and parabolic (TIFR p. 189, (3.3.6)).
- General picture (§3.5, TIFR p. 190, orig. 179): subgroups of finite index of Gamma_1 = PSL_2(Z[1/p]) correspond to pairs of finite-index
  subgroups of Delta_1, Delta'_1 satisfying a matching condition; Gamma_1 is the amalgam Delta_1 *_{Delta_1^0} Delta'_1 with Delta_1^0 Gamma = Gamma_1.

Where the classical "Ihara lemma for GL_2" (our `Conj. s03-iharaGL2`, `5-amalgam.tex` l. 197, stage tex l. 390) comes from. The statement
used by Ribet is **Ribet 1984** (ICM Warszawa; present, scan `ribet_1984_...scan.pdf`, PDF = printed - 502): §4, p. 510, says the
analysis of the group Sigma (the kernel of J_0(N)^2 -> J_0(NM)) is based on Ihara's article [6] (footnote: thanks to Serre);
**Thm 4.1** (p. 511): the kernel of gamma (the degeneracy map J_1(N)^2 -> J_1'(N)) is trivial; **Cor. 4.2** (p. 511): the kernel of beta is trivial and
Sigma is a subgroup of S x S; **Thm 4.3** (p. 511): Sigma = {(x,y) in S x S : x + y = 0}, S the Shimura subgroup. The proof (pp. 512-513) reduces the
statement to the surjectivity of H_1(A,Z) -> H_1(G_1)/Pb(G_1) + H_1(G_2)/Pb(G_2) (4.4), writes Gamma = G_1 *_A G_2 (Serre, Trees II §1.4), uses the exact
sequence of Lyndon, and concludes from "Gamma is generated by parabolic elements"; for parabolics it quotes "page 178 of [6]", which is exactly
Ihara orig. p. 178 (§3.3, (3.3.6)). Ref. [6] on p. 513 reads "pp. 161-202". So: **the original Ihara lemma = Ihara 1975, §3.2 properties (A),(B) and
Lemma 3.2 with proof §3.3 (TIFR pp. 187-189), in Ribet's cohomological form Ribet 1984 Thm 4.1/4.3 (p. 511, proof pp. 512-513).**
For `Conj. s03-iharaGL2` (torsion of coker Psi in H^1(Gamma,V) for the amalgam Gamma = Gamma_0 *_{Gamma_0 ∩ Gamma_0'} Gamma_0') this
means: Ihara's Lemma 3.2 handles weight 2 / trivial coefficients through (A)+(B); weight k > 2 with Sym^{k-2} coefficients is *not* in Ihara 1975 or
Ribet 1984 (both treat H_1(.,Z), i.e. J(N)). The statement `s03-iharaGL2` itself is therefore genuinely a conjecture
beyond these sources, as the chapter already says.
Also: Serre's CSP for SL_2(Z[1/p]) (`serre_1970_*`) is the source of property (B) (Ihara p. 187 credits Mennicke and Serre).

### 1.2 SGA 7 I, Exposé IX (Grothendieck, "Modèles de Néron et monodromie")

File `grothendieck_1972_sga-7-1-...-scan.pdf`, 528 PDF pages, image-only (no text layer); all pages below were rendered
(`pdftoppm -r 75-100`) and read as images, and the key pages were re-opened a second time (see Self-audit). LNM 288, Springer 1972,
Exp. IX = pp. 313-523 (verified: the title page is printed p. 313 = PDF 318). Table of contents of Exp. IX on PDF 318-319.

Sections: 0 introduction; 1 Néron model of abelian schemes, canonical pairing Phi_0 x Phi'_0 -> Q/Z and biextension; 2 fixed and toric part of
T_l, orthogonality theorem for l != p; 3 semi-stable reduction; 5 orthogonality for l = p; 7-8 Raynaud extension; **9 definition of the monodromy
pairing**; **10 properties of the monodromy pairing, integrality and positivity theorem**; **11 connected components of the Néron model: duality,
asymptotics**; **12 Néron model of a Jacobian and the Picard-Lefschetz formula**; 13-14 transcendental links.

**(a) Orthogonality theorem 2.4** (printed p. 338 [PDF 343], Exp. p. 20; proof pp. 338-340 [PDF 343-345]). Paraphrase: for S henselian, A_K an abelian scheme
over K with dual A'_K, l a prime different from the residue characteristic, the canonical filtration of the Tate modules T_l(A(K-bar)),
T_l(A'(K-bar)) by torus part inside fixed part (= inertia invariants, (2.3.4)-(2.3.5), p. 337) satisfies: the torus part of T_l(A) is the
intersection of the fixed part of T_l(A) with the orthogonal of the fixed part of T_l(A') for the canonical pairing (1.0.3), and symmetrically.
The proof (a) uses the canonical biextension W^0 of 1.4.4 and VIII 4.10; (b) uses the non-degeneracy of W_0 (Raynaud, 1.5). The conditions U, V, W of
(2.5.2)-(2.5.5) (p. 341 [PDF 346]) give the dimension count 2 lambda, 2 alpha, mu used in stage-05 (G4). Rem. 2.6 a (p. 341) says 2.4 is an easy consequence of the biextension theory developed in the preceding sections, and that the inclusion (2.4.6) can also be
proved without biextensions by an arithmetic argument (the sentence is cut off at the page break; the continuation was not read).

**(b) The dictionary X(G): character groups of the toric parts.** (5.5.1)-(5.5.3) (p. 378 [PDF 383], Exp. p. 60): M'_0 = D(T_0), M_0 = D(T'_0), the Cartier
duals of the maximal tori of the special fibres of A and A', viewed as twisted constant groups M', M over S; M' = Hom_{k-gr}(T_0, G_m) when T_0
is split. (5.5.7)-(5.5.9) (p. 379 [PDF 384]): T_l(A^0)^t = T_l(T-hat) = M'-check (x) Z_l(1) and T_l(A'^0)^t = M-check (x) Z_l(1); and in the semistable case
T_l(A_K)/T_l(A_K)^f = M (x) Z_l, T_l(A'_K)/T_l(A'_K)^f = M' (x) Z_l; Prop. 5.6 (p. 380) records the same filtration. This is the exact content of
stage-05 (G4): T_t = Hom(X(A), Z_l(1)) with X(A) = M', and T_l A / (T_l A)^I = X(A^vee) (x) Z_l = M (x) Z_l.
The **graph dictionary** for Jacobians is in §12: (12.3.7) (p. 472 [PDF 477], Exp. p. 154): for the curve C with normalisation C-tilde, the character group
M = D(T) of the maximal torus of Pic^0_{C/k} is canonically H_1(Gamma(C), Z) and the dual M-check = R is H^1(Gamma(C), Z), where Gamma(C) is the (unoriented) graph whose
vertices are the irreducible components of C-tilde and whose edges are the pairs of distinct branches through a common point; (12.3.10)-(12.3.11) (pp. 472-473) give M as the kernel of Z^I -> Z^J and as
H_1 = ker(d: Z^{Gamma_1} -> Z^{Gamma_0}) with d(x,C',C'') = g(C'') - g(C'). §12.4 (p. 473 [PDF 478]): in the semistable situation M = Ker(Z^I -> Z^J), I = the set of singular points
of X_0, J = the set of its irreducible components, (12.4.1)-(12.4.2).

**(c) The monodromy pairing.** Definition **9.1.2** (printed p. 418 [PDF 423], Exp. p. 100, start of §9): for l any prime, a canonical pairing
u_l : M_l (x) M'_l -> Z_l, defined through the Barsotti-Tate pro-l-groups T_l(A^0), T_l(A'^0) and the generic fibre T_l(A_K) (for l = p one needs Tate's theorem); for l != p it is
described by the Galois module U = T_l(A_K(K-bar)) (9.1.3). §9.2 (p. 419-421 [PDF 424-426]) gives the case l != p: the inertia action g x = x + u(g) x on U (9.2.2) (a transvection
parallel to W = V^perp, (9.2.1)-(9.2.4)), factoring through the tame quotient I -> Z_l(1) (9.2.4)-(9.2.6) and giving u in Hom(M (x) M', Z_l) (9.2.9) (p. 421 [PDF 426]).
General definition: §9.6 (p. 436 [PDF 441]); (9.7.1) (p. 438) shows the pairing is independent of l and rational-valued. Symmetry and base-change are in §10 (10.2.2) (p. 440), (10.3.5) u^{K'} = e(S'/S) u^K (p. 443 [PDF 448]).
**Theorem 10.4** (integrality and positivity) (printed p. 444 [PDF 449], Exp. p. 126): for A_K semistable over a henselian S, (a) there is a unique pairing
u : M (x) M' -> Z_S whose l-adic realisations are the u_l; it is separating; (b) for a polarisation xi giving xi_t : M -> M', the form phi^t_xi(x,y) = u(x, xi_t(y)) on M (x) M is symmetric, positive and non-degenerate. Proof: reduced (10.5, pp. 445-448) to Jacobians and then
done transcendentally via Theorem 12.5 (see §12.6, p. 476: 12.5 proves 10.4 for the canonical polarisation). Grothendieck remarks (p. 443) that 10.4 is not used in the rest of SGA 7.
**Theorem 12.5 (Picard-Lefschetz)** (printed p. 475 [PDF 480], Exp. p. 157): for S strictly local, X regular, projective, flat of relative dimension 1 with smooth connected geometric generic fibre and
special fibre whose only singular points are ordinary quadratic points, u_l (12.4.7) equals the pairing (12.4.5) u = sum_i phi_{x_i} (x) phi_{x_i} on M (x) M-check, after extension of scalars to Z_l (p. 474 [PDF 479]: (12.4.5), positive definite
because M embeds in Z^I with the standard quadratic form). **Caveat for the weighted graph `Phicomb(G)` with thicknesses w_e:** 12.4-12.5 treat only regular models, i.e. **all weights w_e = 1**.
A weight w_e arises when the model is not regular (local equation xy = pi^{w_e}), and SGA 7 IX reaches it only through the base-change rule (10.3.5) (scaling by the ramification index e(S'/S)) and 10.4/11.5 for the
abstract pairing; I did not find the explicit statement "pairing = diag(w_e)" in Exp. IX. The weighted form is Ribet 1990 pp. 437-438 and Raynaud, as in `rem:s03-grothendieck`.

**(d) Component group.** §11.4 (printed p. 454 [PDF 459], Exp. p. 136): in the semistable case perfect pairings Phi_0(l) x Phi'_0(l) -> Q/Z without restriction on l (11.4.1) (resolves Conjecture 1.3, p. 323, in the semistable case;
the earlier remark p. 323 [PDF 328] credits Artin-Mazur for Jacobians). **Theorem 11.5** (printed p. 455 [PDF 460], Exp. p. 137): S henselian, A_K semistable, l prime, u-tilde_l : M_l -> M-check'_l the map induced by u_l (9.1.2),
Phi(l) := coker(u-tilde_l); then there is a canonical isomorphism Phi_0(l) = Phi(l) x_S s (11.5.1), where Phi_0 = A_0/A_0^0 is the component group of the special fibre of the Néron model.
**Remarks 11.5.2** (same page): (a) u-tilde_l is an isogeny, i.e. u_l separating, even for l = p; (b) using 10.4, with u : M (x) M' -> Z_S and Phi := coker(u-tilde : M -> M-check'), one gets
the integral statement Phi_0 = Phi x_S s ((11.5.3), p. 456 [PDF 461]), uniform in l; applying 11.5 to A' gives Phi'_0(l) = coker(^t u-tilde). In words: the component group is the cokernel of the monodromy pairing M -> Hom(M', Z).
(Independent confirmation: Emerton 2002 preprint, p. 23, Lemma 3.16 remark, quotes "[9, 11.5.2b]" for "coker(X^0 -> Hom(X^0,Z)) = component group of J_0(p) at p".) The definition of ũ in terms of Barsotti-Tate groups: §11.6.1-11.6.2 (p. 456).

**(e) Stage-05 uses.** G3: "monodromy pairing on X_q(J) is w_e delta_ee', Phi_q(J) = X_q(J)^vee/X_q(J), [SGA7 IX 11.5]": supported by Thm 11.5 + Rem. 11.5.2 b (p. 455-456) for Phi = coker of the
pairing, and by 12.4.5/12.5 (p. 474-475) for the diagonal form with weights 1; weights w_e: see the caveat in (c). G4: "[SGA7 IX 2.4, 9.1--10.4]": Thm 2.4 (p. 338), M, M' (5.5.1-5.5.9, pp. 378-379), pairing 9.1.2 (p. 418), Thm 10.4 (p. 444). All correct as numbered.
**9.1.2 versus Illusie Thm 2.7.** Illusie's Theorem 2.7 (in the volume `asterisque_1991_courbes-modulaires-et-courbes-de-shimura_vol.pdf`, printed p. 41 [volume PDF 46], re-checked on the page image and in the text layer):
"With the notation (2.1.3), (2.6.6) one has phi = u (x) Lambda"; the sentence below says: "this is, with the opposite sign, the l-part of Grothendieck's result (SGA 7 IX 9.1.2)". The proof-line above it shows the source of the sign:
Illusie's maps satisfy gamma = -c (2.5.2) and gamma' = -c' (2.4), which are what makes the commutativity of (2.2.3) and (2.6.5) give phi = u rather than -u, where u_l is the pairing of SGA 7 IX (cited by him as "9.1.2" in 2.7, and as "IX 2.5.3" for the notation u_l on the line before; 2.5.3 on p. 341 of Exp. IX is the definition U, V, W of the Tate module and its filtration).
The page matches stage 05 `thm:s05-G` (G4) and `rem:s05-illusie`.

## 2. Item 2: remaining gaps of `MISSING_LITERATURE.md`

Metadata was verified through Crossref where a DOI exists (query on title + journal), and in the PDFs where we have them.

### 2.1 Gelbart 1975. Manual. *Automorphic Forms on Adele Groups*, Ann. of Math. Stud. 83, Princeton UP 1975 (monograph; not freely available). Only §3 pagination from our list; not verified. Caltech library / Princeton UP.

### 2.2 Eichler 1973. Manual. "The basis problem for modular forms and the traces of the Hecke operators", in *Modular Functions of One Variable I*, LNM 320, Springer 1973, **pp. 75-152** (Crossref: DOI 10.1007/978-3-540-38509-7_4, pages 75-152, confirms our page range). URL: https://link.springer.com/chapter/10.1007/978-3-540-38509-7_4 (the PDF URL answers with a client challenge for curl; a browser on the Caltech network should work).

### 2.3 Pizer 1976, obtained
A. Pizer, "On the arithmetic of quaternion algebras II", J. Math. Soc. Japan 28 (1976), no. 4, 676-688 (received Sept. 30, 1975); DOI 10.2969/jmsj/02840676. File from J-STAGE (open access, published pagination, 13 PDF pages, PDF n = printed - 675); the Project Euclid copy answered with a bot challenge. Contents: §2 orders, §3 optimal embeddings (Props. 3-5, 10-12, 16-20, pp. 677-684), §6 orders of level q_1 q_2 and the mass formula, §7 Brandt matrices.
- **Def. 22** (p. 684): an order of level q_1 q_2 (q_1 = prod p_i^{s_i}, s_i odd, algebra ramified exactly at p_i and infinity; local level p_i^{s_i} at p_i, split of level at primes of q_2).
- **Def. 23, Prop. 24** (p. 685): the mass M_{q_1 q_2} is a weighted class number (sum over the left ideal classes of reciprocals of the unit-group orders, the displayed formula is garbled in the OCR), equal to 2 Vol(G/Gamma) for Haar measure with vol U(O) = 1 (G = adelic units of volume one).
- **Prop. 25** (p. 685, evaluated p. 686): the mass formula M = (q_1 q_2/12) prod_{p | q_1}(1 - 1/p) prod_{p | q_2}(1 + 1/p) (the OCR garbles the displayed formula; the form is confirmed by the proof at the top of p. 686 which uses the maximal-order mass (1/12) prod (p-1), the index [U(O'):U(O)] formula (11), and Prop. 24). For maximal orders / Eichler orders this is the classical Eichler mass formula.
- **Theorem 26** (p. 686): trace formula for the Brandt matrix B_{k-2}(n; q_1, q_2) in terms of class numbers of orders of discriminant s^2 - 4n and optimal embedding counts.
This covers the "mass / class-number formulas for Eichler orders" use in stage 01 (Eichler orders appear as the case q_1 q_2 squarefree, Remark after Def. 22, p. 684).

### 2.4 Kneser 1966. Manual. M. Kneser, "Strong approximation", in *Algebraic Groups and Discontinuous Subgroups* (Boulder 1965), Proc. Sympos. Pure Math. 9, AMS 1966, **pp. 187-196**; Crossref: DOI 10.1090/pspum/009/0213361, pages 187-196, year 1966 (confirms the "from memory" pages; a citation of Platonov gives 187-197, so 196 vs 197 should be looked at in the print). URL https://doi.org/10.1090/pspum/009/0213361 (AMS answers curl with a bot check). A full-volume PDF exists on a third-party personal page (panchish, ujf-grenoble); not downloaded: not a publisher or author site.

### 2.5 Swan 1980. Not obtainable. R. G. Swan, "Strong approximation and locally free modules", in *Ring Theory and Algebra III* (Norman 1979), Lecture Notes in Pure and Appl. Math. 55, Dekker 1980, pp. 153-223 (from memory, **not verified**; no Crossref record, no open copy found). Library / interlibrary loan.

### 2.6 Li 1975, already present, verified
W.-C. W. Li, "Newforms and functional equations", Math. Ann. 212 (1975), 285-315 (file `li_1975_...pdf`, 31 PDF pages, PDF n = printed - 284; Crossref DOI 10.1007/BF01344466 agrees). **Theorem 3** (p. 295): for a normalized newform F in the new space of level (M,N) (Li's notation S_k(M,N)), p a prime with (p,MN) = 1, q a prime dividing MN: (i) F | T_p = a(p) F, F | (U_q-type operator) = a(q) F with the Hecke recursion and Euler product; (ii) |a(q)| = q^{(k-1)/2} if the character epsilon is not a character mod MN/q; (iii) if epsilon is a character mod MN/q then a(q) = 0 when q^2 | MN, and **a(q)^2 = epsilon(q) q^{k-2} when q^2 does not divide MN**. The proof of (iii) is Case I (ii), p. 295, via Lemma 3 (p. 289) and Lemma 2. This is exactly the used statement for q exactly dividing N (stage 05 Prop. sign (c)): "q^2 does not divide MN, epsilon a character mod MN/q"; note the hypothesis "epsilon is a character mod MN/q" (i.e. epsilon unramified at q), which stage 05 must check at q || N.

### 2.7 Emerton 2002, obtained as preprint
M. Emerton, "Supersingular elliptic curves, theta series and weight two modular forms", J. Amer. Math. Soc. 15 (2002), no. 3, 671-714; DOI 10.1090/S0894-0347-02-00390-9 (Crossref). File: Emerton's own page (https://math.uchicago.edu/~emerton/pdffiles/two.pdf), 44 pp., a preprint; its page numbers are **not** the JAMS ones, so the references below are "preprint p.". The AMS page answers with a bot challenge, so the JAMS pagination needs a manual download.
- **Def. 3.4, Lemma 3.3** (preprint pp. 18-19): X = Z[S], S = supersingular points of X_0(p); pairing <x_i,x_j> = e_i delta_ij, e_i = half the number of automorphisms of E_i; restricted to X^0 = ker(deg) it is the Picard-Lefschetz pairing of Ribet 1990 §§2-3; the product of the e_i is the denominator Delta of (p-1)/12.
- **Theorem 3.1** (p. 18): X (resp. X^0) is a faithful module over the Hecke algebra T (resp. T^0); proof identifies X^0 with the character lattice of the toric part of the Néron model of J_0(p) at p (by SGA 7 IX; Ribet).
- **Cor. 3.9, Lemma 3.16 and its remark** (pp. 20, 23): the pairing is T-bilinear; the cokernel of X^0 -> Hom(X^0, Z) is the component group of J_0(p) at p (cyclic of order n = numerator of (p-1)/12), through SGA 7 IX 11.5.2 b and Mazur's Eisenstein ideal paper.
- **Thms 0.3-0.6, 1.10, 1.14, 4.2** (pp. 3-5, 11, 14, 25): X is generated by theta series; X is T-free of rank one iff T_m is Gorenstein; the Gorenstein criterion.
Emerton does not compute a "component group" on its own; what he gives is the Gross lattice X with its pairing and the component group as its discriminant module (Lemma 3.16). So it is a cross-check for T1 only through Lemma 3.16 / Def. 3.4.

### 2.8 Takahashi 2001. Manual. S. Takahashi, "Degrees of parametrizations of elliptic curves by Shimura curves", J. Number Theory 90 (2001), no. 1, 74-88; DOI 10.1006/jnth.2000.2614 (Crossref). ScienceDirect (bot challenge; JNT is, as far as we know, in Elsevier's open archive for this age, so a plain browser download should work). Pages 74-88 verified by Crossref.

### 2.9 Buzzard 1997, preprint obtained
K. Buzzard, "Integral models of certain Shimura curves", Duke Math. J. 87 (1997), no. 3, 591-612; DOI 10.1215/S0012-7094-97-08719-6 (Crossref). File: author preprint "original version 13/5/1996, typos fixed 14/6/2002" from Buzzard's Imperial page, 21 PDF pages (so, again, "preprint p. n" below, not Duke pages). The Duke version at Project Euclid answers with a bot challenge.
- **Thm 2.1** (preprint p. 5): the moduli stack X^D(U) of false elliptic curves (A, i) with level structure is an algebraic stack over Z[1/(M_U d)], proper and smooth of relative dimension 1 (from [B] §14).
- **Thm 4.5** (p. 12): lifting of false elliptic curves = lifting of O_D-actions on l-divisible groups (Serre-Tate), for l not dividing d.
- **Thm 4.7** (p. 13), for a prime l not dividing d: X^D(U, Gamma_0(l)) is proper, regular, finite flat over X^D(U), smooth away from the supersingular points in characteristic l; its fibre at l consists of two components, each isomorphic to X^D(U)_{F_l}, **crossing transversally at the supersingular points** (the Deligne-Rapoport picture, (v)).
- **Thm 4.10** (p. 17): the same for the *balanced canonical Gamma_1(l)* structure, with special fibre two copies of the Igusa curve X^D(U, Ig(l)) crossing transversally at supersingular points; regular, proper, over Z[1/(M_U d)][zeta_l].
- §5 (pp. 19-21): the Hodge bundle and Igusa structures (Prop. 5.1, Thm 5.2).
Scope: only primes l not dividing the discriminant d. This is the Shimura-curve analogue of the DR statements (X1)-(X3) at Gamma_0(l) and at a Gamma_1(l)-type level, including diamond-like data through the balanced structure. It does *not* treat the primes dividing d, where Cerednik-Drinfeld is needed.

### 2.10 Brzezinski 1990, obtained
J. Brzezinski, "On automorphisms of quaternion orders", J. reine angew. Math. 403 (1990), 166-186 (file from the Göttingen digitisation centre, GDZ, image scan, PDF n = printed - 164; Crossref DOI 10.1515/crll.1990.403.166). All pages below are read from the page images.
- **Thm 4.2** (p. 183): Eichler's formula: the sum over the genus of H(Lambda_i) e(S, Lambda_i) = h(S) e_{U(Lambda)}(S, Lambda), for S a maximal commutative suborder.
- **Thm 4.3** (p. 184): class number H_Lambda = M_Lambda + sum over S of (1/|S^*|) h(S) e_{U(Lambda)}(S, Lambda), with M_Lambda = sum H(Lambda_i)/[Lambda_i^*:R^*].
- **Thm 4.5** (p. 185): for a Z-order Lambda in a definite quaternion Q-algebra, H_Lambda = M_Lambda + (1/4) a_2 prod_{p | d(Lambda), p+2}(1 + e_p(Lambda)(-1/p))|e_p| + (1/3) a_3 prod(1 + e_p(Lambda)(-3/p))|e_p|, with (4.6) the mass M_Lambda = (d(Lambda)/12) prod_{p | d(Lambda)} (1 - p^{-2})/(1 - e_p(Lambda) p^{-1}) and a_2, a_3 given by (4.7), (4.8) (p. 185). This is the "(4.6)" used in Voight's Main Thm 25.3.19.
- §1-§3 (pp. 167-182): Bass orders, hereditary closure H(Lambda), local automorphism groups, counting of optimal embeddings e(S,Lambda) (Thm 3.10, p. 182 region).

### 2.11 Kurihara 1979. Manual. A. Kurihara, "On some examples of equations defining Shimura curves and the Mumford uniformization", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 25 (1979), no. 3, 277-300 (pages and issue confirmed by a citing reference list, not by the journal; no DOI). The University of Tokyo repository (https://repository.dl.itc.u-tokyo.ac.jp/) returned HTTP 503 "maintenance of JAIRO Cloud since 2026-10-28" at retrieval time (2026-11-14); retry later or use the Caltech library.

### 2.12 Moerdijk-Pronk 1999, already present, verified
I. Moerdijk, D. A. Pronk, "Simplicial cohomology of orbifolds", Indag. Math. (N.S.) 10 (1999), no. 2, 269-293 (file, 25 PDF pages, PDF n = printed - 268; Crossref DOI 10.1016/S0019-3577(99)80021-4; the 1997 K-Theory paper is also present). Contents: **Theorem** (p. 270): for an orbifold M with atlas, there is a simplicial set S(M) (built from a triangulation of the coarse space and the local isotropy groups, §2, pp. 276-280) such that for any local system A on M, H^*(M, A) = H^*(S(M), A) naturally; **Thm 2.1.1** (p. 278); the teardrop example (§3, Thm 3.4.1, p. 285); §4 **Thm 4.1.1** (p. 285): every orbifold is represented by a proper etale topological groupoid, with S(M) of the homotopy type of its classifying space, Prop. 4.1.2 (p. 286), Cor. 4.2.2 (p. 287). This is the language of §11/O2 in stage 05.

### 2.13 Ribet 1988, already present. K. A. Ribet, "On the component groups and the Shimura subgroup of J_0(N)", Sém. Théor. Nombres Bordeaux 1987-1988, Exp. 6, 10 pp. (EuDML record 182260, MR 993107). The file is the GDZ/EuDML scan, image-only (11 PDF pages including a cover); the copy on Ribet's homepage (`math.berkeley.edu/~ribet/Articles/bx_87.pdf`) is the same file (11 pages, same 158 characters of text), so no better copy is available there. Page images not read for any specific theorem in this package.

### 2.14 Bushnell-Henniart 2006 §56. Manual. *The Local Langlands Conjecture for GL(2)*, Grundlehren 335, Springer 2006; Crossref lists the chapter "The Jacquet-Langlands Correspondence" as DOI 10.1007/3-540-31511-x_13, **pp. 325-337** (its section number 56 is *not* verified here; the book itself is not available). Springer, Caltech library.

### 2.15 OCR/text-layer copies
No OCR engine (tesseract, ocrmypdf) is installed on this node and installing one is outside the rules, so no new OCR copy was made. State of the present files (`pdftotext` on the whole file): `hida_1988_p-adic-hecke-algebras-for-gl2-over-totally-real-fields.pdf` (Ann. of Math. 128, 91 pages) **does have a text layer** (175 000 characters from the JSTOR OCR; formulas partly garbled, theorem headers are legible); `shimizu_1965_zeta-functions-of-quaternion-algebras.pdf` (Ann. of Math. 81, pp. 166-193; 29 pages) has only the JSTOR cover page text (1 300 characters), the rest is image; `pizer_1980_an-algorithm-...-scan.pdf` (26 pages) has no text (26 characters). For Pizer 1980 (J. Algebra 64 (1980), 340-390, DOI 10.1016/0021-8693(80)90151-9) the publisher's free open-archive copy at ScienceDirect should give a text layer (bot challenge for curl: manual). Shimizu: JSTOR only (DOI 10.2307/1970389), no open copy known. Other scans without text layer: Ribet 1984, Ribet 1988, SGA 7 I (all image only), Kurihara 1993. Miyake 2006 has a text layer.
Hida 1988 Ann. Math. headers located in the text layer (printed page = PDF - 293 for pp. 362-373): **Thm 8.6** (p. 362): canonical isomorphism of the ordinary parts independent of the weight, Hecke-equivariant for U_1(N) with N prime to p; Thm 8.7 (p. 363); **Thm 9.4** (p. 369): restriction map induces an isomorphism on the ordinary cohomology at finite-order characters (control theorem); **Thm 10.1** (p. 370); **Cor. 10.4** (p. 373).
Hida, AJM 110 (1988), 323-382 (`hida_1988_modules-of-congruence-...pdf`, PDF n = printed - 321): pp. 363-366 are the proof of Theorem 0.1 inside §5 (§5 starts p. 360); §6 "Modules of congruence" starts p. 366; Thm 7.9 is on p. 379, Thm 7.11 on p. 380. (Hsieh Rem. 7.3 uses these pages; the Remark number is Hsieh's, not Hida's.)

### 2.16 Longo-Vigni, bibliographic data resolved
Two different papers, both present: (1) M. Longo, S. Vigni, "Quaternion algebras, Heegner points and the arithmetic of Hida families", **Manuscripta Math. 135 (2011), no. 3-4, 273-328** (Crossref DOI 10.1007/s00229-010-0409-6; first published online 2010-11-09; arXiv:0903.2797, "heavily revised and shortened version, to appear in Manuscripta Mathematica"); file `longo-vigni_2009_*_arxiv.pdf`. (2) M. Longo, S. Vigni, "A note on control theorems for quaternionic Hida families of modular forms", **Int. J. Number Theory 8 (2012), no. 6, 1425-1462** (Crossref DOI 10.1142/S1793042112500856; arXiv:1110.1977); file `longo-vigni_2011_control-theorems-for-quaternionic-hida-families_arxiv.pdf` (its arXiv title is "A note on control theorems for quaternionic Hida families of modular forms"). So stage 01's "Manuscripta Math. 135 (2011) 273-328" is right for the Heegner-points paper, and stage 04's "Int. J. Number Theory 8 (2012)" is right for the control-theorems note; the inputs disagreed only because they cite different papers. The Padova page also hosts the Manuscripta version (https://www.math.unipd.it/~mlongo/docs/Manuscripta.pdf, 43 pages; not saved: the arXiv file is already present).

### 2.17 HPS 1989. Manual / only if Caltech has it. H. Hijikata, A. Pizer, T. Shemanske, "The basis problem for modular forms on Gamma_0(N)", Mem. Amer. Math. Soc. 82 (1989), no. 418 (AMS bot challenge; deferred on our side). Only the 1980 announcement is present.

## 3. Item 3: refresh table, "listed as missing but present"

Entries of `MISSING_LITERATURE.md` that can be updated. "Checked" = bibliographic data on the first page of the file and, where indicated, the cited place.

| item in `MISSING_LITERATURE.md` | now | file | what was checked |
|---|---|---|---|
| 1 Casselman 1973 | present | `casselman_1973_some-results-of-atkin-and-lehner.pdf` (Math. Ann. 201, 301-314, 14 pp., PDF n = printed - 300) | Thm 1 (p. 302): conductor c(pi) of an irreducible admissible infinite-dimensional representation of GL_2(k), the space of vectors fixed by the corresponding K_1-type subgroup is one-dimensional; Corollary to the proof (p. 306): replacing c by an ideal p^i c of larger level gives dimension i+1; Thm 3 (p. 312): adelic dictionary; Thm 4 (p. 313): dim of the level-N space for pi = prod (n_i + 1), newform = case N = c(pi). **Warning: the file does not contain the explicit operator U_p = sum_j pi((p j; 0 1)) or any statement identifying it with the classical U_p** (grep for "Hecke", "U_p", "operator": only Atkin-Lehner newform theory, p. 312-313). The stated "why" (identify N_{U_p} with classical U_p, Rem. rem:s01-Upconv) is therefore not supported by this paper; the oldform count (i+1) of p. 306 is the useful piece |
| 3 Miyake 1989 | present | `miyake_2006_modular-forms.pdf` (Springer Monographs in Math., 2006 repr. of 1989; text layer; 345 PDF pages) | Thm 5.2.9 (printed p. 204, PDF 213): for an indefinite quaternion algebra B over Q, R a maximal order, N a positive integer and local elements beta_p of norm one for p | N, there is beta in B of norm one with beta = beta_p mod N R_p for p | N and beta in R_p for p not dividing N; **Thm 5.2.10 (Approximation Theorem)** (p. 207, PDF 216): the same for prescribed norm n, with beta in R and beta = beta_p mod N R_p. Statement "Thms 5.2.9-5.2.10 (strong approximation over Q)" confirmed |
| 4 Ribet 1984 | present | `ribet_1984_congruence-relations-between-modular-forms_scan.pdf` (12-page scan, printed 503-514, PDF = printed - 502) | Prop. 3.4 (p. 510), Thm 4.1, Cor. 4.2, Thm 4.3 (p. 511), (4.4) and proof (pp. 512-513), refs p. 513-514 (see 1.1); (2.2) p. 506 and Prop. 3.3 p. 509 as in `litnotes/s03.md` |
| 5 Hida 1986a | present | `hida_1986_galois-representations-into-gl2-zp-x-attached-to-ordinary-cusp-forms.pdf` (Invent. Math. 85 (1986), 545-613, 69 pages) | title page and journal data match; no theorem number verified in this package |
| 6 SGA 7 IX | present | `grothendieck_1972_sga-7-1-...-scan.pdf` | all numbers in 1.2 |
| 7 Helm 2007 | **published version present** | `helm_2007_maps-between-modular-jacobians-and-jacobians-of-shimura-curves.pdf` (Israel J. Math. 160 (2007), 61-117, DOI 10.1007/s11856-007-0056-0, 57 pp.) | **Cor. 8.11 and Rem. 8.12 are on p. 110** (PDF 50), numbering confirmed (as in the 2004 preprint): Cor. 8.11: for m outside S controllable at every prime dividing D, J^D[m] and J^1[m] have the same dimension; if m satisfies multiplicity one for J^{1,1} then dim J^D[m] = 2; Rem. 8.12: the same for all non-Eisenstein m if Gamma = Gamma_0(M) or Gamma contains Gamma_1(r), r >= 4. The item "only the 2004 arXiv preprint is present" in the unusable list (item 12) is also out of date |
| 15 Mazur-Wiles 1986 | present | `mazur-wiles_1986_p-adic-analytic-families-of-galois-representations.pdf` (Compositio Math. 59 (1986), 231-264, Numdam; printed = PDF + 229) | **§9 Proposition 2** (p. 254, PDF 25): if the residual representation attached to a prime P of the Hecke algebra T is irreducible, then the equivalent statements (a)-(d) hold, in particular (d) T_P is Gorenstein; the equivalence "(a)-(d)" is stated just before as following from §8 Proposition 2 (p. 247: the T-module M is free of rank 1, A-modules M, W free of ranks r, 2r, T finite flat of rank r over the Iwasawa algebra, Cohen-Macaulay of dimension two). Hsieh's citation "[MW86, §9 Prop. 2]" is correct |
| 16 Moerdijk-Pronk 1999 | present | see 2.12 | |
| 20 Ribet 1988 (Bordeaux) | present (scan, image-only) | see 2.13 | |
| 21 Böckle 2007 | present, published CUP version | `bockle_2007_presentations-of-universal-deformation-rings.pdf` (LMS Lecture Note Ser. 320, CUP 2007, pp. 24-58; DOI 10.1017/CBO9780511721267.003; printed = PDF + 23) | **Cor. 4.3** (p. 39): for the presentation 0 -> J -> O[[T_1..T_h]] -> R_S -> 0 one has h - gen(J) >= h^0(G_{F,S}, ad rho) - h^0(G_{F,S}, (ad rho)^vee) - delta + sum over nu in S of (h_nu + delta_nu - h^0(G_nu, ad rho) - gen(J_nu)) (4.5), proof following Wiles; **Thm 5.8** (p. 49): for F totally real, rho odd, local conditions (i)-(iv) (local gen(J_nu) bound, choice of versal hulls at infinity, flat or ordinary deformations at p, h^0(G_{F,S}, (ad^0 rho)^vee) = 0), the GL_2 deformation ring has the expected presentation (complete intersection bound). Both numbers as in [KO] |
| 27 Li 1975 | present | see 2.6 | |
| 2 HPS 1989 | still missing (only 1980 announcement) | -- | 2.17 |
| 14 Ihara 1975 | **now present** | `ihara_1975_on-modular-curves-over-finite-fields_vol.pdf` | 1.1 |
| 10 Pizer 1976, 22 Brzezinski 1990, 26 Emerton 2002, 17 Buzzard 1997 | now present (Emerton, Buzzard as preprints) | see 2.3, 2.10, 2.7, 2.9 | |
| Hida 1988 (Ann. Math.) in the "unusable" list | has a text layer | see 2.15 | formulas partly garbled, headers legible; theorem numbers/pages in 2.15 confirmed |
| Longo-Vigni bibliographic data (unusable item 7) | resolved | see 2.16 | |

## 4. Self-audit

(1) Proof steps: none (a literature package). (2) Level hypotheses: where a cited statement has hypotheses on the level, they are recorded
with the paraphrase: Li Thm 3(iii) requires "epsilon a character mod MN/q" and q^2 not dividing MN; Helm Cor. 8.11 needs m controllable at primes dividing D and
m outside S (residue characteristic 2, 3 excluded unless Rem. 8.12 applies: Gamma_0(M) or Gamma_1(r), r >= 4); Buzzard Thms 4.7, 4.10 are for l not dividing d only; SGA 7 Thm 10.4 and 11.5 need A_K semistable over a henselian S, Thm 12.5 needs
a regular model with ordinary quadratic singularities (so weight 1 only; weights w_e are not covered, flagged in 1.2 (c)); Ihara's Lemma 3.2 is for n prime to p and trivial coefficients (not Sym^{k-2}, flagged in 1.1);
Casselman Thm 1/4 are local statements for K_1-type fixed vectors (no U_p identification, flagged). (3) Edge cases: none besides the weight-1 and trivial-coefficient restrictions above.
(4) Every cited page re-opened:
- SGA 7 I Exp. IX: the page images of Thm 2.4 (printed p. 338, PDF 343), Def. 9.1.2 (p. 418, PDF 423), Thm 10.4 (p. 444, PDF 449), Thm 11.5 with Rem. 11.5.2 (p. 455, PDF 460),
  (12.3.7) (p. 472, PDF 477), Thm 12.5 (p. 475, PDF 480), (5.5.1)-(5.5.3) (p. 378, PDF 383), (10.3.5) (p. 443, PDF 448) were rendered a second time after the text was written and read again; they contain the stated items.
  Pages read once in a 2x2 contact sheet at 80 dpi (statements legible, not re-opened at higher resolution): pp. 321-337, 339-345, 379-386, 420-421, 436-443, 445-448, 453-454, 456, 465-476, 477-480. The Exposé running numbers ("- k -") agree with printed = 318 + k on every page read.
- Illusie Thm 2.7: rendered page image (volume PDF 46) and the text layer, both read; printed p. 41.
- Ihara 1975: text layer of PDF 178-197 (printed 171-190) read; margin marks of the original pagination read in the text (161-179); Main Theorem p. 171, Lemma 3.2 p. 187, §3.3 pp. 188-189, §3.5 p. 190; the final page range of the paper in the TIFR contents (171-215) vs the original (161-202, from Ribet's reference [6] image, p. 513) checked on both sides.
- Ribet 1984: images of pp. 510, 511, 513, 514 read (Thm 4.1, 4.3, ref. [6] "pp. 161-202", "page 178 of [6]"); pp. 512 not separately re-read beyond the continuation of the argument on 513.
- Text-layer sources (Casselman, Li, Miyake, Helm, Böckle, Mazur-Wiles, Moerdijk-Pronk, Hida 1988 x2, Pizer 1976, Emerton, Buzzard): the printed page numbers were read from the page headers/footers in `pdftotext` output of the very pages that contain the statements (not computed from an offset alone), except Moerdijk-Pronk, where the footer number is the page number of the page it closes (checked on the intro page: footer 269 on PDF 1).
- Brzezinski: page images of printed pp. 166-169 and 182-185 read; statements of (4.1)-(4.8) read there.
- Not verified / flagged: Gelbart §3, Swan pages, Kneser 196 vs 197, Bushnell-Henniart §56 (book not available); Hida 1986a theorem numbers; Ribet 1988 theorem numbers; JAMS and Duke pagination of Emerton and Buzzard.
