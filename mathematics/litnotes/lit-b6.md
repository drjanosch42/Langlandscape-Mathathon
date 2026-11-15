<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# lit-b6: literature for stages 5-6 (work batch 6, package E2)

Node: Abhijit. BASE `7b4b3d7`. Retrieval date 2026-11-14. All paraphrases are our own; status of every citation is *cited*.
PDFs live in `literature/` (git-ignored, never committed). "p." = printed page, "[PDF n]" = page of the file.
Page offsets: Hida 1986a PDF = printed - 544; Eichler (LNM 320 volume file) PDF = printed + 4; Kneser (PSPM 9 volume file) PDF = printed + 9;
Atkin-Li PDF = printed - 220; Li 1975 PDF = printed - 284; Buzzard 1997, Takahashi 2001: PDF = printed - 590 / - 73.

## 0. Summary table

| # | item | obtained? | file / source |
|---|---|---|---|
| 1a | Atkin-Li 1978, Invent. Math. 48, 221-243 | **yes (new this batch)**, 23 pp, page images | `atkin-li_1978_twists-of-newforms-and-pseudo-eigenvalues-of-w-operators.pdf`; Springer publisher PDF `https://link.springer.com/content/pdf/10.1007/BF01390245.pdf` (open download, no login) |
| 1b | Li 1975, Math. Ann. 212, 285-315 | present | `li_1975_newforms-and-functional-equations.pdf` |
| 1c | Atkin-Lehner 1970, Math. Ann. 185, 134-160 | present (scan, whole paper, no text layer) | `atkin-lehner_1970_hecke-operators-on-gamma0-m_scan.pdf` |
| 1d | Hida 1986a, Invent. Math. 85, 545-613 | present, text layer | `hida_1986_galois-representations-...pdf` |
| 2a | Eichler 1973, LNM 320, pp. 75-152 | present (volume); page range **confirmed** | `eichler_1973_..._lnm320-vol.pdf` |
| 2b | Kneser 1966, PSPM 9, pp. 187-196 | present (volume); page range **confirmed** | `kneser_1966_strong-approximation_pspum9-vol.pdf` |
| 3a | Buzzard 1997, Duke 87, 591-612 | present, **verified** (Duke typeset version) | `buzzard_1997_integral-models-of-certain-shimura-curves.pdf` |
| 3b | Takahashi 2001, JNT 90, 74-88 | present, **verified** | `takahashi_2001_degrees-of-parametrizations-...pdf` |
| 3c | Gelbart 1975 (Ann. Math. Stud. 83) | **not obtainable**: Princeton UP book; Open Library lists no full text | library copy needed |
| 3d | Kurihara 1979 | **not obtainable now**: U-Tokyo repository (JAIRO Cloud) is in maintenance since 2026-10-28 (HTTP 503) | retry later; the exact title/DOI of the cited 1979 paper is not recorded in the files I checked |
| 3e | Emerton-Pollack-Weston 2006, Invent. Math. 163, 523-580 | present (58 pp, DOI 10.1007/s00222-005-0467-7) | `emerton-pollack-weston_2006_...pdf` |
| 3f | Deligne 1974, La conjecture de Weil I, Publ. IHES 43, 273-307 | present (36 pp, Numdam) | `deligne_1974_la-conjecture-de-weil-i.pdf` |

## 1. Item 1 (for E3)

### 1.1 Atkin-Li 1978, Invent. Math. 48 (1978) 221-243, DOI 10.1007/BF01390245
Setting (section 0-1, pp. 222-223 [PDF 2-3]): modular forms of weight k on Gamma_0(N) with Nebentypus epsilon (so this is the
"Gamma_1-type" space via the diamond decomposition), N = Q M with (Q, M) = 1, epsilon = epsilon_Q epsilon_{N/Q}. The operator
W_Q is given by a matrix (Qx y; Nz Qw) of determinant Q with y = 1 mod Q, x = 1 mod N/Q; right slash action as in Li 1975.
Checked in page images (p. 223 and p. 224):
- **Prop 1.1, p. 223**: F in M(N, eps_Q eps_{N/Q}, k) gives F|W_Q in M(N, conj(eps_Q) eps_{N/Q}, k) (same for cusp forms), and
  F|W_Q|W_Q = eps_Q(-1) conj(eps_{N/Q})(Q) F; another admissible matrix W' multiplies by conj(eps_Q)(y') conj(eps_{N/Q})(x'); so W_Q is
  well defined. Consequence (ours, not stated there): W_Q <d> W_Q^{-1} = <d'> with d' = d^{-1} mod Q, d' = d mod N/Q.
- **Prop 1.2, p. 223**: p not dividing N: F|T_p|W_Q = eps_Q(p) F|W_Q|T_p (no complex conjugation, checked in a zoomed image).
- **Prop 1.3, p. 223**: q' | N, (Q, q') = 1: F|U_{q'}|W_Q = eps_Q(q') F|W_Q|U_{q'}.
- Prop 1.4, p. 223: composition F|W_Q|W_{Q'} = conj(eps_{Q'})(Q) F|W_{QQ'} for (Q', QN/Q') = 1. Prop 1.5, p. 223: F|B_M|W_Q relations.
- The proofs of 1.1-1.5 are omitted by the authors ("straightforward computations").
- **(1.1), p. 224**: for a newform F with a(p) and G = F|W_Q normalised, b(p) = conj(eps_Q)(p) a(p) for p not dividing Q, and
  b(p) = eps_{N/Q}(p) conj(a(p)) for p | Q. **Thm 1.1, p. 224**: |lambda_Q(F)| = 1. **Thm 2.1, p. 225**: if a(q) is nonzero then
  lambda_q(F) = Q^{k/2-1} g(eps_Q)/a(Q) (Gauss sum; uses F|U_Q|W_Q).
- **Gap for E3**: nothing for U_q with q | Q, i.e. no operator identity for w_{p^s} U_p w_{p^s}^{-1} (only the eigenvalue relation
  (1.1) on newforms); nothing about Gamma_1(Mp^s) with diamonds beyond Prop 1.1; nothing on Jacobians or on X_q(J_s). The formulas
  cover the classical Hecke side T_ell (ell not dividing N), U_ell (ell | M), and the diamonds.
Paraphrase: the paper fixes the sign/character bookkeeping for the Atkin-Lehner operator at Gamma_0(N) with character: W_Q inverts the
Q-part of the character, commutes up to eps_Q(p) with T_p for p outside the level and with U_q for q in the level but outside Q, and
squares to a scalar. These are the only operator identities stated; everything for the q | Q part is deduced via newforms.

### 1.2 Li 1975, Math. Ann. 212 (1975) 285-315 (present)
- **Lemma 2, p. 288**: V_q^M (= q^{-k/2} times a W_{q^e}-type matrix, e = ord_q M) maps C_eps(M,1) to itself for eps a character mod M/q^e,
  commutes with T_p (p not dividing M), and V_q^M|V_q^M = eps(q^e) (an automorphism). Only for eps of conductor prime to q.
- **Lemma 3, p. 289**: for q | M, q^2 not dividing M, eps mod M/q: U_q + q^{k/2-1} V_q^M maps C_eps(M,1) to C_eps(M/q,1)
  (proof in the page shows (q U_q + q^{k/2} V_q^M)|g = eps(d) (...)). Lemma 1, p. 287: U_q preserves C(M,1) for q | M.
- Conclusion: Li 1975 has no Gamma_1 conjugation formulas with diamond twist; Atkin-Li 1.1 is the better source.

### 1.3 Atkin-Lehner 1970, Math. Ann. 185, 134-160 (scan present)
Gamma_0(m), trivial character only (introduction p. 134-135 checked in the image). Not opened beyond that; not usable at Gamma_1 level.
No page is cited from it.

### 1.4 Hida 1986a, Invent. Math. 85 (1986) 545-613 (PDF = printed - 544)
- **Thm 1.1, p. 551 [PDF 7]**: control isomorphism T^ord / (P_k) = T_k(Np^infinity) for k >= 2 (ordinary Hecke algebra of the tower).
- **(1.10a), p. 553 [PDF 9]**: the Hecke algebra (Hida's script T / h^ord) is free of finite rank over Lambda; **quoted** there from
  Hida, "Iwasawa modules attached to congruences of cusp forms" ([13] in the paper, then "to appear in Ann. Sci. Ec. Norm. Sup.";
  Th. 3.1, Cor. 3.2 of that paper). So the Lambda-freeness of T^ord itself is *cited* here, not proved; the page for the proof is in Hida 1986b.
- **Thm 3.1, p. 562 [PDF 18]**: for the Pontryagin duals V^ord, W^ord of the ordinary parts of the cohomology of Gamma_1(Np^r) in
  the limit over r: (i) restriction identifies level r with the Gamma_r-invariants; (ii) **V^ord and W^ord are free of finite rank
  over Lambda**; (iii) the ranks (rank_Lambda V^ord = 2 rank_Lambda of the Hecke algebra of level N; formula for W^ord). Only for the
  *ordinary* parts (the remark after Thm 3.1: false for the whole module).
- **Proof of (ii), Section 6, p. 587 [PDF 43]**: Lemma 6.3 (a compact Lambda-module is free of rank r iff its dual has
  M[P_n] = Z_p^r for infinitely many n), Step II "V^ord and W^ord are Lambda-free", Lemma 6.4 (Shimura: H^1(Gamma_1(M), L_k(K)) is free
  of rank 2 over the Hecke algebra).
- **Albanese/Picard tower, Section 8, p. 595 [PDF 51]**: J_r = Pic^0(X_r), X_r = X_1(Np^r); Tate module J_r; the Hecke ring acts
  contravariantly on Pic^0; projection X_r -> X_s (r > s) gives J_s -> J_r (Pic, contravariant), the covariant picture J_r -> J_s is the
  Albanese one ("we identify J_r with the Albanese variety of X_r", p. 595, covariant action on Alb). **p. 596 [PDF 52]**: the duality
  pairing with (a x, a y) = chi(a)(x, y) and (h x, y) = (x, y h); the maps J_r -> J_s and J_s -> J_r are mutually adjoint, so the
  pairing passes to the limit (Pontryagin duality). **Warning on p. 596**: the right action (Pic^0) and left action (Alb) of the Hecke
  operators on J_r differ and are transformed into each other by the involution of the canonical divisor class. **Lemma 8.1, p. 596**:
  V_K is free of rank 2 over the Hecke algebra h(N; K).

## 2. Item 2: in-volume page numbers

### 2.1 Eichler 1973, "The basis problem for modular forms and the traces of the Hecke operators", LNM 320 (1973), pp. 75-152
Volume: *Modular Functions of One Variable I* (Antwerp 1972, ed. W. Kuijk), 2nd corrected printing 1986; file 197 pages. The article
starts with its title page at **p. 75 [PDF 79]**, the table of contents is p. 76 [PDF 80] (Chapter I theta series 80; Chapter II quaternion
algebras 90; Chapter III traces of Hecke operators 116; Chapter IV the basis problem 138) and the last page is **p. 152 [PDF 156]**
(a note thanking Cohen/Zagier/Ponomarev/Pizer for errata). **Range 75-152 confirmed.** Uses:
- Brandt matrices: Chapter II, **section 6, p. 103 [PDF 107]** (definition (15), the matrices B(n; D, H) from the ideal classes of an
  order of discriminant D and level H); **Thm 2, p. 106 [PDF 110]**: properties (17)-(20), generate a semisimple commutative ring;
  Cor 1 to Thm 2, p. 108 [PDF 112] (index-0 matrices split off a one-rowed component); section 7 (with character) p. 109; Thm 4, p. 112
  [PDF 116]; section 8 and Thm 5 (trace of the Brandt matrix), pp. 112-113 [PDF 116-117].
- Basis problem: Chapter IV section 1, **p. 138 [PDF 142]**: Proposition (theta series times T(n) = Brandt matrix times theta series for
  (n, K) = 1), with a footnote: the proof does not exclude that the theta series in one column are linearly dependent (the erratum by
  Ponomarev and Pizer). **Theorem, p. 139 [PDF 143]** (checked in the page image): for N = p_1 ... p_r a product of distinct primes
  (squarefree), S_k(Gamma_0(N)) (k > 2 even, trivial character) is the direct sum of theta spaces Theta_{k-2}(p_i, p_{i+1}...p_r)
  (i = 1..r, with the Brandt matrices attached to discriminant p_i and level p_{i+1}...p_r) plus oldform images of lower levels; for
  k = 2 replace by Theta^0 and S_2(Gamma) = 0 for Gamma = SL_2(Z). The proof compares traces of T(1) and T(n), n a square.
- Caution: the file text layer is typewritten OCR; formulas were read in a page image only for p. 139.

### 2.2 Kneser 1966, "Strong approximation", PSPM 9 (1966), pp. 187-196, DOI 10.1090/pspum/009/0213361
Volume file 436 pages (whole Proceedings of Symposia in Pure Mathematics 9, Algebraic Groups and Discontinuous Subgroups).
Article: starts at **p. 187 [PDF 196]**, last page (references) **p. 196 [PDF 205]**. **Range 187-196 confirmed.** Uses:
- p. 187: setting (G linear algebraic group over a number field k, S a finite set of places, strong approximation = G_S G_k dense in G_A);
  Example 2: Eichler's theorem for norm-one groups of central simple algebras that are not definite quaternion algebras;
  necessary conditions (1) G_S not compact, (2) G simply connected.
- **Main Theorem, p. 188 [PDF 197]**: if G is simply connected, absolutely almost simple, and G_S is not compact, then (G, S) has strong
  approximation. The text says the proof holds modulo the Hasse principle, hence in all cases except possibly type E_8 at the time.
  The next sentences give the general criterion (unipotent radical, simply connected quotient, each almost simple factor with
  non-compact S-component). Application to class numbers follows on the same page.

## 3. Item 3: items for stages 5-6

### 3.1 Buzzard 1997, "Integral models of certain Shimura curves", Duke Math. J. 87 (1997), 591-612 (DOI 10.1215/S0012-7094-97-08719-6)
The file is the Duke typeset version (22 pp, header "Vol. 87, No. 3 DUKE MATHEMATICAL JOURNAL (C) 1997", printed pages 591-612
confirmed; it supersedes the 1996 preprint). What is in it (all in sections 1-5, text layer read):
- Sec. 1-2: false elliptic curves; Thm 2.1, p. 595 (X(U) is an algebraic stack over Z[1/Mvd]). Def 3.1-3.4, pp. 598-599: Gamma_0(l), Gamma_1(l), balanced and canonical balanced Gamma_1(l)-structures.
- **Thm 4.5, p. 602**; **Thm 4.7, p. 603**: X(U, Gamma_0(l)) is smooth away from the supersingular points in characteristic l, proper,
  finite flat over X(U), regular, and its fibre at l has two irreducible components, both isomorphic to X(U)_{F_l}, crossing transversally
  at the supersingular points (the analogue of Deligne-Rapoport V.1). **Thm 4.10, pp. 607-608**: the same for X(U, Bal.can Gamma_1(l)):
  smooth of relative dimension one over Z[1/Mvd][zeta_l] (i), proper (ii), finite over Gamma_0(l) (iii), flat and regular (iv), special
  fibre two components isomorphic to X(U, Ig(l)) crossing transversally at the supersingular points (v) (the analogue of DR V.2.12).
  Prop 5.1 and Thm 5.2 (Hodge-bundle section with simple zeros), both p. 610, are used elsewhere.
- **No statement about the character group / dual graph of the special fibre** appears (the words "character group" do not occur).
  So the statement "character group of J_0^D(M) at p | D is the group of degree-0 divisors on the definite class set" is, in Buzzard,
  at most a consequence of Thm 4.7(v) read via Grothendieck's monodromy; Takahashi attributes it to "Theorem 4.7 in [3]" (see 3.2) -
  the Duke numbering matches Thm 4.7 only for the Gamma_0(l) special fibre. Flag for E3: cite Takahashi/Ribet for the character group, Buzzard only for the model.

### 3.2 Takahashi 2001, "Degrees of parametrizations of elliptic curves by Shimura curves", J. Number Theory 90 (2001), 74-88 (DOI 10.1006/jnth.2000.2614)
File 15 pp; header "Journal of Number Theory 90, 74-88 (2001)", pages 74-88 confirmed. Uses:
- **Prop 3.1, p. 82**: a canonical exact sequence 0 -> X_p(J') -> X_q(J) -> X_q(J'')^2 -> 0 of character groups, compatible with Hecke
  operators T_n (n prime to N) and with the monodromy pairings (J = J^{dq}_0(m)-type Jacobians of Shimura curves); for D = 1 it is
  Ribet's level-lowering [13, Thm 4.1]; for D > 1 "handled analogously using Buzzard's analogue [3] of Deligne-Rapoport" (also Jordan-Livne, Yang).
- **Thm 3.2, p. 82**: h_q = h'_p, i_q | i'_p (= c'_p) and a formula for the degree-type invariant delta delta' in terms of c'_p, i_q, j_q.
- **Thm 3.8, p. 84** and its proof: the character group X_r(J_0^{(dr)}(rm)) is canonically the group of degree-0 divisors on the set of
  isomorphism classes of locally free rank-1 right modules over the Eichler order of level m in the definite quaternion algebra of
  discriminant d, compatibly with T_n (n prime to N) and with the monodromy pairings; so h_r, i_r, delta j_r do not depend on r | d.
  The proof cites "Theorem 4.7 in [3]" = Buzzard (see 3.1). This is the statement Kohel Thm 4.3 refers to. Section 4 (p. 85) says the
  T-module X_r(J) with its monodromy pairing is describable via the definite quaternion algebra.

### 3.3 Not obtainable
- **Gelbart 1975**, *Automorphic forms on adele groups*, Ann. Math. Stud. 83, Princeton UP: book, no free full text (Open Library: no
  ebook). Needs a library copy; the plan asks for section 3 (adelic vs classical dictionary: diamond inversion, U_p).
- **Kurihara 1979**: the U-Tokyo repository answers 503 "JAIRO Cloud maintenance, from 2026-10-28, end date undecided". Retry later.
  I could not identify the exact title from the repository's search page (unavailable) or Crossref in two tries; do not rely on any
  title until the manual download exists.

### 3.4 Newly recorded as present
EPW 2006 (Invent. 163, 523-580, 58 pp, first page checked) and Deligne 1974 (Publ. IHES 43, 273-307, 36 pp, Numdam first page checked).

## 4. Manual-download list

| item | best URL / action |
|---|---|
| Gelbart 1975 | library copy of Ann. Math. Stud. 83 (Princeton UP) |
| Kurihara 1979 | U-Tokyo repository `https://repository.dl.itc.u-tokyo.ac.jp/` after the maintenance ends; or the journal's Project Euclid/Tokyo J. page |
| Hida 1986b, "Iwasawa modules attached to congruences of cusp forms", Ann. Sci. ENS (4) 19 (1986), 231-273 (bibliographic data from memory, unverified) | not present; needed for the proof of Lambda-freeness of T^ord (Hida 1986a quotes it at (1.10a)); Numdam likely hosts it - **not tried this batch** |

## 5. Self-audit

Every page cited above was re-opened after writing (text layer or image) and the headers/page numbers matched:
- Atkin-Li pp. 223, 224 (images; the absence of a complex conjugate in Props 1.2/1.3 and the form of (1.1) read in zoomed crops), p. 225 (text layer, Thm 2.1).
- Li 1975 pp. 287-289 (p. 289 image; Lemma 3 statement and proof read there).
- Hida 1986a pp. 551, 553, 562, 587, 595, 596: header page numbers re-checked from the page headers, text read.
- Eichler PDF 107, 110, 112, 116, 117, 142, 143 against the printed -103- ... -139-; p. 139 image; PDF 79/156 for pp. 75/152.
- Kneser PDF 196, 197, 205 against printed 187, 188, 196.
- Buzzard 1997: statements of Thms 4.7, 4.10, 5.2 read in the text layer (OCR damaged symbols; pages from the running heads).
- Takahashi 2001: Prop 3.1, Thm 3.2, Thm 3.8 read in the text layer; page numbers from the running heads (82, 84).
Limits (not checked): the Atkin-Lehner scan beyond p. 134-135; the OCR'd proofs inside Eichler and Hida (only statements used);
Hida 1986b not available. No statement was weakened or smoothed over; the gap for U_q, q | Q in Atkin-Li is stated in 1.1.
