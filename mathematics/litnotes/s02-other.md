# S02 literature notes: all non-Voight, non-Serre `\lit` pointers of `plan/staged/stage-02-tree-quotients.tex`

All sources in `/home/janosch/dev/Langlandscape/literature/` (present: every file below). Paraphrases only; page numbers are
printed pages with PDF page in brackets. Status of every item: *cited*.

## Brown, Cohomology of Groups (GTM 87, 1982), VII.7, (7.10), p.174 [PDF 185]
File `brown_1982_cohomology-of-groups.pdf` (318 PDF pages; printed = PDF - 11 here). VII.7 "Equivariant Homology" starts p.173.
Setting: `X` a **`G`-complex** (CW complex, `G` permutes cells; `G_sigma` the cell stabiliser acting on the cell `sigma`
through the orientation character `chi_sigma: G_sigma -> {+-1}`); `M_sigma = Z_sigma (x) M` is `M` **twisted by the orientation
character**. (7.7): `E^1_{pq} = (+)_{sigma in Sigma_p} H_q(G_sigma, M_sigma) => H^G_{p+q}(X,M)`, `Sigma_p` = representatives of
`p`-cells mod `G`. (7.3): if `X` is acyclic, `H^G_*(X,M) = H_*(G,M)`; then (7.10) is the same spectral sequence converging to
`H_{p+q}(G,M)`. For a tree (dimension 1) it has two columns and degenerates to a long exact sequence (Serre II.2.8).
The differential `d^1` is computed in VII.8, Prop. 8.1 (pp.175-176): **only "up to sign"**, via restriction/transfer maps
`H_*(G_sigma) -> H_*(G_{sigma tau}) -> H_*(G_tau)` (transfer for the `G_sigma`-finite boundary cells; conjugation `v_tau`).
Brown does **not** fix the sign convention of the boundary; fixing it is the content of Serre II.2.8 Remark 1.
Hypotheses to watch: `X` acyclic (contractible) is needed; stabilisers are in `G`; if `G` inverts an edge the orientation
character is non-trivial (`M_sigma` twisted by `-1`), whereas the tex works without inversion so `M_sigma = M`.

## Boutot-Carayol, Asterisque 196-197 (1991), Ch. III, "Le theoreme de Cerednik-Drinfeld", Thm (5.2)
File `asterisque_1991_courbes-modulaires-et-courbes-de-shimura_vol.pdf` (262 PDF pages; printed = PDF - 5 in this chapter).
Chapter III begins at PDF 130. Section 5 "Le theoreme de Cerednik-Drinfeld: enonce, variantes, commentaires" starts p.139 [PDF 144];
**Thm (5.2) is on pp.140-141 [PDF 145-146]**.
Setting (5.1, p.139): `A` the quaternion algebra over `Q` (indefinite, ramified at `p`) attached to the Shimura curve `S_U`,
`Delta`/`A'`-type: the algebra `A'` obtained by changing the invariants at `p, infty` (definite), `A'^*` its reductive group;
`U = U^p x GL_2(Z_p)`-type compact open level, `U^p` "assez petit".
Thm (5.2): for `U^p` small enough, an isomorphism of formal `Z_p^{nr}`-schemes
`\hat S_U (x) Z_p^{nr} ~= GL_2(Q_p) \ [ (\hat Omega (x) \hat Z_p^{nr}) x Z_U ]`, with `Z_U = A'^*(Q) \ A'^*(A_f) / U^p`-type finite
double coset set, compatible with change of `U` and the Hecke action; also with formal special modules. The orbits of `GL_2(Q_p)` on `Z_U`
have stabilisers `Gamma_x = A'^*(Q) cap x U^p x^{-1}` (discrete cocompact, containing a power of `p`).
**5.3.3 (p.143, checked on the page image).** Extra hypotheses: (a) `Nrd(U^p) = prod_{l != p} Z_l^*` (maximal) and (b) the `p`-adic valuation
maps `U^p cap Q^*` **onto `Z`** (scalars of all `p`-adic valuations lie in `U^p`). Then by strong approximation `A'^*(Q_p)` acts
transitively on `Z_U`, the quotient is `Gamma \ \hat Omega (x) Z_p^{nr}` with `Gamma = A'^*(Q) cap U^p`, `Gamma_+` = elements of even
`p`-adic valuation of `Nrd` is of **index 2**, `W = Gamma/Gamma_+`, and one gets the **twisted form** `W \ [(Gamma_+\hat Omega) (x) Z_p^{(2)}]`
(Frobenius acts through any `w in Gamma - Gamma_+`).
**5.4.3-5.4.4 (pp.145-146 [PDF 150-151]).** Kurihara's theorem: for a discrete cocompact `Gamma <= PGL_2(Q_p)` the curve `Gamma\Omega` is
admissible (Jordan-Livne) and its dual graph **with lengths** is `(Gamma\I)'` = quotient graph with the edges equal to their own inverse
removed; **length of an edge = order of the stabiliser (in `PGL_2`, i.e. modulo the centre) of a lift**. Under the hypotheses of 5.3.3 the
graph of the special fibre is `[A'^*(Q_p)_+ \ (I x Z_U)]` with Frobenius acting by an element of odd valuation (swaps the two types).
Graph conventions in 5.4.2: Serre graphs (oriented edges, origin = component containing the branch).

## Bass, Covering theory for graphs of groups, JPAA 89 (1993) 3-47
File `bass_1993_covering-theory-for-graphs-of-groups.pdf` (printed = PDF + 2). Setting of 3.2-3.6: a group `Gamma` acting **without inversion**
on a connected graph `X`; choose a maximal tree `T` of `Gamma\X`, lifts `s`, and elements `g_y`, giving a graph of groups `Gamma\\X` with
vertex/edge groups the stabilisers in `Gamma`. **Thm 3.6, p.28 [PDF 26]** (the discussion of data starts p.27): (a) homomorphism
`pi_1(Gamma\\X) -> Gamma` (`e |-> g_{o}g_{t}^{-1}`-type) ; (b) a `Gamma`-equivariant covering `Y -> X` ... ; (c) `Y -> X` is a covering inducing isomorphisms of
the local groups; (d) exact sequence `1 -> pi_1(X) -> pi_1(Gamma\\X, a_0) -> Gamma -> 1`. **Cor. 3.7, pp.28-29 [PDF 26-27]** (cf. Serre I, Thm 13):
for `X` connected TFAE: (a) `X` is a tree; (b) `Y -> X` is an isomorphism; (c) `pi_1(Gamma\\X) -> Gamma` is an isomorphism.
Cor. 3.8 (p.29): morphisms of quotient graphs of groups induce homomorphisms of the acting groups.

## Casselman, "The Bruhat-Tits tree of SL(2)" (preprint, 2014)
File `casselman_2014_bruhat-tits-tree-of-sl2_preprint.pdf` (42 pp.; printed = PDF). **S2, p.5:** nodes = lattice classes `<<[u,v]>>`,
`nu_m = <<[u_0, varpi^m v_0]>>`, `nu_0 = o^2`; `alpha = diag(1, varpi)` has `alpha(nu_n) = nu_{n+1}`; `GL_2(k)` acts by `g[u,v] = [gu,gv]` (columns),
through `PGL_2(k)`. A node `<<M>>` is **even/odd** according to the parity of `n - m` where `[L:M] = [varpi^m : varpi^n]` (matrix index, `L = o^2`);
`SL_2(k)` preserves parity and has exactly two orbits on nodes. Edges are **unoriented** ("lattice pair invariant"); a standard chain is
`nu_0 -- nu_{-1} -- nu_{-2}...` with `L_n > L_{n+1} > varpi L_n`. Prop. 2.1, Cor. 2.3, Cor. 2.4 (tree, `q+1` neighbours). **S3, pp.7-8:** nodes at distance
`m` <-> `P^1(o/p^m)` (Prop. 3.1); `K = GL_2(o)` fixes `nu_0`; `K_0 = SL_2(o)` fixes `nu_0` and its "twin" `K_1 = alpha K alpha^{-1}` fixes
`nu_1 = alpha nu_0` (conjugation by `alpha` not given in a closed form for `K` vs `K_0` in the OCR; printed text reads `K_1 = alpha K alpha^{-1}`, with `K`
presumably `K_0`); both are maximal compact in `SL_2(k)`, not conjugate in `SL_2(k)`.
Casselman does not discuss the Iwahori subgroup as an edge stabiliser in these pages.

## Ludwig-Merten, "Formalising the Bruhat-Tits tree", Ann. Formalized Math. 2 (2026) 55-81
File `ludwig-merten_2026_formalising-the-bruhat-tits-tree.pdf` (27 PDF pp.; printed = PDF + 54). Lean `v4.19.0` ("stable version", p.57).
S3.4 Acyclicity, p.69 [PDF 15]: Lemma 3.3 (every trail is `GL_2(K)`-conjugate to a standard chain, following Casselman Prop. 4.1[sic, in the
2019 version]); main theorem `BTtree : SimpleGraph.IsTree (BTgraph R)`. S3.5 Regularity, pp.69-70 [PDF 15-16]: neighbours of `L` <-> lines in
`L/varpi L`, so for `|k| = q` the tree is `(q+1)`-regular. S3.6 Group actions, pp.70-71 [PDF 16-17]: `GL_2(K)` acts transitively; with
`v_0 = [R^2]`, `v_1 = [L_1]`, `L_1 = (e_0, varpi e_1)`, the **pointwise stabiliser of the edge `{v_0,v_1}` is `K^* x I_1`** (centre times
`I_1`), `I_1 <= GL_2(R)` **"upper triangular modulo `varpi`"** (`c == 0`). `SL_2(K)` is not transitive: **even/odd** vertices by
parity of the valuation of the determinant of a basis matrix (`v_0` even); equivalently parity of distance from `v_0`.
S4 Definition 4.1, p.72 [PDF 18]: edges are **unordered pairs** `{v,w}`; `w_par(v) = +1` (even), `-1` (odd);
`Delta: Maps(E,M) -> Maps(V,M)`, `Delta f (v) = w_par(v) * sum_{e in E, v in e} f(e)`; harmonic cochains `= ker Delta`.

## Vigneras, Arithmetique des algebres de quaternions (LNM 800, 1980)
File `vigneras_1980_arithmetique-des-algebres-de-quaternions.pdf` (176 PDF pp.; printed = PDF - 7).
- **Ch. III, Thm 4.1 (Theoreme des normes), p.80 [PDF 87].** `K_H` = elements of `K` positive at the real places ramified in `H`; then
  `K_H = n(H)` (for `K=Q`, `H` definite: `n(H) = Q_{>0}`). Proof: build a quadratic extension by approximation. Cor. 4.2: integrality version.
- **Ch. III, Thm 4.3 (Approximation forte), p.81 [PDF 88].** `S` nonempty set of places of `K` containing an infinite place if `K` is a number field;
  `H^1_{S'} = prod_{v in S'} H^1_v`; `H^1_v` is compact iff `v in Ram(H)`, else `SL(2,K_v)`. Theorem: if `H^1_S` is **not compact**, then
  `H^1_K H^1_S` is dense in `H^1_A` (equivalently `H^1_K` dense in the `S`-away adelic group). The "condition d'Eichler" (C.E.): `S` contains a
  place not ramified in `H`. The theorem was proved for number fields by Kneser from Eichler's norm theorem.
- **Ch. V, S3.B "Graphes arithmetiques", Prop. 3.3, p.147 [PDF 154].** `p nmid D`; `X = PGL(2,Z)\PGL(2,Q_p)`-tree, fix a maximal order `O`,
  vertices of the tree = maximal orders `O'` with `O'_q = O_q` for `q != p`, edges with origin `O'` = integral left `O'`-ideals of reduced
  norm `pZ` (so edges are **oriented**, `p+1` out of each vertex); `Gamma = O[1/p]^* / Z[1/p]^*` acts, **the quotient graph is finite and the vertex
  stabilisers are `O'^*/{+-1}` (cyclic of order 1, 2 or 3; 12 or 6 for `H = (-1,-1), (-1,-3)`)** (stabilisers taken **modulo the centre `+-1`**).
  Prop. 3.3: **the number of vertices of the quotient graph `Gamma\X` = class number `h` of `H`** (maximal orders; one vertex of order 12 or 6 for
  the two exceptional cases, otherwise the number of vertices of order `i` is `h_i`). Mass formula for each vertex `x`:
  `q+1 = e(x) sum_{y in A(x)} e(y)^{-1}` (`e` = order of vertex/edge stabiliser mod `+-1`); `P_1(x) = e(x) sum_{x'} e(y)^{-1} x'`.
  The `Gamma` here is the **full** group `O[1/p]^*` (including odd `p`-valuation), not the norm-one group; hence one copy of `X_B`.

## Platonov-Rapinchuk, Algebraic Groups and Number Theory (1994), S7.4, Thm 7.12, p.427
File `..._2up.pdf` (**two printed pages per PDF page**; printed p.426-427 on PDF 220; S5.1 definition on printed p.250 [PDF 132]).
Thm 7.12: `G` a **reductive** group over a number field `K`, `S` a finite subset of `V_K`; `G` has the strong approximation property wrt `S`
iff (1) `G` is simply connected (in particular semisimple) and (2) no `K`-simple component `G_i` of `G` has `G_i(K_S)` compact (i.e. `G_S` non-compact).
Definition (S5.1, p.250): `G_K -> G_{A_S}` has dense image, `A_S` = adeles **omitting** `S` (equivalently `G_K G_S` dense in `G_A`). For `K=Q`,
`G = SL_1(B)`, `B` definite: simply connected, `Q`-simple; `S = {infty,q}` gives `G_S` non-compact since `B_q ~= M_2(Q_q)`. Note `S` need not
contain `infty` in the statement; for `S={infty}` alone `SL_1(B)(R)` is compact so SA fails.

## Kneser, Lectures on Galois cohomology of classical groups (Tata 1969), S5.5, Sublemma b
File `kneser_1969_lectures-on-galois-cohomology-of-classical-groups.pdf` (123 PDF pp.). Printed page **72** [PDF 78]; the margin
numbers in the scan (95, 96) are the original Tata page numbers: Sublemma b is on **original p.94**, matching the tex's "p.94".
Sublemma b ("Strong approximation theorem for simple algebras, cf. [11], [15]"), stated **without proof**: `G` the norm-one group of a simple
algebra `A` with centre `K` a number field, `O` an order, `S` a finite set of places with `S` containing the infinite places; suppose `v_0 in S` with `A_{v_0}`
**not a division algebra**; given `a_v in G_{K_v}`, there is `x in G_K` with `x` close to `a_v` for `v in S, v != v_0` and `x in O_v` for `v notin S`.
(Sublemma a, same page: Hasse norm theorem for quadratic extensions, without proof; both are used in the proof of Lemma 1, which is about
`K(tyt')` and not about SA.) Note the shape: approximation only at `S - {v_0}` plus integrality, i.e. SA with the non-compact place `v_0` omitted.

## Diamond-Taylor, Non-optimal levels of mod l modular representations, Invent. math. 115 (1994) 435-462
File `diamond-taylor_1994_non-optimal-levels-...pdf` (28 PDF pp.; printed = PDF + 434). **Lemma 2, statement p.445, proof p.446 [PDF 11-12].**
Setting: definite quaternion algebra `D`, `U` open compact `<= D_f^*` with `U_p <= O_{D,p}^*`... (U_p maximal at `p` as in the text), `p` prime not dividing `N_U s l`.
`A = ker( alpha: S_k(U; F_l)^2 -> S_k(U_0(p); F_l) )`, `alpha(f_1,f_2) = f_1 + phi_p f_2`. Claim: for some `d >= 1`, `T_q - 2` and `S_q - 1` annihilate
`A[l]` for all but finitely many primes `q == 1 mod d`, i.e. the kernel is **Eisenstein-like** (not zero). Proof: `U'` = elements of `U` that are `1 mod l`;
`SL_2(Q_p)` is generated by `SL_2(Z_p)` and `eta^{-1} SL_2(Z_p) eta` (cites Serre [S1]); **strong approximation** gives, for `q == 1 mod d` and
`gamma` of norm `varpi_q`, `g gamma g^{-1} = delta g u g^{-1}` with `delta in D^*`, `u in U' cap SL_2(Q_p)`; hence `f_1(g gamma) = f_1(g)`, `T_q f_1 = (q+1) f_1`.
(The duality part follows, with Cor. 1 on p.446: maximal ideals in the support of the cokernel/kernel are Eisenstein.)

## Mismatches (all non-Voight, non-Serre pointers)
1. **Line 294, Boutot-Carayol Ch. III Thm 5.2, "pp. 139-140":** the theorem sits on **pp.140-141** (statement p.140 bottom/141); section 5 starts p.139. More
   importantly **Thm 5.2 is the Cerednik-Drinfeld uniformisation, not the dual-graph statement.** The identification "dual graph of the special fibre =
   `Gamma_+\ I`" with lengths = stabiliser orders is **5.3.3 (p.143) + 5.4.3 (Kurihara) + 5.4.4 (pp.145-146)**, valid under hypotheses (a) `Nrd(U^p) = prod_{l != p} Z_l^*`
   and (b) scalars of every `p`-adic valuation in `U^p`; the tex's remark states only the scalar condition ("`Gamma_0`-type"), omits (a), and does not
   say that over `Z_p` one gets a **twisted form** (Frobenius = element of odd valuation, swapping the two types). Edge lengths in BC are stabiliser orders in `PGL_2`
   (= modulo centre, i.e. `Gamma_x/+-1`).
2. **Line 228, Brown VII.7 (7.10), p.174:** correct. Brown fixes the differential only "up to sign" (8.1, pp.175-176) and works with
   `G`-complexes and orientation-twisted coefficients `M_sigma`; the tex's "equivalently the equivariant spectral sequence" is right only without inversions
   (then `M_sigma = M`), and the signs `(-s_{0*}, s_{1*})` come from Serre, not Brown.
3. **Line 258, Bass S3 Thm 3.6, Cor. 3.7, "pp.27-29":** Thm 3.6 is p.28 (PDF 26) (the construction 3.2-3.5 precedes it, p.27 is the end of the proof
   discussion), Cor. 3.7 is pp.28-29. Hypothesis: `Gamma` acts **without inversion** on a connected graph; stabilisers are taken in `Gamma` (not mod centre).
   *Applied in S02-M7a (prop:s02-free: Thm 3.6 p.28; Cor 3.7 pp.28-29).*
4. **Line 66, Casselman S2 p.5, S3 pp.7-8:** page numbers correct. The tex's claim "`K_1 = alpha K alpha^{-1}`" is Casselman's text with `K` there equal to
   `K_0 = SL_2(o)` (printed OCR ambiguous). Casselman's even/odd is via the matrix-index parity `n - m`; matches `ord_q det` parity for `SL_2` images. Edges there are
   unoriented.
5. **Line 69, Ludwig-Merten S3.6 p.70-71, Def. 4.1 p.72:** correct, but their stabiliser is `K^* x I_1` (centre included): "pointwise stabiliser of the edge"
   in `GL_2(K)`; the tex quotes only `I_1`, fine for `SL_2` or `GL_2(Z_q)`-level. Their `Delta` uses unordered edges and `w_par`; the tex's equivalence with its
   oriented harmonicity is as claimed. Lean version in the paper is `v4.19.0` as the tex says; the tex's "S3.4 and S3.5, p.69-70" is also right (S3.4 p.69, S3.5 pp.69-70).
6. **Line 194, Vigneras Ch. V S3.B Prop. 3.3, p.147:** correct; Vigneras's `Gamma` is `O[1/p]^*/Z[1/p]^*` (full group, quotient graph has `h` vertices, stabilisers
   `O'^*/+-1` and edge orders `e(y)` also mod `+-1`). The tex's "classical picture with `h` vertices" requires `X_B(U)/<q> = X_B(U)` at maximal level, which holds (diamond
   operator trivial). The statement is for **maximal** `O`, `p nmid D`, `H` over `Q`.
7. **Lines 117-118, Vigneras III Thm 4.1 p.80; line 126 Thm 4.3 p.81:** correct. Vigneras's Thm 4.3 requires `S` to contain an infinite place and `H^1_S` non-compact;
   the tex's `S = {infty, q}` is allowed. Her form is "`H^1_K H^1_S` dense in `H^1_A`" (**all** adeles), which is equivalent to density of `B^1` in the `S`-away group.
8. **Line 127, Platonov-Rapinchuk S7.4, Thm 7.12, p.427:** correct (printed 427, right half of PDF 220). Hypothesis: `G` reductive over a **number field**
   (the tex's `Q`-simple, simply connected `SL_1(B)` qualifies); `S` finite subset of `V_K` (the criterion is that no simple component is `S`-compact).
9. **Line 128, Kneser S5.5 Sublemma b, "p.94":** this is the **original Tata pagination**; in the scanned reprint the page is printed **72** (PDF 78). The statement is
   *Applied in S02-M7a (both paginations given).* Without proof (cites [11], [15]) as the tex says; shape: approximation at `S - {v_0}` with `v_0` a non-division place in `S`, plus integrality outside `S`.
10. **Line 160, Diamond-Taylor Lemma 2 "pp.445-446":** correct. But the lemma does **not** state a definite Ihara lemma (injectivity); it says the kernel `A` of
    `(f_1,f_2) |-> f_1 + phi_p f_2` is **Eisenstein** (annihilated by `T_q - 2`, `S_q - 1` for almost all `q == 1 mod d`), using strong approximation and `SL_2(Q_p)` generated by
    `SL_2(Z_p)` and its `eta`-conjugate. Corollary 1 (p.446) deduces that maximal ideals in the support of the relevant quotients are Eisenstein; the tex's "classical use of SA at this
    point is the definite Ihara lemma" is the paper's remark that this lemma "plays the role of Ihara's result" (p.445).
11. **Brown III.8 (added by audit S02-M6, item M6.9):** the homological "inner automorphisms act trivially" statement is Prop. (8.1), p.79;
    the cohomological one is Prop. (8.3), p.80. *Applied in S02-M7a (rem:s02-minusone cites both).*
