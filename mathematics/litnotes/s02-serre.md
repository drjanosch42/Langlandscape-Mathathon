# S02 literature notes: Serre, Trees (Springer 1980, English transl.)

Source: `literature/serre_1980_trees.pdf` (151 PDF pages, OCR scan; **printed page = PDF page - 9**; some displayed formulas
are lost in the OCR text, the Prop. II.2.8.13 page was checked on the page image). Paraphrases only; status *cited*.
Serre's graphs: oriented edges `y`, with `o(y)`, `t(y)` (origin, terminus), inverse `\bar y`; an orientation `Y+` is a
set of edges containing exactly one of `y, \bar y`; "acts without inversion" means no `g` with `g y = \bar y`.

## I.3.3 Theorem 4 and 4', p.27 [PDF 36]
Thm 4: a group acting **freely** (without inversion, and no `g != 1` fixes a vertex) on a tree is free.
Thm 4': `G` acts freely on the tree `X`; choose a tree `T` of representatives of `X mod G` (3.1) and an orientation `Y+` of
`X` **preserved by `G`**. (a) Let `S` = set of `g != 1` such that some `y in Y+` has `o(y) in T` and `t(y) in gT`; then `S` is
a basis of `G`. (b) If `X* = G\X` has finitely many vertices (`s`) and `Card(edge X*) = 2a`, then `Card S - 1 = a - s`,
so the free rank is `a - s + 1`, `a` = number of **geometric** edges of `X*`.
Convention: edges `y in Y+` with `o(y) in T`, `t(y) not in T` correspond to `S`; the bijection `W -> S`, `W` as in the proof.

## I.4.3 Proposition 18, Proposition 19, p.36 [PDF 45]
Prop. 18: `G = G_1 *_A G_2` acting on its tree `X` (4.1, Thm 7). `Gamma <= G` with `Gamma - {1}` disjoint from all conjugates of
`G_1, G_2` (equivalently `Gamma` acts freely on `X`) is free (by Thm 4, 3.3).
Prop. 19: `Gamma` a group acting on a tree `X`, TFAE: (a) `Gamma . A` bounded for every bounded `A subset vert X`; (b) some orbit
`Gamma . P` bounded; (c) `Gamma` fixes a vertex. Proof of (b)=>(c): the subtree spanned by the bounded orbit is bounded and
stable, so (cor. to Prop. 10, I.2.2) has a fixed vertex **or a fixed geometric edge**; "no inversion" kills the second case.
**"No inversion" is a standing hypothesis of the proof (stated as an assumption in the proof), not in the displayed
statement.** Corollary of Thm 8 (same page): finite subgroups of an amalgam lie in a conjugate of `G_1` or `G_2`.
So: a finite group acting **without inversion** fixes a vertex (finite orbit is bounded). Free action = no inversion +
trivial vertex stabilisers (definition at 3.3, p.27).

## II.1.1 (The tree of `SL_2` over a local field; the tree of `V`), pp.70-72 [PDF 79-81]
`K` field with discrete valuation `v`, `O`, `pi`, residue field `k`; `X` = lattice classes `[L]` of `V = K^2`, adjacency
`d([L],[L']) = 1` (i.e. `L' subset L`, `L/L' ~ k`, up to homothety).
Theorem 1, p.70: the graph `X` is a **tree** (proof shows `d(A,A')` is the tree distance). p.72 "Projective lines": vertices at
distance `n` from `A_0` <-> rank-1 direct factors of `L_0/L_0 pi^n`; for `n = 1` the edges with origin `A_0` <-> points
of `P(L_0/pi L_0) = P^1(k)`, so there are `q+1` of them when `q = |k|` is finite (the tree is `(q+1)`-regular);
ends <-> `P^1(K)`. Exercises 3a (p.73): number of vertices at distance `n>=1` is `q^{n-1}(q+1)`.
Serre's edges here are **unoriented adjacency** (graph of vertices at distance 1); orientations come only via `GL(V)^+`/types
(II.1.3) or `II.1.4`. The transitivity of `SL_2(k)` (`PSL_2(k)`) on `P^1(k)` is **not** in II.1.1: it appears at II.1.4, p.79 (proof of
transitivity on edges, variant), see below.

## II.1.3 (Action of `GL(V)` on the tree; stabilisers), pp.76-77 [PDF 85-86]
Notation: `GL(V)^0 = ker(v(det))`, `GL(V)^+ = ker(GL(V) -> Z -> Z/2Z)` (p.75), so `SL(V) <= GL(V)^0 <= GL(V)^+`.
p.76: `s in GL(V)` lies in `GL(V)^+` iff `s` preserves each of the two vertex classes (distance even); in particular `GL(V)^+`
acts **without inversion**. `GL(V)` acts with inversion: for `L = e_1 O + e_2 O`, `L' = e_1 O + e_2 pi O`, the matrix
`(0 1; pi 0)`-type element swaps `L'` and `L pi` (maps the edge `AA'` to its inverse).
Stabilisers: `G` a subgroup, `G_L` (stabiliser of the lattice) and `G_A` (stabiliser of the class); `G_A = {s : sL = Lx, x in K^*}`.
Lemma 1 (p.76): if `G subset GL(V)^0` then `G_L = G_A` (via `v(det s) = 2 v(x)` and `d(L, Lx) = 2v(x)`); in particular for `SL(V)`.
Proposition 2 (p.76) and Corollary: for `G <= GL(V)^0` bounded <=> fixes a vertex; maximal bounded subgroups = vertex stabilisers.
p.77 "Stabilizers of the edges: Iwahori subgroups": `AA'` edge with lattices `L' subset L`, `l(L/L') = 1`; for `G <= GL(V)^0`,
`G_{AA'} = G_L cap G_{L'}`, the preimage of the stabiliser of a line in `L/pi L`. **Matrix form: `L = e_1 O + e_2 O`,
`L' = e_1 O + e_2 pi O`; `G_{AA'}` = matrices `(a b; c d)` with `c == 0 mod pi`** (inverse image of the upper triangular
subgroup of `GL_2(k)`). Stabilisers are **in `G`** (not mod `+-1` or mod centre); for `G <= GL(V)^0` the centre intersection is `O^*`
elements only, so no `pi`-power scalars appear.

## II.1.4 (Amalgams), Thm 2, pp.78-79 [PDF 87-88] (not in the tex list; relevant to local surjectivity)
Theorem 2: under (D) (closure of `G <= GL(V)^+` contains `SL(V)`) the edge `A0--0A'` is a fundamental domain. In part b) (p.79) `G_L` acts transitively on edges with origin `A`; the variant uses that the
image of `G_L -> PGL_2(k)` contains `PSL_2(k)` and `PSL_2(k)` acts transitively on `P^1(k)`.

## II.1.5 Theorem 4 (Ihara), p.82 [PDF 91]
`Gamma <= GL(V)^0` containing no bounded subgroup `!= {1}` is free; by Prop. 2 (II.1.3) the hypothesis is equivalent to `Gamma` acting
freely on `X`, so it follows from I.3.3 Thm 4 (variant: amalgam + I.4.3 Prop. 18). Thm 5 (same page): `K` locally compact,
`Gamma` discrete torsion-free in `SL_2(K)`: Euler-Poincare-type volume statement (not used).

## II.2.8 Proposition 13 and Remark 1, p.127 [PDF 136] (checked on the page image)
Setting (p.126): `G` acts on a tree `X` (**preserving the chosen orientation `Y+ = edge+(X)`**, i.e. without inversion);
chain complex `C_1(X) = Z[Y+] -> C_0(X) = Z[vert X] -> Z`, with **`d(y) = t(y) - o(y)`** and augmentation `eps(x) = 1`.
`Sigma_0`, `Sigma_1` are systems of representatives of `vert X` and `Y+` modulo `G`; `G_x`, `G_y` stabilisers **in `G`**.
Prop. 13: for each `G`-module `M`, exact sequences
`... -> H_{i+1}(G,M) -> prod_{y in Sigma_1} H_i(G_y,M) -> prod_{x in Sigma_0} H_i(G_x,M) -> H_i(G,M) -> ...` and dually
`... -> H^i(G,M) -> prod_{x} H^i(G_x,M) -> prod_{y} H^i(G_y,M) -> H^{i+1}(G,M) -> ...`.
Remark 1: the maps `H_i(G_y,M) -> H_i(G_x,M)` are zero unless `x` is an end of `y`; if `x = t(y)` it is induced by the inclusion
`G_y -> G_x`, if `x = o(y)` it is **minus** the induced map. Dually for cohomology. Remark 2: it is `H_*(G\X; H_s(G_*,M))` with
the cosheaf of stabiliser homology (`0 -> H_0(G\X, H_i) -> H_i(G,M) -> H_1(G\X, H_{i-1}) -> 0`). Example (Lyndon): amalgams.
Sign convention thus: `partial = (-s_{0*}, s_{1*})` when `o(y)` is the type-0 vertex and `t(y)` the type-1 vertex, matching
the tex's `\partial` (type-0 end gets the minus sign).

## Mismatches (Serre pointers vs tex)
1. **Line 64 (II.1.3 "Stabilizers of the edges", p.77):** correct; same base edge and `c == 0 mod pi` as the tex.
2. **Line 77 (II.1.1 Thm 1, p.70):** correct. The `(q+1)`-regularity and the neighbours-as-`P^1(L/qL)` are at **p.72**
   ("Projective lines"), not p.70; the cited theorem is only "X is a tree". *Applied in S02-M7a (lem:s02-tree(a) cites both pages).*
3. **Lines 80, 86 (II.1.3, p.76; Lemma 1, p.76):** correct. Serre states Lemma 1 for subgroups of `GL(V)^0` (`v(det)=0`),
   not for `SL` only and not for even valuation (`GL(V)^+`). The tex's "`g in GL_2(Q_q)` preserves types iff `ord_q det g` even"
   is the p.76 statement (`GL(V)^+`).
4. **Line 227 (II.2.8 Prop. 13, Remark 1, p.127):** correct page and number. Serre requires the **orientation preserved by `G`**
   and uses stabilisers in `G` itself (no `Gamma_x/+-1`); the tex's sign convention (inclusion at `t(e)`, minus at `o(e)`) agrees
   with Remark 1. If the tex's `Gamma_x` are taken modulo `+-1` somewhere, Serre's sequences do not apply as stated
   (use stabilisers in the actual group acting, `GU`).
5. **Line 257 (I.3.3 Thm 4, 4', p.27; II.1.5 Thm 4, p.82):** correct. Serre's rank formula is `a - s + 1` with `a` = geometric edges of
   the quotient and `s` = its vertices; the tex's `(q-1)|X_B(U)|+1` equals this when `s = 2|X_B|` and `a = (q+1)|X_B|`. Note
   Thm 4' needs a `G`-**preserved orientation** (here the type-0 -> type-1 orientation) and that `X*` be taken with Serre's graph
   structure (no edge equal to its inverse, automatic here).
6. **Line 357 (I.4.3 Prop. 19, p.36):** the statement "a finite subgroup acting on a tree fixes a vertex" holds **without inversion**
   (the proof uses it); Prop. 19 itself is phrased for bounded orbits/fixed vertex. "Trivial vertex stabilisers give a free action"
   additionally needs "without inversion" (Serre's definition of free, I.3.3, p.27), which holds for `GU <= SL_2(Q_q)` (II.1.3, p.76).
   The more direct source for "free on `X`" is I.4.3 Prop. 18's remark and I.3.3 definition.
7. **Line 325 (II.1.1, for "`SL_2(F_q)` transitive on `P^1(F_q)`, the neighbours of `v_0`"):** II.1.1 (p.72) gives only
   "neighbours <-> `P^1(k)`". Transitivity of `PSL_2(k)` on `P^1(k)` is quoted at **II.1.4, p.79** (variant in part b of the proof of
   Thm 2). Suggest citing II.1.1 p.72 plus II.1.4 p.79, or giving the one-line argument.
