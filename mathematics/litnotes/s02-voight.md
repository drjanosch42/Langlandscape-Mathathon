# S02 literature notes: Voight, Quaternion Algebras (GTM 288, 2021)

Source: `literature/voight_2021_quaternion-algebras.pdf` (877 PDF pages; **printed page = PDF page - 12 in Ch. 14, PDF - 6 in
Ch. 27-28, PDF - 4 in Ch. 41**; page numbers below are printed, PDF in brackets). Paraphrases only. Status: all items *cited*.
Notation in Voight: `B` quaternion algebra over a global field `F`; `S` an "eligible" set of places (contains the archimedean
ones); `R` the ring of `S`-integers; hatted objects (`\hat B`, `\hat O`) are the **S-finite** adeles / completion of an
`R`-order `O` (Voight 27.6.4, p.469); `B^1` = reduced-norm-one group; `B_S = prod_{v in S} B_v`.

## 14.7.4 Main Theorem (Hasse-Schilling), p.234 [PDF 246]
Hypotheses: `B` quaternion algebra over a global field `F`; `Omega` = set of ramified real places (empty for function fields).
Statement: `nrd(B^x) = F^x_{>0,Omega}` = elements positive at all `v in Omega` (14.7.3). The inclusion "<=" is 14.7.1.
Proof (pp.234-236) builds a separable quadratic `K = F(t)` embedding in `B` with prescribed norm, via 14.7.5 (local
irreducible quadratics) and 14.7.6 (approximation of polynomials), then 14.6.7.
Consequence used: `B` definite over `Q` (`Omega={infty}`) gives `nrd(B^x) = Q_{>0}`.
No conventions on stabilisers/edges are involved.

## 28.4.8, p.484 [PDF 490]
Hypothesis: `B^1` is **dense in `\hat B^1`** (S-finite norm-one adeles). Conclusion: for **every order `O`**
(an `R`-order), `\hat B^1 \subseteq B^1 \hat O^1 \subseteq B^x \hat O^x`.
Proof: `alpha \hat O^1` is open in `\hat B^1`, so it contains some `alpha' in B^1`; then `alpha = alpha' gamma` with
`gamma in \hat O^1`. The remark after it (and Exercise 28.7) says the density hypothesis fails for some `B`.
Subgroup type: the statement is for `\hat O^1`, the norm-one units of an order (compact open), **not an arbitrary
open subgroup**; the proof uses only openness of the coset, so it extends verbatim (see Mismatches).

## 28.5.1 and Main Theorem 28.5.3 (Strong approximation), p.485 [PDF 491]
Def. 28.5.1: `B` is *S-indefinite* (satisfies the S-Eichler condition) iff `S` contains a place **unramified** in `B`.
Theorem 28.5.3: `B` a quaternion algebra over a **global field** (number or function field), `B` S-indefinite. Then `B^1`
is dense in `\hat B^1` (the S-finite part, i.e. restricted product over places NOT in `S`).
28.5.4 says non-compactness of `B_S^1` is necessary. Two proofs are given later (the first follows Vigneras [Vig80a, Th. III.4.3]; PDF 497-500 are the proof of 28.5.3 using
14.6.7 for embeddings of quadratic fields and the compactness/closure argument; the second, group-theoretic, proof is
a separate section).
For the tex: `F = Q`, `S = {infty, q}`, `R = Z[1/q]`, `B` definite with `q` unramified: `B_q = M_2(Q_q)` unramified, so
S-indefinite. The density is then of `B^1` in `prod'_{l != q} B^1_l`. Matches the tex's wording.

## Cor. 28.5.12, p.486 [PDF 492]
Hypothesis: `B` S-indefinite, `O` an `R`-order. Statement (28.5.13), two equalities: `\hat B^1 = B^1 \hat O^1` and
`\underline B^1 = B^1 \underline O^1`, where (as in the printed text) `\underline B = \hat B x B_S` and
`\underline O = \hat O x B_S` (so `\underline B^1` = S-finite part times the `S`-components `B_S^1 = prod_{v in S} B_v^1`).
Proof: "contained" is trivial; "equal" is 28.4.8 plus 28.5.3; the second statement multiplies the first by `B_S^1`.
For the tex (`S={infty,q}`; note `B_S` then contains the compact archimedean factor `B_infty^1`, so the tex's finite-adelic
(SA_U) is the image of the second equality under projection away from `infty`): (SA_U) `\hat B^1 = B^1(B^1_q x U^{1,(q)})` is the
**second** equality with `O` replaced by an open subgroup. Follow-up 28.5.14: `O^1 -> (O/mO)^1` surjective for ideals `m <= R`.

## Other Voight pointers in the tex (not in the assigned list)
- **Prop. 14.6.7 (local-global principle for splitting/embeddings), p.232 [PDF 244].** `K/F` finite separable of global fields.
  TFAE: (i) `K` splits `B`; (ii) all `K_w` split `B`. If `[K:F]=2`: also (iii) `K -> B` embeds as `F`-algebras; (iv) local
  embeddings `K_v -> B_v` for all `v`; (v) `K_v` is a field for every `v in Ram B`. (14.6.8: also holds for `F x F`.)
  The proof is via Cor. 14.6.5 (`Ram B_K = emptyset`), i.e. Albert-Brauer-Hasse-Noether; Hasse-Minkowski is stated separately
  right after (14.6.9 ff.).
- **Cor. 7.7.3 (Skolem-Noether for elements), p.109 [PDF 128].** `B` central simple over `F`, `alpha_1, alpha_2 in B^x`:
  they have the same **irreducible** minimal polynomial over `F` iff `alpha_2 = beta^{-1} alpha_1 beta` for some `beta in B^x`.
  Irreducibility is essential (Exercise 7.1.5 hint: false otherwise). Conjugation direction: `alpha_2 = beta^{-1} alpha_1 beta`.
- **Main Thm 27.6.14 (Fujisaki's lemma), p.470 [PDF 476].** `B` a finite-dimensional **division** algebra over a global field.
  (a) `B^x <= B_(1)` is cocompact (norm-one ideles); (b) for any eligible `S`, `B^x <= B_S^x` (the S-finite ideles)
  is cocompact and `B^x \ \hat B^x / \hat O^x` is finite. (S-finite version needs `B` division; for `M_2` use other tools.)
- **41.2.13, p.769 [PDF 765] and Example 28.5.19, p.487 [PDF 493].** 41.2.13: `p` prime, the class of `p` generates
  `Cl_G(O)_R`; by Prop. 28.5.18 ideals may be taken of `p`-power reduced norm; the directed graph of such ideals with edges the
  `p`-neighbour relation is a regular directed tree of out-degree `Np+1` (Prop. 41.3.1), and the quotient by left `B^x`-equivalence
  is the `p`-Brandt graph. Ex. 28.5.19: `B` definite over totally real `F`, `S` = archimedean places, `O` locally norm-maximal,
  `Cl^Omega R` trivial, `p` unramified: every class in `Cls O` has an integral ideal of `p`-power norm; for `F=Q`,
  `D` the discriminant, `O` locally norm-maximal (e.g. Eichler) and `p nmid D`, every invertible right ideal class is
  represented by an integral ideal of `p`-power reduced norm. **Edge orientation/type/stabiliser conventions: none stated**
  (vertices are right ideal classes, the graph is the Brandt graph, directed edges = `p`-neighbours; no stabilisers mod `+-1`).

## Mismatches (Voight pointers vs `plan/staged/stage-02-tree-quotients.tex`)
1. **Lem. `lem:s02-normone`(b), line 117:** pointer 14.7.4 p.234 correct. OK.
2. **Thm. `thm:s02-SA`, line 125:** 28.5.3 p.485, Def. 28.5.1 correct. Voight's `\hat B^1` is the **S-finite** group
   (places not in `S`); the tex's `\hat B^{1,(q)}` is this for `S = {infty,q}`. OK. Voight's 28.5.3 is for `B` over a global
   field with the hypothesis "S-indefinite" (existence of an `S`-place where `B` splits); the tex's phrase "non-compact at q"
   is equivalent for number fields.
3. **Line 135, "28.4.8, p.484 and Cor. 28.5.12, p.486 for a general open subgroup":** Voight states both for the norm-one
   group of an **order** (`\hat O^1`), not for an arbitrary open subgroup `U^1`. The same proof works (open coset
   `y U^1` meets `B^1` by density), but the pointer is not a literal citation of the general-`U` shape. Suggest wording:
   "the proof of 28.4.8 applies verbatim to any open subgroup".
   The tex shape (SA_U) with the factor `B^1_q` is the *second* equality of (28.5.13) (`\underline B^1 = B^1 \underline O^1`),
   not the first; the pointer should say "second equality of (28.5.13)".
4. **Line 492, "Prop. 14.6.7 ... equivalent to Hasse-Minkowski for the ternary norm form on `B^0`":** that equivalence is **not**
   in Voight 14.6.7. Voight proves 14.6.7 from Cor. 14.6.5 (ABHN: `Ram B_K=emptyset`); Hasse-Minkowski is a separate
   statement after it. The gloss is mathematically fine (embedding `K -> B` iff `-disc` represented by the trace-zero ternary
   norm form) but should be marked as the plan's own remark, not Voight's.
5. **Line 494, Cor. 7.7.3:** correct page and number; note the hypothesis "same **irreducible** minimal polynomial" and the form
   `alpha_2 = beta^{-1} alpha_1 beta`; the tex's "for a division algebra elementary argument" is consistent.
6. **Line 497, Main Thm 27.6.14 p.470:** correct. The statement used is part (b) (finiteness of `B^x\ \hat B^x/\hat O^x` and
   cocompactness in S-finite ideles); the compactness is in part (a)/(b), division algebra hypothesis: **B definite quaternion
   algebra over `Q` is a division algebra**, so OK.
7. **Line 195, "41.2.13, p.769 and Example 28.5.19, p.487":** pages correct. 41.2.13 is about the `p`-Brandt graph as a quotient of
   a **directed** tree on ideals of `p`-power norm (no `+-1` convention); it does not itself assert `|X_B(U)/<q>|` or "h
   vertices"; the "h vertices" statement in the tex is Vigneras V.3.3 (see `s02-other.md`).
