# Task 1 (v6 request): SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z), Mayer–Vietoris with V = Sym^{k-2}

Written 2026-11-13 by an agent of the HACS project. HACS binary `hacs 0.2.0 (commit 5bd706911c89; contract [C] 1.27.0, [E] 1.25.3,
[U] 0.8.1)`, sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a`; repository tip at the time `ee9b57cc`. No HACS
source was changed, nothing was rebuilt.

**Tags.**

- **[HACS]**: computed by the shipped HACS binary. This covers two runs:
  - fresh `level_n(p, n, l, qs)` runs, which give dim H^1(Γ_0(p); Sym^n F_l), H^0 and char(T_q) mod l;
  - the Task-0 records `descent(N, n, P).module_Z()`, which give rank_Z and the exact char_Z(T_q) at N = 1 and N = p.
- **[indep]**: our own exact computation in stdlib Python + numpy + sympy (`scripts/amalgam.py`, `scripts/cell.py`). It does not call HACS. It re-implements the model of [C] from its definitions: ρ_n, the coset table, the Shapiro module, dg_1, dg_p, ω and T_q.
- **[derived]**: arithmetic on [HACS] and [indep] output, such as polynomial division or factoring (`scripts/summarize.py`, `cusp_compare.py`, `levelraise_check.py`).
- **[thm]**: a standard fact, cited and not computed.
- **[hand]**: checked by hand.
- **[not verified]**.

## 0. Conventions (fixed here; they are those of the HACS contract [C] 1.27.0 wherever [C] has one)

**Coefficients.** n = k − 2, which is even. The ρ_n convention is [C] def:rhon:

- column j of ρ_n(A) holds the coefficients of (ax+cy)^{n-j}(bx+dy)^j in the basis x^{n-t}y^t;
- A ↦ ρ_n(A) is multiplicative on M_2.

V := Sym^n Z_(l)^2 with l ≠ p. The **whole** group SL_2(Z[1/p]) acts on V by ρ_n, and the action is integral because p ∈ Z_(l)^×. **No twist of the action is
needed.** The element g below is never made to act on V as a group element; ρ_n(g) enters only through the identification κ.

For odd k, −I acts by −1, so all the cohomology vanishes over Z_(l) (l ≠ 2). Only even k is listed.

**The amalgam.** Put g := diag(1, p) and let the vertex groups be:

- G_1 := SL_2(Z), the stabiliser of the lattice Z^2;
- G_2 := g SL_2(Z) g^{-1} = { [[a, b/p], [pc, d]] }, the stabiliser of the neighbouring lattice g Z^2 = Z ⊕ pZ.

Then G_1 ∩ G_2 = Γ_0(p) = {c ≡ 0 mod p}, and SL_2(Z[1/p]) = G_1 *_{Γ_0(p)} G_2 [thm, cited by you as Serre, *Trees* II.1.4; we did not check the
page].

- Your diag(p,1)-conjugate δ^{-1}SL_2(Z)δ, δ = diag(p,1), is the same group G_2, because g = p·δ^{-1}.
- The conjugation inside G_2 is x ↦ g^{-1} x g = [[a, pb], [c/p, d]].

**The identification κ of the second vertex term.** κ: H^q(SL_2(Z), V) → H^q(G_2, V), with κ(c)(x) := ρ_n(g) c(g^{-1} x g).

- It is induced by the group isomorphism G_2 → SL_2(Z), x ↦ g^{-1}xg, together with the module isomorphism ρ_n(g) = diag(1, p, …, p^n). The latter is invertible over Z_(l).
- With δ = diag(p,1) in place of g one gets ρ_n(δ)^{-1} = p^{-n}ρ_n(g), which is the same map up to the unit p^n. No elementary divisor at l depends on this choice.

**Mayer–Vietoris** (from the tree 0 → Z[G/Γ_0(p)] → Z[G/G_1] ⊕ Z[G/G_2] → Z → 0):

  0 → H^0(SL_2(Z[1/p]),V) → H^0(G_1,V) ⊕ H^0(G_2,V) → H^0(Γ_0(p),V) → H^1(SL_2(Z[1/p]),V) → H^1(G_1,V) ⊕ H^1(G_2,V) →^α H^1(Γ_0(p),V) → H^2(SL_2(Z[1/p]),V) → H^2(G_1)⊕H^2(G_2) = 0

**The map α.**

- **Sign:** (x, y) ↦ res x − res y. Through κ on the second summand this is

  **α(x, y) = dg_1 x − dg_p y**,  with
  - (dg_1 c)(h) = c(h);
  - (dg_p c)(h) = ρ_n(g) c(g^{-1} h g), h ∈ Γ_0(p).

  These are exactly [C] prop:levelellU's dg_1 and dg_ℓ, and [C] prop:levelcorrespondence(4)(c).
- The other sign convention changes α by the automorphism (x,y) ↦ (x,−y) of the source. Kernel and cokernel are unchanged.

**The adjoint α\*.** α\*(z) := (ω z, −ω' z), where:

- ω = cor^{SL_2(Z)}_{Γ_0(p)}, which is [C]'s trace f ↦ Σ_j ρ_n(s_j^{-1}) f_j;
- ω' := κ^{-1} ∘ cor^{G_2}_{Γ_0(p)}, the transfer to the second vertex group, transported back.

So α\* is the transfer to the two vertex groups. We do not claim that it is the adjoint for a particular pairing.

The resulting blocks were computed [indep] in every cell, in two independent ways:

- ω' is evaluated by its own transfer formula over right cosets of Γ_0(p) in G_2;
- p^{-n}·(ω∘dg_p) and T_p are computed separately.

The blocks are:

  ω∘dg_1 = p+1,  ω∘dg_p = T_p (classical),  ω'∘dg_1 = p^{-(k-2)} T_p,  ω'∘dg_p = p+1,

so that

  **α\*α = [[ p+1, −T_p ], [ −p^{-(k-2)} T_p, p+1 ]]**  on H^1(SL_2(Z),V)^2.

On each T_p-eigenline with eigenvalue λ, det = −p^{-(k-2)}(λ^2 − (p+1)^2 p^{k-2}).

- For a cusp form f, λ = a_p(f).
- For the Eisenstein class, λ = 1+p^{k-1}, and the factor is (1−p^{k-2})(1−p^k).

[C] prop:oldspace(2) states the first two identities and HACS's [C] proves them; we re-checked all four numerically
(`check_*` fields in every `data/cells*/cell_*.json`: all `true`).

**The model.** SL_2(Z) = ⟨S⟩ *_{⟨−I⟩} ⟨U⟩ with:

- S = [[0,−1],[1,0]] and U = ST = [[0,−1],[1,1]];
- relators S^4 = U^6 = 1, S^2 = U^3 = −I.

For a module X on which 6 is invertible and −I acts trivially:

  H^1(SL_2(Z), X) = X / (im(1+S) + im(1+U+U^2))   ([C] prop:levelorbit(2), cl:amalgam).

A class x corresponds to the cocycle c_x(S) = 0, c_x(U) = (U−1)x. A cocycle c corresponds to the class m = b − a, where a = −¼Σ_{i<4} c(S^i) and b = −⅙Σ_{i<6} c(U^i).

**Level p.** We take M = Ind_{Γ_0(p)}^{SL_2(Z)} V with the following data, all as in [C] def:cosetrepsN, eq:MH and prop:levelellU:

- coset table s_j = [[1,0],[j,1]] for 0 ≤ j < p, and s_p = S;
- action (γf)_j = ρ_n(h_j(γ)) f_{j·γ};
- dg_1 = (ρ_n(s_j) v)_j and ω(f) = Σ_j ρ_n(s_j^{-1}) f_j.

A Γ_0(p)-cocycle z is carried to H^1(SL_2(Z), M) by the explicit inverse Shapiro map

  m_j = ¼ Σ_{i<4} F(s_j S^i) − ⅙ Σ_{i<6} F(s_j U^i),  F(x) = z(x s_{[x]}^{-1}).

It was checked against dg_1 = res in every cell.

**T_q (q ≠ p), at both levels.** These are the operators of [C] def:hecke / prop:levelcorrespondence(3) in group-cocycle form:

  (T_q z)(h) = Σ_t ρ_n(δ_t) z(δ_t^{-1} h δ_{t'}).

- The left-coset representatives are δ_t ∈ {[[q,−b],[0,1]] (0 ≤ b < q), [[1,0],[0,q]]}, the adjugates of [C] prop:cosets(1)'s right cosets. They serve both SL_2(Z) and Γ_0(p).
- t' is the index with δ_t^{-1}hδ_{t'} in the group.
- **Normalisation:** the classical one. T_2 = −24 on the Δ-line and T_q = 1+q^{k-1} on the Eisenstein class [indep, = HACS].
- On H^2(SL_2(Z[1/p]), V) = coker α, T_q is **the operator induced through the MV sequence**. α is T_q-equivariant; this was checked mod l^E for every (cell, l, q) and is `equivariance_T_alpha` in the JSON. We do not construct an intrinsic SL_2(Z[1/p])-double-coset operator.
- U_p and W_p are not used in Task 1.

**Arithmetic.**

- Level 1 is exact over Q.
- Level p is computed mod l^E, where E is the largest exponent with l^E < 2^25, and at least 2. The `modulus` field records it; for example 17^6, 29^5 and 131^3.
- An elementary divisor l^e with e < E is exact.
- Which l to examine is decided rigorously:
  - α is a map between free Z_(l)-modules (§1).
  - coker α has l-torsion ⇔ α mod l is not injective ⇒ α\*α mod l is singular ⇒ l | numerator of det(α\*α). That determinant is computed exactly over Q.
  - So **every** l > k, l ≠ p, at which torsion or a non-unit divisor can occur is among the primes of that numerator. Each of those was computed.

## 1. Facts used over Z_(l), l > k, l ≠ p (so l ≥ 5) [thm, and confirmed by the computation]

1. H^q(SL_2(Z), X) = 0 for q ≥ 2, for any Z_(l)[SL_2(Z)]-module X, because 4 and 6 are units. The same holds for G_2 ≅ SL_2(Z).
2. H^0(Γ_0(p), V) = 0 for n ≥ 2. HACS `level_n` prints h0 = 0 in all 270 (cell, l) runs [HACS].
3. H^1(SL_2(Z), V) and H^1(Γ_0(p), V) are **free** over Z_(l).
   - The l-torsion is a quotient of H^0(Γ, V/l), which is 0: Sym^n F_l is irreducible and nontrivial for 0 < n < l, and Γ_0(p) ↠ SL_2(F_l).
   - [indep] confirms this: the relation module is a direct summand mod l^E (unit pivots throughout).
   - [HACS] confirms the ranks: rank_Z (Task-0 records) = dim_{F_l} (`level_n`) = our rank, in every cell.
4. Hence:
   - **H^0(SL_2(Z[1/p]),V) = 0**;
   - **H^1(SL_2(Z[1/p]),V) = ker α = 0**, since α has 2·rk H^1(SL_2(Z),V) nonzero elementary divisors, all < l^E, in every cell;
   - **H^2(SL_2(Z[1/p]),V) = coker α**;
   - **H^q = 0 for q ≥ 3**.

## 2. The anchors

### p = 3, k = 12, l = 17

**(a) Cohomology.**

- H^1(SL_2(Z[1/3]), V) = 0.
- H^2 = Z_(17)^2, the 3-new part. T_q on it has char_Z = (X − a_q(g))^2, where g is the 3-new eigenform with T_2 = 78, T_5 = −5370, T_7 = −27760, T_11 = 637836, T_13 = 766214 [derived from HACS char_Z].
- Over all l > 12, l ≠ 3, the **only torsion of H^2 is Z/13**. It is Eisenstein: T_q acts on it as 1+q^{11} mod 13 for q = 2, 5, 7, 11, 13 [indep].

**(b) coker α.** It is torsion-free at 17 (all six elementary divisors of α are units) [indep], as Ihara predicts.

**(c) coker(α\*α) ⊗ Z_(17).** It is **(Z/17)^2**, supported at m_Δ = (17, T_q − τ(q)): on its kernel T_2 ≡ 10 ≡ −24, T_5 ≡ 2 ≡ 4830, T_7 ≡ 1, T_11 ≡ 13, T_13 ≡ 7. That is one copy for each sign ±.

- Compare τ(3)^2 − 16·3^{10} = −881280 = −2^7·3^4·5·17, with v_17 = 1 per copy [indep + hand].
- The other divisors of coker(α\*α) at l > 12 are all Eisenstein and of order l: 13, 61 and 73. They come from (1−3^{10})(1−3^{12}) = 2^7·5·7·11^2·13·61·73.
- **Level raising, seen in H^2:** char(T_q | H^2) mod 17 has a_q(Δ) mod 17 as a double root for q = 2, 5, 7, 11, 13 [derived]. So g ≡ Δ mod 17 (78 ≡ −24 mod 17), as in Task 0.

### p = 5, k = 12, l ∈ {29, 131}

**(a) Cohomology.**

- H^1 = 0.
- H^2 = Z_(l)^6 = 2·(dim S_12^{5-new} = 3). T_2 on H^2/tors has char_Z (X − 34)^2 (X^2 + 20X − 5336)^2 [derived from HACS char_Z].
- Over all l > 12, l ≠ 5, the **only torsion of H^2 is Z/13** (Eisenstein, T_q ≡ 1+q^{11} mod 13) [indep].

**(b) coker α.** It is torsion-free at 29 and at 131 [indep].

**(c) coker(α\*α).**

- ⊗Z_(29) = **(Z/29)^2** at m_Δ (kernel: T_2 ≡ 5 ≡ −24 mod 29).
- ⊗Z_(131) = **(Z/131)^2** at m_Δ (T_2 ≡ 107 ≡ −24 mod 131).
- Compare τ(5)^2 − 36·5^{10} = −328233600 = −2^7·3^3·5^2·29·131 [indep + hand].
- The remaining divisors (13, 31, 71, 521, 601) are Eisenstein and of order l.
- Level raising seen in H^2: a_q(Δ) mod l is a double root of char(T_q | H^2) at l = 29 and l = 131 for q = 2, 3, 7, 11, 13 [derived].

## 3. The grid p ∈ {3,5,7,11,13}, k = 4..14 (done in full; table `data/grid_table.md`)

In all 30 cells:

- rk H^2 = rk H^1(Γ_0(p)) − 2 rk H^1(SL_2(Z)) = 2 dim S_k(Γ_0(p))^{p-new}. The dimension formula was checked in every cell.
- H^0 = H^1 = 0.

**(b) Torsion of H^2 = torsion of coker α, over all l > k, l ≠ p.** Every torsion summand found is a **single Z/l, with l = k + 1** (when k+1 is a prime ≠ p), and it is **Eisenstein**: T_q ≡ 1 + q^{k−1} mod l for all q tested. Torsion occurs at:

| (p, k) | torsion |
|---|---|
| (3,4), (7,4), (11,4), (13,4) | Z/5 |
| (3,6), (5,6), (11,6), (13,6) | Z/7 |
| (3,10), (5,10), (7,10), (13,10) | Z/11 |
| (3,12), (5,12), (7,12), (11,12) | Z/13 |

- In every other (cell, l) it is 0.
- In particular there is **no torsion at any cuspidal congruence prime** (17 at p=3, 29 and 131 at p=5, 1051 at p=7, 233 and 34267 at p=11, 31, 191 and 5323 at p=13), as Ihara predicts.
- Nor is there torsion at the other Eisenstein primes l | (1−p^{k−2})(1−p^k) with l ≠ k+1.

That "l = k+1" is the only torsion prime is an **observation** on this grid (and on the extension below), not a theorem. Note that l = k+1 is exactly the case p^k ≡ 1 mod l for every p ≠ l (Fermat), and l | denominator of B_k.

**(c) coker(α\*α), per maximal ideal.**

- **Cuspidal part.** Only k = 12 has level-1 cusp forms in the range 4..14. There, at every l > 12, l ≠ p:

  coker(α\*α)_{m_Δ} = (Z/l^{v})^2 with v = v_l(τ(p)^2 − (p+1)^2 p^{10}), one copy per sign.

  | p | τ(p)^2 − (p+1)^2 p^{10} |
  |---|---|
  | 3 | −2^7·3^4·5·17 |
  | 5 | −2^7·3^3·5^2·29·131 |
  | 7 | −2^9·3^3·5^2·7^2·1051 |
  | 11 | −2^7·3^3·5^3·233·34267 |
  | 13 | −2^7·3^3·5·7^2·31·191·5323 |

  Table `data/cusp_compare.md`. Level raising is confirmed in H^2 for each of these l (`data/levelraise_check.json`).
- **Eisenstein part.** coker(α\*α)_{m_Eis} has length v_l((1−p^{k−2})(1−p^k)) at every l > k, l ≠ p. It is cyclic except in two places:
  - (p,k,l) = (13,4,7) and (13,6,7) give (Z/7)^2. Here l | p+1 and l | 1+p^{k−1}, so both blocks of the 2×2 matrix vanish mod l.
  - (3,10,11), (7,4,5) and (11,4,5) give Z/l^2.
- The identity Σ(valuations) = 2·v_l(cusp norm) + v_l(Eisenstein factor) holds at every (cell, l) [derived].

**(d) Hecke.** T_q (q ≤ 13, q ≠ p) on every term:

- H^1(SL_2(Z),V): exact char poly [indep = HACS char_Z, 180 comparisons].
- H^1(Γ_0(p),V): char_Z from HACS [HACS], and our own char mod l [indep]. Our char mod l was compared with 1327 polynomials from fresh `level_n` runs and with 545 Task-0 char_Z reduced mod l: 0 mismatches.
- H^2/torsion: char_Z(T_q | H^1(Γ_0(p))) / char_Z(T_q | H^1(SL_2(Z)))^2. The division is exact everywhere (table `data/hecke_H2.md`).
- H^2 torsion: Eisenstein, as above.
- H^0 = H^1 = 0.

## 4. Extension beyond the requested range (k = 16..24, same p; `data/grid_table_ext.md`)

This was cheap, so it was done. It is computed in the same way and cross-checked against fresh HACS `level_n` runs, but it has no Task-0 char_Z.

- The torsion of H^2 is again only Z/(k+1) for k+1 ∈ {17, 19, 23} prime (≠ p), and Eisenstein.
- coker(α\*α) at cuspidal l again matches v_l(N(a_p(f)^2 − (p+1)^2 p^{k−2})), now with Galois orbits of level-1 forms at k = 24.
- Two mixed cases: (p,k,l) = (5,24,31) gives (Z/31)^3 and (13,18,19) gives (Z/19)^3. In each, the Eisenstein and a cuspidal maximal ideal meet at the same l, and the kernel mod l is not spanned by T_q-eigenvectors. We did not split these further.
- The extension covers 25 cells: p ∈ {3,5,7,11,13}, k ∈ {16,18,20,22,24}.

## 5. Provenance: what is computed by whom

| Quantity | Source |
|---|---|
| α, its Smith form mod l^E, torsion of coker α, H^1(SL_2(Z[1/p])) = 0 | [indep] (HACS has no degeneracy-map verb: `level_n` and `descent` expose H^1 and T_q, not dg_1/dg_p) |
| α\*α, its exact det, its Smith form, kernel eigen-systems | [indep] |
| ω∘dg_p = T_p, ω'∘dg_1 = p^{-n}T_p, ω∘dg_1 = ω'∘dg_p = p+1 | [indep], two routes; the first two are [C] prop:oldspace(2) |
| rank H^1(Γ_0(p), V), H^0 = 0 | [indep] = [HACS] (`level_n` mod l, 270 runs; Task-0 rank_Z, 125 comparisons) |
| char(T_q) on H^1(Γ_0(p)) mod l | [indep] = [HACS] `level_n` (1327 polynomial comparisons) and = Task-0 char_Z mod l (545) |
| char_Z(T_q) on H^1(SL_2(Z)) | [indep], exact = [HACS] Task-0 char_Z (180 comparisons) |
| char_Z(T_q) on H^2/tors | [derived] from HACS char_Z |
| τ(p)^2 − (p+1)^2 p^{10} factorisations; Eisenstein factor | [derived] (sympy) + [hand] at the anchors |
| Ihara / level raising interpretation | [thm], not proved here |

All cross-checks: `data/xcheck.json`, `checks=2447 mismatches=0` (core grid and extension).

## 6. Not verified / caveats

- The page reference for the amalgam (Serre, *Trees* II.1.4) is yours; we did not check it.
- We did not check that our α\* is the adjoint of α for a particular pairing; it is the transfer to the vertex groups (§0).
- Elementary divisors are exact only below l^E. No divisor reached l^{E−1}; the largest valuation seen in any cell is 2.
- At l with l^2 ≥ 2^25 (that is, l > 5792) the level-p T_q matrices were **not** computed (int64 bound). At those l:
  - the α Smith form and the α\*α divisors are still computed (Python integers);
  - the torsion and kernel eigen-systems are read off the level-1 T_q.
- T_q on H^2 is the MV-induced operator; we did not construct an intrinsic SL_2(Z[1/p]) Hecke algebra.
- "Torsion only at l = k+1" is an observation on p ≤ 13, k ≤ 24, not a proof.
