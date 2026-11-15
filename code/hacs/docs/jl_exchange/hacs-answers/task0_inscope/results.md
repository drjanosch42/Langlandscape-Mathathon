# Task 0: results from the shipped HACS (hacs 0.2.0, commit 5bd70691)

**Tags used throughout.**

- **[HACS-cert]**: a value HACS computed and its record labels `certified`. The record's own word is quoted.
- **[HACS]**: a value HACS computed exactly but did not certify further. Examples: an exact integer char_Z, an exported integer matrix, a mod-l characteristic polynomial.
- **[derived]**: our own exact computation (Python + sympy; scripts in `scripts/`) on the integer data HACS exported. It re-implements no HACS route.
- **[hand]**: checked by hand or with stdlib Python.
- **[thm]**: follows from a cited theorem and is not computed.
- **[not verified]**.

## 0. Model, operators, normalisations (as the binding contract [C] 1.27.0 defines them)

- **Group, model, presentation.** We use Γ = SL_2(Z) acting on the upper half-plane ([C] def:model7, def:model7rel).
  - The generators are T = [[1,1],[0,1]] and S = [[0,-1],[1,0]], together with ST and TS. They satisfy S^2 = (ST)^3 = (TS)^3 = -I.
  - The complex K is a 7-vertex, 11-edge, 5-triangle triangulation of a truncated fundamental domain:
    - v0..v3 lie on the horocycle Im z = Y, with v4 = ζ^2, v5 = ζ (ζ = e^{πi/3}) and v6 = i;
    - the triangles are {v0v1v4}, {v1v2v6}, {v2v3v5}, {v1v4v6}, {v2v5v6}.
  - The relation set Rel has 31 rows, each read as f(σ_lhs) = ρ_n(γ) f(σ_rhs):
    - (v3, v0, T), (v5, v4, T), (e35, e04, T);
    - (v4, v5, S), (v6, v6, S), (e46, e56, S);
    - (v4, v4, ST), (v5, v5, TS);
    - and (σ, σ, -I) for all 23 simplices.
  - H^* is the equivariant cohomology H^*_eq(K, Rel; L). With 6 invertible it equals group cohomology; over Z the integral descent of [C] sec:descent / thm:descentcert is used.
- **Coefficients.** Sym^n of the standard representation in the column convention. Column j of ρ_n(A) holds the coefficients of (ax+cy)^{n-j}(bx+dy)^j ([C] def:rhon). Weight k corresponds to n = k - 2, and only even n is used.
- **Level N, by Shapiro.** M_N = Ind_{Γ_0(N)}^{Γ} V_R, with coset representatives w_j from [C] def:cosetrepsN:
  - j indexes P^1(Z/N), and (c_j, d_j) is the canonical pair;
  - w_j = [[1,0],[k,1]] with k = c_j d_j^{-1} mod N when gcd(d_j, N) = 1;
  - w_j = [[0,-1],[1,k']] when gcd(c_j, N) = 1;
  - mixed classes occur only for composite N.

  The level-N model is [C] def:levelNmodel. H^1(Γ_0(N); V) is the cokernel M_N / Rel_N ([C] prop:levelorbit).
- **Hecke operators.**
  - T_p^{(N)} (p ∤ N) and U_p^{(N)} (p | N) are the double coset [Γ_0(N) diag(1,p) Γ_0(N)].
  - They act through the Manin-Merel Heilbronn matrices: H_{N,p} = Σ_{ε ∈ Mer_p} Σ_j E_{j·ε, j} ⊗ ρ_n(adj h_j(ε)), with adj h_j(ε) = w_{j·ε} (adj ε) w_j^{-1} ([C] prop:heilbronn, eq:heilbronn).
  - Equivalently, they act through τ-chain data on the model ([C] def:hecke). [C] prop:heilbronn(2) proves the two agree.
  - **Normalisation:** the classical one.
    - On a normalised eigenform f of weight k, T_p and U_p act by a_p(f) (checked: T_2 = -24 on Δ, 1 + p^{k-1} on Eisenstein).
    - For p | N they have no 1/p factor and no p^{k/2-1} twist.
    - On a p-new form of level N, U_p = a_p = -ε_p p^{k/2-1}, where ε_p is the Atkin-Lehner eigenvalue.
  - **W_p is not implemented in HACS.** Every W_p value below is derived from U_p by that formula [thm].
- **The integral object.**
  - L := H^1(Γ_0(N); Sym^n Z^2)/torsion. It is exported with exact integer matrices F_p of T_p, p ∤ N, as `descent(N,n,P).module_Z()` ([C] prop:torsionhecke, EXPORT-Z step 2). The convention is T_p b_j = Σ_i F_ij b_i.
  - L contains the Eisenstein classes, two for N prime, and both signs (±) of each cusp form.
  - The HeckeZ record `hecke_structure(N,n,"full"|"anemic")` is defined in [C] sec:recordschema item 8, sec:heckeZ and prop:heckeZcong.
- **Congruence module** (as in [C] prop:heckeZcong(3)). For a commutative ring T acting faithfully on L ⊗ Q (semisimple) and two sets A, B of eigen-systems:
  - C_T(A, B) := T / (J_A + J_B), where J_A = Ann_T(V_A).
  - For complementary A and B this is (T_A × T_B)/T.

## 1. The anchor: D = 3, k = 12 (n = 10), l = 17

### 1.1 Cohomology and eigen-systems over Z [HACS]

- H^1(Γ_0(3); Sym^10 Z^2) = Z^8 + Z/2 + Z/4 + (Z/3)^4. The torsion lies at 2 and 3 only.
- char_Z of the Hecke operators on L = Z^8 (from HACS's own Zassenhaus factorisation, verified):

| p | char_Z(T_p on L) | a_p(Δ) = τ(p) | a_p(g) | a_p(g) - τ(p) |
|---|---|---|---|---|
| 2 | (X+24)^4 (X-78)^2 (X-2049)^2 | -24 | 78 | 102 = 2·3·17 |
| 5 | (X+5370)^2 (X-4830)^4 (X-48828126)^2 | 4830 | -5370 | -10200 = -2^3·3·5^2·17 |
| 7 | (X+27760)^2 (X+16744)^4 (X-1977326744)^2 | -16744 | -27760 | -11016 = -2^3·3^4·17 |
| 11 | (X-534612)^4 (X-637836)^2 (X-285311670612)^2 | 534612 | 637836 | 103224 = 2^3·3·11·17·23 |
| 13 | (X+577738)^4 (X-766214)^2 (X-1792160394038)^2 | -577738 | 766214 | 1343952 = 2^4·3^4·17·61 |
| 17 | (X+6905934)^4 (X-3084354)^2 (X-34271896307634)^2 | -6905934 | 3084354 | 9990288 = 2^4·3^2·7·11·17·53 |

Reading the table:

- (X+24)^4: the Δ-old space, two forms Δ(z), Δ(3z), times two signs.
- (X-78)^2: g, the unique newform in S_12^new(Γ_0(3)), times two signs.
- (X-2049)^2: the two Eisenstein classes. The τ values agree with the q-expansion of Δ [hand].
- U_3 on the full record ([HACS-cert], `hecke_structure(3,10)`, `G1.C1.status=certified`, θ = U_3):
  - the cuspidal minimal polynomial is X^3 - 9X^2 + 115911X + 43046721 = (X + 243)(X^2 - 252X + 3^11) [hand];
  - the Eisenstein U_3 eigenvalues are 1 and 3^11.
- So a_3(g) = U_3(g) = -243 = -3^5, and W_3(g) = -a_3/3^5 = **+1** [derived from [thm]].
- On Δ-old, U_3 has roots α, β of X^2 - τ(3)X + 3^11.

### 1.2 Eigenvalues mod 17

| system | T_2 | T_5 | T_7 | T_11 | T_13 | T_17 | U_3 |
|---|---|---|---|---|---|---|---|
| Δ (old, both U_3-roots) | 10 | 2 | 1 | 13 | 7 | 10 | α ≡ 12, β ≡ 2 |
| g (3-new) | 10 | 2 | 1 | 13 | 7 | 10 | -243 ≡ 12 |
| Eisenstein E(z), E(3z) | 9 | 12 | 15 | 13 | 5 | 1 | 1, 3^11 ≡ 7 |

- T_q(Δ) ≡ T_q(g) mod 17 for every q in the table [HACS + hand].
- HACS's mod-17 level-N computation reproduces this exactly ([HACS], `level_n(3,10,17,[2,3,5,7,11,13])`, raw output `data/anchor_mod17_level_n_and_T3.txt`):
  - char(U_3 on H^1(Γ_0(3); Sym^10 F_17)) = (x-1)(x-7)(x-2)^2(x-12)^4;
  - char(T_2) = (x-9)^2 (x-10)^6.

  Both were checked against these factorisations [hand].
- The level-raising number τ(3) + 4·3^5 = 1224 = 2^3·3^2·17 [hand]. Equivalently, X^2 - 252X + 3^11 evaluated at X = -243 is 297432 = 2^3·3^7·17.

### 1.3 The congruence module C_T(3-old, 3-new)

- **Full algebra T (all T_p together with U_3), at l = 17: C_T ⊗ Z_17 = Z/17.**
  - **Lower bound [HACS-cert].** The record generates T ⊗ Z_17: `G2.ell=17.generation.status=certified (saturation)`, `maximal_ideals=certified`, decomposed by θ = U_3. Of its maximal ideals:
    - `m[0]`, residue U_3 ≡ 12, has `local_type: kind=monogenic, rank=2, embdim=1, hilbert=1,1, loewy=2, gorenstein=true`. It contains exactly the Δ-old α-system (U_3 = α ≡ 12) and the g-system (U_3 = -243 ≡ 12).
    - `m[2]` (U_3 ≡ 2, the β-system), `m[1]` (Eisenstein, U_3 ≡ 7) and `m[3]` (Eisenstein, U_3 ≡ 1) are étale of rank 1.
  - **Upper bound.** T_{m[0]} sits inside Z_17 × Z_17 = T_α × T_g and contains Z_17[U_3] = {(a, b) : a ≡ b mod 17^{v}}, where v = v_17(α + 243) = v_17(297432) = 1 (because β ≢ -243 mod 17) [hand]. So [Z_17^2 : T_m] divides 17. Since T_m is local, the index is exactly 17.
  - Hence T_m = Z_17 ×_{F_17} Z_17 and C_T ⊗ Z_17 = Z/17. The **prediction C_T = F_17 is confirmed.** [HACS-cert + hand]
  - Over Z, at all primes: C_T(full) divides X^2 - 252X + 3^11 at X = -243 = 2^3·3^7·17, and divides the anemic value below [derived]. So the full C_T is **2^a·3^b·17 with a ≤ 1, b ≤ 1**.
  - At 2 and 3 the record reports `open(sandwich)` (no generation certificate), so the 2- and 3-parts are **not determined** [not verified]. Both primes are ≤ k, outside the requested range l > k.
- **Anemic algebra (T_p, p ∤ 3 only).**
  - [derived] For T_P = Z[T_2, T_5, T_7, T_11, T_13, T_17] ⊂ End(L): C(Δ-old, new) = **Z/102 = Z/(2·3·17)**.
  - Since T_P ⊂ T^an, the true anemic C_T divides 102.
  - At 17 it is exactly Z/17. The anemic record (`hecke_structure(3,10,"anemic")`, generation at 17 certified by saturation) has `m[0]` of rank 2, monogenic, Loewy length 2, through the cuspidal component {Δ, g} only, with residue T_2 ≡ 10 = τ(2) = a_2(g) mod 17 [HACS-cert].
  - Including the Eisenstein classes in "old": C(Eis + Δ-old, g) = Z/201042 = 2·3^4·17·73 for T_P [derived]. The 73 is an Eisenstein-g congruence: 73 | 3^12 - 1.
- **Jordan structure mod 17** [HACS-cert local type + hand]. Here L ⊗ F_17 = H^1(Γ_0(3); Sym^10 F_17) (no 17-torsion).
  - On the 3-old sublattice (the saturated Δ-old part, rank 4), U_3 ≡ diag(12, 12, 2, 2): **semisimple**. The roots 12 and 2 are distinct mod 17.
  - On the whole of H^1(Γ_0(3); Sym^10 F_17) (dim 8), U_3 has Jordan type **J_2(12) ⊕ J_2(12) ⊕ J_1(2) ⊕ J_1(2) ⊕ J_1(1) ⊕ J_1(7)**. The reason:
    - L_{m[0]} is free over T_{m[0]} (record: `support=free`) of rank 2 (two signs);
    - T_{m[0]}/17 = F_17[ε]/ε^2, and U_3 - 12 maps to a nonzero multiple of ε, because U_3 - 12 ∉ 17 T_m: (α - 12)/17 ≢ -255/17 mod 17, as v_17(α + 243) = 1.
  - The old-new gluing is exactly what makes U_3 non-semisimple mod 17.
- **T_3 on the level-1 side** [HACS], `hecke(H,3)` on H^1(SL_2(Z); Sym^10 F_17), dim 3:
  - the matrix in HACS's basis is [[8,0,0],[0,14,0],[5,0,14]];
  - eigenvalues 1 + 3^11 ≡ 8 and τ(3) = 252 ≡ 14 (twice);
  - rank(T_3 - 14) = 1, so T_3 is **semisimple**: diag(8, 14, 14).

## 2. The grid: D in {3,5,7,11,13}, k = 4..14 even, d | D

All 30 cells come from HACS's exact integer T_p matrices (P = the first six primes from {2,...,19} not dividing D); the full table is
`data/grid_table.md` (machine-readable: `data/congruence_modules.json`). How to read it:

- **Upper bounds.**
  - C(·,·) is computed for T_P = Z[T_p : p ∈ P], a subring of the anemic Hecke algebra T^an. It is therefore a **multiple** of the true anemic congruence module, prime by prime [derived].
  - By support, it also bounds the primes of the full-algebra module (T_p together with U_D): a maximal ideal of T^full containing both parts restricts to one of T^an.
  - It equals the true value wherever T_P ⊗ Z_l = T^an ⊗ Z_l. HACS certifies generation for its own operator set only, so this equality is not claimed.
- **Old cusp forms.** For k ≤ 14 the level-1 cusp space is nonzero only at k = 12 (Δ). So **the old-versus-new cuspidal question exists only at k = 12**; at the other weights "old" means the two Eisenstein classes.
- **Cross-check of our lattice code.** Our C(Eis, cusp) agrees with HACS's certified Eisenstein C_T wherever the record certifies an exact value:
  - (5,4) Z/13, (5,6) Z/31, (11,4) Z/61, (11,6) Z/(5·19·37), (11,8) Z/(61·7321), (11,12) Z/(19·37·61·691·1117);
  - and it lies within the record's upper bound everywhere else [HACS-cert vs derived].

**k = 12, cuspidal 3-old-versus-new (the Task-0 question), at primes l > 12 with l ∤ D:**

| D | C(Δ-old, new) for T_P [derived] | l > 12, l ∤ D | lower bound: anemic record [HACS-cert] | full record (with U_D) [HACS-cert] | conclusion |
|---|---|---|---|---|---|
| 3 | Z/(2·3·17) | 17 | m of rank 2, monogenic, through Δ and g | the U_3 root 12 (≡ -3^5) shares a rank-2 m with g; root 2 étale | **Z/17** (anemic and full) |
| 5 | Z/(2^2·5·29·131) | 29, 131 | rank-2 monogenic m at both | at 29: U_5 root 22 in a rank-2 m (root 23 étale); at 131: root 19 in a rank-2 m (root 95 étale) | **Z/29 × Z/131** (anemic and full) |
| 7 | Z/(2^2·3·5·7·1051) | 1051 | rank-2 monogenic m | U_7 root 9 in a rank-2 m (root 63 étale) | **Z/1051** (anemic and full) |
| 11 | Z/(2·5^2·233·34267) | 233, 34267 | rank-2 monogenic m at both | full record: `C1=open(cap)`, no θ, no maximal ideals: **not read** | anemic **Z/233 × Z/34267**; full: upper bound only, same primes |
| 13 | Z/(2^2·3·7·31·191·5323) | 31, 191, 5323 | rank-2 monogenic m at all three | full record `C1=open(cap)`: **not read** | anemic **Z/31 × Z/191 × Z/5323**; full: upper bound only |

- Each l-part is exact as follows: the upper bound has l-exponent 1, and the lower bound is a certified rank-2 local m through Δ and a new system.
- All of these primes are the level-raising primes, i.e. the l > 12 dividing τ(D)^2 - D^10(D+1)^2 [hand]:
  - τ(3) + 4·3^5 = 2^3·3^2·17;
  - τ(5) - 6·5^5 = -2^5·3·5·29, and τ(5) + 6·5^5 = 2^2·3^2·5·131;
  - τ(7) + 8·7^5 = 2^4·7·1051;
  - τ(11) - 12·11^5 = -2^4·3·5^3·233, and τ(11) + 12·11^5 = 2^3·3^2·34267;
  - τ(13) - 14·13^5 = -2^5·3^3·5·7·191, and τ(13) + 14·13^5 = 2^2·7·31·5323 [hand].

  This is consistent with Ribet's level-raising theorem [thm].
- The full-algebra rows use the record's θ: U_5 + T_7 at D = 5 and U_7 + T_5 at D = 7.
- The full-algebra exponent is ≤ 1 because it divides the anemic exponent [derived].
- The 2-, 3-, 5- and 7-parts listed (l ≤ k or l | D) are upper bounds only [not verified].

For k ≠ 12 the table gives C(Eis, new). Its l > k, l ∤ D primes are Eisenstein-newform congruences (for example 13 at (3, 6) and 41 at (3, 8)).

## 3. Task 0(ii): ordinarity and families (`data/ordinary_family.json`, script `scripts/ordinary_family.py`)

- **p-ordinarity** [HACS char_Z + hand]:

| p | τ(p) mod p | Δ ordinary? | a_p(g) | a_p(g) mod p | g ordinary? |
|---|---|---|---|---|---|
| 5 | 0 (4830 = 2·3·5·7·23) | **no** | -5370 | 0 | **no** |
| 7 | 0 (-16744 = -2^3·7·13·23) | **no** | -27760 | 2 | yes |
| 11 | 1 | yes | 637836 | 1 | yes |
| 13 | 8 | yes | 766214 | 7 | yes |

- **Ordinary ranks.**
  - Computed [HACS + derived]: the number of p-adic-unit roots of char_Z(T_p) on H^1(Γ_0(3); Sym^{k-2})/tors, for all even k ≤ 62. These come from HACS's exact factored char_Z (`data/family_charpolys.txt`).
  - Each total splits as (2 Eisenstein) + (old cusp from level 1, counted 2 × 2) + (3-new). Some rows:
    - p = 11, k ≡ 2 mod 10: k = 12, 22, ..., 62 all give **8 = 2 + 4 + 2**.
    - p = 13, k ≡ 0 mod 12: k = 12, 24, ..., 60 give **8 = 2 + 4 + 2**.
    - p = 5, k ≡ 0 mod 4: 2 (Eisenstein only) for every k.
    - p = 7, k ≡ 0 mod 6: 4 = 2 + 0 + 2.
  - **Every residue class is constant across the whole tested range**, as Hida's control theorem predicts [thm]. The full tables are printed by the script.
  - **Level 3p^r.** For k ≥ 3, e·H^1(Γ_0(3p^r)) has the same rank as the T_p-ordinary part at level 3: each ordinary level-3 eigenform has exactly one unit-root p-stabilisation, and p-new forms of weight k ≥ 3 are not ordinary [thm, Hida]. **We did not compute U_p at level 3p^r.** HACS's `level_n` cannot take U_l with l equal to the coefficient prime, and the integral U_p at p | N is exported only through an owner-gated emitter, which we did not use. Over Z_p this stays **not computed**.
- **Does the mod-17 old/new congruence persist along k = 12 + (p-1)j?**
  - **Exact "no" at k = 16, 18, 20, 22** [derived, rigorous].
    - The cells (3, k) for k = 14..24 were computed exactly as in §2, with level-1 old forms taken from HACS's level-1 char_Z (`data/persist/`).
    - In each of these four cells, 17 does not divide C(old cusp, new) for T_P. Hence there is no maximal ideal over 17 shared by the 3-old and 3-new parts, for either the anemic or the full algebra.
    - k = 22 is the p = 11 Hida family through Δ (Δ is 11-ordinary). k = 16 and 20 lie on p = 5, k = 18 on p = 7, where Δ is not ordinary, so there is no Hida family there.
    - **So the 17-part of the congruence module is not constant along the 11-adic family: Z/17 at k = 12, 0 at k = 22.**
  - **At k = 24** (= 12 + 12, on the p = 13 family; also 12 + 2·6 and 12 + 3·4), 17 divides C(old cusp, new) for T_P (17^1) [derived upper bound].
    - The level-raising condition a_3(f)^2 ≡ 16·3^{22} mod 17 holds on the level-1 Galois orbit, which is 2-dimensional over Q [hand, via the resultant].
    - **No certified lower bound was read** at k = 24 [not verified].
  - For k = 32 ... 62 only the necessary level-raising test was run (`ordinary_family.py`, the resultant mod 17 on the level-1 T_3 factors). It holds at every tested k = 24, ..., 60 of the four families except k = 32, where it fails [hand, necessary condition only; a failure is a proof of "no 17-congruence" at that weight].

## 4. What HACS could not reach, or what we did not do

- **The full-algebra C_T over Z.** Old versus new needs U_D over Z. HACS's record writes `G3.C_T[U_D]=not_run` and the record's U_D matrices sit behind an emitter. So the full C_T is settled only at k = 12, D = 3, 5, 7, at the listed l > 12, by the local argument; at D = 11 and 13 (full record `C1=open(cap)`) we have upper bounds only.
- **2- and 3-parts** (and l | D): upper bounds only.
- **W_p**: not implemented; derived from U_p.
- **U_p at level 3p^r over Z_p, and Λ-adic tests at level 3**: not computed. HACS's Hida tools (`hida_tower`, `hida_lambda`, U_l on the level-1 model) are tame level 1 only. Level-1 ordinary ranks can be reproduced with `notebook/examples/pow_ordinary_rank_13.oc` and `hida_tower_13_10.oc`.
- **Our congruence modules are for T_P (5-6 Hecke operators)**, not the full anemic algebra. Exponents are exact only where a certified lower bound meets an upper bound of exponent 1.
