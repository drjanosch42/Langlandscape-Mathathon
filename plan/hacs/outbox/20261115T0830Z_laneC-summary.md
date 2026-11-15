<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Lane C: the HACS implementation of the definite (quaternionic) side, in one page (final, 2026-11-15)

Code: `code/hacs/src/hacs/Registry/JL/quat/` (namespace `hacs_jl`, C++17, exact `nf::BigInt`/`BigRational`/`__int128`).
Results: `code/results/laneC/`. Notes: `plan/hacs/outbox/20261115T*_{HJ-3,HJ-4a,HJ-4b,HJ-7a,HJ-7b,HJ-8a,HJ-8b,HJ-8-def,HJ-9,INT}*.md`.
Status words: **computed** (our native code produced it), **checked** (it equals an independent reference), **cited**,
**expected**. The word "certified" is not used.

## (a) What exists (definitions in words)

- **Quaternion core and class sets (HJ-1/2, Lane B).**
  - B_D = (a,b)_ℚ, definite, ramified exactly at D (squarefree, ω(D) odd), with a maximal order O.
  - The left-ideal classes come from an ℓ₀-neighbour BFS with an exact isomorphism test, stopped exactly when the mass is
    reached.
  - Γ_x = O_r(I_x)^×, with −1 included.
- **Sym^n Brandt module on the intrinsic lattice (HJ-4a).**
  - The module M_Z = ⊕_x Λ_x^{Γ_x} consists of functions Φ on left ideals with Φ(Lα) = ρ_n(α)⁻¹Φ(L), where ρ_n is
    [C] def:rhon composed with symn.py's splitting B → M₂(ℚ(√a)).
  - The lattice is Λ_x = N(I_x)^{−n/2}·span{Q_{x₁}⋯Q_{x_{n/2}} : x_i ∈ (O_r(I_x)⁰)^#}, built from the quadratic forms
    Q_x(X,Y) = (X,Y)s(x)J(X,Y)ᵀ.
  - It is intrinsic: it does not depend on the class representatives, the class order or the ops.
  - At every p ∤ D, including p = 2 and 3, it is the stage-01 seed lattice Sym^n(ℤ_p²). Only the choice at p | D is ours.
  - Only even k is supported. For odd n, Sym^n has no ℚ-form on the ramified B.
- **Level structures and towers (HJ-3).**
  - X_B(U) for U = U₁(N1) ∩ U₀(N0), with composite levels allowed, as Γ_c-orbits of level data in e·I_c/N·I_c.
  - The data are a primitive vector for U₁ and a line for U₀; e is a rank-1 idempotent of O/N.
  - Further pieces: the projections between levels, the U₀(q)U correspondence (s₀ forgets the q-line; s₁ moves the datum
    to the class of the q-neighbour), and the p-tower S_s = X_B(U₁(p^s)) with the maps π_{s+1,s} and the diamonds.
- **Hecke operators at level (HJ-4b).** All of them act on the Sym^n module at U₁(N1) ∩ U₀(N0), as finite sums
  ρ_n(g)Φ(I_c′, d·g); the level datum moves by the same element g.
  - T_ℓ.
  - U_ℓ for ℓ | N: the **classical** U_p, Σ_j F(x·ι⁻¹[[ℓ,j],[0,1]]), with no p^{k/2−1}. It is the seed's N_{U_p}.
  - U′_p.
  - The adelic diamond ⟨d⟩, which is the classical ⟨d⟩⁻¹.
  - Π_p and Π_D, unnormalised, with Π_D² = D^{k−2}.
  - W_ℓ.
  - The pullback, the trace, and the degeneracy s₁^*.
- **Tree quotient Γ\T and s₀, s₁ (HJ-7a).**
  - BG(U, q) for q ∤ D is the bipartite graph with vertices X_B(U) (two types) and edges X_B(U₀(q)U).
  - s₀ forgets the q-neighbour. s₁ goes to the class of the q-neighbour J = I_c′μ/N_c′.
  - Stabilisers are |Γ| (with −1), and w = |Γ/±1|.
- **Ribet map α and αα† (HJ-7a).**
  - α = d = (−s₀*, s₁*) : ℤ[E] → ℤ[X]².
  - Its adjoint is α†, for ⟨x,x⟩ = w_x and ⟨e,e⟩ = w_e.
  - In the weighted case, αα† = [[(q+1)I, −H′],[−Hᵀ, (q+1)I]].
  - The cuspidal part is the degree-zero sublattice of each type.
- **Φ^comb (HJ-7a).** The cokernel of the cycle lattice X(G) = ker d (saturated) under its weighted Gram, X → X^∨,
  computed by a Smith form. It is computed for BG and for the collapsed two-vertex graph.
- **Weight-k quaternionic Ihara map (HJ-7b; second route via HJ-4b).**
  - ι = (s₀*, −s₁*) : M_Z(O^×; V_k)² → M_Z(O₀(q); V_k), on the intrinsic lattice at vertices and edges (Λ_c^{Γ_e} on edges).
  - Its exact cokernel over ℤ is computed by a BigInt Smith form.
- **W_D (HJ-7b, from HJ-4a).** W_D = Π_D / D^{(k−2)/2}, an integral involution of M_Z that commutes with T_ℓ and is
  self-adjoint for ⟨,⟩_w.
- **Λ-adic U_p on ℤ/p^m[S_s] (HJ-9).**
  - U_p (homological, at the level prime) and U′_p act on ℤ/p^m[S_s], for B₃ with p = 5.
  - The ordinary projector e comes from image stabilisation.
  - Ranks over ℤ/p^m[Δ_s]: directly at s ≤ 3, and by the exact coinvariant route at all s (Δ_s acts freely, so eM is free).

## (b) What is computed, over what range, and checked against what

| WP | Object | Range | Reference / cross-check | Agreement | Status |
|---|---|---|---|---|---|
| HJ-4a | char_ℤ(T_ℓ) on M_Z | D ∈ {2,3,5,7,11,13}, k = 2..12, ℓ ∈ {2,3} | s01/symn.json | 66/66 cells | checked |
| HJ-4a | char_ℤ(T_ℓ), ℓ < 20 | 62 cells of positive rank, including D = 30, 42, 66, 70, 78 | PARI newspace (JL) | 374/374 operators | checked |
| HJ-4a | Π_D eigenspaces and char_ℤ(T_ℓ \| ±) | D ∈ {11,13,17,19}, k ∈ {2,4} | s01/pi_sign.json | 8/8 | checked |
| HJ-4a | lattice independent of the representatives; seed lattice at p ∤ D (determinant test, 10 D, n ≤ 10) | — | proof (WP note §3), self-test H, I | 21/21; all | computed |
| HJ-4a | D = 13, k = 8 congruence | x−10, x²+19x+6 | Lane B (HJ-6b) | 37 in both | checked |
| HJ-3 | mass level changes, towers, trivial stabilisers | 13 level changes, 3 towers, 15 U₁(p) cells | s01/levels.json | all | checked |
| HJ-3 | X, E, masses, fibre sums q+1 (s₀ and s₁) | D ≤ 53, q ≤ 13, O^×/U₀/U₁ (240 cases) | s02/validation.json; HJ-7a build_tree | 240/240; 240/240 | checked |
| HJ-4b | T₂, U₅, U′₅, ⟨2⟩, π_* at k = 2 | B₃, U₁(5^s), s = 1, 2 (relations to s = 3) | s01/up.json (up to one permutation) | match | checked |
| HJ-4b | char(T_ℓ), char(classical U_ℓ) with oldforms | 63 U₀(M) cells, D ≤ 13, k ≤ 6 | PARI | 249/249 operators | checked |
| HJ-4b | commutation, adjoint and sign relations, Eichler relations | 102 level cells; 42 O₀(q) cells | stage-01 lemmas (sign decided on 56/3/19/3 cells) | all | computed |
| HJ-7a | tree quotients, αα†, Φ^comb, H_Vk at k = 2, Mazur | 288 reference cells | s02/{validation,T2,T3,H_Vk}, s03/{T1,T2,T6} | 288/288 cells, 3744/3744 fields | checked |
| HJ-7b | weight-k two-term complexes | 240 H_Vk rows + 36 T6 cells, k ≤ 10 / 14 | twoterm.py, ihara.py | 276/276 | checked |
| HJ-7b | rank M(O;V_k), char(T_q) mod 1000003 | 210 cells | BrandtSym (HJ-4a) | 210/210; 190/190 | checked |
| HJ-7b | exact coker ι over ℤ | D ∈ {2,…,13}, q ≤ 13, q ≠ D, even k ≤ 14: 210 cells | free rank = dim S_k(Γ₀(Dq))^new (PARI); second route via BrandtLevel | 210/210; 210/210 invariant factors exact | checked |
| HJ-7b | W_D | D ≤ 13, even k ≤ 14: 42 cells (38 of positive rank) | PARI mfatkininit traces | 38/38 traces, 42/42 ranks | checked |
| HJ-9 | e, ranks, Ribet identity, U_p/U′_p relations | B₃, p = 5, s ≤ 3; H6, H7 cells | s04/{T3,H6,H7}.json | 7/7 cells, 215/215 fields (168 substantive) | checked |

## (c) New values (headline lines, all *computed*)

- **HJ-7b, the exact quaternionic Ihara cokernel.** For all 210 cells (D ∈ {2,3,5,7,11,13}, q ≤ 13, q ≠ D, even k ≤ 14),
  coker ι ≅ ℤ^r ⊕ torsion, with r = dim S_k(Γ₀(Dq))^new.
  - **Torsion prime to 6Dq** occurs in 68 cells, only at (k, ℓ) ∈ {(8,5), (10,7), (14,5), (14,11)}, always as ℤ/ℓ with
    exponent 1. Each of these has (ℓ+1) | (k−2); that is an observation, not a proof.
  - **No ℓ-torsion for any ℓ > k** (scan 5 ≤ ℓ ≤ 2000, ℓ ∤ 6Dq, and exact over ℤ).
  - 52 cells are torsion-free.
  - Examples, B₁₁ with q = 2:
    - k = 4: ℤ³ ⊕ ℤ/11;
    - k = 8: ℤ⁵ ⊕ (ℤ/2)³ ⊕ ℤ/660;
    - k = 14: ℤ⁹ ⊕ (ℤ/2)² ⊕ (ℤ/4)³ ⊕ (ℤ/8)² ⊕ ℤ/48 ⊕ ℤ/720.
  - The D-parts depend on the lattice choice at D.
  - **Two independent native routes** (TreeK's local frames; BrandtLevel's global lattice) agree on all 210/210 cells,
    exactly.
- **HJ-7b, W_D** as an integral involution in 38 cells (k ≤ 14). For example, D = 11 gives +I at k = 2 and −I at k = 4.
  The traces agree with PARI.
- **HJ-9:** rk_{Δ_s} e ℤ_p[S_s] = 1 for s = 1, 2, 3, 4, 5. It is constant, with |S_5| = 781 250 (|E_5| = 2 343 750), and
  rk_Δ e ℤ[E_s] = 4, rk_Δ e H₁ = 2 at every s. At s ≥ 4 this is by the coinvariant route and the Ribet identity.
- **HJ-3:** |S_4| = 31 250 = 2·25³ (B₃, p = 5), with the mass identity and Δ₄ acting freely.
- **HJ-4a, the intrinsic lattice.** On M_Z, congruence modules (their p-parts) and Gram determinants (up to p-adic units)
  are invariants of the definite side at every p ∤ D, independent of every choice. On it, the HJ-6b congruence 37 at
  D = 13, k = 8 reappears.

## (d) In hacs

- **Five fast validations** with frozen values, registered from `Registry/JL/JL.cpp`: `JLQuatCoreValidation`,
  `JLBrandtSymValidation`, `JLLevelValidation`, `JLTreeW2Validation`, `JLIharaKValidation`. Together with the 4 Lane B
  validations that makes 9 JL names. `--list` gives 303 names.
- **Closure battery** (impl/hacs-laneC @ 08481d69, fresh build final1, sha256 19ab4d06…def9d):
  - `--all`, 4 shards: **253/253**, 0 failed;
  - `GOLDEN_STRICT=1 GoldenRegressionValidation`: tier A 12154 checked, 0 failing; tier B 6231 checked, 0 mismatching;
    PASS.
- **Not run:** the digests, LABEL_CENSUS, `--all-full` and the device lane.
- **Not linked** (standalone tools only): TreeK, Ordinary, the dump and check tools.

## HJ-8: the integral JL defect comparison η_f(q) = 𝔠_q(f)·η^B (all *computed*)

**The objects.**
- **GL₂ side.** η_f(q), 𝔠_q(f) and η_new come from HACS: `descent(q|1, k−2, P).module_Z()` gives the T_ℓ over ℤ at levels q and 1, and `level_n` gives the U_q charpolys. The local ring S_m is then rebuilt by a p-adic local route (precision p^40, checked by Nakayama). This is the Python driver `hacs_bridge/jl_defect.py`.
- **Definite side.** η^B is the congruence invariant at m of the Sym^{k−2} Brandt module of B_{q,∞} on the intrinsic lattice. It is native C++ (`quat/tools/jl_eta_def.cpp`). At weight k+(p−1) it is computed by the ring-theoretic route (a rank-1 m-block gives η^B = 1). Matching between the two sides is by the residual a_ℓ mod p.
- **The U_q sign.** In 3 cells, (19,6,7), (19,6,107) and (2,20,83), the U_q sign comes from the sign of a_q of PARI's q-new eigenforms. That is computed with cypari2, called from our Python driver jl_defect.py, not from HACS. Orbits are matched by the charpolys of T_ℓ. The sign was checked to be among the HACS-admissible assignments, and it is never taken from the definite side. The GL₂ side of these 3 cells is "HACS + PARI".
  - In the 30 blocks where HACS's sign is unique, PARI agrees: 30/30.
  - 16 blocks ran before sign uniqueness was recorded. These count as computed only because every admissible assignment gives the same numbers.

**T5** (7 triples):
- **Weight k:** 7/7 give ord η = ord 𝔠 = 1, ord η_new = 0 and v_p η^B = 0. These equal S06-C6/C4 field by field. η^B native equals η^B Python, 7/7.
- **Weight k+(p−1):**
  - 4 cells satisfy η = 𝔠·η_new = 𝔠·η^B (Thm E). (5,18,23)@40 and (5,16,31)@46 equal S06-C4. (13,18,19)@36 and (13,12,31)@42 are new; S06-C4 could not compute them, and they rest on the local route.
  - Open: (3,18,53)@70 and (3,18,61)@78, because HACS descent requires n ≤ 60; the definite η^B is 1 there. Also (13,16,101)@116, which is open on both sides: n > 60 on the GL₂ side, and a 3 h timeout on the definite side.

**H3** ((q,p,k) = (13,7,4), (13,7,6), (19,5,4), (29,5,4)):
- 9/9 blocks agree.
- 7 of them have residue field F_{p^f} and use the étale route. All 7 were confirmed by the ramified-place check; 0 were relabelled.
- The prediction ord 𝔠 − t_f(q) = 0 holds vacuously (S_k(1) = 0).

**Census.**
- **Bounds:** q prime ≤ 50; k even, 2 ≤ k ≤ 20; p prime, k < p < 200, p ≥ 5, p ≠ q, p ∤ q²−1.
- **Size:** 5869 cells, of which 5538 are trivial on the definite side: χ is squarefree mod p and there is no level raising, so η^B = 1 for every m.
- **Genuine definite congruences, η^B = p:** 5 cells, (q,k,p) = (13,8,37), (17,6,7), (17,8,13), (19,6,7), (19,6,107). On the GL₂ side all 5 agree: rank 2, η_new = 1 for both forms, 𝔠 = 1, η = p.
- **Old-congruent m** (level raising from S_k(1)): 50 cells.
  - 44 were computed on the GL₂ side and all agree: η = 𝔠 = p^t, η_new = 0, ord 𝔠 = t_f(q), η^B = 1.
  - That includes one cell with t = 2: (47,12,17), with η = 𝔠 = 17².
  - **6 were not run** (time): (41,20,113), (41,20,139), (43,20,83), (43,20,199), (47,20,31), (47,20,107).
- **120 definite blocks are not determined.** They are listed one by one in `hj8_def_native.json`. 118 are ramified, and 2 are unramified with residue degree 2, per a PARI check (cited). They are not counted as η^B = 1.
- **No computed block disagrees.**

**Not used for any reported number:** the definite eigenspace route (`--suite shift`), which is a cross-check only. It assumes that m occurs at weight k+(p−1).
