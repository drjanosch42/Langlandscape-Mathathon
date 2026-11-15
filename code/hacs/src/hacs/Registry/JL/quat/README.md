<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception -->

# `hacs_jl` quaternion core (WPs HJ-1, HJ-2; Lane B)

Native C++17 definite quaternion arithmetic, class sets and weight-2 Brandt matrices for B_D (D squarefree,
ω(D) odd), namespace `hacs_jl`. Since WP INT (Lane C) the library sources (not TreeK, tests or tools) are linked into `hacs` via `cmake/jl/JL.cmake`
(`OC_ENABLE_JL`), with five fast validations in `Registry/JL/JlQuatValidation.cpp`. The sources are listed in `SOURCES.txt`. The code is STL-only, uses `__int128`
(so it stays outside `NumberField`), and every overflow-prone operation is checked and throws.

| File | Content |
|---|---|
| `Quat.{h,cpp}` | checked i128 helpers, Hilbert symbols, `find_ab` (the `quat.py` rule, unbounded), `QuatAlgebra` (a,b)_ℚ |
| `Lattice.{h,cpp}` | rank-4 lattices in canonical HNF (plain or modulo a known index), sum, dual, intersection; LLL on the real embedding (\|x\|² = nrd); Fincke–Pohst on the exact Gram matrix |
| `Order.{h,cpp}` | `MaxOrder`: a maximal order by p-saturation of ℤ⟨1,i,j,k⟩ (disc = D² checked); products, conjugates, generic left/right orders, Eichler orders O ∩ O_r(J) |
| `ClassSet.{h,cpp}` | left-ideal classes by ℓ₀-neighbour BFS, `qf_theta` buckets, an exact isomorphism test, \|Γ_x\|, exact mass termination |
| `Brandt2.{h,cpp}` | T_p by neighbours and by theta pairs, the relation checks, `F_fnv`, the permutation matcher, `d_algebra` |
| `Tree.{h,cpp}` | (HJ-7, Lane C) tree quotients BG(U, q) for U = O^x, U_0(N0), U_1(N1); weight-2 maps d, s_j^*, s_{j*}, T_q, alpha alpha^dagger, cycle lattice, Phi^comb (Smith), the Ihara map; exact `zlin` on `nf::BigInt` |
| `TreeK.{h,cpp}` | (HJ-7b) weight-k two-term complexes on BG(U, q) over Z/p^m: local frames at p, transports, `CoeffModel` (Sym^n, Shapiro), d (homological / cohomological traces), coboundary, Smith mod p^m |
| `tools/jl_tree_k.cpp` | HJ-7b suites: s02/H_Vk and s03/T6 cross-check, BrandtSym T_q cross-check, Ihara cokernel torsion, W_D; compared by `hacs_bridge/laneC_hj7k_compare.py` |
| `Ordinary.{h,cpp}` | (HJ-9) U_p and U'_p at the level prime on HJ-3's `LevelSet`, ordinary projector by image stabilisation mod p^m, ranks over Z/p^m[Delta_s] (direct and by Delta-coinvariants) |
| `tools/jl_hj9.cpp` | HJ-9 suites T3 (B_3, q = 2, p = 5; s <= 3 direct, s = 4, 5 coinvariant), H6, H7; compared by `hacs_bridge/laneC_hj9_compare.py` |
| `tests/tree_selftest.cpp` | HJ-7 self-test (B_11 headline; H = Brandt T_q, masses, fibre sums for D <= 53) |
| `tools/jl_tree_dump.cpp` | HJ-7 dump of the s02/s03 reference cells (`langlandscape_tree/v1`); compared by `hacs_bridge/laneC_hj7_compare.py` |
| `Level.{h,cpp}` | (HJ-3, Lane C) X_B(U) for U = U_1(N1) ∩ U_0(N0) (composite levels allowed), projections, the U_0(q)U correspondence (s0, s1), the p-tower S_s with π_{s+1,s} and diamonds; the lattice model of `Tree.cpp` (level data in e·I_c/N·I_c), generalised. Conventions (L1)–(L6) in the header |
| `BrandtLevel.{h,cpp}` | (HJ-4b, Lane C) the Sym^n Brandt module at U_1(N1) ∩ U_0(N0) (Level × BrandtSym): T_ℓ, classical U_ℓ, U'_p, ⟨d⟩, Π_p, W_ℓ, pullback/trace/degeneracy s1^*, pairing; Eichler level O_0(q) = `LevelSpec{1, q}`. Conventions (B1)–(B8) |
| `BrandtSym.{h,cpp}` | (HJ-4a, Lane C) the integral Sym^n Brandt module M_Z = ⊕ Λ_x^{Γ_x} at level O^×: ρ_n, the intrinsic lattice, T_ℓ, Π_p, Π_D = W_D, the pairings; exact (`nf::BigInt`/`BigRational`). All conventions are in the header, (C1)–(C7) |
| `tests/quat_selftest.cpp` | standalone self-test against `code/results/s01` |
| `tests/brandtsym_selftest.cpp`, `tests/JsonMin.h` | HJ-4a self-test against `symn.json`, `pi_sign.json`, `classsets.json`; writes `code/results/laneC/hj4_symn.json` |
| `tools/jl_brandtsym_dump.cpp` | `langlandscape_brandt/v2` records at any k (optional Π and Gram matrices) |
| `tools/jl_brandt2_dump.cpp` | writes `free_block_z` records (`langlandscape_brandt/v1`, format of `$HACS_DATA/laneB/freeblockz-export-format.md`) |

## Conventions
- **Algebra:** B = (a,b)_ℚ, with i² = a, j² = b and ij = −ji = k. (a, b) is chosen by `quat.py`'s rule. It equals the
  `classsets.json` value for all 22 D there. The rule is extended without bound for large D.
- **Basis:** the maximal-order basis is the lower-triangular HNF of O in 1, i, j, k, so e₀ = 1. This is **not** PARI's
  `alginit` basis, which `quat.py` uses. Only basis-independent data are compared: (a, b), disc, h, the \|Γ_x\| multisets,
  the mass, and the Brandt matrices up to class permutation.
- **Ideals:** left O-ideals I ⊂ O. Classes are I ~ Iα. O_r(I) = conj(I)·I / nrd(I).
- **Unit groups:** \|Γ_x\| = \|O_r(I_x)^×\| *including* −1, and w_x = \|Γ_x\|/2. Mass: Σ1/\|Γ_x\| = φ(D)/24 and
  Σ1/w_x = φ(D)/12. For prime D these are (D−1)/24 and (D−1)/12.
- **Brandt matrices:** B[i][j] = #{p-neighbours of I_i in class j}, so row sums are p+1. On the function basis
  b_j = 1_{c_j}, T_p b_j = Σ_i F_ij b_i with F = B (no transpose). The weighted symmetry is \|Γ_j\|F_ij = \|Γ_i\|F_ji.
  Classes are listed in the BFS order of the enumeration.

## Methods
- **Neighbours:** the p+1 neighbours are Iα + pI, with α = v₁ + s·v₂ (s ∈ F_p) and α = v₂. Here (v₁, v₂) is a basis of
  α₀R/pR, and α₀ is an isotropic vector of nrd on R = O_r(I) mod p (Tonelli–Shanks).
- **Isomorphism test (exact):** I ≅ J iff conj(I)J has an element of nrd N_I N_J. This is decided by Fincke–Pohst on
  the LLL-reduced form.
- **`qf_theta`:** the theta prefix r(1..n*) of (J, nrd/N_J), where n* is the first n with cumulative count ≥ K = 48.
  It is an invariant, hence a necessary condition, and is used only as a hash bucket. Once the set is complete, a
  singleton bucket needs no exact test.
- **Representatives:** each one is reduced to J·conj(γ)/N_J, where γ is a shortest vector. This keeps the norms O(√D).
- **Termination:** the BFS stops exactly when Σ 24/\|Γ_x\| = φ(D). It throws if the queue runs out first, or if the
  mass is exceeded.
- **Theta pairs:** B(n)[i][j] = #{x ∈ conj(I_i)I_j : nrd x = n N_i N_j}/\|Γ_j\|, for all n ≤ X at once. This is an
  independent second route.

## Dump tool: class order and schema
- `--order key:v2` (the default) applies the binding canonical order of `langlandscape_brandt/v2`. Classes are sorted
  ascending on (\|Γ_c\|, θ_c), where θ_c = (r(1..20)) is the theta series of the right order O_r(I_c) and
  r(1) = \|Γ_c\|. There is no third key. Tie groups are written to `order_ties` as lists of positions after sorting,
  and θ_c to `class_theta`. `--order enum` keeps the BFS order; it is for debugging only and its output is not v2.
- The schema string is the single constant `kSchema` in `tools/jl_brandt2_dump.cpp`; it is currently `langlandscape_brandt/v2`.
- Default ops: every prime below 50, plus the primes dividing num((q−1)/12). `--ops-mode literal` gives all primes
  ≤ max(13, ℓ_max).
- Comparisons with Python records are made only up to a simultaneous class permutation (`match_permutation`, a
  backtracking search meant for small h), never by `F_fnv`.

## Build and run (no HACS build needed)
```
Q=code/hacs/src/hacs/Registry/JL/quat
g++ -std=c++17 -O2 $Q/tests/quat_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2}.cpp -o quat_selftest
./quat_selftest            # full run (about 4 min); --quick takes about 2 s
g++ -std=c++17 -O2 $Q/tools/jl_brandt2_dump.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2}.cpp \
    code/hacs/src/hacs/NumberField/Sha256.cpp -o jl_brandt2_dump
./jl_brandt2_dump 11 23 1009 --write-index
```

## Tree quotients (HJ-7, Lane C)
Model (lattice form of `tree.py`): a point of class c is level data in e I_c / N I_c (e a fixed rank-1 idempotent of O/N:
a primitive vector mod N1, a line mod N0) plus, for edges, one of the q+1 q-neighbours J of I_c. Gamma_c acts from the
right. s1 moves J = I_{c'} mu / N_{c'} (mu by Fincke-Pohst) and the level data by v -> v conj(mu) / N_c (= v g^{-1},
g = mu/(q N_{c'}), the diamond q included). Every edge orbit is checked to have constant s0, s1.
```
g++ -std=c++17 -O2 $Q/tests/tree_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree}.cpp \
    code/hacs/src/hacs/NumberField/BigInt.cpp -o tree_selftest        # 702 checks, 0.1 s
g++ -std=c++17 -O2 $Q/tools/jl_tree_dump.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree}.cpp \
    code/hacs/src/hacs/NumberField/BigInt.cpp -o jl_tree_dump         # all suites < 1 s, < 1 GB RSS
(cd code/python && python3 -m langlandscape.hacs_bridge.laneC_hj7_compare --binary ./jl_tree_dump)
```
## HJ-4a: Sym^n Brandt module (BrandtSym)
```
Q=code/hacs/src/hacs/Registry/JL/quat; NF=code/hacs/src/hacs/NumberField
g++ -std=c++17 -O2 $Q/tests/brandtsym_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,BrandtSym}.cpp \
    $NF/{BigInt,BigRational,Sha256}.cpp -o brandtsym_selftest
./brandtsym_selftest [--quick] [--write code/results/laneC/hj4_symn.json]     # about 10 s; --quick about 1 s
g++ -std=c++17 -O2 $Q/tools/jl_brandtsym_dump.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,BrandtSym}.cpp \
    $NF/{BigInt,BigRational,Sha256}.cpp -o jl_brandtsym_dump
./jl_brandtsym_dump 11 13 30 --k 2..12 [--ops 2,3,5] [--gram] [--no-pi] [--out DIR] [--write-index]
```
Conventions (BrandtSym.h (C1)–(C7)): symn.py's splitting s and ρ_n ([C] def:rhon column convention); Gross form
Φ(Lα) = ρ_n(α)^{-1}Φ(L); T_ℓ Φ(I_c) = Σ_J ρ_n(conj(δ_J)/N_c) Φ(I_{c'}); Π_p unnormalised (Π_D² = D^n); lattice
Λ_c = N_c^{-n/2}·span{Q_{x_1}⋯Q_{x_{n/2}} : x_i ∈ (O_r(I_c)^0)^#}, intrinsic, and equal to the stage-01 seed lattice
Sym^n(ℤ_p²) at every p ∤ D.

<<<<<<< HEAD
<<<<<<< HEAD
=======
The self-tests find `code/results` through the git top level of the source path or of the current directory
(`tests/RepoRoot.h`): run them from inside the repository, or pass `--results <repo>/code/results/s01`.

## HJ-3: level structures (Level)
```
Q=code/hacs/src/hacs/Registry/JL/quat; NF=code/hacs/src/hacs/NumberField
g++ -std=c++17 -O2 $Q/tests/level_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree,Level}.cpp \
    $NF/{BigInt,Sha256}.cpp -o level_selftest
./level_selftest [--quick] [--write code/results/laneC/hj3_levels.json]      # about 1 s
```
>>>>>>> impl/hacs-laneC
## Weight k on the tree (HJ-7b, Lane C)
Local model at p (TreeK.h): iota_p = right multiplication on e O / p^m (rows); class frames a_c in I_c with
nrd(a_c)/N_c prime to p; u_0 = phi_c(gamma_0), u_1 = iota_p(a_{c'} gamma_1 g a_c^{-1}), g = mu/(q N_{c'}). Built from
the repository root with relative paths (reproducible sha256):
```
g++ -std=c++17 -O2 $Q/tools/jl_tree_k.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,BrandtSym,Tree,TreeK}.cpp \
    $NF/{BigInt,BigRational}.cpp -o jl_tree_k
./jl_tree_k [--suite s02_HVk|s03_T6|brandtsym_xcheck|W_D|ihara]... [--L 2000] [--out FILE]
(cd code/python && python3 -m langlandscape.hacs_bridge.laneC_hj7k_compare --binary ./jl_tree_k [--native FILE])
<<<<<<< HEAD
=======
The self-tests find `code/results` through the git top level of the source path or of the current directory
(`tests/RepoRoot.h`): run them from inside the repository, or pass `--results <repo>/code/results/s01`.

## HJ-3: level structures (Level)
```
Q=code/hacs/src/hacs/Registry/JL/quat; NF=code/hacs/src/hacs/NumberField
g++ -std=c++17 -O2 $Q/tests/level_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree,Level}.cpp \
    $NF/{BigInt,Sha256}.cpp -o level_selftest
./level_selftest [--quick] [--write code/results/laneC/hj3_levels.json]      # about 1 s
>>>>>>> impl/hacs-laneC
=======
>>>>>>> impl/hacs-laneC
```

## Lambda-adic definite side (HJ-9, Lane C)
```
g++ -std=c++17 -O2 $Q/tools/jl_hj9.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree,Level,Ordinary}.cpp $NF/BigInt.cpp -o jl_hj9
./jl_hj9 [--suite T3|H6|H7]... [--smax-coinv 5] [--full-max 3] [--out FILE]   # all: 2.6 min, 3.1 GB (s = 5); via heavy.sh
(cd code/python && python3 -m langlandscape.hacs_bridge.laneC_hj9_compare --binary ./jl_hj9 --native FILE)
```

## HJ-4b: Sym^n Brandt module at level (BrandtLevel)
```
Q=code/hacs/src/hacs/Registry/JL/quat; NF=code/hacs/src/hacs/NumberField
g++ -std=c++17 -O2 $Q/tests/brandtlevel_selftest.cpp $Q/{Quat,Lattice,Order,ClassSet,Brandt2,Tree,Level,BrandtSym,BrandtLevel}.cpp \
    $NF/{BigInt,BigRational,Sha256}.cpp -o brandtlevel_selftest
./brandtlevel_selftest [--quick] [--write code/results/laneC/hj4b_level.json]   # about 4 s
```
Eichler level O_0(q) (e.g. for the weight-k Ihara map):
```cpp
MaxOrder O(D); ClassSet C(O); BrandtSym M(C, k - 2); LevelModel Mo(C, q);
LevelSet Xs(Mo, {1, 1}), Es(Mo, {1, q}); BrandtLevel X(M, Xs), E(M, Es);   // E: cells = O_0(q) classes
ZMat s0 = BrandtLevel::pullback(E, X), s1 = BrandtLevel::degeneracy_s1(E, X, q);  // M(O^x) -> M(O_0(q))
ZMat Uq = E.T(q), Wq = E.W(q), Tl = E.T(ell);  QMat G = E.gram();
```

Independent check of HJ-7b's exact Ihara cokernel through this API: `tools/jl_ihara_xcheck.cpp` (same build set as
`brandtlevel_selftest`); `./jl_ihara_xcheck` writes `code/results/laneC/hj7_ihara_xcheck.json`.
