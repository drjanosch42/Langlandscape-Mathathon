<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changes to the HACS seed

This tree started as a **seed** of HACS 0.2.1 (`PROVENANCE.md`: source commit, public release tag, curated
documents, scrubbed files). Upstream files are kept unmodified where possible; every change made here is listed below,
newest first, with the files it touches and the validation that covers it.

| Date | Change | Files | Covered by |
|---|---|---|---|
| 2026-11-14 | seed extracted (no change to upstream files beyond the documented scrub of owner-machine paths) | all | `PROVENANCE.md` |
| 2026-11-14 | new directory `jl/` (our extension, no upstream file touched): `jl/s03_h1_rerun.py` drives the shipped `hacs` binary (`descent`, `coefficient_ring = Z`) to re-run seed (C3) = S03-H1, writes `code/results/s03/C3_rerun.json` | `jl/s03_h1_rerun.py` | script self-check against `code/results/s03/betti_det.json` (no HACS validation registered) |
| 2026-11-15 | HJ-0 (Lane A): new `jl/README.md` (what lives where, binary build, verb table with smoke status, Q1-Q3 as recorded) and `jl/smoke/hj0_smoke.oc` (every verb of plan section 1.1 once, console only); Python bridge lives outside this tree in `code/python/langlandscape/hacs_bridge/` | `jl/README.md`, `jl/smoke/hj0_smoke.oc` | smoke script exit 0 (no HACS validation registered) |
| 2026-11-15 | planned hooks: **Lane A needs none** (console only; no upstream edit, no new verb, no registered validation). Hooks are a Lane B question (HJ-1ff, Q2/Q3). | none | n/a |
| 2026-11-15 | **Langlandscape JL hook** (WP HJ-6-min): one line `include(cmake/jl/JL.cmake)` after the `cmake/slot27/*.cmake` includes, marked `# Langlandscape JL hook` | `CMakeLists.txt` | build; `--list` |
| 2026-11-15 | **Langlandscape JL hook** (WP HJ-6-min): `void RegisterJL();` declared after `RegisterSlot27HeckeZEisUpChar();` and called after it at the tail of `RegisterAllValidations()` (two lines marked `// Langlandscape JL hook`); the `--list` order of the 294 upstream names is unchanged, the JL names follow | `src/hacs/ValidationRegistry.cpp` | `--list` |
| 2026-11-15 | new: the JL source fragment. Option `OC_ENABLE_JL`, **default ON in this fork** (so the spike is built; plan §3.4 had OFF until HJ-11); OFF compiles `JLOff.cpp` (an empty `RegisterJL()`, `--list` = upstream 294). No switch changes a computed value | `cmake/jl/JL.cmake`, `src/hacs/Registry/JL/JLOff.cpp` | build |
| 2026-11-15 | new: the JL registration fragment `RegisterJL()`: `JLBrandtFreeBlockSpikeValidation` (fast), `JLBrandtFreeBlockRead` (slow) | `src/hacs/Registry/JL/JL.cpp` | `--list` |
| 2026-11-15 | new: the Brandt free-block reader (`langlandscape_brandt/v1` → `FreeBlockZ` + ops; minimal JSON reader, tolerant: unknown fields ignored, nested or flat `F`, string or number entries, aliases; `F_fnv` re-hashed with `freez::MatrixFnv` and compared) and the reads: `LatticeFromFreeZ` → `ReadLocal` on L and on L ⊕ L, plus Lane B's own Smith / `AlgebraClosure` reads over ℤ/ℓ^K | `src/hacs/Registry/JL/JlFreeBlockRead.{h,cpp}` | `JLBrandtFreeBlockSpikeValidation` |
| 2026-11-15 | new: the two validations. `JLBrandtFreeBlockRead` reads **`JL_BRANDT_IN`** (a Langlandscape **read-only input hook, not an emitter**: a file, a directory of `*.json`, or an `index.json`; it writes nothing) and `JL_BRANDT_ELLS` (`ell[:K],…`), `JL_BRANDT_SKIP_PLAIN=1` (skip the ReadLocal on L); unset → `EFFECTIVE JLBrandtFreeBlockRead arm=off`, pass. Output: one `@@JL_READ {json}` line (schema `jl_lattice_read/v1`, tag *computed (HACS ReadLocal on a JL lattice)*) per (D, ℓ, K) | `src/hacs/Registry/JL/JlFreeBlockValidation.cpp` | itself |
| 2026-11-15 | regenerated the CLI manual tables for the two JL names (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`; roster 294 → 296) | `docs/latex/cli_manual/counts.tex`, `docs/latex/cli_manual/validations.tex` | `CliManualCoverageValidation` |
| 2026-11-15 | (m8, HJ-6-min review) the JL names change the tiers: `JLBrandtFreeBlockSpikeValidation` (fast) takes `--all` from **246 → 247**; HJ-6b's `JLBrandtCongruenceSpikeValidation` (fast) takes it to **248**; the two slow reads are only in `--all-full` / by name. `--list` 294 → 296 (HJ-6-min) → 298 (HJ-6b) | `src/hacs/Registry/JL/JL.cpp` | `--list`, `CliManualCoverageValidation` |
| 2026-11-15 | new (WP HJ-6b): exact integral congruence modules of a Brandt lattice at any k: theta = sum c_p T_p with squarefree charpoly_Q (`CharpolyZ`, Faddeev-LeVerrier), orbits = `nf::factor_monic_over_z(chi_theta)`, L_i = ker_Z f_i(theta), L_i^c = ker_Z (chi/f_i)(theta), C_i = L / (L_i (+) L_i^c) by an own exact BigInt Smith form; the index of Z[T_p : p in ops] in its saturation in End_Z(L); T_p on L_i (charpoly, the GL_2 comparison key); at k = 2 the ring congruence module (T_i × T_i^c)/T of T = Z[T_p : p in ops] (lattice-independent); the Gram on L_i of sum x_c y_c / w_c, w_c = abs(Gamma_c)/2, and the self-adjointness check; orders factored by trial division < 2^20 + Miller-Rabin on the cofactor | `src/hacs/Registry/JL/JlCongruence.{h,cpp}` | `JLBrandtCongruenceSpikeValidation` |
| 2026-11-15 | new (WP HJ-6b): `JLBrandtCongruenceSpikeValidation` (fast; inline B_11 k = 2: C_eis = C_cusp = Z/5, Gram dets 5/6 and 5, kernels on fixed inputs) and `JLBrandtCongruenceRead` (slow; the same read-only `JL_BRANDT_IN` hook and reader as `JLBrandtFreeBlockRead`; one `@@JL_CONG {json}` line, schema `jl_congruence/v1`, tag *computed (HACS-native JL module)*, per (cell, orbit); Mazur check at k = 2 up to 2, 3) | `src/hacs/Registry/JL/JlCongruenceValidation.cpp`, `src/hacs/Registry/JL/JL.cpp`, `cmake/jl/JL.cmake` | itself |
| 2026-11-15 | regenerated the CLI manual tables for the two HJ-6b names (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`; roster 296 → 298) | `docs/latex/cli_manual/counts.tex`, `docs/latex/cli_manual/validations.tex` | `CliManualCoverageValidation` |
| 2026-11-15 | HJ-6b small fixes to the HJ-6-min reader (review m1, m2, m4; coordinator): (m1) the JSON parser catches `std::exception` (a bad `\u` escape threw `invalid_argument` past it) and `JLBrandtFreeBlockRead` catches a throwing parse per file (counted as an exception, run continues); (m2) `JL_BRANDT_ELLS` tokens must be `ell[:K]` with ell prime ≥ 2, 1 ≤ K ≤ 64, else `FAIL` by name (ell = 1 looped); (m4) the int64 → uint32 narrowings of D, M, k, n, N, ops, rank and D·M are `ENGINE_CHECK`ed; new `JL_BRANDT_SMALL_ELLS=1` (read-only switch) adds ell = 2, 3 to the default list when they divide num((N−1)/12), flagged `"small_ell":true` and excluded from the Mazur tally (R3); the reader accepts schema `langlandscape_brandt/v1` and `/v2` (v2's `canonical`, `order_ties` ignored); the spike check "v2 rejected" became "v2 accepted, v3 rejected" | `src/hacs/Registry/JL/JlFreeBlockRead.cpp`, `src/hacs/Registry/JL/JlFreeBlockValidation.cpp` | `JLBrandtFreeBlockSpikeValidation` |
| 2026-11-15 | HJ-1 + HJ-2 (Lane B): native quaternion core `hacs_jl` (definite B_D, lattices/orders, left-ideal class sets with `qf_theta` bucketing, weight-2 Brandt T_p), standalone self-test and the `jl_brandt2_dump` writer of `langlandscape_brandt/v2` (binding canonical class order). **Not linked into `hacs`** (not in `cmake/jl/JL.cmake`); built by a direct g++ compile (`quat/README.md`). No upstream file touched | `src/hacs/Registry/JL/quat/**` | `quat_selftest` 8084 checks / 0 failing; dump = Lane A v2 records 14/14 `F_fnv` |
| 2026-11-15 | HJ-7a (Lane C): native tree quotients BG(U, q) of B_D (`Tree.{h,cpp}`: vertices = X_B(U), edges = X_B(U_0(q)U), stabilisers, s_0/s_1 with transport elements; levels O^x, U_0(N0), U_1(N1)), the weight-2 maps (d = (-s_{0*}, s_{1*}), s_j^*, s_{j*}, T_q, alpha alpha^dagger weighted/unweighted, cycle lattice, Phi^comb by exact Smith form, the Ihara map (s_0^*, -s_1^*)), `tests/tree_selftest.cpp`, `tools/jl_tree_dump.cpp`. Exact integer algebra on `nf::BigInt` (own small `zlin`, since `JlCongruence`'s helpers are not separable from their HACS includes). **Not linked into `hacs`**; standalone g++ build (`quat/README.md`). No upstream file touched | `src/hacs/Registry/JL/quat/{Tree.h,Tree.cpp,tests/tree_selftest.cpp,tools/jl_tree_dump.cpp,README.md,SOURCES.txt}` | `tree_selftest` 702/0; s02/s03 reference cells 288/288 matched (`code/results/laneC/hj7_tree_w2.json`) |
| 2026-11-15 | HJ-7b (Lane C): weight-k two-term complexes on BG(U, q) (`TreeK.{h,cpp}`: local frames at p, transports u_0/u_1 from `EdgeMove`, `CoeffModel` = Sym^n or the Shapiro module, homological/cohomological d, coboundary, Smith mod p^m) and `tools/jl_tree_k.cpp` (H_Vk / T6 cross-check suites, BrandtSym T_q cross-check, the quaternionic Ihara cokernel torsion, W_D from HJ-4a's `BrandtSym::Pi`). Also: `idempotent_mod` random search for large l and the Hensel cap fixed (`Tree.cpp`). **Not linked into `hacs`** | `src/hacs/Registry/JL/quat/{TreeK.h,TreeK.cpp,tools/jl_tree_k.cpp,Tree.cpp,README.md,SOURCES.txt}` | H_Vk 270/270 and T6 40/40 cells; BrandtSym charpoly(T_q) 190/190; `code/results/laneC/hj7_ihara_k.json` |
| 2026-11-15 | HJ-9 (Lane C): `Ordinary.{h,cpp}` (U_p, U'_p at the level prime on HJ-3's Level model; ordinary projector mod p^m; ranks over Z/p^m[Delta_s], direct and by Delta-coinvariants; <p>_M) and `tools/jl_hj9.cpp`. Level.* untouched. **Not linked into `hacs`** | `src/hacs/Registry/JL/quat/{Ordinary.h,Ordinary.cpp,tools/jl_hj9.cpp,README.md,SOURCES.txt}` | s04 T3 (s<=3), H6, H7: 7/7 cells, 215/215 fields; rk_Delta e = 1 for s = 1..5 (`code/results/laneC/hj9_lambda.json`) |
| 2026-11-15 | HJ-4a (Lane C): the integral Sym^n Brandt module at level O^× (`BrandtSym`): ρ_n in symn.py's splitting ([C] def:rhon column convention), the intrinsic lattice Λ_c = N_c^{-n/2}·span{Q_{x_1}⋯Q_{x_{n/2}} : x_i ∈ (O_r(I_c)^0)^#} (= the stage-01 seed lattice at every p ∤ D), T_ℓ, Π_p, Π_D = W_D (unnormalised, Π_D² = D^n), pairings with weights w_x and \|Γ_x\|; exact `nf::BigInt`/`BigRational` (NumberField used read-only, no `__int128` added there). Standalone self-test and the `jl_brandtsym_dump` writer (`langlandscape_brandt/v2`, any k, optional Π and Gram). **Not linked into `hacs`**. No upstream file touched | `src/hacs/Registry/JL/quat/BrandtSym.{h,cpp}`, `quat/tests/{brandtsym_selftest.cpp,JsonMin.h}`, `quat/tools/jl_brandtsym_dump.cpp` | `brandtsym_selftest` 665 / 0; symn.json 66/66; pi_sign.json 8/8; PARI newspace 374/374 operators |
| 2026-11-15 | HJ-3 (Lane C): level structures (`Level`): X_B(U) for U = U_1(N1) ∩ U_0(N0) (composite N1, N0), projections, the U_0(q)U correspondence s0/s1, the p-tower S_s (B_3, p = 5 to s = 4, \|S_4\| = 31 250) with π_{s+1,s} and diamonds; reuses `Tree.h` (class_units, find_mu, idempotent_mod), `Tree.cpp` untouched. HJ-4a audit fixes m1 (repo root, `tests/RepoRoot.h`), m2 (seed-lattice determinant test), m5 (wording). Standalone; not linked into `hacs` | `src/hacs/Registry/JL/quat/Level.{h,cpp}`, `quat/tests/{level_selftest.cpp,RepoRoot.h}` | `level_selftest` 569 / 0: levels.json, validation.json 240/240, = build_tree 240/240; `brandtsym_selftest` 715 / 0 |
| 2026-11-15 | HJ-4b (Lane C): the Sym^n Brandt module at level U_1(N1) ∩ U_0(N0) (`BrandtLevel`) on `Level` × `BrandtSym`: T_ℓ, U_ℓ (classical, Σ_j F(x ι⁻¹[[ℓ,j],[0,1]]), no p^{k/2−1}), U'_p, ⟨d⟩ (adelic), Π_p, W_ℓ, pullback / trace / degeneracy s1^*, pairing; Eichler level O_0(q) API for HJ-7b. `Level`: `locate_unit`, `reduce_point`. Even k only (odd k: no ℚ-form). Standalone; not linked into `hacs` | `src/hacs/Registry/JL/quat/BrandtLevel.{h,cpp}`, `quat/Level.{h,cpp}`, `quat/tests/brandtlevel_selftest.cpp` | `brandtlevel_selftest` 476 / 0 (up.json by permutation, pi_sign, commutation, adjoints); PARI at U_0(M) 249/249 operators |
| 2026-11-15 | INT (Lane C): the native quaternion core is linked into `hacs` under `OC_ENABLE_JL`: `Registry/JL/quat/{Quat,Lattice,Order,ClassSet,Brandt2,BrandtSym,Tree,Level,BrandtLevel}.cpp` (only what the validations need: no TreeK, tools or tests; NumberField BigInt/BigRational are already in the binary, no duplicate symbols) | `cmake/jl/JL.cmake` | build `-DOC_ENABLE_CUDA=OFF` RelWithDebInfo `-j12`, 228 s, 0 warnings in `Registry/JL` |
| 2026-11-15 | INT (Lane C): five fast validations with frozen inline values (no file, no env var): `JLQuatCoreValidation` (HJ-1/2: (a,b), h, \|Γ_x\|, mass for 7 D; B_11 T_p), `JLBrandtSymValidation` (symn.json cells, Π_D² = D^n, self-adjointness), `JLLevelValidation` (\|S_s\| = 2, 50, 1250; s02 cells with fibre sums), `JLTreeW2Validation` (B_11, q = 2: coker αα†\|Cusp = ℤ/5, Φ^comb = ℤ/5), `JLIharaKValidation` (5 cells of hj7_ihara_k.json via BrandtLevel). **`--all` 248 → 253**, `--list` 298 → 303 (the upstream 294 in order, then the 9 JL names) | `src/hacs/Registry/JL/JlQuatValidation.cpp`, `src/hacs/Registry/JL/JL.cpp` | each new validation PASS (< 0.1 s each), the 4 existing JL validations PASS, `GOLDEN_STRICT=1 GoldenRegressionValidation` PASS, `LicenceGuardValidation` PASS |
| 2026-11-15 | regenerated the CLI manual tables for the five INT names (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`; roster 298 → 303, `\CMNumAll` 248 → 253) | `docs/latex/cli_manual/counts.tex`, `docs/latex/cli_manual/validations.tex` | `CliManualCoverageValidation` PASS |

### Deviations — Lane C (2026-11-15)

Collected from the Lane C WP notes (`plan/hacs/outbox/20261115T*_{HJ-3,HJ-4a,HJ-4b,HJ-7a,HJ-7b,HJ-9,INT}*.md`), reviews and
audits (`20261115_{HJ3,HJ7a,HJ7b,HJ9,INT}_review.md`, `20261115_HJ4{a,b}_audit.md`); every review/audit verdict was PASS with
0 critical / 0 major findings, the minors were folded in.

- **Process.** Relaxed Mathathon protocol (Fabian Q3): no contract text, no refereed [C] line; status words computed /
  checked / cited / expected only. Targeted validation per WP; one full battery at closure (below).
- **HJ-4a merged ahead of its audit** (so HJ-7b could build on it); the HJ-12a Fable audit then ran on the merged state
  (PASS, 7 minor, folded in with HJ-3). HJ-4b likewise merged before its U_p re-audit (PASS, 6 minor, folded in).
- **Two `rm` uses before the no-delete rule** (worker A, ~06:30Z): the regenerated-records directory
  `/home/janosch/data/hacs-build/laneC/hj34/out2` (build output outside git) and an untracked, dirty
  `code/results/laneC/hj4_congruence.json` (regenerated from a clean tree). Nothing tracked was deleted.
- **P¹(ℤ/M) indexing (HJ-3).** U₀ lines are canonical lexicographic representatives of e·I_c/M·I_c (levels.py / Tree.cpp),
  not HACS's `[C] def:cosetrepsN` (`Hecke/HeckeCosetTables`) as the plan asked. Only basis-independent data are compared;
  cell-by-cell alignment with HACS's level-N coset tables is open.
- **Odd k refused (HJ-4a/b).** For odd n there is no ℚ-form of Sym^n on the ramified B (the module is a vector space over a
  splitting field), so `BrandtSym` gives rank 0 at level O^× (−1 acts by −1) and `BrandtLevel` throws for odd n. S_k(Γ₁(N)) at odd k is not covered.
- **The lattice (HJ-4a).** Our intrinsic Λ_c replaces Lane B's Hecke-stable hull (`brandt_export.py`); k > 2 F matrices are
  therefore not entry-comparable with Lane B's records (compare by char-poly). At p | D it is the stated choice (O⁰)^#.
- **Coinvariant method (HJ-9).** At s = 4, 5 the full e on ℤ/5³[S_s] is not formed; rk_{Δ_s} e uses the exact coinvariant
  route (Δ_s free ⇒ eM free), and rk_Δ eH₁ at s ≥ 4 comes from the exact sequence / Ribet identity with surjectivity
  checked by Nakayama, not from a direct restriction to H₁.
- **Interim ρ_n in TreeK (HJ-7b).** TreeK uses its own local model at p; it is cross-checked against BrandtSym (rank 210/210,
  char T_q 190/190) and, for the exact Ihara cokernel, by the independent BrandtLevel route (210/210 exact).
- **Torsion scan (HJ-7b)** covers 5 ≤ ℓ ≤ 2000, ℓ ∤ 6Dq; superseded for the 210 cells by the exact Smith form over ℤ.
- **Comparisons outside HACS.** All reference comparisons run in Python (GPL, `code/python/langlandscape/hacs_bridge/`),
  PARI only as an independent oracle (mfdim, mfheckemat, mfatkininit); every compared value comes from the C++ code.
- **Own exact linear algebra** (`zlin` in Tree.cpp, `symz` in BrandtSym.cpp) instead of JlCongruence's helpers (not
  linkable standalone) or HACS's mod-ℓ^K routes; `match_permutation` (Brandt2) gained an optional node bound (HJ-4b m3).
- **Not linked into `hacs`:** `TreeK.cpp`, `Ordinary.cpp` and all standalone tools/self-tests (`quat/tools/*`,
  `quat/tests/*`); only the nine library sources of INT are linked. TreeK's results enter the binary only through
  `JLIharaKValidation` (BrandtLevel route, frozen TreeK values).
- **Regenerated CLI manual tables** (`docs/latex/cli_manual/{counts,validations}.tex`, by the generator
  `gen_cli_manual_tables.sh`, not an emitter): the only change outside `Registry/JL` and `cmake/jl`.
- **Not registered as a full HJ-11:** five fast frozen-value validations only (HJ-11-lite); no catalogue entry, no
  `EXPECT_NAMES` update.
- **Closure battery** (impl/hacs-laneC @ 08481d69, `final1`): `--all` 253/253, `GOLDEN_STRICT=1 GoldenRegressionValidation`
  PASS. **Not run:** the four digests, `LABEL_CENSUS`, `--all-full` (slow tier) and the device lane.
- **HJ-8 / HJ-8-def kept out of the `hacs` binary** (option (a), team lead): Python driver `hacs_bridge/jl_defect.py` and the
  standalone tool `quat/tools/jl_eta_def.cpp`; no registered validation. `git diff 08481d69..HEAD` on every hacs-linked path
  (cmake/jl, Registry/JL/*.{cpp,h}, the nine linked quat sources) is empty, so the closure battery covers the final branch.
- **HJ-8 GL₂ side** uses existing HACS binaries via runner.py (`descent(...).module_Z()`, allowed by Q4; `level_n` U_q
  charpolys) plus a p-adic local route (precision p^40, Nakayama-checked) for S_m in place of S06-C4's matrix closure. In 3
  cells ((19,6,7), (19,6,107), (2,20,83)) the U_q sign comes from the sign of a_q of PARI's q-new eigenforms (cypari2, from
  jl_defect.py, not HACS), checked to be HACS-admissible, never from the definite side: GL₂ side "HACS + PARI". 16 census
  blocks ran before sign uniqueness was recorded (sound: `computed` only if all admissible assignments agree).
- **HJ-8 not run / not computed:** T5 at k+(p−1) for (3,18,53)@70, (3,18,61)@78, (13,16,101)@116 on the GL₂ side (HACS
  descent n ≤ 60); (13,16,101)@116 also on the definite side (3 h timeout); 6 census cells at k = 20, q ∈ {41,43,47}
  (time). 120 definite census blocks are "not determined" (118 ramified, 2 unramified with residue degree 2; PARI, cited).
- **HJ-8-def eigenspace route** (`--suite shift`) is a cross-check only; no reported number depends on it. It assumes m
  occurs at weight k+(p−1) (true by the T5 setup, not checked in code).
- **HJ-8 results are splices** of several runs on committed code (T5_hacs: 2 runs; defect_census: 4 runs); every run's
  provenance block is kept.

### Deviations from HACS process (disclosed) — WP HJ-6-min (2026-11-15)

- **No contract text.** The JL reads are in no [C] line; nothing is refereed. HACS's own record words that claim a certificate
  (`c3 = certified`, `…_certified`) are printed as `met(hacs_word)` (`hacs_jl::JlWord`); every value is *computed (HACS ReadLocal on
  a JL lattice)*, never certified.
- **L ⊕ L for the at-root read.** `ReadLocal`'s annihilator is the monic square root of χ/(x−λ)^r (HACS's H¹ carries S_k twice). On a
  Brandt lattice S_k occurs once, so on L itself the at-root read returns `root = inconsistent` (`not_exact`, shown in the spike). The
  spike therefore also reads L ⊕ L (block-diagonal F, `r_eis = 2·e_eis`), where χ = (x−λ)²c² and the read runs with the true cusp
  annihilator c; η_{L⊕L} = η_L ⊕ η_L, so `v_eta` is the ℓ-valuation of the congruence module of L. This is our adapter, not a HACS route.
- **Options.** `d_target = d_algebra` from the record (fallback: rank, noted); `r_eis = e_eis` (fallback 1 at k = 2);
  `full_algebra = false` (T_p, p | N, is not in the read set; ReadLocal does not read the field); `eis_rational = (k = 2)`.
  T_ℓ not in the record → the read set stays P and `t_ell = omitted(not_in_record)` (no ENGINE_CHECK).
- **Not run:** full `--all` / `--all-full`, `GOLDEN_STRICT=1 GoldenRegressionValidation`, the four digests, `LABEL_CENSUS`,
  `ConsoleScriptValidation`; no route bit-identity arm (threads 1 vs N, CPU vs GPU) and no parallel-decomposition statement for the
  JL reads; no `docs/validation-catalogue.md` entry, no `EXPECT_NAMES` / CLAUDE.md roster update; the reads are not timed in a quiet
  window. Run only: `--list`, the spike, `HeckeZExportWordValidation`, `HeckeZLocalValidation`, `CliManualCoverageValidation`,
  `LicenceGuardValidation`, and the data read.
- **Option default** `OC_ENABLE_JL=ON` (plan §3.4 said OFF until HJ-11).
- **JSON reader** is our own minimal one (ServeJson is NOTEBOOK-only), not ConsoleCore's.

### Deviations from HACS process (disclosed) — WP HJ-6b (2026-11-15)

- The HJ-6-min list above applies unchanged (no contract text, `OC_ENABLE_JL=ON`, own JSON reader, and the runs not made).
- **Run only:** `--list`, `JLBrandtCongruenceSpikeValidation`, `JLBrandtCongruenceRead` (on Lane A's 74 records),
  `JLBrandtFreeBlockSpikeValidation`, `JLBrandtFreeBlockRead` (data read, via the collector), `CliManualCoverageValidation`,
  `LicenceGuardValidation`. Not run: `--all`, golden, digests, `LABEL_CENSUS`, `ConsoleScriptValidation`, bit-identity arms.
- **Own exact linear algebra.** HACS's Smith routes (`maps::SmithForm`/`SmithFormBlocked`) are over Z/ell^K; the congruence module
  needs Z. `JlCongruence.cpp` carries a small dense BigInt Smith / HNF / kernel (h ≤ ~40), not an upstream route.
- **Lattice dependence at k > 2.** The records' lattice is `brandt_symn_int/v1` (Z[T]·Z^d, not canonical; format §6): C_i, the
  Hecke-ring index and the T_p-on-L_i charpolys are invariants of that lattice only (GL_h(Z)-invariant, so independent of the
  class order, but not of the choice of lattice).
- **Gram pairing** at k = 2 is sum x_c y_c / w_c, w_c = |Γ_c|/2 (the one making T_p self-adjoint on the function lattice);
  at k > 2 no Gram is computed (the record has no Sym^n pairing).


### Deviations from HACS process (disclosed) — WP HJ-1 + HJ-2 (2026-11-15)

- **Not a registered validation.** The self-test is a standalone executable. It is not in `hacs --list`, and `--all` does not run it.
  Registration as `JlValidation` arms (HJ-11) is open.
- **Not in the HACS build.** The sources are compiled outside CMake. They link only `NumberField/Sha256.cpp`. The tree does
  not contain the binaries.
- **`__int128`** is used in our files under `Registry/JL/quat/`, never in `NumberField` (BIGNTT rule kept).
- **The maximal-order basis is our own** (lower-triangular HNF, e₀ = 1). We compare only basis-independent data with `quat.py`.
- **Default ops of the dump.** The ops are the primes < 50 plus the Eisenstein ℓ. That differs from the format's "all primes ≤ max(13, ℓ_max)", which is available
  as `--ops-mode literal`.
