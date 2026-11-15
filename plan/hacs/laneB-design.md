<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# Lane B design note (HJ-B0): the §3.2 interfaces against the seed

Status: design, 2026-11-15. Seed = HACS dev commit `0ea75f73` (`code/hacs/PROVENANCE.md`). All line numbers below were
read in this tree. The data format is `plan/hacs/freeblockz-export-format.md` (v2: v1 plus the required canonical class order, its §1b). This note does not repeat it.
No C++ was written or built for this note.

## 1. Upstream files Lane B touches (complete list)

**One-line hooks.** These are the only hand edits to upstream files. Each is logged in `code/hacs/CHANGES.md`.

| file | edit | position |
|---|---|---|
| `code/hacs/CMakeLists.txt` | `include(cmake/jl/JL.cmake)                     # JL (Langlandscape): one fragment, OC_ENABLE_JL` | new line **after l. 1412**, which is `include(cmake/slot27/HeckeZEisUpChar.cmake)`, the last `cmake/slot27/*` include, and before the blank line / `target_link_libraries(cohomology_app …)`. It sits after the slot-27 block so the K2 fold (`cmake/slot27/*` → `cmake/sources/*`) does not move it |
| `code/hacs/src/hacs/ValidationRegistry.cpp` | declaration `void RegisterJL();                     // JL (Langlandscape): Registry/JL/JL.cpp` | new line **after l. 409** (`void RegisterSlot27HeckeZEisUpChar();`) |
| `code/hacs/src/hacs/ValidationRegistry.cpp` | call `    RegisterJL();` | new line **after l. 1973** (`RegisterSlot27HeckeZEisUpChar();`), the last statement of `RegisterAllValidations()`. The JL names therefore come last in `--list`, and the order of the 294 upstream names does not change |

**Generated, not hand-edited.** `docs/latex/tools/gen_cli_manual_tables.sh <binary>` regenerates these, in the same commit,
or `CliManualCoverageValidation` fails:

| file | what changes |
|---|---|
| `code/hacs/docs/latex/cli_manual/validations.tex` | one `\ocvalidation{<Name>}{<tier>}` row per JL validation |
| `code/hacs/docs/latex/cli_manual/counts.tex` | the validation count macros |

These are "the two generated tables" of plan HJ-B0.

**Also required by the seed's checklist** (`docs/agent-guides/new-validation.md`, items 5–7). These are owner-visible docs.
They are listed here so that the list is complete, and Q2 decides whether we edit them or hand them to the owner:
- `docs/validation-catalogue.md`: one entry per JL validation, in a new `## JL` section at the end;
- `docs/cluster/noctua2/EXPECT_NAMES`: the `--list` count (**absent in the seed**: no `code/hacs/docs/cluster/` in `0ea75f73`; the checklist item does not apply until the file exists);
- the roster figures in `code/hacs/CLAUDE.md` (l. 94, 96: "294 at seed time", "246").

**Only if HJ-5b (console verbs, Q2)** is approved: one call in `src/hacs/Console/Bindings/Bindings.cpp`,
`docs/console/gen_console_md.sh <binary>`, and the [P] console spec. These are not in the HJ-6 spike.

**Never touched:**
- `Registry/Slot27/*` and `cmake/slot27/*` (package-owned, `Registry/Slot27/README.md`);
- `Registry/Slot<S>.cpp` and `cmake/sources/*`;
- `*GoldenReference.inc`, the emitters, `code/hacs/lean/` and the licence files;
- `NumberField/*`, which stays STL-only (no unguarded `__int128`).

## 2. New files (all ours)

- `code/hacs/cmake/jl/JL.cmake`. It declares `option(OC_ENABLE_JL "Langlandscape JL module (src/jl, Registry/JL)" OFF)`.
  Under `if(OC_ENABLE_JL)` it runs `target_sources(cohomology_app PRIVATE src/jl/….cpp src/hacs/Registry/JL/JL.cpp)` and
  `target_compile_definitions(cohomology_app PRIVATE OC_ENABLE_JL=1)`. The pattern is `cmake/slot27/HeckeZExportWord.cmake`.
- `code/hacs/src/hacs/Registry/JL/JL.cpp`: `void RegisterJL()`. With `OC_ENABLE_JL` off it is an empty body, compiled
  always, so the hook in `ValidationRegistry.cpp` links in both states. The pattern is
  `Registry/Slot27/HeckeZExportWord.cpp`: explicit registration calls `ValidationRegistry::register_validation(name, &fn,
  ValidationTier::…)`, never a static initialiser.
- `code/hacs/src/jl/*.{h,cpp}`: the §3.2 modules, namespace `hacs_jl`.
- SPDX headers on every new C++/cmake file:
  `// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)` and
  `// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception`. These are the HACS scheme
  (`ADD_SPDX_CHECK`, `LicenceGuardValidation`).

## 3. Validation names (registered by `RegisterJL()`)

The prefix `Jl` keeps the names apart from every upstream name. Tiers follow `new-validation.md` item 1.

| name | WP | tier | content |
|---|---|---|---|
| `JlFreeBlockZValidation` | HJ-6 spike | fast | load `code/results/s06/brandt_free_block_z/D11_M1_k2.json` (frozen expected values copied into the .cpp; no file IO at run time), check `freez::MatrixFnv(ColsOfRowMajor(F, r), r)` = `F_fnv` per op, then build **L ⊕ L** (each F_p → diag(F_p, F_p), rank 4; format §7 item 7), run `LatticeFromFreeZ(11, 0, 5, 2, {2, 3, 5}, G⊕G, ops)` (T_5 passed explicitly: a direct call does not append T_ℓ; via `ReadCellLocal` use P = {2, 3}, b1 = 4) and `ReadLocal` with `{d_target = 2, r_eis = 2, eis_rational = true, k_weight = 2, full_algebra = false}`. Expected: Mazur C_T = 5¹, η = [1, 1] (η doubled on L ⊕ L; *expected*, then *computed*). On L itself the root read is `inconsistent` (`HeckeZLocal.cpp:1072–1075`) |
| `JlQuatValidation` | HJ-1 | fast | `Quat` vs `quat.py` (`find_ab`, nrd/trd, the multiplication table) |
| `JlClassSetValidation` | HJ-2 | standard | class numbers and masses vs `classset.py` (exact `BigRational`) |
| `JlLevelValidation` | HJ-3 | standard | X_B(U) fibres vs `levels.py` |
| `JlBrandtValidation` | HJ-4 | standard | native Brandt T_p **= the HJ-B0 records** (same `F_fnv` in the canonical class order of format §1b; permutation-aware only within `order_ties`) |
| `JlLatticeReadValidation` | HJ-6 | standard | the five q of HJ-6 (congruence module ℤ/num((q−1)/12)), plus a route bit-identity arm (threads 1 vs N) |
| `JlTreeValidation` | HJ-7 | standard | `s02`/`s03` Ribet / Ihara tables |
| `JlOrdinaryValidation` | HJ-9 | slow | Λ-adic ranks |

Only `JlFreeBlockZValidation` belongs to the HJ-6 spike. The others are named now so that the roster is fixed. The
records' native writer (the C++ side of the v1 format) writes `writer = "hacs_jl:<binary sha256>"`.

## 4. `FreeBlockZ` fields and the `ReadLocal` options per read type

Field mapping: format spec §3. Only `F` and the operator list are read (`HeckeZLocal.cpp:741–780`). The other members are
carried along. Before any read, `Lattice2HeckeZ` checks `F_fnv`.

| read | `LatticeFromFreeZ` | `ReadOptions` | notes |
|---|---|---|---|
| Mazur / Eisenstein, k = 2 | on **L ⊕ L** (diag(F_p, F_p), rank 2h; format §7 item 7): `N = D·M`, `n = 0`, ℓ \| num((q−1)/12), K ≥ 2 with ℓ^K < 2^63, `P ⊆ ops`, T_ℓ ∈ ops; T_ℓ in P explicitly on a direct `LatticeFromFreeZ` call; `b1 = 2h` via `ReadCellLocal` | `d_target = d_algebra`, `r_eis = 2·e_eis` (= 2), `eis_rational = true`, `k_weight = 2`, `full_algebra = false`, `rat` absent, `allow_bad_primes = false` | λ_p = p + 1. η lists each L-value twice. **ℓ = 2** (q = 17, 41): the annihilator is not sharp, so root = `open(precision)` on L and L ⊕ L alike; refuse by name (`refused(ell2_not_sharp)`) or use our Smith route. Tag *computed*; never carry `c3 = certified` or `root = closes` into a JL claim |
| k > 2 local type (no Eisenstein) | `n = k − 2`, the same | `d_target = d_algebra`, `r_eis = 0`, `eis_rational = false`, `k_weight = k` | ReadLocal stops at `root = general_case` (no L ⊕ L needed). Only `c3`, `mono`, `e` are meaningful. Lattice-dependent at p \| D, ℓ \| \|Γ_x\| and ℓ = 2 (Hecke-stable hull, format §6, §7); records say `canonical: false`, so compare by `charpoly_Z`, not `F_fnv` |
| η^B cusp–cusp | — | — | not ReadLocal. Our `DescentSmith` route (ℤ/ℓ^k, ℓ^k < 2^31) on the q-new Gram |
| ℓ \| \|Γ_x\| cross-check | the same on `F = Bᵀ` (divisor lattice) | the same | the two reads must agree at ℓ ∤ 6∏\|Γ_x\| |

Required, not defaulted: `d_target`. The default 0 trips `ENGINE_CHECK` at `HeckeZLocal.cpp:943`. A read prime missing
from `ops` is an `ENGINE_CHECK` crash, not a refusal. So `Lattice2HeckeZ` checks P ∪ {ℓ} ⊆ ops first and refuses by name
(`refused(op_missing)`, our word).

## 5. The "every C++ package" checklist (slot-27 plan §0, as plan §3.4/§7.1 bind it)

Each Lane-B C++ WP shows all of the following before merge:

1. `git diff <base> -- '*GoldenReference.inc'` is empty.
2. `GOLDEN_STRICT=1`: tier A 12154 / 0 and tier B 6231 / 0 (golden total 18 385 untouched).
3. The four digests are unchanged (the ConsoleDet C4 (a) digest among them).
4. `LABEL_CENSUS … unresolved=0 stale=0`.
5. `ADD_SPDX_CHECK … verdict=OK` and `LicenceGuardValidation … verdict=OK`.
6. `--all` is green at 246 + the JL names (and `--list` = 294 + the JL names).
7. `CliManualCoverageValidation` passes, with the two generated tables of §1 regenerated in the same commit.
8. `ConsoleScriptValidation` passes.
9. The HeckeZ brief rule: state the parallel decomposition, plus a route bit-identity arm (threads 1 vs N; CPU vs GPU
   where a GPU route exists). Neither the HeckeZ default fingerprint nor any HZ record changes: Lane B never calls HZ-RAT
   or the record builder.
10. Box discipline:
    - ≤ 2 heavy jobs, each under `s27/build.lock` / `gate.lock`, through
      `flock /home/janosch/data/hacs-run/<lane>/heavy.lock /home/janosch/data/hacs-run/heavy.sh <tag> <cmd>`;
    - a rule-19 prediction (RSS, wall) and `$HACS_RUN_LOG` start/end lines in UTC;
    - no GPU arm on the box;
    - one build directory.
11. Contract-first: no `certified` word on a JL value until a refereed [C] pre-release carries the statement (Q3).

## 6. Open points (for Q2/Q5; none blocks the HJ-6 spike)

1. Whether we edit the three owner-visible docs of §1 (catalogue, EXPECT_NAMES, CLAUDE.md roster) or hand them to the owner.
2. The `OC_ENABLE_JL` default: OFF until HJ-11 is green, as the plan says. Then `JlFreeBlockZValidation` is compiled out in
   the default build and the generated tables do not change. Confirm that the tables are generated from an `ON` build.
3. Whether `JlFreeBlockZValidation` reads the JSON at run time (file IO from `code/results/`) or embeds the frozen values.
   This note proposes embedding: HACS validations do not read the repo's result files.
