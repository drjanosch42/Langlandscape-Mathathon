# CLAUDE.md — HACS seed (`code/hacs/`)

<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

Operating manual for agents working **inside this HACS subtree**. It is a seed-adapted copy of the HACS development
repository's CLAUDE.md (HACS 0.2.1; `PROVENANCE.md` names the source commit). The repository's top-level
`CLAUDE.md` and `agents/rules/code.md` govern branching, commit messages, roles and the repository-wide rules; this file
adds what is specific to HACS. Where the two disagree, the top-level files win for process, this file wins for HACS
safety rules (golden reference, emitters, Lean, licences) — ask the global master if in doubt.

## What this is

HACS (Harder Arithmetic Cohomology System) computes orbifold cohomology of SL(2,Z) / GL(2) with coefficients in
`Sym^n` local systems over F_p, Z/ℓ^k and Z, the Hecke action on it, Hecke algebras, congruence modules and Hida theory.
All modular arithmetic is on `uint32_t` (primes up to ≈ 2^27). The seed is the public release tree plus the curated
development documents listed in `PROVENANCE.md`. The Jacquet–Langlands work of this repository extends it; **upstream
files stay unmodified where possible**, new work goes into clearly marked modules, and every change is recorded in
`CHANGES.md` (rule of `agents/rules/code.md`).

## Paths in this tree

Every path below is relative to this directory (`$HACS_SRC`). The documents were scrubbed of owner-machine paths; the
placeholders mean:

| Placeholder | Meaning |
|---|---|
| `$HACS_SRC` | this tree |
| `$HACS_DATA` | the persistent scratch / data root of HACS runs: **outside** the repository, never `/tmp` (set it per machine) |
| `$DATA_ROOT` | other data directories of the original development machine |
| `$HACS_RUN_LOG` | the shared log of heavy runs on a machine several agents share (see "Shared machines") |
| `$JL_EXCHANGE`, `$JL_RESEARCH`, `$LANGLANDSCAPE` | the HACS ↔ Jacquet–Langlands exchange directory, the JL research checkout, this repository |
| `<private-library>`, `<host-path>` | the owner's private literature library (never public) and other host paths |
| `host-A`, `host-B`, `arm-board`, `cluster-A`, `cluster-B`, … | pseudonyms of the development machines and clusters |

Historical documents (`docs/implementation/**`, the catalogue, the plans) cite the development repository's slots,
commits and handovers. Those are records, not instructions: a step they describe is not to be repeated here unless a
current plan in this repository says so.

## Documents

**Binding** (authoritative, cite by label; versions at seed time):

| Doc | Path | Version |
|---|---|---|
| [C] the mathematical contract | `docs/latex/gl2_contract.tex` | 1.27.0 |
| [E] Hecke extensions | `docs/latex/hecke_extensions.tex` | 1.25.3 |
| [U] Hida Hecke algebra | `docs/latex/hida_hecke_algebra.tex` | 0.8.1 |
| [X] implementation plan | `docs/implementation/hecke_extensions_implementation_plan.md` | v1.28 |
| [P] console spec | `docs/console/00-console-interface-plan.md` | 3.15.0-pre.9 |
| [LP] Lean programme plan | `docs/implementation/lean/00-lean-programme-plan.md` | v1.10 |
| [GT] ground-truth blueprint | `lean/blueprint/src/gl2_groundtruth.tex` + `gt_part_*.tex` | 0.1.0, **not yet binding** |

Also: `src/ModArithmetic/ENGINE_API.md` (engine API contract — **read it before touching a kernel**),
`docs/matrix-engine/00-implementation-plan.md` (§16.3 acceptance matrix), `docs/matrix-engine/campaign.md`,
`src/hacs/Hecke/README.md` (module map, file → contract-section table). The user manual is `docs/latex/cli_manual.tex`
[CLI]; the phenomena gallery `docs/latex/phenomena_gallery.tex` [PG]. PDFs are **not** in the seed: build them with the
`docs/latex/build_*.sh` scripts or `-DOC_BUILD_DOCS=ON` + `make docs` (output in the build directory, never committed).

Detail files: `docs/validation-catalogue.md` (what each validation checks — read it before touching one, and before
assuming a name means what it sounds like), `docs/architecture-detail.md`, `docs/performance-reference.md`,
`docs/KNOWN_ISSUES.md`. Agent role guides: `docs/agent-guides/` (`lean.md`, `benchmarking.md`, `console.md`,
`slot-close.md`, `new-validation.md`; a role agent reads this file **and** its role file). State of the HACS work at seed
time: `docs/implementation/slot27/00-slot27-plan.md` and `HANDOVER_1113.md`. The JL exchange (requests and HACS answers,
if shipped): `docs/jl_exchange/`.

## Build

CMake ≥ 3.18 (≥ 3.21 for presets), a C++17 compiler; CUDA only if `OC_ENABLE_CUDA=ON` (the default). **Out-of-source
only**; on a machine without the CUDA toolkit configure CPU-only:

```bash
cmake -B <builddir> -S . -DOC_ENABLE_CUDA=OFF      # CMAKE_BUILD_TYPE defaults to RelWithDebInfo
make -C <builddir> -j<N>
<builddir>/hacs --version
```

Put `<builddir>` under `$HACS_DATA` (never inside the repository; one build directory per agent, deleted when done).
`<builddir>/CMakeCache.txt` pins the configuration of the first configure: use a fresh directory to change it.
Configurations: `RelWithDebInfo` (default, `-O2 -g -DNDEBUG`), `Debug`, `Release`, `Bench` (`-O3 -march=native`, timing
runs), `Check` (`-fsanitize=address,undefined`), `CheckThread` (TSan). Switches: `OC_ENABLE_CUDA`, `OC_BUILD_DOCS`,
`OC_BUILD_NOTEBOOK`, `OC_ENABLE_LEGACY` (all but CUDA default `OFF`); **no switch changes a computed value**. Detail:
`docs/architecture-detail.md`, `BUILDING.md`. Toolchain of record of the seed: GCC 11.4, nvcc 13.0, CUDA arch 120.

**Validations read tracked files** through the source path baked into the binary (`OC_SOURCE_DIR`): a binary must be
built from the tree whose fixtures it reads, and that tree must not move while the binary is used.

## Validation

No test framework: validations are functions returning 0, registered by name (`src/hacs/ValidationRegistry.cpp` plus the
per-slot fragments `src/hacs/Registry/Slot<S>/`, `cmake/slot<S>/`).

```bash
./hacs --list            # every registered name with its tier (fast / standard / slow); 294 at seed time
./hacs <Name> [<Name>…]  # run named validations in one process; exit code = failures
./hacs --all             # fast + standard (246 at seed time); --all-full adds slow
./hacs --all --shard i/N # one of N disjoint shards (docs/matrix-engine/tools/run_all_sharded.sh runs all)
```

An escaping exception is that validation's failure (`[EXCEPTION]`, then `[FAIL]`); the run goes on. The Hecke acceptance
gate (`HeckeEndToEndValidation`, `HeckeBadPrimeValidation`, `HeckeBenchmarkSmoke`) is `slow`: run it by name or with
`--all-full`. A package that registers a validation, a console verb / type / setting or a CLI token regenerates the
manual tables (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`) in the same commit, or `CliManualCoverageValidation`
fails. A new JL validation registers in its own fragment (recommendation: `src/hacs/Registry/JL/`, `cmake/jl/`), never by
editing an upstream slot fragment; recipe `docs/agent-guides/new-validation.md`.

### Owner-gated emitters and env interlocks (safety-critical)

Each is a no-op unless its variable is set, which keeps `--all` / `--all-full` read-only. **Never set one of these (or
any env hook) to "make a validation pass".** Every scratch emitter's `<dir>` must exist outside the source tree.

| Env | Effect |
|---|---|
| `GOLDEN_EMIT=1 … GoldenEmit` | regenerates `src/hacs/Golden/GoldenReference.inc`: an **owner-gated re-baseline**, every changed line explained object by object |
| `GOLDEN_DUMP=<dir> … GoldenDump` | the re-baseline protocol's object dump, diffed by `golden_explain.py` |
| `CONSOLE_EMIT_EXPECTED=1 … ConsoleScriptEmit` | regenerates `Console/scripts/*.expected`; changing an existing transcript is an owner-gated re-baseline |
| `HECKE_DUMP_TAU`, `HECKE_DUMP_MEREL`, `HECKE_DUMP_SAT_CERT`, `HECKE_DUMP_HZ_CERT`, `HECKE_DUMP_EXZ2`, `CLI_MANUAL_EMIT` `=<dir>` | scratch dumps for the Lean checkers / manual (`HECKE_DUMP_MEREL` **replaces** its validation's arms) |
| `GOLDEN_STRICT=1` | `GoldenRegressionValidation` gates tier B as well as tier A |
| `HECKE_LOCALITY_PROBE=1`, `HECKE_HIDA_HEAVY=1` | interlocks; `(700, 691)` peaks ≈ 33.5 GiB — **predict RSS first (rule 19)** |

All other env hooks (`HECKE_*_ALL`, `*_CELLS`, `*_HEAVY`, `ENGINE_*`, rollback arms `X=0`, …) are read-only: they widen
or replace an arm's cell list or restore an older route, never write and never change a value (register:
`docs/validation-catalogue.md`). Every env-armed arm prints one `EFFECTIVE <name> arm=<X> cells=<k>` line: **read it
before trusting a run**.

### Golden reference and digests

`src/hacs/Golden/GoldenReference.inc`: 18 385 entries; `GOLDEN_STRICT=1 ./hacs GoldenRegressionValidation` → tier A
12154 failing 0, tier B 6231 mismatching 0. The pathspec for "golden untouched" is `'*GoldenReference.inc'` (the short
form `Golden/GoldenReference.inc` matches nothing). Digests of record: `EngineDeterminismValidation` `0x3dddd2ef9a8efd`;
`HeckeExtDeterminismValidation` `digest=0xaef77d786b4f29b4`, heavy `+(128,5) 0x9ed8b83a2fb26622`;
`ConsoleDeterminismValidation` C4 (a) `0xf6ed04bbe8e6b60a`; `HeckeBenchmarkSmoke` `COMPLETED and CERTIFIED`. A change
that moves any of these is a re-baseline and needs the owner.

## Hard rules

- **Assertions / NDEBUG.** `RelWithDebInfo`, `Release`, `Bench` define `NDEBUG`. Non-validation code uses
  `ENGINE_CHECK` / `ENGINE_CHECK_MSG` (always on, O(1) invariants; throws `std::logic_error`) and `ENGINE_DEBUG_CHECK`
  (size-scaling checks, compiled out under `NDEBUG`) from `src/ModArithmetic/EngineCheck.h`; `ConsoleCore` uses
  `CONSOLE_CHECK` / `CONSOLE_DEBUG_CHECK`. Bare `assert` only in `*Validation.cpp`.
- **Two families of switches.** `ENGINE_*` variables and the `U_ell` levers **cannot** change a value; the mathematical
  settings (`locality`, `u_ell`, `sturm`, …, `coefficient_ring`) may; only their defaults are golden.
- **`ENGINE_DEVICE=cpu` is the default and the golden path; the GPU is never enabled by default.**
- **Licences.** Code `LGPL-3.0-only WITH LicenseRef-CUDA-exception`; `lean/` Apache-2.0; `docs/`, `lean/blueprint/`
  CC-BY-4.0; `lean/Vendor/` upstream notices byte-identical, no SPDX headers. **A new source file gets an
  `SPDX-License-Identifier` header in the commit that adds it** (`docs/licence/tools/add_spdx.py --check`; guard
  `LicenceGuardValidation`, read `… verdict=OK`). Mapping: `REUSE.toml`, `LICENSES/`, `NOTICE`, `COPYRIGHT.md`,
  `docs/licence/THIRD_PARTY.md`.
- **No literature, ever.** Never add a third-party PDF, an arXiv source archive or any file from a literature library
  to this tree (the repository goes public with its history). Cite by bibliographic reference.
- **No external CAS in HACS.** No PARI / Sage / Magma inside HACS; number-field code is in-house (`NumberField`, STL
  only). Exact cross-checks may use them **outside** HACS (`code/cas/`), labelled as such.
- **Lean.** **Never run `lake update`** (nor `lake clean`, `lake exe cache get`, toolchain or manifest changes). HACS's
  `lean/` is its own Lake project on `leanprover/lean4:v4.33.0`, **not** the repository's top-level Lean toolchain;
  it is not built here unless a plan says so (`docs/agent-guides/lean.md`). Regenerate `lean/census.tsv` with
  `lean_census.sh --emit` after any [GT] or Lean change; no `native_decide`.
- **Cluster.** No agent connects to a cluster host: the owner alone submits jobs.
- **Rule 19.** Predict RSS and wall time from a measured run of the same class before any heavy run.
- **Label census.** Read `LABEL_CENSUS … unresolved=0 stale=0` (`docs/matrix-engine/tools/label_census.sh`), never only
  an exit status.

## Shared machines

- Scratch, builds and run outputs under `$HACS_DATA` (persistent, outside the repository; never `/tmp`).
- Before a configure or a heavy run check the free space of the volume that holds `$HACS_DATA`: at **≤ 20 GB free warn
  the owner**, at **≤ 10 GB free pause all builds, runs and extractions** until the owner resolves it.
- Log every heavy run (build, `--all-full`, Lean, census) with UTC times in `$HACS_RUN_LOG` when several agents share the
  machine; timing verdicts only in a quiet window granted by the coordinating agent.
- `systemd-run --scope` caps no memory on WSL hosts: cap with `--unit=` services, `prlimit` or an RSS watchdog.

## Architecture (map — prose in `docs/architecture-detail.md`)

Targets: `ModArithmetic` (modular arithmetic, kernels, block model; `Fnv.h` = the one FNV-1a-64 behind every hash),
`HeckeCore` (exact-integer Hecke substrate), `MatrixEngine` (tape: record → `compile()` → `Executor`), `EngineCuda` (the
only device code; a stub when CPU-only), `ConsoleCore` (STL only), `NumberField` (in-house `BigInt`, cyclotomics, LLL,
`Polred`; STL only), `cohomology_app` (the `hacs` executable). Cohomology layer: `EquivariantCohomologyOnK`,
`LocalSystemSL2Z` (the 7-vertex `SL(2,Z)\H` model, `Sym^n`); Hecke (`Hecke/`, [C]); HeckeExt ([E] / [X]); Integral
(`Integral/`, [C] `sec:integral`); the console (`Console/`, [P]; exit codes 0 ok, 1 usage, 2 parse, 3 runtime, 4 failed
`assert`, 5 not implemented in this build). Level N enters by Shapiro induction on the fixed model ([C]
`def:levelNmodel`). Migration guards (`docs/matrix-engine/tools/check_*_includes.sh`, `raw_mod_calls.sh`,
`label_census.sh`) run inside `--all`.

## Conventions

- Matrix entries and arithmetic are `uint32_t` mod a prime `p`; benchmarks use primes up to ≈ 2^27 (e.g. 134217757).
- Use an even `n_sym` in benchmarks and cells: odd `n` vanishes on this model.
- Matrix classes use lazy-cached RREF (computed on first access, invalidated on mutation).
- State claims with their status (*proved* / *computed* / *conjectural* / *cited*), as the repository requires.

## What this file leaves out (relative to the development CLAUDE.md)

Slot pointers and resume files of the development repository, the per-slot suite-status and digest histories
(`slot-history.md`, not shipped), the release / cluster / device kit procedures (`cluster.md` not shipped), the owner's
machine specifics (WSL snap paths, drive letters, GPU schedule file, worktree paths), and the document version
histories. The safety rules above are kept in full.
