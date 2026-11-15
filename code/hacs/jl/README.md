<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# `code/hacs/jl/` -- Jacquet-Langlands drivers and smoke tests for HACS

This directory is **ours** (new files only; no upstream HACS file is touched). It uses HACS through the console only
(`hacs --script f.oc`, output tags `@@TAG <json>`). Software: HACS v0.2.1, DOI
[10.5281/zenodo.24231446](https://doi.org/10.5281/zenodo.24231446); census data: hacs-data v0.2.0, DOI
[10.5281/zenodo.24147012](https://doi.org/10.5281/zenodo.24147012). Plan: `plan/hacs/HACS-JL-PLAN.md` (Lane A = HJ-0, HJ-A1..A3).

## What lives where

| Path | Content |
|---|---|
| `code/python/langlandscape/hacs_bridge/` | Python bridge (outside `code/hacs`, GPL-3.0-or-later WITH CUDA exception): `runner.py` = `find_hacs`, `hacs_version`, `hacs_sha256`, `run_script`, `child_env`, `parse_tags`, `oc_matrix`, `provenance`, `hz_settings`, `public_path`, `forbidden_env`, `is_forbidden`; the Lane A drivers (A1/A2/A3) are added here |
| `code/python/tests/test_hacs_bridge_runner.py` | pytest: unit tests (no binary) and integration tests (skipped without a binary) |
| `jl/s03_h1_rerun.py` | S03-H1: `descent` over Z re-run of seed (C3), writes `code/results/s03/C3_rerun.json` (existing driver) |
| `jl/smoke/hj0_smoke.oc` | HJ-0 smoke: every verb of plan section 1.1 once, plus `descent(...).module(5, 2)`, exit 0, ~0.2 s |

## The binary

Build **outside the tree** under `$HACS_DATA` (never inside the repository). Two presets (`code/hacs/CMakePresets.json`):

```bash
# minimal = RelWithDebInfo, OC_ENABLE_CUDA=ON (needs the CUDA toolkit; the GPU is still never used by default)
cmake --preset minimal  -B $HACS_DATA/hacs-build/<name> -S code/hacs
# cpu-only = minimal with OC_ENABLE_CUDA=OFF (a machine without the CUDA toolkit)
cmake --preset cpu-only -B $HACS_DATA/hacs-build/<name> -S code/hacs
make -C $HACS_DATA/hacs-build/<name> -j<N>
$HACS_DATA/hacs-build/<name>/hacs --version                              # hacs 0.2.1 (...)
```

The full JL lane (Lane A) builds with `cmake --preset minimal -B /home/janosch/data/hacs-build/laneA` (from `code/hacs`).
No switch changes a computed value.

The bridge finds the binary via an explicit path, else `$LANGLANDSCAPE_HACS`, else
`/home/janosch/data/hacs-build/laneA/hacs`; the path is resolved to an absolute one (the child runs with cwd = a temporary
directory, so relative paths must not leak into it).

### Child environment (allowlist)

`child_env(threads, env_extra)` builds the child's environment from an **allowlist**, never by copying the parent's:
`PATH`, `HOME`, `LANG`, `LC_ALL`, `TMPDIR` (if set) and `ENGINE_THREADS` (from `threads`). `LD_LIBRARY_PATH` is not passed:
the Lane A binary finds `libcudart` through its RUNPATH (checked with `env -i ldd`). `ENGINE_DEVICE` is unset (the CPU
golden path). `run_script(..., env_extra={...})` may add allowlisted names or the documented read-only input hooks of
`READ_ONLY_INPUT_HOOKS` (`ENGINE_DEVICE`, value `cpu` only; `HECKEZ_LOCAL_PAR`); anything else raises `ValueError`, and so
does every write-capable name (`is_forbidden`): the explicit set `forbidden_env()` and the patterns `GOLDEN_*`,
`HECKE_DUMP_*`, `*_OUT`, `*_DUMP`, `*_EMIT`.

Explicit set (from a grep of every `getenv` in the seed's `src/`, 2026-11-15): `GOLDEN_EMIT`, `GOLDEN_DUMP`, `GOLDEN_OUT`,
`GOLDEN_STRICT`, `CONSOLE_EMIT_EXPECTED`, `CLI_MANUAL_EMIT`, `HECKE_DUMP_TAU`, `HECKE_DUMP_TAU_PAIR`,
`HECKE_DUMP_TAU_RHO_CELLS`, `HECKE_DUMP_MEREL`, `HECKE_DUMP_SAT_CERT`, `HECKE_DUMP_SAT_CERT_CELLS`, `HECKE_DUMP_HZ_CERT`,
`HECKE_DUMP_HZ_CERT_CELLS`, `HECKE_DUMP_EXZ2`, `HECKE_EXT_JSON_OUT` (HeckeExtRamanujanValidation.cpp:344),
`HECKE_ATLAS_OUT` (HeckeAtlas.cpp:1223), `ORBIFOLD_MP_DUMP` (OrbifoldMPRulesValidation.cpp:113), `HECKE_LOCALITY_PROBE`,
`HECKE_HIDA_HEAVY`. Every other hook (`HECKE_*_ALL`, `*_CELLS`, `*_HEAVY`, `ENGINE_*` but `ENGINE_THREADS`, input files such
as `HECKE_ATLAS_IN`, `HECKE_*_TSV`, test interlocks `HACS_*`) is simply not on the allowlist, so it never reaches the child.

### Provenance

`provenance(script, params, runtime_s, hacs=None, *, notes=None, hz=False)` has the keys of `langlandscape.results.write`
(`script`, `commit`, `params`, `date`, `runtime_s`, `python`, `pari_version`, `notes`) plus `dirty`, `hacs_version`,
`hacs_sha256` (sha256 of the binary, cached per path + mtime + size) and `hacs_binary`. **No absolute path is recorded**:
paths inside the repository are made relative to its root, others are cut to their last three components
(`hacs-build/laneA/hacs`); this applies to `script`, `hacs_binary` and absolute-path strings in `params`.
With `hz=True` it adds `hz_settings`.

`hz_settings()` = `{default_fp, hz_theta_order, source}`. How the binary reports them: there is no settings verb for the HZ
(integral Hecke structure) settings, and `settings()` does not list them. The fingerprint **is reported**: every
`hecke_structure` record has a `settings_fingerprint` field (FNV-1a-64 of `RationalSettings::canonical_text`); the bridge
reads it from a default `hecke_structure(11, 0, "anemic")` under `coefficient_ring = "Z"` (0.1 s) and gets
`0x8ffc29730c4f9672` (= `kHZDefaultFingerprint`, `GoldenHarness.cpp:2710`). The theta order is **not reported**; it is
**inferred**: `canonical_text` prints a `theta_order` key only when the order is not `lex`
(`Integral/HeckeZRational.cpp:475`), so the documented default fingerprint means `lex`. If the run fails, the documented
values come back with `source = "documented-not-reported"`.

### Tag parsing

`@@TAG<sep><json>`, `<sep>` = spaces or tabs, `TAG` in `[A-Za-z0-9_.-]+`; `@@TAG` with no payload or only whitespace gives
`None`. A malformed `@@` line or undecodable JSON raises `HacsParseError` (a `ValueError`) with `check=True`; with
`check=False` nothing raises and the messages are in `ScriptResult.parse_errors`. A timeout raises `HacsTimeout` (a
`HacsScriptError`, `returncode = None`) with the partial stdout / stderr.

## Verb table and smoke status (HJ-0, `hacs 0.2.1`, run 2026-11-15)

All verbs ran; `hj0_smoke.oc` exits 0 in 0.16 s wall (`ENGINE_THREADS=4`, allowlisted env). Transcript (outside the tree):
`/home/janosch/data/hacs-run/laneA/hj0_smoke.log`. Polynomial lists: `coeffs(...)`, `level_n` and `hida_*` charpolys are
low -> high; `descent` `charpoly[i].exact` and `module(...).ops[i].charpoly_free` are high -> low (strings / ints).

| Verb(s) | Status | Result seen (*computed*) |
|---|---|---|
| `sl2z_model` | ok | `sl2z_7vertex` |
| `symmetric_power`, `cohomology` | ok | n = 10, ell = 7: dims [0, 3, 0] |
| `level_n` (N = 11, n = 0, ell = 7, primes [2, 3, 11]) | ok | h0 = 1, h1 = 3, index 12; T_2, T_3 and U_11 (p dividing N, `bad: true`) charpolys returned |
| `nebentypus` (7.2, n = 2, ell = 13) | ok | order 3, parity ok, h1 = 4 |
| `algebra`, `commutant`, `algebra_invariants`, `is_local`, `socle`, `tangent_space`, `loewy`, `radical`, `charpoly`, `minpoly`, `jordan_type`, `kernel`, `intersect` | ok | on a 3x3 nilpotent Jordan block over F_7: local, Gorenstein, Loewy length 3 |
| `hida_tower` (10, 11, 2), `hida_lambda` (11, 12, 3) | ok | h = 3; U-charpoly [450, 1] (low -> high) = x + 450, so the U-eigenvalue is -450 = 881 mod 11^3, and tau(11) = 534612 = 881 mod 1331 (checked) |
| `descent` under `coefficient_ring = "Z"` (N = 11, n = 0, primes [2, 3]) | ok | status ok; char_Z(T_2) = x^3 + x^2 - 8x - 12 = (x + 2)^2 (x - 3), char_Z(T_3) = x^3 - 2x^2 - 7x - 4 = (x + 1)^2 (x - 4); exact, determined |
| `.module(ell, K)` on that record (ell = 5, K = 2) | ok | status ok, route `cokernel`, K_max = 13, free rank 3, no torsion, invariant factors [2, 2, 2]; T_2 matrix [[23, 0, 0], [0, 23, 24], [0, 0, 3]], charpoly_free [1, 1, 17, 13] = char_Z(T_2) mod 25; T_3 charpoly_free [1, 23, 18, 21] = char_Z(T_3) mod 25. `module_Z()` is **not** called (owner-gated, Q4) |
| `hecke_structure` (11, 0, "anemic") | ok | status final, C_T certified:0x5, `settings_fingerprint` 0x8ffc29730c4f9672 |
| `json(...)` | ok | used on every line |

No verb of section 1.1 is missing from this build.

## Console conventions learned

- `matrix(p, [[1, 2], [3, 4]])` is the literal (entries reduced mod p by the caller; `bridge.oc_matrix` does this).
- `coeffs(f)` gives coefficients low to high; `charpoly` lists inside `level_n` / `hida_*` records are low to high as
  well; `descent`'s `charpoly[i].exact` and `module(...)`'s `charpoly_free` are high to low.
- Setting `coefficient_ring = "Z"` changes later verbs: put integral verbs after the mod-ell ones, or in a separate script.

## Decisions Q1-Q3 (as recorded for Lane A)

- **Q1 (licensing scheme): PROVISIONAL.** Files inside `code/hacs/` follow the HACS scheme (LGPL-3.0-only WITH
  LicenseRef-CUDA-exception, CC-BY-4.0 for Markdown); files outside (`code/python/...`) follow the repository scheme.
- **Q2 (hooks / upstream edits).** Plan default (bracketed in `plan/hacs/HACS-JL-PLAN.md`): *yes*, the three one-line hooks
  of §3.4 may go into upstream files, logged in `code/hacs/CHANGES.md`; else a standalone `hacs-jl`. Slot-27 revision (§7,
  origin/main): the *where* is `Registry/JL/` + `cmake/jl/`, never a slot fragment; permission still open (Fabian).
- **Q3 (internal calls / the word `certified`).** Plan default: *yes*, with the distinct schema name `jl_lattice_read/v1`.
  Slot-27 revision: reads go through the refereed EXW entry `LatticeFromFreeZ` -> `ReadLocal` (no `HeckeZRecord`, no HZ-RAT
  internals); by HACS's contract-first rule a JL read **cannot claim `certified`** until a contract text is refereed, so it is
  tagged *computed (HACS ReadLocal)* under `jl_lattice_read/v1`.
- **Lane B is deferred past the Mathathon** (plan §7.4, slot-27 revision), gated on Q2 and Q5.
- **Lane A needs neither Q2 nor Q3**: console only, no hooks, no upstream edits, no internal C++ calls, no env hook set.
