<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guide: benchmarking, standing gates, build configurations

For an agent that times anything, compares binaries, touches a kernel or runs `cross_config.sh`. Peers share the box: log heavy runs in `$HACS_RUN_LOG` and ask the lead for a quiet window before a timing verdict.

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim

## Benchmarking (`--bench`)

`./hacs --bench <mode> <args...> [--repeat k] [--cross-checks]` drives the shipped pipeline through the **public API
only**, printing phase timings, peak RSS and one `BENCH ...` line. Modes (`--bench --help`): `cohom`, `hecke`, `family`,
`decomp`, `ext`, `micro <op>`. **Use an even `n_sym`** — odd `n` vanishes on this model. For a sweep use `--campaign`. Full
surface: `docs/performance-reference.md`.

**Standing gates**: `--bench hecke 256 134217757 2` **≤ 0.470 s** and `--bench decomp 128 134217757 2` **≤ 0.109 s**,
**plus the paired-ratio regression guard**: the median NEW/REF per-round ratio against the previous slot's reference
binary (`standing_gate_h2h.sh --gate`, 13 alternating rounds, `--repeat 5`, min, `ENGINE_THREADS=16`) must be **≤ 1.04**
on both (owner ruling 2026-09-23). Permanent guard: fitted exponent of total time in `n_sym` over `{64, 96, 128}` ≤ 3.2.
Latest: W1-25, MET, near-quiet window, `verdict_changes=0` (hecke 0.4157 s, 0.989; decomp 0.0922 s, 1.015); ext H2H default route 0.970 / 0.907 (`slot25/CLOSE_report.md` §3).

**The placement lesson**: compare two binaries only when both place the global thread pool alike
(`pool_placement_check.sh <NEW> <REF>`, or `nm -S <bin> | grep _ZZN6engine4tape10ThreadPool6globalEvE4pool`); a REF
older than `ce73c71` does not pin the layout. Window instruments: `box_watch.sh`, `prewindow_check.sh`,
`window_overlap.py` (`docs/matrix-engine/tools/`).

### CMake options

- `OC_ENABLE_CUDA` (default `ON`), `OC_BUILD_DOCS` (default `OFF`), `OC_BUILD_NOTEBOOK` (default `OFF`), `OC_CUDA_ARCHITECTURES`
  (default `120`; `87` on a Jetson Orin): the build switches above.
- `HECKE_PURE_INTEGER` (default `OFF`): disables the certified floating-point fast path in the Hecke sign predicates, forcing exact-integer arithmetic only. Both settings must produce bit-identical Hecke matrices; toggle with `cmake -DHECKE_PURE_INTEGER=ON .`.
- `ENGINE_SHADOW_LEGACY` (default `OFF`; **needs `OC_ENABLE_LEGACY=ON`**, `FATAL_ERROR` otherwise; comparisons in `legacy/*Shadow*.inc` since S24 CL-L1): runs **both** the engine and the legacy route on every retrofitted call and throws on the first differing entry; `cross_config.sh` arm `legacy-shadow` (≈ 9 h under `--all`).
- `ENGINE_VERIFY_DEVICE` (default `OFF`): re-executes every GPU node on the CPU inside a real run and compares every written window entrywise.
- `ENGINE_COUNT_OBJECTS` (default `OFF`): adds `flat_ctors=` / `block_ctors=` to the `BENCH` line.

## Corrections to the verbatim text above (slot-26 close audit m7)

Current figures are in CLAUDE.md (the W1-25 line is historical). "The build switches above" means CLAUDE.md, Build. The in-source
`cmake … .` toggle is refused since the layout change: use `cmake -B <dir> -DHECKE_PURE_INTEGER=ON`.

## Procedure pointers

`cross_config.sh`: procedure in `docs/performance-reference.md`; **keep the per-arm outputs** (copy `<build_dir>/*.out` out before any `rm -rf`), since the script's table alone does not show that an env lever was read.
