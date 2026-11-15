# Performance reference (current tree)

Moved verbatim out of `CLAUDE.md` so the per-session context header stays short. Nothing here has
been edited: every timing, RSS figure, throughput and fitted exponent is exactly as it stood in
`CLAUDE.md` at the hecke-extensions slot-4 close (2026-09-22).

**How to invoke the benchmarks** (`--bench <mode>`, the mode list, `--repeat`, `--count-allocs`,
`--lean`, `--backend`, the `BENCH` line): `CLAUDE.md` → "Benchmarking (`--bench`)".
**The pre-Phase-3 baseline** these numbers are measured against:
`docs/matrix-engine/03-profiling-baseline.md`. **The perf ledger**:
`docs/matrix-engine/perf-ledger.md`. **The per-slot performance references and the standing
gates**: `docs/implementation/slot-history.md`.

---

**Thread scaling, final tree** (default build, `--repeat 4`, min, quiet box;
`ENGINE_THREADS=1` → 16 → 32): `hecke 128` 0.383 → **0.111** → 0.121 s; `hecke 256` 2.607 →
**0.555** → 0.556 s; `family 128 … 2 2` 0.148 s at 16 threads against a `hecke 128` of 0.111 s
(1.33×). The Phase 4 speed exit criteria (≥ 4× / ≥ 8× against the *same binary* at one thread,
and `family ≤ 1.2×` a `hecke`) are therefore **still not met** at 3.4× / 4.7× / 1.33× — the
Phase 4 closure sped the single-thread path up 1.47× as well, so the ratios moved against it
while both walls fell 5–7×. What is left is structural, not schedulable: 19 % of the wall is in
host-serial `PANEL_RREF` / `PIVOT_SEARCH` (a 256-wide panel is ~250 dependent column steps) and
33 % in host recording, `BlockBuilder` assembly and the `q = 1` `factor_basis` stage-2 host steps.
The profile, what each closure step bought and the full serial breakdown are in
`docs/matrix-engine/00-implementation-plan.md` §13.7; the ranked follow-ups are §16.4.

Peak RSS `hecke n --lean` (16 threads): 29 / 56 / 87 / 137 MB at `n = 128 / 192 / 256 / 320` ⇒ a
1.25 GB fit at `n = 1000`; **measured `cohom 1000 --lean`: 14.8 s / 1157 MB** and
`hecke 1000 --lean`: 14.4 s / 1394 MB. Profiling knobs: `ENGINE_TRACE_NODES=1` (per-op /
per-class engine profile, pool idle fraction, dense-PLU phase split, printed by `--bench` per
repeat), `ENGINE_TRACE_RSS=1` (per-step cohomology / Hecke / elimination traces),
`ENGINE_TRACE_PASSES=1` (the `hybrid` cost model's per-group verdict), `ENGINE_ELIM_BASE` (Crout
base width, default 1).

Reference numbers on the **final tree** (2026-09-06, after matrix-engine Phase 6, `--repeat 5`,
`--count-allocs` where an allocation count is shown, quiet box; the **pre-Phase-3** figures of
`docs/matrix-engine/03-profiling-baseline.md` §11 are in parentheses):

```
                                                      time      peak RSS   allocations
./hacs --bench hecke   48 134217757 2  ->  0.0256 s      22 MB               (0.50 s,  71 MB, 2.52 M)
./hacs --bench hecke   64 134217757 2  ->  0.0378 s      32 MB
./hacs --bench hecke   96 134217757 2  ->  0.0752 s      75 MB
./hacs --bench hecke  128 134217757 2  ->  0.1246 s     112 MB      33 355   (10.22 s, 437 MB, 26.19 M)
./hacs --bench hecke  160 134217757 2  ->  0.1917 s     165 MB
./hacs --bench hecke  192 134217757 2  ->  0.2913 s     241 MB
./hacs --bench hecke  256 134217757 2  ->  0.5608 s     374 MB
./hacs --bench cohom   64 134217757    ->  0.0286 s      22 MB               ( 0.64 s, 118 MB, 4.60 M)
./hacs --bench cohom   96 134217757    ->  0.0522 s      40 MB
./hacs --bench cohom  128 134217757    ->  0.0894 s      57 MB      17 153   ( 6.30 s, 437 MB, 26.16 M)
./hacs --bench cohom  160 134217757    ->  0.1442 s      77 MB
./hacs --bench cohom  256 134217757    ->  0.3864 s     235 MB

./hacs --bench cohom 1000 134217757 --lean   -> 14.824 s   1157 MB
./hacs --bench hecke 1000 134217757 2 --lean -> 14.403 s   1394 MB
./hacs --bench family 128 134217757 2 2      ->  0.148 s    178 MB  (16 threads)

./hacs --bench micro gemm 128                  ->    27.8 Gmodmul/s  (legacy arm: 0.216)
./hacs --bench micro gemm 512                  ->    30.3 Gmodmul/s  (legacy arm: 0.215)
./hacs --bench micro gemm 2048 --backend gpu   ->  4065.0 Gmodmul/s  (82 % of the roofline)
./hacs --bench micro rref 1677 1419            ->  0.0559 s          (legacy arm: 2.403 s)
./hacs --bench micro kernel 1677 1419 258      ->  0.0289 s
```

Through the tape at `2048³` (`EngineCoreScalingValidation`, which is where `EngineCostModel.h`'s
CPU constants are re-measured): **28.3 / 115.1 / 307.8 / 371.5 Gmodmul/s** at 1 / 4 / 16 / 32
threads, i.e. 10.9× at 16 threads; the Θ-like batched program 20.8 → 245.4 G (11.8×).

**GPU G1, the elimination session** (slot-18 WP-19a, `ENGINE_API.md` §12.8; RTX 5070 Ti, a loaded
box beside three LAT37 cells, `--repeat 3` min, two interleaved rounds): `--bench cohom 1000 134217757
--lean` **cpu 14.13 / 14.81 s, gpu 11.90 / 12.85 s**, `hybrid` 14.57 s, gpu with the rollback
`ENGINE_ELIM_SESSION=0` 40.2 s (slot 14 [G14a]: cpu 14.7, gpu 28.0, hybrid 18.5 s); VRAM peak 4.6 GB
(session) vs 15.8 GB (rollback); RSS 1.42 GB (gpu) vs 1.16 GB (cpu; the CUDA context and the pinned
pool). `EngineDeviceTrapValidation` rows A / B: gpu 19.3 / 327.6 ms vs cpu 26.4 / 434.0 ms (slot 14:
47.3 / 980 vs 33.2 / 705). The [G14a] stop line (`cohom 1000` gpu ≤ cpu) is met; `cpu` stays the
default and the golden path.

The **campaign driver's** throughput on the same tree: the `n_sym ≤ 200` × 9 ℓ `T_2` exit sweep
(909 jobs) runs in **35.1 s = 1 555 jobs/min** at `jobs = 32, threads = 1` (4 345 MB), and the
`n_sym ≤ 64` probe (297 jobs) in **0.69 s = 25 780 jobs/min**.

The fitted exponent of the total time in `n_sym` over `{64, 96, 128}` is **1.72** for `hecke` and
**1.63** for `cohom` (Phase 3: 2.56 / 2.49; Phase 2: 3.15 / 3.24; Phase 1: 3.17 / 3.34) — both far
under the ≤ 3.2 permanent guard; over the larger `{96 … 256}` band, where the fixed per-run
overhead no longer dominates, both are **2.05**. On a `Bench` build (`-O3 -march=native`)
`-march=native` still buys essentially nothing (the engine dispatches to AVX-512 at runtime).
One `rho_n` at `n_sym = 160`, `ell = 134217757`: **0.215 ms** generic, 0.136 ms for `T`,
0.030 ms for `S`.

**The block model is what closed the gap, and `ENGINE_BACKEND=legacy` measures it.** On the same
binary, `ENGINE_BACKEND=legacy --bench cohom 128` is **6.43 s / 302 MB / 4.90 M allocations**
against the engine's 0.089 s / 57 MB / 17 K, and `hecke 128` is **11.64 s / 302 MB / 4.93 M**
against 0.125 s / 112 MB / 33 K — 72× and 93× on the same binary. (That legacy arm is the *pre-Phase-3 consumers on the
post-Phase-2 substrate*, not the pre-Phase-2 tree, which is why its allocation count is 4.9 M and
not the 26 M of the Phase 3 baseline.) Phase 2 had measured a 3 % spread between the two backends
on `cohom 128`, because the binding constraint was the block *orchestration* — ~4.9 M gemm calls
of mean shape `20x13x12`, 88 % of them with `k == 1`, and 31.7 M short-lived `FlatMatrix`
constructions per run. `BlockBuilder` and the block kernels removed exactly that. Full
measurement: `docs/matrix-engine/00-implementation-plan.md` §12.

## Sharded `--all` (S24 SHARD)

`docs/matrix-engine/tools/run_all_sharded.sh <binary> [N] [--full]` runs `--all` (`--all-full`) as N processes
`<binary> --all --shard i/N` at once and merges them into one `SHARDED_ALL … verdict=OK|FAIL` line (exit = total failures).
No check leaves the suite: the shards' union is the roster, each name once (partition, device group, guard:
`docs/validation-catalogue.md`, "Slot 24 SHARD"). RSS ≈ 4.4 GiB per shard, so N = 4 needs ≈ 18 GiB.

| run | wall | conditions |
|---|---:|---|
| `--all`, unsharded (`e003a975`) | 24:00.6 | quiet box, 2026-11-01 (HANDOVER_1101) |
| `run_all_sharded.sh … 4` (`2402e20e`) | **7:46** (466.2 s) | 2026-11-01 16:28 UTC, load1 0.93 at start (median 15.5, max 33.8 during, with the shards themselves and one CPU-only Lean job of another session), GPU without foreign compute processes |

The four `--all` shards are planned at 493 s each (weights from isolated runs, 4 at a time); the device group (19 names)
is in one shard. `--all-full` cannot shard below ≈ 20 min: `HeckeModuleStreamSlowValidation` alone is ≈ 1205 s.

---

## `--bench` invocation surface (full text)

This is the paragraph `CLAUDE.md` used to carry verbatim; `CLAUDE.md` now keeps a compressed
version of it.

`./hacs --bench <mode> <args...> [--repeat k] [--cross-checks]` drives the shipped
pipeline through the public API only (same code paths as `--all`), printing phase-split timings,
peak RSS and one machine-readable `BENCH ...` summary line. (For a *sweep* rather than one point,
use `--campaign` — see "Campaign driver (Phase 6)" under Architecture.) `--bench --help` lists the modes:
`cohom <n> <ell>`, `hecke <n> <ell> <p>`, `family <n> <ell> <p> <r>`, `decomp <n> <ell> <p>`,
and — since Phase 2 — `micro <op> <args...>` (`--bench micro --help`), the arithmetic
micro-benchmarks: `gemm`, `gemv`, `rref`, `kernel`, `transpose`, `suite`, and — since Phase 5 —
`cuda` (the whole GPU throughput table). `micro` takes `--backend legacy|engine|gpu`,
**default `engine`** (overridable by `ENGINE_BACKEND`); `gpu` selects the `engine::cuda` device
kernels (`gemm` / `gemv` / `transpose`; `rref` / `kernel` stay CPU-driven and report "not
available", exit 2, as does every `gpu` op without a usable device); `legacy` means
the *pre-Phase-2* substrate end to end (it installs an `engine::elim::ScopedLegacy` guard), so the
two columns are a like-for-like before/after, and equal `checksum=` values across them are a
bit-identity statement. Use an **even** `n_sym` (odd `n` vanishes on this model — see the −I /
odd-n gap). `--count-allocs` adds `allocs=` / `alloc_bytes=` to the `BENCH` line, counted by a **counting
replacement global `operator new`/`delete`** in `Bench/BenchDriver.cpp` (every replaceable form,
so no library can pair one allocator's `new` with the other's `delete`), snapshotted around each
measured repeat — so the number is one pipeline run, not the process total. `alloc_bytes` is
*requested* bytes summed at allocation time, not a high-water mark; `rss_mb` is the peak.
`cmake -DENGINE_COUNT_OBJECTS=ON .` additionally reports `flat_ctors=` / `block_ctors=`.
`--lean` (Phase 4) runs the memory-lean configuration — no `Θ_eq` certification, intermediates
released at their last reader, degrees sequenced — `A^{(q)}` unchanged, `lean=1` on the `BENCH`
line. `ENGINE_TRACE_RSS=1` prints VmRSS/VmHWM after every phase and every step of
`compute_cohomology_block()`; `ENGINE_TRACE_ELIM=1` prints the tape elimination driver's
host / compile / run split with the host-serial (`PANEL_RREF`) share.

### The `U_ell` lever flags (hecke-extensions slots 13–14; added at the slot-14 close, WP-17, audit S7)

Three pairs of flags scope the value-preserving `U_ell` levers for one `--bench` run. Like the
`ext` options below they are parsed by `Bench/BenchDriver.cpp` (`:1098–1109`) but are not in the
frozen `--bench --help` text. Each flag installs the lever's scoped guard for the run
(`HeckeOperatorOptions::ScopedUEllLowRank` / `ScopedCosetStreaming` / `ScopedParallelSetup`).
When one is given, the `BENCH` line carries `u_ell_low_rank=<0|1>` / `coset_stream=<0|1>` /
`parallel_setup=<0|1>`. When it is omitted, the process default applies and the key is absent.
**None of them can change a value.** `HeckeUEllStreamValidation` proves every combination equal
to the all-off path.

**Removed by S24 CL-R1 (2026-10-31, owner ruling 2):** the three flag pairs below no longer exist (`--bench: unknown option`,
exit 1, in every build); the four levers are retired, and their env opt-outs are refused in an `OC_ENABLE_LEGACY=OFF` build
and still work in an `ON` build (catalogue, "Rollback-lever register"). The table is kept as the record of slots 13–24.

| flag | lever | process default (owner Q8, 2026-09-28) | env opt-out |
|---|---|---|---|
| `--u-ell-low-rank` / `--no-u-ell-low-rank` | the `U_ell` low-rank lever (slot-13 WP-4): `ρ_n` of singular-mod-`ell` blocks stored as `U V` factors | Auto: in effect iff `ell \| N` and the fibre is `SymN` (`--u-ell-low-rank` forces On) | `HECKE_U_ELL_LOW_RANK=0` |
| `--coset-stream` / `--no-coset-stream` | coset streaming of the coset tables' `ρ_n` (slot-14 WP-10) | on | `HECKE_COSET_STREAM=0` |
| `--parallel-setup` / `--no-parallel-setup` | the serial setup phase on the consumer pool (slot-14 WP-10), above `items · work ≥ 2^22` | on | `HECKE_PARALLEL_SETUP=0` |
| — (no flag) | G0's rank-one closed form for singular-mod-`ell` `ρ_n` over `F_ell` | on (under the low-rank lever) | `HECKE_RANK1_CLOSED_FORM=0` |

Measured effect: `(128, 691)` `U_691` 2745 → 574 MB under the low-rank lever alone (slot-13 WP-4).
The WP-10 / G0 figures, the per-`n` ladder and the cluster-B heavy cells are in
`docs/implementation/slot14/WP-10_report.md`, `G0_report.md` and `WP-C10_cluster-B_september_report.md`.
On the standing gates (`hecke 256`, `decomp 128`: `ell = 134217757`, `T_2`) the low-rank lever is out of
scope (`ell ∤ N`), the parallel setup stays below its work threshold, and streaming only drops the nine unused
tables of 3 cosets. WP-10's indicative pairs gave ratios 0.986 / 0.988 (WP-10 report §4).

### `--bench ext` campaign-cell options (hecke-extensions slot 7, WP-6)

Two flags, **deliberately outside** the frozen `--bench --help` text
(`Console/scripts/cli_frozen/bench_help.stdout` — [S7] plan §3.0's shared-file rule keeps
`BenchDriver.cpp`'s printed usage byte-unchanged), so they are documented here instead, per
[X] §6.2 E2 (e′) / [S7] plan WP-6 scope 1:

* **`--campaign-cell`** — runs the campaign cell's own driver options instead of the plain `ext`
  mode's defaults: `with_cone = true`, `with_sign_split = true`, and (when no explicit family list
  is given) the default family flips from the plain mode's `2,3,5` to the engine's own
  `2,3,5,7` (`CampaignSpec.h`'s `ExtSpec::good_primes` empty case). The record's canonical split
  and rendering need no flag — since slot-7 WP-3 item 6 it runs unconditionally inside
  `HeckeExtDriver::run()`. Without it, `--bench ext` is byte-unchanged from every pre-WP-6 build
  (verified against a `9f4ea8d`-built binary, numbers normalised out).
* **`--u-ell VALUE`** — scopes `hecke::MathSettings::u_ell` (`"auto"` / `"off"` /
  `"budget_mb=<M>"`, `Hecke/HeckeSettings.h`'s `ParseUEll`) for the run, stamped
  `SettingSource::Spec` exactly as `CampaignSpec.cpp` stamps a spec's own `u_ell = ...` line.
  Omitted: the process-wide setting is left alone (itself `"auto"` at the default, matching
  `ext_first.spec`'s own value, [S7] plan §6 confirmation 9).

Together, `--bench ext <n_sym> <ell> [family] --campaign-cell [--u-ell V]` is `T_cell` of
[X] §6.2 E2 (e′): `W_ext − W_0 ≤ c · Σ_cells T_cell`, `c = 1.25` ([S7] plan §10 decision 5). The
per-cell family for a real measurement is `{2,3,5,7} ∪ {p of that cell's jobs}` (read from the
campaign's own `summary.tsv`, not guessed), never the plain mode's `2,3,5`; using the plain form
as `T_cell` would omit the cone, the sign split and the fourth prime and bias (e′) toward a miss
by the cone's cost ([S7A] audit finding 6 / M-4, the same "denominator not the comparable run"
pattern as E1 (d)).

`docs/matrix-engine/tools/e2e_measure.sh --e2prime` drives this end to end: it measures `W_0` /
`W_ext` as (e) always has (three alternating pairs by default, [OD] S6-2), enumerates every
cell the ext pass actually drove from the ext run's own record files (`ext_cells=`, distinct from
the narrower `u_ell_included_cells=` — pre-WP-6 `u_ell_cells`, renamed: it only ever counted the
`"u_ell":{"included":true}` subset, which includes `ell ∈ {2,3}` and `n = 0` and is *not* the ext
subgrid, [S7] plan §2.3 item 6/7), measures `T_cell` per cell at `--repeat 3` (min,
`ENGINE_THREADS=16`), falling back to `--repeat 1` alone once a cell's own first run exceeds 60 s
(decision 5 (B), stated before any number is seen), and prints one `E2E_PRIME ...` summary line.
See the script's own header comment for the full protocol, options (`--c`, `--cell-repeat-gate`,
`--u-ell`, `--family`) and output format. The script never writes into
`docs/matrix-engine/results/` (a `git status --porcelain` guard runs before and after); the real
W3 measurement is the lead's overnight window ([S7] plan §4.5), not WP-6's.

---

## Moved from CLAUDE.md at the slot-17 start (2026-10-02), verbatim — "Cross-config diff runner" and "Benchmarking (`--bench`)" (standing gates and every per-slot reference)

*(Copied unchanged from `CLAUDE.md` at `6863260`, lines 449–591; headings inside keep their original levels. `CLAUDE.md` now carries a compact form.)*

### Cross-config diff runner

`docs/matrix-engine/tools/cross_config.sh` generalizes the `HECKE_PURE_INTEGER` protocol
(`Hecke/README.md`) to an arbitrary list of configurations: for each it configures + builds
`cohomology_app` **out-of-source** under `--build-root` (default `build-xconfig/`), runs
`GOLDEN_STRICT=1 ./hacs GoldenRegressionValidation`, a list of `--bench micro` cases
(default `gemm 512`, `rref 1677 1419 258`) and any `--validations Name1,Name2`, prints one matrix
(tier A/B counts, checksums, exit codes, wall time), and **exits non-zero on any golden failure,
cross-config checksum mismatch or failed validation**. A configuration is
`Config[+OPTION=VAL...][@ENV=VAL...]`; `CheckThread` (`setarch x86_64 -R`) and `Check`
(`ASAN_OPTIONS`/`UBSAN_OPTIONS`) are handled automatically. Usage:

```bash
docs/matrix-engine/tools/cross_config.sh RelWithDebInfo RelWithDebInfo+HECKE_PURE_INTEGER=ON RelWithDebInfo@ENGINE_BACKEND=legacy
```

**Legacy arms since S24 CL-L0 / CL-L1 (2026-10-30/31, owner ruling 1; CLEANUP plan §2.6).** An `OC_ENABLE_LEGACY=OFF` build
refuses `ENGINE_BACKEND=legacy` (exit 1), and `cmake` refuses `ENGINE_SHADOW_LEGACY=ON` without `OC_ENABLE_LEGACY=ON`
(`FATAL_ERROR`). The default list therefore carries the aliases `legacy` (= `RelWithDebInfo+OC_ENABLE_LEGACY=ON@ENGINE_BACKEND=legacy`,
replacing `RelWithDebInfo@ENGINE_BACKEND=legacy`) and `legacy-shadow` (= `RelWithDebInfo+OC_ENABLE_LEGACY=ON+ENGINE_SHADOW_LEGACY=ON`,
replacing `RelWithDebInfo+ENGINE_SHADOW_LEGACY=ON`); the example above needs `legacy` in place of its third token. Both arms
run at every slot close, the `legacy-shadow` build also under `--all`.

**VNNI arm since S26 LEVERS-26 (2026-11-12).** The env arm `ENGINE_VNNI=0` is retired (refused in an OFF build, exit 1), so the
default list's former `RelWithDebInfo@ENGINE_VNNI=0` is replaced by the alias `legacy-vnni-off` (= `RelWithDebInfo+OC_ENABLE_LEGACY=ON@ENGINE_VNNI=0`),
like the `legacy-gpu-*` arms of S24 CL-R2: one more ON build per full run.

**The `Check` arm runs under `ENGINE_CUDA_DISABLE=1`** (slot-6 WP-7 for the golden run and the
validations; its `--bench micro` runs only since the slot-6 close, which found them still carrying
the LSan report; since slot-7 WP-11 the runner checks a bench's exit code as well as its checksum,
`docs/KNOWN_ISSUES.md` §4a RESOLVED). Under `-fsanitize=address`
the WSL CUDA driver's one-time probe leaks 50 960 bytes in 5 allocations whose stacks are entirely
inside `/usr/lib/wsl/lib/libcuda.so.1`, so LeakSanitizer used to fail the run **after** a
device-probing validation had printed `[PASS]` (found at the slot-5 close; the pre-existing
`CudaTransferValidation` reproduces it). The runner now sets the variable for `Check` itself; run
**by hand** under ASan, set `ENGINE_CUDA_DISABLE=1` for any device-probing name. The standing
sanitizer protocol above is unaffected — none of the names it lists probes for a device.

## Module route on more than one thread: the RSS term (S23 G2-P audit F4, 2026-10-18)

G2-P (`HECKE_MODULE_PARALLEL`, default on; ENGINE_API §13.6) runs a sat / Loewy cell's module route on `ENGINE_THREADS = k` workers:
the coset-batch assembly of Θ^{(q)} / route 2, the Howell row split and the read-off row blocks (the last two over the elimination hook, so
`ENGINE_HOST_ELIM_HOOK=0` keeps them serial — the EFFECTIVE line then says `elim_hook=off howell_readoff=serial`). Wall time drops (4.5× at
t8 on (300, 10007), ≈ 2× at ℓ ≈ 10³), values are byte-identical at every k, and the peak RSS grows by at most

  **ΔRSS ≤ k · (32·1024·d + 12·d²) bytes + 256 MiB** (d = n + 1, u32 word; the k-term doubles in the u64 word)

— per worker the low-rank group stack (2·4096·d words at ℓ ≈ 10⁴) and ≈ 3·d² words of ρ / product scratch, plus the coset-batch buffers
(capped at 256 MiB). Measured: +0.085 GiB (300, 10007) t8, +0.10 GiB (600, 1009) t8, +0.17 / +0.38 GiB (600, 10007) t8 / t16.

| cell | d | bound k = 8 u32 / u64 | bound k = 16 u32 / u64 |
|---|---|---|---|
| (1000, 10007) | 1001 | 0.58 / 0.92 GiB | 0.92 / 1.59 GiB |
| SW1 (1410, 37) | 1411 | 0.77 / 1.29 GiB | 1.29 / 2.34 GiB |
| C2210 (2210, ·) | 2211 | 1.23 / 2.20 GiB | 2.20 / 4.16 GiB |
| C2574 (2574, 103) | 2575 | 1.47 / 2.69 GiB | 2.69 / 5.14 GiB |
| C2678 (2678, 103) | 2679 | 1.55 / 2.84 GiB | 2.84 / 5.43 GiB |

**Rule (kits):** a kit that gives one extreme cell k > 1 threads counts k threads in admission and adds this term to the cell's RSS cap
(`--cap-gib`, Slurm `--mem`, the watchdog) on top of its one-thread prediction; census-style many-cell shards stay at `ENGINE_THREADS=1`
(the term is 0, and nothing is gained in CPU time). Written into `docs/cluster/local/sat23/LAUNCH_SAT23.md` §4b and
`docs/cluster/noctua2/LAUNCH_2026-11.md` §5b.

**One `ENGINE_THREADS` reader, per-site caps kept (S24 CL-5, C-05).** ModArithmetic and Integral read `ENGINE_THREADS` only
through `Engine/Threads.h`; each site keeps its own preset, so no thread count, and hence no RSS prediction per thread count
(`PredictCharpolyRss(…, threads, …)`, the tables above), moves. One variable still yields these counts in one process: the tape
pool and consumer pool `kThreadPool` (strtoul; default = hardware; cap 32); the descent Smith pool `smithpar` `kSmithPar`
(strict, warns; default = CPU affinity, capped 64; an explicit value capped 256); the descent assembly `par::Threads()`
`kDescentParAsm` (default = hardware; cap 256); the descent CRT residue / Garner workers `kCap16` (cap 16). On a 128-core node
with no `ENGINE_THREADS` that is 32 / 64 (or the affinity count) / 128 / 16: kits that need one figure set `ENGINE_THREADS`.

## CheckThread startup crash on kernel 6.18 (2026-10-18)

The `CheckThread` binary segfaulted before `main` (NULL in `__tsan_func_entry`): the `target_clones` ifunc resolvers of
`Ring3k.cpp` were TSan-instrumented and ran at relocation time, before libtsan init. Fixed by disabling `target_clones`
under `__SANITIZE_THREAD__` (value-neutral, TSan build only). Run as before (`setarch x86_64 -R`, or `tsan_run.sh`);
`-R` remains required on this kernel (otherwise "unexpected memory mapping"; the root-only alternative is
`sysctl vm.mmap_rnd_bits=28`, not needed). Any future `target_clones` / `ifunc` use must be guarded the same way.
Record and proof: `KNOWN_ISSUES.md` ("CheckThread (TSan) startup crash"). Build about 10 min at `make -j4`.

## Benchmarking (`--bench`)

`./hacs --bench <mode> <args...> [--repeat k] [--cross-checks]` drives the shipped
pipeline through the **public API only** (same code paths as `--all`), printing phase-split
timings, peak RSS and one machine-readable `BENCH ...` summary line. For a *sweep* rather than one
point use `--campaign`. Modes (`--bench --help`): `cohom <n> <ell>`, `hecke <n> <ell> <p>`,
`family <n> <ell> <p> <r>`, `decomp <n> <ell> <p>`, and `micro <op> <args...>`
(`--bench micro --help`: `gemm`, `gemv`, `rref`, `kernel`, `transpose`, `suite`, `cuda`).
`micro` takes `--backend legacy|engine|gpu`, **default `engine`** (overridable by
`ENGINE_BACKEND`): `legacy` is the *pre-Phase-2* substrate end to end, so the two columns are a
like-for-like before/after and equal `checksum=` values across them are a bit-identity statement;
`gpu` selects the `engine::cuda` kernels (`rref` / `kernel` stay CPU-driven and report "not
available", exit 2, as does every `gpu` op without a usable device). **Use an even `n_sym`** — odd
`n` vanishes on this model (the −I / odd-n gap). Flags: `--count-allocs` (adds `allocs=` /
`alloc_bytes=`, one pipeline run rather than the process total; `alloc_bytes` is *requested* bytes,
`rss_mb` is the peak), `--lean` (the memory-lean configuration — `A^{(q)}` unchanged, `lean=1` on
the line), `cmake -DENGINE_COUNT_OBJECTS=ON .` (`flat_ctors=` / `block_ctors=`),
`ENGINE_TRACE_RSS=1` (VmRSS/VmHWM per phase and per `compute_cohomology_block()` step),
`ENGINE_TRACE_ELIM=1` (the tape elimination driver's host / compile / run split with the
host-serial `PANEL_RREF` share). The full text of this surface, including how `--count-allocs`
counts, is in `docs/performance-reference.md`.

**The numbers an agent needs** (2026-09-06 reference, `--repeat 5`, quiet box, 16 threads):
`hecke 128 134217757 2` → **0.1246 s / 112 MB**; `hecke 256` → **0.5608 s / 374 MB**;
`cohom 128` → **0.0894 s / 57 MB**; `micro gemm 512` → **30.3 Gmodmul/s**;
`micro rref 1677 1419` → **0.0559 s**. The **standing gates** are
`--bench hecke 256 134217757 2` **≤ 0.470 s** (0.460 s through slot 7) and `--bench decomp 128 134217757 2`
**≤ 0.109 s**, **plus a paired-ratio regression guard**: the median NEW/REF per-round ratio against the
previous slot's reference binary (`standing_gate_h2h.sh`, 13 alternating rounds, `--repeat 5`, min,
`ENGINE_THREADS=16`) must be **≤ 1.04** on both. **Owner ruling of 2026-09-23 (the slot-7 close, W4)**: the `hecke 256` gate is **loosened to `≤ 0.470 s`**, and a **paired-ratio regression guard** is added — the median NEW/REF per-round ratio against the previous slot's reference binary must be **`≤ 1.04`**, on both standing benchmarks. The owner declined a quiet re-run (the box was in use), after W4 measured `hecke 256` at 0.4604 s against
the old 0.460 s with the reference binary at 0.4638 s in the same rounds (paired ratio 0.999) —
load, not a package; `[X]` v1.11 `[OD]` S7-G.
The **post-slot-5 reference** (2026-09-22, tree `d362c71`, 13 alternating pairs against a binary
built out-of-source from the slot-5 baseline `2b1b339`, `--repeat 5`, min, `ENGINE_THREADS=16`,
quiet box) is `hecke 256` **0.4276 s** (baseline 0.4242 in the same pairs) and `decomp 128`
**0.0962 s** (baseline 0.0955) — both gates met with **7.0 %** and **11.7 %** headroom, and
**no drift**: the paired NEW/REF ratio has mean **1.001** on both arms with the deltas straddling
zero (NEW slower in 7 of 13 `hecke` pairs and 6 of 13 `decomp` pairs) against a per-arm spread of
≈ 4 %. This matters more than usual because slot-5 WP-6 changed a hot path (the `ρ_n` memo),
and the measurement says it did not reach these two benchmarks — as designed: the public
one-argument apply overloads still build a fresh table. The fitted exponent of total
time in `n_sym` is **1.72** (`hecke`) / **1.63** (`cohom`) over `{64, 96, 128}` — far under the
**≤ 3.2 permanent guard, which is defined over that same `n`-set `{64, 96, 128}`** — and **2.05**
over `{96 … 256}` (a second, ungated figure).
The **post-slot-6 reference** (2026-09-22, the slot-6 close tree against a `bd84016` binary built
out-of-source, `docs/matrix-engine/tools/slot6_close_window.sh` step 1: `13`
alternating pairs, `--repeat 5`, min, `ENGINE_THREADS=16`, quiet box) is `hecke 256`
**0.4051 s** (baseline 0.4099 s) and `decomp 128` **0.0936 s** (baseline 0.0922 s) — **both gates met, no flag**, with **11.9 %** and **14.1 %** headroom, paired median NEW/REF
ratio **0.995** (NEW slower in 5 of 13 rounds) and **1.012** (8 of 13) — inside the ≈ 4 % spread, so
**no drift** from slot 6.
The **post-slot-7 reference** (2026-09-23, the slot-7 close tree against a `d7f1549` binary — the
slot-7 base, code-identical to `ff68c55` — built out-of-source,
`docs/matrix-engine/tools/slot7_close_window.sh` step 1: 13 alternating pairs, `--repeat 5`, min,
`ENGINE_THREADS=16`) is `hecke 256` **0.4604 s** (baseline 0.4638 s) and `decomp 128` **0.1003 s**
(baseline 0.0995 s) — paired median NEW/REF **0.999** (NEW slower in 6 of 13 rounds) and **0.991**
(4 of 13): **no drift**, and NEW is not slower than REF. The window opened at load 6.8 / 11.1 / 14.2
(the tail of the close's gate runs), which lifted **both** binaries (`hecke 256` REF 0.4638 s against
0.4099 s at the slot-6 close); `hecke 256` read 0.1 % over the old 0.460 s gate, and the owner ruled
the gate loosened to 0.470 s with the ratio guard above — **both standing gates MET** under it
(2.0 % and 8.0 % headroom; ratios 0.999 / 0.991 ≤ 1.04).
The **post-slot-8 reference** (2026-09-24, the slot-8 close tree against a `3e7abbc` binary — the
slot-7 close, code `79b178f` — built out-of-source, `docs/matrix-engine/tools/slot8_close_window.sh`
step 1, `standing_gate_h2h.sh --gate`: 13 alternating pairs, `--repeat 5`, min,
`ENGINE_THREADS=16`) is **hecke 256 **0.4393 s** (REF `3e7abbc` 0.4422 s), paired median NEW/REF **0.994** (NEW slower in 6 of 13 rounds), headroom 6.5 %; decomp 128 **0.0967 s** (REF 0.0979 s), ratio **0.983** (5 of 13), headroom 11.3 % — `abs_gate=MET ratio_guard=MET`, verdict **MET** on both**. Indicative in-slot pairs (shared box,
WP-3, WP-6b, WP-L1) kept the ratio guard on both arms (0.956–1.011). `--bench` refuses a
non-default `coefficient_ring` at `RunMode`'s entry (slot-8 WP-3); no bench switch for it exists.
The **post-slot-9 reference** (the slot-9 close tree against a `bd6d1bb` binary — the slot-8 close —
built by `docs/matrix-engine/tools/slot9_close_window.sh` step −2, step 1
`standing_gate_h2h.sh --gate`, 13 alternating pairs, `--repeat 5`, min, `ENGINE_THREADS=16`, with the
box watcher running and the overlap table appended) is **hecke 256 new_min 0.4385 s (REF 0.4440), paired median ratio 0.995, headroom 6.7 %; decomp 128 new_min 0.0937 s (REF 0.0933), ratio 1.004, headroom 14.0 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`** (quiet box: no foreign process, Lean < 5 % in every watcher row, all 26 rounds clean). T2 `(10, 691)` 1.054 NOT_MET (the REF ext time is 0.12 ms, the cell is ext-ungated), `(160, 691)` 1.013 MET; T-C4 0.951 s ≤ 5 s MET. Indicative in-slot pairs on a shared box (WP-3, WP-4, WP-6, WP-7) kept the
ratio guard on both arms (0.930–1.082 at load ≈ 25; 0.990 / 0.990 at WP-7's lower load).
`--bench ext … --campaign-cell` prints `cone_s=` / `iota_s=` / `proof_range_s=` since slot-9 WP-7
(L5); read a compile-side lever on the **cold** first repeat, since the program cache serves repeats 2+.
**Window instruments** (slot-9 WP-5, `docs/matrix-engine/tools/`): `box_watch.sh` (a read-only
sampler: load, `lean|lake` CPU/RSS, `foreign_heavy`, top five), `prewindow_check.sh` (lists foreign
long-running processes, never signals one), per-round `t_start=` / `t_end=` on
`standing_gate_h2h.sh` and `ext_driver_h2h.sh` sample lines, and `window_overlap.py` (marks each
round clean / overlapped and re-derives the verdict on the clean rounds, `verdict_changes=`).
The **post-slot-10 reference** (the slot-10 close tree against a `2ac9ee8` binary — the slot-9 close —
`docs/matrix-engine/tools/slot10_close_window.sh`, step 1 `standing_gate_h2h.sh --gate`, 13 alternating
rounds, `--repeat 5`, min, `ENGINE_THREADS=16`; T2 against `2ac9ee8` and T2-D against `bd6d1bb`) is
**hecke 256 new_min 0.4419 s (REF 0.4504), paired median ratio 0.985, headroom 6.0 %; decomp 128 new_min 0.0947 s (REF 0.0972), ratio 0.976, headroom 13.1 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `2ac9ee8`: (10, 691) 0.7365 MET, (160, 691) 0.9744 MET; T2-D against `bd6d1bb`: (10, 691) 0.7594, (160, 691) 0.9808 (reported); T-C4 1.39 s ≤ 5 s MET**. Indicative in-slot pairs on a shared box (WP-3, WP-6, WP-7) kept the ratio
guard on both arms (0.988–1.015). **The placement lesson** (slot-10 WP-6): slot 9's T2 `(10, 691)` miss
was the static `ThreadPool::global()` pool landing at 0 mod 64 in `.bss` after an unrelated merge (the
registry mutex straddling two cache lines; the cell runs 52 558 parallel regions per repeat), not code —
fixed by `alignas(64)` on `slots_` / `regions_` (`ce73c71`). **Compare two binaries only when both place
the pool alike** (`nm -S <bin> | grep _ZZN6engine4tape10ThreadPool6globalEvE4pool`); a REF older than
`ce73c71` does not pin the layout.
The **post-slot-11 reference** (the slot-11 close tree against an `a3ca7b4` binary — the slot-10 close,
which pins the layout — `docs/matrix-engine/tools/slot11_close_window.sh`, step 0
`pool_placement_check.sh <NEW> <REF>` (slot-11 WP-1; `PLACEMENT a=… b=… verdict=SAME|DIFFER`, a `DIFFER`
stops the window), step 1 `standing_gate_h2h.sh --gate`, 13 rounds; T2 against `a3ca7b4`; no T2-D) is
**hecke 256 new_min 0.4434 s (REF 0.4476), paired median ratio 1.007, headroom 5.7 %; decomp 128 new_min 0.0948 s (REF 0.0940), ratio 1.011, headroom 13.0 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `a3ca7b4`: (10, 691) 1.0011 MET, (160, 691) 0.9923 MET; T-C4 1.452 s ≤ 5 s MET** (placement `SAME`; all 13 + 13 + 5 + 5 rounds clean; 2026-09-25 W1, quiet box).

The **post-slot-12 reference** (the slot-12 close tree `28f73ca` against a `9d08a30` binary — the slot-11 close,
built from a detached worktree; `slot12_close_window.sh`, step 0 placement, step 1 `standing_gate_h2h.sh --gate`,
13 rounds; T2 against `9d08a30`; run by slot-12 WP-9) is **hecke 256 new_min 0.4095 s (REF 0.4037), paired median ratio 1.004, headroom 12.9 %; decomp 128 new_min 0.0926 s (REF 0.0912), ratio 1.013, headroom 15.0 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `9d08a30`: (10, 691) 1.0109 MET, (160, 691) 1.0170 MET; T-C4 1.480 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; 2026-09-26 W1, quiet box).**

The **post-slot-13 reference** (the slot-13 close tree against a `032c27c` binary — the slot-13 base, built from a
detached worktree; `slot13_close_window.sh`, step 0 placement, step 1 `standing_gate_h2h.sh --gate`, 13 rounds; T2
against `032c27c`; run by slot-13 WP-15) is **hecke 256 new_min 0.4077 s (REF 0.4051), paired median ratio 0.997, headroom 13.3 %; decomp 128 new_min 0.0923 s (REF 0.0926), ratio 1.002, headroom 15.3 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `032c27c`: (10, 691) 1.0007 MET, (160, 691) 0.9934 MET; T-C4 2.241 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; 2026-09-27 W1, quiet box).**

The **post-slot-14 reference** (the slot-14 close tree, WP-17's `RelWithDebInfo` build of `6152168`, against an `e8ec72d` binary — the slot-13 close after the owner ratification, code-identical to `db976db`, later than `ce73c71` so it pins the pool layout; `slot14_close_window.sh`, step 0 placement, step 1 `standing_gate_h2h.sh --gate`, 13 rounds; T2 against `e8ec72d`) is **hecke 256 new_min 0.3951 s (REF 0.4144), paired median ratio 0.983, headroom 15.9 %; decomp 128 new_min 0.0906 s (REF 0.0912), ratio 0.976, headroom 16.9 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `e8ec72d`: (10, 691) 0.5619 MET, (160, 691) 0.9372 MET; T-C4 2.330 s <= 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; R-E8 reported: 0.174 / 0.351 / 0.869 s at m = 134217757 / 2147483647 / 4294967291; 2026-09-29 W1).** The window ran on a quiet box at its start (other_procs 0, Lean < 5 % in all 1110 watcher rows), but 177 watcher rows flagged a foreign heavy process during the run; the overlap attribution nevertheless marked every round clean. The script's step -2 REF build aborted the first attempt at step 0 (its `build_ref` progress output is captured by the command substitution that should return only the binary path, so the placement check got a garbage path); the REF binary it had built (sha256 `55bf452c...8f18`) was reused with `--ref-bin` in the second, full run — nothing else changed. The `(10, 691)` ratio 0.56 reflects the slot-14 `U_ell`-lever / parallel-setup work reaching that cell's total time (REF ext time 0.11 ms, the cell is ext-ungated).

The **post-slot-15 reference** (the slot-15 close tree `804aca7`, WP-18's `RelWithDebInfo` build, against a `7557127` binary — the slot-14 close, built by the script's own step −2 (`build_ref`'s stdout fix held: REF sha256 `f6809ef5…2f26`), later than `ce73c71` so it pins the pool layout; `slot15_close_window.sh`, step 0 placement, step 1 `standing_gate_h2h.sh --gate`, 13 rounds; T2 against `7557127`) is **hecke 256 new_min 0.4232 s (REF 0.4280), paired median ratio 0.996, headroom 10.0 %; decomp 128 new_min 0.0910 s (REF 0.0904), ratio 1.003, headroom 16.5 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `7557127`: (10, 691) 1.0067 MET, (160, 691) 1.0123 MET; T-C4 2.285 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; R-E8 reported: 0.181 / 0.356 / 0.878 s at m = 134217757 / 2147483647 / 4294967291; 2026-10-01 W1, quiet box: 0 `foreign_heavy` rows).** `hecke 256` reads higher than at the slot-14 W1 for both binaries: the REF here is the slot-14 close code, which measured 0.3951 s as NEW then and 0.4280 s now — box state, not code; the paired ratio in the same rounds is 0.996.

The **post-slot-16 reference** (the slot-16 close tree `edba09c`, WP-18 part B's `RelWithDebInfo` build, against a `b8a196d` binary — the slot-15 post-close tip
(W1 head `804aca7` + the two S15-O1 code commits), later than `ce73c71` so it pins the pool layout; `slot16_close_window.sh`, step 0 placement, step 1
`standing_gate_h2h.sh --gate`, 13 rounds; T2 against `b8a196d`) is **hecke 256 new_min 0.4230 s (REF 0.4317), paired median ratio 0.994, headroom 10.0 %; decomp 128 new_min 0.0897 s (REF 0.0921), ratio 1.000, headroom 17.7 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `b8a196d`: (10, 691) 1.0251 MET, (160, 691) 1.0040 MET; T-C4 2.323 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; R-E8 reported:
0.174 / 0.353 / 0.870 s at m = 134217757 / 2147483647 / 4294967291; 2026-10-02 W1, a quiet box (prewindow `foreign_count=0`, other_procs 0, 0 `foreign_heavy` and 0 Lean rows in 1672 watcher rows)).**

(The slot-17 … slot-20 W1 references are in `docs/implementation/slot-history.md`, suite-status entries; slot 20, quiet: hecke 256 0.3948 s (REF 0.4025), ratio 0.988;
decomp 128 0.0909 s (REF 0.0903), ratio 1.004.)

The **post-slot-21 reference** (added at the slot-21 close; the release commit `15b0d596`, a `RelWithDebInfo` build from the persistent checkout `s21/wp18/src`,
sha256 `a07b9d2a…`, against the slot-20 close binary (code of `df24fd35`, sha256 `46cf855a…`); `slot21_close_window.sh --run`, step 0 placement, step 1
`standing_gate_h2h.sh --gate`, 13 rounds, 16 threads; T2 against the same REF) is **hecke 256 new_min 0.4636 s (REF 0.4669), paired median ratio 0.995 (5 / 13
rounds NEW slower), headroom 1.4 % (`WITHIN_3PCT_OF_GATE`); decomp 128 new_min 0.0952 s (REF 0.0963), ratio 0.990, headroom 12.7 %; abs_gate MET, ratio_guard MET,
verdict MET on both; `verdict_changes=0`; T2: (10, 691) 0.9967 MET, (160, 691) 1.0103 MET; T-C4 3.067 s ≤ 5 s MET (placement `SAME`, a = b = 0; every round
`state=clean`; R-E8 reported: 0.1787 / 0.3583 / 0.8830 s at m = 134217757 / 2147483647 / 4294967291; 2026-10-06 W1, `PREWINDOW foreign_count=0`, `OVERLAP
watch_rows=2620 lean_gt5pct_rows=0 foreign_heavy_rows=0`).** **Box-speed caveat:** the same REF binary measured 0.4669 s here and 0.4025 s at the slot-20 W1,
i.e. the machine ran ≈ 15 % slower on 2026-10-06 than on 2026-10-05; the narrow absolute headroom is the box's, the paired ratio (0.995) is the regression
guard. Source: `docs/implementation/slot21/W1_report.md`.

Full reference tables, thread scaling, per-`n` RSS, `--lean` figures, campaign throughput, the
profiling knobs and the `ENGINE_BACKEND=legacy` 72×/93× comparison:
**`docs/performance-reference.md`** (baseline: `docs/matrix-engine/03-profiling-baseline.md`;
ledger: `docs/matrix-engine/perf-ledger.md`).


## Moved from CLAUDE.md at the slot-21 close (2026-10-07), verbatim — the configuration table (CheckThread / TSan detail) and the benchmarking section with the latest reference

The text below was replaced in CLAUDE.md by the slot-21 close size diet (owner request 2026-10-07: keep CLAUDE.md ≤ 30 KB); each block is the replaced text of CLAUDE.md at `1088dcb3`, unedited.

### "Available configurations" table and the out-of-source note (CLAUDE.md lines 79–93 at `1088dcb3`)

```
Available configurations (`-DCMAKE_BUILD_TYPE=...` on a fresh configure):

| Config | Flags | Use |
|---|---|---|
| `RelWithDebInfo` | `-O2 -g -DNDEBUG` | **default when `CMAKE_BUILD_TYPE` is unset**; everyday builds and validation runs |
| `Debug` | `-O0 -g` | debugging; this was the historical (and much slower) default of the stale cache |
| `Release` | `-O3 -DNDEBUG` | — |
| `Bench` | `-O3 -march=native -DNDEBUG` | timing / benchmark runs |
| `Check` | `-O1 -g -fsanitize=address,undefined` (no `NDEBUG`, so debug checks are live) | sanitizer runs |
| `CheckThread` | `-O1 -g -fsanitize=thread` (no `NDEBUG`) | ThreadSanitizer runs for the engine thread pool; on this WSL2 kernel TSan aborts with "unexpected memory mapping" unless ASLR is off: run as `ENGINE_CUDA_DISABLE=1 setarch x86_64 -R ./hacs <Name>` (TSan cannot see the uninstrumented CUDA driver's locking: driver-internal race reports, slot-17 close report §4.2). **GPU-visible run (slot-20 WP-8, C12):** `docs/matrix-engine/tools/tsan_run.sh <CheckThread binary> <outdir outside the tree> <Name>...` (thread-leak suppression `tsan_libcuda.supp`; `tsan_filter.py` sorts reports into DRIVER / OURS, exit 1 on any OURS; a blanket `race:libcuda` suppression is deliberately not used) |

To compare configurations, configure one build directory per configuration (builds are out-of-source only since the
slot-26 layout; an in-source `cmake .` is refused): `cmake -B <builddir> -S . -DCMAKE_BUILD_TYPE=Bench && make -C <builddir> -j16`.
The `cmake` on this box is a snap; after a WSL restart `/run/user/1000` is missing and the snap wrapper
fails unless `XDG_RUNTIME_DIR` is set — `/snap/cmake/current/bin/cmake` works without it (slot-9 WP-7).
```

### "Benchmarking (`--bench`)" (CLAUDE.md lines 351–371 at `1088dcb3`)

```
## Benchmarking (`--bench`)

`./hacs --bench <mode> <args...> [--repeat k] [--cross-checks]` drives the shipped pipeline through the
**public API only** (same code paths as `--all`), printing phase-split timings, peak RSS and one machine-readable
`BENCH ...` line. Modes (`--bench --help`): `cohom <n> <ell>`, `hecke <n> <ell> <p>`, `family <n> <ell> <p> <r>`,
`decomp <n> <ell> <p>`, `ext …`, and `micro <op> <args...>` (`gemm`, `gemv`, `rref`, `kernel`, `transpose`, `suite`,
`cuda`; `--backend legacy|engine|gpu`, default `engine`). **Use an even `n_sym`** — odd `n` vanishes on this model.
For a sweep use `--campaign`. Flags and the full surface: `docs/performance-reference.md`.

**Standing gates**: `--bench hecke 256 134217757 2` **≤ 0.470 s** and `--bench decomp 128 134217757 2` **≤ 0.109 s**,
**plus the paired-ratio regression guard**: the median NEW/REF per-round ratio against the previous slot's reference
binary (`standing_gate_h2h.sh --gate`, 13 alternating rounds, `--repeat 5`, min, `ENGINE_THREADS=16`) must be **≤ 1.04**
on both (owner ruling 2026-09-23). Permanent guard: fitted exponent of total time in `n_sym` over `{64, 96, 128}` ≤ 3.2.

**Latest reference (slot-21 W1, 2026-10-06, NEW = the close binary (the release commit `15b0d596`, sha256 `a07b9d2a…`) vs REF = the slot-20 close binary (code of `df24fd35`), placement `SAME`, `foreign_heavy_rows=0`, every round `state=clean` — a verdict)**: hecke 256 new_min **0.4636 s** (REF 0.4669) — abs gate MET with only **1.4 %** headroom (flag `WITHIN_3PCT_OF_GATE`), paired ratio **0.995** MET; decomp 128 new_min **0.0952 s** (REF 0.0963), ratio **0.990** MET (headroom 12.7 %); T2 `(10, 691)` 0.9967, `(160, 691)` 1.0103 MET; T-C4 3.067 s ≤ 5 s MET. **Caveat:** the whole box ran ≈ 15 % slower than at the slot-20 W1 (the same REF binary measured 0.4669 s now, 0.4025 s then), so the narrow absolute margin is the machine's, not a regression — the paired ratio is the regression guard. Slot-20 W1 (quiet, the box at its usual speed): hecke 256 0.3948 s (REF 0.4025), ratio 0.988; decomp 128 0.0909 s, ratio 1.004. (Slot-20 Q, the slot-19 binary quiet: hecke 0.4234 s, ratio 0.991. The slot-17 … 19 W1s were loaded.) The
post-slot-16 quiet reference (NEW `edba09c`: hecke 0.4230 s, decomp 0.0897 s) and earlier ones: `performance-reference.md`.

**The placement lesson**: compare two binaries only when both place the global thread pool alike
(`pool_placement_check.sh <NEW> <REF>`, or `nm -S <bin> | grep _ZZN6engine4tape10ThreadPool6globalEvE4pool`); a REF
older than `ce73c71` does not pin the layout. Window instruments: `box_watch.sh`, `prewindow_check.sh`,
`window_overlap.py` (`docs/matrix-engine/tools/`).
```
