<!-- SPDX-License-Identifier: CC-BY-4.0 -->
Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)

# HACS 0.2.1 build and regression results, 2026-11-14

Status: *computed* (all numbers below are measured on localhost, quiet box, one heavy job at a time).
Tree: `code/hacs/` in worktree `/home/janosch/dev/Langlandscape-wt/plan` (branch `wip-plan`), unmodified.
Logs (outside the repo): `/home/janosch/data/hacs-run/` (`cuda/`, `cpu/` shard logs, `*.log` per run).

## 1. Environment

| item | value |
|---|---|
| CPU / threads | AMD Ryzen 9 7950X, 16 cores / 32 threads (WSL2) |
| RAM | 82 GB total, about 66 GB free before the builds (`free -g`); never below 55 GB free during runs |
| Disk | `/` 326 GB free; `/mnt/c` 169 GB free (>= 50 GB, no warning) |
| GPU | NVIDIA RTX PRO 6000 Blackwell Max-Q Workstation Edition, 97887 MiB, cc 12.0, power limit 300 W, driver 591.86 |
| nvcc | `/usr/local/cuda-13.0/bin/nvcc`, release 13.0, V13.0.48 (put on `PATH` by hand; not on the default `PATH`) |
| host compiler | GCC 11.4.0 (Ubuntu 22.04) |
| CMake | 4.5.0 (`/snap/bin/cmake`) |
| HACS | `hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`; `./hacs --list` = 294 validations, `--all` = 246 (fast + standard) |
| build dirs | `code/hacs/build/minimal`, `code/hacs/build/cpu-only` (3.3 GB each; ignored by `/build*/`; `git status` shows nothing from them) |

## 2. CUDA build

```bash
export PATH=/usr/local/cuda-13.0/bin:$PATH
cd code/hacs
cmake --preset minimal                      # binaryDir = build/minimal
time cmake --build build/minimal -j16
build/minimal/hacs --version
```

Configure output (key lines):

```
-- The CXX compiler identification is GNU 11.4.0
-- The CUDA compiler identification is NVIDIA 13.0.48 with host compiler GNU 11.4.0
-- OC_ENABLE_CUDA=ON OC_BUILD_DOCS=OFF OC_BUILD_NOTEBOOK=OFF OC_ENABLE_LEGACY=OFF host=x86_64
-- Build configuration: RelWithDebInfo
-- Found CUDAToolkit: /usr/local/cuda-13.0/targets/x86_64-linux/include;... (found version "13.0.48")
-- Configuring done (10.0s)
```

`CMAKE_CUDA_ARCHITECTURES=120` (from `OC_CUDA_ARCHITECTURES`, default).
**CUDA detected and enabled: yes.** Result: PASS. Wall time of the build: **3 min 29.8 s** (`real 3m29.830s`, user 30m13s, sys 2m09s) at `-j16`;
free RAM stayed above 58 GB. (Earlier build in `s03-ct`: 8.6 min, presumably on a loaded box.) Two compiler warnings
(`SimplicialCohomology.cpp:861, :883`, signed/unsigned comparison), no errors. Binary: `code/hacs/build/minimal/hacs` (881 MB, RelWithDebInfo),
plus symlink `cohomology_app`.

## 3. Regression tests (CUDA build)

No ctest; the documented validations (`BUILDING.md` "Validating a build", `CLAUDE.md` "Validation"). Logs in `/home/janosch/data/hacs-run/`.

**3.1 `--all` in 4 shards** (documented `run_all_sharded.sh`, default N = 4; expected 523 s):

```bash
docs/matrix-engine/tools/run_all_sharded.sh build/minimal/hacs 4 --logs /home/janosch/data/hacs-run/cuda
```
```
SHARD 1/4 names=73 ... All validations PASSED (73/73 passed, shard 1/4).  exit=0
SHARD 2/4 names=57 ... PASSED (57/57)   SHARD 3/4 names=58 ... PASSED (58/58)   SHARD 4/4 names=58 ... PASSED (58/58)
union of the shards = roster: yes (246 planned, 246 in the roster, 0 duplicated)
SHARDED_ALL shards=4 passed=246/246 failed=0 mode=--all wall_s=634.6 ... verdict=OK
```
**PASS 246/246, 0 failures, 10 min 35 s wall.** `[FAIL]`/`[EXCEPTION]` strings in the logs are the engineered negative tests
(`PrivHarnessCatch*`, `HIDA_H2_TAMPER`, `MAZUR_EIS_NEGATIVE`: "captured", expected). The `[SKIP]` lines (19 in total) are by design:
`OC_ENABLE_LEGACY=OFF` (5 validations), `OC_BUILD_NOTEBOOK=OFF` (4), unset owner/dump env hooks, `*_ALL` census arms, and two `(D) GPU lane route: ENGINE_DEVICE != gpu (opt-in)` arms.

**3.2 Device validations** (the device roster of `--list`; all ran, none skipped as a whole):

```bash
ENGINE_DEVICE=gpu build/minimal/hacs CudaBitIdentityValidation CudaTransferValidation EngineCrossDeviceValidation \
  EngineCudaMemoryValidation EngineFingerprintDeviceBitValidation CudaImmaBitIdentityValidation CudaImmaElimValidation \
  GpuLeanSessionValidation DescentSmithGpuValidation          # rc 0, 76 s (same list without ENGINE_DEVICE: rc 0, 75 s)
ENGINE_DEVICE=gpu build/minimal/hacs EngineDeviceTrapValidation   # slow tier; rc 0, 7 s: 14 checks, 0 failed
```
Key lines: `fingerprints: cpu=0x6f hybrid=0xef gpu=0x1ef`; `DescentSmithGpuValidation: 12589 checks, 0 failing`;
`EFFECTIVE DEVICE_ELIM calls=884 device=883 fallbacks=1`; `EFFECTIVE GPU_SMITH2K ... device=5363 resident=3159 tiled=2204 ... verified=1`.
Only arm-level skips: `SKIP-ARM ... D-policy-off / F-imma-off / D-gpu-elim-off: OC_ENABLE_LEGACY=OFF` (retired rollback arms).
Note: `EngineDeviceTrapValidation` prints two throughput lines `target >= 20x: FAIL` (E1 9.2x, E2 18.5x, gpu 175/501 G vs cpu-1 19/27 Gmodmul/s);
these are informational speed targets, the validation itself reports `14 checks, 0 failed`, `[PASS]`.

**3.3 Golden reference and digests of record:**

| command | result | time |
|---|---|---|
| `GOLDEN_STRICT=1 hacs GoldenRegressionValidation` | tier A 12154 failing 0; tier B 6231 mismatching 0; PASS | 32 s |
| same with `ENGINE_DEVICE=gpu` | identical counts; PASS | 39 s |
| `EngineDeterminismValidation HeckeExtDeterminismValidation ConsoleDeterminismValidation HeckeBenchmarkSmoke` | digests `0x3dddd2ef9a8efd`, `0xaef77d786b4f29b4`, `+(128,5) 0x9ed8b83a2fb26622` equal CLAUDE.md values; `HeckeBenchmarkSmoke: COMPLETED and CERTIFIED`; PASS | 59 s |

Not run: `--all-full` (slow tier, about 1 h 45 min on the reference box).

## 4. CPU-only build + regression

```bash
cd code/hacs
cmake --preset cpu-only                        # OC_ENABLE_CUDA=OFF, nvcc never searched
time cmake --build build/cpu-only -j16
docs/matrix-engine/tools/run_all_sharded.sh build/cpu-only/hacs 4 --logs /home/janosch/data/hacs-run/cpu
```
- Configure: `OC_ENABLE_CUDA=OFF ... host=x86_64`, no CUDA lines. Build: **3 min 20.0 s** (user 30m14s), binary `code/hacs/build/cpu-only/hacs` (875 MB). PASS.
- `--all` sharded: `SHARDED_ALL shards=4 passed=246/246 failed=0 mode=--all wall_s=522.6 ... verdict=OK` (**8 min 43 s**). PASS 246/246.
  `[SKIP]` (no usable CUDA device) on: `CudaBitIdentity`, `CudaTransfer`, `EngineCrossDevice`, `EngineCudaMemory`, `EngineElimSession`, `CudaImmaBitIdentity`,
  `CudaImmaElim`, `GpuLeanSession`, `DescentSmithGpu` (whole validation, returns 0), plus device arms of ext / console / HeckeZ validations (`(C4 a) 16 device arms`, `(I) device = gpu`, `(D) GPU lane route`).
  `EngineFingerprintDeviceBitValidation` runs (8 checks, 0 failing; it needs no device).
- Golden strict (`GOLDEN_STRICT=1 ... GoldenRegressionValidation`): rc 0, 31 s, tier A 12154/0, tier B 6231/0. Digest group: rc 0, 52 s, same digests.
- The slow tier was not run on the CPU-only build (as `BUILDING.md` says it never was).

## 5. GPU vs CPU

One job at a time on a quiet box, `--repeat 2` (cohom/hecke) or `--repeat 3` (micro), min of repeats. Same inputs; the `BENCH` line carries the result dimensions, micro ops an FNV-1a-64 checksum.
Command pattern: `ENGINE_DEVICE=<cpu|gpu> <binary> --bench <mode> <args>`; logs `/home/janosch/data/hacs-run/b_*.log`.

| computation | CPU-only build | CUDA build, `ENGINE_DEVICE=cpu` | CUDA build, `ENGINE_DEVICE=gpu` | output identical? |
|---|---|---|---|---|
| `--bench cohom 1000 134217757 --lean` | 13.39 s, 1044 MB RSS | 13.25 s, 1044 MB | **11.69 s**, 1291 MB (1.13x) | yes: `dims=0,167,0 c_eq_dims=3837,9009,5005` |
| `--bench hecke 1000 134217757 2 --lean` | 13.54 s, 1247 MB | 13.50 s, 1258 MB | **11.92 s**, 1467 MB (1.13x) | yes: `dims=0,167,0` |
| `--bench micro gemm 2048` (engine vs `--backend gpu`) | 0.276 s = 31.2 Gmodmul/s (AVX-512) | 0.276 s = 31.1 G | **0.0011 s = 7900 Gmodmul/s** (about 254x; GPU time, operands resident) | yes: checksum `0x55668bbd11acfdb5` in all three |
| `--bench micro rref 4000 4000` | not run | 0.769 s = 41.7 Gmodmul/s, checksum `0x133fc71417d80ac5`, rank 4000 | n/a: "backend 'gpu' has no implementation of this op (elimination is CPU-driven)" (rc 2, expected) | n/a |

Whole-process walls: cohom/hecke 1000 pair of repeats about 27 s on CPU vs 24.6-24.9 s on GPU. The reference (`performance-reference.md`, RTX 5070 Ti) gives cohom 1000 cpu 14.1 / gpu 11.9 s: reproduced here (13.3 / 11.7 s).
Observed: the whole-pipeline GPU gain is modest (about 13 %); only the dense GEMM kernel gains two orders of magnitude. The CPU-only and CUDA-CPU builds perform identically.

## 6. Priority-1 checks

Run 2026-11-14 on the fresh binaries (`hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`), CUDA binary
`code/hacs/build/minimal/hacs` unless stated. Scripts were copy-pasted from `plan/hacs/CHECKS-NOW.md` §2 (extracted verbatim, no script
fixes needed) and run one at a time, `ENGINE_THREADS` as in the scripts. Scripts, logs and outputs: `/home/janosch/data/hacs-run/checks/`
(outside git; `rn1.log`, `rn2_6.log`, `a1_*`, `b3/b5/b1/b4/c1/b14.*`). RAM never below 60 GB free. No mathematical mismatch.

| Check | Result | Wall time | Max RSS |
|---|---|---|---|
| RN-1 (A1) acceptance battery + CPU/GPU hashes | PASS (steps 1-7) | 233 s (steps 1-4) + 16 s + 1.6 s + 0.5 s; CPU-only build step ~10 s | 0.54 GB |
| RN-2 (B3 + B5) Eisenstein congruence modules | PASS | 123 s total (B3 ~116 s, B5 ~7 s) | 0.19 GB |
| RN-3 (B1 + B2) Eichler class number, Brandt vs Gamma_0(p) | PASS (42/42 primes) | 252 s (HACS 11.0 s, rest Python) | 0.44 GB |
| RN-4 (B4) JL with Sym^{k-2} | PASS (61/61 cells) | 153 s (HACS 70 s) | 0.65 GB |
| RN-5 (C1) HACS vs PARI on Gamma_0(M) | PASS (232 cells, 696 charpolys) | 317 s (HACS 315 s) | 0.75 GB |
| RN-6 (B14) T4, q = 3, p = 17 | PASS | 1.8 s | 0.16 GB |

### RN-1 (A1): acceptance battery

- Commands: the five steps of `CHECKS-NOW.md` RN-1 verbatim (blocks in `blk0.sh` .. `blk3.sh`).
- Step 1 `GOLDEN_STRICT=1 GoldenRegressionValidation`: exit 0; `tier A checked 12154, failing 0; tier B checked 6231, mismatching 0`.
  Source of truth: `GoldenReference.inc` (CLAUDE.md of HACS: 12154 / 6231). PASS.
- Step 2 gate: failures=0. `HeckeBenchmarkSmoke: COMPLETED and CERTIFIED (aggregate failing case(s) = 0)`;
  `EngineDeterminismValidation` digest `0x3dddd2ef9a8efd` (all 8 thread/batch arms equal); `HeckeExtDeterminismValidation`
  `digest=0xaef77d786b4f29b4`, `failing_arms=0`; `ConsoleDeterminismValidation` C4 (a) `0xf6ed04bbe8e6b60a` in all cpu/hybrid/gpu arms.
  All match the digests of record. `HeckeEndToEndValidation`, `HeckeBadPrimeValidation` `[PASS]`. (Arm b of ConsoleDeterminism is
  `SKIP-ARM ... OC_ENABLE_LEGACY=OFF`, a build option, not a device skip.) PASS.
- Step 3 (8 JL-related validations): failures=0, all `[PASS]`. Step 4 device validations (`CudaBitIdentityValidation`,
  `EngineCrossDeviceValidation`, `DescentSmithGpuValidation`): failures=0, 3 `[PASS]`, `grep -c '[SKIP]'` = 0, i.e. they ran. PASS.
  Wall time of steps 1-4 together: 233 s (not timed separately).
- Step 5 (CPU vs GPU record hashes), cases (1,30), (11,10), (37,4), (30,2), `descent` over Z, `record digest` printed per case:
  - CUDA binary, `ENGINE_DEVICE` default (cpu) vs `ENGINE_DEVICE=gpu ENGINE_GPU_SMITH2K_MIN=0`: `DEVICE-IDENTICAL`.
    The GPU run reports `EFFECTIVE GPU_SMITH2K mode=on policy_gpu_calls=28 device=28 resident=28 ... fallbacks=0`, so the GPU route was really used.
  - The separate CPU-only build `build/cpu-only/hacs` (no CUDA code) vs the CUDA build on the GPU route: `CPUONLY-vs-GPU-IDENTICAL`
    (also identical to the CUDA binary's CPU route). Digests: (1,30) `0x6b6dd11c0cdffdfb`, (11,10) `0xdcfaaf3893142cf7`,
    (37,4) `0xe398e9ce071f1e4a`, (30,2) `0xeb6a73c6dc8b6003`.
  - H^1(1,30) = `Z^5 + Z/2 + Z/2 + Z/2 + Z/2^2 + Z/2^2 + Z/2^2 + Z/3 + Z/3 + Z/3^2 + Z/5^2 + Z/29`, equal to the expected value from
    `docs/latex/cli_manual_runs/env_descent_gpu.txt`. PASS. Wall: 16 s for both CUDA-binary runs; the CPU-only run took a few seconds (not timed separately).
- Step 6 regression against 0.2.0 answers: `hacs_level_n_xcheck IDENTICAL`, `hacs_level_n_xcheck_ext IDENTICAL`. PASS (1.6 s).
- Step 7 campaign hashes: `EFFECTIVE campaign arm=descent cells=6 ran=6 ... failed=0`, `CAMPAIGN-IDENTICAL` to
  `campaign_z_run.txt` (six `record_fnv1a64`). PASS (0.5 s).

### RN-2 (B3 + B5): Eisenstein congruence modules over Z

- Commands: `ENGINE_THREADS=4 $B --script b3_mazur.oc`, `b3_post.py`; `b5_bernoulli.oc`, `b5_post.py`.
- B3 (weight 2, anemic, prime p in [11, 199], 42 primes). Expected C_T = Z/num((p-1)/12) (Mazur 1977, Ch. II, cited; numbering not
  re-checked). Result: `certified=36 bounded=5  ALL CONSISTENT: True`. 36 primes certified and equal to num((p-1)/12) (p = 11 gives
  `certified:0x5`, equal to HACS's own transcript 060); p = 13 gives `C_T = "-"` (n = 1). The five non-certified primes carry
  `upper_bound_certified`, with per-ell bounds `ell:[lower_v, upper_v]` (= exact, ~ open) against the Mazur value v:
  - p = 113 (n = 28): 2:[2,2]=, 3:[0,3]~ (v=0), 7:[1,1]=, 13:[0,0]=
  - p = 157 (n = 13): 2:[0,1]~ (v=0), 13:[1,1]=
  - p = 191 (n = 95): 5:[1,1]=, 11:[0,1]~ (v=0), 19:[1,1]=
  - p = 197 (n = 49): 2:[0,2]~ (v=0), 7:[2,2]=
  - p = 199 (n = 33): 3:[1,1]=, 11:[1,2]~ (v=1), 149:[0,0]=
  All consistent with Mazur; same picture as the old-binary probe. PASS (~116 s).
- B5 (level 1, k = 12, 14, ..., 32, Z-full Hecke algebra). Expected C_T = Z/num(B_k/2k) (Ribet 1976, Mazur-Wiles; cited; HACS 060 pins
  k = 12 and 24). Result `ALL AGREE: True`, all eleven k certified, e.g. k = 30: `0x19134d4ece1` = 1721 * 1001259881. PASS (~7 s).

### RN-3 (B1 + B2): class numbers and Brandt vs Gamma_0(p), weight 2

- Command: `python3 b1_brandt_vs_hacs.py $B $PYLL <42 primes 11..199>`. Last line
  `{"check": "B1+B2", ..., "all_ok": true, "hacs_wall_s": 10.96}`, exit 0.
- Per prime: Eichler class number formula, mass (p-1)/24, rank H^1 = 2h-1, and char_HACS(T_q)(x-1-q) = char_Brandt(T_q)^2 for q = 2, 3, 5, 7
  all hold, p = 11..199. Source of truth: Eichler formula (cited), our `brandt.py`. PASS (252 s total).

### RN-4 (B4): JL with Sym^{k-2} coefficients

- Command: `python3 b4_symn_jl.py $B $PYLL`. Result: `"n_cells": 61, "all_ok": true, "bad": []`, HACS 70.0 s, total 152.8 s.
  Identity char_HACS(Gamma_0(D)) = char_Brandt^2 * char_HACS(SL_2(Z))^2 holds in all 61 cells (D prime <= 43, k = 4..12 even,
  (D+1)(k-1) <= 300). Source of truth: our `symn.py` (Brandt side), cited Eichler/JL. PASS.

### RN-5 (C1): exact HACS charpolys vs PARI

- Command: `python3 c1_hacs_vs_pari.py $B 60 2,4,6,8,10,12`. Result:
  `{"check": "C1", "cells": 232, "charpolys": 696, "all_ok": true, "bad": [], "hacs_wall_s": 314.6, "total_s": 317.2}`.
  Source of truth: PARI 2.15.4 (`mfinit` flags 1 and 3, `mfheckemat`) via cypari2 plus Eichler-Shimura. Ranks and Eisenstein dimensions also agree. PASS.

### RN-6 (B14): T4, q = 3, p = 17, branch through Delta

- Command: `ENGINE_THREADS=4 $B --script b14_t4.oc`, `b14_post.py`. Result: `ord17_c3 = [1]` at k = 12, 28, 44, 60 (expected 1, seed prediction
  1 for these k; k = 124 out of reach). Branch degree in T_3: 1 in all four weights. Remark (as in the old probe): at k = 60 T_2 sees two
  17-adic roots congruent to tau(2) (`branch_degrees_T2 = [1, 1]`), T_3 only one. PASS (1.8 s).
