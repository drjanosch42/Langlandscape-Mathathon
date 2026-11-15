<!-- SPDX-License-Identifier: CC-BY-4.0 -->
Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)

# Job spec for TITAN: `hacs-build-01` — build and validate HACS 0.2.1 (CUDA)

Job id: `hacs-build-01`. Node: TITAN (clone `/home/claude/dev/Langlandscape`; 16 threads, 94 GB RAM; same GPU model as localhost: RTX PRO 6000 Blackwell Max-Q 96 GB, cc 12.0).
Source: branch `wip-plan` of the global master's push (the tree `code/hacs/`, HACS 0.2.1). TITAN pushes results **only** to `titan/hacs-build-01`.
Reference run (localhost): `plan/hacs/checks-results-2026-11-14.md`.

## Hard rules
- Do **not** touch the Lean pins (no `lake update`, `lake clean`, `lake exe cache get`, no toolchain/manifest change) and do **not** build or touch `code/hacs/lean`.
- Do **not** modify any tracked file under `code/hacs/` (upstream read-only); never set an owner-gated emitter env var (`GOLDEN_EMIT`, `CONSOLE_EMIT_EXPECTED`, `HECKE_DUMP_*`, ...).
- Build directory and logs outside the committed tree: `code/hacs/build/minimal` is git-ignored (`/build*/`); logs go to `$HOME/data/hacs-run/` and only a small report file is committed.
- One heavy job at a time. Keep >= 12 GB RAM free (`free -g`); `/` must have >= 20 GB free.

## 1. Prerequisites (check and report; stop and report if one fails)
```bash
nvidia-smi --query-gpu=name,driver_version,compute_cap,memory.total --format=csv    # expect cc 12.0, driver supporting CUDA 13.0 (>= 580)
ls /usr/local/cuda-13.0/bin/nvcc && /usr/local/cuda-13.0/bin/nvcc --version | tail -2   # expect release 13.0 (12.9 also acceptable; >= 12.8 needed for sm_120)
cmake --version | head -1      # >= 3.21 (presets); localhost 4.5.0
gcc --version | head -1        # GCC 11.4 or 13.3 tested
python3 --version; git --version; free -g; df -h $HOME
```
If CUDA 13.0 is not installed: report; do not install system packages without the global master. If nvcc is only at another path, use
`-DCMAKE_CUDA_COMPILER=<path>` as in BUILDING.md (a) and note it.

## 2. Commands
```bash
cd /home/claude/dev/Langlandscape
git fetch origin && git checkout -B titan/hacs-build-01 origin/wip-plan     # or the ref named in the outbox file
export PATH=/usr/local/cuda-13.0/bin:$PATH
cd code/hacs
cmake --preset minimal 2>&1 | tee $HOME/data/hacs-run/cfg.log           # expect OC_ENABLE_CUDA=ON, CUDA 13.0.48, arch 120
( time cmake --build build/minimal -j16 ) > $HOME/data/hacs-run/build.log 2>&1
build/minimal/hacs --version
git status --short                                                       # must show nothing from build/

mkdir -p $HOME/data/hacs-run/cuda
docs/matrix-engine/tools/run_all_sharded.sh build/minimal/hacs 4 --logs $HOME/data/hacs-run/cuda      # --all in 4 shards
ENGINE_DEVICE=gpu build/minimal/hacs CudaBitIdentityValidation CudaTransferValidation EngineCrossDeviceValidation \
  EngineCudaMemoryValidation EngineFingerprintDeviceBitValidation CudaImmaBitIdentityValidation CudaImmaElimValidation \
  GpuLeanSessionValidation DescentSmithGpuValidation EngineDeviceTrapValidation
GOLDEN_STRICT=1 build/minimal/hacs GoldenRegressionValidation
GOLDEN_STRICT=1 ENGINE_DEVICE=gpu build/minimal/hacs GoldenRegressionValidation
build/minimal/hacs EngineDeterminismValidation HeckeExtDeterminismValidation ConsoleDeterminismValidation HeckeBenchmarkSmoke
# GPU vs CPU spot checks (one at a time):
ENGINE_DEVICE=cpu build/minimal/hacs --bench cohom 1000 134217757 --lean --repeat 2
ENGINE_DEVICE=gpu build/minimal/hacs --bench cohom 1000 134217757 --lean --repeat 2
build/minimal/hacs --bench micro gemm 2048 --repeat 3
build/minimal/hacs --bench micro gemm 2048 --backend gpu --repeat 3
```
Expected wall times scale with the machine (TITAN has 16 threads vs 32 on localhost): the build was 3.5 min on localhost at `-j16` (expect 4-8 min on TITAN);
the sharded `--all` 10.6 min with 32 threads (expect 15-25 min).

## 3. Expected results (localhost, 2026-11-14)
- Configure: CUDA compiler `NVIDIA 13.0.48 with host compiler GNU 11.4.0`, `OC_ENABLE_CUDA=ON`, `CMAKE_CUDA_ARCHITECTURES=120`, version string `hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`; two harmless signed/unsigned warnings in `SimplicialCohomology.cpp`.
- `SHARDED_ALL shards=4 passed=246/246 failed=0 mode=--all ... verdict=OK`; 19 `[SKIP]` lines are by design (legacy off, notebook off, unset hooks, opt-in GPU lane arms).
- Device list: all pass (`DescentSmithGpuValidation: 12589 checks, 0 failing`; `fingerprints: cpu=0x6f hybrid=0xef gpu=0x1ef`; `EngineDeviceTrapValidation: 14 checks, 0 failed`; its two `target >= 20x: FAIL` throughput lines are informational and may vary).
- Golden strict: `tier A checked 12154, failing 0; tier B checked 6231, mismatching 0`, on cpu and gpu.
- Digests: `0x3dddd2ef9a8efd`, `0xaef77d786b4f29b4`, `0x9ed8b83a2fb26622`; `HeckeBenchmarkSmoke: COMPLETED and CERTIFIED`.
- Bench: `cohom 1000 --lean` dims `0,167,0 c_eq_dims=3837,9009,5005` on cpu and gpu (13.3 s vs 11.7 s on localhost); `micro gemm 2048` checksum `0x55668bbd11acfdb5` on both backends (31 vs 7900 Gmodmul/s).
- The results must match on every digest, count and checksum; only timings may differ.

## 4. Report back (commit one file `plan/hacs/titan-hacs-build-01-report.md` on `titan/hacs-build-01`, with `<!-- SPDX-License-Identifier: CC-BY-4.0 -->`)
Prerequisite versions (driver, nvcc, cmake, gcc), configure key lines (CUDA enabled? arch?), build wall time, `SHARDED_ALL` line, each command's rc and wall time,
every `[FAIL]` or unexpected `[SKIP]` verbatim, the golden/digest lines, the bench numbers (BENCH lines), peak RAM observed, anomalies. No logs larger than a few hundred KB; no binaries; nothing from `build/`.
Push only `titan/hacs-build-01`; notify the global master.

## 5. Recommendation: should TITAN get a build?
Pros: a second Blackwell GPU (96 GB) and 94 GB RAM for long sweeps and parallel CUDA jobs, independent of localhost (which is reserved for HACS work and is the only box with 32 threads);
the build is cheap (about 4-8 min, 3.3 GB) and reproducible with the exact commands above; it proves the HACS build is portable (a second workstation was already verified with CUDA 12.9 upstream);
TITAN is idle apart from Lean jobs, and a GPU there takes load off localhost.
Cons: TITAN has only 16 threads, so CPU-bound parts (most of the tier, the cohom/hecke pipeline: GPU speedup there is only about 1.13x) run about 2x slower; Lean jobs are currently routed to TITAN and a 20-minute
validation run competes for its CPU (use one at a time, leave Lean runs first); a source tree plus 3.3 GB build adds a second place to keep in sync; wall-clock gains arise only for GPU-heavy runs
(dense GEMM, device Smith LU / descent cells), so a long sweep must be GPU-bound to profit.
Recommendation: **yes, do the one-off build and validation** (cheap, low risk) so TITAN can run long single-GPU HACS jobs while localhost keeps interactive work; schedule it in a quiet gap between Lean jobs, and decide on regular GPU sweeps only after the first priority-1 checks show which are GPU-bound.
