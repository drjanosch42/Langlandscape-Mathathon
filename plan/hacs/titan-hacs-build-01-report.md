<!-- SPDX-License-Identifier: CC-BY-4.0 -->
Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)

# Report on `hacs-build-01` (TITAN): HACS 0.2.1 build and validation with CUDA

Source: `origin/main` at `0bb3961` (tree `code/hacs/`, HACS 0.2.1), worktree `/home/claude/dev/Langlandscape-hacs`, branch `titan/hacs-build-01`.
Run date: 2026-11-14/15. Logs in `$HOME/data/hacs-run/` on TITAN (not committed).

## Prerequisites
- GPU: NVIDIA RTX PRO 6000 Blackwell Max-Q Workstation Edition, driver 610.88, compute capability 12.0, 97887 MiB.
- CUDA: **13.0 is not installed.** The system `nvcc` is `/usr/local/cuda-12.6` (12.6.85, below the 12.8 needed for sm_120). A user-level
  **CUDA 12.9.86** toolkit exists at `$HOME/cuda-12.9` (no system package was installed); it was used via
  `-DCMAKE_CUDA_COMPILER=$HOME/cuda-12.9/bin/nvcc`, `PATH` and `LD_LIBRARY_PATH` as in BUILDING.md (a). 12.9 is accepted by the spec.
- cmake 4.5.0, gcc 13.3.0 (Ubuntu 24.04), Python 3.12.3, git 2.43.0; 94 GB RAM; `/` 691 GB free.

## Configure and build
- `cmake --preset minimal -DCMAKE_CUDA_COMPILER=$HOME/cuda-12.9/bin/nvcc`: CUDA compiler `NVIDIA 12.9.86 with host compiler GNU 13.3.0`,
  `OC_ENABLE_CUDA=ON`, `CMAKE_CUDA_ARCHITECTURES=120`, CUDAToolkit 12.9.86.
- `cmake --build build/minimal -j16`: **real 7m20.9s** (user 77m54s, sys 3m15s); 22 warning lines in the log.
- `hacs --version`: `hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`. `git status --short`: nothing from `build/`.

## Validation (all commands rc 0)
| step | rc | wall |
|---|---|---|
| `run_all_sharded.sh build/minimal/hacs 4 --logs ...` (`--all`) | 0 | 82m20s wall, **including long SIGSTOP pauses for higher-priority Lean jobs** (shards were paused and resumed by exact PIDs) |
| 10 device validations, `ENGINE_DEVICE=gpu` | 0 | 145 s |
| `GOLDEN_STRICT=1 GoldenRegressionValidation` (cpu) | 0 | 66 s |
| same with `ENGINE_DEVICE=gpu` | 0 | 85 s |
| `EngineDeterminismValidation HeckeExtDeterminismValidation ConsoleDeterminismValidation HeckeBenchmarkSmoke` | 0 | 198 s |
| `--bench cohom 1000 134217757 --lean --repeat 2` cpu / gpu | 0 / 0 | 68 s / 53 s |
| `--bench micro gemm 2048 --repeat 3` cpu / gpu | 0 / 0 | 4 s / 1 s |

Key lines:
- `SHARDED_ALL shards=4 passed=246/246 failed=0 mode=--all wall_s=4940.0 verdict=OK` (shards: 58/58 (shard 3), 57/57, 58/58, 58/58 and shard 1; `[SKIP]` lines per shard: 3, 4, 5, 7).
- Device list: all pass. `DescentSmithGpuValidation: 12589 checks, 0 failing, 58.952 s`; `fingerprints: cpu=0x6f hybrid=0xef gpu=0x1ef`;
  `EngineDeviceTrapValidation: 14 checks, 0 failed`; the two throughput lines (`E1`: 6.96x, `E2`: 27.46x) are informational.
- Golden strict, cpu and gpu: `tier A checked 12154, failing 0; tier B checked 6231, mismatching 0`.
- Digests `0x3dddd2ef9a8efd` (1279 golden records, 0 differ, for all thread/batch arms), `0xaef77d786b4f29b4`, `0x9ed8b83a2fb26622` as expected.
- Bench `cohom 1000 --lean`: `dims=0,167,0 c_eq_dims=3837,9009,5005` on cpu and gpu. `micro gemm 2048` checksum `0x55668bbd11acfdb5` on both backends; gpu 7733 vs cpu 6.6 Gmodmul/s.

All digests, counts and checksums equal the localhost reference (`plan/hacs/checks-results-2026-11-14.md`); only timings differ.

## Anomalies and notes
- CUDA 12.9.86 (user toolkit) instead of 13.0; gcc 13.3.0 (a tested compiler).
- `captured: [FAIL] PrivHarnessCatchThrowsLogicError` / `...NonStd` appear in the logs as captured output of the harness self-tests (their enclosing validations pass).
- **Timings are not comparable to localhost:** the validation was interleaved with Lean jobs (priority), and the cohom/gemm benches ran while a Lean job could run; the cohom wall times (cpu 26.3 s, gpu 33.7 s per run) are therefore noisy (localhost: 13.3 s vs 11.7 s). The 4-shard wall time includes pauses.
- Peak RAM was not instrumented; `free -g` showed at least 74 GB free throughout. One shard process (shard 3) finished while paused-signalled; no failure.
- An incident on my side: my first pause (SIGSTOP) used a `pgrep -f` pattern that also matched my own tool shell; it was fixed (exact PIDs afterwards). No HACS state or file was affected.
