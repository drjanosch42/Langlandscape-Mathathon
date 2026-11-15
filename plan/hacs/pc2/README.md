<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# PC2 (Noctua 2) job: Lane B native census

Status: *prepared, not submitted, not tested on the cluster*. Nothing here has been run on PC2.

## Status (Lane B closure, 2026-11-15)

**Not ready to submit.** Before a 10^5 run, do two things: (i) a sparse record layout (v3), because dense JSON is ≈ 4 GB per q at 10^5; (ii) a second class invariant to cut the exact identifications (6.6 M at q = 10007). Without them, run on the laptop up to q ≈ 5000 instead, or to q ≤ 2·10^4 with ops < 50. Measured values: HJ-1/2 report, Lane B closure.

## What it does
For every prime q <= Q_MAX (default 10^5), compute the weight-2 definite Brandt module B_{q,inf}
(`jl_brandt2_dump`, schema `langlandscape_brandt/v2`, one `D<q>_M1_k2.json` per q) and then read the Mazur/Eisenstein
congruence modules from these records with the HACS Lane B JL module (`JLBrandtFreeBlockRead`, `JLBrandtCongruenceRead`).

## CPU only: do not use the GPUs
The census uses **no GPU**. `jl_brandt2_dump` is single-threaded C++17 per q, and HACS is built with `-DOC_ENABLE_CUDA=OFF`.
Run it on a **CPU partition** (`normal`; `largemem` for the read stage if RAM requires it). Do **not** pass `--gres=gpu`
and do not submit to the H100 partition: that would burn the 20 H100 GPU-hours quota for nothing.

## Files
| File | Content |
|---|---|
| `jl_census.sbatch` | one script, three stages selected by `STAGE=build\|gen\|read` |
| `collect.sh` | laptop side: rsync results back, verify sha256, place them |

## Placeholders to fill (grep for `TODO` and `<`)
`<PC2_PROJECT>`, `<CPU_PARTITION>`, `--time`, `--mem`, `--cpus-per-task`, `<COMMIT>`, `<REPO_URL>`, `WORK` (a scratch path),
module names (`module spider GCC CMake Python`, EasyBuild style; the names in the script are **placeholders, to be verified by Fabian**),
`ALPHA` (placeholder 2; replace by the measured cost exponent of the HJ-1/2 timings).

## Sources
The commit must contain **both** the Lane B JL module (`code/hacs/src/hacs/Registry/JL/`) **and** the quat sources
(`.../JL/quat/`, currently on `impl/hacs-laneB-quat`). Check with `git ls-tree` that `quat/tools/jl_brandt2_dump.cpp` is present
at `<COMMIT>` (branch `impl/hacs-laneB` after integration). Either `git clone <REPO_URL>` + checkout (the script does this
for `STAGE=build`), or rsync the working tree to `$WORK/Langlandscape` and set `COMMIT=local`. Never run `lake` or Lean; the job needs no Lean.
The repo's `literature/` is git-ignored and must not be copied.

## Run (all on a login node; nothing is submitted by this repo)
```
mkdir -p $WORK/logs && cd $WORK && cp .../plan/hacs/pc2/jl_census.sbatch .
python3 -m pip install --user sympy                       # collector dependency, once
# 0. smoke test, one core, minutes
JB=$(sbatch --parsable --array=0-0 --cpus-per-task=4 --time=02:00:00 --export=ALL,STAGE=build,COMMIT=<COMMIT>,REPO_URL=<URL> jl_census.sbatch)
JG=$(sbatch --parsable --dependency=afterok:$JB --array=0-0 --cpus-per-task=1 --time=00:30:00 --export=ALL,Q_MAX=200,NCHUNK=1 jl_census.sbatch)
sbatch --dependency=afterok:$JG --array=0-0 --cpus-per-task=1 --time=00:30:00 --export=ALL,STAGE=read,Q_MAX=200 jl_census.sbatch
# 1. full run: gen array (NCHUNK = size of #SBATCH --array, default 64) then read
JG=$(sbatch --parsable --dependency=afterok:$JB --export=ALL,Q_MAX=100000,NCHUNK=64,ALPHA=<measured> jl_census.sbatch)
sbatch --dependency=afterok:$JG --array=0-0 --partition=<largemem> --mem=<..> --cpus-per-task=16 --export=ALL,STAGE=read,Q_MAX=100000 jl_census.sbatch
```
Notes: use a different `WORK` (or `rm -r census_json census_out`) between smoke and full run. If `--array` size is changed,
set `NCHUNK` equal to it. The gen stage is restartable: existing non-empty `D<q>_M1_k2.json` are skipped.
Chunking: greedy LPT on cost q^ALPHA (biggest q first, onto the lightest chunk); inside a task `xargs -P $SLURM_CPUS_PER_TASK`
runs one single-threaded `jl_brandt2_dump` per q, biggest first. q = 2, 3 are skipped (no congruence module). Timing and
peak RSS per q go to `census_out/gen_<task>.log` (`/usr/bin/time`; verify it exists on the compute nodes, else drop it).

## Rule-19 resource prediction (fill from HJ-1/2 measurements)
| Quantity | Predicted | Measured |
|---|---|---|
| time per q at q = 10^3 | 2.0 s median (measured HJ-1/2, ops = primes < 50 + Eisenstein ℓ); class set + T_2 alone 0.025 s at q = 997 | |
| time per q at q = 10^4 | 382 s measured at q = 10007 (359 s of it T_5003); model 85 µs · h · Σ_{p∈ops}(p+1) | |
| time per q at q = 10^5 | ≈ 5 min (ops < 50 only) up to ≈ 10 h when ℓ ≈ q/12 is in ops (model); class set alone 2.0 s at q = 100003 (h = 8334) | |
| cost exponent ALPHA | cost is dominated by the largest T_ℓ, not by a power of q; use the model above for chunking (ALPHA = 2 is a rough proxy) | |
| RAM peak per q (10^5) | ≈ 8.9 GB (dense h² × #ops × 8 B); 16 MB measured at q = 2999 | |
| total core-hours, Q_MAX = 10^5 | ≈ 4000 core-h with the Eisenstein T_ℓ, ≈ 300 core-h with ops < 50 only (model) | |
| wall time = core-hours / (NCHUNK * cpus-per-task) | `<TBD>` | |
| read stage (HACS) time / RAM | `<TBD>` / `<TBD>` GB | |
| output size (JSON dir, tar.gz) | dense v2 JSON ≈ 45 MB per q at 10^4, ≈ 4 GB per q at 10^5: **not viable** before a sparse v3 layout | |

Choose cpus-per-task x (RAM peak per q) <= `--mem`. Per-q time is dominated by the largest q; make sure the single biggest q
fits within `--time`.

## Output collection
Produced in `$WORK/census_out/`: `census_q<Q_MAX>.tar.gz` (the JSON dir, `reads.log`, `congruence_k.json`, `collect.log`,
`binaries.sha256`, `gen_all.log`) and its `.sha256`. The `binaries.sha256` holds the checksums of `jl_brandt2_dump` and `hacs`.
Copy back with `plan/hacs/pc2/collect.sh <user@noctua2:WORK> <repo>`:
* tarball <= 10 MB: goes to `code/results/laneB/census/` (committed by the lane / global master via `wip-code`);
* larger: keep outside git (e.g. `~/data/hacs-run/laneB/census/`), reference its sha256 in a small note; never commit > 10 MB.
The collector (`code/python/langlandscape/hacs_bridge/laneB_collect.py`) is called with `--no-read` since `reads.log` is
produced directly; it re-runs `JLBrandtCongruenceRead`. Its GL_2-side comparison uses `code/results/s01/symn.json`, which only covers small D,
so for large q that comparison is simply absent (the status of every claim stays *computed*).

## Dry run (login node, no submission)
```
bash -n jl_census.sbatch && bash -n collect.sh
shellcheck jl_census.sbatch collect.sh        # if available
```

## Optional, later: GPU section (*not needed for this census*)
Candidate GPU use (HJ-10): dense charpoly / rref mod l of Brandt matrices for large class number h, through HACS's
`ENGINE_DEVICE=cuda` (opt-in). It would need a separate build and a GPU partition job:
```
cmake -B build-cuda -S code/hacs -DOC_ENABLE_CUDA=ON -DCMAKE_CUDA_ARCHITECTURES=90 -DCMAKE_BUILD_TYPE=Release   # 90 = H100
make -C build-cuda -j 16
ENGINE_DEVICE=cuda JL_BRANDT_IN=<dir> ./build-cuda/hacs ...   # plus: module load CUDA/<ver> (to verify), #SBATCH --gres=gpu:1
```
Do not do this unless a measured CPU bottleneck in the read stage justifies it, within the 20 GPU-hour quota.

## Not verified
Nothing was run on PC2; module names, partition names, `/usr/bin/time` availability; whether `jl_brandt2_dump --write-index`
with no q indexes existing JSONs without recomputation; whether the quat sources and the CMake JL wiring are on one branch.
