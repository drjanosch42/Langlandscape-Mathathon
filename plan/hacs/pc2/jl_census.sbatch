#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
#
# Lane B native census (Mazur/Eisenstein congruence modules over B_{q,inf}, weight 2), Paderborn PC2 / Noctua 2.
# CPU-ONLY. No GPU is used: do NOT request --gres=gpu and do NOT use a GPU partition (it would burn H100 GPU-hours).
#
# Stages (selected by STAGE, default gen):
#   STAGE=build    configure/compile jl_brandt2_dump and the hacs binary (once; 1 core, ~ tens of minutes for hacs)
#   STAGE=gen      array job: each task generates D<q>_M1_k2.json for its cost-balanced chunk of primes q <= Q_MAX
#   STAGE=read     single job (after all gen tasks): JLBrandtFreeBlockRead JLBrandtCongruenceRead + collector + tar
# Typical submission (see README.md):
#   JB=$(sbatch --parsable --array=0-0 --export=ALL,STAGE=build jl_census.sbatch)
#   JG=$(sbatch --parsable --dependency=afterok:$JB jl_census.sbatch)                  # STAGE=gen, uses #SBATCH --array below
#   sbatch --dependency=afterok:$JG --array=0-0 --export=ALL,STAGE=read --mem=400G --cpus-per-task=16 jl_census.sbatch
# (all options precede the script name.) Smoke test: --array=0-0 --cpus-per-task=1 --time=00:30:00 --export=ALL,Q_MAX=200,NCHUNK=1
# (the read stage also needs the same Q_MAX in --export so the tarball is named consistently).
# TODO Fabian: values to fill: account <PC2_PROJECT>, partition <CPU_PARTITION>, time, mem, cpus, COMMIT, REPO_URL, module names.
#
#SBATCH --job-name=jl_census
#SBATCH --account=<PC2_PROJECT>
#SBATCH --partition=<CPU_PARTITION>
#SBATCH --time=12:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=32
#SBATCH --mem=128G
#SBATCH --array=0-63
#SBATCH --output=logs/jl_census_%A_%a.out
#SBATCH --error=logs/jl_census_%A_%a.err

set -euo pipefail

# ----------------------------------------------------------------------------- parameters (override via --export)
STAGE="${STAGE:-gen}"
Q_MAX="${Q_MAX:-100000}"              # all primes q <= Q_MAX (smoke test: 200)
NCHUNK="${NCHUNK:-64}"                # number of array tasks; must equal the size of --array
ALPHA="${ALPHA:-2}"                   # PLACEHOLDER: cost of one q ~ q^ALPHA; replace by the measured exponent from HJ-1/2
COMMIT="${COMMIT:-<COMMIT>}"          # TODO Fabian: commit on branch impl/hacs-laneB (must contain the quat sources + JL module)
REPO_URL="${REPO_URL:-<REPO_URL>}"    # TODO Fabian: clone URL (or rsync the tree into $WORK/Langlandscape and set COMMIT=local)
WORK="${WORK:-${PC2DATA:-$HOME}/langlandscape_census}"   # TODO: a scratch/work filesystem path with enough space
SRC="$WORK/Langlandscape"
BIN="$WORK/bin"
OUT="$WORK/census_json"               # D<q>_M1_k2.json files
RES="$WORK/census_out"                # reads.log, collector output, tarball, checksums
cd "$WORK" 2>/dev/null || { mkdir -p "$WORK"; cd "$WORK"; }
mkdir -p logs "$BIN" "$OUT" "$RES"

# ----------------------------------------------------------------------------- modules (EasyBuild style)
# TODO Fabian: verify the exact names with `module spider GCC`, `module spider CMake`, `module spider Python` on Noctua 2.
module purge
module load GCC/13.2.0 CMake/3.27.6 Python/3.11.5      # PLACEHOLDER names -- to verify by Fabian
# Python needs sympy for the collector (STAGE=read): `python3 -m pip install --user sympy` once on a login node.
# No Lean/lake is used anywhere in this job. Never run `lake`.

NJ="${SLURM_CPUS_PER_TASK:-1}"
Q="$SRC/code/hacs/src/hacs/Registry/JL/quat"

case "$STAGE" in
# ----------------------------------------------------------------------------- build
build)
    if [ ! -d "$SRC/.git" ] && [ "$COMMIT" != local ]; then
        git clone "$REPO_URL" "$SRC"
    fi
    if [ "$COMMIT" != local ]; then
        git -C "$SRC" fetch origin && git -C "$SRC" checkout --detach "$COMMIT"
    fi
    echo "building at $(git -C "$SRC" rev-parse HEAD 2>/dev/null || echo local-tree)"
    g++ -std=c++17 -O2 "$Q/tools/jl_brandt2_dump.cpp" "$Q"/{Quat,Lattice,Order,ClassSet,Brandt2}.cpp \
        "$SRC/code/hacs/src/hacs/NumberField/Sha256.cpp" -o "$BIN/jl_brandt2_dump"
    # HACS with the Lane B JL module; CPU only (OC_ENABLE_CUDA=OFF)
    cmake -B "$WORK/build" -S "$SRC/code/hacs" -DOC_ENABLE_CUDA=OFF -DCMAKE_BUILD_TYPE=Release
    make -C "$WORK/build" -j "$NJ"
    cp "$WORK/build/hacs" "$BIN/hacs"
    ( cd "$BIN" && sha256sum jl_brandt2_dump hacs | tee "$RES/binaries.sha256" )
    ;;

# ----------------------------------------------------------------------------- generate (array)
gen)
    TASK="${SLURM_ARRAY_TASK_ID:-0}"
    [ "$TASK" -lt "$NCHUNK" ] || { echo "array task $TASK >= NCHUNK $NCHUNK"; exit 1; }
    # cost-balanced chunking (greedy LPT: largest q first onto the currently lightest chunk, cost q^ALPHA);
    # deterministic, so every array task computes the same partition and takes its own chunk.
    python3 - "$Q_MAX" "$NCHUNK" "$ALPHA" "$TASK" > "$RES/chunk_$TASK.txt" <<'PY'
import sys, heapq
qmax, n, alpha, task = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
sieve = bytearray([1]) * (qmax + 1); sieve[:2] = b"\0\0"
for i in range(2, int(qmax ** 0.5) + 1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
# q = 2, 3 are skipped: B_{q,inf} with q=2,3 has class number 1 and no Mazur congruence module (q-1)/gcd(q-1,12) = 1
qs = [q for q in range(5, qmax + 1) if sieve[q]]
heap = [(0.0, c) for c in range(n)]; heapq.heapify(heap); mine = []
for q in sorted(qs, reverse=True):
    w, c = heapq.heappop(heap)
    if c == task: mine.append(q)
    heapq.heappush(heap, (w + q ** alpha, c))
print("\n".join(map(str, sorted(mine, reverse=True))))   # biggest first inside the chunk
PY
    echo "task $TASK: $(wc -l < "$RES/chunk_$TASK.txt") primes, $NJ concurrent, Q_MAX=$Q_MAX ALPHA=$ALPHA"
    # skip q whose JSON already exists (restartable); one dump process per q, single-threaded
    todo() { while read -r q; do [ -s "$OUT/D${q}_M1_k2.json" ] || echo "$q"; done < "$RES/chunk_$TASK.txt"; }
    todo | xargs -r -P "$NJ" -I{} bash -c \
        '/usr/bin/time -f "q={} %e s %M KB" "$0" {} --out "$1" --commit "$2" 2>&1 | tail -n 2' \
        "$BIN/jl_brandt2_dump" "$OUT" "$COMMIT" > "$RES/gen_$TASK.log"
    ;;

# ----------------------------------------------------------------------------- read + collect (single job, after gen)
read)
    "$BIN/jl_brandt2_dump" --out "$OUT" --write-index --commit "$COMMIT"   # TODO verify: index over existing JSONs without recomputing
    ( cd "$BIN" && sha256sum jl_brandt2_dump hacs ) > "$RES/binaries.sha256"
    JL_BRANDT_IN="$OUT" "$BIN/hacs" JLBrandtFreeBlockRead JLBrandtCongruenceRead > "$RES/reads.log"
    # collector: re-runs JLBrandtCongruenceRead itself (reads were already done above -> --no-read); symn.json covers small D only
    python3 -I "$SRC/code/python/langlandscape/hacs_bridge/laneB_collect.py" \
        --binary "$BIN/hacs" --records "$OUT/index.json" --out "$RES/congruence_k.json" --no-read \
        > "$RES/collect.log" 2>&1
    cat "$RES"/gen_*.log > "$RES/gen_all.log" 2>/dev/null || true
    ( cd "$WORK" && tar czf "$RES/census_q${Q_MAX}.tar.gz" census_json census_out/reads.log census_out/congruence_k.json \
        census_out/collect.log census_out/binaries.sha256 census_out/gen_all.log )
    sha256sum "$RES/census_q${Q_MAX}.tar.gz" | tee "$RES/census_q${Q_MAX}.tar.gz.sha256"
    du -sh "$RES/census_q${Q_MAX}.tar.gz"
    ;;
*) echo "unknown STAGE=$STAGE (build|gen|read)"; exit 2 ;;
esac
