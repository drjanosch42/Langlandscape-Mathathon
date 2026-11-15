# Run log (Task 1, v6 request, HACS side)

- **Binary:** `$HACS_DATA/s26/close/build/hacs` = `hacs 0.2.0 (commit 5bd706911c89; contract [C] 1.27.0, [E] 1.25.3, [U] 0.8.1)`, sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a`.
- **Repository tip:** `ee9b57cc` (branch `hecke-extensions`). No source was changed and nothing was rebuilt.
- **Host:** the shared 32-core WSL2 box.
- **How the runs were made:** everything under `nice -n 19`, at most 4 threads (HACS `ENGINE_THREADS=4`; the Python runs single-threaded), CPU only, no GPU, no Lean and no `lean.lock`. No environment emitter or interlock was set.
- **Scratch:** `$HACS_DATA/s27/jl1/`.
- **Logging:** heavy runs were logged in `$HACS_RUN_LOG`. Wall time and peak RSS are from `/usr/bin/time`.
- **Software:** Python 3.10, numpy 2.2.6, sympy 1.14.0.

| Date (UTC) | What | Command | Wall | Peak RSS |
|---|---|---|---|---|
| 2026-11-13 08:1x | anchors, development runs (p=3,k=12; p=5,k=12; p=13,k=14) | `python3 scripts/cell.py 3 12 17`, `... 5 12 29 131`, `... 13 14` | 0.7 s / 3.5 s / 6.5 s | ≤ 81 MB |
| 2026-11-13 08:2x | core grid, 30 cells p ∈ {3,5,7,11,13}, k ∈ {4,…,14} | `scripts/run_grid.sh` (writes `data/cells/`) | 61 s total; max 8.0 s per cell (p=13, k=12) | max 81 MB |
| 2026-11-13 08:2x | extension, 25 cells, k ∈ {16,…,24} | `KS="16 18 20 22 24" scripts/run_grid.sh data/cells_ext` (+ the six cells p=11,k=24 and p=13 rerun by hand after a fix: int64 overflow for l > 2^63 in an unused matrix) | about 7 min total; max 47 s per cell (p=13, k=22) | max 145 MB |
| 2026-11-13 08:2x | HACS cross-check, core: 109 `level_n(p, n, l, qs)` | `hacs --script scripts/hacs_level_n_xcheck.oc` → `data/hacs_level_n_xcheck.out` | 0.23 s | 19 MB |
| 2026-11-13 08:3x | HACS cross-check, extension: 161 `level_n` | `hacs --script scripts/hacs_level_n_xcheck_ext.oc` → `data/hacs_level_n_xcheck_ext.out` | 1.7 s | 20 MB |
| 2026-11-13 08:3x | comparisons + summaries (pure Python) | `python3 scripts/xcheck.py`; `summarize.py`; `cusp_compare.py data/summary.json data/summary_ext.json`; `levelraise_check.py` | < 30 s each | < 150 MB |

- **Per-cell timings:** `data/cells*/time_p*_k*.txt`, in the format "wall_s rss_kB".
- **Cross-check result:** `data/xcheck.json` → `checks=2447 mismatches=0`.
- **HACS exit codes:** all HACS runs exited 0.
- **Total compute:** about 9 CPU-minutes of Python and 2 s of HACS.
- **The Task-0 HACS records reused (read-only):** `../task0_inscope/data/cell_D{1,p}_n{n}.json`.
