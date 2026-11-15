# Run log (Task 0, HACS side)

Binary: `$HACS_DATA/s26/close/build/hacs` = `hacs 0.2.0 (commit 5bd706911c89; contract [C] 1.27.0, [E] 1.25.3, [U] 0.8.1)`,
sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a`. Host: shared 32-core WSL2 box, 82 GB RAM; every run
under `nice -n 19`, `ENGINE_THREADS=8`, CPU only (no GPU), no environment emitter or interlock set. Scratch:
`$HACS_DATA/s27/jl/work/` (the generated `.oc` scripts are also embedded verbatim, key `oc`, in each `data/cell_*.json`).
Wall and peak RSS from `/usr/bin/time -v`.

| Date (UTC) | What | Command | Wall | Peak RSS |
|---|---|---|---|---|
| 2026-11-13 | probe: `hecke_structure(3,10)` | `hacs --script hs3.oc` | 0.9 s | 49 MB |
| 2026-11-13 | probe: `descent(3,10,[2,5,7,11,13]).module_Z()` | `hacs --script d3.oc` | 0.9 s | 158 MB |
| 2026-11-13 | mod 17: `level_n(3,10,17,[2,3,5,7,11,13])`, level-1 `hecke(H,3)` | `hacs --script l3.oc` | < 1 s | < 0.2 GB |
| 2026-11-13 | grid: 36 cells (D in {1,3,5,7,11,13}, n = 2..12): `descent(D,n,P).module_Z()`, `charpoly_factored`, `hecke_structure(D,n,"full"/"anemic")` | `python3 scripts/run_cells.py <hacs> data` | 3 min 41 s total; max 28.5 s per cell (D=13, n=6) | max 325 MB (D=13, n=12) |
| 2026-11-13 | family: char_Z(T_p) factored at levels 1 and 3, n = 2..60 even | `hacs --script fam.oc` (in `scripts/fam.oc`) | 2 min 28 s | 1.16 GB |
| 2026-11-13 | persistence cells: D in {1,3}, n = 14..22, P = [2,5,7,11,13] | `JL_PRIMES=2,5,7,11,13 python3 scripts/run_cells.py <hacs> data/persist 1,14 ... 3,22` | 2 min 34 s total; max 46 s | max 271 MB |
| 2026-11-13 | lattice analysis (pure Python + sympy, no HACS) | `python3 scripts/congruence_modules.py data`, `... data/persist 3,14 ... 3,22` | 20 min 7 s (grid; (13,14) alone 755 s), < 1 s (persist) | 83 MB |
| 2026-11-13 | ordinary ranks / persistence test (pure Python + sympy) | `python3 scripts/ordinary_family.py data/family_charpolys.txt` | ~ 10 s | small |
| 2026-11-13 | lower bounds read from the HACS records | `python3 scripts/record_lower_bounds.py data` | < 1 s | small |

Per-cell lines: `data/runs.tsv`, `data/persist/runs.tsv`. All HACS runs exited 0. Heavy runs were logged in `$HACS_RUN_LOG`.
Total HACS compute: about 9 CPU-minutes of wall time at ≤ 8 threads. The Python lattice analysis is single-threaded; one cell,
(13, k=14), dominates it because the HNF is unoptimised.
