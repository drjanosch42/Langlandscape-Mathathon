# Rule: code/

- `code/hacs/`: HACS snapshot (provided by the team) and our extension implementing the
  Jacquet–Langlands transfer. Keep upstream snapshot files unmodified where possible;
  put our changes in clearly marked modules and document them in `code/hacs/CHANGES.md`.
- `code/python/`: Python code (package + tests, `pytest`); `code/cas/`: Sage/PARI/Magma etc. scripts;
  `code/examples/`: small reproducible examples; `code/results/`: computed results.
- Every result in `code/results/` records: generating script + commit, parameters, date, runtime.
- Results ≤ 10 MB in git; larger data is referenced, not committed.

## HACS snapshot (added 2026-11-14)
- **Public release (2026-11-14):** HACS v0.2.1 is published at https://github.com/drjanosch42/hacs, DOI
  [10.5281/zenodo.24231446](https://doi.org/10.5281/zenodo.24231446); it is **code-identical** to our initial `code/hacs/` snapshot; since then `code/hacs/` additionally carries our marked JL module (`jl/`, `src/hacs/Registry/JL/`, `cmake/jl/`) and three documented hook lines (`code/hacs/CHANGES.md`).
  The census data stays at hacs-data v0.2.0 (https://github.com/drjanosch42/hacs-data, DOI
  [10.5281/zenodo.24147012](https://doi.org/10.5281/zenodo.24147012)). Cite both (software + data) in the documentation,
  the chapters and the talk.
- `code/hacs/` holds the **unmodified HACS 0.2.1 seed** (LGPLv3 with a CUDA linking exception; see `code/hacs/LICENSE`,
  `NOTICE`, `LICENSES/`, `PROVENANCE.md`). Upstream files are read-only; our extensions go in clearly marked new modules,
  documented in `code/hacs/CHANGES.md`. `code/hacs/CLAUDE.md` adds HACS-specific safety rules (top-level rules win for process).
- `code/hacs/lean/` is a separate Lean project on **Lean v4.33.0 with its own Mathlib pin**. It is NOT our frozen toolchain:
  never build it with `lake` (that would fetch), never `lake update` it. Treat it as read-only reference until a plan WP
  provides a frozen toolchain for it.
- HACS builds (CMake/CUDA) use the local CPU/GPU on Fabian's node; the CMake `build*/` dirs are git-ignored.
