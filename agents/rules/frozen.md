# Rule: frozen paths and the frozen Lean/Mathlib toolchain (global, all agents, all nodes)

## Frozen repository paths — read-only, never edit, move or delete
- `plan/seed/` — the seed outline of the implementation route.
- `lean/trace-formula-project-import/lean/{lakefile.toml,lean-toolchain,lake-manifest.json}` and
  `lean/trace-formula-project-import/latex/backtranslation/generated/`.

## Frozen toolchain
- Lean `leanprover/lean4:v4.35.0` and the matching Mathlib (rev `56a005855ea17e0b0958f73ec801ae140b0a1679`)
  are fixed and frozen on every node as a local copy (path is node-specific; each node's master knows it).
- **Forbidden for all agents:** `lake update`, `lake clean`, `lake exe cache get`, changing any
  `lean-toolchain` / `lake-manifest.json` / Mathlib `require`, `elan` toolchain changes, and any write
  into the frozen Mathlib copy or its dependency farm.
- Dependencies are linked as symlinks into the frozen copy (see
  `lean/trace-formula-project-import/tools/link_deps.sh`, `tools/deps.conf`); `.lake/packages` is never committed.
- Build only through the provided wrapper scripts (e.g. `tools/lbuild.sh`, `tools/lfile.sh`), which enforce
  locks, memory caps and frozen-tree checks. Never call `lake` directly in the import.
- Exception, node `abhijit` only (global master 2026-11-14): a draft check of a Mathlib-only file (imports `Mathlib.*` and the WP's own `Langlandscape.CommAlg.*` files only) by a direct `lean` call with `LEAN_PATH` into the frozen Mathlib's `.lake/build/lib/lean` trees, outputs (`-o`) only into a scratch directory outside the repo and outside the frozen tree, under a memory cap, followed by a `find <frozen tree> -newer <marker>` check. Never `lake`; never a wrapper of `lean/Langlandscape/` there. This is not an acceptance check; acceptance is the TITAN round.
- `tools/deps.conf` contains Fabian-node paths; never edit it. On another node create the git-ignored override
  `tools/deps.local.conf` (e.g. `GL2TF_DATA=<node data dir>`) and add it to `.git/info/exclude` (as done on TITAN).

## literature/
- `literature/` is git-ignored and must never be committed (copyright; repo will be public with full history).
  Do not copy literature text or PDFs into tracked files; cite instead.

## Exception: submission clean-room build test (Fabian, 2026-11-15 ~06:00Z, in the global-master session: "all necessary exceptions are authorized"; item 5 "Yes" to the lakefile fix and the clean-room build test)
Scope, ONE-OFF, job `subl-clean-1` (spec plan/implementation/outbox/20261115T063727Z_titan-subl-gate-1.md on impl/submission-lean dc61af50), on TITAN only:
- In a fresh `mktemp -d` scratch directory under /tmp with its OWN `.lake`, and with `XDG_CACHE_HOME` and `MATHLIB_CACHE_DIR` pointing inside it; `LAKE_PKG_URL_MAP` and `LEAN_PATH` unset; a `file://` clone of impl/submission-lean; no symlinks into the frozen Mathlib tree or the dependency farm.
- Allowed there: `lake exe cache get`, `lake build` (incl. `lake build AlgJL`, the tests, VendorStacks), and `lake env lean Audit/PrintAxioms.lean`.
- Still forbidden everywhere: `lake update`, `lake clean`, any edit of the frozen trees, and `lake exe cache get` outside that scratch directory.
- The scratch directory may be deleted afterwards (an exception to the no-rm rule for this directory only; or leave it under /tmp).
Also authorized (same decision): the lakefile.toml / lake-manifest.json / pins change of impl/submission-lean (GL2TF path → ../trace-formula-project-import/lean).
