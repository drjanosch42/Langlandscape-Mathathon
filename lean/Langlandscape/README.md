# lean/Langlandscape — our Lake project (package `Langlandscape`)

Created by S01-X1a (2026-11-14; `plan/implementation/OVERVIEW.md` §3.3–§3.5). Outcome **P**: the import
(package `GL2TF`, modules `AlgJL.*`, declarations `GL2TF.*`) is a `path` dependency. Since the submission bundle
(2026-11-15) the `require` points at the in-repo import `../trace-formula-project-import/lean` (formerly the git-ignored
symlink `.lake/GL2TF`), so a fresh clone builds with plain Lake (`BUILDING-LEAN.md` at the repo root). On a team node,
`tools/link_deps.sh` makes that directory's git-ignored `.lake` a symlink to the main checkout's built import
(`$GL2TF_IMPORT/.lake`; nothing to link in the main checkout itself), so its oleans are read in place; this
project never builds a GL2TF module. Decision record: `DECISION-PV.md`. Rules: `agents/rules/lean.md`, `frozen.md`.

## Layout
- `lakefile.toml`: libraries `Langlandscape`, `LanglandscapeTests`, `LanglandscapeVendorStacks`
  (`Vendor/AxiomStacks`, `StacksCore.+`; created by S01-X3). No WP edits it.
- `lake-manifest.json`: **generated** by `tools/make_manifest.py` (the import's manifest, `name` = `Langlandscape`,
  plus one `path` entry for GL2TF). Never hand-edit or delete it. Only the stage master regenerates it
  (`python3 -I tools/make_manifest.py --pins`), and `tools/pins.sha256` changes in the same commit.
- `Langlandscape/<Area>/<Topic>.lean` (namespace `Langlandscape.<Area>`), `Langlandscape/Hyp/<Name>.lean`
  (hypotheses), `LanglandscapeTests/` (non-vacuity examples), `Audit/PrintAxioms.lean`.
- `Langlandscape/Smoke.lean`: regression test of the frozen setup; keep it.
- The aggregator files `Langlandscape.lean`, `LanglandscapeTests.lean`, `SORRIES.md` and `HYPOTHESES.md` belong to
  the stage master. A WP reports its one-line additions.

## Building (only through the wrappers; never call `lake`)
Run every command from `lean/Langlandscape/` of your worktree:
- `tools/link_deps.sh`, then `tools/link_deps.sh --verify`: links `.lake/packages/<pkg>` into the frozen farm and
  `../trace-formula-project-import/lean/.lake` to the built import's `.lake` (after checking that the sources agree). Run once per fresh worktree. Expected output:
  `link_deps: OK (9 packages …; GL2TF -> …)`.
- `tools/check_frozen.sh`: dry no-rebuild check of every dependency module we import (Mathlib, AlgJL, …). Expected
  output: `check_frozen: All targets up-to-date (…) over N dependency modules`.
- `tools/lbuild.sh <target>…`. The allowed targets are `Langlandscape`, `LanglandscapeTests`,
  `LanglandscapeVendorStacks`, and `+M` for a module with a source file here (`Langlandscape.*`,
  `LanglandscapeTests.*`, `StacksCore.*` under `Vendor/AxiomStacks/`). GL2TF, Mathlib and bare builds are refused.
  Lock model (S01-X1b, `tools/locks.sh`): `lean.lock` **shared** (the import's `lbuild` holds it exclusively and blocks
  us), then the per-checkout lock `ll-<sha1 of path>.lock` (exclusive for `lbuild`, shared for `lfile`), then a node slot
  (`SLOTS` <= 3, settable in `deps.local.conf`), then the memory wait. Two worktrees can build concurrently. Both wrappers
  print `slot acquired <ts>` and `mem ok <ts>` to stderr.
- `tools/lfile.sh <file.lean>`: single-file check (`lake env lean`, locks as above). Every project
  import of the file must already be built, by `lbuild` or by seeding.
- `tools/check_frozen.sh --sweep <marker>`: post-hoc check that no frozen tree (Mathlib, the farm, the import)
  changed since `<marker>`.
- `tools/lbuild.sh --smoke`: S01-X1a step 3 only (sandboxed first contact).
- **Exit 99** from any wrapper means the pin guard fired or a frozen tree was written: stop and alert the global
  master.

## Fresh worktree
1. `git worktree add <wt> -b impl/sNN-<wp> wip-implementation`
2. `cd <wt>/lean/Langlandscape && tools/link_deps.sh && tools/link_deps.sh --verify && tools/check_frozen.sh`
3. Seed `.lake/build` from the `impl` worktree (regime (a), `DECISION-PV.md`). Until S01-X2's `tools/new_wp.sh`
   exists, do it by hand:
   `flock -s -w 600 ~/.cache/gl2tf/lean.lock cp -a --reflink=auto /home/janosch/dev/Langlandscape-wt/impl/lean/Langlandscape/.lake/build .lake/build`.
   **Never use hard links** (`cp -al`, `ln`).
4. Remove the worktree only with `git worktree remove <wt>`, never with `rm -rf`.

### Per-WP tooling (S01-X2)
`tools/new_wp.sh <wp> [--base <rev>] [--from <wt>]` (or `--exp <wp>-<model>`) creates the worktree, branch and link_deps,
and seeds `.lake/build` (lean.lock shared + the source checkout's per-checkout lock shared; never hard links).
`tools/check_wp.sh <file.lean>…` is the acceptance gate: one lbuild; exit 1 on a sorry in the log, on a forbidden-token
grep hit (sorry, admit, axiom, native_decide, implemented_by), or on a theorem/lemma without an `s01-` docstring directly
before it (`Smoke.lean` exempt from the docstring check only); exit 99 propagated.
