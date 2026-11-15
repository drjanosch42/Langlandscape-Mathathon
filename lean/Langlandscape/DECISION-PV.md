# DECISION-PV: outcome of the S01-X1a smoke test (2026-11-14)

**Outcome: P** (path dependency on the built import through `.lake/GL2TF`). P′ (an import rebuild) and V (vendoring)
are not needed.
**Worktree regime: (a), seeding.** A fresh worktree's `.lake/build` is copied from the `impl` worktree with
`cp -a --reflink=auto`, holding the lock shared (until S01-X1b: `lean.lock`). Hard links are never used. Step 7 passed.

All results are *computed*, on Fabian's node, with Lean v4.35.0 / Lake 5.0.0 and Mathlib `56a00585…`.
Procedure: `plan/implementation/OVERVIEW.md` §3.5. Base commit `a4efa59`; the skeleton commit is `e78539d`
(`impl/s01-x1a`).

## Steps
| step | what | result | wall |
|---|---|---|---|
| 0 | pre-flight | `/mnt/c` 182 GB free, MemAvailable 83 GB, no lake process, import `git status` empty, `unshare -rmn true` OK; sha256 of the import's 3 frozen files recorded | — |
| 1 | skeleton | all 3 stage-01 libs declared (`LanglandscapeVendorStacks` with a missing `srcDir`); manifest generated (diff below); `pins.sha256` written | — |
| 2 | `link_deps.sh && link_deps.sh --verify` | `link_deps: OK (9 packages at the manifest revs, links in place; GL2TF -> /home/janosch/dev/Langlandscape/lean/trace-formula-project-import/lean)` | 0.2 s |
| 3 | `lbuild.sh --smoke` (sandbox: `unshare -rmn`, `/home/janosch/data` and `…/trace-formula-project-import` read-only, no network) | (a) `All targets up-to-date (3763 jobs).` (b) `⚠ [3765/3765] Built Langlandscape.Smoke (8.5s)`, the only `Built` line; `Build completed successfully (3765 jobs).`; frozen trees untouched | 24 s total |
| 4 | `check_frozen.sh` | `check_frozen: All targets up-to-date (3763 jobs). over 4 dependency modules`; 0 matches of `fetching\|materializing\|cloning\|remote URL changed\|manifest out of date` | 4 s |
| 5 | `lbuild.sh +Langlandscape.Smoke` | rc 0, no `Built` line (no AlgJL module built); `Smoke.olean` mtime unchanged | 7 s |
| 6 | `lfile.sh Langlandscape/Smoke.lean` | `lfile: OK Langlandscape/Smoke.lean (slot 1)` | 8 s |
| 6 post | | `sha256sum -c` of our 3 pinned files and of the import's 3: all OK; `find <import>/lean -newer $marker`: empty; `check_frozen.sh --sweep $marker`: `frozen trees untouched`; import `git status --porcelain`: empty; `.lake/packages/*`: all symlinks | — |
| 7 | second worktree `…-wt/s01-x1a-2` at `e78539d` | `link_deps` OK; dry check `All targets up-to-date (3763 jobs). over 4 dependency modules` (5 s); seeding `cp -a --reflink=auto` of 6.4 MB (< 1 s, no file with link count > 1); then `lbuild.sh +Langlandscape.Smoke`: `⚠ [3765/3765] Replayed Langlandscape.Smoke`, **zero modules compiled**, `Smoke.olean` byte-identical with the same mtime (7 s); `lbuild Langlandscape LanglandscapeTests`: only replays; `lfile` OK; step-6 post-checks repeated, all clean; worktree removed with `git worktree remove`; sweep clean afterwards | ≈ 1 min |

Also checked:
- `lbuild.sh Langlandscape LanglandscapeTests` builds both roots (1.6 s each).
- `lfile.sh Audit/PrintAxioms.lean` gives `'Langlandscape.Smoke.eichlerMass_apply' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- Pin guard negative tests, each rc 99 with no Lake call:
  - on a scratch copy, a modified manifest and a missing manifest;
  - in the project, a temporary `.lake/package-overrides.json`.
- `lbuild.sh +AlgJL.Hyp.EichlerMass` and `lbuild.sh Mathlib` are refused (rc 1).
- `lbuild.sh LanglandscapeVendorStacks` fails, as expected while `Vendor/AxiomStacks/` is absent:
  `error: no such file or directory`. Loading the config with that `srcDir` missing is harmless; every other build
  passes. S01-X3 creates the directory.

Total build wall time of steps 3–7: about 1 minute. The plan estimated 6–8 min.

## Manifest diff (ours against `lean/trace-formula-project-import/lean/lake-manifest.json`)
```diff
@@ -109,9 +109,19 @@
    "inputRev": "v4.35.0",
    "inherited": true,
    "configFile": "lakefile.toml"
+  },
+  {
+   "type": "path",
+   "scope": "",
+   "name": "GL2TF",
+   "manifestFile": "lake-manifest.json",
+   "inherited": false,
+   "dir": ".lake/GL2TF",
+   "copy": false,
+   "configFile": "lakefile.toml"
   }
  ],
- "name": "GL2TF",
+ "name": "Langlandscape",
  "lakeDir": ".lake",
  "fixedToolchain": false
 }
```

## Lake log excerpts
Step 3 (a), dry check inside the sandbox. Only the import's existing warnings are replayed: 52 `AlgJL.*` modules and
2 `Definitions.*` modules.
```
⚠ [1086/1136] Replayed Definitions.Def_LocalLanglands_HeckePair
warning: Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_HeckePair.lean: imports `Mathlib.Algebra.Algebra.Defs` from package `mathlib`, which is designed for use with the module system; …
…
All targets up-to-date (3763 jobs).
check_frozen: frozen trees untouched since build.uH2WtK
```
Step 3 (b), first build inside the sandbox:
```
⚠ [3765/3765] Built Langlandscape.Smoke (8.5s)
warning: Langlandscape/Smoke.lean: imports `Mathlib.RingTheory.SimpleRing.Basic` from package `mathlib`, which is designed for use with the module system; consider adding `module` to the start of this file
Build completed successfully (3765 jobs).
check_frozen: frozen trees untouched since build.uH2WtK
lbuild: --smoke OK
```
Step 7, the seeded second worktree:
```
check_frozen: All targets up-to-date (3763 jobs). over 4 dependency modules
lbuild: lake build +Langlandscape.Smoke (MemoryMax=8G, LEAN_NUM_THREADS=2)
⚠ [3765/3765] Replayed Langlandscape.Smoke
Build completed successfully (3765 jobs).
check_frozen: frozen trees untouched since build.vsZD9i
lbuild: OK
```

## Notes for later WPs
- The import's oleans replay under P, as predicted in OVERVIEW §3.1(6). They were built at another path; the package
  id `GL2TF` and the options are unchanged.
- The "module system" warning about Mathlib imports appears in every non-`module` file. It is harmless and is the
  same warning the import shows.
- Wrapper diff against the import's `tools/` (changed lines): deps.conf 10, deps_load.sh 27, link_deps.sh 59,
  check_frozen.sh 5, lbuild.sh 77 (of which the `--smoke` block is about 50), lfile.sh 3, load_profiles.conf 1
  (header only). `prune_stale_build.sh` and `stale_build.py` were not copied.

## Amendment (submission bundle, 2026-11-15; Fabian-authorized exception to `agents/rules/frozen.md`)

The `require` of GL2TF now reads `path = "../trace-formula-project-import/lean"` (manifest `dir` likewise, regenerated
by `tools/make_manifest.py --pins`), because the official check builds a fresh clone, where the git-ignored
`.lake/GL2TF` does not exist. Outcome P is unchanged on the nodes: `tools/link_deps.sh` links the in-repo import's
`.lake` to `$GL2TF_IMPORT/.lake` (after `diff -rq` of the sources), so the node's built oleans are still read in place.
Lake's module traces hash the source contents, module names, package id and options, not the package directory, so the
link is equivalent to the former `.lake/GL2TF`.
