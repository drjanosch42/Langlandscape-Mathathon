# Draft update of `agents/rules/lean.md` (OVERVIEW §8 F9)

Status: **PROVISIONAL (global master, 2026-11-14)**. Drafted on `wip-plan` from the Fable audit
(`audits/stage-01-fable.md` C1, C3, M1, M3) and OVERVIEW §3. The global master applies it on `main` (`agents/` is
committed on `main` only) **before stage 1 starts**; Fabian may revisit. Base: `agents/rules/lean.md` as on `main`
at b5c4e7b. Four replacements (R1–R4) and one appended block (A1). Every replaced passage is quoted verbatim.

## R1 — project path
Replace
```
- Toolchain `leanprover/lean4:v4.35.0` (pinned in `lean/lean-toolchain`); Lake project lives in `lean/`.
```
by
```
- Toolchain `leanprover/lean4:v4.35.0` (pinned in `lean/lean-toolchain`; `lean/Langlandscape/lean-toolchain` is a byte
  copy). Our Lake project lives in `lean/Langlandscape/` (package `Langlandscape`; libs `Langlandscape`,
  `LanglandscapeTests`, `LanglandscapeVendorStacks`); it depends on the built import through the git-ignored symlink
  `lean/Langlandscape/.lake/GL2TF` (decision record `lean/Langlandscape/DECISION-PV.md`).
```

## R2 — the import: build wrappers, read-only
Replace
```
- `lean/trace-formula-project-import/`: curated fork (package `GL2TF`, libs `AlgJL`, `AlgJLTests`, Vendor);
  read its `README.md` before use; build only via its `tools/lbuild.sh` / `tools/lfile.sh`.
```
by
```
- `lean/trace-formula-project-import/`: curated fork (package `GL2TF`, libs `AlgJL`, `AlgJLTests`, Vendor);
  read its `README.md` before use; build only via its `tools/lbuild.sh` / `tools/lfile.sh`.
  **During implementation `lean/trace-formula-project-import/lean/**` is read-only for all agents** (our project
  reads its oleans in place). Any change goes through the global master, who rebuilds the import with its own
  `tools/lbuild.sh` in the main checkout before any stage build resumes. Our project never builds GL2TF modules.
- Build only through the wrappers of the project you work in: `lean/Langlandscape/tools/{lbuild.sh,lfile.sh,
  check_frozen.sh,link_deps.sh}` for our project, `lean/trace-formula-project-import/tools/*` for the import. Never call
  `lake` directly in either project (opencode jobs included).
```

## R3 — sorries
Replace
```
- No `sorry`/`admit`/new `axiom` on `main`; on `wip-lean` every `sorry` is tracked in `lean/SORRIES.md`.
```
by
```
- No `sorry`/`admit`/new `axiom` on `main`. `sorry` is allowed on `impl/*` branches only for declared stubs; on
  `wip-implementation` (and `wip-lean`) every `sorry` is tracked in `lean/Langlandscape/SORRIES.md`. Hypotheses are
  `def … : Prop` in `lean/Langlandscape/Langlandscape/Hyp/<Name>.lean`, taken as explicit arguments (never `axiom`,
  never a global instance), and registered in `lean/Langlandscape/HYPOTHESES.md`. Both registries and the root import
  files are edited only by the stage master (plan/implementation/OVERVIEW.md §1, §3.6).
```

## R4 — build before commit
Replace
```
- `lake build` must pass before every commit to `wip-lean`. `.lake/` is not committed.
```
by
```
- The build (`tools/lbuild.sh` of the touched targets, run through the wrapper, never `lake build` directly) must
  pass before every merge into `wip-implementation` / `wip-lean`. `.lake/` is not committed.
```

## A1 — append at the end of the file
```
- **Pin guard — never delete or hand-edit `lake-manifest.json`.** A missing manifest makes Lake run a full update
  through the frozen farm symlinks. Every wrapper of `lean/Langlandscape/` checks `tools/pins.sha256` (sha256 of
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) and the absence of `.lake/package-overrides.json` before any
  `lake` call, and exits 99 on failure. The manifest is regenerated only by `tools/make_manifest.py`, with
  `pins.sha256` updated in the same commit, by the stage master. Exit 99 from any wrapper: stop, alert the global master.
- **Seeding a worktree's `.lake/build`**: only with `tools/new_wp.sh` or `cp -a --reflink=auto` from the `impl`
  worktree, holding that checkout's lock shared. **Never hard links** (`cp -al`, `ln`): a rebuild in one worktree would
  corrupt the other's build. Remove worktrees only with `git worktree remove` (never `rm -rf`: `.lake/packages/*` and
  `.lake/GL2TF` are symlinks into frozen trees).
- **Lock order** (for anyone writing or changing a script that takes Lean locks): (1) `exp.lock` (experiment checks
  only), (2) `lean.lock`, (3) the per-checkout lock, (4) a node slot, (5) the memory wait. Never wait for (3) while
  holding (4). Workers only call the wrappers, which take the locks themselves; never hold a Lean lock by hand.
```
