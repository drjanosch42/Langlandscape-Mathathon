# Rule: lean/

- Toolchain `leanprover/lean4:v4.35.0` (pinned in `lean/lean-toolchain`; `lean/Langlandscape/lean-toolchain` is a byte
  copy). Our Lake project lives in `lean/Langlandscape/` (package `Langlandscape`; libs `Langlandscape`,
  `LanglandscapeTests`, `LanglandscapeVendorStacks`); it depends on the in-repo import by `path = "../trace-formula-project-import/lean"` (since the submission bundle,
  2026-11-15; a fresh clone builds). On nodes, `tools/link_deps.sh` links that import's `.lake` to the node's built import
  (git-ignored symlink); re-run it once per worktree after updating (decision record `lean/Langlandscape/DECISION-PV.md`, `BUILDING-LEAN.md`).
- The frozen-toolchain rules of `agents/rules/frozen.md` apply without exception (no `lake update` etc.).
- `lean/trace-formula-project-import/`: curated fork (package `GL2TF`, libs `AlgJL`, `AlgJLTests`, Vendor);
  read its `README.md` before use; build only via its `tools/lbuild.sh` / `tools/lfile.sh`.
  **During implementation `lean/trace-formula-project-import/lean/**` is read-only for all agents** (our project
  reads its oleans in place). Any change goes through the global master, who rebuilds the import with its own
  `tools/lbuild.sh` in the main checkout before any stage build resumes. Our project never builds GL2TF modules.
- Build only through the wrappers of the project you work in: `lean/Langlandscape/tools/{lbuild.sh,lfile.sh,
  check_frozen.sh,link_deps.sh}` for our project, `lean/trace-formula-project-import/tools/*` for the import. Never call
  `lake` directly in either project (opencode jobs included).
- Exception, node `abhijit` only (global master 2026-11-14): a draft check of a Mathlib-only file (imports `Mathlib.*` and the WP's own `Langlandscape.CommAlg.*` files only) by a direct `lean` call with `LEAN_PATH` into the frozen Mathlib's `.lake/build/lib/lean` trees, outputs (`-o`) only into a scratch directory outside the repo and outside the frozen tree, under a memory cap, followed by a `find <frozen tree> -newer <marker>` check. Never `lake`; never a wrapper of `lean/Langlandscape/` there. This is not an acceptance check; acceptance is the TITAN round.
- Mathlib conventions for naming, style, and docstrings; one topic per file.
- **Lean file header (Abhijit/Fabian, 2026-11-14; replaces the SPDX two-liner for Lean):** the first lines of every Lean file are exactly
  ```
  /-
  Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fabian Januszewski, Abhijit A J
  -/
  ```
  (only these two names). Exceptions: the generated aggregators `Langlandscape.lean` / `LanglandscapeTests.lean` (no header) and
  vendored files (`Vendor/**`, upstream headers). Licence compliance comes from `REUSE.toml` (`**/*.lean` → Apache-2.0).
- **Imports (Abhijit, 2026-11-14; the earlier hold is LIFTED; build time is the priority):** never umbrella imports. **Merge gate
  for main: every new Lean file has minimised imports.** Method per file: (1) in a scratch copy add `import Mathlib.Tactic.MinImports`
  and `#min_imports` at the end (run via `tools/lfile.sh` on TITAN/CONCEPTD, never `lake`); (2) do not trust the list: check by hand
  that the file builds with it, drop imports one at a time, prefer narrower Mathlib files where cheap; (3) the file AND every file
  importing it still build (dependants that cannot be built locally, e.g. GL2TF/AlgJL-dependent ones, need a TITAN/CONCEPTD
  build before the change counts as final: lesson of s04-int9, Ribet/Mazur.lean); (5) **`#min_imports` lists are
  not sufficient for Mathlib imports**: tactic extensions (e.g. `Mathlib.Tactic.NormNum.Prime`), instances and some constants are
  invisible to them (S04-IMP-old: CentralSimple, Mazur, SerreFree, SerreCoh broke). Drop a `Mathlib.*` import only if a full root build
  proves it redundant; by default keep them and minimise project/AlgJL imports, axioms unchanged (a dependant relying on a transitive import gets it explicitly); (4) keep the
  public/private split and the module layout. Existing files: GL2TF/AlgJL-dependent ones on our side (stage WP), the locally
  buildable ones on Abhijit's branch `abhijit/min-imports`.
- **Docstring layout:** the docstring sits directly before the declaration; attributes (`@[simp]`, …) go between the docstring and
  the declaration; `include … in` goes above the docstring. No docstring line may start with `theorem`/`lemma`/`def`.
- **Module layout (Abhijit, 2026-11-14; build time is the priority; Mathlib layout, e.g. Mathlib/RingTheory/Ideal/Colon.lean):**
  header, `module`, the imports, the module docstring `/-! … -/`, then `@[expose] public section`, then `namespace …`.
- **Public/private imports (Abhijit, 2026-11-14; exception to the minimisation hold):** a dependency needed only inside proofs (not in
  any public statement or exposed definition) is a plain `import`; everything else is `public import`. This changes how, not which,
  files are imported. Done as a step AFTER the module conversion. Tooling: `lake exe shake` is NOT allowed yet (direct `lake` is
  forbidden, and building `shake` may write into the frozen Mathlib tree); until the global master provides a checked wrapper, the
  split is done by hand and verified by a TITAN build.
- Not adopted (pending Abhijit): `open scoped …` as a build-time measure.
- **Module system (target, converted bottom-up):** a file becomes `module` (header, then `module`, then `public import …`, with
  cross-file declarations marked `public`) once all its imports are modules. Files importing the frozen import `AlgJL`/`GL2TF`
  (non-module, read-only) stay non-module until a global-master decision on converting the import. Mathlib-only and
  CommAlg/Ordinary-style files convert first; a conversion is its own WP with a TITAN build, never mixed into a proof WP.
- No `sorry`/`admit`/new `axiom` on `main`. `sorry` is allowed on `impl/*` branches only for declared stubs; on
  `wip-implementation` (and `wip-lean`) every `sorry` is tracked in `lean/Langlandscape/SORRIES.md`. Hypotheses are
  `def … : Prop` in `lean/Langlandscape/Langlandscape/Hyp/<Name>.lean`, taken as explicit arguments (never `axiom`,
  never a global instance), and registered in `lean/Langlandscape/HYPOTHESES.md`. Both registries and the root import
  files are edited only by the stage master (plan/implementation/OVERVIEW.md §1, §3.6).
- **Docstring rule (OVERVIEW §3.6, O8):** every `theorem`/`lemma`, including `private` ones and those in
  `LanglandscapeTests/`, has an immediately preceding `/-- … -/` containing a label `s<NN>-…` (stage-tex label until the
  chapter exists, then the `mathematics/` label); public `def`/`structure` have a docstring.
- Each main theorem's docstring references the corresponding statement in `mathematics/`.
- The build (`tools/lbuild.sh` of the touched targets, run through the wrapper, never `lake build` directly) must
  pass before every merge into `wip-implementation` / `wip-lean`. `.lake/` is not committed.
- Milestones close only after `agents/roles/lean_audit.md` passes.
- **Pin guard — never delete or hand-edit `lake-manifest.json`.** A missing manifest makes Lake run a full update
  through the frozen farm symlinks. Every wrapper of `lean/Langlandscape/` checks `tools/pins.sha256` (sha256 of
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) and the absence of `.lake/package-overrides.json` before any
  `lake` call, and exits 99 on failure. The manifest is regenerated only by `tools/make_manifest.py`, with
  `pins.sha256` updated in the same commit, by the stage master. Exit 99 from any wrapper: stop, alert the global master.
- **Seeding a worktree's `.lake/build`**: only with `tools/new_wp.sh` or `cp -a --reflink=auto` from the `impl`
  worktree, holding that checkout's lock shared. **Never hard links** (`cp -al`, `ln`): a rebuild in one worktree would
  corrupt the other's build. Remove worktrees only with `git worktree remove` (never `rm -rf`: `.lake/packages/*` and
  `lean/trace-formula-project-import/lean/.lake` are symlinks into frozen trees).
- **Lock order** (for anyone writing or changing a script that takes Lean locks): (1) `exp.lock` (experiment checks
  only), (2) `lean.lock`, (3) the per-checkout lock, (4) a node slot, (5) the memory wait. Never wait for (3) while
  holding (4). Workers only call the wrappers, which take the locks themselves; never hold a Lean lock by hand.

(Rules R1–R4 and A1: adopted by the global master 2026-11-14 from plan/implementation/RULES_LEAN_UPDATE.md; applied in stages 1–6, no longer provisional.)
