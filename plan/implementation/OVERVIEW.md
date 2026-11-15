# OVERVIEW — implementation plan (P3), conventions for all stages

Status: binding for all stage plans `stage-NN.md` and for implementation. **Revision 2 (2026-11-14, after stage 1;
re-planning brief `briefs/replan-s02-06.md`, conventions A–F → §5, §5.2, §4.3, §9, §6.1, §4.4); cross-stage integration
(`audits/cross-stage-consistency.md`): §4.3 tool/merge-order items, §5.2, §6.1, §7 final.** It overrides
`briefs/common.md` where they differ, but keeps what common.md fixes (WP id scheme, schema fields, difficulty classes).
**Precedence (O9):** this OVERVIEW also overrides `plan/implementation/EXPERIMENT_PROTOCOL.md` §1 (limits, slots: ≤ 8
subagents per delegating agent, Fable in parallel, TITAN slots §4.3) and §7 (opencode strands: none are planned), and
`briefs/common.md` l. 31 (concurrency). It does **not** override `agents/rules/*`; where those are stale the global
master updates them before stage 02 launches (F18, §8), and until then the stage master follows this OVERVIEW and
logs the conflict in `runs/sNN.md`.
Stage-1-specific text is kept as history and marked **DONE (stage 1)**; its decisions stay in force. Claims are marked
*verified* (read in source/files), *measured* (timestamps/logs, mostly `runs/s01.md`, `agents/status/master_log.md`) or
*estimate*.

## 1. Work packages (WPs)

**Id** `S<NN>-<T><k>`: NN = stage 01–06, T ∈ {`X` infra/setup, `M` maths/LaTeX, `L` Lean, `C` code/Python/CAS,
`H` HACS, `T` talk}, k = 1, 2, … in DAG order. Sub-WPs created during execution: `S02-L3a`, `S02-L3b` (never renumber).
Experiment strands of one WP: `S02-L5@opus`, `S02-L5@sonnet` in the plan; on branches and in TITAN job ids the strands
are **neutral** (`a`/`b`, §4.3), model names only in `experiments/LOG.md`.

**Schema** (one table row or block per WP; all fields mandatory, `—` if empty):
`id` | track | goal (1 sentence) | inputs (stage-tex labels such as `def:s02-tree`, `if:s01-…`; Lean declarations of
earlier stages by full name, e.g. `Langlandscape.Brandt.Tl_selfAdjoint_U0'`; import declarations `GL2TF.*`) | outputs
(files; Lean declaration names; result files) | acceptance check | difficulty | **model (+fix)** (§5.1) | est. agent wall
(min, *estimate*) | est. TITAN runs (Lean only) | **TITAN round** (`int1`, `int2`, …, or `—`; §4.3) | **remote-eligible**
(`yes`/`no`, §6.1) | deps.

- **difficulty**: `mechanical` (copy/rename/boilerplate, mechanical check), `routine` (standard proof or code, known
  route), `hard` (known route, long or fiddly: heavy elaboration, coercions, big case analyses), `conceptual` (route not
  fixed: needs a design or mathematical decision). Lean `mechanical-with-meaning` (new Props/defs against an existing or
  drafted API) is a sub-class of `mechanical` with its own model row (§5.1).
- **model** ∈ {`haiku`, `sonnet`, `opus`, `fable`} (cost order cheapest first). **`muse` and `mistral` are dropped as
  implementers** (stage-1 study, §5.1); no opencode WPs are planned. The `+fix` part names the fix-round budget, e.g.
  `sonnet (+1 opus fix ≤ 5 min)`, `opus (+1 planned opus fix)`, `haiku (ladder → sonnet)`.
- **Acceptance checks must be mechanical where possible**: `latexmk -pdf` exit 0 and no undefined refs/cites; for Lean:
  the WP's spec line passes in its TITAN round — `CHECK_WP <wp> rc=0 0 FAIL lines` and its `AXIOMS` line `rc=0
  nonstandard=0` (§4.3, §9) — on the **integration tree**; `pytest` pass; numbers equal a stated table (give the table
  or its file). Non-mechanical parts name the reviewer.
- **Interfaces.** Every Lean WP cites the statement it formalizes (stage-tex label or `mathematics/` label); the
  statement must *exist* (not be proved) before the WP starts (§6). Every `Hyp.*` used names its registry row (§3.6). A
  Lean WP may start against an upstream WP's **declared signatures** before that upstream is green (stacking, §4.3).
- **Size** (calibrated, §4.4): local short WPs 2–17 min; Lean WPs under TITAN 33–80 min wall (agent-active 10–20 min,
  *estimate*);
  a WP whose estimate exceeds ~60 min agent-active is split.
- **Aggregator files** (`lean/Langlandscape/Langlandscape.lean`, `…Tests.lean`, `SORRIES.md`, `HYPOTHESES.md`,
  `Audit/PrintAxioms.lean`, `Vendor/*/MANIFEST.tsv`, `mathematics/main.tex`, `mathematics/references.bib`,
  `code/results/INDEX.md`, `talk/main.tex`) are edited **only by the stage master** on `wip-implementation` (or on the
  integration branch, §4.3) when merging. A WP — local or remote (§6.1) — delivers its one-line additions in its final
  report instead.

## 2. Branches, worktrees, merges

| Branch | Base | Worktree | Who writes | Merged by → into |
|---|---|---|---|---|
| `wip-implementation` | `main` (re-synced from `main` before each stage) | `/home/janosch/dev/Langlandscape-wt/impl` | stage master (merges, aggregator files, outbox, runs file) | global master → `main` at stage end |
| `impl/sNN-<wp>` (e.g. `impl/s02-l3`) | `wip-implementation`, or the head(s) of the fixed upstream WP branch(es) when stacking; never an integration branch's `.titan/` commit (§9 lesson 4) | `/home/janosch/dev/Langlandscape-wt/sNN-<wp>` | one WP worker | stage master → `wip-implementation` (`--no-ff`) after the WP is green in an integration round |
| `impl/sNN-int<k>` (e.g. `impl/s02-int2a`) | `wip-implementation` + merged WP drafts; its **top commit contains only `.titan/`** (spec + axiom files, §4.3) | stage master's integration worktree `…-wt/sNN-int` | stage master only (merges of drafts, aggregator lines, the `.titan/` top commit; axiom files are written by the stage master from the haiku WP's report, §9 lesson 2) | **never merged**; if its content is wanted, merge the top commit's parent `impl/sNN-int<k>~1`; kept until stage end |
| `exp/sNN-<wp>-<model>` | `wip-implementation`, or the fixed upstream WP head(s) when stacking | `…-wt/exp-sNN-<wp>-<model>` | one experiment strand (§5.2) | stage master merges **at most one** strand (its head, which carries no `.titan/`); others stay unmerged as data (local only, never pushed) |
| `titan-in/<job-id>` | a throwaway commit whose only content is `.titan/`, on top of a strand head or a single-WP head (§4.3) | — (a ref only) | global master pushes `<sha>:refs/heads/titan-in/<job-id>` | deleted after TITAN fetched it; the commit itself is never merged |
| `titan/<job-id>` (e.g. `titan/s02-int2a-1`) | as sent | TITAN clone `/home/claude/dev/Langlandscape` | TITAN only | global master fetches; stage master reads `.titan/out/*`, never merges it |
| `abhijit/<wp-id-lowercase>` (e.g. `abhijit/s03-m4`) | `origin/wip-implementation` at the sha in the request, or the head of an upstream `abhijit/<wp>` (stacking; (global master 2026-11-14, Abhijit batch 1)) | Abhijit's node | one remote WP (§6.1) | global master fetches → stage master merges into `wip-implementation` (remote S06 early-lane drafts: the early coordinator merges them into `impl/s06-int<k>`; (global master 2026-11-14, Abhijit batch 1)) |

- WP branches change only their track directory (`mathematics/`, `lean/Langlandscape/`, `code/`, `talk/`), plus files
  explicitly assigned in the WP; **never `lean/Langlandscape/.titan/`** (§4.3). `wip-implementation` is the one branch
  that spans all four track directories; the per-track `wip-*` branches are not used during implementation (global
  master syncs them from `main` after each stage merge). Nobody edits `plan/` or `agents/` from an impl branch, except
  the stage master's `plan/implementation/runs/sNN.md`, `plan/implementation/outbox/*` (§4.3) and
  `plan/implementation/experiments/**` (strand records, §5.2).
- **Merge gate** (stage master): the WP's acceptance check passes **on the merged result**. For Lean that is the
  integration round in which the WP's spec line passed (the integration tree = `wip-implementation` + drafts); a WP whose
  check only passed on its own branch is not done. Before merging a WP branch: `git diff --name-only
  wip-implementation...impl/sNN-<wp> | grep -c '^lean/Langlandscape/\.titan/'` = 0 (the same grep applies to a strand
  before its merge). **Stacking rule (O6):** a WP is merged only together with, or after, all its upstream WPs; the
  stage master then builds `Langlandscape LanglandscapeTests` on the merged `wip-implementation` sha (step 2 of every
  job, §4.3) before the next merge. When a WP branch is based on unmerged upstream drafts, compare `git diff
  --name-only` against the WP's declared files only.
- **`.lake/build` seeding** (regime (a) in force per `DECISION-PV.md`; procedure in `agents/rules/lean.md`, `tools/new_wp.sh`): only relevant when a local
  Lean build runs again; on TITAN every job runs in a checkout seeded by reflink copy from the previous round's build
  (TITAN's own procedure, see the s01 job specs). Never hard links.
- Commit/push: workers commit on their branch, never push. Only the global master pushes (`main`, `wip-implementation`,
  `impl/sNN-int<k>`, `titan-in/*`). Commit messages `<area>: <imperative>` with area ∈ {math, lean, code, talk, plan,
  agents, msg}; include the WP id.
- **Cleanup** (stage master, after the merge): `git worktree remove <path>` (never `rm -rf`; `.lake/packages/*` and
  `.lake/GL2TF` are symlinks into frozen trees), then `git branch -d impl/sNN-<wp>`. Integration and experiment
  branches are kept until the stage report is written. ≤ 12 live worktrees per node (Fabian may raise it to 16 for
  `.lake`-free worktrees, stage-02 Q6).

## 3. Lean project structure (decision)

**Status: DONE (stage 1).** S01-X1a decided **P with seeding regime (a)** (`lean/Langlandscape/DECISION-PV.md`,
9f49151); S01-X1b (lock model, `SLOTS ≤ 3`) merged a8b6ffb. §3.1–§3.5 are kept as the record of the decision; P′ and V
are not in force. The layout §3.3, the wrapper rules §3.4 and the hypothesis/sorry conventions §3.6 remain binding.

### 3.1 Findings (read-only feasibility analysis, Lake 5.0.0-src+eb6cafb = Lean v4.35.0; *verified* in Lake sources)
1. **Offline resolution.** `lake build` with a manifest present calls `Workspace.materializeDeps` (no update, no manifest
   write). Every dependency — direct or transitive — is looked up **by name in the root manifest only**; a missing one is an
   error, never a fetch. A git entry whose checkout HEAD equals `rev` returns early with no fetch (but Lake *resets the
   origin URL* if it differs: our `link_deps.sh` copy keeps the import's byte-equal URL check). A `path` entry
   (`{"type":"path","dir":…,"copy":false}`, manifest v1.3.0) is used in place; `validateManifest` does not warn for
   path/path. So a manifest = the import's manifest + one path entry resolves fully offline. **But a missing
   `lake-manifest.json` makes Lake silently run a full update** (fetch, git inside `.lake/packages/<pkg>`, i.e. through
   the farm symlinks); a malformed one only throws (*verified*, Fable A.1). Hence the pin guard (§3.4).
2. **The dependency's manifest and `.lake/packages`** are *not* used for resolution: GL2TF's `lake-manifest.json` is read
   only for its `fixedToolchain` flag (`false`); mathlib & co. resolve to **our** `.lake/packages/<pkg>` (symlinks into
   the same frozen farm). Config oleans of `lakefile.lean` deps are written under the **root** workspace
   (`<ws>/.lake/config/<idx>`), not into the dependency.
3. **Build artefacts of a path dependency** live in the dependency's own `.lake/build`. Building GL2TF from our project
   would write into `lean/trace-formula-project-import/lean/.lake/build` (git-ignored, not a frozen path in
   `frozen.md`, but the import must only be built by its own wrappers). Hence: **our project must never build GL2TF**; it
   only reads its oleans, enforced by a dry `lake build --no-build +AlgJL.…` check (below).
4. **Worktrees.** A relative `path = "../trace-formula-project-import/lean"` would point at each worktree's *unbuilt*
   copy of the import → a full import build (*measured*: 112 modules in 1786 s ≈ 30 min locally from olean mtimes; 6:43 on
   TITAN, master log) per worktree. Therefore the path points at a git-ignored symlink `.lake/GL2TF` → the node's one
   **built** import (main checkout `/home/janosch/dev/Langlandscape/lean/trace-formula-project-import/lean`, 112 oleans,
   339 MB, `.hash` files present). Lake canonicalises the path (`resolvePath` = realpath).
5. **Wrappers and locks.** The import's `link_deps.sh` refuses any `path` key and any non-git manifest entry;
   `lbuild.sh` takes the node-wide `lean.lock` *exclusively* (one build per node, blocking all file checks);
   `check_frozen.sh` dry-checks only `DEP_ROOTS` modules. Our copies change exactly these points (§3.4).
6. The import oleans were built at another path and copied (trace logs show `/home/janosch/dev/trace_formula_gl2/…`,
   but the absolute path is only a caption). *Verified* (Fable A.5/A.6, Lake `Build/Common.lean:213–255`,
   `Build/Module.lean:1066–1100`): up to date = saved `depHash` equals the recomputed input hash, which mixes the Lean
   version, the source content hash, the options `-DautoImplicit=false -DrelaxedAutoImplicit=false`, `Module.name` and
   `Package.id? = GL2TF`; then the log is replayed and nothing is written, provided the `.hash` files exist
   (*computed*: 112 `.olean`/`.ilean`/`.c`, each with its `.hash`). Under P the package identity is unchanged, so the
   oleans should replay (*judgement*: P, not P′; S01-X1a decides). Under V the package is `Langlandscape`: nothing is
   reusable from the import. Copying `.lake/build` between worktrees of the same project is trace-valid (§2 seeding).
   Dependency build caches are fetched only for scope ∈ {`leanprover`, `leanprover-community`} or `preferReleaseBuild`
   with a missing build dir: **keep `"scope": ""`** in the path entry (*verified*, A.4).
7. Vendoring cost: the import closure our stage-1 code needs (`AlgJL.VolIII.{P2,Brandt}.*`, `Hyp.EichlerMass`) is
   **37 AlgJL modules + 2 `Definitions.*` (AnthropicFLT, via `VolI.P1.Spherical`) + 2 `FLT.*` (ImperialFLT:
   `FLT.NumberField.Padics.RestrictedProduct`, `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic`), 25.1k lines**
   (*computed*, Fable A.7; + `AlgJLTests.*` files if a test uses the import's Hurwitz instances). All import names used
   by the L-WPs lie in it except `jl_formula_identity` (`AlgJL.VolIII.P1.JLFormula`). ≈ 20–25 min first build per fresh
   worktree locally (*estimate*, scaled from the 30 min import build).

### 3.2 Decision (settled: P, regime (a))
- **Primary P (path dependency):** new Lake project `lean/Langlandscape/` (package `Langlandscape`) with
  `[[require]] name = "GL2TF", path = ".lake/GL2TF"`, **generated** manifest (§3.3), never builds GL2TF (dry-check
  gate). P needs the import's sources to stay fixed: **`lean/trace-formula-project-import/lean/**` is read-only during
  implementation** (Fable M3(b); decision §8 F1); any change goes through the global master, who rebuilds with the
  import's `tools/lbuild.sh` before any stage build resumes.
- **Fallback V (vendor):** byte copies (no edits at all) of the 37+2+2 closure files (§3.1(7)) under `Vendor/GL2TF/`,
  `Vendor/AnthropicFLT/` and `Vendor/ImperialFLT/`, **keeping module names `AlgJL.*`/`Definitions.*`/`FLT.*` and
  declaration names `GL2TF.*`**. MANIFEST.tsv: for the `AlgJL.*` files `sha256_upstream = sha256_local` (upstream = the
  import path at the repo commit); for the four third-party files **the import's `Vendor/MANIFEST.tsv` rows copied
  verbatim** (true upstream URL, rev, `sha256_upstream`; `modified = yes` for the two AnthropicFLT files) with
  "via lean/trace-formula-project-import @<commit>" added to the note column — never the import as "upstream" for
  them. `Vendor/AnthropicFLT/{LICENSE,NOTICE}` and `Vendor/ImperialFLT/LICENSE` copied verbatim from the import. No
  namespace clash arises because P and V never coexist; no drift because the import is read-only (`tools/vendor_check.sh`
  re-hashes against the import). Cost: per-worktree first build ≈ 20–25 min (*estimate*), ~150–250 MB `.lake` each
  (seeding, §2, removes it for all but the first).
- **Downstream WPs are agnostic**: under both P and V our files `import AlgJL.VolIII.Brandt.Pairing` etc. and use
  `GL2TF.Quat.*` names. Only `lakefile.toml`, `lake-manifest.json`, `deps.conf` (`DEP_ROOTS`) and `Vendor/` differ.
- Fallback trigger: S01-X1a fails (§3.5). Intermediate case P′: if only "GL2TF oleans stale" fails, the **global master**
  runs the import's own `tools/lbuild.sh AlgJL` once in the main checkout (≈ 30 min; the documented import route), then
  S01-X1a is re-run; still failing → V.
- The top-level `lean/lean-toolchain` (v4.35.0) stays; elan uses the nearest file, which is our byte copy. *History (DONE, F9):* the old
  statement "the Lake project lives in `lean/`" in `agents/rules/lean.md` was updated by the global master
  (→ `lean/Langlandscape/`; `SORRIES.md` at `lean/Langlandscape/SORRIES.md`) before stage 1 (`RULES_LEAN_UPDATE.md`).

### 3.3 Layout of `lean/Langlandscape/` (P; V differences marked)
```
lean/Langlandscape/
  lakefile.toml          name="Langlandscape", defaultTargets=["Langlandscape"]; [leanOptions] autoImplicit=false,
                         relaxedAutoImplicit=false; [[require]] mathlib (git url + rev 56a005855ea1… byte-equal to the import);
                         [[require]] name="GL2TF" path=".lake/GL2TF"                                  (V: absent)
                         [[lean_lib]] Langlandscape; [[lean_lib]] LanglandscapeTests;
                         [[lean_lib]] name="LanglandscapeVendorStacks" srcDir="Vendor/AxiomStacks" globs=["StacksCore.+"]
                                      leanOptions={ maxSynthPendingDepth = 3 }
                         (V adds: LanglandscapeVendorGL2TF srcDir="Vendor/GL2TF" globs=["AlgJL.+"]; LanglandscapeVendorFLT
                          srcDir="Vendor/AnthropicFLT" globs=["Definitions.+"] with the import's AlgJLVendor leanOptions;
                          LanglandscapeVendorImperial srcDir="Vendor/ImperialFLT" globs=["FLT.+"]
                          leanOptions={ maxSynthPendingDepth = 3 } as the import's AlgJLVendorImperial)
  lean-toolchain         `cp` byte copy of the import's
  lake-manifest.json     GENERATED, never hand-edited: committed `tools/make_manifest.py` loads the import's manifest, sets
                         "name": "Langlandscape", appends exactly this entry (keys as written; "scope": "", "copy": false,
                         "inherited": false), dumps it                                                  (V: no entry)
                         {"type":"path","scope":"","name":"GL2TF","manifestFile":"lake-manifest.json",
                          "inherited":false,"dir":".lake/GL2TF","copy":false,"configFile":"lakefile.toml"}
                         S01-X1a records the diff against the import's file in DECISION-PV.md. Never deleted (§3.4 pin guard).
  Langlandscape.lean     root import file (stage master only)
  Langlandscape/         our code, one topic per file: Langlandscape/<Area>/<Topic>.lean, namespace Langlandscape.<Area>
    Hyp/<Name>.lean      registered hypotheses (§3.6)
  LanglandscapeTests.lean, LanglandscapeTests/   non-vacuity examples, instances of hypotheses
  Audit/PrintAxioms.lean `#print axioms` of headline theorems (run with lfile.sh; used by lean_audit)
  Vendor/AxiomStacks/    LICENSE (Apache-2.0 verbatim), ATTRIBUTION.md, MANIFEST.tsv (import's column format), PROVENANCE.md,
                         StacksCore/** : the 8 Skolem–Noether files (893 lines) at upstream module paths, rev c496df0d9bee…,
                         unmodified (modified=no) unless a change notice is added at the file top (Apache §4(b))
  Vendor/GL2TF/, Vendor/AnthropicFLT/, Vendor/ImperialFLT/  (V only) byte copies; AnthropicFLT/{LICENSE,NOTICE},
                         ImperialFLT/LICENSE verbatim from the import; MANIFEST rows per §3.2 (third-party rows verbatim
                         from the import's Vendor/MANIFEST.tsv + "via lean/trace-formula-project-import @<commit>")
  DECISION-PV.md         S01-X1a record: P / P′ / V, seeding (a) or lanes (c) (§2), manifest diff, wall times, Lake log excerpts
  SORRIES.md             every sorry: file:line, declaration, WP id, owner, reason, planned discharge
  HYPOTHESES.md          hypothesis registry (§3.6)
  tools/                 copies of the import's tools (§3.4) + make_manifest.py + pins.sha256;
                         tools/deps.local.conf git-ignored (.git/info/exclude)
  .lake/                 git-ignored: packages/<pkg> -> farm (link_deps.sh), GL2TF -> built import (P), build/, config/
```

### 3.4 Wrapper copies (`lean/Langlandscape/tools/`) — what changes
All copies get a header line "COPY of lean/trace-formula-project-import/tools/<f> @<commit>, changed: …". In every
script `lean="$repo"` (the project root is the Lake dir; no `lean/` subdir). Otherwise unchanged:
- **Pin guard (fail-closed, Fable C1; S01-X1a).** `tools/pins.sha256` (committed by S01-X1a) holds the sha256 of
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. `deps_load.sh` (sourced by every wrapper) runs
  `sha256sum -c --quiet tools/pins.sha256` and checks that `.lake/package-overrides.json` is absent, **before any
  `lake` invocation**; on failure exit 99 without calling Lake. Reason: a missing manifest = silent `lake update` through
  the farm symlinks (§3.1(1)); the post-flight `find -newer` only reports damage afterwards. `lake-manifest.json` is
  never deleted or hand-edited; it is regenerated only by `tools/make_manifest.py` and `pins.sha256` updated in the same
  commit (stage master; never in a WP).
- `deps.conf`: same pins/limits (`SLOTS=2`, `BUILD_MEMORY_MAX=8G`, `FILE_MEMORY_MAX=6G`, `LEAN_THREADS=2`, same
  `LOCK_DIR=/home/janosch/.cache/gl2tf`, `FROZEN_TREES`). New: `GL2TF_IMPORT` (default derived in `deps_load.sh`:
  `$(git -C $repo rev-parse --path-format=absolute --git-common-dir)/../lean/trace-formula-project-import/lean`, i.e.
  the main checkout's built import, from any worktree); P: `DEP_ROOTS` += `AlgJL AlgJLTests Definitions FLT`
  (`AlgJLTests`: the first-component match does not cover it, and a stale test module imported by `LanglandscapeTests`
  would be built *into the import*; Fable M3(a)) and `FROZEN_TREES` += `$GL2TF_IMPORT`. V: neither.
- `deps_load.sh`: pin guard (above); local-conf allowlist += `GL2TF_IMPORT` (S01-X1a), and `SLOTS` (only ≤ 3; used on
  TITAN = 3; S01-X1b).
- `link_deps.sh`: lakefile check allows `path` exactly once, in the `[[require]]` named `GL2TF` with value
  `".lake/GL2TF"`; manifest check allows exactly one `type: path` entry (that one) and skips it in the git loop; it
  creates/verifies `.lake/GL2TF -> $GL2TF_IMPORT` and verifies that the import's manifest git entries (name, url, rev)
  and `lean-toolchain` equal ours and that `$GL2TF_IMPORT/.lake/build/lib/lean/AlgJL.olean` exists.
- `check_frozen.sh`: unchanged logic; through `DEP_ROOTS` its dry `lake build --no-build` now covers every imported
  `AlgJL.*`/`AlgJLTests.*` module, so "All targets up-to-date" **proves GL2TF will not be rebuilt**; post-flight
  `find -newer` covers the import. The log pattern that fails the dry check gains `fetching|materializing`
  (→ `manifest out of date|cloning|URL has changed|checking out|updating|fetching|materializing`).
- `lbuild.sh`: target allowlist `Langlandscape`, `LanglandscapeTests`, `LanglandscapeVendorStacks` (V: + the three
  vendor libs), `+M` for modules with a source file in the project; GL2TF targets refused; audit modes refused (as in the
  import). Lock model in S01-X1a: **the import's** (`lean.lock` exclusive, no slot). `--smoke` mode: S01-X1a step 3 only.
- `lfile.sh`: S01-X1a: same as the import's (lean.lock shared → slot → memory wait → `check_frozen.sh --file`).
- **Lock model of S01-X1b** (separate WP, §3.5; until it is merged the X1a model holds and merge gates are batched,
  stage-01 R4): `lbuild.sh` takes `lean.lock` *shared* (an import `lbuild` still excludes everything) + one node-wide
  `slot.N` (shared with `lfile.sh`, so ≤ `SLOTS` Lean jobs (scopes) per node in total) + an *exclusive* per-checkout lock
  `$LOCK_DIR/ll-<sha1 of realpath of the project>.lock`; `lfile.sh` takes the per-checkout lock *shared* (no check while
  this checkout builds). So two worktrees can build concurrently; each scope 8G.
- **Acquisition order (Fable C3), in both scripts and in every model:** (1) `exp.lock` if an experiment check
  (EXPERIMENT_PROTOCOL §1.5), (2) `lean.lock` (shared; X1a `lbuild`: exclusive), (3) the per-checkout lock (`lbuild`:
  exclusive, `lfile`: shared; X1b only), (4) a node slot, (5) the memory wait. **No script waits for (3) while holding
  (4)**; the slot is taken with a blocking retry loop only after (3) is held. Locks are released in reverse order. Seeding
  (§2) takes only (2)/(3) of the `impl` checkout, shared, and no slot.
- **Adding a vendor lib** (O18; stage 04 "small Weil vendoring"): a new `[[lean_lib]]` in `lakefile.toml`, regenerated
  manifest only if requirements change, `tools/pins.sha256` updated **in the same commit** (stage master, never a WP),
  a target in the `lbuild.sh` allowlist, MANIFEST/LICENSE rows as in §3.2; checked in one TITAN round before any WP
  imports it. Vendor files never appear on `titan_batch.sh` spec lines (the script does not strip `Vendor/…` prefixes,
  §4.3 tool item "vendor path mapping"); a vendored lib is built through its own library target.
- `load_profiles.conf`: byte copy with the path change. **`prune_stale_build.sh`, `stale_build.py` are not copied**
  (not needed in stage 1; a prune tool next to `.lake/GL2TF` is an avoidable hazard; Fable C2).
- Never call `lake` directly. (*History:* revision 1 let opencode jobs call `lfile.sh`/`lbuild.sh`; opencode is not
  used as implementer any more, §5.1.) The only direct `lake` calls are inside the wrappers (and S01-X1a's sandboxed `--smoke` mode).

### 3.5 Smoke test `S01-X1a` (decides P / P′ / V) and lock change `S01-X1b` — DONE (stage 1)
*Outcome:* X1a all steps passed → P, seeding (a), 10 min wall (`runs/s01.md`); X1b merged with acceptance (a)–(c).
The text below is history.

**Timing.** X1a (and S01-X4 on TITAN, after it) run **before the stage-1 clock starts**, as the last step of P4/P5: they
need no other input, gate every Lean WP, and the §8 decisions are needed anyway. Stage 01 then starts at t = 0 with
L1, L3a (stage-01 §8/§9).

**S01-X1a (smoke).** WP: X, mechanical, model **opus** (cost is negligible against "a wrong conclusion costs the whole
stage"; Haiku stalled before on long shell work), agent wall ~40 min, build wall ~6–8 min, deps: none. Worktree
`…-wt/s01-x1a`, branch `impl/s01-x1a`. Wrapper copies with the **minimal diff only**: `lean="$repo"`, target
allowlist, the `path` exception in `link_deps.sh`, `GL2TF_IMPORT`, `DEP_ROOTS`, the pin guard (§3.4). Lock model = the
import's. No prune tools.
0. Pre-flight: `df -BG /mnt/c` ≥ 50 GB, `MemAvailable` ≥ 24 GB; no import `lbuild` running.
   `sha256sum` of the import's `lean/{lake-manifest.json,lakefile.toml,lean-toolchain}` → `<scratch>/pre-import.sha`;
   `marker=$(mktemp)`; `git -C /home/janosch/dev/Langlandscape status --porcelain lean/trace-formula-project-import`
   empty; `unshare -rmn true` succeeds (*verified* on this node, Fable A.9; `bwrap` absent).
1. Create the P skeleton (§3.3/3.4): `lakefile.toml` with **all** stage-01 libs declared (incl.
   `LanglandscapeVendorStacks` with its not-yet-existing `srcDir`, so that this is exercised), the manifest generated by
   `tools/make_manifest.py`, `tools/pins.sha256`, plus `Langlandscape/Smoke.lean`: `import AlgJL.VolIII.Brandt.Pairing`,
   `import AlgJL.Hyp.EichlerMass`, `import Mathlib.RingTheory.SimpleRing.Basic`, a trivial `theorem` mentioning
   `GL2TF.Quat.mass` and `GL2TF.Hyp.EichlerMass`, no sorry. (Stacks vendoring is S01-X3; S01-X2 is the per-WP tooling.)
   `sha256sum lake-manifest.json lakefile.toml lean-toolchain > <scratch>/pre.sha` (ours).
2. `tools/link_deps.sh && tools/link_deps.sh --verify` → `link_deps: OK (9 packages …)` (9 git entries; the path entry
   is checked separately); `.lake/GL2TF` resolves to the main checkout's import.
3. **Sandboxed first contact** (`tools/lbuild.sh --smoke`; pin guard first, inside the wrapper's systemd scope and
   locks, `unshare` innermost): the dry check and the first build run once in a namespace where the farm, the Mathlib
   tree and the import are read-only and there is no network:
   `unshare -rmn sh -c 'for d in /home/janosch/data /home/janosch/dev/Langlandscape/lean/trace-formula-project-import; do
   mount --bind "$d" "$d" && mount -o remount,ro,bind "$d"; done; exec lake build --no-build +Mathlib.Init
   +AlgJL.VolIII.Brandt.Pairing +AlgJL.Hyp.EichlerMass'`, then the same with `lake build +Langlandscape.Smoke`.
   Expected: "All targets up-to-date", then exactly one module built (`Langlandscape.Smoke`). Any attempted write or
   fetch fails with an error instead of damaging a frozen tree. (The one place where X1a calls `lake` directly.)
4. `tools/check_frozen.sh` (unsandboxed, as all later steps) → `check_frozen: All targets up-to-date over N dependency
   modules` (N includes the AlgJL imports). Log must not contain
   `fetching|materializing|cloning|remote URL changed|manifest out of date`.
5. `tools/lbuild.sh +Langlandscape.Smoke` → rc 0; the log builds no module other than `Langlandscape.Smoke` (normally
   none: step 3 built it); any line naming `AlgJL.` as built/building = FAIL.
6. `tools/lfile.sh Langlandscape/Smoke.lean` → `lfile: OK`. Post: `sha256sum -c pre.sha` and `sha256sum -c
   pre-import.sha` OK (Lake did not rewrite a manifest); `find <import lean dir> -newer $marker` and
   `tools/check_frozen.sh --sweep $marker` print nothing; import `git status` still empty; `.lake/packages/*` all
   symlinks.
7. Second worktree `…-wt/s01-x1a-2` off the same commit: `link_deps`, dry check (step 4), **and the seeding test (§2)**:
   `cp -a --reflink=auto` of the first worktree's `.lake/build` (its lock held shared), then `tools/lbuild.sh
   +Langlandscape.Smoke` must report the module as replayed, **zero modules compiled**. Repeat the post-checks of step 6.
**Decision**: all pass → **P** with seeding (a). Steps 3–4 fail only with AlgJL modules not up to date (in step 3: a
write error under the import's `.lake/build` only) → **P′** (§3.2), re-run 3–7. Only the seeding test of step 7 fails →
P with lanes (c) (§2). Any other failure (Lake error on the path entry, any fetch, any write attempt into the import or
the farm, manifest rewritten) → **V**: delete the path require/entry, regenerate the manifest, vendor the closure with a
script that walks `import` lines from the needed roots (generates MANIFEST rows per §3.2), `lbuild.sh
LanglandscapeVendorGL2TF` (TITAN candidate for the first build: ~7 min there vs ~25 locally), re-run 4–7. Exit 99 from
any wrapper = stop all agents and alert the global master. Record everything in `DECISION-PV.md`. Est. total: P ≈ 40
min wall; V ≈ +45 min.

**S01-X1b (lock model + `SLOTS` allowlist).** WP: X, routine, model sonnet, agent ~30 min, build ~5 min, deps X1a;
approved §8 F2. Implements the X1b lock model and the acquisition order of §3.4 in `lbuild.sh`/`lfile.sh`, and the
`SLOTS ≤ 3` local-conf allowlist in `deps_load.sh`. Acceptance: (a) two worktrees run `tools/lbuild.sh
+Langlandscape.Smoke` concurrently and both finish; (b) **deadlock test** (C3): in one checkout start one `lbuild` and
two `lfile`s while the second node slot is held by a dummy `flock`; all three finish; (c) an import `lbuild` (simulated
by holding `lean.lock` exclusively with `flock`) blocks both of (a); `shellcheck` clean; X1a steps 4–6 still pass.
**The stage does not wait for X1b**: until it is merged, the stage runs with the exclusive lock and batched merge gates
(stage-01 R4). `SLOTS=3` on TITAN (S01-X4) takes effect only after X1b; before that TITAN runs with `SLOTS=2`.

### 3.6 Hypotheses and sorries
- Convention mirrors the import's `AlgJL/Hyp/EichlerMass.lean`: one file `Langlandscape/Hyp/<Name>.lean`, `namespace
  Langlandscape.Hyp`, `def <Name> (params) : Prop := …` with a docstring giving: stage-tex label (e.g.
  `hyp:s02-sa` / the `Hyp.SA` name used in the plan), precise literature source, discharge plan, owner WP. Plan names
  map as `Hyp.SA` → `Langlandscape.Hyp.SA`, `Hyp.X.char` → `Langlandscape.Hyp.X.char`. Existing import hypotheses are
  reused, not redefined (`GL2TF.Hyp.EichlerMass`).
- Use: theorems take the hypothesis as an explicit argument `(hSA : Hyp.SA B U)`; never `axiom`, never a global
  instance, never inside a structure field that hides it. Every hypothesis gets a non-vacuity example or a proved
  instance in `LanglandscapeTests/Hyp/` where feasible, or a sentence why not.
- `HYPOTHESES.md` columns: Lean name | file | statement label (stage tex / mathematics) | source | used by (decls) |
  instances | discharge plan | status (open / partially discharged / proved).
- `sorry` is allowed only on `impl/*` branches for declared stubs; on `wip-implementation` every sorry is listed in
  `SORRIES.md`; on `main` none in `Langlandscape/` (tests/examples only if listed, like the import's two).
- Docstring rule (exact, O8; §9 lesson 3): **every `theorem`/`lemma`, including `private` ones and those in
  `LanglandscapeTests/`**, has an immediately preceding `/-- … -/` containing a label `s<NN>-…` (any stage; stage-tex
  label until the chapter exists, then the `mathematics/` label); `check_wp.sh` enforces this in the integration round.
  Public `def`/`structure` need a docstring too, but this is **not** machine-checked: it is reviewed in the WP audit.


## 4. Resources, TITAN, wall time

### 4.1 Resource checks
- **Before every spawn/build** (`resources.md`): `df -BG /mnt/c` (< 50 GB warn, < 20 GB stop), `free -g` (keep ≥ 12 GB
  available; budget 2 GB/Claude agent, 8 GB/Lean process). Localhost at the end of stage 1: /mnt/c 174 GB, RAM ok
  (*measured*, master log); local CPU/GPU is reserved for HACS (§8 F16).
- **Parallelism** (`orchestration.md`, Fabian 2026-11-14): ≤ 8 concurrent Claude subagents per delegating agent,
  resource-permitting; Fable may run in parallel with other agents, including another Fable (supersedes revision-1 F4,
  §8). Stage 1 ran the M track and the C/T track under one Opus sub-coordinator each (F3); stages 02–06 keep that
  pattern: stage master = X/L track + merges; M sub-coordinator; C/T sub-coordinator. Only the stage master merges.

### 4.2 Local Lean (history) and build mechanics
- **No local Lean in stages 02–06** (§8 F10; `resources.md` TEMPORARY): no `lbuild.sh`, `lfile.sh` or building
  `check_wp.sh` on localhost. Workers write Lean without compiling; every check is a TITAN job (§4.3). If Fabian lifts
  the directive, the revision-1 rules apply again: `SLOTS=2`, 8G/6G caps, X1b lock model, seeding per §2.
- `lbuild.sh +A +B +C` = one Lake process for several modules (lake keeps going past failing modules); `lfile.sh F` =
  `lake env lean F` (builds nothing; all project imports of F must be built). `titan_batch.sh` combines both (§4.3).
- Build times on TITAN (*measured*): import full build 6:43; stage-1 library from scratch 82 s (3838–3842 jobs) seeded
  from the import; an integration round's `titan_batch.sh` build 17 s (int3, seeded), i.e. the round trip is
  dominated by coordination (push, relay, report), not by Lean.

### 4.3 TITAN
TITAN = Lean build node (16 threads, 94 GB, **≤ 3 concurrent builds**), clone `/home/claude/dev/Langlandscape`, frozen
Mathlib at `/home/claude/data/gl2tf-data/mathlib4_v4350`, `SLOTS=3` in its git-ignored `tools/deps.local.conf`. It
takes jobs **only from the global master**, and pushes **only** `titan/<job-id>`.

**Flow (file outbox; §8 F11).**
1. Stage master merges the current drafts/fixes into `impl/sNN-int<k>` (§2) and adds, as a **separate top commit that
   contains only `lean/Langlandscape/.titan/`**, the spec file `.titan/spec-<job>.txt` and the axiom scratch files
   `.titan/sNN_<wp>_axioms.lean` (one per WP; commit message `lean: TITAN spec <job> (scratch)`). **One rule for every
   job kind (O4):** a TITAN job always runs a throwaway `.titan/`-only commit on top of the tree under test: the
   integration tree (pushed as `impl/sNN-int<k>`), a single-WP head, or a strand head (both pushed as
   `titan-in/<job-id>`). The stage master merges the commit's *parent* (`~1`), never the commit itself. It then writes the job spec `plan/implementation/outbox/<UTC>_titan-sNN-<job>-<n>.md`
   (UTC = `YYYYMMDDTHHMMSSZ`) and commits it on `wip-implementation`. It notifies the global master by SendMessage
   ("outbox: <file>") — **the notification is never the job spec** (§9 lesson 5).
2. Global master pushes `impl/sNN-int<k>` (and `wip-implementation` for the outbox file); for strands and single-WP jobs
   it pushes the ref `titan-in/<job-id>` (`git push origin <sha>:refs/heads/titan-in/<job-id>`; neutral, no model names for
   strands); relays the outbox file to TITAN.
3. TITAN runs the command in a checkout of the given sha **seeded from its previous round's `.lake/build`** (reflink
   copy; finals unseeded), commits `.titan/out/*` on `titan/<job-id>`, pushes, replies with the report.
4. Global master fetches, deletes the `titan-in/<job-id>` ref, logs the result in `agents/status/master_log.md` and
   relays the report: to the stage master in full; **to experiment strands verbatim, errors only, no fix hints, no
   model names** (§5.2).
5. Stage master dispatches fixes, merges green WP branches into `wip-implementation` (only together with or after all
   upstream WPs, §2), and opens the next round.

**Job ids, rounds, priorities.**
- **Grammar (O16).** Job id `sNN-<job>-<n>`, n = attempt (1, 2, …), result branch `titan/<job-id>`, outbox file
  `…_titan-<job-id>.md`. `<job>` ∈ {`int<k>` first run of integration round k; `int<k>a`, `int<k>b`, … re-runs of the
  same round after fixes; `gate<m>` early/intermediate full gate (`s02-gate1-1`); `final` from-scratch gate
  (`s02-final-1`); `<wp>` single ext/fix WP (e.g. `l16b`); `<wp>-<a|b>` experiment strand}. (Stage 1 wrote `int1, int2a,
  int3`; from stage 02 the first run of round k is always `int<k>`.)
- **Integration rounds**: `int1` = first build of the first draft wave; a **new number** when a new set of WPs enters
  (next wave, audit-fix WPs); a **letter** = re-run of the same round after fixes. Stage 1: `int1` (13 drafts) →
  `int2a`…`int2f` (fixes + remaining drafts) → `int3` (audit fix L16a): 8 TITAN runs, int1 → int2f = 7 runs in ≈ 26 min.
  **One integration build per round**; a newer letter supersedes an unstarted older one ("supersedes …" in the spec).
  Do not hold a round for a slow WP: it joins the next letter. **Spec contents:** all WPs of the round that are not yet
  green, plus fix WPs (stage 1: int2f listed only L17, L4c); merged green WPs are covered by step 2 of the job (below).
  Expect 5–9 TITAN runs per stage (letters count), one run ≈ 1–6 min relay→report, ≈ 4 min all-in per run (*measured*).
- **Priorities (O7).** Priority 1 = the integration round on the critical path and the gates; 2 = experiment strands
  and ext WPs; 3 = everything else. TITAN runs ≤ 3 builds, so: **both strands of a pair go in one outbox file** as two
  jobs that start together or wait together (equal latency; log each strand job's TITAN start time in
  `experiments/events.tsv`). While a strand pair is waiting for its round, **no gate is dispatched** and ext/single-WP
  jobs drop to priority 3; round + pair = 3 slots, nothing else runs concurrently.
- **Parallel stages and the S06 early lane (merge order).** A Mathlib-only early lane of a later stage (S06 CommAlg, started
  by stage 03) runs at priority 3 on `impl/s06-int<k>` off a clean `impl/s06-early` and never pre-empts the active stage. The
  **global master** merges `impl/s06-early` into `wip-implementation` at a stage boundary (after stage k's merge to `main`,
  before stage k+1's X1; at the latest before S05-X1) once its gate `s06-gate1-1` and Fable audit (S06-L18) pass; the
  aggregator lines go into that merge commit, the next stage's `int1` is its merge gate, and an outbox hand-over file
  announces it. For parallel stages (05 ∥ 06) the global master orders TITAN jobs: priority 1 (integration rounds, gates)
  before priority 2/3, ties by critical path; **merge order into `wip-implementation` = order of green gates**; the later
  stage rebases onto the other's merge before its next round; shared files (`Audit/PrintAxioms.lean`, `HYPOTHESES.md`,
  `SORRIES.md`, root import files, `main.tex`, `references.bib`) are edited by stage masters only, as aggregator lines.

**Spec-file format of `tools/titan_batch.sh`** (*verified*, script @ 3234aef; run from `lean/Langlandscape/`):
```
<WP-id> <file.lean> [<file.lean> ...]
AXIOMS <.titan/sNN_<wp>_axioms.lean>
```
Rules (O1, O15, O18): whitespace-separated tokens; **no trailing comments** (the script skips only lines whose *first*
token starts with `#`; on any other line every token after the WP id is taken as a file, so `# …` yields modules `+#`,
`+…` and a non-`.lean` argument that makes `check_wp.sh` exit 1); blank lines and whole-line `#` comments are allowed;
paths relative to `lean/Langlandscape/`; one line per WP; the WP-id is a free token (`L3`, `L5bc`, `L16a`); **no
`Vendor/…` paths**; one `AXIOMS` line **per WP** (one file `.titan/sNN_<wp>_axioms.lean` each; the file's imports must all
be built by the round, i.e. on spec lines, because `lfile.sh` builds nothing). Meaning: the WP line = "library + test
files of one WP"; the `AXIOMS` line = axiom scratch file, `lfile`'d after the build.
The script (1) runs **one** `tools/lbuild.sh` over the modules of all WP lines (file path → module, `/` → `.`);
(2) runs `tools/check_wp.sh <files>` per WP line (build is then a no-op; adds the `declaration uses 'sorry'`,
forbidden-token and docstring checks); (3) runs `tools/lfile.sh` per `AXIOMS` file. Output: `.titan/out/summary.txt`,
`build.log`, `checkwp-<WP>.log`, `axioms-<name>.log`; exit 99 (pin guard) stops everything. `summary.txt` lines:
`BUILD rc=<r> wall=<s>s`; `## errors per file` (count + file); `## modules built / failed` (lines `Built|Building|Replayed
<module>`; a `Building` without a later `Built` is the failure signal, O17); `CHECK_WP <WP> rc=<r> <k> FAIL lines` (the
count includes the line `check_wp: FAILED`; only `k = 0` is meaningful); `AXIOMS <file> rc=<r> nonstandard=<k>`.
A WP is green iff `CHECK_WP … rc=0 0 FAIL lines` **and** its `AXIOMS` line has `rc=0` and every printed line is ⊆
`{propext, Classical.choice, Quot.sound}` (judged by the **patched** counter, or by the stage master reading
`axioms-*.log` while the patch is unverified; strict subsets such as `[propext, Quot.sound]` of a Hyp-def WP are fine).
**Known defects of the current counter (*verified* on `titan/s01-final-1:.titan/out/c-axioms.log`; O2):**
(a) **false negative**: Lean prints a primed name as `'Langlandscape.Brandt.Tl_adjoint'' depends on axioms: …`; the
pattern `'[^']+' depends on axioms` never matches it, so a primed line is not counted at all, even with `sorryAx`
(stage 1 has four primed headline declarations); (b) **false positive**: wrapped output `[propext,⏎ Classical.choice,⏎
Quot.sound]` becomes `[propext,  Classical.choice,  Quot.sound]` (double spaces) after `tr '\n' ' '`, so a standard
line counts as non-standard (3 such lines in the real log). So `nonstandard=0` is **not** reliable in either direction
until the tool fix lands: **S02-X1 tool fix: `titan_batch.sh` axiom counter** (new `tools/axcount.sh`, called by
`titan_batch.sh`; committed by S02-X1 step 1 on `wip-implementation` before any S02 branch exists, verified live in `int1`;
it also counts `does not depend on any axioms` lines, printed by Prop-valued `Hyp` defs, as printed): normalise whitespace (`tr -s '[:space:]' ' '`), match `depends on axioms: \[[^]]*\]` without the
name, count a line as non-standard iff its axiom set is not ⊆ the standard three, and print `printed=<k>
expected=<number of #print axioms lines in the file>` (a silently missing line, as in the stage-1 L14 failure, then shows).
Until `int1` verifies the patch, the stage master reads every `axioms-*.log` by hand. Axiom scratch file:
```
import Langlandscape.<Area>.<File>
#print axioms Langlandscape.<Area>.<decl>
```
(one `import` per module that declares a listed name; fully qualified names, one `#print` per declared output.)
Example (stage-1 `impl/s01-int3`, `.titan/spec-int3.txt`; there the axioms file was `s01_l16a_axioms.lean`):
```
L16a Langlandscape/Quat/LevelFinite.lean Langlandscape/Brandt/HeckeFinite.lean Langlandscape/Quat/MassTower.lean LanglandscapeTests/S01/HeckeFinite.lean LanglandscapeTests/S01/Up.lean
AXIOMS .titan/s01_l16a_axioms.lean
```

**Job-spec template (integration round)** — derived from `outbox/*titan-s01-int2*.md`; every field is mandatory:
````markdown
# TITAN job sNN-int<k><x>-<n> (priority 1 — critical path)

- Job id: `sNN-int<k><x>-<n>`; result branch: `titan/sNN-int<k><x>-<n>`; supersedes: `sNN-int<k><x-1>-<n>` if not started (or —).
- Branch to push: `impl/sNN-int<k><x>` at **<full 40-hex sha>** (top commit = `.titan/` only) (= wip-implementation <short sha> + drafts <WP list>;
  fixes since the last round: <WP list>).
- On TITAN: checkout of that sha, `.lake/build` seeded by reflink copy from the `<previous job-id>` build; from
  `lean/Langlandscape/`, **two steps (O3)**:
  (1) `bash tools/titan_batch.sh .titan/spec-int<k><x>.txt` (spec = WPs of the round not yet green + fix WPs);
  (2) `tools/lbuild.sh Langlandscape LanglandscapeTests` (seeded, ≈ 12 s in stage 1: `FULL lbuild … rc=0`), so that a fix
  to an upstream file cannot silently break merged, unlisted modules. Report rc, error lines and the `declaration uses
  'sorry'` count of step 2.
- Report (message + `.titan/out/*` committed on `titan/sNN-int<k><x>-<n>` and pushed):
  1. `.titan/out/summary.txt` in full;
  2. per failing WP: its `error:` lines from `.titan/out/build.log` (≤ 200 per WP), with the goal state of every
     "unsolved goals" error (≤ 30 lines each);
  3. the `FAIL` lines of `.titan/out/checkwp-<WP>.log`;
  4. every `#print axioms` line in `.titan/out/axioms-*.log` that is not exactly `[propext, Classical.choice, Quot.sound]`,
     and every error line of those logs.
- Any rc 99: stop and report.
````
Variants (same header fields):
- **Strand** (`sNN-<wp>-<a|b>-<n>`, priority 2; a pair goes in **one** outbox file, §4.3 priorities): "push `<full
  sha>:refs/heads/titan-in/sNN-<wp>-<a|b>-<n>`" where `<full sha>` is the `.titan/`-only throwaway commit on top of the
  strand head; "delete the ref after the fetch"; run after the integration round it depends on, seeded from that round's
  build; command `bash tools/titan_batch.sh .titan/spec-<wp>.txt` then step (2) above; report: summary + errors/goal
  states only, **no model names**. The throwaway commit is never merged, so the §2 `.titan/` grep also holds for a merged strand.
- **Single-WP job** (`sNN-<wp>-<n>`): same as a strand, ref `titan-in/<job-id>`, parent = the WP head.
- **Early full gate** (`sNN-gate<m>-<n>`) and **final gate** (`sNN-final-<n>`, fresh **unseeded** checkout, import oleans via
  `.lake/GL2TF`), on `wip-implementation` at a full sha, no `.titan/` content: (a) `tools/lbuild.sh Langlandscape
  LanglandscapeTests` (b) `tools/lbuild.sh LanglandscapeVendorStacks` (c) `tools/lfile.sh Audit/PrintAxioms.lean`
  (join wrapped lines with whitespace normalisation; **the gate spec states `expected = <number of #print axioms lines
  in Audit/PrintAxioms.lean>` and TITAN reports printed vs expected** (O22), non-standard = axiom set ⊄ standard,
  primed names included) (d) `grep -rnE '\bsorry\b|\badmit\b|^axiom|native_decide|implemented_by'
  Langlandscape LanglandscapeTests` → empty (e) `declaration uses 'sorry'` count in the log of (a) (only the import's
  replayed `AlgJL/VolIII/P2/Instances.lean:1815` allowed) (f) `tools/check_frozen.sh` clean. Report rc + wall per step,
  printed/expected axiom-line counts, #non-standard, warning count in `Langlandscape/`, all error lines; logs on `titan/<job-id>`.

**What TITAN reports** (in the reply and on `titan/<job-id>`): the items of the job spec; for batches `summary.txt` in
full, error lines per failing WP (≤ 200) with goal states, `check_wp` FAIL lines, non-standard/erroring axiom lines; for
gates rc + wall per step, axiom-line count and non-standard count, sorry count, warnings count, `check_frozen` result.
TITAN never edits sources and never reports suggestions.

**`.titan/` is never committed on WP branches** (stage-1 audit finding A0.1). Spec and axiom scratch files exist only
in a throwaway top commit that contains nothing else (on `impl/sNN-int<k>`, or behind a `titan-in/<job-id>` ref for strands and
single-WP jobs, see the flow above); `wip-implementation` and `main` contain no `lean/Langlandscape/.titan/` (checked at
every merge gate, §2). Workers deliver their spec line and their axiom-file contents in the WP report; **the stage
master writes the files** (the haiku axiom-list WP returns the list in its report and writes no files, §9 lesson 2).

**Tooling items** (*verified* gaps in `lean/Langlandscape/tools/`; the plan edits no tool; **S02-X1 step 1 commits all of
them on `wip-implementation` before any S02 branch is created** (stage-02 A1) and `int1` verifies them live; **later stages
never edit tools**: their X1 only greps for the fix and reports to the global master if it is missing):
- **S02-X1 tool fix: axiom counter** in `titan_batch.sh` (primed names, whitespace normalisation, ⊆ standard,
  printed/expected; text above; O2, O15, O22).
- **S02-X1 tool fix: docstring pattern** in `check_wp.sh`: accept `s[0-9][0-9]-` instead of `s01-`, so a stage-03
  lemma may cite `lem:s02-…`; X1 also decides whether `LanglandscapeTests/**` is exempt (default: **not exempt**, as the
  rule of §3.6 says). The check covers `theorem`/`lemma` only (O8).
- **S02-X1 tool fix: vendor path mapping** in `titan_batch.sh`: strip `Vendor/AxiomStacks/` as `check_wp.sh` does
  (l. 25–27), so that a vendor file on a spec line gives the right module (O18; low priority until stage 04).
- **Global-master rule edit:** `agents/rules/lean.md` l. 22 "main theorem docstring references `mathematics/`" →
  the exact rule of §3.6 (O8); see also F18 (§8).

### 4.4 Wall calibration
Stage 1 took **2.2 h against an 8.8 h plan** (factor ≈ 0.25; t = 0 15:32Z → done ≈ 17:46Z, `runs/s01.md`). Use these
values (*measured* from `runs/s01.md` and `agents/status/master_log.md`, n = 1 stage, unless marked) instead of the
revision-1 estimates:

| Item | Wall (min) |
|---|---|
| local short WP (X/C/M/T, no Lean) | 2–17 |
| Lean WP under TITAN (wall; dominated by integration rounds) | 33–80 |
| … of which agent-active (draft + fixes) | 10–20 (*estimate*: stage-master estimates in SUMMARY, not in `runs/s01.md`) |
| TITAN run, relay → report | 1–6 (stage 1: int1 2, int2a 6, int2b 5, int2c 3, int2d 3, int2e 2, int2f 1, int3 1) |
| TITAN run, all-in incl. fix dispatch and next push | ≈ 4 (int2c → 2d → 2e → 2f every ≈ 4 min); int1 → int2f = 7 runs in ≈ 26 min |
| M track, 10 WPs incl. Fable chapter audit + resolution | 52 |
| C/T track, 11 WPs | 28 |
| Fable Lean audit | ~6 |
| audit fix WP (incl. its TITAN round) | 2–13 |
| final from-scratch gate | ≈ 3–5 |

**Method** (every stage plan; O10): Lean track wall ≈ kickoff X1 (10–15) + first draft wave (10–20 agent-active,
parallel) + **R × 4–8 min**, where **R = the number of TITAN runs** (letters count; expect 5–9) and 4–8 min is the
all-in cost of a run, which already contains the fix; add fix time (+5–10 min) only for a `hard` fix that is itself on
the critical path. Tail: early gate ~5, Fable Lean audit ∥ chapter audit ~6–10, audit fix WPs + their round 10–20,
final gate ~5, closure ~5. Do not add "round trip + fix" per round (double count). Give the **critical path as summed
wall** along the DAG and a **stage wall estimate with a ± range** (typically ±30 %); the stage wall is the maximum of
the track walls (Lean usually), not their sum. Cross-check: revision-1 estimate × 0.25–0.35 (**n = 1**, the measured
factor was 0.25); deviation > 50 % must be explained. Stages 02–06 contain less reuse than stage 1 (import Vol III) and
more `hard` WPs, so take the upper half of each range for `hard`/`conceptual` WPs.

## 5. Model selection

### 5.1 Assignment (binding; from `experiments/SUMMARY.md` §3 priors)
| Class | Model | Fix round |
|---|---|---|
| mechanical copy / vendoring (Lean or other) | haiku | ladder haiku → sonnet |
| Lean mechanical-with-meaning (new Props/defs against existing API, incl. stacked on unverified drafts), Lean routine | sonnet | one budgeted opus fix round (~2–5 min) |
| code routine (pytest loop, PARI), LaTeX routine | sonnet | one budgeted opus fix round (~2 min; expect 6–8 minors at r0) |
| Lean hard, LaTeX hard (full proofs) | opus | one planned opus fix round |
| conceptual (design, interfaces, normalisations, audits of concept) | opus or fable | — |
| audits | Lean audit `agents/roles/lean_audit.md` and chapter audit `agents/roles/mathematics_chapter_audit.md` = **fable**, run in parallel; WP-level audits = opus (alternate with fable for adversarial audits) | — |

- **muse and mistral are dropped as implementers** (E2/E4: muse failed r0; E3: mistral passed only after two
  escalations, 46 vs 11 min; E1: muse cancelled, no local Lean loop). No opencode WPs are planned.
- **Every WP row names model + fix-round budget.** A fix round that does not reach green escalates one rung (haiku →
  sonnet → opus); an opus WP still failing after its planned fix round goes to the stage master (split, re-scope or
  fable), recorded in `runs/sNN.md`.
- Cheapest model that does not lengthen the stage's wall time: on the critical path a failed cheap attempt plus TITAN
  round trips costs more wall than one strong attempt (E1: opus 1 round vs sonnet 4 rounds), so critical-path `hard`
  Lean goes to opus. Haiku never for M-track proofs or for Lean beyond copy/vendoring; a haiku WP that produces `.lean` text
  (the axiom-list WP) **returns it in its report** and the stage master writes the files (E5: haiku major signature
  deviation). The F17 hygiene WP (edits Lean, ≈ 80 warnings) is **sonnet (+1 opus fix)**.
- **HACS** (`code/hacs/`, when filled; F16): sonnet routine, opus for the JL-transfer interface (conceptual).
- All verdicts are **priors** (one comparison each, SUMMARY §2); stage-02–06 `runs/sNN.md` data revise them
  (EXPERIMENT_PROTOCOL §8–§9). The global master approves changes; each stage file logs "model per OVERVIEW §5.1".

### 5.2 Experiment strands
Only for cells SUMMARY leaves undecided or confounded; **at most 1–2 strands per stage**. Allocation (binding):
| Stage | Strand | Cell | Pair | WP choice |
|---|---|---|---|---|
| S02 | **E1** | Lean hard (confounded in S01) | opus vs sonnet, both under the same batched-TITAN regime | one hard S02 L WP |
| S02 | **E4** | LaTeX routine (undecided) | sonnet + budgeted opus fix vs opus single-shot | one routine S02 M WP |
| S03 | **E8** | LaTeX hard (undecided, all-fail) | opus + planned opus fix round vs fable single-shot | one hard S03 M WP |
| S04 | E1′ (conditional) | Lean hard | opus vs sonnet, as E1 | S04-L6, only if E1 leaves the cell undecided |
| S05 | E8′ (conditional) | LaTeX hard | as E8 | S05-M3, only if E8 leaves the cell undecided |
| S06 | E1′ (conditional) | Lean hard (Mathlib-only) | as E1 | S06-L5b, only if E1 **and** S04's E1′ leave the cell undecided |

Conditional strands run only after the global master approves per EXPERIMENT_PROTOCOL §9. **One E1′ per project:** S04's
runs first; S06's (on L5b, a leaf) runs only if S04's was not triggered or left the cell undecided. **E8/E8′ override
protocol §2.4:** the opus reference gets exactly one planned opus fix round regardless of W0, then a delta audit (`failed`
if r1 fails); the fable challenger has no fix round. E1 (S02) has a deadline D (stage-02 §5; event `stop reason=deadline`).

Rules:
- Equal regime: each strand of a pair gets **one TITAN slot per integration round** (§4.3); the two jobs of a pair are
  in **one outbox file** and start together or wait together, and no gate is dispatched meanwhile (§4.3 priorities, O7),
  so latency is equal; record
  **agent-active minutes separately from TITAN wait** (events in `experiments/events.tsv`; rows in `LOG.md`).
- Strand WPs **always run on Fabian's node** (never remote-eligible, §6.1), so measurements are comparable; as for all
  WPs their Lean checks go to TITAN (no local Lean, §4.2).
- Neutral naming on everything TITAN or an auditor sees: job id `sNN-<wp>-<a|b>-<n>`, ref `titan-in/<job-id>` (deleted
  after fetch), no model names in specs, reports or commit messages of strand branches; `exp/sNN-<wp>-<model>` stays
  local.
- **No fix hints in relays**: stage master and global master relay TITAN results to strands verbatim (errors only).
- Auditor model ≠ strand models where possible (S01 confound: opus audited opus): E1, E4 → fable WP audit; E8 → opus
  audit, confound noted in LOG.md. Decision rule, merge of at most one strand, logging: EXPERIMENT_PROTOCOL §2–§6, §9.
- Rebase both strands at the same time when an upstream fix lands, onto the **fixed upstream WP head(s)** or, if the
  integration tree is the base, onto `impl/sNN-int<k>~1` (never onto its `.titan/` commit; §9 lesson 4).

### 5.3 Verification and audits
- WP-level audit (opus; fable for adversarial or strand audits) before merge for every `hard`/`conceptual` WP and for
  strands; mechanical/routine WPs: acceptance check only, plus the stage master's read of the report.
- Milestone audits: Fable Lean audit (`lean_audit.md`) on the TITAN-verified early-gate commit **in parallel with** the
  Fable chapter audit (`mathematics_chapter_audit.md`); required remarks become audit-fix WPs in the same stage (stage 1:
  L16a/b/c), hygiene remarks may be carried over (stated in the closure).

## 6. Track decoupling, merge points, milestones
- Tracks M (maths), L (Lean), C/H (code, HACS), T (talk) run independently. **The only coupling is the interface**: a
  Lean WP needs the statement (stage tex now, `mathematics/` later) to exist; a T WP needs the claim to be traceable to
  `mathematics/`, `lean/` or `code/results/` (talk rule). Maths may run ahead; no milestone waits for another track.
- A stage's WPs may start as soon as their own inputs exist: cross-stage inputs that are not merged yet are stubbed as
  registered hypotheses (§3.6) or as `sorry`-stubs listed in `SORRIES.md` (never on `main`); within a stage, Lean WPs
  stack on unverified drafts (§4.3).
- **Merge points**: per WP (stage master → `wip-implementation`, after the gate in §2); per stage (global master →
  `main`, after review). Per-track "stage NN done": M = chapter compiles + chapter audit passed; L = all stage targets
  build in the final from-scratch gate, SORRIES/HYPOTHESES up to date, `lean_audit` PASS; C/H = tests pass and results
  recorded with script, commit, parameters, runtime (`code.md`); T = slides compile, every claim traceable. A stage may
  merge to `main` with some tracks done and others continuing in stage NN+1 (stated in the closure).
- **Milestone closure**: `plan/implementation/outbox/<UTC>_milestone-closure-sNN.md` (format of the s01 closure:
  delivered / verification / open issues / request), committed by the stage master.
- **Milestone PDFs**: at each stage merge `mathematics/main.pdf` (and talk PDFs) are committed next to their sources;
  only the global master mirrors them (`rclone copy … gdrive:dev/Langlandscape/<dir>/`).
- Stage reports: `plan/implementation/runs/sNN.md` (stage master): WP outcomes, wall/agent-active/TITAN-wait times,
  rounds, deviations, strand metrics.

### 6.1 Remote-eligible WPs (node "Abhijit")
- **Node** (`agents/status/abhijit_candidates.md`): Abhijit's notebook, **16 GB RAM, no Lean** (no frozen Mathlib; Q1
  open), own Claude session, git channel `agents/messages/` (`messages.md`); literature must be copied out of band
  (git-ignored). **Prerequisites (O12):** TeX Live with `latexmk`, `biblatex` and `biber` (`mathematics/preamble.tex`
  l. 12 uses `backend=biber`); a node-specific resource budget for 16 GB (≈ ≤ 4 concurrent agents, ≥ 3 GB free, `latexmk`
  ≈ 0.5 GB), because `agents/rules/resources.md` (≥ 12 GB free, 2 GB per agent) would allow ≤ 1 agent there.
  **Global-master rule edit:** add this node row and budget to `resources.md` (F18). The "5–8 Opus" of the candidates
  file is *not* assumed.
  *Update (global master 2026-11-14, Abhijit batch 1):* node facts: 15 GB RAM, ≈ 4 GB free, built Mathlib at the pin present, 3–4 Opus agents, one heavy job (`latexmk` or `lean`) at a time; `resources.md` row updated.
- **Precondition for assigning any WP remotely (O12c):** Q5 (transport: who pushes `abhijit/*`, since §2 lets only the
  global master push) approved **and** Q2 (literature access) settled for that WP's sources. **Until then every WP is
  local**; this is the default state at stage-02 launch. *Update (global master 2026-11-14, Abhijit batch 1):* O12c preconditions are met (Q5 approved 20:32, Q2 out of band 18:50, Q-C settled 2026-11-14); the early lane is open for the WPs the global master assigns.
  **New eligible class: Mathlib-only Lean WPs** (GL2TF-free files; no `Hyp`/aggregator edits): the node may run a local direct-`lean` *draft* check (exception in `lean.md`/`frozen.md`, one Lean check at a time); acceptance only in our TITAN round. Stacked remote branches `abhijit/<wp>` off another `abhijit/<wp>` head are allowed.
- **Tag `remote-eligible`** (O14) on M (maths chapter), literature and second-reader/review WPs of stages 02–06 **that
  satisfy all conditions below** — **except** experiment-strand WPs (§5.2), Fable chapter audits, **audit-fix WPs**
  (they edit existing files) and M WPs whose inputs include code results not yet merged (e.g. "sketch until S02-C4").
- **Conditions**: self-contained; inputs only the stage tex + merged `mathematics/` + `literature/`; **new files only**.
- **Package structure (O13).** The per-stage files (`mathematics/standalone-sNN.tex`, `mathematics/bib/sNN.bib`,
  `mathematics/chapters/sNN/NOTES.md`, and the chapter driver `mathematics/chapters/sNN.tex`, as `\input{chapters/s01}`
  is used for s01) would be created by every M WP of the stage, i.e. several writers (add/add conflicts, breach of "one
  writer per file"). Therefore a stage's remote M WPs form **one package branch `abhijit/sNN-math`** (off
  `origin/wip-implementation` at the sha in the request) with **one writer** for the per-stage files; the WPs' own files
  are `mathematics/chapters/sNN/<wp-id-lowercase>.tex` and `mathematics/litnotes/*`. **Allowed variant (stages 02, 03, 05,
  06):** per-WP bib files `mathematics/bib/sNN-<wp>.bib` (new file, one writer), loaded by explicit name with
  `\IfFileExists{…}{\addbibresource{…}}{}`, de-duplicated and merged into `references.bib` by the stage's M closure WP
  (stage 04 keeps the single `bib/sNN.bib` written by X1, entries returned as aggregator lines). (Single-WP assignment, e.g. one
  literature WP: branch `abhijit/<wp-id-lowercase>`, files `mathematics/litnotes/*` only.) **Aggregator lines**
  (`mathematics/main.tex` `\input`, `references.bib`) are returned in the report and applied by the stage master. The X1
  kickoff creates **no maths stubs for WPs assigned remote**.
- **Standalone driver** (as in `abhijit_candidates.md` §4): `\input{preamble}`; `\addbibresource{bib/sNN.bib}`;
  `\input{chapters/s01}` (for the `if:s01-*` labels of stage 1); `\providecommand` for macros, listed in NOTES.md.
  Undefined refs/cites are tolerated **only** for labels of the listed sibling WPs of the same package.
- **Acceptance**: `latexmk -pdf standalone-sNN.tex` exit 0, no undefined refs/cites (except the sibling-WP rule); labels
  exactly as in the stage tex; then the stage master re-runs it on the merged tree, and the Fable chapter audit runs locally.
- **Every stage launches without Abhijit**: the default executor is local; the global master decides per WP at stage
  launch (request message with WP id, base sha, files, acceptance). Each stage plan has a table "Remote-eligible WPs"
  (WP id | branch | files | local fallback model) and the sentence "the stage is launchable without Abhijit". A remote
  WP not delivered when its first consumer is ready is re-run locally (fallback model from the table).

## 7. Stage overview (final after the re-plan; sizes calibrated after stage 1, §4.4)
| Stage | Maths (M) | Lean (L) | Code/HACS (C/H) | Talk (T) | WPs | Critical path | Wall (*estimate*) |
|---|---|---|---|---|---|---|---|
| 01 quaternion-foundations | **DONE**: chapter s01, 31 labels, 29 pp, Fable audit PASS w/ remarks | **DONE**: P regime (a), X1b, X2, X3; 22 core + 4 ext WPs + L16a/b/c; final gate from scratch PASS (161 axiom lines standard, 0 sorry) | **DONE**: C0–C7, pytest 231 pass, R1 closed | **DONE**: T0–T2 | ~56 | — | **2.2 h measured** (plan 8.8 h) |
| 02 tree-quotients | T_q, Γ_U, SA (cited), `prop:s02-BG`, (co)homology, D1 | SA-free core: coset tree (`EdgeO`), `Γ_U`, `BG`, quotient bijections, Hecke commutation, bipartite `H_1`, two-term complex (trivial coeff.); `Hyp.SA/HS/BTtree/SerreCoh/SerreFree` | tree builder, validation, T2/T3, torsion, `H_*(Γ_U,V_k)` | 2 slides | 36 (X 4, L 17, M 8, C 5, T 2) | 144 min (X1→L4a→L4b→L5b→L6→gate1→L12→L13a→final) | 2.5 h (1.8–3.2) |
| 03 ribet-ihara | weighted graphs, Φ^comb, Mazur, Ribet, Ihara, amalgam (`Ψ*Ψ` fixed) | graph layer, Lemma bip/Ribet/Ihara (i),(ii) over any `R`, coefficient layer `alphaV` (L14), `Hyp.IharaH0` | T1, T2, T6, Betti det | 3 slides | 34 (X 2, M 9, L 14, C 5, H 1, T 3) | 171 min (X1→L1→L3→L4/L6→gate1→L12→L13→final) | 2.85 h (2.2–3.6) |
| 04 lambda-adic | ekills, control, Λ-adic Ribet, Hsieh (cited), η-principle (maths) | projector `e`, ekills, Hida, control (finite), `Mord`/`Lam`; `Hyp.PadicOrdDecomp`, `HidaControl`, `HsiehCR`, `MordLambdaFree` (`HsiehGor` registered by S06; no Weil vendoring) | T3, H6, C2, H7 | 2 slides | 43 (X 4, M 10, L 20, C 6, H 1, T 2) | ≈ 175 min (X1→L1→L8→L10→L13b→gate1→L16→L17→final) | 3.0 h (2.6–3.8) |
| 05 comparison-hypothesis | sign/ε, Hyp.X (X1)–(X4), subquot, Xlambda, simplicial shape | `Hyp.X.char/gal/iso`, `theta`, consistency, subquot on `if:s06-lemD`, Xlambda finite | T05-1, T05-2, T05-3 | 2 slides | 31 rows, 27 scheduled | 126 min (X1→L1→int1/2a/2b→merge→G1→L10→L11→G2) | 2.1 h (1.5–3.2) |
| 06 integral-defect | Lemmas S/G/D, Thm E, decomp, defect, galois, levM, betti | CommAlg core (early lane, incl. η-principle L17), `Defect.Setting`, `Hyp.HsiehGor` + 8 `Hyp.*`, Thm defect, corollaries | T4, T5, H3, C4(i) | 3 slides | 53 rows (AW = 16 audits in 1 row), 48 planned | A 130 min / B 154 min | A 2.2 h (1.6–2.9), B 2.6 h (1.8–3.4); early lane 2.0 h off-path |

Total stages 02–06 ≈ 12.7 h sequential (05 ∥ 06 possible after 04: ≈ 10.6 h), against the stage-plan walls above (§4.4
method; cross-check revision-1 × 0.25–0.35 rests on **n = 1**). Dependencies: 01 → 02 → 03 → 04 → {05, 06}; 05 imports
`if:s06-lemD` (Lemma D) from the S06 early lane (merged before S05-X1, §4.3) or stubs it. Remote M WPs (§6.1) start after their
stage's X1 (drivers) and their inputs are merged. Stage 02 is planned **ready to launch**; 03–06 are concrete but get a final pass
before launch. Re-plan summary: `REPLAN-S02-06.md`.

## 8. Decisions
Revision-1 decisions F1–F9 were **PROVISIONAL (global master, 2026-11-14)**; Fabian may revisit any of them. Status after
stage 1, and decisions taken during stage 1 (F10–F17):
- **F1 — P (path dependency). SETTLED by S01-X1a: P with seeding regime (a)**, no P′, no V (`DECISION-PV.md`, 9f49151).
  The import `lean/trace-formula-project-import/lean/**` stays read-only; changes only via the global master (§3.2).
- **F2 — lock model S01-X1b. DONE** (a8b6ffb); `SLOTS=3` on TITAN in force.
- **F3 — track sub-coordinators. Used in stage 1** (M 52 min, C/T 28 min); kept for 02–06 (§4.1).
- **F4 — Fable. SUPERSEDED** by Fabian (2026-11-14): Fable may run in parallel, including several Fable agents; Lean
  audit ∥ chapter audit (§5.3).
- **F5 — licensing is Fabian's decision. OPEN**: `lean/Langlandscape/THIRD-PARTY-NOTICES.draft.md` (S01-X6), "Fabian:
  choose license".
- **F6 — schematic JL interfaces. In force**: `Hyp.JLClassical`, `Hyp.LambdaJL` registered in `HYPOTHESES.md`.
- **F7 — `ι_ℓ` as the import's `Classical.choose`; ext WPs may continue into later stages. In force**; carried-over
  items in each stage plan §0 (closure "open issues", `runs/s01.md` coverage updates).
- **F8 — HACS. Updated by F16.**
- **F9 — `agents/rules/lean.md` update. DONE** (applied on `main` before stage 1).
- **F10 — no local Lean** (Fabian, ≈ 15:52Z): all Lean builds/checks on TITAN (§4.2–4.3) for stages 02–06 until Fabian
  lifts it (`resources.md` TEMPORARY).
- **F11 — file outbox** (incident ≈ 16:49Z: a SendMessage with job batches and `s01-int1-1` was lost; stage idle ≈ 6
  min): every TITAN job spec, status and closure is a committed file in `plan/implementation/outbox/`; SendMessage only
  notifies (§4.3, §9 lesson 5).
- **F12 — subagent limit 8 per delegating agent** (Fabian, 2026-11-14), resource-permitting (§4.1).
- **F13 — model assignment §5.1**; muse/mistral dropped as implementers (stage-1 study, SUMMARY.md 1d02384).
- **F14 — stacking on unverified drafts + batched integration rounds** (§4.3); worked in stage 1 (int1 → int2f ≈ 25 min).
- **F15 — Abhijit node** (scout b4d42ea): remote-eligible WPs per §6.1; no Lean there until Q1 is answered; every stage
  launches without him. Abhijit questions Q2/Q5/Q6/Q7 to Fabian pending.
- **F16 — HACS 0.2.1** arrives in `code/hacs/` and runs on local CPU/GPU (Fabian); H-WPs are scheduled once
  `code/hacs/` is filled, otherwise stay optional.
- **F17 — audit remarks**: required remarks of a milestone audit are fixed in the same stage as audit-fix WPs; the
  stage-1 hygiene carry-over (80 linter warnings in `Langlandscape/`, L15 R8b/R8c helper/test names) goes to one
  **sonnet (+1 opus fix)** hygiene WP in S02 (it edits Lean), checked in a TITAN round (O20).
- **F18 — rule updates before S02 launch (O9; OPEN, global master, on `main`, as F9 did for `lean.md`).** The following
  rules still contradict this OVERVIEW; the stage masters read the rules first and would follow the old flow: (1)
  `agents/rules/resources.md` TEMPORARY job flow ("SendMessage 'main': job spec") → file outbox (§4.3, F11), plus the
  Abhijit node row and 16 GB budget (§6.1); (2) `agents/rules/git.md` area list: add `plan`, and the branch
  `wip-implementation` with the `impl/`, `exp/`, `titan-in/`, `titan/`, `abhijit/` families (§2); (3) opencode/muse/mistral
  text in `agents/roles/global_master.md`, `agents/roles/coordinator.md` and `CLAUDE.md` marked "not used as implementer
  (§5.1)"; (4) `agents/rules/lean.md` l. 22 docstring line per §3.6 (O8); (5) `agents/rules/orchestration.md`/
  `plan/implementation/EXPERIMENT_PROTOCOL.md` §1, §7 and `briefs/common.md` l. 31 are superseded by the precedence
  clause in the header. These are **not** made in `plan/`; the stage-02 launch condition is that (1)–(4) are done.

## 9. Stage-1 lessons (each is a concrete gate/step in every stage plan)
1. **Early full gates.** As soon as the core Lean WPs are green (≈ mid-stage), run the full stage gate `sNN-gate1-1` on
   `wip-implementation` (all targets + `Audit/PrintAxioms.lean` + forbidden-token grep + `check_frozen.sh`; §4.3
   variant), not only at the end; it is the commit the Fable Lean audit reads. The final gate `sNN-final-1` runs from
   scratch (unseeded) after the audit fixes. (Stage 1: L14 gate failed once only at the axioms step, 12 unqualified
   names; caught at 17:18Z, not at the end.)
2. **Axiom scratch files.** Fully qualified names (`Langlandscape.…`), every needed import listed (s01-int3:
   `card_XB_Utower` lives in `Quat/MassTower.lean`, not imported → `Unknown constant`), and the wrapped-line join
   (`#print axioms` output wraps; join with whitespace normalisation, primed names included: the current
   `titan_batch.sh` counter does neither until **S02-X1 tool fix: axiom counter** lands, §4.3). One file per WP
   (`.titan/sNN_<wp>_axioms.lean`). **Generate the list mechanically** from the WPs' declared outputs (one haiku WP per
   stage, input: WP table outputs + the merged `Audit/PrintAxioms.lean`); the haiku WP **returns the list in its report**
   and the stage master writes the scratch files and extends `Audit/PrintAxioms.lean`.
3. **Docstring gates (exact rule, O8).** **Every `theorem`/`lemma`, including `private` ones and those in
   `LanglandscapeTests/`**, has an immediately preceding `/-- … -/` containing a label `s<NN>-…` (stage-tex label until
   the chapter exists, then the `mathematics/` label); public `def`/`structure` have a docstring, reviewed in the WP audit
   (not machine-checked). `check_wp.sh`'s check must pass **in the integration round** (it is in `CHECK_WP`); the stage
   master does not patch docstrings afterwards (stage 1: L8a docstring fixed by the stage master). Worker briefs state
   the exact rule; **S02-X1 tool fix: docstring pattern** generalises `s01-` to `s[0-9][0-9]-` (§4.3).
4. **Stale strand bases (O5).** When an upstream fix lands in an integration round, rebase open strands and WP branches
   before their next TITAN round onto the **fixed upstream WP head(s)**, or onto `wip-implementation` once the upstream
   fix is merged; if the integration tree is the base, use `impl/sNN-int<k>~1`, never its `.titan/` commit and never
   non-green drafts that are not upstream of the WP (stage 1: L13 strands blocked 3 of 4 rounds by upstream errors).
5. **Per-coordinator outbox, never SendMessage-only.** Every job spec, status and closure goes to
   `plan/implementation/outbox/` (committed); SendMessage is only a notification (F11).
6. **No fix hints in experiment relays** (§5.2; stage 1: hints in the l9-b-2 relay had to be stripped).
