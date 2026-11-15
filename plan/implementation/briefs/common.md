# Common brief for all P3 implementation-plan writers (drafters, revisers)

Worktree: `/home/janosch/dev/Langlandscape-wt/plan`, branch `wip-plan`. Write only the files your brief names, under
`plan/implementation/`. Commit only your own files (`git add <files> && git commit -m "plan: ..." -- <files>`; if
`index.lock` exists, wait 10 s and retry; other agents commit in the same worktree). **Never push.** Never edit `plan/seed/`,
`plan/staged/` or anything under `lean/trace-formula-project-import/`. Do not run Lean builds (this is a planning phase).
Read: `CLAUDE.md`; `agents/rules/{orchestration,resources,frozen,opencode,lean,mathematics,code,talk}.md`;
`plan/staged/SPLIT.md`; your stage tex `plan/staged/stage-NN-*.tex` (note `\provisional{}` markers); `plan/staged/audits/
global-fable-seam.md` + `global-fable-resolution.md`; `plan/staged/METRICS.md`; `plan/scouting/SUMMARY.md` (+ per-repo files
as needed); `plan/implementation/OVERVIEW.md` once it exists (it overrides this brief where they differ).
The import: `lean/trace-formula-project-import/{README.md,TEAM_BRIEF.md,MANIFEST_SCOUT.md,KEPT_IDS}`, `lean/AlgJL/**`, `tools/`.
Literature (read-only, never copy text): `/home/janosch/dev/Langlandscape/literature/` (pdftotext).

## WP schema (one block or table row per WP)
`id` | track | goal | inputs (stage-tex labels, e.g. `def:s01-brandt`, `if:s01-...`; import declarations) | outputs (files,
Lean declaration names) | acceptance check (mechanical where possible: `latexmk` exit 0, `lfile.sh` ok with no `sorry`,
`pytest` pass, numbers match table) | difficulty | model | est. agent wall (min) | est. build wall (min, Lean) | deps.
- id: `S<NN>-<T><k>`, T ∈ {`X` infra/setup, `M` mathematics/LaTeX, `L` Lean, `C` code/Python/CAS, `H` HACS, `T` talk}, e.g. `S01-L3`.
- difficulty ∈ {mechanical, routine, hard, conceptual}.
- model ∈ {muse, haiku, mistral, sonnet, opus, fable} (cost order, cheapest first; muse/mistral run via opencode and need a
  Claude verifier, name it). Prefer the cheapest model that does not lengthen WALL time (a failed cheap attempt + retry
  can cost more wall than one strong attempt — say so where relevant). Haiku is weak at conceptual maths.
- Every Lean WP has an explicit statement interface in `mathematics/` or the stage tex (decoupled tracks: maths may run ahead;
  Lean WPs depend only on the existence of the statement, not on a finished LaTeX proof).

## DAG and wall time
- Give the DAG as an edge list (`A -> B`) plus a Mermaid block, mark parallel waves, and state the critical path with
  summed estimated wall time. Optimise for minimal WALL time: start long Lean builds early, keep both localhost build slots
  (wrapper `SLOTS=2`, `BUILD_MEMORY_MAX=8G`) and up to 3 TITAN slots busy while agents write the next code. TITAN jobs are sent
  by the global master only; TITAN pushes only to `titan/<job-id>`. Mark which builds/checks are TITAN candidates.
- Concurrency: ≤ 3 Claude subagents per coordinator (Fable alone), ≤ 6 opencode jobs (Lean-building ones count double),
  RAM budget per `resources.md`.
- Baselines (from P1 METRICS): Opus draft of a ~500-line stage tex 14–22 min; Muse audit ~1 min; Sonnet revision ~2 min,
  Opus revision 4–8 min. Import build: full `--audit` ~70 min (deps.conf); give your own estimates with a reason.

## Branching for implementation (provisional; OVERVIEW.md finalises)
- Stage NN integration branch: `wip-implementation` (synced with the previous stage's result before stage NN starts); the
  global master merges it to `main`. Per WP: worktree `/home/janosch/dev/Langlandscape-wt/sNN-<wp>` on branch
  `impl/sNN-<wp>` off `wip-implementation`, merged back by the stage master. Experiment strands: branch
  `exp/s01-<wp>-<model>`, worktree `/home/janosch/dev/Langlandscape-wt/exp-s01-<wp>-<model>`.
- Each WP changes only its track's directory (`mathematics/`, `lean/`, `code/`, `talk/`).

## Lean project structure (provisional; OVERVIEW.md decides after a feasibility analysis)
- Our own code (incl. vendored Stacks Skolem–Noether, Apache-2.0, identical toolchain + Mathlib rev) lives in a NEW Lake
  project `lean/Langlandscape/` (never inside the frozen import). It reuses the frozen Mathlib farm (this node:
  `/home/janosch/data/gl2tf-deps-v4350` → `/home/janosch/data/mathlib4_v4350`) through its own copy of the import's
  `link_deps.sh` mechanism and its own `lbuild.sh`/`lfile.sh`-style wrappers (copies adapted to the new project path).
- Option P: `require GL2TF from "../trace-formula-project-import/lean"` (path dependency; manifest must resolve offline,
  no `lake update`). Option V: byte-copy (vendor) the needed `AlgJL` files into our project. Stage 1 begins with a smoke
  test WP (`S01-X1`) that decides P vs V; stage-1 WPs downstream must work under either outcome.
