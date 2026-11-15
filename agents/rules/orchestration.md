# Rule: orchestration (all coordinators and workers)

- **Subagents may commit, never push.** Only the global master pushes and merges into `main`.
- Each master/coordinator works in its own git worktree under `/home/janosch/dev/Langlandscape-wt/<name>`
  on its assigned branch; parallel writers use separate worktrees or disjoint files. The global master removes
  worktrees after a successful merge.
- Implementation of stage k merges first into `wip-implementation` (synced to the latest completed stage beforehand),
  then to `main` after the global master's review.
- Every planning/implementation stage gets a dedicated master (Opus) that delegates further, in parallel whenever
  possible, to minimize WALL time. At most 8 concurrent Claude subagents per delegating agent, as long as
  `agents/rules/resources.md` allows (RAM ≥ 12 GB free, disk thresholds); Fable may run in
  parallel with other agents, including other Fable agents (Fabian, 2026-11-14).
  opencode jobs are not Claude subagents but count towards `agents/rules/resources.md` limits.
- `literature/` lives only in the main checkout: `/home/janosch/dev/Langlandscape/literature/` (git-ignored, except
  `literature/MISSING_LITERATURE.md`, which lists missing literature and is committed).
- Model choice: see `agents/roles/global_master.md`. opencode models: `agents/rules/opencode.md`.
- Reports to the parent: short (≤ 30 lines); full detail goes to files, and the report gives their paths.

## Milestone PDFs
- At every milestone the built PDFs (e.g. `plan/staged/main.pdf`, stage PDFs, mathematics/talk PDFs) are **committed**
  in-tree next to their sources, so that they can be checked without recompiling.
- Only the global master mirrors them to Google Drive: `rclone copy <pdf> gdrive:dev/Langlandscape/<repo-relative dir>/`.
  Only `rclone copy`/`copyto` are allowed (additive; overwriting is fine). **No** sync, move, delete, purge, dedupe,
  mkdir-free cleanups or any other rclone operation. No other agent uses rclone.

## Decoupled tracks
- Mathematics/LaTeX and Lean formalization are **not** synchronized: the mathematical text may run ahead of the
  formalization. Milestones are per track (math, Lean, code, talk); no milestone may stall one track to wait for another.
  The only coupling is an explicit interface (the statement being formalized must exist in the mathematics first).

**Precedence:** `plan/implementation/OVERVIEW.md` takes precedence over `plan/implementation/EXPERIMENT_PROTOCOL.md` §1/§7 and `briefs/common.md` where they conflict (precedence clause in the OVERVIEW header).

## No deletions by shell (Fabian, 2026-11-15)
Agents NEVER run `rm`, `rm -rf`, `rmdir`, `find -delete` or `unlink`. Each triggers a permission prompt on the human's shell and blocks unattended work. Use `git worktree remove` for worktrees, `git rm` for tracked files, and `mv` to /home/janosch/data/trash/ (or leave files in a scratch dir) for everything else; for CMake rebuilds, use a new build dir name. Every brief must repeat this rule.
Refinement (Fabian, 2026-11-15 ~07:00Z): the prompts come from wildcard (`*`) or unclear-scope deletes, and sometimes from `git rm`. Until further notice, no `git rm` either; `git worktree remove <exact path>` is fine.
