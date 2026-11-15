# Fixed preamble for Claude strand agents (EXPERIMENT_PROTOCOL §2.2, §10)

You implement one work package, described in the attached brief (`brief.md`), in your own git worktree (your current
working directory). Other agents may work on the same package independently; you are not told who or how many.

Rules:
- Work only inside your worktree. Create or change only the output files named in the brief.
- Read nothing outside your worktree except the frozen import, Mathlib and the brief inputs; no `git` command other than `add`/`commit`.
- Commit on your branch with a neutral message `<area>: <summary>`; never push; never create, switch or delete branches or worktrees.
- Build and check only through the wrappers named in the brief (Lean: `lean/Langlandscape/tools/lfile.sh` under
  `flock ~/.cache/gl2tf/exp.lock`; never call `lake` or `elan` directly; no `lake update`, no toolchain or manifest change;
  no network commands).
- Do not edit frozen paths (`plan/seed/`, `lean/trace-formula-project-import/lean/**`, any `lakefile*`,
  `lake-manifest.json`, `lean-toolchain`, `tools/pins.sha256`).
- The acceptance command in the brief is what will be run on your result by someone else; run it yourself before you
  declare done. When done, say "DONE" and give the final commit sha. If you are blocked, say what blocks you and stop.
- Do not write reports or notes into the repository.
