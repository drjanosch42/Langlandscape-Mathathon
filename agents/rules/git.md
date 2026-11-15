# Rule: git workflow

- `main`: integrated state; merges from `wip-*` only by a global master after milestone closure.
- `wip-mathematics` → `mathematics/`, `wip-lean` → `lean/`, `wip-code` → `code/`, `wip-talk` → `talk/`, `wip-plan` → `plan/`.
  Implementation (OVERVIEW §2): `wip-implementation` (spans all track directories; merged into `main` by the global master
  at stage end) and the branch families `impl/` (WP and integration branches), `exp/` (experiment strands; **local only,
  never pushed**), `titan-in/` (neutral temporary refs for TITAN jobs; deleted after fetch), `titan/` (TITAN results;
  fetched by the global master, never merged) and `abhijit/` (remote packages; fetched by the global master).
  A `wip-*` branch changes only its own directory unless the brief says otherwise.
- Keep `wip-*` branches up to date by merging `main` into them regularly.
- `agents/` (roles, rules, messages) is edited on `main` only.
- Parallel agents on one branch use separate `git worktree`s; one writer per file at a time.
- Commit message: `<area>: <imperative summary>`; area ∈ {math, lean, code, talk, plan, agents, msg}.
- Never force-push shared branches; never rewrite `main` history.
