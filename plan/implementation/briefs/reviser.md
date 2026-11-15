# Brief: reviser of the implementation plan for stage NN (after the Muse audit)

Worktree `/home/janosch/dev/Langlandscape-wt/plan`, branch `wip-plan`; commit only the two files below, never push.
Read `plan/implementation/briefs/common.md`, `plan/implementation/OVERVIEW.md`, `plan/implementation/stage-NN.md`, its stage
tex `plan/staged/stage-NN-*.tex`, and the Muse Spark Open audit `plan/implementation/audits/stage-NN-muse.md`.
(For NN = 01 also `plan/implementation/EXPERIMENT_PROTOCOL.md`.)
Muse audits are known to be mostly wrong in their fixes and to inflate severity (see `plan/staged/METRICS.md`). **Check each
finding independently** against the files (labels exist? DAG edge really missing? limit really exceeded — note that the
3-Claude-agent limit is per coordinator, and opencode jobs do not count as Claude agents?). Classify each finding as
confirmed / partially confirmed / rejected with a one-line reason and your own severity. Apply the confirmed (and the
confirmed part of partial) fixes to `stage-NN.md` with minimal edits; fix any further defects you notice while checking
(list them as R1, R2, ...). Keep the WP ids stable.
Write `plan/implementation/audits/stage-NN-resolution.md`: table (finding | Muse severity | verdict | own severity | action),
then the extra findings, then counts C/P/R. Commit `plan: stage-NN Muse audit resolution`.
Report ≤ 8 lines: sha, counts C/P/R, own severity counts, wall time (start/end `date +%T`).
