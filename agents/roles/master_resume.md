# Global master: resume / handover / post-compaction procedure

Use this file in three situations: (A) after a crash or unexpected termination, (B) a planned handover to a fresh master session,
(C) after context compaction in the running session. It is the operational complement of `agents/roles/global_master.md`.
**The authoritative live state is `agents/status/STATE.md`** (updated by the master at every heartbeat and at every milestone);
the history is `agents/status/master_log.md`.

## 1. Read, in this order (all paths relative to /home/janosch/dev/Langlandscape)
1. `CLAUDE.md`, `agents/roles/global_master.md` (role, model table, limits, the recorded lessons), `agents/rules/model-selection.md` (model-vs-task policy + evidence), this file.
2. `agents/status/STATE.md` (what is running, open decisions, next steps). Then `tail -40 agents/status/master_log.md`.
3. `agents/rules/*.md` (frozen, lean, resources incl. node table, orchestration, messages, licensing, code, git, opencode).
4. The active stage: `plan/implementation/stage-0N.md` and the latest files in
   `/home/janosch/dev/Langlandscape-wt/impl/plan/implementation/{outbox,inbox}/` (`ls -t | head`).

## 2. Re-establish the machinery (A and B only; in C everything still runs: verify, don't recreate)
- **Crons** (session-only; they die with the session; re-create them with CronCreate):
  - heartbeat at minutes 7,37: disk/RAM check, agent status, launch the next phase, commit and push, one log line;
  - inbox check at minutes 3,13,…,53: `git fetch`; new files in origin/main:agents/messages/fabian/ → `git pull --no-rebase`, answer/ack, archive, push.
- **Peers** (ListAgents): TITAN (Lean build node, 3 slots) and CONCEPTD (Lean build node, 2 slots) are separate sessions reached by
  SendMessage; they keep running across a master crash. Send each a one-line "new global master session is <name>; continue to
  report to it". Abhijit's node is reached ONLY via git messages (agents/messages/abhijit/); nothing to re-establish.
- **Stage master** (an in-process teammate of the old session) is GONE after A/B. Re-launch it with the Agent tool (Opus, background)
  as "stage-N master (resumed)", with its usual brief plus: "Resume from the outbox/inbox state and wip-implementation; do not redo
  merged WPs; check impl/* and titan-in/* branches and the per-WP worktrees under …-wt/ for drafts in flight." Stopped teammates'
  half-done WPs survive as commits on their impl/* branches or in their worktrees.
- **Worktrees**: `git worktree list`; keep those of WPs that aren't merged yet (writers may need fix rounds). Never `rm -rf` (symlinks into frozen trees).
- **Pane hygiene**: `tmux capture-pane` on new agent panes (folder-trust dialog), CPU time to detect idle agents.

## 3. Standing procedures (all scenarios)
- **TITAN/CONCEPTD job relay:** read the outbox spec → `git push origin <branch>` (or `<sha>:refs/heads/titan-in/<id>` for neutral
  experiment refs) and `wip-implementation` → SendMessage the node a self-contained spec (job id, sha, seed, wrapper commands, report
  format, result branch `titan/<id>` or `conceptd/<id>`) → on the result: write `…/impl/plan/implementation/inbox/<UTC>_<job>.md`
  (verbatim errors and goal states; NO fix hints for experiment strands) + a short SendMessage to the stage master → delete the
  `titan-in/*` ref after the node confirms the fetch. Route to the node with the warmest build and a free slot; batch in parallel.
- **Git on main:** only `git pull --no-rebase` (never --rebase after merges). Commit the master log before pulling. Only the master
  pushes main/wip-*; TITAN/CONCEPTD push only `titan/*`/`conceptd/*`; Abhijit pushes only `abhijit/*` and his messages.
- **Milestones:** review the closure (outbox) → push wip-implementation → `git merge --no-ff` into main (check: no literature/, no
  .lake, no files > 10 MB, frozen paths unchanged) → push → fast-forward wip-implementation to main → remove merged worktrees →
  rclone COPY the milestone PDFs (mathematics/main.pdf, talk/main.pdf, summary/six_stage_plan.pdf, plan/staged/main.pdf) to
  `gdrive:dev/Langlandscape/<same path>` (copy only; never sync/delete) → `rclone lsl` to verify → launch the next stage master.
- **Abhijit:** acknowledge every report, archive his message, accept Lean drafts by a TITAN/CONCEPTD acceptance build, merge his
  branches when the owning stage starts. Batch plans: `agents/status/abhijit_batch1.md` and the sent batch messages.
- **Resources:** /mnt/c < 50 GB warn, < 20 GB no new spawns; RAM ≥ 12 GB free. Local Lean is OFF (CPU/GPU reserved for HACS);
  all Lean goes to TITAN/CONCEPTD.

## 4. Handover checklist (B: old session, before it stops)
1. Update `agents/status/STATE.md` (running jobs with node + sha, open decisions, next step), commit and push main and wip-implementation.
2. Tell the stage master to write a status file to the outbox.
3. Delete the old session's crons (CronDelete), then stop the session. The new session follows §1–§2.

## 5. After compaction (C)
Re-read §1 items 1–2 and the last 10 outbox/inbox files; check `CronList` (both crons present?) and `ListAgents` (stage master
alive?). Then continue; don't re-send jobs that already have an inbox result.
