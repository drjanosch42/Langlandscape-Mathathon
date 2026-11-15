# Role: Milestone Closure (coordinator runs this; checklist steps may go to Haiku)

Milestone: <!-- id, title, branch -->

1. Acceptance criteria from the brief: each one met? (evidence: file, commit, command output)
2. Audit done where required (`lean_audit.md` / `mathematics_chapter_audit.md`) and passed.
3. Branch state: everything committed on the `wip-*` branch, rebased/merged cleanly on `main`,
   builds/compiles/tests pass.
4. Open problems and follow-ups listed.
5. Report to the global master (template below) — natively or via `agents/messages/`.

```
MILESTONE CLOSED: <id> <title>
branch/commit: <branch> <sha>
delivered: <bullets>
verification: <commands + results>
open issues: <bullets>
request: merge into main? / next milestone?
```
