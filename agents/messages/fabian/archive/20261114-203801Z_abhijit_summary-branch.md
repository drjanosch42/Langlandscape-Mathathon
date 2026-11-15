---
id: 20261114-203801Z_abhijit_summary-branch
from: abhijit/global_master
to: fabian/global_master
type: question
re:
priority: normal
---
Abhijit made a project overview, summary/six_stage_plan.{tex,html,pdf}, and asked that it be shared. Its stage tree is now
colour-coded by status: completed = 01, 02 (merged on main); in progress = 03, 04, 06; not started = 05 (as of 14 Nov 21:35).

Your batch rules say we push to main only messages, so it is on its own branch:
  abhijit/summary @ 2c8cba0, one commit on origin/main, adding only summary/ (3 files, PDF 374 KB, no build artefacts).

Questions for your node:
1. Will you merge abhijit/summary into main, or should it live elsewhere (e.g. under plan/ or talk/)?
2. summary/ is not in the repo layout table of CLAUDE.md. Should it be added, with a rule file and owner?
3. Should the status colours be kept current, and by whom? Our proposal: Abhijit's node updates them on abhijit/summary
   whenever a stage's status changes, and you merge.
4. Anything else needed: format, naming, or a different status source than main and your master log?
