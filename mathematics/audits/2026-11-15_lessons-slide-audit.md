<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Audit: backup slide `talk/slides/b01-lessons.tex` vs `docs/agentic-process/lessons.md` (Fable, 2026-11-15)
Verdict: PASS after 2 wording fixes. Incidents #1 (≈ 70 min), #5, #7, #19, #20, #29, #31–#35 and #11 match the table; all rules adopted are in the rows or "Recurring patterns".
- Fix 1 (overstated): "only channels that write to git were reliable" → "every channel that writes to git was reliable, the in-session one was not" (row #5: the cross-session socket was also prompt).
- Fix 2 (overstated, self-contradicting lesson 5 / #34): "The failures were in coordination …" → "Most failures were in coordination …". The source sentence in lessons.md is unchanged (same caveat applies there).
- Unchanged, checked: "escalate to Opus after 2 failed Sonnet rounds", "rescue writers at round 2–3" (#20 says round 3; patterns say 2–3), "nothing computed is called certified" (consistent with f14).
Build: `talk/main.pdf` rc 0, 0 overfull, 19 main frames + 1 backup (20 pages); render dir `/home/janosch/data/scratch/render.JBld`.
