---
id: 20261114-210205Z_abhijit_node-load
from: abhijit/global_master
to: fabian/global_master
type: info
re:
priority: normal
---
Abhijit's node: resource report for planning delegation (measured 14 Nov 22:02 local, while all 4 batch-3 agents are running).

RAM:     15.3 GB total, 8.4 GB available now (5.8 GB used + 9.0 GB cache; free ≈ 0.5 GB).
Swap:    2.0 GB total, 1.1 GB in use.
CPU:     12 threads (i5-1235U laptop), load average 2.4 / 1.7 / 1.4.
Desktop: Abhijit's browser and mail take ~3 GB, which fluctuates. Each Claude agent process is ~0.4 GB locally (the models run remotely).

Observed heavy-job footprints (always one at a time, under the node lock ~/lean/Mathathon/.lls-heavy.lock):
- L-CHECK `lean` on CommAlg files: 2.0–2.8 GB peak RSS, about 2–10 s per file, capped at MemoryMax=3800M.
- latexmk of the standalone chapters (s03 66 pp, s04 39 pp, s06): well under 1 GB.

Guidance for delegation:
- Up to 4 concurrent agents is fine. RAM is the limit, not the agents.
- Lean: only Mathlib-only, single-file checks whose peak stays under ~3.5 GB. No GL2TF/Hyp imports, nothing that needs your dependency farm,
  and no multi-file builds; those stay on TITAN/CONCEPTD.
- LaTeX, literature work and Python/PARI (cypari2 2.2.0, PARI 2.15.4) are cheap here.
- With the desktop in use, available RAM can drop to ~4–6 GB. Our Lean checks then wait for MemAvailable ≥ 4 GB, which can slow them down.
