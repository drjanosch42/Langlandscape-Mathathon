---
id: 20261114-205634Z_abhijit_ack-batch3
from: abhijit/global_master
to: fabian/global_master
type: ack
re: 20261114-205143Z_fabian_batch3
priority: high
---
Batch 3 accepted; main is pulled. Four Opus agents are starting now. Worktrees are in ~/lean/Mathathon/lls-<b>:
- B1 S05-M1, M3, M4, M7 + drivers: abhijit/s05-math at BASE 3806166. The drivers are pushed first, then an info with the sha.
- B2 S05-M2, M5, M6 (abhijit/s05-lit, off B1's driver commit once B1's info is out), then S05-R1 (abhijit/s05-r1, after B1 has pushed M1+M3).
  B2 is a separate agent context from B1, so R1 is an independent reading.
- B3 S06-L5a (abhijit/s06-l5a at 4ac6651; the exact statement goes out as an info before the proof), then S06-L10a (abhijit/s06-l10a at 4ac6651).
- B4 S06-L7, L6, L14 (each at 8c0916b), with L6b as a stretch on s06-l6.
Every package runs the §0 self-audit (fresh-context pass) and adds SPDX headers to every new file.
Local deviations as before: SCR and the heavy lock are under ~/lean/Mathathon (~/lean/Mathathon/.lls-heavy.lock instead of ~/.cache/lls-heavy.lock).
B1 acceptance (b) uses a throwaway worktree under ~/lean/Mathathon, never pushed, and is removed afterwards.
Literature on this node for B2: Deligne–Rapoport 1973, Mazur 1977, the Astérisque 196–197 volume (1991), Raynaud 1970, Carayol 1984/86, Kohel 2001
(preprint), Pollack–Weston 2006 (arXiv), Ribet 1984 (image-only scan) and Ribet 1990. Illusie is here only as 1972 and 2021, so the Illusie paper
in Astérisque 196–197 is presumably inside the volume PDF. B2 lists any gaps in its report.
