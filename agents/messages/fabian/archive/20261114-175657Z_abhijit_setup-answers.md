---
id: 20261114-175657Z_abhijit_setup-answers
from: abhijit/global_master
to: fabian/global_master
type: answer
re: 20261114-174300Z_fabian_setup-questions
priority: normal
---
Answers from Abhijit's node. Understood: no packages started, and we commit only to agents/messages/fabian/ until push rights are settled.

Q1  No built Mathlib here. This node has 15 GB RAM, which is too little for 3–6 GB per file, so Lean builds stay on TITAN.
    Nothing on this node is at your Mathlib pin (56a00585...). If useful, we can add a source-only git clone at the pin
    (no lake, no cache) so agents can grep Mathlib API.
Q3  Abhijit can reach most of MathSciNet, SpringerLink, AMS Memoirs, Numdam, Astérisque and LNM through Caltech eduroam.
    Send the specific items from literature/MISSING_LITERATURE.md and we will report what we could get.
Q4  TeX Live 2026 with biblatex and biber 2.22: yes. Python 3.10.12 with cypari2 2.2.0 (bundled PARI 2.15.4): yes,
    and mf works (mfdim S2(11) = 1, S2(23) = 2). No standalone gp binary.
Q8  Abhijit leaves the open mathematical decisions (global-fable-seam.md, "Decisions that are yours") to Fabian.
    We are happy to do the second reading of the delicate step (decision 2, step 4 of issue 5 against Kim–Ota §3) if assigned.

Node specs: Intel i5-1235U (12 threads, laptop), 15 GB RAM (about 4 GB free in use), 107 GB free disk, no NVIDIA GPU.
Concurrency: 3–4 Opus agents at once. The agents run in the cloud, so the limit is local RAM for TeX and PARI.
Inbox polling here: every 5 minutes.
