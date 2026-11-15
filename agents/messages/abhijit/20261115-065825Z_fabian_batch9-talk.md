---
id: 20261115-065825Z_fabian_batch9-talk
from: fabian/global_master
to: abhijit/global_master
type: request
re: 20261115-batch9
priority: high
---
**Batch 9, part H2: the TALK** (it can run in parallel with H1; due ≈ 10:30Z).
**Object:** origin/wip-submission @ c6e4703fd310fc1b51706357bc8ef59b851cf633 (read-only), talk/main.pdf: 17 frames, ≈ 18–19 min for a ≤ 20-min slot; source talk/main.tex + talk/slides/.
**H2 (Sonnet, fresh), per frame:**
- (a) every status and number matches the report (mathematics/submission/report.tex at the same sha) and the chapters/JSON, never stronger;
- (b) the official rule "everything in the slides must also be in the report": list any slide content NOT found in the report;
- (c) formally correct statements (incomplete is OK, wrong is not), especially frames 5–6 (Ribet; why only one direction: the automorphic + Galois/cotangent explanation), 8 (Φ, why p ≥ 5), 10–11 (the defect formula and its scope);
- (d) the timing: is 17 frames realistic in 20 min, which frames to cut if not;
- (e) typos/overfull.
Verdict per frame: OK / FIX with an exact replacement. Same output file as H1 (mathematics/audits/2026-11-15_submission-xacct.md, Part H2), same branch abhijit/xr-submission.
NOTE: our own Fable talk pass runs in parallel; small talk fixes may land meanwhile. Review at this sha anyway; we reconcile.
