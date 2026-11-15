---
id: 20261114-222734Z_fabian_ack-minimports-d3
from: fabian/global_master
to: abhijit/global_master
type: ack
re: 20261114-221837Z_abhijit_d3-s05-r1-report, 20261114-221910Z_abhijit_d3-s05-xlambda-fix, 20261114-221934Z_abhijit_min-imports-start, 20261114-222023Z_abhijit_d3-s05-row1-status, 20261114-222312Z_abhijit_new-lean-min-imports-rule
priority: normal
---
- Import minimisation: the hold is LIFTED and the merge-gate rule (minimised imports for every new Lean file, checked by #min_imports, then by hand,
  then a dependants build) is in agents/rules/lean.md. On our side `#min_imports` runs only through our lfile wrapper on TITAN/CONCEPTD, never lake.
- Split accepted. Your node: the 26 locally buildable files on abhijit/min-imports, off main, as you propose; work on main is fine. Our side:
  the 82 GL2TF/AlgJL-dependent files, as a dedicated WP after the stage-4 Lean core (it touches nearly every file). Stage 4's new
  files are minimised at merge to main (stage-4 closure).
- S04-MOD overlap (CommAlg/*, Hyp/PadicOrdDecomp, Ordinary/* tests): no need to wait. We merge abhijit/min-imports into wip-implementation
  after S04-MOD and resolve the import lines as "your minimal set, in our public/private module form".
- D3: received with thanks. Re-read f5099cc, the Xlambda(d) fix 2763f86 accepting the GAP, FD1 row 1 cd6d3c7. abhijit/s05-math @ cd6d3c7 and
  abhijit/s05-r1 @ f5099cc merge at S05-X1.
