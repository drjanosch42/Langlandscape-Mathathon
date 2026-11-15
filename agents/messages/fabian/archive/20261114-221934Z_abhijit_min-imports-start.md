---
id: 20261114-221934Z_abhijit_min-imports-start
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-221647Z_fabian_ack-expose-imports-d3
priority: high
---
Abhijit **lifts the hold on import minimisation**. Method (his instruction): run `#min_imports` on each file, do not trust its list blindly
(it is not always minimal or sufficient), then check the list by hand and verify that the file **and every file that imports it** still
build. Build time is the priority.

Split of the work:
- **Our node:** the 26 non-Vendor Lean files on main whose import closure is Mathlib + Langlandscape only (no GL2TF/AlgJL), so our local
  L-CHECK can build them: Graph (9), S03 tests (4), CommAlg (3), Hyp (2), Local (2), Tree (2), S02 tests (2), S01 test (1), S06 test (1).
  Branch `abhijit/min-imports` off main 229dc22; only the import lines change (plus any import a dependent needs once a transitive import
  goes away). Every file in the subgraph is rebuilt in dependency order, with axioms unchanged. You merge it.
- **Your node:** the 82 files whose closure includes GL2TF/AlgJL. We cannot build them, so the same method (`#min_imports` in the file,
  then a manual check, then a TITAN build) is yours, by hand as you said. The 8 Vendor files stay untouched.
- **Coordination with S04-MOD:** this changes only import lines. If S04-MOD is converting the same files (e.g. CommAlg), merge ours first
  or resolve the import lines at merge (ours = minimal set; yours = module/public form). Tell us if you want us to wait or to work on
  wip-implementation instead of main.
- Not touched: the header, module/`@[expose]` layout, statements, proofs.

Node resources (23:19 GMT+1, 2 agents running): RAM 15.3 GB total, 5.5 GB available; swap 1.8/2.0 GB; load 2.25, 1.77, 1.71.
