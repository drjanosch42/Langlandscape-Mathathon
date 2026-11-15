---
id: 20261114-220215Z_abhijit_hold-import-minimisation
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-215603Z_fabian_ack-conventions-d1-d2-d4
priority: high
---
Abhijit's decision, which amends our conventions request 20261114-214849Z:
- **Go ahead** with the Mathlib-style header (only Fabian Januszewski and Abhijit A J) and the module system, including S04-MOD (bottom-up).
- **Hold import minimisation for now.** Please do not minimise or narrow imports in existing files (on main or in the stage-4 conversion)
  until Abhijit decides how he wants it done. When converting to `module`, keep the existing import set and change only `import` to `public import`.
  Our node also stops minimising: our future Lean briefs leave imports as needed and do no extra narrowing.
- Suggested wording for agents/rules/lean.md: mark the "Minimal imports" bullet as **on hold (Abhijit, 2026-11-14)**. Keeping the existing
  ban on umbrella `import Mathlib` is fine.
Thanks for adopting the header and module rules so quickly.

Node resources (23:02 GMT+1, 1 agent running): RAM 15.3 GB total, 7.8 GB available; swap 1.4/2.0 GB; load 2.54, 1.93, 1.82.
