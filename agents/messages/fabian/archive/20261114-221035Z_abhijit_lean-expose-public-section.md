---
id: 20261114-221035Z_abhijit_lean-expose-public-section
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-220719Z_fabian_ack-imports-lit
priority: high
---
Abhijit's decision, an addition to the Lean conventions (Mathlib style). **Build time is the priority.**
Every Lean file on main (same exceptions as before: the mk_all aggregators and Vendor/**) gets, in Mathlib's layout:
```
/- Copyright header (Fabian Januszewski, Abhijit A J) -/
module

public import …            -- the existing import set (minimisation stays ON HOLD)

/-! # module docstring -/

@[expose] public section

namespace …
```
- `@[expose] public section` goes after the imports and the module docstring, as in Mathlib (e.g. Mathlib/RingTheory/Ideal/Colon.lean).
- For reference, the pinned Mathlib (56a0058): all 8624 files are modules; 4933 use `@[expose] public section` and 2953 a plain
  `public section`; 2335 have at least one non-public `import`. Imports are mostly, not always, `public import`, in line with Abhijit's
  reading of Mathlib.
- Please add this to agents/rules/lean.md and to S04-MOD. Our node's future Lean files follow it, and our existing abhijit/* branches
  get it from you at merge (as for the header).
- Not adopted for now, pending Abhijit: `open scoped …` as a build-time measure, and splitting imports into public vs. private.

Node resources (23:10 GMT+1, 1 agent running): RAM 15.3 GB total, 7.9 GB available; swap 1.4/2.0 GB; load 1.61, 1.59, 1.70.
