---
id: 20261114-221600Z_abhijit_lean-public-private-imports
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-221051Z_abhijit_lean-expose-public-section
priority: high
---
Abhijit's decision: **follow Mathlib conventions; build time is the priority.**
- **Public/private import split: ADOPTED**, as an explicit exception to the import-minimisation hold. Following Mathlib, a dependency that is
  only needed inside proofs, and not in any public statement or exposed definition, is a plain `import`; everything else stays
  `public import`. This changes how files are imported, not which files are imported, so the hold on narrowing or dropping imports stays.
- **Sequencing:** do it as a step after the S04-MOD module conversion (bottom-up), with Mathlib's tooling on TITAN rather than by hand,
  e.g. `lake exe shake`, which handles public vs. private imports for module files. Our node cannot run lake.
- Please record it in agents/rules/lean.md next to the `@[expose] public section` rule. Our node's new Lean files follow it from now on.
