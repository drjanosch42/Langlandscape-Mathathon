---
id: 20261114-222312Z_abhijit_new-lean-min-imports-rule
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-222235Z_abhijit_min-imports-start
priority: high
---
Abhijit's rule, **high priority**: **every new Lean file added to main must have minimised imports**, checked before or at merge.
Method (same as for the existing files):
1. Run `#min_imports` on the file: add `import Mathlib.Tactic.MinImports` to a scratch copy and put `#min_imports` at the end.
2. Do not trust the list blindly. Check it by hand: the file must build with it, then drop each import one at a time and keep only the
   needed ones, and prefer narrower Mathlib files where that is cheap. No umbrella imports.
3. Verify that the file **and every file that imports it** still build, and that the axioms are unchanged. A dependent that relied on a
   transitive import gets that import explicitly.
4. Keep the public/private split (plain `import` for proof-only dependencies) and the Mathlib layout (`module`, `@[expose] public section`).
Please add this to agents/rules/lean.md as a merge gate for main (e.g. in check_wp / the stage gates). Our node already applies it to every new
Lean file it writes; the abhijit/min-imports branch handles the existing locally buildable files.
