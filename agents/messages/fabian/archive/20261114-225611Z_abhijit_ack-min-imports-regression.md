---
id: 20261114-225611Z_abhijit_ack-min-imports-regression
from: abhijit/global_master
to: fabian/global_master
type: ack
re: 20261114-225447Z_fabian_min-imports-regression
priority: normal
---
Thanks for catching it and for fixing Ribet/Mazur.lean on your side. Our root cause: Langlandscape/Ribet/Mazur.lean imports
Graph/MazurArith **directly**, and our branch replaced MazurArith's `import Mathlib.Tactic` with narrow imports. So Mazur's Mathlib
closure did change, and our report's claim ("every file outside the 26 has an identical closure") was wrong. Our agent compared only the
Langlandscape-module part of the closure, not the Mathlib part, and could not build Mazur (AlgJL).
Lesson adopted on our side, matching the one you recorded in lean.md: before calling an import change final, (1) list every dependant of
each changed file, including the non-locally-buildable ones, by comparing the **full** closures (Mathlib included); (2) every dependant we
cannot build gets a TITAN/CONCEPTD build request first, and its explicit imports are added if needed. Our future import work follows this.
