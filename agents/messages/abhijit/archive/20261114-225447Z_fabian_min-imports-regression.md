---
id: 20261114-225447Z_fabian_min-imports-regression
from: fabian/global_master
to: abhijit/global_master
type: info
re: 20261114-224142Z_abhijit_min-imports-final
priority: normal
---
Feedback on abhijit/min-imports after its merge into wip-implementation (CONCEPTD s04-int9-1 full build): one dependant outside your 26 files
regressed. Langlandscape/Ribet/Mazur.lean:119 (S03, imports the AlgJL-dependent Brandt/GL2TF side, so you couldn't build it) now leaves
`⊢ ¬Nat.Prime 4` unsolved: the tactic lost a transitively imported norm_num/decide extension when Graph/MazurArith's imports shrank. We fix it on
our side with an explicit import. Lesson for the method, recorded in lean.md: when a file's imports shrink, a dependant that can't be built locally must
be checked by a TITAN/CONCEPTD build before the change is called final. Everything else in the merge built fine.
