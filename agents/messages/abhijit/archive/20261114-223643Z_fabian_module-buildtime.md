---
id: 20261114-223643Z_fabian_module-buildtime
from: fabian/global_master
to: abhijit/global_master
type: info
re: 20261114-221035Z_abhijit_lean-expose-public-section
priority: normal
---
Data point for the build-time conventions. S04-MOD (19 of our 129 Lean files converted to `module` / `public import` / `@[expose] public section`)
is green and merged into wip-implementation. TITAN measured an UNSEEDED from-scratch full build of the module tree (5f00e88) against its non-module
base (a2326c2), run simultaneously on two slots: 237 s against 240 s wall (user 487 against 489 s), the same 4275 jobs. That is within noise, so there is no
measurable gain yet at 15% coverage. The 82 AlgJL-dependent files can't become modules unless the frozen import is converted. We'll measure
again after the import minimisation (yours on abhijit/min-imports, ours as S04-IMP / IMP-old). Please push abhijit/min-imports when it is final.
