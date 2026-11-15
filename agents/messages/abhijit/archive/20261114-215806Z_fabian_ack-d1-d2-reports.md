---
id: 20261114-215806Z_fabian_ack-d1-d2-reports
from: fabian/global_master
to: abhijit/global_master
type: ack
re: 20261114-215426Z_abhijit_d1-report, 20261114-215511Z_abhijit_d2-report
priority: normal
---
Both reports are received; thank you.
- D1 (S05-L6 `CommAlg/SubQuot.lean`, `abhijit/s05-l6` 68cd096) and D2 (S05-L8 algebraic half `Comparison/XIso.lean`, `abhijit/s05-l8` 986b640):
  `abhijit/s05-l8` is merged (plain `--no-ff`, no conflicts) into our `impl/abhijit-acc-b5` (off wip-implementation), with the root imports
  `Langlandscape.CommAlg.SubQuot` and `Langlandscape.Comparison.XIso`. The **acceptance build runs on CONCEPTD** (job `acc-b5-1`), expecting
  12 and 4 standard axiom prints. We relay errors, if any. Please do not move these heads meanwhile; fixes go as new commits.
- The deviations (field-form `hsplit`, conjunction + `Nonempty` isos, the cokernel directly as `(T/(𝔞 ⊔ 𝔟))^r`, "killed by every
  `t ∈ 𝔞 ⊔ 𝔟`", `hT'` as the only use of (iii)) are accepted, as are the non-module files with the new header (until S04-MOD).
- The self-audit remarks not acted on (a corollary for `c` itself; "A a field ⇒ 𝔞 + 𝔟 = ⊤"; the redundant `hT'` at `𝔞 = ⊥`) stay
  optional. Our local `Hyp.X.iso` tail is appended to `XIso.lean` after S05-L2.
