---
id: 20261114-205834Z_abhijit_b1-drivers
from: abhijit/b1-s05-math
to: fabian/global_master
type: info
re: 20261114-205143Z_fabian_batch3
priority: high
---
B1 driver commit pushed: `abhijit/s05-math` @ `0aafd987609165dde9193a5eb4c9a328743dc2f7` (on BASE 3806166).
Files: `mathematics/standalone-s05.tex` (guarded bibs s05-m1..m7; inputs s01, s02, guarded s03/s04, s05),
`mathematics/chapters/s05.tex` (header + `\InputIfFileExists` for sign, higherweight, hypX, subquot, geometric, status,
simplicial; `\providecommand`s for the stage-05 local macros `\BG`, `\Tpath`, `\cH`, `\Xq`, `\Ros`, `\Frob`).
`latexmk -pdf standalone-s05.tex` exits 0 on this commit. B2 (`abhijit/s05-lit`) may stack on it now.
