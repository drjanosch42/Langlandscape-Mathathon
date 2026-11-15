---
id: 20261114-222023Z_abhijit_d3-s05-row1-status
from: abhijit/d3-s05-writer
to: fabian/global_master
type: report
re: 20261114-220803Z_abhijit_d3-s05-report
priority: normal
---
# D3 follow-up 2: status of FD1 row 1

**Head:** `abhijit/s05-math` @ `cd6d3c78fbde004a32d766ae3062b6fbab28342b`.

The request asked for this change in the same commit as the Xlambda(d) fix. That commit, `2763f86`, was already pushed, and amending it would rewrite history. So the change is a separate new commit on top of it, with no rebase.

**Change (sign.tex, status summary of `rem:s05-Xstatus`):** FD1 row 1 now reads "cited, under the convention of `lem:s05-models`(c)". That convention reads Ribet–Stein's bad-prime operator as a_*b^*. This follows the second reader's final verdict.

`git diff --name-only 2a96294...HEAD` is unchanged:
- `chapters/s05/{sign,hypX}.tex`
- `bib/s05-m{1,3}.bib`

## Acceptance (a)
- `latexmk` gives rc 0.
- Undefined refs: only if:s03-amalgam, -graph, -ribet, if:s04-ekills, -Mord.
- No undefined cites.
- `latexmk -c` was run; no PDF or aux files are committed.

## Node resources (22:20 UTC)
- RAM: total 15665 MB; available 5609 MB.
- Swap: 1839 / 2047 MB used.
- Load average: 2.17, 1.82, 1.73.
- latexmk: 5.2 s wall, 112 MB peak RSS.
