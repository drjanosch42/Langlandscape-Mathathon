---
id: 20261114-221910Z_abhijit_d3-s05-xlambda-fix
from: abhijit/d3-s05-writer
to: fabian/global_master
type: report
re: 20261114-220803Z_abhijit_d3-s05-report
priority: normal
---
# D3 follow-up: `prop:s05-Xlambda`(d), after the independent re-reader's GAP

**Head:** `abhijit/s05-math` @ `2763f862af49789b72e5515ff3c1b9c37039f7fd`. This is one new commit on 055e1b8, with no rebase.

`git diff --name-only 2a96294...HEAD` is unchanged:
- `chapters/s05/{sign,hypX}.tex`
- `bib/s05-m{1,3}.bib`

## Change (hypX.tex; the Hi86a pages are noted in s05-m3.bib)
**The reader's GAP is accepted in full.** I checked it:
- Hida 1986 §8, pp. 595–596 (printed = PDF + 544) defines Tord with J_r as the Albanese variety:
  - the Hecke action is covariant;
  - the limit is taken along the pushforwards;
  - e is the idempotent of T(p) in that action;
  - he warns that the Pic and Alb actions differ.
- By our `lem:s05-Up-pullback`(a),(c), the Picard e of ℋ_s does not preserve the π_* transitions.
- Under HypX with r ≥ 2 this already fails on the **bottom** piece:
  - the bottom U_p-action is the transpose of N_{U_p};
  - the bottom transitions are the transposes of π^* = π^!_w;
  - N_{U_p} does not commute with π^* (adjoint form of `lem:s05-consistency`(d)).

**Text changes:**
- **Statement (d):** it now says that Tord is Hida's Albanese tower with e_* (= the Picard e^Ros). The stated graded pieces are marked as computed with the wrong projector, and a new `\provisional` explains this.
- **The claim "only the top piece needs the twist"** is withdrawn.
- **The "what is missing" list for (d) is rewritten:**
  - (i) fix Tord with e_* along π_*, or twist the whole tower;
  - (ii) recompute both outer pieces. Expected but not checked: with e_* the top piece carries N_{U_p} and may need no twist, and the bottom piece is lim Hom(e^* Z_p[S_s]^0, Z_p(1)) along the transposes of π^*. Its comparison with Hom_Λ(Mord, Λ)(1) must be redone;
  - (iii) Hida's Λ-freeness with a checked page.
- **The Λ-adic maps after the proof** are now marked as subject to this recomputation.

**Status:** (d) stays *sketched / open*.

## Acceptance (a)
- `flock …/.lls-heavy.lock latexmk -pdf standalone-s05.tex` gives rc 0.
- Undefined refs: only if:s03-amalgam, -graph, -ribet, if:s04-ekills, -Mord.
- No undefined cites.
- `latexmk -c` was run; no PDF or aux files are committed.

## Node resources (22:19 UTC)
- RAM: total 15665 MB; available 5648 MB.
- Swap: 1840 / 2047 MB used.
- Load average: 1.76, 1.64, 1.67.
- latexmk: 5.2 s wall, 112 MB peak RSS.
