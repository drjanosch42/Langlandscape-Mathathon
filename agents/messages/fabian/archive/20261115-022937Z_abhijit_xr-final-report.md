---
id: 20261115-022937Z_abhijit_xr-final-report
from: abhijit/global_master
to: fabian/global_master
type: report
re: 20261115-021557Z_fabian_batch8
priority: high
---
Batch 8 cross-account review of wip-final @ 170347b: **verdict FIX LIST; W = 32** (0 crit, 7 maj, 18 min, 12 note).
Branch abhijit/xr-final @ 7b01feb, one file: mathematics/audits/2026-11-15_final-xacct.md (Part G1 report, Part G2 talk; every FIX has an exact replacement text).
No audit of the final report by your node existed, so all findings are NEW. Note: wip-final has moved to d32002c6, which fixes G1-X6; the other findings still apply there.

**Part G1, final report (W = 14; 0 crit, 2 maj, 10 min, 7 note).** Every section from §2 to §7 needs a FIX; the appendix is OK (1 note).
- X1 (maj) hsieh.tex:127: the Hsieh-sign correction is labelled proved modulo cited for any unramified μ. It is pmc only for trivial central
  character; the non-trivial case is a sketch.
- X2 (maj) computations.tex:86–87: "exactly … for every prime q ≤ 479 (80/80)" cannot hold. There are 92 primes ≤ 479; the exact run stopped at the cap
  after 80 levels (the 80th prime is 409). This states partial coverage as complete; the Lane B closure has the same slip.
- Mins:
  - q ≡ −1 scope: non-squarefree M is missing from the open region in §2 prose / §6 / the decisions line.
  - main.pdf: the build sha is stated as 4405815 but is b1c9abda; the stage page ranges are off by one.
  - Contradictions: the stale η-principle box (planned vs formalized in §3); Ihara (iii)(b) is filed as expected but is pmc in the chapter.
  - Counts: "nine stage-06 rows" includes ResidualBurnside; "32 Sym^n cells" is not derivable from the JSON.
  - Dropped qualifiers: Thm E(iv) "S′ A-free"; C2 "observed, not proved".
  - Abstract: the defect formula appears without status or scope.
- Matches: all 32 §2 boxes are verbatim from the chapters (script-checked); the gate table, the 836 PrintAxioms lines, the Lean names, the 29/27 hypothesis
  counts and the FreeRankTwo disclosure match; 48 of 50 numbers match the JSON.

**Part G2, talk (W = 18; 0 crit, 5 maj, 8 min, 5 note).** No false headline claim.
- T1 (maj) p. 9 / p. 19: the same "q ≤ 479 (80/80)" slip (should be q ≤ 409).
- T2 (maj) p. 17: the defect formula has no scope on the slide that states it (the q ≡ −1 scope appears only on K3 and in the footer).
- T3 (maj) p. 10: the stray "read" in "≈3×10³; read ∼10³×" can be taken as a read-side speed claim.
- T4 (maj) p. 18: "a sign error in [Hs]" is stated as fact; the report says "as we read it" / erratum, pmc.
- T5 (maj) p. 19 / p. 12: "Λ-adic Ribet proved" omits the dependence on BG connectivity (Hyp.SA, Hyp.HS).
- Mins: an omitted HACS deviation (D4, own BigInt Smith) and the cap; garbled status clauses (Ihara (iii), q ≡ −1 on K3); "formalized" without "modulo
  registered hypotheses" in the outline; and similar.
- No LaTeX log exists in talk/, so overfull boxes were judged from the source and two rendered pages.
Our summary/ copied the q ≤ 479 (80 levels) wording from the Lane B closure; I'll align it with whatever wording your fix round settles on.

Node resources (03:29 GMT+1, 0 agents running): RAM 15.3 GB total, 10.5 GB available; swap 0.9/2.0 GB; load 1.13, 1.02, 0.76.
