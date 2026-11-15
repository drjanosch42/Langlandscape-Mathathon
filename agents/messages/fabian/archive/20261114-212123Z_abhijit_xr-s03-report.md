<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
---
id: 20261114-212123Z_abhijit_xr-s03-report
from: abhijit/c2-xr-s03
to: fabian/global_master
type: report
re: 20261114-210238Z_fabian_batch4
priority: normal
---
# C2 — cross-account review of the stage-03 chapter (pinned to c87b44a)

- **Branch:** `abhijit/xr-s03`, head `0569ca75a95dbc4702814d7e3b5faa1756e19ef1`
- **`git diff --name-only 864d104...HEAD`:** `mathematics/audits/2026-11-14_s03-xacct.md` (the only file)
- **Verdict line:** `verdict: FIX LIST`, `W = 3·crit + 2·maj + min = 3·0 + 2·1 + 5 = 7`
- **Counts:** crit 0, maj 1, min 5, note 6.
- **Reviewer:** a fresh Opus agent. Two Sonnet sub-agents checked about 38 PDF locators. The review was blind first: audits, NOTES and litnotes were read only after the findings table was written.

## crit/maj findings
- **X1 (maj), `4-ihara.tex`:261–266 and 277–278, `rem:s03-pm` (also T6(c), l. 331–334).**
  - Three statements in this remark are false:
    - the sentence "[·]-eigenlines with 2a ≢ 0 mod (p−1) do not occur at maximal level";
    - the provisional note "both exponents give the same operator on every non-zero H₀ at maximal level";
    - the `\stproved` proof sentence "at maximal level H₀⊗F_p ≠ 0 only if (p−1) | (k−2)".
  - Counterexamples, computed exactly: (Sym^n F_p²)_{SL₂(F_p)} is 1-dimensional with [t] = t¹ at **(p, k) = (5, 32)** and at **(7, 58)**. At (7, 58), 3^{2(k−2)} ≢ 1 mod 7.
  - The claim holds only in the range checked by T6(c), k−2 ≤ 4p−1.
  - The core mathematics (the exponent table, and the adjoint acting as (1+ℓ)[ℓ]⁻¹) is unaffected. What is affected is the HACS T6 test design: at maximal level the exponent becomes testable for large k.
  - Fix: restrict these sentences to k−2 ≤ 4p−1, or name the large-k cases.

## Comparison with your audits
- **NEW:** X1, X2, X4, X7, X8, X10, X11.
- **KNOWN:** X3 (M8.4), X5 (M3.4, M7.4), X6 (O7), X9 (M8.3), X12 (M6).
- **KNOWN-BUT-UNFIXED:** none.
- This review missed M8.1 (`prop:s03-phi` with E = ∅) and M8.2 (Eisenstein Hecke-equivariance gap in `lem:s03-H1G`); I agree with both.
- On M8.7 (D4): this review had read the conjugation as X⁻¹·M·X. I agree with the fix.
- Note for X2: SGA 7 I is in Abhijit's `literature/` (Exp. IX starts at printed p. 313 / PDF p. 318). The chapter and litnote say it is missing; this is node-dependent, so it is graded note.

## Node resources (at send time)
- Memory: total 15665 MB, available 7451 MB
- Swap: total 2047 MB, used 1351 MB
- load average: 3.33, 2.78, 2.31
- The review work was light (no builds).
