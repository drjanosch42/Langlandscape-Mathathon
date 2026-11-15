<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Audit: talk frame "Three lanes in parallel" (talk/slides/f15b-lanes.tex, frame 17/19), 2026-11-15
Checked against chapters/s00/computing.tex, submission/src/hacs.tex, chapters/s06/s06-m3.tex thm:s06-defect, talk f10-defect.tex, counts.tex.
- Defect formula: hypotheses (H0)-(H2), (P), (H0^-) or (Lev) and the open case (q = -1 mod p, rho-bar unramified at q, outside (Lev)) agree with thm:s06-defect and frame 10. OK.
- Lean: 950 audited, 29 registered, 2 discharged + 1 conditionally (counts.tex macros = computing.tex). OK.
- HACS A 66/66, signs 8/8; B q <= 600 at l >= 5, first 80 primes q <= 409 (capped), factor 37 at D = 13, k = 8; C 210 cells, census 0 disagreements on computed blocks, 120 undetermined; all "computed", no "certified". OK.
- MAJOR, fixed: "Lean statements match the tex" overstated (the Lean table records differences; abstract settings, JL schematic). Now: "each Lean declaration is named next to its tex statement, differences recorded (Lean table)".
- MAJOR, fixed: "tree/Ribet/Ihara maps 288/288" did not say what 288/288 measures. Now: "tree quotients (Ribet/Ihara maps) reproduce the stage-02/03 values on 288/288 cells".
- Minor, not changed: "Mazur's module" abbreviates "Eisenstein congruence module of order num((q-1)/12), as Mazur predicts"; "(Lev)" on the frame is not split into M = 1, (F1), (F1') (frame 10 does this).
- Bottom line: agrees with computing.tex ("Three lanes in parallel") after the first fix.
- Build: talk/main.pdf rebuilt, rc 0, 0 overfull, 19 frames; frame 17 inspected visually, no overflow.
Verdict: PASS after two major fixes; no critical finding.
