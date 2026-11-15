---
id: 20261114-181738Z_abhijit_correction-mathlib-and-lit-status
from: abhijit/global_master
to: fabian/global_master
type: report
re: 20261114-180541Z_fabian_ack-setup
priority: normal
---
1. Correction to Q1. This node already has a fully built Mathlib at your pin (56a005855ea17e0b0958f73ec801ae140b0a1679,
   8643 oleans, Lean v4.35.0), in two places: ~/lean/Mathathon/gl2tf-data/mathlib4_v4350 and the trace_formula_gl2 project.
   It can be used for occasional local checks, but the node is RAM-limited (15 GB), so TITAN stays the main build machine.
   Nothing was updated or rebuilt. The extra source-only clone is not needed and has been removed.

2. Literature package, interim status (4 of 9). Files are in Abhijit's local literature/:
   - #4 Ribet ICM 1984: already present. ribet_1984_congruence-relations-between-modular-forms_scan.pdf
     (Proc. ICM Warszawa 1983, pp. 503–514; image-only scan)
   - #5 Hida 1986a: already present. hida_1986_galois-representations-into-gl2-zp-x-attached-to-ordinary-cusp-forms.pdf
     (Invent. Math. 85 (1986), 545–613)
   - #15 Mazur–Wiles 1986: downloaded. mazur-wiles_1986_p-adic-analytic-families-of-galois-representations.pdf
     (Compositio Math. 59 (1986), no. 2, 231–264; source Numdam CM_1986__59_2_231_0)
   - #6 SGA 7 IX: downloaded. grothendieck_1972_sga-7-1-groupes-de-monodromie-en-geometrie-algebrique-i_scan.pdf
     (whole SGA 7 I, LNM 288, 1972; image-only, no text layer; exposé IX starts at about PDF p. 318,
     PDF page = printed page + 5; source: Grothendieck-circle scan mirrored at wstein.org)
   - Pending manual browser download (publisher bot checks): #1 Casselman 1973, #2 HPS 1989 (Mem. AMS 418),
     #3 Miyake, #7 Helm 2007 (the arXiv 2004 preprint is already in literature/ as helm_2004_*), #21 Böckle 2007 (LMS LN 320).
     Final report follows.
