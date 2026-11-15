# Resolution of the Muse audit of stage 03 (ribet-ihara)

Verification: all computations re-derived by hand (Smith form of the (2,2,2) example, the class-number linear system, the table T1 values for q=11,23,37,101,131, the Voight class-number list); Voight Thm 11.5.14, Ed91 Thm 1 and Ri90 p.449 checked in the PDFs (pdftotext / OCR).

| F | Title | Verdict | Reason | Change |
|---|---|---|---|---|
| F1 | two-vertex formula | REJECTED (no defect claimed; claim correct) | Order 12 and Z/2×Z/6 for w=(2,2,2) re-derived (Smith d=1,2,6). | no change |
| F2 | cyclicity lemma | REJECTED (no defect; correct) | λ well defined, image = gcd(W/w_e)Z/n; pairwise coprime ⇒ gcd 1. | no change |
| F3 | elliptic classes, unit-group classification | CONFIRMED (presentational gap) | The classification step was uncited. Voight Thm 11.5.14 (p.176) gives the list C2,C4,C6,Q8,2D6,2T; Q8 ⇒ B=(-1,-1) (disc 2), 2D6 ⇒ B=(-3,-1) (disc 3, Hilbert symbol), 2T ⊃ Q8. Muse's suggested "Ch. 17" is not the right place. Also the old proof's "non-abelian ⇒ contains Q8 or 2D6" is now replaced by the direct list. | Lemma s03-elliptic proof sketch rewritten with citation; bib/stage-03.bib Vo note |
| F4 | Mazur check | REJECTED (no defect; correct) | num((q-1)/12) = (q-1)/gcd(q-1,12) re-derived; table values all check. | no change |
| F5 | conventions C2–C3 | REJECTED (no defect; correct) | |Γ_x|=2w_x when -1∈U, mass formula in w-form re-derived. | no change |
| F6 | Φ Eisenstein | PARTIALLY CONFIRMED | Claimed "major gap" is not one (cited theorem, labelled \stcited). Only the optional remark is valid: Ed91 Th.1 assumes p>3 (verified in the PDF), which the stage did not mention. | Prop s03-phieis: sentence on p>3 and range of validity |
| F7 | bipartite lemma / Ribet thm | REJECTED (no defect; correct) | Sign remark and connectivity-only input re-checked. | no change |
| F8 | Hecke action on H_0 | PARTIALLY CONFIRMED | Muse says surjectivity of ε needs τ surjective: false. Taking f_0 supported at one class with Γ_x-averaged value gives ε=[τ(x)]v (Γ_x⊂U^1_p), so no condition on τ is needed. But the sketch did not contain the surjectivity argument. Exponent +1 and the rest agree. | Proof strategy, Thm s03-iharaH0 (a): surjectivity sentence added |
| F9 | Eisenstein support, T6 | REJECTED (no defect; correct) | Irreducibility of Sym^r F_p^2 for 0≤r≤p-1, Nakayama, unipotent coinvariants nonzero: all fine. | no change |
| F10 | references | REJECTED (no defect) | Spot-checked Vo p.415/479/543, Ed91 Th.1, Ri90 p.449; consistent. | no change |
| F11 | interfaces vs SPLIT | REJECTED (no defect) | Deviations D1–D4 already documented; nothing to change. | no change |
| F12 | Lean/HACS feasibility | REJECTED (no defect) | Predicted numbers checked by hand; no change needed. | no change |

Counts: total 12; confirmed 1 (major F3, presentational); partially confirmed 2 (F6 major, F8 major, both only in a minor part); rejected 9 (all reported "no fix"; none was a real defect).
Severity breakdown of the non-rejected: major 3 (F3, F6, F8), minor 0. No interface changes; seam items (factor-2 hypothesis C3, amended if:s02-indef import, Ihara (iii) exponent +1 with full-density hypothesis) preserved.
Overall judgement: the audit found no mathematical error; its useful content is the request for a citation of the unit-group classification, and its stated "fixes" for F3 (wrong chapter) and F8 (wrong necessary condition) were partly incorrect.
