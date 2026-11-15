# Stage 06 (integral-defect): resolution of the Muse audit

Reviser: Claude Opus 5.5. Start 12:04:22, end 12:07:27 (local time, 2026-11-14).
Input: `audits/stage-06-muse.md` (10 findings: 1 critical, 5 major, 4 minor). Every finding in this audit *endorses* the stage
file. The verdict below says whether the finding identifies a real defect: REJECTED = no defect (the endorsement was re-checked),
CONFIRMED / PARTIALLY CONFIRMED = a real issue, or part of one, which was fixed. I opened Kim–Ota (arXiv v4), Pollack–Weston (arXiv)
and the Hida 1986 OCR with pdftotext, and checked the interfaces word for word against `SPLIT.md`. Drafter deviations D1–D4 and seam
items S1–S7 are kept unchanged.

| F | Title | Verdict | Reason | Change |
|---|---|---|---|---|
| F1 | I_F Λ-free (H1) | REJECTED | No defect. Normal ⇒ (S2), so depth = dim = 2 and I_F is CM; a finite CM module over the regular local Λ of dimension 2 is free by Auslander–Buchsbaum. Re-derived. | no change |
| F2 | Hida Thm 3.1 / Cor 3.3 attribution | PARTIALLY CONFIRMED | Thm 3.1 and Cors 3.2–3.3 are on p. 250 (OCR checked). But the audit's suggested pointer "Cor 3.3 = old congruence ideal" exposed an imprecision. Hida's old ideal (Def. before Cor 3.3, (3.4a–d)) is the annihilator of the forms old at *any* divisor t>1 of the tame level. So it is only contained in our 𝔟 (q-old only), and equals it when no form in the 𝔪-part is old at a prime of M. | Lemma `lem:s06-decomp`, Inputs (b) |
| F3 | Lemma D(c) correction | REJECTED | No defect. Re-derived: S/𝔟 free ⇒ 𝔟 is an A-summand; the kernel of s ↦ ℓ(s·)\|_𝔟 is Ann 𝔟 = 𝔞 (𝔟 is an ideal, ℓ perfect); restriction S^∨→𝔟^∨ is onto. | no change |
| F4 | Thm E, two Gorenstein hypotheses | REJECTED | No defect. Re-derived (i)–(iv). Rank one of S'[λ'] is automatic from (Gor_S), because S_K[λ] lies in the S'_K factor. The Lean request (Hyp.HsiehGorenstein for both hypotheses) is already in L6. | no change |
| F5 (critical) | q ≡ −1 excluded, (H0⁻) | REJECTED | No defect; the endorsement is correct. Checked against the sources: KO Thm 1.1(6) (±1) p. 1; KO Thm 2.13 (only q≡1 excluded) p. 7; KO Prop 2.15(1) (primes in Σ⁻ not ≡ ±1) p. 8; KO Rem 5.5 and Prop 5.6 (Euler factors) p. 19; PW (CR)(2) (±1) p. 2. The seed's step (4) does claim "including q≡−1" (seed line 509). Rederived: L_q(ad⁰f,1)^{-1} = 1−q^{-2} for Steinberg f is a p-unit iff q≢±1. Also re-checked (c): St⊗χ and St⊗χη reduce alike mod p iff q≡−1, and both factors of δ lie in 𝔪. The T5 and H3 triples satisfy their stated congruences. | (wording fix below) |
| F6 | (P1)/(P2) and the control step | PARTIALLY CONFIRMED | No mathematical defect: at weight 2, the ordinary algebra of level Np contains the p-new (a_p=±1) forms, so (P2)'s extra condition is needed, as stated. The audit's Lean request is valid: L6 did not say what Hyp.HidaControl must cover. | Lean track L6 |
| F7 | Betti incarnation | REJECTED | No defect. Re-derived: δ matches the seed's matrix (q+1, −T_q; −q^{2−k}T_q, q+1); when q+1 is a unit the matrix is equivalent to diag(1, δ); only one sign factor can lie in 𝔪 when p∤2(q+1); in (c), O/λ'(𝔠) is a quotient of T'/𝔠, which gives ≤. | no change |
| F8 | Interfaces and seams | REJECTED | No defect. The imported interfaces were compared word for word with SPLIT.md lines 189–226 and match; if:s06-defect is documented as an addition (D4). | no change |
| F9 | Lean/HACS feasibility | REJECTED | No defect. L3 needs only "a saturated submodule of a free module over a PID is a summand" (quotient torsion-free ⇒ free), which Mathlib has. | no change |
| F10 | Bib and missing registry | REJECTED | No defect. The bib notes match: Ri84, MW86 and Böc07 are marked NOT in literature/, and the OCR caveat for Hi86b is honest. | no change |

**Reviser's additional fix (found while checking F5; not an audit finding).** The (H0⁻) item said it was "needed only for the
Galois half". That contradicts the remark after Prop. `prop:s06-galois` ("does not use (H0⁻)") and Remark `rem:s06-minus1`. It now reads:
needed only for Cor. `cor:s06-fixed` (hence for the equality in Thm `thm:s06-defect`) and for Prop. `prop:s06-betti`, not for the
inclusion of Prop. `prop:s06-galois`. Hypothesis `hyp:s06-H`, item (H0⁻). There are no interface changes.

Compile: private copy, `latexmk -f`. Stage 06 has no errors and no unresolved s06 references; the only LaTeX error comes from stage 05 (`\Mord_\m`).

Counts: total 10; confirmed 0; partially confirmed 2; rejected 8.

Overall: of little use. Every finding is an endorsement (several just paraphrase the stage file), and the "critical" F5 asserts no
defect. Its claims were correct where checked, but it missed the (H0⁻) wording inconsistency and the Hida old-ideal imprecision. Only its
suggested fixes for F2 and F6 led to small real improvements.
