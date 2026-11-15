# Resolution of the global Fable seam audit (`audits/global-fable-seam.md`)

Coordinator: Claude Opus 5.5, 2026-11-14, branch `wip-plan`. Workers: Claude Sonnet 5.5 (high; stages 01–04) and
Claude Opus 5.5 (stages 05–06). The coordinator edited `preamble.tex` and `SPLIT.md`.

Every applied fix is **provisional**. Each change site carries a visible orange note `\provisional{F<n>[/D<m>]: …; before: …}`
(the macro is defined in `preamble.tex`). The note records the old wording. To revert a change, restore the "before"
text and delete the note. There are 80 notes in all: 01: 3, 02: 5, 03: 4, 04: 8, 05: 24, 06: 36.

Counts: **APPLIED 19, MODIFIED 1, NOT APPLIED 0.**

## Provisional human decisions (Fabian is away; the global master relayed them)
| D | Decision | Where |
|---|---|---|
| D1 | Hyp.X uses the Ribet–Stein conventions (μ_N-model, Picard functoriality), so Frob_q = qU_q | F1 |
| D2 | q ≡ −1 is restored in the defect theorem under the explicit hypothesis (Lev_M); M = 1 is the proved case. A visible note asks a second reader to check step 4 of audit issue 5 against Kim–Ota §3 ([KO, Thm 3.14]) before the talk claims it | F3 |
| D3 | Hsieh's sign JL(U_q) = −U_q is an erratum and is not imported | F6 |
| D4 | (Im) is kept, still flagged "probably superfluous". No text change | stage 06 `hyp:s06-H`, R4 |
| D5 | Hyp.SA and Hyp.HS stay registered hypotheses | F7 (Lean line) |
| D6 | Kim–Ota Cor. 5.4 is not cited beyond q ≢ 1. Neither stage cited it; one sentence saying so was added to the proof of `cor:s06-fixed` | stage 06 |

## Fixes
| F | Verdict | What was done |
|---|---|---|
| F1 (D1) | MODIFIED | The Setting of stage 05 now fixes the μ_N-model and Picard functoriality. The audit cites "Ribet–Stein §3" for the model, but the model is in Ribet–Stein §2.3.1.1, pp. 28–29 (checked), so that is the citation used. (X4) now says that σ_q = U_q⁻¹ and that the Frobenius permutation is Π_q⁻¹. `rem:s05-Xstatus` has the four-row table with its anchors, Ribet–Stein Lemma 3.17 and Conrad Thm 5.16 (both checked). Status: \stpmc at Γ_0-level, \stexp at Γ_1-level. Also updated: `prop:s05-sign`(a), Proof strategy 1, `if:s05-hypX`, Risk R4. |
| F2 | APPLIED | `lem:s06-decomp`(b) now says T″ ≅ T(M)_m via U_q ↦ α_q, and T″ = 0 if ρ̄ is ramified at q. The Chebotarev argument is deleted. These now agree with it: step (3) of `thm:s06-defect`, `prop:s06-betti`(b) (the extra factor is ≡ 1 − q, a unit), Proof strategy, M2, and Hyp.OldDecomp in L6. |
| F3 (D2) | APPLIED | (a) `rem:s06-minus1` no longer says the seed is wrong. (b) Hypothesis (Lev_M) is added, with M = 1 as the proved case. New `prop:s06-levM` gives the five-step proof, citing [KO, Thm 3.14, p. 12], and carries the second-reader note. That note also asks the reader to check the U_ℓ, ℓ \| M, because KO's Hecke algebra is the anemic one. (c) `thm:s06-defect` is stated under "(H0⁻) or (Lev_M)", \stpmc. (d) The conjectured v_ϖ(q+1) correction is deleted from the Decision, R2 and M5. H3 is now a validation with predicted difference 0, and its Hecke algebra must contain U_q. |
| F4 | APPLIED | `thm:s04-control`(b) now says that the whole module is dual to e·M(UK_1;V_k). The ω^{−(k−2)}-piece is dual to the Γ_0(p)-level module for k ≥ 2, and equals the level-U module for k ≥ 3 by p-stabilisation (\stexp). |
| F5 | APPLIED | Stage 05 has import blocks for `if:s02-quot` and `if:s02-coh` in stage 02's wording. `SPLIT.md` now reads "02 → 03, 04, 05", and the `if:s02-coh` entry has the full-strong-approximation caveat. |
| F6 (D3) | APPLIED | Stage 01: `thm:s01-lambdaJL` now has U_ℓ ↦ +Π_ℓ, and `ex:s01-Pi11` says "his operator is our Π_q". The open-points line in 01 is aligned (an extra edit). Stage 04: item 5 now says the sign is not imported. Stage 05: `rem:s05-hsieh` gives the verdict and its three reasons, and R3 is restated. T05-1 is kept as validation. Stage 06: (S7) is replaced. |
| F7 (D5) | APPLIED | `thm:s04-lambdaribet` and `if:s04-lambdaribet` now assume that BG(UU_s,q) is connected for all s ≥ 1. On the Lean track the theorem takes this, or Hyp.SA ∧ Hyp.HS, as an argument. |
| F8 | APPLIED | `def:s02-Mhom` now sums over Γ_x/±1. R4's "must fix" is replaced. |
| F9 | APPLIED | `if:s02-indef` has the normative Hecke-action sentence. Stage 03 (R3) refers to it. `thm:s03-iharaH0`(b) has a remark on the exponent: +1 cohomological, −1 homological. |
| F10 | APPLIED | Hsieh's weight is now w_x, and the factor 2 is against \|Γ_x\|. Changed in 05 `rem:s05-BN` (two sites), 06 (S1) and H2. |
| F11 | APPLIED | 05 now cites `if:s04-ekills`(d); its import block reads "(a)–(d)". |
| F12 | APPLIED | `prop:s05-subquot` no longer assumes T Gorenstein or T″ free; it uses Lemma D(a) only. The note after it, the interface and Proof strategy 4 are corrected. |
| F13 | APPLIED | `prop:s03-phieis` is \stproved for all q and all M with ℓ ∤ qM, with the four-step proof. Ri90 and Ed91 are kept as cross-references, and the "we do not claim" sentence is removed. 06 (S5) now says "resolved". |
| F14 | APPLIED | The stage 04 import block now has both amendments: the ℤ-version via BG, and the full-SA caveat for H_0. |
| F15 | APPLIED | The `if:s01-hecke` import blocks in 02–06 now read "T* = T_{g⁻¹}; T_ℓ is self-adjoint only at level U_0(M)". Stage 01's own export omits the word "only"; it was left as it is. |
| F16 | APPLIED | New interface `if:s06-lemD` (Lemma D (a)–(c)), exported by 06 and imported by 05. 05 cites Lemma D only through it. `SPLIT.md` records `if:s06-lemD` and `if:s06-defect`, and the stage-independence sentence is amended. |
| F17 | APPLIED | `def:s02-indef` gives both rank formulas only at a free level, with a warning for non-free levels. |
| F18 | APPLIED | 06 (S3) no longer uses T ↦ T*. It now says that B_N is Hecke-equivariant, so η^B is computed in T_B. |
| F19 | APPLIED | Every use of the amalgam for k ≥ p (T4 at k = 28, 44, 60, 124) is marked \stexp: after `prop:s06-betti`, in D1 and in H1. |
| F20 | APPLIED | The clause in stage 04 R2 is deleted. |

## Left open
- **D2 second reader.** Someone must check step 4 of `prop:s06-levM` against Kim–Ota §3, including how the U_ℓ, ℓ \| M, are matched with KO's anemic Hecke algebra.
- **D3, writing to Hsieh.** Writing to the author about the sign is still to be decided.
- **Fabian's review.** Every `\provisional` note awaits it.
- **F19.** If the T4 predictions are to become more than expectations, stage 03 must export an m-localised ordinary Mayer–Vietoris sequence for k ≥ p.

Compile: `latexmk -pdf main.tex` in `plan/staged`. No errors and no undefined references.
