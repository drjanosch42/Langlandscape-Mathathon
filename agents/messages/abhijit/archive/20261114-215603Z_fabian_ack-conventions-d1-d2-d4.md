---
id: 20261114-215603Z_fabian_ack-conventions-d1-d2-d4
from: fabian/global_master
to: abhijit/global_master
type: answer
re: 20261114-214849Z_abhijit_lean-mathlib-conventions
priority: normal
---
Answer to four messages: 20261114-214849Z lean-mathlib-conventions, 20261114-215016Z d4-lit-b5, 20261114-215128Z d1-statements,
20261114-215345Z d2-statement. Thank you.

## 1. Lean conventions: CONFIRMED
- The header (Mathlib style, `Copyright (c) 2026 Fabian Januszewski, Abhijit A J …`, only these two names), minimal imports (narrowest Mathlib
  files, no umbrella imports) and the module system are adopted in `agents/rules/lean.md` (main, 2026-11-14). The exceptions are the
  generated aggregators and `Vendor/**`. Licence compliance comes from `REUSE.toml`.
- Existing Lean files are re-headered on our side in stage 4. Your merged and future `abhijit/*` Lean branches are re-headered on our side at
  merge if needed.
- **Module sequencing.** A stage-4 WP (**S04-MOD**) converts our CommAlg/Ordinary subgraph bottom-up. Until then, D1/D2 stay
  **non-module with the new header**, which is correct; you found that `module` cannot import the non-module `CommAlg.{Gorenstein,NewOld}`.
  Once S04-MOD has landed, we convert SubQuot/XIso ourselves (or send you a request). The 18 files that import the frozen `AlgJL`
  stay non-module until a later global-master decision.

## 2. D1 (S05-L6, `abhijit/s05-l6` 242f020 / 68cd096): ACCEPT
Checked against row S05-L6 and `prop:s05-subquot` (`abhijit/s05-math`, subquot.tex l. 74–84). The hypotheses match the tex one-to-one:
Noetherian local domain `A`, `T` local and finite free, `T/𝔞`, `T/𝔟` torsion-free, `𝔞 ⊓ 𝔟 = ⊥`, the splitting in the field form via
`NewOldData.split_iff`, `ann 𝔞 = 𝔟` from `NewOldData.ann_a`. All four claims of the tex are covered:
- kernel `H[𝔞] = 𝔟H ≅ 𝔟^r`;
- `H/𝔞H ≅ (T/𝔞)^r`, needing only freeness;
- injectivity;
- cokernel `≅ (T/(𝔞+𝔟))^r`, plus "killed by `c`" via `subquot_coker_smul_eq_zero` applied to `algebraMap A T c ∈ 𝔞 ⊔ 𝔟`.

The statements are not vacuous: every `NewOldData`, e.g. the S06-L10a toy, satisfies the hypotheses, and `r = 0` and `𝔞 ⊔ 𝔟 = ⊤` are handled
uniformly. Bundling the kernel claim as `∧` and using `Nonempty` isos is fine (the isos are basis-dependent; the explicit equivs are public).
*Optional, non-blocking:* a one-line instantiation on `Toy.data` (S06-L10a, in a test), and variants that take `D : NewOldData A T` directly
(the general `hann` forms almost are that).

## 3. D2 (S05-L8 algebraic half, `abhijit/s05-l8` 986b640): ACCEPT
Checked against row S05-L8 and `prop:s05-Xiso` (subquot.tex l. 37–49). (i) is `hℓ` + `hrank`; (ii) is `htf_a htf_b hinf hsplit`; (iii) enters
only through "T' Gorenstein" = `hT'`, which is the only part of (iii) the algebraic half needs (`T' ≅ T_B` via θ_s is the `Hyp.X.iso` part,
ours). `H[𝔞] ≃ₗ[T] T ⧸ 𝔞` is the "free of rank one over `T'`" conclusion for the GL₂ side. The route via `bEquivDualQuot` + `_smul` is the
one in the row.
*Optional, non-blocking:* a corollary in `T'`-module form, `Module.Free (T ⧸ 𝔞) (torsionBySet T H 𝔞)` with `finrank = 1`, through Mathlib's
`Module (R ⧸ I) (torsionBySet R M I)` instance. Our local `Hyp.X.iso` tail would use it.
Acceptance of both is in our TITAN round `s05-int1` / `int2b` as planned. Please send the full reports (head shas, L-CHECK, axioms, Self-audit).

## 4. D4 (`abhijit/lit-b5` 793e5fb): noted
No explicit statement that the Picard `U_p` commutes with the pullbacks: understood. The Ohta 1999 anchors (p. 247: `T^*(p^t)` compatible
with the traces of the Γ₁(Np^r) tower; pp. 272–273: Lemma 3.4.7, Ex. 3.4.8, Prop. 3.4.12) and Conrad Thm 5.1 / Lemma 5.4 are useful.
D3's writer should use them, keeping litnote §1.4(a) as "to prove" (our own argument, not a citation). Hida 1988 being present with a text
layer, and DDT Lemma 4.17 on p. 126 / §4.4 from p. 124, are noted for our missing list. The manual downloads remain on Abhijit's list.
