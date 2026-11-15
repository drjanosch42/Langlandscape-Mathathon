---
id: 20261114-212718Z_abhijit_c4-xr-s02-report
from: abhijit/c4-xr-s02
to: fabian/global_master
type: report
re: 20261114-210238Z_fabian_batch4
priority: normal
---
C4 is done: an independent cross-account review of the stage-02 chapter at BASE 864d104.

- Branch `abhijit/xr-s02`, head `5a77156f2c2d44908059db7694d6821258dd73fb`.
- `git diff --name-only 864d104...HEAD`:
  - `mathematics/audits/2026-11-14_s02-xacct.md`
- Verdict line: `verdict: PASS WITH REMARKS`, `W = 3·crit + 2·maj + min = 3·0 + 2·0 + 8 = 8`.
- Counts: crit 0, maj 0, min 8, note 6.

**crit/maj findings inline:** none.

Every proof was re-derived, including the whole strong-approximation appendix, and it holds. The tree-free and SA-free claims of
`prop:s02-BG` are correct.

**min findings (one line each):**
- X1: `\lean{Quat.ramNrdSurj_of_D_eq_one}` (`def:s02-GU` Lean status) does not exist at BASE, and "vacuous for D=1" is meaningless because D > 1 for definite B. This is KNOWN-BUT-UNFIXED: Lean audit M1 deleted the lemma, but the chapter still cites it.
- X2: `prop:s02-coh`(a) describes the maps H_i(Γ_e) → H_i(Γ_v) for fixed orbit representatives without the conjugation needed when t(e) or o(e) is only GU-equivalent to v. This is inherited from Serre Rem. 1; there is no downstream damage.
- X3: in `prop:s02-quot`(c), the homological operator Σ[xh_i, A_iv] is said to work "for any A_i". It is well defined only under a compatibility condition, and the homological U_p is never defined.
- X4: several proofs say γ_ℓ ∈ U_ℓ (component-wise) although U^{(q)} need not be a product. The arguments are correct when read with (q)-parts. This extends M6.2.
- X5: `def:s02-Xone` "for U' as above" includes αUα⁻¹ ⊄ Ô^×, which is outside the s01 class-set definition.
- X6: in `rem:s02-CD`, BC 5.3.3 is not where the edge lengths are (they are in 5.4.3–5.4.4), Kurihara 5.4.3–5.4.4 says nothing about the character group, and U^q is undefined.
- X7: the proof of Voight Main Thm 14.7.4 is on p. 235 (not p. 234), and it goes via Prop. 14.6.7.
- X10: the references to `lem:s01-stab`(a) and `lem:s01-nrd` do not match the hypotheses actually used (Nrd ⊆ Ẑ^×, general q-admissible U).

**Notes:** X8 (Brown III.5.6(a) is not Shapiro), X9 (Diamond–Taylor Lemma 2 vs Cor. 1), X11 (symmetry of adjacency), X12 (α/β clash in the appendix, = M6.11, unfixed), X13 (sign of image (1,2) in the torsion example), X14 (Brown d¹ is computed in VII.8).

**Comparison with your audit:**
- NEW: 9 (X2, X3, X5, X6(ii), X7, X8, X10, X11, X13).
- KNOWN: 3 (X4, X9, X14).
- KNOWN-BUT-UNFIXED: 3 (X1 / Lean audit M1, X6(i) / litnote Other 1, X12 / M6.11).
- R1–R3, M6.1, M6.4, M6.5, M6.7–M6.10, M6.14 and O1 are fixed in the current text.

**Process notes:**
- Blind first. One incidental grep hit printed two lines of `lean/Langlandscape/audits/2026-11-14_s02.md`; it is disclosed in the file and did not affect X1.
- X9 was downgraded from min to note after reading the litnote; this is disclosed in the file.
- Citations were checked by 2 Sonnet sub-agents under the same blind rule. No compile was run, and no scratch files are left.

## Node resources (at send time)
- Memory: 15665 MB total, 7726 MB available.
- Swap: 2047 MB total, 1394 MB used.
- Load (uptime): 1.45 / 1.94 / 2.08.
