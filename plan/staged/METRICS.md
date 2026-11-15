# METRICS — P1 staged plan (2026-11-14)

Wall times are measured from the task notifications and `date` stamps; Muse audit times come from `muse_audit.sh`.
Audit: `opencode run --model openmathos/meta/muse-spark-open --auto --file stage.tex --file SPLIT.md --file stage.bib`.
Counts are C/P/R = confirmed / partially confirmed / rejected (from `audits/stage-NN-resolution.md`). Severity counts are crit/major/minor, as Muse assigned them.

| Stage | Draft (Opus) | Draft commit | Muse audit | Findings (crit/maj/min) | C / P / R | Revision | Reviser | Rev. commit |
|---|---|---|---|---|---|---|---|---|
| 01 quaternion-foundations | 17.8 min | 3b64f9b | 64 s | 8 (0/3/5) | 2 / 4 / 2 | ~1.5 min | Sonnet (run by master) | c946d7b |
| 02 tree-quotients | 18.2 min | 9199e24 | 51 s | 15 (0/7/8) | 2 / 4 / 9 | ≤ ~2 min (unreliable) | Sonnet (run by master) | d4d252f |
| 03 ribet-ihara | 22.0 min + 0.7 min seam fix | aac7bc3, e189e43 | 59 s | 12 (0/3/9) | 1 / 2 / 9 | ~2 min | Sonnet (run by master) | ea1c72a |
| 04 lambda-adic | 14.1 min | cee04eb | 57 s | 13 (0/7/6) | 2 / 4 / 7 | 4.9 min | Opus | cded11a |
| 05 comparison-hypothesis | 14.5 min | bff51eb | 59 s | 12 (0/8/4) | 0 / 6 / 6 | 8.1 min | Opus | 24bfabe |
| 06 integral-defect | 15.5 min | f6f75c0 | 26 s | 10 (1/4/5) | 0 / 2 / 8 | 3.7 min | Opus | 2c2a967 |
| **Total** | | | **~5.3 min** | **70 (1/32/37)** | **7 / 22 / 41** | | | |

Other phases:
- Coarse split (SPLIT.md, preamble, main.tex skeleton): one Opus helper, 4.4 min, 2753da8.
- Integration: a Sonnet worker merged the bib and macros but stalled after ~12:10 without committing, and was stopped at 12:50 (≈ 40 min lost). The plan master finished it: it fixed a bare-math bib note that broke the bibliography (`Gamma_{N,x}` in Hsieh's note) and committed in 1f3e48b. latexmk exit code 0, 61 pages.
- End to end: split start 11:20 → last revision 12:07 (≈ 47 min). The integration stall adds ~40 min.
- Drafting ran at ≤ 3 concurrent Opus drafters. Stages 04–06 were queued and started when slots freed up.

## Observations on Muse Spark Open
- **Usefulness rate:** 7/70 findings (10 %) were confirmed in full, and 29/70 (41 %) were at least partially confirmed. 41/70 (59 %) were rejected.
- **Severity inflation:** Muse labelled 33 findings critical or major. For stage 02 the reviser judged all 15 to be minor or wording-level, against Muse's 7 major. The single "critical" finding (stage 06, F5) was an endorsement of the draft, not a defect.
- **Endorsement-style findings:** many findings restate that the draft is correct, with "Fix: none" (most of stage 06; F13–F15 in stage 02). They inflate the counts and contain no actionable content.
- **Wrong suggested fixes:** in stage 01 F3 the failing case and the factor were wrong, and it claimed [K_s:K_{s+1}] = p³ where the correct index is p². In stage 04 F8 the proposed Mittag-Leffler fix was wrong. In stage 04 F11 Muse endorsed a factor-2 note that Hsieh (4.1) contradicts.
- **Wrong correctness claims:** in stage 05 every correctness claim was wrong, mixing up the sign with the exponent, or using S_ℓ = ⟨ℓ⟩ instead of ⟨ℓ⟩⁻¹.
- **Real value:** a few genuine gaps were found. Stage 05 F7: Prop. Xiso needs the Gorenstein property. Stage 04 F9: missing interface imports. Stage 03 F3: the unit-group citation. Revisers also found defects while checking findings that Muse itself had not flagged (stage 06: an internal contradiction about (H0⁻)).
- **Cost and speed:** about 1 min per audit (26–64 s) against a 15–22 min Opus draft, so very cheap. The token counts in `audit_metrics.log` record only the last step (≈ 40–64k cached input) and understate the true usage.
- **Verdict:** Muse is useful as a cheap first-pass checklist, but only behind a verifying reviser. Its severity labels and suggested fixes should not be trusted.
