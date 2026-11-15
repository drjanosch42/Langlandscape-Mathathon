# Resolution of the Muse audit of stage-06.md

Reviser: Sonnet, 2026-11-14. Each finding checked against `stage-06.md`, `staged/stage-06-integral-defect.tex`, `OVERVIEW.md`,
`stage-04.md`, `stage-05.md`. WP ids unchanged (stage-05 names for Lemma D untouched). Verdicts: C confirmed, P partial, R rejected.

| finding | Muse sev. | verdict | own sev. | action |
|---|---|---|---|---|
| F1 inputs not labels | major | P | minor | brace shorthands and `tex L1`/`KO §3` replaced by literal labels in M1, M2, M3, M5, L1, L9b, L13, C1; WP-dep mentions (S03-C1, S01-C4) marked as such; bibliographic sources are in the tex, not labels |
| F2 `Gorenstein.lean` ownership | minor | C | minor | S06-L1 declared sole owner/creator (§0); S04-L10 only imports (see R1) |
| F3 L6 conditional dep | minor | C | minor | `Defect/Galois.lean` moved from L6 to L8 (L8 deps += L6); L6 deps = L1 only; DAG edge `L6->L8` added; L6 45/6, L8 75/10 |
| F4 L8 bundles 9 files | minor | P | minor | one WP kept (statements only, one file per `Hyp`), estimate 60 -> 75; no split |
| F5 label shorthands | major | P | minor | expanded; `§ss:s06-ca` typo fixed to `ss:s06-ca`; all labels exist in the tex (checked) |
| F6 external WP ids unverifiable | minor | R | - | all exist: S01-{M0,X1,T0,C0,H0,C4,L13}, S03-{C1,C5}, S04-L9 (grep of stage-01/03/04.md) |
| F7 brace labels | minor | P | minor | same as F5 |
| F8 missing DAG edges | critical | P | minor | added `L8->L6` (via F3), `M1->T1`, `M3->T2`, `C2->T2` (talk claims must be traceable to maths/results); rejected `M7->C3`, `M7->L14`, `M4->L6b`, `M1->L10`, `L2->C1`, `L4->T1` hard (statements exist in tex, OVERVIEW §6 interface rule; L4->T1 kept soft) |
| F9 shorthand edges / waves | major | P | minor | `{M1..}->M9` and `{L1..L10}->L11` expanded; waves unchanged (M-WPs are in W0, M6 in W1 consistent with `M5->M6`) |
| F10 critical path ties | major | P | minor | length 470 right; tie `L5`/`L9a` stated, slacks recomputed (L2 45, L6->L8 chain 45, L7 ~135) |
| F11 gate build wall | minor | P | minor | gate = acceptance re-run incl. lbuild (8-12 min), stated; 10 min/gate kept |
| F12 TEXCHK not mechanical | major | R | - | TEXCHK is defined in stage-02 as latexmk exit 0, no undefined refs, labels present; now spelled out inline in §0 |
| F13 M6 verdict subjective | major | P | minor | four-item checklist with KO quotes added to acceptance; Fable sign-off stays (it is a review WP) |
| F14 C3 "mismatch = finding" | major | P | minor | split acceptance: mechanical part (exit 0, provenance, finite ranks, k = 12 row) gating; comparison with prediction recorded, not gating (a prediction is not an oracle for k >= p, \stexp) |
| F15 M7/M9/L12/H1 non-mechanical | major | P | minor | L12 now also re-runs `PrintAxioms` rows; M9/M-audits are review WPs by design (named reviewer); H1 seed value is gated/optional |
| F16 LCHK expansion / axioms | minor | R | - | LCHK is defined in §0 (and stage-02); `#print axioms` for L3, L4, L9a, L9b is in L11 |
| F17 C5 "unit-equivalent" vague | minor | C | minor | explicit assert: `v_p` of Gram-determinant ratio `= 0` |
| F18 M7 opus too strong | major | R | - | (b) needs Ihara + Dia89, \stexp parts; off critical path, opus kept |
| F19 M1 routine | minor | R | - | proofs are complete in the tex, M1 is write-up |
| F20 L5 routine vs opus | minor | C | minor | L5 difficulty -> hard (Mathlib gap, see F28) |
| F21 L14 | minor | R | - | Muse itself reports no defect |
| F22 waves exceed 3 agents | critical | R | - | waves are ready sets, not concurrency; limit is per coordinator and already stated ("worker-bound"); clarifying sentence added (priority order, background work shares Lean slots) |
| F23 build slots / V | major | R | - | CommAlg is Mathlib-only, imports no GL2TF/vendor, so the ~25 min V first build does not apply; slot sharing note added with F22 |
| F24 TITAN tag | minor | R | - | "TITAN cand." is the OVERVIEW §4 convention; job id assigned by the global master at dispatch |
| F25 Gorenstein encoding unsound for non-local S | critical | R | - | tex definition is `S^∨` free of rank one over `S`; `IsGorenstein := ∃ ℓ` bijective is that (Muse's `ℓ = (1,0)` is just not a trace; `(1,1)` is); `A x A` is Gorenstein, no problem |
| F26 torsion-freeness missing | major | P | minor | not a counterexample to the plan but a real gap in the field list: `NewOldData` now lists all `lem:s06-D` hypotheses as fields (S finite free, S/a, S/b torsion-free, a ⊓ b = ⊥, encoding (iii)) |
| F27 Thm E(iv) hypothesis | major | P | minor | tex (iv) implicitly needs `S'` finite free (true under D(c)); L4 states (iv) with `Module.Free A S'` explicit; Muse's reading (D(c) hypothesis) is the right cause |
| F28 Nakayama over semilocal | major | P | minor | Mathlib Nakayama needs `𝔪_A S ≤ jacobson ⊥` for finite `S` over local `A`: made an explicit L5 sub-lemma; L5 -> hard (F20); the claimed obstruction otherwise is wrong |
| F29 Hsieh weights acceptance | major | P | minor | same fix as F17; `B_N`/Atkin-Lehner twist is not part of the tex claim; `p = 2` irrelevant (p >= 5) |
| F30 `⊔` notation | minor | R | - | `algebraMap A S c ∈ 𝔞 ⊔ 𝔟` typechecks (`Ideal S` membership) |
| F31 `δ` integrality | minor | R | - | `q` is a unit in `ℤ_p`, so `q^{2-k} ∈ ℤ_p^×`; note added to C3 |
| F32 EXPERIMENT_PROTOCOL | minor | R | - | not a defect of the plan; `runs/s06.md` is already named in §5 |

Counts of Muse findings (32): C = F2, F3, F17, F20 = 4; P = F1, F4, F5, F7, F8, F9, F10, F11, F13, F14, F15, F26, F27, F28, F29 = 15; R = F6, F12, F16, F18, F19, F21, F22, F23, F24, F25, F30, F31, F32 = 13.
**C 4 / P 15 / R 13.** Own severity: critical 0, major 0, minor 23 (19 acted Muse findings plus R1-R4); Muse's critical F8 is P/minor, F22 and F25 rejected.

## Extra findings

- **R1 (minor, cross-stage mismatch with `stage-04.md`).** S04-L10 says "`congruenceIdeal`/`IsGorenstein` shared with stage 06 (defined here if 04 runs first)" and lists deps only `S01-X1`; stage 06 makes S06-L1 the sole owner of `CommAlg/Gorenstein.lean`. Stage-04 reviser: S04-L10 should depend on S06-L1 (or stub its signatures) and not define them. Other checks: `Hyp.HsiehGor` exists in S04-L9 as assumed (abstract Hecke data `T`, `M`, `λ`; `stage-04.md` l. 31, 34); `Hyp.HidaControl` is registered there as the weight-k control, so `Hyp.HidaControlGL2` is required and stage-04 does not mention it (fine). Stage 06 does **not** use `Hyp.HsiehEta` in Lean (documented in §0).
- **R2 (minor).** Stray `;` and a separate-cell glitch in the L6 row after the edit; fixed. Header sentence on the 05/06 seam updated: names checked against `stage-05.md` §0 (match).
- **R3 (minor).** Throughput note: L6 -15 / L8 +15 leaves the total unchanged; critical-path text updated (tie, slacks).
- **R4 (minor).** Risk 7 text updated from "must be confirmed" to "checked against current stage-04.md" plus the open S04-L10 ownership point.
