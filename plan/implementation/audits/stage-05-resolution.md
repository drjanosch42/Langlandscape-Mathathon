# Resolution of the Muse audit of `stage-05.md` (stage-05 reviser, 2026-11-14)

Muse findings checked independently against `stage-05.md`, `OVERVIEW.md`, `stage-02.md` §0, `stage-06.md`, `stage-01.md`, the tex.

| finding | Muse sev. | verdict | own sev. | action |
|---|---|---|---|---|
| F1 M4 lacks dep on Lemma D producer | Critical | partial | minor | maths WPs depend only on the existence of the statement (common.md); `lem:s06-D`/`if:s06-lemD` exist in the 06 tex. Added soft dep `S06-M1` (tex home of the label) to M4 and DAG. No hard edge. |
| F2 L6b deps is a disjunction | Major | confirmed | minor | deps now `S06-L3` (stub allowed; L6a only fallback); no `∨`. |
| F3 cited labels not in stage tex | Major | rejected | none | cross-stage `if:`/`prop:s01-*`/`lem:s06-D` labels exist in their own stage tex (grep: `prop:s01-relations`, `lem:s06-D`, `if:s06-lemD` present); importing by interface label is the SPLIT mechanism. |
| F4 acceptance abbreviations undefined / non-mechanical | Major | rejected | none | LCHK/TEXCHK/PYCHK are defined in `stage-02.md` §0 (and referenced as such); they include `latexmk` no-undefined-refs and lfile/pytest steps; M8 reviewer is named (Muse pre-pass then Fable). |
| F5 DAG inconsistencies (`M1->M6`, `S01-L3c->L1`, soft L2) | Major | partial | minor | `S01-L3c` is a real input of L1: added to L1 deps and DAG. `M1->M6` is stated soft in the text; added dashed to Mermaid. Soft S03-L3 edge for L2 is intentional (bridge only, stated), kept. |
| F6 resource limit violated (6 agents) | Major | rejected | none | OVERVIEW §4 limits are per coordinator (≤3 Claude subagents each); two coordinators are allowed, opencode jobs are not Claude agents; slots are node-wide and the plan already assigns slot 2. |
| F7 slack overstated | Minor | confirmed | minor | recomputed: L5 slack ≈ 2.2 h (not ≥ 3 h; Muse missed this), L6b ≈ 2.7 h after S06-L3, L8 ≈ 1.5 h. |
| F8 L9 puts aggregator edits in a WP | Major | rejected | none | L9 outputs say "aggregator edits (stage master)", same pattern as S06-L11/S01; workers only report one-line additions. |
| F9 `Utower`/`ZX` naming mismatch with stage-01 | Minor | rejected | none | `stage-01.md` uses exactly `Utower`, `ZX`, `Up`, `Tl Ul diamond PiEll` (checked). |
| F10 C2 needs `B_q` class sets confirmed | Minor | partial | minor | S01-C2 covers `U_1(N)` class sets; added explicit precondition `(N,pq)=1, p≥5` and that the used `(q,N)` are produced. |

## Extra findings
- **R1** (minor): Hyp table said "optional S05-L9" for the algebraic half of Xiso; it is S05-L8. Fixed.
- **R2** (minor): L5 deps column omitted `S01-L8b` (present in DAG and inputs). Added.
- **R3** (major, seam): stage-06 now owns Lemma D as S06-L3 (`CommAlg/NewOld.lean`, `NewOldData.ann_a/ann_b`, `bEquivDualQuot`) on S06-L1 (`NewOldData`, `IsGorensteinWith`, `IsGorenstein`, `ann`). Replaced all `S06-L(D)` placeholders; §0 ownership rewritten (stage 05 does not write Lemma D; L6a demoted to fallback with signatures identical to S06-L3, deps S06-L1); L6b/L8 deps and inputs rebound; waves, entry conditions, risks, merge point, DAG and Mermaid updated.
- **R4** (minor): L8 named `IsGorensteinAlg`; stage 06 defines `IsGorensteinWith A S ℓ` / `IsGorenstein A S` (S06-L1). Rebound.

## Seam 05/06
- Consistent: 06 plan states "S05 Prop subquot uses (a), Prop Xiso uses (b)", L3 first in the L track, `sorry`-stubs of exact L3 signatures on impl branches, names fixed by S06-X1's message to the stage-05 master. File `CommAlg/NewOld.lean` agrees. Both sources name the 05→06 export `if:s06-lemD`.
- Unresolved, to settle in S06-X1's message / S05-M4: (i) 06 encodes the tex hypothesis `S_K = (S/𝔞)_K × (S/𝔟)_K` field-free as `∃ c ≠ 0, algebraMap A S c ∈ 𝔞 ⊔ 𝔟`; S05-M4 should state `prop:s05-subquot` so that this `c` is visibly available (e.g. `T` torsion-free with `T_K` splitting, `c` a common denominator), and S05-L6b must build a `NewOldData` rather than restate the splitting. (ii) 06 fixes `A` a Noetherian *local* domain; S05 originally said Noetherian domain; for `T` localised at `m` over `ℤ_p`/`Λ` this is fine, but if S05 ever applies it to a non-localised Hecke algebra the hypothesis fails. (iii) Exact field names (`ann_a`, `ann_b`, `bEquivDualQuot`) come from the stage-06 plan, not yet from code; to be reconfirmed at S06-X1.
- Scheduling: S05-L6b/L8 now wait on S06-L3 (early-start WP, no critical-path impact for 05).

Counts: confirmed 2 (F2, F7), partial 3 (F1, F5, F10), rejected 5 (F3, F4, F6, F8, F9). Own severity: 1 major (R3), 0 critical, 7 minor-or-less actions (F1, F2, F5, F7, F10, R1, R2, R4 minor).
