# Resolution of the Muse audit of `stage-03.md`

Reviser: stage-03 reviser (Sonnet), 2026-11-14. Each finding was checked against `stage-03.md`, `OVERVIEW.md`, `stage-01.md`,
`stage-02.md` and `plan/staged/stage-03-ribet-ihara.tex` (all tex labels used in `stage-03.md` exist; no label is missing).

| Finding | Muse sev. | Verdict | Own sev. | Action |
|---|---|---|---|---|
| F1 WP count 31 vs 29 rows | minor | confirmed | minor | count set to 29; optionals declared inside rows; L5 execution split `L5a`/`L5b` stated |
| F2 `deps` cells not WP ids | major | partially confirmed | minor | X1 "stage-02 partial export" -> `—` (entry condition in §3); ranges `M1–M5`, `L1–L9` expanded; "(soft)" annotations kept deliberately (soft edges are in the edge list, same as stage 02) |
| F3 X2 edits aggregator files | critical | partially confirmed | minor | the lakefile glob is an explicitly assigned edit (OVERVIEW §1 allows); MANIFEST/ATTRIBUTION rows are aggregator content: now delivered as report lines, applied by the stage master |
| F4 missing hard edges | critical | partially confirmed | minor | L8 uses vendored `weightedAdjoint`: dep `X2 (soft)` added; T3 deps gain `L7 (soft)` (it was in the edge list only). Rejected: M3 needs only the tex interface `if:s02-*` (exists), M1/M4/M5 soft links to C2/C4/C5 are intended (checks closed in M7, see F6); L10 reaches X2 through L1 |
| F5 critical path not longest | major | confirmed (own computation) | minor | chain B with X2 = 495 min > A = 485 min (plan wrote B "after X2"); B is the longest, total ≈ 9.3 h (not 9.1; Muse's 575/635 assumes L5 atomic, but L5(i) runs in W1); risk/throughput text updated |
| F6 acceptance not mechanical | major | partially confirmed | minor | L3 test file named + `#print axioms`; L5 part (i) axioms check; X1 report lists 3 rows; M7 closes the soft numeric checks of M1/M4/M5. Rejected: splitting M1, L9 shape check at its own gate (L11 audits shapes; hypothesis shapes cannot be machine-checked), C3/C4 provenance (inside PYCHK) |
| F7 M3, L6 difficulty | major | rejected | — | M3: proofs already in the tex, SA dependence explicit (R4), routine; L6: abstract linear algebra plus a cited-hypothesis instantiation, routine; no model change |
| F8 resources (3 Lean slots etc.) | major | rejected | — | `SLOTS=2` is enforced by the wrappers (OVERVIEW §3.4/§4), opencode jobs do not count as Claude agents; the 3-agent limit is per coordinator; nothing in stage 03 exceeds it |
| F9 external WP ids unverified | minor | partially confirmed | minor | checked all S01/S02 ids: `S01-L8` does not exist (it is `S01-L8a/L8b`) and `S01-X0` does not exist (`S01-X1`); fixed in L9 inputs/deps, DAG, §3. All other ids (S01-X3, L1, L6, L12, L13, C0, C1, C3, C4, H0, H1, T0, M0, M2, M3, M4; S02-L4b, L6, L7, L8, L9, C1, C5) exist with the stated meaning |
| F10 soft X2->L1 not a DAG branch | major | rejected | — | both outcomes expose the same names (`Graph.PhiComb`, `Graph.X`); decision recorded in `runs/s03.md`; hard edge would idle L1 for 45 min |
| F11 `Fintype`/`DecidableEq`/`hw` missing | minor | confirmed | minor | L1 goal now states `[Fintype]`, `[DecidableEq]`, `hw : ∀ e, 0 < w e` |
| F12 mass/factor-2 conversion | major | partially confirmed | minor | at `U = Ô^×` (the only level used) `−1 ∈ U` holds; an explicit `mass_w_form` lemma was missing from L5(iii) and is added. Rejected: "L6 level M unstated" (L6 states `U_0(M)`, `ℓ ∤ qM`) |

## Additional findings
- **R1 (minor)**: placeholder/nonexistent upstream ids `S01-L8`, `S01-X0` in L9 inputs, DAG line, §3 (merged with F9; fixed).
- **R2 (minor)**: critical-path arithmetic mixed bases (A with X2, B without X2); recomputed (F5).
- **R3 (minor)**: `S03-L9` deps listed only `S01-L8`; Brandt modules are `S01-L7`: deps now `S01-L7, S01-L8a, S02-L9`.
- **R4 (minor)**: `S03-X1` acceptance `latexmk` alone did not cover its registry deliverable; report must list the 3 rows.
- **R5 (major, cross-stage)**: `stage-02.md` §5 states stage 03 needs "only L8 and L4b" from stage 02, but S03-L7 also needs S02-L6, S02-L7 and S03-L9 needs S02-L9. Noted in stage-03 §3; the stage-02 export list should be widened (global master / stage-02 reviser).

## Counts
Muse findings 12: **C = 3** (F1, F5, F11), **P = 6** (F2, F3, F4, F6, F9, F12), **R = 3** (F7, F8, F10).
Own severity of the 12 findings plus R1-R5: critical 0, major 1 (R5), minor 13 (F1-F6 minus rejected, F9, F11, F12, R1-R4); 3 rejected.
Muse severities were inflated for F3 and F4 (critical -> minor).
