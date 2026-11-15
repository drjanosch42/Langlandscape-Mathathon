# Resolution of the Muse audit of `stage-04.md` (P3)

Reviser: stage-04 reviser (Sonnet), 2026-11-14. Every finding was checked against `stage-04.md`, `OVERVIEW.md`,
`stage-01.md` (f3872ec), `stage-02.md`, `stage-03.md` (84a8973), `stage-06.md` and the stage tex. WP ids unchanged.

| Finding | Muse sev. | Verdict | Own sev. | Action |
|---|---|---|---|---|
| F1 placeholder `S03-L*` names, stub WPs | critical | partial | major (resolved) | placeholders were real; rebound to the real S03 ids (L3 deps S03-L1/L3, L7 deps S03-L7 + S03-L2, C5 deps S03-C1/C2); stub WPs rejected (§3 already prescribes stubs, now only for unmerged S06-L1 and S02/S03 signatures) |
| F2 undeclared `Hyp.InvLimExact` | critical | confirmed | minor | conditional row added to the §0 hypothesis table; L8 acceptance and L9 outputs refer to it; "remove fallback" rejected (L8 is a stretch WP) |
| F3 C2/C5 acceptance only "computed" | major | partial | minor | C2: s = 1 rank cross-checked against the independent PARI count (C4); byte-equal expected-JSON demand and the C5 complaint rejected (`U_p* = 5` is already an explicit check) |
| F4 schema columns, X1 inputs, M7/M8 not mechanical | major | partial | minor | columns/`TITAN?` form identical to stages 02/03 (rejected); M7 and M8 acceptance made checkable (`verdict:` line, latexmk no undefined refs, items closed) |
| F5 DAG edges / mermaid / W0 vs §3 | major | partial | minor | mermaid gained the soft edges `S01-L4c→L3`, `S06-L1→L10`; `L1→L6` redundant (via L2, L5b); W0/L4 consistent with §3 (rejected) |
| F6 Weil vendoring and aggregator rule | major | partial | minor | stated: X2 only proposes the lakefile diff; `LanglandscapeVendorWeil` is a `[[lean_lib]]`, no new `[[require]] path` |
| F7 `IsLocalRing (ℤ_p[G])` false/underestimated | major | partial | minor | claim "not local" is wrong (`ℤ_p` complete local, `G` p-group: `ℤ_p[G]` is local); but the Mathlib gap is real: cyclic fallback now accepted in L5a acceptance, general p-group = stretch |
| F8 split L8, no fallback | major | rejected | nit | stretch WP with a registered, now declared, fallback (F2); Artinian ML on `ZMod (p^m)` levels is the planned route |
| F9 C1 does not discriminate `N_{U_p}` vs `U'_p` | minor | confirmed | major | C1 acceptance now requires `π_* U_p = U_p π_*` and failure for `U'_p` |
| F10 `S01-T0` undefined, T acceptance | minor | rejected | – | `S01-T0` exists in `stage-01.md` (talk skeleton); latexmk check as in other stages |
| F11 second coordinator vs resource limits | minor | rejected | – | the 3-agent limit is per coordinator; M/C/T have no Lean builds, so the node-wide 2 Lean slots are untouched |
| F12 split M4 | minor | rejected | – | 120 min within the 2–3 h limit for coarse stages; labels already in the goal |
| F13 L9 outputs wording / model | minor | rejected | – | outputs already say "registry rows in report"; model default is a `TBD` |

## Extra findings (reviser)

- **R1 (major, from the stage-06 resolution).** S04-L10 said `congruenceIdeal`/`IsGorenstein` are "defined here if 04 runs
  first". S06-L1 (`CommAlg/Gorenstein.lean`) is the sole owner: S04-L10 now imports them, depends on S06-L1 (or a stub of its
  exact signatures, SORRIES.md), has an acceptance grep forbidding local definitions; W0, build batching, §3 and §5 adjusted.
- **R2 (major).** Stage-03 ids rebound (see F1); in addition S04-L7 cited "S03-L2 `ribet`", but the `BG U q` Ribet sequence
  (`ribet_exact`, `ihara_*`) is S03-L7 (S03-L2 is the abstract graph lemma): fixed in inputs, deps, DAG, waves, slack note.
  S04-C5 cited an unnamed "S03 T1 code": now S03-C1/S03-C2. All S01 ids (X1, X3, L3a/c, L4c, L5c, L7, L9, L10, C2, C4, C5, H1,
  T0) and S02 ids (L4a/b, L7, L8, C1) re-verified against the current plans: all exist.
- **R3 (minor).** Naming note added: stage 06 registers `Hyp.HidaControlGL2`, distinct from stage-04's `Hyp.HidaControl`
  (definite weight-k control); §0 table row says so.
- **R4 (nit).** Risk 6 no longer claims stage-03 names are unplanned.

## Counts

Confirmed 2 (F2, F9), partial 6 (F1, F3, F4, F5, F6, F7), rejected 5 (F8, F10, F11, F12, F13). Own severity: major 3
(F1 resolved, F9, plus R1, R2 as extras), minor 7, nit/none 5.
