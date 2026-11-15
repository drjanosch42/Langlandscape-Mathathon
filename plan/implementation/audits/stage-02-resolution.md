# Resolution of the Muse audit of stage-02.md

Each finding was checked against `stage-02.md`, `OVERVIEW.md` (§4: 3 Claude agents per coordinator; opencode jobs do not
count) and `stage-02-tree-quotients.tex`. Verdicts: C confirmed, P partially confirmed, R rejected.

| finding | Muse sev. | verdict | own sev. | action |
|---|---|---|---|---|
| F1 waves exceed the 3-agent limit | critical | P | minor | waves are eligibility lists, the text already caps workers at 3; wording made explicit (per coordinator, opencode not counted, priority order) |
| F2 M2/M3 acceptance is TEXCHK only | major | P | minor | reviewer named in acceptance (M6, Fable); M6 already depends on M2/M3 |
| F3 M4 soft dep on C4 | major | C | minor | C4 -> M4 made a hard dep (DAG, mermaid, M4 row); M4 may be drafted as sketch but merges after C4 (C4 is W0, M4 is W1) |
| F4 GL₂ vs SL₂ model mismatch in L1/L2 | major | R | - | L2 outputs the GL₂-coset `Vert`/`Edge` (§0); SL₂ appears only in lem:s02-tree(c) as transitivity with stabilisers `SL2Zq`, `K1q`, `IwSL`; no second model |
| F5 L6 lacks direct dep on L1 | major | C | minor | `L1 -> L6` added (row, DAG, mermaid) |
| F6 L10 contradicts "cannot be instantiated" | major | R | - | §0 says only `Hyp.SA/HS/BTtree` cannot be instantiated; L10 gives a per-instance `BGConnected` relative to `Hyp.BGData`, as the SA registry row already states |
| F7 L3 model/difficulty (haiku option) | minor | C | minor | difficulty routine, model sonnet, haiku option removed (row and §4) |
| F8 L8 acceptance incomplete | minor | C | minor | acceptance extended: rank over `ZMod p` = ℤ rank, `decide` connectivity example |
| F9 C2 verifier accounting | minor | R | - | OVERVIEW §5: launching worker is the named verifier and re-runs PYCHK; opencode drafts do not count as Claude agents |
| F10 TITAN accounting | minor | R | - | TITAN limit (`SLOTS=3`) is enforced by the global master; stage-02 only names candidates; nothing to serialise in the plan |

## Additional items

- **R1 (cross-stage, from stage-03 resolution R5; minor).** Partial-export list in §5 now includes S02-L6 and S02-L7
  (needed by S03-L7) and S02-L9 (needed by S03-L9).
- **R2 (rebinding to revised stage-01; minor).** `S01-X0` -> `S01-X1` (L8 deps, §3); `S01-L8` -> `S01-L8a` (L7 inputs and
  deps, DAG, §3; `heckeT` lives in L8a, the adjoint L8b is not used).
- **R3 (minor).** S02-L7 uses `Up` (S01-L10) in its inputs but had no dep on it: `S01-L10` added to deps and DAG; `S01-L8a`
  added to the DAG edge list.

Counts: C 4 (F3, F5, F7, F8), P 2 (F1, F2), R 4 (F4, F6, F9, F10). Own severity: critical 0, major 0, minor 6 (plus R1-R3).
