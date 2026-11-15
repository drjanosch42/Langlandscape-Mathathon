# Brief: coarse implementation-plan drafter for stage NN (NN ∈ 02..06)

Read `plan/implementation/briefs/common.md` and everything it lists, then `plan/implementation/OVERVIEW.md` (wins on
conventions), `plan/implementation/stage-01.md` if present (as a model of format; yours is coarser), and your stage tex
`plan/staged/stage-NN-*.tex` with SPLIT.md §NN, its interfaces, its P1 audit/resolution files and the relevant
plan/scouting reports (bruhat-tits.md for 02; Stacks.md for 03; Weil.md for 04–05).

Write `plan/implementation/stage-NN.md` at a COARSE level (150–300 lines); it will be revised after stage 1:
- WPs per track (M, L, C, H, T, X) with all schema fields, but WPs may be larger (≤ ~2–3 h agent time) and estimates rough.
  Name the key Lean declarations/hypotheses (`Hyp.*`) and files, which import declarations or vendored sources they reuse,
  and which stage-tex statements stay hypotheses (registered `Hyp.*`) rather than being formalized.
- DAG (edge list + Mermaid), parallel waves, critical path with summed estimate; build batching (2 local + 3 TITAN slots).
- Model per WP (provisional; mark `model: TBD-after-S01` where the stage-1 experiment should decide, with a default).
- Entry conditions (which stage-(NN−1) / earlier interfaces `if:sMM-*` must be merged in `wip-implementation`, or which
  can be stubbed as hypotheses so this stage can start early — decoupled tracks: say what can start before the previous
  stage finishes).
- Merge point and "stage NN done" per track; main risks.
Commit `plan: stage-NN implementation plan (coarse)`. Report ≤ 10 lines: path, sha, WP count, critical path estimate, risks.
