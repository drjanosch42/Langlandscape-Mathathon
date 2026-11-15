<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# HACS Lane A: closure (2026-11-15)

Branch `impl/hacs-laneA` (worktree `/home/janosch/dev/Langlandscape-wt/hacsA`) holds 22 commits on origin/main 17d8acfc. Wall time: START 00:31Z → closure ≈ 01:40Z, about 1 h 10 min. Merge notes for each WP are in this outbox (HJ-0, HJ-A1, HJ-A2, HJ-A3, HJ-B0).

## Delivered (all *computed*; HACS 0.2.1 = v0.2.1, DOI 10.5281/zenodo.24231446; data hacs-data v0.2.0, DOI 10.5281/zenodo.24147012)

| WP | What | Result | Audit |
|---|---|---|---|
| HJ-0 | `hacs_bridge/runner.py` (env **allowlist**, `@@TAG` parser, sha256 provenance, `hz_settings`); smoke script `code/hacs/jl/smoke/hj0_smoke.oc`; `code/hacs/jl/README.md`; CHANGES rows | every verb of §1.1 runs (exit 0, 0.16 s); default_fp 0x8ffc29730c4f9672, θ order `lex` | Opus FAIL r0 → fixed |
| HJ-A1 | `gl2_dnew.py` → `code/results/s05/gl2_dnew.json` | symn.json 66/66, pi_sign.json 8/8; extended grid 152/204 OK | Opus FAIL r0 → fixed |
| HJ-A2 | `definite_alg.py` → `code/results/s06/definite_local.json` | Mazur's 5 is non-étale and Gorenstein; negative control clean (D = 3, 5, 7, k = 12); generation over Z certified 14/14 | Opus PASS (3 minor, fixed) |
| HJ-A3 | `betti_t4.py` → `code/results/s06/T4_betti.json` (= S06-H1) | coker(Ψ*Ψ)_m = (Z/17)² = (T(1)_m/δ)² at k = 12, 28, 44, 60; k = 124 not_reachable; off-route k = 124 gives (Z/17²)² (expected, not gating) | Fable FAIL r0 → fixed |
| HJ-B0 | spec `langlandscape_brandt/v2` (`plan/hacs/freeblockz-export-format.md`), `brandt_export.py`, 74 `free_block_z` records, `plan/hacs/laneB-design.md` | F_fnv byte-exact vs HACS; Lane B matches 74/74; deterministic canonical class order | Opus FAIL r0 → fixed (v2) |

Verified at closure:
- Lane A tests: 86 passed. Full Python suite: 483 passed, 3 skipped (178 s), run once at closure.
- The Lane A binary (`cmake --preset minimal -B /home/janosch/data/hacs-build/laneA`, CUDA 13.0 sm_120, 3m25s) passes strict golden (tier A 12154/0, tier B 6231/0), run once at build time.
- No upstream HACS file is modified (only `code/hacs/CHANGES.md` rows appended). No hooks, no Lean, no lake, no GPU arm, no s27 lock, no emitter env var.

## Disclosed deviations
1. **Code location.** All new Python lives in `code/python/langlandscape/hacs_bridge/` (GPL), not in `code/hacs/jl/*.py` as the plan names it. Inside `code/hacs/` there is documentation and the smoke script only. The exporter in particular uses PARI, which HACS forbids inside `code/hacs/`.
2. **No re-audit of the fix rounds** (Fabian's targeted-validation directive). Each fix was verified by its WP pytest and a regeneration of its records. No sharded `--all`, `--all-full` or repeated golden runs.
3. **HJ-A1:**
   - 52 extended cells are skipped as `predicted_rss` (> 3 GiB per process, the box rule).
   - U_D signs are ambiguous on 8 cells; the per-factor signs there are null and the totals exact.
   - Signs are computed for prime D, M = 1 only. Non-squarefree N is refused.
   - The process took 21.4 min against a 20 min HACS-wall cap (HACS wall itself was 19.3 min).
4. **HJ-A2:**
   - The algebra is the anemic T^(Dℓ) (no T_ℓ, no U_D); adding T_ℓ changes nothing at k = 2, as checked.
   - The S06-C1 comparison is replaced by an independent Python check.
5. **HJ-A3:**
   - `module_Z()` is off by default (Q4), and gating uses the amalgam route.
   - The ω′ block is adapted from `task1_v6/scripts/cell.py` (CC-BY-4.0, Fabian), with attribution and SPDX snippet tags inside a GPL file. **The global master confirms this licence handling.**
   - The k ≥ ℓ rows are tagged `interpretation: expected` (outside the amalgam's proven range ℓ > k).
6. **HJ-B0:**
   - The v1 spec was superseded by v2 within about 1 h (the v1 class order was process-dependent).
   - k > 2 records are `canonical: false`.
7. **Provenance.** Several result records carry `commit …-dirty`, because the worktree was shared by parallel workers. Each record was generated from the WP's final code, and the following commit contains exactly that code.

## Open items
- S06-C3 cross-check of HJ-A3 (`pending_crosscheck`; done when stage 6 merges C3). S06-C1 comparison of HJ-A2.
- Fabian Q4 (`module_Z()`; flip `--allow-module-z`). Q1 licence scheme still PROVISIONAL.
- HJ-A1: the 52 high-RSS cells (need > 3 GiB, or TITAN). Sign disambiguation would need U_D matrices from HACS, which `level_n` does not expose.
- HJ-B0:
  - k > 2 canonical lattices;
  - `d_target` for M > 1;
  - ℓ = 2 C_T reads, which need Lane B's Smith route;
  - the D = 11 L ⊕ L C_T = 5 example, *expected* on our side.
- t_{G_k}(3) vs the Tamagawa exponent t_f(3) is unchecked.
- `code/results/INDEX.md` lacks rows for the new s05/s06 files. Update it at merge (global master, or a follow-up).
- Worktree `/home/janosch/dev/Langlandscape-wt/hacsA` and the build `/home/janosch/data/hacs-build/laneA` (3.3 GB) can be removed after the merge. The build is kept for now in case Lane B or re-runs need it.

## Fabian decisions after closure (2026-11-15 ~01:48Z)
- Licence: the CC-BY-4.0 snippet adapted from task1_v6/scripts/cell.py inside GPL `betti_t4.py` (attribution + snippet SPDX tags) is CONFIRMED.
- Q4: YES, `descent(...).module_Z()` may be used. The A3 opt-in flag stays; enabling it is allowed.
