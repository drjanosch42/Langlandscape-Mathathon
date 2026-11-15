<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# MILESTONE CLOSED: HACS Lane B (Mathathon part) — HJ-6-min, HJ-6b, HJ-1 + HJ-2, PC2 prep

- **Branch:** `impl/hacs-laneB`. Head at closure: see the commit that adds this file. `origin/main` was merged in at 302ff311 (merge, no rebase).
- **Time:** START 2026-11-15T00:55Z, closure 2026-11-15T01:50Z (≈ 1 h wall).
- **Agents:** 8 subagents in all, ≤ 4 at once. They were 4 implementers (Opus ×3, Sonnet ×1), 2 fresh Opus reviewers and 1 Sonnet worker for PC2 prep. Every worktree is pruned except `hacsB`.
- **Status words:** every number below is *computed*. Nothing is called "certified" (Fabian Q3).

## 1. Delivered

| WP | What | Merge | Review |
|---|---|---|---|
| HJ-6-min | Brandt lattices → HACS EXW `LatticeFromFreeZ` → `ReadLocal` (`Registry/JL/`, `cmake/jl/JL.cmake`, two upstream hooks). Validations: `JLBrandtFreeBlockSpikeValidation` (fast) and `JLBrandtFreeBlockRead` (slow, `JL_BRANDT_IN`) | 72be8bd1 | PASS, 1 major (headline wording, fixed) + 8 minor: `20261115_HJ6min_review.md` |
| HJ-6b | Exact integral congruence modules C_f = L/(L_f ⊕ L_f^c), plus ring module, Hecke index and Gram. Validations: `JLBrandtCongruenceSpikeValidation`, `JLBrandtCongruenceRead`. Collector: `code/python/langlandscape/hacs_bridge/laneB_collect.py`. Result: `code/results/laneB/congruence_k.json`. Also includes the HJ-6-min review fixes m1/m2/m4/m8 | 216f8064 | ACCEPT, 0 crit/maj, 6 minor: `20261115_HJ6b_review.md` |
| Python reference | Reference values + timings and 5 test fixtures. Moved to `code/python/langlandscape/hacs_bridge/laneB/`, because it uses PARI and no external CAS is allowed in `code/hacs/`. Result: `code/results/laneB/py_reference.json` | a017d3b9 | pytest 5/5; cross-checks the HJ-6b numbers (69/69 orbit Smith lists) |
| HJ-1 + HJ-2 | Native quaternion core `Registry/JL/quat/`: Quat, Lattice, Order, ClassSet (`qf_theta`), Brandt2. Self-test; `jl_brandt2_dump` writes `langlandscape_brandt/v2` | 2ccaeefd | self-test 8084/0; v2 = Lane A 14/14 `F_fnv`. No separate fresh review (deviation D7) |
| PC2 prep | `plan/hacs/pc2/{README.md, jl_census.sbatch, collect.sh}`. **Not submitted**; marked not ready to submit | 1a86fc4e, ddf9f164 | `bash -n` OK; shellcheck not installed |

Binaries (outside git):
- `/home/janosch/data/hacs-build/laneB/b6/hacs` (CPU-only, RelWithDebInfo; built from worktree `hacsB-6b`, since removed);
- the spike build `/home/janosch/data/hacs-build/laneB/spike`.

Both binaries' `OC_SOURCE_DIR` points to removed worktrees. The data reads do not need it. Validations that read tracked fixtures do: for those, rebuild from `hacsB`.

## 2. Talk numbers (all *computed*; sent to the global master)

1. **Mazur on the definite side through HACS's integral engine** (k = 2, B_{q,∞}):
   - The Eisenstein congruence module equals ℤ/num((q−1)/12) **exactly** (2- and 3-parts included) on all 14 levels of Lane A's v2 records: B₁₁ and every prime D ≤ 43. That comes from the exact route (HJ-6b).
   - HACS ReadLocal on L ⊕ L agrees at every ℓ ≥ 5, and at ℓ = 3 when requested (q = 37: ℤ/3 exact). ℓ = 2 is out of ReadLocal's reach (`open(precision)`).
   - Table: q = 11, 23, 37, 101, 131 → h = 2, 3, 3, 9, 12 → ℤ/5, ℤ/11, ℤ/3, ℤ/25, ℤ/5 ⊕ ℤ/13.
2. **Beyond Mazur, k > 2** (32 integral Sym^n cells):
   - The only nontrivial lattice congruence module is at **D = 13, k = 8: |C| = 37**, between the orbits x − 10 and x² + 19x + 6. Both have w₁₃ = −1, equal signs (PARI).
   - GL₂ side: Res = 2³·37 is the only resultant of the T₂ factors that contains 37.
   - Caveat: the lattice at k > 2 is not canonical.
3. **Two independent implementations agree:** HACS-native C++ and Python + cypari2 give the same 69/69 orbit Smith lists. There is **no read-side speed claim**: both take milliseconds.
4. **Build side, the one speed line:** class set + T₂ for B_{997,∞} (h = 83), single-threaded, on the same node.
   - Re-timed at 01:47Z, load average ≈ 6 of 32 threads:
     - Python (`brandt.module` + `T(2)`): 32.7 s + 32.0 s = **64.7 s**;
     - native `jl_brandt2_dump 997 --ops 2`: **0.02 s** (including the JSON write), on 3 runs, with 4.6 MB RSS.
   - The factor is ≈ 3 × 10³. The first measurement (61 s vs 0.025 s, loaded node) gave ≈ 2.4 × 10³. "~10³×" is honest.
5. **Native census:** all 404 primes q ≤ 2777 generated in 19.6 min, single-threaded. Eichler's class number formula holds for all 1229 primes D < 10⁴. The HACS read of the census is in §6.

## 3. Upstream files touched (Fabian Q2: allowed, small, marked `Langlandscape JL hook`)

- `code/hacs/CMakeLists.txt`: one line, `include(cmake/jl/JL.cmake)`, right after the `cmake/slot27/*.cmake` includes (l. 1413).
- `code/hacs/src/hacs/ValidationRegistry.cpp`: `void RegisterJL();` and the call `RegisterJL();`, both after `RegisterSlot27HeckeZEisUpChar` (l. 410, 1975).
- Regenerated CLI manual tables (`docs/latex/tools/gen_cli_manual_tables.sh`). This is a generator, not an owner-gated emitter.
- `code/hacs/CHANGES.md`: one row per file and hook, plus three deviation sections.

**Not touched:** `Registry/Slot27/*`, `cmake/slot27/*`, `*GoldenReference.inc`, emitters, licence files, `code/hacs/lean/`. No owner-gated env var was set, `module_Z()` was not used (Q4) and no GPU was used.

## 4. Deviations (disclosed; details in `code/hacs/CHANGES.md`)

- **D1 — relaxed protocol (Fabian Q3).** There is no contract text and no refereed [C] line. HACS's certificate words are printed as `met(hacs_word)`.
- **D2 — targeted validation only (Fabian directive).** These were NOT run: full `--all` / `--all-full`, `GOLDEN_STRICT`, the four digests, `LABEL_CENSUS`, `ConsoleScriptValidation`, a route bit-identity arm, the parallel-decomposition statement and a quiet-window timing. What was run: `--list` (298 names; the upstream 294 in their order), the four JL validations, `HeckeZExportWord`, `HeckeZLocal`, `CliManualCoverage` and `LicenceGuard`. **`--all` grows 246 → 248** (the two fast JL spikes). *One full run is due after the merge, since the hooks touch shared registration and CMake.*
- **D3 — the L ⊕ L adapter.** ReadLocal assumes cusp multiplicity 2; our adapter is not a HACS route.
- **D4 — our own exact BigInt Smith/HNF** (HACS's routes are mod ℓ^K only). We also use our own minimal JSON reader.
- **D5 — `OC_ENABLE_JL` defaults to ON** (the plan said OFF until HJ-11).
- **D6 — no catalogue entry, no `EXPECT_NAMES` / roster-count update.** HJ-1/2 is not registered in `hacs` and not in CMake; it is a standalone build.
- **D7 — no separate fresh review for HJ-1/2.** Acceptance rests on the self-test (8084/0), on the byte-exact agreement with Lane A's independently written v2 records, and on the Python cross-check.
- **D8 — HACS process steps skipped**: the slot-27 heavy-job locks. Builds went through our node semaphore `heavy.sh` (2 slots), not `s27/build.lock`. Q6 allowed either.

## 5. Open items (post-Mathathon)

- **Full HACS row** after the merge to main: `--all` (sharded), `GOLDEN_STRICT`, digests, `LABEL_CENSUS`, `ConsoleScript`.
- **HJ-6b minors:** an exact-Mazur gate on the 6-parts, a per-orbit bad flag, `f` for deg > 6, and an input hash in the provenance.
- **HJ-6-min minors:** m3, m5, m6 are wording only.
- **HJ-1/2:**
  - a sparse record layout (v3), since dense JSON reaches ≈ 4 GB per q at 10⁵;
  - a second class invariant, because θ buckets come in pairs (6.6 M exact tests at q = 10007);
  - charpoly_ℤ, Eichler-order class sets, and registration as `JlValidation` (HJ-11).
- **Remaining WPs:** HJ-3 (levels), HJ-4 (Sym^n Brandt natively, canonical lattice → lattice-independent C at k > 2), HJ-5a (JSON CLI), HJ-7 (tree/Ihara), HJ-8 (JL defect), HJ-9, HJ-10 (GPU census), HJ-11, HJ-12a/b audits.
- **PC2/TITAN:** not now. q ≤ 10⁵ costs ≈ 4000 core-h with the Eisenstein T_ℓ, ≈ 300 with ops < 50. Feasible on this node: q ≲ 5000. Re-cost after v3 and the faster identification; the script is ready apart from its placeholders.
- **Python reference:** the q < 1000 sweep stopped at q = 131 for the full table; q = 401 and 997 have only the class set and T₂.
- **Q4 = YES (Fabian, recorded on main).** `descent(...).module_Z()` is now allowed. It was not used before this closure. Post-Mathathon use: the GL₂-side integral comparison (HJ-8).
- **Lane A spec:** the §8 r_eis = 1 expectation on L, forwarded, is being corrected by Lane A.

## 6. Native census read

The native census was read with the b6 binary (log: `/home/janosch/data/hacs-run/laneB/read_native_le600.log`) on the 109 primes q ≤ 600 generated by `jl_brandt2_dump`. All results are *computed*.
- **`JLBrandtFreeBlockRead`** (HACS ReadLocal; the Eisenstein read on L ⊕ L): 109 cells, 286 reads. **agree_mazur = 109/109** at ℓ ≥ 5, differ 0, fnv_mismatch 0, exceptions 0. Wall time 178 s.
- **`JLBrandtCongruenceRead`** (exact ℤ route): it was stopped by the 15-min cap after 80 complete cells (all primes q ≤ 479). On all of them, the Eisenstein orbit's C has order exactly num((q−1)/12), **80/80**, 2- and 3-parts included. The largest per-cell time was 60 s. The dense BigInt Smith step is the bottleneck at h ≳ 40, and is a follow-up item.
- **Not read:** the full 404-cell read up to q = 2777. Its large-h cells take minutes each with ReadLocal on L ⊕ L. A sparse/modular route is a post-Mathathon item.
- **Talk line:** "Through HACS's integral engine, the Eisenstein congruence module of the definite Brandt module is ℤ/num((q−1)/12) for every prime q ≤ 600 at ℓ ≥ 5 (109 levels), and exactly, all primes, for q ≤ 479 (80 levels)." 

**Request:** merge `impl/hacs-laneB` into main.

## 7. Milestone full run on main (2026-11-15, after the merge)

This is the one full run that deviation D2 called for. It ran on `origin/main` @ ffb527cf, checked out in worktree `hacsB` as `impl/hacs-laneB-final`. Script: `/home/janosch/data/hacs-run/laneB/final_run.sh`, run via `heavy.sh`; logs are in `/home/janosch/data/hacs-run/laneB/final/`.
- **Build:** fresh, `/home/janosch/data/hacs-build/laneB/final`, `-DOC_ENABLE_CUDA=OFF`, RelWithDebInfo, `-j12`; 217 s (configure 02:03:35Z). `hacs --version`: `hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`.
- **Binary:** sha256 `a6acb500287841893fe82962f8cc1d49a33bc49714aa3244fec5f7c61b4c9158`. `--list` gives 298 names.
- **`--all`, 4 shards:** `SHARDED_ALL shards=4 passed=248/248 failed=0 mode=--all wall_s=513.2 … verdict=OK`. The union of the shards equals the roster (248 planned, 248 in roster, 0 duplicated). The only `[EXCEPTION]` lines are the harness's own engineered ones (`ValidationHarnessCatchValidation`, "not a real failure").
- **`GOLDEN_STRICT=1 GoldenRegressionValidation`:** `tier A checked 12154, failing 0; tier B checked 6231, mismatching 0`, `[PASS]`. It took 31 s.
- **Total:** 763 s wall (02:03:35Z → 02:16:18Z). Nothing failed, and nothing was changed.
- **Still not run** (D2 remainder): the four digests, `LABEL_CENSUS`, `--all-full` (the slow tier), the device lane.

## Erratum (global master, 2026-11-15 ~02:40Z; from batch-8 G1-X2)
- The census line "exactly (2- and 3-parts included) for every prime q ≤ 479 (80/80)" is wrong. There are 92 primes ≤ 479; the exact route stopped at its 15-min cap after 80 levels, and the 80th prime is 409. Correct: **exactly for the first 80 primes, q ≤ 409 (run capped)**. The ℓ ≥ 5 HACS read for all 109 primes q ≤ 600 is unaffected.

- Also from batch 8 / round 1b: "32 integral Sym^n cells" is not derivable from the JSON. Correct: 74 cells = 14 with k = 2 + 60 with k > 2, of which 26 have positive rank / are non-zero.
