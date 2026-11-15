<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# MILESTONE CLOSED: HACS Lane C — HJ-3, HJ-4a/b, HJ-7a/b, HJ-8 (a, b, def), HJ-9, INT

- **Branch:** `impl/hacs-laneC` (worktree `Langlandscape-wt/hacsC`), from main f0ddadc9. The head is the commit that adds this file. Not pushed.
- **Time:** START 2026-11-15T06:10Z (plan 1296ea9d) → closure ≈ 13:55Z, about 7 h 45 min wall. Hard stop 17:30Z kept.
- **Agents:** 3 Opus workers (A: HJ-4a/HJ-3/HJ-4b/INT/summary; C: HJ-7a/b, HJ-9, HJ-8-def; D: HJ-8a/b), 10 fresh reviewers/auditors (Opus ×6, Fable ×2, Sonnet ×3). At most 4 subagents ran at once, and at most 4 worktrees existed at once.
- **Status words:** computed / checked / cited / expected. Nothing is called "certified". HACS record words are quoted only as record words.
- **One-page report summary:** `20261115T0830Z_laneC-summary.md`, final, with the HJ-8 section filled in.

## 1. Delivered (each merged into impl/hacs-laneC after its review)

| WP | Content (native C++ in `Registry/JL/quat/` unless said) | Accept, computed | Review |
|---|---|---|---|
| HJ-4a | `BrandtSym`: integral Sym^n Brandt module at O^× on the intrinsic lattice (= Sym^n(ℤ_p²) at p ∤ D); T_ℓ, Π_p, W_D, pairings w_x / \|Γ_x\| | symn.json 66/66; pi_sign 8/8; PARI newspace 374/374 operators | Fable audit (HJ-12a) PASS, 7 minor |
| HJ-3 | `Level`: U₀(M), U₁(N), U₀(q)U, S_s towers | levels.json; \|S_4\| = 31 250 (new); s02/validation fibre sums 240/240 | Sonnet PASS |
| HJ-4b | `BrandtLevel`: Sym^n at U₁(N1) ∩ U₀(N0); T_ℓ, classical U_ℓ, U′_p, ⟨d⟩, Π, W_ℓ; Eichler-level API | up.json (incl. the U′_p failure); pi_sign 8/8; PARI T_ℓ/U_ℓ 249/249; commutation/adjoints on 102 cells | Fable re-audit (U_p) PASS, 6 minor |
| HJ-7a | `Tree`: Γ\T, s₀, s₁, α, αα†, Φ^comb, Ihara at weight 2 | s02/{validation,T2,T3,H_Vk}, s03/{T1,T2,T6} k = 2: 288/288 cells (3591 substantive fields); B₁₁, q=2: coker αα†\|cusp ≅ ℤ/5, Φ^comb ≅ ℤ/5 | Opus PASS, 7 minor |
| HJ-7b | `TreeK`: weight-k Ihara ι = (s₀*, −s₁*), exact Smith over ℤ; W_D integral | Python two-term 276/276; 210 new cells exact, second route (BrandtLevel) 210/210 identical; W_D vs PARI 38/38 | Opus PASS, 6 minor |
| HJ-9 | `Ordinary`: U_5 on ℤ/5^m[S_s], B₃, q = 2 | s04/T3 (s ≤ 3), H6, H7: 7/7 cells, 215/215 fields; rk_Δ e = 1 for s = 1..5 (new) | Opus PASS, 6 minor |
| INT | 9 quat sources linked under OC_ENABLE_JL; 5 fast validations (`JlQuatValidation.cpp`) | `--list` 303; battery below | Sonnet PASS |
| HJ-8-def | `tools/jl_eta_def.cpp` (standalone): native η^B | T5@k 7/7 = s06/T5_def; census (bounds §2) | Opus FAIL (2 major) → fixed → re-check PASS; addendum Sonnet PASS |
| HJ-8a/b | `hacs_bridge/jl_defect.py` (Python driver, GL₂ side through HACS) | T5, H3, census (§2); 14 pytest | Opus PASS ×2 (5 + 6 minor, fixed) |

Results (all with provenance: tool, commit, params, date, runtime, binary sha256) are in `code/results/laneC/`: hj4_symn(+_mfcheck), hj4_congruence, hj3_levels, hj4b_level(+_mfcheck), hj7_tree_w2, hj7_ihara_k, hj7_ihara_xcheck, hj9_lambda, hj8_def_native, T5_hacs, H3_hacs, defect_census. The WP notes, merge notes and reviews are in `plan/hacs/outbox/20261115*`.

## 2. Headline numbers (computed; for the report and the talk; details in the 1-page summary)
- **The explicit map (HJ-7):** the Ribet/Ihara comparison realised natively on the Bruhat–Tits tree quotient. At weight 2, s02/s03 is reproduced 288/288. At weight k, the exact ℤ-cokernel of the quaternionic Ihara map is computed on 210 cells (D ∈ {2,3,5,7,11,13}, q ≤ 13, q ≠ D, even k ≤ 14), with free rank = dim S_k(Γ₀(Dq))^new 210/210. Odd torsion prime to 6Dq occurs only at (k,ℓ) ∈ {(8,5),(10,7),(14,5),(14,11)}, as a single ℤ/ℓ, in 68 cells; there is none for ℓ > k. Two independent native routes agree 210/210.
- **HJ-9:** rk_{ℤ/5³[Δ_s]} e = 1 for s = 1..5, with |S_5| = 781 250.
- **HJ-8:**
  - T5: weight k 7/7 = S06; weight k+(p−1) Thm E holds on 4 cells, 2 of them new: (13,18,19)@36 and (13,12,31)@42; 3 cells open.
  - H3: 9/9 blocks.
  - Census: q prime ≤ 50; k even, 2 ≤ k ≤ 20; p prime, k < p < 200, p ≥ 5, p ≠ q, p ∤ q²−1. 5869 cells (5538 trivial). 5 genuine congruences with η^B = p: 5/5 agree. 50 old-congruent: 44/44 computed agree (one t = 2 at (47,12,17)), **6 not run**. **120 blocks not determined.**
  - **No computed block disagrees anywhere.**
  - U_q sign in (19,6,7), (19,6,107), (2,20,83): taken from the sign of a_q of PARI's q-new eigenforms (cypari2, called from our Python driver jl_defect.py, not from HACS); orbit matching by charpolys of T_ℓ; checked to be among the HACS-admissible assignments; never from the definite side. GL₂ side "HACS + PARI". Where HACS's sign is unique, PARI agrees 30/30.

## 3. Validation (the one full battery; `20261115T0725Z_laneC-battery.md`)
- Fresh build at impl/hacs-laneC @ 08481d69 (`/home/janosch/data/hacs-build/laneC/final1`, CUDA off, RelWithDebInfo), sha256 19ab4d0670f25e5c14d290f363b3fd86c9eebc636e5dcffec181029bf59def9d.
- `--list` 303 = upstream 294 in order + 4 Lane B JL + 5 Lane C JL.
- `--all`, 4 shards: **253/253**, 0 failed.
- `GOLDEN_STRICT=1 GoldenRegressionValidation`: tier A 12154 / 0; tier B 6231 / 0; PASS.
- **Coverage of the final branch:** `git diff 08481d69..HEAD` on code/hacs/cmake/jl, code/hacs/src/hacs/Registry/JL/*.{cpp,h} and the nine linked quat sources is **empty** (checked at closure). HJ-8 stays out of the binary (option (a)).
- Not run: digests, LABEL_CENSUS, `--all-full`, the device lane.
- Python at closure: `tests/test_hacs_bridge_jl_defect.py` + laneB tests, 19 passed.

## 4. Upstream files touched
None beyond Lane B's hooks (CMakeLists include, ValidationRegistry RegisterJL). Within code/hacs/ there are three further touches:
- Lane C rows and the Lane C deviation section in `code/hacs/CHANGES.md`;
- `cmake/jl/JL.cmake`;
- the generator-regenerated `docs/latex/cli_manual/{counts,validations}.tex`.
No Slot27, golden, licence or emitter edits. No owner-gated env vars, no PARI inside code/hacs/, no Lean, no push.

## 5. Deviations (full list: `code/hacs/CHANGES.md`, "Deviations — Lane C")
- **Plan order:** HJ-4a before HJ-3. HJ-4a and HJ-4b were merged ahead of their audits (both audits PASS afterwards). HJ-9, the optional WP, was done.
- **Two `rm` uses before the no-delete rule** (build output and an untracked result file). Nothing tracked was deleted. After the rule, all deletes went to `/home/janosch/data/trash/` (one untracked file, worker D).
- **Representation and method choices:**
  - P¹ indexing ≠ HACS def:cosetrepsN.
  - Odd k refused.
  - The intrinsic lattice replaces Lane B's hull.
  - HJ-9 uses the coinvariant method at s ≥ 4.
  - TreeK, Ordinary and all tools are not linked.
  - HJ-11-lite: frozen-value validations only, no catalogue entry.
- **HJ-8:**
  - The GL₂ side is a Python driver over HACS plus a p-adic local route; the sign oracle is PARI in 3 cells.
  - 16 blocks ran before sign uniqueness was recorded.
  - Results are splices of runs on committed code: T5 from 2 runs, census from 4, each with its own provenance.
  - The eigenspace route is a cross-check only.

## 6. Open items
- **HJ-8:** T5@k+(p−1) for (3,18,53)@70 and (3,18,61)@78 on the GL₂ side (HACS descent requires n ≤ 60); (13,16,101)@116 on both sides; 6 census cells at k = 20 (about 4 h single-threaded); 120 definite blocks not determined (ramified Hecke fields); sign-uniqueness records for 16 blocks.
- **HJ-7:** W_p for composite D (e.g. 30); a direct H₁ at s ≥ 4 (HJ-9); weight k > 2 on the tower.
- **HJ-3:** alignment with HACS's coset tables.
- **HACS:** the full HJ-11 registration (catalogue, EXPECT_NAMES); the HJ-5 CLI and verbs; HJ-10 GPU census; HJ-12b final audit. Remaining battery items: digests, LABEL_CENSUS, --all-full.
- **Housekeeping:**
  - Worker worktrees hacsC-34, hacsC-7 and hacsC-8 are removed at closure with `git worktree remove`.
  - `hacsC` is kept for the merge.
  - The worker branches impl/hacs-laneC-{34,7,8} remain; they are fully merged.
  - Build dirs under /home/janosch/data/hacs-build/laneC are left in place.

**Request:** merge `impl/hacs-laneC` into main (green: battery 253/253 + golden strict; every WP reviewed).
