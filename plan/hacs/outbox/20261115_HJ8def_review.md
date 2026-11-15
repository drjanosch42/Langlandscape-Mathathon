<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Review: WP HJ-8-def (native definite-side η^B, Lane C)

- **Reviewer:** fresh-context reviewer. Read-only, except for this file.
- **Reviewed:** `impl/hacs-laneC` at merge 513366bf.
  - `jl_eta_def.cpp`, added in b0dee376 and unchanged by the merge.
  - The collector, `hj8_def_native.json` and the WP note `20261115T0740Z_HJ-8-def.md`.
- **Verdict:** **FAIL as written. It becomes PASS after the fixes below.**
  - The weight-k numbers, the H3 numbers and the census skip rule are correct.
  - Claim 2 is mis-stated, and it misses a definite-side check that the existing output already settles.
  - Five census blocks are mis-classified.
  - No critical findings.

## Reproduction (computed)

**Build.** I rebuilt in `/home/janosch/data/hacs-build/laneC/review8d/` with the note's `build_cmd`.
- The build took 12 s.
- The sha256 is `de450395…1155`. The provenance records `537127a0…` (see minor m3).

**`--suite h3`.** The output is byte-identical to the original dump `hj8def/h3.json`, after dropping timings.

**`--suite t5`.** This took 125 s. Every cell has the same dim, n_blocks, block multiset (rank, n_orbits, vp) and m as the committed JSON.
- At weight k, the 7/7 triples equal `s06/T5_def.json`: dim, n_blocks, m rank 1, and `vp_etaB = [0]`.
- (13, 116, 101) is skipped, with a predicted cost of 5351 s.

**Independence.** The C++ reads no files: the only stream is `std::ofstream` for `--out`, and the triples are hard-coded. Only the Python collector reads `s06/T5_def.json`, and it does so for the comparison. OK.

**Hygiene.**
- The SPDX header follows HACS's own scheme (LGPL-3.0-only WITH LicenseRef-CUDA-exception, as `code/hacs/REUSE.toml` and `licensing.md` §"new files inside code/hacs/" require).
- The collector and note headers are correct.
- The only file under `code/hacs` that the WP adds or changes is the new tool. No linked hacs file is touched.
- The word "certified" does not occur in the four files.
- Provenance (script, tool, build_cmd, binary sha, commit, date, runtimes) is present.

## Claims

1. **Weight k: confirmed.**
   - The 7/7 triples equal `T5_def.json`.
   - η^B is a unit at m, which is a rank-1 block with one degree-1 orbit.
2. **Weight k+(p−1): partly wrong. See M1.**
   - It is correct that the Gram valuations are not η^B. Here n' = k+p−3 ≥ p, so ⟨,⟩_V is not perfect on Sym^{n'}(ℤ_p²). This is also the reason `t5_compare.py:13,58` and stage-06 R3 give.
   - The skip, however, is not the right treatment.
3. **H3 reading (q, p, k): confirmed.**
   - The stage-06 tex, item "[validation] q≡−1", reads "q=13, p=7, 3≤k≤6; q=19 or q=29 with p=5, k=4".
   - Plan §4 HJ-8 lists (13,7,4), (13,7,6), (19,5,4), (29,5,4).
   - These are (q, p, k), and the cpp maps them to (q, k, p) correctly at `jl_eta_def.cpp:986`.
4. **Census skip rule: sound.**
   - Every census cell has p > k > n, p ≥ 5, p ≠ q and p ∤ q²−1. Together with w_x ∈ {1, 2, 3}, this makes G_w perfect on M⊗ℤ_p.
   - The Hecke idempotents are G_w-self-adjoint, so M⊗ℤ_p = ⊕_m M_m orthogonally.
   - If χ mod p is squarefree, each M_m is a single unramified ℚ_p-orbit A_φ = M_m, so det G_w|A_φ is a unit, that is, η^B = 1 for every m.
   - The "no level raising" condition is not needed for η^B. It is needed only so that old-congruent blocks are not dropped, and that is sound by the necessity of Ribet's condition. In the range k ≤ 20, g is unique when it exists.
   - The counts hold: 5869 − 5538 = 331 examined cells, 166 nontrivial cells and 175 blocks. Of these, 5 are multi-orbit blocks with η^B = p each, all with `all_ok`.
   - The breakdown of the 120 "unresolved" blocks is wrong. See M2.

## Findings

### Major

**M1 — weight k+(p−1): the definite-side object is available, and two statements in the note are false.**

Note line 32 says "The Gram valuations come out as −(block rank)". This is false.
- In the committed and rebuilt output, the old-congruent m block has `vp_det_gram_w = 0` in all 6 computed cells.
- Across the blocks, vp + degree takes the values 0…7. For example, (13,36,19) gives {0,1,2,3,4,5,7}.

Note line 34 says "No old-congruent m exists at k+(p−1), because dim S_k(1) > 1 there". This is false.
- The m of weight k appears at k+(p−1) with the identical residual eigensystem (ℓ ≤ 11), because g·E_{p−1} ≡ g.
- In all 6 computed cells, it is a **rank-1 block**:
  - (13,36,19): a_2..a_11 ≡ 4,10,17,1,14
  - (5,40,23)
  - (5,46,31)
  - (13,42,31)
  - (3,70,53)
  - (3,78,61)
- The tool only fails to *detect* it, because `level_one()` (`jl_eta_def.cpp:410-421`) requires dim S_k(1) = 1.

What Thm E / Cor. allweights (stage-06 tex lines 346-357) needs at k' is the ring-theoretic congruence ideal η_{f'}(M,q) of the q-new algebra T_{k'}^B localised at m, not a Gram determinant.
- A rank-1 M_m forces T^B_m = ℤ_p, and so η^B = (1). This needs no pairing.
- It agrees with the GL₂ side in `s06/T5.json`. At k+(p−1), the GL₂ side has S_new_m = 1 and ord η_new = 0 for (3,18,53), (3,18,61), (5,16,31) and (5,18,23).
- So the Thm E check at k+(p−1) can be **closed on 4 triples now**, with definite rank 1 and η^B = 1 (*computed*). The other 2 triples (13,18,19) and (13,12,31) have the definite value but no GL₂ value.

**Fix:**
- Match m at k' by the residual eigensystem of m at k.
- Report rank(M_m) and the ring-theoretic η^B, which is 1 for rank 1.
- Correct note lines 32 and 34, and the corresponding text under "Deviations", item 2 (line 46).

**M2 — 5 of the 120 "unresolved single-orbit blocks" are mixed blocks, and the note says "No errors occurred".**

The note's statement is at lines 57 and 60. The cells are (5,14,139), (17,10,11), (29,6,11), (29,8,11) and (47,14,43).
- Each block has `all_ok = false`.
- Each block mixes two residual eigensystems. For example, at (5,14,139) the T_2 residual is `(x+2)^2*(x+132)`.
- The PARI `idealprimedec` check shows a ramified orbit plus a separate degree-1 orbit in each case.

The cause is at `jl_eta_def.cpp:811`. Separation by T + cT_ℓ accepts T' only if its charpoly on the block is **squarefree** mod p. That never happens when the block contains a ramified orbit, even when T_2 already splits the block into coprime factors.
- **Fix:** split on coprime factors, using Hensel on g^e · rest exactly as at the ℚ-factor level, instead of requiring squarefree.
- The cells and blocks should then be recounted.
- The remaining 115 blocks are genuine single ℚ_p-orbits. 113 are ramified. For (31,6,13) and (31,10,23), the reviewer checked with PARI that p is unramified, with a degree-2 prime, so the explanation there is a non-maximal ℤ_p[T] rather than ramification. Note line 57 should say so.
- The claim "v_p det G_w over the union = 0" carries no information: it is automatic for any block when G_w is perfect (see claim 4).

### Minor

- **m1.** `laneC_hj8def_collect.py:50` writes `vp_etaB` and `etaB = "p^v"` (for example `19^-1`) for cells with `pairing_perfect = false`. The field name asserts η^B where the schema says it is not η^B. Keep `vp_det_gram_w` there.
- **m2.** The collector (`laneC_hj8def_collect.py:47-52`) drops `e`, `Q_factor`, `residue_of_generic_T` and `vp_ratio` from the orbits. Because of this, the HJ-6 acceptance item "v_p ratio = 0" cannot be read from the committed JSON (it is recoverable as vp_etaB − vp_det_gram_Gamma).
- **m3.** The provenance `binary_sha256` belongs to the pre-merge build. The merge 513366bf changed `Brandt2.cpp/.h` and `BrandtLevel.h`, so a rebuild gives a different sha with identical values. Record the source commit of the binary, b0dee376 plus laneC 5dfe8f6d.
- **m4.** The H3 definite side uses only T_ℓ with ℓ ≠ q, not U_q. Adding U_q (stage-06 H3) can only refine the blocks, so η^B = 1 is unaffected. Mention this in the note.
- **m5.** `level_one()` (`jl_eta_def.cpp:410-421`) contains dead code: the a/b search runs before the dim-1 test. It is harmless.

## Fix list for PASS

1. M1: report the old-congruent m at k+(p−1) with its rank and ring-theoretic η^B, and correct note lines 32, 34 and 46.
2. M2: use the coprime split at cpp:811, rerun the census, and correct note lines 57 and 60.
3. m1 and m3.

## Re-check (fixes da63fae5 … 1d29e694, merged at 558b4f9a)

**Verdict: PASS.**

**Reproduction (computed).** I rebuilt in `/home/janosch/data/hacs-build/laneC/review8d_recheck/`.
- The sha256 is `a9a33783…11a4`, which equals the provenance `binary_sha256`.
- jl_eta_def.cpp and the collector are unchanged between ffceac54, the recorded commit, and 558b4f9a.
- I reran `--suite h3` and `--suite t5` but not the census. Both are identical to the worker's dumps in `hj8def3/`, after dropping timings.

**M1: fixed.**
- `run_cell` compares the `residual_eigen` map (a_ℓ mod p, ℓ ∈ {2,3,5,7,11}∖{q}) of each block with that of the old-congruent m at weight k. It reports rank and `etaB_ring` (`jl_eta_def.cpp`, `m_from_weight_k`).
- Independent check on the rerun: in each of the 6 cells, exactly one block at k' has the weight-k m's residual eigenvalues, and it has rank 1. So `etaB_ring = p^0` is right.
- `T5_comparison` closes (5,18,23), (5,16,31), (3,18,53) and (3,18,61) against ord η_new = 0.
- Note lines 31-38 are corrected.
- Residual minor: the match would also hit residue-degree > 1 blocks if the weight-k target map were empty, and the last match wins. Neither case occurs, since every T5 weight k has a unique rank-1 old m. A guard (`!target->empty()`, unique match) would be cleaner.

**M2: fixed.**
- `split_block` splits recursively on coprime factors (Hensel on h^e · rest).
- The 5 previously mixed blocks now have a single residual eigensystem. Each is the ramified rank-2 or rank-3 part, and its degree-1 partner moved to its own block. For example, (5,14,139) is now rank 2 with T_2 ≡ x+2, and (17,10,11) is rank 3.
- No census block has `all_ok = false` (0 of 175).
- The 120 unresolved blocks are listed in `census.classification.unresolved_not_determined` with `etaB = "not determined"`, tagged 118 ramified and 2 unramified of residue degree 2. This agrees with my PARI check once the 5 mixed blocks are split.
- The counts are 5 genuine, 50 old-congruent, 120 not determined and 0 other.

**Minors.**
- **m1 fixed:** at `pairing_perfect = false`, `vp_etaB` and `etaB` are null and the method reads "not η^B … for information only". `vp_det_gram_w` is kept.
- **m2 fixed:** `e`, `Q_factor`, `residue_of_generic_T` and `vp_ratio` are restored.
- **m3 fixed:** the binary is rebuilt from the recorded commit, and its sha reproduces.
- **m4 fixed:** the U_q remark is in the note.
- **m5 fixed:** the dim-1 test now comes first in `level_one()`.
