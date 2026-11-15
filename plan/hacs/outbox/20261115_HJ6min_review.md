<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# HJ-6-min review (fresh reviewer, targeted, read-only)

Target: merge `72be8bd1` on `impl/hacs-laneB` (diff `72be8bd1^1..72be8bd1`, 11 files, +927/−4).
Scope: about 30 minutes, targeted. This is not a HACS certification. Run: `JLBrandtFreeBlockSpikeValidation` on
`/home/janosch/data/hacs-build/laneB/spike/hacs`, which gives **19 checks, 0 failing, [PASS]**. Nothing was built and `--all` was not run.

## Verdict

**PASS with one major (claim scope) and minor follow-ups.**
- The L ⊕ L adapter is mathematically correct: v_eta(L ⊕ L, r_eis = 2) = v_ℓ of the Eisenstein congruence module of L. It is neither twice that value nor the module of another splitting.
- The "multiplicity 2" diagnosis is correct.
- The reader is correct for the data it is meant to read.
- The process is clean.
- The headline "ℤ/num((q−1)/12) on 24/24 levels" overstates what was computed: only the ℓ-parts with ℓ ≥ 5 are read.

## 1. Mathematics of the L ⊕ L adapter (checked against `Integral/HeckeZLocal.cpp`)

- **Diagnosis is right.** ReadLocal's annihilator (`HeckeZLocal.cpp:1066-1079`) is `MonicSqrt(χ/(x−λ)^r)` for odd ℓ. This assumes that the cusp part occurs twice, as in H¹ ≅ S_k ⊕ S̄_k.
  - On a Brandt lattice χ = (x−λ)·c, with c the cusp characteristic polynomial. Generically c is not a square, so the read gives `not_exact` → `root = inconsistent`.
  - The spike confirms this on B_11: every op gives `not_exact`.
- **The adapter is right.** On L ⊕ L the characteristic polynomial is χ² = (x−λ)²c².
  - `DivideByRoot(·, λ, 2)` gives c², and MonicSqrt returns c. The root is unique: for odd ℓ, if (c+ℓ^j h)² ≡ c² then ℓ^j h(2c+ℓ^j h) ≡ 0, and 2c + ℓ^j h has unit leading coefficient, so ℓ^j h ≡ 0.
  - c(T) on L ⊕ L equals c(T_L) ⊕ c(T_L). Its Smith valuations are therefore a_L, a_L. This rank is 2 = r_eis, so `rank_mismatch` cannot occur. The read gives η = [η_L, η_L] and v_eta = `eta.front()` = η_L (`HeckeZLocal.cpp:1186-1222`).
  - So v_eta is the congruence module of L, not twice it.
- **The splitting is right.** For e_eis = 1 (λ = 1+p is a simple root over ℚ, since |a_p| ≤ 2√p < p+1), c_p(T_p) kills L_cusp exactly, and c_p(T_p)L = c_p(λ)·π(L) with π(L) = ℓ^{−η}L_eis.
  - The Smith valuation is a = v(c(λ)) − η, so η = v − a is the exponent of L/(L_eis ⊕ L_cusp). Since L_eis has rank 1, this module is cyclic.
  - This is the splitting along the Eisenstein line Z·(1,…,1) and its T-stable complement ker φ. It is the intended one.
- **Is the own Smith route independent? Only partly.** `OwnReads` (`JlFreeBlockRead.cpp:417-446`) uses the same formula η = v − a and the same primitives (`Charpoly`, `DivideByRoot`, `SmithValuations`) as ReadLocal's at-root read; only the square-root step is left out.
  - Agreement between the two therefore tests the adapter (the square root and the doubling). It does not test the primitives.
  - The genuinely independent checks are `v_mass` and the comparison with Mazur:
    - `v_mass` is exact integer arithmetic from |Γ_c| (`JlFreeBlockRead.cpp:449-458`). I verified the left-eigenvector symmetry |Γ_j|F_ij = |Γ_i|F_ji on B_11, and Eichler's mass formula gives v_ℓ = v_ℓ(q−1) for ℓ ≥ 5.
    - The comparison with Mazur is described under M1.
- **`d_target = d_algebra` is sound.** The fallback is the rank h, which is the correct a-priori ℤ-rank of T at prime level and k = 2.
  - On L ⊕ L the operators are diagonal, so A'_1, the power spans and the monogenicity reads are those of L.
  - ReadLocal's guard `dim_A1 ≤ d` (`HeckeZLocal.cpp:943`) therefore still holds.
  - `full_algebra = false` is harmless: the field (`HeckeZLocal.h:227`) is not read anywhere in `HeckeZLocal.cpp`.
  - `eis_rational = (k = 2 ∧ e = 1)`, and LL is run only in that case (`JlFreeBlockRead.cpp:505,518`). This is consistent.

## 2. Reader

- **Column convention.** Every quantity read is invariant under transpose: characteristic polynomials, Smith valuations, lengths of the algebra closure and of power spans, and the idempotent rank. So "no transpose" cannot change any output; it matters only for `F_fnv`.
  - `FnvRowMajor` (`JlFreeBlockRead.cpp:168-173`) builds the columns and calls `freez::MatrixFnv`.
  - The spike checks this against the Python hashes on all four ops of B_11, and it detects a tampered hash.
- **Missing T_ℓ.** The read falls back to P with `t_ell = omitted(not_in_record)` (`:494-497`), so no ENGINE_CHECK fires. The spike checks this at ℓ = 13.
- **Overflow.**
  - Matrix entries are BigInt and are reduced by `FreeBlockModQ`.
  - Scalars are limited to at most 18 digits, so they fit in int64 (`:148`).
  - ℓ^K ≥ 2^63 gives `refused(word_modulus)` before any Zlk is made (spike, 5^28).
  - Remaining issues are listed under the minor findings.

## Findings

### crit
None.

### major
- **M1. The claim covers only ℓ ≥ 5.** `JlFreeBlockValidation.cpp:163` starts the default ℓ list at p = 5, and `:168` adds 5 and 7. The ℓ-parts at 2 and 3 are never read.
  - The statement "the Eisenstein congruence module is ℤ/num((q−1)/12) on 24/24 levels" (`plan/hacs/outbox/20261115T0115Z_HJ6min_merge.md:18`) therefore overstates what was computed. For example, num(36/12) = 3 at q = 37 and num(72/12) = 6 at q = 73.
  - Restate it as: "*computed*: v_ℓ(congruence module of L) = v_ℓ num((q−1)/12) for every prime ℓ ≥ 5 dividing num, and at ℓ = 5, 7".
  - Alternatively, add the 2- and 3-parts. Note that at ℓ = 2 ReadLocal takes the non-sharp branch, so the adapter needs care there (see m3).

### minor
- **m1. Uncaught exception on a bad `\u` escape.** `JlFreeBlockRead.cpp:80` calls `std::stoul`, which throws `std::invalid_argument`/`out_of_range`. These are not `runtime_error`, so the `catch` at `:49` misses them. `ParseBrandtRecord` is called outside the `try` (`JlFreeBlockValidation.cpp:150`), so one malformed file aborts the whole run. Catch `std::exception`.
- **m2. `JL_BRANDT_ELLS` is not validated** (`JlFreeBlockValidation.cpp:132`). ℓ = 1 makes `MazurValuation` loop forever (`JlFreeBlockRead.cpp:206`), ℓ = 0 is UB, and a composite ℓ is silently accepted. `stoull` on a bad token throws outside the `try`. Require a prime ℓ ≥ 2.
- **m3. ℓ = 2 through `JL_BRANDT_ELLS`.**
  - ReadLocal uses `chi/(x−l)^r` without a square root (`HeckeZLocal.cpp:1078`, `sharp = false`). On L ⊕ L this is c², and the read still gives η (c²(T) = c(λ)c(T) on L, so v′ − a′ = 2v − (v + a) = η). It does so at double the precision cost.
  - `v_gP` stays −1, so `root = open(precision)` even though `v_eta` is set.
  - At ℓ = 2 the plain read on L would be the natural one. Document this, or refuse ℓ = 2 for LL.
- **m4. Unchecked narrowing.** D, M, k, N and the ops are cast from int64 to uint32 without a range check (`JlFreeBlockRead.cpp:237-241,256`). `R.D * R.M` can wrap, and then the `N != D*M` check can be passed by accident. In `v_mass`, `lcm` over arbitrary `gammas` can overflow uint64 (`:451`); for real data (|Γ| ∈ {2,4,6}) this cannot happen.
- **m5. "Two routes" overstates independence** (see §1). In the merge note and CHANGES, say that the own route shares HACS's primitives and formula. Name `v_mass` and the comparison with Mazur as the independent checks.
- **m6. Plain-L read as a diagnostic.** If c happened to be a square mod ℓ^K, MonicSqrt on L would succeed with a wrong annihilator. The read would then not give `inconsistent`. It is not reported as a result, so there is no harm, but do not cite "root = inconsistent on L" as a general fact beyond the spike.
- **m7. Evidence pointer.** The on-disk log `/home/janosch/data/hacs-run/laneB/read_f54b109e.log` shows `cells=74 reads=127 agree_mazur=14 differ=0 … exceptions=0`. I found no run log that shows the 24/24 tally. Commit the log or name it.
- **m8. CHANGES.md.** The roster is noted as 294 → 296, but the row for `JL.cpp` does not say that `--all` goes from 246 to 247 (the fast spike is now in `--all`, `counts.tex` `\CMNumAll`). The merge note says it; CHANGES should too.

## 3. Process: all OK

- **Hooks.** There are three marked lines: `CMakeLists.txt:1413`, and `ValidationRegistry.cpp:410` and `:1975`. Each comes directly after the last slot-27 line (`HeckeZEisUpChar`). The upstream `--list` order is unchanged.
- **Untouched paths.** `git diff --stat 72be8bd1^1 72be8bd1 -- Registry/Slot27 cmake/slot27 '*GoldenReference.inc' '*LICENSE*' '*LICENCE*' '*COPYING*' '*Emit*' '*emit*'` is empty.
- **SPDX.** All six new files carry SPDX headers. They use HACS's scheme, `LGPL-3.0-only WITH LicenseRef-CUDA-exception`, which `agents/rules/licensing.md:24-25` requires.
- **"certified".** The word appears in no JL output. `JlWord` rewrites HACS words, and the spike asserts that the string is absent from the `@@JL_READ` lines; the run output confirms `c3: met(hacs_word)`. The remaining occurrences are in comments, the sanitiser and checks that compare against raw HACS words.
- **CHANGES.md.** It lists every file and both hooks, and has a deviations section (no contract text, L ⊕ L, the options, the runs not made, `OC_ENABLE_JL = ON`, and its own JSON reader). See m8.

## Master addendum (2026-11-15, Lane B master)
- **M1 accepted.** The headline is restated: the Eisenstein congruence module agrees with the ℓ-part of num((q−1)/12) for all primes **ℓ ≥ 5** on the 14 k = 2 levels of Lane A's records (f54b109e: every prime D ≤ 43 plus B₁₁; `read_f54b109e.log`: agree 14, differ 0), plus the spike fixtures (q = 101, 131).
- **The 2- and 3-parts are read on request.** Global-master question (1), q = 37, ℓ = 3: we ran `JL_BRANDT_ELLS=3:3,3:5`. ReadLocal on L ⊕ L gives `root=closes`, `C_T=3^1_exact`, `v_eta=1` at K = 3 and K = 5. On L alone the root read is `inconsistent`. The own route gives v_cong = 1, v_mass = 1. At 37 ≡ 1 mod 12 every |Γ_x/±1| = 1, so ℓ = 3 is unproblematic there. Hence ℤ/3 is *computed* by HACS too; it is not a bug, it was just not in the default list.
- **m1, m2, m4, m8** are assigned to the next C++ WP (HJ-6b). **m3, m5, m6** are wording items for the closure.
