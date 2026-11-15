<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# HACS planning master: report (2026-11-14)

1. **Files** (`plan/hacs/`): HACS-JL-PLAN.md, CHECKS-NOW.md, checks-results-2026-11-14.md, titan-hacs-build-job.md, REPORT.md.
2. **Plan:** 17 scheduled WPs plus HJ-13, which is gated on Q5 and owned by HACS.
   - Lane A (HJ-0, HJ-A1..A3): Python bridge driving `hacs --script` against our Python Brandt matrices; serves S05 T05-1 and S06 now.
   - Lane B (HJ-1..HJ-11, audits HJ-12a/b): native `code/hacs/src/jl/` module (quaternion orders, class sets, Brandt modules incl. Sym^n, Hecke, Ribet/Ihara, certified integral reads, Λ-adic, GPU census).
   - Critical path HJ-0→1→2→3→4→6→8→12b ≈ 7 h; about 14 h sequential, 8–9 h with both lanes in parallel. Implementation held.
3. **CUDA build:** CUDA detected and enabled (nvcc 13.0.48, sm_120, GCC 11.4, CMake 4.5). Built in 3:30 (CPU-only build 3:20).
   - Regressions: `--all` 246/246 on both builds.
   - Strict golden: tier A 12154 with 0 failing, tier B 6231 with 0 mismatching.
   - Device validations pass on GPU; the slow `--all-full` tier was not run.
4. **GPU vs CPU:** the outputs are bit-identical (record digests, 4 cases, 28 GPU calls, 0 fallbacks).
   - Whole pipelines gain only about 13% (`cohom`/`hecke 1000`: 13.3 s → 11.7 s).
   - The dense mod-p GEMM goes from 31 to 7900 Gmodmul/s, about 250×. The GPU pays off only for large dense mod-ℓ linear algebra.
5. **RUN-NOW checks (fresh CUDA binary): all PASS.**
   - RN-1 acceptance battery, plus CPU-vs-GPU hashes and the 0.2.0 diff, which is identical.
   - RN-2 Mazur number = num((p−1)/12) for p ≤ 199: 36 primes certified exactly, 5 consistent upper bounds, p = 13 trivial. Level-1 Eisenstein module = num(B_k/2k) for k = 12..32.
   - RN-3 Eichler class number/mass and Brandt-vs-HACS charpolys at weight 2: 42/42 primes.
   - RN-4 JL with Sym^{k−2}, k ≤ 12, D ≤ 43: 61/61 cells.
   - RN-5 HACS vs PARI charpolys on Γ0(M), M ≤ 60: 232/232 cells.
   - RN-6 T4: ord₁₇ c₃ = 1 at k = 12, 28, 44, 60.
6. **Disagreements with our Python, Lean or maths:** none.
   - Pitfall: at levels divisible by 9 or 16, the Eisenstein part has twisted eigenvalues; the scripts take that factor from PARI.
   - Limit: HACS allows Sym^n only up to n ≤ 60, so the seed's T4 case k = 124 is out of reach.
7. **Licence (Q1): DECIDED** (Fabian, 2026-11-15). New files inside `code/hacs/` follow HACS's scheme: LGPL-3.0-only WITH LicenseRef-CUDA-exception for code, Apache-2.0 for its `lean/`. Files outside `code/hacs/` are GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL; our Lean is Apache-2.0.
8. **Citations:** HACS v0.2.1, DOI 10.5281/zenodo.24231446 (code-identical to `code/hacs/`); hacs-data v0.2.0, DOI 10.5281/zenodo.24147012.
9. **Open questions for Fabian** (HACS-JL-PLAN §6.2):
   - Q2: one-line hooks in upstream files?
   - Q3: may we use `HeckeZLocal` on non-cohomological lattices?
   - Q4: may we use the owner-gated U_p emitter?
   - Q5: is a HACS definite module (slot 27) already planned, so that Lane B would duplicate it? Are W_p, α over ℤ and tame-level Hida on the HACS roadmap?
   - Q6: GPU sharing on this node.
10. **TITAN:** yes, a one-off build (job `hacs-build-01`, spec in titan-hacs-build-job.md), as a second GPU for long sweeps.
11. **Notes:**
    - The old build at `Langlandscape-wt/s03-ct/code/hacs/build` was deleted mid-session by someone else.
    - The new build directories take about 3.3 GB each and are git-ignored.
    - Raw logs are in `/home/janosch/data/hacs-run/`.
