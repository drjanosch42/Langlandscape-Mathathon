# Validation catalogue

> **Registry paths (S24 CL-10, 2026-11-01).** Registry fragments `Registry/Slot<S>/<pkg>.cpp` and `cmake/slot<S>/<pkg>.cmake` named in this file for
> slots S <= 23 are historical: they are folded into `Registry/Slot<S>.cpp` (the package function `RegisterSlot<S><pkg>()` is kept there, called by
> `RegisterSlot<S>()` in the old order) and `cmake/sources/<Module>.cmake`; the old READMEs are in
> `docs/implementation/registry-slot-readmes-9-26.md`, the convention in force in `src/hacs/Registry/README.md`.

The per-validation encyclopaedia that used to live in `CLAUDE.md`, moved out verbatim so the
per-session context header stays short. Nothing here has been edited: every count, timing, tier,
check number and claim was exactly as it stood in `CLAUDE.md` at the hecke-extensions slot-4 close
(2026-09-22); since then the slot-5 … slot-15 packages and their closes (slot-5
WP-13, slot-6 WP-14, slot-7 WP-14, slot-8 WP-14, slot-9 WP-17, slot-10 WP-17, slot-11 WP-17, slot-12 WP-9, slot-13 WP-15, slot-14 WP-17,
slot-15 WP-17, slot-16 WP-18a) have added to it. **At the slot-16 close the roster is 169 registered validations: 61 `fast`, 92 `standard`, 16 `slow`, of
which 108 are `Hecke*`** (derived from the source at `7f36871`; six names added, listed in the slot-16 block at the end). **In slot 15 (WP-17, derived from `--list` on the merged tree `94dd3ae` + WP-17) the roster is 162 (163 after S15-O1: see the note under slot 15)
registered validations: 59 `fast`, 88 `standard`, 15 `slow`, of which 102 are `Hecke*`** (three names added, listed in the slot-15
block at the end). **The roster at the slot-13
close is 155 registered validations: 58 `fast`, 82 `standard`, 15 `slow`, of which 96 are
`Hecke*`; at the slot-14 close it is 159 registered validations: 59 `fast`, 85 `standard`, 15 `slow`, of which 99 are `Hecke*`** (slot-14 WP-17, derived
from `--list`; four names added, listed in the slot-14 block below; the slot-13 close was derived from `./hacs --list` on its close tree; 148 / 57 / 78 / 13 / 89 at the
slot-12 close, 141 / 55 / 74 / 12 / 82 at the
slot-11 close, 130 / 53 / 67 / 10 / 75 at the
slot-10 close, 125 / 52 / 63 / 10 / 71 at the
slot-9 close, 114 / 46 / 58 / 10 / 65 at the
slot-8 close, 108 / 43 / 56 / 9 / 61 at the
slot-7 close, 106 / 43 / 55 / 8 / 60 at the slot-6 close, 100 / 40 / 54 / 6 / 55 at the slot-5
close).

**How to run these**: see `CLAUDE.md` → "Validation / Tests" (`--list`, `<Name>`, `--all`,
`--all-full`, several names in one process, the tier semantics and the owner-gated emitters).
**Slot-by-slot programme history, the suite-status table with its historical figure series, the
re-baselines and the per-slot performance references**: `docs/implementation/slot-history.md`.
**Architecture detail for the units these validations gate**: `docs/architecture-detail.md`.

The catalogue is organised exactly as `CLAUDE.md` had it: the six pre-existing validations, then
one block per matrix-engine phase, then one block per hecke-extensions slot.

---

The six pre-existing (non-Hecke) validations:
- `mod_arithmetic_validation()` — modular arithmetic ops (incl. the `p >= 2^31` boundary cases)
- `MatrixValidation()` — Matrix class (incl. the RREF-cache-invalidation regression: 12 checks; since slot-24 CL-M
  without the print-only change-of-basis / factor-basis demo, whose deprecated free functions were deleted)
- `FlatMatrixValidation()` — FlatMatrix class (119 tests since slot-14 WP-3: the G1 arm, `rows·cols ≥ 2^32` on
  scalar / empty-data shapes, nothing allocated — `65536 × 65536` with empty data refused, the scalar reads, and
  materialising `(2^32−1)²` refused by the `size_type` `ENGINE_CHECK`)
- `BlockFlatMatrixValidation()` — BlockFlatMatrix class
- `SimplicialCohomologyValidation()` — simplicial cohomology on standard spaces
- `LocalSystemCohomologyValidation()` — equivariant cohomology on local systems

Added in matrix-engine Phase 0:
- `SubstrateDifferentialValidation()` — cross-checks `Matrix` vs `FlatMatrix` vs
  `BlockFlatMatrix` (RREF / rank / kernel / image / product / inverse, cache-coherence
  sequences, algebraic identities) over `p in {2, 3, 7, 23, 134217757, 2^31-1, 2^32-5, 2^61-1}`
  and both element widths; 774 cases.
- `GoldenRegressionValidation()` — the bit-exactness backbone. Recomputes 14049 objects over the
  `(n_sym, ell, p_hecke, r, q)` grid of `Golden/GoldenHarness.cpp` and compares FNV-1a-64 hashes
  against the frozen `Golden/GoldenReference.inc`, which was emitted at `-O0` from the code as it
  stood *before* the Phase 0 fixes. **Tier A (9446 entries) gates**: dimensions, `Θ^{(q)}_flat`,
  char-poly / rank / trace of every `A^{(q)}`, decomposition invariants, normalised JSON. **Tier B
  (4603 entries)** — legacy bases, projectors, change-of-basis matrices — is compared and reported
  but fails only under `GOLDEN_STRICT=1` (owner decision Q1: the engine must reproduce the
  canonical objects, not the legacy basis choices).
- `GoldenEmit()` — regenerates `Golden/GoldenReference.inc`. **Owner-gated re-baseline**: it is a
  no-op unless run as `GOLDEN_EMIT=1 ./hacs GoldenEmit` (optionally `GOLDEN_OUT=<path>`),
  so `--all` stays read-only. Every changed line of a re-baseline must be explained object by
  object.

Added in matrix-engine Phase 1 (all four are `standard` tier except where noted):
- `SymmetricPowerValidation()` — pins the new `O(d_V^2)` `ComputeSymmetricPowerMatrixFM` (closed
  forms `[C1]`–`[C6]` + the two recurrences `[R1]`/`[R2]`, see the branch table at
  `FlatMatrix.cpp:1440`) bit-for-bit against `ComputeSymmetricPowerMatrixFM_reference`, the
  pre-Phase-1 double-sum route kept alive solely as this oracle. Exhaustive small-`n` sweep, the
  spot grid `n_sym in {64, 96, 128, 160}`, and structural checks (closed forms vs independent
  Pascal/power oracles, `ρ_n(A)ρ_n(B) = ρ_n(AB)`, `ρ_n(A)^{-1} = ρ_n(A^{-1})`) that need no
  `O(n^5)` reference and therefore cover the large-`n` regime.
- `SymmetricPowerValidationSlow()` — **`slow` tier**; the same comparison against the `O(n^5)`
  reference over the wide grid.
- `ThetaEqSolveValidation()` — the multi-RHS `Θ_eq` solve (`change_of_basis_fm_multi`, one
  augmented RREF for all `dim C^q_eq` right-hand sides) against the old per-vector
  `change_of_basis_fm`, on the golden grid, plus the exact residual certificate and rejection of
  out-of-span vectors.
- `VacuousRelationValidation()` — the vacuous-relation short-circuit in `A_Cq`/`A_Zq`
  (`M == I` skipped, `M == αI` emitted as a scalar block) against the pre-7.4 code path:
  dimension tables for even and odd `n`, so the odd-`n` `H^* = 0` semantics stay exact.

Added in matrix-engine Phase 2 (the arithmetic engine — see "Matrix engine" under Architecture;
all five are `standard` tier and run in `--all`):
- `ModContextValidation()` — every `ModCtx` primitive (`mod_mul_barrett`, Shoup, Montgomery-64,
  `batch_inv`) against the old `mod_*` at all regime boundaries
  `p in {2, 3, 2^26.5±, 2^27, 2^31-1, 2^31+11, 2^32-5, 2^61-1, 2^63-25}`, 10^6 fixed-seed samples
  each, plus the `k_max` overflow assertion.
- `KernelBitIdentityValidation()` — `engine::kernels` GEMM/GEMV/TRMM/transpose against
  `RefLinAlg` **and** against the pre-Phase-2 `FlatMatrix`, on fixed-seed inputs at sizes
  `{1, 2, 7, 16, 17, 64, 65, 129, 256, 517}`, all four layouts, both element widths,
  rank-deficient and structured inputs.
- `DenseElimValidation()` (**split** by S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — 73,559 checks on `engine::elim`'s blocked in-buffer PLU/RREF and the
  bases derived from it (kernel, image, `solve_multi_rhs`, complement), against the legacy
  elimination core selected by `engine::elim::ScopedLegacy`.
- `DenseElimPipelineValidation()` — the same, but through a real `A_Cq` and a whole cohomology
  run, i.e. the consumer's own matrices rather than synthetic ones.
- `PerformanceSmokeValidation()` — coarse floors that catch a silent loss of the AVX-512 path:
  GEMM 512^2 >= 4 Gmodmul/s and RREF 1677x1419 <= 8 s. **Its default backend is `engine`**;
  `ENGINE_BACKEND=legacy` selects the legacy arm together with the (much lower) legacy floors.

Added in matrix-engine Phase 3 (the block model and the consumer migration — see "Block model
(Phase 3)" under Architecture). Every one of these compares **bases entrywise, never by span**
(plan D5b: `verify_flat_kernel_properties` / `verify_flat_image_properties` check only span and
rank and would not catch a changed basis choice):
- `BlockMatValidation()` — **`standard`**, ~3 s. 56,952 entrywise checks on the model's structure
  over both element widths and the Phase-0 boundary primes: `BlockPool` dedup / refcount /
  collision chains / entry-address stability, every `BlockRef` kind (transposed windows and
  `αI + βM` pencils included), CSR determinism, `BlockBuilder` kind folding, zero-width
  partitions, `BlockView`, relayout, `blk::gemm` / `gemm_dense` / `add` / `scale` / `equal`
  against the `RefLinAlg` oracle, and the `to_flat` / `from_flat` round trip against a
  hand-written `s*d_V + k` loop (the L1 contract).
- `BlockEliminationValidation()` (**split** by S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**, ~43 s, the single largest entry in `--all`.
  10,121 checks: block RREF / pivots / `kernel_basis` / `image_basis` / `factor_basis` /
  `solve_multi_rhs` entrywise against `engine::elim` on the flattened matrix **and** against the
  legacy `BlockFlatMatrix` (`flat_kernel`, `flat_image`, true RREF, `factor_basis_block`,
  `change_of_basis_fm`, through `ScopedLegacy`), on `A_Cq`-shaped (`I` / `-M` / `I-M`),
  `A_Zq`-shaped (pencils), generic and rank-deficient inputs, `d_V in {17, 65, 129}`. A sweep of
  the panel width proves panel widths, pivot-row choices and GEMM blocking never reach the output.
- `BlockModelPipelineValidation()` — **`standard`**, ~11 s. The same claims on the *real*
  `A_C0/1/2` of the SL(2,Z) model at `n_sym = 128` (both short-circuit modes) and on the real
  `W^1 = C^1/Z^1` and `H^1 = Z^1/B^1` problems lifted out of a `compute_cohomology()` run.
- `CohomologyBlockModelValidation()` — **`standard`**, ~0.5 s. Pins the
  `EquivariantCohomologyOnK` migration inside one process: 57 local systems, 10,792 checks
  comparing the engine arm entrywise with the kept legacy arm
  (`EquivariantCohomologyOptions::ScopedLegacyCohomologyPath`) — `dim H^q`, the C/Z/B/H_eq lists
  and the projectors with their legacy shape conventions — plus, on both arms, the `*_block`
  accessors against the `FlatMatrix` ones (`nbc == 1`, the `(N_q, d_V)` partition, `to_flat`
  column `t` == cochain `t`) and the certificates `A_Cq X = 0`, `P_q H_eq = I`, `P_q B_eq = 0`.
- `HeckeThetaBlockValidation()` — **`standard`**, ~0.4 s. 65 cases, 4,745 checks: engine arm vs
  the forced legacy arm (`HeckeOperatorOptions::ScopedLegacyHeckeOperatorPath`) entrywise on
  `Θ^{(q)}_flat`, `Θ^{(q)}_eq`, `A^{(q)}` and the whole `to_json()` text (certificate counters
  included); `Theta_block(q)` vs `get_Theta_flat_matrices()[q]`, with the structural non-zeros
  confined to the τ-table's `(σ, σ_k)` pattern; and
  `apply_Theta(q, e_b) == Θ_flat[:,b] == apply_route2(q, e_b)` on the full standard basis.
- `BarCocycleSolverValidation()` — **`fast`**. The `BarCocycleH1` RREF-with-RHS solver, absorbed
  into `engine::elim::solve_multi_rhs`, against a frozen byte-for-byte copy of the pre-Stage-B
  body on 1,830 fixed-seed systems over `ell in {5, 13, 691, 134217757, 2^31-1, 2^32-5}` —
  verdict *and* entrywise coefficients — including rank-deficient column sets, zero and
  duplicated columns, out-of-span right-hand sides, wide/tall/empty shapes and `Kc = 0` with
  `b != 0`, i.e. the cases the production call sites never reach.
- `ConsumerMigrationValidation()` — **`fast`**, ~0.05 s. The static migration gate: it locates
  the source tree (two independent routes, `OC_SOURCE_DIR` baked in by CMake and walking up from
  `/proc/self/exe`), runs each script in `docs/matrix-engine/tools/` that is present, and fails
  on any site outside that script's allow-list. `raw_mod_calls.sh` is **required** (currently
  195 sites, **0 outside the allow-list**); `check_matrix_includes.sh` is probed, not required,
  so a tree without it reports SKIP rather than failing.
- `MatrixRetirementValidation()` — **`fast`**. The Phase 3 exit criterion "zero `Matrix` includes
  outside `MatrixValidation` / `HeckeModuleDecomposition`" is a property of the source tree, so it
  is checked by running `docs/matrix-engine/tools/check_matrix_includes.sh` over the checkout via
  `std::system`. That script owns the allow-list (`ModArithmetic/` itself, every `*Validation.*`,
  `HeckeModuleDecomposition.*`, `FpPoly.*`, `SubspaceOps.*` (the verbatim E0a move out of the
  first), `HeckeExt/HeckeIdentityCertificate.*`, `HeckeExt/HeckeLocalAlgebra.h` and
  `HeckeExt/HeckeBoundary.*` (slot 1 WP-2, slot 2 WP-4 / WP-7: "`MatrixT<uint32_t>` for everything in
  `HeckeExt/`"), and the two read-only consumers of the `Matrix`-typed
  `A^{(q)}`: `Golden/GoldenHarness.cpp` and `Bench/BenchDriver.cpp`) with a reason per entry;
  *removing a file from it is the unit of progress*. It checks DIRECT includes only — `Matrix.h`
  stays reachable transitively through `FlatMatrix.h`'s conversion constructor, by design.

Added in matrix-engine Phase 4 core (the tape — `ENGINE_API.md` §10; all five `standard`, in
`--all`, timings from the final tree):
- `EngineTapeValidation()` — **~1.5 s**, 7233 checks. Record → passes → execute against direct
  `engine::blk` / `engine::kernels` execution, over every op, both element widths and every pass
  setting (fold, CSE/fusion, layout, k-split, batching, arena, device), plus a `device=gpu` arm.
- `EngineTapeEliminationValidation()` — **~4.5 s**, 8489 checks. The tape panel driver
  (`TapeElim`) against `engine::blk` entrywise on RREF / `kernel_basis` / `image_basis` /
  `factor_basis` / `solve_multi_rhs`, including the identity-augmentation-free `factor_basis`
  (7330 panels, 11514 programs, 97882 nodes in one run).
- `EngineDeterminismCoreValidation()` — **~5.3 s**, 36 arms. FNV-64 hashes identical across
  `ENGINE_THREADS ∈ {1,4,16,32}` × `ENGINE_BATCH`, and under `arena=0`, `layout=0`, `cse=0
  fuse=0`, `device=hybrid`, over `p ∈ {134217757, 2^31−1, 2^61−1}`.
- `EngineArenaValidation()` — **~0.07 s**, 447 checks: temp lifetimes, arena vs owned storage, a
  poisoned arena, replay reuse.
- `EngineCoreScalingValidation()` — **~4.3 s**, 12 checks; identity-gated, throughput reported.
  It is where `EngineCostModel.h`'s CPU constants are re-measured: on the final tree the dense
  2048³ program runs at 28.3 / 115.1 / 307.8 / 371.5 Gmodmul/s at 1 / 4 / 16 / 32 threads
  (10.9× at 16) and the Θ-like batched program at 20.8 → 245.4 G (11.8×).

Added in matrix-engine Phase 4 Stage B (the consumers on the tape — `ENGINE_API.md` §10.9; both
`standard`, in `--all`):
- `EngineTapeConsumerValidation()` — **~0.45 s**, 246 checks: the tape path vs the direct
  `engine::blk` path entrywise on the consumers' stored objects; program-cache replay == fresh
  recording == forced fresh compile (also on another pool size); a changed τ pattern misses the
  cache.
- `EngineDeterminismValidation()` — **~1.5 s**, 8 arms × 4 cells. The golden grid's small/medium
  cells in process under `ENGINE_THREADS ∈ {1,4,16,32}` × `ENGINE_BATCH ∈ {0,1}`: 966 records per
  arm, every record equals the reference (both tiers) and every arm's digest is identical
  (`0xe446b3bd2d28bd6e` since the 2026-09-16 `hecke_report/v2` re-baseline — 30 of the 966
  records per arm are `report_*` texts, so the digest is a function of them, see
  `docs/matrix-engine/rebaseline-2026-09-16-hecke-report-v2.md`; it was `0x2fa804dae5e9d98d`
  after the 2026-09-16 re-baseline of the canonical τ — the ι-symmetric tie-break and
  tree-routed path templates, `docs/matrix-engine/rebaseline-2026-09-16-iota-symmetric-tau.md`
  — and `0x8c1fd2b31a07c778` before that).

Added in matrix-engine Phase 5 (the CUDA backend — see "Matrix engine (Phase 4–5)" under
Architecture; `ENGINE_API.md` §11–§12). **Every one of them prints `[SKIP]` and returns 0 without
a usable device**, so `--all` is green on a GPU-less machine:
- `CudaBitIdentityValidation()` — **`standard`**, ~7 s, **10,844 checks**. Every device kernel
  against its CPU twin by `memcmp` — GEMM (all four layout combinations, tiles, split-K),
  `GemmBatch`, GEMV, AXPY/SCAL, copy/transpose, canonicalise, TRSM — over every regime
  (`u32` Barrett / Shoup / Barrett-64, `u64` Montgomery and the wide path) and edge shapes. The
  contract is byte identity, never a tolerance.
- `CudaTransferValidation()` — **`standard`**, ~0.8 s, 27 checks: residency transitions, the
  pinned staging pool (chunk recycling through events, peak = cap), the device arena.
- `EngineCrossDeviceValidation()` — **`standard`**, ~13 s, 372 checks: Θ-like `gemm_dense`
  (replayed), block × block, the elimination driver, gather / scatter / `COMPARE`, the op set, a
  scaled batched program and a `k = 4200` GEMM, over `p ∈ {134217757, 2^31−1, 2^32−5, 7}` (u32)
  and `{2^61−1, 134217757}` (u64) under 10 settings (`cpu`/`gpu`/`hybrid` × threads × batching ×
  graph mode × verify) — hashes identical everywhere.
- `EngineCudaMemoryValidation()` — **`standard`**, ~2 s, 31 checks (17 before slot-14 WP-3): a 144 MB operand through
  the 128 MB pinned pool, `pageable_copies == 0`, and the arena's `live_bytes` back to baseline
  after `release_device_state()` and after executor teardown; since slot-14 WP-3 arm **(H)**: two GEMM workloads
  with shifted shapes in one process — `release_device_caches()` returns every idle slab and the pinned pool, the
  second workload WITHOUT a release grows the arena (192 → 320 MiB, the counterfactual), and after a release run 2's
  high-water is ≤ run 1's + one 64 MB slab (192 / 192 MiB).
- `EngineDeviceTrapValidation()` — **`slow`**, ~9 s, 14 checks. The unblocked-kernel trap table
  (plan §14.4): `cpu` / `gpu` / `hybrid` wall times, transfers included, for the elimination
  driver, a Θ-like program, a 4096³ GEMM and two batched small-block programs. **Gated on
  identity only** — the timings are reported, never asserted, so a slower box cannot fail it.

Added in matrix-engine Phase 6 (the campaign driver — see "Campaign driver (Phase 6)" under
Architecture):
- `CampaignSmokeValidation()` — **`standard`**, ~1.2 s, 1045 checks: 548 objects pinned against
  20 individual campaigns and `GoldenReference.inc`, plus the batching seam's own contract — the
  same spec at four `jobs × threads` splits must produce the same jobs in the same *order* with
  the same objects, `dim_H`, char-polys and C3–C6 certificates as the sequential arm, and a
  `summary.tsv` byte-identical outside its two timing columns (2192 objects compared
  concurrently) — and, since 2026-09-16, the **job-id / shape-signature regression**:
  `Job::id()` is injective on a 112-point grid that varies the reported degree list, the
  default-degree id is byte-unchanged (`n16_ell5_p2_r1`), two jobs differing only in degrees have
  distinct ids, shape signatures and resume paths, and a two-degree-list campaign writes four
  files and then resumes all four (`docs/matrix-engine/campaign.md` §4 "Job ids").
- `CampaignCertificateValidation()` — **`fast`**, ~0.05 s, 38 checks: the JSON records the
  `certify` mode it ran in, and the in-process certificates C3–C6 ran unconditionally in **every**
  mode, `certify = none` included.

**Added in hecke-extensions slot 1** (2026-09-16, branch `hecke-extensions`; the slot changed **no
golden value** — `GoldenReference.inc` and `tau_table_p2.txt` are byte-identical; the close is
`docs/implementation/slot1/WP-7_report.md`). The roster, one line each, with the detailed
per-package paragraphs below:
- `HeckeLocalityValidation` (**split** by S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**, ~6.4 s (slot 1 WP-1 + slot 2 WP-1): the locality
  certificate `hecke::CertifyLocality`, **since E0b the one the refinement loop itself
  enforces**, on constructed non-local / local / trap families, on the settings layer, and on
  the whole golden grid — verdict **every block local**, `witness_changes = 0`,
  `loop_disagreements = 0`.
- `HeckeLocalityProbe` — **`slow`** and interlocked on `HECKE_LOCALITY_PROBE=1` (WP-1): the
  `(160, 691)` probe on `{T_2, T_3, T_5}`, recorded, not asserted — seven blocks
  `2:1 1:1 2:1 2:1 4:2 6:3 10:5`, all local.
- `GoldenDump` — **`fast`**, owner-gated on `GOLDEN_DUMP=<dir>` (WP-1): the before/after object
  dump for E0b's re-baseline protocol, diffed by `docs/matrix-engine/tools/golden_explain.py`.
- `HeckeIdentityValidation` — **`fast`** (WP-2): the slot-1 subset of the identity certificate on
  ten pipeline points plus a four-way tamper arm.
- `HeckeSturmBoundValidation` — **`fast`**, ~0.011 s (WP-3): the computed Sturm bound
  `B'(k, ell)`, 20 pinned bounds, the certificate, and the R3 resume-invariance arm.
- `HeckeExtArchitectureValidation` — **`fast`** (WP-3): the `HeckeExt/` one-way include guard
  (`check_heckeext_includes.sh`).
- `HeckeBoundaryTauValidation` — **`standard`**, ~0.03 s (WP-4a): the certified `Γ`-level `τ_∂`
  over `Z`, `obl:taubdry`(i)–(iv), 138 tables.
- `HeckeBoundaryOperatorValidation` — **`standard`**, ~5.5 s (WP-4b): the boundary Hecke operator
  `Θ^∂`, routes A/B, the `χ_b` oracles, the `β_j` negative control, `r^q` equivariance —
  `obl:taubdry`(v)–(vii), 546 cells.
- `ConsoleC0Validation` — **`fast`**, ~0.03 s (WP-5): the console language core, 612 checks,
  STL-only.

**Added in hecke-extensions slot 4** (2026-09-22, branch `hecke-extensions`, `9ae1d7a..` the slot-4
close; the close is `docs/implementation/slot4/WP-11_report.md`). **The slot changed no golden value
and emitted no golden entry**: `git diff 9ae1d7a` is empty for `Golden/GoldenReference.inc`, for
`docs/implementation/tau_table_p2.txt` and for `Hecke/HeckeReport.{h,cpp}` (the extension record is
a **separate writer**, never an extension of `BuildHeckeReportJson`), tier A 9446/0 and tier B
4603/0 under `GOLDEN_STRICT=1`, digest `0xe446b3bd2d28bd6e` on all 8 determinism arms. Every new
golden collector (`ext_ideals^q`, `ext_certify^q`, `ext_json_canonical^q`, `sturm_bound`,
`charpoly_iota^q`, `rank_iota^q`, `dim_Hplus^q`, `dim_Hminus^q`, `eisenstein_line_defined`,
`iota^q`) is defined and called **from its own validation only** — never from `RunCell32` /
`RunCell64`, where a call would be an emission in effect. Five new registered names
(89 → **94**; `fast` 36 → **39**; `standard` 48 → **50**; `slow` still **5**; `Hecke*` 45 → **49**),
one line each:
- `HeckeInvolutionValidation` — **`standard`**, ~2.2 s, **2954 checks** (WP-3, E3): the
  **production** `ι^*` of [C] `sec:involution` (`Hecke/HeckeInvolution`) and the sign split
  (`HeckeExt/HeckeSignSplit`). Until slot 4 `ι^*` existed only inside two *validations*
  ([C] `sec:codemap`: "no production `ι^*` exists"); this is the object [C] specified for it,
  **verbatim** — an `EquivariantCochainComplexMorphismOnK` through the general constructor whose
  `FiberBlockTable` holds one `PerSimplexBlock` per simplex (source `|ι_K σ|`, block
  `−ε_σ ρ_n(ι)`, the sign of `lem:iotamodel` **negated** per `def:iota`(iv) v1.2.0 and folded into
  the matrix), so it carries no data beyond the one interned `d_V × d_V` diagonal
  `ρ_n(ι) = diag((−1)^{n−j})`. `ι_K` is *proposed* by an exact `QuadPoint` match of `z ↦ −z̄`
  against the shipped `vertex_position` and then *certified* against `lem:iotamodel` (invariant
  I8). `compute()` discharges `obl:iota`(i), (ii), (iii) and **aborts** on failure — with
  (iii-a)/(iii-b) decided **blockwise and exactly** (`ι_C² = id` reduces to `ε_{ισ} = ε_σ` and
  `ρ² = I`; `ι_C d = d ι_C` to `D[ι t][ι s] = ε_t ε_s D[t][s]` over **Z**), so the cost is
  `O(N_q²)` integer work and the verdict is a *proof*, while the dense matrices are compared
  entrywise by the validation. Clause (iv) is `HeckeIotaTauSymmetryValidation`'s; clause (v) is
  `HeckeSignSplit`'s: `[ι^*, A^{(q)}] = 0` **asserted** at `ℓ ≥ 5` and **recorded** at `ℓ = 3`,
  `A^{(q)}_±` by an exact solve, the per-sign decomposition beside the unsplit one, cyclicity per
  sign through slot-2 WP-4's certificate (a), and the **Eisenstein line** `soc(X^+_{4,m}) = m_S
  X^+_{4,m}` of [E] D6 — `"undefined"` off `dim_F = 1`. The `±` split of `prop:iotasplit`(1) is
  stored on `C^q_eq`, `Z^q_eq`, `B^q_eq` and `H^q_eq`; at `ℓ = 2` `sign_split = not_applicable`
  with clause (2)'s `a`/`b` recorded. **The acceptance is entrywise against an independent
  construction**: WP-3 exports `HeckeIotaSignValidation`'s builders as `hecke::iota_oracle`
  **value-preservingly** (that validation's printed lines, `checks=4104267 gating_failures=0`
  included, are byte-identical), and the production object reproduces its reference line *field
  for field* — `IOTA_SIGN_PRODUCTION eisenstein=plus (geometric=minus) cells=77 signed=74
  route_a=74 route_b=53 both=53 split_match=66/66 split_mirror=0/66 dickson=11 h0_anchor=-1
  (geometric=+1)` — with route (b) through the **production** restriction
  (`Hecke/SL2ZBoundaryPair`), so the 53 agreeing cells are an independent confirmation. Also: at
  `(10, 691)` `dim H^1_± = (2, 1)`, cyclic on both signs, the Eisenstein line **defined** and in
  the bottom Loewy layer while the unsplit socle is 2-dimensional ⇒ `"undefined"`; the unsplit
  blocks the direct sum of the per-sign ones **block by block** (matched by `SameMaximalIdeal`);
  `r^q ι^* = ι^*_∂ r^q` and `D_c ι_c = ι_c D_c` asserted, with `dim H^q_{c,±} = (1, 2)` at
  `(10, 691)` — the **mirror** of `H^1`'s `(2, 1)`, confirming [C] `rmk:iotapairing` — and
  `[ι_c, A_c^{(1)}(T_2)] = 0` **recorded, never asserted** (it needs `ι h = h ι` on the stored
  `C_eq`, which no [C] statement provides); and a tamper arm in which a flipped orientation sign
  fails `obl:iota`(i) *by name* and `+ι^*_geo` fails **exactly** the degree-0 anchor `ι^* = −1` on
  `H^0(Γ; F_ℓ)` at `n = 0`. `check_matrix_includes.sh`'s `Matrix.h` list gains
  `HeckeExt/HeckeSignSplit.h`.
  PERF1 audit R2: the iota carry checks (iii-c) call `engine::elim::column_rank_profile` directly, but fall back to the `FlatMatrix` route under `use_legacy()` (`ENGINE_BACKEND=legacy` / `ENGINE_SHADOW_LEGACY`); prints `IOTA_CARRY_ROUTE use_legacy=<0|1> legacy_route_calls=<n>` and fails if legacy is active and the count is 0. The cone's span tests stay engine-direct (their twin is `CONE_SPAN_SHADOW`).
- `HeckeExtRecordValidation` — **`fast`**, ~0.04 s, **381 checks** (WP-1, E2a): the extension
  record `hecke_ext/v1` (`HeckeExt/HeckeExtRecord.h` + `HeckeExt/HeckeExtReport`, a **separate
  writer** from `hecke_report/v2`, which the slot does not touch) — the [E] §7 key set on a
  constructed record and on the real `(10, 691)` bulk record built from the shipped pieces under
  `u_ell = off` (`dim H^1 = 3`, one local block, `A_S = F_691[ε]/ε²`, Stage 5's
  `loewy = socle = [2,1]` and the `[0,1]` structure map of [E] §7's worked example, (b)
  `excluded_by_socle_bound`, (c) `sturm(B' = 2)`, `final = true`); the **one tri-state**
  `hecke_ext::Final` of `HeckeExt/HeckeExtFinal.h`, to which `SturmFinal` / `SturmFinality` are now
  aliases, with its fixed reason list accepted and rejected; `is_final`'s truth table over
  `final_mode × sturm_unavailable × {proof range, heuristic range, none}` with every reason, plus a
  9216-point grid on which the **default configuration never produces `"heuristic"`**; the
  per-complex degree fields of [C] `sec:recordschema` item 5 (a `set` `q_max` on an untruncated
  complex and a complex with no degree count both **refused**); `not_applicable` at `n = 0`; the
  R3.1 item-6 **sidecar** round trip on a forced-oversize state (relative path, FNV-1a-64, reload
  byte for byte, the no-stem `state_oversize` rule, the same-kind disambiguator); the two new
  mathematical keys **`commutant_budget`** (default `kCommutantBudget = 2·10^10`, whose one
  definition now lives in `Hecke/HeckeSettings.h` with `CommutantRoute::kCommutantBudget` a
  `constexpr` alias; `CommutantRoute` reads the setting, and its R3 resume refuses a lower budget
  and equals a fresh run modulo `budget_history`) and **`final_mode`**, both appended so the
  all-defaults fingerprint is still `0`; the campaign job-id arm (`n16_ell5_p2_r1` byte-unchanged,
  `_s<16 hex>` after any `_q` tail on a non-default setting, distinct ids / shape signatures /
  resume paths, a mathematical key parsed by the spec and refused with the engine's own message);
  and a concurrency arm (two `std::thread`s under two budgets, and a `jobs = 4` campaign with a
  non-default key) that is **`CheckThread`-clean**.
- `HeckeExtRamanujanValidation` — **`standard`**, ~4.0 s, **295 checks** (WP-2, E2b):
  [E] `cl:ramanujan` (Claim 8.1) at `(10, 691)` **through `HeckeExt/HeckeExtDriver`**, the Stage
  1–5 orchestration that turns a cell into WP-1's `hecke_ext/v1` record. The
  **basis-independent** checks first: `U_691` inside the frozen `u_ell` budget (104.06 MB
  predicted against 2048), `S_0 = {2,3,5,7,691}`, one local ideal with `T_m ≅ F_691[ε]/ε²`
  (`D = 3`, `f = 1`, `ν = 2`, Gorenstein, embdim 1), the **four** exact identities in
  `M_3(F_691)` — `3(T_3−252) = 256(T_2+24)`, `3(T_5−4830) = 174(T_2+24)`,
  `3(T_7+16744) = 137(T_2+24)` and **`3(U_691−1) = −542(T_2+24)`**, the strongest single test in
  [E] since it exercises `U_ell` and `τ(691)` — the eigenvalues `667, 252, 684, 531, 1`, Jordan
  type `(2,1)` for every `T_q − τ(q)` re-derived from the nullity sequence, Loewy `= socle =
  (2,1)`, and the generation verdict (a) `not_cyclic` / (b) `excluded_by_socle_bound` with the
  independent naive `dim End_{A_S} = 5 ≠ 2` / (c) `sturm(B' = 2)`, `generators_certified = [2]`,
  **`final = true`**; then the **basis-dependent** pins `T_q = a_q I + c'_q E_31`
  (`c'_q = 23, 120, 643, 129, 221`), labelled as such because they depend on the stored `H^1`
  basis, a golden tier-B object. Plus the **streamed-operator** arm at `(22, 5)` and `(26, 7)`
  (same `S_0`, same blocks, only the route differs: the streamed `T_q|_V` equals the family-built
  one **entrywise** and the whole record is byte-identical); the **`u_ell` resume** of [X] §1.3.1
  R3.3 item 4 (`budget_mb=64` refuses `U_691` and emits a `resumable {kind: "u_ell"}`, `resume(32)`
  is refused by name, `resume(2048)` reproduces a fresh `u_ell = auto` record **byte for byte**, a
  resume on an included verdict is a strict no-op, and `u_ell = off` forms no prediction); the
  **Stage-3 fast path** (consuming the block's certified locality data) equal **entrywise** to
  re-deriving it on `ŵ`, every `n_p` and every `A_S` basis element; and the `n = 0`
  (`not_applicable`) / odd-`n` (no ideal) edges.
- `HeckePredictionsValidation` — **`fast`**, ~0.7 s, **113 664 checks** (WP-7, E6): the two E6
  pre-record units. **`HeckeExt/HeckePredictions`** — `bernoulli_mod(w, ell)` by the `F_ℓ`
  recursion `Σ_j C(w+1, j) B_j = 0`, valid for `w < ℓ − 1` by von Staudt–Clausen, with the named
  `BernoulliOutOfRange` outside it, and `kummer_divides(k, ell)` = `ℓ | num(B_k/k)` total on even
  `k ≥ 2` by three provable branches (`von_staudt_clausen` / `direct` / `kummer_congruence`);
  **`HeckeExt/GloverFactors`** — the Glover / Ash–Stevens composition factors `Sym^{n_i} ⊗ det^{j_i}`
  of `Sym^n(F_ℓ^2)` as a `GL_2(F_ℓ)`-module, by the θ-multiplication recursion, in the pipeline's
  own `ρ_n` convention. Arms: **the pin** — `HeckeBoundary`'s `num(B_k/k)` table (`k ≤ 26`)
  reconstructed **as an integer** from `bernoulli_mod` alone by CRT over four `2^30` primes,
  **13 of 13 entrywise**; the same reconstruction to `k = 42`; the **Worpitzky/Stirling** closed
  form as an independent second formula for every `w < ℓ − 1` at every prime `ℓ ≤ 131` (1819
  values) and sampled to `w = 3615`; the Kummer congruence on 3252 triples; the predicate against
  integer divisibility on 735 `(k, ℓ)` cells plus the four named divisors, the regularity of every
  prime `ℓ ≤ 31` and the irregular pair `(37, 32)`; the refusal at `w ≥ ℓ − 1`; Glover's structural
  invariants on 2970 decompositions (`ℓ ≤ 691`, `n ≤ 4ℓ+5`); and **Glover against the Brauer
  character of the real `ρ_n`** on every `ℓ`-regular class of `GL_2(F_ℓ)` — eigenvalues read off
  the characteristic polynomial of the matrix `ComputeSymmetricPowerMatrixFM` returns (Hessenberg
  over `F_ℓ`, roots over `F_{ℓ²}`, the Hessenberg routine cross-checked against `det(xI − ρ_n(g))`
  at every `x`) — on **3848 `(class, n)` cells**, 531 of them in `SL_2(F_ℓ)`, at `ℓ ∈ {2,3,5,7}`
  with `n ≤ 3ℓ` and `ℓ = 11` with `n ≤ 2ℓ`. **`HeckeExt/HeckeBoundary`'s pinned table is
  deliberately not rewired** (that moves its recorded `harder_applicable` for `k > 26`; slot 5,
  with the record integration).
- `ConsoleScriptEmit` — **`fast`**, owner-gated on `CONSOLE_EMIT_EXPECTED=1` (WP-5, console C1b):
  regenerates the `.expected` transcripts of `Console/scripts/`, exactly as `GoldenEmit`
  regenerates `GoldenReference.inc`. A no-op otherwise, so `--all` stays read-only; it refuses to
  freeze a script that does not exit 0. The **first** emission was part of C1b — a new artefact,
  nothing re-baselined — and every hash line in those files is cross-checked by
  `ConsoleScriptValidation` against `golden(...)` at fingerprint `0`.

And, extended rather than added in slot 4:
- `ConsoleScriptValidation` (WP-5) is now **~3 s, 259 checks** (was 174) and compares each of the
  **16** numbered scripts' transcripts against its frozen `.expected` (`#! oc-format 1`, `#~`
  annotation lines excluded); its registration arm asserts the C1b surface is *present*
  (`decompose` / `report` / `crosschecks`, `Decomposition` / `Block` / `Report`, `Decomposition`
  filling `TypeInfo::hash`) and that the C2/C5 reserved names are still absent; and it registers
  the extension verbs from `HeckeExt/` on its own registry. `ConsoleC0Validation`'s tree arm is
  narrowed from "no `.expected` under `Console/`" to "no frozen transcript names a pre-E0b
  decomposition object".
- `ContractCensusValidation` (WP-6) gains **four scratch arms** for the content-keyed
  `label_census.allow` (below, "Migration tools"): a line inserted above an allow-listed site
  leaves the census green; a planted undefined citation still fails; a stale allow-list entry
  fails; the retired `relpath:line` form is rejected with a named error — all four against scratch
  roots, never the real allow-list or `label_census.tsv`. At the close the census reports
  **429 labels defined, 1575 citation sites in 128 of 471 scanned files, 152 distinct labels
  cited, 4 allow-listed, 0 unresolved, 0 stale**.
- `HeckeConeValidation` / `HeckeConeActionValidation` (WP-4) are **1.9 → 1.7 s** and
  **11.9 → 10.0 s** after the value-preserving cost reductions recorded under "Cone complex"
  below; every printed line, both collector digests and all 403 tamper item-set lines are
  byte-identical to a `9ae1d7a` binary's.

**Added in hecke-extensions slot 5** (2026-09-22, branch `hecke-extensions`, `2b1b339..d362c71`;
the close is `docs/implementation/slot5/WP-13_report.md`). **The slot made the stage's one
add-only golden emission** (WP-3: 2617 entries added, **0 changed, 0 removed**) and changed no
golden value. **Six** new registered names (94 → **100**; `fast` 39 → **40**;
`standard` 50 → **54**; `slow` 5 → **6**; `Hecke*` 49 → **55**):
- `HeckeCanonicalFieldValidation` — **`fast`**, ~0.5 s, **17 054 checks** (WP-7, E6): the
  project-canonical split field `HeckeExt/HeckeCanonicalField` ([X] §2.2 Stage 6; [E] `def:canon`,
  `cl:canon`, `alg:split`; [OD] OQ9 / OQ10 — the package planned as slot-4 WP-10, which did not
  run). The unit is **pipeline-free** (`Hecke/FpPoly`, `Hecke/HeckeSettings`, `ModCtx.h`,
  `EngineCheck.h`, nothing else) and has **no report consumer in this slot**: nothing on any
  pipeline path calls it and no record gains a key — the integration is E6's, in slot 6. It ships
  `C_{ℓ,r}` (the `CanonicalLess`-least monic irreducible of degree `r`, by enumeration in that
  order + `hecke::CertifyIrreducible`), the arithmetic of `F = F_ℓ[Y]/(C)`, univariate polynomials
  over `F` (`FqPoly` — the only new arithmetic Stage 6 needs), the root finding of `alg:split`
  step 1 with its **fixed** candidate sequence, the split form `hecke_canonical_split/v1` with a
  re-deriving nine-clause certificate, and the two settings keys `field_polynomial`
  (`least | conway`, the latter parsed and raising `hecke::NotImplementedInThisBuild`) and
  `split_field_report` (`canonical | own_field`), **appended** so the all-defaults fingerprint is
  still `0`. Two facts about the *order* are load-bearing and are what the arms pin:
  `hecke::CanonicalLess` compares the **constant** coefficient first, so the candidate odometer's
  rightmost digit turns fastest (`C_{2,3} = Y³ + Y² + 1`, not `Y³ + Y + 1`); and no `s ∈ F_ℓ` can
  ever split `π_w` (the roots are one Frobenius orbit, `x ↦ x + s` commutes with Frobenius for
  `s ∈ F_ℓ`, and both two-valued invariants the splitting polynomial uses are Frobenius-invariant),
  so the sequence starts at `Y` — a theorem, not a heuristic, and worth `ℓ` rejected candidates per
  splitting step. Seven arms, every oracle independent of the unit: (A) `C_{ℓ,r}` against
  **exhaustive trial division** (no gcd, no Frobenius) on 31 `(ℓ, r)` cells — the two
  irreducibility oracles agree on every one of the `ℓ^r` candidates, not only on the winner — with
  the Möbius count `(1/r) Σ_{d|r} μ(d) ℓ^{r/d}` and eight pinned answers; (B) the field arithmetic
  against the `FpPoly`-mod-`C` model, the ring axioms, Fermat, the Frobenius fixed field and
  `element_at` as an order-preserving bijection onto `F`; (C) `FqPoly`'s ring laws, the division
  identity re-multiplied out, gcd against its definition, `FqPowMod` against naive repeated
  multiplication; (D) root finding against an **exhaustive** root search over `F` for **every**
  monic irreducible of degree `r`, 264 of them — the conjugate set is exactly the true root set and
  `rho_canonical` its `CanonicalLess`-least element; (E) the split, its certificate, determinism of
  `to_json()`, independence of the caller's prime order, and a **nine-way tamper** in which each
  corruption fails exactly its own clause; (F) the **(2, 30)** stress case — the char-2 trace-map
  branch at the largest residue degree the repository produces (`HeckeLocalityValidation` arm 7's
  witness polynomial is a degree-30 irreducible over `F_2`): `C_{2,30} = Y³⁰ + Y²⁹ + 1`, its
  minimality shown by *exhibiting* a proper factor of every candidate below it, and two further
  degree-30 irreducibles split inside `F_2[Y]/(C_{2,30})`; (G) the two settings keys — defaults,
  registry order, canonical text, `text()` as `set()`'s inverse, the named refusals, and
  `FieldPolynomialFromSettings` raising the `not_implemented_in_this_build:`-tagged error under
  `conway`. `--bench ext` gains `canonical_field_s=` / `own_field_s=` /
  `canonical_field_ideals=` / `canonical_field_ok=` / `canonical_field_r_max=`, the measurement
  E6's performance gate is stated over — **reported, never acted on**: the gate is E6 acceptance's,
  in slot 6, and this package does not flip the default. See
  `docs/implementation/slot5/WP-7_report.md` §4 for the measured table and the finding about the
  gate's second half.

- `HeckeExtCampaignValidation()` — **`standard`**, ~2.1 s, **143 checks** (WP-2, E2 *cont.*): the
  extension record on the campaign. Seven arms: the per-cell grouping of [X] §1.5 / [XA m14] as a
  property of `plan_campaign()` alone (one record per `(n_sym, ℓ)` cell, on the cell's *first* job
  in plan order, every job of the cell carrying the family `spec.family ∪ {p}`); **`ext = false`
  byte-identity** — the frozen 21-column `summary.tsv` header, the id `n16_ell5_p2_r1` and the
  default shape signature as literals, and no `extensions` key anywhere; the attachment in both
  files (the standalone `ext/hecke_ext_ell<ℓ>_n<n>.json` with its sidecars, and those bytes
  verbatim inside the owner job's JSON) with the eight ext columns **appended**; **determinism**
  across four `jobs × threads` splits, ext record files byte-identical and `summary.tsv`
  byte-identical outside its two timing columns; the **record-level `u_ell` resume** of [X] §1.3.1
  R3.3 item 4 at `(10, 691)` — refused at `budget_mb=64` with `resumable_items = 1`, a lower budget
  refused *by name*, the resume to the shipped default byte-identical to a fresh `u_ell = auto`
  campaign's record, a resume over an included verdict a strict no-op; the R3.1 item-6 **state
  sidecar** on a forced-oversize record (found, FNV-verified, refused by name when altered or
  deleted); and the two cases a resume must not reuse (a cone asked for over a record built without
  it, and `ℓ ≥ 2^32`'s item-6(c) placeholder). **Open (slot 6):** it has no *golden* arm yet — [X]
  §5 asks it to compare campaign ext hashes against `GoldenReference.inc`, which became possible
  only with WP-3's emission. Whoever adds it must install `u_ell = off` **and**
  `good_primes = {2, 3, 5}`, because the campaign defaults to `u_ell = auto` and `S_0 ⊇ {2,3,5,7}`
  and would otherwise compare two different computations (WP-3 report §7).
- `HeckeExtDeterminismValidation()` — **`standard`**, ~10.4 s, 10 arms (WP-2, E2 *cont.*): the
  FNV-1a-64 of the **whole `hecke_ext/v2` record text** — the unsplit record and both per-sign ones
  — on `(10, 691)`, `(34, 5)` and `(24, 7)` with both WP-1 attachments on, under
  `ENGINE_THREADS ∈ {1,4,16,32} × ENGINE_BATCH ∈ {0,1}`, plus the large `(128, 5)` cell on the
  threads `{1, 16}` arms and two `device = gpu` arms where a device exists (`[SKIP]` otherwise).
  Every arm agrees with arm 0 and `failing_arms = 0`. The digest input is the record text and not a
  hand-picked invariant list, because a hand-picked list is what an order-dependence bug slips past
  ([X] §2.4 risk R10). **Its value is not reproducible bare**: the record text contains the
  `commit` key, so the digest moves on every commit — at the slot-5 close tree it is
  `0x415f73f051702a71@d362c71`. Always quote it `digest@SHA` (WP-3 finding 3; the redaction repair
  is slot 6's). **Repaired by slot-6 WP-6: the digest is now `0xfb71e225e4185be7`, bare** (see the
  slot-6 "Extended" block).
- `HeckeExtKummerValidation()` — **`slow`**, ~37.5 s, **424 checks** (WP-8, M1). [E] §8.3's Kummer
  list on `X_4`: all ten cells of [E] Claim 1.8 with `n < ell − 1` and `k ≤ 26`, at the **default**
  mathematical settings. Arm 1 checks the LIST against an oracle that is not the list — slot-4
  WP-7's `kummer_divides` / `bernoulli_mod` — and sweeps every odd prime `ell ≤ 20000` with every
  even `k ≤ 26`, finding **exactly** [E] Claim 1.8's seven pairs in that range and nothing else,
  asserted both ways. Arm 2 runs each cell through `HeckeExtDriver`: `dim X_1 = 0`,
  `dim X_4 = dim M_k + dim S_k`, the frozen model's `U_ell` admission (included at
  `ell ∈ {691, 3617, 283, 617, 131, 593, 103}`, `u_ell_over_budget` at `{43867, 2294797, 657931}`,
  with **one** `u_ell` object per cell as `hecke_ext/v2` requires), **exactly one non-split
  Eisenstein–cuspidal ideal** with `D = 3`, `f = 1`, `dim A_S = 2`, `embdim = 1`, `ν = 2`,
  Gorenstein and Loewy = socle = `(2, 1)`, every other block semisimple with `A_S = F_{ell^f}`, and
  `B' = 2` on every cell with the non-split block final **only** via `sturm(B')` ([XA B1]).
  **Registered `slow` because the ten cells cost 37.5 s at the defaults, of which `U_3617` alone is
  33.9 s.** *(The slot-5 plan's §3 WP-8 says `standard` and [X] §5 says `slow ≈ 40 s`; the
  measurement settles it for `slow` and the plan text is corrected in [X] v1.9.)*
- `HeckeExtSmallEllValidation()` — **`standard`**, ~1.4 s, **225 checks** (WP-8, M1). [E] §8.3's
  small-`ell` cases, in five arms. ASSERTED: the Dickson loci `(6,5)`, `(8,7)`, `(12,11)` — `dim X_1`
  equal to `Hecke/DicksonCount.h`'s count, the `H^0` character `χ_1(p) = p + p^n` of [C] `cl:chi`
  (`T_2 ↦ 1`, `T_3 ↦ 2`, `T_5 ↦ 0` at `(6,5)`), `dim X_4 = dim M_k + dim S_k + dim X_1`;
  `τ(5) ≡ 0 (5)` and `τ(7) ≡ 0 (7)`; `B'(60,5) = 5 = ell` with `U_5` admitted, the one case whose
  proof sweep contains `U_ell`; **the Sturm counterexamples** at `(22,5)` and `(26,7)` on the
  pipeline's own `H^1` — `dim H^1 = 5`, `dim ⟨A(T_2), A(T_3)⟩ = 2 < dim ⟨A(T_q) : q ≤ 13⟩ = 3 =
  dim M_k`, so the naive `B(k) = 3` sweep would have certified falsely; `B'(34,131) = 2`. RECORDED
  (rule A6): `(12,5)`'s `H^0` character multiset (`χ_2 ≡ χ_3` as functions mod 5, so an index label
  is not distinguishable), the `Δ` ideal's split verdict at `(34,5)` / `(58,7)`, the `T_ell` data at
  `(58,5)` / `(82,7)`. **Arm 5 is the `final = false` half of M1** — it exhibits the `false` /
  `"heuristic"` branches on the same cells under the one input that controls them.
- `HeckeExtSeparationValidation()` — **`standard`**, ~2.9 s, **92 checks** (WP-8, M1). [E] §8.2's
  two further `ell = 691` rows. `(160, 691)`: the seven blocks `2:1 1:1 2:1 2:1 4:2 6:3 10:5` the
  slot-1 probe recorded and [X] §5 says this validation "must assert", plus the separation claim
  **measured** — and **refuting [E] §8.2's closing sentence** (WP-8 finding 1). `(198, 691)`:
  `dim H^1 = 33`, blocks `2:1 3:1 4:2 4:2 20:10`, exactly one non-split block (the `3:1`, Loewy
  `(2,1)`, Gorenstein) and exactly one `20:10` block, with `691 | num(B_200/200)` recomputed from
  `bernoulli_mod`; the index-one `‖` and the uniqueness of the congruent eigenform are RECORDED,
  not asserted ([Q13]).

**Extended in hecke-extensions slot 5** (2026-09-22, branch `hecke-extensions`, base `2b1b339`).
No new registered name, and no golden value moved:
- `ConsoleScriptValidation` (WP-10, console C1b *cont.* / C5 early) is **~2.2 s, 277 checks**
  (was 259) over **20** numbered scripts: 017–020 are new artefacts with first-freeze `.expected`
  files, and **the 16 existing transcripts and `cli_frozen/` are byte-unchanged** — a
  `CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` run rewrites all 16 identically
  (`git status` clean on them afterwards). Its registration arm additionally asserts the two verbs
  C1b deferred, `bernoulli_mod` and `glover_factors`, are registered from
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp`. The four new scripts are `017_predictions.oc` (the
  two verbs: the published Bernoulli rationals as `F_ℓ` residues at three primes, [E] Claim 1.8's
  ten Kummer cells **derived** by `bernoulli_mod` rather than copied, the regularity of every
  prime `ℓ ≤ 31`, the irregular pair `(37, 32)`, the named refusal at `w = ℓ − 1`, and Glover's
  structural invariants — dimension `n + 1`, restricted weights, the central-character congruence
  `sym + 2·det ≡ n (mod ℓ − 1)`, the SL₂ multiplicities — over `n ≤ 3ℓ` at `ℓ ∈ {5, 7, 13}`),
  `018_e0_locality_grid.oc` (**E0a's verdict from the console**: six grid cells × every degree
  that carries cohomology, every block `local` and `certified` in the `linear` phase,
  `witness_poly` of the block's residue degree, the blocks partitioning `H^q`, `splits = 0` on
  every cell **and** on the three-operator refinement, each decomposition still at its golden
  `_invariants` hash — 12 certified-local blocks), `019_e1_stage1_sturm.oc` (**Stage 1's two
  decisions on the ten Kummer cells**: `u_ell_decision` 7 admitted / 3 refused with the frozen
  model's `predicted_mb`, `B'(k, ℓ) = 2` on all ten, plus [E] `cl:bprime`'s two counterexamples
  `(22, 5)` and `(26, 7)` where `{2, 3}` generates a *proper* subalgebra, with `none_at_cap` and
  the R3 `resume` reaching the same `B'`, and the `u_ell = off` branch forming no prediction), and
  `020_e2_ramanujan_10_691.oc` (**[E] `cl:ramanujan` at `(10, 691)`**: the eigenvalues
  `667, 252, 684, 531` derived from `τ(q) ≡ σ_11(q) = 1 + q^11 (mod 691)` and `1` for `U_691`,
  Jordan type `(2, 1)` and rank 1 for every `T_q − a_q` and for `U_691 − 1`, the **four** exact
  identities in `M_3(F_691)` — `3(T_3−252) = 256(T_2+24)`, `3(T_5−4830) = 174(T_2+24)`,
  `3(T_7+16744) = 137(T_2+24)`, `3(U_691−1) = −542(T_2+24)` — the one certified-local block with
  `min_poly = witness_poly²`, i.e. `A_S = F_691[ε]/ε²`, the three golden `A(T_p)^1` hashes, and
  the **basis-dependent** `A^{(1)}(U_691) = I + 221 E_31` asserted but deliberately not printed).
- `ConsoleC0Validation` (WP-10) is **613 checks** (was 612): one added arm, unchanged in kind.
- `HeckeExtRecordValidation`'s settings arm (WP-10) is unchanged at **381 checks** and still green
  after `MathSettings::canonical_text()` / `to_json()` / `text()` were unified onto one per-key
  view; the emitted text is separately proved byte-unchanged against the pre-WP-10 writers
  (7462 comparisons, `docs/implementation/slot5/WP-10_report.md` §3).
- `HeckeExtRecordValidation` is **`fast`**, ~0.1 s, **582 checks** (was 381), across WP-1, WP-11a
  and WP-12a: the extension record is `hecke_ext/v2` ([OD] slot-4 close-out 5) — the schema bump,
  the **cell-level** `u_ell` with one `resumable` (a four-ideal cell reports `resumable_items = 1`
  against v1's four, the arm that proves the repair), the per-ideal `groups` list with its
  `SameMaximalIdeal` witness, the `boundary` and `pair` complexes with `les_maps` and the two
  recorded cone flags (`phi_flat_identity` / `residual_flat_zero`, reserved in v1, **emitted** in
  v2), the per-sign (E3) objects with `iota_sign`, a `v1` reader arm asserting the two schemas are
  distinguishable by their `schema` key alone, and the real `(10, 691)` cell through
  `HeckeExtDriver` with both attachments on (`dim H^1_c = 3`, `dim H^1_! = 2`,
  `dim H^1_± = (2, 1)`, the Eisenstein line defined, cyclic on each sign and not cyclic unsplit),
  plus a from-scratch mini parser and the [X] §1.6 collector inventory. **WP-11a** inverts arm 13:
  `verify()` **code 22** now refuses a `q_max_source = "set"` on a *derived* complex
  ([C] `sec:recordschema` item 5), with a positive control on a source complex. **WP-12a** adds the
  key **`iota_exact_comparison`** ([OD] 2026-09-22 Q3), the record's half of [C] `obl:iota`(ii)'s
  rider — `ran` / `relation_rows` / `rows_with_exact` / `rows_compared`, at **record** level beside
  `iota` because one `HeckeInvolution` discharges the clause for the whole complex — every scalar
  re-derived from the production certificate, the emitted text asserted, and **code 23**
  demonstrated on five mutations against two positive controls. The shipped `(10, 691)` cell
  reports 31 relation rows, 31 exact, 31 compared.
- `HeckeConeValidation` (WP-4, WP-5) is **~1.7 s** and value-identical: `ConeCertificate` item **11**
  now evaluates the **first** `eq:conedims` identity **without consulting `H2_zero`** (OI-2,
  Option A — item code 11 kept, each identity under its own minimal guard), and since WP-5 the
  cone's `Z / B / H / P` and the certificate's C2 / C3 / C5 span inclusions run on the **tape**.
  Both packages are proved value-preserving by a whole-printed-output and collector-digest diff
  against a pre-package binary (`0x4ecd2e429ec3b49`) with the 403 tamper item-set lines identical.
  Its `CONE_LARGE` line gains `inputs_VmHWM=`, and **`HECKE_CONE_LARGE=n ./hacs
  HeckeConeValidation` is the measurement harness for [X] §6.2 E5 acceptance (d)** under the
  restated protocol: a process that builds exactly one cone and calls `verify()` once.
- `HeckeConeActionValidation` (WP-4, WP-6, WP-12a) is **~10.2 s**, **124 607 checks** (was 123 634).
  `obl:coneexact`(iii)'s `r`-half is asserted at **every** `ell` (OI-3, Option A; the `ell ∈ {2,3}`
  carve-out is dropped, and [C] v1.7.0 writes in the proof that clause (i) implies it). WP-6's
  `ρ_n` memo cuts the `n = 256` build 74.5 → 42.6 s for ~3.2 MB, entrywise identical (a warm-vs-cold
  shadow arm over 15.9 M entries, and the public one-argument overloads keep the cold path so this
  validation's own matrix-free side is unchanged). WP-12a adds `ConeActionCertificate` **item 12**,
  the record-honesty clause of [OD] 2026-09-22 Q2: the emitted `restriction_equivariance_asserted`
  must report the assertion item 8 actually performs, which since WP-4 carries no `six_invertible`
  guard, so the record now reads `true` at `ℓ ∈ {2, 3}` too (`record_r_asserted = 212/212`,
  `ell23_record_r_asserted = 74/74`); the negative control runs once per cell
  (`item12_tamper_arms = 63`) and a flipped flag fails item 12 **alone**.
- `HeckeIdentityValidation` (WP-8) is **~0.40 s** (was ~0.05 s): a third arm discharges **E1
  identity class 5**, the Dickson multiplication `L·` — the unit's own certificate on eight
  `(n, ell)` points (entries re-derived by an independent convolution, injectivity, and
  `ρ_n(A) L = det(A) L ρ_m(A)` entrywise on 24 seeded `A` including singular ones), then the
  cohomology-level `A^{(1)}_n(T_p) L_* = p L_* A^{(1)}_m(T_p)` through `IdentityCertificate`'s new
  item 5, with the untwisted identity asserted to FAIL so the exponent is pinned, the image
  asserted to be a `T_S`-submodule of `X_4`, and a tamper arm that searches all 15 single-entry
  perturbations at `(22,5)` (9 of 15 break the identity) and checks that a breaking one fails
  exactly clause 5.
- `GoldenRegressionValidation` (WP-3) now computes **16 666** objects (was 14 049) in ~5.7 s, with
  tier A **10 914** and tier B **5752** (was 9446 / 4603). Since slot-5 WP-3 the grid also carries
  the **extension-layer objects of [X] §1.6** on the ext subgrid (`n > 0` even, `5 ≤ ell < 2^32`;
  31 cells) — the `hecke_ext/v2` record (`ext_ideals`, `ext_certify`, `ext_json_canonical`,
  `ext_json_full`), the computed `sturm_bound`, and the four shipped unit collectors for E3
  (`HeckeSignSplit`), E4b (`HeckeExt/HeckeBoundary`), E5-2 (`EquivariantMappingCone`) and E5-3
  (`HeckeConeAction`), each under its own point suffix — with one tier-A `ext_excluded` on every
  other cell and on every 64-bit point. It runs under a scoped `u_ell = off` and the family
  `{T_2, T_3, T_5}`. **Two qualifications a reader of the new reference must carry.** (i) At
  `ell = 5` that family and `u_ell = off` leave `S_0 = {2, 3}`, so on `(22, 5)` and `(32, 5)`,
  where route (c) needs `B' = 5 = ell`, the sweep is `unavailable` and **four ideals are published
  `final = false`, reason `closure_unreachable`** — the first `final = false` rows the programme
  has published, a consequence of the harness's settings and not a mathematical failure. (ii)
  `final = true` in these entries **is not a proof**: `ExtDriverOptions::proof_range` defaults to
  `true` and is an unverified *caller assertion*, because identifying a Dickson-type maximal ideal
  needs E6's residue atlas, which does not exist; the records make the claim attributable, each
  carrying `"proof_range": true` beside `"proof_range_source": "dickson_count"`. The owner
  approved emitting it as-is with the qualification recorded.
- `EngineDeterminismValidation` (consequence of WP-3) is **~2.3 s**, 8 arms × **1216** records (was
  966), digest **`0xa81480950dffb0d2`** (was `0xe446b3bd2d28bd6e`). The digest moved with the
  add-only emission — three of its four golden-grid cells are in the ext subgrid — **not** with the
  engine; every record still equals the reference and every arm still agrees. *(The slot-5 plan
  §4.4 exempts WP-3 from this gate while WP-3's own acceptance (c) restates it: an internal
  contradiction, unsatisfiable by any emission touching those cells. [X] v1.9 restates the gate as
  "every arm agrees and every record equals the reference", carrying the digest as a value an
  emission may update.)*


**Added in hecke-extensions slot 6** (2026-09-22, branch `hecke-extensions`, `bd84016..` the
slot-6 close; the close is `docs/implementation/slot6/WP-14_report.md`). **The slot moved no
golden value and emitted no golden entry** (`git diff --stat bd84016 -- '*GoldenReference.inc'`
empty, tier A 10 914 / 0 and tier B 5752 / 0 under `GOLDEN_STRICT=1`; `EngineDeterminismValidation`
unchanged at `0xa81480950dffb0d2`); every new golden collector (E7's `dim_H(D_n)^q`,
`charpoly_A(D_n)(T_p)^q`, `pairing_perfect^t`, `pd_adjoint^t`, `pairing_matrix^t`) is defined and
called from its validation only, waiting for slot 7's separate add-only emission. **Six** new
registered names (100 → **106**; `fast` 40 → **43**; `standard` 54 → **55**; `slow` 6 → **8**;
`Hecke*` 55 → **60**):
- `HeckeDualityValidation` — **`standard`**, ~6 s, **13 308 checks** (WP-1, E7a; arms A10–A15 by
  WP-3, E7b). Coefficient level: `ρ_n^∨(g) = ρ_n(adj g)^T` a monoid homomorphism, the Gram matrix
  `I`, `⟨ρ_n(g) v, φ⟩ = ⟨v, ρ_n^∨(adj g) φ⟩`, `Φ_n` intertwining and an isomorphism iff `n < ℓ`;
  `H^•(D_n)` and `A(D_n)(T_p)^q`; **the intertwining arm**: `A(D_n)(T_p)^q Φ_n = Φ_n A(M_n)(T_p)^q`
  asserted **untwisted** (the `DUALITY_EXPONENT` line derives the expected exponent 0 from
  [C] `lem:symdual`) on 120 cases, the `p^{+n}` and `p^{−n}` twisted relations failing on all 20
  non-vacuous ones. WP-3's arms, on 20 cells (WP-1's ten, `(10, 691)`, the Kummer cells): the
  cone-level pairing `H^t_c(M_n) × H^{2−t}(D_n)` and the circle pairing perfect ([C] `cl:pd`(1),
  60 / 60 and 40 / 40), **the PD gate** `A_c^T G = G A(D_n)` for `p ∈ {2, 3, 5, 7}` on 160
  (operator, `t`) pairs, failing 0, the `p^n`-twisted controls 65 / 65 rejected (this is
  `obl:coneexact`(vii)'s third sentence, asserted), socle ↔ Loewy as `HeckeIdentityCertificate`
  **item 7** (19 / 19, 10 tamper rejections), the `ι`-pairing sign recorded (`−(−1)^n` on 21 / 21).
  Compares through the pairing, never through `Φ_n`.
- `HeckePresentationValidation` — **`fast`**, ~1.9 s, **995 checks** (WP-2, E2 (a), OQ11):
  `HeckeExt/HeckePresentation` on constructed algebras against their known presentations (`A^∨`
  over `F[x, y]/(x, y)²`: `t = 2`, three relations; cyclic `F[x]/(x³)`; `A ⊕ A`; `A ⊕ A/m`; the
  `f = 2` analogue, whose one relation has `F`-dimension 2; `F_{ℓ²}`), plain and conjugated over
  four primes; an eleven-way tamper arm (codes 1, 2, 4, 6, 7, 8); `(10, 691)` through the driver
  (`H^1_+` free of rank one, the unsplit `H^1_m` with `t = 2` and one minimal relation, `H^1_−`
  free) with **the record texts byte-identical with the option on and off**. The `presentation`
  settings key and its hash-invariance arm are **not** here: booked for slot 7's re-baseline.
- `HeckeAtlasSkeletonValidation` — **`fast`**, ~1.6 s, **405 checks** (WP-8, E6): the atlas at
  `ℓ ∈ {5, 7}` — `θ`-twist closure on keys and on polynomial data, `S_sep`, the store's round trip
  and byte-determinism, the write gate closed (a directory under `docs/matrix-engine/results/` is
  refused before anything is created), and the `r ≥ 2` path on constructed data (arm J).
- `HeckeAtlasValidation` — **`slow`**, ~3 s, **15 563 checks** (WP-8): `Σ(5)`, `Σ(7)`, `Σ(11)`,
  `Σ(13)` (4 / 9 / 35 / 48 systems), the Eisenstein systems and the `χ` family, `Δ mod 11` and
  `Δ mod 13` equal to `τ(q)` with `a_ℓ = τ(ℓ)`, not a lower-weight twist, the Kummer table and
  Kummer / Ribet on the atlas, Glover / Brauer for `n ≤ 3ℓ` at `ℓ ∈ {5, 7}` through
  `GloverBrauerCrossCheck` (the same oracle as `HeckePredictionsValidation` arm [H]), and the
  per-cell `canonical_field_s / total_s` column (all `r = 1` at `ℓ ≤ 13`).
- `HeckeExtEndToEndValidation` — **`slow`**, ~45 s, **5135 checks** (WP-9, E6): **identity 6**
  (`HeckeIdentityCertificate` item 6, the residue-atlas identity) on 108 cells at
  `ℓ ∈ {5, 7, 11}`, `n ≤ 200`, all passing under `cl:glover`'s standard-module convention (the
  validation prints that sentence verbatim), **the contragredient (`det^{−n}`) reading failing on
  all 63 non-vacuous cells** (named: `(22, 5)`); item 7 asserted on 8 cells; the certificate's own
  Glover recursion against `GloverFactors` on 404 cells; the `S_sep` / Stage 2(3) table (vacuous at
  `ℓ ≤ 13` on the subgrid and M1; acts on constructed one-prime `S_0'`, 38 of 150 pairs); the
  `proof_range` comparison table (4 `final` flips, one on golden cell `(24, 5)` — **recorded, never
  fed back**).
- `ConsoleSettingsValidation` — **`fast`**, **179 checks** (WP-13, console C2a; [P] v3.4 §10 C2
  (f), (g), (h)): every settable engine knob moves its getter and its default restores it, the 17
  env-only knobs refused naming their variable, `threads` / `lean` / `backend` / `locality` visible
  on `run_concurrently` task threads, a session restoring its baseline at its end; every key of
  `MathSettings::keys()` (count printed, 8, reconciled against [X] §1.5's 13 rows) round-tripping
  with its `source`; the exit-5 arm (`set field_polynomial = "conway"` then
  `canonical_field_polynomial(5, 2)` exits 5); `resume` on `Decomposition` (`budget = 8 → 64` equal
  to a fresh `budget = 64` handle modulo `budget_history`) and on `Sturm`, a lower budget and a
  changed non-budget setting refused. **Deviation**: a resume on a *complete* handle stays a typed
  refusal, because the frozen `014_expect_error.expected` pins it (an owner-gated transcript item).

**Extended in hecke-extensions slot 6** (base `bd84016`). No golden value moved:
- `HeckeConeActionValidation` — arms **A14** (WP-4, the strict-pair route: `CONE_STRICT_PAIR
  operators=212 asserted=138 recorded=74 agree=212 recorded_disagreements=0 fills_int64=4650
  fills_widened=0 checks=10201`) and **A15** (WP-5, route 3: `CONE_ROUTE3 operators=212 agree=212
  degrees=636 theta_prime_differs=212 naive_leaves_ker_r=131 checks=4339`), each with its own
  check log, so every pre-existing printed line is unchanged (`cone_output_diff.sh`). ~13 s.
- `HeckeExtCampaignValidation` — **180 checks** (was 143): arm 8 (WP-6, E2 (a)'s golden arm over
  the settings-independent `ext_ideals`, `ext_certify`, `sturm_bound` on `(10, 691)` and `(4, 13)`,
  with the harness's `u_ell = off` and `family = 2,3,5`, and the one-substring `source` difference
  of `ext_json_canonical` recorded, never asserted) and arm 9 (the ext-identity fix: the ext record
  file's `_x<16 hex>` tag; `ext = false` byte-identical).
- `HeckeExtDeterminismValidation` — `commit` redacted before hashing (WP-6): the digest is
  **`0xfb71e225e4185be7`, reproducible bare** (it was `0x415f73f051702a71@d362c71`).
- `ConsoleScriptValidation` — **281 checks** (was 277) over **21** scripts: `021_settings_resume.oc`
  is a new artefact with a first-freeze transcript; the 20 pre-existing `.expected` files and
  `cli_frozen/` are byte-unchanged.
- `HeckeIdentityValidation` / the certificate — items **6** (WP-9) and **7** (WP-3) are defined;
  the failing-code order is 1–7.
- `GoldenRegressionValidation` — unchanged: 16 666 objects, tier A 10 914 / 0, tier B 5752 / 0.
- `HeckeExtSeparationValidation` — unchanged in behaviour; its "same dimension multiset, so the
  same partition" comment is reworded by the close ([E] v1.7.1 finding M-1: the partition identity
  follows from refinement plus equal block counts).

**Added in hecke-extensions slot 7** (2026-09-23, branch `hecke-extensions`, `d7f1549..` the
slot-7 close; the close is `docs/implementation/slot7/WP-14_report.md`). **Golden moved eight
times, each a ledger event** (close report §2): stage 0, E7's add-only emission (+651, 16 666 →
**17 317**, tier A **11 472**, tier B **5845**), and the staged changed-line re-baseline of the 62
`ext_json_*` lines (stage 1 (1), items 3–7, stage 3 → `hecke_ext/v3`), whose one value change is
golden cell `(24, 5)` ideal 1 `final true → false`. `EngineDeterminismValidation` ends at
**`0xe501ca19ee7815e1`** (1279 records per arm), `HeckeExtDeterminismValidation` at
**`0x03b4f07c14555fec`** (printed `0x3b4f07c14555fec`), heavy **`0x498147a50c6c1e30`**. **Two** new
registered names (106 → **108**; `standard` 55 → **56**; `slow` 8 → **9**; `Hecke*` 60 → **61**):
- `HeckeDualityCoverageSlowValidation` — **`slow`**, ≈ 28 s (WP-1, E7 acceptance (b)): arm A16 of
  `HeckeDualityValidation` on the M1 cells `(58, 7)`, `(58, 5)`, `(82, 7)`, whose cones over `D_n`
  are too costly for the `standard` name — the `PairingCertificate`, `dim H^t_c(M_n) =
  dim H^{2−t}(D_n)`, perfectness of the cone and circle pairings, the PD gate
  `A_c^T G = G A(D_n)` for `p ∈ {2, 3, 5, 7}` with the `p^n`-twisted negative controls.
  `(160, 691)` and `(198, 691)` (129 s + 241 s, indicative) run only under
  `HECKE_DUALITY_COVERAGE_LARGE=1` (read-only; they pass: 40 gate pairs, 0 failing). Writes nothing.
- `ConsoleDeterminismValidation` — **`standard`**, **122 checks** (WP-8, console C2b; [P] §10 C2
  (a)–(e) and §11's first arm): the 22 numbered scripts under `threads = 1` and `threads = 16`,
  transcripts identical; the C1 set 001–016 under `backend = "legacy"` equal to the engine arm;
  `run_validation("GoldenRegressionValidation") == 0` from a script, the chatter captured and the
  session's `threads` / `device` lifted and restored; `run_campaign` on the `CampaignSmokeValidation`
  spec equal to the driver's `summary.tsv` outside the timing columns;
  `bench("hecke", 48, …).dims == cohomology(…).dims`; `--log` in script mode; gap G9 on 366 cells.

**Extended in hecke-extensions slot 7** (base `d7f1549`):
- `GoldenRegressionValidation` — **17 317** objects, tier A **11 472** / 0, tier B **5845** / 0
  (stage 0 added `RunE7Cell32`'s 651 entries; stages 1–3 changed the `ext_json_*` texts and item 3
  the `ext_ideals` / `ext_certify` of `(24, 5)`). ≈ 12–18 s (was 5.7 s): the E7 cells and the
  anemic pool at `ell ≤ 13`.
- `EngineDeterminismValidation` — **1279** records per arm (was 1216: +3 subgrid cells × 21 E7
  objects), digest **`0xe501ca19ee7815e1`**; ≈ 4.6 s (was 2.3 s).
- `HeckeExtDeterminismValidation` — hashes the record text with the top-level `settings` block
  reduced to its fingerprint (WP-2, owner decision 2), the same reduction as golden; digest
  **`0x03b4f07c14555fec`**, heavy `(128, 5)` **`0x498147a50c6c1e30`**.
- `HeckeDualityValidation` — arm **A16** (WP-1): `cl:pd`(1)–(2) on the 34 E2-case-list cells at
  `ell ≥ 5` that E7b's 20 did not cover (29 ext-subgrid cells + `(8, 7)`, `(12, 11)`, `(34, 5)`,
  `(26, 7)`, `(32, 131)`): 102 / 102 cone and 68 / 68 circle pairs perfect, 272 PD-gate pairs
  failing 0, 106 / 106 controls rejected. ≈ 6 → **≈ 21 s**.
- `HeckeCanonicalFieldValidation` — arm **H** (WP-4, `fa829c7` / `cab4e38`): the deterministic
  operation counter of the root finder at `r = 2..20`, `ell ∈ {5, 691, 134217757}`, the fitted
  exponent in `r` of the **fixed** route (4.89 / 4.23 / 3.87 over `r = 10..20`), and the pre-WP-4
  route kept verbatim as the byte-identity oracle for `r ≤ 10`; `CANONFIELD_OPS 691 19 … 12096005`.
  Arm **I**: `field_polynomial = conway` raises `NotImplementedInThisBuild` from the constructor,
  `--bench ext`, the certificate, the atlas and the record consumer. Adds ≈ 0.5 s to a `fast` name.
- `HeckeExtRecordValidation` — arms **17–21** (WP-3, one per stage-2 item): 17 the cell-local
  `proof_range` (tampers 25a–25h), 18 `s_sep` default vs `S_0`-only on 18 subgrid cells (26a–26e),
  19 the atlas labels against the independent full-pool `AtlasIdealCharacters` route on 7 cells
  (27a–27e), 20 the record's `split` byte-identical to an independent split, `CertifyCanonicalSplit`,
  `own_field` (28a–28d), 21 the predictions at `(10, 691)` and `(20, 131)`, `assert` (29a–29e);
  `verify()` codes 24–29; the literal schema reads `hecke_ext/v3`.
- `HeckePresentationValidation` — the key arm (k1)–(k5) (WP-2): `presentation` absent by default,
  not a hash input (`ext_ideals`, `ext_certify`, the record's `hashes` equal under `on`, (k4)), the
  fingerprint moving (k3), on-text minus the objects with the default `settings` restored equal to
  the off-text; `verify()` code 24; (k2) names item 7's record keys since R3e.
- `HeckeExtCampaignValidation` — arm 8 **asserts** `ext_json_canonical` **and** `ext_json_full`
  equal to the reference at `(10, 691)` and `(4, 13)`, and the campaign's full `settings` block
  equal to the harness's install (WP-2: E2 (a) in full); the literal schema reads `v3`.
- `HeckeExtEndToEndValidation` — **5271 checks** (was 5135; WP-3 [F]): the default run's
  cell-local `proof_range` asserted against the atlas oracle and its `final` against the re-run
  Sturm route; the `ell > 13` subgrid cells measured by re-running the driver. ≈ 45–75 s.
- `HeckeAtlasSkeletonValidation` / `HeckeAtlasValidation` — **15 607 checks** in the `slow` name
  when (K) skips, **15 963** when it runs (was 15 563; WP-5): (L) `AtlasSeparationBy` against the slot-6 pairwise loop kept verbatim, on
  every subset `S`; (M) `CollectAtlas + CloseAtlas == BuildAtlas`, a parsed store re-closing to
  itself; **(K)** the `ell = 691` store's integrity without rebuilding it (1 002 225 systems,
  `Δ = χ(0, 11)` at `n = 10` with `a_691 = 1`, `S_sep = {5, 17, 29}`) — **(K) prints `SKIP` unless
  `HECKE_ATLAS_IN=<dir>` names a directory holding the store**, which is not published (owner
  amendment to confirmation 14); (N), (N′) the per-`ρ̄` tangent pairs (`hecke_tangent_pair/v1`,
  printed only).
- `HeckeExtRamanujanValidation` — the literal schema reads `v3`; arm 3 pins `streamed()` to the
  Sturm route (the anemic-pool builds are counted in `pool_streamed()`).
- `ConsoleSettingsValidation` — `keys()` = **10** (`presentation`, `predictions`), key-order pins.
- `ConsoleScriptValidation` — over **22** scripts: `022_harness.oc` is a new artefact with a
  first-freeze transcript; the 21 pre-existing `.expected` files and `cli_frozen/` are
  byte-unchanged. **293 checks** (was 281).
- `ConsoleCliPreservationValidation` — green on the extracted `--bench` runner (WP-8; the
  `bench_identity.sh` gate: 45 cases, 0 differ against the base binary).
- `HeckeEndToEndValidation` — its last file-local `IsDicksonExceptional` wrapper retired onto the
  public `hecke::IsDicksonExceptional` (G9). No printed line moved.

**Added in hecke-extensions slot 8** (2026-09-24, branch `hecke-extensions`, `b72b839..` the
slot-8 close; the close is `docs/implementation/slot8/WP-14_report.md`, the ledger
`docs/implementation/slot8/golden_ledger.md`). **Golden moved once, by the ruled event R1**
(`53a1909`, E8 item 4a's add-only emission: +124 at seven new `E8 ring=…` points, 17 317 →
**17 441**, tier A **11 575**, tier B **5866**); **both determinism digests unchanged**
(`0xe501ca19ee7815e1` × 1279 records; `0x03b4f07c14555fec`, heavy `0x498147a50c6c1e30`). **Six**
new registered names (108 → **114**; `fast` 43 → **46**; `standard` 56 → **58**; `slow` 9 → **10**;
`Hecke*` 61 → **65**):
- `HeckeReductionValidation` — **`standard`**, **68 632 checks**, ≈ 2.4 s (E8; WP-1 registered it,
  WP-3, WP-3r and WP-4 extended it; the arm list is the header comment of
  `Hecke/HeckeReductionValidation.h` plus the TU `HeckeReductionPipelineValidation.cpp`):
  **WP-1** the composite `ModCtx` against `ModArithmetic` on fixed-seed samples, `inv` on units only,
  `valuation` / `unit_part` / `divide_exact`, `elim::howell` against `ref::howell` (unique form,
  `kernel_module` / `image_module` as modules with length bookkeeping, `solve_multi_rhs_module`
  exact), `invariant_factors` by the Smith step with M1's column `[[2], [1]]` over `Z/4` (the
  negative assertion that its Howell pivots are `(1, 1)`); **WP-3** (K) the key, fingerprint and
  grammar (`Z/<m>` reserved → `NotImplementedInThisBuild`; at WP-3 `Z` was reserved too, un-reserved at slot-24 D6 — `Z` now parses, is stored with a non-zero fingerprint, and `CoefficientRingK()` refuses it naming the site), (B) the `BlockMat` / `BlockBuilder`
  `ModCtx` overload and the §13.3 guards of `blk::rref` / `tape::rref`, (P) `ComputeSymmetricPowerMatrixRing`
  against the division-free oracle and against the field builder mod `ell`, (C) the pipeline cells
  `(10, 691)`, `(6, 5)`, `(16, 5)`, `(30, 5)`, `(60, 5)` over `Z/ell^k` (freeness of `C^q`, `d∘d = 0`,
  the certified `K`-mode, `ladic_type^q` by universal coefficients), (T) `A^{(q)}(T_p)` over the ring,
  `Θ` fused = route 2, the free-quotient `charpoly` dividing the `F_ell` one, (U) the `U64_Wide`
  cells, (X) **the refusal closure**: 36 named members (each constructor or surface outside the
  honouring set raises `NotImplementedInThisBuild` naming itself) plus 5 checks, the console `Z` arm
  at exit 5 (after `06bebdc`); **WP-3r** (M) the cyclic-summand basis rule directly
  (`H_class_coordinates = I` per cell and level, mutation-tested), the D6 value
  `(x − 2049)(x + 24)²` asserted, a composite local system under `F_ell` refused (m-6); **WP-4** the
  item-4a arms: `red_H^q` and the Bockstein as map equalities, Hecke-equivariance at `ell ≥ 5`, the
  identity `bockstein_rank^0 + higher_torsion_count == dim H^0(F_ell)`, P3's controls exact.
- `HeckeReductionCoverageSlowValidation` — **`slow`**, ≈ 4 s (≈ 29 s with
  `HECKE_REDUCTION_COVERAGE_LARGE=1`, read-only: adds `(160, 691)`, `(198, 691)`) (WP-4, E8
  acceptance (d) on the bulk): (R0)–(R4) over the E2 case list at `ell ≥ 5` where `Z/ell²` is
  admitted — the reductions and the Bockstein, the identity above, `higher_torsion_count == #{e_i ≥ 2}`
  wherever the `K`-mode certifies, the D6 refinement (1 + 2 split asserted, index 691 recorded).
- `HeckeIntegralCharpolyValidation` — **`standard`**, **322 checks**, ≈ 3 s (WP-7, line 2 M-0,
  `Integral/`): `char_Z(T_p | Λ^1)` by CRT over existing `F_ell` runs at good primes against the
  Deligne bound (carried as a bit length), residue vectors, no bignum (the O5 table frozen in
  source); `HECKE_INTEGRAL_CAMPAIGN=1` (read-only)
  adds the `n = 128` arm (`p ∈ {2, 3}`, 131 `F_ell` runs, ≈ 30 s).
- `HeckeBredonTreeValidation` — **`fast`**, ≈ 0.5 s (WP-8, line 2 V-B, `Integral/`): the shipped
  pipeline over `F_ell` at `ell ∈ {2, 3}` against the Bass–Serre tree model (`TreeRhoN`,
  `TreeModelDims`) on **82 cells** `n ≤ 40` (odd `n` included), 0 mismatches, and a frozen 16-cell
  golden oracle table ([C] `prop:bredon`(2)).
- `ConsoleErrorValidation` — **`fast`**, **107 checks**, ≈ 0.1–0.6 s (WP-10, console C4; 101 at
  WP-10, then the `coefficient_ring` arm and WP-13's `--set` pin): (R) the 16 [P] §8 rows through
  real script files on the `--script` path with `file:line:col`, (U) the exit-1 usage rows, (L) a
  lazy failure with its creation site, never retried, (P) the REPL surviving every error, (I)
  post-throw integrity (after seven induced throws the session recomputes 13 golden objects of
  `(10, 691)` and matches `golden(...)`, `device = cpu` and `gpu`), (K) `coefficient_ring` (as pinned now, slot-24 D6): `set coefficient_ring = "Z"` is legal and stored; `cohomology(...)` under `Z` is exit 5 (names `coefficient_ring=Z`, carries its statement's `file:line:col`); `Z/ell^2` at a pipeline verb exit 5; `--set coefficient_ring=Z` is exit 0 (`print(1)`) and `cohomology` after it exit 5; `--set coefficient_ring=Z/ell^1` exit 1; `--set coefficient_ring=Z/ell^2` accepted. (Until D6: `Z` on `set` exit 5, `--set …=Z` exit 1, then 5 from slot-9 WP-12.)
- `ProgramCacheReleaseValidation` — **`fast`**, **15 checks**, ≈ 0.1 s (WP-5): (A) the release
  policy and the count, (B) the recompile identity (a pipeline point with `A^{(q)}(T_2)` and a
  `uint64_t` tape program, before and after a clear), (C) two threads clearing while running (the
  `CheckThread` proof). `SKIP`s under `ENGINE_BACKEND=legacy`.

**Extended in hecke-extensions slot 8** (base `b72b839`):
- `GoldenRegressionValidation` — **17 441** objects, tier A **11 575** / 0, tier B **5866** / 0 (R1:
  `RunE8Point` at the seven `E8 ring=…` points, called from `ComputeAll()` only). ≈ 14–16 s.
- `ConsoleDeterminismValidation` — **531 checks** with a device (122 + 409), ≈ 20–30 s, **stays
  `standard`** (WP-10: C4 (a), the C1 set under `threads ∈ {1,4,16,32}` × `program_cache ∈ {on,off}`
  × `device ∈ {cpu,hybrid,gpu}`, 24 arms, one digest `0xf6ed04bbe8e6b60a`, device arms `[SKIP]`
  without a device; `CONSOLE_DETERMINISM_ARMS=threads`, read-only, restricts it to the four thread
  arms for `CheckThread`).
- `HeckeExtCampaignValidation` — **342 checks** (180 at the slot-7 close): arm 10 (WP-6) the
  parallel ext pass — serial == parallel at `ext_jobs` 1 / 2 / 4 / 16, the `u_ell = off`
  non-default arm, admission, knob invariance, the scheduler, a parallel resume; arm 11 (WP-6b) the
  device worker, records bit-identical (fewer checks without a device); arm 5 step (6) (WP-11b) a
  non-default-budget resume stamps `source = spec`, fresh and resumed records byte-identical.
- `CampaignSmokeValidation` — **1045 checks**, **0** `CheckThread` reports (11 before WP-6 made
  the engine's `g_stats` counters race-free).
- `EngineTapeConsumerValidation` — **261 checks** (WP-6b §4: the thread-local device override — a
  `Gpu` thread's programs carry GPU nodes, a `Cpu` thread's none, inherited through
  `run_concurrently()`).
- `ModContextValidation` — the composite `ModCtx` arms (WP-1); the unused `str(u128)` removed at
  the close.
- `ConsoleSettingsValidation`, `HeckeCanonicalFieldValidation`, `HeckeExtRecordValidation` —
  `keys()` = **11**, `coefficient_ring` pinned at the tail with the sample `Z/ell^2` (`HeckeReductionPipelineValidation` (K) since slot-24 D6: `Z` parses and round-trips with a non-zero fingerprint, `CoefficientRingK()` throws `NotImplementedInThisBuild` naming `coefficient_ring=Z`, and the reserved-refusal pin runs over `Z/25`, `Z/7`, …).
- `ConsoleScriptValidation` — 22 scripts, every `.expected` and `cli_frozen/` byte-unchanged;
  `ConsoleScriptEmit` re-emits them with no `git` change after `coefficient_ring`'s registration.

**Added in hecke-extensions slot 9** (2026-09-25, branch `hecke-extensions`, `ea90668..` the
slot-9 close; the close is `docs/implementation/slot9/WP-17_report.md`, the ledger
`docs/implementation/slot9/golden_ledger.md`). **Golden moved once, by the ruled event R1** (inside
the merge `762dbc3`, E8 item 4b's add-only emission: +126 — tier A 91, tier B 35 — at the seven
existing `E8 ring=…` points, 17 441 → **17 567**, tier A **11 666**, tier B **5901**); **all four
digests unchanged** (`0xe501ca19ee7815e1` × 1279 records; `0x03b4f07c14555fec`, heavy
`0x498147a50c6c1e30`; ConsoleDet `0xf6ed04bbe8e6b60a`). **Eleven** new registered names, all in the
per-package fragments `Registry/Slot9/WP<n>.cpp` (114 → **125**; `fast` 46 → **52**; `standard` 58 →
**63**; `slow` **10**, unchanged; `Hecke*` 65 → **71**); every pre-existing `--list` line
byte-identical and in order, no name re-tiered:
- `HeckeBredonTreeRingValidation` — **`standard`**, **1394 checks**, ≈ 0.3 s (WP-3, `Integral/`): E8
  at `ell ∈ {2, 3}`, `EquivariantCohomologyOnK` over `Z/ell^k` by the flat-coordinate module route
  (the Bredon object, `SmallEllPolicy::Bredon`), lengths and invariant factors against the frozen O7
  table (`integral_line_probe.py --model-R`, probe blob `f50f3cd3…`; 133 cells frozen) on 96 cells
  (`k ∈ {2, 3, 4}`, even `n ≤ 20`, odd `n ≤ 9`, the 30 `−I` / odd-`n` cells printed by name); arms
  (P) provenance, (R) `ρ_n` at 2, 3 against the division-free oracle, (A) the oracle arm, (T) the
  in-process tree model (a consistency check, shared Howell code), (K1) O7 at `k = 1` = the `F_ell`
  pipeline, (N) O7 at `ell = 5` = slot 8's module route, (G) dispatch guards.
- `EngineElimPassOptionsValidation` — **`fast`**, **18 checks**, ≈ 0.3 s (WP-6): (A) with no override
  `elim_pass_options() == consumer_pass_options() == from_env()`; (B) the new fingerprint equals the
  old formula on 512 / 512 options values that set the pair and the policy together, and a
  `policy`-only `gpu` / `hybrid` value carries bit 128; (C) under `ScopedPassOptions(batch = false)`
  12 / 12 panel programs compile with `batch = false`, RREF entrywise equal; (D) a `policy = gpu`
  override puts 12 / 12 panel programs on the device (`[SKIP]` without one).
- `EngineArenaFirstFitValidation` — **`fast`**, **17 checks**, ≈ 0.4 s (WP-7, lever L3): five
  randomized programs (20 400 temps, u32 and u64, CSE on / off, mixed shapes, chains, late reads), an
  independent re-derivation of every temp's offset and of `arena_elts`, both placement branches
  exercised (13 720 interior-gap, 6 680 appends), arena run == owned-storage run == poisoned-arena run.
- `HeckeFamilyConcurrentBuildValidation` — **`fast`**, 4 comparisons, ≈ 3.7 s (WP-7, lever L2): (A)
  two independent cells `(10, 691)` / `(12, 1009)` build `U_ell` and `T_2` on two threads released by
  one barrier, (B) two families on one shared K `(8, 691)`; every `A^{(q)}` equal to the serial build
  entrywise and each thread's `PredicateStats` deltas equal to the serial run's.
- `CampaignRingValidation` — **`standard`**, **693 checks**, ≈ 1.2 s (WP-8, C5c): (A) two ring
  campaigns (17 jobs) at the seven E8 points, every carried object equal to the golden entry and the
  object set equal to the point's 4a golden set; (T) the weight-12 free charpoly as decimal strings at
  `(10, 691)` and the `uint64_t` cell `(10, 134217757)`; (B) the O7 rows at `ell ∈ {2, 3}` with the
  three refusals, `ok_partial`; (R) `r = 2`; (S) `summary.tsv` / `index.json`; (X) the spec-validation
  refusals (`ext = true` under a ring, `ell^k ≥ 2^64`).
- `SmallEllPolicyScopeValidation` — **`fast`**, ≈ 0 s (WP-9, review m-1): a `<filesystem>` scan —
  the token `SmallEllPolicy::Bredon` only in `EquivariantCohomologyOnK.cpp`,
  `Hecke/CoefficientRing.{h,cpp}`, `*Validation.{cpp,h}` and `Registry/Slot9/WP9.cpp`; the expected
  site still exists. It caught WP-8's job loop at the merge (`158c0be`). **Since slot-14 WP-2**: its
  repository-root probe falls back to `OC_SOURCE_DIR` and a `/proc/self/exe` walk-up (the
  `ConsumerMigrationValidation` / `ContractCensusValidation` pattern), not just cwd-relative
  candidates, and its `[SKIP]` line now uses the bracketed form the kit's `EFFECTIVE`/`[SKIP]`
  convention expects — off-checkout (a cluster case dir on `/scratch`) it used to print a bare
  `SKIPPED:` line while still returning 0, so the guard silently never ran (`[C3]` finding 5).
  `MatrixRetirementValidation` gets the identical fix for the identical reason.
- `ValidationHarnessCatchValidation` — **`fast`**, new at slot-14 WP-2 (`Registry/Slot14/WP2.cpp`;
  plan item 4, the S13 WP-16 carry): drives two PRIVATE, unregistered `ValidationFn`s — one throwing
  `std::logic_error`, one throwing a non-`std::exception` type — through
  `ValidationRegistry::run_guarded_standalone()` (the same guard `run()`/`run_all()` use, factored out
  of `RunGuarded` for this purpose), captures stdout, and asserts the printed
  `[EXCEPTION] <name>: …` then `[FAIL] <name> (code 1)` lines, that a third clean function run
  afterwards still prints its own `[PASS]` (the suite really continues past an exception, never
  aborts), and that the failure tally is exactly one per thrower. No throwing name is ever added to
  the global registry. **Since S24 SHARD** it also carries the `--shard i/N` partition check
  (`ShardPartitionSelfCheck`, section "Slot 24 SHARD" below): 160 checks in all, two `SHARD_PARTITION` lines.
- `HeckeBredonU64FlatRouteValidation` — **`fast`**, ≈ 0 s (WP-9, review m-2): one honouring
  `uint64_t` Bredon cell (`ell = 2`, `n = 4`, `Z/2^33`) against the frozen O7 `(2, 4, 4)` row through
  the route's `K`-scaling law (`H^1 = [33, 2]`: the factor equal to `K` a free-rank artefact, the one
  below `K` genuine torsion).
- `IsotropyModelDeltaSquaredValidation` — **`fast`**, **20 checks**, ≈ 0 s (WP-9, review m-4):
  `coboundary(q+1)·coboundary(q) == 0` on `C_I(R)` directly, over `Z/4` and `F_5`, `n ∈ {2, 4}`.
- `HeckeIsotropyModelValidation` — **`standard`**, **1032 checks**, ≈ 2 s (WP-10, line 2 L2-1a;
  `Integral/Model/IsotropyModel`): (A) the descriptor against the shipped triangulation and relations
  (31 / 31); (B) the ranks 5/14/19 and 3/6/6 of [C] `prop:isomodel`(2), `n ≤ 40`; (C) `d² = 0`, `R_∂`
  closed and `ε` a chain map, exactly over `Z[Γ]`; (D) the model's `ρ_n`; (E) at
  `ell ∈ {5, 13, 691, 10007, 134217757}`, `n ≤ 24`, dimensions = the pipeline and `ε^*` a cochain map,
  injective, an isomorphism on `H^0`, `H^1`; (F) Appendix A of [IB] through universal coefficients at
  `ell ∈ {2, 3}`, `q ≤ 5`; (G) O2 mod 2; (H) composite `Z/4`, `Z/8`, `Z/9`, `Z/25`; (I) `R_∂` against
  `H^•(Γ_∂)`. The odd rows 9–19 are the probe's own output, labelled `[probe row]`.
- `HeckeFreeModelValidation` — **`standard`**, **803 checks**, ≈ 3–4 s (WP-11, line 2 M0, a/s,
  accepted; `Integral/Model/IntegralGroups`): `H^q(SL_2(Z); Sym^n Z²)`, `n ≤ 20`, `q ≤ 5`, **equal to
  Appendix A of [IB] exactly on all 126 cells** — ranks of `C_I` at 10007, the 2- and 3-parts from
  `σ^{≤6} C_I ⊗ Z/ℓ^K` with `K` certified per differential ([C] `prop:certifiede`, 34 refused levels
  below a certified one; the held-out level `f = K_max + 1` 42 / 42), the Dickson-prime parts from the
  shipped `K`-mode on `C_7 ⊗ Z/ℓ^K` cross-checked on `C_I`; O2, X3 (the cone of `ε^*` acyclic through
  degree 5 at the ten Dickson cells), O9 (with `tors H^6`), O8 (`C_{7,Z} = 0` beside the group object
  and the Bredon object), [X] E9's tests (1), (2), (6). **Open (review m-6, m-7)**: (T6)'s negative
  control refuses on the validation's own `ComplexKind` label, so it cannot catch a shipped-code
  regression; arm (R) re-runs `HeckeBredonTreeRingValidation` and `HeckeIntegralCharpolyValidation`
  in-process, so both run twice in `--all` and `HECKE_INTEGRAL_CAMPAIGN=1` grows this `standard` name
  by ≈ 30 s.
- `HeckeExtAlgebraInvariantsValidation` — **`standard`**, **404 checks**, ≈ 4.7–6.5 s (WP-13, C5b):
  (A) the certificate-free route (`HeckeExt/HeckeAlgebraInvariants`) against `HeckeLocalAlgebra` /
  `HeckeModuleStructure` on the 17 certified-local ideals of six cells (3 non-reduced) — basis, `rad`,
  `ν`, Hilbert, socle, Gorenstein, `nilpotent_part(t_p) == n_p`, Loewy / socle series; (B) constructed
  algebras including the Galois-conjugate trap `diag(J, J)`, `diag(J, −J)` over `F_7`; (C)
  Jordan–Chevalley and the refusals; (D) the binding-support builders at `(12, 5)` (cone action, η,
  `T_3^bd`, ι and the sign split, `L_*`, the identity certificate with all seven items).

**Extended in hecke-extensions slot 9** (base `ea90668`):
- `GoldenRegressionValidation` — **17 567** objects, tier A **11 666** / 0, tier B **5901** / 0 (R1:
  18 item-4b objects at each of the seven `E8 ring=…` points, called from `ComputeAll()` only).
- `HeckeReductionValidation` — **68 970 checks**, ≈ 3.4 s (68 632 at the slot-8 close): WP-3's arm
  (X) 36 → **66 members** (two rows flipped to honouring — `CoefficientRingContext` at `ell = 2`
  under the Bredon policy, `EquivariantCohomologyOnK` at `(10, 3)` asserting O7 — plus the
  default-policy refusals, the ten refusing accessors and `HeckeOperatorOnK` at 2 and 3,
  `HeckeReduction`'s four entry points, the console at exit 5); WP-4's **E8 item-4b arms**
  (`Hecke/HeckeReductionConeValidation.cpp`): (4b-B) the boundary, (4b-C) the cone with
  `ConeModuleCertificate` and two negative controls (a tampered item-14 witness, a wrong item-11
  length), (4b-H) the ring Hecke actions and the commutators `[A_c(T_p), A_c(T_p')] = 0`, (4b-R) the
  map equalities (`A∘red = red∘A`, the LES maps commute with `red`, β equivariance, level
  reductions, the coefficient-LES length bookkeeping), (4b-K) the class route equals the template
  route, (X4b) 21 honour / refuse closure rows — at `(10, 691)`, `(6, 5)`, `(16, 5)` (`m = 1` pinned),
  `(30, 5)` (`k = 2, 3`) and the two word-regime cells `(10, 134217757)`, `(10, 4294967291)`;
  **306 checks, ≈ 0.95 s** since WP-4t (458 / 5.7 s before: `(60, 5)` moved to the slow sibling,
  41 implied rows dropped — the `coneexact_iv_certified` and `routes_bit_identical` flag re-reads,
  the image-length vector and `l(H^1_c)` rows, boundary `lengths H^0 == H^1`); WP-8 re-spelled arm
  (X)'s two campaign rows with `ext = true`; WP-12 moved one console probe to `family(H)`.
- `HeckeReductionCoverageSlowValidation` — **`slow`**, **3731 checks**, ≈ 17–18 s (≈ 4 s at the
  slot-8 close): WP-4 added the 4b arms on the E2 case list at `ell ≥ 5`, `k = 2`, `p = 2` (50 cells
  run, 2 left out behind the existing interlock; `E8_4B_COVERAGE` 1232 checks after WP-4t's drops),
  and WP-4t the `(60, 5)` 4b cell at `k = 2, 3`, `p ∈ {2, 3}` with every arm (99 checks, ≈ 4.2 s, its own
  `E8_4B_POINT (60, 5)` line) — the only cell with `c2 = 2`, so the ring Hecke action at `n = 60` is
  now `--all-full`'s; its lengths, invariant factors and reduction bases stay gated in `--all` by
  golden R1.
- `ConsoleErrorValidation` — **218 checks**, ≈ 1.3 s (107 at the slot-8 close): WP-12 extended arm (K)
  to 204 checks (the `set`-statement position, the `--set` codes 5 / 1 / 0 — **the pin 1 → 5** — the
  (h) closure: 61 single-access scripts under `Z/ell^2` at `(10, 691)`, 25 honour / 8 exit 3 / 28
  exit 5, and 5 rows at the uncertified `(30, 5)`); WP-8c added arm **(M)**: `campaign_spec_text` /
  `campaign_spec` with a ring refusal exit 5, an ordinary spec error still exit 3.
- `ConsoleScriptValidation` — **346 checks**, ≈ 8 s: **34** numbered scripts (001–025, 040–048;
  WP-12 023–025, WP-13 040–047, WP-8c 048), each new transcript a first freeze; the 22 pre-existing
  `.expected` files and `cli_frozen/` byte-unchanged.
- `ConsoleDeterminismValidation` — **567 checks**, ≈ 29–32 s (indicative), **stays `standard`**
  (owner decision 13 ratified S8-D3 since WP-6 (e) stayed under 45 s): C4 (a) `0xf6ed04bbe8e6b60a`
  on 24 / 24 arms, unchanged; since WP-6 its `gpu` arms reach the per-panel programs (771 / 771 with
  GPU nodes) and each arm prints its non-vacuity counts; the (a) all-scripts digest moves with every
  new script and is not pinned.
- `HeckeExtDeterminismValidation` — digests unchanged; ≈ 14 s (10.8 s at the slot-8 close) because
  since WP-6 its two `gpu` arms compile into their own cache slots (607 new) and run on the device;
  stop threshold 20 s (owner decision 7).
- `EngineDeterminismValidation` — digest and 1279 records unchanged; since WP-6 the `batch = 0` arms
  compile their 546 panel programs with `batch = 0` (0 before).
- `EngineTapeConsumerValidation` — **261 checks**, unchanged.
- `PerformanceSmokeValidation` — since WP-9 the GEMM / RREF speed floors print `[SKIP floor: …]`
  under a non-`NDEBUG` build (`Debug`, `Check`, `CheckThread`); availability and checksums still
  asserted; byte-identical under `NDEBUG`.
- `HeckeIntegralCharpolyValidation` — unchanged (322 checks); `RunPipelineModEll` now refuses a
  composite ring by name (WP-9).

**Added in hecke-extensions slot 10** (2026-09-25, branch `hecke-extensions`, `2ac9ee8..222ab36`;
the close is `docs/implementation/slot10/WP-17_report.md`, the ledger
`docs/implementation/slot10/golden_ledger.md`). **Golden did not move** (a zero-golden-event slot:
17 567 entries, tier A **11 666**, tier B **5901**; `golden_landing_check.sh 2ac9ee8` →
`merges=0 orphans=0 verdict=OK`); **all four digests unchanged** (`0xe501ca19ee7815e1` × 1279
records; `0x03b4f07c14555fec`, heavy `0x498147a50c6c1e30`; ConsoleDet `0xf6ed04bbe8e6b60a`).
**Five** new registered names, all in the per-package fragments `Registry/Slot10/WP<n>.cpp`
(125 → **130**; `fast` 52 → **53**; `standard` 63 → **67**; `slow` **10**, unchanged; `Hecke*` 71 →
**75**), appended in fragment call order (WP-3, WP-8, WP-10, WP-11, WP-13 — so WP-11's name precedes
WP-13's); every pre-existing `--list` line byte-identical and in order, no name re-tiered. Check
counts from runs by name on the close's build:
- `HeckeConeCrossRouteRingValidation` — **`standard`**, **431 checks**, ≈ 3.5 s (WP-3, E8's last
  clause; m-12's asserts by WP-8: 386 + 45): `obl:coneexact`(vii) sentences 1–2 over `Z/ell^k`.
  (R) at the seven E8 points (`(10, 691)` `Z/691²` with `T_2`, `T_3`, `T_5`; `(6, 5)`, `(16, 5)`
  `Z/25`; `(30, 5)`, `(60, 5)` `Z/25` and `Z/125` with `T_2`, `T_3`) route 1 (`ModuleConeActionT`),
  route 2 (`HeckeConeStrictPairRoute`) and route 3 (`HeckeConeRelativeRoute` on the relative
  sub-complex constructor's module route; `M N = N M = I` in (c5) form) entrywise equal in degrees
  0–2, with the non-vacuity rows (`τ^s ≠ τ`, `E ≠ 0`, `Θ' ≠ Θ`, `A_c ≠ 0`, `A_c(T_2) ≠ A_c(T_3)`)
  asserted; (N) a perturbed strict table refused by its certificate (code 30), and one pushed past it
  caught by route 1's item 4; (W) at `(10, 134217757)` over `Z/ell²` route 1 runs, both cross-routes
  refuse by the named `uint32_t` regime refusal; (X) the three members honour / refuse both ways
  (at `ell = 3`, on an `F_ell` system, under a mismatched ring). Sentence 3 (the PD gate) is not
  tested over the ring — recorded unavailable.
- `EngineFingerprintDeviceBitValidation` — **`fast`**, **8 checks**, ≈ 0.3 s (WP-8, the ninth
  fingerprint bit): (A) `cpu` / `hybrid` / `gpu` fingerprints `0x6f` / `0xef` / `0x1ef` — bits
  (128, 256) = (0,0) / (1,0) / (1,1), the seven other bits unaffected; (B) one tiny tape program
  compiled under each policy lands in three distinct `ProgramCache` slots and replays its own on a
  second compile (no device needed: a GPU-assigned node falls back to the CPU).
- `HeckeStrictLiftValidation` — **`standard`**, **1824 checks**, ≈ 3.0 s (WP-10, line 2 L2-1b (1);
  `Integral/Model/StrictLift`): (A) `StrictLift::certify()` re-derived from the stored table for
  `p ∈ {2, 3, 5}`, degrees 0–6 — (T1) on the Schreier generators of `Γ″ = Γ_0(p)` (definitional on the
  free basis: it certifies the bookkeeping), (T2) chain map over `Z[Γ]`, (T3) augmentation, (S)
  `ε τ_Iso = τ^s ε` strictly (canonical `Xbulk` chains, independent of the construction's
  conversion), (B) `τ_Iso(R_∂) ⊆ R_∂` and `ε τ^∂_Iso = τ_∂ ε` against the boundary table — with the
  integer sizes printed (K1: coefficients ≤ 3, entries ≤ `p`); (B) `Θ̂_g` a cochain map on 165 cells
  over `F_2 … F_691`, `Z/4 … Z/343`, and in 64-bit over `Z/2^40`, `Z/3^30` reducing to the 32-bit one;
  (C) the strict compatibility `ε^* Θ^s_g = Θ̂_g ε^*` entrywise on **359** cells of the eight rings with
  a shipped `Θ^s_g` (`F_2, F_3, F_5, F_7`, `Z/5², Z/5³, Z/7², Z/7³`; a consistency check of the
  transport code — over `Z/ell^k` at 2, 3 it follows from (S) + (T1) + `ε`'s equivariance); (D) `Θ̂_g`
  on `H^1` equal to the shipped `A^{(1)}(T_p)` built on the **canonical** `τ` on 26 cells at
  `ell ≥ 5`; (E) O5 with `H^1` intrinsic to the model, 21 cells; (F) a negative control (one entry
  `+e_c`: `certify()` refuses at (T2), (C) catches it).
- `HeckeIntegralActionValidation` — **`standard`**, **4601 checks**, ≈ 13.5 s (WP-11, line 2 M1(a),
  a/s, accepted; `Integral/Model/IntegralHecke`): [IB] §6.2 M1(a) items 1–5 at `n ∈ {10, 12, 16}`,
  arms (3) and (5) also over every `n ≤ 20`. (P) the three `StrictLiftBundle`s are one complex; (1)
  O6 `(T_2 − 2049)(T_2 + 24)`, `3(T_3 − 252) − 256(T_2 + 24)` at 8 good primes, O5 at `n = 12, 16`,
  wrong constants refused (17 / 17); (2) the 691-congruence module of `H^1_+ ⊗ Z_691` at `n = 10` is
  `Z/691` on line 1 (E8's route) and line 2 (`Θ̂`), by two readings, through `T_2` and `T_3`, at
  `k = 2, 3` (`ι`-free); (3a) X7 = **commutativity** on `H^q`, `q ≤ 5`, pairs (2,3), (2,5), (3,5)
  (non-vacuous: 1510 cochain-level non-commuting cases; the `thm:relations` recursion is **not**
  tested — M-3); (3b) the torsion modules read as (sub) and (quot), equal to M0's groups; (3c) X6 =
  `HeckeFreeModelValidation`'s test (4) (219 non-vacuous cells, the mixed control refused in 142);
  (3d) test (5), `charpoly A^{(3)} | charpoly A^{(1)}`; (4) `Λ^1 ⊗ Z/ell^4` at 2, 3 (O5 / O6 locally;
  the local type recorded, `(16, 3)` without a `T_3` oracle); (5) X1 at `k < K`. The strict
  `ε^*`-compatibility is cited (WP-10), not re-checked.
- `HeckePeriodicityClassValidation` — **`standard`**, **2483 checks**, ≈ 2.3 s (WP-13, line 2 L2-1b
  (2); `Integral/Model/PeriodicityClass`; test (3) of `HeckeFreeModelValidation`): (A) the
  construction certificate (`e ∘ d_3 = 0`, `12e = Φ ∘ d_2`, `χ = ζ_+` on 224 finite-order elements,
  `aug E_0 = e`, `d E = E d` on 76 generators exactly over `Z[Γ]`, the Bass–Serre tree map) plus
  `IsotropyModel`'s; (F) `fill` on 60 random chains and — since WP-8's M-2 — an **oriented** disc
  (every `γ` with entries `≤ 2`, orientation propagated by BFS: 130 triangles, 148 interior edges,
  `x_max_rounds() ≥ 2` asserted, so `fill_x1`'s growth path is exercised); (O) `[e]` of order 12
  (O2); (C) `E_q^*` a cochain map; (P) `lem:bulkperiodic`(2) clause by clause on 126 ring cells
  (isomorphisms at `q = 2, 3`; at `q = 1` surjective, kernel `= ∂(N_{−I}V)` as submodules with an
  independent MV-exactness length, injective at odd `n`), lengths equal to M0's groups; (N) N1–N4
  refused (N4's vacuous check skipped since m-9).

**Extended in hecke-extensions slot 10** (base `2ac9ee8`):
- `HeckeFreeModelValidation` — **801 checks**, ≈ 1.2 s (803 at the slot-9 close; WP-8): **m-6 / m-7
  closed** — (T6)'s negative control builds the shipped 7-vertex complex and refuses because the
  object has only 3 cohomological degrees (< `q_max`), not on the caller's label; arm (R) dropped
  (`HeckeBredonTreeRingValidation` and `HeckeIntegralCharpolyValidation` are cited by their own
  `--list` lines, no longer re-run in process, so `HECKE_INTEGRAL_CAMPAIGN=1` no longer grows this
  name). **Hosting** (m-16): test (3) is `HeckePeriodicityClassValidation`, tests (4) / (5) are
  `HeckeIntegralActionValidation` arms (3c) / (3d).
- `EngineElimPassOptionsValidation` — **19 checks** (18 at the slot-9 close; WP-8): (B)'s `gpu`
  mapping now compares against the old formula `| 256`, and a `ninth_bit_ok` check pins that a
  `policy`-only `gpu` carries bit 256 and `hybrid` does not.
- `ConsoleErrorValidation` — **294 checks**, ≈ 1.5 s (218 at the slot-9 close; WP-12): new arm
  **(W)**, 24 scripts — the member-access position on a test-only raw-getter stub (exit 3 / 5 by the
  classifier, `<Type>.<member> failed`, the creation site), a positioned error keeps its position,
  `expect_error` catches the wrap, the `resume` hook's position, the positions on the shipped
  bindings, the five structural ring-handle members with values, the handle's own ring, the
  ring-mismatch rule both ways, the campaign verbs (w23, w24 the recorded non-reachability of the
  exit-5 branch; w22 an ordinary failure, exit 3); arm (K)'s rows `L.n`, `L.d_V`, `T.p`, `T.r`
  **changed 5 → 0**, `L.coefficient_ring` new. Negative control: with the two Core sites reverted
  the arm fails 21 checks.
- `ConsoleScriptValidation` — **350 checks** (346): **35** numbered scripts (001–026, 040–048; WP-12's
  `026_c5_leftovers_ring_members`, a first freeze); the 34 pre-existing `.expected` files and
  `cli_frozen/` byte-unchanged.
- `ConsoleDeterminismValidation` — **570 checks** (567; the new script): C4 (a) `0xf6ed04bbe8e6b60a`
  on 24 / 24 arms, unchanged; stays `standard`.
- `HeckeReductionValidation` — **68 970 checks**, unchanged in count; WP-3 changed three rows of arms
  (X) and (X4b) in place (the two cross-routes and the relative constructor now honour the ring at
  `ell ≥ 5`).
- `HeckeInvolutionValidation`, `HeckeIotaSignValidation` — unchanged; since WP-7 (I-1) the checks they
  gate run as host tasks in the serial order (the `IOTA_PRODUCTION … seconds=` field moves; a timing).
- `EngineDeterminismValidation`, `HeckeExtDeterminismValidation` — digests and record counts
  unchanged, across WP-6's `alignas(64)` pool layout, WP-7's levers and WP-8's ninth bit.

**Added in hecke-extensions slot 11** (2026-09-25, branch `hecke-extensions`, `a3ca7b4..9833321` + WP-17;
the close is `docs/implementation/slot11/WP-17_report.md`, the ledger
`docs/implementation/slot11/golden_ledger.md`). **Golden did not move** (a zero-golden-event slot, decision
6 (A): 17 567 entries, tier A **11 666**, tier B **5901**; `golden_landing_check.sh a3ca7b4` →
`merges=0 orphans=0 verdict=OK`); **all four digests unchanged** (`0xe501ca19ee7815e1` × 1279 records;
`0x03b4f07c14555fec`, heavy `0x498147a50c6c1e30`; ConsoleDet `0xf6ed04bbe8e6b60a`). **Eleven** new
registered names, all in the per-package fragments `Registry/Slot11/WP<n>.cpp` (130 → **141**; `fast`
53 → **55**; `standard` 67 → **74**; `slow` 10 → **12**; `Hecke*` 75 → **82**), appended in fragment call
order (WP-5, WP-6, WP-7, WP-11, WP-12, WP-18a, WP-18b, WP-18c); every pre-existing `--list` line
byte-identical and in order, no name re-tiered. Check counts from the close's `--all-full` run:
- `HeckeDicksonThetaValidation` — **`standard`**, **979 checks**, ≈ 3.7 s (WP-5, [C] `sec:dicksontheta`):
  on 108 cells (`ell ∈ {5, 7, 11, 13}`, even `n`) the six terms of `thm:thetales`, exactness at all six
  spots as subspaces (both inclusions, ranks), `H^2 = 0` on the three terms, the alternating sum; the
  closed forms `dim H^0(Q_n) = [(ell−1) | n+2]`, `rank δ = [(ell−1) | n+2] − [ell(ell−1) | n+ell+1]` and
  `thm:thetales`(4)'s; `H^0` spanned by the classes of `L^a D^b` (`prop:dicksonH0`); the fibre, projector
  and cochain-level certificate; (N1) `x^ell y · Sym^n` not well defined, (N2) a perturbed `δ` fails
  exactness (35 cells); (Hk) `HeckeOperatorOnK(QuotientL)` routes bit-identical; (X) `ell ∈ {2, 3}`
  refused by a `std::logic_error` naming `lem:h2torsion` (since slot-11 WP-17; `NotImplementedInThisBuild`
  before).
- `HeckeDicksonThetaCoverageSlowValidation` — **`slow`**, **3590 checks**, ≈ 2.5 min, 350 MB (WP-5): the
  same on 404 cells, even `n ≤ 200`.
- `HeckeDicksonThetaHeckeValidation` — **`standard`**, **5482 checks**, ≈ 9 s (WP-6): (T) the coset / τ
  tables at `n` and `n + ell + 1` identical; (F) `prop:thetatwist` on flat cochains (`n ≤ 20`, `q ≤ 2`,
  every `p` incl. `U_ell`); (E) / (U) `A_m θ = p θ A_n` for `p ∈ {2, 3, 5, 7} \ {ell}` with the untwisted
  identity asserted to fail, `π A_m = A_Q π`, `δ A_Q = p A_n δ`, `U θ = 0`, `δ A_Q(U) = 0`; (C2) `H^0` —
  `(1+p)p^a` on `L^a D^b`, `U_ell` rank `≤ 1`, square 0, zero except at `(120, 5)` (`U_5 D⁶ = −L²⁰`),
  `U = 1` at `n = 0`, `T_p = p + 1` and `U = 0` on `H^0(Q_n)`; (P3) `ker θ = im δ` the Eisenstein line;
  (B) the multiplicity inequality blockwise; (C3)–(C9) with `Σ(ell)` lookups; θ-cycles on the Δ block.
  Under **`HECKE_THETA_IMAGE_ALL=1`** (read-only) **34 337 checks**, ≈ 4.5 min, ≈ 2 GB: the census θ-image
  column over 384 cells, 1934 ideals matched one-to-one, `THETA_IMAGE` lines. Since slot-12 WP-6
  **`HECKE_THETA_IMAGE_CELLS=<file>`** (read-only, the census cell-list format) runs that arm over the listed
  cells (records from `ext_first`, then `ext_census_l7l11`); the default count does not move.
- `HeckeDicksonThetaHeckeCoverageSlowValidation` — **`slow`**, **3836 checks**, ≈ 50 s, 1.4–1.6 GB (WP-6):
  the equivariance arms on the slow grid.
- `HeckeCensusSplitValidation` — **`standard`**, **117 checks**, ≈ 9 s (WP-7, [E] `sec:census`): (A)
  `(10, 691)` `mixed`, `dim_E = 3`, `rank_r1 = 1`, `±` = `2 / 1`; (B) 11 grid cells at `ell ∈ {5, 7, 11, 13}`
  with every per-cell invariant and identity 6; (C) the `t_p` fingerprint's negative controls. Under
  **`HECKE_CENSUS_SPLIT_ALL=1`** (read-only) arm (D): all 406 census cells, 1958 `CENSUS_SPLIT` lines,
  **5643 checks**, ≈ 14 min, **≈ 9.6 GB peak**. Since slot-12 WP-6 **`HECKE_CENSUS_SPLIT_CELLS=<file>`**
  (read-only; `HeckeCensusCellList.h`'s `<n> <ell> [<u_ell_budget_mb>]`) runs arm (D) over the listed cells
  instead (census edition 2's W2 cells, `docs/implementation/slot12/WP-6_w2_cells.txt`); without it arm (D)
  is edition 1's grid exactly, and the default count (117) does not move. With both variables set the cell
  list wins (printed: `HECKE_CENSUS_SPLIT_ALL=1 ignored`); identity 6's Glover reconciliation is asserted at
  `ell ∈ {5, 7, 11, 13}` only (reported elsewhere) — slot-12 WP-11, A12.
- `HeckeStrictLiftRelationsValidation` — **`standard`**, **3619 checks**, ≈ 13–15 s (WP-11, M-3): the
  strict lifts for `diag(1, p²)`, `diag(1, p³)`, `pI` (`p ∈ {2, 3}`; `p = 5` at `ν = 2`) certified exactly
  over `Z[Γ″]` with their sizes; `Θ̂_g` a cochain map over fields, `Z/ell^k`, 64-bit `Z/ell^K`; strict
  compatibility with `BoundaryStrict` at `r = 2`; `T(p, p) = p^n`; **X7 in full**
  (`T_{p^{ν+1}} = T_p T_{p^ν} − p^{n+1} T_{p^{ν−1}}`, `ν ∈ {1, 2}`, `H^q`, `q ≤ 5`) at 2 and 3 (with
  `p = ell`) and at good primes, with the `err:e1` and `rmk:relcoeff` controls refused; the `ell ≥ 5`
  consistency with the shipped primitive `T_{p^ν}`; a negative control.
- `ModCtxMontgomeryPairValidation` — **`fast`**, **61 checks** (WP-12, F-1): (A) `mul_prepped(x,
  mul_prep(w)) == mul(x, w) == (u128)x·w % p` on 20 000 samples plus boundaries at the Montgomery and
  `U64_Wide` moduli; (B) the eight composite entry points entrywise equal with Montgomery cleared (the
  pre-package path) and to `ref::howell`; (C) u64 = u32 below `2^32`; (D) the module route at `(10, 691)`,
  `(10, 5)`, `(22, 7)` over `Z/ell^3`.
- `CoefficientRingKthRootValidation` — **`fast`**, **28 checks** (WP-12, F-2): `IsPrimeU64` against trial division and
  the A014233 pseudoprimes; `ExactKthRoot` against a verbatim copy of the slot-8 routine; the `(ell, k)`
  declaration and its refusals; the `k < 2` edge.
- `EngineU128CompositeValidation` — **`standard`**, **26 587 checks**, ≈ 1.5 s (WP-18a): (A) Montgomery-128
  arithmetic against `naive128` on 1.2·10^6 samples, `k_max` tight, the kernels across k-blocks; (E) `u128`
  = `u32` / `u64` entrywise on `HeckeReductionValidation`'s elimination generators (2652 cases); (B) beyond
  `2^64` against `ref::howell` / `ref::invariant_factors` and planted divisors; (K) the block model; (W)
  `DigitWord<W>`'s `m` table, `split` / `mac_split`, the three widths' entry points at `691^3`.
- `EngineLadicInductionValidation` — **`standard`**, **1888 checks**, ≈ 2 s (WP-18b, `engine::ladic`): the
  owner's width oracle matrix — (A) digit arithmetic; (B) `1 × 32 / 64 / 128` and **2 × 32 vs native
  `u64`** on 8 moduli × 9 families × up to 12 variants; (G) **4 × 32, 2 × 64 vs native `u128`**; (C)
  cross-width beyond `2^127` plus the base-`ell` oracle and planted exponents; (E) truncation; (D) the
  certificate `U A V = diag(ell^s) ⊕ 0`; (F) the pipeline's own `d^q` at `(10, 691)` / `Z/691^6` and
  `(30, 5)` / `Z/5^20`. `LADIC_INDUCTION_PROBE_N128=1` adds the indicative cost probe.
- `HeckeLadicCellValidation` — **`standard`**, **897 checks** (891 + 6 of arm (L), slot-27 L691), ≈ 25 s (WP-18c, `Hecke/LadicCell`): oracle (i)
  2 × 32 vs the shipped `u64` route at the 7 E8 points and the `u64` limit; (ii) M-0's charpoly at
  `(10, 691)` for `k ∈ {7, 12, 20, 40}` (beyond `2^127`) and O5 at `691^7`; (iii) UCT; (iv) whole records
  byte-identical over `w ∈ {32, 64, 128}`; (v) truncation; (vi) native `u128`; (P) the bound
  (`e_max = 1, 2, 2` at `(20, 5)`, `(30, 5)`, `(60, 5)`; forced-uncertified refusal); (P′) cross-`K` and
  cross-route `χ(T_2)`; (H) / (H′) the ordinary idempotent at `(10, 691)` and `(30, 5)`; (R) / (C) the
  per-cell rule, the grammar (`Z/ell^4096` valid, `4097` invalid), campaign jobs and spec refusals.
  **Arm (L) (slot-27 L691, 6 checks; [EX] `ex:m0`):** at `(10, 691)` over `Z/691^2` (the published job's cell, `k = 2` forced
  onto the digit pipeline, `allow_native_range`), the free eigenline of `a_E = 2049` and the free eigenplane of `a_Δ = −24` of `T_2`
  on the free `H^1` (kernels of `A − 2049`, `A + 24` by Smith elimination over `Z/691^2`, ranks 1 and 2) are `T_2`-eigenvectors and
  their three-column determinant has valuation exactly 1, i.e. they span a submodule of index exactly 691 in `H^1`. Printed line:
  `(L) (10, 691) Z/691^2: det(eigenline of 2049, eigenplane of -24) = <d> = 691 * <u> (generators up to a unit), index 691 in H^1`.
  The determinant is defined up to a unit of `Z/691^2` (generator normalisation): the value `415291 = 601·691` of [EX] is one
  normalisation (this arm's own generators print `62190 = 691·90`, a unit multiple), so the arm asserts the valuation, not the
  literal. Three teeth inside the arm: a generator moved off the eigenline, a generator scaled by 691 (index `691^2`), a repeated
  generator (determinant 0) are each refused by the same predicate. No roster, golden or digest change.

**Extended in hecke-extensions slot 11** (base `a3ca7b4`):
- `ConsoleErrorValidation` — **309 checks** (294 at the slot-10 close; WP-18c): arm (K) gains the digit
  rows (13) and the `--set` pins (2), with `H.dims` → exit 3 and `H.C(1)` → exit 3 (WP-14 pass 2 M-1).
- `HeckeReductionPipelineValidation` — count unchanged; the pinned invalid `coefficient_ring` value
  `Z/ell^64 → Z/ell^4097` (WP-18c, the grammar cap).
- `CampaignRingValidation` — gains the digit-job arm (C) (WP-18c).
- `HeckeDicksonThetaValidation`'s refusal arm (X) — the exception kind (WP-17, F-2).
- `EngineDeterminismValidation`, `HeckeExtDeterminismValidation`, `ConsoleDeterminismValidation` — digests
  and record counts unchanged across F-1, the θ line, the `u128` layer, the digit route and the census.

**Added in hecke-extensions slot 12** (2026-09-26, branch `hecke-extensions`, `9d08a30..28f73ca` + WP-9; package
reports in `docs/implementation/slot12/`; seven names, 141 → **148 = 57 `fast` / 78 `standard` / 13 `slow`**, 89
`Hecke*`; registered in `Registry/Slot12/WP{1,4,5,6,7,14}.cpp`):
- `HeckeThetaCensusRingRefusalValidation` — **`fast`**, **15 checks**, ≈ 0.4 s (WP-1, carry F-1; [E] `sec:ring`
  (b1)): five closure members of the θ / census line — `GenerateSL2ZQuotientLRelationsWithGroupData` and
  `ComputeQuotientLMatrixFM` (the two new named guards), `DicksonThetaCell`, `HeckeCensusSplit` through
  `HeckeExtDriver`'s guard, `HeckeOperatorOnK(FibreRepresentation::QuotientL)` through the contragredient guard —
  each under `coefficient_ring = Z/ell^2`: (kind) `hecke::NotImplementedInThisBuild`, (name) the refusal names the
  member, (default) the same call unchanged at `F_ell`.
- `HeckeOrdinaryPrecisionValidation` — **`standard`**, **916 checks** (829 at WP-4; WP-11 +84 odd-`n` cells,
  +3 `prepass=1` record checks), ≈ 12 s (WP-4, `Hecke/HeckeOrdinaryPart`,
  [C] v1.12.0-pre.2 `sec:hida`): (A) the torsion pre-pass on every even `n ≤ 200` at `ell ∈ {5, 7, 11, 13}`
  (400 cells; the two stopping rules agree, `λ_1` = the Dickson count, `rmk:bocksteinexp`(3)'s table) and,
  since slot-12 WP-11 (A11), every odd `n ≤ 41` there (84 cells: `λ_1 = 0`, `e_max = 0`, no torsion);
  (Hi1) pre-pass `e_max` and torsion = the certified word-size K-mode's on 20 cells; (B) `λ_e = Σ min(a_t, e)`;
  (C) `T_2`, `T_3` preserve `ker(J_n mod ell^e)` and act at `e = 1` as `prop:heckeH0`(1); (Hi2)(i)
  `(U_F')^{N_ord(h, e')}` = WP-18c's Fitting idempotent mod `ell^{e'}` at `(10, 691)`, `(30, 5)`, `(20, 5)`;
  (Hi2)(ii) `U^{N_ord(h^1, e')}` on `H_{e'}` (the shipped module route, torsion included) is the Fitting
  projection; (E) reduction `e' → e' − 1`; (F) `n = 0` and the precision use at `ell ∈ {2, 3}` refused by name;
  (G) `LadicCell`'s opt-in `precision_source = prepass` gives the default route's cell record at three cells
  beyond `2^64` (word fields and, since WP-11 (A8), the pre-pass record's own ` prepass=1` aside — a field
  `canonical_text()` appends only when set, so no default text moves); (N) negative controls (exponent terms, `T_p − 1`, `K = e'` for the free quotient, `ρ(S)` alone).
- `HeckeHidaTowerValidation` — **`standard`**, **5222 checks** (5449 at WP-5; WP-11 restated the arms, see
  `docs/implementation/slot12/WP-11_report.md`), ≈ 16 s (WP-5, `HeckeExt/HeckeHidaTower`,
  [C] v1.12.0-pre.2 `def:hidatower`, `rmk:hidacheckable` (Hi2)–(Hi6)): 165 cells — even `n ≤ 80` at
  `ell ∈ {5, 7, 11, 13}` plus `(94, 7)`, `(112, 11)`, `(114, 11)`, `(116, 11)`, `(120, 11)` — each computed once over `Z/ell^K`,
  `K = 2 + e_max` (the pre-pass), by the shipped module route (concurrently, ≤ 12 `std::thread` workers,
  results in grid order); per cell and `e' ∈ {1, 2}`: (Hi2) rank and `χ(T_2)`, `χ(T_3)` of the ordinary
  part read on `H_{e'}` (torsion included) == on the free block (WP-4's deferred last sentence) — **this
  comparison has content only at `e_max > 0`** (at `e_max = 0` the two readings are the same matrices), so
  since WP-11 (A1) it is gated on the 58 `e_max > 0` cells (31 / 15 / 7 / 5) alone; `P M` free of rank
  `ord_rank` on both readings (A4, also `ENGINE_CHECK`ed in `CharpolyOnImage`); (Hi3) the
  ordinary rank == the committed table (1 at 5, 7; 3 on `n ≡ 0 (10)` at 11 and `n ≡ 10 (12)` at 13);
  (Hi4) `χ^ord` constant mod `ell` on every `Tw_1` class and mod `ell²` on every `Tw_2` class in range
  (`ell = 5` period 20, `ell = 7` period 42, `ell = 11` `2 ↔ 112`, `4 ↔ 114`, `6 ↔ 116`, `10 ↔ 120`; **none at
  `ell = 13` in this tier** — its first `Tw_2` pair needs `n = 158`, ≈ 25 s a cell; the slow tier carries it,
  A15); (Hi5) `1 + p^{n+1}` a root mod `ell^{e'}`; at the primitive root mod `ell²` the index-arithmetic clause
  (roots of one `Tw_1` class, different `Tw_2` classes, equal mod `ell`, different mod `ell²`) is ONE check per
  `ell`, and the model check (A2): at `ord_rank = 1` each cell's computed `χ^ord(T_{p_0})` mod `ell²` misses the
  other's Eisenstein root (791 pairs; rank > 1 reported); (Det) the concurrent runner's cells == a sequential
  main-thread recomputation on four cells, every field (A7); (Hi6) `(10, 2411)` over `Z/2411^2` (`m = 1` by
  reduction): `χ(U) = (X − τ)²(X − (1 + 2411^{11}))` with the model's `τ(2411) ≡ 0`, `150·2411`,
  `h^1_ord = 1`, `χ^ord(T_p) = X − (1 + p^{11})`, `(U(1 − P))^{2K} = 0` (its free-block comparison, trivial at
  `e_max = 0`, dropped by WP-11); (N) every pair in different `Tw_1`
  classes differs mod `ell`, some pair in one `Tw_1` but different `Tw_2` classes differs mod `ell²`, a
  perturbed `τ` misses `χ(U)`. One `HIDA_TOWER` line per (cell, level) on stdout (not published).
- `HeckeHidaTowerSlowValidation` — **`slow`**, the same arms on even `n ≤ 120` at `ell ∈ {5, 7, 11}` and
  `n ≤ 200` at `ell = 13` (the period-156 tower `2..44 ↔ 158..200`), and `(10, 2411)` over `Z/2411^3`
  (`2411³ > 2^32`: the `uint64_t` module route honours it; `τ(2411) ≡ 9 539 365 011 mod 2411³` confirmed).
  **11 722 checks** since WP-11 (12 299 at WP-5); (Hi2)'s comparison gated on the 110 `e_max > 0` cells.
  Counts and time in `docs/implementation/slot12/WP-5_report.md` and `WP-11_report.md`.
- `HeckeCensusCellListValidation` — **`fast`**, **45 checks**, < 0.1 s (WP-6, `HeckeExt/HeckeCensusCellList`):
  the census cell-list parser behind `HECKE_CENSUS_SPLIT_CELLS` / `HECKE_THETA_IMAGE_CELLS` — (A)
  `CensusEdition1Grid()` is edition 1's 406 cells in order (`(198, 691)` at `budget_mb=8192`); (B) a
  well-formed list (comments, tabs, the budget field; the 112-cell W2 grid); (C) eleven refusals with their
  line numbers (field count, non-decimal, odd `n`, `ell` not a prime `≥ 5`, duplicate, overlong, empty) and
  a missing file. Pure parsing; writes nothing.
- `HeckeFormsHeckeAlgebraValidation` env hook added in slot-16 WP-3 (row text by WP-2): `HECKE_FORMS_CENSUS_U_ELL=<mb>` (read-only;
  overrides arm (T)'s per-source-set `u_ell` budget, printed as `u_ell=` on the `EFFECTIVE` line; an unknown source set is refused by line number).
  **Since the slot-16 WP-3 audit repairs**: arm (T) (and arm (I) of `HeckeBoundaryFinalityValidation`, which shares `CensusCell`) no
  longer joins by id alone — per `f = 1` row the driver's `D` must equal `module_D`, its witness_poly the census's, `U_ell` must be in the
  re-run iff in the row's record (without a record: a budgeted row needs it), and where the record is readable
  (`HECKE_FORMS_CENSUS_RECORDS=<dir[:dir…]>`, default the tree's results) its split system must equal the driver's (`join=system`);
  a mismatch is `FORMS_CENSUS_REFUSED … reason=join:<why>` and a failing check; a row without a usable record is a reported
  `FORMS_CENSUS_FALLBACK`. `EFFECTIVE … arm=T` gains `skipped=<f>1 rows> join=system:…,witness:…,fallback:…,refused:… records=<roots>`,
  and `refused=` counts the join refusals too. Malformed `HECKE_FORMS_CENSUS_CELLS` tokens and a list selecting no row fail.
  Default `HeckeFormsHeckeAlgebraValidation` unchanged (172 checks).
- `HeckeFormsHeckeAlgebraValidation` — **`standard`**, **138 checks** (129 at WP-7; WP-11 +6 residual-depth
  checks, +3 the separated `p ≤ max(k/12, 7)` check), ≈ 1.7 s (WP-7,
  `HeckeExt/HeckeFormsHeckeAlgebra`, pipeline-free except the ext-driver comparison): the forms-side
  `T_m/ℓ` of `S_k(F_ℓ)_m` from `q`-expansions (the basis `Δ^j E_6^{2(d−j)} E_{k'}` mod `ℓ`, `T_p` on
  `q`-expansions checked to the available precision, `HeckeAlgebraInvariants` for the algebra). (Q) `τ(n) mod 7`,
  `n ≤ 10`; `T_p = τ(p)` on `S_12` at `ℓ ∈ {7, 11, 13}`; `T_p` commute on `S_84`, `S_144`; (D) at `k = 36, 84,
  144`: `dim span{T_1..T_d} = d` (duality), `F_7[T_p : p ≤ k/12]` (the Sturm set) and, separately,
  `F_7[T_p : p ≤ max(k/12, 7)]` of dimension `d`, primes `≤ 31` add nothing (Sturm sufficiency); since WP-11
  (A6) every `T_p` is residual-checked on `≥ d` `q`-coefficients beyond the `d` it is read from (asserted); (R) **the slot-11 WP-20 referee datum reproduced**: `(82, 7)` ideal 4 — `T_m/7` of
  dimension 4, embdim 3, Hilbert `(1,3)`, socle 3, not Gorenstein; `(142, 7)` ideal 4 — dimension 6, Hilbert
  `(1,3,2)`, Loewy length 3, socle 3, not Gorenstein, `T_2 − 4` of Jordan type `(3,2,1)`; `(34, 7)` the agreeing
  control (`F_7[ε]/ε²` on both sides); (C) the cohomological `A` (driver primes `{2,3,5,7}`, `U_7` read as `T_7`)
  is a quotient: the joint algebra of `(T_p|V_m, t_p|E_m)` has `dim T_m/7` (4 at `(82, 7)`, 6 at `(142, 7)`),
  `A`'s Hilbert function is bounded by `T_m/7`'s, `length A = length T_m/(7, m²)` at `(142, 7)`; (N) `t_2 + 1`
  breaks the quotient, `F_7[T_2]` alone is a proper subalgebra, the system shifted at `p = 2` carries no form
  (`dim 0`, asserted as such since WP-11, A5), `T_7` beyond
  the precision throws. One `FORMS_ALGEBRA` line per compared ideal on stdout; writes nothing.
  **Slot-12 WP-12: 163 checks, ≈ 3 s** (+25): the unit gains `BuildModularSpace` (`M_k(F_ℓ)`, basis
  `f_0 … f_d`, read from `a_0 … a_d`; every `S_k` value unchanged) and three arms. (M) `M_k` substrate at
  `k = 36, 84, 144`: `dim M_k = d + 1`, `1 + p^{k−1}` an eigenvalue of every `T_p`, `p ≤ 31`, `F_7[T_p : p ≤ 31]`
  of dimension `d + 1`, `T_2|M_k` restricting to `T_2|S_k`. (T) **`HECKE_FORMS_CENSUS_ALL=1`** (read-only, not
  an emitter; `HECKE_FORMS_CENSUS_CELLS="n:ell,…"` **wins** and restricts it, printed; input
  `HECKE_FORMS_CENSUS_TSV`, default the tracked edition 1): every non-reduced census row — one driver run per
  cell (`ext_u691` rows at `u_ell = budget_mb=8192`), the forms side on `S_k` **and** `M_k` localised at `A`'s
  full system (`U_ℓ` = `T_ℓ` included) over `F_ℓ[T_p : p ≤ 31]` (+ `T_ℓ` at `ℓ > 31`), Sturm generation checked
  per cell; census agreement (length, embdim, Hilbert) **gated**, the quotient / equality verdicts reported;
  one `FORMS_CENSUS` TSV line per row (655 rows over the staged edition 2: ≈ 12 min in 6 shards). (F) the
  **boundary finality certificate** of `docs/implementation/slot12/WP-12_finality_proposal.md` on the
  heuristic `ℓ = 5` ideals — by default `(26, 5)`, `(30, 5)`; **`HECKE_FORMS_FINALITY_ALL=1`** (read-only) all
  184 census rows (86 cells, ≈ 5 min, 1073 checks; `HECKE_FORMS_FINALITY_ELLS=7,11,13` widens it, gated at
  `ℓ = 5` only): per ideal `r^q` injective on the block, the boundary law `t_q = t_{q'}` for `q ≡ q' mod ℓ`
  (gated on every injective block), `t_q ∈ A_S` for one prime per class of `(Z/ℓ)^×` plus `U_ℓ` (the
  certificate; gated at `ℓ = 5`), one `FORMS_FINALITY` line each; negative control: the cuspidal `Δ` block of
  `(10, 13)` (`r^1 = 0`) breaks the law (`t_3 = 5 ≠ t_29 = 1`). Writes nothing. **Since slot-14 WP-2**: arm (F)
  prints `[SKIP] (F): the TSV holds no heuristic rows` and does not fail when `HECKE_FORMS_CENSUS_TSV` names a
  TSV with zero `sturm_heuristic` rows (edition 2, since S12-FIN made every heuristic row `final = true`) —
  previously `Check(!cells.empty(), …)` failed there (`[C4]` headline 5, the cluster's `forms_census_all` case);
  it still fails when heuristic rows exist elsewhere in the TSV but none matched the requested cells. Every arm
  also prints one `EFFECTIVE HeckeFormsHeckeAlgebraValidation arm=<T|F> cells=<k>` line when it runs.
  **Slot-12 WP-14:** default counts unchanged (163); arm (T)'s loop body is factored out as `CensusCell` and
  now also **gates** the Eichler–Shimura identity `dim V = dim T(S_k)_m + dim T(M_k)_m` on every `H1` row it
  runs (one `FORMS_ES` line each; WP-13 F9) — env-only, so the default run does not move.
  **Since slot-15 WP-20** (163 → **172 checks**, ≈ 3 s): F9 gated in its **torsion-corrected** form `D = dim T(S_k)_m + dim T(M_k)_m + h`
  (`h` = `DicksonH0Lambda`, [C] `prop:heckeH0` closed form; `h = 0` is F9 proper; `FORMS_ES` carries `h=`, `F9_CORRECTED` when
  `h > 0`, reached synthetically only), `M_gen` a `Check`, `M_k` faithfulness per block (arm (M) +6 cells `(24,5) (30,7) (34,7) (40,11)
  (24,13) (52,13)`), the census columns `saturated` / `mult_one` appended to `FORMS_CENSUS` (WP-20 report).
- `HeckeBoundaryFinalityValidation` — **`standard`**, **13 332 checks, ≈ 9.4 s** (**13 442 since the slot-16 WP-3 audit repairs**: arm (I)
  joins its five edition-1 rows to their tracked records by eigen-system, `FORMS_CENSUS_JOIN_SUMMARY arm=I rows=5 join=system:5,…`, one
  gate) (**13 441 since slot-15 WP-20**, ≈ 16 s on a shared
  box: arm (I) shares `CensusCell`, so the corrected F9 and `F9_H0` (`DicksonH0Lambda = D` on every `H^0` row; test cell `(120, 5)`
  ideal 0, `D = h = 2`) run here too; slot-12 WP-14; registered in
  `Registry/Slot12/WP14.cpp`, body in `HeckeExt/HeckeFormsHeckeAlgebraValidation.cpp` beside the helpers it
  reuses): the coverage the WP-13 referee asked of the boundary finality proposal (`WP-12_finality_proposal.md`
  v2). (L) **Lemma B′ on the boundary operators themselves** (F3): for `ℓ ∈ {5, 7, 11, 13}`, even `n ≤ 40 / 40 /
  34 / 30` (72 cells), the pool primes `q ≤ 31`, `q ≠ ℓ`, plus the least prime of every class of `(Z/ℓ)^×` the pool
  misses, the shipped `A^∂(T_p)` (`HeckeBoundaryOperator::compute()`) on `H^0(C_∂)` and `H^1(C_∂)` — 1628
  operators: diagonalisable over `F_ℓ`; equal to the transport of the Lemma B′(0) / (1) fibre formula
  (`ρ(diag(1,p̄)) + p̄ρ(diag(p̄,1))` resp. `p̄ρ(diag(1,p̄)) + ρ(diag(p̄,1))`, descending to classes); `A^∂(T_p) =
  A^∂(T_p')` for `p ≡ p' (mod ℓ)` (648 pairs); pairwise commuting (8574 pairs); eigenvalue multiset
  `{χ_b(p)}_{b ≤ ⌊n/ℓ⌋}` **gated on `H^0`** ([C] `prop:bdrychar`(1)) and **recorded on `H^1`** ([C] `cl:chi`(2),
  a conjecture: 814 / 814 agree). (I) the Eichler–Shimura identity (F9) gated on the non-reduced edition-1 rows
  of `(10, 691)`, `(34, 7)`, `(38, 13)`, `(40, 7)`. (X) the `mixed` negative control `(34, 7)` ideal 2 (F12 (c)):
  `0 < rank r^1 = 2 < D = 4`, not certified (the boundary law fails there although every class representative
  lies in `A_S`). (H) **`HECKE_BOUNDARY_FINALITY_ALL=1`** (read-only, not an emitter; input
  `HECKE_FORMS_CENSUS_TSV`, default the tracked edition 1): every `sturm_heuristic` census row at `ℓ ∈ {5, 7, 11,
  13}` through arm (F)'s finality instance, the certificate **gated at every `ℓ`**, one `FORMS_FINALITY` line per
  row and a `BOUNDARY_FINALITY_SUMMARY` line — on the staged edition 2: **376 / 376 certified** (`184 / 150 / 37 / 5` at `5 / 7 / 11 / 13`, all injective, law held on all, every `q ≤ 31` in `A_S`; no other non-final row), 15 213 checks, 0 failing, 999 s (`docs/implementation/slot12/WP-14_finality_all.txt`). Writes nothing.
  **Slot-12 S12-FIN (the certificates landed, `hecke_ext/v4`):** now **13 395 checks, ≈ 15 s** (in `--all`; 19.8 s
  under load). Wherever it gates per ideal ((X), (H) and the new (R)) it also runs the **production driver** on the
  cell and compares the **emitted** `certificate_routes.d0` / `.d1`, `certificate`, `final` and `boundary_reps` with
  its own independent computation (a `FIN_ROUTE` line per row): on `H0` rows an independent Proposition D over the
  whole pool, on `H1` rows the validation's certificate. (X) runs that driver with routes (b) / (c) off, so (d1)
  runs on the mixed block and must say `not_injective` with `final = false`. **(R)** (default): every heuristic
  edition-1 row of `(26, 5)`, `(126, 5)` (one `X_1` (d0), two `X_4`), `(50, 7)`, `(122, 11)` (representatives 37, 43
  streamed) — 6 / 6 agree, all `final = true` (1 `dickson`, 5 `boundary`; `FIN_ROUTES_SUMMARY`) — plus `verify()`'s
  clauses 30 / 31 and the certificate object's code 4 on tampered copies of the `(126, 5)` record; since the
  FIN audit (G1) also (d1)'s stream cap: all 400 census-range cells within it, `(2|10, 691)` and `(2|18, 10007)`
  over it, a synthetic `(10, 691)` block → `not_run:budget` with no representative computed (`FIN_STREAM_CAP` line).
  `HeckeExtRecordValidation` arm 3 gained the `is_final` branch-ordering cases of a passed (d0) / (d1) (G3). Under (H) a
  `FIN_ROUTES_ALL` line counts driver agreements over all rows (`docs/implementation/slot12/FIN_report.md` §3).

**Extended in hecke-extensions slot 12**:
- `ConsoleErrorValidation` — **347 checks** (309 at the slot-11 close), still **`fast`**, ≈ 1.6 s (WP-8, console
  phase θ, [P] v3.9.2): new arm **(T)** — the θ rows of [P] §8 through ten script files and one REPL run:
  `dickson_les` / `theta` under `Z/ell^2` exit 5, a ring `Cohomology` handle in either argument of `theta` exit 5,
  mismatched `n` (naming `n`, `n_up`, `ell`) and mismatched `ell` type errors exit 3, `ell < 5` exit 3 naming
  `lem:h2torsion` for both verbs (lazily for `DicksonLES`, with its creation site), the creation-time snapshot rule,
  odd `n` not refused, a failed `DicksonLES` rethrown on every access and never retried.
- `ConsoleScriptValidation` — **354 checks** (350): **36** numbered scripts; `027_dickson_theta.oc` (WP-8) is a
  first freeze — the Dickson LES at `(30, 5)` and `(16, 7)` (exact at six spots, `ker θ^1 = im δ`, alternating sum
  0), `theta`'s `induced[0]`, `induced[1]` and ranks == the `DicksonLES` handle's (the LES route; since WP-11,
  A13, replacing a `theta == L_map` comparison of one function with itself — the `.oc` changed, its transcript
  did not), `θ^1 · ker θ^1 = 0`, `twist_check == 0`, `u_ell_zero`, the det twist at `p = 2` by hand; the 35
  pre-existing `.expected` files and `cli_frozen/` byte-unchanged.
- `ConsoleDeterminismValidation` — **573 checks** (570; the (a) threads arm runs 36 scripts), C4 (a) digest
  `0xf6ed04bbe8e6b60a` unchanged (16 C1 scripts).

**Extended by slot-12 WP-17** (post-close, owner-approved 2026-09-26; [P] v3.9.3, Q9 decided (a) — the console
serves the wide band `2^32 ≤ ell^k < 2^64` through the native `uint64_t` pipeline, as the campaign does):
- `ConsoleErrorValidation` — **539 checks** (347), still **`fast`**, ≈ 2.4 s: new arm **(Q9)** — (1) the routing at
  the four band edges on both primes (`5^13 | 5^14`, `5^27 | 5^28`, `691^3 | 691^4`, `691^6 | 691^7`:
  `bind::IsWideCell`, `H.lengths` served at every edge, `H.precision` exit 5 below `2^64` and exit 0 on the digit
  side) and an `A^(1)(T_2)` entry `6103515601 > 2^32` at `Z/5^14`; (2) **value identity with the campaign job loop**
  on seven band cells — `(10, 5)` at `Z/5^{14,20,27}`, `(10, 691)` at `Z/691^{4,6}`, `(10, 19)` at `Z/19^15 > 2^63`
  (entries as decimal Strings), `(30, 5)` at `Z/5^14` with `U_5`: the console runs the campaign (`run_campaign`),
  then the verbs, and the 13 hashed objects of the `hecke_ring_report/v1` record (lengths, invariant factors,
  `red_H^q` for `q ≤ 2`, `r_K(d^0)`, `r_K(d^1)`, the Bockstein pair) and the free charpoly (precision and every
  coefficient) are equal (91 / 91 objects); (3) the member closure of a wide handle at `Z/691^4` (48 rows: 24
  honour, 7 exit 3 — the six field members and `resume` —, 17 exit 5).
- `ConsoleScriptValidation` — **358 checks** (354): **37** numbered scripts; `028_wide_band.oc` is a first freeze —
  `(10, 691)` over `Z/691^3` (the `uint32_t` route) and `Z/691^4` (the `uint64_t` route): lengths `k · 3`,
  `H^1 = (Z/691^4)^3`, the charpoly over `Z/691^4` reduces mod `691^3` to the one over `Z/691^3` and equals
  `(X + 24)^2 (X − 2049)`, `A^(1)(T_2)` carries `−24` and `2049`; the 36 pre-existing `.expected` files and
  `cli_frozen/` byte-unchanged.
- `ConsoleDeterminismValidation` — **576 checks** (573; the (a) threads arm runs 37 scripts), C4 (a) digest
  `0xf6ed04bbe8e6b60a` unchanged.

**Added in hecke-extensions slot 3** (2026-09-17, branch `hecke-extensions`, `20c8530..d65e96f`;
the close is `docs/implementation/slot3/WP-11_report.md`). **The slot changed no golden value and
emitted no golden entry** (`GoldenReference.inc` and `tau_table_p2.txt` byte-identical to
`b391a3a`, digest `0xe446b3bd2d28bd6e` on all 8 arms); every new golden collector (cone
dimensions, `A_c` invariants, `h_flat`, table hashes) is defined and called from its validation
only. Nine new registered names (80 → **89**; `Hecke*` 39 → **45**; `slow` 4 → **5**), one line
each (tier, package, what it gates):
- `HeckeUEllReachValidation` — **`standard`**, ~11 s, 6160 checks (WP-1, E1b-0): the `U_ell` reach
  repair — `alg:tau` step 1 through `escalate_on_overflow`, the forced-wide arm bit-identical to
  the `int64` tier wherever that completes (τ scalars and `A^{(q)}(U_ell)`), the forced-narrow
  negative control (under `ForceNarrow` `ell = 5003` still throws the named `HeckeOverflow`; `Auto`
  escalates 284 times and certifies), a 4000-transform `QuadPointW`-vs-`QuadPoint` sweep (473 past
  `int64`), coset tables self-checked at `N = 3617` and `N = 5041`, 0 escalations on the
  sub-threshold cells, and the `u_ell` propagation onto `run_concurrently()` tasks.
- `HeckeUEllReachSlow` — **`slow`**, ~2 min, 32 checks (WP-1): the forced-wide arm at `ell = 3617`,
  the certified τ at `ell = 5003` / `10007`, `U_5003` at `n = 2` end to end, the `ell = 43867` coset
  tables, and the new limit — `ell = 43867` escalates and is then refused by `certify()` clause (e)
  (code 51), with `4·23170² ≤ 2³¹−1 < 4·23171²` pinned. **Since slot-24 ELL-W** arms (9)/(10) follow the lever
  `HECKE_TAU_WIDE`: by default `ell = 43867` and `ell = 23173` certify in the **wide tier** (`wide_tier()`, B = 4N²) and `23167` stays narrow;
  under `HECKE_TAU_WIDE=0` both are refused with code 51 exactly as before (the rollback arm). Prints the `EFFECTIVE HeckeTauWide` line.
- `HeckeUEllBudgetValidation` — **`fast`**, 575 checks (WP-1): the frozen RSS model
  `u_ell_rss/v2-2026-09-17` (its constants, its residual band asserted both ways, monotonicity),
  `UEllDecision(16, 43867, 2048) = {included = false, u_ell_over_budget, 8254.76 MB}` pinned, the
  admission table and the ten Kummer verdicts, `off` short-circuiting without a prediction, the
  `u_ell` key (defaults, parsing, round trip, registry order, fingerprint `0` at the default).
- `HeckeExtSturmSweepValidation` — **`standard`**, ~2.4 s, 274 checks (WP-2, E1b): generation
  certificate (c) on real blocks (`HeckeExt/HeckeSturmSweep`) — at `(10, 691)` `A_S = F_691[ε]/ε²`,
  (a) fails, (b) `excluded_by_socle_bound` with the naive `dim C = 5`, (c) `sturm(B' = 2)`,
  `generators_certified = [2]`, `final = true`; the `B(k)` counterexamples `(n, ell) = (22, 5)`,
  `(26, 7)` rejected by `{2, 3}` and accepted by `B'`; both `sturm_unavailable` modes on a forced
  `cap = 3` at `(22, 5)` with the R3 resume arms; Stage 1's `S_0` with the `u_ell` admission (a
  refused `U_7` under `u_ell = off`); `not_applicable` at `n = 0`; a fifteen-way tamper; the ext
  layer's wall at `n = 256` recorded (20.1 % of the `{2, 3, 5}` pipeline).
- `HeckeConeValidation` — **`standard`**, ~1.9 s, 5350 checks on 74 cells (WP-5, E5-2): the
  equivariant cone `EquivariantMappingCone` on `Hecke/SL2ZBoundaryPair` — an own dense
  `eq:conediff` == the stored `D_c`, `D² = 0`, an own zig-zag connecting map == `r^q` ==
  `HeckeBoundary::r(q)`, exactness at every spot by own ranks (592/592) with `im π^1 = ker r^1`
  explicitly, `H^0_c = 0` at every `ell` and `n`, `eq:conedims`, **`dim H^1_c = 3` at `(10, 691)`**
  and `1 + 2 dim S_{n+2}` with `H^2_c = 0` at the ten Kummer cells, the per-complex degree fields
  (a `set` `q_max` on the finite model rejected), the truncated branch of `obl:coneexact`(iv) on a
  declared truncation, a three-way tamper, the golden collectors' digest across
  `ENGINE_THREADS = 1 / 16` children and `ENGINE_BACKEND=legacy`.
- `HeckeConeActionValidation` — **`standard`**, ~11.9 s, 123 634 checks on 63 cells / 212
  operators (WP-6, E5-3): the cone Hecke action `Hecke/HeckeConeAction` — `h := η̃` by coset
  transport (two bracketings bit-identical, an own transport), `Φ_g`, the `lem:conesign` residual
  zero **on the stored `C^q_eq` basis** (the flat identity recorded: 29 of 424 degrees),
  `A_c^{(q)}` by `alg:assembly`, `apply_Phi == Φ_flat[:,b] == apply_Phi_direct` on every basis
  vector, `ConeActionCertificate` (`obl:eta`(v),(vi) + `obl:coneexact`(i)–(iii); `r^q A = A_∂ r^q`
  on 424/424, recorded at `ell ∈ {2, 3}`) and `ConeRelationsCertificate` (`obl:coneexact`(vi) on
  335/335 with the **full** `T_{p²}`), **`obl:coneexact`(viii)(a)** on the four `EtaVertexPolicy` ×
  `TauBoundaryVertexPolicy` arms (`A_c^{(q)}` bit-identical, both table hashes asserted to move)
  and **(viii)(b)** — `h' = h + ξ` failing exactly `obl:eta`(v) and moving `A_c^{(1)}` at
  `(10, 691)`.
- `ConsoleScriptValidation` — **`fast`**, ~0.5 s, 174 checks (WP-7, console C1a): the C1a binding
  surface on its own registry, the five smoke scripts of `Console/scripts/` in process with every
  pin `hash(x) == golden(point, object).hash` through `GoldenLookup` at fingerprint `0` (`golden`
  refused at a non-zero fingerprint, rule R19), the exit-code table 0–5 (5 =
  `hecke::NotImplementedInThisBuild`, via a test-only verb), `state` / `resume` / `save_state`,
  the narrowed "no decomposition transcript before C1b" guard, `check_console_includes.sh`.
- `ConsoleCliPreservationValidation` — **`fast`**, ~1.5 s, 41 checks (39 before S24 CL-7) (WP-7): the frozen CLI forms
  (`--help`, `--bench --help`, `--bench micro --help`, `--campaign --help`, a `--campaign --dry-run`,
  one validation name) byte-compared against stdout frozen before the console branch (`Console/scripts/cli_frozen/`),
  `--list` compared **modulo appended names**, then `-c`, `--script f.oc n=10 ell=691`, stdin,
  `--console --help`, `--set`, a parse error that runs nothing, an unknown name still exit 1.
  Since S24 CL-7 (owner ruling 4) also the no-argument form: the `--help` text, byte-identical, with exit 1;
  `help.stdout` itself was re-frozen there (the no-argument line, plus `--help`, `--atlas`, the console forms, `--serve`).
  Since S24 CL-L1, in an `ENGINE_SHADOW_LEGACY` build only, the live stdout loses the shadow's own
  `[TIMING] A_Cq kernel q=` / `[TIMING] A_Zq kernel q=` lines (printed by the legacy cohomology arm the shadow runs) before
  the byte comparison; the check count is unchanged, and OFF / ON builds compare the raw stdout as before.
  **Spawns child copies of the binary — never run it while relinking.**
- `ContractCensusValidation` — **`fast`**, ~0.2 s (WP-10): `label_census.sh` — every
  `[C, <label>]` / `\HA{<label>}` citation in the tree resolves to a `\label` of
  `gl2_contract.tex`; at the close 429 labels, 1408 sites in 121 of 430 files, 4 allow-listed,
  **0 unresolved**; regenerates `docs/latex/label_census.tsv` on every run.

And, extended rather than added: `HeckeLocalityValidation` (WP-3) is now **~8.1 s, 1500 checks**
with **arm 7, strict locality mode** — the `(2, 30)` covering example built from a certified
degree-30 irreducible (budget `local = false` / bound 30, strict `local = true` / `f = 30` /
`phase_reached = residue_search`, 0.10 s), the Berlekamp split path, grid identity under
`locality = strict` (`LOCALITY_GRID_STRICT … nonlinear_phase=0 hashes=944 failing=0`),
interruption + `resume_locality()`, the fingerprint, the lexicographic fallback, a five-way tamper
on `certify()` codes 20 / 23 / 25 / 26 / 30, a concurrent budget-vs-strict arm.

**Added in hecke-extensions slot 2** (2026-09-16, branch `hecke-extensions`, `ac84baf..45f7c4e`;
the close is `docs/implementation/slot2/WP-13_report.md`). **The slot made the stage's one golden
re-baseline** (WP-2, phase E0b: `hecke_report/v2` — exactly the 384 predicted `report_canonical^q`
/ `report_full^q` lines, 0 elsewhere, 0 splits, `golden_explain.py --allow-keys e0b.keys` exit 0,
digest `0x2fa804dae5e9d98d → 0xe446b3bd2d28bd6e`; note
`docs/matrix-engine/rebaseline-2026-09-16-hecke-report-v2.md`; `tau_table_p2.txt` byte-identical)
and **no other package changed a golden value**. What else landed, one line each:
- **`Hecke/HeckeSettings`** (WP-1) — the *mathematical settings* layer, `MathSettings`: the first
  registered key is **`locality`** (`budget=<N>`, default 64; `strict` parses and validates but
  throws the named `hecke::NotImplementedInThisBuild` until slot 3's WP-6 — never silently
  degraded; *implemented in slot 3, WP-3*); `thread_local` scoped overrides propagate onto `run_concurrently()` tasks; the
  FNV-1a-64 fingerprint of the non-default entries is `0` at the defaults.
- **The locality certificate inside `compute()`'s refinement loop** (WP-1, E0b): a candidate with
  two irreducible factors **splits** the block, an exhausted budget emits `local = false` with a
  resumable `LocalityState` (R3 instance 2), `k = 1` is local for free — value-preserving on the
  whole golden grid (`loop_disagreements = 0`).
- **`hecke_report/v2`** (WP-2): the per-block keys `local` / `witness_poly` / `coefficient_field`
  (`P` keyed by prime), `level_c.locality`, and the four **per-complex** fields `q_max` /
  `truncated` / `q_max_source` / `degrees`, derived from `HeckeReportInput::num_degrees`, which
  the writer now **requires**; `resumable` is not emitted; `docs/matrix-engine/results/` is stale
  by schema (banner written), republished by E6.
- **`HeckeExt/HeckeLocalAlgebra`** + **`HeckeExt/HeckeGenerationCertificates`** (WP-4 / WP-5,
  phase E1a): the local algebra `A_S`, generation certificates (a) and (b), the socle bound, the
  resumable `CommutantState` (R3 instance 3). The whole layer is **`namespace hecke_ext`** since
  WP-5 (`HeckeIdentityCertificate` moved from `heckeext`; the name is in no emitted text).
- **`HeckeExt/HeckeBoundary`** + **`Hecke/HeckeBoundaryDiagnostics`** (WP-7, phase E4b): `H^1_! =
  ker r^1` with its Hecke action, the joint `1 + p^{n+1}` eigenspace, Harder's criterion, the
  split, and the two recorded diagnostics `cochain_commutes` / `eta_zero`.
- **`Hecke/HeckePairHomotopy`** + **`Hecke/HeckeIntegerSolve`** (WP-8, phase E5-1): the certified
  pair homotopy `η` over `Z`, `obl:eta`(i)–(iv); the integer solver moved **verbatim** out of
  `HeckeTauTable.cpp` so the `η` fills use the one solver (golden and `tau_table_p2.txt`
  unchanged).
- **Documents** (as of the slot-2 close; the slot-3 close moved them to [C] v1.5.2, [E] v1.4.2,
  [P] v3.1, [X] v1.7, and the slot-4 close to **[C] v1.6.2, [E] v1.5.1, [P] v3.2, [X] v1.8**): [C] v1.4.0 (WP-9, the nine deferred boundary-chapter points) → v1.4.1 (WP-10,
  referee) → **v1.4.2** (WP-13, status only); [E] v1.4.0 (WP-11); [P] v3 (WP-12); [X] v1.6
  (WP-13).
- **Not done in slot 2**: WP-3 (E1b-0, the `U_ell` exact-integer reach repair and the RSS re-fit)
  **did not run** — `docs/KNOWN_ISSUES.md` §3 stays OPEN, booked for slot 3 at the head of Lane
  B1; WP-6 (strict locality mode), WP-14 (console C1a) and WP-15 (`label_census.sh`) are slot 3's.

The three new validations (all **`standard`**, in `--all`; 77 → 80 registered, `slow` tier still
four; `Hecke*` count 36 → 39):
- `HeckeExtAlgebraValidation` — **`standard`**, 0.10 s (WP-4 + WP-5): the local algebra `A_S` of a
  certified-local block, its invariants and generation certificates (a) **and** (b) — the socle
  bound, the structured commutant and its resumable `CommutantState` — on constructed monomial
  algebras over `ell ∈ {5, 13, 691, 134217757}`.
- `HeckeBoundaryParabolicValidation` — **`standard`**, ~4.7 s (WP-7 / E4b): `H^1_! = ker r^1` as a
  `T_p`-stable Hecke submodule with its action, the joint `1 + p^{n+1}` eigenspace, Harder's
  criterion on the ten Kummer cells of [E] Claim 1.8 (all `consistent`), the Harder split, and
  the two recorded diagnostics `cochain_commutes` / `eta_zero` (both false on all 315 pairs).
- `HeckePairHomotopyValidation` — **`standard`**, ~0.3 s (WP-8 / E5-1): the certified pair homotopy
  `η` of [C] `sec:cone` over `Z` — `∂η + η∂ = j τ_∂ − τ j` against the shipped `τ` and `τ_∂`,
  `obl:eta`(i)–(iv) re-derived independently on 152 tables, tamper rejection, `eta_zero` agreeing
  with WP-7's walk (false everywhere), and `lem:etaunique` exhibited on two vertex-chain policies.

Added in hecke-extensions slot 2 (WP-4 / WP-5 — phase E1a, the extension layer's Stage-3 and
Stage-4(b) units; `docs/implementation/slot2/WP-4_report.md`, `WP-5_report.md`):
- `HeckeExtAlgebraValidation()` — **`standard`**, ~0.10 s, **4930 checks**. The local algebra
  `A_S = F_ell[t_p : p ∈ S] ⊆ End(V)` of a block that `hecke::CertifyLocality` has certified
  local (`HeckeExt/HeckeLocalAlgebra`, [E] `sec:localalg` / `alg:stage3`), its coefficient field
  `K = F_ell[ŵ]` and generators `n_p = t_p − P_p(ŵ)` — **`ŵ` and the `P_p` consumed from the
  locality verdict, never re-derived differently** — the ideal `m_S = (n_p)_p`, its powers, `ν`,
  `soc A_S`, the Gorenstein verdict, the Hilbert function, and the tangent test **over `K`**
  giving `embdim = dim_{F_ell}(m_S/m_S²)/f`; **generation certificate (a)** ([E] `cert:cyclic`),
  whose `verify()` re-derives the closure (compared entrywise against the canonical RREF), the
  `n_p`, `m_S`, `dim m_S V` and `A_S v = V` rather than reading any of them; and **generation
  certificate (b)** of [E] `cert:comm` (`HeckeExt/HeckeGenerationCertificates`, [X] §2.2 Stage
  4(b)): `C = End_{A_S}(V)`, `dim C = dim A_S` proving `A_S = T_m`, gated by the **socle bound**
  `dim C ≥ dim A_S + f·t·s − dim_F soc A_S`, so `f·t·s > dim_F soc A_S` is a **proof** that (b)
  fails (`excluded_by_socle_bound` — every Gorenstein non-cyclic block, `(10, 691)` included,
  where the bound `2 + 4 − 1 = 5` is the exact `dim C`); where admitted, `X t_p = t_p X` solved
  inside the explicit `u`-element basis of `End_{F_ell[a]}(V)` for a fixed cyclic-most `a` in
  rational canonical form (`u ≤ m·D` against `D²` naive; the naive `O(k D⁶)` route ships as the
  validation oracle only, `over_budget` never a silent fall-back). `CommutantState` is **R3
  instance 3**: the `k·D²` rows stream into a canonical incremental RREF, `rows_done` is a pure
  function of the budget (`kCommutantBudget = 2·10^10` modmul, a named constant), `resume`
  continues from the row reached, refuses a lower budget, is a no-op on a complete state.
  `verify()` re-derives all eighteen clauses and **deliberately does not pin the RCF basis** (a
  rescaled cyclic block is another valid RCF basis and must still verify — the positive control
  of the sixteen-way tamper arm). `generation_verdict` is [X] §1.3.1 R3.2's `(a, b, c) → (kind,
  final, reason)` map; an ideal that cannot reach closure is **emitted** `final = false` with
  `closure_unreachable` / `budget_exhausted:commutant`, never withheld. The oracle is a closed
  form, not a second run: monomial algebras `F_{ell^f}[x_1..x_v]/(monomial ideal)` — `F[ε]/ε²`,
  `F[x,y]/(x,y)²`, `F[x]/(x³)`, `F_{ell²}[ε]/ε²` (**embdim 1 by the `K`-span test**),
  `F_{ell²}[x,y]/(x,y)²`, a non-cyclic `A ⊕ A`, the degenerate field, `V = A^∨` (where (b) passes
  and (a) fails) — each run plain and conjugated by a seeded **non-centralising** `U`, over
  `ell ∈ {5, 13, 691, 134217757}`; the `[XA B2]` negative control; the `[XA M5]` cross-block
  evaluation test; structured == naive == closed form; the R3 arms (interrupted at **every**
  reachable row count and resumed to a state and certificate entrywise equal to a fresh run's);
  and the two tamper arms (ten-way for (a), sixteen-way for (b)), each corruption failing exactly
  its own clause. The real-block arms (Sturm membership at `(10, 691)`, the joint `X_1 ⊕ X_4`
  decomposition) are E1b's. `Hecke/SubspaceOps` gains `RrefRowSpan`, `VecOfMatrix`,
  `MatrixOfVec`; `raw_mod_calls` 149 → 164 sites (all in `*Validation.*` TUs or `SubspaceOps.cpp`'s
  PERMANENT entry, now 8), 0 outside; `check_matrix_includes.sh`'s `Matrix.h` list gains
  `HeckeExt/HeckeLocalAlgebra.h`.

Added in hecke-extensions slot 2 (WP-7 / phase E4b — the parabolic cohomology and the two
recorded diagnostics; `docs/implementation/slot2/WP-7_report.md`):
- `HeckeBoundaryParabolicValidation()` — **`standard`**, ~4.7 s, 4966 checks on 75 cells
  (`ℓ ∈ {2,3,5,7,691,134217757,2^31−1}` × even `n ≤ 16` × `(p, ν) ∈ {(2,1),(3,1),(5,1),(7,1),(2,2)}`,
  plus `(20,5)`, `(24,5)`, `(10,13)` and the nine off-grid Kummer cells up to `ℓ = 2294797`). The
  ext-layer consumer `HeckeExt/HeckeBoundary` (`MatrixT<uint32_t>`) on top of `HeckeBoundaryDatum`
  / `HeckeBoundaryOperator`: **`H^1_! = ker r^1`** ([C] `cl:les`(2)) as the RREF kernel of the
  shipped restriction, `T_p`-stable with `A^{(1)} B = B A_!` by an exact solve on all 339 operator
  instances (asserted at `ℓ ≥ 5`, recorded and true at `ℓ ∈ {2,3}`), `dim H^1_! + rank r^1 =
  dim H^1`; the joint `1 + p^{n+1}` eigenspace by `HeckeIotaSignValidation`'s route-(a) rule — a
  line on every off-Dickson non-Kummer cell, **2-dimensional at every Kummer cell** ([E] D6: the
  Eisenstein and congruent cuspidal reductions are not separable mod `ℓ`); **Harder** ([E]
  `cl:harder`) from a pinned `num(B_k/k)` table (`k ≤ 26`), verdict `consistent` on all 37
  applicable cells — `r^1` vanishes on the whole joint eigenspace at the ten Kummer cells and on
  no non-Kummer line — recorded at `(10,5)`, `(10,7)`; the split `charpoly(A) = charpoly(A_!) ·
  charpoly(A_∂|_{im r^1})` (339/339), `χ_0` on the quotient at `n < ℓ` (131), `H^1 = H^1_! ⊕ Eis`
  (34 cells); the classical `dim H^1_! = 2 dim S_{n+2}` with `rank r^1 = 1` on 37/37 cells with
  `ℓ > n+1` — Kummer cells included, so **`H^1_! ≠ H^1` there**, against [E] v1.3.3 `sec:tests`
  (corrected in [E] v1.4.0); a seven-way tamper arm; the 15 golden collectors per `(p, ν)`
  (defined, never emitted) digest-stable in-process and across `ENGINE_THREADS ∈ {1, 16}` child
  processes; and the two diagnostics of `Hecke/HeckeBoundaryDiagnostics` — `cochain_commutes`
  (`r Θ_g = Θ_g^∂ r` on `C^q_eq(K)`) and `eta_zero` (the cusp-support walk of the bulk `τ`
  against `τ_∂`) — **recorded, never branched on**: both false on all 315 `(cell, p, ν)` pairs
  (the shipped `τ` is not a map of pairs; 10 of 12 vertex and 5 of 9 edge slots leave the boundary
  at `p = 2`, 11 of 12 and 6 of 9 differ from `j τ_∂`), with `eta_zero ⇒ cochain_commutes`
  asserted. Prints `BOUNDARY_DIAG …` and `BOUNDARY_PARABOLIC …`. `check_matrix_includes.sh`'s
  `Matrix.h` list gains `HeckeExt/HeckeBoundary.*`.

Added in hecke-extensions slot 2 (WP-8 / phase E5-1 — the first third of the cone chapter;
`docs/implementation/slot2/WP-8_report.md`):
- `HeckePairHomotopyValidation()` — **`standard`**, ~0.3 s, 113 596 checks on 152 tables
  (`(p, ν) ∈ {(2,1),(3,1),(5,1),(7,1),(11,1),(2,2),(3,2)}` × `ℓ ∈ {2,3,5,691,134217757}` × `n ∈ {0,2}`
  at u32, plus `(2,1),(3,1),(2,2)` at `2^61−1` / `2^32+15` (u64), both vertex-chain policies). The
  certified pair homotopy `Hecke/HeckePairHomotopy` (`HeckePairHomotopyT<Elt>`, no `ℓ`, no `n`;
  the first third of the Hecke datum of the pair `(τ, τ_∂, η)` the cone action consumes): built
  by [C] `lem:etaexists` — vertex slots by the `alg:tau` step-2 path device from `τ(s_j v)` to
  `τ_∂(s_j v)`, edge slots by the **unique** 2-chain with boundary `(j τ_∂ − τ j)(s_j e) − η(∂ s_j e)`
  through the one integer solver `HeckeIntegerSolve` — and certified in its constructor:
  `obl:eta`(i) (structure, canonical form, the same coset datum and model as `τ` / `τ_∂`, `τ`
  integral), (ii) the homotopy identity on every stored slot through the (T1) helpers, (iii) the
  (T1) bookkeeping across every stored transporter and the entry bound, (iv) solve regime `Z` for
  **every** `ℓ` with no mod-`m` path (OP2). The validation re-derives all four with an own
  canonical accumulation, own boundary operator and own (T1) translation, also on 12 random
  `Γ`-translates per slot; the table is `ℓ`/`n`/width-independent term for term; 27 tampered
  chains are rejected; `eta_zero` agrees slot by slot with `cusp_support_walk` (**false on all 152
  tables** — 5 266 of 7 504 slots are nonzero, so the `η`-table is genuinely needed); the two
  policies' tables differ on 2 342 slots and every difference is `∂Λ − Λ∂` for the unique
  degree-2 `Λ` (`lem:etaunique`); every one of the 3 216 edge fills solved on its initial
  neighbourhood with coefficients in `{±1}`; degrees built `[0, 1]`, `q_max = 1` derived,
  `truncated = false`. Prints the `p = 2` table, its JSON record and `PAIR_HOMOTOPY tables=152
  checks=113596 failures=0 …`. The cone action `Φ_g`, the derived `h = η̃` and `obl:eta`(v) are
  slot 3's, under a second validation name.

Added in hecke-extensions slot 1, phase E0a (WP-1; `docs/implementation/slot1/WP-1_report.md`,
`docs/implementation/hecke_extensions_slot1_plan.md` §3):
- `HeckeLocalityValidation()` — **`standard`**, ~6.4 s, **1356 checks**. The locality
  certificate `hecke::CertifyLocality` ([E] Cert. 5.2 / Claims 3.1, 3.3), declared in
  `Hecke/HeckeModuleDecomposition.h` and **called inside `compute()`'s refinement loop since
  slot-2 WP-1 (E0b)**. Constructed truths:
  48 non-local `(α, α^ell)` / `(α, α)` families that a **frozen copy of the pre-fix acceptance
  predicate** accepts and the certificate rejects — which slot-2 WP-1 now **splits** into their
  two maximal ideals at the default budget, while a forced budget of one candidate reproduces
  the unsplit pre-fix block for the frozen predicate to accept and the certificate to reject
  (the bounded exit), plus the R3 resume arm `run(1) + resume(64) == run(64)` modulo
  `budget_history` and the `HeckeSettings` arm (defaults, parsing, fingerprint, the named
  strict-mode error, propagation onto `run_concurrently()` tasks); 18 genuinely local algebras
  (`F_{ell^f}[ε]/ε²`, `F_{ell^f}[x,y]/(x,y)²`); the Teichmüller trap `t = α + ε` with the v1.0
  recipe's `0` as the negative control; 36 `k = 1` analytic-vs-matrix twins. Plus **the grid
  arm**: every decomposition the golden harness builds (236 decompositions, 348 blocks) is
  recomputed, certified, and all four golden hashes are re-checked against
  `GoldenReference.inc` through a lookup. It prints
  `LOCALITY_GRID decompositions=236 blocks=348 analytic=269 nonlocal=0 witness_changes=0
  loop_disagreements=0 hashes=944 failing=0 []` — **the E0a verdict: every block on the golden
  grid is local**, so by [X] §3.3's Claim E0b cannot move a `decomp_*` hash — and it did not:
  E0b's re-baseline was exactly the 384 report lines.
- `HeckeLocalityProbe()` — **`slow`** *and* interlocked on `HECKE_LOCALITY_PROBE=1`, so it runs
  in neither `--all` nor `--all-full` nor `Check` nor `cross_config.sh`. The `(160, 691)` probe
  of [Q17]: `{T_2, T_3, T_5}` at `q = 1`, **recorded, not asserted**.
- `GoldenDump()` — the "before"/"after" object dump of E0b's re-baseline protocol ([X] §1.6
  steps 1–4): every text object (555) and every decomposition's block list (236) written to
  `<dir>/{index.tsv,texts.tsv,decompositions.txt}`. **Owner-gated exactly like `GoldenEmit`**: a
  no-op unless `GOLDEN_DUMP=<dir>` is set, so `--all` stays read-only.
  `docs/matrix-engine/tools/golden_explain.py before after [--allow-keys FILE]
  [--accept-split "<point> <object>"]…` diffs two dumps, failing on any JSON key path outside the
  allow-list and on **any** change to a decomposition block list that is not an owner-accepted
  split.

Added in hecke-extensions slot 1 (WP-5 — console phase C0, the language core; binding design
`docs/console/00-console-interface-plan.md` v2 §10 Phase C0):
- `ConsoleC0Validation()` — **`fast`**, ~0.03 s, **612 checks** over `ConsoleCore` only (it
  constructs no matrix and touches no pipeline arithmetic, so it can change no golden value):
  lexing (every literal form, comments, `\` continuation, the reserved-word list, every lexical
  error), parsing (every production of the §3.2 EBNF, the precedence table, terminator rules,
  caret positions), evaluation (overflow-checked `int64_t` arithmetic, exact `/`, `for`/`if`,
  loop-variable shadowing, `;` suppression, `include` + include cycles, `args`, `expect_error`,
  the exit-code table 0/1/2/3/4), printing (canonical vs display form, the `print_max_entries`
  cap, `show`, JSON escaping), the registry (overload resolution in registration order, keyword
  arguments, defaults, arity/type errors, members and methods on a stub type it registers
  itself), the settings layer and the handle model (see below), the drivers (REPL error
  recovery, `RunFile`, the `#~` annotation, `ChatterCapture` over `cout` **and** `cerr`), the
  C0 (c) floor (10 000 statements parsed + evaluated in ~0.015 s against a 0.5 s floor), and the
  slot-1 **"no transcript freezing before E0b"** guard: a C0-only registry has no `hash` /
  `golden` / `cohomology` / `hecke` / `decompose` / `report` verb, no type fills
  `TypeInfo::hash`, and no `*.expected` / `*.transcript` file exists under `Console/`. It also
  runs `check_console_includes.sh` over the checkout (probed, not required, like
  `check_matrix_includes.sh` in `ConsumerMigrationValidation`).

Added in hecke-extensions slot 1 (WP-4a / phase E4a — the certified boundary datum of contract
chapter `sec:boundarydatum`, `docs/latex/gl2_contract.tex`):
- `HeckeBoundaryTauValidation()` — **`standard`**, ~0.03 s, 52,686 checks on 138 tables. The
  Γ-level boundary datum `τ_∂` of `Hecke/HeckeBoundaryDatum` (`HeckeBoundaryTauTableT<Elt>`,
  chains in `HeckeTauTable`'s `ChainTerm` format, certified in its constructor — invariant I8)
  and its `B_N/Γ_∞` table, over `(p, ν) ∈ {(2,1),(3,1),(5,1),(7,1),(11,1),(2,2),(3,2)}` ×
  `ℓ ∈ {2, 3, 5, 7, 691, 134217757}` × `n ∈ {0, 2, 10}` at `u32` and `ℓ ∈ {2^61−1, 2^32+15}` at
  `u64`: `obl:taubdry`(i)–(iv) re-derived independently of the table's own helpers (single
  component; the forced component map `c ↦ g^{-1}c` recomputed from `g` alone; `(T2∂)` through
  an own boundary operator and an own `(T1∂)` translation; the `(T1∂)` bookkeeping across
  `i(v3) = T·i(v0)` and on random words; coefficients in `{±1}` with solve regime `Z` for
  **every** `ℓ`, `ℓ ∈ {2, 3}` included), `prop:bdrycosets`(1)–(3), the `ℓ`/`n`/element-width
  independence of the table (it is a datum over `Z`), seven tampered chains rejected by
  `certify_with_override`, and the `(B1)–(B3)` boundary subcomplex data of
  `SL2ZTessellationTables`. Clauses (v)–(vii) (the operator `Θ^∂`) are WP-4b's.

Added in hecke-extensions slot 1 (WP-4b / phase E4b — the boundary Hecke operator of the same
chapter; `docs/implementation/slot1/WP-4b_report.md`):
- `HeckeBoundaryOperatorValidation()` — **`standard`**, ~5.5 s, 19,669 checks on 546 cells
  (`(p, ν) ∈ {(2,1),(3,1),(5,1),(7,1),(2,2),(3,2)}` × `ℓ ∈ {2,3,5,7,11,13,101,691,134217757,2^31−1}`
  × even `n ≤ 16` at `u32`, plus `ℓ = 2^61−1` at `u64`). The operator `Θ^∂_g` / `T_p^∂` of
  `Hecke/HeckeBoundaryOperator` (`HeckeBoundaryOperatorT<Elt>`) on the circle model
  `C^•_eq(K_∂, Rel_∂; L)` (`LocalSystemSL2Z::CreateSL2ZBoundaryPathTriangulation` /
  `GenerateSL2ZBoundaryRelationsElt`, lifted out of the demo) — the normative `eq:bdrychain`
  assembled from the bulk's own `s_j`, `δ_j` and WP-4a's `τ_∂` in two bracketings asserted
  `memcmp`-identical, `A_∂^{(q)} = P_q Θ^∂ z_i`. **`obl:taubdry`(v)**: route A (the Shapiro
  transcription — a Γ_∞-level twisted datum on the ∞-line with the canonical left cosets
  `δ_∞, δ_t`, no `τ_∂`, no class map) and route B (`Σ_δ ρ_n(δ)` on `V^T`, `eq:bdrygroupform`
  on `V_T`, re-derived in the validation) both equal the normative operator on cohomology,
  entrywise, on every cell — `p = ℓ` and `ν = 2` (route B, `H^0`) included. **(vi)**: every
  `x^{n−bℓ} Nm^b` (own polynomial arithmetic) has eigenvalue `χ_b(p) = p^b + p^{n+1−b}` on `H^0`
  (575 vectors) and `[y^n]` has `1 + p^{n+1}` on `H^1` for `n < ℓ` (232 cells) — asserted; the
  general-`n` `H^1` multiset of `cl:chi`(2) recorded, 330/330 cells agree. **(vii)**
  `r^q A^{(q)} = A_∂^{(q)} r^q` against `HeckeOperatorOnK` through the public restriction
  morphism, asserted on 864 `(cell, q)` pairs at `ℓ ≥ 5`, recorded at `ℓ ∈ {2, 3}` (216/216
  hold). The `β_j` right-coset **negative control** (`prop:bdrycosets`(4)) gives `χ_{b+1}` in
  place of `χ_b` (212 cells differ) and breaks (vii) on `H^1` (170 cells), as it must. The circle
  model is computed at **every** `ℓ` and recorded (`boundary_model = circle`,
  `boundary_is_group_cohomology = (ℓ ≠ 2)`, `q_max = 1` derived, `truncated = false`), with the
  `ℓ = 2` dimensions asserted to be `prop:circlemodel`(2)'s and never `lem:ell2unbounded`'s.

Added in hecke-extensions slot 1 (WP-3 / phase E1s — the extension layer's first unit,
`src/hacs/HeckeExt/`; `docs/implementation/slot1/WP-3_report.md`):
- `HeckeSturmBoundValidation()` — **`fast`**, ~0.011 s, **1306 checks**. The computed Sturm bound
  `B'(k, ell)` of `docs/latex/hecke_extensions.tex` `def:bprime` / `cl:bprime`: the least prime
  bound `B` for which the `F_ell`-**algebra** generated by `T_q mod ell`, `q ≤ B` prime, on the
  Miller basis of `M_k(F_ell)` reaches dimension `dim M_k`, with the default cap `12·B(k)` and the
  outcome recorded either way. The unit (`HeckeExt/HeckeSturmBound`) is **pipeline-free** — no
  cohomology, no coset table, only `q`-expansions of `E_4`, `E_6` and `Δ = q ∏ (1−q^n)^24` reduced
  mod `ell` as they are formed (no bignum, no division by 1728, so `ell ∈ {2, 3}` work too) — which
  is why a whole grid of bounds costs 11 ms. Arms: the `q`-expansions against **exact-integer**
  `σ_3` / `σ_5` and the published `τ(2..7)`, and against the independent `E_4^3 − E_6^2 = 1728Δ`;
  `dim M_k` against `#{(a,b) : 4a + 6b = k}`; the echelon Miller basis and its stability in the
  precision; `T_q` on `M_12(F_691)` with `τ(q) ≡ σ_11(q)`; **20 pinned bounds** (`B' = 2` on all ten
  Kummer cells of [E] Claim 1.8 and at `(12,691)`, `(34,131)`, `(162,691)`, `(200,691)`; `5` at
  `(24,5)`, `(30,5)`, `(32,5)`, `(36,5)`, `(60,5)`; `7` at `(28,7)`; `3` at `(36,7)`), each with
  `SturmBoundCertificate::verify() == 0` and two tampered variants failing; the **proper**
  subalgebra `⟨T_2, T_3⟩` of dimension `2 < 3` at `(24,5)` and `(28,7)`, i.e. the counterexample
  that makes the naive `B(k)` sweep unsound; and the **resumable-state contract** R3 of
  `hecke_extensions_implementation_plan.md` §1.3.1, of which the Sturm bound is instance 1 and this
  the first implementation — a `none_at_cap` under a forced `cap = 3` at `(24,5)` **recorded, not
  thrown**, `resume(cap = 36)` reaching `B' = 5` with a state and certificate **entrywise equal** to
  a fresh run's, `resume(cap = 2)` refused with the named error, a resume on a complete state a
  strict no-op, and `budget_history == [3, 36]`. Slowest pinned case `(k, ell) = (258, 691)` at
  **1.4 ms**, against the plan's 0.1 s target.
- `HeckeExtArchitectureValidation()` — **`fast`**, ~0.02 s. Runs
  `docs/matrix-engine/tools/check_heckeext_includes.sh` over the checkout via `std::system` (the
  `MatrixRetirementValidation` pattern); see "Migration tools" below for its four rules.

Added in hecke-extensions slot 1 (WP-2 — the E0a remainder; `docs/implementation/slot1/WP-2_report.md`):
- `HeckeIdentityValidation()` — **`fast`**. The E0a subset of [X] §1.3's `IdentityCertificate`
  (`HeckeExt/HeckeIdentityCertificate.{h,cpp}`, `MatrixT<uint32_t>` + `engine::ModCtx`, no
  `HeckeCrossChecks`): Eichler–Shimura in its `dim H^0`-robust form
  `dim H^1 = dim M_{n+2} + dim S_{n+2} + dim H^0` (holds at Dickson-exceptional loci), Hecke
  commutativity `[A_p, A_p'] = 0` (every `ell`), `d_2 = 0` (`dim H^2 = 0`), and the `p^2` recursion
  `A_{p^2} = A_p^2 − p^{n+1}·I` checked against the **independent** double-coset route
  `T_p_pow_direct(p, 2)`, never the recursion's own output (gated on `ell ≥ 5`, as the recursion
  itself is). `verify()` re-derives every value with its own `dim M_k` / `dim S_k`. Ten real
  pipeline points (classical; Dickson-exceptional `(6,5)`, `(12,5)`, `(8,7)`; `n = 0`; odd `n`;
  `ell < 5`) plus a four-way tamper arm in which each corruption fails exactly its own item.
- **`Hecke/DicksonCount.h`** — `hecke::DicksonInvariantCount(n, ell)` /
  `IsDicksonExceptionalCount(n, ell)`, replacing the three file-local `IsDicksonExceptional` copies
  (`HeckeOracleValidation.cpp`, which had under-approximated the locus with the first Dickson
  generator only — no row of its own grid changes — `HeckeEndToEndValidation.cpp` and
  `Golden/GoldenHarness.cpp`; the golden `dickson` tier-A entry is unchanged).
- **`src/ModArithmetic/Fnv.h`** — the one byte-wise FNV-1a-64 (`kFnvOffset64`,
  `FnvU64`, `FnvBytes`, `FnvHasher`), shared by `Golden/GoldenHarness.cpp`,
  `Campaign/CampaignDriver.cpp` and `PerformanceSmokeValidation.cpp` (previously three copies of the
  same function) and by `HeckeSturmBound`'s `state_ref.fnv64` / `state_fnv64` integrity field —
  since the slot-1 close (WP-7) from the **standard** offset basis `kFnvOffset64 =
  0xcbf29ce484222325`, so a recorded state hash is the same function as every other recorded hash
  (WP-3's historical seed `1469598103934665603` had pinned nothing). `BlockPool.h`'s word-wise hash and `engine::tape::fnv_mix` are different functions and
  are deliberately not folded in. Value-preserving: golden, campaign and determinism digests unchanged.
- **`U_ell` RSS** (recorded, not gated): `--bench hecke 128 691 691` 2716.7 MB, `hecke 256 131 131`
  1677.1 MB; `hecke 16 43867 43867` does not run out of memory but throws a **pre-existing**
  `exact multiply overflow` (`Hecke/ExactInt.h`) in `U_ell`'s coset construction, independent of
  `n`, first seen between `ell = 3617` and `ell = 5003` at `n = 16` — an open finding. The two
  fits of `rss_mb = (ell+1)(c0 + c1 (n+1)^2)` (report §4) agree on `c1 ≈ 1.8–1.9e-4` and disagree
  4.4× on `c0`; re-fit on a wider grid before freezing E1b's constants. *(Historical, slot 1: the
  overflow site was misattributed — it is `alg:tau` step 1, repaired in slot 3 WP-1, and the
  constants are frozen as `u_ell_rss/v2-2026-09-17`; see "Hecke action" → "Reach of `U_ell`".)*

**Slot 13 (hecke-extensions, 2026-09-26 / 27): seven new names, registered only in `Registry/Slot13/WP<n>.cpp`
(fragment order WP4, WP5, WP6, WP9, WP10, WP11); arms added to existing names by WP-7, WP-12, WP-14.**

- `HeckeUEllLowRankValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL"; **S24 CL-R1: OFF 44 checks (arm (M) only), ON 388 = 44 + the 344 below**, see "Slot 24 CL-R1") — **`standard`**, **344 checks, ≈ 13 s** (slot-13 WP-4, 230; +3 by WP-14's arm (E); +77 by WP-16's arm (F); +34 by arm (G), `c0566e2`;
  `Registry/Slot13/WP4.cpp`): the `U_ell` memory lever (`HeckeOperatorOptions::ScopedUEllLowRank`) is value-preserving.
  (A) under the lever `A^{(q)}`, `Θ_flat^{(q)}`, `Θ_eq^{(q)}` and the certificate bundle equal the default at
  `ell ∈ {5, 7, 11, 13, 691}`, `n ≤ 36`, plus `T_{ell²}` at 5 and 7; (B) the refusal on `T_2`; (C) `H_matrix_module(q)`,
  `Θ_module(q)` over `Z/ell²` and `Z/5³`; (D) printed: `U_691`, `n = 128`, peak above the cohomology, default 2041 MiB,
  lever 248 MiB; (E) (WP-14, audit A1) τ built outside the scope and compute inside (the `!tau_factored` branch) equals
  the default; τ inside, compute outside → `logic_error` naming `ScopedUEllLowRank`; `RhoRefT::get()` on a factored
  pool throws; (F) (S13 WP-16) the **legacy arm** in-process (`ScopedLegacyHeckeOperatorPath` + `engine::elim::ScopedLegacy`)
  under the lever at five cells (`ell ∈ {5, 13, 691}`, `T_{7²}`): `A^{(q)}`, `Θ_flat`, `Θ_eq` equal to the default route's and
  `A^{(q)}` to the legacy arm's without the lever (the factored τ pool read as `U V`), plus the two refusals on that arm.
  (G) (`c0566e2`, the WP-17 §8.2 legacy fix) E7's `ContragredientCell(n, 5).hecke_pair(5)`, `n ∈ {10, 24}`, on the legacy arm
  under the default `Auto` lever (one factored τ table shared by `op_M` / `SymN` and `op_D` / `ContragredientN`) against the
  default route with the lever off: both operators' `A^{(q)}`, `Θ_flat^{(q)}` and O12(a).
  Passes under `ENGINE_BACKEND=legacy` too (≈ 86 s there). The rank claim (`≤ min(k, n + 1)` terms per singular block) is `ENGINE_CHECK`ed inside every run.
- `HeckeHidaControlValidation` — **`standard`**, **1134 checks, ≈ 58 s, ≈ 1.1 GiB** (slot-13 WP-5; `Registry/Slot13/WP5.cpp`,
  `HeckeExt/HeckeHidaControlValidation.cpp`): [C] `rmk:hidacheckable2`'s (Hi7)–(Hi9) on 49 cells in one pool (≤ 12
  threads, heaviest first; the `(210, 5)` mod-`5³` cell is the long pole). (P) / (N) the (Hi8) decision procedure's
  positive and negative controls (177 / 177 different-class pairs "not isomorphic"; synthetic conjugates; a Jordan
  block vs. the scalar); (Hi7) `χ^ord` mod `ell³` on `Tw_3(5; 10) = {10, 110, 210}` read on `H_3` over `Z/5^K`,
  `K = 3 + e_max`, with the control `n = 30` (equal mod 25, different mod 125); (Hi8)(a) the lattice datum on
  `Sym^n` and (b) on Hida's `L_n` (`FibreRepresentation::HidaLatticeH`) constant on 130 `Tw_1` + 15 `Tw_2` pairs, each
  "isomorphic" with a certificate `P` re-verified over `Z/ell^m`; (c) `D_*` equivariant on all of `H^1`, maps ordinary
  into ordinary, an isomorphism at the 14 Lucas cells (reported 45 / 45 at `m = 1, 2`); (Hi9) `T_5`, `T_7` 157 / 157
  and the Eisenstein root at every `p ∈ {2, 3, 5, 7} \ {ell}`. 184 `HIDA_TOWER` lines (`lattice=`, `charpoly_T5`,
  `charpoly_T7`, `module_digest=`, `Dstar_iso=`). The `ell = 7` (Hi7) pair (187 s) is **not** in the suite.
- `HeckeHidaLevelEllValidation` — **`standard`**, **2906 checks, ≈ 42 s, ≈ 1 GB** (slot-13 WP-6;
  `Registry/Slot13/WP6.cpp`, `Hecke/HeckeHidaLevelEllValidation.cpp`): `Γ_0(ell)` on the model by Shapiro
  (`Hecke/HeckeLevelEll`). Cells: `F_1000003` (the characteristic-0 surrogate) at ten `(n, ell)`, rings `Z/ell²`,
  `Z/5³` at eight, `F_ell` on the 92 (Hi10) cells. Arms (R) `eq:Ulevellmodel` = `eq:levelcorr` entrywise as cochain maps
  and `eq:levelcorr` at `A = B = Γ` = the shipped `Θ_g` and `A^{(1)}(T_ell)`; (X) the level-`ell` operators are cochain
  maps; (O) `prop:oldspace` (1), (2) as cochain maps, (3), (4), the new space; (H) `U`, `T_2`, `T_3` commute at level
  `ell` and intertwine `dg_1`, `dg_ell`, `ω`; **(G) an independent group-cocycle route** (Shapiro on `⟨S, T⟩`, its own
  coset table, class map and word decomposition, no τ; joint charpolys agree) with a negative control (the varpi row
  with its `(1:0)` block kept); (S) `prop:levelorbit`(3); (T) `lem:levelelltorsion`(1); (St) `prop:stabilisation` as
  `(e_ell ∘ dg_ell, c_st^{-1} ω)` mod `ell`, `ell²`, `ell³`; (Hi10) on 92 cells.
- `HeckeCensusLatticeValidation` — **`standard`**, **69 checks, ≈ 32 s, 0.77 GB** (slot-13 WP-9; `Registry/Slot13/WP9.cpp`,
  `HeckeExt/HeckeCensusLattice.{h,cpp}`): C-F9 (`m_A² = 0` on `H^1(Sym^n Z_ell)^±_m`, [E] `pr:latticesplit`) — (P) the
  detector on planted data, the default census cells through both routes (the `Z/ell²` lattice by the shipped module
  route with the Fitting projector `e_m`, and the `F_ell` block), the verdict pinned to the observed `held`. Env hooks
  (read-only): `HECKE_CENSUS_LATTICE_ALL=1` (all 655 non-reduced edition-2 rows: 654 held, 1 `not_applicable:H0`;
  51.7 min sharded), `HECKE_CENSUS_LATTICE_CELLS`, `HECKE_CENSUS_LATTICE_TSV`.
  **Since slot-16 WP-3** (rows added by WP-2 from `docs/implementation/slot16/WP-3_report.md`): `HECKE_CENSUS_LATTICE_U_ELL=<mb>` (read-only;
  overrides the `u_ell` budget the lattice arm takes from the row's source set — np sets 16384, `ext_u691` 8192; printed as `u_ell=` on
  the `EFFECTIVE` line), `HECKE_CENSUS_LATTICE_RECORDS=<dir[:dir…]>` (the record roots for the eigen-system join; default the tree's
  results; `join=` on the `EFFECTIVE` line), `HECKE_CENSUS_LATTICE_JOIN_ONLY=1` (the driver, blocks, eigenvalues, signs, Loewy lengths and
  the join only; skips the `Z/ell²` module run and (F), (L), (W); reported as `arm=JOIN`).
  **Since the slot-16 WP-3 audit repairs** (`docs/implementation/slot16/WP-3_WP-5_audit.md`, Repairs): **91 checks, ≈ 36 s** — the
  new default arm (J) (22 checks, a few ms) gates the record reader on a tracked record, the `u_ell` table against
  `WP-3_expected_uell.tsv`, malformed records and `JoinRow` on synthetic cells (the WP-12 §8.1 merged-ideal negative control).
  The witness join checks the operator set and must match uniquely; a residue-degree-1 row that fell back prints
  `CENSUS_LATTICE_FALLBACK` and is counted (`…,refused:<c>,fallback:<k> records=<roots>` appended to `EFFECTIVE`); an explicit
  `HECKE_CENSUS_LATTICE_RECORDS` naming no root or a missing directory fails, as does one under which every residue-degree-1 row
  fell back; a malformed `CELLS` token is refused by position and a `CELLS` list selecting no row fails; the `U_ELL` override
  waives the unknown-set refusal, as in arm (T).
- `HeckeSaturationDefectValidation` — **`standard`**, **299 checks, ≈ 23 s, 0.19 GB** (slot-16 WP-5, 170 checks / 12 s; the audit repairs
  added arm (H); `Registry/Slot16/WP5.cpp`, `HeckeExt/HeckeSaturationDefect.{h,cpp}`): `I_m = Tor_1^{Z_ell}(T^sat/T_m, F_ell)` per
  torsion-free block, two routes (R-ker, R-len), the `ε`-filtration and `T^sat/T`, the note's predictions (`WP-5_tor_note.md` §4) at
  `(82, 7)`, `(142, 7)`, torsion refusal at `(18, 5)`, agreement with `ComputeRingLoewyCell`, and (H) the hidden-chain law L-F1 at its
  cheapest instance `(168, 13)` (`I = m`, dim 1, principal, Loewy 1, `Ann I = m`, `T^sat/T = Z/13`; other blocks `I = 0`). **The forms
  cross-route runs at `k = n + 2 ≥ 12` only.** Env hook `HECKE_SAT_DEFECT_CELLS="n:ell[:KMAX],…"` (read-only): a set-but-empty value fails;
  fields range-checked, `ell` prime, a bad cell refused by position (since slot-24 ELL-W audit F6 also `n + 2 ≥ 12` with `ell ≥ 2¹⁶`:
  the forms cross-route cannot run, refused at parse time instead of after the module run); `SAT_DEFECT_REFUSED` lines; `EFFECTIVE … arm=CELLS cells=<k>
  refused_cells= blocks= ok= torsion_refused= not_stable= strict= expectations=<held>/<k>` after the run; a cell with no ok block fails
  unless all its blocks are torsion refusals; `HECKE_SAT_DEFECT_STRICT=1` fails `not_stable_at_KMAX` too. **Hook-only expectations**
  (28–124 s per cell): `(220, 17)`, `(238, 17)` (`j = 2`), `(246, 19)` the hidden chain as in (H); `(258|294|296|334, 37)` `I = 0` on every
  block with a saturated Kummer block present.
- `HeckeHidaHeavyCellProbe` — **`slow`, interlocked** on `HECKE_HIDA_HEAVY=1` (without it `[SKIP]`, return 0, even
  under `--all-full`), 9 checks per cell (slot-13 WP-10; `Registry/Slot13/WP10.cpp`): the heavy Hida cells from
  `HECKE_HIDA_HEAVY_CELLS="n:ell:m,…"` (default `100:691:1,200:691:1,400:691:1,700:691:1`), `m = 1` the field route,
  `m ≥ 2` the module route, `U_ell` under the lever, only `e_max = 0` served. Gated: `U T_p = T_p U`, `T_2 T_3 = T_3 T_2`,
  `B X = T B` on every row, (Hi5)'s Eisenstein half, and at `n ≤ 40` equality with the slot-12 reader. Reported (not
  gated): `HI11`/`HI12 … verdict=HELD|FAILED` — **since slot-14 WP-2**, automatic on every requested cell with
  `ell ∈ {691, 2411}` and `n ≡ 10 (mod ell − 1)` (not just the single literal point `(700, 691)`), against the
  `n = 10` reference of the same class computed in-process and cached per `ell`; `n = 10` itself is not compared
  against itself. Measured: `(700, 691)` `m = 1` 13.65 GiB / 61 s, `m = 2` 33.45 GiB / 47 min — predict
  RSS first (rule 19).
- `HeckeMixedFinalityValidation` — **`slow`**, **163 checks, ≈ 2 s** on its default cells (slot-13 WP-11, repaired
  after the referee; `Registry/Slot13/WP11.cpp`): the evidence arm of the `mixed` finality proposal (Proposition M,
  (d2) "Dickson-mixed"; `WP-11_mixed_finality_proposal.md` v2) — (H5) and (d2) exactly as Corollary M1 (`trivial:S_V=0`,
  `trivial:K=0`, `complementary` gated never to pass, `reduced:J=0`, the literal (H5)), a planted arm
  (`MIXED_FIN_PLANT`), pins at `(34, 7)` ideal 2 and `(50, 7)` ideal 3; `MIXED_FIN_CELL` lines with the cost split. Scan
  hook `HECKE_MIXED_FINALITY_CELLS` (the `ell = 7`, `n ≤ 400` probe: 2303 checks; `ell ∈ {11, 13}`: 2782; 0 failing,
  no non-injective Dickson-type block). Writes nothing; no finality logic changed.
- `HeckeBocksteinCuspValidation` — **`fast`**, **1447 checks, 0.05 s** (slot-13 WP-11, referee m6;
  `HeckeExt/HeckeBocksteinCuspValidation.{h,cpp}`): pipeline-free over `Sym^n(Z/ell²)`, on `ell ∈ {5, 7}`, `n ≤ 300`, and
  `ell ∈ {11, 13}`, `n ≤ 240` (318 cells, 467 classes): `rank(β^0_∂ ∘ r^0 | class) = #monomials − #Frobenius powers`
  per class and cell — certifying Claim (H4′) (`r^1` injective on `im β^0`) cell by cell on that range; pins
  `rank β^0` at `(26, 5)`, `(30, 5)`, `(300, 5)`, `(56, 7)`.
- **Arms added to existing names.** `HeckeExtRecordValidation` arm v5 (WP-7: the `(26, 5)` record's `boundary_data`,
  tampers 32a–h each refused by `verify()` code 32; 966 checks); `HeckeBoundaryFinalityValidation` (WP-7: the
  record-side re-derivation equals the in-process verdict on every row it drives, `BoundaryDataRederive`'s clauses on
  synthetic data, G5's synthetic `failed:<class>`; 13 418 checks, ≈ 17 s); the schema string `hecke_ext/v5` in four
  validations and script 040's assert (WP-7, no transcript moved).

**Slot 14 (hecke-extensions, 2026-09-28 … 2026-09-29; closed by WP-17; window W1 run 2026-09-29, figures in `docs/implementation/slot-history.md` — the WP-2 / WP-3 arms are recorded in their names' entries
above).** New names (four; roster 155 → 159 = 59 `fast` / 85 `standard` / 15 `slow`): `ValidationHarnessCatchValidation` (WP-2, above, `Registry/Slot14/WP2.cpp`),
`HeckeRingLoewyValidation` (WP-6, `Registry/Slot14/WP6.cpp`), `HeckeUEllStreamValidation` (WP-10 + G0, `Registry/Slot14/WP10.cpp`) and
`HeckeLevelNValidation` (WP-12, `Registry/Slot14/WP12.cpp`; each with its `cmake/slot14/WP<n>.cmake`). No golden line or digest moved; wall times of record: W1 (`--all` 702.1 s, `--all-full` 1240.3 s):

- `HeckeRingLoewyDigitSlowValidation` — **`slow`**, **22 checks**, ≈ 4.6 s (S15-O1, owner 2026-10-01; `Registry/Slot15/WP5.cpp`): arm (C3) of `HeckeRingLoewyValidation` (the digit route, u64 == digit, `ell = 5`, `K = 28` beyond `2^64`; slot-15 WP-5) split into its own name, checks and values unchanged. Roster 162 → 163 = 59 / 88 / 16; `--all` stays at 147, `--all-full` 163. `HeckeRingLoewyValidation` keeps the other arms: 159 checks (123 + the WP-5 additions minus (C3)), ≈ 80 s after the split alone ((C3) was only 4.6 s of the 82 s); a validation-local `RunModuleCached` for the repeated module runs of arms (a), (C1), (C2) brings it to 63.8 s, still over 60 s (further cut needs the owner: move the four largest census rows). **The owner set this name's target to 64 s on 2026-10-01**, so 63.8 s meets it; no census row moves.
- `HeckeRingLoewyValidation` — **`standard`**, **123 checks** (slot-14 WP-6, `HeckeExt/HeckeRingLoewyValidation.cpp`; audit S1): the `Z/ell^K` Hecke-algebra
  route (`HeckeExt/HeckeRingHeckeAlgebra`, [E] v1.15.1-pre.2 `sec:ring`, its `stable` verdicts readings, not certificates) against its oracles: (P) planted modules
  (`(Z/49)^2` with `T^2 = 7`; the hidden algebra `T = 7·swap`, `ε = 1`; `Z/7^3 ⊕ Z/7` read with shift `t = 1`, incl. an `ENGINE_CHECK` negative arm); (a) [M1] §5.1 —
  `(82, 7)`, `(142, 7)` at `K ≤ 4` block by block and the `(10, 691)` control; (b) `A_1` = the census algebra
  on 20 non-reduced rows; (c) `A_K/ell` at the stable `K` = the forms-side `T_m/ell` on the same rows; (d) one torsion block, `(112, 7)`; (W) native `u32` route vs
  `hida::RunModuleCell` (`u64`) at `(58, 7)`; (e) C-F9 (`m_A² = 0`) pinned to what the runs observed (a change is a finding about a conjecture). Env
  `HECKE_RING_LOEWY_CELLS="n:ell[:KMAX],…"` (read-only, not an emitter; `KMAX` 7 at `ell = 7`, else 6): the route over the listed cells, lines `LOEWY_RING`,
  `LOEWY_RING_SUMMARY`, `LOEWY_RING_CELL`, `LOEWY_RING_REFUSED`, `HECKE_RING_LOEWY_EFFECTIVE`, and C-F9 failures **reported** as `LOEWY_RING_CF9_FINDING`, never gated.
  **Since slot-15 WP-5** (no new name; 123 → **181 checks, ≈ 85 s**, ≈ 0.14 GB — over the 60 s `standard` target, recorded by WP-17; since S15-O1 (C3) is `HeckeRingLoewyDigitSlowValidation` and the target of this name is **64 s** (owner 2026-10-01), met at 63.8 s after the module cache):
  the `stable` verdict is a **certificate** citing [C] `cor:stablecert` (`CertifyStable`; the label reads "core only: no Setting check
  (2')"), and `ell^K ≥ 2^64` runs on the digit route. **(C1)** every stable-family verdict of (a)–(d) certified
  (`LOEWY_RING_CERT label=cor:stablecert stable_family=85 certified=85`); **(C2)** negative controls refused (length/dim/eps/`f`
  perturbed, `stable` one level early, wrong `n`, `K_cls ≤ e_max`, planted `A_K`, perturbed `T_2`, and the WP-5 audit's M6 set);
  **(C3)** u64 route = digit route line for line at `(58, 7)`, `(30, 5)`, `(34, 5)`, and beyond `2^64` (`5^28`) the digit module
  meets the u64 prediction and is certified. Passes under `ENGINE_LADIC_WIDTH` 32 / 64 / 128 (WP-5 report).

- `HeckeUEllStreamValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL"; **S24 CL-R1: legacy-gated whole name, `[SKIP]` in OFF builds, 2262 checks ON; source now `Hecke/legacy/`**) — **`standard`**, **2262 checks, ≈ 27 s** on a shared box (slot-14 WP-10, 1577 checks;
  +14 by WP-16's (B) failing direction; G0 arms (H) and (I), 2004; the G0 repairs' `ell ∈ {2, 3}` rows, the dense-pool
  arm and the two-pool case, 2262; `Hecke/HeckeUEllStreamValidation.cpp`): the three `U_ell` levers — the low-rank
  lever (slot-13 WP-4), **coset streaming** (`ScopedCosetStreaming`) and **the serial phase on the pool**
  (`ScopedParallelSetup`) — and G0's **rank-one closed form** (`ScopedRankOneClosedForm`) cannot change a value. The
  levers are the **defaults** since the owner decision of 2026-09-28 (Q8), so the reference of every arm is the
  **opt-out** path. (A) every `ρ_n` block of a streamed and of a parallel-built coset table equal to the default's,
  the DoD batteries on a streamed table, its reference accessors refused, `uint32_t` and `uint64_t`; (B) the τ table
  under `ScopedParallelSetup`: the same ξ terms and pool slot by slot (dense and factored), (f) passing, and its
  failing direction (a corrupted slot → `certify()` 60, serially and in parallel); (C) `U_ell` at `ell ∈ {5, 7, 11, 13,
  691}` (+ `T_{ell²}`, `T_2`, the legacy arm): `A^{(q)}`, `Θ_flat`, `Θ_eq`, the certificate counters of every lever
  combination equal; (D) `Z/ell²`, `Z/5³` (the module route); (E) `ENGINE_THREADS = 1` vs 16 in-process; (F) the
  α/β/ω cross-checks on a streamed table; (G) printed: `U_691`, `n = 128`, peak RSS with and without streaming;
  **(H)** (G0) the closed form (`lowrank::rank_one_rho_factors`) against the dense route, `(t, U, V)` and `U V == ρ_n`
  entrywise, over **every** 2×2 key at `ell ∈ {2, 3, 5, 7}` (2 and 3 since the G0 repairs, audit S2) and structured +
  pseudo-random keys at `ell ∈ {11, 13, 691, 2411}`, `n` up to 2420, both widths, `binomial_row_mod` against `ρ_n`'s
  binomials; the negative direction (every non-singular key refused by both routes, a perturbed factor caught, a
  composite ring refused); the τ pool with and without the closed form at `(2, 2, 8)`, `(3, 3, 8)`, `(5, 5, 24)`,
  `(13, 13, 40)`, `(691, 691, 36)`, `(2411, 2411, 16)`; operators three ways (closed form, its opt-out, all levers off)
  at `ell ∈ {2, 3, 5, 7, 13, 691, 2411}`; and (G0 repairs, audit m2) a **dense** τ pool read by an operator with the
  lever in effect — the host assembly factors each slot by the closed form from `HeckeTauTable::rho_pool_key`, equal
  to the dense factoriser and to the all-off operator, at `ell ∈ {3, 5, 691}`; **(I)** (G0, audit M-2) the one host
  fan-out budget (`HeckeOperatorOptions::for_each_index`): every index once, the lowest failing index rethrown,
  nested fan-outs bounded by the callers + pool − 1 helpers at 1 / 4 / 16 workers, and (G0 repairs, audit S1) **the
  budget per consumer pool**: two pools of 4 in two threads, each pool's concurrency ≤ 4 (gated), the overall peak
  reported (8 measured; ≤ 5 under G0's process-wide count). Passes at the defaults, under `HECKE_RANK1_CLOSED_FORM=0`,
  under all four opt-outs (with fewer checks: the `EFFECTIVE … default_*` arms drop out) and under
  `ENGINE_THREADS=1`; TSan-clean (`CheckThread`).

Registered only in `Registry/Slot14/WP12.cpp` (`cmake/slot14/WP12.cmake`; gated package, owner Q4 yes 2026-09-29):

- `HeckeLevelNValidation` — **`standard`**, **1665 checks, ≈ 4 s, ≈ 0.2 GB** (slot-14 WP-12; 1574 before the review repairs of 2026-09-29;
  `Hecke/HeckeLevelNValidation.cpp`): level `N` on the fixed model by Shapiro ([C] v1.14.0 `sec:levelN`,
  `Hecke/HeckeLevelN`). Arms: **(T)** `def:cosetrepsN` / `lem:cosetrepsN` (1)–(5) on every `N ≤ 60` and
  `N ∈ {77, 91, 105, 120, 180, 181, 210, 330, 1001, 1321, 2310}` — `m_N`, every `w_j ∈ SL_2(Z)` of class `j`, case (iii)
  exactly at mixed classes, the fixed points of `S`, `ST` = `ν_2`, `ν_3`, an independent `P^1(Z/N)` test by cross products
  (`N ≤ 60`), the right action and its digitwise form, `h_j` in `Γ_0(N)` (and for `det p` matrices at `p ∤ N`; at `p | N` the `U_p` admissibility of `diag(1, p)` — defined iff
  `p ∤ c_j`, `h_j` of `det p` with lower left `≡ 0 (N)`), item (6) at `N' = Np`;
  prime powers = the shipped `HeckeCosetTables` entrywise; `dim S_k(Γ_0(N))` and `c(N)` against classical values;
  **(D)** (LN1) `dim H^1 − dim H^0 = 2 dim S_{n+2} + c(N) − 2δ` and `prop:levelorbit`(3) on 22 `F_1000003` cells
  (`N ∈ {4, 5, 6, 8, 9, 10, 11, 12, 15, 21, 30, 35}`, `n ≤ 4`, one odd `n`) and five `F_ell` cells (`ell | N` and
  `ell ∤ N`); **(O)** (LN2) `M^{⟨S⟩}`, `M^{⟨ST⟩}` orbit-wise = dense as subspaces, the orbit cokernel = the model's
  `H^1`, `H^0` (fields), orbit vectors fixed over `Z/5²`; **(X)** `T_p^{(N)}`, `U_p^{(N)}` map `C^q_eq` into `C^q_eq` and
  commute with `d` (all 21 even-`n` `F_P` cells and both `Z/5²` cells); **(H)** commutativity on `H^1`, and the pinned `r_t` of `def:cosetrepsN`(6) against
  `Gamma0SubTransversal`'s give the same `H^1` matrix; **(G)** an **independent** group-cocycle route (own `P^1(Z/N)`
  table and lifts, own transversals, no τ, no model) — `h^0`, `h^1` and the characteristic polynomials of every
  operator and of a linear combination equal on 20 cells; **(K)** classical charpolys (`N = 11` `T_2`, `T_3`, `U_11`;
  `N = 5`, `n = 2` `T_2`, `U_5`; `N = 6`, `n = 2` `U_2`; `N = 35` `T_2`); **(E)** the plug-point regression at `N = ell`
  (`(2, 5)`, `(4, 7)` over `F_P`, `(2, 5)` over `F_5` and `Z/5²`): the relation list, the cochain maps and the `H^1`
  matrices of `U_ell^{(ell)}`, `T_2^{(ell)}` entrywise = slot-13 WP-6's; **(R3)** Mazur's Eisenstein ideal at weight 2,
  `F_p`, `p ∤ N`, on the 26 cells `N ≤ 211` of `docs/implementation/slot14/wp4/eisenstein_scan.tsv`: `dim H^1`,
  `dim W_{N,p}` (joint generalised eigenspace of `T_q − (1 + q)`, `q ∈ {2, 3, 5, 7}`), its Loewy length (radical
  layers) = the frozen scan, Merel's criterion recomputed, Loewy = `(dim W + 1)/2` and `dim W ≥ 5` iff Merel ((LN4)–(LN6)).
  `HECKE_LEVEL_N_R3_CELLS="N:p:dimH1:dimW:loewy:merel,…"` (read-only, not an emitter) replaces the R3 list (every cell is validated first — `N` prime, `p ≥ 5` prime, `p | N − 1`, six integer fields —
  and a bad one refused by its position, exit through `[EXCEPTION]` / `[FAIL]`): `(1321, 11)`
  26 s / 4.1 GB and `(1571, 5)` 40 s / 5.7 GB — both `dim W = 7`, Loewy length 4 (WP-12 report). Writes nothing; `LEVEL_N` / `LEVEL_N_R3` lines.
  **Since slot-15 WP-9 / WP-17** (1665 → **1871 checks, ≈ 7 s, ≈ 0.11 GB**; `Hecke/HeckeLevelNR3`): **(R3s)** the 26 frozen cells plus
  `(1321, 11)`, `(1571, 5)` on the **sparse** scan reader `ReadEisensteinR3Scan` (WP-8's presentation and Heilbronn operators, engine
  dense kernels) against the frozen values, (LN4)–(LN6), `MerelCriterionLN5` (product form `∏ k^k`, independent of the discrete-log
  `MerelCriterion`, WP-17) and, on the 26, the model route's layers; **(R3x)** (WP-17, WP-9 audit) `W` itself as a subspace, scan reader
  vs WP-7's dense presentation in the shared quotient coordinates, at `(31,5) (127,7) (181,5) (211,5) (1321,11)`, and the scan reader vs
  WP-8's `ReadEisensteinR3` at `(3001, 5)`, `(4159, 7)` (12 checks, ≈ 2.4 s). The hook `HECKE_LEVEL_N_R3_CELLS` now runs on the sparse
  route: a six-field cell gates there (the model route only under `HECKE_LEVEL_N_R3_ROUTE=model`); a bare `N:p` is a **reading**
  ((LN4)–(LN6) reported, never gated) and refuses the whole list under `ROUTE=model`; `HECKE_LEVEL_N_R3_QMAX=<q>` (default 7) widens
  `W`'s primes to every `q ≤ QMAX`; the `EFFECTIVE` line prints `route=` and `qmax=`; lines `LEVEL_N_R3_SCAN`, `LEVEL_N_R3_SCAN_SUMMARY`.
  The 1881-cell run `N ≤ 10^4` is `docs/implementation/slot15/WP-9_r3.tsv` (≤ 1.1 s, ≤ 180 MB per cell).
  **Since slot-16 WP-2** (1871 → **1883 checks**, +0.06 s): **(R3m)** the MODEL route against WP-7's dense presentation at `(11, 5)`,
  `(31, 5)`, `(61, 5)` — the two `H^1` carry different bases, so basis-free: per `q ∈ {2,3,5,7} \ {N}` the charpoly of `T_q`, the ranks of
  `T_q − (1+q)` and of its `h`-th power; `dim W`; the joint invariants (charpoly of `Σ c_q T_q`, rank and charpoly against the
  product of the `T_q − (1+q)`). Closes WP-17 §7's "(R3x) compares with the dense presentation, not the model route" (4 checks per cell;
  **since slot-17 WP-8** a fifth: one invertible `P` with `P T^model_q = T^pres_q P` entrywise for all `q`, 1883 → 1886 checks).

**The slot-14 lever switches** (none can change a value — each is a rollback / bit-identity arm, not an emitter;
none moves a fingerprint, record, job id or golden line; each environment variable sets a thread's **initial**
state, `0` turns the lever off, anything else or unset leaves it on):

| switch | lever | default | scoped opt-out | `--bench` flags |
|---|---|---|---|---|
| `HECKE_U_ELL_LOW_RANK=0` | the `U_ell` low-rank lever (slot-13 WP-4; Auto since Q8, slot-14 WP-10) | Auto: in effect iff `ell \| N` and SymN | `ScopedUEllLowRank(false)` | `--no-u-ell-low-rank`; `--u-ell-low-rank` forces On |
| `HECKE_COSET_STREAM=0` | coset streaming (slot-14 WP-10) | on | `ScopedCosetStreaming(false)` | `--no-coset-stream` / `--coset-stream` |
| `HECKE_PARALLEL_SETUP=0` | the serial phase on the pool (slot-14 WP-10), above `items · work ≥ 2^22` | on | `ScopedParallelSetup(false)` | `--no-parallel-setup` / `--parallel-setup` |
| `HECKE_RANK1_CLOSED_FORM=0` | the rank-one closed form for singular-mod-`ell` `ρ_n` (slot-14 G0): the τ pool, route 2, and (G0 repairs) the host assembly's own factoring of a dense pool | on (over `F_ell`, under the low-rank lever) | `ScopedRankOneClosedForm(false)` | — |

The one host fan-out budget (G0) has no switch of its own: it runs serially with one consumer-pool worker or under
`ENGINE_HOST_THREADS=0` (pre-existing), and since the G0 repairs it is accounted **per consumer pool** (the campaign
job loop's per-job pools each keep `threads − 1` helpers).

**Slot 15 (hecke-extensions, 2026-09-30 …; entries by WP-17).** New names (three, all `standard`; roster 159 → 162 = 59 `fast` /
88 `standard` / 15 `slow`, `Hecke*` 99 → 102), each registered only in `Registry/Slot15/WP<n>.cpp` with its `cmake/slot15/WP<n>.cmake`.
Changed names (no new registration): `HeckeRingLoewyValidation` (WP-5), `HeckeFormsHeckeAlgebraValidation` and
`HeckeBoundaryFinalityValidation` (WP-20), `HeckeLevelNValidation` (WP-9, WP-17) — see their entries above. No golden line or digest moved.
Figures below: WP-17's runs on a shared box (another build and a lattice job running), indicative, not W1 figures.

- `HeckeHidaComponentsValidation` — **`standard`**, **157 checks, ≈ 13 s, ≈ 0.12 GB** (slot-15 WP-6, `Registry/Slot15/WP6.cpp`;
  `HeckeExt/HeckeHidaComponentsValidation.cpp`, unit `HeckeExt/HeckeHidaComponents`, `hecke_ext::hidacomp`): the bignum-free
  `B_k/k mod ell^K` (direct and Kummer–Mahler routes, `ell ≥ 5`, `ell^K < 2^64`) and the readings of [U] (U1)–(U3) at tame level 1 on
  the `Z/ell^K` module route. **(A1)** both routes vs the frozen sympy oracle `HeckeExt/HeckeHidaComponentsOracle.inc` (611 values,
  incl. `5^27`, `7^22`, `691^6`, `1009^6`); **(A2)** Mahler = direct on every even `k ≤ 1200`; **(A3)** irregular indices below 160;
  **(A4)** `λ = 1`, `k*`; **(A5)** the depth law `v = 1 + v(k − k*)` on `k ≤ 6000` at 37, 59, 67, 103; **(A6)** named refusals;
  **(B)** synthetic division / square roots; **(C)** `(10, 691)` over `Z/691²` (`c_p = τ(p) mod 691²`); **(D)** `L_coh = v = L_pred = 1`
  at six irregular cells, two regular controls; **(E)** the `D = 4` blocks `(30, 67)`, `(26, 131)`; **(F)** (U3) at `(30, 67)`: `stable`,
  `ε = 0`; **(W)** native = Hida runner. Env `HECKE_HIDA_COMPONENTS_CELLS="n:ell[:K],…"` (read-only, not an emitter; `K` defaults to
  3): the readings over the listed cells, `EFFECTIVE HeckeHidaComponentsValidation arm=CELLS cells=<k>`, one `HIDA_COMPONENT` line per
  cell and `HIDA_INTRA` per `g = 2` block; `"282:37:3,226:103:3"` (the `L = 2` cells) 105 s / 0.49 GB. Open citation: Washington
  Thm 7.10 (`VERIFY-loc`, WP-6 report).
- `HeckeLevelNHeilbronnValidation` — **`standard`**, **637 checks, ≈ 2 s, ≈ 0.27 GB** (636 until slot 25; +1: arm (M) compares `MerelSet(n)` with the
  direct enumeration, in order, for every n ≤ 200, after the HZ-REC re-audit R12 rewrite of its inner loop) (slot-15 WP-7, `Registry/Slot15/WP7.cpp`;
  `Hecke/HeckeLevelNHeilbronnValidation.cpp`, unit `Hecke/HeckeLevelNHeilbronn`): Merel's Heilbronn action `H_{N,p}` on the cokernel
  presentation ([C] `lem:merelpath`, `prop:heilbronn`, `rmk:heilbronnconv`). **(M)** `|Mer_p|` at `p ≤ 13` and 101, the lattice cover,
  `Σ ε D_0 = [∞] − [0]`; **(N1)** `H_{1,p} = Σ ρ_n(adj ε)` entrywise; **(Z)** `Rel_N` preserved, the two convention traps leave it;
  **(L)** (LN3) on **both halves** — Heilbronn = τ-route of `prop:levelcorrespondence`(4)(d) — on 39 cells, 133 operators (73 `T_p`,
  60 `U_p`); **(K)** classical charpolys on the Heilbronn side; **(E)** the `N = ell` plug point against the shipped level-`ell` table.
  Writes nothing; `LEVEL_N_HEILBRONN` lines.
- `HeckeLevelNSparseValidation` — **`standard`**, **1229 checks, ≈ 7.7 s, ≈ 0.1 GB** (slot-15 WP-8, 1044 checks; +185 by WP-17's audit
  repairs; `Registry/Slot15/WP8.cpp`; `Hecke/HeckeLevelNSparseValidation.cpp`, unit `Hecke/HeckeLevelNSparse`): the sparse cokernel of
  [C] `rmk:levelcost`(4), level change and degeneracy maps. **(S)** sparse = dense on 47 cells: `D`, `dim Rel`, `h1`, the free columns,
  every RREF row entrywise, the fixed-space dimensions, every `[H_{N,q}]` entrywise for `q ∈ {2, 3, 5, 7}` and (WP-17) also 11, 13 on
  the 40 cells with `D ≤ 300`, `CokernelHeckeMatrices` dense = sparse = auto; (WP-17) `p ∈ {2, 3}` refused by name on every route,
  `kAuto` included. **(F)** `α^0`, `ω` on the presentation (15 pairs `M | N`) and the model-side cross-route at `(2,6,0)`, `(5,10,2)`,
  `(3,15,0)`: charpolys of `ω T_q α^0`, `α^0 ω`, `T_q`, and (WP-17) the ranks of `α^0`, `ω`, `T_q`, `ω T_q α^0`, `α^0 ω` and the joint
  invariants `charpoly(T_q + 2 α^0 ω)`, `charpoly(T_q α^0 ω)`. **(D)** the degeneracy maps `α_d` on the model (22 cells): `dim H^1`,
  `ω α_d = [Γ_0(dM):Γ_0(N)] [Γ_0(M) g_d Γ_0(M)]`, factor-order independence, the rank of the old space = the classical formula.
  **(R)** (R3) through `ReadEisensteinR3` on the 28 frozen cells. **(C)** the ladder and the cost model (`dim M^S`, `dim M^ST`,
  the Euler characteristic, commutation, `SPARSE_CELL` lines with the model ratios, the route choice). Env
  `HECKE_LEVEL_N_SPARSE_CELLS="N:n:p,…"` (read-only, not an emitter; `N < 2^20`, `n` even, `p ≥ 5` prime) replaces the ladder;
  `EFFECTIVE HeckeLevelNSparseValidation arm=CELLS cells=<k>`. Writes nothing; `LEVEL_N_SPARSE` / `SPARSE_CELL` lines.
  **Since slot-16 WP-13** (1744 checks, ≈ 16.5 s, ≈ 0.25 GB; unit `Hecke/HeckeLevelNDegen`, arms in
  `Hecke/HeckeLevelNDegenValidation.cpp`, [C] `sec:levelNdegsec`): **(K)** (LN7) `κ` model = presentation on 17 cells; **(A)** (LN8)
  `α_d` on the presentation, 43 cells (40 against the model, `D_N ≤ 260`) + the two traps of `rmk:degenpresconv` on 4 cells;
  **(W)** `prop:degenpres`(5), the trace, incl. `d = p | M` (20 cells; the old-space relations reported); **(L9)** (LN9) `R3_k`,
  reported, two gates on the reading; **(G)** `α_d` at scale on the sparse route (4 cells, `DEGEN_CELL` lines). Env
  `HECKE_LEVEL_N_DEGEN_CELLS="M:N:d:n:p,…"` (read-only, not an emitter; `N < 2^20`, `dM | N`, `n` even `< 200`, `p ≥ 5` prime) replaces
  (G)'s list, `EFFECTIVE HeckeLevelNSparseValidation arm=DEGEN cells=<k>`; `HECKE_LEVEL_N_R3K_CELLS="N:p:k,…"` (read-only, not an
  emitter; `N < 2^20`, `5 ≤ p < 2^21` prime, `p ∤ N`, `k` even in `[2, 200)`) replaces (L9)'s list, `EFFECTIVE … arm=R3K cells=<k>`.
  **Since the slot-16 WP-17 audit repairs** (`docs/implementation/slot16/WP-13_audit.md`, Repairs; **1798 checks, ≈ 21 s, ≈ 0.2 GB**):
  **(F1)** the `__int128` fallback of `HeilbronnOperator` forced on every term (`ScopedForceWideHeilbronn`, validation only) = the
  int64 route term for term and entry for entry on 9 composite cells (651 780 terms, 404 454 at case (iii)); (A) gates the model-cell
  count (`= #{D_N ≤ 260} ≥ 40`); the negative controls gate **both** signals; (K) checks the orientation **exactly** in the real
  complex (`d^0 = D_0 ⊗ I` spans the stored `B^1_eq`, `(dg)(e_46) = g(v_6) − g(v_4)`); both hooks parse strictly (digits only, an
  empty value, cell or field refused by position) and refuse a cell whose predicted sparse presentation exceeds 8 GiB before the run.
  **Since slot-17 WP-5** (**1867 checks, ≈ 19 s, ≈ 0.65 GB**; slot-16 finding F-1; arms in `Hecke/HeckeLevelNWideValidation.cpp`, listed in
  `cmake/slot17/WP5.cmake`, no new name): the level-`N` coset products (`MonomialOf`, `OrbitWiseFixedSpace`, `OrbitWiseFixedGenerators`,
  `LevelChangeMap`) go through `SubgroupProductForRho` — `int64` first, `__int128` on a `HeckeOverflow`, membership checked exactly
  (`CosetLevel::contains_wide`), the block keyed on the residues mod the coefficient modulus. **(W5b)** bit-identity, a gate: the forced-`__int128`
  path (`ScopedLevelNWidth`, validation only) equals the shipped path generator for generator on 8 cells up to `N = 30030` (incl. `15015:2`,
  `4620:4`, `2310:10`), `MonomialOf` / `OrbitWiseFixedSpace` on 4 small cells, `LevelChangeMap` (restriction and trace) on 3 pairs, and the
  shipped path escalates **nowhere** at `N ≤ 30030` (`auto_escalations=0`); **(W5n)** the negative control: the old width
  (`kForceNarrow`) throws `HeckeOverflow` on a synthetic product (`T^{2^33} L T^{−2^33}`) and on the generators of `Γ_0(60060)` at `n = 0`,
  where the shipped path completes (603 escalations, the orbit counts of `prop:levelorbit`(3), the supports partition the columns).
  `LEVEL_N_WIDE` lines; `SPARSE_CELL` / `DEGEN_CELL` gain `level_wide_products=`. Ladder through the existing hooks (wall / peak RSS,
  shared box): `60060:0:17` 26 s / 0.97 GB, `90090:0:17` 45 s / 1.64 GB, `100003:0:11` 10 s / 0.40 GB, **`60060:2:17` (`k = 4`,
  `D = 580 608`) 157 s / 2.57 GB**; `α_2` `30030 → 60060` and `α_3` `30030 → 90090` at `n = 0`: (LN8) held, trace `U_p` held, 1.44 / 2.11 GB.
  `99330:0:13` (`2·3·5·7·11·43`) exceeded the 8 GB watchdog (a fill-law miss, carried).
- `HeckeIsotropyModelEllValidation` — **`standard`**, **5486 checks, ≈ 5.3 s, ≈ 0.1 GB** (slot-16 WP-16, `Registry/Slot16/WP16.cpp`;
  `Integral/HeckeIsotropyModelEllValidation.cpp`, unit `Integral/Model/IsotropyModelEll`; [C] `sec:isomodelell`): the `ell`-local
  isotropy model at `ell = 3`, (IL0)–(IL4) of `rmk:isomodellcheckable`, the (NC) negative controls and (MP) `ell = 2`. **Since the
  slot-16 WP-17 audit repairs** (`docs/implementation/slot16/WP-16_audit.md`, Repairs; **5655 checks, ≈ 21 s, ≈ 0.17 GB**): the (NC)
  count pinned (22 of 25) with chain map and strictness asserted; `T'_p` a cochain map with `T' = P T' P`; 126 charpolys, 0 skipped,
  asserted; `δ = PδP` on 95 (IL2) cells; `Iso^(3) = Iso` on 28 cells `20 < n ≤ 200`; **(PHI)** the column maps
  `φ_t = |Q|^{⌊t/2⌋} π` of `prop:isomodelell`(4). Writes nothing; `ISOMODEL_ELL_*` lines.
  **Since slot-17 WP-7** (the open halves; arms only, `Integral/HeckeIsotropyModelEllOpenHalvesValidationArms.cpp`, listed in `cmake/slot17/WP7.cmake`,
  `Registry/Slot17/WP7.cpp` empty; `docs/implementation/slot17/WP-7_report.md`): **9193 checks, ≈ 25 s, ≈ 0.17 GB** (the four arms ≈ 4.3 s).
  **(IL3N)** `IL3`'s level-`N` clause: `M = Ind_{Γ_0(N)}^Γ Sym^n` built from the shipped `Gamma0LevelN` table through `MonomialOf` (a
  `CoefficientModule` of `LocalModel`; a left action, `−I ↦ (−1)^n`, `= Sym^n` at `N = 1` checked), `Iso^(3) = Iso`, the Bredon row, the closed
  form, and the shipped level-`N` pipeline (`InducedRelationsLevel` + `EquivariantCohomologyOnK`) over `F_3` at `N ∈ {1,2,3,4,5,7,11,13}`,
  `n ∈ {0,1,2,4,6}`, map-level over `Z/9` (52 cells, 40 against the pipeline; at `N = 7` the `Z/3` part is non-zero: `n = 4`
  `h1_group = 9 = 7 + 2`); **(IL4e)** `IL4` over `Z/9` (`n ≤ 12`) and `Z/27` (`n ≤ 8`): `Φ^*`, `Ψ^*`, `T'_p`, invariant factors of `H^q` and of
  `im(T'_p − a)`, `a ∈ {0, 1, −1}` (648), free charpolys (12); **(PC)** the pair / cone half of `prop:isomodelell`(5): `res` commutes with
  `Φ^*`, `Ψ^*`, `T_p`; `T'_cone` on `Cone(res)` and on the boundary, 252 charpolys over `F_3`, 180 image invariants over `Z/9`;
  **(REF)** the synthetic refined descriptor (`SubdivideEdgeOrbit` of the three edge orbits at `ζ²`, then a horocycle edge; through
  `IsotropyModel(ModelData)`): certificates, `χ_orb = −1/12`, one periodic column, cohomology only against the unrefined model (`Z/3^e`,
  boundary, odd `n`, a level-`N` module, `ell = 2`), a re-oriented edge invariant, a corrupted transport refused ((NC)). Env hook
  `HECKE_ISOMODEL_ELL_FULL=1` (any other value throws): `EFFECTIVE HeckeIsotropyModelEllValidation arm=FULL cells=248`, **11 517 checks, ≈ 56 s,
  0.22 GB** (`N ≤ 16`, `n ≤ 6`; `Z/27` level `N`; `n ≤ 20` for (IL4e), (PC)).

**Slot 16 (hecke-extensions, 2026-10-01; entries for the names not yet listed above added by WP-18a).** New names (six; roster 163 → **169 = 61 `fast` /
92 `standard` / 16 `slow`**, `--all` 153, `Hecke*` 103 → 108; derived from the source at `7f36871`): `LeanCensusFileValidation` (L16-0, `Registry/Slot16/L0.cpp`),
`HeckeTauDumpValidation` (L16-4, `L4.cpp`), `HeckeSaturationDefectValidation` (WP-5, `WP5.cpp`, entry above), `HeckeNebentypusValidation` (WP-10, `WP10.cpp`),
`HeckeIsotropyModelEllValidation` (WP-16, `WP16.cpp`, entry above), `HeckeHidaCMValidation` (WP-15, `WP15.cpp`). Arms only: WP-2 (`HeckeLevelNValidation`
(R3m), above), WP-3 (arm (T) of `HeckeFormsHeckeAlgebraValidation`, arm (I) of `HeckeBoundaryFinalityValidation`, `HeckeCensusLatticeValidation`, above),
WP-6 (`ConsoleErrorValidation` arm (HR), 562; script 029), WP-11 (arms (X4), (M2), F1 of `HeckeNebentypusValidation`), WP-13 (`HeckeLevelNSparseValidation`,
above). No golden line or digest moved. Figures: the packages' own runs on loaded boxes, indicative; W1 figures in `docs/implementation/slot-history.md`.

- `LeanCensusFileValidation` — **`fast`**, **1767 checks** (slot-16 L16-0; WP-1 taught it `gt_part_*.tex`, L16-2 `proved_mod_lit`, L16-5's repairs the
  5-column census with `lit_hyp` / `lit_hyps`): the committed Lean census `lean/census.tsv` against the [GT] sources, **never running lake** — the
  toolchain pin (`v4.33.x`), mathlib `db584cd`, no `packagesDir`, every [GT] `\lean{}` statement has a census row whose status (`proved`,
  `proved_mod_lit`, `stated`, `planned`, `lit_hyp`) is the one [GT]'s `\leanok` marks give, no stale row, no duplicate, every proved / `lit_hyp` row on the
  standard axioms only, `lit_hyps = -` outside `proved_mod_lit`. Regenerate the census (`lean/tools/lean_census.sh --emit`) in the same commit as any
  [GT] / Lean change, or this name fails.
- `HeckeTauDumpValidation` — **`fast`**, an **emitter into scratch** (slot-16 L16-4, Lean Q14): `[SKIP]` and exit 0 unless `HECKE_DUMP_TAU=<dir>` names an
  existing directory **outside** the source tree (inside it: `REFUSED`, exit 1). Writes `tau_p2.txt` (the default `HeckeTauTable` at `p = 2`,
  `certify = 0`, its FNV equal to the golden `tau_table_fnv64_p2_r1`) and `rho_n2_ell5.txt`, `rho_n10_ell691.txt`, `rho_n16_ell13.txt` (18 matrices each),
  the inputs of the Lean checkers `tauP2_spec` / `rho_golden_cells` (`lean/tools/tau_dump_to_lean.py`). `EFFECTIVE HeckeTauDumpValidation arm=DUMP cells=3`,
  one `TAU_DUMP` line per file.
- `HeckeNebentypusValidation` — **`standard`**, **2434 checks (2661 since slot-17 WP-6, below), ≈ 41 s, ≈ 0.57 GB** (slot-16 WP-10 1958, WP-11's arms, the WP-10/11 audit repairs;
  `Hecke/HeckeNebentypusValidation.cpp`, unit `Hecke/HeckeNebentypus`; [C] `sec:nebentypus`, convention [GT] `conv:nebentypus`). Arms: **(B)** (NB2)
  `χ = 1` bit for bit against the shipped level-`N` objects at 4 cells (58); **(C)** three independent routes (cokernel + `H_{N,p,χ}`, the fixed model,
  a group-cocycle route with a character) on 12 cells + 4 parity-mismatched zero cells (86); **(D)** (NB1) `prop:neborbit`(4) on 1668 cells (31);
  **(E)** (NB3) the `Γ_1(N)` decomposition on 79 cells, `d = 1, 2` (1355; the full 132-cell grid under `HECKE_NEBENTYPUS_NB3_FULL=1`: 3808 checks, 947 s,
  6.5 GB, run at every close); **(F)** `Fq` = `CanonicalField`, Conrey labels and generators (incl. `p = 40487`), the character group, Teichmüller (64);
  **(M2)** `m = 2` / `H^1_m ≅ A_W²` on `(72, 47)`, `(118, 47)`, `(156, 103)` and the F1 hidden blocks `(220, 17)`, `(246, 19)` (`Λ_m ≇ T_m²` for the full
  algebra, generation certificate `p ≤ d`) (54); **(N5)** WP-9's LMFDB table: 94 real rows, 20 / 20 non-real distinguishing cases `[psi]`, 4 controls,
  24 `psi` notes, all gated (225); **(N6)** 377 CM rows and `T(p,p) = χ(p) p^n` with the `χ̄` negative control (415); **(R)** named refusals (7);
  **(W)** `W_K(F_ell)` reduces to `F_ell` (6); **(X4)** (NB4) the sharp form at `n = 0` on 132 cells, the swapped reading holding on exactly 18 (gated),
  `n = 1, 2` reported (133). Hooks `HECKE_NEBENTYPUS_CELLS`, `_F1_RING`, `_F1_PMAX`, `_NB3_FULL` (CLAUDE.md's env table). Writes nothing; `NEB_*` lines.
  **Slot-17 WP-6 (nebentypus at scale; unit `Hecke/HeckeNebentypusSparse`, `HeilbronnChi::Power`): 2661 checks** (the 2434 above unchanged arm by arm,
  plus 227), ≈ +2.6 s. **(SP)** the sparse cokernel with a character = the dense route **entrywise** on 14 overlap cells (13 + 1 parity-zero; `d = 1, 2`,
  prime and composite `N ≤ 210`, `n ≤ 11`, `U_p` at `p \| N`): parity, `D`, `dim M^S`, `dim M^ST`, orbit counts, `h0`, `h1`, pivots, free columns,
  every RREF row, `H(Rel) ⊆ Rel` on every sparse generator, `T_p` / `U_p` (`p ≤ 7`) and `T_{2^2}` on `H^1`; `HeilbronnChi`'s `__int128` route forced =
  the int64 route term for term; `route=auto` dense iff `D ≤ 4096` (174); **(PV)** [C] `thm:nebrelations`(2) `T_{p^{ν+1}} = T_p T_{p^ν} − χ(p)p^{n+1}T_{p^{ν−1}}`
  with `T_{p^ν}` the direct double coset (Merel's `Mer_{p^ν}`), `ν ≤ 3`, and (3) `U_{p^ν} = U_p^ν`, on 6 cells; negative control: the recursion without
  `χ(p)` fails at every case with `χ(p) ≠ 1` (48); **(SL)** one cell beyond the dense cap on the sparse route, `(4099, order 3, k = 2)` over `F_7`,
  `D = 4100` (5). Hooks: `HECKE_NEBENTYPUS_CELLS` gains `:route=dense|sparse|auto` (default `auto`; a pre-run RSS model refuses above 8 GiB,
  `refused=rss_model`), `HECKE_NEBENTYPUS_NB3_ROUTE=dense|sparse|auto` runs the (NB3) grid on the chosen route.
  **Slot-18 WP-6 (nebentypus over the Galois ring; unit `Hecke/HeckeNebentypusGalois`; [C] `sec:nebentypus` code map (iv)–(vi); predictions
  `docs/implementation/slot18/WP-6_predictions.md`, committed first): 2857 checks** (the 2661 above unchanged arm by arm, plus 196), ≈ +2.3 s.
  **(GR)** cohomology over `W_K(F_q)`, `K ≤ 3`, `d(χ) ∈ {2, 3, 4}` (and two `d = 1` controls) on 8 cells: the canonical Howell form of `Rel` on the
  **dense** route (column by column, least-valuation pivot) = the **sparse** route (incremental insertion) **entrywise**, both self-checked as Howell
  forms; `K = 1` = the `F_q` RREF entrywise; `rk M^S`, `rk M^ST` = the `F_q` dimensions; `h1(F_q)` invariant factors; truncation `K → K − 1` = the
  `K − 1` run; `χ ≠ 1` ⇒ `H^1 = W_K^{h1}`, `H^0 = 0`; the Teichmüller lift = `GaloisRing`'s on `W_3(F_25)`; a synthetic saturation case (156);
  **(GT)** oracles: the `Γ_1(N)` model over `Z/ell^K` (`N = 5, 7`) has the union over all `φ(N)` characters of the `W_K(F_{ell^2})` exponents and
  `H^0` lengths (prop:nebdecomp (3)); at `d = 1` the fixed model over `Z/ell^K` with the Teichmüller table = the `W_K` cokernel route on 5 cells, incl.
  three torsion cells at `n = ell + 1` (`H^1(SL_2(Z); Sym^6 Z/125) = Z/5 ⊕ Z/125`); the non-free summands number `h0(F_ell)` (14); **(T2)** the
  model-route `T_{p^2} = [Γ_0(N) diag(1, p^2) Γ_0(N)]_χ + χ(p)p^n` (`BuildLevelCorrespondenceChi` on the level-1 `diag(1, p^2)` tables, transversal
  `Gamma0SubTransversalN` to level `N p^2`, verified) = `T_p^2 − χ(p)p^{n+1}` **entrywise** on the model's `H^1`, and its charpoly = `H_{N,p^2,χ}`
  (`Mer_{p^2}`), 6 cells / 11 `(cell, p)` pairs, negative control (24); **(A1)** a natural (unforced) `__int128` escalation: `U_3` at `N = 30030`,
  26 of 508 032 terms wide, = the forced-wide build term for term (1). Hook: `HECKE_NEBENTYPUS_CELLS` gains `:K=1|2|3` (the sparse `W_K` route
  against the `F_q` sparse route; `K = 1` entrywise), e.g. the ladder cell `30030:21451:3:19:K=1` (`D = 193 536`, 1.7 s, 0.68 GB).
- `HeckeHidaCMValidation` — **`standard`**, **1376 checks, ≈ 44 s, 42 MB** (slot-16 WP-15 1121, the WP-15 audit repairs M1, M2, m1–m6;
  `HeckeExt/HeckeHidaCMValidation.cpp`, unit `HeckeExt/HeckeHidaCM`; [U] 0.2.0 `sec:u-tameN`). **(A)** oracles: `h_K` on 22 discriminants, `χ_K` = the
  LMFDB Conrey characters, `a_p(θ_{λ_k})` = LMFDB on 42 rows, exact = mod on 4080 values, `Tr α^{k−1}` by powers in `Z[w]`; **(C0)** the characteristic-0
  CM count `2 h_K [w_K | k−1]` on 25 cells (`F_{10^9+7}` as the char-0 proxy); **(U9)** no CM at tame level 1, 2 on 403 (cell, `K`) pairs, the residually
  dihedral detections all at `d_K = −ell` (confirmed on `p ≤ 150`, shadows asserted); **(U8)** ordinarity on 146 / 146 runs (gates corrected for coinciding
  Eisenstein systems), the Eisenstein-multiplicity control on 109 runs against `ell ∤ B_{k,χ}/k`; **(U10)** CM ∩ Eisenstein on 10 cells with the excess pinned
  per cell (Loewy 2, or 4 at the two excess cells); the `h_K = 2` negative example (U-1) at `(15, χ_{−15}, 17|19)` gated `== 4` on both systems; the Sturm
  bound printed and checked on every gated reading. Hook `HECKE_HIDA_CM_CELLS`. Near its 60 s target on loaded boxes (47 s inside `--all`); if W1 reads
  > 60 s, drop `ell = 31` from the (U8) grid (lead note).

**Slot 17 (hecke-extensions, 2026-10-02 …).** The golden event R1 (WP-4, owner O2; add-only, predicate-gated):
- `GoldenRegressionValidation` — **17 756** objects, tier A **11 821** / 0, tier B **5935** / 0 (R1: **168** entries, 134 A + 34 B, at 18 NEW
  points, 0 changed, 0 removed; `docs/matrix-engine/rebaseline-2026-10-02-addonly-levelN-loewy-neb.md`): six `LEVELN N=<N> n=<n> p=1000003`
  points (`h0`, `h1`, the charpolys of `H_{N,q}`, `q ≤ 7`, and their matrices (B), `model_dim_H^1`, `kappa_rank^1`, and per `α_d` its term
  count, rank and matrix (B)), six `LOEWY_RING n=<n> ell=<ell> kmax=<K>` cells (the block count and every certified `LOEWY_RING` line as a
  text; three `torsion_free_stable` lines also hash the uncertified full-algebra fields `AK_hilbert`, `len_AK` — deterministic readings, F2 m1), six `NEB N=<N> chi=<N.m> k=<k> ell=<ell>` cells (`d`, `h0`, `h1`, the charpolys of `H_{N,p,χ}`). Reached from `ComputeAll()` only,
  so `GoldenSubset32`, the ext records and C4 (a) are untouched (all four digests unchanged); the new points cost ≈ 2.9 s of the golden run.

**Slot 17 WP-8 (small carries; refusals only, no value moves).** New name (roster 170 → **171**, `fast` 62 → **63**, `--all` 154 → **155**,
`Hecke*` 108 → 109; `Registry/Slot17/WP8.cpp`):
- `HeckeSmallCarriesValidation` — **`fast`**, **26 checks**, < 0.1 s, no env read, no output file: negative tests of (1) the strict grammar
  `HookParseCells` behind `HECKE_LEVEL_N_SPARSE_CELLS` (a good list parses; empty value, trailing / leading / inner empty cell, short cell,
  trailing `:`, non-digit and signed fields refused); (2) the rule-19 pre-run refusal `HookRefuseOverCap` (`(1571, 0)`, `(210, 4)` admitted at
  factor 6; `(1048575, 200)` refused at factor 1; the cap boundary at `0.99` / `1.01 × cap / sparse_bytes`; **rewritten by WP-17 for
  `hook_rss/v1`, 53 checks, below**); (3) the
  `HECKE_DUMP_SAT_CERT_CELLS` grammar `HeckeSatCertDumpParseCells` (the default list parses; nine malformed lists refused, a trailing comma
  by position as `cell 2`).
- `ConsoleErrorValidation` arm **(HR)** 7 → **10 rows** (562 → **570 checks**): `r08` `hecke_ring_algebra(608, 547, 2)` exit 5 at the default
  `u_ell` (the frozen model `u_ell_rss/v2` predicts 45 794 MB > 2048 MB; R17-2's finding), `r09` `set u_ell = "off"` exit 5, `r10`
  `set u_ell = "budget_mb=64"` at `(16, 7)` runs. The verb's other new refusals (exit 5, before the run): `ell^kmax ≥ 2^64` and
  `ell^{K_cls} ≥ 2^64` by an exact `u128` power (no `log2` margin). Script 029's transcript is unchanged.
- `HeckeLevelNValidation` (R3m) gains the entrywise intertwiner check (1883 → 1886, above).
- `HECKE_LEVEL_N_SPARSE_CELLS` (env table below) now parses strictly and refuses a cell **before the run** when `6 ×` the cost model's
  `sparse_bytes` exceeds 8 GiB. The factor is a coarse ceiling, **not** a calibrated RSS model: measured peak RSS / `sparse_bytes` is
  ≈ 10× at `n = 0` (`30030`, `60060`, `90090`, `100003`) and ≈ 1.8× at `60060:2`. `99330:0:13`, which went past 8 GB (W5-F1), is
  **admitted** (0.96 GiB predicted after the factor), so keep the VmHWM watchdog on every hook run. `90090:2:17` and `99330:2:7` are refused,
  and there is no override (WP-8 audit).
- `HECKE_DUMP_SAT_CERT_CELLS` additionally refuses a trailing `,` or `:` by position and a set-but-empty value (`REFUSED`, exit 1; unset
  keeps the default list).

**Slot 17 WP-17 (audit repairs; value-free, no golden line or digest moves).**
- The level-`N` hooks' pre-run refusal is now the calibrated **`hook_rss/v1`** (WP-8 audit MAJOR-1, MINOR-2, MINOR-3;
  `Hecke/HeckeLevelNDegenValidation.h`). It replaces the SPARSE hook's flat `6 ×` and the DEGEN / R3K hooks' `1 ×`. The predicted peak RSS is
  `512 MiB + factor × CokernelCostModel.sparse_bytes`; a DEGEN cell sums its `M` and `N` presentations. The factor is:
  - **64** when `N` has ≥ 2 distinct prime factors and one of them is `> 13` (the W5-F1 regime: `99330`, measured > 50×);
  - **16** at `d = n + 1 = 1` (measured 10.0–10.6 SPARSE, 11–16 DEGEN);
  - **4** (SPARSE, measured 1.9 at `60060:2`) or **6** (DEGEN / R3K) at `d ≥ 3`.

  Every WP-5 rung is predicted above its measured peak and admitted. `99330:0:13` (10 991 MiB) and `90090:2:17` (9622 MiB) are refused at
  the default cap. **`HECKE_LEVEL_N_HOOK_RSS_CAP_GIB=<G>`** (whole GiB in `[1, 1024]`; a malformed value throws) moves the 8 GiB cap for a
  deliberate exclusive-window run. It applies to all three hooks, and each `EFFECTIVE` line now ends with
  `rss_cap_gib=<G> rss_cap_source=default|HECKE_LEVEL_N_HOOK_RSS_CAP_GIB rss_model=hook_rss/v1`. Every admitted cell prints a
  `HOOK_RSS <hook> cell=<i> … factor=<f> predicted_mib=<x> cap_gib=<G>` line. It is a ceiling, not a model: keep the VmHWM watchdog.
- `HeckeSmallCarriesValidation` (2) is rewritten for it: 26 → **53 checks**. It covers the factor per regime, the six WP-5 rungs and three
  DEGEN scale cells predicted above their measured peaks, the refusals of `99330:0` / `90090:2` / `(1048575, 200)`, the override (it admits
  `90090:2` at 12 GiB; at 1 GiB it refuses `30030:0`; eight malformed values are refused), the `EFFECTIVE` texts, and the cap boundary.
- `HeckeNebentypusValidation` (X4): `n12_held == 240` is now gated (F1 m-C2), +1 check.
- `HeckeIsotropyModelEllValidation` (open halves): the (REF) label now reads "descriptor round-trip" (WP-7 audit MINOR-1). `SubdivideEdgeOrbit`
  `ENGINE_CHECK`s that the edge's and each split triangle's stabiliser is the centre `{±I}` (MINOR-2). There are two new checks: every shipped
  edge representative has stabiliser `{±I}`, and (NC) a planted non-central edge stabiliser (`S`, order 4) is refused.

**Slot 17 close (WP-18, W1 2026-10-02, head `410d4e4`).** Roster **171 = 63 / 92 / 16** (`--all` 155, 109 `Hecke*`). `HeckeSatCertDumpValidation`
(L17-2, **`fast`**; an env-interlocked scratch emitter, `HECKE_DUMP_SAT_CERT`, `[SKIP]` unset — see the env table) and `HeckeSmallCarriesValidation`
(WP-8, **`fast`**, 53 checks after WP-17) are the two new names. W1's walls (a **loaded** box, `foreign_heavy_rows=1309` of 1924): golden 30.0 s,
EngineDet 4.9 s, ExtDet 9.3 s, ConsoleDet 44.0 s (T_C4_INFO 41.8 s; threshold 45 s), smoke 0.1 s, `--all` 1011.6 s, `--all-full` 1556.5 s; the NB3_FULL
close step 965.0 s, 0.8 GB, 4036 checks; `LeanCensusFileValidation` 3056 checks. Quiet-box re-times (ConsoleDet, `HeckeRingLoewyValidation`,
`HeckeNebentypusValidation`): carried to slot 18's W1 (owner, 2026-10-02).
- `HeckeSatCertDumpValidation` — **`fast`**, an **emitter into scratch** (slot-17 L17-2; `HeckeExt/HeckeSatCertDumpValidation.cpp`, `Registry/Slot17/L2.cpp`):
  `[SKIP]` unless `HECKE_DUMP_SAT_CERT=<dir>` (outside the source tree, else `REFUSED`, exit 1); then one `satcert_n<n>_ell<ell>_b<k>.txt` per torsion-free
  certified `stable` block of the cells `HECKE_DUMP_SAT_CERT_CELLS` (default `168:13:2,220:17:2,258:37:2`: 19 files, ≈ 14 min, 0.43 GB) for
  `lean/tools/satcert_to_lean.py` → `GL2/Algorithms/SatCertData.lean`; prints `EFFECTIVE HeckeSatCertDumpValidation arm=DUMP cells=<k>` and one
  `SAT_CERT_DUMP` line per file. The 19 dumps' sha256 sums: `docs/implementation/slot17/L17-2_satcert_dump_ledger.md`.

**Slot 18 (hecke-extensions, 2026-10-03 …).** The golden event R1 (WP-4, owner O2 of 2026-10-03; add-only, predicate-gated):
- `GoldenRegressionValidation` — **18 058** objects, tier A **11 827** / 0, tier B **6231** / 0 (slot-18 R1: **302** entries, 6 A + 296 B, 0 changed,
  0 removed; `docs/matrix-engine/rebaseline-2026-10-03-addonly-tau-neb2.md`): at the 31 NEW points `n=<n> ell=<ell> ext tau` (the ext-subgrid cells
  whose `ext cone_action` point carries the `p = 2` tables) the tier-B hashes `tau_table_fnv64_p<p>_r<ν>` / `tau_bd_table_fnv64_p<p>_r<ν>` for
  `(p, ν) ∈ {(3,1), (5,1), (7,1), (2,2), (3,2)}`, `p ≠ ℓ` (the recipe of `HeckeConeAction::golden_objects()` at `p = 2`; one value per `(p, ν)` at
  all cells), and the `d = 2` point `NEB N=7 chi=7.2 k=4 ell=5` over `F_25` (`d`, `h0`, `h1`, the charpolys of `T_2`, `T_3`, `U_7`). Reached from
  `ComputeAll()` only, so `GoldenSubset32`, the ext records and C4 (a) are untouched (all four digests unchanged); the new points cost ≈ 0.13 s of
  the golden run (the same under `ENGINE_BACKEND=legacy`).

**Slot 18, WP-M (the CLI / console user manual; owner ruling 2026-10-03).** Roster **172 = 64 / 92 / 16** (`--all` 156) with the one new name:
- `CliManualCoverageValidation` — **`fast`** (≈ 0.03 s; `Console/CliManualCoverageValidation.cpp`, `Registry/Slot18/WPM.cpp`, `cmake/slot18/WPM.cmake`).
  Gates `docs/latex/cli_manual.tex` [CLI] against the binary: (1) the 19 generated include files `docs/latex/cli_manual/*.tex` (counts, six usage
  texts, eight command-line token tables, verbs, types, settings, the validation roster) equal what the binary generates; (2) every registered
  verb / type / setting / validation and every token-table entry appears in them; (3) `cli_manual.tex` `\input`s each; (4) the token table equals,
  per context, the set of string literals the parsers compare against (`arg1 ==` in `kernel.cu`; `a ==` / `mode ==` / `op ==` in
  `Bench/BenchDriver.cpp`; `s ==` in the `--backend` parser; `a ==` in `Campaign/CampaignDriver.cpp` and `Console/Core/ConsoleCli.cpp`; `key ==` in
  `Campaign/CampaignSpec.cpp`; `a[i] ==` in `HeckeExt/HeckeAtlasCli.cpp`) — a new flag without a manual row fails, and so does a row no parser reads;
  (5) the top-level usage literal equals `Console/scripts/cli_frozen/help.stdout`; (6) every line of every `\excerptfrom{<script>}` block occurs in
  that script and every `\octranscript{<name>}` names an existing `.expected`. **Since slot-24 DOCS-CLI (F7):** (7) every registered verb is
  called in a numbered script the manual names (an excerpt, a transcript or a `\file{NNN_*.oc}` mention), or is an `example` row of
  `docs/latex/cli_manual_gate.tsv` with a reason (4 rows: `exit`, `save_state`, `help_markdown`, `campaign_spec`; a row for a verb that has an
  example, or is not registered, is STALE and fails); (8) every complete string literal `"ENGINE_*"`, `"HECKE_DESCENT_*"`, `"L23_*"` in
  `ModArithmetic/` and `src/hacs/` sources, and every `lever` row of that file (the 21 `HECKE_*` rollback levers), appears as
  `\env{NAME}` between `\label{sec:env}` and the next `\chapter` of the manual (`env-exempt` rows with a reason excepted; a `lever` row no
  source names is STALE); (9) every `\runoutput{<name>}` has `docs/latex/cli_manual_runs/<name>.txt` (written by
  `docs/latex/tools/gen_cli_manual_runs.sh <binary> [--check]`). Prints (slot 24, 1.5.0) `CLI_MANUAL_COVERAGE files=22 verbs=163 types=31
  settings=41 validations=263 tokens=125 excerpts=16 transcripts=16 examples=159 example_exempt=4 env=115 env_exempt=0 runs=10 failing=0`
  (slot 18: `files=19 verbs=154 types=30 settings=41 validations=172 tokens=107 excerpts=12 transcripts=9 failing=0`). `[SKIP]` without a checkout. **Emitter into scratch** under
  `CLI_MANUAL_EMIT=<dir>` (outside the tree, else `REFUSED`): `EFFECTIVE CliManualCoverageValidation arm=EMIT files=19`;
  `docs/latex/tools/gen_cli_manual_tables.sh <binary> [--check]` drives it. **Coupling:** a package that registers a validation, a console
  verb / type / setting or a CLI token must regenerate the tables in the same commit.

**Slot 18, WP-19a (GPU G1, the elimination session; `ENGINE_API.md` §12.8).** Roster **174 = 64 / 94 / 16** (`--all` 158, with
WP-19b's `HeckeLadicSplitValidation`):
- `EngineElimSessionValidation` — **`standard`** (≈ 9 s, 4889 checks with `OC_ENABLE_LEGACY=ON`, **4086** in the default OFF build since S24 CL-R2 (the rollback arm `session-off` ×4 and the rollback side of the volume case, `volume-rollback`, are legacy arms: `SKIP-ARM` lines; first line `EFFECTIVE ENGINE_ELIM_SESSION route=new source=retired|default`); `src/Engine/EngineElimSessionValidation.cpp`,
  `Registry/Slot18/WP19a.cpp`, `cmake/slot18/WP19a.cmake`). (A) `tape::rref` (no rank hint: `R` grows, release / re-adopt), `kernel_basis`,
  `factor_basis` (chunks 256 / 7, pivots / basis / projector) and `solve_multi_rhs` entrywise against `engine::blk` on 2x11 / 13x7 `d = 17`,
  non-uniform, single-block (+ 2x11 `d = 65`, 6x7 `d = 129` at `134217757`) grids x the four shapes, under six arms: gpu session with
  the `ENGINE_VERIFY_DEVICE` re-execution, gpu session, gpu session `threads=1 batch=0 graph=2`, gpu `ENGINE_ELIM_SESSION=0` (rollback),
  hybrid session verify, hybrid session `threads=4`; u32 `134217757`, `7`, `2^32-5`, u64 `2^61-1`; per arm the non-vacuity counters (sessions
  opened; under gpu mirrors made, planned H2D skipped, epilogue D2H deferred; none under the rollback) and `device_bytes() == 0` after
  `release_device_state()`. (B) the device row-list `GATHER` (`cuda::gather`'s row-list form; repeats, column lists, identity source,
  accumulate, both layouts) against the CPU executor, verify on and off, u32 / u64. (C) the cpu policy opens no session; the session arm moves
  fewer bytes and fewer H2D copies than the rollback on `rref 1677x1419` (56 MB / 32 vs 161 MB / 76); `pageable_copies == 0`. `[SKIP]` without
  a usable device. Read-only, no env.

**Slot 18, WP-5 (level `N` at scale II; [C] `rmk:levelNscale`(4), the `sec:levelN` code map's items (a)–(e)).** No new name (roster unchanged):
- `HeckeLevelNSparseValidation` — **1970 checks** (1867 + 103), ≈ 27 s, ≈ 0.7 GB; new arms in `Hecke/HeckeLevelNOrderValidation.cpp`
  (`cmake/slot18/WP5.cmake`). **(W18o)** the generator order is value-free, a gate: `SparseCokernel` built from the same generators under
  `GeneratorOrder::kAsBuilt` (slots 15–17: every `S` generator, then every `ST` one) and `kLastColumnDescending` (shipped since slot 18:
  sorted by the largest column, descending) has the same pivots, free columns, RREF rows entry for entry, ranks, `h0`, `final_nnz` and
  `PresentationDigest` on 12 cells (`1571:0:5` … `9030:0:13`, incl. `1290:0`, `2838:0`, `9030:0`: `P(N) = 43`, the W5-F1 shape, where it
  also gates `occ_sorted ≤ occ_as_built`), and `CokernelHeckeMatrices` (sparse route) is bit-identical under both on 4 cells;
  `LEVEL_N_ORDER (W18o)` lines report `merge_ops_*` / `occ_*` / `peak_nnz_*` per order (e.g. `9030:0:13`: merge ops 4.8·10^8 → 2.7·10^6).
  **(W18g)** `Gamma1LevelN::contains_wide` agrees with `contains` on int64 probes (members and non-members), a product beyond int64 in
  `Γ_1(13)` escalates through `SubgroupProductForRho` with independently checked residues, the old width and the `CosetLevel` default refuse
  it (negative controls), and `MonomialOf` on five `Γ_1(N)` cells is equal at both widths. `SPARSE_CELL` gains `gen_order=`, `occ_entries=`,
  `presentation_fnv=`; the hook's `EFFECTIVE` line gains `gen_order=`. Gate run on every logged slot-16 / slot-17 rung (21 levels, both orders,
  `presentation_fnv` and `final_nnz` equal: `docs/implementation/slot18/WP-5_report.md`). `hook_rss/v1` unchanged (the structure-aware law
  failed the × 1.5 rule; finding). `HeilbronnChi`'s wide route now forms its product by `Gamma0LevelN::cocycle_wide` (gated by
  `HeckeNebentypusValidation`'s forced-wide arm, unchanged); `hecke_ring_loewy` runs the torsion pre-pass once (`LoewyOptions::prepass`).
- **S24 CL-G2 (2026-10-30; owner ruling 2):** `HECKE_LEVEL_N_GEN_ORDER=as_built` retired to `Hecke/legacy/`. (W18o) is now
  **(W18o-pin)**, every build: on the same 12 cells `PresentationDigest` of the sorted order equals the value printed by the slot-24
  binary before the retirement (12 checks, `LEVEL_N_ORDER (W18o-pin) … pinned=1`), and **(W18o-as_built)**, `OC_ENABLE_LEGACY=ON` only
  (`Hecke/legacy/HeckeLevelNOrderLegacyArms.cpp`, the slot-18 twin unchanged, 43 checks); an OFF build prints
  `SKIP-ARM HeckeLevelNOrderValidation arm=as_built: OC_ENABLE_LEGACY=OFF`. **`HeckeLevelNSparseValidation`: 1939 checks (OFF), 1982
  (ON)** (was 1970 = 1939 − 12 + 43). Same package: `SparseCokernel` / `NebSparseCokernel` share one sparse kernel (`Hecke/SparseRref.h`,
  B1) and `level::Rref`, `tame::Rref` (hence `NullSpace` / `SolveSquare`) and `ordinary::FieldNullspace` run on `engine::elim::rref`
  (`Hecke/DenseRref.h`, B3 (b)); no check count of `HeckeNebentypus`, `HeckeTameFamily`, `HeckeOrdinaryPrecision`, `HeckeLevelInfRes`,
  `HeckeHidaLevelEll`, `HeckeLevelNHeilbronn` changed.


**Slot 18 close (WP-18, W1 2026-10-03, head `c044f64`).** Roster **174 = 64 / 94 / 16** (`--all` 158, 111 `Hecke*` by `--list | grep -c ^Hecke`).
New in slot 18: `CliManualCoverageValidation` (WP-M, **`fast`**), `HeckeLadicSplitValidation` (WP-19b, **`standard`**), `EngineElimSessionValidation`
(WP-19a, **`standard`**). W1's walls (**loaded box (3 LAT37 cells)**, our own declared load plus another session's `rqaudit`; not a verdict): golden 28.5 s
(A 11827 / 0, B 6231 / 0), EngineDet 5.2 s, ExtDet 9.3 s, ConsoleDet 44.9 s (T_C4_INFO 42.6 s; threshold 45 s), smoke 0.1 s, `--all` 995.5 s,
`--all-full` 1562.2 s; the NB3_FULL close step 961.1 s, 0.3 GB, 4231 checks (4036 at the slot-17 close: WP-6's arms); `LeanCensusFileValidation` 5742
checks. Quiet re-times: slot 19's WP-RC "Q" (`docs/implementation/slot18/WP-18_close_report.md` §1.3).
- `HeckeLadicSplitValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`** (≈ 8 s, 56 checks; `Hecke/HeckeLadicSplitValidation.cpp`, `Registry/Slot18/WP19b.cpp`,
  `cmake/slot18/WP19b.cmake`; slot-18 WP-19b): the `p ≠ ℓ` digit split of `Hecke/LadicCell` (`hecke::ladic_cell::DigitCellSession`: steps 1–2 once per
  cell, the Hecke step per prime). Shared-cell records equal fresh `RunCell` records bit for bit (canonical text, objects and the omitted fields) over
  prime orders, widths 32 / 64 / 128, the pre-pass, `module_K` / `keep_hecke` and the refusals; a console transcript of nine digit `hecke()` calls is
  identical to the slot-18 shared binary's. No env hook; no golden line.

**Slot 20 close (WP-18, W1 2026-10-05, the release commit `568cc357`; quiet box, `foreign_heavy_rows=0`).** Roster **182 = 66 / 99 / 17** (`--all` 165).
New in slot 20: `HeckeLValueMeasureValidation` (WP-MEAS + S1 / S2, **`standard`**), `ConsoleServeAtlasValidation` (NB-4, **`standard`**; `[SKIP] …:
OC_BUILD_NOTEBOOK=OFF` in a default build). W1's walls (quiet; the figures of record): golden 26.1 s (A 11827 / 0, B 6231 / 0), EngineDet 4.5 s, ExtDet 8.4 s,
ConsoleDet 41.1 s (T_C4_INFO 39.5 s; threshold 45 s), smoke 0.1 s, `--all` 946.6 s, `--all-full` 1563.8 s; `HeckeRingLoewyValidation` 63.0 s (owner target 64 s, met);
`HeckeLValueValidation` 28.6 s, 1471 checks; the NB3_FULL close step 836.6 s, 1.07 GB, 4231 checks; `LeanCensusFileValidation` 9100 checks. Notebook build (close
report §4.2): `ConsoleServeAtlasValidation` 429 checks, `ConsoleServeValidation` 492, `ConsoleReadOnlyTagValidation` 990, all 0 failing.
- `ConsoleServeAtlasValidation` — **`standard`**, ≈ 2.9 s, **429 checks** (435 with the real store), peak ≈ 0.16 GB (0.47 GB with the real store's open)
  (`Console/ConsoleServeAtlasValidation.{h,cpp}`, `Registry/Slot20/NB4.cpp`, `cmake/slot20/NB4.cmake`; slot-20 NB-4; [P] v3.11 §18.16): the atlas sidecar
  `oc-atlas-index/1` (`--atlas --index`) and the read-only server `--serve-atlas` (`oc-serve-atlas/1`), arms A–H on `Σ(23)` + `Σ(13)` built in process, every query
  checked against an in-process reader; with `HECKE_ATLAS_IN=<ell691 dir>` also the real `Σ(691)` store and its sidecar (`real=sidecar`). Prints `EFFECTIVE
  ConsoleServeAtlasValidation arm=ALL cells=19 systems=290 queries=… real=absent|sidecar git=…`. Only with `-DOC_BUILD_NOTEBOOK=ON`; otherwise
  `[SKIP] ConsoleServeAtlasValidation: OC_BUILD_NOTEBOOK=OFF` (`BuildSwitchSkip`). Report `docs/implementation/slot20/NB-4_report.md`.

**Slot 19 close (WP-18, W1 2026-10-04, head `e296a84b` + the release commit `02f417fd`).** Roster **180 = 66 / 97 / 17** (`--all` 163, 114 `Hecke*` by
`--list | grep -c ^Hecke`). New in slot 19: `NumberFieldValidation` (WP-NF / WP-NF2, **`fast`**), `ConsoleReadOnlyTagValidation` (NB-2, **`fast`**),
`HeckeLValueValidation` (WP-LV, WP-LV2, WP-LIN, WP-BIL, **`standard`**), `ConsoleServeValidation` (NB-2, **`standard`**), `HeckeLambdaValidation` (WP-HL,
**`standard`**), `HeckeLatticeModuleValidation` (WP-LC, registered `standard`, **`slow`** by the owner's ruling of 2026-10-03). The two NB-2 names print
`[SKIP] …: OC_BUILD_NOTEBOOK=OFF` in a default build (the close binary); they run in a notebook build (close report §4). W1's walls (**loaded box**: our own
`(1184, 37)`, E2 and 691 level-3 runs, declared, plus another session's `rqaudit`; not a verdict): golden 27.3 s (A 11827 / 0, B 6231 / 0), EngineDet 4.7 s,
ExtDet 8.8 s, ConsoleDet 43.2 s (T_C4_INFO 41.8 s; threshold 45 s), smoke 0.1 s, `--all` 991.9 s, `--all-full` 1680.3 s; the NB3_FULL close step 1013.1 s,
0.45 GB, 4231 checks; `LeanCensusFileValidation` 7933 checks (5742 at the slot-18 close). Quiet re-times: slot 20's WP-RC20 "Q"
(`docs/implementation/slot19/WP-18_close_report.md` §1.3). The entries below were written by the packages during the slot.
- `HeckeLValueValidation` — **`standard`** (≈ 5.4 s, 311 checks at slot-19 WP-LV; **≈ 28.6 s, 1471 checks** at the slot-20 close (W1, quiet box), after WP-LV2, WP-LIN, WP-BIL and slot-20 WP-LV3; `HeckeExt/LValue/`, `Registry/Slot19/WPLV.cpp`, `cmake/slot19/WPLV.cmake`;
  slot-19 WP-LV; [E] `sec:lvalue`): the `LValueRoute` interface (`def:lvroute`, kinds linear / bilinear / congruence) and its Eisenstein /
  Bernoulli instance (kind congruence) on `rmk:lvgates`'s untwisted cells `(n, ℓ) = (30, 37), (10, 691), (42, 59), (56, 67)` (`v(B_k/k) = 1`) and the
  regular controls `(10, 37), (22, 37)` (`v = 0`), `m = 1, 2, 3`: the `m_Eis`-block of `H^-` (iota^* on `H^1(Z/ℓ^4)`, the joint idempotent), its
  saturation verdict (`dim A_1 = f`), `Q_m = A_m/(T_p − e_p)` cyclic of length `min(m, v)` (`cl:lveis(3)`), the inequality over `p ≠ ℓ`, and the
  module form `(2)` read as the lattice index on the plus block. Bernoulli numbers in-house: exact (tangent numbers, five printed `B_k`) against
  Voronoi mod `ℓ^m` and the slot-15 Kummer–Mahler route, and the depth-2 rungs (284 @ 37, 228 @ 103, 342252 / 342440 @ 691). Negative controls: the plus side (length `m`), a
  wrong-weight character (`Q = 0`), a planted non-saturated `Z[ℓe]`, the Birch / Hida stubs (`NotImplementedInThisBuild`), the kind refusals, the
  character model refused. Prints `LVALUE` / `LVALUE_CELL` / `LVALUE_MODULE_FORM` lines. No env hook; no golden line.
  **Slot-19 WP-LV2 extension (≈ 14 s, 537 checks default, 0.17 GB; env arm `HECKE_LVALUE_HEAVY=1`: 657 checks, 419 s, 0.98 GB).** (BT) twisted
  Bernoulli `B_{k,ω^j}/k mod ℓ^m` by the definition (exact `B_i`, Teichmüller `ω`) against Kummer's congruence (Voronoi `B_{k'}/k'`) and the
  Kummer–Mahler route, `v` at 7 cells (incl. the twisted depth-2 rung `k = 62`, `ω^6` at 37: `v = 2`); (ET) [E] `cl:lvtwist` on the character model
  `H^1(Γ_0(37); V_{Z/37^4}(ω^j))` (slot-18 WP-6's model route; `ι^*` on `Ind` new): `(k, j) = (4, 28), (6, 26)` (`v = 1`, `f^- = 1`, `#Q_m = 37`),
  controls `(4, 8)` and the torsion cell `(4, 34)` (`v = 0`, `Q = 0`), `rank H^+ = rank H^- + 2`, (N6) the conjugate and (N7) the untwisted
  character give `Q = 0`; (EF) the free part `(H/tors)/ℓ^K` at `K_run = K + t` on the torsion cells `(8, 7), (24, 23), (38, 37)` (refused without the
  opt-in; `tr T_p^i` independent of `K_run`); (N8) `c_sat` and the two-sided bound of `cl:lveis(3)` on planted `Z[ℓe]`, `Z[ℓ + ℓ²e]`; (N5) the
  character model accepted at level `ℓ`, the MP and Shapiro models refused. Prints `BERNOULLI_TWIST` / `LVALUE_TWIST_CELL` / `LVALUE_FREE_PART` /
  `LVALUE_RUNG_CELL` lines.
  **Slot-19 WP-BIL extension: the `bilinear` kind (≈ 25 s, 1115 checks default, 0.18 GB; the bilinear arms ≈ 5 s, ≈ 577 checks; env arm
  `HECKE_LVALUE_BILINEAR_HEAVY=1`: +5 checks, +13 s, 0.86 GB).** `HidaPairingRoute` (Hida's GL2 × GL2 pairing, [E] `rmk:lvshapes` (H); core
  `HeckeExt/LValue/HidaPairing.{h,cpp}`, route `HidaPairingRoute.cpp`, arms `HidaPairingValidationArms.cpp`; spec R19-9 §6, oracle `r199/out/*.out`,
  predictions `docs/implementation/slot19/wpbil/predictions.md`). (G1) on the C++ `PoincareDualityPairing` at R19-9's 9 cells `(10,691) (10,5) (10,7)
  (12,5) (22,144169) (24,7) (36,37) (40,37) (72,37)`: `gram(1) == −⟨Ψ(c,c_∂), y(v4v6)⟩` on the stored bases, the route's `evaluate_pairing`
  reproduces it, the route's `ρ`, `ρ^∨` == `ComputeSymmetricPowerMatrixFM` / `ComputeContragredientPowerMatrixFM` on `S, T, U`, perfect over `F_p`;
  (G2) `A_D(T_p) = A_c(T_p)^T` for `p = 2, 3, 5` (`T_5` new), `T_2T_5 = T_5T_2`, `ι` anti-isometric at the 27 cells `k = 12 … 28` and at `(258, 37)`
  mod `37^10`; (G3) `G_! = −B_{R19-8}/6`, radical `Z p_0`, unimodular on `W/p_0` (`n + 1 < ℓ`); (G4) R19-9's frozen valuations (mixed even / mixed
  odd / Hida `H^1_!`: 8 Eisenstein cells 1/0/0, `144169`, `131`, `139` ramified 1/1/1, split `[0,1]/[0,0]/[0,0]`, controls 0) and `(258, 37)`
  (`H^1(D)` free of rank 43, `m`-blocks of rank 4 with charpoly R19-1's `P`, types free / `m`, unimodular Grams, mixed `v_π = 3 / 2`, P9 index 37 and
  `3 / 3`, `Σ_f v_37 = 6`); (G5) every value == the congruence module of its lattice read from `A_c(T_2)` alone, the Eisenstein values ==
  `v(B_k/k)` (`Bernoulli.h`), the route's `IndexStatement` (H1)/(H2)/(H3); (NB) a perturbed cocycle refused, `D^S + D^U` invisible while `u_0^∨` is
  not, the wrong lattice gives the other module (Eisenstein `H^1_!` 0 vs 1; `(258,37)` `m`-sign 2 vs 3), a planted non-adjoint caught, the route's
  refusals. Prints `HIDA_PAIR_CELL` / `HIDA_PAIR_258*` / `HIDA_PAIR_MODEL` / `NORMALISATION (H)` lines.
  **Slot-19 WP-LIN extension (the linear instance; default ≈ 30 s on a loaded box (the (BS) arms ≈ 17 s), 795 checks, 0.59 GB; `HECKE_LVALUE_HEAVY=1`:
  936 checks, 505 s, 1.2 GB).** `BirchModularSymbolRoute` ([E] `rmk:lvshapes` (B); `HeckeExt/LValue/BirchModularSymbol.{h,cpp}`, arms in
  `HeckeLValueBirchArms.cpp`; spec R19-8 §6, predictions `docs/implementation/slot19/wplin/predictions.md`): `Φ({0,∞}) = (ρ(S)−1)(c(v0v4)+c(v4v6)−c_∂(v0))`
  on the C++ cone's `H^1_c` (field `EquivariantMappingCone` at `F_ℓ`, `ModuleConeT<uint64_t>` at `Z/ℓ^m`), Birch's `ev_{χ,j}`. (BS-G5) `ρ_n` by L·D·U ==
  the `O(n³)` def:rhon construction, multiplicativity; (BS-G1) `Ψ : H^1_c(R) ≅ W(R)` (lengths, invariant factors; incl. the torsion summand at
  `(72,37)` over `Z/37^3`), coboundaries killed, at `(10,691)`, `(10,5)`, `(10,7)`, `(22,144169)`, `(36,37)`, `(40,37)`, `(72,37)` × `{F_ℓ, Z/ℓ^3}` and
  `(258,37)` over `F_37`; negative: the wrong boundary sign leaves `W` (every `Z/ℓ^3` cell); (BS-G2) Manin relations, `Γ`-equivariance, additivity
  (20 seeded trials per cell), `T_p W ⊂ W`; (BS-G3) `Ψ∘T^c_p = T_p^{sym}∘Ψ` (`ModuleConeActionT`, `p = 2,3`, `Z/ℓ^2`) with the `ρ(α)`-for-`ρ(adj α)`
  negative, and `Ψ∘ι^*_{[C]} = −ρ(ι)∘Ψ` read through `π` (negative: `+ι^*`); (BS-Q5) the sign rule for 9 quadratic and 3 non-real characters,
  `ev_χ ≠ ev_{χ̄}`; (BS-G4) R19-8's frozen numbers (`BirchFrozenR198.inc`, generated by `wplin/frozen_r198.py`): `r^±` = the `a_2`-eigenlines of the cone
  action at `ℓ = 1000003`, the 9-twist tables at `k = 12…26` (108 rows), leg (c) at the 8 Eisenstein cells over `Z/ℓ^3` (the route's
  `index_statement()` (L1) depth = `v(B_k/k) = 1`, `r^− ≡ s·Bern_k` to depth 1, `Bern_k ∈ W(F_ℓ) \ W(Z/ℓ²)`, (L2) twisted values on `r^+` ≡ 0),
  controls `(10,37)`, `(22,37)` depth 0; (BS-Q8) `(258,37)`: charpoly factorisation, block rank 4 per sign, ranks of `t,t²,t³` `(3,2,1)` on
  geometric-even = [C]-minus (free) and `(2,1,0)` on [C]-plus, `π` rank 3 per sign (isign (K)), the unit-`j` sets (free sign: 14 `j`; `m`-sign on the
  line `ker t ∩ im t²`: non-units `j ≡ 1,3,5 mod 36`, 24 of 129); (BS-API) the declared constructor, refusals (MP model by name, `H^1`, `ℓ | M`,
  conductor 8), the record's two signs. Heavy adds `(258,37)` over `Z/37^2` (G1, the `ι` reading, Q8) and G3 at `(72,37)`. Prints `BIRCH_G1`,
  `BIRCH_G3`, `BIRCH_FROZEN`, `BIRCH_LEGC`, `BIRCH_258`, `BIRCH_258_MSIGN`, `LVALUE BirchModularSymbol …`, `BIRCH_ARMS`; `EFFECTIVE HeckeLValueValidation
  arm=HEAVY_BIRCH cells=1` under the hook.
  **Slot-20 WP-LV3 extension (L-value code at depth 2; default 1471 checks, 30.7 s paired with the slot-19 binary's 29.4 s on the same box
  (1373 checks), the LV3 arms ≈ 4–7 s (the route's cell memo saves the rest), 0.58 GB; `HECKE_LVALUE_HEAVY=1`: 1614 checks, 729 s, 1.55 GB).** Arms in
  `HeckeExt/LValue/HeckeLValueLV3Arms.cpp` on the generic m-block reader `HeckeExt/LValue/MBlockReader.{h,cpp}` (Newton polygon by
  `nf::newton_polygon`, roots refined digit by digit in tame totally ramified local orders `Z_ℓ[π]/(π^e − ℓu)`; refuses f > 1, e ∤ ℓ − 1,
  multiple roots by name), which `HidaPairingRoute` now reads (WP-BIL's `ReadCell258` kept as the cross-check arm). (LV3-L) [E] `def:lvlattice` (`θ = Φ_n`):
  the whole-lattice lengths of `Φ_{n,*}` / of `Θ = (Φ_n/n!)^{−1}` at `(10,5) (10,7) (12,5) (24,7) (40,37) (72,37) (30,37)` (gated: injective,
  ≥ 0, 0 for `n < ℓ`) and the negative control `d_f = 1` on generic eigenlines at `(40,37)` (R20-3); (LV3-R) planted polynomials (split depth-2 pair, two Eisenstein quadratics, `e = 3`) and the four
  refusals; (LV3-258) generic == `ReadCell258(10)` field by field (ranks, charpoly == R19-1's `P` mod 37^8, t-ranks, Gram and P9 pivots), the
  four roots identified with `P_1`, `P_2` (recovered, not read), per-factor multisets of (mixed, P9, `v_π P′`, content) equal, the route's
  norms 6 / 4 / 6, `def:lvlattice`'s `c_f = e v(n!) − d_f` in the `NormalisationRecord` (`d_f = 0`, `c_f = 6` on all four forms, both signs; R20-3's prediction);
  (LV3-D2) at `(282,37)`, `(226,103)` (depth 2) and `(30,37)`, `(10,691)` (depth 1), `m_Eis` joint in `T_2, T_3, T_5`: block ranks 2 / 1,
  (H2) `v = v(B_k/k)` on the `p_0` sign and 0 on the other, every value == the lemma's congruence module, the congruence kind
  `T(W_m^{odd})/I_e`, (L1) by `BirchModularSymbolRoute` on the group-cocycle `W` over `Z/ℓ^3`, and the CROSS-KIND gate congruence =
  bilinear = linear = `v(B_k/k)`, and `c_f = v(n!)` with `d_f = 0` for `f` and `E_k` (7 / 2 / 0 / 0; R20-3); (LV3-I) `ι^*` over `Z/37^3` (`hecke::BuildRingInvolution`) at `(22,37)`, `(30,37)`, the torsion cell
  `(38,37)`: uint32 == uint64, free parts `d_k / d_k − 1`, `k = 1` == the field `HeckeInvolution`'s dims, `ℓ = 3` refused. Heavy adds the
  depth-2 cross-kind on [C]'s own `H^1` (the congruence route's `#Q_3`) and on the C++ cone's (L1) over `Z/37^3` / `Z/103^3`
  (`LV3_CROSS_KIND_HEAVY`), and `ι^*` on `H^1(Sym^282, Z/37^3)` (24 / 23 free summands, `LV3_IOTA_RING_282`). Prints `LV3_THETA_INDEX`,
  `LV3_258`, `LV3_L1`, `LV3_DEPTH`, `LV3_IOTA_RING`, `LV3_ARMS`. `ReadEisensteinSymbols` (R19-8's (L1)) now cuts a too-large `T_2`-block by
  `T_3`, `T_5` (no change where the `T_2` block already has the reading's rank). Console: `iota(H)` honours a `Z/ℓ^k` handle (script
  `049_lv3_iota_ring`).

**Slot 19, WP-NF (the number-field core; [E] 1.19.0-pre.2 `sec:lvnf`; the seventh target `NumberField`).** Roster after WP-LV + WP-NF **176 = 65 / 95 / 16**
(`--all` 160) with the one new name:
- `NumberFieldValidation` — **`fast`** (≈ 3.5 s, 117 checks; `NumberField/NumberFieldValidation.cpp`, `Registry/Slot19/WPNF.cpp`,
  `cmake/slot19/WPNF.cmake`). Oracle: slot-18 R18-2 (`docs/implementation/slot18/r182/`) and R19-3's `eqlayer2.py`; every expected value is
  copied from them. (1) `BigInt` (Karatsuba == schoolbook, Knuth-D identity under all signs, decimal round trip, gcd, valuation),
  `mulmod64` == its portable fallback, the NTT (2 / 3 primes, Garner) == schoolbook mod `37^3`, `67^3`, `691^3`, `2^32-5`; exact `B_12 = -691/2730`,
  `37 | B_i` by exact Bernoulli == the power-sum criterion. (2) exact `η_32`, `η_6` in `Z[ζ_37]`: FNV-1a-64 of the 36 decimal coefficients
  (`0xcba3d1938a721f7b`, `0xef292f5a4e321b01`), 127 / 31 digits, the coefficients and exponents against `r182/kummer_polys_l37.txt` (when present),
  `v_π(η^36 - 1) = 38 / 6` exactly and mod `37^3`. (3) layer 1 at 37: `v_i = i` except `v_32 = 38`, unit, not a 37th power, eigen `ω^i`, Kummer
  oracle. (4) the equivariant `Z/ℓ²` layer at `(37,32)`, `(59,44)`, `(67,58)`: exactly one unramified lift, `κ = 284 / 914 / 3292`
  (`u = y_0 = 13 / 31 / 59`), levels / thresholds / best `v` (2732 vs 2696, 6946 vs 6888, 8968 vs 8902), greedy == R18-2's full scan at two
  lifts of 37, the global tests and `Σ f_c`, `Σ |f_c|` of the canonical generator. (5) layer 1 at 691: `v = 692` at `i = 12, 200`, `v = 2` at `i = 2`.
  (6) negative controls: `(37, 30)` (regular) has no unramified lift; `η_6^37` passes the local test but is detected as a 37th power; a tampered
  `η_32` changes the FNV and is not a unit. (7) `Q(√2)`, `Q(2^{1/3})`, a unit of `Q(ζ_37)` inverted by Euclid over `Q`; Newton polygons
  (`Φ_37(x+1)` at 37: one slope `-1/36`); Hensel (`√-1` in `Z/5^10`, a root of `Φ_37` in `Z/149^3`). (8) runs
  `docs/matrix-engine/tools/check_numberfield_includes.sh` (STL only; no lower library includes `NumberField/`). Prints `NUMBERFIELD_ETA`,
  `NUMBERFIELD_LAYER1`, `NUMBERFIELD_LAYER2`, `NUMBERFIELD_CONTROL` and `NUMBERFIELD_GATE checks=117 failing=0`. Read-only, no golden line.
  **Slot-19 WP-NF2 adds part (9), the Coates–Wiles layer route** (`NumberField/{CwLayer,Ntt64,Sha256}.{h,cpp}`, `LadicInt.h`, `Mont.h`,
  `Parallel.h`; checks in `NumberField/CwLayerValidation.cpp`, `cmake/slot19/WPNF2.cmake`; no new name; now **≈ 6 s, 630 checks**). Oracle:
  R19-7 (`docs/implementation/slot19/R19-7_report.md`, `r197/out/level2_l*.json`). (9a) `mul128` == its portable fallback, Montgomery,
  Miller–Rabin, the 62-bit NTT primes `p ≡ 1 (15·2^32)`, NTT convolution == schoolbook at `f·2^a` lengths (direct and four-step), SHA-256
  vectors, base-`ℓ^d` limbs == `BigInt`. (9b) ring products == schoolbook, `π^n/ℓ` from binomials == by products, `σ_2` multiplicative,
  P6 `ℓ^s log(1+z) = ℓ^s(σ_2−1)λ_2` in all 9 digits. (9c) level 2 at 37 (35 classes), 59, 67, 103: the `λ_2` SHA-256 prefixes
  (`796a44bad240a894`, `d71f473a05266835`, `ef8deaad1ebc67f5`, `848b71076e769003`), **2314 / 2314 rows** == the JSON and == the exact
  Bernoulli / Kummer-law reference, the zeros 284 / 914 / 3292 / 228, `α`, `L_ℓ(1, ω^w)`, the level-1 control; level 3 at (37, 32): sha
  `bfe0068dbec3fba7`, zero **37580**, `α ≡ 28305`, control 1369 / 37, and the lean parameters `r = 3, W = 11` give the same rows.
  (9d) `W` below `r + 3m − 1` refused; a perturbed unit (`× u_2`, one digit) caught. Prints `NUMBERFIELD_CWLAYER`, `NUMBERFIELD_CWLAYER_CLASS`,
  `NUMBERFIELD_CWLAYER_ROWS`, `NUMBERFIELD_CWLAYER_CONTROL`. Env arms `NUMBERFIELD_LAYER_ALL=1` / `NUMBERFIELD_LAYER_CELLS` (env table).
- `HeckeLatticeModuleValidation` — **`slow`** (moved from `standard` by owner ruling 2026-10-03; ≈ 125–150 s on a loaded box, ≈ 0.8 GB, 301 checks; `HeckeExt/HeckeLatticeModule.{h,cpp}`,
  `HeckeExt/HeckeLatticeModuleValidation.cpp`, `Registry/Slot19/WPLC.cpp`, `cmake/slot19/WPLC.cmake`; slot-19 WP-LC; [E] `sec:block258`,
  `chk:latcmp`). The lattice comparison. `H^1(Γ; Sym^n Z/ℓ^K)` comes from the shipped `Z/ℓ^K` module route (`EquivariantCohomologyOnKT<uint64_t>`,
  `HeckeOperatorOnKT::H_matrix_module`), together with ι^* (`def:iota`(iv), read back by `H_class_coordinates`). The joint idempotent is Newton-lifted. The
  block and its ι-sign parts are found by `cyclic_decomposition`, and the Smith valuations by `invariant_factors(I, X)`.
  **(P)** Planted from R19-1's `P`, `P_1`, `P_2`, `Q_37` mod `37^6`, which are in source: `T_m ⊕ m` reproduces `chk:latcmp` (b), (c) at `M = 1 … 4`. `T_m ⊕ T̃` is rejected by
  `U_37` alone, and `T_m²` by `μ = 2`. **(L)** `(258, 37)`, `m = (37, T_2 − 29)`, one module run at `K = 4` (T_2, T_3, T_37), and
  `H_M = H_4/37^M` (that is (a)). At every `M` it checks: (a) the block is free of rank 8, each sign free of rank 4; (b) `μ = 3`; (c) `t` `⟨0^5,1,1,2⟩_M`
  and `U_37` `⟨0^3,1,5,6,6,6⟩_M`; (d) one sign is `T_m` and the other `m`, with **free sign = plus** (pinned after the run); (e) `P(t) = 0` and `T_p = Q_p(t)`
  (R19-1's tracked `universal_eigenform_n1000_mod37e6.txt`, read through the source root), on the block and on each sign. Negative controls: a perturbed `Q_p`
  is rejected, and the two signs are not alike. **(C)** The `ℓ = 7` controls chosen by WP-LC (`docs/implementation/slot19/wplc/predictions.md`, committed
  before the first run): `(48,7)` `(1,0,0,0)` Loewy 2, `(90,7)` `(3,3,1,0)` Loewy 2 and `(1,0,0,0)` Loewy 3, at `K = 4`, `M = 1 … 4`. The forced
  items are `P(t) = 0` and `T_p = Q_p(t)` for `p ≤ 13`. Each sign is matched against the over-orders `Z_7[t/7^j]` formed in source, and the gate pins
  the order read: `(48,7)` plus `Z_7[t/7]`, minus `T_m`; `(90,7)(3,3,1,0)` both `Z_7[t/7]`; `(90,7)(1,0,0,0)` plus `Z_7[t/7]`, minus none
  (readings pinned). The predicted "free" is printed and was **refuted** (a finding). A system that is not an eigenvalue is refused. Prints
  `EFFECTIVE HeckeLatticeModuleValidation arm=DEFAULT|FULL cells=4`, `PLANTED`, `LATCMP` and `LATCMP_SIGN` lines. Env:
  `HECKE_LATTICE_MODULE_FULL=1` (below). No golden line.

**Slot 19, WP-HL (the truncated `Λ`-adic Hecke algebra; [U] 0.3.0-pre.3 `sec:u-lambda`).** Roster **180 = 66 / 97 / 17**, `--all` 163.
- `HeckeLambdaValidation` — **`standard`** (≈ 7 s, ≈ 70 MB, 138 checks; `HeckeExt/HeckeHidaLambda{,Forms}.cpp`, `HeckeExt/HeckeLambdaValidation.cpp`,
  `Registry/Slot19/WPHL.cpp`, `cmake/slot19/WPHL.cmake`; slot-19 WP-HL). Oracle: R19-2's JSON (`docs/implementation/slot19/r192/data/`), never this
  code's output. (1) self-tests: NTT == schoolbook at `37^10`, `103^10`, `691^8`; `Δ = q∏(1−q^n)^24`, `E4³ − E6² = 1728Δ` on 600 coefficients; Berkowitz
  == exact determinants; tangent-number `B_k/k` == WP-NF's exact Bernoulli (294 / 294, `k ≤ 200`). (2) arm (Q): every ordinary Hecke matrix of
  `forms_37.json` (13 weights) and `forms_103.json` (6) reproduced exactly (`T_p`, `U` on `e M_k`, `e S_k` mod `ℓ^10`). (3) the `Λ` stage:
  `lambda_37_32.json`, `lambda_103_24.json` reproduced **field by field** (`LAMBDA_ORACLE … IDENTICAL`: `F`, `P_q`, `U`, `G̃`, the general route, `J`,
  the further-weight (U11) checks, `α`, rungs, `G̃(0)`); (U11) / (U12) / (U13) at all 12 truncations; KL `47910634`; rungs 284 / 37580, 228 / 914250;
  F4 m10: `(a_2 − eis_2)/G ≡ 35 (mod 37)` at the 8 weights 32 … 284 (F4's script forms `a_2 − eis_2 = −F_1`; in m10's sign `F_1/G ≡ 2`); 24
  `HECKE_LAMBDA` record lines (`hecke_lambda/v1`, FNV digest per line, not pinned). (4) arm (T): `HeckeHidaTower` at `(30, 37)`, `(66, 37)`, `(22, 103)`,
  `m ≤ 2`: `χ(T_2), χ(T_3) | H^1_ord = (Y − eis_p)·χ(T_p | e S_k)²` and `ord_rank = 2 s_S + 1` (6 / 6). (5) the `hida_tower/v1` catalogue at
  `ℓ ≤ 13`: 744 / 744 rows (R19-2 P7 in C++). (6) negative controls: `K + m − 2` digits, `K + m − 2` weights, non-consecutive weights,
  forms data mod `37^4` (monogenic route) and `37^5` (general route, `K + N − 1 = 7`), `k − 1 < W`: all `REFUSED`; `T_2 + 37²` at the further weight
  464 caught by (U11) at every `m`; `T_2 + 37` at the node 68 caught (the interpolant is not `ℓ`-integral, thm:u-interp(1)). Prints
  `EFFECTIVE HeckeLambdaValidation arm=DEFAULT|ALL cells=2|4`, `FORMS_ORACLE`, `LAMBDA_ORACLE`, `LAMBDA_CLASS`, `TOWER_CROSSCHECK`, `CATALOGUE_CHECK`.
  Env: `HECKE_LAMBDA_ALL=1` (below). No golden line.

**Slot 19, NB-2 (the served console, [P] v3.10.1 §18; `OC_BUILD_NOTEBOOK`).** Roster **179 = 66 / 96 / 17**, `--all` 162. Both names
are registered in every build and print `[SKIP] <name>: OC_BUILD_NOTEBOOK=OFF` (exit 0) when the switch is off.
- `ConsoleReadOnlyTagValidation` — **`fast`**, ≈ 1 s, **1483 checks** (`Console/ConsoleReadOnlyTagValidation.cpp`): (A) registry ⇄
  `Console/serve/read_only_verbs.tsv` both ways, tag for tag, in registration order; (B) registered == explicitly tagged (177 / 177);
  (C1) the registration TUs (`CoreVerbs.cpp`, `Console/Bindings/*.cpp`, `RegisterHeckeExtensionVerbs.cpp` and its six S24 CL-8 area siblings) have no writer / env /
  process entry point outside `Console/serve/read_only_sources.allow` (content-keyed, STALE fails; 8 hits allowed); (D) the
  `verbs.tex` read_only marks and `\CMNumReadOnly`; (E) PrintJson: the D set equals §18.5's table, 14 in-process envelopes (2^53 rule,
  Poly `low_to_high`, Matrix entries, a declared handle never forced, Record as pairs); (U) JSON reader / writer, env-gate pattern.
  `EFFECTIVE ConsoleReadOnlyTagValidation arm=ALL cells=177 tagged=177 read_only=168 not_read_only=9 read_only_verbs=158 fixture_rows=177 source_files=28 source_hits=8 envelopes=14 hint_rows=27 coverage_rows=45` (figures of the slot-24 CL-WD binary, notebook build; refreshed 2026-11-01).
- `ConsoleServeValidation` — **`standard`**, ≈ 20 s, **≈ 470 checks**, peak RSS of a child ≈ 0.33 GiB (arm H)
  (`Console/ConsoleServeValidation.cpp`): fork/exec of its own binary with `--serve`, whitelist env + `ENGINE_CUDA_DISABLE=1`, an empty
  scratch cwd under `$HACS_DATA/scratch` (removed). Arms (A) hello; (B) the 32 runnable numbered scripts, served
  `out` == `.expected` body byte for byte, `progress` == the in-process `#~` lines (digits normalised), 6 exempt scripts rejected as the
  table says (recomputed); (C) envelopes + `hash(x)` / `type(x)` cross-checks + the served determinism grid (`SERVE_DETERMINISM` line:
  default, `ENGINE_THREADS` 1 / 2 / 8, `program_cache=false`, one digest); (C2) every one of the 157 tagged overloads called
  (`Console/serve/coverage.oc` supplies the rest), cwd empty before / after, `git status --porcelain` unchanged; (D) the §18.7 rows with
  survival; (E) interrupt; (F) protocol (malformed, unknown op, missing id, busy at the 65th, close, EOF, an 8 MiB line ⇒ exit 70);
  (G) the env gate for `GOLDEN_EMIT`, `CONSOLE_EMIT_EXPECTED`, `HECKE_NEBENTYPUS_NB3_FULL`, `ENGINE_DEVICE`, `ASAN_OPTIONS`, the child's
  `RLIMIT_FSIZE` / `RLIMIT_CORE` = 0 and `NoNewPrivs`, a regular-file stdout refused; (H) RSS cap ⇒ `fatal rss_cap`, exit 70;
  (I) chatter; (J) completion / help / `verbs()` show the served view. `EFFECTIVE ConsoleServeValidation arm=ALL cells=… scripts=32
  exempt=6 … coverage=157/157 …`. Read-only; no env hook.

**Slot 20, WP-MEAS (the measure route; [E] 1.20.0-pre.1 `sec:lvmeasure`, gate `chk:lvmeas`; owner ruling O5: no fourth kind).** Roster
**181 = 66 / 98 / 17** (`--all` 164).
- `HeckeLValueMeasureValidation` — **`standard`** (≈ 4.5 s, ≈ 37 MB peak RSS, **220 checks** since slot-20 S1 (178 at WP-MEAS); `HeckeExt/LValue/ModularSymbolMeasure.{h,cpp}`,
  `HeckeExt/LValue/LFunctionRecord.{h,cpp}` (S1),
  `HeckeExt/LValue/HeckeLValueMeasureValidation.{h,cpp}`, `HeckeExt/LValue/MeasureFrozenR201.inc`, `Registry/Slot20/WPMEAS.cpp`,
  `cmake/slot20/WPMEAS.cmake`; slot-20 WP-MEAS). The `ℓ`-stabilised Mazur–Tate–Teitelbaum measure `μ(a+ℓ^m) = α^{−m}c(a,m) − α^{−m−1}ℓ^{k−2}c(a,m−1)`
  of an ordinary eigensymbol on [C]'s 7-vertex model (`def:lvmtt`), carried as the accessor `LValueRoute::measure()` of `linear` routes. Oracle:
  R20-1's Python (`docs/implementation/slot20/r201/`), frozen in `MeasureFrozenR201.inc`, never this code's output; predictions
  `docs/implementation/slot20/wpmeas/predictions.md` (committed first). Cells `(10,37)`, `(16,37)` (controls), `(30,37)` (`d = 1`), `(282,37)`,
  `(226,103)` (`d = 2`), all mod `ℓ^4`, levels 2 / 3. Arms: (M0) 8 — the route on the C++ module cone at `(30,37)` over `Z/37^4` (`measure()` of
  the cone classes over `r^±` == the symbol-side measure, frozen FNV; linearity; `HidaPairingRoute` / `EisensteinBernoulliRoute` refuse with
  `std::logic_error`; `(10,5)` refuses "not ordinary"; a non-eigenclass refuses); (M1) 45 — three-term relation, distribution, parity, the moment
  identity against WP-LIN's `EvAllJ` at six characters (0 / 66 … 1698 per sign), Riemann sum == group-ring branch value; (M2) 48 — `a_2`, `a_3`, `a_ℓ`,
  `α`, `s`, `μ^±(2+ℓ²)`, FNV of the level-2 unit balls, `μ^−(Z_ℓ^×) = 0`; (M3) 21 — `v(a_p − e_p) = d`, (L1) depth `d`, `μ^+ = d`, the reduced
  measure, `P^{Eis}` integral / primitive / `W`-residual `d`, `r^− ≡ sP^{Eis}` to depth `d`; (M4) 20 — the two Kubota–Leopoldt group rings
  (`E_{1,c}` and NumberField's `CwLayer`, `G_b = −(ℓ−1)ν_b`) agree for all 17 / 50 even classes at 37 (level 3) / 103 (level 2) and give
  `−(1−ℓ^{k−1})B_k/k` at 4 weights each; the in-TU Bernoulli tables == the slot-19 library; the congruence of measures at the critical moments
  (0 / 496, 4528, 11123) and as group-ring elements by both routes (16, 16, 49 branches); the pole branches fail mod `ℓ^d` everywhere and mod
  `ℓ^{d−1}` exactly at the located points (4 at 103; the **14 predicted points at `(282,37)`**); (M5) 13 — the `(μ, λ)` tables per sign and of the
  reduced plus measure; (M6) 23 — no `ℓ^{k−2}`, wrong root `α(1+ℓ)`, wrong twist `G_{a+3}`, wrong sign `+s`, the separator `T_2+3T_3+7T_5` refused
  with multiplicity 2 at the depth-2 cells; (M7) 42 (slot-20 S1, [E] `sec:lvlfunction`) — the record `lfunction/v1` at the five cells, both signs,
  every branch of the right parity: the `T`-polynomial at `u^j − 1` == the group-ring branch value (every `j ≤ n`, exact mod `ℓ^R`); at the three
  level-3 cells the level-3 element folded == the level-2 element and the level-2 coefficients == the level-3 ones mod `ℓ^{prec_2(t)}`, `t < ℓ`
  (`lem:lvlfunprec`; sharp at 628–631 of 648 per sign where `μ = 0`); `(μ, λ)` from the coefficients == `invariants()`; the canonical text
  deterministic. Env: `HECKE_LVALUE_MEASURE_691=1` (S2, below) adds the 691 arm. Prints `EFFECTIVE HeckeLValueMeasureValidation arm=DEFAULT|HEAVY cells=5|3` (and `arm=ELL691 cells=1`), `MEAS_CELL`, `MEAS_ROUTE`,
  `MEAS_ID`, `MEAS_EIS`, `MEAS_KL`, `MEAS_INV`, `MEAS_NEG`, `MEAS_LFUN`, `MEAS_ARMS checks=<c> failing=<f>`. Env: `HECKE_LVALUE_MEASURE_HEAVY=1` (below). No golden
  line.

**Slot 21, T1 (the in-house LLL and POLRED; the talk; plan `00-slot21-plan.md` "Talk"; Cohen GTM 138 §2.6 and Alg. 4.4.11 / 4.4.12, LIT-09 substitute).**
Roster **183 = 67 / 99 / 17** at its registration (`--all` 166).
- `NumberFieldLllValidation` — **`fast`**: ≈ 2.3 s (standalone `-O2` build of the six NumberField sources, quiet box), ≈ 6 MB, **674 checks**; prints `LLL_GATE checks=674 failing=0
  digest=0x9cfd92fb4a3968ec` (the FNV of every `H`, a fingerprint for the `-DNF_NO_INT128` arm and aarch64, not asserted) and `int128_path=<0|1>`. Files: `NumberField/{Lll,Polred}.{h,cpp}`
  (library, STL only), `NumberField/LllValidation.{h,cpp}`, `Registry/Slot21/T1_lll.cpp`, `cmake/slot21/T1_lll.cmake`. Every oracle is independent of `Lll.cpp` / `Polred.cpp`
  (own Gram–Schmidt reducedness test, own rational determinant, own products, brute-force shortest vector, expected polynomials known or from the Dickson recursion in the TU).
  - (1) Known lattices: a scrambled `Z^n` (`λ_1 = 1`), a scrambled `E_8` (`λ_1 = 2`), `A_2` at `δ = 1`, the integer relations of `2^{1/3}` and `√2 + √3` from decimals.
  - (2) Random lattices, `n = 2 … 6`, three `δ`: `H` unimodular, reduced Gram `= H G H^T`, Definition 2.6.1, `det G` preserved, the rational Alg. 2.6.3 and integral Alg. 2.6.7 give the same `H`
    (also on `G/q`), brute-force `λ_1` against Theorem 2.6.2's bound, Lagrange–Gauss at `n = 2`, `δ = 1`.
  - (3) POLRED: `Q(ζ_7)^+`, `Q(ζ_37)^+` (degree 18, `disc = 37^17`), `Q(ζ_ℓ)` for `ℓ = 7, 11, 37` (degree 36; `Φ_ℓ(−x)`, `λ_1 = ℓ − 1`).
  - (4) Negative controls: dependent rows, an indefinite Gram matrix, `δ ∉ (1/4, 1]`, a tampered `H`, non-reduced Gram matrices.
  - Read-only, no env hook, no golden line.

**Slot 21, P7 (`Λ`-adic `q`-expansions, truncated; [U] 0.4.0 `sec:u-lambda`; spec `s20/lead/owner_q3_padic_hida.md` P7).** Roster
**184 = 67 / 100 / 17** (`--all` 167; T1's `NumberFieldLllValidation` is the 67th `fast` name).
- `HeckeLambdaQExpValidation` — **`standard`** (≈ 7–9 s on a loaded box, ≈ 20 MB, **592 checks**; `HeckeExt/HeckeLambdaQExp.{h,cpp}`,
  `HeckeExt/HeckeLambdaQExpValidation.{h,cpp}`, `Registry/Slot21/P7_qexp.cpp`, `cmake/slot21/P7_qexp.cmake`). `Σ_{n≤30} a_n(X) q^n mod (ℓ^3, (X−x_c)^m)`,
  `m = 1, 2, 3`, per component of the cuspidal ordinary algebra (`Λ_{K,m}(x_c)[Y]/(F)`, `Y = T_{p0}`, `p0` the least residually squarefree prime) and the
  `Λ`-adic Eisenstein series (`a_p = 1 + ε_p`, `a_0 = G̃/2`), from WP-HL's forms arm at the 5 weights `k_0 + j(ℓ−1)`, `j = 3 … 7`, by thm:u-interp and the
  Hecke recursions (`a_{ℓ^r} = α^r`). Classes `(11, 2)` (Δ family), `(13, 0)` (Δ, class 0), `(23, 2)` (one residue-degree-2 component, `S_24`), `(37, 32)`,
  `(103, 24)`; centres: the first interpolation weight, the three further weights `j = 0, 1, 2`, and `k = 2` at 11 (63 truncations). Oracle: an
  independent forms route in the TU (Δ from Euler's pentagonal series, basis `Δ^i E4^a E6^b`, schoolbook products, `T_n` by the divisor formula for
  every `n ≤ 30`, the component as a unit-pivot generalised kernel). Arms: (1) τ(p), `p ≤ 13`; `T_2Δ = −24Δ`; 11a's η-product `a_p`; oracle `e S_k` ==
  WP-HL's forms arm (rank, charpoly) at the further weights; (2) `ε_p` interpolated == the closed form `p^{c−1} Σ binom(s_p, j) u^{−cj} Z^j`; (3) the
  Hecke relations `a_m a_n = Σ_{d|(m,n)} ε_d a_{mn/d²}`; (4) **Hida's control at the further weights** (429 specialisations): every `a_n` as a
  polynomial in `T_{p0}` == the oracle's `T_n` on the component mod `ℓ^{min(K, m v(x_{k'}−x_c))}`, `F(x_{k'}, T_{p0}) = 0`, rank 1 also the eigenform's
  `q`-expansion; the series == `E_{k'}^{ord}` with the exact `B_{k'}`; (5) the Δ family at `x_2` == 11a's η-product mod `11^{min(3, m v)}` (`α(x_2) = 1`);
  (6) the `Λ`-adic Eisenstein congruence `a_n(f) ≡ a_n(E) mod (G̃)` at 37 / 103 with `|Λ_{K,m}(x_c)/(G̃)| = ℓ^{min(K, m L_c)}` (`L_c` from the exact `B_c`:
  `103^{min(3,2m)}` at the rung centre 228); (7) negative controls: `W = K+m−2` and `K+m−2` weights `REFUSED`, `T_5 + 37²` at one node refused (not
  `ℓ`-integral), at every node caught at `k' = 32`, the wrong-weight specialisation caught. Prints `EFFECTIVE HeckeLambdaQExpValidation arm=DEFAULT
  cells=5`, `CLASS`, `CLASS_DONE`, `ALPHA_AT_2` (`α(Z) = [1, 19, 229]` mod `11^3` centred at `x_2`, for P5), `CONGRUENCE_AT_RUNG`, and the
  `HECKE_LAMBDA_QEXP` record lines (`hecke_lambda_qexp/v1`, FNV per line, not pinned) at `m = 3`. Read-only, no env hook, no golden line.

**Slot 21, T2 (the degree-`ℓ` Ribet field polynomial; `owner_q2_q4.md` Q2 (b); claims for F4 in `docs/implementation/slot21/T2_claim_for_F4.md`).**
Roster **185 = 67 / 101 / 17** (`--all` 168).
- `NumberFieldRibetFieldValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 65 s with 8 threads (`ENGINE_THREADS`), ≈ 35 MB, **29 checks**. Files: `NumberField/{MpReal,RibetField}.{h,cpp}`
  (library, STL only), `NumberField/RibetFieldValidation.{h,cpp}`, `Registry/Slot21/T2_ribet.cpp`, `cmake/slot21/T2_ribet.cmake`.
  - At `(37, 32)` it builds `P = charpoly(θ)`, `θ = Tr_{H/F}(η_32^{1/37})` (claims C3, C5), at two numerical precisions and exactly by CRT at split primes; all three must be equal.
  - It checks the Frobenius root counts at every prime `q < 20000` against the Kummer prediction (C4).
  - It checks `disc P = +37^185 · m²` (C2).
  - It builds the maximal order and checks its disc, exactly `+37^35` (C6).
  - It runs T1's POLRED on `O_F` with exact cross-checks (C7); the chosen polynomial is pinned.
  - Negative controls: another complement (twist `m + 1`) and `P + 1`.
  - It also prints the field data at `(691, 12)` and `(691, 200)`.
  - Lines: `RIBET_SPEC`, `RIBET_LAYER1`, `RIBET_NUMERIC`, `RIBET_MODULAR`, `RIBET_FROB`, `RIBET_DISC`, `RIBET_ORDER`, `RIBET_POLRED`, `RIBET_POLRED_POLY`.
  - **Read-only env arm** `NUMBERFIELD_RIBET_CELLS="691:12,691:200"` prints `EFFECTIVE NumberFieldRibetFieldValidation arm=CELLS cells=<k>`. For each cell it builds the polynomial by both routes (equal), prints its digests (`RIBET_CELL … fnv= sha256=`) and checks the Frobenius counts at 10 split, 10 non-split and 10 `q ≢ 1` primes. Times are in `docs/implementation/slot21/T2_report.md`. No golden line.

**Slot 21, P8 (`Λ`-adic modular symbols, truncated; [U] v0.5.0-pre.2 part 4 `sec:u-msym`; spec `docs/implementation/slot21/P8_spec.md` v0.2, referee F4).**
Roster **186 = 67 / 102 / 17** (`--all` 169).
- `HeckeLambdaModSymValidation` — **`standard`**: ≈ 24 s, ≈ 0.29 GB, **1126 checks + 179 finding gates** (default arm). Files: `HeckeExt/HeckeLambdaModSym.{h,cpp}`
  (library), `HeckeExt/HeckeLambdaModSymValidation.{h,cpp}`, `Registry/Slot21/P8_msym.cpp`, `cmake/slot21/P8_msym.cmake`.
  - Cells `(11, 2)`, `(13, 0)`, `(23, 2)` (residue degree 2), `(37, 32)` (both components, the cusp one through `m_Eis`); `K = 3`, `m = 1, 2, 3`, `B = 30`,
    `M_max = 2`; `N = 5` consecutive weights `k_0 + j(ℓ−1)` mod `ℓ^5`, then `F = 3` further weights. Per étale component of P7 and per [C]-sign
    ([C]-minus = geometric-even): `W(Z/ℓ^R)` read as the image of `W(Z/ℓ^{R+2})`, the `g(T_{p0})`-part, `T_ℓ` on that part only, `e_1`, then the rank.
  - Gates (spec Sec. 4): G1 ranks (per component both signs; totals of `e_1 W^±` at `ℓ ≤ 23`, of `e_1 H^1_±` on `V/(V^S+V^U)` at `ℓ ≤ 13`, the tower catalogue
    `2d_k+1`); G2 / G3 charpoly and every `T_p`, `U` as polynomials in `T_{p0}` == P7's forms data at the weight (mod `ℓ^5`) and P7's truncations (mod
    `ℓ^{SpecPrecision}`); G5 / G15 (BF) over all `ℓ−1` residues `b`, the second-line check at `m_Eis`, WP-LV3's joint `(T_2,T_3,T_5)` block; G6 operator
    masses a distribution, `= BuildMeasure` at `r = 1`; G7 `μ_{p_0} = 0` on unit balls; G8 unit check at the fixed `B_0` (finding); G9 the Newton interpolant of
    `ν_B` predicts every further weight mod `ℓ^{min(K',N)}` (finding); G10 `ν` independent of `φ`; G11 `j_k = L_k` (dual-D route at every weight; the amalgam
    route on `H^1(Γ; V)` at `n < ℓ−1`; defect at `n < ℓ−1`, finding beyond); G12 `r` has unit masses `≡ 0 mod ℓ^d`; G13 `ℓ ∈ {5,7}`; G14 `D_*` iso over `Z/ℓ^3`
    (slot-13 lattice pair) at `(10,5)`, `(12,5)`, `(24,7)`, `(30,11)`, `(40,37)` and the five `d_f ≥ 1` lines of `(40,37)` non-ordinary; G16 `U = T_ℓ`,
    `ℓ^{k−2} ≡ 0`; G4 level `ℓ` on the slot-13 code at `(11; k=12, 22)`, `(13; k=12)`: rank `2r`, charpoly `F²`, `U^{(ℓ)} = α(x_k, T_{p0})`.
  - Negative controls (9, each caught): perturbed `a_5`, wrong component, `K+m−2` weights, non-consecutive weights, values mod `ℓ^{K+m−2}`, planted non-unit at
    `B_0`, geometric sign as [C] sign, `HeckeTpWrongAdjoint`, scalar `α_0` for `U` at `r = 2`.
  - Lines: `CELL`, `RANKS`, `SIDE`, `DEPTH`, `GLUING`, `LEVEL_ELL`, `LATTICE`, `LATTICE_NEG`, `ARM`, and the record `HECKE_LAMBDA_MSYM` (`hecke_lambda_msym/v1`, one
    line per cell / component / sign / `m`; level-1 balls printed, level-2 balls in the FNV digest only; not pinned).
  - **Read-only env arms** (print `EFFECTIVE HeckeLambdaModSymValidation arm=<X> cells=<k>`): `HECKE_LAMBDA_MSYM_ALL=1` adds `(103, 24)` (weights to `n = 736`),
    `F = 5` on the default cells, the level-`ℓ` arm at `(11; 32)` and `(13; 24)`, G1 totals at 37 (1830 checks + 290 finding gates, ≈ 215 s, ≈ 0.59 GB); `HECKE_LAMBDA_MSYM_CELLS="ℓ:a:k0,…"`
    replaces the cell list (malformed token refused by position). No golden line.

**Slot 21, P9 (the two-variable measure by interpolation; spec `docs/implementation/slot21/P9_spec.md` v0.2, not refereed).**
Roster **187 = 67 / 103 / 17** (`--all` 170).
- `HeckeLambdaTwoVarValidation` — **`standard`**: ≈ 7.5 s, ≈ 32 MB, **71 checks + 41 finding gates** (default arm). Files: `HeckeExt/HeckeLambdaTwoVar.{h,cpp}`
  (library: branch elements from unit-ball masses, the Taylor shift, Lagrange weights of `thm:u-interp` at any point of the disc and their derivative, the zero of a
  `Λ`-function, 11a's Manin symbols on `Γ_0(11)`, Tate's `L`-invariant of 11a1, the Iwasawa log), `HeckeExt/HeckeLambdaTwoVarValidation.{h,cpp}`,
  `Registry/Slot21/P9_twovar.cpp`, `cmake/slot21/P9_twovar.cmake`.
  - Inputs: P8's readings and normaliser of record (`ReadComponent`, `FirstUnitBall`, `Normalised`) at `N = 5` + `F = 3` weights, `K = 3`, `K' = 5`, `m = 1, 2, 3`;
    cells `(11, 2)`, `(13, 0)` (ball level `M = 3`), `(23, 2)`, `(37, 32)` (`M = 2`). Builds the branch elements `g^{(a)}_i(X)` of the normalised family, their
    truncations mod `(ℓ^K, (X−x_c)^m)` and the coefficients of `L_a(X, T) mod ω_{M−1}(T)` (record `HECKE_LAMBDA_TWOVAR`, `hecke_lambda_twovar/v1`, one line per
    cell / component / sign / `m` / branch of the right parity; `t < 4` printed, every `t` in the FNV digest; not pinned).
  - Gates (spec Sec. 4): V1 assembly (parity vanishing, integrality, specialisation at the interpolation weights, Lagrange == P8's `NewtonWeights`); V2 numerical control
    at the further weights (finding); V3 P1's `lfunction/v1` pipeline (`RunSymbolCell` with a crafted separator, `BuildMeasure`, `MakeLFunctionRecord`) `= μ^{P1}(B_0)·L_a(x_k)`
    mod `ℓ^5` at the interpolation weights; V4 the same against the predicted `L_a` at the further weights (finding; `P1_COVERAGE` line: P1 refuses at `(11; k ≥ 22)`, `W`
    not free, and cannot select the non-Eisenstein component of `(37, 32)`); V5 / V6 / V7 the Eisenstein arm at `(37, 32)` (WP-MEAS's KL group ring at `M_E = 3`;
    `α_32` from 7 exact Bernoulli values, `== 281570 mod 37^4`; the cross products with `G_{a+1}G_{k−1−a}` weight by weight mod `37^{L_k}` and **at `X = α_32` mod `37^3`**);
    V8–V12 the weight-2 arm at `(11, 2)` (11a's symbols: rank 1, distribution, trivial zero; control at `x_2` on every unit ball to level 3, both signs; the family's
    trivial zero and GS's derivative; `L_GS = −2 dα/dk(2)` from P7's forms side at `W = 8`, 8 weights `== L_Tate mod 11^8`, `L_MTT == L_Tate mod 11^5`).
  - Negative controls (14, each caught): `ω^{a+1}` for `ω^a`, four weights for `m = 3`, P1 with the other sign's symbol, the wrong twist `G_{a+3}`, `α + ℓ`, 11a with
    `ψ∘T_2 = +3ψ`, `L_GS` without `−2`.
  - Lines: `CELL`, `SIDE`, `P1`, `P1_COVERAGE`, `P9_EIS2V`, `P9_11A`, and the record lines.
  - **Read-only env arms** (print `EFFECTIVE HeckeLambdaTwoVarValidation arm=<X> cells=<k>`): `HECKE_LAMBDA_TWOVAR_ALL=1` adds `(103, 24)` (Eisenstein arm at `M_E = 2`)
    and `M = 3` at 37 (99 checks + 58 finding gates, 0 failing, 0 fired, ≈ 100 s, ≈ 0.29 GB; V6 at `(103, 24)`: `α_24` `== 2266 mod 103^2`, cross products `≡ 0 mod 103^2` on 5047 slots at `X = α_24`, the KL precision; at 37 with `M = 3`: 21904 slots mod `37^3`); `HECKE_LAMBDA_TWOVAR_CELLS="ℓ:a:k0,…"` replaces the cell list (malformed token refused by position). No golden line.

**Slot 21, P3 (coefficient rings for the measure; spec `docs/implementation/slot21/P3_spec.md` v0.2, not refereed).**
Roster **188 = 67 / 104 / 17** (`--all` 171).
- `HeckeLValueCoefficientRingValidation` — **`standard`**: ≈ 1.2 s, ≈ 24 MB, **603 checks** (default arm). Files: `HeckeExt/LValue/CoefficientRingMeasure.{h,cpp}`
  (library: `ORing` = `(Z/ℓ^R)[x]/(F)`, Rabin irreducibility / multiplicity / two-factor Hensel lifting, the eigen-symbol by Gauss–Jordan over the local ring with unit
  pivots, `α` in `O`, the measure by `O`-linearity from WP-MEAS's `BuildMeasure` `c`-tables, route B through WP-LV3's `m`-block reader and `φ_ρ`),
  `HeckeExt/LValue/HeckeLValueCoefficientRingValidation.{h,cpp}`, `HeckeExt/LValue/CoefficientRingFrozenP3.inc` (GENERATED by `docs/implementation/slot21/p3/run_p3.py
  --emit`, the Python oracle of record), `Registry/Slot21/P3_coeffring.cpp`, `cmake/slot21/P3_coeffring.cmake`.
  - Cells (`R = 4`, level 2): `(10,37)`, `(16,37)` (`deg F = 1`); `W(F_{q})`: `(22,23)`, `(22,29)`, `(26,31)`, `(26,37)`, `(28,29)` (`f = 2`), `(34,37)` (`f = 3`); totally
    ramified `Z_ℓ[x]/(F)`, `e = 2`: `(26,131)`, `(26,139)` (`S_28`); refusal `(30,29)` (not ordinary); Hida `(50|78|106, 29)` against `(22,29)` at `R = 3`.
  - Arms: R0 Eichler–Shimura (`charpoly T_2, T_3 | W^−` == the `q`-expansion charpolys of `S_k`, frozen from `p3/qexp_oracle.py`), `ḡ`, `F`; R1 the eigen-symbols
    (`T_p`-eigen `p ∈ {2,3,5,7,ℓ}`, `a_2 = x`, frozen `t_0`, `a_2`, `a_3`, `a_ℓ`, `α`); R2 `prop:lvmtt` over `O` (three-term, distribution, the moment identity against
    `EvAllJ`, five characters, `μ^{geo-odd}(Z_ℓ^×) = 0`); R3 frozen `μ(2+ℓ²)`, `μ(Z_ℓ^×)`, FNV of the coefficients and of `(Tr, N)`; R4 Galois (Frobenius / `x ↦ −F_1 − x`,
    the conjugate symbol recomputed, every level-2 ball); R5 route B (one order, `e = 2`, two roots; `φ_ρ(P) = P_ρ`, `a_p`, `α`, every ball; presentation-free FNV == frozen);
    R6 Hida control mod `𝔪` over `W(F_{29²})` (`μ_n ≡ c μ_22`, `c = 19, 4, 21` / `1, 1, 1`, 0 / 812 mismatches); R7 R20-1's frozen Δ FNVs, WP-MEAS's `c`/`μ` tables entry by
    entry, base change into `(Z/37^4)[x]/(x² − 2)`; R8 negatives (no `ℓ^{k−2}`, wrong root, Galois without `σ`, Hida with the conjugate: best 86 / 812) and refusals by
    name (`not ordinary`, `does not divide`, `not irreducible`, `residual eigenspace of rank >= 2`).
  - Lines: `P3_CELL`, `P3_ID`, `P3_FROZEN`, `P3_GAL`, `P3_RAMB`, `P3_HIDA`, `P3_BASE`, `P3_NEG`, `P3_ARMS checks=<c> failing=<f>`. No golden line, no record.
  - **Read-only env arm** `HECKE_LVALUE_COEFFRING_HEAVY=1` (prints `EFFECTIVE HeckeLValueCoefficientRingValidation arm=HEAVY cells=2`, else `arm=DEFAULT cells=11`): adds
    `(22, 144169)` (`S_24` at its ramified prime, `R = 2`, level 1, routes A and B, no frozen values) and `(34, 37)` at level 3 — 674 checks, 0 failing, ≈ 138 s, ≈ 74 MB.

**Slot 21, P2 (the Eisenstein measure exactly in Λ; spec `docs/implementation/slot21/P2_spec.md` v0.2, not refereed).**
Roster **189 = 67 / 105 / 17** (`--all` 172).
- `HeckeLValueEisensteinMeasureValidation` — **`standard`**: ≈ 6.2 s, ≈ 40 MB, **239 checks** (default arm; 225 before P2x, 5.3 s, 20 MB). Files: `HeckeExt/LValue/EisensteinMeasure.{h,cpp}` (library:
  Bernoulli numbers mod a prime, Zagier's Laurent polynomial `n!·p_k^-` mod a prime, its Manin-path symbol with the singular monomial dropped, the Dedekind–Rademacher
  sums `D(a,m)`, `μ^Eis = −D(a,m) + ℓ^{k−2}D(a,m−1)`, the convolution `−E_1 ⋆ ι_*E_{k−1}` on units in a scaled `ℓ`-adic representation, branch elements, the level-`M`
  polar element, the residue `Res = (1−ℓ)(log_ℓ u/ℓ)(1−ℓ^{k−1})B_k/k` and `Res/(u^r−1)`), `HeckeExt/LValue/HeckeLValueEisensteinMeasureValidation.{h,cpp}`,
  `Registry/Slot21/P2_eismeas.cpp`, `cmake/slot21/P2_eismeas.cmake`. Calls WP-MEAS's public API only (`EisensteinSymbol`, `BuildMeasure`, `RunSymbolCell`, the two KL routes,
  `TwistedBernoulliTable`). Python oracle `docs/implementation/slot21/p2/run_p2.py` (output of record `p2/out_run_p2.txt`).
  - Eisenstein cells `(n,ℓ)` at level `M`: `(12,5)` 4, `(14,7)` 3, `(16,11)`, `(20,13)`, `(10,37)` (`d = 0`); `(30,37)`, `(66,37)`, `(42,59)`, `(56,67)`, `(22,103)` (`d = 1`),
    `(282,37)`, `(226,103)` (`d = 2`) at level 2; `(10,691)` at level 1. Cusp-form cells (WP-MEAS's): `(30,37)` `M = 3`, `(282,37)` `M = 3`, `(226,103)` `M = 2`, `R = 4`.
  - Arms: E0 Zagier's relations `1+S`, `1+U+U²` at 6 random points mod `2^61−1` (the interior `P^Eis` alone fails: negative); E1 the symbol `= −D(a,m) + (B_k/k)a/ℓ^m` at
    every residue `a < ℓ^m`, `m ≤ M` (mod `2^61−1` and `2^62−57`; one prime at `ℓ ≥ 100`); E2 `μ^Eis` a distribution and odd (negatives: the cusp term kept, WP-MEAS's
    `μ^poly`); E3 the convolution form on units; E4 the twisted masses `Σ ω^i(a)μ^Eis(a+ℓ^M) = −B_{1,ω^i}B_{k−1,ω^{−i}}/(k−1)` exactly (`TwistedBernoulliTable`); E5 regular odd
    branches `= −G_{a+1}(u(1+T)−1)G_{k−1−a}(u^{k−1}(1+T)^{−1}−1)` by both KL routes (`E_{1,c}` only at `ℓ > 103`), even branches 0; E6 pole branches: valuation `d − M`
    (`≥ 0` when `d ≥ M`), minus the polar element integral; E7 `v(μ^poly − μ^Eis) = d` exactly off the pole branches, `v(μ^poly − (μ^Eis − polar)) = d` on them; E8 the
    cusp forms' pole branches at every critical point: `𝓛^−_{f,a}(u^j−1) ≡ −s(F_1F_2 + Res/(u^r−1)) mod ℓ^d` (0 / 62, 0 / 566, 0 / 454) and the points with
    `v(Res/(u^r−1)) < d−1` = [E] `cl:lvmeascong`(4)'s located 14 + 4; E9 negatives (no polar term, `−Res`: every point fails; `Res·(1+ℓ)`: fails exactly where `ℓ | r`;
    the wrong twist `G_{a+3}` at `M ≥ 2`: 0 matches).
  - **E8L2 / E9L2 (P2x, spec §10; in the default arm, 14 checks, ≈ 0.8 s at 16 threads, ≈ 3.9 s at `ENGINE_THREADS=1`)**: Δ's own eigensymbol at `(10,691)`,
    `R = 2`, level 2 (S2's symbol cell): (a) `𝓛^−_{Δ,a}(u^j−1) ≡ −s(F_1F_2 [+ Res/(u^r−1)]) mod 691` at every critical point of **every** odd branch (3795 = 3773 + 22,
    0 failing, located ∅; NEG no polar / `−Res` 22 / 22, `Res·(1+ℓ)` 0 / 22) — level-independent at `d = 1` since `u ≡ 1 mod ℓ`; (b) the genuine level-2 check,
    `g^Δ_a ≡ s(g^Eis_a − polar_a)` in `Z/691[C_691]` on all 345 odd branches (`g^Eis` by the E3 convolution through the branch homomorphism, `BuildEisLadic(…, with_mu =
    false)`), E6 at level 2 (`min v = −1`, minus polar integral), `s = 286647`; NEG no polar / `−Res` / `Res·(1+ℓ)` (a unit times `N_u`: fails here, passes at every
    critical point) 2 / 2, `s+1` 345 / 345. Line `EISMEAS_DELTA2 …` with the fingerprint `fp_gDelta=11:(443652,194679)689:(443652,11103)` (= the Python oracle
    `p2/p2x_oracle.py`, Δ from its classical period polynomial; output `p2/out_p2x_oracle.txt`).
  - Lines: `EISMEAS cell=…`, `EISMEAS_POLE cell=…`, `EISMEAS_DELTA2 cell=…`, `P2_ARMS checks=<c> failing=<f>`. No golden line, no record.
  - **Read-only env arm** `HECKE_LVALUE_EISMEAS_HEAVY=1` (prints `EFFECTIVE HeckeLValueEisensteinMeasureValidation arm=HEAVY cells=15`, else `arm=DEFAULT cells=13`): adds
    `(30,37)` at level 3 (`37^3` balls) and `(20,131)` at level 2 — 273 checks (259 before P2x), 0 failing, ≈ 12.6 s, ≈ 40 MB.

**Slot 21, P4 (wild characters on the L-side; spec `docs/implementation/slot21/P4_spec.md` v0.2, not refereed).**
Roster **190 = 67 / 106 / 17** (`--all` 173).
- `HeckeLValueWildCharacterValidation` — **`standard`**: ≈ 5.3 s, ≈ 0.09 GB, **222 checks** (default arm; 201 / 4.0 s / 24 MB before slot-21 P4x). Files: `HeckeExt/LValue/WildCharacter.{h,cpp}` (library:
  `OArith` = `(Z/ℓ^P)[ζ]/Φ_{ℓ^{m−1}}` in `uint64` with `v_π`; since P4x its twin `OArith128` (`u128` coefficients through `engine::ModCtx<u128>`, `ℓ^P < 2^126`) with the
  128-bit W6 inputs `OmegaTable128`, `EllBernoulli128`, `Residue128`, `WildBernoulliFB128`, `GroupRingAtWildPoint128`; the wild characters `χ_{i,t} = ω^iψ_t` of conductor `ℓ^m`, character sums, `F·B_{r,χ}` by the definition,
  group-ring elements at a wild point `Σg_iζ^{ti}u^{ir}`; the complex side: `Δ`, `ΔE_4` to `q^{mmax}` in int128, `ρ_n` exactly over `Z` (BigInt), the two eigensymbols
  `P^±` exactly by BigRational elimination, `ρ_n(γ_{a,M})Φ({a/M,∞})` exactly), `HeckeExt/LValue/HeckeLValueWildCharacterValidation.{h,cpp}`, `Registry/Slot21/P4_wild.cpp`,
  `cmake/slot21/P4_wild.cmake`. Calls the public APIs of WP-MEAS, P2 and NumberField (`CycloModRing`, `MpReal`) only. Python calibration `docs/implementation/slot21/p4/`
  (output of record `p4/out_cal.txt`).
  - Arms: W0 the characters (multiplicative, primitive, `χ(u) = ζ^t`) at `(ℓ,m) = (5,2), (5,3), (7,2), (11,2), (37,2)`, `OArith` = `nf::CycloModRing` (product, `v_π`); NEG `t = ℓ`
    not primitive. W1 `F·B_{r,ω^{b−r}ψ_t} = −F·r·G_b(ζ^tu^r−1)` (both KL routes, `r ≤ 10`), pole branch `v_π(B/r) = −1`, NEG `ζ^{−t}` (0 matches). W2 [E] `prop:lvmtt`(4) at wild `χ`
    (`α^{−m}`), both signs, all `i`, `t ∈ {1,2}`, all `j`, at `(10,11)`, `(10,13)`, `(10,37)` (controls) and `(30,37)` (`R = 4`, `M = 3`, `m = 2`); the symmetry
    `λ_{χ,j} = −ελ_{χ̄,n−j}`; NEG `χ` for `χ̄` (matches only at `j = n/2`), `α^{−(m−1)}` (0 matches). W3 branch elements at `ζ^tu^j−1` = Riemann sums (mod `ℓ^{min(M,R)}`),
    `v_π(𝓛_b(ζ−1)) = eμ_b + λ_b` at every readable branch (`μ = 1` on every even branch of `r^+` at `(30,37)`). W4 P2's `μ^Eis` at wild `χ`: `−B_{1,χ}B_{k−1,χ̄}/(k−1)`
    exactly, even masses 0, the polar element at `ζ^t` of `v_π = ed−1`, value − polar integral, at `(12,5)` `m = 2, 3`, `(14,7)`, `(16,11)`, `(30,37)`. W5 complex: every
    primitive `χ` of conductor 25, 49, 121 (`k = 12`) and 25, 49 (`k = 16`): `Ω_{χ,j} = I(j+1)C(n,j)M^{j+1}/(χ(−1)(−i)^{j+1}τ(χ)λ_{χ,j})` equals the conductor-1 `Ω^±` to
    `≤ 10^{−59}` (gate `10^{−30}`; 256-bit `nf::MpReal`), split-independence, root number `w = τ(χ)²/M`, `λ` of the wrong sign 0; NEG `τ(χ̄)` and conductor `ℓM` (rel. dev ≈ 2
    and `≥ 10^4`). W6 the cusp form's pole branches at wild points `≡ −s(F_1F_2 + Res/(ζ^{±t}u^r−1)) mod ℓ^d`: `(30,37)` 0 / 62, `(282,37)` 0 / 566 and (P4x, by the 128-bit route:
    `103^{vD+d}` reaches `103^{10} > 2^62` at four points) `(226,103)` 0 / 454; NEG no polar, `−Res` fail everywhere; `Res·(1+ℓ)` 0 failures (invisible at wild points);
    route agreement (P4x): at `(30,37)`, `(282,37)` the 128-bit route (`P = 13`) is run beside the 64-bit one (`P = 11`): `ω^x`, `ℓB_s`, `Res`, every point's `F·B`, product and
    polar element equal mod `37^{11}`, the five counts equal. Python oracle `p4/p4x_pole_oracle.py` (exact integers; output `p4/out_p4x_oracle.txt`): the same counts at all three cells. W7 `UnitRoot` refuses at `(10,5)`, `(10,7)` (non-ordinary).
  - Lines: `WILD_W0`, `WILD_W1`, `WILD_CUSP`, `WILD_EIS`, `WILD_COMPLEX`, `WILD_POLE` (`route=u128 P=… Pneed=…` on the 128-bit route), `WILD_ROUTE`, `WILD_W7`, `P4_ARMS checks=<c> failing=<f>`. No golden line, no record.
  - **Read-only env arm** `HECKE_LVALUE_WILD_HEAVY=1` (prints `EFFECTIVE HeckeLValueWildCharacterValidation arm=HEAVY cells=32`, else `arm=DEFAULT cells=28`; 31 / 27 before P4x): adds W5 at
    conductors 125 and 169 (`k = 12`), W2/W3 `(10,11)` at `m = 3` (`e = 110`) and W6 `(30,37)` at `t = 2` — 259 checks, 0 failing, ≈ 8.9 s, ≈ 0.09 GB (238 / 7.4 s before P4x).

**Slot 21, WP-LIC (licence compliance; owner rulings 2026-10-04 / 2026-10-06; inventory `docs/licence/THIRD_PARTY.md`).**
Roster **191 = 68 / 106 / 17** (`--all` 174; `EXPECT_NAMES` 191).
- `LicenceGuardValidation` — **`fast`** (≈ 1 s, read-only, no env hook, no golden line; `Registry/Slot21/WPLIC.cpp`, `cmake/slot21/WPLIC.cmake`). Runs
  `docs/licence/tools/check_licences.sh` on the source tree (path baked in as `OC_SOURCE_DIR`, then walked up from the executable / cwd; `[SKIP]` when the
  tree or git / python3 is absent) and requires its `LICENCE_GUARD … failures=0 verdict=OK` line. The script checks: (1) `LICENSE`, `LICENSE.GPL`, `NOTICE`,
  `REUSE.toml` (default annotation `path = "**"`), `COPYRIGHT.md`, `lean/LICENSE`, `docs/LICENSE`, `THIRD_PARTY.md` exist; (2) `add_spdx.py --check`: every
  header-able tracked file (C / C++ / CUDA / cmake / shell / python / js / css / sbatch, and LaTeX / bib / sty) has an `SPDX-License-Identifier` header or is on
  `docs/licence/pending_tex_headers.txt` (a stale or unknown pending entry fails; `lean/**`, vendored paths, `docs/literature/`, generated and data files are covered
  by `REUSE.toml` instead); (3) every identifier in use is on the allow-list (`LGPL-3.0-only WITH LicenseRef-CUDA-exception`, `CC-BY-4.0`, `Apache-2.0`, `MIT`, `OFL-1.1`,
  `LicenseRef-third-party-literature`) and has its text in `LICENSES/`; (4) no SPDX header inside `lean/Vendor/**`, every file of `lean/Vendor/AnthropicFLT/MANIFEST.tsv`
  matches its sha256, `notebook/vendor/katex/SHA256SUMS` verifies; (5) no tracked PDF outside `docs/latex`, `docs/talk` (the 14 third-party PDFs of
  `docs/literature/` were reported as `known_third_party_pdfs=14` until slot 22 WP-LIC2 removed them from HEAD: now `known_third_party_pdfs=0`; history still holds them, `THIRD_PARTY.md` §3). Negative controls (a `GPL-2.0-only` header, a missing header) were run by hand at
  its landing. Sweep tool: `docs/licence/tools/add_spdx.py [--apply | --check]`.

**Slot 21, P5 (b), (c) (the Iwasawa invariants of the measure branches, the tame functional equation; spec `docs/implementation/slot21/P5_spec.md` v0.2, not refereed).**
Roster **192 = 68 / 107 / 17** (`--all` 175; `EXPECT_NAMES` 192).
- `HeckeLValueIwasawaInvariantsValidation` — **`standard`**: ≈ 22 s, ≈ 0.10 GB, **580 checks** (default arm, 22 cells). Files: `HeckeExt/LValue/HeckeLValueIwasawaInvariantsValidation.{h,cpp}`,
  `Registry/Slot21/P5_iwasawa.cpp`, `cmake/slot21/P5_iwasawa.cmake`. Calls the public APIs of WP-MEAS (`RunSymbolCell`, `UnitRoot`, `BuildMeasure`, `branch`, `invariants`,
  `KlGroupRingBernoulli`, `GrTwInv`), WP-LIN's `EvAllJ` and WP-LV's `BernoulliOverKTable` only; includes `MeasureFrozenR201.inc` / `MeasureFrozenS2.inc` for (I5). No Python calibration.
  - Arms: (I0) 60 — the Kubota–Leopoldt `(μ, λ)(G_b)` at every even `b` for `ℓ ∈ {11, …, 47, 59, 67, 103, 131}`, by the group ring (level 2) and by exact Bernoulli numbers alone
    (Newton divided differences of `−(1−ℓ^{r−1})B_r/r` at `r = b + s(ℓ−1)`), equal; `μ = 0`; `λ = 1` exactly at `(37,32)`, `(59,44)`, `(67,58)`, `(103,24)`, `(131,22)` (HHO 2017, LIT).
    (I1) 132 — the tame functional equation `λ_{χ,j}(P) = −χ(−1)(−1)^jλ_{χ̄,n−j}(P)` at conductor 1 and `ℓ` on `r^±` and a generic `P ∈ W`, every `i`, `j`; parity; NEG flipped sign (0 matches);
    NEG `χ` for `χ̄` (matches exactly at `j = n/2` on `r^−`; pairs of power `ℓ^{R−v} < 10^5` left out as `low_power`, the expected number of accidental matches printed).
    (I2) 88 — the branch FE `g_b = −(−1)^b·GrTwInv(g_{n−b}, n+1)` mod `ℓ^{min(M,R)}`; NEG flipped sign (vacuous where every branch is `0` mod `ℓ^{min(M,R)}`, recorded).
    (I3) 270 — the table per cell and sign: `invariants()` against the **values oracle** (divided differences of the critical values `(−1)^jC(n,j)^{−1}E_{i,j}λ_{ω^i,j}` at
    `T_j = u^j − 1`, no ball table), integrality, `(μ,λ)_b = (μ,λ)_{n−b}`, `λ` odd at even self-dual branches / even at odd ones, the near-trivial zero where `α ≡ 1 (ℓ)`, `μ = 0` at
    the controls. (I4) 24 — level-1 Greenberg–Vatsal `λ^−_a = λ(G_{a+1}) + λ(G_{k−1−a})`, `μ^− = 0` off the pole branches; `μ^+ = d`. (I5) 6 — the frozen WP-MEAS / S2 tables.
  - Cells: `(10, ℓ)` (Δ) at the 15 primes above, `R = 5`, level 2; `(16,37)`; Eisenstein `d = 1` at `(30,37)`, `(66,37)` (`R = 5`), `(42,59)`, `(56,67)`, `(22,103)`, `(20,131)`, level 3.
  - Lines: `IWA_KL`, `IWA_FE`, `IWA_GRFE`, `IWA_TABLE cell=… sign=… default=(μ,0) other: b:(μ,λ)<src>` (`i` invariants, `v` values oracle, `iv` both), `IWA_GV`, `IWA_FROZEN`, `IWA_CELL`,
    `P5_ARMS checks=<c> failing=<f>`. No golden line, no record.
  - **Read-only env arm** `HECKE_LVALUE_IWASAWA_HEAVY=1` (prints `EFFECTIVE HeckeLValueIwasawaInvariantsValidation arm=HEAVY cells=25`, else `arm=DEFAULT cells=22`): adds the KL table at 691
    (344 classes, `λ = 1` at 12 and 200) and the cells `(282,37)`, `(226,103)` (`d = 2`, level 2; their plus side by the values oracle) and `(10,691)` (`R = 3`) — 658 checks, 0 failing, ≈ 72 s, ≈ 0.10 GB.


**Slot 22, LN23 (the weight-2 level-`N` Eisenstein route at `p = 2, 3`, the curve object; spec `docs/implementation/slot22/LN23_spec.md` v0.2, report `LN23_report.md`; [C] `prop:levelNcurve`, `rmk:levelNcurvefamily` (v1.22.0-pre.1)). LN23-F (spec v0.3 §11, report `LN23F_report.md`) added the family certificate, (FC), (FC0), (G), (G2) and the STURM arm.**
Roster **193 = 68 / 108 / 17** (`--all` 176; `EXPECT_NAMES` 193). Fragment `Registry/Slot22/LN23.cpp`, `cmake/slot22/LN23.cmake` (the slot's first C++ package created `Registry/Slot22/`).
- `HeckeLevelNCurveValidation` — **`standard`**: ≈ 19 s, ≈ 41 MB, **1177 checks** (default arms; 1064 before LN23-F). Files: `Hecke/HeckeLevelNCurveValidation.{h,cpp}`; library changes in
  `Hecke/HeckeLevelN.cpp`, `HeckeLevelNSparse.{h,cpp}`, `HeckeLevelNHeilbronn.{h,cpp}`, `HeckeLevelNR3.{h,cpp}`: at `n = 0` the fixed spaces of `S`, `ST` are orbit sums at every `p`
  (value-identical at `p ≥ 5`); the curve object is an explicit opt-in (`SparseCokernel::BuildCurve`, `CokernelPresentation::BuildCurve`, `CokernelHeckeMatrices(…, CokernelObject::kCurve)`,
  `n > 0` refused by name); `ReadEisensteinR3Scan` admits `p ∈ {2, 3}` at prime `N` (reading fields `object`, `num_condition = v_p(num((N−1)/12))`, `exact`). The default entry points keep their
  `p ≥ 5` refusals and texts (`HECKE_LEVEL_N_R3_CELLS` unchanged).
  - Arms: (P) the `n = 0` generators are orbit indicators covering `P^1(Z/N)` once, sparse and dense, at `p ∈ {2, 3, 5, 7, 134217757}`; `BuildCurve = Build` (same RREF) at `p ≥ 5`.
    (Z1) the torsion gate: `dim_{F_p} = 2g + c − 1` and `h0 = 1` at `p ∈ {2, 3, 5, 7, 134217757}`, every prime `N ≤ 600` and composite `N ≤ 100` (183 levels). (H) `RelEscapesOnGenerators = 0`
    at `p = 2, 3`, `q ≤ 13`, 10 levels. (X) dense = sparse on the curve route, `kCurve = kGroup` at `p ≥ 5`. (Z3) CE §6 `(41,2)` 7/7/4, `(2143,3)` 357/7/4, `(73,2)`, `(89,2)`, `(137,2)`,
    `(17,2)`, `(19,3)`, `(37,3)`, `(73,3)` and the WP-9 controls `(11,5)`, `(31,5)`, `(181,5)`, `(29,7)` (`dimH1 / dim W / Loewy`, Hecke primes `q ≤ 13`); every reading also checks
    `dimH1 = 2g + 1`, `dim W` odd, strictly decreasing radical layers, `dim W = 1` iff `p ∤ num((N−1)/12)`. (Z4) CE Thm 1.1 on the 34 primes `N ≡ 9 mod 16`, `N ≤ 2000` (`2^m ‖ h(−4N)` by a
    reduced-form count, `dim W = 2^m − 1`, Loewy `2^{m−1}`). (Z5) CE Thm 1.2(i)+1.3(i) on the 39 primes `N ≡ 10, 19 mod 27`, `N ≤ 2500` (`dim W = 3` iff `((N−1)/3)!` not a cube mod `N`).
    (Z6) negative controls: `n = 2` refused by name on the curve route; the averaging path at `n = 2`, `p ∈ {2,3}` refused; the default `CokernelHeckeMatrices`, `SparseCokernel::Build`,
    `CokernelPresentation::Build`, `ReadEisensteinR3` refused at `p ∈ {2, 3}` with their old texts; `dim W = 1` at `(11,2)`, `(19,2)`, `(43,2)`, `(13,3)`, `(31,3)`.
    **(LN23-F) the family certificate**: every (Z3)/(Z4)/(Z5)/(SMALLP) reading widens its family `q ≤ QMAX` along `13, 19, 31, 47, 71, 101, …, 997` (incremental `R3FamilyReader`,
    `HeckeLevelNR3`) until it contains a Mazur good prime (`MazurGoodPrime`: II.16 Def., case (b) excluded by (17.1); at odd `p`, `q = 2` is good iff not a `p`-th power), `dim W` and
    the layers are unchanged at the next two rungs and the layers read `d, d − 2, …, 1` (CERTIFIED; the signature clause, conditional on (LN6)'s faithfulness, was added after stabilisation
    alone falsely certified `(24473, 2)` at `q ≤ 13`, spec v0.3.1 §11.3), or `dim W = 1` (TRIVIAL); the CE / oracle checks compare the **certified** reading ("on the certified family q <= Q*
    (from q <= QMAX; W_F contains W_m; equality part of the prediction)"), the `q ≤ QMAX` reading is printed beside it. (FC) the certificate is reached (91 checks); (FC0) the reader
    equals `ReadEisensteinR3Scan` value for value on 6 cells, `MazurGoodPrime` on hand values; (G) at `(41,2)`, `(2137,2)`, `(2143,3)`, `(1747,3)` every good `q` alone reads `dim W_{q}` and
    Loewy `≥` the certified ones (14); (G2) at `(2473,2)` `η_2` generates although 2 is a quartic residue (Mazur's predicate is sufficient, not necessary, at `p = 2`, `q = 2`).
  - Lines: `LN23_CELL`, `LN23_Z1` (only on a failure), `LN23_Z1_SUMMARY`, `LN23_THM11` / `LN23_THM12I` (failures, cells not certified at `QMAX`, widened arms, `e_3 ≥ 2`), `LN23_THM11_SUMMARY`,
    `LN23_THM12I_SUMMARY` (with `agree_at_qmax=`, `certified_at_qmax=`), `LN23_SMALLP`, `LN23_GEN_CERT`, `LN23_GEN`, `LN23_GEN2`, `LN23_STURM`, `LN23_STURM_SUMMARY`; every cell line carries
    `good=`, `cert=<TRIVIAL|CERTIFIED|NONE>@<Q*>`, `cert_dimW=`, `cert_loewy=`, `cert_layers=`, `cert_first_good=`, `ladder=<Q>:<dimW>/<loewy>,…`. No golden line, no record.
  - **Read-only env arms** (each prints `EFFECTIVE HeckeLevelNCurveValidation arm=… cells=…`): `HECKE_LEVEL_N_R3_SMALLP_CELLS="N:p,…"` (replaces every arm; `N` prime `< 2^20`, `p ∈ {2,3}`,
    `p | num((N−1)/12)`, else refused by position; CE comparison where `exact`); `HECKE_LN23_Z1_NMAX` (2000: 377 levels, 0 torsion); `HECKE_LN23_THM11_NMAX` (`3·10^4`: see the report);
    `HECKE_LN23_THM12I_NMAX` (`10^4`: 133 / 133, 1.45 s / 151 MiB max per cell); `HECKE_LN23_QMAX` (default 13: the first rung of the certificate; see the env table); `HECKE_LN23_STURM=1` (arm=STURM, see the env table); the heavy interlock `HECKE_LN23_HEAVY=1` adds `(21929, 2)`: `dim W = 255`, Loewy 128 (CE `e_2 = 127`),
    10.6 s, 0.59 GiB at `ENGINE_THREADS=1` (LN23); with the certificate (CERTIFIED at 13) 34 s, 0.34 GiB for the cell, 1184 checks, 56 s (`ENGINE_THREADS=4`).


**Slot 22, WAKE-1 (the `Γ_H(N)` level and the tame family of Hsu–Pozzi–Wake–Wang-Erickson, arXiv:2610.03401v1; spec `docs/implementation/slot22/WAKE1_spec.md` v0.3; oracle `docs/implementation/slot22/wake/{msymb.py, wake_check.py, wake1_controls.py}`, never called).**
Roster **194 = 68 / 109 / 17** (`--all` 177; `EXPECT_NAMES` 194). Fragment `Registry/Slot22/WAKE1.cpp`, `cmake/slot22/WAKE1.cmake`.
- `HeckeTameFamilyValidation` — **`standard`**: ≈ 18 s, ≈ 0.19 GB, **138 checks** (default arms). Files: `Hecke/HeckeGammaH.{h,cpp}` (`GammaHLevelN : CosetLevel`, the table of the
  P10-C text's `prop:nebgammaH` (2) — `w_{(j,u)} = σ_u w_j`, `u` the least coset representatives of `G_N/H`; `PrimeToPart(N, p)`; `class_of_row` / `act`; `GammaHSubTransversal`;
  `GammaHDiamondOnModel`; the symbol operators `GammaHHeilbronn` (`Mer_n`, any `n`), `GammaHDiamond`; `QuotientCoords`; `CuspsOf`), `Hecke/HeckeTameFamily.{h,cpp}` (dense `F_p`
  algebra, localisation, `MatAlgebra`, `ReducibilityIdeal`, `RunTameCell` / `RunMParts`), `Hecke/HeckeTameFamilyValidation.{h,cpp}`. No existing file changed beyond the two one-line hooks.
  - Arms: (T) the table (action formula on `S`, `T`, `ST`; `H = G_N` = `Gamma0LevelN`'s table, `H = {1}` = `Gamma1LevelN`'s; `PrimeToPart` at WAKE and P10 levels; N2 `gammaH_minus_one`;
    the sub-transversal). (S) `H = G_N`, `N = 253`: `PresentationDigest`, `[T_2]`, `[U_11]`, `[U_23]` equal the shipped Heilbronn route entrywise; the `n = 2` blocks equal
    `HeilbronnOperator`'s at `N = 11`, `F_7`; `RelEscapes = 0` at `Γ_H(33)`, `n = 2`. (M) the model route at `Γ_H(33)`, `F_5` (`h = 41`): charpolys of `T_2`, `U_3`, `U_11`, `⟨2⟩`, a
    combination equal. (W) W-P1/2/3/5 and N1 on `Γ_0(11, 253, 737, 473, 2167)`, `±Γ_1(11)`. (H) the HPWWE cells `ℓ_1 = 23, 67` (`EFFECTIVE … arm=HPWWE cells=2`): W-P4, W-P4b,
    W-P6a/b, W-P7, W-P8, W-P8w, identities I4–I8, controls N3–N7 — every number against the frozen oracle (`ORACLE … cpp= py= agree=`); `ℓ_1 = 43` printed only (`INFO`).
  - Lines: `TABLE`, `MPART`, `TAME_CELL`, `ORACLE`, `INFO`, last `TAME_FAMILY checks=<k> failing=<f> verdict=OK|FAIL`. No golden line, no record.
  - **Read-only env arm** `HECKE_TAMEFAMILY_HEAVY=1` (`EFFECTIVE HeckeTameFamilyValidation arm=HEAVY cells=1`): adds `ℓ_1 = 263` (`Γ_0` rank 2; `Γ_H(2893)`: `m = 15840`, `h = 2641`,
    cusp / full 20 / 30, `dim A = 10`, all inside, `dim A/J^red = 2`, surjective — the oracle's W-P9 line) and `INFO ℓ_1 = 197`: 149 checks, 0 failing, **328 s, 1.56 GiB** (`263`: 209 s).
  - **(slot-22 WAKE-3) Read-only survey arm** `HECKE_TAME_FAMILY_CELLS="p:ℓ_0:ℓ_1,…"` (spec `docs/implementation/slot22/WAKE3_spec.md`, report `WAKE_survey_report.md`): a malformed item is
    refused by position (`REFUSED HeckeTameFamilyValidation cell #k '<item>': <reason>`, one failing check each); `EFFECTIVE HeckeTameFamilyValidation arm=CELLS cells=<k>`; per cell the
    preprint's hypotheses and the filters F0 `rk T°_{Γ_0(ℓ_0)} = 1`, F1 `rk T°_{Γ_0(N)} = 2` (`FILTER … pass=yes|no`; a failing cell is printed, not run), then `RunTameCell` with
    `TameCellSpec::lean` (no memo of full matrices; subspace reads; `A` = the algebra of every Frobenius `T_q`, `q < 200`, `T_p`, `U_ℓ`, `⟨u⟩`): one `SURVEY …` line and the
    gates V3-P1 … P9 (cusp / full `4p` / `6p`, `dim A = 2p`, full algebra `4p`, ordinary, diamonds, **case (ii)**); a case-(iii) reading prints `FINDING` (R-22a). At `(5, 11, 263)`
    the oracle's W-P9 fields (`ORACLE … agree=`). Faster `Mul` / `Rref` (row blocks, lazy reduction, the engine pool; value-neutral: the RREF is unique). Cost ≈ `0.15 GB + 20 h²`
    bytes, `≈ 57 s · (h/2641)³` per cell (`ENGINE_THREADS=4`); `(5, 11, 263)`: 44 s, 0.19 GB.

**Slot 22, P10 (the real Hida tower, `Γ_{H_r}(ℓ^r)` with the tame character; P10 (a) the wild character models; spec `docs/implementation/slot22/P10_spec.md` v0.3 — §15 the implementation predictions, committed before the first run; text [C] v1.22.0-pre.1 `sec:nebwildsec`, [U] 0.6.0-pre.1 `sec:u-tower`, refereed F-U5).**
Roster **196 = 68 / 111 / 17** (`--all` 179; `EXPECT_NAMES` 196). Fragment `Registry/Slot22/P10.cpp`, `cmake/slot22/P10.cmake`. WAKE-1's `Hecke/HeckeGammaH` is reused, not edited.
- `HeckeLambdaTowerValidation` — **`standard`**: ≈ 80–100 s with 8 threads (`ENGINE_THREADS`), ≈ 0.73 GB, **610 checks**, 0 failing. Files: `Hecke/HeckeGammaHTower.{h,cpp}` (`ZK`, `TameCharacterTable`,
  `MonomialChiOf` (`χ(a_{h_J(γ)})` on `GammaHLevelN`), `RelGeneratorsChi` (norms of order 2 / 3, or 4 / 6 when `−1 ∉ H`), `ChainCokernel` (lem:nebchainrref: sparse Gauss–Jordan over `Z/ℓ^K`
  with unit pivots; `chainring_pivot`, `tower_rss_cap`; torsion kept on request), `ChiHeilbronn` (prop:nebgammaHheilbronn, `χ(d_h)`, `d_h ∈ H` asserted), `ChiDiamond` (`R_{σ_d}`, `χ(a_R)`),
  `OnQuotient`, `RelEscapesChi`, `HowellZK`), `HeckeExt/HeckeLambdaTower.{h,cpp}` (`BuildTower`: the certified block Krylov ordinary part, the split by `T_2`'s residual Eisenstein value,
  the `Λ_r = (Z/ℓ^K)[G_r]`-bases and scalars, `Weierstrass`, `FibreAt`, `ReduceTo`, `EisensteinScalar`; `BuildGamma1Oracle`; `TowerRecordLines`), `HeckeExt/HeckeLambdaTowerValidation.{h,cpp}`.
  - Gates: **G0** first (prop:u-towerorient on the project code, the 8 `r = 1` cells of spec §7.2; a failure stops the validation), G1 (`m`, the `r = 1` table = def:cosetrepsN), G2 (`h` of §7.1;
    the chain-ring pivots and tails = the `F_ℓ` RREF of `SparseCokernel`), G3 (`Rel` preserved by `T_p` (`p ≤ 29`), `U`, `⟨g⟩`, `⟨p⟩`, `⟨h⟩`; commutation; `⟨p⟩ = ⟨g⟩^{s(p)}`, `⟨h⟩ = 1`),
    G4 (NB10: `Γ_1(ℓ^r)`, `r ≤ 2`, `tr e_χ = h`, ordinary rank, charpolys of `T_2`, `T_3`, `U`), G5 (Krylov certificate, rank `ℓ^{r−1}(2d+1)`), G5′ (`r ≤ 2`: `e = U^T` on the whole module,
    equal canonical bases), G6–G9 (`Λ_r`-bases, cusp scalars, (BF′), `T_p = 1 + p ω^{a−2}(p) g^{s(p)}`, `U = 1` on `M^Eis`), G10 (`r → r'`), G11 (weight fibres against WP-HL's forms side and
    11a), G12 (§7.3 first-order coefficients), G13 (P7's truncations `(3, m ≤ 3)` in `Q`, lengths §7.4), G14 ((U21)), negative controls of §5 (`NEG … caught`).
  - Cells: `ℓ ∈ {5, 7}` every even class `r ≤ 3`; `(11, 2)`, `(11, 4)`, `(13, 0)`, `(13, 4)` at `r ≤ 2` (`EFFECTIVE HeckeLambdaTowerValidation arm=DEFAULT cells=23`).
  - **G11 at `ℓ = 13` re-targeted after the first run (spec v0.4 erratum E1, approved by the lead):** the spec's weight 158 is not in class 0 (`158 ≡ 2 mod 12`, `e S_158 = 0`: the
    first run failed 1 of 600 checks there); now `k = 132` (`v_13(130) = 1`), predicted from the forms side before the re-run (`p10c/p10_k132_predict.py`: `a_2 = 1159`, `U = 944` mod `13^3`, …),
    met; the gate's statement is unchanged.
  - Lines: `ORIENT`, `CELL`, `BF'`, `TOWER`, `FORMS`, `FIBRE(S)`, `FIRST_ORDER`, `GENERATE`, `P7`, `GAMMA1`, `NB10`, `NEG`, the record `HECKE_LAMBDA_TOWER ell= a= r= K= component= …
    digest=0x…` (`hecke_lambda_tower/v1`, not pinned), last `HECKE_LAMBDA_TOWER checks= failing= … verdict=`. No golden line.
  - **Read-only arms**: `HECKE_LAMBDA_TOWER_R3=1` (`(11, 2, 3)`, `(13, 0, 3)`; bytes and Krylov work predicted from the measured `r = 2` fill **before** allocation, printed in
    `EFFECTIVE … arm=R3 cell=… predicted_bytes= predicted_krylov_ops=`; refused `tower_rss_cap` above `HECKE_LAMBDA_TOWER_RSS_CAP_GIB` (default 4) and `tower_cost_cap` above
    `HECKE_LAMBDA_TOWER_OPS_CAP` (default `10^12`), counted, not failures: at P10 both cells are refused (33.5 GB / 1.5·10¹⁴ and 86 GB / 6.4·10¹⁴); `HECKE_LAMBDA_TOWER_CELLS="ℓ:a:r[:K],…"`
    replaces the list (`ℓ > 13` refused `tower_edge_not_built`).
- `HeckeNebentypusWildValidation` — **`standard`**: ≈ 3.5 s, ≈ 47 MB, **70 checks**. Files: `Hecke/HeckeNebentypusWild.{h,cpp}` (`WildRing` = `O_{j,Kφ_j}` on the power basis,
  `WildCharacter` `χ_{i,t}`, `WildModel` (the `Γ_0(ℓ^r)` character model expanded over `Z/ℓ^K`, the torsion kept), `SpanLength`; refusals `wild_precision`, `wild_ring_order`,
  `wild_tame_level`), `HeckeExt/HeckeNebentypusWildValidation.{h,cpp}`. W1 (NB7: `χ_{i,t} ≡ ω^i mod π`; `dim_{F_ℓ} H^1 = EC + [i = 0]`), W2 (NB8: lengths of `H^1`, `H^0` of §7.5; a non-unit
  Howell pivot exactly at `i = 0`), W3 (NB9 / U20: `e H^1` of length `e(2d+1)`, free where torsion-free; `T_p` (`p = 2, 3, 5, 7`), `U` on it annihilated by the tower's `a_p`, `α`, `ε` at
  `g ↦ ζ`, `ε_p(ζ) = 1 + p χ_{i,t}(p)`), W4 (`character_wild` over `F_q` unchanged; the three new refusals fire). Cells: `O_{1,3(ℓ−1)}` at `r = 2`, `ℓ ∈ {5, 7, 11, 13}`; `O_{2,40}` at
  `(5, 3)`. Read-only `HECKE_NEB_WILD_ALL=1` adds `O_{2,42}` at `(7, 3)` (not run at P10: the dense `e` at `h ≈ 2.8·10³` is ≈ 2.6·10¹¹ operations).

**Slot 22, NF-PRANK (the `p`-rank of `Cl(Q(N^{1/p}))`, `p = 5` first; spec `docs/implementation/slot22/NF-PRANK_spec.md` §8; predictions `NF-PRANK_predictions.md`, committed before the first run; oracle the frozen prototype `docs/implementation/slot22/nfprank/{pure_quintic_rank.py, pure_quintic_hR.py, chevalley.py}` → `hR_runs.out`, `chevalley_cells.tsv`; report `NF-PRANK_report.md`).**
Roster **197 = 68 / 112 / 17** (`--all` 180). Fragment `Registry/Slot22/NFPRANK.cpp`, `cmake/slot22/NFPRANK.cmake`; library sources in the `NumberField` block of `CMakeLists.txt` (slot-21 T1 / T2 precedent).
- `NumberFieldPRankValidation` — **`standard`**: ≈ 5 s, ≈ 53 MB (`ENGINE_THREADS=1`; single-threaded), **106 checks**. Files: `NumberField/PureField.{h,cpp}` (`F_q` polynomials, distinct-degree +
  Cantor–Zassenhaus factorisation, the multiplicity factorisation of a non-squarefree `f mod q`, Dedekind's criterion, Round 2 (`p`-radical, ring of multipliers), `pure_field`, the factor base,
  valuations incl. the `P_1 P_2^{p−1}` shape at `p` when `p^2 | N − 1` via the `p`-adic root), `NumberField/Ambiguous.{h,cpp}` (Chevalley: `t`, `λ`-ramified, `r*`, exponent, non-norm characters),
  `NumberField/ClassGroupRel.{h,cpp}` (`nf_prank`: line sieve, 3-term box, `(q)` relations, strict descent above `B_0` (2-d lattice / 3-d LLL / `(q)`), lattice-element rows for weakly covered ideals,
  `±1`-pivot sparse elimination carrying log vectors and local `p`-th-power characters instead of histories, BigInt Smith form, the found regulator `R'`, the `p ∤ [E:E']` certificate, the truncated
  Euler product; Miller–Rabin + Pollard–Brent on 64 bits), `NumberField/PRankValidation.{h,cpp}`. STL only (`check_numberfield_includes.sh`); passes with `-DNF_NO_INT128`.
  - Gates: **G1** field data at `(11,5) (31,5) (41,5) (61,5)` = prototype (`d_K`, signature, `M_K`, Dedekind); Round 2 at `(401,5)`: index 5, `d_K = 5^3·401^4`, `5 O_K = P_1 P_2^4`, the 5-adic root;
    primitives on fixed inputs. **G2** Chevalley on all 1240 cells of `chevalley_cells.tsv` (sha256 `3d6f6903…` checked): 0 differences. **G3** the four prototype cells field by field
    (`NF_PRANK_AGREE … proto= cpp= ok`: factor base, degree-≥ 2 ideals, `Z^S/Rel`, `rank_upper`, `rank_lower`, genus, `5 ∤ [E:E']`, `R'`, `Res`, `hR`, `hR/R'` within 1 %, level); `(61,5)` with
    `B_0 = 3000` (1136 ideals descended) gives the same `[5]`; `(101,5)` (`25 | N − 1`) internal consistency. **G4** (a) an ideal removed → REFUSED "not Minkowski-complete"; (b) a corrupted valuation →
    genus REFUSED; (c) `Z[α]` forced at `(401,5)` → REFUSED "not 5-maximal"; (d) `p = 37, 59, 67` → REFUSED "p divides h_F"; (e) `X = 500` moves `hR/R'` to 24.745 (margin 0.155; the truncation error is not monotone in X).
  - Levels (spec §4.6): `CERTIFIED_EXACT` (`rank_upper = rank_lower = 1`), `UPPER_CERTIFIED_LOWER_ANALYTIC` (the upper bound certified, the decision analytic), `REFUSED` (by name); `GRH` not built.
    Note: `hR/R'` is `h / [E:E']` (`R' = [E:E'] R`); the spec's field name `h_times_index` is kept.
  - Lines: `NF_PRANK_ROUND2`, `NF_PRANK_CHEVALLEY`, `NF_PRANK_CELL N= p= dK= … group_bound= rank_upper= rank_lower= … level=`, `NF_PRANK_AGREE`, `CE_VERDICT`, `CE_FINDING` (never seen), last
    `NF_PRANK_SUMMARY checks= failing= secs=`. No golden line, no record.
  - **Read-only env arms** (each prints `EFFECTIVE NumberFieldPRankValidation arm=<X> cells=<k> dense_bound=<B_0>`): `NF_PRANK_CE=CE1,CE2,CE1C,CE2C` or `all` (the CE set of spec §8: CE1 9 cells, CE2 3 cells
    with the prediction `rank_upper ≥ 2` checked, a `rank_upper ≤ 1` printed as `CE_FINDING` (R-22a); controls CE1C 17, CE2C 4 cells unchecked in rank), `NF_PRANK_CELLS="N:p,…"`, `NF_PRANK_DENSE=<B_0>`
    (default 20000). All four arms at NF-PRANK: 152 checks, 0 failing, 77 s, 0.10 GB; largest cell `(761,5)` (`M_K = 2.0·10^6`, 150 352 ideals, 148 030 descended) 6.1 s.

**Slot 22, P6 (the Birch route on `Γ_0(N)` by Shapiro; the tame twists of the measure; spec + predictions `docs/implementation/slot22/P6_spec.md`, committed before the first run; oracle `docs/implementation/slot22/p6/p6_oracle.py` → `p6/P6_oracle.out`, frozen in the validation; report `P6_report.md`).**
Roster **198 = 68 / 113 / 17** (`--all` 181). Fragment `Registry/Slot22/P6.cpp`, `cmake/slot22/P6.cmake`.
- `HeckeLValueShapiroValidation` — **`standard`**: ≈ 0.1 s, ≈ 25 MB, **296 checks**. Files: `HeckeExt/LValue/Gamma0NShapiro.{h,cpp}` (`P1N` — `P^1(Z/N)`, canonical
  representatives, `SL_2(Z)` lifts, the `S`/`U`/`ι` actions; `RunGamma0NCell` — `W(Ind V)^{±}` over `Z/ℓ^m` with the `S`-orbit elimination, `U`- and `ι`-relations once per orbit, Smith;
  `PhiOoTo`/`PhiCuspN`/`PhiPairN` (Manin with cosets), `HeckeTpN` (`p ∤ N`), `IotaN`, `ResFromLevelOne`/`CoresToLevelOne`, `EvAllJN`, `EigenvalueN`, `EigenSubmodule`, `BuildMeasureN`
  (the level-`N` MTT measure as `ModularSymbolMeasure`), `TameMeasure` / `BuildTameMeasure` (balls `b + Tℓ^m`, `γ = [[Tℓ^m, −b],[0,1]]`), `TameMomentIdentity`, `TameCharacter`, the
  Eichler–Shimura `DimCuspFormsGamma0`/`CuspsGamma0`, `EtaProductCoefficient`), `HeckeExt/LValue/HeckeLValueShapiroValidation.{h,cpp}`; the route (`BirchModularSymbolRoute`,
  `LValueRoute.h`, `BirchModularSymbol.cpp`, `ModularSymbolMeasure.cpp`) now accepts `ModelId::Gamma0NShapiro` (the slot-19 `RequireSupportedDomain` refusal lifted; `shapiro_cell()`,
  `symbol`, `evaluate_all_j`, `measure` at level `N`; `cell()` and `index_statement()` refuse there).
  - Arms: **S0** the route (accepts `Gamma0NShapiro`; still refused: Moerdijk–Pronk, the character model, 7-vertex at `N > 1`, `gcd(M, N) > 1`, odd `n`, `ℓ < 5`, `ℓ | N` in `measure()`, level-`N`
    `index_statement` / `cell()`); **S1** ranks of `W_N^±` (free) at `N ∈ {2,3,5,7,11}` × `n ∈ {0,…,12}` and `N ∈ {4,6}` × `n ≤ 4`, `ℓ = 13^3` and `F_7` = the oracle's D table and
    Eichler–Shimura (`W^- = s_k`, `W^+ = s_k + c`, `c − 1` at `k = 2`); the `ℓ = 7`, `k = 14` jump (`W^- = s_k + 1`) at exactly four cells; **S2** `Res(W_1) ⊂ W_N`, `Cores∘Res = N + 1`,
    `T_p` commutes with both, `HeckeTpN` at `N = 1` = `HeckeTp`, and `W_1` (Shapiro) = the span of the slot-19 cone symbols `Ψ(H^1_c)` at `m = 1, 3`; **S3** the newform lines
    `(2,8) (3,6) (5,4) (7,4) (11,2)`: `a_p` = the oracle = the η products `η(z)^r η(Nz)^r` (`N ≠ 7`), fnv of the normalised symbol; **S4** 11a = P9's `Gamma0Weight2Symbol` up to a unit
    (`ℓ ∈ {5,7,11,13}`, both signs), `Φ({a/M,∞}) = −u·AtCusp` (`M ≤ 40`), P9's `MultiplicativeMeasure` at `ℓ = 11`; **S5** the level-`N` measure at seven cells (three-term, distribution,
    moment identity, fnv; `BuildMeasureN` = the tame builder at `T = 1`; the route's `measure()` / `evaluate_all_j` at level 11); **S6** the tame twists of Δ's measure at `ℓ = 13`,
    `T ∈ {2,3,5,7,11}`: distribution, three-term, the moment identity with `E = α^{−1}` (`i ≢ 0`) and `(1 − χ̄(ℓ)ℓ^j/α)(1 − χ(ℓ)ℓ^{n−j}/α)` (`i ≡ 0`), 0 / 55 at every `(T, d)`;
    `T = 1` = `BuildMeasure` table by table; **S7** negative controls (no permutation in the coset map, `ρ(α)` for `ρ(adj α)`, no `ℓ^{k−2}`, `α(1+ℓ)`, `χ ↔ χ̄` in `E` — caught at
    `T = 5`; vacuous at `T = 7` since `13 ≡ −1 mod 7` makes `χ(13)` real, checked as such).
  - Lines: `SHAPIRO_ROUTE`, `SHAPIRO_RANKS`, `SHAPIRO_RESCORES`, `SHAPIRO_NEWFORM`, `SHAPIRO_P9`, `SHAPIRO_MEAS`, `SHAPIRO_TAME`, `SHAPIRO_NEG`, `SHAPIRO_CELL`, last `P6_ARMS checks= failing= secs=
    peak_rss_gb=`. No golden line, no record, no digest.
  - **Read-only arm** `HECKE_SHAPIRO_CELLS="N:n:ell:m,…"` (**S8**; `EFFECTIVE HeckeLValueShapiroValidation arm=CELLS cells=<k>`; malformed cells refused by position): ranks vs
    Eichler–Shimura (not gated where `n + 1 ≥ ℓ`) and the cost of the reduced system. At P6: `(101,20,23^3)` 4.8 s, `(211,10,13^3)` 2.6 s, `(37,100,211^2)` 44 s, `(11,200,401)` 20 s,
    `(1,400,409^2)` 0.3 s, all ranks = Eichler–Shimura, peak 0.23 GB (dense Smith, cubic in `|P^1|(n+1)/2`).

**Slot 22, LES-1 (the fibre maps of the level-change cone; [C] v1.22.0-pre.3 `sec:nebles`, item (LES1) of `rmk:lescheckable`; spec `docs/implementation/slot22/LES0_spec.md` v0.1, predictions `LES_predictions.md` §1 and `LES1_predictions.md`, committed before the first run; report `LES1_report.md`).**
Roster **199 = 68 / 114 / 17** (`--all` 182). Fragment `Registry/Slot22/LES1.cpp`, `cmake/slot22/LES1.cmake`.
- `HeckeLevelNormalityValidation` — **`standard`** (audit R1; Q13: fast < 0.5 s): ≈ 6.4 s at load ≈ 21 (≈ 4.6 s of it arm F), ≈ 90 MB, **3748 checks** (3618 + 130 after audit R2, R4, R5; 4.1 s idle). Files: `Hecke/HeckeLevelPair.{h,cpp}` (`CongruenceLevel(M, K)` —
  the preimage of `K ≤ SL_2(Z/M)`, `Principal(M)` = `Γ(M)`, `Commutator(M)` = `Γ²`, `Γ³`; `CosetPermutation`, `TorsionContent`, `ModelTagOf` (prop:modeltorsion);
  `QuotientOf` — containment by the equivariance of the fibre, normality by `Γ`-set automorphisms, the multiplication table of `A/B`; `IntersectionIndex`;
  `CharacterDatum`, `TwistedMonomialMatrix` (eq:MHchi on any `CosetLevel`); `RestrictionFibreMap` (`α`, the trace `ω`, eq:levelres; refusals `les_not_contained`,
  `les_character_level`, `les_incompatible_character`); `ConjugationFibreMap` (`R_σ`, def:normalpair; refusal `les_not_normal`); `FibreMatrix`; `RhoBlocks`),
  `Hecke/HeckeLevelNormalityValidation.{h,cpp}`.
  - Arms: **N1** prop:gamma0normal on `N ≤ 60`, `2 ≤ M ≤ 24` (1380 pairs, 89 normal, the `a c / N mod M` isomorphism); **N2** the `Γ_1` statements of prop:hidanormalsteps
    (60 pairs × 3); **N3** the `p`-tower table, `p ∈ {5,7}` (rows 5–8 to `r = 3` at 5, `r = 2` at 7); **N4** `Γ²`, `Γ³`, `[Γ : Γ² ∩ Γ³] = 6`, `Γ(M)` (`M ≤ 7`);
    **N5** the model tags, the order-3 criterion on `Γ_0(N)`, 25 torsion-free groups; **L** `RestrictionFibreMap` = `LevelChangeMap` (52 cells, 0 differing), the twisted
    monomial matrices = `MonomialOf` / P10's `MonomialChiOf` (60 cells); **F** obl:levelconeexact (i) at the 201 cells of `LES_predictions.md` §§2–3 (127 normal; `α ω = Nm_G`
    gated where `m_B [A:B] (n+1)³ ≤ 6·10⁷`, skipped at `Γ(7)`, ℓ = 7, n = 8 only); **NEG** res_wrong_scalar (vacuous at `Γ_0(25) ⊂ Γ_0(5)`, where every `a_{h_i} ≡ 1`
    mod 5 on the shipped tables — recorded; gated at `Γ_1(5) ⊂ Γ_0(5)`), res_no_block, incompatible_chi, sigma_not_normalising (refusal + the unchecked formula), not_contained,
    character_level.
  - Lines: `GAMMA0_NORMAL`, `normal pairs (N: M list)` (identical to `les0/out_predict.txt`), `GAMMA1_STEPS`, `TOWER`, `LEVEL1`, `MODEL_TAG`, `LEVELCHANGE_ORACLE`, `MONOMIAL_ORACLE`,
    `FIBRE_IDENTITIES`, `slowest cell`, `NEG`, `ARM <name> wall=`, last `LEVEL_NORMALITY checks= failing= verdict=`. No env hook, no golden line, no record.

**Slot 22, G-EVT (the golden event R1, add-only, predicate-gated; plan §3 G-EVT / §5, owner decisions 2026-10-06; referee F2g ACCEPT WITH REPAIRS).**
- `GoldenRegressionValidation` — **18 117** objects, tier A **11 886** / 0, tier B **6231** / 0 (slot-22 G-EVT R1: **59** entries, 59 A + 0 B, 0 changed,
  0 removed; `docs/matrix-engine/rebaseline-2026-10-09-addonly-lvalue-hidapair.md`, ledger `docs/implementation/slot22/golden_ledger.md`): at the NEW points
  `LVALUE n=<n> ell=<ell>` (7: G1 `eis_index_m{1,2,3}` / `eis_module_c`, G2 `xkind_{congruence,bilinear,linear,bernoulli}`, G7 `cf_{plus,minus}_<block>`)
  and `HIDAPAIR k=<k> ell=<ell>` (27: G4 `pairing_valuations`). Reached from `ComputeAll()` only, so `GoldenSubset32`, the ext records and C4 (a) are
  untouched (all digests unchanged); the new points cost ≈ 2.8 s of the golden run on a quiet box (≈ 4.5 s at load ≈ 20), paid twice in `--all`
  (the regression and ConsoleDet arm (c)); RSS ≈ 0.5 GB.

**Slot 22, MP-1a (the Moerdijk–Pronk route: orbifold triangulations as data, the decidable MP predicates, the choice-free MP set to `k = 3`; plan
`docs/implementation/slot22/MP_impl_plan.md` v0.2 §2.2 / §2.6, math plan `MP_math_plan.md` v0.2 Defs. 1.3–1.5, §3.1; predictions `MP_predictions.md` P1, committed and
countersigned (`c529179d`) before the first run; report `MP1a_report.md`).**
Roster **200 = 69 / 114 / 17** (`--all` 183; the LES-1 line above reads 69 / 113, the binary before MP-1a listed 68 / 114 / 17). Fragment `Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`
(MP-1b adds its name to the same pair).
- `OrbifoldMPRulesValidation` — **`fast`**: ≈ 0.7 s, ≈ 85 MB, **77 checks**. Files: `Orbifold/MP/Descriptor.{h,cpp}` (`Descriptor` read off `integral_model::ModelData` —
  vertex orbits, every `K'` label as a point `g·ι(orbit)` with key = least `GKey` of `g Γ_orbit`, `Σ_top`; `RGoodDescriptor()` = `mp_rules.py`'s `R_good` table; `Arrows` (vertex
  transporters), `SimplexOrbitKey`; predicates `Adapted(D, ℓ, subgroup_form)` (`ℓ = 0` full, else the Sylow datum; generator membership), `AdaptedFace` (plantable),
  `Good` (finite-group criterion, closure declared infinite above 6 elements, the stronger `T(v) ⊆ Γ_p` beside it), `Collar`, `SimplicialComplexProperty`, `InvariantOrder`,
  `OrbitOrdered` (refuses two vertices in one orbit), `Quotient` `(V,E,F,χ)`, `OrderedChainSignBridge` (orbit-ordered simplicial signs = `IsotropyModel::faces`)),
  `Orbifold/MP/MPSet.{h,cpp}` (`MPSet(D, k_max)`: the strings of [MP] Def. 1.5 by extension + the common-vertex test, `face(s, i)`, `degenerate`, `member` (forward-intersection
  re-test); `MuFormCount`), `Orbifold/MP/OrbifoldMPRulesValidation.{h,cpp}`.
  - Triangulations: `M7`; `R_Z` = `SubdivideEdgeOrbit(M7, arc)`, the arc found from the inventory (ends of stabiliser order 6 and 4); `R_ζ` (the three edges at `ζ²`, slot 17);
    `R_Z⁺` (`R_Z` + the three edge orbits horocycle–`ρ`, iterated; = `mp_rules.py`'s after relabelling midpoints 10, 11, 12 → 12, 10, 11); `R_good` (table).
  - Gates (P1): `|S_0..S_3|^nd` 5/127/2541/53143 (`M7`), 7/165/2927/56349 (`R_Z`); all-strings `|S_1|,|S_2|` 172/3264 = `μ`-form on `R_Z`, 132/2800 vs 124/2704 on `M7`;
    `(V,E,F,χ)`; adapted for `𝒯^{(3)}`, `𝒯^{(2)}`, full; good; collar; `good_fails_at`; (SC) and the invariant order on all five; the sign bridge on the four `ModelData` ones;
    `S_{≤3}` on `M7`, `R_Z`, `R_ζ`: unique strings, forward re-test, faces closed, `d_i d_j = d_{j−1} d_i`; subgroup-form = order-only and finite-group good = strong good on
    the four candidates; **NC1** order-only accepts `{⟨ST⟩, T⟨(ST)²⟩T⁻¹}` and R_Z with a planted `v0` stabiliser `T²⟨ST⟩T⁻²`, the subgroup form rejects both; **NC2** `v0 v3 v4`
    refused. `R_ζ` (P1.12) is OUTPUT: `(8, 18, 11, 1)`, adapted at 3 / 2 / full, not good (fails at 2, 9, 10), `|S_0..S_3|^nd` 11/267/4379/75099.
  - Lines: `MP_RULES model=mp tri=… ` (the 12 `mp_rules.py` rows, same format), `ORACLE mp_rules.py cells=12 agree=12`, `MP_SET`, `MP_MUFORM`,
    `ORACLE adapted_form_check.py cells=6 agree=6`, `OUTPUT P1.12`, `NC1 planted:`, last `ORBIFOLD_MP OrbifoldMPRulesValidation checks= failing= wall_s=`.
    No golden line, no record, no setting.
  - **Scratch emitter** `ORBIFOLD_MP_DUMP=<dir>` (pattern `HECKE_DUMP_TAU`): unset = no-op; `<dir>` must exist and lie **outside** the source tree, else `REFUSED` and the
    validation fails (exit 1). Writes `mp_rz_orbits.tsv`, `mp_rz_points.tsv`, `mp_rz_top.tsv`, `mp_rz_arrows.tsv`, `mp_predicates.tsv`, `mp_rz_sk.tsv` (`|S_0..S_2|`) for the
    Lean cross-checks of plan §3.3 and prints `EFFECTIVE OrbifoldMPRulesValidation arm=dump dir=<real dir> files=6 fnv=0x<FNV-1a-64 over names + bodies>`
    (at MP-1a: `fnv=0x24ca42ad1b6a4fa0`). Values unchanged by the hook.

**Slot 22, MP-1b (the Moerdijk–Pronk route: the interned MP set, its twisted normalised cochains and the nerve cohomology `H^{≤2}`; plan
`MP_impl_plan.md` v0.2 §2.3 / §2.6, math plan `MP_math_plan.md` v0.2 Def. 1.5, Thm 2.1, §5; review R1, R3, R5; predictions `MP_predictions.md` P2
(countersigned) + the appended R3 measurement; report `MP1b_report.md`).**
Roster **201 = 69 / 115 / 17** (`--all` 184). Same fragment pair `Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`.
- `OrbifoldMPNerveValidation` — **`standard`**: ≈ 6.6 s, ≈ 260 MB, **580 checks** (592 with the arm). Files: `Orbifold/MP/Nerve.{h,cpp}` (`InternedMPSet(D, k_max)`: the
  strings of [MP] Def. 1.5 with 32-bit indices into the interned transporter union `U` (20 elements on `M7` and `R_Z`) and its partial multiplication table; level keys
  `(parent·F + σ)·|U| + γ` increasing, so `find` is `k` binary searches; per-string cumulative product + vertex mask (the common-vertex test in O(1)); `face`, `degenerate`,
  `nd`; `Coboundary(S, k, n, m, twisted)` = `d^k` over `Z/m` as CSR, `(df)(s) = ρ_n(γ_1) f(d_0 s) + Σ_{i≥1} (−1)^i f(d_i s)` with `integral_model::rho_n`, `f := 0` on
  degenerate faces; `ProductIsZero`; `FormalDSquared` (`d∘d = 0` in `Z[U] ⊗ Z[S_q^nd]`, every string)), `Orbifold/MP/SparseLength.{h,cpp}` (`RowSpanLength`: unit-pivot sparse
  elimination over `Z/ℓ^e`, residual rows by the dense Howell `engine::elim::length`; `RowOrder::Reversed` default — R3: 100× less work than the natural order),
  `Orbifold/MP/AmalgamOracle.{h,cpp}` (C++ port of `mv_check.py` (1); `MvCheckOracle()` = `MvCheckOracle.inc`, the frozen `mv_check.out` (1) transcribed by `sed`),
  `Orbifold/MP/OrbifoldMPNerveValidation.{h,cpp}`.
  - Gates (P2): nerve `H^0, H^1` over `F_ℓ`, `ℓ ∈ {2,3,5,7}`, `n = 0..12`, `M7` and `R_Z` (104 cells); `H^2`, `ℓ ∈ {2,3,5}`, `n ≤ 3` (24 cells; `n ∈ {4, 6}` behind
    `ORBIFOLD_MP_CELLS`); `Z/ℓ^k` lengths `H^0, H^1`, `ℓ ∈ {2,3}`, `k ≤ 3`, `n ∈ {0,1,2,4}` (48 cells) and `n = 0`, `q = 2` (12); `C_I` integral `H^0..H^3` for
    `n ∈ {0,1,2,4}` (`IntegralGroups`, certified at 2, 3) and every nerve length = its UCT prediction (`PredictedLengths`); `d∘d = 0` formally through degree 4 and on every
    cell's matrices; odd `n` with `2 ∈ R^×`: 36 non-zero acyclic cells; NC untwisted `d_0` (`F_2`, `n = 2`: `H^0, H^1 = 3, 3`, fires on both); interned `S_{≤3}` = `MPSet`'s
    string for string; `S_4` faces and simplicial identities exhaustive; `.inc` = the tracked `mv_check.out`; `AmalgamOracle == .inc` (416 values, its own check); `RowSpanLength`
    = dense length on 96 pseudo-random matrices (residual path exercised). OUTPUT: `|S_4^nd|` 1 166 229 (`M7`), 1 190 807 (`R_Z`).
  - Lines: `MP_NERVE_SET`, `OUTPUT P5`, `SPARSE_LENGTH self-test:`, `AMALGAM_ORACLE AmalgamOracle == mv_check.inc rows=52 values=416 agree=416`, `NERVE_H2` (per cell, with the
    `d^2` fill), `NERVE model=mp tri=… ring=F_ℓ (H^0,H^1) n=0..12: …`, `ORACLE mv_check.out cells=128 agree=128` (140 armed), `INTEGRAL model=C_I`, `NERVE_ZLK_H2`, `NERVE_ZLK`,
    `ZLK summary:`, `NC P2.6b`, last `ORBIFOLD_MP OrbifoldMPNerveValidation checks= failing= wall_s=`. No golden line, no record, no setting.
  - Hook `ORBIFOLD_MP_CELLS` (read-only; `EFFECTIVE OrbifoldMPNerveValidation arm=h2 cells=12 n=4,6`), see the env table. The arm also accepts the aliases `h2n4` (= `4`) and `h2n6` (= `6`) in the same comma-separated list, and `all` (= `4,6`); any other token is `REFUSED`.

**Slot 22, MP-T (MP's teardrop `Tear-n` in the `G^k`-form of `S(𝒯)`; plan `MP_impl_plan.md` v0.2 §2.6, math plan `MP_math_plan.md` v0.2 §6, predictions
`MP_predictions.md` P3 + its appended MP-T deviation note; report `MPT_report.md`).** Roster **202 = 70 / 115 / 17** (`--all` 185). Same fragment pair
`Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`.
- `OrbifoldMPTeardropValidation` — **`fast`**: ≈ 0.3 s, ≈ 23 MB, **66 checks** (63 + the audit's NC4). Files: `Orbifold/MP/OrbifoldMPTeardropValidation.{h,cpp}` (the C++ port of
  `docs/implementation/slot22/mp/teardrop.py`; reuses `SparseLength` (`RowSpanLength`, `e = 1`)). Gates (P3): 9 cells `n ∈ {2,3,4}` × `ℓ ∈ {2,3,5}`, `dim H^0..H^3` =
  `1, 0, 1, [ℓ | n]` and `|S_0..S_4|` = 6,39,177,705,2877 / 6,48,294,1866,13290 / 6,57,465,4323,44925 (81 values); `d∘d = 0` exhaustively on every
  non-degenerate string of `S_2..S_4` (3759 / 15450 / 49713). NC1 `μ_ac = μ_ca = ρ` and NC2 `μ` from order `n+1` break `d∘d = 0` (44 strings each); NC1b the swapped
  `μ` does **not** (it is the `g ↦ g^{-1}` twin: `d∘d = 0`, same dims; `d² = 0` iff `μ_ac + μ_ca ≡ 0 mod n`); NC3 `n = 1`, `ℓ = 2`: `H^3 = 0`; NC4 (Opus audit) trivial `μ` keeps
  `d∘d = 0` but fails the dims gate (`1, 1, 2, 1`), `n = 2, 3, 4`.
  Lines: `ORACLE teardrop.py cells=9 agree=9`, last `ORBIFOLD_MP OrbifoldMPTeardropValidation checks= failing= wall_s= model=mp`. No golden line, no hook, no setting.

**Slot 22, MP-2 (the Moerdijk–Pronk route: the comparison maps to the shipped models, the Bredon map `ε^*`, the refinement map `R_Z → M7`, the
"all degrees" certificate; plan `MP_impl_plan.md` v0.2 §2.4 / §2.6, math plan `MP_math_plan.md` v0.2 Thm 2.1 (Step 3, via `F'`), Thm 2.6, §7; review
R1, R2, R5; predictions `MP_predictions.md` P4 + the "MP-2 predictions" addendum, committed before the first run; F-MP1 repairs F1–F4, F6; report
`MP2_report.md`).** Roster **206 = 70 / 118 / 18** (`--all` 188). Same fragment pair `Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`. New library files:
`Orbifold/MP/Comparison.{h,cpp}` (`PhiLift`: `Φ: Z[F'_•]^N → Iso_•` generator by generator, `Φ_0(e_s) = h·e_{0,v,0}` at the first vertex of `ι(s)` in an orbit of the
target, `Φ_k(e_s) = fill(Φ_{k−1}(d e_s))` with `PeriodicityClass::fill` (the target is the shipped 7-vertex `Iso_•` for both triangulations); `certify()` re-derives
`dΦ = Φd` over `Z[Γ]` and `aug ∘ Φ_0 = aug` from the stored values; `Pullback(q, n, ℓ, e)` = `Φ^*_q` as CSR; `perturb_for_negative_control`), `Orbifold/MP/Refinement.{h,cpp}`
(`LabelsFromRecord` (the subdivision record, least-`GKey` label of `h_0 Γ_σ`), `ContainedIn` (decidable `ι̃(σ̃) ⊆ hι(σ)`), `MapStrings`, `RefinementPullback` with the
twist `ρ(h_{σ̃_0})` — the plan's one-line formula omits it; it is load-bearing for mixed labels at odd `n`), `Orbifold/MP/CochainMaps.{h,cpp}` (iso-on-cohomology certificate:
image length of `H^q(A)` in `H^q(B)` = `len(B^q + φ(Z^q)) − len(B^q)`; `KernelGenerators` (rref kernel / Howell kernel module), `SpMul`, `Transpose` (in `SparseLength`,
replacing the dead `ReverseColumns`, F-MP1 F6)), `Orbifold/MP/Models.{h,cpp}` (`M7`, `R_Z` from the inventory), `Orbifold/MP/MP2Common.{h,cpp}` (harness: `Source`, `MPSide`).
Also `Nerve.h`: 64-bit `kNoIndex` for string indices (F6) and `Twist { Left, Untwisted, Inverse }` (F1).
- `OrbifoldMPComparisonValidation` — **`standard`**: ≈ 11 s, ≈ 60 MB, **901 checks**. P4.5a `Φ` certified to degree 3 on `M7` (55 816 generators) and `R_Z` (59 448),
  ≈ 0.3 s, ≈ 200 k terms, 20 distinct group elements; P4.5b `Φ^*_{q+1}δ^q_I = d^q_MP Φ^*_q` exactly (54 sparse products: `F_2, F_3, Z/4`, `n ≤ 2`, `q ≤ 2`); P4.5c `Φ^*`
  iso `H^q(C_I) → H^q(MP)`, `q ≤ 1` (`ℓ ≤ 7`, `n ≤ 12`), `q = 2` (`ℓ ≤ 5`, `n ≤ 3`), both triangulations, = the frozen rows; P4.5d the same over `Z/ℓ^k` (`ℓ ∈ {2,3}`,
  `k ∈ {2,3}`, `n ∈ {0,2}`, `q ≤ 2`; 16 cells); P4.3 / P4.5f–h `ε^* = Φ^* ∘ ε_I^*` from the shipped Bredon complex (`EquivariantCohomologyOnK`): quasi-iso at `ℓ ∈ {5,7}`
  (`n ≤ 12`), rank = Bredon dim and the defect `[0,1,1] / [0,1,2] / [0,1,1] / [0,0,0]` at `(ℓ,n) = (2,0), (2,2), (3,0), (3,2)`, the "if, not iff" witness `ℓ = 3`, `n ∈ {1,3,5}`;
  P4.5i the hybrid `LocalModel` (`ℓ ∈ {2,3}`, `n ≤ 12`): dims = `C_I` = oracle, the strict comparison's pullback an iso on `H^{≤2}`, and on to the nerve (`n ≤ 3`);
  NCs: perturbed `Φ_1` fails `certify()`; the zero map in place of `Φ^*` is not an iso.
  Lines: `PHI`, `PHI_COCHAIN_MAP`, `PHI_ISO`, `PHI_ISO_ZLK`, `EPS_STAR`, `HYBRID`, `ORACLE mv_check.out cells=310 agree=310`, `NC P4.5e`, `NC zero-map`, last
  `ORBIFOLD_MP OrbifoldMPComparisonValidation checks= failing= wall_s=`. No hook, no golden line, no setting.
- `OrbifoldMPRefinementValidation` — **`standard`**: ≈ 3 s, ≈ 60 MB, **115 checks**. P4.6a 7 / 7 labels (each `R_Z` triangle in one `M7` triangle; label `−I`, containment for
  `h` and `h·(−I)`); P4.6b every string of `S_{≤3}(R_Z)` maps into `S(M7)` (1044 non-degenerate strings with a degenerate image carry the zero cochain); P4.6c `u^*` a cochain
  map (27 products) and, with `h·(−I)` on one simplex only, at `F_3`, `n = 1` — where dropping `ρ(h_{σ̃_0})` breaks it (NC); P4.6d `u^* Φ^*_{M7}` iso `H^q(C_I) → H^q(MP(R_Z))`
  and equal to `Φ^*_{R_Z}` on cohomology (`ℓ ∈ {2,3,5}`, `n ∈ {0,2,4}`, `q ≤ 2`), so `u^*` is an iso on `H^{≤2}`; P4.6e label independence; P4.6f NC label `h·T`: containment
  fails, 7146 strings leave `S(M7)`. Lines: `REFINE_LABEL`, `REFINE_STRINGS`, `REFINE_COCHAIN_MAP`, `REFINE_TWIST`, `REFINE_ISO`, `REFINE summary`, `NC P4.6f`, last
  `ORBIFOLD_MP OrbifoldMPRefinementValidation checks= failing= wall_s=`.
- `OrbifoldMPAllDegreesValidation` — **`standard`**: ≈ 5 s, ≈ 40 MB, **1086 checks**. P4.1a `C_I` (`IsotropyModel(7)`) and the hybrid (`LocalModel`) `H^0..H^7` over `F_ℓ`,
  `ℓ ∈ {2,3,5,7}`, `n = 0..12` = the frozen `mv_check.out` (832 values); P4.1b `E^* = e ∪ −` iso `H^q → H^{q+2}`, `q = 2..5`, all 52 rows (`PeriodicityClass` on `q_max = 7`,
  certified); NC P4.1c `ℓ·E^*` not iso at every cell with `H^2 ≠ 0` (13 at `ℓ = 2`, 5 at `ℓ = 3`); P4.2 the eight certificate lines
  `MP_ALL_DEGREES model=<M7|R_Z> ring=F_ℓ nerve_to=2 periodic_on=C_I from=2 via=thm:mpcomparison certified=4/4 scope=bulk verdict=OK` (the `via=` label is [C, thm:mpcomparison]; the MP chapter [C, sec:mpmodel] since [C] 1.22.0-pre.5, MP-CT, with [C, def:mpmorphism], [C, rmk:mphybrid], [C, prop:mpalldegrees]) (`n ≤ 3`: `E^*` iso on `C_I` and `Φ^*`
  iso on `H^{≤2}`). **On the MP complex the degrees above `nerve_to` are Thm 2.1 transported, not computed; scope `Γ = SL_2(Z)`, the bulk only** (not the boundary, the
  pair, or a finite-index subgroup; [C] `rmk:bulkperiodicscope`). Lines: `PERIODICITY_CLASS`, `ALLDEG` (per row), `PERIODIC_C_I`, `ORACLE mv_check.out cells=832 agree=832`,
  `NC P4.1c`, `MP_ALL_DEGREES`, last `ORBIFOLD_MP OrbifoldMPAllDegreesValidation checks= failing= wall_s=`.
- `OrbifoldMPNerveH3Slow` — **`slow`**: ≈ 38 s, ≈ 1.0 GB (predicted ≤ 6 GB, ≤ 10 min), **23 checks**; `d^3` at `n = 2` on `R_Z`: 3 572 421 × 169 047, ≈ 19.7 M nnz, fill ≤ 1.35 M, ≤ 6 s. Nerve `H^3` over `F_ℓ`, `ℓ ∈ {2,3}`, `n ∈ {0,2}`, `M7` and `R_Z` (8 cells, `d^3` on the `k = 4` strings) = the
  frozen rows (P4.4: `1, 1, 2, 0`); `Φ^*` iso on `H^3` (`Φ_3` certified; `Φ^*_3(z)` checked a cocycle by `d^3`); F-MP1 F3: `MPSet(D, 4)` = the interned `S_4` string for string
  (1 394 560 / 1 434 432). Prints `EFFECTIVE OrbifoldMPNerveH3Slow arm=default cells=8` (no env hook: the line states the fixed arm). Lines: `F3`, `NERVE_H3` (with the `d^3`
  fill), `ORACLE mv_check.out cells=8 agree=8`, last `ORBIFOLD_MP OrbifoldMPNerveH3Slow checks= failing= wall_s=`.
- **F-MP1 repairs carried by MP-2.** `OrbifoldMPNerveValidation` gains **4 checks (580 → 584; 596 with the arm)**: F1 the twist `ρ_n(γ_1^{-1})` (an anti-homomorphism)
  breaks `d∘d = 0` at `F_2`, `n = 1` on both triangulations (`NC F1`), and F2(a) the planted `Γ_{ρ²} := ⟨(ST)²⟩` on `M7` (`|U| = 14`, `|S_3^nd| = 10 003`) gives
  `H^0..2(F_2, n = 0) = [1, 1, 2]` against the oracle's `[1, 1, 1]` (`NC F2a`). **F2(b): the nerve's default `H^2` cells (`ℓ ∈ {2,3,5}`, `n ≤ 3`) are load-bearing for the
  central gerbe** — with `−I` dropped at `ρ` every `H^0`/`H^1` and every `Z/ℓ^k` cell still agrees (the F-MP1 probe) — **and must never move behind a hook or into the
  slow tier; (AC), the one hypothesis of Thm 2.1 not decided in C++, is guarded by this cohomology gate (and by Lean L0b), not by a predicate.**
  `OrbifoldMPRulesValidation` gains **4 checks (73 → 77)**: F4 `ModelData` orbit representatives = the descriptor's quotient `(V, E, F)` on `M7`, `R_Z`, `R_Z⁺`, `R_ζ`.

**Slot 22, G1 (the int8 tensor-core IMMA GEMM in `EngineCuda`, package G1 of `docs/implementation/slot22/P5G_prototype_report.md` §7; contract
`src/ModArithmetic/ENGINE_API.md` §11.8; report `docs/implementation/slot22/G1_report.md`).**
Roster **207 = 70 / 119 / 18** (`--all` 189) on top of MP-2. Fragment `Registry/Slot22/G1.cpp`, `cmake/slot22/G1.cmake`.
- `CudaImmaBitIdentityValidation` — **`standard`**: ≈ 5.2 s, ≈ 0.38 GB host, **1357 checks** with `OC_ENABLE_LEGACY=ON`, **1333** in the default OFF build since S24 CL-R2 (the `ENGINE_GPU_IMMA=0` cases of (D) and (F) are legacy arms `D-policy-off`, `D-batch-policy-off`, `F-imma-off`; first line `EFFECTIVE ENGINE_GPU_IMMA route=new source=retired|default`; 634 cases on the IMMA route; 1346 / 633 at G1, +11 / +1 from the audit-R7 policy cases). Files: `src/Cuda/ImmaKernels.cuh`
  (the kernels, included by `cuda_kernels.cu` only), the routing in `cuda_kernels.cu` / `Engine/DeviceBackend.cpp`, `src/Cuda/CudaImmaValidation.{h,cpp}`.
  Every case compares the device's `C` with `engine::kernels::gemm` / `gemm_nt` by `memcmp` of the whole footprint (padding included) **and** asserts the
  number of IMMA launches (1 on the route, `⌈k / w⌉` for a K-chunked case, 0 off it — a vacuous pass is a failure):
  - (A) random operands at `p ∈ {2, 3, 5, 13, 127}` and `Z/{4, 9, 125}`, 11–12 shapes `1³ … 1024 × 1031 × 1024` with M / N / K tails (`k` not ≡ 0 mod 16 / 64),
    rotated over the A / B / C layouts, logical transpositions, `Set` / `Add` / `Sub`, `gemm_nt` and `schur_update`;
  - (B) structured: zero `A` / `B`, extreme residues (every product `+⌊p/2⌋²` or `−⌊p/2⌋²`), zero rows / columns at tile boundaries 0, 31, 32, 63, 64, 127, 128, 255, 256,
    duplicated columns;
  - (C) K-chunking: forced flush intervals 1, 2, 3 around `64 f ± 1`, at `p ∈ {2, 13, 127}`; workspaces for K chunks of 64 / 128 / 320 at
    `k ∈ {w − 1, w + 1, 3w, 1000}`, `Set` / `Add` / `Sub` (the launch count `⌈k / w⌉` asserted); the true int32 bound `K0 = 64 T(p)` (541 056 at 127, 558 656 at 125)
    at `K0 − 16 … K0 + 65`, extreme residues of both signs; `imma_flush_tiles > T(127)` refused (`std::logic_error`);
  - (D) routing: `p ∈ {128 (= 2^7), 131, 65521, 134217757}` and a `uint64_t` context at 13 take the u32 / u64 kernel even with `imma = 1` and a workspace;
    `imma = 0`, no workspace, a workspace below one 64-deep chunk and `k = 0` too (one byte short of the whole K: two K chunks); `imma = −1` follows `ENGINE_GPU_IMMA`,
    tested under **both** states whatever the process environment (`EnvGuard` `0` → 0 launches, unset → 1; audit R7), and a `GemmBatch` at `p = 13` whose
    `prepare_imma` runs under `0` (→ `false`, 0 launches) / unset, and whose prepared `run(imma = −1)` runs under `0` (→ 0 launches) / unset (→ launches);
  - (E) `GemmBatch` with `prepare_imma` (shared operands, `d = 65, 129, 7`, `Set` / `Add` / `Sub`, row- and column-major `C`) against the CPU and against the
    u32 batched kernel;
  - (F) the tape under `ENGINE_DEVICE=gpu` at `p ∈ {13, 2}` (a plain GEMM and its graph replay, a scaled `Sub`, a Θ-like batched `gemm_dense`), verify on and off:
    hashes equal the `cpu` policy's, `DeviceStats::imma_nodes > 0` and IMMA launches > 0, and a larger GEMM grows the slot's IMMA block (`imma_blocks ≥ 2`)
    and drops the cached program's graph (`imma_graph_drops ≥ 1`), whose re-run (re-captured on the new block) is hash-equal; the rollback
    `ENGINE_GPU_IMMA=0` gives the same hashes with all four counters 0.
  - Last line `CUDA_IMMA checks=<c> failing=<f> imma_cases=<k> policy=on|off wall_s=<t>`. `[SKIP]` without a usable device (and with `OC_ENABLE_CUDA=OFF`), or
    when the device / build has no sm_80+ image. Mutation-tested at G1 (a wrong k-loop reduction: 96 failures; a wrong epilogue sign fix: 248 failures and
    an `ENGINE_VERIFY_DEVICE`-style mismatch in arm (F)). No golden line, no record, no setting.
- By construction (the tape gives every GPU GEMM-class node at a qualifying modulus an IMMA workspace) the `gpu` / `hybrid` arms of the existing device
  gates cross the route wherever their modulus is `<= 127` (`EngineCrossDeviceValidation`'s `p = 7` arms). `CudaBitIdentityValidation` passes no IMMA
  workspace and keeps testing the u32 kernel at `p = 2, 3`.

**Slot 22, MP-3 (the Moerdijk–Pronk route: the boundary, restriction / corestriction and the sequence of a pair of groups on the MP model; plan
`MP_impl_plan.md` v0.2.1 §2.5 / §2.6, math plan `MP_math_plan.md` v0.2.1 §4.4, §7.1, §7.4; [C] 1.22.0-pre.6 `prop:mpboundary`, `prop:mprescor`,
`def:mpmorphism`, `thm:mpnatural`; predictions `MP3_predictions.md` P5 / P6, committed before the first run; report `MP3_report.md`).** Roster
**209 = 70 / 121 / 18** (`--all` 191). Same fragment pair `Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`. New library files: `Orbifold/MP/ModuleCochains.{h,cpp}`
(`ModuleRep` — any finite `Z/ℓ^e`-module with a left `Γ`-action, memoised `ρ(g)`; `CoboundaryRep` (= `Coboundary` on `Sym^n`, checked); `LabelledPullbackRep`, the
cochain map `(u^*f)(s) = L(h_{s_0}) f(u(s))` of a labelled morphism — `L = ρ` (the **label factor**) or `ev_h` (Shapiro), `drop_factor` for the NC; `CoefficientMap`;
`PhiPullbackRep` (MP-2's `Φ^*` for any module); `CICoboundaryRep` / `CIRestrictToBoundary` / `CICoefficientMap` (`C_I` = `Hom_Γ(Iso_•, N)`, optionally on `R_d`);
`ConeDifferential` / `DenseCone` in the relative indexing `Cone^q = C^q ⊕ D^{q−1}`; `RepSide`, `CIRepSide`), `Orbifold/MP/Boundary.{h,cpp}` (`BoundaryDescriptor`: `Σ_top` =
the boundary edges `v0v1, v1v2, v2v3` (planted-stabiliser NC switch); `ContainingLabels` / `BoundaryLabels`: the labels of `j`), `Orbifold/MP/SubgroupMP.{h,cpp}`
(`SubgroupDescriptor`: `X` as a `B`-complex — vertex `B`-orbits = double cosets `B\Γ/Γ_v`, top `B`-orbits `(σ, r)`, every point element in `B`; `ForgetCosetLabels`
/ `LabelsToGamma`; `CoindRep` (the coset-representative form = LES-1's `M_{A,1}`); `ResCorMaps` (`res` block `ρ(v_i w_{a(i)}^{-1})`, `cor` the inverse blocks; NC switches
`wrong_rep`, `drop_rho`); `EvaluationMatrix` `ev_h`), `Orbifold/MP/MP3Oracle.{h,cpp}` + `MP3Oracle.inc` (the frozen `mp/mp3/mp3_oracle.out`, sha256 `d1e9042e…`,
transcribed by `mp3_oracle_to_inc.py`; `MP3OracleFileAgrees` re-reads the tracked file row for row). Uses LES-1's `CongruenceLevel`, `Gamma0LevelN`, `GammaHLevelN`,
`TwistedMonomialMatrix`, `RestrictionFibreMap` (read-only; no LES file touched).
- `OrbifoldMPBoundaryValidation` — **`standard`**: ≈ 7 s, ≈ 240 MB, **332 checks** (MP-3b: 331 + the `ORACLE_FILE` sha256 gate). P5.1–P5.3 the boundary MP set on `M7` and `R_Z` (3 edges, (SC), order;
  `|S_k(∂X)|` = (3,3), (18,15), (84,51), (360,159), (1488,483) as the oracle's line model; `MPSet` agrees; `d∘d = 0`); P5.4 `H^0..3(S(∂X); Sym^n)` = `H^•(Γ_∂; Sym^n)`
  (prop:mpboundary (1)) on 134 cells (`F_2, F_3, F_5, F_7`, `n ≤ 12`; `Z/4, Z/8, Z/9`, `n ≤ 4`) and P5.5 the shipped `C_{R_d}` on the 67 `M7` cells, both = the oracle;
  P5.6 labels (each edge in one triangle, coset `{−I, I}`); P5.8 `j^*` a cochain map (18 / 18 per triangulation); P5.9 rank of `j^*` on `H^{≤3}` (classes `Φ^*` of
  `C_I`'s) = `C_I`'s restriction to `R_d` and the derived cells, 38 cells; P5.10 the cone of `j^*` exact = the LES = `C_I`'s cone (18 cells, `q ≤ 2`), P5.10b degree 3 on
  `S_4(M7)` at `n = 0` (`F_2`, `F_3`: `[0,0,1,1]`); P5.11 lem:ell2unbounded (`q = 2, 3`; `H^1(X,∂X; F_2) = 0` at `n = 0`); NCs P5.12a planted `{I}` horocycle stabiliser
  (`|S_1| = 9`, `H = [1,1,0,0]`), P5.12b label `h·T`, P5.12c mixed labels without the factor. Lines: `ORACLE_FILE`, `BDRY_SET`, `BDRY_H`, `BDRY_LABEL`, `BDRY_STRINGS`,
  `JSTAR_COCHAIN_MAP`, `JSTAR_RANK`, `BDRY_CONE`, `BDRY_CONE_H3`, `NC P5.12a/b/c`, `ORACLE mp3_oracle.out cells=134 agree=134`, `BDRY summary`, last
  `ORBIFOLD_MP OrbifoldMPBoundaryValidation checks= failing= wall_s=`. No hook, no golden line, no setting.
- `OrbifoldMPLevelConeValidation` — **`standard`**: ≈ 54 s, ≈ 1.1 GB, **723 checks** (MP-3: 537; MP-3b: + 1 sha256 gate + 185 of the P7 arm). The five LES-0 (iv) pairs `Γ_0(4) < Γ_0(2)`, `Γ_0(9) < Γ_0(3)`, `Γ_1(4) < Γ_0(4)`,
  `Γ^2 < Γ`, `Γ^3 < Γ`; MP cells `(ℓ, n) ∈ {(2,0), (2,1), (3,0), (3,2)}` (+ `(3,1)` for `Γ_1(4)`). P6.1 the seven `B`-descriptors (vertex / top orbits = oracle; (SC); every
  arrow in `B`; `|S_k^nd(B)| = [Γ:B]|S_k^nd(M7)|` when `−I ∈ B`); P6.2 `Coind_B` a representation, = LES-1's `TwistedMonomialMatrix` (48 / 48); P6.3 `C_I(Coind_B)` = the
  oracle (93 cells, `q ≤ 4` / `3`); P6.4 / P6.5 `H^q(S_Γ; Coind_B)` (`Γ`, `Γ_1(4)`) and the nerve `H^q(S_B)` (30 cells) = the oracle; the Shapiro comparison a cochain map,
  a bijection of coordinates when `−I ∈ B`, an iso on `H^{≤2}` after `Φ^*`; P6.6 `res`, `cor` `Γ`-maps = LES-1's `α`, `ω`, `cor ∘ res = [A:B]` on the cochains; P6.7 rank of
  `res` (MP = `C_I` = oracle, 21 cells); P6.8 the cone = `H^q(A,B)` = the LES (21 cells), P6.8b degree 3 on `S_4(M7)` for `Γ^2, Γ^3 < Γ`, P6.8c `C_I` pairs `q ≤ 3` (42 cells);
  P6.9 the forget-coset map `S_B → S_A` (labels in `A`, partly non-central) a cochain map, rank = `res`'s, `= Shapiro ∘ res` on `H^q`; P6.9b for `A = Γ` on the nose; NCs P6.10a
  label factor dropped (`Γ_0(2) → Γ`, `F_3`, `n = 2`), P6.10b wrong coset representative in `res`, P6.10c `cor` without `ρ(h_i)^{-1}`, P6.10d label `r·T`. Lines:
  `ORACLE_FILE`, `SUBGROUP_SET`, `COIND`, `CI_COIND`, `FORGET_COSET`, `PAIR`, `PAIR_H3`, `CI_PAIR`, `NC P6.10a–d`, `ORACLE mp3_oracle.out cells=228 agree=228`, `LEVEL summary`,
  last `ORBIFOLD_MP OrbifoldMPLevelConeValidation checks= failing= wall_s=`. The pair sequence, **not** inflation–restriction. No hook, no golden line, no setting.
  **MP-3b arm P7** (`Orbifold/MP/MP3bLevelArms.{h,cpp}`, oracle `mp/mp3b/mp3b_oracle.py` → `mp3b_oracle.out` sha256 `5b85e393…` → `MP3bOracle.{h,cpp,inc}`;
  `MP3b_predictions.md`): 9 cells -- `Γ_0(4) < Γ_0(2)` over `Z/4` (`n = 0, 1`), `Γ_0(9) < Γ_0(3)` over `Z/9`, `Γ_0(25) < Γ_0(5)` over `Z/25` (`n = 0`) on `M7`;
  `Γ^2 < Γ` (`F_2`), `Γ_0(4) < Γ_0(2)` (`F_3` `n = 2`, `Z/4` `n = 1`) on `R_Z`; `Γ_1(8) < Γ_1(4)` (`−I ∉ A`; `F_2` `n = 0`, `F_3` `n = 1`, MP `q ≤ 1`). Per cell `C_I` and
  `C(S_Γ; Coind)` lengths, the nerves and Shapiro comparisons, `res` / `cor`, the image length of `res` (MP + `C_I`), the cone (MP + `C_I` `q ≤ 3`) and the LES, the
  forget-coset map; P7.9 the `u = −I` forget-coset labels reached (60 of 120, gate `≥ 5`), NC P7.9b (`u = −I` labels replaced by `r^B (r^A)^{-1}` leave `S_A`; `−h ∉ A` is automatic since `−I ∉ A`, so the NC is structurally guaranteed: it shows that P7.8's containment gate detects a `u = I`-only labelling, F-MP3b R1).
  Lines `ORACLE_FILE mp3b_oracle.out`, `PAIR_B`, `NC P7.9b`, `ORACLE mp3b_oracle.out cells=9 agree=9`. Both MP-3 validations now print
  `ORACLE_FILE mp3_oracle.out sha256=<file read> frozen=<inc> sha_match=1` (F-MP3 F2).

**Slot 22, MP-4 (the Moerdijk–Pronk route: Hecke operators on the MP model; plan `MP_impl_plan.md` v0.2.1 §2.5 / §2.6, math plan `MP_math_plan.md`
v0.2.1 §7.3 (G3); [C] 1.22.0-pre.6 `rmk:mphecke`, `def:mpmorphism` (3), `prop:mprescor` (1), `eq:cosettransport`; predictions `MP4_predictions.md` P7, committed
before the first run; report `MP4_report.md`).** Roster **211 = 70 / 123 / 18** (`--all` 193). Same fragment pair `Registry/Slot22/MP.cpp`, `cmake/slot22/MP.cmake`.
New library files: `Orbifold/MP/MPFill.{h,cpp}` (an explicit Z-linear filling of the MP resolution `N Z[F'_•]`: the double complex of thm:mpcomparison's proof with
exact columns (cone from the least vertex of `∩s`) and exact rows (prepend the least translate containing `x`), plus `C_•(X)` in degree 0 (a 1-skeleton path) and 1 (the
unique 2-chain, `F_p` solve certified over `Z`); `d y = z` ENGINE_CHECKed; concrete strings of translates `(h, t)`, `ConcreteString` / `FreeForm`),
`Orbifold/MP/MPHecke.{h,cpp}` (`MPHeckeDatum`: the `conj`-twisted chain datum `τ` on `N Z[F']` over `h ↦ g^{-1}hg`, `g = diag(1, p)`, on the basis `s_j e_s` (shipped
coset representatives), `τ_0 = e_s`, `τ_k = fill(τ_{k−1} d)`; `certify()` (T1)–(T3); `Operator` = `T_p = cor ∘ conj_g ∘ res` in the `eq:cosettransport` form
`Σ_j ρ_n(δ_j γ)`, NC switches `Dropped` (no `ρ_n(g)`) and `WrongRep` (`g T`; the NC is a label factor mismatched with the datum, not a wrong double-coset representative); the factorisation `CgRes` (with the label factor `ρ_n(g)`) into `C(S; Coind_{Γ_0(p)})`
and `Cor`), `Orbifold/MP/MP4Oracle.inc` (the frozen `mp/mp4/mp4_oracle.out`, sha256 `5ed31713…`, transcribed by `mp4_oracle_to_inc.py`). No shipped `τ` table enters
`τ`; `C_I`'s `Θ̂_g` (`StrictLift`) and the Bredon pipeline are the comparison objects only.
- `OrbifoldMPHeckeValidation` — **`standard`**: ≈ 30 s, ≈ 125 MB, **2059 checks**. P7.0 bundle layouts; P7.1 `τ` certified on `M7` (`p ∈ {2,3,5,7}`, degrees `0..2`,
  `(p+1)·2673` generators) and `R_Z` (`p ∈ {2,3}`, degrees `0, 1`); P7.2 `T_{q+1}d^q = d^qT_q` (300: `F_2, F_3, F_5, F_7, Z/4, Z/9`, `n ≤ 4`); P7.3 `T = Cor ∘ CgRes`
  and `CgRes` a cochain map into the Coind complex (96); P7.4 `T_pΦ^* = Φ^*Θ̂_g` on `H^q` (592: `F_ℓ`, `ℓ ∈ {2,3,5,7}`, `n ≤ 12`, `q ≤ 1`, `q = 2` at `ℓ ≤ 3`, `n ≤ 3`;
  `Z/4, Z/8, Z/9, Z/27`, `n ∈ {0,2}`, `q ≤ 2`; `R_Z`); P7.5 the intrinsic matrices on `H^0, H^1(MP; F_ℓ)`: charpolys = `mp4_oracle.out` (464 rows; amalgam cocycles,
  own coset representatives), matrices = `Θ̂`'s (464), τ / Eichler–Shimura `(x − τ(p))^2(x − 1 − p^{11})` at `n = 10`, `ℓ ∈ {5,7}` (8); P7.6 the shipped Bredon `T_p`
  transported by `ε^*` (108: `F_5, F_7` iso, `F_2, F_3` on `im ε^*`); NCs P7.7a label factor dropped, P7.7b label factor mismatched with the datum (`gT` for `g`), P7.7a2 `CgRes` Non-vacuous counts (Fable audit F3, gated, printed as `nontrivial=`): P7.4 `M7` over `F_ell` 240 of 448, P7.5 `M7` 220 of 416, P7.6 66 of 108 (`F_2,F_3` 15 of 24; `F_5,F_7` 51 of 84).
  without `ρ(g)`, P7.7c perturbed `τ_1`. Lines: `HECKE_DATUM`, `HECKE_COCHAIN_MAP`, `HECKE_FACTOR`, `TAU_ES`, `HECKE_CHARPOLY`, `HECKE_INTERTWINE`, `HECKE_BREDON`,
  `NC P7.7a/b/a2/c`, `ORACLE mp4_oracle.out cells=464 agree=464`, last `ORBIFOLD_MP OrbifoldMPHeckeValidation checks= failing= wall_s=`. No hook, no golden line,
  no setting.

**Slot 22, G2 (the device-resident IMMA elimination, package G2 of `docs/implementation/slot22/P5G_prototype_report.md` §7; contract
`src/ModArithmetic/ENGINE_API.md` §11.9; report `docs/implementation/slot22/G2_report.md`).**
Roster **208 = 70 / 120 / 18** (`--all` 190) on top of G1. Fragment `Registry/Slot22/G2.cpp`, `cmake/slot22/G2.cmake`.
- `CudaImmaElimValidation` — **`standard`**: ≈ 11–14 s, ≈ 1.0 GB host, **1819 checks** with `OC_ENABLE_LEGACY=ON` (1814 at G2), **1816** in the default OFF build since S24 CL-R2 (the `ENGINE_GPU_ELIM=0` case of (D) is the legacy arm `D-gpu-elim-off`; first line `EFFECTIVE ENGINE_GPU_ELIM route=new source=retired|default`), ≈ 1010 device eliminations. Files: `src/Cuda/ImmaElim.cuh`
  (kernels + driver `cuda::imma_rref`, included by `cuda_kernels.cu` only), the int8 epilogues in `ImmaKernels.cuh`, the routing in `Engine/TapeElim.{h,cpp}`
  (`device_elim_wanted`, the `tape::rref` route, the `DenseElim` hook) and `ModArithmetic/DenseElim.{h,cpp}` (`set_device_rref_hook`),
  `src/Cuda/CudaImmaElimValidation.{h,cpp}`. Every reference is computed under the thread-local `Cpu` override, so the arm is meaningful under any
  process `ENGINE_DEVICE`:
  - (A) `imma_rref` directly vs `engine::elim::rref`: rank, pivots, the RREF rows by `memcmp`, the host's zero rows, `pivot_rows` as a set (= the row rank profile,
    the column rank profile of `Aᵀ`) and, for `m n ≤ 4·10^5`, as the full sequence (= a scalar reference of the smallest-original-row rule). `p ∈ {2, 3, 5, 13, 127}`;
    `1 × 1`, `1 × 77`, `77 × 1`, zero, identity, random, planted rank (`L·R`), zero columns at 0/15/16/31/32/63/64/255/256/257/511/512 + duplicated columns + a zero
    row, duplicated / scaled rows, sparse ±1 (3 ‰), extreme residues `±⌊p/2⌋`, up to `2500 × 2200` and `4100 × 300` / `300 × 4100` at 13 and 127; base widths 32 / 16,
    7-row upload slabs, a windowed source and sink (`ld > n`; the sink's neighbouring columns untouched); the rank-only (empty) sink.
  - (B) `tape::rref` under the `Gpu` override vs `engine::blk::rref` (rank, pivots, `pivot_rows` in the driver's per-panel order, `R`), `kernel_basis`,
    `image_basis`, `factor_basis` (pivots, relations, basis, projector), `solve_multi_rhs` and its out-of-span message, on `EngineTapeEliminationValidation`'s
    generator (Cq / Zq / generic / dependent shapes, 9 grids `d = 1 … 129`) at `p ∈ {2, 13, 127}`, the device route asserted per case
    (`device_elim_totals().tape_rrefs`, `TapeElimStats::device_elims`); one-column panels (the driver's order = the pivot order = the scalar rule); the
    `ENGINE_GPU_ELIM_VERIFY=1` host re-run (3 eliminations verified, no throw).
  - (C) the `DenseElim` hook under `Gpu` vs `Cpu`: `elim::rref` in place (row- and column-major), `column_rank_profile`, `inverse` (and its refusal of a singular
    matrix), `solve_multi_rhs` (and the out-of-span message), `complement_basis` with projector, `rref_with_transform`; the hook counters must move by exactly
    8 + 1 per prime.
  - (D) routing: `ENGINE_GPU_ELIM=0`, the `Cpu` override, `p = 131`, `p = 134217757`, `Z/9` / `Z/125`, the size floor `ENGINE_GPU_ELIM_MIN` (46000 < 46001 ≤ 46200)
    and a `uint64_t` `tape::rref` never call `imma_rref` (its call counter unchanged), with the same values; `imma_rref` refuses `p = 131`.
  - (E) launch counts: a full-column-rank `1100 × 1000` at 13 runs exactly `⌈n / W⌉` bases (32 / 63), one cooperative launch per base, `n` base columns, and the
    IMMA launch counter of `LaunchStats` moves by exactly the elimination's GEMM count; a zero `300 × 300`: `⌈300/32⌉` bases, 0 GEMMs.
  - (F) negative controls that must fire: a one-entry perturbation of the input is detected; the largest-row rule disagrees with `pivot_rows` (and the smallest-row
    rule agrees); in (B) the device's raw pivot order differs from the driver's per-panel order on ≥ 1 blocked case (43 of 48), so the per-panel sort is exercised.
  - (H) the fallback is loud (G2 audit R1): `ENGINE_GPU_ELIM_SIMULATE_CUDA_ERROR=1` makes the route fail as an OOM would; the host fallback returns the same RREF, `fallbacks` moves by 1, one `[imma_rref] fallback to the host route (<route>, <m>x<n>): <reason>` stderr line is printed, and `device_elim_summary_line()` reports `EFFECTIVE DEVICE_ELIM calls=<n> device=<n> fallbacks=<n>` (also printed to stderr once per process at exit whenever a device elimination was attempted).
  - (G) optional timing arm, read-only hook `CUDA_IMMA_ELIM_BENCH=m,n[,p]` (`EFFECTIVE CudaImmaElimValidation arm=bench …`; `CUDA_IMMA_ELIM_BENCH_CPU=1` adds the
    host elimination and an identity check; `CUDA_IMMA_ELIM_BENCH_ONLY=1` runs it alone and then reports a failure on purpose — a timing run is never a pass).
  - Last line `CUDA_IMMA_ELIM checks=<c> failing=<f> device_calls=<k> bases=<b> gemms=<g> wall_s=<t>`. `[SKIP]` without a usable device (and with
    `OC_ENABLE_CUDA=OFF`) or without an sm_80+ image. Mutation-tested at G2 (the position pivot rule: 297 failures; the int8 `Sub` epilogue sign: 74 failures —
    `CudaImmaBitIdentityValidation` does not see that one, it tests the u32 epilogue). No golden line, no record, no setting.
- The device route is taken by every `gpu`-policy elimination at `p ≤ 127` above the size floor, so the `gpu` arms of the existing device gates and
  `GOLDEN_STRICT=1 ENGINE_DEVICE=gpu GoldenRegressionValidation` (the golden's small primes) cross it.

**Slot 22, BIN-1 (native `F_2` arithmetic, package BIN-1 of `docs/implementation/slot22/L23_master_plan.md` §5; contract
`src/ModArithmetic/ENGINE_API.md` §8.1; report `docs/implementation/slot22/BIN1_report.md`).**
Roster **212 = 70 / 124 / 18** (`--all` 194) on top of MP-4. Fragment `Registry/Slot22/BIN1.cpp`, `cmake/slot22/BIN1.cmake`.
- `BinaryF2Validation` — **`standard`**: ≈ 3.4–3.6 s, ≈ 0.3 GB, **12 479 checks**. Files: `src/ModArithmetic/Binary/BitMatrix.{h,cpp}` (library),
  the opt-in route in `ModArithmetic/DenseElim.{h,cpp}`, `src/ModArithmetic/Binary/BinaryF2Validation.{h,cpp}`. Every engine reference runs under
  `ScopedBinaryF2(false)`, so the arm is meaningful with `ENGINE_BINARY_F2=1` too:
  - negative controls: `p = 3` never takes the route (counter unchanged); `from_dense` refuses an entry `3`.
  - 500 random matrices (word / lane boundary shapes `1, 63, 64, 65, 127, 128, 129, 511, 512, 513` both ways, zero, identity, densities
    2 %–90 %, planted rank `L·R`, ten of `300…1100`²): pack round trip; `binary::rref` rank / pivots / RREF entrywise vs `elim::rref`, `echelon`,
    `rank`, `kernel_basis` entrywise vs `elim::kernel_basis` and `A·Kᵀ = 0`, on **every available row path** (portable, AVX2, AVX-512; FNV of the RREF
    equal across paths); `rref_naive`; the routed `elim::rref` and `column_rank_profile` (counters move by exactly 1 each); `RefLinAlg` on every
    5th (≤ 40 000 entries); M4RM and naive product vs `kernels::gemm` at `p = 2` on every 10th; the `uint64_t` route on every 25th.
  - 100 real `A_Cq` (`q = 0, 1, 2`) of the 7-vertex `SL_2(Z)` model at `ell = 2`, `n_sym ∈ {1 … 128}` (20 values), vacuous short-circuit on and off
    (up to `1677 × 1419`): the same comparisons.
  - `compute_cohomology()` at `ell = 2`, `n_sym = 16, 17`, route on vs off: `dim H^q`, `Z_eq`, `B_eq`, `H_eq` bases equal; ≥ 1 routed elimination (46).
  - Lines `BINARY_F2_TIMING n=1024|4096 … bit_rref_s= routed_rref_s= engine_rref_s= speedup_*= m4rm_s=` (4096 adds `target_0.06s=MET|MISSED`;
    **reported, never gated**), last `BINARY_F2 random=500 amalgam=100 paths=… checks= failing= verdict=OK`. No hook, no golden line, no setting.
  - **BIN-2 repair R1 (BIN-1 audit F1, 2026-10-10)**: `from_dense<uint32_t>` (whose body follows the active row path) now runs **inside** the
    row-path loop, for the matrix and for the product operand, so every path's pack is exercised on every machine (the scalar pack was never run on
    an AVX-512 box, the AVX-512 pack never on host-B / the Jetson); audit F2: a transposed-view (strided) pack / unpack round trip on every 10th
    random and every 7th `A_Cq`. **14 539 checks** (was 12 479). Mutation: dropping column 64 in the scalar `uint32_t` pack gives failures on the
    portable and AVX2 paths of this AVX-512 box (`from_dense on this path == the Auto pack`); reverted, `failing=0`.

**Slot 22, BIN-2 (the `Z/2^k` ladder, package BIN-2 of `docs/implementation/slot22/L23_master_plan.md` §2.2 / §5; contract
`src/ModArithmetic/ENGINE_API.md` §8.2; report `docs/implementation/slot22/BIN2_report.md`).**
Roster **213 = 70 / 125 / 18** (`--all` 195) on top of BIN-1. Fragment `Registry/Slot22/BIN2.cpp`, `cmake/slot22/BIN2.cmake`.
- `Ring2kLadderValidation` — **`standard`**: ≈ 12–14 s, ≈ 80 MB, **17 750 checks**. Files: `src/ModArithmetic/Binary/Ring2k.{h,cpp}` (library),
  `src/hacs/Binary/Ring2kReference.{h,cpp}` (rung R6, `nf::BigInt`, `cohomology_app` only), `src/hacs/Binary/Ring2kLadderValidation.{h,cpp}`
  (both under `src/ModArithmetic/Binary/` until the slot-23 NF-layering fix: a lower library's directory may not include NumberField).
  - (A) the rung table: `select_rung(k)` at 19 boundary values (1 → R0, 8 / 9, 16 / 17, 32 / 33, 64 / 65, 128 / 129, 192 / 193, …, 4096 → R5(N=64)),
    4097 refused, `next_rung` walks R0 … R5(N=64) with growing capacity.
  - (B) wraparound fuzz: `u8` exhaustively (65 536 pairs, inverses, valuations); `u8`, `u16`, `u32`, `u64`, `u128`, `WordN<3, 4, 5, 8, 16, 64>`
    (edge values `0, 1, 2, 3, 2^(W-1), 2^W - 1`, word-boundary bits, random) — add, sub, mul, neg, mask, zero test, valuation, shifts, `ctz`,
    odd, Newton inverse (`u · u⁻¹ = 1`), word round trip — against `nf::BigInt` mod `2^W`; the native AXPY / GEMM kernels on **every kernel path**
    (portable, AVX2, AVX-512) against a scalar loop, tails and leading dimensions included.
  - (C) 449 random and planted matrices at 26 values of `k` from 1 to 1024 (shapes `0×5`, `4×0` … `200×200`; families uniform, `2^c ·` uniform,
    small integers, sparse, low rank, planted `P L D R` with known valuations and zero entries): Smith valuations, Howell form, kernel module on
    **every rung that carries `k`** (the non-R5 rungs and the first one or two R5 word counts) equal; vs `ModCtx<uint64_t>::prime_power(2, k)`
    (`howell`, `invariant_factors`, `length`, `kernel_module`; `k ≤ 63`) and `uint32_t` (`k ≤ 31`, every 3rd); vs `engine::ladic` (`smith_lift`,
    `howell`, `kernel_module`) for `k ≥ 64` (≤ 2500 entries) and as spot checks below; vs R6 (≤ 196 entries); vs the unblocked references; Howell
    conditions 1–3 read off the words; `A Kᵀ = 0`; `length(ker) + length(im) = n k`; `#{σ = 0}` = the F₂ rank (BitMatrix); planted valuations
    recovered; kernel-path re-runs on every 5th; panel / reduce-block sweeps (`1, 3, 8, 33, 200` × `1, 5, 64, 300`) leave every value unchanged.
  - (D) 331 amalgam matrices: the 7-vertex model's `A_Cq` over `Z/2^k` (`hecke::GenerateSL2ZRelationsRing<uint64_t>`, `n_sym ∈ {1 … 33}`,
    `k ∈ {2, 4, 8, 16, 31, 32, 63}`, `q = 0, 1, 2`), and the exact (`nf::BigInt`) `Sym^n` coboundary `[ρ(S) − 1; ρ(U) − 1]` (`2d × d`) and cocycle
    relation matrix `[[N_S, 0], [0, N_U], [1 + S, −(1 + U + U²)]]` (`3d × 2d`) of `Z/4 *_{Z/2} Z/6`, `n ∈ {1, 2, 3, 5, 8, 16, 33, 64}`, reduced to
    `k ∈ {8, 40, 63, 64, 65, 100, 128, 129, 256, 600}`: the same comparisons, plus the cross-`k` consistency of the Smith valuations; exact `ρ_n`
    mod `2^63` = `hecke::RhoOfExactRing` (`S`, `ST`, `T`, six `n`).
  - (E) the adaptive rung: planted `2^70`, `2^150` with rank hint 10 → `RING2K_ADAPTIVE` R2(u32) → R3 → R4 → R5(N=3), resolved after 3 reruns;
    no hint → resolved at once (zero invariants are not near the cap); `2^62` at K = 64, guard 4 → one rerun to R4; `2^150` beyond `k_cap = 128` →
    UNRESOLVED.
  - (F) negative controls: a carry-dropping R5(N=4) product caught on 12 / 12 matrices (vs the correct rung and R6); a one-step-short Newton
    inverse on R3 caught by the engine comparison on 12 / 12; one flipped bit of a Howell form caught. Line `NEGATIVE_CONTROL …`.
  - (G) lines `RING2K_TIMING …` (Smith / Howell per rung; R1–R3 vs the engine's field RREF at `n = 1024`, R4 / R5 vs R3 at the same `n` with the
    `N(N+1)/2` model) and `RING2K_ENGINE_TIMING k=32|63 n=512 …` (vs `elim::invariant_factors` / `elim::howell`) — **reported, never gated**.
  - Last line `RING2K_LADDER rungs=R0,R1,R2,R3,R4,R5,R6 random=449 amalgam=331 paths=… checks= failing= verdict=OK`. No hook, no golden line,
    no setting.
  - *BIN-2 audit repairs (slot-22 BIN-3 step 0, 2026-10-10).* **17 765 checks**, `random=450`. R1: `AdaptiveSmith` carries
    `zeros = min(rows, cols) − |σ|` and `verified`; the `RING2K_ADAPTIVE` line prints `zeros=` and, without a rank hint and with
    `zeros > 0`, `-> resolved (unverified: no rank hint)` — (E) asserts `zeros = 2` and that wording on the no-hint run, `verified` and
    `zeros = 0` on the hinted one. F6: three multi-tile GEMM cases per kernel path and width (`np = 64`, `ncols = 2·tile + 37 …`) and one
    planted `3 × 3` at `k = 4096` (R5(N=64) vs `engine::ladic`). R2 (memory, no value changes) and F4 (the `FirstOdd` guard) are code changes
    covered by the existing parts.

**Slot 23, LES-2 (Route A: the level cone on the fixed model; [C] v1.22.0-pre.3 `sec:nebles`, items (LES2)–(LES4), (LES6) and the Route-A half of (LES9) of
`rmk:lescheckable`; plan `docs/implementation/slot23/00-slot23-plan.md` §2 LES-2; predictions `../slot22/LES_predictions.md` §2 and `slot23/LES2_predictions.md`, committed
before the first run; report `slot23/LES2_report.md`).** Roster **218 = 70 / 129 / 19** (`--all` 199). Fragment `Registry/Slot23/LES2.cpp`, `cmake/slot23/LES2.cmake`.
- `HeckeLevelConeValidation` — **`standard`**: ≈ 84 s at load ≈ 5 (slowest cell `Γ_1(11) < Γ_0(11)`, ℓ = 5, n = 4, `m_B(n+1) = 600`: ≈ 22 s), peak ≈ 1.23 GB,
  **1793 checks** (1792 before the audit repairs R1–R3). Files: `Hecke/HeckeLevelCone.{h,cpp}` (`BuildLevelModel` — the character model `L^χ_A` through `InducedRelationsChi`; `RestrictionBlockTable` — `α_*` as a
  constant per-simplex fibre table; `LevelPairCone` — the morphism and the cone, `SixTerm`; `ApplyFibre`, `ApplyCoboundary`), `Hecke/HeckeLevelConeValidation.{h,cpp}`;
  `EquivariantMappingCone` takes a boundary fibre `d_bd ≠ d_V` on the `F_ℓ` route (LES-2 step 0; every equal-fibre path unchanged).
  - Per cell (137 cells): the cone's `ConeCertificate` C1–C13 re-derived; `H⁰(A,B) = H³(A,B) = 0`, `res⁰` injective, every spot exact, the two dimension identities of
    `lem:levelconeexact` (3); `d α_* = α_* d` on `C^q_eq(L_A)`; the connecting map by the zig-zag `= +res^q`; the predicted numbers. Arms **I** (48 split cells),
    **I′** (9), **II** (`Γ_0(25) ⊂ Γ_0(5)`, χ ∈ {1, (·/5), χ_4}, 14), **III** (`Γ_1(11) ⊲ Γ_0(11)`, 6), **III′** (`Γ_1(p) ⊲ Γ_0(p)` at ℓ = p ∈ {5, 7}, 6, with
    `h¹(Γ_1(p)) = Σ_i h¹(Γ_0(p), ω^i)`), **R3** (`Γ_1(5) ⊂ Γ_0(5)`, χ_4 on A, 2), **IV** (ℓ ∈ {2, 3}, 50 cells: `model=` tags and the model dimensions, COMP);
    **H** 118 strict squares (`T_2`, `T_3`, same-level `U_11`): `D_cone Φ = Φ D_cone` on the stored basis, the three families intertwine `Φ`, the alternating product of the
    characteristic polynomials over eq:levelsixterm is 1; **VI** level-raising `U_5` (`Γ_0(25) ⊂ Γ_0(5)`, χ = 1, ℓ ∈ {5, 7}, n ∈ {0, 2}): `U^B_5 α_* = 5 dg_g` on `C^q_eq(L_A)`
    (0 differing; `= 0` at ℓ = 5), the `H¹` square's defect **recorded, not gated** (rank 1, 0, 1, 3; at ℓ = 7, n = 0 labelled as the (LES9) prediction "non-zero",
    met); **NEG** cone_sign, res_no_block, res_wrong_scalar (both refused by the certificate's C2), incompatible_chi, criterion_fails (`U^B_5 α_* ≠ α_* U^A_5` on
    `C^q_eq(L_A)` at ℓ = 7, n = 0, 3988 entries) caught; **gated, not a negative control** (`obl:levelconeexact` (ix)): hecke_two_transversals (formerly hecke_fixed_tables) at
    `Γ_0(25) ⊂ Γ_0(5)`, `T_2`, ℓ = 7, n = 2: transversal-independence on `C_eq` and the strict square with A's own transversal gated (0 / 0); the flat-`C^q` difference recorded (0: `eq:levelcorr` is transversal-independent by construction —
    report §3 item 2).
  - Lines: `LEVEL_RAISE_COCHAIN_SQUARE`, `LEVEL_RAISE_SQUARE`, `NEG <name> caught`, `HECKE_FIXED_TABLES`, `HECKE_FIXED_TABLES_FLAT`, `LEVEL_CONE cells= built= hecke_squares= hecke_bad_entries= families_bad= charpoly_bad= zigzag_bad=
    dalpha_bad= level_raise_cells= level_raise_bad_entries=`, `slowest cell … peak_rss= wall=`, last `LEVEL_CONE checks= failing= verdict=`. No env hook, no golden line, no record.

**Slot 23, PERF-P5 (the AVX-512 VNNI u8×s8 route of `gemm<uint32_t>` for `p ≤ 128`; plan `docs/implementation/slot23/00-slot23-plan.md` §P5;
contract `src/ModArithmetic/ENGINE_API.md` §6.1; predictions and outcome `slot23/P5_predictions.md`).** Roster
**219 = 70 / 130 / 19** (`--all` 200) on top of LES-2 (recount at merge: TER-1 may add a name). Fragment `Registry/Slot23/PERF.cpp`, `cmake/slot23/PERF.cmake`.
- `VnniGemmBitIdentityValidation` — **`standard`**: ≈ 3.8 s, ≈ 26 MB, **2818 checks** (2801 before the audit repair R1), 1 thread. Files: the route in `ModArithmetic/Kernels.{h,cpp}`
  (library, in place), `ModArithmetic/VnniGemmBitIdentityValidation.{h,cpp}`. Arms, each product on every available path (portable, u32 AVX-512 with
  VNNI off, Auto, VNNI forced) against `engine::ref::gemm`, whole buffer compared (padding and the frame around a window untouched):
  **(G)** 656 cases over p ∈ {2, 3, 5, 7, 13, 37, 101, 103, 127} and the composites {4, 9, 121, 125, 128}, shapes across the 8×32 tile, the 128-row
  block and the 1024 k-block, all layouts / transposed views / pads / windows, Set / Add / Sub; **(N)** (audit R1) 4 cases with
  `n > VNNI_NC = 2048` (the second B block: `(m, k, n)` = (9, 20, 2051), (17, 5, 4100), and (130, 33, 2100) twice with a window and a
  transposed B), every one routed by the forced arm (`(N) … routed=`); **(W)** 24 worst cases (every entry `p − 1`, k up to
  3075); **(E)** 9 eliminations (`FlatMatrix` product / rank / RREF and `engine::elim::rref` with the route Off / Auto / Force; the Off arm against
  `ref::gemm` / `ref::rref`); **(R)** refusals (`Force` without VNNI throws; a Canonical-tagged entry 200 at p = 127 on a routed call throws;
  p > 128 and `Off` never route); **(S)** the routed-call counter moves. Without `avx512_vnni` (host-B) the routed arms print a SKIP note. Last line
  `VNNI_GEMM vnni= checks= failing= routed= verdict=`. No env hook of its own; `ENGINE_VNNI=0` / `ENGINE_VNNI_SHADOW=1` are the engine's
  (env table).

**Slot 24, G4 (the two-limb VNNI route of `gemm<uint32_t>` for `128 < p ≤ 2^14`; plan `docs/implementation/slot24/00-slot24-plan.md` §3;
contract `ENGINE_API.md` §6.2; report `slot24/G4_report.md`, audit `slot24/G4_audit.md`). No new name** (roster unchanged, 237): `VnniGemmBitIdentityValidation` extended —
now ≈ 8–10 s, ≈ 36 MB, **6180 checks** (5857 before the audit fixes), still `standard`. New arms: **(G2)** 700 cases over p ∈ {131, 137, 503, 547, 691, 997, 1009, 8191, 16381}
and the composites {3^5, 2^8, 5^6, 127^2, 2^14}, shapes across the 8×32 tile, the 128-row block, the 512-term k-block (k = 513, 1029, 1539) and the
1024-column B block (n = 1025 … 3075, also with m > 128 and k > 512 at once), every layout / transposition / op at 691 and 16381; each case on
every arm, the forced arm through the two-limb route (`(G2) … routed2=`); **(W)** +36 worst cases (every entry `p − 1` at p = 2^14, 16381, 131,
997 over 1–3 k-blocks; the maximal-lane pattern A = 16255, B = 16380 at p = 16381); **(E)** + p ∈ {131, 691, 16381}; **(R)** p = 131 / 16381 / 2^14
route iff VNNI is available, p = 16411 never, `vnni_limbs_for` boundaries 128 / 129 / 16384 / 16385, `Off` never routes p = 691, an entry 20000
behind a Canonical tag at p = 16381 refused on the A side and on the B side, and (audit F1) Auto's large-p shape threshold (p ≥ 2^13 needs
m, n ≥ 128: 8191 / 64³ routes, 8209 / 64³ and 16381 with m or n = 127 do not); **(B)** (audit F6) a sampled sweep of the packer's
`b~ = 128 b mod p`: 317 moduli (129 … 160, every 64th to 16352, 16353 … 16384, composites included), each with every residue b < p
against the limb patterns {128, p−1, 1, 127, 129, (p−1)/2, 255, p−128}, forced two-limb, checked against `(a·b) mod p` (`(B) … routed2=317 bad=0`);
**(S)** the two-limb counter moves on a p = 691 call only. Last line
`VNNI_GEMM vnni= checks= failing= routed= routed2= verdict=` (`routed2` = two-limb calls, also counted in `routed`).

**Slot 23, TER-1 (ℓ = 3 arithmetic: the bit-sliced `F_3` rung T0 and `Mod3k<N>`; `docs/implementation/slot23/00-slot23-plan.md` §2 TER-1;
contract `src/ModArithmetic/ENGINE_API.md` §8.3; predictions `slot23/TER1_predictions.md`, report `slot23/TER1_report.md`).**
Roster **220 = 70 / 131 / 19** (`--all` 201) on top of PERF-P5. Fragment `Registry/Slot23/TER1.cpp`, `cmake/slot23/TER1.cmake`.
- `TernaryF3Validation` — **`standard`**: ≈ 9 s at load ≈ 12, ≈ 0.25 GB, **12 186 checks** (S24 CL-G3: 12 738 before the `Mod3k<N>` part (3) was deleted with
  `Mod3k.h`, CODEAUDIT C-04; 11 166 before the TER-1 audit repairs). Files: `src/ModArithmetic/Binary/TritMatrix.{h,cpp}` (library), the opt-in route in `ModArithmetic/DenseElim.{h,cpp}`, the reader's `F_3` route in
  `Orbifold/L23/AmalgamReader.{h,cpp}` (`Ops3F`, `taylor3`), `src/hacs/Binary/TernaryF3Validation.{h,cpp}` (moved out of `src/ModArithmetic/Binary/`, NF-layering fix). Every engine reference runs under
  `ScopedTernaryF3(false)`, so the arm is meaningful with `ENGINE_TERNARY_F3=1` too:
  - negative controls: `p = 5` never takes the route; `from_dense` refuses an entry `3`.
  - (0) the arithmetic on every row path: bit-sliced `x + y` / `x − y` on all 9 pairs, the plane swap = negation, the byte kernels `f3_add_u8 /
    f3_sub_u8 / f3_neg_u8` on every length 0…200.
  - (1) 400 random matrices mod 3 (word / lane boundary shapes both ways, zero, `2·I`, densities 2 %–94 %, planted rank, eight of `300…1000`²) and
    109 real `A_Cq` of the 7-vertex model at `ell = 3` (`n_sym` 1…100, 20 values, vacuous short-circuit on and off): `TritMatrix::rref` rank / pivots /
    RREF entrywise vs `elim::rref`, `echelon`, `rank`, `kernel_basis` entrywise vs `elim::kernel_basis` and `A·Kᵀ = 0`, on every row path (FNV equal
    across paths); `rref_naive` and `RefLinAlg` (≤ 20 000 entries); the routed `elim::rref` / `column_rank_profile` (counters move by 1 each);
    `rref_with_transform` and `inverse` route on = off; the `uint64_t` route; the product vs `kernels::gemm` and the naive product; strided and `uint8_t`
    pack round trips. `compute_cohomology()` at `ell = 3`, `n_sym = 16, 18`, route on vs off (dims 2 4 0 / 2 5 0; 46 / 47 routed eliminations).
  - (2) the reader: `l23::h1_mod(3, n, 1, {(3,0), (3,1), (2,3), (5,6)})` through `Ops3F` equals the `Ops3<1>` route (`h0`, `length`, every image length)
    for **even** n = 0…40, 52, 64, 78, 80, 82, 100, 128, 160, 240, 242, 244 (32 cells; odd n is vacuous at ℓ = 3, audit F1) plus `mutate = 1` at
    n ≡ 2 mod 4 (13 cells); `k = 2` is unaffected by the switch. **`TAYLOR3_SELFCHECK`** (audit F1): `Rho<Ops3F>::T / Ti` (the characteristic-3 shift)
    against the d²/2 row-operation shift, entrywise on random d × r matrices, and `Ti ∘ T = id`, for d = 1…300 and 3^k + e (|e| ≤ 2, up to d = 731):
    305 sizes, `differing=0`.
  - (1′) audit additions: `solve_multi_rhs` (on `Y = A X`) and `complement_basis([A | I])` with its projector, route on = off (F3); the boundary × boundary
    grid {0, 1, 63, 64, 65, 511, 512, 513}² incl. zero dimensions (64 shapes, R5).
  - (3) **deleted (S24 CL-G3)**: the `Mod3k<N>` arm (71 cases against `nf::BigInt` and `ModCtx<uint64_t>`) and its `MOD3K_TIMING` line went with
    `Mod3k.h`; its one consumer, `engine::ring3k`'s pivot-unit inverse, is now `ModCtx::inv` (gated by `OrbifoldMod3kValidation`).
  - Lines `TERNARY_F3_TIMING n=1024|4096 … trit_rref_s= routed_u32_s= engine_u32_s= speedup_*` (n = 1024 adds the `uint64_t` engine),
    `TERNARY_F3_READER ell=3 n=256 … ops3_s= f3_s= speedup=` (**reported, never gated**), last
    `TERNARY_F3 random=464 amalgam=109 reader_cells=45 paths=… checks= failing= verdict=OK` (`mod3k_cases=` dropped by S24 CL-G3). Mutation-tested: a wrong `z2` plane in the
    AVX-512 add body (1908 failures) and a wrong sign in `taylor3` (55 failures, all in the reader arm). No golden line, no record, no setting.

**Slot 23, LES-3 (Route B: the tree complex of a level pair, inflation–restriction, the Hida `p`-tower; [C] v1.23.0-pre.1 `sec:nebles`, items (LES5),
(LES7), (LES8) and the Route-B half of (LES9) of `rmk:lescheckable`, `obl:levelconeexact` (iv), (vii); plan `docs/implementation/slot23/00-slot23-plan.md` §2 LES-3;
predictions `../slot22/LES_predictions.md` §3 and `slot23/LES3_predictions.md`, committed before the first run; report `slot23/LES3_report.md`).** Roster
**221 = 70 / 132 / 19** (`--all` 202) on top of TER-1. Fragment `Registry/Slot23/LES3.cpp`, `cmake/slot23/LES3.cmake`.
- `HeckeLevelInfResValidation` — **`standard`**: ≈ 23 s at load ≈ 5 (slowest cell: the Route A side of `(AB) Γ_1(5)∩Γ_0(25) ⊲ Γ_1(5)`, n = 3, ≈ 11.5 s), peak
  ≈ 0.9 GB, **1729 checks** (1723 before the audit repairs R1, R2). Files: `Hecke/HeckeLevelInfRes.{h,cpp}` (`TreeCokernel` — `prop:bredon` (2)'s tree complex as one sparse elimination
  `M / (M^S + M^U + M^-)` over `Z/ℓ^K`, ℓ ≥ 5, the fixed spaces as orbit-wise norms of LES-1's `TwistedMonomialMatrix`, P10's `ChainCokernel`; `OnH1` / `Escapes` for
  fibre maps and Merel's operators (every overload refuses a `TreeCokernel` whose generators were not kept); `RankModEll`, `SpanLength` (Howell), `JordanTypeUnipotent`; `RouteBSixTerm`; `FiniteGroupH1SL2` — oracle O3, crossed homomorphisms
  on `SL_2(F_ℓ)` with its own `ρ_n`), `Hecke/HeckeLevelInfResValidation.{h,cpp}`. Every map on `H¹` is gated to preserve the tree complexes (0 escaping generators).
  - **AB** (10 cells, ℓ ∈ {5, 7}): LES-2's cone (`LevelPairCone`, certificate, exactness) and Route B give the same `h0A h1A h0B h1B rank res¹ H¹(A,B) H²(A,B)`, equal to the
    committed numbers (`obl:levelconeexact` (iv), (LES5)).
  - **Z/p** (78 cells): the `Γ_1`-type `Z/p` steps at ℓ = p ∈ {5, 7}, N ∈ {1, 2, 3}, both steps, n ≤ 12 (`D ≤ 7800`, `h1B ≤ 653`): `m_A, m_B`, `h0 = c`, `h1A, h1B` of
    `prop:cycliccone` (3)(c); Jordan type `J_p^{h1A−c} ⊕ J_1^c` of `R_σ` on `H¹(B)`; `R_σ^p = 1`; invariants = coinvariants = `h1A`; `Ĥ^{1,2}(G; H¹(B)) = c`;
    `(R_σ − 1) res¹ = 0`, `res¹ cor¹ = N_G`, `cor¹ res¹ = p = 0`, `cor¹ (R_σ − 1) = 0`, `rank cor¹ = h1A`; the five-term identity; `H¹(A,B) = c`, `H²(A,B)`.
  - **HIDA1** (18 cells): `Γ_0(N)∩Γ_1(p) ⊲ Γ_0(pN)`, p ∈ {5, 7}, N ∈ {1, 2, 3}, n ∈ {0, 2, 4}: `ker res¹ = 0`, `H¹(A) = H¹(B)^G`, `R_σ^{p−1} = 1`, and the `ω(a_σ)^{−i}`-eigenspace of
    `R_σ` on `H¹(B)` has the dimension of the `ω^i` character model of `A` (`prop:levelinfres` (4); the eigenvalue convention is [C] `prop:nebgammaH` (4)'s
    `R_σ F = ψ(d_σ) F`, derivation repeated in the predictions; the p = 7 cells at n = 2 and n = 4 discriminate the sign). The N ∈ {2, 3} identities, promised as
    REC, are gated (they are PROVED).
  - **TOWER** (5 cells × {`F_p`, `Z/p²`}): `Γ^t_2 ⊲ Γ_0(p²)`, n = 0, χ = `ω^{a−2}`: LES8's numbers, Jordan types (free / `J_p^{h1A−1} ⊕ J_1`), the `Z/p²` pivots = the `F_p`
    pivots, reduction mod p, Howell lengths (`res H¹(A) = H¹(B)^G = N·H¹(B)` at a ≢ 2; `length ker res¹ = 1` at a ≡ 2); freeness of `H¹(B)` over `(Z/p²)[G]` at
    a ≢ 2 follows from the `K = 1` Jordan type `J_p^{h1A}` plus the `K = 2` free rank `h1B = p·h1A` (Nakayama), not from the lengths alone; Merel `T_2`, same-level
    `U_p` squares and `R_σ` commuting; the witness: the Eisenstein eigenvalue 3 of `T_2` on `H¹(Γ_0(p²); F_p)` at a = 2.
  - **GAMMA** (24 cells): `Γ(ℓ) ⊲ Γ`, ℓ ∈ {5, 7}, n = 0..8, against `out_predict.txt` and `dim ker res¹ = O3`; `res¹` invariant under `R_S`, `R_T`; `cor¹` an isomorphism on
    the coinvariants; `dim H¹(B)^G − rank res¹` **recorded** (= `dim H²(SL_2(F_ℓ); Sym^n)`); the split cross cells `Γ(5)` at ℓ = 7, `Γ(7)` at ℓ = 5.
  - **MEREL** (6 cells, 34 squares): `T_2`, `T_3` on `Γ_0(25) ⊂ Γ_0(5)` (ℓ ∈ {5, 7}, n ∈ {0, 2}) and `T_2`, `T_3`, same-level `U_11`, the diamond on `Γ_{±1}(11) ⊲ Γ_0(11)`:
    `res¹ T^A = T^B res¹`, 0 differing entries, `rank T^A`, `rank T^B` recorded per square (`MEREL_SQUARE`); the non-vacuity witness (audit R1) `T_2 = 3`, `T_3 = 4` on
    the one-dimensional Eisenstein `H¹(Γ_0(5); F_ℓ)`, n = 0, ℓ ∈ {5, 7}; level-raising `U_5`: `U^B_5 res¹ = 0` at ℓ = 5, the defect ranks 1, 0, 1, 3 = Route A's (`LEVEL_RAISE_SQUARE_B`).
  - **NEG**: res_no_block (escaping generators); jordan_wrong_step (audit R2: `CyclicGates` fed `R_b`, `b = [[1,0],[25,1]] ∈ B`, on `H¹(B)` at ℓ = 5, n = 3 — its Jordan,
    invariants and five-term checks fail on a scratch checker) caught; `MEREL_ODD_LEVEL` (Merel's `T_2` at `−1 ∉ H`) recorded.
  - Lines: per-arm cell lines, `LEVEL_RAISE_SQUARE_B`, `NEG <name> caught`, `MEREL_ODD_LEVEL`, `INF_RES cells ab= zp= hida1= tower= gamma= merel= merel_squares=
    square_bad_entries= escapes=`, `slowest cell … peak_rss= wall=`, last `INF_RES checks= failing= verdict=`. No env hook of its own, no golden line, no record.
- `HeckeLevelConeValidation` gains the read-only hook **`HECKE_LEVEL_CONE_CELLS`** (env table); unset, its arms and lines are unchanged.

**Slot 23, PERF-P2 (threaded host eliminations: `engine::tape::ScopedHostElimHook` around the cone / ι host `engine::elim` calls; plan
`docs/implementation/slot23/00-slot23-plan.md` §P2; contract `src/ModArithmetic/ENGINE_API.md` §10.9, the paragraph "Host eliminations off the tape"; predictions and outcome
`slot23/P2_predictions.md`).** Roster **222 = 70 / 133 / 19** (`--all` 203) on top of LES-3 (recounted from `--list` after the rebase). Fragment
`Registry/Slot23/PERF.cpp`, `cmake/slot23/PERF.cmake`.
- `HostElimThreadDeterminismValidation` — **`standard`**: ≈ 4.5 s, ≈ 0.25 GB, **73 checks** (45 before the audit repairs; 62 under the rollback). Files: the guard in `src/Engine/EngineRuntime.{h,cpp}`
  (library, in place), its four call sites (`EquivariantMappingCone::compute`, `ConeCertificate::verify`, `HeckeInvolution::compute`,
  `InvolutionCertificate::verify`), `src/hacs/HostElimThreadDeterminismValidation.{h,cpp}`. In process, on consumer pools of **1, 4, 16**
  workers (`ScopedConsumerPool`; the global pool is never touched): **(D)** `elim::rref` / `column_rank_profile` / `rref_with_transform` of three
  rank-deficient matrices (700×900 mod 13 — the VNNI route —, 640×520 mod 134217757, 512×512 mod 691) under the hook against the hook-free route on the
  calling thread, one FNV over every output entry and pivot; **(C)** the boundary-pair cone (`make_cone()`: compute + certificate) at (64, 13), (96, 691),
  (64, 134217757): `golden_digest()` plus every `Z` / `B` block, equal to the pool-1 run; **(I)** the production ι^* (`set_exact_relation_data`, compute +
  certificate) at the same cells: every ± basis of `C_eq / Z_eq / B_eq / H`, equal to the pool-1 run; **(R)** hook regions (`host_elim_hook_regions()`)
  **> 0 at 4 and 16 workers, the cone's and ι's counted separately (audit L1; cone 124 / 166 / 124), and = 0 at 1** (no vacuous arm), all 0 under `ENGINE_HOST_ELIM_HOOK=0`. Lines `D … pool= digest= regions=`, `C/I (n, ell)
  pool= cone= iota= dim_Hc1= dim_H1+-= regions=`, `EFFECTIVE HostElimThreadDeterminismValidation arm=hook|rollback pools=1,4,16 regions=`, last
  `HOST_ELIM_DET direct= tall= cone= iota= checks= failing= verdict=` — the three digests are the cross-process check: identical at `ENGINE_THREADS=1, 4, 16`
  and under the rollback (`direct=0xd749725e83de2b27 tall=0x98f836fcbafb5174 cone=0x0172a9f4d585f462 iota=0x9b51032b87e84a2e`). Audit repairs
  (`slot23/P2_audit.md`): **L2** a tall direct case 1600×300 mod 13 (base_panel's tiled pivot search; its own `tall=` digest, so `direct=` is unchanged;
  region count equal at pools 4 and 16); **L3** on a 4-worker pool: (B) `run_concurrently` inheritance 0/6 unhooked → 6/6 hooked, caller restored;
  (C) forced throws in a hook region and in a hooked task reach the caller, the guard and the pool survive (direct arm bit-equal), a nested guard
  installs nothing, a foreign hook already in effect is not replaced (**L4** precedence); (D) four concurrent cells (64, 13) equal the sequential
  run — line `L3 B inherit 0/6 -> 6/6; C caught=2; D concurrent cells 4, mismatches 0`. No golden line, no record, no setting.

**Slot 23, PERF-P4a (the `compute_block()` RSS diet: program 1's arena and route 2's ρ₂ memo released at their last readers, the A-N3 residual
chunked over 512 right-hand sides (`hecke.resid.chunk`), `W` / the `C_eq` scratch released before the Θ_eq copy; plan `00-slot23-plan.md` §P4a;
`slot23/PERF_P4a_predictions.md`, `PERF_P4a_report.md`, `P4a_audit.md`).** Roster **223 = 70 / 134 / 19** (`--all` 204) on top of PERF-P2 (recounted
from `--list` after the rebase). Fragment `Registry/Slot23/PERF.cpp`, `cmake/slot23/PERF.cmake`.
- `HeckeThetaRssDietValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 21 s, ≈ 0.3 GB, 16 arms, 370 checks, `chunked_arms=8 chunked3_arms=4`, digest `0xa3326bcdd2505bae` (277 checks / 12 arms / `chunked_arms=4` /
  digest `0x9771bf22181ff4a6` before audit repair R5). Files: `Hecke/HeckeOperatorOnK.cpp` (in place), `Hecke/HeckeThetaRssDietValidation.{h,cpp}`.
  **Slot-24 G6 arm** (the `HECKE_FIELD_DIET` diet against its rollback, entrywise): (P) program 1 in parts at a two-product budget
  ((50, 13), (64, 101), p ∈ {2, 31}, certified and memory-lean), (F) `HeckeOperatorFamily::release_level_a()`, (M) the boundary
  morphism's lean basis read, (S) the cone's unit-row span route on in-span / out-of-span / no-unit-row operands and one cone per
  setting at (96, 13) (golden digests equal, every stored Ceq / D / Z / B / H / P equal, the shared-Z degree among them, certificates
  verify; the unit-row route must have decided ≥ 3 of the diet-on cone's span tests and none of the rollback's — G6 audit F3: at the
  original (60, 13) the cone's tests were all below the tape threshold, so that comparison never reached the route); second line
  `G6_FIELD_DIET checks=106 failing=0 parted_degrees=16 parts=650 released_pipelines=2 unit_row_routes=3 fallbacks=2 cone_unit_routes=4
  verdict=OK`; the P4A line and digest unchanged. (`tape::factor_basis`'s G6 changes — the early release of stage 1's `R` and the
  1024-row slabs of stage 2 — are not under the lever; their oracle is `EngineTapeEliminationValidation`'s `2x11 d=129` grid, a = 1419,
  i.e. two slabs with a partial last one, against `blk::factor_basis`.)
  Cells `(n, ell)` ∈ {(50, 13), (42, 7), (64, 101), (114, 13)} × `p` ∈ {2, 3, 31, ell} (`p = ell`: U_ell, the low-rank lever). **(T)** the tape operator with
  the Θ_eq certification == the independent legacy route (`ScopedLegacyHeckeOperatorPath`, its own solve and residual) on Θ_flat, Θ_eq, A^{(q)} and the
  certificate counters; **(L)** the memory-lean operator (`ScopedThetaEqCertification(false)` + `ScopedMemoryLean(true)`, exactly the streamed pool /
  Sturm operators' flag pair) == the certified one on A^{(q)} and Θ_block(q); **(C)** chunk coverage: an arm with `dim C_eq^1 > 512` and a ragged tail
  ((64, 101): 585), and one with ≥ 3 chunks ((114, 13): 1035 = 2·512 + 11; audit R5 named (113, 13), but odd n has C_eq = 0 on this model). Last line `P4A_RSS_DIET arms= checks= failing= chunked_arms= chunked3_arms= digest=
  verdict=`; the digest (FNV over A^{(q)} and Θ_eq of every arm) is the printed value of record. No env hook, no golden line, no record.
**Slot 23, PERF-P7 (the VRAM-lean device session; plan `docs/implementation/slot23/00-slot23-plan.md` §P7; contract `src/ModArithmetic/ENGINE_API.md`
§12.9; predictions `slot23/P7_predictions.md`, report `slot23/P7_report.md`).** Roster **224 = 70 / 135 / 19** (`--all` 205) on top of PERF-P4a (recounted
from `--list` after the rebase onto `ab30694c`). Fragment `Registry/Slot23/PERF.cpp`, `cmake/slot23/PERF.cmake`.
- `GpuLeanSessionValidation` — **`standard`**: ≈ 0.3–2 s, ≈ 0.3 GB host, **169 checks** (161 before audit R4); `[SKIP]` without a usable device (CPU-only build,
  `ENGINE_CUDA_DISABLE=1`). Files: the rule in `src/Engine/Executor.{h,cpp}` (library, in place), `PassStats::gpu_compute_nodes` (`Program.h`,
  `Passes.cpp`), the slack and `arena_idle_slack()` in `src/Cuda/CudaCtx.{h,cpp}` (+ stub), `src/hacs/GpuLeanSessionValidation.{h,cpp}`.
  **(L)** at `p = 13` and `134217757` (u32) and `134217757` (u64): a memory-only program (zero / AXPY / AXPY-identity / SCAL / TRANSPOSE / COMPARE,
  `192 × 192`) and a compute program (GEMM + AXPY + COMPARE). They run under `cpu`, `gpu` lean and `gpu` `ENGINE_GPU_LEAN=0`, each `gpu` arm with and
  without the executor's `ENGINE_VERIFY_DEVICE` re-execution. Checks: outputs and result slots hash-equal to `cpu`. Under lean the memory-only program
  makes exactly one lean host run, executes no device node and changes no arena counter (`live_bytes`, `cuda_mallocs + reuses`). Under `lean=0` it
  executes device nodes (the contrast, so the arm is not vacuous). The compute program is never lean and executes on the device. `gpu_compute_nodes`
  is checked as compiled.
  **(S)** inside an elimination session the rule is off: the memory-only program runs on the device, makes no lean run, and its values equal `cpu`.
  **(H)** the Hecke operator (`Θ_flat`, `Θ_eq`, `A`) at `(ℓ, n, p) = (13, 24, 7)` and `(7, 30, 5)` under `cpu`, `gpu` lean and `gpu` `lean=0`:
  digests equal; route 2's memory-only programs are lean host runs under lean (23 per cell) and there are none under `lean=0` or `cpu`. The
  thread's `DeviceTally` agrees: `lean_host_programs` equals the lean runs, and `gpu_programs − lean_host_programs > 0` (audit R4; line
  `gpu-compiled programs 56, of which lean host runs 23, device runs 33`). This still holds after PERF-P4a's route-2 rewrite (audit R1).
  **(A)** the soft-trim slack is a sixteenth of the card under the lean default (a quarter under `lean=0`, within 3 %), unless
  `ENGINE_CUDA_ARENA_SLACK_MB` sets it. A churn of 72 distinct block sizes (8–79 MB) leaves at most the post-trim idle plus the slack plus two
  blocks idle.
  Last line: `GPU_LEAN checks= failing= hecke_lean_runs= slack_mb= wall_s=`.
  Mutation tests (reverted): M1, the rule ignoring compute nodes, gives 12 failures; M2, the rule ignoring an open session, gives 6. The census
  records are byte-identical `cpu` vs `gpu` at `(7, 900)`, `(7, 1000)` and `(13, 700)` (report §2). No golden line, no record, no setting.

**Slot 23, Z2K (the ℓ = 2 (Z) phase of the orbifold census on the `Z/2^k` ladder `engine::ring2k`; owner ruling 2026-10-13, `GPU_scout.md` target 3,
CPU part; contract `src/ModArithmetic/ENGINE_API.md` §8.2 "Second consumer"; predictions `slot23/Z2K_predictions.md`, report `slot23/Z2K_report.md`).**
Roster **225 = 70 / 136 / 19** (`--all` 206). Fragment `Registry/Slot23/Z2K.cpp`, `cmake/slot23/Z2K.cmake`.
- `OrbifoldRing2kValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 52–72 s at load ≈ 7, ≈ 0.5 GB, **365 checks** (342 before the S24 L23-H1 audit's per-body "no wall time" check F3, one per record cell; 317 before the audit repairs). Files: the route in `Campaign/CampaignOrbifold.{h,cpp}`
  (`OrbifoldSmithTorsion`, `OrbifoldKernelModule`, `OrbifoldRing2kEnabled`, `ScopedOrbifoldRing2k`, `OrbifoldRing2kEffectiveLine`, the route counters),
  `Campaign/OrbifoldRing2kValidation.{h,cpp}`.
  - (M) on the real coboundaries of the model C_I at ℓ = 2, n ∈ {0…12, 15, 16, 17, 24, 31, 32, 33, 47, 48, 63, 64, 65, 96, 100, 128} (28 cells): the Smith
    torsion of `δ⁰` over `Z/2^31` and of `δ¹`, `δ²` over `Z/16` (84 comparisons), and the Howell kernel module of `δ¹`, `δ²` over `Z/16` (56: rows, pivots,
    valuations, every entry), `engine::ring2k` vs `elim::invariant_factors` / `elim::kernel_module`; non-vacuity: 79 non-empty torsion lists, 10 239
    non-unit Howell pivots.
  - (R) 23 whole ℓ = 2 cells (`ComputeOrbifoldCell`, n ∈ {0…8, 10, 12, 16, 22, 24, 31, 32, 33, 40, 48, 64, 80, 100, 128}) route on vs off: the record bodies
    byte-identical, **raw** (S24 L23-H1: `orbifold_cell/v2` keeps the sum-rule oracle's wall time out of the body, so the former H-1 mask is the identity; the "masked sites" are the 16 oracle-gate sites, at most one per body; the L23-H1 audit (F3) adds one check per cell that the raw bodies start `"schema":"orbifold_cell/v2"` and carry no ` s)"` time token, the same check in the Z3K / F3L (R) arms), `reader_path` / `sumrule_path` equal, the FNV equal, the log equal after masking decimal fractions, the (Z) fields equal,
    status `ok`; the route counters move by exactly 3 Smith + 2 kernel calls on the claimed route and 0 on the other; an ℓ = 3 cell with the route
    on makes engine calls only.
  - (C) (S24 L23-H1) the v2 synthetic body has one oracle gate site and nothing to mask, a one-character value change is flagged, the site is anchored on the oracle's phrase and on that gate; K = 1 / E = 1 refused; `ScopedOrbifoldRing2k` on / off and the
    `EFFECTIVE l23_ring2k=… source=scoped` line.
  Last line `ORBIFOLD_RING2K matrix_cells= smith= kernels= record_cells= masked_sites= checks= failing= s= verdict=`. Mutation tests (reverted): keeping
  `σ = 0` in the torsion gives 161 failures; one flipped bit in a ladder kernel row gives 212. No golden line, no setting; the records do not move
  (report §3). On-disk records are compared with GL-1's `docs/implementation/slot22/l23_census/record_compare.py` (pairs, or `--dirs <dirA> <dirB>`; **unmasked since S24 L23-H1**, `orbifold_cell/v2` only (a `v1` record is refused: convert with `slot24/l23_record_convert.py`); FNV integrity; `reader_path` / `sumrule_path` equal) -- the one comparator since the Z2K audit (M1); Z2K's own `l23_record_compare.py` is retired.

**Slot 23, C3 (the cyclic cubic field of prime conductor ℓ, `h_K = [E_K : C]`, and Λ̄ of arXiv:2610.17865; owner-approved 2026-10-15;
assessment `slot23/arxiv_2610_17865_assessment.md` §5, report `slot23/C3_report.md`).** Roster **226 = 70 / 137 / 19** (`--all` 207). Fragment
`Registry/Slot23/C3.cpp`, `cmake/slot23/C3.cmake` (which also joins the library file `NumberField/CyclicCubic.cpp` to `NumberField`).
- `NumberFieldCyclicCubicValidation` — **`standard`**: ≈ 2.5 s, ≈ 21 MB, **750 checks**. Files: `NumberField/CyclicCubic.{h,cpp}` (the Gaussian-period
  normal basis with exact structure constants, `cubic_mul` / `cubic_norm` / `cubic_sigma`, the cyclotomic units ξ, u = σξ/ξ, v with v² = u, the saturation of
  C = ⟨−1, v, σv⟩ up to Cusick's bound `R ≥ (1/16) log²(d/4)`, the digamma `hR`), `NumberField/CyclicCubicValidation.{h,cpp}`.
  - (F) 148 primes ℓ ≡ 1 mod 3 below 2000: `4ℓ = a² + 27b²` with `a ≡ 1 mod 3`, the period polynomial `x³ + x² − (ℓ−1)/3 x − (ℓ(a+3)−1)/27` exact,
    its discriminant `ℓ²b²`, `d_K = ℓ²`; Gauss's polynomials at 7, 13, 19, 31, 37; `N` multiplicative, `σ³ = 1`.
  - (H) the 80 primes ℓ ≡ 1 mod 3 below 1000: units exact, `hR` (digamma) = `R(C)` to 1e-10 (the independent check, of `R(C) = hR`), `h_an` within
    1e-6 of the index (a consistency check only: it cannot detect an incomplete saturation), `3 ∤ h`, `p ≡ 2 mod 3` to even powers, `h` against the
    pinned table (reproduced by the C3 audit's independent mpmath computation, `slot23/C3_audit.md` finding 2) (`h = 4` at 163, 277, 349, 397, 547, 607, 709, 853, 937; `h = 7` at 313, 877; else 1); Λ̄ below 1000 =
    those nine; the paper's Λ = {163, 277, 349, 547, 607} ⊆ Λ̄ with `Cl[2] = (Z/2)²`; no ℓ < 163 in Λ̄.
  - (D) the table at +64 bits and the ℓ < 400 part rerun: equal SHA-256. (N) saturation from ⟨v^k, σv^k⟩, k = 2, 3, finds `k²h` at 7, 163, 313; the
    `−x²` variant is not the period polynomial; `N(2η₀) = 8`.
  Lines `CUBIC_FIELDS`, `CUBIC_FIELD`, `CUBIC_CLASS` (one per ℓ), `CUBIC_LAMBDA_BAR`, `CUBIC_DETERMINISM`, `CUBIC_CONTROL`; last line
  `NF_CUBIC_SUMMARY checks= failing= secs=`. Every acceptance in the saturation is exact. The rejections rest on MpReal traces at P bits (no interval
  arithmetic), with an NF_CHECK of ≥ 80 bits below the trace magnitudes at P. `closest_reject_log2` is a diagnostic about non-roots, not a soundness margin.
  No env hook, no golden line, writes nothing.

**Slot 23, R5V (the SoA / SIMD kernels of `ring2k`'s R5 rung; BIN-2 open item O1, `GPU_scout.md` T6 CPU part; contract
`src/ModArithmetic/ENGINE_API.md` §8.2 "R5 kernels"; predictions `slot23/R5V_predictions.md`, report `slot23/R5V_report.md`).** Roster
**227 = 70 / 138 / 19** (`--all` 208) on R5V's branch; **228 = 70 / 139 / 19** (`--all` 209) after the Z3K merge. Fragment `Registry/Slot23/R5V.cpp`, `cmake/slot23/R5V.cmake` (which also joins the library file
`src/ModArithmetic/Binary/Ring2kR5.cpp` to `ModArithmetic`).
- `Ring2kR5SimdValidation` — **`standard`**: ≈ 5 s, ≈ 78 MB, **7174 checks**. Files: `src/ModArithmetic/Binary/Ring2kR5.cpp`, `Ring2kR5Body.inc` (one body per
  kernel path), `Ring2k.h` (`Traits<WordN<N>>` → `r5k::`, the scalar bodies kept as `*_scalar`), the reader's Taylor shifts in
  `Orbifold/L23/AmalgamReader.cpp` (`HasR5Rows`), `src/hacs/Binary/Ring2kR5SimdValidation.{h,cpp}`. The oracle is the scalar
  `Traits<WordN<N>>` body (itself checked against R6 / ModCtx / ladic by `Ring2kLadderValidation`), for N ∈ {3, 4, 5, 6, 8, 10, 12, 16} on every available
  path (portable / AVX2 / AVX-512):
  - (A) 6024 kernel cases: GEMM (`mr ≤ 9`, `np` up to `2 TC + 8`, `nc` up to 300, padded leading dimensions), the all-ones delayed-carry stress
    (`np = 3 TC + 5`), AXPY (`n` up to 400), row add / sub / neg (`n` up to 500, chunk tails); operands zero / small ± / all ones / one word / masked
    to k bits / random.
  - (B) 112 matrices end to end, SIMD (each path) vs `set_r5_kernel(Scalar)`: `smith` (σ and the level ranks), `howell`, `kernel_module` entrywise,
    on random, planted (`X diag(2^v) Y`) and amalgam matrices (the exact Sym^n coboundary `[ρ(S) − 1; ρ(ST) − 1]` and the cocycle relation matrix,
    n = 6, 17, 30, built in `WordN` arithmetic), k from 65 to 64 N.
  - (C) the BIN-3 reader `l23::read_lattice` at (2, 12 / 30 / 46) on R5(N=3), (2, 30) on R5(N=4), (2, 24) on R5(N=6): 15 SIMD runs, every reported
    field (`ladic2_line`, rung, K, m, the `ED_*` censuses, the `RING2K_ADAPTIVE` / `BIN3_ADAPTIVE` log) equal to the scalar run.
  - (D) 88 mutation controls, all caught: `r5k::set_fault` 1 (GEMM borrow chain dropped), 2 (no carries between rank-one updates), 3 (the row
    kernels' element top-word mask dropped; AVX2 / AVX-512 only), and one flipped output bit, per N and path.
  - (E) `R5V_TIMING` lines (reported, never gated): GEMM 192 × 64 × 384 AVX-512 vs scalar 6.3× (N = 3) … 4.1× (N = 16); row add 7.2× … 2.7×.
  Last line `RING2K_R5_SIMD Ns= paths= kernel= e2e= reader= mutations= checks= failing= verdict=`. Mutation tests (reverted): the straddling limb's high
  part dropped in `from_limbs` gives 2096 failures; no carry propagation in the row chunks (`c = G << 1`) gives 2164. The production switches
  (`set_r5_kernel`, `r5k::set_fault`) are process globals restored on exit; no env hook, no golden line, writes nothing.
**Slot 23, Z3K (the ℓ = 3 (Z) phase of the orbifold census on the `Z/3^k` rung `engine::ring3k`; `Z2K_report.md` §4, `GPU_scout.md` target 3, CPU part at
ℓ = 3; contract `src/ModArithmetic/ENGINE_API.md` §8.4; predictions `slot23/Z3K_predictions.md`, report `slot23/Z3K_report.md`).** Roster
**227 = 70 / 138 / 19** (`--all` 208) on Z3K's branch; merged after R5V: **228 = 70 / 139 / 19** (`--all` 209). Fragment `Registry/Slot23/Z3K.cpp`, `cmake/slot23/Z3K.cmake`, which also joins the library file
`src/ModArithmetic/Binary/Ring3k.cpp` to `ModArithmetic`.
- `OrbifoldMod3kValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 25–30 s at load ≈ 5, ≈ 0.47 GB, **7362 checks** (7339 before the S24 L23-H1 audit's per-body "no wall time" check F3; 5841 before the merge-time audit fix F2 added k = 5, 6). Files: `src/ModArithmetic/Binary/Ring3k.{h,cpp}`, the route in
  `Campaign/CampaignOrbifold.{h,cpp}` (`OrbifoldMod3kEnabled`, `ScopedOrbifoldMod3k`, `OrbifoldMod3kEffectiveLine`, `OrbifoldMod3kCalls`; the
  `ladder` argument of `OrbifoldSmithTorsion` / `OrbifoldKernelModule` selects ring2k at ℓ = 2 and ring3k at ℓ = 3), and
  `Campaign/OrbifoldMod3kValidation.{h,cpp}`.
  - (L) The rung on 665 matrices: 12 shapes from 1×1 to 130×40 / 97×101; k ∈ {1, 2, 3, 4, 5, 6, 7, 19} (5 / 6 straddle the u16 / dense variant switch; small shapes only); five modes (uniform, zero, high valuation,
    planted `P·diag(3^σ)·Q` with σ including 0, k − 1 and k, planted plus a duplicated row); default and tiny (5 / 3) panel / reduce-block.
    - Checks: `smith` = `smith_naive` = `smith_levels` (= `smith_lengths` at k ≤ 5; 420 matrices), and = the planted σ.
    - `howell` = `howell_naive` = `howell_blocked`.
    - `length(ker) + length(rowspan) = n k`.
    - At k ≥ 2, also against `elim::invariant_factors` / `elim::howell` / `elim::kernel_module` entrywise.
  - (M) On the coboundaries of C_I at ℓ = 3 (27 cells, n ∈ {0…12, 15–18, 26–28, 36, 54, 80–82, 100, 128}), route on = off:
    - 81 Smith readings (`δ⁰` over `Z/3^19`, `δ¹`, `δ²` over `Z/9`);
    - 54 Howell kernel modules over `Z/9` (rows, pivots, valuations, every entry).
  - (R) 23 whole ℓ = 3 cells route on vs off:
    - the bodies are byte-identical after GL-1's H-1 mask (16 masked sites), the FNV equal, the log equal after masking decimal fractions;
    - `reader_path` / `sumrule_path` and the (Z) fields are equal;
    - the counters move by exactly 3 Smith + 2 kernel calls on the claimed route, and an ℓ = 2 cell (ring2k off) never reaches ring3k.
  - (C) The mask controls, K = 1 / E = 1 refused, a non-canonical entry and k = 20 refused, `ScopedOrbifoldMod3k` and the `EFFECTIVE l23_mod3k=…`
    line.
  Last line `ORBIFOLD_MOD3K rung_matrices= matrix_cells= smith= kernels= record_cells= masked_sites= checks= failing= s= verdict=`.
  Mutation tests (reverted): keeping `σ = 0` in the ring3k torsion gives 158 failures; one entry bumped in each small-modulus Howell output gives 1209.
  No golden line, no setting. The records do not move: route on = off = the census of record on 24 ℓ = 3 cells up to n = 400 (report §3).
  `OrbifoldRing2kValidation`'s ℓ = 3 control now runs under `ScopedOrbifoldMod3k(false)`, so its engine-call count stays exact.
**Slot 23, P4R (route 2's host RSS: `rho2` streamed key by key; P7_report §4, value-neutral, P4(a)-class; report `slot23/P4R_report.md`).**
Roster **227 = 70 / 138 / 19** (`--all` 208) on this branch, recounted from `--list`; **229 = 70 / 140 / 19** (`--all` 210) merged after R5V and Z3K. Fragment `Registry/Slot23/P4R.cpp`, `cmake/slot23/P4R.cmake`.
- `HeckeRho2StreamValidation` — **`standard`**: ≈ 1 s, ≈ 0.13 GB, **16 arms, 257 checks, 673 blocks, 38 mutations, 7 reduce arms** (15 / 225 / 594 / 24 before the merge-time audit fixes F3, F4). Files: `Hecke/HeckeOperatorOnK.{h,cpp}`
  (in place: the streamed route 2 of `compute_block()`, `HeckeOperatorOptions` (5) `ScopedRho2Streaming`, `rho2_stream_stats()`, the validation-only
  `ScopedRoute2Capture` / `ScopedRoute2TargetMutation`), `Hecke/HeckeRho2StreamValidation.{h,cpp}`. Arms `(n, ℓ) ∈ {(50, 13), (42, 7), (64, 101)}`,
  `p ∈ {2, 3, 31, ℓ}` plus one memory-lean `p = 5` arm per point (the census path).
  - (X) streamed vs materialised (`ScopedRho2Streaming(false)`, the rollback) route-2 blocks captured entrywise: same `(q, σ, σ_k)` key set, equal
    entries, both equal to `Theta_block(q)`; `Theta_flat`, `A^{(q)}` and O12(a) equal on / off.
  - (V) non-vacuity: 3 degrees streamed and 0 materialised (and the reverse under the rollback), every distinct key evaluated exactly once, the
    streamed block counter equal to the captured blocks; at `p = ℓ` (the U_ℓ lever's factored route 2) neither counter moves and nothing is captured.
  - (N) the comparators flag one flipped entry. (M) `ScopedRoute2TargetMutation` adds 1 to one entry of the fused block route 2 is compared
    against (first and last captured block; at `p = 31`, audit F4, the first block of every degree, so 2–6-batch degrees are mutated too):
    `compute()` must throw `O12(a) FAILED` naming exactly that entry, streamed and materialised.
  - (R) (merge-time audit fix F3) the validation-only `ScopedRho2StreamReduceEvery(1 / 2)` forces the delayed accumulation's in-loop reduction
    (dead in production unless `k_max ≤ 64`; `r` clamped to `[1, k_max − 1]`, so the same residues): the counter
    `Rho2StreamStats::mid_reductions` must move and the blocks must equal the materialised ones.
  - (B) (merge-time audit fix F4) `(n, ℓ, p) = (12, 101, 61)`: q = 1 has 257 keys (≡ 1 mod the batch of 64, last batch one key): (X), (R)
    and one streamed + one materialised (M) arm in that degree.
  Line `P4R_RHO2_STREAM arms= checks= failing= blocks= mutations= reduce_arms= verdict=`. No golden line, writes nothing. Rollback env `HECKE_RHO2_STREAM=0`
  (the table below).

**Slot 23, P4I (the ι phase's host RSS: admission under a byte budget, streamed flat split, one copy of the ± bases; P4R_report F2,
value-neutral, P4(a)-class; report `slot23/P4I_report.md`).** Roster **230 = 70 / 141 / 19** (`--all` 211) on this branch, recounted from
`--list` (BIN3O1 adds one name concurrently: the lead reconciles). Fragment `Registry/Slot23/P4I.cpp`, `cmake/slot23/P4I.cmake`.
- `HeckeIotaStreamValidation` — **`standard`**: ≈ 1 s, ≈ 0.18 GB, **9 arms, 506 checks, 18 mutations, 4 installer faults**. Files: `Hecke/HeckeInvolution.{h,cpp}`
  (the route; validation-only hooks `HeckeInvolution::ScopedIotaTaskBudget`, `ScopedIotaStreamMutation`, counters `stream_stats()`),
  `Hecke/HeckeIotaStreamValidation.{h,cpp}`. Arms `(n, ℓ) ∈ {(12, 13), (24, 7), (30, 13), (40, 5), (18, 3), (20, 101), (13, 7), (12, 2), (100, 13)}`
  (odd n: no flat family; ℓ = 2: no split, obl(iii) admission only). (X) `HeckeInvolution::compute()` streamed (admission budgets: automatic =
  twice the largest task's estimate, 1 byte = one task at a time, 40000 bytes = tasks above the budget alone, unbounded) against the materialised
  route (`ScopedIotaStreaming(false)`), entrywise: ι^* on H^q, H^q_±, C/Z/B^q_± in every degree, dims, certificate verify. (V) the budget in
  force, admitted estimate ≤ max(budget, largest task), one task at a time at 1 byte, streamed families > 0 (even n, ℓ ≠ 2). (S) a one-worker
  consumer pool (serial). (L) `engine::elim::ScopedLegacy` on a one-worker pool (the streamed split's FlatMatrix branch). (M) mutations 1 (an
  entry of the lowest-degree C^q_+ basis), 2 (a pivot replaced by the largest non-pivot column), 3 (the last split task with real work not run),
  at two budgets, must be applied and caught (throw or entrywise difference); the materialised route ignores them. (N) the comparator flags a
  flipped entry. (F) (audit F1, at the landing) a validation-only thread-context installer that throws (registered by the validation, armed per
  scope), once and on every task thread, streamed and materialised, on a 4-worker pool at (24, 7): `compute()` returns within a 300 s watchdog
  (else the process exits with `[FAIL] … (hang)`) and surfaces exactly the injected error; a clean streamed run afterwards equals the reference;
  skipped under `ENGINE_HOST_THREADS=0`. Restoring the pre-fix in-task-order admission makes (F) report the hang (mutation run at the landing).
  Line `P4I_IOTA_STREAM arms= checks= failing= streamed_families= admissions= mutations= faults= verdict=`. No golden line, writes
  nothing. Rollback env `HECKE_IOTA_STREAM=0` (the table below). A code-level mutation of the streamed minus formula (`(ix − x)/2`, reverted)
  fails 37 checks (`first difference: object 4 (degree 0, slot 4)`).
**Slot 23, F3L (the F₃ field half of an ℓ = 3 orbifold census cell; `Z3K_report.md` §5, value-neutral; predictions `slot23/F3L_predictions.md`, report
`slot23/F3L_report.md`).** Roster **231 = 70 / 142 / 19** (`--all` 212) on this branch, recounted from `--list`. Fragment `Registry/Slot23/F3L.cpp`,
`cmake/slot23/F3L.cmake`.
- `OrbifoldF3lValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 26 s, ≈ 0.19 GB, **39168 checks** (39135 before the S24 L23-H1 audit's per-body "no wall time" check F3; 39163 before the W1-23 S1 fix `e66e0805`). Files: `Integral/Model/IsotropyModel.{h,cpp}` (in place: `rho_n` =
  `rho_n_recurrence`, the O(d²) column recurrence `(a x + c y) f_{j+1} = (b x + d y) f_j`, ascending when `a` is a unit mod `ctx.p`, descending when
  `c` is, else `rho_n_cubic`, the old closed double sum; `F3lRouteEnabled`, `ScopedF3lRoute`, `rho_n_totals`), `Campaign/CampaignOrbifold.{h,cpp}` (in
  place: an ℓ = 3 cell runs under `engine::elim::ScopedTernaryF3(true)`; `OrbifoldF3lEffectiveLine`, `OrbifoldF3lCalls`, `OrbifoldStrictLift`) and
  `Campaign/OrbifoldF3lValidation.{h,cpp}`.
  - Note (audit F3): a cell's `ScopedTernaryF3(true)` overrides an outer `ScopedTernaryF3(false)`; a future engine-vs-ternary cell comparison must use `ScopedF3lRoute(false)`, not an outer ternary-off scope.
  - (P) `rho_n_recurrence` = `rho_n_cubic` entrywise on 21251 cases: F₂, F₃, F₅, F₇, F₁₃, F₆₉₁, F₁₃₄₂₁₇₇₅₇, `Z/9`, `Z/3^19`, `Z/16`, `Z/2^31`, `Z/125`, and
    the u64 contexts F_(2^61−1), `Z/3^30`; fixed `g` (I, T, S, diag(1, p), diag(p, 1), …), random `g` and planted `a ≡ 0` / `c ≡ 0` / both; d_V = 1…40
    and 64…402 at the boundaries `3^k ± 1`, `2^k`. The recurrence runs iff `a` or `c` is a unit (12339 ascending, 4899 descending, 4013 refused).
    The public `rho_n` on = off with the counters on the claimed path; a diagnostic `F3L_RHO_TIMING` line (d = 401: ≈ 44 ms cubic vs ≈ 1.2 ms).
  - (T) `StrictLift::theta_hat` on = off for the census's `T_2, T_3, T_5, T_7`, q = 0…3, n ∈ {0, 1, 4, 9, 26, 27}, over F₃, F₂, `Z/9` (288 matrices).
  - (R) 33 whole cells route on vs off (26 at ℓ = 3: n = 0…12, 16, 17, 25–29, 40, 53, 54, 80–82; 7 at ℓ = 2): bodies byte-identical after GL-1's
    H-1 mask (17 masked sites), FNV equal, logs equal after masking decimal fractions, the (F) / (Z) / reader fields equal; at ℓ = 3 the cell ran
    under the ternary scope and routed F₃ eliminations (none with the route off unless `ENGINE_TERNARY_F3=1`); `rho_n` by the recurrence only
    (on) / the cubic sum only (off); ℓ = 2 never enters the ternary scope.
  - (C) `ScopedF3lRoute` and the `EFFECTIVE l23_f3l=…` line; the cell's `ScopedTernaryF3` is released on return.
  Last line `ORBIFOLD_F3L rho_cases= theta= record_cells= masked_sites= checks= failing= s= verdict=`. Mutation tests (reverted): see the report §4.
  No golden line, no setting, writes nothing. Rollback env `L23_F3L=0` (the table below). The records do not move: route on = off = the census of
  record (report §3).

**Slot 23, BIN3O1 (BIN-3 open item O1: the degree-1 amalgam reader's `r3` / `m2` cost; `DEEP0_report.md` §5; contract
`src/ModArithmetic/ENGINE_API.md` §8.2 `kernel_shift_rows`; predictions `slot23/BIN3O1_predictions.md`, report `slot23/BIN3O1_report.md`).**
Roster **229 = 70 / 140 / 19** (`--all` 210) on BIN3O1's branch (base `d3c09ea7`); **232 = 70 / 143 / 19** (`--all` 213) merged after P4R, P4I and F3L, recounted from `--list`. Fragment `Registry/Slot23/BIN3O1.cpp`, `cmake/slot23/BIN3O1.cmake`.
- `L23Bin3o1Validation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**: ≈ 52–57 s at load ≈ 3–5, **7374 checks** (7371 before the merge-time audit fix F1). Files: `Orbifold/L23/L23Bin3o1Validation.{h,cpp}`; the route in
  `Orbifold/L23/AmalgamReader.{h,cpp}` (`bin3o1_enabled`, `ScopedBin3o1`, `bin3o1_effective_line`, `bin3o1_counters`, the hooks `taylor2_selfcheck`,
  `relation_selfcheck`, `rows_selfcheck`) and the native kernel `ring2k::kernel_shift_rows` (`src/ModArithmetic/Binary/Ring2k.{h,cpp}`).
  Every arm compares the BIN3O1 route with the old one (`ScopedBin3o1(false)` = `L23_BIN3O1=0`) entrywise:
  - (K) `kernel_shift_rows` = the `kernel_axpy` sweep for u8 / u16 / u32 / u64, `f ∈ {−1, +1, 3, random odd}`, n ∈ {0, 1, 2, 15, 16, 17, 31, 32, 33, 47,
    100} (the 16-pass block boundaries), widths around the lane counts, contiguous and strided rows (the padding untouched), every kernel path: 4752 cases.
  - (R) the relation matrix and B¹ (the Pascal / `U³ = (−1)ⁿ` route against five Taylor shifts) over `Z/2^k`, k ∈ {1 … 300} (R1 … R5), n ∈ {1 … 129} at
    the boundaries, and over `Z/3^k`, k ∈ {1, 2, 39, 40, 80}; the parity structure of A on the route: 324 cases.
  - (S) ρ(T), ρ(T)⁻¹, ρ(U), words with runs (T⁹, T⁻⁵, `(13, 3; 4, 1)`), `mat_add`, `mat_sub` on random matrices over every rung kind and kernel path; the
    characteristic-2 shift against the u8 one mod 2; the old dense-Symⁿ `rho_selfcheck` on the route: 2055 cases.
  - (H) `h1_mod` at ℓ = 2, k = 1 (the F₂ / `BitMatrix` route) for every n ≤ 130 and n ∈ {200, 255 … 513}, k ∈ {2, 3, 8, 16, 40}, ℓ = 3 k ∈ {1, 2}; seven
    operators `T_p − c`; the negative control `mutate = 1` compared too: 180 cells.
  - (L) `read_lattice` at ℓ = 2 (K = 64: 20 cells incl. odd n and powers of 2; adaptive full precision on R4 / R5: 5 cells; `mutate = 1, 2`) and ℓ = 3
    (6 cells), every field (divisors, torsion, `BIN3_ADAPTIVE` / `RING2K_ADAPTIVE` logs, failures); `h1_layers` (8), `oddn_row` (5): 50 cells.
  - (C) the route counters (the even-n split accepted 24 / 24, the odd-n reduction 6, F_p block ranks 111, F₂ cells 150, reused `T_p Z` 564; a split
    **fallback** fails the gate, and (merge-time audit fix F1) so does a `rankq_fallback` / `parity_fallback`, the parity structure of A not found),
    the `BIN3O1_ROUTE route=on … fallback=` line, `ScopedBin3o1` and the `EFFECTIVE l23_bin3o1=…` line, a flipped-entry comparator control, `mutate = 1` moving an image.
  Last line `BIN3O1 shift_kernel= relation= operators= h1_mod= lattice= split= odd= rankq= f2= reused= checks= failing= s= verdict=`.
  Mutation tests (reverted): the wavefront's pass count off by one (M1) gives 3260 failures; the sign of ρ(U)² (M2) 385; the top level of the
  characteristic-2 shift dropped (M3) 206; a wrong doubling shift in the cocycle evaluation (M4) 53; `ker(1 + U + U²)` doubled in the even-n split
  (M5: the split falls back, the values stay right) 1 (the fallback counter). No env hook writes, no golden line, no setting.

**Slot 23, G1 (one module run per saturation / Loewy cell, the precision levels below it derived; [C] v1.23.0-pre.3 `sec:satprecisionsec`,
[C, lem:precisionreduction], [C, obl:precisionreuse]; note `slot23/G1_clause_note.md`, audit `slot23/G1_clause_audit.md`, report `slot23/G1_report.md`).**
Roster **234 = 70 / 144 / 20** (`--all` 214) on G1's branch (base `50796ba4`), recounted from `--list`. Fragment `Registry/Slot23/G1.cpp`, `cmake/slot23/G1.cmake`.
Files: `HeckeExt/HeckePrecisionReuseValidation.{h,cpp}`; the route `ringalg::LevelCache`, `ReduceToLevel`, `CheckLevelModule`, `CheckDerivedModule`
(`HeckeExt/HeckeRingHeckeAlgebra.{h,cpp}`), used by `ComputeRingLoewyCell` and `ComputeSaturationDefectCell`. Rollback / oracle arm
`HECKE_PRECISION_REUSE=0` (read-only; the per-K route, one module run per level read; scoped form `ScopedPrecisionReuse`). Every arm compares the
whole printed output of the two routes byte for byte (timings and the run list `Lv_run` excepted; `K_run`, the levels read, must agree).
- `HeckePrecisionReuseValidation` — **`standard`**: **254 checks, ≈ 69 s, 1.38 GiB** (after the implementation-audit fixes F1–F3, 2026-10-16, DEEP-1
  running beside it; first build: 219 checks, ≈ 56 s, 0.17 GiB). Grid:
  (G1) (108, 7) KMAX 6 Loewy + sat (K_stab = 3 with a plateau, a Dickson torsion block; one run at K* = 6, per-K 4.12 s vs 2.44 s);
  (G2) (158, 7) KMAX 3, a `not_stable_at_KMAX` block; (G3) (108, 7) policies `lazy` (a restart: runs [2, 6]) and `at_request`;
  (G4) (10, 691) KMAX 4, policies `auto` (run in the u32 word) and `max` (run at 691⁴ ≥ 2³², the u64 word);
  (G5) (34, 5) KMAX 3 on `ModuleRoute::Digit` (`native_range`) derived, against the per-K native reading;
  (G6) (10, 37), (24, 41): only `reduced_rank1` blocks (one run, nothing derived); (G7) (40, 5) KMAX 3, a Dickson-locus torsion block;
  (G8) (108, 7) with an injected failure of the run above the request (`ScopedInjectRunFailure`): the cell drops to `per_K:failure_at_K=6(…)`, output identical;
  (N) the (iii) checks on (108, 7) at K = 3 (K = 1 against `ReduceModEll` entry for entry) and the two negative controls of [C, obl:precisionreuse](v)
  (a_i kept in place of min(a_i, K) must fire `exponent`; one T_p entry moved by ℓ^{K−1} inside a block of dimension ≥ 2 must fire `commute`),
  plus (audit F3) two on M_3|2: an entry moved by +1 mod ℓ^{a_i} must fire `ReduceModEll` (derived against run), one pushed out of [0, ℓ^{a_i}) must fire `range`;
  (N2) (audit F2) a `ModuleRoute::Digit` run of (34, 5) at K = 3 reduced to K = 2 in the digit and the native form (`ReduceToLevel`'s digit → native
  branch at K ≥ 2): the native entries are the digit sums, both forms pass (iii), the blocks and `ReadAlgebra` agree for every joint system;
  (G9) (audit F1) (60, 5) KMAX 6 Loewy + sat: **K_cls = 3** (e_max = 2; torsion summands of exponent 2 kept while the free summands are cut from
  K* = 6), a certified block, Lv_run = [6] (Loewy per-K 1.23 s vs 0.51 s).
  One `PRECISION_REUSE_CELL (<arm>) … K_run= Lv_run(per_K)= Lv_run(derived)= mode= seconds per_K= derived=` line per comparison.
- `HeckePrecisionReuseSlowValidation` — **`slow`**: **37 checks, ≈ 672 s, 0.55 GiB**. (S1) (300, 7) KMAX 6 sat route: the D = 24 block reads
  eps = [9, 16, 21, 25, 27, 27], five levels read, one run (K* = 6): **per-K 347.0 s vs derived 73.8 s**; (S2) (300, 11) KMAX 6: two levels read,
  one run at 6: **per-K 159.0 s vs derived 92.0 s**.
- Printed: `SAT_DEFECT_LEVELS n= ell= K_run= Lv_run= mode=` by the `HECKE_SAT_DEFECT_CELLS` arm of `HeckeSaturationDefectValidation` only (not its
  default arm); the `hecke_ring_algebra` record fields `Lv_run` and (audit F5) `level_mode`; `EFFECTIVE HECKE_PRECISION_REUSE levels=derived|per_K …`
  (the validation's line, or else the first cell's short line when the variable is set — once per process). A fallback of a run above the request
  to the per-K route prints `WARNING HeckeRingHeckeAlgebra: precision reuse fell back to per_K at (n, ell) = (…): …` on stderr (audit F5).
  The derived-module checks (iii) (`CheckDerivedModule`): summands, exponent, commute, and (audit F3) range and `ReduceModEll` against the run;
  `CheckRunModule` (K = 1 against `ReduceModEll`) once per run.
  No env hook writes, no golden line, no setting.

**Slot 23, G2-X (the forms cross-route's fast q-series product; `slot23/G2_plan.md` §3 G2-X, report `slot23/G2X_report.md`).**
Roster **235 = 70 / 145 / 20** (`--all` 215) on G2-X's branch (base `886357b6`), recounted from `--list`. Fragment `Registry/Slot23/G2X.cpp`,
`cmake/slot23/G2X.cmake`. Files: `HeckeExt/HeckeFormsFastMulValidation.{h,cpp}`; the route `forms::MulSeries` / `MulSeriesFast` /
`MulSeriesSchoolbook` / `MulSeriesChunked` (the audit-M1 route past the transform length) and the `EisensteinSeries` divisor sieve (`HeckeExt/HeckeFormsHeckeAlgebra.{h,cpp}`), used by every caller of the forms
module (`BuildCuspSpace`, `BuildModularSpace`, `DeltaSeries`: the sat route's forms cross-route, `HeckeFormsHeckeAlgebraValidation`, the
`forms_algebra` verb). Rollback / oracle arm `HECKE_FORMS_FASTMUL=0` (read-only; the O(N²) product and trial-division loop through slot 23,
unchanged; scoped form `ScopedFormsFastMul`). The product mod ℓ is unique, so every route returns the same bytes.
- `HeckeFormsFastMulValidation` — **`standard`**: **13204 checks, ≈ 16 s, 0.66 GiB** (after the audit fixes; 12816 / ≈ 13 s / 0.07 GiB before). Grid:
  (P1) 3168 random products, ℓ ∈ {2, 3, 5, 7, 691, 1009, 10007, 65521}, lengths around the schoolbook threshold (63/64/65) and the NTT threshold
  N = 1024, |a| + |b| − 1 on / next to a transform power of two, N below / at / above |a| + |b| − 1: fast = schoolbook = naive, and `MulSeries`
  under both scopes; (P2) every entry ℓ − 1 at ℓ = 65521, length 20000 (the CRT bound's worst case), a monomial, zero and empty series, the square
  (one object twice, and equal content), N = 0, 1, the pentagonal series, `DeltaSeries` fast = naive at five ℓ; (P3) ℓ = 65537 takes the
  fallback; (P5, audit M1 / M2) the transform-length guard: |a| = 2²⁵ − 63, |b| = 65, ℓ = 65521, N = 2²⁵ + 1 takes the length fallback (not the
  NTT) and equals the schoolbook, and `MulSeriesChunked` at chunk_lg ∈ {1, 3, 6, 9} against naive (384 products: random, unequal, truncated, empty);
  (P4) independent identities beyond the oracle's reach: E₄² = E₈ at N = 300001 (transform 2²⁰) for ℓ = 65521, 1009, and
  E₄³ − E₆² = 1728 Δ at N = 100001, ℓ = 10007; (E) the sieve against the loop, ℓ ∈ {5, 7, 691, 1009, 10007, 65521}, N ∈ {1, 2, 3, 97, 5000};
  (F) the sat route's forms objects at its precision N = 2 (k/12 + 1) p_max + 2 for (10, 5), (40, 5), (108, 7), (300, 43), (60, 691),
  (24, 1009): M_k and S_k basis series and T_p on M_k for every generator prime; (S) whole SAT_DEFECT cells (40, 5), (24, 1009), every line
  and the forms fields; (C) non-vacuity counters (NTT, schoolbook, fallback, chunked, sieve taken; the naive scope takes only the naive routes).
  Prints `EFFECTIVE HECKE_FORMS_FASTMUL mul=fast|naive source=default|env|scoped ntt= schoolbook= naive= fallback= chunked= sieve= divisor_loop= (…)`
  first and last. Mutation tests (reverted): CRT dropped (x = r₁) → 200 FAIL lines and the forms build throws; a schoolbook row cut short →
  4488 FAIL lines (then a crash); one sieve term dropped → 21; one DIF butterfly off by one → 634.
- Hook `HECKE_FORMS_FASTMUL_CELLS="n:ell[:naive],…"` (read-only, replaces the arms): the sat route's forms stage alone, `FORMS_STAGE n= ell= k=
  N= dim_M= primes= route= M_gen= seconds= VmHWM_MiB= VmRSS_MiB=` per route (`:naive` adds the naive route and compares the two), then
  `EFFECTIVE HeckeFormsFastMulValidation arm=HECKE_FORMS_FASTMUL_CELLS cells=<k>`; 0 valid cells fails. One cell per process for a clean peak.

**Slot 23, G2-A / G2-B (the module route: Θ_eq, X_q and `H_class_coordinates`' C^q_eq coordinates read off the unit pivots of C, d∘d by GEMM, `cyclic_decomposition`'s loop interchange; F4 folded in;
`slot23/G2_plan.md` §2.1, §2.2, §1.4; report `slot23/G2AB_report.md`).** Roster **237 = 70 / 146 / 21** (`--all` 216) after the rebase onto the G2-X merge `1ba46525` (236 = 70 / 145 / 21 on G2-AB's branch, base `886357b6`),
recounted from `--list`. Fragment `Registry/Slot23/G2.cpp`, `cmake/slot23/G2.cmake`. Files: `HeckeExt/HeckeModuleStreamValidation.{h,cpp}`; the levers are
in-place edits of `src/ModArithmetic/DenseElim.{h,cpp}` (`solve_unit_pivot_readoff`, `module_stream_enabled`, `ScopedModuleStream`,
`ScopedReadoffCorruption`, the counters; ENGINE_API.md §13.6), `EquivariantCohomologyOnK.{h,cpp}` (`ModuleDegree::piv`) and `Hecke/HeckeOperatorOnK.{h,cpp}`
(`Theta_eq_module(q)` accessor). Rollback / oracle arm `HECKE_MODULE_STREAM=0` (read-only, cannot change a value). **F4:** `kEagerEllMax` 13 → 11
(`HeckeExt/HeckeRingHeckeAlgebra.h`): the `auto` run-level policy looks ahead to K_need on the first run only at ℓ ≤ 11 now (value-neutral,
[C, obl:precisionreuse](ii): only `Lv_run` can move).
- `HeckeModuleStreamValidation` (**split** by S24 VAL-IMPL; see "Slot 24 VAL-IMPL"; the independent oracle (R): see "Slot 24 CL-O") — **`standard`**: **941 checks, ≈ 32–40 s, ≈ 0.18 GiB** (849 before the audit fixes m1 / m3) (DEEP-1 running beside it). Every arm runs the stream route and the legacy
  route in process (`ScopedModuleStream(true|false)`), so the environment does not matter.
  (U) the read-off against `solve_multi_rhs_module` and a planted solution on random injective unit-pivot B over Z/5³, Z/7², Z/2⁵ (u32), Z/7¹² (u64);
  `cyclic_decomposition` stream vs legacy on random (G, Rl) over the same rings and Z/5³⁰ (u128), every field;
  (N) negative controls: a right-hand side off im B at a non-pivot row → `Residual`, and the Howell fallback throws the legacy message
  `Vector is not in image of basis (right-hand side 3).`; B[piv, :] ≠ I and a non-increasing piv → `NotIdentity`; the operator-level control
  (`ScopedReadoffCorruption`, one read-off entry +1 at (20, 5, K = 3)) fires the residual check on every solve, falls back to the Howell solve and
  leaves every object unchanged, at (20, 5, K = 3) u32 and (40, 7, K = 12) u64 (audit m3 (a)); an **inconsistent Θ_eq**
  (`hecke::ScopedThetaEqPerturbation`, validation only: W = T·C gets +1 at the first non-pivot row of C, off im C) at the same two cells:
  the legacy route throws `HeckeOperatorOnK (Z/ell^k): runtime assertion (iii) failed -- …` and the stream route (read-off → `Residual` →
  Howell) throws the same text byte for byte (audit m3 (b)); the **d∘d predicate** `engine::elim::product_is_zero` (GEMM and the legacy scalar
  loop) on planted products over Z/5³, Z/2⁵ (u32) and Z/7¹² (u64): zero (one entry ℓ^{k−1}·ℓ = 0), one non-zero entry (→ false, the check
  fires) and an empty inner dimension, on both routes (audit m1);
  (O) object level, entrywise: C, piv, X, Zc, H, dec.{exponents, position, basis, Gamma, U}, dK, length_H, and per T_p (p ∈ {2, 3, 5, 7, ℓ})
  A^{(q)}, Θ^{(q)}, Θ^{(q)}_eq and the certificate bundle, q = 0, 1, 2, at (20, 5, 3), (60, 5, 6), (30, 7, 4), (24, 11, 2), (40, 13, 3), (24, 43, 2),
  (12, 101, 2), (10, 1009, 2) (u32), (40, 7, 12) (u64) and Hida's lattice L_n at (8, 5, 3) (the non-unit-pivot fallback, `howell` ≥ 1);
  non-vacuity counters (stream: read-off, d∘d GEMM, interchanged clear taken, no legacy step, `howell` = 0 on SymN; legacy: only legacy steps);
  (B) ℓ ∈ {2, 3}, the Bredon flat route, (10, 2, 3) and (10, 3, 2): lengths and invariant factors equal, no module-stream step;
  (S) sat cells, byte for byte (`SAT_DEFECT` lines + cell header; K_run, Lv_run equal): (60, 5) KMAX 6 (K_cls = 3), (108, 7) KMAX 6, (160, 11) KMAX 6,
  (50, 13) KMAX 3, (24, 43), (16, 101), (10, 1009). One `MODULE_STREAM_CELL <arm> … seconds stream= legacy= peak_rss_mib …` line per arm, the
  `EFFECTIVE HECKE_MODULE_STREAM …` line before and after.
- `HeckeModuleStreamSlowValidation` — **`slow`**: (300, 1009) and (500, 43) sat cells, stream vs legacy byte for byte, with per-run time and peak RSS
  (VmHWM after a `/proc/self/clear_refs` reset; recorded, not gated). Figures in `slot23/G2AB_report.md`.
  No env hook writes, no golden line, no setting.

**Slot 23, G2-C / G2-D / G2-E (the module route's assembly streamed: Ω per coset with the grouped low-rank GEMM, route 2 in σ-row chunks,
Θ_eq read off the product Θ·C, the lean retention of `RunModuleT`; `slot23/G2_plan.md` §2.3–2.5; report `slot23/G2CDE_report.md`).** No new
name: the roster stays **237 = 70 / 146 / 21** (`--all` 216); the two G2 validations are extended in place. Files: `Hecke/HeckeOperatorOnK.{h,cpp}`
(`compute_module_stream()`, the legacy body kept verbatim as `compute_module_legacy()`, `ModuleRetention`, `set_module_retention`,
`ScopedRoute2Perturbation`), `Hecke/HeckeLowRank.h` (`FastValuation`, `sum_of_low_rank(…, GemmOp)`), `EquivariantCohomologyOnK.{h,cpp}`
(`release_module_intermediates()`, the guarded `module_X` / `module_Zc`), `Hecke/HeckeReduction.cpp` (reads X through `module_X`),
`HeckeExt/HeckeRingHeckeAlgebra.cpp` (`RunModuleT` sets Lean on the stream route), `src/ModArithmetic/DenseElim.{h,cpp}`
(`solve_unit_pivot_readoff_product`, the new counters; ENGINE_API.md §13.6). Rollback `HECKE_MODULE_STREAM=0`.
- `HeckeModuleStreamValidation` adds: (U) `FastValuation` == `ModCtx::valuation` on 4000 residues each over Z/5³, Z/1009², Z/65521² (u32),
  Z/7¹², Z/10007⁴ (u64), and `factor_low_rank` stream == legacy (t, U, V) on 24 blocks per ring (ρ_n of matrices singular mod ℓ and planted
  sums of outer products, some t ≥ 2); the product read-off against the read-off on Y for row blocks 1, 4, 7, 256; (N) its `Residual` (Y off
  im B at a non-pivot row; X(0, 0) + 1) and `NotIdentity` controls; a **corrupted route-2 block entry** (`hecke::ScopedRoute2Perturbation`)
  throws `HeckeOperatorOnK (Z/ell^k): the fused route and route 2 differ at q=0 (O12(a) over Z/ell^k)` byte for byte on both routes at
  (20, 5, 3), (10, 101, 2) (low-rank route 2) and (40, 7, 12) u64, at three sites each (`hecke::Route2Site`, audit m1): the last entry of
  q = 0 (one chunk), and at q = 1 (two chunks, block rows 0–5 and 6–10) entry (0, 0) in the first chunk and the last entry in the second,
  the `q=1` text expected there; the corruption and inconsistent-Θ_eq controls also at (10, 101, 2);
  (O) adds (16, 211, 2), (12, 101, 3), (10, 101, 5) u64 (101⁵ > 2³²), (8, 1009, 4) u64, (6, 10007, 2) (chains of > 2048 terms per group:
  the `kGroupCap` early flush, `lr_early_flush` ≥ 1 asserted there — 198 —, 0 asserted at ℓ ≤ 101; audit m2) and (8, 1291, 3) u32
  (1291³ ∈ (2³¹, 2³²): the u32 word with Barrett `axpy`; audit m3), and every (O) arm checks the counters (stream:
  `omega_streamed` = Σ_p 3(p + 1), `route2_blocked` = 23 σ block **rows** (not chunks) per operator, `lr_grouped` ≥ 1 on SymN, `w_nonpivot` ≥ 1,
  no table / full / scalar step; legacy: `omega_table` = `route2_full` = 3 per operator, `lr_scalar` = 3, none of the stream steps); (L) the **lean retention** at
  (24, 43, 2), (12, 101, 2), (40, 7, 12) u64: C, piv, H, dec, dK, length_H, A^{(q)} and the certificate bundle equal the legacy route's (Full),
  X / Zc are 0 × 0, `module_X` / `module_Zc` / `Theta_module` / `Theta_eq_module` throw their named `… released …` text, `retention=lean`
  counts the cohomology object and every operator. (S) the sat cells now run `RunModuleT`'s lean route against the legacy route, byte for byte.
  **1730 checks, 0 failing, ≈ 43 s, ≈ 0.30 GiB** (maximum resident set, `/usr/bin/time -v`; 1626 / ≈ 45 s / ≈ 0.45 GiB before the audit
  fixes, `slot23/G2CDE_audit.md` "Fixes applied"; DEEP-1 running beside it).
- `HeckeModuleStreamSlowValidation` adds (O) (60, 1009, 4) u64 and (L) (100, 1009, 2) before its two sat cells.

**G2-G (slot 23: the lean work buffers of `elim::cyclic_decomposition` / `elim::invariant_factors`; report `slot23/G2G_report.md`).** No new
name: the roster stays **237 = 70 / 146 / 21** (`--all` 216). Files: `src/ModArithmetic/DenseElim.{h,cpp}` (on the stream route N = [Rl | G]
is never formed, Nh.H is dropped once copied into Γ, one Howell form of [Γᵀ | I] gives both `kernel_module(Γ)` and the coordinates of Rl, K / the
coordinates / the relation matrix are dropped once read, `length(colspan Rl)` is taken right after the s = 0 return (audit n2); `kernel_module` / `solve_multi_rhs_module` now share
`kernel_from_augmented` / `solve_from_augmented`, code motion; counters `cyc_lean`, `cyc_lean_legacy`, `invf_lean`, `invf_legacy`),
`EquivariantCohomologyOnK.cpp` (Z^q's Howell rows dropped before the decomposition). Rollback `HECKE_MODULE_STREAM=0` (the legacy buffers).
- `HeckeModuleStreamValidation` adds (C): `cyclic_decomposition` (exponents, position, basis, Γ, U), `invariant_factors` (G, Rl) and (G) and
  `cyclic_coordinates`, lean == legacy, on random (G, Rl) of eight shapes (nr = 0, ng = 0, m = 1, wide, s = 0, Rl inside / outside span G,
  cohomology-shaped) over Z/5³, Z/43², Z/2⁵, Z/1291³ (u32), Z/7¹², Z/10007⁴ (u64), Z/5³⁰ (u128); the four counters; (N) the F_ℓ refusal and a
  row-count mismatch give the same text on both routes, an ℓ^{k−1} perturbation of G is seen by the comparator. The (O) arms assert the
  `cyc_buffers` / `invf` routing, (B) that `invariant_factors`' buffers are the flat route's only lever step. **1778 checks, 0 failing, ≈ 44 s,
  ≈ 0.47 GiB** (guard peak; DEEP-1 running beside it).
- **G2-G audit fixes** (`slot23/G2G_audit.md`, "Fixes applied"): (C) gains six shapes (m3: m = 0, Rl = 0 with nr > 0, Rl = I, G = I,
  socle-only Rl, socle-only G; fourteen in all, each asserted to run, with M = 0 at s > 0 and m = 0 non-vacuity counts) and an
  **independent oracle** (m2) on Z/2³, Z/3², Z/2⁴, Z/5² (u32) and Z/3² (u64), 980 cases, m ≤ 3, the fourteen shapes: |M[ℓ^j]| counted by
  brute force over (Z/ℓ^k)^m equals ∏ ℓ^{min(e_i, j)} for 0 ≤ j ≤ k (lean `cyclic_decomposition` and `invariant_factors`), with its own
  control (an appended exponent 1 is rejected on every M ≠ 0 case: 545 of 545), and a **fault injection on the lean route**
  (`el::ScopedLeanBufferCorruption`: relation matrix (0, 0) + 1) that must be caught per ring by both entry points (vs legacy, or their
  step-4 check throws), by the oracle on some corruption that passes the step-4 check (pooled: 10), and that leaves the legacy route
  inert. One `MODULE_STREAM_ORACLE <ring> cases= agree= nonzero= ctrl_rejected= inj_cyc= inj_invf= inj_throw= inj_oracle= legacy_inert=`
  line per ring. **1799 checks, 0 failing, ≈ 51 s, peak_rss_mib ≈ 309** (DEEP-1 running beside it).

**G2-F (slot 23: the module route's tau table without its xi-term table and ρ_n pool; report `slot23/G2F_report.md`).** No new name: the
roster stays **237 = 70 / 146 / 21** (`--all` 216). Files: `Hecke/HeckeTauTable.{h,cpp}` (`hecke::TauTableContents::{Full, ChainsOnly}`, a
trailing constructor argument, default `Full`; on `ChainsOnly` no xi-term table and no pool are built, `certify()` skips (f) and (a)'s
length match, the field-route accessors throw a named `std::logic_error`; `stored_bytes()` for reporting), `HeckeExt/HeckeRingHeckeAlgebra.cpp`
(`RunModuleT` builds `ChainsOnly` on the stream route), `src/ModArithmetic/DenseElim.{h,cpp}` (counters `tau_chains`, `tau_pooled`,
EFFECTIVE field `tau=chains:<a>,pooled:<b>`). Rollback `HECKE_MODULE_STREAM=0` (the `Full` table).
- `HeckeModuleStreamValidation` adds (T): per Hecke prime in {2, 3, 5, 7, ℓ}, `Full` vs `ChainsOnly` on one coset table — chain records term
  for term, B_tab / B / fill counters / regime / `to_string()`, `certify() == 0` on both, the seven refusing accessors and the field operator's
  constructor (named text), `stored_bytes()` strictly smaller; the module operator on `ChainsOnly` (stream) equals the stream and the legacy
  route on `Full` (A^{(q)}, Θ, Θ_eq, certificates) — at (20, 5, 3), (12, 101, 2), (6, 10007, 2) u32 and (40, 7, 12), (8, 1009, 4) u64; the
  (L) arms build `ChainsOnly` tables as `RunModuleT` does; the (S) arms assert `tau=chains` (stream) / `tau=pooled` (legacy). **2574 checks,
  0 failing, ≈ 73 s, peak_rss_mib ≈ 293** (DEEP-1 running beside it). **Audit fix F2** (`slot23/G2F_audit.md`): per Hecke prime a negative
  control — `corrupt_record_for_validation()` (validation-only: negates the first coefficient of the vertex slot (q, σ, i) = (0, 0, 1)) on both
  tables after the operator comparison, then `certify() == 20` (clause (b)) on `Full` and on `ChainsOnly` alike. **2597 checks, 0 failing,
  68.3 s, peak_rss_mib 318.9.**
- `HeckeModuleStreamSlowValidation` adds (T) the tau tables of T_10007 alone at n = 300, `ChainsOnly` then `Full`, with `stored_bytes()`
  (gated) and the peak RSS above the RSS before each (recorded): ChainsOnly 75.1 MB stored / +70.8 MiB in 2.7 s, Full 428.3 MB / +427.8 MiB in
  9.9 s (35 KB per coset saved). **143 checks, 0 failing, ≈ 1265 s, max RSS 1.51 GiB** (the legacy (500, 43) cell).

**G2-T (slot 23: the module route's term evaluation; report `slot23/G2T_report.md`).** No new name: the roster stays **237 = 70 / 146 / 21**
(`--all` 216). Files: `src/ModArithmetic/FlatMatrix.{h,cpp}` (`RingPascalRow`, `ComputeSymmetricPowerRowsRing`),
`Hecke/HeckeLowRank.h` (`factor_low_rank(…, fast_scan)`, `PowDivisibility`), `Hecke/HeckeOperatorOnK.cpp` (`compute_module_stream()`),
`src/ModArithmetic/DenseElim.{h,cpp}` (the lever `HECKE_MODULE_EVAL`, `ScopedModuleEval`, counters `eval_fast`, `eval_legacy`,
EFFECTIVE field `eval=fast:<a>,legacy:<b>`). Rollback `HECKE_MODULE_EVAL=0` (the G2-F evaluation).
- `HeckeModuleStreamValidation` adds (V): `ComputeSymmetricPowerRowsRing` == `ComputeSymmetricPowerMatrixRing` entrywise on keys of all four
  routes (each counted) at n ∈ {0, 1, 2, 7, 8, 9, 30, 64} over Z/5^3, Z/1009^2, Z/10007^2, Z/1291^3 (u32, unfused), Z/3^20 and Z/65521^2 (u32, unfused,
  above ⌊2^32/√3⌋ ≈ 2.48·10^9, where a wrongly fused u32 step overflows; audit F2), Z/7^12, Z/10007^4 (u64)
  and Z/3^40 (u64, p > 2^62, unfused); `factor_low_rank` fast_scan == the per-entry scan (t, U, V) on singular ρ_n blocks and planted sums
  (t ≥ 2 asserted) at d ∈ {1, 5, 23, 40} over seven rings; the stream route with the lever on vs off, every (O) object and certificate and
  the counters (`eval=fast` 3 per operator on, `eval=legacy` off), at (20, 5, 3), (12, 101, 2), (6, 10007, 2), (8, 1291, 3) u32, (40, 7, 12),
  (10, 101, 5) u64 and Hida's L_n (8, 5, 3); the SAT_DEFECT lines on vs off at (16, 101) and (10, 1009) KMAX 6; the (O) arms assert
  `eval=fast` on the stream run and no eval counter on the legacy run. **3155 checks, 0 failing, 80.9 s, max RSS 0.47 GiB** (DEEP-1 and
  G2-T's A/B cells running beside it). After the audit fixes (F2: Z/3^20, Z/65521^2 added): **3159 checks, 0 failing, 86.1 s, 0.31 GiB**.
- `HeckeModuleStreamSlowValidation` adds (V) the SAT_DEFECT lines on vs off at (100, 10007) KMAX 4, with both runs' seconds.

**G2-T2 (slot 23: the dispatched SIMD ρ_n fill and route 2's memo across chunks; report `slot23/G2T2_report.md`).** No new name: the roster
stays **237 = 70 / 146 / 21** (`--all` 216). Files: `src/ModArithmetic/FlatMatrix.{h,cpp}` (`RhoFillPath`, `ScopedRhoFillPath`,
`rho_fill_counts`, the AVX2 / AVX-512F column steps under target attributes; lever `HECKE_RHO_SIMD`), `src/ModArithmetic/DenseElim.{h,cpp}`
(lever `HECKE_ROUTE2_SHARED_MEMO`, `ScopedRoute2SharedMemo`, `route2_memo_counts`), `Hecke/HeckeOperatorOnK.cpp` (route 2 in one chunk).
- `HeckeModuleStreamValidation` adds (V) (d)–(g): every rho fill path available on the CPU (scalar, AVX2, AVX-512F), each forced, against
  `ComputeSymmetricPowerMatrixRing` entrywise into a dirty buffer at every n ∈ 0..140 and n ∈ {191, 192, 193, 255, 256, 257, 300} (every tail of the
  8-, 32- and 64-lane wavefronts) on keys of every route plus all-(p − 1), w = 0, t = 0, over Z/5^3, Z/1009^2, Z/10007^2, Z/23159^2, Z/3^19,
  Z/46337^2, Z/2^31, Z/2^2 (SIMD rings), Z/1291^3, Z/65521^2 (u32 > 2^31) and Z/10007^4, Z/3^40 (u64), with the [U] fill counters proving the path
  (scalar wherever SIMD does not apply); each SIMD path against scalar at operator level (every (O) object) at (20, 5, 3), (12, 101, 2),
  (70, 101, 2), (30, 7, 11), (8, 1291, 3) u32, (10, 101, 5) u64, and the SAT_DEFECT lines at (16, 101) KMAX 6 and (70, 1009) KMAX 3; route 2's memo
  shared vs chunked at operator level at (20, 5, 3), (16, 211, 2), (6, 10007, 2) u32, (40, 7, 12), (10, 101, 5) u64 (`route2_degrees` counters
  asserted) and the SAT_DEFECT lines at (16, 101). **4471 checks, 0 failing, 143.2 s, 0.47 GiB** (on the AMD 7950X: all three paths).

**G2-P (slot 23: the parallel module route for single extreme cells; report `slot23/G2P_report.md`).** No new name: the roster stays
**237 = 70 / 146 / 21** (`--all` 216). Files: `Hecke/HeckeOperatorOnK.cpp` (`compute_module_stream()`: the coset-batch parallel assembly of
Θ^{(q)} and route 2, the elimination hook), `src/ModArithmetic/DenseElim.{h,cpp}` (lever `HECKE_MODULE_PARALLEL`,
`ScopedModuleParallel`, the counters; `howell_rows` and `solve_unit_pivot_readoff_product` split over the hook), `EquivariantCohomologyOnK.cpp`
(the hook in `compute_cohomology_module()`). Rollback `HECKE_MODULE_PARALLEL=0` (the serial route); `ENGINE_THREADS=1` is the serial route.
- `HeckeModuleStreamValidation` adds (P): the stream route in process on consumer pools of 1, 2, 7 and 16 workers (`ScopedConsumerPool`):
  every (O) object and certificate and the stream counters equal pool 1's; `par=parallel` on every degree at > 1 worker, `par=serial` and no
  hook region at 1; Howell steps split over the hook at n ≥ 40; the rollback at 7 workers equals pool 1; at 7 workers under each of G2-T2's
  four lever combinations (ρ fill auto / forced scalar × route-2 memo shared / chunked) every object equals pool 1's — at (20, 5, 3),
  (12, 101, 2), (60, 5, 6), (6, 10007, 2) (early flush), (8, 1291, 3) u32, (40, 7, 12), (10, 101, 5) u64 and Hida's L_n (8, 5, 3); the
  SAT_DEFECT lines at pools 1 / 2 / 7 / 16 and at 7 with both G2-T2 levers off, at (16, 101) KMAX 6, (10, 1009) KMAX 6, (40, 211) KMAX 4.
  **9032 checks, 0 failing, 163.8 s, 0.47 GiB** (`ENGINE_THREADS=2`, merged with G2-T2; DEEP-1 and G2-P's timing cells beside it).
- (G2-P audit F1–F3, 2026-10-18) (P) asserts the parallel read-off ran (`module_parallel_readoff_regions`) at (60, 5, 6) u32 and (40, 7, 12) u64
  on every pool > 1, and adds (P) (N): unit level over Z/5^6 u32 and Z/7^12 u64 on a 7-worker hook (m = 1024, 8 row blocks) — Ok == serial,
  Residual for a perturbed row in the last block and for X(0, 0) + 1, a residual injected on a pool worker other than the caller
  (`el::ScopedReadoffWorkerFault(1)`, validation only) → Residual, a throw there (mode 2) rethrown on the caller with its text, Ok again after;
  operator level at (60, 5, 6) u32 and (40, 7, 12) u64 on a 7-worker consumer pool — the worker residual in every parallel read-off → the Howell
  fallback with every object == pool 1's, the worker throw escapes `compute()` with its text and the pool then reproduces pool 1, the corrupted
  read-off and inconsistent-Θ_eq controls. F3: the assembly's task bodies run under `el::ScopedInHookTask`. **9460 checks, 0 failing** (157.5 s at `ENGINE_THREADS=1`, 140.5 s at 8; 0.39 GiB; was 9032).
- `HeckeModuleStreamSlowValidation` adds (P) the SAT_DEFECT lines at pools 1 and 8 at (100, 10007) KMAX 4, with both runs' seconds.

### Slot 24 ELL-W (ℓ > 23170, the [C] `lem:bounds` reach; `docs/implementation/slot24/ELLW_report.md`)

- `HeckeWideTauValidation` — **`standard`**, ≈ 37 s, 1.8 GB peak, **62 checks** (lever on; 48 under `HECKE_TAU_WIDE=0`; 52 / 40 before the audit fixes). Prints
  `EFFECTIVE HeckeTauWide wide_tier=on|off HECKE_TAU_WIDE=<v>` first and `HECKE_WIDE_TAU checks= failing= wide_tier= wall_s= verdict=` last.
  [1] the tiered helpers `hecke::mul_tiered` / `det_tiered` / `inv_unimodular_tiered` (`Hecke/ExactInt.h`): 20000 random int64-fitting pairs give
  the int64 value under `Auto` and `ForceWide` with 0 escalations; fault injection (int64 intermediates overflow, result fits: `operator*` throws,
  `mul_tiered` exact, one escalation counted; a unimodular matrix whose int64 determinant overflows); `ForceNarrow` rethrows; a result outside int64
  throws; extreme operands at ‖·‖ = 2⁶²−1 (intermediates ≈ 2¹²⁴). Under the rollback every overflow propagates. [2] forced-wide = narrow: the τ
  tables of `U_ell` at ℓ ∈ {5, 691, 5003} (n = 0) and of T_2, T_3 at ℓ = 691 (n = 10), chains / B_tab / B entrywise equal under `ForceWide`,
  all narrow, 0 escalations. [3] ℓ = 23173 (first prime past 23170): certifies in the wide tier (B = 4N², B_tab = 20447); under `ForceNarrow`
  refused (`HeckeOverflow`), under `HECKE_TAU_WIDE=0` code 51. [4] at n = 10 (dim H¹ = 3) against τ(p) from Δ = q∏(1−qⁿ)²⁴ (Jacobi's η³,
  computed in the validation): (b) `U_1009` mod 1009 (narrow) charpoly = (X − τ(1009))²(X − 1) (Eichler–Shimura, ℓ > n + 1); (c) `U_30011`
  mod 30011 (wide) the same. [5] (audit F3) `hecke::tau_bound_clause` — the function `certify()` calls — at its boundaries: 0 / 51 / 52 at
  N = 23170, 23171, 1048575, 1048576 (B = 4N²), the B_tab-dominated edge 2NB = 2⁶³ − 1, B = 2⁶³ / UINT64_MAX / 2¹²⁷; and the code-52
  **pre-flight** at N = 2²⁰ (p = 2, r = 20): refused before the build. `HECKE_TAU_WIDE` set → `EFFECTIVE HeckeTauWide` at exit in any run; a
  value other than 0 / 1 → `WARNING` (audit F2).
- `HeckeWideTauSlowValidation` — **`slow`**, ≈ 155 s, 3.4 GB peak, 12 checks (7 under the rollback): [2] at ℓ = 23167 (the largest narrow prime; 16 007 200 τ scalars
  equal under `ForceWide`, B = 2 146 839 556, narrow); [3w] (audit F4) the **wide** table at ℓ = 23173 under `ForceWide` = `Auto` entrywise
  (16 015 126 τ scalars; the 128-bit forms on large operands inside the pipeline); and [4](a) `T_30011` mod 13 at n = 10, charpoly = (X − τ(30011))²(X − (1 + 30011¹¹))
  (wide, B_tab = 26480, B = 3 602 640 484, 0 escalations).
  Read-only hook `HECKE_WIDE_TAU_CELLS=<ell>[,…]` (slow name only; **replaces** its arms): the τ table of `U_ell` (p = ℓ, n = 0) at each
  prime, one `WIDE_TAU_CELL ell= certify= wide_tier= B_tab= B= B_tab_over_N= wide_escalations= step1_escalations= seconds=` line each and
  `EFFECTIVE HeckeWideTauSlowValidation arm=CELLS cells= ok=`; 0 cells fails. Measured: 43867 34 s, 100003 112 s / 1.96 GiB (B_tab/ℓ = 0.882).

### Slot 24 FNTT (the forms NTT levers for ℓ ≥ 10⁴, and the forms ℓ range past 2¹⁶; `docs/implementation/slot24/FNTT_report.md`)

No new name: the arms extend `HeckeFormsFastMulValidation` (slot 23 G2-X). Roster unchanged, `EXPECT_NAMES` unchanged. The route is
`HeckeExt/HeckeFormsHeckeAlgebra.{h,cpp}`: `BuildCuspSpace` and `BuildModularSpace` take the FNTT route. That route uses one NTT plan per
space, caches the spectra F(E₆²), F(Δ) and F(Δʲ), and computes M_k in one pass (f₀ = G_d). It keeps no Dpow / Epow tables: the slots
hold G_{d−j}, which are multiplied by Δʲ in place. Its butterflies are cache-blocked radix-2 butterflies, AVX2 at runtime with a scalar
fallback. The CRT uses Barrett reduction. `HeckeOnCusp` does its elimination in two passes with delayed reduction (chunked residual, AVX2
axpy). The rollback arm is `HECKE_FORMS_NTT_CACHE=0`: the G2-X code, verbatim. The forms range is `forms::FormsSpaceSupported(ell, N)`:
any ℓ < 2¹⁶, and above that, up to ℓ < 2²⁷ inside the FNTT route's exactness bounds (2N − 1 ≤ 2²⁵, N(ℓ−1)² < P₁P₂). The sat route
refuses before the module run outside that range, and so does the `HECKE_SAT_DEFECT_CELLS` parser.

- `HeckeFormsFastMulValidation` — **`standard`**: **13842 checks** (13799 at the package, 13204 before; the audit's (N6) and rollback counters, `FNTT_audit.md`), ≈ 37 s under load 25 (≈ 16 s before), 0.65 GiB. New
  arms, run after the G2-X arms so their random inputs are unchanged:
  - **(N1)** The engine's product (`MulSeriesFntt`) equals the schoolbook at ℓ ∈ {5, 7, 691, 1009, 10007, 20011, 40009, 65521}, with
    N ∈ {1024, 1500, 4097, 9000}. It is tested on four shapes plus the square, with SIMD and scalar butterflies. It also covers the CRT worst
    case (all entries ℓ − 1 at 65521, N = 20000) and is compared with `MulSeriesFast` at N = 600001 (transform 2²¹) for 40009 and 65521.
    The `FnttApplicable` bounds are checked too.
  - **(N2)** Ten cells at the sat route's precision: (10, 65521), (12, 1009) (k = 14, d = 0), (14, 691), (18, 10007), (20, 20011), (40, 40009),
    (300, 43), (60, 691), (24, 1009) and (102, 10007). They cover k′ ∈ {0, 4, 6, 8, 10, 14}. On each cell, the FNTT route with SIMD and with
    scalar butterflies equals the G2-X route: M_k and S_k basis series, and T_p on M_k for every generator prime (delayed loop against the
    legacy loop). The route counters are checked as well. The M_k basis to precision ≤ 2500 also equals an independent construction from
    `HeckeSturmBound`'s E₄ / E₆ / Δ and the schoolbook.
  - **(N3)** A perturbed series makes both `HeckeOnCusp` loops throw the same message.
  - **(N5)** ℓ ∈ {65537, 100003, 131071, 1000003}: the engine's product equals the naive product, including the all-(ℓ − 1) square. The
    M_k basis at k ∈ {12, 16, 18, 20, 22, 26, 50} (N = 2501) equals the `HeckeSturmBound` construction under naive products, and T_2, T_3,
    T_5, T_7 agree on both loops. `SatFormsPrecision` matches `BuildForms` on a (k, ℓ) grid. `FormsSpaceSupported` is checked on both
    sides of its bounds, also under the rollback, and the refusals are checked.
  - The `EFFECTIVE HECKE_FORMS_NTT_CACHE route= simd= source= fntt_spaces= legacy_spaces= forward= inverse= simd_transforms=
    scalar_transforms= hoc_delayed= hoc_legacy= (…)` line is printed first and last.
  - **(N6)** (the FNTT audit) The all-(ℓ − 1) square at the largest N with N(ℓ−1)² < P₁P₂ (ℓ = 1000003, N = 78812; ℓ = 300007,
    N = 875664) equals the closed form (n + 1) mod ℓ, SIMD and scalar, and `FnttApplicable` is false at N + 1. ℓ ≥ 2¹⁶ at N = 1000
    (65537, 1000003, 2²⁷ − 39) builds M_k on the legacy route and matches `HeckeSturmBound`, with T_p on both loops.
    `ComputeSaturationDefectCell` refuses (10, 1000003) and (20, 300007) before the module run, naming `FormsSpaceSupported`, and
    `FormsSpaceSupported` holds at ℓ = 100003 to n = 464 and fails at n = 466. In (N2) the rollback scope's route counters are checked
    (both spaces and every `HeckeOnCusp` on the G2-X code).

  Mutation tests (each reverted):

  | mutation | result |
  |---|---|
  | a de-interleave in the AVX2 h = 2 stage | the forms build throws in arm (F) |
  | the Barrett correction | 200 FAIL lines |
  | the pointwise Montgomery scale | throws |
  | the residual pass dropping a row | throws `HeckeOnCusp … not in the space` |
  | swapping the scalar DIT outputs | 129 FAIL lines in (N1) / (N2) |
- Hook `HECKE_FORMS_FASTMUL_CELLS="n:ell[:naive|:legacy],…"`: `:legacy` runs the default route, then the G2-X route with the FNTT route off,
  and compares the two byte for byte. The `route=` field reads `fntt`, `g2x` or `naive`.

### Slot 24 MT-1 (module-route multithreading for single extreme cells; `docs/implementation/slot24/MT1_report.md`)

- `HeckeModuleMtValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL") — **`standard`**, ≈ 85–115 s (load-dependent), 0.40 GiB peak, **3128 checks** (2900 before the MT-1 audit) (registered by `Registry/Slot24.cpp`;
  code in `HeckeExt/HeckeModuleStreamValidation.cpp`). Every comparison is against the route of before MT-1: `HECKE_MODULE_MT=0`
  (`ScopedModuleMt(false)`) on a 1-worker consumer pool. The lever on runs at pools 1 / 2 / 7 / 16 (`ScopedConsumerPool`; at pool 1 only the
  pivot-search exit applies). (U) `cyclic_decomposition` on 33 relation-shaped inputs (m 128–223, high-valuation columns so the pivot column
  often holds no unit) over Z/5^6, Z/1009^3 u32, Z/7^12 u64 and the tie-heavy Z/4, Z/3^4 u32 (MT-1 audit), at pools 1 / 2 / 3 / 7 / 13 / 16: exponents, position, basis, Γ, U equal, also with every split forced
  (`ScopedModuleMtForceSplit`; the tiled search and the row splits asserted to run); `gemm_rows_hook` = `kernels::gemm`,
  `solve_unit_pivot_readoff` (Ok / Residual) and `solve_multi_rhs_module` (coordinates, or the same first message for a planted off-image
  right-hand side) over Z/101^4 u32 and Z/10007^4 u64. (O) every (O) object (C, X, Zc, H, dec; per operator A^{(q)}, Θ, Θ_eq, the certificate
  bundle) and the stream counters at (60, 5, 6), (12, 101, 2), (6, 10007, 2), (8, 1291, 3), (40, 7, 12) u64, Hida's L_n (8, 5, 3) u64 and
  (120, 1009, 2), with no MT region at pool 1, the (σ, σ_k) assembly tasks at > 1, the per-column checks / row-block products where large
  enough, the tiled pivot search at (120, 1009), the part-(0) exit at every pool (`pivot_exit` > 0); the lever off at 7 workers equals the
  reference with no MT region and no exit. (C) the SAT_DEFECT lines at
  (16, 101) KMAX 6, (40, 211) KMAX 4 and (120, 1009) KMAX 3, byte-identical at every pool (the opt-in forms-overlap arm was removed with
  `HECKE_MODULE_MT_FORMS` at the audit, `slot24/MT1_audit.md` F1).
  Prints `MODULE_MT_CELL` lines with per-pool seconds and region counts and `EFFECTIVE HECKE_MODULE_MT …` first and last.

### Slot 24 G2-H (the time-neutral sat-route memory package; `docs/implementation/slot24/G2H_report.md`)

- No new name (roster unchanged). `HeckeModuleStreamValidation` adds **(H)**, the lean-peak lever `HECKE_MODULE_LEAN_PEAK` against its
  rollback (`ScopedModuleLeanPeak(false)`), and prints `EFFECTIVE HECKE_MODULE_LEAN_PEAK …` first and last; 10 337 checks in all (9460
  before; 10 325 before the audit's F1 / F2 kinds and site), ≈ 130–210 s (load-dependent), 0.53 GiB. (a) `unit_pivot_residual_product`'s status equals `solve_unit_pivot_readoff_product`'s on
  random unit-pivot B over Z/5³, Z/43², Z/1291³ u32 and Z/7¹² u64, four shapes (small, tall with several 128-row tiles, nb = 0, nb = m) and
  eight kinds (consistent, off im B at a non-pivot / pivot row, an ℓ^{k−1} torsion perturbation, `perturb_row` at a non-pivot / pivot row,
  the corruption hook, B[piv, :] ≠ I), row blocks 1 / 3 / 64 / 256, serially and over a 7-worker hook; Ok and Residual both met; l = 0 and a
  non-increasing piv. **Audit F1** (`slot24/G2H_audit.md`): three more kinds confined to the end of the matrix (off im B at the last non-pivot
  row and at the last pivot row, `perturb_row` at the last non-pivot row) and a fifth shape (m = 700, nb = 150: a partial third pivot block,
  550 non-pivot rows in five tiles), so a residual that skipped its last tile, last hook range or last pivot block fails the arm (mutation-tested). (b) `howell` / `kernel_module` / `image_module` / `cyclic_decomposition` / `invariant_factors` lever on == off on 24
  random inputs each over Z/5³, Z/2⁵, Z/10007⁴ u64, Z/5³⁰ u128 (adopted store, copy and pivot-loop length all asserted to run; no lever
  event with the lever off). (c) lean retention (as `RunModuleT`, early release included) at (24, 43, 2), (60, 5, 6), (12, 101, 2),
  (6, 10007, 2), (40, 7, 12) u64, (10, 101, 5) u64, pools 1 and 7: every kept cohomology object, A^{(q)} and the certificate bundle equal
  the lever-off lean run and the legacy run; `residual` and `route2_inplace` once per operator degree, `early_release` once, no product
  read-off (`w=nonpivot` 0). (d) on the lean route at (20, 5, 3), (10, 101, 2), (40, 7, 12) u64: the corrupted certificate falls back to the
  Howell solve with the same objects and counts as the lever off; an inconsistent Θ_eq throws the (iii) text, a corrupted route-2 entry
  (four sites, shared and chunked memo; the fourth, `Route2Site::Degree1Middle` at q = 1's interior block row σ = 3, is audit F2, also in
  the (N) arm stream vs legacy) the O12(a) text, both byte for byte as the lever off. (e) the SAT_DEFECT lines at (60, 5) KMAX 6,
  (16, 101) KMAX 6, (120, 1009) KMAX 3 with the lever on at pools 1 / 4 / 16 and with `HECKE_MODULE_MT` off, against the lever off at one
  worker, byte for byte (`MODULE_LEAN_PEAK_CELL` lines).

### Slot 24 FNTT3 (the forms NTT's third prime, past the two-prime CRT range; `docs/implementation/slot24/FNTT3_report.md`)

- `HeckeFormsNtt3Validation` — **`standard`**, **930 checks** (900 before the audit fixes F1 / F2), ≈ 19–21 s (loaded box), 1.27 GiB (registered by `Registry/Slot24.cpp`;
  code `HeckeExt/HeckeFormsNtt3Validation.cpp`). The route under test is the three-prime chunked engine of `HeckeFormsHeckeAlgebra`
  (P₁ = 5·2²⁵+1, P₂ = 7·2²⁶+1, **P₃ = 45·2²³+1**, root 7; three-limb Garner CRT; blocks of 2²², the block spectra summed per output block),
  reached by `MulSeriesFntt3` and by `BuildCuspSpace` / `BuildModularSpace` where the two-prime route is not exact and ℓ ≥ 2¹⁶. It sets
  `ScopedFormsNtt3(true)` itself (independent of `HECKE_FORMS_NTT3`). (G) Garner on 4009 x ∈ [0, P₁P₂P₃) (random u128 and the edges
  0, P₁P₂ ± 1, P₁P₂P₃ − 1, …), plain and lazy [0, 2P) residues, against x mod ℓ at ℓ ∈ {5, 65537, 1000003, 134217689}. (G2) (audit F2) the ENGINE's own constants, read from engines at four (ℓ, N) up to the production layout: primes, P₃'s root, Garner's constants, its P₁P₂ mod ℓ and Barrett constant, its layout, each plan's w_L of order exactly L; its own Garner step on 1006 x per engine. (A) products ==
  naive at ℓ ∈ {5, 691, 65521, 65537, 100003, 1000003, 134217689}, N ∈ {1024, 1500, 3001}, block 2²² (nb = 1) and the probe's 2⁹ / 2⁴
  (`ScopedFormsNtt3Probe`, nb up to 188), unequal / short / truncated operands, the square and the all-(ℓ−1) square, SIMD and scalar. (I) ==
  the two-prime engine byte for byte at N = 600001, ℓ ∈ {40009, 65521}, blocks 2²² and 2¹⁷. (B) past the two-prime bound
  (`!FnttApplicable`, `Fntt3Applicable`): the all-(ℓ−1) square == (n+1) mod ℓ at (1000003, 200000) blocks 2²² / 2¹⁴ and
  (134217689, 2²⁰+3); (audit F1) the production block 2²² with nb = 2 (1000003, 2²²+5003) and nb = 4 (134217689, 3·2²²+17, third limb live): closed form and sampled exact dot products at the block edges; random products at 300 coefficients == an exact u128 dot product; E₄² == E₈ and E₄E₆ == E₁₀ (σ₇ / σ₉ by a sieve) at
  (1000003, 200000). (S) forced three-prime spaces == two-prime spaces byte for byte (M_k, S_k) at the sat precision of (12, 1009),
  (14, 691), (60, 691), (102, 10007), (300, 43), blocks 2²² / 2¹²; past the bound, the default route at (26, 1000003, 2·10⁵),
  (36, 1000003, 2·10⁵), (30, 300007, 10⁶) takes the three-prime engine, equals the 2¹⁵-block layout, its first 2501 coefficients equal the
  `HeckeSturmBound` construction under the naive product, and T₂, T₃, T₅, T₇ are in the space on both `HeckeOnCusp` loops. (R) the
  refusal: `FormsSpaceSupported` at the sat precision of (1000, 100003), (466, 100003), (10, 1000003), (300, 1000003) true by default,
  false under `ScopedFormsNtt3(false)` / `ScopedFormsNttCache(false)` / `ScopedFormsFastMul(false)`; (1000, 100003) is N = 16800506,
  nb = 5; under the rollback `BuildModularSpace(26, 1000003, 2·10⁵)` throws naming `FormsSpaceSupported`; `ComputeSaturationDefectCell(10,
  1000003)` is refused at once by the KMAX check by default and by the forms check under the rollback; admitted spaces keep their route.
  (C) non-vacuity counters. Prints `EFFECTIVE HECKE_FORMS_NTT3 three_prime=… spaces= forward= inverse= pointwise_blocks= multiblock_engines=`
  first and last.
- `HeckeFormsFastMulValidation` (slot-24 FNTT) is unchanged in its checks (13842) and output: its (N5) / (N6) refusal checks now run inside
  `ScopedFormsNtt3(false)` (the rollback), since by default those cells are admitted.
### Slot 24 SATPERF (the serial post-module part of sat cells; `docs/implementation/slot24/SATPERF_report.md`)

- **New name `HeckeSatPerfValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL")** — **`standard`**, ≈ 13 s at load ≈ 20, 0.43 GiB, **78 checks** (registered by
  `Registry/Slot24.cpp`; code in `HeckeExt/HeckeModuleStreamValidation.cpp`). The lever `HECKE_SAT_PERF` against its rollback
  (`ringalg::ScopedSatPerf(false)`, the route of `4dd1a7e0`) on a 1-worker consumer pool. (SP) (a) sat cells (142, 7) KMAX 5 (r = 25, K_stab ≥ 3),
  (168, 13) KMAX 2 (r = 29), (60, 5) KMAX 6 (K_cls = 3, a torsion block, the certificate at K ≠ K_cls), (40, 211) KMAX 4: the lever on at pools
  1 / 2 / 4 (`ScopedConsumerPool`), every SAT_DEFECT line byte for byte (`RunCell`'s text), K_run / Lv_run equal, the memo served the
  certificate (hits and misses > 0), uint64_t products ran, no row split at one worker and a split at 2 / 4 workers where r ≥ 24; the
  rollback shows no lever event. (b) planted modules over Z/1009⁶ (r = 30, entries near ℓ^K: the u128 rows of `mul_fast` beside its uint64_t
  rows) and Z/7³ (r = 40): `RationalSystems`, every `Localize` block (exponents, e and the ops, hashed) and its `ReadAlgebra` with the lever on
  at pools 1 / 4 under a `ScopedHostElimHook` equal the lever off at one worker. Lines `SAT_PERF_CELL`, `SAT_PERF_PLANTED`, and
  `EFFECTIVE HECKE_SAT_PERF …` first and last. Roster after FNTT3 + SATPERF **242 = 70 / 150 / 22** (`--all` 220).
- `HeckeSaturationDefectValidation`'s `HECKE_SAT_DEFECT_CELLS` arm prints one more line per cell, `SAT_DEFECT_TIMES n=… ell=… seconds=…
  module=… cert=… forms=… localize=… prepass=… systems=… other=… sat_perf=on|off memo_hits=… memo_misses=… mul_narrow=… mul_wide=…
  mul_parallel=…` (diagnostic; the counters are this cell's deltas; no other line moves). The sat anchor normalisers
  (`docs/cluster/host-B/sat_anchor_check.sh`, `docs/cluster/noctua2/satc/satc_gate.py`) drop this line (SATPERF audit F1).

### Slot 24 DESCENT D0 (the level-1 integral groups by the owner's descent; `docs/implementation/slot24/DESCENT0_report.md`)

- **New name `IntegralDescentGroupsValidation`** — **`standard`**, ≈ 6 s serial, 0.10 GiB, **809 checks** (registered by
  `Registry/Slot24.cpp`; code `Integral/Descent/`). `H^q(SL_2(Z); Sym^n Z^2)`, q ≤ 5, glued ([C] `prop:descent`(2)) from the
  good-prime rank (shipped C_7 at 10007), the shipped C_7 K-mode at the Dickson primes ≥ 5, `Iso^(3)` mod 3^19 on `ring3k` and `Iso^(2)` mod
  2^30 on `ring2k` (W = 61 through `ModCtx<uint64_t>` on a non-certified differential), certified by [C] `prop:certifiedeell` (rank on
  the same `LocalModel(desc, ℓ)` mod 10007). Arms: (Q) build-time denominators (307 elements at 2, 59 at 3); (A) n = 0..20 = [IB]
  Appendix A, 126 cells; (T) the oracle table `slot24/descent_oracle_n128.tsv` on n ≤ 20 and n ∈ {22, 24, 30, 32, 36, 48, 64, 128}
  (174 cells), A/T agreement on 126 cells, [IB] F-4 (`Z/2^j` at `n = 2^j`, j = 5, 6, 7); (D) = comparator (a) (IntegralGroups on C_I to
  degree 4; independent route, shared model family) at n ∈ {22, 32, 44, 60}; (P) `Iso^(2)` to degree 6 there (direct H^4 = H^2,
  H^5 = H^3); (c), (c′) the tree and tree-Bredon comparators reproduce the groups; (C) UCT consistency at the Dickson primes, at 2 and 3
  against `Iso^(ℓ) ⊗ F_ℓ`, and `prop:ellthreeclosed`(3) against the shipped Bredon F_3 value; (Z) every zero-count prime 5 ≤ ℓ ≤ n + 1
  (shipped F_ℓ dims = good-prime dims); (B) Dickson summand counts = `prop:badprimes`(1); (W) the W = 61 route = the K = 30 route
  (n = 16, 32, 40); (N) negative control: Z/2^4 at n = 16 and Z/3^2 at n = 12 refuse d^0; (R) the whole descent is REFUSED (H empty)
  at n = 12 with `Iso^(3)` at Z/3^2 (D0 audit M3); (G) seven guards (ℓ / ring mismatch, rank module over the wrong ring or of the wrong
  dimension, a non-qualifying ℓ′ = 7, a wrong `b_1`) refuse, and the natural K = 4 → W = 61 escalation certifies; (4b) counted. Both names
  run on one serial consumer pool (CPU = wall).
- **New name `IntegralDescentGroupsSlowValidation`** — **`slow`**, ≈ 34 min serial, **1.69 GiB** peak (`/usr/bin/time`; no `clear_refs`), **1823 checks**.
  (T) every cell of the oracle table (774, n = 0..128, ≈ 73 s); `DESCENT_COST n=… t_descent= t_a= t_c= t_c'= ratio_a= ratio_c= ratio_c'=
  share2= share3= shareZ16= … kmode_overhead= struct_vs_c= struct_ii_vs_c= rss_*` (medians of 5 rotated serial rounds, min / max / CPU
  beside) at n ∈ {100, 200, 300} (`HECKE_DESCENT_CELLS`, `HECKE_DESCENT_REPEATS`), with (Z′) the tree-Bredon Betti numbers at every prime
  5 ≤ ℓ ≤ n + 1; the level-N probe `DESCENT_LEVELN N= n= D= t_* rss_pred_*
  rss_meas_* agree=` at (11, 6), (11, 20), (16, 6), (16, 20), (50, 6) (`HECKE_DESCENT_LEVELN_CELLS`), RSS predicted before each cell, the
  `Iso^(ℓ)` torsion checked against the tree comparator with the `Ind` module. Both hooks print their `EFFECTIVE` line.
- `HeckeFreeModelValidation`: the frozen O1 table moved verbatim to `Integral/Descent/DescentOracle.cpp` (one copy); checks and output
  unchanged. Roster after D0 **244 = 70 / 151 / 23** (`--all` 221).

### Slot 24 DESCENT D1 (the level-N integral groups by the descent; `docs/implementation/slot24/DESCENT1_report.md`)

- **New name `IntegralDescentLevelNValidation`** — **`standard`**, ≈ 10 s serial, 0.28 GiB, **1290 checks** (registered by
  `Registry/Slot24.cpp`; code `Integral/Descent/DescentLevelN.{h,cpp}`). `H^q(Γ_0(N); Sym^n Z^2)`, q ≤ 5, glued ([C]
  `prop:descentN`(2)) from the closed-form Betti numbers (`prop:levelorbit`(3) over Q; cross-checked by the shipped `SparseCokernel` at the
  good prime), the sparse cokernel over Z/ℓ^K at each ℓ ≥ 5 of [C] `prop:badprimesN`'s list (`prop:descentN`(7)(b): orbit-wise generators,
  averaging-idempotent columns at fixed points, unit-pivot sparse elimination, the leftover by `SmithLevelsEll`), the ℓ = 3 shortcut when
  ν_3(N) = 0 (`prop:modeltorsion`; else `Iso^(3)`), `Iso^(2)` on `ring2k` (H^5 := H^3 by `prop:descentN`(5)); rank on `Iso^(ℓ)` from the
  certified Betti numbers (`prop:certifiedeell`(4)(c)(ii)); refused as a whole on any uncertified piece or an RSS prediction above the 40 GiB
  ceiling. Arms: (T) the oracle `slot24/descentN_oracle.tsv` (`descentN_oracle.py`: coinduced module on the tree, exact ℓ-adic Smith
  certified by exact ranks; 204 cells) on every cell with D ≤ 100 (140 cells, 840 groups); (R) 75 good-prime cross-checks; (B, Z) C-D2's
  counts against the shipped F_ℓ `SparseCokernel` and the Z/ℓ^K Smith at every prime ≤ n + 2 and ℓ | N of seven cells, incl. ℓ = N = n + 1
  ((5, 4), (7, 6), (11, 10)) and Z/25 at (5, 20); (D) sparse = densely stacked generators = the direct Smith of `C_eq(M_N) ⊗ Z/ℓ^K`
  (`prop:descentN`(7)(a), d^1 onto checked) on six cells, and `SmithLevelsEll` = `elim::invariant_factors` on 18 matrices; (S) the ν_3 = 0
  shortcut = dense `Iso^(3)` on five cells; (Q) rank sources (4)(c)(i) = (ii); (L) level 1: `AssembleDescentN(1, n)` = `AssembleDescent(n)` and
  the direct Smith (the new default of `AssembleDescent`) = the C_7 K-mode at n ∈ {12, 30, 56}; (N) Z/5^2 at (5, 20) not certified and the
  descent REFUSED with H empty; a 1 MiB ceiling REFUSES before `Iso^(2)` starts; (D1 audit m4) a perturbed summand count, a perturbed b_1, the direct-Smith and residual ceilings and the ℓ = 3 gate at ν_3 > 0 all refuse. The ℓ = 3 shortcut is [C] `prop:descentNthree` (pre.17, audit M1); arm (S) checks the gate `Nu3(N) == 0` is its hypothesis on N ≤ 5000.
- **New name `IntegralDescentLevelNSlowValidation`** — **`slow`**, ≈ 12 min serial, 1.70 GiB, **1760 checks** (the env reach run of DESCENT1_report.md §4.2: 91 min, 23.6 GiB): (T) every oracle cell (204, 1224 groups); `DESCENT1_L1_COST n=…
  t_kmode= t_direct= t_sparse= t_descent_d1= speedup_*` at n ∈ {100, 200, 300} (5 rotated serial rounds); `DESCENT1_N_PRED` (RSS of every
  dense piece, printed before it starts) and `DESCENT1_N_COST N= n= D= t_good= t_ell5_sparse= t_ell5_direct= t_three= t_two= t_tree2= rss_*`
  at (11, 20), (16, 20), (35, 10), (50, 6) (`HECKE_DESCENT_N_CELLS`, `HECKE_DESCENT_REPEATS`), the tree at 2 (measured only) checked
  against `Iso^(2)`. One `EFFECTIVE` line.
- `IntegralDescentGroupsValidation` / `…SlowValidation`: `AssembleDescent`'s default ℓ ≥ 5 route is now the direct Smith of
  `C_eq ⊗ Z/ℓ^K` (D1); the slow name's `DESCENT_COST` pins the K-mode, so its line still measures D0's design. Checks unchanged (809 pass).
  Roster after D1 **246 = 70 / 152 / 24** (`--all` 222).

### Slot 24 DESCENT D2 (res / cor and the level-change long exact sequence over Z; `docs/implementation/slot24/DESCENT2_report.md`)

- **New name `IntegralDescentMapsValidation`** — **`standard`**, ≈ 6.5 s serial, **4257 checks** (registered by `Registry/Slot24.cpp`;
  code `Integral/Descent/DescentMaps.{h,cpp}`). For A = Γ_0(N) ⊇ B = Γ_0(MN), Sym^n Z²: H^q(A), H^q(B), H^q(A, B) = H^{q−1}(Cone α), q ≤ 5,
  and res^q, cor^q, j^q, dl^q with their kernel / image / cokernel types over Z ([C] `prop:descentmaps`, pre.19), glued from one local
  piece per prime of S = {2, 3} ∪ B(n, N) ∪ B(n, MN) ∪ {ℓ | [A:B]} (dense `Iso^(2)`; `Iso^(3)` or the ν_3 = 0 cokernel shortcut at 3; the
  cokernel route at ℓ ≥ 5); cohomology as presentations from certified Smith forms with transforms over Z/ℓ^k (every Smith form certified
  against a theoretical rank_Q, precision tracked), exactness checked as subgroups. Arms: (T) `slot24/d2_maps_oracle.tsv` (82 cells, exact
  Python over Z; shares module code with `cd3_descentmaps_check.py`, nothing with `cohomology_app`) on the 57 cells with ψ(MN)(n+1) ≤ 40,
  3933 groups; (E) 1411 exact spots; (I, F) 981 identities (cor ∘ res = [A:B], the split case, c_σ ∘ res = res, res ∘ cor = Nm_G, the
  five-term statement in degree 1); (X) H^3(Γ_0(4), Γ_0(8)) = Z/2 at n = 0, H^3(Γ, Γ_0(11)) = Z/3 at n = 4, 24 H^{≥3}(A, B) = 0; (P) `Iso^(2)`
  to degree 6 at two cells (H^5, res^5, cor^5 computed = q = 3); (D) end groups = D1's `AssembleDescentN`; (N) α perturbed, rank_Q(res^1) ± 1,
  a 1 MiB ceiling: all REFUSED with empty results.
  *(D2 code audit fixes, 2026-10-25, `slot24/D2_code_audit.md`, `DESCENT2_report.md` §8:)* now ≈ 7 s, **4480 checks**; (T) table 87 cells (+5 with a
  prime ℓ ≥ 5 dividing [A:B], F2; a second, independent oracle `slot24/d2audit/d2audit_oracle.py` agrees on all 6003 rows, F6), 60 cells here,
  4140 groups; (E) 1540 spots; (I, F) 1047 identities; (N) + rank_Q(invariants map) + 1, admissible but false, refused by the Smith
  certification (F5); [C] `prop:descentmaps`(2)(g), pre.22, is the precision rule (F1).
- **New name `IntegralDescentMapsSlowValidation`** — **`slow`**, ≈ 5 min serial, ≈ 1.1 GiB: (T) every oracle cell (82, 5658 groups; end
  groups also through D1); `DESCENT2_PREDICT` (printed first) and `DESCENT2_COST … repeats= median_s= min_s= max_s= iso2_median_s= | ell= route
  t= rss= base= pred= smith= prec>=` at (1, 11, 10), (5, 25, 4), (6, 12, 6), (4, 16, 6) in 5 rotated serial rounds
  (`HECKE_DESCENT_PAIR_CELLS`, `HECKE_DESCENT_REPEATS`); a cell predicted above 40 GiB is checked to be refused before any piece. One
  `EFFECTIVE` line. Roster after D2 **248 = 70 / 153 / 25** (`--all` 223).
  *(Audit fixes:)* 87 cells, 6003 groups, **6484 checks**, ≈ 5 min 13 s, 1.0 GiB; the model is recalibrated per class (ℓ = 2 index 2: 17/10,
  index > 2: 19/10; ℓ = 3: 41/20) with ≥ 15 % headroom on every calibration cell (F3), and a cell is refused above **0.9 ×** the 40 GiB ceiling.

### Slot 24 DESCENT D4 (the boundary pair and the cone over Z, glued; `docs/implementation/slot24/DESCENT4_report.md`)

- **New name `IntegralDescentPairValidation`** — **`standard`**, ≈ 20 s serial, < 100 MiB, **7132 checks** after the audit / referee fixes
  (3561 at `d82c7761`; the fixes are listed at the end of this entry) (registered by
  `Registry/Slot24.cpp`; code `Integral/Descent/DescentPair.{h,cpp}`, `DescentPairHecke.cpp`). For Γ_0(N), Sym^n Z², trivial
  character: H^q, H^q(Γ_∂; M_N), H^q_c = H^{q−1}(Cone rres), q ≤ 4 (cochains to 5, [C] `prop:descentpair`(6)'s truncation), and res^q,
  ι^q, π^q with kernel / image / cokernel types over Z ([C] `sec:descentpair`, pre.27, code map (a)–(h)), glued from one piece per prime of
  S = {2, 3} ∪ {5 ≤ ℓ ≤ n+1} ∪ {ℓ | N, n > 0} ∪ B(n, N) (dense `Iso^(2)` with its free boundary; `Iso^(3)` with the circle boundary; at ℓ ≥ 5
  the shipped E8 item-4b pair at level 1, the Bredon pair at level N); D2's certified presentations and maps; every cone differential's
  rank also mod ℓ′ = 10007 on the same O_ℓ-model (code map (c)). Arms: (T) `slot24/d4_pair_oracle.tsv` (32 cells, 1824 groups / map types;
  shares the pair code of `cd7_pair_check.py`, nothing with `cohomology_app`), all equal; (E) 962 spots exact as subgroups over 74 pieces;
  (B) the boundary = the closed form from the cusp widths, |tors H^1(∂)|_ℓ = ∏ n! w_c^n; (5) H^0_c = 0, H^1_c torsion-free, 48 H^{≥3}_c = 0,
  π_* an isomorphism at 3 in degrees ≥ 3, tors H^2_c ⊗ Z_(ℓ) = tors H_0 ⊗ Z_(ℓ) at ℓ ≥ 5, 310 cone ranks mod ℓ′ = the recursion; (P) q_max = 5:
  H^5_c = H^3_c, H^{4,5}(∂) = H^{2,3}(∂); (I) free Iso = Iso^(ℓ), Bredon = E8 pair, on every group and map; (Q) ε^* an identity of complexes
  from the shipped E8 pair onto the Bredon pair, the shipped ModuleCone's invariant factors = the glued H_c by universal coefficients
  (level 1, n ≤ 12); (S) the pair lifts' boundary certificates, p ∈ {2, 3, 5, 7, 11, 13}; (3) the (PC) arm reproduced: 189 identities T′_p = T_p on
  H^q_c / H^q(∂) through Φ^* mod 3^19, torsion included; (H) T~_Iso / T~_Isob by eq:levelcorr from the pair lift (built on demand
  for every prime p ∤ N, owner scope addition), strict identity entrywise, Φ_p a cochain map, T~ = θ̂ at N = 1, 96 operators p ≤ 13,
  288 equivariance squares on cohomology, 369 characteristic polynomials (H^1_c, H^1 vs the referee / τ(p) / a_p(X_0(11)); H^0(∂), H^1(∂)
  vs 1 + p^{n+1}) mod 10007², 2^30, 3^19 at (1, 10), (1, 12), (11, 0), (2, 6), (13, 0), (3, 4); (N) 16 refusals (perturbed rres, false
  rank of res^1, K = 3 at 2, ℓ′ = 5 | tors H_0 at (1, 8), ℓ′ by rule ×2, 1 MiB ceiling, q_max = 3, closed form without widths, p | N ×2,
  p = 4, a perturbed pair lift at p = 2, 7, 13, the bulk-only lift). **Audit / referee fixes** (`DESCENT4_report.md` §11, D4 audit `ab439fc0`,
  C-D7p referee `fd985727`): (H) now p ≤ 23, cochains to degree 5, 150 operators, char T_p on H^1_c / H^1 against the exact integer a_p of
  the eta products at every (cell, p) (compared as residues mod 10007², 2^30, 3^19), 1950 equivariance squares in degrees ≤ 4, T_p T_p′ on
  H^1_c and H^2_c; a torsion arm over Z/5^K, Z/7^K at (1, 8), (1, 12), (5, 4) (tors H^2_c ⊗ Z_(ℓ) ≠ 0 asserted); T~_Isob assembled
  separately and compared entrywise; the E8 identity of complexes and the ℓ′ ranks inside the assembly; (N) 29 refusals, each with its
  `PairRefusal` code (added: an off-Isob lift term ×3 caught by the strict identity alone, `prime_rank_check` off, p = 100003 above the
  lift RSS ceiling (`PredictPairLiftRss`, 4 GiB), two homotopy faults τ + dK + Kd caught by (S)/(B) ×2, q_top = 7, q_max = 6, the
  exception classification).
- **New name `IntegralDescentPairSlowValidation`** — **`slow`**, ≈ 4 min serial, ≈ 2.3 GiB, 55 checks: `DESCENT4_PREDICT` (first) and
  `DESCENT4_COST` of the 2-adic pair piece on dense `Iso^(2)` and of the boundary alone on `Isob^(2)` at (N, n) = (4, 2), (11, 2), (23, 2),
  (47, 2), (71, 2), (97, 2) (D = 18 … 294; `HECKE_DESCENT_BDRY_CELLS`), the full pair at (23, 2), (47, 2) per piece, (997, 2) refused before
  anything is built, the level-1 pair at n = 16, 20, 24, 30, the pair lift at p = 17, 31, 61, 127 (`DESCENT4_LIFT` build / certify cost; T_p on
  the pair at (1, 10), (11, 0)). One `EFFECTIVE` line. Roster after D4 **250 = 70 / 154 / 26** (`--all` 224).

### Slot 24 DESCENT D5 (the tree bulk, [C] `prop:isomodeltree`; `docs/implementation/slot24/DESCENT5_report.md`)

- **New name `HeckeIsotropyModelTreeValidation`** — **`standard`**, ≈ 39 s serial, **1625 checks** (registered by `Registry/Slot24.cpp`;
  code `Integral/Model/{TreeCochains,IsotropyModelTree}.{h,cpp}`, `Integral/Descent/{DescentTree,TreeComparisonArms}.{h,cpp}`). The tree models of
  [C] `def:isomodeltree` and the tree route of the ℓ-local bulk pieces (the default; `HECKE_DESCENT_TREE=0` is the dense rollback). Arms:
  (L1) 46 level-1 cells (n ≤ 40, 48, 56, 64, 96, 128): `AssembleDescent` tree == dense == `descent_oracle_n128.tsv`, the 2- and 3-primary
  pieces equal, (4)(b) on the tree; (LN) the 140 `descentN_oracle.tsv` cells with D ≤ 100: tree == dense == oracle; (D2) the 60
  `d2_maps_oracle.tsv` pairs with ψ(MN)(n+1) ≤ 40: `AssemblePairMaps` tree == dense (groups, res, cor, j, dl, exact spots, identities);
  (E) every d^q built explicitly == the (2)(d) copy (2 and 3, degree 8); (W) the tree at Z/2^61 == Z/2^30; (I) the two rank sources of (1)(d)
  agree on the tree; (B) the Bredon tree at ℓ ≥ 5 == the direct Smith of C_eq; (M) the five tree models certified, (4)(a)'s tables, Φ^ℤ_𝒯,
  Ψ^ℤ_𝒯 by (L) on the code's `Iso` (chain maps, over r_𝒯 / i_𝒯, integral), H_𝒯, H_X, and per ℓ ∈ {2, 3, 5} Φ^𝒯_ℓ Ψ^𝒯_ℓ = id, Φ_𝒯, Ψ_𝒯 chain
  maps, H_ℓ, K, K′ (degree 6); (C) over F_2, F_3, F_5 on six cells: dim H^q(C_I) = dim H^q(C_𝒯) = dim H^q(C_{𝒯,ℓ}), Φ*, Ψ* mutually inverse on
  H^q, the transport hook of (6) on T = 2·id; (N) four mutated (4)(a) tables caught; two `DESCENT_COST … route=tree` / `route=dense` lines with
  (R) RSS ≤ prediction. One `EFFECTIVE HeckeDescentTree route= source=` line.
  **Changed at the D5 audit fixes** (`slot24/D5_code_audit.md`, report §8): ≈ 60 s, **1809 checks**. (L1)'s "(4)(b) on the tree" (a tautology)
  is now `TreeFieldDimsEqual`: the production form over F_ℓ′, ranks computed in the arm, dim H^q == the shipped C_7 Betti numbers, q ≤ 3.
  (E)'s "explicit d^q == copy" (the same branch twice) is now `CheckTreeFormAgainstChain`: `TreeLocalForm` against `TreeModelChain` over F_p
  (p = ℓ and two primes prime to q_ℓ; 9 cells incl. odd n and Ind; ℓ = 2, 3 to q = 7, the Bredon tree at 5, 7), d^{q+1} G⁻¹ d^q = 0, c_q =
  rank of the chain projector, dim H^q equal (108 runs, 1458 statements). New (NT): the ten faults of `integral_model::TreeFault`
  (validation-only, `ScopedTreeFault`) through `AssembleDescent`, `AssembleDescentN`, `AssemblePairMaps` on the tree, (E) and (L1), the
  caught / clean pattern asserted exactly; (G): D0's guards, the uncertified pieces, the K = 4 escalation and the tree descent refused, on the
  tree route (14 cases); (RB): D0 / D1 / D2's standard names rerun in-process under `ScopedDescentTree(false)` (the rollback in `--all`); (R)
  adds `DESCENT_RSS_WHOLE`: the whole level-1 run against `PredictDescentLevel1Rss` (good prime + tree pieces), and the 2-adic window runs on
  the production rank prime.
- **New name `HeckeIsotropyModelTreeSlowValidation`** — **`slow`**: (L1) all 129 oracle levels n ≤ 128 (774 groups), (LN) all 204, (D2) all 87 pairs, each on
  both routes; (M), (C), (N) to degree 8 on 13 cells and ℓ = 7 as well; (S) (4) to degree 17 certified, Ψ^ℤ, H_𝒯 in {−1, 0, 1},
  Φ^ℤ, H_X growing at most linearly (the re-referee's N2; the maxima are printed: ⌊q/2⌋ for both); `DESCENT_ELL5_COST` (direct Smith vs Bredon tree vs sparse at ℓ ≥ 5, n = 100, 200, 300); `DESCENT_COST` (level 1
  n = 100, 200, 300; (11, 20), (16, 20), (35, 10), (50, 6)) and `DESCENT_PAIR_COST` ((4, 16, 6), (10, 20, 6)), both routes, 5 rotated serial
  rounds (`HECKE_DESCENT_TREE_CELLS`, `HECKE_DESCENT_REPEATS`). Figures: `DESCENT5_report.md`. Roster after D5 merged beside D4 **252 = 70 / 155 / 27**
  (`--all` 225).
- **In-place**: D0's `DESCENT_COST`, D1's `DESCENT1_N_COST` and D2's `DESCENT2_COST` pin the dense route (`ScopedDescentTree(false)`), so they
  keep measuring the design of record; every other arm of those validations runs on the default (tree) route and still passes.

### Slot 24 DESCENT D3 (Hecke T_p, p ∤ N, over Z as invariants, [C] `sec:descenthecke`; `docs/implementation/slot24/DESCENT3_report.md`)

- **New name `IntegralDescentHeckeValidation`** — **`standard`**, ≈ 5 s, < 0.1 GiB, **2464 checks** (2144 at `a1375159`, before the D3 audit fix round; registered by `Registry/Slot24.cpp`;
  code `Integral/Descent/DescentHecke{.h,Crt.cpp,Ops.cpp,Torsion.cpp}`). char_Z(T_p | H^1/tors) by residues of the shipped H_{N,p} on the
  sparse cokernel over word primes, the bound b_{p,i} = r + i (n+1) bitlen(p) and Garner in words ([C] `prop:crtcharpolyN`); the level-N
  operator T~ on the free model (eq:levelcorr with D4's certified lift, applied sparsely); its transport Ψ_𝒯* T~ Φ_𝒯* to the tree at ℓ = 2 and 3
  (every N); the torsion read of `prop:torsionhecke`(3) with the choice-free invariants of (1). Arms: (O) the oracle `d3_hecke_oracle.tsv`
  (`d3_hecke_oracle.py`: group cocycles of Γ_0(N) over Z, the C-D4 referee's modules; independent of `cohomology_app`) on the cells with
  ψ(N)(n+1) ≤ 120: 260 char_Z equal coefficient by coefficient, 157 torsion groups of H^1, H^2 at every torsion prime (772 (group, p) rows) equal
  in every invariant (type, P_j, the layer blocks mod ℓ^{e_j}, ker / coker (T_p − c) for every c, the Fitting types), 79 empty groups
  confirmed; (S) 175 residue comparisons: production = char_Z mod ℓ′ = the shipped F_p pipeline (level 1 `RunPipelineModEll`, level N
  eq:levelcorr / `HFrame`) = T~ on H^1(C_I) over F_10007, and (C) 30 pairs T_p T_p′ = T_p′ T_p on H^1 over F_10007; (X) the tree read = the dense Iso^(ℓ) read (T′^(ℓ) = Ψ_ℓ* T~ Φ_ℓ*) = the free-model read
  (T~ itself), every invariant, q = 1, 2, 3, ℓ = 2, 3, 10 cells (D5's arm "the transported T′_p equals the one on Iso^(2)"), and (G) the tree
  read's groups = D5's production groups; (E) H^4 = H^2 with T_p on the tree; (M) T~ (sparse) = D4's dense bulk operator entrywise (2.75 M
  entries), T~ a cochain map on C_I; (W) Garner, the sign, mod 2^64 / 3^40 (word mulmod, the negative case), and the read's Smith engine `SmithLevelsLeft` against D2's `maps::SmithForm` on 75 matrices; (B) the bound, the Eisenstein
  root, `thm:descentcert`(4) at ℓ = 691, n = 10 (T_2 − 667, − 2740: 691^{0,1,2}, as `cd4_hecke_check.out`; T_2 − 2049 a root, T_2 − 479530 refused
  at k = 3); (K) a read at K = 2σ_max − 1 refuses the module ([ModulePrecision]) and keeps P_j and the Fitting types; (N) the faults of
  `hecke3::D3Fault` (validation-only, `ScopedD3Fault`) through the production route, each pattern pinned exactly (a dropped coset, a perturbed
  block term, a dropped Ψ_𝒯 term on eight tree reads; one residue prime; the bound without the Eisenstein term, a perturbed int64 residue and
  a perturbed residue of c_r beyond 2^63 (the held-out check's digits branch) → a `hecke::HeckeInternalError` "[HeldOutMismatch]", a defect, not
  a refusal); (R) the refusal codes (NotPrime, PDividesN, DegreeRange, RssCeiling — the tree read, char_Z and the ℓ ≥ 5 cokernel read, the
  last also at (1, 70000) under the default 40 GiB ceiling —, Lift with D4's code), `HeckeRecord::refused` and the exception
  classification (a `HeckeInternalError`, an ENGINE_CHECK, out_of_range propagate; HeckeOverflow → IntegerCap, overflow_error → DomainCap).
  **S24 ICENSUS-P1** ([C] v1.23.0-pre.39, `docs/implementation/slot24/ICP1_acceptance.md`): **2944 checks, ≈ 8 s** (2944 / 6.4 s also on the WIP
  `a4561cd6`), arm **(L)** the ker / coker width ladder at ℓ = 2, q = 1, level 1, n = 48, 64, 80, 200, P = {2, 3, 5}: every read reads (T_2
  escalated from k_0 = 13 / 15 / 13 / 11 to k = 30 on all four, T_3 and T_5 at k_0); the module = the groups' 2-primary part; an escalated read
  forced back to k_0 refuses as a precision shortfall, a k_0 read forced to k = 30 gives the same text; per c the full ker / coker types against an
  independent 2-adic Smith form (coker [F | diag 2^{a_i}]; ker as the Pontryagin dual's cokernel).
  **D3 audit fix round (2026-10-26)**: (O) also compares the output-rule digest `CharpolyZ::digest()` (FNV-1a-64 over i, sign, c_i mod 2^64,
  c_i mod 3^40) with the digest of the oracle's integers (260 equal) and the record's torsion primes with the oracle's (53 sets); (W) adds 12
  signed ~ 8680-bit products through 300 primes; each arm runs in its own `try`.
- **New name `IntegralDescentHeckeSlowValidation`** — **`slow`**, ≈ 1 min, 0.9 GiB, **2500 checks**: (O) on every oracle cell, (S) with all three primes and seven more cells, (X)
  on 17 cells, and the `DESCENT3_COST` cells (1, 60), (1, 100), (37, 2), (11, 10), (101, 0), (23, 4), (1, 200), (1009, 0), (101, 10), (211, 10)
  (char_Z and the torsion read; figures `DESCENT3_report.md`). Read-only hook `HECKE_DESCENT_HECKE_CELLS` replaces the cells (one `EFFECTIVE`
  line); each `DESCENT3_COST … part=chi` line carries `undetermined=<k> chi_fnv=0x<digest>` (the output rule's checkable value; the full
  text `char_Z = …;fnv=…` follows when r ≤ 40); one `try` per arm and per cost cell. Roster after D3 **254 = 70 / 156 / 28** (`--all` 226).

### Slot 24 DESCENT D5c (the tree cusp pair, [C] `sec:treepair`; `docs/implementation/slot24/DESCENT5c_report.md`)

- **New name `IntegralDescentTreePairValidation`** — **`standard`**, ≈ 24 s serial (20 s of it the (RB) re-run), < 0.1 GiB, **2934 checks** (2819 before the D5c
  audit fixes, `D5c_code_audit.md` m1–m3, and the C-D8b referee's Arm (G); `DESCENT5c_report.md` §9)
  (registered by `Registry/Slot24.cpp`; code `Integral/Model/TreePair.{h,cpp}`, `Integral/Descent/DescentTreePair.{h,cpp}`). The
  2- and 3-adic pair pieces of `AssembleDescentPair` are read by default on the tree cone `Cone(a^(ℓ)*)` of `def:treepair`
  (`HECKE_DESCENT_TREE_PAIR=0` is the dense rollback). Arms:
  * (M) `prop:treepair`(1)(b), (3)(a)–(c), exactly in ℚ[Γ], at ℓ = 2, 3 and 5: the tables, B, a^(ℓ), Φ^ℤ_∂, Ψ^ℤ_∂, Φ^∂_ℓ, Ψ^∂_ℓ and the
    two square homotopies;
  * (X) the closed form = the chain-level pullbacks, entry by entry;
  * (T) tree = dense = `d4_pair_oracle.tsv` on all 32 cells, every group and map type; and `extra_primes = {3}` with n odd at (1, 1),
    (1, 5), where M^{−I} = 0: tree = dense (audit m3);
  * (J) j_Φ, j_Ψ: cochain maps and the strict blocks, entrywise; mutually inverse on H^q_c, H^q(∂) and H^q at 10 cells, among them (1, 0),
    which has 2-torsion in H^4_c;
  * (H) T_p by transport (`ReadTreePairHecke`) = D4's operator through H(j_Φ), H(Φ_𝒯*), H(Φ_∂*), at 32 operators; the η identity checked
    entrywise, on cone degrees 0–3 with none skipped; the **applied** operator's blocks = (T′_𝒯, η_𝒯; 0, T′_∂), each assembled separately,
    entrywise (audit m1); the oracle HECKE rows and the Eisenstein value; the D > 1300 mode (generators + 64 seeded random vectors of
    C^{j+1}_𝒯 and B^j, the C-D8b referee's Arm (G)) forced at 4 small cells: certified, the same read;
  * (Q5) q_max = 5 (audit m2): q ≤ 5, H^5_c included, against D4's `BuildConeHecke(…, 6)` at (1, 10), (11, 0) at 2 and (1, 10) at 3
    (3 operators, 41 identities); the η identity's top cone degree 4 is counted as skipped (`TreePairCertCounts::eta_skipped`);
  * (O) θ* = 1 + K*d + dK*: = id on H_c, with η ≠ 0 and the diagonal not a cochain map; a K leaving Isob is refused [IsobClosure];
  * (N) the planted faults of `integral_model::TreePairFault`, each through the production route, with the patterns pinned:
    * S for S⁻¹ in a is caught at ℓ = 2 for n odd; it gives the same cochains for n even (ρ(−I) = (−1)^n) and at ℓ = 3;
    * the dropped S⁻¹e_U v^U term and 1 − T² in B are each caught at 2 and at 3;
    * +Y_Φ* in j_Φ (T_p at (1, 4) at 2; (1, 4), (1, 10), (11, 0) at 3) and η dropped (θ* at four cells, T_p at (1, 10) at 2 and 3) are
      planted into the operator only, never into η_𝒯 (audit m1), and caught by the applied operator's η block; the catching certificate
      is printed;
    * Arm (G), ported: a d_B-cocycle-valued error shared by the applied operator and η_𝒯 (planted in Y_Ψ*, validation-only
      `ScopedPlantedCocycleEta`), at ℓ = 2, (11, 0), T_3, q = 2: in the forced generators mode **clean without the random vectors, with the
      read of H^3_c changed**; caught with the 64 random vectors and in the default entrywise mode (by the η identity);
      `TREEPAIR_FAULTS caught=19 clean=3`;
    * the refusal codes NotPrime, PDividesN, DegreeRange ×2, RssCeiling ×3 (one through Lift);
  * (RB) `IntegralDescentPairValidation` re-run in-process on the dense rollback.
- **New name `IntegralDescentTreePairSlowValidation`** — **`slow`**, ≈ 3.5 min, 1.5 GiB (78 checks); reach cells via the hook to D = 6 000 (50 min, 22 GiB): `DESCENT5c_report.md` §4. It prints:
  * the `DESCENT5c_COST` ladder of the 2-adic tree piece (47, 97, 191, 283, 383, 499) × 2, with the growth checked against
    `PredictTreePairRss`;
  * the full pair, tree = dense, at (23, 2) and (47, 2);
  * `DESCENT5c_ETA`, the cost of the entrywise η identity and the block check, up to D = 1152, with `rss_pred_mib` and its transport
    term `of_which_transport_mib` (audit N2); `DESCENT5c_FREIVALDS`, the forced generators + random-vectors mode at (97, 2), (191, 2),
    (383, 2), its cost against D;
  * the transport against D4 at (23, 2).

  The read-only hook `HECKE_DESCENT_TREEPAIR_CELLS` replaces the ladder. Roster after D5c **256 = 70 / 157 / 29** (`--all` 227).

### Slot 24 DESCENT D6 (records, campaign and the staged golden event; `docs/implementation/slot24/DESCENT6_report.md`)

`coefficient_ring = Z` is **un-reserved** (stored as k = 0, canonical text `Z`, fingerprint = FNV-1a-64 of `coefficient_ring = Z\n`);
it is honoured by the integral descent only — the record `integral_descent_record/v1` (`Integral/Descent/DescentRecord.{h,cpp}`), the
console verb `descent(N, n, primes)` with the type `DescentRecord` (`Console/Bindings/Descent.{h,cpp}`, read_only, twin rows in
`ReadOnlyTags.cpp` / `read_only_verbs.tsv`) and the campaign's descent cells (`Campaign/CampaignDescent.{h,cpp}`, grid key `level`,
`campaign.md` §17). Every other reader of the ring refuses it by name (`CoefficientRingK(who)`, exit 5). Pins moved in three existing
names (no transcript): `ConsoleErrorValidation` (K) (`set coefficient_ring = "Z"` is legal; `cohomology` under it is the exit-5 refusal,
positioned at its statement), `HeckeReductionPipelineValidation` (K)/(X) (Z parses; the set()-refusal pin moves to the still-reserved
`Z/25`), `ConsoleServeValidation` (D) row "not implemented" (`Z/25`); `CliManualCoverageValidation` gains the token row `level`.

- **New name `IntegralDescentRecordValidation`** — **`standard`**, ≈ 6.5 s, < 0.1 GiB, **725 checks** since S24 FMTMP's arm (X) (+90; 635 at the ed.1 binary, ICP1/ICP2 included; 602 before them; 591 before NB-TOURFIX's arm (Z), 512 before the D6 audit fixes;
  registered by
  `Registry/Slot24.cpp`). Arms, one `try` each:
  * (S) the setting: `Z` parses, round-trips, its fingerprint; `Z/<m>` stays reserved; `CoefficientRingK` refuses under Z, naming the site;
  * (F) the refusal closure under Z: `EquivariantCohomologyOnK`, `HeckeOperatorOnK`, a `RequireFieldCoefficientRing` site refuse by name;
    `BuildDescentRecord` under F_ell / Z/ℓ² is refused; console: a field verb under Z exit 5, `hecke` after `set` exit 5, `descent` under
    Z exit 0, under F_ell exit 3, p | N exit 3, beyond the cost bound exit 3 (N, n, D, and since the D6 audit (m2) Σp ≤ 100); (D6 audit
    m1) every scalar-argument field verb (`dickson_*`, the six presets, `sturm_bound`, `u_ell_decision`, `bernoulli_mod`,
    `glover_factors`, `lfunction`, `kummer_unit`, `hida_tower`, `level_n`, `nebentypus`, `forms_algebra`, `hida_lambda`) and the five
    self-refusing ones refuse Z and Z/ℓ² at their statement, exit 5 (51 calls); `campaign_plan` of a Z spec lists its descent cells (N1);
  * (R) the record against three oracles outside the build on 13 cells ((1, 2), (1, 3), (1, 4), (1, 6), (1, 10), (1, 12), (2, 2), (2, 3),
    (2, 6), (3, 2), (5, 2), (7, 2), (11, 0)): every group (`descentN_oracle.tsv`, `descent_oracle_n128.tsv`), every char_Z
    (`d3_hecke_oracle.tsv` CHI), every torsion Hecke module (TORS; an empty group where the oracle has no row), every pair group
    (`d4_pair_oracle.tsv`);
  * (J) the schema and the hash input: deterministic digest; no timing / RSS / route / K / `derived_from` in the hashed body (and the JSON
    does carry the timings, so the check is not vacuous); primes `[3, 2]` give the record of `[2, 3]` (N3); a second non-default setting
    (`locality = strict`) changes the digest and the fingerprint, not the invariants; the JSON keys and the per-complex fields
    (`q_max` 3 / 4, `truncated` true, `derived`; the pair's `compact` with `derived_from` `["bulk","boundary"]`); K certified at 2, 3 and every bad prime; refusals (p | N, non-prime p, N = 0, a part
    above the RSS ceiling: status `refused`, the groups EMPTY);
  * (K) the campaign: `ext`, `ell`, `r`, `q`, a non-prime p, a p dividing a section's level (N2), a section without `n_sym` refused under
    Z, `level` refused elsewhere; the
    plan's ids `desc_N<N>_n<n>[_p..]_s<fp>`; the field job loop refuses a Z spec; a two-cell run into a temporary directory (cell files
    with the trailer, `summary.tsv`, `index.json`), resume skips both;
  * (G) the staged golden points (`GoldenDescentRecords()`, not in `ComputeAll()` until the owner-gated landing): their keys equal
    `docs/implementation/slot24/d6golden/expect.tsv` (156, all tier A), none is in the reference, two computations agree hash for hash,
    and (N5) the values equal the pin `d6golden/values.tsv` line for line (rows, cols, hash; from the audit's ten byte-identical
    emissions). **On the landing branch `s24-d6golden`** (G) reads instead: every staged key is **present** in the reference with equal
    rows, cols and hash (M1);
  * (B) (D6 audit, [C] sec:recordschema item 7 (h)) the rollbacks keep `record_fnv1a64`: five cells under the default,
    `ScopedDescentTree(false)` and `ScopedDescentTreePair(false)` (the routes differ, the bodies are equal), and (1, 12) through the real
    env variables `HECKE_DESCENT_TREE=0` / `HECKE_DESCENT_TREE_PAIR=0` in a child process.
  * (Z) (slot-24 NB-TOURFIX, 11 checks) the factored char_Z of the console member `DescentRecord.charpoly_factored`: the factoriser
    `NumberField/IntPolyFactor.h` (Yun + Zassenhaus) on eight constructed products with known factorisations (incl. X^4 + 1,
    X^4 − 10X^2 + 1, X^8 + 1, irreducible over Z and split modulo every prime, so the recombination is exercised), on all 235 char_Z of
    `d3_hecke_oracle.tsv` (each product verified), and the console member at (1, 10) (`(X + 24)^2 (X - 2049)`) and (11, 0)
    (`(X + 2)^2 (X - 3)`);
  * (X) (slot-24 FMTMP, 90 checks; [C] sec:recordschema item 7 (l)) the faithful char_Z coefficients beyond 2^63 (canonical signed hex,
    `CharpolyEntry::exact`, JSON `big`, one hashed body line each): (X1) `ExactHex` against an `nf::BigInt` mixed-radix rebuild on 200
    seeded numbers (1 .. 40 primes near 2^30, sign boundary included) and `ExactHexModQ` against BigInt's remainder at six moduli
    (2^64, 3^40, 2^64 − 59, …); the canonical form; (X2) at (1, 22), (1, 26), (2, 10), (5, 6) (31 big coefficients): each decodes to D3's
    c mod 2^64, mod 3^40 and sign (a D3 rerun), every coefficient to `ShippedResidueCharpoly` at every residue prime of the list, the
    held-out prime and 1000003, 999983 (876 residues); output rule (5)'s digest recomputed from the integers is the entry's; the
    integers equal `d3_hecke_oracle.tsv` in decimal (12 char_Z); one body line / `big` item each; (X3) (1, 12) has no `big` key and no
    exact line (bytes and `record_fnv1a64` unchanged), a perturbed hex digit moves `record_fnv1a64`; (X4) the JSON of (1, 22) decoded by
    `docs/integral_census/icensus_exact.py` (python3 -I; SKIPPED without python3) gives the same integers and `verdict=OK`; the console
    `descent(1, 22).charpoly[2].exact[5]`. **Env arm** `INTEGRAL_DESCENT_EXACT_CELLS="N:n,…"` (read-only, not an emitter): **replaces**
    (X2)'s cells, prints `EFFECTIVE IntegralDescentRecordValidation arm=X cells=<k>` and per cell `EXACT_CELL N= n= record_fnv1a64= big=
    residues_checked= json_bytes= verdict=`; the records are built with groups + Hecke only (`pair = false`, as the campaign's `parts = groups,hecke`: with the pair, (90, 20) took ≈ 27 GB, FMTMP_acceptance.md); no D3 rerun (the digest recomputed from the integers stands in for it), residues at a sample
    of the list (first two, middle, last two) and the two outside primes; (X4) is skipped. Cost = one record build per cell (e.g.
    (90, 20): ≈ 48 min CPU at 2 threads, ≈ 2.3 GB, the ed.1 figures) plus 7 residue pipelines per p.

  Roster after D6 **257 = 70 / 158 / 29** (`--all` 228).

### Slot 24 PAR-D2 (the blocked, threaded, SIMD `maps::SmithForm`; `docs/implementation/slot24/PARD2_report.md`)

D2's minimal-valuation Smith form with transforms is replayed with the oracle's exact pivot sequence (the first unit in row-major
order, else the first entry of minimal valuation): deferred (panel) row updates, lazy column swaps, a monotone row-valuation bound that
lets the search skip rows exactly, `std::thread` workers (PAR-D2 shipped `ENGINE_THREADS` capped at 16 over the hardware count; since PAR-UNIFY the shared descent pool, below: `ENGINE_THREADS` in [1, 256], default the CPU affinity count capped at 64) and AVX-512 / AVX2 / scalar kernel bodies
(`Integral/Descent/DescentSmith{,Kernels}.{h,cpp}`). The transforms stay FACTORED (multipliers F below, normalised pivot rows G above the
diagonal; L = F⁻¹P, L⁻¹ = PᵀF, R = QG⁻¹, R⁻¹ = GQᵀ); `BuildPres`, `InducedMap`, `LatticeQuotient` read only the rows they use. Under the
lever also: D2's `Mul` (threaded SIMD), the cone's cochain-map check (streamed `r d = d_d r`, no transposes), `D^{q-2}` consumed by its
Smith form, and the tree pair's RSS model (3 instead of 7 c_max² words). Rollback `HECKE_DESCENT_SMITH_BLOCKED=0` (read-only).

- **New name `IntegralDescentSmithBlockedValidation`** — **`standard`**, ≈ 11 s, < 0.5 GiB, ≈ 18 400 checks (registered by
  `Registry/Slot24.cpp`). Arms:
  * (R) 819 random matrices (ℓ^k = 2^30, 2, 2^5, 3^19, 9, 5^13, 7^11, 691³, 46337²; 13 shapes incl. empty and thin; dense, low rank with
    prescribed torsion, sparse, zero / repeated / divisible rows, all divisible, {-1, 0, 1} differentials, mixed valuations): σ, L, L⁻¹ᵀ, Rᵀ,
    R⁻¹ equal to `SmithFormOracle` entrywise at threads 1 / 2 / 7 / 16, panels 1 / 5 / 32 and every SIMD path of the CPU; the row
    accessors and L·B against the dense transforms;
  * (D) every Smith input with r·c ≥ 400 of D2's level pairs (tree and dense routes, ℓ = 2, 3, ≥ 5), D5c's tree pair (23, 2) and D4's
    dense pair (11, 2), captured (277) and replayed: full transforms equal at threads 1, 16 and at 7 on each SIMD path;
  * (C) the callers on their captured inputs, lever on vs off, field by field: 188 `BuildPres` (+ 123 false-rank refusal probes: the same
    refusal text) and 373 `InducedMap` (incl. `LatticeQuotient`): precision, exponents, `gensT`, `coord`, F, Lf, kernel / image / cokernel;
    then 13 pipeline runs (`AssemblePairMaps` on the tree / dense routes incl. ℓ ≥ 5 and two negative controls; `AssembleDescentPair` tree
    and dense): every group, map type, count (`smith_forms` included) and refusal equal;
  * (P) `SMITH_BLOCKED_COST r= c= ell= rank= oracle_s= blocked_s= threads= simd=` on the largest captured input (printed, not gated).

  Roster after PAR-D2 **258 = 70 / 159 / 29** (`--all` 229).

### Slot 24 PAR-2K (the threaded ring2k / ring3k Smith of the integral descent; `slot24/PAR2K_report.md`)

The 2-adic and 3-adic valuation-level Smith forms (`ring2k::smith`, `ring3k::smith_levels`) run on many threads inside the descent's
Smith calls (`DescentTree.cpp`, `DescentAssembly.cpp` open `smithpar::ScopedEnable`; every other consumer stays serial). Threaded: the
trailing GEMM (row / column tiles of C), the panel TRSM (column tiles), the panel itself (a left-looking "lazy" panel: the pivot search
brings only the rows it reads up to date, every other row receives the panel's pivots in one parallel region per panel), and per level
the F_2 / F_3 matrix build, the column permutation and the Schur halving / division by 3. Every entry receives the serial arithmetic in the
serial order per row; the pivots are the serial ones; so every output is bit-identical at every thread count. Pool: a private persistent
pool (`src/ModArithmetic/Binary/SmithPar.{h,cpp}`), `ENGINE_THREADS` workers (default hardware concurrency, cap 256; since PAR-UNIFY
the CPU affinity count capped at 64, shared with PAR-D2, below), lever
`HECKE_DESCENT_SMITH_MT` (table below).

- **New name `DescentSmithMtValidation`** — **`standard`**, ≈ 3–5 s, < 0.2 GiB, **1793 checks** (registered by `Registry/Slot24.cpp`;
  code `Integral/Descent/DescentSmithMtValidation.{h,cpp}`). Thread counts 1, 2, 7, 16 (scoped), size threshold lowered to 0 so that every
  step splits. Arms:
  * (R2) ring2k on random inputs (uniform, rank-deficient products, 2-power scaled rows; up to 261 × 300), rungs u8 / u16 / u32 / u64 /
    u128 / WordN<4>, on **every available kernel path** (portable, AVX2, AVX-512 — so AVX-512 forced off is covered): `echelon_blocked`'s
    whole matrix and `EchelonInfo` under both pivot rules (FirstOdd after the F_2 profile, MinValuation), `smith` (sigma, level_ranks),
    `howell` (H entrywise, pivots) equal to the serial code; `smith` = `smith_naive` (u32);
  * (R3) ring3k at k = 19 and 7 (the dense blocked variant): `smith_levels`, `howell_blocked` (H entrywise) equal to the serial code, with the
    engine GEMM on its portable and AVX-512 paths; `smith_levels` = `smith_naive`;
  * (R2)/(R3) non-vacuity: split panel regions and parallel regions counted > 0;
  * (D) real descent inputs: `RunTreeLocalPieceN` at ℓ = 2 (q_top 4) and 3 (q_top 6) on (11, 6), (13, 10), (25, 4), (9, 8), (7, 20) — every
    differential's rows, cols, r_K, rank, W, nonunit and the torsion equal to the serial run; `AssembleDescentN(11, 6)` H^0..H^5 on the tree
    and on the dense rollback (`ScopedDescentTree(false)`: `DescentAssembly.cpp`'s Smith call site) at T = 7, 16; parallel regions > 0;
  * (L) the lever: outside a `ScopedEnable` `threads()` = 1; `ScopedLever(false)` → `threads()` = 1 and no region at all (the serial code
    verbatim), lever on = off; the EFFECTIVE line printed.
  * Read-only measurement hooks (print `EFFECTIVE DescentSmithMtValidation arm=<hook> cells=<k> …`, then `PAR2K_BENCH` / `PAR2K_CELL`
    lines): `HECKE_DESCENT_SMITH_MT_BENCH`, `HECKE_DESCENT_SMITH_MT_CELLS`, with `_THREADS`, `_REPEATS`, `_PANEL` (table below).

  Roster after PAR-2K **258 = 70 / 159 / 29** (`--all` 229).

  Roster after the integration of PAR-D2 and PAR-2K (`s24-par-integrate`) **259 = 70 / 160 / 29** (`--all` 230).

### Slot 24 PAR-UNIFY (one descent thread pool, the 128-wide panel, the audit follow-ups; `slot24/PARUNIFY_report.md`)

PAR-2K's ring2k / ring3k Smith and PAR-D2's `maps::SmithForm` now share **one** persistent pool per process
(`engine::smithpar`, `src/ModArithmetic/Binary/SmithPar.{h,cpp}`; PAR-D2 no longer creates a pool per factorisation or per product). The
thread budget `smithpar::default_threads()` is `ENGINE_THREADS` when it is an integer in [1, 256] (0 / unset = the default; above 256
clamped with a warning; `-1`, `abc`, `16x` warn once and take the default), else the process's **CPU affinity count**
(`sched_getaffinity`: taskset / Slurm / `numactl --cpunodebind` allotments) capped at 64 — not `hardware_concurrency`. One region
runs at a time; a nested call or a call while another thread holds the pool runs serially (same values), so several descents in one
process never oversubscribe. Kits that run several processes per node must set `ENGINE_THREADS`; on multi-socket nodes one process
per socket under `numactl --cpunodebind=k --membind=k`. Both Smith forms use the same work threshold (`smithpar::min_work()`, 2^20
multiply-adds; a step below 2 × it stays serial; a function of the shape only). The threaded ring2k / ring3k route runs the LU with a
**128-wide panel** (`HECKE_DESCENT_SMITH_PANEL=64` restores 64; the serial route keeps `Params::panel` = 64; since slot-24 PANEL-IMPL the
ring2k width is size-dependent, 512 from 12 000 rows — see the `HECKE_DESCENT_SMITH_PANEL` row of the env table). The EFFECTIVE line
prints at start-up and at exit and reports the actual mode (table). No new name; two validations widened:

- `DescentSmithMtValidation` — **`standard`**, ≈ 5 s, **6111 checks** (was 1793). New arms: (E) edge shapes 0×7, 7×0, 1×1, 1×200,
  200×1, 65×63, 129×257, 140×140; all-zero, high-valuation ties, entries ≡ 0 mod 2^k with garbage above bit k (k ≪ W: u32 k = 5,
  u64 k = 7, u8 k = 3), duplicate rows; ring3k k = 19 and 2; at T = 3, 16, **64** × panel **64, 128**, `echelon_blocked` /
  `smith` / `howell` (`smith_levels` / `howell_blocked`) equal to the serial panel-64 run entrywise; a 64-thread region counted;
  (S) the shared pool: 2000 regions at 5 / 64 threads (every task exactly once), an exception reaching the caller and a clean region
  after it, nested regions, six concurrent outside callers of the threaded `smith` equal to serial.
- `IntegralDescentSmithBlockedValidation` — **`standard`**, ≈ 12 s, **18 553 checks** (was 18 408). New arm (B) (audit PARD2 M1):
  nine adversarial matrices ≥ 300 × 300 (rings 2^30, **(2^31 − 1, 1)** (the Montgomery limit), 46337², 3^19; pure ties of
  valuation 1, valuation ladders, low rank with torsion, structured rows) at threads 16 and 64, work threshold default and 0: σ,
  L, L⁻¹, R, R⁻¹, the row accessors, L·B and `MulMod` equal to the oracle; parallel regions counted > 0.

  Roster unchanged **259 = 70 / 160 / 29** (`--all` 230).

### Slot 24 PAR-F2 (the lazy F_2 / F_3 echelon with a transposed search window; `slot24/PARF2_report.md`)

On the threaded descent route (`smithpar::f2_route()`; lever `HECKE_DESCENT_SMITH_F2_MT`, table below) the per-level F_2 / F_3 rank
profile runs `binary::echelon_lazy` (strip clears batched per pass over row tiles; the pivot search on a transposed 512-column window of the
reduced rows) and the level passes are threaded / vectorised (zero test, `pack_low_bits`, trit planes, `smithpar::compact_rows`; the
device route's L-store copy and left-columns permutation). (1000, 20): the F_2 echelon 63–103 s → 5–8 s. No new name:

- `DescentSmithMtValidation` — **`standard`**, ≈ 14–20 s, **8649 checks** (was 6111). New arm (F): `echelon_lazy` == `echelon` (whole
  matrix, rank, pivots) for F_2 and F_3 on 11 shapes (up to 3000 × 1100 and 300 × 9000) × nine adversarial kinds (dense, sparse, low
  rank, zero, bottom rows, wide zero column bands, duplicated rows, noisy identity, late hits) at T = 1, 2, 7, 16, 64 on the portable,
  AVX2 and AVX-512 row paths (AVX-512 forced off covered), small cases also against `rref_naive`; `pack_low_bits` per path;
  `compact_rows` == the serial `memmove` (direct and buffered waves, T = 2, 16, 64); non-vacuity counters. (L) adds the F2 lever (off:
  no lazy call; on == off for ring2k and ring3k Smith).

  Roster unchanged **261 = 70 / 162 / 29** (`--all` 232).

### Slot 24 PAR-ASM (the descent's remaining serial assembly stages; `slot24/PARASM_report.md`)

The stages left serial after PAR-D2 / PAR-2K / PAR-L1, made parallel, deterministic and value-identical (`Integral/Descent/DescentParAsm.{h,cpp}`:
the levers, the worker count, two fork-join primitives on `std::thread`, `ENGINE_THREADS` workers, default hardware concurrency, cap 256):
(a) the tree pair's complex assembly `BuildTreePairComplex` (every root matrix d^q, d_B^q, a^{*,q} one task, the periodic copies tasks;
its two certificates streamed through PAR-D2's `maps::ProductsEqual`; DescentPair's `MatMulZ` on PAR-D2's threaded `MulMod` for reduced
operands) and the identity-like cone maps j, π (D4/D5c `RunPairLes`) and j, dl (D2's `DensePiece`) through `maps::InducedMapEmbed` (a column
block of Y.coord times a column block of X.gens; no dense c × c f); (b) the level-1 groups route's ℓ ≥ 5 Bredon-tree primes
(`AssembleDescent`) concurrently, at most `floor(0.9 cap / PredictTreeBredonRss(n + 1))` at a time (96 D² bytes + 32 MiB per prime,
`DescentOptions::rss_cap_bytes`, default 40 GiB); (c) `AssembleDescentPair`'s ℓ ≥ 5 pieces (the E8 pair at level 1, the Bredon pair at level N)
concurrently after the ℓ ≤ 3 pieces, at most `floor(0.9 cap / PredictPairRss(3, D, T))` at a time; their `PieceReport`s carry the joint RSS
sample. Results land in per-index slots and are consumed in the serial order; an exception re-throws from the lowest index (the serial loop's
first); workers run under the caller's thread-local math settings; nested regions are serial; `ENGINE_DEVICE` ≠ cpu keeps (b), (c) serial.
Not done: the level-N record's sparse ℓ ≥ 5 cokernels (`AssembleDescentN`), the tree pair's ℓ' rank source (one rref per cone degree).

- **New name `IntegralDescentParAsmValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL")** — **`standard`**, ≈ 9 s, ≈ 0.5 GiB, **372 checks** (registered by `Registry/Slot24.cpp`;
  code `Integral/Descent/IntegralDescentParAsmValidation.{h,cpp}`). Every arm compares the threaded run (levers on, scoped worker counts
  1, 2, 7, 16) with the serial code of record (the three levers off, scoped):
  * (X) the primitives: every index once; the LOWEST throwing index re-thrown, every lower index run; row blocks cover every row once; a
    nested region stays on its worker; the caller's `coefficient_ring = Z` in force on every worker; `JointWorkers` (0.9 × ceiling, thread
    count, an item above the ceiling alone);
  * (M) `pair::MatMulZ` on random reduced operands (dense and sparse, up to 4 100 inner) mod 2^30, 3^19, 5^13, 691^3, entrywise;
  * (B) `BuildTreePairComplex` at ℓ = 2 on (23, 2), (47, 2), (11, 4), (283, 2) and ℓ = 3 on (23, 2), (11, 4): c, c_B, every d^q, d_B^q, a^{*,q}
    entrywise; the fault `CuspOneMinusT2` throws the same certificate message on both routes;
  * (E) `RunPairLes` on the tree pair at (ℓ, N, n) = (2, 23, 2), (3, 23, 2), (2, 11, 4) with `HECKE_DESCENT_EMBED_MAP` scoped on / off: every
    presentation and every map (F, Lf, ZL, kernel, image, cokernel) equal; the structured path counted;
  * (P) `AssembleDescentPair` at (1, 30), (11, 4), (23, 2): every group, map type, count, closed form, piece report (route, ranks, counts,
    verdict) and refusal equal; the ℓ ≥ 5 pieces ran min(t, #pieces) at a time; the joint growth within the joint prediction; a ceiling of
    three piece predictions bounds the concurrency;
  * (L) `AssembleDescent` at n = 100, 202: H and every ℓ ≥ 5 run equal; min(t, #primes) at a time; growth within the joint prediction; a
    ceiling of 2.5 predictions runs 2 at a time, of one prediction 1;
  * (R) `BuildDescentRecord` body and digest at (1, 30), (11, 4) at 1, 7, 16 workers.
  Prints `EFFECTIVE HeckeDescentParAsm asm=… ell=… embed=… threads=… device=… row_regions=… index_regions=… embed_maps=… ell_concurrent=…
  ell_rss_limited=…` (+ `ln=…` since PAR-LN, and `ln_concurrent=… ln_rss_limited=…` since integration 3: the level-N sparse stage
  counted apart, PAR-LN audit A3).  `DESCENT1_N_COST` / level-N `DESCENT_COST` end in `ell5_timing=residual-only|full` (audit A6).

  Roster after PAR-ASM **260 = 70 / 161 / 29** (`--all` 231).

### Slot 24 PAR-GPU (the opt-in device-resident 2-adic Smith LU of the integral descent; `slot24/PARGPU_report.md`)

Under `ENGINE_DEVICE=gpu` (the calling thread's policy, as for the G2 device elimination) the LU of the 2-adic Smith form
(`ring2k::echelon_blocked`, rungs u32 / u64, i.e. Z/2^32 and Z/2^64) runs with its working matrix resident on the device: per panel (64 columns, 128 on
the threaded route since PAR-UNIFY) the host fetches the panel, factors it (PAR-2K's lazy panel, the host arithmetic), the device replays the swaps, runs the unit-lower
TRSM and the trailing GEMM C -= L U in native wraparound integer arithmetic (exact: one answer per entry), with a one-panel lookahead on a
second stream. When the matrix does not fit, it is tiled in phases: a window of columns is factored on the device, the columns right of it
pass through the device in slabs that receive the window's panels (replayed from a host store of L factors bounded by
`ENGINE_GPU_SMITH2K_HOST_MB`, default 4096 MiB per phase), the columns left of it receive the window's swaps on the host. Default `cpu`: no
CUDA call at all. Files:
`src/ModArithmetic/Binary/Ring2kDevice{.h,.cpp,LU.h}` (table + driver; dispatch at the top of `echelon_blocked`), `src/Cuda/CudaRing2k.h`,
`ring2k_device.cu` (stub `CudaRing2kStub.cpp`), `Integral/Descent/DescentSmithGpu.{h,cpp}` (policy, installation). Not on the device: the
ring3k (3-adic) LU, the F_2 echelon (M4RI), the per-level permutation and Schur halving.

- **New name `DescentSmithGpuValidation`** — **`standard`**, ≈ 30–36 s on the RTX 5070 Ti, < 0.3 GiB host, < 0.1 GiB device, **12589 checks**
  (registered by `Registry/Slot24.cpp`; code `Integral/Descent/DescentSmithGpuValidation.{h,cpp}`). Without a device (or in a
  CPU-only build) it prints `[SKIP] DescentSmithGpuValidation: no usable CUDA device (<reason>) …` and passes. The device is forced by a
  scoped override (`smith_gpu::ScopedForce`, the size floor off); every comparison is device against host, entry for entry:
  * (K) the device GEMM C -= L U against the host kernel on 10 edge shapes (1 … 300 rows / columns, K = 0 … 130), u32 and u64;
  * (E) `echelon_blocked`: the whole matrix and `EchelonInfo`, MinValuation and FirstOdd (after the F_2 profile), u32 k = 30 / 32 / 7 and
    u64 k = 61 / 64 / 13, six adversarial input kinds (uniform, rank-deficient products, 2-power scaled rows, sparse 2-powers, odd entries
    only in the bottom rows, nearly all even), shapes 37 × 41 … 300 × 170 plus one row / one column / zero, panel widths 64 / 16 / 128 / 1,
    host threads 1 and 16, resident and tiled (window capped at 128 / 16 columns; the L store at its default budget and capped to one panel
    per phase: the most phases, replays and host permutations); each case also checks that the device (and, when capped, the tiled
    route) really ran;
  * (S) `smith` (sigma, level_ranks) and `howell` (H, pivots) through the device LU, u32 and u64;
  * (D) real inputs: `RunTreeLocalPieceN` at ℓ = 2 on (11, 6), (13, 10), (25, 4), (9, 8), (7, 20), resident, tiled (cw = 128) and tiled
    with one-panel phases; every
    differential and the torsion equal to the host run; `AssembleDescentN(11, 6)` tree and dense H^0..H^5;
  * (V) the `ENGINE_VERIFY_DEVICE` twin (scoped): every device LU re-run on the host and compared, counted;
  * (F) a simulated CudaError at session open: one fallback, the host LU ran, same values;
  * (P) the policy: thread-local `cpu` → `plan()` declines; `gpu` below the size floor declines; `gpu` at 5000 × 5000 u32 plans resident;
    non-vacuity: device LUs, tiled LUs, panel replays and lookahead panels counted > 0.
  * Mutation controls (temporary edits, not committed): the swap kernel dropping the last swap of a panel → 4 failing + an exception;
    the lookahead fetched before its columns' update → failing + an exception; the tiled route's host row permutation of the columns left
    of the window dropped → 470 failing (the k < W cases with skipped columns and the real inputs carry it).
  * Read-only measurement hook `HECKE_DESCENT_SMITH_GPU_CELLS=<N>:<n>[,…]` (+ `HECKE_DESCENT_SMITH_GPU_ARMS=gpu` for the device run only):
    `RunTreeLocalPieceN` at ℓ = 2 on the host and on the device, compared, `PARGPU_CELL N=… n=… D=… ell=2 arm=cpu|gpu t_piece=… t_smith=…
    device_lus=… tiled=… slabs=… panels=… dev_s=open:…,fetch:…,panel:…,step:…,host:…,close:… d=[…]`; prints
    `EFFECTIVE DescentSmithGpuValidation arm=HECKE_DESCENT_SMITH_GPU_CELLS cells=…`.

  Roster after PAR-GPU **260 = 70 / 161 / 29** (`--all` 231) on its own branch; after the integration of PAR-UNIFY, PAR-ASM and PAR-GPU (`s24-par-integrate2`) **261 = 70 / 162 / 29** (`--all` 232).

### Slot 24 PAR-LN (the level-N sparse stage of `AssembleDescentN` made concurrent; `slot24/PARLN_report.md`)

`RunSparseCokernelSmith` is split into `EliminateSparseCokernel` (generators + sparse unit-pivot elimination, single-threaded, host only;
returns the residual rows with dense column numbers and frees the rest) and `FinishSparseCokernelSmith` (the residual ceiling rule of
record, `SmithLevelsEll`, the certificate); the one-call function is their composition. In `AssembleDescentN` the good prime's shipped
`SparseCokernel`, the ℓ ≥ 5 eliminations and the ℓ = 3 shortcut's elimination (ν₃ = 0) run concurrently, at most
`floor(0.9 cap / PredictSparseElimRss(N, n))` at a time (`par::JointWorkers`, PAR-ASM's `ForEachIndex`: full thread context, `parworker`
flag), then everything is consumed in the serial order (good prime, each ℓ ≥ 5 residual, the shortcut's residual), an exception re-thrown
where the serial code meets it first. The level-N width (`ScopedLevelNWidth`) and the generator order (`ScopedGeneratorOrder`) are now
registered thread-context options, so workers see the caller's. Files: `Integral/Descent/DescentLevelN.{h,cpp}`, `DescentParAsm.{h,cpp}`
(lever (d)), `Hecke/HeckeLevelN.cpp`, `Hecke/HeckeLevelNSparse.cpp` (the two registrations). `HeckeIsotropyModelTreeSlowValidation`'s
level-N `DESCENT_COST` line now also prints `t_ell5=` and `t_good=` (print only).

- **New name `IntegralDescentParLnValidation` (**now `slow`**, S24 VAL-IMPL; see "Slot 24 VAL-IMPL")** — **`standard`**, ≈ 30 s, < 0.5 GiB, **227 checks** (registered by `Registry/Slot24.cpp`;
  code `Integral/Descent/IntegralDescentParLnValidation.{h,cpp}`). Cells (11, 12), (7, 20), (5, 24), (11, 24), (35, 30) (2–4 bad primes,
  Borel and Dickson counts, the ℓ = 3 shortcut and `Iso^(3)` both occur):
  * (S) sparse == dense: each bad prime's split run equals the one-call run field by field, and its rank and valuations equal
    `DenseCokernelSmith` (the same generators stacked densely); the threaded assembly's runs equal them at 1, 2, 7, 16 workers;
  * (T) threaded == serial: `AssembleDescentN` with the lever on (scoped 1, 2, 7, 16 workers) against `HECKE_DESCENT_PAR_LN` off: H,
    refusal, good prime and its h⁰ / h¹, every `SparseSmithRun` (counts, units, residual shape, r_K, certificate, torsion), the shortcut,
    the 2- and 3-adic torsion; items = 1 + #bad + [shortcut], workers = min(threads, items), the counter, the joint prediction;
  * (P) ceilings of 2.5 and 1 predictions give 2 and 1 items at a time (counted RSS-limited, values unchanged); the stage's measured growth
    within the joint prediction; a ceiling below the smallest residual refuses the same primes with the same text in both modes;
  * (E) K = 1 (an `ENGINE_CHECK` in every elimination): the same exception in both modes at 1, 2, 7, 16 workers;
  * (R) `BuildDescentRecord` body and digest at (11, 12), (7, 20), lever off and on at 1, 7, 16 workers.
  * Read-only measurement hook `HECKE_DESCENT_PARLN_CELLS=<N>:<n>[:full|:no2][,…]`: per cell the stage serial, with one worker
    (the single-item RSS growth) and threaded, compared, one `PARLN_COST N=… n=… D=… items=… workers=… t_good=… t_ell_serial=…
    t_sparse_serial=… t_stage_par=… gain=…x fill_max=… residual_max=… growth_one=… pred_one=… growth_joint=… pred_joint=…` line
    (`:full` adds the whole call and the shares, `:no2` runs the 3-adic piece too); checks the growth against the predictions; prints
    `EFFECTIVE IntegralDescentParLnValidation arm=cells cells=…`.

  Roster after PAR-LN **262 = 70 / 163 / 29** (`--all` 233).

### Slot 24 AVX2K (the AVX2 u32 GEMM kernels for CPUs without AVX-512; `slot24/AVX2K_report.md`, ENGINE_API §6.3)

- **New name `KernelAvx2BitIdentityValidation`** — **`fast`**, ≈ 0.7 s, < 0.1 GiB, **9501 checks** on the box (AVX2 + AVX-512; 9131 before integration 3)
  (registered by `Registry/Slot24.cpp`; code `src/ModArithmetic/KernelAvx2BitIdentityValidation.{h,cpp}`). Arms portable,
  avx2-u64 (pair route off), avx2-pair (forced), avx2-auto, avx512 (VNNI off), each against `RefLinAlg::gemm` over the whole C buffer
  (padding and the frame outside the window included): (P) 24 moduli 2 … 4294967291 (incl. 997, the pair route's edge 4093 / 4096 / 4099,
  2^13 / 2^14 neighbours, 134217757, the U32_Delayed / U32_Shoup switch 1518500213 / 1518500249, 2^31 − 1, > 2^31); (L) n = 1 … 33, m = 1 … 17;
  (K) k ∈ {1, 2, 255, 256, 257, 513, 1029}; (W) every entry p − 1; (Y) B / C column-major, windows, Set / Add / Sub, a 40 × 600 × 530
  product; (A) Auto → AVX-512 / AVX2 / portable by CPU, a forced Avx2 path never routes to VNNI; (S) the pair route is selected and its
  counter moves; (R) an entry ≥ p behind a Canonical tag is refused on the pair route; (F) (integration 3, AVX2K audit F3) A column-major (p ∈ {271, 4093, 4096, 16381, 2^31 − 1}, B row- and column-major), the pair route's column-major-B packer in the worst case at p = 4093 / 4096 with k = 127 / 129 / 257 (kc = 128), and k = 3 … 9 across the u64 microkernel's k_max near 2^30.5 … 2^32. Without an ISA its arms print `[SKIP arm]`. Line
  `AVX2K_GEMM avx2=<0|1> avx512=<0|1> checks= failing= verdict=<OK|FAIL>`.
- `KernelBitIdentityValidation` (its gemm battery and the `ENGINE_KERNEL_TIMING=1` table) and `VnniGemmBitIdentityValidation` (arm
  `u32-avx2`) run the AVX2 path too. Since integration 3 (AVX2K audit F1) `VnniGemmBitIdentityValidation`'s (R) / (S) arm pins `KernelPath::Avx512` when the CPU has it
  (prints `(R)/(S) kernel path pinned to avx512 (ENGINE_KERNEL=…)`), so it passes under `ENGINE_KERNEL=avx2|portable` too.
- Env: `ENGINE_KERNEL`, `ENGINE_AVX2_PAIR` (read-only; the env table below).

  Roster after AVX2K **262 = 71 / 162 / 29** (`--all` 233) on its own branch; after integration 3 (`s24-par-integrate3`: PAR-GP, PAR-LN,
  PAR-F2, AVX2K) **263 = 71 / 163 / 29** (`--all` 234).

### Slot 24 CL-1 (the shared helpers; `slot24/CLEANUP_plan_1030.md` CL-1, CODEAUDIT A2–A4, A7, B2, C-05–C-08, F10, F11)

- **New name `SharedHelpersValidation`** — **`fast`**, < 1 s, < 0.1 GiB, **35 checks** (registered by `Registry/Slot24.cpp`; code
  `Util/SharedHelpersValidation.{h,cpp}`). It proves the header-only helpers reproduce the copies the later CL packages replace, against the
  LIVE copy wherever one is callable: (A) `ScalarMod.h` vs `nf::{mulmod32,mulmod64,mulmod64_portable,powmod32,invmod32}`,
  `lvalue::{PowModU64,InvModU64}`, `eis::{PowModP,InvModP}` and naive routines (random + edge, 2^61 − 1, 2^64 − 59, m = 1);
  (B) `ModCtx::chain` vs `ModCtx(ell)` / `prime_power`; (C) `EnvLever.h` parse matrix (11 values × FASTMUL / GOOD_SPARSE / GOOD_DENSE /
  SMITH2K_VERIFY transcribed, `engine::cuda::imma_policy()` live), the WARNING texts byte for byte, Scoped nesting, say_once, and the live
  `DescentGood{Sparse,Dense}{Enabled,Source}()` / `FormsFastMulEffectiveLine()` (the latter only when `HECKE_FORMS_FASTMUL` is unset);
  (D) `Engine/Threads.h` vs `ThreadPool::default_threads()`, `birch::MeasureThreads()`, `tower::TowerThreads()` (18 values of
  `ENGINE_THREADS`, set and restored per value), `smithpar::default_threads()` as configured, and 41 transcribed rows (SmithPar,
  DescentParAsm, GammaHTower, ThreadPool, with both SmithPar WARNING texts); (E) `CpuFeatures.h` implications and names;
  (F) `Util/ValidationCheck.h` output styles; (G) `Util/CellList.h` vs `HookParseCells`, `HeckeSatCertDumpParseCells` and
  `census::ParseCellList` (every error text `HeckeSmallCarriesValidation` pins); (H) `Util/TextIo.h` vs `atlas_index::Hex16` and
  `std::hex`, `ReadFile`; (I) `Util/Timing.h`; (J) `Util/ParallelFor.h` vs the three copies' splits (264 cases).
  Prints `(E) cpu: avx2= fma= avx512f= avx512_f_bw_dq_vl= vnni=`. Read-only: sets only `OC_CL1_*` probe variables, `ENGINE_THREADS` and
  `ENGINE_GPU_IMMA`, each restored at once, around readers that re-read per call.
- Roster after CL-1 **267 = 72 / 150 / 45** (`--all` 222), on top of VAL-IMPL (266).

### Slot 24 CL-L0 (the legacy-flag machinery; `slot24/CLEANUP_plan_1030.md` §2.1–2.4, CL-L0; owner ruling 1 of 2026-10-30)

- No new name; `--list` is byte-identical with `OC_ENABLE_LEGACY=OFF`, `=ON` and the build before (`EXPECT_NAMES` 267). Design and
  file map: `architecture-detail.md`, "The legacy flag `OC_ENABLE_LEGACY`".
- `SharedHelpersValidation` — **41 checks** (was 35): new arm **(K)** — `LegacyConfig.h`'s refusal text and the `SKIP-ARM` line
  byte for byte; `retired_refuses` on 7 values × {default-on `Exact01`, default-off, `FirstChar`}; the retired mode (OFF: one route for
  unset / `1` / invalid / empty, `source=retired`, `refusal_text()` exactly for `0`; ON: `RetiredLever` is `EnvLever`, `X=0` and `Scoped`
  as before); `OC_LEGACY_VALIDATION` (ON: the function, OFF: the `[SKIP]` stub, exit 0) and `RunLegacyArm` (OFF prints one
  `SKIP-ARM SharedHelpersValidation arm=K5: OC_ENABLE_LEGACY=OFF` line). Prints `(K) OC_ENABLE_LEGACY=<0|1>` and its live probe's
  `EFFECTIVE OC_CL1_RETIRED_PROBE route=new source=retired` (OFF) / `… source=default` (ON). Same check count OFF and ON.
- Env: **`OC_CL1_RETIRED_PROBE`** (read-only probe of arm (K1), read as the process was started): in an OFF build
  `OC_CL1_RETIRED_PROBE=0 ./hacs SharedHelpersValidation` is the refusal smoke of a retired lever (stderr
  `REFUSED OC_CL1_RETIRED_PROBE=0: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1); ON it reads `route=old`, and the validation passes.
- **`ENGINE_BACKEND=legacy` is refused in an OFF build** (any entry point, `main()` reads it first; exit 1). It still selects the
  legacy arm in an ON build, so every catalogue line "under `ENGINE_BACKEND=legacy`" now means an ON build; `cross_config.sh`'s
  `legacy` arm (`RelWithDebInfo+OC_ENABLE_LEGACY=ON@ENGINE_BACKEND=legacy`) replaces `RelWithDebInfo@ENGINE_BACKEND=legacy`.
  In-process forcing (`ScopedLegacy`, console `backend = "legacy"`, `--bench micro --backend legacy`) is unchanged until CL-L2.

### Slot 24 PANEL-IMPL (the size-dependent ring2k LU panel, the decoupled device panel, the resident-route RSS term; `slot24/PANEL_report.md` §6–§7)

- No new name, no new env name. The threaded ring2k host LU's default panel is **512 at ≥ 12 000 rows** of the factored matrix, else 128
  (ring3k 128; `HECKE_DESCENT_SMITH_PANEL` overrides at every size; the device LU keeps 128): env table, `HECKE_DESCENT_SMITH_PANEL` row.
- `DescentSmithMtValidation` — **`standard`**, ≈ 13 s, **10451 checks** (was 8649): (E) adds panel 512 to the ring2k T × panel grid;
  (S) checks the size rule (128 below 12 000 rows, 512 from 12 000, ring3k 128) and that an explicit width wins at every size, and prints
  `panel2k=128|512@12000 panel3k=128`.
- `DescentSmithGpuValidation` unchanged (12589 checks; direct `echelon_blocked` callers pass the device the same panel as before).

### Slot 24 VAL-IMPL (the leaner `--all`; `slot24/VALSTREAM_audit_1030.md`, Phase 1 + `NumberFieldRibetFieldValidation`)

No check was dropped: every check that left `--all` runs under `--all-full` (in its own name, now `slow`, or in a `…SlowValidation`
sibling), and every split pair adds up to the pre-split check count. Roster **266 = 71 fast / 150 standard / 45 slow** (`--all` 221;
was 263 = 71 / 163 / 29, `--all` 234); `EXPECT_NAMES` 266.

- **Thirteen tier moves `standard` → `slow`** (no code change; the audit row in brackets): `HeckeModuleMtValidation` [2],
  `L23Bin3o1Validation` [3], `OrbifoldRing2kValidation` [4], `HeckeUEllStreamValidation` [5], `OrbifoldF3lValidation` [6],
  `IntegralDescentParLnValidation` [8], `HeckeThetaRssDietValidation` [11], `OrbifoldMod3kValidation` [14], `HeckeUEllLowRankValidation` [15],
  `HeckeSatPerfValidation` [16], `HeckeLadicSplitValidation` [17], `IntegralDescentParAsmValidation` [18],
  `NumberFieldRibetFieldValidation` [20]. Rows 2–18 compare a lever or stream route with its own
  rollback / legacy route or sweep thread counts; the default route's values stay pinned in `--all` (golden tier A, the census and descent
  validations, the math validations of the audit's table). Row 20 is static (`NumberField/` only).
- **Splits** (the standard name keeps its `EFFECTIVE` lines; check counts measured 2026-10-30):

  | standard name | checks before | standard after | slow sibling (new or existing) | sibling gains | what moved |
  |---|---:|---:|---|---:|---|
  | `HeckeModuleStreamValidation` | 10903 | 9672 | `HeckeModuleStreamSlowValidation` (existing; 153 before) | 1231 (now 1384) | every arm at (6, 10007, 2) ((O), (T), (V) eval and memo, (P), (H) (c)) and the (S) cell (160, 11) KMAX 6; the sibling prints `MODULE_STREAM_SLOW moved_from_standard checks=<k>` |
  | `BlockEliminationValidation` | 10170 | 9626 | `BlockEliminationSlowValidation` (new) | 544 | the "2x11 d=65" grid at the eight non-big (prime, width) passes; a skipped case still consumes its seed, so every input is the pre-split one |
  | `DenseElimValidation` | 73559 | 41174 | `DenseElimSlowValidation` (new) | 32385 | the u64 width at 2, 3, 134217757, 2^31−1, 2^32−5 and the parameter sweeps at 2^32−5 and 2 (u32); the u32 width, u64 at 2^61−1 and the sweeps at 134217757 / 2^61−1 stay |
  | `HeckeLocalityValidation` | 1501 | 1497 | `HeckeLocalitySlowValidation` (new) | 4 | arm 7 (c), the strict-mode grid identity (the whole golden-grid sweep under `locality = strict`, line `LOCALITY_GRID_STRICT`); arm 5's sweep and the rest of arm 7 stay |

- **Not done, and why.** `ThetaEqSolveValidation` and `BlockModelPipelineValidation` (row 19, ≈ 8 s): both lines are frozen with
  tier `standard` in `Console/scripts/cli_frozen/list.stdout`, which `ConsoleCliPreservationValidation` checks (name and tier, in order;
  [P] Sec. 11); moving them would change a frozen CLI output, so they stay `standard`. `HeckeFormsFastMulValidation` (row 12): its (P1) half at four ℓ measured **0.3 s** as a sibling, so the split
  saved nothing and was dropped (no name added). `ConsoleDeterminismValidation` arm (c) swap (row 10): [P] "Phase C2" acceptance (c) names
  `run_validation("GoldenRegressionValidation")` itself, so the swap is a console-spec change, not a suite change; left as is.
  `HeckeLambdaTowerValidation` / `HeckeLValueIwasawaInvariantsValidation` (rows 21, 22): skipped by decision. Parallel sharding: the next package.
- **Process rule.** A package that touches a lever's code runs that lever's validation **by name** although it is now `slow`:
  `HECKE_MODULE_MT` → `HeckeModuleMtValidation`; `HECKE_SAT_PERF` → `HeckeSatPerfValidation`; any L23 route (`L23_BIN3O1`, `L23_RING2K`,
  `L23_F3L`, `L23_MOD3K`) → `L23Bin3o1Validation` / `OrbifoldRing2kValidation` / `OrbifoldF3lValidation` / `OrbifoldMod3kValidation`;
  the U_ℓ stream / low-rank levers → `HeckeUEllStreamValidation` / `HeckeUEllLowRankValidation`; `HECKE_FIELD_DIET` →
  `HeckeThetaRssDietValidation`; the descent PAR levers → `IntegralDescentParAsmValidation` / `IntegralDescentParLnValidation`; the
  shared digit-cell session → `HeckeLadicSplitValidation`; the module-stream levers → `HeckeModuleStreamSlowValidation` too; the
  elimination core (`DenseElim`, `BlockElim`) → `DenseElimSlowValidation` / `BlockEliminationSlowValidation`; `NumberField/` → `NumberFieldRibetFieldValidation`; the locality code → `HeckeLocalitySlowValidation`.
- **Wall.** `--all` after VAL-IMPL: **221/221 passed, 1731 s (28:51)**, peak RSS 4.8 GiB, on a loaded box (load1 min 9.8 / median 19.5 / max 28.5;
  the audit measured 1990 s at median 8.4). The removed work, measured by name: 13 moved names ≈ 429 s, the four splits ≈ 147 s
  (ModuleStream 145 → 58 s, BlockElimination 47 → 20 s, DenseElim 29 → 17 s, HeckeLocality 48 → 27 s); ≈ 575 s together. A wall on a
  quiet box is still owed.

---

### Slot 24 CL-O (the independent oracle of `HeckeModuleStreamValidation`; `slot24/CLEANUP_plan_1030.md` CL-O, ruling 1; audits A8 / B9)

No new name, no tier change: roster **266 = 71 / 150 / 45** (`--all` 221). File `HeckeExt/HeckeModuleStreamValidation.cpp` only. Until
now every (O) / (L) arm's only oracle was the legacy module route (`ScopedModuleStream(false)`, the twin of `HECKE_MODULE_STREAM=0`,
`compute_module_legacy`). Arm **(R)** adds an oracle that reads neither the legacy route nor the stream route nor `engine::elim`:
`engine::ref` (RefLinAlg: the naive `mod_*_w` GEMM, the naive Howell form and the naive Smith rule of `ref::invariant_factors`) on
the flat cochain complex rebuilt from the relations (A_Cq: I at s_lhs, −M at s_rhs, I − M when equal) and the simplicial coboundary
(D_q = D_1 ⊗ I). Lengths are Σ (K − v) over Howell pivots. The legacy comparison stays beside it until `HECKE_MODULE_STREAM`
retires at the slot-25 close (CL-L2 moves it behind `OC_ENABLE_LEGACY`).
- **Clauses** (per degree q): (R1) A_Cq C = 0; (R2) length(colspan C) = c_q K = length(ker A_Cq), so colspan C = C^q_eq; (R3) D C = C' X;
  (R4) A_Cq H = 0 and D_q H = 0; (R5) ℓ^{e_i} b_i ∈ B^q = colspan(D_{q−1} C_{q−1}); (R6) length(B + colspan H) = length(Z^q) =
  c_q K − length(D_q C_q) and Σ e_i = length(Z/B) = length_H (so ⊕ Z/ℓ^{e_i} → H^q is an isomorphism); (R7) |H^q[ℓ^j]| =
  ℓ^{Σ min(e_i, j)} for 0 < j < K, counted as length(Z) − length(ℓ^j Z + B); (R8) `ref::invariant_factors(H, B)` = (e_i); (R9)
  `ref::invariant_factors(D C)` = dK. Per T_p and q: (T1) Θ C = C Θ_eq; (T2) D Θ_q C = Θ_{q+1} D C; (T3) 0 ≤ A_ij < ℓ^{e_i} and
  Θ H − H A ∈ B column by column (T_p b_j = Σ_i A_ij b_i in H^q); (T4) Θ mod ℓ = the F_ℓ field route's flat Θ
  (`HeckeOperatorOnKT<uint32_t>`, `get_Theta_flat_matrices`) entrywise. 82–96 clauses per full cell (70 on Hida's L_n: no (T4), the
  field route has no Hida lattice); a lean cell (X, Θ, Θ_eq released) runs every clause but (R3), (T1), (T4), on the Θ of a full stream
  run of the same cell that (R) has checked first. One `MODULE_STREAM_ORACLE <arm> clauses= failing= seconds=` line per run.
- **Coverage: every (O) and (L) cell of the pair.** In the standard name on the stream run of (20, 5, 3), (24, 11, 2), (24, 43, 2),
  (12, 101, 2), (10, 1009, 2), Hida (8, 5, 3), (16, 211, 2), (12, 101, 3), (10, 101, 5) u64, (8, 1009, 4) u64, (8, 1291, 3) and the lean
  (12, 101, 2); in the slow name, where the oracle costs ≈ 1 s or more, (60, 5, 6), (6, 10007, 2), (40, 13, 3), (30, 7, 4), (24, 43, 2) +
  lean, (40, 7, 12) u64 + lean (line `MODULE_STREAM_SLOW oracle_for_standard_cells checks=654`; these cells' legacy comparison stays in
  the standard name; `moved_from_standard checks=1231` is unchanged), and on (60, 1009, 4) u64 and the lean (100, 1009, 2) beside their
  legacy comparison. On every cell both oracles agree (0 failing).
- **Negative controls** (in the standard name, at (20, 5, 3) u32 and (10, 101, 5) u64; one `ORACLE_NEGATIVE <arm> '<kind>'
  rejected_by={…}` line each): one entry of a copy of the inputs perturbed — C(0, 0) + 1 (→ R3, T1), X(0, 0) + ℓ^{K−1} (→ R3),
  H(piv_0, 0) + 1 (→ R4, T3), e_0 − 1 (→ R5, R6, R8), an extra summand b = 0 with e = 1 (→ R6, R7, R8), dK_0 + 1 (→ R9),
  Θ(piv_0, piv_0) + ℓ, invisible mod ℓ (→ T1, T2), Θ(0, 0) + 1 (→ T1, T4), Θ_eq(0, 0) + 1 (→ T1), A(0, 0) + 1 mod ℓ^{e_0} (→ T3):
  10 of 10 rejected at both cells. **Fault injection (once, not committed):** A^{(1)}(0, 0) + 1 mod ℓ^{e_0} written into
  `compute_module_stream()` was caught at every (O) / (L) cell where (R) runs in the standard name by the legacy comparison and by (R)
  alike, operator for operator (4 or 5 failing checks each, one per T_p; the run then stops in a sat arm's own ENGINE_CHECK).
- **B9 (the stream route's downstream readers).** `HeckeRingLoewyValidation`, `HeckeSaturationDefectValidation` and the golden E8 points
  (`GoldenHarness.cpp` `kGridE8`: 7 points, lengths, invariant factors, `ladic_type`, the free charpoly of A^{(1)}(T_p), the boundary and
  the cone) run on the default route, which is the stream route (`HECKE_MODULE_STREAM` unset), so they read its values. They pin
  basis-free invariants; the basis-dependent objects (C, H, A^{(q)}, Θ_eq) are pinned entrywise only by the legacy comparison and are
  now proved correct by (R). The (S) sat cells are not re-derived by (R): they consume these objects through `RunModuleT`.
- **Counts** (measured 2026-10-30, the box shared with other agents): `HeckeModuleStreamValidation` **9672 → 10870 checks**, 0 failing,
  63.0 s → 70.3 s, peak_rss_mib 190.5 → 258.4; `HeckeModuleStreamSlowValidation` **1384 → 2294 checks**, 0 failing, 963.8 s → 1137.5 s.

### Slot 24 CL-R1 (the slot-13/14 levers retired; `slot24/CLEANUP_plan_1030.md` CL-R1, owner ruling 2 of 2026-10-30, CODEAUDIT-B B6)

- No new name, no tier change; `--list` byte-identical OFF / ON / the build before (`EXPECT_NAMES` 267). Retired:
  `HECKE_U_ELL_LOW_RANK`, `HECKE_COSET_STREAM`, `HECKE_PARALLEL_SETUP`, `HECKE_RANK1_CLOSED_FORM` (`engine::lever::RetiredLever`;
  OFF: `<NAME>=0` → `REFUSED <NAME>=0: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1). Removed in every build: the `--bench` flags
  `--[no-]u-ell-low-rank`, `--[no-]coset-stream`, `--[no-]parallel-setup` (now `--bench: unknown option`, exit 1); register row above.
- `HeckeUEllStreamValidation` — whole name legacy-gated (`OC_LEGACY_VALIDATION`): OFF `[SKIP] HeckeUEllStreamValidation:
  OC_ENABLE_LEGACY=OFF` (exit 0); ON 2262 checks as before (2246 under `HECKE_COSET_STREAM=0`, as before).
- `HeckeUEllLowRankValidation` — new arm **(M)** in every build (the default `Auto` mode on `(n, ell)` ∈ {(10, 5), (24, 13), (10, 691),
  (22, 691)}: in effect for `U_ell` and not for `T_2`, never for `ContragredientN`; the coset table streams; the τ pool factored
  exactly for `U_ell`; `RhoRefT::get()` on the factored default pool throws ((E-iii) on the default pool); O12(a) on both), **44
  checks**; the lever arms (A)–(G) and the RSS print (D) under `RunLegacyArm(…, "lever")` (`Hecke/legacy/HeckeUEllLowRankLegacyArms.cpp`).
  **OFF 44 checks** (+ `SKIP-ARM HeckeUEllLowRankValidation arm=lever: OC_ENABLE_LEGACY=OFF`), **ON 388** (44 + 344). In an ON build
  started with `HECKE_U_ELL_LOW_RANK=0` or `HECKE_COSET_STREAM=0`, (M) prints `(M) skipped` (344 checks).
- `HeckeHidaHeavyCellProbe` no longer forces the lever (`ScopedUEllLowRank(p == ell)`); the default `Auto` mode is the same route
  on its cells (ENGINE_CHECKed per operator). B11: `HeckeCosetTables::cocycle_upper` and `parallel_setup_min_work()` deleted.

### Slot 24 CL-L2 (legacy stage 2: the backend and `BlockFlatMatrix` behind `OC_ENABLE_LEGACY`; `slot24/CLEANUP_plan_1030.md` CL-L2, §2.2 / §2.3, owner ruling 1 of 2026-10-30)

- No new name, no tier change; `--list` byte-identical OFF / ON / ON + shadow / the build before (`EXPECT_NAMES` 267). The
  `--all` pass count is unchanged (a `[SKIP]` stub passes). Check counts below are **OFF / ON** (`RelWithDebInfo`, CUDA ON,
  2026-10-31; ON = `-DOC_ENABLE_LEGACY=ON`).
- **Whole names legacy-gated** (`OC_LEGACY_VALIDATION`; OFF prints `[SKIP] <name>: OC_ENABLE_LEGACY=OFF`, exit 0; sources now under
  `legacy/`): `BlockFlatMatrixValidation` (ON 179 tests), `CohomologyBlockModelValidation` (ON 10 788 checks on 57 local systems),
  `HeckeThetaBlockValidation` (ON 65 cases, 4745 checks), `BarCocycleSolverValidation` (ON 1830 systems).
- **Arms legacy-gated** (OFF prints one `SKIP-ARM <name> arm=<x>: OC_ENABLE_LEGACY=OFF` line; the arm bodies are `legacy/*LegacyArms.inc`
  or sit under `#if OC_ENABLE_LEGACY`):
  - `FlatMatrixValidation` arm `Q11-BlockFlatMatrix` (the third class of Q11): **119 / 119** tests (the two Q11 checks compare two
    classes when OFF).
  - `SubstrateDifferentialValidation` arm `BlockFlatMatrix` (the third substrate): **686 / 774** cases (the three-way checks compare
    Matrix with FlatMatrix when OFF; the `*/Matrix-vs-BlockFlatMatrix`, block cache-coherence (d)/(e), block product and inverse
    cases exist ON only).
  - `DenseElimValidation` arm `legacy` (the `ScopedLegacy` / `factor_basis_block` halves; the retrofit checks stay): **33 693 / 41 174**
    checks. `DenseElimSlowValidation`: the same arm, OFF 26 172 checks (ON not run: slow tier).
  - `BlockEliminationValidation` arm `legacy`: **6611 / 9626** checks (the engine checks are the same set in both builds: the
    generator cap `with_legacy && a > 500` still applies). `BlockEliminationSlowValidation`: the same arm, OFF 544 checks.
  - `BlockModelPipelineValidation` arm `legacy`: **29 / 44** checks.
  - `DenseElimPipelineValidation` arms `legacy-real-matrices` and `whole_pipeline`: **38 / 125** checks. OFF assembles A_Cq through
    `BuildACqBlockMat` (BlockModelPipelineValidation.h) instead of the `BlockFlatMatrix` `BuildACq`; the engine, `RefLinAlg` and
    retrofit-`FlatMatrix` checks run in both builds.
  - `ConsoleDeterminismValidation` arm `b` (`backend = "legacy"` on the C1 set): **573 / 606** checks; C4 (a) digest
    `0xf6ed04bbe8e6b60a` on 24 / 24 arms in both builds (ON: (b) legacy = engine `0xf6ed04bbe8e6b60a`).
  - `ConsoleSettingsValidation` arm `backend-legacy` (the three `backend` knobs, `run_concurrently`, session end; ON also the
    engine-vs-legacy `micro("gemm", 64)` checksum pair moved from `022_harness.oc`): **218 / 220** checks; OFF instead checks the two
    refusals `set backend = "legacy"` and `micro(…, backend = "legacy")` (exit 5, `compiled out (OC_ENABLE_LEGACY=OFF)`).
  - `HeckeInvolutionValidation` arm `IOTA_CARRY_ROUTE` (the line and its counter `iota_carry_legacy_calls()` exist ON only):
    **2954 / 2954** checks.
  - `HeckeDualityValidation` arm `contragredient-legacy` (one check: the contragredient operator's legacy arm == engine arm).
  - `HeckeIotaStreamValidation` arm `L` (the legacy elimination on a one-worker pool; one `SKIP-ARM` line per cell it would run on):
    **503 / 506** checks.
  - `HeckeConeActionValidation` arm `A15-route3-legacy` (the relative sub-complex's legacy cohomology arm on three cells):
    `CONE_ROUTE3 … legacy_cells=0 checks=4321` / `legacy_cells=3 checks=4339`; total 124 607 in both (`CONE_ACTION` line).
  - `HeckeThetaRssDietValidation` (slow) arm `T-legacy` (the (T) tape == legacy comparisons): **194 / 370** checks; `P4A_RSS_DIET … digest=0xa3326bcdd2505bae` in both
    (the digest reads the tape arm only).
  - `PerformanceSmokeValidation`: unchanged code path; its legacy floors run only under `ENGINE_BACKEND=legacy`, i.e. in an ON build.
  - `HeckeUEllLowRankValidation`: its legacy-backend sites were already in CL-R1's `Hecke/legacy/HeckeUEllLowRankLegacyArms.cpp`.
- **`022_harness.oc`** now pins two engine `micro("gemm", 64)` runs against each other (the engine-vs-legacy pair is the ON arm of
  `ConsoleSettingsValidation` above); the transcript `022_harness.expected` is unchanged (the lines printed nothing).
- **Refusals in an OFF build** (§2.4): `ENGINE_BACKEND=legacy` → `REFUSED ENGINE_BACKEND=legacy: compiled out (OC_ENABLE_LEGACY=OFF)`,
  exit 1 (CL-L0); console `set backend = "legacy"` / `--set backend=legacy` / `micro(…, backend = "legacy")` → `not implemented in
  this build: … compiled out (OC_ENABLE_LEGACY=OFF)`, exit 5; `--bench micro … --backend legacy` → `--bench: --backend legacy:
  compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1. `ENGINE_COUNT_OBJECTS` keeps `block_ctors=` (0 in OFF builds).
- **Value change: none.** One default-route caller of the legacy `factor_basis_block` was found (not in the plan's list):
  `CochainComplex::compute_cohomology_bases` (trivial coefficients, unit block rows). It now calls `engine::elim::complement_basis`
  (the same rule on the same augmented matrix; `DenseElimValidation` pins the two entrywise, pivots and projector, in ON builds),
  with `factor_basis_block`'s return conventions; under `use_legacy()` (ON) the old call runs. Golden tier A / B unchanged.

### Slot 24 CL-6 (validation boilerplate in HeckeExt; `slot24/CLEANUP_plan_1030.md` CL-6, CODEAUDIT A4)

No new name, no tier change, no check count changes (every `… checks` line of `--all` read equal before and after). The 35
`void Check(bool, const std::string&)` copies in `HeckeExt/` (all but `HeckeModuleStreamValidation`, CL-O's) are one
`oc_util::Checker Check(<prefix>[, endl, print_limit])` object each (`Util/ValidationCheck.h`), with the prefix, the newline style and
the print limit of the copy, so no transcript line moves; `HeckeLambdaModSym` / `HeckeLambdaTwoVar` keep thin `Check` / `Finding`
wrappers for their per-gate tally. The `*_CELLS` readers split through `oc_util::cells::Tokenize` (`Util/CellList.h`, new in CL-6: one
token per `,`-item with its 1-based position, numeric only when every `:`-field is digits, no empty item or field) and print through
`EffectiveLine` where their line had that form; `HECKE_DUMP_SAT_CERT_CELLS` is `ParseStrict(Style::SatCert)`, and
`census::CellList` / `ParseCellList` (`HECKE_CENSUS_LATTICE_CELLS`, `HECKE_FORMS_CENSUS_CELLS`) are the lax grammar's
`LaxList` / `ParseLax` — all three byte for byte (SharedHelpersValidation (G), HeckeSmallCarriesValidation (3)). Not migrated:
`HECKE_HIDA_CM_CELLS` (signed `d` field, its own trim/split) and `HeckeHidaHeavyCellProbe` (CL-R1). Every `EFFECTIVE` line reads
the same under the default arms and under one armed list per reader.

**Accepted grammars that narrow** (each was a lax `std::stoul` / `std::sscanf` read; every launch-kit list in `docs/cluster/` still parses):
- `HECKE_HIDA_COMPONENTS_CELLS`: a trailing `:` (`34:7:` read as `34:7`) and non-digit fields (`+34`, `34x`, or a `std::stoull` throw)
  are refused with the hook's own `is not n:ell[:K]` check.
- `HECKE_MIXED_FINALITY_CELLS`: exactly two digit fields, at most 9 digits; `34:7:9` and `34:7x` were read as `34:7`; now `expected n:ell`.
- `HECKE_LAMBDA_TOWER_CELLS`: fields at most 9 digits (a 10-digit field was cast to `uint32_t`, wrapping), a trailing `:` refused;
  the text stays `malformed token at position <k>`.
- `HECKE_LAMBDA_MSYM_CELLS`, `HECKE_LAMBDA_TWOVAR_CELLS`: `std::sscanf("%llu")` let a field carry blanks or a sign; now digits only, else
  the token's own `REFUSED` line.
- `HECKE_RING_LOEWY_CELLS`: digit fields only (blanks are still stripped first); a non-digit field or trailing `:` now gives the hook's
  `bad item '<item>' (n:ell[:KMAX])` instead of `std::stoul`'s exception or a silent read.
- `HECKE_LVALUE_CELLS`, `HECKE_SHAPIRO_CELLS`: fields at most 18 digits; `HECKE_SHAPIRO_CELLS` also refuses a trailing `:`.
- Unchanged: `HECKE_SAT_DEFECT_CELLS` and `HECKE_FORMS_FASTMUL_CELLS` (only the split moved; their field checks are their own),
  `HECKE_DUMP_SAT_CERT_CELLS`, `HECKE_CENSUS_LATTICE_CELLS`, `HECKE_FORMS_CENSUS_CELLS`.

### Slot 24 SHARD (parallel-shard `--all`; `slot24/VALSTREAM_audit_1030.md` §3 / §5 item 5, `slot24/SHARD_acceptance.md`)

No new name, no tier change (roster 267 = 72 / 150 / 45). `--all --shard i/N` and `--all-full --shard i/N` (1-based, 1 ≤ i ≤ N ≤ 64)
run shard i of N of that tier's roster in one process; the union over i is exactly the roster, each name once, so sharding drops no check.
- **Partition** (`ValidationShard.{h,cpp}`): a pure function of (roster in registry order, N). Units are single names, except the
  co-location groups, each one unit. The **device group** is one of them (`ValidationShardDevice.inc`: the 19 names that create the CUDA context in
  a default run, *measured*: each name run alone with `ENGINE_TRACE_DEVICE_RELEASE=1`; besides the `Cuda*` / `Gpu*` / `Engine*Device*` names it
  holds `EngineTapeValidation`, `EngineTapeConsumerValidation`, `EngineDeterminismCoreValidation`, `EngineElimPassOptionsValidation`,
  `HeckeExtCampaignValidation`, `HeckeExtDeterminismValidation`, `ConsoleDeterminismValidation`, `ConsoleErrorValidation`). No other group is
  known (every name passed alone). Unit weight = the summed expected wall from `ValidationShardWeights.inc` (integer ms; a missing name
  gets 5 s); LPT greedy (heaviest unit first, ties by registry position, to the lightest shard, ties to the lowest index); registry order
  within a shard. Weights only steer the balance; a stale table can make shards uneven, never drop or duplicate a name.
- **Output**: `SHARD i/N names=<k> of <total> roster=all|all-full expected_s=<s> device_shard=<d> device_guard=on|off` first, then the
  usual `[PASS]` / `[FAIL]` lines, then `All validations PASSED (k/k passed, shard i/N).`; exit = the shard's failures. Slow names
  outside the `--all` roster are not printed. `--list` after the spec prints the shard's `name<TAB>[tier]` lines instead (exit 0);
  `--all --list` is the whole roster as shard 1/1. A malformed or out-of-range spec, or any other argument after `--all`, is a usage
  error (exit 1). The token is in the manual's token table, not in the frozen help text (`cli_frozen/help.stdout` unchanged).
- **Device guard**: in a shard other than the device shard (N > 1, `ENGINE_DEVICE` unset or `cpu`), a validation after which the
  CUDA context exists, and before which it did not, prints `[SHARD-DEVICE] <name> created the CUDA context outside the device shard`
  and fails, so a new device validation cannot slip into a CPU shard unnoticed: add it to `ValidationShardDevice.inc`.
- **Driver**: `docs/matrix-engine/tools/run_all_sharded.sh <binary> [N] [--full] [--logs <dir>]` (default N = 4, logs outside the
  tree): launches the N shards at once, prints each header and summary, checks that the shards' planned names (`--shard i/N --list`)
  add up to plain `--list`'s roster each once and that each shard ran its planned count, and prints
  `SHARDED_ALL shards=N passed=x/y failed=z mode= wall_s= logs= verdict=OK|FAIL`; exit = total failures. RSS ≈ 4.4 GiB per shard.
- **Regenerating the tables**: `docs/matrix-engine/tools/shard_measure.sh <binary> <outdir> [jobs] [--full]` (every name alone, `jobs`
  at a time; also the state-dependency probe: a name failing alone but passing in `--all` depends on an earlier one) then
  `shard_weights.py <outdir>/measure.tsv <repo>`. Do it when a heavy name is added or the device set changes.
- **Self-check**: an arm of `ValidationHarnessCatchValidation` (`ShardPartitionSelfCheck`): for N ∈ {1, 2, 3, 4, 5, 8, 16} on both
  rosters, union = roster, disjoint, the device group (and every co-location group) in one shard and equal to `device_shard`, loads
  summing to the roster weight, no shard empty, reproducible; malformed specs refused. Two `SHARD_PARTITION roster=… N=4 loads_s=…`
  lines. 160 checks with the catch-path checks.
- **What sharding changes**: a state dependency between validations reproduces only within one shard. The isolated measurement
  run passed every name alone (`SHARD_acceptance.md`). `--all-full` shards are bounded below by `HeckeModuleStreamSlowValidation`
  (≈ 20 min alone).

### Slot 25 EXPORT (the module H^1 (x) Z/ell^K with its T_p as an object; `slot25/00-slot25-plan.md` §2.1, `slot25/EXPORT_report.md`)

- **New name `HeckeZExportValidation`** — **`standard`** (plan §2.1; ≈ 1.1 s and 28 MiB max RSS alone, `/usr/bin/time`, after the audit fixes; ≤ 10 MiB growth per arm; ≈ 90 MiB is the process RSS after `IntegralDescentRecordValidation` in the same process, not the validation's own), roster **268 = 72 / 151 / 45**,
  `--all` runs **223**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code:
  `Integral/Descent/DescentModuleExport.{h,cpp}` (`modexport::ExportModule`); console: the method `DescentRecord.module(ell, K)`
  (`Console/Bindings/Descent.cpp`; a method, not a verb, so no read-only tag row), script `058_s25_descent_module.oc` (new `.expected`).
- **What it checks** (basis-free invariants only, R-E2; seven arms, ≈ 240 checks; an exception fails its arm only; each arm prints
  `ARM (x) checks= failed= seconds= rss_peak_mib= within_budget=`):
  (a) level 1 at (1, 10), ell = 691 and (1, 26), ell = 5, K = 2 against the console's Z/ell^K module route
  (`hecke_ext::ringalg::RunModule`): invariant factors, the F_ell-rational joint systems, per system `ReadAlgebra` of the localized module
  (A_K, and at shift t = the torsion exponent the free-part image), char(T_p | free) mod ell^{K-t};
  (b) the universal-coefficient types (03 B2(1)) of H^1 (x) Z/ell^K, K = 1 .. 4, against the descent record's groups (`BuildDescentRecord`,
  `hecke = pair = false`) at T1 (1, 10) at 2, 3; T4 (2, 6) at 2, 3, 5; T5 (8, 10) at 2, 3; the refusals `[PDividesN]` / `blocked(export)` at
  ell = 2, 3 (p | N) and `[BadEll]` (ell = 4);
  (c) char(T_p | free) = char_Z(T_p) (`CharpolyOverZ`, the output rule's residues mod ell^K) at (2, 6) ell = 2 (tree, K = 8), (8, 10) ell = 3
  (tree, K = 6), (11, 0) ell = 5 (K = 2), and at K = 1 the F_5 matrices of `level_n` (`CokernelHeckeMatrices`) at (11, 0); (audit F1) a word prime with
  ell^2 ≥ 2^31: (11, 0) and (1, 10) at ell = 65521, K_run = K_max = 1 (the field F_ell), against char_Z mod ell and, at (11, 0), `level_n`'s
  F_65521 matrices (the descent's own torsion read is not compared there: it needs K ≥ 2);
  (d) the Bockstein's Hecke equivariance at (1, 30), ell = 5: T_2, T_3 on H^0(V/25) (the shipped module route in degree 0) = on tors_5 H^1 = Z/25
  (21 and 22);
  (e) T3 (11, 0): the Smith form of T_2 + 2 on L/25 has the exponents [0] (a unit entry: 02 §6's T3 certificate, eta_L = Z/5);
  (f) (1, 30), ell = 5: H^1/5 = L/5 + tors_5/5 (6 = 5 + 1); dim A'_1(L/5) (= 5 A'_2) per system = the console route's A_3 at shift 2;
  (g) (audit F4) the mixed block at ell ∈ {2, 3}: (8, 10) at 2, 3; (2, 6), (1, 10), (4, 12) at 2; (1, 10), (9, 8) at 3; K = 1, 2, K_max: every T_p
  an endomorphism of ⊕ Z/ell^{e_i} and T_p T_q = T_q T_p on the full matrix (torsion, free and mixed blocks; the mixed block is non-zero at
  (8, 10) ell = 2 and (9, 8) ell = 3, checked); forced refusals `[ModulePrecision]` ((1, 30) ell = 5 `K_run = 3`; (8, 10) ell = 2 `K_run = 5`)
  and `[RssCeiling]` (`rss_cap_bytes = 1`, ell = 2 and 691). Since the audit fixes the export also checks that the generators are cocycles
  (d^1 g ≡ 0 mod ell^{K_run} free, mod ell^{K_run − σ_max} torsion; refusal `[NotCocycle]`).
  Every export is also compared with the descent's own q = 1 torsion read (`TorsionOnTree` / `TorsionOnCokernel`: sigma and the
  `hecke3::Invariants` canon) — the `descent_records_identical` field.
- **Gate line**: `HECKEZ_EXPORT arms=7 failing=0 descent_records_identical=yes verdict=OK budget=gated(standalone) entry_rss_mib=… (met: …)`
  (`rss_peak_mib` is the absolute process RSS of the descent's `RssSampler`; the budget is `rss_growth_mib`, the arm's growth over its entry RSS).
  **The RSS budget (≤ 1 GiB growth per arm) gates the verdict only in a standalone run** (entry RSS < 256 MiB: `budget=gated(standalone)`);
  inside `--all` or after other names in one process it prints `budget=informational(in-process)` and does not decide the verdict, because
  freed heap of earlier validations stays resident and is reused without raising VmRSS (audit F2). Its figure of record is the standalone
  run. Seconds are printed, never gated (shared box).
- No env hook, no emitter, no setting, no record key, no golden object; the descent record's bytes are unchanged (`IntegralDescentRecordValidation`).

### Slot 25 HZ-RAT + HZ-UTAG (the rational step of the Hecke structure over Z; `slot25/00-slot25-plan.md` §2.2, `slot25/HZRAT_report.md`)

Two new names, both **fast** (roster 268 → **270** = 74 / 151 / 45; `--all` 225). Libraries `Integral/HeckeZRational.{h,cpp}` (certified
side), `Integral/HeckeZFactorFinder.{h,cpp}` (the untrusted finder: `nf::factor_u64`, a Pratt-certificate search, an `nf::BigInt`
Miller–Rabin; `NumberField/` unchanged), `Integral/HeckeZUTag.{h,cpp}`. Every value comes from residues modulo word primes
(`CrtPrimes`, < 2^30, the shipped cokernel route of `level_n`, [C, prop:crtcharpolyN](2)) with a certified bound, recovered by Garner's
mixed radix and written as FMTMP's canonical hex; the sec:heckeZ labels cited: [C, prop:heckeZrat], [C, thm:heckeZcert], [C, prop:heckeZcong].
- **`HeckeZRationalValidation`** (fast, ≈ 1.0 s, 17 MB): cells T1 (1, 10), T2 (1, 22), T5 (8, 10) anemic, W44 (1, 42). (C1) by the degree
  of the squarefree part at one word prime (certified: deg rad(χ mod ℓ') ≤ deg f_θ ≤ d); disc f_θ and c_θ(λ_θ) = f_θ'(λ_θ) at the good
  primes; factorisations by trial division to 10^6 with valuations by residues (D mod q^j while q^j < 2^64, then the cofactor route
  X = D q^{-e}), the cofactor by residues (c ∏ q^e = |D| checked inside the cover), the finder's word factors re-divided and Pratt-verified,
  above 2^64 `probable` (a probable root q < 2^64 of C = q^e, e ≥ 2, is handed to Pratt); pool passes to a fixed point divide every
  certified prime of the cell out of every value; a gcd's cofactor above 2^64 is kept only if C | D_j is certified by residues for
  every j, else printed `upper_bound`. Checks: T1 f = x² − 2025x −
  49176, disc 3²·691², gcd 691², S_cand {691}, c_2(λ) = 3·691, g_P = 691; T2 running g_P 3⁵5²7²·103·2294797 → 5²·103·2294797 →
  103·2294797 (the drop at T_5), 2294797 `pratt`, cusp part x² − 1080x − 20468736, θ[3]'s disc complete with 79249298311832863²
  `pratt` (pool fixed point, audit F2 + F3); T5 b1 = 22, d = 13, d^an = 6, (C1) with T_3,
  square part of S_cand ⊆ {2, 3, 5, 7, 691}; W44 the 67-bit prime 92013596772457847677 `probable`, C2 `partial(unfactored)`; five negative
  controls rejected (through the production verifier `CertifyWordClaim`: a wrong exponent, a replaced factor, a composite claimed
  prime; through `VerifyPratt`: a square as witness, a well-formed forged certificate of the composite 236364091 = 103·2294797 with
  the Fermat liar 4511); digests of T1, T2 equal at 1, 4, 16 threads. Gate line
  `HECKEZ_RAT cells=4 mismatched=0 tampered_rejected=5 threads_equal=yes verdict=OK`.
  **S25 HZ-RAT-PERF arms** (value-neutral speed and memory, `slot25/HZRATPERF_report.md`; ≈ 5.5 s, 25 MB in all): **CP** the Hessenberg
  charpoly (O(b³), Shoup / Barrett) against the Berkowitz route (`hecke::level::HCharpoly`, O(b⁴)) on 658 cases — random dense, sparse,
  nilpotent, cyclic-permutation, rank-one and block matrices of size 0 … 40 mod 5, 7, 11, 1009, 65521, 1073741789, 2³¹ − 1, and the real
  Hecke matrices of (1, 22), (11, 10), (8, 10) at three word primes — plus one b = 128 timing (`ARM CP … (x≈70)`); **GA** the one-pass
  Garner digits (Barrett, parallel over the later indices) against the descent's `GarnerDigits` / `GarnerInverses` at K = 1 … 6000, 1 and
  4 threads; **EX** the export's column-batched Heilbronn application (`ApplyHeilbronnColumns`) against `HeilbronnOperator::apply`
  column by column, and the partial operators over slices of Mer₉₇ summed against the full operator (N = 26, n = 4, Z/7¹⁰); **WP** the
  grown word-prime list = `WordPrimes(4096, N)` at N = 1, 26, 107, 2089, 30030, and the cap the last (unhashed) key of the canonical
  text; **RF** (1, 22) at cap 8 ends in `WordPrimeCapRefusal` = `refused(word_prime_cap)`, at cap 200 the default's text; **CHI** the
  χ_Z(T_p) route (χ_Z rebuilt independently by CRT) gives the matrix route's text at (1, 22), (1, 34), (11, 10), (8, 10), 1 and 4 threads,
  and a tampered χ_Z(0) is caught at the probe primes (4/4); T5 (8, 10)'s digest equal at 1, 4, 16 threads (the parallel prime walk
  at level N). `HeckeZRecordValidation` gained the record-level refusal (1, 22) at cap 8: `refused`, `G1.C2_status =
  refused(word_prime_cap)` (pending class), scan clean, the caps text unchanged. **Re-audit N4**: the record-level catch of a U_p tag's
  `WordPrimeCapRefusal` (`HeckeZRecord.cpp`, after `UTagStep`; not reached with one cap on the measured cells: the record's rational
  step needs more word primes, (2,6) 10 vs χ_Q(U_2)'s 3), via the validation-only `RecordSettings::utag_word_prime_cap` (0 = the rational
  cap; not in the settings text; it also caps the U_p tag's nested anemic `RationalStep`): `WORD_PRIME_CAP_UTAG (2,6) full utag_cap=2
  status=refused C2=refused(word_prime_cap)`; the cap given as 2^21 = the default record hash.
- **`HeckeZUTagValidation`** (fast, ≈ 0.04 s): χ_Q(U_2) by CRT at T4 (2, 6) = (x − 1)(x − 128)(x + 8)², split, 3 distinct roots = d,
  `upper_bound_certified` with C(f, E^(1)) | 1, C(f, E^(2^7)) | 136 (with g_P^an = 2^7·17 from HZ-RAT), C(E^(1), E^(2^7)) | 127; at T5
  (8, 10) = x^16 (x − 1)(x − 2048)(x² + 24x + 2048)², `non_reduced_certified` (22 − 16 < 13 − 6). The tag's scope guard (audit F1:
  the counting argument needs N a power of p): at (12, 2) (margin 0) and (24, 2) (raw criterion 24 − 18 < 16 − 5 holds) U_2 the tag
  is not set and the text says `nr_scope=N_not_p_power(criterion=0|1)`. **S25 HZ-RAT-PERF fix round 1** (`slot25/HZRATPERF_report.md` §8; ≈ 0.25 s,
  25 MB in all): **RT** the U_p routes of `UTagRuns` (`count_once`: n = 0, the prime-independent count matrix built once; `dense_per_prime`)
  against the shipped term route (`RunAtPrime`) entrywise at three word primes — (11,0) U_11, (37,0) U_37, (26,0) U_13 count_once, (26,0) U_2 and
  (8,10) U_2 term_table, (2,6) U_2, (3,4) U_3, (26,12) U_13 dense_per_prime, both new routes exercised; **CAP** (2,6) U_2 (3 primes) refused at cap 2,
  the default text at cap 3 (F7); **THREADS** (37,0) U_37 and (2,6) U_2 equal at 1 and 4 threads (a fifth cell). 26 checks. Gate line
  `HECKEZ_UTAG cells=5 mismatched=0 verdict=OK` (was `cells=4`).
  **S25 HZ-RAT-PERF re-audit N1** (`slot25/HZRATPERF_reaudit.md` §3, on `s25-wip-ratperffix2`): **RT-MULTI** the RT cells all run
  `BuildCounts` as one slice on one worker; (37,0) U_37 with the validation-only slice size of 64 terms (`UTagRuns(…, count_slice_terms,
  &UTagCountInfo)`; one Merel matrix per slice, ≥ 3 slices on ≥ 2 of 4 workers, the default still 1 slice) = the term route at 3 word
  primes — the multi-slice, multi-worker partial-count sum of (431,0) … (2089,0), kept in the **fast** tier (the alternative cell (431,0)
  costs ≈ 17 s). 27 checks; the gate line unchanged.
- **Read-only arm** `HECKEZ_RAT_CELLS="N:n,N:n,..."` (report only, checks nothing, changes no value): one `ARM (N,n) … secs=` line per cell
  (P = the first four primes of 2..13 prime to N, 4 threads), then `EFFECTIVE HeckeZRationalValidation arm=cells cells=<k> refused=<r>`;
  the factoring-cost measurement of `HZRAT_report.md` §4 is this arm over the level-1 cells n = 10 .. 118.
- No verb, setting or token; nothing reaches a record, a golden object or a campaign job id.

### Slot 25 HZ-LOC (the local reads of the Hecke structure over Z; `slot25/00-slot25-plan.md` v0.2 wave 2, `slot25/HZLOC_report.md`)

Two new names (roster 270 → **272** = 74 / 152 / 46; `--all` 226). Library `Integral/HeckeZLocal.{h,cpp}` (Z/ell^K on
`engine::ModCtx<uint64_t>` — every modulus ell^K < 2^63, FX-1 / R-1 —, Howell spans, Smith valuations, division-free Berkowitz, the
reads) and `HeckeExt/HeckeZLocalSource.{h,cpp}` (the level-1 source: `ringalg::RunModule`, which is H^1 / ell^K and equals L / ell^K
iff it is free of rank b1; otherwise — level N, ell in {2, 3}, a level-1 torsion prime — the EXPORT's free block). Reads per (cell, ell):
(C3) dim A'_1(L/ell) = d [C, prop:heckeZgen]; the monogenic test and the stopping rule e [C, prop:heckeZmono], [C, prop:heckeZlocal],
the `AK_unsaturated` route when dim A'_1 < d; (2.6) the Eisenstein block's lifted idempotent and the components through it
[C, prop:heckeZthrough]; the at-root read (01 P 5.4) with the HZ-RAT cusp part and, per T_p, c_p = sqrt(chi_L(T_p)/(x - lambda)^r)
mod ell^K, and the ell-wise Eisenstein certificate (01 P 5.3): `closes` iff v(exp eta_L) >= v(g_P). A level-1 torsion prime's H^1
module is read only as `A1_of_computed` (never certified). Refusals `refused(word_modulus)`, `refused(export_word)` (level N,
ell >= 46341: the export serves K <= 1 — HZ-LOC's scope limit), `blocked(export)`, `refused(by_theory)`, `general_case`.
**Audit fixes (2026-11-06, `HZLOC_report.md` "Audit fixes"):** the read set at ell is P plus T_ell when ell ∤ N and ell <= 23170
(`t_ell=added`; else `omitted(cap:ell>23170)` / `omitted(ell|N:U_ell_not_exported)` / `omitted(export:…)`), and g_P is taken
ell-wise over P ∪ {ell} (`v_gP=..(hz_rat+T_ell)` when T_ell lowers it) — lead decision on F1, `04-record-census.md` §1.5 amendment;
the K-escalation (`ReadCellLocal`) carries a refusal into the read's root / C_T (F2); each read prints `word=` (the word
`RunModule` ran on: u32 / u64 / digit / hida, or `export`; F3).
- **`HeckeZLocalValidation`** (standard, ≈ 10 s, ≈ 0.33 GB, 146 checks): T1 (1, 10) at 691 (dim A'_1 = 2, e = 0, both components through the block,
  eta_L = Z/691, closes); T2 (1, 22) at 103 and 2294797 (u64); **the u64 item** — every certified prime >= 5 of g_P at (1, 24), (1, 26),
  (1, 28), (1, 30), (1, 42), the seven named primes with ell^2 > 2^31 (T2's 2294797; 657931,
  362903, 1001259881, 305065927; 2947939, 1798482437) pinned by value, each `word=u64` (RunModuleT<uint64_t>) and closing at v = 1, any
  other prime with ell^2 > 2^31 a mismatch; 11 at (1, 42) with T_11: (C3) certified (dim 4 = d), v_11(g_{P∪{11}}) = 0, closes, C_T
  11-part exactly 1; (1, 246) at 37 local-only (D = 41, d = 21, pinned: closes, v_37 = 1); T3 (11, 0) at 5
  on the export (eta_L = Z/5); T4 (2, 6) anemic, r = 2, at 17 (pinned: a = [0, 1], eta = Z/17, closes) and at 2 (K = 9, pinned: θ a =
  [7, 7], eta_2 trivial, v_2(g_P) = 7, `upper_bound_certified` 2^<=7; no U_2); the torsion routing at (1, 40), ell = 7 and (1, 24),
  ell ∈ {7, 11, 23} (F5); the escalation arm (2, 22) at 2294797 from K = 1 → `refused(export_word)` (F2); refusals, and (1, 40) at 3
  with T_3 (closes, 3-part 1). Gate lines `U64_ITEM named=7 closed=7 verdict=OK`,
  `HECKEZ_LOCAL cells=30 mismatched=0 torsion_prime_certified_from_H1=0 verdict=OK`.
- **`HeckeZLocalCensusXcheck`** (slow): the 213 saturated census-4.0 rows of the level-1 list
  (`slot25/hzloc/census40_level1_saturated.tsv`, from `mk_census_rows.py`, sha256 of the two sources in its header) against the per-block
  invariants (dim_E, length_A, Hilbert function, embdim, Gorenstein, Loewy) re-read by HZ-LOC's spans on `ringalg::RunModule` at K = 2
  with P = {2, 3, 5, 7, ell} (the census operators), blocks by `RationalSystems` / `Localize`; each row matched to a distinct block,
  also on the system (the census witness T_2: a_2 = −c for `witness_poly` [c, 1]) and the block rank D = `module_D` (audit F6; the
  TSV carries `witness_poly`, `module_D`, `label_system`, and `mk_census_rows.py` checks the full sha256 against `MANIFEST40.txt`).
  Gate line `HECKEZ_LOCAL_XCHECK rows=213 disagree=0 unchecked_witness=0 unchecked_module_D=0 dim_E_not_computed=86 verdict=OK`;
  informational `XCHECK nonreduced_blocks_without_saturated_row=8`. Audit-fix run: 117 (n, ell) cells, 8:30 wall, peak RSS 1.30 GiB.
- No verb, setting, token or env variable; nothing reaches a record, a golden object or a campaign job id.

### Slot 25 H3 (Mazur's Eisenstein ideal at prime level, integrally; `slot24/heckez/06-work-packages.md` "H3", `05-hida-targets.md` §3, `slot25/H3_report.md`)

One new name, **standard** (roster 272 → **273** = 74 / 153 / 46; `--all` 227). Library `Integral/HeckeMazurEis.{h,cpp}` on HZ-RAT's word-prime
route (`RunAtPrime`, `CharpolyOfCombination`, `ZFromResidues`) and slot 15/22's `HeckeLevelNR3` (`ReadEisensteinR3Scan`, `MazurGoodPrime`,
`MerelCriterionLN5`, `NumConditionValuation`). Per cell (N, ℓ), N prime, ℓ ≥ 5, ℓ | ν = num((N − 1)/12), weight 2:
c_q = √(χ_Z(T_q)/(x − 1 − q)) by CRT (per word prime: the division's remainder 0 and the top-down monic square root re-squared, counted as
`structure_failures`; bound |c_i| ≤ binom(g, i)(2√q)^i); the Hensel factor F_q of c_q at 1 + q mod ℓ^K (ℓ^K < 2^62; linear lifting,
F·H = C re-checked); the good-prime finder (Mazur good primes in increasing order, batches of 4, ≤ 16) **accepts q only on the valuation check**
v_ℓ F_q(1 + q) = v_ℓ(ν) (A7-M1), and re-checks goodness by two modular powers. Checks (a) deg F = e_W = (dim W − 1)/2 of [C, LN6]'s reading
on {2, 3, 5, 7} and (e ≥ 2) ⇔ Merel [C, LN5]; (b) F(y + 1 + q) Eisenstein when ℓ ∥ ν; (c) a good q passes the valuation check; (d) at ℓ² | ν
the Newton polygon, the embedding dimension of Z_ℓ[y]/(F) (1 ⇔ DVR) and irreducibility over Q_ℓ when the polygon decides it, reported.
- **`HeckeMazurEisValidation`** (standard, ≈ 0.1 s, 17 MB): (11, 5), (31, 5), (41, 5), (61, 5), (71, 7), (101, 5) (ν = 25), (113, 7),
  (131, 13), (151, 5) (ν = 25), (181, 5) (e = 3); expected e = 1 at (11, 5), e = 3 and Merel at (181, 5); the negative control (61, 5) at the
  forced good q = 37 (61a: a_37 = 8 ≡ 1 + 37 mod 5) has deg F = 2, v F(1 + q) = 2 > 1 and is rejected. Gate line
  `HECKE_MAZUR_EIS arm=default cells=10 a_ok=10 b_ok=8/8 c_ok=10 good_q_ok=10 d_reported=2 … negative_control=rejected … verdict=OK`.
- **Read-only arms** (change no value, write nothing): `HECKE_MAZUR_EIS_ALL=1` (the whole H3 list `MazurEisCellList()`: C4 ∪ [C, LN6]'s
  168 = 180 cells; ≈ 5 CPU-h single-threaded, the largest cells N ≈ 1950 ≈ 12 min, < 60 MB) and `HECKE_MAZUR_EIS_CELLS="N:ell,…"`; each
  prints `EFFECTIVE HeckeMazurEisValidation arm=<ALL|CELLS> cells=<k> parse_refused=<r>`; a malformed or out-of-scope `_CELLS` cell is refused
  and fails the arm. The gate also fails on `cells == 0`, on the default arm unless `cells == 10` and `refused == 0`, and on the ALL arm unless `cells == 180`. Check (b) is implied by the acceptance rule (not an independent test of Calegari–Emerton; the content is (c)). The negative control is pinned to `e = 2, v = 2`. `slot25/H3_report.md` is the `_CELLS` arm over the 180 cells, one process each.
- No verb, setting or token; nothing reaches a record, a golden object or a campaign job id.
### Slot 25 EXPORT-Z step 1 (H^1 over Z as a presented Hecke module: tau and M; `slot25/EXPORTZ_design.md`, `slot25/EXPORTZ1_report.md`)

- **New name `HeckeZExportZValidation`** — **`standard`** (≈ 3.0 s and ≈ 142 MiB max RSS alone since the audit fixes, `/usr/bin/time`), roster 273 → **274 = 74 / 154 / 46**, `--all` 228,
  `--all` runs **226**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code:
  `Integral/Descent/DescentModuleExportZ.{h,cpp}` (`modexport::ExportModuleZ`, `RetractionFnv`, the step-2 batch hook
  `MatricesInBasisBatch`), `DescentModuleExport.{h,cpp}` (additive: `ModuleExport::retraction`, `ExportOptions::basis` → `F_basis`);
  console: the method `DescentRecord.module_Z()` (script `059_s25_descent_module_z.oc`, new `.expected`).
- **What it checks** (cells (1, 10) [2, 3], (2, 6) [3, 5], (8, 10) [3, 5], (9, 8) [2, 5], (11, 0) [2, 3], (11, 2) [2, 3], and since the
  audit fixes (1, 30) [2, 3] (Z/25, Z/29) and (5, 12) [2, 3] ((Z/5)^2 at ell = 5 | N, Z/11); seven arms, **633 checks**; each arm prints
  `ARM (x) checks= floor= skipped= failed= seconds=` and **fails below its floor** (124 / 62 / 76 / 79 / 213 / 24 / 55 for A B C D E G S);
  a skipped block prints `SKIP <arm> <cell>: <reason>`):
  (A) τ_p an endomorphism of ⊕ Z/d_i, block-diagonal over ell, τ_p τ_q = τ_q τ_p, the full ell-local block [[τ, M], [0, F_local]] commutes;
  the retraction π_ell kills B^1 (against d^0 re-built from the model), π_ell(g_b) = δ_ab, π_ell(free generators) = 0, its FNV reproducible;
  (B) the d_i per ell = the torsion of the record's H^1, r = its free rank, char(F_local) = the record's char_Z mod ell^K;
  (C) cochain-level presentation: T_p g_j − Σ_i A_ij g_i ∈ B^1 + ell^K C^1 for every generator, decided by a fresh Smith form of
  [d^0 | residuals] over Z/ell^K (its levels = those of d^0), the operators re-built from the shipped constructors; a perturbed entry is rejected;
  (D) τ's ell-block read by `hecke3::Invariants` = the record's torsion canon (q = 1);
  (E) splitting invariance: random h ∈ Hom(L, T_ell) (two seeds), the moved generators g_j + Σ h_ij t_i are presented by M + τh − hF_local
  (by (C)); the unmoved M is rejected where it differs;
  (G) hand checks: (11, 0) T = 0, r = 3; (1, 10) Z/2 + Z/4 + Z/3, r = 3, char_Z(T_2) = (x − 2049)(x + 24)^2; (8, 10) (Z/2)^3 + Z/4 + (Z/8)^2 + Z/3,
  r = 22; the step-1 words (`free_block = pending(step 2)`, `export_retraction/v1`, `split = unknown`, `M_basis = local`, `word`); a forced
  `[RssCeiling]` gives `blocked(export)` with no τ; a provider accepted at ell = 2 and refused at ell = 3 leaves `free_rank = 0` and no
  torsion data; (1, 30) and (5, 12) by hand (both also matched against the audit's independent model, 3530 / 1103 checks, 0 mismatches);
  (S) the step-2 hook: one random integral B at (1, 10) and q = 691, 65521 (and 7, 1009 in the batch): char(T_p in B) = char_Z mod q^{K_max},
  T_2, T_3 commute in B, B = the export's free generators gives its free block (also the tree at (8, 10), ell = 2), B G conjugates, a
  singular / misshaped B is refused by name, the batch at 1 and 2 threads is bit-identical (ok, K, why, F); q = 3 refused (`q >= 5`); q | N
  refused by name; an injected lane defect is rethrown after the join, never `std::terminate`; B = Own G + Tors h + d^0 w (G a random unit)
  where the export has torsion at q — (9, 8) q = 7 (cokernel) and (8, 10) ell = 2 (tree) — gives G F_B = F_own G and char(F_B) = char_Z mod
  ell^{K_max}, K_max < K_run. Run once under `CheckThread` (TSan) at the audit fixes (`EXPORTZ1_report.md`, "Audit fixes").
- **Gate line**: `HECKEZ_EXPORTZ arms=7 failing=0 cells=8 checks=633 largest_torsion_prime=29 free_block=pending(step 2) verdict=OK seconds=…`.
- No env hook, no emitter, no setting, no record key, no golden object; the record's bytes are unchanged.

### Slot 25 HZ-TOR (Tor terms, separation, splitting, the glue; `slot24/heckez/06-work-packages.md` "HZ-TOR", `03-bockstein-tor.md` B2, B7, B8, B11–B14, `slot25/HZTOR_report.md`)

- **New name `HeckeZTorValidation`** — **`standard`** (≈ 1.7 s and ≈ 34 MiB max RSS alone, `/usr/bin/time`), roster 274 → **275 = 74 / 155 / 46**,
  `--all` runs **229**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code: `Integral/HeckeZTor.{h,cpp}`
  (`heckez::tor::ReadTor` on the EXPORT at (N, n, ell) with HZ-LOC's read set `ReadPrimes` (T_ell added); `ReadExtension`, the solver on any
  extension [[C_p, beta_p], [0, B_p]] mod ell^e; `SolveLinear`, a Smith form with transforms over Z/ell^E giving a section, a dual witness and
  the kernel length; the EXPORT-Z step-2 entry `SplitFromModuleZ` / `ModuleZSplitWord`).
- **What it checks** (25 export units + 7 toy / control reads, `cells=32`; 324 checks): (A) (1, 18), (1, 20) at 5: no single T_p separates
  (03 §3.1), the joint T'-blocks do: `split(separated)`, every J `zero`; the control without T_5: one common T'-block, |Hom_T'| = 5;
  (B) (1, 26), (1, 30) at 5: one common block (r_m = 2), `split(T')` with the section checked by substitution, J `bounds(<=5^2)`, j' = 1
  (J ∩ T' = 0), coincidence `not_certified(T'_block)`; (C) **K5**: B2(1) h^q = b_q + t_q + t_{q+1} (t_4 := t_2) from the descent record's
  groups at (1, n), n even in [8, 60], ell = 2, 3, against `slot22/lv/lean_dims_l{2,3}.tsv` (rows `lean_dims = 1`): 54 / 54;
  (D) **K6** at (1, 8), ell = 2: chi(T_2 | L) = x + 1, chi(T_2 | tors) = x^2, gcd 1 with a checked Bézout pair, a torsion-only point;
  (E) **B8 / Cor. B8'** at the eight cells of 03 §6.2 at 2 and 3: T_p ≡ 1 + p on H^1 / ell (p ≠ ell), torsion-only point iff S_k = 0
  (n = 8, 12), else one common block with T_ell residue x, `certified(B8)`; (F) T4 (2, 6) at 5: r_m = 2, `split(T')`, |J| ≤ 25;
  T5 (8, 10) at 3: r_m = 12, `split(T')`, |J| ≤ 3^12, `lean = absent(cap)`; (2, 6) at 2: one anemic block, `split(T')`, |Hom| = 2^24 (every T_p, p = 3, 5, 7, is the scalar 1 + p^7 on H^1 / 2^6);
  **(8, 10) at 2: `non_split` for T** (dual witness checked; B14 coincidence), the same verdict at K = e, e + 1, e + 2 (B12(1)), and (1, 30)@5
  `split(T')` at K = 3, 4; (G) toys: the B12(3) counterexample (`non_split`, witness, J bound 25 although J = 0), tamper β = 0 → split,
  mixed exponents Z/3 + Z/9 (non-split twice), a separated toy (Bézout checked), `SolveLinear` on a consistent and a perturbed system;
  (H) EXPORT-Z: at (2, 6) and (8, 10), P = [3, 5, 7], `SplitFromModuleZ` = the export read byte for byte at every torsion prime, and
  `ModuleZSplitWord` folds them; (I) the 25 units on 1 and 4 threads: digest equal; (J) presentation invariance: three random
  re-presentations g' = gG + τh_0 (G unimodular on L) at (8, 10)@2, (1, 30)@5, (1, 26)@2, (1, 18)@2, (8, 10)@3: the matrices move and
  every verdict, Hom length, J word, j' and |A'_K| stays (15 / 15); (O5) the T4 (2, 6) 2-adic at-root read for the referee:
  chi(T_p | L) = (x − 1 − p^7)^2 (x − a_p)^2 mod 2^20, Smith valuations of T_p − a_p on L / 2^20 equal [v, v] with v = 7, 9, 8 for p = 3, 5, 7.
- **Gate line**: `HECKEZ_TOR cells=32 mismatched=0 exact_J=0 verdict=OK` (`exact_J` counts any J emitted as `exact`: CB-3 forbids it).
- No env hook, no emitter, no setting, no record key, no golden object; the descent, EXPORT, EXPORT-Z and HZ-LOC code is not edited.
### Slot 25 HZ-REC + HZ-EMIT (the record `integral_hecke_structure/v1` and its certificate emitter; `slot24/heckez/06-work-packages.md` "HZ-REC", "HZ-EMIT", `slot25/HZREC_report.md`)

- **New names `HeckeZRecordValidation`** — **`standard`** (≈ 6 s, ≈ 86 MiB max RSS alone, `/usr/bin/time`) — and
  **`HeckeZCertDumpValidation`** — **`slow`** (a no-op printing `[SKIP]` without `HECKE_DUMP_HZ_CERT`; ≈ 2 s on its default list) —
  roster 275 → **277 = 74 / 156 / 47**, `--all` 230 (after HZ-TOR). Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`).
  Code: `Integral/HeckeZRecord.{h,cpp}` (the schema: fields with vocabularies, the closed status list of [C] item 8 (c) with its
  pending / final classes, `record_fnv1a64` / `cert_sha256` / provenance, the builder `BuildHeckeStructureRecord` with injected sources,
  the scans, the ed.1 join, `WriteCertFiles`), `HeckeExt/HeckeZRecordSource.{h,cpp}` (the shipped sources: `ReadCellLocal`, `BernoulliOverK`;
  HZ-LOC audit F8), `HeckeExt/RegisterHeckeZRecordVerbs.{h,cpp}` (the console verb `hecke_structure(N, n, algebra = "full")`,
  script `060_s25_hecke_structure.oc`, new `.expected`), `Campaign/CampaignHeckeZ.{h,cpp}` (the campaign key `structure = hecke`, grid key
  `algebra`, output knob `hz_cert`; `campaign.md` §18), `lean/tools/hzcert_to_lean.py` (the untrusted K3 generator, manifest
  `lean/cells/HZ/manifest.tsv`).
- **`HeckeZRecordValidation`** (the five toy cells T1 = (1, 10), T2 = (1, 22), T3 = (11, 0) anemic, T4 = (2, 6) anemic + full, T5 = (8, 10)
  anemic + full; seven records, **49 checks**): each record's status signature (G1 C1 / reduced_Q / C2, the per-ℓ generation status and
  route, C_T, the fibre product, the count of `pending(HZ-TOR)` fields, the overall status) equals the frozen table
  `Integral/HeckeZRecordExpected.inc` (04 §2 as built, every deviation in `HZREC_report.md` §3); the scans: no value outside its
  vocabulary (status words, enumerations, `int`, `zbig` = canonical signed hex, `hex64`, `sha256`, `t_ell` with `omitted(export:<Name>)` by
  name only), no conditional field (local types, pair kinds, `C_T.exact`, `deg_f`) under a parent that is not `certified`, and the overall
  rule (`pending` iff a hashed field is pending); `record_fnv1a64` and `cert_sha256` equal at 1, 4 (level 1) and 16 threads; four tamper
  arms ((1) a status flip moves the record hash and orphans the local type, (2) a G9 change moves `cert_sha256` only, (3) a cap change
  moves the fingerprint, the id and the hash, (4) a Lean cap change moves `cert_sha256` only); the ed.1 join (descent `record_fnv1a64` and
  every char_Z digest against `docs/integral_census/results/ed1/rows.tsv`; `cell_sha256` joined); the word mapping of the Z0 merge report §7
  through three forged sources at T1's ℓ = 691 (the export's `open(precision)` above its K_max → `refused(export_word)`, pending; the
  level-1 module route's `refused(word_modulus)` at a ℓ < 2^63 → (C3) `refused(k1_route)`, pending; the step cap → `open(precision)`,
  final; line `HECKEZ_RECORD_WORDS export_word=mapped modes=3/3`); the refusals of item 8 (a) (F_ell in
  force; `anemic` at N = 1); the vocabulary classes; T1 and T2 golden-eligible (`final`) with HZ-TOR wired. Since the HZ-TOR merge the
  G4–G6 fields come from `ReadTor` (`HZREC_report.md` §4): `HZREC_DIGEST … golden_eligible=4` (T1, T2, T3, T4 anemic).
  **As of the re-audit fix round (2026-11-06, `HZREC_report.md` §10; supersedes the counts above): 70 checks, ≈ 10 s, ≈ 0.14 GB.** The
  table pins `{signature, record_fnv1a64}` of all seven records (F14, re-pinned at §10); seven tamper arms (the four above, (5) a provenance
  change moves neither hash, (6) the resume check rejects a hash-breaking G6 edit and an out-of-list value, (7) with the hashes recomputed
  `split_on_P → split`, a vocabulary swapped to `status`, a blanked parent, an added G8 field and a changed header `descent_ref` are rejected
  by the schema table of the scan, re-audit R5); six word-mapping modes (the three above, (4) `[Lift]` with a cap → `blocked(export)`,
  (5) `[Lift]` with a certificate code → `refused(no_lift)`, final, (6) `[ModulePrecision]` → `refused(export_word)`, R6) and
  `ExportWord` on seven texts; R1 (`components[0].mult = e_k`: 2 at (2,6) anemic), R9 ((1,26) at 7 decomposed by `θ = T_5 + T_7` over
  P ∪ {T_7}), F1, F2, F5, F6 as before. (Slot-27 EXW: the forged sources run with EXW off, `local_read_free = nullptr`; the pin
  `8,10,anemic` is EXW's, see "Slot 27 EXW".)
  **Gate lines**: `HECKEZ_RECORD_WORDS export_word=mapped modes=6/6`; `HECKEZ_RECORD cells=5 status_table=exact hashes_pinned=7/7 exact_under_bound=0 values_outside_lists=0 threads_equal=yes tampered_detected=7 ed1_digest_mismatch=0 verdict=OK`.
- **`HeckeZCertDumpValidation`** (HZ-EMIT): `HECKE_DUMP_HZ_CERT=<dir>` (must exist, outside the source tree, else `REFUSED`, exit 1);
  `HECKE_DUMP_HZ_CERT_CELLS=<N:n:ell[:K][:full],…>` (S26 Z1: `:full` at N > 1 adds the `<record id>.Up<p>.mat` files; n even ≤ 60; set-but-empty or malformed: `REFUSED`; default `1:10:691, 1:22:103, 1:22:2294797`)
  writes `hzcert_N<N>_n<n>_<K1|K2|K3>_l<ℓ>.txt` (TAB-separated key / value lines, matrices row-major decimal) twice and compares them byte for
  byte; the dump sha256 recomputed in each file must equal the record's G9 value. Prints `EFFECTIVE HeckeZCertDumpValidation arm=<default|cells> cells=<k>`
  then `HECKEZ_CERT_DUMP cells=<k> files=<f> byte_stable=yes dump_sha_mismatch=0 verdict=OK` (default list: 8 files). n > 60 is emitted
  by a `structure = hecke` campaign with `hz_cert = on` (<output>/hzcert/), not by this hook.
- No setting, no golden object, no existing transcript; the descent, EXPORT, HZ-RAT, HZ-LOC code is not edited.

### Slot 25 H1 (the Eisenstein component over Λ at irregular pairs; `slot24/heckez/06-work-packages.md` "H1", `05-hida-targets.md` §2, [U] 0.7.0-pre.2 part 6, `slot25/H1_report.md`)

One new name, **standard** (roster 277 → **278** = 74 / 157 / 47; `--all` 231), registered in `Registry/Slot25.cpp` (sources
`cmake/sources/*.cmake`). Library `HeckeExt/HeckeHidaEisLambda.{h,cpp}` on HeckeHidaLambda's q-expansion arm
(`ComputeFormsWeight`, the certified Fitting split of the full residual system, now exposed as `lambda::EisensteinBlock`): `ReadBlock` /
`ReadBlockFrom` (the ordinary Eisenstein block of `e S_k`: g, per `q` the valuation of `det(T_q − e_q | block)` and whether `T_q − e_q`
generates mod ℓ, `v(B_k/k)`, the λ-test, `χ(T_2 | block)`), `K9Line` (the Lean checker K9's integers below ℓ² with its four kernel checks),
`HidaBlockAt` (the record's G8 source), `RungPrediction` ((U23)).
- **`HeckeHidaEisLambdaValidation`** (standard, ≈ 12 s, ≈ 135 MiB, 164 checks): (A) [U, prop:u-H11] on the C2 chains — 11 pairs (37, 32),
  (59, 44), (67, 58), (101, 68), (103, 24), (131, 22), (149, 130), (157, 62), (157, 110), (691, 12), (691, 200), 29 weights (k ≤ 258; 691 at
  12, 702, 200), forms side mod ℓ³: g = 1, L_forms = min_q v(a_q − e_q) = v(B_k/k) at every weight ((U1) on the forms side; 103 at k = 228
  is on its rung, v = 2), the generator of the first weight at every weight (T_2 at all 11 pairs), one `HIDA_H11` and one `HIDA_K9` line per
  pair (K9's checks 11/11); (B) (U1) on cohomology, `HeckeHidaComponents` at K = 3 on (30, 37), (66, 37), (42, 59), (56, 67), (66, 101),
  (22, 103), (20, 131), (60, 157): D = 3, g = 1, L_coh = v(B_k/k), kind exact; (C) the record's G8 under `heckez.G8 = hida`: the 15 golden
  default records of `HZREC_report.md` §10.2 recomputed bit-identical (fingerprint `0x8ffc29730c4f9672`, golden-eligible, no G8 field, the `off` line byte
  for byte), the hida records (1,10), (1,22), (1,30) (fingerprint `0x08cec5d00e4d4294`, pinned record hashes, final but `golden_eligible = false`: H1 audit F1; re-pinned after F4's settings-line text) with the settings
  text differing in the G8 line only, every G0–G7 field equal to the default record's, the Eisenstein ideal's G8 equal to (A)'s reading,
  (1,30)'s non-ordinary cuspidal ideal at 29 (T_29 nilpotent on S_32 mod 29), the scan clean, the cell file verified; tamper 3/3; `lambda`
  refused. Gate line `HIDA_EIS_LAMBDA pairs=11 h11_held=11/11 u1_forms_held=29/29 coh_held=8/8 k9_ok=11/11 golden_default_unchanged=15/15
  g8_records=3 g8_agree=3/3 tampered_detected=3 verdict=OK`; prints `EFFECTIVE HeckeHidaEisLambdaValidation arm=<DEFAULT|ALL> cells=<k>`.
- **Read-only arms** (change no value, write nothing): `HECKE_HIDA_EIS_ALL=1` ((B) on every chain weight, (198, 691), (700, 691) and (D2) at
  (484, 547): D = 5, g = 2, L_coh = 1); `HECKE_LAMBDA_CELLS="ell:a:K:m,…"` on **`HeckeLambdaValidation`** (replaces its default arms after the
  self-tests; `EFFECTIVE HeckeLambdaValidation arm=CELLS cells=<k>`): the truncation of the Eisenstein component at any cuspidal rank, N = K + m − 1
  weights a, a + (ℓ − 1), …, forms data mod ℓ^{K+N−1}, the T_p to the Sturm bound; checks the ranks (1 + g, g), the monogenic route at rank 1 + g,
  F(0) = 0, (F_1) = (G̃) = (Z − (α − c)), the general route, |coker|, J = (G̃), the structure (`fibre_LxL` | `regular_deg_g`), I^0 = (T_p − e_p),
  (U1) and K9 at every weight, and at g = 2 v(disc f_k) = 1 and the rung prediction (U23); at (547, 486) the data (D1), (D3) of [U, prop:u-H12].
  `547:486:3:3`: 43 checks, ≈ 85 s, ≈ 95 MiB; `HECKE_LAMBDA_CELLS cells=1 records=2 … verdict=OK`.
- New campaign key `hz_g8 = off | hida` (`structure = hecke` only; `campaign.md` §18). No verb, setting or golden object; the default records,
  their fingerprint and the golden list never move.
### Slot 25 EXZ2-P1a (EXPORT-Z step 2, package P1a: the carrier Iso_T over Z and the Dixon pairs; `slot25/EXPORTZ2_design.md` v2 §1.0, §1.1, §7, `slot25/EXZ2P1a_report.md`)

- **New name `HeckeZFreeBasisPairsValidation`** — **`standard`** (≈ 0.2 s and ≈ 24 MiB max RSS alone, `/usr/bin/time`), roster 278 → **279 = 74 / 158 / 47**,
  `--all` runs **232**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code:
  `Integral/Descent/IsoTreeCarrierZ.{h,cpp}` (`freez::IsoTreeCarrierZ`: d^0, d^1 of Hom(Iso_T, M_N) over Z as sparse `nf::BigInt` matrices,
  `RhoNZ` / `RhoNAbsZ`, the lanes `apply_hecke_mod` = Ψ^* T̃_Iso Φ^* mod q, `d_mod`, `apply_hecke_majorant`; `EchelonModQ`, the
  left-looking zero-skipping sparse echelon mod q0; `BuildPairs`, the K = 3 Dixon pairs under `iso_dixon/v2` with RNS residual products,
  Garner, the model's reconstruction schedule and the multimodular exactness proof; `PredictPairsRss` and the `[RssCeiling]` refusal);
  `DescentHecke.h`: `IsoHeckeN::terms_Z()` (the integer term list) and `IsoHeckeN::modulus()` (additive; no value moves).
- **What it checks** (five arms, **608 checks**): (C) `RhoNZ` mod p = `rho_n_cubic` (n ≤ 30, det 1, det p, a = 0) and |ρ_n(g)| ≤ ρ_n(|g|);
  on (1, 10), (2, 6), (11, 2), (5, 12), (9, 8): d^0, d^1 over Z reduced mod 1000003 and q0 = `TreeModelChain(0)::coboundary` on the dense
  `InducedSymModule` entrywise, = the lane route `d_mod`, d^1 d^0 = 0 over Z; (T) on (1, 10) T_2, (2, 6) T_3, (11, 2) T_2, (1, 12) T_3:
  `terms_Z` reduced applies as `IsoHeckeN::apply` in degrees 0–2, T̃_T = Ψ^* T̃ Φ^* is a cochain map 0 → 1 → 2 mod a lane, the
  `BlockSign` fault breaks it (teeth), the majorant dominates |T̃_T X| on 0/1 columns; (D) on (1, 10), (2, 6), (11, 2), (11, 0), (1, 30),
  (9, 8): rank d^1 + rank d^0 + b_1 = dim C^1, |P_s| = r, d^1 B_s = 0 and Φ_s^T d^0 = 0 by plain BigInt products, supports / positivity /
  primitivity, the rotation, det(Φ_s^T B_s) ≠ 0; on (1, 10), (2, 6), (11, 2) every column = the primitive exact rational solution of an
  independent Gauss–Jordan over Q; q0-independence (the pairs again at the second `CrtPrimes` prime: the same FNVs); the pinned FNVs of
  (1, 10) (also reproduced by the model's rule in `exz2p1a/exz2p1a_check.py`); teeth b_1 + e_c (no cocycle) and 7 b_1 (not primitive);
  (R) a 1-byte ceiling refuses `[RssCeiling]` with the predicted bytes printed; (M) the `EXZ2_P1A` measurement lines on (1, 10), (11, 2)
  (H_s = Φ_0^T T̃_T B_s by lanes checked against a held-out lane).
- **Gate line**: `HECKEZ_FREEBASIS_PAIRS arms=5 failing=0 checks=608 rule=iso_dixon/v2 verdict=OK seconds=…`.
- **Env hooks** (both no-ops when unset): `HECKE_EXZ2_CELLS="N:n[:p1/p2],…"` (read-only: replaces arm (M)'s cells, n even ≤ 400; set-but-empty
  or malformed: `REFUSED`, exit 1; prints `EFFECTIVE HeckeZFreeBasisPairsValidation arm=<default|cells> cells=<k> dump=<on|off>`);
  `HECKE_DUMP_EXZ2=<dir>` (**an emitter into scratch**: `<dir>` must exist outside the source tree, else `REFUSED`, exit 1) writes per cell
  `c<N>_<n>/{meta,d0,d1,pair_<s>,H}.txt` and, for dim C^1 ≤ 420, `T_<p>.txt` / `Tmaj_<p>.txt` for `exz2p1a_check.py`. No setting, no
  record key, no golden object, no console surface.
- **Changed by EXZ2-P1b**: the rule is `iso_dixon/v3` (P1a audit F1, "alt2": π_s = rot(ρ_t), reversed for s odd, ρ = (0, ⌊D/2⌋, ⌊D/4⌋)[⌊s/2⌋]);
  the (1, 10) s = 1, 2 FNVs re-pinned (s = 0 unchanged); arm (D) checks the v3 order and PackedFnv = MatrixFnv; the pairs are stored
  packed (`PackedZ`), the Dixon is column-batched with an output-sensitive stop, `PredictPairsRss` is the audit's calibrated formula;
  **632 checks**, gate line `HECKEZ_FREEBASIS_PAIRS arms=5 failing=0 checks=632 rule=iso_dixon/v3 verdict=OK`.

### Slot 25 EXZ2-P1b (EXPORT-Z step 2, package P1b: lattice sums, saturation, the det = ±1 certificate; `slot25/EXPORTZ2_design.md` v2 §1.2–§1.4, §6 (B), (E), (F), `slot25/EXZ2P1b_report.md`)

- **New name `HeckeZFreeBasisSatValidation`** — **`standard`** (≈ 4 s and ≈ 26 MiB max RSS alone, `/usr/bin/time`), roster 279 → **280 = 74 / 159 / 47** on its own branch (merged after EXZ2-P2: **281 = 74 / 160 / 47**),
  `--all` runs **233** (**234** merged). Registered in `Registry/Slot25.cpp` (the P1a fragment; sources `cmake/sources/*.cmake`).
  Code: `Integral/Descent/DescentFreeBasisZ.{h,cpp}` (`LatticeSums`: incremental column HNF with transform, the relation lattice LLL-reduced
  (exact, ≤ 48 relations) + Babai, else the reduction by the structural relations of the diagonal first block; `Saturate`: sparse local Smith passes mod ℓ^k (adaptive k), composite
  mode with gcd splits, the multi-word mode, `[SaturationCofactor]` as the resource refusal; `CertifyBasis`: exact d^1 B = 0, Φ^T d^0 = 0
  and det(Φ^T B) = ±1 by residues under the Hadamard bound; `BuildFreeBasis` with the K-escalation 3 → 5); `IsoTreeCarrierZ.{h,cpp}`:
  `PackedZ` (CSC over a limb arena), `PairOrder` / `PairRotation` (v3), `ExtendPairs`, the F10 move to the next q0.
- **What it checks** (six arms, **92 checks**): (M, first, fresh process) one `EXZ2_P1B` / `_SUMS` / `_SAT` / `_CERT` block for (2, 6);
  (S) on (1, 10), (2, 6), (11, 2), (1, 30), (5, 12), (9, 8): B_Σ cocycles and Φ_Σ killing d^0 (dense exact), |det G_Σ| (Bareiss) = Δ_Σ,
  |Δ_Σ| bits = the P1a audit's alt2 figures (1, 2, 1, 42, 29, 18); (B) d^1 B = 0, Φ_cert^T d^0 = 0 and det(Φ_cert^T B) = ±1 by the
  validation's own dense code, the library certificate's sign agrees, basis_fnv = the canonical text's FNV; (K) on (8, 10): π_0 … π_4
  pairwise distinct and none of π_1 … π_4 a rotation by a multiple of D, the K = 5 pairs valid, `ExtendPairs` 3 → 5 = `BuildPairs(K = 5)`,
  |Δ_Σ(K = 3)| bits = 33 (audit) and Δ_Σ(K = 5) | Δ_Σ(K = 3); the structural size reduction (the path above 48 relations) forced on
  K = 3 keeps Δ_Σ and exactness; (1, 10): q0 = 3 (| 6N) skipped, a forced rank drop at q0 moves to the next
  CrtPrimes prime with the same pairs (F10), small q0 = 5, 7, 11, 691 give valid pairs (5, 7 another greedy profile: printed
  `profile=other`); (E) on (9, 8): 7 b_1, 2 b_1 (local mode), 2147483659 b_1 (composite mode), a 71-bit composite multiplier (multi-word
  mode) fail the certificate with |det| = the multiplier and are repaired by `Saturate` to det = ±1; with the multi-word mode off the
  71-bit cofactor is refused `[SaturationCofactor]`; B U (U unimodular) keeps det = ±1; (F) on (1, 10), (2, 6), (11, 2): an
  in-validation integer kernel (unimodular row reduction) gives Z^1 and B^1_sat, det[B | B^1_sat] = ±1 in Z^1 coordinates, = ±7 for 7 b_1.
- **Gate line**: `HECKEZ_FREEBASIS_SAT arms=6 failing=0 checks=92 rule=iso_dixon/v3 saturation=det_pm1 verdict=OK seconds=…`.
- **Env hook**: the read-only `HECKE_EXZ2_CELLS="N:n[:p1/p2],…"` (P1a's) also replaces arm (M)'s cell (2, 6) here (the primes are ignored;
  set-but-empty or malformed: `REFUSED`, exit 1); prints `EFFECTIVE HeckeZFreeBasisSatValidation arm=<default|cells> cells=<k>`. No emitter,
  no setting, no record key, no golden object, no console surface.
- **Fix round 1** (`slot25/EXZ2P1b_audit.md` F1–F13; `EXZ2P1b_report.md` "Fix round 1"): **136 checks** (was 92), same six arms, gate
  line `HECKEZ_FREEBASIS_SAT arms=6 failing=0 checks=136 rule=iso_dixon/v3 saturation=det_pm1 verdict=OK`, ≈ 4 s, ≈ 24 MiB; roster
  unchanged (280). New: (M) the sums alone sampled after `malloc_trim` against `PredictSumsRss` (never below), `q0= q0_confirm=
  q0_skipped=` beside the rule, the rank witness; (K) inline vs post-hoc structural reduction bit-identical on (8, 10), (9, 8) (FNV of
  B_Σ, Φ_Σ), `dixon_batch` 1 / 8 / 32 identical pairs on (9, 8), every small q0 (5, 7, 11, 691) gives the rule's pairs (profile
  confirmed at a second prime), `ExtendPairs` above the ceiling `REFUSED [RssCeiling]`, the K-escalation loop executed on (1, 30)
  through the validation hooks (`testing::FreeBasisHooks`: cofactor limit 2^6, trial bound 8 → K_used = 5, multi-word passes,
  6 splits, certified) and refused `[RssCeiling]` with the pairs' ceiling at the K = 3 prediction; (E) teeth with asserted splits
  (b_1 p1, b_2 p2 composite64; b_1 P1, b_2 P2 multi-word), side Φ (φ_1 p2, φ_1 P1 P2, φ_1 7), B M (M triangular, det 504), no side-Φ
  pass for a B-only piece, `[SaturationStall]` at once (Δ given 49 for 7), r − 1 columns fail the rank witness.

### Slot 25 EXZ2-P2 (EXPORT-Z step 2, package P2: RNS lanes, the §1.6 bound, the proven CRT, BigInt output; `slot25/EXPORTZ2_design.md` v2 §1.5, §1.6, §2, §7.4, `slot25/EXZ2P2_report.md`)

- **New name `HeckeZFreeBlockCrtValidation`** — **`standard`** (≈ 2.3 s and ≈ 150 MiB max RSS alone at `ENGINE_THREADS=4`, `/usr/bin/time`),
  roster 279 → **280 = 74 / 159 / 47** on its own branch (**281 = 74 / 160 / 47** merged with EXZ2-P1b), `--all` runs **233** (**234** merged). Registered in `Registry/Slot25.cpp` (sources
  `cmake/sources/*.cmake`, which also adds `src/ModArithmetic/RnsKernels.cpp` to the `ModArithmetic` target).
  Code: `Integral/Descent/DescentFreeBlockCrt.{h,cpp}` (`freez::FreeBlockCrt`: one lane per word prime — the pair-0 functionals Ψ by a
  per-lane sparse elimination of the rows R0 of d^0 and a transposed solve per column, tiles of B reduced on the fly, T̃_Iso as one
  `kernels::gemm` per integer term, the r × r solve mod q; the upward-rounded majorant β_H = |Φ_0|^T M |B| (`UpReal`), the a-priori
  (Q |det G'| > 2 |adj G'| β_H) and a-posteriori (Q > |G'||F̂| + β_H) proofs, output-sensitive rounds; the GPU lane route
  (`engine::cuda::GemmBatch`, one stream per prime, opt-in); the fixture loader); `ModArithmetic/RnsKernels.{h,cpp}` (`engine::rns::garner_step`,
  portable / AVX2 / AVX-512); `IsoTreeCarrierZ`: `SparseZ::seal()` (no mutable cache), `EchelonModQ::solve` with local scratch and
  `solve_transposed`, `CachedCrtPrimes`, `release_lane` / `release_exact_memo` (audit F7, F11, F13); `IsoHeckeN(…, with_terms_z)`
  (`terms_Z()` only on request, F9). Fixtures `docs/implementation/slot25/exz2p2/fixtures/c<N>_<n>.txt` (9 cells; generator
  `exz2p2/gen_fixtures.py` = the P1a model's saturation on the P1a dumps).
- **What it checks** (nine arms, **291 checks**): (X) each fixture re-certified (d^1 B = 0, Φ_0^T d^0 = 0, Φ_cert^T d^0 = 0 in plain BigInt,
  det(Φ_cert^T B) = ±1, R0 / P = `BuildPairs`' pair 0); (L) single lanes = the model's F_p mod q at ≥ 4 admissible q on (1, 10), (11, 2),
  (9, 8); (A) the proven F_p = the model's exact F_p on all 9 cells and char(F_p) (Berkowitz) = `CharpolyOverZ` on the 6 small ones;
  (C) F_p F_q = F_q F_p, char F_2 = (x − 3)(x + 2)^2 at (11, 0) and (x − 2049)(x + 24)^2 at (1, 10); (P) a-priori alone, a-posteriori alone
  and a later prime window give the same F; teeth: B with a column scaled by s (F not integral) is refused by the a-posteriori test
  within 3× the lanes, a T-stable index-s twin is proven = D^{-1} F D, a 1-lane cap refuses; (D) FNV(F) and the lane residues identical
  for GEMM portable / AVX2 / AVX-512, Garner portable / AVX2 / AVX-512, threads 1 / 4 / 16, tiles 1 / 3 / 128 and (with
  `ENGINE_DEVICE=gpu` and a device; else `[SKIP]`) the GPU lane route; (T) `EchelonModQ::solve` / `solve_transposed` and
  `SparseZ::max_row_abs_bits` from 8 threads, no carrier lane left after a 16-thread run; (R) a 1-byte ceiling refuses `[RssCeiling]`;
  (M) the `EXZ2_P2` measurement lines.
- **Fix round 1** (`EXZ2P2_audit.md` F1–F11, `EXZ2P2_report.md` "Fix round 1"): **eleven arms, 422 checks** (426 with `ENGINE_DEVICE=gpu`).
  `FreeBlockCrt` now establishes both proof premises itself (det G' ≠ 0 by the inverse or a witness prime, else `[SingularG]`; the
  certificate Φ_cert is part of `FreeBlockInput` and re-checked, else `[Uncertified]`; the a-priori post-check, else `[BoundViolated]`)
  and reports data-dependent outcomes as `FreeBlockRefusal` codes (`[NoProof]`, `[Inadmissible]`, …), not exceptions. New checks: (A)
  the bound against the exact H = G'F (|H| ≤ ⌈β_H⌉, |det G'||F| ≤ ⌈|adj G'|β_H⌉ entrywise) and the pinned a-priori prefix /
  bits(β_H) / bits(β_F) per cell and operator; (P) Φ_0 := 0, a zero column and two equal columns at (1, 60) refused `[SingularG]` on
  both routes, 7·b_{1,2,3} at (1, 30) and no certificate refused `[Uncertified]`, a corrupted lane residue refused `[BoundViolated]`
  (and `[NoProof]` a-posteriori only), the inadmissible prime q_1 (column 1 × q_1, `lanes_only`) skipped with residues D^{-1}FD mod q,
  the teeth matching the specific refusal; (U) an `UpReal` battery against exact `BigInt` values (40 000 add / mul, 20 000 `of_big`,
  20 000 `ceil_big`); (Z) rank 0 at (1, 0) and (1, 7) (b_1 = 0; was a SIGSEGV). β_H · 2^−8, β_H · 2^−40 and `UpReal` without
  upward rounding each fail it (mutations, reverted).
- **Gate line**: `HECKEZ_FREEBLOCK_CRT arms=11 failing=0 checks=422 cells=9 verdict=OK seconds=…` (fix round 1; was `arms=9 … checks=291`).
- **Env hook** (read-only, a no-op when unset): `HECKE_EXZ2P2_FIXTURES=<path>[,<path>…]` replaces arm (M)'s list by those fixture files
  (a file without Φ_cert — e.g. from `exz2p2/dump_to_fixture.py` on a P1a dump, B = B_0 — is measured with `lanes_only`: lane timings,
  the bound's bits and the a-priori prime count, no proof); prints `EFFECTIVE HeckeZFreeBlockCrtValidation arm=<default|env> cells=<k>`.
- **`KernelBitIdentityValidation`** gains the RNS battery: `garner_step` portable / AVX2 / AVX-512 against a scalar oracle (plain `%`,
  Horner digits) on three prime sets (the first nine `CrtPrimes`, 2^31 − 1 and tiny moduli, mixed), every tail 1 … 40 (fix round 1: the
  102 checks on empty vectors dropped, 21 034 checks) and 63 / 257 / 1031 / 4099 entries, random and worst-case digits; the `garner_digits` round trip and the sign rule against u64 values.

### Slot 25 EXZ2-P3 (EXPORT-Z step 2, package P3: F exact over Z on T ⊕ Z^r, M in the same basis, `module_Z()`; `slot25/EXPORTZ2_design.md` v2 §5–§7.5 with the as-built (P3) notes, `slot25/EXZ2P3_report.md`)

- **New names `HeckeZExportZ2Validation`** — **`standard`** (≈ 5.9 s and ≈ 180 MiB max RSS alone at `ENGINE_THREADS=4`, `/usr/bin/time`)
  **and `HeckeZExportZ2SlowValidation`** — **`slow`** (≈ 69 s, ≈ 335 MiB), roster 281 → **283 = 74 / 161 / 48**, `--all` runs **235**.
  Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code:
  `Integral/Descent/DescentModuleExportZ2.cpp` (`modexport::ExportModuleZ2` = `RunFreeBlock` (carrier, P1b's `BuildFreeBasis`, P2's
  `FreeBlockCrt`) + `AssembleModuleZ2` (every torsion prime's export run ONCE in the global basis B through `RouteBasis` — the pullback
  along Ψ^T_ℓ, J-coordinates at ℓ ∈ {2, 3}, the edge cochains M_N at ℓ ≥ 5 — then C_ℓ, M_global = M_local C_ℓ and two production checks:
  F mod ℓ^{K_max} = the route's own T_p in B, C_ℓ F ≡ F_local C_ℓ); `ModuleZ::free_view` / `free_view_local` / `free_mod` / `full_matrix`);
  `DescentFreeBlockCrt` takes `PackedZ` and uses P1b's certificate (`CertifyBasis`) and `FirstNonCocycle` / `FirstNotKillingD0`; the
  bound `BoundBasis::{Phi0, PhiCert, Auto}` (Φ_cert: G_c unimodular, `InverseUnimodular` by q-adic lifting, with the a-posteriori test
  of Φ_0 on the same majorant pass; Auto = Φ_0 while r (bits Φ_0 + bits B) ≤ 20000); `HeckeZTor::FromModuleZ` reads `free_view` (HZ-TOR
  audit M1). Console: `DescentRecord.module_Z()` = step 2, `module_Z("local")` = step 1 byte for byte (script 059 now calls it; its
  `.expected` unchanged); new script `061_s25_module_z_exact.oc` (new `.expected`); notebook tour `09_integral_hecke_module.oc`.
- **Standard arms** on (1, 10), (2, 6), (9, 8), (11, 0), (11, 2), (1, 30), (5, 12), (1, 60) (the step-1 cells but (8, 10), plus (1, 60)):
  (R) P2's lanes on P1b's real basis — proven, the Φ_0 and the Φ_cert bound and the production (Auto) run give the same F (FNV and
  entries), threads 1 / 4 / 16 and tile 1 the same F, proof and primes_used, the Auto rule's choice, the Φ_cert bound entrywise, pins
  FNV(B), FNV(Φ_cert) (= P1b's), FNV(F_p) per cell; (A) char(F_p) = the record's char_Z exactly; (C) F_pF_q = F_qF_p over Z and the full
  T_p on T ⊕ Z^r commute (rows < t mod d_i), (11, 0) T_2 (x − 3)(x + 2)^2, (1, 10) T_2 (x − 2049)(x + 24)^2; (G) HZ-TOR's words on
  `free_view` local vs global on every torsion unit (24 units), `ModuleZSplitWord` equal; (H) the global oracle: F mod ℓ^{K_max} = the
  route's T_p in B at every torsion prime and at 5, 7, 13, 1000003, 2^31 − 1 (no torsion; the field above 46341), M_global = M_local C_ℓ
  and C_ℓ F ≡ F_local C_ℓ recomputed, `free_mod` prefix-consistent; (L) the step-1 fields of the basis exports = a plain step-1 run
  (τ, d, M_block, F_local, retractions) on four cells; (T) teeth (`InverseUnimodular` refuses diag(2, 1), inverts [[2, 3], [1, 2]] and
  a 6 × 6 unimodular matrix with 80-bit entries; F_11 + 1 fails the oracle at every torsion prime; 2 b_1 is not a basis mod 2^K; 7 φ_1
  refused `[Uncertified]`). Verdict line `HECKEZ_EXPORTZ2 arms=7 failing=0 cells=8 checks=507 tor_units=24 free_block=exact
  M_basis=global rule=iso_dixon/v3 verdict=OK`.
- **Slow arms** on (8, 10), (1, 200), (23, 20), (311, 2) with one `EXZ2_P3_STAGE` line per stage (carrier, basis, crt, exports, assembly:
  seconds, RSS, HWM) and one `EXZ2_P3` / `EXZ2_P3_BOUND` line per cell (pairs, sums, saturation, certificate, bound, inverse, lanes, lift,
  exports, assembly; both bounds): (R) as above (no tile-1 run), (A) char(F_p) against `CharpolyOverZ` (D3's char_Z route) mod 2^64 and
  mod 3^40 on every certified coefficient (Berkowitz over both rings; the record is not built), (C), (H) (ℓ = 7, 1000003 beside the
  torsion primes). Verdict `HECKEZ_EXPORTZ2_SLOW arms=4 failing=0 cells=4 … verdict=OK`.
- No env variable, golden object, record key, settings key or digest. `HeckeZFreeBlockCrtValidation` keeps its checks and pins (its
  fixtures go through `SparseColsZ::to_packed`; its default bound stays Φ_0).
- **Fix round 1** (`EXZ2P3_report.md`, "Fix round 1"; audit F2, F4, F5): M is served against the classes [b_j] of B (M = M_local C_ℓ −
  π_B F + τ π_B; the "M_global = M_local C_ℓ" above is the pre-fix block), π_B and `M_fnv` / `pi_B_fnv` exported. Standard: (H) adds
  **the M oracle** π_ℓ(T_p B) = M + π_B F at every torsion unit (the route's own operator on B, no M_local, no C; 402 checks), (R) pins
  `M_fnv` per op and `pi_B_fnv` per torsion prime and checks the lanes' route follows `ENGINE_DEVICE`, (T) real teeth (C = I fails the
  commutation, M + 1 and the pre-fix block fail the M oracle at (1, 30), (11, 2), (9, 8); floor 20). Verdict
  `HECKEZ_EXPORTZ2 arms=7 failing=0 cells=8 checks=716 …` (≈ 7.7 s, ≈ 300 MiB). Slow: arm **(D)** the GPU lane route vs the CPU route on
  the four real bases and `ExportModuleZ2(lanes = Gpu)` vs `Cpu` on (8, 10) — `[SKIP]` unless `ENGINE_DEVICE=gpu` and a device (floor 0
  then, 5 with a device); verdict `HECKEZ_EXPORTZ2_SLOW arms=5 failing=0 cells=4 checks=276 …` (261 with the device; ≈ 70–100 s, ≈ 450 MiB).

### Slot 25 NBCONFIRM S3 (the console cost confirmation, core + REPL/scripts; `docs/console/NBCONFIRM_design.md`, `docs/console/NBCONFIRM_S3_report.md`)

- **New name `ConsoleCostModelValidation`** — **`fast`** (≈ 0.1 s, one pty child of the binary), roster 283 → **284 = 75 / 161 / 48**,
  `--all` runs **236**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`, which also embeds
  `Console/cost/cost_models.tsv` into ConsoleCore at configure time). Code: `Console/Core/CostModel.{h,cpp}` (the line-for-line port
  of `docs/console/tools/nbconfirm_estimate.py`: `load_models`, `estimate` incl. the safety rule, `decide`; the feature map of
  `nbconfirm_fit.py::feats`; the device profile and its staleness test), `Console/Core/Confirm.{h,cpp}` (`CostGate`, the per-mode policy,
  the prompt, the settings `confirm` / `confirm_wall_s`), `Console/Bindings/HostProbe.cpp` (isatty, MemAvailable, statvfs `/mnt/c`,
  `sched_getaffinity`, the ELF build id), `Console/Bindings/Calibrate.cpp` (`--calibrate`).
- **Arms**: (A) the C++ estimate = the frozen Python reference `Console/cost/expected_estimates.tsv` (`nbconfirm_expected.py`) on the 213
  checked S2 cells (hw 32, no profile) and 72 rows with the fixture profile `Console/cost/test_device_profile.tsv` (threads 1/4/6/16,
  hw 6/32), every float to 1e-9 relative (measured: bit-identical, `max_rel=0.00e+00`), flags and strings exactly; (B) `Decide` = the
  reference on every (A) cell under 5 environments (1065 rows); (C) the embedded model text = the tracked TSV, every capped verb's groups,
  class rows, safety rows, 20 calib rows, `fitted_on`; (D) the two settings (defaults `ask` / 60, refusals, engine family, the
  mathematical snapshot unmoved); (E) **prompt-less byte identity**: the 41 frozen pre-S3 refusals `Console/cost/refusals_pre_s3.tsv`
  (captured once from the a4a38bc4 binary) reproduced byte for byte under `-c`, `confirm=no`, a hostile host (terminal, 1 MiB
  MemAvailable, C: 5 GB, the fixture profile), the script on stdin, and a piped REPL; (F) `confirm=yes` runs four just-over cells (a `#~`
  note), the hard memory / C: refusals still refuse, the descent refusal names threads = 1; (G) the terminal policy in process (silent
  rule 4, normal accept / decline with nothing bound, strong needs a typed `yes`, `confirm = no`, hard refusals never ask, a stale profile is
  named); (H) the real binary's `--console` under a pseudo-terminal (decline → `not run`, accept → runs); (I) `hecke_structure(1, 0)`
  and `hida_tower(100, 23, 1)` are TypeErrors (they leaked `ENGINE_CHECK`s); (J) the profile path, `none`, the staleness rule, the build id.
- **Gate line** (S3): `CONSOLE_COST_MODEL estimates=213+72 decisions=1065 max_rel=… ab_fails=0 refusals_pre_s3=41x5 pty=OK calib_set=calib/v2 verdict=OK` (since Fix round 1 with `beyond= no_model= unusable=`, below).
- **Pinned env**: the validation sets `HACS_DEVICE_PROFILE=none` (or the fixture) for its whole run, so no user profile can change a
  verdict (S2 audit F5). Not an env hook: it reads nothing from the caller's environment.
- **Not a validation (by design)**: the model-drift gate, `hacs --calibrate=thorough` on the reference box, read
  `COST_MODEL_DRIFT … verdict=OK|DRIFT` (S2 FR.6): a close-window step, because timings are not machine-independent.
- **S3 Fix round 1 (S3 audit M1, m1–m5)**: (A)/(B) gain the X rows (`descent(10^6, 0)` at T = 32 and 16, `hida_tower(200, 5, 3)` at
  T = 32, with their D rows: 3 + 15), the N rows (no model, 5 envs: refused whenever a memory limit or C: ≤ 10 GB is known, else
  strong) and the S rows (the last X estimate with wall / rss / wall_hi / rss_hi set to nan, ±inf, −1, 0, 5 envs: always refused;
  100); (F) `descent(1000000, 0)` under `confirm=yes` at threads 32 and 16 is hard-refused, `level_n` / `nebentypus(2147483648, …)` are
  TypeErrors by name under `confirm=yes` and keep the pre-S3 text prompt-less; (J) `--calibrate --profile <in-tree path>` is REFUSED
  (exit 1). Gate line now `CONSOLE_COST_MODEL estimates=213+72 decisions=1065 max_rel=… ab_fails=0 refusals_pre_s3=41x5 pty=OK
  beyond=3+15 no_model=5 unusable=100 calib_set=calib/v2 verdict=OK` (4483 checks).
- **`HACS_HOST_PROBE_FIXTURE=1`** (read-only test interlock, S3 Fix round 1, audit m2): set **only** in (H)'s pty child, it pins the
  host probe's MemAvailable to 4096 MiB and C: free to 255 GB, so (H) does not depend on this host's memory or free space on C:
  (it failed at C: ≤ 20 GB before). It changes no value, record or hash input; on a host with more than 4 GiB available it only
  lowers the rule-1 limit. Never set it to make a run pass.

### Slot 25 NBCONFIRM S4 (the served console, the gateway, the page; [P] 3.15.0-pre.3 §18.19; `docs/console/NBCONFIRM_S4_report.md`)

No validation added (roster unchanged, **284 = 75 / 161 / 48**); two existing gates extended.
- **`ConsoleServeValidation`** (`standard`; `[SKIP] …: OC_BUILD_NOTEBOOK=OFF` in a default build) — (A) also pins
  `hello.limits.confirm_wall_s = 60` (and `settable` gains `confirm_wall_s`, through `ServeSettableKeys()`); new arm **(L)**,
  its child with `HACS_DEVICE_PROFILE=none` and **`HACS_HOST_PROBE_FIXTURE=1`** (MemAvailable 4096 MiB, C: 255 GB; the read-only
  interlock of S3, now set in (L)'s served children too): inside the envelope `descent(1, 10)` runs as before (no frame added);
  `descent(1, 62)` under `confirm_wall_s = 0` is `confirm_required` (exit 3, token `0x<16 hex>`, level normal, site, estimate),
  the statements before it ran and their bindings persist, the call bound nothing; the same cell offers the same token; a
  forged token, an edited cell, another argument value at the same site, a changed setting and another session are not
  confirmed (a new token each time); with its token the cell runs and sends `progress` frames carrying `confirmed.wall_hi`;
  a token serves no unserved verb, `set confirm` is `forbidden_overload`; malformed `confirm` lists (5 shapes, 17 tokens) are
  `rejected` / `protocol`; `level_n(30, 100, 7)` is a strong confirmation (never run); `descent(1000000, 0)` is a hard refusal
  without a token; `hida_tower(240, 5, 1)` (≈ 13 s at 32 threads, < 0.7 GiB) shows one start frame and the 10 s heartbeat;
  `--serve --set confirm_wall_s=0 --rss-cap-mib 300` refuses `descent(1, 62)` before the run (R_cap of rule 1). Line
  `EFFECTIVE ConsoleServeValidation arm=L tokens=ok heartbeats=<k> rss_hi=<MiB>`. Adds ≈ 15 s; peak child RSS ≈ 0.85 GiB.
  The served script set (B)/(C) is unchanged: `054_s24_descent.oc`'s `expect_error { descent(1, 400) }` stays the pre-S3
  refusal because a cost gate never asks inside `expect_error` (S4; before that rule the served threads=1 / 2 arms saw
  `confirm_required` there).
- **`test_gateway.py`** (`GATEWAY_TEST … verdict=OK`; 25 → 27 tests) — class `Confirm`: the wall formula
  max(`--cell-wall-s`, 3 · wall_hi + 60) ≤ `--cell-wall-max-s` (0 = no raise; NaN / Bool = no raise; `--cell-wall-s 0` stays
  off); a live round trip under `--cell-wall-s 5 --cell-wall-max-s 30`: `hello.limits.confirm_wall_s`, a forged token with extra
  page fields (`wall_hi`, `rss_cap_mib`) raises nothing, six malformed `confirm` shapes rejected by the gateway, the confirmed
  cell raises the wall to 30 (one `gw cell_wall` event), the lazy work in a later cell raises it from the child's `progress`
  frame, an ordinary cell raises nothing, after `restart` the old token is stale.
- **S4 fix round 1** ([P] 3.15.0-pre.4; audit `docs/console/NBCONFIRM_S4_audit.md`). `ConsoleServeValidation` (G) +1 check
  (661): `HACS_HOST_PROBE_FIXTURE=1` under a non-validation parent (`/bin/sh -c '"$0" --serve; exit $?'`) is refused at the
  environment gate (exit 1, the refusal on stderr); (L) still runs the fixture as a direct child of the binary (L2).
  `test_gateway.py` 27 → 29: `Confirm.test_stale_token_does_not_raise_wall` (M1: a token offered for `descent(1, 62)`
  presented with the unconfirmed `hida_tower(200, 5, 1)` cell under `--cell-wall-s 3 --cell-wall-max-s 100` raises nothing,
  no `progress.confirmed`, the session is killed at 3 s — fails on the pre-fix gateway) and
  `Confirm.test_non_idempotent_cell_stops_after_one_retry` (M2: `k = k + 2; r = descent(1, 60 + k)` asks again at the same
  site with a new token after its confirmation, `k = 4` afterwards; the page rule `OCRender.confirmStep` (render.js) answers
  ask → stop (with the "idempotent" explanation), and still asks at a different site; the node part skips without node).
- **Process rule (S4 audit L3, the S3 lesson).** `ConsoleServeValidation`, `ConsoleServeAtlasValidation` and
  `ConsoleReadOnlyTagValidation` `[SKIP]` in a default (notebook-OFF) build, so **a package that touches `Console/` (or
  `notebook/`) must also build its merge candidate with `-DOC_BUILD_NOTEBOOK=ON` and run those three plus the gateway
  self-test (`GATEWAY_TEST … verdict=OK`)** before its audit; S3 merged with `ConsoleReadOnlyTagValidation` failing (6
  unlisted source hits) because only the notebook-OFF build was run.

### Slot 25 NBCONFIRM S5 (the cooperative cancel: REPL Ctrl-C, the served interrupt inside a verb; [P] 3.15.0-pre.5 §7, §18.6; `docs/console/NBCONFIRM_S5_report.md`)

- **New name `ConsoleCancelValidation`** — **`standard`** (≈ 29 s on an idle box, ≤ 0.7 GiB child RSS), roster 284 → **285 = 75 / 162 /
  48**, `--all` runs **237**. Registered in `Registry/Slot25.cpp` (sources `cmake/sources/*.cmake`). Code:
  `Console/Core/Cancel.{h,cpp}` (ConsoleCore: the request flag, `CancelScope` / `NoCancelScope`, `PollCancel`, `console::Interrupted`, the
  test interlock), `Util/CancelPoint.h` (the pipeline's neutral hook), the points in the evaluator, `Confirm.cpp`, the descent record,
  `RunDescentHecke`, the HeckeZ record, `ComputeTowerCell` / `RunCellOn`, `ComputeFormsWeight` and the `level_n` / `nebentypus` /
  `forms_algebra` bindings (the list: the S5 report §2). No shard-weights row (generated table): the 5 s default until the next
  `shard_weights.py` measurement.
- **Arms**: (A) in process, per verb — `descent(11, 2)` (the lazy read), `hecke_structure(5, 10, "anemic")`, `level_n(37, 10, 101)`,
  `nebentypus(13, 4, 10, 37)`, `hida_tower(40, 5, 2)`, `hida_lambda(11, 100, 3)`, `forms_algebra(200, 7)`: the statement's points are
  traced, then the statement is cancelled at **every** traced point in turn (`after:K`), each in a fresh in-process REPL session: the
  `interrupted (at <site>)` line names that point, `x` is unbound after a stop in its making (a lazy handle
  stopped in its read is kept and re-read), the re-run's last line equals a **cold child process** (`-c`, nothing cancelled), and after
  all the cancels a fresh uncancelled session equals the cold child too (the cache-poisoning check; 111 cancels, 23 distinct inner
  sites); (B) the binary's `--console` on a pseudo-terminal with `HACS_CANCEL_TEST=wait:1:descent.charpoly`: Ctrl-C prints
  `interrupted`, the prompt returns, the re-read prints the cold digest, Ctrl-C at the idle prompt ends the process by SIGINT; with
  `hold:1:…` a second Ctrl-C 0.3 s after the first (before it took effect) ends it by SIGINT; (C) (notebook-ON only, else `[SKIP]` of
  the arm) `--serve` with the same interlock: an `interrupt` while `print(r.digest)` waits at the point gives
  `done{status:"interrupted"}`, the next cell's read prints the cold digest; (D) `-c` with `HACS_CANCEL_TEST=after:1` is unaffected.
- **Gate line**: `CONSOLE_CANCEL verbs=7 cancels=111 verbs_with_inner_points=7 pty=OK serve=OK verdict=OK` (`serve=skipped` in a
  notebook-OFF build).
- **`HACS_CANCEL_TEST=after:K|wait:K|hold:K[:PREFIX]`** (read-only test interlock): read by the interactive REPL and by `--serve` (there
  only as the direct child of this same binary, the `HACS_HOST_PROBE_FIXTURE` rule; refused at the environment gate otherwise). It
  can only stop a statement at a cancellation point (or hold it there); it changes no value, record or hash input. Never set it in
  a production session.
- **`test_gateway.py`** (`GATEWAY_TEST … verdict=OK`; 29 → 30 tests) — `Live.test_interrupt_inside_verb`: an Interrupt 1 s into the
  single statement `x = hida_tower(160, 5, 1)` (≈ 5 s) through the gateway ends it `interrupted` (before S5 it finished `ok`), `x` is
  unbound, the session answers the next cell.

### Slot 25 HZ-GOLD (the add-only golden event, k = 112; `slot25/golden_ledger.md`, `docs/matrix-engine/rebaseline-s25-hzgold-addonly-gevt23-heckez.md`)

**No validation is added, removed or re-tiered; the roster stays 285.** The golden reference grows from 18 273 to **18 385** entries
(tier A 12 042 → **12 154**, tier B 6231). The additions are the 97 G-EVT23 points (TAMEFAM / PRANK / TOWER / SHAPIRO / LESLEVEL, ported by
GOLD-PORT) and 15 `HZ N=1 n=<n> alg=full` points (`HZ_N1_n<n>_full` = the default `integral_hecke_structure/v1` record's
`record_fnv1a64`).

- `GoldenRegressionValidation`: `tier A checked 12154, failing 0; tier B checked 6231, mismatching 0`.
- Each golden pass grows by ≈ +11.5 s (HZ 7.2–7.6 s and the families ≈ 4.1 s; HZ 11.1 s at `ENGINE_THREADS=1`). Its users are:
  - `GoldenRegressionValidation`;
  - `HeckeLocalityValidation` arm 5;
  - `ConsoleDeterminismValidation` arm (c);
  - `HeckeLocalitySlowValidation` (slow tier).

  So `--all` makes 3 passes and `--all-full` makes 4.
- **`ConsoleDeterminismValidation` soft threshold: 70 s** (owner ruling 2026-11-07, I5). It replaces the 45 s threshold quoted in the
  per-slot records above and the slot-23 audit's 55 s recommendation, which was never ruled. Measured with both gates true:
  - 47–50 s by name at load ≈ 5 (gates false: 37–39 s);
  - 67.8 s inside a 4-shard `--all` at load up to 12.5.

  The threshold is a documentation figure: no code asserts it.
- The scratch interlock `GOLDEN_GEVT23` is retired (env-hook rows below).
- A change to the HeckeZ record schema, or to its settings or caps text, makes the HZ fingerprint `ENGINE_CHECK` throw in every golden pass.
  That is an owner-gated 15-line changed re-baseline (rebaseline note §4).

### Slot 26 Z1 (UP-Z (a): U_p, p | N, over Z_(ℓ), ℓ ≥ 5; `slot26/Z1_report.md`, design `slot26/UPZ_design.md` route (i))

**One validation is added (standard); the roster grows 285 → 286** (`--all` 237 → 238).

- **`HeckeZUpValidation`** (standard, ≈ 15 s at 8 threads, peak RSS ≈ 0.27 GiB; Z1 and, since slot-26 Z2, ℓ ∈ {2, 3}). Gate line
  `HECKEZ_UP cells=6 mismatched=0 umodl=24/24 wordprime=6/6 t4_chiU2=ok newform_ap2=5/5 threads=1,4,16:equal isa=scalar,avx2,avx512:equal tamper=caught
  recompute=18/18 full_scan=5/5 iso=19/19 isoroute=5:equal dropcoset=caught checks=213 … verdict=OK`. It first prints the twelve-lever `EFFECTIVE HeckeZ descent …` line. Arms:
  - (R1) the default export refuses p ∣ N (`PDividesN`) on both routes; with `ExportOptions::allow_bad_primes` the tree route (ℓ = 3) serves it (Z2);
  - (a) at (11, 0), (2, 6), (8, 10), (3, 4), (5, 4), (23, 0), ℓ = 2, 3, 5, 7, every p ∣ N: the characteristic polynomial of the export's U_p
    (ℓ ≥ 5: Heilbronn on M_N / Rel_N; ℓ ∈ {2, 3}: the free-model U_p of `prop:strictliftN` (9) transported to the tree; the free block over Z/ℓ^{K_max}) equals HZ-UTAG's
    χ_Q(U_p) (word primes, level_n) mod ℓ^{K_max}, the independent oracle at ℓ ∈ {2, 3}; (2, 6) at ℓ ≥ 5 is the T4 check (`t4_chiU2`, a subset of `umodl`); (a′) at one word prime q per (N, p) the characteristic polynomial of
    `RunAtPrime`'s U_p (the residues `RationalStepFull` reads) = χ_Q(U_p) mod q (`wordprime=6/6`);
  - (c) at N = p ∈ {11, 23, 5} (every cusp form p-new): (U_p² − p^{k−2})(U_p − 1)(U_p − p^{k−1}) = 0 on L ⊗ Z/ℓ^K, and χ_Q(U_p) splits
    with every root in {1, p^{k−1}} or of square p^{k−2} (2 dim S_k of them). Measured roots: (5, 4) → 1, 25², 3125;
  - (d) the export's U_p at threads 1 / 4 / 16 and under every available rho-fill path, entrywise; HZ-UTAG's word-prime routes
    (count-once / dense-per-prime vs the term table) entrywise; the (2, 6, full) record at 1 / 4 / 16 threads hash-equal;
  - (e) a perturbed U_p entry and a perturbed χ_Q(U_p) coefficient are both caught by (a); (e′) (Z2) a dropped coset of the free-model U_p at (11, 0), (23, 0), (2, 6), ℓ ∈ {2, 3}, is refused by the read or caught by χ (`dropcoset=caught`);
  - (g) the free-model U_p over Z (`IsoHeckeN` with `allow_bad_primes`, `prop:strictliftN` (9)) in EXPORT-Z's basis B against the route's own U_p in the same B
    (`ExportInBasis`) mod ℓ^{K_max}, entrywise, at (11, 0), (23, 0), (2, 6), (8, 10), (5, 4), ℓ ∈ {2, 3, 5, 7} (`iso=19/19`; at ℓ ≥ 5 Heilbronn, ℓ ∤ N; at ℓ ∈ {2, 3} the transport); IsoHeckeN refuses p ∣ N by default; the whole object [[τ, M], [0, F]] of U_2 at (2, 6) is served at the tree route (Z2) and refused without the option; a perturbed F entry is caught;
  - (h) (Z2) `IsoHeckeN`'s routes at p ∣ N (`materialised`, `streamed`, `count_dense` at n = 0) entrywise on the tree export at threads 1 / 4 / 16 and on the operator's dense matrix, with equal term counts, at (11, 0), (23, 0), (2, 6), (8, 10), (6, 0) (`isoroute=5:equal`), each cell failing unless the compared export matrix is non-empty;
  - (N2) every `blocked(` / `refused(` / `open(` word of every closed enumeration (`EnumVocabNames()`) has a `StatusTable()` class
    (44 words, `VOCAB … unclassed=0`);
  - (f) the 15 golden level-1 records (n = 2 … 30) and the anemic (2, 6), (8, 10), (11, 0) rebuilt: `record_fnv1a64` equal to HZ-DS ed. 1
    (`hecke_ed1/rows.tsv`); five full level-N records scan clean and carry `G1.theta_ops` and `G10.contract = gl2_contract 1.26.0-pre.9, item 8 (d′)`; (Z2) no `blocked(U_p)` outside `G1.components` / `maximal_ideals`, the G3 words of [C] 1.26.0-pre.9 the W-1 rule (a tag step that did not run keeps `blocked(U_p)`, three combinations of `FullG3Rule`), `open(sandwich)` at ℓ ∈ {2, 3} on the non-reduced branch and (8, 10, full) `final`; fingerprint
    `0x8ffc29730c4f9672`.
- `HeckeZRecordValidation`: the pins `2,6,full` and `8,10,full` of `HeckeZRecordExpected.inc` move (two pending records recomputed with U_p;
  `slot26/golden_ledger.md`, "non-golden lines moved"); `HECKEZ_RECORD … hashes_pinned=7/7 … verdict=OK`.
- The 141-record recompute (the Z1 merge gate, audit C3) is not a validation: `docs/integral_census/hz_up_recompute.py --binary <bin>
  --scratch <dir>` prints `HZUP_RECOMPUTE records=141 changed=0 failed=0 … verdict=OK` (≈ 7 h at 4 threads).
- The campaign's `hecke_structure` arm prints `EFFECTIVE HeckeZ descent HECKE_DESCENT_TREE=route=<v>,source=<default|env|env-invalid> …`
  (twelve tokens) once per process (stdout only; no record byte depends on it). `route=` is the **composed** effective route: each lever's
  own reading (exactly `0` / `1`; unset or empty = default, except `GOOD_DENSE`, whose empty value is `env-invalid` as in its module), then
  `TREE=0` ⇒ `TREE_PAIR=route=dense,source=…+composed(TREE=0)` and `GOOD_SPARSE=0` ⇒ `GOOD_DENSE=route=shipped,…+composed(GOOD_SPARSE=0)`.

### Slot 27 TS-FIX / TS (the θ search; `slot27/TS_design.md` v0.2, audit `slot27/TS_design_audit.md`)

**One validation is added (standard); the roster grows 290 → 291** (`--all` 242 → 243). Registered in `Registry/Slot27/HeckeZThetaSearch.cpp`
(sources `cmake/slot27/HeckeZThetaSearch.cmake`).

- **`HeckeZThetaSearchValidation`** (standard, ≈ 9 s at 4 threads, peak RSS ≈ 0.11 GiB). Gate line `HECKEZ_THETA_SEARCH text=OK orders=OK
  last_round=OK gp=OK pure=OK site2=OK route=OK default_fp=0x8ffc29730c4f9672 checks=107 failing=0 … verdict=OK` (`default_fp` is the
  build's default settings fingerprint: the flip commit changes it). Arms (TS-FIX: (c′); TS: the rest):
  - (a) the text rule (design §6.1): at **explicit** `theta_order = lex` HZ-RAT's `canonical_text()` is the edition-1–3 literal and the
    caps text under `coefficient_ring = Z` the edition-3 member's settings string, byte for byte (fingerprint `0x8ffc29730c4f9672`); at
    `lex_then_greedy` exactly the two insertions (`;theta_order=lex_then_greedy(t=2654435761;steps_without_U_p:|P|>=p_rule_cap)` after
    `theta_coeff_max`, the continuation clause of `heckez.maximal_ideals`), fingerprint `0x325b510edad11c8d`; the default text's fingerprint
    = `default_fp`; `p_rule_cap`'s copy, `threads` and the TS-FIX hook unprinted; the campaign spec: absent key → the default's id, `hz_theta_order
    = lex` → `hz_N1_n10_full_s8ffc29730c4f9672`, `lex_then_greedy` → its own id; the key refused outside `structure = hecke` and for an unknown value;
  - (b) / (c) the full steps (C1) of (9, 0), (18, 0), (25, 0), (49, 0) (certified in `lex`: the same θ under both orders) and (25, 2), (45, 0)
    (`lex`: `open(cap)` after 64 candidates; `lex_then_greedy`: θ = T_2 + 2U_5 resp. T_2 + U_3 + 2U_5); the `lex_then_greedy` candidate list
    begins with `lex`'s unchanged, no vector listed twice; the last-round rule: (341, 0) `anemic` through `P_rule` keeps P = {2, 3, 5, 7},
    θ = T_7, (147, 0) `anemic` certifies at P = {2, 5, 11, 13, 17, 19} with θ = T_2 + 2T_5, a direct `RationalStep(147, 0, {2, 5, 11})` is
    `lex` alone (`open(cap)`);
  - (d) the continuations as pure functions: 55 random separating eigenvalue tables (fixed seed) — `GreedyContinuation` returns a primitive θ
    with every c_i ≤ binom(d, 2), equal to an independent least-argmax construction with exact targets, in ≤ m(B + 1) tests, never re-testing a
    vector of `tested`; negative control (duplicated operator, two systems never separated): none within m(B + 1); the caveat table (t an
    excluded value): none, documented; on the record cells of (b) / (c): candidates ≤ `theta_cap` + m(B + 1), every c_i ≤ binom(d, 2);
  - (e) site 2: `KrylovContinuation` on synthetic ranks (no gain: one target probe per operator; a rising score runs into the cap: exactly
    `theta_cap` = 64 tests; the scan bound min(B₂, ℓ − 1) at ℓ = 3); records (2, 6) `full` at ℓ = 3 and (77, 0) `anemic` at ℓ = 7:
    `maximal_ideals` `not_run` under `lex`, `certified` under `lex_then_greedy`; (5, 8) `full` keeps `decomposed_by` at ℓ = 107; every word the
    continuation moves is a word of an ideal `lex` left `not_run` (rule R2), and the three `lex` records equal edition 3's `record_fnv1a64`;
  - (f) route identity: the (25, 2) full step and the (2, 6) `full` record under `lex_then_greedy` at threads 1 vs 16 (equal `R.thetas`,
    digest, record hashes; the search itself is sequential, no batch knob);
  - (c′) (TS-FIX, design §5.4 / §9 (c′)) the predicate `heckez::GPIsBound` on its five words (`upper_bound_certified`, `partial(unfactored)` a
    bound; `open(no primitive T_p)`, `open(C1)`, `general_case` not); `RationalStep(1, 10, {2, 3, 5})` under the validation-only hook
    `RationalSettings::validation_skip_units` (unprinted: HZ-RAT's text unchanged) certifies θ = T_3 + T_5 with g_P `open(no primitive T_p)`, no
    factors; the record (1, 10) `full` under the hook is `final`, `G3.partition = eisenstein`, `G3.C_T.status = not_run`,
    `G3.fibre_product = not_certified`, no `G3.C_T.upper` / `exact` / `cofactor*` / `C_T.ell=` / `eta_L` / `second_route` / `G9.K3` word,
    no `eis_single` route (the G2 words at 691 are printed, read from the run); the control without the hook is the golden record
    `0x5e84b4c2540ff22a` at fingerprint `0x8ffc29730c4f9672`.

### Slot 27 BIGNTT M1 (the NTT big-integer finder, first half; `slot27/BIGNTT_design.md` v0.2, audit `slot27/BIGNTT_design_audit.md`)

**One validation is added (standard); the roster grows by +1 over the merge base** (on `93b9d9b4`, after TS and EXW: 292 → 293, `--all` 244 → 245; read the
count on the tip merged onto). Registered in `Registry/Slot27/BigIntNtt.cpp` (sources `cmake/slot27/BigIntNtt.cmake`, which also adds
`NumberField/BigNtt.cpp` to the STL-only NumberField target).

- **`BigIntNttValidation`** (standard, ≈ 10–20 s). Every arm runs on the **forced** NTT route (threshold passed as a parameter, audit M2);
  `EFFECTIVE BigIntNttValidation ntt_products=<n> barrett_steps=<m> min_limbs_default=<k>` (the gate requires both counts > 0), then
  `BIGNTT_VALIDATION arms=4 checks=<k> products=<n> mismatched=0 routes_equal=yes secs=<s> verdict=OK`. Arms:
  - **P**: `nf::bigntt::mul_ntt` = `BigInt::mul_schoolbook` (≤ 2 048 limbs) / `mul_mag` (Karatsuba, above) on random balanced and unbalanced
    operands of 8 … 32 768 limbs, around every transform-length class f·2^a (nc = L − 3, L − 1, L + 1 chunks, f ∈ {1, 3, 5}); adversarial
    all-0xffffffff operands (the coefficient bound attained) up to 16 384 limbs, `sqr_ntt`, 2^k ± 1, a single non-zero chunk, a zero operand.
  - **T**: products, squares, Barrett steps and powmods equal at threads 1 / 4 / 16; since M1b (code audit m4) every threaded check runs where
    `effective_threads` grants > 1 thread (checked; printed `arm T … effective=<e>`): products at 5 000 / 22 000 / 40 000 limbs (L = 5·2¹²,
    3·2¹⁵, 5·2¹⁵), Barrett / powmod at k = 5 000 / 6 000 (L = 5·2¹², 3·2¹³); a barrier pass (four ranges that each wait for all four) proves the
    pool runs ranges concurrently, ≥ 3 of them on pool workers (`pool_worker_ranges=` printed); products inside `nf::parallel_ranges` tasks
    (the nested spawn fallback of the slot-27 persistent pool) equal; an exception thrown in a pool task reaches the caller and the pool stays usable.
  - **B**: `BarrettModulus::mulmod` / `sqrmod` = `(x y) % m` on 31 moduli (2 … 2 048 random limbs; 2^k ± 1, 2^k + 12 345, 2^k − 999 for
    k ∈ {64, 255, 256, 4 096, 65 536}; since M1b b^{k−1} for k ∈ {2, 3, 1 100}, code audit m1) with edge operands 0, 1, m − 1, m − 2; powmods with
    ≤ 64-bit exponents = the pre-slot-27 `PowModBig`; since M1b (code audit m2) `powmod(−3, 5)` = (−243) mod m on both routes and a negative
    `mulmod` operand refused (`NF_CHECK`) on both routes.
  - **MR**: the finder's own Miller–Rabin (`finder::MillerRabinBigForTest`): Mersenne primes 2^p − 1, p ∈ {521, 607, 1 279, 2 203, 2 281} at
    12 bases (and p ≤ 1 279 on the old route), p = 4 423 at 2 bases; composites M521·M607, 2^523 − 1, M4423·M2281 (6.7 kbit, one base); the
    isqrt branch of `BigProbablePrime` on M1279² (root and e = 2); ψ₁₂ = 318 665 857 834 031 151 167 461 = 399 165 290 221 · 798 330 580 441
    `probable` at 12 bases on both routes and caught by base 41.
- **Regression coverage** of the pool (`nf::parallel_ranges`) and of the batched radix-f sub-transforms of `Ntt64Plan` (same ranges, same
  per-block arithmetic, byte-equal by construction): `NumberFieldValidation`, `CwLayerValidation`, `RibetFieldValidation`, `PRankValidation`
  in `--all`.

### Slot 27 EISUPb (HZ-EISUP (b): the Eisenstein U_p systems with characters ψ ≠ 1; design `slot26/HZEISUPb_design.md` v0.4, [C] 1.28.0-pre.1 `prop:heckeZeisupchar`)

**One validation is added (standard); the roster grows by +1 over the merge base** (on `2e3374a5`, after TS, EXW, BIGNTT: 293 → 294, `--all`
245 → 246; read the count on the tip merged onto). Registered in `Registry/Slot27/HeckeZEisUpChar.cpp` (sources
`cmake/slot27/HeckeZEisUpChar.cmake`: `Integral/HeckeZEisUpChar.cpp`, the validation, the fragment). Record-path change (the (b) branch, taken on
`full` N > 1 records with (C1) `certified` and e^an_k(N) ≠ 1 only), schema amendment A5 (`psi_cond`, `psi_order`, `theta_poly`,
`U_<p>.charpoly`; the free-text names `theta_poly`, `charpoly`), and `G10.contract` = `gl2_contract 1.28.0-pre.1, item 8 (d')` on every `full`
record at N > 1 the binary writes (per binary, design §5.5; G10 is in neither hash).

- **`HeckeZEisUpCharValidation`** (standard, ≈ 12 s by name at `ENGINE_THREADS=8`, peak RSS ≈ 83 MiB; prediction ≤ 60 s, ≤ 0.4 GiB). Gate line
  `HECKEZ_EISUPB cells=4 step_cells=4/4[…] records=4/4 components=19 deg_ge2=3 meetings=5 second_route=4/4 utag_div=26/26 disc_match=16/16
  vdisc_record=4/4 threads=1,4,16:equal reuse=equal isa=…:equal embed=equal direction=ok s_read=ok s_forced=ok s_appended=ok qstar_cap=ok
  tamper=10/10 schema_tamper=4/4 ed3_rescan=226/226 a_regress=4/4 a_step=equal contract=8/8 nonreduced_unchanged=7/7 checks=138 failing=0 … verdict=OK`,
  preceded by `EFFECTIVE HeckeZEisUpCharValidation step_cells=4` (gated: a pinned step cell whose (C1) is not reached FAILS; audit M1). Arms:
  - (a) the step `EisUpCharStep` (C-B0 … C-B8) on the four in-scope record cells (9, 0), (18, 0), (25, 0), (49, 0), digests of
    `EisUpCharResult::text()` pinned; (a′) step level at a non-default θ (the full step under TS's `lex_then_greedy`, never a record): (9, 2),
    (49, 2), (121, 0) (degree-4 orbits, o_N = 10), (225, 0) (s_N = 15, (Z/15)^× not cyclic), digests pinned, components = the closed form;
  - (b) second route (only `cusps_minus = e_k`, by `Gamma0Cusps`, is independent of the step: `ClosedForm()` and the step's rows both come
    from `Components()`; the independent routes are (c) and (d); audit m6): the multiset of components (degree, `psi_cond`, `psi_order`, type) = the closed form of design §2.3, Σ deg = e_k = c(N) − [k = 2];
  - (c) v_ℓ(disc f_θ) (exact Sylvester resultant) = the design-time prediction (design §3, 16 primes) = the record's `G1.S_cand.ell=*.v_disc`;
  - (d) every g_{U_p,j} divides HZ-UTAG's χ_Q(U_p) exactly over Z (26 divisions);
  - (e) the four records through the record path: rows equal the step's, scan clean, no `blocked(U_p)` in `G1.components` / `maximal_ideals`,
    `G10.contract`, `record_fnv1a64` pinned; the Eisenstein–Eisenstein congruences of design §2.4 observed on θ (at every ℓ | o_N two factors
    e_{θ,j} share a residue factor; on these records ℓ ∈ {2, 3} are not decomposed by the shipped binary, so `components_through` cannot show them);
  - (f) bit identity: `text()` at threads 1 / 4 / 16, reuse vs forced recompute, every rho-fill path, two embeddings at q* (the least and the next
    primitive root; invariance only); the (25, 0) record's hashes at threads 1 / 4 / 16; the direction unit check at o_N = 10 (ψ(2) = ζ read at
    σ_3𝔮 as ζ³, referee M1);
  - (f′) 𝔖 and the q* chooser: `ExtraPrimesS(225, {2, 17}) = {7}`, generating lists give ∅; the arithmetic conditions on q*; a capped list →
    `refused(word_prime_cap)`; the (6′) read forced (𝔖 = {13} appended at (25, 0) by the validation-only `validation_extra_S`: T_13 read on
    K_q* at an extra run, labels unchanged; `s_appended`); 𝔖 produced by `ExtraPrimesS` on a real (C1), end to end (`s_forced`, a failure if not
    reached): (18, 0) on T_7, T_13 (both ≡ 1 mod 3), U_2, U_3 under `lex_then_greedy`: 𝔖 = {5}, T_5 read at q* on an extra run, labels equal the
    default list's. (The design's (225, 0) on T_2, T_17, U_3, U_5 can never reach (C1): with the T_p in ker χ_3χ_5 and no p ∥ N, (1, (0,0)) and
    (χ_3χ_5, (0,0)) agree on every operator.) The q* chooser's own cap refusal (`qstar_cap`, audit m5): at the cap the untampered (25, 0) step
    passes with, the validation-only `qstar_none` hook admits no candidate → `refused(word_prime_cap)` from the chooser.
  - (g) tampers, each caught: a factor + 1 (C-B4), the order-4 / quadratic labels swapped (C-B6), ψ → ψ² (C-B4), the norm from Q(ζ_{o_N})
    (C-B4), y_3 = α on the order-4 orbit (5, (0)) at (225, 0) (a valid wrong type: v_3 = 2, 3 ∤ cond ψ; C-B4), e_k + 1 (cap refusal), a forged
    g_{U_5,j} on the degree-2 row (C-B5 re-check), f_0(θ′) + 1 before the attribution at ℓ = 13 of (25, 0) (C-B7); and (audit M2) the two that
    leave C-B4 intact: the proposal g_{U_5,0} + 1 **before** the CRT comparison (C-B5's g = gprop) and the order-4 orbit's closed form misaligned
    on T_2, whose θ-coefficient at (25, 0) is 0 (ψ³ on T_2, ψ elsewhere: the orbit marginals unchanged, so C-B5 passes; C-B6's operator-by-
    operator comparison of the read character with the closed form catches it). C-B8 as coded is a decomposition-consistency check mod q
    (audit m2; the design's exact trace identity is implied by C-B5);
  - (h) `G10.contract` = 1.28.0-pre.1 on every full N > 1 record the arm writes ((b) words or not, 8/8);
  - (i) amendment A5: forged U_5 zbig on the degree-2 row, Σ degree ≠ e_k, φ(`psi_order`) ≠ degree, `psi_cond` ∤ s_N caught; edition 3's 226
    records re-scanned `values_outside_lists=0`;
  - (j) (a)-regression: (11, 0), (22, 0), (2, 4), (5, 4) `full` = (a)'s pinned `record_fnv1a64`, no (b) key; the (b) step forced on (22, 0)
    (`force_scope`, s_N = 1) reproduces (a)'s rows, e_θ, c_θ (design §2.10);
  - (k) the seven `refused(non_reduced)` records of edition 3 (16, 27, 32, 64, 125) = edition 3's `record_fnv1a64`.
- **Merge gate** (not a validation): the neutrality re-run of edition 3's 85 `full` N > 1 records on the branch binary at the default `lex`
  (`slot27/HZEISUPb_predictions.md`), gate line `EISUPB_NEUTRAL … moved_outside_rule=0`.

## Suite wall-time composition

The suite grew from 50 to 66 validations while the pipeline got ~7× faster again, so the wall time
went up. Two entries are half of it: **`BlockEliminationValidation` 43.7 s** and
**`DenseElimValidation` 26.6 s** — both entrywise comparisons of a whole elimination against two
independent references, which is exactly what they are for. The Phase 4–6 additions are cheap by
comparison (the eleven `Engine*` / `Cuda*` / `Campaign*` entries total ≈ 49 s, of which
`EngineCrossDeviceValidation` is 13 s and `EngineDeviceTrapValidation` — `slow`, so not in `--all`
— is 9 s).

**Slot 9 (2026-09-25).** `--all` gains ≈ 23 s of new `standard` / `fast` names
(`HeckeExtAlgebraInvariantsValidation` ≈ 5–6.5 s, `HeckeFamilyConcurrentBuildValidation` ≈ 3.7 s,
`HeckeFreeModelValidation` ≈ 3–4 s, `HeckeIsotropyModelValidation` ≈ 2 s, the rest ≲ 1.2 s each) plus
the growth of `ConsoleScriptValidation` (≈ +5.6 s, twelve new scripts), `ConsoleDeterminismValidation`
(≈ +7 s) and `HeckeExtDeterminismValidation` (≈ +3 s, the device arms), less WP-4t's ≈ 4.7 s moved out
of `HeckeReductionValidation` to the `slow` sibling (which grew ≈ 4 → 17–18 s). All figures indicative
(shared box); the close's measured walls: golden 15.1 s, EngineDet 4.7 s, ExtDet 13.6 s, ConsoleDet 29.2 s, smoke 0.1 s, `--all` 351 s, `--all-full` 544 s (W1, 2026-09-25).

**Slot 10 (2026-09-25).** `--all` gains ≈ 20 s of new `standard` / `fast` names
(`HeckeIntegralActionValidation` ≈ 13.5 s, `HeckeConeCrossRouteRingValidation` ≈ 3.5 s,
`HeckeStrictLiftValidation` ≈ 3.0 s, `HeckePeriodicityClassValidation` ≈ 2.3 s,
`EngineFingerprintDeviceBitValidation` ≈ 0.3 s), less ≈ 2–3 s from `HeckeFreeModelValidation`
(arm (R)'s in-process re-runs dropped). All figures indicative (shared box); the close's measured
walls: golden 13.8 s, EngineDet 4.6 s, ExtDet 13.1 s, ConsoleDet 28.8 s, smoke 0.1 s, `--all` 370.2 s, `--all-full` 540.3 s (W1, 2026-09-25).

**Slot 11 (2026-09-25).** `--all` gains ≈ 65–70 s of new `standard` / `fast` names
(`HeckeLadicCellValidation` ≈ 25 s, `HeckeStrictLiftRelationsValidation` ≈ 13–15 s,
`HeckeDicksonThetaHeckeValidation` ≈ 9 s, `HeckeCensusSplitValidation` ≈ 9 s, `HeckeDicksonThetaValidation`
≈ 3.7 s, `EngineLadicInductionValidation` ≈ 2 s, `EngineU128CompositeValidation` ≈ 1.5 s, the two `fast`
names < 0.2 s); `--all-full` also gains the two `slow` θ names (≈ 2.5 min and ≈ 50 s). All figures
indicative (shared box); the close's measured walls: golden 13.6 s, EngineDet 4.5 s, ExtDet 13.0 s, ConsoleDet 28.3 s,
smoke 0.1 s, `--all` 408.6 s, `--all-full` 756.3 s (W1, 2026-09-25).

**Slot 12 (2026-09-26).** `--all` gains ≈ 35–40 s of new `standard` / `fast` names
(`HeckeHidaTowerValidation` ≈ 16 s, `HeckeOrdinaryPrecisionValidation` ≈ 12 s, `HeckeBoundaryFinalityValidation`
≈ 9.4 s, `HeckeFormsHeckeAlgebraValidation` ≈ 3 s, `HeckeThetaCensusRingRefusalValidation` ≈ 0.4 s,
`HeckeCensusCellListValidation` < 0.1 s) plus ≈ 1 s of `ConsoleScriptValidation` / `ConsoleErrorValidation` growth
(script 027, arm (T)); `--all-full` also gains `HeckeHidaTowerSlowValidation` (≈ 160 s). The close's measured
walls: golden 13.5 s, EngineDet 4.5 s, ExtDet 12.6 s, ConsoleDet 28.3 s, smoke 0.1 s, `--all` 445.1 s, `--all-full`
945.3 s (W1, 2026-09-26, run by WP-9).

**Slot 13 (2026-09-27).** `--all` gains ≈ 2.5 min of new `standard` / `fast` names
(`HeckeHidaControlValidation` ≈ 58 s, `HeckeHidaLevelEllValidation` ≈ 42 s, `HeckeCensusLatticeValidation` ≈ 32 s,
`HeckeUEllLowRankValidation` ≈ 8 s, `HeckeBocksteinCuspValidation` < 0.1 s) plus ≈ 10 s of `GoldenRegressionValidation`
(the nine `HIDA` points of R1) and ≈ 8 s of `HeckeBoundaryFinalityValidation` / `HeckeExtRecordValidation` growth (WP-7);
`--all-full` also gains `HeckeMixedFinalityValidation` (≈ 2 s; `HeckeHidaHeavyCellProbe` prints `[SKIP]`). The
close's measured walls: golden 23.2 s, EngineDet 4.4 s, ExtDet 12.8 s, ConsoleDet 38.0 s (T-C4 info 36.7 s; under the 45 s threshold, up from 28.3 s — script 028 and arms (Q9), (T) of slot 12 WP-17 / WP-8), smoke 0.1 s, `--all` 626.6 s, `--all-full` 1133.4 s (W1, 2026-09-27, run by WP-15).

### Slot 26 Z9 HZ-LOC-PAR (the parallel HZ-LOC route; `slot26/Z9_predictions.md`, `slot26/Z9_report.md`)

- **`HeckeZLocalParValidation`** (standard, new): the route bit-identity of `Integral/HeckeZLocal`'s par route (parallel
  closure products with serial-order inserts, semi-naive worklist, K = 1 closure once, exact two-phase column-parallel
  `Span::reduce`, row-parallel `MatMul`) against the slot-25 serial route (the lever `HECKEZ_LOCAL_PAR=0`).
  - (S) 12 span cases: 6 rings incl. u64 moduli, m = 300 / 2000, planted valuations and in-span combinations. Each runs at
    threads 1 / 4 / 16 with the parallel forms forced below their thresholds and compares insert results, row lists
    entrywise and membership.
  - (C) 12 random closures at D = 20–28. Serial vs par: equal length, Smith length, generator count and mutual containment;
    par row lists equal across threads. Plus one natural D = 128 closure, threads 1 vs 16, row lists entrywise.
  - (R) the 30 `HECKEZ_LOCAL` cells under the serial route and under the par route (forced) at threads 1 / 4 / 16: the DIGEST
    over every `LocalRead::text()` is equal, and each gate reads `verdict=OK`.

  Gate line `HECKEZ_LOCAL_PAR cells=30 threads_equal=yes routes_equal=yes default_route=par verdict=OK`.
  Fix round 1 (Z9 audit SF-1/SF-2/SF-3): a preceding line `HECKEZ_LOCAL_PAR threads_max=<k> par_reduce_calls=<n> par_matmul_calls=<m>`;
  the validation installs a scoped 4-worker pool when the ambient pool has < 2 workers, and a check requires both counts > 0 (so the
  gate cannot pass vacuously). Record path: once per process `EFFECTIVE HECKEZ_LOCAL_PAR route=<par|serial> threads=<n>
  source=<default|env>` on C stderr via fprintf (servefix: the `--serve` cell capture swaps `std::cout`/`std::cerr`, so the line must bypass both; first `ReadLocal`; never a record field). `G10.threads` is the EXPORT / descent thread count
  (not hashed); Z9 sizes itself by the consumer pool (`ENGINE_THREADS`).

### Slot 26 HZ-EISUP (the Eisenstein U_p systems of the full algebra at N > 1; design `slot26/HZEISUP_design.md` v0.2, report `slot26/HZEISUP_report.md`)

**One validation is added (standard); the roster grows 287 → 288** (`--all` 239 → 240).

- **`HeckeZEisUpValidation`** (standard, ≈ 9–10 s by name at 4 threads, peak RSS < 0.1 GiB; prediction ≤ 60 s, ≤ 0.4 GiB). Gate line
  `HECKEZ_EISUP cells=10 systems=21 mismatched=0 tag_xcheck=3/3 records=4/4 ce7_ells=12 threads=1,4,16:equal reuse=equal isa=scalar,avx2,avx512:equal
  tamper=6/6 schema_tamper=10/10 support_cases=7/7 ed2_rescan=226/226 hz_level1=15/15 checks=121 failing=0 … verdict=OK` (code-audit fixes m2, m4:
  `schema_tamper` 5 → 10, new `support_cases`, checks 109 → 121). Cells (N, n): (11, 0), (23, 0), (2, 4), (2, 12),
  (3, 6), (5, 8), (7, 4), (22, 0), (33, 0), (38, 0), each with the record's P (P_rule) and the full step's retained runs. Arms:
  - (a) `EisUpStep` runs (C-E1 … C-E5 are `ENGINE_CHECK`s inside it): e_k systems, the `EisUpResult::text()` digest pinned per cell;
  - (b) the second route: the tuples (λ_j(U_p))_{p | N} equal the closed form Ê(N, k) of `prop:heckeZeisup` (5) (`mismatched`, the joint check at
    k = 2 and on the multi-prime cells);
  - (c) every λ_j(U_p) is a root of HZ-UTAG's χ_Q(U_p) (`UTagStep`); at the tag-certified cells (2, 4), (2, 12), (3, 6) the `eis(·)` roots equal the
    tuple set (`tag_xcheck=3/3`);
  - (d) (11, 0), (2, 4), (22, 0), (5, 4) full through the record path: the `G1.components[j].*` rows, no `blocked(U_p)` in `G1.components` /
    `maximal_ideals`, `G0.status = final`, `G10.contract = gl2_contract 1.27.0-pre.1, item 8 (d')`, scan clean, `record_fnv1a64` pinned; C-E7 at
    every decomposed ℓ (`ce7_ells`), ℓ = 5 at (5, 4) decomposed (ℓ | N);
  - (e) `text()` equal at threads 1 / 4 / 16, reuse of the retained runs vs. forced recompute, and under every available rho-fill path, at (22, 0)
    and (2, 12);
  - (f) six tampers, each caught: f_θ + 1 (C-E2), e_k + 1 on a 16-prime cap (`refused(word_prime_cap)`), θ altered after e_θ (C-E5), C_p without
    p^{k−1} (C-E4), U_2 swapped between the lines (1, 11) and (2, 1) at (22, 0) (C-E5; audit m7), λ_0(U_5) + 1 before the attribution at (5, 4),
    ℓ = 5 (C-E7; audit M4; the validation-only `RecordSettings::eisup_tamper_ell`);
  - (g) the 15 `HZ_N1_n<n>_full` records equal HZ-DS edition 1 (`hecke_ed1/rows.tsv`), fingerprint `0x8ffc29730c4f9672`;
  - (h) amendment A4: a forged `G1.components[2]` on an anemic and on a level-1 record of edition 2, a forged `U_3` and a missing `U_11` on (22, 0)
    full, an Eisenstein count e_k + 1 — each caught by `ScanRecord` (the first five); edition 2's 226 cell files (`hecke_ed2/records_bundle.tar.gz`,
    read by `tar -xzOf`) re-verified (`VerifyCellText`) with `values_outside_lists = 0` (`ed2_rescan=226/226`: A4 neutral). Code audit m4 (each
    of the five new cases must be caught by its own problem text, not by any scan problem): the layout beside `G1.C1.status = open(cap)`; the
    (22, 0) layout relabelled to the first N with e^an_k(N) ≠ 1 (scope); a missing `m[0].components_through.1`; a forged `pair_kinds[j,j′]` with
    one component not passing; a level-1 key `m[0].components_through.eis` on the full rows (`schema_tamper=10/10`);
  - (i) code audit m2, `SupportWordOfRead` on a forged torsion read at ℓ = 5 carrying T_3, T_5, T_7 (no U_2), one common block, θ′ on
    (T_3, U_2, T_5, T_7): with the full rows' rule (`involved_only`) θ′ = T_5 (a unit listed after U_2) → `both` / `free`, θ′ = T_3 + T_7 (U_2
    coefficient 0) → `both`; θ′ = U_2 and T_3 + U_2 → `not_run` ([C] (d′)(ii), M1); the anemic / level-1 rule unchanged (θ′ = T_5 after U_2 →
    `not_run` there); an involved residue of degree 2 → `not_run` (`support_cases=7/7`).
- `HeckeZRecordValidation`: the pin `2,6,full` of `HeckeZRecordExpected.inc` moves (`0x980a4da95386391f`, pending → `0xaa516b325e24eed5`, final;
  `slot26/golden_ledger.md`, "non-golden lines moved"); `HECKEZ_RECORD … hashes_pinned=7/7 … verdict=OK`. `HeckeZUpValidation` (f): its printed
  `RECORD` / `HASH` lines of the full records move (final), no assertion changes.


### Slot 26 Z6 (= H2: the discriminant series of the ramified ordinary families at tame level 1; design `slot26/Z6_design.md` v0.2, report `slot26/Z6_report.md`)

**One validation is added (standard by the Q7 rule: measured wall 11.3 s at `ENGINE_THREADS=16` ≤ 30 s); the roster grows 288 → 289** (`--all` 240 → 241).

- **`HeckeHidaDiscLambdaValidation`** (standard, slot-26 Z6, ≈ 11 s at 16 threads / ≈ 34 s serial, peak RSS ≈ 0.16 GiB; 220 checks; prediction
  ≤ 2 CPU-min, wall ≤ 30 s, ≤ 1 GiB): [U] part 7 (`lem:u-DF`, `lem:u-DFread`, `pr:u-H2` (U25)) on the eleven ramified ordinary blocks of
  `prop:u-loewy`(4) at ten cells ((68, 157) carries two). Forms side mod ℓ⁵ (`ComputeFormsWeight`, one prime list P = `SturmPrimes(ℓ, k5)` per
  family) at 5 consecutive weights per class (6 at ℓ ≤ 227: the held-out weight), the non-reduced residual systems at k0
  (`FindNonReducedSystems`), the per-block Fitting split (`ResidualBlock`: sequential generalised kernels of T_p − λ̄_p, then U − ū, certified
  by rank 2; the nilpotency check is a consistency check that holds by construction, code audit F3), D_F mod (ℓ³, Z³) through T_2 (`ReadDisc`).
  **Evidence**: the held-out weight (the full Newton polynomial, mod ℓ⁵), the eleven rows pinned as oracle constants (r̄_2, D, case, s_F mod ℓ²,
  rung2, rung3, λ; `Z6_report.md` §3 = [U] `rmk:u-H2data`; code audit F2; any change fails, `pinned=11/11`),
  the oracles (30, 67) (χ(T_2 | block at 32) = X² − 39960X − 2235350016 mod 67⁵, det U = 56 mod 67) and (68, 157) (r̄_2 ∈ {96, 111}), the
  must-refuse controls (54, 67) at k = 56 and (46, 383) at k = 48 (T_3 has no F_ℓ eigenvalue on the T_2-double-root piece: a conjugate pair).
  **Code checks, not evidence** (audit F11): ring consistency τ̃² − 4ν̃ = D̃, the internal v-reading at the nodes, the one-bit unit-square
  test of q-independence (plus the case word and s_F mod ℓ² agreeing through t′ = T_3), and the (2, 2) subset self-check (j = 2, 3, 4;
  `subset_selfcheck=`): it is **not an error detector** — once the five-node interpolant is ℓ-integral the three-node truncation agrees for
  any values (code audit F1). Tampers, each with its detector: (i) +ℓ⁴ at j = 2 of (30, 67) → held-out; (ii) +ℓ² at j = 3 → the
  integrality refusal of the five-node interpolation (a single-node error of valuation < 4 makes the degree-4 Newton coefficient
  non-ℓ-integral; the precondition of `thm:u-interp`(2)); (iii) r̄_2 + 1 → `ResidualBlock` refuses (rank 0). One `HIDA_H2_BLOCK` line per
  block; gate `HIDA_H2 blocks=11 cells=10 rank2=11/11 gen=11/11 v_e0_one=11/11 oracle=3/3 controls_refused=2/2 ring=11/11
  subset_selfcheck=11/11 q_indep=11/11 heldout=9/9 caseA=10 caseB=1 undecided=0 pinned=11/11 rung_checked=0/0 tampered_detected=3
  fnv=0xcccfa6030f795398 verdict=OK` (the case counts are findings and pinned by the rows; the `fnv=` is not a digest of record, audit Q8; bit-identical
  at `ENGINE_THREADS=1` and 16). Finding: (36, 181) is case (B), λ = 2 (e2 a unit). Read-only arms: `HECKE_HIDA_H2_ALL=1` adds the held-out
  weights at 349 and 479, the known answer (547, 486) of `pr:u-H2`(c) (H1's five f_k mod 547⁵, case A, rung2 = 55086) and the rung check at
  ℓ ∈ {67, 71, 73} in case A (the block at k^{(2)}_F cut with P′ = `SturmPrimes(ℓ, k0)`; v(disc) = 1 + v(k − s_F) ≥ 2); ≈ 19 s at 16 threads,
  0.36 GiB; gate `… oracle=4/4 … heldout=11/11 … pinned=11/11 rung_checked=3/3 … verdict=OK`. `HECKE_HIDA_H2_PROBE=1` (replaces the arms) runs the design's
  two-job cost probe serially and prints walls, no gate. Both print `EFFECTIVE HeckeHidaDiscLambdaValidation arm=<DEFAULT|ALL|PROBE> …`.
  Writes nothing. Not golden. The forms driver runs the per-weight jobs on `oc_util::ParallelForBlocks` (index-addressed merge) and is never
  bound to a console verb.

### Slot 26 Z3b (an M oracle at ℓ = 2, 3 independent of T̃_Iso; design `slot26/Z3b_design.md` v0.2, audit `slot26/Z3b_design_audit.md`, report `slot26/Z3b_report.md`)

**One validation is added (standard: 2.8 s by name at `ENGINE_THREADS=4`, peak RSS 149 MiB; prediction 3–5 s, ≤ 250 MiB); the roster grows +1
relative to the tip at merge** (here 289 → 290, `--all` 241 → 242).

- **`HeckeZCrossedHomOracleValidation`** (standard, slot-26 Z3b). The M block of EXPORT-Z step 2 checked against T_p = [AgA] computed **without
  T̃_Iso**: H¹(SL₂(ℤ); M_N) as crossed homomorphisms (f(S), f(U)), compared with the free tree carrier Iso_T by the closed-form κ, κ′; T_p by
  [C, eq:barcorrected] for A = Γ₀(N) (δ_j = [[p, −j], [0, 1]], δ_p = diag(1, p)) moved to SL₂(ℤ) by Shapiro ([C, prop:descentN](5)); cocycles
  evaluated on words in S, U, T, T⁻¹ (Euclid, multiplied back) by a Horner scheme on the (n+1)² blocks; the oracle's own ρ_n.
  Eight cells (1, 10), (2, 6), (9, 8), (11, 2), (1, 30), (5, 12), (1, 60), (4, 12); 28 torsion units, 15 at ℓ ∈ {2, 3}. Arms: **(K)** conventions
  before any Hecke step (the oracle's ρ_{M_N}(S), ρ_{M_N}(U) = the carrier's d⁰ blocks exactly, own ρ_n = `RhoNZ`, w₁ = I, κ / κ′ identities,
  d¹κ′κ b = 0 exactly, f(−I) ≡ 0, Euclid words, Φ_certᵀ d⁰ ≡ 0 mod q₁, q₂, ℓ^{K_run}, H⁰ = 0); **(F)** Φ_certᵀ y ≡ G F and d¹ y ≡ 0 mod q₁, q₂ and
  ℓ^{K_run}; **(M)** π(R y_j) ≡ M_{·j} + π_B F_{·j} (row a mod ℓ^{σ_a}, R = `RouteBasis`, π = the export's retraction) at every unit and op, plus the
  pinned counts; **(Π)** π(R d⁰m) ≡ 0, π(R b_i) = the exported π_B, π(cocycles) = e_a (sanity); **(I)** RouteBasis is injective on the ℓ-torsion:
  g_i = d⁰(m_i)/ℓ for a basis of ker(d⁰ mod ℓ), ν = t_ℓ and the socle matrix has rank t_ℓ; **(W)** another representative system changes y,
  not (F) or (M); **(T)** teeth (all must fail): M + 1, the pre-fix block M_local C, ρ_n(δ^ι), and y_j + g_i (a real carrier torsion class through
  R) at every g_i of every unit at ℓ = 2, 3. Gate `HECKEZ_XHOM_ORACLE arms=7 failing=0 cells=8 checks=748 tor_units=28 units_23=15 nonzero_23=11
  teeth=125/125 hecke=barcorrected/shapiro verdict=OK` (bit-identical at `ENGINE_THREADS=1` and 4). Read-only hook `HECKE_XHOM_CELLS="N:n:p1/p2,…"`
  (replaces the cells; prints `EFFECTIVE HeckeZCrossedHomOracleValidation arm=cells cells=<k>`; floors and the pinned counts are then not
  asserted). Writes nothing. Not golden; no production file changes.
  **Slot-27 Z3b-F** (audit F6, F7 and the design-Q4 τ follow-up; no new name, no value moves): an eighth arm **(Tau)** checks τ on the
  ℓ-socle without T̃_Iso: π(R T^× g_i) ≡ τ|_ℓ π(R g_i) (row a mod ℓ^{σ_a}) for the exact integral socle cocycles g_i of (I), with T^× g_i by
  [C, eq:barcorrected] via Shapiro, at every unit (ℓ = 2, 3 and ℓ ≥ 5) and op. Its teeth (all must fail): τ + 1 at every diagonal entry of the
  ℓ-block, caught because each row of the (I) socle matrix is non-zero mod ℓ; and T^× g_i + g_i pushed through R. Floor 200 (250 checks,
  166 teeth). The gate line adds `nonzero_M_23` (units at ℓ ∈ {2, 3} with M ≠ 0 for some op, F6) and `tau_nonzero` (units with
  π(R T^× g) ≠ 0); the ARM lines drop the always-zero `skipped=` field, and `caught=` is printed per arm (F7; every global is reset at the top of
  `Run()`). Gate `HECKEZ_XHOM_ORACLE arms=8 failing=0 cells=8 checks=998 tor_units=28 units_23=15 nonzero_23=11 nonzero_M_23=9 tau_nonzero=18
  teeth=291/291 hecke=barcorrected/shapiro verdict=OK` (3.4 s, 154 MiB; bit-identical at `ENGINE_THREADS=1` and 8, and across two in-process runs).

### Slot 27 EXW (the at-root read and the (C3) read on the free block over Z where rule (α) fires; design `slot27/EXW_design.md` v0.2, audit `slot27/EXW_design_audit.md`)

**One validation is added (standard); the roster grows +1 relative to the tip at merge** (here, after TS, 291 → 292, `--all` 243 → 244).

- **`HeckeZExportWordValidation`** (standard, slot-27 EXW; ≈ 100 s by name at the default threads on a loaded box, peak RSS ≈ 0.42 GiB;
  prediction 60–100 s, ≤ 0.8 GiB). The free route: `LatticeFromFreeZ` (`Integral/HeckeZLocal`: T_o = F_o mod ℓ^K, F_o the proven matrix over Z
  of EXPORT-Z step 2 in the certified basis, `word_modulus` first), `ReadCellLocal(…, FreeSource*)`, the record source
  `RecordSources::local_read_free` = `FreeLocalRead()` (`HeckeExt/HeckeZRecordSource`: a per-cell lazy cache of one `RunFreeBlock`;
  route refusals → `blocked(free_block)`, never a word; `Uncertified` / `SingularG` / `BoundViolated` are defects). The record calls it only
  where rule (α) fires (`CtListed` = the G3 writer's own condition; `decide_gen` = the G2 writer's own decision) and ENGINE_CHECKs χ(F_p mod ℓ^K)
  against the descent's χ_Z on every free read it uses. Arms:
  - (A) route identity (Lemma 1): `ReadLocal`'s words (`LocalRead::text()` with `source` / `word` blanked) equal on the EXPORT / level-1 route
    and on the free block wherever both serve: (11, 0) anemic @5 K ≤ 2, (2, 6) anemic @17 and @2 (K = 9), (1, 40) @7 (a level-1 torsion prime,
    T_7 appended and compared), (8, 10) anemic @2 (K = 25), (11, 0) anemic @65521, (11, 0) full @5 and @2 (U_11), (1, 22) @103 (the H^1 route);
    `identity=17/17`;
  - (B) class A beyond K_max: (8, 10) anemic @2 at K0 = 33 > K_max = 25 → `upper_bound_certified`, `lower_v` 18, `upper_v` 32, η exponents {8, 18}
    (`eta_oracle.py`);
  - (C) class C / k1 at K = 1, ℓ > 2^32: (7, 12) anemic @5322111401, (173, 0) anemic @5608385124289 (export `refused(export_word)`), (1, 32)
    @151628697551 (level-1 `refused(word_modulus)`): (C3) `certified`, dim A'_1 = d = 8, 15, 3 (`c3probe.py`), monogenic (T_2);
  - (D) overflow teeth: `FreeBlockModQ` against a u128 Horner residue at q ∈ {2^31 − 1, 2^32 + 15, 5103536431379173, 2^62, 7^17}; q ≥ 2^63
    refused; `Zlk::Fits(3037000493, 2)` and not `Fits(3037000507, 2)` (the design's 3037000499 is not prime and fits); `LatticeFromFreeZ`
    serves K = 2 at 3037000493, `refused(word_modulus)` at 3037000507; an operator outside the block is a defect;
  - (E) four whole records, EXW on vs. the seam empty (`local_read_free = nullptr`): (173, 0) anemic, (197, 0) anemic, (1, 36) full (one (C3)
    trigger each), (8, 10) anemic (one root trigger): the seam-empty record is edition 3's (`pending`), EXW on is `final` with no
    `export_word` / `k1_route`; every moved hashed field inside the diff rule of the design's Sec. 5 at the triggered ℓ; G10 moves only there
    (timings blanked); `maximal_ideals` at ℓ ≥ 2^31 by `FpPoly64`; `WriteCertFiles` twice on (8, 10) and (173, 0) anemic: byte-stable,
    `dump_sha256_recomputed` = G9's, the triggered ℓ's file written (M2);
  - (F) route bit-identity: the free source at threads 1 / 16 and HZ-LOC-PAR par / serial on (7, 12) @5322111401 K = 1 and (8, 10) @2 K = 33:
    words, module and F FNVs equal;
  - (G) teeth: F_3 + ℓ^(K−1) E_11 on the free read of (8, 10) anemic is caught by the χ_Z check; a free-block `RssCeiling` (cap 1 MiB) keeps the
    pending word, writes `G10.read.ell=2.exw = refused(RssCeiling)`, and the hashed record equals the seam-empty one; a forced `[Terms]` of the
    appended T_7 at (1, 40): retried without it, @7 refused by name, @65537 served;
  - (H) record-level identity by forcing: (i) (1, 52) @7 with the export's K_max refusal forged at K ≥ 2 → the root trigger gives the unforged
    record's `record_fnv1a64`, the cert differing only in the basis-dependent values (`G9.K3.ell=7.dump_sha256`, the `tb_mat` entry);
    (ii) (5, 4) full @5 and @11 with `[ModulePrecision]` forged at every K → the (C3) trigger on the full loop gives every hashed field of the
    unforged record (`G0.operators` up to the T_ℓ that the forged K0 read no longer appends); (iii) origin (b) of the design's §1: (1, 52) @7
    served at K0 = 3 with its escalation forged to stop at "the export's K_max" → the root trigger; the (C3) path keeps the served module
    (moved to `c3out`), so G2, G9.K1 and `tb_mat` are byte for byte and only `G9.K3.ell=7.dump_sha256` differs;
  - (I) the negative case of (α): (1, 22) @3 (generation `eis_single`, a forged (C3) refusal at every K) and (1, 40) @7 (7 ∤ g_P, a forged K_max
    refusal): the free source is never called (counter 0) and the record is byte-identical to the seam-empty one (body, cert, G10 without
    timings);
  - (J) (code audit M-EXW1, EXW fix) free-block refusals per requested set, on (8, 10) anemic with the ceiling set to P's own prediction
    (pred(P) = 398986344 B, pred(P + T_11) = 785092968 B at 16 lanes): (i) @11 (P + T_11) refused `[RssCeiling]`, then @2 (P only) served with
    the reference words, @11 not re-run (`runs=2`); (ii) @2 served, @11 refused, @2 served again from the cached block; (iii) the record at
    that ceiling is the default record (`final`), the same source then poisoned by a refused @11, and `WriteCertFiles` with it succeeds;
  - (K) (code audit M-EXW2, EXW fix) the `[RssCeiling]` decision at threads 1 / 4 / 16: @2 served at the ceiling pred, refused at pred − 1,
    the prediction equal (made at `kFreeReadRssLanes` = 16 lanes, `FreeBlockOptions::rss_lanes`, whatever the run's lanes).
  Gate line `HECKEZ_EXW arms=11 failing=0 identity=17/17 pairs=4 moved=264 negative=2/2 checks=124 secs=… verdict=OK` (130.7 s by name,
  ENGINE_THREADS=8, on a loaded box, of which (J)+(K) 57 s; before the EXW fix `arms=9 … checks=116`, 100.6 s. If a quiet-window measure
  exceeds 100 s, arms (E) and (F) — and now (J)/(K) — move to a `slow` sibling, the design's §6 rule).
  Rule 19 (code audit m-EXW3): the free source keeps its carrier and block resident for the life of the source (in a campaign until the
  next cell and through `WriteCertFiles`), so an EXW cell's peak RSS is the EXPORT read's plus the free block's.
  `ValidationShardWeights.inc` (generated) is not regenerated by EXW: the name runs unweighted until the next `shard_weights.py` measure. Env arm (not in `--all`,
  read-only, writes nothing): `HECKEZ_EXW_ALL=1` builds the 22 pending records of edition 3 EXW on (`HECKEZ_EXW_CELLS="N:n:alg,…"` restricts to
  those of the 22 named), prints `EFFECTIVE HeckeZExportWordValidation arm=all cells=<k>`, one `EXW_ALL` line per record with its `exw` lines,
  and `HECKEZ_EXW_ALL cells=… pairs=… final=… failing=… verdict=…` (cost: the design's Sec. 7, up to ≈ 1.9 h one-thread free blocks plus the
  records). Not golden; no golden object moves (the 15 HZ objects trigger nothing).
- `HeckeZRecordValidation`: the forged sources of the word-mapping arm run with the seam empty (`f.local_read_free = nullptr`, design M3); the
  pin `8,10,anemic` of `HeckeZRecordExpected.inc` moves (`0x45bdc565b75b660b`, pending → `0xb16a763da2fc4205`, final: its at-root read at
  ℓ = 2 is one of rule (α)'s 23 pairs; not golden).
- `HeckeZUpValidation`: arm (f) (the 18 records hash-equal to HZ-DS ed. 1) runs with the seam empty, since (8, 10) anemic is EXW's.
- `Integral/HeckeZEisUp.cpp` (HZ-EISUP's attribution at ℓ): `AttributeAtEll`, `ValuationOfDifference`, `CuspResultantValuation` accept ℓ < 2^63
  (were 2^31 / 2^32), since EXW's (C3) read certifies generation at ℓ ≥ 2^31 on the full records (167, 0), (173, 0), (197, 0) (class C). The
  products are 128-bit and v_ℓ is taken by exact BigInt division only above those bounds; below them the code is unchanged byte for byte.
  Env arm `HECKEZ_EXW_CELLS="167:0:full,173:0:full,197:0:full"`: `HECKEZ_EXW_ALL cells=3 pairs=3 final=3 failing=0 verdict=OK` (232 s,
  2.86 GB at `ENGINE_THREADS=8`). The other 10 cheap records of the 22 read `final` on 707f7aa9 (1103 s, 2.8 GB); the 9 class-A level-1
  records (n ≥ 166) have not run yet.

---

## Moved from CLAUDE.md at the slot-17 start (2026-10-02), verbatim — "Validation / Tests" (tiers with their per-slot history, the full owner-gated emitter / env-hook table, the EFFECTIVE convention)

*(Copied unchanged from `CLAUDE.md` at `6863260`, lines 169–284; headings inside keep their original levels. `CLAUDE.md` now carries a compact form.)*

## Validation / Tests

There is no test framework. Validation is done via functions returning 0 on success, registered by name in `src/hacs/ValidationRegistry.cpp` and runnable without editing `main()`:

```bash
./hacs --list      # print every registered validation name, with its tier
./hacs <Name>      # run exactly one; exit code = its own return code
./hacs --all       # run the fast + standard tiers; exit code = failure count
./hacs --all-full  # run every tier, slow included; exit code = failure count
./hacs             # no args: legacy default benchmark, unchanged
```

An exception escaping a validation (an `ENGINE_CHECK`'s `std::logic_error`, …) is reported as **that
validation's failure** (an `[EXCEPTION] <name>: …` line, then `[FAIL]`) and the run goes on — since S13 WP-16;
before it the harness caught nothing and such an exception ended the process in `std::terminate` (exit 134).
**Since slot-14 WP-2 the catch path has its own test**: `ValidationHarnessCatchValidation` (`fast`) sends two
private, unregistered throwing functions through the same guard (`run_guarded_standalone()`): one throws a
`std::exception`, one does not. It checks the printed `[EXCEPTION]` / `[FAIL]` lines, that a third, clean
function still runs, and one failure per thrower. This closes the S13 WP-16 carry ([X] v1.18.1 (3)).

**Tiers.** Every registered validation carries a tier (`fast` / `standard` / `slow`, printed by
`--list`). `--all` runs `fast` + `standard` and skips the `slow` tier; `--all-full` runs
everything. Of the **169** registered validations (**61** `fast`, **92** `standard`, **16** `slow`, so `--all` runs **153**; derived from the source by slot-16 WP-18a —
every `register_validation("<Name>", …, ValidationTier::<T>)` call at `7f36871`, 169 unique names — and equal to WP-15's `--list` on its repaired build; slot 16 added
`LeanCensusFileValidation`, `HeckeTauDumpValidation` (both `fast`), `HeckeSaturationDefectValidation`, `HeckeNebentypusValidation`,
`HeckeIsotropyModelEllValidation` and `HeckeHidaCMValidation` (all `standard`); the slot-15 close was 163 = 59 / 88 / 16 after S15-O1, and slot 15 added
`HeckeHidaComponentsValidation`, `HeckeLevelNHeilbronnValidation`, `HeckeLevelNSparseValidation`, all `standard`; the slot-14 close was 159 = 59 / 85 / 15, WP-17; slot 13 closed at 155 = 58 / 82 / 15, and slot 14 added `ValidationHarnessCatchValidation` (`fast`), `HeckeRingLoewyValidation`, `HeckeUEllStreamValidation` and `HeckeLevelNValidation` (all `standard`)), the `slow` tier holds exactly sixteen (fifteen since slot 13, plus `HeckeRingLoewyDigitSlowValidation`, S15-O1; slot 16 added none) —
`HeckeBenchmarkSmoke`, `SymmetricPowerValidationSlow`, `EngineDeviceTrapValidation`,
`HeckeUEllReachSlow`, **`HeckeExtKummerValidation`** (slot-5 WP-8: ten Kummer cells at the default
settings cost 37.5 s, of which `U_3617` alone is 33.9 s), **`HeckeAtlasValidation`** (slot-6 WP-8:
`Σ(ell)` for `ell ≤ 13`, 15 607 checks since slot-7 WP-5, 15 963 when its arm (K) on the `ell = 691` store runs —
it `SKIP`s unless `HECKE_ATLAS_IN=<dir>` names a directory holding the unpublished store), **`HeckeExtEndToEndValidation`**
(slot-6 WP-9: identity 6 on 108 cells, ≈ 45–75 s), **`HeckeDualityCoverageSlowValidation`** (slot-7
WP-1: `cl:pd` on three M1 cells, ≈ 28 s), **`HeckeReductionCoverageSlowValidation`** (slot-8 WP-4: E8
acceptance (d) on the bulk over the E2 case list at `ell ≥ 5`, the identity
`bockstein_rank^0 + higher_torsion_count == dim H^0(F_ell)` and P3's controls; since slot 9 also
E8 item 4b's arms on that list and, since slot-9 WP-4t, the `(60, 5)` 4b cell at `k = 2, 3`; 3731 checks, ≈ 17 s) and `HeckeLocalityProbe` (the last one additionally interlocked on `HECKE_LOCALITY_PROBE=1`, so even
`--all-full` only sees its `[SKIP]` line), and since slot 11 **`HeckeDicksonThetaCoverageSlowValidation`** (WP-5: the θ
long exact sequence on 404 cells, 3590 checks, ≈ 2.5 min) and **`HeckeDicksonThetaHeckeCoverageSlowValidation`** (WP-6:
θ's Hecke equivariance on the slow grid, 3836 checks, ≈ 50 s), and since slot 12 **`HeckeHidaTowerSlowValidation`** (WP-5:
the Hida towers on 280 cells, `n ≤ 200` at 13, and `(10, 2411)` at `K = 3`; 11 722 checks, ≈ 160 s, ≈ 4 GB), and since
slot 13 **`HeckeHidaHeavyCellProbe`** (WP-10: the heavy Hida cells behind the `U_ell` lever; **interlocked** on
`HECKE_HIDA_HEAVY=1`, so `--all-full` sees only its `[SKIP]` line) and **`HeckeMixedFinalityValidation`** (WP-11: the
evidence arm of the `mixed` finality proposal, Proposition M; ≈ 2 s on its default cells, `slow` for its scan hook
`HECKE_MIXED_FINALITY_CELLS`) — so
**the Hecke acceptance gate (`HeckeEndToEndValidation` + `HeckeBadPrimeValidation` +
`HeckeBenchmarkSmoke`) needs `--all-full`, not `--all`** — or run the three by name.

**The catalogue.** What each of the 169 validations actually checks — check counts, tiers, timings,
arm lists, the oracles it compares against, organised by matrix-engine phase and by
hecke-extensions slot — is **`docs/validation-catalogue.md`**. Read it before touching a
validation, and before assuming a name means what it sounds like. (The six pre-existing non-Hecke
validations are `mod_arithmetic_validation`, `MatrixValidation`, `FlatMatrixValidation`,
`BlockFlatMatrixValidation`, `SimplicialCohomologyValidation`, `LocalSystemCohomologyValidation`.)

`./hacs Name1 Name2 ...` runs several validations **in one process** (exit code = number
of failures) — the way to reproduce a state-dependent failure without a full `--all`.

The Hecke feature's tests are the **108** `Hecke*` names registered in `ValidationRegistry.cpp` and the slot-9 …
slot-16 fragments `Registry/Slot{9,10,11,12,13,14,15,16}/<name>.cpp` (108 derived from the source at slot-16 WP-18a; the base `b8a196d` had 103, one more
than the 102 this line used to quote — `HeckeRingLoewyDigitSlowValidation` of S15-O1 was not counted) (e.g. `HeckeOracleValidation`, `HeckeRelationsValidation`, `HeckeBlockFormValidation`, `HeckeEndToEndValidation`) — run any of them the same way, or see `src/hacs/Hecke/README.md` for the full list and the file→contract-section map.

### Owner-gated emitters and env interlocks (safety-critical)

Four registered names can **write** (`GoldenEmit` and `ConsoleScriptEmit` into the tracked tree,
`GoldenDump` and, since slot-16 L16-4, `HeckeTauDumpValidation` into a directory you name), one variable selects the strict acceptance mode, and two
validations are interlocked on a run (`HeckeLocalityProbe`, `HeckeHidaHeavyCellProbe`). Each is a no-op unless its environment variable is set, which is
what keeps `--all` and `--all-full` read-only. Never set one of these to "make a validation pass".

| Env | Effect |
|---|---|
| `GOLDEN_EMIT=1 ./hacs GoldenEmit` (optionally `GOLDEN_OUT=<path>`) | regenerates `Golden/GoldenReference.inc`. **Owner-gated re-baseline**: every changed line must be explained object by object. |
| `GOLDEN_DUMP=<dir> ./hacs GoldenDump` | writes the before/after object dump of the re-baseline protocol ([X] §1.6 steps 1–4) to `<dir>/{index.tsv,texts.tsv,decompositions.txt}`; diffed by `docs/matrix-engine/tools/golden_explain.py before after [--allow-keys FILE] [--accept-split "<point> <object>"]…`. |
| `GOLDEN_GEVT23` | **RETIRED** by the HZ-GOLD landing (slot 25, 2026-11-07; `docs/matrix-engine/rebaseline-s25-hzgold-addonly-gevt23-heckez.md`): it was the scratch interlock of slot-25 GOLD-PORT / HZ-GOLD while `kGEvt23InReference` / `kHZInReference` were false, adding the 97 G-EVT23 and 15 HZ tier-A points to a scratch `GoldenEmit` / `GoldenDump` only. Both gates are now `true` and in the reference, and the variable is no longer read. |
| `GOLDEN_STRICT=1` | makes `GoldenRegressionValidation`'s **tier B** gate as well as tier A. Not an emitter; the strict acceptance mode. |
| `CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` | regenerates the `.expected` transcripts of `Console/scripts/`, exactly as `GoldenEmit` regenerates `GoldenReference.inc`; refuses to freeze a script that does not exit 0. |
| `HECKE_LOCALITY_PROBE=1` | the only interlock on a *run*: without it `HeckeLocalityProbe` prints `[SKIP]` even under `--all-full`. |
| `HECKE_DUALITY_COVERAGE_LARGE=1` | read-only, not an emitter: adds `(160, 691)` and `(198, 691)` (≈ 6 min) to `HeckeDualityCoverageSlowValidation` (slot-7 WP-1). |
| `HECKE_REDUCTION_COVERAGE_LARGE=1` | read-only, not an emitter: adds `(160, 691)` and `(198, 691)` (≈ 25 s) to `HeckeReductionCoverageSlowValidation` (slot-8 WP-4). |
| `HECKE_INTEGRAL_CAMPAIGN=1` | read-only, not an emitter: adds the `n = 128` campaign arm (`p ∈ {2, 3}`, 131 `F_ell` runs, ≈ 30 s) to `HeckeIntegralCharpolyValidation` (slot-8 WP-7). |
| `CONSOLE_DETERMINISM_ARMS=threads` | read-only, not an emitter: restricts `ConsoleDeterminismValidation`'s C4 product to its four thread arms (the `CheckThread` run; slot-8 WP-10). |
| `HECKE_THETA_IMAGE_ALL=1` | read-only, not an emitter: adds the census θ-image arm to `HeckeDicksonThetaHeckeValidation` — the 384 `ext_first` cells at `ell ≤ 13`, 1934 ideals matched one-to-one, one `THETA_IMAGE` line each (34 337 checks, ≈ 4–5 min, ≈ 2 GB; slot-11 WP-6). `… \| grep ^THETA_IMAGE` regenerates `docs/implementation/slot11/WP-6_theta_image.tsv`'s rows. |
| `HECKE_CENSUS_SPLIT_ALL=1` | read-only, not an emitter: adds arm (D) to `HeckeCensusSplitValidation` — the computed split over every census cell of edition 1 (406 cells, 1958 `CENSUS_SPLIT` lines, 5643 checks, ≈ 14 min, **≈ 9.6 GB peak** at `(198, 691)`; slot-11 WP-7). The grid is edition 1's (`CensusEdition1Grid()`); `HECKE_CENSUS_SPLIT_CELLS` wins over it (slot-12 WP-6). |
| `HECKE_LEVEL_CONE_CELLS="A:B:ell:n[:chi],…"` | read-only, not an emitter (slot-23 LES-3; `LES0_spec.md` §4): **replaces** `HeckeLevelConeValidation`'s arms by the listed cells and prints `EFFECTIVE HeckeLevelConeValidation arm=CELLS cells=<k>`; each cell runs Route A (`RunCell`: certificate, exactness, zig-zag, `d α = α d`; no predicted numbers, no Hecke operators) and, at ℓ ≥ 5, Route B's six numbers, gated equal. Levels `G`, `G0.<N>`, `G1.<N>`, `GH.<N>.<u>…` (H generated by the units), `Gp.<M>` (`Γ(M)`, M ≤ 30), `G2`, `G3`; χ `1` (default), `w<e>` (`u ↦ (u mod ℓ)^e`, ℓ ∣ N_A) or `leg<q>`, the same datum on B. A malformed token is refused **by position** (`REFUSED … token <k>`, `cells=0`, nothing runs, FAIL); a set-but-empty value is refused as token 0; `G0.1` / `G1.1` denote `Γ`. Cost per cell: predict it (rule 19) — Route A's dense bases grow as `(11 m_B(n+1))²`; the spec cap `m_B(n+1) = 1200` (`G1.5:GH.25.6:5:9`) ran in ≈ 106 s at ≈ 4.6 GB peak (predicted ≤ 8 min, ≤ 5.5 GB) (`slot23/LES3_report.md`). |
| `LADIC_INDUCTION_PROBE_N128=1` | read-only, not an emitter: adds the indicative cost probe (`d^1` of `(128, 5)` over `Z/5^26`) to `EngineLadicInductionValidation` (slot-11 WP-18b). |
| `ENGINE_LADIC_WIDTH=32\|64\|128` | the digit width of the (C2) route (`Hecke/LadicCell`, `ell^k ≥ 2^64`); **cannot change a value** (the records are width-independent — `HeckeLadicCellValidation`'s oracle (iv)); not an emitter (slot-11 WP-18c). |
| `ENGINE_BIGNTT_MIN_LIMBS=<k>` | (slot-27 BIGNTT M1) the size in 32-bit limbs of the modulus from which the untrusted factor finder's Miller--Rabin uses `nf::bigntt::BarrettModulus` (NTT product + Barrett) instead of BigInt's `(x y) % n`; default 1 024 (measured crossover ≈ 900–1 024 limbs). A **route knob, not a rollback lever** (design v0.2 §4, audit m6): every value is exact and unique, so it **cannot change a value**; not an emitter. |
| `ENGINE_GPU_IMMA=0` (any value starting with `0`) **(retired in OFF builds)** | **a rollback arm, not an emitter, cannot change a value** (slot-22 G1, ENGINE_API §11.8; **retired 2026-11-04 by S24 CL-R2**: honoured only with `OC_ENABLE_LEGACY=ON`; the default OFF build refuses it, `REFUSED ENGINE_GPU_IMMA=0: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, read at start-up; the arms that set it are legacy arms, `cross_config.sh` arm `legacy-gpu-imma`): turns off the int8 tensor-core GEMM route of `EngineCuda` for `u32` moduli `2 ≤ p ≤ 127`; unset, empty or any value **not starting with `0`** = on; any value starting with `0` (`0`, `00`, `0x`, …) = off (`imma_policy()` tests the first character). Reached only by device GEMMs (`ENGINE_DEVICE=gpu\|hybrid`, or a direct call of the CUDA layer), so the `cpu` golden path never sees it; also needs cc ≥ 8.0. Re-read per call. `CudaImmaBitIdentityValidation` (F) proves the rollback hash-equal; `--bench micro gemm … --backend gpu` takes the route at `ell ≤ 127` unless it is `0`. |
| `ENGINE_GPU_ELIM=0` (any value starting with `0`) **(retired in OFF builds)** | **a rollback arm, not an emitter, cannot change a value** (slot-22 G2, ENGINE_API §11.9; **retired 2026-11-04 by S24 CL-R2**: honoured only with `OC_ENABLE_LEGACY=ON`; the default OFF build refuses it, exit 1, read at start-up; arm (D)'s `=0` case is a legacy arm; `cross_config.sh` arm `legacy-gpu-elim`): turns off the device-resident elimination (`cuda::imma_rref`) that otherwise replaces, under `ENGINE_DEVICE=gpu` only (never `cpu` / `hybrid`), `tape::rref` and every `uint32_t` DenseElim RREF / `column_rank_profile` over a field `p ≤ 127` with `≥ ENGINE_GPU_ELIM_MIN` entries. Re-read per call. `CudaImmaElimValidation` (D) proves it; the census records of `G2_report.md` are byte-identical under both states. |
| `ENGINE_ELIM_SESSION=0` (any value starting with `0`) **(retired in OFF builds)** | **a rollback arm, not an emitter, cannot change a value** (slot-18 WP-19a, ENGINE_API §12.8; **retired 2026-11-04 by S24 CL-R2**: honoured only with `OC_ENABLE_LEGACY=ON`; the default OFF build refuses it, exit 1, read at start-up): no elimination session under a device policy (each per-panel program binds its own mirrors). Re-read per call. `EngineElimSessionValidation`'s arms `session-off` and `volume-rollback` (legacy arms) compare it; `cross_config.sh` arm `legacy-gpu-session`. |
| `ENGINE_GPU_ELIM_MIN=<entries>` | **tuning, cannot change a value** (G2): the size floor `m·n` of the device elimination (default `1048576`); re-read per call. `CudaImmaElimValidation` sets `0` for its small cases and checks the floor in (D). |
| `ENGINE_GPU_ELIM_VERIFY=1` | **diagnostic, cannot change a value** (G2): re-runs every device elimination on the host and compares it entrywise (always on in an `ENGINE_VERIFY_DEVICE=ON` build); a difference throws. |
| `ENGINE_GPU_ELIM_SIMULATE_CUDA_ERROR=1` | **test-only, cannot change a value** (G2 audit R1): raises a `CudaError` at the start of each device elimination so the counted, announced host fallback runs (`CudaImmaElimValidation` (H)); the values are the host's. |
| `ENGINE_TRACE_IMMA_ELIM=1` | **diagnostic trace, cannot change a value** (G2): one line of phase times per `imma_rref` call (synchronises per phase). |
| `ENGINE_BINARY_F2=1` | **opt-in route, default off, cannot change a value** (slot-22 BIN-1, ENGINE_API §8.1): exactly `1` (read once per process) routes every DenseElim RREF / `column_rank_profile` over the field `F_2` (`uint32_t`, `uint64_t`) to `engine::binary` (bit-packed M4RI); `tape::rref` and `engine::blk` are not routed. `BinaryF2Validation` proves it entrywise; `GOLDEN_STRICT=1 ENGINE_BINARY_F2=1 GoldenRegressionValidation` is clean. |
| `ENGINE_GPU_LEAN=0` (any value starting with `0`) | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `ENGINE_GPU_LEAN=0…` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its validations switch it by the `Scoped` override since the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 PERF-P7, ENGINE_API §12.9). By default, under `ENGINE_DEVICE=gpu` / `hybrid`, a compiled program whose GPU nodes are all memory-class runs on the host path, unless an elimination session is open. The arena's soft-trim slack is a sixteenth of the card. `0` restores the pre-P7 behaviour: such programs run on the device and the slack is a quarter of the card. The rule is re-read per run; the slack is read once, at context creation. `GpuLeanSessionValidation` proves it; `EngineCrossDeviceValidation`'s first three `gpu` arms run with `0`, so they keep the memory kernels' device coverage. **An `ENGINE_VERIFY_DEVICE` campaign includes an `ENGINE_GPU_LEAN=0` arm** (audit R3): under the default, lean programs never reach the device, so their kernels are not re-checked on the workload. Set it before the first GPU use: the slack is read once. |
| `ENGINE_TRACE_VRAM=<ms>` | **diagnostic, cannot change a value** (P7): a sampler prints `VRAM t= live_mb= reserved_mb= dev_used_mb=` to stderr every `<ms>` (default 1000). At exit it prints `EFFECTIVE DEVICE_MEM peak_live_mb= peak_reserved_mb= dev_used_peak_mb= … at_peak: <family>:<count>x<KB> …`, the live blocks at the live peak grouped by program family. |
| `ENGINE_HOST_ELIM_HOOK=0` | **a rollback arm, not an emitter, cannot change a value** (in the rollback-lever register since S26 LEVERS-26; retirement deferred to the slot-27 close) (slot-23 PERF-P2, `EngineRuntime.h`): read once per process. By default the cone (`EquivariantMappingCone::compute`, `ConeCertificate::verify`) and ι^* (`HeckeInvolution::compute`, `InvolutionCertificate::verify`) bind `engine::elim`'s inner parallel hook to the consumer pool (`ScopedHostElimHook`; nothing on a one-worker pool); exactly `0` installs nothing (the pre-P2 single-threaded host eliminations). `HostElimThreadDeterminismValidation` prints `arm=rollback regions=0` and the same digests under it. |
| `ENGINE_VNNI=0` / `ENGINE_VNNI_SHADOW=1` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `ENGINE_VNNI=0` / `ENGINE_VNNI=off` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route (the u32 kernel) stays in every build (its comparison arms use `set_vnni_path(VnniPath::Off)`, unchanged by the retirement; `ENGINE_VNNI_SHADOW=1` and `ENGINE_VNNI=1` are unchanged; the `cross_config.sh` arm is now `legacy-vnni-off`, the ON build). Before: **rollback arm / shadow, cannot change a value** (slot-23 PERF-P5, ENGINE_API §6.1): read once per process. The VNNI route of `gemm<uint32_t>` for `p ≤ 128` (and, slot-24 G4, ENGINE_API §6.2, the two-limb route for `128 < p ≤ 2^14`) is **default on** where the CPU has `avx512_vnni`; `ENGINE_VNNI=0` (or `off`) selects the pre-P5 u32 kernel for both; a set `ENGINE_VNNI` prints one `EFFECTIVE ENGINE_VNNI arm=<off|auto> value= vnni_available= one_limb_max=128 two_limb_max=16384` line on stderr, exactly once per process (also when `set_vnni_path` overrides it), and a value other than `0` / `off` / `1` / empty also prints `WARNING engine: ENGINE_VNNI='<v>' is neither 0, off nor 1; the VNNI route stays ON` (G4 audit F2 / F3) (the `cross_config.sh` arm: `legacy-vnni-off`, the ON build, since S26 LEVERS-26; was `RelWithDebInfo@ENGINE_VNNI=0`). `ENGINE_VNNI_SHADOW=1` recomputes every routed call on the u32 route and throws on the first differing cell; it prints `VNNI_SHADOW calls= cells= differ=` on stderr at exit (`differ` = calls that threw, audit R2; the shadow holds an `m × n` copy per routed call, so RSS grows by about one C window) (slot-23 run: golden strict 11 652 calls, EngineDet 68 380, ExtDet 65 232, 0 differing). |
| `ENGINE_VNNI2_FLOOR=<digits>` | **rollback arm / calibration knob, cannot change a value** (slot-25 PERF-VF (a), ENGINE_API §6.2): the two-limb VNNI route (`128 < p ≤ 2^14`) under Auto also needs `m·n·k ≥ floor · threads` (default floor **`2^20`** since S26 LEVERS-26, calibrated at ext n = 160, ℓ = 691 under `gate.lock`, 7 rounds: t16 median 0.2426 s vs 0.2544 s at `2^18`, t1 0.8531 vs 0.8632, `slot26/LEVERS26_report.md` §3; `2^18` before; threads = the configured global pool size); read once; `0` restores the slot-24 Auto rule; a set value prints `EFFECTIVE ENGINE_VNNI2_FLOOR floor= value= threads=` on stderr **when the floor is first consulted** (under Auto, at the first two-limb call that passes the large-p test; nothing prints under `ENGINE_VNNI=0` / Force or without such a call); digits only: anything else (a sign, whitespace, a value over 64 bits) keeps the default and prints a WARNING; `floor · threads` saturates. `VnniGemmBitIdentityValidation` (R) checks the predicate, its boundaries, the saturation and (PERF-VF audit S2) the G4-F1 contrast at 64×1024×1024; its two-limb expectations follow the floor, so an extreme value does not fail it. |
| `ENGINE_KERNEL=portable\|avx2\|avx512\|auto` / `ENGINE_AVX2_PAIR=0` | **read-only kernel selector / rollback arm, cannot change a value** (slot-24 AVX2K, ENGINE_API §6.3): read once per process. `ENGINE_KERNEL` names the u32 GEMM microkernel `Auto` resolves to (unset = AVX-512 if the CPU has it, else AVX2, else portable); `avx2` on an AVX-512 box is the Zen 3 / host-B proxy (no VNNI routes); an unavailable or unknown value prints a `WARNING` and stays `auto`; a set value prints `EFFECTIVE ENGINE_KERNEL path= value= cpu=avx2:<0\|1>,avx512:<0\|1> governs=gemm,ring2k,ring3k(portable),bitmatrix,tritmatrix,rho_fill,descent_smith` on stderr. **(S24 CL-5, C-06) It governs every module with ISA bodies, not only the GEMM**: each module's `Auto` takes its best body at or below the value (`portable` = portable bodies everywhere, `avx2` = no AVX-512 body anywhere): ring2k, `BitMatrix` / `TritMatrix`, the rho fill, the descent Smith kernels, ring3k's small-modulus rows (portable only); a module's own setter or variable (`HECKE_RHO_SIMD`, `HECKE_DESCENT_SMITH_SIMD`, the validations' forced paths) still wins. `ENGINE_AVX2_PAIR=0` (or `off`) turns the AVX2 pair route (vpmaddwd, p ≤ 4096) off, so the AVX2 path runs its u64 microkernel for every p; a set value prints `EFFECTIVE ENGINE_AVX2_PAIR arm=<off\|auto> value= avx2_available= max_modulus=4096`. Gated by `KernelAvx2BitIdentityValidation`. |
| `ENGINE_TERNARY_F3=1` | **opt-in route, default off, cannot change a value** (slot-23 TER-1, ENGINE_API §8.3): exactly `1` (read once per process) routes every DenseElim RREF / `column_rank_profile` over the field `F_3` (`uint32_t`, `uint64_t`) to `engine::binary::TritMatrix` (bit-sliced Gauss–Jordan); `tape::rref` and `engine::blk` are not routed. `TernaryF3Validation` proves it entrywise; `GOLDEN_STRICT=1 ENGINE_TERNARY_F3=1 GoldenRegressionValidation` is clean. |
| `L23_TERNARY_F3=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `L23_TERNARY_F3=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 TER-1): the degree-1 amalgam reader's `F_3` route (`l23::h1_mod` at ℓ = 3, k = 1: `Ops3F`, byte kernels, the characteristic-3 Taylor shift, `TritMatrix` eliminations) is **on by default**; exactly `0` (read once per process) restores the `Ops3<1>` route. `TernaryF3Validation` (2) compares the two cell by cell; `L23AmalgamReaderValidation` and `OrbifoldCampaignL23Validation` pass under both. Any other value prints `WARNING l23: L23_TERNARY_F3='…' is neither 0 nor 1; the F_3 route stays ON` (audit F4); `deep_cell` (ℓ = 3 m2) and a verbose orbifold campaign print `EFFECTIVE l23_ternary_f3=on|off source=default|env|scoped`. |
| `L23_RING2K=0` | **a rollback arm, not an emitter, cannot change a value** (slot-23 Z2K): the (Z) phase of an ℓ = 2 orbifold census cell (Smith readings over `Z/2^31`, `Z/16`; the (U) kernel modules over `Z/16`) runs on `engine::ring2k` **by default**; exactly `0` (read once per process) restores `elim::invariant_factors` / `elim::kernel_module`. `OrbifoldRing2kValidation` compares the two on the coboundaries and on whole records. Any other value prints `WARNING campaign: L23_RING2K='…' is neither 0 nor 1; the ring2k route stays ON`; a verbose orbifold campaign prints `EFFECTIVE l23_ring2k=on|off source=default|env|scoped`. ℓ = 3 is never routed. **It switches only the orbifold (Z) phase: BIN-3's degree-1 amalgam reader (`l23::read_lattice` / `h1_mod`) stays on `engine::ring2k` whatever its value** (Z2K audit L4). |
| `L23_MOD3K=0` | **a rollback arm, not an emitter, cannot change a value** (slot-23 Z3K): the (Z) phase of an ℓ = 3 orbifold census cell (Smith readings over `Z/3^19`, `Z/9`; the (U) kernel modules over `Z/9`) runs on `engine::ring3k` **by default**; exactly `0` (read once per process) restores `elim::invariant_factors` / `elim::kernel_module`. `OrbifoldMod3kValidation` compares the two on the coboundaries and on whole records. Any other value prints `WARNING campaign: L23_MOD3K='…' is neither 0 nor 1; the ring3k route stays ON`; a verbose orbifold campaign prints `EFFECTIVE l23_mod3k=on|off source=default|env|scoped`. ℓ = 2 is never routed by it; it does not touch the degree-1 reader's `F_3` route (`L23_TERNARY_F3`). |
| `L23_F3L=0` | **a rollback arm, not an emitter, cannot change a value** (slot-23 F3L): by default `integral_model::rho_n` runs the O(d²) column recurrence (every caller, every context; the cubic double sum when neither `a` nor `c` is a unit) and an ℓ = 3 orbifold census cell runs under `engine::elim::ScopedTernaryF3(true)` (every F₃ RREF / rank profile on TER-1's `TritMatrix`); exactly `0` (read once per process) restores the O(d³) double sum and the engine PLU. `OrbifoldF3lValidation` compares the two on `rho_n`, `theta_hat` and whole records. Any other value but `1` prints `WARNING: L23_F3L='…' is neither 0 nor 1; the F3L route stays on`; a verbose orbifold campaign prints `EFFECTIVE l23_f3l=on|off source=default|env|scoped rho_n=recurrence|cubic ell3_f3_elim=ternary|engine`. |
| `L23_BIN3O1=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `L23_BIN3O1=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 BIN3O1): the degree-1 amalgam reader's BIN3O1 route (`l23::read_lattice` / `h1_mod` / `h1_layers` / `oddn_row`: the O(d²) Pascal relation matrix and B¹, the parity-split relation matrix for the rank over Q and for L, `ring2k::kernel_shift_rows` and run-grouped words in the Taylor shifts, `h1_mod` at ℓ = 2, k = 1 on F₂ / `BitMatrix`) is **on by default**; exactly `0` (read once per process) restores the old route. `L23Bin3o1Validation` compares the two entrywise. Any other value prints `WARNING l23: L23_BIN3O1='…' is neither 0 nor 1; the BIN3O1 route stays ON`; `deep_cell` and a verbose orbifold campaign print `EFFECTIVE l23_bin3o1=on|off source=default|env|scoped`, and (merge-time audit fix F1) after their last cell `BIN3O1_ROUTE route=… split=a/b odd= rankq= f2= reused= split_fallback= rankq_fallback= parity_fallback= fallback=` (`fallback=0` expected; the DEEP-1 kit's `run_shard.sh` stops a shard on a cell without `route=on … fallback=0`). It does not touch `L23_TERNARY_F3`, `L23_RING2K` or `L23_MOD3K`. |
| `CUDA_IMMA_ELIM_BENCH=m,n[,p]` (+ `CUDA_IMMA_ELIM_BENCH_CPU=1`, `CUDA_IMMA_ELIM_BENCH_ONLY=1`) | read-only, not an emitter: `CudaImmaElimValidation` arm (G), the timing of one random and one sparse `m × n` elimination (prints `EFFECTIVE CudaImmaElimValidation arm=bench …`; `_ONLY` skips arms A–F and fails on purpose). |
| `HECKE_CENSUS_SPLIT_CELLS=<file>` | read-only, not an emitter: `HeckeCensusSplitValidation` arm (D) over the listed cells (`<n> <ell> [<u_ell_budget_mb>]`, `#` comments, refusals by line number); wins over `HECKE_CENSUS_SPLIT_ALL=1` (printed). Census edition 2's W2 cells: `docs/implementation/slot12/WP-6_w2_cells.txt` (112 cells, ≈ 18 min, 4.6 GB; slot-12 WP-6). |
| `HECKE_THETA_IMAGE_CELLS=<file>` | read-only, not an emitter: `HeckeDicksonThetaHeckeValidation` (P5), the θ-image over the listed cells (records from `ext_first`, then `ext_census_l7l11`); wins over `HECKE_THETA_IMAGE_ALL=1` (slot-12 WP-6). |
| `HECKE_FORMS_CENSUS_ALL=1` / `HECKE_FORMS_CENSUS_CELLS="n:ell,…"` (+ `HECKE_FORMS_CENSUS_TSV=<census.tsv>`, default the tracked edition 1) | read-only, not an emitter: `HeckeFormsHeckeAlgebraValidation` arm (T), the forms-side `T_m/ell` against `A` on every non-reduced census row (the cell list wins; 655 rows of the staged edition 2 in 6 shards ≈ 3.5 min each, ≤ 7.2 GB; slot-12 WP-12). |
| `HECKE_FORMS_FINALITY_ALL=1` (+ `HECKE_FORMS_FINALITY_ELLS=7,11,13`) | read-only, not an emitter: arm (F), the boundary finality instance on the 184 heuristic `ell = 5` ideals (86 cells, ≈ 5 min, 1073 checks; the `ELLS` rows reported, not gated; slot-12 WP-12). Arm (F) also runs, unconditionally, at its two default cells `(26, 5)`, `(30, 5)` whenever `HeckeFormsHeckeAlgebraValidation` runs at all — **since slot-14 WP-2** it prints `[SKIP] (F): the TSV holds no heuristic rows` and does not fail when `HECKE_FORMS_CENSUS_TSV` names a TSV with none (edition 2, since every heuristic row there is `final = true`); before the fix this failed `HeckeFormsHeckeAlgebraValidation` outright (`[C4]` headline 5, the cluster's `forms_census_all` case, `HECKE_FORMS_CENSUS_ALL=1` against edition 2). |
| `HECKE_BOUNDARY_FINALITY_ALL=1` | read-only, not an emitter: `HeckeBoundaryFinalityValidation` (H), every `sturm_heuristic` row of `HECKE_FORMS_CENSUS_TSV` at `ell ∈ {5, 7, 11, 13}`, the certificate gated at every `ell` (edition 2: 376 / 376, 15 213 checks, ≈ 17 min; slot-12 WP-14). |
| `HECKE_CENSUS_LATTICE_ALL=1` / `HECKE_CENSUS_LATTICE_CELLS="n:ell,…"` (+ `HECKE_CENSUS_LATTICE_TSV=<census.tsv>`, default edition 2) | read-only, not an emitter: `HeckeCensusLatticeValidation`, C-F9 (the lattice test `m_A² = 0`) on every non-reduced census row, one `CENSUS_LATTICE` line each + `CENSUS_LATTICE_SUMMARY` (655 rows, 654 held, ≈ 52 min sharded, ≈ 30–40 GB summed; slot-13 WP-9). Through slot 13, `CELLS` alone did not enable the arm — it only filtered inside `_ALL`, so `CELLS` without `ALL=1` was a no-op (slot-14 [C3] §5 finding, the eleven `census_lattice_s0…s10` cluster shards). **Fixed by slot-14 WP-2**: `CELLS` alone now enables the arm as well, matching every other `_CELLS` row of this table; an `EFFECTIVE HeckeCensusLatticeValidation arm=ALL cells=<k>` line is printed whenever the arm runs. |
| `HECKE_HIDA_HEAVY=1` (+ `HECKE_HIDA_HEAVY_CELLS="n:ell:m,…"`, default `100:691:1,200:691:1,400:691:1,700:691:1`) | the interlock on a *run*, like `HECKE_LOCALITY_PROBE`: without it `HeckeHidaHeavyCellProbe` prints `[SKIP]` even under `--all-full`. Read-only, not an emitter; `(700, 691)` at `m = 1` peaks ≈ 13.7 GiB (61 s), at `m = 2` ≈ 33.5 GiB (47 min) — **predict RSS first, rule 19** (slot-13 WP-10). **Since slot-14 WP-2** a listed cell at `ell ∈ {691, 2411}` with `n ≡ 10 (mod ell − 1)` also gets a reported `HI11` / `HI12` line, `HELD` / `FAILED` against the `n = 10` class reference. That reference is computed in the same process, once per `ell`, by the `m = 1` field route. Before WP-2 only the literal point `(700, 691)` was compared. |
| `ORBIFOLD_MP_CELLS=4,6` (or `4`, `6`, `all`) | read-only cell hook (slot-22 MP-1b, R3): `OrbifoldMPNerveValidation` adds the nerve-`H^2` cells `n ∈ {4, 6}` (`ℓ ∈ {2, 3, 5}`, `M7` and `R_Z`; 12 cells), gated against the frozen `mv_check.out` rows, and prints `EFFECTIVE OrbifoldMPNerveValidation arm=h2 cells=<k> n=<list>`; any other token is `REFUSED` (exit 1). Measured before registration (`MP_predictions.md`, "R3 measurement"): +5 s, RSS unchanged (≈ 260 MB). Never an emitter, never changes a value. |
| `HECKE_MIXED_FINALITY_CELLS="n:ell,…"` | read-only, not an emitter: `HeckeMixedFinalityValidation`'s scan hook over the listed cells (the `ell = 7`, `n ≤ 400` probe: 45 min, 19.3 GB summed over four shards; slot-13 WP-11). |
| `HECKE_PRECISION_REUSE=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_PRECISION_REUSE=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **rollback arm, cannot change a printed value** (slot-23 G1, [C, obl:precisionreuse](v)): the saturation / Loewy cells (`ComputeSaturationDefectCell`, `ComputeRingLoewyCell`) run the module route once per level read (the per-K route, the oracle) instead of once per cell with the lower levels derived. Only exactly `0` selects it (any other value warns and stays derived). When set, the first cell prints `EFFECTIVE HECKE_PRECISION_REUSE levels=per_K (HECKE_PRECISION_REUSE=0)`; the cells of the `HECKE_SAT_DEFECT_CELLS` arm print `SAT_DEFECT_LEVELS … Lv_run= mode=per_K:rollback(…)` (the default arm prints no such line); the `hecke_ring_algebra` record carries `Lv_run` and `level_mode`. Cost: (300, 7) 352 s vs 68 s derived, (300, 11) 155 s vs 89 s (`G1_report.md`). |
| `HECKE_FORMS_FASTMUL=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_FORMS_FASTMUL=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **rollback arm, cannot change a value** (slot-23 G2-X): the forms module's q-series product (`forms::MulSeries`: by default NTT over 5·2²⁵+1, 7·2²⁶+1 + CRT, the delayed-reduction schoolbook below min length 64 or N < 1024) and the E₄ / E₆ divisor sums (by default a sieve) run the O(N²) routes through slot 23 instead. Only exactly `0` selects them (any other value warns and stays fast). When set, the first product of the process prints `EFFECTIVE HECKE_FORMS_FASTMUL mul=naive (HECKE_FORMS_FASTMUL=0)`. Cost: the sat route's forms stage at (300, 1009) 261.8 s vs 1.6 s fast; the whole cell 583 s vs 329 s (`G2X_report.md`). |
| `HECKE_FORMS_NTT_CACHE=0` | **rollback arm, cannot change a value** (slot-24 FNTT): `BuildCuspSpace` / `BuildModularSpace` / `HeckeOnCusp` run the G2-X code verbatim instead of the FNTT route (cached spectra, one pass for M_k, no Dpow / Epow tables, blocked AVX2 butterflies, delayed-reduction elimination). Only exactly `0` selects it (any other value warns and stays on). When set, the first space prints `EFFECTIVE HECKE_FORMS_NTT_CACHE route=legacy simd=… (HECKE_FORMS_NTT_CACHE=0)`. Under it a space with ℓ ≥ 2¹⁶ and N ≥ 1024 is refused (`FormsSpaceSupported`: the only other route would be the O(N²) naive one). Cost: (1000, 10007) forms stage 283 s / 1778 MiB vs 53 s / 745 MiB (`FNTT_report.md`). |
| `HECKE_FORMS_NTT3=0` | **rollback arm, cannot change a value** (slot-24 FNTT3): removes the three-prime chunked forms route (P₃ = 45·2²³+1, Garner CRT), i.e. restores the FNTT refusals — `FormsSpaceSupported` false, `BuildCuspSpace` / `BuildModularSpace`'s `ENGINE_CHECK`, the sat pre-run refusal and the `HECKE_SAT_DEFECT_CELLS` parser's — for every space with ℓ ≥ 2¹⁶, N ≥ 1024 past the two-prime bound (N(ℓ−1)² ≥ P₁P₂ or 2N − 1 > 2²⁵), e.g. (1000, 100003). No other space changes route either way (the three-prime route runs only where the space was refused before). Only exactly `0` selects it (any other value warns and stays on). When set, the first space or support query of the process prints `EFFECTIVE HECKE_FORMS_NTT3 three_prime=off (HECKE_FORMS_NTT3=0)` (since the audit fix F6 also when every space is two-prime). Cost: none (refusals are immediate); with it on, (1000, 100003)'s forms stage is predicted 7.4–8.3 GB (`FNTT3_predictions.md` §4). |
| `HECKE_FORMS_FASTMUL_CELLS="n:ell[:naive\|:legacy],…"` | read-only, not an emitter: **replaces** `HeckeFormsFastMulValidation`'s arms by the sat route's forms stage alone per cell (time, VmHWM; `:naive` also runs and compares the naive route; `:legacy`, slot-24 FNTT, the G2-X route with the FNTT route off); prints `EFFECTIVE HeckeFormsFastMulValidation arm=HECKE_FORMS_FASTMUL_CELLS cells=<k>`. (1000, 10007) ≈ 0.75 GiB on the FNTT route (≈ 1.7 GiB on the G2-X route). |
| `HECKE_RING_LOEWY_CELLS="n:ell[:KMAX],…"` | read-only, not an emitter: `HeckeRingLoewyValidation` runs the `Z/ell^K` Hecke-algebra route (`HeckeExt/HeckeRingHeckeAlgebra`, slot-14 WP-6) over the listed cells. `KMAX` defaults to 7 at `ell = 7` and 6 otherwise. It prints `LOEWY_RING`, `LOEWY_RING_SUMMARY`, `LOEWY_RING_CELL`, `LOEWY_RING_REFUSED` and `HECKE_RING_LOEWY_EFFECTIVE cells=<k>` lines. C-F9 failures are **reported** as `LOEWY_RING_CF9_FINDING` and never gated. The shard / collate driver for cluster data is `docs/implementation/slot14/wpc14/loewy_collate.sh`. |
| `HECKE_LEVEL_N_R3_CELLS="N:p:dimH1:dimW:loewy:merel,…"` (or bare `N:p`; + `HECKE_LEVEL_N_R3_ROUTE=sparse\|model`, `HECKE_LEVEL_N_R3_QMAX=<q>`) | read-only, not an emitter: **replaces** `HeckeLevelNValidation`'s (R3) list (Mazur's Eisenstein ideal at weight 2 over `F_p`, `p ∤ N`). Every cell is validated first: `N` prime, `p ≥ 5` prime, `p \| N − 1`, six or two integer fields. A bad cell is refused by its position, through `[EXCEPTION]` / `[FAIL]`. **Since slot-15 WP-9 every hook cell runs on the sparse route** (`Hecke/HeckeLevelNR3`, ≤ 1.1 s / 180 MB per cell at `N ≈ 10^4`): a six-field cell **gates there only** (the slot-14 model route only under `_ROUTE=model`); a bare `N:p` is a **reading** ((LN4)–(LN6) reported, never gated) and, under `_ROUTE=model`, **refuses the whole list**. `_QMAX` (default 7) widens `W`'s Hecke primes to every prime `q ≤ QMAX`. The `EFFECTIVE HeckeLevelNValidation r3_cells=<k> route=<r> qmax=<q>` line is printed. On the model route `(1321, 11)` takes 26 s / 4.1 GB and `(1571, 5)` 40 s / 5.7 GB (slot-14 WP-12, review M-6). |
| `HECKE_LEVEL_N_SPARSE_CELLS="N:n:p,…"` | read-only, not an emitter: replaces `HeckeLevelNSparseValidation`'s ladder (arm (C): the sparse cokernel, every `H_{N,q}`, the cost model; `N < 2^20`, `n` even, `p ≥ 5` prime; slot-15 WP-8). Prints `EFFECTIVE HeckeLevelNSparseValidation arm=CELLS cells=<k>` and one `SPARSE_CELL` line per cell (since slot-17 WP-5 with `level_wide_products=`, the `__int128` escalations of the cell's coset products; composite `N` beyond `5.5·10^4` runs since WP-5, e.g. `60060:2:17` 2.57 GB / 157 s). **Since slot-17 WP-8** strict parsing (an empty value, an empty cell or field, a non-decimal field throws by position) and a pre-run RSS refusal. **Since slot-17 WP-17** that refusal uses the calibrated `hook_rss/v1` (`512 MiB + factor × sparse_bytes`; factor 64 in the W5-F1 regime, 16 at `n = 0`, 4 at `n ≥ 2`), so `99330:0:13` and `90090:2:17` are refused at the default 8 GiB. `HECKE_LEVEL_N_HOOK_RSS_CAP_GIB` overrides the cap, and the `EFFECTIVE` line names the cap and its source. |
| `HECKE_HIDA_COMPONENTS_CELLS="n:ell[:K],…"` | read-only, not an emitter: `HeckeHidaComponentsValidation` runs the [U] (U1)–(U3) readings over the listed cells (`K` defaults to 3; slot-15 WP-6). Prints `EFFECTIVE HeckeHidaComponentsValidation arm=CELLS cells=<k>`, one `HIDA_COMPONENT` line per cell, `HIDA_INTRA` per `g = 2` block. `"282:37:3,226:103:3"` (the `L = 2` cells) takes 105 s / 0.49 GB. |
| `HECKE_DUMP_TAU=<dir>` | **an emitter into scratch** (slot-16 L16-4, Lean Q14): `HeckeTauDumpValidation` (`fast`) writes exactly `tau_p2.txt`, `rho_n2_ell5.txt`, `rho_n10_ell691.txt`, `rho_n16_ell13.txt` into `<dir>` — the `p = 2` τ table and three `ρ_n` sets the Lean checkers (`lean/GL2/Checkers/`, `tau_dump_to_lean.py`) read. `<dir>` must exist and must **not** lie inside the source tree (`realpath` against `OC_SOURCE_DIR`; otherwise `REFUSED`, exit 1). Unset: `[SKIP] … HECKE_DUMP_TAU not set`, exit 0 — so `--all` stays read-only. Prints `EFFECTIVE HeckeTauDumpValidation arm=DUMP cells=3` and one `TAU_DUMP` line per file (the τ line carries the golden hash `tau_table_fnv64_p2_r1`). Builds only objects the golden harness builds; no record, golden or setting. |
| `HECKE_DUMP_TAU_RHO_CELLS="n:ell,…"` | read-only (slot-17 L17-4 repair), meaningful only with `HECKE_DUMP_TAU`: replaces `HeckeTauDumpValidation`'s three default ρ cells by the list (the 31 golden `ext cone_action` points for `lean/tools/rho_grid_to_lean.py` → `GL2/Checkers/RhoGrid/`, [GT] `orc:rhogrid`). Strict: decimal `n ≤ 1000`, `5 ≤ ell < 2^32`, no duplicate, no empty cell (set-but-empty and a trailing comma included); the first bad cell is `REFUSED` by its 1-based position, exit 1. Prints `EFFECTIVE HeckeTauDumpValidation arm=RHO_CELLS cells=<k>`. Unset: byte-identical to the default arm. 31 cells: 558 matrices, 544 KB, < 1 s. |
| `HECKE_DUMP_TAU_PAIR="p:nu,…"` | read-only selection (slot-18 L18-3), meaningful only with `HECKE_DUMP_TAU`: for each `(p, ν)` additionally builds the golden recipe's certified τ, `τ_∂` and η (`HeckeCosetTables(p, ν, ell, 2)`, `ell = 5`, or 13 at `p = 5`; `u_ell` off, as `GoldenHarness` `RunExtTauCell`) and writes `tau_p<p>_r<ν>.txt`, `taubd_p<p>_r<ν>.txt`, `eta_p<p>_r<ν>.txt` into the same scratch directory (for `lean/tools/taubd_eta_to_lean.py` → `GL2/Checkers/PairData/`, [GT] `chk:taubd-p2`, `chk:eta-p2`, `chk:pairgrid`). Each `TAU_DUMP` line prints the table's `HashScalar64` (= the golden `tau_table_fnv64_*` / `tau_bd_table_fnv64_*` / `eta_table_fnv64_p2_r1`). Strict: `p` prime `≤ 97`, `1 ≤ ν ≤ 2`, no duplicate, no empty entry; the first bad entry is `REFUSED` by its 1-based position, exit 1. Prints `EFFECTIVE HeckeTauDumpValidation arm=PAIR tables=<k>`. Unset: byte-identical to the default arm. The six grid pairs `2:1,3:1,5:1,7:1,2:2,3:2`: 18 extra files, < 1 s. |
| `HECKE_DUMP_MEREL=<dir>` | **an emitter into scratch** (slot-20 L20-4, ruling O9; no read-only arm printed the Heilbronn–Merel data): with it set, `HeckeLevelNValidation` runs **only** the dump and writes `merel_N5_n2_p2.txt` and `merel_N5_n2_p5.txt` into `<dir>` — the C++ `HeilbronnOperator` (`T_2^{(5)}`, `U_5^{(5)}` at the validation's own cell `(N, n) = (5, 2)`, over `F_1000003`): the `def:cosetrepsN` table, `Mer_p`, every term `(j·ε, j, adj h_j(ε), ρ_n block)` in the operator's order, and the dense `D × D` matrix, for `lean/tools/merel_dump_to_lean.py` → `lean/GL2/Checkers/MerelData.lean` ([GT] `chk:merel-n5`). `HECKE_DUMP_TAU`'s rules: `<dir>` must exist and must **not** lie inside the source tree (`realpath` against `OC_SOURCE_DIR`; otherwise `REFUSED`, exit 1). Unset: one `  [SKIP] MEREL_DUMP: HECKE_DUMP_MEREL not set` line and the validation runs unchanged — so `--all` stays read-only. Prints `EFFECTIVE HeckeLevelNValidation arm=MEREL_DUMP cells=2 validation_arms=skipped` (the validation's own arms do not run when the variable is set) and one `MEREL_DUMP` line per file, ending in `dense_fnv64=0x…` (slot-20 L20-6, F3-20 MINOR 7 / 8: FNV-1a-64 via `Fnv.h` of `D` and the dense entries row-major, one 64-bit word each; recomputed by `merel_dump_to_lean.py` into `MerelData.lean`'s docstrings; `0x029f2ae7b5c322c1` for `p = 2`, `0xa321b63a9401bf42` for `p = 5`). No new registered name; < 1 s, 2 files, ≈ 7 KB. |
| `HECKE_NEBENTYPUS_CELLS="N:chi:k:ell[:d][:route=dense\|sparse\|auto][:K=1\|2\|3],…"` | (slot-18 WP-6: the optional `K=` field runs the cell over `W_K(F_q)` on the sparse Howell route against the `F_q` sparse route — `K = 1` entrywise, `K ≥ 2` the generator count and freeness at `χ ≠ 1`; it excludes `route=`; RSS model `30 × sparse_bytes`, refused above 8 GiB; one `NEB_WK_CELL` line; the `EFFECTIVE` line counts `wk_sparse_K<k>`.) (slot-17 WP-6: the optional `route=` field, default `auto` = dense iff `D ≤ 4096`, sparse above; a dense cell above the cap stays `refused=neb_dense_cap`; a cell whose RSS model exceeds 8 GiB is `refused=rss_model` before the run; the `EFFECTIVE` line gains `route=<dense:a,sparse:b>`, each `NEB_CELL` line `route=`, `pred_rss_mib=`, `ops_fnv=`, `wall_s=`, `peak_rss_mib=`; beyond `h1 = 1500` the operators are checked on generators and 32 sampled vectors, charpolys printed only at `h1 ≤ 400`.) read-only, not an emitter (slot-16 WP-10; `chi` is the Conrey index `m` of `N.m`): **replaces** `HeckeNebentypusValidation`'s default arms. Each cell is validated first (whole decimal fields, `N < 2^20`, `m < N` a unit, `2 ≤ k ≤ kNebDenseCap + 1`, `ell ≥ 5` prime `< 2^31`, `ell ∤ N`, `d ≤ 64`); an empty / separator-only value or a malformed cell throws by position (`[EXCEPTION]` / `[FAIL]`), and a list in which no cell ran fails. Per cell the cokernel route over `F_{ell^d}` (`d = d(χ)` unless given): (NB1) and commutativity gated, one `NEB_CELL` line with `h0`, `h1` and the charpolys of `T_2, T_3, T_5, T_7` (`U_p` at `p \| N`); a designed refusal (`field_too_large`, `character_wild`, `character_field`, `neb_dense_cap` at `D = m_N(n+1) > 4096`) is reported `refused=<code>` and counted in `NEB_CELLS_SUMMARY`, not failed. Prints `EFFECTIVE HeckeNebentypusValidation arm=CELLS cells=<k>`. |
| `HECKE_NEBENTYPUS_F1_RING=first\|all`, `HECKE_NEBENTYPUS_F1_PMAX=<23..199>` | read-only, not emitters (slot-16 WP-10/11 audit repairs): `HeckeNebentypusValidation`'s F1 arm. `F1_RING` adds the certified `Z/ell^K` route (`T'_m/ell = F[x]/x²`, [C] `cor:stablecert`(1); ≈ 30 s per cell) at `(220, 17)` (`first`) or also `(246, 19)` (`all`); `F1_PMAX` widens the full-algebra reading from `T_p`, `p ≤ 23` (default, gated) to every `p ≤ PMAX`. Any other value throws. Each prints its `EFFECTIVE … arm=F1_RING cells=<k>` / `arm=F1_PMAX pmax=<p>` line. `F1_RING=all F1_PMAX=97`: 2438 checks, 260 s. |
| `HECKE_NEBENTYPUS_NB3_ROUTE=dense\|sparse\|auto` | read-only, not an emitter (slot-17 WP-6): the route of the character models in `HeckeNebentypusValidation`'s (NB3) arm (default dense, as shipped); prints `EFFECTIVE HeckeNebentypusValidation arm=NB3_ROUTE cells=<k> route=<r>`; any other value throws. With `_NB3_FULL=1` and `sparse`: the 132 cells read the same verdicts as on the dense route. |
| `HECKE_LVALUE_HEAVY=1` | read-only (slot-19 WP-LV2): `HeckeLValueValidation` adds the twisted cells `(4, ω^40)` at 59, `(4, ω^54)` at 67 and the deep rungs `(282, 37)`, `(226, 103)` (`v(B_k/k) = 2`; `f^- = 1`, saturated, `#Q_m = ℓ^{min(m,2)}`; no ℓ-torsion in `H^1` there); `EFFECTIVE HeckeLValueValidation arm=HEAVY cells=4`. **657 checks, 419 s, 0.98 GB** (WP-LV2); since slot-19 WP-LIN it also runs the Birch heavy cell `(258, 37)` over `Z/37^2` and G3 at `(72, 37)` (`EFFECTIVE … arm=HEAVY_BIRCH cells=1`): **936 checks, 505 s, 1.2 GB**. The twisted rung `k = 62` at 37 is NOT in it (> 7.3 GB, killed by a 6 GB watchdog). Since slot-20 WP-LV3 it also runs the depth-2 cross-kind on [C]'s `H^1` and the C++ cone and `ι^*` over `Z/37^3` at `(282, 37)`: **1614 checks, 729 s, 1.55 GB**. |
| `HECKE_LVALUE_HEAVY=twist62` | read-only (slot-20 WP-LV3): `HeckeLValueValidation` runs (after its default arms) only the twisted depth-2 rung `(37; ω^6, 62)` (`n = 60`, character model `H^1(Γ_0(37); V(ω^6))` over `Z/37^4`, `v = 2`, `f^- = 1`); `EFFECTIVE HeckeLValueValidation arm=HEAVY_TWIST62 cells=1`. **1506 checks, 26 333 s (7 h 19 min), 16.4 GB peak** (predicted 17.5 GB / 7.3 h from the curve at `n = 20, 40`; `#Q_m = 37^{min(m,2)}`). Run under a 22 GB watchdog only. |
| `HECKE_LVALUE_CELLS="n:ell[:j],…"` | read-only cell hook (slot-19 WP-LV2, R19-7's request): `HeckeLValueValidation` runs each cell (level one, or the character model `χ = ω^j` at level `ℓ`), torsion-aware, `m = 1..3`, prints `LVALUE_HOOK_CELL` / `LVALUE` lines and gates only `holds` of the index statement; a malformed list is one failing check. `EFFECTIVE HeckeLValueValidation arm=CELLS cells=<k>`. Cost per cell as in the arms (seconds at `n ≤ 60`, level one; ~ 250 s at `n = 282`; the character model above `n ≈ 40` at 37 can exceed 6 GB — predict RSS first). |
| `NUMBERFIELD_LAYER_ALL=1` | read-only (slot-19 WP-NF2): `NumberFieldValidation` part (9e) adds R19-7's heavy gates — 691 level 2 (five classes, sha `1cc99c56e175f32f`, **3455 / 3455** rows, 342252 / 342440), 103 level 3 (sha `71ca74ef9863f524`, **914250**), 37 level 4 (sha `91277ba0d2e2defe`, **1072544**, `α ≡ 281570`), each again with the lean parameters `r = m, W = 4m − 1` (same rows); 160 more checks, ≈ 55 s at 8 threads, 0.2 GB. `EFFECTIVE NumberFieldValidation arm=LAYER_ALL cells=6`. |
| `NUMBERFIELD_LAYER_CELLS="ell:m:w1/w2[:r[:W[:bern]]],…"` | read-only cell hook (slot-19 WP-NF2): the Coates–Wiles layer route at any `(ℓ, m)` and classes; a `NUMBERFIELD_CWLAYER_PREDICT` line (fitted wall, planned peak) precedes each run; checks integrality, the `Δ^m` law, the exact Bernoulli / Kummer-law rows, rows mod `ℓ²` against R19-7's level-2 JSON, the depth-`m` rung and `α` where known, the level-`(m−1)` control; a malformed entry is refused by position (one failing check). `EFFECTIVE NumberFieldValidation arm=LAYER_CELLS cells=<k>`. **The 691 level-3 run is `"691:3:12/200:3:11"`: ≈ 32 GB, ≈ 1.2–1.5 h at 8 threads — predict RSS first, rule 19** (`docs/implementation/slot19/wpnf2/README.md`). Threads: `ENGINE_THREADS` (values never depend on it). |
| `HECKE_LVALUE_BILINEAR_HEAVY=1` | read-only (slot-19 WP-BIL): `HeckeLValueValidation` adds the (G1) model gate at `(258, 37)` (`n ≥ ℓ`): the C++ `PoincareDualityPairing`'s `gram(1) == −⟨Ψ, y(v4v6)⟩` on the 43 × 43 stored bases and the route reproduces it; `EFFECTIVE HeckeLValueValidation arm=BILINEAR_HEAVY cells=1`. **+5 checks, +13 s, 0.86 GB peak.** |
| `HECKE_NEBENTYPUS_NB3_FULL=1` | read-only, not an emitter: `HeckeNebentypusValidation`'s (NB3) arm over the **full committed grid** of [C] `rmk:nebcheckable`, `n = 0 … 10` at all 12 `(N, ell)` pairs, **132 cells** (the default runs 79); `EFFECTIVE HeckeNebentypusValidation arm=NB3_FULL cells=132`; any value other than `1` throws. **3808 checks, 947 s, 6.5 GB peak** — too slow for `standard`. **Owner ruling 2026-10-01: run at EVERY slot close** (a close-window step since `slot16_close_window.sh` step 6). |
| `HECKE_SAT_DEFECT_CELLS="n:ell[:KMAX],…"` (+ `HECKE_SAT_DEFECT_STRICT=1`) | read-only, not an emitter (slot-16 WP-5 + audit repairs): `HeckeSaturationDefectValidation` over the listed cells (`KMAX` defaults to 6, lowered while `ell^KMAX ≥ 2^64`; `n` even in `[2, 2^20]`, `ell` prime in `[5, 2^31)`, `KMAX` in `[2, 64]`; a bad cell refused by position, a set-but-empty value fails). One `SAT_DEFECT` line per block with the census-3.1 columns `sat_defect_dim`, `sat_defect_loewy`, `sat_length_col`, `SAT_DEFECT_REFUSED` per refused block, one `SAT_DEFECT_CELL` per cell, `SAT_DEFECT_SUMMARY`, and after the run `EFFECTIVE HeckeSaturationDefectValidation arm=CELLS cells=<k> refused_cells= blocks= ok= torsion_refused= not_stable= strict= expectations=<held>/<k>`. Torsion blocks are refused by design and pass; a cell with no ok block fails unless all its blocks are torsion refusals; `not_stable_at_KMAX` is reported and passes, **and fails under `STRICT=1`** (census shards set it). The hidden-chain cells `(220, 17)`, `(238, 17)`, `(246, 19)` and the `ell = 37` Kummer cells `(258\|294\|296\|334, 37)` are gated against hard-coded expectations when listed (`SAT_DEFECT_EXPECT`). ≤ 0.7 GB, 0.4 s … 5 min per cell at `n ≤ 400`, steeply more beyond. |
| `HECKE_FORMS_CENSUS_U_ELL=<mb>`, `HECKE_FORMS_CENSUS_RECORDS=<dir[:dir…]>` | read-only, not emitters (slot-16 WP-3 + audit repairs): `HeckeFormsHeckeAlgebraValidation` arm (T) — and arm (I) of `HeckeBoundaryFinalityValidation` — now take each cell's `u_ell` budget from the rows' **source set** (`HeckeExt/HeckeCensusJoin.h`: np / npx sets 16384, `ext_u691` 8192, `ext_first` / `ext_census_l7l11` `auto`; an unknown or mixed set is refused by TSV line number, never run at the default). `_U_ELL` overrides every cell (and waives the unknown-set refusal). `_RECORDS` names the record roots (default the tree's `docs/matrix-engine/results`) for the **join by eigen-system** (`D == module_D`, the witness polynomial, `U_ell` present in the re-run iff in the record, the record's split system); an explicit list naming no root or a missing directory fails, as does one under which every row fell back. Lines: `FORMS_CENSUS_U_ELL n= ell= u_ell= u_ell_operator=present\|absent` per cell, `FORMS_CENSUS_REFUSED … reason=…`, `FORMS_CENSUS_SKIPPED … reason=residue_degree_<f>` (rows of residue degree `f > 1`, not failed), `EFFECTIVE … arm=T cells=<k> u_ell=<override:…\|source_set{…}> refused=<k> skipped=<k> join=system:<a>,witness:<b>,fallback:<c>,refused:<d> records=<roots>`. A census shard must read `refused=0` and `fallback:0`. |
| `HECKE_CENSUS_LATTICE_U_ELL=<mb>`, `HECKE_CENSUS_LATTICE_RECORDS=<dir[:dir…]>`, `HECKE_CENSUS_LATTICE_JOIN_ONLY=1` | read-only, not emitters (slot-16 WP-3 + audit repairs): the same `u_ell` rule and override for `HeckeCensusLatticeValidation`'s arm (ALL / CELLS), and the join **by eigen-system, never by id** (the slot-15 `(654, 37)` ids 17 / 18 merge is gone): the record's split must match exactly one re-run ideal with every split prime a re-run operator (else `CENSUS_LATTICE_REFUSED … reason=join:operator_set:record=[…],rerun=[…]`), `f > 1` / record-less rows join by `(ideal_id, witness_poly, module_D)` uniquely (`CENSUS_LATTICE_FALLBACK`, counted). `JOIN_ONLY=1` runs the driver, blocks, eigenvalues, signs, Loewy lengths and the join only (`CENSUS_LATTICE_RERUN_IDEAL` lines, `arm=JOIN`; `(654, 37)` 99 s / 6.4 GB against 6.8 h for the full cell) — the cheap pre-flight of every lattice case (the October kit's PF37). `EFFECTIVE HeckeCensusLatticeValidation arm=ALL\|JOIN cells=<k> operators=with_U_ell:<a>,without_U_ell:<b> u_ell=<…> join=system:<a>,witness:<b>,refused:<c>,fallback:<k> records=<roots>`; one `CENSUS_LATTICE_OPERATORS` line per cell, `CENSUS_LATTICE_JOIN` per row. A malformed `CELLS` token is refused by position; a `CELLS` list selecting no row fails. |
| `HECKE_LEVEL_N_DEGEN_CELLS="M:N:d:n:p,…"` | read-only, not an emitter (slot-16 WP-13 + WP-17 repairs): replaces arm (G)'s list of `HeckeLevelNSparseValidation` (`α_d` at scale on the sparse route: `D(Rel_M) ⊆ Rel_N` on every generator, Hecke equivariance and the trace `prop:degenpres`(5) on 32 sampled vectors; one `DEGEN_CELL` line each). `N, M, d < 2^20`, `dM \| N`, `n` even `< 200`, `p ≥ 5` prime; every field a digit string, an empty value / cell / field refused by position; a cell whose predicted peak RSS exceeds the cap is refused **before** the run (rule 19). Since slot-17 WP-17 the prediction is `hook_rss/v1` on `M` + `N`: factor 64 in the W5-F1 regime, 16 at `n = 0`, 6 otherwise, plus 512 MiB. The cap is 8 GiB, or `HECKE_LEVEL_N_HOOK_RSS_CAP_GIB`. `EFFECTIVE HeckeLevelNSparseValidation arm=DEGEN cells=<k> rss_cap_gib=… rss_cap_source=… rss_model=hook_rss/v1`. `α_2`: `15015 → 30030` at `n = 2` (`D_N = 290 304`): 3.14 GB, 74.5 s. |
| `HECKE_LEVEL_N_R3K_CELLS="N:p:k,…"` | read-only, not an emitter (slot-16 WP-13 + WP-17 repairs): replaces arm (L9)'s list — (LN9), the `R3_k` Eisenstein reading at weight `k` (`ReadEisensteinR3k`: the joint generalised eigenspace of `H_{N,q}` at `1 + q^{k−1}`, `q ≤ 7`, `q ∤ Np`, with its Loewy layers), **reported, never gated**. `N < 2^20`, `5 ≤ p < 2^21` prime, `p ∤ N`, `k` even in `[2, 200)`; same strict parsing and pre-run refusal as `DEGEN` (`hook_rss/v1`, factor 16 at `k = 2`, 6 otherwise, since slot-17 WP-17). `EFFECTIVE HeckeLevelNSparseValidation arm=R3K cells=<k> rss_cap_gib=…`. |
| `HECKE_LEVEL_N_HOOK_RSS_CAP_GIB=<G>` | read-only, not an emitter (slot-17 WP-17, WP-8 audit MINOR-2): the pre-run RSS cap of the `HECKE_LEVEL_N_SPARSE_CELLS`, `_DEGEN_CELLS` and `_R3K_CELLS` hooks, in whole GiB in `[1, 1024]` (default 8). A malformed value throws (`[EXCEPTION]` / `[FAIL]`). It exists to run a refused cell **deliberately** in an exclusive window, such as slot 18's `90090:2:17`, which is predicted at 9622 MiB. It is named on every hook's `EFFECTIVE` line (`rss_cap_source=HECKE_LEVEL_N_HOOK_RSS_CAP_GIB`). Predict RSS first and keep the watchdog (rule 19). |
| `HECKE_LEVEL_N_GEN_ORDER=as_built` | **RETIRED 2026-10-30 (S24 CL-G2, owner ruling 2)**: in the default build (`OC_ENABLE_LEGACY=OFF`) `as_built` is **refused** at the first elimination (`REFUSED HECKE_LEVEL_N_GEN_ORDER=as_built: compiled out (OC_ENABLE_LEGACY=OFF)`, stderr, exit 1); `sorted` and unset are the one route; any other value throws (`[EXCEPTION]`). With `OC_ENABLE_LEGACY=ON` it is the old read-only rollback arm (slot-18 WP-5 (b), `Hecke/legacy/HeckeLevelNGenOrderLegacy.inc`): `SparseCokernel` consumes its generators in the slots 15–17 order (every `S` generator, then every `ST` one) instead of the `sorted` order (largest column, descending). Value-free: the stored RREF is unique; only `merge_ops`, `peak_nnz`, `occ_entries` and the wall time change. The `SPARSE_CELL` lines and the hook's `EFFECTIVE` line print `gen_order=`. |
| `HECKE_LATTICE_MODULE_FULL=1` | read-only, not an emitter (slot-19 WP-LC): `HeckeLatticeModuleValidation`'s full arm. `(258, 37)` at `K = 4` with **every prime `p < 100`** (`chk:latcmp` (e) in full: 25 / 25 `T_p = Q_p(t)`), plus independent module runs at `K = 2, 3` (T_2, T_37) compared with the `K = 4` run reduced. The `ℓ = 7` controls are also run at `K = 2, 3`. 585 checks, ≈ 22 min, ≈ 2.9 GB (the `K = 4`, 25-prime run). Prints `EFFECTIVE HeckeLatticeModuleValidation arm=FULL cells=4`. |
| `HECKE_LAMBDA_ALL=1` | read-only, not an emitter (slot-19 WP-HL): `HeckeLambdaValidation` adds the 691 classes — `(691, 12)` (`forms_691_12.json` and `lambda_691_12.json` reproduced) and `(691, 200)` (`lambda_691_200.json`; its 5 MB forms file is not tracked) — and the 9 catalogue rows at 691 (753 / 753). 224 checks, ≈ 400 s on a loaded box, ≈ 0.15 GB peak RSS; all four `LAMBDA_ORACLE … IDENTICAL`, 42 record lines. Prints `EFFECTIVE HeckeLambdaValidation arm=ALL cells=4`. |
| `HECKE_LAMBDA_CELLS="ell:a:K:m,…"` | read-only, not an emitter (slot-25 H1): `HeckeLambdaValidation` **replaces** its default arms (after the self-tests) by the truncation of the Eisenstein component at each listed irregular pair (N = K + m − 1 weights, forms data mod ℓ^{K+N−1}); [U] part 6's readings, at (547, 486) the data (D1), (D3) and the rung prediction (U23). `547:486:3:3`: ≈ 85 s, ≈ 95 MiB, 43 checks. Prints `EFFECTIVE HeckeLambdaValidation arm=CELLS cells=<k>` and `HECKE_LAMBDA_CELLS cells=… verdict=OK`. |
| `HECKE_HIDA_EIS_ALL=1` | read-only, not an emitter (slot-25 H1): `HeckeHidaEisLambdaValidation`'s (B) on every C2 chain weight, (198, 691), (700, 691) and (D2) at (484, 547). Prints `EFFECTIVE HeckeHidaEisLambdaValidation arm=ALL cells=<k>`. |
| `HECKE_HIDA_H2_ALL=1`, `HECKE_HIDA_H2_PROBE=1` | read-only, not emitters (slot-26 Z6): `HeckeHidaDiscLambdaValidation`; `_ALL` adds the held-out weights at 349 and 479, the known answer (547, 486) and the rung check at ℓ ∈ {67, 71, 73}; `_PROBE` replaces the arms by the two-job serial cost probe (no gate). Prints `EFFECTIVE HeckeHidaDiscLambdaValidation arm=<ALL|PROBE> cells=<k> …`. |
| `HECKE_XHOM_CELLS="N:n:p1/p2,…"` | read-only, not an emitter (slot-26 Z3b): `HeckeZCrossedHomOracleValidation` **replaces** its eight cells (n even, every p ∤ N); floors and the pinned counts (`tor_units=28 units_23=15 nonzero_23 ≥ 4`) are printed, not asserted. Prints `EFFECTIVE HeckeZCrossedHomOracleValidation arm=cells cells=<k>`; a refused value (p not prime, p ∣ N, malformed) prints `… cells=0 refused` and fails (exit 1). `11:2:2/3,13:4:2/3`: 0.4 s, 109 checks (127 with slot-27 Z3b-F's (Tau) arm). |
| `HECKEZ_EXW_ALL=1`, `HECKEZ_EXW_CELLS="N:n:alg,…"` | read-only, not emitters (slot-27 EXW): `HeckeZExportWordValidation` **replaces** its nine arms by the 22 pending records of edition 3 built with EXW on (`_CELLS` restricts to the named ones among them). Prints `EFFECTIVE HeckeZExportWordValidation arm=all cells=<k>` and `HECKEZ_EXW_ALL … verdict=`; writes nothing. Up to ≈ 1.9 h of one-thread free blocks plus the records' own walls. |
| `HECKE_LVALUE_MEASURE_HEAVY=1` | read-only, not an emitter (slot-20 WP-MEAS): `HeckeLValueMeasureValidation` adds `(226, 103)` at level 3 (`103^3` balls), `(282, 37)` at `R = 5` with every character `ω^i` in the moment identity, and `(30, 37)` with every character (M1, M2 mod `ℓ^4`, M3, M4 b–d, M5; M4c by both routes where `ℓ^{M−1} ≤ 1369`). `EFFECTIVE HeckeLValueMeasureValidation arm=HEAVY cells=3`. **275 checks, 16 s, 72 MB** (WP-MEAS, the default arm included). |
| `HECKE_LVALUE_MEASURE_691=1` | read-only, not an emitter (slot-20 stretch S2, [E] `cl:lvmeas691`, `chk:lvmeas` (M691)): `HeckeLValueMeasureValidation` adds the 691 arm — the two Kubota–Leopoldt group rings at `ℓ = 691`, level 2 (344 classes), and `Δ` at `(10, 691)`, `R = 2`, level 2, through (M1), (M3)–(M7) as at the other Eisenstein cells (`d = 1`; 0 / 3773 off-pole moments, 343 / 343 branches by both routes, the 22 pole points a unit off), `a_p ≡ τ(p) mod 691²`, the Python oracle's values (`MeasureFrozenS2.inc`). `EFFECTIVE HeckeLValueMeasureValidation arm=ELL691 cells=1`; line `MEAS_691`. **263 checks (43 added), 38.5 s, 66 MB** (first run, `ENGINE_THREADS=8`, loaded box). Independent of `HECKE_LVALUE_MEASURE_HEAVY`. |
| `HECKE_LVALUE_COEFFRING_HEAVY=1` | read-only, not an emitter (slot-21 P3): `HeckeLValueCoefficientRingValidation` adds `(22, 144169)` (`S_24` at its ramified prime, `R = 2`, level 1: R0–R2, R4, R5 without frozen values) and `(34, 37)` at level 3 (R2). `EFFECTIVE HeckeLValueCoefficientRingValidation arm=HEAVY cells=2`. **674 checks (71 added), 138 s, 74 MB** (first run, quiet-ish box). |
| `HECKE_LVALUE_EISMEAS_HEAVY=1` | read-only, not an emitter (slot-21 P2): `HeckeLValueEisensteinMeasureValidation` adds `(30, 37)` at level 3 (E0–E7, E9 on `37^3` balls) and `(20, 131)` at level 2 (KL route `E_{1,c}` only). `EFFECTIVE HeckeLValueEisensteinMeasureValidation arm=HEAVY cells=15`. **259 checks (34 added), 11.9 s, 20 MB** (first run); 273 since P2x (the default arm gained E8L2 / E9L2), 12.6 s, 40 MB. |
| `HECKE_LVALUE_WILD_HEAVY=1` | read-only, not an emitter (slot-21 P4): `HeckeLValueWildCharacterValidation` adds W5 (complex `L(Δ,χ,j+1)`) at conductors 125 and 169, W2/W3 `(10,11)` at `m = 3` (`O = Z_11[ζ_{121}]`, `e = 110`) and W6 `(30,37)` at `t = 2`. `EFFECTIVE HeckeLValueWildCharacterValidation arm=HEAVY cells=32` (31 before P4x). **259 checks (37 added), 8.9 s, 0.09 GB** (P4x; 238 checks, 7.4 s, 25 MB at the first run). |
| `HECKE_LVALUE_IWASAWA_HEAVY=1` | read-only, not an emitter (slot-21 P5): `HeckeLValueIwasawaInvariantsValidation` adds the Kubota–Leopoldt table at 691 and the cells `(282,37)`, `(226,103)`, `(10,691)`. `EFFECTIVE HeckeLValueIwasawaInvariantsValidation arm=HEAVY cells=25`. **658 checks, ≈ 72 s, ≈ 0.10 GB** (first run). |
| `HECKE_LN23_STURM=1` | read-only (slot-22 LN23-F): replaces every arm of `HeckeLevelNCurveValidation` by the Sturm separating family `q ≤ B = ⌊(N+1)/6⌋` ([C] `rmk:levelNcurvefamily` (2)) on the default grids (34 cells `p = 2`, 39 cells `p = 3`) + `(2137,2)`, `(2377,2)`, `(2953,2)` — or on the `HECKE_LEVEL_N_R3_SMALLP_CELLS` cells when both are set; per cell (ST1) = the certified reading, (ST2) a good prime in the family, (ST3) CE; prints the caveats (`𝕋^0` only: the constant term of the full algebra at `p ∈ {2,3}` not covered; Loewy needs (LN6)'s \CONJ). `EFFECTIVE HeckeLevelNCurveValidation arm=STURM cells=<k>`. **76 cells, 228 checks, 0 failing, 27.4 min, 0.45 GiB** (`ENGINE_THREADS=4`; cost ≈ `N^3`, max `(2953,2)` 181 s). Any other value than `1` is refused. |
| `HECKE_LN23_HEAVY=1` | read-only, not an emitter (slot-22 LN23): `HeckeLevelNCurveValidation` adds `(21929, 2)` (CE §6 `e_2 = 127`: `dim W = 255`, Loewy 128). `EFFECTIVE HeckeLevelNCurveValidation arm=HEAVY cells=1`. **10.6 s, 0.59 GiB** for the cell (`ENGINE_THREADS=1`). |
| `HECKE_TAMEFAMILY_HEAVY=1` | read-only, not an emitter (slot-22 WAKE-1): `HeckeTameFamilyValidation` adds `ℓ_1 = 263` (the oracle's W-P9 cell, `Γ_H(2893)`, `h = 2641`) and the INFO cell `ℓ_1 = 197`. `EFFECTIVE HeckeTameFamilyValidation arm=HEAVY cells=1`. **328 s, 1.56 GiB** (`ENGINE_THREADS=8`). |
| `HECKE_TAME_FAMILY_CELLS="p:ℓ_0:ℓ_1,…"` | read-only, not an emitter (slot-22 WAKE-3): `HeckeTameFamilyValidation` adds the survey cells after the default arm (preprint hypotheses, the `Γ_0` rank filters F0 / F1, then the lean `Γ_H(ℓ_0ℓ_1)` route; case (ii) gated, case (iii) printed as `FINDING`); malformed items refused by position (each a failing check). `EFFECTIVE HeckeTameFamilyValidation arm=CELLS cells=<k>`. Per cell ≈ `0.15 GB + 20 h²` bytes; `(5,11,263)` 44 s, 0.19 GB; largest run `h ≈ 6900` (see `WAKE_survey_report.md`). |
| `HECKE_LAMBDA_TOWER_R3=1` (+ `HECKE_LAMBDA_TOWER_RSS_CAP_GIB`, default 4; `HECKE_LAMBDA_TOWER_OPS_CAP`, default `10^12`) | read-only (slot-22 P10): `HeckeLambdaTowerValidation` adds `(11, 2, 3)`, `(13, 0, 3)` after predicting bytes and Krylov work from the measured `r = 2` cell; refused by name (`tower_rss_cap`, `tower_cost_cap`) above the caps, counted. `EFFECTIVE HeckeLambdaTowerValidation arm=R3 cells=2` and one line per cell with the predictions. At P10 both refused (33.5 GB, 86 GB). |
| `HECKE_LAMBDA_TOWER_CELLS="ℓ:a:r[:K],…"` | read-only (slot-22 P10): replaces the tower cell list; a malformed / out-of-range token is refused by position, an empty list fails, `ℓ > 13` is refused `tower_edge_not_built`. `EFFECTIVE HeckeLambdaTowerValidation arm=CELLS cells=<k>`. |
| `HECKE_NEB_WILD_ALL=1` | read-only (slot-22 P10 (a)): `HeckeNebentypusWildValidation` adds `O_{2,42}` at `(7, r = 3)` (three classes). `EFFECTIVE HeckeNebentypusWildValidation arm=ALL cells=3`. Not run at P10 (≈ 2.6·10¹¹ operations, dense). |
| `NF_PRANK_CE=CE1,CE2,CE1C,CE2C` or `all` | read-only (slot-22 NF-PRANK): `NumberFieldPRankValidation` runs the Calegari–Emerton cells of `NF-PRANK_spec.md` §8 (CE1 / CE2 check `rank_upper ≥ 2`; a `rank_upper ≤ 1` prints `CE_FINDING`, R-22a). `EFFECTIVE NumberFieldPRankValidation arm=<X> cells=<k> dense_bound=<B_0>`. All arms 77 s, 0.10 GB. |
| `NF_PRANK_CELLS="N:p,…"` / `NF_PRANK_DENSE=<B_0>` | read-only (slot-22 NF-PRANK): any cells (`p ≠ 5` refused by name) / the dense base bound of the hook arms (default 20000; descent above it). `EFFECTIVE NumberFieldPRankValidation arm=CELLS cells=<k>`. |
| `HECKE_SHAPIRO_CELLS="N:n:ell:m,…"` | read-only (slot-22 P6): `HeckeLValueShapiroValidation` arm S8 — ranks of `W_N^±` on `Γ_0(N)` by Shapiro vs Eichler–Shimura and the cost of the reduced system, per cell. `EFFECTIVE HeckeLValueShapiroValidation arm=CELLS cells=<k>`. Cost cubic in `|P^1(Z/N)|(n+1)/2` (`(37,100,211^2)` 44 s, 0.23 GB). |
| `HECKE_LEVEL_N_R3_SMALLP_CELLS="N:p,…"` | read-only (slot-22 LN23): replaces every arm of `HeckeLevelNCurveValidation` by curve readings at `p ∈ {2, 3}` (`N` prime, `p | num((N−1)/12)`, refused by position otherwise), CE Thm 1.1 / 1.2(i)+1.3(i) compared where `p ‖ num`. `EFFECTIVE HeckeLevelNCurveValidation arm=SMALLP smallp_cells=<k> object=curve`. |
| `HECKE_LN23_Z1_NMAX` / `HECKE_LN23_THM11_NMAX` / `HECKE_LN23_THM12I_NMAX` / `HECKE_LN23_QMAX` | read-only (slot-22 LN23): widen the torsion gate (primes `N ≤` value; 2000: 377 levels, ≈ 1 s), the CE Thm 1.1 grid and the Thm 1.2(i) grid (`10^4`: 133 / 133, ≈ 50 s), and the Hecke primes `q ≤ QMAX` of every reading (default 13). **At the default `q ≤ 13` the Thm 1.1 grid to `3·10^4` reads 369 / 397: two failure modes, `LN23_report.md` §5 / F4 §5: 23 of the 28 cells lack a Mazur good prime `≤ 13` (9 with `dim W` right and the series short, 14 also with `W` too large), the other 5 have one and fail by separation only (`W` large); at `q ≤ 31` 26 of the 28 agree, at `q ≤ 100` all 28 (LN23: 1002 s, max 81 s / 3.0 GiB per cell). Since LN23-F the CE checks compare the certified family: the Thm 1.1 grid to `3·10^4` reads **397 / 397** (369 at `q ≤ 13`, 358 certified at `q ≤ 13`; 3718 checks, 0 failing, 72 min, 0.77 GiB max per cell, `ENGINE_THREADS=4`); Thm 1.2(i) to `10^4`: 133 / 133, 132 certified at `q ≤ 13` (8011: `q ≤ 13` reads Loewy 2, certified at 19 with Loewy 4), 213 s, 0.12 GiB; `LN23F_report.md`.** Each prints `EFFECTIVE HeckeLevelNCurveValidation arm=Z1 / THM11 / THM12I cells=<k> nmax=<n>` or `qmax=<q>`. |
| `HECKE_HIDA_CM_CELLS="N:d:k:ell,…"` | read-only, not an emitter (slot-16 WP-15 + repairs): replaces `HeckeHidaCMValidation`'s default arms. `d < 0` a fundamental discriminant with `\|d\| \| N`, `N ∈ [3, 2^20)`, `ell ≥ 5` prime, `ell ∤ N`, `k ∈ [2, 4096]`; an empty value or a malformed / out-of-range cell throws by position. Per cell: the characteristic-0 CM count at `N = \|d\|` (gated), (U8) when `λ_k` exists with `h_K = 1`, (U10) when `(ell − 1) \| (k − 1)` and `ell` splits; the prime list is extended to the Sturm bound when it is ≤ 100, beyond that the cell's U8 / U10 checks are `gates=reported` (only the char-0 count stays gated). One `HIDA_CM_CELL` line per cell (with `sturm_bound`, `p_max`, `gates=`), `HIDA_CM_CELLS_SUMMARY`, `EFFECTIVE HeckeHidaCMValidation arm=CELLS cells=<k>`; `neb_dense_cap` reported as `refused=`. |
| `HECKE_U_ELL_LOW_RANK=0`, `HECKE_COSET_STREAM=0`, `HECKE_PARALLEL_SETUP=0`, `HECKE_RANK1_CLOSED_FORM=0` | **RETIRED 2026-10-31 (S24 CL-R1, owner ruling 2)**: in the default build (`OC_ENABLE_LEGACY=OFF`) each `=0` is **refused** at its first read (`REFUSED <NAME>=0: compiled out (OC_ENABLE_LEGACY=OFF)`, stderr, exit 1); any other value, or unset, is the one route; the `--bench` flags below are gone in every build. With `OC_ENABLE_LEGACY=ON` the text that follows holds unchanged. **rollback arms, not emitters, and none can change a value**. Each turns off one of the `U_ell` levers, which are **default-on since the owner's Q8 of 2026-09-28**: the low-rank lever (slot-13 WP-4, `Auto`: in effect iff `ell \| N` and the fibre is `SymN`), coset streaming and the serial setup phase on the pool (slot-14 WP-10), and G0's rank-one closed form over `F_ell`. `0` turns a lever off; any other value, or unset, leaves it on. The variable sets a thread's **initial** state, and the `Scoped…` guards override it. No lever moves a fingerprint, record, job id or golden line. `HeckeUEllStreamValidation` proves every combination equal to the all-off path. `--bench` flags: `docs/performance-reference.md`. |
| `HECKE_IOTA_STREAM=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_IOTA_STREAM=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 P4I): `HeckeInvolution::compute()` (the ι phase of the HeckeExt sign split) **admits the tasks of `check_obl_iii` and `build_split` first come, first served under a byte budget by default** (twice the largest task's estimate; before, `run_concurrently` held every task's buffers at once), **splits each flat family by one `(X ± ι_C X)/2` buffer per sign** (its column rank profile in place, then the pivot columns recomputed into the output; no `x` / `Pmat` / RREF cache / `image()` copies) and **keeps the C/Z/B ± bases once** (in the certificate); exactly `0` restores the pre-P4I (materialised) computation. Sets a thread's initial state; `HeckeInvolution::ScopedIotaStreaming` overrides it; read once per `compute()`. When the variable is set (any value) the first `compute()` of the process prints `EFFECTIVE HECKE_IOTA_STREAM iota=streamed|materialised (HECKE_IOTA_STREAM=<v>)` (what the variable selects, not a scoped override); under `ENGINE_TRACE_RSS=1` the ι phase prints `[iota] …` marks (steps, per-task lines, the `admission:` line). `HeckeIotaStreamValidation` compares the two entrywise. |
| `HECKE_FIELD_DIET=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_FIELD_DIET=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use `ScopedFieldDiet(false)`, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 G6; `Util/FieldDiet.h`, one thread-local flag): by default (1) `compute_block()`'s dense program 1 runs **in parts** when its CSE temps would exceed 256 MiB (`HeckeOperatorOptions::kThetaPartBudgetBytes`), (2) a HeckeExt cell releases its `HeckeOperatorFamily`'s level (a) and tables after Stage 1 (`release_level_a()`), (3) `malloc_trim(0)` after each streamed prime, (4) the boundary morphism reads the bulk H basis from its block form (no bulk FlatMatrix list cache), (5) the cone certificate's span tests C2 / C3 / C5 take the **unit-row route** where every basis column has a unit row, and a cone degree whose differential has no rows shares Z with Ceq, and (6) a census campaign cell releases its cone's cochain objects before the ι phase; exactly `0` restores the pre-G6 computation for all of them (not `tape::factor_basis`'s memory-only G6 changes, which have no switch: `ENGINE_API.md` §8). `HeckeOperatorOptions::ScopedFieldDiet` / `ConeOptions::ScopedUnitRowSpan` set the same flag. When the variable is set (any value) the first reader of the flag in the process (any lever, also a cone or boundary morphism built without a Hecke operator; G6 audit F2) prints `EFFECTIVE HECKE_FIELD_DIET field_diet=on|off (HECKE_FIELD_DIET=<v>)`; under `ENGINE_TRACE_RSS=1` the parts print `[hecke] q=<q> program 1 in parts: …`, the release `[ext] family level (a) released: …`, the sweep `[streamed] p=<p> pipeline released, VmRSS=… (heap in use …)`. Measured: `docs/implementation/slot24/G6_report.md`. `HeckeThetaRssDietValidation`'s G6 arm compares the two entrywise. **Size floors (slot-25 PERF-VF (b), speed / memory only)**: lever (1)'s pre-walk is skipped when `floor(#terms / 2) · d_V² · 4 B` already fits the part budget (the parted decision is then "whole" by construction; counted in `FieldDietStats::prewalk_skipped`), and lever (2) runs only when `max_q dim C^q_eq ≥ kFieldDietReleaseMinDimCeq = 2700` (`HeckeExtDriver.h`; = n ≥ 299 on the SL(2,Z) model; `ENGINE_TRACE_RSS=1` prints `[ext] max dim C_eq=… (release floor 2700)`). **PERF-VF fix 1:** the skip test is `floor(T/2) ≤ floor(budget / temp)` (no product to wrap, audit N1); the validation-only `ScopedPrewalkAudit` re-runs the pre-walk after a skip and `ENGINE_CHECK`s `shared ≤ floor(T/2)` and "not parted" (audit S4; `HeckeThetaRssDietValidation` G6-P lean-mode runs, `prewalk_audits=`); the validation-only `hecke_ext::ScopedReleaseMinDimCeq(0)` forces lever (2) on a small cell, and `HeckeExtDeterminismValidation` (standard, so inside `--all`) prints `STAGE1_RELEASE cell=(10,691) default: releases +0 … floor 0: releases +1 … (released == not released)` (audit S3; a separate check, outside the printed digest). |
| `HECKE_RHO2_STREAM=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_RHO2_STREAM=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 P4R): route 2 of `HeckeOperatorOnK::compute_block()` (the O12(a) cross-check) is **streamed by default key by key (one d × d accumulator per route-2 block; the distinct keys' `ρ_n` evaluated in batches of 64, each once, and added with delayed reduction; no per-degree memo `rho2`)**; exactly `0` restores the materialised memo and its `hecke.route2` programs. Sets a thread's initial state; `ScopedRho2Streaming` overrides it. When the variable is set (any value) the first `compute_block()` of the process prints `EFFECTIVE HECKE_RHO2_STREAM route2=streamed|materialised (HECKE_RHO2_STREAM=<v>)`; under `ENGINE_TRACE_RSS=1` each streamed degree prints `[hecke] q=… route 2 streamed: keys …, evaluations …, blocks …, batch 64 (evaluate … s, accumulate … s, compare … s), VmRSS=…`. The U_ℓ lever's factored route 2 is not affected. `HeckeRho2StreamValidation` compares the two entrywise. |
| `HECKE_MODULE_STREAM=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_MODULE_STREAM=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 G2-A / G2-B, `slot23/G2_plan.md` §2.1–2.2): by default the Z/ℓ^k module route **reads Θ_eq ([C, obl:welldef](iii), `HeckeOperatorOnKT::compute_module()`), X_q (`EquivariantCohomologyOnKT::compute_cohomology_module()`) and the C^q_eq coordinates of `H_class_coordinates()` off the unit pivots of C** (`engine::elim::solve_unit_pivot_readoff`: C[piv, :] = I checked, the residual recomputed exactly over every row in row blocks; any other outcome takes the Howell solve), **checks d∘d by one GEMM**, and runs `cyclic_decomposition`'s column clear i-outer; exactly `0` restores the Howell solve, the scalar d∘d loop and the i-inner clear, bit for bit. Any other value warns once on stderr (`WARNING HECKE_MODULE_STREAM=<v> is neither 0 nor 1: the stream route stays on`) and stays on. Read once per process; `engine::elim::ScopedModuleStream` overrides it. When the variable is set (any value), the first consultation of the lever anywhere (Θ_eq, X_q, `H_class_coordinates`, d∘d, `cyclic_decomposition` — also a cohomology-only or Integral `Subquotient` run) registers one line per process, printed **at exit** with the final counters (audit m2): `EFFECTIVE HECKE_MODULE_STREAM mode=stream|legacy source=env (HECKE_MODULE_STREAM=<v>) solve=readoff:<a>,howell:<b>,legacy:<c> dd=gemm:<d>,scalar:<e> cyc=interchanged:<f>,legacy:<g> omega=streamed:<h>,table:<i> lr=grouped:<j>,scalar:<k>,early_flush:<f> route2=blocked:<l>,full:<m> w=nonpivot:<o> retention=lean:<r>` (`early_flush` ⊂ `grouped`: flushed at the stacked-width cap; `route2=blocked` counts σ block rows, 23 per operator, not chunks). **Since G2-C / G2-D / G2-E** (`slot23/G2CDE_report.md`) the same lever also selects, in `HeckeOperatorOnKT::compute_module()`, the coset-outer Θ assembly (Ω_i per (degree, coset), no Ω table, memos per coset), the grouped low-rank GEMM for T_ℓ, route 2 in σ-row chunks compared and dropped (no T2), Θ_eq read off the product Θ·C (`solve_unit_pivot_readoff_product`, W never materialised), `factor_low_rank`'s valuation by multiplication, and in `RunModuleT` the lean retention (X, Zc, Θ, Θ_eq released; their guarded accessors throw); **since G2-G** (`slot23/G2G_report.md`) also the lean work buffers of `elim::cyclic_decomposition` / `elim::invariant_factors` (EFFECTIVE fields `cyc_buffers=lean:<a>,legacy:<b> invf=lean:<c>,legacy:<d>`); **since G2-F** (`slot23/G2F_report.md`) also, in `RunModuleT`, each operator's tau table built `TauTableContents::ChainsOnly` (the same chain records, no xi-term table, no ρ_n pool; EFFECTIVE field `tau=chains:<a>,pooled:<b>`); `0` restores all of it. The flat-coordinate route (ℓ ∈ {2, 3}) and the digit route are not affected, except for `invariant_factors`' work buffers on the flat route (value-neutral, G2-G; audit m1). `HeckeModuleStreamValidation` compares the two entrywise and byte for byte. |
| `HECKE_MODULE_EVAL=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_MODULE_EVAL=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 G2-T, `slot23/G2T_report.md`): by default the stream route of the Z/ℓ^k module operator (`HeckeOperatorOnKT::compute_module_stream()`, only there) evaluates every ρ_n(g) mod ℓ^k by `ComputeSymmetricPowerRowsRing` (row-major, one Pascal row per operator, the column steps in a wavefront, one reduction per entry) and factors the T_ℓ terms by `factor_low_rank(…, fast_scan = true)` (divisibility scan, valuation floor, rank-1 GEMM update); exactly `0` restores the G2-F evaluation (`ComputeSymmetricPowerMatrixRing` through its FlatMatrix carrier, the per-entry scan and loop), bit for bit. Any other value warns once (`WARNING HECKE_MODULE_EVAL=<v> is neither 0 nor 1: the fast evaluation stays on`) and stays on; `engine::elim::ScopedModuleEval` overrides it. Inert under `HECKE_MODULE_STREAM=0`. When set, one line at exit, registered at load (so also when the lever is never consulted, e.g. under `HECKE_MODULE_STREAM=0`, with `eval=fast:0,legacy:0`; audit F3): `EFFECTIVE HECKE_MODULE_EVAL mode=fast|legacy source=env (HECKE_MODULE_EVAL=<v>) eval=fast:<a>,legacy:<b>` (operator degrees per route; also on the `EFFECTIVE HECKE_MODULE_STREAM` line as `eval=`). Cost: none (T_ℓ sat cells 1.5–2.4× faster with it on). Oracle: `HeckeModuleStreamValidation` (V). |
| `HECKE_RHO_SIMD=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_RHO_SIMD=0` / `=scalar` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 G2-T2, `slot23/G2T2_report.md`): by default `ComputeSymmetricPowerRowsRing`'s [U_a] / [U_b] column steps (the stream route's ρ_n, `HECKE_MODULE_EVAL` on) run, on a u32 word with p ≤ 2^31, on the runtime-dispatched SIMD path: AVX-512F (64 lanes) if the CPU has it, else AVX2 (32 lanes), else the G2-T scalar 8-lane wavefront (target attributes, no `-march`; non-x86 builds: scalar only). Each lane step is three Shoup products and two canonical sums: the same canonical residues. Values: `0` / `scalar` = the scalar wavefront; `avx2` / `avx512` = that path (if unavailable: a warning, the automatic choice stays); `1` / `auto` = automatic; anything else warns once (`WARNING HECKE_RHO_SIMD=<v> is none of …`) and stays automatic. `ScopedRhoFillPath` overrides it (validation). u64 words and u32 moduli > 2^31 always take the scalar path. When set, one line at exit, registered at load: `EFFECTIVE HECKE_RHO_SIMD path=<p> source=env (HECKE_RHO_SIMD=<v>) cpu=avx2:<0|1>,avx512:<0|1> fills=avx512:<a>,avx2:<b>,scalar:<c>` ([U] fills per path). Cost: none. Oracle: `HeckeModuleStreamValidation` (V) (d)–(f) (every available path forced). |
| `HECKE_MODULE_PARALLEL=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_MODULE_PARALLEL=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 G2-P, `slot23/G2P_report.md`): by default, when the consumer pool has more than one worker (`ENGINE_THREADS` > 1), the stream route of the Z/ℓ^k module operator assembles Θ^{(q)} and route 2 in parallel coset batches (keys listed serially, evaluated by the pool, rows accumulated in the serial order) and the Howell forms / product read-offs split their disjoint row updates over the elimination hook; exactly `0` restores the serial route; any other value warns once and stays on. At `ENGINE_THREADS=1` it is inert. The Howell / read-off splits run over the elimination hook, so **`ENGINE_HOST_ELIM_HOOK=0` keeps them serial** while the assembly stays parallel (G2-P audit F2). `EFFECTIVE HECKE_MODULE_PARALLEL mode=… threads=… par=parallel:<a>,serial:<b> hook=howell:<c>,readoff:<e> elim_hook=on|off[ howell_readoff=serial]` at exit when set, or when `ENGINE_HOST_ELIM_HOOK=0`. Extra peak RSS at k > 1 threads ≤ k·(32·1024·d + 12·d²) B + 256 MiB (u32; `performance-reference.md`). Gated by `HeckeModuleStreamValidation` (P). |
| `HECKE_MODULE_MT=0` | **a rollback arm, not an emitter, cannot change a value** (slot-24 MT-1, `slot24/MT1_report.md`, `ENGINE_API.md` §13.6): by default `cyclic_decomposition`'s pivot search on the lean module route stops at the first unit at **every** thread count (census mode included; owner ruling 2026-10-20), and, where `HECKE_MODULE_PARALLEL` is on and the pool has more than one worker, the module route splits further steps over the pool: the tiled pivot search and the row operations of `cyclic_decomposition`, the row-block products Y = Θ H / D C / C · dec.basis, the per-column runtime assertions (i) / (ii), one assembly task per (σ, σ_k) block, the read-off residual blocks and the right-hand sides of `solve_from_augmented`, Exactly `0` restores the route of before MT-1 (G2-P's) verbatim; any other value warns once and stays on. `EFFECTIVE HECKE_MODULE_MT mode=… regions=cyc_search:…,cyc_rows:…,gemm:…,check:…,assembly:… pivot_exit=…` at exit when set (`pivot_exit` = `cyclic_decomposition` calls on the exit search, every thread count; suffix `(HECKE_MODULE_STREAM off: inert)` / `(HECKE_MODULE_PARALLEL off: splits inert, pivot-search exit on)` where it applies). Peak RSS within ±2 % of the pre-MT route ((1000, 10007) at 16 threads 2.74 GiB, REF 2.70). The opt-in `HECKE_MODULE_MT_FORMS` of the implementation round was removed at the audit (`slot24/MT1_audit.md` F1). Gated by `HeckeModuleMtValidation`. |
| `HECKE_MODULE_LEAN_PEAK=0` | **a rollback arm, not an emitter, cannot change a value** (slot-24 G2-H, `slot24/G2H_report.md`, `ENGINE_API.md` §13.6): by default, on the stream route, `howell_rows` adopts its store as H when no closure row was appended and every row is a pivot row, and the lean decompositions take length(colspan Rl) from the pivot loop alone; under the lean retention of `RunModuleT` (sat / Loewy cells) (iii) is certified by `unit_pivot_residual_product` (Θ_eq never formed), route 2 is subtracted from Θ in place after Y and (i)–(iii) (no route-2 buffer), and the cohomology's Z^q / H^q loop runs kernels first, then the decompositions in descending q, freeing X_q / Zc_q after their last reader. Exactly `0` restores the route of before G2-H verbatim; any other value warns once and stays on. `EFFECTIVE HECKE_MODULE_LEAN_PEAK mode=… howell=adopt:…,copy:… residual=… route2_inplace=… early_release=… length_only=…` at exit when set (suffix `(HECKE_MODULE_STREAM off: inert)` where it applies). Tracked peak (300, 43) 529 → 426 d². Gated by `HeckeModuleStreamValidation` (H). |
| `HECKE_ROUTE2_SHARED_MEMO=0` | **Env arm retired 2026-11-07 by S25 LEVERS-25** (`slot25/LEVERS25_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_ROUTE2_SHARED_MEMO=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-23 G2-T2, `slot23/G2T2_report.md`): by default the stream route builds route 2 (the O12(a) certificate) of a degree with N_q > 7 in ONE chunk of all N_q block rows, so its ρ memo spans (degree, coset) — every distinct δ_iγ key of a coset evaluated once instead of once per chunk; exactly `0` restores G2-D's two σ-row chunks with the memo per (chunk, coset), verbatim. The route-2 buffer is N_q d × N_q d instead of ⌈N_q/2⌉ d × N_q d (+5 d² words at q = 1). Any other value warns once and stays on; `engine::elim::ScopedRoute2SharedMemo` overrides it. Inert under `HECKE_MODULE_STREAM=0`. When set, one line at exit, registered at load: `EFFECTIVE HECKE_ROUTE2_SHARED_MEMO mode=shared|chunked source=env (HECKE_ROUTE2_SHARED_MEMO=<v>) route2_degrees=shared:<a>,chunked:<b>`. Oracle: `HeckeModuleStreamValidation` (V) (g). |
| `HECKE_SAT_PERF=0` | **a rollback arm, not an emitter, cannot change a value** (slot-24 SATPERF, `slot24/SATPERF_report.md`; `HeckeExt/HeckeRingHeckeAlgebra.h`): by default (1) a sat cell (`ComputeSaturationDefectCell`) reads every whole-module derivation — the characteristic polynomials (Berkowitz), `RationalSystems`, each system's joint idempotent, its block e N (`Localize`) and the certificate's Smith exponents of e N — from a per-level memo (`ringalg::ModuleDerived`), once per cell instead of once per block (up to five times per block inside `CertifyStable`), and hands its torsion pre-pass to every certificate; the Loewy cell's certificates read the same memos; (2) every End(N) product (`EndCtx::mul`) accumulates in uint64_t when r · max A · max B < 2⁶⁴ (exact, so the same residue) and, under an installed host elimination hook and r ≥ 24, splits its output rows over the pool; (3) the sat cell installs `engine::tape::ScopedHostElimHook` around its post-module stages (never around a module run; a no-op at one worker or with `ENGINE_HOST_ELIM_HOOK=0`). Exactly `0` restores the route of `4dd1a7e0` verbatim (no memo, the serial u128 product, no hook); any other value warns once and stays on. When set, the first sat cell prints `EFFECTIVE HECKE_SAT_PERF route=memo+par|legacy source=env (HECKE_SAT_PERF=<v>)` (configuration only; audit F9); the per-cell counters are on the cells arm's `SAT_DEFECT_TIMES` line, the process totals on `HeckeSatPerfValidation`'s last line. The uint64_t accumulation is decided per product on the actual maxima (dense entries: roughly q² r < 2⁶⁴, e.g. ℓ = 103, r = 429 up to K = 4). Measured (4 threads, loaded box): (700, 37) KMAX 6 245.4 s → 61.5 s, the non-module part 176.6 s → 9.2 s. Gated by `HeckeSatPerfValidation`. |
| `HECKE_DESCENT_CELLS=<n>[,<n>…]` | **read-only** (slot-24 DESCENT D0, `slot24/DESCENT0_report.md`): **replaces** the `DESCENT_COST` cells of `IntegralDescentGroupsSlowValidation` (default `100,200,300`); prints `EFFECTIVE IntegralDescentGroupsSlowValidation arm=HECKE_DESCENT_CELLS cells=<k>` (`arm=default` unset); a non-integer item throws, an empty list fails. Cost ≈ n³ (n = 300: descent 36 s, comparator (a) 145 s, 1.3 GiB peak); n ≤ 10005 (good prime 10007). Chooses cells only, never a value. |
| `HECKE_DESCENT_REPEATS=<k>` | **read-only** (slot-24 DESCENT D0 audit M2): the number of timing rounds per `DESCENT_COST` cell of `IntegralDescentGroupsSlowValidation` (default 5, 1..99; the route order rotates each round; median, min and max are printed); on the `EFFECTIVE … repeats=<k> threads=1` line. Never a value. |
| `HECKE_DESCENT_LEVELN_CELLS=<N>:<n>[,…]` | **read-only** (slot-24 DESCENT D0): **replaces** the level-N probe cells of `IntegralDescentGroupsSlowValidation` (default `11:6,11:20,16:6,16:20,50:6`); prints `EFFECTIVE IntegralDescentGroupsSlowValidation levelN_arm=HECKE_DESCENT_LEVELN_CELLS cells=<k>`; each cell prints its predicted RSS (`PredictLocalRss`, `PredictTreeRss`) **before** it starts and is `NOT STARTED` above the 40 GiB cap (rule 19; `Iso^(2)` alone is skipped above it). `D = ψ(N)(n + 1)`; (50, 20), `D = 1890`, predicts 15.3 GiB and hours of single-threaded Smith. Never a value. |
| `HECKE_DESCENT_N_CELLS=<N>:<n>[:<pieces>][,…]` | **read-only** (slot-24 DESCENT D1, `slot24/DESCENT1_report.md`): **replaces** the `DESCENT1_N_COST` cells of `IntegralDescentLevelNSlowValidation` (default `11:20,16:20,35:10,50:6`) and drops the level-1 cost lines; `pieces` ⊆ `z32t` (z: ℓ ≥ 5 and the direct-Smith comparator, 3, 2, t: the tree at 2), default all; prints `EFFECTIVE IntegralDescentLevelNSlowValidation arm=env cells=<k> repeats=<r> rss_cap_gib=40`. Every dense piece's RSS is printed before it starts and a piece above the 40 GiB ceiling is refused, never started (`Iso^(2)` 4 524 D² B, `Iso^(3)` 2 320 D² B, tree 228 D² B, direct Smith 424 D² B). `HECKE_DESCENT_REPEATS` (default 5) applies too. Chooses cells only, never a value. |
| `HECKE_DESCENT_TREE=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_TREE=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 DESCENT D5, `slot24/DESCENT5_report.md`; `Integral/Descent/DescentTree.h`): by default the 2-adic piece (level 1, level N, and D2's level pair), the dense 3-adic piece (level 1, level N with ν₃(N) > 0, the pair) and the level-1 ℓ ≥ 5 piece (the Bredon tree in place of the direct Smith of C_eq) run on the tree models Iso^(ℓ)_𝒯 of [C] `prop:isomodeltree` (closed-form cochains, ranks 4/3, 7/3, … D at 2). Exactly `0` restores the dense Iso^(ℓ) route of D0–D2 (same groups and maps: `HeckeIsotropyModelTreeValidation` (L1), (LN), (D2)); `1` or unset = the tree; any other value warns and keeps the tree. Read once; `ScopedDescentTree` overrides it in validations. |
| `HECKE_DESCENT_TREE_CELLS=<N>:<n>[:both/tree],p<N>:<MN>:<n>[:both/tree],…` | **read-only** (slot-24 DESCENT D5): **replaces** the cost cells of `HeckeIsotropyModelTreeSlowValidation` (N = 1: level 1 by `AssembleDescent`; `p…`: a level pair by `AssemblePairMaps`) and drops its oracle and chain-level arms; prints `EFFECTIVE HeckeIsotropyModelTreeSlowValidation arm=env cells=<k> repeats=<r> rss_cap_gib=40`. Every cell's RSS (`PredictTreeLocalRss`, `maps::PredictPairRssTree`) is printed first; `both` also runs the dense route when its prediction is under the ceiling. `HECKE_DESCENT_REPEATS` applies. Chooses cells only, never a value. |
| `HECKE_DESCENT_HECKE_CELLS=<N>:<n>[:<p>/<p>…][:chi\|tors\|all][:<max primes>],…` | **read-only** (slot-24 DESCENT D3): **replaces** the cells of `IntegralDescentHeckeSlowValidation` (and drops its oracle arms); per cell `DESCENT3_COST` lines for char_Z(T_p) (default p ∈ {5, 7, 13}; `max primes` caps the residue primes -- the coefficients beyond the coverage are then reported as residues and bound, the output rule of [C] `prop:crtcharpolyN`(5)) and for the torsion reads (tree at 2, 3; cokernel at ℓ ≥ 5); prints `EFFECTIVE IntegralDescentHeckeSlowValidation arm=HECKE_DESCENT_HECKE_CELLS cells=<k>`. Every read's RSS prediction is decided before building (refused above 40 GiB). Chooses cells only, never a value. |
| `HECKE_DESCENT_PAIR_CELLS=<N>:<M>:<n>[,…]` | **read-only** (slot-24 DESCENT D2, `slot24/DESCENT2_report.md`): **replaces** the `DESCENT2_COST` cells of `IntegralDescentMapsSlowValidation` (default `1:11:10,5:5:4,6:2:6,4:4:6`, i.e. (N, MN, n)) and drops its oracle arm; prints `EFFECTIVE IntegralDescentMapsSlowValidation arm=env cells=<k> repeats=<r> rss_cap_gib=40`. Every cell's RSS (`maps::PredictPairRss`) is printed before anything runs and a cell above 0.9 × the 40 GiB ceiling (audit F3) is refused, never started. `HECKE_DESCENT_REPEATS` (default 5) applies. Chooses cells only, never a value. |
| `HECKE_DESCENT_BDRY_CELLS=<N>:<n>[,…]` | **read-only** (slot-24 DESCENT D4, `slot24/DESCENT4_report.md`): **replaces** the `DESCENT4_COST` ladder of `IntegralDescentPairSlowValidation` (default `4:2,11:2,23:2,47:2,71:2,97:2`) and drops its fixed cells (the (997, 2) refusal, the full pairs, level 1); prints `EFFECTIVE IntegralDescentPairSlowValidation arm=env cells=<k> rss_cap_gib=40`. Every cell's RSS (`pair::PredictPairRss`) is printed before anything runs and a cell above 0.9 × the 40 GiB ceiling is refused, never started. Chooses cells only, never a value. |
| `HECKE_DESCENT_TREE_PAIR=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_TREE_PAIR=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 DESCENT D5c, `slot24/DESCENT5c_report.md`; `Integral/Descent/DescentTreePair.h`). By default the 2-adic and the 3-adic pair pieces of `AssembleDescentPair` run on the tree cusp pair, the cone of the axis map of [C] `def:treepair`. Its cone ranks are 4/3, 10/3, 13/3, … D at 2. Exactly `0`, or `HECKE_DESCENT_TREE=0`, restores D4's dense (Iso^(ℓ), Isob^(ℓ)) pair. The two give the same groups and map types (`IntegralDescentTreePairValidation` (T)); Smith generators differ (invariants only). `1` or unset = the tree; any other value warns. Read once per process and once per call; `ScopedDescentTreePair` overrides it in validations. D4's standard name prints the route it ran: `EFFECTIVE IntegralDescentPairValidation route=tree\|dense source=…` (D5c audit N4). |
| `HECKE_DESCENT_GOOD_SPARSE=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_GOOD_SPARSE=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-L1, `slot24/PARL1_report.md`; `Integral/Descent/DescentAssembly.h`): by default the good-prime step of the level-1 groups route `AssembleDescent` (and `GoodPrimeFieldDims`, which the level-1 cost arm of `HeckeIsotropyModelTreeSlowValidation` uses for its Betti numbers) runs at **even n** on the shipped sparse cokernel of Γ_0(1) over F_good — the record route's step (`AssembleDescentN` (1)) — with h_0, h_1 checked against the closed form b_0, b_1 (`LevelNClosedForm(1, n)`, a throw on disagreement) and h_2 := 0; odd n keeps the shipped C_7. Measured at n = 2000 (one thread): the good prime 296 s (C_7; 55 s on 16 threads) → 22.8 s, the level-1 tree descent 315 s → 43.8 s. Exactly `0` restores `ShippedFieldDims` (the shipped C_7 pipeline on the caller's consumer pool) verbatim; `1` or unset = sparse; any other value warns and keeps sparse. Read once per process; `ScopedDescentGoodSparse` overrides it (validation use). Oracle: `IntegralDescentGroupsValidation` (GS) (sparse == shipped C_7 == the rollback, n ∈ {0, 2, 10, 12, 22, 40, 64, 100, 128, 13}) and (Z). Printed: `EFFECTIVE HeckeDescentGoodSparse route=sparse(even n; odd n: shipped)\|shipped source=default\|env\|scoped (<name>)` by `IntegralDescentGroupsValidation` and the two `HeckeIsotropyModelTree*` names. |
| `HECKE_DESCENT_GOOD_DENSE=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_GOOD_DENSE=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-GP, `slot24/PARGP_report.md`; `Integral/Descent/DescentAssembly.h`): by default (even n, `HECKE_DESCENT_GOOD_SPARSE` not 0) the level-1 good prime reads PAR-L1's three numbers dim M^<S>, dim M^<ST>, dim Rel as **dense ranks** — rank e_S, rank e_ST, rank [e_S \| e_ST] of the averaging idempotents 1 + ρ(S), 1 + ρ(ST) + ρ(ST)² over F_good (the one coset of Γ_0(1) is a fixed point of both, so every sparse generator is a column of one of them) — by the engine's blocked PLU (`engine::elim::rref` of e_S^T and e_ST^T, `eliminate_against` in row tiles, `column_rank_profile`), threaded over the one descent pool (`ENGINE_THREADS`; serial on a PAR-ASM worker) through the elimination's ParallelFor hook; h_0 / h_1 checked against the closed form as before. Ranks are unique, so no route moves a value. Measured at n = 2000, 16 threads: the good prime 22.75 s → 0.28 s (1 thread 0.46 s), the level-1 tree descent 30.8 → 8.1 s. Exactly `0` restores PAR-L1's sparse cokernel verbatim; `1` or unset = dense; any other value warns and keeps dense (printed `source=env-invalid(default kept)`, integration 3). Read once per process; `ScopedDescentGoodDense` overrides it; (GS) pins the sparse route with it since integration 3 (PAR-GP audit F2). Oracle: `IntegralDescentGroupsValidation` (GD) (dense ranks at 1 / 2 / 7 / 16 threads == the sparse cokernel's `dim_S`, `dim_ST`, `dim_rel`; dims dense == sparse == shipped C_7 at n ∈ {0, 2, 10, 40, 100, 200, 400, 13}; hook regions > 0). Printed: `EFFECTIVE HeckeDescentGoodDense route=dense\|sparse\|shipped(even n; odd n: shipped) source=default\|env\|env-invalid(default kept)\|scoped (<name>)`. |
| `HECKE_MODULE_TILE_WORK=0` | **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-L1, `slot24/PARL1_report.md`; `src/ModArithmetic/DenseElim.cpp`, `mod_tiles`): by default the hook splits of the module routes (`howell_rows`' elimination and back-reduction, `gemm_rows_hook`, `unit_pivot_residual_product`, `cyclic_decomposition`'s splits) use at most work / 2^20 tiles (at least ~1 M modular MACs per tile) and stay serial below two such tiles; before, a step of ≥ 2^17 MACs split into up to 16 tiles of ~8 000 MACs, and at (N, n) = (1, 60) the descent record's pair modules opened ~170 000 such regions whose pool wake-ups (≈ 43 futex calls per region) made 16 threads 40 % slower than 1 (7.63 s against 5.44 s; now 5.14 s). Exactly `0` restores the extent-only tile count verbatim; `1` or unset = the bound 2^20; a number ≥ 2 sets the bound (measurement knob); anything else warns and keeps the default. Read once per process; the tape's PLU hooks are untouched; tiling is value-neutral (`ENGINE_API.md` §13.6). When set, one line at exit, registered at load: `EFFECTIVE HECKE_MODULE_TILE_WORK mode=bounded\|extent source=env (HECKE_MODULE_TILE_WORK=<v>) min_tile_work=<w> capped=<a> serial=<b>`. Oracles: `HeckeModuleStreamValidation` (P) and `HeckeModuleMtValidation` (MT)(O) pin the extent-only tiling (`ScopedModuleTileWork(0)`) so their split assertions stay exercised, and each adds a 16-worker run under the bound 2^20 compared object by object with pool 1 / the pre-MT route ((P) also asserts the bound acted at n ≥ 40); `HostElimThreadDeterminismValidation` and the record digests. |
| `HECKE_DESCENT_SMITH_BLOCKED=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_SMITH_BLOCKED=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-D2, `slot24/PARD2_report.md`; `Integral/Descent/DescentSmith.h`). By default `maps::SmithForm` and its D2 / cone callers (`BuildPres`, `InducedMap`, `LatticeQuotient`, D2's `Mul`, the cone's cochain-map check in `RunPairLes`, the tree pair's RSS model) run the blocked, threaded, SIMD Smith form with factored transforms. Exactly `0` restores the scalar oracle code of record (`SmithFormOracle`, `BuildPresLegacy`, the dense transforms, the transposed check, the 7 c_max² RSS term). Bit-identical outputs (`IntegralDescentSmithBlockedValidation`); only the tree pair's RSS prediction (and so its refusal wall, D ≈ 6 340 → 8 000) differs. `1` or unset = blocked; any other value warns. Read once per process; `ScopedDescentSmithBlocked` overrides it in validations. |
| `HECKE_DESCENT_SMITH_SIMD=scalar\|avx2\|avx512` | **read-only** (slot-24 PAR-D2): forces the kernel body of the blocked Smith form (clamped to what the CPU has; default the best). Chooses a route, never a value. |
| `HECKE_DESCENT_TREEPAIR_CELLS=<N>:<n>[,…]` | **read-only** (slot-24 DESCENT D5c): **replaces** the `DESCENT5c_COST` ladder of `IntegralDescentTreePairSlowValidation`. That ladder is the 2-adic tree pair piece with `only_primes = {2}` (a measurement), refused before building above 0.9 × 40 GiB of `PredictTreePairRss`. It drops the full-pair, η and transport arms and prints `EFFECTIVE IntegralDescentTreePairSlowValidation arm=env cells=<k> rss_cap_gib=40 route=…`. Chooses cells only, never a value. |
| `HECKE_DESCENT_SMITH_MT=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_SMITH_MT=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-2K, `slot24/PAR2K_report.md`; `src/ModArithmetic/Binary/SmithPar.h`). By default the descent's ring2k / ring3k Smith forms (the 2-adic and 3-adic tree and dense pieces) run on `ENGINE_THREADS` threads (since PAR-UNIFY: an integer in [1, 256], garbage warns and takes the default; default the CPU affinity count, cap 64 — not the engine pool's 32; the one descent pool, shared with PAR-D2's `maps::SmithForm`): threaded trailing GEMM, panel TRSM, lazy panel (128 wide, `HECKE_DESCENT_SMITH_PANEL`) and per-level passes. Exactly `0` restores the serial code verbatim (as does `ENGINE_THREADS=1`); `1` or unset = on; any other value warns once and stays on. Read once per process; `smithpar::ScopedLever` overrides it in validations. Only call sites inside a `smithpar::ScopedEnable` (the descent's) are affected: the census, the orbifold campaign and the L23 reader stay serial. When set (or `HECKE_DESCENT_SMITH_PANEL` is), `EFFECTIVE HECKE_DESCENT_SMITH_MT phase=start mode=threaded|serial lever=on|off source=… threads=… threads_source=env|affinity|hardware|env-invalid panel=…` on stderr at start-up (so a killed run shows it) and the same with `phase=exit … max_used=… regions=parallel:…,serial:… d2_regions=… tasks=… panel_splits=… scoped_regions=…` at exit (PAR-UNIFY: `mode` is what the descent's unscoped calls run; `d2_regions` are PAR-D2's `maps::SmithForm` regions on the shared pool (lever `HECKE_DESCENT_SMITH_BLOCKED`); `scoped_regions` counts a validation's scoped-override regions apart). Gated by `DescentSmithMtValidation`. |
| `HECKE_DESCENT_SMITH_PANEL=<w>` | **read-only tuning knob, a route, never a value** (reclassified 2026-11-12 by S26 LEVERS-26 from "rollback lever" to a selector: every value stays admitted in every build) (slot-24 PAR-UNIFY, `slot24/PARUNIFY_report.md`; `src/ModArithmetic/Binary/SmithPar.h`). The LU panel width of the threaded ring2k / ring3k descent Smith (`threads() > 1`). **Unset = auto** (slot-24 PANEL-IMPL, `slot24/PANEL_report.md` §6–§7): the ring2k host LU takes **512** columns when the matrix it factors (that Smith level's / Howell call's matrix) has **≥ 12 000 rows**, else **128**; the ring3k LU takes 128 (until PANEL-IMPL the default was 128 for both). An explicit value **wins for every size and both rings**: `128` is the pre-PANEL-IMPL default, `64` PAR-2K's panel; any integer in [1, 4096] is accepted, anything else warns and stays auto. The ring2k **device** LU (`ENGINE_DEVICE=gpu`, `Ring2kDeviceLU.h`) is not reached by the knob or the size rule: it keeps `smithpar::kDevicePanel` = 128 on the threaded route (512 costs it ≈ 20 s at (1000, 20)). The serial route (`ENGINE_THREADS=1`, `HECKE_DESCENT_SMITH_MT=0`, every non-descent consumer) keeps `Params::panel` = 64. Identity: every pivot is a function of the exact column values (audit `da38ffe0` §2); gated by `DescentSmithMtValidation` (E) (panel 64 vs 128, ring2k also 512, at T = 3, 16, 64; (S) checks the size rule and that an explicit width wins). Read once per process; `smithpar::ScopedPanel` overrides it in validations; prints the EFFECTIVE line of `HECKE_DESCENT_SMITH_MT`, whose `panel=` field reads the explicit width or `auto(128|512) panel_rows=12000`, and whose exit line counts the host width chosen per threaded ring2k LU call (`lu_panels=128:<a>,512:<b>,other:<c>`; under `ENGINE_DEVICE=gpu` a call the device takes runs at 128 instead — `EFFECTIVE GPU_SMITH2K … panels=` shows it). |
| `HECKE_DESCENT_SMITH_F2_MT=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_SMITH_F2_MT=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-F2, `slot24/PARF2_report.md`; `src/ModArithmetic/Binary/SmithPar.h`, `BitMatrix.h`, `TritMatrix.h`). On the threaded descent route (`HECKE_DESCENT_SMITH_MT` on and more than one thread) the per-level F_2 / F_3 rank profile of the ring2k / ring3k Smith forms runs the lazy blocked echelon (`binary::echelon_lazy`: M4RI clears of up to eight strips per pass over row tiles, the pivot search on a transposed 512-column window; trit: a lazy blocked Gauss), and the level passes are vectorised / threaded (zero test, F_2 pack, trit planes, Schur compaction; on the device route the L-store copy and the left-columns permutation). Exactly `0` restores the PAR-2K code verbatim; `1` or unset = on; any other value warns once and stays on. Read once per process; `smithpar::ScopedF2Lever` overrides it in validations. When set, the `EFFECTIVE HECKE_DESCENT_SMITH_MT` line is printed (start and exit; `f2=threaded|serial f2_source=env|default`, at exit also `f2_lazy=… f2_par_searches=… t_s=f2_pack:…,f2_ech:…,f3_pack:…,f3_ech:…,level:…,lu:…,ech_search:…,ech_flush:…,ech_table:…,perm:…,schur:…`, per-phase wall seconds, diagnostic). Gated by `DescentSmithMtValidation` arm (F). |
| `HECKE_DESCENT_SMITH_MT_BENCH=<D>[,…]`, `HECKE_DESCENT_SMITH_MT_CELLS=<N>:<n>[,…]` (+ `_THREADS=<t>[,…]`, `_REPEATS=<r>`, `_PANEL=<w>`) | **read-only** (slot-24 PAR-2K): **adds** timing arms to `DescentSmithMtValidation` after its gate arms. `_BENCH`: `ring2k::smith<u32>` (k = 30) and `ring3k::smith` (k = 19) on a random D × D matrix (a rank-deficient product plus a 2-power scaled part), `PAR2K_BENCH D=… threads=… t_ring2k=… t_ring3k=…`; `_CELLS`: `RunTreeLocalPieceN` at ℓ = 2 and 3 on the level-N cell, `PAR2K_CELL N=… n=… D=… ell=… threads=… t_piece=… t_smith=…`; both compare every thread count's values with the first one's. `_THREADS` (default 1,2,4,8,16,32), `_REPEATS` (median printed), `_PANEL` (the LU panel width of both rungs for the bench only, on the serial route (a `Params` value) and, since PAR-UNIFY, on the threaded route (`smithpar::ScopedPanel`), restored after). Prints `EFFECTIVE DescentSmithMtValidation arm=… cells=… threads=… repeats=…`. RSS: the bench ≈ 12 D² bytes; a cell as `PredictTreeLocalRss`. Never a value. |
| `HECKE_DESCENT_PAR_ASM=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_PAR_ASM=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-ASM, `slot24/PARASM_report.md`; `Integral/Descent/DescentParAsm.h`). By default the tree pair's complex assembly runs its root matrices and copies as concurrent tasks, streams its two certificates (`maps::ProductsEqual`), and DescentPair's `MatMulZ` uses PAR-D2's threaded `MulMod` on reduced operands. Exactly `0` restores the serial code of record (the materialised products, `IsZero` / `EqualMod`, the serial loops) verbatim; `1` or unset = on; any other value warns once and stays on. Read once per process; `par::ScopedLever` overrides it in validations. Gated by `IntegralDescentParAsmValidation`. |
| `HECKE_DESCENT_PAR_ELL=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_PAR_ELL=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-ASM). By default the level-1 groups route's ℓ ≥ 5 Bredon-tree primes and `AssembleDescentPair`'s ℓ ≥ 5 pieces run concurrently under a joint RSS prediction (at most `floor(0.9 cap / one prediction)` at a time). Exactly `0` runs them one after another (verbatim, each with its own RSS sample); `1` or unset = on; other values warn. `ENGINE_DEVICE` ≠ cpu also keeps them serial. Gated by `IntegralDescentParAsmValidation` (L), (P), (R). |
| `HECKE_DESCENT_EMBED_MAP=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_EMBED_MAP=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-ASM). By default the identity-like cone maps (j, π of `RunPairLes`; j, dl of D2's `DensePiece`) go through `maps::InducedMapEmbed` (no dense c × c cochain map). Exactly `0` forms the dense f and calls `maps::InducedMap` verbatim; `1` or unset = on; other values warn. Gated by `IntegralDescentParAsmValidation` (E). |
| `HECKE_DESCENT_PAR_LN=0` | **Env arm retired 2026-11-12 by S26 LEVERS-26** (`slot26/LEVERS26_report.md`): an `OC_ENABLE_LEGACY=OFF` build refuses `HECKE_DESCENT_PAR_LN=0` (`REFUSED …: compiled out (OC_ENABLE_LEGACY=OFF)`, exit 1, at start-up in `main()` and at the first read); an ON build reads it as below; the old route stays in every build (its comparison arms use the `Scoped` override, unchanged by the retirement). Before: **a rollback arm, not an emitter, cannot change a value** (slot-24 PAR-LN, `slot24/PARLN_report.md`). By default `AssembleDescentN` runs its good prime, ℓ ≥ 5 sparse eliminations and ℓ = 3 shortcut elimination concurrently under the joint RSS rule (`PredictSparseElimRss` per item), then the dense residuals in the serial order. Exactly `0` runs every stage in place, one after another (the serial order); `1` or unset = on; other values warn. Read once per process; `par::ScopedLever(Lever::EllN)` overrides it. Gated by `IntegralDescentParLnValidation`. |
| `HECKE_DESCENT_PARLN_CELLS=<N>:<n>[:full\|:no2],…` | **read-only measurement hook** (slot-24 PAR-LN): replaces `IntegralDescentParLnValidation`'s arms by the `PARLN_COST` measurement (serial, one worker, threaded; compared). Cost: the cells' level-N sparse stage three times (with `:full` the whole `AssembleDescentN` twice: predict the 2-adic piece's RSS first). Prints its `EFFECTIVE` line. |
| `ENGINE_GPU_SMITH2K=0` (+ `ENGINE_GPU_SMITH2K_MIN=<entries>`, `ENGINE_GPU_SMITH2K_VRAM_MB=<MiB>`, `ENGINE_GPU_SMITH2K_HOST_MB=<MiB>`, `ENGINE_GPU_SMITH2K_VERIFY=1`) | **the switches of an opt-in route (reclassified 2026-11-12 by S26 LEVERS-26: not rollback levers; `=0` is the host fallback of an opt-in device route, kept while that route exists — a card decision, unlike the CL-R2-retired `ENGINE_GPU_ELIM` / `_IMMA`), cannot change a value** (slot-24 PAR-GPU, `slot24/PARGPU_report.md`; `Integral/Descent/DescentSmithGpu.h`). Only under `ENGINE_DEVICE=gpu` (the thread's policy) does the 2-adic Smith LU (`ring2k::echelon_blocked`, u32 / u64) run device-resident (tiled when it does not fit); the default `cpu` never reaches CUDA. Exactly `0` keeps the host LU under `gpu` too; `1` or unset = on; other values warn once. `_MIN`: the size floor m·n (default 2^24); `_VRAM_MB`: caps the device budget (default: free memory − 512 MiB − 1/32 of the card); `_VERIFY=1` (or a `-DENGINE_VERIFY_DEVICE=ON` build): every device LU re-run on the host and compared, a difference throws. `ENGINE_GPU_SMITH2K_HOST_MB` (default 4096): the tiled route's host L store per phase (a larger value means fewer phases, i.e. fewer slab passes, and more RSS); the route declines when MemAvailable is below that + one panel + 2 GiB. `EFFECTIVE GPU_SMITH2K mode=… policy_gpu_calls=… device=… resident=… tiled=… slabs=… replays=… fallbacks=… declined_vram=… declined_host=… panels=… lookahead=… verified=… min_entries=… t_s=…` on stderr at exit when set or under `ENGINE_DEVICE=gpu`. **RSS** (audit L2 / L3, `s24-par-integrate2`): when the route would run for the calling thread, the descent's predictions (`PredictTreeLocalRss`, `PredictLocalRss` at ℓ = 2) add `smith_gpu::PredictHostRssBytes`: min(`_HOST_MB` + one panel, the whole L) + the 2 m·panel driver buffers + the pinned staging (at the device LU's panel `smithpar::kDevicePanel` = 128), and under `_VERIFY` the input twin m·n·elem (the verify mode doubles the matrix on the host: a diagnostic for small cells). Under `cpu` the term is 0 (predictions unchanged). **Since slot-24 PANEL-IMPL** the store term is dropped when the whole m × n window fits the device budget at the prediction (the plan would run the LU resident, so the store is never allocated; `_VRAM_MB` and a validation's column cap count). Consequence: Γ_0(1000), n = 20 predicts 36.47 GiB on the CPU; under `gpu` it predicted 40.73 GiB at the default `_HOST_MB` (refused at the 40 GiB ceiling; `_HOST_MB=3072` / `1024` admitted it) and now, on the 96 GB RTX PRO 6000 where every LU is resident, ≈ 36.7 GiB at the default `_HOST_MB` (admitted; `PANEL_report.md` §7). On a card where the LUs tile (e.g. the 16 GB RTX 5070 Ti) the store still counts and `_HOST_MB=3072` is still needed for that cell. A device exception other than a `CudaError` (an `ENGINE_CHECK`, `bad_alloc`) closes the device session before it propagates (audit L1). Gated by `DescentSmithGpuValidation`. |
| `HECKE_DESCENT_SMITH_GPU_CELLS=<N>:<n>[,…]` (+ `HECKE_DESCENT_SMITH_GPU_ARMS=gpu`) | **read-only** (slot-24 PAR-GPU): **adds** a timing arm to `DescentSmithGpuValidation` after its gate arms: `RunTreeLocalPieceN` at ℓ = 2 on the host and on the device (forced), compared; `PARGPU_CELL …` lines; `_ARMS=gpu` runs the device arm only. RSS: as `PredictTreeLocalRss`, plus the tiled route's L store (≤ `ENGINE_GPU_SMITH2K_HOST_MB`) when the matrix does not fit the device. Never a value. |
| `HECKE_EXZ2P2_FIXTURES=<path>[,<path>…]` | **read-only measurement hook** (slot-25 EXZ2-P2): replaces arm (M) of `HeckeZFreeBlockCrtValidation` by the listed fixture files (`EXPORTZ2` fixture format, checked read by read by the loader). A file with a Φ_cert block runs `mode=proven` only through `FreeBlockCrt`'s own re-certification (d^1 B = 0, Φ_cert^T d^0 = 0, det(Φ_cert^T B) = ±1; else `[Uncertified]`); a file without one (e.g. `exz2p2/dump_to_fixture.py` on a P1a dump, B = B_0) runs `lanes_only` (8 lanes: lane timings, the bound's bits, the a-priori prime count, no proof), plus the GPU lane route's residues with `ENGINE_DEVICE=gpu`. Prints `EFFECTIVE HeckeZFreeBlockCrtValidation arm=<default\|env> cells=<k>`. Cost: (311, 2), (23, 20), (1, 200) ≈ 6 s, ≈ 300 MiB CPU-only, ≈ 550 MiB with the GPU arm (whole process). Never writes. |

**The `EFFECTIVE` convention** (slot-14 WP-2, the vacuous-arm lesson). Every env-armed `_ALL` / `_CELLS` arm in
this table, and `HeckeHidaHeavyCellProbe`, prints one `EFFECTIVE <name> arm=<X> cells=<k>` line when it runs.
The line says which arm actually ran and over how many cells, so an env variable that was silently ignored can
be seen. Slot 14's own hooks print their equivalents: `HECKE_RING_LOEWY_EFFECTIVE`,
`EFFECTIVE HeckeLevelNValidation r3_cells=`, and `EFFECTIVE HeckeUEllStreamValidation default_*`. Every slot-16 hook in the table
prints one (`arm=CELLS`, `arm=NB3_FULL`, `arm=F1_RING`, `arm=F1_PMAX`, `arm=DEGEN`, `arm=R3K`, `arm=JOIN`, `arm=DUMP`, and the `u_ell=` / `join=` fields of
arm (T) and the lattice arm). Read that line before trusting a sharded or cluster run.


## Moved from CLAUDE.md at the slot-21 close (2026-10-07), verbatim — tiers with the per-slot additions, the owner-gated emitter / env-hook table, the EFFECTIVE convention

The text below was replaced in CLAUDE.md by the slot-21 close size diet (owner request 2026-10-07: keep CLAUDE.md ≤ 30 KB); each block is the replaced text of CLAUDE.md at `1088dcb3`, unedited.

### "Tiers" and "The catalogue" (CLAUDE.md lines 244–260 at `1088dcb3`)

```
**Tiers.** Every registered validation carries a tier (`fast` / `standard` / `slow`, printed by `--list`). `--all`
runs `fast` + `standard`; `--all-full` runs everything. **193** registered validations at the slot-21 close: **68** `fast`, **108** `standard`, **17** `slow`, so `--all` runs **176**; **123** of them are `Hecke*` names (`--list | grep -c ^Hecke` on the close binary, sha256 `a07b9d2a…`). Slot 21 added T1 `NumberFieldLllValidation` and WP-LIC `LicenceGuardValidation` (`fast`, ≈ 2.3 s / ≈ 1 s), P7 `HeckeLambdaQExpValidation` (≈ 7–9 s), T2 `NumberFieldRibetFieldValidation` (≈ 65 s with 8 threads; arm `NUMBERFIELD_RIBET_CELLS="691:12,691:200"`), P8 `HeckeLambdaModSymValidation` (≈ 24 s, 0.29 GB; arm `HECKE_LAMBDA_MSYM_ALL=1`), P9 `HeckeLambdaTwoVarValidation` (≈ 7.5 s; `HECKE_LAMBDA_TWOVAR_ALL=1`), P3 `HeckeLValueCoefficientRingValidation` (≈ 1.2 s; `HECKE_LVALUE_COEFFRING_HEAVY=1`), P2 `HeckeLValueEisensteinMeasureValidation` (≈ 6.2 s; `HECKE_LVALUE_EISMEAS_HEAVY=1`), P4 `HeckeLValueWildCharacterValidation` (≈ 5.3 s; `HECKE_LVALUE_WILD_HEAVY=1`), P5 `HeckeLValueIwasawaInvariantsValidation` (≈ 22 s; `HECKE_LVALUE_IWASAWA_HEAVY=1`) (all `standard`), and early slot 22 (LN23) `HeckeLevelNCurveValidation` (`standard`, ≈ 2.6 s, 1064 checks; `HECKE_LN23_HEAVY=1` = `(21929, 2)`); the nine arms all ran green at the slot-21 W1. Slot 20 added WP-MEAS `HeckeLValueMeasureValidation` (`standard`, ≈ 4.5 s, 220 checks with S1; 691 arm `HECKE_LVALUE_MEASURE_691=1`) and NB-4 `ConsoleServeAtlasValidation` (`standard`; `[SKIP] …: OC_BUILD_NOTEBOOK=OFF` in a default build). Slot 19 added WP-NF `NumberFieldValidation` (`fast`, ≈ 3.5 s), WP-LV `HeckeLValueValidation` (`standard`; extended by WP-LV2, WP-LIN, WP-BIL), WP-LC `HeckeLatticeModuleValidation` (registered `standard`, `slow` by owner ruling 2026-10-03; ≈ 125–150 s, ≈ 0.8 GB; full arm `HECKE_LATTICE_MODULE_FULL=1` ≈ 22 min, ≈ 2.9 GB), NB-2 `ConsoleReadOnlyTagValidation` (`fast`) + `ConsoleServeValidation` (`standard`; both `[SKIP] …: OC_BUILD_NOTEBOOK=OFF` in a default build), WP-HL `HeckeLambdaValidation` (`standard`, ≈ 7 s, ≈ 70 MB; 691 arm `HECKE_LAMBDA_ALL=1` ≈ 6.6 min, ≈ 0.15 GB, 224 checks). Any package that registers a validation,
a console verb / type / setting or a CLI token must regenerate the manual's tables (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`) in the
same commit, or that validation fails. The
`slow` tier: `HeckeBenchmarkSmoke`, `SymmetricPowerValidationSlow`, `EngineDeviceTrapValidation`, `HeckeUEllReachSlow`,
`HeckeExtKummerValidation`, `HeckeAtlasValidation`, `HeckeExtEndToEndValidation`, `HeckeDualityCoverageSlowValidation`,
`HeckeReductionCoverageSlowValidation`, `HeckeLocalityProbe`, `HeckeDicksonThetaCoverageSlowValidation`,
`HeckeDicksonThetaHeckeCoverageSlowValidation`, `HeckeHidaTowerSlowValidation`, `HeckeHidaHeavyCellProbe`,
`HeckeMixedFinalityValidation`, `HeckeRingLoewyDigitSlowValidation`, `HeckeLatticeModuleValidation` (slot 19, owner 2026-10-03). So **the Hecke acceptance gate
(`HeckeEndToEndValidation` + `HeckeBadPrimeValidation` + `HeckeBenchmarkSmoke`) needs `--all-full`, not `--all`** — or
run the three by name.

**The catalogue.** What each validation actually checks — check counts, tiers, timings, arm lists, the oracles it
compares against — is **`docs/validation-catalogue.md`**. Read it before touching a validation, and before assuming a
name means what it sounds like. (The six pre-existing non-Hecke validations are `mod_arithmetic_validation`,
`MatrixValidation`, `FlatMatrixValidation`, `BlockFlatMatrixValidation`, `SimplicialCohomologyValidation`,
`LocalSystemCohomologyValidation`.)
```

### "Owner-gated emitters and env interlocks (safety-critical)" (CLAUDE.md lines 262–294 at `1088dcb3`)

```
### Owner-gated emitters and env interlocks (safety-critical)

Four registered names can **write**, one variable selects the strict acceptance mode, and two validations are
interlocked on a run. Each is a no-op unless its environment variable is set, which is what keeps `--all` and
`--all-full` read-only. **Never set one of these (or any env hook) to "make a validation pass".**

| Env | Effect |
|---|---|
| `GOLDEN_EMIT=1 ./hacs GoldenEmit` (optionally `GOLDEN_OUT=<path>`) | regenerates `Golden/GoldenReference.inc`. **Owner-gated re-baseline**: every changed line must be explained object by object. |
| `GOLDEN_DUMP=<dir> ./hacs GoldenDump` | writes the before/after object dump of the re-baseline protocol ([X] §1.6 steps 1–4) to `<dir>/{index.tsv,texts.tsv,decompositions.txt}`; diffed by `docs/matrix-engine/tools/golden_explain.py`. |
| `GOLDEN_GEVT23` | **RETIRED** by the HZ-GOLD landing (slot 25, 2026-11-07; `docs/matrix-engine/rebaseline-s25-hzgold-addonly-gevt23-heckez.md`): it was the scratch interlock of slot-25 GOLD-PORT / HZ-GOLD while `kGEvt23InReference` / `kHZInReference` were false, adding the 97 G-EVT23 and 15 HZ tier-A points to a scratch `GoldenEmit` / `GoldenDump` only. Both gates are now `true` and in the reference, and the variable is no longer read. |
| `CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` | regenerates the `.expected` transcripts of `Console/scripts/`; refuses to freeze a script that does not exit 0. Changing an existing transcript is an owner-gated re-baseline. |
| `HECKE_DUMP_TAU=<dir>` | `HeckeTauDumpValidation` writes four τ / `ρ_n` files for the Lean checkers into `<dir>`, which must exist and must **not** lie inside the source tree (else `REFUSED`, exit 1); unset: `[SKIP]`. |
| `HECKE_DUMP_MEREL=<dir>` | **an emitter into scratch** (slot-20 L20-4, ruling O9): `HeckeLevelNValidation` writes `merel_N5_n2_p{2,5}.txt` (the C++ `HeilbronnOperator` at `(N, n) = (5, 2)`) into `<dir>` for `lean/tools/merel_dump_to_lean.py` → `GL2/Checkers/MerelData.lean`; rules as `HECKE_DUMP_TAU` (`<dir>` must exist outside the source tree, else `REFUSED`, exit 1; unset: one `[SKIP] MEREL_DUMP` line and the validation runs unchanged). **When set it replaces the validation's arms**: only the dump runs (`EFFECTIVE HeckeLevelNValidation arm=MEREL_DUMP cells=2 validation_arms=skipped`, one `MEREL_DUMP … dense_fnv64=0x…` line per file). |
| `HECKE_DUMP_SAT_CERT=<dir>` (+ `HECKE_DUMP_SAT_CERT_CELLS="n:ell:kmax,…"`, default `168:13:2,220:17:2,258:37:2`) | **an emitter into scratch** (slot-17 L17-2): `HeckeSatCertDumpValidation` (`fast`) writes one `satcert_n<n>_ell<ell>_b<k>.txt` per torsion-free certified `stable` block for `lean/tools/satcert_to_lean.py` → `GL2/Algorithms/SatCertData.lean`; `<dir>` must exist outside the source tree (else `REFUSED`, exit 1); a malformed cell is refused by position; unset: `[SKIP]`. Prints `EFFECTIVE HeckeSatCertDumpValidation arm=DUMP cells=<k>` and one `SAT_CERT_DUMP` line per file. Default list: 19 files, ≈ 14 min, 0.43 GB. |
| `HECKE_DUMP_HZ_CERT=<dir>` (+ `HECKE_DUMP_HZ_CERT_CELLS="N:n:ell[:K],…"`, default `1:10:691,1:22:103,1:22:2294797`) | **an emitter into scratch** (slot-25 HZ-EMIT): `HeckeZCertDumpValidation` (`slow`) writes the HeckeZ certificate files `hzcert_N<N>_n<n>_<K1|K2|K3>_l<ell>.txt` of the record `integral_hecke_structure/v1` for `lean/tools/hzcert_to_lean.py`; `<dir>` must exist outside the source tree (else `REFUSED`, exit 1); set-but-empty or malformed cells: `REFUSED`; unset: `[SKIP]`. Prints `EFFECTIVE HeckeZCertDumpValidation arm=<default\|cells> cells=<k>` and `HECKEZ_CERT_DUMP … byte_stable=yes … verdict=OK`. Default list: 8 files, ≈ 2 s. **(S26 Z1)** a cell `N:n:ell[:K]:full` (N > 1) builds the full record and also writes one file per p ∣ N, `<record id>.Up<p>.mat` (`schema=hz_up_matrix/v1`: header with the operator convention (the adjoint U_p, `prop:levelconehecke`(3)(d)), basis rule and FNV, r, F's proof; τ and M, or `tau_M=blocked(U_p): <refusal>` while the tree route at 2 / 3 refuses p ∣ N (until Z2); F over Z, exact decimal, by the free-model U_p; trailing `sha256=` of the preceding bytes), written twice and compared; the line gains `up_files=<k> up_refused=<k>`. (11, 0, full): 2 files, ≈ 1 s. |
| `HECKE_DUMP_EXZ2=<dir>` (+ the read-only `HECKE_EXZ2_CELLS="N:n[:p1/p2],…"`, default `1:10, 11:2`) | **an emitter into scratch** (slot-25 EXZ2-P1a): `HeckeZFreeBasisPairsValidation` (`standard`; arm (M)) writes the Iso_T carrier d^0, d^1, the K = 3 Dixon pairs, H_s = Φ_0^T T̃_T B_s and (dim C^1 ≤ 420) T̃_T on C^1 with its majorant into `<dir>/c<N>_<n>/` for `docs/implementation/slot25/exz2p1a/exz2p1a_check.py`; `<dir>` must exist outside the source tree (else `REFUSED`, exit 1); `HECKE_EXZ2_CELLS` set-but-empty or malformed: `REFUSED`. Prints `EFFECTIVE HeckeZFreeBasisPairsValidation arm=<default\|cells> cells=<k> dump=<on\|off>`. Since EXZ2-P1b `HECKE_EXZ2_CELLS` also replaces arm (M)'s cell of `HeckeZFreeBasisSatValidation` (read-only; `EFFECTIVE HeckeZFreeBasisSatValidation arm=… cells=…`). |
| `CLI_MANUAL_EMIT=<dir>` | **an emitter into scratch** (slot-18 WP-M): `CliManualCoverageValidation` (`fast`) writes the 19 generated include files of `docs/latex/cli_manual/` into `<dir>`, which must exist outside the source tree (else `REFUSED`, exit 1); prints `EFFECTIVE CliManualCoverageValidation arm=EMIT files=19`. Driven by `docs/latex/tools/gen_cli_manual_tables.sh <binary>`, which copies them into the tree. Unset: the read-only coverage check. |
| `GOLDEN_STRICT=1` | makes `GoldenRegressionValidation`'s **tier B** gate as well as tier A. Not an emitter; the strict acceptance mode. |
| `HECKE_LOCALITY_PROBE=1` | interlock on a *run*: without it `HeckeLocalityProbe` prints `[SKIP]` even under `--all-full`. |
| `HECKE_HIDA_HEAVY=1` (+ `HECKE_HIDA_HEAVY_CELLS`) | interlock on a *run* for `HeckeHidaHeavyCellProbe`; `(700, 691)` at `m = 2` peaks ≈ 33.5 GiB — **predict RSS first, rule 19**. |

All other env hooks (`HECKE_LVALUE_MEASURE_691=1` (S2 691 arm), `HECKE_LVALUE_HEAVY=1`, the slot-21 / 22 arms `HECKE_LVALUE_{COEFFRING,EISMEAS,WILD,IWASAWA}_HEAVY=1`,
`HECKE_LAMBDA_{MSYM,TWOVAR}_ALL=1`, `NUMBERFIELD_RIBET_CELLS`, `HECKE_LN23_HEAVY=1`, `HECKE_*_ALL`, `HECKE_*_CELLS`, `_U_ELL`, `_RECORDS`, `_JOIN_ONLY`, `HECKE_NEBENTYPUS_*`,
`HECKE_SAT_DEFECT_*`, `HECKE_LEVEL_N_*` (incl. the cap `HECKE_LEVEL_N_HOOK_RSS_CAP_GIB`), `HECKE_HIDA_*_CELLS`, `ENGINE_LADIC_WIDTH`, the rollback arms
`HECKE_U_ELL_LOW_RANK=0` / `HECKE_COSET_STREAM=0` / `HECKE_PARALLEL_SETUP=0` / `HECKE_RANK1_CLOSED_FORM=0`, …) are
**read-only** — they widen or replace an arm's cell list, never write and never change a value. Their full table,
with costs and RSS, is in **`docs/validation-catalogue.md`** ("Moved from CLAUDE.md at the slot-17 start").
`HECKE_NEBENTYPUS_NB3_FULL=1` (132 cells, ≈ 845–947 s, 6.5 GB) **runs at every slot close** (owner ruling 2026-10-01;
a close-window step).

**The `EFFECTIVE` convention** (slot-14 WP-2, the vacuous-arm lesson). Every env-armed `_ALL` / `_CELLS` arm, and
`HeckeHidaHeavyCellProbe`, prints one `EFFECTIVE <name> arm=<X> cells=<k>` line when it runs (slot 14's own hooks print
the equivalents `HECKE_RING_LOEWY_EFFECTIVE`, `EFFECTIVE HeckeLevelNValidation r3_cells=`, `EFFECTIVE
HeckeUEllStreamValidation default_*`), so an env variable that was silently ignored can be seen. **Read that line
before trusting a sharded or cluster run.** A census shard must read `refused=0` and `fallback:0`.
```

### Slot 22 VERB-3 (appended; no new validation name)

`ConsoleServeAtlasValidation` gains **arm (Q)**: `hacs --atlas --query <store.json> '<request JSON>'` (the `--serve-atlas` request handler run once;
owner decision O13) is compared with a served child on 11 requests (`info`, `cells`, `cell`, `system`, `systems` with filters, `not_found`, unknown op, missing `id`, malformed
JSON; frames equal up to `seq` / `perf`), exit codes 0 (`ok`) / 3 (`error`, `rejected`), refusals (missing store, one argument, `op close`, over-long, blank or multi-line request; the last two added by the Opus audit) exit 1 with empty
stdout. 429 -> **438 checks** on the 0.16 GB fixture run (5 s). Registered-name count unchanged (VERB-3 delta 0; `EXPECT_NAMES` untouched).

**Slot 22, BIN-3 (the degree-1 amalgam reader, package BIN-3 of `docs/implementation/slot22/L23_master_plan.md` §2 / §5, replacing
`census_l23_plan.md` v0.3's L23-2; report `docs/implementation/slot22/BIN3_report.md`).** Roster **214 = 70 / 126 / 18** (`--all` 196) on top of
BIN-2. Fragment `Registry/Slot22/BIN3.cpp`, `cmake/slot22/BIN3.cmake`.
- `L23AmalgamReaderValidation` — **`standard`**: ≈ 17 s, ≈ 80 MB, **2 195 checks** (default arm, 54 of the 200 frozen `ladic2.py` rows);
  `BIN3_ORACLE_ALL=1` (read-only hook, `EFFECTIVE L23AmalgamReaderValidation arm=BIN3_ORACLE_ALL cells=200`) arms all 200 rows: ≈ 147 s,
  6 821 checks. Audit R1: part (C) also asserts the level-1 modular-forms determinant sum rules (`v_ℓ det(T_p − c \| S_k)`, Hodge ≤ Newton) from the
  frozen `Bin3SumRules.inc` (`docs/implementation/slot22/bin3/gen_bin3_sumrules.py`, uses `fbin3/sumrules.py`). Files: `src/hacs/Orbifold/L23/AmalgamReader.{h,cpp}` (the library API `l23::read_lattice`, `h1_mod`,
  `oddn_row`, `rho_selfcheck`), `L23AmalgamReaderValidation.{h,cpp}`, the oracle `Bin3Oracle.inc` (generated by
  `docs/implementation/slot22/bin3/gen_bin3_oracle.py` from the tracked prototype outputs `docs/implementation/slot22/bin3/oracle/*.out`;
  `run_oracles.sh` reproduces those).
  - (A) the structural `ρ_n` (Taylor shifts, signed reversals, diagonals, Euclid words) = the dense `Sym^n` matrix of [C] `def:rhon`
    (52 blocks, ℓ = 2 at K = 64, 200, ℓ = 3 at K = 50, 120).
  - (B) the tracked `.out` files still equal `Bin3Oracle.inc` (200 `ladic2` rows, 51 `oddn` rows).
  - (C) `ladic2.py` **bit for bit** (`ladic2_line()` = the prototype line without `comm_v` / `s`): ℓ = 2 at cap 240 (R5(N=4), K = 256), ℓ = 3 at
    cap 160 (`engine::ladic`, K = 195); on every cell the census gates `rank_lambda1 = 2 dim M_{n+2} − 1`, `t1 = h0`, one unit in `ed_tell`,
    one `≥ cap` in `ed_eis_p`, no unit in `ed_tp`, the `c_p` rule ([C] `lem:cprule`), the Eisenstein floors, commuting `T_p`; ℓ = 3: ι² = 1,
    ι commutes, `dim Λ⁺ = dim S + 1`, `dim Λ⁻ = dim S`, the Eisenstein line in `Λ⁺`, `ed⁺ ∪ ed⁻ = ed`. Lines `(C) LADIC2 …`, `(C) PM_TELL_HALVES …`
    (a G-conj finding, not gated).
  - (D) `oddn_l2.py` bit for bit (odd n ≤ 101, K = 4) and the closed forms of [C] `prop:oddnltwo`, `lem:oddnsplit`, `prop:oddnhecke`(1)–(3),
    `lem:tellrank`; CONJ `prop:oddnhecke`(4) counted (`conj_T2_rank_one_idempotent=51`), not gated; the lattice reader at odd n ≤ 41.
  - (E) [C] `prop:ltwothreescalar`: `T_p − (1+p) = 0` on `H¹(Γ; Sym^n F_ℓ²)`, ℓ = 2, 3, n ≤ 40; `rank T_ℓ ≤ 2`; `lem:oddnsplit` at k = 2, 3.
  - (F) the adaptive rule: (2, 64) R3 → R4, (3, 40) 2 → 3 digits, logged `BIN3_ADAPTIVE …`, equal to direct runs.
  - (G) negative controls 8 / 8 (`r_∞` dropped from the bar formula, no precision guard, a tampered oracle row).
  - Last line `BIN3_READER ladic2_cells= oddn_cells= checks= failing= s= verdict=OK`. No setting, no golden line, no record.

**Slot 22, L23-1 (the orbifold record and driver, package L23-1 of `docs/implementation/slot22/census_l23_plan.md` v0.3 §6 as amended by
`L23_master_plan.md` v0.2: BIN-3 is the reader, the odd-n gates of §1; report `docs/implementation/slot22/L23_1_report.md`).** Roster
**215 = 70 / 127 / 18** (`--all` 197) on top of BIN-3. Fragment `Registry/Slot22/L231.cpp`, `cmake/slot22/L231.cmake`.
- `OrbifoldCampaignL23Validation` — **`standard`**: ≈ 65 s, ≈ 130 MB, **672 checks** (669 before the slot-23 L23-flake mask, KNOWN_ISSUES §7; 417 before the L23-1 audit repairs R1–R6). Files `src/hacs/Campaign/CampaignOrbifold.{h,cpp}`
  (the `orbifold = c_i` campaign section, `orbifold_cell/v1`), `CampaignOrbifoldValidation.{h,cpp}`; the oracles are BIN-3's frozen
  `Bin3Oracle.inc` / `Bin3SumRules.inc` (read, not regenerated).
  - (A) a spec without `orbifold` (and with `orbifold = off`) plans `n16_ell5_p2_r1` with an unchanged shape signature; the spec-time refusals
    (ell = 5 `not_implemented_in_this_build`, a `p` axis, `ext = true`, a non-default `coefficient_ring`, `jobs = 2`, a cell beyond the reader's
    precision range, an unknown model, a non-prime `orbifold_primes`); `RunCampaignSpec` refuses an orbifold spec.
  - (B) identity: fingerprint 0 / `orb_ell2_n10` at the defaults; `orbifold_primes`, `locality = budget=32`, `orbifold_m_target` give three distinct
    `_s<16 hex>` ids; a non-default mathematical setting changes the record hash input, not the values.
  - (C) the end-to-end campaign ℓ = 2, 3 × n = 0 … 60 (122 cells): every cell `ok`, `failed = fallback = refused = 0`; every record complete with
    `record_fnv1a64` = FNV(body); the reader columns = the frozen `ladic2.py` rows (60 / 60), the three level-1 sum rules (60 / 60), the frozen
    `oddn_l2.py` rows (30 / 30); the [C] `sec:oddnltwo` / [P3] §2 closed forms are the record's own G gates (3 809 evaluated, 0 failing),
    G-conj findings printed (0 at n ≤ 60). Since the audit repairs (4 319 gates): every gate names its source class (`C` / `R` / `LIT` / `UCT` /
    `cross-model` / `internal`, `CONJ` exactly on the G-conj gates; R2); the amalgam oracle `l23::h1_mod` ran on the 90 cells n ≥ 1 (ℓ = 2) /
    even n ≥ 2 (ℓ = 3) with its 450 cross-model `G` gates (`h⁰`, `h¹`, `rank T_ℓ`, `rank (T_ℓ − 1)`, `L_k`; R3); `e_cup_h0_h2_injective` on every
    ℓ = 2 cell with `h⁰ > 0` (R5); the hashed body carries no precision path and is unchanged when `rung` / `K` / `m` / `e_A` / `e_1` / `reruns`
    change (R4); every file carries `reader_path` and `provenance` (commit, binary sha256; R6); the triage reading per source class.
  - (D) `resume` skips all 122 cells; two cells recomputed give identical bodies, **compared raw** (S24 L23-H1: `orbifold_cell/v2`, the sum-rule oracle's wall time is the unhashed `timings_s.sumrule_oracle`; checked per body: one oracle gate, detail `-> resolved` without a time; a negative control: a different time moves the JSON but neither the body nor `record_fnv1a64`; KNOWN_ISSUES §7 closed; the resume counts `resumed_not_v2 = 0` there, and `= 1` on R1's planted `v1` fallback record, L23-H1 audit F2); `resume` over a planted complete `failed` record at
    (2, 3) **stops** there (R1: `stopped`, `failed = 1`, `ran = 2`, the planted `fallback` record at (2, 2) skipped, no n = 4 file, `failed`
    in `index.json` / `summary.tsv`, the CLI exits 2). (E) negative controls: `orbifold_m_target = 3` at (2, 10) is a
    `fallback` cell with an `_s` id; a tampered `ladic2.py` row is caught.
  - Last line `ORBIFOLD_L23 cells= ell2= ell3= gates= conj_findings= ladic2= sumrules= oddn= amalgam=<cells>/<gates> checks= failing= s= verdict=OK`. No setting
    registered, no golden line; the campaign prints `EFFECTIVE campaign arm=orbifold cells=<k> … refused=<r> fallback:<f> …`.

**Slot 22, L23-3 (the census validations of the orbifold section, package L23-3 of `census_l23_plan.md` v0.3 §6 with the scope of
`L23_1_audit.md` §7; predictions `docs/implementation/slot22/L23_3_predictions.md`, report `L23_3_report.md`).** Roster **217 = 70 / 128 / 19**
(`--all` 198) on top of L23-1. Fragment `Registry/Slot22/L233.cpp`, `cmake/slot22/L233.cmake`; oracles `Orbifold/L23/L233Oracle.inc`
(`docs/implementation/slot22/l233/gen_l233_oracle.py`, sha256 of every source) and BIN-3's `Bin3SumRules.inc`.
- `OrbifoldCensusL23Validation` — **`standard`**: ≈ 6 s, ≈ 45 MB, **812 checks** (770 before the L23-3 audit repairs, `L23_3_repairs_report.md`).
  - (A) the C++ sum-rule oracle `l23::sum_rule_oracle` against all 200 frozen `Bin3SumRules.inc` rows (`v det` of `T_ℓ`, `T_ℓ² − T_ℓ`,
    `T_p − (1+p)`, `T_p − (1+p^{n+1})`, `v(pⁿ − 1)`): `SUMRULE_FROZEN rows=200 agree=200`.
  - (B) `l23::h1_layers` at ℓ = 2, n = 1 … 24 and ℓ = 3, even n ≤ 36 against the independent `layers_proto.py` rows (`h⁰`, `h¹`, `dim H¹_Br`,
    `dim H¹_!`, `dim(H¹_! ∩ H¹_Br)`, `dim L`) and `mv_numpy.py` (`bredon_h1 = dim H¹_Br`); `dim T¹/ℓ = h⁰`; [R] Thm B(5) / C(1) / C(3) / E / Q10;
    [R] C(4) restated (`dim(T¹/3 ∩ H¹_Br) = dim T¹/3 − [n ≡ 4 mod 6]`, `L ⊄ T¹/3`, both OBSERVED); the `H¹_!` stability check is labelled
    vacuous (`dim H¹_! = 0` on every row).
  - (C) 50 `orbifold_cell/v1` cells (ℓ = 2, 3, n = 0 … 24, `ComputeOrbifoldCell`, no I/O): all `ok`; the (S) gates (8 per ℓ = 2 lattice cell,
    22 per ℓ = 3 one), the (B/!/L) gates on every layered cell — exactly 8 (ℓ = 2) or 12 (ℓ = 3, incl. the `G-conj`
    `t1_mod_3_leaves_br_iff_n4mod6`), + 1 (`layers_dim_t1`) when the reader certified; the MV rows (`h⁰…h³`, `rank Λ¹`, `t₁…t₃`, `dim H¹_Br`); schema and defaults.
  - (D) negative controls 7 / 7 (the oracle without `p^{k−1} a_{m/p}`, a tampered row, the reader with `r_∞` dropped at both primes, the layers
    with `r_∞` dropped and with a wrong `c(T)`, and the non-convex Jordan rank sequence `(3, 2, 0)` read as invalid by
    `l23::jordan_blocks_from_ranks`, audit M1). Last line `ORBIFOLD_CENSUS_L23 … verdict=OK`.
- `OrbifoldCensusL23SlowValidation` — **`slow`**: ≈ 56 s, ≈ 115 MB, **276 checks**. (E) the reader (`m_target` auto) and the oracle on every even
  n ≤ 200 at both primes, every sum rule incl. the ι halves (200 / 200); (F) the `C_I` (lat) reading of `IntegralHecke.h` (`uint32_t`,
  K' = 31 / 19, `ℓ^{e₁} IM(red)`) against the reader's `ed_tp`, `ed_eis`, `ed_tell` clipped at m, n = 10, 16, 22, 34, 46, 64 (12 / 12);
  (G) the layers against MV at n = 50 … 200; (H) the oracle at the four L23-4 calibration cells (n = 240, 500, 700, (3, 700)) against the
  records' divisor sums (4 / 4). Last line `ORBIFOLD_CENSUS_L23_SLOW … verdict=OK`.

## Rollback-lever register

Written by CL-0 (2026-10-30) to the owner's rule of 2026-10-30 (text: `CLAUDE.md`, "Rollback-lever retirement"; design:
`docs/implementation/slot24/CLEANUP_plan_1030.md` §3). A lever of slot S is retirable at the close of slot S+2, plus one
cluster/census run on the default route whose `EFFECTIVE` lines were read (`fallback:0`, `refused=0`). Slot closes used:
slot 21 2026-10-07; slot 22 CLOSE-T 2026-10-12 (`fd2382c6`); slot 23 W1-23 2026-10-19 (`59faa73d`). Landing dates from the commit history.
All arms are read-only in the sense of CLAUDE.md: they restore an older route and cannot change a value.
Not levers: `HECKE_TAU_WIDE` (`=0` refuses ell > 23170: a capability gate, B13), `ENGINE_TERNARY_F3` (an opt-in route, S25 LEVERS-25) and the 2026-09-06 tape / CUDA pass switches
(`ENGINE_ARENA`, `_BATCH`, ..., `ENGINE_CUDA_*`: diagnostics; `ENGINE_BATCH` is one of the eight pinned `EngineDeterminism` arms), among them
`ENGINE_HOST_THREADS` (`=0` runs the host fan-out serially: a 2026-09-06 tape switch and the console engine setting `host_threads`, a
thread-count choice like `ENGINE_THREADS=1`, not a superseded route; named here since S26 LEVERS-26, audit F2; its sibling
`ENGINE_HOST_ELIM_HOOK` of slot 23 is a lever, row below).
`ENGINE_KERNEL`, `ENGINE_BINARY_F2` (an opt-in route; reclassified by S24 CL-R2), `HECKE_DESCENT_SMITH_SIMD`, `HECKE_DESCENT_SMITH_PANEL` and the `ENGINE_GPU_SMITH2K*` switches (reclassified by S26 LEVERS-26) and the `*_CELLS` / `*_ALL` / `*_HEAVY` hooks are selectors, not rollbacks.

"Oracle role" = the old route is the independent oracle of a surviving validation (or still production in some regime), so
it stays in the default build and only the env arm retires. "legacy/ destination" = where the old route goes behind
`OC_ENABLE_LEGACY` at retirement.

| Lever | Landed (slot) | Eligible at | Oracle role | `legacy/` destination |
|---|---|---|---|---|
| `HECKE_U_ELL_LOW_RANK`, `HECKE_COSET_STREAM`, `HECKE_PARALLEL_SETUP`, `HECKE_RANK1_CLOSED_FORM` | 09-26 / 09-28 (13/14) | **RETIRED 2026-10-31 by CL-R1** (each `=0` refused in OFF builds; the `--bench` flags `--[no-]u-ell-low-rank`, `--[no-]coset-stream`, `--[no-]parallel-setup` removed in every build) | dense U_ell and the dense factoriser stay (production for ell not dividing N, non-SymN fibres, non-field rings); the serial loop is `for_each_index(..., false, ...)` (plumbing only) | `Hecke/legacy/HeckeOperatorLeversLegacy.h` (setters, `Scoped*`), `HeckeCosetTablesMaterialised.inc` (materialised coset tables), `HeckeUEllStreamValidation.cpp`, `HeckeUEllLowRankLegacyArms.cpp` |
| `HECKE_LEVEL_N_GEN_ORDER=as_built` | 10-03 (18) | **RETIRED 2026-10-30 by CL-G2** (refused in OFF builds) | none | `Hecke/legacy/HeckeLevelNGenOrderLegacy.inc` + `HeckeLevelNOrderLegacyArms.cpp` |
| `ENGINE_ELIM_SESSION`, `ENGINE_GPU_IMMA`, `ENGINE_GPU_ELIM` | 10-03 (<= 20) / 10-09 (22) | **RETIRED 2026-11-04 by S24 CL-R2** (slot-24 close K2; each `0...` refused in OFF builds, also at start-up in `main()`; one lever object each in `src/ModArithmetic/RetiredDeviceLevers.h`; evidence: the default-route GPU census cells of GL2_T2 and GL-1, `EFFECTIVE DEVICE_ELIM ... fallbacks=0`, `EFFECTIVE campaign ... refused=0 fallback:0`, quoted in `slot24/CLR2_acceptance.md` §1) | **all three old routes stay** (production / oracle exception): the per-program-mirror executor path (every program outside a session), the u32 device GEMM (`p >= 128`, `uint64_t`, `imma = 0`), the host / tape-panel elimination (`cpu`, `p > 127`, below the size floor); only the env arms retire | none (no code moves); the comparison arms are legacy arms (`RunLegacyArm`: `EngineElimSessionValidation` `session-off`, `volume-rollback`; `CudaImmaBitIdentityValidation` `D-policy-off`, `D-batch-policy-off`, `F-imma-off`; `CudaImmaElimValidation` `D-gpu-elim-off`); `cross_config.sh` arms `legacy-gpu-imma`, `legacy-gpu-elim`, `legacy-gpu-session` (one lever each) |
| `ENGINE_BINARY_F2` | 10-10 (22) | **not a lever: reclassified 2026-11-04 by S24 CL-R2 as an opt-in route (selector)**, like `ENGINE_KERNEL` (default off; `=1` turns the new `engine::binary` route on, nothing rolls back). Making it the default would be a separate measured package | — | — |
| `ENGINE_TERNARY_F3` | 10-12 (23) | **not a lever: reclassified 2026-11-07 by S25 LEVERS-25 as an opt-in route (selector)**, like `ENGINE_BINARY_F2` (default off; `=1` turns TER-1's `TritMatrix` route on, nothing rolls back) | — | — |
| `ENGINE_VNNI` | 10-12 (23) | slot-25 close, kept (route-parity arm of the ext H2H gate); **ENV ARM RETIRED 2026-11-12 by S26 LEVERS-26** together with `HECKE_FIELD_DIET` under (R-a) of `slot26/00-slot26-plan.md` §1 item 7 (`0` / `off` refused in OFF builds, also at start-up in `main()`; evidence: the ext default-route arm, PERF-VF §3 0.994 / 0.990 and W1-25 step 2 0.9700 / 0.9065 MET with both levers unset, value pass MATCH — **the weaker LEVERS-25 R4 standard, named**: not a census run in this register's letter; `slot26/LEVERS26_report.md`) | **production / oracle**: the u32 kernel is the route for p > 2^14 and without `avx512_vnni`; `set_vnni_path(VnniPath::Off)` stays for `VnniGemmBitIdentityValidation`; only the env arm retires | none (stays); `cross_config.sh` arm `legacy-vnni-off` (ON build) replaces `RelWithDebInfo@ENGINE_VNNI=0` |
| `ENGINE_VNNI2_FLOOR` | 11-07 (25) | slot-27 close (default recalibrated `2^18` → `2^20` by S26 LEVERS-26; the knob stays); **the qualifying default-route run must post-date `295c999b`** (the `2^20` default): a run on a `2^18` binary does not qualify (audit F5) | the slot-24 rule (`=0`) is no oracle; the routes are bit-identical by construction | none |
| `ENGINE_GPU_LEAN`, `L23_TERNARY_F3` | 10-12 / 10-13 (23) | **ENV ARM RETIRED 2026-11-07 by S25 LEVERS-25** (`0…` / `0` refused in OFF builds, at start-up in `main()`; evidence `slot25/LEVERS25_brief.md` R2 (GL2_T2: 20 default-route GPU census cells, `DEVICE_ELIM … fallbacks=0`) and R1 (DEEP-1: 196 `EFFECTIVE l23_ternary_f3=on source=default`, `BIN3O1_ROUTE … fallback=0`)) | **both old routes stay** (production / oracle): a memory-class-only program on the device is the route inside every elimination session; `Ops3<1>` is `TernaryF3Validation` (2)'s comparison. `ENGINE_GPU_LEAN` became an `EnvArmRetiredLever` (`RetiredDeviceLevers.h`), its validations switch it by `Scoped`, not by the env | none (no code moves) |
| `L23_BIN3O1` | 10-16 (23) | **ENV ARM RETIRED 2026-11-07 by S25 LEVERS-25** (`=0` refused in OFF builds; evidence R1, DEEP-1: `EFFECTIVE l23_bin3o1=on source=default` in 12 220 / 12 220 logs, 11 878 of them ℓ = 2, 12 220 `BIN3O1_ROUTE … fallback=0`) | **oracle**: the old route is `L23Bin3o1Validation`'s comparison (F10); only the env arm retires | none (stays) |
| `L23_RING2K`, `L23_MOD3K`, `L23_F3L` | 10-13 / 10-16 (23) | slot-25 close; **deferred to slot 26 by S25 LEVERS-25** (no default-route L23 orbifold census run after landing: only 20 audit re-runs `s24/l23h1*/rerun`; `L23_F3L`'s orbifold half is in no census run); **deferred again to the slot-27 close by S26 LEVERS-26** (the L23 n ≤ 1000 run, owner F2, was not launched) | **oracle**: the old routes are the oracles of `OrbifoldRing2k` / `OrbifoldMod3k` / `OrbifoldF3l` (F10); only the env arm retires | none (stays) |
| `HECKE_RHO2_STREAM`, `HECKE_IOTA_STREAM` | 10-16 (23) | **ENV ARM RETIRED 2026-11-07 by S25 LEVERS-25** (`=0` refused in OFF builds; evidence R2, GL2_T2: 40 C1a census cells, `route 2 streamed:` 5460 / materialised 0, `[iota] compute enter (streamed)` 40 / 40) | materialised memo stays under low-rank (B10); the materialised ι route stays (`ScopedIotaStreaming(false)`) | none (stays) |
| `HECKE_PRECISION_REUSE`, `HECKE_FORMS_FASTMUL` | 10-16 / 10-17 (23) | **ENV ARM RETIRED 2026-11-07 by S25 LEVERS-25** (`=0` refused in OFF builds; evidence R3, PHASE2 C2574 / C2678: `EFFECTIVE HECKE_PRECISION_REUSE levels=derived source=default`, `refused_cells=0`, the sat cells' forms stage on the default product) | **oracle**: per-K runs and the naive product (A7); only the env arm retires | none (stays) |
| `HECKE_MODULE_STREAM`, `HECKE_MODULE_EVAL`, `HECKE_MODULE_PARALLEL`, `HECKE_RHO_SIMD`, `HECKE_ROUTE2_SHARED_MEMO` | 10-17 / 10-18 (23) | **ENV ARM RETIRED 2026-11-07 by S25 LEVERS-25** (`=0`, and `HECKE_RHO_SIMD=scalar`, refused in OFF builds; CL-O landed in slot 24; evidence R4, HZ-RUN passes 1 + 2: 141 cells `EFFECTIVE campaign arm=hecke_structure … refused=0 … failed=0`, the cell shape's reach on each module route shown by `slot25/LEVERS25_brief.md` §2; and R3) | `compute_module_legacy` **stays in every build** as `HeckeModuleStreamValidation`'s entrywise comparison of C, H, A, Θ_eq (CL-O: (R) proves the stream route, the legacy comparison pins the basis-dependent objects); the G2-F evaluation, the serial assembly, the G2-D chunks and the scalar ρ fill (production off x86) stay | **Decision: moving `compute_module_legacy` to `Hecke/legacy/` is a slot-26 package.** `compute_module_legacy` -> `Hecke/legacy/`: **not moved** by LEVERS-25 (proposed as its own package, slot 26) |
| `HECKE_FIELD_DIET` | 10-20 (24) | **ENV ARM RETIRED 2026-11-12 by S26 LEVERS-26** with `ENGINE_VNNI` (same (R-a) evidence and standard as the `ENGINE_VNNI` row; `0` refused in OFF builds, also at start-up) | the undieted route stays (`ScopedFieldDiet(false)`: `HeckeThetaRssDietValidation`, `HeckeExtDeterminismValidation`); only the env arm retires | none (stays) |
| `HECKE_MODULE_MT`, `HECKE_MODULE_LEAN_PEAK`, `HECKE_FORMS_NTT_CACHE`, `HECKE_FORMS_NTT3`, `HECKE_SAT_PERF` | 10-20 ... 10-23 (24) | slot-26 close; **deferred to the slot-27 close by S26 LEVERS-26** (the qualifying census sat run, C1K-b2 = owner F1, did not run in slot 26) | NTT_CACHE: the G2-X builders stay (route where FNTT does not apply, A7 / A11); NTT3=0 only restores a refusal | per lever |
| `HECKE_DESCENT_TREE`, `_TREE_PAIR`, `_GOOD_SPARSE`, `_GOOD_DENSE`, `_SMITH_BLOCKED`, `_SMITH_MT`, `_SMITH_F2_MT`, `_PAR_ASM`, `_PAR_ELL`, `_EMBED_MAP`, `_PAR_LN` (all `HECKE_DESCENT_*`) | 10-25 ... 10-27 (24) | **ENV ARMS RETIRED 2026-11-12 by S26 LEVERS-26** (`=0` refused in OFF builds, also at start-up in `main()`; evidence HZ-RUN pass 3 (Z4): `EFFECTIVE HeckeZ descent …` in 453 / 453 logs, each with twelve `source=default`, every `EFFECTIVE campaign arm=hecke_structure` line `rejected=0 refused=0 failed=0`; `slot26/LEVERS26_report.md`) | **all old routes stay** (oracle / production): `SmithFormOracle` (C-13), the dense Iso^(ℓ) and pair routes, the shipped C_7 good prime (odd n), the serial Smith / echelon (= `ENGINE_THREADS=1`), the serial assembly; reached through their `Scoped` overrides | none (stays) |
| `HECKE_DESCENT_SMITH_PANEL` (`=128`) | 10-27 (24) | **not a lever: reclassified 2026-11-12 by S26 LEVERS-26 as a tuning knob (selector)**: every width in [1, 4096] is valid and value-neutral; `128` / `64` are two of them | — | — |
| `ENGINE_GPU_SMITH2K` (+ `_MIN`, `_VRAM_MB`, `_HOST_MB`, `_VERIFY`) | 10-27 (24) | **not a lever: reclassified 2026-11-12 by S26 LEVERS-26** as the switches of an opt-in route (`ENGINE_DEVICE=gpu` only): `=0` is the host fallback of an opt-in device route, kept while that route exists; a card decision (LEVERS-26 plan), not a rule — unlike `ENGINE_GPU_ELIM` / `_IMMA` / `ENGINE_ELIM_SESSION`, same shape, which CL-R2 retired on default-route GPU census cells; the `EFFECTIVE GPU_SMITH2K … fallbacks=` line would let a GPU descent census run qualify it if the owner prefers retirement (audit F3) | — | — |
| `ENGINE_AVX2_PAIR`, `HECKE_MODULE_TILE_WORK` | 10-27 (24) | slot-26 close; **deferred to the slot-27 close by S26 LEVERS-26** (`ENGINE_AVX2_PAIR`: no default-route run on an AVX2-only machine; `TILE_WORK`: no census sat run; both owner F1) | per lever | per lever |
| `ENGINE_HOST_ELIM_HOOK` (`=0`: the cone / ι certificates do not bind the elimination's inner parallel hook) | 10-12 (23) | slot-25 close; **missing from this register until S26 LEVERS-26** (found by its completeness check); **deferred to the slot-27 close** (no default-route run was read for it; candidate: a census run with cone / ι certificates on > 1 thread) | production at one thread (the serial elimination) | per lever |
| `HECKEZ_LOCAL_PAR` (`=0`: the slot-25 serial HZ-LOC route of `Integral/HeckeZLocal.cpp`, byte for byte) | 11-08 (26, Z9) | slot-28 close | **oracle**: the serial route is `HeckeZLocalParValidation`'s comparison route (`ScopedParRoute`), so it stays; only the env arm retires | none (stays) |

Tokens added to the register by CL-0 (absent from CLAUDE.md's list before): `HECKE_FORMS_FASTMUL`, `HECKE_PRECISION_REUSE` (A7);
`HECKE_RHO2_STREAM`, `HECKE_IOTA_STREAM`, `HECKE_LEVEL_N_GEN_ORDER` (B13); `L23_RING2K`, `L23_MOD3K`, `L23_BIN3O1`,
`L23_TERNARY_F3`, `L23_F3L`, `ENGINE_VNNI`, `ENGINE_BINARY_F2`, `ENGINE_TERNARY_F3`, `ENGINE_GPU_IMMA`, `ENGINE_GPU_ELIM`,
`ENGINE_GPU_LEAN`, `ENGINE_ELIM_SESSION` (planner-found). The old CLAUDE.md enumeration is kept verbatim in
`implementation/slot-history.md`, "Moved from CLAUDE.md at 2026-10-30 (CL-0 ...)".
