# Architecture detail

The long per-module prose that used to live in `CLAUDE.md`'s Architecture section, moved out
verbatim so the per-session context header stays short. Nothing here has been edited.

`CLAUDE.md` keeps a condensed paragraph per layer plus the hard rules (the one-way dependency
guards, the two families of switches, the assertions policy); this file keeps the full text.

Companion files: `docs/validation-catalogue.md` (what every validation checks),
`docs/implementation/slot-history.md` (the slot-by-slot programme history),
`docs/performance-reference.md` (benchmark tables and thread scaling),
`src/ModArithmetic/ENGINE_API.md` (the binding engine contract: invariants, structure
tags, layouts, elimination, the tape §10, the device layer §11–§12),
`src/hacs/Hecke/README.md` (the Hecke module map: file → contract section,
matrix-level definitions, the full validation list),
`docs/latex/gl2_contract.tex` ([C], the binding mathematical contract),
`docs/implementation/hecke_extensions_implementation_plan.md` ([X]),
`docs/console/00-console-interface-plan.md` ([P], the console plan).

---

#### Matrix engine (Phase 2) — `namespace engine`

Since matrix-engine Phase 2 the dense arithmetic and the elimination of `FlatMatrix` and
`BlockFlatMatrix` no longer hand-roll their inner loops: they hand **non-owning views of
`flat_data_`** to a layout-aware kernel layer. Nothing above the substrate changed, and no
computed value changed — the contract is bit-identity, not "close enough".

- **`ModCtx.h`** (`engine::ModCtx<Elt>`) — a per-modulus context built once and passed by
  `const&`: Barrett/Shoup/Montgomery-64 forms, `batch_inv`, and `k_max`, the number of products
  that may be accumulated before a reduction is forced.
- **`DenseBuf.h` / `DenseView.h`** — owning buffer and non-owning view with an explicit `ld`,
  layout and structure tags (`UpperUnitri`, `SignedAntiDiag`, …).
- **`Kernels.h/.cpp`** (`engine::kernels`) — `gemm`/`gemm_nt`/`gemv`/`axpy`/`scal`/`trmm`/
  `transpose`, all four layout combinations resolved by view flags, `u64` delayed accumulation
  with k-blocking at `min(k_max, 256)`, an 8×16 register-blocked outer-product microkernel with
  **runtime AVX-512 dispatch** and a portable fallback.
- **`DenseElim.h/.cpp`** (`engine::elim`) — blocked **in-buffer** PLU with a 32-wide Crout base
  panel; RREF as `U_1^{-1} * U`; rank profile, pivot columns, optional transform, and the derived
  `kernel` / `image` / `solve_multi_rhs` / `complement_basis` with the **same basis-choice rules**
  the legacy code used (golden tier B gates exactly that).
- **`RefLinAlg.h/.cpp`** (`engine::ref`) — the naive in-tree oracle the kernels are checked against.
- **`ENGINE_API.md`** — the binding contract: invariants, structure tags, the k-blocking overflow
  bound (§5), what layouts to pass (§6), and elimination (§8). Read it before touching a kernel.

**Bit-identity is by construction**: products of canonical residues are accumulated exactly
(`uint64_t` for `Elt = uint32_t`, `unsigned __int128` for `uint64_t`) and reduced once per k-block,
so reassociation, register blocking, vectorisation and the CPU path chosen cannot move a bit.
The reduction epilogue uses an FP64 quotient estimate for `p >= 2^13`, corrected by an integer
compare-and-subtract against a proved ±1 bound and re-derived by an `ENGINE_DEBUG_CHECK` in
non-`NDEBUG` builds — a deliberate, exact, documented exception to the "all arithmetic is integer"
convention below.

**Two rollbacks, both preserved:**
- `ENGINE_BACKEND=legacy` — runtime, no rebuild; sends every retrofitted path (products *and*
  elimination) back to the pre-Phase-2 loop. `engine::elim::ScopedLegacy` is the thread-local
  equivalent, used by the validations and the `--bench micro` legacy arm. **Since S24 CL-L2 the whole legacy route is
  compiled only with `-DOC_ENABLE_LEGACY=ON`** (`src/ModArithmetic/legacy/`: `BlockFlatMatrix.{h,cpp}`,
  `DenseElimLegacy.inc`, `FlatMatrixLegacy.inc`, `MicroBenchLegacy.inc`; `src/hacs/legacy/`:
  `EquivariantCohomologyOnKLegacy.inc`, `SimplicialCohomologyLegacy.inc`; `Hecke/legacy/`: `HeckeOperatorOnKLegacy.inc`,
  `HeckeInvolutionLegacy.inc`); an OFF build refuses `ENGINE_BACKEND=legacy` (exit 1).
- `cmake -DENGINE_SHADOW_LEGACY=ON` — compile time; runs **both** routes on every call and throws
  `std::logic_error` on the first differing entry. `GoldenRegressionValidation` under
  `GOLDEN_STRICT=1` is green on that build. **Since S24 CL-L1 it needs `-DOC_ENABLE_LEGACY=ON`**
  (`FATAL_ERROR` otherwise): the comparison code lives in `src/ModArithmetic/legacy/ShadowLegacy.inc`,
  `src/hacs/legacy/EquivariantCohomologyOnKShadow.inc` and
  `Hecke/legacy/HeckeOperatorOnKShadow.inc`, reached from one-line `#ifdef ENGINE_SHADOW_LEGACY` hooks.

Not retrofitted (deliberately, see plan §11.6): `operator+`/`-` between a scalar (`αI`) and a
general matrix, `image()`/`flat_image()`/true-RREF assembly, `Matrix::operator*`, and
`BlockFlatMatrix::_block_gaussian_elimination`'s *orchestration* (only its per-block operations
were rerouted) — that last one is Phase 3's `BlockBuilder`.

**The composite modulus `Z/ell^k` (hecke-extensions slot 8, E8 items 2–3; `ENGINE_API.md` §13).**
`ModCtx<Elt>::prime_power(ell, k)` declares a ring (`is_field() == false`, `ell`, `k`, `p = ell^k`,
a fixed `std::array` table of `ell^v`; 208 / 608 bytes for `uint32_t` / `uint64_t`, still trivially
copyable; `init(p)` resets the ring members). Everything modulus-only (§13.2: `mul` / `add` /
Barrett / Shoup / Montgomery-64 below `2^63`, `U64_Wide` for `ell = 2` and above, GEMM / GEMV /
AXPY, the tape's arithmetic nodes) runs unchanged; every **field-only** entry point (§13.3: `pow`,
`batch_inv`, `elim::rref` / `column_rank_profile` / `rref_with_transform` / `kernel_basis` /
`inverse` / `solve_multi_rhs` / `complement_basis`, `blk::rref`, `tape::rref`) `ENGINE_CHECK`s
`is_field()`; `inv` is unit-only (the extended Euclid throws on a non-unit). The composite-only
entry points (each `ENGINE_CHECK(!ctx.is_field())`) are `elim::howell` (valuation pivoting: the
leftmost column, the minimal valuation, the topmost row; the Howell closure rows), `kernel_module`,
`image_module`, `solve_multi_rhs_module` (the solution reduced modulo the kernel), `length`,
`invariant_factors` (the Smith step of §13.6 — **not** the Howell pivot valuations: `rowspan[[2, 1]]`
over `Z/4` has pivots `(1, 1)` and is `Z/4`), `cyclic_decomposition` / `cyclic_coordinates` (the
M3 basis rule, [E] `sec:ring` (c1)–(c5)); the oracle is `ref::howell`. The composite path is
selected by `is_field()` alone, so the `F_ell` path is byte-identical (R21). §13.7: `BlockMat` /
`BlockBuilder` take a `ModCtx` (the `Elt p` forms delegate on `ModCtx(p)`), `blk::gemm` / `add`
refuse mixed rings, and a tape replay never crosses the declared ring (`Executor.cpp`). There is no
block or tape Howell form (the composite eliminations are dense), and no CUDA change.

#### Arbitrary `k` — native widths and the (C2) digit induction (hecke-extensions slot 11, WP-12, WP-18a, WP-18b)

**F-1 / F-2** (WP-12). `ModCtx::mul_prep(w)` / `mul_prepped(x, w')` — a reused-operand pair, `== mul(x, w)`
bit for bit: under `U64_Montgomery` (odd `p < 2^63`) `w' = w·R mod p` and one `mont64_reduce` per
product; under `u32` and `U64_Wide` `w' = w` and `mul_prepped` is `mul`, so the `u32` code is unchanged.
`DenseElim.cpp`'s composite section applies every row / column factor through the pair (Howell's
`row_sub_scaled`, the pivot-row scaling, the closure row, the Smith multipliers); one-shot products stay
on `ctx.mul`, which itself is **not** changed (a two-REDC one-shot measured slower than `%`); the field
route and `RefLinAlg` untouched; ≈ 1.35–1.5× on `u64` Howell (indicative). `hecke::ExactKthRoot` tests
primality by deterministic Miller–Rabin (`hecke::IsPrimeU64`, the first 12 prime bases, exact below
`2^64`); the preferred route: **the ring travels as `(ell, k)`** —
`LocalSystemSimplicialComplex::declare_coefficient_ring(ell, k)` (checked `ell^k ==` the modulus,
overflow-checked), read by `EquivariantCohomologyOnK::init_coefficient_ring` in place of the derivation
(an `ENGINE_DEBUG_CHECK` confirms they agree); `SL2ZBoundaryPair` declares its ring. A latent UB
(`1 << 65` in `ExactKthRoot(m, 1)`) found by UBSan and fixed. `ModCtxMontgomeryPairValidation`,
`CoefficientRingKthRootValidation` (`fast`).

**The native `u128` layer** (WP-18a; `ENGINE_API.md` §13.12.9). `ModCtxU128.h`: `engine::u256` (two
`u128` limbs), `detail::mul_wide128`, a construction-only 256-bit division, `ModTraits<u128>`,
`is_composite_only<Elt>`, and `ModCtx<u128>` as a full specialisation — `prime_power` only (odd
`ell < 2^64`, `k ≥ 2`, `ell^k < 2^127`), Montgomery-128 `redc` / `mul`, the F-1 pair, Hensel `inv`, the
§13.4 members, a tight `k_max`; no field constructor, `pow` or `batch_inv`, so a field use does not
compile. `gemm<u128>` (scalar, `u256` accumulation, k-blocked at `min(k_max, 256)`), `gemv`,
`dot_delayed`; the §13.6 entry points instantiated with their bodies unchanged (the F-1 interface is
what makes that possible); `ref::naive128` and `ref::{gemm, gemv, trmm, transpose, howell,
invariant_factors}<u128>` the oracle; `BlockPool`'s hash mixes both 64-bit halves of a 16-byte entry
(other widths byte-identical). `DigitWord.h`: `engine::DigitWord<W>`, `W ∈ {uint32_t, uint64_t,
u128}` — `Word`, `Ctx`, `Wide`; `digit_exponent(ell)` = the largest `m` with `ell^m < 2^{bits−1}` (0 when
`ell² ≥ 2^{bits−1}`); `mul_wide`, `split` (Knuth D on 64-bit halves at `u128` since `f90a9ee`; the
restoring loop kept as `split_restoring`, its oracle), `mac_split`, `widen` / `narrow`; the word entry
points forwarded verbatim, so an `L = 1` digit run *is* the shipped direct route.
`EngineU128CompositeValidation` (`standard`, 26 587).

**The (C2) digit induction** (WP-18b; `ENGINE_API.md` §13.11, written as contract before the code).
`LadicInduction.h` (`engine::ladic`, header-only): `DigitLayout<W>` (`L = ⌈K/m⌉` planes fixed at
construction), `Ring<W>` (lazy-carry convolution on the native double word for `u32` / `u64` digits,
schoolbook at `u128`; valuation, exact shifts, Newton unit inverse, window extraction), `LadicMat<W>`
(`from_word` / `to_word` / `truncate` / `transpose` / `ell_digits` / `serialise`), and the entry points
`smith_lift`, `howell`, `kernel_module`, `image_module`, `length`, `solve_multi_rhs_module`,
`invariant_factors`, `cyclic_decomposition`, `cyclic_coordinates`, `stopping_rule`, `multiply`,
`convert`. **(L1)** (§13.11.3, proved; re-derived by the WP-14 review): with `U1 Ā V1 = diag(ell^{s_i}) ⊕ 0`
over `R_{k1}`, any lifts give the pivot block `D·W`, `W ≡ I mod ell`, and a Schur complement
`ell^{k1} S'`; the elementary divisors of `A` mod `ell^K` are `{ell^{s_i}} ∪ {ell^{k1+t_j}}`. The level
driver realises it row side only: the window `floor(active / ell^c) mod ell^k` eliminated in word
arithmetic by valuation pivoting (smallest valuation, leftmost column, topmost row), the pivot sequence
replayed at `K` in place, three `ENGINE_CHECK`s (pivot valuation, divisibility, the level's exit
`S = ell^{k1} S'`) so a divergence throws rather than returns. Every derived entry point returns
exactly the §13.5–§13.6 object. Domain `2 ≤ ell < 2^31`, `K ≥ 2`, no engine cap on `K`; `W = u128` needs
`ell` odd. `LadicRef.h` (`engine::ref::ladic`): an independent base-`ell` single-digit arithmetic with
`howell`, `kernel_module`, `smith_exponents`, `multiply`. `EngineLadicInductionValidation` (`standard`,
1888) runs the **owner's width oracle matrix** (§13.11.7): 1 × 32 / 64 / 128 and **2 × 32 vs native
`u64`**; **4 × 32 and 2 × 64 vs native `u128`**; cross-width agreement plus the base-`ell` oracle beyond
`2^127`; truncation; the certificate `U A V = diag(ell^s) ⊕ 0`; and the pipeline's own `d^q` at
`(10, 691)` over `Z/691^6` and `(30, 5)` over `Z/5^20`. Indicative cost (§13.11.9): ≈ 3–4× the native
route at `(128, 5)` over `Z/5^26`, structural (canonicalisation, back-substitution); levers recorded.

#### Block model (Phase 3) — `engine::BlockMat` / `engine::blk`

Phase 2 made the *arithmetic* fast; Phase 3 removed the *orchestration* that was issuing it in
millions of tiny pieces. The pipeline no longer assembles matrices cell by cell into
`BlockFlatMatrix`: it declares a block grid, writes **one call per block**, and hands the finished
object to block kernels. Contract: `src/ModArithmetic/ENGINE_API.md` §9.

- **`BlockPool.h`** (`engine::BlockPool<Elt>`) — a content-addressed, immutable, refcounted store
  of dense blocks shared by every `BlockMat` built on it. `intern()` returns the id of an existing
  entry with the same entries (full compare on hash hit; layout is not part of the identity), so a
  `ρ_n(g)` recurring across simplices is stored once. Entry addresses are stable (`std::deque`), and
  relayout twins are memoised. No hash container anywhere on a result path (audit §6.5(5)): the
  pool's table is a hand-rolled chained vector, the kernels' CSE caches are `std::map`.
- **`BlockMat.h`** (`engine::BlockRef` / `BlockMat` / `BlockView` / `BlockBuilder`) — a `BlockRef`
  is `alpha*I + beta*M^(T?)` over a pool window, with `kind ∈ {Zero, Scalar, Dense, Affine}`
  canonical from `(alpha, beta)`; so `I`, `-M`, `I-M` and the `A_Zq` pencils
  `β_lhs·I − β_rhs·M` are each **one ref with no data of their own**. `BlockMat` is an immutable
  prefix-sum grid plus a block-CSR pattern, sorted and insertion-order-independent;
  `BlockBuilder` declares the grid up front and offers `set` / `accumulate` / `set_dense` /
  `intern_dense` / `compose`.
- **The L1 contract (`nbc == 1`).** A `BlockMat` with **one block column** over the row partition
  `(d_V, …, d_V)` *is* the pipeline's flat cochain layout: the flat index of component `k` of
  simplex `s` is `row_off[s] + k = s*d_V + k`. `BlockMat::to_flat` / `from_flat` are now the
  **single source of truth** for that layout (plan item 7.20) — the three hand-written
  `s*d_V + k` loops that used to spell it out in `EquivariantCohomologyOnK.cpp`,
  `HeckeOperatorOnK.cpp` and `Matrix.cpp` are gone.
- **`BlockKernels.h`** (`engine::blk`) — pattern-driven `gemm` with `(alpha, beta)` constant
  folding (scalar×scalar touches no data) and CSE on data windows, `gemm_dense` for multi-vectors,
  `add` / `scale` without data work, `equal` **as mathematical matrices** (any grids, kinds,
  layouts), `materialise_rows/cols`, and a structural (metadata-only) transpose.
- **`BlockElim.h`** (`engine::blk`) — a left-looking block-column panel driver over `DenseElim`
  keeping one fully reduced RREF prefix, so the multipliers are the input's own blocks, gathered
  structurally: structural zeros cost nothing and `I` / `αI` pivot blocks are diagonals with no
  data. On top of it `kernel_basis`, `image_basis`, `factor_basis` and `solve_multi_rhs`, all
  producing the **same D5b bases** the legacy code did (golden tier B gates exactly that).

**The consumers now live on it.** `EquivariantCohomologyOnK` assembles `A_Cq` / `A_Zq` with
`BlockBuilder` and computes and *stores* `C_eq`, `Z_eq`, `B_eq`, `H_eq` and `P_q` as block objects,
exposed by `block_pool()`, `block_row_dims(q)`, `A_C_block(q)`, `A_Z_block(q)`, `C_eq_block(q)`,
`Z_eq_block(q)`, `B_eq_block(q)`, `H_eq_block(q)`, `P_block(q)`; the `get_*_bases_fm()` accessors
keep their signatures and legacy shapes and materialise lazily. `HeckeOperatorOnK` holds
`Θ^{(q)}` as an `N_q × N_q` `BlockMat` over the τ-table's `(σ, σ_k)` pattern — the fused route and
route 2 are two predefined programs over that pattern, compared with `blk::equal` — exposed by
`Theta_block(q)` / `block_pool()`, with `get_Theta_flat_matrices()` kept as a lazily materialised,
cached `to_dense` shim for `HeckeCrossChecks`, `HeckeOperatorFamily`, the JSON writer and the
golden harness. `HeckeCrossChecks`, `InducedLocalSystem`,
`EquivariantCochainComplexMorphismOnK` (M1/M3 as block GEMMs, contract B6 preserved) and
`SimplicialCohomology` followed.

**Both rollbacks now cover the consumers, not just the substrate.** `ENGINE_BACKEND=legacy` runs
the pre-Phase-3 dense arm of `EquivariantCohomologyOnK` and `HeckeOperatorOnK` (kept verbatim, with
its scalar arithmetic routed through `ModCtx`) and rebuilds the block objects from its output;
`cmake -DENGINE_SHADOW_LEGACY=ON` (with `-DOC_ENABLE_LEGACY=ON`, S24 CL-L1) runs **both** arms and compares dims, C/Z/B/H, `P_q`,
`Θ_flat`, `Θ_eq`, `A^{(q)}` and the certificate counters entrywise. The validations get the same
switch in-process, per class, via `EquivariantCohomologyOptions::ScopedLegacyCohomologyPath` and
`HeckeOperatorOptions::ScopedLegacyHeckeOperatorPath`.

**`Matrix` is retired from the pipeline.** `SimplexRelation::M` is a `FlatMatrix`, and no pipeline
TU includes `Matrix.h` directly; `Matrix` / `Matrix64` survive only for `MatrixValidation` and
`HeckeModuleDecomposition` (`d_q ≤ ~20`, 0.004 % of runtime — explicitly left alone), plus the two
read-only consumers of the `Matrix`-typed `A^{(q)}`.
**Since slot-24 CL-M** (CODEAUDIT C-02) the `Matrix` / `Matrix64` aliases carry no `[[deprecated]]`
attribute (the `BlockFlatMatrix.h` precedent: `check_matrix_includes.sh` enforces the include policy without
warnings), the dead deprecated free functions (`change_of_basis` ×2, `factor_basis`, `basis_to_string`,
`ComputeSymmetricPowerMatrix(MatrixT)`) and the five `EquivariantCohomologyOnK` `MatrixT` compatibility
accessors are deleted (callers use the `*_fm` accessors), and `cohomology_app` no longer carries
`-Wno-deprecated-declarations`, so a deprecation warning is a real diagnostic again. HeckeExt's `ExtMatrix`
(= `MatrixT<uint32_t>`) is the sanctioned `MatrixT` user (A9; `ENGINE_API.md` §2.1, the guard's `census` line).

#### Matrix engine (Phase 4–5) — the tape (`src/Engine/`, `engine::tape`) and the CUDA backend (`src/Cuda/`, `engine::cuda`)

Phase 3 removed the per-cell orchestration; Phase 4 removed the *per-call* one. A consumer no
longer issues block kernels one at a time: it **records** a program of block ops on a `Recorder`,
`compile()` rewrites it, and an `Executor` runs its wavefront levels on a work-stealing
`ThreadPool`. Binding contract: `src/ModArithmetic/ENGINE_API.md` §10 (tape), §11
(device layer), §12 (tape ↔ device). Static library `MatrixEngine`, plus `EngineCuda` for the
device layer.

* **Seven passes** (`compile(prog, opts)`, idempotent, a pure function of `(program, options)`):
  1 fold on `BlockRef` kinds, 2 CSE on exact temp identities + fusion, 3 layout assignment by
  cost-weighted votes with **one** memoised physical `TRANSPOSE` per mismatch, 4 k-blocking,
  5 batching within a wavefront, 6 device assignment, 7 residency / transfer insertion. Then
  dependency analysis on overlapping windows, wavefront levels, temp lifetimes, and a first-fit
  **arena** over lifetime intervals. Every decision is recorded *in the program*, so a compiled
  program runs identically under any thread, batching, graph or device setting.
  **Since hecke-extensions slot-9 WP-7 (lever L3)** the arena's first-fit (`Passes.cpp`,
  `ArenaFirstFit`) is `O(log L)` per temp: temps are visited in (`first_level`, footprint desc, id)
  order; before a temp is placed every live temp with `last_level < first_level` is released (a
  min-heap on `last_level`); the temp goes to the lowest offset in `{0} ∪ {aligned ends of live
  temps}` whose range meets no live temp, found by one descent of a treap keyed by offset whose nodes
  carry the gap before them and their subtree's maximum gap. Every answer is a function of the live
  **set**, never of the treap's shape or priorities, so every `arena_offset` / `arena_elts` — and so
  the compiled program and its cache key — is identical by construction. Under `!NDEBUG`
  `schedule()` also runs the old linear scan (`ArenaFirstFitLinear`) and `ENGINE_DEBUG_CHECK`s every
  offset; `EngineArenaFirstFitValidation` (`fast`, 17 checks) re-derives offsets independently on
  20 400 randomized temps. The old `O(T · L)` scan was 17 s of an 18 s compile at `U_10007`,
  `n = 18` (≈ 10⁶ temps): cold `(18, 10007)` 25.9 s → 10.8 s.
* **`EngineRuntime.h`** is the consumer-side glue: `consumer_pool()`, `consumer_pass_options()`,
  `run_cached(ex, key, program, bindings)` — the **record-always / compile-on-miss** protocol,
  keyed by a shape signature that carries the pass-options fingerprint and the prime — and
  `run_concurrently(tasks)`, the host-side fan-out. The consumers' scoped options are
  `thread_local` and are propagated onto task threads through a registered-propagator registry,
  so concurrent pipelines cannot see each other's settings. `EquivariantCohomologyOnK` and
  `HeckeOperatorOnK` record on it (`tape::kernel_basis` / `image_basis` / `factor_basis`,
  `cohom.Zeq`, `hecke.theta`, `hecke.route2` (since S23 P4R only under the rollback `HECKE_RHO2_STREAM=0`; by default route 2 is streamed key by key on the host, no memo), `hecke.resid.chunk` (per 512-RHS chunk), `tape::solve_multi_rhs`); τ
  construction, the `BlockBuilder` metadata assembly, `HeckeModuleDecomposition` / `FpPoly` and
  `HeckeCrossChecks` deliberately stay off it.
* **Environment switches** (`PassOptions::from_env()` — none of them can change a value):
  `ENGINE_BATCH`, `ENGINE_KSPLIT`, `ENGINE_ARENA`, `ENGINE_CSE`, `ENGINE_FUSE`, `ENGINE_LAYOUT`,
  `ENGINE_DEVICE`; executor `ENGINE_THREADS` (default `min(hardware_concurrency, 32)`),
  `ENGINE_TILE_MULT`, `ENGINE_TILE_COLS`, `ENGINE_SPIN`, `ENGINE_ELIM_BASE`; CUDA
  `ENGINE_CUDA_DISABLE`, `ENGINE_CUDA_DEVICE`, `ENGINE_CUDA_GRAPH`, `ENGINE_CUDA_MERGE_LEVELS`,
  `ENGINE_CUDA_PROGRAM_CACHE`, `ENGINE_CUDA_PINNED_MB`, `ENGINE_CUDA_COPY_THREADS`; tracing
  `ENGINE_TRACE_NODES`, `ENGINE_TRACE_RSS`, `ENGINE_TRACE_ELIM`, `ENGINE_TRACE_LEVELS`,
  `ENGINE_TRACE_PASSES`.
* **`ENGINE_DEVICE` semantics** (pass 6): `cpu` (**the default and the golden path**) assigns
  every node to the CPU and inserts no transfers; `gpu` assigns every device-eligible node
  (everything but `PANEL_RREF`, `PIVOT_SEARCH`, `COMPARE`) to the GPU; `hybrid` runs the static
  cost model of `EngineCostModel.h` per group of would-be batch members, with a residency
  simulation, and always chooses the GPU for a `uint64_t` context. **The GPU is never enabled by
  default, and on the measured evidence must not be**: the elimination driver records one program
  per panel, so the `gpu` arm re-uploads its operands and is 1.4–3.3× *slower* than the CPU on
  the pipeline's own shapes (plan §14.4); `hybrid` wins ≈ 13 % at `n_sym = 256` and loses at
  every size on a campaign sweep. The GPU wins where work amortises: a 4096³ GEMM (6×) and a
  replayed batched small-block program (up to 17×).
* **`src/Cuda/`** — `CudaCtx` (3 streams, a ≤ 128 MB `cudaHostAlloc` pinned staging
  pool copied by a persistent 4-thread `CopyPool`, a device arena, graph capture), `DeviceBuf`
  (mirror + two-counter residency), `CudaKernels` / `cuda_kernels.cu` (GEMM with shared-memory
  tiles and split-K, `GemmBatch`, GEMV, TRSM, transpose, canonicalise, gather/scatter). Every
  public header is **CUDA-header-free**, so the tape includes them from plain C++ TUs. Exact
  integer arithmetic throughout — no floating point, no atomics on results; split-K partials are
  canonicalised and summed mod `p` in a fixed order, so **a device result is the same bytes as
  the CPU result by construction** (`CudaBitIdentityValidation` asserts it by `memcmp`).
* **Three device rollbacks / gates**: `ENGINE_DEVICE=cpu` (runtime), `ENGINE_CUDA_DISABLE=1`
  (pretend there is no device), and `cmake -DENGINE_VERIFY_DEVICE=ON`, which re-executes every
  GPU node on the CPU inside a real run and compares every written window entrywise, throwing
  with node / op / level / buffer / window on the first difference. Without a device every
  device validation prints `[SKIP]` and returns 0, so `--all` is green on a GPU-less machine.
* **A thread-local device override** (hecke-extensions slot-8 WP-6b; ENGINE_API §10.9):
  `engine::tape::ScopedThreadDevice(d, tally)`, `d ∈ {Cpu, Gpu}`, replaces the three device fields
  of the options that thread would use (`device_policy`, `device_model`, `policy`), with exactly
  `from_env()`'s `cpu` / `gpu` mappings; `register_thread_context()` captures it, so
  `run_concurrently()`'s tasks inherit it (a plain `std::thread` does not). `consumer_pass_options()`
  and the elimination driver's new `elim_pass_options()` apply it; with none installed both are
  exactly what they were. `hybrid` is not offered. **WP-6b findings 2–3, fixed in hecke-extensions
  slot-9 WP-6** (owner decision 7 (A), value-free): `elim_pass_options()` is now
  `consumer_pass_options()`, so the tape elimination driver's per-panel programs `P1` / `P2` and
  `solve_multi_rhs`'s unit-row certificate program compile under the process-wide `ScopedPassOptions`
  override (before: `from_env()` whatever was installed — the `batch = 0` determinism arms never
  reached elimination); and `pass_options_fingerprint()` sets bit 128 iff `effective_policy() != Cpu`
  (before: iff `device_model && device_policy == GPU`), so an options value selecting the device
  through `PassOptions::policy` alone keys its programs apart from the CPU arms (ENGINE_API §10.6,
  §10.9). Every `from_env()` mapping, `ScopedThreadDevice` and the console's `set device` set both
  together, so their fingerprints do not move; `hybrid` and `gpu` still share the bit (the key's
  `extra << 56` has room for eight bits — a ninth would move every key; slot 10). `TapeElimStats`
  gained five diagnostic counters (`batch_off_programs`, `device_policy_programs`,
  `batched_programs`, `gpu_programs`, `gpu_nodes`) printed per arm by the three determinism
  validations (non-vacuity: e.g. ExtDet's first `gpu` arm now keys 607 new slots with 770 of 784
  programs carrying GPU nodes); the per-panel programs never form a batch. The CUDA layer's
  `g_stats` launch counters became relaxed atomics (a pre-existing race the device arms now reach;
  what CheckThread still reports with a live device is inside `libcuda`). No value, digest or golden
  line moved; `EngineElimPassOptionsValidation` (`fast`, 18 checks).
  **Since slot-10 WP-8** (owner decision 10 (A), value-free) the fingerprint has a **ninth bit**,
  256, set iff `effective_policy() == Gpu`, so `hybrid` (bit 128) and `gpu` (bits 128 + 256) no
  longer share a `ProgramCache` slot; `run_cached()` folds it at `<< 55` (it was `<< 56`, where
  `256 << 56` wraps a `uint64_t` to 0 and the bit would vanish). ENGINE_API §10.6 amended;
  `EngineFingerprintDeviceBitValidation` (`fast`, 8: fingerprints `0x6f` / `0xef` / `0x1ef`, three
  distinct cache slots, each replayed); `EngineElimPassOptionsValidation` 18 → 19 (the `gpu` mapping
  now carries bit 256). Cache keys only: the four digests did not move.
  **Since slot-10 WP-6** `ThreadPool`'s cache-line layout is pinned: `alignas(64)` on `slots_` and on
  `regions_` (`sizeof` 144 → 192, `static_assert(alignof(ThreadPool) == 64)`), reproducing the good
  grouping (line 1: `slots_` + the whole `reg_m_`; line 2: `regions_`, `n_regions_`, `reg_epoch_`,
  `stop_`) wherever the linker puts the object. At the slot-9 close the static `ThreadPool::global()`
  pool had moved from 32 to 0 mod 64 in `.bss` (slot 9's WP-4 merge `8c9faf4` added globals ahead of
  it), splitting `reg_m_` across two lines; `(10, 691)` runs 52 558 regions of ≈ 3.5 µs per repeat,
  so its 16-thread `--bench ext` read ≈ 4 % slower with identical work (proved by node counts,
  allocations, `ENGINE_THREADS=1` and a controlled `.bss` padding experiment, [WP10-6]). Layout only;
  `bench_identity` 45 / 0, `ext_compare_mini` PASS, digests unchanged. Heap pools (`new ThreadPool`)
  get the same layout through C++17 aligned new. **Compare two binaries' timings only when both place
  the pool alike** (`nm -S <bin> | grep _ZZN6engine4tape10ThreadPool6globalEvE4pool`). Unevaluated
  follow-up (E-1): `ThreadPool::Slot` objects are heap-allocated back to back (≈ 100 B) and may share
  lines.
* **The CPU-only build (hecke-extensions slot 19, NB-0).** `-DOC_ENABLE_CUDA=OFF` keeps the device seam
  and swaps only its implementation: `project()` enables `CXX` alone and `CUDAToolkit` is never searched;
  `EngineCuda` keeps its name and public headers but is built from `src/Cuda/CudaStub.cpp`
  (instead of `CudaCtx.cpp` + `cuda_kernels.cu`), which defines every symbol of `CudaCtx.h` /
  `CudaKernels.h` with the same explicit instantiations: `available()` / `device_enabled()` are false
  (reason `built without CUDA (OC_ENABLE_CUDA=OFF)`), `requested_device()` still parses `ENGINE_DEVICE`,
  `CudaCtx::get()`, the kernels and graph capture throw `CudaError` — exactly the no-device branch of the
  CUDA build, which `DeviceBackend::usable()` and every device validation already test first (each prints
  its `[SKIP] … no usable CUDA device (…)` line). `CudaValidation.cpp` / `CudaBench.cpp`, `MatrixEngine`'s
  `DeviceBackend.cpp` and all consumers compile unchanged; nothing links `CUDA::cudart`. The entry point
  `main.cpp` (formerly `main.cpp`; no device code) is a host-compiler TU in both builds, so `main()` has one source. On aarch64 (Jetson Orin, `sm_87` or CPU-only;
  kit `docs/cluster/jetson/`) the AVX-512 kernels of `Kernels.cpp` are compiled out by their `__x86_64__`
  guard and the thread pool spins with `std::this_thread::yield()`; `unsigned __int128` is native in GCC
  on aarch64. The other two build switches, `OC_BUILD_DOCS` / `OC_BUILD_NOTEBOOK`, live in
  `cmake/OcDocs.cmake` / `cmake/OcNotebook.cmake`, read only when ON; all three reach the code as `0`/`1`
  macros on `cohomology_app` through `src/hacs/BuildSwitches.h`
  (`oc::BuildSwitchSkip` for a switched-off validation body).

#### The legacy flag `OC_ENABLE_LEGACY` (slot-24 CL-L0; owner ruling 1 of 2026-10-30; design `slot24/CLEANUP_plan_1030.md` §2)

The fourth build switch. Retired routes — the legacy engine route (CL-L1, CL-L2) and the old routes of retired rollback
levers (CL-R1, CL-G2; the rollback-lever retirement rule) — are **kept in the tree** in `legacy/` directories and compiled only
when the flag is ON. CL-L0 installed the machinery; **no code has moved yet**, so at CL-L0 the OFF and ON builds differ only in
the refusals below.

- **The option.** `option(OC_ENABLE_LEGACY … OFF)`, decided before `project()`, printed on the configure status line
  (`… OC_BUILD_NOTEBOOK=OFF OC_ENABLE_LEGACY=OFF host=…`). **One flag** for both rulings: every extra flag doubles the close-time
  configurations.
- **The macro is always defined**, to `0` / `1`: `PUBLIC` on `ModArithmetic`, `HeckeCore`, `MatrixEngine` and `EngineCuda`,
  `PRIVATE` on `cohomology_app` (the `ENGINE_SHADOW_LEGACY` pattern: it will guard class members, so every TU must agree — ODR).
  `ConsoleCore` and `NumberField` (STL-only) do not see it.
- **`src/ModArithmetic/LegacyConfig.h`** (header-only, STL-only): `#error` when the macro is undefined;
  `oc::legacy::kLegacyBuild`; `compiled_out_text(request)` and `[[noreturn]] refuse_compiled_out(request)` — stderr
  `REFUSED <request>: compiled out (OC_ENABLE_LEGACY=OFF)`, flush, `std::_Exit(1)` (safe inside a static's initialiser or on a
  pool thread). Code tests the flag with `#if OC_ENABLE_LEGACY` or `if constexpr (kLegacyBuild)`, **never `#ifdef`**.
- **Sources.** `cmake/legacy.cmake`, included unconditionally after every target exists, adds each `legacy/` `.cpp` to its target
  inside `if(OC_ENABLE_LEGACY)` (empty at CL-L0). A `.inc` is included at the end of its `.cpp` under `#if OC_ENABLE_LEGACY`.
  Each `legacy/` directory gets a `README.md` (what, when retired, by which package, how to reactivate).
- **Validations** (`src/hacs/Registry/LegacyValidation.h`). A legacy-gated name stays registered in every
  build, at its place and tier, so `--list` and `EXPECT_NAMES` never depend on the flag:
  `register_validation("Foo", OC_LEGACY_VALIDATION(Foo), tier)` is `&Foo` when ON and, when OFF, a stub printing
  `[SKIP] Foo: OC_ENABLE_LEGACY=OFF` (exit 0, `oc::BuildSwitchSkip`) that does not reference `Foo`. A gated **arm** runs under
  `if (oc::legacy::RunLegacyArm("Foo", "b"))`, which prints `SKIP-ARM Foo arm=b: OC_ENABLE_LEGACY=OFF` when OFF; the catalogue
  records both check counts.
- **Refusals in an OFF build** (§2.4: a request for a compiled-out route is refused, never ignored — the vacuous-arm lesson):
  - `ENGINE_BACKEND=legacy`: refused at the first `engine::backend_is_legacy()` read, which `main()` performs first, so every
    entry point (`--list` included) exits 1. **Wired at CL-L0.** Other `ENGINE_BACKEND` values are unchanged.
  - a retired lever's rollback (`X=0`): `engine::lever::RetiredLever` (`EnvLever.h`'s retired mode). ON: it **is** `EnvLever`.
    OFF: one route (`enabled()` = the policy default), the old route's valid reading refused at the first read, invalid readings
    keep their WARNING, no `Scoped`, `source()` = `retired` (`EFFECTIVE … source=retired`). **Mechanism at CL-L0; the first
    levers retire in CL-R1 / CL-G2.** Smoke: `SharedHelpersValidation` arm (K) reads the probe `OC_CL1_RETIRED_PROBE` as started.
  - console `set backend = "legacy"` and `micro(…, backend = "legacy")` → `NotImplementedError` (exit 5), and
    `--bench micro --backend legacy` → usage error `--bench: --backend legacy: compiled out (OC_ENABLE_LEGACY=OFF)` (exit 1),
    all built on `compiled_out_text()`: **wired by CL-L2 (landed)**, together with the arms that used them: `ConsoleDeterminism`
    (b) and `ConsoleSettings`' backend knobs are `SKIP-ARM` when OFF (`ConsoleSettings` checks both refusals instead);
    `022_harness.oc`'s engine-vs-legacy `micro` pair moved to `ConsoleSettings` arm (f) (ON) and the script now pins two engine
    runs (transcript unchanged: it printed nothing); the `PerformanceSmoke` legacy floors are reachable only under
    `ENGINE_BACKEND=legacy` (ON builds), as before.
- **Keeping it compiling** (§2.6). `cross_config.sh`'s default list carries the `legacy` arm
  (`RelWithDebInfo+OC_ENABLE_LEGACY=ON@ENGINE_BACKEND=legacy`), which replaces `RelWithDebInfo@ENGINE_BACKEND=legacy` (an OFF
  build refuses it). **CL-L1 (landed)** added the `legacy-shadow` arm (`RelWithDebInfo+OC_ENABLE_LEGACY=ON+ENGINE_SHADOW_LEGACY=ON`,
  replacing `RelWithDebInfo+ENGINE_SHADOW_LEGACY=ON`) and the `FATAL_ERROR` for shadow-ON with legacy-OFF, and moved the shadow
  comparisons into `legacy/` (`ShadowLegacy.inc`, `EquivariantCohomologyOnKShadow.inc`, `HeckeOperatorOnKShadow.inc`; each
  directory's `legacy/README.md`). Both arms run at every slot close, `legacy-shadow` also under `--all`.

#### Campaign driver (Phase 6) — `--campaign`

`./hacs --campaign <spec-file> [--output <dir>] [--dry-run] [--quiet]` turns the
pipeline into a survey instrument: it enumerates a `(n_sym, ℓ, p, r, q)` grid, groups the jobs by
shape signature, runs `spec.jobs` of them concurrently (each on its own engine pool of
`spec.threads` workers) and writes one streamed JSON per job — the canonical objects and their
FNV-1a-64 hashes, the full `HeckeReport` levels (a)/(b)/(c), which certificates ran, timings and
peak RSS — plus a campaign-level `index.json` and a `summary.tsv`. Everything goes through the
**public API only**, the same code path as `--bench` and every validation. The spec is
line-oriented and hand-rolled (`---` starts a new section, `key = value`, ranges `a..b step c`);
`certify = full | sampled(...) | none` controls only the *external* cross-checks
(`HeckeCrossChecks`, `T_p_pow_direct`) — the in-process certificates C3–C6 are **never** sampled —
and `lean`, `level_a`, `resume`, `model` are the other knobs. Full documentation:
`docs/matrix-engine/campaign.md`; the shipped specs and the published table live in
`docs/matrix-engine/results/` (`results_table.tsv`, `analysis.txt`, `specs/*.spec`). Gated by
`CampaignSmokeValidation` (the same spec at four `jobs × threads` splits must produce the same
jobs in the same order with the same objects as the sequential arm) and
`CampaignCertificateValidation`.

Since slot-5 WP-2 the spec also takes `ext`, `family`, `sign` and `ext_groups` ([X] §1.5). With
`ext = true` the driver runs `HeckeExt/HeckeExtDriver` once per `(n_sym, ℓ)` **cell**,
**sequentially on the campaign's main thread and before the job loop** — the driver builds its
tessellation tables outside `hecke::tau_construction_mutex()` and so may not run on a job thread,
while holding that lock around `run()` would deadlock on its own re-entry — and attaches the
record to the cell's first job in plan order, as the standalone `ext/hecke_ext_ell<ℓ>_n<n>.json`
(with its state sidecars) and verbatim inside that job's `"extensions"`. `summary.tsv` gains eight
appended columns and `index.json` an `"extensions"` block, **only** when `ext = true`; with it
false every byte of the campaign's output is unchanged — the frozen 21-column header, the id
`n16_ell5_p2_r1` and the default shape signature are asserted as literals. The campaign's `resume`
continues a refused `U_ℓ` from the persisted record plus its sidecar ([X] §1.3.1 R3.3 item 4).
The seam is `Campaign/CampaignExt.{h,cpp}`, the only `Campaign/` TU that includes a `HeckeExt/`
header. Gated by `HeckeExtCampaignValidation` and `HeckeExtDeterminismValidation`.
**Open (slot 6):** `Job::id()` carries no extension key, so two campaigns differing only in
`family` share a resume key — WP-2's finding; the ext keys must join the id or the shape
signature before an ext campaign is resumed across specs.

**Slot 8 (hecke-extensions): the parallel ext pass and the program-cache release.**
* **The release** (WP-5, `Campaign/ProgramCacheRelease.{h,cpp}`, engine-free header so the nvcc TU
  can include it): `ReleaseEngineProgramCaches(threshold)` clears both global program caches iff
  their size exceeds `threshold`, then calls glibc `malloc_trim(0)` (without it the clear alone
  left RSS unchanged — the half of [KI] §4c's cause that was not written down). **Where it is
  called**: `RunExtPass` after every cell the engine ran (`kCellLoopReleaseThreshold = 512`),
  `RunJobList` after every job on both paths (`kJobLoopReleaseThreshold = 2048`), and the
  `--atlas` build between cells (`HeckeAtlasCli`'s `between_cells` callback, reaching
  `CollectAtlas` through `AtlasOptions::between_cells`; `HeckeExt/` still never names the engine).
  Changes no value, id or file name — only RSS. `ProgramCacheReleaseValidation`.
* **The parallel ext pass** (WP-6): `RunExtPass` is split into a **decide** step (per cell: the
  `u_ell` admission and the resume decision, in cell order) and a **run** step (`RunCellWork`,
  per cell, on a worker context that installs the spec's settings and a per-worker engine pool).
  `ExtCellScheduler` admits cells by memory-aware LPT: a cell's predicted cost is
  `kExtCellFloorMb = 512` plus the frozen `PredictUEllRssMb` when `U_ell` is admitted
  (`PredictExtCellCost`), ordered by `U_ell` predicted MB, then `n` descending; at most
  `ext_jobs` cells run at once and the admitted predictions stay under `ext_memory_mb` (default
  40 000). Records are written in cell order, so **serial and parallel passes are byte-identical**
  (every ext record and `analysis.txt`; `summary.tsv` / `index.json` after normalising the timing
  and RSS fields), shown on `ext_compare_mini.spec`, a non-default-setting arm (`u_ell = off`) and
  `HeckeExtCampaignValidation` arm 10 (`docs/matrix-engine/tools/ext_pass_identity.sh`). The pass
  prints `EXT_PASS wall_s=… jobs=… peak_rss_mb=… memory_cap_mb=… peak_admitted_mb=… peak_running=…`
  (`campaign.md` §14). Thread-safety prerequisites fixed in the same package: the engine's
  `elim_stats` / `gemm_stats` counters are relaxed atomics, and `hecke::PredicateStats` is per
  thread (`Hecke/Predicates.{h,cpp}`); `CheckThread` clean. T-P's instrument is
  `docs/matrix-engine/tools/ext_pass_tp.sh` (the verdict is window W1's).
* **The device worker** (WP-6b, the owner's optional item, accepted): `ext_gpu = off | on | force`
  and `ext_gpu_cells` add one worker that runs its cells under `ScopedThreadDevice(Gpu)` beside the
  CPU workers; records bit-identical (also under `-DENGINE_VERIFY_DEVICE=ON`); **measured no gain**
  (indicative, ≈ 9 % slower on the mini spec), so the default stays `off`, which costs one
  thread-local read per compile. `HeckeExtCampaignValidation` arm 11;
  `docs/matrix-engine/tools/ext_gpu_timing.sh`.
* **`resume_u_ell`** (WP-11b): the campaign's resume branch passes `SettingSource::Spec`, so a
  resumed record's `u_ell` source reads `spec` ([KI] §4d RESOLVED).
* **Ring jobs (hecke-extensions slot-9 WP-8, C5c; owner decision 6 (A))**: `RunOneJob` dispatches to
  `RunRingJob` (`Campaign/CampaignRing.{h,cpp}`) whenever `coefficient_ring` is `Z/ell^k`, `k ≥ 2`;
  nothing of the field path runs. Per job: the cohomology over the ring (the module route at
  `ell ≥ 5`, the Bredon flat-coordinate route at `ell ∈ {2, 3}` — since the merge fix `158c0be` the
  relation list there takes the raw `ModCtx::prime_power` context and only
  `EquivariantCohomologyOnK` applies the Bredon policy), `uint32_t` below `2^32` and `uint64_t`
  above; at `ell ≥ 5` the `K`-mode on its range, the Bockstein counts (each comparison object built
  under its own `ScopedCoefficientRing`), `red_H^q`, and for `r = 1` with `1 ∈ degrees` `A(T_p)` and
  the free charpoly at a certified level; the [E] `sec:ring` (d) objects under their golden names.
  Refusals come **from the real guards** (`HeckeOperatorOnK`, `HeckeReduction::BocksteinCounts`,
  `ReduceHToField` at `ell ∈ {2, 3}`; `hecke` at the job loop's own dispatch for `r ≥ 2`) and a guard
  that stops refusing **fails the job**. The file is `hecke_ring_report/v1` ([E] (g1)–(g16),
  `charpoly_free.coeffs` as decimal strings — they exceed `2^53` at the `uint64_t` cells), written
  once; `summary.tsv` keeps its 21 columns (the ten field ones `-`) and appends 15, `status`
  `ok_partial` when anything is refused; `index.json` gains `coefficient_ring`. Both only when
  `k ≥ 2`, so **no id or file at the defaults moves** (the seven shipped specs' `--dry-run`
  byte-identical). At spec validation, before any job or output directory: `ext = true` under a
  ring, and any grid cell with `ell^k ≥ 2^64`, are refused by name (`--campaign` exit 1).
  `CampaignRingValidation` (`standard`, 693 checks: every carried object equals the golden entry at
  the seven E8 points; the O7 rows at `ell ∈ {2, 3}`); `campaign.md` §15.

#### Migration tools (`docs/matrix-engine/tools/`)

Five acceptance guards — four grep-level, one a small parser — each owning an allow-list **with a
reason per entry**, and each run inside `--all` by a validation so they cannot rot:

- **`raw_mod_calls.sh` + `raw_mod_calls.allow`** — census of raw `ModArithmetic::mod_*` call sites
  under `src/hacs/`. The target is *not* zero: the allow-list's PERMANENT section
  (`FpPoly.cpp`, `HeckeModuleDecomposition.cpp`, `HeckeTauTable.cpp`, every `*Validation.*`,
  `Golden/`, `Bench/`) is deliberately out of scope for the whole programme. The assertion is **zero
  outside the allow-list**, and *removing a line from the file is the unit of progress*. Phase 3
  emptied the Stage B backlog: **195** sites remain, all allow-listed, 0 outside (185 at the
slot-3 close; slot 4 added 10, every one of them in a new `*Validation.cpp`, covered by the
existing `*Validation.*` glob, so no allow-list edit was needed; 164 at the slot-2
close; slot 3 added 21 — 19 in `Hecke/HeckeModuleDecomposition.cpp` and 2 in
`Hecke/SubspaceOps.cpp`, both PERMANENT entries, for WP-3's strict mode; 149 at the
  slot-1 close; slot 2 added 15 — 13 in `HeckeExt/HeckeExtAlgebraValidation.cpp`, covered by the
  `*Validation.*` glob, and 2 in `Hecke/SubspaceOps.cpp`'s PERMANENT entry, now 8; 113 before
  hecke-extensions slot 1, whose WP-3 added a PERMANENT block — `HeckeExt/HeckeSturmBound.cpp`,
  14 sites, and `Hecke/SubspaceOps.cpp`, 6 — permanent *by design*, because the `HeckeExt/` guard's
  rule 3 forbids `HeckeSturmBound` from including `ModCtx.h` at all, plus the new validation TU's
  16; the figure was 108 before the 2026-09-16 iota-symmetric-tau merge). Run by
  `ConsumerMigrationValidation`.
- **`check_matrix_includes.sh`** — no DIRECT include of a *deprecated substrate header* outside its
  allow-list, one list per header: `Matrix.h` (the Phase 3 exit criterion) and, since the
  `BlockFlatMatrix` trim, `BlockFlatMatrix.h`, whose list is deliberately tiny — `ModArithmetic/`,
  `*Validation.*`, and the only two production headers that still declare legacy-arm members
  (`EquivariantCohomologyOnK.h`, `SimplicialCohomology.h`) — so a new consumer cannot appear
  without the guard failing. Run by `MatrixRetirementValidation`.
- **`check_console_includes.sh`** — the console's one-way dependency, both halves. *Rule 1 (the
  reverse rule)*: inside `Console/Core/` every `#include <...>` must be a C++ standard header
  (a closed list) and every `#include "..."` must name a `Console/Core/` file — that is what
  makes "`ConsoleCore` has no include outside the STL" checkable rather than promised. *Rule 2*:
  no TU outside `Console/` may include a console header, allow-listing only `main.cpp` (the C1
  CLI branch), `*Validation.*` and `ValidationRegistry.cpp`. Run by `ConsoleC0Validation`.
- **`check_heckeext_includes.sh`** — the hecke-extensions layer's one-way dependency.
  `src/hacs/HeckeExt/` is compiled straight into `cohomology_app` and not into a
  static library, so there is no link-time barrier; this script is it. Four rules: (1) no
  `#include` of `HeckeExt/` outside `HeckeExt/`, `Campaign/`, `Golden/`, `Bench/`, `main.cpp`,
  `*Validation.*` and `ValidationRegistry.cpp` — the pipeline never depends on the extension layer;
  (2) inside `HeckeExt/`, no `Console/`, no `src/Cuda/`, no `src/Engine/` and no
  `BlockFlatMatrix.h` (the layer is `Matrix`-sized and single-threaded); (3) `HeckeSturmBound.*`
  limited to `Hecke/SubspaceOps.h`, `Hecke/FpPoly.h`, `Matrix.h`, `ModArithmetic.h`,
  `EngineCheck.h` and `Fnv.h` (both dependency-free) — the unit that consumes *nothing* of the pipeline; (4) no `unordered_` anywhere
  in the layer. Run by `HeckeExtArchitectureValidation`. **The slot-3 "Open for slot 4" note is
  CLOSED** (slot-4 WP-5, [OD] slot-4 confirmation 4): rule 1 still does **not** admit
  `Console/Bindings/`, and does not need to — `HeckeExt/RegisterHeckeExtensionVerbs.cpp` registers
  the extension verbs itself, which costs **one exact-path entry in each guard's rule 2**
  (`check_console_includes.sh` gains one `ALLOW_CONSOLE` line; this script gains a one-element
  `Console/`-only exception array, so `Cuda/`, `Engine/` and `BlockFlatMatrix.h` stay banned in
  that TU too). The entry is the `.cpp` **alone** — its header forward-declares `console::Registry`
  and includes no `Console/` header, and must never become an offending path. Rule 1 of each guard
  and `ConsoleCore`'s STL-only rule are untouched.
- **`label_census.sh` + `label_census.py` + `label_census.allow`** (slot-3 WP-10) — the citation
  guard of [C] `sec:machinery` item 2 (rule L1). Not a line-level grep: a `[C, <label>]` payload is
  comma-separated, sometimes clause-suffixed, sometimes multi-label, so the parser is a small
  Python module the bash entry point shells out to (the `golden_explain.py` precedent makes
  `python3` a tooling dependency, never a build one). Every `[C, <label>]` citation — C++
  comments, `CMakeLists.txt`, READMEs, plans, reports — and every `\HA{<label>}` of
  `hecke_extensions.tex` must name a `\label` of `gl2_contract.tex`. Regenerates
  `docs/latex/label_census.tsv` on **every** run (not owner-gated: it reports the tree as it
  stands); the site count is never gated, only the unresolved count after the allow-list's four
  placeholder entries must be 0. **Since hecke-extensions slot 4 WP-6 `label_census.allow` is
  content-keyed**: each entry is `relpath|<verbatim fragment of the site's source line>`, not
  `relpath:line`, and matches every unresolved citation in `relpath` whose full source line
  contains the fragment — so inserting or deleting lines above a cited passage cannot silently
  move an entry off its site, which is what makes the format safe for a contract rewrite. An entry
  matching **zero** sites is flagged **STALE** and fails the census (the same "removal is the unit
  of progress" rule the other allow-lists use); the retired `relpath:line` form is rejected with a
  named error, never silently reinterpreted or skipped. At the slot-4 close: **429 labels defined,
  1575 citation sites in 128 of 471 scanned files, 152 distinct labels cited, 4 allow-listed,
  0 unresolved, 0 stale.** Run by `ContractCensusValidation`, which since slot-4 WP-6 also
  exercises the content-keyed property itself, on scratch roots and never on the real allow-list
  or `label_census.tsv`.

The allow-lists are also where migration *decisions* are recorded in prose — notably the verdict
on `HeckeTauTable.cpp`'s mod-`ℓ` RREF-with-RHS solver (**not absorbed**, and why) and the engine
API gap that verdict exposes.

**Registry and cmake folding (S24 CL-10, 2026-11-01).** The per-package fragments described below were folded at the slot-24 cleanup: each closed
slot S in 9..23 is one `Registry/Slot<S>.cpp` (the package functions `RegisterSlot<S><pkg>()` verbatim, plus an aggregate `RegisterSlot<S>()` in the old
call order, which `RegisterAllValidations()` calls), and the source lists are per module in `cmake/sources/<Module>.cmake` (`Registry`, `Hecke`,
`HeckeExt`, `Integral`, `Campaign`, `Console`, `NumberField`, `Util`, `Orbifold`, `Binary`, `Root`; `Special` = library-target sources, compile
flags and notebook-conditional sources). Slot 24 (open) keeps one pair per package until its close. (Slots 24, 25 and 26 were folded the same way at their closes, S24 CL-10b, S25 FOLD and S26 FOLD; the open slot keeps one pair per package.) The per-slot READMEs moved verbatim to
`docs/implementation/registry-slot-readmes-9-26.md`; the guard allow-lists (`ALLOW_CONSOLE`, `ALLOW_FORWARD`) name the folded files. The text
below is the history of the pattern; its paths are the pre-fold ones.

**Per-package registration fragments (hecke-extensions slot-9 WP-1, owner decision 11).** Slot 9 ran
up to five packages at once; to keep them from colliding on the two shared-structure files, each
package `n ∈ {3, …, 13}` owned `src/hacs/Registry/Slot9/WP<n>.cpp` (an empty
`void RegisterSlot9WP<n>()` it fills) and `cmake/slot9/WP<n>.cmake` (`target_sources(cohomology_app
PRIVATE …)`, `include`d right after `add_executable`); `RegisterAllValidations()` calls the eleven
functions at its tail in package order, so `--list` stays byte-identical in every pre-existing line
and appends new names. Fragments cover `cohomology_app` only (library blocks unchanged). Two guard
allow-list entries, each with its reason, admit `Registry/Slot9/*.cpp` (`ALLOW_CONSOLE` in
`check_console_includes.sh`, `ALLOW_FORWARD` in `check_heckeext_includes.sh`); a negative control
showed both load-bearing. **At the slot-9 close the fragments are kept, not folded**, as the pattern
for slot 10 (`Registry/Slot9/README.md`). A further tree-scanning guard arrived with slot-9 WP-9:
`SmallEllPolicyScopeValidation` (`fast`) allows the token `SmallEllPolicy::Bredon` only in
`EquivariantCohomologyOnK.cpp`, `Hecke/CoefficientRing.{h,cpp}`, `*Validation.{cpp,h}` and its own
fragment `Registry/Slot9/WP9.cpp` — it caught one real violation at a merge (WP-8's job loop, fixed
by `158c0be`).

**Slot 10 kept the pattern** (slot-10 WP-1): `Registry/Slot10/WP<n>.cpp` (`RegisterSlot10WP<n>()`,
`n ∈ {3, 6, 7, 8, 10, 11, 12, 13}`, called after slot 9's) and `cmake/slot10/WP<n>.cmake`, both guards
admitting `Registry/Slot10/*.cpp` with a reason; five packages registered (WP-3, WP-8, WP-10, WP-11,
WP-13), so the five new names append in that order. **Kept, not folded, at the slot-10 close.** Two
process tools arrived with it: **`disk_guard.sh [--min-free-gb N] [--no-worktrees]`** (prints
`DISK c_free_gb= root_free_gb= worktrees_gb= verdict=`, exit 1 below the floor, deletes nothing; the
15 GB floor on `C:`) and **`golden_landing_check.sh <R0>`** (every commit in `<R0>..HEAD` touching
`*GoldenReference.inc`: a merge among them, or a commit not reachable first-parent, is a `FAIL` —
`LANDING merges= orphans= verdict=`; negative control `3e7abbc` → `merges=2 … FAIL`, the slot-8 and
slot-9 landings). `slot10_close_window.sh` runs both (steps −3, −1b).

#### Console language core (C0) — `src/hacs/Console/Core/`, `namespace console`

The first phase of the CAS-style console specified by `docs/console/00-console-interface-plan.md`
v2: a small, deterministic, hand-rolled expression language (working name **OC script**, files
`*.oc`) with **no third-party dependency and no pipeline dependency**. C0 ships the language only;
the bindings that wrap matrices, polynomials and pipeline objects, the `--console` / `--script` /
`-c` CLI surface and the script-transcript validation are phase C1.

- **Grammar** (`Lexer`, `Ast`, `Parser`) — the plan's §3.2 EBNF verbatim: assignment, expression
  statements (printed unless the statement ends in `;`), `for x in <list> { }`, `if`/`else if`/
  `else`, `set key = value`, `include("f.oc")`, `help` / `?name`, `expect_error "sub" { }`,
  `quit`; infix `+ - * / % ^`, comparison, `and`/`or`/`not`, calls with keyword arguments,
  member access, method calls, indexing, list literals, `args.name`. `Int` is `int64_t` and every
  operation is overflow-checked; `/` is **exact** integer division and errors on a remainder.
  There are no user-defined functions and no `while` (owner question Q2; `def` is reserved).
- **Values** (`Value`, `Record`) — `Int`, `Bool`, `String`, `List`, `Record`, plus the `Object`
  handle. Compound payloads are `shared_ptr<const T>`, so values are immutable and copying is O(1).
- **Handles** (`Object`, `TypeInfo`) — the plan's C2 object model, type-erased so the core names
  no pipeline type: keep-alive edges to everything the wrapped C++ object may dereference, a
  `declared → computed | failed` state machine where `failed` stores its error, rethrows it on
  every access and is **never retried**, the settings snapshot taken at **creation** (not at
  compute) and installed around `compute()`, and the creation site, so a lazy failure names both
  the access line and the constructing line.
- **Settings** (`Settings`, `SettingsSnapshot`, `SettingsScope`) — the session holds the
  *authoritative* value of every setting and installs a snapshot by re-applying every value, so
  there is deliberately **no RAII stack** (a stack of guards destroyed out of LIFO order restores
  stale values). Each `SettingSpec` carries a kind, a source (`session` / `env`-only, the latter
  naming its environment variable), engine-owned `validate` / `apply` hooks, and a **family**:
  owner decision R1 splits *engine* knobs from *mathematical* settings (`final_mode`,
  `sturm.cap`, `locality`, `field_polynomial`, `coefficient_ring`, …), which are part of what a
  result *means* and are the subset a reproducibility record must carry into its hash input.
  C0 registers only the two console-owned presentation keys (`print_max_entries`, `verbose`);
  the engine owns the defaults and the validation of everything else.
- **Resumable handles** (`ResumableState`, `Object::resume`) — owner decision R3, *designed now,
  implemented later*: a computation a budget cuts off records the budget setting, its value, a
  reason and its iteration state, `state(x)` reports them, and `resume(x, budget)` produces a new
  handle whose snapshot differs in exactly that key and which links back to its parent.
- **Registry** (`Registry`, `RegisterCoreVerbs`) — the evaluator knows no verb and no type; both
  come from a registry populated by explicit registration functions (never self-registering
  statics, which the linker drops across a static-library boundary). Overload resolution is by
  arity then by argument type, **first match in registration order**, so an extension adds
  overloads without editing anything. A registry-level exception translator is the seam through
  which C1 installs the plan's C7 catch order without the core seeing a pipeline header.
- **Output** (`Printer`, `Session`) — one canonical printer per type, a `print_max_entries` cap,
  `#~`-tagged annotation lines that every transcript comparison ignores, JSON with a proper
  escaper, and `ChatterCapture`, which swaps **both** `std::cout` and `std::cerr` to a sink while
  the session keeps writing to the buffer it captured.
- **Invariants** — `Console/Core/` cannot include `EngineCheck.h` (it would break the STL-only
  rule), so it defines `CONSOLE_CHECK` / `CONSOLE_DEBUG_CHECK` with exactly the semantics
  CLAUDE.md demands of `ENGINE_CHECK` / `ENGINE_DEBUG_CHECK`. No bare `assert` outside the
  validation TU; no `unordered_*` anywhere.

#### Console bindings and CLI (C1a) — `src/hacs/Console/Bindings/`, `Console/Core/ConsoleCli.*`

The second phase of the console (hecke-extensions slot 3, WP-7; `docs/implementation/slot3/WP-7_report.md`;
[P] v3.2 §10 Phase C1a): the language of C0 gains the objects. `Bindings/` is compiled into
`cohomology_app`, never into `ConsoleCore` — that is what keeps the library STL-only — and is the
only place a console type and a pipeline type meet. Nine types (`Fp`, `Poly`, `Matrix`, `Model`,
`Complex`, `LocalSystem`, `Cohomology`, `HeckeOperator`, `Family`) and 68 verbs on top of C0's 25:
the [P] §3.5 linear-algebra surface over `Hecke/SubspaceOps` (matrix arithmetic through named verbs
`mul` / `add` / `sub` / `scale`, since `+` / `*` are `Int`-only; `solve` requires full column rank;
`jordan_type` is the nilpotent partition), and `hash` / `hash_int` / `golden` / `fingerprint` /
`save_state` (`Bindings/Reproducibility.cpp`). `golden(point, object)` resolves through
**`GoldenLookup`** in `Golden/GoldenHarness.h` — the one read-only lookup over
`GoldenReference.inc` (inventory gap G13; `GoldenLocalitySweep` re-routed through it,
value-preservingly) — and refuses at a non-zero `MathSettings` fingerprint (rule R19). **No
`decompose` and no `report`** (C1b, slot 4), no `bernoulli_mod` (E6), no local-algebra invariants
(C5), no `HeckeExt/` binding (the guard, above), 32-bit types only. `main.cpp` gains exactly one
branch, entered only when `argv[1]` is a form keyword — `--console` / `-i` (dumb REPL),
`--script <f.oc> [name=value …]`, `-c '<code>'`, `-` (stdin) — followed by the modifiers
`--set key=value`, `--log <file>`, `--quiet` / `--verbose`; `print_usage` and the no-argument
default benchmark are byte-identical, and `-c`, `-i` and `-` changing from "unknown validation" to
a console form is the only behavioural change to an argument the binary accepted before (S24 CL-7, owner
ruling 4 of 2026-10-30: the no-argument benchmark is gone; with no argument the binary prints the `--help`
text, which now also lists `--atlas`, the console forms and `--serve`, and exits 1). Exit
codes: 0 success; 1 usage / file not found / undeclared `--set` key; 2 parse error (the whole file
is parsed before anything runs); 3 runtime error, every `ENGINE_CHECK` and `hecke::HeckeOverflow`
included; 4 a failed `assert` / `expect_error`; **5** `hecke::NotImplementedInThisBuild` — a legal
mathematical setting this build cannot execute, never reported as a bad value or a failed
computation. The one-line preservation gate: a `-c` session computing `A^{(1)}(T_2)` at
`(10, 691)` prints the same hash as `golden("n=10 ell=691 p=2 r=1", "A(T_p)^1")`. The five smoke scripts live in
`Console/scripts/`, the frozen pre-branch CLI output in `Console/scripts/cli_frozen/`.

#### Console decomposition surface (C1b) — `Console/Bindings/Decomposition.cpp`, `Console/Bindings/Presets.cpp`, `HeckeExt/RegisterHeckeExtensionVerbs.*`

The third phase of the console (hecke-extensions slot 4, WP-5;
`docs/implementation/slot4/WP-5_report.md`; [P] v3.2 §10 Phase C1b): the objects the extension
stage's single golden re-baseline moved, bound against the **post-E0b** `hecke_report/v2`. Three
types (`Decomposition`, `Block`, `Report`) and three verbs (`decompose(ops, q)` with `q`
mandatory, `report(D [, level_a, path])`, `crosschecks(T)`), plus the six `LocalSystemPresets`
local systems (`s1_scalar`, `s1_unipotent`, `cylinder_*`, `moebius_*`), which carry no
tessellation model and which `hecke` / `family` therefore refuse by name. `TypeInfo::hash` on a
`Decomposition` **is** the golden `decomp_*_invariants` recipe and `.witness_hash` the
`decomp_*_witness` one, so `hash(D)` and `hash(D.U)` compare directly with `golden(...)`; a
`report(D, level_a = true).json` hashes to the golden `report_full^q` entry byte for byte. The
**mathematical settings become `set` keys**: a third registry seam (`Registry`'s settings
installer, the analogue of C1a's two exception seams) lets `Console/Bindings/Decomposition.cpp`
register one console setting per `hecke::MathSettings::keys()` entry, validated and applied
through `MathSettings::set()` alone — so `set locality = strict` works and a key a later slot
appends needs no console edit. The script set grows to **16** numbered scripts with frozen
`.expected` transcripts (`#! oc-format 1`; `#~` annotation lines excluded from every comparison),
emitted by the owner-gated `ConsoleScriptEmit` and cross-checked, hash by hash, through
`golden(...)` at fingerprint `0`. **The extension layer registers its own console verbs**
(`HeckeExt/RegisterHeckeExtensionVerbs.cpp`: `sturm_bound(k, ell)` over the real `SturmState`,
`u_ell_decision(n, ell)`; [OD] slot-3 close-out 1), called from `main.cpp`'s existing console
branch — which costs exactly one exact-path exception in `check_console_includes.sh` rule 2 and a
new one-element `Console/`-only exception array in `check_heckeext_includes.sh` rule 2, both
reasoned; rule 1 of each and `ConsoleCore`'s STL-only rule are untouched. Not bound **as C1b
shipped**: `bernoulli_mod` and `glover_factors` (WP-7 had not merged when C1b froze its
transcripts — bound in slot 5, below), `solve` for under-determined systems and the general
π-primary `jordan_type` (C2), the local-algebra invariants (C5), 64-bit types.

#### Console — C1b's deferral closed and C5's early scripts (hecke-extensions slot 5, WP-10)

`docs/implementation/slot5/WP-10_report.md`; [X] §8 slot 5 Lane C, [P] v3.2 §10. Three things,
none of which moved a golden value or an existing frozen transcript:

* **The two deferred verbs are bound**, from the same `HeckeExt/RegisterHeckeExtensionVerbs.cpp`
  and therefore under the same two exact-path guard entries — no second console dependency in
  `HeckeExt/`. `bernoulli_mod(w, ell)` returns `B_w ∈ F_ℓ` as an `Int` and passes the unit's named
  `BernoulliOutOfRange` through as an ordinary console runtime error, so `expect_error` can pin
  the refusal; `glover_factors(n, ell)` returns a `Record` (`n`, `ell`, `dimension`, `length`,
  `factors` = `(sym, det_twist, multiplicity, dimension)` records, `sl2_multiplicities`, `text`,
  `json`). **The `det`-twist convention the verb reports is the pipeline's standard-module one**
  ([WP4-7] F3) — `Sym^n` of the standard representation, the one `ρ_n` acts on, not of its dual,
  which would shift every `det_twist` by `−n` — and the verb's doc string says so.
* **`MathSettings::canonical_text()`, `to_json()` and `text(key)` are one loop over `keys()`**
  built on a single per-key view (`HeckeSettings.cpp`'s file-local `view_of`), instead of three
  hand-written copies of the same six spellings. A key is now spelled in exactly **one** place,
  and a key appended to `registry()` without a `view_of` arm **throws** rather than silently
  rendering `""` or dropping out of the fingerprint. The at-default test stays the **struct**
  comparison the old lists used, not `text == defaults().text(key)`: a struct can carry a member
  the text does not render (`u_ell = {Auto, budget_mb = 1024}`), and the two tests disagree
  exactly there. The emitted text is byte-unchanged — proved against the pre-WP-10 writers copied
  verbatim out of `2b1b339`, 7462 comparisons over the all-defaults instance, every key off its
  default under every source, the full 768-point non-default cross product and three hand-built
  structs; the all-defaults fingerprint is still `0`.
* **Four new scripts, 017–020**, the first of [X] §8 slot 5 Lane C's "engine `.oc` scripts for the
  E0–E2 cases": `017_predictions.oc` (the two new verbs — the Bernoulli rationals as residues, the
  ten Kummer cells of [E] Claim 1.8 **derived** rather than copied, the regular primes `ℓ ≤ 31`,
  the irregular pair `(37, 32)`, the refusal at `w = ℓ − 1`, and Glover's structural invariants
  over `n ≤ 3ℓ` at `ℓ ∈ {5, 7, 13}`), `018_e0_locality_grid.oc` (E0a's verdict from the console —
  per-block `local` / `certified` / `phase` / residue degree / witness degree on six grid cells in
  **every** degree that carries cohomology, `splits = 0` including the three-operator refinement),
  `019_e1_stage1_sturm.oc` (Stage 1's two decisions on the ten Kummer cells — `u_ell_decision`
  7 admitted / 3 refused with `predicted_mb`, `B'(k, ℓ) = 2` on all ten — plus [E] `cl:bprime`'s
  two counterexamples `(22, 5)` and `(26, 7)`, where `{2, 3}` is a *proper* subalgebra, with the
  R3 resume), and `020_e2_ramanujan_10_691.oc` ([E] `cl:ramanujan` at `(10, 691)`: the eigenvalues
  `667, 252, 684, 531, 1` derived from `τ(q) ≡ σ_11(q) mod 691` rather than copied, Jordan type
  `(2, 1)` for every `T_q − a_q` and for `U_691 − 1`, the **four** exact identities in
  `M_3(F_691)` including `3(U_691 − 1) = −542(T_2 + 24)`, the one local block with
  `min_poly = witness_poly²` (i.e. `A_S = F_691[ε]/ε²`), and the basis-dependent
  `A^{(1)}(U_691) = I + 221 E_31` asserted but deliberately not printed). **The 16 existing
  `.expected` files and `cli_frozen/` are untouched**: a `CONSOLE_EMIT_EXPECTED=1 ConsoleScriptEmit`
  run rewrites all 16 byte-identically. Still not bound, and why: the `hecke_ext/v1` record object
  (`HeckeExtDriver`, `A_S`, the Loewy/socle profiles, the generation verdict) is **C5 proper**,
  which [P] §10 gates on E5's record-schema freeze.

#### Console — C2b, the harness verbs and the bench extraction (hecke-extensions slot 7, WP-8)

`Console/Bindings/Harness.cpp` binds the harness: `validations([tier])`, `run_validation(name
[, inherit_settings])` (refuses unknown names, the owner-gated emitters and a validation already
in the call chain), `bench(mode, n, ell, p, r, family, repeat, lean, cross_checks, count_allocs,
inherit_settings)` over the public `bench::RunMode`, `micro(op, a..d, backend, repeat)`
(`micro("cuda")` refused as CLI-only), `campaign_spec` / `campaign_spec_text` (the one handle
type `CampaignSpec`), `campaign_plan`, `run_campaign`, `golden_subset`, `timed`, `bench_line` (a
`#~` line, the exact bytes `--bench` prints) and `rss`. Every harness verb runs with the session's
settings **lifted** to its baseline (`SettingsScope`) unless `inherit_settings`, with `std::cout` /
`std::cerr` captured unless `verbose`. The console has no float, so times and MiB figures are
Strings with Int micro-unit twins (`total_us`, `wall_us`, `peak_rss_kb`). The substrate changes are
the four gaps of [P] §14.2: **G4** — `Bench/BenchDriver.h` exposes `bench::RunMode(ModeArgs) ->
BenchRecord` and `bench::FormatBenchLine`, `RunBench` keeping its argument parse verbatim, with
`--bench`'s stdout and exit code byte-identical on 45 cases (`docs/matrix-engine/tools/bench_identity.sh`);
**G4b** — `Util/Rss.h` (`PeakRssMiB`, `CurrentRssMiB`, `ResetPeakRss`, header-only), used by the
bench, campaign and console; **G9** — `hecke::IsDicksonExceptional` public in `Hecke/DicksonCount.h`;
**G14** — `Hecke/HeckeLinAlg.h` (`PartitionFromNullities` moved verbatim, `SolveColumnsExact`
re-exported). `--log` logs script / `-c` / stdin input lines. Script `022_harness.oc` is a new
artefact; `ConsoleDeterminismValidation` (`standard`, 122 checks) gates [P] §10 C2 (a)–(e).

#### Console — C4, hardening, every determinism arm, documentation (hecke-extensions slot 8, WP-10)

`ConsoleErrorValidation` (`fast`, 107 checks at the slot-8 close): every [P] §8 row reaches its
exit code with `file:line:col` (and the creation site for a lazy failure) through real script files
on the `--script` path; the exit-1 rows; a failed handle is never retried; the REPL survives every
error; **post-throw integrity** — after seven induced throws the same session recomputes 13 golden
objects of `(10, 691)` and matches `golden(...)`, under `device = cpu` and `gpu`; arm (K) pins
`coefficient_ring` (`set coefficient_ring = "Z"` exit 5 with no location, `"Z/ell^1"` exit 3, a
pipeline verb under `Z/ell^2` exit 5, `--set coefficient_ring=Z` exit 1 — the exit-5 form of the
last, and the `set`-statement error position, are C5's Core batch, slot 9; *since slot-24 D6* `Z` is stored and
legal on `set` and `--set` (exit 0), every verb but `descent` under it exits 5 naming itself, and the reserved
pin is `Z/25`).
`ConsoleDeterminismValidation` gains C4 (a): the C1 set 001–016 under `threads ∈ {1,4,16,32}` ×
`program_cache ∈ {on,off}` × `device ∈ {cpu,hybrid,gpu}` (24 arms) with one digest
`0xf6ed04bbe8e6b60a`, device arms `[SKIP]` without a device; `CONSOLE_DETERMINISM_ARMS=threads`
restricts it to the four thread arms (the `CheckThread` run); it stays `standard` (531 checks,
≈ 20–30 s). Hardening: `bind::LazyCompute` keeps exit 5 (`NotImplementedInThisBuild`) through a
lazy handle (it was 3). **`docs/console/console.md` is generated** by the binding verb
`help_markdown()` ([P]'s `help --markdown`; `Console/Core/` stayed frozen) via
`docs/console/gen_console_md.sh` (`--check` diffs) — regenerate it whenever a verb, type or setting
is registered. The 22 `.expected` files and `cli_frozen/` are byte-unchanged. [P] §10 C4 (d) (the
budget of the names C4 registers, `≤ 5 s`) is measured by `docs/matrix-engine/tools/console_c4_budget.sh`
in the lead's window.

#### Console — C5a / C5b / C5c (hecke-extensions slot 9, WP-12, WP-13, WP-8, WP-8c)

**C5a (WP-12, `Console/Bindings/`).** *E8's ring lift* ([E] `sec:ring` (h)): at `ell ≥ 5`, under
`coefficient_ring = Z/ell^k`, `symmetric_power` returns a LocalSystem over the ring
(`GenerateSL2ZRelationsRing`); `cohomology(L)` a Cohomology honouring `.coefficient_ring`,
`.computed`, the four degree fields, `.lengths`, `.invariant_factors(q)`, the `K`-mode trio
(`.ladic_type_certified`, `.r_K(q)`, `.ladic_type(q)`), `.bockstein_rank`, `.higher_torsion_count`
and `.red(q)` (a Matrix over `F_ell`); `hecke(H, p)` with `r = 1` (`p = ell` included) honours
`.coefficient_ring`, `.A(q)` (a List of Int rows — row `i` lives modulo `ell^{e_i}`) and
`.charpoly_free` (`{precision, coeffs}`). The ring is read once at dispatch and stored in the payload;
`ensure()` installs exactly that ring around construction, and a handle of one ring handed to a verb
under another is refused with `NotImplementedInThisBuild` (exit 5). The `ladic_level` state is the
handle's R3 `ResumableState` (`resume` at an uncertified level refuses by the non-budget rule, exit
3). Field members (`dims`, `C`, `Z`, `B`, `H`, `P`) raise their accessor's `logic_error` (exit 3);
**every other member refuses with exit 5 through one mechanism, `bind::GateTypeOnRing`**, so a member
added later refuses until (h) lists it — including the harmless structural ones (`LocalSystem.n`,
`HeckeOperator.p`, `Cohomology.ell`, …; open). Verbs refused at dispatch (exit 5): `hecke(…, r ≥ 2)`,
`family`, `decompose`, `report`, `crosschecks`, `dual`, `pairing`, and every pipeline verb at
`ell ∈ {2, 3}`. `hash()` of a list of Ints follows the golden list recipe (length, then entries).
*E7*: `dual(L)` → `ContragredientLocalSystem` (`Phi`, `induced_Phi(q)`, `A(p, q)`, `A_M(p, q)`,
`intertwines(p)`, …) and `pairing(L, D)` → `Pairing` (`perfect(t)`, `gram(t)`, the circle pairing,
`certificate`, `pd_gate(primes)`), `Bindings/Duality.cpp`; every E7 golden object at `(10, 691)`
reachable with a byte-identical hash. *The Core batch* (owner decision 2 (ii), the only two
`Console/Core/` edits of the slot, recorded in [P] as named exceptions): `Evaluator.cpp`'s `exec_set`
back-fills the statement's position into a `ConsoleError` (`file:1:1: not implemented in this
build: …`), and `ConsoleCli.cpp` makes a `--set` refusal of kind not-implemented exit 5 (an invalid
value or an undeclared key stays exit 1; `ConsoleErrorValidation` (K) 1 → 5 in the same commit).
`ConsoleErrorValidation` (K) closes (h) with 61 single-access scripts under `Z/ell^2` at `(10, 691)`.
Scripts 023–025. **Open (Core, next batch)**: `Evaluator::object_member` does not wrap a member
getter's exception, so such an error carries no `file:line:col` (exit codes are right: the gated types
convert in the bindings).

**C5b (WP-13, `HeckeExt/RegisterHeckeExtensionVerbs.cpp` + two console-free units).** 13 types and
30 verb overloads under 29 names: `ExtRecord` (`ext_record(n, ell, cone, sign_split, presentation,
sturm, commutant)`, lazy) with `MaximalIdeal` / `HeckeAlgebra` / `LoewyProfile` / `ExtensionClass` /
`Presentation` children, `Atlas` (`atlas(ell)`, `ell ∈ {5, 7, 11, 13}` in-process; `atlas(691)` a
typed `atlas_unavailable` refusal), `GF` / `GFElt` (`GF(ell, r)`, `canonical_field(ell, r)`, the
`gf_*` verbs — C1a's `add` / `mul` take `any`), `Settings` (`settings_snapshot()`; C1a's
`math_settings()` keeps its Record), `Involution` (`iota(H)`), `BoundaryCohomology` (`boundary(H)`),
`ConeCohomology` (`cone(H)`, `.h(p, q)` and `.pair_homotopy(p)` per prime), `L_map(H_lower, H)`,
`check_identities(H [, primes [, items]])` (items 6–7 assembled on request), and the local-algebra
verbs `nilpotent_part`, `radical`, `tangent_space`, `socle`, `nilpotency_index`, `loewy`,
`socle_series`, `is_local`, `algebra_invariants` on any commuting family through
`HeckeExt/HeckeAlgebraInvariants` (certificate-free, decided not searched: `rad = ker Frob^e`,
Berlekamp's count of maximal ideals, `Ann(rad)`, the Jordan–Chevalley split `s = t^(ell^N)`).
`HeckeExt/HeckeExtBindingSupport` composes the pipeline objects in the order an existing validation
already does. Not bound: `MatrixQ` (not landed), `PairComplex` (the record's pair *is* `Cone(r)`),
`divided_power` (it is E7's `ContragredientLocalSystem`). Every pipeline verb of the set refuses a
non-default `coefficient_ring` at dispatch and in its lazy compute (exit 5). Scripts 040–047 (040–045
the [S Stage 9] cases, 046 `identities.oc`, 047 the local-algebra verbs);
`HeckeExtAlgebraInvariantsValidation` (`standard`, 404 checks).

**C5c from the console (WP-8, WP-8c).** The harness verbs `campaign_spec` / `campaign_spec_text` /
`campaign_plan` / `run_campaign` reach the ring job loop through the same parse and run functions.
Since WP-8c (`Console/Bindings/Harness.cpp`) `campaign_spec` and `campaign_spec_text` rethrow a
`hecke::NotImplementedInThisBuild` as the console's not-implemented error (exit 5) ahead of their
generic wrap, so a spec refused for a ring reason is exit 5 while an ordinary spec error stays exit 3
(`ConsoleErrorValidation` arm (M)); script `048_c5c_ring_campaign` runs a two-job ring campaign at
`(6, 5)` over `Z/25` from the console and pins the point's values against `golden(...)`.

At the slot-9 close: 34 numbered scripts (001–025, 040–048), every new transcript a first freeze;
the 22 pre-existing `.expected` files and `cli_frozen/` byte-unchanged; `ConsoleErrorValidation`
218 checks, `ConsoleScriptValidation` 346, `ConsoleDeterminismValidation` 567 — its C4 (a) digest
`0xf6ed04bbe8e6b60a` unchanged; its (a) all-scripts digest is not pinned (it moves with every new
script). Since slot-9 WP-9 `gen_console_md.sh` requires the binary path (no silent fallback to a
possibly stale in-source binary).

#### Console — C5 leftovers (hecke-extensions slot 10, WP-12)

Specified first by [P] v3.8-pre.1 (§2 C7, §3.6, §8, §10) and [E] v1.11.0-pre.1 `sec:ring` (h) (WP-2).
**The one named `Console/Core/` exception** (owner decision 6 (A)), at **two sites** (a lead default:
the plan named one function, the type-level `resume` refusal needs the second) — `git diff` of
`Console/Core/` since the base shows exactly these: `Evaluator::object_member` calls the member
getter inside one `try` in `eval_method`'s catch order (a `ConsoleError` gets `set_pos_if_unknown(pos)`
and is re-thrown; `ExitSignal` / `QuitSignal` pass; any other `std::exception` goes through
`ThrowWrapped(registry, ex, "<Type>.<member> failed", pos, &obj)`, so the kind classifier decides the
code and the creation site is noted), and the core `resume` verb back-fills `ctx.pos` onto a
`ConsoleError` from the type's resume hook. No shipped exit code moves (every gated getter already
converted through `GuardedMember`); a *raw* getter raising `NotImplementedInThisBuild` is now exit 5
(was 3). **Bindings**: `LocalSystem` gains the structural member `coefficient_ring`
(`hecke::CoefficientRingText(ring_k)`, `"F_ell"` on a field or preset handle); `bind::GateTypeOnRing`
honours `LocalSystem.n / .d_V / .coefficient_ring` and `HeckeOperator.p / .r` on a ring handle (pure
payload reads, no computation forced); every other ring-handle member keeps exit 5; the ring-mismatch
rule at a verb's dispatch (exit 5 naming both rings) pinned both ways. `Harness.cpp`'s one
`CampaignVerbHandler` wraps `campaign_plan`'s body and `run_campaign`'s `RunCampaignSpec` call
(`ConsoleError` re-thrown; `NotImplementedInThisBuild` → exit 5 before `std::exception`; others exit
3); no input reaches the exit-5 branch at the base (a spec's ring refusals fire at parse time; the job
loop and the ext pass catch per job / per cell) — recorded, no test hook. `ConsoleErrorValidation`
arm (W), 218 → 294 checks (negative control: the two Core sites reverted fail 21); script
`026_c5_leftovers_ring_members` (first freeze); `console.md` regenerated. At the slot-10 close: 35
numbered scripts (001–026, 040–048), the 34 pre-existing `.expected` files and `cli_frozen/`
byte-unchanged; `ConsoleScriptValidation` 350, `ConsoleDeterminismValidation` 570, C4 (a) digest
unchanged.

#### Console — digit handles (hecke-extensions slot 11, WP-18c)

Specified by [E] v1.12.0-pre.2 `sec:ring` (h) (not by a pre-release of [P]; [P] v3.9 records it as
built). Under `coefficient_ring = Z/ell^k` with `ell^k ≥ 2^64`, `ell ≥ 5`, `symmetric_power`,
`cohomology` and `hecke(H, p)` run `Hecke/LadicCell`'s digit route: `bind::GateTypeOnDigit`
(`Bindings.{h,cpp}`) with the digit member list; `Cohomology.precision` (new); a digit
`HeckeOperator`'s `charpoly_free` is the Record `{precision, coeffs}` with the coefficients as residue
Strings. The field members (`dims`, `C`, `Z`, `B`, `H`, `P`) raise the field accessor's
`std::logic_error` (exit 3), as on every ring handle (WP-14 pass 2 M-1); other members off the digit list
exit 5. The per-cell caps are checked at the console's dispatch at `k + K_w − 1` (the largest reachable
working precision). `ConsoleErrorValidation` (K) +14 digit rows plus the `H.C(1)` row → **309** checks.
**Gaps recorded**: the console's `uint32_t` limit refuses `Z/5^14 … Z/5^27` and `Z/691^4 … Z/691^6` while
larger `k` is served ([P] Q9, an owner item — *closed by slot-12 WP-17*, below); `hecke(H, p)` on a digit
handle recomputes the cell per operator (deterministic; cost only). **θ at the console** (`dickson_les`, `theta`; [P] v3.9-pre.1 §3.6)
was specified and **not built** (WP-16 gave way); its `ell < 5` → exit 3 row now agrees with the build
(`DicksonThetaCell`'s precondition, slot-11 WP-17). No `Console/Core/` line moved; the 35 transcripts are
byte-unchanged; C4 (a) digest unchanged.
**Wide handles (slot-12 WP-17, post-close; [P] v3.9.3, Q9 decided (a) by the owner 2026-09-26).** Under
`coefficient_ring = Z/ell^k` with `2^32 ≤ ell^k < 2^64`, `ell ≥ 5` (`bind::IsWideCell`), `symmetric_power` /
`cohomology` / `hecke(H, p)` build the `uint64_t` instantiations (`LocalSystemSimplicialComplex64`,
`EquivariantCohomologyOnK64` and its `F_ell` / `Z/ell^2` comparison objects, `HeckeCosetTables64` /
`HeckeTauTable64` / `HeckeOperatorOnK64`) by the campaign job loop's recipe (`RunRingPipeline<uint64_t>`), so
the per-cell route is the campaign's (`uint32_t` < `2^32` ≤ `uint64_t` < `2^64` ≤ digit). `bind::GateTypeOnWide`
(the digit gate's wrapper, every member without a `uint64_t` getter passed through to `GateTypeOnRing`) gives a
wide handle exactly a `uint32_t` ring handle's member set: the (h) list honours, the field members exit 3 by the
`uint64_t` object's own accessor, the rest exit 5; entries above `2^63` are decimal Strings.
`ConsoleErrorValidation` arm (Q9) → **539** (band edges, campaign value identity on seven cells, the member
closure); script `028_wide_band` (first freeze; 37 scripts); ConsoleDet digest unchanged.


#### Console — θ verbs (hecke-extensions slot 12, WP-8)

[P] v3.9.2 §3.6 as built: `dickson_les(n, ell)` → the lazy handle `DicksonLES` (wrapping
`hecke_ext::DicksonThetaCell`; members `.n`, `.ell`, `.n_up`, `.dims`, `.ranks`, `.maps`, `.exact`, `.ker_theta`,
`.im_delta`, `.ker_equals_im`, `.dickson_count`, `.certificate`, `.coefficient_ring` — the structural ones do not
force the compute; `.maps.delta` is the degree-0 connecting map) and `theta(H, H_up)` → Record `{n, n_up, ell,
induced, ranks, ker, image, twist_check, u_ell_zero}` (`DicksonInducedMaps` + `HeckeOperatorFamily` on the two
handles). Both live in `HeckeExt/RegisterHeckeExtensionVerbs.cpp`: a new `Console/Bindings/` TU could not include
`HeckeExt/` (`check_heckeext_includes.sh` rule (1)), and a second console-including TU in `HeckeExt/` is forbidden
by rule (2). `ell < 5` exit 3 (`ENGINE_CHECK_MSG`, `lem:h2torsion`), a ring exit 5; a failed `DicksonLES` rethrows
on every access. `ConsoleErrorValidation` arm (T) (309 → 347); script `027_dickson_theta` (first freeze; after
WP-11 A13 it compares `theta` with the LES handle, not with `L_map`, which calls the same routine). No
`Console/Core/` line moved; C4 (a) digest unchanged.

### Hecke action — module-by-module (`src/hacs/Hecke/`)

The full bullet list of `CLAUDE.md`'s "Hecke action" section. `CLAUDE.md` keeps the one-paragraph
summary and the pointer here.

- **Exact-integer / FP-filter substrate** (`ExactInt`, `Predicates`, `QuadPoint`, in the `HeckeCore` static library) — overflow-checked exact 2x2 integer matrices (`Mat22`), the early-reduction group-element triple, and certified FP64/FP32 sign predicates with exact fallback (disabled by `HECKE_PURE_INTEGER`).
- **Coset + tau tables** (`HeckeCosetTables`, `HeckeTauTable`, `SL2ZTessellationTables`) — exact coset representatives/cocycles for `Γ_0(N)\Γ` (`N = p^r`), and the certified `g`-twisted chain datum `τ` (mandatory exact certification `∂τ = τ∂` at construction).
- **`HeckeOperatorOnK`** — assembles the fused cochain map `Θ_g = ω•∘Ξ_g`, producing cochain-level matrices (`Θ^{(q)}_flat`/`Θ^{(q)}_eq`) and cohomology-level matrices (`A^{(q)}(T_p)`), with a second, independently-bracketed evaluation route asserted bit-identical to the first.
- **Operator family** (`HeckeOperatorFamily`) — `T_p`, `T_{p^r}`/`T_n` (recursion + an independent direct double-coset route), `T(p,p)` (diamond scalar), `U_ell` (bad prime, same pipeline as `T_p`).
- **Block decomposition** (`FpPoly`, `HeckeModuleDecomposition`) — exact F_ell[X] polynomial arithmetic and certified factorization; primary decomposition of `H^q` as a module over the commutative F_ell-algebra generated by one or several computed Hecke matrices (generalized-Jordan partitions, residue degrees, certified change of basis — never trusting randomized factor-finding without a deterministic certificate).
- **Report** (`HeckeReport`) — hand-rolled JSON writer (no third-party library) covering all three matrix levels (cochain / cohomology / block-diagonalized).
- **Cross-checks** (`HeckeCrossChecks`, `BarCocycleH1`) — the classical three-map `α`/`β`/`ω` factorization and an independent bar-cocycle `H^1` route, both asserted to agree with the fused pipeline above.
- **Boundary datum and boundary operator** (`HeckeBoundaryDatum`, `HeckeBoundaryOperator`; hecke-extensions slot 1, WP-4a/4b — contract chapter `sec:boundarydatum`, implemented since [C] v1.3.3) — the certified `Γ`-level boundary datum `τ_∂` over `Z` (built for every `ell`, `ell ∈ {2, 3}` included; certified in the constructor like `τ`) with the `B_N/Γ_∞` coset table, and the boundary Hecke operator `Θ^∂_g` / `T_p^∂` on the circle model (`LocalSystemSL2Z::CreateSL2ZBoundaryPathTriangulation` / `GenerateSL2ZBoundaryRelationsElt`, the demo's path lifted into a library call with the `−I` self-relations), with the Shapiro route A and the closed-form route B both asserted equal to the normative operator on cohomology inside `compute()`, and the record fields `boundary_model = circle`, `boundary_is_group_cohomology = (ell != 2)`, `q_max = 1` derived. `obl:taubdry`(i)–(vii) discharged by `HeckeBoundaryTauValidation` + `HeckeBoundaryOperatorValidation`. Since slot-2 WP-7 (E4b) **`HeckeExt/HeckeBoundary`** computes, on top of them, `H^1_! = ker r^1` ([C] `cl:les`(2)) with its Hecke action, the joint `1 + p^{n+1}` eigenspace (**2-dimensional at every Kummer cell**), Harder's criterion (`consistent` on all 37 applicable cells; `H^1_! ≠ H^1` at every Kummer cell) and the Harder split, with golden collectors defined and never emitted; and **`Hecke/HeckeBoundaryDiagnostics`** records the two diagnostics of [C] `rmk:conestrict`(2), `cochain_commutes` and `eta_zero` (the cusp-support walk) — both false on every `(cell, p, ν)` of the grid, never branched on. Not yet in `HeckeReport` / the campaign record (E2).
- **Pair homotopy** (`HeckePairHomotopy`, `HeckeIntegerSolve`; slot 2, WP-8 — contract chapter `sec:cone`, `def:pairhomotopy` / `lem:etaexists` / `obl:eta`(i)–(iv)) — the certified pair homotopy `η : C_*(∂X) → C_{*+1}(X)` over `Z` for **every** `ell` (no mod-`m` path; a tier failure aborts), `∂η + η∂ = j τ_∂ − τ j` against the shipped `τ` and `τ_∂`: vertex slots by the `alg:tau` step-2 path device, edge slots by the unique 2-chain fill through `HeckeIntegerSolve` (the one integer solver, moved verbatim out of `HeckeTauTable.cpp`), certified in the constructor, `eta_zero` recorded (false on every table of the grid — the `η`-table is needed on every cell), JSON `hecke_pair_homotopy/v1`. The cone action `Φ_g`, the derived `h = η̃` and `obl:eta`(v) are slot 3's.
- **Mathematical settings** (`Hecke/HeckeSettings.{h,cpp}`, slot-2 WP-1 — [X] §1.2/§1.5, [OD] R1) — `MathSettings`: the values in force with their `source`, the canonical text of the **non-default** entries and its FNV-1a-64 fingerprint (`0` at the defaults, so a golden mismatch can never be explained by a setting), `to_json()`, and one validation point `set(key, value, source)`. The registry holds, in fingerprint order, **`locality`** (`budget=<N>` \| `strict`, default `budget=64`), **`u_ell`** (`auto` \| `off` \| `budget_mb=<M>`, default `auto` / `M = 2048`; slot-3 WP-1), **`sturm`** (`auto` \| `off` \| `cap=<B>`, default `12·B(k)`), **`sturm_unavailable`** (`nonfinal` \| `heuristic`, default `nonfinal`; both slot-3 WP-2), **`commutant_budget`** (default `kCommutantBudget = 2·10^10`, whose one definition moved here in slot-4 WP-1, with `CommutantRoute::kCommutantBudget` a `constexpr` alias; `CommutantRoute` reads the setting and its R3 resume refuses a lower budget), **`final_mode`** (slot-4 WP-1), **`field_polynomial`** (`least` \| `conway`, default `least`; `conway` parses and round-trips but `HeckeExt/HeckeCanonicalField::FieldPolynomialFromSettings` raises the named `hecke::NotImplementedInThisBuild` — the `locality = strict` precedent, inverted in time) and **`split_field_report`** (`canonical` \| `own_field`, default `canonical` per [OD] OQ10; **no consumer in this build** — the report layer that reads it is E6's, in slot 6, the `u_ell` pattern of slot-3 WP-1; both slot-5 WP-7) — **eight keys**, each appended with its default unchanged, so the all-defaults fingerprint is still `0` and no golden value or job id moved. `ScopedMathSettings` / `ScopedLocality` are `thread_local` and propagate onto `engine::tape::run_concurrently()` tasks (`CheckThread`-clean). **`locality = strict` is implemented since slot-3 WP-3 and no longer throws**; `hecke::NotImplementedInThisBuild` (and its `not_implemented_in_this_build:` tag) survives as the named build-capability error behind the console's exit code 5, raised by no settings value today. The TU consumes nothing of the pipeline. **Since slot-5 WP-10 the three text writers are one loop over `keys()`**: `canonical_text()`, `to_json()` and `text(key)` are all built on a single file-local per-key view (`view_of`), so a key is spelled in exactly one place and adding one is four edits (member + source, a `registry()` row, a `view_of` arm, a `set()` case) instead of seven. A key appended to `registry()` without a `view_of` arm **throws**, rather than silently rendering `""` or dropping out of the fingerprint; the at-default test stays the **struct** comparison (a struct can carry a member the text does not render, and a text-based test would disagree exactly there). The emitted text is byte-unchanged, proved against the pre-WP-10 writers copied verbatim out of `2b1b339` over 7462 comparisons. **Slot 7 (WP-2)**: **`presentation`** (`off` | `on`) and **`predictions`** (`annotate` | `assert`) are appended — **ten keys**, fingerprint `0` at the defaults — and a setter's `source` is an argument: `ScopedUEll(u, src = Console)`, `ScopedMathSettings(s, src)` through `MathSettings::with_source` (a value at its default is always stamped `default`; the golden harness stamps `spec`). Since slot-7 stage 1 (1) the golden texts and `HeckeExtDeterminismValidation` see the record's top-level `settings` member reduced to `{fingerprint}` (`ReduceSettingsToFingerprint` in `Golden/GoldenHarness.cpp`, a depth-1 member walk), so a key registered at its default moves no golden line; the record itself still carries every key with value and `source`.
- **Locality certificate** (`hecke::CertifyLocality` in `HeckeModuleDecomposition.h`, `Hecke/SubspaceOps`; slot 1 WP-1, slot 2 WP-1) — the certificate of [E] Cert. 5.2. Slot 1 shipped it read-only; **slot-2 WP-1 (E0b) calls it inside `ComputeMultiOp`'s refinement loop**: a candidate with ≥ 2 distinct irreducible factors **splits** the block (sub-blocks at the parent's position, in `CanonicalLess` order), a candidate passing all of Cert. 5.2 certifies it, and an exhausted budget emits it `local = false` with a proven lower bound and a **resumable `LocalityState`** ([X] §1.3.1 R3 instance 2) — never silently, and the loop never spins. `k = 1` is local for free and the Teichmüller lift `ŵ` is never formed. `PrimaryBlock` carries `local_certified`, `witness_poly`, `w_hat_exponent` and `character`; `certify()` re-derives them as codes 25–29. Value-preserving: the slot-1 grid verdict (every block local, `witness_changes = 0`) meant the loop takes no new branch on the golden grid, so `GoldenReference.inc` was unchanged by WP-1 and E0b's re-baseline was exactly the 384 allow-listed **report** lines of WP-2. `Hecke/DicksonCount.h` (slot-1 WP-2) is the one Dickson count. **Strict mode** (slot-3 WP-3, [X] §3.1, [E] `sec:localcert`): after the *same* bounded linear witness family budget mode runs, an undecided block enters `HeckeModuleDecomposition::StrictLocalityRoute` — `rad A_S = ker Frob^N` (`SubspaceOps::frobenius_matrix` / `frobenius_kernel`; the trace form is deliberately not used), then the Berlekamp subalgebra `B = ker(Frob_Ā − id)`: `dim B = 1` **is** locality, `dim B ≥ 2` splits (every split strictly reduces the dimension, so it terminates) — and the certifying witness is drawn from the whole residue field `Ā`, reported as `PrimaryBlock::witness_matrix` and re-derived by `certify()` (code 30: a matrix witness must commute with the family). Byte-identical to budget mode wherever budget mode certifies, by construction; never the default; a non-zero fingerprint; `local = false` only by interruption (a cooperative, thread-local step limit), resumable. WP-3 also fixed a latent resume defect of slot-2 WP-1 (a carried certified block lost its certificate), value-preserving.
- **Reach of `U_ell`** (repaired 2026-09-16→17, hecke-extensions slot 3 WP-1 / phase E1b-0; `docs/KNOWN_ISSUES.md` §3 is now **RESOLVED**, `docs/implementation/slot3/WP-1_report.md`). The old limit — `hecke: exact multiply overflow` at `p = ell >= ~4580`, independent of `n` — was **not** in the coset construction (which builds and self-checks at `ell = 43867`) and **not** a failure of [C] `lem:bounds` (whose certified `B = max(B_tab, 4N^2)` is `1.0e8` at `ell = 5003`, `2B^2 = 2.0e16 << 2^63`, and `certify()` clause (e) passes). It was `QuadPoint::moebius` inside [C] `alg:tau` **step 1's fundamental-domain reduction**: the point's cleared coordinates reach `~145 N^2` and the Möbius step squares them, so `int64` dies at `N >= ~4580`. The repair is `thm:backend`'s own third tier — `QuadPoint` is now `QuadPointT<I>` (`QuadPoint` = `int64_t`, `QuadPointW` = `__int128`) and `construct_vertex` runs step 1 through `hecke::escalate_on_overflow`: **`int64` first, widened only after a `HeckeOverflow`**, so bit-identity wherever `int64` completes is a property of the control flow, and nothing *stored* widens. `hecke::ScopedExactTier` forces either tier. **The new limit is a different one and it is `lem:bounds`'s own**: `certify()` clause (e) requires `B = max(B_tab, 4N^2) ≤ 2^31 − 1`, i.e. `ell ≤ 23170` (largest prime 23167) — at `ell = 43867` the table now builds without an overflow and is then *refused by its own certification*, code 51, in 20 s (`--bench hecke 0 43867 43867`), which is the designed loud failure. Lifting that is a **storage** change (`Mat22W` as the stored transporter type) and is out of scope: `u_ell = auto` refuses every `ell > 23170` cell on memory grounds first. Measured: `--bench hecke 16 5003 5003` 73.1 s / 950 MB; `hecke 2 10007 10007` 356 s / 1019 MB; `hecke 16 10007 10007` 612 s / 1924 MB.
- **`U_ell` budget and the `u_ell` setting** (slot 3 WP-1): `HeckeExt/HeckeUEllBudget.h` is the pure, frozen decision `rss_mb = (ell+1)(c0 + c1 (n+1)^2)` with `c0 = 0.123152`, `c1 = 2.24985e-4` (`kUEllRssC0` / `kUEllRssC1`, model version `u_ell_rss/v2-2026-09-17`), re-fitted on a 16-point measured grid (relative-error least squares); residual band `+17.88 % / −15.94 %` (asserted both ways as `kUEllRssWorstOverPredict` / `kUEllRssWorstUnderPredict`), rms 9.8 %; `UEllDecision(16, 43867, 2048)` predicts 8254.76 MB and refuses. Two three-parameter alternatives were fitted and rejected (better rms, no better under-prediction, negative third coefficient — one of them predicts a *negative* RSS at `(1000, 13)`). `Hecke/HeckeSettings` registers the second mathematical key, **`u_ell`** (`auto | off | budget_mb=<M>`, default `auto` / `M = 2048`); its first consumer is Stage 1 of `HeckeExt/HeckeSturmSweep` (E1b, slot-3 WP-2), which consults `UEllDecision` to decide whether `ell` joins `S_0`; the **resume** of a refused `U_ell` (R3.3 item 4) needs `HeckeExtDriver` and is E2's (slot 4). Against [X] §1.5's placeholder prose the admitted `n`-ranges shrink (`ell ≤ 13` to `n ≤ 804`, `ell = 691` to `n ≤ 110`, `ell = 10007` to `n ≤ 18`); the ten Kummer verdicts (7 admitted, 3 refused) are unchanged.

- **Involution and sign split** (`Hecke/HeckeInvolution`; `HeckeExt/HeckeSignSplit`; slot 4, WP-3 / phase E3 — [C] `sec:involution`, `def:iota`(iv) v1.2.0, `lem:iotamodel`, `prop:iotacommutes`(1),(2), `prop:iotasplit`, `obl:iota`(i)–(iii),(v)) — the **production** `ι^* := −ι^*_geo`, an `EquivariantCochainComplexMorphismOnK` with one `−ε_σ ρ_n(ι)` block per simplex over a single interned `d_V × d_V` diagonal; `ι_K` proposed by an exact `QuadPoint` match of `z ↦ −z̄` and certified against `lem:iotamodel`; `obl:iota`(i)–(iii) discharged **blockwise and exactly over Z** in `compute()`, which **aborts** on failure; the `±` split of `prop:iotasplit`(1) stored on every `C^q_eq / Z^q_eq / B^q_eq / H^q_eq` at `2 ∈ R^×` and `sign_split = not_applicable` at `ℓ = 2`; and, in the ext layer (`HeckeExt/HeckeSignSplit`, `MatrixT<uint32_t>`), `[ι^*, A^{(q)}] = 0` (asserted at `ℓ ≥ 5`, recorded at `ℓ = 3`), `A^{(q)}_±`, the per-sign decomposition with cyclicity, and the Eisenstein line `soc(X^+_{4,m})`. Until slot 4 `ι^*` existed only inside validations. **Slot 5 integrated it into the record**: WP-1 emits the per-sign (E3) objects with `iota_sign` inside `hecke_ext/v2`, and WP-12a adds the record-level `iota_exact_comparison` ([OD] 2026-09-22 Q3) — the record's half of [C] `obl:iota`(ii)'s rider, saying whether the exact `Mat22` comparison ran and on which relation rows (31 rows, 31 exact, 31 compared at `(10, 691)`), refused by `HeckeExtRecord::verify()` code 23 if it misreports. `Hecke/HeckeReport`'s `hecke_report/v2` is still untouched — the two writers stay separate, by design. **Since slot-10 WP-7 (lever I-1)** `check_obl_iii`'s fifteen independent (degree, family) decisions and `build_split`'s flat and H-level splits run as host tasks through `run_concurrently` **in the serial order** (the first failure in task order, so the aborting check and its message are the serial loop's); the shared inputs are made read-only first (the shapes, `ρ_n(ι)² = I` decided once, the morphism's pull-back operators built once); each task writes only its own slots; on a one-worker pool the old serial order runs. `(160, 691)`'s sign split 1.80 → 0.79 s (it had not scaled with threads at all: serial `FlatMatrix` elimination); every stored object computed by the same code on the same inputs.
- **Cone complex** (`EquivariantMappingCone`, `Hecke/SL2ZBoundaryPair`; slot 3, WP-5 / phase E5-2 — [C] `sec:cone`, `def:pair`, `eq:conediff`, `eq:coneles`, `obl:coneexact`(iv),(v)) — `Cone(r)` of the pair as a cohomology-layer object, **generic** (no Hecke include, `uint32_t`), in `H_c`-indexing (`Cone^q = C^{q+1}_eq ⊕ C^q_eq(∂)`, `eq:conediff` verbatim — the sign convention of `CochainComplexMorphism::ConeComplex`, so the connecting map is `+r^{q+1}`) on the flat layout of `alg:assembly`; `Z / B / H / P` through `engine::blk` with the pipeline's D5b basis rules; the three map families `π_*^q`, `r^q`, `ι_*^q` of the long exact sequence in stored bases per degree; the per-complex degree fields derived (`bulk 2 / boundary 1 / cone 2`, none truncated; a `set` `q_max` with `truncated = false` rejected), the truncated branch of (iv) implemented degree-generically; `ConeCertificate` (thirteen items, a re-deriving `verify()`); golden collectors defined, never emitted. The restriction `r^•` is built **pipeline-side** in `Hecke/SL2ZBoundaryPair`, lifted verbatim out of `HeckeExt/HeckeBoundary` (which now consumes it) — value-preserving. At `(10, 691)`: `dim H^q_c = [0, 3, 0]`. **Cost, measured in slot 4 (WP-4 — E5 cost), which corrects the slot-3 open point verbatim**: `ConeCertificate::verify()` does **not** dominate — it is **half** the cone's wall (4.34 s build + 4.31 s verify at `n = 256`) and runs **~20 % below** the cone's VmHWM, which is set inside `compute()`'s `Z / B / H / P` elimination loop; and since E5 acceptance (d) is an **RSS** gate, no amount of certificate work can move it. Three value-preserving reductions — none of them sampling, relaxing or moving a clause, every clause of both certificates still running unconditionally inside `compute()`: (1) `ConeCertificate`'s span inclusions C2 / C3 / C5 are the rank identity `rank [B | Y] = rank B`, read off **one** RREF of `[B | Y]` by testing that no pivot lands in the `Y` block — the same test on the same elimination `engine::elim::solve_multi_rhs` does before back-substituting, minus the `ny × nb` coefficient matrix the caller discarded (verdict-identity *proved* by a shadow arm over the whole grid: 1408 calls, 2 false verdicts, **0 disagreements**); (2) the per-degree buffers of `compute()`'s elimination loop and of `verify()` are released at their last reader (pure scoping; the `BlockPool` interning order and the item evaluation order are unchanged); (3) the action's standard-basis sweep is batched (below). Measured (`Bench`, interleaved against a `9ae1d7a` binary on a quiet box): the cone **620 → 573 MB** at `n = 256` and 275 → 250 MB at `n = 160`, `HeckeConeValidation` 1.9 → **1.7 s**. **The measured verdict on [X] §6.2 E5 acceptance (d) (`RSS at n = 256 within 1.5× of hecke 256`) is NOT MET** — at `n = 256` and at every `n ≤ 200` — **and, as written, (d) is not decidable**: it pins neither the denominator's protocol (`--bench hecke 256 … --repeat 1` peaks at 262 MB and `--repeat 5` at 365–421 MB, so the same tree reads **2.19×** or **1.54×**; the `--repeat 5` spread, ±10 % at `n = 256` and ±28 % at `n = 160`, is itself larger than the 4 % by which the cone misses) nor which E5 object the numerator is (cone alone vs cone + action differ by **2.2×**: 573.2 vs 1243.0 MB). Under the `--repeat 5` denominator slot 3 implicitly used, WP-4 closed 71 % of the recorded gap, 1.66× → 1.54×. Restating (d) was the **owner's**, and on 2026-09-22 the owner took it ([OD] slot-4 close-out 1): the numerator is the **cone object alone**, the denominator `--bench hecke 256 134217757 2 --repeat 1` in a separate process in the same session, and the bound **2.0×**. **Slot-5 WP-5 put the cone on the tape and E5 acceptance (d) is MET**: the cone's `Z / B / H / P` loop records its two block GEMMs as tape `gemm_dense` programs, `H^q_c` / `P_c^q` go through `engine::tape::factor_basis`, and `ConeCertificate`'s C2 / C3 / C5 span inclusions run on the tape's borrowed-operand panel driver — **510.8–524.1 MB against 262.6–275.5 MB over five interleaved rounds, i.e. 1.90–1.95×, median 1.93×**, met at every `n` of the grid (1.58 / 1.81 / 1.86 / 1.89 / 1.93× at `n = 64 / 128 / 160 / 200 / 256`), and the worst cross-pairing of the five rounds, 1.996×, still under the bound. Nothing was sampled, relaxed or moved out of `compute()`. **Two facts from that measurement supersede slot 4's**: [WP4-4] finding 5 — "`verify()` runs ~20 % *below* the cone's high-water mark" — **no longer holds**, because after the tape the construction peaks at 450.2 MB and the certificate takes the cone to 511.4 MB, so `verify()` is now 13.6 % *above* the construction peak and **is** the binding item; and the input floor at `n = 256` is **0.80×**, not 0.85×. Slot-5 WP-4 additionally ungated the **first** `eq:conedims` identity from `H2_zero` (item code 11 kept, each identity under its own minimal guard; [OD] OI-2, Option A), value-preservingly. The next lever below ~1.7× is a `--lean`-style release of the bulk intermediates the cone does not read twice — a change to `EquivariantCohomologyOnK`'s retention contract, not attempted.
- **Cone Hecke action** (`Hecke/HeckeConeAction`; slot 3, WP-6 / phase E5-3 — [C] `def:coneaction`, `eq:derivedh`, `eq:conemap`, `lem:conesign`, `obl:eta`(v),(vi), `obl:coneexact`(i)–(iii),(vi),(viii)) — `h := η̃`, the **coset transport** of slot-2 WP-8's `η`-table (never chosen), in two bracketings asserted bit-identical; `Φ_g(c, c_∂) = (Θ_g c, Θ^∂_g c_∂ + h c)`; the `lem:conesign` residual computed in every degree and asserted zero **on the stored `C^q_eq` basis** — the flat identity is recorded, not claimed, because the coset transport uses `φ`'s Γ-equivariance (it holds flat in 29 of 424 degrees; a normative wording point for the next [C] `X`); `A_c^{(q)} = P_c Φ H_c`; `ConeActionCertificate` and `ConeRelationsCertificate` (the **full** `T_{p²} = T'_{p²} + p^n I`), both re-deriving; the record fragment `hecke_cone_action/v1` (standalone — not yet in `HeckeReport`, E2). Here in `Hecke/`, not `HeckeExt/`, because `check_heckeext_includes.sh` rule 2 forbids `Engine/` in the extension layer and rule 1 forbids the pipeline (which E2 consumes) from depending on it. **The vertex policies** that `obl:coneexact`(viii)(a) runs on, both value-preserving at their defaults: `EtaVertexPolicy` (`Hecke/HeckePairHomotopy`) and `TauBoundaryVertexPolicy` (`Hecke/HeckeBoundaryDatum`: `NearestLineVertex` = the canonical `alg:taubdry`, default; `NextLineVertex`, admissible by `lem:taubdryexists`(1) and non-tie), plus `table_fnv64()` on the τ, `τ_∂` and `η` tables and the recorded tie counter `num_vertex_ties()` (189 over the grid). **Cost, measured in slot 4 (WP-4)**: `ConeActionCertificate::verify()` is only ~9 % of the action's wall — **88 % of `HeckeConeAction::compute()` is the standard-basis sweep** `apply_Phi(q, e_b) == Φ_flat[:, b] == apply_Phi_direct(q, e_b)`, which is in `compute()` and **outside** the certificate (slot 3's attribution of the cost to `verify()` was wrong). The sweep's stored-matrix side is now evaluated one identity column block of width 64 at a time — one product per block, every basis vector still compared individually — and the matrix-free side shares one `ρ_n` memo per degree instead of rebuilding it per call: **122 → 75 s** at `n = 256` (−38 %) and 30.9 → 18.9 s at `n = 160`, RSS unchanged, `HeckeConeActionValidation` 11.9 → **10.0 s**, `A_c^{(q)}` bit-identical. **Slot 5**: WP-4 drops the `ℓ ∈ {2, 3}` carve-out and asserts `obl:coneexact`(iii)'s `r`-half at **every** `ell` ([OD] OI-3, Option A; [C] v1.7.0 writes in the proof that clause (i) implies it), value-preservingly — the two collector digests `0x4ecd2e429ec3b49` / `0xedbff302058416f3` and all 403 tamper item-set lines are byte-identical to a pre-package binary's. WP-6 replaces the per-call `ρ_n` memo with `Hecke/RhoMemo.h` (below): the `n = 256` build falls **74.5 → 42.6 s** for an added peak of 12 blocks ≈ 3.2 MB, entrywise identical. WP-12a adds `ConeActionCertificate` **item 12**, the record-honesty clause of [OD] 2026-09-22 Q2 — `hecke_cone_action/v1`'s `restriction_equivariance_asserted` must report the assertion item 8 actually performs, so it now reads `true` at `ℓ ∈ {2, 3}` too, and a certificate that says otherwise fails item 12 alone. **Since slot 6 `obl:coneexact`(vii) is implemented**: the strict-pair and route-3 cross-routes (WP-4, WP-5; next bullet but one) and PD adjointness (WP-3, E7b, `Hecke/HeckePairing`).
- **Contragredient and pairing** (`Hecke/HeckeContragredient`, `Hecke/HeckePairing`; slot 6, WP-1 /
  WP-3, phase E7 — [C] `sec:contragredient`, `lem:symdual`, `prop:pairing`, `cl:pd`) — `Mat22::adj`
  (`HeckeCore`), `FibreRepresentation {SymN, ContragredientN}` with
  `ComputeContragredientPowerMatrixFM = ρ_n(adj ·)^T` and the dispatcher `ComputeFibreMatrixFM`
  (`LocalSystemUtils`), `GenerateSL2ZContragredientRelationsWithGroupData` (`LocalSystemSL2Z`), an
  optional `FibreRepresentation` argument on `HeckeOperatorOnK` (default `SymN`: the pre-slot-6
  operator byte for byte — same tables, same calls, same program-cache keys; `ContragredientN`
  rebuilds the fused blocks from the exact coset / tau data and refuses a non-contragredient local
  system), `RhoMemoT::Identity` gaining `representation`; `Φ_n`, the coefficient pairing and
  `ContragredientCell`. `HeckePairing`: the relative fundamental 2-chain of the 7-vertex model (signs
  found combinatorially; `d[K] = −(horocycle)`), the Alexander–Whitney cup-product evaluation with
  the fibre Gram, the cone-level pairing `P_t((c, c_bd), y) = <c ∪ y, [K]> + <c_bd ∪ r y, d[K]>`, the
  circle pairing, `PairingCertificate` (perfectness recorded, never an item) and `PairingAdjoint`
  (the PD gate). Golden objects defined, not emitted. The cone is read-only to it.
- **Cone cross-routes** (`HeckeConeStrictPairRoute`, `HeckeConeRelativeRoute` in
  `Hecke/HeckeConeAction`; slot 6, WP-4 / WP-5 — [C] `prop:coneroutes`, `prop:strictpair`,
  `eq:route3`, `obl:coneexact`(vii)) — the strict pair: `TauVertexPolicy::BoundaryStrict` and the
  `HeckeTauTable` constructor taking the `τ_∂` table (boundary slots pre-assigned `j τ_∂`, fills over
  `Z` only — int64 then `__int128` through `solve_integer_system_wide` — never mod `ℓ`, its own
  `certify()` with strictness clause (g), codes 70–72), `η^s ≡ 0`, `Φ^s`, `A_c` compared entrywise;
  aborts at `6 ∈ R^×`, records at `ℓ ∈ {2, 3}`. Route 3: `EquivariantCohomologyOnK`'s relative
  sub-complex constructor (`(lssc, vanishing_simplices)`, one zero relation per forced simplex on a
  list only that object reads), `E = ext_0 h`, `Θ' = Θ + dE + Ed`, `A'` on `H(ker r)`, `M A' M^{-1}`
  vs `A_c`, aborting at every `ℓ`. Known minor finding (WP-4): `HeckeTauTable::to_string_offset`
  prints `GeometricNearestLegacy` as `"FixedV6"`. **Over `Z/ell^k` since slot-10 WP-3** (owner
  decision 3 (A)): both routes and the relative constructor honour the ring at `ell ≥ 5`,
  `ell^k < 2^32` (`CrossRouteRingGuard`: a normative `k ≥ 2` equal to `CoefficientRingK()`, then
  `CoefficientRingContext<uint32_t>` — above `2^32` the named uint32 regime refusal,
  `RequireRingRegime`); every other combination keeps slot 8's refusal. The strict route's
  `compute_composite()`: `τ^s`, `η^s` integral exactly as over `F_ell`; `Θ^s` = `HeckeOperatorOnK`'s
  module route; `Φ^s` = route 1 (`ModuleConeActionT`) with `η^s = 0`; `A_c` entrywise against the
  normative `ModuleConeActionT::A_c(q)` in the cone's one stored cyclic-summand basis; a validation
  seam constructor takes an external strict table (re-certified in `compute()`). Route 3's
  `compute_composite()`: `ext_0` from `ModuleConeT::r_flat`, `E = ext_0 h`, `Θ' = Θ + dE + Ed`, R3.1
  (`r ext_0 = I`, `ext_0 C_eq(K_bd) ⊂ C_eq(K)` by solves), R3.3 (`r Θ' = Θ^∂ r` on the nose), `ker r`
  by the relative constructor's **module route** (`C^q_rel` a summand of the free `C^q_eq`, so the
  free-Howell assertion holds), R3.5 **with no inverse over the ring** — `M: z ↦ [(z, 0)]` and the
  explicit `N: [(c, c_∂)] ↦ [c + d ext_0 c_∂]` (from `D_c(c, c_∂) = (−dc, d_∂c_∂ + rc)`), `M N = I`,
  `N M = I` in (c5) form and equal invariant factors — then `M A' N == A_c`; field accessors throw a
  named `logic_error` on a composite route. The relative constructor refuses by name at
  `ell ∈ {2, 3}`. `HeckeConeCrossRouteRingValidation` (`standard`, 431 with WP-8's m-12 asserts on
  route 3's non-vacuity). **(vii) sentences 1–2 are discharged over the ring; sentence 3** (the PD
  gate) **is recorded unavailable there** (`PoincareDualityPairing`, `ContragredientCell` refuse a
  composite ring).
- **`RhoMemo.h`** (slot 5, WP-6) — `hecke::RhoMemoT<Block>`, the one memo type behind the layer's matrix-free apply routines. It caches the pure function `(j, γ) ↦ ρ_n((δ_j γ) mod ell)` in a `std::map` (never `unordered_*`: a memo is a result path) and carries an `Identity` stamp `{owner, coset table, ell, n_sym, m}` — the part of the value's dependency set that is *not* in the key — which `bind()` `ENGINE_CHECK`s on every use, so a table handed to the wrong operator throws instead of returning a wrong block. `HeckeOperatorOnK::apply_route2`, `HeckeBoundaryOperator::apply_direct` and `HeckeConeAction::apply_h_direct` each take a caller-owned table; **the public one-argument overloads keep creating a fresh local one**, so every external caller, validations included, executes the pre-package path. `HeckeConeAction` holds **three** tables (`RhoMemos`), one per coset table, and `compute()`'s standard-basis sweep shares them per degree. `assemble_theta` / `assemble_h` deliberately keep **call-local** tables, because their `fused` flag makes `(j, γ)` key two different expressions — the one hazard the stamp does not cover, documented in the header. Value preservation is established three ways: structurally (the memo's output is never stored), empirically at 15.9 M entries against the cold path, and by a byte-diff of both cone validations' whole printed output.

- **Slot 8 (hecke-extensions) in the Hecke layer.** **`coefficient_ring`** (WP-3), the eleventh
  `MathSettings` key: `F_ell | Z/ell^<k>` (`2 ≤ k ≤ 63`), `Z` / `Z/<m>` refused inside `set()` by
  `NotImplementedInThisBuild` (*since slot-24 D6 only `Z/<m>`: `Z` is stored, `k = 0`, and honoured by the integral
  descent only; every other consumer refuses it by name through `CoefficientRingK(who)`, exit 5; [C] `def:ringsemantics`(3)*). The honouring context `CoefficientRingContext` refuses `ell ∈ {2, 3}`,
  `ell^k ≥ 2^64` and an `ell^k` that does not fit the element type. `EquivariantCohomologyOnK` reads
  the ring once, in its constructor; over `Z/ell^k` it takes the **module route** per degree
  (`C^q = kernel_module(A_Cq)` on a composite `BlockMat`, asserted free; `X_q` by
  `solve_multi_rhs_module`; `d∘d = 0` in coordinates; `Z^q = kernel_module(X_q)`; `H^q =
  cyclic_decomposition(Z^q, B^q)` in `C^q_eq` coordinates; `r_K(d^q)`; certified iff
  `r_K(d^0) = rank C^0` and `r_K(d^1) = rank C^2`, else a `ladic_level` state), and every field
  accessor throws a named `logic_error`. `HeckeOperatorOnK` follows the object's ring (a mismatch
  with the ring in force raises by name), builds `Θ` fused and by route 2 through the composite
  `ρ_n` (`ComputeSymmetricPowerMatrixRing`: the unit recurrences `[U_a]` / `[U_b]`, the `diag(ell, 1)`
  split `[S]`, the zero-first-row case `[Z]`, Pascal binomials by additions) and asserts them equal;
  `charpoly` only on the free quotient at a certified level, over `Z/ell^{K − e_max}`. **Every other
  construction site refuses by name** — one guard per member of [E] `sec:ring` (b1)'s closure plus
  the seven surfaces (`--bench` at `RunMode`'s entry, the campaign after parse, the console verbs,
  `--atlas`, `StreamHeckeReportJson`, …); `refusal_arm()` tests 36 members. **`HeckeReduction`**
  (WP-4): the reductions `red_H^q` and the Bockstein `β^q` as maps between stored bases,
  `BocksteinCounts` (`bockstein_rank^0`, `higher_torsion_count`), Hecke-equivariance certificates
  at `ell ≥ 5`. **Route 2's key rank** (WP-L1, owner-approved): a Fenwick tree over the slot range
  `[0, |rho2|)`, allocated once per degree and cleared by undoing the row's own insertions, gives
  `rank(slot)` in `O(log |rho2|)`; the same integer reaches the same `fnv_mix` in the same order,
  so every `hecke.route2` `ShapeKey` is bit-identical; `U_10007` at `n = 0` ≈ 256 s → ≈ 9 s.
  **`PredicateStats`** is per thread (WP-6).

**Hecke-extensions slot 9.** *`ell ∈ {2, 3}` under a composite ring* (WP-3, owner decision 4 (A),
superseding S8-D2): `CoefficientRingContext` takes a policy `SmallEllPolicy {Refuse (default),
Bredon}` and `IsBredonPrime(ell)`; only `EquivariantCohomologyOnK::init_coefficient_ring()` passes
`Bredon`, every other caller keeps slot 8's refusal (a global flip would let any later caller hold a
context at 2, 3 silently). The object records `flat_route_` and `compute_cohomology()` dispatches to
`compute_cohomology_flat_module()` — the only edit on the `ell ≥ 5` path is that dispatch line. In
flat cochain coordinates: `C^q = kernel_module(A_Cq)` (Howell generators, not a basis — `C^q_eq` is
not free at 2 and 3), `Z^q = kernel_module([A_Cq ; d^q])`, `B^q = d^{q−1}·C^{q−1}`, `H^q =
invariant_factors(ctx, Z^q, B^q)`, with three re-derived certificates (`B ⊆ Z` entrywise, `Σ e_i =
length Z − length B`, rank–nullity of `d^q` in lengths), stored as `FlatModuleDegree`. Honouring
accessors: `num_degrees`, `H_lengths`, `H_invariant_factors`, `ring_context`, `flat_module_degree`,
`is_flat_route`; refusing by name: the four stored-basis accessors and the six `K`-mode accessors
(`prop:certifiede`(5)); `HeckeOperatorOnK` refuses at 2 and 3 (`init_composite()`), `HeckeReduction`
through the accessors and an explicit `IsBredonPrime` guard on its 4b entry points. This is the
Bredon object ([C] `prop:bredon`(2)), not group cohomology ([C] `prop:bredon`(3)); its oracle O7 is
the tree model over `Z/ell^k` computed **over `Z`** by the probe (`integral_line_probe.py --model-R`,
preimage lattices and the probe's own Smith form — nothing shared with the C++), frozen in
`HeckeBredonTreeRingValidation` (133 cells, 96 compared). Arm (X) of `HeckeReductionValidation` 36 →
66 members (two rows flipped to honouring). *E8 item 4b* (WP-4, owner decision 3 (A) with (iii) (A)):
`ModuleConeT<Elt>` (`EquivariantMappingConeModule.cpp`) — the cone over `Z/ell^k` on ENGINE_API
§13.6 only, templated over u32 / `U64_Montgomery` / `U64_Wide`; `Cc^q_eq` = the two Howell bases
concatenated, bulk first, asserted once per degree to be the block sum's Howell form; `X_q` by
`solve_multi_rhs_module`; `H^q_c` by (c2)–(c4); the eight `eq:coneles` maps as (c5) matrices;
`ConeModuleCertificate` keeps the E5 numbering where a ring reading exists and appends **item 14**,
`obl:coneexact`(iv)'s non-field half (every composite zero by a solve, every Howell generator of
`ker(out)` exhibited as `in(w1) + D_M w2`, witnesses stored and re-derived by `verify()`).
`EquivariantMappingCone` has a composite branch (field accessors throw a named `logic_error`);
`SL2ZBoundaryPair` builds the circle model over the ring (`GenerateSL2ZBoundaryRelationsRing`);
`EquivariantCochainComplexMorphismOnK`'s constant-fibre constructor honours a shared ring (a
mismatch is a `logic_error`; the `FiberBlockTable` constructor keeps refusing);
`HeckeBoundaryOperatorT<Elt>` builds `Θ^∂` over the ring in both bracketings; `ModuleConeActionT<Elt>`
is **route 1 only** (`h` both ways, `Φ`, `A_c` on the cyclic summands, items 2, 4–9 exactly; the
`[A_c(T_p), A_c(T_p')] = 0` commutator asserted in arm (4b-H) — the `ν = 2` recursion is not computed
over the ring); the strict-pair and relative routes and the relative sub-complex constructor keep
refusing, now also a composite normative action (`obl:coneexact`(vii)'s composite half open);
`cochain_commutes` became reachable and refuses by name. `HeckeReduction` gained
`ReduceConeHcToField`, `ReduceConeHcBetweenLevels`, `BocksteinConeHc` (β¹_c, validated, not an object)
and `ReductionIntertwines`. The four classes stay `uint32_t`-instantiated (they honour
`ell^k < 2^32`); the templated route runs the `U64_*` regime cells end to end. The `F_ell` cone is
byte-identical (`cone_output_diff.sh` against `bd6d1bb`). R1 made 18 objects per E8 point golden
(126 entries). **E8 is declared complete as specified: 4b by route 1; (vii) over the ring open.**
Checks: `HeckeReduction(Cone)Validation`'s arms (4b-B/C/H/R/K), (X4b); since WP-4t (owner-approved
2026-09-25) `(60, 5)` at `k = 2, 3` runs in `HeckeReductionCoverageSlowValidation` and the implied
rows are dropped (4b arms 458 → 306, 5.7 s → 0.95 s). *Carries* (WP-9): `get_prime()` refuses a
composite object (`ENGINE_CHECK`; the one live composite caller, the constant-fibre constructor,
re-pointed to `ring_context().p`); `RunPipelineModEll (Integral)` opens with
`RequireFieldCoefficientRing`. *Lever L2* (WP-7): `HeckeOperatorFamily::build_pipelines()` holds
`tau_construction_mutex()` only while priming K's simplex index (ell-independent, built once,
read-only afterwards); the constructions run outside it, serially, in key order (audit hazards 1–2
are intra-construction, hazard 3 has been thread-local since slot-8 WP-6);
`HeckeFamilyConcurrentBuildValidation` (`fast`).

- **Slot 10 (hecke-extensions) in the Hecke layer.** *Lever L4* (WP-7, owner decision 11 (A)):
  `HeckeOperatorOnK`'s route 2 runs its block rows as host tasks on the consumer pool — per-row start
  offsets into `term_slot` (counted in the same σ-ordered walk and prefix-summed), one task per row
  with its own `Executor` and its own Fenwick tree (a fresh tree is the state the per-degree tree was
  reset to between rows, so every rank, pattern hash, `ShapeKey` and program is the serial loop's),
  the first failing row's exception in σ order; `rho2`'s non-scalar entries materialised before the
  fan-out and the failure path's `block_index[...]` made `.at(...)`. `U_10007` `n = 0` route 2 1.26 →
  0.25 s; T2's `(10, 691)` ≈ −24 %; neutral on the parallel ext pass. The cross-routes over the ring
  (WP-3) are in the cone cross-routes bullet above.

### Hecke extensions layer — unit by unit (`src/hacs/HeckeExt/`)

The full bullet list of `CLAUDE.md`'s "Hecke extensions layer" section. `CLAUDE.md` keeps the
one-paragraph summary, the one-way dependency rule and the "two families of switches" rule.

- **`HeckeSturmBound`** — the computed Sturm bound `B'(k, ell)` of [E] `def:bprime` / `cl:bprime`,
  **pipeline-free** (only `SubspaceOps`, `FpPoly`, `Matrix`, `ModArithmetic`, `EngineCheck`,
  `Fnv`): `q`-expansions mod `ell` on the Miller basis, the algebra closure, the certificate with
  `verify()`, and the first implementation of the **resumable-state contract** [X] §1.3.1 (R3):
  `state()`, `resume(cap)` (refuses a lower cap; a no-op on a complete state), `budget_history`,
  the `"resumable"` JSON object with an inline-or-sidecar state hashed by `Fnv.h`.
- **`HeckeIdentityCertificate`** — the slot-1 subset of [X] §1.3's identity certificate
  (Eichler–Shimura in the `dim H^0`-robust form, commutativity, `d_2 = 0`, the `p^2` recursion
  against the independent double-coset route).
- **`HeckeLocalAlgebra`** (slot 2, WP-4, E1a) — the local algebra `A_S` of a certified-local block
  with every invariant of [E] `alg:stage3` (`ŵ`, the `P_p`, the `n_p`, `m_S` and its powers, `ν`,
  `soc A_S`, Gorenstein, the Hilbert function, the `K`-tangent table, `embdim`), **generation
  certificate (a)** with a re-deriving `verify()`, and `SameMaximalIdeal`, Stage 2's cross-block
  evaluation test. It has no resumable state: the budgeted item in E1a is the commutant.
- **`HeckeGenerationCertificates`** (slot 2, WP-5, E1a-2) — generation certificate (b): the socle
  bound as an attempt gate and a proof of failure, the structured commutant on the rational
  canonical form of a cyclic-most element of `A_S`, the naive oracle, the budgeted resumable
  `CommutantState` (R3 instance 3; `kCommutantBudget = 2·10^10`, a named constant, not a setting)
  and the route-combining `generation_verdict` of R3.2 — the tri-state `final` in the default
  configuration, with OQ8's "emit, never withhold". Its `verify()` re-derives `dim C` and does
  **not** pin the RCF basis.
- **`HeckeBoundary`** (slot 2, WP-7, E4b) — the ext-layer consumer of `Hecke/HeckeBoundaryDatum` +
  `HeckeBoundaryOperator`: `H^1_! = ker r^1` with its Hecke action, the joint eigenspace /
  Eisenstein line, Harder's criterion from a pinned `num(B_k/k)` table (`k ≤ 26`; `bernoulli_mod`
  is E6's), the Harder split, the copyable `HeckeBoundaryCertificate`, golden collectors (never
  emitted) and `to_json()` (`hecke_boundary_parabolic/v1`, the per-complex degree fields). Since
  slot-3 WP-5 it takes the restriction from `Hecke/SL2ZBoundaryPair` (value-preserving).
- **`HeckeSturmSweep`** (slot 3, WP-2, E1b) — generation certificate (c) of [E] `cert:sturm` on
  real blocks: `T_q|_V` for every prime `q ≤ B'(k, ell)`, membership in `A_S` by one reduction
  against `RrefRowSpan` (on the proof range of [E] `cl:sturmmodl` a **proof** that `A_S = T_m`, off
  it recorded as a heuristic); the operators come from a `SturmOperatorSource`
  (`BlockRestrictionSource` over a supplier, `FamilyOperatorSupplier` backed by a
  `HeckeOperatorFamily`), so reuse-before-streaming is the caller's decision and a refused `U_ell`
  becomes `false`, never a `1.3·10^8`-coset run; both `sturm_unavailable` modes with the R3
  resume; `generation_verdict_with_sweep` beside the unchanged default-configuration
  `generation_verdict` (only the user-selected `heuristic` mode reaches the tri-state value);
  Stage 1's `S_0 = {2, 3, 5, 7} ∪ {ell iff UEllDecision admits it}`. Not shipped: the streaming
  route for `q ∉ S_0` (E2's `HeckeExtDriver`; `B' ∈ {2, 3, 5, 7}` on every cell measured) and a
  swept `S_sep(ell)` (E6's atlas).
- **`HeckeUEllBudget.h`** (slot 3, WP-1, E1b-0) — header-only, pure, allocation-free: the frozen
  RSS model, `PredictUEllRssMb`, `UEllDecision` / `UEllVerdict` (`included`, `reason ∈
  {within_budget, u_ell_over_budget, off}`, `predicted_mb`, `budget_mb`, `model_version`; no
  `resumable`, which is E2's), `MaxAdmittedN`; `off` short-circuits without forming a prediction.
- **`HeckeExtRecord.h` + `HeckeExtReport`** (slot 4, WP-1, E2a; **`hecke_ext/v2` since slot-5
  WP-1**; **`hecke_ext/v3` since slot-7 stage 3**, below) — the extension record of [E] §7: a **separate writer** from `Hecke/HeckeReport`'s
  `hecke_report/v2`,
  which slot 4 does not touch at all (`git diff 9ae1d7a -- Hecke/HeckeReport.{h,cpp}` empty — a
  stronger proxy than the golden gate, and the reason no shared helper had to be extracted). It
  carries the record's `settings` block (`MathSettings::to_json()`, source and fingerprint), the
  per-complex degree fields of [C] `sec:recordschema` item 5, the per-ideal objects, and the
  R3.1 item-6 **sidecar** for an oversize resumable state (relative path + FNV-1a-64; a
  `.<i>` disambiguator where [X]'s literal name is not injective, one `commutant` state per ideal).
  **Slot-5 WP-1 bumped the schema to `hecke_ext/v2`** ([OD] slot-4 close-out 5, the `u_ell`
  per-ideal → per-cell repair, made *before* the stage's first emission): the `u_ell` verdict is
  the **cell's**, with a single `resumable` where v1 emitted one per ideal (`resumable_items()`
  counts a refused `U_ℓ` once on a four-ideal cell); an ideal carries its `sign` and a `groups`
  list naming the ambient groups Stage 2 matched it across; the `boundary`, `pair` and cone complex
  objects are **computed**, each with its own `q_max` / `truncated` / `q_max_source` / `degrees`
  and `les_maps` per reported spot, where v1 wrote `{"status": "unavailable"}`; the per-sign (E3)
  objects carry `iota_sign`; and the two cone keys `phi_flat_identity` / `residual_flat_zero`,
  RESERVED in v1, are **emitted**. The two schemas are distinguishable by their `schema` key alone.
  **Slot-5 WP-11a** added `verify()` **code 22** — a `q_max_source = "set"` on a *derived*
  complex is refused ([C] `sec:recordschema` item 5). **Slot-5 WP-12a** added the record-level key
  `iota_exact_comparison` ([OD] 2026-09-22 Q3), the record's half of [C] `obl:iota`(ii)'s rider
  (`ran` / `relation_rows` / `rows_with_exact` / `rows_compared`), with `verify()` **code 23**.
  `Hecke/HeckeReport.{h,cpp}` is still untouched by the whole extension stage.
- **`HeckeExtComplexRecords`** (slot 5, WP-1, E2 *cont.*) — the one translation layer between
  the E3 / E4b / E5 objects (`HeckeSignSplit`, `HeckeExt/HeckeBoundary`,
  `EquivariantMappingCone`, `HeckeConeAction`) and the record's complex objects. The driver's two
  new options that turn the `boundary` and `pair` attachments on are **OFF by default**.
- **`HeckeExtGoldenObject.h`** (slot 5, WP-3) — the one definition of the layer's
  golden-collector POD. `HeckeBoundary.h` (slot 2) and `HeckeSignSplit.h` (slot 4) each defined
  `hecke_ext::GoldenObject` identically; that is legal only while no TU includes both, and
  `Golden/GoldenHarness.cpp` is the first that calls both collector families. Moved verbatim,
  value-preservingly.
- **`HeckeDicksonMultiplication`** (slot 5, WP-8, E1 identity class 5 — the inventory gap
  [I G12] / [XA m10]) — multiplication by the Dickson invariant `L = x^ell y − x y^ell`,
  `Sym^{n−ell−1} → Sym^n`, an `(n+1) × (n−ell)` matrix with entries in `{0, ±1}`, and the
  certificate that re-derives its entries by an independent convolution and the det-twisted
  intertwining `ρ_n(A) L = det(A) L ρ_m(A)` entrywise on seeded `A`; **typed `FlatMatrix` because
  it is a fibre-level object consumed by the cochain layer**, so it needs no `Matrix.h`
  allow-list entry.
- **`HeckeM1Table`** (slot 5, WP-8) — the one definition of an M1 row and of a well-formed one,
  shared by the three case validations.
- **`HeckeExtFinal.h`** (slot 4, WP-1) — the **one** tri-state `hecke_ext::Final` with its fixed
  reason list, to which `SturmFinal` / `SturmFinality` are now aliases; `is_final` is a pure
  function of `final_mode × sturm_unavailable × {proof range, heuristic range, none}`, and the
  **default configuration never produces `"heuristic"`**.
- **`HeckeExtDriver`** (slot 4, WP-2, E2b) — one cell, one triangulation, **one** cohomology and
  **one** `HeckeOperatorFamily` through [X] §2.2 Stages 1–5 into the record, with a phase split
  (`setup_s`, `stage1_s`, …) that is exactly what [X] §6.2 E1 (d) is a statement about. Stage 3
  **consumes** the decomposition's certified `PrimaryBlock` locality data
  (`LocalAlgebraOptions::precomputed_locality`; `ŵ` rebuilt by `hecke::FrobeniusPower`, the one
  field a `PrimaryBlock` does not store) instead of re-running `CertifyLocality` — −19.5 % of
  `ext_s` at `n = 256`, every check after Step 0 still running. A Sturm prime outside `S_0` is
  **streamed** (`StreamedOperatorSupplier` / `ReuseBeforeStreamingSupplier` in `HeckeSturmSweep`):
  coset → τ → Θ built in a local scope under the τ-construction mutex and
  `ScopedThetaEqCertification(false)` + `ScopedMemoryLean(true)`, the `d_q × d_q` result memoised
  per `(degree, q)` and the pipeline destroyed, so the family's never-evicting cache holds only
  `S_0`. The **`u_ell` resume** (R3.3 item 4) lives here.
- **`HeckeSignSplit`** (slot 4, WP-3, E3) — the ext-layer consumer of `Hecke/HeckeInvolution`:
  `[ι^*, A^{(q)}] = 0`, `A^{(q)}_±` by an exact solve, the per-sign decomposition with cyclicity
  through slot-2 WP-4's certificate (a), and the Eisenstein line `soc(X^+_{4,m})` of [E] D6.
  `check_matrix_includes.sh`'s `Matrix.h` list gains `HeckeExt/HeckeSignSplit.h`.
- **`HeckePredictions`** (slot 4, WP-7, E6) — Bernoulli numbers mod `ℓ` (`bernoulli_mod`, the
  `F_ℓ` recursion, valid for `w < ℓ − 1` by von Staudt–Clausen, with the named
  `BernoulliOutOfRange` outside it) and the Kummer / Harder divisibility predicate
  (`kummer_divides`, total on even `k ≥ 2` by three provable branches); pipeline-free (only
  `engine::ModCtx` and `EngineCheck.h`).
- **`GloverFactors`** (slot 4, WP-7, E6) — the Glover / Ash–Stevens composition factors of
  `Sym^n(F_ℓ^2)` over `F_ℓ[GL_2(F_ℓ)]` with multiplicities, by the θ-multiplication recursion, in
  the pipeline's own `ρ_n` convention; pure integer combinatorics, **no modular arithmetic at
  all**, so it consumes nothing but `EngineCheck.h` and the STL.
- **`RegisterHeckeExtensionVerbs`** (slot 4, WP-5, console C1b) — the extension layer's **own**
  console registration TU (`sturm_bound(k, ell)` over the real `SturmState`,
  `u_ell_decision(n, ell)`), called from `main.cpp`'s existing console branch. It is the single
  place the layer includes `Console/`, admitted by one exact-path entry in each of the two guards'
  rule 2 ([OD] slot-3 close-out 1 / slot-4 confirmation 4); its header forward-declares
  `console::Registry` and includes no `Console/` header. (S24 CL-8, CODEAUDIT A10: the TU is split by
  area into `RegisterHeckeExtensionVerbs.cpp` — entry points, `RegisterC5`, the C5 helpers — and six siblings
  `RegisterHeckeExtensionVerbs{Sturm,Algebra,Records,Values,Complex,Gallery}.cpp` sharing the private
  `RegisterHeckeExtensionVerbsDetail.h`; each of the eight files is one exact-path guard entry; the registration
  order is unchanged.)
- **`HeckeCanonicalField`** (slot 5, WP-7, E6 — [X] §2.2 Stage 6; [E] `def:canon`, `cl:canon`,
  `alg:split`; [OD] OQ9 / OQ10; planned as slot-4 WP-10, which did not run) — the
  **project-canonical split field**. A block reports its residue data in its *own* field
  `F_ℓ[X]/(π_w)`, which is free but names a different field per block; Stage 6 re-embeds all of
  them into one field per `(ℓ, r)`, `F = F_ℓ[Y]/(C_{ℓ,r})` with `C_{ℓ,r}` the
  `CanonicalLess`-least monic irreducible of degree `r`, so eigenvalues become comparable across
  blocks and across runs. Two order facts are load-bearing: `hecke::CanonicalLess` compares the
  **constant** coefficient first, so the candidate odometer's *rightmost* digit turns fastest
  (`C_{2,3} = Y³ + Y² + 1`, not `Y³ + Y + 1`), with the one sound prune `c_0 = 0 ∧ r ≥ 2 ⇒ Y | f`
  — without it `(2, 30)` would have to reject `2²⁹` candidates one at a time; and in `alg:split`
  step 1 the fixed candidate sequence (the elements of `F` in `CanonicalLess` order) **starts at
  `Y`**, because no `s ∈ F_ℓ` can ever split `π_w` — the roots are one Frobenius orbit, `x ↦ x + s`
  commutes with Frobenius for `s ∈ F_ℓ`, and both two-valued invariants the splitting polynomial
  uses (the quadratic character for odd `ℓ`, the absolute trace for `ℓ = 2`) are
  Frobenius-invariant. Ships `FqPoly` (univariate polynomials over `F`, the only new arithmetic
  Stage 6 needs), the split record `hecke_canonical_split/v1` with a re-deriving nine-clause
  certificate that **re-enumerates** `C_{ℓ,r}` rather than trusting it, and the own-field
  rendering of [E] `sec:field` tier (i) (the slot-6 close repointed this from `sec:reportfield`, a
  label that never existed in [E]). Pipeline-free (`Hecke/FpPoly`,
  `Hecke/HeckeSettings`, `ModCtx.h`, `EngineCheck.h`). **No report consumer in this slot** —
  nothing on any pipeline path calls it and no record gains a key; the integration is E6's, in
  slot 6. `--bench ext` carries the measurement of E6's performance gate
  (`canonical_field_s=` / `own_field_s=` / `canonical_field_r_max=`), **reported and never acted
  on**. Since slot-6 WP-7 it also prints `[E6 gate] canonical_field_s/total_s = … (gate: <= 0.10)`
  and the BENCH line carries `canonical_field_total_ratio=` — the restated gate of [X] v1.10
  §6.2 E6 (d). **The first consumer is the atlas (slot 6)**, not the record. Open (slot-6 WP-13
  finding 1): `CanonicalField(ell, r)` and `SplitInCanonicalField` call `CanonicalFieldPolynomial`
  directly and so bypass `FieldPolynomialFromSettings`, which is where `conway` is refused.
- **`HeckePresentation`** (slot 6, WP-2, E2 (a), OQ11) — generators (the least-index Nakayama
  lift, in the block's own basis) and a minimal set of relations of a certified-local block over
  `T_m`, relations as `t`-tuples over the stored RREF basis of `A_S`, counted over the residue
  field (`dim_F(ker / m_S ker) / f`), with an eight-clause re-deriving `verify()`;
  `hecke_presentation/v1` JSON that is **not** a record key. Reached only through
  `ExtDriverOptions::with_presentation` (default off). The `presentation` settings key, the record
  object and the hash-invariance arm are booked for slot 7's re-baseline (registering a key now
  moves 62 golden lines).
- **`HeckeAtlas`** (slot 6, WP-8 / WP-9, E6) — `BuildAtlas(ell)`: `HeckeExtDriver` on every even
  `n ≤ ell − 1` with the anemic pool `{q ≤ 31} \ {ell}`; every certified-local ideal in its
  canonical split form through **one** `CanonicalField` per `(ell, r)`; systems keyed by the least
  Frobenius conjugate of the anemic eigenvalue vector (identification across `n`); `a_ell` per
  occurrence where the `u_ell` verdict admitted `U_ell`, else `unknown` with the reason; the
  `θ`-twist closure `Σ(ell)`; the greedy `S_sep(ell)` separating `Σ(ell) ∪ {χ_{a,b}}` as Galois
  orbits (an undecidable cross-degree pair counted unseparated). The store `hecke_atlas/v1` is
  byte-deterministic, has its own reader, and is written only under `HECKE_ATLAS_OUT=<dir>`,
  refused under `docs/matrix-engine/results/`. WP-9 adds `AtlasIdealCharacters` /
  `AtlasResidueMultisets` (the inputs of identity 6). Nothing enters `hecke_ext/v2` or golden.
  At `ell ≤ 13` every system is `F_ell`-rational, so the atlas's own cells never reach `r ≥ 2`.
- **`HeckeIdentityCertificate` items 6 and 7** (slot 6) — item 6 (WP-9, code 6, the residue
  atlas): `[H^1(M_n)] = Σ θ^{j_i}[H^1(M_{n_i})]` plus the `H^0` / `H^2` corrections over
  `cl:glover`'s factors by the certificate's own Glover recursion, under the standard-module
  convention; `GloverConvention::kContragredient` is the negative control. Item 7 (WP-3, socle ↔
  Loewy, `cl:pd`(3)): `rad^i(W) = (soc^i V)^⊥` with both series computed independently. The
  failing-code order is 1–7.
- **`ExtDriverOptions::s_sep`** (slot 6, WP-9) — Stage 2(3) as an opt-in: non-empty means Stage 1
  runs on `S_0 ∪ S_sep`. Default empty; not a settings key; not reachable from the campaign or the
  console. **Since slot-7 WP-3 item 4 it is `std::optional`**: unset = the in-process atlas's
  `S_sep` where one is built, set = the caller's override.
- **The record at slot 7: `hecke_ext/v3`** (WP-2, WP-3; [E] v1.8.0 `sec:schema`, "The stage-2
  keys"). `HeckeExtDriver` now decides `proof_range` **at the cell** unless the caller sets
  `ExtDriverOptions::proof_range` (`std::optional<bool>`): `V ⊕ H^0` is decomposed jointly over
  `AnemicPool(ell) = {q ≤ 31} \ {ell}` and a primary component meeting both summands is a shared
  (Dickson-type) system; the decided value is fed to the Sturm sweep (source `cell_local` /
  `caller_input` / `method_undefined`; record-level `anemic_pool`). At `ell ∈ {5, 7, 11, 13}`
  `InProcessAtlas(ell)` / `InProcessAtlasSSep(ell)` build `Σ(ell)` once per `(ell, fingerprint)`,
  mutex-guarded, never reading a stored atlas; the record's `s_sep` and each ideal's `label` come
  from it (`atlas_unavailable` at every other `ell`, owner ruling 3b (B)); `consult_atlas = false`
  in the atlas's own cell runs prevents recursion. Every local ideal carries the
  `hecke_canonical_split/v1` fragment as `split` under `split_field_report = canonical`, computed
  inside `run()` through one `CanonicalField` per `(ell, r)` and timed as
  `ExtDriverTimings::canonical_field_s` (`--bench ext` reads it rather than recomputing the split,
  and prints `total_s − canonical_field_s`). `predictions_mode` and `predictions` (the Kummer
  verdicts, `hecke_glover_factors/v1`) sit beside `settings`; each `H^1` ideal carries `predicted` /
  `confirmed` / `unpredicted` by `pr:eiscusp`, and `predictions = assert` throws on a refuted
  prediction. Under `presentation = on` every ideal carries the `presentation` object. `verify()`
  codes 24–29. The anemic-pool operator builds are counted in `pool_streamed()`, not `streamed()`.
  The **default-path cost** at `ell ≤ 13` is the anemic pool (7–8 streamed `T_q`): ext cells
  ≈ 0.12 s against ≈ 0.015 s, the golden run ≈ 5.7 → ≈ 12–18 s; nothing of it is paid at
  `ell ≥ 691`.
- **`HeckeCanonicalField`'s root finder at slot 7** (WP-4) — `FindCanonicalRoot` keeps [E]
  `alg:split`'s fixed candidate sequence and every gcd outcome and changes only how the splitting
  polynomial `(X + s)^{1 + ell + … + ell^{r−1}}` is evaluated: `u ↦ u^ell` in `A = F[X]/(f)` as a
  precomputed `F_ell`-linear map (the Frobenius of `F` as an `r × r` matrix, `X^{i·ell} mod f`
  once per `f`), a flat allocation-free quotient-ring product with delayed `uint64` accumulation
  (`ModCtx::k_max`), and the root's Frobenius orbit through the same matrix. `F_ell`
  multiplications at `r = 19`: 144.1 M → 12.1 M (`ell = 691`); every value exact, so
  `candidates_used` and all 629 `hecke_canonical_split/v1` texts measured are byte-identical.
  `CanonicalFieldOpCounts` / `ScopedCanonicalFieldOpCounter` count the operations (thread-local).
  `CanonicalField(ell, r)` and `CertifyCanonicalSplit` clause 3 now take the polynomial from
  `FieldPolynomialFromSettings`, so `conway` is refused from every production entry point (the
  slot-6 open finding, closed).
- **`HeckeAtlas` at `ell = 691`, `HeckeAtlasCli`, `HeckeTangentPair`** (slot 7, WP-5) —
  `BuildAtlas = CollectAtlas + CloseAtlas`, rewritten to scale (`θ`-twists as scaled conjugates, a
  `(r, key)` index, `AtlasSeparationBy` by group counting) with the **same** output — the four
  `ell ≤ 13` stores byte-identical; `CloseAtlas(ParseAtlasStore(json))` re-closes a store byte for
  byte. `Σ(691)`: 1 002 225 systems from 1626 collected, `S_sep(691) = {5, 17, 29}`, 451 875 793
  bytes, FNV `0x73c7210047a81b97`, byte-identical across two builds (≈ 2.6–3.2 h and ≤ 19.5 GB
  peak, indicative). Built **outside the suite** by `hacs --atlas <ell> [--n-max N]
  [--collect-only]` / `--atlas --close` / `--atlas --verify` (`HeckeAtlasCli`, dispatched from
  `main.cpp`), driven by `docs/matrix-engine/tools/atlas_build.sh` under a `git status` guard.
  `HeckeTangentPair` (`hecke_tangent_pair/v1`, printed only): for each cuspidal system, `dim_K m/m²`
  and a greedy generating set of anemic operators at `n = w − 2 + ell² − 1`, with `u_ell = off` and
  `consult_atlas = false`; deferred beyond `n = 1000` (all of `ell = 691`).
  `docs/matrix-engine/tools/ext_compare.py` writes a campaign's `analysis.txt` ([1]–[8] of E6 (c)).
  **Slot 9** (WP-13, C5b): `HeckeAlgebraInvariants` (console-free; the invariants of any commuting
  family over `F_ell` without a locality certificate — reuses `Hecke/SubspaceOps`' strict-locality
  primitives, no search, no randomness) and `HeckeExtBindingSupport` (console-free; the pipeline
  plumbing the bindings need, each composed in an existing validation's order); `HeckeExtDriver` and
  the record stay `F_ell`-only (the ext pass refuses a ring). WP-7's profile: at `(160, 691)` the cone
  (1.49 s) and the ι split (1.77 s) are 89 % of the cell and no slot-9 lever reaches them (slot 10).
  **Resolved in slot 8** (WP-5): the engine's process-wide program cache was unbounded, so the
  atlas build's RSS grew ≈ 16 GB across cells and a campaign's ext pass never released RSS; the
  `--atlas` build and the ext pass now release it between cells (`docs/KNOWN_ISSUES.md` §4c).

**Slot 11** added three units (all `cohomology_app` sources through `cmake/slot11/WP<n>.cmake`, all
`F_ell`-only):
- **`HeckeDicksonTheta`** (WP-5; [C] `sec:dicksontheta`, [E] `sec:thetaobj`) — `hecke_ext::DicksonThetaCell(n, ell)`:
  the three computed `EquivariantCohomologyOnK` objects of `Sym^n ⊗ det → Sym^{n+ell+1} → Q_n`, the
  five maps `ι = θ`, `π`, `δ` in the stored bases (column convention of `A^{(q)}`), `δ` by the snake
  construction (an exact solve for the lift, exact back-substitution for the division by `L·`, both
  re-multiplied), `hecke_triple(p)` (the operators on the three terms; `Sym^n` and `Q_n` share the coset /
  τ tables at `n`). `DicksonThetaCertificate` (code 0 = all held): the fibre level (`L·`'s own
  certificate, `π L· = 0`, `π E = I`, `ρ_Q(g) π = π ρ_m(g)` on fixed, seeded, `U_ell`-coset and relation
  samples), the pipeline projectors, the cochain level, exactness at the six spots (ranks, bases of
  `im` and `ker`, both inclusions), `H^2 = 0` on the three terms, the alternating sum, and `H^0` spanned by
  the classes of `L^a D^b`. Refusals: **`ell < 5` by `ENGINE_CHECK_MSG` naming `lem:h2torsion`** (a
  `std::logic_error`, console exit 3 — the mathematical precondition [E] (h) specifies; through the
  slot-11 WP-15 tree it threw `NotImplementedInThisBuild`, changed at WP-17 on the referee's ruling), and a
  non-default ring by name. Negative seams (N1) `x^ell y · Sym^n` fails well-definedness, (N2) a perturbed
  `δ` fails exactness. `HeckeDicksonThetaValidation` (979), `HeckeDicksonThetaCoverageSlowValidation`
  (`slow`, 3590).
- **`HeckeDicksonThetaHecke`** (WP-6) — θ's Hecke module structure: (T) the coset / τ tables built at `n`
  and at `n + ell + 1` identical slot by slot ([C] `lem:heckefibre`: the datum is not keyed on `n`); (F)
  [C] `prop:thetatwist`'s cochain identities for the shipped operators; (E) / (U) `A_m(p) θ = p θ A_n(p)`
  (the untwisted identity asserted to fail), `π A_m = A_Q π`, `δ A_Q = p A_n δ`, and at `p = ell` `U θ = 0`;
  (C2) `H^0` as [C] `prop:heckeH0`, the `(120, 5)` exception entrywise; `ker θ = im δ` the Eisenstein
  line; the multiplicity inequality blockwise; (C3)–(C9) against `Σ(ell)`; θ-cycles; and, under
  `HECKE_THETA_IMAGE_ALL=1`, the census θ-image column (`THETA_IMAGE` lines; the block's own
  `witness_poly` in place of the driver's local-algebra witness, exact under the shipped
  `consume_block_locality = true`). `HeckeDicksonThetaHeckeValidation` (5482; 34 337 under the
  interlock), `HeckeDicksonThetaHeckeCoverageSlowValidation` (`slow`, 3836).
- **`HeckeCensusSplit`** (WP-7; [E] `sec:census`) — per `H^1` ideal of a census cell: re-runs the shipped
  `HeckeExtDriver` with the published campaign's attachments (routes (b), (c) off: they act after Stage 2
  and change no ideal), asserts block by block that the re-run block **is** the record ideal
  (`witness_poly` and every restricted `t_p`), and computes `rank(r^1 | E_m)` with the driver's own
  `SL2ZBoundaryPair` restriction (→ `eisenstein` / `cuspidal` / `mixed`), `dim(E_m ∩ H^1_±)` with the
  production `ι^*`, and the Glover reconciliation through `HeckeIdentityCertificate`'s item-6 evaluation;
  per-cell invariants (`Σ dim_E = dim H^1`, `Σ rank_r1 = rank r^1`, `Σ dim_± = dim H^1_±`, identity 6).
  One `CENSUS_SPLIT` line per ideal, with `t_p=<fnv64>` of the restricted operators (so the tool's
  matching is exact without printing matrices). The tool `docs/matrix-engine/tools/congruence_census.py`
  (read-only; writes only the edition directory it is given, refuses an existing one; a dataset mode
  since WP-8) builds `results/congruence_census/`. `HeckeCensusSplitValidation` (117; 5643 under
  `HECKE_CENSUS_SPLIT_ALL=1`, ≈ 9.6 GB peak).

### Hecke action — the slot-11 additions

- **`FibreRepresentation::QuotientL`** (slot-11 WP-5; `LocalSystemUtils`, `LocalSystemSL2Z`,
  `Hecke/HeckeOperatorOnK`, all append-only): `ρ_{Q_n}(A) = π ρ_{n+ell+1}(A) E` for **every** 2×2 `A` over
  `F_ell`, singular included, on [C] `def:Qn`'s fixed basis `{u_0, …, u_{ell−1}, u_{n+ell+1}}` (the
  top-down reduction `u_r ↦ u_{r−ell+1}`); its relation list (the `Sym^n` list's rows, tags, simplices and
  `g_r`, other matrices); `HeckeOperatorOnK` on it with `d_V = ell + 1`, `n_sym` read from the tau table
  (the tables of `Sym^n`), its own program-cache tag `kQuotientLKeyTag`. The `SymN` dispatch line runs
  first and the contragredient keeps its tag, so both old paths are byte-identical.
- **`Hecke/LadicCell`** (slot-11 WP-18c; [E] v1.12.0 `sec:ring`, `ENGINE_API.md` §13.11.11) —
  `hecke::ladic_cell::RunCell`, the digit pipeline route at `ell^k ≥ 2^64`, `ell ≥ 5`: (1) `e_max` from
  the **shipped** native `K`-mode at word size (start `K0 = max(2, ⌊1 + log_ell(n/(ell+1))⌋ + 1)`,
  escalated once to `K_w`; uncertified at the last level → `PrecisionInsufficient`, a
  `NotImplementedInThisBuild`, exit 5, with the R3 state `ladic_precision`; `ladic_type^2` asserted 0);
  `K = k + e_max`. (2) Over `Z/ell^K` in planes (WP-18b's recipe): `C^q_eq` (asserted free), `X_q`
  (residual checked), `Z^q`, (c1)–(c5), `dK`; the stopping rule re-evaluated at `K`; UCT of
  `H^q(Z/ell^K)` against the certified type. (3) `Θ_g` both routes from the shipped exact coset / τ
  tables, asserted equal; `A^{(q)}` by `cyclic_coordinates`; the free block and a division-free
  Berkowitz charpoly at precision `k`; `ρ_n(g)` by §13.10 F4 on `Ring<W>`. (4) At `p = ell` the
  **ordinary idempotent** `e = −p_0^{-1} W s(W)`, `W = U^{rk}`, `χ_W = x^a p(x)`, certified by `e² = e`,
  commutation with every Hecke matrix of the cell, `(U(1 − e))^r ≡ 0 mod ell` and
  `rank_{F_ell} e = rank_{F_ell}(U mod ell)^r` ([C] `def:ordinary`; the ordinary part is torsion-free at
  level 1 by [C] `rmk:ordtorsionfree`). No existing class template is instantiated for a new element
  type. The campaign's ring job loop runs digit jobs (`CampaignRing::RunDigitPipeline`: `route`,
  `precision`, textual `modulus`, `hida` with keys `precision`, `rank`, `rank_e_mod_ell`,
  `ordinary_rank_mod_ell`, `certified`, `e`); spec validation applies the per-cell rule
  (`RequireDigitCell`). `HeckeLadicCellValidation` (`standard`, 891).

### Hecke action and extensions — the slot-12 additions

- **`Hecke/HeckeOrdinaryPart`** (slot-12 WP-4, WP-11; [C] v1.12.0-pre.2 `sec:hida`) — namespace
  `hecke::ordinary`. `TorsionExponentPrepass(n, ell)`: `J_n = [ρ_n(S) − 1; ρ_n(T) − 1]` over `Z/ell^e`
  (`ComputeSymmetricPowerMatrixRing`, the pipeline's basis), `λ_e` = the length of `ker(J_n mod ell^e)` (`e = 1` over
  `F_ell`, `e ≥ 2` by `engine::elim::kernel_module`), stopped at the first `λ_{e+1} = λ_e`; the torsion multiset read
  separately from `invariant_factors` of colspan `J_n` over `Z/ell^{e_max+1}`, and the second stopping rule
  (`r_{e_max+1}(J_n) = n + 1`) `ENGINE_CHECK`ed — `prop:torsionprepass`, valid at every prime, `n ≥ 1` (`n = 0` refused;
  beyond `2^64` refused by name). `RequirePrecisionUse` / `CertifiedWorkingPrecision(n, ell, e') = e' + e_max`,
  `ell ≥ 5` only (`cor:ordprecision`). `FreeRankH1(n)` = `2d_k − 1` / 0. `OrdinaryExponent`: `lem:ordexponent`'s
  `N_ord(g, K) = ell^{K−1+⌈log_ell g⌉} ∏_{f≤g}(ell^f − 1)` kept as factors; `U^N` by those factors
  (`X^{ell^f−1} = ∏_{i<f}(X^{ell−1})^{ell^i}`), `value()` only where it fits `u128`. `RingMat` (endomorphisms of
  `⊕ Z/ell^{a_i}`) and `OrdinaryProjector(U) = U^{N_ord(rows, max a_i)}`. `ApplyTpOnH0` (`T_p` on `ker J_n` by right
  coset representatives). Modular sums in `u128` (A3). **`LadicCell`**: opt-in `Request::precision_source =
  Prepass` (`e_max` and the `Z_(ell)`-type from the pre-pass, no word-size run; ` prepass=1` in the record text
  only there); `DefaultWordLevels` the one escalation policy; `CertifiedWordKMode` exposes step 1.
  `HeckeOrdinaryPrecisionValidation` (`standard`, 916).
- **`HeckeExt/HeckeHidaTower`** (slot-12 WP-5, WP-11; `hecke_ext::hida`) — per cell `(n, ell)`: `K = m_max + e_max`
  (the pre-pass, before the run); `H_K`, `U_ell`, `T_2`, `T_3` by the shipped module route
  (`EquivariantCohomologyOnKT<uint64_t>`, `HeckeOperatorOnKT::H_matrix_module`, under `tau_construction_mutex`);
  `ReadOnModule` (on `H_{e'}`, torsion included, `cor:ordprecision`(1)) and `ReadOnFreeBlock` (the summands of
  order `ell^K`, (2)–(3)); in each `P = OrdinaryProjector(U)`, its `F_ell`-rank, `TopLayerRank` (`P M` free, A4),
  idempotence, commutation and `χ(T_p | P M)` by `CharpolyOnImage` (a Nakayama basis of columns of `P`, an
  `ell`-adic digit solve, re-verified, Berkowitz over `Z/ell^{e'}`); `PredictedOrdinaryRank` (Hi3's committed
  table); one `HIDA_TOWER` line per cell (stdout only). The validations run cells concurrently (≤ 12 threads on
  the shared engine pool; checks in grid order; the (Det) arm recomputes four cells sequentially).
  `HeckeHidaTowerValidation` (`standard`, 5222: even `n ≤ 80` + named `Tw_2` partners, `(10, 2411)` at `K = 2`),
  `HeckeHidaTowerSlowValidation` (`slow`, 11 722, ≈ 160 s).
- **`HeckeExt/HeckeHidaLambda`** (slot-19 WP-HL; `hecke_ext::lambda`; [U] 0.3.0-pre.3 `sec:u-lambda`) — the truncated
  `Λ`-adic ordinary Hecke algebra `T^ord(a) ⊗ Λ/(ℓ^K, X^m)`, a C++ port of R19-2's prototype (`docs/implementation/slot19/r192/`).
  **Arm (Q)** (`HeckeHidaLambdaForms.cpp`, the primary input by owner ruling 2026-10-03): `M_k(Z/ℓ^W)` on the Miller basis
  `Δ^j E4^{a+3(d−j)} E6^b` from q-expansions (series products by an exact multimodular NTT over three or four 62-bit primes,
  Montgomery, Garner straight into `Z/ℓ^W`; residues in `u128`, `ℓ^W < 2^84`), `T_p` by `a_n(T_p f) = a_{pn} + p^{k−1}a_{n/p}`, the ordinary
  projector `T_ℓ^N` (columns independent mod `ℓ`), `U = T_ℓ` on `e M_k` (`k − 1 ≥ W`, refused otherwise). **Λ stage**
  (`HeckeHidaLambda.cpp`): a certified Fitting split (`V_E` = the `m_Eis`-part: every `T_p − eis_p`, `U − 1` nilpotent mod `ℓ` on it),
  the monogenic route through `InterpolateTruncation` (thm:u-interp with its precision bound **enforced**: consecutive weights,
  `N ≤ ℓ`, `N ≥ K + m − 1`, values mod `ℓ^{K'}` with `K' ≥ K + m − 1`, else `REFUSED`), the general route (Howell spans over
  `Z/ℓ^{K+N−1}`, refused below), Bernoulli values by tangent numbers mod `ℓ^{W+V}` (cross-checked against WP-NF's exact `B_k`),
  `α`, the rungs, `G̃(0) mod ℓ^5`; `RecordLines` emits `hecke_lambda/v1`. The cohomological tower route (`HeckeHidaTower`) is a
  cross-check at 37 and 103 only. `HeckeLambdaValidation` (`standard`).
- **`HeckeExt/HeckeCensusCellList`** (slot-12 WP-6; STL only) — the cell-list parser (`<n> <ell>
  [<u_ell_budget_mb>]`, `#` comments; refusals with a line number) and `CensusEdition1Grid()`; consumed by
  `HeckeCensusSplitValidation` arm (D) (`HECKE_CENSUS_SPLIT_CELLS`) and `HeckeDicksonThetaHeckeValidation` (P5)
  (`HECKE_THETA_IMAGE_CELLS`), each winning over its `_ALL=1` twin. `congruence_census.py --edition 2` (tool v2)
  first rebuilds edition 1 in memory byte for byte, then adds `ext_census_l7l11`; it refuses an `--out` under
  `--results`. `HeckeCensusCellListValidation` (`fast`, 45).
- **`HeckeExt/HeckeFormsHeckeAlgebra`** (slot-12 WP-7, WP-11, WP-12; pipeline-free, `hecke_ext::forms`) —
  `DeltaSeries`, `EisensteinSeries`, `BuildCuspSpace` (`S_k(F_ell)`, basis `Δ^j E_6^{2(d−j)} E_{k'}`),
  `BuildModularSpace` (`M_k`, `j = 0 … d`), `HeckeOnCusp` (`T_p` on `q`-expansions, residual-checked on `≥ d`
  coefficients beyond those read, `N = 2·d·p_max + 2`), `SturmRangeOperators`, `LocaliseAtSystem`,
  `NilpotentJordanType`, `RationalEigenvalue`; the algebra by `HeckeAlgebraInvariants`, the linear algebra by
  `Hecke/SubspaceOps`. `HeckeFormsHeckeAlgebraValidation` (`standard`, 163; arms (Q), (D), (R) the [EX] datum,
  (C) the quotient test with `U_ell` ↔ forms `T_ell`, (N), (M), (T) the census, (F) the finality instance) and
  `HeckeBoundaryFinalityValidation` (`standard`, 13 332; same TU, `Registry/Slot12/WP14.cpp`: (L) Lemma B′ on the
  shipped `A^∂(T_p)` — diagonalisable over `F_ell`, the fibre formula at `p mod ell`, same-class equality; (I)
  `dim V = dim T(S_k)_m + dim T(M_k)_m`; (X) the `mixed` control; (H) under `HECKE_BOUNDARY_FINALITY_ALL=1`).
  Neither touches a record writer, the finality logic or a golden collector. **Slot-12 S12-FIN** landed the
  certificates: `HeckeExt/HeckeFinalityRoutes` ((d0) Proposition D, (d1) Proposition F′ with its certificate
  object), run by `HeckeExtDriver` in Stage 4 where (a)–(c) fail; the record is `hecke_ext/v4`
  (`certificate_routes.d0` / `.d1`, `boundary_reps`, names `dickson` / `boundary`, `verify()` 30 / 31); the
  validation (now 13 389 checks) compares the driver's emitted routes with its independent computation (arms (X),
  (R), (H)). Golden: 62 `ext_json_*` lines (`docs/matrix-engine/rebaseline-2026-09-26-hecke-ext-v4-finality.md`).
- **F-1's named ring guards** (slot-12 WP-1): `GenerateSL2ZQuotientLRelationsWithGroupData` and
  `ComputeQuotientLMatrixFM` refuse a non-default ring through `hecke::RequireFieldCoefficientRing` naming
  themselves; `HeckeThetaCensusRingRefusalValidation` (`fast`, 15) probes five closure members.

### Hecke action and extensions — the slot-13 additions

- **The `U_ell` memory lever** (slot-13 WP-4, audit repairs WP-14; `Hecke/HeckeLowRank.h`, `hecke::lowrank`) — opt-in
  through `HeckeOperatorOptions::ScopedUEllLowRank` (thread-local, propagated into the engine's host fan-out like the
  other `HeckeOperatorOptions`; not a mathematical setting, so no fingerprint, record or job id sees it; refused unless
  `ell | N` and the fibre is `SymN`). Step 0 (`ENGINE_TRACE_RSS` at `(128, 691)`) attributed the 238 B per entry per coset:
  193 B are `ρ_n(M)` with `M` singular mod `ell` (the per-`(i, slot)` product temps, route 2's `rho2`, the τ pool and its
  certification cache), each of rank `≤ min(k, n + 1)` (`M = P diag(1, ell) Q`); 34 B are the coset tables' `ρ_n` of
  unimodular matrices — the floor. `factor_low_rank` writes a block as `U V` by exact min-valuation elimination (the
  term count `ENGINE_CHECK`ed per block, `U V = R` re-derived under `ENGINE_DEBUG_CHECK`); a τ table constructed inside
  the scope keeps `rho_pool()` factored (0 × 0 placeholders on which `RhoRefT::get()` throws); `compute_block`
  assembles `Σ c (Ω_i U) V` with one GEMM per block; route 2 factors `ρ_n(δ_i γ_k)` and still compares every entry
  (O12(a)); the module route holds `(Ω_i U, V)`. A race found and fixed in the package: a scalar-flagged `Ω_i` is applied
  as `α U`, never borrowed. ≈ 5× smaller, ≈ 1.8× faster; fit `rss_MiB = (ell + 1)(0.0697 + 37.2e-6 (n+1)²) +
  4793e-6 (n+1)²`. `--bench … --u-ell-low-rank`. The frozen `u_ell_rss/v2` model is unchanged.
- **Hida part 2** (slot-13 WP-5; [C] v1.13.0 `def:hidalattice`, (Hi7)–(Hi9)) — `FibreRepresentation::HidaLatticeH`
  (`ρ^H_n(A) = ρ_n(A^T)^T`, Hida's lattice `L_n`, `D`-conjugate to `Sym^n`, `D = diag(binom(n, j))`) on the module
  route only; the module route's **Nakayama-basis fallback** in `EquivariantCohomologyOnK::compute_cohomology_module`
  (non-unit Howell pivots of a free `C^q_eq` on `L_n`; checked free by length; value-preserving on the unit-pivot
  branch). `HeckeHidaTower`: towers mod `ell³` (`K = 3 + e_max`), `T_5` / `T_7`, `ModuleDatum`, `DecideIsomorphic`
  (the (Hi8) decision procedure: `Hom` over `Z/ell^m`, cheap invariants first, `det` on a grid, a verified certificate
  or "not isomorphic"), `LatticePair` / `ReadDstar` (`D_*`). `HeckeOrdinaryPart`: the pre-pass beyond `2^64` by
  `engine::ladic` (`PrepassRoute::Auto`).
- **`Γ_0(ell)` on the model** (slot-13 WP-6; `Hecke/HeckeLevelEll`, `hecke::level`; [C] v1.13.0 `sec:levelshapiro`,
  `sec:stabilisation`) — the owner's Shapiro route: the level-`ell` model is the induced local system on the fixed
  `(K, Rel)` (`Gamma0Level` reads the shipped `HeckeCosetTables` at `N = p^ν`). `BuildLevelCorrespondence` is
  `eq:levelcorr` for every `[A g B]`: block `(σ, i) ← (σ', a·γ)` with coefficient `c ρ_n(v_i s_j^{-1} g γ w_{a·γ}^{-1})`,
  every product exact and `det = det g` checked, reading only the level-1 τ-table (no new coset or τ table);
  `BuildUellLevelEllFused` the second route (`eq:Ulevellmodel`); `BlockCochainMap` applies operators as block terms,
  det-`ell` blocks factored (`2d` per column). The cohomology is the shipped dense `EquivariantCohomologyOnK` at
  `D = (ell + 1)(n + 1)` (37 s of the validation's 42 s); the monomial / orbit-wise routes of `rmk:levelcost` and the
  Manin–Merel action (`rmk:levelscaling` (O2)) are the general-`N` interface, not built.
- **`hecke_ext/v5`** (slot-13 WP-7) — see `HeckeExt/README.md` "Slot 13": (d1)'s `boundary_data` in the record,
  `verify()` code 32; golden R2.
- **`HeckeCensusLattice`** (slot-13 WP-9) — C-F9 on the census: the lattice mod `ell²` by the module route with the
  Fitting projector `e_m = ∏_q (1 − (T_q − ã_q)^{N_ord})`, against the `F_ell` block; at `ell ≥ 5` the lattice statement
  is `loewy(A) ≤ 2` (the higher cohomology of `SL_2(Z)` is killed by 12).
- **`HeckeHidaHeavyCellProbe`** (slot-13 WP-10) — `m = 1` field route, `m ≥ 2` module route, `U_ell` under the lever,
  the ordinary summand `im U^{m g}` read by a Nakayama basis, `B X = T B` verified on every row, Faddeev–LeVerrier;
  only `e_max = 0` served.
- **Digit handles** (slot-13 WP-12, A2 of WP-13) — `RunDigitPipeline` books the Hecke + Hida step as
  `CellRecord::hecke_seconds` (timing only, never hashed); `HeckeVal::ensure` keeps a bounded (4) process-wide cache
  keyed `(n, ell, k, width, p, hida, precision_source)` so a repeated `hecke(H, p)` on a digit handle is served from the
  stored record; a different `p` still recomputes the cell (re-carried).

### Hecke action and extensions — the slot-14 additions

- **`HeckeExt/HeckeRingHeckeAlgebra`** (slot-14 WP-6; [E] v1.15.1-pre.2 `sec:ring`) — the `Z/ell^K` Hecke-algebra route of [M1] in C++, reading the algebra
  `Z_ell[T_p]` mod `ell` from `H^1(Gamma; Sym^n Z/ell^K)`: the shipped module route on `uint32_t` (`ell^K < 2^32`) or `uint64_t`, `RationalSystems`,
  `Localize` (`e_m` Newton-lifted, the block by the shipped cyclic-summand rule — torsion summands are handled), `ReadAlgebra` (`howell` / `length` only, the
  `shift = t` reading of the free part), `ComputeRingLoewyCell` and the `LOEWY_RING` line. Verdicts are readings, not certificates. `ell^K >= 2^64` refused by name.
  `HeckeRingLoewyValidation` (`standard`, 123); env `HECKE_RING_LOEWY_CELLS`. No record key, no golden object.
- **The `U_ell` levers, default-on** (slot-14 WP-10 and G0; owner Q8) — the low-rank lever (`Auto`), coset streaming and the serial phase on the pool are
  the defaults, each with an opt-out (`HECKE_U_ELL_LOW_RANK=0`, `HECKE_COSET_STREAM=0`, `HECKE_PARALLEL_SETUP=0`), and G0's rank-one closed form
  (`HECKE_RANK1_CLOSED_FORM=0`) with a per-pool host fan-out budget. Value-preserving, no fingerprint. Detail is in the module-by-module list
  (`Hecke/HeckeLowRank.h`) and `docs/performance-reference.md`. `HeckeUEllStreamValidation` (`standard`, 2262) takes the opt-out path as its reference.
- **`Hecke/HeckeLevelN`** (slot-14 WP-12, gated by Q4; [C] v1.14.2 `sec:levelN`) — level `N` on the fixed model by Shapiro, extending slot-13's plug points:
  `Gamma0LevelN`, `Gamma0SubTransversalN`, `InducedRelationsLevel`, `MonomialAction`, `OrbitWiseFixedSpace` / `CokernelFromFixedSpaces`
  (`prop:levelorbit`), the count functions; operators are the shipped `BuildLevelCorrespondence`. Pipeline-free and value-free; the Heilbronn action and the
  sparse route are slot 15. `HeckeLevelNValidation` (`standard`, 1665); env `HECKE_LEVEL_N_R3_CELLS`.
- **The harness catch path** (slot-14 WP-2; slot-13 WP-16 introduced it) — an exception escaping a validation is reported as that validation's failure
  (`[EXCEPTION] <name>: ...`, then `[FAIL]`) and the run goes on. It now has its own test, `ValidationHarnessCatchValidation` (`fast`): two engineered throws (a
  `std::logic_error` and a non-`std::exception`) must come back `[FAIL]`, not abort. Also WP-2: the `EFFECTIVE` convention for env-armed arms, the ISA-aware
  performance floor, and the tree-locating fallbacks of two guards.
- **G1 / G2 and the device release** (slot-14 WP-3) — index products in `size_t` with `ENGINE_CHECK`s (`FlatMatrix`, the recorder's strides) and the arena
  lifetime rule on device release (ENGINE_API §6 / §11 / §12.5).

### The slot-21 additions (and the early slot-22 packages on the branch at the slot-21 close)

Added at the slot-21 close (2026-10-06) as a factual list; what each validation checks is in `docs/validation-catalogue.md`.

- **Registration fragments.** `Registry/Slot21/` + `cmake/slot21/` (`T1_lll`, `P7_qexp`, `T2_ribet`, `P8_msym`, `P9_twovar`, `P3_coeffring`, `P2_eismeas`,
  `P4_wild`, `P5_iwasawa`, `WPLIC`, `WPNB`, `WPENG`; order in `Registry/Slot21/README.md`); slot 22 uses `Registry/Slot22/` + `cmake/slot22/` (`90aa4bc5`).
- **`NumberField/`** (STL only, `check_numberfield_includes.sh`): `Lll` (T1, in-house LLL; `NumberFieldLllValidation`, `fast`), `Polred`, `MpReal`
  (multiprecision reals) and `RibetField` (T2: the degree-`ℓ` Ribet-field polynomial, done at 37, partial at 691 by plan; `NumberFieldRibetFieldValidation`,
  `standard`, arm `NUMBERFIELD_RIBET_CELLS`).
- **`HeckeExt/LValue/`** (the `ℓ`-adic track, [E] 1.21.0): `EisensteinMeasure` + `EisensteinBernoulliRoute` + `TwistedEisensteinCell` (P2 / P2x; Eisenstein
  measure exactly in Λ), `CoefficientRingMeasure` + `CoefficientRingFrozenP3` (P3), `WildCharacter` (P4 / P4x, the 128-bit route for `(226, 103)`),
  `HeckeLValueIwasawaInvariantsValidation` (P5 (b), (c)); validations `HeckeLValue{CoefficientRing,EisensteinMeasure,WildCharacter,IwasawaInvariants}Validation`
  (`standard`, each with a `…_HEAVY=1` arm).
- **`HeckeExt/` Λ-adic files** ([U] 0.5.0 part 4): `HeckeLambdaQExp` (P7, Λ-adic `q`-expansions), `HeckeLambdaModSym` (P8, ordinary cohomology as a
  Λ-module), `HeckeLambdaTwoVar` (P9, the two-variable measure by interpolation), each with its `…Validation` (`standard`).
- **`Hecke/` level `N` at `p = 2, 3`** (early slot 22, LN23; [C] v1.21.0 `prop:levelNcurve`): orbit-sum fixed spaces of `S`, `ST` at `n = 0` at every `p`, sparse
  and dense routes; `Hecke/HeckeLevelNCurveValidation` (`standard`, arm `HECKE_LN23_HEAVY=1`).
- **Console.** Read-only verbs `pow`, `kummer_unit`, `hida_tower` (slot 21; scripts `050`, `051`) and `level_n`, `nebentypus`, `forms_algebra`, `hida_lambda`
  (slot-22 WP-VERB-2, `17e93767`; scripts `052`, `053`); each tagged `read_only` in `Console/Bindings/ReadOnlyTags.cpp` and `Console/serve/read_only_verbs.tsv`
  (166 of 175 overloads). `VerbRss` reads `VmRSS` before `VmHWM` (`64602a59`, `KNOWN_ISSUES.md` §6).
- **Notebook theme** (slot-22 FR-1): `notebook/page/themes.js` (presets Auto / Light / Dark / two high-contrast / Custom, a 13-token editor with WCAG contrast
  warnings, import / export as `oc-notebook-theme/1`); client-side only, no server state, no verb; gateway self-test 22 tests.
- **Licence tooling** (WP-LIC, WP-LIC2): `REUSE.toml`, `LICENSES/`, `LICENSE`, `LICENSE.GPL`, `NOTICE`, `COPYRIGHT.md`, `docs/LICENSE`, `lean/LICENSE`,
  `docs/licence/THIRD_PARTY.md`; `docs/licence/tools/add_spdx.py` (sweep / check) and `check_licences.sh`, run by `LicenceGuardValidation` (`fast`,
  `Registry/Slot21/WPLIC.cpp`).
- **Lean vendoring** (L21-V): `lean/Vendor/AnthropicFLT/` (25 modules, byte-identical, `MANIFEST.tsv`, `PROVENANCE.md`), `[[lean_lib]] AnthropicFLT`; the
  `VENDOR_OPTION_ALLOW` allowance in `lean/tools/lean_census.py`.

### Integral line — `src/hacs/Integral/` (hecke-extensions slots 8–11)

Line 2 of the owner's two-line direction (true computation over `Z`), designed in
`docs/implementation/integral_line_design_brief.md` [IB] and specified by [C] v1.8.0 Part VI
(`sec:integral`). Pure host C++, compiled into `cohomology_app`; no bignum anywhere ([IB] OD-3 (c):
residue vectors plus certified bounds, reconstruction out of process).
- **`IntegralCharpolyCrt`** (WP-7, milestone M-0) — `char_Z(T_p | Λ^1)` by CRT over existing `F_ell`
  runs of the shipped pipeline at good primes `ell > n + 1` (where `H^1(F_ell) = Λ^1 ⊗ F_ell`),
  primes taken descending from `2^30`, the Deligne bound carried as a bit length, the O5 table
  frozen in source ([C] `prop:crtcharpoly`). It builds `F_ell` local systems, so under a non-default
  `coefficient_ring` `EquivariantCohomologyOnK` refuses it structurally. Gated by
  `HeckeIntegralCharpolyValidation` (`standard`, 322 checks; `HECKE_INTEGRAL_CAMPAIGN=1` adds the
  `n = 128` arm).
- **`HeckeBredonTreeValidation`** (WP-8, V-B) — `TreeRhoN`, `TreeModelDims`: the Bredon cohomology
  of the Bass–Serre tree model over `F_ell`, `ell ∈ {2, 3}`, against the shipped pipeline on 82 cells
  `n ≤ 40` and a frozen 16-cell golden oracle table ([C] `prop:bredon`(2)).
- **`HeckeBredonTreeRingValidation`** (slot-9 WP-3, `standard`, 1394 checks) — E8 at `ell ∈ {2, 3}`:
  the Bredon flat-coordinate route over `Z/ell^k` against the frozen O7 table on 96 cells
  (`k ∈ {2, 3, 4}`, even `n ≤ 20`, odd `n ≤ 9`; the 30 `−I` / odd-`n` cells printed by name), with
  O7 controls at `k = 1` (= the `F_ell` pipeline) and at `ell = 5` (= slot 8's module route) and an
  in-process tree model as a consistency check. `HeckeBredonU64FlatRouteValidation` (WP-9, `fast`):
  one honouring `uint64_t` cell (`Z/2^33`, `n = 4`) against O7 through the route's `K`-scaling law
  (an invariant factor equal to `K` is a free-rank artefact, one below `K` genuine torsion).
- **`Integral/Model/IsotropyModel`** (slot-9 WP-10, line 2's phase **L2-1a**, namespace
  `integral_model`; includes `Hecke/ExactInt.h` and `ModArithmetic/` only) — [C] `def:isomodel` made
  effective: the descriptor of `def:model7` (`Σ_0` five vertices, `Σ_1` nine edges, `Σ_2` five
  triangles, the four transporters of `lem:model7coincidences`(2), stabilisers `ST` / `S` / `−I` of
  orders 6 / 4 / 2), `d^(0) = (−1)^s d^F`, `d^(1)` / `d^(2)` by the contracting homotopy of the periodic
  resolution coset by coset (every homotopy input `ENGINE_CHECK`ed to be a cycle), to degree
  `q_max + 1` (default 6); `certify()` (`d² = 0`, `R_∂` closed, `ε` a chain map, `ε(R_∂) ⊂ Xbdry`,
  exactly over `Z[Γ]`); `coboundary(ctx, n, q)` / `boundary_coboundary` / `comparison` (`ε^*` on the
  pipeline's flat layout) / `cohomology_lengths` over any `ModCtx`. 11 distinct group elements, all
  coefficients ±1 — the integer-size risk did not materialise. [IB]'s ranks 7/18/23 were wrong; the
  code has `prop:isomodel`(2)'s 5/14/19. `HeckeIsotropyModelValidation` (`standard`, 1032 checks: the
  ranks, the certificates, `ε^*` an isomorphism on `H^0`, `H^1` at five `ell ≥ 5`, [IB] Appendix A
  through universal coefficients at `ell ∈ {2, 3}` over fields and `Z/ell^k`, `R_∂` against
  `H^•(Γ_∂)`); `IsotropyModelDeltaSquaredValidation` (WP-9, `fast`, 20 checks: `δ² = 0` on `C_I(R)`
  directly).
- **`Integral/Model/IntegralGroups`** (slot-9 WP-11, milestone **M0**, a/s, accepted) —
  `RationalRanksAtGoodPrime` (`ℓ' ≥ 5`, `ℓ' > n + 1`; M0 uses 10007), `CertifyAtPrime` (per
  differential, `K = 2, 3, …` until `r_K(d^q) = rank_Q d^q`; the non-unit elementary divisors are
  `K − e_t`; [C] `prop:certifiede`(1)–(2) and `rmk:certifiedeperdiff`), `AssembleFromModel`,
  `PredictedLengths` (the UCT prediction), `DicksonPrimes`, `AbelianGroupType`. The rule runs on
  `C_I` only, never on the Bredon object. `HeckeFreeModelValidation` ([X]'s E9 name re-hosted,
  `standard`, 803 checks, ≈ 3–4 s): `H^q(SL_2(Z); Sym^n Z²)`, `n ≤ 20`, `q ≤ 5`, equal to [IB]
  Appendix A (O1) on all 126 cells; O2, X3 (the cone of `ε^*` acyclic over `Z/ℓ^K` through degree 5 at
  the ten Dickson cells), O9 (with `tors H^6`), O8, [X] E9's tests (1), (2), (6). Since slot-10 WP-8
  (m-6 / m-7 closed): (T6)'s negative control builds the shipped 7-vertex complex and refuses because
  that object has only 3 cohomological degrees (< `q_max`); arm (R) dropped (the two names cite their
  own `--list` lines); **801 checks**. Tests (3)–(5) are hosted by `HeckePeriodicityClassValidation` and
  `HeckeIntegralActionValidation` (below).
- **`Integral/Model/StrictLift`** (slot-10 WP-10, line 2's **L2-1b (1)**, [C] `prop:strictlift`,
  `lem:strictlifting`, `rmk:strictliftbuilt`) — `g = diag(1, p)`, `Γ″ = Γ_0(p)`; `R` free over
  `Z[Γ″]` on `{s_j e_c}`, so a (T1)-map is a free choice of the values `τ_Iso(s_j e_c)`, extended
  through `HeckeCosetTables::twisted_conjugate`. Built degree by degree to `q_max + 1 = 6`, boundary
  summands first: `y_0` read off the shipped `BoundaryStrict` table term by term as `γ g_tr e_{ρ,0}`
  (at `t = 0`; `y_0 = 0` above), then `k` with `∂k = τ_Iso(∂x) − ∂y_0` by **descent through the
  columns** with the closed-form `Z`-linear contracting homotopies (`k_s = (−1)^s h(z_s)`) — **no
  linear solve** (the plan's `HeckeIntegerSolve` step was unnecessary: `ker ε` is the sum of the
  augmented periodic columns). `certify()` re-derives (T1) on the Schreier generators of `Γ″`
  (definitional on the free basis — it certifies the bookkeeping), (T2), (T3), (S) `ε τ_Iso = τ^s ε`
  as canonical `Xbulk` chains, (B) `τ_Iso(R_∂) ⊆ R_∂` and `ε τ^∂_Iso = τ_∂ ε` against the boundary
  table. `theta_hat(ctx, n, q)`: the coset transport `Θ̂_g` on `C^q_I` over any `ModCtx<uint32_t |
  uint64_t>` (`δ_j γ` formed exactly, never inverted). `StrictLiftBundle(p, q_max)` owns K, the
  tessellation, the coset table, `τ_∂`, `τ^s`, `R` and the lift. Integer sizes (K1): coefficients ≤ 3,
  entries ≤ `p`, ≤ 26 terms per value, period 2 from degree 2. Only `T_p` (`diag(1, p)`) is built;
  `diag(1, p²)` / `diag(p, p)` are slot 11 (M-3). `HeckeStrictLiftValidation` (`standard`, 1824).
- **`Integral/Model/PeriodicityClass`** (slot-10 WP-13, **L2-1b (2)**, [C] `lem:bulkperiodic`) — `χ:
  Γ → Z/12` (`χ(S) = 3/12`, `χ(ST) = 2/12`), `Φ ∈ Hom_{Z[Γ]}(R_1, Z)` an integer lift of `12·χ` via
  the chain map to the bar resolution, `e := (Φ ∘ d_2)/12` (the Bockstein; division `ENGINE_CHECK`ed
  exact; `e = [1,1,1,1,1, 0×13, 1]` on `R_2`'s 19 generators); `E_0(e_c) = e(c)·e_{0,v0,0}`,
  `E_q = fill(q−1, E_{q−1}(d e_c))` for `q ≤ 4` by the staircase of the `s`-filtration (the columns'
  homotopies; in degree 0 paths and `c_γ`; in degree 1 the unique 2-chain of `Xbulk` bounding a
  1-cycle, found over `F_134217757` and certified exactly over `Z`); `E_q^*` over any `ModCtx`; the
  Mayer–Vietoris connecting cochains through the Bass–Serre tree (`φ: C(Xbulk) → C(T)` certified a
  chain map). `certify()`: `e ∘ d_3 = 0`, `12e = Φ ∘ d_2`, `χ = ζ_+` on 224 finite-order elements,
  `aug E_0 = e`, `d E = E d` on 76 generators over `Z[Γ]`. Re-implements ≈ 30 lines of
  `IsotropyModel.cpp`'s anonymous helpers (the third copy with `StrictLift`; one
  `PeriodicColumn.h` is a slot-11 candidate, review m-2). `HeckePeriodicityClassValidation`
  (`standard`, 2483).
- **`Integral/Model/IntegralHecke`** (slot-10 WP-11, **M1(a)**, a/s, accepted) — `ModelCohomology<Elt>`
  (`C_I ⊗ R` at one `n`: `δ^q`, `Z^q` — a basis over a field, Howell generators over `Z/ell^k` with
  `length Z^q` by rank–nullity — and `B^q`; `induces_zero(q_src, q_dst, P)` checks `P(Z) ⊆ B`, the
  basis-free form of an operator identity on cohomology), `Subquotient` / `OperatorMatrix` (the operator
  induced on `(G + Rl)/Rl` via `complement_basis` over a field and [E] `sec:ring` (c)'s
  `cyclic_decomposition` over the ring), `CharpolyDivisionFree` (signed principal minors, valid over
  `Z/ell^m`, `t ≤ 7`), `ReducedCocycles`; the header proves the three UCT torsion readings (sub),
  (quot), (lat). `T_p` is `StrictLift::theta_hat`, `E_q` is `PeriodicityClass::matrix`.
  `HeckeIntegralActionValidation` (`standard`, 4601): [IB] §6.2 M1(a) items 1, 2, 4, 5 in full, item 3
  with X7 = commutativity (the `thm:relations` recursion needs the `diag(1, p²)` / `diag(p, p)` lifts).
  `uint32_t` only; no bignum, no `__int128`.
- None of the three is a member of [E] `sec:ring` (b)'s refusal closure: each takes its ring as an
  explicit `ModCtx`, reads no mathematical setting, adds no key, record or golden object, and
  constructs `EquivariantCohomologyOnK` / `HeckeOperatorOnK` only inside `*Validation.*`.
- **M-3** (slot-11 WP-11, accepted): `StrictLift` also builds `τ_Iso` for `diag(1, p²)`, `diag(1, p³)`
  (`p ∈ {2, 3}`; `p = 5` for `diag(1, 25)`) and the central `pI` (`τ = id` of [C] `prop:diamond`'s proof
  as `τ^s`), certified exactly over `Z[Γ″]` with their integer sizes printed; `Θ̂_g` a cochain map over
  fields, `Z/ell^k` and 64-bit `Z/ell^K`; strict compatibility with the shipped `BoundaryStrict` table at
  `r = 2`; `T(p, p) = p^n` on `H^q(C_I ⊗ R)`; **X7 in full** — the full operators of [C]
  `eq:fullassembly` (`T_{p²} = Θ̂_{diag(1,p²)} + Θ̂_{pI}`, `T_{p³} = Θ̂_{diag(1,p³)} + p^n Θ̂_{diag(1,p)}`)
  satisfy `T_{p^{ν+1}} = T_p T_{p^ν} − p^{n+1} T_{p^{ν−1}}`, `ν ∈ {1, 2}`, on `H^q`, `q ≤ 5`, basis-free,
  at 2 and 3 (with `p = ell`) and at good primes, with the `err:e1` and `rmk:relcoeff` negative controls;
  the `ell ≥ 5` consistency with the shipped primitive `T_{p^ν}`; [C] `prop:relationsmodel`(2).
  `HeckeStrictLiftRelationsValidation` (`standard`, 3619).
- **Not built** (line 2's later phases, [X] v1.15 §8): the pair and cone over `Z` (L2-3), the record and
  the golden emission (L2-4), M1(b) (OD-3). `HeckeOperatorOnK`
  over `Z/ell^K` at `ell ∈ {2, 3}` is **withdrawn** (owner decision 4 (A); [C] `rmk:bredonhecke`).

---

## Deprecated substrate: `BlockFlatMatrix` (full text)

Moved out of `CLAUDE.md`'s "ModArithmetic library" bullet list.

- **BlockFlatMatrix** — Block matrix of FlatMatrix entries with deduplication of identical blocks (`unique_blocks_` + index layout). Implements block Gaussian elimination with two-phase RREF (block-level then scalar refinement). Caches multiple RREF representations. **Deprecated since Phase 3 and legacy-arm only** — the live block model is `engine::BlockMat` / `engine::blk` (below). Its validation-only surface was deleted; what remains is exactly what the `ENGINE_BACKEND=legacy` arms and the validations call, guarded by `check_matrix_includes.sh`'s second allow-list (a header banner rather than `[[deprecated]]`, which would add ~103 warnings). **Since S24 CL-L2** it lives in `src/ModArithmetic/legacy/` and is compiled only with `OC_ENABLE_LEGACY=ON`; the allow-list admits it only from files under a `legacy/` directory.

## Build target `ConsoleCore` (full text)

Moved out of `CLAUDE.md`'s build-target list.

- `ConsoleCore` — static library for the console's language core (`src/hacs/Console/Core/`, phase C0: lexer, parser, evaluator, value model, object handles, settings layer, type/verb registry, printers, session, dumb line input, script runner). Like `HeckeCore` it depends on **nothing else in the tree** — STL only — which is what lets the language be validated without constructing a matrix; the rule is enforced by `docs/matrix-engine/tools/check_console_includes.sh`. Everything that needs a matrix, a polynomial or a pipeline object is a *binding* and arrives in phase C1. C0 adds **no** `main.cpp` branch, so the CLI is unchanged. **Since console C1a (hecke-extensions slot 3, WP-7)** the bindings exist as `Console/Bindings/`, compiled into `cohomology_app` and never into `ConsoleCore`, and `main.cpp` has exactly one console branch (`--console` / `-i` / `--script` / `-c` / `-`) — see "Console bindings and CLI (C1a)" under Architecture.

## Cohomology layer — full bullet list (`src/hacs/`)

Moved out of `CLAUDE.md`, which keeps a one-line-per-class form.

- **SimplicialCohomology** — `SimplicialComplex` (simplicial complex by dimension-grouped simplex lists), `CochainComplex` (coboundary operators, cocycle/coboundary/cohomology bases, projectors), `CochainComplexMorphism` (induced maps on cohomology, mapping cones). Includes preset spaces (spheres, cylinder, Möbius band, projective plane).
- **LocalSystemSimplicialComplex** — Defines a local system on a simplicial complex K via `SimplexRelation` structs: `f(s_lhs) = M * f(s_rhs)` identifying simplex values under group action. Wraps a base `SimplicialComplex` with representation dimension and monodromy matrices.
- **EquivariantCohomologyOnK** — Computes H^q_eq(K, R; L) = Z^q_eq / B^q_eq. Finds equivariant cochains (satisfying the local system relations), then computes cocycles, coboundaries, and quotient. Stores projectors from equivariant cochains to cohomology. Since hecke-extensions slot-8 WP-3 also over `Z/ell^k` (`coefficient_ring`), by a module route with lengths and invariant factors in place of dimensions (see "Hecke action", slot 8); since slot-9 WP-3 also at `ell ∈ {2, 3}` by the flat-coordinate module route under `SmallEllPolicy::Bredon` (see "Hecke action", slot 9).
- **EquivariantCochainComplexMorphismOnK** — Induced maps on equivariant cohomology from simplicial inclusions with fiber maps between representations.
- **LocalSystemPresets** — Factory functions for standard local systems on S^1, cylinder, Möbius band with various monodromies (scalar, unipotent, generic).
- **LocalSystemSL2Z** — The main mathematical application: triangulation of SL(2,Z)\H, cohomology with Sym^n(F_p^2) coefficients, and restriction morphisms to the cusp S^1.
- **LocalSystemUtils** — Helper: `ComputeSymmetricPowerMatrix` for the induced action of a 2x2 matrix on Sym^n.
  Since Phase 1 the live implementation is `ComputeSymmetricPowerMatrixFM` (`FlatMatrix.cpp:1440`, `O(d_V^2)`);
  the `Matrix`-returning `ComputeSymmetricPowerMatrix` is deprecated and all 24 live call sites were migrated.

---

## Verbatim originals of three paragraphs `CLAUDE.md` now carries in compressed form

Kept here so no wording is lost.

**`USE_SCALAR_KERNEL` (build note).**

`USE_SCALAR_KERNEL` is defined **nowhere** in this project. It appeared only in a stale in-source `CMakeCache.txt` (`CMAKE_CUDA_FLAGS=-DUSE_SCALAR_KERNEL`), where it reached CUDA TUs that never test it; the C++ `#ifdef USE_SCALAR_KERNEL` branches it never reached have been deleted.

**The cross-config diff runner.**

`docs/matrix-engine/tools/cross_config.sh` generalizes the `HECKE_PURE_INTEGER` protocol above
(`Hecke/README.md`, "To exercise the pure-integer configuration") to an arbitrary list of
configurations: for each it configures + builds `cohomology_app` **out-of-source** under
`--build-root` (default `build-xconfig/`), runs `GOLDEN_STRICT=1 ./hacs
GoldenRegressionValidation`, a list of `--bench micro` cases (default `gemm 512`,
`rref 1677 1419 258`) and any `--validations Name1,Name2`, then prints one matrix (tier A/B
counts, checksums, validation exit codes, wall time) and exits non-zero on any golden failure,
cross-config checksum mismatch, or failed validation. A configuration is
`Config[+OPTION=VAL...][@ENV=VAL...]`, e.g. `RelWithDebInfo+HECKE_PURE_INTEGER=ON`,
`RelWithDebInfo@ENGINE_BACKEND=legacy`; it handles `CheckThread` (`setarch x86_64 -R`) and `Check`
(`ASAN_OPTIONS`/`UBSAN_OPTIONS`) automatically. Usage:

**`Fnv.h` (the one FNV-1a-64).**

- **Fnv.h** (`engine::kFnvOffset64`, `kFnvPrime64`, `FnvU64`, `FnvBytes`, `HashScalar64`, `FnvHasher`) — **the one byte-wise FNV-1a-64** behind every golden, campaign, benchmark and recorded-state hash (hecke-extensions slot 1, WP-2). Dependency-free (`<cstdint>`, `<string>`), which is why it lives here and not under `src/hacs/Util/`: `PerformanceSmokeValidation.cpp` is compiled into this library. `BlockPool.h`'s word-wise hash and `engine::tape::fnv_mix` are different functions, deliberately not folded in.

---

## Moved from CLAUDE.md at the slot-17 start (2026-10-02), verbatim — "Architecture" (ModArithmetic, engine, block model, tape + CUDA, campaign, migration tools, console, cohomology layer, Hecke, HeckeExt, Integral, Lean lane, data flow)

*(Copied unchanged from `CLAUDE.md` at `6863260`, lines 592–1437; headings inside keep their original levels. `CLAUDE.md` now carries a compact form.)*

## Architecture

> **Everything below is a summary.** The full per-module prose — every invariant, every rollback,
> every design rationale — is **`docs/architecture-detail.md`**, section by section in this same
> order. The binding engine contract is `src/ModArithmetic/ENGINE_API.md` (§5 the
> k-blocking overflow bound, §6 layouts, §8 elimination, §9 the block model, §10 the tape,
> §11–§12 the device layer, §13 composite modulus `Z/ell^k` and non-field (Howell) elimination —
> E8's contract, written and reviewed in slot 7, **implemented in slot 8** (E8 items 2–3, WP-1 /
> WP-3; §13.7's choice is the `ModCtx` overload on `BlockMat` / `BlockBuilder`), reviewed again on
> Fable (WP-12); slot 9 touched §10.6 (the options fingerprint), §10.9 (the elimination driver
> honours the process-wide override, WP-6) and §13.7 (a pointer, WP-4); slot 10 §10.6 again (the ninth
> fingerprint bit, WP-8) and **§13.12** (slot-10 WP-9: **L1-X** — a composite-only `u128` element type,
> `U128_Montgomery`, `ell^k < 2^127` — *specified, not built*; §13.11's trigger restated as T-1 / T-2 /
> T-3; the build is an owner question); **slot 11** §13.11 rewritten as the **(C2) `ell`-adic digit
> induction's contract** (slot-11 WP-18b: the precision-split lemma (L1) with its proof, the level
> driver, canonicalisation, the owner's width oracle matrix, `obl:backend`(iv)'s digit-plane reading),
> §13.11.11 (its pipeline consumer, WP-18c), §13.12.9 (the native `u128` layer as built, WP-18a) and §1 /
> §13.5 (F-1's `mul_prep` / `mul_prepped` pair, WP-12); **slot 14** touched §6 (the index and stride domains
> G1 / G2, WP-3), §11 (the device arena's lifetime rule and the release between validations, WP-3 / WP-16) and
> §12.5 (cross-architecture provenance, WP-13)) — **read it before touching a kernel**.

### ModArithmetic library (`src/ModArithmetic/`)

Foundation layer for modular linear algebra over F_p:

- **ModArithmetic** — Primitive operations: `mod_mul`, `mod_add`, `mod_sub`, `mod_inv`, `mod_pow`, `mod_nCr` (Lucas's theorem, with per-`(n, ell)` factorial / inverse-factorial tables since Phase 1). All operate on `uint32_t`.
- **Fnv.h** (`engine::kFnvOffset64`, `kFnvPrime64`, `FnvU64`, `FnvBytes`, `HashScalar64`, `FnvHasher`) — **the one byte-wise FNV-1a-64** behind every golden, campaign, benchmark and recorded-state hash. Dependency-free, which is why it lives here. `BlockPool.h`'s word-wise hash and `engine::tape::fnv_mix` are different functions, deliberately not folded in.
- **Matrix** — Dense matrix with `vector<vector<uint32_t>>` storage. Supports Gaussian elimination, rank, kernel, image, inverse. Caches row echelon form via `unique_ptr`.
- **FlatMatrix** — Row-major flat `vector<uint32_t>` storage. Optimizes scalar matrices (alpha * I) by storing only the scalar. Lazy-caches RREF. Preferred for performance over Matrix.
- **BlockFlatMatrix** — Block matrix of FlatMatrix entries with deduplication of identical blocks; block Gaussian elimination with two-phase RREF. **Deprecated since Phase 3 and legacy-arm only** — the live block model is `engine::BlockMat` / `engine::blk` (below). What remains is exactly what the `ENGINE_BACKEND=legacy` arms and the validations call; since S24 CL-L2 in `legacy/`, compiled only with `OC_ENABLE_LEGACY=ON`. Full text: `docs/architecture-detail.md`.

Each class has a corresponding `*Validation.cpp` file with tests.

#### Arbitrary `k` (slot 11) — native widths and the (C2) digit induction

- **`ModCtxU128.h`** (slot-11 WP-18a) — `ModCtx<u128>`, `Regime::U128_Montgomery`: **composite-only**
  (`prime_power`, odd `ell < 2^64`, `k ≥ 2`, `ell^k < 2^127`; no field constructor, so a field use does
  not compile), Montgomery-128, `engine::u256`; the kernels and the §13.6 entry points instantiated for
  it; `ref::naive128` the oracle. **`DigitWord.h`** — `engine::DigitWord<W>`, `W ∈ {uint32_t, uint64_t,
  u128}`: `digit_exponent(ell)` = the largest `m` with `ell^m < 2^{w−1}`, `mul_wide` / `split` (Knuth D at
  `u128`) / `mac_split`, and the word entry points forwarded verbatim. `EngineU128CompositeValidation`.
- **`LadicInduction.h`** (`engine::ladic`, header-only, slot-11 WP-18b) — `Z/ell^K` for **any** `K` as
  `L = ⌈K/m⌉` fixed-width digit planes: the precision-split lemma (L1) (`ENGINE_API.md` §13.11.3, proved),
  the level driver (the pivot search per window in word arithmetic, replayed at `K`, row side only, three
  `ENGINE_CHECK`s make a divergence throw), `smith_lift`, `howell`, `kernel_module`, `image_module`,
  `cyclic_decomposition`, `invariant_factors`, `stopping_rule`, `truncate` — each the §13.5–§13.6 object
  exactly. **`LadicRef.h`** an independent base-`ell` oracle. `EngineLadicInductionValidation` runs the
  **owner's width oracle matrix** (2 × 32 vs native `u64`; 4 × 32 and 2 × 64 vs native `u128`; cross-width
  agreement beyond `2^127`). **F-1** (WP-12): `ModCtx::mul_prep` / `mul_prepped`, a Montgomery-64 pair on
  the composite row updates (`mul` itself unchanged); **F-2**: the ring travels as `(ell, k)`
  (`declare_coefficient_ring`), `ExactKthRoot` by deterministic Miller–Rabin (`hecke::IsPrimeU64`).

#### Matrix engine (Phase 2) — `namespace engine`

The dense arithmetic and elimination of `FlatMatrix` / `BlockFlatMatrix` hand **non-owning views**
to a layout-aware kernel layer: `ModCtx.h` (per-modulus Barrett / Shoup / Montgomery-64 context,
`batch_inv`, `k_max`; since slot-8 WP-1 also the **composite** context `ModCtx::prime_power(ell, k)`
over `Z/ell^k` — `is_field()`, `valuation`, `unit_part`, `divide_exact`, 208 / 608 bytes, still
trivially copyable — with every field-only entry point `ENGINE_CHECK`ing `is_field()`, §13.3),
`DenseBuf.h` / `DenseView.h`, `Kernels.h/.cpp` (`engine::kernels` GEMM /
GEMV / AXPY / TRMM / transpose, runtime AVX-512 dispatch), `DenseElim.h/.cpp` (`engine::elim`
blocked in-buffer PLU, RREF, kernel / image / `solve_multi_rhs` / `complement_basis` with the
**legacy basis-choice rules**; since slot 8 the **composite-only** Howell / Smith entry points
`howell`, `kernel_module`, `image_module`, `solve_multi_rhs_module`, `length`, `invariant_factors`,
`cyclic_decomposition` of §13.5–§13.6), `RefLinAlg.h/.cpp` (the naive in-tree oracle, `ref::howell`). **Bit-identity is by
construction**: exact accumulation, one reduction per k-block, so vectorisation and blocking cannot
move a bit. Two rollbacks, both preserved: `ENGINE_BACKEND=legacy` (runtime; `engine::elim::ScopedLegacy`
is the thread-local equivalent) and `cmake -DENGINE_SHADOW_LEGACY=ON` (compile time, needs `-DOC_ENABLE_LEGACY=ON`
since S24 CL-L1; runs both and throws on the first differing entry). Detail, including what was deliberately **not** retrofitted:
`docs/architecture-detail.md`.

#### Block model (Phase 3) — `engine::BlockMat` / `engine::blk`

The pipeline declares a block grid, writes **one call per block**, and hands the finished object to
block kernels. `BlockPool` (content-addressed, immutable, refcounted; no hash container anywhere on
a result path), `BlockRef` = `alpha*I + beta*M^(T?)` with `kind ∈ {Zero, Scalar, Dense, Affine}`,
`BlockMat` / `BlockView` / `BlockBuilder`, `BlockKernels.h` (`engine::blk`) and `BlockElim.h`
(panel driver + `kernel_basis` / `image_basis` / `factor_basis` / `solve_multi_rhs`, same **D5b
bases** as the legacy code — golden tier B gates exactly that). **The L1 contract**: a `BlockMat`
with `nbc == 1` over the row partition `(d_V, …, d_V)` *is* the flat cochain layout, and
`to_flat` / `from_flat` are the **single source of truth** for it. The consumers
(`EquivariantCohomologyOnK`, `HeckeOperatorOnK`, `HeckeCrossChecks`, `InducedLocalSystem`,
`EquivariantCochainComplexMorphismOnK`, `SimplicialCohomology`) live on it, and both rollbacks
cover them (`EquivariantCohomologyOptions::ScopedLegacyCohomologyPath`,
`HeckeOperatorOptions::ScopedLegacyHeckeOperatorPath`). **`Matrix` is retired from the pipeline**
(survives for `MatrixValidation`, `HeckeModuleDecomposition` and two read-only consumers; guarded
by `check_matrix_includes.sh`).

#### Matrix engine (Phase 4–5) — the tape (`src/Engine/`, `engine::tape`) and CUDA (`src/Cuda/`, `engine::cuda`)

A consumer **records** a program of block ops on a `Recorder`, `compile()` rewrites it through
**seven passes** (fold, CSE+fusion, layout, k-blocking, batching, device assignment, residency /
transfers), and an `Executor` runs its wavefront levels on a work-stealing `ThreadPool`.
`compile` is idempotent and a pure function of `(program, options)`; every decision is recorded *in
the program*, so a compiled program runs identically under any thread, batching, graph or device
setting. `EngineRuntime.h` is the consumer glue (`consumer_pool()`, `run_cached()` —
record-always / compile-on-miss — `run_concurrently()`, with `thread_local` consumer options
propagated onto task threads; since slot-8 WP-6b `engine::tape::ScopedThreadDevice`, a
**thread-local device override** (`cpu | gpu`) captured by `register_thread_context()`, ENGINE_API
§10.9 — with none installed the process-wide policy is unchanged). **Since slot-9 WP-6** the tape
elimination driver compiles its per-panel programs under `consumer_pass_options()` (the
`ScopedPassOptions` override included), so `set batch` / `set device` and the determinism
validations' batch and device arms really reach them, and `pass_options_fingerprint()` sets its device
bit iff the **effective** policy is not `cpu` (§10.6); no
value, key at the defaults, digest or golden line moved. **Since slot-10 WP-8** a **ninth bit** (256)
is set iff the effective policy is `gpu`, so `hybrid` and `gpu` no longer share a `ProgramCache` slot
(`run_cached()`'s fold `<< 56 → << 55`, since `256 << 56` wraps to 0;
`EngineFingerprintDeviceBitValidation`); cache keys only. **Since slot-10 WP-6** `ThreadPool`'s
cache-line layout is pinned (`alignas(64)` on `slots_` and `regions_`, `static_assert`ed): the global
pool's `.bss` offset had made `(10, 691)`'s 16-thread `--bench ext` ≈ 4 % slower at the slot-9 close
with identical work (the placement lesson, above). **Since slot-9 WP-7 (L3)** the scheduler's
arena first-fit is `O(log L)` per temp (a max-gap treap keyed by offset plus an expiry heap), the same
rule with every offset identical — the old linear scan survives as a `!NDEBUG` cross-check,
`EngineArenaFirstFitValidation`; at `U_10007`, `n = 18` it was 17 s of an 18 s compile.
**Since slot-14 WP-3 (G1 / G2):** `FlatMatrix` forms every index product in `size_t` and `ENGINE_CHECK`s the
materialised size (G1, the owner's Q7: widen). A bound tape view's strides must fit the `uint32` `ld` domain,
`ENGINE_CHECK`ed in `Recorder.cpp` (G2). Both only add refusals. The device arena now frees idle slabs
(`release_cached()`, a soft trim at `ENGINE_CUDA_ARENA_SLACK_MB`, a trim and retry on a `cudaMalloc` OOM), and
the harness releases device memory after every validation (`Util/DeviceRelease`; since WP-16 under every device
policy). This came from the cluster OOMs on the 40 GB A100 and the 94 GB H100 (ENGINE_API §11).

**`ENGINE_DEVICE=cpu` is the default and the golden path.** `gpu` assigns every device-eligible
node (everything but `PANEL_RREF`, `PIVOT_SEARCH`, `COMPARE`); `hybrid` runs the static cost model
of `EngineCostModel.h`. **The GPU is never enabled by default and on the measured evidence must
not be** — the elimination driver records one program per panel, so `gpu` is 1.4–3.3× *slower* on
the pipeline's own shapes. The CUDA layer is exact-integer throughout, so **a device result is the
same bytes as the CPU result by construction**; three gates: `ENGINE_DEVICE=cpu`,
`ENGINE_CUDA_DISABLE=1`, `cmake -DENGINE_VERIFY_DEVICE=ON`. Without a device every device
validation prints `[SKIP]`.

Environment switches — **none of them can change a value** (see "Two families of switches"):
`ENGINE_BATCH`, `ENGINE_KSPLIT`, `ENGINE_ARENA`, `ENGINE_CSE`, `ENGINE_FUSE`, `ENGINE_LAYOUT`,
`ENGINE_DEVICE`; `ENGINE_THREADS` (default `min(hardware_concurrency, 32)`), `ENGINE_TILE_MULT`,
`ENGINE_TILE_COLS`, `ENGINE_SPIN`, `ENGINE_ELIM_BASE`; `ENGINE_CUDA_DISABLE`,
`ENGINE_CUDA_DEVICE`, `ENGINE_CUDA_GRAPH`, `ENGINE_CUDA_MERGE_LEVELS`,
`ENGINE_CUDA_PROGRAM_CACHE`, `ENGINE_CUDA_PINNED_MB`, `ENGINE_CUDA_COPY_THREADS`;
`ENGINE_TRACE_NODES`, `ENGINE_TRACE_RSS`, `ENGINE_TRACE_ELIM`, `ENGINE_TRACE_LEVELS`,
`ENGINE_TRACE_PASSES`. Also `ENGINE_BACKEND=legacy` (Phase 2/3 rollback). Since slot-14 WP-3:
`ENGINE_CUDA_ARENA_SLACK_MB` sets the idle device-arena bytes tolerated before a soft trim (default a quarter of
the device; ENGINE_API §11), and `ENGINE_TRACE_DEVICE_RELEASE=1` prints one `DEVICE_RELEASE` line per
between-validations release (`Util/DeviceRelease.h`).

#### Campaign driver (Phase 6) — `--campaign`

`./hacs --campaign <spec-file> [--output <dir>] [--dry-run] [--quiet]` turns the pipeline
into a survey instrument: it enumerates a `(n_sym, ℓ, p, r, q)` grid, groups jobs by shape
signature, runs `spec.jobs` of them concurrently (each on its own engine pool of `spec.threads`
workers) and writes one streamed JSON per job plus a campaign-level `index.json` and a
`summary.tsv`. Public API only, same code path as `--bench`. The spec is line-oriented
(`---` starts a section, `key = value`, ranges `a..b step c`); knobs are
`certify = full | sampled(...) | none` (**only** the external cross-checks — the in-process
certificates C3–C6 are never sampled), `lean`, `level_a`, `resume`, `model`, and for the ext pass
`ext`, **`ext_jobs`** (since slot-8 WP-6: that many cells at once under memory-aware LPT admission,
**`ext_memory_mb`**, default 40 000; `ext_jobs = 1` is the sequential pass; the pass prints an
`EXT_PASS` timing line, `campaign.md` §14) and **`ext_gpu = off | on | force`** / `ext_gpu_cells`
(slot-8 WP-6b: an optional device worker, **off by default, measured as no gain**) — all four
scheduling-only: no value, id or file name moves. Since slot-8 WP-5 the ext pass, the job loop and
the `--atlas` build **release the engine's program caches** above a pinned size, with `malloc_trim`
(`Campaign/ProgramCacheRelease.h`, `docs/KNOWN_ISSUES.md` §4c RESOLVED). **Since slot-9 WP-8 (C5c)**
the job loop honours `coefficient_ring = Z/ell^k` (`Campaign/CampaignRing.{h,cpp}`): a ring job
writes `hecke_ring_report/v1` ([E] `sec:ring` (g); `campaign.md` §15; `hecke_report/v2` untouched),
the Bredon object's lengths and invariant factors at `ell ∈ {2, 3}` with Hecke / Bockstein /
reduction recorded as refused, `summary.tsv` gains 15 columns and `index.json` a
`coefficient_ring` key — only under a non-default ring, so **no job id at the defaults moves**; the
ext pass under a ring and any cell with `ell^k ≥ 2^64` are refused at spec validation, by name.
Full documentation:
**`docs/matrix-engine/campaign.md`**; shipped specs and the published table:
`docs/matrix-engine/results/` (its `README.md` §7 lists the later sets: `ext_first/` (slot 7), and
from slot-10 window W2 **`ring_survey_l2/`** — the first ring campaign, `Z/ell²` over
`ell ∈ {2,3,5,7,11,13,691}`, even `n ≤ 64`, 462 jobs; `ell²`-torsion exactly at `(30,5)`, `(60,5)`,
`(56,7)`, analysed by `docs/matrix-engine/tools/ring_survey_analysis.py` — and **`ext_u691/`**, the
45 `u_ell_over_budget` `ell = 691` cells of `ext_first` recomputed with `U_691` at
`u_ell = budget_mb=8192`, `ext_jobs = 6` (216 s, 32.7 GB peak); and from slot 13 **`hida_towers/`** — the Hida
tower catalogue `hida_tower/v1` (756 rows of `HIDA_TOWER` lines plus 92 `HeckeHidaLevelEllValidation` (Hi10)
cells, all `HELD`), published 2026-09-27, owner sign-off); and from slot 15 **`congruence_census/edition3/`** — census edition 3 (`hecke_census_dataset/v2`, a sibling of edition 2: 80 293 rows, edition 2 + 77 008 at `ell = 17 … 103`, complete at 61 … 103, partial at 17 … 59 with 3064 of 7350 C1 cells missing; WP-15, owner request 2026-10-01). Gated by `CampaignSmokeValidation`,
`CampaignCertificateValidation`, `HeckeExtCampaignValidation` (arm 10 the parallel pass, arm 11 the
device worker), `ProgramCacheReleaseValidation` and `CampaignRingValidation` (slot 9, 693 checks).

#### Migration tools (`docs/matrix-engine/tools/`) — five acceptance gates

Each owns an allow-list **with a reason per entry**, and each is run inside `--all` by a validation
so it cannot rot. *Removing an entry from an allow-list is the unit of progress; adding one needs a
reason.* Full text, including the recorded migration decisions: `docs/architecture-detail.md`.

| Script | Forbids | Run by |
|---|---|---|
| `raw_mod_calls.sh` + `.allow` | raw `ModArithmetic::mod_*` call sites under `src/hacs/` **outside the allow-list** (the target is not zero — the PERMANENT section is out of scope for the whole programme). Currently **208** sites, **0 outside** (slot 5 added 3, slot 6 added 6, slot 7 none, slot 8 four, slot 9 none, slot 10 none, slot 11 none, slot 12 none, slot 13 none, slot 14 none, slot 15 none, slot 16 none — and no slot edited the allow-list). | `ConsumerMigrationValidation` (**required**) |
| `check_matrix_includes.sh` | any **DIRECT** include of a deprecated substrate header outside its allow-list — one list for `Matrix.h` (the Phase 3 exit criterion), one for `BlockFlatMatrix.h`. Direct only: `Matrix.h` stays reachable transitively through `FlatMatrix.h`, by design. | `MatrixRetirementValidation` |
| `check_console_includes.sh` | *(1)* inside `Console/Core/`, any `#include <...>` that is not a C++ standard header and any `#include "..."` that is not a `Console/Core/` file — this is what makes "`ConsoleCore` is STL-only" checkable; *(2)* any TU outside `Console/` including a console header (allow-listing `main.cpp`, `*Validation.*`, `ValidationRegistry.cpp`, the one exact path `HeckeExt/RegisterHeckeExtensionVerbs.cpp`, and — since slot-9 WP-1 / slot-10 WP-1 / slot-11 WP-1 — `Registry/Slot9/*.cpp`, `Registry/Slot10/*.cpp`, `Registry/Slot11/*.cpp`, `Registry/Slot12/*.cpp`, `Registry/Slot13/*.cpp`, `Registry/Slot14/*.cpp`, `Registry/Slot15/*.cpp`, `Registry/Slot16/*.cpp`). | `ConsoleC0Validation` |
| `check_heckeext_includes.sh` | the extension layer's one-way dependency: *(1)* no `#include` of `HeckeExt/` outside `HeckeExt/`, `Campaign/`, `Golden/`, `Bench/`, `main.cpp`, `*Validation.*`, `ValidationRegistry.cpp` (and, since slot-9 / slot-10 / slot-11 WP-1, `Registry/Slot9/*.cpp`, `Registry/Slot10/*.cpp`, `Registry/Slot11/*.cpp`, `Registry/Slot12/*.cpp`, `Registry/Slot13/*.cpp`, `Registry/Slot14/*.cpp`, `Registry/Slot15/*.cpp`, `Registry/Slot16/*.cpp`); *(2)* inside `HeckeExt/`, no `Console/`, `Cuda/`, `Engine/` or `BlockFlatMatrix.h` (one `Console/`-only exception, the verb-registration TU); *(3)* `HeckeSturmBound.*` limited to six dependency-free headers; *(4)* no `unordered_` anywhere in the layer. | `HeckeExtArchitectureValidation` |
| `label_census.sh` + `.py` + `.allow` | any `[C, <label>]` citation (C++ comments, CMake, READMEs, plans, reports) or `\HA{<label>}` in `hecke_extensions.tex` not naming a `\label` of `gl2_contract.tex`. The allow-list is **content-keyed** (`relpath\|<verbatim fragment of the source line>`), so inserting lines cannot move an entry off its site; an entry matching **zero** sites is **STALE** and fails; the retired `relpath:line` form is rejected by name. Regenerates `docs/latex/label_census.tsv` every run. At the slot-16 close (WP-18a, on `7f36871` + its documents; W1 re-read it: `LABEL_CENSUS labels_defined=629 files_scanned=1142 files_with_citations=239 sites=2781 distinct_labels_cited=269 allowed=8 unresolved=0 stale=0`, `text_verdict=OK`): **629 labels defined, 2775 citation sites in 239 of 1139 scanned files, 268 distinct labels cited, 8 allow-listed, 0 unresolved, 0 stale** — **read the text** (slot-11 lesson; the bare exit code is 1 on a failure, slot-12 WP-1) (slot 15, W1 2026-10-01: 609 labels defined, 2650 citation sites in 214 of 1056 scanned files, 255 distinct labels cited, 8 allow-listed; slot 14: 565 labels, 2563 sites in 210 of 1006 files, 247 labels; slot 13: 539 labels, 2366 sites in 201 of 905 files, 217 labels; slot 12: 502 labels, 2299 sites in 195 of 838 files, 213 labels; slot 11: 489 labels, 2296 sites in 193 of 796 files, 212 labels, 5 allowed; slot 10: 462 labels, 2088 sites in 181 of 721 files, 187 labels; slot 9: 460 labels, 1949 sites in 164 of 677 files, 179 labels; slot 8: 459 labels, 1807 sites in 152 of 613 files, 163 labels; slot 7: 429 labels, 1773 sites in 144 of 566 files, 159 labels; slot 6: 429 labels, 1761 sites in 144 of 547 files, 159 labels; slot 5: 1609 sites in 136 of 517 files, 152 labels). | `ContractCensusValidation` |

#### Console (C0 / C1a / C1b / C2a / C2b / C4 / C5) — `src/hacs/Console/`

A small, deterministic, hand-rolled CAS-style expression language (**OC script**, files `*.oc`),
specified by `docs/console/00-console-interface-plan.md` ([P] **v3.9.3**). Full prose:
`docs/architecture-detail.md`.

- **C0, `Console/Core/` (`ConsoleCore`, STL-only)** — lexer, parser, evaluator, value model (`Int`
  is overflow-checked `int64_t`; `/` is exact and errors on a remainder), the `Object` handle model
  (`declared → computed | failed`, never retried; settings snapshot taken at **creation**), the
  `Settings` layer (no RAII stack — the session re-applies every value), the `Registry` (the
  evaluator knows no verb and no type; overload resolution by arity then type, **first match in
  registration order**; explicit registration functions, never self-registering statics), printers
  and `Session`. It defines `CONSOLE_CHECK` / `CONSOLE_DEBUG_CHECK` with exactly the
  `ENGINE_CHECK` semantics, because it may not include `EngineCheck.h`.
- **C1a, `Console/Bindings/` + `Console/Core/ConsoleCli.*`** — compiled into `cohomology_app`,
  **never** into `ConsoleCore`; nine types, 68 verbs; `golden(point, object)` resolves through
  `GoldenLookup` and **refuses at a non-zero `MathSettings` fingerprint** (rule R19). `main.cpp`
  gains exactly one branch: `--console` / `-i` / `--script <f.oc> [name=value …]` / `-c '<code>'` /
  `-`, plus `--set key=value`, `--log <file>`, `--quiet` / `--verbose`. **Exit codes: 0** success,
  **1** usage / file not found / undeclared `--set` key, **2** parse error, **3** runtime error
  (every `ENGINE_CHECK` and `hecke::HeckeOverflow` included), **4** failed `assert` /
  `expect_error`, **5** `hecke::NotImplementedInThisBuild`.
- **C1b, `Console/Bindings/Decomposition.cpp` + `Presets.cpp` + `HeckeExt/RegisterHeckeExtensionVerbs.*`** —
  `Decomposition` / `Block` / `Report` types, `decompose` / `report` / `crosschecks`, the six
  `LocalSystemPresets`, and the **mathematical settings as `set` keys** (one console setting per
  `hecke::MathSettings::keys()` entry, validated through `MathSettings::set()` alone). **20**
  numbered scripts in `Console/scripts/` with frozen `.expected` transcripts; frozen pre-branch
  CLI output in `Console/scripts/cli_frozen/`. **Slot-5 WP-10** closed C1b's one deferral —
  `bernoulli_mod(w, ell)` and `glover_factors(n, ell)` are bound from the same
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (the `det`-twist convention reported is the
  pipeline's **standard-module** one) — and added scripts **017–020**, the first of C5's early
  `.oc` scripts for the E0–E2 cases. **The 16 pre-existing `.expected` files and `cli_frozen/`
  are byte-unchanged**; a new script is a new artefact, changing an existing transcript is an
  owner-gated re-baseline.
- **C2a, `Console/Bindings/EngineSettings.cpp` + `Session` + `resume` (slot-6 WP-13)** — the engine
  knobs as `set` keys (`threads`, `backend`, `device`, `batch`, `ksplit`, `arena`, `cse`, `fuse`,
  `layout`, `lean`, `program_cache`; 17 env-only knobs refused naming their variable), through a
  second settings installer; a session **restores every knob it moved** when it ends; `resume`
  refuses a changed non-budget mathematical setting and `Decomposition` is resumable;
  `canonical_field_polynomial(ell, r)` makes the exit-5 arm reachable (`field_polynomial =
  conway`). `ConsoleSettingsValidation` (fast, 179 checks); script **021** with a first-freeze
  transcript — **the 20 pre-existing `.expected` files are byte-unchanged**.
- **C2b, `Console/Bindings/Harness.cpp` + `Bench/BenchDriver.h` + `Util/Rss.h` (slot-7 WP-8)** — the
  harness verbs `validations`, `run_validation`, `bench`, `micro`, `campaign_spec` /
  `campaign_spec_text` / `campaign_plan` / `run_campaign` (a `CampaignSpec` handle type),
  `golden_subset`, `timed`, `bench_line`, `rss`, each run with the session's settings **lifted** to
  the baseline unless `inherit_settings`; times are Strings with Int micro-unit twins (the console
  has no float). The `--bench` per-mode runner is public (`bench::RunMode(ModeArgs) -> BenchRecord`,
  G4; `--bench` output byte-identical, `docs/matrix-engine/tools/bench_identity.sh`, 45 cases),
  `Util/Rss.h` (G4b), `hecke::IsDicksonExceptional` public (G9), `Hecke/HeckeLinAlg.h` (G14);
  `--log` in script mode. Script **022** (first freeze); `ConsoleDeterminismValidation`
  (`standard`, 122 checks: [P] §10 C2 (a)–(e)). **The 21 pre-existing `.expected` files and
  `cli_frozen/` are byte-unchanged.**
- **C4, hardening + documentation (slot-8 WP-10)** — `ConsoleErrorValidation` (`fast`, **107**
  checks at the slot-8 close): every [P] §8 row reaches its exit code with `file:line:col` (and the
  creation site for a lazy failure) through real script files on the `--script` path, the exit-1
  rows, a failed handle never retried, the REPL surviving every error, and **post-throw integrity**
  (after seven induced throws the same session recomputes 13 golden objects of `(10, 691)` and
  matches `golden(...)`, under `device = cpu` and `gpu`); arm (K) pins `coefficient_ring`: `Z` on a
  `set` statement exit 5, `Z/ell^2` at a pipeline verb exit 5, `--set coefficient_ring=Z` exit 1
  (exit 5 since slot-9 WP-12; *since slot-24 D6* `Z` on `set` is legal and `--set coefficient_ring=Z` runs, exit 0, while `cohomology` under it is exit 5). `ConsoleDeterminismValidation` (still **`standard`**, 531 checks at the slot-8 close,
  ≈ 20–30 s) gains C4 (a): the C1 set under `threads ∈ {1,4,16,32}` × `program_cache ∈ {on,off}` ×
  `device ∈ {cpu,hybrid,gpu}`, one digest (`0xf6ed04bbe8e6b60a`), device arms `[SKIP]` without a
  device (`CONSOLE_DETERMINISM_ARMS=threads` restricts it to the thread arms for CheckThread).
  Hardening: `bind::LazyCompute` keeps exit 5 through a lazy handle (it was exit 3). **`docs/console/console.md`
  is generated** by the binding verb `help_markdown()` ([P]'s `help --markdown`; `Console/Core/`
  stayed frozen) via `docs/console/gen_console_md.sh <binary>` (`--check` to diff; since slot-9 WP-9
  it requires the binary path) — regenerate it whenever a verb, type or setting is registered.
- **C5a, `Console/Bindings/` (slot-9 WP-12)** — E7's `ContragredientLocalSystem` / `Pairing`
  (`dual`, `pairing`, `Bindings/Duality.cpp`; every E7 golden object at `(10, 691)` reachable with a
  byte-identical hash) and E8's ring lift ([E] `sec:ring` (h)): under `coefficient_ring = Z/ell^k`,
  `ell ≥ 5`, `symmetric_power` / `cohomology` / `hecke(H, p)` (r = 1) honour the ring (lengths,
  invariant factors, K-mode, Bockstein pair, `red(q)`, `charpoly_free`, the `ladic_level` state);
  field members exit 3, every other member exit 5 (`bind::GateTypeOnRing`); nothing lifted at
  `ell ∈ {2, 3}`. **The Core batch** (owner decision 2 (ii), the two named `Console/Core/` exceptions):
  `set`-statement refusals carry `file:line:col`, and a legal but unexecutable `--set` value is exit 5
  (`ConsoleErrorValidation` (K) pin 1 → 5). Scripts **023–025**.
- **C5b, `HeckeExt/RegisterHeckeExtensionVerbs.cpp` + `HeckeExt/HeckeAlgebraInvariants` +
  `HeckeExt/HeckeExtBindingSupport` (slot-9 WP-13)** — the extension-layer bindings: `ExtRecord`
  (`ext_record(n, ell, …)`) with its `MaximalIdeal` / `HeckeAlgebra` / `LoewyProfile` /
  `ExtensionClass` / `Presentation` objects, `Atlas`, `GF` / `GFElt` (`gf_*` verbs), `Settings`
  (`settings_snapshot()`), `Involution` (`iota`), `BoundaryCohomology` (`boundary`),
  `ConeCohomology` (`cone`, `A_c(T_p)` and `h` derived from η per prime), `L_map`,
  `check_identities`, and the local-algebra verbs on any commuting family (certificate-free:
  `rad = ker Frob^e`, Berlekamp's count, Jordan–Chevalley). Every pipeline verb of the set refuses a
  non-default `coefficient_ring` (exit 5). Scripts **040–047** (040–045 the [S Stage 9] cases, 046
  `identities.oc`); `HeckeExtAlgebraInvariantsValidation` (`standard`, 404 checks).
- **C5c from the console (slot-9 WP-8 / WP-8c)** — the harness verbs reach the ring campaign job
  loop; since WP-8c `campaign_spec` / `campaign_spec_text` surface a ring refusal as exit 5
  (`ConsoleErrorValidation` arm (M); an ordinary spec error stays exit 3), and script **048**
  (`048_c5c_ring_campaign`) runs a ring campaign and pins its values against `golden(...)`.
  At the slot-9 close: **34 numbered scripts** (001–025, 040–048), every new transcript a first
  freeze; **the 22 pre-existing `.expected` files and `cli_frozen/` are byte-unchanged**;
  `ConsoleErrorValidation` 218 checks, `ConsoleScriptValidation` 346, `ConsoleDeterminismValidation`
  567 (≈ 29–32 s, its `gpu` arms now reach the per-panel programs, WP-6), C4 (a) digest
  `0xf6ed04bbe8e6b60a` unchanged.
- **C5 leftovers (slot-10 WP-12)** — **the one named `Console/Core/` exception, at two sites**
  (`Evaluator::object_member` wraps a member getter's exception: a `ConsoleError` gets the member's
  `file:line:col`, any other `std::exception` becomes `<Type>.<member> failed` with the object's
  creation site, the kind classifier deciding the code; and the core `resume` verb back-fills its
  position onto the type's resume refusal) — recorded in [P] v3.8 §2 C7 as an exception, not a
  precedent. The five structural members of a ring handle honour (`LocalSystem.n`, `.d_V`, the new
  `.coefficient_ring` — `"F_ell"` on a field handle — `HeckeOperator.p`, `.r`), pure reads; every
  other ring-handle member keeps exit 5. `run_campaign` / `campaign_plan` share one handler
  (`NotImplementedInThisBuild` → exit 5, others exit 3; no input reaches the exit-5 branch at the
  base — recorded, no test hook). `ConsoleErrorValidation` arm (W). Script **026** (first freeze).
  At the slot-10 close: **35 numbered scripts** (001–026, 040–048); **the 34 pre-existing `.expected`
  files and `cli_frozen/` are byte-unchanged**; `ConsoleErrorValidation` **294** checks,
  `ConsoleScriptValidation` **350**, `ConsoleDeterminismValidation` **570**, C4 (a) digest
  `0xf6ed04bbe8e6b60a` unchanged; `console.md` regenerated (one row).
- **Digit handles (slot-11 WP-18c; [P] v3.9)** — under `coefficient_ring = Z/ell^k` with
  `ell^k ≥ 2^64`, `ell ≥ 5`, `symmetric_power` / `cohomology` / `hecke(H, p)` run the digit route
  (`bind::GateTypeOnDigit`; the new member `Cohomology.precision`; `charpoly_free` as Strings); the
  field members (`dims`, `C`, `Z`, `B`, `H`, `P`) exit 3 as on every ring handle, other members exit 5.
  **The console's `uint32_t` gap is closed** (slot-12 WP-17, [P] v3.9.3, Q9 decided (a) by the owner
  2026-09-26): `2^32 ≤ ell^k < 2^64` (`Z/5^14 … Z/5^27`, `Z/691^4 … Z/691^6`) is served by the native
  `uint64_t` pipeline exactly as the campaign job loop serves it (`bind::GateTypeOnWide`; entries above
  `2^63` as decimal Strings); `ConsoleErrorValidation` arm (Q9) **539**, script **028** (37 scripts),
  `ConsoleScriptValidation` **358**, `ConsoleDeterminismValidation` **576**. At the slot-11 close: **35 numbered scripts**, all
  byte-unchanged (no script `027_`); `ConsoleErrorValidation` **309**, `ConsoleScriptValidation`
  **350**, `ConsoleDeterminismValidation` **570**, C4 (a) digest `0xf6ed04bbe8e6b60a` unchanged.
- **θ verbs (slot-12 WP-8; [P] v3.9.2)** — `dickson_les(n, ell)` → `DicksonLES` (lazy; `.dims`, `.ranks`,
  `.maps`, `.exact`, `.ker_equals_im`, `.certificate`, …) and `theta(H, H_up)` → Record, bound in
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (no `Console/Core/` or `Console/Bindings/` edit); `ell < 5` exit 3,
  a ring exit 5. `ConsoleErrorValidation` arm (T) → **347**; script **027** (first freeze) → **36 scripts**, the
  35 older transcripts byte-unchanged; `ConsoleScriptValidation` **354**, `ConsoleDeterminismValidation` **573**,
  C4 (a) digest unchanged.
- **`hecke_ring_algebra` (slot-16 WP-6; owner Q6 of slot 15)** — `hecke_ring_algebra(n, ell, kmax = 3)` → Record, eager, no new type, bound in
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (no `Console/Core/` edit): it binds `hecke_ext::ringalg::ComputeRingLoewyCell` (the `Z/ell^K`
  Hecke-algebra route with [C] `cor:stablecert` verdicts) and adds no mathematics; members `n, ell, kmax, primes, e_max, K_cls, K_run, blocks,
  lines` (each block a Record: `system, D, free_rank, torsion, rank_T, A1_hilbert, AK_hilbert, K_stab, eps, verdict, stable_cert, stable, cf9,
  hidden`; `lines` the `LOEWY_RING` lines byte for byte). A non-default `coefficient_ring` and `ell^kmax ≥ 2^64` (the digit route, not bound to
  the verb) exit 5; `ell < 5`, odd / zero `n`, non-prime `ell`, `kmax ∉ [2, 12]` exit 3. Script **029** (first freeze, ≈ 0.5 s) → **38 numbered
  scripts**, every older `.expected` and `cli_frozen/` byte-unchanged; `ConsoleErrorValidation` arm (HR) → **562**; `ConsoleDeterminismValidation`
  **579**; the pinned C4 (a) digest unchanged, the unpinned all-scripts digest moved; `console.md` regenerated (+1 line).

### Cohomology layer (`src/hacs/`)

One line per class — **full bullet list in `docs/architecture-detail.md`**:

- **SimplicialCohomology** — `SimplicialComplex`, `CochainComplex` (coboundary operators,
  cocycle / coboundary / cohomology bases, projectors), `CochainComplexMorphism` (induced maps,
  mapping cones), plus preset spaces (spheres, cylinder, Möbius band, projective plane).
- **LocalSystemSimplicialComplex** — a local system on `K` via `SimplexRelation` structs
  (`f(s_lhs) = M * f(s_rhs)`), wrapping a base complex with a representation dimension and
  monodromy matrices.
- **EquivariantCohomologyOnK** — `H^q_eq(K, R; L) = Z^q_eq / B^q_eq`: equivariant cochains, then
  cocycles, coboundaries and the quotient; stores the projectors to cohomology. **Since slot-8 WP-3
  also over `Z/ell^k`** (`coefficient_ring = Z/ell^<k>`, `ell ≥ 5`, E8 item 3): a module route
  (`C^q` by `kernel_module`, `H^q` by `cyclic_decomposition` in `C^q_eq` coordinates, lengths and
  invariant factors in place of dimensions, the certified `K`-mode); the field accessors throw
  there, and `HeckeOperatorOnK` follows the object's ring. **Since slot-9 WP-3 also at `ell ∈ {2, 3}`**
  (owner decision 4): under `SmallEllPolicy::Bredon` of `Hecke/CoefficientRing`, which this class
  alone passes (`SmallEllPolicyScopeValidation` guards the token), a **flat-coordinate module route**
  (`compute_cohomology_flat_module`; `C^q_eq` is not free there) reports lengths and invariant
  factors only — the Bredon object, against O7 (the tree model over the ring,
  `integral_line_probe.py --model-R`) in `HeckeBredonTreeRingValidation`; its `K`-mode and stored-basis
  accessors, `HeckeOperatorOnK` and `HeckeReduction` refuse there by name. `get_prime()` refuses a
  composite object since slot-9 WP-9 (use `ring_context()`).
- **EquivariantCochainComplexMorphismOnK** — induced maps on equivariant cohomology from
  simplicial inclusions with fiber maps between representations.
- **LocalSystemPresets** — factory functions for standard local systems on `S^1`, cylinder,
  Möbius band.
- **LocalSystemSL2Z** — the main application: triangulation of `SL(2,Z)\H`, cohomology with
  `Sym^n(F_p^2)` coefficients, restriction morphisms to the cusp `S^1`.
- **LocalSystemUtils** — `ComputeSymmetricPowerMatrix` for the induced action of a 2×2 matrix on
  `Sym^n`. Since Phase 1 the live implementation is `ComputeSymmetricPowerMatrixFM`
  (`FlatMatrix.cpp:1440`, `O(d_V^2)`); the `Matrix`-returning form is deprecated and all 24 live
  call sites were migrated. Over `Z/ell^k` it is `ComputeSymmetricPowerMatrixRing` (slot-8 WP-3,
  E8-P5: the unit recurrences, a division-free Pascal route, the `diag(ell, 1)` split for `U_ell`).

### Hecke action (`src/hacs/Hecke/`)

Integral Hecke operators (`T_p` for all primes, `U_ell` for the bad prime `p = ell`, `T_{p^r}`/`T_n`, and the diamond `T(p,p)`) on `H^q(K,R;L)`, `L = Sym^n(F_ell^2)`, for all degrees `q ∈ {0,1,2}`, on the same 7-vertex `SL(2,Z)\H` model as `LocalSystemSL2Z`. Binding mathematical contract: **`docs/latex/gl2_contract.tex`** (**v1.16.0**, released at the slot-16 close (owner O2 of 2026-10-01, WP-14's Fable referee ACCEPT WITH REPAIRS, 0 blocking, 16 / 16 repairs confirmed): `sec:levelNdegsec` (`prop:kappamodel`, `prop:degenpres`, `rmk:degenpresconv`, `rmk:levelNscale`, (LN7)–(LN9)), `sec:isomodelell` (`def:isomodelell`, `prop:isomodelell`, `prop:ellthreeclosed`, `rmk:isomodellmp`, (IL1)–(IL4)), the `sec:nebentypus` code map "built" and WP-8's verified locators; before it, **v1.15.0**, released at the slot-15 close (owner Q2 of 2026-09-30, WP-4's Fable referee ACCEPT WITH REPAIRS, 0 blocking): `sec:nebentypus` (contract first, code in slot 16) and `sec:saturation` (P15 / P17 / P18 / P20, `cor:stablecert`); before it, **v1.14.2**: v1.14.0 was the owner-signed release of 2026-09-28, slot-14 WP-13. It released `sec:levelN` unbuilt: level `N` by Shapiro, `def:cosetrepsN`, `prop:levelorbit`, `prop:heilbronn`, (LN1)–(LN6). v1.14.1 holds the audit rulings, and the v1.14.2 Z-bump flips the code map to "built" after WP-12. Before that, v1.13.0 was owner-signed 2026-09-27 at the slot-13 close — `sec:hidafull`: level `ell` by Shapiro on the fixed model, the old space, the integral stabilisation, Hida's control and weight independence as verified literature, the lattice datum, (Hi7)–(Hi12); over v1.12.x — slot 12's `sec:hida` and the Shapiro transcription (`prop:bdrytranscription`, `lem:bdrytorus`); `open:ordprecision` answered at `ell ≥ 5`, `n ≥ 1`, tag `PROVED`; cited as [C] by label; `hecke_action.tex` and `monodromy_v5.tex` are frozen inside it since v1.0.0); implementation plan of the original feature: `docs/implementation/hecke_action_implementation_plan.md`; module map (file→contract-section table, matrix-level definitions, full validation list): `Hecke/README.md`.
The modules, one line each — **full prose in `docs/architecture-detail.md`**; file→contract-section
map and the complete validation list in `src/hacs/Hecke/README.md`:

- **Exact-integer / FP-filter substrate** (`ExactInt`, `Predicates`, `QuadPoint`, in `HeckeCore`) —
  exact 2×2 integer matrices with overflow checks; certified FP64/FP32 sign predicates with exact
  fallback (disabled by `HECKE_PURE_INTEGER`). The `PredicateStats` counters are **per thread**
  since slot-8 WP-6 (the parallel ext pass; the engine's `g_stats` counters became relaxed atomics
  in the same package).
- **Coset + tau tables** (`HeckeCosetTables`, `HeckeTauTable`, `SL2ZTessellationTables`) — exact
  coset representatives / cocycles for `Γ_0(N)\Γ`, and the `g`-twisted chain datum `τ` with
  **mandatory exact certification `∂τ = τ∂` at construction**.
- **`HeckeOperatorOnK`** — the fused cochain map `Θ_g`, `Θ^{(q)}_flat` / `Θ^{(q)}_eq` and
  `A^{(q)}(T_p)`, with a second independently-bracketed route asserted bit-identical. Since slot-8
  WP-L1 (owner-approved) route 2's per-row pattern hash takes each slot's rank from a Fenwick tree
  (`O(log)`), not `std::distance` over the `ops2` map (`O(ℓ)`); keys unchanged; `U_10007` at
  `n = 0` ≈ 256 s → ≈ 9 s. Over `Z/ell^k` (slot-8 WP-3) `Θ` is built both ways and asserted equal.
  Since slot-10 WP-7 (**L4**) route 2's block rows run as host tasks on the consumer pool (per-row
  offsets into `term_slot`, an `Executor` and a Fenwick tree per row, the first failing row in σ
  order); keys and programs unchanged: `U_10007` `n = 0` route 2 1.26 → 0.25 s; T2's `(10, 691)`
  ≈ −24 %; neutral on the parallel ext pass (1-thread pools).
- **`HeckeReduction`** (slot-8 WP-4, E8 item 4a) — the reductions `Z/ell^{k+1} → Z/ell^k` on
  cohomology and the Bockstein of `0 → F_ell → Z/ell² → F_ell → 0` as **map equalities** between
  stored bases, Hecke-equivariant at `ell ≥ 5`, with `bockstein_rank^0` and
  `higher_torsion_count` (`bockstein_rank^0 + higher_torsion_count == dim H^0(F_ell)`);
  `HeckeReductionValidation` (`standard`, 68 970 checks) and `HeckeReductionCoverageSlowValidation`
  (`slow`, 3731). Since slot-9 WP-4 it also reduces and Bocksteins the boundary and the cone
  (`ReduceConeHcToField`, `ReduceConeHcBetweenLevels`, `BocksteinConeHc`, `ReductionIntertwines`).
- **`HeckeOperatorFamily`** — `T_p`, `T_{p^r}`/`T_n` (recursion **and** an independent direct
  double-coset route), `T(p,p)`, `U_ell`. Since slot-9 WP-7 (L2) `build_pipelines()` holds
  `tau_construction_mutex()` only while priming K's simplex index, so family builds of different cells
  run concurrently (`HeckeFamilyConcurrentBuildValidation`; the parallel ext pass on `sweep_full`'s
  `ell = 10007` cells 53 s → 16 s).
- **`FpPoly` / `HeckeModuleDecomposition`** — exact `F_ell[X]` arithmetic and certified primary
  decomposition; randomized factor-finding is never trusted without a deterministic certificate.
- **`HeckeReport`** — hand-rolled JSON writer (`hecke_report/v2`), all three matrix levels.
- **`HeckeCrossChecks` / `BarCocycleH1`** — the classical `α`/`β`/`ω` factorization and an
  independent bar-cocycle `H^1` route, both asserted to agree with the fused pipeline.
- **`HeckeBoundaryDatum` / `HeckeBoundaryOperator`** — the certified `Γ`-level `τ_∂` and
  `Θ^∂_g` / `T_p^∂` on the circle model.
- **`HeckePairHomotopy` / `HeckeIntegerSolve`** — the certified `η` over `Z` for every `ell`;
  `HeckeIntegerSolve` is **the one integer solver**.
- **`HeckeSettings.{h,cpp}`** — `MathSettings`, **eleven** registered keys (the eleventh,
  `coefficient_ring`, slot-8 WP-3: `F_ell | Z/ell^<k>` — **`k ≤ 4096`** since slot-11 WP-18c, beyond
  `2^64` the digit route — `Z/<m>` refused inside `set()`, `Z` stored since slot-24 D6 and honoured by the integral descent only (the record `integral_descent_record/v1`, the console verb `descent`, the campaign's descent cells; [C] `sec:recordschema` item 7), refused by name, exit 5, at every other consumer; a
  non-default ring is honoured only by `EquivariantCohomologyOnK`, `HeckeOperatorOnK`,
  `HeckeReductionValidation` and the golden harness's E8 points and **refused by name, exit 5,
  everywhere else** — [E] `sec:ring` (b)), the FNV-1a-64 fingerprint of
  the **non-default** entries (`0` at the defaults); a setter's `source` is an argument
  (`ScopedMathSettings(s, src)`, `ScopedUEll(u, src)`; the golden harness stamps `spec`). See "Two families of switches" below.
  `canonical_text()`, `to_json()` and `text(key)` are **one loop over `keys()`** built on a single
  per-key view, so **adding a key is four edits** — a member + its source, a `registry()` row, a
  `view_of` arm and a `set()` case — and a key added to the registry without a `view_of` arm
  **throws** instead of silently emitting an empty value.
- **`hecke::CertifyLocality` / `SubspaceOps`** — called inside `ComputeMultiOp`'s refinement loop:
  it splits, certifies, or emits `local = false` with a resumable state — never silently, and the
  loop never spins. `locality = strict` is implemented and byte-identical to budget mode wherever
  budget mode certifies.
- **Reach of `U_ell`** — the old `exact multiply overflow` is **RESOLVED** (`docs/KNOWN_ISSUES.md`
  §3): `QuadPointT<I>` reduces in `int64` first and widens to `__int128` only after a
  `HeckeOverflow`. **The new limit is `lem:bounds`'s own, `ell ≤ 23170`** (largest prime 23167);
  beyond it `certify()` refuses by code 51 — the designed loud failure.
  `HeckeExt/HeckeUEllBudget.h` is the frozen RSS model (`u_ell_rss/v2-2026-09-17`) behind `u_ell`.
- **`HeckeInvolution` / `HeckeExt/HeckeSignSplit`** — the **production** `ι^* := −ι^*_geo`;
  `obl:iota`(i)–(iii) discharged blockwise and exactly over `Z` in `compute()`, which **aborts** on
  failure; the `±` split stored on every `C/Z/B/H^q_eq` at `2 ∈ R^×`. Since slot-5 WP-12a the
  rider of `obl:iota`(ii) is discharged by an **emitted record** as well as by the certificate:
  `hecke_ext/v2`'s `iota_exact_comparison` says whether the exact `Mat22` comparison ran and on
  which relation rows. Since slot-10 WP-7 (**I-1**) `obl:iota`(iii)'s carry / H-level checks and
  `prop:iotasplit`'s splits run as host tasks in the serial order (first failure in task order):
  `(160, 691)`'s sign split 1.80 → 0.79 s, every stored object computed by the same code.
- **`EquivariantMappingCone` / `SL2ZBoundaryPair` / `HeckeConeAction`** — `Cone(r)` with its long
  exact sequence and `A_c^{(q)}`, both with re-deriving certificates. **Over `Z/ell^k`, `ell ≥ 5`,
  since slot-9 WP-4 (E8 item 4b)** a dense module route beside the tape route, selected by the ring:
  `ModuleConeT` (`EquivariantMappingConeModule.cpp`; `ConeModuleCertificate` item 14 discharges
  `obl:coneexact`(iv)'s non-field half by solves), `ModuleConeActionT` (**route 1 only**) and
  `HeckeBoundaryOperatorT`. **Since slot-10 WP-3 both cross-routes honour the ring** at `ell ≥ 5`,
  `ell^k < 2^32` (the uint32 regime rule: above `2^32` they refuse by the ring context's named
  refusal; at `ell ∈ {2, 3}` all three members refuse by name): `HeckeConeStrictPairRoute` (`Θ^s`
  by `HeckeOperatorOnK`'s module route on the `BoundaryStrict` table, `η^s = 0`, `A^s_c` by route 1)
  and `HeckeConeRelativeRoute` on the relative sub-complex constructor's **module route** (no inverse
  over the ring: `M` and an explicit `N`, `M N = N M = I`, then `M A' N`) give `A_c` entrywise equal
  to route 1's at the seven E8 points (`HeckeConeCrossRouteRingValidation`, 431 checks).
  **E8 is complete: `obl:coneexact`(vii) sentences 1–2 discharged over the ring; sentence 3 (the PD
  adjointness gate) recorded unavailable there** — the pairing and the contragredient refuse a
  composite ring. Since slot-5 WP-5 the cone's
  `Z / B / H / P` and the certificate's span inclusions run on the **tape**, and
  **[X] §6.2 E5 acceptance (d) — restated by the owner on 2026-09-22 as `M_cone ≤ 2.0 · M_base`
  with the numerator the cone object alone and the denominator `--bench hecke 256 … --repeat 1`
  — is MET**: 1.90–1.95×, median 1.93×, over five interleaved rounds (it was 2.17–2.19× before).
  Since slot-5 WP-4 `ConeCertificate` item 11 evaluates the first `eq:conedims` identity under its
  own minimal guard and `obl:coneexact`(iii)'s `r`-half is asserted at **every** `ell`; since
  slot-5 WP-12a `hecke_cone_action/v1` reports `restriction_equivariance_asserted` from the
  assertion the run actually performs, and certificate item 12 refuses a record that says
  otherwise. **Since slot 6 `obl:coneexact`(vii) is implemented in all three sentences**: the
  strict-pair route (`HeckeConeStrictPairRoute`, `TauVertexPolicy::BoundaryStrict`, WP-4) and
  route 3 (`HeckeConeRelativeRoute` on `EquivariantCohomologyOnK`'s relative sub-complex
  constructor, WP-5) each give `A_c` entrywise equal on 212 / 212 operators, and the PD gate for
  `X_3` is asserted (WP-3, below). `docs/matrix-engine/tools/cone_output_diff.sh` proves a cone
  change value-preserving.
- **`Hecke/HeckeContragredient` / `Hecke/HeckePairing`** (slot 6, WP-1 / WP-3, phase E7) — the
  contragredient `ρ_n^∨ = ρ_n(adj ·)^T` (`Mat22::adj`, `ComputeContragredientPowerMatrixFM`, the
  contragredient relation list, `HeckeOperatorOnK`'s `FibreRepresentation` argument, default
  `SymN` byte for byte the old operator), `Φ_n` and `A(D_n)(T_p)^q` with the intertwining asserted
  **untwisted**; the cone-level and circle pairings, perfectness and the **PD adjointness gate**
  `A_c^T G = G A(D_n)` — a test of [C] `cl:pd`, which stays OPEN. `HeckeDualityValidation`.
  **E7 is accepted since slot 7** (WP-1): `cl:pd`(1)–(2) tested on all 54 cells of the E2 case list
  at `ell ≥ 5` (arm A16, `HeckeDualityCoverageSlowValidation`), failing on none; its objects are
  golden (the 651-entry add-only emission).
- **`Hecke/LadicCell`** (slot-11 WP-18c) — **the digit pipeline route**, taken exactly when
  `ell^k ≥ 2^64`, `ell ≥ 5` (every `ell^k < 2^64` keeps the shipped route bit for bit): `e_max` from the
  shipped word-size `K`-mode (escalated once; uncertified → `PrecisionInsufficient`, exit 5, resumable
  state `ladic_precision`), the **per-cell certified precision bound `K = k + e_max`**, the cohomology over
  `Z/ell^K` in digit planes, `Θ_g` both routes, `A^{(q)}`, the free charpoly to precision `k`, and at
  `p = ell` the **ordinary idempotent** (`e = −p_0^{-1} W s(W)`, Fitting, four certificates; [C]
  `def:ordinary`). `ENGINE_LADIC_WIDTH` picks the digit width without moving a value. Caps: grammar
  `k ≤ 4096`, `K⌈log₂ ell⌉ ≤ 8192` and a predicted working set ≤ 40 GB checked at `k + K_w − 1`; `ell ≥ 2^31`,
  `n` odd / 0, and `ell ∈ {2, 3}` beyond `2^64` refused by name. Campaign digit jobs (`route`,
  `precision`, textual `modulus`, `hida`) and console digit handles. `HeckeLadicCellValidation`
  (897 checks, arm (L) added by slot-27 L691: the M-0 charpoly at `(10, 691)` beyond `2^127`, O5, UCT, cross-width, truncation, native
  `u128`, the bound at `e_max > 0`).
- **`Hecke/HeckeOrdinaryPart`** (slot-12 WP-4; [C] `sec:hida`) — `hecke::ordinary`: the torsion pre-pass
  `TorsionExponentPrepass(n, ell)` (`e_max`, lengths `λ_e`, the torsion multiset from `J_n = [ρ_n(S) − 1; ρ_n(T) − 1]`
  over `Z/ell^e`, no cochain complex; every prime, `n ≥ 1`), `CertifiedWorkingPrecision` (`K = e' + e_max`, `ell ≥ 5`
  only, refusal naming `prop:torsionprepass(6)`), `OrdinaryExponent` (`N_ord(g, K)` kept as factors, never
  materialised), `OrdinaryProjector` (`U^{N_ord}`); `LadicCell` gains an **opt-in** `precision_source = prepass`
  (default route byte-identical). `HeckeOrdinaryPrecisionValidation` (916): (Hi1) pre-pass `e_max` = K-mode's,
  (Hi2) `U^{N_ord}` = WP-18c's idempotent. Since slot-13 WP-5 the pre-pass runs beyond `2^64` by `engine::ladic`
  (`PrepassRoute::Auto`; `ell ≥ 2^31` there refused by name).
- **`Hecke/HeckeLowRank.h`** — **the `U_ell` memory lever** (slot-13 WP-4, **default-on (`Auto`) since slot-14 Q8**, opt-out `HECKE_U_ELL_LOW_RANK=0`, value-preserving; audit repairs
  WP-14): `HeckeOperatorOptions::ScopedUEllLowRank` (thread-local, no fingerprint — it cannot change a value; refused
  unless `ell | N` and the fibre is `SymN`) stores the `ρ_n` of singular-mod-`ell` blocks (τ pool, fused blocks, route
  2, the module route) as `U V` factors of rank `≤ min(k, n + 1)`, the rank claim `ENGINE_CHECK`ed per block;
  `--bench … --u-ell-low-rank` (`u_ell_low_rank=1` on the `BENCH` line only when set). ≈ **5× smaller, ≈ 1.8× faster**
  (`(128, 691)` 2745 → 574 MB). The floor it left, the coset tables' full-rank `ρ_n` (34 B / entry / coset), was
  removed by slot-14 WP-10's streaming (next bullet). The frozen `u_ell` model is not re-fitted (audit Q-D, an owner
  decision: a re-fit is a value change). `HeckeUEllLowRankValidation` (344; arm (F) the legacy arm, S13 WP-16; arm (G) the contragredient fibre over a factored τ pool on the legacy arm, `c0566e2`).
- **`Hecke/HeckeLevelEll`** (slot-13 WP-6; [C] `sec:hidafull`) — `hecke::level`: **`Γ_0(ell)` on the fixed model by
  Shapiro** — one routine for `eq:levelcorr` (`U_ell^{(ell)}`, `dg_ell`, `T_p^{(ell)}`, `T_ell`, and the fibre maps
  `dg_1`, `ω`) reading only the level-1 τ-table, the second model route `eq:Ulevellmodel`, block cochain maps applied
  without a `D_N × D_N` matrix, the induced relations over `Z/ell^k`; pipeline-free, value-free, with general-`N` plug
  points. `HeckeHidaLevelEllValidation` (2906, ≈ 42 s): against an **independent group-cocycle route**, the old space
  as cochain maps, the stabilisation `(e_ell ∘ dg_ell, c_st^{-1} ω)` mod `ell^{1,2,3}`, (Hi10) on 92 cells.
- **The slot-14 `U_ell` levers** (WP-10, G0; **default-on since the owner's Q8**, 2026-09-28; value-preserving, no
  fingerprint). *Coset streaming* (`HeckeOperatorOptions::ScopedCosetStreaming`, `HECKE_COSET_STREAM=0`): of the ten
  `ρ_n` tables of `HeckeCosetTables` the `U_ell` pipeline reads one. Streaming stores none of them and evaluates the
  `*_block()` accessors (`CosetRhoT`, `HeckeTauTable::rho_pool_block`) on demand. *The serial phase on the pool*
  (`ScopedParallelSetup`, `HECKE_PARALLEL_SETUP=0`) runs the coset-table and τ-table setup on the consumer pool above
  `items · work ≥ 2^22`. *G0's rank-one closed form* (`lowrank::rank_one_rho_factors`, `ScopedRankOneClosedForm`,
  `HECKE_RANK1_CLOSED_FORM=0`) gives `ρ_n` of a singular-mod-`ell` key over `F_ell` directly as `U V`. G0 also adds
  one host fan-out budget, `HeckeOperatorOptions::for_each_index`, accounted per consumer pool. Measured: `(384, 2411)`
  13.7 GB / 62.8 s → 1.5 GB / 13.9 s (WP-10) → 3.9 s (G0); `(700, 691)` 13.7 GB / 60.8 s → 2.2 GB / 15.9 s → 8.4 s.
  `HeckeUEllStreamValidation` (`standard`, 2262) proves every lever combination equal to the all-off path.
  `--bench` flags: `docs/performance-reference.md`.
- **`Hecke/HeckeLevelN`** (slot-14 WP-12, gated, owner Q4 2026-09-29; [C] v1.14.2 `sec:levelN`) — **level `N` on
  the fixed model by Shapiro**, which extends slot-13's three general-`N` plug points. `Gamma0LevelN` is the
  `def:cosetrepsN` table for every `N < 2^31` (CRT of the prime-power components, the first applicable case
  (i)/(ii)/(iii)). `Gamma0SubTransversalN` gives `r_t`. `InducedRelationsLevel` works over any `CosetLevel` and any
  `ModCtx`, with `M_A(γ)` kept monomial. `OrbitWiseFixedSpace` implements `prop:levelorbit`(1) with no solve on free
  orbits, and `CokernelFromFixedSpaces` gives `h^0`, `h^1`. `T_p^{(N)}` (`p ∤ N`) and `U_p^{(N)}` (`p | N`) come from the
  shipped `BuildLevelCorrespondence`, over `F_ell` with `ell | N` or `ell ∤ N`, and over `Z/ell^k`. The Heilbronn–Merel action and the sparse route
  followed in slot 15 (next bullet). `HeckeLevelNValidation` (`standard`, 1665,
  ≈ 4 s) checks it against an independent group-cocycle route, classical charpolys, the `N = ell` plug-point
  regression and (R3), Mazur's Eisenstein ideal on 26 cells (`HECKE_LEVEL_N_R3_CELLS`).
- **Level `N` at scale (slot 15)** — `Hecke/HeckeLevelNHeilbronn` (WP-7: Merel's `H_{N,p}` on the cokernel presentation, (LN3)
  on both halves; `HeckeLevelNHeilbronnValidation`, 636), `Hecke/HeckeLevelNSparse` (WP-8: the sparse cokernel of
  `rmk:levelcost`(4), entrywise = dense, the cost model, `α^0` / `ω` on the presentation, `α_d` at composite `N` on the model;
  `p ∈ {2, 3}` refused by name; `HeckeLevelNSparseValidation`, 1229), `Hecke/HeckeLevelNR3` (WP-9: R3 over Merel's candidates
  `N ≤ 10^4`, 1881 cells, `docs/implementation/slot15/WP-9_r3.tsv`; `HeckeLevelNValidation` 1871). [C] v1.15.0 records them (its `sec:levelN` scope sentence on `α_d`, added at pre.3, is released unrefereed — replaced at v1.16.0 by the refereed `sec:levelNdegsec`).
  Slot-16 WP-2 added arm (R3m) to `HeckeLevelNValidation` (the model route against the dense presentation, basis-free; **1883** checks).
- **`Hecke/HeckeLevelNDegen`** (slot-16 WP-13 + WP-17 repairs; [C] v1.16.0 `sec:levelNdegsec`) — **`κ_N` as code** (`prop:kappamodel`:
  `KappaModelPoints` finds the edge `e46 = {v4, v6}` by its vertex set and checks its orientation in the real complex; `κ^mod(f) = −f(e46)`)
  and **`α_d` on the cokernel presentation** (`prop:degenpres`, `eq:degenpres`: `DegeneracyOperator` holds `D_{M,N,d}` as block terms over any
  word-sized ring, two enumerations (per-`ε` buckets and a full scan) that must agree on the term multiset, every block self-checked in
  `__int128`; `rmk:degenpresconv`'s two traps exist only as negative controls). `ReadEisensteinR3k` (`HeckeLevelNSparse`) is the (LN9)
  `R3_k` reading; `HeilbronnOperator` gained an `__int128` fallback where the int64 triple product overflows (first at `N = 30030`, `p = 17`;
  value-preserving, `ScopedForceWideHeilbronn` proves it term for term). Arms in `HeckeLevelNSparseValidation` (no new name; **1798** checks):
  (K) (LN7) 17 cells, (A) (LN8) 43 cells (40 against the model) + traps, (W) the trace incl. `U_p` at `d = p | M` (12 cells), (L9) reported,
  (G) `α_d` at scale, (F1) the wide path. **Largest `N` reached: 30030** at `k = 4` (`D_N = 290 304`, 3.14 GB). **Carry (F-1):** the
  level-`N` table's int64 cocycles overflow at composite `N ≈ 5.5·10^4` (a loud `HeckeOverflow`, never a wrong value); `__int128` / residue-only
  cocycles are a slot-17 item. Hooks `HECKE_LEVEL_N_DEGEN_CELLS`, `HECKE_LEVEL_N_R3K_CELLS`.
- **`Hecke/HeckeNebentypus`** (slot-16 WP-10, WP-11 + audit repairs; [C] v1.16.0 `sec:nebentypus` "built"; the convention pinned first in Lean,
  [GT] `conv:nebentypus`, Fable-audited) — `hecke::neb`: `Fq` / `FqMat` (characteristic-`ell` fields `F_{ell^d}` from `C_{ell,d}` passed as data
  and certified irreducible — `Hecke/` may not include `HeckeExt/`), `GaloisRing` + Teichmüller lift (`W_K(F_q)`), `DirichletCharacter` (Conrey
  labels, LMFDB's generator rule), `ReduceCharacter` (`e(1/o) ↦` the least element of order `o`), the character model as a cokernel
  (`TwistedMonomialOf`, `NebCokernel`, `HeilbronnChi`, `HeilbronnChi::Central` for `T(p,p) = χ(p)p^n`) and on the fixed model
  (`InducedRelationsChi`, `BuildLevelCorrespondenceChi`: every block carries `χ(a_δ)`, `ENGINE_CHECK`ed in `Δ_0(N)`), `Gamma1LevelN` /
  `DiamondOnModel` (`⟨d⟩ = χ(d)`). **No new `FibreRepresentation` value** (the level-`N` routes bypass `HeckeOperatorOnK`). `HeckeNebentypusValidation`
  (`standard`, **2434** checks, ≈ 41 s): (NB1) on 1668 cells, (NB2) bit for bit at `χ = 1`, (NB3) on 79 cells (132 under `NB3_FULL`), (NB5) 94 real
  rows + **20 / 20 non-real distinguishing cases read `[psi]`** (the χ / χ̄ dictionary observed as [GT] states it), (NB6) 377 / 377, (C) three
  independent routes, (X4) **(NB4)'s sharp form at `n = 0` held on 132 / 132** (`Sym^i` untwisted), (M2) `m = 2` and `H^1_m ≅ A_W²` on the
  non-ordinary dihedral blocks `(72, 47)`, `(118, 47)`, `(156, 103)`, the F1 hidden blocks `(220, 17)`, `(246, 19)` with `Λ_m ≇ T_m²` for the full
  Hecke algebra. **Not built (carries):** the dense cap `D = m_N(n+1) ≤ 4096` (no sparse route with a character), `T_{p^ν}` for `ν ≥ 2`
  (`thm:nebrelations`(2) untested), Galois-ring cohomology at `d ≥ 2`. Hooks `HECKE_NEBENTYPUS_CELLS`, `_F1_RING`, `_F1_PMAX`, `_NB3_FULL`.
- **`Hecke/HeckeTauDumpValidation`** (slot-16 L16-4; `fast`; Lean Q14) — the env-interlocked scratch dump (`HECKE_DUMP_TAU`) of the `p = 2`
  τ table and three `ρ_n` sets that the Lean checkers `tauP2_spec` / `rho_golden_cells` verify by kernel `decide`; `[SKIP]` without the variable.
- **`RhoMemo.h`** — the one `ρ_n` memo type (`hecke::RhoMemoT`, slot-5 WP-6): a `std::map` keyed
  on `(j, γ)` plus an `ENGINE_CHECK`ed identity stamp for the `(coset table, ell, n_sym)` the key
  is relative to. The three matrix-free apply routines take a caller-owned table; the
  one-argument overloads keep creating a fresh one, so external callers see the pre-package path.
  Worth **−43 %** on the cone action's `n = 256` build for ~3 MB.

The code-level fix of a bug in `monodromy_v5.tex` §12 (the proposed conjugation map `β` is not a morphism of local systems, by a Schur/scalar argument — see the erratum at the head of that section) is `EquivariantCochainComplexMorphismOnK`'s generalization from a single constant fiber matrix to per-simplex sparse block rows (`FiberBlockTable`); the legacy single-matrix constructor is unchanged and still produces byte-identical results.

### Hecke extensions layer (`src/hacs/HeckeExt/`, `namespace hecke_ext`)

The extension stage's own layer (branch `hecke-extensions`), **binding plan
`docs/implementation/hecke_extensions_implementation_plan.md` v1.20.2** ([X]; mathematics in
`docs/latex/hecke_extensions.tex` **v1.16.1** (v1.16.0 released 2026-10-01; 1.16.1 a patch: census edition 3 in `sec:census`) ([E]; v1.14.0 was owner-released 2026-09-27 from v1.14.0-pre.3, no further
edit: `hecke_ext/v5`'s `boundary_data`, `verify()` code 32, the `\CONJ` Prediction `pr:latticesplit`) — its `sec:ring` specifies `coefficient_ring`, the
refusal rule and the E8 objects; the contract is [C] above). Compiled straight into
`cohomology_app`, not into a static library, so its one-way dependency (`HeckeExt → Hecke`, never
the reverse; no `Console/`, no `Cuda/`, no `Engine/`, no `BlockFlatMatrix.h`; no `unordered_`)
is enforced by `check_heckeext_includes.sh` (see "Migration tools"). `MatrixT<uint32_t>` for
everything in it (`D ≤ ~200`), and **`namespace hecke_ext` throughout** since slot-2 WP-5
(`HeckeIdentityCertificate` moved from `heckeext`; the name is in no emitted text). Slot 1
shipped two units, slot 2 three more, slot 3 two more, slot 4 seven more, slot 5 five more,
**slot 6 two more** (at the end of this list):
The units, one line each — **full prose in `docs/architecture-detail.md`**: `HeckeSturmBound`
(the computed Sturm bound `B'(k, ell)`, pipeline-free; the first implementation of the
**resumable-state contract** [X] §1.3.1 R3), `HeckeIdentityCertificate`, `HeckeLocalAlgebra`
(`A_S` + generation certificate (a)), `HeckeGenerationCertificates` ((b), the socle bound, the
resumable `CommutantState`), `HeckeBoundary` (`H^1_! = ker r^1`, the joint eigenspace, Harder's
criterion, the split), `HeckeSturmSweep` ((c) on real blocks), `HeckeUEllBudget.h`,
`HeckeExtRecord.h` + `HeckeExtReport` (the record `hecke_ext/v1` — a **separate writer** from
`hecke_report/v2`), `HeckeExtFinal.h` (the one tri-state `Final`), `HeckeExtDriver` (Stages 1–5
for one cell), `HeckeSignSplit`, `HeckePredictions` (`bernoulli_mod`, `kummer_divides`),
`GloverFactors`, `RegisterHeckeExtensionVerbs`, `HeckeCanonicalField` (slot 5, WP-7 — the
project-canonical split field `F_ell[Y]/(C_{ell,r})` of [X] §2.2 Stage 6, pipeline-free, with
**no report consumer in this slot**), `HeckeExtComplexRecords` (slot 5, WP-1 — the one translation
layer between the E3 / E4b / E5 objects and the record), `HeckeExtGoldenObject.h` (slot 5, WP-3 —
the one definition of the layer's golden-collector POD, previously duplicated in `HeckeBoundary.h`
and `HeckeSignSplit.h`), `HeckeDicksonMultiplication` and `HeckeM1Table` (slot 5, WP-8 —
multiplication by the Dickson invariant `L = x^ell y − x y^ell` with its certificate, discharging
E1 identity class 5, and the one definition of an M1 row). **The record is `hecke_ext/v2` since
slot-5 WP-1**: the `u_ell` verdict is the **cell's**, with one `resumable` where v1 emitted one per
ideal; an ideal carries its `sign` and a `groups` list naming the ambient groups Stage 2 matched it
across; the `boundary` and `pair` complexes are computed objects with `les_maps` and the two
recorded cone flags (`phi_flat_identity` / `residual_flat_zero`, reserved in v1, **emitted** in v2).
`hecke_report/v2` is untouched — the two writers stay separate. **Slot 6**: `HeckePresentation`
(WP-2 — generators and a minimal relation set of a certified-local block with a re-deriving
`verify()`, reached through `ExtDriverOptions::with_presentation`, **no settings key and no
record key**) and `HeckeAtlas` (WP-8 — `Σ(ell)` for `ell ≤ 13`, `S_sep`, the write-gated
`hecke_atlas/v1` store, the canonical split field's first consumer); `HeckeIdentityCertificate`
gained **item 6** (the residue-atlas identity under `cl:glover`'s standard-module convention, the
contragredient reading its negative control, WP-9) and **item 7** (socle ↔ Loewy, WP-3);
`ExtDriverOptions::s_sep` is opt-in; the campaign's ext record file carries an `_x<16 hex>` ext
tag (WP-6). **The record text did not move in slot 6**: its 62 `ext_json_*` golden lines are
frozen until slot 7's staged re-baseline. **Slot 7**: the record is **`hecke_ext/v3`** — the
cell-local `proof_range` decided over the anemic pool `{q ≤ 31} \ {ell}` at every `ell`, `s_sep`
and the atlas `label` from an **in-process** `Σ(ell)` at `ell ∈ {5, 7, 11, 13}`
(`atlas_unavailable` elsewhere), the canonical `split` of every local ideal (inside `run()`, timed
as `canonical_field_s`), `predictions_mode` / `predictions` / per-ideal `predicted` / `confirmed` /
`unpredicted`, and the `presentation` object under `presentation = on` (WP-2, WP-3);
`HeckeCanonicalField`'s root finder evaluates the splitting polynomial through a precomputed
Frobenius (≈ 12× fewer `F_ell` multiplications at `r = 19`, every value byte-identical) and routes
`field_polynomial` through the setting (WP-4); `HeckeAtlas` reaches `ell = 691` (`Σ(691)`: 1 002 225
systems, built outside the suite by `hacs --atlas`, `HeckeAtlasCli`, driven by
`docs/matrix-engine/tools/atlas_build.sh`) and `HeckeTangentPair` computes the per-`ρ̄` tangent pairs
(WP-5); `--bench ext --campaign-cell` times the campaign cell's own computation (WP-6). **E6 and E7
are accepted; the first ext campaign is published** (`docs/matrix-engine/results/ext_first/`, 505
cells; `docs/matrix-engine/tools/ext_compare.py` writes its `analysis.txt`). **Slot 8** added no
`HeckeExt/` unit: the layer gained `coefficient_ring` refusals (WP-3), the `--atlas` build's
`between_cells` hook (WP-5; the engine's program caches are released between cells,
`docs/KNOWN_ISSUES.md` §4c RESOLVED), and `resume_u_ell`'s `source = spec` in the campaign (WP-11b,
§4d RESOLVED). **Slot 9** added two console-free units for C5b (WP-13): `HeckeAlgebraInvariants`
(the local-algebra invariants of any commuting family over `F_ell`, certificate-free) and
`HeckeExtBindingSupport` (the bindings' pipeline plumbing); `HeckeExtDriver` stays `F_ell`-only.
**Slot 11** added three units. `HeckeDicksonTheta` (WP-5): `hecke_ext::DicksonThetaCell` — **θ** ([C]
Part VII, `sec:dicksontheta`): the short exact sequence `0 → Sym^n ⊗ det → Sym^{n+ell+1} → Q_n → 0` on
the model (`Q_n` = `FibreRepresentation::QuotientL`, [C] `def:Qn`'s fixed basis, `ρ_{Q_n}` for every 2×2
matrix; its own `HeckeOperatorOnK` program-cache tag), the six terms and five maps in the stored bases,
`δ` by the snake construction, exactness at all six spots as subspaces, `H^0` = the Dickson ring
`F_ell[L, D]`; `ell < 5` is refused as a precondition (`ENGINE_CHECK_MSG` naming `lem:h2torsion`, exit 3,
since slot-11 WP-17), a non-default ring by name. `HeckeDicksonThetaHecke` (WP-6): the Hecke operators on
the three terms — `T_p θ = p θ T_p`, `U_ell θ = 0`, `ker θ = im δ` the Eisenstein line, `U_ell` on `H^0`
as [C] `prop:heckeH0` (non-zero only at `(120, 5)` in the grid), the (C3)–(C9) instances against
`Σ(ell)`, the θ-image column. `HeckeCensusSplit` (WP-7): per `H^1` ideal the computed boundary split
(`rank r^1` on the block → `eisenstein` / `cuspidal` / `mixed`), the `±` content and identity 6's Glover
reconciliation, one `CENSUS_SPLIT` line each; the catalogue is built by
`docs/matrix-engine/tools/congruence_census.py` into `results/congruence_census/` (edition 1, owner-signed;
the W2 data set `hecke_census_dataset/v1`; edition 2 below).
**Slot 12** added three units. `HeckeHidaTower` (WP-5): the first Hida weight towers ([C] `def:hidatower`) —
per cell `H_K` at `K = 2 + e_max` by the shipped module route, the ordinary part (`U^{N_ord}`) read on `H_{e'}` and
on the free block, `χ^ord(T_2)`, `χ^ord(T_3)`; `HeckeHidaTowerValidation` (5222) / `…SlowValidation` (`slow`,
11 722): (Hi2)–(Hi6) held, incl. `(10, 2411)` non-ordinary over `Z/2411^{1,2,3}`. `HeckeCensusCellList` (WP-6): the
census cell list behind `HECKE_CENSUS_SPLIT_CELLS` / `HECKE_THETA_IMAGE_CELLS`; census **edition 2** (3285 rows,
+ `ext_census_l7l11`) **published, owner-signed 2026-09-26** in `results/congruence_census/edition2/`, its finality
columns under `hecke_ext/v4` — every row final (S12-census2, `docs/implementation/slot12/census2_report.md`).
`HeckeFormsHeckeAlgebra` (WP-7, WP-12): the forms-side `T_m/ell` on `S_k` and `M_k` from `q`-expansions (the [EX]
`RCOMP` datum at `(82, 7)`, `(142, 7)` reproduced; on 655 census rows `A = T_m/ell` 309, a proper quotient 345);
`HeckeFormsHeckeAlgebraValidation` (163) and `HeckeBoundaryFinalityValidation` (WP-14, 13 332: Lemma B′ on the
boundary operators). **S12-FIN** (post-close, owner-approved 2026-09-26) landed the finality certificates of
`docs/implementation/slot12/WP-12_finality_proposal.md` v2: `HeckeFinalityRoutes` — (d0) "dickson" ([C]
`prop:heckeH0`(1)) on `X_1`, (d1) "boundary" ([C] `prop:bdrytranscription`, `lem:bdrytorus`) on `X_4` — run by
`HeckeExtDriver` only where (a)–(c) fail; the record is **`hecke_ext/v4`** (`certificate_routes.d0` / `.d1`,
`boundary_reps`, certificate names `dickson` / `boundary`, `verify()` 30–31; [E] v1.13.0 `cert:dickson`,
`cert:boundary`; since the Fable audit, [E] v1.13.1, (d1)'s representative stream is capped at 4 × the `u_ell`
budget by the frozen `u_ell` RSS model — over it `d1 = not_run:budget`, e.g. every `ell = 691` / `10007` cell); every `sturm_heuristic` census row at `ell ≤ 13` becomes `final = true` in production;
`HeckeBoundaryFinalityValidation` compares the driver's routes with its independent computation
(`docs/implementation/slot12/FIN_report.md`).
**Slot 13** made the record **`hecke_ext/v5`** (WP-7, owner Q3, FIN_audit G2): per ideal `boundary_data =
{rank_r1, r1, t}` iff (d1) passed, and `verify()` code 32 re-derives (d1)'s (H1), (H2) from the record; the ext
record sets were re-emitted under it and **published** as siblings (WP-8, `9526242`: `ext_first_v5`,
`ext_census_l7l11_v5`, `ext_u691_v5`; `EDITION2_NATIVE rows=3285 identical=3285`). `HeckeHidaTower` part 2 (WP-5):
towers mod `ell³`, `T_5` / `T_7`, the lattice datum (`def:hidalattice`) on `Sym^n` and on Hida's lattice (the
`FibreRepresentation::HidaLatticeH` fibre), (Hi8)'s decision procedure (`DecideIsomorphic`), `D_*`;
`HeckeHidaControlValidation` (1134). New units: `HeckeCensusLattice` (WP-9: C-F9, `m_A² = 0`, held on 654 / 654
census rows; `HeckeCensusLatticeValidation`, 69), `HeckeHidaHeavyCellProbe` (WP-10: `(700, 691)` over `F_691` and
`Z/691²`, (Hi11) held; `slow`, interlocked), and two validation-only units of the `mixed` finality proposal (WP-11,
Proposition M, refereed, not landed): `HeckeMixedFinalityValidation` (`slow`) and `HeckeBocksteinCuspValidation`
(`fast`, 1447: (H4′) certified cell by cell).
**Slot 14** added one unit, `HeckeRingHeckeAlgebra` (WP-6, `hecke_ext::ringalg`, console-free; the owner's Q13: C++,
validation and env hook only). It is the **`Z/ell^K` Hecke-algebra route** (route R1 of the Loewy note [M1]).
`RunModule` computes `H^1(Γ; Sym^n Z/ell^K)` and `T_p` by the shipped module route, on `uint32_t` while
`ell^K < 2^32` and on `uint64_t` above; `ell^K ≥ 2^64` is refused by name. The joint `F_ell`-rational systems `m`
give `e_m` over `Z/ell^K` (Newton-lifted, `e² = e` and `e T_p = T_p e` checked exactly). The block `e_m M` is read by
the cyclic-summand rule. From it the route reads `A_K`, its length, the Hilbert function of `A_K ⊗ F_ell`, the free
part of a torsion block on `ell^t`-scaled generators, and the `stable` verdict at `dim A_K/ell = ⌈f/2⌉`. That verdict
is a reading, not a certificate: it rests on [M1] Prop. 1, which is not yet a [C] statement (P15 / P17, slot 15).
Its validation is `HeckeRingLoewyValidation` (`standard`, 123; `HECKE_RING_LOEWY_CELLS`). The record, golden and
settings are untouched. [E] v1.15.1-pre.2 `sec:ring` carries its text. Slot 14 made **no record, schema or golden
change**. WP-14c's C++ (`HeckeHidaComponents`) is deferred to slot 15.
**Slot 15**: `HeckeHidaComponents` (WP-6: bignum-free `B_k/k mod ell^K`, the [U] (U1)–(U3) readings;
`HeckeHidaComponentsValidation`, 157); the `stable` verdict is now a **certificate** citing [C] `cor:stablecert`, and
`ell^K ≥ 2^64` runs on the digit route (WP-5; `HeckeRingLoewyValidation` 181, [E] 1.15.1-pre.6); the forms side gates F9
torsion-corrected (WP-20). No record, schema, golden or settings change. **Contract at the close** ([C] v1.15.0):
`sec:saturation` (P15 `prop:saturation`, P17 `prop:satdefect`, `lem:heckerankone`, `lem:freepart`, `cor:stablecert` — what the
certificate cites —, `prop:cohforms`, P18 `prop:hidaalgconst`, P20 `rmk:thetaforms`) and `sec:nebentypus` (`Γ_1(N)` and
`(Γ_0(N), χ)` for every `N`, `χ` into `F_q^×`, by Shapiro with a character on the fixed model; **not built — slot 16**).
WP-12 / WP-13 refuted [E] `pr:latticesplit` as stated: C-F9 fails at `(654, 37)` ideal 8 (Loewy 4).
**Slot 16** added three units, all console-free and validation / hook only (no record, schema, golden, setting or verb change):
`HeckeSaturationDefect` (WP-5 + audit repairs, `hecke_ext::satdefect`; the owner-approved Tor package): per torsion-free block
`I_m = Tor_1^{Z_ell}(T^sat/T_m, F_ell) = ker(T_m/ell → End(Λ_m/ell))` by two routes (R-ker at the first stable `K`, R-len `ε_1 = rank_T − dim A_1`),
generators as polynomials in `T_q − a_q`, radical layers, Loewy length, socle, annihilator, `principal?`, the `ε`-filtration and `T^sat/T`; the forms-side
kernel as a cross-route (at `k ≥ 12`); every stable claim certified through `CertifyStable`; torsion blocks refused by name.
`HeckeSaturationDefectValidation` (`standard`, **299** checks, ≈ 23 s): planted modules, the note's predictions at `(82, 7)`, `(142, 7)`, (H) the
hidden-chain law L-F1 at `(168, 13)`. Findings: the hidden chains are saturation defects of length exactly 1 (`I = m`, `T^sat/T = Z/ell`); the
`ell = 37` Loewy-4 Kummer blocks are **saturated** (`I = 0`), so the `pr:latticesplit` failure is a property of `T_m` itself. Its three columns
`sat_defect_dim`, `sat_defect_loewy`, `sat_length` go into census 3.1 (owner O5; partial). `HeckeCensusJoin.h` (WP-3 + audit repairs, header-only):
the census re-runs' `u_ell` budget from the row's source set (`CensusUEllBudgetMb`), the record reader (`ReadRecordSystems` / `ParseRecordSystems`),
`CompareSystem`, `CheckUEllOperator`, `RecordRootsFrom`, `ParseCellList` — the joins **by eigen-system, never by id** in arm (T) and in
`HeckeCensusLatticeValidation` (new default arm (J), **91** checks). `HeckeHidaCM` (WP-15 stretch + repairs, `hecke_ext::hidacm`; [U] 0.2.0 part 2):
exact imaginary-quadratic arithmetic (`h_K`, `w_K`, Kronecker, principal split primes), the CM oracle `a_p(θ_{λ_k})`, `χ_K` as a
`DirichletCharacter`, on WP-10's character model. `HeckeHidaCMValidation` (`standard`, **1376** checks, ≈ 44 s): (C0) the characteristic-0 CM count
`2 h_K [w_K | k−1]` on 25 cells, **(U9)** no CM at tame level 1, 2 (403 pairs), **(U8)** ordinarity at split `ell` on 146 / 146 runs, **(U10)** CM ∩
Eisenstein on 10 / 10 `h_K = 1` cells with the Eisenstein-multiplicity control, the `h_K = 2` negative example of the referee's U-1, the Sturm
bound printed and checked. Hook `HECKE_HIDA_CM_CELLS`. The census: **3.1** (WP-4) — arm (T) on the 230 dropped `n ≤ 500` cells and on all
669 cells with `n > 500` (`saturated` / `mult_one` filled on 2544 rows, add-only proof `violations=0`), the WP-5 columns partial — staged in
`results/congruence_census/edition3/3.1/`, **published at the close by owner default** (merge `edba09c`, 2026-10-02; `sat_cells_done=897 of 1459` — every cell `n ≤ 544` plus `(546, 59)`; `FINGERPRINT.txt` sha256(rows31.tsv) `4e13bda2…6cf9b3`; the unfinished
sat-defect cells read `not_computed:no_log`; the cluster cells RA / RS / LAT37 are census 3.2).

### Integral line (`src/hacs/Integral/`, slots 8–10)

Line 2 of the owner's two-line direction (true computation over `Z`; design brief
`docs/implementation/integral_line_design_brief.md` [IB]; contract [C] v1.8.0 Part VI,
`sec:integral`). Compiled into `cohomology_app`; pure host C++, no bignum ([IB] OD-3 (c)).
**M-0** (WP-7): `IntegralCharpolyCrt` — `char_Z(T_p | Λ^1)` by CRT over existing `F_ell` runs at
good primes, the Deligne bound carried as a bit length, residue-vector output;
`HeckeIntegralCharpolyValidation` (`standard`, 322 checks; `HECKE_INTEGRAL_CAMPAIGN=1` adds the
`n = 128` arm). **V-B** (WP-8): `HeckeBredonTreeValidation` (`fast`) — the shipped pipeline over
`F_ell`, `ell ∈ {2, 3}`, against the Bass–Serre tree model on 82 cells `n ≤ 40`, 16 frozen golden
cells ([C] `prop:bredon`(2)). **Slot 9**: `HeckeBredonTreeRingValidation` (WP-3, `standard`, 1394
checks) — the Bredon route over `Z/ell^k` at `ell ∈ {2, 3}` against O7 on 96 cells; **L2-1a** (WP-10):
`Integral/Model/IsotropyModel` — the isotropy-resolution model `R`, `R_∂`, `ε` of [C] `def:isomodel` on
the unrefined tessellation (ranks 5/14/19, boundary 3/6/6; `d² = 0` and `ε` a chain map certified
exactly over `Z[Γ]`), `Ĉ` over any `ModCtx`; `HeckeIsotropyModelValidation` (`standard`, 1032) and
`IsotropyModelDeltaSquaredValidation` (`fast`); **M0** (WP-11, a/s, accepted):
`Integral/Model/IntegralGroups` assembles `H^q(SL_2(Z); Sym^n Z²)`, `n ≤ 20`, `q ≤ 5`, from a rank at
a good prime, the 2- and 3-parts of `C_I ⊗ Z/ℓ^K` with `K` certified per differential
([C] `prop:certifiede`) and the Dickson-prime parts from the shipped `K`-mode —
`HeckeFreeModelValidation` (`standard`, 801 since slot-10 WP-8's m-6 / m-7) finds them equal to [IB]
Appendix A on all 126 cells. **Slot 10 — line 2 acts.** **L2-1b (1)** (WP-10):
`Integral/Model/StrictLift` — the strict lift `τ_Iso` of [C] `prop:strictlift` for `T_2`, `T_3`, `T_5`
in degrees 0–6 (`y_0` read off the `BoundaryStrict` table, `k` by the closed-form column homotopies —
no linear solve), certified exactly over `Z[Γ″]` ((T1) on Schreier generators, (T2), (T3), (S)
`ε τ_Iso = τ^s ε` strictly, (B) `τ_Iso(R_∂) ⊆ R_∂`); the coset transport `Θ̂_g` over any `ModCtx`;
K1 did not materialise (coefficients ≤ 3); `HeckeStrictLiftValidation` (`standard`, 1824). **L2-1b (2)**
(WP-13): `Integral/Model/PeriodicityClass` — `e ∈ Hom_{Z[Γ]}(R_2, Z)` (the Bockstein of `χ = ζ_+`,
order 12) and `E = e ∪ −` as a certified chain map `R_{•+2} → R_•`, every clause of
`lem:bulkperiodic`(2) on 126 ring cells; `HeckePeriodicityClassValidation` (`standard`, 2483).
**M1(a)** (WP-11, a/s, accepted): `Integral/Model/IntegralHecke` — `T_p` = `Θ̂_g` read on
`H^q(C_I ⊗ R)` with no integral basis (`induces_zero`, the UCT torsion readings, a division-free
charpoly): O6 at 8 good primes, the 691-congruence module `Z/691` on both lines, `T_2`, `T_3`, `T_5`
on the 2- and 3-torsion in degrees ≤ 5 (X6, X7 = commutativity — the `thm:relations` recursion needs
`StrictLift` for `diag(1, p²)` / `diag(p, p)`, slot 11), `Λ^1 ⊗ Z_ell` at 2, 3; hosts
`HeckeFreeModelValidation`'s tests (4) / (5); `HeckeIntegralActionValidation` (`standard`, 4601).
None of the three is in [E] `sec:ring`'s refusal closure (explicit `ModCtx`, no setting read).
**Slot 11 — M-3** (WP-11, accepted): `Integral/Model/StrictLift` also lifts `diag(1, p²)`,
`diag(1, p³)` and the central `pI` (`p ∈ {2, 3}`; `p = 5` at `ν = 2`), certified exactly over `Z[Γ″]`;
`T(p, p) = p^n`; **X7 in full** — the `thm:relations` recursion `T_{p^{ν+1}} = T_p T_{p^ν} −
p^{n+1} T_{p^{ν−1}}`, `ν ∈ {1, 2}`, on `H^q(C_I ⊗ R)`, `q ≤ 5`, at 2 and 3 (with `p = ell`) and at good
primes, under [C] `prop:relationsmodel`(2); `HeckeStrictLiftRelationsValidation` (`standard`, 3619).
Line 2's next phases (L2-3, L2-4; M1(b) under OD-3) — [X] v1.16 §8.
**Slot 16 — the `ell`-local isotropy model** (WP-16 stretch + WP-17 repairs; [C] v1.16.0 `sec:isomodelell`, built at `ell = 3`):
`Integral/Model/IsotropyModelEll` — `integral_model::LocalModel(desc, ell, LiftAveraging)` on `IsotropyModel`'s plug point (`ell = 0` = the free
model, identical entry by entry): exact `Q[Γ]` with denominators prime to `ell`, columns `F'^σ` (`P_σ` the `ell`-Sylow of `⟨g_σ⟩`,
`Q_σ`, `e_σ`), periodic where `P_σ ≠ 1`, the differential by `prop:isomodelell`(1)'s lifting with **every lift averaged by `e_σ`** (referee C-1),
the strict comparison maps `Φ_ell`, `Ψ_ell` of (4), cochains over any `ModCtx` with the projector `diag ρ_n(e_σ)`. It reads only the stabiliser
inventory of the descriptor it is given (no 7-vertex hard-wiring; `−I` kept; the MP constraint). `HeckeIsotropyModelEllValidation` (`standard`,
**5655** checks, ≈ 21 s): (IL0) `ell = 0` = `IsotropyModel`; (IL1) `d∘d = 0`, IM1, IM2, lengths = `Iso`'s and [IB] Appendix A on 63 ring cells;
(IL2) the closed form `H^q(Γ; M) = H^q(Z/3; M^{−I})`, `q ≥ 2`, to `n = 200`; (IL3) against the shipped Bredon route at `ell = 3`, `n ≤ 40`, and at the
map level over `F_3`, `Z/9`; (IL4) `Φ`, `Ψ` strict and inverse on cohomology, the transported `T'_p` = `StrictLift`'s `T_p` on 126 charpolys;
(NC) the un-averaged `Ψ_3` is **not well defined** on 22 / 25 generators (the averaging is a no-op on `d` at `ell = 3`, load-bearing in `Ψ`);
(MP) `ell = 2` through the same code. **Not run (carried):** (IL3)'s level-`N` clause, (IL4) over `Z/3^e`, the pair / cone half of
`prop:isomodelell`(5), the refinement half of `rmk:isomodellmp`.

**Two families of switches.** None of the `ENGINE_*` variables can change a value. The
*mathematical settings* of [X] §1.5 (`locality`, `u_ell`, `sturm`, `sturm_unavailable`,
`commutant_budget`, `final_mode`, `field_polynomial`, `split_field_report`, `presentation`,
`predictions`, `coefficient_ring` — the eleven registered today — plus `integral_fallback`, `q_max`, …
still to come; owner decision R1) are the second family: **every one
of them may change a published value**, a non-default setting changes the record's hash input and
the campaign job id, and only the defaults are golden. Slot 1 implemented the mechanism (the
console's `Settings` layer, the Sturm cap); **slot-2 WP-1 adds the engine-side struct
`Hecke/HeckeSettings.h` and registers the first mathematical key, `locality`**; slot 3 implemented
`locality = strict` and registered **`u_ell`**, **`sturm`** and **`sturm_unavailable`**; **slot-4
WP-1 registered `commutant_budget` and `final_mode`** (see "Hecke action" above) and **slot-5
WP-7 `field_polynomial` and `split_field_report`** (E6; `conway` parses and raises
`hecke::NotImplementedInThisBuild`, and `split_field_report` has no consumer until slot 6),
bringing the registry to **eight** keys with the all-defaults fingerprint still `0`. **Slot 6
registered none, deliberately**: since slot 5's emission the record's `settings` block (every
registered key, value and `source`) is inside 62 golden lines, so **registering any key now moves
62 golden lines** — the next keys (`presentation`, `predictions`, …) wait for slot 7's recipe
change ([X] v1.10 §1.5, §8). **Slot 7 made that change** (stage 1 (1): the golden texts see the
record's `settings` block reduced to its fingerprint) **and registered `presentation` and
`predictions` at zero golden movement** (stage 1 (2)): registration at the default is
**key-additive** again, permanently. **Slot 8 registered `coefficient_ring`** (WP-3, E8) at zero
golden movement, as predicted (a fresh `GoldenEmit` byte-identical; `ConsoleScriptEmit` no change).
**Slots 9, 10, 11, 12, 13, 14, 15 and 16 registered none** (slot 14's `U_ell` levers are engine-side, value-free
switches like the `ENGINE_*` family, not settings; `q_max` still waits; slot 11 widened `coefficient_ring`'s grammar to
`k ≤ 4096`, a value range, not a key).
A registration still moves every campaign per-job `settings` block (never an id, a file name or a
header).

### Lean lane (`lean/`, slot 16 onward)

The owner's multi-slot Lean formalisation programme ([LP] `docs/implementation/lean/00-lean-programme-plan.md` v1.0, approved 2026-10-01): formalise the
statements we use (literature) and our own arguments, beside a clean ground-truth LaTeX blueprint [GT]. **Not binding yet**; [C] stays the contract until the
owner's supersession review at milestone M4. Slot 16 ran L16-0 … L16-6 (all seven, L16-6 as stretch) on at most two Lean seats.

- **Memory budget (S25 housekeeping, audit `LATEX_polish_s6_audit.md` §5).** Scan (`lean_census.py` incl. `CensusScan.lean`, up-to-date build) **≤ 10 GiB**
  (watchdog 12); build (`lake build GL2`) **≤ 24 GiB** with jobs capped (watchdog 28); replay **≤ 16 GiB** (unchanged). Lake 5.0 (Lean v4.33.0) has **no `-j`**
  flag; its module jobs are tasks of the Lean runtime pool, each blocking on a child `lean`, so `lean_census.sh` sets `LEAN_NUM_THREADS=${LEAN_CENSUS_JOBS:-4}`
  for its internal build only (an exported `LEAN_NUM_THREADS` wins); manual builds stay plain `lake build`. It prints `LEAN_CENSUS_PEAK build_gib=… scan_gib=…`
  (`/usr/bin/time -v` maximum resident set of the *largest single process*, not the sum over concurrent children). Measured on a from-scratch build (no
  `.lake/build`): `jobs=4`, ≤ 4 concurrent `lean` processes observed, `build_gib=13.36`, `scan_gib=7.39`; the summed RSS of all `lean`/`lake`/`python3`
  processes sampled every 2 s peaked at 36.8 GiB, which double-counts shared mmap'd `.olean` pages (true PSS is lower).
- **The project.** `lean/` is a Lake project `GL2` (`lakefile.toml`, `autoImplicit = false`). Toolchain **`leanprover/lean4:v4.33.0`** with mathlib pinned
  at **`db584cd`** (the v4.33.0 tag — **not** FLT's v4.33.1, whose cache would force a full mathlib rebuild; L16-0's recorded deviation). **One shared
  dependency tree** `$HACS_DATA/lean-deps/` (≈ 7.9 GB), linked into a checkout by `lean/tools/lean_link_deps.sh` as the git-ignored
  symlink `lean/.lake/packages`; never a per-worktree mathlib, never `packagesDir` in the lakefile. Builds: `disk_guard.sh --min-free-gb 15` first,
  `lake build -j8`, never beside a ≥ 20 GB C++ run, `box_watch.sh` checked first.
- **Contents.** `GL2/Conventions/` (L16-2: the convention layer C1–C3, C8, C9, C11 — `ρ_n`, the contragredient and `prop:pairing`, `T_{p^ν}` full =
  primitive + `p^n`-term, Bernoulli, `ε_K`, and **`conv:nebentypus` / `bridge:nebentypus-dictionary`**: `δ ∈ Δ_0(N)` acts by `χ(a_δ) ρ_n(δ)`, `⟨d⟩ = χ(d)`,
  `T(p, p) = χ(p) p^n`, the `S_k(N, χ)` / `S_k(N, χ̄)` dictionary, `proved_mod_lit`; Fable-audited (F1) before WP-10 coded it; L16-6 closed `lem:detsym`,
  `prop:symconv`(3), `lem:symdual`); `GL2/Literature/` (L16-3: 13 `Prop` hypothesis structures, 12 with verbatim quotations and locators read from the
  scans — Bourbaki 416, Washington 1st ed., Hida ENS / Invent., Emerton, Wiles, Mazur, Bellaïche–Khare; guarded by their sources' standing hypotheses after
  L16-5); `GL2/Checkers/` (L16-4: the executable `ρ_n` oracle over `ZMod m` and the `obl:tau` checker, `tauCheck D = true ⇒ TauSpec D` kernel-proved and
  run by `decide +kernel` on the real `p = 2` table dumped by `HeckeTauDumpValidation`, its hash tied to the golden `tau_table_fnv64_p2_r1`; no
  `native_decide`); `GL2/Saturation/`, `GL2/Cone/` (L16-6: the G10 / G3 statement skeletons, `thm:conewelldef`(a) and three cone lemmas proved). [GT]:
  `lean/blueprint/src/gl2_groundtruth.tex` (Part 0, Part L3) + `gt_part_L.tex`, `gt_part_G.tex`, built by `lean/tools/build_gt.sh` (outputs git-ignored).
  Surveys: `lean/survey/flt_harvest_survey.tsv` (L16-1: 77 rows against Anthropic FLT `6e837e7`: 58 F-H, 9 F-A, 10 none); the inventory
  `docs/implementation/lean/statement_inventory_v1.tsv` (358 rows).
- **The census gate.** `lean/tools/lean_census.sh` (lake build + `lake env lean`, `lean_census.py`, the per-constant scan `CensusScan.lean`) prints one
  line — **read the text**: `LEAN_CENSUS decls= proved= proved_mod_lit= stated= planned= sorries= global_axioms= unresolved= stale= lit_hyp= native=
  gl2_consts= escapes= modlit_bad= verdict=OK|FAIL`; `--selftest` runs seven negative controls (planted sorry / axiom / stale name, unlinked `admit` /
  `native_decide`, vacuous `\gtmodlit`), each must FAIL and show its field. **Line of record** (L16-5 repairs, fresh build, merged tree):
  `LEAN_CENSUS decls=258 proved=194 proved_mod_lit=16 stated=32 planned=0 sorries=32 global_axioms=0 unresolved=0 stale=0 lit_hyp=16 native=0
  gl2_consts=1117 escapes=0 modlit_bad=0 verdict=OK` — every `sorry` is a declared `stated` row (the G10 / G3 skeletons). The committed
  `lean/census.tsv` (label, decl, status, axioms, lit_hyps) is what C++ sees: `LeanCensusFileValidation` (`fast`, **1767** checks; L16-0, `Registry/Slot16/L0.cpp`)
  re-derives every status from [GT] and checks the axioms column, **never running lake**; the close window reads the same committed state with
  `docs/matrix-engine/tools/lean_census_committed.py` (`LEAN_CENSUS_COMMITTED … verdict=OK`, no lake) and runs the live gate only under `--lean-live`.
  Regenerate `census.tsv` with `lean_census.sh --emit` after any [GT] or Lean change, in the same commit.
- **Exit criteria of [LP] §4.1 at the slot-16 close:** (1) census `global_axioms=0 unresolved=0 stale=0 verdict=OK` — met; (2) [GT] builds (web + PDF;
  `unresolved=0` replaces `checkdecls`, recorded in [LP] §2.5) — met; (3) C1, C2, C3, C8, C9, C11 `proved`, bridges `proved` / `proved_mod_lit` — met
  (L16-2, L16-6); (4) ≥ 12 quoted hypothesis structures — met, exactly 12; (5) one checker green on real C++ output — met (`tauP2_spec`); (6) the Fable audit
  (L16-5) ACCEPT WITH REPAIRS, repairs applied (`9bbdbc3`) — met; (7) `label_census.py` resolves `[GT, …]` — met. **Next: milestone M1** in slot 17
  (G1 complete, the compiled checker on the full golden τ grids, G10 saturation proved + the stable-certificate checker, the L1 register ≈ 25), with
  [LP] §4.3's velocity re-estimate.

### Data flow

1. Define a `SimplicialComplex` (triangulation of the space)
2. Specify monodromy via `SimplexRelation`s to create a `LocalSystemSimplicialComplex`
3. Pass to `EquivariantCohomologyOnK` and call `compute_cohomology()`
4. Optionally create morphisms via `EquivariantCochainComplexMorphismOnK`


## Moved from CLAUDE.md at the slot-21 close (2026-10-07), verbatim — build switches, licences, the seven targets, the architecture map, the Lean lane

The text below was replaced in CLAUDE.md by the slot-21 close size diet (owner request 2026-10-07: keep CLAUDE.md ≤ 30 KB); each block is the replaced text of CLAUDE.md at `1088dcb3`, unedited.

### "Build switches, presets, CPU-only, ARM" (CLAUDE.md lines 95–127 at `1088dcb3`)

```
**Build switches, presets, CPU-only, ARM (slot-19 NB-0; owner decisions 2026-10-03).** Three options, decided before
`project()`: `OC_ENABLE_CUDA` (default `ON`), `OC_BUILD_DOCS` and `OC_BUILD_NOTEBOOK` (both default `OFF`). An `OFF`
component is neither required nor probed (its `cmake/OcDocs.cmake` / `cmake/OcNotebook.cmake` is not even read).
`CMakePresets.json` holds `minimal` (= a plain configure), `cpu-only`, `reference` (this box: CUDA `sm_120`, docs ON,
notebook ON), `jetson-orin` (`OC_CUDA_ARCHITECTURES=87`) and `jetson-orin-cpu`; the presets' `binaryDir` is the in-tree
`build/<preset>` (ignored by version control) — agents pass `-B $DATA_ROOT/...`: `cmake --preset cpu-only -B <dir>`.
- **CPU-only** (`-DOC_ENABLE_CUDA=OFF`): the CUDA language is never enabled and `CUDAToolkit` never searched, so no nvcc /
  libcudart is needed; `EngineCuda` is built from its stub `src/Cuda/CudaStub.cpp` (`engine::cuda::available()`
  false, reason `built without CUDA (OC_ENABLE_CUDA=OFF)`), the entry point is `main.cpp` (host-compiled), and the device validations print their `[SKIP] <name>: no usable CUDA device (built without
  CUDA …)` line. Verified at NB-0 with no CUDA directory on `PATH`: `--list` 176, `GOLDEN_STRICT=1` A 11827 / 0, B 6231 / 0,
  the three digests unchanged, `--all` 160/160 (16 min 47 s, 3.7 GB peak). `cross_config.sh`'s default list carries this arm
  (`RelWithDebInfo+OC_ENABLE_CUDA=OFF`, built with the toolkit stripped from `PATH`) and a `host` column.
- **Docs** (`-DOC_BUILD_DOCS=ON`, needs pdflatex / bibtex / makeindex): `make docs` (or `make docs_<name>`) builds the
  manual and the contracts through the `docs/latex/build_*.sh` scripts into `OC_DOCS_OUTPUT_DIR` (default
  `<build>/docs-pdf`, ignored by version control); never part of `all`.
- **Notebook** (`-DOC_BUILD_NOTEBOOK=ON`): `OC_BUILD_NOTEBOOK=1` is the `--serve` compile flag; `cmake --install` puts
  the gateway, page, vendored KaTeX and `read_only_verbs.json` under `<prefix>/share/oc-notebook/` (NB-3). Gateway:
  `python3 notebook/gateway/oc_gateway.py --binary <build>/cohomology_app [--bind <LAN IP>]` (stdlib only; default
  loopback; public bind refused; private-peer filter; per-process token printed once; no TLS; scrubbed child env;
  RSS / wall / idle limits) — `notebook/gateway/README.md`. Page `notebook/page/` (KaTeX 0.19.0 vendored in
  `notebook/vendor/katex/`, `PROVENANCE.txt` + `SHA256SUMS`). Self-test (not a registered validation):
  `python3 notebook/gateway/test_gateway.py --binary <bin> --scratch <dir outside the tree> [--scripts all]` → last line
  `GATEWAY_TEST … verdict=OK` (≈ 10 s).
- `cohomology_app` always gets `OC_ENABLE_CUDA` / `OC_BUILD_DOCS` / `OC_BUILD_NOTEBOOK` defined to `0`/`1`; code reads them
  through `src/hacs/BuildSwitches.h`. A validation excluded by a switch keeps its name (the `--list` count
  never depends on a switch) and returns `oc::BuildSwitchSkip(name, "OC_BUILD_<X>")` — an explicit `[SKIP] <name>:
  OC_BUILD_<X>=OFF` line and exit 0, never a silent pass. No switch changes a value.
- **`-ffp-contract=off` (slot-24 CL-12, audit D §4).** `CMakeLists.txt` adds it to every C++ compile on every architecture
  (`$<COMPILE_LANGUAGE:CXX>`; formerly aarch64 only). GCC defaults to `-ffp-contract=fast`, which on aarch64 fuses `a*b+c`
  into FMA (on x86-64 only with `-mfma` / `-march=native`, i.e. the `Bench` configuration, where the flag now also applies; the
  default and `Release` builds contract nothing). The value paths are integer; the one certified FP filter (`Hecke/Predicates.cpp`) already uses volatile
  stores. The flag is a value-safety statement, a no-op on x86-64 as built. It is **host C++ only**: CUDA device-code FP
  semantics (nvcc's `--fmad`) are untouched.
- **aarch64 / Jetson Orin**: the owner-run kit `docs/cluster/jetson/` (`README.md`, `run_jetson_kit.sh`: the `sm_87` and
  CPU-only arms, golden, digests, device validations, bench checksums, `--all`, one tarball; rule O11 — no agent connects, **except `arm-board`: agents may connect since 2026-10-04, owner-authorised, slot-20 WP-JET**; the clusters stay owner-only).
  The AVX-512 kernels and `_mm_pause` are already `__x86_64__`-guarded with scalar / `yield` fallbacks.
  **Android / Termux** (clang + libc++ + bionic, CPU-only): recipe `docs/cluster/termux/README.md` (slot-20 S4; `malloc_trim` is `__GLIBC__`-guarded). The owner's first device build (clang 21, CPU-only) found one GCC-only construct, fixed and merged in slot 21
  (`termux-patch`, `50c95fe6`: a multi-declarator `auto` in `Kernels.cpp`); a local clang build is a slot-22 item.
```

### "Licences" (CLAUDE.md lines 145–154 at `1088dcb3`)

```
**Licences (slot-21 WP-LIC, slot-22 WP-LIC2; the project will be open-sourced).** Code: **`LGPL-3.0-only WITH LicenseRef-CUDA-exception`** (`LICENSE`,
`LICENSE.GPL`; the exception permits linking the proprietary CUDA Toolkit); `lean/`: **Apache-2.0** (`lean/LICENSE`); `docs/` and `lean/blueprint/`: **CC-BY-4.0**
(`docs/LICENSE`); the vendored FLT modules under `lean/Vendor/` keep upstream's Apache-2.0 notices and carry **no** SPDX headers (exempt; byte-identical). Mapping:
`REUSE.toml` (REUSE 3.x; an inline SPDX header wins), texts in `LICENSES/`, `NOTICE`, `COPYRIGHT.md`, `docs/licence/THIRD_PARTY.md` (+ `third_party/`). Tools:
`docs/licence/tools/add_spdx.py [--apply | --check]` (every header-able tracked file needs an `SPDX-License-Identifier` header — **a new source file gets one
in the commit that adds it**) and `docs/licence/tools/check_licences.sh`, run by `LicenceGuardValidation` (`fast`; line of record `LICENCE_GUARD candidates=1406
pending=0 missing=0 stale=0 unknown=0 spdx_ids_in_use=2 vendored_files=28 vendored_mismatch=0 known_third_party_pdfs=0 failures=0 verdict=OK`, slot-21 W1). The
third-party PDFs of `docs/literature/` were **removed from HEAD** (`0a502f9c`; private copy `$HACS_DATA/library-private/docs-literature/`
+ `.sha256`); **git history still contains them** — publication goes through **option C** of the slot-22 plan (a `git filter-repo` mirror with a commit map,
dry run in WP-PUB; the owner executes the publication). Never re-add a third-party PDF to the tree.
```

### "The seven targets" (CLAUDE.md lines 171–179 at `1088dcb3`)

```
### The seven targets

- `ModArithmetic` — static library for modular arithmetic and linear algebra (including the Phase 2 kernel layer and the Phase 3 block model)
- `HeckeCore` — static library for the Hecke feature's exact-integer substrate (`Mat22`, certified FP-filtered sign predicates, `QuadPoint`); pure C++, does not depend on `ModArithmetic`
- `MatrixEngine` — static library for the Phase 4 tape (`src/Engine/`: recorder, passes, executor, thread pool, program cache, `TapeElim`) and its device seam; links `EngineCuda`
- `EngineCuda` — static library for the Phase 5 CUDA layer (`src/Cuda/`); the only target that compiles CUDA device code, depends on `ModArithmetic` + `CUDA::cudart`, and nothing but `cohomology_app` depends on it. In a CPU-only build (`OC_ENABLE_CUDA=OFF`) it is the plain-C++ stub `CudaStub.cpp` + the unchanged `CudaValidation.cpp` / `CudaBench.cpp`, with no `CUDA::cudart`
- `ConsoleCore` — static library for the console's language core (`Console/Core/`, phase C0). Like `HeckeCore` it depends on **nothing else in the tree — STL only**, enforced by `docs/matrix-engine/tools/check_console_includes.sh`; everything needing a matrix, a polynomial or a pipeline object is a *binding* (`Console/Bindings/`, compiled into `cohomology_app`, never into `ConsoleCore`). `main.cpp` has exactly one console branch.
- `NumberField` — static library for the in-house number-field core (`src/hacs/NumberField/`, slot-19 WP-NF, [E] `sec:lvnf`): own `BigInt` (schoolbook + Karatsuba, Knuth D; no GMP, no CAS, owner O3), exact rationals / Bernoulli numbers, `Z[ζ_{ℓ^k}]` exactly and mod `ℓ^M` (multimodular NTT), cyclotomic units, `v_π`, the Kummer local `ℓ`-th-power tests (layer 1 and the equivariant `Z/ℓ²` layer), `Q(α)`, Newton polygons, Hensel; slot 21 added in-house LLL (`Lll`), `Polred`, multiprecision reals (`MpReal`) and the degree-`ℓ` Ribet-field polynomial (`RibetField`). **STL only**, like `HeckeCore` / `ConsoleCore`, enforced by `docs/matrix-engine/tools/check_numberfield_includes.sh` (run by `NumberFieldValidation`); no `__int128` without the portable fallback (`-DNF_NO_INT128` forces it)
- `cohomology_app` — main executable (`HeckeExt/`, `Integral/`, `Console/Bindings/`, `Campaign/`, … are compiled straight into it)
```

### "Architecture (map)" (CLAUDE.md lines 373–430 at `1088dcb3`)

```
## Architecture (map — full prose in `docs/architecture-detail.md`)

- **ModArithmetic** (`src/ModArithmetic/`) — `mod_*` primitives on `uint32_t`; `Fnv.h` (**the one**
  FNV-1a-64 behind every golden / campaign / bench hash); `Matrix` (retired from the pipeline), `FlatMatrix`
  (preferred), `BlockFlatMatrix` (**deprecated, legacy-arm only**); `ModCtxU128.h`, `DigitWord.h`, `LadicInduction.h`
  (arbitrary `k`: native `u128` and the (C2) `ell`-adic digit induction).
- **Matrix engine Phase 2** (`namespace engine`) — `ModCtx` (incl. composite `Z/ell^k`), `Kernels`, `DenseElim`
  (incl. Howell / Smith over `Z/ell^k`), `RefLinAlg` oracle. Bit-identity by construction. Rollbacks
  `ENGINE_BACKEND=legacy`, `-DENGINE_SHADOW_LEGACY=ON`.
- **Block model Phase 3** (`engine::BlockMat` / `engine::blk`) — `BlockPool`, `BlockRef`, `BlockElim` (same D5b
  bases as legacy); `to_flat` / `from_flat` are the single source of truth for the flat cochain layout.
- **Tape Phase 4–5** (`src/Engine/`, `engine::tape`; `src/Cuda/`, `engine::cuda`) — record →
  `compile()` (seven passes) → `Executor` on a work-stealing `ThreadPool`. **`ENGINE_DEVICE=cpu` is the default and the
  golden path; the GPU is never enabled by default** (1.4–3.3× slower on the pipeline's shapes). None of the `ENGINE_*`
  env switches can change a value.
- **Campaign driver Phase 6** (`--campaign <spec> [--output <dir>] [--dry-run] [--quiet]`) — `docs/matrix-engine/campaign.md`;
  results and published sets (census editions 1–3, `ext_*`, `hida_towers/`, …) in `docs/matrix-engine/results/`.
- **Migration guards** (`docs/matrix-engine/tools/`, each run inside `--all` by a validation; removing an allow-list
  entry is progress, adding one needs a reason): `raw_mod_calls.sh` (`ConsumerMigrationValidation`, 208 sites, 0
  outside), `check_matrix_includes.sh` (`MatrixRetirementValidation`), `check_console_includes.sh`
  (`ConsoleC0Validation`), `check_heckeext_includes.sh` (`HeckeExtArchitectureValidation`; `HeckeExt → Hecke` one way,
  no `Console/`, `Cuda/`, `Engine/`, `BlockFlatMatrix.h`, no `unordered_`), `label_census.sh` (`ContractCensusValidation`).
- **Console** (`src/hacs/Console/`, OC script `*.oc`, [P] v3.11.1) — `Console/Core/` (STL-only),
  `Console/Bindings/`, `HeckeExt/RegisterHeckeExtensionVerbs.cpp`. CLI: `--console` / `-i` / `--script <f.oc>` / `-c` /
  `-`, `--set key=value`, `--log`. **Exit codes: 0** ok, **1** usage, **2** parse, **3** runtime, **4** failed `assert`,
  **5** `NotImplementedInThisBuild`. 43 numbered scripts (`NNN_*.oc`, up to `053`) with frozen `.expected` transcripts; slot 21 added the read-only verbs
  `pow(A, e)`, `kummer_unit(ell, i)`, `hida_tower(n, ell, m)` (scripts `050`, `051`), early slot 22 (WP-VERB-2, `17e93767`) `level_n`, `nebentypus`,
  `forms_algebra`, `hida_lambda` (scripts `052`, `053`); `docs/console/console.md`
  is generated by `docs/console/gen_console_md.sh <binary>` — regenerate it whenever a verb, type or setting is registered; the same holds for the LaTeX user manual's tables (`docs/latex/tools/gen_cli_manual_tables.sh <binary>`, gated by `CliManualCoverageValidation`).
  **`--serve`** ([P] §18, `oc-serve/1`; only with `-DOC_BUILD_NOTEBOOK=ON`): one read-only session as NDJSON on stdio;
  only overloads tagged `read_only` in `Console/Bindings/ReadOnlyTags.cpp` (166 of 175 overloads; twin `Console/serve/read_only_verbs.tsv`,
  a new verb needs a row in both) are served; the launch refuses any non-whitelisted `GOLDEN_*` / `CONSOLE_*` / `CLI_MANUAL_*` /
  `HECKE_*` / `ENGINE_*` / `OC_*` / `*SAN_OPTIONS` variable (exit 1); `fatal` frames exit 70. **Notebook theme** (early slot 22 FR-1,
  `docs/implementation/slot22/nbtheme_report.md`): a dark, user-definable theme (Auto / Light / Dark / two high-contrast / Custom, a 13-token editor with WCAG contrast warnings), client-side only, in `notebook/page/themes.js` (import / export format
  `oc-notebook-theme/1`); no server state, no verb; the gateway self-test now runs 22 tests (`GATEWAY_TEST ran=22 … verdict=OK`); the [P] §18.17 addendum
  (v3.12.0) is proposed, not applied.
- **Cohomology layer** (`src/hacs/`) — `SimplicialCohomology`, `LocalSystemSimplicialComplex`,
  `EquivariantCohomologyOnK` (also over `Z/ell^k`), `EquivariantCochainComplexMorphismOnK`, `LocalSystemPresets`,
  `LocalSystemSL2Z` (the 7-vertex `SL(2,Z)\H` model, `Sym^n`), `LocalSystemUtils`.
- **Hecke action** (`Hecke/`, contract [C]) — integral `T_p`, `U_ell`, `T_{p^r}`, `T(p,p)` on `H^q`, `q ∈ {0,1,2}`;
  coset / τ tables (certified), `HeckeOperatorOnK`, `HeckeReduction`, cone / boundary / pairing / contragredient,
  `HeckeSettings` (`MathSettings`, eleven keys), the `U_ell` levers (default-on, value-preserving), `LadicCell` (the
  digit route), Hida / level-`ell` / level-`N` (Shapiro, Heilbronn, sparse, degeneracy `α_d`), nebentypus. `U_ell`'s
  limit is `ell ≤ 23170` (`lem:bounds`). The weight-2 level-`N` route at **`p = 2, 3`** (early slot 22, LN23; spec / report
  `docs/implementation/slot22/LN23_{spec,report}.md`, F4 ACCEPT WITH REPAIRS): at `n = 0` the fixed spaces of `S`, `ST` are orbit sums at every `p`, and the
  cokernel presentation is `H^1(Y_0(N))` ([C] `prop:levelNcurve`, `sec:levelNcurve`); gated by `HeckeLevelNCurveValidation`; it closes §3.1 of the slot-21 Calegari–Emerton
  probe (`docs/implementation/slot21/ce_probe_report.md`, `ce_elkies_check.md`; CE's `p = 2, 3` grids in `LN23_report.md` §5). Module map: `Hecke/README.md`.
- **Hecke extensions** (`HeckeExt/`, `namespace hecke_ext`, [E] / [X]) — the ext driver and record `hecke_ext/v5`,
  certificates, atlas `Σ(ell)`, θ / Dickson, census split / lattice / joins, forms side, Hida towers / components / CM,
  `Z/ell^K` Hecke-algebra route, saturation defect; the `ℓ`-adic L-value layer `HeckeExt/LValue/` (MTT / Eisenstein measures, coefficient rings, wild
  characters, Iwasawa invariants: slot 21 P2–P5) and the Λ-adic files `HeckeLambdaQExp` / `HeckeLambdaModSym` / `HeckeLambdaTwoVar` (P7–P9).
- **Integral line** (`Integral/`, [C] `sec:integral`) — isotropy models (incl. the `ell`-local model at `ell = 3`),
  strict lift, periodicity class, integral groups and Hecke action; pure host C++, no bignum.
- **Two families of switches.** The `ENGINE_*` variables (and the `U_ell` levers) **cannot** change a value. The
  *mathematical settings* (`locality`, `u_ell`, `sturm`, `sturm_unavailable`, `commutant_budget`, `final_mode`,
  `field_polynomial`, `split_field_report`, `presentation`, `predictions`, `coefficient_ring` — eleven registered)
  **may**; only the defaults are golden; a non-default setting changes the record's hash input and the campaign job id;
  registering a key at its default is key-additive (no golden movement).
```

### "Lean lane" (CLAUDE.md lines 432–475 at `1088dcb3`)

```
### Lean lane (`lean/`, slot 16 onward)

[LP] v1.4; **not binding yet** ([C] stays the contract; the owner's Q5 rulings of 2026-10-05, `docs/implementation/slot21/owner_rulings_Q5_1005.md`:
Q5-1 clause-scoped supersession conditional on C1–C3, Q5-2 M4-f weak, Q5-3 R20-L, Q5-4 `Tfull`). Lake project `GL2`; toolchain
**`leanprover/lean4:v4.33.0`**, mathlib pinned at **`db584cd`** (the v4.33.0 tag — **not** FLT's v4.33.1). **One shared
dependency tree** `$HACS_DATA/lean-deps/` (≈ 7.9 GB), linked by `lean/tools/lean_link_deps.sh` as the
git-ignored symlink `lean/.lake/packages`; never a per-worktree mathlib, never `packagesDir` in the lakefile. **Never run
`lake update`** (in the main checkout or any worktree): on a mismatched mathlib URL it deletes and re-clones the package
directory, and through the symlink that deletes the shared mathlib checkout (owner warning, 2026-10-03). Builds:
`disk_guard.sh --min-free-gb 15` first, `lake build` (this Lake has no `-j` option: `lake build -j8` fails with `unknown short option '-j'`), never beside a ≥ 20 GB C++ run, `box_watch.sh` checked first.
**Census gate**: `lean/tools/lean_census.sh` prints one line — read the text; line of record:
`LEAN_CENSUS decls=1303 proved=1238 proved_mod_lit=37 stated=0 planned=0 sorries=0 global_axioms=0 unresolved=0 stale=0
lit_hyp=28 native=0 gl2_consts=6290 escapes=0 modlit_bad=0 hyp_bad=0 sources_hash=OK verdict=OK` (re-emitted unchanged by a real `--emit` at the slot-21 close, C-4; first reached in slot 20, M4 on `s20/lean-m4` after the
L20-6 repairs, `docs/implementation/slot20/L20-6_repairs.md`: M4 met, M4-f in the weak form, `def:m4-hecke` `proved`; before slot 20:
`decls=1136 proved=1077 proved_mod_lit=19 … planned=16 … lit_hyp=24 … gl2_consts=5690`, slot 19, L19-1 (M3-a: `stablecert_ES` /
`stable_of_spec_ES`, `hrank` discharged, `hES` only) + L19-3 (M3-b: `model7_acyclic` proved in `GL2/Model/Acyclic.lean`, the last `stated` row)
+ L19-2 (M3-c/d/e: the bridge `GL2/Model/Bridge.lean`, `model7_projRes`, `model7_rmkOrbifold` in `GL2/Model/RmkOrbifold.lean`,
`model7_tauexists_2`, `heckeTilde_indep_tau` in `GL2/Model/WellDefTau.lean`) + the F3 repairs (`docs/implementation/slot19/L19-6_repairs.md`:
`heckeTildeR_indep_tau` for `τ` over `R`, `heckeRel_indep_tau`, `heckeTilde_indep_g`, `rmkOrbifold` / `rmkOrbifoldL`; the five
`\gtmodlit` rows split into `-uncond` / `-aux` siblings, so `proved_mod_lit` counts declarations: 42 → 19) + L19-4 (C2: the boundary
descriptor `XBdryDatum` / `model7Bd`, `PairHyp` for the model with no hypothesis (`model7_pairHyp`, `model7_pairHypQ`), `EtaSpec.toIsPairHomotopy`,
`GL2/Model/{XBdry,XBdryModel,EtaPair}.lean`) + L19-5 (the M4 skeleton: 16 `planned` rows in `lean/blueprint/src/gt_part_M4.tex`, linked to sorry-free
`def … : Prop` statements and definitions in `GL2/M4/Skeleton.lean`; a `planned` row has no `\leanok`, never counts `stated`; task list and forecast
`docs/implementation/slot19/L19-5_M4_skeleton.md`)); `lean/census.tsv` carries a `# sources_sha256=` line, re-emitted with every source change; the replay step is
`docs/matrix-engine/tools/lean_replay.sh` (dated run directory, verdict line kept in `verdict.txt` + `verdicts.log`; replay of record
`LEAN_REPLAY modules=150 ok=150 failed=0 peak_rss_gib=13.76 peak_module=GL2.Checkers.TauP2 cap_gib=16 rc=0 killed=0 verdict=OK`, slot-21 close step C-4, 2026-10-06,
`docs/implementation/slot21/close_lean_report.md`; 125 GL2 modules + the 25 vendored ones; the census line above re-emitted there by a real `--emit`, byte-identical
to the committed `census.tsv`); W1's committed-state line
`LEAN_CENSUS_COMMITTED decls=1303 proved=1238 proved_mod_lit=37 stated=0 … planned=0 sorries=0 … hyp_bad=0 sources_hash=OK sorries_vs_stated=eq leanfile=PASS verdict=OK`). The committed `lean/census.tsv` is what C++ sees
(`LeanCensusFileValidation`, never runs lake; the close window uses `lean_census_committed.py`). **Regenerate
`census.tsv` with `lean_census.sh --emit` after any [GT] or Lean change, in the same commit.** No `native_decide`.
**Milestone M1 met in slot 17, M2 in slot 18, M3 in slot 19, M4 in slot 20** (M4: F3 ACCEPT WITH REPAIRS, 0 B / 1 M / 9 m, all repaired; M4-f in the weak form;
`docs/implementation/slot20/L20-6_F3_audit.md`, `L20-6_repairs.md`, the Q5 brief `L20-6_Q5_brief.md`); [C] v1.21.0 carries **140** clause-scoped `\LEAN` / `\LEANlit` markers on 65 labels
(M1's list `docs/implementation/slot17/lean_taggable_labels.md` + F3-18 §8 + F3-19 §8 + F3-20 §8 as amended by the repairs; no marker on `thm:classical`, `eq:corconjres`,
`eq:fullop`) — a marker covers only its clause. **R20-L ran in slot 21** (`docs/implementation/slot21/R20-L_report.md`): the Shimura / Brown / Ash–Stevens locators
verified ([C] v1.21.0-pre.1, [GT] repairs `a8d7459a`); `hcl` stays unverified (slot 22).
**FLT vendoring (slot 21, L21-V, `da3084b8`):** `lean/Vendor/AnthropicFLT/` = **25 modules, 2 958 lines** of `anthropics/fermats-last-theorem` @ `6e837e75`
(Apache-2.0, upstream Lean `v4.33.1`, mathlib `db584cd`), **byte-identical to upstream**; ours are `MANIFEST.tsv` (per-file sha256, lines, consumer labels) and
`PROVENANCE.md`; `LICENSE`, `NOTICE`, `ATTRIBUTION.md` are upstream's. Built as `[[lean_lib]] AnthropicFLT` (`srcDir = "Vendor/AnthropicFLT"`) on our toolchain
`v4.33.0` (no `require`, no `lake update`). The lib keeps upstream's `leanOptions`; `lean/tools/lean_census.py` allows `backward.isDefEq.respectTransparency.types`
**for that lib only** (`VENDOR_OPTION_ALLOW`), never in `[leanOptions]`, GL2's lib or a GL2 source, with its negative control in the self-test
(`LEAN_CENSUS_SELFTEST controls=17 controls_not_failing=0 verdict=OK`); every vendored module is kernel-replayed by `lean_replay.sh`. **Next: M5 in slot 22**
(transport `HeckeH1 → End(H^n)`, `thm:classical` in [C]'s sense, the `eq:fullop` / Smith-form enumeration lemma, with its F5 audit); the M5 cut text was not
written in slot 21 (carried).
```

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim — "Data flow"

1. Define a `SimplicialComplex` (triangulation of the space)
2. Specify monodromy via `SimplexRelation`s to create a `LocalSystemSimplicialComplex`
3. Pass to `EquivariantCohomologyOnK` and call `compute_cohomology()`
4. Optionally create morphisms via `EquivariantCochainComplexMorphismOnK`
