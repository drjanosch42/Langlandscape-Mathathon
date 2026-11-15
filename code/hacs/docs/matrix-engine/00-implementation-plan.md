# Matrix Engine — Implementation Plan (September 2026)

**Status:** architect's synthesis of the four September-2026 audits. Binding for the engineering
team until amended by the owner. Branch `hecke-action` @ `c8227c8`.

**Evidence base (cited as `01 §x` … `04 §x`):**
`01-matrix-substrate-audit.md` (substrate, 32 ranked defects), `02-pipeline-consumer-audit.md`
(every call site, op-graphs, 10 bit-identity assertions B1–B10, 16 certificates C1–C16, 8
determinism hazards), `03-profiling-baseline.md` (measured baseline, hotspots, reproduction
commands), `04-hardware-limits-and-prior-art.md` (rooflines, reduction schemes, prior art,
feasibility formulas). Predecessor: `docs/optimization-audit/00-synthesis-and-implementation-plan.md`
(March 2026, Phases 0–7 merged at `cdad0b9`); its vocabulary (`A_Cq`, `A_Zq`, `factor_basis_block`,
`D1 ⊗ I`) is reused unchanged.

---

## 1. Executive summary

**Where we are.** The pipeline is correct, exhaustively cross-checked, and slow for reasons that
have almost nothing to do with matrix engines yet:

* The shipped binary is `-O0`: `CMakeLists.txt` sets no build type and no flags at all, and the
  in-source `CMakeCache.txt` (which is **git-ignored, not checked in** — a fresh clone gets an
  *empty* flag set, equally unoptimised) resolves to `CMAKE_BUILD_TYPE=Debug`. Cost: **5.3–7.3×
  end-to-end** on the real workloads (`03 §4.4`) and **5.9–8.3×** on the substrate
  microbenchmarks (`01 §1`, GEMM/RREF; the scalar `mod_mul` loop is only 2.5×). `--all`
  16m33s → ≈2m45s.
* Every inner loop is division-bound: `mod_mul = (uint64)a*b % p` (`ModArithmetic.cpp:36`); no SIMD
  ISA has integer division, so `-march=native` buys 6–12 % and the AVX-512 units idle
  (`01 §3.4`, `03 §7.1`). Delayed `uint64` accumulation + transposed right operand measured
  **5–21×** on exactly the `d_V = 17…129` block sizes this project uses, and **12–23×** over the
  wider `n = 64…512` band (`03 §7.2`; `01 §3.4` measures 20× at 512).
* At `n_sym = 100` the 575 s (`-O0`) `HeckeBenchmarkSmoke` run sits **≈ 90 % in three algorithmic
  defects** outside the block layer (`02 §5.5` consolidated table); the three Tier-0/1 fixes remove
  **68–90 %** of it (68 % is `02 §7`'s conservative count, which credits only the part of
  `factor_basis_block` that the densification fix removes): per-vector re-RREF in `HeckeOperatorOnK.cpp:352` (≈ 54 %), the
  `O(n⁵)` `ComputeSymmetricPowerMatrixFM` via `mod_nCr_small` (≈ 14 %), and
  `factor_basis_block`'s re-densification through an `O(B_r+B_c)` accessor (≈ 22 %). The March
  block kernels are 0.2 % (`02 §0, §5.5`).
* The matrices are small (≤ 1677 × 1419 at `n_sym = 128`, 9 MB, L3-resident; `03 §2`) and
  structurally block-sparse (18–29 % block density; blocks drawn from `{0, I, αI, −M, I−M}`,
  `M ∈ {ρ_n(T), ρ_n(S), ρ_n(ST), ρ_n(TS)}` which are triangular/anti-diagonal; `02 §5.3`,
  `04 §6.1`). The block grid is fixed and small — `A_Cq` is `13 × 7` / `13 × 11` / `5 × 5`
  (relations × simplices) on the 7/11/5 model (`03 §2`), shrinking to `6 × 7` / `2 × 11` / `0`
  once the vacuous FIX-negI rows are short-circuited at even `n` (`02 §5.4`), so grid shape is a
  function of `(model, n mod 2)` and belongs in the program cache's shape signature; only
  `d_V = n_sym + 1` grows.
* `mod_inv` is silently wrong for `p ≥ 2^31` (`01 §3.1`, defect #2). Two determinism hazards
  (`τ` first-match-wins derivation; underdetermined triangle-fill solve) will produce a
  *different-but-valid* `Θ` under any iteration reordering, invalidating every recorded
  reference (`02 §6.5`).

**Where we are going.** A block-sparse, layout-aware, exact-integer matrix engine — uint32
storage, uint64 delayed accumulation, a content-addressed block pool with structural kinds,
a recorded block-op program that is canonicalised, batched and scheduled onto a 16-thread CPU
pool and CUDA graphs — with **bit-identical results regardless of device or schedule**, gated
by a golden-output harness captured *before* anything changes.

**Expected end state (estimates, §6).** At `ℓ ≈ 2^27`: a full `T_p` run (cohomology +
operator + all in-process certificates) at `n_sym = 1000` in **≈ 5–30 s** (GPU / CPU) versus
an extrapolated ~10⁴ s today; `n_sym ≈ 2000–3000` in minutes; `n_sym ≈ 5000` in tens of
minutes with out-of-core panels. Sweeps of many `(n_sym, ℓ, p)` batched through one CUDA graph
at ~10³ problems/min for `n_sym ≤ 200`. The `ℓ < 2^64` regime becomes practical on the GPU
(44× CPU advantage, `04 §1.5`).

**The five decisions that shape everything** (details and evidence in §2, which also carries
D5 — structured elimination — and D6 — external dependencies; the numbering below is §2's):

| # | Decision |
|---|---|
| D1 | **Fix the three algorithmic defects and the build before any engine code** — otherwise the engine is benchmarked against noise (`02 §0`, `01 §9.1`). |
| D2 | **uint32 storage / uint64 delayed accumulation, integer-only, on both devices.** No FP64 (unusable at `p ≈ 2^27`, 1/72 rate on the GPU), no FP16/BF16/TF32 ever. Regime-dependent reduction (delayed / Shoup / 64-bit Montgomery). The bound `k·(p−1)² < 2^64` is a runtime assertion. |
| D3 | **A block pool with structural kinds** (`Zero`, `αI`, `αI + βM` over a deduplicated immutable dense pool with triangular/anti-diagonal tags), block-CSR pattern, per-buffer layout, transposes and sub-ranges as views. Bases are single column-major block multi-vectors, not `std::vector<Matrix>`. |
| D4 | **A small in-house tape + static scheduler**, not StarPU/Halide/CUTLASS: record block ops → canonicalise/dedup/const-fold → k-block → batch → assign device by measured cost model → execute (CPU pool / CUDA graph). Elimination is a panel-driven driver that emits batched Schur updates through the same executor with a schedule-independent pivot rule. |
| D7 | **Bit-identity is the acceptance criterion at every phase**, enforced three ways: the golden harness (old → new), dual-route in-process assertions (kept from the Hecke feature), and `HECKE_PURE_INTEGER`-style build/runtime toggles for old-vs-new engine and CPU-vs-GPU. |

---

## 2. Design decisions with rationale

### D1 — Order of work: defects → arithmetic → data model → engine → GPU → campaign

*Alternatives.* (a) Build the engine first and migrate consumers onto it; (b) fix the three
defects first, then build.
*Evidence.* The three defects are 68–90 % of the run and 100 % of the super-cubic growth
(`02 §5.5`); none needs the engine; each is 0.5–2 days with exhaustively checkable output. The
`-O0` build alone is 5.3–8.3× (`03 §4.4`). Measuring an engine against this baseline would
credit it with ~two orders of magnitude that belong to `-O3` and to a table lookup (`01 §9.1`).
*Consequence.* Phase 0/1 are mandatory and short; the engine's exit criteria are stated against
the *post-Phase-1* baseline, which Phase 1 must re-record.

### D2 — Arithmetic representation and reduction, per prime regime

*Decision.*

| Regime | Storage | Accumulation / reduction | Where |
|---|---|---|---|
| `p < 2^30.5` (**project default**: `ℓ = 134217757 = 2^27 + 29`, `(p−1)² = 1.8014e16 ≈ 2^54.0`) | `uint32` in `[0,p)` | `u32×u32→u64`, **delayed**: accumulate up to `k_max = ⌊(2^64−1)/(p−1)²⌋` terms — **1023 at the project prime** (1024 holds only at exactly `p = 2^27`), ≥ 256 for `p < 2^28`, ≥ 16 for `p < 2^30`; one `%`/Barrett per output cell; k-blocked loops for longer dots. `k_max` is computed at runtime from `p`, never hard-coded | CPU (`vpmuludq`/autovec) and GPU (`mad.wide.u32`) |
| `2^30.5 ≤ p < 2^31` | `uint32` | `k_max ≤ 8` — delay stops paying; eager Shoup (precomputed `⌊w·2^32/p⌋` for the reused operand: the `A` panel in GEMM, the pivot-row factor in elimination) | both |
| `2^31 ≤ p < 2^32` | `uint32` | Shoup-32 does **not** apply here (it needs `2p < 2^32` for the lazy `[0,2p)` representative): use eager Barrett-64, or promote to the 64-bit path. Forbidden by a runtime check until **both** the `mod_inv` fix (defect #2) **and** the `mod_add` fix (defect #33, §Phase 0) land | both |
| `2^32 ≤ p < 2^63` (S13 `ℓ < 2^64` backend) | `uint64` | 64-bit Montgomery (`mulx`/`__umul64hi`); conversion at engine boundaries | **prefer GPU** (629 G vs 14.3 G modMAC/s, `04 §7.4`) |

Plus: a **modulus context** `ModCtx<Elt>` (`p`, `p²`, Barrett `⌊2^64/p⌋`, Montgomery
`−p^{-1} mod 2^64`, `R² mod p`, `k_max`) constructed once and passed by reference to every kernel
(`01 §3.3, §3.5`), replacing the loose `p` argument; **batched inversion** (Montgomery's trick)
for pivot normalisation; an explicit **canonicalise** op so every buffer's invariant (canonical
`[0,p)` vs lazy `[0,2p)`/`u64`) is a documented property, never implicit.

> **Correction to `04 §1.5`/`§8.1`'s regime labels.** Doc 04 tabulates this project's operating
> regime as "`p < 2^26.5`" and yet (correctly) places `134217757 ≈ 2^27.0` inside it with
> `k ≤ 1024` (`04 §1.5` note, `§2.2` table). `2^26.5` is the FP64 *single-product* boundary
> ((p−1)² < 2^53), not the `uint64` delayed-accumulation boundary. The governing bound is
> `k·(p−1)² < 2^64`, which still yields `k_max ≥ 4` as `p → 2^31`; doc 04's "`k ≤ 4` makes delay
> pointless" therefore applies only within about half a bit of `2^31`, not from `2^26.5` upward.
> Taking doc 04's labels literally would route the project's own default prime into the
> eager-Shoup row and forfeit the 4–5× (512 G vs 120 G) that the whole of D2 rests on. The table
> above uses the arithmetically correct boundaries.

*Alternatives rejected.* FP64 delayed reduction (FFLAS): a single product overflows 2^53 at this
`p`; the GPU's FP64 is 1/72 of FP32 and slower than the CPU (`04 §1.4, §2.3`). INT8 tensor
cores via 7-bit digit splitting: exact and ≈2× at best over the integer path, large complexity;
deferred until GPU-compute-bound (`04 §2.4`). Compile-time-constant modulus (Linac ≈50 %):
adopted **optionally** for the GPU in Phase 5 as a build-time list of hot primes
(`-DENGINE_HOT_PRIMES=134217757,...`), never as the only path (open question Q3).
*Evidence.* `04 §1.5` (512 G CPU / 4931 G GPU modMAC/s in regime (b) vs 120 G / 2460 G eager),
`03 §7.2` (12–23× at `n = 64…512`), `01 §3.4` (20× at 512, plain C++ autovectorised).
*AVX-512 on Zen 4 — no width dividend.* 512-bit ops are double-pumped over two 256-bit pipes:
AVX2 `vpmuludq` measures 41.2 G lane-mul/s against AVX-512's 41.0 G on the same core
(`04 §1.2`). **Budget zero speedup from vector width** (`04 §8.5(2)`). AVX-512 is adopted for
(a) `k`-mask registers, which make block-sparsity and pivot handling branch-free — the actual
win here; (b) halved instruction count (front-end/loop-overhead relief); (c) `vpermi2*` /
`vpcompress*` for gather-free layout changes. The portable AVX2 fallback in Phase 2 is therefore
a *portability* path, not a slow path.

*Consequences.* Every kernel carries a static `k_max` and the executor inserts reduction
boundaries; overflow is impossible by construction and asserted in debug. Exact integer
arithmetic is associative, so **reassociation, vectorisation and CPU/GPU partition cannot change
results** (`04 §7.2`) — this is what makes D7 achievable.

### D3 — The block-sparse data model

*Decision.* Two layers, both in `src/ModArithmetic/` (new files):

1. **`DenseBuf<Elt>`** — an owned or arena-backed contiguous buffer with `rows, cols, ld,
   layout ∈ {RowMajor, ColMajor}`, `invariant ∈ {Canonical, Lazy2p, Accum64}`, and a
   `structure ∈ {Generic, UpperUnitri, LowerUnitri, SignedAntiDiag, Diagonal}` tag.
   **`DenseView<Elt>`** = `{buf*, row0, rows, col0, cols, transposed}`; a sub-range is an
   offset, and a *logical* transpose is a flag flip (a row-major `r×c` read column-major **is**
   its transpose). **Do not confuse the two kinds of transpose.** A logical transpose changes
   only the index mapping and is free; it does **not** change the memory access pattern, and the
   measured 20× (`01 §3.4`) comes precisely from *physically* streaming the `B` operand
   contiguously in the `k` direction. So a kernel-level layout mismatch that the microkernel
   cannot absorb is resolved by a **physical, blocked (16×16-tile) relayout** — a real
   `TRANSPOSE` node, materialised once and cached in the arena, never a flag flip. Replaces
   `FlatMatrix`'s hard-coded `r*cols_+c` (`01 §9.3`).
2. **`BlockMat<Elt>`** — block grid as prefix-sum offsets `row_off[nbr+1], col_off[nbc+1]`
   (kills the `O(#blocks)` `get_entry`, defect #8); pattern in **block-CSR** with entries sorted
   by `(br, bc)` (deterministic iteration order, no hash containers on any result path, per
   `02 §6.5(5)`); each entry a `BlockRef { kind, α, β, pool_id, flags }` meaning
   `α·I + β·M[pool_id]^(T?)`, so `Zero (α=β=0)`, `I`, `αI`, `M`, `−M`, `I−M` are all one
   representation and the elimination can constant-fold on `(α, β)` without touching data
   (`04 §4.3`). Dense blocks live in a **content-addressed immutable `BlockPool<Elt>`**
   (hash → id, full compare on collision, `std::hash<Elt>` not `<uint32_t>` — fixes defect #14;
   refcounted so overwritten blocks do not leak — fixes #15). A `BlockBuilder` bulk-fills a
   block from a span in one call — no per-cell `set_entry` anywhere (defect #4, `02 §2.3`).
   **`BlockMat` with `nbc = 1` and block width `k` is the vector/multi-vector type**: a basis of
   `k` cochains is one column-major `dim_q × k` object whose flat index is exactly the binding
   layout L1 `s·d_V + k` (`02 §2.2, §6.4`), so the seven `Matrix ↔ FlatMatrix ↔ BlockFlatMatrix`
   round-trips per degree disappear (`02 §2.2`).

*What is carried forward from `BlockFlatMatrix`.* The `αI` scalar flag and content dedup — "the
substrate's real sparsity mechanism" (`01 §9.5`). What is not: the dense index grid, value-zero
instead of structural-zero, dense flattening inside every kernel/image path, the 20 validation-only
members (`01 §5.1`: five members are used externally — ctor, `set_block_entry`, `flat_kernel`,
`operator*`, `to_flat_matrix`).

*Layout policy (the owner's "row- or column-major depending on the next operation" requirement,
made concrete).* Every `DenseBuf` carries exactly one physical layout, assigned by pass 3 of D4
as follows:

1. Each op declares a *preferred* layout per operand (GEMM: `A` row-major, `B` column-major —
   that *is* the measured 20×, `01 §3.4`; `P_q` is only ever applied to columns ⇒ row-major;
   bases are only ever consumed column-wise ⇒ column-major, `02 §3.1`; `PANEL_RREF` wants
   row-major panels; `GATHER/SCATTER` to the L1 flat layout wants column-major multi-vectors).
2. A buffer's layout is the preference of its consumers weighted by each consuming node's `cost`
   (the same cost estimate pass 6 uses); ties break toward the *producer's* natural layout, and
   deterministically toward `RowMajor` when still tied — so layout assignment is a pure function
   of the program, not of the schedule.
3. For each remaining mismatch the planner inserts one physical `TRANSPOSE` node, hoisted to the
   earliest point where the operand is live and memoised on `(buf, target-layout)` so `n` mismatched
   consumers cost one relayout, not `n`.
4. Layout is a *property of the buffer recorded in the program*, so it is stable across replays of
   a cached program and identical on CPU and GPU. Because the relayout is an exact permutation of
   exact integers, no layout decision can change a value — only the time it takes to produce it.

*Alternatives rejected.* Retrofitting layout into `FlatMatrix` (row-major is baked into every
method, `01 §9.3`); scalar CSR (sparsity is block-regular and densifies under elimination,
`04 §4.2`); keeping semantic block boundaries as the tiling — the engine must be free to
re-block semantic `d_V` blocks into cache-sized tiles (`01 §4.5`), so tile size is a scheduler
parameter and block boundaries are metadata.

### D4 — Engine execution model

*Decision.* A **recorded program of block ops**, executed by an in-house scheduler.

```
Recorder      ──► Program { nodes: [ (op, in-views, out-view, k_bound, cost) ], buffers }
                     ops: GEMM (C ±= A·B, with kind-folding), AXPY, SCAL, TRANSPOSE,
                          CANONICALIZE, PANEL_RREF, PIVOT_SEARCH, TRSM (no-op for I pivots),
                          SCHUR_UPDATE, GATHER/SCATTER (block ↔ flat), COMPARE (memcmp)
Passes        ──► 1 constant-fold on BlockRef kinds (0 / I / αI / ±M / I−M)
                  2 CSE: identical (op, operand pool-ids, view) ⇒ one node   (the M·X memo of 04 §4.3)
                  3 layout assignment (per consumer) + TRANSPOSE insertion
                  4 k-blocking to honour k_max (D2)
                  5 batching: same-shape GEMMs ⇒ one BATCHED_GEMM node
                  6 device assignment by static cost model (measured constants of 04 §1, §6.4)
Executor      ──► wavefronts; CPU nodes → thread pool sized to the machine (32 HW threads),
                  with a PER-KERNEL thread count: 16 (1/core) for memory-bound kernels,
                  32 for compute-bound ones (04 §7.5 measures 829 vs 477 GB/s L3 at 16 vs 32
                  threads, but 1023 vs 847 GFLOP/s the other way round);
                  GPU nodes of a wavefront → captured once into a cudaGraph, replayed
```

* **"Predefined" programs.** A program is keyed by its *shape signature* (block grid, pattern
  hash, `d_V`, prime regime). Recording is `O(#blocks)` and cheap; compiled programs (after
  passes, with the CUDA graph) are cached and replayed across problems with the same signature —
  both Θ routes, all `d_q` columns, and — **subject to the caveat below** — every `ℓ` at fixed
  `(n_sym, p, r, q)`. This is the owner's "collect all block ops, group, batch" idea; the
  τ-table's `(σ, σ_k)` pattern is known before any arithmetic (`02 §7.8`), so the entire Θ
  assembly is one predefined program.
  **Caveat (cache-poisoning hazard).** The τ pattern is *not* unconditionally `ℓ`-independent:
  the triangle-fill solve is ℤ-first with a **mod-`ℓ` fallback** taken on `HeckeOverflow`
  (`02 §6.5(2)`), and the fallback branch can yield a chain with different support. The shape
  signature must therefore include a hash of the actual τ pattern for the concrete `(n_sym, p,
  r, q, ℓ)`, computed before lookup; a miss must fall back to recording, never to replaying a
  stale program. `EngineTapeValidation` covers this by asserting that a replayed program and a
  freshly recorded one produce identical buffers on a grid that includes a mod-`ℓ`-fallback case.
* **Batching (pass 5), concretely.** The grouping key is
  `(op, m, n, k, layouts, elt-width, k_bound, device)` — *not* the operand addresses; instances
  are then sorted by `(output-buffer id, output row0, col0)` so the batch order is a pure
  function of the program. A group of size 1 is emitted as a plain node. Because every instance
  writes a distinct output view, no batch introduces a reduction and no atomics are needed.
* **Device assignment (pass 6), concretely.** `04 §6.4`'s inequality
  `W·(1/R_cpu − 1/R_gpu) > 8·M·N/B` with the measured `R_cpu, R_gpu, B` of `04 §1.5, §1.3`, plus
  a fixed per-node launch term (0.68 µs inside a CUDA graph, `04 §1.4`) and the residency state
  of each operand. The constants live in one table so the model can be re-measured, and the
  chosen device is recorded in the program — the same program always picks the same device, and
  `ENGINE_DEVICE` overrides it wholesale for the determinism validations.
* **Elimination.** Not a single static node: rank is data-dependent. A **panel driver** runs on
  the host: `PIVOT_SEARCH` on the current panel (rule: *first non-zero row in original row order
  per column* — a pure function of the matrix contents, hence schedule-independent; over `F_p`
  any non-zero pivot is as good as any other, `04 §3.3`), then `PANEL_RREF`, then a batched
  `SCHUR_UPDATE` of the trailing matrix as GEMMs of depth = panel width (128–512, which
  satisfies the `k_max` bound *and* cache blocking simultaneously — `04 §2.5`). Structural
  shortcuts: `I` pivot ⇒ no TRSM; `αI` ⇒ scaling; `±M`, `I−M` ⇒ one shared `M·X`.
  **Why the pivot rule may be changed freely, and where it may not.** RREF over a field is
  unique, so *the RREF itself, the pivot-column set and the rank are invariant under any pivot
  rule* — including the legacy block layer's own structural heuristic, which is **not** the
  topmost-non-zero rule (`get_pivot_block_priority`, `BlockFlatMatrix.cpp:581-592`, prefers an
  `I` block, then `−I`, then other scalars, then general, ties by first index). Everything
  *derived* from the RREF — kernel bases, image bases, the transform `U`, `factor_basis_block`'s
  complement and projector, and the block-shaped `block_kernel`/`block_image` outputs — is
  **convention-dependent, not canonical**, and is where a rewrite silently diverges. Those
  conventions are specified in **D5b**; the engine must implement them verbatim.
* **CPU/GPU partition.** Static: a node goes to the GPU when its work exceeds the measured
  crossover (`r ≳ 45` for elimination-shaped work, `04 §6.4`) *and* its operands are resident or
  the transfer is amortised across the wavefront; small-block batches go as a unit; regime
  `ℓ ≥ 2^32` always GPU. Residency (`host/device/both`, version) is tracked per buffer. No
  dynamic work stealing between devices in v1 (`04 §5.3`).
* **Split-K and reductions.** Where a GPU GEMM splits the `k` dimension, each partial must be
  **canonicalised to `[0,p)` before combination** (or the *total* `k` must satisfy `k_max`) — the
  combination is then an exact mod-`p` sum, which is associative and commutative, so any
  reduction tree or atomic order gives the same bits. This is the one place where "no atomics on
  results" (below) is relaxed, and it is safe for that reason alone; it must not be generalised.
* **Determinism guarantee.** Every node's output is a mathematically unique object (exact
  integer result, canonicalised at node boundaries; pivot choice a function of contents only;
  no floating point; no atomics on results; block-CSR order fixed). Therefore **any schedule,
  thread count, batch grouping or device yields bit-identical buffers.** This is asserted, not
  assumed: `ENGINE_VERIFY_DEVICE` (§4.3) re-executes every GPU node on the CPU and `memcmp`s.

*Alternatives rejected.* Expression templates (cannot reorder across an elimination or target
two devices); StarPU/PaRSEC/Legion (heavyweight, known GPU-saturation issues, and the hard part —
our cost model and structural folding — is not something they supply; `04 §5.2, §8.3`); a fully
static elimination graph (would need worst-case rank assumptions).

### D5 — Structured elimination strategy

Recursive/blocked PLUQ à la FFPACK, ported not linked (`04 §4.1, §8.4`): panel RREF, TRSM,
Schur-complement GEMM, rank profile as a by-product (ranks/kernels/images are what the pipeline
computes constantly). On the block level, exploit kinds only where they survive: assembly, the
first one or two panels (`I`/`αI` pivots, shared `M·X`), multi-RHS application, and — above
all — batching across problems. Budget **20–30 %** from structure on a single RREF, not 70 %
(`04 §4.3`); the asymptotic win is GEMM-bound blocking (`O(1)` → `O(b)` arithmetic intensity),
which is what moves the GPU off the bandwidth roofline (unblocked GPU elimination is *slower*
than this CPU, `04 §6.3`). No block Wiedemann (`04 §4.2`).

`factor_basis` specifically: never materialise the identity augmentation (already true,
`02 §2.1`), give the relation/generator columns real `d_V`-wide blocks (`02 §7.11`), and return
the RREF/projector as block objects — the `Θ_eq` solve (`02 §3.2`) becomes one factorisation of
`C_eq` + one multi-RHS TRSM.

### D5b — The legacy basis-choice contract (what "bit-identical" actually pins)

The plan's default answer to Q1 is *strict*: the engine reproduces the legacy **bases**, not only
the canonical objects. That is only implementable if the conventions are written down, because
several of them are load-bearing and none is asserted anywhere in the current tree. They are:

| Object | Legacy convention (verbatim) | Where |
|---|---|---|
| RREF | leftmost pivot column, topmost non-zero row from `r` downward, leading 1, eliminate above *and* below, zero rows at the bottom. **Canonical** — safe under any correct rewrite | `FlatMatrix.cpp:133-181`; scalar fast path `:1023-1034` agrees |
| **kernel basis** | one vector per **free column in ascending column index**; coordinate at the free column is exactly `1`; coordinate at the `i`-th pivot column is `−RREF[i][j_free]`; empty basis returned early when square and full rank | `FlatMatrix.cpp:1332-1396`; `Matrix.cpp:409-437`; `BlockFlatMatrix.cpp:1501-1543` (same rule on the assembled true scalar RREF, then re-blocked by `block_col_dims_`) |
| image basis | the **original** matrix columns at the pivot-column indices, ascending. **Exception, and a live inconsistency:** `FlatMatrix::image()`'s scalar fast path returns `e_j`, not `α·e_j`, where `Matrix::image()` and `BlockFlatMatrix::flat_image()` return `α·e_j` (new defect #34) | `FlatMatrix.cpp:1398-1436` (fast path `:1411-1420`); `Matrix.cpp:440-452`; `BlockFlatMatrix.cpp:1646-1675` |
| transform `U` | **`U` is the trailing `m` columns of `RREF([A ∣ I_m])`, eliminated over all `n+m` columns** — hence *unique given `A`*. The obvious reimplementation (accumulate row operations while eliminating `A` only) satisfies `U·A = RREF(A)` and is therefore "correct", yet differs on rank-deficient `A`: the rows corresponding to zero rows of `RREF(A)` would carry un-reduced left-null-space vectors instead of that space's RREF. **Spec the rewrite as the augmented RREF, never as "any `U` with `U·A = RREF(A)`."** Sole caller: `BlockFlatMatrix.cpp:652` | `FlatMatrix.cpp:1094-1177` |
| true scalar RREF from the block layer | rows emitted **one per definitive pivot, in ascending pivot-column order**, zero rows at the bottom. This ordering is an **undocumented contract**: `factor_basis_block` indexes it arithmetically as `rref_row = independent_relations + i` (`Matrix.cpp:625-634`) and produces a silently wrong projector — not an error — under any other row order | `BlockFlatMatrix.cpp:1041-1182`, pivot selection `:940-1027` |
| `factor_basis_block` complement | greedy **leftmost-independent** subset of the ordered `generators` list, modulo the ordered `relations`; projector rows read off the identity block of `RREF([R ∣ G ∣ I])`. Canonical *given the input order* — and that order is inherited from the kernel-basis order above | `Matrix.cpp:553-638` |

Two consequences the phases must honour:

* **The kernel-basis convention is the root of everything.** `C_eq` (`EquivariantCohomologyOnK.cpp:214`)
  and `Z_eq` (`:365`) are `flat_kernel()` outputs; `W`, `B_eq`, `H_eq` and `P_q` (`:406`, `:447-451`)
  are deterministic functions of them. Change the kernel convention and every entry of
  `Θ^{(q)}_eq`, `A^{(q)}(T_p)`, the induced `H*` maps and the shipped JSON `level_b` /
  `change_of_basis` changes with it (char-/min-polys survive; entries do not).
* **`FpPoly` hard-codes the convention even though the plan leaves `FpPoly` alone.**
  `MinPolyKrylov` (`FpPoly.cpp:422-425`) asserts `ker[0].data[j][0] == 1` — i.e. that `ker[0]` is
  the leftmost-free-column vector with a unit at coordinate `j = rank` — and *throws* otherwise.
  A reordered or renormalised kernel basis fails loudly there, which is fortunate, but it is a
  hard structural dependency, not a style preference.

**Test-coverage gap this exposes (feeds R12).** `BlockFlatMatrixValidation`'s
`verify_flat_kernel_properties` / `verify_flat_image_properties` (`:1086`, `:1192`) check only
size, `M·K = 0`, rank and **mutual span inclusion** — never entrywise identity. A rewrite that
changed the kernel basis would pass the substrate suite and silently change every shipped
cohomology-level matrix. Every basis-producing validation added by this plan
(`BlockEliminationValidation`, `SubstrateDifferentialValidation`) must therefore compare
**entrywise**, not by span; and the block layer's own RREF-idempotency self-check is currently
dead in every build (`#ifdef DEBUG_BLOCKFLATMATRIX`, commented out at `BlockFlatMatrix.h:4`, with
its corrective fallback commented out at `BlockFlatMatrix.cpp:1166`) — Phase 0 should either
revive it under `ENGINE_DEBUG_CHECK` or delete it, not leave it as decoration.

### D6 — External dependencies: none beyond the CUDA toolkit

*Decision.* Write in-house; no FFLAS-FFPACK/LinBox (FP64 core is unusable here; port the
algorithms), no cuBLAS/cuSPARSE (no mod-`p`), no StarPU, no FLINT in the build. **CUTLASS is not
adopted in v1**: its strength is large dense tiles, ours is batched `d ≈ 100` blocks with a
custom 2–5-instruction modular MAC; copy its threadblock→warp→instruction tiling structure by
hand (`04 §3.3, §8.4`). Revisit only if Phase 5's hand-written GEMM stays below ~40 % of the
INT32 roofline (open question Q2). This matches the repo culture (hand-rolled JSON writer, no
test framework, explicit registry). A tiny fixed-seed naive reference (`RefLinAlg`: schoolbook
GEMM/RREF with the *old* `mod_*` primitives) ships in-tree as the oracle for kernel tests.

### D7 — The dual-route bit-identity discipline, extended

The Hecke feature's rule — two independently-bracketed routes, `memcmp`-equal — extends to
three new axes, each with its own toggle in the `HECKE_PURE_INTEGER` style:

| Axis | Toggle | Mechanism |
|---|---|---|
| old substrate vs new engine | `ENGINE_BACKEND={legacy,engine}` (runtime, env/CLI) + `-DENGINE_SHADOW_LEGACY=ON` (build: run both, compare, throw) | every migrated call site is wrapped by a `shadow_check` in Phases 2–3 |
| CPU vs GPU | `ENGINE_DEVICE={cpu,gpu,hybrid}` (runtime) + `-DENGINE_VERIFY_DEVICE=ON` (build: every GPU node re-executed on CPU, `memcmp`) | Phase 5 |
| schedule/thread count | `ENGINE_THREADS=N`, `ENGINE_BATCH={0,1}` (runtime) | `EngineDeterminismValidation` runs the golden grid under several settings and compares hashes |

The golden harness (§4.1) is the common denominator: one hash file, one validation, every
axis compared against it.

---

## 3. Phased plan

Ordering is by (risk-adjusted value)/(effort). Effort is in agent-days (one Claude agent
implementing + owner review), following the endorsed reproduce→diagnose→plan→implement→validate
pipeline for anything bit-identity-critical. Every phase ends with `./hacs --all`
exit 0 and `GoldenRegressionValidation` exit 0 unless the phase explicitly re-baselines (only
Phase 0 may create golden values; no later phase may change them without an owner decision).

### Dependency graph

```
                    ┌──► P1 defects (consumer/Hecke layer) ──┐
P0 build + golden ──┤                                        ├──► P3 block model + consumer migration
                    └──► P2 arithmetic layer (ModArithmetic/) ┘                     │
                                                                                    ▼
                                        P4 engine: tape / passes / scheduler / CPU pool
                                                          │
                                    ┌─────────────────────┴─────────────────────┐
                                    ▼                                           ▼
                              P5 CUDA backend  ─────────────────────────►  P6 campaign
                              (kernels may start after P2;                 (CPU-only campaign
                               integration needs P4)                        possible after P4)

Cross-cutting V (validation & determinism) runs alongside every phase.
```

Parallelisable among agents: **P1 ∥ P2** (disjoint files: consumer/Hecke layer vs
`ModArithmetic/`); inside P3, the data model (one agent) precedes the consumer migration, which
splits by file (`EquivariantCohomologyOnK` / `HeckeOperatorOnK` / `HeckeCrossChecks`+
`InducedLocalSystem` / `SimplicialCohomology`+morphism); **P5 kernel work can start after P2**
(it needs only the arithmetic decisions and `DenseView`) in parallel with P3/P4; P6's sweep
driver and streaming JSON can be built during P4.

---

### Phase 0 — Build hygiene, correctness fixes, golden-output harness

**Goal.** An honest, optimised, reproducible baseline and a frozen bit-exact reference *before*
any arithmetic changes.

**Scope.**
* `CMakeLists.txt` (whole file, `01 §1`, `03 §1.2`): default `CMAKE_BUILD_TYPE=RelWithDebInfo`
  when unset; add configs `Bench` (`-O3 -march=native -DNDEBUG`) and `Check`
  (`-O1 -g -fsanitize=address,undefined`, asserts on); per-target `target_compile_options`
  with `-Wall -Wextra`; `CMAKE_CUDA_ARCHITECTURES` **75 → 120** (`03 §1.2`; cc 12.0 GPU);
  optionally `-Wno-deprecated-declarations` *only* on the pipeline TUs until Phase 3 (defect #26
  hides real warnings); record the compiler (`03 §1.1` says CMake selects GCC 11.4 while `01`
  measured with GCC 15 — pin and document which). Three mechanics that will otherwise cost a day:
  (i) the tree is built **in-source** and the existing `CMakeCache.txt` pins
  `CMAKE_BUILD_TYPE=Debug`; a new default only takes effect on a *fresh* configure, so the Phase-0
  instructions must say "delete `CMakeCache.txt`/`CMakeFiles/` (both git-ignored) and reconfigure",
  and `CLAUDE.md`'s build recipe must be updated to match; (ii) a custom config needs
  **`CMAKE_CUDA_FLAGS_<CONFIG>` as well as `CMAKE_CXX_FLAGS_<CONFIG>`**, because `kernel.cu` is an
  nvcc TU and inherits neither the CXX flags nor `-march=native` (which must be passed as
  `-Xcompiler=-march=native`) — or move the new `--bench` driver into a plain `.cpp` TU and leave
  `kernel.cu` thin, which is simpler and is the recommendation; (iii) the existing cache carries
  `CMAKE_CUDA_FLAGS=-DUSE_SCALAR_KERNEL`, so that macro **is** defined for CUDA TUs — it is
  undefined only for the C++ TUs where defect #32's dead branches live
  (`EquivariantCohomologyOnK.cpp:145` and `:275`, *two* sites, both to be deleted).
* `ModArithmetic.cpp:59-83` `mod_inv`: `int64_t` accumulators, with a boundary test at
  `p = 2147483659 = 2^31 + 11` (defect #2). `ModArithmetic.h:44-45` currently *claims* the regime
  is `ℓ < 2^32`; until the fixes land, correct the comment to the true bound (`p < 2^31`) and add
  a runtime guard, then restore `p < 2^32` once they do.
* **NEW — defect #33 (this review; not in `01 §6`): `ModArithmetic.cpp:41-45` `mod_add` is
  silently wrong for `p > 2^31`.** `uint32_t result = a + b;` wraps modulo `2^32`: at
  `p = 4294967291`, `a = b = p−1` returns `4294967284` instead of `4294967289`, with no throw.
  It is the *same latent regime* as defect #2, it is reached by `mod_nCr_small` (`:101-113`) and
  hence by every `ρ_n`, and the 64-bit twin `mod_add64` (`:172-180`) already carries exactly the
  right test — `if (r < a || r >= p) r -= p;` — together with the explanatory comment. Port that
  test to the 32-bit version. **This must be fixed before Phase 0's differential harness runs at
  `p = 4294967291`, or that harness will report a "difference" that is really a shared bug.**
* **Defect #9 (`Matrix.h:41`, `Matrix.cpp:286`) — severity C, unscheduled in the first draft:**
  `MatrixT`'s RREF cache is never invalidated while `data` is public. `Matrix` survives Phase 3
  in `MatrixValidation` and `HeckeModuleDecomposition`, so this does not go away on its own.
  Cheapest correct fix at this stage: make the cache invalidate on any non-`const` access, or
  privatise `data` behind an accessor. Add a regression case (`rank(); data[i][j] = …; rank();`)
  to `MatrixValidation`. (Defect #16 — dangling `IntermediateRREFForm` pointers — is deliberately
  *not* scheduled: it is subsumed when `BlockFlatMatrix` is retired in Phase 3/4.)
* `BlockFlatMatrix.cpp:83-95` `_compute_block_hash`: `std::hash<Elt>` (defect #14).
* `Matrix.h:99` deprecate `Matrix64` (#23); `Matrix.cpp:155` invalid escape (#25); delete dead
  code listed in defect #32 (`IdentityMatrix`, `flatten_to_column_vector`,
  `unflatten_from_column_vector`, `factor_basis_fm`, `get_block_pivot_coords`,
  `SimplicialCohomology.cpp:159`, the never-defined `USE_SCALAR_KERNEL` branches at
  `EquivariantCohomologyOnK.cpp:280-296`).
* **NDEBUG policy:** Release defines `NDEBUG`; the `assert`s at `BlockFlatMatrix.cpp:1120-1133`
  become no-ops there. Introduce `ENGINE_CHECK(cond)` (always on, for O(1) invariants such as
  the `k_max` bound and dimension matches) vs `ENGINE_DEBUG_CHECK` (off under `NDEBUG`, for
  O(n²) checks). All new code uses these, never bare `assert`.
* **In-repo benchmark CLI** — `kernel.cu` gains `--bench <mode> <args>` mirroring the scratch
  driver of `03 §1.3` (`cohom <n> <ell>`, `hecke <n> <ell> <p>`, `family <n> <ell> <p> <r>`,
  `decomp …`) with phase-split timings and peak-RSS print. Reason: "there is no supported way to
  sweep a parameter from the CLI" (`03 §1.3`), and every exit criterion below is a `--bench`
  command.
* **Golden harness** — new `src/hacs/Golden/GoldenHarness.{h,cpp}` +
  `GoldenReference.inc` (generated by `./hacs --golden-emit`, checked in).
  Grid: `n_sym ∈ {0,1,2,4,10,16,22,24,32}` × `ℓ ∈ {2,3,5,13,691,10007,134217757}` (skipping
  mathematically excluded pairs) × `p_hecke ∈ {2,3,5}` × `r ∈ {1,2}` × `q ∈ {0,1,2}`, plus the
  `HeckeExtendedRegimeValidation` 64-bit points. (Both "mathematically excluded" and
  "Dickson-exceptional" must be decided by calling the shipped predicates — in particular
  `IsDicksonExceptional` (`HeckeEndToEndValidation.cpp:98`), never a hard-coded list; see R8. In
  this grid it fires at `(n, ℓ) = (24, 5)` and `(32, 5)`. Golden *hashes* are pinned at
  exceptional points too; only the dimension/char-poly **oracle assertions** are relaxed there.)
  Captured objects, each as `(dims, FNV-1a-64
  over entries widened to uint64 in the L1 flat layout)`: `dim H^q`; `C_eq`, `Z_eq`, `B_eq`,
  `H_eq` bases; `P_q`; `Θ^{(q)}_flat` and `Θ^{(q)}_eq`; `A^{(q)}(T_p)`, `A(T_{p^2})` (recursion
  and direct); the level-(b)/(c) JSON (`HeckeReport`) hashed after whitespace normalisation;
  `get_induced_H_eq_maps()` for the S6 cases. Hashes must be identical between the `-O0`
  shipped binary and the Release build (already verified byte-identical for validations,
  `01 §1`) and under `HECKE_PURE_INTEGER=ON/OFF`.
* **Substrate differential harness** (`01 §7` gap #9): `SubstrateDifferentialValidation` —
  fixed-seed random matrices at `p ∈ {2,3,7,23,134217757,2147483647,4294967291, 2^61−1}` and
  both widths; `Matrix` vs `FlatMatrix` vs `BlockFlatMatrix` RREF/rank/kernel/image compared
  entrywise; non-uniform block dims (`{3,7,2} × {5,1,6}`, zero-width blocks); cache-coherence
  sequences (`rank; set_entry; rank`, `rank; is_zero; rank`); algebraic identities
  (`(AB)^T = B^T A^T`, `rank A = rank A^T`, `dim ker + rank = cols`, `A·A^{-1} = I`).

**Non-goals.** Any change to arithmetic results; any performance work beyond flags.

**Prerequisites.** None.

**Steps.** (1) CMake + flags, rebuild, run `--all` (expect ~2m45s, `01 §1`). (2) `mod_inv` and
`mod_add` fixes + boundary tests in `mod_arithmetic_validation`. (3) dead-code deletion,
deprecations, hash fix, defect #9; `--all` green. (4) `--bench` CLI. (5) golden harness: emit
from a **`c8227c8` + harness-only** binary built `-O0` in a scratch worktree — note that
`--golden-emit` does not exist at `c8227c8`, so the harness commit must be *cherry-picked onto*
that tag and must touch nothing but the new `Golden/` files and the registry; then verify the
Phase-0 Release binary reproduces the same hashes. That ordering proves the harness catches
nothing spurious, and keeping the emitting binary free of the Phase-0 correctness fixes is what
makes it a true "before" reference. (6) differential harness. (7) re-time `HeckeBenchmarkSmoke`;
update `CLAUDE.md` timings *and its build recipe* (both are `-O0`-era).

**Validations.** Keep green: all 32. New (register in `ValidationRegistry.cpp` via
`ValidationRegistry::register_validation("Name", &Fn)`): `GoldenRegressionValidation`,
`SubstrateDifferentialValidation`, `ModInvBoundaryValidation` (or fold into
`mod_arithmetic_validation`).

**Exit criterion.** `./hacs --all` exit 0 in ≤ 4 min on the default build
(`01 §1`: ~2m45s predicted); `GoldenRegressionValidation` exit 0 on Release, Debug, and both
`HECKE_PURE_INTEGER` settings; `./hacs --bench hecke 48 134217757 2` reports ≈ 5 s
(`03 §4.1`: 5.29 s at `-O2`).

**Effort.** 3–5 days. **Risk.** Low. Rollback: revert CMake defaults (results are unchanged by
construction).

---

### Phase 1 — The three algorithmic defects (and the mechanical substrate fixes)

**Goal.** Remove all super-cubic behaviour and ~90 % of the current run without touching the
arithmetic representation.

**Scope (consumer/Hecke layer, `02 §7` Tier 0–1):**
* **7.0 `ρ_n`** — replace `ComputeSymmetricPowerMatrixFM` (`FlatMatrix.cpp:1441-1486`) by the
  two-term recurrence in `O(d_V²)` multiplications, no `mod_nCr`, no `mod_pow`. *Implementation
  note:* the `O(d_V²)` form advances column `j → j+1` by multiplying by `(bx+dy)` and dividing by
  `(ax+cy)`, which needs `a ≠ 0` in `F_ℓ`; when `a ≡ 0` (e.g. `S = [[0,−1],[1,0]]`) run the
  mirrored recurrence in `b` — `det A = 1` guarantees `a` and `b` are not both zero — and take the
  `ρ_n(T)` / `ρ_n(S)` / `ρ_n(−I)` / `ρ_n([[1,0],[k,1]])` closed forms of 7.5 first. The result is
  a mathematically unique matrix, so bit-identity is automatic once the branch is right; the
  branch is exactly what `SymmetricPowerValidation` must cover.
  Remaining scope: tabulate
  `mod_nCr` via factorial/inverse-factorial tables per `(n, ℓ)` for remaining callers
  (`ModArithmetic.cpp:101-129`; the direct-formula variant sits commented out at `:114-128`,
  `03 §5.2 A1`). Closed forms for `ρ_n(T)` (upper unitriangular Pascal), `ρ_n(S)` (signed
  anti-diagonal), `ρ_n(−I)` (scalar), `ρ_n([[1,0],[k,1]])` (lower unitriangular) — **7.5**.
  Consumers: `LocalSystemSL2Z.cpp:166,211`, `HeckeCosetTables.cpp:79`, `HeckeTauTable.cpp:974`,
  `HeckeOperatorOnK.cpp:106`, `HeckeCrossChecks.cpp:133`, `BarCocycleH1.cpp:283`,
  `InducedLocalSystem.cpp:128`. Migrate the **24** live sites of the deprecated `Matrix`-returning
  `ComputeSymmetricPowerMatrix` (`01 §5.1`) to the FM version.
* **7.0b** memoise `ρ_n` in `HeckeTauTable::certify()` (`HeckeTauTable.cpp:1161`) as
  `build_xi_terms` already does (`HeckeTauTable.cpp:995-998`).
* **7.1 `Θ_eq` solve** — `HeckeOperatorOnK.cpp:348-352`: one augmented RREF of
  `[C_eq | Θ·C_eq]` (all `dim C^q_eq` RHS at once) or one factorisation + back-substitutions,
  replacing `dim C^q_eq` calls to `change_of_basis_fm` (`FlatMatrix.cpp:1489-1522`). The
  coordinates are unique (independent columns), so the result is bit-identical by mathematics;
  the A-N3 residual (`:363-384`, certificate C5) still re-verifies every column against the
  unfactored data.
* **7.2** memoise `ω_i·ρ_n(gγ_k)` and `ρ_n(δ_iγ_k)` on `(i, γ_k)` (`HeckeOperatorOnK.cpp:163,
  184, 485`): 125 → ≤ 24 products at `p = 2`.
* **7.3** `XiTerm::rho_g_gamma` by pool index, not by value (`HeckeTauTable.h:135`,
  `HeckeTauTable.cpp:978-1004`): 501 MB → 32 MB at `n = 1000`.
* **7.4** vacuous-relation short-circuit (`EquivariantCohomologyOnK.cpp:189-210, 326-359`):
  when `M == I` skip the block row; when `M == αI` emit a scalar block. `A_C1` shrinks
  1313 → 202 rows at even `n`. **Must preserve odd-`n` semantics (`H^* = 0`) exactly** — that is
  the FIX-negI purpose (`02 §5.4`; memory note "−I/odd-n base-model gap"); guarded by the golden
  grid's odd `n_sym = 1` points and Hecke oracle O2.
* **7.6** `FlatMatrix`-returning accessor beside `HeckeOperatorFamily::theta_flat`
  (`HeckeOperatorFamily.cpp:254-265`); the existing `std::vector<Matrix>` signature is
  plan-mandated (`HeckeOperatorFamily.h:193-201`) and stays (Q6).
* **`factor_basis_block` densification** (`Matrix.cpp:608` → `BlockFlatMatrix.cpp:1041-1182`,
  `:1125`): add prefix-sum block offsets to `BlockFlatMatrix` (`_get_block_start_{row,col}_idx`,
  `:1266-1288`, and `get_entry`, `:333-354`) and copy pivot rows block-wise; this alone removes
  the `(N_q + B_c)`-fold multiplier on the ≈ 22 % (`02 §2.1`). Move `factor_basis_block` out of
  `Matrix.cpp:553-638` into `BlockFlatMatrix.cpp` (defect #22).
* **Mechanical substrate fixes in the block-elimination hot loop** (`01 §6` items 6, 8, 10, 11,
  12, 13, 18, 19, 20, 24; `01 §2.4`): drop the six copies made solely to call the now-`const`
  `is_zero()`/`is_invertible()` (`BlockFlatMatrix.cpp:742,771,823,833,1327,1373`;
  `FlatMatrix.cpp:1197,1287`); swap-and-pop instead of `erase` (`:647`); in-place accumulation
  in `operator*` (`:516`); `unique_ptr` caches in `FlatMatrix` (`FlatMatrix.h:41-42`);
  const-correct `rank/kernel/image/is_invertible` and `BlockFlatMatrix::is_zero`; fused
  `operator-`; delete `_ensure_data_populated_if_empty`. Also #28 (`HeckeOperatorOnK.cpp:238-256`
  → two `memcmp`s) and #31 (`FpPoly.cpp:420,422` one RREF).

**Non-goals.** Layout changes, delayed reduction, any new class.

**Prerequisites.** Phase 0 (golden harness).

**Validations.** Keep green: all, plus `GoldenRegressionValidation` (every change here is
value-preserving). New: `SymmetricPowerValidation` — bit-comparison of the new `ρ_n` against the old
implementation. **The first draft's scope (all `n ≤ 200` × 6 generators + 50 random `Mat22`s ×
5 primes) is not runnable:** the *reference* side is the `O(n⁵)` code, at 5.94 s for a single
`n = 160` evaluation (`02 §5.5 C`), so the grid costs on the order of `10⁵` s. Rescoped to:
(a) **exhaustive** — every `n ≤ 48`, all of `{T, S, −I, ST, TS, [[1,0],[k,1]]}` and 20 fixed-seed
random `Mat22`s, at `ℓ ∈ {2,3,5,691,134217757}` (≈ 30 s against the old code); (b) **spot** —
`n ∈ {64, 96, 128, 160}` × `{T, S, generic}` × `ℓ ∈ {5, 134217757}` (≈ 60 s); (c) **structural**
— for all `n ≤ 1000`, assert the new implementation against the 7.5 closed forms and against
`ρ_n(A)·ρ_n(B) = ρ_n(AB)` and `ρ_n(A)^{-1} = ρ_n(A^{-1})` on 100 fixed-seed pairs (no `O(n⁵)`
reference involved), which is what actually covers the large-`n` regime; `ThetaEqSolveValidation` — new solve vs
old `change_of_basis_fm` on the golden grid, plus the residual certificate; `VacuousRelationValidation`
— even/odd `n` dimension table against the pre-7.4 code path.

**Exit criterion** (Release build, `--bench`; the baselines are `-O2` unless marked): `hecke 96
134217757 2` from 59.7 s (`03 §4.1`) to **≤ 8 s**; `cohom 128 134217757` from 59.4 s
(`03 §3.1`) to **≤ 12 s**; one `ρ_n` at `n_sym = 160` from 5.9 s (`-O0`, `02 §5.5 C`) to
**≤ 5 ms**; `HeckeBenchmarkSmoke` (`n = 100`) from 575 s (`-O0`) to **≤ 30 s**; fitted exponent
of `hecke` in `n_sym` **≤ 3.6** over `n ∈ {64, 96, 128}`.
*Why 3.6 and not 3.2 here.* The residual `≈ 0.4–0.5` of excess exponent measured today is
`_determine_and_set_flags_from_data()` rescanning a whole `d_V × d_V` block after every block
operation plus `_clear_cached_rref()` firing on every mutation (`03 §3.1`) — i.e. defect #4,
which Phase 1 explicitly does **not** touch (it is fixed by the bulk `BlockBuilder` in Phase 3).
Gating Phase 1 on ≤ 3.2 would gate it on work scheduled two phases later. The **≤ 3.2 permanent
guard of §4.4 therefore takes effect from Phase 3 onward**; Phase 1's job is to prove the `n⁴`
and `n⁵` terms are gone.

**Effort.** 6–9 days (parallelisable: `ρ_n` / `Θ_eq` / `factor_basis`+substrate — three agents).
**Risk.** Low: each item's output is checkable exhaustively or is a unique mathematical object.
Rollback per item (independent commits).

---

### Phase 2 — Arithmetic primitive layer (CPU, single-thread, bit-identity harness)

**Goal.** Make the arithmetic vectorisable and layout-aware without changing any consumer.

**Scope (new files in `src/ModArithmetic/`):**
* `ModCtx.h` — `ModCtx<Elt>` per D2; `mod_mul_barrett`, `shoup_precompute/shoup_mul`,
  `mont64_*`, `batch_inv` (Montgomery's trick); `k_max` and `ENGINE_CHECK` of the bound.
* `DenseBuf.h/.cpp`, `DenseView.h` — per D3 (layout, `ld`, invariant, structure tags, views).
* `Kernels.h/.cpp` — `gemm(C ±= A·B)` with all four layout combinations resolved by view
  flags, `u64` delayed accumulation with k-blocking, `k-j` inner loop order (`03 §7.2`),
  register-blocked microkernel (4×16 as in `04 App. A`) with an AVX-512-masked path
  (`-march=native` build) and a portable fallback; `gemv`/multi-vector `gemm_nt`; `axpy` with
  Shoup-form scalar; `trmm` for `UpperUnitri`/`LowerUnitri`; permutation apply for
  `SignedAntiDiag`; `transpose` (blocked, 16×16 tiles).
* `DenseElim.h/.cpp` — **in-buffer** RREF (no `vector<vector>` copy, defect #7,
  `FlatMatrix.cpp:1043-1051`): blocked recursive PLUQ/RREF per D5 on `DenseView`, panel width
  `b ∈ [128, 512]`, returns rank profile, pivot columns, and optional transform; `kernel`,
  `image`, `solve_multi_rhs`, `complement_basis` derived from it with the **same basis-choice
  rules** the current code uses (checked by golden).
* Retrofit — `FlatMatrix::operator*` (`FlatMatrix.cpp:878-888`), `_gaussian_elimination_core`
  (`:132-182`), `compute_row_echelon_form` (`:1043`), `get_rref_and_transform_matrix` (`:1094`),
  `compute_elimination_factor_and_apply` (`:1181-1258`), `inverse` (`:1284`) call the new
  kernels through a `DenseView` over `flat_data_`. `BlockFlatMatrix::_block_gaussian_elimination`
  (`BlockFlatMatrix.cpp:596-890`) keeps its structure but its per-block ops route through
  `Kernels`. `Matrix::operator*` untouched (retired in Phase 3).
* `RefLinAlg.h/.cpp` — the naive in-tree oracle (D6).

**Non-goals.** Threads, GPU, new block model, consumer changes.

**Prerequisites.** Phase 0; independent of Phase 1 (disjoint files; merge order P1 then P2).

**Validations.** Keep green: all + golden. New: `ModContextValidation` (every new primitive vs
the old `mod_*` at all regime boundaries `p ∈ {2, 3, 2^26.5±, 2^27, 2^31−1, 2^31+11, 2^32−5,
2^61−1, 2^63−25}`, 10⁶ fixed-seed samples each; `k_max` overflow assertion fires);
`KernelBitIdentityValidation` (new GEMM/GEMV/TRMM/RREF vs `RefLinAlg` and vs the *old*
`FlatMatrix` on fixed-seed inputs at sizes `{1, 2, 7, 16, 17, 64, 65, 129, 256, 517}`, all four
layouts, both widths, rank-deficient and structured inputs); `-DENGINE_SHADOW_LEGACY=ON` build
run of `HeckeEndToEndValidation`; `PerformanceSmokeValidation` (coarse floors: GEMM 512² ≥ 4
Gmodmul/s single-thread, RREF 1677×1419 ≤ 3 s — loose enough for WSL2 noise).

**Exit criterion.** `--bench` micro modes. *The first draft's floors were below measured naive
references and are raised here — an exit criterion the reference kernel already beats gates
nothing.* GEMM `n = 128` ≥ **15 Gmodmul/s** single core (`03 §7.2` measures 14.70 for the plain
kij-lazy reference at `-O3` and 16.29 for the AVX-512 intrinsics version, so 15 is "at least as
good as the reference"; the stretch target implied by `04 §8.2`'s ≥ 400 G on 16 threads is
≈ 25 G/core); RREF `1677 × 1419` ≤ **0.6 s** (the *naive* lazy-reduction reference is already
1.108 s and the scalar one 6.589 s, `03 §7.3`; a blocked kernel running at ~40–60 % of the GEMM
rate does 3.38 Gmodmul in 0.4–0.55 s); `cohom 128 134217757` ≤ **4 s**;
`GoldenRegressionValidation` exit 0.

**Effort.** 10–15 days. **Risk.** Medium (overflow bound, layout bugs) — mitigated by the
shadow build and the boundary-prime battery. Rollback: `ENGINE_BACKEND=legacy`.

---

### Phase 3 — Block-sparse data model, block kernel set, consumer migration, `Matrix` retirement

**Goal.** "Essentially all relevant matrix/vector operations" go through the block model; no
dense flattening inside kernel/image/factor paths; no per-cell assembly; `Matrix` gone from the
pipeline.

**Scope.**
* New `BlockPool`, `BlockMat`, `BlockBuilder`, `BlockView` (D3); block kernels: pattern-driven
  block GEMM (iterate CSR, fold kinds, CSE on pool ids), block GEMV/multi-vector, block
  `TRANSPOSE` as metadata, block structured RREF/kernel/image/`factor_basis`/`solve_multi_rhs`
  per D5 (panel driver over `DenseElim`), `to_flat`/`from_flat` in the L1 layout, block-wise
  `COMPARE`.
* **Consumer migration** (every site in `02 §1`, with the "loop of GEMVs → one GEMM" rewrites
  of `02 §7.9`):
  - `EquivariantCohomologyOnK.cpp`: C1/Z1 assembly via `BlockBuilder` with kinds
    (`I`, `−M`, `I−M`, pencils `β_lhs·I − β_rhs·M`), the `:195-197, :204-207, :348-354` cell loops
    gone; C2/Z2 block kernel returns a column-major block multi-vector; W2/H2 `factor_basis`
    with real `d_V`-wide blocks (`02 §7.11`); B2 as one GEMM; bases and `P_q` stored per
    `02 §7.10`; the seven conversions of `02 §2.2` deleted; **compatibility accessors**
    `get_H_eq_bases()` etc. still return `vector<Matrix>` (copy on demand) until every validation
    is migrated, then removed.
  - `HeckeOperatorOnK.cpp`: `Θ^{(q)}` as an `N_q × N_q` `BlockMat` with pattern from the τ-table
    (`02 §7.8`); fused route and route 2 as two predefined programs compared block-wise *as
    mathematical matrices* (`02 §6.1` engine note); Θ5/Θ10 as GEMMs; Θ6/Θ7 batched over
    `i_basis`, Θ7 using the existing `D1 ⊗ I` block form; Θ9 residual as a GEMM;
    `get_Theta_flat_matrices()` kept via a `to_flat` shim (consumed by `HeckeCrossChecks.cpp:449`
    and the JSON writer).
  - `HeckeCrossChecks.cpp`: β `FiberBlockTable` block-sparse (`:233-256`, density ≤ 1/m); X2
    reuses the C1 block assembly instead of the dense copy (`:329-353`); X3 one GEMM (`:365-468`);
    X4 no `set_entry` accumulation. `InducedLocalSystem.cpp:47-79` `M_H(g_r)` block-sparse
    (the `TODO Q8`).
  - `EquivariantCochainComplexMorphismOnK.cpp:250-302, 311-350`: M1/M3 as GEMMs — **but the
    accumulation order at `:255-284`/`:325-345` is the S6 bit-identity contract B6**; the GEMM
    must reproduce that exact per-column result (it does, by exactness — verified by
    `HeckeMorphismRegressionValidation`).
  - `SimplicialCohomology.cpp`: keep `Matrix` semantics for the trivial-coefficient layer but
    move storage to `FlatMatrix`/`BlockMat`; replace the `O(N²)` `std::find` simplex lookup at
    **all three sites** `02 §7.17` names — `SimplicialCohomology.cpp:191`,
    `LocalSystemUtils.cpp:28`, `EquivariantCochainComplexMorphismOnK.cpp:165` — with a
    **precomputed index vector or an ordered `std::map`, never `unordered_*`**: `02 §6.5(5)`
    records that no hash container exists anywhere in `Hecke/` or the morphism class *by design*,
    and R10 forbids introducing one on a result path. (`02 §7.17` says "hash map"; that
    recommendation and `02 §6.5(5)` are in direct conflict, and §6.5(5) wins.)
  - **7.20 — one source of truth for the L1 flat layout.** The `s·d_V + k` loop exists in three
    copies today (`EquivariantCohomologyOnK.cpp:111-119`, `HeckeOperatorOnK.cpp:113-120`,
    `Matrix.cpp:647-659`) and invariant L1 is asserted only by convention and by comments. Since
    Phase 3 makes `BlockMat` with `nbc = 1` *be* the layout, collapse the three into one
    `to_flat`/`from_flat` pair and delete the copies. Cheap here, painful later.
  - Absorb the two hand-rolled RREF-with-RHS solvers (`HeckeTauTable.cpp:228-263`,
    `BarCocycleH1.cpp:119-163`) and the ~20 raw `mod_*` loops (`01 §5.1`) into engine calls —
    **this is the API's acceptance test** (`01 §9.8`): if a loop survives, the API is missing a
    primitive (fused assembly, strided view, `axpy`, multi-RHS solve). **Conditional, per R2:**
    absorb these two *only if* the engine's `solve` reproduces their exact pivot rule and their
    ℤ-first / mod-`ℓ`-fallback policy; otherwise leave them in place and record why in the PR.
    The τ triangle-fill solve (`HeckeTauTable.cpp:783-910`) is **not** migrated in any phase.
  - `HeckeOperatorFamily.cpp:264` `to_matrix()` copy removed behind the 7.6 accessor.
* **`Matrix` retirement.** `LocalSystemSimplicialComplex.h:32` `SimplexRelation::M` becomes
  `FlatMatrix` (the structural pin, `01 §5.1`); `Matrix.h` no longer included by any pipeline
  TU; `Matrix`/`Matrix64` remain only for `MatrixValidation` and `HeckeModuleDecomposition`
  (`d_q ≤ ~20`, 0.004 % of runtime — **explicitly left alone**, `03 §4.3`; migrate only if the
  compatibility accessors make it free).
* Delete `BlockFlatMatrix`'s validation-only surface once `BlockFlatMatrixValidation` is
  re-pointed at `BlockMat` (keep the old class compilable behind `ENGINE_BACKEND=legacy`
  until Phase 4 ships, then remove).

**Non-goals.** Threads, tape, GPU. Decomposition/`FpPoly` (leave alone).

**Prerequisites.** Phases 1 and 2.

**Validations.** Keep green: all, golden, `HeckeMorphismRegressionValidation` (B5),
`HeckeCrossCheckValidation` (B3/B4), `HeckeIndependenceValidation` (B1/B8). New:
`BlockMatValidation` (structure: kinds, dedup/refcount, views, CSR order, builder, non-uniform
dims, both widths, primes as in Phase 0); `BlockEliminationValidation` (block RREF/kernel/
image/factor/solve vs `DenseElim` on the flattened matrix and vs the legacy `BlockFlatMatrix`
on fixed seeds, including the structural-shortcut paths `I`/`αI`/`±M`/`I−M` pivots);
`ConsumerMigrationValidation` (`-DENGINE_SHADOW_LEGACY=ON`: every migrated call site compares
against the legacy path on the golden grid; also asserts the raw-`mod_*`-loop count by a
build-time grep script in `docs/matrix-engine/tools/`). **The grep target is not zero** — a
literal "0 raw `mod_*` calls in the pipeline" is unachievable, since the tree today has **146**
`ModArithmetic::mod_*` call sites under `src/hacs/` and the largest concentrations are in files this plan
deliberately leaves alone: `FpPoly.cpp`, `HeckeModuleDecomposition.cpp`, `HeckeTauTable.cpp`'s
exact-ℤ solver, and every `*Validation.cpp`. The script therefore carries an **explicit
allow-list** (those files plus `ModArithmetic/` itself), the assertion is "zero outside the
allow-list", and *removing* a file from the allow-list is the unit of progress.
**All three new validations compare bases entrywise, never by span** — see D5b: the existing
`verify_flat_kernel_properties`/`verify_flat_image_properties` check only span and rank and
would not catch a changed kernel basis.

**Exit criterion.** `GoldenRegressionValidation` exit 0; peak RSS of `hecke 128 134217757 2`
≤ **120 MB**, against a baseline that **Phase 0's `--bench` must actually record** — `03 §4.4`
measures `cohom 128` at 434 MB but never `hecke 128`; the two are close at equal `n`
(`cohom 96` = 248 MB vs `hecke 96` = 247 MB), so ≈ 430 MB is the expected baseline, but the
criterion must be stated against a measured number, not an inferred one. `malloc` count ≤ 5 % of
today's 24 M (`03 §6`); projected memory at `n_sym = 1000` ≤ **1.5 GB** — `02 §5.1`'s ~400 MB
covers only the three representation fixes (Θ block-sparse, `XiTerm` pool, β blocks) and omits
the `C_eq` basis (330 MB), `Θ_eq` (325 MB) and the `factor_basis` workspace
(`dim_q × (n_rel+n_gen+dim_q)`, ≈ 485 MB at `q = 1`); the same audit extrapolates *measured* RSS
to ≈ 27 GB, so 1.5 GB is already a ~18× win and 1 GB was over-tight. `hecke 128 134217757 2`
≤ **6 s** single-thread; zero `Matrix` includes outside
`MatrixValidation`/`HeckeModuleDecomposition`.

**Suggested first deliverable inside Phase 3** (`01 §9.7`): rewrite the single call path
`EquivariantCohomologyOnK.cpp:214` / `:365` (`flat_kernel` → block elimination → dense flatten →
`set_entry` loops → re-block) before anything else. It is already chrono-instrumented by the
original author, defects #4, #6, #7, #8, #11, #13 and #27 all sit on it, and it is self-contained
and measurable — the cheapest possible proof that the data model is right.

**Effort.** 20–30 days (one agent on the model, then 3–4 on migration by file). **Risk.**
Medium-high: the largest diff of the programme; B6 accumulation order; L1 layout. Mitigation:
shadow build on every site, accessors for compatibility, one file per PR, golden after each.

---

### Phase 4 — The engine: tape/IR, passes, scheduler, CPU thread pool

**Goal.** The predefined-program execution model of D4 on the CPU, deterministic under any
thread count, with the pipeline's parallel axes exploited.

**Scope (new `src/Engine/`):** `Program`, `Recorder`, passes 1–6 of D4, `Executor`
with a pool of 32 worker threads and a **per-kernel** thread count — 16 (1 per core) for
memory-bound kernels, 32 for compute-bound ones (`04 §7.5`: 829 vs 477 GB/s L3-resident at
16 vs 32 threads, but 847 vs 1023 GFLOP/s the other way) — arena allocator with per-program
buffer lifetimes (removes the 24 M-malloc churn as a serialisation point, `03 §6 M1`), program
cache by shape signature, panel-driven elimination driver issuing batched `SCHUR_UPDATE`s.
Parallel axes wired in (`02 §4`): (a) coset reps `i` as a batched GEMM of the ≤ `m·8` distinct
products then scatter; (b) simplices `σ` as independent block rows; (c) the three `A_Cq`
kernels and three `Z^q_eq` computations concurrently (`02 §7.15`; step 2/3 stay sequential);
(d) `(p, r)` pipelines of `T_p_pow_direct`/`ComputeMultiOp` on the pool (`02 §7.7`;
`pipeline_cache_` stays a `std::map` — L3 — behind a mutex); (g) `d_q`/`dim_q` columns as GEMMs
(already Phase 3); (h) the multi-RHS solve; (i) τ certification per slot (read-only). **Not**
parallelised: τ *construction* (hazards 1–3, `02 §6.5`), any `FactorPoly`/witness search RNG
consumer (hazard 4).

**Non-goals.** GPU; dynamic rescheduling; autotuning.

**Prerequisites.** Phase 3.

**Validations.** Keep green: all + golden + `HeckeFpFilterValidation` (exact `PredicateStats`
counts, P4 — proves τ construction was not parallelised). New: `EngineTapeValidation` (record →
passes → execute equals direct execution; CSE/const-fold produce identical buffers; program
cache replay identical); `EngineDeterminismValidation` (golden grid under `ENGINE_THREADS ∈
{1, 4, 16, 32}` × `ENGINE_BATCH ∈ {0,1}`, hashes identical); `EngineArenaValidation`
(lifetimes, no use-after-free under ASan `Check` build).

**Exit criterion.** `hecke 256 134217757 2` ≥ **8× faster at the default thread count than at
`ENGINE_THREADS=1`**, and `hecke 128 134217757 2` ≥ **4×** — the split is deliberate: after
Phase 3 the `n = 128` problem is ≈ 6 s of work on a 9 MB, L3-resident matrix (`03 §2`), so
per-node overhead and the genuinely sequential parts (τ construction, which R1 keeps
single-threaded; `compute_cohomology`'s steps 2/3, which are *not* independent across `q`,
`02 §4(c)`) put an Amdahl floor well above 1/16 there. `family 128 134217757 2 2` overlaps its
two pipelines (wall ≤ 1.2× a single `hecke` run); hashes identical across all thread/batch
settings.

**Effort.** 15–20 days. **Risk.** Medium: allocator/threading bugs; hidden order dependence in
consumer code. Mitigation: ASan/TSan `Check` builds; determinism validation is mandatory in
`--all`.

---

### Phase 5 — CUDA backend

**Goal.** GPU execution of the same programs, bit-identical, with a static CPU/GPU partition.

**Scope (`src/Engine/cuda/`):** device buffer pool + residency tracking; pinned
staging pool of **≤ 128 MB** reusable buffers allocated with `cudaHostAlloc` from the start
(WSL2: no `cudaHostRegister`, ~300 MB pinned cap, pageable D2H 11× slower — `04 §7.1`); 2–3
streams; **CUDA graph capture per wavefront** (0.68 µs/node vs 24 µs launch+sync, `04 §1.4`);
kernels: blocked mod-`p` GEMM (`u32×u32→u64` delayed, `int64` accumulators, CUTLASS-shaped
tiling by hand, split-K for small `M,N`), batched small-block GEMM for `d ≲ 256`, panel
RREF + pivot-search reduction kernel (separate, as Linac), TRSM, transpose, canonicalise,
Shoup/Montgomery variants per regime, optional compile-time-prime specialisation (Q3). Device
introspection via `cudaDeviceGetAttribute` (CUDA 13 removed `clockRate`, `04 §1.0`). Cost-model
device assignment (pass 6) with constants from `04 §1.5, §6.2`. **Run the fused Θ route on the
CPU and route 2 on the GPU concurrently** (`02 §7.16`) — a stronger cross-check for free.

**Non-goals.** Tensor cores; out-of-core (Phase 6); multi-GPU.

**Prerequisites.** Phase 2 (kernels can be written against `DenseView` early); Phase 4 for
integration.

**Validations.** Keep green: all + golden + `EngineDeterminismValidation`. New:
`EngineCudaKernelValidation` (each device kernel vs its CPU twin on fixed seeds, all regimes,
edge shapes `1, 7, 17, 129, 517, 4097`, rank-deficient panels); `EngineCrossDeviceValidation`
(golden grid under `ENGINE_DEVICE ∈ {cpu, gpu, hybrid}`, identical hashes; plus an
`-DENGINE_VERIFY_DEVICE=ON` build run of `HeckeEndToEndValidation`); `EngineCudaMemoryValidation`
(pinned pool never exceeds cap; no pageable D2H — assert via a counter around every copy).

**Exit criterion.** `cohom 1000 134217757` in **≤ 1.5 s** on `ENGINE_DEVICE=gpu` vs
≈ 2–3 s CPU-16 (`04 §6.3`: 0.31 s + 11 ms PCIe predicted for the base kernels; the ×5 margin
covers `factor_basis` and driver overhead); blocked GEMM ≥ **2 TmodMAC/s** at `4096³` — note that `4096 > k_max = 1023` at this prime, so
this benchmark *must* k-block into ≥ 4 chunks with a reduction between them (D2); a kernel that
accumulates 4096 terms in one `uint64` is silently wrong, and `ModContextValidation`'s bound
assertion must fire on it; batched
`d = 100` GEMM ≥ 20× the CPU rate on a 256-instance batch; `EngineCrossDeviceValidation` exit 0.
**The GPU must never be enabled by default until the unblocked-kernel trap (`04 §6.3`, §5 risk R6)
is shown avoided: a naive port would be slower than the CPU.**

**Effort.** 20–30 days. **Risk.** High (WSL2 quirks, driver/toolkit drift, kernel correctness).
Rollback: `ENGINE_DEVICE=cpu` is always available and is the golden reference.

---

### Phase 6 — Batching across problems and the campaign for new cases

**Goal.** Turn the engine into a survey instrument and compute cases not computed before.

**Scope.** A sweep driver (`--campaign <spec-file>`) that enumerates `(n_sym, ℓ, p, r, q)`
jobs, groups them by shape signature, and submits batches to one program/CUDA graph (axis (e),
`02 §4`: many `ℓ` share `Mat22` tables and `n_k`; per-batch modulus); memory-lean mode for
large `n_sym` (route-2 comparison streamed block-by-block instead of both Θ resident; β/M_H
block-sparse; cross-checks (`HeckeCrossChecks`, `T_p_pow_direct`) **sampled** rather than
mandatory at scale — they are validation costs, `03 §4.2` — under an explicit `--certify=full|
sampled` flag reported in the JSON); streaming JSON for level (a) (`02 §7.19`); out-of-core
left-looking panels — `04 §6.5` puts the resident ceiling at `d ≲ 4500` (`N_max ≈ 45–50 k` after
workspace, on ≈ 13 GiB usable), so `d ≳ 3000` is the point at which the *streaming path must
exist and be tested*, not the point at which it becomes mandatory (`04 §7.3`); relax the 7/11/5 hard assertion into a model
descriptor (`02 §7.18`) so a refined model can follow. Campaign targets (§6): `n_sym` up to
~1000 at `ℓ ≈ 2^27` for `T_2, T_3, T_5`; a broad `(n_sym ≤ 200) × (many ℓ)` sweep; first
`ℓ < 2^64` results at moderate `n_sym`.

**Prerequisites.** Phases 4–5 (CPU-only campaign possible after Phase 4).

**Validations.** New: `CampaignSmokeValidation` (a 20-job batched sweep equals 20 individual
runs hash-for-hash); `CampaignCertificateValidation` (JSON records `certify` mode and all
in-process certificates C3–C6 still run unconditionally).

**Exit criterion.** ≥ 1000 `(n_sym ≤ 200, ℓ)` `T_2` results per minute batched on GPU
(estimate, §6); one `n_sym = 1000`, `ℓ = 134217757`, `T_2` run end-to-end ≤ 60 s; a
published table of new `A^{(1)}(T_p)` char-polys.

**Effort.** 10–15 days + campaign wall-clock. **Risk.** Medium (scope creep — see R7).

---

### Cross-cutting track V — determinism & validation

Runs in every phase; owns §4. Deliverables: the golden harness and its `--golden-emit`/`--golden-check`
CLI (P0); the shadow/verify build options (P2/P3/P5); the determinism validations (P4/P5); the
`docs/matrix-engine/tools/` scripts (raw-`mod_*` loop grep, cross-config diff runner mirroring
`Hecke/README.md`'s `HECKE_PURE_INTEGER` protocol); and a **performance ledger**
`docs/matrix-engine/perf-ledger.md` appended at every phase exit with the `--bench` numbers,
build config and commit.

---

## 4. Validation & bit-identity strategy

### 4.1 Golden-output harness (the backbone)

* **What is pinned.** Everything a rewrite could legitimately change but must not: bases
  (`C_eq, Z_eq, B_eq, H_eq`), projectors, `Θ_flat`, `Θ_eq`, `A^{(q)}` for `T_p`, `T_{p²}` (both
  routes), induced `H*` maps (S6), level-(b)/(c) JSON, dimensions. Hash = FNV-1a-64 over
  `(rows, cols, entries widened to uint64, L1 order)`; per-object, so a failure names the object.
* **Why hashes pinned on intermediates, not only invariants.** B1/B3/B5/B8 already pin
  `Θ_flat` and induced maps entrywise (`02 §6.1`); the S6 regression baseline (`41df5e2`) pins
  values captured on an old commit. Basis *choice* is part of the shipped semantics
  (`02 §6.5(1)`). If the owner relaxes this (Q1), the harness gains a second, weaker tier
  (dimensions, char-polys, `A^{(q)}` up to conjugacy) and the engine may pick better pivots.
* **Provenance.** Golden values are emitted once from the `-O0` `c8227c8` binary and checked in
  with the emitting commit, compiler, and build flags in the file header. Only an owner-approved
  re-baseline may change them; the change must be explained object-by-object.
* **Grid economics.** The grid runs in ~1 min on the Phase-1 build; it is part of `--all`.

### 4.2 Dual-route assertions kept

All of B1–B10 and C1–C16 (`02 §6.1–6.2`) remain in-process and unconditional, including at
campaign scale for C3–C6 (they are `O(d_q·d²)`/GEMM-shaped and cheap). B1/B3 are *full
mathematical-matrix* comparisons; with block-sparse Θ the comparison covers structurally-zero
blocks in one route that are materialised in the other (`02 §6.1` engine note). The route-2
requirement that the `Mat22` product stay exact over ℤ until one final reduction (I6) is
untouched. P1–P4 (`HECKE_PURE_INTEGER`) stay as they are; the cross-config diff protocol of
`Hecke/README.md` is scripted in `tools/`.

### 4.3 CPU-vs-GPU and old-vs-new equality

| Check | When | Cost |
|---|---|---|
| `-DENGINE_SHADOW_LEGACY=ON`: each migrated op runs legacy + engine, `memcmp` | P2–P3 CI, per PR | ≈ 2× |
| `-DENGINE_VERIFY_DEVICE=ON`: every GPU node re-executed on CPU, `memcmp` | P5 CI, per PR | ≈ 2× |
| `EngineDeterminismValidation` / `EngineCrossDeviceValidation`: golden grid under all runtime settings | every `--all` | ~minutes |
| fused route CPU ∥ route 2 GPU (B1) | production default after P5 | free |

Because every op is exact-integer with canonical outputs (D2/D4), a *single* differing bit is a
bug, never "noise" — the checks are strict `memcmp`, no tolerances anywhere.

### 4.4 Performance regression checks

`PerformanceSmokeValidation` with coarse floors (≥ 2× below the phase-exit numbers, to survive
WSL2 variance and a busy desktop, `03 §9`), `--bench` numbers appended to `perf-ledger.md` at
each phase exit, and the fitted `n_sym` exponent as a permanent guard against a return of super-cubic
bookkeeping (`03 §3.1`) — **≤ 3.6 from Phase 1, tightened to ≤ 3.2 from Phase 3**, because the
residual 0.4–0.5 of excess exponent is defect #4's per-block flag rescan, which Phase 3 removes
and Phase 1 does not (see Phase 1's exit criterion). All benchmark code must consume its results
(dead-code-elimination hazards, `04 App. A.2`).

---

## 5. Risk register (top 12)

| # | Risk | Likelihood / impact | Mitigation |
|---|---|---|---|
| R1 | **τ first-match-wins derivation order** (`HeckeTauTable.cpp:523-554`, build order `:681/:770/:950`): any reordering yields a different valid `τ` ⇒ different `Θ`, breaking B5 and every reference (`02 §6.5(1)`) | High if τ construction is touched / catastrophic | τ construction is **out of scope for all phases**; only certification (read-only, per-slot) is parallelised; `HeckeFpFilterValidation`'s exact `PredicateStats` counts (P4) detect any change in the geometry call sequence |
| R2 | **Underdetermined triangle-fill solve** (`HeckeTauTable.cpp:783-908`): particular solution fixed by column order, pivot rule "smallest |entry|, ties → lowest column", ℤ-first/mod-ℓ fallback on `HeckeOverflow` (`02 §6.5(2)`) | High if its solver is "absorbed" into the engine / catastrophic | The two hand-rolled solvers absorbed in Phase 3 are `HeckeTauTable.cpp:228-263` and `BarCocycleH1.cpp:119-163` **only if** the engine's `solve` reproduces the exact pivot rule; otherwise leave them and document why. The triangle-fill solve itself is not migrated. |
| R3 | Non-atomic global `PredicateStats` (`Predicates.cpp:19-20`) with asserted counts (P4) | Certain if τ geometry runs on >1 thread | Never call `QuadPoint`/`Predicates` from the pool; `EngineDeterminismValidation` runs `HeckeFpFilterValidation` under `ENGINE_THREADS=32` |
| R4 | **WSL2 CUDA quirks**: no `cudaHostRegister`, ~300 MB pinned cap, pageable D2H 5 GB/s, inflated launch latency, no `perf`/`gdb` (`03 §1.1`, `04 §7.1`) | Certain / medium | Own the staging buffers (`cudaHostAlloc`, ≤ 128 MB pool), CUDA graphs, counters asserting zero pageable copies; gprof + in-process timers instead of `perf` |
| R5 | **16 GB VRAM** (≈ 13 GiB usable): `d = 5000` needs 7.7 GB for `δ⁰` alone; `uint64` halves capacity (`04 §6.5, §7.3`) | Certain above `d ≈ 3000` / medium | uint32 everywhere possible; block-sparse Θ (43 %); left-looking out-of-core panels in Phase 6 (PCIe 55 GB/s makes streaming cheap) |
| R6 | **Naive-GPU trap**: an unblocked elimination on the 5070 Ti is 2.7× slower than the CPU yet 190× faster than today's code — a first CUDA port "looks great" for the wrong reason (`03 §7.4`, `04 §6.3`) | High / high | Phase 5 exit criterion is stated against the Phase-4 CPU number and the roofline, not against today; GPU off by default until `EngineCrossDeviceValidation` and the ≥ 2 T GEMM floor pass |
| R7 | **Scope creep**: tensor cores, Wiedemann, CUTLASS, autotuning, distributed, refining the model, optimising `HeckeModuleDecomposition`/`FpPoly` (0.004 %) | High / medium | Each phase has explicit non-goals; `04 §8.5`'s three traps are in the exit criteria; anything not in §3 needs an owner decision |
| R8 | **−I / odd-`n` semantics**: FIX-negI relations are vacuous at even `n` and *load-bearing* at odd `n` (`02 §5.4`; memory note); the 7.4 short-circuit or a kind-folding pass could drop them | Medium / high (silently wrong `H^*` at odd `n`) | Golden grid includes odd `n_sym = 1`; Hecke oracle O2. **Correction:** the Dickson exceptional locus is *not* the finite set `{(6,5),(12,5),(8,7)}` the first draft named — the shipped, S12-refined predicate is the **numerical semigroup** `n = a(ℓ+1) + b·ℓ(ℓ−1)`, `a,b ≥ 0`, `n > 0` (`IsDicksonExceptional`, `HeckeEndToEndValidation.cpp:75-105`; the `(ℓ+1) ∣ n` test alone is the older S7V version and misses e.g. `(20,5)`). Any grid or gate must **call that predicate**, not enumerate a set; in the §4.1 grid it fires at `(24,5)` and `(32,5)`. |
| R9 | **Silent overflow** of the delayed-reduction bound `k·(p−1)² < 2^64` (`04 §2.2`) | Medium / catastrophic (plausible wrong answers) | `k_max` in `ModCtx`, `ENGINE_CHECK` at every accumulation loop, `ModContextValidation` proves the assertion fires; regime `p ≥ 2^30.5` forced to eager Shoup |
| R10 | **Order dependence creeping in**: hash containers, thread-dependent accumulation, RNG stream consumption order (`02 §6.5(4,5)`) | Medium / high | Block-CSR sorted order; no `unordered_*` in result paths (grep in `tools/`); RNG consumers never parallelised; determinism validations in `--all` |
| R11 | **`Matrix` retirement ripple**: 480 lines / 35 files; plan-mandated signatures (`HeckeOperatorFamily.h:193-201`); `SimplexRelation::M` pin | Certain / medium | Compatibility accessors; one file per PR; shadow build; Q6 to the owner |
| R12 | **Oracle circularity**: most block-RREF machinery is exercised only by `BlockFlatMatrixValidation` (`01 §9.9`); the golden harness would freeze a latent legacy bug as "correct". **Sharpened:** that validation pins the *true scalar RREF* entrywise (`BlockFlatMatrixValidation.cpp:934-984`, against `FlatMatrix::get_row_echelon_form_as_flat_matrix`) but pins kernel and image bases only by **rank + mutual span inclusion** (`:1086`, `:1192`) — so today's suite would *not* notice a changed kernel basis, which is precisely the convention D5b shows everything downstream rests on | Medium / high | `RefLinAlg` naive oracle and the algebraic-identity sweep are independent of both substrates; certificates C3–C5 are independent of the solver; every new basis check is **entrywise**; disagreement between golden and `RefLinAlg` is escalated, never patched over |

Also noted: `NDEBUG` now disabling the `BlockFlatMatrix.cpp:1120-1133` asserts (P0 policy);
toolchain drift (GCC 11.4 vs 15; CUDA 13 API removals); `-O3` exposing latent UB (run the
`Check` sanitizer build in every phase).

---

## 6. Target-capability table (estimates)

**Method.** Work per full `T_p` run modelled as modular MACs `W ≈ c·d³`, `d = n_sym + 1`, from
`04 §6.2` (base cohomology `≈ 6.1e2 d³` after 25 % structural saving) plus the Hecke-layer
terms after Phases 1–3: `factor_basis` ×2 per degree on real blocks (`≈ 3e3 d³`), `Θ·C_eq`
GEMM at 43 % block density + `C_eq` factorisation + multi-RHS solve (`≈ 2.5e3 d³`), A-N3
residual GEMM (`≈ 9e2 d³`), Θ assembly (`≤ 24·d³` at `p = 2`, `∝ m` in general — negligible).
**`W_Tp ≈ 7e3 · d³`.** Rates (`04 §1.5, §6.2`): CPU-16 `2.7e11` modMAC/s (regime b),
GPU-blocked `2.0e12`; regime (e) `ℓ < 2^64`: CPU `1.4e10`, GPU `6.3e11`. Memory from
`02 §5.1` after 7.3/7.8/7.12 (Θ at 43 %, bases as single buffers). Estimates carry ±3×
uncertainty; the Hecke prime `p` enters mainly through `m = p^r + p^{r-1}` in Θ assembly and
τ-table geometry (cheap) and through Θ's block density (saturating at dense), so `p ≤ ~100`
changes runtime by < 2×. Cross-checks (`HeckeCrossChecks`, `T_p_pow_direct`) are excluded —
they are sampled at scale (Phase 6).

**"Today (extrapolated)" — method, and a correction.** The first draft's figures for this column
(≈ 3000 s at `n = 200`, ~6 h at 500, ~3 days at 1000) implied an exponent of ≈ 2.3–2.7, which is
*below* every exponent actually measured. Today's code grows at `α ≈ 3.4–3.6` for the linear
algebra (`03 §3.1, §4.1`), `α ≈ 3.9` for `HeckeOperatorOnK::compute()` and `α ≈ 4.2–5.0` for the
`ρ_n` term (`02 §5.5 B, C`), and the `ρ_n` term alone dominates beyond `n ≈ 200`: `02 §5.5 C`
states outright that at `n_sym = 1000` **one** `ρ_n` evaluation takes on the order of an hour and
a pipeline needs 300–420 of them, i.e. ≈ 300–420 h before any linear algebra. The column below is
therefore restated from the measured 575 s at `n = 100` with `α = 3.5` for the linear-algebra
part plus the `ρ_n` term taken directly from `02 §5.5 C`. The correction makes the *case for the
programme stronger*, not weaker; it is fixed here so nobody plans against a 15×-optimistic
"today".

| Regime | `n_sym` | `ℓ` | level | `W_Tp` | RAM / VRAM | CPU-16 (P4) | GPU (P5) | Today (extrapolated) | Status |
|---|---|---|---|---|---|---|---|---|---|
| A | 100 | 2^27 | `p ≤ 5`, `r ≤ 2` | 7e9 | < 50 MB | 0.03 s (+ overhead ≈ 0.3 s) | overhead-bound ≈ 0.1 s | 575 s (`-O0`) | routine; **batch** |
| B | 200 | 2^27 | `p ≤ 11` | 5.7e10 | 0.1 GB | 0.2 s | 0.03 s + launch | **~3 h** | sweep-scale: ~10³ jobs/min GPU-batched |
| C | 500 | 2^27 | `p ≤ 11` | 8.8e11 | 0.4 GB | 3.3 s | 0.5 s | **~5–6 days** | **new** |
| D | 1000 | 2^27 | `p ≤ 11`, `r ≤ 2` | 7e12 | 1–1.5 GB | 26 s | 3.5 s + 0.1 s PCIe | **~5–7 weeks** | **new** (Phase 6 headline) |
| E | 2000 | 2^27 | `p ≤ 5` | 5.6e13 | 4–6 GB | 3.5 min | 30 s | — | **new**; VRAM-resident |
| F | 3000–5000 | 2^27 | `p ≤ 3` | 1.9e14–8.8e14 | 10–40 GB RAM; > VRAM | 12–55 min | 1.5–8 min + streaming | — | needs out-of-core (Phase 6); `uint32` only |
| G | 200 | `2^32 ≤ ℓ < 2^64` | `p ≤ 5` | 5.7e10 | ×2 | 4 s | 0.1 s | (S13 validation only) | **new**; GPU-preferred (44×) |
| H | 1000 | `ℓ < 2^64` | `p ≤ 3` | 7e12 | 2–3 GB | 8 min | 11 s | — | **new** |
| I | 100–200 | many `ℓ` | `p ≤ 11` | per job as B | small | 16 jobs in parallel | 32-job graph batches | one at a time | the "matrix VM" payoff |

Levels `p^r` with `r ≥ 2` use the recursion (free, `03 §4.2`); the direct double-coset route is
a cross-check and is sampled. `HeckeModuleDecomposition` remains negligible up to
`n_sym ≈ 2000` (`d_q ≈ n/6`, `03 §4.3`) — **but not beyond it, which regimes E–F reach.** Its
`O(d_q⁴)` core (`02 §5.2`) runs on the untouched, un-vectorised `Matrix` class at ≈ 0.9
Gmodmul/s (`03 §7.2`, "current" column): `d_q ≈ 333` at `n = 2000` is ≈ 13 s (≈ 6 % of regime E's
CPU time — still fine), but `d_q ≈ 833` at `n = 5000` is ≈ 9 min against regime F's 12–55 min,
i.e. **15–70 %**. Phase 3's decision to leave `HeckeModuleDecomposition`/`FpPoly` alone is
correct for regimes A–D and must be **revisited before regime F is attempted**; the cheapest fix
at that point is to route only its `rank`/`kernel`/`inverse` calls through the engine, which the
compatibility accessors make nearly free. Flagged as Q10.

---

## 7. Appendix — open questions for the owner (plan-changing only)

| # | Question | Why it changes the plan |
|---|---|---|
| Q1 | Must the new engine reproduce the **legacy basis choices** (kernel/complement bases, projectors) bit-for-bit, or only the mathematically canonical objects (`Θ_flat`, `A^{(q)}`, `dim`, JSON) with bases allowed to differ? **Now costed: D5b writes the six conventions down.** The expensive ones are the kernel-basis convention (free columns ascending, unit at the free column, `−RREF[i][j]` at pivot `i`) and the augmented-RREF definition of the transform `U`; a textbook FFPACK-style PLUQ produces neither by default. | Strict: Phase 2/3 elimination must implement D5b verbatim (default assumption here), and `FpPoly.cpp:422-425`'s hard-coded normalisation check keeps it honest. Relaxed: the engine may use structural pivoting freely; S6's B5 baseline (`41df5e2`) and the golden basis hashes need re-capture — one documented, object-by-object re-baseline. Note the *pivot rule itself* is free either way: RREF, its pivot columns and the rank are unique regardless. **Decided (owner, Phase 0): relaxed — canonical objects only.** The golden harness therefore gates on tier A (`dim H^q`, `Θ^{(q)}_flat`, char-poly/rank/trace of every `A^{(q)}`, decomposition invariants, redacted JSON) and captures the legacy bases, projectors and change-of-basis matrices as tier B, which is compared and reported on every run but fails the validation only under `GOLDEN_STRICT=1`; D5b stands as documentation of the current conventions, not as a constraint the new elimination must honour. |
| Q2 | Is a **header-only CUTLASS** dependency acceptable if the hand-written GPU GEMM stalls below ~40 % of the INT32 roofline? | Changes Phase 5 effort by ~2× either way; the repo culture says no third-party code. |
| Q3 | May the build **specialise on a list of hot primes** (`-DENGINE_HOT_PRIMES=…`, Linac's ≈ 50 % GPU win), and/or use NVRTC JIT at runtime? | JIT is a runtime dependency on the CUDA toolkit; a compile-time list is zero-dependency but must be maintained per campaign. |
| Q4 | Priority between **larger `n_sym` at `ℓ ≈ 2^27`** (regimes C–F) and **`ℓ < 2^64`** (G–H)? | 64-bit work is GPU-first and would pull Phase 5 kernels for regime (e) earlier; otherwise they are last. |
| Q5 | At campaign scale, may the **external cross-checks** (`HeckeCrossChecks` β-route, `T_p_pow_direct`) be *sampled* (with the mode recorded in the JSON), while the in-process certificates C3–C6 stay unconditional? | Regime D–F runtimes assume sampling; requiring them always roughly doubles cost and memory (β blocks). |
| Q6 | May the plan-mandated `std::vector<Matrix>` signatures (`HeckeOperatorFamily::theta_flat`, `HeckeOperatorFamily.h:193-201`; `get_H_eq_bases()` consumers) be **amended** in `docs/implementation/hecke_action_implementation_plan.md` once compatibility accessors exist? | Decides whether `Matrix` can be fully retired (Phase 3) or must persist at the API boundary. |
| Q7 | Which **first new cases** are scientifically most valuable — one `n_sym ≈ 1000` at a single large `ℓ`, or a broad `(n ≤ 200) × (many ℓ) × (many p)` survey? | Orders Phase 6's driver work (out-of-core vs batching) and decides whether Phase 5 must precede Phase 6. |
| Q8 | Is the **7/11/5 model refinement** (larger level, `Γ_0(N)` base; `HeckeOperatorOnK.cpp:61-66`) on the horizon? | If yes, the block grid stops being constant and `N_q`-driven planning plus hash-map simplex lookup (`02 §7.17–7.18`) move from Phase 6 into Phase 3. |
| Q9 | Note: `Hecke/README.md` still states S13 has not landed and `--all` does not exit 0 (`README.md:10-11`, `:143-147`); both are stale (`HeckeExtendedRegimeValidation` is registered; `--all` is green). May the README be corrected in Phase 0? | Documentation only; flagged so the team does not act on stale guidance. |
| Q10 | **Regime F only:** may `HeckeModuleDecomposition`/`FpPoly` be migrated off the legacy `Matrix` after all? Phase 3 leaves them alone on the strength of `03 §4.3` ("0.002–0.004 %"), which holds through regime E; at `n_sym = 5000` its `O(d_q⁴)` core on the un-vectorised `Matrix` is 15–70 % of the run (§6). | Decides whether regime F needs a Phase-6 addendum, and whether `Matrix` can finally be deleted rather than merely quarantined. |
| Q11 | **Which `image()` is right?** `FlatMatrix::image()`'s scalar fast path (`FlatMatrix.cpp:1411-1420`) returns `e_j` where `Matrix::image()` (`Matrix.cpp:440-452`) and `BlockFlatMatrix::flat_image()` (`BlockFlatMatrix.cpp:1646-1675`) return `α·e_j`, for `A = α·I`, `α ∉ {0,1}`. No test exercises it and I could not establish that any shipped path reaches it. | The golden harness will freeze whichever behaviour it observes. If this is a bug, fix it in Phase 0 *before* emitting golden values; if it is intended, D5b must say so and all three classes must be made to agree. Cheap now, permanent later. **Decided (owner, Phase 0): `α·e_j` — `FlatMatrix::image()` was the outlier and was fixed** to agree with `Matrix::image()` and `BlockFlatMatrix::flat_image()`, before any golden value was emitted; `SubstrateDifferentialValidation` now pins the agreement of all three. |
| Q12 | May **FLINT `nmod_mat` be used as a test-only oracle** (never in the production build), as `04 §8.4` explicitly suggests? D6 currently rules out all third-party code, leaving `RefLinAlg` — code we wrote — as the only independent oracle, which is exactly the circularity R12 is about. | Adds a genuinely external check on the new kernels at the cost of a dev-only dependency. A middle road: keep it out of the tree and use it once, offline, to bless the Phase-0 golden file. |
| Q13 | Should `--all` stay a single gate? Phase 0 brings it to ≈ 2m45s, but this plan adds the golden grid (~1 min), `EngineDeterminismValidation` (thread × batch grid, "~minutes"), `EngineCrossDeviceValidation` (device grid) and `SubstrateDifferentialValidation`; by Phase 5 `--all` plausibly costs 15–30 min again. | Either accept that, or tier it: `--all` = fast correctness gate, `--all-full` = the grids, run per-PR in the background. The per-phase exit criterion "`--all` exit 0" needs to name which one. **Decided (owner, Phase 0): tier it.** Every validation carries a `fast`/`standard`/`slow` tier printed by `--list`; `--all` runs fast+standard and `--all-full` adds slow, so the per-phase exit criterion "`--all` exit 0" means `--all`, while the Hecke acceptance gate (whose `HeckeBenchmarkSmoke` is the only `slow` entry) means `--all-full`. |

---

## 8. Review log

Adversarial review of the first draft, September 2026. Every line: **what was wrong → what
changed → evidence**. Findings that are judgement calls rather than errors were *not* applied
silently; they went into §7 as Q10–Q13 and as the extension of Q1. No source file and none of the
four audit documents were modified.

**Arithmetic and the D2 regime table (the most consequential group).**

1. D2's regime boundary `p < 2^26.5` excluded the project's own default prime
   (`134217757 ≈ 2^27.0 ≥ 2^26.5`), putting it in the next row where "`k ≤ 4` makes delay
   pointless" → boundaries recomputed from `k·(p−1)² < 2^64` (`p < 2^30.5` delayed,
   `2^30.5 ≤ p < 2^31` eager Shoup), with a boxed note explaining that `2^26.5` is doc 04's FP64
   *single-product* boundary, not the `uint64` one → `04 §1.5` itself places `2^27.0` in regime
   (b) with `k ≤ 1024`, and `04 §2.2`'s table gives `k ≤ 4` only at `p = 2^31`. Read literally,
   the draft forfeited the 4–5× (512 G vs 120 G) the whole design rests on.
2. `k_max` given as "= 1024 at 2^27" → **1023** at the actual prime; 1024 holds only at exactly
   `p = 2^27` → `(134217756)² = 18 014 406 025 675 536`, and `1024 ×` that exceeds `2^64`.
   Added the runtime-computed-`k_max` rule and the `≥ 256 / ≥ 16` intermediate points.
3. Regime `2^31 ≤ p < 2^32` was to use "Shoup, as above" → corrected: Shoup-32 needs `2p < 2^32`
   for its lazy `[0,2p)` representative, so that regime needs Barrett-64 or promotion to the
   64-bit path → standard Shoup/Harvey bound.
4. **New correctness defect (#33), missed by all four audits:** `ModArithmetic.cpp:41-45`
   `mod_add` computes `a + b` in `uint32_t` and wraps for `p > 2^31` (at `p = 4294967291`,
   `a = b = p−1` returns `4294967284`, should be `4294967289`) → added to Phase 0 next to
   defect #2 → the 64-bit twin `mod_add64` (`:172-180`) already carries the wrap test
   `if (r < a || r >= p) r -= p;` and an explanatory comment, so this is a 32-/64-bit asymmetry.
   It is reached through `mod_nCr_small` by every `ρ_n`. Flagged as a blocker for Phase 0's
   differential harness, which was going to run at exactly `p = 4294967291`.
5. No design consequence was drawn from `04 §1.2`/`§8.5(2)` → added "AVX-512 on Zen 4 — no width
   dividend" to D2 → AVX2 `vpmuludq` 41.2 G lane-mul/s vs AVX-512 41.0 G, same core; AVX-512 is
   adopted for `k`-masks, instruction density and `vpermi2*`/`vpcompress*`, not throughput.

**Defect coverage and file:line references.**

6. Defect #9 (`Matrix`'s RREF cache is never invalidated while `data` is public — severity **C**)
   was the only ranked defect scheduled in no phase, and `Matrix` survives Phase 3 → added to
   Phase 0 with a regression case → `01 §6` table, `Matrix.h:41`, `Matrix.cpp:286`. Also recorded
   why #16 is deliberately unscheduled.
7. "the 16 live sites of the deprecated `ComputeSymmetricPowerMatrix`" → **24** → 12 in
   `LocalSystemSL2Z.cpp` + 4 each in `HeckeTessellationSmokeValidation.cpp`,
   `HeckeTessellationValidation.cpp`, `HeckeMorphismRegressionValidation.cpp`. (The "16" is
   inherited from `01 §5.1`, which is also wrong; the audit is not edited here.)
8. `get_Theta_flat_matrices()` cited at `HeckeCrossChecks.cpp:456` → **`:449`** → `:456` is a
   `for` header seven lines later.
9. Four function-boundary citations off by 1–3 lines → `BlockFlatMatrix.cpp:596-891 → 596-890`,
   `1041-1183 → 1041-1182`, `Matrix.cpp:553-641 → 553-638`, `HeckeTauTable.cpp:523-553 → 523-554`,
   `978-1003 → 978-1004`, and the `build_xi_terms` memo cited at `:993-998` → the actual
   `cache.find`/`emplace` is `:995-998`.
10. Defect #32's `USE_SCALAR_KERNEL` was described as one site and "never defined" → there are
    **two** `#ifdef` sites (`EquivariantCohomologyOnK.cpp:145` and `:275`) and the macro **is**
    defined for CUDA TUs (`CMakeCache.txt: CMAKE_CUDA_FLAGS=-DUSE_SCALAR_KERNEL`); it is
    undefined only for the C++ TUs where the dead branches live.

**Provenance and build mechanics.**

11. "`CMakeCache.txt: CMAKE_BUILD_TYPE=Debug`" implied a committed file (`01 §1` calls it "the
    committed in-source cache") → it is **git-ignored** (`.gitignore`), so a fresh clone gets an
    *empty* flag set instead → restated, and Phase 0 now says to delete the stale in-source cache
    and reconfigure, since a new CMake default cannot override an existing cache entry.
12. "`-O0` costs **5.3–8.3×** measured on every workload" mixed two disjoint measurement sets →
    split into 5.3–7.3× end-to-end (`03 §4.4`) and 5.9–8.3× on substrate microbenchmarks
    (`01 §1`, where the scalar `mod_mul` loop is only 2.5×).
13. "Delayed accumulation + transposed operand measured **12–23×** on exactly the `d_V = 17…129`
    sizes" → **5–21×** on those sizes; 12–23× is the `n = 64…512` band → `03 §7.2` states
    verbatim "Relevant block sizes here are `d_V = 17…129` … the 5–21× band".
14. Phase 0 step 5 said to emit golden values "from `c8227c8`" → `--golden-emit` does not exist at
    `c8227c8`; the harness commit must be **cherry-picked onto** it, touching only `Golden/` and
    the registry. Otherwise the step is unexecutable as written.
15. Phase 0's new configs would not reach `kernel.cu` → added: a custom config needs
    `CMAKE_CUDA_FLAGS_<CONFIG>` as well as `CMAKE_CXX_FLAGS_<CONFIG>`, `-march=native` must go
    through `-Xcompiler`, and the recommendation is to put `--bench` in a plain `.cpp` TU instead.

**Internal consistency.**

16. §1's decision table labelled bit-identity "D5", but §2's D5 is *structured elimination* and
    bit-identity is D7 → relabelled, including the "makes D5 achievable" back-reference.
17. The dependency graph drew P2 as a child of P1 while the text said "P2 … independent of Phase
    1" and "P1 ∥ P2" → graph redrawn so both branch from P0, and P5/P6 edges made explicit.
18. Phase 1's exit gate "fitted exponent ≤ 3.2" is not reachable in Phase 1 → relaxed to ≤ 3.6,
    with the ≤ 3.2 permanent guard (§4.4) moved to Phase 3 onward → the residual 0.4–0.5 of
    excess exponent is `_determine_and_set_flags_from_data()` + `_clear_cached_rref()`
    (`03 §3.1`), i.e. defect #4, which Phase 1 explicitly does not touch.
19. Phase 2's exit floors were **weaker than measured naive references**: GEMM `n = 128`
    ≥ 10 Gmodmul/s against a 14.70 reference, RREF `1677 × 1419` ≤ 1.5 s against a 1.108 s naive
    lazy reference (`03 §7.2, §7.3`) → raised to ≥ 15 Gmodmul/s and ≤ 0.6 s, with the derivations
    stated.
20. Phase 3's RSS exit compared `hecke 128` against `cohom 128`'s 434 MB — a different workload,
    and `hecke 128` is nowhere measured → criterion now requires Phase 0 to record the real
    baseline (with the `cohom 96` ≈ `hecke 96` evidence for why ≈ 430 MB is expected).
21. Phase 3's "≤ 1 GB at `n_sym = 1000`" cited `02 §5.1`'s ~400 MB, which covers only three
    representation fixes → raised to ≤ 1.5 GB, itemising `C_eq` (330 MB), `Θ_eq` (325 MB) and the
    `factor_basis` workspace (≈ 485 MB) that the 400 MB omits, and noting the same audit's 27 GB
    *measured*-RSS extrapolation. §6's "1–1.5 GB" and this criterion now agree.
22. `ConsumerMigrationValidation` asserted "the count of raw `mod_*` loops in the pipeline is 0" →
    impossible: 146 `ModArithmetic::mod_*` call sites exist under `src/hacs/`,
    concentrated in files this plan deliberately leaves alone → replaced with an explicit
    allow-list, "zero outside the allow-list", and removal from the allow-list as the unit of
    progress.
23. Phase 4's "≥ 8× at 16 threads" was stated at `n = 128`, a 9 MB L3-resident problem reduced to
    ≈ 6 s by Phase 3, where Amdahl (sequential τ construction per R1; `compute_cohomology` steps
    2/3 not independent across `q`, `02 §4(c)`) puts a floor well above 1/16 → split into ≥ 8× at
    `n = 256` and ≥ 4× at `n = 128`.
24. Phase 5's "blocked GEMM ≥ 2 TmodMAC/s at `4096³`" contradicted D2's own bound → annotated:
    `4096 > k_max = 1023`, so the benchmark must k-block into ≥ 4 chunks and
    `ModContextValidation`'s assertion must fire on a kernel that does not.
25. Phase 6's out-of-core trigger `d ≳ 3000` was presented as the capacity limit → `04 §6.5` puts
    the resident ceiling at `d ≲ 4500`; restated as "the point at which the streaming path must
    exist and be tested", not the point at which it is mandatory.
26. R9's "regime `2^26.5 ≤ p` forced to eager Shoup" → `p ≥ 2^30.5`, following correction 1.

**Correctness of the science-facing numbers.**

27. §6's "Today (extrapolated)" column implied `α ≈ 2.3–2.7`, below every measured exponent →
    recomputed (B ~3000 s → ~3 h; C ~6 h → ~5–6 days; D ~3 days → ~5–7 weeks) with the method
    stated → measured `α ≈ 3.4–3.6` (`03 §3.1, §4.1`), `α ≈ 3.9` for `compute()` and
    `α ≈ 4.2–5.0` for `ρ_n`, plus `02 §5.5 C`'s explicit "one `ρ_n` ≈ an hour at `n = 1000`,
    300–420 per pipeline". The correction strengthens the case for the programme.
28. R8 named the Dickson exceptional locus as the finite set `{(6,5),(12,5),(8,7)}` → it is the
    **numerical semigroup** `n = a(ℓ+1) + b·ℓ(ℓ−1)`, `n > 0` → the shipped, S12-refined predicate
    `IsDicksonExceptional` (`HeckeEndToEndValidation.cpp:75-105`); the `(ℓ+1) ∣ n` form is the
    older S7V version and misses e.g. `(20,5)`. §4.1's grid now calls the predicate, and it fires
    there at `(24,5)` and `(32,5)`.
29. §6 claimed `HeckeModuleDecomposition` "remains negligible up to `n_sym ≈ 2000`" and Phase 3
    leaves it on the legacy `Matrix` → true through regime E, but its `O(d_q⁴)` core is ≈ 15–70 %
    of regime **F** (`d_q ≈ 833` at `n = 5000`, ≈ 9 min at the `Matrix` class's measured
    ~0.9 Gmodmul/s against F's 12–55 min) → added, with Q10 for the owner.
30. `SymmetricPowerValidation` as scoped (all `n ≤ 200` × 6 generators + 50 random matrices ×
    5 primes) is **not runnable**: the *reference* side is the `O(n⁵)` implementation at 5.94 s
    for one `n = 160` evaluation, giving ≈ 10⁵ s → rescoped into exhaustive (`n ≤ 48`), spot
    (`n ∈ {64,96,128,160}`) and structural (`n ≤ 1000`, closed forms + `ρ_n(A)ρ_n(B) = ρ_n(AB)`,
    no `O(n⁵)` reference) tiers.

**Under-specified design (the owner's two explicit requirements).**

31. "Row- or column-major depending on the next operation" was named, not designed, and D3's
    "a transpose is a flag flip … no copies" contradicts the measurement it cites → D3 now
    separates the *logical* transpose (index-mapping flag, free) from the *physical* relayout
    (blocked 16×16 copy, materialised once, arena-cached), and states the layout-assignment rule
    as a four-step, cost-weighted, schedule-independent algorithm → the measured 20×
    (`01 §3.4`) comes from streaming `B` contiguously in `k`, which a flag flip does not achieve.
32. The VM's "group → batch → CPU/GPU" was named without a grouping key or a cost model → pass 5
    now has an explicit key `(op, m, n, k, layouts, elt-width, k_bound, device)` with a
    deterministic instance order and the observation that no batch introduces a reduction; pass 6
    now cites `04 §6.4`'s crossover inequality with the measured constants and the 0.68 µs
    in-graph launch term, and records the chosen device *in the program*.
33. "Compiled programs are cached and replayed … every `ℓ` at fixed `(n_sym, p, r, q)`" is unsafe
    as stated → added the cache-poisoning caveat: the τ pattern is **not** unconditionally
    `ℓ`-independent, because the triangle-fill solve is ℤ-first with a mod-`ℓ` fallback
    (`02 §6.5(2)`) that can change a chain's support. The shape signature must hash the actual τ
    pattern, and a miss must re-record, never replay.
34. Split-K on the GPU was listed in Phase 5 while D4 says "no atomics on results" → added the
    reconciliation: partials must be canonicalised to `[0,p)` before combining (or the total `k`
    must satisfy `k_max`), after which any reduction tree or atomic order is bit-identical.

**The bit-identity contract itself — the largest addition.**

35. D4 asserted that "kernel/image/complement bases are derived by the same fixed rules the
    current code uses (verified by the golden harness)" without saying what those rules are, which
    makes Phase 2/3 unimplementable and Q1 un-answerable → added **D5b**, a table specifying all
    six conventions verbatim with file:line, plus the two consequences and the test-coverage gap.
    The substantive findings inside it:
    * The **kernel-basis convention** (free columns ascending; unit at the free column;
      `−RREF[i][j_free]` at pivot `i`) is the root of `C_eq`, `Z_eq`, `W`, `B_eq`, `H_eq`, `P_q`
      and hence of every entry of `Θ_eq`, `A^{(q)}`, the induced `H*` maps and the shipped JSON.
    * `get_rref_and_transform_matrix` returns the trailing block of `RREF([A | I_m])`, eliminated
      over **all** `n+m` columns, so `U` **is** unique given `A`. The natural reimplementation
      (accumulate row operations while eliminating `A` only) satisfies `U·A = RREF(A)` and is
      still not bit-identical on rank-deficient `A`. Sole caller `BlockFlatMatrix.cpp:652`.
    * `get_true_row_echelon_form_as_flat_matrix` emits rows in ascending pivot-column order, and
      `factor_basis_block` indexes that arithmetically (`rref_row = independent_relations + i`,
      `Matrix.cpp:625-634`) — any other row order yields a **silently wrong projector**.
    * `FpPoly.cpp:422-425` hard-codes the kernel normalisation and throws if it changes — a
      structural dependency inside a file the plan otherwise leaves untouched.
    * The legacy block layer's pivot rule is a **structural heuristic**
      (`get_pivot_block_priority`, `BlockFlatMatrix.cpp:581-592`: `I` before `−I` before other
      scalars before general), not the topmost-non-zero rule D4 proposes. Harmless for the RREF
      (unique) but not for anything block-shaped; D4 now says so.
    * `FlatMatrix::image()`'s scalar fast path returns `e_j` where the other two classes return
      `α·e_j` (**new defect #34**) — surfaced as Q11 because it must be resolved *before* golden
      values are emitted, and I could not establish whether any shipped path reaches it.
36. R12 sharpened accordingly: `BlockFlatMatrixValidation` pins the true scalar RREF entrywise
    (`:934-984`) but pins kernel/image bases only by rank + mutual span inclusion (`:1086`,
    `:1192`) → today's suite would **not** catch a changed kernel basis. Every new basis check in
    this plan is now required to be entrywise. Also noted that the block layer's own
    RREF-idempotency self-check is dead in every build (`#ifdef DEBUG_BLOCKFLATMATRIX`, commented
    out at `BlockFlatMatrix.h:4`, corrective fallback commented out at `:1166`).

**Coverage of "essentially all relevant matrix/vector operations".**

37. `02 §7.17` was applied to one of its three sites → all three named
    (`SimplicialCohomology.cpp:191`, `LocalSystemUtils.cpp:28`,
    `EquivariantCochainComplexMorphismOnK.cpp:165`), **and** the direct conflict between
    `02 §7.17` ("hash map") and `02 §6.5(5)` / R10 (no hash containers on result paths) is
    resolved in favour of §6.5(5): index vector or ordered map only.
38. `02 §7.20` (single source of truth for the L1 flat layout, three copies today) appeared in no
    phase → added to Phase 3, where `BlockMat` with `nbc = 1` makes it nearly free.
39. Phase 3's "absorb the two hand-rolled solvers" contradicted R2's condition → the condition is
    now stated inline, and the τ triangle-fill solve is explicitly excluded in every phase.
40. `01 §9.7`'s recommended first deliverable (`EquivariantCohomologyOnK.cpp:214`/`:365`, where
    defects #4, #6, #7, #8, #11, #13, #27 all sit) was dropped → reinstated as Phase 3's
    suggested opening move.

**Verified and left alone** (recorded so it is not re-litigated): every `--bench` baseline
(59.7 s / 59.4 s / 5.29 s / 575 s / 434 MB / 24 M mallocs / 14.6 G / 6.6 s / 1.1 s / 1677 × 1419),
the 54 / 22 / 14 / 0.2 % attribution, the `r ≳ 45` crossover, the 2.7× naive-GPU trap, the 44×
64-bit GPU advantage, the 7.7 GB / 13 GiB VRAM figures, the whole `W_Tp ≈ 7e3·d³` table and every
CPU/GPU time derived from it (all arithmetic re-checked), the 32 registered validation names and
the `ValidationRegistry::register_validation` signature, the `HECKE_PURE_INTEGER` option, commits
`c8227c8` / `cdad0b9` / `41df5e2`, and Q9's claim that `Hecke/README.md:10-11, :143-147` is stale.

---

## 9. Phase 0 — execution record (2026-09-05)

Executed by four engineers on branches `phase0/{build,arith,bench,golden}` off `matrix-engine`
and integrated there by merge. Reference machine as recorded in `CMakeLists.txt`: GCC 11.4.0,
nvcc 13.0.48, RTX 5070 Ti (cc 12.0), 16 threads, `make -j16`. Unless stated otherwise every
number below was measured by the integrator on the **fully merged** tree, in-source,
`CMAKE_BUILD_TYPE` unset (⇒ `RelWithDebInfo`).

### 9.1 Exit criteria

| # | Exit criterion (§ "Phase 0") | Result | Evidence |
|---|---|---|---|
| E1 | `./hacs --all` exit 0 in ≤ 4 min on the default build (predicted ~2m45s) | **PASS** | `All validations PASSED (34/34 passed, 1 slow-tier skipped)`, **2m19s** |
| E2 | `GoldenRegressionValidation` exit 0 on Release-class **and** Debug builds | **PASS** | RelWithDebInfo 69.7 s; Debug 485.5 s; Bench 72.6 s |
| E3 | `GoldenRegressionValidation` exit 0 under both `HECKE_PURE_INTEGER` settings | **PASS** | OFF 69.7 s; ON 69.7 s |
| E4 | `./hacs --bench hecke 48 134217757 2` ≈ 5 s (`03 §4.1`: 5.29 s at `-O2`) | **PASS** | **4.88 s**, 68 MB peak RSS (Bench config: 4.87 s) |
| E5 | All pre-existing validations stay green | **PASS** | `--all-full`: `All validations PASSED (35/35 passed)`, **3m33s** |
| E6 | New validations registered | **PASS** | `GoldenRegressionValidation`, `GoldenEmit`, `SubstrateDifferentialValidation`; the `mod_inv` boundary cases were folded into `mod_arithmetic_validation` rather than given their own name |

In all four configurations `GoldenRegressionValidation` reports **tier A checked 9446, failing 0;
tier B checked 4603, mismatching 0**. The reference was emitted at `-O0` from the *unmodified
pre-fix* code (harness cherry-picked onto `c8227c8`), so this is the substantive Phase-0 claim:
the build, arithmetic and dead-code changes altered **no** computed result — not even a legacy
basis choice, which tier B would have caught and merely reported.

### 9.2 Measured baseline (default `RelWithDebInfo`)

| Command | Result | Wall |
|---|---|---|
| `make -j16` (fresh configure) | 0 errors | 12 s |
| `--all` (fast + standard) | 34/34, 1 slow skipped | 2m19s |
| `--all-full` (all tiers) | 35/35 | 3m33s |
| `GoldenRegressionValidation` | 14049 objects | 69.7 s |
| `HeckeBenchmarkSmoke` | PASS, certified | 71.0 s |
| `SubstrateDifferentialValidation` | 774/774 cases | ~2 s |
| `--bench hecke 48 134217757 2` | dims 0,7,0 | 4.88 s / 68 MB |
| `--bench cohom 64 134217757` | dims 0,11,0 | 4.66 s / 115 MB |

`--all` was additionally run green under `-DCMAKE_BUILD_TYPE=Bench` and under
`-DHECKE_PURE_INTEGER=ON`. `Bench` (`-O3 -march=native`) is **not** measurably faster than the
`RelWithDebInfo` default on this workload (82.9 s vs 79.4 s for the pre-golden `--all`), which is
consistent with `03`'s attribution of the run to algorithmic, not vectorisable, cost.

**Warning census.** `-Wall -Wextra` on all three targets: 1536 → 93 (the build engineer measured
88 with a slightly different census; 91 is the count reproduced on `phase0/build` alone). The
+5/−3 delta from the arithmetic branch is: +5 `-Wdeprecated-declarations` in
`MatrixValidation.cpp` / `FlatMatrixValidation.cpp`, whose new regression cases deliberately
exercise the now-deprecated `Matrix`; −1 invalid escape in `Matrix.cpp` (defect #25) and −2
`-Wtype-limits` in `ModArithmetic.cpp`, both fixed. No new warning outside validation TUs, and
none in the new `Golden/`, `Bench/` or `SubstrateDifferentialValidation` sources.

### 9.3 New finding (not in `01 §6`, found by the new warnings)

**`CochainComplex::get_euler_characteristic()` returned a dangling reference.** It was declared
`const uint32_t&` while returning an `int32_t` member, so the returned reference bound to a
temporary produced by the implicit conversion — undefined behaviour, 36 `-Wreturn-local-addr`
hits. It now returns `int32_t` by value. It had no callers, which is why no validation ever
tripped over it; it is recorded here because it is the kind of defect the audit's four documents
did not find and `-Wall -Wextra` did, in one build.

### 9.4 Caveats carried forward

* **`GoldenHarness.cpp` pins its own copy of `IsDicksonExceptional`.** The original lives in an
  anonymous namespace in `HeckeEndToEndValidation.cpp` and is therefore not linkable. The copy is
  itself captured as the tier-A `dickson` entry at every grid point, so the two implementations
  diverging is a golden failure rather than a silent drift — but this remains a duplicated
  predicate, and R8 ("decide exclusion by calling the shipped predicate") is satisfied only in
  that weakened sense. Give the predicate external linkage when `HeckeEndToEndValidation` is next
  touched.
* **`Θ^{(q)}_flat` is captured for `r = 1` only.** The `r = 2` pipeline's `Θ_flat` is *not* in the
  golden grid; `A(T_{p^2})` is captured for both the recursion and the direct double-coset route,
  so the `r = 2` path is pinned at the cohomology level but not at the cochain level.
* **Tier is a judgement call at `GoldenRegressionValidation`.** At 71 s it exceeds the `slow`
  threshold (~60 s) but is registered `standard`, i.e. it runs in plain `--all`: it is a
  *correctness* gate for every later phase, unlike the one genuine `slow` entry
  (`HeckeBenchmarkSmoke`, a performance smoke), and a correctness gate behind an opt-in flag is a
  gate nobody runs. `--all` stays at 2m19s, inside E1's 4-minute budget. Re-tier if that budget
  gets tight.
* **`GoldenEmit` is registered `fast`** because under `--all` it hits its `GOLDEN_EMIT=1` safety
  interlock and returns immediately without computing or writing; the real emission is minutes
  long and must stay an explicit owner action.
* Two engineer commits (`ee77b97`, `e5fa53d`) carry a `Co-Authored-By: Claude Opus 5` trailer;
  history was deliberately not rewritten.

### 9.5 Owner decisions taken

`Q1` (relaxed — canonical objects gate, bases reported), `Q11` (`image()` = `α·e_j` everywhere)
and `Q13` (tiered `--all` / `--all-full`) were decided during this phase; the decisions are
recorded inline in §7 and are implemented as described above.

---

## 10. Phase 1 — execution record (2026-09-05)

Executed by four engineers on branches `phase1/{rho,theta,tau,block}` off `matrix-engine` and
integrated there by merge; integration HEAD **`60a20f7`** (`Merge branch 'phase1/block' into
matrix-engine`), 22 commits on top of the Phase 0 tip `779dc45`. Reference machine as in §9
(GCC 11.4.0, nvcc 13.0.48, RTX 5070 Ti cc 12.0, 16 threads, `make -j16`). Unless stated
otherwise every number below was re-measured by the integrator on the **fully merged** tree,
in-source, `CMAKE_BUILD_TYPE` unset (⇒ `RelWithDebInfo`), with `--bench --repeat 3` (min of 3).

### 10.1 Exit criteria

| # | Exit criterion (§ "Phase 1") | Result | Measured |
|---|---|---|---|
| E1 | `--bench hecke 96 134217757 2` from 59.7 s to **≤ 8 s** | **PASS** | **6.64 s**, 250 MB (Bench build: 6.27 s) |
| E2 | `--bench cohom 128 134217757` from 59.4 s to **≤ 12 s** | **PASS** | **9.80 s**, 435 MB (Bench build: 8.78 s) |
| E3 | one `ρ_n` at `n_sym = 160` from 5.9 s (`-O0`) to **≤ 5 ms** | **PASS** | **0.215 ms** generic, 0.136 ms `T`, 0.030 ms `S` (`ell = 134217757`, best of 20) |
| E4 | `HeckeBenchmarkSmoke` (`n = 100`) from 575 s (`-O0`) to **≤ 30 s** | **PASS** | **7.80 s**, `COMPLETED and CERTIFIED (aggregate failing case(s) = 0)` |
| E5 | fitted exponent of `hecke` in `n_sym` over `{64, 96, 128}` **≤ 3.6** | **PASS** | **3.17** (`RelWithDebInfo`), **3.11** (`Bench`); `cohom`: 3.34 |
| E6 | keep every validation green, incl. `GoldenRegressionValidation` (all changes value-preserving) | **PASS** | `--all` 37/37 + 2 slow skipped, 58.6 s; `--all-full` 39/39, 1m27s |
| E7 | new validations registered: `SymmetricPowerValidation`, `ThetaEqSolveValidation`, `VacuousRelationValidation` | **PASS** | all three registered `standard`, plus `SymmetricPowerValidationSlow` (`slow`) |

**Bit-exactness gate.** `GoldenRegressionValidation` was run under **`GOLDEN_STRICT=1`** — i.e.
with tier B (legacy bases, projectors, change-of-basis matrices) also *failing* rather than merely
reporting — on all four configurations that matter, and returned 0 on every one, with identical
hashes and **tier A checked 9446, failing 0; tier B checked 4603, mismatching 0** throughout:

| Configuration | `GOLDEN_STRICT=1 GoldenRegressionValidation` | Wall |
|---|---|---|
| default `RelWithDebInfo` (in-source) | exit 0, A 9446/0, B 4603/0 | 12.0 s |
| `-DCMAKE_BUILD_TYPE=Bench` (`-O3 -march=native`) | exit 0, A 9446/0, B 4603/0 | 12.7 s |
| `-DHECKE_PURE_INTEGER=ON` | exit 0, A 9446/0, B 4603/0 | 12.0 s |
| `-DCMAKE_BUILD_TYPE=Debug` | exit 0, A 9446/0, B 4603/0 | 59.8 s |

Phase 1 is value-preserving by construction, so this is its acceptance gate. `--all` was
additionally run green on the `Bench` build (59.1 s) and with `HECKE_PURE_INTEGER=ON` (57.1 s).
No re-baseline of `Golden/GoldenReference.inc` was performed or needed.

### 10.2 Before / after

Phase-0 baselines from §9.2 and `03`; Phase-1 numbers on the same box, same configuration.

| Measurement | Phase 0 | Phase 1 | Speed-up |
|---|---|---|---|
| `--bench hecke 48 134217757 2` | 4.88 s / 68 MB | **0.81 s** / 70 MB | 6.0× |
| `--bench hecke 64 134217757 2` | — | **1.86 s** / 118 MB | — |
| `--bench hecke 96 134217757 2` | ≈ 57–74 s | **6.64 s** / 250 MB | ≈ 9–11× |
| `--bench hecke 128 134217757 2` | ≈ 189 s | **16.77 s** / 436 MB | ≈ 11× |
| `--bench cohom 64 134217757` | 4.66 s / 115 MB | **0.97 s** / 117 MB | 4.8× |
| `--bench cohom 96 134217757` | — | **3.74 s** / 250 MB | — |
| `--bench cohom 128 134217757` | ≈ 59–88 s | **9.80 s** / 436 MB | ≈ 6–9× |
| `HeckeBenchmarkSmoke` | 71.0 s | **7.80 s** | 9.1× |
| `--all` (fast + standard) | 2m19s (34/34) | **58.6 s** (37/37) | 2.4× |
| `--all-full` (all tiers) | 3m33s (35/35) | **1m27s** (39/39) | 2.4× |
| `GoldenRegressionValidation` | 69.7 s | **12.0 s** | 5.8× |
| one `ρ_n`, `n_sym = 160`, generic | 5.9 s (`-O0`, `02 §5.5 C`); engineer-reported 970 ms at `-O2` | **0.215 ms** | ≥ 4500× (see 10.5) |

Peak RSS is essentially unchanged at these sizes; item 7.3's win is structural (see 10.3, tau).

### 10.3 Per-workstream summary

**`phase1/rho` — items 7.0, 7.5, `mod_nCr` tables** (`0a2e415`, `0ed9c55`, `47b3f5d`, `4ebc562`).
`ComputeSymmetricPowerMatrixFM` was rewritten from the direct double sum (`O(n⁵)` with a
`mod_nCr`/`mod_pow` per term) to an `O(d_V²)` routine. The dispatch is the branch table at
`FlatMatrix.cpp:1440`:

| Branch | Condition on `A = [[a,b],[c,d]]` | Result |
|---|---|---|
| `C1` | `b = c = 0` | diagonal, `a^{n−k} d^k` |
| `C2` | `a = d = 0` | anti-diagonal |
| `C3` | `a = b = 0` (singular) | row `n` only |
| `C4` | `c = d = 0` (singular) | row `0` only |
| `C5` | upper unitriangular (`T` and its powers) | Pascal triangle |
| `C6` | lower unitriangular (`[[1,0],[k,1]]`) | transposed Pascal |
| `R1` | `a ≠ 0`, general | forward two-term column recurrence (`×(bx+dy)`, `÷(ax+cy)`) |
| `R2` | `a = 0`, general | mirrored backward recurrence in `b` (`det A = 1` ⇒ `a`, `b` not both zero) |

`ρ_n` is a mathematically unique matrix, so bit-identity is automatic once the branch is right —
which is exactly what `SymmetricPowerValidation` pins. `ρ_n(160)`, `ℓ = 134217757`, `-O2`, best of
20: **0.215 ms** generic, 0.136 ms `T`, 0.030 ms `S` (integrator's own micro-benchmark against the
shipped `libModArithmetic.a`; the rho engineer reported 0.49 / 0.20 / 0.04 ms on their branch,
against a `970 ms` `-O2` baseline). `mod_nCr` now uses per-`(n, ℓ)` factorial / inverse-factorial tables
for the remaining callers. All **24** live sites of the deprecated `Matrix`-returning
`ComputeSymmetricPowerMatrix` were migrated; the deprecated overload survives as a thin wrapper
that delegates to the FM version, so external callers keep byte-identical results.

**`phase1/theta` — items 7.1, 7.2, 7.6, defects #28, #31** (`2c5748a`, `d345803`, `4c81e51`,
`6b9d73e`, `f414b20`, `714d953`). 7.1: `change_of_basis_fm_multi` solves the whole `Θ_eq` system
with **one** augmented RREF of `[C_eq | Θ·C_eq]` instead of `dim C^q_eq` separate calls; the
coordinates are unique, so the result is bit-identical by mathematics, and the A-N3 residual
certificate (C5) still re-verifies every column. 7.2: a per-route memo of `ω_i·ρ_n(gγ_k)` /
`ρ_n(δ_iγ_k)` on `(i, γ_k)` cuts **125 → 12** distinct term-blocks at `p = 2`. #28: the two
independently-bracketed `Θ` evaluation routes are now compared by two `memcmp`s. 7.6: a
`FlatMatrix`-returning `theta_flat_fm` accessor beside the plan-mandated `std::vector<Matrix>`
signature, which stays (Q6). #31: `MinPolyKrylov` reads a single RREF of the Krylov matrix.
Net effect: the `Θ`-assembly share of the `hecke` run at `n = 128` fell from **47 % → 11 %**.

**`phase1/tau` — items 7.0b, 7.3** (`553d7a8`, `830e566`). 7.0b: `HeckeTauTable::certify()`
memoises `ρ_n` the way `build_xi_terms` already did — **133 → 16** `ρ_n` calls per `τ` table.
7.3: `XiTerm::rho_g_gamma` is held as a pool reference (`RhoRefT`) instead of by value. At
`n ≤ 128` the RSS win is **not** measurable (peak RSS is dominated by the cohomology blocks);
it is a structural fix for the large-`n` regime (`02`: 501 MB → 32 MB at `n = 1000`) and is
recorded as such rather than as a measured Phase-1 gain. The `τ` phase at `n = 128` went
**36.8 s → 4.9 s**.

**`phase1/block` — `factor_basis_block`, defects #8 #22, mechanical items, 7.4** (`2478596`,
`1d6cf72`, `987c3b6`, `2f03306`, `9a54422`, `2a5a700`). #8: `BlockFlatMatrix` gained `O(1)`
prefix-sum block offsets (`_get_block_start_{row,col}_idx`, `get_entry`). #22: `factor_basis_block`
moved out of `Matrix.cpp` into `BlockFlatMatrix.cpp` and now copies pivot rows **block-wise**,
removing the `(N_q + B_c)`-fold multiplier on the ≈ 22 % of `02 §2.1`. The mechanical hot-loop
fixes **#6, #12, #18, #19, #20, #24** were applied (drop the copies made solely to call the
now-`const` `is_zero()`/`is_invertible()`, in-place accumulation in `operator*`, `unique_ptr`
caches in `FlatMatrix`, const-correct `rank`/`kernel`/`image`/`is_invertible` and
`BlockFlatMatrix::is_zero`, fused `operator-`, delete `_ensure_data_populated_if_empty`).

> **Deliberately skipped: #11 (swap-and-pop instead of `erase`).** The pivot tie-break in the
> block elimination depends on the *order* of the block list, so swap-and-pop changes which basis
> the algorithm produces. The result would still be a correct basis, but tier B of the golden
> harness pins the legacy basis choices, and Phase 1's whole claim is that it changes no computed
> value — including tier B. #11 is deferred to a phase that re-baselines deliberately.

7.4 (vacuous-relation short-circuit in `A_Cq`/`A_Zq`): `M == I` block rows are skipped and
`M == αI` is emitted as a scalar block, shrinking `A_C1` from **13 → 2 block rows** at even `n`.
Odd-`n` semantics (`H^* = 0`, the FIX-negI purpose) are preserved exactly, pinned by the golden
grid's odd `n_sym = 1` points, by Hecke oracle O2, and by the new `VacuousRelationValidation`
dimension tables for even *and* odd `n`. **Tier B survived this with 0 mismatches, so no
re-baseline was needed.**

> **Out of nominal scope, landed early: `9a54422`** (`perf(substrate): zero-skipping GEMM order +
> zero-block skips in block elimination`) — the `i-k-j` GEMM loop order with a skip on a zero
> `A[i][k]`, plus zero-block skips in the block elimination. This is a **Phase-2-style** change
> (`03 §7.2`), not a Phase-1 item. It landed here because it is exact (no reassociation of a
> reduction: only additions of terms known to be zero are removed), it was `GOLDEN_STRICT`-clean,
> and it is worth **48.9 s → 10.9 s on `cohom 128`** by itself — i.e. the single largest item of
> the phase. It is named explicitly here so that Phase 2's own accounting does not double-count it.

### 10.4 New validations

| Name | Tier | What it pins |
|---|---|---|
| `SymmetricPowerValidation` | `standard` | the new `O(d_V²)` `ρ_n` bit-for-bit against `ComputeSymmetricPowerMatrixFM_reference` (exhaustive small `n`, spot grid `n ∈ {64, 96, 128, 160}`), plus the `C1`–`C6` closed forms against independent Pascal/power oracles and the reference-free structural identities `ρ_n(A)ρ_n(B) = ρ_n(AB)`, `ρ_n(A)^{-1} = ρ_n(A^{-1})` that cover the large-`n` regime |
| `SymmetricPowerValidationSlow` | **`slow`** | the same comparison against the `O(n⁵)` reference over the wide grid |
| `ThetaEqSolveValidation` | `standard` | `change_of_basis_fm_multi` vs the per-vector `change_of_basis_fm` on the golden grid (12 grid points, 3122 `Θ_eq` columns bit-identical, all residuals exactly 0), plus rejection of out-of-span vectors |
| `VacuousRelationValidation` | `standard` | the 7.4 short-circuit against the pre-7.4 path: dimension tables for even *and* odd `n` |

Because `SymmetricPowerValidationSlow` is `slow`, the slow tier now holds two entries
(`HeckeBenchmarkSmoke` and `SymmetricPowerValidationSlow`) and `--all` reports "2 slow-tier
skipped"; the Hecke acceptance gate still needs `--all-full`.

### 10.5 Carried forward

* **The residual excess exponent is defect #4.** At 3.17 (`RelWithDebInfo`) / 3.11 (`Bench`) the
  `hecke` fit is comfortably inside Phase 1's ≤ 3.6 gate and the `n⁴`/`n⁵` terms are demonstrably
  gone, but it is not yet the ≤ 3.2 permanent guard of §4.4. The remainder is
  `_determine_and_set_flags_from_data()` rescanning a whole `d_V × d_V` block after every block
  operation plus `_clear_cached_rref()` firing on every mutation — defect #4, which Phase 1
  explicitly does not touch and which the bulk `BlockBuilder` of **Phase 3** fixes. The ≤ 3.2
  guard takes effect from Phase 3 onward, as planned.
* **The `970 ms` `-O2` `ρ_n` baseline could not be reproduced post-merge.** The surviving
  `ComputeSymmetricPowerMatrixFM_reference` oracle now runs `n = 160` in **37.2 ms** at `-O2`, not
  ≈ 1 s — because item 7.0 also tabulated `mod_nCr` per `(n, ℓ)`, and the reference calls
  `mod_nCr` per term, so the oracle inherited that speed-up and is **no longer** a faithful stand-in
  for the pre-Phase-1 cost. The `≥ 4500×` in 10.2 therefore rests on the engineer's pre-merge
  `970 ms` and on `02 §5.5 C`'s 5.9 s at `-O0`, not on a post-merge measurement; the *absolute*
  Phase-1 number, 0.215 ms, is the integrator's own and is what E3 (≤ 5 ms) is decided on, with
  173× of headroom even against the deflated 37.2 ms oracle.
* **Defect #11 is open** (see the callout in 10.3) and needs a phase willing to re-baseline tier B.
* The §9.4 caveats (duplicated `IsDicksonExceptional` in `GoldenHarness.cpp`; `Θ^{(q)}_flat`
  captured for `r = 1` only; `GoldenRegressionValidation` tiered `standard` by judgement) are all
  **still open** and unchanged by Phase 1 — though the third is now much less pressing, the whole
  golden run having dropped to 12.0 s.
* `CLAUDE.md` was updated in the same commit as this record with the re-measured timings.

---

## 11. Phase 2 — execution record (2026-09-05)

Executed by three engineers — **core** (`ModCtx`/`DenseBuf`/`DenseView`/`Kernels`/`RefLinAlg` +
the `--bench micro` harness, branch `phase2/bench`), **GEMM retrofit** (`FlatMatrix` /
`BlockFlatMatrix` dense arithmetic onto `engine::kernels`, branches `phase2/arith`+`phase2/gemm`)
and **elimination** (`DenseElim` + the elimination retrofit, branch `phase2/elim`) — and
integrated on `matrix-engine` by merge. Same reference machine as §9/§10 (GCC 11.4.0, nvcc
13.0.48, RTX 5070 Ti cc 12.0; here 32 hardware threads, `make -j16`). Every number below was
measured by the integrator on the **fully merged** tree, in-source, `CMAKE_BUILD_TYPE` unset
(⇒ `RelWithDebInfo`), unless the row says otherwise; benchmark runs used `--repeat 5` on an
otherwise idle box.

### 11.1 Exit criteria

| # | Exit criterion (§ "Phase 2") | Result | Evidence |
|---|---|---|---|
| E1 | `--bench micro gemm 128 --backend engine` ≥ **15 Gmodmul/s** (stretch 25) | **PASS (stretch met)** | **27.27 Gmodmul/s** (median 77 µs); `Bench` build 27.53 |
| E2 | `--bench micro rref 1677 1419 --backend engine` ≤ **0.6 s** | **PASS (9.4× under)** | **0.0643 s** (26.51 Gmodmul/s); `Bench` build 0.0705 s |
| E3 | `--bench cohom 128 134217757` ≤ **4 s** | **FAIL** | **6.51 s** (was 9.80 s). Diagnosis in 11.5 — the arithmetic layer is not the binding constraint; the block layer is |
| E4 | `GoldenRegressionValidation` exit 0 | **PASS** | exit 0, and **tier A 9446 failing 0, tier B 4603 mismatching 0 under `GOLDEN_STRICT=1`** on all five configurations built (default, `Bench`, `Debug`, `HECKE_PURE_INTEGER=ON`, `ENGINE_SHADOW_LEGACY=ON`) |
| E5 | New validations registered and green | **PASS** | `ModContextValidation`, `KernelBitIdentityValidation`, `DenseElimValidation`, `DenseElimPipelineValidation`, `PerformanceSmokeValidation` — all `standard`, all in `--all` |
| E6 | `-DENGINE_SHADOW_LEGACY=ON` build runs `HeckeEndToEndValidation` | **PASS** | plus `LocalSystemCohomologyValidation`, `HeckeOracleValidation`, `BlockFlatMatrixValidation`, `DenseElimPipelineValidation` and strict Golden — every dual-route memcmp/entrywise comparison silent |

Phase 2 therefore **exits with one criterion missed, E3**, and it is missed for a reason the phase
was never scoped to fix; see 11.5. E1/E2 — the two criteria that actually gate *this* phase's
deliverable, the arithmetic layer — are met with 1.8× and 9.4× of margin.

### 11.2 Before / after

Legacy baselines are `03 §10` (pre-Phase-2, i.e. before the `mod_*` header inlining as well). The
"legacy (merged tree)" column is `--backend legacy` on the merged tree, which after the merge fix
of 11.4 really is the pre-Phase-2 substrate end to end; the difference from `03 §10` is the
inlining alone.

| Benchmark | `03 §10` legacy | legacy (merged tree) | **engine (merged tree)** | speed-up vs `03 §10` |
|---|---|---|---|---|
| `micro gemm 128` | 0.17 Gmodmul/s | 0.214 Gmodmul/s | **27.27 Gmodmul/s** | **160×** |
| `micro gemm 512` | 0.17 Gmodmul/s | 0.215 Gmodmul/s | **30.36 Gmodmul/s** | **179×** |
| `micro rref 1677 1419` | 3.50 s | 2.417 s | **0.0643 s** | **54×** |
| `micro rref 1677 1419 258` | — | — | 0.0293 s (19.07 Gmodmul/s) | — |
| `micro kernel 1677 1419 258` | — | — | 0.0299 s (18.71 Gmodmul/s) | — |

All four backend pairs report **identical FNV-1a-64 checksums** (`gemm` `0xed477c39ebebece5` /
`0xdf6200e19d2b9a44`, `rref` `0x40f866e97e396213`), which is the micro-harness's bit-identity
statement, independent of `KernelBitIdentityValidation` and of the shadow build.

Pipeline modes (default build; Phase-1 figures from §10 in the last column):

| Benchmark | total | peak RSS | Phase 1 |
|---|---|---|---|
| `--bench cohom 64 134217757` | 0.68 s | 117 MB | 0.97 s |
| `--bench cohom 96 134217757` | 2.45 s | 251 MB | — |
| `--bench cohom 128 134217757` | **6.51 s** | 437 MB | 9.80 s |
| `--bench hecke 48 134217757 2` | 0.53 s | 71 MB | 0.81 s |
| `--bench hecke 64 134217757 2` | 1.18 s | 118 MB | — |
| `--bench hecke 96 134217757 2` | **4.12 s** | 251 MB | 6.64 s |
| `--bench hecke 128 134217757 2` | 10.51 s | 437 MB | — |
| `HeckeBenchmarkSmoke` | 4.96 s (PASS, certified) | — | 7.8 s |

Fitted exponent in `n_sym` over `{64, 96, 128}`: **hecke 3.15**, **cohom 3.24** (Phase 1: 3.17 and
3.34). Still above the ≤ 3.2 permanent guard of §4.4 for `cohom`, and for the same reason as §10.5
— defect #4 and the block orchestration, both Phase 3.

`Bench` build (`-O3 -march=native`): `cohom 128` **6.42 s**, `hecke 96` **4.16 s**, `micro gemm
128` 27.53 Gmodmul/s, `micro rref 1677 1419` 0.0705 s. As in Phases 0 and 1, `-march=native` buys
essentially nothing on the pipeline modes — the engine already dispatches to AVX-512 at runtime,
so the `Bench` config no longer even has vectorisation to add.

Suite:

| Command | Result | Wall |
|---|---|---|
| `./hacs --all` | `All validations PASSED (42/42 passed, 2 slow-tier skipped)` | **1m02s** |
| `./hacs --all-full` | `All validations PASSED (44/44 passed)` | **1m20s** |
| `ENGINE_BACKEND=legacy ./hacs --all` | `All validations PASSED (42/42 …)` | 1m26s |
| `GoldenRegressionValidation` | tier A 9446 / 0, tier B 4603 / 0 | 6.2 s |

### 11.3 Per-workstream summary

**Core layer (`ModCtx`, `DenseBuf`/`DenseView`, `Kernels`, `RefLinAlg`, `--bench micro`).**
`gemm` reaches **28–30 Gmodmul/s at `n = 128`–512** single-thread via an **8×16 register-blocked
outer-product microkernel with runtime AVX-512 dispatch** (`micro_u32_avx512<MR>`, `MR ∈
{1,2,4,8}`, plus a portable fallback that measures ≈ 2.7 Gmodmul/s and is what
`PerformanceSmokeValidation`'s engine floor of 4.0 exists to catch), `u64` delayed accumulation
with **k-blocking at `min(k_max, 256)`**, and a **FP64-quotient Barrett epilogue for `p ≥ 2^13`**.

> **Documented deviation.** The FP64 epilogue is a departure from the "integer-only arithmetic"
> convention of `CLAUDE.md`. It remains **exact**: the FP64 quotient estimate is proved to be
> within ±1 of the true quotient over the admissible range, the ±1 is corrected by an integer
> compare-and-subtract, and an `ENGINE_DEBUG_CHECK` re-derives the integer quotient in non-`NDEBUG`
> builds. `ModContextValidation` pins it at every regime boundary (`p ∈ {2, 3, 2^26.5±, 2^27,
> 2^31−1, 2^31+11, 2^32−5, 2^61−1, 2^63−25}`, 10⁶ fixed-seed samples each) and the `k_max`
> overflow assertion is exercised. It is recorded here so that a future GPU or `__int128` port
> knows the epilogue is a *deliberate*, bounded use of floating point, not an accident.

**GEMM retrofit.** Two steps, measured separately: (i) header-inlining `mod_mul`/`mod_add`/
`mod_sub`/`mod_minus` and their `*64` twins bought **1.25–1.47×** across the pipeline modes on its
own; (ii) routing `FlatMatrix::operator*`/`+`/`-`/`scal`/`transpose` and `BlockFlatMatrix::operator*`'s
per-block loop through `engine::kernels` bought **130× on GEMM** in isolation. It also added the
`ENGINE_SHADOW_LEGACY` CMake option and `EngineConfig.h`'s runtime switch, and wired the
`RunGemm`/`RunGemv`/`RunTranspose` engine arms.

**Elimination.** `DenseElim` is a **packed column-panel PLU with a 32-wide Crout base panel**,
operating **in-buffer** on a `DenseView` over `flat_data_` — defect #7 (the `vector<vector>` copy
at `FlatMatrix.cpp:1043-1051`) is gone. RREF is formed as **`U₁⁻¹·U`** rather than by a second
elimination sweep. Bit-identity with the legacy core is argued from **uniqueness** (the reduced row
echelon form of a matrix over a field is unique, and the derived bases — kernel, image,
`solve_multi_rhs`, complement — are fixed by the same pivot-order rules the legacy code used), and
then *checked*: `DenseElimValidation` runs **73,559 checks**, `DenseElimPipelineValidation` runs a
real `A_Cq`/whole-cohomology pass, and golden tier B (the legacy basis choices) is 0 under
`GOLDEN_STRICT=1`. Net **52×** on RREF at the micro level (54× against `03 §10`).

### 11.4 Merge-level changes made by the integrator

Three conflicts (`FlatMatrix.cpp` includes + helper block, `BlockFlatMatrix.cpp` includes,
`PerformanceSmokeValidation.cpp` comment) were resolved as unions; `FlatMatrix.h`,
`CMakeLists.txt`, `ENGINE_API.md` and `ValidationRegistry.cpp` auto-merged. Beyond that:

1. **One backend predicate, not two.** The GEMM side gated on `engine::backend_is_legacy()` (env
   only) and the elimination side on `engine::elim::use_legacy()` (env **or** the thread-local
   `ScopedLegacy`). Post-merge, `--backend legacy` therefore meant "legacy elimination with
   *engine* products" and the `gemm` column of `--bench micro` reported 27 Gmodmul/s for *both*
   backends — a before/after table that silently compared the engine with itself.
   `FlatMatrix.cpp`'s `engine_path()` now reads `engine::elim::use_legacy()`, so a single
   `ScopedLegacy` rolls products and elimination back together, and `GemmLegacy`/`GemvLegacy`/
   `TransposeLegacy` install that guard exactly as `RrefLegacy`/`KernelLegacy` already did. The
   legacy column then reproduces `03 §10` (0.214 vs 0.17 Gmodmul/s, the gap being the inlining) —
   which is how 11.2 became measurable at all. Value-preserving: strict golden re-run on all five
   configurations after the change, `cohom 128` unmoved (6.60 s before, 6.60 s after).
2. **`PerformanceSmokeValidation`'s default backend switched from `legacy` to `engine`** (and with
   it `--bench micro`'s, which now takes its default from `ENGINE_BACKEND`). Both arms exist and
   the engine arm is the shipped substrate, so the floor inside `--all` must gate the code the
   pipeline runs. `ENGINE_BACKEND=legacy` still selects the legacy arm together with the legacy
   floors, which is what `ENGINE_BACKEND=legacy ./hacs --all` exercises (green).

### 11.5 E3 (`cohom 128 ≤ 4 s`) — why it misses, measured

Not hidden, and not a merge defect: **the arithmetic layer is no longer the constraint, and the
block layer now is.** Three independent measurements say so.

* **`ENGINE_BACKEND=legacy --bench cohom 128` is 6.71 s against the engine's 6.51 s** — a 3 %
  spread. The whole 130×-on-GEMM / 52×-on-RREF retrofit is worth 3 % on this pipeline. (The
  9.80 s → 6.6 s improvement over Phase 1 is almost entirely the `mod_*` header inlining.)
* **A gemm shape census** (temporary instrumentation of `engine::kernels::gemm<uint32_t>`, not
  committed) over one `cohom 128` run: **4,922,627 gemm calls, 19.19 G modmuls, mean `m`=20.6,
  `n`=13.0, `k`=12.0, and 4,322,633 calls — 88 % — with `k == 1`.** These are rank-1 updates on
  ~20×13 tiles. An 8×16 register-blocked microkernel with a Barrett epilogue cannot reach its
  27 Gmodmul/s on shapes that small; the realised rate across the run is ≈ 2.9 Gmodmul/s, i.e.
  a 9× shape penalty, and it is the same ≈ 2.9 Gmodmul/s the inlined scalar loop achieves — which
  is exactly why the two backends tie.
* **The work itself is redundant.** 19.19 G modmuls are issued for a problem whose largest
  equivariant cochain group is `dim C¹_eq = 1161`; one dense RREF of that size is ≈ 1.6 G modmuls,
  and the micro-harness does a *larger* one (1677×1419) in **0.064 s**. The block layer issues
  roughly **12× more arithmetic than a dense route would**, in ~4.9 M pieces too small to
  vectorise.

`gprof` (`-O2 -pg`) agrees: 64.6 % self time in `micro_u32_avx512<8>` (15.3 M calls), then the
block-layer object churn — 5.19 M `FlatMatrix` constructions, 3.85 M copies, 31.7 M destructions,
4.36 M `block_sub_product`, 3.67 M `_add_or_get_block_index`, 46.0 M `_clear_cached_rref` and
5.99 M `_determine_and_set_flags_from_data` rescans (defect #4).

**No merge-level fix was attempted** beyond 11.4, because none of the above is reachable from the
merge: the fix is to stop emitting thousands of 1-wide block columns and millions of temporary
`FlatMatrix` objects, which is precisely **Phase 3's `BlockBuilder` + block kernel set**, plus
defect #4. A `k ≤ 8` specialisation in the gemm driver would recover part of the shape penalty and
is a cheap Phase-3 precursor, but it addresses 6 % of the arithmetic and cannot close a 6.5 s → 4 s
gap. **E3 is therefore re-asserted as a Phase 3 exit criterion**, where the mechanism that owns it
is being built.

### 11.6 Not retrofitted (both engineers' lists, merged)

* `FlatMatrix::operator+` / `operator-` between a **scalar (`αI`) and a general** matrix still runs
  the legacy loop; only general⊕general goes through `engine::kernels`.
* `operator*`'s **zero-block skip was dropped** on the engine path (the kernel is called
  unconditionally for general×general). Harmless at these sizes, but it is a behaviour difference
  from the legacy loop worth remembering when block sparsity arrives in Phase 3.
* `image()`, `flat_image()` and the **true-RREF assembly** are untouched — they still build their
  result outside `DenseElim`.
* `Matrix::operator*` untouched, as scoped (retired in Phase 3).
* `BlockFlatMatrix::_block_gaussian_elimination` keeps its **structure**: only its per-block
  operations were rerouted. Its orchestration is 11.5's problem and Phase 3's scope.

### 11.7 Carried forward

* **E3 (`cohom 128 ≤ 4 s`) moves to Phase 3**, with 11.5 as its brief: block orchestration
  (`BlockBuilder`, bulk construction, no per-cell `FlatMatrix` temporaries) and defect #4.
* **The ≤ 3.2 exponent guard of §4.4** is met by `hecke` (3.15) but not `cohom` (3.24); same
  mechanism, same phase.
* **The FP64 Barrett epilogue** (11.3 callout) is a documented, bounded deviation from
  integer-only arithmetic; any GPU port must re-derive its ±1 bound for the target's FP semantics.
* **A `k ≤ 8` gemm specialisation** is an identified, self-contained win for the block-update
  regime; deliberately not taken in Phase 2 (it is core-layer work landing after the phase's
  bit-identity harness was frozen).
* The §9.4 caveats (duplicated `IsDicksonExceptional`; `Θ^{(q)}_flat` at `r = 1` only;
  `GoldenRegressionValidation` tiered `standard`) and §10.5's defect #11 are **all still open** and
  untouched by Phase 2.
* **Warning census: 93 → 94** (`-Wall -Wextra`, all three targets). The one added warning is a
  `-Wunused-function` for a `str(engine::u128)` debug helper in the new `ModContextValidation.cpp`;
  no warning in `Kernels.cpp`, `DenseElim.cpp`, `DenseBuf.cpp`, `RefLinAlg.cpp`,
  `PerformanceSmokeValidation.cpp` or `DenseElimPipelineValidation.cpp`, and none in the
  retrofitted regions of `FlatMatrix.cpp` / `BlockFlatMatrix.cpp`.
* **Sanitizers clean.** `-DCMAKE_BUILD_TYPE=Check` (`-fsanitize=address,undefined`, no `NDEBUG`, so
  every `ENGINE_DEBUG_CHECK` is live) running `KernelBitIdentityValidation`,
  `DenseElimValidation`, `SubstrateDifferentialValidation` and `LocalSystemCohomologyValidation`:
  **0 findings**, 0 leaks.
* `CLAUDE.md` was updated in the same commit as this record.

---

## 12. Phase 3 — execution record (2026-09-06)

Executed as **Stage A** (the model itself: `BlockPool`/`BlockMat`/`BlockBuilder`/`BlockElim` +
block kernels, branch `phase3/model`; the `Matrix` retirement + the two migration tools, branch
`phase3/retire`; the measured baselines of `03 §11`, branch `phase3/tools`) followed by **Stage B**
(the consumer migration, one branch per group of files: `phase3/cohom`, `phase3/xchk`,
`phase3/morph`, `phase3/hecke`) and integrated on `matrix-engine` by merge. Same reference machine
as §9–§11 (Ryzen 9 7950X, 32 hardware threads, WSL2, GCC 11.4.0, nvcc 13.0.48, RTX 5070 Ti cc 12.0;
`make -j16`). **Every number below was measured by the integrator on the fully merged tree**,
in-source, `CMAKE_BUILD_TYPE` unset (⇒ `RelWithDebInfo`), single-threaded, `--repeat 5`
`--count-allocs` on an otherwise idle box, unless the row says otherwise. Baselines are the
*measured* ones of `03 §11.1`, not the plan's inferred figures.

### 12.1 Exit criteria

| # | Exit criterion (§ "Phase 3", plus the §4.4 guard and the E3 carried over from §11.7) | Result | Evidence |
|---|---|---|---|
| E1 | `GoldenRegressionValidation` exit 0 | **PASS** | exit 0, and **tier A 9446 failing 0, tier B 4603 mismatching 0 under `GOLDEN_STRICT=1`** on all five configurations built: default, `Bench`, `Debug`, `HECKE_PURE_INTEGER=ON`, `ENGINE_SHADOW_LEGACY=ON` |
| E2 | peak RSS of `hecke 128 134217757 2` ≤ **120 MB** (baseline 436.9) | **PASS** | **100.3 MB**, a **4.36×** reduction |
| E3 | allocations ≤ **5 %** of the baseline 26.19 M / 26.16 M (⇒ ≤ 1.31 M) | **PASS (by 67×)** | `hecke 128` **19 641** (0.075 %); `cohom 128` **61 324** (0.23 %) |
| E4 | `hecke 128 134217757 2` ≤ **6 s** single-thread (baseline 10.22) | **PASS (7×)** | **0.845 s** |
| E5 | `cohom 128 134217757` ≤ **4 s** (Phase 2's E3, re-asserted here by §11.7) | **PASS (8.7×)** | **0.462 s** (Phase 2: 6.51 s) |
| E6 | zero `Matrix` includes outside `MatrixValidation`/`HeckeModuleDecomposition` | **PASS** | `check_matrix_includes.sh`: 173 files scanned, 0 offenders; gated in `--all` by `MatrixRetirementValidation` |
| E7 | raw `mod_*` call sites outside the allow-list = 0 | **PASS** | `raw_mod_calls.sh`: **108 sites, 0 outside**; the Stage B backlog is empty. Gated in `--all` by `ConsumerMigrationValidation` |
| E8 | new validations registered and green | **PASS** | `BlockMatValidation`, `BlockEliminationValidation`, `BlockModelPipelineValidation`, `CohomologyBlockModelValidation`, `HeckeThetaBlockValidation`, `BarCocycleSolverValidation`, `ConsumerMigrationValidation`, `MatrixRetirementValidation` — all in `--all` |
| E9 | fitted time exponent in `n_sym` over `{64, 96, 128}` ≤ **3.2** (the §4.4 permanent guard, in force from this phase) | **PASS** | **hecke 2.56**, **cohom 2.49** (Phase 2: 3.15 / 3.24). First phase in which `cohom` meets it |
| E10 | projected memory at `n_sym = 1000` ≤ **1.5 GB** | **FAIL** | **≈ 4.7–5.3 GB.** See 12.6 |

Phase 3 therefore **exits with one criterion missed, E10**, and — unlike Phase 2's E3 — it is
missed by a *factor*, not by a mechanism nobody owns: see 12.6 for the measurement and the reason.

### 12.2 Before / after

Baselines are `03 §11.1`, measured on `matrix-engine` tip `3c1ac45`.

| Benchmark | pre-Phase-3 | **post-Phase-3** | factor |
|---|---|---|---|
| `--bench hecke 128 134217757 2` — time | 10.22 s | **0.845 s** | **12.1×** |
| — peak RSS | 436.9 MB | **100.3 MB** | **4.36×** |
| — allocations | 26 186 806 | **19 641** | **1333×** |
| — requested bytes | 7.42 GiB | 0.61 GiB | 12.2× |
| `--bench cohom 128 134217757` — time | 6.30 s | **0.462 s** | **13.7×** |
| — peak RSS | 436.8 MB | **92.0 MB** | **4.75×** |
| — allocations | 26 161 308 | **61 324** | **427×** |
| — requested bytes | 7.23 GiB | 0.44 GiB | 16.6× |
| `--bench cohom 64 134217757` | 0.64 s / 117.5 MB / 4.60 M | **0.082 s / 30.8 MB / 32 045** | 7.8× / 3.8× / 143× |
| `--bench hecke 48 134217757 2` | 0.50 s / 70.6 MB / 2.52 M | **0.072 s / 21.4 MB / 17 984** | 6.9× / 3.3× / 140× |

Full sweep (default build, `--repeat 5 --count-allocs`; `--repeat 3` at `n ≥ 224`):

| `n_sym` | hecke: time / RSS / allocs | cohom: time / RSS / allocs |
|---:|---|---|
| 48 | 0.072 s / 21.4 MB / 17 984 | — |
| 64 | 0.143 s / 28.6 MB / 18 414 | 0.082 s / 30.8 MB / 32 045 |
| 96 | 0.388 s / 62.1 MB / 18 986 | 0.220 s / 71.4 MB / 46 676 |
| 128 | **0.845 s / 100.3 MB / 19 641** | **0.462 s / 92.0 MB / 61 324** |
| 160 | 1.546 s / 141.3 MB / 20 245 | 0.838 s / 134.0 MB / 75 947 |
| 192 | 2.569 s / 258.9 MB / 20 700 | 1.529 s / 231.3 MB / 90 497 |
| 224 | 3.944 s / 312.8 MB / 21 213 | 2.204 s / 284.6 MB / 105 011 |
| 256 | 5.795 s / 344.8 MB / 21 901 | 3.112 s / 312.5 MB / 119 682 |

`n = 224` and `256` were measured for E10 only and are new to this programme. Note that the
**hecke allocation count is essentially flat in `n_sym`** (17 984 → 21 901 across a 5.3× range):
the block model allocates per *object*, and the object count is a property of the 7-vertex model,
not of `d_V`. `cohom`'s grows slowly (32 045 → 119 682) through the lazily materialised
`get_*_bases_fm()` compatibility lists, which are still one `FlatMatrix` per basis vector.

Other modes:

| Run | Result |
|---|---|
| `--bench family 96 134217757 2 2` | 0.584 s / 72.6 MB / 32 064 allocs, `rec_eq_direct=1` |
| `--bench hecke 96 134217757 2 --cross-checks` | 1.006 s / 149.2 MB (cross-check phase ≈ 0.62 s; **28.7 s** before) |
| `--bench decomp 128 134217757 2` | 0.838 s / 100.7 MB, `q=1 blocks=5 certify=0` |
| `HeckeBenchmarkSmoke` | **0.47 s**, PASS (certified); Phase 2: 4.96 s |
| `micro gemm 128 / 512` | 24.86 / 29.70 Gmodmul/s, checksums `0xed477c39ebebece5` / `0xdf6200e19d2b9a44` — unchanged from §11.2 |
| `micro rref 1677 1419` | 0.0627 s, checksum `0x40f866e97e396213` — unchanged from §11.2 |
| `Bench` build (`-O3 -march=native`) | `cohom 128` 0.464 s, `hecke 128` 0.799 s, `hecke 96` 0.382 s — `-march=native` still buys ≈ nothing |

**The rollback measures the phase.** On the same binary, `ENGINE_BACKEND=legacy` runs the
pre-Phase-3 consumer arms:

| Run | engine | `ENGINE_BACKEND=legacy` |
|---|---|---|
| `cohom 128` | 0.462 s / 92 MB / 61 K allocs | **6.483 s / 303.4 MB / 4 968 390** |
| `hecke 128` | 0.845 s / 100 MB / 20 K allocs | **11.649 s / 303.8 MB / 4 943 986** |

That legacy arm is the *pre-Phase-3 consumers on the post-Phase-2 substrate* — not tip `3c1ac45`
— which is why its allocation count is 4.9 M rather than 26 M (Phase 1's `ρ_n`, the `Matrix`
retirement and the simplex-index change all sit below it). Contrast with §11.5, where the two
backends tied to within 3 %: the arithmetic was never the constraint, and this table is the direct
measurement that the orchestration was.

Suite (default build):

| Command | Result | Wall |
|---|---|---|
| `./hacs --all` | `All validations PASSED (50/50 passed, 2 slow-tier skipped)` | **1m43s** |
| `./hacs --all-full` | `All validations PASSED (52/52 passed)` | **2m00s** |
| `ENGINE_BACKEND=legacy ./hacs --all` | `All validations PASSED (50/50 …)` | 2m34s |
| `-DCMAKE_BUILD_TYPE=Bench ./hacs --all` | `All validations PASSED (50/50 …)` | — |
| `-DHECKE_PURE_INTEGER=ON ./hacs --all` | `All validations PASSED (50/50 …)` | — |
| `GOLDEN_STRICT=1 GoldenRegressionValidation` | tier A 9446 / 0, tier B 4603 / 0 | 3.9 s |

The suite got **slower** (1m05s → 1m43s) while the pipeline got 12× faster, entirely because of
the new validations: `BlockEliminationValidation` 43.9 s, `BlockModelPipelineValidation` 4.6 s,
`ConsumerMigrationValidation` 2.2 s, `BlockFlatMatrixValidation` 1.5 s,
`CohomologyBlockModelValidation` 0.43 s, `HeckeThetaBlockValidation` 0.41 s,
`MatrixRetirementValidation` 0.26 s, `BlockMatValidation` 0.17 s, `BarCocycleSolverValidation`
< 0.01 s. That is the intended trade: they are the entrywise evidence for the bit-identity claim.

### 12.3 Per-workstream summary

**Stage A — the model (`phase3/model`).** `BlockPool` (content-addressed, full compare on hash hit,
refcounted, borrowed entries, memoised relayout twins, entries in a `std::deque` so views survive
later interns), `BlockRef` = `α·I + β·M^(T?)` with `kind` canonical from `(α, β)`, `BlockMat`
(prefix-sum grid + sorted block-CSR, insertion-order-independent `finalize()`), `BlockView`,
`BlockBuilder` (one call per block, never per cell), the block kernels (`gemm` with `(α, β)`
constant folding and CSE on data windows, `gemm_dense`, `add`/`scale` without data work, `equal`
as *mathematical* matrices, structural transpose) and `BlockElim` (left-looking block-column panel
driver over `DenseElim` with one fully reduced RREF prefix, so multipliers are the input's own
blocks gathered structurally; `kernel_basis` / `image_basis` / `factor_basis` / `solve_multi_rhs`
on top, all D5b). **Re-measured by the integrator on the real `n_sym = 128` matrices**, via
`BlockModelPipelineValidation`'s own timing output: `A_C1` (1677×1419) assembly + `rref` +
`kernel_basis` **7.8 ms** against the legacy `BlockFlatMatrix::flat_kernel`'s **15.9 ms** (and the
Phase-2 retrofit's 16.6 ms); the real `W¹ = C¹/Z¹` `factor_basis` (ambient 1419, 516 relations,
1161 generators) **0.223 s** against `factor_basis_block`'s **3.175 s** — a **14.2×** on the single
operation `03 §11` identified as the pipeline's largest. `H¹ = Z¹/B¹` is 0.158 s and
`solve_multi_rhs` with 516 RHS in `C¹` 0.079 s. The allocation figures quoted in `ENGINE_API.md §9`
(191 vs 48 121 for `A_C1`; 785 vs 2.33 M for `W¹`) come from the model's own instrumentation on the
branch and are consistent with the whole-run counts of 12.2. Two bugs were found
*by* the new validations and fixed in Stage A: a `std::vector` reallocation in the pool dangled a
borrowed view of a multi-vector (hence the `std::deque`), and `BlockBuilder::set` released the old
ref before acquiring the new one.

**Stage A — the `Matrix` retirement (`phase3/retire`).** `SimplexRelation::M` became a
`FlatMatrix` (the structural pin of `01 §5.1`); `LocalSystemSL2Z`, `LocalSystemPresets`, the
morphism class, `InducedLocalSystem::BuildMH`, `BarCocycleH1` and `HeckeReport` followed. For even
`n`, `ρ_n(−I)` now **stays in `FlatMatrix`'s scalar (`αI`) storage** instead of being materialised
as a `d_V × d_V` `vector<vector>` once per simplex — the branch measured **~30 % of the
pre-Phase-3 peak RSS as coming from the `Matrix` conversions alone** (the integrator did not
re-derive that split, which is no longer separable on the merged tree; what is re-measured is the
end-to-end 4.36× of 12.2). `Matrix`/`Matrix64` survive only for `MatrixValidation`,
`HeckeModuleDecomposition` (`d_q ≤ ~20`, 0.004 % of runtime, explicitly left alone by the plan) and
the two read-only consumers of the `Matrix`-typed `A^{(q)}`. The golden `Collector` gained
`FlatMatrixT` overloads whose `HashFlatInto` feeds FNV *exactly the bytes* `HashMatrixInto` did, so
every record that changed type kept its frozen hash.

**Stage B — the cohomology core (`phase3/cohom`).** `EquivariantCohomologyOnK::compute_cohomology()`
now computes **and stores** on the block model, per degree: `A_Cq` via `BlockBuilder` with kinds
`I` / `−M` / `I−M` and every `ρ_n(g)` interned once; `C_eq` = `blk::kernel_basis`; `A_Zq` as
pencils `β_lhs·I − β_rhs·M`, one ref per block; `Z_eq` = one `gemm_dense`; `W` =
`blk::factor_basis` with real `d_V`-wide blocks; `B_eq` = one `gemm_dense`; `H`, `P_q` =
`blk::factor_basis`. The three per-cell loops, the seven representation round trips of `02 §2.2`
and all six raw `mod_*` sites are gone; the 7.4 vacuous-relation short-circuit is preserved. Nine
`*_block` accessors were added; `get_*_bases_fm()` keeps its signatures and legacy shapes and
materialises lazily. **`cohom 128`: 6.317 s / 304 MB → 0.475 s / 80 MB; 19.39 M → 61.4 K
allocations** (the branch's own measurement, `--repeat 3`).

**Stage B — cross-checks, induced system, bar route, coset tables (`phase3/xchk`).** `β_•`'s fibre
data became one `BlockMat` per degree on a shared pool — density ≤ 1/m, so the `m² − m` zero
sub-blocks per block row are *structural*, never written, stored or multiplied — with `α`, `ω` and
the independent `Ξ_g` on the same pool; the `C^q_eq(K,R;L')` basis reuses the cohomology core's own
`BuildACqBlockMat` instead of a second dense copy; the three A-F3 identities became whole-matrix
block GEMMs compared with `blk::equal`, with failure diagnostics re-scanning in the original
per-basis-vector order so a failing run still names the same first offender. `M_H(g_r)` is
assembled block-sparse (the `TODO Q8` of `02 §7.12`). **The cross-check phase of `hecke 96` went
28.74 s → 0.77 s** on the branch (0.62 s on the merged tree), total 32.83 s → 4.90 s.
Independence is preserved *in method*: `t_i` is still rebuilt from the S3 closed form, `j_k`/`h_k`
still come from the exact τ table, no `Θ` table is read.

**Stage B — morphism, simplicial, presets, family (`phase3/morph`).** M1 (the pullback in
`compute_induced_maps_on_cohomology`) and M3 (`apply_to_flat_cochain`) became **one block GEMM each**
against a cached `Φ^{(q)}` built from `fiber_blocks_[q]`. **Contract B6 — the S6 accumulation
order — was verified, not assumed**: every term is an exact product of canonical residues, the
engine accumulates exactly and reduces once per k-block, and a sum of exact integers is independent
of its bracketing, so the GEMM reproduces the old per-column result entry for entry;
`HeckeMorphismRegressionValidation` and strict golden confirm it. A follow-up commit was needed and
is itself instructive: the first version *regressed* `hecke 64 --cross-checks` from 10.2 s to
11.5 s, because S8 applies the composite to **one standard basis vector at a time**, so nearly
every block's operand slice is identically zero — the per-cell code short-circuited those for free
while a dense block GEMM does the full `d_V1 × d_V2` work regardless. The fix iterates the block
pattern (never a cell), skips structurally-zero operand slices, and uses `gemv` straight into the
destination for a single column: 10.2 s → **7.2 s**, i.e. 30 % *below* the pre-migration baseline.

**Stage B — `HeckeOperatorOnK` (`phase3/hecke`).** `Θ^{(q)}` is an `N_q × N_q` `BlockMat` over the
uniform `(N_q, d_V)` partition whose pattern is the `(σ, σ_k)` pairs the τ table names, assembled
by `BlockBuilder::accumulate` from one `BlockRef` per term — the per-cell `mod_add_w` accumulation
is gone. **The two routes are two predefined programs over that pattern**: the fused route memoises
on the τ table's own `ρ` pool, so identical `ρ_n(gγ)` blocks are shared rather than copied
(**5590 refs backed by 2981 distinct pool windows**); route 2 builds from the exact `Mat22` product
**in its own `BlockPool`**, and the two are compared with `blk::equal` — as mathematical matrices,
so the differing pools mean no content dedup can turn the comparison into a tautology. Θ5/Θ6/Θ7/Θ10
are single `gemm_dense` calls (Θ6 checking all `i_basis` at once against a relation block matrix,
Θ7 using `D_1 ⊗ I` as `Scalar ±1` blocks), Θ8 is one `blk::solve_multi_rhs` for all RHS, Θ9's A-N3
residual is one `kernels::gemm` with `GemmOp::Sub` plus a zero scan. **`hecke 128`: 4.62 s → 0.82 s
total, operator assembly 4.23 s → 0.37 s, RSS 145.7 → 108.4 MB** (the branch's own measurement).

**Stage B — the `BlockFlatMatrix` trim (`phase3/trim`, merged last).** With the pipeline on the
block model, `BlockFlatMatrix` is *legacy-arm only*, and the plan's "delete `BlockFlatMatrix`'s
validation-only surface once `BlockFlatMatrixValidation` is re-pointed at `BlockMat`" became
collectable: **702 lines out of `BlockFlatMatrix.cpp` and 139 out of the header** —
validation-only members, `IntermediateRREFForm`, dead `DEBUG_BLOCKFLATMATRIX` scaffolding —
keeping exactly the members the legacy arms and the validations still call. The block-diagonal and
sparse-grid cases were **ported into `BlockEliminationValidation`** (+49 entrywise checks) rather
than dropped, the surviving `BlockFlatMatrixValidation` checks were made entrywise, and the
RREF-idempotency self-check was revived under `ENGINE_DEBUG_CHECK`. Deprecation is enforced by a
**header banner plus an extended `check_matrix_includes.sh`** rather than `[[deprecated]]`, which
would have added 103 warnings: the script now guards `BlockFlatMatrix.h` as a second header with a
deliberately tiny allow-list — `ModArithmetic/`, `*Validation.*`, and the two production headers
that still declare legacy-arm members (`EquivariantCohomologyOnK.h`, `SimplicialCohomology.h`) —
so a new consumer cannot appear without the guard failing. The class is removed once Phase 4 ships.

### 12.4 Decisions recorded

1. **The τ solver was NOT absorbed — a policy mismatch, not a pivot-rule mismatch.** The plan makes
   the absorption of `HeckeTauTable.cpp:228-263` conditional on the engine reproducing *both* the
   pivot rule and the ℤ-first / mod-`ℓ`-fallback policy. The **pivot rule matches exactly**
   (leftmost column with a nonzero entry, topmost such row, full reduction, free variables at 0 —
   entry for entry what `solve_multi_rhs` computes from `RREF([B | y])`). The **policy does not**:
   the solver signals infeasibility by `return false`, and its only caller uses that as the second
   arm of the ℤ-first ladder inside the triangle-fill solve at `:783-910` — the function the plan
   says is *not migrated in any phase*, because τ's derivation is first-match-wins (`02 §6.5(2)`).
   `solve_multi_rhs` throws instead, so absorbing it would re-express a determinism-critical ladder
   as exception control flow keyed on a type `ENGINE_CHECK` also uses for genuine engine bugs; and
   the free-variable convention it relies on for a rank-deficient system is not part of
   `ENGINE_API.md §8`'s stated contract. Verdict and full argument live in
   `docs/matrix-engine/tools/raw_mod_calls.allow`, next to the file's permanent allow-list entry.
   Cost of leaving it: **none measurable** (the 7-vertex model, at most 11 columns).
2. **The API gap that verdict exposes.** The plan calls this absorption "the API's acceptance test:
   if a loop survives, the API is missing a primitive". One survives, and the missing primitive is
   named: `engine::elim` has **no non-throwing solve** — a `bool try_solve_multi_rhs` returning
   `false` for an out-of-span right-hand side. With that, and with the free-variable convention
   written into `ENGINE_API.md §8`, this solver becomes a two-line call. **Phase 4 item.**
3. **The *other* hand-rolled solver WAS absorbed.** `BarCocycleH1.cpp:119-163` had no ℤ-first
   policy to reproduce (that belongs to the τ solver) and its pivot rule is literally D5b's, so it
   became `engine::elim::solve_multi_rhs`, with the throw caught and converted back to `false`
   where `MinPolyOfMatrix` uses inconsistency to find the degree. It is pinned by a **frozen
   oracle**: `BarCocycleSolverValidation` compares a byte-for-byte copy of the pre-absorption body
   against the engine route on 1830 fixed-seed systems — verdict *and* entrywise coefficients —
   including cases the production call sites never reach.
4. **`A^{(q)}` stays `MatrixT`.** `HeckeModuleDecomposition` consumes it and is explicitly out of
   scope (`d_q ≤ ~20`, 0.004 % of runtime, `03 §4.3`), so the `MatrixT`-typed `A^{(q)}` remains the
   boundary, and `Golden/GoldenHarness.cpp` + `Bench/BenchDriver.cpp` remain on the
   `check_matrix_includes.sh` allow-list as its two read-only consumers.
5. **`Θ_eq` stays a dense `FlatMatrix`.** It is `dim C^q_eq × dim C^q_eq` with no exploitable block
   structure (the solve mixes all coset contributions), so blocking it would add metadata without
   removing work.
6. **`apply_route2` stays matrix-free** (gemv + axpy per term) rather than being expressed on the
   block: its whole value is being an independently bracketed evaluation, and routing it through
   the same block object would weaken the O12 independence claim.
7. **The D3 layout planner is deferred to Phase 4**, as designed. Layout choices are currently made
   by the fixed preferences of `ENGINE_API.md §9.2(3)`, not planned per program.

### 12.5 Bit-identity evidence

Phase 3 is the largest diff of the programme, and its entire claim is that **no computed value
moved**. The evidence, in the order it gates:

* `GOLDEN_STRICT=1 GoldenRegressionValidation` — **tier A 9446 failing 0, tier B 4603 mismatching 0
  on all five configurations** (default, `Bench`, `Debug`, `HECKE_PURE_INTEGER=ON`,
  `ENGINE_SHADOW_LEGACY=ON`), i.e. with the *legacy basis choices* also gating. This is the
  strongest statement available and it is unconditional.
* The **kept legacy arms**. Every migrated consumer keeps its pre-Phase-3 code path verbatim.
  `ENGINE_BACKEND=legacy` selects it process-wide (and `./hacs --all` is green on it,
  50/50); `EquivariantCohomologyOptions::ScopedLegacyCohomologyPath` and
  `HeckeOperatorOptions::ScopedLegacyHeckeOperatorPath` select it in-process, per class, which is
  what lets the new validations compare both arms **inside one run**.
* `-DENGINE_SHADOW_LEGACY=ON` runs **both** arms on every call and throws on the first differing
  entry. Green on strict golden and on `LocalSystemCohomologyValidation`,
  `HeckeEndToEndValidation`, `HeckeOracleValidation`, `HeckeCrossCheckValidation`,
  `CohomologyBlockModelValidation`, `HeckeThetaBlockValidation`.
* The new validations compare **bases entrywise, never by span** (D5b): 56 952 checks in
  `BlockMatValidation`, 10 121 in `BlockEliminationValidation`, 10 792 in
  `CohomologyBlockModelValidation`, 4 745 in `HeckeThetaBlockValidation`, 1830 systems in
  `BarCocycleSolverValidation` — plus `BlockModelPipelineValidation` on the *real* `A_C0/1/2`,
  `W¹` and `H¹` problems.
* **Sanitizers clean.** `-DCMAKE_BUILD_TYPE=Check` (`-fsanitize=address,undefined`, no `NDEBUG`, so
  every `ENGINE_DEBUG_CHECK` is live), `ASAN_OPTIONS=detect_leaks=1`
  `UBSAN_OPTIONS=print_stacktrace=1`, running `BlockMatValidation` (1.2 s),
  `BlockEliminationValidation` (267 s), `CohomologyBlockModelValidation` (4.6 s),
  `HeckeThetaBlockValidation` (4.5 s), `BarCocycleSolverValidation`,
  `LocalSystemCohomologyValidation` and `HeckeEndToEndValidation` (9.5 s): **7/7 exit 0, 0
  findings, 0 leaks.**

### 12.6 E10 (projected memory at `n_sym = 1000` ≤ 1.5 GB) — why it misses, measured

The plan states this criterion against an extrapolation, so it is answered with one. Peak RSS was
measured out to `n_sym = 256` (new points at 224 and 256, added for this purpose) and fitted two
ways over `n ≥ 128`:

| fit | hecke | cohom |
|---|---|---|
| power law `RSS ∝ n^k` | `k = 1.92`, ⇒ **5.2 GB** at `n = 1000` | `k = 1.88`, ⇒ **4.5 GB** |
| affine `RSS = a + b·n²` | `26.6 MB + 5.27·10⁻³·n²` MB ⇒ **5.3 GB** | `27.2 MB + 4.72·10⁻³·n²` MB ⇒ **4.7 GB** |

Both fits agree, and both agree with theory: the surviving large objects are genuinely `Θ(n²)` —
the `C_eq` basis is `(N_q·d_V) × dim C^q_eq` ≈ `11n × 9n`, `Θ_eq` is `dim C^q_eq` squared, and
`factor_basis`'s `R` is `a × (n_rel + n_gen + a)`. So **E10 misses by ≈ 3.2×.**

What Phase 3 *did* deliver on memory: the same `n²` extrapolation from the pre-Phase-3 tree gives
≈ 27 GB (as `02 §5.1` found), so the phase is a **5.2× improvement in the projection**, on top of
meeting E2 (the measured `hecke 128` criterion) with 17 % of margin. The gap to 1.5 GB is *not*
recoverable by better orchestration: at `n = 1000` the three objects above are ~400 MB, ~330 MB and
~485 MB of *mathematically necessary* dense data, and E10 was set (§ "Phase 3" exit criterion)
against a `02 §5.1` estimate that itself only "covers the three representation fixes and omits the
`C_eq` basis, `Θ_eq` and the `factor_basis` workspace". Closing it requires **not storing all three
simultaneously** — streaming `factor_basis` panels to a scratch arena and releasing `Θ_eq` after
`A^{(q)}` is read — which is Phase 4's arena allocator with per-program buffer lifetimes (D4), not
a block-model change. **E10 is therefore re-asserted as a Phase 4 exit criterion**, with this
subsection as its brief.

### 12.7 Merge-level changes made by the integrator

None beyond conflict resolution. The four Stage B branches touched disjoint file sets by design;
the only overlaps were `ValidationRegistry.cpp` (new registrations, resolved as unions),
`raw_mod_calls.allow` (each branch deleting its own backlog lines) and `ENGINE_API.md`.
`phase3/trim`, merged last, was **conflict-free** (its file set — `BlockFlatMatrix.*`,
`BlockFlatMatrixValidation.*`, `BlockEliminationValidation.cpp`, `MatrixRetirementValidation.cpp`,
`check_matrix_includes.sh` — is disjoint from the Stage B branches', and it registers no new
validation). No behavioural change was needed at any merge.

Everything in 12.1–12.2 was re-measured on the **final** tree, after the trim merge, rather than
trusted from the branches: strict golden in all five configurations, `--all` / `--all-full` /
`ENGINE_BACKEND=legacy --all`, and the two exit-criterion benchmarks. The trim is
value-preserving to the bit — `hecke 128` and `cohom 128` report **byte-identical allocation
counts and peak RSS** before and after it (19 641 / 100.3 MB and 61 324 / 92.0 MB), times within
noise (0.845 → 0.832 s, 0.462 → 0.460 s) — which is the expected result for a change that only
deletes unreachable code.

### 12.8 Carried forward to Phase 4

* **E10 (projected memory at `n_sym = 1000` ≤ 1.5 GB) moves to Phase 4**, with 12.6 as its brief:
  the fix is D4's arena with per-program buffer lifetimes, not the block model.
* **`bool try_solve_multi_rhs`** — the API gap of 12.4(2). Adding it, and writing the
  free-variable convention into `ENGINE_API.md §8`, retires the last hand-rolled solver in
  `HeckeTauTable.cpp:228-263`. (The triangle-fill solve at `:783-910` stays unmigrated, by plan.)
* **The `cohom` allocation count still grows with `n_sym`** (32 K at 64 → 120 K at 256) through the
  lazily materialised `get_*_bases_fm()` compatibility lists — one `FlatMatrix` per basis vector.
  The plan's own Phase 3 scope says these accessors exist "until every validation is migrated, then
  removed"; `phase3/trim` re-points `BlockFlatMatrixValidation`, and the remaining consumers can
  follow in Phase 4.
* **`BlockFlatMatrix` is removed when Phase 4 ships.** It survives only as the legacy arm's
  container, behind the extended `check_matrix_includes.sh` guard whose allow-list names its two
  remaining production headers. Dropping `ENGINE_BACKEND=legacy` retires the class.
* **A `k ≤ 8` gemm specialisation** (§11.7) was again not taken; with the block model in place the
  shape census that motivated it no longer describes the workload, so it should be re-measured
  before being scheduled.
* **The FP64 Barrett epilogue** (§11.3) remains a documented, bounded deviation from integer-only
  arithmetic.
* The §9.4 caveats (duplicated `IsDicksonExceptional`; `Θ^{(q)}_flat` at `r = 1` only;
  `GoldenRegressionValidation` tiered `standard`) and §10.5's defect #11 are **still open**.
* **Warning census: 94 → 69** (`-Wall -Wextra`, all three targets), i.e. **−25** — 82 after the
  Stage A/B merges and 69 after the `phase3/trim` merge, which removed the 13
  `-Wmisleading-indentation` / `-Wunused-parameter` hits in the deleted
  `BlockFlatMatrixValidation` surface. No warning is
  emitted by any new engine file (`BlockPool.h`, `BlockMat.h`, `BlockKernels.*`, `BlockElim.*`) or
  by any migrated consumer TU. The only *new* warnings are three `-Wunused-function` for leftover
  helpers in `BlockModelPipelineValidation.cpp`; the net fall is the `Matrix` retirement removing
  `-Wdeprecated-declarations` hits from pipeline TUs. `cohomology_app`'s temporary
  `-Wno-deprecated-declarations` still cannot be dropped (`HeckeModuleDecomposition` and the
  `A^{(q)}` boundary account for ~300 suppressed hits), but its original reason is gone: the
  suppressed count fell from ~1440 to ~450.
* `CLAUDE.md` and `src/hacs/Hecke/README.md` were updated in the same commit as
  this record.

## 13. Phase 4 — execution record (2026-09-06, Stage B consumer wiring)

Stage A (the engine core: tape/IR, passes, executor, pool, program cache, `TapeElim`) was merged
as `phase4/core`; Stage B put the consumers on it (branch `phase4/wire`, on top of the
`phase5/backend` + `phase6/campaign` merges). Contract: `ENGINE_API.md §10.9`.

### 13.1 Exit criteria

Default build, `--repeat 3` (min), 16-core / 32-thread reference machine; `ENGINE_THREADS`
default = 32.

| criterion | measured | verdict |
|---|---|---|
| `hecke 256 134217757 2` ≥ 8× at the default thread count vs `ENGINE_THREADS=1` | 3.898 s → 1.181 s (32 threads) = **3.3×**; 1.137 s at 16 threads = 3.4× | **FAIL** |
| `hecke 128 134217757 2` ≥ 4× | 0.570 s → 0.270 s (32) = **2.1×**; 0.229 s (16) = 2.5× | **FAIL** |
| `family 128 134217757 2 2` wall ≤ 1.2× a single `hecke 128` | 0.384 s vs 0.319 s (32 threads) = **1.20×**; 0.285 vs 0.229 = 1.24× at 16 | **PASS (at the margin)** |
| hashes identical across all thread / batch / device settings | `EngineDeterminismValidation`: 8 arms (`ENGINE_THREADS ∈ {1,4,16,32}` × `ENGINE_BATCH ∈ {0,1}`), 966 golden records each, 0 differing from the reference, one digest; strict golden at 1/16/32 threads; `EngineCrossDeviceValidation` 372/0 | **PASS** |
| E10: projected RSS at `n = 1000` ≤ 1.5 GB | lean fit 1.25 GB; **measured `cohom 1000 --lean`: 1157 MB**; non-lean 4.9 GB | **PASS** (memory-lean configuration; 05 §9) |
| Phase 5 carry-over: `cohom 1000` ≤ 1.5 s under `ENGINE_DEVICE=gpu` | cpu 24.6 s / 1157 MB; hybrid 25.8 s / 1451 MB; gpu 80.1 s / 1449 MB | **FAIL** |

**Where the serial remainder is** (`hecke 256`, `ENGINE_TRACE_ELIM=1`, 1 → 16 threads): setup /
coset / τ 0.02 s (serial by design); cohomology 1.34 → 0.59 s (**2.3×**); operator assembly
(Θ, route 2, `Θ_eq` solve, A-N3, `A^{(q)}`) 2.64 → 0.52 s (5.1×). Inside the elimination driver
(sums over concurrent executors): host recording + bookkeeping 0.09 → 0.17 s, compile 0.05 s,
per-panel programs P1 0.61 → 0.28 s of which the host-serial `PANEL_RREF` / `PIVOT_SEARCH` nodes
are 0.19 → 0.21 s (the trailing-update hook parallelises their GEMMs, the 32-wide Crout base
panels remain serial), P2 0.97 → 0.12 s. The pool runs one region at a time, so the consumer-level
fan-out (axes (c)/(d)) buys little on top of the intra-program parallelism and 32 threads are
slightly *worse* than 16 (SMT siblings compete with the host threads). Closing the gap needs a
parallel panel factorisation (a tape `PANEL_RREF` that is itself a wavefront program) and fewer,
larger programs per elimination — both engine-core work, not consumer wiring.

### 13.2 Validations

New, both `standard` and in `--all`: **`EngineTapeConsumerValidation`** (246 checks: tape vs the
direct `engine::blk` path entrywise on the consumers' stored objects; cache replay == fresh
recording == forced fresh compile, also on another pool size; a changed τ pattern misses) and
**`EngineDeterminismValidation`** (above). Kept green: `--all`, strict golden in every thread
setting, `HeckeFpFilterValidation` with its exact `PredicateStats` counts (τ construction
untouched), `EngineTapeEliminationValidation` (8489 checks, the new `factor_basis` vs the
identity-augmented reference), `CohomologyBlockModelValidation` (10788 checks, `B^q` via the
image basis vs the legacy arm). `--all`: 63/63 (158 s); `ENGINE_BACKEND=legacy --all`: 63/63
(`EngineTapeConsumerValidation` reports SKIP on the legacy arms, which record no programs).
**TSan** (`CheckThread`, `setarch -R`): `EngineDeterminismValidation`, `HeckeEndToEndValidation`,
`EngineTapeConsumerValidation`, `CohomologyBlockModelValidation` — 0 reports (the only finding,
the bench driver's non-atomic allocation counters, was fixed). **ASan/UBSan** (`Check`): the same
four plus `EngineTapeEliminationValidation` — 0 findings, leaks included.

### 13.3 Device arms (report only; default stays `cpu`)

`--repeat 2`: `cohom 256` cpu 0.718 s / hybrid 0.622 s / gpu 0.732 s; `hecke 256` cpu 1.314 s /
hybrid 1.153 s / gpu 1.451 s. `cohom 1000 --lean`: cpu 24.6 s (1157 MB), hybrid 25.8 s
(1451 MB), gpu 80.1 s (1449 MB). The per-panel elimination programs are one-shot, so the `gpu`
arm re-uploads (§12.5 rows A/B) and loses 3.3× at `n = 1000`; `hybrid` keeps them on the CPU and
wins ~13 % on the block GEMMs at `n = 256`, nothing at `n = 1000`.

> **Re-measured at integration (2026-09-06, final `matrix-engine` tree, quiet box).** The CPU arm
> of the last row improved with the 13.7 closure, which was never re-run at `n = 1000`:
> **`cohom 1000 --lean` is 14.8 s / 1157 MB** (peak RSS unchanged to the megabyte), and
> `hecke 1000 --lean` is **14.4 s / 1394 MB** — a figure this record never had. The device arms
> were not re-measured; the `gpu` deficit is structural (§14.4), so the gap only widens. The
> `hecke`/`cohom 256` and thread-ratio rows re-measure within 2 % of 13.7 and are left as they
> stand (`hecke 256` 2.607 / 0.555 / 0.556 s at 1 / 16 / 32 threads; `hecke 128` 0.383 / 0.111 /
> 0.121; `family 128` 0.148 s at 16 = 1.33× a `hecke 128`), so **all three ratio criteria still
> fail, by the same margins**.

### 13.4 Defects found and fixed on the way

* **Shared-pool borrow race** (`factor_basis` / `solve_multi_rhs`, both drivers): the borrowed
  operand was held only through the augmented `BlockMat`, whose destructor freed and *recycled* the
  id before `sweep_if_unreferenced(id)`; with the pool shared by concurrent degrees another
  thread's fresh block was freed — a 1-in-3 abort of `CohomologyBlockModelValidation` and a
  `--all` exit 134. Fixed with an explicit acquire/release hold; no stale-id sweep remains.
* `GrowRows::take()` returned a `0 × 0` buffer for rank-0 eliminations (36 failures in
  `EngineTapeEliminationValidation`).
* Every `Executor` probed CUDA in its constructor: +110 MB of RSS on every CPU run, on top of the
  `kernel.cu` probe the memory profile had found.
* The legacy arm segfaulted under `--lean` (`C_eq_dims_` unset).

### 13.5 Decisions recorded

1. **Memory-lean is a mode, not the default**: every validation, the golden objects and the JSON
   certificate are unchanged by default; `--lean` (and the campaign's `lean`) turn the `Θ_eq`
   certification and the retained intermediates off, sequence the degrees, and record
   `"theta_eq_certified": false`.
2. `HeckeOperatorOptions::memory_lean()` is kept for the campaign but the engine arm now always
   streams route 2.
3. Scoped consumer options are thread-local and propagated into the fan-out (the campaign
   engineer's flag), rather than process-wide atomics.
4. The pool size default stays `min(hardware_concurrency, 32)`; the measurements above are
   reported at both 16 and 32.

### 13.6 Carried forward

* The speed criteria (13.1): parallel panel factorisation; fewer programs per elimination; a pool
  that can run regions of different executors concurrently.
* Cross-program residency of pool inputs on the device (`§12.7` item 2).
* `C² = Z² = I` stored densely while live (05 §7); an `Identity` multi-vector kind.
* `BlockFlatMatrix` removal (the legacy arms still use it).

### 13.7 Performance closure (2026-09-06, branch `phase4/perf`)

The two missed speed criteria of 13.1 were attacked from the profile, not from the plan's guesses.
A per-op / per-class trace was added first (`ENGINE_TRACE_NODES`, `EngineTrace.h`: node / task /
busy per op, region wall vs busy per thread class, executor and compile wall, pool region wall,
idle inside regions, region-mutex wait, the dense PLU's phase split; `ENGINE_TRACE_RSS` now also
marks every Hecke assembly phase, every `tape::rref` and every unit-row solve).

**Profile at the start** (`hecke 256`, 16 threads, 1.18 s wall): pool regions covered only
0.36 s (30 %) of the wall — the workers were idle 70 % of the time; host time outside the
executor and the compiler was 0.53 s (45 %), the host-serial `PANEL_RREF` / `PIVOT_SEARCH` nodes
0.21 s. Inside the dense PLU (140 calls, 0.56 s summed): `to_rref`'s serial `U^{-1}` solve 0.21,
the Crout base panels 0.16, the trailing TRSM 0.09, the (only hooked) trailing GEMM 0.09. The
critical path was the `q = 1` chain (`image_basis` 0.09 + `factor_basis` 0.37, of which the
stage-2 host steps — a 1028² inverse, a single-threaded 1799×1028×1028 GEMM, an in-place
1799×2827 dense RREF — 0.27) followed by the `q = 1` operator (`Θ_eq` solve 0.22 as an
`2827 × 4626` elimination, A-N3 0.12 with a physical TRANSPOSE and a column-major output, 45 ms of
`FlatMatrix` re-reduction in the `Θ_eq` hand-over), with the degrees of the operator sequential.

**What was done, in order, and what each step bought** (`hecke 256`, 16 threads, min of 3, on
a box shared with the campaign engineer's jobs — load 8–30 throughout, so every figure is
pessimistic and the ratios are the reliable part):

| step | change | `hecke 256` @16 |
|---|---|---|
| 0 | merge tip `32cc62d` | 1.117 s |
| 1 | hook-parallel column tiles of both TRSMs, row tiles of the Crout Schur step (pivot scan fused, multiplier scaling deferred), stage-2 `Mact·Winv` over the hook | 0.929 s |
| 2 | unit-row `Θ_eq` solve (one exact product instead of the `[C_eq | W]` elimination), A-N3 recorded as `W^T -= coords·C_eq^T` (no relayout, row-major output), `PIVOT_SEARCH` from the PLU factor alone, the Hecke degrees as `run_concurrently` tasks, spin-then-block join in the pool | 0.645 s |
| 3 | the pool runs regions of different callers concurrently (registry + task claiming, epoch-gated rescans, `pause` spinning) | 0.636 s; **32 threads 0.86 → 0.69 s** |
| 4 | `certify = false` for the solve under A-N3, `L21` read in place, row-list `GATHER` (17.6 K → ~1 K P2 gathers), `FlatMatrix::FromCanonical` | 0.591 s |
| 5 | Crout base 32 → 1 (every column step a vectorised rank-`k` update; base panels 0.52 → 0.025 s summed) | **0.538 s**; 1 thread 3.39 → **2.60 s** |

Steps 1–5 are all value-preserving by construction (disjoint rows / columns of exact modular
values; unique coordinates; the same products), and were gated at each commit by
`DenseElimValidation`, `EngineTape*`, `EngineDeterminism*` (8 arms, one digest),
`CohomologyBlockModelValidation`, `HeckeThetaBlockValidation`, `HeckeFpFilterValidation` (exact
`PredicateStats`: τ construction untouched), `HeckeEndToEndValidation`, `EngineTapeConsumer`,
`GOLDEN_STRICT=1` golden at 1 and 16 threads; `--all` 63/63 on the final tree; **TSan**
(`CheckThread`, `setarch -R`): `EngineTapeValidation`, `EngineDeterminismCoreValidation`,
`EngineTapeConsumerValidation`, `CohomologyBlockModelValidation`, `HeckeEndToEndValidation`,
`EngineDeterminismValidation` — 0 reports (one real race in the first concurrent-pool patch — a
`Region` read after the member count that lets the caller free it — was caught by TSan and fixed
before it shipped).

**Final table** (default build, min of 4–5, loaded box; "baseline" = this binary at
`ENGINE_THREADS=1`, "13.1" = the Stage B figures of 13.1):

| benchmark | 1 thread | 16 | 32 (default) | speed-up vs 1 | vs the 13.1 single-thread figure |
|---|---|---|---|---|---|
| `hecke 256 134217757 2` | 2.602 s | **0.538 s** | 0.560 s | **4.8× / 4.6×** (target 8×: **FAIL**) | 3.898 → 0.538: 7.2× |
| `hecke 128 134217757 2` | 0.402 s | **0.125 s** | 0.133 s | **3.2× / 3.0×** (target 4×: **FAIL**) | 0.570 → 0.125: 4.6× |
| `family 128 134217757 2 2` | — | 0.161 s | 0.174 s | 1.29× / 1.27× a single `hecke 128` (target ≤ 1.2×: **FAIL, at the margin**; it was 1.20× at 32 threads in 13.1 with a 2.3× slower `hecke 128`) | — |

The ratio criteria moved *against* the closure: steps 2 and 5 sped the single-thread baseline up
by 1.47× (3.82 → 2.60 s) — the unit-row solve and the vectorised base panel are serial
improvements — so the denominator shrank as fast as the numerator. Against the 13.1 baselines the
walls are 7.2× and 4.6× lower; against the same binary they are 4.8× and 3.2×.

**Where the remaining serial time is** (`hecke 256`, 16 threads, 0.551 s, `ENGINE_TRACE_NODES`):

* setup + coset tables + τ construction: **0.019 s** (3.5 %) — the design floor (τ is serial by
  plan; `HeckeFpFilterValidation`'s exact counts prove it stayed so).
* host-serial nodes (`PANEL_RREF` + `PIVOT_SEARCH`, 35 of them): 0.106 s (19 %) — now dominated
  not by arithmetic (the PLU's phases total 0.196 s *summed over 81 calls* and are mostly hooked)
  but by the per-panel structure itself: each 256-wide panel is a sequence of ~250 dependent
  column steps, each a small hook region or a serial rank-`k` update.
* host time outside executor + compile: 0.184 s (33 %): `BlockBuilder` assembly, recording,
  bookkeeping of the panel driver, the `factor_basis` stage-2 host steps of `q = 1` (inverse 0.035,
  `Y` assembly 0.025, `Y` RREF 0.068 — hook-parallel inside, but on the chain's critical path),
  the `Θ_eq` hand-over.
* pool regions: 0.292 s of wall (53 %) at a mean width of 11.0 of 12.9 threads, 15 % idle inside
  regions (tails of small regions).

The critical path is unchanged in shape: the `q = 1` cohomology chain (0.29 s: `image_basis`
0.06, `factor_basis` 0.215) then the `q = 1` operator (0.16 s: program 1 0.063, A-N3 0.055, solve
0.014, hand-over 0.018). Reaching 8× on the same binary (≤ 0.33 s) would need the chain's
elimination structure changed — a `PANEL_RREF` that is itself a wavefront program with a
parallel panel factorisation (recursive PLU whose every level's trailing update is a batched node),
fewer / wider panels, and `factor_basis` stage 2 as tape programs rather than host PLUs — i.e.
the items of 13.6 that were *not* attempted here because they change the elimination driver's
program structure, not its schedule.

**32 vs 16 threads.** Before the concurrent pool, 32 workers spinning on `sched_yield` in every
idle gap competed with the host threads' serial work (13.1's "SMT siblings"), and after the first
concurrent-pool patch surplus workers that could not join a full region hammered the registry
mutex (0.86 s). With `pause`-based spinning and epoch-gated rescans 32 threads is within 4 % of
16 on both sizes (0.560 vs 0.538 s; 0.133 vs 0.125 s) — no longer *worse* in any measured case,
but not better either: the pipeline has no phase left that is compute-bound enough for SMT to pay.
Affinity / pinning was not attempted: WSL2 exposes `sched_setaffinity`, but the host scheduler
behind it does not honour the pinning on this box, and the shared load made a measurement
meaningless.

**Decisions.** `Params::base = 1` (env `ENGINE_ELIM_BASE` still overrides; `DenseElimValidation`
sweeps it); the Hecke degrees fan out in the default mode and stay sequential in the memory-lean
mode; `tape::solve_multi_rhs(certify)` defaults to `true` — only `HeckeOperatorOnK` (which runs the
same exact residual as A-N3 right after) passes `false`; the pool's concurrency is unconditional
(there is no serialised mode left to fall back to: `ENGINE_THREADS=1` is the single-threaded arm).


---

## 14. Phase 5 — execution record (2026-09-06)

Two stages, two branches: **`phase5/kernels`** — the device layer, merged as `8d16a3d` — and
**`phase5/backend`** — the tape ↔ device seam, merged as `c341910`. The binding contract is
`src/ModArithmetic/ENGINE_API.md` **§11** (`src/Cuda/`, `engine::cuda`) and
**§12** (`src/Engine/DeviceBackend.h/.cpp`, passes 6/7 of `Passes.cpp`); this section
is the execution record those two sections were written without, and it is the reason the phase
records jump from §13 to §15 in every earlier revision of this file.

Hardware of record: RTX 5070 Ti (cc 12.0, 16 GB), driver 610.53 / CUDA 13.3 UMD, nvcc 13.0,
WSL2 — the same box as every other phase.

### 14.1 Exit criteria

| criterion | measured | verdict |
|---|---|---|
| blocked GEMM ≥ **2 TmodMAC/s** at `4096³`, k-blocked into ≥ 4 chunks | **2.25 T** (`gpu`) / 2.30 T (`hybrid`) *through the tape, transfers included*; the kernel alone 3.9 T; the 192 MB of transfers are ≈ 13 ms of the 30 ms. At `ℓ = 134217757`, `k_max = 1023` and the kernel flushes every `kb = min(k_max, 256) = 256` products, so a 4096-deep dot is **16 chunks**; the unblocked variant `kernels::dot_delayed(ctx, a, b, 4096)` trips `ModContextValidation`'s `k ≤ k_max` `ENGINE_CHECK` and an unchecked accumulation yields 130777117 where the exact value is 4096 | **PASS** |
| batched `d = 100` GEMM ≥ **20×** the CPU single-thread rate on a 256-instance batch | **17.2×** (E2, the Θ shape, 32 in / 32 out blocks: 0.57 ms against 9.9 ms; 447 G against 26 G). E1, with 256 *distinct* in/out blocks and 21 MB moved: 8.8×. The kernel itself is 0.13 ms = 2 T; ≈ 0.4 ms of the 0.57 ms is ~30 µs per staged copy × 10 buffers + 3 graph launches | **FAIL** (transfer latency, not arithmetic) |
| `EngineCrossDeviceValidation` exit 0 | **372 checks, 0 failed** (13.2 s at integration): 10 settings (`cpu`/`gpu`/`hybrid` × threads × batching × graph mode × verify) over `p ∈ {134217757, 2^31−1, 2^32−5, 7}` (u32) and `{2^61−1, 134217757}` (u64), hashes identical | **PASS** |
| golden grid identical under `ENGINE_DEVICE ∈ {cpu, gpu, hybrid}` | `GOLDEN_STRICT=1 GoldenRegressionValidation` — tier A **9446 / failing 0**, tier B **4603 / mismatching 0** under `cpu` (5.5 s), `gpu` (17.2 s) and `hybrid` (11.0 s), and at `ENGINE_THREADS=1` (3.1 s) and under `ENGINE_BACKEND=legacy` (9.3 s) | **PASS** (closed at integration; §12.5 recorded it *pending* because the consumers were not yet on the tape when Phase 5 shipped) |
| a `-DENGINE_VERIFY_DEVICE=ON` build runs the end-to-end gate | the `cross_config.sh` row `RelWithDebInfo+ENGINE_VERIFY_DEVICE=ON@ENGINE_DEVICE=gpu`, §16.3: strict golden and `HeckeEndToEndValidation` green with every GPU node re-executed on the CPU and compared entrywise | **PASS** |
| `EngineCudaMemoryValidation`: the pinned pool never exceeds its cap, no pageable D2H | 17 checks, 0 failed: a 144 MB operand through the 128 MB pool (peak = cap, 25 chunk waits), `pageable_copies == 0`, arena `live_bytes` back to baseline after `release_device_state()` and after executor teardown | **PASS** |
| **the GPU is never enabled by default until the unblocked-kernel trap (`04 §6.3`, R6) is shown avoided** | the trap table of 14.4 is the evidence, and it shows the trap is *real* on this workload; `ENGINE_DEVICE` default stays `cpu` | **PASS** |
| `cohom 1000 134217757` ≤ **1.5 s** under `ENGINE_DEVICE=gpu` | cpu 24.6 s / 1157 MB, hybrid 25.8 s / 1451 MB, **gpu 80.1 s** / 1449 MB (§13.3). On the final tree the CPU arm is **14.8 s / 1157 MB**; the `gpu` arm is not competitive at any measured size | **FAIL** |

Two of nine miss, and they are the same defect seen from two ends: **nothing is amortised across
programs**. The batched criterion misses by transfer *latency* (the arithmetic is at 2 T), and the
consumer-level criterion misses because the elimination driver records one program per panel, so
the `gpu` arm re-uploads every panel operand instead of keeping the pool's blocks resident.

### 14.2 Stage A — the device layer (`phase5/kernels`)

`src/Cuda/`: `CudaCtx.h/.cpp` (context, 3 non-blocking streams, the ≤ 128 MB
`cudaHostAlloc` **pinned staging pool** with a 4-thread `CopyPool`, the device arena, staged
transfers, graph capture), `DeviceBuf.h` (mirror + two-counter residency + `DeviceView`),
`CudaKernels.h` / `cuda_kernels.cu`, `CudaValidation.cpp`, `CudaBench.cpp`. Static library
`EngineCuda`; **every public header is CUDA-header-free**, so the tape includes them from plain
C++ TUs. No floating point, no atomics on results: split-K partials are canonicalised to `[0,p)`
and summed mod `p` in a fixed order, which is the only cross-block reduction in the layer.

**Measured (§11.6), re-confirmed on the final tree where marked:**

| | rate | roofline (`04 §1.5`) |
|---|---|---|
| u32 GEMM 512³ / 1024³ / **2048³** / 4096³ at `ℓ = 134217757` | 2446 / 3816 / **4064** / 3915 G modmul/s (**4064.99 G re-measured at 2048³**, `--bench micro gemm 2048 --backend gpu --repeat 5`) | 4931 G → 50 / 77 / **82 %** / 79 % |
| u32 GEMM 2048³ at `2^31−1` (`k_max = 4`) / `2^32−5` (`k_max = 1`) | 1628 / 523 G | 2460 G (eager) → 66 / 21 % |
| u64 GEMM 512³ / 1024³ / 2048³ at `2^61−1` | 257 / **275** / 274 G | 629 G → 41 / 44 / 44 % |
| batched 2000 × 129³: CPU 1 thread / 2000 stream launches / **one batched launch** / graph replay | 26 / 198 / **2067** / 2066 G | **79× CPU-1** (Phase 5 floor: 10×) |
| pinned direct H2D / D2H; staged through the pool (4 copy threads); pageable direct | 55 / 55; 18.0 / 14.4; 15 / 13 GB/s | doc 04: 55.5 / 56.0; —; 24.4 / 5.1 |
| launch: graph node / async stream / launch+sync | **0.80** / 6.0 / 21 µs | 0.68 / 6.11 / 24.0 |

Phase 5's two *kernel-level* floors are both cleared with margin: dense u32 GEMM ≥ 40 % of the
roofline at 2048 (**82 %**) and the batched small-block program ≥ 10× the CPU single-thread rate
(**79×**). `CudaBitIdentityValidation` asserts the device result is the same **bytes** as the CPU
result by `memcmp`: **10,844 checks**, 0 failures, 7.2 s; `CudaTransferValidation` 27 checks.

**WSL2 caveats that shaped the design** (§11.7): `cudaHostRegister` is unsupported, hence the
staging pool (`std::vector` storage is never pinned); reading `cudaHostAlloc`ed memory from *one*
host thread runs at 5.4 GB/s, so a single-threaded staged D2H was slower than a pageable
`cudaMemcpy` — hence the persistent 4-thread `CopyPool` (`ENGINE_CUDA_COPY_THREADS`); the first
launch of each kernel instantiation costs milliseconds (lazy module loading), so `--repeat 1` on
a fresh process is not a measurement; no MPS, one process per GPU.

### 14.3 Stage B — the tape ↔ device seam (`phase5/backend`)

`MatrixEngine` links `EngineCuda`; every `Executor` owns one `DeviceBackend` when
`engine::cuda::available()`, and GPU-assigned nodes fall back to the CPU when it does not
(`ExecStats::fallback_nodes`). **A value never depends on the device**: each device kernel is the
exact-integer twin of its CPU kernel, the k-blocking and split-K rules are unchanged, and the
decision is *recorded in the node* (`Node::device`) with the transfers as ordinary program nodes,
so a compiled program runs the same way under any `ENGINE_THREADS`, batching or graph setting.

* **Pass 6 (`pass_device`)** implements `ENGINE_DEVICE=cpu|gpu|hybrid`. `cpu` is the golden path
  and the default. `gpu` sends every device-eligible node to the GPU (all ops but `PANEL_RREF`,
  `PIVOT_SEARCH`, `COMPARE`). `hybrid` evaluates the D4 inequality per **group** = the would-be
  batch, with `R_cpu`/`R_gpu`/bandwidths/latencies from `EngineCostModel.h` (every constant
  carries the section it was measured in), a residency simulation that charges only non-resident
  operands, and the rule that any `uint64_t` context always goes to the GPU.
  `ENGINE_TRACE_PASSES=1` prints both estimates and the verdict per group.
* **Pass 7 (`pass_residency`)** simulates whole-buffer residency level by level and inserts `H2D`
  / `D2H` nodes, **hoisting** `H2D` to the level after the buffer's last host write so the DMA
  overlaps the CPU levels in between, and downloading device-resident Outputs in an epilogue
  level. Two devices writing one buffer in one level would leave neither copy whole, so such GPU
  writers are moved back to the CPU to a fixed point (`PassStats::forced_cpu`). At run time the
  mirrors' version pairs are the ground truth and the *plan* is asserted against them: an `H2D`
  of a device-newer buffer is an `ENGINE_CHECK` failure.
* **Execution.** One device program per compiled program (`Program::uid`): mirrors, `GemmBatch`
  tables, split-K workspaces, device index lists and graphs, in an LRU of
  `ENGINE_CUDA_PROGRAM_CACHE` (64) per executor. Consecutive wavefronts with no CPU node and no
  `D2H` merge into one **run**, captured as one graph and synchronised once
  (`ENGINE_CUDA_MERGE_LEVELS=0` disables); `ENGINE_CUDA_GRAPH=1` (default) launches directly on a
  program's first run and captures on its second, so a **one-shot program never pays a capture**.
* **`ENGINE_VERIFY_DEVICE`** (compile-time default or `Executor::set_verify_device(true)`)
  re-executes every GPU node on the CPU and compares every written window entrywise, throwing
  with node, op, level, buffer and window on the first difference. The contract is byte identity,
  never a tolerance.

### 14.4 The unblocked-kernel trap, measured

`EngineDeviceTrapValidation` (`slow` tier, 14 checks, 8.9 s at integration; gated on identity
only — the timings are reported, never asserted). Wall time *including every transfer*, 32-thread
pool, best of 3; `ENGINE_DEVICE` as the column:

| case | cpu | gpu | hybrid | GPU nodes gpu/hybrid, MB moved gpu/hybrid |
|---|---|---|---|---|
| A. `tape::rref` 1677×1419 rank 258 (13×11, `d = 129`) | **33.2 ms** | 47.3 ms | 33.4 ms | 2837 / 0, 76 / 0 |
| B. `tape::rref` dense 4096² full rank (16×16, `d = 256`) | **705 ms** | 980 ms | 720 ms | 31702 / 15, 2471 / 252 |
| C. Θ-like 2000 × 129³, first run (direct launches) | 32.4 ms | 44.2 ms | 32.9 ms | 628 / 628, 34 / 34 |
| C. Θ-like 2000 × 129³, replay (graph) | 16.6 ms | **13.0 ms** | 16.5 ms | |
| D. dense GEMM 4096³, first run | 181 ms | 31.4 ms | 30.6 ms | 1 / 1, 201 / 201 |
| D. dense GEMM 4096³, replay | 179 ms | **30.6 ms** | 29.9 ms | |
| E1. batched `d = 100` × 256, 256 in / 256 out blocks, replay (cpu = 1 thread) | 14.4 ms | **1.63 ms** | 14.5 ms | 3 / 0, 21 / 0 |
| E2. batched `d = 100` × 256, 32 in / 32 out blocks, replay (cpu = 1 thread) | 9.9 ms | **0.57 ms** | 9.8 ms | 10 / 0, 2.9 / 0 |

**Reading.** The trap is real and the table is what proves the default. The elimination driver
records one program per panel, so nothing amortises: the `gpu` arm re-uploads the panel operands
every time (2.5 GB for B) and is **1.4× slower than the CPU**. The cost model keeps A and B on the
CPU (B: 15 small Schur updates go over, +2 %). The Θ-like program pays for its 34 MB of transfers
on the first run and wins on replay; the 4096³ GEMM wins 6× on the first run already. `hybrid` is
never worse than the better of the two by more than the model's slack (C replay: 16.5 against
13.0 — the model's `cpu_modmac_16t_small` is a 16-thread figure and the 32-thread pool is faster
than it).

Through the *consumers* the same shape holds and the CPU wins at every size measured:
`cohom 256` cpu 0.718 / hybrid 0.622 / gpu 0.732 s; `hecke 256` cpu 1.314 / hybrid 1.153 /
gpu 1.451 s; `cohom 1000 --lean` cpu 24.6 s (1157 MB) / hybrid 25.8 s (1451 MB) / **gpu 80.1 s**
(1449 MB; the CUDA context and pinned pool add ≈ 290 MB). Phase 6's campaign then measured
`hybrid` **1.6–1.9× slower** on a broad sweep at every size up to `n_sym = 200` (6 454 against
10 209 jobs/min): at these matrix sizes a PCIe round trip does not pay, and concurrent jobs
contend for one device (§15.1).

### 14.5 Decisions recorded

1. **`ENGINE_DEVICE=cpu` is and stays the default, and the golden path.** The GPU is never
   enabled by default; the plan's own condition ("not until the unblocked-kernel trap is shown
   avoided") is not satisfied on this workload, and the trap table is the evidence rather than an
   argument.
2. **`hybrid` was built and measured rather than assumed.** It is the cost model's arm, it is
   never materially worse than the better of `cpu`/`gpu` on the trap table, it wins ≈ 13 % on the
   block GEMMs at `n_sym = 256` — and it loses at every size on the campaign's workload. It is
   recommended for a *single large* problem once the consumers replay cached programs, and it must
   not be flipped on before the consumer-level number exists.
3. **No third-party GPU code** (Q2 answered in the negative in practice): the GEMM is hand-written
   and reached 82 % of the roofline, so the CUTLASS escape hatch was never needed. Q3
   (compile-time hot primes, NVRTC) was not exercised — the modulus stays a runtime value.
4. **Bit-identity is by construction, and asserted three ways**: `CudaBitIdentityValidation`
   (`memcmp` against the CPU twin), `ENGINE_VERIFY_DEVICE` (every GPU node re-executed and
   compared entrywise inside a real run), and `EngineCrossDeviceValidation` plus the golden grid
   under all three policies.
5. The device backend is created **lazily** (`Executor::device_usable()` or the first run of a
   program with device nodes): the constructor's probe was creating a CUDA context on every
   CPU-only run and cost 110 MB of RSS (memory profile 05 §0).

### 14.6 Carried forward

1. **Cross-program residency of pool blocks** (§12.7 item 2) — the single missing piece. Today
   `Recorder::pool_input` mints a fresh key per recorder, so an Input is re-uploaded on every run;
   a stable content identity across recorders would let a `BlockPool` block stay resident and would
   turn rows A/B of the trap table around. It needs an owner decision on the identity contract
   before it is built. This is the prerequisite for the `cohom 1000` GPU criterion.
2. **Persistent device mirrors for one-shot panel programs**, and a device-side panel
   factorisation, so `TapeElim`'s per-panel programs stop paying a full upload each.
3. **Batched small-block transfer latency** — the 20× criterion misses at 17.2× with the kernel
   already at 2 T; ~0.4 ms of the 0.57 ms is staged-copy latency and graph launches. Fewer, larger
   staged copies (or device-resident inputs, item 1) is the fix, not a faster kernel.
4. Route 2 on the GPU with the fused route on the CPU (`02 §7.16`) is **moot**: route 2 is now
   streamed per block row as `COMPARE` programs, and the two-executor arrangement needs no backend
   change if it is ever wanted (`PassOptions::policy` is per compile).

---

## 15. Phase 6 — execution record (2026-09-06)

Branch `phase6/batch`, off the `matrix-engine` merge tip `32cc62d`. Default
`RelWithDebInfo` build, GCC 11.4, 32 hardware threads. **Without** the Phase 5
performance closure, which is on a sibling branch.

The campaign driver, the spec parser, the certify logic and the two validations
had already shipped (`docs/matrix-engine/campaign.md`); Phase 6 here is Part A,
the batching seam, and Part B, running the campaign.

### 15.1 Exit criteria

| criterion | result | |
|---|---|---|
| ≥ 1000 `(n_sym ≤ 200, ℓ)` `T_2` results per minute, batched | **1 085 / min** (909 jobs in 50.3 s at `jobs = 32`, `threads = 1`); re-measured on the final merged tree: **1 554.6 / min** (909 jobs in 35.1 s, 4 345 MB) | **met** |
| — with the `rank(Θ_flat)` diagnostic left on | 987 / min | |
| one `n_sym = 1000`, ℓ = 134217757, `T_2` run end to end ≤ 60 s | **48.5 s**, 4 269 MB; on the final merged tree 24.2 s through the driver and **14.4 s / 1 394 MB** as `--bench hecke 1000 134217757 2 --lean` | **met** |
| a published table of new `A^{(1)}(T_p)` char-polys | `docs/matrix-engine/results/` — 2 745 points, README + `results_table.tsv` | **met** |
| `CampaignSmokeValidation` (batched == sequential == golden) | 1 024 checks, 0 failing | **met** |
| `CampaignCertificateValidation` | 38 checks, 0 failing | **met** |

The throughput criterion was written as a *GPU* estimate (§6); it is met on the
CPU. `ENGINE_DEVICE=hybrid` is **1.6–1.9× slower** on this workload (6 454
against 10 209 jobs/min on the `n_sym ≤ 64` probe; 519 against 989 on the
`n_sym ≤ 200` sweep) — at these matrix sizes a PCIe round trip does not pay and
32 concurrent jobs contend for one device. The device arm is for a single large
`n_sym`, not for a broad sweep.

### 15.2 Part A — the batching seam

`RunJobGroup()`'s body was a loop. It now runs `spec.jobs` jobs concurrently,
each on its own engine `ThreadPool(spec.threads)`. Three things make that safe:

1. **Thread context.** The consumers' scoped options are `thread_local` (Stage B
   decision 13.5.3), so a job thread would otherwise see the defaults. The
   driver installs the launching thread's context on every job thread through
   `engine::tape::capture_thread_context()` — the engine's own propagator
   registry, not a private copy.
2. **The τ/coset lock.** `HeckeTauTable`'s build is first-match-wins over a fixed
   order and drives the non-atomic global `PredicateStats` (`02 §6.5`, hazards
   1–3). Every `HeckeCosetTables` / `HeckeTauTable` / `SL2ZTessellationTables`
   construction in the driver runs under `hecke::tau_construction_mutex()` — the
   same lock `HeckeOperatorFamily::build_pipelines()` has always held, moved out
   of that file's anonymous namespace into its header so the process has one
   lock and not two. It costs nothing: τ is 6 ms of a 1.7 s job at `n_sym = 200`.
3. **Determinism.** Results land in a pre-sized slot vector and are appended in
   plan order, so job order, `index.json`, `summary.tsv` and every hash are
   independent of the schedule.

And one makes it fast: **`engine::tape`'s consumer-pool override became
`thread_local`.** `ThreadPool::parallel_for()` serialises concurrent callers on
one region mutex, so *N* job threads sharing one pool serialise all of their
engine work — measured, 32 concurrent jobs on the shared pool bought only 1.7×.
This is §13.6's carried-forward item *"a pool that can run regions of different
executors concurrently"*, in its cheapest form: separate pools rather than a
concurrent one. A `register_thread_context()` capture next to the existing
`elim::ScopedLegacy` one keeps a job's inner degree fan-out on that job's pool.
The driver **probes** for the thread-local behaviour rather than assuming it and
falls back to sharing the process pool, reporting `per_job_pools` in
`index.json`.

**jobs × threads** — 297 jobs, `n_sym = 0..64 step 2` × 9 ℓ, `T_2`, lean,
`certify = none`:

| split | wall | jobs/min | | split | wall | jobs/min |
|---|---|---|---|---|---|---|
| 1 × 1 | 12.62 s | 1 412 | | 16 × 4 | 2.12 s | 8 389 |
| 1 × 32 | 13.54 s | 1 316 | | 32 × 1 | 1.80 s | 9 892 |
| 32 × *shared pool* | 7.40 s | 2 409 | | 32 × 2 | 1.81 s | 9 830 |
| 2 × 16 | 7.31 s | 2 437 | | **16 × 2** | **1.75 s** | **10 209** |
| 4 × 8 | 4.21 s | 4 230 | | 64 × 1 | 2.04 s | 8 732 |
| 8 × 2 | 2.56 s | 6 960 | | `hybrid`, 16 × 2 | 2.76 s | 6 454 |

Two readings. *Shared pool 2 409 against private pools 9 892 at the same 32
jobs*: the ceiling was `region_mutex_`, not the arithmetic. *1 × 32 slower than
1 × 1*: at `n_sym ≤ 64` intra-job parallelism is worth nothing, and the
parallelism that pays is across jobs. The chosen default is `16 × 2` for a broad
sweep (`32 × 1` for the largest, where per-job memory dominates); the *parsed*
default stays `jobs = 1` so a spec that says nothing is the sequential driver.

**A second change was needed.** Running a group at a time imposes a join barrier
at every group boundary, and a shape group is only as wide as its number of
moduli — 9 in the shipped sweeps. Under `certify = sampled` the selected job
runs the external cross-checks and costs ~5× its neighbours (measured 5.05 s
against 0.81 s), so it sat on every group's critical path: mean concurrency
**2.4 out of 9**, and 116 jobs/min on the `n_sym = 42..200` sweep.
`RunCampaignSpec()` now submits `flatten(groups)` — the whole plan, in plan
order — as one work queue. Nothing is lost: a group's jobs share only their
shape, and the `ProgramCache` that could exploit it is process-global and keyed
by the prime anyway (`ENGINE_API` §10.9). **116 → 494 jobs/min** on that sweep,
and 146 → 980 on the exit-criterion sweep. The price is peak RSS: jobs of
different `n_sym` are now in flight together.

`CampaignSmokeValidation` gained the seam's contract — the same spec at four
`jobs × threads` splits must produce the same jobs in the same *order* with the
same objects, `dim_H`, char-polys and C3–C6 certificates as the sequential arm,
and a `summary.tsv` byte-identical outside its two timing columns. 2 192 objects
compared concurrently, on top of the 548 pinned against 20 individual campaigns
and `GoldenReference.inc`; 1 024 checks, 0 failing.

### 15.3 Part B — the campaign

**2 745 points**, `docs/matrix-engine/results/` (README, `results_table.tsv`,
`analysis.txt`, the specs, and each campaign's `index.json` / `summary.tsv`;
the two broad sweeps' 33 MB of per-job JSON is git-ignored and regenerates from
the specs).

| campaign | grid | jobs | certify | wall |
|---|---|---:|---|---:|
| `sweep_full` | `n_sym = 0..40 step 2` × 9 ℓ × `p ∈ {2,3,5}` | 567 | full | 4.7 s |
| `sweep_sampled` | `n_sym = 42..200 step 2` × 9 ℓ × `p ∈ {2,3,5}` | 2 160 | `sampled(every 10)` | 262.3 s |
| `large_n` | `n_sym ∈ {400, 600}` × `p ∈ {2,3,5}` | 6 | full | 999.4 s |
| `large_n_sampled` | `n_sym ∈ {800, 1000}` × `p ∈ {2,3,5}` | 6 | none | 229.0 s |
| `u64_first` | `n_sym ∈ {16,32,64}` × ℓ ∈ {2⁶¹−1, 2⁶³−25} | 6 | full (n/a at 64 bit) | 2.0 s |

Sweep 1 is 2 727 jobs in **4.5 minutes** (612 jobs/min including `p = 3, 5`,
whose coset counts make them 1.2× and 1.7× the cost of `T_2`). ℓ ranges over
`{2,3,5,7,11,13,691,10007,134217757}`, `r = 1`, all three degrees reported.

**The certify split.** Measured cost of the external cross-checks relative to
the job: 1.53× at `n_sym = 16`, 1.65× at 32, 1.57× at 40, **2.29× at 48**, 2.8×
at 64, 5.1× at 128 — so the plan's "full where it costs < 2×" cut lands at
`n_sym = 40`, which is where `sweep_full` hands over to `sweep_sampled`. The
in-process certificates C3–C6 ran on **all 2 745 jobs** in every mode.

**Results.** Every row at `n_sym ≥ 160` is beyond §6's pre-engine practical
limit of `n_sym ≈ 128`; `n_sym ∈ {400, 600, 800, 1000}` is beyond it by an
order of magnitude. `n_sym = 1000` gives `dim H¹ = 167` and a degree-167 char
poly for each of `T_2`, `T_3`, `T_5`.

**Checks, all in `results/analysis.txt`:**

* **Golden** — 3 678 canonical objects also lie on the `GoldenReference.inc`
  grid: **0 mismatching**.
* **The modular-forms oracle** — 37 comparisons of the char poly against
  `(X − σ_{n+1}(p))·∏_f (X − a_p(f))²` at weights 12–24 and ℓ ∈ {10007,
  134217757}, including the weight-24 Galois-conjugate pair: **0 mismatching**.
* **σ_{n+1}(p) = 1 + p^{n+1} is a root of `charpoly A^{(1)}(T_p)` in all 2 718
  rows with `dim H¹ > 0`** — every prime, `n_sym = 1000` and the 64-bit rows
  included. **0 failures.**
* **`dim H¹ = 1 + 2·dim S_{n+2}`** at ℓ = 134217757 for 312 of 315 rows; the
  three exceptions are `n_sym = 0` (weight 2, the known exception).
* **The level-(c) primary decomposition reproduces the Galois-orbit structure of
  `S_{n+2}(SL(2,Z))`** — one `1:1` Eisenstein block plus one block of dimension
  `2f` per orbit of residue degree `f`, with `Σf = dim S_{n+2}`: **312/312** at
  ℓ = 134217757, **300/300** at ℓ = 10007, 293/300 at ℓ = 691. At `n_sym = 1000`
  that is `1 + 1 + 3 + 3 + 4 + 71 = 83 = dim S_1002`.

**Anomalies: zero flagged.** No failed job, no missing Eisenstein root, no
C3–C6 failure, no uncertified residue degree, no external cross-check with a
non-zero rc, no golden mismatch. Two things are *reported* rather than flagged:

* 2 600 of 2 718 char polys are **not squarefree** — the rule, not a defect:
  Eichler–Shimura puts the cuspidal part in holomorphic/antiholomorphic pairs
  with the same eigenvalue.
* The **seven ℓ = 691 rows** that miss the orbit count are the **Ramanujan
  congruence**. At `n_sym = 10` (weight 12) the decomposition returns a *single
  indecomposable 3-dimensional block* and the char poly is `(X − a_p(Δ))³` —
  `τ(p) ≡ σ_11(p) (mod 691)` made visible as the Eisenstein line and the
  cuspidal pair fusing. The other four (`n_sym = 160, 198`) are higher-weight
  congruences of the same kind.
* 1 006 structure notes, **every one at ℓ ∈ {2,3,5,7,11,13}** and none at 691 or
  above: the primes where mod-ℓ Eichler–Shimura is not expected to be clean
  (2 and 3 divide the elliptic stabiliser orders, `ℓ ≤ n + 2` leaves the
  comparison range, and at ℓ = 2 the missing central −I relation is invisible).
  These rows are mod-ℓ data at small ℓ, not a mod-ℓ realisation of
  characteristic-zero modular forms.

**The first 64-bit results.** Six points at ℓ ∈ {2⁶¹−1, 2⁶³−25}, `n_sym ∈
{16, 32, 64}`; all six reproduce the classical prediction exactly (at
`n_sym = 16`, `(X − (1 + 2^17))(X + 528)²` with `a_2(E₆Δ) = −528`). 1.5–2.0 s at
`n_sym = 64`, against 0.02 s at ℓ = 134217757 — the `unsigned __int128`
accumulation has no AVX-512 microkernel.

### 15.4 Cost at scale, and what it says

`certify = full` — not the operator — is what makes a large run expensive, and
it is what makes it grow in `p`: `n_sym = 600, p = 5` with full cross-checks is
388 s and **16.6 GB**, while the *larger* `n_sym = 800, p = 5` without them is
25.5 s and 2.9 GB. The operator is nearly flat in `p` (48.5 / 54.0 / 48.8 s at
`n_sym = 1000` for `p = 2 / 3 / 5`). Sampling the external checks at scale is
therefore not a convenience but the difference between a run that completes and
one that does not.

### 15.5 Gates

`--all`: **`All validations PASSED (63/63 passed, 3 slow-tier skipped)`, 2m36s**.
`GOLDEN_STRICT=1 GoldenRegressionValidation` (tier A 9 446 / 0, tier B
4 603 / 0), `HeckeEndToEndValidation`, `HeckeBadPrimeValidation`,
`HeckeBenchmarkSmoke`, `CampaignSmokeValidation`, `CampaignCertificateValidation`,
`EngineDeterminismValidation`, `EngineTapeConsumerValidation` — all green.

### 15.6 Carried forward

* **Measured on a trial merge with the `matrix-engine` tip `561491b`** (the
  Phase 4 performance closure, which among other things removes
  `ThreadPool`'s region mutex so one pool can run regions of different
  executors concurrently — §13.6's carried-forward item, in its full form):
  **1 508 jobs/minute** on the exit-criterion sweep (909 jobs in 36.2 s at
  `32 × 1`, against 1 085 here) and **`n_sym = 1000, T_2` in 24.2 s / 3 262 MB**
  (against 48.5 s / 4 269 MB). Both exit criteria are then met with a wide
  margin. `CampaignSmokeValidation` (1 024 checks) and
  `CampaignCertificateValidation` pass on the merged tree; the merge is clean in
  code and conflicts only where both branches appended to this file and to
  `perf-ledger.md`. The campaign specs need no change.
* With that pool, the driver's per-job pools stop being load-bearing and become
  isolation: `jobs × threads` remains expressible, but the shared-pool fallback
  is no longer a cliff. Whether per-job pools still pay on the merged tree is
  worth one re-measurement before the knob's default is fixed for good.
* `ENGINE_DEVICE=hybrid` loses on this workload at every size measured, up to
  `n_sym = 200`. Whether it wins on a *single* `n_sym = 1000` job is untested
  here and belongs with Phase 5.
* Per-job peak RSS is only exact at `jobs = 1`; with concurrent jobs the driver
  reports the process high-water mark and says so (`peak_rss_scope`). A genuine
  per-job figure under concurrency needs an allocator-level per-thread
  high-water counter that also sees the pool workers' allocations.
* `HeckeCrossChecks`'s memory at large `n_sym` (16.6 GB at `n_sym = 600, p = 5`)
  is the one place where the pre-block-model shapes survive; it was deliberately
  left verbatim as the reference (`ENGINE_API` §10.9) and is now the campaign's
  binding constraint on `certify = full`.

---

## 16. Programme summary

Written at the close of the programme (2026-09-06, branch `matrix-engine`), from measurements on
the **final tree**, not from the phase records. Reference machine throughout: Ryzen 9 7950X
(16C / 32T), RTX 5070 Ti (cc 12.0), GCC 11.4.0, nvcc 13.0.48, WSL2; default
`CMAKE_BUILD_TYPE=RelWithDebInfo`.

### 16.1 Phase status

| phase | exit criteria | final status |
|---|---|---|
| **0** — build hygiene, correctness fixes, golden harness | 6 | **6 / 6 PASS**. `--all` 2m19s against a ≤ 4 min bound; golden green on Release-class **and** Debug and under both `HECKE_PURE_INTEGER` settings; `hecke 48` 4.88 s. Q1 / Q11 / Q13 decided here (canonical objects only; `α·e_j`; tiers). |
| **1** — the three algorithmic defects | 7 | **7 / 7 PASS**. `hecke 96` 59.7 → **6.64 s** (≤ 8); `cohom 128` 59.4 → **9.80 s** (≤ 12); one `ρ_n` at `n = 160` 5.9 s → **0.215 ms** (≤ 5 ms); `HeckeBenchmarkSmoke` 575 → **7.80 s** (≤ 30); exponent **3.17** (≤ 3.6). |
| **2** — arithmetic primitive layer | 6 | **5 / 6**. GEMM 128 **27.3 G** (≥ 15, stretch 25); RREF 1677×1419 **0.064 s** (≤ 0.6, 9.4× under); strict golden on five configurations; shadow-legacy build green. **E3 `cohom 128` ≤ 4 s FAILED at 6.51 s** — diagnosed in §11.5: the arithmetic was never the binding constraint, the block orchestration was. Closed by Phase 3 (0.462 s), and 0.089 s on the final tree. |
| **3** — block model, consumer migration, `Matrix` retirement | 10 | **9 / 10**. `hecke 128` RSS **100 MB** (≤ 120); allocations **0.075 %** of baseline (≤ 5 %); `hecke 128` **0.845 s** (≤ 6); `cohom 128` **0.462 s** (≤ 4); **0** `Matrix` includes outside the allow-list; **0** raw `mod_*` sites outside it; exponents **2.56 / 2.49** (≤ 3.2 — the first phase in which `cohom` met the permanent guard). **E10 projected memory at `n_sym = 1000` ≤ 1.5 GB FAILED at ≈ 4.7–5.3 GB.** Closed by Phase 4's memory-lean mode. |
| **4** — the engine: tape / passes / scheduler / CPU pool | 6 | **2 / 6**. Determinism **PASS** (8 arms × `ENGINE_THREADS` × `ENGINE_BATCH`, 966 records each, one digest `0x8c1fd2b31a07c778` — `0x2fa804dae5e9d98d` after the 2026-09-16 re-baseline of the canonical τ, `rebaseline-2026-09-16-iota-symmetric-tau.md`; `EngineCrossDeviceValidation` 372 / 0). **E10 PASS**: measured `cohom 1000 --lean` **1157 MB**. **The three ratio criteria FAIL on the final tree**: `hecke 256` 2.607 → 0.555 s = **4.7×** (target 8×), `hecke 128` 0.383 → 0.111 s = **3.4×** (target 4×), `family 128` 0.148 s = **1.33×** a `hecke 128` (target ≤ 1.2×). The absolute walls fell 7.0× and 5.1× against the Stage B baselines; the *ratios* moved against the closure because it sped the single-thread path up 1.47× as well. Phase 5's carried-over `cohom 1000` GPU criterion also FAILs here. |
| **5** — CUDA backend | 9 | **7 / 9** (§14.1). GEMM 4096³ through the tape **2.25 T** (≥ 2 T) and **82 %** of the roofline at 2048³; `CudaBitIdentityValidation` **10 844 / 0**; `EngineCrossDeviceValidation` **372 / 0**; `EngineCudaMemoryValidation` **17 / 0**; the golden grid identical under `cpu` / `gpu` / `hybrid`; `ENGINE_VERIFY_DEVICE=ON@ENGINE_DEVICE=gpu` green; GPU never default. **Batched `d = 100` 17.2× of a 20× floor FAIL** and **`cohom 1000` under `gpu` 80.1 s of ≤ 1.5 s FAIL** — both the same defect: nothing amortises across programs. |
| **6** — batching across problems and the campaign | 6 | **6 / 6 PASS**. **1 554.6 jobs/min** on the exit sweep (909 jobs, `n_sym ≤ 200` × 9 ℓ, `T_2`, 32×1, 35.1 s) against a ≥ 1000 floor, and **25 780 jobs/min** on the `n_sym ≤ 64` probe; `n_sym = 1000`, `T_2` end to end in **14.4 s** (`--bench hecke 1000 … --lean`) / 24.2 s through the campaign driver, against ≤ 60 s; **2 745 published points**; `CampaignSmokeValidation` 1 024 / 0 and `CampaignCertificateValidation` 38 / 0. |

**49 distinct exit criteria** (the 50 listed above less one: Phase 4's sixth row and Phase 5's last
are the same `cohom 1000` GPU criterion, carried over), **of which 42 are met**. The seven misses
are five distinct problems: Phase 2's E3 (closed by Phase 3 — 6.51 → 0.462 s, and 0.089 s here),
Phase 3's E10 (closed by Phase 4's memory-lean mode — 4.7 GB projected → 1157 MB measured), the
three Phase 4 thread-ratio criteria, and the two Phase 5 GPU criteria. **Every one of the five open
misses is a *speed* criterion; no correctness, determinism or bit-identity criterion was missed at
any phase** — the golden grid, the dual-route assertions, the shadow-legacy build, the
cross-device gate and the two static migration guards are green in every configuration tested.

### 16.2 Before and after

Baselines: the `-O0` tree at `hecke-action` @ `c8227c8` (`03-profiling-baseline.md` §10–11) where
marked, otherwise the Phase-2 tree (`3c1ac45`) — the point at which the arithmetic was fast and the
orchestration was not. Final column: this tree, `--repeat 5`, quiet box.

| metric | baseline | final | factor |
|---|---:|---:|---:|
| `--bench hecke 128 134217757 2` | 10.51 s (Phase 2) / ≈ 190 s (`-O0`, extrapolated from `hecke 96` = 59.0 s) | **0.125 s** | 84× / ≈ 1500× |
| `--bench cohom 128 134217757` | 6.51 s (Phase 2) / **56.99 s** (`-O0`) | **0.089 s** | 73× / **640×** |
| `hecke 128` peak RSS | 437 MB | **112 MB** | 3.9× |
| `hecke 128` allocations | 26.19 M | **33 355** | **785×** |
| `cohom 128` peak RSS | 434 MB (`-O0`) | **62 MB** | 7.0× |
| `cohom 128` allocations | 24 M (`-O0`) / 26.16 M | **17 153** | **1 400×** |
| `HeckeBenchmarkSmoke` | **575 s** (`-O0`) | **0.09 s** | **6 400×** |
| `./hacs --all` | 16m33s (32 validations, `-O0`) | **2m24s** (63 of 66; `--all-full` 2m46s, 66/66) | — |
| `GOLDEN_STRICT=1 GoldenRegressionValidation` | 69.7 s (Phase 0) | **5.2 s** | 13× |
| GEMM 128³ / 512³, one thread | **0.170 / 0.170 Gmodmul/s** (`-O0`) — 0.216 / 0.215 on the legacy arm of this binary | **27.8 / 30.3 Gmodmul/s** | **163 / 178×** |
| GEMM 2048³ through the tape | — | **28.3 G** (1 thread) → **307.8 G** (16) → **371.5 G** (32) → **4 065 G** (GPU) | 10.9× / 13.1× / **144×** CPU-1 |
| RREF 1677×1419 | 2.403 s (legacy arm, same binary) | **0.056 s** | 43× |
| `n_sym = 1000` | **not computable** (≈ 5–7 weeks extrapolated, §6) | `cohom 1000 --lean` **14.8 s / 1157 MB**; `hecke 1000 --lean` **14.4 s / 1394 MB** | — |
| campaign throughput, `n_sym ≤ 200` × 9 ℓ, `T_2` | one job at a time | **1 555 jobs/min** (909 jobs in 35.1 s) | — |
| `ENGINE_BACKEND=legacy` on the same binary | `cohom 128` **6.43 s / 302 MB / 4.90 M allocs**; `hecke 128` **11.64 s / 302 MB / 4.93 M** | 0.089 s / 62 MB / 17 K; 0.125 s / 112 MB / 33 K | 72× / 93× |

The fitted exponent of the total time in `n_sym` over `{64, 96, 128}` is now **1.72** for `hecke`
and **1.63** for `cohom` (Phase 3: 2.56 / 2.49; Phase 2: 3.15 / 3.24; Phase 1: 3.17 / 3.34) — far
under the ≤ 3.2 permanent guard of §4.4. Over the larger `{96 … 256}` band, where the fixed
per-run overhead no longer dominates, both are **2.05**.

### 16.3 Acceptance on the final tree

* `./hacs --all` → `All validations PASSED (63/63 passed, 3 slow-tier skipped)`, **143.8 s**;
  `--all-full` → `All validations PASSED (66/66 passed)`, **166.2 s**. Exit 0 both.
* `GOLDEN_STRICT=1 GoldenRegressionValidation`, **tier A 9446 failing 0 / tier B 4603 mismatching 0**
  in every arm: `ENGINE_THREADS=1` (3.1 s), default (5.5 s), `ENGINE_DEVICE=gpu` (17.2 s),
  `ENGINE_DEVICE=hybrid` (11.0 s), `ENGINE_BACKEND=legacy` (9.3 s).
* `docs/matrix-engine/tools/cross_config.sh` over six configurations — `RelWithDebInfo`, `Bench`,
  `Debug`, `+HECKE_PURE_INTEGER=ON`, `+ENGINE_SHADOW_LEGACY=ON`,
  `+ENGINE_VERIFY_DEVICE=ON@ENGINE_DEVICE=gpu` — all six build, all six golden-clean (A 0 / B 0),
  and the `gemm 512` and `rref 1677 1419 258` checksums (`0xdf6200e19d2b9a44`,
  `0xc4799960ca8cfaa2`) agree across every one: **`cross_config.sh: PASS`**. On the
  verify-device GPU build `HeckeEndToEndValidation` is additionally green (12.2 s) with every GPU
  node re-executed on the CPU and compared entrywise.
* `HeckeBenchmarkSmoke`: `COMPLETED and CERTIFIED (aggregate failing case(s) = 0)`, 0.09 s.

### 16.4 Open items, ranked

1. **The Phase 4 thread-ratio criteria** (`hecke 256` 4.7× of 8×, `hecke 128` 3.4× of 4×,
   `family/hecke` 1.33× of ≤ 1.2×). The remaining serial time is structural, not schedulable
   (§13.7): 19 % in host-serial `PANEL_RREF` / `PIVOT_SEARCH` — each 256-wide panel is ~250
   dependent column steps — and 33 % in host recording, `BlockBuilder` assembly and the `q = 1`
   `factor_basis` stage-2 host steps. Reaching 8× needs the *elimination structure* changed: a
   `PANEL_RREF` that is itself a wavefront program with a recursive parallel panel factorisation,
   fewer and wider panels, and `factor_basis` stage 2 recorded as tape programs. Highest value:
   it is the only item that improves the shipped default path.
2. **The Phase 5 consumer-level GPU criterion** (`cohom 1000` ≤ 1.5 s; 80.1 s today, against
   14.8 s on the CPU). Blocked on **cross-program residency of pool blocks** (§12.7 item 2): today
   `Recorder::pool_input` mints a fresh key per recorder, so every Input is re-uploaded on every
   run and the one-shot per-panel programs pay a full upload each. This needs **an owner decision
   on the content-identity contract** before it can be built, and it subsumes item 3.
3. **Batched small-block transfer latency** — 17.2× against a 20× floor with the kernel already at
   2 TmodMAC/s; ≈ 0.4 ms of the 0.57 ms is ~30 µs per staged copy × 10 buffers plus 3 graph
   launches. Fewer, larger staged copies, or device-resident inputs (item 2).
4. **Certified-mode memory.** `--lean` fits `n_sym = 1000` in 1157 MB, but the *certified* profile
   projects **4.9 GB** at `n = 1000` and measured **16.6 GB** at `n_sym = 600, p = 5` with
   `certify = full`. `HeckeCrossChecks` is the one consumer deliberately left on the
   pre-block-model shapes as the independent reference (`ENGINE_API` §10.9), and it is now the
   binding constraint on `certify = full` past `n_sym ≈ 400`. Migrating it costs the independence
   of the cross-check, so this is a **policy** decision, not a residency problem (05 §5.2).
5. **`HeckeTauTable`'s mod-ℓ RREF-with-RHS solver, deliberately not absorbed** into
   `engine::elim::solve_multi_rhs` (the verdict and its reasoning are in
   `tools/raw_mod_calls.allow`): it carries a Z-first / mod-ℓ fallback policy the engine API has no
   way to express. The API gap that verdict exposes is unclosed.
6. **`BlockFlatMatrix` removal.** Deprecated since Phase 3 and reachable only from the
   `ENGINE_BACKEND=legacy` arms and their validations, guarded by `check_matrix_includes.sh`'s
   second allow-list. Removing it means retiring the legacy arms, which are still the cheapest
   independent oracle the tree has.
7. **Owner questions still open** (§7): Q4 (priority between larger `n_sym` at `ℓ ≈ 2^27` and the
   `ℓ < 2^64` regime — the campaign produced first results in both, so this is now a scheduling
   question), Q6 (may the plan-mandated `std::vector<Matrix>` signatures be amended, which is what
   stands between `Matrix` being *quarantined* and being *deleted*), Q8 (the 7/11/5 model
   refinement — now cheap: `HeckeModelDescriptor` is the single place the model is written down),
   Q10 (regime F only: migrate `HeckeModuleDecomposition` / `FpPoly` off `Matrix`; negligible
   through regime E, 15–70 % of the run at `n_sym = 5000`), Q12 (FLINT as a dev-only external
   oracle). Q2 and Q3 are moot in practice — the hand-written GEMM reached 82 % of the roofline,
   so neither CUTLASS nor prime specialisation was needed. Q1, Q5, Q11 and Q13 are decided and
   implemented.

### 16.5 The campaign

The programme's scientific output is `docs/matrix-engine/results/` — **2 745 computed points** of
the Hecke action on `H^q(SL(2,Z), Sym^n(F_ℓ^2))`, every one through the public API and every one
carrying the never-sampled in-process certificates C3–C6: a broad sweep `n_sym = 0..200` × 9 moduli
× `p ∈ {2,3,5}`, deep points at `n_sym ∈ {400, 600, 800, 1000}`, and the first `ℓ < 2^64` results.
Everything at `n_sym ≥ 160` is past §6's pre-engine practical limit of ≈ 128, and
`n_sym ∈ {400 … 1000}` is past it by an order of magnitude; at `n_sym = 1000`, `dim H¹ = 167` with
a degree-167 characteristic polynomial for each of `T_2, T_3, T_5`. The mathematics checks out on
every axis tested: 3 678 objects that also lie on the golden grid match it exactly, 37 comparisons
against the classical modular-forms oracle at weights 12–24 agree, `σ_{n+1}(p) = 1 + p^{n+1}` is a
root of `charpoly A^{(1)}(T_p)` in **all 2 718 rows with `dim H¹ > 0`**, and the level-(c) primary
decomposition reproduces the Galois-orbit structure of `S_{n+2}(SL(2,Z))` in 312/312 rows at
`ℓ = 134217757`. **Zero anomalies were flagged.** Two things are *reported* rather than flagged,
and the second is the campaign's nicest result: 2 600 char polys are not squarefree (Eichler–Shimura
pairs the cuspidal part, so this is the rule), and the seven rows at **ℓ = 691** that miss the orbit
count are the **Ramanujan congruence** — at `n_sym = 10` (weight 12) the decomposition returns a
single indecomposable 3-dimensional block with char poly `(X − a_p(Δ))³`, which is
`τ(p) ≡ σ_11(p) (mod 691)` made visible as the Eisenstein line and the cuspidal pair fusing. The
published table is `results/results_table.tsv` (all 2 745 rows), the checks are `results/analysis.txt`,
and `results/specs/*.spec` re-runs any of it.
