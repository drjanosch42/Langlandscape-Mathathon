# Known Issues

**§7** (a rare red of `OrbifoldCampaignL23Validation` (D), 2026-10-17) is **root-caused, fixed on the test side and
CLOSED at the root** (slot 24 L23-H1, `orbifold_cell/v2`: the oracle's wall time left the hashed record body, finding H-1). Otherwise no open defect or limitation. §3 (the `U_ell` exact-integer reach, recorded 2026-09-16 by
hecke-extensions slot 1) was **resolved 2026-09-17** by slot-3 package WP-1, which also corrected
its diagnosis — the overflowing site was `alg:tau` step 1's fundamental-domain reduction, not the
coset construction this file originally named. **The current `U_ell` reach is `ell ≤ 23170`**
(largest prime 23167), set by the `τ`-table's own certification — `certify()` clause (e),
`B = max(B_tab, 4N²) ≤ 2³¹ − 1` — past which the table is refused by name (code 51), never
silently wrong; it is a recorded limit, not a defect (§3). The two defects of §1–§2 are resolved as of
2026-07-03. Both defects below
were pre-existing and unrelated to the Hecke feature — they were surfaced (not
introduced) by the Hecke work when the S0 validation harness first made every
validation runnable by name, and both reproduced on the pre-Hecke base commit
`0a931e1`. Issue 2 (`SimplicialCohomologyValidation`) was fixed earlier this
session; issue 1 (`BlockFlatMatrixValidation`) was fixed by the performance work
recorded below. Both entries are retained for the historical root-cause record.

Consequence: **`./cohomology_app --all` now exits 0** (verified 2026-07-03: a
full foreground run reported `All validations PASSED (32/32 passed)`, exit code
0, in ~16m33s, including the certified `HeckeBenchmarkSmoke`). The full Hecke
acceptance gate (`HeckeEndToEndValidation`, `HeckeBadPrimeValidation`,
`HeckeBenchmarkSmoke`) also passes when run individually.

---

## 1. `BlockFlatMatrixValidation` stalls (performance) — RESOLVED

- **Status:** RESOLVED (2026-07-03). `./cohomology_app BlockFlatMatrixValidation`
  now completes and exits 0 (85/85 sub-tests pass, ~2m49s; the hang is gone).
- **Symptom (historical):** `./cohomology_app BlockFlatMatrixValidation` made
  monotonic forward progress (~30 sub-tests passed, incl. 800×800 / 400×800 dense
  cases) and then hung; did not complete in practical time (>10 min), independent
  of optimization level. The stall was in the "Large Sparse Block
  (1000×1000, blocks 10×10)" test section — an already-documented bottleneck (see
  `docs/optimization-audit/03-blockflatmatrix-deep-audit.md`, item 2.1). Nature:
  performance, not correctness (the section was genuinely slow, not wrong).
- **Root cause:** `get_true_row_echelon_form_as_flat_matrix()` assembled the true
  RREF cell-by-cell, issuing up to ~10^6 `set_entry` calls, each of which
  triggered an O(rows·cols) `_determine_and_set_flags_from_data()` full rescan of
  the whole matrix ⇒ overall O(N^2). The cost was further amplified because the
  validation's verify-helpers recompute the true RREF several times.
  Secondarily, `_block_gaussian_elimination` performed 9 gratuitous full-block
  copies per relevant step.
- **Fix:** rewrite `get_true_row_echelon_form_as_flat_matrix()` to assemble the
  true RREF into a single bulk buffer that is fed once to the `FlatMatrix` DATA
  constructor, so the flag computation runs a single time (O(N^2) → O(N)); add an
  empty-pivot early-return that preserves the legacy `CreateZero` representation,
  plus debug asserts. Additionally, remove the 9 gratuitous block copies in
  `_block_gaussian_elimination` (7 replace-on-true paths call `is_zero()` on the
  stored block directly; 2 continue-on-true paths use a non-mutating
  `is_currently_scalar()` pre-check). The change is bit-identical (proven under
  `HECKE_PURE_INTEGER` parity and the full validation battery).
- **Validation:** `BlockFlatMatrixValidation` (85/85), `FlatMatrixValidation`
  (107/107), `MatrixValidation`, `LocalSystemCohomologyValidation`, and the full
  Hecke acceptance gate (`HeckeEndToEndValidation`, `HeckeBadPrimeValidation`,
  `HeckeBenchmarkSmoke` — all exit 0, benchmark CERTIFIED) all pass. With this
  fix `./cohomology_app --all` exits 0 (32/32).
- **Reproduce (historical, pre-fix):** on commit `0a931e1` or any commit before
  this fix: `cmake . && make && timeout 120 ./cohomology_app BlockFlatMatrixValidation`
  (timed out).

## 2. `SimplicialCohomologyValidation` aborts (correctness) — RESOLVED

- **Status:** RESOLVED. `./cohomology_app SimplicialCohomologyValidation` now
  exits 0.
- **Symptom (historical):** `./cohomology_app SimplicialCohomologyValidation`
  threw `std::runtime_error("Matrix dimensions or prime moduli do not match for
  multiplication.")` → `SIGABRT` (exit 134).
- **Location:** inside `CochainComplexMorphism::compute_cohomology_maps()` in
  `src/hacs/SimplicialCohomology.cpp`, for the
  **"Boundary of Projective Plane" → "Projective Plane"** mapping-cone example.
- **Root cause:** a producer/consumer coordinate-convention mismatch.
  `cohomology_projectors[q]` (despite `cochain_bases[q]` naming, this is a basis
  of the *cocycle* space Z^q = ker d^q) expects its input already expressed in
  Z^q-basis coordinates, shape (dim H^q) x (dim Z^q). But
  `compute_cohomology_maps()` was instead feeding it the raw ambient cochain
  vector `mapped_element` (living in C^{q+degree}) directly, without a
  change-of-basis step — a dimension/prime mismatch that manifested as the
  matrix-multiplication SIGABRT for the projective-plane (non-orientable, ℤ/2
  torsion) mapping cone.
- **Fix:** insert a `change_of_basis` re-expression of `mapped_element` into
  Z^{q+degree} coordinates (w.r.t. `cochain_bases[q+degree]`) before applying
  `cohomology_projectors[q+degree]`, indexed consistently by `q+degree`; add
  three shape asserts (`<cassert>`) at the call site so any recurrence fails
  fast with a clear message instead of deep inside `Matrix::operator*`; remove
  the now-dead `codomain_coboundary_lifted_basis` block; add a regression guard
  at the end of `SimplicialCohomologyValidation` asserting the degree-0
  restriction map H^0(RP^2) -> H^0(boundary RP^2) is the 1x1 identity `[1]`.
- **Relevance note:** this is the `CochainComplexMorphism` class (trivial
  coefficients), a *sibling* of the equivariant `EquivariantCochainComplexMorphismOnK`
  that the Hecke feature uses and generalized (S6). The Hecke pipeline does not
  route through the trivial mapping-cone path and was unaffected either way;
  post-fix, `LocalSystemCohomologyValidation` and the Hecke acceptance gate
  (`HeckeEndToEndValidation`, `HeckeBadPrimeValidation`, `HeckeBenchmarkSmoke`)
  all still exit 0.
- **Reproduce (historical, pre-fix):** on commit `0a931e1` or any commit before
  this fix: `cmake . && make && ./cohomology_app SimplicialCohomologyValidation`
  (aborted).

---

## 3. `U_ell` at large `ell`: the `alg:tau` step-1 reduction exhausted `int64` — **RESOLVED**

- **Status:** **RESOLVED 2026-09-17** by hecke-extensions slot 3 package WP-1 (phase E1b-0;
  `docs/implementation/slot3/WP-1_report.md`). `U_ell = T_p(ell)` at `p = ell` now runs past the
  old limit exactly, and **bit-identically wherever the `int64` tier already completed**. The
  entry is kept because its original diagnosis in this file was **wrong about the site**, and
  because the repair leaves a new, much larger, stated reach limit.
- **Symptom (historical, `b391a3a` and earlier):**
  `./cohomology_app --bench hecke <n> <ell> <ell>` threw `hecke: exact multiply overflow`
  (`Hecke/ExactInt.h`, `__builtin_mul_overflow`) for `ell >= 5003`, **independently of `n`**
  (`n in {2, 4, 8, 16}` all failed identically). The same `ell` with a good prime
  (`--bench hecke 16 43867 2`) ran in 9 ms / 12 MB.
- **Where it actually was.** This entry said "inside `HeckeCosetTables`' coset construction".
  **That was incorrect.** WP-1 instrumented the throw and captured the backtrace: the site is
  `hecke::QuadPoint::moebius` called from `HeckeTauTableT::reduce_to_fundamental_domain`, called
  from `HeckeTauTableT::construct_vertex` — i.e. **[C] `alg:tau` step 1's fundamental-domain
  reduction**, not the coset tables. The coset construction's own products are `~N^2`
  (`gamma * s_j^{-1}` and the `diag(1,N)`-conjugate) and build fine far past the old limit: the
  `Gamma_0(ell)\Gamma` tables are constructed and `self_check()`ed at `ell = 5003` **and
  `ell = 43867`** by `HeckeUEllReachValidation` / `HeckeUEllReachSlow`.
- **What overflowed, exactly.** Step 1 forms `z = (g^{-1} s_i) . pos(v)` through the projective
  `adj(g) = diag(N, 1)` trick. The point's cleared coordinates `(u, v, w)` reach
  `||z|| ~ ||pos||^2 N^2` — **measured `144.8 * N^2`** on the shipped 7-vertex model, where
  `||pos|| <= 12` — and `QuadPoint::moebius` forms `t^2` and `r*t` from them, i.e. products of
  size `~||z||^2 ~ 2.1e4 * N^4`. The `int64` tier therefore dies at `145 N^2 >= 2^31.5`, i.e.
  **`N >= ~4580`**, which is exactly the measured bracket `3617 < N < 5003`. The failing operand
  captured at `ell = 5003` was `3037539817^2 = 9.2267e18` against `2^63 - 1 = 9.2234e18`.
- **It was NOT a failure of [C] `lem:bounds`.** The certified whole-pipeline bound
  `B = max(B_tab, 4 N^2)` of `HeckeTauTable::certified_bound_B()` is `1.0012e8` at `N = 5003`,
  with `2 B^2 = 2.0e16 << 2^63`, and `certify()` clause (e) **passes**. `lem:bounds` bounds the
  *stored transporters*; what overflowed is a step-1 **intermediate** that no clause of it
  covers. This was WP-1's contract finding (`docs/implementation/slot3/WP-1_report.md` §6) and
  **is resolved in the contract**: `gl2_contract.tex` v1.5.0 (slot-3 WP-8) added
  `lem:bounds`(6) — the bound on step 1's reduction point — and `thm:backend`(iv), and corrected
  `thm:backend`(1); the referee pass v1.5.1 (WP-9) repaired that item's arithmetic
  (`4N² ≤ 2³¹ − 1` is `N ≤ 23170`, the `≈ 4580` is the *measured* int64 threshold, not a
  consequence of the tier criterion). The contract's record of the repair is `sec:heckedatum`'s
  code map and `rmk:btabsmall` (v1.5.2 adds the code-map rows).
- **The repair** is [C] `thm:backend`'s own third tier, made reachable: `QuadPoint` is now
  `QuadPointT<I>` with `I in {int64_t, __int128}` (`QuadPoint` / `QuadPointW`), and
  `construct_vertex` runs step 1 through `hecke::escalate_on_overflow` — **the `int64` tier
  first, widened only after a `HeckeOverflow`**. Bit-identity wherever `int64` completes is
  therefore a property of the control flow, not of a test. Nothing *stored* widens: the
  reduction's outputs are `gamma_red` (`||.|| ~ N`) and a vertex index. `hecke::ScopedExactTier`
  forces either tier for the validations (`ForceWide` / `ForceNarrow`).
- **The new reach limit is a DIFFERENT one, and it is `lem:bounds`'s own.** Step 1's `__int128`
  tier would carry `ell` to ~`1.8e8` (`~7 (145 N^2)^2 < 2^127`), but it is no longer what binds.
  The next constraint is `HeckeTauTable::certify()` clause (e) — [C] `lem:bounds`(5) /
  `obl:backend` — which requires the certified bound `B = max(B_tab, 4 N^2)` on the **stored**
  transporters to satisfy `2 B^2 < 2^63`, i.e. `B <= 2^31 - 1`. With `B = 4 N^2` that is exactly

      N <= 23170,   i.e.  ell <= 23170   (largest prime: 23167).

  At `ell = 43867` the table is now built without an overflow and then **refused by its own
  certification, loudly**: `HeckeTauTable: certification FAILED (code 51) ... table rejected,
  computation aborted ([C, obl:tau])`, reproducible in **20 s** with
  `--bench hecke 0 43867 43867`. That is the designed behaviour, not a regression — the failure
  moved from an anonymous `exact multiply overflow` to the named certificate clause that owns
  the bound.
- **Lifting `ell <= 23170` is a STORAGE change and is out of scope here.** `B` bounds the
  `Mat22` transporters the table *stores*, so widening it means making the stored type
  `Mat22W` (`__int128`) and extending the recount to it — the "stored transporter" branch of the
  slot-3 diagnosis checkpoint, which makes the package L. It is not needed: `u_ell = auto`
  refuses every cell with `ell > 23170` on memory grounds long before the bound bites
  (`ell = 43867` is predicted at 5491 MB at `n = 2` and 8255 MB at `n = 16` against a 2048 MB
  budget), and no Kummer cell of
  `docs/latex/hecke_extensions.tex` Claim 1.8 with `ell > 23170` needs `U_ell` (`B' = 2` there).
  A genuine `__int128` overflow would still be a named exception, never a wrong value
  ([C] `obl:backend`); the next tier would be fixed-width 192-bit and arbitrary precision stays
  banned.
- **Measured after the repair** (default `RelWithDebInfo`, `--repeat 1`, this box):
  `--bench hecke 16 5003 5003` **73.1 s / 949.9 MB**; `hecke 2 5003 5003` 70.2 s / 504.1 MB;
  `hecke 2 7001 7001` 161.6 s / 739.5 MB; `hecke 2 10007 10007` 356.4 s / 1019.1 MB. The cost is
  the `m = ell + 1` coset slots of `tau`, not the escalation.
- **`U_43867` end to end is still not run**, and now cannot be (see the limit above); it was
  deliberately out of scope either way, because the frozen RSS model of
  `HeckeExt/HeckeUEllBudget.h` (`u_ell_rss/v2-2026-09-17`, `c0 = 0.123152`,
  `c1 = 2.24985e-4`) predicts **8254.76 MB** at `(n, ell) = (16, 43867)` against the
  `u_ell = auto` default budget of 2048 MB, so the shipped setting **refuses** it with
  `reason = u_ell_over_budget`. That refusal is pinned by `HeckeUEllBudgetValidation`. Its coset
  tables *are* built and self-checked (`HeckeUEllReachSlow`).
- **Gated by:** `HeckeUEllReachValidation` (`standard`, ~11 s, 6160 checks — including the
  negative control: under `ExactTier::ForceNarrow` `ell = 5003` still throws the named
  `HeckeOverflow`, so the reach demonstrably comes from the wide tier),
  `HeckeUEllReachSlow` (`slow`) and `HeckeUEllBudgetValidation` (`fast`).
- **Value-preserving:** `GoldenReference.inc` unchanged (`GOLDEN_STRICT=1` tier A 9446/0,
  tier B 4603/0), `EngineDeterminismValidation` digest `0xe446b3bd2d28bd6e` on all 8 arms,
  `docs/implementation/tau_table_p2.txt` byte-identical.
- **Reproduce the historical failure** on the current tree: run any `ell >= 5003` `p = ell`
  construction under `hecke::ScopedExactTier(hecke::ExactTier::ForceNarrow)` — that is exactly
  what `HeckeUEllReachValidation`'s arm [5] does.
- **Slot-24 ELL-W (2026-10-20): the `ell <= 23170` limit is lifted, without a storage change.**
  The stored transporters satisfy `B_tab ~ 0.88 N` (measured), so they fit `int64` far past 23170;
  what the narrow criterion `2 B^2 < 2^63` protected is the arithmetic on two stored-class operands.
  Those sites (`(T1)`'s translate, step 2's vertex relation, clause (a)'s determinant,
  `twisted_conjugate`, `word_in_T_S`'s determinant) now go through `hecke::mul_tiered` /
  `det_tiered` / `inv_unimodular_tiered` (int64 first, `__int128` after a `HeckeOverflow`, the
  result narrowed with a check), and `certify()` clause (e) certifies a table with
  `B > 2^31 - 1` in the **wide tier** when `2 N B <= 2^63 - 1` ([C] v1.23.0-pre.9 draft,
  `lem:bounds`(7), `thm:backend`(4); code 52 otherwise), i.e. `ell <= 1048573` when `B = 4 N^2`.
  `--bench hecke 0 43867 43867` now completes (27.7 s, 2.10 GB). Rollback `HECKE_TAU_WIDE=0`
  (code 51 as before); gates `HeckeWideTauValidation`, `HeckeWideTauSlowValidation`,
  `HeckeUEllReachSlow` arms (9)/(10). Not lifted: the boundary datum / eta (cone route, still
  code 51 above 23170), the `u_ell = auto` memory model (a mathematical setting, unchanged), and
  the `hida_tower` verb's `ell <= 23170` guard. Report `docs/implementation/slot24/ELLW_report.md`.

---

## 4. Open tool findings (hecke-extensions slot 7, WP-11)

Two findings recorded at the hecke-extensions slot-6 close (`[X] v1.10` "Open items at the
slot-6 close", item 9 and item 4), carried here as this file's first **open findings** (as
opposed to resolved defects) per its stated scope. Both are tool-level, not value-preserving
questions: neither one ever produced a wrong emitted number.

### 4a. `cross_config.sh` ignored a bench's exit code — **RESOLVED (this package)**

- **Status:** RESOLVED (hecke-extensions slot 7, WP-11). `docs/matrix-engine/tools/cross_config.sh`
  captured a `--bench micro` run's `checksum=0x...` field but never its own exit code
  ([WP6-14] slot-6 WP-14 close report §9: "a bench that crashes after printing its checksum
  still reads green"). Fixed by capturing `$?` right after the bench invocation: a non-zero exit
  now prints `!! bench micro '<case>' exited non-zero for '<config>' (rc=<code>)`, the checksum
  column shows `ERR(rc=<code>)` instead of the (possibly stale) printed value, and the run's own
  exit code becomes non-zero — exactly the treatment already given to a failed
  `GoldenRegressionValidation` run or a failed named validation.
- **Proof.** A deliberately failing stub `cohomology_app` (a two-branch program: it answers
  `GoldenRegressionValidation` clean and, on `--bench micro ...`, prints
  `checksum=0xdeadbeef`, flushes, then calls `abort()`) was built out-of-source under a scratch
  copy of the tree (`CMakeLists.txt` + `main.cpp`, `docs/matrix-engine/tools/cross_config.sh`
  copied alongside it — nothing under this repository's tracked tree). Run against it: the
  **pre-fix** script printed the matrix with `chk:gemm 512 = 0xdeadbeef` and exited 0
  (`cross_config.sh: PASS`); the **post-fix** script printed
  `!! bench micro 'gemm 512' exited non-zero for 'RelWithDebInfo' (rc=134)`, the matrix showed
  `ERR(rc=134)`, and it exited 1 (`cross_config.sh: FAIL`). Nothing from the stub was committed.

### 4b. `field_polynomial = conway` silently falls back to `least` outside `MathSettings` — **RESOLVED (slot 7, WP-4)**

- **Resolution (slot-7 close, WP-14).** Slot-7 WP-4 (`cab4e38`, merged `3a40f68`) routed
  `CanonicalField(ell, r)` and `CertifyCanonicalSplit`'s clause 3 through
  `FieldPolynomialFromSettings`. Under `least` this is byte-identical by construction; under
  `conway` the constructor, the `--bench ext` path, the certificate, the atlas and the record
  consumer (WP-3 item 6's `split`) all raise `hecke::NotImplementedInThisBuild` —
  `HeckeCanonicalFieldValidation` arm I. The routing landed **before** item 6 put the canonical
  split into the record, as [S7] §2.3 item 3 required. The text below is the finding as recorded.
- **Status (as recorded by WP-11):** OPEN as of the hecke-extensions slot-7 WP-11 close. Recorded here per
  `[X] v1.10` "Open items at the slot-6 close" item 4 (WP-13 finding 1, slot 6). **The fix is
  routed to slot 7's WP-4** (the `HeckeCanonicalField` root-finder package); WP-11 does not touch
  `HeckeExt/HeckeCanonicalField.*` (the shared-file rule reserves it to WP-4 first, then WP-3
  item 6 and WP-5).
- **Symptom.** `hecke::MathSettings::set` legally accepts `field_polynomial = "conway"`; only
  `hecke_ext::FieldPolynomialFromSettings(ell, r)` — the settings-aware entry point — enforces
  the key's contract, raising `hecke::NotImplementedInThisBuild` for that value (`conway` parses,
  the routine is not shipped). `hecke_ext::CanonicalField(ell, r)` and
  `hecke_ext::SplitInCanonicalField(ell, ...)` and their direct callers (e.g. the atlas path of
  `Bench/BenchDriver.cpp`) call `hecke_ext::CanonicalFieldPolynomial(ell, r)` directly instead of
  routing through the settings-aware entry point, so under `field_polynomial = conway` they
  silently compute with the `least`-degree polynomial rather than raising the named error the
  key's contract requires.
- **Blast radius.** Latent: no `hecke_ext` report layer reads `field_polynomial` yet in slot 6,
  so no emitted record or golden value is currently wrong. The requirement is prospective — "the
  E6 report layer must route through `FieldPolynomialFromSettings`" before it gains a consumer of
  that setting — which is why WP-4's canonical-field work is where it is fixed, not here.

### 4c. The engine's process-wide program cache is unbounded — **RESOLVED (slot 8, WP-5)**

- **Status:** **RESOLVED by hecke-extensions slot-8 WP-5** (the repair and the evidence are at
  the end of this section). It was OPEN at the slot-7 close ([X] v1.11 "Open items at the slot-7
  close" item 1). Found by slot-7 WP-5 (the `ell = 691` atlas build) and confirmed by WP-7 (the
  first ext campaign).
- **Symptom.** A long-running process that computes many cells never releases RSS: the `Σ(691)`
  build's RSS grows ≈ 16 GB across its cells (peak 19.5 GB), and a campaign's ext pass holds
  6.87 GB at its end (505 cells), the peak 10.35–10.58 GB occurring in the job loop, where 32
  concurrent jobs sit on top of the retained memory. Growth slows as the `n` shapes repeat.
- **Cause.** The engine's program cache (`src/Engine/`, `run_cached()` — record-always,
  compile-on-miss) is process-wide and has no eviction. The extension layer cannot clear it:
  `check_heckeext_includes.sh` rule 2 forbids `Engine/` inside `HeckeExt/`.
- **Blast radius.** No value; memory only. Bounded at this scale on the 62 GB reference box.
- **Repair (slot 8).** A between-cells release hook outside `HeckeExt/` — in `kernel.cu`'s
  `--atlas` branch and in the campaign driver's ext pass — reaching the process-wide cache's
  `ProgramCache::clear()` (`src/Engine/ProgramCache.h`).
- **Fix (slot-8 WP-5).** `campaign::ReleaseEngineProgramCaches(threshold)`
  (`Campaign/ProgramCacheRelease.{h,cpp}`) clears **both** `ProgramCache<uint32_t>::global()` and
  `ProgramCache<uint64_t>::global()` when their combined size exceeds `threshold`, and then calls
  glibc's `malloc_trim(0)`. It is called after every cell of `RunExtPass`
  (`Campaign/CampaignExt.cpp`) and of an `--atlas` build at `kCellLoopReleaseThreshold` = 512
  programs, and after every job of `RunJobList` (`Campaign/CampaignDriver.cpp`, both paths) at
  `kJobLoopReleaseThreshold` = 2048. The atlas build's loop is in `HeckeExt/HeckeAtlas.cpp`, so
  `kernel.cu` injects the release as the new STL callback
  `RunAtlasCli(argc, argv, std::function<void()> between_cells = {})` →
  `AtlasOptions::between_cells`, and `HeckeExt/` never names the engine. **No value can move**: a
  cleared program is recompiled on its next miss, and `compile()` is a pure function of
  `(program, options)`. A clear concurrent with `run_cached()` is memory-safe (the cache mutex,
  `shared_ptr` entries).
- **The policy is the plan's fallback.** Releasing after *every* cell cost 6–7 % of the ten-cell
  `ext_first` sample's ext-pass wall in the quietest indicative rounds (median NEW/REF 1.067 >
  1.04): the trim hands the pages back and the next cell faults them in again. With the 512
  threshold the median over five rounds is 1.013. In the job loop, per-job release cost 4–8 % on a
  729-job sweep of 18 ms jobs; the 2048 threshold costs nothing measurable there (0.990–1.008).
- **The second half of the cause (found by WP-5).** Clearing the cache alone does **not** lower
  VmRSS: on every cell of the ten-cell sample, VmRSS after `clear()` equalled VmRSS before it. The
  freed programs stay with the allocator. `malloc_trim(0)` returns them: after the `(80, 691)` cell,
  VmRSS went 813 → 298 MB with clear + trim, against 893 → 446 MB with the trim alone (the cache
  kept, 472 programs).
- **Evidence** (`docs/implementation/slot8/WP-5_report.md`; indicative, `ENGINE_THREADS=6`, shared
  box):
  * byte identity with and without the hook: all 84 ext records and `analysis.txt` of
    `ext_compare_mini.spec` (sha256 `a2202abd…4b819`, both `EXT_COMPARE_MINI … verdict=PASS`); the
    `--atlas 13` store (FNV `0xb1834937dd087980` both, the published value); the scratch
    `--atlas 691 --n-max 40` store (`0x3a39f59d0487e307` both); the ten ext records, the job files
    outside their timing fields and `summary.tsv` of the ten-cell `ext_first` sample;
  * RSS: `ext_compare_mini` end of the ext pass **1686 → 210 MB**, process peak **1762 → 494 MB**;
    the ten-cell sample end of the ext pass **1106 → 703 MB** (medians of 5), and the between-cells
    floor falls back to 82–158 MB at the release, where it climbs monotonically to ~1100 MB without
    the hook. The sample's peak (1734 MB) is one cell's own working set (`(100, 691)` with
    `U_691`) and does not move.
  * `ProgramCacheReleaseValidation` (fast): the policy, the recompile identity, and a two-thread
    clear-while-running arm. It is clean under `CheckThread` (0 reports), as is an 8-job concurrent
    `ext = true` campaign with a per-job clear.
  * The `Σ(691)` rebuild with the hook is the lead's optional W2 run (slot-8 plan decision 11). Its
    store FNV must stay `0x73c7210047a81b97`, and its peak is reported against 19.5 GB.

### 4d. The campaign's `u_ell` resume stamps `source = "console"` — **RESOLVED**

- **Status:** RESOLVED (slot-8 WP-11b; [X] v1.11 open item 2; owner ruling 9 (A)).
- **Symptom.** A campaign's record-level `u_ell` resume (`Campaign/CampaignExt.cpp`,
  `RunCellWork`'s resume branch) ended up stamping the resumed record's `settings.u_ell.source`
  `"console"`. Tracing it: the final stamp is whichever `hecke::ScopedUEll` guard is active the
  LAST time `HeckeExtDriver::stages_two_to_five_()` runs, because that call unconditionally resets
  and refills the whole record (`rec_ = HeckeExtRecord(); ... rec_.settings = settings;`). For a
  resumed cell that is `HeckeExtDriver::resume_u_ell()`'s OWN internal guard
  (`HeckeExtDriver.cpp`), not the campaign's outer `guard(u_old)` around the historical
  reproduction — that outer guard's scope closes (and is overwritten) before `resume_u_ell()` ever
  runs. `resume_u_ell()`'s guard took no `SettingSource` argument and so always defaulted to
  `Console`; the setter is the campaign spec, never an interactive console session, so `spec` is
  right. The fingerprint is `0` at the defaults and no job id moves (`canonical_text()` /
  `fingerprint()` do not include `source`); the stamp was visible only in a resumed record's own
  `settings.u_ell.source` text, at a NON-default resumed budget (a resume to the shipped default
  collapses to `source = "default"` regardless, by `ScopedUEll`'s own value-equality rule, which is
  why the slot-7 arm that resumes to the default never caught this).
- **Repair.** `HeckeExtDriver::resume_u_ell(uint32_t budget_mb, hecke::SettingSource src =
  hecke::SettingSource::Console)` now takes the source as an argument (default unchanged, so every
  existing caller — the console-adjacent validations that call it directly — is unaffected); its
  internal `ScopedUEll guard(u, src)` uses it. `Campaign/CampaignExt.cpp`'s `RunCellWork` passes
  `hecke::SettingSource::Spec` to both the outer reproduction guard and the `resume_u_ell()` call
  (the former for consistency; it does not itself reach the final record, per the trace above, but
  it is spec-driven too). A per-job text change on resumed records only, at a non-default budget;
  a resume to the default budget is byte-identical to before (both `default`).
- **Proof.** `HeckeExtCampaignValidation` arm 5 step (6) (slot-8 WP-11b): a cell refused at
  `u_ell = budget_mb=64`, resumed under a campaign spec to `u_ell = budget_mb=4096` (deliberately
  NOT the shipped default, so the source actually shows), asserts the resumed record's text
  contains `"u_ell":{"value":"budget_mb=4096","source":"spec"}` and no `"source":"console"`
  anywhere, and that the resumed record equals a FRESH `u_ell = budget_mb=4096` campaign's record
  byte for byte. Reverting the fix (source code only, keeping the new test) reproduces exactly 3
  failures on this step; the golden text, both determinism digests, `GoldenRegressionValidation`
  and every other `HeckeExtCampaignValidation` arm are unaffected. A grep of
  `docs/matrix-engine/results/` for a resumed `u_ell` (`resumed_from_mb` in a job's `extensions`)
  found none, so no published record was stale.

---

## 5. Legacy arm: E7's contragredient operator read the factored `SymN` τ pool — **RESOLVED (`c0566e2`, 2026-09-30)**

- **Found by:** the slot-14 close's cross-config line (`docs/implementation/slot14/WP-17_report.md` §8.2). Under
  `ENGINE_BACKEND=legacy`, `GOLDEN_STRICT=1 GoldenRegressionValidation` failed tier A with 154 objects at the seven
  `e7`, `ell = 5` points (`n = 2, 4, 10, 16, 22, 24, 32`), each `EXCLUDED: HeckeOperatorOnK::compute: O12(a) FAILED --
  ... differ at q=0, entry (0,0): 2 vs 1`; `ConsoleDeterminismValidation` then failed its arm (c). The slot-13 binary
  `e8ec72d` passed; `HECKE_U_ELL_LOW_RANK=0` cleared it. The default (engine) backend was never affected.
- **Root cause.** `ContragredientCell::hecke_pair(p)` computes `op_M` (`SymN`) and `op_D` (`ContragredientN`) on
  **one** `HeckeTauTable`. Since slot-14 Q8 the `U_ell` low-rank lever is default-on (`Auto`), so at `p = ell` the
  table is built with its ρ pool **factored** (the `SymN` blocks `ρ_n(g γ)` as `U V`). The legacy fused route,
  `HeckeOperatorOnK::assemble_theta_matrix_legacy` (S13 WP-16's branch), materialised `U V` whenever the pool was
  factored, **whatever the operator's fibre** — `op_D` therefore multiplied `ρ_n^∨(s_i^{-1})` by `ρ_n(g γ_k)` instead
  of `ρ_n^∨(g γ_k)`, and O12(a) caught it against route 2 (`rho_of_exact`, in the operator's own fibre). The engine
  route reads `rho_of_term`, i.e. the operator's own `rho_pool_dual_` for a non-`SymN` fibre, so it was correct. The
  lever's refusal ("SymN only") was not bypassed: under `Auto` the lever is simply not in effect for `op_D`, and only
  this legacy branch read the shared pool regardless. Before slot 14 the lever was opt-in, the pool was dense, and the
  branch never ran for E7.
- **Why arm (F) missed it.** `HeckeUEllLowRankValidation`'s legacy arm built a dedicated τ table per `SymN`
  operator; no case shared a factored table with a non-`SymN` fibre.
- **Repair.** The legacy fused route reads the factored pool for a `SymN` operator only; every other fibre goes
  through `rho_of_term`, exactly as `compute_block` does. One condition; the lever's `SymN` path is unchanged (its
  memory benefit re-measured on the fixed build: `--bench hecke 128 691 691` 204 MB / 0.62 s with `--u-ell-low-rank`, 2098 MB / 4.60 s with `--no-u-ell-low-rank` — the slot-14 levers together; the fix touches no `SymN` path).
- **Guard.** `HeckeUEllLowRankValidation` arm (G): `ContragredientCell(n, 5).hecke_pair(5)`, `n ∈ {10, 24}`, on the
  legacy arm under `Auto` against the default route with the lever off — both operators' `A^{(q)}`, `Θ_flat^{(q)}` and
  O12(a) (34 checks; 310 → 344). Without the fix it fails twice with the golden message.
- **Value-preserving:** golden A 11687/0, B 5901/0 under default and `ENGINE_BACKEND=legacy`; EngineDet
  `0x3dddd2ef9a8efd`, ExtDet `0xaef77d786b4f29b4`, heavy `0x9ed8b83a2fb26622`, ConsoleDet `0xf6ed04bbe8e6b60a` unchanged.

## 6. The console's `rss()` reads its two fields non-atomically — **RESOLVED (slot 21, 2026-10-05)**

- **Found by:** the slot-20 close's cross-config line (`docs/implementation/slot20/WP-18_close_report.md` §4.1). Under `Check` (ASan,
  `ENGINE_CUDA_DISABLE=1`), `ConsoleScriptValidation` failed one check: `[FAIL] script 022_harness.oc exits 0 [got: 4 want: 0]`, at
  `022_harness.oc:86: assertion failed: the peak is at least the current resident set`. Re-run twice on the same binary: once the same, once
  `366 checks, 0 failure(s)`. Never seen in the `RelWithDebInfo` arms or in W1.
- **Cause.** `Console/Bindings/Harness.cpp` `VerbRss` calls `oc_util::PeakRssMiB()` (`VmHWM`) and then `oc_util::CurrentRssMiB()` (`VmRSS`), two
  separate reads of `/proc/self/status` (`Util/Rss.h`). A thread that grows the RSS between the reads (ASan's allocator) makes `rss_kb > peak_rss_kb`.
- **Fix (slot 21).** `VerbRss` now reads the current RSS (`VmRSS`) first and the peak (`VmHWM`, monotone) second, so `peak_rss_kb >= rss_kb` holds by construction; value-neutral (no golden line, no digest — `ConsoleDeterminismValidation`
  does not pin `rss()`).
- **Verification.** Fix commit `64602a59`. The re-verification under a `Check` (ASan) build is the `Check` arm of the slot-21 close's `cross_config.sh` run (step C-9):
  **FIXED `64602a59` and VERIFIED under the `Check` arm, 2026-10-06/07:** `ConsoleScriptValidation` incl. `022_harness.oc` passed in the `Check` arm and twice more (382 checks, 0 failures) (`docs/implementation/slot21/WP-18_close_report.md` §4).

## 7. `OrbifoldCampaignL23Validation` (D) `deterministic body at (3, 34)`: a rare red — **ROOT-CAUSED and FIXED (test side), 2026-10-17; CLOSED at the root by `orbifold_cell/v2` (slot 24 L23-H1)**

- **CLOSED (slot 24, L23-H1; `slot24/L23H1_report.md`).** The record format moved to `orbifold_cell/v2`: the oracle's wall time left the hashed body
  (the gate detail now ends `-> resolved`; the time is the unhashed number `timings_s.sumrule_oracle`), `record_fnv1a64` no longer depends on the
  box's load, and the masks are gone from (D), `record_compare.py` and the Z2K / Z3K / F3L validations (their bodies are compared raw).
  `slot24/l23_record_convert.py` re-derives the hash of stored v1 records (no value moves; inputs never modified). H-1 is closed. The text below
  is the history of the test-side fix of 2026-10-17.
- **Audit (slot 24, `slot24/L23H1_audit.md`, Opus adversarial).** Verdict MERGE after fixes: the converter refuses to write into its own input
  (F1); a resume over `v1` records counts them and prints `RESUME_FORMAT resumed_not_v2=<k>` (mixed-format shard, F2); the Z2K / Z3K / F3L (R) arms
  check per body that no wall time came back (F3); `ingest_l23.py` refuses a mixed v1 / v2 input (F4, for census 3.5). All 1052 census records
  (plus 180 others) converted and checked; 11 further cells re-run on the v2 binary match their converted v1 records raw.

- **Root cause (2026-10-17, `slot23/L23_flake_report.md`).** Not a nondeterminism of any value. The hashed record body carries one wall-clock
  string: the detail of the gate `sumrule_oracle_resolved` is the sum-rule oracle's last log line,
  `"SUMRULE_ORACLE ell=… n=… … -> resolved (%.3f s)"` (`Orbifold/L23/SumRuleOracle.cpp`, put into the body by `CampaignOrbifold.cpp`) —
  finding **H-1** of `slot23/GPU_scout.md` §2.3, already masked by `record_compare.py` and by the Z2K / Z3K / F3L validations, but **not by
  (D)**, which compared the two bodies raw. At (2, 22) and (3, 34) the oracle takes ≈ 0.2–0.5 ms on a release build, so both runs print
  `(0.000 s)` and (D) passes; a run preempted on a loaded box (the failing `--all` ran beside DEEP-1 and another `--all`) prints `(0.001 s)`
  and (D) fails. That is why the audit's 40 trials passed.
- **Reproduced** on demand: the `Check` (ASan / UBSan) build is slow enough that the times differ in most runs — **4 of 5** by-name runs of the
  unfixed tree failed (D), at (2, 22) and at (3, 34), each first-difference text pointing at exactly that field, e.g. ``run `"detail":"SUMRULE_ORACLE
  ell=3 n=34 dimS=3 K=80 max_invariant=10 -> resolved (0.009 s)"` vs recompute `… (0.003 s)"` ``. The bytes before the time are equal.
- **Fix (value-neutral, test only).** (D) compares the bodies with that one time masked to `(<t> s)`, by the `record_compare.py` regex
  (`MaskOracleTime` in `CampaignOrbifoldValidation.cpp`). Three new checks: the mask hits exactly one site in each body (so it is never
  vacuous), and a negative control (a changed time is hidden, a one-character change of a value is not). 669 → 672 checks. No record, hash or
  golden entry moves. The record format keeps the time in the hash (H-1 stays as filed: the owner agreed on 2026-10-13 to drop it from the
  hashed body at the next record-format event).
- **Sanitizers:** ASan + UBSan (`Check`, `ENGINE_CUDA_DISABLE=1`, `detect_leaks=1`) on the validation by name and on the `--all` window
  below: no report. TSan was not feasible: the `CheckThread` binary segfaults inside `libtsan` at startup on the current WSL kernel
  6.18.54, with or without `setarch -R`, even for `--list`; a TSan hello-world works. That is a separate toolchain issue (report §4).

- **Seen:** once, in the `--all` run of the slot-23 G2-A / G2-B branch (`slot23-g2ab` at `bfaf271b`, binary
  `$HACS_DATA/s23/g2ab/build/cohomology_app`, log `s23/g2ab/all.log`), beside the DEEP-1 production run and another
  agent's `--all`: `[FAIL] (D) deterministic body at (3, 34)`. (D) compares the hashed body of the campaign run's ℓ = 3, n = 34 cell with a
  recompute of the same cell in the same process.
- **Not reproduced** in about 45 executions: 40 audit trials (`slot23/G2AB_audit.md` §5; `s23/g2abaudit/summary.txt`) — by name 12× on NEW and
  12× on REF (the base `886357b6`), 6× on NEW with `HECKE_MODULE_STREAM=0`, 5× each on NEW and REF in the one-process `--all` window
  `OrbifoldMPHeckeValidation … L23AmalgamReaderValidation OrbifoldCampaignL23Validation` with the GPU live — and the implementer's by-name,
  window and 197-name one-process prefix runs on NEW and REF. All `[PASS]`, `ORBIFOLD_L23 … verdict=OK`.
- **Not G2.** Statically, the ℓ = 3 orbifold cell (`Campaign/CampaignOrbifold.cpp`) reaches none of the functions G2 modified: it constructs
  neither `EquivariantCohomologyOnK` nor `HeckeOperatorOnK`; its three `integral_model::Subquotient` calls pass the field `ModCtx<U32> F(ell)`,
  so `complement_basis` runs, not `cyclic_decomposition`; `AmalgamReader` uses `ladic::kernel_module` / `invariant_factors`; its composite-ring
  work goes through `ring3k` / `elim::kernel_module`. No device elimination runs in it either (the `EFFECTIVE DEVICE_ELIM` totals are final after
  `CudaImmaElimValidation`). The cell's code is identical on REF, so the defect is pre-existing in kind: a rare state- or timing-dependent
  nondeterminism in the orbifold cell's own path (or a memory error), not bisectable to G2.
- **Diagnostic added (slot-23 G2-A / G2-B merge).** On a mismatch (D) now names the first differing byte and the JSON field around it
  (the check text gains ``-- first difference at byte <k>: run `…` vs recompute `…` ``), so the next occurrence names the field. Value-neutral (failure text only).
- **Follow-ups:** (1)–(3) done 2026-10-17 (above; `slot23/L23_flake_report.md`). Still open, and not part of this defect: H-1 itself
  (the time leaves the hashed body at the next record-format event), and the `CheckThread` startup crash on kernel 6.18.

## CheckThread (TSan) startup crash on WSL kernel 6.18 -- root cause and fix (2026-10-18)

- **Symptom** (`slot23/L23_flake_report.md` section 4): the `CheckThread` `cohomology_app` segfaulted before `main`, even for `--list`,
  with or without `setarch x86_64 -R`; a TSan hello-world was fine. (Without `-R`, any TSan binary on this kernel dies with
  "FATAL: ThreadSanitizer: unexpected memory mapping" -- the separate, known ASLR issue; `-R` handles it.)
- **Root cause: not the kernel.** `strace -k` shows `SIGSEGV si_addr=NULL` in `__tsan_func_entry` called from
  `engine::ring3k::(anonymous)::axpy_small_3` during relocation processing in `ld.so`. `Ring3k.cpp` declares the small-modulus
  row kernels with `__attribute__((target_clones("arch=skylake-avx512","arch=haswell","default")))`; GCC 11 emits an ifunc
  resolver for each and, under `-fsanitize=thread`, instruments that resolver. The resolver runs at relocation time, before
  libtsan is initialised, so the thread state is NULL. Not PIE-related (`-no-pie` crashes identically), not libcudart-related.
- **Fix** (value-neutral): `RING3K_CLONES` is empty under `__SANITIZE_THREAD__` (`src/ModArithmetic/Binary/Ring3k.cpp`); the kernels
  are compiled once for the baseline ISA in the TSan build only. Normal builds are unchanged.
- **Proof:** `tsan_run.sh` (GPU visible, `setarch -R`) on `EngineDeterminismValidation` (262 s) and `ValidationHarnessCatchValidation`:
  both `[PASS]`, `TSAN_FILTER reports=0 driver=0 ours=0 verdict=OK`. No sysctl change is needed or requested.

## `HeckeExtArchitectureValidation` red since slot-23 G2-P -- **RESOLVED (2026-10-19)**

- **Symptom:** `check_heckeext_includes.sh` (run by `HeckeExtArchitectureValidation`) reported two rule-2 offenders,
  `HeckeExt/HeckeModuleStreamValidation.cpp:152-153` (`Engine/EngineRuntime.h`, `Engine/ThreadPool.h`), introduced by G2-P (`77042d3a`).
- **Cause:** the validation's thread-count arms (1 / 7 / 16 workers) need `ScopedConsumerPool`; rule 2 banned `Engine/` in all of `HeckeExt/` with no exception.
- **Fix** (guard only, no value touched): a second rule-2 exception list `ALLOW_EXT_ENGINE` (exact paths, reason per entry; `Engine/` only,
  `Cuda/` and `BlockFlatMatrix.h` stay banned) holding that one test-harness file. Non-validation `HeckeExt/` files remain Engine-free.
- **Proof:** `check_heckeext_includes: OK -- 1043 files scanned`.

## W1-23 sanitizer finding S1: UBSan signed overflow in `OrbifoldF3lValidation` -- **RESOLVED (2026-10-19)**

- **Symptom:** UBSan (`Check`) reported 6 `signed integer overflow` errors in the planted-matrix block of `RhoArm`
  (`Campaign/OrbifoldF3lValidation.cpp`, `l * e(rng)`), `l = 2^61 - 1` on the u64 arm, `e` uniform in [-60, 60].
- **Cause:** the signed product overflowed int64 and wrapped, so on that arm the "planted" `a ≡ 0` / `c ≡ 0 (mod ell)` matrices were not multiples of `l`.
- **Fix** (test side only): the multiplier is folded into `|m| ≤ (INT64_MAX - 1)/l` (a no-op for every small `l`, so those arms draw the same matrices),
  keeping `l*m` and `1 + l*m` in range and exact multiples of `l`.
- **Effect:** the check count moved 39163 → 39135 (the u64 arm's planted matrices now have the intended unit / non-unit pattern, which changes
  which cases are refused); `failing=0`. No golden entry and no digest depends on this validation. Proof: `Check` build, ASan+UBSan run: exit 0, no runtime-error lines.

## W1-23 sanitizer finding S2: TSan report in `HeckeIotaStreamValidation`'s Watchdog -- **tool limitation, no code change (2026-10-19)**

- **Symptom:** `CheckThread` reports a "double lock" on `m_` in `~Watchdog` and a race on `done_` against the watchdog thread inside `cv_.wait_for` (`Hecke/HeckeIotaStreamValidation.cpp:155–163`; W1-23 ledger §5).
- **Cause:** GCC 11's libtsan has no interceptor for `pthread_cond_clockwait` (what libstdc++'s `wait_for` calls), so TSan misses the mutex re-acquire: a false positive.
- **Disposition:** recorded only; code unchanged. Ignore this report on GCC 11 (a newer libtsan has the interceptor).

## S24 MT-1 notes (2026-10-20) -- **open, by design; no defect**

1. **The block model's diagnostic counters depend on the thread count under `HECKE_MODULE_MT`.** `compute_cohomology_module()` runs X_q's
   D C as `blk::gemm_dense` on column tiles of C when a hook is installed (pool > 1), so `engine::blk` statistics (`dense_products`,
   `axpys`, `cse_hits`) count once per tile. No value and no validated counter changes (`HeckeModuleMtValidation` compares the module-stream
   counters, which are unaffected); a future validation comparing `blk` statistics across thread counts must pin `HECKE_MODULE_MT=0`.
2. **Resolved at the audit (`slot24/MT1_audit.md` F1):** the opt-in forms overlap `HECKE_MODULE_MT_FORMS` (+1.6 GiB at (1000, 10007),
   16 threads; no gain after FNTT) and the `ALLOW_EXT_ENGINE` exception it needed for `HeckeExt/HeckeSaturationDefect.cpp` were removed;
   the extension layer is Engine-free again outside its validations.

## The `ENGINE_SHADOW_LEGACY=ON` build was red on two comparisons that were not value divergences -- **RESOLVED (S24 CL-L1, 2026-10-31)**

Found by CL-L1's first `legacy-shadow` build (`OC_ENABLE_LEGACY=ON` + `ENGINE_SHADOW_LEGACY=ON`, RelWithDebInfo): `--all` read
`Some validations FAILED (206/222 passed, 45 slow-tier skipped)` and `GOLDEN_STRICT=1 GoldenRegressionValidation` read
`tier A checked 11434, failing 1104; tier B checked 5748, mismatching 0`. **Pre-existing**: the unmodified base `3ed47b59`, built with
`-DENGINE_SHADOW_LEGACY=ON`, fails both in the same way: the same golden line (`tier A checked 11434, failing 1104; tier B checked
5748, mismatching 0`), the same 13 `EXCLUDED` points with the same message (line-for-line diff empty), and the same throw in
`HeckeExtSmallEllValidation` and the same `ConsoleCliPreservationValidation` failure. No default-build value was ever involved:
OFF and ON builds and `ENGINE_BACKEND=legacy` all read the golden figures of record.

1. **`HeckeOperatorOnK: Theta_eq differs at q=0`** (34 throws in `--all`; 15 of the 16 failing names).
   - *First differing object:* `Theta_eq_[0]` of the golden point `n=2 ell=5` (object `ext`, the HeckeExt cell); engine side
     **0×0**, legacy side **27×27**. The same at every golden `ext` point (`n=2,4,10…` at `ell=5,13`), which the harness then
     reports as `ext_excluded` (computed but missing from the reference) and the determinism digests as one differing record.
   - *Intermediate:* Theta_eq, the level-(a) restriction solved by Theta8/Theta9 -- not a published value of the `ext` cell.
   - *Cause:* under `HeckeOperatorOptions::ScopedThetaEqCertification(false)` (set by `HeckeSturmSweep` / the HeckeExt driver since
     slot-4 E2b, `47677b6b`, 2026-09-21) the block arm skips the Theta8/9 solve and publishes an empty Theta_eq with
     `theta_eq_certified_ = false` (its documented contract), while the legacy arm always solves. The shadow compared the two
     unconditionally.
   - *Fix* (shadow-only code, `Hecke/legacy/HeckeOperatorOnKShadow.inc`): Theta_eq and the counters `theta_eq_solves` /
     `residual_max` are compared only when `theta_eq_certified_`; Theta_flat, `A^{(q)}` and the relation / cocycle counters are
     compared as before.
2. **`ConsoleCliPreservationValidation`: `HeckeIdentityValidation` stdout is not byte-identical to the frozen file.**
   - *Cause:* the shadow also runs the legacy cohomology arm (`compute_cohomology_legacy`), which prints `[TIMING] A_Cq kernel q=…` /
     `[TIMING] A_Zq kernel q=…` on stdout (130 extra lines); the frozen transcript has none.
   - *Fix* (`Console/ConsoleValidation.cpp`, under `#ifdef ENGINE_SHADOW_LEGACY` only): `CompareFrozen` drops those two line prefixes from
     the live stdout before comparing. The legacy arm's prints are untouched (they are `ENGINE_BACKEND=legacy` code, CL-L2's to move).
- **After the fix** (same shadow build): the 16 previously failing names, run in one process, all `[PASS]`; `GOLDEN_STRICT=1` reads
  `Reference entries: 18273`, `tier A checked 12042, failing 0; tier B checked 6231, mismatching 0`. Record: `slot24/CLL1_acceptance.md`.

## W1-24 sanitizer findings (slot-24 close K7, 2026-11-04/05)

Source: `docs/implementation/slot24/CLOSE_P3_report.md` §3 (logs `$HACS_DATA/s24/close/xsan/`).

- **UBSan, real, test side -- RESOLVED (`3b007e20`, in CLOSE-24b `6e64815e`).** `IntegralDescentHeckeValidation.cpp:534:24: runtime error:
  signed integer overflow` in arm (W): `r3 += static_cast<int64_t>(Q340)` with `Q340 = 3^40 > INT64_MAX`, so the reference residue was formed by
  int64 wraparound. Fix: the residue is computed in uint64 (`r = |v| mod Q340`, `Q340 - r` for `v < 0`, `r != 0`); `H3::` code untouched; check
  count 2944 unchanged; `Check` re-run 0 reports. No golden entry or digest depends on it.
- **ASan RSS-prediction artefact -- TOOL class, no code change.** Under `Check`, `IntegralDescentPairValidation` (exit 3) and
  `IntegralDescentTreePairValidation` (exit 1, its (RB) arm re-runs the former) fail only `(S) the pair lift at p=5 / 7 … within its RSS prediction
  (rule 19)` (`rss_pred_mib=64 rss_growth_mib=126`): the instrumentation inflates RSS past a fixed prediction. No sanitizer report; all value
  checks pass; both names pass in the non-sanitizer builds. Run them under a sanitizer expecting these three RSS checks to fail.
- TSan: no report (5 names + `tsan_run.sh` on `DescentSmithGpuValidation`). LSan: no leak.

## `hida_tower(n, ell, 1)` with e_max = 0 leaks an `ENGINE_CHECK` (K < 2) -- **FIXED in NBCONFIRM S3 (2026-11-07, branch `s25-wip-nbconfirm-s3`); value-neutral**

Source: `docs/console/NBCONFIRM_S2_calibration.md` §6 item 7 and Fix round 1; `docs/console/NBCONFIRM_S2_audit.md` §4.

- **Symptom.** `hida_tower(n, ell, 1)` at a cell whose torsion pre-pass gives e_max = 0 (seen in S2 at ℓ = 23 and ℓ = 101) sets
  `K = m_max + e_max = 1` (`HeckeExt/HeckeHidaTower.cpp:385-386`) and then fails `ENGINE_CHECK_MSG(... K >= 2, "... the module route needs
  ell >= 5, n >= 1, K >= 2 (def:hidatower)")` (`:171`, also `:130`) inside `RunModuleCell`. The console reports an `[EXCEPTION]`-style
  internal error instead of a typed refusal. No value is produced, so no value, record, golden entry or digest is affected.
- **Why it is not a bug in the check.** K ≥ 2 is a precondition of the contract's module route (`def:hidatower`), not an implementation
  accident. Running at K = max(2, m + e_max) and reading off level 1 would be a **route change** under a binding definition.
- **Fix (S3, value-neutral).** Right after the pre-pass, when `t.K < 2`, throw a typed error that the binding maps to
  `TypeError: hida_tower: m + e_max = K = 1 < 2: the module route of def:hidatower needs K >= 2 (e_max = 0 from the torsion pre-pass)`.
  The message states the fact only; it gives no "use m ≥ 2" recipe, because it is unverified that a level-2 tower contains the level-1
  datum asked for.
- **Owner / [C] question (later, not blocking).** Whether a `K = max(2, ·)` route that reads level 1 off a level-2 tower is admissible.
- **Related, separate.** Whether `Pow64` (`pow_wrap`) can wrap silently for ℓ^(m + e_max) ≥ 2^64 inside today's envelope was
  investigated separately: unreachable, and guarded anyway by `CoefficientRingContext` (exit 5 at ℓ^K ≥ 2^64;
  `docs/implementation/slot25/POW64_investigation.md`); it is not part of this entry.
- **As fixed (S3).** `hida::ComputeTowerCell` throws `hida::TowerPreconditionError` (an `std::invalid_argument`) right after the pre-pass
  when K = m_max + e_max < 2; the console binding maps it to `type error: hida_tower(n, ell, m): m + e_max = K = 1 < 2: the module route
  of def:hidatower needs K >= 2 (e_max = 0 from the torsion pre-pass)` (exit 3). Every in-tree caller of the module route uses m >= 2, so
  no call that ran before is refused. Gated by `ConsoleCostModelValidation` (I).

## `hecke_structure(1, 0)` leaks an `ENGINE_CHECK` (`RationalStep: d_target >= 1`) -- **FIXED in NBCONFIRM S3 (2026-11-07); value-neutral**

Source: `docs/console/NBCONFIRM_S1_classification.md` §4 item 5, S2 §6 item 7 (line `Integral/HeckeZRational.cpp:1185`).

- **Symptom.** `set coefficient_ring = "Z"; hecke_structure(1, 0)` failed with `error: hecke_structure(...) failed / caused by:
  std::logic_error: …HeckeZRational.cpp:1185: ENGINE_CHECK failed: D >= 1 -- RationalStep: d_target >= 1` (exit 3). The cusp space at
  N = 1, n = 0 is 0, so there is no Hecke structure to compute; no value was produced. It is the only (1, n) / (N, 0) cell that leaks (S2 §2.2).
- **Fix (S3).** The binding refuses (1, 0) by name before any work: `type error: hecke_structure(N, n, algebra): at N = 1, n = 0 the cusp
  space is 0 (no Hecke structure to compute)` (exit 3, unchanged). The record builder is untouched. Gated by `ConsoleCostModelValidation` (I).

## `descent(N, n, primes)`: the primality loop of a `primes` entry near 2^32 -- **FIXED in NBCONFIRM S3 (2026-11-07); value-neutral**

- **Symptom (found reading the code, never hit).** `Console/Bindings/Descent.cpp` tested p prime with a `uint32_t d` and `d * d <= p`;
  for a prime p > 65535² the product wraps, so the loop can run up to ≈ 2^32 iterations (and divide by zero if `d` itself wraps)
  before the old `p > 97` refusal is reached. No wrong value was possible: the call could only refuse, hang or crash.
- **Fix (S3).** `d` is 64-bit. No accepted input changes.

## `level_n` / `nebentypus` with N ≥ 2^31 leak an `ENGINE_CHECK` (`FactorLevel: N in [1, 2^31)`) past the envelope -- **FIXED in NBCONFIRM S3 Fix round 1 (2026-11-07); value-neutral**

S3 audit m1. Under `confirm = yes` (or on a terminal REPL) the N bound no longer throws, so `hecke::level::IndexGamma0(N)` ran on the
huge N and `FactorLevel`'s `ENGINE_CHECK` escaped (`error: level_n(...) failed / caused by: std::logic_error`, exit 3). Both verbs now
refuse N ≥ 2^31 by name right after the envelope bound (`TypeError`: "N must be < 2^31 (word size of the level code)", exit 3).
Prompt-less modes stop at the N bound first, with the pre-S3 text (byte identity re-checked, `NBCONFIRM_S3_report.md` §8). Pinned by
`ConsoleCostModelValidation` arm (F).

## HeckeZ record: g_P `open(no primitive T_p)` was read as the certified value 1 -- **FIXED in S27 TS-FIX (2026-11-13, branch `s27-wip-tscode`); value-neutral on HZ-DS editions 1--3**

Source: `docs/implementation/slot27/TS_design.md` §5.4 (v0.2), `TS_design_audit.md` B1; the [C] wording is item 8 (j) of C128 (T1 / T7).

- **Defect (latent in the shipped `lex` code).** `RationalStepImpl` (`Integral/HeckeZRational.cpp`) computes g_P only from the
  **primitive unit** candidates of the (C1) search. A step certified by a combination (no unit is primitive -- units are tested first)
  has none: `gP_status = open(no primitive T_p)` and `R.gP` stays a default `Factored` (`cofactor_test = one`, `complete()` true, no
  factors). Five consumers in `Integral/HeckeZRecord.cpp` read that as "g_P = 1, certified": `RatFor` (the at-root read's `v_gP = 0`,
  `gP_complete = true`), `every_closes` (hence `eis_single`), G3's `eisenstein` branch (`G3.C_T.upper = 1`, **`G3.C_T.status =
  certified`, `G3.C_T.exact = 0x1`, `G3.fibre_product = certified`**), its second route / Mazur rows (no rows, by accident) and K3
  (`CertVal > 0` false, skipped by accident). Today the at-root read's `ENGINE_CHECK` (`HeckeZLocal.cpp`, v(exp eta_L) > 0 with v_gP = 0)
  throws first wherever a congruence prime is in the read set, so the false G3 was never written; a fix confined to the read would have
  turned the throw into a false `certified`.
- **Reach.** Every Eisenstein-rational level-1 or `anemic` step certified by a combination. No record of editions 1--3 is such a step
  (census `docs/implementation/slot27/TS_tools/ed3_gp_census.py` over the 226 edition-3 records: `ED3_GP records=226
  eis_rational_with_combination=0 verdict=NEUTRAL`); under `theta_order = lex_then_greedy` (TS) every continuation-certified
  Eisenstein-rational step is one, which is why the fix lands first.
- **Fix (TS-FIX).** One predicate `heckez::GPIsBound(R)` <=> `gP_status in {upper_bound_certified, partial(unfactored)}`, asked at every
  consumer: `RatFor` gives the read no g_P (`v_gP = -1`, `gP_complete = false`: the read uses its own local value or none, by its own
  rule); `every_closes` is false (no `eis_single`); G3's `eisenstein` branch writes `G3.partition = eisenstein`, `G3.S = 0`,
  `G3.S_prime = 1`, **`G3.C_T.status = not_run`**, `G3.fibre_product = not_certified` and no `upper` / `upper_v` / `read` / `cofactor`
  / `cofactor_test` / `exact` / `lower_v` / `eta_L` / second-route / Mazur word; K3 asks the predicate; the `congruence` reason loop asks it
  too (no factors either way). The congruence-module bound of such a step is lost (a bound from non-primitive T_p would be a [C] change
  of `def:heckeZcong`'s use; not planned, `TS_design.md` §11.2).
- **Gate.** `HeckeZThetaSearchValidation` arm (c'): a validation-only `RationalSettings::validation_skip_units` hook (unprinted) marks the
  units of (1, 10) `full` non-primitive; `lex` then certifies theta = T_3 + T_5, g_P is `open(no primitive T_p)`, the record is `final` with
  G3 `not_run` and no bound word (before the fix: the `ENGINE_CHECK` of the at-root read); the control without the hook is the golden
  (1, 10) record `0x5e84b4c2540ff22a`.
