# The campaign driver (`--campaign`) — matrix-engine Phase 6

**Status.** Shipped. CPU, **batched**: since Phase 6 Part A a shape group's
jobs run concurrently on the Phase 4 tape engine, `jobs` of them at a time and
each on its own engine pool of `threads` workers (§12). `jobs = 1` is the
original sequential driver and is still the default.

`--bench hecke <n> <ell> <p>` runs *one* point and prints timings. The campaign
driver runs a *sweep* and writes down the mathematics: one JSON per job with the
canonical objects and their FNV-1a-64 hashes, the full `HeckeReport` levels
(a)/(b)/(c), the certificates that were executed, timings and peak RSS — plus a
campaign-level `index.json` and a `summary.tsv`, which is the plan's
"published table of new `A^{(1)}(T_p)` char-polys".

```
./hacs --campaign <spec-file> [--output <dir>] [--dry-run] [--quiet]
./hacs --campaign --help
```

Everything runs through the **public API only** — the same construction recipe
as `--bench` and every V-stage validation
(`CreateSL2ZFundamentalDomainTriangulation` → `GenerateSL2ZRelationsElt` →
`EquivariantCohomologyOnK::compute_cohomology` → `HeckeCosetTables` →
`HeckeTauTable` → `HeckeOperatorOnK::compute` → `HeckeOperatorFamily` /
`HeckeModuleDecomposition` / `HeckeCrossChecks`), so campaign numbers and `--all`
results come from identical code paths.

---

## 1. Spec format

Line-oriented, hand-rolled, no third-party parser (repo convention).

```
# or //          comment to end of line
---              on a line by itself: start a new SECTION
key = value      value is a comma-separated list whose elements are literals
                 or ranges `a..b [step c]` (step defaults to 1)
```

**Grid keys — per section.** The campaign is the union of the sections'
cartesian products, so one file can mix a broad shallow sweep with a deep one.

| key | meaning |
|---|---|
| `n_sym` (`n`) | symmetric-power degree `n` (`d_V = n + 1`) |
| `ell` | coefficient prime `ℓ`; `ℓ ≥ 2^32` selects the `uint64_t` pipeline (see §6) |
| `p` (`p_hecke`) | Hecke prime; `p == ell` is `U_ℓ`, same code path |
| `r` | exponent in `T_{p^r}`; `r ≥ 2` adds the algebra recursion (32-bit `ℓ` only) |
| `q` (`degrees`) | which cohomological degrees to report (default: all of the model's). The pipeline always computes every degree in one call. A non-default list is part of the job's identity: it changes the job id (§4) and the shape group (§2). |

**Campaign keys — anywhere, last assignment wins.**

| key | default | meaning |
|---|---|---|
| `name` | `campaign` | echoed into `index.json` and every job file |
| `output` (`output_dir`) | `campaign_out` | output directory (created) |
| `model` | `sl2z_7vertex` | model-descriptor name (§5); an unknown name is a spec error |
| `resume` | `false` | skip jobs whose output file exists *and* carries the completion trailer (§4) |
| `certify` | `full` | `full` \| `sampled(<fraction>)` \| `sampled(every <k>)` \| `sampled(<k>)` \| `none` (§3) |
| `lean` | `false` | memory-lean mode (§7) |
| `level_a` | `auto` | `auto` \| `always` \| `never` — whether the per-job report carries level (a) |
| `level_a_max_entries` | `16000000` | the `auto` size gate, in matrix entries |
| `theta_rank_max_dim` | `2048` | `rank(Θ_flat^q)` is computed only below this dimension |
| `jobs` | `1` | how many of a shape group's jobs run **concurrently** (§12) |
| `threads` | `0` | engine worker threads **per concurrent job**; `0` = share the process-wide pool (`ENGINE_THREADS`) |

**Mathematical settings — campaign-wide, and they may change a value.** Every
key `hecke::MathSettings` registers (`locality`, `u_ell`, `sturm`,
`sturm_unavailable`, `commutant_budget`, `final_mode`) is accepted here,
validated by the engine and nowhere else. A non-default one changes the job id
and the shape signature (§4); at the defaults the fingerprint is `0` and
nothing is appended.

**Extension-layer keys (hecke-extensions slot 5, WP-2) — §14.**

| key | default | meaning |
|---|---|---|
| `ext` | `false` | run the extension engine once per `(n_sym, ℓ)` **cell**. **With it `false` the campaign's output is byte-identical to the pre-WP-2 driver's** |
| `family` | `2,3,5,7` | the **good** primes of `S_0`; the literal token `ell` is recorded and admitted only through the `u_ell` budget |
| `sign` | `all` | `all` \| `plus` \| `minus` — which `ι`-sign record the cell reports |
| `ext_groups` | `all` | `bulk` \| `bulk+bd` \| `all` — `bulk` leaves the cone unbuilt |
| `ext_jobs` | `1` | *(slot-8 WP-6, a scheduling knob)* how many cells of the ext pass run **at once**, each on its own worker with its own engine pool of `threads` workers; `1` is the sequential pass (§14) |
| `ext_memory_mb` | `40000` | *(slot-8 WP-6, a scheduling knob)* the admission cap of the parallel pass: the sum of the running cells' predicted memory (§14) |
| `ext_gpu` | `off` | *(slot-8 WP-6b, optional, a scheduling knob)* `off` \| `on` \| `force` — one extra **device worker** beside the `ext_jobs` CPU workers, whose engine programs are compiled for the GPU (§14, "The device worker"). **Never on by default** |
| `ext_gpu_cells` | — | *(slot-8 WP-6b, a scheduling knob)* `n:ell` pairs (commas / blanks) the device worker takes — and only it — instead of its own rule; needs `ext_gpu ≠ off` |

**`ext_jobs`, `ext_memory_mb`, `ext_gpu` and `ext_gpu_cells` change no value,
no job id, no shape signature, no record file name and no line of `index.json`
or `summary.tsv`** — only *when*, and on which device, a cell runs. They are not
part of `ExtSpec::signature_tag()`, and `HeckeExtCampaignValidation` arms 10 (d)
and 11 (f) assert all of it.

A complete example:

```
name    = t2_sweep
output  = out/t2_sweep
certify = sampled(every 10)
lean    = true
n_sym   = 0..200 step 2
ell     = 2,3,5,13,691,10007,134217757
p       = 2
r       = 1
```

`--dry-run` prints the plan (groups, jobs, which jobs get the external
cross-checks) and exits without computing anything.

---

## 2. Shape signatures, grouping, and the Phase 4 batching hook

`campaign::plan_campaign(spec) -> std::vector<JobGroup>` expands the sections,
de-duplicates identical points (first occurrence wins), and groups the jobs by
**shape signature**

```
(n_sym, p, r, degrees, model)
```

— everything that fixes the matrix *shapes* and the exact `Mat22` coset / τ
tables. Only `ℓ` varies inside a group. That is exactly axis (e) of
`02-pipeline-consumer-audit.md` §4: *"several `ℓ` share the same `Mat22` tables
and the same `n_k`, so the reductions `γ mod ℓ` and the `ρ_n` evaluations could
be batched **across `ℓ`** into one wide kernel with a per-batch modulus."*

Ordering is deterministic and total: groups ascending by signature, jobs inside a
group ascending by `ℓ`, campaign-wide indices assigned in that emission order
(the `certify = sampled` subset is a function of that index, so it is stable).

**The batching seam is `RunJobGroup()`** in `Campaign/CampaignDriver.cpp`, and
since Phase 6 Part A it *is* batched: it runs `jobs` of a group's jobs at a time,
each on its own engine pool — see §12. Nothing else in the driver moved: the spec
parser, the JSON writers, the certify logic and the validations are untouched.
`CampaignSmokeValidation` pins the contract: a group's jobs are shape-uniform and
`ℓ`-sorted, they produce hash-for-hash the same objects as 20 individual
single-job campaigns, and the concurrent arm reproduces the sequential one job
for job, object for object, at four different `jobs × threads` splits.

---

## 3. `certify`: what is sampled and what is never sampled

**The in-process certificates C3–C6 are NEVER sampled.** They run on every job in
every mode, because they are not optional extras — they are part of what
`compute()` means:

| | certificate | where |
|---|---|---|
| C3 | `∂τ = τ∂` proven exactly | `HeckeTauTable`'s constructor (throws otherwise) |
| C4 | O12(a): the two Θ routes agree over **every entry of every degree** | inside `HeckeOperatorOnK::compute()` |
| C5 | the exact `Θ_eq` solve residual (amendment A-N3), recomputed independently of the solver and asserted identically zero | inside `compute()` |
| C6 | `HeckeModuleDecomposition::certify() == 0` on every reported degree | the level-(c) step |

Every job's JSON records their **executed counts** (`tau_certified`,
`routes_bit_identical`, `relation_checks`, `cocycle_checks`, `theta_eq_solves`,
`theta_eq_residual_max`, `decomposition_certified`), so "did they run?" is a
machine-checkable property of the output rather than a claim.
`CampaignCertificateValidation` counts them.

**The external cross-checks are the sampled ones** — they are validation cost,
not result (`03 §4.2`):

* `HeckeCrossChecks::run_all` — the classical `α`/`β`/`ω` three-map
  factorisation, asserted equal to the fused `Θ_g`;
* `HeckeOperatorFamily::T_p_pow_direct` (for `r ≥ 2`) — the independent direct
  double-coset route, compared entrywise against the algebra recursion.

| `certify` | external cross-checks run on |
|---|---|
| `full` | every job |
| `sampled(every k)` / `sampled(k)` | jobs whose campaign index satisfies `index % k == 0` |
| `sampled(<fraction>)` (`0.25`, `1/4`) | the same, with `k = round(1/fraction)` |
| `none` | no job |

`none` exists because `sampled(every k)` always selects index 0, and a
thousand-point campaign at `n_sym ≈ 1000` cannot afford even one
`HeckeCrossChecks` run. The mode, the stride, and the **per-job** decision
(`"selected"` / `"ran"` / `"rc"` / `"note"`) are all recorded in the JSON.

---

## 4. Output layout

```
<output>/
  index.json            campaign metadata, the shape groups, one row per job
  summary.tsv           one row per job — the published table
  jobs/<job-id>.json    one streamed JSON per job (the job id is below)
  ext/hecke_ext_ell<L>_n<N>.json      (only with `ext = true`, §14) one record
  ext/hecke_ext_ell<L>_n<N>.state.<kind>[.<i>].json   its oversize states
```

### Job ids (`Job::id()`)

The job id is three things at once: the **stem of the job's output file**, the
**`id` / `file` fields of `index.json` and `summary.tsv`**, and the **resume
key** (`resume` skips a job iff `jobs/<id>.json` exists and carries the
completion trailer). It must therefore be *injective on exactly the tuple
`plan_campaign()` de-duplicates by*, which is `(n_sym, ℓ, p, r, degrees)`.

```
n<N>_ell<L>_p<P>_r<R>                 the model's DEFAULT degree list
n<N>_ell<L>_p<P>_r<R>_q<d1>-<d2>-…    any other degree list, ascending
```

The **default degree list** is the model descriptor's own full list
`0 … num_degrees()-1` — i.e. exactly what a section *without* a `q` key expands
to (`sl2z_7vertex`: `0,1,2`). So the suffix appears only when a spec names `q`
and names something other than every degree, and **every id ever written by a
spec that does not use `q` is unchanged**; the published campaigns under
`docs/matrix-engine/results/` keep their file names, `index.json` ids and
`summary.tsv` `file` column verbatim.

The encoding is unambiguous: the four prefix fields are tagged and the last of
them is `_r<digits>`, so an `_q…` tail can never be read as a prefix field; the
degree list is sorted and duplicate-free by construction, so its `-`-joined
form is a canonical name for the set; the empty tail denotes exactly one list
(the model default); and an *unknown* model has no default, so the suffix is
then always emitted rather than guessed. Examples:
`n16_ell5_p2_r1` (`q = 0,1,2`), `n16_ell5_p2_r1_q1`, `n16_ell5_p2_r1_q0-2`.

#### The mathematical-settings suffix (hecke-extensions slot 4, WP-1 / E2a)

Since slot-4 WP-1 the spec also accepts the **mathematical settings** of
[X] §1.5 (`locality`, `u_ell`, `sturm`, `sturm_unavailable`, `commutant_budget`,
`final_mode` — every key `hecke::MathSettings` registers), parsed beside the
campaign-wide keys and validated by `HeckeSettings` and nowhere else. Unlike
every `ENGINE_*` knob, **a mathematical setting may change the value a job
computes**, so it is part of the job's identity:

```
n<N>_ell<L>_p<P>_r<R>[_q<tag>]_s<16 hex>    a NON-DEFAULT mathematical setting
```

`<16 hex>` is the **whole** FNV-1a-64 fingerprint of the non-default entries,
never a truncation, because the id is the output stem and the resume key and
must stay injective. The tail comes *after* any `_q` tag, so the encoding
argument above extends verbatim: `_q`'s characters are digits and `-`, and `_s`
can follow only `_r<digits>` or a `_q` tag. The `shape_signature` string gains
` s=<16 hex>` under the same condition, and the per-job JSON gains a `settings`
block with every registered key, its value and its `source`.

**At the defaults the fingerprint is `0` and nothing is appended**, so every
published file name, `index.json` id, `summary.tsv` `file` column and shape
signature is byte-unchanged — `CampaignSmokeValidation` pins `n16_ell5_p2_r1`
and `HeckeExtRecordValidation`'s job-id arm pins the whole table.

**Registering a key moves the per-job `settings` block, and nothing else**
(hecke-extensions slot 7, WP-2). The `settings` block lists **every
registered** key (rule 2 of [X] §1.5: a setting is recorded, never inferred),
so a key registered at its default — slot 7 registered `presentation` and
`predictions`, bringing the registry to **ten** keys — adds one member to the
`settings` block of every per-job JSON, and of every ext record file, written
afterwards. Because the new key is at its default, the fingerprint stays `0`,
so **job ids, file names, the `_x<16 hex>` ext record tags, the 21-column
`summary.tsv` header and every shape signature do not move**. So slot-6
WP-6's statement that `ext = false` output is byte-identical holds of ids,
names and headers, and **not of per-job file contents across a key
registration**. No published campaign stores per-job files
(`results/*/` hold `index.json` and `summary.tsv` only), so nothing published
moved. Golden is unaffected: since slot-7 stage 1 (1) the golden harness sees a
record's `settings` only as `{"fingerprint": …}` (a path-scoped reduction of
the top-level member), so a key registered at its default moves no golden line.

> **Fixed 2026-09-16.** Before that date the id omitted the degree list while
> `plan_campaign` de-duplicated *with* it, so two jobs differing only in the
> reported degrees were distinct jobs that wrote to the **same file** and
> mis-resumed off each other; the per-job `shape_signature` string likewise
> dropped the `q=` component that `index.json`'s group signature always
> carried. Both are now derived from one source
> (`Job::id()` / `Job::shape().to_string()`), and `CampaignSmokeValidation`
> pins injectivity (112 points), the backward-compatible default-list id, the
> distinct resume paths and an end-to-end two-degree-list campaign.
> Background: `docs/implementation/oc1_decision_brief.md` §4.4.

**Per-job JSON** (`"schema":"campaign_job/v1"`):

* `point`, `model_descriptor` (name, dimension, simplex counts, relation source),
  `shape_signature` (the **same string** as the job's group signature in
  `index.json`, `q=` component included), `lean`;
* `reports` — per reported degree with `d_q > 0`, the **full `HeckeReport`**:
  level (a) `Θ^{(q)}_flat`, level (b) `A^{(q)}(T_p)`, level (c) the certified
  primary decomposition. Written *first* and **streamed** (§7);
* `dim_H`, `objects` — the canonical objects with their FNV-1a-64 hashes (§8);
* `certify` — the block described in §3;
* `timings_s`, `peak_rss_mb` / `peak_rss_scope`, `status`;
* `"campaign_job_complete": true` — **the completion trailer**.

`resume = true` skips a job iff its file exists *and* its last 256 bytes contain
that trailer. A job that failed writes `false`, and a job killed mid-write has no
trailer at all — both are re-run. A failed job's file is rewritten from scratch
(header + error + `false` trailer) so it stays well-formed JSON.

**Resume semantics and the degree list.** The file whose trailer is inspected is
`jobs/<id>.json` with the id above, so resume is keyed on
`(n_sym, ℓ, p, r, degrees)` — the same tuple that makes two points distinct
jobs. Re-running a spec with a *different* `q` therefore re-runs the jobs
(different ids, different files) instead of silently accepting the other degree
list's output, and re-running a spec with the same `q` skips them as before.
Resume does **not** key on `certify`, `lean`, `level_a` or `theta_rank_max_dim`:
a completed file is accepted whatever those were, exactly as before.

**`summary.tsv`** columns:

```
index n_sym ell p r model status dim_H0 dim_H1 dim_H2
charpoly_A0 charpoly_A1 charpoly_A2 trace_A1 rank_A1
theta_flat_hash_q1 certify external time_s rss_mb file
```

`charpoly_A<q>` holds the **coefficients** of the characteristic polynomial of
`A^{(q)}(T_p)` (or of the recursion's `T_{p^r}` for `r ≥ 2`), **low → high
degree** (amendment A-N4), semicolon separated. Example rows from the mini
campaign of §9 (`ℓ = 134217757`, `p = 2`, `r = 1`):

| n_sym | dim H¹ | charpoly of `A^{(1)}(T_2)` |
|---|---|---|
| 8 | 1 | `134217244;1` → `X − 513`, and `513 = 1 + 2^9 = σ_9(2)` — the level-1 weight-10 Eisenstein eigenvalue |
| 16 | 3 | `100392429;130301210;134087740;1` |

---

## 5. The model descriptor (audit item 7.18 / plan Q8)

Until Phase 6 the pipeline pinned its base complex with the **literal** shape
test "7 vertices, 11 edges, 5 triangles, dimension 2". `Hecke/HeckeModelDescriptor.{h,cpp}`
turns that literal into a datum:

```cpp
struct SimplicialModelDescriptor {
    std::string name;                      // "sl2z_7vertex"
    std::string description;
    uint32_t dimension;                    // 2
    std::vector<uint32_t> simplex_counts;  // {7, 11, 5}
    std::string relation_source;           // "GenerateSL2ZRelationsWithGroupData"
    uint32_t num_degrees() const;          // dimension + 1
    bool matches(const SimplicialComplex&) const;
};
const SimplicialModelDescriptor& SL2Z7VertexModel();
const SimplicialModelDescriptor* FindModelDescriptor(const std::string& name);
void RequireModel(const SimplicialModelDescriptor&, const SimplicialComplex*, const char* who);
```

`HeckeOperatorOnK`'s and `HeckeCrossChecks`'s constructors now call
`RequireModel(SL2Z7VertexModel(), K(), "...")`, and `HeckeOperatorOnK` takes
`num_degrees_` from the descriptor instead of `K->get_dimension() + 1`. **The
predicate tested is exactly the predicate that was tested before**, so the change
is value-preserving — `GoldenRegressionValidation` under `GOLDEN_STRICT=1` is the
gate, and it is green (tier A 9446 failing 0, tier B 4603 mismatching 0). The
campaign driver asserts on the descriptor too and records it in every job file.

This is deliberately **not** a model abstraction layer: the SL(2,Z) 7-vertex
model is the only instance and the relation table is still
`GenerateSL2ZRelationsWithGroupData`. It is the single place "which model is
this?" is written down, so a refined model (the −I / odd-`n` gap,
`docs/KNOWN_ISSUES.md`) can be added as a second instance without hunting for
literals.

**Migrated at integration** (commit `3dce92e`, one line each): the same literal
test in `HeckeTauTable.cpp` and `SL2ZTessellationTables.cpp` now calls
`RequireModel(SL2Z7VertexModel(), &K, ...)` too, so no 7/11/5 literal survives
in the Hecke layer.

---

## 6. Element widths

| `ℓ` | pipeline | available |
|---|---|---|
| `< 2^32` | `uint32_t` instantiations | everything: `r ≥ 2` via `HeckeOperatorFamily`, level (c) decomposition + report, both external cross-checks |
| `≥ 2^32` | `uint64_t` instantiations | dims, `Θ^{(q)}_flat` hash (+ rank under the gate), char-poly / rank / trace of `A^{(q)}(T_p)`. **`r` must be 1**, and there is no level-(c) report or external cross-check: `HeckeOperatorFamily`, `HeckeModuleDecomposition`, `HeckeReport` and `HeckeCrossChecks` are the 32-bit instantiations. The JSON records `"n/a (ell >= 2^32: the cross-check layer is 32-bit)"`. |

The 64-bit point strings follow the golden harness's convention
(`n=<n> ell=<ℓ> [u64] p=<p> r=1`), so they are comparable with the golden
`HeckeExtendedRegimeValidation` cells.

---

## 7. Memory-lean mode

`lean = true` changes two things; **no computed value moves**:

1. **The O12(a) route-2 comparison is streamed.**
   `HeckeOperatorOptions::ScopedMemoryLean` makes `HeckeOperatorOnK::compute()`
   assemble route 2 **one block row at a time** and compare it against the
   corresponding row of the finished fused `Θ`, freeing as it goes, instead of
   holding a second complete `Θ`. `blk::equal` is block-local and the row grids
   agree, so the verdict over all rows *is* the whole-matrix verdict — every
   entry is still compared and a mismatch throws the same message.
2. **Level (a) is never materialised.** Both its FNV hash and its JSON are read
   block-row-wise off `HeckeOperatorOnK::Theta_block(q)` through the new
   `hecke::LevelARowSource` pull interface, so the `(N_q·d_V)²` `FlatMatrix` of
   `get_Theta_flat_matrices()` is never built (audit item 7.19).

Measured on the default `RelWithDebInfo` build, `ℓ = 134217757`, `p = 2`,
`r = 1`, `certify = none`, `level_a = auto` (so level (a) *is* in the JSON in
both modes):

| job | peak RSS, resident | peak RSS, lean | Δ | time |
|---|---|---|---|---|
| `n_sym = 192` | 316.9 MB | 309.1 MB | −7.8 MB (−2.5 %) | 2.86 → 2.80 s |
| `n_sym = 256` | 477.1 MB | 445.5 MB | −31.6 MB (−6.6 %) | 6.34 → 6.11 s |

The saving is exactly the `(N_q·d_V)²` term: at `n_sym = 256`, `Θ^{(1)}_flat` is
`2827² × 4 B = 32 MB`. That term is the one that grows as `n²` against a total
that grows as `n²`-ish but from a much larger constant, so the *relative* saving
climbs with `n`: at `n_sym = 1000`, `Θ_flat` alone is `485 MB` for `q = 1` and
≈ 780 MB across the three degrees, against the ≈ 5 GB projected in
`00-implementation-plan.md` §12. **The lean and resident runs produce byte-identical
objects and byte-identical level-(a) JSON** — asserted by
`CampaignSmokeValidation` and re-verified here at `n_sym = 256`
(2827 × 2827 level-(a) rows, identical).

Also relevant at scale, and independent of `lean`: `level_a = never` (or the
`auto` size gate) drops level (a) from the report entirely, and
`theta_rank_max_dim` (default 2048) suppresses `rank(Θ_flat^q)`, which is an
`O((N_q d_V)^3)` elimination.

---

## 8. Hashing, and the relation to the golden harness

The campaign uses **byte-for-byte the FNV-1a-64 of `Golden/GoldenHarness.cpp`**
(offset `0xcbf29ce484222325`, prime `0x100000001b3`; `rows`, `cols`, then every
entry widened to `uint64` in row-major order; for a scalar invariant the value
itself), **and the golden point / object vocabulary**:

| point string | objects |
|---|---|
| `n=<n> ell=<ℓ>` | `num_degrees`, `dim_H^q` |
| `n=<n> ell=<ℓ> p=<p> r=1` | `Theta_flat^q`, `rank_Theta_flat^q`, `charpoly_A(T_p)^q`, `rank_A(T_p)^q`, `trace_A(T_p)^q`, `A(T_p)^q`, `decomp_A(T_p)^q_invariants`, `decomp_A(T_p)^q_certify` |
| `n=<n> ell=<ℓ> p=<p> r=<r>` (`r ≥ 2`) | `charpoly_A(T_p^r)_rec^q`, `rank_…`, `trace_…`, `A(T_p^r)_rec^q` |

So a campaign point that also lies on the golden grid **must** reproduce the
frozen `GoldenReference.inc` hash. `CampaignSmokeValidation` asserts exactly
that: on its 20-job spec it finds **548 shared `(point, object)` keys and 0
mismatches**.

Note that an `r ≥ 2` job runs the `r = 1` pipeline as well (that is what produces
`Θ` and the C3–C5 certificates), so its file carries the `r = 1` objects too.

---

## 9. Validations

| name | tier | what it pins |
|---|---|---|
| `CampaignSmokeValidation` | standard (~0.5 s) | a 20-job spec run through the driver equals **20 individual single-job campaigns** hash for hash (548 objects); every shared `(point, object)` key matches `GoldenReference.inc`; groups are shape-uniform and `ℓ`-sorted; `plan_campaign` is deterministic; job files carry the trailer; `index.json` / `summary.tsv` are well-formed; **memory-lean == resident on every object**; and (since 2026-09-16) the **job-id / shape-signature regression** of §4: injectivity on a 112-point grid that varies the degree list, the unchanged default-list id, distinct resume paths, and a two-degree-list campaign that writes four files and then resumes all four |
| `CampaignCertificateValidation` | fast | `sampled(every 3)` parses; the in-process certificates C3–C6 ran on **every** job (counted); the external checks ran on exactly the sampled subset and the JSON records mode, stride and the per-job decision; `resume` skips all 6 completed jobs and then re-runs exactly the one whose trailer was truncated |
| `HeckeExtCampaignValidation` | standard (~2 s) | §14: the per-cell grouping as a property of `plan_campaign()` alone; **`ext = false` byte-identity** (the frozen 21-column `summary.tsv` header, the id `n16_ell5_p2_r1` and the default shape signature as literals, and no `extensions` key anywhere); the attachment in both files; **determinism across four `jobs × threads` splits** — ext record files byte-identical, `summary.tsv` byte-identical outside its two timing columns; the record-level `u_ell` **resume**; and the state-sidecar contract |
| `CampaignRingValidation` | standard (~1 s) | §15 (slot-9 WP-8): a campaign under `coefficient_ring = Z/ell^<k>` — the E8 points' objects **equal the frozen golden entries** (a set equality with the 4a set of each point), the `(e)` table literally, the weight-12 free characteristic polynomial at `(10, 691)` and at the `uint64_t` cell `(10, 134217757)`, `ell ∈ {2, 3}` against the frozen O7 rows with the three refusals, `r = 2` refused at the job loop, the record's member order, `summary.tsv`'s 21 + 15 columns, `index.json`'s key, `resume`, `jobs = 1` == `jobs = 2`, and the spec-validation refusals |
| `HeckeExtDeterminismValidation` | standard (~12 s) | the FNV-1a-64 of the whole `hecke_ext/v2` record text (unsplit **and** both per-sign records) on `(10, 691)`, `(34, 5)`, `(24, 7)` under `ENGINE_THREADS ∈ {1,4,16,32} × ENGINE_BATCH ∈ {0,1}`, plus `(128, 5)` on the threads `{1, 16}` arms and two `device = gpu` arms where a device exists |

Gates run on this branch (default `RelWithDebInfo`): `--all` green,
`GOLDEN_STRICT=1 GoldenRegressionValidation` tier A 9446 / 0, tier B 4603 / 0,
`HeckeEndToEndValidation`, `HeckeCrossCheckValidation`,
`HeckeThetaBlockValidation` all PASS.

---

## 10. Worked example specs for the plan's three campaign targets

Wall-clock estimates from this branch's measurements: the 32-bit total time fits
`t(n) ≈ 1.2·10⁻⁷ · n^2.91 s` on `{128, 192, 256}` at `ℓ ≈ 2^27`, `p = 2`, `r = 1`,
level (a) on. (The `--bench` exponent of 2.56 is measured over `{64, 96, 128}`;
the campaign's is steeper because it also writes the `n²`-sized level-(a) JSON.
Drop `level_a` and the exponent falls back.) Single-threaded, one core.

### (a) The broad sweep: `n_sym ≤ 200` × many `ℓ`, `T_2`

```
name    = t2_broad
output  = out/t2_broad
certify = sampled(every 25)
lean    = true
resume  = true
n_sym   = 0..200 step 2
ell     = 2,3,5,13,691,10007,134217757
p       = 2
r       = 1
```

**707 jobs, ≈ 9.4 min.** (`step 2` because odd `n` vanishes on this model — the
−I / odd-`n` gap.) 101 shape groups of 7 jobs each: every group is one `n_sym`
with seven moduli, i.e. exactly the batch the Phase 4 engine wants.

### (b) The deep sweep: `n_sym` up to ~1000 at `ℓ ≈ 2^27`, `T_2`/`T_3`/`T_5`

```
name    = deep_2_3_5
output  = out/deep_2_3_5
certify = none
lean    = true
level_a = never
theta_rank_max_dim = 512
resume  = true
n_sym   = 0..1000 step 2
ell     = 134217757
p       = 2,3,5
r       = 1
```

**1503 jobs; ≈ 36 h single-threaded**, of which the single `n_sym = 1000`,
`p = 2` job is ≈ 5.5 min — comfortably inside the plan's "one `n_sym = 1000`,
`ℓ = 134217757`, `T_2` run end-to-end ≤ 60 s"? **No**: 5.5 min is 5.5× over that
exit criterion, which is a Phase 4/5 (tape + GPU) target, not a Phase 6 one. The
campaign driver is what will *measure* it. `resume = true` is essential here —
this is a multi-day run.

### (c) The first `ℓ < 2^64` results, moderate `n_sym`

```
name    = u64_first
output  = out/u64_first
certify = none
lean    = true
level_a = never
n_sym   = 0..128 step 2
ell     = 8589934627,68719476767,1099511627791,2305843009213693951
p       = 2
r       = 1
```

**260 jobs, ≈ 13 min.** The 64-bit path fits `t(n) ≈ n^2.77` with a constant
≈ 80× the 32-bit one (measured: `n_sym = 64` takes 1.68 s against 0.021 s at
`ℓ = 134217757`) — the `unsigned __int128` accumulation has no AVX-512
microkernel. Reported objects are the reduced 64-bit set of §6.

---

## 11. What the tape engineer changed (Phase 6 Part A) — done

Every item of this section's original backlog is closed; §12 is the result.

* `RunJobGroup()` was the only place changed, exactly as §2 promised.
* `threads` is no longer reserved: it is the number of engine workers **per
  concurrent job**, and the new `jobs` key is how many jobs of a group are in
  flight. `index.json` records both plus `per_job_pools`.
* `HeckeOperatorOptions::ScopedMemoryLean` had already become thread-local in
  Phase 4 Stage B, together with the other consumer options; the driver
  installs the launching thread's whole context on every job thread through
  `engine::tape::capture_thread_context()`, so nothing has to be re-listed here
  when a new scoped option appears.
* The per-job `peak_rss_mb` reset is **dropped** when jobs run concurrently
  (`/proc/self/clear_refs` resets the *process* high-water mark, so with
  several jobs in flight it would attribute one job's peak to another).
  `"peak_rss_scope"` then reads `"process-concurrent"` and the number is the
  process `VmHWM` observed at that job's end; `index.json` gained the
  campaign's own `peak_rss_mb`. **Run a group with `jobs = 1` when a genuine
  per-job figure is what is wanted** — that is what `large_n.spec` does.

---

## 12. The 2-level split (`jobs` × `threads`)

A shape group's jobs share `(n_sym, p, r, degrees, model)` and differ only in
the modulus, so they are independent pipelines of *identical shape*: the group
is exactly the unit to run concurrently (audit §4 axis (e)). Three things make
that safe and one makes it fast.

**Thread context.** The consumers' scoped options (`ScopedMemoryLean`, the
legacy arms, `elim::ScopedLegacy`) are `thread_local`, so a job thread would
otherwise run with the *defaults* rather than the campaign's settings. The
driver installs the launching thread's context on every job thread through
`engine::tape::capture_thread_context()` — the engine's own propagator
registry, the same one `run_concurrently()` uses, not a private copy.

**The τ / coset lock.** `HeckeTauTable`'s build is first-match-wins over a
fixed transporter order and drives the **non-atomic** global `PredicateStats`
counters (audit §6.5, hazards 1–3). Every `HeckeCosetTables` /
`HeckeTauTable` / `SL2ZTessellationTables` construction in the driver therefore
runs under `hecke::tau_construction_mutex()` — the *same* process-wide lock
`HeckeOperatorFamily::build_pipelines()` has always held for its phase A, moved
from that file's anonymous namespace into `HeckeOperatorFamily.h` so there is
one lock in the process and not two. Everything downstream of it
(`compute_cohomology`, `compute()`, the report) is a pure function of per-job
objects and runs concurrently. A job's `t_cosets` therefore also carries its
wait for that lock.

**Determinism.** Results land in a pre-sized slot vector indexed by the job's
position in the group and are appended in **group order**, so the job order,
`index.json`, `summary.tsv` and every hash are independent of how the work was
scheduled. `jobs == 1` takes a separate branch that is the pre-Phase-6 loop
unchanged, down to the order its progress lines print.

**Per-job engine pools — the speed.** `ThreadPool::parallel_for()` serialises
concurrent callers on one region mutex, so *N* job threads sharing one pool
serialise all of their engine work. `engine::tape`'s consumer-pool override is
therefore `thread_local` (with a `register_thread_context()` capture next to
the existing `elim::ScopedLegacy` one, so a job's inner degree fan-out stays on
that job's pool), and each job thread installs its own `ThreadPool(threads)`.
The driver **probes** whether the override is thread-local rather than assuming
it, and falls back to sharing the process pool — correct either way, just
slower — reporting `per_job_pools` in `index.json`.

### The measurement

297 jobs — `n_sym = 0..64 step 2` × `ℓ ∈ {2,3,5,7,11,13,691,10007,134217757}`,
`p = 2`, `r = 1`, `lean`, `certify = none`, `level_a = never` — on the default
`RelWithDebInfo` build, 32 hardware threads.

| `jobs` × `threads` | wall | jobs / minute | peak RSS |
|---|---|---|---|
| 1 × 1 (the sequential driver) | 12.62 s | 1 412 | 126 MB |
| 1 × 32 | 13.54 s | 1 316 | 120 MB |
| 32 × *(shared process pool)* | 7.40 s | 2 409 | 255 MB |
| 2 × 16 | 7.31 s | 2 437 | 294 MB |
| 4 × 8 | 4.21 s | 4 230 | 389 MB |
| 8 × 2 | 2.56 s | 6 960 | 377 MB |
| 16 × 4 | 2.12 s | 8 389 | 507 MB |
| 32 × 1 | 1.80 s | 9 892 | 261 MB |
| 32 × 2 | 1.81 s | 9 830 | 420 MB |
| **16 × 2** | **1.75 s** | **10 209** | 420 MB |
| 64 × 1 | 2.04 s | 8 732 | 257 MB |

Read the third row against the last: **32 concurrent jobs on the *shared* pool
buy 1.7×, on private pools 7.2×.** That row is the whole argument for the
thread-local override — it is `region_mutex_`, not the arithmetic, that was the
ceiling.

Read the second row against the first: at `n_sym ≤ 64` the *intra-job* engine
parallelism is worth nothing at all (13.54 s at 32 threads against 12.62 s at
one). These matrices are small; the parallelism that pays is across jobs. That
is why the optimum sits at the far end of the table, and why `threads` should
stay at 1–2 for a broad sweep and go up only for the large-`n_sym` runs, where
a single job is big enough to fill the machine on its own (§13).

**The recommended split is `jobs = 16`, `threads = 2` for a sweep whose `n_sym`
stays small, and `jobs = 32`, `threads = 1` once it reaches into the hundreds.**
The two are within 3 % of each other here, but on the full `n_sym ≤ 200`
exit-criterion sweep the ordering reverses — `32 × 1` runs it at 1 085 jobs per
minute against `16 × 2`'s 917 — because at `n_sym ≈ 200` a single job already
saturates its own memory bandwidth and one more concurrent job buys more than
one more thread inside a job does. `sweep_full.spec` / `sweep_sampled.spec`
therefore ship `16 × 2` and `exit_t2.spec` ships `32 × 1`, and the largest runs
(`large_n.spec`) use `jobs = 1` so that peak RSS is per job. The *parsed* default
stays `jobs = 1` so that a spec which says nothing is the sequential,
trivially-reproducible driver; every shipped spec in
`docs/matrix-engine/results/specs/` sets the split explicitly, and
`--jobs` / `--threads` override it from the command line.

**`ENGINE_DEVICE=hybrid`** on the same 297 jobs: **2.76 s / 6 454 per minute**,
i.e. 1.6× *slower* than the CPU arm. Expected, and not a defect: at `n_sym ≤ 64`
every GEMM is far below the size at which a PCIe round trip pays (`04 §6.3`),
and 16 concurrent jobs then contend for one device. The device arm is for the
large-`n_sym` runs of §13, not for a broad sweep.

---

## 13. Large `n_sym`: what it costs

`jobs = 1` (so `/proc/self/clear_refs` gives a genuine per-job peak), `lean`,
`level_a = never`, ℓ = 134217757, default `RelWithDebInfo` build, 32 threads.
`certify` is `full` at `n_sym ≤ 600` and `none` above.

| `n_sym` | `p` | dim H¹ | certify | time | peak RSS |
|---|---|---|---|---|---|
| 400 | 2 | 67 | full | 43.2 s | 2 216 MB |
| 400 | 3 | 67 | full | 79.8 s | 4 261 MB |
| 400 | 5 | 67 | full | 186.8 s | 7 536 MB |
| 600 | 2 | 99 | full | 102.6 s | 5 102 MB |
| 600 | 3 | 99 | full | 198.4 s | 9 349 MB |
| 600 | 5 | 99 | full | 388.2 s | **16 581 MB** |
| 800 | 2 | 133 | none | 25.4 s | 2 671 MB |
| 800 | 3 | 133 | none | 26.1 s | 2 863 MB |
| 800 | 5 | 133 | none | 25.5 s | 2 864 MB |
| 1000 | 2 | 167 | none | **48.5 s** | 4 269 MB |
| 1000 | 3 | 167 | none | 54.0 s | 4 450 MB |
| 1000 | 5 | 167 | none | 48.8 s | 4 506 MB |

Two things stand out.

**`certify = full` is the whole cost above `n_sym ≈ 400`, and it is what makes
the run grow in `p`.** Compare `n_sym = 800, p = 5` (25.5 s, 2.9 GB) with
`n_sym = 600, p = 5` (388 s, 16.6 GB): the *smaller* problem with the external
cross-checks on is 15× slower and 6× larger. `HeckeCrossChecks` builds the
classical `α`/`β`/`ω` three-map factorisation, whose intermediates scale with the
coset count `p + 1`; the operator itself is nearly flat in `p` (48.5 / 54.0 /
48.8 s at `n_sym = 1000` for `p = 2 / 3 / 5`). The plan's advice to sample the
external checks at scale is not a convenience — past `n_sym ≈ 400` `full` is
what will exhaust the machine, and it is the reason `large_n_sampled.spec`
exists as a separate campaign.

**`n_sym = 1000` fits the Phase 6 exit criterion.** 48.5 s end to end — the
triangulation, `compute_cohomology()`, the coset and τ tables with their exact
certification, `Θ^{(q)}` for all three degrees with the two routes compared over
every entry, the exact `Θ_eq` residual, `A^{(q)}(T_2)`, and the certified primary
decomposition — against the criterion's 60 s. `Θ^{(1)}_flat` alone would be
`11011² × 4 B = 485 MB`; `lean` never materialises it.


---

## 14. The extension record on the campaign (`ext = true`)

*hecke-extensions slot 5, WP-2 / phase E2 cont.; [X] §1.5, §1.3.1 R3.3 item 4.*

**`ext = false` is the default and with it nothing below happens.** Every byte
of `index.json`, `summary.tsv` and every job file is what the pre-WP-2 driver
wrote — pinned by `HeckeExtCampaignValidation` arm 2 against the frozen
21-column header, the shipped id `n16_ell5_p2_r1` and the default shape
signature, and measured once against a binary built from the package's base
commit (identical modulo the timing and RSS fields).

### Per cell, not per job

A campaign job is `(n_sym, ℓ, p, r)`; the extension record is a property of
the **cell** `(n_sym, ℓ)` ([XA m14]). `plan_campaign()` therefore marks the
cell's **first job in plan order** as its `ext_owner` and gives every job of
the cell the same family, `spec.family ∪ {p of the cell's jobs}`, ascending and
duplicate-free. Both assignments are pure functions of the spec, so the
`jobs × threads` determinism contract (§12) is untouched.

The **shape signature** gains ` ext=S0=<primes>` when `ext = true` — it is a
campaign-wide constant, so it never splits a shape group. **`Job::id()` does
not**: the extension keys cannot change any object the *job* computes, only
the record the cell's owner attaches.

### Where the work runs — and why not on a job thread

The pass runs **before the job loop**, never on a job thread, so the ext half of
the output is independent of the `jobs × threads` split **by construction**.

Until slot 8 it ran **sequentially on the campaign's main thread**:
`HeckeExtDriver`'s `Impl` constructor builds a `SimplicialComplex` and an
`SL2ZTessellationTables` **outside** `hecke::tau_construction_mutex()`, and that
build — like `HeckeInvolution` and `HeckeBoundaryDatum` — drove the non-atomic
global `PredicateStats` (audit 02 §6.5 hazard 3), so two drivers could not run at
once. Holding the lock around `HeckeExtDriver::run()` is still not an option (the
driver re-enters it in `HeckeSturmSweep`'s streamed route and `HeckeBoundary`, and
`std::mutex` is not recursive).

### The parallel pass (`ext_jobs`; hecke-extensions slot 8, WP-6)

**Slot 8 removed the hazard instead of the lock.** `PredicateStats` is
`thread_local` (`Hecke/Predicates.h`, "PER THREAD": every reader asserts its
counts on the thread that made the calls, so every asserted count is
unchanged), and the engine's `elim_stats` / `gemm_stats` diagnostic counters are
relaxed atomics. A cell's state is otherwise its own — one driver owns its `K`,
its model, its cohomology and its family — and the coset / τ constructions keep
their lock, held by the code that builds them, exactly as before. So with
`ext_jobs = J > 1`:

* **every cell is decided first**, in plan order (the placeholder for `ℓ ≥ 2^32`
  and the record-level `u_ell` resume below) — a refusal therefore throws
  before any engine runs;
* the cells that need the engine run on **`J` worker threads**, each with its
  own engine pool of `threads` workers (the job loop's model, §12; `threads = 0`
  shares the process pool, which serialises the workers' engine regions — correct,
  but slow);
* every worker first installs the launching thread's **thread context**
  (`engine::tape::capture_thread_context()`): the **mathematical settings**
  among it — a worker started any other way would silently run at the defaults,
  which a default-settings byte identity cannot see — memory-lean, the legacy
  arms;
* **admission**: a cell starts only while the sum of the running cells' predicted
  memory stays `≤ ext_memory_mb`. A cell's prediction is a floor of
  `kExtCellFloorMb = 512` MB plus, when `U_ℓ` is admitted, the frozen `U_ℓ` RSS
  model (`HeckeUEllBudget.h`). A cell above the whole cap runs when nothing else
  does, so the pass never stalls;
* **order**: longest processing time first — the `U_ℓ` cells by predicted MB
  (linear in the coset count `ℓ + 1`), then the rest by `n` descending, then the
  plan index — so the pass wall approaches the slowest cell;
* after each cell its worker calls the WP-5 release
  (`ReleaseEngineProgramCaches(kCellLoopReleaseThreshold)`), memory-safe while
  other workers run;
* the result is assembled in **plan order**: `pass.cells` is an ordered
  `std::map`, the counters and `force_rerun_job_ids` follow the plan, and the
  verbose per-cell lines are buffered and printed in plan order.

A cell is a pure function of `(n_sym, ℓ, family, spec, settings)`, so **every
record, `analysis.txt`, `summary.tsv` and `index.json` is byte-identical to the
serial pass's outside the timing and RSS fields** — `HeckeExtCampaignValidation`
arm 10 at `ext_jobs ∈ {1, 2, 4, 16}`, under a non-default setting (`u_ell = off`,
where both runs must also differ from the default one), under a cap that forces
one cell at a time, and on a parallel `resume`. `ext_jobs = 1` is the sequential
pass, cell by cell on the calling thread.

**The `EXT_PASS` line.** A verbose campaign with `ext = true` prints, after the
`ext:` summary,

```
EXT_PASS wall_s=<f> jobs=<J> cells=<n> engine_cells=<n> ran=<n> reused=<n> resumed=<n> failed=<n> peak_rss_mb=<f> memory_cap_mb=<n> peak_admitted_mb=<f> peak_running=<n> per_worker_pools=<0|1>
```

`wall_s` is the pass's wall (the `ext.wall_s` of `index.json`), `peak_rss_mb` the
process VmHWM at the end of the pass (the pass runs first, so it is the pass's
peak). It is what the T-P measurement reads
(`docs/matrix-engine/tools/ext_pass_tp.sh`).

### The device worker (`ext_gpu`; hecke-extensions slot 8, WP-6b, optional)

**Off by default, and it stays off by default.** `ENGINE_DEVICE=gpu` is 1.4–3.3×
*slower* than the CPU on the pipeline's own shapes (the elimination driver
records one program per panel), and an ext cell's cost is dominated by
host-serial work the device never touches (the `U_ℓ` coset tables, route 2, the
Sturm sweeps; WP-6 report §8). What the mode offers is the otherwise idle device
taking **whole cells** while every CPU slot is busy — a scheduling mode, not an
arithmetic path. Under `ext_gpu = on`:

* the parallel pass runs **one extra worker** beside the `ext_jobs` CPU workers
  (even at `ext_jobs = 1`), on its own engine pool of `threads` workers, with a
  **thread-local device override** installed after the captured thread context
  (`engine::tape::ScopedThreadDevice(Gpu)`, `ENGINE_API.md` §10): its programs —
  and those of every task thread it launches — are compiled with the `gpu`
  policy, while **every CPU worker installs `ScopedThreadDevice(Cpu)`**, so it
  compiles for the CPU whatever `ENGINE_DEVICE` says. `ENGINE_DEVICE` itself is
  not read or changed. Only `gpu`, never `hybrid`: the two share
  `pass_options_fingerprint()`'s device bit, and the program cache must keep
  CPU- and GPU-compiled programs apart (it does: bit 128);
* **its rule**: the **cheapest** pending cell (the tail of the LPT order — so the
  cells without `U_ℓ` first, then the cheapest `U_ℓ` cells), **only while every
  CPU slot is busy**, and only while its modelled GPU cost
  (`kExtGpuCostFactor = 3.3` × the CPU prediction, the pessimistic end of the
  measured factor) does not exceed the pending work per CPU slot — so, by the
  model, the slower device never becomes the pass's tail. Its cell counts
  against `ext_memory_mb` like any other, and must fit a **device-memory cap**
  read from the device when the pass starts (`kExtGpuDeviceCapFraction = 0.8` of
  its free memory). `ext_gpu_cells` replaces the rule by an explicit list;
* **no device, no mode**: without a usable device (or under
  `ENGINE_CUDA_DISABLE=1`), `on` prints one line — `ext_gpu = on: <reason>;
  running the CPU-only pass` — and runs WP-6's pass. `force` runs the worker
  anyway, its GPU-assigned nodes falling back to the CPU inside the executor:
  the plumbing test (the `CheckThread` run), never needed in production;
* **`off` installs nothing** — no override, no tally, no CUDA probe — and its
  `EXT_PASS` line is WP-6's byte for byte.

**Why no value can move.** A device result is the same bytes as the CPU result
by construction (the CUDA layer is exact-integer; `ENGINE_API.md` §11), every
program is keyed by its device, and which worker ran a cell is written into **no
record, no `index.json` and no `summary.tsv`**: only into the `EXT_PASS` line and
the verbose `EXT_GPU_CELLS count=<k> <n:ell> …` line (the assignment log, plan
order). `HeckeExtCampaignValidation` arm 11 checks `force` (every box) and `on`
(with a device) against the serial CPU-only pass byte for byte, the listed cells
on the device worker, the fallback, a non-default setting, and — from the
programs the workers actually ran — **zero GPU-assigned nodes on every CPU
worker** and ≥ 1 on the device worker. `docs/matrix-engine/tools/ext_pass_identity.sh`
takes `--jobs 1,2+gpu,4+force` for the same comparison on any spec, and
`ext_gpu_timing.sh` times a spec with and without the worker (indicative only).

Under a non-default `ext_gpu` the `EXT_PASS` line gains

```
 ext_gpu=<on|force> gpu_worker=<0|1> gpu_cells=<n> gpu_programs=<n> gpu_nodes=<n> cpu_programs=<n> cpu_gpu_nodes=<n> device_cap_mb=<f> [gpu_fallback="<reason>"]
```

(`gpu_nodes` / `cpu_gpu_nodes`: the GPU-assigned nodes in the programs the device
worker / the CPU workers ran).

### Two appearances of one record

The pass writes the record **once**, standalone, to
`<output>/ext/hecke_ext_ell<ℓ>_n<n>[_x<16 hex>].json` through
`hecke_ext::WriteHeckeExtReport` — the only form that has a *stem* and can
therefore write the R3.1 item-6 **state sidecars** beside it. The owner job's
JSON then carries those same bytes verbatim under `"extensions"`, followed by
`"extensions_file"` naming the file the sidecars' relative paths are taken
from. The record file name carries **no settings fingerprint** — it is the
cell's persisted state, and the resume path's whole job is to read the
previous budget's record and continue it, which a fingerprinted name would
hide from its successor.

**It does carry the `family` identity** (hecke-extensions slot 6, WP-6 / E2
close-out; [WP5-2] finding 3: "`ext`, `family`, `sign`, `ext_groups` do not
fingerprint, so two campaigns differing only in `family` share the ext record
file and its resume key"). The optional `_x<16 hex>` suffix is the FNV-1a-64
of `ExtSpec::signature_tag()` (the `S0=...` string that also extends the
**shape signature**, §2 above) — present whenever `ext = true`, since
`signature_tag()` is non-empty exactly then. A resume under a *different*
`family` therefore computes a different suffix, finds no file, and **re-runs
the cell** instead of silently reusing a record built for a different `S_0`.
`sign` and `ext_groups` are **not** part of this tag: `sign` selects which
record the *same* `(n_sym, ℓ, family)` cell writes into that one file
(`RunExtPass`), and a resume asking for the cone over a record built without
it is caught by the separate `pair_available` check (below), not by the file
name. This closes the hazard `family` demonstrated; it does not fingerprint
`Job::id()` — no published campaign ever carried `ext = true` ([WP5-13] §7),
so the fix is free now and would be costly once one did.

### `summary.tsv`

Eight columns are **appended** when `ext = true` — `ideals`, `max_embdim`,
`max_loewy`, `nonsplit_ideals`, `nonlocal_ideals`, `sturm_B_prime`,
`ext_certificate`, `ext_final` — so the pinned default form (21 columns,
`time_s` at index 18 and `rss_mb` at 19) is untouched. Only the cell's **owner
row** carries values; every other row prints `-`, as a skipped job's row
already does. [X] names the columns without defining two of them; this driver
defines them in band:

* `max_loewy` — the longest Loewy series of any module of any ideal;
* `nonsplit_ideals` — the ideals carrying a module of Loewy length `≥ 2`, i.e.
  a **non-semisimple** block. At `(10, 691)` the one ideal has `loewy = [2, 1]`,
  which is the nonsplit Eisenstein/cuspidal gluing of [E] `cl:ramanujan`.

### The record-level `u_ell` resume ([X] §1.3.1 R3.3 item 4)

With `ext = true` and `resume = true` the pass reads each cell's persisted
record, **verifies every `state_ref` sidecar it names** (present, and
FNV-1a-64 of the bytes as recorded — a missing or altered one is refused by
name), and then:

| persisted state | the spec's `u_ell` budget | what happens |
|---|---|---|
| included, or no `resumable` | any | **reuse** — a strict no-op; the owner job is skipped |
| refused at `B` | `off` | reuse |
| refused at `B` | `< B` | **refused by name**: `resume: u_ell budget below reached state` |
| refused at `B` | `== B` | reuse |
| refused at `B` | `> B` | **resume**: the driver runs Stage 1 under `B` and then `resume_u_ell(new)` — slot-4 WP-2's own semantics, so the continuation is the run the enlarged budget would have produced from the start |

Whenever the engine ran for a cell (fresh **or** resumed) the owner job is
re-run even if `resume` would have skipped it, so the job file that carries
`"extensions"` is rewritten with the record. A cell the pass *reused* sets no
such flag, so an unchanged campaign still skips everything.

**Measured** (`HeckeExtCampaignValidation` arm 5, `(10, 691)`): a campaign at
`u_ell = budget_mb=64` refuses `U_691` (≈ 104 MB predicted) and records one
`resumable` with `budget_history = [64]` and `resumable_items = 1`; a resume at
the shipped default reproduces a **fresh `u_ell = auto` campaign's record byte
for byte**, fingerprint included.

### What is *not* here

No golden object. The extension record's golden entries are WP-3's single
add-only emission; this driver's output is compared against campaign output and
against literals only.

---

## 15. Campaigns over `Z/ell^k` (`coefficient_ring`, `hecke_ring_report/v1`)

*(hecke-extensions slot 9, WP-8 — C5c, decision 6 (A); binding text [E]
`sec:ring` (g), members (g1)–(g16); code `Campaign/CampaignRing.{h,cpp}`.)*

### The key

`coefficient_ring` is a registered **mathematical setting**
(`Hecke/HeckeSettings.h`), so a spec sets it like any other:

```
coefficient_ring = Z/ell^2      # or Z/ell^<k>, 2 <= k <= 63; the default is F_ell
n_sym = 6,16,30,60
ell   = 5
p     = 2,3
r     = 1
```

The value is `F_ell` (the default) or `Z/ell^<k>`: `ell` is the **literal
token** — the prime is each job's own. `Z` and `Z/<m>` are refused inside
`MathSettings::set()`, i.e. as an ordinary spec error.

### It changes no id at the defaults

A fingerprint-`0` campaign (every spec that does not name the key, or names
`F_ell`) never reaches the ring code: its job files (`campaign_job/v1` with
their `hecke_report/v2` reports), `summary.tsv` (21 columns) and `index.json`
are **byte for byte what they were**, and so are every job id, file name and
shape signature. Proven for slot 9 WP-8 by running a reduced sweep, a
`level_a = always` resident spec and `ext_compare_mini.spec` on the base and
the new binary (identical after blanking the timing / RSS numbers; the ext
records raw-identical) and by `--dry-run` diffs of all seven shipped specs.

Under `Z/ell^<k>` the fingerprint is non-zero, so — by the existing rule of §4 —
every id carries `_s<16 hex>` (`n6_ell5_p2_r1_s2e3e46911970e56a` under
`Z/ell^2`) and every shape signature ` s=<16 hex>`. There is no new id rule.

### What is refused at spec validation (before any job runs)

* `ext = true` under a non-default ring: the extension record is `F_ell`-only
  ([E] `sec:ring` (b4)). `not_implemented_in_this_build: campaign spec <file>:
  coefficient_ring=Z/ell^2 is not honoured in this build for the ext pass ...`;
  `--campaign` exits 1 and creates no output directory.
* a grid cell with `ell^k >= 2^64` (outside ENGINE_API.md §13), naming the cell
  (`... at the grid cell (n_sym = 10, ell = 4294967311) of the section at line 3
  ...`).

No refusal ever follows a job that has run. `ell^k < 2^32` runs the `uint32_t`
instantiation, `2^32 <= ell^k < 2^64` the `uint64_t` one.

### The job file: `hecke_ring_report/v1`

`jobs/<id>.json`, one JSON object, **instead of** `campaign_job/v1`, members in
this order:

| member | content |
|---|---|
| `schema` | `"hecke_ring_report/v1"` |
| `job_id` | `Job::id()`, with its `_s` suffix |
| `point`, `model_descriptor`, `shape_signature` | as in `campaign_job/v1`; `point.degrees` is the reported selection |
| `coefficient_ring`, `modulus`, `ladic_level` | `"Z/ell^<k>"`; `ell^k` as a **decimal string**; `K = k` |
| `settings` | `MathSettings::to_json()` with the non-zero `fingerprint` |
| `certify` | `{"mode": <the spec's certify text>, "applicable": false}` — every external cross-check is a field route |
| `degree_fields` | `{q_max: 2, truncated: false, q_max_source: "derived", degrees: [0,1,2]}` on the model |
| `kmode` | `certified` / `uncertified` / `not_applicable` (at `ell ∈ {2, 3}`, and at `ell >= 5` off the K-mode's range `n > 0` even); not a refusal |
| `cohomology` | per reported `q`: `{q, length, invariant_factors}` (exponents, descending; `[]` = zero module). **No member is a dimension** |
| `ladic` | `ell >= 5`, `n > 0` even: `{r_K: [r_K(d^0), r_K(d^1)], certified, type}` when certified (`type` per `q`: `{q, free_rank, torsion}`), `{r_K, certified: false, state}` otherwise — `state` = `{kind: "ladic_level", budget: {K}, reached: {r_K0, r_K1}, need: {r_K0, r_K1}, complete: false}`; its continuation is a fresh campaign at a larger `k`, never `resume` |
| `bockstein` | `ell >= 5`: `{bockstein_rank_0, higher_torsion_count, dim_H0_F_ell}` from the cell's `Z/ell^2` object and the `F_ell` object (each built with its own ring installed for its construction only); the bookkeeping identity is asserted, and `higher_torsion_count == #{e_i >= 2}` wherever the K-mode certifies |
| `hecke` | `ell >= 5`, `r = 1`, `1 ∈ point.degrees`: `{p, r: 1, charpoly_free: {precision: K - e_max, coeffs: [low .. high]}}` — the coefficients as **decimal strings** (they may exceed `2^53`, like `modulus`), `charpoly_free` only when certified; `p = ell` is `U_ell` |
| `objects` | `{name, tier, rows, cols, fnv1a64}` for every (d) object present, under its golden name and recipe, in (e)'s order: `lengths_H^q`, `invariant_factors_H^q`, `r_K(d^0)`, `r_K(d^1)`, `ladic_type_certified`, `ladic_type^q` (certified), `bockstein_rank^0`, `higher_torsion_count`, `charpoly_A(T_p)^1_free_p<p>` (certified), `red_H^q` (tier B). At an E8 point of [E] (e) each equals the frozen golden entry (`CampaignRingValidation` arm (A)) |
| `refusals` | `{part, who, message}` per refused part, the message tagged `not_implemented_in_this_build:`; empty when nothing was refused |
| `status` | `ok`, `ok_partial` (computed, with at least one refusal), `failed` (then also `error`) |
| `timings_s`, `peak_rss_mb`, `peak_rss_scope` | as in `campaign_job/v1` (same nine timing keys: `cosets` / `tau` / `theta` are the `r = 1` Hecke part, `family` and `external` are `0`, `report` is the objects' own time including the `F_ell` and `Z/ell^2` comparison objects) |
| `campaign_job_complete` | the same completion trailer, so `resume` works unchanged |

The file is small and is written once, at the end of the job.

### What each job refuses — recorded, never silently skipped

* **`ell ∈ {2, 3}`**: the cohomology is the Bredon object (lengths and
  invariant factors only, [C] `def:ringsemantics`(2)); `hecke` is refused by
  `HeckeOperatorOnK`, `bockstein` and `reduction` by `HeckeReduction` — each
  message is the real guard's, so a guard lifted later makes the job **fail**
  here until this schema is amended, rather than silently change its record.
  Every such job is `ok_partial`.
* **`r >= 2`**: `hecke` is refused at the job loop's own dispatch (`T_{p^r}`
  over the ring is not validated in this build); everything else runs.

### `summary.tsv` and `index.json` of a ring campaign

* `summary.tsv` keeps its 21 columns in order; `status` carries `ok_partial`
  where it applies; the ten field-valued columns (`dim_H0..2`,
  `charpoly_A0..2`, `trace_A1`, `rank_A1`, `theta_flat_hash_q1`, `external`)
  hold `-`. Fifteen columns are appended: `coefficient_ring ladic_level kmode
  length_H0 length_H1 length_H2 invariant_factors_H0 invariant_factors_H1
  invariant_factors_H2 r_K0 r_K1 bockstein_rank0 higher_torsion_count
  charpoly_free_A1 refusals` — lists `;`-separated, `()` empty, `-` absent (a
  degree outside `point.degrees` included), the charpoly as
  `c0;c1;...;1@<precision>`, `refusals` as the refused parts. A job `resume`
  skipped writes the ring and level and `-` elsewhere.
* `index.json` gains one top-level key, `"coefficient_ring"`, after
  `spec_origin`.
* A fingerprint-`0` campaign writes neither change.

### Example

```
$ ./hacs --campaign ring.spec --output /tmp/ring
  [ok  ] n_sym=6 ell=5 p=2 r=1 s=2e3e46911970e56a  Z/ell^2  lengths=(1,3,0)  kmode=certified ...
  [ok  ] n_sym=30 ell=5 p=2 r=1 s=2e3e46911970e56a  Z/ell^2  lengths=(2,12,0)  kmode=uncertified ...
  [part] n_sym=4 ell=2 p=2 r=1 s=2e3e46911970e56a  Z/ell^2  lengths=(2,4,0)  kmode=not_applicable ... refused=hecke;bockstein;reduction
```

Golden cost: none — the schema exists only at a fingerprint `!= 0`, and no
golden text is at one.


---

## 16. The orbifold section at ℓ = 2, 3 (`orbifold = c_i`, `orbifold_cell/v1`)

*(hecke-extensions slot 22, L23-1 — `docs/implementation/slot22/census_l23_plan.md` v0.3 §2 / §6 as amended by
`L23_master_plan.md` v0.2; code `Campaign/CampaignOrbifold.{h,cpp}`; report `docs/implementation/slot22/L23_1_report.md`.)*

At ℓ = 2, 3 the shipped field pipeline and the ext record compute **Bredon** objects. The orbifold section computes **ordinary group
cohomology** `H^q(SL₂(Z); Sym^n F_ℓ²)`, q ≤ 3, and the ℓ-adic lattice of `H¹(SL₂(Z); Sym^n Z²)` instead, one record per `(n_sym, ℓ)` cell.

### The keys

| key | default | meaning |
|---|---|---|
| `orbifold` | absent (`off`) | `c_i` turns the campaign into an orbifold campaign; `off` / absent leaves it **byte-identical** (nothing below is consulted) |
| `orbifold_primes` | `2,3,5,7` | the `T_p` of a cell; `T_ℓ` is always included |
| `orbifold_m_target` | `auto` | the certified ℓ-adic precision every cell reaches; `auto` = `max(⌊(n+1)/(ℓ+1)⌋ + 10, 40)` ([P3] §3.3: `max ed_tell ≤ (n+1)/(ℓ+1) + 4`) |
| `orbifold_k_cap` | `0` | the largest working precision K the reader may climb to (0 = its instantiated range: 1024 at ℓ = 2, 312 at ℓ = 3) |

A section gives `n_sym` and `ell` only. **Refused at spec validation, before any cell runs** (exit 1, no output): ℓ ∉ {2, 3}
(`not_implemented_in_this_build`), a `p` / `r` / `q` axis, `ext = true`, a non-default `coefficient_ring` (`not_implemented_in_this_build`),
`jobs > 1` (shard by spec instead), a cell whose `m_target + 16` exceeds the reader's range, an unknown model, a non-prime in `orbifold_primes`.
`RunCampaignSpec` refuses an orbifold spec, so its Hecke grid is never run by accident.

### Identity

Cell id `orb_ell<L>_n<N>`; when `OrbifoldFingerprint(spec) ≠ 0` — a non-default `hecke::MathSettings` entry (recorded, not consulted by the
cell) or a non-default `orbifold_primes` / `orbifold_m_target` / `orbifold_k_cap` (each may change a recorded value) — the id gains
`_s<16 hex>`, the whole FNV-1a-64 fingerprint, as in §4. The record's `record_fnv1a64` is the FNV-1a-64 of its canonical body, which carries
the `settings` block (both fingerprints and the orbifold keys), so a non-default setting changes the hash input as well; timings, RSS, the log
and the full `MathSettings` JSON (`settings_full`) are outside the body. So are, since the L23-1 audit (R4, R6), the reader's
**working-precision path** (`reader_path`: `rung`, `K`, `m`, `e_A`, `e_1`, `reruns`) and the **provenance** (`provenance`: `commit` =
`OC_GIT_COMMIT` baked at configure time, `binary` = `/proc/self/exe`, `binary_sha256`; also in `index.json`). The hashed `reader` block keeps
what the certification is relative to (`ran`, `ok`, `m_target`, `cap`, `certified`): every divisor below the cap is a module invariant read
at a certified precision `m ≥ m_target`, so a different `k_min`, width set (another build) or ladder leaves `record_fnv1a64` unchanged
unless a value moves. Records of record are produced by a binary built from a detached checkout under `$DATA_ROOT/` (so the baked commit is the
source commit; CLAUDE.md "shared and long-running binaries").

**`resume`** ([P3] R7 across restarts; audit R1) skips a cell whose file carries the trailer `"orbifold_cell_complete":true` **and** whose
`status` is `ok` or `fallback`. A complete `failed` record (or any other status) **stops** the campaign there: `STOP (resume on a failed
cell; [P3] R7): <id>: <its first failure> -- remove or rename cells/<id>.json to re-run it`, `stopped=1`, `failed=1`, the record's status
carried into `summary.tsv` / `index.json` (`"from":"resume"`), nothing after it runs, exit 2. A file without the trailer (a cell killed
mid-write) is recomputed.

### What a cell computes

* **(F)** on the isotropy-resolution model `C_I` over `F_ℓ` ([C] `prop:isomodel`(3)), q_max = 3: `h⁰ … h³`; `T_p = Θ̂_{diag(1,p)}`
  ([C] `prop:strictlift`(3)) as a matrix on every `H^q` (one prime at a time, applied to the `h^q` basis columns, one solve per degree);
  the Jordan type of `T_ℓ` per degree; `e ∪ −` (`H⁰ → H²`, `H¹ → H³`) and its Hecke equivariance ([C] `lem:bulkperiodic`).
* **(Z)** over `Z/ℓ^K`: the torsion of `H^q(V)` as the Smith invariants of `δ^{q−1}` (K = 31 / 19 at q = 1, a cross-check of the reader;
  K = 4 / 2 at q = 2, 3); `H^q(V)/ℓ ⊂ H^q(M)` for the (U) layers (q = 1, 2) by reducing the cocycles mod ℓ^4 / ℓ^2.
* **(L)** the BIN-3 reader `l23::read_lattice` with `m_target = cap = orbifold_m_target`: `rank Λ¹`, the torsion of `H¹(V)_ℓ`, the divisors
  of `T_p − (1+p)`, `T_p − (1+p^{n+1})`, `T_ℓ` on `Λ¹ ⊗ Z_ℓ`, and at ℓ = 3 on `Λ^±`.
* **(A)** the independent amalgam oracle (audit R3; specification `docs/implementation/slot22/fl231/compare_h1mod.py`): `l23::h1_mod` on
  `Z/4 *_{Z/2} Z/6`, no code shared with `C_I`, at ℓ = 2 for n ≥ 1 and at ℓ = 3 for even n ≥ 2 — `h⁰`, `h¹`, `rank T_ℓ`, `rank (T_ℓ − 1)` on
  `H¹(M)` and `L_k = log_ℓ |H¹(Γ; V/ℓ^k)|`, k ≤ 4 / 2 (recorded in `ladic.amalgam`), gated against `C_I` and
  `L_k = k·rank Λ¹ + Σ min(k, a_i) + Σ min(k, b_j)` (`a` = `T¹`, `b` = `T²`), which pins the `T²` multiset given `T¹`. ≤ 33 s at n = 700.

* **(S)** (L23-3) the level-1 q-expansion sum rules, `l23::sum_rule_oracle` (`Orbifold/L23/SumRuleOracle.h`; independent of the amalgam, the
  reader and `C_I`): `v_ℓ det(X | S_k)`, k = n + 2, for `X = T_ℓ`, `T_p − (1+p)`, `T_p − (1+p^{n+1})` from a unitriangular integral basis of
  `S_k(Z)` modulo `ℓ^K` (K doubles until every Smith invariant is below it); `G` gates on every certified lattice cell: `Σ ed_tell = 2 v det`,
  `Σ ed_tp_p = 2 v det + v(pⁿ − 1)`, `Σ` finite `ed_eis_p = 2 v det`, at ℓ = 3 also on `Λ^±` (`v det`, `+ v(λ_Eis)` on `Λ⁺`). Recorded in
  `ladic.sumrules`; the oracle's K is in the non-hashed `sumrule_path`. ≈ 2 s at n = 700. A rule whose divisor list is at the cap is not
  gated: the cell logs `SUMRULE_SKIPPED <name> at_least=<k> cap=<m>` and counts it in `ladic.sumrules.skipped` (data; `L23_3_audit.md` m2).
  An oracle that has not resolved at `k_cap` emits no gate (a precision shortfall is not a refutation, audit n7): the cell logs
  `SUMRULE_UNRESOLVED …` and records it as a finding.
* **(B/!/L)** (L23-3) `l23::h1_layers` on the amalgam over `F_ℓ` (no `cmpI^*`): `dims.dim_h1_br` (computed, both primes) and the `T_ℓ` triple on
  `H¹_Br` / `H¹ / H¹_Br` / `H¹` (`mod_hecke.t_ell_triple_B`, layer lines `br_sub`, `br_quot`); `dims.dim_h1_cusp` (`H¹_! = ker(H¹ → H¹(Γ_∞))`,
  `Γ_∞ = ±⟨T⟩`, [C] `def:bdrygroup`) with its intersections with `H¹_Br`, `H¹(V)/ℓ`, `T¹/ℓ` and `T_ℓ` on it (layer line `cusp`); `T¹/ℓ` as
  the Bockstein image; at ℓ = 3 `dims.L` (`L = ker(res to Γ(3))`, `L ∩ H¹_Br`, whether `L ⊂ T¹/3` — data, see below). ≤ 35 s / 0.3 GB at
  n = 700.

Divisor convention ([P3] §2.3): `0` a unit, `inf` the known kernel (the Eisenstein line of `ed_eis`), `>=<cap>` not certified below the cap.

### Gates, status and the discipline

Every record carries its gates, each `G` (a theorem: [C] `sec:oddnltwo` — `lem:centralminusone`, `lem:bocksteinallell`, `prop:oddnltwo`,
`lem:tellrank`, `prop:ltwothreescalar`, `prop:oddnhecke`(1)–(3), `lem:cprule` —, the UCT and periodicity identities, [R] Thm A / C closed forms,
the reader's internal checks, the Hatada–Rustom floors (LIT)) or `G-conj` (a conjecture: `T_ℓ` a rank-one idempotent on `H¹(M)`,
`prop:oddnhecke`(4), `e ∪ H⁰ = H²` at ℓ = 3, the ±-C law of `BIN3_audit.md` §4.4). A `G` failure makes the cell `failed` and **stops the
campaign** at that cell ([P3] R7: a bug or a refutation — stop and report); a `G-conj` mismatch is a finding. A cell with a divisor that should be
finite but is `>=cap`, or whose reader reached `orbifold_k_cap` unresolved, is `fallback` (recorded, counted, not failed).

**Gate sources** (audit R2). Every gate's JSON carries `source: {class, ref}`, and a failed `G` gate's message names it with its triage
reading — e.g. `t_ell_h0_rank [G R: Thm B(2)]: … -- a bug, a refutation, a misquoted citation, or an error in the review's proof`:

| class | ref | a `G` failure means |
|---|---|---|
| `C` | the [C] label (`lem:tellrank`, `prop:oddnltwo(3)`, …) | a bug, a refutation of [C], or a misquoted citation |
| `R` | the theorem of the review `census_l23_classification_review.md` (`Thm A` … `Thm E`; PROVED there, not refereed into [C]) | the same, or an error in the review's proof |
| `LIT` | the reference (Hatada–Rustom floors, Hida control, Eichler–Shimura, Dickson, Hecke commutativity) | a bug, a refutation of the literature, or a misquote |
| `UCT`, `cross-model`, `internal` | the identity / the two models / the reader's self-check | a bug |
| `CONJ` | the conjecture (every `G-conj` gate, and only those) | a finding, never a failure |

`dims.dim_h1_br` is `{"kind":"computed", …}` from the amalgam since L23-3 (at ℓ = 3 gated against `h¹ − rank e ∪`, [R] Thm E). L23-3 gates:
`sumrule_*` (`LIT`), `layers_*` (`cross-model` / `internal`), `br_codim_eq_h0` ([R] Thm B(5)), `br_codim` ([R] Thm C(1)), `br_eq_ker_e_cup`,
`br_hecke_stable` ([R] Thm E), `cusp_hecke_stable` ([R] Q10; **vacuous** while `dim H¹_! = 0`, i.e. on every cell computed: the detail then
reads `vacuous: dim H^1_! = 0` and the cell logs `CUSP_EMPTY`, audit m1), `L_dim`, `L_direct_sum` ([R] Thm C(3)) and the `G-conj`
`t1_mod_3_leaves_br_iff_n4mod6` ([R] Thm C(4) restated: [P3] §2.1's "`L ⊂ T¹/3` iff n ≡ 4 mod 6" is false as a subspace statement — the Bockstein
line restricts non-trivially to `T³ ∈ Γ(3)` — so `L.in_T1` is data; `L23_3_report.md` §4). At ℓ = 2 the `G` gate
`e_cup_h0_h2_injective` (`e ∪ − : H⁰ → H²` injective, [R] Thm B(4)) runs on every cell with `h⁰ > 0` (audit R5).

**Memory** (audit F7). The driver has **no** RSS cap or admission of its own, deliberately: an in-process `RLIMIT_AS` would turn an
allocation failure into an exception, i.e. a `failed` cell and a false [P3] R7 stop. The per-cell bound (16 GB at n = 700 by the L23-1
forecast, ±35 %) is the **runner's**: run each shard under a tree-RSS watchdog as `docs/cluster/local/run_local_census.sh` does (admission
on the sum of predicted RSS, `TERM` of the youngest cell above cap + 8 GiB, summed ≤ 64 GiB, rule O3), with cells n ≥ 600 alone or two at a
time. A `TERM` is resume-safe: a record is written only after its cell completes, so a killed cell leaves no file or one without the trailer,
and `resume` recomputes it. L23-4 measures `(2, 700)` and `(3, 700)` alone first (rule 19).

The run ends with

```
EFFECTIVE campaign arm=orbifold cells=<k> ran=<r> skipped=<s> failed=<f> refused=0 fallback:<b> findings=<c> stopped=<0|1> wall_s=… peak_rss_mb=…
```

(and starts with `EFFECTIVE campaign arm=orbifold model=c_i cells=<k> primes=… m_target=… fingerprint=…`). A census shard must read
`refused=0` and `fallback:0`.

### Output

`<output>/cells/<id>.json` (`orbifold_cell/v2` since slot 24 L23-H1; `v1` = the same record with the sum-rule oracle's wall time inside the hashed gate detail: `dims`, `mod_hecke`, `ladic` (with `amalgam`), `layers`, `gates`, `census_columns`,
`record_fnv1a64`, `log`, `reader_path`, `provenance`, `timings_s`, `peak_rss_mb`), `summary.tsv` (one cell line, 42 columns), `layers.tsv` (one line per `(q, layer, T_ℓ-eigenvalue)`: `dim`,
`t_ell_jordan`), `index.json` (`orbifold_campaign/v1`). `census_columns` classifies every `hecke_census/v1` + `dataset/v2` column per
maximal ideal `ord` / `nonord` of `F_ℓ[T_ℓ]` on `H¹(M)` as `computed`, `formal` (with its value), `not_applicable`, `not_computed`,
`replaced` or `ingest` ([P3] §2.4), so the L23-6 section tool can lay ℓ = 2, 3 rows beside the census.

**Record format versions (slot 24 L23-H1, KNOWN_ISSUES §7 / finding H-1).** `record_fnv1a64` is FNV-1a-64 (`ModArithmetic/Fnv.h`) of BODY, the bytes
of the record between the leading `{` and `,"record_fnv1a64":"`. `v1`: the detail of the gate `sumrule_oracle_resolved` ended
`-> resolved (0.274 s)`, the sum-rule oracle's wall time, so the hash moved with the box's load. `v2`: the body's schema string is
`orbifold_cell/v2`, that detail ends `-> resolved`, and the time is the unhashed number `timings_s.sumrule_oracle` (the digits as printed,
between `sumrules` and `total`); no other byte of the body moves, no value changes. **Reads old vs new:** the writer (`OrbifoldCellJson`) writes
only `v2`; `RunOrbifoldCampaign` resume, `run_shard.sh`, `watch.py`, `gen_specs.py` and the ingest scripts (`ingest_l23.py`, `ingest_even_lean.py`)
look at `status` / `orbifold_cell_complete` / the census columns only, so they read `v1` and `v2` alike (a resume over `v1` files skips them as before:
their values stand; the shard is then **mixed-format**, and since the L23-H1 audit (F2) a verbose run says so on one line
`RESUME_FORMAT resumed_not_v2=<k> (...)`, printed only when `k > 0`; `OrbifoldCampaignResult::resumed_not_v2`);
`ingest_*` copy `record_fnv1a64` verbatim, so a census table ingested from `v1` records keeps the `v1` hashes until it is re-ingested from converted
records; `ingest_l23.py` refuses a mixed v1 / v2 input (audit F4) and names the one schema on its verdict line (`schema=orbifold_cell/v2`). **For census 3.5:**
convert every `v1` run (`s22/l23_census/{even,even4,odd4}`, any v1 shard a resumed run left behind) and ingest the converted copies: the L23-H1 audit converted
all 1052 census records and the ingest of the copies equals the 3.4 table but for the `record_fnv1a64` column (`slot24/L23H1_audit.md`). `docs/implementation/slot22/l23_census/record_compare.py` and the validations compare `v2` raw (no mask) and refuse `v1`.
`docs/implementation/slot24/l23_record_convert.py --out DIR (--dir RUN | FILE...)` turns stored `v1` records into `v2` copies (hash re-derived
over the new body, time moved, `index.json` / `summary.tsv` hash columns rewritten, `hash_map.tsv` old -> new); it never modifies its inputs and refuses an
`--out` that is the run directory or an input file (audit F1), and writes no `index.json` / `summary.tsv` when any record failed.
The DEEP production run (`s23/deep1`) stores `.cells` / `.log` / `.time` files, not `orbifold_cell` records, and is not affected.

```
name     = l23_first
orbifold = c_i
n_sym    = 0..700
ell      = 2
---
n_sym    = 0..700 step 2
ell      = 3
```

Golden cost: none — no golden text, setting or default changes; a spec without `orbifold` is byte-identical.

## 17. Campaigns over `Z` (`coefficient_ring = Z`, `integral_descent_record/v1`)

(Slot 24, DESCENT D6; `DESCENT_plan.md` §4 D6, [X] OD-10 (a); code `Campaign/CampaignDescent.{h,cpp}`, the record
`Integral/Descent/DescentRecord.h`; [C] `thm:descentcert`, `sec:descentpair`.)

Under `coefficient_ring = Z` the campaign is a campaign of **descent cells**, one per `(level, n_sym)`: the integral descent of
`H^q(Γ_0(N); Sym^n Z²)` — the groups to `q_max = 3` (`object = group`, `truncated = true`, `derived`, periodic from `q = 2` by
`thm:descentcert(6)`), the bad primes `B(M_N)` with their counts, the certified precision `K` per torsion prime (provenance, not hashed),
`char_Z(T_p | H^1/tors)` per Hecke prime, the torsion Hecke modules by their choice-free invariants, and the boundary pair (`H`, `H(∂)`,
`H_c`, q = 0 … 4).

### The keys

| Key | Meaning |
|---|---|
| `coefficient_ring = Z` | selects the descent cells (a mathematical setting: every cell id carries `_s<16 hex>`) |
| `n_sym` (grid, required) | n |
| `level` (grid, default 1) | N of Γ_0(N); **a spec error outside `coefficient_ring = Z`** |
| `p` (grid, optional) | the cell's Hecke primes P; a p dividing a level of its section is a spec error (D6 audit N2: put that level in a section of its own); absent: the first three of 2, 3, 5, 7, 11, 13 not dividing N |
| `parts` (default `all`) | `all` \| `groups,hecke` \| `groups`: which parts of each record a cell computes (ICENSUS-P2). `all` is the campaign as before (ids and record bytes unchanged); a skipped part is written `"ran":false` (`"hecke":{"ran":false}` / `"pair":{"ran":false}`) and the hashed body says `hecke=not_run`; a non-default value is part of the cell id (`_partsGH`, `_partsG`) and of `index.json` (`"parts"`); an unknown value is a spec error (one of three words: blanks only around the comma); a `groups` record skips the torsion-read-vs-groups cross-check (it lives in the Hecke part), so a groups-only grid is not cross-checked as a full one; **a spec error outside `coefficient_ring = Z`**. Measured (RelWithDebInfo): (30,2) 3.6 s / 0.83 s / 0.02 s, (12,4) 0.89 / 0.34 / 0.016, (1,40) 0.36 / 0.20 / 0.026 for all / groups,hecke / groups |
| `name`, `output`, `resume` | as everywhere |

Refused at spec validation, by name, before any cell runs: `ell`, `r`, `q` (a descent cell has no coefficient prime, records `T_p`
only and derives its degrees), `orbifold`, `ext = true` (exit 5, as for every non-default ring), `jobs > 1`, `level = 0`, a non-prime p.

### Identity and output

Cell id `desc_N<N>_n<n>[_p<p1>-<p2>-…]_s<16 hex>[_partsGH|_partsG]` (the `_p` tag only when P is not N's default; the `_parts` tail only for a non-default `parts`). Each cell writes
(Slot 24 FMTMP, [C] `sec:recordschema` item 7 (l).) A char_Z coefficient beyond 2^63 is in the cell file exactly: the entry's list
`big` of `{"i":…,"hex":"<canonical signed hex>"}`, hashed by one body line each (a record without one keeps its bytes and its
`record_fnv1a64`). The cell id does not change with the format (no mathematical setting changed; the precedent of the slot-2 `q` rule
above: resume keys on what determines the values, not on presentation), so `resume = true` into a directory of older cells accepts them as
they are; write a re-run that is to carry the exact values to a fresh `--output`.

`<output>/cells/<id>.json`: one line `{"schema":"integral_descent_cell/v1","id":…,"campaign":…,"record":<integral_descent_record/v1>,
"complete":true}`; then `summary.tsv` (`id N n primes status H0 H1 H2 H3 record_fnv1a64 seconds`) and `index.json`
(`integral_descent_campaign/v1`). The record's `record_fnv1a64` hashes its invariants and the settings' canonical text, so a non-default
setting changes the id and the hash input; timings, RSS, K and routes are outside it. The last line printed is
`EFFECTIVE campaign arm=descent cells=<k> ran=<r> resumed=<s> refused=<x> failed=<f>`. A refused record (a cap or a precision limit of a
part, with its reason) is written with `status = refused` and counted; a cell that throws is `failed` (exit 2). `resume = true` skips a
cell file ending in the completion trailer. `--dry-run` lists the cells with `D = ψ(N)(n+1)`.

**From the console** (D6 audit N1): `campaign_plan(spec)` of a `coefficient_ring = Z` spec returns one group, signature
`integral_descent_cell/v1`, whose `jobs` are the cell ids above; `run_campaign(spec, output)` runs the descent cells under the spec's
settings, as `--campaign` does, and returns the usual record (`skipped` = the resumed cells) plus `refused`.

```
coefficient_ring = Z
name   = descent_small
n_sym  = 0..12 step 2
level  = 1, 2, 3, 5, 7, 11
```

**Running a grid** (ICENSUS P3): `jobs > 1` is refused, so a large grid is sharded by spec, one process per shard, under an RSS watchdog, resumable and gated, by `docs/integral_census/mk_icensus.py` (README beside it).

Golden cost: none on this branch (the staged DESCENT points are the owner-gated add-only event, `slot24/d6golden/ledger.md`); a spec
without `coefficient_ring = Z` is byte-identical (`level` is refused there).

## 18. Hecke-structure cells over `Z` (`structure = hecke`, `integral_hecke_structure/v1`)

(slot-25 HZ-REC; `[C]` `sec:recordschema` item 8; code `Campaign/CampaignHeckeZ.{h,cpp}`, `Integral/HeckeZRecord.h`; report
`docs/implementation/slot25/HZREC_report.md`.) Under `coefficient_ring = Z` the key **`structure = hecke`** makes the campaign write one
record `integral_hecke_structure/v1` per (level, n_sym, algebra) cell instead of a descent record. `structure` selects the record
schema; it is a campaign key, **not** a twelfth mathematical setting ([C] item 8 (a), Q17(v)); the default `none` is §17's descent
campaign, byte-identical.

```
name = hz_toy
coefficient_ring = Z
structure = hecke
n_sym = 10, 22            # level 1 (default), algebra full (the only algebra at N = 1)
---
level = 2, 8
n_sym = 6
algebra = full, anemic    # default: full at every N (as the console verb)
hz_cert = on              # optional: also the certificate files (HZ-EMIT) into <output>/hzcert/
hz_g8 = hida              # optional (slot-25 H1): heckez.G8 = hida, the Hida block per maximal ideal (G8); default off
hz_theta_order = lex      # optional (slot-27 TS): the theta search's order, lex | lex_then_greedy; absent = the default (lex until the flip)
```

- **Keys.** Per section `n_sym` (required, even), `level` (default 1), `algebra` (`full`, `anemic` or both; default `full` at every N,
  as the console verb `hecke_structure`; `anemic` at level 1 is a spec error). Refused at spec validation: `ell`, `r`, `q`, `p` (the operator set is the record's `P_rule`, a cap of its settings text),
  `parts` (the descent_ref is always the `groups,hecke` descent), `orbifold`, `jobs > 1`, an odd `n_sym`, N = 0. `structure`, `algebra`
  `hz_cert`, `hz_g8` and `hz_theta_order` outside `coefficient_ring = Z` (or `algebra` / `hz_cert` / `hz_g8` / `hz_theta_order` without `structure = hecke`) are spec errors.
  (slot-25 H1) `hz_g8 = off | hida` sets the record's settings value `heckez.G8`: `hida` writes H1's G8 (the Hida block per maximal
  ideal at level 1; `docs/implementation/slot25/H1_report.md`), a non-default value with its own fingerprint and cell ids, never golden.
  (slot-27 TS) `hz_theta_order = lex | lex_then_greedy` sets HZ-RAT's settings value `theta_order` ([C] item 8 (j);
  `docs/implementation/slot27/TS_design.md`): `lex` is the order of HZ-DS editions 1–3 (the units, then the lexicographic combinations,
  at most `theta_cap`) and serialises to their settings text byte for byte; `lex_then_greedy` adds the greedy per-operator continuation
  where `lex` ends without a primitive θ (in a step without U_p only at `|P| = p_rule_cap`) and the capped continuation at
  `heckez.maximal_ideals`, printed as `;theta_order=lex_then_greedy(t=2654435761;steps_without_U_p:|P|>=p_rule_cap)` in the
  `theta_search` line and one clause of the `maximal_ideals` line: its own fingerprint and cell ids. **An absent key is not `lex`**: it
  keeps the build's default (`lex` until the slot-27 flip; afterwards `lex_then_greedy`), while an explicit `lex` always reproduces
  editions 1–3. Refused like `hz_g8` outside `structure = hecke` / `coefficient_ring = Z`.
- **Identity.** `hz_N<N>_n<n>_<alg>_s<16 hex>`, the hex = FNV-1a-64 of the record's settings text (the mathematical settings' canonical
  text and the HeckeZ caps: `P_rule`, `theta_search` + `factor_budget`, `S_rule`, `K_read`, `maximal_ideals`, `irreducible`,
  `G8` (default `off`: no G8 field; `hida` under `hz_g8`), `bezout_record_cap`); a non-default setting or cap is a
  new id and a new hash input.
- **Output.** `<output>/cells/<id>.json` = `{"schema":"integral_hecke_structure_cell/v1","id",…,"campaign",…,"record":<record>,"seconds",…,"rss_mib",…,"complete":true}`
  (each field as `[group, path, value, vocabulary, parent]`);
  `summary.tsv` (id, N, n, algebra, status, record_fnv1a64, cert_sha256, descent record hash and the ed.1 `cell_sha256` join, seconds,
  RSS MiB); `index.json`. Each record's descent is run in process (parts `groups,hecke`, the ed.1 configuration) and joined to integral
  census edition 1 (`docs/integral_census/results/ed1/rows.tsv`: `cell_sha256`, or `not_in_ed1` / `ed1_mismatch`). Last line:
  `EFFECTIVE campaign arm=hecke_structure cells=<k> ran=<r> resumed=<s> rejected=<j> refused=<x> pending=<p> final=<f> failed=<e>
  outside=<o> under=<u> ed1_mismatch=<m>`. Every written record is scanned (a value outside the closed lists or an exact value under a
  bound fails the cell). `resume = true` re-reads a complete cell file and accepts it only if its id, settings fingerprint, both hashes
  and its status recompute and its scan is clean; a rejected file is counted and the cell recomputed. A failed cell or an ed.1 mismatch
  exits 2.
- **Cost.** The toy cells take 0.05–1.6 s and ≤ 90 MiB each; the HeckeZ run (HZ-KIT / HZ-RUN, 145 cells) is costed in
  `slot24/heckez/04-record-census.md` §4.

