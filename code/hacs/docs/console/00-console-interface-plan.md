# Console Interface — Implementation Plan (September 2026)

**Version 3.15.0-pre.9 (2026-11-12, slot-27 NB-A' C1: Copy as LaTeX; pre-release; page only).** The notebook page gains a *Copy as LaTeX* action: per value block (*LaTeX*, shown when the value has a math rendering), per output box (the values' TeX as display formulas), and per text cell (its source, whose `$…$` / `$$…$$` are the TeX the page renders). The TeX is the page's own (`toTeXRaw` and the hint path of §18.5), built in the browser from the envelope and independent of the LaTeX switch; **no TeX comes from the binary** (§18.1 item 2 stands). No protocol, binary, value, transcript, registration or golden change; tested by `test_render.mjs`.

**Version 3.15.0-pre.8 (2026-11-12, slot-26 NBMATH stage A: text cells typeset; pre-release; page and examples only).** §18.18 (e) is replaced: a text cell renders `$…$` / `$$…$$` through the vendored KaTeX (`trust: false`) and a minimal markdown (paragraphs, `- ` lists, `> ` a statement box, `| … |` tables whose rows may continue over lines, `**bold**`, `` `code` ``), built from text nodes only (never `innerHTML`); with LaTeX off it shows its source verbatim, and *Copy* / *Export* / *Save* always use the source. A text cell titled `Reading…` is a **reading panel** (one two-column table, *Mathematics* ↔ *What HACS computed, and how*), folded by default and open in a notebook named `showcase_*.oc`. New §18.18 (g): a String value of the exact form `certified:<signed hex>` (the HeckeZ record's convention) is shown in decimal with LaTeX on, the stored form on hover; its canonical text is unchanged. The examples directory gains the showcases `showcase_ramanujan_691.oc` and `showcase_cohomology_ses.oc` (listed first in *Examples…*), and the ten tour files are rewritten (statement in TeX, one `assert` per stated fact, a reading panel per output; design `docs/implementation/slot26/NBMATH_plan.md`). No TeX from the binary (§18.1 item 2 holds), no toTeXRaw / hintTeX case (the render coverage gate is unchanged), no protocol, binary, value, transcript, golden or registry change.

**Version 3.15.0-pre.7 (2026-11-09, slot-26 LAYOUT: repository layout; pre-release).** Paths only, no change of content (repository layout, owner ruling 2026-11-09): the code moved under `src/` (`src/hacs/`, `src/ModArithmetic/`, `src/Engine/`, `src/Cuda/`; old → new: `tools/layout/mapping.tsv`), so this plan's long-form paths now read `src/hacs/Console/…`; module-relative paths (`Console/Core/…`, `Hecke/…`) are unchanged. No mechanism, grammar, setting or transcript changes.

**Version 3.15.0-pre.6 (2026-11-09, slot-26 R1b: the binary is called `hacs`; pre-release).** Name only: command lines in this plan say `hacs`; the build target stays `cohomology_app`, and a `cohomology_app` link is kept as an alias (rename plan `docs/hacs/HACS_rename_plan.md`). No mechanism, grammar or setting changes.

**Version 3.15.0-pre.5 (2026-11-07, slot-25 NBCONFIRM S5: the cooperative cancel; pre-release).** A running statement can be cancelled **inside** a long verb, not only between statements (report `docs/console/NBCONFIRM_S5_report.md`; design §2.7; owner ruling 2026-11-06 Q5). §7 (normative, replacing the "not interruptible" bullet): the interactive REPL installs a SIGINT handler; the first Ctrl-C during a statement stops it at its next **cancellation point** (`<pos>: interrupted (at <site>)`, the prompt returns; the interrupted statement's own binding is not made, while earlier effects of a compound statement (e.g. a `for` body's earlier assignments) and earlier statements stay, exactly as after any error; a lazy handle whose work was stopped stays `declared` and its next read retries); Ctrl-C at the idle prompt, and a second Ctrl-C before the first took effect, end the process by SIGINT as before. Scripts, `-c` and `-` install no handler (unchanged). §18.6: `interrupt` (and SIGTERM) take effect at the next cancellation point of the running cell. New §7.2 (the points, their rules, the test interlock `HACS_CANCEL_TEST`). The engine `ThreadPool` is unchanged (no point inside a kernel or a parallel region). No value, golden entry, `.expected` transcript, ConsoleDet digest or `SERVE_DETERMINISM` digest moves; a statement that is not cancelled runs exactly as before.

**Version 3.15.0-pre.4 (2026-11-07, slot-25 NBCONFIRM S4 Fix round 1; pre-release).** The S4 audit's repairs (`docs/console/NBCONFIRM_S4_audit.md`; report "Fix round 1" of `NBCONFIRM_S4_report.md`), all in §18.19: the gateway raises a confirmed cell's wall limit **only** on the child's own `progress.confirmed` frame for the in-flight request, never on a presented token (M1); "Re-sending" corrected — a re-send re-executes the cell's earlier statements with the stopped run's bindings (side effects and earlier confirmed calls included), a cell that rebinds what it reads never converges, and the page asks at most once per call site per cell run (M2); one token confirms every execution of the same call in the cell run, and is not single-use within the session (L1, N3); the dialog's two fixed notes; `--serve` refuses `HACS_HOST_PROBE_FIXTURE` unless its parent is the same binary (L2). No value, golden entry, `.expected` transcript or ConsoleDet digest moves; the binary's frames are unchanged.

**Version 3.15.0-pre.3 (2026-11-07, slot-25 NBCONFIRM S4: the served console, the gateway, the page; pre-release).** The cost confirmation of §7.1 reaches `--serve` (report `docs/console/NBCONFIRM_S4_report.md`; design §2.5–2.6; owner ruling 2026-11-06 Q4). New **§18.19** (normative): under `confirm = ask` a served cell gets rules 1–4 of §7.1 exactly as a terminal REPL, with the protocol as the prompt — a call needing a normal or strong confirmation stops the cell with `done{status:"confirm_required", exit:3, error.kind:"confirm_required", confirm:{token, level, estimate …}}`; the client re-sends the **same** `eval` with `"confirm":[token, …]`; the token (FNV-1a-64) binds the session, the cell text, the call site, the call, the estimator's arguments, model, threads and level, and every setting in force. A hard refusal has no token. A confirmed run sends `progress` frames with a `confirmed` member (at its start and every 10 s; also when a lazy `descent` starts its work in a later cell). §18.3 (`eval.confirm`), §18.4 (the `done` status and `confirm` member; the `progress` member; `hello.limits.confirm_wall_s`), §18.6 (heartbeat; the page's "Kill session" fallback), §18.8 (`confirm_wall_s` settable; `confirm` not), §18.10 (the session's `--rss-cap-mib` is R_cap of rule 1, per cell). The gateway forwards `confirm` and sets a confirmed cell's wall limit to max(`--cell-wall-s`, 3 · wall_hi + 60), at most `--cell-wall-max-s` (default 21600 s), from the child's own estimate only; the page shows a confirmation dialog. §7.1: inside an `expect_error` block a cost-gated call never asks (every mode). No value, golden entry, `.expected` transcript or ConsoleDet digest moves; every served script's frame stream is unchanged (none crosses an envelope outside `expect_error`).

**Version 3.15.0-pre.2 (2026-11-07, slot-25 NBCONFIRM S3 Fix round 1; pre-release).** The S3 audit's repairs (`docs/console/NBCONFIRM_S3_audit.md`; report §8 of `NBCONFIRM_S3_report.md`), all in §7.1: rule 1 also refuses a non-finite or non-positive estimate and a no-model call whenever a memory limit is known (M1); a threaded RSS model is never below its T = 16 fit beyond T = 16 (a conservative model-rule change: it only raises estimates; ids `descent_cost/v2`, `hida_tower_cost/v2`); `level_n` / `nebentypus` refuse N ≥ 2^31 by name (m1); `module` / `module_Z` exports of a confirmed `descent` cell take the lowered piece cap (m3); `--calibrate` refuses an in-tree profile path (m5); the pty arm's host fixture (m2); `include` at a terminal REPL may ask (i2, documented). §8: one row (the "no usable estimate" refusal). No value, golden entry, `.expected` transcript or ConsoleDet digest moves; every prompt-less mode is byte-identical to 3.15.0-pre.1 (the new refusals fire only where a call gets past its envelope bound: `confirm = yes` or a terminal REPL).

**Version 3.15.0-pre.1 (2026-11-07, slot-25 NBCONFIRM S3: core + REPL/scripts; pre-release).** Ask before a long computation instead of capping it (`docs/console/NBCONFIRM_design.md` with the S2 corrections; owner rulings of 2026-11-06 Q1–Q5 and the S1 follow-up; report `docs/console/NBCONFIRM_S3_report.md`). (1) **New §7.1**: the cost bounds of `descent`, `hecke_structure`, `level_n`, `nebentypus`, `forms_algebra`, `hida_lambda`, `hida_tower` (and their prime-list sizes) become each verb's **silent envelope**; inside it nothing changes; outside it a **terminal REPL** shows an estimate and asks (`[y/N]`, a strong warning needs a typed `yes`), and **every prompt-less mode** (`--script`, `-c`, `-`, a piped REPL, the script half of `--script f --console`, `--serve` until S4) refuses with the **pre-S3 text, byte for byte, exit 3**, unless `confirm = "yes"`; a **hard refusal** (estimated peak RSS above min(session cap, 80 % of MemAvailable), or C: ≤ 10 GB free) refuses in every mode. Mathematical, word-size and well-definedness preconditions stay refusals. (2) **Two settings** (§2 C4, engine family, never in a record, a hash or the fingerprint): `confirm` = `ask` (default) | `yes` | `no` and `confirm_wall_s` (Int ≥ 0, default 60). (3) **§8**: rows for the hard refusal, a declined prompt (`not run`, nothing bound) and two typed refusals that replace `ENGINE_CHECK` leaks (`hecke_structure(1, 0)`; `hida_tower` with K = m + e_max < 2). (4) **CLI**: `hacs --calibrate[=thorough]`, the per-device speed profile (`${HACS_DEVICE_PROFILE:-${XDG_CONFIG_HOME:-~/.config}/hacs/device_profile.tsv}`; calib/v2); not in the frozen help text, in the manual's token table. (5) The served console (§18.4 `confirm_required`, §18.6 heartbeat, §18.8 settable +1, §18.10 per-cell rule 19) is **S4, not in this version**: `--serve` refuses outside the envelopes exactly as before. Gate: `ConsoleCostModelValidation` (`fast`). No value, golden entry, `.expected` transcript or ConsoleDet digest moves.

**Version 3.14.0-pre.9 (2026-11-06, slot-25 EXZ2-P3, EXPORT-Z step 2; pre-release).** The method `DescentRecord.module_Z` gains one optional argument, **`module_Z(mode)`** (`computed = true`, as before; §3.6 row of `descent`). **`module_Z("local")` is step 1 byte for byte** (the 3.14.0-pre.7 value: `free_block = "pending(step 2)"`, M against the local free generators of `module(ell, K)`); any other argument is a type error (exit 3). **`module_Z()` is step 2**: the same record keys with the free block **exact over Z** — `free_block = "exact"` (or `"refused"` with `free_refusal` when the free basis or the CRT refuses on a resource ceiling; M then stays local), `M_basis = "global"`, `entry_encoding = "exact"` — plus `basis: {rule (iso_dixon/v3), q0 (q0= q0_confirm= q0_skipped=), saturation (det_pm1, or rank0 at r = 0), basis_fnv (FNV-1a-64 of B), phi_fnv (of Φ_cert), bits_B, bits_Phi, bound}` (`bound`: the functionals of the CRT bound by the Auto size rule — `phi0` while r·(bits Φ_0 + bits B) ≤ 20000, which holds on every script and tour cell, else `phi_cert`; `-` at rank 0) and `free_refusal`; per op `F` is the r × r matrix of **decimal integer strings** (no word bound, no residues-plus-bound), `M` the mixed block **against the classes [b_j] of the cocycles of B themselves** (EXZ2-P3 fix round 1, audit F2, the owner's option (b)): T_p b_j = Σ_i F_ij b_i + Σ_a M_aj g_a holds as printed (g_a the torsion generators, row a mod d_a), i.e. M = M_local C_ell − π_B F + τ π_B with π_B = π_ell(B) the torsion coordinates of B under `export_retraction/v1`, printed per torsion prime as `retractions[].pi_B` (t_ell × r, row a mod d_a) with `pi_B_fnv` (the complement s_j = [b_j] − Σ_a π_a(b_j) g_a = ker π is recovered by M_kerπ = M + π_B F − τ π_B); production checks π_ell(T_p B) = M + π_B F at every torsion prime (the route's own operator on B, no M_local, no C); and new keys `F_fnv`, `M_fnv` (FNV-1a-64 of M over every ell, `M_span/v1|N|n|p|basis_fnv|` then per ell its d and rows), `F_proof` (`apriori` | `apost` | `rank0`), `F_primes` (the CRT lanes of the proof), `C: [{ell, modulus, matrix}]` (B in the export's local free generators mod ell^σ_max: C F = F_local C). B is the picked basis of EXPORT-Z step 2 (`Integral/Descent/DescentFreeBasisZ.h`, design `slot25/EXPORTZ2_design.md` §1.1–§1.4: Dixon pairs on the free tree model, lattice sums, saturation, certified by det(Φ_cert^T B) = ±1 and a rank witness), F_p is the proven multimodular CRT of `DescentFreeBlockCrt.h` (§1.5, §1.6), M comes from the exports run once in B (`ExportModuleZ2`, `Integral/Descent/DescentModuleExportZ.h`, "STEP 2"). With `ENGINE_DEVICE=gpu` (and a device) the CRT lanes run on the GPU lane route (bit-identical; no printed key depends on it). The matrices remain a presentation, unique up to the block-triangular group; the basis is named and reproducible (rule + FNV), not canonical. Computed once per handle (its exports run in the basis B and are not shared with `module(ell, K)`). Script `059_s25_descent_module_z.oc` now calls `module_Z("local")` (its `.expected` does not echo script lines: byte-identical, no re-baseline); new script **`061_s25_module_z_exact.oc`** (new `.expected`; it prints `pi_B` and `M_fnv` since the fix round); the notebook tour gains `09_integral_hecke_module.oc` (and `tour_all.oc` its cells; nine tour files). A method of a `read_only` type: no tag row. No verb, member, setting, exit code, existing transcript, golden entry, record key or ConsoleDet digest moves; `console.md` and the `[CLI]` tables regenerated.

**Version 3.14.0-pre.8 (2026-11-06, slot-25 HZ-REC; pre-release).** New verb **`hecke_structure(N, n, algebra = "full")`** → Record (`read_only`; §3.6 row after `descent`): the record `integral_hecke_structure/v1` of the cell (`[C]` `sec:recordschema` item 8, `sec:heckeZ`; `Integral/HeckeZRecord.h`, registered from `HeckeExt/RegisterHeckeZRecordVerbs.cpp` because the record builder's level-1 source lives in `HeckeExt/`, HZ-LOC audit F8). **Only under `coefficient_ring = Z`** (otherwise a runtime error asking for it, exit 3); `algebra` `"full"` or `"anemic"` (`"anemic"` only at N > 1); the descent verb's bounds N ≤ 300, n even ≤ 60, index(N)(n+1) ≤ 300 (a limit is a type error, exit 3). Record `{schema, id, N, n, algebra, status (final | pending | refused), golden_eligible, record_fnv1a64, cert_sha256, settings_fingerprint, descent_record_fnv1a64, signature, generation: ["<ell>:<status>(<route>)", …], C_T ("<status>[:<exact hex>]"), body: ["<path>=<value>", …] (the hashed fields G0 … G8)}`. Computed eagerly (≈ 0.1–1.5 s at the toy cells). New script `060_s25_hecke_structure.oc` (new `.expected`; it prints the generation statuses and C_T only, the parts HZ-TOR does not move). Rows added to `ReadOnlyTags.cpp` and `Console/serve/read_only_verbs.tsv`. No member, setting, exit code, existing transcript, golden entry or ConsoleDet digest moves; `console.md` and the `[CLI]` tables regenerated.

**Version 3.14.0-pre.7 (2026-11-06, slot-25 EXPORT-Z step 1; pre-release).** `DescentRecord` gains the **method** `module_Z()` (no arguments; `computed = true`: it forces the record, whose basis-free invariants it prints; §3.6 row of `descent`): H^1(Γ_0(N); Sym^n Z^2) over Z as a **presented** Z[T_p : p ∈ `primes`]-module (`Integral/Descent/DescentModuleExportZ.h`, design `slot25/EXPORTZ_design.md`; `[C]` `prop:torsionhecke`(1), (3)). In generators torsion first, then lifts of a basis of L = H^1/tors, T_p = [[τ, M], [0, F]] (column convention). Step 1 serves τ (block-diagonal over the record's torsion primes, row i mod d_i; generators = the torsion cocycles of `module(ell, K)` at K = σ_max(ell), ell ascending) and M (per ell, row i mod d_i, **against the local free generators of `module(ell, K)`**: `M_basis = "local"`), all in-word (`entry_encoding = "word"`). **F over Z is not computed in step 1**: `free_block = "pending(step 2)"` and every op's `F` is that string, never a matrix; the export's free block mod ell^K is given as `F_local` with its `modulus` (it is not F). The splitting is named: `splitting = "export_retraction/v1"` (π = ⊕ π_ell, π_ell the export's torsion coordinates), each π_ell by its FNV-1a-64 in `retractions: [{ell, route, K_run, K, fnv}]`. Record `{N, n, primes, status (ok | blocked(export)), refusal, splitting, retractions, torsion_primes, largest_torsion_prime, invariant_factors (the **elementary divisors** d_i = ell^{σ_i}, prime powers, ell ascending — not the invariant factors d_1 | d_2 | …; the key name is kept, as in `module(ell, K)`, so no transcript moves), torsion_generators: [{ell, exponent, d}], free_rank, free_block, M_basis, entry_encoding, split ("unknown" until HZ-TOR), presentation, ops: [{p, tau, M: [{ell, K, matrix}], F, F_local: [{ell, modulus, matrix}], charpoly_Z (the record's char_Z(T_p | H^1/tors), high → low)}], torsion_canon: [{ell, ops: [{p, invariants}]}] (the record's, q = 1)}`. The matrices are a presentation, **unique up to the block-triangular group [[Aut T, Hom(L, T)], [0, GL_r(Z)]]**; the basis-free invariants are `invariant_factors`, `free_rank`, `charpoly_Z`, `torsion_canon`. An export refused at any torsion prime makes the whole value `blocked(export)` with `refusal` `ell = <ell>: REFUSED [<code>] …` and no τ / M (not an error); in a blocked value `largest_torsion_prime`, `invariant_factors`, `torsion_generators` and `free_rank` are the string `"blocked"` (never `[]` / `0`, which would read as torsion-free; EXPORT-Z audit F1). The exports are shared with `module(ell, K)` (the same per-handle cache). As `module`: a method of a `read_only` type, no tag row. New script `059_s25_descent_module_z.oc` (new `.expected`). No verb, member, setting, exit code, existing transcript, golden entry or ConsoleDet digest moves; `console.md` and the `[CLI]` tables regenerated.

**Version 3.14.0-pre.6 (2026-11-05, slot-25 EXPORT; pre-release).** `DescentRecord` gains the **method** `module(ell, K)` (`computed = false`: it does not force the record; §3.6 row of `descent`): H^1(Γ_0(N); Sym^n Z^2) ⊗ Z/ell^K with T_p, p in the handle's `primes`, by cochain-level lifts (`[C]` `prop:torsionhecke`(3), `prop:strictliftN`(2), (3), (5); `Integral/Descent/DescentModuleExport.h`) as a Record `{N, n, ell, K, K_max, route, carrier, primes, status, refusal, free_rank, torsion, invariant_factors, generators: [{kind, exponent, cocycle}], ops: [{p, matrix, charpoly_free}]}` — `route` `tree` at ell ∈ {2, 3} (the ell-local tree model with the transported lift), `cokernel` at ell ≥ 5 (the presentation M_N / Rel_N with the shipped Heilbronn operator); generators torsion first, then free (each `cocycle` is a cocycle mod ell^K: checked on the generators, mod ell^{K_run} free and mod ell^{K_run − σ_max} torsion, at the export); `matrix` in the column convention (T_p g_j = Σ_i A_ij g_i), row i mod ell^{exponent_i}; `charpoly_free` = det(x − T_p | L/ell^K), high → low. One export per ell at the route's ring width (computed on the first call per ell and cached on the handle) serves every K ≤ `K_max`; the word ring needs ell^K < 2^31, so for ell ≥ 46341 `K_max` ≤ 1 (the field F_ell; K ≥ 2 at such ell is not served at level N > 1). The handle's four bounds (N ≤ 300, n ≤ 60, index(N)(n+1) ≤ 300, Σ p ≤ 100) were checked by `descent`; the method adds: ell a prime < 2^31 and K ≥ 1 (else a type error, exit 3). Not an error: `status` `blocked(export)` with `refusal` `REFUSED [<code>] …` when the export is refused (R-E1: a missing lift, a precision limit, …), `refused` with `[Precision]` when K > `K_max`. A method of a `read_only` type is served without a tag row (tags are per verb overload, §18.8), so `ReadOnlyTags.cpp` / `read_only_verbs.tsv` do not change; §18.5's D-m calls of `DescentRecord` stay none (the served form does not call it). New script `058_s25_descent_module.oc` (new `.expected`). No verb, member, setting, exit code, existing transcript, golden entry or ConsoleDet digest moves; `console.md` and the `[CLI]` tables regenerated.

**Version 3.14.0-pre.5 (2026-10-30, slot-24 NB-FILE; pre-release; front end only).** New **§18.18**: the notebook file. The page opens, inserts and saves a notebook as a plain OC script with `# %%` cell separators (the Jupytext / VS Code percent convention; optional titles; a `# %% [md]` text cell whose body lines all start with `#`; the text before the first separator is a kept preamble, a file with no separator is one cell), so the file is still a valid script and `--script nb.oc` runs every cell. Canonical form (LF, one blank line between cells, one final newline) with a byte-identical round trip; outputs are never saved. *Open notebook…* replaces the cells and restarts the session (asking first when there are unsaved cells), *Insert file as cell…* inserts below the current cell, *Save notebook (.oc)* downloads; drag and drop; *Restart session* resets the execution count. The gateway serves a read-only listing of one fixed directory (`/examples/`, the notebook tour; no path arithmetic). The eight tour files are converted to titled cells; `tour_all.oc` is the whole tour. New script `057_s24_notebook_file.oc`. No protocol, binary, value, existing transcript or golden change.

**Version 3.14.0-pre.4 (2026-10-30, slot-24 NB-OUTBOX; pre-release; front end only).** The notebook page (§18.15) shows a cell as a **code box** (editable; its own *Copy code*) and, below it, a separate read-only **output box** (a thin left rule, no card): hidden until the cell has run, replaced (cleared when the new run starts, never appended to), errors marked, its own *Copy output* (the canonical text behind every display, LaTeX on or off; shown on hover / focus, always on touch). Colab-style state in the code bar: `[ ]` not run, `[…]` queued, `[*]` running (spinner), `[k]` execution count; one cell runs at a time, in submission order (Run all queues every cell; *Interrupt* drops the queued ones). Keys: Shift+Enter run and advance, Ctrl/Cmd+Enter run and stay, Alt+Enter run and insert below. Exports: *Export text* (as before), *Export code* (code only, an `.oc` script) and *Export JSON* (`oc-notebook-export/1`: code and output as separate fields). New `notebook/page/cellbox.js`; tested by `notebook/gateway/test_render.mjs`. No protocol, binary, value, transcript or golden change.

**Version 3.14.0-pre.3 (2026-10-30, slot-24 NB-TOURFIX; pre-release).** (1) `DescentRecord` gains the member `charpoly_factored` (computed, `read_only` with its type): per Hecke prime `{p, status, expanded, factored, factors: [{coefficients, degree, multiplicity, irreducible}], complete, verified, note}`, char_Z(T_p | H^1/tors) factored into irreducibles over Z by Yun's squarefree decomposition and Zassenhaus (in-house, `NumberField/IntPolyFactor.h`; Hensel lifting past Mignotte's bound, exhaustive recombination under a cap; a factor left unseparated at the cap says `irreducible: false`), the product checked against char_Z exactly; a coefficient beyond 2^63 is rebuilt from D3's mixed-radix digits. Presentation only: the record's JSON, text, digest and golden points are unchanged, no transcript moves. (2) **§18.5** gains the hint kind `factored` and the row `DescentRecord` `charpoly_factored[].factors`. (3) The notebook tour files each state the `coefficient_ring` they need, and `08` restores the default `F_ell` at its end, so the files run in any order in one session (§18.2: a setting persists across cells; there is no reset op, `reset_settings()` or the page's restart drop it).

**Version 3.14.0-pre.2 (2026-10-29, slot-24 NB-RENDER R3 + R4; pre-release).** From `NOTEBOOK_render_audit_1029.md` §5 (packages NB-R3, NB-R4; owner decision O2 = a new verb, not value frames for `print`). (1) **A new core verb `display(x, ...)`** (`read_only`, group `core`, registered right after the core printing verbs; §4.3, §18.4): it forces each declared handle among its arguments (as `compute` does) and then shows each argument — **in a served session** exactly what a bare expression statement sends (the canonical echo on `stdout`, then one `value` frame per argument, at the call's `line` / `col`, `stmt` = the enclosing statement), **elsewhere** one `show(x)` line per argument. `print` is unchanged, so no served text and no transcript moves. (2) **§18.5** grows within `json_version` 1: three hint kinds, `cyclic` (exponents e_i of ⊕ Z/ell^{e_i}; `ell`), `eigen` (a character value P_p(w) in F_ell[w]/(π_w) ≅ F_{ell^f}; `f`) and `lesmap` (one map of the Dickson long exact sequence by name, with `n`, `n_up`); an attribute `key=@name` is resolved like the ring parameters; a `nil` at a hinted path carries no hint. New rows: `hecke_ring_algebra/v1` `blocks[].torsion` (`cyclic`), `blocks[].A1_hilbert` / `AK_hilbert` (`hilbert`); `MaximalIdeal` `character()` (`eigen`); `DicksonLES` `maps.theta0` … `maps.pi1` (`lesmap`). The Record of `hecke_ring_algebra` gains its first key `schema = "hecke_ring_algebra/v1"` (no other value moves; no transcript prints it). (3) **The render-coverage gate** (§18.5 "coverage"): `Console/serve/render_coverage.tsv` states, for every core kind, registered type and Record schema, how the page renders it (`tex` / `hint` / `table` / `allow` with a reason); `ConsoleReadOnlyTagValidation` arm (R) checks it in both directions against the registry, the verb sources' `schema` sites, `render_hints.tsv` and the `toTeXRaw` / `hintTeX` cases of `notebook/page/render.js`. `ConsoleServeValidation` arm (K) checks `display`. (4) **The page** (§18.15): a declared value gets a **compute** button (evaluates `display(<the statement>)`), a shape-only Matrix a **show all** button (raises `print_max_entries` to its size for one `display(...)`, then restores it; up to 100 000 entries, the frame cap); the course-ordered tour `notebook/examples/notebook/01…08_*.oc` renders through `display`. (5) **Slot-close duty**: one `OC_BUILD_NOTEBOOK=ON` build, `GATEWAY_TEST … verdict=OK` and `RENDER_TEST … verdict=OK` (`docs/implementation/slot-close-notebook.md`). No TeX enters the binary; no value, golden entry, `.expected` transcript or ConsoleDet digest moves.

**Version 3.14.0-pre.1 (2026-10-29, slot-24 NB-RENDER R1 + R2; pre-release).** From `docs/implementation/slot24/NOTEBOOK_render_audit_1029.md` (§5, packages NB-R1 and NB-R2; owner decisions O1 = keep "no TeX in the binary", O3 = add the structural members). **§18.5** grows additively within `json_version` 1: (1) the **member form D-m** for ten types that used the generic form (`HeckeOperator`, `Pairing`, `MaximalIdeal`, `HeckeAlgebra`, `LoewyProfile`, `ExtensionClass`, `BoundaryCohomology`, `ConeCohomology`, `DicksonLES`, `DescentRecord`): `v = {"members":{…},"calls":[[method,[arg],envelope],…]}`, the generic members plus per-type method calls (`A(q)` and `charpoly(A(q))`, `perfect(t)`, `character(p)`, `t(p)`, `jordan(p)`, `matrix(p)`), never forcing a declared handle; (2) `Cohomology` over `Z/ell^k` adds `invariant_factors` (per degree); (3) the optional envelope key **`hint`** (after `state`) from the twin tables `Console/serve/render_hints.tsv` and `PrintJson.cpp`: it tells the page that a List of Int / String at a given path of a Record schema or type is a polynomial (with its order label, variable and ring), a q-series, an abelian group, a Hilbert function, Loewy layers or a Jordan type. Two new **members** of `DescentRecord`, `groups_inv` and `pair_inv` (the integral groups as `{free_rank, torsion: [[p, k, mult], …]}`, read from the record's group type directly; the String members `groups` / `pair` are unchanged). No TeX enters the binary; no value, canonical text, `.expected` transcript, golden entry or ConsoleDet digest moves. The page (`notebook/page/render.js`) renders the new data and gains a LaTeX on/off switch (default on, remembered per browser) and plain-text extraction (per value "text" / "copy", per cell "Copy text", "Export text" for the whole notebook); gated by `ConsoleReadOnlyTagValidation` arm (H) and `notebook/gateway/test_render.mjs` (run by `test_gateway.py`).

**Version 3.13.1 (2026-10-29, slot-24 DOCS-CLI; documents only).** The verb `descent` and its type `DescentRecord`, built at slot-24 D6 (merge `2aa61397`) and so far written in only through the `coefficient_ring` wording of 3.13.0, get their **§3.6 row** after `hida_lambda` (signature, limits, the members of `DescentRecord`, the torsion-invariants grammar by reference to `[C]` `prop:torsionhecke`(1); text as generated in `console.md`). New frozen scripts `054_s24_descent.oc` and `055_s24_language_tour.oc` (served verbs only, so `ConsoleServeValidation` arm (B) compares them byte for byte; no `set threads`, no file access). No verb, type, member, setting, exit code, canonical printer, existing transcript or ConsoleDet C4 (a) digest moves.

**Version 3.13.0 (2026-10-26, slot-24 D6 wording fix; documents only).** `coefficient_ring = Z` is no longer described as refused. As built at slot-24 D6 (merge `2aa61397`; `slot24/DESCENT6_report.md`; `[C]` v1.23.0-pre.37 `sec:recordschema` item 7 and `def:ringsemantics`(3), `[E]` 1.23.0-pre.1 `sec:ring` (a)): `Z` is **stored** by `MathSettings::set()` (k = 0, canonical text `Z`, non-zero fingerprint) and **honoured by the integral descent only** (the verb `descent`, the type `DescentRecord`, the campaign's descent cells, the record `integral_descent_record/v1`); **every other consumer refuses it by name with exit 5** (`CoefficientRingK(who)`, `GateVerbsOnField`), also on a `set` statement's next verb and after `--set coefficient_ring=Z`; `--set coefficient_ring=Z` itself is **legal (exit 0)**. `Z/<m>` stays reserved (refused inside `set()`, exit 5 on `set` and on `--set`). Corrected in place: §2 C4 item 3 (v3.6 summary), the C4 row of the §2 change table, the `coefficient_ring` row of the settings table, the exit-code paragraph of §6, and the §8 row on legal-but-unexecutable settings; the old texts stay as history where marked. No verb, type, member, setting, exit code, transcript or digest moves; `console.md` and `[CLI]` tables are not regenerated (unchanged).

**Version 3.12.0 (2026-10-12, slot-22 CLOSE-T): the release of 3.12.0-pre.1; only the version changes.**

**Version 3.12.0-pre.1 (2026-10-08, slot-22 DOC22; pre-release).** Two additions, both writing in what already exists. (1) **§18.17**, the page themes (FR-1, client-side only), from `docs/implementation/slot22/nbtheme_report.md`: no route, verb, setting, CLI token or `read_only` tag moves. (2) The **verbs of slots 21 and 22 not yet written in**, as rows after `lfunction` in **§3.6** (all tagged `read_only`, text from `console.md` as generated; scripts 050-053): `pow`, `kummer_unit`, `hida_tower` (slot 21), `level_n`, `nebentypus`, `forms_algebra`, `hida_lambda` (slot 22, WP-VERB-2). No type, member, setting, exit code, canonical printer, transcript or ConsoleDet digest moves. Counts of verbs and overloads: see `console.md` and `[CLI]` (generated).

**Version 3.11.1 (2026-10-04, slot-20 stretch S1): the verb `lfunction`.** One new row in **§3.6** (after `theta`): `lfunction(n, ell, a, M = 2, R = 4, sign = "minus", sep = nil)` → Record, one branch of the record `lfunction/v1` of `[E]` 1.20.0-pre.5 `sec:lvlfunction` (`def:lvlfun`, `lem:lvlfunprec`, `rmk:lvlfunschema`): the truncated one-variable `ell`-adic L-function `L_a(T) mod (ell^R, omega_{M-1}(T))` of the `ell`-stabilised MTT measure, its `T`-coefficients with their certified precision, `mu`, `lambda`, the critical values. Tagged **`read_only`** (pure in-memory arithmetic; one row in `Console/Bindings/ReadOnlyTags.cpp` and in `Console/serve/read_only_verbs.tsv`). No type, member, setting, exit code, canonical printer, transcript or ConsoleDet digest moves; `docs/console/console.md` and the `[CLI]` tables regenerated in the same commit.

**Version 3.11 (2026-10-04, slot-20 NB-4): the atlas sidecar and `--serve-atlas`.** One new subsection, **§18.16**: the index sidecar `oc-atlas-index/1` of a `hecke_atlas/v1` store (written only by the owner's one-off `--atlas --index`, keyed to the store's size and FNV, checked field by field at every open, a stale one refused), the read-only process mode `hacs --serve-atlas` (protocol `oc-serve-atlas/1`: the §18.9 environment gate and hardening reused, the store opened `O_RDONLY` and mapped `PROT_READ`, the queries `info` / `cells` / `cell` / `system` / `systems` with paged, capped replies), the gateway's `--atlas-store`, the page's atlas panel, and the validation `ConsoleServeAtlasValidation` (`standard`; `[SKIP]` with `OC_BUILD_NOTEBOOK=OFF`). `oc-serve/1` is unchanged; no verb, type, member, setting, exit code, canonical printer, `.expected`, `read_only` tag, ConsoleDet digest or golden moves. New CLI tokens: `--serve-atlas` and its modifiers, `--atlas --index` / `--out`.

**Version 3.10.2 (2026-10-04, slot-19 NB-report): `report` split.** A pathless overload `report(D, level_a = false)` is registered first and tagged `read_only`; the file-writing overload `report(D, level_a, path)` keeps its signature and stays untagged (served: `forbidden_overload`). Counts become **158 tagged / 9 not** (167 overloads, **148** of 154 verbs served); `Report.write(path)` is disabled in a served session (`bind::ForbidReportWrite`). Scripts `006_flagship` and `012_report_schema` join arm (B)'s byte-for-byte set; `014_expect_error` stays exempt, now as `forbidden_overload` (its pinned text `argument 'path' expects String` is still a substring of the two-overload `TypeError`). No `.expected`, ConsoleDet digest or golden moved. Details: §18.14 (g).

**Version 3.10.1 (2026-10-04): the served console BUILT** (hecke-extensions slot 19, package NB-2). §18 is implemented as
specified, with the as-built record of **§18.14** (the four points NB-1 left open, and every place the build is more precise than
the text). The `read_only` audit moved nothing: **157 tagged / 9 not** on the slot-18-close registry (166 overloads, 147 served
verbs). Two validations registered (`ConsoleReadOnlyTagValidation` `fast`, `ConsoleServeValidation` `standard`; `[SKIP]` with
`OC_BUILD_NOTEBOOK=OFF`). **One additive Core API**: `Registry::transform_overloads` (§18.14 (a)); no Core semantics, verb, type,
member, setting, exit code, canonical printer or `.expected` moved; ConsoleDet C4 (a) `0xf6ed04bbe8e6b60a`, golden 11827 / 6231
unchanged.

**Version 3.10 (2026-10-03): the served console — `--serve`, protocol `oc-serve/1`** (hecke-extensions slot 19, package NB-1;
specification only, no code: built by NB-2 under `OC_BUILD_NOTEBOOK`; `docs/implementation/slot19/NB-1_note.md`). One new
section, **§18**: the `--serve` CLI token (newline-delimited JSON on stdio; one process = one session), the request / reply frame
schema and session lifecycle, the mapping of exit codes 1–5 to structured `done` replies (the session keeps running), `PrintJson`
(a versioned, deterministic JSON envelope for every console type — **no TeX printer**: LaTeX is rendered only in the notebook, owner
decision 2026-10-03), the **`read_only` verb tag** (per overload, default *not* read-only; which overloads are tagged; shown in the
manual's verb table), environment scrubbing (the owner-gated emitters and every env hook are refused in a served session), the RSS
cap and `fatal` frame, the LAN rules as gateway requirements, and the conformance tests NB-2 must implement
(`ConsoleReadOnlyTagValidation`, `ConsoleServeValidation`, the latter comparing served text with the `.expected` transcripts byte for
byte). **Nothing in §1–§17 moves**: no verb, type, member, setting, exit code, canonical printer, transcript or ConsoleDet digest.
Companion documents of v3.10: `[C]` **v1.18.0**, `[E]` **1.18.0**, `[X]` **v1.23**.

**Version 3.9.3 (2026-09-26): Q9 decided (a) — the console's `uint32_t` gap is closed** (hecke-extensions
slot 12, post-close package WP-17, owner-approved 2026-09-26; `docs/implementation/slot12/WP-17_report.md`).
The owner ruled **Q9 → (a)**: under `coefficient_ring = Z/ell^<k>` with `2^32 ≤ ell^k < 2^64` and `ell ≥ 5`
the console serves `symmetric_power`, `cohomology` and `hecke(H, p)` (`r = 1`) through the **native
pipeline's `uint64_t` instantiation**, exactly as the campaign job loop does (`Campaign/CampaignRing.cpp`,
`RunRingPipeline<uint64_t>`) — the **wide band** (`Z/5^14 … Z/5^27`, `Z/691^4 … Z/691^6`, which refused
until now). A wide handle honours exactly the members a `uint32_t` ring handle honours, with the same
values as the campaign; the field members exit 3; every other member keeps its exit 5
(`bind::GateTypeOnWide`, the digit gate's mechanics). An entry of a wide handle that does not fit the
console's `int64` `Int` (`ell^k > 2^63`, e.g. `Z/19^15`) is its decimal **String** (Q7 unchanged: no
bignum). **§3.6** — the wide handles as built; **§8** — no row, no exit code; **§10** — a phase row "wide
band"; **§11** — `ConsoleErrorValidation` arm **(Q9)**, **539 checks** (still `fast`), script
**`028_wide_band`** (a first freeze, **37** numbered scripts), `ConsoleScriptValidation` **358**; **§16** —
Q9 **decided (a)**. **Nothing in `Console/Core/` moved**; the 36 pre-existing `.expected` files and
`cli_frozen/` are byte-unchanged; C4 (a) digest `0xf6ed04bbe8e6b60a` unchanged; `console.md` unchanged
(no verb, type, member or setting was registered; `gen_console_md.sh --check` current). Each site is
marked *v3.9.3* where it moves. Companion documents of v3.9.3: `[C]` **v1.12.0-pre.2**, `[E]` **v1.12.1**,
`[X]` **v1.16**.

**Version 3.9.2 (2026-09-26): phase θ built as specified** (hecke-extensions slot 12, package WP-8;
`docs/implementation/slot12/WP-8_report.md`). §3.6's v3.9-pre.1 rows — the type `DicksonLES` with the
verb `dickson_les(n, ell)` and the verb `theta(H, H_up)` — are **registered**, in
`HeckeExt/RegisterHeckeExtensionVerbs.cpp` (the one `Console/`-including TU of the extension layer, as
§3.6 and phase θ's scope item 2 say; `Console/Core/` and `Console/Bindings/` untouched), on slot-11
WP-5 / WP-6's `HeckeExt/HeckeDicksonTheta` / `HeckeDicksonThetaHecke` — no second implementation.
§8's θ rows hold as specified (no new row, no new exit code), pinned by `ConsoleErrorValidation`'s new
arm **(T)** (still `fast`, **347** checks); script **`027_dickson_theta`** is a first freeze (**36**
numbered scripts); the 35 pre-existing `.expected` files and `cli_frozen/` are byte-unchanged; C4 (a)
digest `0xf6ed04bbe8e6b60a` unchanged (it hashes the 16 C1 scripts only); `console.md` regenerated. Each
site is marked *v3.9.2* where it moves. Companion documents of v3.9.2: `[C]` **v1.12.0-pre.2**, `[E]`
**v1.12.1**, `[X]` **v1.15**.

**Version 3.9.1 (2026-09-25): the slot-11 close — two wording repairs, no row moves** (hecke-extensions
slot 11, package WP-17; `docs/implementation/slot11/WP-17_report.md`). **§10**'s schedule row "Digit
handles" named `af1617e` as the merge of `[E]` v1.12.0-pre.2; it is the spec commit itself (slot-11
WP-18c, "spec first") — the slot-11 WP-15 referee's m-5. **§3.6 / §8's θ rows**: `ell < 5` → exit 3
(the `ENGINE_CHECK_MSG` naming `lem:h2torsion`) was specified and is unchanged; since slot-11 WP-17 the
build agrees (`DicksonThetaCell` no longer throws `NotImplementedInThisBuild` there — the referee's
ruling on F-2), so a later binding of the θ verbs inherits no code conflict. No verb, type, setting, exit
code, transcript or `Console/Core/` line moves; `console.md` is not regenerated (nothing it reads moved).
Companion documents of v3.9.1: `[C]` **v1.11.1**, `[E]` **v1.12.1**, `[X]` **v1.15**.

**Version 3.9 (2026-09-25): the slot-11 console rows as built** (hecke-extensions slot 11, package
WP-15; `docs/implementation/slot11/WP-15_report.md`). v3.9-pre.1 with every site it specified
recorded as built or not built, plus the one console surface slot 11 *did* build, which no pre-release
of this plan specified — `[E]` v1.12.0-pre.2 (h) did, and `[E]` owns it: **the digit handles** of
slot-11 WP-18c (`symmetric_power`, `cohomology` and `hecke(H, p)` at `ell^k ≥ 2^64`, `ell ≥ 5`;
`bind::GateTypeOnDigit`; the new member `Cohomology.precision`). What moves (§0's v3.9 entry), each
marked *v3.9* at its site: **§3.6** — the digit handles as built, the field members **exit 3** on a
digit handle as on every ring handle (slot-11 WP-14 pass 2, M-1), every other member off `[E]` (h)'s
digit list exit 5; the θ verbs **not built** (slot-11 WP-16 gave way under the owner's re-ruling of
decision 3, `[S11]` §10), recorded as specified; **§2 C4** — `coefficient_ring`'s grammar `k ≤ 4096`;
**§8** — the digit rows; **§10** — phase θ "specified, not built", a phase row "digit handles" (built,
slot-11 WP-18c); **§11** — `ConsoleErrorValidation` (K)'s digit rows, 309 checks; script `027_` not
frozen; **§16** — Q7 re-read against the digit route (unchanged: no bignum), and **Q9, an open owner
item**: the console's `uint32_t` gap below `2^64` (`Z/5^k` for `14 ≤ k ≤ 27`, `Z/691^k` for
`4 ≤ k ≤ 6` refused, while larger `k` is served). **Nothing in `Console/Core/` moved**; the 35
`.expected` transcripts and `cli_frozen/` are byte-unchanged; nothing of v3.9-pre.1 is removed.
Companion documents of v3.9: `[C]` **v1.11.0**, `[E]` **v1.12.0**, `[X]` v1.14.1.

**Version 3.9-pre.1 (2026-09-25): θ and the Dickson long exact sequence at the console, specified
before it is built** (hecke-extensions slot 11, package WP-4, spec first;
`docs/implementation/slot11/WP-4_report.md`). A pre-release of v3.9 with its own identifier, so
that no version number is published twice under different text; slot-11 WP-15 publishes v3.9 with
what slot-11 WP-16 built at the same sites. Written under the owner's rulings of 2026-09-25 on the
slot-11 decisions, every one at recommendation (decision 3 at (A′); `[S11]` §10); decision 5 (A) is
the one used here — **WP-16 is as schedule permits**, so this pre-release specifies a phase that may
be stopped at the close, in which case v3.9 records it as specified, not built. **Nothing below is
provisional.** What it specifies (§0's v3.9-pre.1 entry), each marked *v3.9-pre.1* at its site:
**§3.6** — the `DicksonLES` type with `dickson_les(n, ell)` and the verb `theta(H, H_up)`, on
slot-11 WP-5 / WP-6's `HeckeExt/HeckeDicksonTheta` (`[E]` v1.12.0-pre.1 `sec:thetaobj`); a census
verb recorded **not bound** (the catalogue `hecke_census/v1` is a derived artefact, `[E]`
`sec:census`); **§8** — no new row or exit code: both verbs refuse a non-default `coefficient_ring`
with exit 5 (θ is `F_ell`-only in slot 11, `[E]` `sec:ring` (b)); **§10** — a phase row "θ" (slot
11, WP-16) with its step-1 transcript guard; **§11** — script `027_`, one new arm letter. **Nothing
in `Console/Core/` moves**; nothing of v3.8 is removed or loosened. Companion documents of
v3.9-pre.1: `[C]` **v1.11.0-pre.1**, `[E]` **v1.12.0-pre.1**, `[X]` v1.14.1.

**Version 3.8 (2026-09-25): the C5 leftovers, as built** (hecke-extensions slot 10, package WP-15;
`docs/implementation/slot10/WP-15_report.md`). v3.8-pre.1 with every site it specified recorded as
slot-10 WP-12 built it (`3c96d63`, merged at `6726075`; `docs/implementation/slot10/WP-12_report.md`),
each marked *v3.8* at its site; no design decision changes, no acceptance item is dropped or
loosened, and nothing of v3.8-pre.1 is removed. What moves (§0's v3.8 entry): **§2 C7** — the one
named `Console/Core/` exception is built at its two sites and nowhere else, and is **recorded as an
exception** to C5's acceptance (b), the third beside C5a's two; **§3.6** — the five structural
members honour, the ring-mismatch rule is pinned both ways; **§6, §8** — the member-getter position,
and the one exit code that moves by the exception's own rule: an **unwrapped** getter raising
`hecke::NotImplementedInThisBuild` is **exit 5** (it was 3); the two campaign verbs' handler, with
the exit-5 branch recorded **unreachable** by any input at the base; **§10** — "C5 leftovers"
**IMPLEMENTED**; **§11** — `ConsoleErrorValidation` 294 checks (arm (W)), 35 numbered scripts with
`026_`, `ConsoleScriptValidation` 350, `ConsoleDeterminismValidation` 570, the roster 129 at this
version's base; **§16.4** — the member-getter follow-up done. None of slot 10's lane-B packages
(WP-7, WP-8) touches the console, so this version has no phase-2 site. Companion documents of v3.8:
`[C]` **v1.10.0**, `[E]` **v1.11.0-pre.2** (v1.11.0 in the same package's second phase), `[X]` v1.13.

**Version 3.8-pre.1 (2026-09-25): the C5 leftovers, specified before they are built**
(hecke-extensions slot 10, package WP-2, spec first; `docs/implementation/slot10/WP-2_report.md`).
A pre-release of v3.8 with its own identifier, so that no version number is published twice under
different text; slot-10 WP-15 publishes v3.8 with what slot-10 WP-12 built at the same sites. Written
under the owner's rulings of 2026-09-25 on the slot-10 decisions, every one at recommendation (A)
(`[S10]` §10); decision 6 is the one used here, and **nothing below is provisional**. What it
specifies (§0's v3.8-pre.1 entry), each marked *v3.8-pre.1* at its site: **§2 C7, §6, §8** — a
member getter's error carries `file:line:col` (decision 6 (i), **one named `Console/Core/`
exception**: `Evaluator::object_member`'s wrap, and the same back-fill around the type-level
`resume` hook); `run_campaign` and `campaign_plan` map `hecke::NotImplementedInThisBuild` to
**exit 5** (decision 6 (iii), the WP-8c pattern), every other exception keeping exit 3; **§3.6** —
the five structural members of a ring handle that honour (decision 6 (ii); `[E]` `sec:ring` (h)'s
v1.11.0-pre.1 block, which owns the list); **§10** — a "C5 leftovers" phase row; **§11** — the new
scripts from `026_`, `ConsoleErrorValidation`'s new arm; **§16.4** — the member-getter follow-up
scheduled. Nothing of v3.7.1 is removed or loosened. Companion documents of v3.8-pre.1: `[C]`
v1.9.1, `[E]` **v1.11.0-pre.1**, `[X]` v1.13.

**Version 3.7.1 (2026-09-25): the Fable referee's repairs to v3.7, and C5c's console surface as
repaired by slot-9 WP-8c** (hecke-extensions slot 9, package WP-17, the slot close;
`docs/implementation/slot9/WP-17_report.md`). No design decision changes and no acceptance item is
dropped or loosened. What moves (§0's v3.7.1 entry): **§8 and §6 name the harness verbs' behaviour
on a `hecke::NotImplementedInThisBuild`** (referee m-6), which slot-9 WP-8c (`cc3d30a`, merged at
`bdbb93c`) changed after v3.7 was written: `campaign_spec` / `campaign_spec_text` now surface a
spec-validation ring refusal as **exit 5**, not 3 (`ConsoleErrorValidation` arm (M)); **§10 C5c**:
the exit-3 observation is resolved, and C5c is pinned from the console by the first-freeze script
`048_c5c_ring_campaign` (no verb, type or member added; `console.md` unchanged); **§11**: 34
numbered scripts, `ConsoleScriptValidation` 346 checks, `ConsoleErrorValidation` 218; the roster
stays **125**; the v3.7 header's "nothing else" sentence gains the clause the referee asked for
(m-10). Companion documents of v3.7.1: `[C]` **v1.9.1**, `[E]` **v1.10.1**, `[X]` **v1.13**.

**Version 3.7 (2026-09-25): C5 implemented — C5a, C5b and C5c as built, the Core batch, the C5
binding list as shipped** (hecke-extensions slot 9, package WP-15, **phase 2**;
`docs/implementation/slot9/WP-15_report.md`). v3.7 is the first text under this number: it is
v3.7-pre.1 (WP-15 phase 1, below) with every site phase 1 marked for phase 2 filled from the lane-B reports
(slot-9 WP-6 … WP-9 and WP-4t), at base `9b004f2` (every slot-9 code package merged). The Fable
referee reads v3.7; its repairs go to v3.7.1. What phase 2 adds (§0's v3.7 entry): C5c as built
(§10 C5, the schedule row); `ConsoleDeterminismValidation`'s wall after slot-9 WP-6 and the
disposition of S8-D3's ratification (§11); `CampaignRingValidation`'s row and the roster at the
base, **125** (§11). Companion documents of v3.7: `[C]` **v1.9.0**, `[E]` **v1.10.0**, `[X]` v1.12.
*(v3.7.1, referee m-10: "every site phase 1 marked for phase 2 filled" is to be read with "plus the
two notes the §0 table lists", §2 C4's engine-knob note (slot-9 WP-6) and §4.1's lock note (slot-9
WP-7), which v3.7-pre.1 had not marked as slots.)*
The v3.7-pre.1 header follows; its sentences on the markers are restated in the past tense.

**Version 3.7-pre.1 (2026-09-24): C5a and C5b as built, the Core batch, the C5 binding list as
shipped** (hecke-extensions slot 9, package WP-15, **phase 1**; `docs/implementation/slot9/WP-15_report.md`).
A pre-release of v3.7, with its own identifier so that no version number carries two texts: the
slot's lane-B packages (WP-6 … WP-9) were still running when it was written, and the sites they
completed were marked for phase 2; WP-15's phase 2 filled them and published **v3.7** (above).
Sources:
* the slot-9 plan (`docs/implementation/hecke_extensions_slot9_plan.md`, `[S9]`) §3 WP-12, WP-13,
  WP-15 and §10 — the owner's rulings of 2026-09-24, all at recommendation (A): decision 2 (i) (A)
  C5 in three lanes (C5a WP-12, C5b WP-13, C5c WP-8), 2 (ii) (A) the two `Console/Core/` edits
  authorised as named exceptions;
* slot-9 WP-12's report (`[WP9-12]`, `docs/implementation/slot9/WP-12_report.md`) §1, §4, §5;
* slot-9 WP-13's report (`[WP9-13]`, `docs/implementation/slot9/WP-13_report.md`) §1, §2, §7, §8;
* `[E]` v1.10.0-pre.2 `sec:ring` (a), (h).

Base `7ddb555`, every slot-9 package but lane B's merged; every count below was measured there on
a fresh out-of-source `RelWithDebInfo` build. **No design decision changes and no acceptance item
is dropped or loosened.** What moves:
1. **C5a and C5b are implemented** (§10 C5): C5a by slot-9 WP-12 (`b3cd0d3`, merged at
   `4bf2289`) — E7's `ContragredientLocalSystem` / `Pairing` and E8's ring lift at `ell ≥ 5`;
   C5b by slot-9 WP-13 (`80eb184`, merged at `53066cd`) — the extension-layer bindings and the
   local-algebra verbs; their follow-up `f28a0fa`. **C5c** (the campaign, slot-9 WP-8) was
   left to phase 2; v3.7 records it (§10 C5).
2. **The Core batch** (decision 2 (ii) (A)), the two named exceptions to C5 (b): a `set`-statement
   refusal carries its `file:line:col`, and a **legal but unexecutable `--set` value is exit 5**
   (an invalid value and an undeclared key stay exit 1). §6, §8, §2 C4, §2 C7, §11.
3. **The binding list as shipped** (§3.5, §3.6): the reserved names as bound, the spellings the
   build chose — **`settings_snapshot()`** (because C1a's `math_settings()` already returns a
   Record) and the **`gf_*`** verb family (because C1a's arithmetic verbs take `any`, so a typed
   overload could never be reached) are recorded as the binding spellings — and what is not bound
   (`MatrixQ`, `PairComplex`, `divided_power`, G15, G16).
4. **Four as-built facts** of C5a (`[WP9-12]` §4): member getters carry no source position (a
   next Core batch, §16.4); unlisted structural members of a ring handle exit 5; a ring mismatch
   is exit 5; `.A(q)` over the ring is a List of rows.
5. **`gen_console_md.sh` takes the binary's path** when the build is not in `./build/` or the
   repository root (§4.4).

Companion documents: `[C]` **v1.9.0**, `[E]` **v1.10.0-pre.2** (published as v1.10.0 in WP-15's
phase 2), `[X]` v1.12.

**Version 3.6.1 (2026-09-24): the referee repairs of v3.6** (slot-8 WP-13, Fable referee pass,
`docs/implementation/slot8/WP-13_report.md` §7). A `Y`-type revision: pointers and evidence only.
No design decision, acceptance item or rule moves. The repairs:
* **§6, the `--set` exit code** (finding M-1). v3.6 stated that exit 1 was measured, but the
  evidence run had a mis-ordered argv and never selected the console branch. The code was
  re-measured correctly (still 1), and it is now pinned by one check in
  `ConsoleErrorValidation` arm (K).
* **§1 and §5's "Today" column** (finding m-5). The stale `BenchDriver` / `CampaignDriver` /
  `kernel.cu` pointers are re-read at `5c70e95`.

Finding m-6 ("Thirteen keys" in §2 C4 is annotated, not rewritten) is kept as is: the referee
accepted the annotation, and the paragraph is v3.2's inventory. Companion documents: `[C]` v1.8.0,
`[E]` **v1.9.1**, `[X]` v1.11.

**Version 3.6 (2026-09-24): C4 as built, the slot-7 queue P-1 … P-5 applied, `coefficient_ring`,
C5 moved to slot 9.** Written by hecke-extensions slot 8, package WP-13. Sources:
* the slot-8 plan (`docs/implementation/hecke_extensions_slot8_plan.md`, `[S8]`), §3 WP-13;
* the owner's rulings of 2026-09-24 in `[S8]` §10: all at recommendation, in particular ruling 4
  (A) on `coefficient_ring` and ruling 8 (A), C4 in slot 8 and C5 in slot 9;
* slot-8 WP-10's report (`[WP8-10]`, `docs/implementation/slot8/WP-10_report.md`) §7.2;
* slot-8 WP-3's report (`[WP8-3]`, `docs/implementation/slot8/WP-3_report.md`) §3 and §4 (d).

Base: `5c70e95`, with every slot-8 code package merged. Every pointer below was re-read there.
**No design decision changes, and no acceptance item is dropped or loosened.** One spelling is
recorded as built (§4.4), one tier note is restated (§11), and one known gap is recorded and
scheduled (§6). What moves:
1. **C4 is implemented** by slot-8 WP-10. Its commits are `da2e591` and `101a221`, merged at
   `e8aeeb4`, with the WP-3 × WP-10 follow-up `06bebdc`. Acceptance (a), (b) and (c) are met. (d)
   is measured, and indicative only: 0.49 s against 5 s. The verdict is the lead's window. See §10
   C4.
2. **`help --markdown` ships as the binding verb `help_markdown()`**, because `Console/Core/` was
   frozen in slot 8 (`[S8]` §3.0, the shared-file rule). `docs/console/gen_console_md.sh`
   regenerates `docs/console/console.md`, and `--check` reports whether the file is stale (§4.4,
   §9).
3. **`coefficient_ring` is registered** (slot-8 WP-3, `[E]` v1.9.0 `sec:ring`). It is the eleventh
   mathematical key, and the console refuses it:
   * the reserved `Z` / `Z/<m>` on the `set` statement exit 5;
   * every pipeline verb under `Z/ell^<k>` exits 5, through a lazy handle too;
   * a `--set` argument naming a reserved value exits 1, as every `--set` refusal does.

   *(v3.13.0, slot-24 D6: of these, `Z` is no longer reserved. It is stored and honoured by the integral descent only — the verb `descent`; every other verb under `Z` exits 5 naming itself; `set coefficient_ring = "Z"` is legal and `--set coefficient_ring=Z` exits 0. `Z/<m>` stays reserved as listed. `[C]` `sec:recordschema` item 7, `def:ringsemantics`(3); `[E]` `sec:ring` (a).)*

   **Known gap, deferred to C5 in slot 9:** the `set`-statement refusal carries no
   `file:line:col`. Closing it takes a one-line `Console/Core/` edit, and Core is frozen in slot 8.
   It is an owner item (§2 C4, §6, §8).
4. **The slot-7 close's queue P-1 … P-5 is applied** (the status block below; §5, §10 C2b, §11,
   §14).
5. **C5 moves to slot 9** (ruling 8 (A)). Its binding list is extended by E7's and E8's types, and
   it takes on the campaign and record support for `Z/ell^k` (ruling 4 (A)) (§10 C5, schedule).
6. **§11**: `ConsoleDeterminismValidation`'s tier note "≈ 5 s" is restated as measured: ≈ 25–30 s,
   531 checks. It stays `standard`, and re-tiering it is an owner item. `ConsoleErrorValidation` is
   shipped.

Companion documents at this revision: `[C]` **v1.8.0**, `[E]` **v1.9.0** and `[X]` v1.11.

**Version 3.5 (2026-09-23): C2b as built, (h) restated at the engine level, C4 moved to slot 8.**
Written by hecke-extensions slot 7, package WP-12, from the slot-7 plan
(`docs/implementation/hecke_extensions_slot7_plan.md`, `[S7]`), §3 WP-12 and the owner's rulings of
2026-09-23 in its §10: decision 6 (A) and confirmation 12. The C2b facts come from slot-7 WP-8's
commits `fee4690` (G4, G4b), `2855084` (G9, G14) and `3d0322e` (the harness verbs, `--log`,
script 022 and `ConsoleDeterminismValidation`). WP-8 is **not yet merged** at this revision's base
`4b6e88a`, so each C2b item below is described **as WP-8 built it**, and its acceptance is the
lead's. *(v3.6, P-1: merged at `4508641` and accepted by the lead; see the slot-7 close block
below.)* **No design decision changes, and no acceptance item is dropped or loosened.** What moves:
1. **The surface follows what was built, or is marked deferred.** The console has no float type,
   so times and MiB figures are **Strings** with **Int twins** in micro-units
   (`total_us`, `wall_us`, `peak_rss_kb`). The campaign plan verb is **`campaign_plan(spec)`**,
   not `plan(spec)`, and the campaign runner is **`run_campaign`**. Three things are **deferred**
   and unbound, with none of C2b's acceptance items depending on them: **`run_validations`**,
   **`time`** and **`single_job`**. **`micro("cuda")`** is refused as **CLI-only**
   (`--bench micro cuda`).
2. **C2 (h)'s "a resume on a complete state is a strict no-op" is restated at the engine level**
   (owner decision 6 (A)). The strict no-op is `HeckeModuleDecomposition::resume_locality` on a
   complete state, and `ConsoleSettingsValidation` asserts it. At the console, `resume` on a
   complete handle is a **typed refusal** ("is complete"). That refusal is recorded as
   **conforming**, and the frozen transcript `014_expect_error.expected` that pins it is **kept**.
   No transcript is re-baselined.
3. **C4 moves to slot 8** (owner confirmation 12). Its gate stays "C2b accepted".

The two pointer corrections queued at the slot-6 close are applied (§10 C4 (d); the companion
pointer). Companion documents at this revision: `[C]` v1.7.3, `[E]` **v1.8.0** and `[X]` v1.10
(v1.11 at the slot-7 close).

> **Status at the slot-7 close (2026-09-23, `[S7]` WP-14; status only, nothing in v3.5 changes).**
> The companion documents are now `[C]` **v1.7.4**, `[E]` **v1.8.2** (v1.8.1 was slot-7 WP-13's
> referee pass on v1.8.0, v1.8.2 the close's status bump) and `[X]` **v1.11**. **v3.5 was
> accepted as written** by the slot-7 referee (WP-13, `docs/implementation/slot7/WP-13_referee.md`
> §1 check 6). **C2b is implemented, merged and accepted**: WP-8's commits `fee4690`, `2855084`
> and `3d0322e` reached `hecke-extensions` **without a rebase** in the merges `cb1a874` (G4, the
> staged extraction, byte identity 45 / 0) and `4508641` (the rest), and `git diff 3d0322e 4508641
> -- Console Bench Util Campaign` is empty, so every SHA cited above is valid at the merged head.
> Five items that v3.5 states correctly **at its own base** are stale after the merge (WP-13
> P-1 … P-5); they are recorded here and are **queued as pointer corrections for v3.6**, the body
> being v3.5's published text. *(v3.6: all five are applied in the body, each at its site and
> re-read at `5c70e95`; the pointers of P-2 and P-4 had drifted again, and §0 gives their values
> there.)*
> 1. **(P-1)** the header's "WP-8 is not yet merged … its acceptance is the lead's" and §10 C2b's
>    "not merged at this revision's base, and its acceptance is the lead's" now read: merged at
>    `4508641`, accepted by the lead.
> 2. **(P-2)** §5's "Benchmarks" row, "gap G4: today only `bench::RunBench(argc, argv)` is public
>    (`BenchDriver.h:51`); `RunCohom/…` (`BenchDriver.cpp:265/299/363/424`) … sit in an anonymous
>    namespace", is **closed**: `bench::RunMode(const ModeArgs&) -> BenchRecord` is public at
>    `Bench/BenchDriver.h:102`, `RunBench` at `:132`, the four runners at
>    `BenchDriver.cpp:302/336/400/461`.
> 3. **(P-3)** §14.1's row `bench::RunBench(argc, argv)` / "`bench` (argv route until G4)" is stale;
>    §14.2's rows **G4, G4b, G9, G14 are CLOSED** (the G5 pattern) — G4 and G4b by `fee4690`
>    (`bench::RunMode`, `Util/Rss.h`), G9 and G14 by `2855084` (`hecke::IsDicksonExceptional` in
>    `Hecke/DicksonCount.h`, `Hecke/HeckeLinAlg.h`).
> 4. **(P-4)** line pointers that had drifted before WP-8: §5 and §14.1's `CampaignSpec.h:169-170,
>    177, 180` are `CampaignSpec.h:358-359, 366` and `CampaignDriver.h:164, 169-170, 174, 178` are
>    `CampaignDriver.h:188, 193, 202` at `4508641`.
> 5. **(P-5)** the counts re-verified at the close: **22** numbered scripts, **21** pre-existing
>    `.expected` files byte-unchanged plus `022_harness.expected` (WP-8's first freeze);
>    `ConsoleDeterminismValidation` **122** checks; G9 on **366** cells — re-verified by the close's
>    second commit: `ConsoleDeterminismValidation` 122 checks, 0 failing, and `ConsoleScriptEmit`
>    rewriting all 22 transcripts byte-identically. No
>    numbered script was added after `4508641`.
>
> **The registered roster is 108** (43 `fast`, 56 `standard`, 9 `slow`; 61 `Hecke*`), the
> two new names being `ConsoleDeterminismValidation` (`standard`, C2b) and
> `HeckeDualityCoverageSlowValidation` (`slow`, E7). **Mathematical settings**: `presentation` and
> `predictions` were registered in slot 7 (stage 1 (2)), so `hecke::MathSettings::keys()` has
> **ten** keys and `ConsoleSettingsValidation` counts ten — C2 (g)'s "every key `keys()`
> registers" holds as restated in v3.4. **C4 and C5** remain slot 8's (confirmation 12).

**Version 3.4 (2026-09-22) — C2 split, and four acceptance clauses restated**, written by
hecke-extensions slot 6, package WP-11, on the slot-6 plan
(`docs/implementation/hecke_extensions_slot6_plan.md` §2.3 item 9, §3 WP-11, §6 confirmation 7 and
the owner's ruling 7 of 2026-09-22 in its §10) and on slot-6 WP-10's ratio-criterion audit
(`docs/implementation/slot6/WP-10_report.md` §4.2–§4.4). **One phase boundary moves**: C2 is split
into **C2a** (settings and resume, slot 6) and **C2b** (the harness verbs and the bench extraction,
slot 7), with C2's acceptance items distributed between them and none dropped. **Four acceptance
clauses are restated, none loosened in substance**: C2 (g)'s literal "twelve keys" becomes "every
key `hecke::MathSettings::keys()` registers at the tree under test"; the exit-5 arm moves back into
C2 (now C2a) on `field_polynomial = conway`, as v3.2 said it would; C4 (d)'s "`--all` grows by
< 5 s" becomes a sum over C4's named new validations, each measured in isolation; C5 (c)'s
"identities 1–6" becomes "every item `HeckeIdentityCertificate` defines". No design decision
changes. Companion documents at this revision: `[C]` v1.7.2, `[E]` **v1.7.0**, `[X]` v1.9 (v1.10
with the slot-6 close).

> **Status at the slot-6 close (2026-09-22, [S6] WP-14; status only, nothing in v3.4 changes).**
> The companion documents are now `[C]` **v1.7.3**, `[E]` **v1.7.2** (v1.7.1 was the referee
> pass on v1.7.0, v1.7.2 the close's status bump) and `[X]` **v1.10**. **C2a is implemented**
> (slot-6 WP-13): the engine knobs as `set` keys through a second settings installer, the session
> baseline restored at session end, `resume` refusing a changed non-budget mathematical setting,
> `Decomposition` resumable, the exit-5 arm reachable through `canonical_field_polynomial(ell, r)`
> under `field_polynomial = conway`; `ConsoleSettingsValidation` (`fast`, 179 checks) is green on
> §10 C2 (f), (g) and (h), its key count **derived from `keys()`** (8, reconciled against `[X]`
> §1.5's 13 rows). Script **021** (`021_settings_resume.oc`) is a new artefact with a first-freeze
> transcript; the **20** pre-existing `.expected` files and `cli_frozen/` are byte-unchanged
> (`CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` rewrites all 20 identically);
> `ConsoleScriptValidation` is 281 checks. The registered roster is **106** (`--list`: 43
> `fast`, 55 `standard`, 8 `slow`). **Two items for the owner, recorded, not ruled**: (1) C2 (h)'s
> "a resume on a complete state is a strict no-op" conflicts with the frozen
> `014_expect_error.expected`, which pins a typed refusal ("is complete"); WP-13 kept the
> transcript and asserted the engine-level no-op, and changing 014 is an **owner-gated transcript
> re-baseline**; (2) `conway` is *accepted* as a setting (this plan's wording is right), but two
> production entry points (`CanonicalField(ell, r)`, `SplitInCanonicalField`) bypass the consumer
> that refuses it, so under `conway` they silently use `least` — latent until E6's report consumer,
> which must route through `FieldPolynomialFromSettings` (`[X]` v1.10 open item 4). **Pointer
> corrections for the next revision** ([E] v1.7.1 referee, finding m-3): §10 C4 (d)'s "in the
> manner of `[X]` §6.2 E2 (e)" should read "in the manner of `[S6]` §10 ruling 2 for `[X]` §6.2
> E2 (e)" — and note that E2 (e) itself is restated in `[X]` v1.10 to a bound on the campaign's
> overhead over the sum of per-cell timings; and v3.4's companion pointer `[E]` v1.7.0 is now
> v1.7.2. C2b (harness verbs, the bench extraction, §10 C2 (a)–(e)) is slot 7's. Close report:
> `docs/implementation/slot6/WP-14_report.md`.

**Version 3.3 (2026-09-22) — status and two bindings**, written by hecke-extensions slot 5,
package WP-11 (`docs/implementation/slot5/WP-11_report.md`) on slot-5 WP-10's report
(`docs/implementation/slot5/WP-10_report.md` §7, the four sentences it queued for this revision).
**No design decision, phase boundary or acceptance criterion of v3 changes.** What it records:
C1b's one deferral is closed — `bernoulli_mod(w, ell)` and `glover_factors(n, ell)` are **bound**,
from `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (the same TU as `sturm_bound` and
`u_ell_decision`, so neither include guard's rule 1 or 2 moves and no second `Console/` dependency
enters `HeckeExt/`), so §3.5's `bernoulli_mod` row leaves phase **C5** and the C5 phase list loses
both names; `glover_factors` returns a **`Record`**, and its `det`-twist is the **standard**
module's, which is worth a sentence because a reader comparing against a dual-convention table
would read every `det_twist` wrong (`[E]` v1.6.0, Claim `cl:glover`, now records that this
convention gates phase E7). The script set is **20** numbered scripts and
`ConsoleScriptValidation` **277 checks**, the four new ones (`017`–`020`) being `[X]` §8 slot-5
Lane C's "engine `.oc` scripts for the E0–E2 cases" — **early, partial C5**; C5 *proper*, the
`hecke_ext` record object, still gates on E5's record-schema freeze, and that schema is
`hecke_ext/v2` since slot-5 WP-1. §3.6's `crosschecks` row was already corrected to `Record` at
v3.2 (`[WP4-5]` §5 item 2) and is confirmed here, not changed. Companion documents at this
revision: `[C]` v1.7.0, `[E]` v1.6.0, `[X]` v1.8 (v1.9 with the slot-5 close).

> **Status at the slot-5 close (2026-09-22, [S5] WP-13; status only, nothing in v3.3 changes).**
> The companion documents are now `[C]` **v1.7.2**, `[E]` **v1.6.2** and `[X]` **v1.9**, and the
> record schema C5 *proper* gates on is frozen as **`hecke_ext/v2`** (slot-5 WP-1), with E5
> accepted in slot 5 — so C5's gate is met and C5 is schedulable. The console surface is unchanged
> by the rest of the slot: the 20 numbered scripts and `cli_frozen/` are byte-unchanged,
> `ConsoleScriptValidation` is 277 checks and `ConsoleC0Validation` 613. The registered roster is
> **100** validations (`--list`: 40 `fast`, 54 `standard`, 6 `slow`). The **eight** mathematical
> settings keys registered as `set` keys through C1b's third registry seam now include
> `field_polynomial` and `split_field_report` (slot-5 WP-7) — added without a console edit, which
> is what that seam is for — and the all-defaults fingerprint is still `0`, so
> `golden(point, object)` still resolves at rule R19. Close report:
> `docs/implementation/slot5/WP-13_report.md`.

**Version 3.2 (2026-09-21)**, written by hecke-extensions slot 4, package WP-8
(`docs/implementation/slot4/WP-8_report.md`): **C1b is implemented** (slot-4 WP-5,
`docs/implementation/slot4/WP-5_report.md`), and this revision records what C1b settled, closes
the C1a findings v3.1 listed, and takes the five findings C1b reported. Concretely: the
extension layer registers its own console verbs from `HeckeExt/RegisterHeckeExtensionVerbs.cpp`
with one exact-path exception in each of the two guards' rule 2 (`[OD]` slot-3 close-out 1,
confirmed 2026-09-21 as slot-4 confirmation 4); `golden()` lives in
`Bindings/Reproducibility.cpp`; §3.5 gains a **phase** column; the obsolete
`locality = strict → not_implemented_in_this_build` example is replaced by a pointer to the
shipped `015_strict_locality.oc`; the mathematical settings are named as the engine registers
them; and §11 records that C1b narrows `ConsoleC0Validation`'s tree arm. **No design decision or
phase boundary of v3 changed**; the one acceptance criterion that moved is C0's tree arm, and it
moved because C1b legitimately creates the files it forbade. Companion documents at this
revision: `[C]` v1.6.0, `[E]` v1.5.0, `[X]` v1.7 (v1.8 with the slot-4 close).

> **Status completed at the slot-4 close (2026-09-22, WP-11 — this note only; no design
> decision, phase boundary or acceptance criterion moves).** C1b's acceptance holds on the
> integration head: `ConsoleScriptValidation` is **259 checks over 16 numbered scripts**, each
> compared against its frozen `.expected` (`#! oc-format 1`, `#~` lines excluded), with **every
> hash pinned through `golden(...)` at `MathSettings` fingerprint `0`**; `ConsoleScriptEmit` is
> registered, owner-gated on `CONSOLE_EMIT_EXPECTED=1` and a no-op otherwise;
> `ConsoleCliPreservationValidation` and `ConsoleC0Validation` are green, so **C1a's preservation
> guarantee survived C1b** — the frozen CLI forms are byte-identical and `ConsoleCore` is still
> STL-only. The one *behavioural* CLI change of the slot is WP-2's re-capture of the
> `--bench --help` frozen output, made under lead authorisation because `--bench ext` is a new
> mode and the frozen text enumerates the modes. Companion documents at the close: `[C]` v1.6.2,
> `[E]` v1.5.2, `[X]` v1.8. **Not bound in C1b, and booked for slot 5**: `bernoulli_mod` and
> `glover_factors` (WP-7 shipped after C1b froze its transcripts), `solve` for under-determined
> systems and the general π-primary `jordan_type` (C2), the local-algebra invariants (C5), and
> 64-bit types. — *v3.3: the first of those is **done** (slot-5 WP-10); the rest stand.*

**Version 3.1 (2026-09-17) — status only**, written by the hecke-extensions slot-3 close (WP-11,
`docs/implementation/slot3/WP-11_report.md`): **C1a is implemented** (the status block below
the C0 one), `locality = strict` is **implemented** (slot-3 WP-3), so every sentence of this plan
that has it throw `not_implemented_in_this_build` is marked obsolete in place, and the C1a
findings are listed for the next revision. No design decision, phase boundary or acceptance
criterion of v3 changed.

**Version 3 (2026-09-16)** — revised in slot 2 of the hecke-extensions stage (WP-12,
`docs/implementation/slot2/WP-12_report.md`) so that this plan agrees with **what C0 built** and
with the documents the extension stage has since frozen. Version 2 (2026-09-14) was the revision
after the independent audit `docs/console/01-console-plan-audit.md` (verdict ACCEPT WITH
AMENDMENTS; every factual error E1–E12, contradiction I1–I5 and citation offset of §1.4 there is
fixed here, and every amendment A1–A16 is answered in §17) and after the extension engine's
capability inventory `docs/implementation/hecke_extensions_capability_inventory.md` (cited
`[I §n]`, gap list `[I G1–G17]`). Versions 1 and 2 are superseded in place; the changelog is §0.

**Status:** architect's plan for a CAS-style console (interactive REPL + scripting + CLI driver)
on top of the shipped pipeline. Binding for the engineering team until amended by the owner.
Branch `hecke-extensions` (matrix-engine programme closed, Phases 0–6; Hecke action S0–S14
complete; slot 1 closed; **77 registered validations**, of which `ConsoleC0Validation` is the
console's first). *v3.1:* slot 3 closed 2026-09-17 with **89 registered validations**, three of
them the console's (`ConsoleC0Validation`, `ConsoleScriptValidation`,
`ConsoleCliPreservationValidation`).

*v3.2:* slot 4 shipped **C1b** (WP-5) — the decomposition
surface, the six local-system presets, the mathematical settings as `set` keys, 16 numbered
scripts with frozen `.expected` transcripts, `ConsoleScriptEmit`, and the extension layer's own
verbs from `HeckeExt/RegisterHeckeExtensionVerbs.cpp`; the roster count at the slot close is the
close package's to state.

**Cited as** (added in v3; refreshed at v3.2): `[X]` =
`docs/implementation/hecke_extensions_implementation_plan.md` v1.7 (§n); `[E]` =
`docs/latex/hecke_extensions.tex` **v1.5.0**; `[C]` = `docs/latex/gl2_contract.tex` **v1.6.0**
(by label only); `[OD]` = `docs/implementation/hecke_extensions_owner_decisions.md`
(decisions **R1** mathematical settings, **R3** resumable state, and the **slot-4
confirmations** of 2026-09-21); `[S2]` = `docs/implementation/hecke_extensions_slot2_plan.md`;
`[WPn]` / `[WP2-n]` / `[WP3-n]` / `[WP4-n]` = the slot-1 / slot-2 / slot-3 / slot-4 package
reports under `docs/implementation/slot{1,2,3,4}/`.

**C0 implemented: 2026-09-16** (branch `hecke-extensions`, slot 1 WP-5, commit `2a332e5`).
`ConsoleCore` is a static library of 13 STL-only TUs; the acceptance criteria (a)–(d) of §10 are
all met (612 checks in `ConsoleC0Validation`, green on `RelWithDebInfo` / `Check` / `Bench`;
10 000 statements in 0.015 s). The nine deviations of `[WP5]` §2 are **resolved in v3**: eight are
*adopted into the text below* — the plan was wrong or silent and the implementation is right — and
one is a process note. Adopted, each at its section:

| # | Deviation | Adopted at |
|---|---|---|
| 1 | the validation is **`ConsoleC0Validation`**, not `ConsoleLanguageValidation` | §10 C0, §11 |
| 2 | its TU is `Console/ConsoleC0Validation.{h,cpp}`, not `Core/…` — so `ConsoleCore` stays test-free and `check_console_includes.sh` needs no exception for its own test | §9, §10 C0 (b) |
| 3 | **`quit` is a statement** (§3.1 reserved the word, §3.2 gave it no production) | §3.2 EBNF |
| 4 | printing has a **canonical** and a **display** rendering, differing only for a top-level `String`, so `print("text")` prints bare | §2 C5, §3.3, §4.3 |
| 5 | **`-2 ^ 2 == 4`** — what the §3.2 EBNF says, implemented as written and pinned both ways | §3.2 |
| 6 | **`CONSOLE_CHECK` / `CONSOLE_DEBUG_CHECK`**, because `EngineCheck.h` would break the STL-only rule | §2 C8, §9 |
| 7 | **`ScriptRunner` is C0**, `ConsoleCli` + the `kernel.cu` branch stay C1 (§9 and §10 contradicted each other) | §9, §10 C0/C1a |
| 8 | C0 registers the two **console-owned presentation** settings (`print_max_entries`, `verbose`) and no engine or mathematical key | §2 C4 |

**C1a implemented: 2026-09-17** (v3.1; branch `hecke-extensions`, slot-3 WP-7, commit `bd83f59`,
report `docs/implementation/slot3/WP-7_report.md`). `Console/Bindings/` (compiled into
`cohomology_app`, never into `ConsoleCore`) binds nine types (`Fp`, `Poly`, `Matrix`, `Model`,
`Complex`, `LocalSystem`, `Cohomology`, `HeckeOperator`, `Family`) and 68 verbs on top of C0's 25;
`kernel.cu` gains exactly one branch (`--console` / `-i` / `--script` / `-c` / `-`), with
`print_usage` and the no-argument benchmark byte-identical; `Golden/GoldenHarness.h` exposes the
one read-only `GoldenLookup(point, object)` (inventory gap G13), through which `golden(...)`
resolves and which refuses at a non-zero `MathSettings` fingerprint (rule R19); exit code **5** is
the `hecke::NotImplementedInThisBuild` outcome of the C7 catch order. Acceptance (a)–(g) of §10
C1a are met, with fingerprint `0` at every pin and `--list` compared modulo appended names, by
**`ConsoleScriptValidation`** (`fast`, 174 checks) and **`ConsoleCliPreservationValidation`**
(`fast`, 39 checks). Twelve deviations are recorded in the report's §2 — among them
`bernoulli_mod` not bound (E6), the local-algebra invariants and `check_identities` not bound
(C5), `save_state` bound early, **no `HeckeExt/` binding and therefore no `Sturm` type** (the
`HeckeExt/` guard's rule 1 does not admit `Console/Bindings/`), `hash(x)` returning the canonical
`0x…` text, matrix arithmetic through named verbs, 32-bit types only. **All six C1a findings are
closed at v3.2** (slot-4 WP-8), each in the section it names: §3.5 has its **phase** column
(WP-7 finding 1); `golden()`'s home is `Bindings/Reproducibility.cpp`, and §9 and §10 now agree
on it (finding 2); §2 C5, §3.6, §9 and §10 all say that the extension layer registers its own
verbs from `HeckeExt/RegisterHeckeExtensionVerbs.cpp` — confirmed by the owner on 2026-09-21
(slot-4 confirmation 4), together with the **one exact-path exception per guard rule 2** that the
option actually costs, which is the part `[OD]` close-out 1 had been told it did not (finding 3);
§11 records that **C1b**, not C1a, narrows `ConsoleC0Validation`'s tree arm (finding 4); the
obsolete `strict` → `not_implemented` examples are **replaced**, not merely marked, by a pointer
to the shipped `015_strict_locality.oc` (slot-3 WP-3 finding 7); and the §2 C4 table carries the
registered spellings `sturm_unavailable` / `sturm`, with `commutant_budget` appended (slot-3
WP-2, slot-4 WP-1). **C1b's own five findings** (`[WP4-5]` §7) are applied at v3.2 as well:
`CrossChecks` is a `Record` and not a handle type (§3.6), the local-system presets are C1b's and
carry no model (§3.6), §2 C4 says "register before you construct a `Session`", and §2 C5 records
that `level_c.locality.source` is a value-bearing field. Finding 6 — that `HeckeExt/` rule 1
stays as it is — is the disposition this revision writes into §9.

Deviation 9 is not a plan matter: WP-5 edited `CLAUDE.md` under an explicit brief override. Going
forward the slot plans' shared-file rule holds — **a console phase does not edit `CLAUDE.md`; the
slot's close package does** — and this plan's phases are written that way.

Two **C1 debts** the deviations leave (the plan was right, the work is simply not done): the
generated language reference must state the `-2 ^ 2 == 4` precedence and the canonical/display
split explicitly, because neither is the school convention (§4.4, §10 C1a); and the *command-line*
surface (`--script`, `-c`, stdin, `--console`, `--log`, `name=value`) with its one `kernel.cu`
branch is still unwritten (§10 C1a).

The settings layer additionally carries owner decision R1's engine/mathematical **family** split
and R3's resumable-handle contract (`ResumableState`, `TypeInfo::resume`, the `state` / `resume` /
`save` verbs) — designed in C0, bound in C2/C5 to the engine-side `Hecke/HeckeSettings` and the
shipped R3 instances (§2 C4, §2 C5).

**Evidence base.** Every claim about the current code carries a `file:line` reference verified on
the `d54c589` tree (re-verified for version 2; v3 changed no `file:line` claim, and its new
statements cite `[X]` / `[E]` / the slot-2 package reports instead). The two feature documents this plan must anticipate
are `docs/implementation/hecke_extensions_mathematics.md` (cited `[M §n]`) and
`docs/implementation/hecke_extensions_computational_strategy.md` (cited `[S Stage n]`). The
matrix-engine plan `docs/matrix-engine/00-implementation-plan.md` (cited `[ME §n]`) is the model
for structure, rigour and acceptance discipline; its decision **D6 — no external dependencies
beyond the CUDA toolkit** (`[ME §2 D6]`) and **D7 — bit-identity as the acceptance criterion**
(`[ME §2 D7]`) are inherited unchanged.

**Notation crosswalk (normative).** The two feature notes and the code name the three parameters
differently (`[I]` "Notation bridge"); the console uses the **code's** names, and every script
comment that quotes `[S]`/`[M]` must translate:

| Meaning | `[S]` / `[M]` | Code and console |
|---|---|---|
| coefficient prime (the field `F_ℓ`) | `p` | `ell` |
| Hecke prime / index | `q` | `p` (`p_hecke`) |
| weight of the symmetric power | `k` | `n` (`n_sym`) |
| cohomological degree | — | `q` |
| the operator at the coefficient prime | `T_p` | `U_ell` = `hecke(H, p = ell)` (same code path, `HeckeOperatorFamily.h:17-20`) |

So `[S Stage 9]`'s "`(k, p) = (10, 691)`" is the console's `symmetric_power(K, n = 10, ell = 691)`,
and its `T_2` is `hecke(H, p = 2)`.

---

## 0. Changelog

**v3.10 (2026-10-03)**: slot-19 NB-1 — the served console specified (no code).

| Section | Change | Source |
|---|---|---|
| Header | v3.9.3 → **v3.10**; companions `[C]` v1.18.0, `[E]` 1.18.0, `[X]` v1.23 | slot-19 NB-1 |
| §18 (new) | `--serve` / `oc-serve/1`: launch + handshake + lifecycle (18.2), requests (18.3), frames (18.4), `PrintJson` envelope and per-type schemas, `json_version` 1 (18.5), interrupt (18.6), exit-code mapping (18.7), the `read_only` tag and the tagged-overload table (18.8), env scrubbing and process hardening (18.9), RSS cap / `fatal` (18.10), conformance tests (18.11), LAN rules as gateway requirements (18.12), non-goals (18.13) | owner decisions 2026-10-03; `WP-19d_notebook_design_note.md` §0–§5, §7, §10 |
| §10, §11 | one phase row **N (notebook)** and two validation rows (`ConsoleReadOnlyTagValidation` `fast`, `ConsoleServeValidation` `standard`), both *specified, not built*, guarded by `OC_BUILD_NOTEBOOK` | slot-19 plan v1.0 NB-1 / NB-2 |
| §16 | follow-up recorded: R-U1b (persistence, hosting beyond the token, TLS promotion) stays with the owner | design note §8 |

**v3.9.3 (2026-09-26)**: slot-12 WP-17 (post-close, owner-approved) — Q9 decided (a): the wide band
`2^32 ≤ ell^k < 2^64` served by the native `uint64_t` pipeline, as the campaign serves it.

| Section | Change | Source |
|---|---|---|
| Header | v3.9.2 → **v3.9.3**; companions `[C]` v1.12.0-pre.2, `[E]` v1.12.1, `[X]` v1.16 | slot-12 WP-17 |
| §3.6 | *v3.9.3*: **wide handles** as built (members, values = the campaign's, Strings above `2^63`) | owner ruling Q9 (a), 2026-09-26 |
| §8 | *v3.9.3*: the wide band adds no row and no exit code; the former exit-5 refusal of the band is gone | slot-12 WP-17 |
| §10 | *v3.9.3*: phase row **wide band** (slot 12, WP-17) **implemented** | slot-12 WP-17 |
| §11 | *v3.9.3*: `ConsoleErrorValidation` arm (Q9), **539 checks**, `fast`; `ConsoleScriptValidation` **358**; 37 transcripts | slot-12 WP-17 |
| §16 | *v3.9.3*: **Q9 decided (a)** | owner, 2026-09-26 |

**v3.9.2 (2026-09-26)**: slot-12 WP-8 — phase θ **built**: `dickson_les(n, ell)` → `DicksonLES` and
`theta(H, H_up)` registered as §3.6 specifies, §8's θ rows pinned (arm (T)), script `027_` frozen.

| Section | Change | Source |
|---|---|---|
| Header | v3.9.1 → **v3.9.2**; companions `[C]` v1.12.0-pre.2, `[E]` v1.12.1, `[X]` v1.15 | slot-12 WP-8 |
| §3.6 | *v3.9.2*: the θ rows **as built** (members exactly as specified; four recorded choices, below the rows) | slot-12 WP-8 |
| §8 | *v3.9.2*: the θ rows as built, pinned by `ConsoleErrorValidation` arm (T) | slot-12 WP-8 |
| §10 | *v3.9.2*: phase θ **implemented**; schedule row | slot-12 WP-8 |
| §11 | *v3.9.2*: `ConsoleErrorValidation` arm (T), **347 checks**, `fast`; `ConsoleScriptValidation` **354**; 36 transcripts | slot-12 WP-8 |

**v3.9.1 (2026-09-25)**: slot-11 WP-17 (the slot close) — the WP-15 referee's m-5 (§10's "Digit handles"
row: `af1617e` is the spec commit, not a merge) and the F-2 ruling recorded (the θ rows' `ell < 5` → exit 3
unchanged; the build now agrees). No row, exit code, verb or transcript moves.

**v3.9 (2026-09-25)**: slot-11 WP-15 — v3.9-pre.1's sites as slot 11 left them (WP-16 not run), and
the digit handles slot-11 WP-18c built under `[E]` v1.12.0-pre.2 (h) (`db1b454`, repaired in `eff5851`
after the slot's review, pass 2). Base `1106200`.

| Section | Change | Source |
|---|---|---|
| Header | v3.9-pre.1 → **v3.9**; companions `[C]` **v1.11.0**, `[E]` **v1.12.0**, `[X]` v1.14.1 | `[S11]` WP-15 |
| §2 C4 | *v3.9*: `coefficient_ring`'s grammar `Z/ell^<k>`, `2 ≤ k ≤ 4096` (a parse cap; `Z/ell^4097` exit 1 as `--set`); executability decided at the cell | `[E]` v1.12.0 `sec:ring` (a) |
| §3.6 | *v3.9*: the digit handles as built — members, `Cohomology.precision`, `HeckeOperator.charpoly_free` as Strings, the field members exit 3, the rest exit 5, `hecke(H, p)` recomputing the cell per operator; the θ verbs **not built** | slot-11 WP-18c; WP-14 pass 2 M-1, m-2 |
| §8 | *v3.9*: the digit rows (per-cell refusals exit 5, caps checked at `k + K_w − 1`); the θ rows specified, not built | slot-11 WP-18c; `[E]` v1.12.0 |
| §10 | *v3.9*: phase θ **specified, not built**; phase row **digit handles** (slot 11, WP-18c) **implemented**; schedule rows | `[S11]` §10 |
| §11 | *v3.9*: `ConsoleErrorValidation` (K) digit rows, **309 checks**; script `027_` not frozen (35 transcripts) | slot-11 WP-18c |
| §16 | *v3.9*: Q7 re-read (unchanged); **Q9** the console's `uint32_t` gap below `2^64` — open | WP-14 pass 2 m-4 |

**v3.9-pre.1 (2026-09-25)**: slot-11 WP-4, spec first — the console rows of `[S11]` WP-16
(a/s under decision 5 (A)), written before WP-16 builds them (`[S11]` =
`docs/implementation/hecke_extensions_slot11_plan.md` rev 2, §3 WP-4, WP-16 and §10). Base
`54bc2b5` (slot-11 R0). No count below is measured: every count is WP-16's to measure and WP-15's
to record in v3.9 (or, if WP-16 is stopped a/s, WP-15 records the rows as specified, not built).

| Section | Change | Source |
|---|---|---|
| Header | v3.8 → **v3.9-pre.1**; companions `[C]` **v1.11.0-pre.1**, `[E]` **v1.12.0-pre.1**, `[X]` v1.14.1 | `[S11]` WP-4 |
| §3.6 | *v3.9-pre.1*: the `DicksonLES` type, `dickson_les(n, ell)` and `theta(H, H_up)` — members, the source-indexing, the equality with `L_map`, the errors, the name note beside `Family.theta(p, q)`; a census verb recorded **not bound** | `[S11]` WP-16; `[E]` v1.12.0-pre.1 `sec:thetaobj`, `sec:census` |
| §8 | *v3.9-pre.1*: no new row or code — the ring refusal exit 5, the mismatched handles exit 3, `ell < 5` exit 3 (`ENGINE_CHECK`), a failed lazy handle never retried | `[S11]` WP-16; `[E]` `sec:ring` (b), v1.12.0-pre.1 paragraph |
| §10 | new phase row **"θ"** (slot 11, WP-16, a/s): scope, acceptance, the step-1 transcript guard; schedule row | `[S11]` WP-16 |
| §11 | *v3.9-pre.1*: script `027_` (first freeze); `ConsoleErrorValidation` one new arm letter, tier stays `fast`; the roster entering slot 11 is 130 | `[S11]` WP-16; `[S11]` §2 |

**v3.8 (2026-09-25)**: slot-10 WP-15, phase 1 — v3.8-pre.1's sites as slot-10 WP-12 built them.
Base `f0640d0` (slot-10 WP-2, WP-3, WP-6, WP-9, WP-10, WP-11, WP-12, WP-13 merged). Every count
below is WP-12's own measurement (`[WP10-12]` = `docs/implementation/slot10/WP-12_report.md`), except the roster,
re-derived from the registration fragments at the base.

| Section | Change | Source |
|---|---|---|
| Header | v3.8-pre.1 → **v3.8**; companions `[C]` **v1.10.0**, `[E]` **v1.11.0-pre.2**, `[X]` v1.13 | `[S10]` WP-15 |
| §2 C7 | *v3.8*: the exception **built** at its two sites (`Evaluator.cpp` +19/−1, `CoreVerbs.cpp` +11/−1; nothing else in `Console/Core/`), recorded as the **third named exception** to C5's acceptance (b); the negative control (the two sites reverted → 21 checks of arm (W) fail) | `[WP10-12]` (i) |
| §3.6 | *v3.8*: the five members as built; `LocalSystem.coefficient_ring` new; the mismatch rule pinned in both directions (no code needed) | `[WP10-12]` (ii) |
| §6, §8 | *v3.8*: the position on a getter's error; **an unwrapped getter's `NotImplementedInThisBuild` is exit 5 (was 3)**, the raw getter's text `<Type>.<member> failed` + cause; the campaign verbs' handler, exit-5 branch unreachable at the base (per verb, recorded); an ordinary `campaign_plan` failure's text `campaign_plan: <what>` (code 3 both) | `[WP10-12]` (iii), notes 1–2 |
| §10 | "C5 leftovers" **IMPLEMENTED**, acceptance (a)–(e) as met; schedule row | `[WP10-12]` |
| §11 | `ConsoleErrorValidation` **294** (arm (W), 24 scripts), `ConsoleScriptValidation` **350**, **35** numbered scripts (`026_` new), `ConsoleDeterminismValidation` **570**; the roster **129** at `f0640d0` | `[WP10-12]`; the fragments |
| §16.4 | the member-getter wrap: **done** | `[WP10-12]` |

**v3.8-pre.1 (2026-09-25)**: slot-10 WP-2, spec first — the console rows of `[S10]` decision 6 (A),
written before slot-10 WP-12 builds them (`[S10]` = `docs/implementation/hecke_extensions_slot10_plan.md`
rev 2, §3 WP-2, WP-12 and §10). Base `6bb5bce` (slot-10 R0). No count below is measured: every
count is WP-12's to measure and WP-15's to record in v3.8.

| Section | Change | Source |
|---|---|---|
| Header | v3.7.1 → **v3.8-pre.1**; companions `[C]` v1.9.1, `[E]` **v1.11.0-pre.1**, `[X]` v1.13 | `[S10]` WP-2 |
| §2 C7 | *v3.8-pre.1*: the member-getter position gap is **scheduled to close** in slot-10 WP-12 under decision 6 (i) — the one named `Console/Core/` exception, its two sites and its rules | `[S10]` decision 6 (i); `[WP9-12]` §4 item 1 |
| §3.6 | *v3.8-pre.1*: `LocalSystem.n`, `.d_V`, a new `LocalSystem.coefficient_ring`, `HeckeOperator.p`, `.r` honour on a ring handle; every other unlisted member keeps exit 5; the ring-mismatch rule binding | `[S10]` decision 6 (ii); `[E]` v1.11.0-pre.1 `sec:ring` (h) |
| §6, §8 | *v3.8-pre.1*: a member getter's error carries `file:line:col`; `run_campaign` / `campaign_plan` map `NotImplementedInThisBuild` to exit 5, other exceptions exit 3 | `[S10]` decision 6 (i), (iii) |
| §10 | new phase row **"C5 leftovers"** (slot 10, WP-12): scope, acceptance, the step-1 transcript guard | `[S10]` WP-12 |
| §11 | *v3.8-pre.1*: scripts from `026_` (first freezes); `ConsoleErrorValidation` gains one arm letter for the leftovers, tier stays `fast` | `[S10]` WP-12 scope 5 |
| §16.4 | the member-getter wrap moves from "recorded, not scheduled" to slot 10 | `[S10]` decision 6 (i) |

**v3.7.1 (2026-09-25)**: slot-9 WP-17, the slot close — the Fable referee's repairs to v3.7
(`WP-15` referee, finding m-6 and m-10; M-1's review file is now
`docs/implementation/slot9/WP-14_review.md`) and slot-9 WP-8c's binding fix (`cc3d30a`, merged at
`bdbb93c`; `docs/implementation/slot9/WP-8c_report.md`). Counts measured on a fresh out-of-source
`RelWithDebInfo` build of `bdbb93c`.

| Section | Change | Source |
|---|---|---|
| Header | v3.7 → **v3.7.1**; companions `[C]` **v1.9.1**, `[E]` **v1.10.1**, `[X]` **v1.13**; the v3.7 header's "nothing else" sentence read with the two §0 notes (m-10) | referee m-10 |
| §6, §8 | the exit-5 row names the four campaign harness verbs as built: `campaign_spec` / `campaign_spec_text` map `NotImplementedInThisBuild` to **exit 5** (since WP-8c; before it, exit 3), `campaign_plan` does not wrap (a ring refusal cannot arise there: the spec is validated at parse), `run_campaign` wraps every exception as a runtime error (exit 3) | referee m-6; WP-8c; `Harness.cpp` |
| §10 C5c | the exit-3 observation **resolved** by WP-8c; C5c **pinned from the console** by script `048_c5c_ring_campaign` (a first freeze at `(6, 5)`, `Z/ell^2`, two jobs, the point's objects against `golden(...)`) | WP-8c; `ConsoleErrorValidation` (M), `ConsoleScriptValidation` |
| §11 | `ConsoleScriptValidation`: **34** numbered scripts, **346 checks**; `ConsoleErrorValidation`: arm (M), **218 checks**; the roster **125** (52 / 63 / 10), unchanged | `--list`; WP-8c |

**v3.7 (2026-09-25)**: slot-9 WP-15, phase 2 — the first text under this number (v3.7-pre.1 with
its phase-2 sites filled; nothing else of v3.7-pre.1 changes). Sources: `[S9]` §3 WP-6 … WP-9,
WP-15 and §10 (decisions 2 (i) (A), 6 (A), 7 (A), 13); slot-9 WP-6's report §2 (b), (d), (e)
(`[WP9-6]`), WP-7's §0 (the merge fix `158c0be`), WP-8's (`[WP9-8]`) and WP-9's §2 (m-1). Base
`9b004f2`, every slot-9 code package merged; every count measured there on a fresh out-of-source
`RelWithDebInfo` build. Timings are indicative.

| Section | Change | Source |
|---|---|---|
| Header | v3.7-pre.1 → **v3.7**; companions `[C]` v1.9.0, `[E]` **v1.10.0** | `[S9]` WP-15 |
| §10 C5 | **C5c IMPLEMENTED** (slot-9 WP-8, `ad65bd9`, `f4fc3d2`, merged at `8853544`; `158c0be`): what it built, what the console's harness verbs see of it (no verb, type or member added; `console.md` unchanged), the exit-3 observation for a spec-validation refusal through `campaign_spec`, and the "campaign and record" bullet met for the campaign | `[WP9-8]`; `CampaignRingValidation`; a hand check at the base |
| §10 heading, status, schedule | C5 **implemented** in its three lanes | as above |
| §2 C4, engine knobs (`batch` … `device` row) | a note: since slot-9 WP-6 the override reaches the elimination driver's per-panel programs, and the fingerprint's device bit follows the effective policy | `[WP9-6]` §1; `EngineElimPassOptionsValidation` |
| §4.1 | a note: slot-9 WP-7's L2 narrows `tau_construction_mutex()` in `HeckeOperatorFamily::build_pipelines()` only; the console's rule stands | WP-7 report §2; `HeckeFamilyConcurrentBuildValidation` |
| §11 `ConsoleDeterminismValidation` | after slot-9 WP-6 the device arms reach the per-panel programs (771 / 771 with GPU nodes); checks 564 and digest unchanged; wall 28.60 → 29.22 s (min, R0 → WP-6), 32.4 s at the base at load ≈ 14; the 45 s stop not reached, so **S8-D3's ratification stands** (decision 13) | `[WP9-6]` §2 (d), (e); a run at the base |
| §11 | new row `CampaignRingValidation` (C5c's engine-side gate, `standard`, 693 checks); the roster at the base **125** (52 `fast`, 63 `standard`, 10 `slow`) | `--list` at `9b004f2` |

**v3.7-pre.1 (2026-09-24)**: slot-9 WP-15, phase 1. Sources: `[S9]` §3 WP-12, WP-13, WP-15 and
§10 (decision 2 (i) (A), (ii) (A)); `[WP9-12]` §1, §4, §5; `[WP9-13]` §1, §2, §7, §8. Base
`7ddb555`; every count measured there. One line per changed section; where a row changes a
claim, it names the validation that measures it. Timings are indicative.

| Section | Change | Source |
|---|---|---|
| Header | v3.6.1 → **v3.7-pre.1** (phase 1 of WP-15; v3.7 in phase 2); companions `[C]` v1.9.0, `[E]` v1.10.0-pre.2 | `[S9]` WP-15 |
| §2 C4, `coefficient_ring` | as built: the `set`-statement refusal carries its position; `--set` legal-but-unexecutable is exit 5; under `Z/ell^<k>`, `ell ≥ 5`, the verbs of `[E]` `sec:ring` (h) honour the ring, everything else exits 5 | `[WP9-12]` §1.1, §1.3; `ConsoleErrorValidation` (K) |
| §2 C7 | the `set`-statement position gap is **closed** (the `exec_set` back-fill); a new, narrower gap: a member getter's error carries no position | `[WP9-12]` §1.3, §4 item 1 |
| §3.5 | the C5 rows are **shipped** (slot-9 WP-13), their signatures and return shapes as built; two new rows, `is_local` and `algebra_invariants` | `[WP9-13]` §1, §2, §7; `HeckeExtAlgebraInvariantsValidation`, script 047 |
| §3.6 | the types C5 binds, as shipped: E7's two (WP-12), E8's ring members on `Cohomology` / `HeckeOperator` (WP-12), C5b's thirteen (WP-13); the reserved names bound under other spellings; what is not bound | `[WP9-12]` §1.1, §1.2; `[WP9-13]` §1 |
| §4.4 | `gen_console_md.sh` takes the binary's path; `console.md` current at `7ddb555` | `gen_console_md.sh build/cohomology_app --check` |
| §6 | exit codes: a legal but unexecutable `--set` value is **exit 5**; the error-location exception is closed | `[WP9-12]` §1.3; `ConsoleErrorValidation` (K) |
| §8 | the exit-5 row: `--set`, the set-statement position, the ring mismatch, the C5 dispatch refusals | `[WP9-12]` §1.1, §4 |
| §10 C5 | **C5a and C5b IMPLEMENTED**, the binding list as shipped, acceptance (a)–(c) as met, the two Core exceptions made; C5c left to phase 2 (v3.7) | `[WP9-12]`, `[WP9-13]` |
| §10 schedule | C5 row: slot 9, C5a / C5b implemented, C5c left to phase 2 (v3.7) | as above |
| §11 | `ConsoleErrorValidation` 107 → **210** checks (arm (K), exit 5); `ConsoleScriptValidation` **33** numbered scripts, 342 checks; `ConsoleDeterminismValidation` 564 checks; C5b's `HeckeExtAlgebraInvariantsValidation`; the roster at the base **118** | measured at `7ddb555` |
| §16.4 | the member-getter position wrap recorded for the next authorised Core batch | `[WP9-12]` §4 item 1 |

**v3.6.1 (2026-09-24)**: slot-8 WP-13, the referee repairs. Source: the WP-13 Fable referee report,
findings M-1, m-5 and m-6.

| Section | Change | Source |
|---|---|---|
| Header | v3.6 → v3.6.1; companion `[E]` v1.9.1 | referee |
| §1 | pointer note, re-read at `5c70e95` | m-5 |
| §5 | "Today" / "Underlying call" pointers of the first rows, re-read at `5c70e95` | m-5 |
| §6, §11 | the `--set` exit 1: re-measured correctly, and pinned by `ConsoleErrorValidation` (K), which goes 105 → 107 checks | M-1 |
| §2 C4 | "Thirteen keys" annotation kept (m-6, accepted as is) | m-6 |

**v3.6 (2026-09-24)**: slot-8 WP-13. Sources:
* `[S8]` §3 WP-13 and §10, rulings 4 (A) and 8 (A);
* `[WP8-10]` §4, §5, §6, §7.2 and §8;
* `[WP8-3]` §3 and §4 (d);
* the slot-7 close's queue P-1 … P-5 (the status block at the head).

Base `5c70e95`: every pointer below was re-read there, and every count was measured there on a
fresh `RelWithDebInfo` build, out of source. **No design decision changes, and no acceptance item
is dropped or loosened.** There is one line per changed section. Where a row changes a claim, it
names the validation that measures it. A timing is indicative unless a window is named.

| Section | Change | Source |
|---|---|---|
| Header | v3.5 → v3.6; companion pointers `[C]` v1.8.0, `[E]` v1.9.0, `[X]` v1.11. **P-1** in the v3.5 paragraph (C2b merged at `4508641`, accepted). The slot-7 close block marks P-1 … P-5 as applied | `[S8]` WP-13; slot-7 close |
| §2 C4, mathematical settings | `coefficient_ring` **registered**, the eleventh key. `Z` / `Z/<m>` are refused inside `set()`: exit 5 on the `set` statement, exit 1 as `--set` *(v3.13.0: `Z` has been stored since slot-24 D6 and is honoured by the integral descent only, every other verb exits 5 naming itself; `Z/<m>` alone stays refused inside `set()`; `[C]` `def:ringsemantics`(3))*. Every pipeline verb refuses `Z/ell^<k>` with exit 5, so the E8 objects are console-unreachable in slot 8. "Thirteen keys" is annotated: 11 are registered | `[WP8-3]` §3, §4 (d); `[S8]` ruling 4 (A); `ConsoleErrorValidation` (K), `HeckeReductionValidation` (X), `ConsoleSettingsValidation` |
| §2 C7 | the two paths that lost exit 5, and C4's fixes: a lazy handle (`bind::LazyCompute`) and the `set` statement (`InstallMathSettings`). The `set`-statement error has no position yet | `[WP8-10]` §3, §3b; `ConsoleErrorValidation` r05, r06, (K) |
| §3.6, §4.4 | `help --markdown` ships as the **binding verb `help_markdown()`** (`Bindings/Reference.cpp`), with `docs/console/gen_console_md.sh` (`--check`). The statement form stays the design, as a Core edit for the owner | `[WP8-10]` §4, §7.2 item 1; `gen_console_md.sh --check` current at `5c70e95` |
| §5 | **P-2**: the Benchmarks row's gap G4 is closed; `RunMode` `BenchDriver.h:124`, `RunBench` `:154`, runners `BenchDriver.cpp:307/341/405/466` (+ `RunExt` `:561`). **P-4**: the Campaigns row's pointers are `CampaignSpec.h:371-372, 379` and `CampaignDriver.h:163, 188, 199, 208`. **P-3**: G4b and G9 are closed in their rows | slot-7 close P-2 … P-4, re-read at `5c70e95` (P-2's and P-4's values of the close had drifted again) |
| §6 | exit codes: every `--set` refusal is exit 1, a legal-but-unexecutable value included (C5 owner question). Error location: the one exception, the `set`-statement refusal, deferred to C5 | `[WP8-10]` §3b; measured at `5c70e95` |
| §8 | the exit-5 row gains `coefficient_ring` and C4's two fixes; the compute-failure row names `ConsoleErrorValidation` | `[WP8-10]` §2, §3 |
| §9 | the TU tree as built: `Bindings/Reference.cpp` (C4), `Bindings/EngineSettings.cpp` (C2a, missing since v3.4), the three validations in their own TUs, `gen_console_md.sh` | `[WP8-10]` §1 |
| §10 C2b | **P-1**: merged and accepted | slot-7 close |
| §10 C4 | **IMPLEMENTED 2026-09-24**. The status paragraph covers (a)–(d), CheckThread, the manual and the `CLAUDE.md` hand-over | `[WP8-10]` §5, §6, §7.2; `ConsoleDeterminismValidation`, `ConsoleErrorValidation`, `cross_config.sh`, `console_c4_budget.sh` |
| §10 C5, schedule | C5 → **slot 9**. The binding list is extended by **E7's and E8's types**, plus the campaign and record support for `Z/ell^k`. Two owner items (Core edits) ride with C5 | `[S8]` rulings 4 (A), 8 (A); `[E]` v1.9.0 `sec:ring` |
| §11 | **P-5** and C4's counts: `ConsoleScriptValidation` 22 scripts, 294 checks; `ConsoleSettingsValidation` 11 keys, 219 checks; `ConsoleErrorValidation` **shipped**, 105 checks; `ConsoleDeterminismValidation` 531 checks. Its tier note "≈ 5 s" is **restated** as ≈ 25–30 s, measured and indicative; it stays `standard`, and re-tiering it is an owner item. The roster is 114 | measured at `5c70e95`; `[WP8-10]` §6, §8 item 2 |
| §14.1, §14.2 | **P-3**: G4, G4b, G9, G14 **CLOSED** (the G5 pattern), with their shipped locations. **P-4**: the `CampaignSpec.h` and `CampaignDriver.h` pointers | slot-7 close P-3, P-4 |
| §16.4 | the freshness gate's tool is `gen_console_md.sh --check`; the gate itself stays unscheduled | `[WP8-10]` §4 |

**v3.5 (2026-09-23)**: slot-7 WP-12. Sources: `[S7]` §3 WP-12 and §10 (owner decision 6 (A),
confirmation 12), and slot-7 WP-8's commits `fee4690`, `2855084` and `3d0322e` (`[WP7-8]`).
**No design decision changes, and no acceptance item is dropped or loosened.** One line per
changed section. Where a row changes a claim, it names the validation that measures it.

| Section | Change | Source |
|---|---|---|
| Header | v3.4 → v3.5; companion pointers `[C]` v1.7.3, `[E]` v1.8.0, `[X]` v1.10 (the v3.4 status block's queued correction) | slot-7 WP-12 |
| §2 C5 "No timings on stdout" | `timed` returns `{value, wall_s, wall_us, peak_rss_mb, peak_rss_kb, allocs, alloc_bytes}`, times and MiB figures as **Strings** with **Int** micro-unit twins, since the console has no float type; `time(expr)` is **deferred** (unbound) | `[WP7-8]` `3d0322e`; `ConsoleDeterminismValidation`, script 022 |
| §2 C5 `resume` | the strict no-op on a complete state is an **engine-level** statement (`resume_locality`). The console's `resume` on a complete handle is a typed refusal "is complete", recorded as conforming | `[S7]` §10 decision 6 (A); `ConsoleSettingsValidation` (h) |
| §3.6 types | `ValidationRun`, `BenchRun` and `CampaignResult` are **Records**, not handle types; `CampaignSpec` is the one handle type C2b registers | `[WP7-8]` `3d0322e` |
| §5 table | `run_validations` **deferred**; `bench` returns a Record (`total_s` / `total_us`, …); `micro("cuda")` **CLI-only**; `plan(spec)` → **`campaign_plan(spec)`**; `single_job` **deferred**; `time(expr)` **deferred** | `[WP7-8]` `3d0322e` |
| §9 layout | `Harness.cpp`'s verb list as built; `ConsoleDeterminismValidation` in its own TU | `[WP7-8]` `3d0322e` |
| §10 C2 | C2b status (as built, pending acceptance); (h) restated at the engine level, with transcript 014 kept | `[S7]` §10 decision 6 (A); `[WP7-8]` |
| §10 C4 (d) | "in the manner of `[X]` §6.2 E2 (e)" → "in the manner of `[S6]` §10 ruling 2 for `[X]` §6.2 E2 (e)" (the v3.4 status block's queued pointer correction; `[E]` v1.7.1 finding m-3) | slot-6 close |
| §10 schedule | C4: slot 7 → **slot 8**, gate unchanged (C2b accepted); C5 follows C4 | `[S7]` §10 confirmation 12 |
| §11 | `ConsoleDeterminismValidation`: C2b's arms (a)–(e) as built, `standard`, 122 checks; C4 adds the remaining arms | `[WP7-8]` `3d0322e` |
| §14.1 | `plan` → `campaign_plan`; `single_job` deferred | `[WP7-8]` `3d0322e` |

**v3.4 (2026-09-22)** — slot-6 WP-11. Sources: the slot-6 plan (`[S6]`) §2.3 item 9, §3 WP-11 and
WP-13, §6 confirmation 7 with the owner's ruling 7 (§10); slot-6 WP-10 (`[WP6-10]`) §4.2, §4.3,
§4.4. **One phase boundary moves (C2 → C2a + C2b); four acceptance clauses are restated.** One line
per changed section:

| Section | Change | Source |
|---|---|---|
| Header | v3.3 → v3.4; companion pointer `[E]` v1.7.0 | slot-6 WP-11 |
| §1 C4 row | "the twelve mathematical settings" → "the mathematical settings of `[X]` §1.5, registered by their consuming phases" (a derived count, not a literal) | `[WP6-10]` §4.4 |
| §2 C4 | the v3.1 note "no settings value raises `NotImplementedInThisBuild` today" is marked stale: `field_polynomial = conway` does, since slot-5 WP-7 | `[S6]` §2.3 item 9 |
| §8 | the `NotImplementedInThisBuild` row names `field_polynomial = conway` as the value this build cannot execute | `[S6]` §2.3 item 9 |
| §10 C2 | **split into C2a (slot 6) and C2b (slot 7)**: C2a = the settings half of the goal and acceptance (f), (g), (h) plus the exit-5 arm; C2b = the harness verbs, the bench extraction (G4, G4b), `--log`, G9, G14 and acceptance (a)–(e). No item is dropped | `[S6]` §6 confirmation 7, §10 ruling 7, §3 WP-13 |
| §10 C2 (g) | "each of the **twelve** keys" → "each key of `hecke::MathSettings::keys()` as registered at the tree under test", the count printed and reconciled against `[X]` §1.5, never written here | `[WP6-10]` §4.4; `[S6]` §2.3 item 9 |
| §10 C2 (g) | **the exit-5 arm moves back into C2 (C2a)**: `field_polynomial = conway` is the registered value this build cannot execute, as the v3.2 text foresaw | `[S6]` §2.3 item 9, §3 WP-13 scope 4 |
| §10 C4 (d) | "`--all` wall time grows by < 5 s" → `Σ_V t(V) ≤ 5 s` over the validations C4 registers in `fast` + `standard`, each the min of three isolated runs at `ENGINE_THREADS=16`; `--all`'s total reported, not gated; `5 s` retained, unjustified | `[WP6-10]` §4.2 |
| §10 C5 (c) | "`[M §8]`'s identities 1–6" → every identity item `hecke_ext::HeckeIdentityCertificate` defines at the tree under test, the item count read from the certificate | `[WP6-10]` §4.3 |
| §10 graph, schedule, totals | C2 → C2a (slot 6, 0.60 AU) then C2b (slot 7, ≈ 0.90 AU); C4 gated on C2b | `[S6]` §3 WP-13, §6 item cost line |
| §11 | `ConsoleSettingsValidation` is C2a's, and carries the exit-5 arm on `conway`; `ConsoleDeterminismValidation` is C2b / C4's | `[S6]` §3 WP-13 |

**v3.3 (2026-09-22)** — slot-5 WP-11, on slot-5 WP-10's §7. **Status and two bindings; no design
decision, phase boundary or acceptance criterion moves.** One line per changed section:

| Section | Change | Source |
|---|---|---|
| Header | v3.2 → v3.3; C1b's one deferral **closed**; companion pointers to `[C]` v1.7.0 / `[E]` v1.6.0 | slot-5 WP-10 §7 item 1 |
| Head status block | the slot-4 "not bound in C1b" list annotated: the two verbs are done, the rest stand | slot-5 WP-10 §1 |
| §3.5 | `bernoulli_mod(w, ell)` leaves phase **C5** for **shipped**, registered by `HeckeExt/RegisterHeckeExtensionVerbs.cpp` as the v3.2 row predicted; a new **`glover_factors(n, ell)`** row returning a `Record`, with the **standard-module `det`-twist convention** stated, because a reader against a dual-convention table reads every `j_i` wrong | slot-5 WP-10 §7 items 1, 2; `[E]` v1.6.0 `cl:glover` |
| §3.6 | `crosschecks` → `Record` **confirmed**, not changed: it was corrected at v3.2 already (`[WP4-5]` §5 item 2 was taken then) | — |
| §10 C5 | both verb names dropped from the phase's goal list; scripts `017`–`020` recorded as **early, partial C5** — `[X]` §8 slot-5 Lane C's E0–E2 scripts — with C5 *proper* still gated on E5's record-schema freeze (now `hecke_ext/v2`, slot-5 WP-1) | slot-5 WP-10 §3, §7 item 4 |
| §11 | `ConsoleScriptValidation` **20** scripts / **277 checks** (was 16 / 259), the 16 pre-existing `.expected` byte-unchanged; its registration arm now also asserts the two new verbs resolve | slot-5 WP-10 §4 |
| §14.3 | G13's row: `bernoulli_mod` **bound**, with `glover_factors` | slot-5 WP-10 §1 |

**v3.2 (2026-09-21)** — slot-4 WP-8. Sources: `[WP4-5]` §7 findings 1–7 (C1b's own report),
`[WP4-7]` §5 finding F5, the slot-4 plan §2.2's `[P]` list and §2.3 item 4, and `[OD]`'s
slot-4 confirmations 3 and 4. One line per changed section:

| Section | Change | Source |
|---|---|---|
| Header | v3.1 → v3.2; **C1b implemented**; the companion pointers to `[C]` v1.6.0 / `[E]` v1.5.0 | slot-4 WP-5, WP-8 |
| §2 C4 | one sentence: **register the verbs before you construct a `Session`** — the authoritative store is a session member while the installer is on the registry, so a `Session` built first silently has no mathematical settings; and the keys under their registered names (`sturm`, `sturm_unavailable`, `commutant_budget`) | `[WP4-5]` §7 item 4; `[E]` §7 |
| §2 C5 | `level_c.locality.source` is a **value-bearing record field**: passing a non-`default` source for a value equal to the default moves published text | `[WP4-5]` §7 item 5 |
| §3.5 | a **phase** column, so the table says what is bound today and what is C2's or C5's; `bernoulli_mod`'s row re-pointed to the shipped `HeckeExt/HeckePredictions` | slot-4 plan §2.2; `[WP4-7]` F5 |
| §3.6 | `CrossChecks` produces a **`Record`**, not a handle type; the `LocalSystem` presets are **C1b's** and carry no model, so `hecke` / `family` refuse them by name and `LocalSystem.n` on a preset is `d_V − 1` with no `Sym^n` meaning | `[WP4-5]` §7 items 1, 2 |
| §9 | the shipped `Bindings/` tree: `Bindings.{h,cpp}`, `Payloads.h`, `Presets.cpp`, **`Reproducibility.cpp`** (where `golden()` lives), `Decomposition.cpp`; and `HeckeExt/RegisterHeckeExtensionVerbs.{h,cpp}` with the two guard exceptions spelled out | `[WP4-5]` §1.4, §3; slot-4 plan §2.3 item 4 |
| §10 C1b | marked **IMPLEMENTED**; the obsolete `locality = strict` `expect_error` line dropped in favour of `015_strict_locality.oc`; the script set is **16** numbered scripts | `[WP4-5]` §7 item 3 |
| §11 | `ConsoleScriptValidation` at C1b (16 scripts, 259 checks); `ConsoleScriptEmit` shipped and owner-gated; **`ConsoleC0Validation`'s tree arm narrowed** from "no `.expected` under `Console/`" to "no frozen transcript names a pre-E0b decomposition object" | `[WP4-5]` §1.6, §7 item 7 |
| §11, §13 | what the frozen-CLI gate protects (an **additive** `--bench` mode is not a regression; the re-capture protocol) and **R20**, the risk it answers | `[WP4-2]` §3 |
| §14.3 | `bernoulli_mod` exists (`HeckeExt/HeckePredictions`, slot-4 WP-7) and is bindable; `HeckeCanonicalField` and the atlas are slot 5's | `[WP4-7]` F5; `[OD]` slot-4 confirmation 3 |

**v3 (2026-09-16)** — slot-2 WP-12. Sources: `[WP6]` §5 items 1–7, `[WP5]` §2's nine deviations,
`[WP2-11]` §5 items 1–6, `[WP2-1]` / `[WP2-2]` / `[WP3]` / `[WP2-5]` for what is implemented, `[X]`
§1.3.1 / §1.5 / §8, `[E]` §7, and `[S2]` §2.3 / §3 WP-12 / §6. One line per changed section:

| Section | Change | Source |
|---|---|---|
| Header | v2 → v3; branch and validation count refreshed; `[X]`/`[E]`/`[C]`/`[OD]`/`[S2]`/`[WPn]` citation keys added; the C0 status block rewritten as **eight adopted deviations** + one process note + two C1 debts | `[WP5]` §2 |
| §2 C4 | **Three setting families**; the twelve R1 **mathematical settings** with their defaults, bound to `Hecke/HeckeSettings`; the fingerprint rule, the recorded `source`, thread-local propagation onto `run_concurrently`; `locality = strict` legal-but-unimplemented; the two console-owned presentation keys C0 registers | `[WP6]` §5 item 3, `[X]` §1.5, `[E]` §7, `[WP2-1]` §1.1, `[WP5]` §2 dev. 8 |
| §2 C5 | canonical vs display printing; the FNV header is `src/ModArithmetic/Fnv.h` (G5 **closed**) and the lookup is `Golden/GoldenHarness.h`'s **one** `GoldenLookup`; the fingerprint enters `hash(x)`; **resumed handles** — `state` / `resume` / `save_state`, the `resumable` object, the sidecar rule, resume-invariance, and `not_applicable` at `n = 0` | `[WP6]` §5 items 1, 2, 4; `[WP2-11]` items 1, 2, 5; `[X]` §1.3.1 |
| §2 C7, §6, §8 | `hecke::NotImplementedInThisBuild` inserted in the catch order (before `std::runtime_error`, like `HeckeOverflow`); its own message and **exit code 5**, added to the exit-code table as a C2 addition | `[WP2-11]` item 3, `[WP2-1]` §1.1 |
| §2 C8, §9 | TU layout corrected: `ConsoleC0Validation` outside `Core/`, `ScriptRunner` in C0 and `ConsoleCli` in C1a, `CONSOLE_CHECK`, no `Util/Fnv.h` / `Util/GoldenLookup.h`; `check_console_includes.sh`'s two rules spelled out; **`ConsoleArchitectureValidation` retired as a name** | `[WP5]` §2 dev. 2, 6, 7; `[S2]` §3 WP-12 item 5 |
| §3.2 | `quit` given its production; the `-2 ^ 2 == 4` precedence stated and its reference-manual debt recorded | `[WP5]` §2 dev. 3, 5 |
| §3.3, §4.3, §4.4 | the two print renderings; `?x` prints the three setting families, the fingerprint and a `resumable:` line; the two things the generated reference must say in words | `[WP5]` §2 dev. 4 |
| §3.6 | `Report` is `hecke_report/v2`; the **four degree members per complex**, never a maximum, and the campaign's `degrees` kept distinct; the `[X]` v1.5.1 reserved types and verbs; the extension namespace is `hecke_ext` | `[WP2-11]` items 4, 6; `[WP6]` §5 item 5; `[E]` §7 |
| §10 | C0 marked **IMPLEMENTED** with its result; **C1 split into C1a / C1b** with the E0b gate stated and `hecke_report/v2` named as the frozen shape; C2 acceptance (g)/(h); C5 scheduled after E5's schema freeze; a **schedule table** (C1a slot 3, C1 through slots 3–4/5, C2 6–7, C4 7, C5 8) | `[S2]` §3 WP-12 item 3–4, §2.3 item 3, §6 item 4; `[X]` §8 |
| §11 | `ConsoleC0Validation` replaces `ConsoleLanguageValidation`; `ConsoleArchitectureValidation` struck; **`--list` compared modulo appended names**; the new C2 arms | `[S2]` §2.3 item 6 |
| §12, §13 | rollback list without `Util/Fnv.h`/`GoldenLookup.h`; R13 half-closed; **R18** (a pin frozen against a moving schema) and **R19** (a pin under a non-default mathematical setting) added | `[WP2-2]`, §2 C4 |
| §14.2, §14.3 | G5 **CLOSED**; G13 re-pointed to `Golden/GoldenHarness.h` with the slot-1 sweep re-routed; G1 records that the re-baseline happened; G10 carries all four per-complex degree members | `[WP6]` §5 items 1–2, `[X]` §1.1, `[E]` §7 |
| §15, §16 Q7, §17 | the order as *executed*; Q7 re-examined and still "no" (E8's `Z/ell^k` stays under `2^64`); the audit closed except the contested A3(c), with A4 and A7 re-pointed | `[WP6]` §5 item 6, `[PA]` |

**v2 (2026-09-14)** — the revision after the independent audit `[PA]` (ACCEPT WITH AMENDMENTS):
factual errors E1–E12, contradictions I1–I5 and the §1.4 citation offsets fixed in place; all
sixteen amendments dispositioned in §17 (A3(c) contested, the rest adopted); the settings model
rewritten around the three in-process switches that already exist (G2/G3 withdrawn as phantoms);
the flagship example moved to `(10, 691)`; the line editor descoped to an optional C3; the split
implementation order adopted.

**v1** — the first architect's plan. Superseded in place.

---

## 1. Executive summary

**Where we are.** The binary has three hand-parsed entry points, all dispatched by string
comparison on `argv[1]` in `src/hacs/kernel.cu:127-172`: the validation
harness (`--list` / `--all` / `--all-full` / `<Name>…`, `kernel.cu:129-146, 165-172`), the
benchmark driver (`--bench`, `kernel.cu:148-152` → `bench::RunBench`, `Bench/BenchDriver.h:51`)
and the campaign driver (`--campaign`, `kernel.cu:154-158` → `campaign::RunCampaign`,
`Campaign/CampaignDriver.h:178`). The no-argument form runs a legacy benchmark verbatim
(`kernel.cu:76-110`). Every one of these re-implements the same construction recipe
(`BenchDriver.cpp:304-326`: `CreateSL2ZFundamentalDomainTriangulation → SL2ZTessellationTables →
relations → LocalSystemSimplicialComplex → EquivariantCohomologyOnK::compute_cohomology →
HeckeCosetTables → HeckeTauTable → HeckeOperatorOnK::compute → …`) and none of them lets a user
*compose*: there is no way to compute `T_2` and `T_3` on one cohomology object, feed both to
`HeckeModuleDecomposition`, inspect a block's minimal polynomial and then write a report — the
exact workflow `[S Stage 1–5]` needs — without writing C++. Engine settings are environment
variables; the global pool size is read **once** into a function-local static
(`ThreadPool.cpp:40-52`), while every other knob the console needs already has an in-process
override the validations use (`EngineRuntime.h:69-109`, `DenseElim.h:176-204`,
`EquivariantCohomologyOnK.h:224-275`, `HeckeOperatorOnK.h:361-415`). Objects print through
per-class `to_string()` (`FlatMatrix.h:131`, `EquivariantCohomologyOnK.h:194`,
`HeckeOperatorOnK.h:263`, `FpPoly.h:105`) with no shared canonical form, and the only
reproducibility record of a computation is a campaign spec file (`Campaign/CampaignSpec.h:5-67`)
or a validation's C++ source.
*(v3.6.1, pointers re-read at `5c70e95`: `--bench` is
`kernel.cu:153-157` → `bench::RunBench`, `Bench/BenchDriver.h:154`, with the per-mode
`bench::RunMode` at `:124` since C2b; `--campaign` is `kernel.cu:159-163` →
`Campaign/CampaignDriver.h:208`; the recipe is `BenchDriver.cpp:312-319` (cohomology) and
`:359-368` (cosets, tau, operator). The paragraph describes the state before the console; the
other pointers in it are kept as written.)*

**Where we are going.** A small, deterministic, hand-rolled scripting language — working name
**OC script**, files `*.oc` — with a script runner (`--script f.oc`, `-c "…"`, stdin), an
interactive mode, and a value model that wraps the pipeline's objects as shared, lazily computed
handles; a verb registry populated by an explicit table (the `ValidationRegistry` pattern,
`ValidationRegistry.h:43-50`) to which the Hecke extension engine adds its own types and verbs
without touching the evaluator; scripts + checked-in expected outputs as a new `fast`-tier
validation (`ConsoleScriptValidation`); and session settings that replace the environment
variables through the existing in-process overrides. **Nothing computed changes**: the console
only calls the public API the validations, `--bench` and `--campaign` already call, and every
existing CLI form keeps its exact behaviour (gated by `ConsoleCliPreservationValidation`, §11).

**The six decisions that shape everything** (rationale and alternatives in §2):

| # | Decision |
|---|---|
| C1 | **A small expression language, not a command language and not an embedded interpreter**: assignment, calls with keyword arguments, member access, `for`/`if`, lists, integers/strings/booleans, `include`, script parameters; no user-defined functions, no `while` in the first release. Hand-rolled lexer/parser/evaluator (D6). |
| C2 | **Handles, not copies**: every pipeline object is a `shared_ptr<Object>` with keep-alive edges to what it borrows (the pipeline holds raw pointers and demands "must outlive", `HeckeOperatorOnK.h:199-207`), computed lazily on first use under the **settings snapshot taken at its creation**, never retried after a failure. |
| C3 | **One-way dependency, two TU groups**: a `ConsoleCore` static library with zero pipeline dependency (lexer, parser, evaluator, `Int/Bool/String/List/Record`, registry, printer, session, script runner), and *bindings* — including the arithmetic types `Fp`/`Poly`/`Matrix` — compiled into `cohomology_app` like `BenchDriver.cpp` is (`CMakeLists.txt:380-386`), because the pipeline itself is not a library (`CMakeLists.txt:342-619`). |
| C4 | **Settings are session-owned values applied through the existing public setters** — `set threads = 4` installs a console-owned `ThreadPool` via `set_consumer_pool_override` (`EngineRuntime.h:67`) exactly as the campaign driver does per job (`CampaignDriver.cpp:98-104`); `set backend = legacy` is the three existing scoped switches, which already reproduce `ENGINE_BACKEND=legacy` in-process (`DenseElim.h:204`, `EquivariantCohomologyOnK.cpp:390`, `HeckeOperatorOnK.cpp:306`); `set device` edits `PassOptions` only (`Passes.cpp:133-139`). **No engine substrate edit is needed.** A knob with no in-process override is documented as env-only, never silently accepted. **Settings come in three families** (v3): engine knobs, which change no value; the **mathematical settings** of `[X]` §1.5 (registered by their consuming phases — eight at v3.4; the count is `hecke::MathSettings::keys()`'s, never a literal here), each of which *may* change a published value and whose fingerprint therefore enters `hash(x)`; and two console-owned presentation keys. The engine owns every default and every check — the console sets, it never re-implements. |
| C5 | **Deterministic output by construction**: canonical printers, no timings on stdout unless asked (`#~`-tagged lines), the pipeline's own `std::cout` **and `std::cerr`** chatter redirected during verb execution, and a per-kind `hash()` that is byte-identical to the golden harness's (`GoldenHarness.cpp:76-81`) with a read-only lookup into `GoldenReference.inc` — so a script's transcript is comparable byte for byte across threads, devices and builds. |
| C6 | **Dumb line input first; no readline; the termios editor is unscheduled**: `--console` reads `std::getline`, and `rlwrap ./hacs --console` — a user-installed tool, nothing in the tree — gives history and editing. The hand-rolled editor of §7 keeps its design and its acceptance gate verbatim as an optional phase C3, commissioned only on owner demand (Q3). |

---

## 2. Design decisions with rationale

### C1 — Language shape

**Chosen.** A dynamically typed expression language:

```
# (n, ell) = (10, 691): on the golden grid AND [S Stage 9]'s first test case
K   = sl2z_model()                               # model + tessellation tables + descriptor
L   = symmetric_power(K, n = 10, ell = 691)      # LocalSystemSimplicialComplex
H   = cohomology(L)                              # lazy; computed on first use
H.dims                                           # -> [0, 3, 0]
assert(H.dims[1] == 3, "dim H^1 at (10, 691)")   # scalar pin: golden entry "dim_H^1" = 3 (GoldenReference.inc:7537)
T2  = hecke(H, p = 2)                            # cosets -> tau -> Theta -> A^(q), on first use
A   = T2.A(1)                                    # 3 x 3 matrix over F_691
charpoly(A)                                      # -> (X + 24)^3 printed high -> low degree
D   = decompose([T2, hecke(H, p = 3)], q = 1)    # HeckeModuleDecomposition, certified
for b in D.blocks { print(b.dim, b.residue_degree, b.min_poly(2), b.jordan(2)) }
                                                 # -> 3 1 X^2 + 48*X + 576 [2, 1]   (the non-split (2,1) block, [I §3.3])
assert(hash(A) == golden("n=10 ell=691 p=2 r=1", "A(T_p)^1"), "golden A^(1)")
report(D, path = "hecke_report_ell691_n10.json")
```

(The `n = 8, ell = 134217757` row of the campaign documentation — `charpoly_A1 = 134217244;1`,
i.e. `X − 513 = X − σ_9(2)`, `docs/matrix-engine/campaign.md:199` — remains a good *unpinned*
illustration; it is **off the golden grid** `{0,1,2,4,10,16,22,24} ∪ {(32,5)}`
(`GoldenHarness.cpp:160-173`) and therefore must not carry a `hash()` assertion — rule R10.)

Statements: assignment, expression (its value is printed unless the statement ends in `;`),
`for x in <list> { … }`, `if … { … } else { … }`, `set key = value`, `include("path.oc")`,
`help [name]`, `?name`, `quit`. Expressions: literals (decimal / hex integers, strings,
`true`/`false`), lists `[…]`, binary `+ - * / % ^`, comparison, `and` / `or` / `not`, unary `-`,
call `f(a, k = v)`, member `x.f`, method `x.f(…)`, index `x[i]`, and `args.name` for script
parameters (§6). Comments `#` and `//` to end of line — the campaign spec's convention
(`CampaignSpec.h:16`, `docs/matrix-engine/campaign.md:35`). Full grammar in §3.

**Alternatives considered.**

* *(a) A verb-per-line command language* like the campaign spec (`key = value`, `---` sections,
  `CampaignSpec.h:15-21`). Rejected: it cannot express composition — `decompose([hecke(H, p=2),
  hecke(H, p=3)])` — which is the whole point; every `[S Stage 2–5]` step is a function of the
  results of the previous one.
* *(b) Embedding Lua / a Python module.* Rejected by D6 (`[ME §2 D6]`; `CampaignSpec.h:13-14`
  restates it for parsers). It would also make the reproducibility record depend on an external
  interpreter version.
* *(c) A "real" language* with user functions, closures, `while`, exceptions. Rejected for the
  first release: every construct is surface area the extension engine does not need, and
  termination of a script is a property worth keeping trivial (a `for` over a finite list always
  terminates; the validation harness runs scripts unattended). Functions are the one feature
  most likely to be wanted later (parametrising `[S Stage 9]`'s test cases beyond what script
  parameters and `include` give) and are reserved as an owner decision (Q2, §16) with a design
  that does not disturb the grammar (`def name(args) { … }`).
* *(d) Prefix / Lisp-style syntax.* Trivially parseable, but the users are mathematicians who
  will compare against Magma / PARI / Sage; infix wins on readability at ~400 lines of parser.

### C2 — Object model

Every pipeline object is held by a `std::shared_ptr<console::Object>`; the `Object` owns the C++
instance and **keep-alive `shared_ptr`s to every object it borrows**. The pipeline's contract is
raw pointers with "must outlive this object": `HeckeOperatorOnKT(const EquivariantCohomologyOnKT*,
const HeckeCosetTablesT*, const HeckeTauTableT*)` (`HeckeOperatorOnK.h:206-207`, contract at
`:199-205`, stored at `:280-282`), `HeckeTauTableT` itself borrows `K_`, `model_`, `cosets_`
(`HeckeTauTable.h:298-300`), `HeckeOperatorFamily(const EquivariantCohomologyOnK*, const
SimplicialComplex&, const SL2ZTessellationTables&, …)` (`HeckeOperatorFamily.h:111-112`, "must
outlive this object and every reference/value it returns" `:103-110`, stored at `:250-252`),
`HeckeCrossChecks` (`HeckeCrossChecks.h:167-169`), `HeckeReportInput::decomp` and its
`level_a_stream` pointers (`HeckeReport.h:98-101, 111-115`), `EquivariantCohomologyOnKT(const
LocalSystemSimplicialComplexT*)` (`EquivariantCohomologyOnK.h:113, 126`). A console user who
writes `T = hecke(cohomology(L), p=2)` and never binds the intermediate must still get a valid
`T`; the keep-alive edges are what make that true (§4.1 has the full graph).

Consequences:

* **Logically immutable after construction; internally caching.** Console values are never
  mutated in place; `set_entry`-style operations are not exposed (the substrate's caches assume
  frozen inputs — lazy RREF caches invalidated on mutation, CLAUDE.md "Conventions",
  `FlatMatrix.h:61`). Arithmetic verbs return new objects. `Family` is the one type whose C++
  methods are non-`const` (`T_p`, `T_p_pow`, `prepare` fill a cache keyed by `(p, r)`,
  `HeckeOperatorFamily.h:263-270`); that is invisible to a script and safe on one thread.
* **Laziness is preserved, not added.** The pipeline is already lazy at every level
  (`get_Theta_flat_matrices()` "materialised … on the first call and cached",
  `HeckeOperatorOnK.h:220-226`; `HeckeOperatorFamily::T_p` "cached: the first call … builds and
  owns", `:115-119`; `get_*_bases_fm()` materialise lazily, CLAUDE.md "Block model"). The console
  adds one more level: `hecke(H, p=2)` returns a handle whose `compute()` runs on the first access
  of a computed member (`.A(q)`, `.Theta(q)`, `.certificates`), so `T2 = hecke(H, p=2)` on a line of
  its own costs nothing and `?T2` reports `state: declared`. An explicit `compute(T2)` exists.
* **Settings are captured at creation, not at compute.** Every handle snapshots the session's
  effective settings when it is created and installs that snapshot around its own `compute()`
  (§2 C4); `?x` prints the snapshot. Without this, `set lean = true; T = hecke(H, p=2); set lean
  = false; T.A(1)` would compute non-lean, and a transcript would misstate the arm it ran under
  (audit §3.2).
* **Failure is a bound state.** If `compute()` throws, the handle enters `failed`, stores the
  error, rethrows it on every later access, and is **never retried**: idempotence of `compute()`
  is documented only after success (`computed_` is set last — `HeckeOperatorOnK.cpp:945, 1550`,
  `HeckeModuleDecomposition.cpp:401, 517, 559, 767`) and nothing specifies the state after a throw
  except in `HeckeOperatorFamily`, which inserts into its cache only after success
  (`HeckeOperatorFamily.cpp:108-115`). A *verb-time* error (a type or contract error raised
  before any object exists, e.g. a 64-bit object handed to `family`) creates nothing, so the
  assignment does not happen. §8 has the table.
* **Expensive objects never copy.** A console `Matrix` holds *either* a `FlatMatrixT<Elt>` or a
  `MatrixT<Elt>` (the deprecated dense type, `Matrix.h:111`) and converts lazily on demand,
  caching the other form. `.A(q)` therefore *shares* the `MatrixT` inside `HeckeOperatorOnK`
  (`get_H_matrices()` returns a `const&`, `HeckeOperatorOnK.h:231`) through a keep-alive edge, and
  `charpoly(A)` / `minpoly(A)` call `CharPolyBerkowitz` / `MinPolyKrylov` (`FpPoly.h:125, 129`,
  which take `MatrixT`) on it with **no conversion at all**; arithmetic verbs produce
  `FlatMatrixT`. `Theta(q)` exposes the `BlockMat` (`HeckeOperatorOnK.h:217`) and materialises the
  flat form only under `dense(...)`.
* **Printing has three tiers**: `print(x)` / bare expression — one line or a small block with a
  size cap (`print_max_entries`, default 400); `show(x)` — the full canonical form; `?x` /
  `describe(x)` — type, state, dimensions, settings snapshot, creation site, members.
  (v3.14.0-pre.2) `display(x, ...)` forces each declared handle, then shows each argument: as `show(x)` on a
  terminal or in a script, as a rendered value (a §18.4 `value` frame) in a served notebook.
  `hash(x)` — the per-kind golden hash (§2 C5).
* **Element width is a property of the object.** `symmetric_power(K, n, ell)` picks `uint32_t` or
  `uint64_t` from `ell` exactly as the campaign does (`docs/matrix-engine/campaign.md:47` "ℓ ≥ 2^32
  selects the `uint64_t` pipeline"); the object carries the width and verbs that only exist at 32
  bits (`HeckeOperatorFamily`, `HeckeModuleDecomposition`, `HeckeCrossChecks`, `HeckeReport` are
  not templated — `HeckeOperatorFamily.h:102`, `HeckeModuleDecomposition.h:152`,
  `HeckeCrossChecks.h:116`, `HeckeReport.h:88`) fail with a typed error on a 64-bit object (gap G6,
  §14). `[I §1 Stage 0]` records that `ℓ < 2^32` is irrelevant to the extension engine.
  *(v3.9.3: under a non-default `coefficient_ring` the width follows the MODULUS `ell^k` exactly as the
  campaign's ring job loop picks it — `uint32_t` below `2^32`, `uint64_t` up to `2^64`, the digit route
  beyond; §3.6 "Wide handles".)*

**Alternative considered:** value semantics with copy-on-write. Rejected: the objects are not
copyable in any useful sense (they hold pointers to each other and to the block pool
`EquivariantCohomologyOnK.h:148`), and nothing in the workflow mutates.

### C3 — Verb registry and extensibility

The evaluator knows *no* verb and *no* type. Both come from a registry:

```
struct TypeInfo  { name; describe; print; show; hash; members; methods; };
struct VerbEntry { name; overloads: [ (signature, impl, doc) ]; };
void Registry::register_type(TypeInfo);
void Registry::register_verb(name, signature, impl, doc);
```

populated by **explicit registration functions** called from `kernel.cu` — `console::RegisterCoreVerbs`
(ConsoleCore's own types: `Int`, `Bool`, `String`, `List`, `Record`), `console::RegisterPipelineVerbs`
(the bindings, including `Fp`/`Poly`/`Matrix`), and, later, `RegisterHeckeExtensionVerbs` from the
extension engine's own TU. The reason is the one `ValidationRegistry.h:43-50` records:
self-registering statics in a static library are dropped by the linker when nothing references
the TU. Overload resolution is by arity then by argument type, first match in registration
order, so an extension can add `charpoly(MatrixQ)` next to `charpoly(Matrix)` without editing
either. Because `ConsoleCore` cannot see the bindings (one-way dependency), the `kernel.cu`
branch calls two symbols — `RegisterPipelineVerbs()` then `RunConsole()` — in one branch.

### C4 — Session settings instead of environment variables

**Three families, not one** (v3; owner decision `[OD]` R1, `[X]` §1.5). A setting belongs to
exactly one:

* **engine knobs** — `threads`, `device`, `backend`, `lean`, … The table below. **None of them
  can change a computed value**; they change how fast it is produced. Registered in C2.
* **mathematical settings** — `final_mode`, `locality`, `sturm`, `sturm_unavailable`,
  `u_ell`, `commutant_budget`, … The second table below. **Every one of them may change a
  published value.** Registered through the engine-owned registry of `Hecke/HeckeSettings`,
  never re-implemented here; **shipped in C1b** (slot-4 WP-5) rather than waiting for C2,
  as a third registry seam that walks `hecke::MathSettings::keys()` and validates and applies
  through `MathSettings::set()` alone, so a key a later slot appends needs no console edit.
  **The names are the registry's**, not this plan's earlier dotted spellings: `sturm`
  (with `cap=<B>`) and `sturm_unavailable`, never `sturm.cap` / `sturm.unavailable`
  (v3.2; `[E]` §7).
* *(v3.15.0-pre.1, NBCONFIRM S3)* **console policy keys of the cost confirmation (§7.1)** — `confirm`
  (`ask` | `yes` | `no`, default `ask`) and `confirm_wall_s` (Int ≥ 0, default 60): engine family, no `apply` hook,
  never a hash input, never serve-settable in this version; registered by `RegisterConfirmSettings`
  (`Console/Core/Confirm.h`) from the engine-settings installer.
* **console-owned presentation keys** — `print_max_entries` (default 400) and `verbose`
  (default: off in script mode, on in the REPL). They have no engine counterpart, they change no
  value and no hash, and they are the only two settings **C0 registers itself** (`[WP5]` §2
  deviation 8, adopted). Everything else arrives with its owning phase.

`settings()` prints all three families with each key's `source`; `?x` prints the handle's
snapshot the same way.

**Register before you construct a `Session`** (v3.2; `[WP4-5]` §7 item 4). The authoritative
store of every setting is a **session** member, while the installer that seeds it from the
engine's registry hangs off the **registry**. A `Session` constructed before the bindings have
registered therefore comes up with the console-owned presentation keys and *no* mathematical
settings, silently: `set locality = strict` then fails as an undeclared key rather than as a bad
value. `kernel.cu`'s console branch registers first and is correct; a host that holds a `Session`
as a member must either register in its own constructor's initialiser list or re-run the
installer by hand. A `Session::attach_registry_settings()` that makes the order irrelevant is a
C2 candidate, not a C1b defect.

#### Engine knobs

What each knob is today and what the console does (all verified; the audit's E6–E8, E12 are
incorporated):

| Setting | Today | Scope of the override | Console mechanism |
|---|---|---|---|
| `threads` | `ENGINE_THREADS` → `ThreadPool::default_threads()` `ThreadPool.cpp:40-47`; `ThreadPool::global()` is a function-local static `:49-52` (**read once**) | `set_consumer_pool_override` is **thread-local** (`EngineRuntime.cpp:23`) | own a `ThreadPool(n)` (`ThreadPool.h:46`) and call `set_consumer_pool_override` (`EngineRuntime.h:67`); precedent `CampaignDriver.cpp:98-104`; `EngineDeterminismValidation` runs 1/4/16/32 this way (`EngineRuntime.h:11-16`) |
| `batch`, `ksplit`, `arena`, `cse`, `fuse`, `layout`, `device` | `PassOptions::from_env()` `Passes.cpp:126-140`, re-read at every compile unless overridden (`EngineRuntime.cpp:55-68`) | **process-global**, mutex-guarded (`EngineRuntime.cpp:24-26`) | `set_pass_options_override` (`EngineRuntime.h:81`) with the edited struct (`Program.h:187-205`); the program-cache key carries the options fingerprint (`EngineRuntime.h:148`) so switching is safe. `device` is **only** this: the tape's device decision is pass 6 on `PassOptions::policy` (`Passes.cpp:133-139`); `cuda::requested_device()` / `device_enabled()` (`CudaCtx.cpp:116-125`, `CudaCtx.h:50-51`) have **no caller** in the tree and `InstallMicroHooks()` only registers the `--bench micro --backend gpu` kernels (`CudaBench.cpp:330-335`) — neither is touched *(v3.7, slot-9 WP-6, `5689c20`: the override now reaches the tape elimination driver's per-panel programs too — `elim_pass_options()` is `consumer_pass_options()`, which it was not before, so `set batch` / `set device` apply there; and the options fingerprint's device bit follows the **effective** policy, so a `policy`-only `gpu` or `hybrid` value keys its programs apart from the CPU's (`hybrid` and `gpu` still share the bit); `ENGINE_API.md` §10.6, §10.9; `EngineElimPassOptionsValidation`. No value, digest or golden line moved.)* |
| `backend` | `ENGINE_BACKEND=legacy` → `backend_is_legacy()` static (`EngineConfig.h:7-13`) | the three in-process switches are thread-local: `elim::ScopedLegacy` (`DenseElim.h:198`, `DenseElim.cpp:33`), `set_legacy_cohomology_path_forced` (`EquivariantCohomologyOnK.h:246`), `set_legacy_hecke_operator_path_forced` (`HeckeOperatorOnK.h:363`) | those three. They **already reproduce** `ENGINE_BACKEND=legacy` in-process: every `FlatMatrix` retrofit path reads `engine::elim::use_legacy()` (`FlatMatrix.cpp:68, 1358, 1492, 1599`) `== backend_is_legacy() \|\| legacy_forced()` (`DenseElim.h:204`), and the two consumers OR the static with their own flag (`EquivariantCohomologyOnK.cpp:390`, `HeckeOperatorOnK.cpp:306`) — which is how `--bench micro --backend legacy` and the legacy validation arms work today. *(S24 CL-L2: all of it is compiled only with `OC_ENABLE_LEGACY=ON`; an OFF build keeps the setting and its two values but refuses `backend = "legacy"` — and `micro(…, backend = "legacy")` — with `NotImplementedError`, exit 5.)* |
| `lean`, `theta_eq_certify`, `retain_intermediates`, `vacuous_shortcircuit` | plain setters `HeckeOperatorOnK.h:375, 406`, `EquivariantCohomologyOnK.h:226, 259` | thread-local (`EquivariantCohomologyOnK.cpp:338-340`, `HeckeOperatorOnK.cpp:280-282`) | those setters |
| `program_cache` | `set_program_cache_bypassed` (`EngineRuntime.h:101`) | **process-global** `std::atomic` (`EngineRuntime.cpp:27`) | that setter; verb `clear_program_cache()` → `ProgramCache::global().clear()` (`ProgramCache.h:60, 63`) |
| **env-only (not settable; `settings()` shows their values as `source: env`)** | `ENGINE_HOST_THREADS` (`EngineRuntime.cpp:124-129`, static), `ENGINE_TILE_MULT` / `ENGINE_TILE_COLS` (`Executor.cpp:42-55`, static), `ENGINE_SPIN` (`ThreadPool.cpp:77`), `ENGINE_ELIM_BASE` (`DenseElim.cpp:26`), `ENGINE_CUDA_DISABLE` (`CudaCtx.cpp:68-75`, static), `ENGINE_CUDA_DEVICE` (`CudaCtx.cpp:57`), `ENGINE_CUDA_PROGRAM_CACHE` (`DeviceBackend.cpp:37-43`, static), `ENGINE_CUDA_GRAPH` / `ENGINE_CUDA_MERGE_LEVELS` (`DeviceBackend.cpp:33, 52`), every `ENGINE_TRACE_*` (`Executor.cpp:38`, `DenseElim.cpp:74`, `DeviceBackend.cpp:46`, `Passes.cpp:740`) | — | documented; `set` on one of these is an error naming the variable |

#### Mathematical settings (v3; `[OD]` R1, `[X]` §1.5, `[E]` §7)

These are **not** engine knobs: each is part of what a result *means*. The engine owns the
defaults, the allowed values and the validation — one struct, `Hecke/HeckeSettings.h`
(`hecke::MathSettings`, shipped in slot 2 WP-1, `[WP2-1]` §1.1) — and the console only *sets* them
through its registry. The console never re-implements a default or a check ("never twice", R1).

| Key | Values (**default**) | Console mechanism / notes |
|---|---|---|
| `final_mode` | `closure` \| `sturm_heuristic` (**`closure`**) | `set final_mode = "closure"` → `MathSettings::set(key, value, source = console)` |
| `sturm_unavailable` | `nonfinal` \| `heuristic` (**`nonfinal`**) | **the registered spelling** (v3.2, corrected from `sturm.unavailable`; slot-3 WP-2, `[E]` §7 item (e)). Dotted keys remain legal setting *names* — C0 parses the chain after `set` — but this key is not one |
| `sturm` | `auto` \| `off` \| `cap=<B>` (**`auto`**, `B = 12·B(k)`) | **the registered spelling** (v3.2, corrected from `sturm.cap`): the cap is a *value* of the `sturm` key, not a key of its own. The budget of the R3 `SturmState`; see "Resumed handles" in C5 |
| `commutant_budget` | modmul count (**`2·10^10`**) | v3.2; registered by slot-4 WP-1 after `sturm_unavailable`, the budget of the R3 `CommutantState` (`[X]` §1.3.1; `[OD]` slot-3 confirmation 3) |
| `locality` | `budget=<N>` \| `strict` (**`budget=64`**) | **registered today**, and `strict` **computes** since slot-3 WP-3 (v3.2: the v3 text "a legal value this build cannot execute" is struck, not merely marked). `budget=0` is rejected. `strict` is never the default, always has a non-zero fingerprint, and is byte-identical to budget mode wherever budget mode certifies |
| `field_polynomial` | `least` \| `conway` (**`least`**; `conway` parsed and rejected as not implemented) | |
| `split_field_report` | `canonical` \| `own_field` (**`canonical`**) | |
| `coefficient_ring` | `F_ell` \| `Z/ell^<k>`, `2 ≤ k ≤ 63` (**`F_ell`**; *v3.9*: `2 ≤ k ≤ 4096`, `[E]` v1.12.0 `sec:ring` (a), a parse cap; whether `ell^k` is served is decided at the cell — native below `2^64`, the digit route at and above it for `ell ≥ 5`) | E8; `Z/<n>` reserved. *(v3.13.0: `Z` is **un-reserved** by slot-24 D6 — grammar `F_ell` \| `Z/ell^<k>` \| `Z`; stored as `k = 0`, canonical text `Z`, fingerprint FNV-1a-64 of `coefficient_ring = Z\n`; honoured by the integral descent only (the verb `descent`, the campaign descent cells, the record `integral_descent_record/v1`), every other consumer refuses it by name with exit 5; `set coefficient_ring = "Z"` is legal and `--set coefficient_ring=Z` exits 0; only `Z/<m>` stays reserved. `[C]` `sec:recordschema` item 7, `def:ringsemantics`(3); `[E]` `sec:ring` (a). The v3.6 / v3.7 text below is history for `Z`.)* **v3.6: registered** by slot-8 WP-3 as the eleventh key, at the registry's tail; `[E]` v1.9.0 `sec:ring` (a) owns its grammar and refusal rule. `Z` and `Z/<m>` are refused **inside `MathSettings::set()`**, with `hecke::NotImplementedInThisBuild`; unlike `conway`, the value is never stored. The `set` statement surfaces that as **exit 5**: the binding seam `InstallMathSettings` (`Bindings/Decomposition.cpp:840`) maps it to `console::NotImplementedError`. The message carries **no `file:line:col`**, a known gap deferred to C5 (§6). `Z/ell^1` and other invalid texts are a bad value, exit 3. As a `--set` argument every refusal is exit 1 (§6). Under `Z/ell^<k>` every pipeline verb (`symmetric_power`, `cohomology`, `hecke`, `family`) refuses with exit 5, through a lazy handle too (§8). E8's objects are therefore **console-unreachable in slot 8** (`[S8]` ruling 4 (A)); C5 binds them (§10). Measured by `ConsoleErrorValidation` arm (K) and `HeckeReductionValidation` arm (X). *v3.7-pre.1, as built (slot-9 WP-12, `b3cd0d3`)*: the `set`-statement refusal **carries its `file:line:col`** (`set coefficient_ring = "Z"` prints `file:1:1: not implemented in this build: …`), and a `--set` argument naming a reserved value is **exit 5** (an invalid value and an undeclared key stay exit 1; §6). Under `Z/ell^<k>` at `ell ≥ 5` the verbs and members of `[E]` `sec:ring` (h) **honour** the ring — `symmetric_power`, `cohomology(L)` and `hecke(H, p)` at `r = 1` (§3.6, §10 C5) — and every other pipeline verb keeps exit 5, through a lazy handle too; at `ell ∈ {2, 3}` nothing is lifted. The E8 item-4b objects (boundary and cone over the ring) stay console-unreachable in slot 9 (`[E]` (h)). `ConsoleErrorValidation` arm (K), 210 checks |
| `predictions` | `annotate` \| `assert` (**`annotate`**) | |
| `presentation` | `off` \| `on` (**`off`**) | |
| `u_ell` | `auto` \| `off` \| `budget_mb=<M>` (**`auto`, `M = 2048`**) | |
| `integral_fallback` | `forbid` \| `allow` (**`forbid`**) | |
| `q_max` | integer (**derived**; settable only where `truncated = true`, E9) | see the per-complex degree members, §3.6 |

Thirteen keys as of v3.2 (`commutant_budget` appended by slot-4 WP-1), and the list is closed
until `[X]` §1.5 grows one. *(v3.6: the thirteen are the inventory. `hecke::MathSettings::keys()`
registers **eleven** of them at `5c70e95`: `integral_fallback` and `q_max` are not registered, and
`coefficient_ring` was the last to be added, by slot-8 WP-3. `ConsoleSettingsValidation` counts
`keys()`, never a literal.)* The registry is **append-only**
(a key is added at the end, never inserted), because the canonical text below walks it in order.

Three rules bind the console side:

1. **The fingerprint is part of `hash(x)`.** `MathSettings::canonical_text()` is the
   `key = value` lines of the **non-default** entries in registry order, and its FNV-1a-64
   (`src/ModArithmetic/Fnv.h`) is the **fingerprint** — `0` when everything is at its
   default. For every extension-layer type, `hash(x)` mixes the fingerprint into its input, so
   `hash` is per kind *and* per configuration. Consequence for §6: **the golden pins are the
   default configuration**, and a golden mismatch can never be explained by "a different setting".
   A script that pins a hash under a non-default mathematical setting is a script error, and
   `ConsoleScriptValidation` refuses it (§11).
2. **A setting is recorded, never inferred.** Every key carries `source ∈ {default, spec,
   console}`; `settings()` and `?x` print it. A handle's snapshot carries the mathematical subset
   separately (`SettingsSnapshot::mathematical()`), because that is the subset a reproducibility
   record hashes.
3. **Propagation.** `hecke::ScopedMathSettings` / `ScopedLocality` are `thread_local` and are
   propagated onto `engine::tape::run_concurrently()` task threads by a registered capture, just
   as the engine's own scoped options are (`[WP2-1]` §1.1). A handle's snapshot therefore follows
   its computation onto the host fan-out, and two concurrent pipelines under different `locality`
   cannot see each other's.

*(v3.1: this paragraph is obsolete — `locality = strict` is implemented since slot-3 WP-3; no
settings value raises `hecke::NotImplementedInThisBuild` today, which survives as the named
build-capability error behind exit 5. v3.4: the "no settings value" half is stale —
`field_polynomial = conway` parses, validates, moves the fingerprint and makes its consumer
(`HeckeExt/HeckeCanonicalField`) raise `hecke::NotImplementedInThisBuild`, since slot-5 WP-7; §10 C2a
(g) pins it.)* **`locality = strict` is legal and unimplemented for one slot** (slot-2 owner confirmation 3,
`[S2]` §6 item 3). It parses, it validates, it round-trips through `canonical_text()` and it
changes the fingerprint — and the consumer throws `hecke::NotImplementedInThisBuild`, whose
`what()` begins with the literal token `not_implemented_in_this_build:`. It is **never silently
degraded to budget mode**. The console must surface it as its own error class, not as "bad value":
see the C7 catch order and the §8 table.

**The session model (no RAII stack).** Every `Scoped*` guard restores the value it *saved* on
destruction, so a stack of guards replaced out of LIFO order restores stale values (audit §3.2).
The session therefore holds the **authoritative values** of every setting and applies them
through the plain setters above; `reset_settings()` re-applies a snapshot taken at session start
(the environment's values). `elim::ScopedLegacy` is depth-counted with no plain setter
(`DenseElim.h:176-200`) and is the single RAII member, held for as long as `backend = legacy`.
The two process-global overrides (pass options, cache bypass) are harmless on the session's one
thread; an in-session `run_validation` / `bench` / `run_campaign` would inherit them silently,
which is why those verbs run with the session overrides **lifted** by default (§5, A8(d)).
Thread-local settings reach `run_concurrently()` task threads through the registered capture
functions (`EngineRuntime.h:111-126`), so a handle's snapshot follows its computation onto the
host fan-out.

**Why not `setenv` + re-read?** Because the pool size and several others are read once into
statics, and because the in-process setters are what every validation arm already uses — the
console adds no second mechanism.

### C5 — Deterministic output and the reproducibility record

* **Canonical printers**, one per type, fixed for the life of a format version (`#! oc-format 1`
  is the first line of every `.expected` file). **Two renderings** (v3; `[WP5]` §2 deviation 4,
  adopted): `PrintCanonical` — the transcript form, which quotes a `String` — backs a bare
  expression statement, a list and a record; `PrintDisplay` — which prints a **top-level** `String`
  bare — backs `print(x)` and `str(x)`, so that `print("dim H^1")` is usable. Inside a compound
  value the two coincide, so a list of strings prints identically either way, and every
  `.expected` comparison sees exactly one form per position.
  Matrices print row-major with `[` `]` and single
  spaces; lists print `[a, b]`; **polynomials print high → low degree** in `FpPoly::to_string()`'s
  human convention (`FpPoly.h:105`), while `coeffs(f)`, `json(x)` and `hash(f)` use the machine
  order **low → high** of the report JSON (`"poly_coeff_order":"low->high degree (A-N4)"`,
  `HeckeReport.cpp:113`, `HeckeModuleDecomposition.cpp:1018`) and of the campaign table
  (`134217244;1`). The two orders are stated in `help charpoly`; console text and JSON do **not**
  share an order and are not claimed to.
* **`hash(x)` is per kind**, copied from `GoldenHarness.cpp:76-81`: FNV-1a-64 (offset
  `0xcbf29ce484222325`, prime `0x100000001b3`) fed byte-wise; a matrix as rows, cols, then entries
  widened to `uint64` row-major; a basis (list of matrices) as count then each matrix; a
  polynomial as count then coefficients low → high; a scalar invariant as that single `uint64`.
  **The one FNV-1a-64 is `src/ModArithmetic/Fnv.h`** (v3; gap G5 **closed** by
  hecke-extensions slot 1 WP-2, commit `6ecd3d5` + `8e6fdb5`): the three former copies
  (`GoldenHarness.cpp`, `CampaignDriver.cpp`, `PerformanceSmokeValidation.cpp`) were folded into
  it and it is the header C1 consumes. It is **not** `Util/Fnv.h` — `PerformanceSmokeValidation.cpp`
  is compiled into the `ModArithmetic` library (`CMakeLists.txt:195`), so `Util/` would be an
  upward include (`[WP6]` §5 item 1). `Program.h:231-233`'s `fnv_mix` (cache keys) and
  `BlockPool.h`'s word-wise hash (pool identity) are different functions and stay.
  The pin target is the read-only lookup `GoldenLookup(point, object)` over
  `GoldenReference.inc`, which C1a adds to **`Golden/GoldenHarness.h`** (gap G13), exposed as the
  verb `golden(point, object)`; today the `.inc` is only `#include`d by `GoldenHarness.cpp` and
  slot 1's `GoldenLocalitySweep` carries an internal lookup that C1a re-routes through the public
  one (v3: **one lookup, not two**, and no `Util/GoldenLookup.h` — `[X]` §1.1, `[WP6]` §5 item 2).
  **Shipped that way in C1a**, and the verb's home is `Bindings/Reproducibility.cpp` beside
  `hash` / `hash_int` / `fingerprint` / `save_state`, not `Bindings/Harness.cpp` (v3.2, where §9
  and §5 disagreed; `[WP4-5]`).
* **On an extension-layer type, `hash(x)` also mixes in the mathematical-settings fingerprint**
  (v3; C4 rule 1). At the defaults the fingerprint is `0`, which is what makes a golden pin a
  statement about the default configuration and nothing else.
* **A setting's `source` is itself a value** (v3.2; `[WP4-5]` §7 item 5). `level_c.locality`
  of `hecke_report/v2` carries `source ∈ {default, spec, console}`, and that field is part of
  the report **text** — so a record written at the default *value* but with `source = console`
  is a different record from one written at the default with `source = default`, and its hash
  differs. The fingerprint, which counts only *non-default* entries, is `0` in both. Anything
  that calls `hecke::MathSettings::set` outside a spec or console entry point must therefore
  pass the source the run actually had; passing `SettingSource::Console` for a value equal to
  the default moves published text. `[C]` `sec:recordschema` item 6(a) states the same rule for
  the extension record.
* **No timings on stdout by default.** `timed(expr)` returns `Record{value, wall_s, wall_us,
  peak_rss_mb, peak_rss_kb, allocs, alloc_bytes}`. `bench_line(record [, mode])` prints the
  tree's `BENCH …` format as a `#~` line. *(v3.5, as built by slot-7 WP-8.)* The console has no
  float type. Every time and every MiB figure is therefore a **String** (`"0.0421"`), with an
  **Int twin** in micro-units for arithmetic: `wall_us` / `total_us` for times, `peak_rss_kb` /
  `rss_kb` for memory. `time(expr)`, which was to print `#~ time <s>`, is **deferred**: it is
  unbound at C2b, and `timed` plus `bench_line` cover its use. The `.expected` comparison ignores every line
  beginning with `#~`; `bench(...)` output is `#~`-tagged wholesale.
* **The pipeline's own `std::cout` and `std::cerr` chatter is redirected.** Validations,
  `HeckeCrossChecks` (`HeckeCrossChecks.h:129-130` "details on std::cout"), the decomposition's
  block-dependent `NOTE` (`HeckeModuleDecomposition.cpp:725`), the legacy arm's `[TIMING]` lines
  (`EquivariantCohomologyOnK.cpp:1057, 1138`) and the SL(2,Z) setup's `std::cerr` warnings
  (`LocalSystemSL2Z.cpp:425, 494, 540`) print freely. The session captures the original
  `std::cout` streambuf at start-up and writes console output there; around every verb call it
  swaps **both** `std::cout`'s and `std::cerr`'s buffers to a sink (`set verbose = false`, the
  default in script mode) or leaves them alone (`set verbose = true`, the default in the REPL).
  `capture(expr)` returns the chatter as a string for scripts that *want* to assert on it. The
  `rdbuf` swap is process-global: any future `parallel_for` verb must give each task its own sink
  (R17).
* **Transcript.** `--log <file>` appends every input line and every output line, prefixed
  `> ` / nothing, so a REPL session is replayable as a script by stripping the prefix.

**Resumed handles** (v3; `[OD]` R3, `[X]` §1.3.1, `[E]` §7). A computation that a *budget* cuts
off is not a failure: it persists its iteration state, and the console is one of the two places
that state is meant to be continued from (the other is the record layer). Three verbs, all on
`Object`, all C2 (the mechanism is `ResumableState` / `TypeInfo::resume`, already in C0):

* **`state(x)`** — the `Record` `{kind, complete, budget, reached, budget_history}`, where
  `kind ∈ {sturm_bound, locality, commutant, u_ell, fill}` is `[E]` §7's list. `?x` prints it as
  a `resumable:` line whenever the handle has one.
* **`resume(x, budget = …)`** — returns a **new handle** continued *from `x.state()`*, never from
  scratch. It keeps `x`'s creation-time settings snapshot with **exactly one key changed** (the
  budget), appends the new budget to `budget_history`, and links back to `x`. Three refusals,
  each a typed error: a budget **below** what the state reached ("resume: budget below reached
  state"); a resume under a changed **non-budget** setting ("resume under a different setting →
  start a new computation"); and a resume on a handle that is not resumable. A resume on a
  **complete** state is a strict no-op returning the same outcome, the same certificate and the
  same state *including* the history. **(v3.5; `[S7]` §10 owner decision 6 (A).) This no-op is
  an engine-level statement.** The engine's resume on a complete state
  (`HeckeModuleDecomposition::resume_locality`) changes nothing, the history included, as
  `ConsoleSettingsValidation` (h) asserts. The console's `resume` on a complete **handle** is a
  fourth typed refusal ("… is complete"), and the refused call moves nothing
  (`ConsoleSettingsValidation` (h) asserts that too). The refusal is **conforming**: the handle
  already holds the engine's no-op outcome, so refusing a new handle loses nothing. The frozen
  transcript `014_expect_error.expected`, which pins the refusal for a complete `sturm_bound`, is
  **kept**.
* **`save_state(x [, path])`** — writes R3.1 item 6's object: `{kind, complete, budget, reached,
  budget_history, state}` inline when its JSON is ≤ 64 KiB, else a sidecar
  `<stem>.state.<kind>.json` referenced by relative path **and** its `Fnv.h` FNV-1a-64
  (`state_ref = {path, fnv64}`). With no stem the state is inlined regardless of size and flagged
  `state_oversize: true` — the shipped behaviour of `HeckeSturmBound` (`[WP3]`), which is R3
  instance 1. **Named `save_state`, not `save`** (v3): `[WP6]` §5 item 4 proposed `save(x)`, but
  §4.3 already gives `save(x, path)` the meaning "write the canonical *printed* form", and two
  verbs of the same name whose meaning turns on the argument count is exactly the ambiguity a
  transcript language must not have. Same object, unambiguous name.

**Resume-invariance is the gating property**, and the console asserts it: a handle created under
`locality = budget=8` and resumed to `64` must hash equal to a fresh handle under `64`, and the
two states must be equal **modulo `budget_history`** — `[8, 64]` against `[64]`, the one member
that must differ. `ConsoleSettingsValidation` carries that arm (§11). The two shipped instances
behave exactly so (`HeckeSturmBound`, `[WP3]`; `CommutantState`, `[WP2-5]`), so the console binds
a contract that is already twice implemented rather than inventing one.

A budgeted computation that is **not applicable** rather than incomplete reports so instead of
throwing: the Sturm handle at `n = 0` (`k = 2`, `M_2 = 0`) has `state(x).kind = sturm_bound` with
the record-level outcome **`not_applicable`**, which `?x` prints (`[E]` `def:bprime`, `[WP2-11]`
item 5). It is not an error and not an incomplete state.

### C6 — Interactive line input

**Chosen for release 1:** dumb mode — `std::getline`, prompt `oc> `, continuation `... ` while
brackets are unbalanced or the line ends in `\`, no echo tricks; identical under a pipe and a
terminal. Users who want history and editing run `rlwrap ./hacs --console` (a
user-installed tool; nothing enters the tree, so D6 is intact). The hand-rolled raw-mode editor
(POSIX `termios`: cursor keys, history file, Ctrl-A/E/K/U/L/D, Tab completion over registered
names, terminal restore on `atexit`/`SIGINT`, `_WIN32` fallback — the tree still ships
`src/hacs.sln`) is specified in §7 and kept as **optional phase C3**, gated by
the pty-driven `ConsoleLineReaderValidation`, commissioned only on owner demand (Q3).

**Alternatives.** *GNU readline* behind `-DCONSOLE_READLINE=ON`: full-featured, but GPL-3 (a
licensing decision the owner has not made), a link-time dependency that would be the tree's
first outside the CUDA toolkit (D6), and a second code path to validate. *libedit / linenoise*:
BSD, but still a third-party file in the tree, which D6 forbids as stated. *The termios editor
in release 1* (version 1 of this plan): ~1 AU of work whose value is independent of the
extension engine; the audit's `rlwrap` observation makes it deferrable at no loss.

### C7 — Error model

Every verb call runs inside one `try`, catching in this order: `console::AssertionFailure`,
`hecke::HeckeOverflow` (`ExactInt.h:25-27` — it *derives from* `std::runtime_error`, so it must
be caught first to be named), **`hecke::NotImplementedInThisBuild`** (v3; `HeckeSettings.h`, also
a `std::runtime_error`, so likewise before it — its `what()` begins with the literal token
`not_implemented_in_this_build:`, exported as `hecke::kNotImplementedInThisBuildTag`),
`std::logic_error` (every `ENGINE_CHECK`, `EngineCheck.h:40-56`,
message already `file:line: ENGINE_CHECK failed: cond`), `std::runtime_error` /
`std::invalid_argument` (the pipeline's contract violations, e.g. `HeckeOperatorOnK.h:207-208`,
`HeckeModuleDecomposition.h:159-165`, `HeckeModelDescriptor.h:76-80`), `std::bad_alloc`,
`std::exception`. Each becomes a `console::Error` carrying the script position of the *access*
that triggered the work, the creation site of the handle (so a lazy failure still names the
constructing line), and the C++ `what()`:

```
script.oc:14:7: error: T2.A(1): compute() failed
  object T2 created at script.oc:9:7 by hecke(H, p = 2)
  caused by: src/hacs/Hecke/HeckeOperatorOnK.cpp:NNN: ...
```

**`not_implemented_in_this_build` is its own outcome, not a bad value** (v3; `[WP2-11]` item 3).
`set locality = "strict"` is *accepted* by the settings layer — it is a legal value of a
registered key, it changes the fingerprint, and `settings()` shows it — and the **computation**
that would need it throws the typed error above. The console therefore prints

```
script.oc:14:7: not implemented in this build: D.blocks: locality = strict
  (the value is legal; the terminating strict-mode route lands in slot 3)
  object D created at script.oc:11:5 by decompose([T2, T3], q = 1)
```

with its **own** exit code — `5`, appended to the §6 table, so a script or a CI matrix can tell
"this build cannot do it" from "you asked for something wrong" (exit 1) and from "the computation
failed" (exit 3). It is never reported as an `invalid_argument`, and the console never degrades
the setting to its default: doing so would publish a result under a mode the build cannot prove.
`expect_error "not_implemented_in_this_build"` is the script-level test of it, and the C1a script
set carries one. *(v3.1: the `locality = strict` example is obsolete — strict mode computes since
slot-3 WP-3; C1a tests exit 5 through a test-only verb and a test-only lazy handle instead.)*

*(v3.6, C4 as built.)* Two paths used to lose exit 5, and C4 fixed both in the bindings:
* **A lazy handle.** `Object::ensure` (Core) wraps any non-console exception raised inside a
  handle's `compute()` as a runtime error, so a `hecke::NotImplementedInThisBuild` from a lazy
  handle surfaced as exit 3. C4's `bind::LazyCompute` (`Bindings/Bindings.h:113`) wraps the six
  lazy `Object::create` sites in `Cohomology.cpp`, `Hecke.cpp` and `Decomposition.cpp`. It
  translates that type into `console::NotImplementedError` first, so the handle fails with
  **exit 5**. Measured by `ConsoleErrorValidation` rows r05 and r06.
* **The `set` statement.** A value that `MathSettings::set()` itself refuses, `coefficient_ring =
  "Z"`, reaches the setting's validate lambda directly and never the registry's classifier. The
  binding `InstallMathSettings` now converts it to `console::NotImplementedError`, so it exits 5;
  a bad value still returns its reason and exits 3. The error **carries no position**, because
  `Evaluator::exec_set` (Core) never calls `ConsoleError::set_pos_if_unknown`. The fix is one line
  of Core, and Core is frozen in slot 8, so it is deferred to C5 (§6, §10 C5). Measured by
  `ConsoleErrorValidation` arm (K) and `HeckeReductionValidation` arm (X).

*(v3.7-pre.1, the Core batch as built; slot-9 WP-12, `b3cd0d3`, decision 2 (ii) (A).)* The
position gap is **closed**: `Evaluator::exec_set` now runs
`catch (ConsoleError& e) { e.set_pos_if_unknown(s.pos); throw; }`, so the `set`-statement refusal
carries `file:line:col`. One narrower gap remains, recorded and **not** fixed, because it needs a
Core edit the owner has not authorised: `Evaluator::object_member` does not wrap a C++ exception
raised by a **member getter** as a method call's is wrapped (`ThrowWrapped`). The gated types
convert their members' exceptions into console errors in the bindings (`GuardedMember`), so the
exit codes are right (5 and 3), but the error carries no position, a getter having none; the
type-level `resume` refusal lacks one for the same reason. The fix is one `try` / `catch` in Core,
the analogue of the `exec_set` back-fill, and belongs to the next authorised Core batch (§16.4).

*(v3.8-pre.1, specified; slot-10 decision 6 (i) (A), built by slot-10 WP-12.)* The owner authorised
**one named `Console/Core/` exception** to close that gap. It is binding in this form:
* **Site 1, `Evaluator::object_member`.** The getter call `m->get(obj)` runs inside one `try`, in
  the catch order of a method call (`eval_method`): a `ConsoleError` is **re-thrown with
  `set_pos_if_unknown(pos)`** (so the bindings' `GuardedMember` errors keep their kind and gain the
  member access's `file:line:col`, and an error that already carries a position keeps it);
  `ExitSignal` / `QuitSignal` pass through; any other `std::exception` goes through `ThrowWrapped`
  with the message `<Type>.<member> failed`, the member access's position and the object's creation
  site — so the registry's kind classifier decides its code exactly as for a method. The
  missing-member `TypeError` and the lazy `ensure_computed` path are unchanged (both already carry
  the position).
* **Site 2, the type-level `resume` refusal.** The core's `resume` verb (`CoreVerbs.cpp`) calls the
  type's `resume` hook inside one `try` that re-throws a `ConsoleError` with
  `set_pos_if_unknown(ctx.pos)`; the verb's own refusals already carry `ctx.pos` and are unchanged.
* **Exit codes do not move.** Every code the bindings produce today (5 for
  `NotImplementedInThisBuild`, 3 for a named `std::logic_error` or a runtime error, 3 for the
  type's non-budget resume text) is the code after the change; only the position is added. A
  frozen transcript records `stderr` only where a script prints it, so the prediction is **no
  transcript moves**; slot-10 WP-12's step 1 lists every transcript and pin that exercises a
  member-getter error and **stops** (an owner-gated re-baseline) if any would.
* **Nothing else in `Console/Core/` changes**: `git diff <R0> -- src/hacs/Console/Core/`
  shows the two sites only (their tests live outside `Core/`: `ConsoleErrorValidation`'s new arm,
  and `ConsoleC0Validation` if it gains a core-only case), and `check_console_includes.sh` stays
  OK. It is recorded as a named exception to C5's acceptance (b), beside C5a's two, not as a binding.

*(v3.8, as built; slot-10 WP-12, `3c96d63`.)* **Built exactly as specified, and recorded as an
exception** — the third named `Console/Core/` exception to C5's acceptance (b), beside C5a's two
(the `set`-statement position and the `--set` exit 5), and not a precedent for a fourth, which needs
its own owner authorisation. `git diff <R0> -- src/hacs/Console/Core/` shows the
two sites only: `Evaluator.cpp` (+19/−1, site 1) and `CoreVerbs.cpp` (+11/−1, site 2);
`check_console_includes.sh` OK (`ConsoleC0Validation` passes). Site 1 is in `eval_method`'s catch
order — a `ConsoleError` gains the member access's position via `set_pos_if_unknown(pos)` and is
re-thrown, `ExitSignal` / `QuitSignal` pass, any other `std::exception` goes through
`ThrowWrapped(registry, ex, "<Type>.<member> failed", pos, &obj)` with the object's creation site;
site 2 back-fills `ctx.pos` onto a `ConsoleError` from the type's `resume` hook. **Exit codes of every
shipped binding are unchanged**, as predicted: each gated getter (`LocalSystem`, `Cohomology`,
`HeckeOperator`, through `GuardedMember`) already produced its code. **One code moves outside the
shipped bindings, by site 1's own rule**: an *unwrapped* getter that raises
`hecke::NotImplementedInThisBuild` was exit 3 at the base (it escaped as a plain `std::exception`)
and is **exit 5** now, the kind classifier deciding as for a method; its text is now
`<Type>.<member> failed` with `caused by: …` (was the bare `what()`). WP-12 found no shipped
ungated getter that raises the refusal, and records that it did not audit every extension-layer
type's getters exhaustively. **No transcript moved** (step 1's prediction held: an `expect_error`
block records nothing in a `.expected`). The **negative control**: with the two Core sites reverted
and the bindings kept, `ConsoleErrorValidation` arm (W) fails 21 checks (every position row, and the
wrapped-getter and `expect_error` rows), and passes with them restored. Tests: arm (W)'s w01–w12
(a test-only raw-getter stub, `__member_stub`, registered on the validation's own registry only,
for `std::runtime_error` exit 3, `NotImplementedInThisBuild` exit 5, `std::logic_error` exit 3, an
unpositioned console error and the missing member; a positioned error keeps its position; the wrapped
error is catchable by `expect_error`; site 2 on the stub's resume hook; the positions on the shipped
`L.p` (5), `H.dims` (3), `T.cosets` (5) and on `Cohomology`'s real resume refusal at `(30, 5)`).

REPL: print and continue; a handle whose `compute()` threw stays bound in the `failed` state
(§2 C2), a verb-time error binds nothing. Script / `-c` / stdin: abort at the first error with
exit code 3 (§6). `assert(cond, msg)` failing is exit code 4 and prints `assertion failed: msg`.
For validation scripts that *test* error paths, the statement form `expect_error "substring"
{ … }` succeeds iff the block raises an error whose message contains the substring (and fails,
code 4, otherwise). Nothing catches `std::terminate`-class failures (a bare `assert` in a
`*Validation.cpp` under the `Check` build aborts, as it does today). Exception safety of the
pipeline's *global* state after a throw (program cache between compile and insert, device
residency, the non-atomic `PredicateStats`) is not established by the code; it is **measured**
by `ConsoleErrorValidation`'s post-throw integrity arm (§11).

### C8 — Architecture and the one-way dependency

```
ConsoleCore   (static library, SHIPPED 2026-09-16; STL only, nothing from ModArithmetic or the pipeline)
   ConsoleError (CONSOLE_CHECK) / Lexer / Parser / AST / Evaluator / Value (Int, Bool, String, List, Record)
   Object + TypeInfo (+ ResumableState) / Settings / Registry / Printer / Session / ScriptRunner / LineInput (dumb)
   + ConsoleCli   (C1a; the only Core/ file not yet written)
cohomology_app (bindings, compiled into the executable like BenchDriver.cpp)
   Console/Bindings/{CoreMath,Model,Cohomology,Hecke,Decomposition,Settings,Harness,RegisterPipelineVerbs}.cpp
   Console/ConsoleC0Validation.* (shipped), Console/ConsoleValidation.cpp, Console/scripts/*.oc + *.expected
Console/Platform/LineEditor.*   (optional phase C3 only; termios/unistd behind #ifndef _WIN32)
kernel.cu      one new `if` branch calling RegisterPipelineVerbs() and RunConsole(); nothing else
```

`ConsoleCore` is the analogue of `HeckeCore` (`Hecke/README.md:14-24`: a pure static library
that the executable links) and is unit-tested by **`ConsoleC0Validation`** without
constructing a single matrix. The pipeline never includes a `Console/` header; the guard is a
third grep script next to `check_matrix_includes.sh` (`docs/matrix-engine/tools/`):
`check_console_includes.sh` — *rule 1*, the reverse rule: inside `Console/Core/` every
`#include <…>` is a C++ standard header from a closed list and every `#include "…"` names a
`Console/Core/` file; *rule 2*: no TU outside `Console/` includes a console header, allow-listing
only `kernel.cu` (the C1a branch), `*Validation.*` and `ValidationRegistry.cpp`.

**`ConsoleArchitectureValidation` is retired as a name** (v3, WP-12 decision; `[S2]` §3 WP-12
scope item 5). The script is run by `ConsoleC0Validation` through `std::system`, probed rather
than required, exactly as `ConsumerMigrationValidation` runs `check_matrix_includes.sh` — and it
already is, on the shipped tree (261 files scanned). A separate registered name would buy one more
`--list` entry and nothing else, and the guard must run in *every* console phase anyway, which one
arm of the phase's own validation gives for free. C1a re-runs the same arm from
`ConsoleValidation.cpp` so the guard survives if C0's validation is ever narrowed.

**Why not a `Pipeline` library first?** Because the executable's source list
(`CMakeLists.txt:342-619`) mixes pipeline and validation TUs with commentary that records
*why* each one is there; re-homing ~40 sources into a library is a build refactor with its own
risk and no functional gain for the console. It remains available as a later clean-up (§16.4).

---

## 3. Language specification (normative for Phase C0)

### 3.1 Lexical

* Whitespace separates tokens; newline terminates a statement unless brackets are unbalanced or
  the line ends in `\`. `;` also terminates and, at the end of an expression statement,
  **suppresses printing**.
* Comments: `#` or `//` to end of line.
* Identifiers: `[A-Za-z_][A-Za-z0-9_]*`; case-sensitive. Reserved: `for in if else set help
  quit true false and or not expect_error include args def` (`def` reserved for Q2).
* Integers: decimal, `0x…` hex, `_` separators allowed (`134_217_757`). Type `Int` = `int64_t`;
  a literal outside `[−2^63, 2^63−1]` is a parse error. This covers every modulus the tree
  validates (the largest is `2^63−25`, `ModContextValidation`, CLAUDE.md) and every `uint64_t ell`
  the campaign accepts below `2^63`; `ell ∈ [2^63, 2^64)` is out of the console's reach (gap G7,
  documented, no user). Integers beyond `int64_t` that `[S Stage 6]` needs (Bernoulli numerators)
  are handled by a residue verb, not a bignum (§3.5, Q7).
* Strings: `"…"` with `\" \\ \n \t`. No interpolation; `str(x)` and `+` concatenate.

### 3.2 Grammar (EBNF)

```
program    := { statement }
statement  := assign | exprstmt | for | if | setstmt | include | help | expect | quit
assign     := IDENT "=" expr TERM
quit       := "quit" TERM
exprstmt   := expr TERM
for        := "for" IDENT "in" expr block
if         := "if" expr block [ "else" ( block | if ) ]
setstmt    := "set" IDENT "=" expr TERM
include    := "include" "(" STRING ")" TERM
help       := ( "help" [ IDENT | "?" ] | "?" IDENT ) TERM
expect     := "expect_error" STRING block
block      := "{" { statement } "}"
TERM       := NEWLINE | ";"
expr       := orexpr
orexpr     := andexpr { "or" andexpr }
andexpr    := notexpr { "and" notexpr }
notexpr    := "not" notexpr | cmp
cmp        := arith [ ("==" | "!=" | "<" | "<=" | ">" | ">=") arith ]
arith      := term { ("+" | "-") term }
term       := power { ("*" | "/" | "%") power }
power      := unary [ "^" power ]                         (right-assoc)
unary      := "-" unary | postfix
postfix    := primary { "(" args ")" | "." IDENT | "[" expr "]" }
primary    := INT | STRING | "true" | "false" | IDENT | "args" | "(" expr ")" | "[" [ expr { "," expr } ] "]"
args       := [ arg { "," arg } ]           arg := expr | IDENT "=" expr
```

`quit` is a **statement** (v3; `[WP5]` §2 deviation 3, adopted): §3.1 reserves the word, so it can
be neither an identifier nor a verb name, and a statement is the only place it can go. It is the
one production v2 named in §3.1 and §6 without giving it a grammar slot.

`/` on `Int` is exact integer division and errors on a non-zero remainder; on `Fp` it is field
division. `^` on `Int` is exact and overflow-checked; on `Fp`/`Poly`/`Matrix` it is repeated
squaring. **`power := unary [ "^" power ]` puts the unary minus inside the base**, so
`-2 ^ 2 == 4` and `0 - 2 ^ 2 == -4`. That is what the grammar above says, it is what C0
implements, and both forms are pinned by `ConsoleC0Validation` so the choice cannot drift
silently (v3; `[WP5]` §2 deviation 5, adopted). It is **not** the school convention and the
generated language reference must say so (§4.4). Comparison on objects is `equal` as mathematical objects (matrices entrywise;
polynomials by `CanonicalLess` equality, `FpPoly.h:115`). `include` is resolved relative to the
including file, cycle-checked, and runs in the same global frame.

### 3.3 Core value types (ConsoleCore, no pipeline)

| Type | Construction | Print form | Notes |
|---|---|---|---|
| `Int` | literal, arithmetic | decimal | `int64_t`, overflow → error |
| `Bool` | `true`/`false`, comparisons | `true` | |
| `String` | literal, `str(x)` | quoted **canonically**, bare under `print`/`str` (§2 C5) | the one place the two renderings differ |
| `List` | `[a, b]`, `range(a, b [, step])` | `[a, b]` | homogeneous not required; `len`, index, `for` |
| `Record` | returned by verbs (`settings()`, `certificates`, `timed`) | `{k: v, …}` | read-only key/value; members by `.k`; `json(record)` |

### 3.4 Arithmetic types (bindings; `Bindings/CoreMath.cpp`, needs `ModArithmetic` + `HeckeCore`)

| Type | Construction | Print form | Notes |
|---|---|---|---|
| `Fp` | `Fp(p, a)` or `GF(p)(a)` | `a mod p` | wraps `engine::ModCtx`-backed scalar ops (`ModCtx.h`), 32/64-bit by `p` |
| `Poly` | `poly(p, [c0, c1, …])` (low → high), `X(p)`, arithmetic | `X^2 + 3*X + 1 mod 7` (high → low) | wraps `FpPolyT<Elt>` (`FpPoly.h:48-105`); `coeffs(f)` low → high; `factor(f)` → `FactorPoly` (`FpPoly.h:176`), always certified (`:170`); `gcd`, `powmod`, `eval` |
| `Matrix` | `matrix(p, [[…]])`, `identity(p, n)`, `zero(p, r, c)` | bracketed rows | dual representation (§2 C2): `FlatMatrixT<Elt>` (`FlatMatrix.h:84-87` ctors, `:110-112` shape, `:124` entry) or `MatrixT<Elt>`; `rank`, `rref`, `kernel`, `image`, `inverse`, `transpose`, `charpoly` (`FpPoly.h:125`), `minpoly` (`:129`), `eval_at(f, A)` (`:133`) |

### 3.5 The linear-algebra surface `[S Stage 2–5]` needs (bindings; enumerated per `[I G4–G7]`)

These are the verbs the extension engine's authors will prototype against before its C++
exists, and the ones its scripts will keep using afterwards. All are `F_ℓ`-linear algebra on
`Matrix` — `[I §4.3]`'s recommendation ("do not introduce an `F_{ℓ^r}` `Elt`; implement the
extension-field needs inside the small algebra layer as `F_ℓ`-linear algebra") is adopted.

**The phase column** (v3.2) says what is bound **today** and what is still a plan; it is the
column a reader of this table most needs, because §3.5 was written before any of it existed.
`C1a` = slot-3 WP-7, `C1b` = slot-4 WP-5, both shipped; `C2` / `C5` are the phases of §10.

| Verb | Phase | Meaning | Underlying / new | Needed by |
|---|---|---|---|---|
| `solve(A, B)` | **C1a**, full column rank only; the under-determined case is C2 | exact `X` with `A·X = B`; typed error "not in span" | `engine::elim::solve_multi_rhs`; the pattern of `SolveColumnsExact` (`HeckeModuleDecomposition.cpp:68-94`, file-local — gap G14 makes it public) | `[S Stage 3.1, 4(b), 4(c)]`, `[I G5, G6]` |
| `hstack(list)`, `vstack(list)`, `submatrix(A, r0, r1, c0, c1)`, `columns(A, idx)` | **C1a** | block assembly | `FlatMatrixT` | everywhere |
| `vec(A)`, `unvec(v, rows, cols)` | **C1a** | `End(H_𝔪) ↔ F_ℓ^{d²}` | trivial | `[S Stage 3.1]` algebra closure |
| `column_space(A)` / `image`, `kernel`, `nullity(A)` | **C1a** | bases | `engine::elim` | `[S Stage 2.1, 3.2]` |
| `intersect(U, V)`, `sum_spaces(U, V)`, `contains(U, v)`, `in_span(list, A)` | **C1a** | subspace lattice | one `kernel` of a stacked system | `[S Stage 2.2, 4(c)]`, `[I G6]` Sturm membership |
| `restrict(A, basis)` | **C1a** | the matrix of `A` on an invariant subspace via the exact solve; typed error "not invariant" | `SolveColumnsExact(basis, A·basis)` pattern (`HeckeModuleDecomposition.cpp:632-633, 935-936`) | `[S Stage 3]`, `[I G5, G6]` |
| `algebra(ops [, max_dim])` | **C1a** | basis of `F_ℓ[ops] ⊂ End(V)` by span closure | new, on `vec` + `rref` | `[S Stage 3.1]`, `[I G5]` |
| `commutant(ops)` | **C1a** | `{X : X·A = A·X ∀ A}` as a subspace | one linear system over `vec` | `[S Stage 4(b)]`, `[I G6]` |
| `is_cyclic(ops, v)` / `cyclic_vector(ops, seed)` | **C1a** | `dim F_ℓ[ops]·v == d` | `random_vector` + `algebra` | `[S Stage 4(a)]`, `[I G6]` |
| `random_vector(p, n, seed)`, `random_matrix(p, r, c, seed)` | **C1a** | **seed mandatory**, SplitMix64 as in `FpPoly.cpp`/`HeckeModuleDecomposition.cpp` (`[I §5]`) | new (ConsoleCore-independent) | `[S Stage 4(a)]` |
| `mul`, `add`, `sub`, `scale`, `transpose`, `inverse`, `rref`, `rank`, `trace`, `identity`, `zero`, `entry`, `row`, `col` | **C1a** (v3.2: this row was implicit in "matrix arithmetic") | matrix arithmetic **through named verbs**, since `+` and `*` are `Int`-only in the C0 language (§3.2) | `FlatMatrixT` / `Hecke/SubspaceOps` | everywhere |
| `nilpotent_part(ops)`, `radical(alg)`, `tangent_space(alg)` (`𝔪/𝔪²`), `socle(alg)`, `nilpotency_index(alg)` | **C5, shipped** (v3.7-pre.1; slot-9 WP-13, `80eb184`). `alg` is a List of commuting operators, the Record of `algebra(ops)`, or a `HeckeAlgebra`; `nilpotent_part` has a Matrix and a List overload | local-algebra invariants of **any** commuting family over `F_ℓ`, **certificate-free, decided not searched**: `rad = ker Frob^e`, `Ann(rad)`, powers of the radical, `rad/rad²`; `nilpotent_part` is the Jordan–Chevalley nilpotent part, `s = t^(ℓ^N)` re-verified | `HeckeExt/HeckeAlgebraInvariants` (new, console-free; reuses `Hecke/SubspaceOps`' strict-locality primitives) | `[S Stage 3.2, 5.1]`, `[I G5, G7]`; `HeckeExtAlgebraInvariantsValidation` arms (A)–(C), script 047 |
| `loewy(alg, V)`, `socle_series(alg, V)` | **C5, shipped** (v3.7-pre.1; slot-9 WP-13) | `𝔪^i V` layer dimensions of an `A`-stable subspace; return `{dims, layers, f, layers_over_f, length}` | `HeckeExt/HeckeAlgebraInvariants` | `[S Stage 5.1]`, `[I G7]`; scripts 045, 047 |
| `is_local(alg)`, `algebra_invariants(alg)` | **C5, shipped** (v3.7-pre.1, new rows; slot-9 WP-13) | locality by **Berlekamp's count** of maximal ideals (so the Galois-conjugate trap `F_49 × F_49` is not called local, which a per-generator primary test would), and the invariants of the rows above as one Record (the member list is `help algebra_invariants`'s, generated into `console.md`) | `HeckeExt/HeckeAlgebraInvariants` | `HeckeExtAlgebraInvariantsValidation` arm (B) |
| `jordan_type(A)` | **C1a**, the **nilpotent** partition only; the general π-primary form is C2 | partition from nullities of `π(A)^r` | `PartitionFromNullities` pattern (`HeckeModuleDecomposition.cpp:180-204`, file-local — G14) | `[S Stage 5.2]` |
| `bernoulli_mod(w, ell)` | **shipped** (v3.3; slot-5 WP-10), registered by `HeckeExt/RegisterHeckeExtensionVerbs.cpp` as predicted — a binding, not a computation, the unit having existed since slot-4 WP-7. Outside `0 ≤ w < ell − 1` the unit's named `BernoulliOutOfRange` reaches the session as an ordinary runtime error (exit 3), which is what lets a script pin the refusal with `expect_error` | `B_w mod p` for even `w < p−1` by the `F_p` recursion `Σ C(w+1, j) B_j = 0` (all denominators prime to `p` by von Staudt–Clausen when `(p−1) ∤ j`), hence the test `p \| num(B_w/w)`; `[E]` `cl:harder` states the three branches outside that range | `HeckeExt/HeckePredictions` (`bernoulli_mod`, `kummer_divides`), `O(w²)` in `Fp` | `[S Stage 6.4]`, `[M §7.1]` — the reason Q7 needs no bignum |
| `glover_factors(n, ell)` | **shipped** (v3.3; slot-5 WP-10), same TU. Returns a **`Record`**: `n`, `ell`, `dimension`, `length`, `factors` (a list of `{sym, det_twist, multiplicity, dimension}`), `sl2_multiplicities`, `text`, `json`. **The `det`-twist is the standard module's** — `Sym^n` of the representation `ComputeSymmetricPowerMatrixFM` acts on, not of its dual, which would shift every `det_twist` by `−n`. A reader comparing against a dual-convention table reads every `j_i` wrong, which is why the row says so; `[E]` v1.6.0 `cl:glover` is the normative statement, and it gates phase E7 | the Glover / Ash–Stevens θ-recursion | `HeckeExt/GloverFactors`, pure integer combinatorics | `[E]` `cl:glover`, `[S Stage 6]` |
| `check_identities(H, ops)` | **C5, shipped as `check_identities(H [, primes [, items]])`** (v3.7-pre.1; slot-9 WP-13) | every item of `hecke_ext::HeckeIdentityCertificate` (items 1 … `k_max`, `k_max` read from the certificate, 7 at the base; items 6 and 7 assembled on request) as the Record `{items: [{item, name, status, detail}], k_max, code, passed, failed, not_applicable, unavailable}` | `HeckeExt/HeckeIdentityCertificate`, assembled by `HeckeExt/HeckeExtBindingSupport` (`AssembleIdentityCertificate`) | `[S Stage 1]`; script 046 (`identities.oc`, acceptance (c)); `HeckeExtAlgebraInvariantsValidation` arm (D) |
| `sturm_bound(k, ell [, cap])`, `u_ell_decision(n, ell [, budget_mb])` | **C1b**, registered by **`HeckeExt/RegisterHeckeExtensionVerbs.cpp`** and not by `Bindings/` | the real `SturmState` of `HeckeExt/HeckeSturmBound`; the frozen `UEllDecision` of `HeckeExt/HeckeUEllBudget` | `HeckeExt/` | `[E]` `def:bprime`; `[X]` §1.5 `u_ell` |

### 3.6 Pipeline object types (bindings)

| Type | Wraps | Members / methods (→ underlying API) |
|---|---|---|
| `Model` | `SimplicialComplex` + `SL2ZTessellationTables` + descriptor | `.name`, `.dims` (`SimplicialModelDescriptor::simplex_counts`, `HeckeModelDescriptor.h:49`), `.descriptor` (`SL2Z7VertexModel()`, `:69`; `FindModelDescriptor`, `:74`); built by `CreateSL2ZFundamentalDomainTriangulation()` (`LocalSystemSL2Z.h:12`) and `SL2ZTessellationTables(K)` (`SL2ZTessellationTables.h:78`) |
| `Complex` | `SimplicialComplex` | presets `sphere(n)`, `cylinder()`, `moebius()`, `projective_plane()` (`SimplicialCohomology.h:233-243`); `complex([[…]], name)` (`:63`); `.simplices(q)`; `cochain_complex(K)` → the trivial-coefficient `CochainComplex` (`:129`) |
| `LocalSystem` | `LocalSystemSimplicialComplexT<Elt>` | `symmetric_power(Model, n, ell)` (relations via `GenerateSL2ZRelationsWithGroupData`, `LocalSystemSL2Z.h:63-64`, or `GenerateSL2ZRelationsElt` for 64-bit, `:71-73`); presets `s1_scalar`, `s1_unipotent`, `cylinder_*`, `moebius_*` (`LocalSystemPresets.h:15-23`) — **C1b's, not C1a's** (v3.2), and they carry **no tessellation model**, so `hecke` and `family` refuse them *by name* with a typed error, and `LocalSystem.n` on a preset is `d_V − 1` with **no `Sym^n` meaning**; `.p`, `.d_V` (`LocalSystemSimplicialComplex.h:89-90`), `.relations` (`:86`); ctor 2/2b **copies `K`** (`:66-80`), so no `Model` edge is needed |
| `Cohomology` | `EquivariantCohomologyOnKT<Elt>` | `cohomology(L)` (`EquivariantCohomologyOnK.h:113`); `.dims` (`:173`), `.computed` (`:129`), `.Z(q)`, `.B(q)`, `.H(q)`, `.C(q)`, `.P(q)` (`:167-171`, block forms `:150-159`), `.A_C(q)`, `.A_Z(q)` — the last four throw under `retain_intermediates = false` (`:247-257`), which the handle's settings snapshot makes visible in `?H` |
| `HeckeOperator` | `HeckeCosetTablesT` + `HeckeTauTableT` + `HeckeOperatorOnKT<Elt>` | `hecke(H, p [, r=1])` (`HeckeCosetTables.h:116`, `HeckeTauTable.h:225`, `HeckeOperatorOnK.h:206-211`); `.A(q)` (`:231`), `.Theta(q)` (`:217`), `.Theta_eq(q)` (`:227`), `.certificates` (`:242-250`), `.apply(q, v)` (`:261`), `.apply_route2(q, v)` (`:258`), `.json` (`:267`), `.tau` (`HeckeTauTable.h:283`) |
| `Family` | `HeckeOperatorFamily` | `family(H)` (`HeckeOperatorFamily.h:111-112`); `.T(p)` (`:120`), `.T_pow(p, r)` (`:131`), `.T_pow_direct(p, r)` (`:173`), `.T_pow_primitive(p, r)` (`:186`), `.T_n(n)` (`:195`), `.T_pp(p)` (`:206`), `.theta(p, q)` (`:230`), `.prepare(list)` (`:247`); 32-bit only |
| `Decomposition` | `HeckeModuleDecomposition` | `decompose(ops, q)` (`HeckeModuleDecomposition.h:157, 166`; `q` **mandatory**, gap G12); `.blocks` → list of `Block` (`:168`), `.U` (`:171`), `.conjugated(p)` (`:175`), `.certify()` (`:180`), `.json` (`:183`); keeps its source `HeckeOperator`/`Family` handles and `q` (needed by `report`) |
| `Block` | `PrimaryBlock` | `.dim`, `.residue_degree`, `.certified`, `.witness`, `.basis`, `.min_poly(p)`, `.char_poly(p)`, `.jordan(p)` (`:129-150`); note `[I §2.3.4]`: a block is **not** proven local — `is_local(block)` is reserved for `[I G4]` |
| `Report` | `HeckeReportInput` + JSON | `report(D [, level_a=…, path=…])` (`HeckeReport.h:88-141`; `ell`, `n_sym`, `degree`, `level_b` come from the kept handles) → the JSON string or the file; streaming form for large levels (`:132`). **Schema `hecke_report/v2`** since slot 2 (`[WP2-2]`), which is what C1b freezes; `.schema`, and the four per-complex degree members below |
| ~~`CrossChecks`~~ | `HeckeCrossChecks` | **not a handle type** (v3.2, as shipped in C1b; `[WP4-5]` §7 item 1): `crosschecks(T)` returns a **`Record`** of the `run_all` / (i)(ii)(iii) codes (`HeckeCrossChecks.h:126-141`) — there is no object to keep alive, nothing is lazy, and a record prints and hashes with the C0 machinery. Expensive in `p` (`[I §2.6]`) |
| `Morphism` | `EquivariantCochainComplexMorphismOnK` | `cusp_restriction(H)` — today only inside `TestSL2Z_To_S1Cusp_RestrictionMorphism` (`LocalSystemSL2Z.h:117`; gap G8 = `[I G3]`) |
| `ValidationRun`, `BenchRun`, `CampaignSpec`, `CampaignResult` | §5 | *v3.5, as built (slot-7 WP-8)*: only **`CampaignSpec`** is a handle type (`campaign_spec` / `campaign_spec_text`). `run_validation` returns an **Int**. `bench`, `micro`, `run_campaign`, `golden_subset`, `timed` and `rss` return **Records**, and there are no `BenchRun` / `CampaignResult` / `ValidationRun` types |

Every type prints with `describe` (`?x`) listing exactly these members, so the language reference
in `docs/console/console.md` is generated from the registry (`help --markdown`; v3.6: shipped as
the binding verb `help_markdown()`, §4.4), not written by hand.

**The four degree members are per complex, never per record** (v3; `[C]` `sec:recordschema`
item 5, `[E]` §7's "The degree fields are per complex", slot-2 owner confirmation 1,
`[WP2-11]` item 4). Every type that *is* a complex — `Cohomology` today; `BoundaryCohomology`,
`ConeCohomology` and the pair complex when they land — carries **its own**

* `.q_max` — the top degree of *that* complex (bulk `2`, boundary `1` on the model);
* `.truncated` — `false` on a finite model;
* `.q_max_source ∈ {"derived", "set"}` — `"set"` only where `truncated` is true (E9);
* `.degrees` — `[0 .. q_max]`, derived.

A handle that holds several complexes (a `Report` over the extension record) exposes them *inside*
each complex's record, never as a maximum. **The campaign's `degrees` is a different field** — the
*reported* degree selection that `Job::id()` carries — and it keeps its meaning; the console must
not conflate the two, and `help` says which is which.

**Reserved names for the extension engine** (registered by its own TU, never by this plan; each
maps to an inventory gap): `GF(p, r)` / `GFElt` — an `F_ℓ[X]/(π)` algebra on `FpPolyT`
(`[I §4.3]` item 3; `π` = the `CanonicalLess`-least monic irreducible of degree `r`, so no Conway
tables), `MatrixQ`; `HeckeAlgebra`, `MaximalIdeal`, `is_local` (`[I G4, G5]`); `LoewyProfile`,
`ExtensionClass`, `active_directions` (`[I G7]`); `Atlas` (`[I G13]`); `boundary_cohomology(H)`,
`compact_support(H)`, `long_exact_sequence(H)` (`[M §3]`, `[I G10, G11]`); `iota(H)`,
`sign_split(x)` / `H_plus`, `H_minus` (`[S Stage 1]`, `[I G9]`); `divided_power(K, n, ell)`
(`[M §8]` identity 5, `[I G14]`); `L_map(H_lower, H)` (`[M §8]` identity 6, `[I G12]`);
`H1_shriek(H)`; `sl2z_model("gamma2")` (`[I G15]`); `hecke(H, p, method = "heilbronn")`
(`[I G16]`). The console's contribution is that each is a `TypeInfo` + a set of overloads; the
language does not change.

**Reserved additionally by `[X]` v1.5.1** (v3; `[WP6]` §5 item 5): types
`ContragredientLocalSystem`, `Pairing`, `Presentation`, `Settings` (the `MathSettings` snapshot as
a value, `.fingerprint`), `HeckeAlgebra` / `MaximalIdeal` as above, and the complex types
`BoundaryCohomology`, `ConeCohomology`, `PairComplex` with the four degree members; verbs
`dual(L)`, `pairing(X, Y)`, `presentation(m, group)`, `reduce(H, k)`, `bockstein(H)`, and the
three R3 verbs `state(x)` / `resume(x, budget)` / `save_state(x)` of §2 C5. `coefficient_ring` becomes a
member of `Cohomology` and of every Hecke object when E8 lands. The campaign's new spec keys of
`[X]` §1.5 pass through `campaign_spec_text` untouched and need no console change.

**The extension layer's namespace is `hecke_ext`** (v3; `[WP2-11]` item 6), so its registration TU
is `HeckeExt/RegisterHeckeExtensionVerbs.cpp` declaring `void hecke_ext::RegisterHeckeExtensionVerbs()`.
`Console/Core/` still names none of it.

**The C5 types as shipped** (v3.7-pre.1; slot-9 WP-12 and WP-13; the member lists are
`docs/console/console.md`'s, generated from the registry, and are not copied here).
* **E7, C5a** (`Console/Bindings/Duality.cpp`, WP-12): `dual(L)` → **`ContragredientLocalSystem`**
  (`hecke::ContragredientCell`: `n`, `p`, `d_V`, `coefficient_ring`, `phi_is_isomorphism`, `dims`,
  `dims_M`, `Phi`, `induced_Phi(q)`, `A(p, q)`, `A_M(p, q)`, `intertwines(p)`); `pairing(L, D)` →
  **`Pairing`** (`hecke::PoincareDualityPairing`: `perfect(t)`, `gram(t)`, `boundary_perfect(s)`,
  `boundary_gram(s)`, `certificate`, `pd_gate(primes)`, the gate built exactly as `RunE7Cell32`
  builds it — `[C]` `cl:pd` stays open, the gate tests it). Every E7 golden object at
  `(10, 691)` is reachable with a byte-identical hash (script 023). Both verbs refuse a ring
  (exit 5).
* **E8, C5a** (WP-12): `coefficient_ring` is a member of `Cohomology` and of every
  `HeckeOperator` (`F_ell` on a field handle). Under `Z/ell^<k>`, `ell ≥ 5`, a ring `Cohomology`
  honours exactly `[E]` `sec:ring` (h)'s members (`.coefficient_ring`, `.computed`, the four degree
  members, `.lengths`, `.invariant_factors(q)`, `.ladic_type_certified`, `.r_K(q)` for
  `q ∈ {0, 1}`, `.ladic_type(q)` as the Record `{free_rank, torsion}`, `.bockstein_rank`,
  `.higher_torsion_count`, `.red(q)` as a Matrix over `F_ell`, and `state` / `save_state`), and a
  ring `HeckeOperator` (`hecke(H, p)`, `r = 1`, `p = ell` included) honours `.coefficient_ring`,
  **`.A(q)` as a List of Int rows** — not a `Matrix`, because row `i` lives modulo `ell^{e_i}` and the
  `Matrix` type's field algorithms would be meaningless on it — and `.charpoly_free` as the Record
  `{precision, coeffs}`. The field members (`dims`, `C`, `Z`, `B`, `H`, `P`, …) raise the object's
  named `std::logic_error` (exit 3); **every other member exits 5**, through one mechanism
  (`bind::GateTypeOnRing`), so a member added later refuses until `[E]` (h) lists it. That includes
  the structural members `LocalSystem.n` / `.p` / `.d_V` / `.relations`, `HeckeOperator.p` / `.r`
  and `Cohomology.ell` / `.d_V` / `.dim_C` on a ring handle; listing them is an owner item for a
  later amendment of (h) (`[WP9-12]` §4 item 2). **A handle of one ring used under another is
  exit 5**, naming both rings — the pipeline's own classification (`HeckeOperatorOnK`), which (h)
  did not state (`[WP9-12]` §4 item 4).
  *(v3.8-pre.1, ruled; slot-10 decision 6 (ii) (A), built by slot-10 WP-12; the list is `[E]`
  v1.11.0-pre.1 `sec:ring` (h)'s, which owns it.)* On a ring handle at `ell ≥ 5` **five structural
  members honour**: `LocalSystem.n` (`n`), `LocalSystem.d_V` (`n + 1`, the rank of the free module
  `Sym^n(R^2)`), **`LocalSystem.coefficient_ring`** — a **new member** of the type, on every handle
  (`"Z/ell^<k>"` on a ring handle, `"F_ell"` on a field handle, as `Cohomology`'s and
  `HeckeOperator`'s), the one member slot 10 adds, so `console.md` is regenerated by the lead after
  WP-12's merge — and `HeckeOperator.p`, `HeckeOperator.r` (always `1` on a ring handle). Each is a
  read of the handle's stored data and forces no computation. **Every other unlisted member keeps
  exit 5** — `LocalSystem.p` (it would read `ell` under `Z/ell^k`) and `.relations`,
  `Cohomology.ell` / `.d_V` / `.dim_C`, and `HeckeOperator`'s other members. The ring-mismatch
  rule above is **binding** from this pre-release (`[E]` (h)): a verb refuses a handle of another
  ring at dispatch, exit 5, naming both rings; a member read follows the handle's own ring.
  *(v3.8, as built; slot-10 WP-12, `Cohomology.cpp`, `Hecke.cpp`; `[E]` v1.11.0-pre.2 (h).)* The
  five members honour as listed, each a read of the payload: `state(...).state == "declared"` after
  the reads on a lazy handle (pinned). `LocalSystem.coefficient_ring` is `hecke::CoefficientRingText(ring_k)`,
  `"F_ell"` on a field or preset handle. `ConsoleErrorValidation` arm (K): `L.n`, `L.d_V`, `T.p`,
  `T.r` changed from exit 5 to 0, each with its value; `L.coefficient_ring` new; the other member
  rows' codes unchanged. **The mismatch rule needed no code**: it already held at every
  handle-taking verb at the base (`cohomology`, `hecke` name both rings; `family`, `decompose`,
  `crosschecks`, `dual`, `pairing` and the C5b verbs refuse a ring handle outright); it is now
  pinned both ways (arm (W) w16–w19: `Z/ell^3` in force against a `Z/ell^2` handle, `F_ell` against
  a ring handle, a ring against an `F_ell` handle), and a member read following the handle's own
  ring is pinned both ways (w14–w15). `docs/console/console.md` regenerated
  (`gen_console_md.sh <binary>`): one added row, `LocalSystem.coefficient_ring`.
* **C5b** (`HeckeExt/RegisterHeckeExtensionVerbs.cpp`, WP-13; thirteen types, thirty overloads
  under twenty-nine verb names): **`GF`** (`GF(ell, r)`, and `canonical_field(ell, r)`, `[X]` §7's
  name; `field_polynomial = conway` → exit 5) and **`GFElt`**, whose arithmetic is the named verbs
  **`gf_add`, `gf_sub`, `gf_mul`, `gf_inv`, `gf_pow`, `gf_frobenius`, `gf_eval`** — recorded as the
  binding spelling, because C1a's `add` / `mul` take `any`, so a typed overload registered after
  them could never be reached (first match in registration order, §2 C3); **`HeckeAlgebra`**
  (`local_algebra(m)`, `MaximalIdeal.algebra`), **`MaximalIdeal`** (the children of an
  `ExtRecord`), **`LoewyProfile`** (`module_structure(m [, group])`), **`ExtensionClass`** (one
  consecutive Loewy-layer pair), **`Atlas`** (`atlas(ell)`, `ell ∈ {5, 7, 11, 13}` in process;
  `atlas(691)` is a typed `atlas_unavailable` refusal — the out-of-suite `Σ(691)` store is not
  bound), **`Presentation`** (`presentation(m)`), **`Settings`** (verb **`settings_snapshot()`** —
  recorded as the binding spelling, because C1a's `math_settings()` already returns a Record and
  keeps it; `ExtRecord.settings`), **`Involution`** (`iota(H)`: `.sign_split(q)`,
  `.eisenstein_line(q)`, `.plus(q)`, `.minus(q)` — the reserved `sign_split(x)` / `H_plus` /
  `H_minus` as members), **`BoundaryCohomology`** (`boundary(H)` — the reserved
  `boundary_cohomology(H)`), **`ConeCohomology`** (`cone(H)` — the reserved `compact_support(H)`;
  `.h(p, q)` and `.pair_homotopy(p)` per prime, since the engine's `h` is derived from `η` per
  prime), **`ExtRecord`** (`ext_record(n, ell, cone, sign_split, presentation, sturm, commutant)`,
  lazy); the verbs `is_local`, `L_map(H_lower, H)` (a Record `{n, m, ell, L, certificate, induced,
  ranks}`), `check_identities` and the §3.5 local-algebra verbs. The two complex types carry the
  four degree members and `.coefficient_ring` (`"F_ell"`). Every C5b verb that runs the pipeline
  refuses a non-default `coefficient_ring` at dispatch and again in its lazy compute, and every one
  handed a `Cohomology` handle calls `bind::RequireFieldHandle` at dispatch (`f28a0fa`): exit 5.
* **Not bound** (recorded, `[WP9-13]` §1): `MatrixQ` (no rational matrix type exists);
  `PairComplex` (the record's pair *is* `Cone(r)`, bound as `ConeCohomology`, and the name is not
  registered); `divided_power(K, n, ell)` (the engine object is E7's `ContragredientCell`, bound
  once, as C5a's `ContragredientLocalSystem`); `long_exact_sequence(H)`, `H1_shriek(H)` and
  `active_directions` as verbs (their content is on `ConeCohomology`, `BoundaryCohomology` and
  `ExtensionClass`); `sl2z_model("gamma2")` (G15) and `hecke(H, p, method = "heilbronn")` (G16),
  not landed; `[X]` §7's `GenerationCertificate` type (its outcome is on
  `MaximalIdeal.certificate` / `.certificate_routes`); `resume` on an `ExtRecord` (the cell's
  `u_ell` state is read-only, `.u_ell.resumable`); the reserved `reduce(H, k)` and `bockstein(H)`
  (unbound: the ring `Cohomology` carries `.red(q)` and the Bockstein pair as members).

**θ and the Dickson long exact sequence** — *v3.9-pre.1 (specified; slot-11 WP-16, a/s under the
owner's decision 5 (A); the objects are `[E]` v1.12.0-pre.1 `sec:thetaobj`, the mathematics is
`[C]`'s section on the Dickson invariant and θ).* Registered by `HeckeExt/RegisterHeckeExtensionVerbs.cpp`
(the one `Console/`-including TU of the extension layer), on top of slot-11 WP-5 / WP-6's
`HeckeExt/HeckeDicksonTheta`; nothing in `Console/Core/` moves. Names and indexing are `[E]`'s:
θ is **source-indexed**, `θ_n : H^q(M_n ⊗ det) → H^q(M_{n+ℓ+1})`, the same map as C5b's
`L_map(H_lower, H)` (target-indexed, `m = n − ℓ − 1`).

| Type / verb | Wraps | Members / result |
|---|---|---|
| `dickson_les(n, ell)` → **`DicksonLES`** (lazy handle; `declared → computed \| failed`, settings snapshot at creation, as every C5b handle) | `hecke_ext::` the WP-5 / WP-6 driver of `HeckeDicksonTheta` for one `(n, ell)`: the three pipelines at `n`, `n + ell + 1` and `Q_n`, the five maps, the certificates | `.n`, `.ell`, `.n_up` (`= n + ell + 1`); `.dims` → Record `{H0_n, H0_up, H0_Q, H1_n, H1_up, H1_Q}`; `.ranks` → Record `{theta0, pi0, delta, theta1, pi1}`; `.maps` → Record of the five `Matrix` values in the stored bases (`[E]` `sec:thetaobj` (c)); `.exact` (Bool: exactness certified at all six spots as subspaces); `.ker_theta`, `.im_delta` (`Matrix`: bases in `H1_n`'s stored coordinates) and `.ker_equals_im` (Bool); `.dickson_count` (Int: `#{(a, b) : a(ell + 1) + b(ell² − ell) = n}`); `.certificate` (Int, `0` = every certificate of `[E]` (6a)–(6d) passed); `.coefficient_ring` (`"F_ell"`) |
| `theta(H, H_up)` → Record | `DicksonInducedMaps` + the WP-6 checks, on two `Cohomology` handles of one `ell` with `H_up.n = H.n + ell + 1` | `{n, n_up, ell, induced, ranks, ker, image, twist_check, u_ell_zero}`: `induced` the List of per-degree `Matrix` values in the stored bases, in `DicksonInducedMaps`'s degree order (equal, matrix for matrix, to `L_map(H, H_up).induced`; the degree-2 term is `0` at `ell ≥ 5`); `ker`, `image` bases of `ker θ^1` and `im θ^1`; `twist_check` the number of `p ∈ {2, 3, 5, 7} \ {ell}` failing `A(T_p)_{n+ℓ+1} θ = p θ A(T_p)_n` (`0` expected); `u_ell_zero` (Bool, `A(U_ell) θ = 0` over `F_ell`) |

**Errors** (§8): a non-default `coefficient_ring` in force → exit 5 at dispatch **and** in the lazy
compute; a ring `Cohomology` handle → exit 5 (`bind::RequireFieldHandle`), as for every C5b verb;
`H_up.n ≠ H.n + ell + 1` or two different `ell` → `TypeError`, exit 3, with the message pattern of
`L_map` (the three numbers named); `ell < 5` → the `ENGINE_CHECK_MSG` of `[E]` `sec:thetaobj` (h)
naming `lem:h2torsion`, exit 3 — a mathematical precondition, not a build capability; odd `n` is
not refused (every term is `0`, `-I`). **Not bound** (recorded): a census verb — the catalogue
`hecke_census/v1` (`[E]` `sec:census`) is a derived artefact read by `congruence_census.py`, not a
pipeline object; θ over `Z/ell^m` (slot 12). **Name note**: the verb `theta(H, H_up)` and the member
`Family.theta(p, q)` (the cochain operator `Θ`, C1a) live in different namespaces (verb vs member) and
do not collide in the registry; `help` lists both, and the verb's help line says "Dickson θ = L_*".
*(v3.9: **not built.** Slot-11 WP-16 was not run — the owner's re-ruling of decision 3 put arbitrary
`k` into slot 11, and WP-16 was the named give-way, `[S11]` §10. Neither `dickson_les` nor `theta` is
registered; this row stays the binding specification for a later slot. The objects exist in the engine
(`hecke_ext::DicksonThetaCell`, `[E]` v1.12.0 `sec:thetaobj`).)*
*(v3.9.2, **as built** — slot-12 WP-8: both verbs and the type are registered in
`HeckeExt/RegisterHeckeExtensionVerbs.cpp`, members and result keys exactly as the rows above. Recorded
choices: (1) `.n`, `.ell`, `.n_up`, `.dickson_count` and `.coefficient_ring` are structural reads
that do not force the compute (so `dickson_les(10, 3).n` is `10`; `.dims` then fails with the
`ell < 5` check); every other member forces it. (2) `.maps.delta` and `.ranks.delta` are the degree-0
connecting map `δ^0 : H^0(Q_n) → H^1(M_n)` (the only one of the five-map sequence; `δ^1` lands in
`H^2 = 0`); `.im_delta` is its image. (3) `theta`'s `twist_check` and `u_ell_zero` test every degree in
which θ is a non-empty map, with the operators of `HeckeOperatorFamily` on the two handles (`U_ell` =
`T_p` at `p = ell`); the `ell < 5` refusal of `theta` is an `ENGINE_CHECK_MSG` in the verb with
`DicksonThetaCell`'s wording (naming `theta(H, H_up)`), raised before any Hecke work. (4) A
`DicksonLES` computes under its creation-time snapshot (§2 C2): created under `F_ell` it computes even
if the ring in force has changed since; created under a ring it is refused at dispatch, so the lazy
compute's own refusal is defence in depth and unreachable from a script.)*

**The `ell`-adic L-function of a modular symbol** — *v3.11.1, as built (slot-20 stretch S1; `HeckeExt/LValue/LFunctionRecord.{h,cpp}`, the binding in `HeckeExt/RegisterHeckeExtensionVerbs.cpp`; `[E]` 1.20.0-pre.5 `sec:lvlfunction`).*

| Verb | Wraps | Result |
|---|---|---|
| `lfunction(n, ell, a, M = 2, R = 4, sign = "minus", sep = nil)` → Record (eager; `read_only`) | `lvalue::ComputeLFunction`: `birch::RunSymbolCell(n, ell, R, sep, control = true)` (the root of `charpoly(sep \| W^-)` congruent to the Eisenstein value if it occurs, else the first root mod `ell`; simple mod `ell` or refused), `UnitRoot`, `BuildMeasure` to level `M` — the measure `BirchModularSymbolRoute::measure()` returns on the class with this symbol (`[E]` `chk:lvmeas` (M0)); `sep` a List of `[p, c]` pairs (`p ≤ 97` prime), `nil` = `T_2 + 3T_3 + 7T_5` | `{schema, n, k, ell, R, M, G, u, sign, geometric, form, normalisation, a, vanishes, mu, lambda, readable, lambda_mod_ell, coefficients, precision, values_modulus, critical_values, hash, line}`: `schema` `"lfunction/v1"`; `form` `{separator, target_root, eisenstein_congruent, a_p, a_ell, alpha, symbol}`; `coefficients` the `G = ell^{M-1}` coefficients `c_t mod ell^R` of `L_a(T)` in `Z/ell^R[T]/(omega_{M-1}(T))`; `precision` `lem:lvlfunprec`'s `prec(t)`; `critical_values` `L_a(u^j - 1) mod ell^{min(M,R)}`, `0 ≤ j ≤ n`; `hash` the FNV-1a-64 of the record's canonical JSON (`rmk:lvlfunschema`); `line` one `LFUNCTION` line |
| `pow(A, e)` → Matrix (`read_only`) | matrix power, `A` square, `e ≥ 0` (`A^0 = I`) | the `Matrix` `A^e` (slot 21) |
| `kummer_unit(ell, i)` → Record (`read_only`) | the cyclotomic unit `η_i` of layer 1 (`[E]` `sec:lvnf`) and its Kummer `ell`-th-power test; `ell` prime, `5 ≤ ell ≤ 65521`, `i` even, `2 ≤ i ≤ ell − 3` | `{schema, ell, i, exponents, coefficients, max_digits, v_pi, unramified, lambda_split, not_lth_power, eigen_ok, unit_ok, ell_divides_Bi, oracle_agrees, split_primes}` (slot 21) |
| `hida_tower(n, ell, m)` → Record (`read_only`) | the Hida weight-tower cell at class `n` (`[C]` `def:hidatower`); `ell ≥ 5` prime, `n` even `≤ 200`, `m ≤ 3`; both readings of the ordinary part at levels `e = 1 … m` | `{schema, n, ell, m, e_max, K, h, exps, levels: [{e, ord_rank, image_free, charpoly, free_ord_rank, free_charpoly, readings_agree}], lines}` (slot 21) |
| `level_n(N, n, ell, primes = nil)` → Record (`read_only`) | `H^1(Γ_0(N); Sym^n F_ell)` by Shapiro's lemma (`[C]` `sec:levelN`) and the Heilbronn operators `T_p` (`p ∤ N`) / `U_p` (`p \| N`); `primes` at most 6 primes `≤ 97`, none `= ell` (nil = 2, 3, 5 without `ell`); `ell ≥ 5`, `n` even, `N ≤ 100`, `index(N)(n+1) ≤ 1000` | `{schema, N, n, ell, index, D, dim_S, dim_ST, h0, h1, cusps, dim_cusp_forms, ops: [{label, p, bad, charpoly}]}` (slot 22) |
| `nebentypus(N, m, n, ell, primes = nil)` → Record (`read_only`) | `H^1(Γ_0(N); Sym^n F_ell ⊗ χ)`, `χ` the Dirichlet character of Conrey label `N.m` reduced into `F_ell` (`[C]` `sec:nebentypus`), and the Heilbronn operators; `ell ∤ N`, `order(χ) \| ell − 1`, `n ≥ 0`, `N ≤ 100`, `index(N)(n+1) ≤ 1000`; `primes` at most 4 primes `≤ 13` | `{schema, label, N, m, order, parity_ok, n, ell, D, h0, h1, ops}` (`h0 = h1 = 0`, no `ops` when `χ(−1) ≠ (−1)^n`) (slot 22) |
| `forms_algebra(k, ell, primes = nil, terms = 8)` → Record (`read_only`) | the forms side mod `ell`: `S_k` over `F_ell` with its Miller `q`-expansion basis and `T_p` on it (`[E]` `sec:forms`); `ell ≥ 5`, `k` even, `12 ≤ k ≤ 400`, `terms ≤ 64` | `{schema, k, ell, d, k_prime, precision, basis, ops: [{p, charpoly}]}` (slot 22) |
| `hida_lambda(ell, k, W, primes = nil)` → Record (`read_only`) | the forms side of the Λ-adic Hecke algebra at one weight (`[U]` `sec:u-lambda`): `e M_k`, `e S_k` over `Z/ell^W`, characteristic polynomials of `T_p` and `U = T_ell`; `ell ≥ 5` prime `≤ 101`, `k` even, `4 ≤ k ≤ 200`, `k − 1 ≥ W`, `W ≤ 6`, `ell^W < 2^62` | `{schema, ell, k, W, dim_M, dim_S, rank_M, rank_S, comm_ok, stable_ok, eisenstein, ops: [{name, charpoly}]}` (slot 22) |
| `descent(N, n, primes = nil)` → DescentRecord (lazy; `read_only`) | the integral descent record `integral_descent_record/v1` of `H^q(Γ_0(N); Sym^n Z^2)` over `Z` (`[C]` `thm:descentcert`, `sec:descentpair`, `sec:recordschema` item 7; slot 24 D6); **only under `coefficient_ring = Z`** (otherwise a runtime error asking for it); `primes` 1 to 6 primes `≤ 97` not dividing `N`, sum `≤ 100` (nil = the first three of 2, 3, 5, 7, 11, 13 not dividing `N`); `N ≤ 300`, `n ≤ 60`, `index(N)(n+1) ≤ 300`; a limit or `p \| N` is a type error (exit 3) | the type `DescentRecord`: structural `N`, `n`, `primes`, `coefficient_ring` (`Z`), `object` (`group`), `q_max` (3), `truncated` (true), `q_max_source` (`derived`), `degrees` ([0, 1, 2, 3]); computed `groups` (H^0 … H^3 as strings, `"Z^r + Z/l^a + …"`, `"0"`), `bad_primes` ([ell, count]), `torsion_primes`, `K` ([{ell, route, K, W, certified}], provenance, not hashed), `charpoly` ([{p, r, coefficients high → low as strings, `"[sign,D digits]"` beyond 2^63, `"?"` undetermined; determined, digest, refused}]), `torsion` ([{q, ell, exponents, module_certified, ops: [{p, invariants}], refused}], the invariants `a=..;P=..;B=..;ker=..;cok=..;fit=..` of `[C]` `prop:torsionhecke`(1)), `pair` ({bulk, boundary, compact}, q = 0 … 4), `groups_inv` / `pair_inv` (the same groups as `{free_rank, torsion: [[p, k, mult], …]}`, 3.14.0-pre.1), `status` (`ok` \| `refused`), `refusal`, `digest` (`record_fnv1a64`), `json` (slot 24; script `054_s24_descent.oc`; `[CLI]` 1.5.0 ch. *Integral cohomology*); the method `module(ell, K)` → Record, H^1 ⊗ Z/ell^K with the T_p matrices (3.14.0-pre.6, slot-25 EXPORT; script `058_s25_descent_module.oc`); the method `module_Z(mode)` → Record, H^1 over Z as [[τ, M], [0, F]]: `module_Z()` with F exact over Z in the certified basis iso_dixon/v3 and M in that basis (3.14.0-pre.9, slot-25 EXZ2-P3; script `061_s25_module_z_exact.oc`), `module_Z("local")` with F `pending(step 2)` (3.14.0-pre.7, slot-25 EXPORT-Z step 1; script `059_s25_descent_module_z.oc`) |
| `hecke_structure(N, n, algebra = "full")` → Record (`read_only`) | the record `integral_hecke_structure/v1` of the cell (N, n, algebra) (`[C]` `sec:recordschema` item 8, `sec:heckeZ`; slot-25 HZ-REC); **only under `coefficient_ring = Z`** (otherwise a runtime error asking for it); `algebra` `"full"` \| `"anemic"` (`"anemic"` only at N > 1); `N ≤ 300`, `n` even `≤ 60`, `index(N)(n+1) ≤ 300`; a limit is a type error (exit 3) | `schema`, `id`, `N`, `n`, `algebra`, `status` (`final` \| `pending` \| `refused`), `golden_eligible`, `record_fnv1a64`, `cert_sha256`, `settings_fingerprint`, `descent_record_fnv1a64`, `signature`, `generation` (["ell:status(route)"]), `C_T`, `body` (the hashed fields, "path=value") (3.14.0-pre.8; script `060_s25_hecke_structure.oc`) |

**Errors** (§8, no new row): `ell < 5` or not prime, `n` odd or `< 2`, `M < 2`, `R < 1`, `ell^R ≥ 2^62`, `ell^M > 4·10^6` (the read-only budget: `≤ ≈ 2 s`, `≤ 0.2 GB`), `a ∉ [0, ell − 1)`, `sign` not `"minus"`/`"plus"`, a non-simple root, no unit `r^+_0`, `a_ell ≡ 0 mod ell` → `RuntimeError`, exit 3 (the verb's `Guard`); a malformed `sep` → `TypeError`, exit 3. The verb reads no setting (the measure is over `Z/ell^R` whatever `coefficient_ring` is in force) and writes nothing.

**Digit handles** — *v3.9, as built (slot-11 WP-18c, `Console/Bindings/{Bindings,Cohomology,Hecke}.cpp`,
`Payloads.h`; `[E]` v1.12.0 `sec:ring` (h), which owns the list).* Under `coefficient_ring = Z/ell^<k>`
with `ell^k ≥ 2^64` and `ell ≥ 5`, `symmetric_power(M, n, ell)`, `cohomology(L)` and `hecke(H, p)`
(`r = 1`, `p = ell` included) return **digit handles** over `Hecke/LadicCell` (`[E]`'s digit route).
`symmetric_power` checks the per-cell rule at dispatch (`ell ∈ {2, 3}`, `ell ≥ 2^31`, `n` odd or `0`,
the 8192-bit and 40 GB caps — the caps at the largest reachable working precision `k + K_w − 1`),
exit 5 naming the cell. On a digit `Cohomology` handle **honour**: `.computed`, `.q_max`, `.truncated`,
`.q_max_source`, `.degrees`, `.coefficient_ring`, `.lengths`, `.invariant_factors(q)`,
`.ladic_type_certified`, `.r_K(q)`, `.ladic_type(q)` and the new **`.precision`** — the Record
`{precision_requested, precision_working, e_max, word_level, precision_certified, digit_width,
digits_L}`, honoured on digit handles only (on every other handle exit 5). **The field members
`dims`, `C`, `Z`, `B`, `H`, `P` exit 3** with the field accessor's own `std::logic_error` text, as on a
native ring handle (repaired after the slot's review, pass 2, M-1 — WP-18c's first commit had them at
exit 5); **every other member exits 5** (`bind::GateTypeOnDigit`, one mechanism, as
`GateTypeOnRing` for native ring handles). On a digit `HeckeOperator` handle `.coefficient_ring`,
`.p`, `.r` and **`.charpoly_free`** honour — the Record `{precision, coeffs}`, each coefficient a
**String** in `[E]` (g)'s residue form (signed decimal when it fits `int64`, else
`"ell-adic:[a_0,a_1,…]"`), because the console's `Int` is `int64` (Q7); `.A` and every other member
exit 5. `hecke(H, p)` on a digit handle **recomputes the whole cell** once per operator, independently
of `H`'s own run — deterministic, so no value moves; a cost only (review pass 2, m-2). The width is
`ENGINE_LADIC_WIDTH`, an engine-family variable, not a console setting. `console.md` gained the one row
`Cohomology.precision` (`db1b454`).

**Wide handles** — *v3.9.3, as built (slot-12 WP-17, `Console/Bindings/{Bindings,Cohomology,Hecke}.cpp`,
`Payloads.h`; Q9 decided (a) by the owner, 2026-09-26).* Under `coefficient_ring = Z/ell^<k>` with
`2^32 ≤ ell^k < 2^64` and `ell ≥ 5` (`bind::IsWideCell`, decided at `symmetric_power`'s dispatch from
`(ell, k)`, forcing nothing), `symmetric_power(M, n, ell)`, `cohomology(L)` and `hecke(H, p)` (`r = 1`,
`p = ell` included) return **wide handles**: the local system, the cohomology, its two comparison objects
(`F_ell` and `Z/ell^2`, each under its own ring for its construction only) and the operator are the
**`uint64_t` instantiations** (`LocalSystemSimplicialComplex64`, `EquivariantCohomologyOnK64`,
`HeckeCosetTables64` / `HeckeTauTable64` / `HeckeOperatorOnK64`) built by the **campaign job loop's own
recipe** (`RunRingPipeline<uint64_t>`), so every value is the campaign's (`ConsoleErrorValidation` (Q9)
compares 13 hashed objects and the free charpoly on seven band cells). The per-cell route is now exactly
the campaign's: `ell^k < 2^32` the native `uint32_t` route (unchanged, bit for bit), the wide band the
native `uint64_t` route, `ell^k ≥ 2^64` the digit route. On a wide `Cohomology` handle **honour** exactly
the members of a `uint32_t` ring handle (`[E]` (h)'s list: `.computed`, `.q_max`, `.truncated`,
`.q_max_source`, `.degrees`, `.coefficient_ring`, `.lengths`, `.invariant_factors(q)`,
`.ladic_type_certified`, `.r_K(q)`, `.ladic_type(q)`, `.bockstein_rank`, `.higher_torsion_count`,
`.red(q)`, and the `ladic_level` state); **the field members `dims`, `C`, `Z`, `B`, `H`, `P` exit 3**
with the `uint64_t` object's own field-accessor `std::logic_error`; every other member (`.ell`, `.d_V`,
`.dim_C`, `.precision` — the last stays digit-only) exits 5 by `GateTypeOnRing`, unchanged. On a wide
`LocalSystem` `.n`, `.d_V`, `.coefficient_ring` honour; on a wide `HeckeOperator` `.coefficient_ring`,
`.p`, `.r`, **`.A(q)`** (a List of rows) and **`.charpoly_free`** honour, the rest exit 5. **An entry
that does not fit `int64`** (possible only when `ell^k > 2^63`, e.g. `Z/19^15`) is its **decimal
String**; every other entry is an `Int`, so a wide handle below `2^63` prints like a `uint32_t` ring
handle. The mechanism is `bind::GateTypeOnWide`, applied after `GateTypeOnDigit`: the digit gate's
wrapper with every member not given a `uint64_t` getter passed through to the ring gate, so the refusal
set is exactly `GateTypeOnRing`'s. Every verb that refuses a ring handle (`family`, `decompose`,
`crosschecks`, `dual`, the C5b verbs, …) refuses a wide handle by the same `RequireFieldHandle`
(`ring_k ≥ 2`), exit 5. `console.md` is unchanged (no verb, type, member or setting was registered).

---

## 4. Object model — lifetimes, laziness, printing, introspection

### 4.1 Ownership graph (every edge is a verified borrow)

```
Model ──> LocalSystem (copies K: LocalSystemSimplicialComplex.h:66-80) ──> Cohomology (borrows lssc: EquivariantCohomologyOnK.h:126)
Cohomology + Model ──> HeckeOperator      (owns cosets + tau; tau borrows K_, model_, cosets_: HeckeTauTable.h:298-300;
                                           op borrows coh_, cosets_, tau_: HeckeOperatorOnK.h:280-282)
Cohomology + Model ──> Family             (borrows cohomL_, K_, model_: HeckeOperatorFamily.h:250-252; owns its pipelines in a
                                           std::map with stable addresses: :263-270)
HeckeOperator ──> CrossChecks             (borrows coh_L_, cosets_, tau_: HeckeCrossChecks.h:167-169)
HeckeOperator | Family ──> Matrix (A^(q)) (shares the MatrixT inside; HeckeOperatorOnK.h:231 returns const&)
[HeckeOperator | Family …] + q ──> Decomposition   (ctor copies the ops: HeckeModuleDecomposition.h:157; the handle ALSO keeps the
                                           source handles and q, because HeckeReportInput needs ell, n_sym, degree, level_b:
                                           HeckeReport.h:88-96)
Decomposition ──> Report                  (borrows decomp, level_a_stream: HeckeReport.h:98-101, 111-115)
```

Rule: a handle keeps alive everything the C++ object may dereference, transitively.
`HeckeTauTable` construction takes `hecke::tau_construction_mutex()` (`HeckeOperatorFamily.h:100`,
`HeckeOperatorFamily.cpp:91`; reason at `CampaignDriver.h:73-76`) even though the console is
single-threaded at the script level, so a future `parallel_for` verb or an in-session
`run_campaign` cannot race it. *(v3.7: slot-9 WP-7's lever L2, `b2941cb`, narrows the lock in
`HeckeOperatorFamily::build_pipelines()` alone, to priming K's simplex index — the family's
constructions run outside it, `HeckeFamilyConcurrentBuildValidation`; every other holder, the
console's and the bindings' builds included, is unchanged, so this rule stands.)*

### 4.2 State machine

`declared → computed | failed`. Members are *structural* (available when declared: `.p`, `.n`,
`.dims` of a `Model`) or *computed* (trigger `compute()` under the handle's settings snapshot).
`?x` shows the state, the snapshot and the creation site. `failed` rethrows the stored error on
every access and is never retried (§2 C2); the user constructs a new object.

### 4.3 Printing

* Size cap `print_max_entries` (default 400): a larger matrix prints as `Matrix 1677 x 1419 over
  F_134217757 (hash 0x…)`; `show(x)` prints everything; `save(x, path)` writes the canonical form
  to a file; `json(x)` gives the report JSON where one exists (`HeckeOperatorOnK.h:267`,
  `HeckeModuleDecomposition.h:183`, `HeckeReport.h:126`) and a console-generated JSON (with a
  proper string escaper, gap G1) for `Record`s.
* Numbers are canonical residues in `[0, p)`.
* The **canonical** rendering is what a transcript contains and what `hash` never sees (hashes are
  computed from the object, not from its text); the **display** rendering differs only in that a
  *top-level* `String` loses its quotes under `print` and `str` (§2 C5). `show(x)` is canonical.

### 4.4 Introspection

`help` lists verb groups; `help hecke` prints the overloads, argument names, defaults and the
doc string registered with the verb, plus the header:line of the API it wraps; `?x` describes a
value — type, state, dimensions, the settings snapshot **with its engine, mathematical and
presentation families separated** and the mathematical fingerprint, the creation site, the
members, and a `resumable:` line when the handle has one (§2 C5). `types()`, `verbs()`, `vars()`,
`settings()` enumerate; `settings()` shows every key with its `source`. `help --markdown` emits
the reference manual (`docs/console/console.md`, regenerated when the registry changes; a
freshness gate is a §16.4 follow-up, not a validation).

*(v3.6, C4 as built.)* `help` is a C0 grammar statement inside `Console/Core/`, and Core was frozen
in slot 8 (`[S8]` §3.0). So the generator ships as a **binding verb, `help_markdown()`**
(`Bindings/Reference.cpp`, registered after the harness verbs, so no existing overload moves). It
returns the manual as one String, and `print(help_markdown())` prints it bare.
`docs/console/gen_console_md.sh` runs `cohomology_app -c 'print(help_markdown())'`. With `--check`
it diffs the output against the committed file and exits 1 when that file is stale. The manual is a
**pure function of the registry**:
* the CLI usage;
* the language section, with the §3.2 EBNF and the two rules below in words;
* the exit-code table;
* every verb and overload, in registration order, which is resolution order;
* every type with its members;
* every setting, with the engine knobs naming their environment variable instead of a
  machine-dependent default.

At `5c70e95`, `gen_console_md.sh --check` reports the committed file current, `coefficient_ring`
row included. The statement form `help --markdown` stays the design. Adding it is a Core edit, and
the owner decides when (§16.4).

*(v3.7-pre.1.)* **Pass the binary's path** whenever the build is not `./build/cohomology_app` or
`./hacs` under the repository root — an agent's worktree build, a `cross_config.sh`
build root, an out-of-source build elsewhere: `docs/console/gen_console_md.sh
<path>/cohomology_app [--check]`. Without it the script takes the first of those two it finds,
which in a shared checkout can be a stale in-source binary, and a `--check` against the wrong
binary is not evidence. At `7ddb555`, `gen_console_md.sh build/cohomology_app --check` (the fresh
out-of-source build) reports the committed file **current**, with C5a's and C5b's verbs and types
in it, and its exit-code table names a legal but unexecutable `--set` value under exit 5 and an
invalid `--set` value under exit 1, as §6 now says.

**Two things the reference must state in words** (v3, the C1 debts of the header): that
`-2 ^ 2 == 4` because the unary minus binds inside the base of `^`, and that `print`/`str` render
a top-level string bare while every other position quotes it.

---

## 5. Mapping existing capabilities onto console verbs

| Capability | Today | Console verb | Underlying call |
|---|---|---|---|
| Cohomology of `Sym^n(F_ell^2)` on the SL(2,Z) model | `--bench cohom n ell` (`BenchDriver.cpp:265`; v3.6.1: `:307`) | `cohomology(symmetric_power(sl2z_model(), n, ell))` | `BenchDriver.cpp:304-315` recipe (v3.6.1: `:312-319`) |
| `T_p` (and `U_ell`, same path) | `--bench hecke n ell p` (`:299`; v3.6.1: `:341`) | `hecke(H, p)` | `:317-326` (v3.6.1: `:359-368`) |
| `T_{p^r}` recursion vs direct | `--bench family n ell p r` (`:363`; v3.6.1: `:405`) | `F = family(H); F.T_pow(p, r) == F.T_pow_direct(p, r)` | `HeckeOperatorFamily.h:131, 173` |
| Primary decomposition | `--bench decomp n ell p` (`:424`, largest degree chosen `:452-457`; v3.6.1: `:466`, `:492-499`) | `decompose([T2, T3], q = 1)` | `HeckeModuleDecomposition.h:157-180` |
| Report JSON | campaign per-job JSON; `HeckeReport` | `report(D, path = …)`, `T2.json` | `HeckeReport.h:126-141` |
| Cross-checks | `--bench hecke … --cross-checks` (`:844-847`; v3.6.1: the flag is parsed at `:1076`, the cross-checks run at `:391-392`) | `crosschecks(T2)` → record | `HeckeCrossChecks.h:141` |
| Validations | `<Name>`, `--all`, `--all-full`, `--list` (`kernel.cu:129-146, 165-172`) | `validations([tier])` → list of `(name, tier)` (`ValidationRegistry.h:76`); `run_validation("Name" [, inherit_settings])` → Int (`:62`); `run_validations(tier = "fast")` → Record (`:70`) — **deferred** (v3.5: unbound at C2b; no acceptance item uses it) | in-process, same registry; run with the session overrides **lifted** (env defaults) unless `inherit_settings = true`, session state restored afterwards; the validation's chatter goes to the sink or, under `verbose`, to the console stream |
| Benchmarks | `--bench <mode> …` | `bench("hecke", n=128, ell=…, p=2, repeat=3, lean=true)` → a Record `{mode, params, dims, total_s, total_us, median_s, repeats, rss_mb, phases, extra, bench_line}` (v3.5 as built: times are Strings with an Int twin; `checksum` on `micro`) | ~~**gap G4**: today only `bench::RunBench(argc, argv)` is public (`BenchDriver.h:51`); `RunCohom/RunHecke/RunFamily/RunDecomp` (`BenchDriver.cpp:265/299/363/424`) return `PhaseTimes` but sit in an anonymous namespace.~~ **v3.6 (P-2): G4 is CLOSED** (C2b, `fee4690`): `bench::RunMode(const ModeArgs&) -> BenchRecord` is public at `Bench/BenchDriver.h:124`, `RunBench` at `:154`; the runners `RunCohom/RunHecke/RunFamily/RunDecomp` are at `BenchDriver.cpp:307/341/405/466` (+ `RunExt` `:561`), at `5c70e95`. `--bench`'s printed output is byte-identical (`ConsoleCliPreservationValidation`; `bench_identity.sh`, 45 cases) |
| Micro-benchmarks | `--bench micro …` | `micro("gemm", 512, backend = "engine")` | same route. v3.5: `gemm` / `gemv` / `rref` / `kernel` / `transpose` / `suite`; **`micro("cuda")` is CLI-only** (`--bench micro cuda`), since the GPU throughput table is a printed report, and the verb refuses it with a typed error |
| Campaigns | `--campaign spec [--output …] [--dry-run]` (`CampaignDriver.h:178`; v3.6, P-4: `:208`) | `spec = campaign_spec("file.spec")` / `campaign_spec_text("…")` (`CampaignSpec.h:169-170`; v3.6, P-4: `:371-372`); `campaign_plan(spec)` → groups (`:177`; v3.6: `:379`; v3.5: named `campaign_plan`, not `plan`, as built); `run_campaign(spec, output = …)` → a Record `{output_dir, ran, skipped, failed, jobs, summary_tsv, index_json, wall_s}` (`CampaignDriver.h:144-164`; v3.6: the struct at `:163`, the runner `RunCampaignSpec` at `:188`); `single_job(spec, job, output)` (`:169-170`; v3.6: `SingleJobSpec` at `:199`) — **deferred** (v3.5: unbound at C2b) | all public already; runs with session overrides lifted (as for validations) |
| Golden harness | `GoldenRegressionValidation`, `GoldenEmit` (owner-gated) | `golden_subset([[10, 691], …])` → `(mismatches, digest, records)` (`GoldenHarness.h:53-54`); `golden(point, object)` → the frozen hash / value (G13; **shipped in C1a**, in `Bindings/Reproducibility.cpp` and not in `Harness.cpp` — v3.2) | `GoldenEmit` **not** exposed as a verb (stays `GOLDEN_EMIT=1` gated, `GoldenHarness.h:30-33`) |
| Engine settings | env vars | `set threads = 4`, `set device = "cpu"`, `set backend = "engine"`, `set lean = true`, … (§2 C4) | plain setters |
| Timing / memory | `--bench` prints | `timed(expr)` → `Record`, `time(expr)` (**deferred**, v3.5), `bench_line(record)`, `rss()` (`CampaignDriver.cpp:299-316`, file-local — gap G4b; **the process high-water mark**, not the verb's) | v3.6 (P-3): **G4b CLOSED** (`fee4690`): `Util/Rss.h` (`PeakRssMiB` `:47`, `ResetPeakRss` `:56`), used by bench, campaign and console |
| Model descriptor | campaign `model =` key | `models()`, `sl2z_model("sl2z_7vertex")` | `HeckeModelDescriptor.h:74` |
| Dickson-exceptional predicate | `IsDicksonExceptional` (`HeckeEndToEndValidation.cpp:98`, file-local) | `dickson_exceptional(n, ell)` | gap G9: public header (`[ME §5 R8]` demands the predicate, never a list). v3.6 (P-3): **G9 CLOSED** (`2855084`): `hecke::IsDicksonExceptional`, `Hecke/DicksonCount.h:62` |

**Preservation of the existing CLI.** The new branch is inserted in `kernel.cu` *after* the
`--help` test (`:160-163`) and *before* the validation-name loop (`:165-172`), recognising
`--script <file>`, `-c <code>`, `--console` / `-i`, and `-` (stdin). None collides with a
registered name (every registered name is identifier-shaped — 66 at `d54c589`, 77 today,
`ValidationRegistry.cpp:236-…`); today
`-c`, `-i` and `-` are "unknown validation" failures printing `[FAIL] Unknown validation: …` with
exit 1 (`ValidationRegistry.cpp:148-149`) — **they change meaning, and this is stated here as the
only behavioural change to an argument the binary currently accepts.** The no-argument path
(`kernel.cu:76-110`) is untouched (Q1). `print_usage` (`kernel.cu:60-72`) stays **byte-identical**
by default; console usage is printed by `--console --help` (Q8). The lazy CUDA hook install
(`kernel.cu:119-125`) is untouched. All of this is gated by `ConsoleCliPreservationValidation`
(§11), which byte-compares the stdout and exit codes of the existing forms against outputs frozen
before the branch lands.

---

## 6. Scripting and reproducibility

* **Script = record.** A `.oc` file is the complete, replayable description of a computation:
  settings, objects, assertions, exports; `--log` (C5) turns an interactive session into one.
* **Parameters.** `--script f.oc [--set key=value]… [name=value]…`: `--set` applies session
  settings before the first statement; `name=value` pairs are parsed as literals and read as
  `args.name`; an `args.name` the command line did not supply is a runtime error (exit 3), and an
  undeclared `--set` key is exit 1. This is what makes a script usable from a shell loop or a CI
  matrix (`for n in 64 96 128; do ./hacs --script bench.oc n=$n; done`).
* **`include("prelude.oc")`** shares definitions between scripts (§3.2).
* **Exit codes** (`--script`, `-c`, stdin): `0` success; `1` usage / file not found / undeclared
  `--set` key; `2` parse error (reported before anything runs — the whole file is parsed first);
  `3` runtime error (including every `ENGINE_CHECK` and a missing `args.name`); `4` a failed
  `assert` / `expect_error`; **`5` a legal mathematical setting this build cannot execute**
  (`hecke::NotImplementedInThisBuild`, v3 — §2 C7; *v3.7.1*: through the campaign harness verbs as
§8's exit-5 row says — `campaign_spec` / `campaign_spec_text` exit 5 since slot-9 WP-8c,
`run_campaign` exit 3; *v3.8-pre.1*: `run_campaign` and `campaign_plan` exit 5 as well, from slot-10 WP-12, §8; *v3.8*: built, the exit-5 branch reached by no input at the base, §8; and an unwrapped member getter's `NotImplementedInThisBuild` is exit 5, §2 C7); `exit(n)` sets it explicitly. The REPL exits
  0 on `quit`/EOF, or with the code of the last `exit(n)`. Codes 0–4 are C0's, shipped and pinned;
  **5 is added by C2**, the phase in which a mathematical setting first exists — no C0 behaviour
  changes, and a C0-only build can never produce it. *(v3.6.)* **A `--set` argument is refused
  with exit 1 in every case.** That covers an undeclared key, a bad value, and a legal value this
  build cannot execute, such as `--set coefficient_ring=Z` *(v3.13.0: legal since slot-24 D6, exit 0; the example is now `--set coefficient_ring=Z/25`, exit 5)*. The refusal happens before any
  statement runs, so it is a usage error. It is not exit 5, even though the same value on a `set`
  statement is exit 5. Measured at `5c70e95`, re-measured for v3.6.1 with the console branch
  selected (`cohomology_app -c 'print(1)' --set coefficient_ring=Z` exits 1; v3.6's evidence run
  had a mis-ordered argv and never reached the console), and **pinned since v3.6.1** by one check
  in `ConsoleErrorValidation` arm (K).
  The CLI parser is `Core/ConsoleCli`, and Core was frozen in slot 8. Whether a legal but
  unexecutable `--set` value should be exit 5 is an owner question for C5, recorded here and not
  decided. *(v3.7-pre.1: **decided and built.** Owner ruling 2 (ii) (A) of 2026-09-24, `[S9]` §10;
  slot-9 WP-12, `b3cd0d3`.)* **A `--set` argument whose value is legal but unexecutable in this
  build — `MathSettings::set()` refuses it with `hecke::NotImplementedInThisBuild`, e.g.
  `--set coefficient_ring=Z` — is exit 5** *(v3.13.0: `Z` is no longer such a value; `Z/<m>` is)*, as the same value on a `set` statement is; an
  undeclared key and an invalid value (`--set coefficient_ring=Z/ell^1`) stay **exit 1**, a usage
  error. `Core/ConsoleCli` maps the refusal kind; `ConsoleErrorValidation` arm (K) changed its pin
  from 1 to 5 in the same commit and pins the three codes 5 / 1 / 0. The paragraph above, from
  "*(v3.6.)*", is the slot-8 state, kept as history.
* **Error location** `file:line:col:` on every message, plus the creation site of a lazily failed
  handle (§2 C7) — *v3.8-pre.1*: from slot-10 WP-12 also on a **member getter's** error and on the
  type-level `resume` refusal (§2 C7's two sites; the exit codes do not move — *v3.8*: built, and
  pinned by `ConsoleErrorValidation` arm (W); the codes of every shipped binding unchanged, one code
  of an unwrapped getter moved 3 → 5, §2 C7); a parse error also prints the offending line with a caret. *(v3.6: one known
  exception.)* The refusal of a reserved value on the `set` statement, `coefficient_ring = "Z"`,
  prints without a position. `Evaluator::exec_set` never back-fills one; the fix is
  `catch (ConsoleError& e) { e.set_pos_if_unknown(s.pos); throw; }`, one line in `Core/`. Core was
  frozen in slot 8, so the fix is **deferred to C5 in slot 9**, as an owner-authorised Core edit
  (§10 C5). The exit code is right (5); only the position is missing. `ConsoleErrorValidation`
  arm (K) pins the code and the key's name, not a position. *(v3.7-pre.1: **closed.** Slot-9
  WP-12's `exec_set` back-fill, the second authorised Core edit: the refusal now reads
  `file:1:1: not implemented in this build: …`, and arm (K) pins the position. The one exception
  left is narrower — an error raised by a type's **member getter** carries no position, because
  `Evaluator::object_member` does not wrap it (§2 C7; the fix is recorded for the next authorised
  Core batch, §16.4); its exit code is right.)*
* **Determinism contract.** With `verbose = false` (script default) the stdout of a script is a
  pure function of `(script, parameters, format version, build configuration)` — the same
  property `EngineDeterminismValidation` asserts for the golden digest under every
  `ENGINE_THREADS × ENGINE_BATCH` arm (CLAUDE.md, "Phase 4 Stage B"). `ConsoleDeterminismValidation`
  (§11) asserts it for the console transcript.
* **Tests and benchmarks as scripts.** Directory `src/hacs/Console/scripts/`:
  `NNN_name.oc` + `NNN_name.expected` (first line `#! oc-format 1`). `ConsoleScriptValidation`
  (`fast`) locates the tree via `OC_SOURCE_DIR` (`CMakeLists.txt:709-715`) with the
  `/proc/self/exe` walk-up fallback of `ConsumerMigrationValidation.cpp:37-51`, runs every script
  **in-process on a fresh `Session`** with stdout/stderr captured, and compares byte for byte, `#~`
  lines excluded. `CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` regenerates the
  `.expected` files — owner-gated exactly like `GoldenEmit` (`GoldenHarness.h:30-33`), so `--all`
  stays read-only and every changed expected line must be explained. Pins by `hash()` are
  restricted to **golden-grid points** (`GoldenHarness.cpp:160-173`: `n ∈ {0,1,2,4,10,16,22,24}`,
  `ℓ ∈ {2,3,5,13,691,10007,134217757}`, `p ∈ {2,3,5}`, `r ∈ {1,2}`, plus `(32, 5)`) and compare
  against `golden(point, object)`, never against a copied number; dimensions are pinned as the
  scalars `dim_H^q` (e.g. `GoldenReference.inc:7537`, `{"n=10 ell=691", "dim_H^1", 'A', 3, …}`),
  not as a hash of the list. Off-grid scripts assert *identities* (dims, certificates,
  recursion == direct) — rule R10. **And every pin is taken at the default mathematical
  configuration** (v3, rule R19): the settings fingerprint must be `0` where a `hash()` is
  compared, because the golden objects pin the defaults and nothing else (§2 C4 rule 1). A script
  that sets a mathematical key and then pins a hash is rejected by `ConsoleScriptValidation`, not
  silently compared.
* Benchmarks become scripts with `#~` output: `bench_hecke_128.oc` is runnable by
  `ConsoleScriptValidation` for *identity* (the `dims=` and checksum lines are un-tagged and
  compared) while its timings are ignored.

---

## 7. Interactive mode

* `./hacs --console` (alias `-i`). Prompt `oc> `, continuation `... `. Release 1 reads
  lines with `std::getline` (C6); `rlwrap` supplies history and editing.
* `--script f.oc --console`: run the script, then drop into the REPL with its bindings — the
  natural way to explore a prepared state.
* `Ctrl-C` *(v3.15.0-pre.5, NBCONFIRM S5; this bullet replaces the pre-S5 "not interruptible" text, which the code never
  implemented: until S5 the REPL installed no SIGINT handler and Ctrl-C ended the process)*. The process's own interactive REPL
  (`--console` / `-i`, also after `--script f.oc --console`) installs a SIGINT handler while it runs:
  - **during a statement**, the first Ctrl-C only raises the cancel request; the statement stops at its next cancellation point
    (§7.2) and the REPL prints `<pos>: interrupted (at <site>)`, then the next prompt. The
    interrupted statement's own binding is not made; earlier effects stay, as with any error (earlier statements of the same input line, and the earlier statements of a compound statement such as a `for` body's earlier assignments); a lazy handle whose work
    was stopped stays `declared` and its next read retries the work from the start; nothing else of the session changes;
  - **at the idle prompt**, and for **a second Ctrl-C before the first took effect** (a step with no point inside that the user
    wants to abandon), the handler restores the default action and re-raises: the process ends by SIGINT exactly as before S5
    (shell status 130). Two presses in quick succession therefore end the process;
  - at a §7.1 confirmation question the read continues (the handler restarts it); the answer is then not acted on: the call
    stops with `interrupted` before its work;
  - `run_validation`, `bench`, `micro`, `run_campaign` and `golden_subset` have no point inside (they report their own
    exceptions); a Ctrl-C takes effect after them.
  Scripts, `-c` and `-` install no handler (a Ctrl-C ends them, unchanged). The engine's thread-pool regions are still not
  aborted (`ThreadPool.h`): the points lie between whole units of work, so the cancel latency is at most one loop step of the
  running verb (measured: report §4).

### 7.1 Confirming a long computation (v3.15.0-pre.1; NBCONFIRM S3)

*Normative for the console core and the REPL / script modes; for `--serve` see §18.19 (v3.15.0-pre.3, NBCONFIRM S4).* Source of truth for the numbers:
`src/hacs/Console/cost/cost_models.tsv` (NBCONFIRM S2), embedded into ConsoleCore at configure time.

* **The silent envelope.** Each capped verb keeps its old cost bound as written (`descent`: N ≤ 300, n ≤ 60,
  index(N)(n+1) ≤ 300, Σp ≤ 100, p ≤ 97, ≤ 6 primes; `hecke_structure`: the same three; `level_n`: N ≤ 100, n ≤ 200,
  index(N)(n+1) ≤ 1000; `nebentypus`: N ≤ 100, n ≤ 100, index(N)(n+1) ≤ 1000, p ≤ 13, ≤ 4 primes; `forms_algebra`:
  k ≤ 400, `terms` ≤ 64; `hida_lambda`: ℓ ≤ 101, k ≤ 200, W ≤ 6; `hida_tower`: n ≤ 200; the four Gallery verbs: p ≤ 97,
  ≤ 6 primes). **Inside it nothing changes and nothing is estimated** — for `hecke_structure` too, where a cell inside
  takes up to ≈ 94 s (owner ruling 2026-11-06).
* **What stays a refusal**: every mathematical, word-size or well-definedness precondition (N ≥ 1, n even, p prime,
  p ∤ N, p ≠ ℓ, the ℓ ranges of `hida_tower` (≤ 23170, `lem:bounds`) and of the Gallery verbs (≤ 65521), m ≤ 3, k even,
  W ≤ k − 1, ℓ^W < 2^62 (`hida_lambda`, now checked before the run), the algebra name, the N = 1 rule, χ a unit and
  ord χ | ℓ − 1). Checks run in the pre-S3 order; when a crossed bound is followed, in the same call, by a failing
  precondition, every prompt-less mode reports the crossed bound's text (the pre-S3 first failure), a terminal REPL the
  precondition (it would refuse anyway, so nothing is asked).
* **Outside the envelope**, per mode and `confirm`:

  | mode | `ask` (default) | `yes` | `no` |
  |---|---|---|---|
  | `--script`, `-c`, `-`, a REPL whose stdin or stderr is not a terminal, the script half of `--script f --console` | the pre-S3 `TypeError`, byte for byte, exit 3 — **independent of the estimate and of the device profile** | runs (a `#~ confirm = yes: …` note) unless a hard refusal | pre-S3 `TypeError` |
  | REPL with stdin and stderr terminals | the decision rule below | runs unless a hard refusal | pre-S3 `TypeError` |
  | *(v3.15.0-pre.3)* `--serve` | the decision rule below, the protocol as the prompt (§18.19) | not settable in a served session | not settable in a served session |
  | *(v3.15.0-pre.3)* any mode, **inside an `expect_error` block** | the pre-S3 `TypeError`, byte for byte, exit 3 (a block that expects an error never asks) | runs unless a hard refusal | pre-S3 `TypeError` |

* **The decision rule** (`console::cost::Decide`, design §2.2 as amended by S2 Fix round 1). The estimator gives the
  central wall time and peak RSS and their upper edges `wall_hi = wall · max(band, 1.5) · x²`, `rss_hi = rss · max(band, 1.5) · x`
  (x ≥ 1: the extrapolation factor in cost space and in the model's own features); T = `confirm_wall_s`. *(S3 Fix round 1,
  S3 audit M1.)* A threaded RSS model (fitted at T = 1 and 16: `descent`, `hida_tower`) is interpolated in ln T, and **beyond
  T = 16 it is never below the T = 16 model**: rss(T) = max(r₁₆, r₁ + (r₁₆ − r₁) · ln T / ln 16) for T > 16 (unchanged for
  T ≤ 16); those two verbs' estimates carry the id `<verb>_cost/v2`, the others `<verb>_cost/v1`.
  1. **Hard refusal** (`RuntimeError`, exit 3, every mode, no override): `rss_hi` > min(session RSS cap, 0.8 · MemAvailable),
     or free space on C: (`/mnt/c`) ≤ 10 GB. For a threaded verb the message adds the estimate at `threads = 1`. *(S3 Fix
     round 1.)* Also refused, in every mode and environment: an estimate whose wall, RSS, `wall_hi` or `rss_hi` is not a
     finite number > 0 (`no usable estimate`); and a call with **no cost model** whenever a memory limit is known (without
     one, and with C: > 10 GB, it is a strong warning).
  2. **Strong warning** (asked twice; the second answer must be `yes`): `rss_hi` > 0.5 · MemAvailable, or `wall_hi` > 1 h, or
     x > 2, or a low-confidence model, or C: ≤ 20 GB free.
  3. **Normal warning** (asked once, `[y/N]`): `wall_hi` > T, or the estimate is extrapolated.
  4. Otherwise the call runs silently (a cell just outside the old bound whose estimate is small).
* **The prompt** goes to the real stderr (past any chatter capture), the answer is one line of the REPL's stdin:
  `<verb> is outside its silent envelope (<the pre-S3 refusal text>)` / `estimated ~ <wall> (up to ~ <wall_hi>), ~ <rss>
  (up to ~ <rss_hi>) at threads = <T_eff> (model <verb>_cost/v1|v2; <calibration>[; extrapolated x<x>][; low confidence])` /
  the strong reasons / notes (`descent` is lazy: the work runs at the first member read; a part may come back
  `status "refused"`; `hida_tower` may still refuse after its pre-pass) / `run it? [y/N]`. A declined prompt (or end of
  input) prints `not run` on stdout; nothing is bound and the session goes on. `descent` confirms in its constructor, the
  call that validates the arguments, not at the first member read; a confirmed `descent` cell hands its pieces the console's
  memory limit (min(40 GiB, the rule-1 limit)) as their own rule-19 cap, so an under-estimate ends as `status "refused"`;
  *(S3 Fix round 1, audit m3)* the exports of its methods `module(ell, K)` and `module_Z(mode)` get the same lowered cap
  (min of their own default and that limit; inside the envelope their defaults are untouched).
* *(S3 Fix round 1, audit m1)* `level_n` / `nebentypus` with N ≥ 2^31 refuse by name (`TypeError`, exit 3: "N must be
  < 2^31 (word size of the level code)") wherever the call gets past its envelope bound (`confirm = yes`, a terminal REPL);
  every prompt-less mode still stops at the N bound with the pre-S3 text.
* *(S3 audit i2)* `include("f.oc")` typed at a terminal REPL runs the included statements with the REPL's confirm input,
  so they may ask; `--script f --console` keeps the script half prompt-less.
* **T_eff** = min(`threads`, the CPUs of the affinity mask). **The device profile** scales the wall estimate only (never
  RSS): `${HACS_DEVICE_PROFILE:-${XDG_CONFIG_HOME:-~/.config}/hacs/device_profile.tsv}`, `none` = no profile; a profile
  whose calib set or ELF build id (size + mtime when either side has none) differs from the running binary is **stale**: not
  applied (factor 1) and named in the prompt. It is written by `hacs --calibrate[=thorough]` and never read by a
  record, a hash, the golden or the campaign. Without a profile the prompt says `uncalibrated` and points at `--calibrate`.
* **Validations** pin `HACS_DEVICE_PROFILE` (`none` or a frozen fixture), and the pty child of `ConsoleCostModelValidation`
  runs with the read-only test interlock `HACS_HOST_PROBE_FIXTURE=1` (MemAvailable 4096 MiB, C: 255 GB; S3 Fix round 1,
  audit m2). `--calibrate` refuses a profile path inside the source tree (`REFUSED`, exit 1; audit m5). The model-drift gate (`--calibrate=thorough` on
  the reference box, `COST_MODEL_DRIFT … verdict=OK|DRIFT`) is a close-window step, never part of `--all`.

---

### 7.2 Cancellation points (v3.15.0-pre.5; NBCONFIRM S5)

* **Limits (documented, no behaviour change).** (i) A handle whose work completed before the stop is `computed` (e.g. `descent(23, 10, [5, 7])`: the parallel pair region is one step, so a Ctrl-C during it takes effect at the next point after it, and the handle is computed). (ii) The served `done` for an interrupted cell carries the position only (`<cell>:L:C: interrupted`), not the site that the REPL prints; this is consistent with §18.6. (iii) The `hida_lambda.*` points also lie inside `BuildHeckeStructureRecord` under the non-default `heckez.G8 = hida`; the console verb always passes the default `RecordSettings`, so a cancel cannot reach it today.
* **The request** is one process-wide flag (`Console/Core/Cancel.h`), raised by the REPL's SIGINT handler (§7), by a served
  `interrupt` and by SIGTERM in `--serve` (§18.6); it is cleared at the start and the end of every REPL statement and served cell.
* **A point** (`console::PollCancel(site)`, in the pipeline `oc_util::CancelPoint(site)` of `Util/CancelPoint.h`, a hook that is
  null unless the console bindings are registered) is a no-op unless the calling thread runs a REPL statement or a served cell
  (`CancelScope`) and is not inside a `NoCancelScope` (rendering, the harness drivers above). It then throws `console::Interrupted`,
  which is neither a `std::exception` nor a `ConsoleError`: no verb, no evaluator `catch`, no `expect_error` and no lazy-handle
  state machine swallows it.
* **Where**: every statement and every verb / method / lazy-member call of the evaluator; the confirmation answer (§7.1); `descent`
  (the record's stages, per Hecke prime, per torsion read; also inside a later cell's lazy read); `hecke_structure` (per `P_rule`
  round, per p | N, per local read, per Tor read, and the descent's points); `level_n` / `nebentypus` (the cokernel, per Hecke
  prime); `forms_algebra` (the cusp space, per Hecke prime); `hida_tower` (the pre-pass, the module cell, its cohomology, per Hecke
  operator, per level); `hida_lambda` (per Miller basis form, per space, per Hecke operator). The full list with file:line: the S5
  report §2.
* **Rules** (normative for every new point): only on the thread that called the verb; between whole units of work, never inside a
  kernel, a parallel-region body, a destructor, a `noexcept` function or the builder of a cache entry; so unwinding drops only
  stack-local partial results and **a cancelled run never populates a cache entry that a later run reads**. A point reads and
  changes no value: a statement that is not cancelled computes exactly what it computed before S5, and a statement re-run after a
  cancel computes exactly what an uncancelled run computes (`ConsoleCancelValidation`).
* **Test interlock** `HACS_CANCEL_TEST=after:K | wait:K | hold:K [:PREFIX]` (read-only): at the K-th visit of a point (whose site
  starts with PREFIX) raise the request / announce a `#~ cancel test: waiting at <site>` line (a `progress` frame in `--serve`) and
  wait ≤ 60 s for an outside request / announce and stay 3 s. Read by the interactive REPL and by `--serve` (there only as the
  direct child of this same binary, as `HACS_HOST_PROBE_FIXTURE`). It can only stop a statement; it changes no value.
* **Optional phase C3 (unscheduled, design kept verbatim).** A hand-rolled raw-mode editor over
  POSIX `termios`: left/right$HOME, backspace/delete, up/down history, Ctrl-A/E/K/U/L/D, Tab
  completion over registered verb names, type members, session variables, `set` keys and file
  paths after a quote (computed from the registry, so extension-engine verbs complete for free);
  history file `$OC_HISTORY`, else `~/.cohomology_history`, disabled by `--no-history`, never
  written in script mode (Q5); terminal state restored by an `atexit` hook and on
  `SIGINT`/`SIGTERM`; dumb fallback when `isatty(STDIN_FILENO)` is false or on `_WIN32`. It lives in
  `Console/Platform/` so `ConsoleCore` stays STL-only. Gate: `ConsoleLineReaderValidation`
  (`fast`), pty-driven (`posix_openpt`), feeding escape sequences and asserting the edited buffer,
  the completion candidates and the restored `termios`.

## 8. Error model (summary; C7 is normative)

| Origin | C++ type | Console behaviour |
|---|---|---|
| `assert` / `expect_error` | `console::AssertionFailure` | exit 4 |
| exact-integer overflow | `hecke::HeckeOverflow` (`ExactInt.h:25`, a `std::runtime_error`; caught first) | error, class named |
| a legal setting this build cannot execute (v3: `locality = strict`; v3.1: no settings value; v3.4: `field_polynomial = conway`, raised by its consumer, slot-5 WP-7; v3.6: `coefficient_ring = Z` / `Z/<m>`, raised by `MathSettings::set()` itself (*v3.13.0: `Z/<m>` only; `Z` is stored and refused by name at every consumer but the integral descent*), and `Z/ell^<k>`, raised at every pipeline verb, slot-8 WP-3) | `hecke::NotImplementedInThisBuild` (`HeckeSettings.h`, a `std::runtime_error`; caught before it) | its own message and **exit 5**; never reported as a bad value, never degraded to the default. *v3.6 (C4)*: also through a lazy handle's `compute()`, via `bind::LazyCompute` (exit 3 before C4), and on the `set` statement, via the binding `InstallMathSettings`; the `set`-statement message has no `file:line:col` yet (§6). *v3.7-pre.1 (C5a, slot-9 WP-12)*: also as a **`--set` argument** (exit 5, no longer 1), and the `set`-statement message **carries its position**; a handle of one `coefficient_ring` used under another, at any verb; every member of a ring handle that `[E]` `sec:ring` (h) does not list (`bind::GateTypeOnRing`); every C5 verb that does not honour the ring, at dispatch and in its lazy compute, and every C5b verb handed a ring handle (`bind::RequireFieldHandle`). A member getter's refusal has the right code and no position (§2 C7). *v3.7.1 (referee m-6; slot-9 WP-8c, `cc3d30a`)*: **the campaign harness verbs** — `campaign_spec` and `campaign_spec_text` rethrow a `NotImplementedInThisBuild` from the spec parser (`ext = true` under a non-default `coefficient_ring`, or a grid cell with `ell^k >= 2^64`) as exit 5 (through v3.7 they wrapped it as a runtime error, exit 3), while every other spec error keeps exit 3 (`ConsoleErrorValidation` arm (M), with that control); `campaign_plan` has no wrap and can raise no ring refusal (the spec is validated when it is parsed); `run_campaign` wraps every exception as a runtime error (exit 3), a ring refusal included — a spec that reaches it has already been accepted by the parser. *v3.8-pre.1 (specified; slot-10 decision 6 (iii) (A), built by slot-10 WP-12)*: **`run_campaign` and `campaign_plan` map `hecke::NotImplementedInThisBuild` to exit 5**, by the WP-8c pattern — each verb's body runs inside one handler that re-throws a `ConsoleError` unchanged, turns a `NotImplementedInThisBuild` into `NotImplementedError("<verb>: " + what(), pos)` (exit 5), and turns every other `std::exception` into `RuntimeError("<verb>: " + what(), pos)` (exit 3, as today); the handler must catch the refusal kind **before** `std::exception`. For `campaign_plan` this makes explicit what the core's classifier already does for an unwrapped verb (its code does not move); for `run_campaign` it changes exit 3 to 5 for a ring refusal only. Slot-10 WP-12 names, per verb, an input at its base that reaches a `NotImplementedInThisBuild` (e.g. `run_campaign` with `inherit_settings = true` under a session ring, if the run reaches a refusing surface) and pins it, with an unrelated error kept at exit 3 as the control; a verb that no input reaches is recorded so, and **no test-only hook is added to production code** for it. *v3.8-pre.1*: a **member getter's** refusal (exit 5, or 3 for a named `std::logic_error`) now carries the member access's `file:line:col` (§2 C7, site 1). *v3.8, as built (slot-10 WP-12, `Console/Bindings/Harness.cpp`)*: one `CampaignVerbHandler` wraps `campaign_plan`'s body and `run_campaign`'s `RunCampaignSpec` call — a `ConsoleError` re-thrown, a `NotImplementedInThisBuild` → `NotImplementedError("<verb>: …", pos)` (exit 5, caught before `std::exception`), anything else → `RuntimeError("<verb>: …", pos)` (exit 3); an ordinary `campaign_plan` failure's text moves from `campaign_plan(...) failed` + cause to `campaign_plan: <what>`, its code 3 unchanged. **Reachability, recorded per verb, no test hook added**: `campaign_plan` — **no input** reaches the refusal (the spec's ring refusals fire at parse time, arm (M); `plan_campaign()` is a pure function of the parsed spec; a wrong argument type fails overload resolution first); `run_campaign` — **no input found**: under `inherit_settings = true` with a session ring on a field spec the jobs run under the spec's own settings (exit 0), `field_polynomial = conway` with `ext = true` raises the refusal inside the ext pass but the pass catches it per cell (the cell "unavailable", exit 0), and a ring job's refusals at `r ≥ 2` or `ell ∈ {2, 3}` are recorded by the job, caught per job — these facts are pinned (arm (W) w23, w24), with an uncreatable output directory kept at exit 3 as the control (w22). So the handler makes explicit, for both verbs, a code no input reaches today. And by §2 C7's site 1, **an unwrapped member getter raising `NotImplementedInThisBuild` is exit 5** (it was 3 at the base); every shipped gated getter already was |
| `ENGINE_CHECK` | `std::logic_error` (`EngineCheck.h:55`) | error, message verbatim (already `file:line`) |
| pipeline contract | `std::runtime_error` / `std::invalid_argument` | error |
| memory | `std::bad_alloc` | error; session continues |
| console type / arity | `console::TypeError` | error with the verb's signature list; nothing bound |
| parse | `console::ParseError` | before execution; exit 2 |
| *(v3.15.0-pre.1)* a call outside its silent envelope, prompt-less (§7.1) | `console::TypeError` (the pre-S3 text, byte for byte) | exit 3; nothing bound |
| *(v3.15.0-pre.1)* hard refusal of the cost rule (§7.1 rule 1: memory, C:) | `console::RuntimeError` ("… refused before the run (…): …") | exit 3 in every mode, no override; nothing bound |
| *(v3.15.0-pre.2)* no usable cost estimate (§7.1 rule 1: a non-finite or non-positive estimate; no cost model while a memory limit is known) | `console::RuntimeError` ("… refused before the run (…): no usable estimate …" / "no cost model …") | exit 3 in every mode, no override; nothing bound |
| *(v3.15.0-pre.1)* a declined confirmation (terminal REPL only) | `console::ConfirmDeclined` (kind `not run`) | the REPL prints `not run`; nothing bound; the session goes on |
| *(v3.15.0-pre.1)* `hecke_structure(1, 0)`; `hida_tower` with K = m + e_max < 2 | `console::TypeError` (the latter after the torsion pre-pass, from `hida::TowerPreconditionError`) | exit 3 (was the `ENGINE_CHECK` row, also exit 3) |
| compute-time failure of a handle | any of the above, raised inside `compute()` | handle bound in state `failed`; error names access site + creation site; rethrown on every later access; never retried. *v3.6*: `ConsoleErrorValidation` (C4) asserts every row of this table through real script files on the `--script` path, with the exit code, the `path:line:col` prefix and, for a lazy failure, the creation site |

*v3.9-pre.1 (specified; slot-11 WP-16, a/s)*: the two θ verbs of §3.6 add **no row and no exit
code** to this table. `dickson_les` and `theta` raise `hecke::NotImplementedInThisBuild` under a
non-default `coefficient_ring` (at dispatch and in `DicksonLES`'s lazy compute, through
`bind::LazyCompute`) and on a ring handle — **exit 5**; a mismatched pair of handles is a
`console::TypeError` — **exit 3**; `ell < 5` is the `ENGINE_CHECK` row — **exit 3**, message
verbatim; a failed `DicksonLES` compute binds the handle `failed`, never retried (the last row).
`ConsoleErrorValidation` pins each through real script files, in one new arm letter.
*(v3.9: not built — slot-11 WP-16 was not run; the rows above stay specified.)*
*(v3.9.2, as built — slot-12 WP-8: every row above holds as specified; `ConsoleErrorValidation` arm
**(T)** pins them through ten script files and one REPL run — the ring in force at `dickson_les` /
`theta` dispatch and a ring handle in either argument exit 5, mismatched `n` (naming the three numbers)
and mismatched `ell` exit 3 as type errors, `ell < 5` exit 3 naming `lem:h2torsion` for both verbs
(for `DicksonLES` a lazy failure naming its creation site), the creation-time snapshot rule, odd `n`
not refused, and a failed `DicksonLES` rethrown on every access, never retried.)*

*v3.9 (as built; slot-11 WP-18c)*: the digit handles of §3.6 add **no row and no exit code**. A
per-cell refusal (`ell ∈ {2, 3}` beyond `2^64`, `ell ≥ 2^31`, `n` odd or `0`, the bit and memory caps,
"precision insufficient") is `hecke::NotImplementedInThisBuild` — **exit 5**; a member off `[E]` (h)'s
digit list — **exit 5**; a field member (`dims`, `C`, `Z`, `B`, `H`, `P`) — the `std::logic_error`
row, **exit 3**; `--set coefficient_ring=Z/ell^4097` — an invalid value, **exit 1**.

*v3.9.3 (as built; slot-12 WP-17)*: the wide handles of §3.6 add **no row and no exit code**; the band
`2^32 ≤ ell^k < 2^64` no longer reaches the `uint32_t` ring context's refusal (formerly exit 5 at the
first computed access). A member off `[E]` (h)'s list on a wide handle — **exit 5**; a field member —
**exit 3**, as on every ring handle.

In the REPL every error leaves the session usable; in scripts every error is fatal. There is no
`try`; `expect_error` is the only error-consuming construct and exists for validation scripts.

---

## 9. Architecture and TU layout

```
src/hacs/Console/
  Core/                         -> static library ConsoleCore (STL only; checked by check_console_includes.sh rule 1)
    ConsoleError.h/.cpp         SourcePos, the error hierarchy, ExitSignal/QuitSignal, CONSOLE_CHECK/CONSOLE_DEBUG_CHECK   [C0]
    Lexer.h/.cpp                tokens, positions, numeric literals                                                        [C0]
    Ast.h                       node types, source spans; the §3.2 EBNF reproduced verbatim                                [C0]
    Parser.h/.cpp               recursive descent per §3.2                                                                 [C0]
    Value.h/.cpp                Int/Bool/String/List/Record (+ Nil)                                                        [C0]
    Object.h/.cpp               Object, TypeInfo, keep-alive edges, state, settings snapshot, creation site, ResumableState[C0]
    Settings.h/.cpp             SettingSpec / Settings / SettingsSnapshot / SettingsScope; the R1 family split             [C0]
    Registry.h/.cpp             types, verbs, overload resolution, docs, the exception-translator seam                     [C0]
    Evaluator.h/.cpp            statements, expressions, scoping (one global frame + for-loop shadowing), include, args    [C0]
    Printer.h/.cpp              canonical + display printers, size caps, #~ tagging, JSON escaping for Records             [C0]
    Session.h/.cpp              variables, authoritative settings + snapshot, cout/cerr redirection (ChatterCapture), log   [C0]
    LineInput.h/.cpp            dumb getline input with continuation                                                       [C0]
    ScriptRunner.h/.cpp         in-process drivers (RunSource / RunFile / RunRepl), parameters, exit codes                 [C0]
    ConsoleCli.h/.cpp           RunConsole(argc, argv) -- the command-line surface                                         [C1a]
  Bindings/                     -> compiled into cohomology_app, never into ConsoleCore
    Bindings.h/.cpp             the shared binding helpers (argument coercion, typed errors, the payload base)             [C1a]
    Payloads.h                  the type-erased payload structs every binding TU stores in an Object                       [C1a]
    CoreMath.cpp                Fp / Poly / Matrix and the §3.5 linear-algebra verbs over FlatMatrixT / MatrixT / FpPolyT / ModCtx  [C1a]
    Model.cpp                   sl2z_model, complexes                                                                      [C1a]
    Cohomology.cpp              symmetric_power, cohomology, block accessors, the four degree members                      [C1a]
    Hecke.cpp                   hecke, family (no decompose/report yet)                                                    [C1a]
    Reproducibility.cpp         hash, hash_int, golden(point, object), fingerprint, save_state -- GOLDEN()'S HOME (v3.2)    [C1a]
    Presets.cpp                 the six LocalSystemPresets local systems                                                   [C1b]
    Decomposition.cpp           decompose, report, crosschecks, the Block members, .json; and the settings seam that
                                registers one console setting per hecke::MathSettings::keys() entry                        [C1b]
    Harness.cpp                 validations(), run_validation(), bench(), micro(), campaign_spec(_text)(),
                                campaign_plan(), run_campaign(), golden_subset(), timed(), bench_line(), rss()   [C2b, v3.5]
    Reference.cpp               help_markdown(): the reference manual as one String (the shipped form of help --markdown) [C4, v3.6]
    EngineSettings.cpp          the engine knobs as set keys (second settings installer)                        [C2a; v3.6: listed]
    RegisterPipelineVerbs.h/.cpp  the explicit table                                                                       [C1a]
  Platform/                     -> optional phase C3 only
    LineEditor.h/.cpp           termios editor, history, completion (#ifndef _WIN32)
  ConsoleC0Validation.h/.cpp    (fast) the language core on core types only -- OUTSIDE Core/ by design                     [C0, shipped]
  ConsoleValidation.cpp         ConsoleScriptValidation, ConsoleScriptEmit, ConsoleCliPreservationValidation
                                (+ ConsoleLineReaderValidation under C3)
  ConsoleSettingsValidation.h/.cpp     (fast)     [C2a]            v3.6: each of these three in its own TU, as built
  ConsoleDeterminismValidation.h/.cpp  (standard) [C2b, C4]
  ConsoleErrorValidation.h/.cpp        (fast)     [C4]
  scripts/                      NNN_name.oc + NNN_name.expected; cli_frozen/ (the pre-console CLI outputs)
src/hacs/HeckeExt/
  RegisterHeckeExtensionVerbs.h   forward-declares `namespace console { class Registry; }` ONLY -- no Console/ include   [C1b]
  RegisterHeckeExtensionVerbs.cpp sturm_bound(k, ell [, cap]), u_ell_decision(n, ell [, budget_mb]); the ONE file in
                                  HeckeExt/ that includes Console/ headers, by one exact-path exception per guard        [C1b]
src/ModArithmetic/Fnv.h   the one FNV-1a-64 (G5, SHIPPED -- not Util/Fnv.h)
src/hacs/Golden/GoldenHarness.h   GoldenLookup(point, object) (G13, added by C1a -- not Util/GoldenLookup.h)
src/hacs/Util/ Rss.h (G4b, C2)
docs/console/
  00-console-interface-plan.md  this file;  01-console-plan-audit.md  the audit
  console.md                    generated language + verb reference (help --markdown; v3.6: help_markdown()), checked in
  gen_console_md.sh             regenerates console.md from the binary; --check diffs it (exit 1 when stale)   [C4, v3.6]
docs/matrix-engine/tools/check_console_includes.sh
```

Three v3 corrections are visible in that tree. **(1)** The validation TU is
`Console/ConsoleC0Validation.{h,cpp}`, *outside* `Core/` (`[WP5]` §2 deviation 2, adopted): its
tree-level arms walk directories through POSIX `<dirent.h>` and shell out to the include guard,
which inside `Core/` would either break the STL-only rule or force `check_console_includes.sh` to
carry an exception for its own test. Putting it in `cohomology_app` keeps `ConsoleCore` free of
both. **(2)** `ScriptRunner` is C0 and `ConsoleCli` is C1a — v2's §9 put both in `Core/` while its
§10 listed both under C1; the split is by *what the C0 validation needs* (the in-process drivers
and the exit-code table) versus *what touches `argv`*. **(3)** `Util/Fnv.h` and
`Util/GoldenLookup.h` are gone: the FNV header shipped at `src/ModArithmetic/Fnv.h` and
the lookup belongs to `Golden/GoldenHarness.h`, which is where the `.inc` already lives.

`Core/` cannot include `EngineCheck.h` without breaking its own acceptance criterion (b), so it
defines **`CONSOLE_CHECK` / `CONSOLE_DEBUG_CHECK`** with exactly the semantics CLAUDE.md demands
of the engine pair — an always-compiled `std::logic_error` carrying `file:line` and the
stringified condition, and an `NDEBUG`-compiled-out debug twin (`[WP5]` §2 deviation 6, adopted).
No bare `assert` outside the validation TU, and no `unordered_*` anywhere in `Console/`.

CMake: `add_library(ConsoleCore STATIC …)` with `-Wall -Wextra` like the other four
(`CMakeLists.txt:156, 225, 278, 317`); `target_link_libraries(cohomology_app PRIVATE … ConsoleCore)`
(`:624`); the binding TUs appended to the executable's source list with a placement comment in the
style of `:380-386`. No new options. `kernel.cu` adds one branch:

```
if (arg1 == "--console" || arg1 == "-i" || arg1 == "--script" || arg1 == "-c" || arg1 == "-") {
    console::RegisterPipelineVerbs();
    return console::RunConsole(argc - 1, argv + 1);
}
```

**How the extension engine plugs in — as shipped in C1b** (v3.2; `[OD]` slot-3 close-out 1,
confirmed as slot-4 confirmation 4; `[WP4-5]` §3). It ships
`HeckeExt/RegisterHeckeExtensionVerbs.cpp`, calls `Registry::register_type` for its objects and
`register_verb` for its operations (adding overloads to `charpoly`, `hash`, `print` where its
`F_ℓ[X]/(π)`-algebra objects need them), and the `kernel.cu` branch calls that one function too,
beside `console::RegisterPipelineVerbs()`. It never edits `Core/`.

**That costs exactly two guard entries, and they are exact paths.** The option was chosen on the
statement that it "needs no guard change", which was false: `check_heckeext_includes.sh` rule 2
forbids *any* `Console/` include inside `HeckeExt/`, and `check_console_includes.sh` rule 2
forbids a console include outside `Console/` except `kernel.cu`, `*Validation.*` and
`ValidationRegistry.cpp`. So:

* `check_console_includes.sh` rule 2 gains **one `ALLOW_CONSOLE` line**, the exact path
  `src/hacs/HeckeExt/RegisterHeckeExtensionVerbs.cpp`;
* `check_heckeext_includes.sh` rule 2, which had **no allow-list at all**, gains a
  **one-element exact-path exception array admitting `Console/` includes only** — `Cuda/`,
  `Engine/` and `BlockFlatMatrix.h` stay banned in that file as in every other.

Each entry carries its reason. **Rule 1 of each guard is untouched**, and `ConsoleCore` stays
STL-only: rule 1 of the heckeext guard still does not admit `Console/Bindings/`, and does not
need to. **Only the `.cpp` may carry the entry**: `RegisterHeckeExtensionVerbs.h`
forward-declares `namespace console { class Registry; }` and includes no `Console/` header, so it
is not a second offending path. Its header is included by `kernel.cu` (admitted by heckeext
rule 1 and console rule 2 already) and by `Console/ConsoleValidation.cpp` (a `*Validation.*` TU,
admitted by both); `Console/Bindings/` and `Console/Core/ConsoleCli.*` never include it. Its objects obey C2
(keep-alive edges, `compute()`-on-first-use, settings snapshot) and C5 (a canonical printer and
a per-kind hash — the engine's output schema `[S Stage 8]`, `[I §1 Stage 8]`, maps onto `Record`
and `json()`).

---

## 10. Phased plan

**Effort unit.** 1 AU = one engineer-agent workstream of the size the matrix-engine phases were
cut into (≈ 2–4 k lines including its validation and documentation, one review cycle). LOC are
estimates of new code, validations included.

### Dependency graph

```
C0 core language ──> C1a bindings + CLI + GoldenLookup + smoke scripts ──> C1b decomposition/report + the script set
       (SHIPPED)                                                    │              (needs E0b's hecke_report/v2)
                                                                    └──> C2a settings ──> C2b harness verbs ──> C4 hardening + docs   (split v3.4)
                                        └──> (C3 line editor: optional, on owner demand, independent)
Extension engine Stage 0 (in parallel with C1) ──> engine Stages 1–5 scripted on C1 + §3.5 ──> C5 extension bindings
```

### Phase C0 — Language core (ConsoleCore only) — **IMPLEMENTED 2026-09-16**

**Goal.** A pipeline-free interpreter for §3.1–3.3 with the core value types, testable in isolation.

**Scope.** `Core/` (dumb `LineInput`, `ScriptRunner`'s in-process drivers; no `Platform/`, no
`ConsoleCli`); `ConsoleC0Validation` (`fast`, target ≤ 0.1 s): ~600 cases over lexing (every
literal form, every error), parsing (every production, precedence table, continuation rules, caret
positions), evaluation (integer overflow, exact division, `for`/`if`, shadowing, `;` suppression,
`include` cycles, `args`, `expect_error`, the exit-code table 0–4), printing (format 1 fixtures,
canonical vs display, the entry cap, JSON escaping), the registry (overload resolution order,
keyword arguments, defaults, arity errors), the settings layer and the handle model — using a stub
type registered by the validation itself, since the arithmetic types are bindings (C3).

**Acceptance.** (a) `ConsoleC0Validation` returns 0 on `RelWithDebInfo`, `Check` (ASan/UBSan
clean) and `Bench`. (b) `ConsoleCore` has no include outside the STL (checked by
`check_console_includes.sh`'s reverse rule). (c) Parse + evaluate of a 10 000-statement synthetic
script ≤ 0.5 s (a sanity floor, not a benchmark). (d) The grammar in §3.2 and the implementation
agree — the validation carries the EBNF as a comment next to each production's tests.

**Result** (`[WP5]`, commit `2a332e5`): **all four met** — 612 checks / 0 failures in all three
configurations, the guard clean over 261 files, 10 000 statements in 0.015 s (0.061 s under ASan),
the EBNF reproduced in `Ast.h` with each parser function naming its production. 13 TUs,
`-Wall -Wextra` clean, no `unordered_*`, no `Matrix.h`, no raw `mod_*`. The eight adopted
deviations are in this plan's header table.

**Effort.** 1.5 AU, ≈ 3 000 lines. **Spent, in slot 1 of the hecke-extensions stage.**

### Phase C1a — Bindings, the CLI branch and the first pins — **IMPLEMENTED 2026-09-17** (slot-3 WP-7; see the status block at the head)

**Goal.** Every row of §3.4–3.6 *except the decomposition surface* callable; `--script` / `-c` /
stdin / dumb `--console`; parameters and `include`; `GoldenLookup`; `hash` / `golden`;
`ConsoleCliPreservationValidation`; a small smoke script set.

**Why the split** (v3; `[S2]` §3 WP-12 scope item 3, `[X]` §8 "no decomposition transcript before
E0b"). The decomposition and report objects are exactly the ones the extension stage's single
golden re-baseline moves: slot 2's E0b changes `HeckeReport`'s schema to `hecke_report/v2`, adds
the block keys `local` / `witness_poly` / `coefficient_field`, the `level_c.locality` object, the
four per-complex degree fields and a corrected multiplicity note — **384 golden lines**. A
transcript or a `decomp_*` pin frozen before that would be frozen against a schema that is about
to change, and re-baselining it would be indistinguishable from re-baselining a bug. So everything
that touches a decomposition or a report waits; everything else does not have to.

**Scope.** `Bindings/{CoreMath,Model,Cohomology,Hecke,RegisterPipelineVerbs}.cpp` (CoreMath
includes the §3.5 verbs that need no new substrate: `solve`, stacking, `vec`, subspace lattice,
`restrict`, `algebra`, `commutant`, `is_cyclic`, `random_*`, `jordan_type`, `bernoulli_mod`;
the local-algebra invariants follow in C5 when `[I G5]` exists). `Hecke.cpp` covers operators and
families and registers **no `decompose` / `report` verb**. `ConsoleCli` and the one `kernel.cu`
branch (`check_console_includes.sh` rule 2 already allow-lists `kernel.cu`).
**`GoldenLookup(point, object) -> const GoldenEntry*`** in `Golden/GoldenHarness.{h,cpp}`, with
slot 1's internal sweep lookup re-routed through it — value-preserving, and **one** lookup.
`hash` / `golden` over the shipped `src/ModArithmetic/Fnv.h`, filling `TypeInfo::hash`.
The frozen CLI outputs + `ConsoleCliPreservationValidation`. A handful of `fast` smoke scripts on
dimensions and `A(T_p)` hashes only, every pin through `golden(...)`.

**The C0 "no transcript before E0b" guard** (`[WP5]` §4) is retired **for the C1 registry only**
once E0b has merged; its three assertions — no `hash`/`golden`/`cohomology`/`hecke`/`decompose`/
`report` verb, no `TypeInfo::hash` filled, no `*.expected` under `Console/` — become, for C1a, "no
`decompose` / `report` verb and no `.expected` naming a decomposition object". The C0-only registry
assertion stays as it is.

**Acceptance.** (a) `ConsoleScriptValidation` (smoke subset) 0, `fast`. (b) Every pin compares
against `golden(point, object)` read from `GoldenReference.inc` through `GoldenLookup` — never a
copied number — every pinned point is on the grid, and every pin runs at the **default**
mathematical configuration (fingerprint `0`, §2 C4). (c) `ConsoleCliPreservationValidation` 0:
`--list`, `--help`, `--bench --help`, `--bench micro --help`, `--campaign --help`,
`--campaign <CampaignSmoke spec> --dry-run` and one validation name produce byte-identical stdout
and exit codes to the frozen files — with `--list` **compared modulo appended names** (§11).
(d) `-c 'print(1+1)'` exits 0 and prints `2`; a script with a parse error on line 7 exits 2
without running line 1; `--script f.oc n=10` binds `args.n`. (e) No `Console/` include outside the
allow-list. (f) ASan/UBSan clean on the script set (`Check` build). (g) The standing golden gate
(`GOLDEN_STRICT=1 GoldenRegressionValidation`) holds — C1a changes no value.

**Effort.** 1.0 AU, ≈ 1 500 lines + scripts.

### Phase C1b — The decomposition surface and the script set (after E0b) — **IMPLEMENTED 2026-09-21** (slot-4 WP-5; `docs/implementation/slot4/WP-5_report.md`)

**Goal.** The workflow of the §2 C1 flagship example end to end, and the ≥ 12-script set with its
`.expected` files, frozen against the **post-E0b** reference.

**Scope.** `Bindings/Decomposition.cpp`: `decompose`, `report`, `crosschecks`, the `Block` members,
`.json`. The script set: the §2 C1 example at `(10, 691)`, one script per golden-grid cell class
pinning `H.dims[q]` against `dim_H^q`, `hash(T.A(q))` against `A(T_p)^q` and `hash(D.U)` against
`decomp_*_U` via `golden(...)`, a `family` script asserting `T_pow == T_pow_direct`, a `decompose`
script asserting `certify() == 0`, an `expect_error` script for every documented throw (model
mismatch `HeckeModelDescriptor.h:76-80`, non-commuting operators
`HeckeModuleDecomposition.h:159-165`, a 64-bit object handed to `family`, `.Z(q)` under
`retain_intermediates = false`), a
`presets` script over the S¹ / cylinder / Möbius local systems (`LocalSystemPresets.h:15-23`), and
a linear-algebra script exercising every §3.5 verb on the `(10, 691)` operators (`restrict` of
`T_3` to the `T_2` block, `algebra([T2, T3])`, `commutant`, `is_cyclic`).
`ConsoleScriptValidation` + `ConsoleScriptEmit`.

**Strict locality is a script, not an `expect_error`** (v3.2; `[WP4-5]` §7 item 3;
`[WP3-3]` finding 7). Through v3 this scope line demanded an `expect_error` arm for
`locality = strict → not_implemented_in_this_build`; slot-3 WP-3 implemented strict mode, so
that arm would now assert a falsehood. It is replaced by **`015_strict_locality.oc`**, which
*runs* strict mode and pins the result. `hecke::NotImplementedInThisBuild` and **exit code 5**
stay pinned — by `ConsoleScriptValidation`'s test-only verb, which raises the named error
deliberately, since no settings value raises it today. **As shipped**: 16 numbered scripts with
frozen `.expected` transcripts, `016_extensions.oc` exercising the `HeckeExt/` verbs.

**The frozen shape is `hecke_report/v2`** (v3): a `.expected` file that contains report text
contains `"schema": "hecke_report/v2"`, the per-complex `q_max` / `truncated` / `q_max_source` /
`degrees`, the block keys `local` / `witness_poly` / `coefficient_field` (with `P` **keyed by
prime**) and `level_c.locality`. Any later schema move re-emits these files under
`ConsoleScriptEmit`'s owner gate with every changed line explained, exactly as `GoldenEmit` does.

**Acceptance.** C1a's (a)–(g), extended to the full script set, plus: every `.expected` carries
`#! oc-format 1`; `CONSOLE_EMIT_EXPECTED=1 ./hacs ConsoleScriptEmit` regenerates them
and is a no-op otherwise.

**Dependency.** **E0b merged** (slot 2 WP-2). Nothing in C1b may be started against the
pre-re-baseline reference.

**Effort.** 1.0 AU, ≈ 1 500 lines + scripts. **C0 + C1a + C1b ≈ 3.5 AU is the "usable console"
milestone**, unchanged in total by the split.

### Phase C2 — Settings and the harness verbs (split v3.4: C2a, C2b)

**Goal.** §2 C4 settings — **all three families**: the engine knobs, the **mathematical settings
through `Hecke/HeckeSettings`**, and the two presentation keys C0 already registers; the R3 verbs
`state` / `resume` / `save_state` (§2 C5) on the shipped instances; `validations` /
`run_validation` / `bench` / `micro` / `campaign_*` / `golden_subset` / `timed` / `bench_line` /
`rss`; `--log`; gaps G4, G4b, G9, G14.

**The split (v3.4; `[S6]` §6 confirmation 7, owner ruling 7 of 2026-09-22).** C2 is delivered as
two phases, so that the part that needs no bench refactor comes first. The acceptance items below
keep their v3 letters and are distributed, none dropped:

* **C2a — settings and resume (slot 6, `[S6]` WP-13, ≈ 0.60 AU).** The settings half of the goal:
  the three settings families through `set`, `reset_settings()`, env-only keys erroring,
  propagation into `run_concurrently`, snapshot-at-creation; the mathematical keys through
  `Hecke/HeckeSettings` only; `state` / `resume` / `save_state`; the exit-5 arm (in (g)).
  **Acceptance (f), (g), (h)**, with `ConsoleSettingsValidation`.
* **C2b — the harness verbs (slot 7, ≈ 0.90 AU).** `validations` / `run_validation` / `bench` /
  `micro` / `campaign_*` / `golden_subset` / `timed` / `bench_line` / `rss`; the bench-runner
  extraction under the byte-identity gate (G4, G4b); `--log`; G9; G14;
  `ConsoleDeterminismValidation`'s first arm. **Acceptance (a)–(e).**
  **Status (v3.5): built by slot-7 WP-8** (commits `fee4690`, `2855084`, `3d0322e`); **not merged
  at this revision's base, and its acceptance is the lead's**. *(v3.6, P-1: **merged** at
  `4508641`, with G4 at `cb1a874`, without a rebase, and **accepted by the lead** at the slot-7
  close; C2b is IMPLEMENTED.)* As built:
  * **G4**: `bench::RunMode(ModeArgs) -> BenchRecord`, with `--bench` output byte-identical.
  * **G4b**: `Util/Rss.h`.
  * **G9**: a public `hecke::IsDicksonExceptional`.
  * **G14**: `Hecke/HeckeLinAlg.h`.
  * **The verbs**: `validations([tier])`, `run_validation`, `bench`, `micro`, `campaign_spec` /
    `campaign_spec_text` / `campaign_plan` / `run_campaign`, `golden_subset`, `timed`,
    `bench_line` and `rss`. Each runs with the session's settings lifted to its baseline, unless
    `inherit_settings`, and with the chatter captured, unless `verbose`.
  * **`--log`** now also logs script, `-c` and stdin input.
  * **Script `022_harness.oc`**, a new artefact with a first-freeze transcript; the 21
    pre-existing `.expected` files are byte-unchanged.
  * **`ConsoleDeterminismValidation`** (`standard`, 122 checks), whose arms are (a)–(e).

  Relative to the goal list above: `run_validations`, `time` and `single_job` are **deferred**
  (unbound), and `micro("cuda")` is CLI-only (§5). No acceptance item names any of them.

**Acceptance.** (a) `set threads = 1` then `set threads = 16`: the script transcript is identical
(this is `ConsoleDeterminismValidation`'s first arm). (b) `set backend = legacy`: every `hash()`
of the C1 script set equals the engine arm's, **unconditionally** (the `ENGINE_BACKEND=legacy`
golden result, CLAUDE.md "Validation suite status"). (c) `run_validation("GoldenRegressionValidation")`
returns 0 from inside a script with the console's own output unaffected by the validation's
chatter, and with the session's `threads`/`device` overrides lifted for its duration.
(d) `run_campaign` on the `CampaignSmokeValidation` spec produces the same `summary.tsv` outside
its timing columns. (e) `bench("hecke", n=48, ell=134217757, p=2)` returns a record whose `dims`
equal `cohomology(...).dims`, and `./hacs --bench hecke 48 134217757 2` still passes
`ConsoleCliPreservationValidation`. (f) `ConsoleSettingsValidation` 0: each `set` key changes the
documented getter; `set` on an env-only key errors; interleaving `set` on three keys then
`reset_settings()` returns every getter to its env default; a setting is visible inside a
`run_concurrently` task; a handle created under `lean = true` computes lean after `set lean =
false`. (g) **The mathematical settings** (v3; C2a): each key of `hecke::MathSettings::keys()`
**as registered at the tree under test** (v3.4; through v3.3 "each of the twelve keys", a literal no
tree has matched — eight are registered at v3.4, and `[X]` §1.5's table has thirteen rows) — the
validation prints the count and the list, never compares them to a number written here, and its
report reconciles them against `[X]` §1.5, naming each row not yet registered and its consuming
phase — round-trips through `settings()` with its `source`; an unknown key and a bad value are both errors *raised by
`HeckeSettings`*, never by a console-side copy of the rule; at the defaults the fingerprint is
`0` and every `hash()` of the C1 script set is unchanged; a non-default key changes the
fingerprint and therefore every ext-layer `hash()`; and a mathematical setting set in the session
is visible inside a `run_concurrently` task. **The exit-5 arm is a settings arm again** (v3.4):
`set field_polynomial = "conway"` is accepted — it parses, validates and moves the fingerprint —
and a use that reaches its consumer (`HeckeExt/HeckeCanonicalField`) raises
`hecke::NotImplementedInThisBuild`, **exit 5**, never a bad-value error and never a silent fall-back
to `least`. *(v3.2 had moved the arm out of C2, because `locality = strict` computes since slot-3
WP-3 and no settings value then raised the error, pinning the mechanism by
`ConsoleScriptValidation`'s test-only verb (`hecke::kNotImplementedInThisBuildTag`), and said the arm
would move back "when a later slot registers a value its build cannot execute — `field_polynomial =
conway` is the standing candidate". Slot-5 WP-7 registered it; the test-only verb stays as the
mechanism's own pin.)* (h) **Resume-invariance** (C2a)
(v3): a handle created under `locality = budget=8` and resumed to `64` hashes equal to a fresh
handle under `64`, its state equals the fresh one's **modulo `budget_history`** (`[8, 64]` vs
`[64]`, asserted to differ), a resume to a lower budget is refused with the named error, a resume
on a complete state is a strict no-op, and a resume under a changed non-budget setting is refused.
*(v3.5; `[S7]` §10 owner decision 6 (A).)* "A resume on a complete state is a strict no-op" is
read **at the engine level**: `HeckeModuleDecomposition::resume_locality` on a complete state
leaves the state, the history and the change of basis unchanged. The console's `resume` on a
complete handle raises a typed refusal ("is complete") that moves nothing. That refusal
**conforms** to (h), and `014_expect_error.expected` is kept. Both halves are asserted by
`ConsoleSettingsValidation` (h). C2a shipped this reading in slot 6 (WP-13), and it was an open
owner item until this ruling.

**Effort.** 1.5 AU, ≈ 1 800 lines — v3.4: C2a ≈ 0.60 AU, C2b ≈ 0.90 AU (the bench-runner extraction under a byte-identity gate is the
cost the audit priced in, and it is C2b's; the mathematical settings add registration and arms, not logic — the
engine owns every default and every check).

### Phase C3 — Interactive editor (optional; on owner demand)

**Goal.** §7's termios editor; history; completion; `ConsoleLineReaderValidation`.

**Acceptance.** (a) The pty-driven validation asserts the edited buffer, the completion
candidates and the restored `termios` after `quit`, EOF and `SIGINT`. (b) Dumb mode still
selected automatically under a pipe. (c) `_WIN32` compiles the dumb path (build-only check).

**Effort.** 1 AU, ≈ 900 lines. **Not in the scheduled total.**

### Phase C4 — Hardening, determinism, documentation — **IMPLEMENTED 2026-09-24** (slot-8 WP-10; `docs/implementation/slot8/WP-10_report.md`)

**Status (v3.6).** C4 is implemented as scoped: commits `da2e591` and `101a221`, merged at
`e8aeeb4`; the WP-3 × WP-10 follow-up `06bebdc` tightened the console `coefficient_ring` arm to
exit 5.
* **(a) Met.** 24 / 24 arms produce one digest, `0xf6ed04bbe8e6b60a`. That is the C2b arm (b)
  engine digest over the same 16 scripts. The device arms `[SKIP]` without a device.
  `CONSOLE_DETERMINISM_ARMS=threads` is a read-only filter that restricts the product to the four
  thread arms, for CheckThread. Measured by `ConsoleDeterminismValidation`: 122 → **531** checks
  with a device.
* **(b) Met.** `ConsoleErrorValidation` (`fast`) passes 101 checks at WP-10's tip and **105** at
  `5c70e95`, where its conditional arm (K) on `coefficient_ring` is live. The arms:
  * (R): the §8 rows, as 16 real script files on the `--script` path;
  * (U) and (L): the exit-1 rows, and a failed handle never retried;
  * (P): the REPL survives every error;
  * (I): post-throw integrity, 13 golden objects of `(10, 691)` recomputed and matched after seven
    induced throws, under `device = cpu` and `gpu`;
  * (K): `coefficient_ring`.
* **(c) Met.** The line below, with `ConsoleErrorValidation` added to `--validations`, which makes
  it stricter, passes on all five configurations: golden 0 / 0, checksums equal, every validation
  0 (`[WP8-10]` §5.1). The `Check` row is the sanitizer run.
* **(d) Measured, indicative.** `docs/matrix-engine/tools/console_c4_budget.sh` measures the one
  name C4 registers, `ConsoleErrorValidation`, at 0.49 s against 5 s. The run was at load 23, so
  it is labelled `indicative`. The verdict (`label=window`) is the lead's window, and is not taken
  at this revision.
* **CheckThread** on (a)'s thread arms: 0 ThreadSanitizer warnings.
* **Documentation.** `docs/console/console.md` is generated by `help_markdown()` (§4.4).
* **`CLAUDE.md`.** Its section text was handed to the slot's close package (`[WP8-10]` §7.1), as
  the goal below requires.

Relative to the goal, as built: the generator is spelled `help_markdown()`, not `help --markdown`
(§4.4). The §8 table's exit 5 now also holds through a lazy handle and on the `set` statement
(§2 C7). One gap is left open, because it needs `Console/Core/`: the position of a `set`-statement
refusal (§6, C5).

**Goal.** `ConsoleDeterminismValidation` (all arms), `ConsoleErrorValidation` (with the post-throw
integrity arm), `docs/console/console.md` generated, sanitizer and `cross_config.sh` runs, and the
text of a **CLAUDE.md section handed to the slot's close package** — v3: a console phase does not
edit `CLAUDE.md` itself (the shared-file rule; `[WP5]` §2 deviation 9 was an explicit one-off
override and is withdrawn going forward).

**Acceptance.** (a) `ConsoleDeterminismValidation` 0: the C1 script set under `threads ∈
{1, 4, 16, 32}` × `program_cache ∈ {on, off}` × `device ∈ {cpu, hybrid, gpu}` (device arms `[SKIP]`
without a device, like every Phase 5 validation) produces one identical transcript digest.
(b) `ConsoleErrorValidation` 0: every row of §8 reaches its exit code with `file:line:col` and,
for a lazy failure, the creation site; after an induced throw (model mismatch, non-commuting
operators) the same session recomputes a golden-grid object and matches its `golden(...)` value,
repeated under `device = gpu` when a device exists. (c) `cross_config.sh RelWithDebInfo Bench Check
RelWithDebInfo+HECKE_PURE_INTEGER=ON RelWithDebInfo@ENGINE_BACKEND=legacy` with
`--validations ConsoleScriptValidation,ConsoleDeterminismValidation` green. (d) **The wall-time
budget of C4's new validations** (v3.4; `[WP6-10]` §4.2). Let `t(V)` be the wall of
`./hacs V` for each validation `V` that C4 **registers** in the `fast` or `standard` tier,
measured as the minimum of three runs at `ENGINE_THREADS=16`, default build, on the reference
machine (CLAUDE.md), and in the lead's measurement window when other agents share the box. **(d) is
met iff `Σ_V t(V) ≤ 5 s`.** The numerator is the named set of new names measured in isolation, so
no baseline `--all` run is needed and the numerator cannot contain its denominator; `--all`'s total
wall is reported beside it and is not gated. `5 s` (≈ 2.4 % of the 94-validation `--all`) is the
owner's pre-phase budget, **retained and marked unjustified**, in the manner of `[S6]` §10 ruling 2
for `[X]` §6.2 E2 (e) (v3.5 pointer correction; `[X]` v1.10 restates E2 (e) as a bound on the
campaign's overhead over the sum of per-cell timings).
*(Through v3.3: "`--all` wall time grows by < 5 s" — a difference of two ≈ 210 s walls with no
baseline tree, repeat count or reduction named, at a constant inside the ≈ 4 % run-to-run spread;
decidable by no protocol.)*

**Effort.** 0.75 AU, ≈ 700 lines + docs.

### Phase C5 — Extension-engine bindings (after E5's record-schema freeze) — **IMPLEMENTED 2026-09-24/25** (C5a slot-9 WP-12, C5b WP-13, C5c WP-8)

**Status (v3.7-pre.1; C5c v3.7).** Decision 2 (i) (A) split C5 into three lanes (`[S9]` §2.3 item 1), all
must-accept:
* **C5a — E7's and E8's types, the ring lift, the Core batch** (slot-9 WP-12, `b3cd0d3`, merged
  at `4bf2289`; `[WP9-12]`). `dual` / `pairing` (E7), and under `coefficient_ring = Z/ell^<k>` at
  `ell ≥ 5` the verbs and members of `[E]` `sec:ring` (h) (§3.6). Scripts `023`–`025`, first
  freezes.
* **C5b — the extension-layer bindings and the local-algebra verbs** (slot-9 WP-13, `80eb184`,
  merged at `53066cd`; `[WP9-13]`). Thirteen types and the §3.5 verbs, registered from
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (§3.6); the new console-free units
  `HeckeExt/HeckeAlgebraInvariants` and `HeckeExt/HeckeExtBindingSupport`; the validation
  `HeckeExtAlgebraInvariantsValidation` (`standard`, 404 checks). Scripts `040`–`047`, first
  freezes.
* **The follow-up of the two** (`f28a0fa`): the `Sturm` lazy handle wrapped in
  `bind::LazyCompute`, so a refusal inside it keeps exit 5 (C5a's scope item 5, deferred to the
  second merge because the TU is C5b's); `bind::RequireFieldHandle` at the dispatch of every C5b
  verb taking a `Cohomology` handle; arm (K) 204 → 210 checks.
* **C5c — the campaign's job loop under a non-default ring, `hecke_ring_report/v1`** (slot-9
  WP-8, `ad65bd9` with the amendment `f4fc3d2`, merged at `8853544`; the merge fix `158c0be`;
  `docs/implementation/slot9/WP-8_report.md`, `[WP9-8]`). **IMPLEMENTED (v3.7).** The job loop
  honours `Z/ell^<k>` at every `ell` with `ell^k < 2^64` and writes `hecke_ring_report/v1`
  (`[E]` `sec:ring` (g), with its four recorded deviations and the decimal-string coefficients of
  (g11)); a fingerprint-0 campaign is byte-identical; the ext pass and a grid cell with
  `ell^k >= 2^64` are refused at spec validation, before any job (`campaign.md` §15). Its gate is
  `CampaignRingValidation` (`standard`, 693 checks; §11). At `ell ∈ {2, 3}` the job loop reaches
  the Bredon object through `EquivariantCohomologyOnK` alone: since `158c0be` it builds its
  relation list from the raw `ModCtx::prime_power` context and does not name
  `SmallEllPolicy::Bredon` (`SmallEllPolicyScopeValidation`, slot-9 WP-9).
  **What the console sees of it.** C5c adds **no verb, type or member**, so `console.md` does not
  move. The C2b harness verbs reach it unchanged, because they call the same parse and run
  functions as `--campaign`: a spec text or file carrying `coefficient_ring = Z/ell^2` parses in
  `campaign_spec` / `campaign_spec_text`, `campaign_plan` lists the ring job under its `_s<16 hex>`
  id, and `run_campaign` runs it and returns the usual record, the job file being
  `hecke_ring_report/v1` (checked by hand at this revision's base, `(10, 691)`, `p = 2`; **no
  script or arm pins it** — a C5c console script is not in the slot). The session's own
  `coefficient_ring` does not reach the campaign: `run_campaign` lifts the session's settings to
  the baseline unless `inherit_settings`, and the spec's `math` section is what the job installs.
  **One observation for the owner** (v3.7): a spec-validation refusal (`ext = true` under a ring, or
  `ell^k >= 2^64`) reached the console as **exit 3**, not 5 — `campaign_spec` /
  `campaign_spec_text` wrapped every `std::exception` in a runtime error (`Harness.cpp`), so the
  `not_implemented_in_this_build:` tag survived in the message but not in the code. §8's exit-5
  row names `NotImplementedInThisBuild`; mapping it needed a binding edit (not a Core one).
  **Resolved in v3.7.1** by slot-9 WP-8c (`cc3d30a`, merged at `bdbb93c`): both verbs now rethrow
  it as exit 5, every other spec error keeps exit 3 (`ConsoleErrorValidation` arm (M), four checks
  with that control), and **C5c is pinned from the console** by `048_c5c_ring_campaign.oc` (a first
  freeze): `campaign_spec_text` → `campaign_plan` → `run_campaign` of a two-job `Z/ell^2` campaign
  at `(6, 5)`, then the same point built directly and its objects asserted against `golden(...)`
  (the console has no verb that reads a job file). `Console/Core/` untouched; `console.md`
  unchanged.
  **"Campaign and record"** (the v3.6 binding list's bullet, ruling 4 (A): "the campaign rows and record fields for `Z/ell^k`"): **met for the campaign** — the
  15 appended `summary.tsv` columns, `index.json`'s key and the record's members are those of
  `[E]` (g) as built; not as console *types* (no `RingJob` handle is bound: a user reads the
  record's files, as for a field campaign).

**Acceptance, as met by C5a and C5b.**
(a) **Met.** The `[S Stage 9]` cases are scripts `040`–`045`, each run to completion by
`ConsoleScriptValidation`: case 1 at `(10, 691)` through `ExtRecord` (040) and on all seven Kummer
cells (041), case 2 (042), case 3 (043), case 4 (044; `(58, 7)`'s non-split ideal recorded as
observed, `[E]` keeps it CONJ), case 5 (045). Whether a predicted outcome holds stays the engine's
acceptance, asserted in its own validation.
(b) **Met, with the two named exceptions** decision 2 (ii) (A) authorised: `Evaluator::exec_set`'s
position back-fill and `Core/ConsoleCli`'s exit 5 for a legal but unexecutable `--set` value, both
in C5a's commit. No other `Console/Core/` line moved; `check_console_includes.sh` reports OK.
(c) **Met.** `046_c5_identities.oc` is `identities.oc`: `k_max` is read from the certificate (7
at the base); at `(12, 5)` all seven items are assembled, none fails and none is unavailable; at
`(10, 691)` the default request passes 1–4, reports 5 `not_applicable`, and prints 6 and 7
`unavailable`, as (c) requires.
**The 22 pre-existing `.expected` files and `cli_frozen/` are byte-unchanged** (`ConsoleScriptEmit`
re-emitted them identically in both packages). `ConsoleDeterminismValidation`'s pinned digest
`0xf6ed04bbe8e6b60a` (the C1 set, 16 scripts) is unchanged; its arm (a) digest over every numbered
script moves with each new script by construction, and no document pins it.

**Goal.** `hecke_ext::RegisterHeckeExtensionVerbs` for whatever of `[I G2–G15]` has landed: `GF`,
`GFElt`, `MatrixQ`, `HeckeAlgebra`, `MaximalIdeal`, `is_local`, `LoewyProfile`, `ExtensionClass`,
`Atlas`, the boundary / compact-support / `ι` objects, `divided_power`, `L_map`, and the reserved
names of §3.6 (`ContragredientLocalSystem`, `Pairing`, `Presentation`, `Settings`, the complex
types with their four degree members, `coefficient_ring`); the remaining §3.5 local-algebra verbs
on `[I G5]`; the `[S Stage 9]` test cases as scripts. **Not in C5 any more** (v3.3):
`bernoulli_mod` and `glover_factors`, bound in slot-5 WP-10 from the same TU this phase will use —
neither needed the record schema, which is the only thing C5 waits for.

**Early and partial, already done** (v3.3; slot-5 WP-10, `[X]` §8 slot-5 Lane C): scripts
`017_predictions.oc`, `018_e0_locality_grid.oc`, `019_e1_stage1_sturm.oc` and
`020_e2_ramanujan_10_691.oc` — the E0–E2 cases as far as the C1b binding surface reaches, each a
**new** file with a first-freeze `.expected` and every pin taken at `MathSettings` fingerprint `0`.
They are acceptance (a) of this phase for those cases; what they do **not** carry is the record
object, which is the rest of (a) and still gates on the schema freeze.

**Scheduling** (v3; `[WP6]` §5 item 7): C5 runs **after E5's record schema freezes**, which
`[X]` §8 places in slot 5 of the extension stage, so C5 is slot 8 there. Binding it earlier would
freeze printers and hashes for objects whose record shape is still moving — the same mistake C1b
avoids against E0b, one layer up. *(v3.6: C5 is **slot 9's**, by owner ruling 8 (A) of
2026-09-24, `[S8]` §10. C4 took slot 8's console lane and is merged at `e8aeeb4`; its acceptance is the slot close's.)*

**The binding list, extended (v3.6; `[S8]` §3 WP-13, rulings 4 (A) and 8 (A)).** C5 binds **E7's
and E8's types** as well as the list above.
* **E7** (slot 6, accepted slot 7): the contragredient local system and its Hecke action (the
  reserved `ContragredientLocalSystem`), and the pairings with their perfectness and the PD
  adjointness gate (the reserved `Pairing`).
* **E8** (slot 8, `[E]` v1.9.0 `sec:ring` (d)): a cohomology object over `Z/ell^k`. It reports
  `lengths`, `invariant_factors` and `ladic_type` per degree, with `ladic_type_certified`, `r_K`
  and the `ladic_level` resumable state, and never a `dim`. Its free-quotient `charpoly(T_p)` is
  present only at a certified level. It carries `bockstein_rank` and `higher_torsion_count`, and
  `red(q)`, the reduction to the `F_ell` object.
* **Lifting the E8 refusals.** Binding E8 means lifting `coefficient_ring`'s console refusal for
  exactly the verbs that honour it. Every other verb keeps exit 5, per `[E]` `sec:ring` (b).
* **Campaign and record.** The campaign rows and record fields for `Z/ell^k` come with C5 (ruling
  4 (A)), under `[E]` `sec:ring` (a)'s golden-cost rule: a field emitted only under a non-default
  ring moves no golden line.
* **Core is still not touched.** Acceptance (b) below stands: no edit to `Console/Core/` is needed
  for any binding. *(v3.7-pre.1: held — no binding needed a Core edit; the two Core edits made
  are the owner items below, not bindings.)*

**Two owner items ride with C5 (v3.6), each a `Console/Core/` edit and so outside (b).**
1. The **position back-fill** on the `set` statement: one line in `Evaluator::exec_set` (§6).
2. Whether a legal but unexecutable **`--set`** value becomes exit 5 (§6).

If the owner authorises either, it is recorded as a named exception to (b), not as a binding.
Neither blocks C5. *(v3.7-pre.1: the owner authorised both, decision 2 (ii) (A) of 2026-09-24;
both are built in C5a's commit and recorded as the two named exceptions to (b) above.)*

**Acceptance.** (a) Each `[S Stage 9]` case exists as one script that **runs to completion**
under `ConsoleScriptValidation`; whether its *predicted outcome* holds (e.g. `(10, 691)`: exactly
one non-split Eisenstein–cuspidal `𝔪` in `X_4^+`, `r^1 = 0` on it) is the extension engine's
acceptance, asserted in its own validation, not the console's. (b) No edit to `Console/Core/` was
needed (the registry contract held). (c) **Every identity item that
`hecke_ext::HeckeIdentityCertificate` defines at the tree under test** (the E1 classes and
certificate items of `[S6]` §2.5 — items `1 … k_max`, with `k_max` read from the certificate's own
item list, never written here) is a script (`identities.oc`) that the engine's own validation runs;
an item the certificate reports `unavailable` is run and must print `unavailable`. *(v3.4,
`[WP6-10]` §4.3; through v3.3 "`[M §8]`'s identities 1–6", a third numbering that `[S6]` §2.5
retired and that silently excludes item 7, reserved from slot 6 on.)*

**Effort.** 1–1.5 AU, ≈ 1 200 lines (engine side excluded); a placeholder until the engine's API
exists.

**Scheduled total: ≈ 6.75–7.25 AU (C0 1.5 + C1a 1 + C1b 1 + C2 1.5 [v3.4: C2a 0.60 + C2b 0.90] + C4 0.75 + C5 1–1.5), ≈ 9.7 k
lines including validations, scripts and generated docs; C3 adds 1 AU if commissioned; the usable
console is at ≈ 3.5 AU. C0's 1.5 AU is spent.**

### Phase C5 leftovers (slot 10, WP-12) — **IMPLEMENTED 2026-09-25** (specified v3.8-pre.1; slot-10 WP-12, `3c96d63`, merged at `6726075`)

*(v3.8, as built.)* **Step 1** found no frozen transcript and no `cli_frozen/` case exercising
(i)–(iii) (`025` pins `L.relations` / `H.ell` / `T.cosets` by substring only; `048` runs a ring
campaign to exit 0), so no re-baseline. **Acceptance, as met**: (a) the 34 frozen transcripts and
`cli_frozen/` byte-unchanged, `026_c5_leftovers_ring_members` a first freeze (8-line transcript);
(b) `ConsoleDeterminismValidation`'s C4 (a) digest `0xf6ed04bbe8e6b60a` unchanged on 24/24 arms (its
all-scripts (a) digest moves with the new script, as designed and unpinned); (c) arm (W) and the
script green — `ConsoleErrorValidation` 218 → **294** checks, tier `fast` (≈ 1.8–2.5 s), so no new
name; (d) `ConsoleScriptEmit` changed no existing transcript; (e) `git diff <R0> -- Console/Core/`
shows §2 C7's two sites only, `check_console_includes.sh` OK, `prelude.oc` / `cli_params.oc`
untouched. `console.md` regenerated (one row). Under `Check` (ASan/UBSan, `ENGINE_CUDA_DISABLE=1`)
`ConsoleErrorValidation` and `ConsoleC0Validation` pass with no sanitizer finding. No validation name
registered. The package's scope and acceptance as specified follow, unchanged.

**Why.** C5 shipped with three recorded leftovers (`[X]` open item 4): a member getter's error has
no position (§2 C7), the structural members of a ring handle exit 5 (§3.6), and `run_campaign`
wraps a ring refusal as exit 3 (§8). The owner ruled all three at recommendation (A) (`[S10]`
decision 6); this row is their specification. **Base** slot-10 WP-2's accepted tip; **lane C**,
after WP-2; its lift commit is the last commit of its branch (`[S10]` §4.2).

**Scope.**
1. **Step 1, before any edit**: list every frozen transcript (`Console/scripts/*.expected`,
   `cli_frozen/`) and every `ConsoleErrorValidation` / `ConsoleScriptValidation` pin that exercises
   (i) a member-getter error, (ii) a structural member on a ring handle, (iii) `run_campaign` /
   `campaign_plan` raising `NotImplementedInThisBuild`. **Prediction: no frozen transcript.** A
   non-empty transcript list **stops** the package (an owner-gated re-baseline).
2. **(i) Core, the one named exception** — §2 C7's two sites, nothing else in `Console/Core/`.
3. **(ii) Bindings** — §3.6's five members through `bind::GateTypeOnRing`'s rule functions (one
   new member, `LocalSystem.coefficient_ring`, registered on the type); every other unlisted member
   still exit 5.
4. **(iii) Bindings** — §8's handler on `run_campaign` and `campaign_plan` (`Console/Bindings/Harness.cpp`).
5. **Tests**: a new arm letter of `ConsoleErrorValidation` for (i)–(iii) (the four changed rows of
   arm (K) — `L.n`, `L.d_V`, `T.p`, `T.r` — reported as changed, `L.coefficient_ring` new), the
   count moves, the tier stays `fast` (a new name if its wall would cross the tier); scripts from
   **`026_`**, each a first freeze; `docs/console/gen_console_md.sh --check` after the lead
   regenerates `console.md`.

**Acceptance.** (a) The 34 frozen transcripts and `cli_frozen/` byte-unchanged (or the ruled
re-baseline); (b) `ConsoleDeterminismValidation`'s digest `0xf6ed04bbe8e6b60a` unchanged; (c) the
new arm and scripts green; (d) `ConsoleScriptEmit` changes no existing transcript; (e)
`git diff <R0> -- src/hacs/Console/Core/` shows §2 C7's two sites only;
`check_console_includes.sh` OK; `prelude.oc` and `cli_params.oc` untouched (`[S10]` §3.0).

**Effort.** ≈ 0.15 AU (`[S10]` §8).

### Phase θ — the Dickson long exact sequence at the console (slot 11, WP-16, a/s) — **specified v3.9-pre.1; not built (v3.9)**

*(v3.9.2.)* **Built in slot 12 (WP-8)**: step 1's prediction held (no frozen transcript or pin named
`theta` or `dickson_les`); the bindings are in `HeckeExt/RegisterHeckeExtensionVerbs.cpp` only; arm (T)
of `ConsoleErrorValidation` (tier `fast` kept, 347 checks); script **`027_dickson_theta`** at `(30, 5)`
and `(16, 7)` (a first freeze) asserts every item of scope 3, plus the det twist at `p = 2` by hand
(`mul(A_up, t) == scale(mul(t, A_n), 2)`, the untwisted identity failing). Acceptance (a)–(d) met.

*(v3.9.)* **Not built in slot 11**: WP-16 was the named give-way when the owner put arbitrary `k` into
slot 11 (`[S11]` §10, decision 3 re-ruled). The row below is unchanged and binding for the slot that
takes it up; its step-1 prediction ("no frozen transcript names `theta` or `dickson_les`") still holds
at `1106200` (35 transcripts).

*(v3.9-pre.1, spec first; `[S11]` = `docs/implementation/hecke_extensions_slot11_plan.md` rev 2, §3
WP-16 and §10, decision 5 (A): WP-16 is **as schedule permits**.)* If the slot's lanes leave no room,
the package is stopped at the close and this row stays specified, not built.

**Why.** The slot's headline — θ as the Dickson multiplication, its long exact sequence and its
Hecke equivariance (`[E]` v1.12.0-pre.1 `sec:thetaobj`, identities (6a)–(6h)) — should be reachable
from a script, as C5b made the Stage 1–5 objects reachable. **Base** WP-6's accepted tip (the verbs
bind WP-5 / WP-6's driver, never a second implementation) and this pre-release merged; **lane** after
WP-4 and WP-6 (`[S11]` §4.1); its registration commit is the last of its branch.

**Scope.**
1. **Step 1, before any edit**: list every frozen transcript (`Console/scripts/*.expected`,
   `cli_frozen/`) and every `ConsoleErrorValidation` / `ConsoleScriptValidation` pin that names
   `theta` or `dickson_les`. **Prediction: none** (the names are new). A non-empty list stops the
   package (an owner-gated re-baseline).
2. **Bindings** — §3.6's `DicksonLES` type and the two verbs, in
   `HeckeExt/RegisterHeckeExtensionVerbs.cpp` only (`[S11]` §3.0: `Console/Bindings/*` and that TU
   are WP-16's alone; `Console/Core/`: nobody).
3. **Tests**: one new arm letter of `ConsoleErrorValidation` for §8's v3.9-pre.1 rows, tier `fast`
   kept (a new name if its wall would cross the tier; no re-tier); script **`027_`** (a first freeze)
   at one cell with `ell = 5` and one with `ell = 7` of WP-5's grid, asserting `.exact`,
   `.ker_equals_im`, the alternating sum of `.dims` equal to `0`, `twist_check == 0`,
   `u_ell_zero == true` and `theta(H, H_up).induced == L_map(H, H_up).induced` — no `golden(...)`
   pin exists for θ (slot-11 decision 6 (A): no golden event); `docs/console/console.md`
   regenerated by `gen_console_md.sh` and `--check` clean.

**Acceptance.** (a) The 35 frozen transcripts, `cli_frozen/`, `prelude.oc` and `cli_params.oc`
byte-unchanged; (b) `ConsoleDeterminismValidation`'s C4 (a) digest `0xf6ed04bbe8e6b60a` unchanged
(it runs the C1 set only; the all-scripts (a) digest moves with the new script, as designed and
unpinned); (c) the new arm and script green; (d) `ConsoleScriptEmit` changes no existing transcript;
(e) `git diff <R0> -- src/hacs/Console/Core/` empty; `check_console_includes.sh`
and `check_heckeext_includes.sh` OK.

**Effort.** ≈ 0.15 AU (`[S11]` §8).

### Phase N — the served console (slot 19, NB-1 spec / NB-2 build) — **specified v3.10; built v3.10.1 (NB-2)**

§18 is the whole specification; NB-2 (`--serve`, `PrintJson`, the `read_only` tags, the two validations of §11, the manual regeneration) is its only C++ package, guarded by the CMake option `OC_BUILD_NOTEBOOK`; the gateway and page (NB-3) are Python / JS outside the C++ build. Serial: NB-1 → NB-2 → NB-3.

### Schedule (v3), in the extension stage's slots

`[X]` §8's Lane C, re-cut by `[S2]` §2.3 item 3 and §4.1 and by owner confirmation 4 ("documents
first"). Lane C's **slot 2 is the four document packages** — `[C]` v1.4.0, its referee pass, `[E]`
v1.4.0 and this revision — and under the stage's "≤ 4 concurrent agents" rule a document editor is
an agent, so C1 could not have started in slot 2 as `[X]` v1.5.1 had it.

| Phase | Slot | Gate |
|---|---|---|
| **C0** | 1 | — | 
| **C1a** | **3** | this plan (v3) accepted; **E0b merged**, so no pin is taken against the old reference |
| **C1b** | 3 → 4 | C1a accepted; E0b merged (the hard gate: no decomposition transcript before it) |
| **C2a** (v3.4) | 6 | C1 accepted; the mathematical settings are the keys registered at the tree under test, `[X]` §1.5's others arriving with their consuming phases |
| **C2b** (v3.4) | 7 | C2a accepted |
| **C4** | **8** (v3.5; `[S7]` §10 confirmation 12; through v3.4: 7) — **IMPLEMENTED** (v3.6; slot-8 WP-10) | C2b accepted |
| **C5** | **9** (v3.6; `[S8]` §10 ruling 8 (A); through v3.5: 8) — split into C5a / C5b / C5c (v3.7-pre.1, `[S9]` decision 2 (i) (A)); **IMPLEMENTED**: C5a and C5b (slot-9 WP-12, WP-13), C5c (slot-9 WP-8; v3.7) | E5's record schema frozen (slot 5); C4 accepted (slot 8); the E8 objects specified (`[E]` v1.9.0 `sec:ring`; the ring lift in v1.10.0-pre.1 (h)) |
| **C5 leftovers** (v3.8-pre.1; **implemented**, v3.8) | **10** (`[S10]` decision 6 (A); slot-10 WP-12, merged at `6726075`) | C5 accepted (slot 9); `[E]` v1.11.0-pre.1 (h) and this pre-release merged (slot-10 WP-2) |
| **θ** (v3.9-pre.1; specified; *v3.9: not built*; *v3.9.2: **built***) | **11**, *a/s* (`[S11]` decision 5 (A); slot-11 WP-16) — not run; **12** (slot-12 WP-8) — **implemented** | C5 leftovers accepted (slot 10); `[E]` v1.12.0-pre.1 `sec:thetaobj` and this pre-release merged (slot-11 WP-4); WP-6 accepted |
| **Digit handles** (*v3.9*, as built; specified by `[E]` v1.12.0-pre.2 (h), not by a pre-release of this plan) | **11** (slot-11 WP-18c, `db1b454`; repaired `eff5851`) — **implemented** | `[E]` v1.12.0-pre.2 committed (`af1617e`, WP-18c's spec commit; *v3.9.1*: v3.9 said "merged") and merged with WP-18c; `Hecke/LadicCell` |
| **Wide band** (*v3.9.3*, Q9 decided (a) by the owner, 2026-09-26) | **12** (slot-12 WP-17, post-close) — **implemented** | Q9 ruled; the campaign's `RunRingPipeline<uint64_t>` (slot 9) |
| C3 | — | optional, on owner demand (Q3) |

C1 therefore spans **slots 3–4, possibly 5**, where `[X]` v1.5.1 had 2–4. **Track C gates no
engine phase** (`[X]` §8), so the stage's milestone M1 and its slot-5 deliverable do not move;
this is a lane-order decision the owner may reverse at any slot boundary. `[X]` v1.6 carries the
re-cut.

---

## 11. Validations added (all registered in `ValidationRegistry.cpp`, explicit table)

| Name | Tier | Phase | What it gates |
|---|---|---|---|
| `ConsoleC0Validation` | fast (~0.03 s) | **C0, shipped** | lexer / parser / evaluator / printer / registry / settings / handles on core types; **612 checks**; **and** `check_console_includes.sh` over the checkout (probed, not required). **Its tree arm is narrowed at C1b** (v3.2): from "no `.expected` file exists under `Console/`" — a slot-1 guard against freezing a transcript before the E0b re-baseline — to "**no frozen transcript names a pre-E0b decomposition object**". C1b legitimately creates the files the old arm forbade, and the property that actually mattered is the one now checked |
| ~~`ConsoleArchitectureValidation`~~ | — | — | **retired as a name** (v3): the guard is an arm of `ConsoleC0Validation` and, from C1a, of `ConsoleValidation.cpp` — §2 C8 |
| `ConsoleScriptValidation` | fast (~3 s) | C1a (smoke) → **C1b, shipped** | every `scripts/*.oc` vs its `.expected`, byte for byte (`#~` excluded); every pin is a golden-grid point compared through `golden(...)` **at the default mathematical configuration**. As shipped at v3.3 (slot-5 WP-10): **20** numbered scripts, **277 checks** — `017`–`020` are C5's early E0–E2 scripts, added as new files, the 16 pre-existing `.expected` byte-unchanged; the registration arm asserts the C1b surface is present (`decompose` / `report` / `crosschecks`, `Decomposition` / `Block` / `Report`), that `bernoulli_mod` and `glover_factors` now resolve, and that the C2 / C5 reserved names are still absent; it registers the `HeckeExt/` verbs on its own registry; and it carries the test-only verb that pins `NotImplementedInThisBuild` → exit 5. *v3.6 (P-5)*: **22** numbered scripts (`021` C2a, `022` C2b, each a first freeze), the 20 older `.expected` byte-unchanged; **294 checks** at `5c70e95`. C4 added no script. *v3.7-pre.1 (C5a, C5b)*: **33** numbered scripts — `023`–`025` (C5a) and `040`–`047` (C5b), each a first freeze, the numbering split so the two lanes never collided; the 22 older `.expected` byte-unchanged; **342 checks** at `7ddb555`. *v3.7.1*: **34** numbered scripts with `048_c5c_ring_campaign` (slot-9 WP-8c, a first freeze; the 33 older `.expected` byte-unchanged); **346 checks** at `bdbb93c`. *v3.8*: **35** numbered scripts (`001`–`026`, `040`–`048`) with `026_c5_leftovers_ring_members` (slot-10 WP-12, a first freeze; the 34 older `.expected` byte-unchanged); **350 checks** |
| `ConsoleScriptEmit` | fast (no-op unless `CONSOLE_EMIT_EXPECTED=1`) | **C1b, shipped** | regenerates `.expected`; owner-gated like `GoldenEmit`; refuses to freeze a script that does not exit 0. The **first** emission was part of C1b — a new artefact, nothing re-baselined |
| `ConsoleCliPreservationValidation` | fast | C1a | stdout + exit code of `--help`, `--bench --help`, `--bench micro --help`, `--campaign --help`, `--campaign … --dry-run`, one validation name, byte-identical to files frozen before the console branch; **`--list` compared modulo appended names** (below); re-run after the C2 bench extraction. **What the gate protects, and what it does not** (v3.2; slot-4 WP-2 §3): it protects *pre-console CLI forms from regressing*. A package that **adds** a `--bench` mode therefore legitimately changes `bench_help.stdout`, and the frozen file is re-captured — by regeneration from the binary, never by hand, on explicit authorisation, one file only, with the diff quoted in that package's report and asserted to be additive (no existing line modified, reordered or removed) and every other capture byte-unchanged. Slot 4's `--bench ext` is the first instance |
| `ConsoleSettingsValidation` | fast | C2 → **C2a** (v3.4) | each `set` key changes its getter; env-only keys error; interleave + `reset_settings()` restores env defaults; propagation into `run_concurrently`; snapshot-at-creation semantics; the mathematical keys and the fingerprint (**registered in C1b**, so C2 tests the *engine* knobs and the harness verbs on top of them) and resume-invariance (§10 C2 (g)(h)). *v3.2*: "`strict` → exit 5" is struck — strict mode computes, and exit 5 is pinned by `ConsoleScriptValidation`'s test-only verb. *v3.4*: the exit-5 arm returns here on `field_polynomial = conway` (§10 C2 (g)); the key count is `keys()`'s, printed, never a literal. *v3.6*: **11** keys (`coefficient_ring` appended by slot-8 WP-3), **219 checks** at `5c70e95` |
| `ConsoleErrorValidation` | fast | **C4, shipped** (v3.6; slot-8 WP-10) | every §8 row → exit code, `file:line:col`, creation site; post-throw integrity (golden object recomputed after an induced throw, CPU and GPU). *As shipped*: arms (R) 16 script files on the `--script` path, (U), (L), (P), (I) under `cpu` and `gpu`, and (K) `coefficient_ring`, live once the key is registered; **105 checks** at `5c70e95` (101 at WP-10's tip, before (K) was live); **107** since v3.6.1, which adds (K)'s `--set coefficient_ring=Z` exit-1 check; ≈ 0.4 s. *v3.7-pre.1 (C5a)*: arm (K)'s `--set coefficient_ring=Z` pin is **exit 5** (changed from 1 in C5a's commit, `b3cd0d3`, as the owner ruled); (K) also pins the `set`-statement position, the `--set` codes 5 / 1 / 0, `[E]` (h)'s closure member by member (61 single-access scripts under `Z/ell^2` at `(10, 691)`: 25 honour, 8 exit 3, 28 exit 5) and five rows at the uncertified `(30, 5)`; the follow-up `f28a0fa` adds one row per C5b verb that takes a ring handle. **210 checks** at `7ddb555`, ≈ 0.8 s (indicative). *v3.7.1*: arm **(M)** (slot-9 WP-8c) — a ring refusal through `campaign_spec_text` / `campaign_spec` is exit 5, an unrelated spec error stays exit 3; **218 checks** at `bdbb93c`. *v3.8*: arm **(W)** (slot-10 WP-12, 24 scripts) — the member-access position (§2 C7's two sites, on a test-only raw-getter stub and on the shipped bindings), the five ring-handle members with values, the handle's own ring, the mismatch rule both ways, the campaign verbs' recorded reachability with an exit-3 control; arm (K)'s four changed rows (`L.n`, `L.d_V`, `T.p`, `T.r`: 5 → 0) and one new (`L.coefficient_ring`); **294 checks**, ≈ 1.8–2.5 s, still `fast`. *v3.9 (slot-11 WP-18c)*: arm (K) gains the digit rows — a digit cell `Z/691^40` at `(10, 691)`: `H.lengths`, `H.invariant_factors(1)`, `H.precision`, `H.ladic_type(1)`, `T.charpoly_free` honour with their values; `H.bockstein_rank`, `H.red(0)`, `T.A(1)` exit 5; the field members `H.dims`, `H.C(1)` exit 3; the per-cell refusals exit 5 (`ell = 3` beyond `2^64`, the bit cap at `Z/ell^820` naming 8250 bits, odd `n`); `Z/ell^4097` exit 1, `Z/ell^64` exit 0; **309 checks**, still `fast`. The θ arm letter of v3.9-pre.1 does not exist (WP-16 not run). *v3.9.2 (slot-12 WP-8)*: arm **(T)** — the θ rows of §8 (ten script rows, one REPL run); **347 checks**, still `fast`. *v3.9.3 (slot-12 WP-17)*: arm **(Q9)** — the wide band: the routing at the four band edges on both primes (`5^13 | 5^14`, `5^27 | 5^28`, `691^3 | 691^4`, `691^6 | 691^7`: `IsWideCell`, served, `.precision` exit 5 below `2^64` and exit 0 beyond), an `A^(1)(T_2)` entry above `2^32` at `Z/5^14`, value identity with the campaign (`run_campaign` from the console, then the verbs: 13 hashed objects and the free charpoly) on seven band cells (`Z/5^14`, `Z/5^20`, `Z/5^27`, `Z/691^4`, `Z/691^6`, `Z/19^15 > 2^63`, `(30, 5)` at `Z/5^14` with `U_5`), and the member closure of a wide handle (48 rows: 24 honour, 7 exit 3, 17 exit 5); **539 checks**, ≈ 2.4 s, still `fast` |
| `ConsoleDeterminismValidation` | standard (≈ 5 s; **v3.6: restated, ≈ 25–30 s** — see the note after the table) | C2b/C4 (v3.4) | transcript digest identical across threads × program cache × device. *v3.5, as built by slot-7 WP-8 (`3d0322e`, in `Console/ConsoleDeterminismValidation.cpp`), 122 checks*: C2b's arms (a)–(e), which are the 22 numbered scripts under `threads = 1` and `threads = 16`, the C1 set under `backend = legacy`, `run_validation("GoldenRegressionValidation")` from a script, `run_campaign` against `summary.tsv`, and `bench` dims; plus `--log` replay and G9 on 366 cells. C4 adds the program-cache and device arms. *v3.6, C4 as built (slot-8 WP-10)*: the full product of (a), 24 arms, one digest `0xf6ed04bbe8e6b60a`; **531 checks** with a usable device (122 without the product). *v3.7-pre.1*: **564 checks** at `7ddb555`, digest unchanged; ≈ 27.5 s in the base's `--all` (indicative; decision 7's stop threshold is 45 s). *v3.7, after slot-9 WP-6* (`5689c20`, merged at `85a3c6a`): the tape elimination driver now compiles its per-panel programs under the caller's pass options (`consumer_pass_options()`), so the `gpu` arms reach the per-panel programs for the first time — **771 of 771 carry GPU nodes** (4330 nodes), the `hybrid` arms compile 771 of 771 under the hybrid policy (whose cost model keeps every node of these shapes on the CPU), and each arm prints one indented count line; checks (564) and digest unchanged. The wall, indicative (WP-6 §2 (e), 3 rounds each, shared box with the device): R0 min **28.60 s**, WP-6 min **29.22 s** (+0.6 s); **32.4 s** at the v3.7 base `9b004f2` at load ≈ 14 (this revision's own run). **Decision 7's stop (> 45 s) is not reached, so decision 13's conditional ratification of S8-D3 stands: the name stays `standard`.** The verdict wall is the lead's window's. *v3.8*: **570 checks** with script `026` (slot-10 WP-12), C4 (a) digest `0xf6ed04bbe8e6b60a` unchanged on 24/24 arms; 35.9 s inside a shared-box `--all` (indicative; the stop is 45 s) |
| `HeckeExtAlgebraInvariantsValidation` | standard | **C5b, shipped** (v3.7-pre.1; slot-9 WP-13) | not a console name, but C5b's engine-side gate: `HeckeExt/HeckeAlgebraInvariants`' certificate-free route against `HeckeLocalAlgebra` / `HeckeModuleStructure` on 17 certified-local ideals (3 non-reduced), constructed algebras including the Galois-conjugate trap, Jordan–Chevalley, the refusals, and `HeckeExt/HeckeExtBindingSupport`'s builders at `(12, 5)`; **404 checks**, ≈ 3–7 s (indicative) |
| `CampaignRingValidation` | standard | **C5c, shipped** (v3.7; slot-9 WP-8) | not a console name, but C5c's engine-side gate (`campaign.md` §15): a campaign under `coefficient_ring = Z/ell^<k>` at the seven E8 points (17 jobs) with every carried object equal to its frozen golden entry, the weight-12 free charpoly at `(10, 691)` and at the `uint64_t` cell `(10, 134217757)` in string form, `ell ∈ {2, 3}` against the frozen O7 rows with the three refusals, `r = 2`, the record's member order, `summary.tsv`'s 21 + 15 columns, `index.json`'s key, `resume`, `jobs = 1` == `jobs = 2`, and the spec-validation refusals; **693 checks**, ≈ 1 s (indicative) |
| `ConsoleLineReaderValidation` | fast | C3 (optional) | pty-driven editor behaviour, completion, terminal restore |
| `ConsoleReadOnlyTagValidation` | fast | **N, built v3.10.1 (slot-19 NB-2)** | registry ⇄ `Console/serve/read_only_verbs.tsv` both ways, no untagged-by-default, no tagged overload reaches a writer / emitter, manual tag column, `PrintJson` coverage — §18.11; `[SKIP]` when `OC_BUILD_NOTEBOOK=OFF` |
| `ConsoleServeValidation` | standard | **N, built v3.10.1 (slot-19 NB-2)** | the 38+ scripts through `--serve`: served `out` == `.expected` body byte for byte; envelope schema; determinism grid; §18.7 error mapping with the session surviving; interrupt; protocol robustness; env refusal; RSS cap; chatter capture — §18.11; `[SKIP]` when `OC_BUILD_NOTEBOOK=OFF` |
| `ConsoleServeAtlasValidation` | standard | **N, built v3.11 (slot-20 NB-4)** | the atlas sidecar writer and `--serve-atlas` (`oc-serve-atlas/1`) on Σ(23) and Σ(13) built in process: index = in-process index, every reply against `ParseAtlasStore`, sidecar ⇄ memory byte-identical, paging and the frame cap, errors, stale / corrupt index refused, env gate and hardening, the stores never written; optional real Σ(691) arm under `HECKE_ATLAS_IN` — §18.16 (h); `[SKIP]` when `OC_BUILD_NOTEBOOK=OFF` |

`--all` grows by **one** `fast` entry that is already registered (C0) and by five more `fast` plus
one `standard` as C1a–C4 land (plus one `fast` if C3 is commissioned).

**The `ConsoleDeterminismValidation` tier note, restated (v3.6; `[WP8-10]` §6, §8 item 2).** "≈ 5 s"
was v3.4's estimate before C2b existed, and it is stale.
* **As measured**, on the shared box and indicative: ≈ 19 s at C2b as merged, 122 checks; ≈ 25 s
  with C4 at WP-10's tip, at load 23; **29.4 s** at `5c70e95`, at load 23–25, 531 checks. C2b's
  campaign, golden and script arms dominate the wall. C4's 24-arm product adds ≈ 5 s.
* **The tier stays `standard`.** C4 (d) does not gate the name: C4 extended it but did not register
  it, and `console_c4_budget.sh` prints it on a `T_C4_INFO` line, not gated.
* **Owner decision.** Whether to re-tier it to `slow`, or keep it `standard` with this note, is the
  owner's. The recommendation is to keep it `standard`, because it is the only suite-level check of
  the console's determinism contract (§6).

The roster at `5c70e95` is **114** registered names: 46 `fast`, 58 `standard`, 10 `slow`. The
console's are the seven above, `ConsoleLineReaderValidation` aside. *(v3.7-pre.1: at `7ddb555`
the roster is **118** — 46 `fast`, 62 `standard`, 10 `slow`, from `--list`; the four added are
`HeckeBredonTreeRingValidation`, `HeckeIsotropyModelValidation`, `HeckeFreeModelValidation` and
C5b's `HeckeExtAlgebraInvariantsValidation`, all `standard`. C5a registered none. *v3.7*: at
`9b004f2` (every slot-9 code package merged) the roster is **125** — **52 `fast`, 63 `standard`, 10
`slow`**, 71 `Hecke*`, from `--list`; the seven added since `7ddb555` are WP-6's
`EngineElimPassOptionsValidation`, WP-7's `EngineArenaFirstFitValidation` and
`HeckeFamilyConcurrentBuildValidation`, WP-9's `SmallEllPolicyScopeValidation`,
`HeckeBredonU64FlatRouteValidation` and `IsotropyModelDeltaSquaredValidation` (all `fast`), and
C5c's `CampaignRingValidation` (WP-8, `standard`, 693 checks). None is a console name; the console's
seven are unchanged. *v3.7.1*: unchanged at `bdbb93c` — **125**, 52 / 63 / 10, 71 `Hecke*`; slot-9
WP-8c registered nothing.)* *(v3.8-pre.1: slot-10 WP-12 registers **no new name** unless `ConsoleErrorValidation`'s new arm would push it over the `fast` tier, in which case the arm goes under a new name and the old one keeps its tier (`[S10]` §3.0, "no package re-tiers"); its scripts are numbered from **`026_`** (the 34 numbered scripts `001`–`025`, `040`–`048` keep their numbers and transcripts); counts are WP-12's to measure and v3.8's to record.)* *(v3.8: WP-12 registered **no** name — arm (W) kept `ConsoleErrorValidation` inside `fast`. At `f0640d0` the roster is **129** — **52 `fast`, 67 `standard`, 10 `slow`**, 75 `Hecke*` — re-derived from the slot-10 registration fragments: the four added since `bdbb93c` are `HeckeConeCrossRouteRingValidation` (WP-3), `HeckeStrictLiftValidation` (WP-10), `HeckePeriodicityClassValidation` (WP-13) and `HeckeIntegralActionValidation` (WP-11), all `standard`; none is a console name, and the console's seven are unchanged. The slot close re-derives the roster from `--list`.)* *(v3.9-pre.1: slot-11 WP-16 (a/s) registers **no new name** unless `ConsoleErrorValidation`'s new arm would push it over the `fast` tier, in which case the arm goes under a new name; its script is numbered **`027_`** (the 35 numbered scripts `001`–`026`, `040`–`048` keep their numbers and transcripts). The roster entering slot 11 is **130** — 53 `fast`, 67 `standard`, 10 `slow` (`[S11]`, from `--list` at the slot-10 close); counts are WP-16's to measure and v3.9's to record.)*

**`--list` is compared modulo appended names** (v3; `[S2]` §2.3 item 6). Freezing `--list` byte
for byte would fail at the *next* registration by anyone, and every slot of the extension stage
registers validations — slot 1 alone took the count from 68 to 77. The gate is therefore: every
line of the frozen `--list` must appear in the live `--list`, **in the same relative order**, with
the same tier; extra lines are allowed and are *reported* so an unexpected growth is visible. The
rest of the preservation set stays a byte comparison, because nothing legitimately appends to
`--help`.

---

## 12. Rollback story

The console is **additive**. Rolling it back is: delete `src/hacs/Console/`,
`src/hacs/Util/Rss.h` (if nothing else adopted it), `docs/console/`,
the `check_console_includes.sh` script, the `ConsoleCore` target and the binding sources in
`CMakeLists.txt`, the one branch in `kernel.cu`, and the registrations. No pipeline value depends
on it (the console calls the public API; `check_console_includes.sh` rule 2 proves the pipeline
does not call back). The only non-additive edits are the API gap closures of §14.2 — each a small,
independently revertible change (a public header for a file-local function; a lookup over an
existing `.inc`), each carrying its own regression case in an existing validation
(`ConsoleCliPreservationValidation` for G4, `GoldenRegressionValidation` for G13's re-routed
sweep), and each listed in the commit that lands it. **G5 is no longer one of them**: the one
FNV-1a-64 landed independently of the console, in the extension stage's slot 1, and
`CampaignSmokeValidation` plus the unchanged golden digests are its regression case.
**No engine substrate file changes**
(version 1's G2/G3 edits to `EngineConfig.h` / `CudaCtx.cpp` were phantoms; audit E7/E8).
`ENGINE_BACKEND`, `ENGINE_THREADS`, `ENGINE_DEVICE` and every other environment variable keep
working exactly as before for every non-console entry point; inside the console the environment
is the *initial* value of every setting (`settings()` shows `source: env` until `set` overrides it).

There is deliberately no `-DCONSOLE=OFF` option: a build-configuration axis costs a
`cross_config.sh` column forever, and the library is cheap (STL only, no CUDA).

---

## 13. Risk register

| # | Risk | Likelihood / impact | Mitigation |
|---|---|---|---|
| R1 | **A transcript silently runs under a different arm than it states** — the pool size is read once (`ThreadPool.cpp:49-52`); pass options and the cache bypass are process-global (`EngineRuntime.cpp:24-27`); settings are read when `compute()` *runs* | Certain if ignored / high | C4: only knobs with a verified in-process setter are settable, env-only knobs error; the session holds authoritative values (no guard stack); handles snapshot settings at creation; `ConsoleSettingsValidation` asserts each |
| R2 | **Dangling borrows** inside pipeline objects when a console user drops an intermediate (`HeckeOperatorOnK.h:280-282`, `HeckeTauTable.h:298-300`, `HeckeOperatorFamily.h:250-252`, `HeckeCrossChecks.h:167-169`) | High without C2 / crash or silent garbage | keep-alive edges are the rule, audited per borrow in §4.1; ASan run of the script set in `Check`; a script that binds nothing but the final object is in the set |
| R3 | **Output drift** breaking every `.expected` file when a printer changes | Medium / medium (re-baseline noise) | format version in every `.expected`; `ConsoleScriptEmit` owner-gated; each changed line explained, as for `GoldenEmit` |
| R4 | **Pipeline `std::cout` / `std::cerr` chatter** in transcripts (validations, `HeckeCrossChecks`, the decomposition `NOTE` `HeckeModuleDecomposition.cpp:725`, legacy `[TIMING]` lines, `LocalSystemSL2Z.cpp:425, 494, 540`) — timings and block-dependent text | Certain / breaks determinism | C5: both streams redirected around verb calls; `verbose` off in scripts; `capture()` for scripts that need the text; `ConsoleDeterminismValidation` under 1/4/16/32 threads |
| R5 | **Scope creep** into a general-purpose language (functions, closures, modules, exceptions) | High / medium | §3 is the whole language; `def` is reserved but unimplemented pending Q2; every addition needs an owner decision and a `ConsoleC0Validation` extension |
| R6 | **Process-global overrides leak** into in-session validations, benches and campaigns (E6) | Medium / high (a validation runs under a non-default arm and its result is misread) | those verbs run with the session overrides lifted by default (§5), restored afterwards; `ConsoleSettingsValidation` checks the restore |
| R7 | **Half-built objects and unclean global state after a throw** (program cache between compile and insert, device residency, non-atomic `PredicateStats`) | Medium / medium | the handle is `failed` and never retried; `ConsoleErrorValidation`'s post-throw integrity arm recomputes a golden object after an induced throw, on CPU and GPU |
| R8 | **Terminal left in raw mode** after a crash (only if C3 is commissioned) | Medium / annoying | `atexit` + signal handlers restore `termios`; `ConsoleLineReaderValidation` reads the state back |
| R9 | **`Matrix` deprecation** (`Matrix.h:111` `[[deprecated]]`): the bindings must touch `MatrixT` for `A^{(q)}` and the decomposition | Certain / cosmetic | bindings compile inside `cohomology_app`, which already carries `-Wno-deprecated-declarations` (`CMakeLists.txt:634-649`); the dual-representation `Matrix` (§2 C2) keeps the deprecated type out of every console-visible signature |
| R10 | **Golden coupling**: a console-pinned hash that is *not* on the golden grid silently freezes a bug | Medium / medium (`[ME §5 R12]`) | pins only at grid points, only through `golden(...)`; off-grid scripts assert identities, not hashes |
| R11 | **`SIGINT` cannot interrupt a running verb** (no cancellation point in the pool) | Certain / usability | documented; deferred flag; follow-up in §16.4 |
| R12 | **The extension engine changes core objects** (boundary cohomology, cones, `ι`, possibly a Manin-sized `H^1` substrate for `k ∼ 10^4`, `[I §1 Stage 7]`) that the console has already bound | High / low with the registry | additive: new types + new overloads; C5 is scheduled after the engine's API freeze; the language does not change; the `HeckeOperatorOnK` bindings remain the cross-check route |
| R13 | ~~Three FNV copies drift~~, or the per-kind encoding is applied to the wrong kind | Low / high | **Half closed (v3)**: the three copies are gone — one header, `src/ModArithmetic/Fnv.h`, since slot 1 WP-2, and C1 consumes it. What remains is the per-kind encoding: `hash()` is per kind by `TypeInfo`, `CampaignSmokeValidation` cross-pins golden and campaign, and on an ext-layer type the **settings fingerprint** joins the input (§2 C4) |
| R18 | **A pin frozen against a schema that is about to move** — `hecke_report/v2` (slot 2 E0b, 384 golden lines) is the live example; E2's `hecke_ext/v1` and E5's cone record are the next ones | Certain if unsequenced / high (a re-baseline of a pin is indistinguishable from a re-baseline of a bug) | v3's C1a/C1b split: nothing touching a decomposition or a report is written before E0b merges; C5 waits for E5's schema freeze; `ConsoleScriptEmit` is owner-gated and every changed line is explained |
| R19 | **A transcript pinned under a non-default mathematical setting** would be golden-looking and not golden | Medium / high | the fingerprint is part of `hash()` and is `0` only at the defaults (§2 C4 rule 1); `ConsoleScriptValidation` refuses a pin taken at a non-zero fingerprint (§11) |
| R14 | **64-bit objects reach 32-bit-only verbs** (`HeckeOperatorFamily`, `HeckeModuleDecomposition`, `HeckeCrossChecks`, `HeckeReport`) | Certain for `ell ≥ 2^32` / medium | typed refusal naming the gap (G6); `expect_error` script covers it |
| R15 | **`ProgramCache` has no cap** (`ProgramCache.h:53-63`): a long session accumulates compiled programs | Certain over a long session / medium | `clear_program_cache()`; `settings()` reports `program_cache_size`; documented |
| R16 | **`std::cerr` chatter** outside a `cout`-only redirect | Certain / breaks transcripts | both streams redirected (C5) |
| R17 | **The `rdbuf` swap is process-global** and races with concurrent writers | None today (single-threaded evaluator; campaign jobs write through the driver) / high if a `parallel_for` verb appears | on record: any future concurrent verb must give each task its own sink |
| R20 | **The frozen CLI captures go stale by legitimate growth** — a new `--bench` mode, a new `--campaign` key — and a package that re-captures by hand could hide a real regression in the same diff | Certain over the stage / medium | v3.2, from slot-4 WP-2 §3: a re-capture is **regenerated from the binary**, touches exactly the one file the addition changes, is authorised rather than taken, and its diff is quoted in the package report and shown to be **additive**. `--list` was already compared modulo appended names for the same reason; the other five captures stay byte-frozen |

---

## 14. Public API inventory and gaps

### 14.1 Callable today (the console's substrate)

| Area | Class / function | Header:line | Console use |
|---|---|---|---|
| Model | `CreateSL2ZFundamentalDomainTriangulation()` | `LocalSystemSL2Z.h:12` | `sl2z_model()` |
| | `CreateSL2ZOrbifoldFundamentalDomainTriangulation()` | `:14` | `sl2z_model(variant="orbifold")` |
| | `SL2ZTessellationTables(K)` | `Hecke/SL2ZTessellationTables.h:78` | inside `Model` |
| | `SL2Z7VertexModel()`, `FindModelDescriptor`, `RequireModel` | `Hecke/HeckeModelDescriptor.h:69, 74, 79` | `models()`, checks |
| | preset complexes | `SimplicialCohomology.h:233-243` | `sphere(n)` … |
| | `SimplicialComplex(simplices, name)` | `SimplicialCohomology.h:63` | `complex([[…]])` |
| | `CochainComplex` (trivial coefficients), `ConeComplex` | `SimplicialCohomology.h:129, 227` | `cochain_complex(K)`; the cone exists only here (`[I §1 Stage 0.3]`) |
| Local systems | `GenerateSL2ZRelationsWithGroupData(K, n, ell)` | `LocalSystemSL2Z.h:63-64` | `symmetric_power` (32-bit) |
| | `GenerateSL2ZRelationsElt<Elt>(K, n, ell)` | `:71-73` | `symmetric_power` (64-bit) |
| | `LocalSystemSimplicialComplexT` ctors 1/2/2b | `LocalSystemSimplicialComplex.h:59, 67, 76` | 2b (adopting) |
| | presets `CreateS1*`, `CreateCylinder*`, `CreateMoebius*` | `LocalSystemPresets.h:15-23` | `s1_scalar(...)` … |
| | morphism presets | `LocalSystemPresets.h:34-57` | `morphism_*` |
| Cohomology | `EquivariantCohomologyOnKT(lssc*)`, `compute_cohomology()` | `EquivariantCohomologyOnK.h:113, 123` | `cohomology(L)` |
| | `get_H_eq_dimensions()`, `is_cohomology_computed()` | `:173, 129` | `.dims`, state |
| | `*_block(q)`, `block_pool()` | `:148-159` | `.H(q)` etc. |
| | `get_*_bases_fm()`, projectors | `:167-171` | dense forms |
| | options: vacuous short-circuit, legacy path, retain intermediates (setters) | `:226, 246, 259` | settings |
| Hecke | `HeckeCosetTablesT(p, r, ell, n)` | `Hecke/HeckeCosetTables.h:116` | inside `hecke` |
| | `HeckeTauTableT(K, model, cosets, ell, n)` (certifying ctor) | `Hecke/HeckeTauTable.h:225` | inside `hecke`; `.tau` print `:283-284` |
| | `HeckeOperatorOnKT(coh*, cosets*, tau*)`, `compute()` | `Hecke/HeckeOperatorOnK.h:206-211` | `hecke(H, p)` |
| | `Theta_block`, `get_Theta_flat_matrices`, `get_Theta_eq_matrices`, `get_H_matrices` | `:217, 226, 227, 231` | members |
| | `certificates()`, `apply_route2`, `apply_Theta`, `to_json` | `:250, 258, 261, 267` | members |
| | options: legacy path, Θ_eq certification, memory-lean (setters) | `:363, 375, 406` | settings |
| | `HeckeOperatorFamily(...)`, `T_p`, `T_p_pow`, `T_p_pow_direct`, `T_p_pow_primitive_direct`, `T_n`, `T_pp`, `theta_flat_fm`, `prepare` | `Hecke/HeckeOperatorFamily.h:111, 120, 131, 173, 186, 195, 206, 230, 247` | `family(H)` |
| | `tau_construction_mutex()` | `:100` | taken around tau construction |
| | `HeckeModuleDecomposition(ops, ell)`, `compute`, `blocks`, `change_of_basis`, `conjugated`, `certify`, `to_json` | `Hecke/HeckeModuleDecomposition.h:157-183` | `decompose` |
| | `PrimaryBlock` fields | `:129-150` | `Block` |
| | `HeckeCrossChecks(...)`, `run_all`, (i)(ii)(iii) | `Hecke/HeckeCrossChecks.h:126-141` | `crosschecks` |
| | `HeckeReportInput`, `BuildHeckeReportJson`, `StreamHeckeReportJson`, `DefaultHeckeReportPath`, `WriteHeckeReport` | `Hecke/HeckeReport.h:88, 126, 132, 136, 141` | `report` |
| | `BarCocycleH1` (validation-only, `H^1`, `ℓ ≥ 5`) | `Hecke/BarCocycleH1.h:91, 104` | not bound; `[I G15]` may promote it |
| Polynomials | `FpPolyT` ctors, arithmetic, `eval`, `gcd`, `extgcd`, `powmod`, `frobenius_powmod`, `to_string` | `Hecke/FpPoly.h:57-105` | `Poly` |
| | `CharPolyBerkowitz`, `MinPolyKrylov`, `EvalPolyAtMatrix` | `:125, 129, 133` | `charpoly`, `minpoly`, `eval_at` |
| | `SquarefreeDecomposition`, `CertifyIrreducible`, `CertifyFactorization`, `FactorPoly` | `:159, 165, 170, 176` | `factor` |
| Matrices | `FlatMatrixT` ctors, `FromCanonical`, `CreateScalar`, shape, `get_entry`, `to_matrix`, `to_string` | `ModArithmetic/FlatMatrix.h:84-87, 93-95, 97, 110-112, 124, 130-131` | `Matrix` |
| | `MatrixT` (deprecated alias `Matrix`) | `ModArithmetic/Matrix.h:111` | the shared `A^{(q)}` representation |
| | `engine::elim` (RREF, kernel, image, `solve_multi_rhs`, complement) | `ModArithmetic/DenseElim.h` | §3.5 verbs |
| | `engine::BlockMat` / `BlockPool` / `blk::*` | `ModArithmetic/BlockMat.h`, `BlockKernels.h`, `BlockElim.h` | `Block*` values, `dense()` |
| Exact | `Mat22` generators, `operator*`, `reduced_mod` | `Hecke/ExactInt.h:74-78, 81, 101` | `mat22(...)` (optional) |
| Engine runtime | `set_consumer_pool_override`, `set_pass_options_override`, `set_program_cache_bypassed`, `run_concurrently`, thread-context capture | `Engine/EngineRuntime.h:67, 81, 101, 134, 125-126` | settings |
| | `PassOptions` fields / `from_env` | `Engine/Program.h:187-205`, `Passes.cpp:126-140` | settings |
| | `ThreadPool(n)`, `global()` | `Engine/ThreadPool.h:46, 57` | settings |
| | `ProgramCache::global().{clear,size,stats}()` | `Engine/ProgramCache.h:59-63` | `clear_program_cache()`, `settings()` |
| | `engine::elim::ScopedLegacy`, `legacy_forced`, `use_legacy` | `ModArithmetic/DenseElim.h:180, 198, 204` | `set backend` |
| Harness | `ValidationRegistry::{run, run_all, list, list_with_tiers, tier_of}` | `ValidationRegistry.h:62-79` | `run_validation`… |
| | ~~`bench::RunBench(argc, argv)`~~ → **`bench::RunMode(const ModeArgs&) -> BenchRecord`** (v3.6, P-3: G4 closed by C2b) | `Bench/BenchDriver.h:124` (`RunBench` `:154`) | `bench`, `micro` |
| | `ParseCampaignSpec`, `ParseCampaignSpecFile`, `plan_campaign`, `flatten` | `Campaign/CampaignSpec.h:371-372, 379, 382` (v3.6, P-4; were `:169-170, 177, 180`) | `campaign_spec`, `campaign_plan` (v3.5; was `plan`) |
| | `RunCampaignSpec`, `SingleJobSpec`, `JobOutputComplete`, `RunCampaign` | `Campaign/CampaignDriver.h:188, 199, 204, 208` (v3.6, P-4; were `:164, 169-170, 174, 178`) | `run_campaign`; `single_job` **deferred** (v3.5) |
| | `GoldenRegressionValidation`, `GoldenEmit`, `GoldenSubset32` | `Golden/GoldenHarness.h:38-39, 53-54` | `golden_subset` |

### 14.2 Gaps (each closed by a small change, each with a regression case)

| # | Gap | Evidence | Fix (phase) |
|---|---|---|---|
| G1 | No JSON string escaper anywhere: `HeckeReport.cpp` emits only literals and numbers | `HeckeReport.cpp:16-90` | the console's `Printer` owns JSON escaping for its own `json()` of records; `HeckeReport` untouched (C0) |
| ~~G2~~ | *withdrawn* — `cuda::requested_device()` / `device_enabled()` have no caller; the tape reads the device only from `PassOptions` | `CudaCtx.cpp:116-125`, `CudaCtx.h:50-51`, `Passes.cpp:133-139` | none (optional clean-up outside console scope: delete the dead pair) |
| ~~G3~~ | *withdrawn* — the three in-process legacy switches already reproduce `ENGINE_BACKEND=legacy` | `FlatMatrix.cpp:68, 1358, 1492, 1599` → `DenseElim.h:204`; `EquivariantCohomologyOnK.cpp:390`; `HeckeOperatorOnK.cpp:306` | none |
| ~~G4~~ | **CLOSED** (v3.6, P-3; C2b `fee4690`) — bench per-mode runners were file-local; only the argv entry was public | `BenchDriver.h:51` vs `BenchDriver.cpp:265, 299, 363, 424` | `bench::RunMode(const ModeArgs&) -> BenchRecord` public at `Bench/BenchDriver.h:124`; `--bench` output byte-identical (`bench_identity.sh`, 45 cases) |
| ~~G4b~~ | **CLOSED** (v3.6, P-3; C2b `fee4690`) — `PeakRssMiB()` / `ResetPeakRss` were file-local in the campaign driver | `CampaignDriver.cpp:299-316` | `Util/Rss.h` (`:47`, `:56`), used by bench, campaign and console |
| ~~G5~~ | **CLOSED** (v3) — the byte-wise FNV-1a-64 was defined three times | `GoldenHarness.cpp:76-81, 207-215`, `CampaignDriver.cpp:148-164`, `PerformanceSmokeValidation.cpp:86-90` | **`src/ModArithmetic/Fnv.h`** (`kFnvOffset64`, `FnvU64`, `FnvBytes`, `HashScalar64`, `FnvHasher`), landed by hecke-extensions slot 1 WP-2 with all three callers switched and the golden / campaign / determinism digests unchanged. **Not** `Util/Fnv.h`: `PerformanceSmokeValidation.cpp` is compiled into the `ModArithmetic` library (`CMakeLists.txt:195`), so `Util/` would be an upward include. C1 consumes the header and creates nothing. `Program.h:231-233` and `BlockPool.h`'s word-wise hash stay |
| G6 | `HeckeOperatorFamily`, `HeckeModuleDecomposition`, `HeckeCrossChecks`, `HeckeReport` are 32-bit only | `HeckeOperatorFamily.h:102`, `HeckeModuleDecomposition.h:152`, `HeckeCrossChecks.h:116`, `HeckeReport.h:88` | not closed by this plan; typed refusal (C1); `[I §1 Stage 0]` says the engine does not need it |
| G7 | `ell ∈ [2^63, 2^64)` unreachable from `Int` | §3.1 | none (no validated point uses it); documented |
| G8 | The cusp-restriction morphism exists only as `TestSL2Z_To_S1Cusp_RestrictionMorphism` | `LocalSystemSL2Z.h:117` | = `[I G3]` (`ComputeCuspRestriction`): C1 binds it if landed, else the extension engine |
| ~~G9~~ | **CLOSED** (v3.6, P-3; C2b `2855084`) — `IsDicksonExceptional` was file-local to a validation | `HeckeEndToEndValidation.cpp:98` | public: `hecke::IsDicksonExceptional`, `Hecke/DicksonCount.h:62`; `[ME §5 R8]` |
| G10 | No object has a *provenance* or a machine-readable `describe`; `to_string()` forms are ad hoc | `FlatMatrix.h:131-134`, `EquivariantCohomologyOnK.h:194-195`, `HeckeOperatorOnK.h:263-264`, `HeckeTauTable.h:283-284` | the console's `TypeInfo` supplies both without touching the classes (C1) |
| G11 | No cancellation point in the engine pool | `ThreadPool.h`, `EngineRuntime.h:134` | follow-up (§16.4), not in scope |
| G12 | The `--bench decomp` degree choice ("largest non-empty degree") is a driver policy, not an API | `BenchDriver.cpp:452-457` | the console makes `q` mandatory in `decompose`; no guessing |
| G13 | `GoldenReference.inc` has no **public** lookup API; it is only `#include`d by `GoldenHarness.cpp`, and slot 1's `GoldenLocalitySweep` carries an internal one | `GoldenHarness.cpp`; `GoldenHarness.h:90-95` | `GoldenLookup(point, object) -> const GoldenEntry*` in **`Golden/GoldenHarness.{h,cpp}`** (v3 — not `Util/GoldenLookup.h`: the `.inc` lives there and an upward include would be needed otherwise), with the slot-1 sweep re-routed through it, value-preserving. **One lookup, not two.** C1a; prerequisite of every pin |
| ~~G14~~ | **CLOSED** (v3.6, P-3; C2b `2855084`) — `SolveColumnsExact` and `PartitionFromNullities` were file-local to the decomposition | `HeckeModuleDecomposition.cpp:68-94, 180-204` | public in `Hecke/HeckeLinAlg.h` (`PartitionFromNullities` `:45`; `SolveColumnsExact` via `SubspaceOps.h`), reused by `restrict`, `solve`, `jordan_type` and later by `[I G5–G7]` |

### 14.3 What the extension engine will need from the console (from `[I G1–G17]`)

The inventory's dependency order for a first working engine is `G1 → G2 → G4 → G5 → G6 → G7 →
G8` on `H^0(Γ)`, `H^1(Γ)` over `F_ℓ`, then `G3 → G9 → G10 → G11 → G12` for the rest of `[M (3.1)]`.
For each, what the console must already offer (C1/C2) and what C5 adds:

| `[I]` gap | Console support in C1/C2 | C5 binding |
|---|---|---|
| G1 report text | nothing (a golden re-baseline; the console's `.expected` files that print the note re-emit under `ConsoleScriptEmit`). **It happened**: slot 2's E0b moved the schema to `hecke_report/v2` and corrected the multiplicity note, 384 golden lines — which is why C1b is scheduled after it (§10) | — |
| G2 identity checks | `check_identities(H, ops)` as a script over `H.dims`, `dickson_exceptional`, `A*B == B*A` (§3.5) | wraps `HeckeIdentityChecks` |
| G3 `r^0, r^1` | reserved `cusp_restriction(H)` (= G8 here) | `Morphism` members `.matrix(q)`, `.kernel(q)` → `H1_shriek` |
| G4 locality test | `algebra`, `radical`, `restrict` let a script *compute* `dim A_S/rad` on a block today | `is_local(block)`, `split(block)` |
| G5 local algebra | the §3.5 surface: `algebra`, `radical`, `tangent_space`, `socle`, `nilpotency_index` (C1 where no new substrate is needed) | `HeckeAlgebra` type replaces the script-level versions with certified ones |
| G6 certificates | `is_cyclic`, `commutant`, `in_span` + `family(H).T(p)` for the Sturm sweep | `certify_generation(alg, method = "cyclic" \| "commutant" \| "sturm")` |
| G7 module structure | `loewy`, `socle_series`, `jordan_type` | `LoewyProfile`, `active_directions` |
| G8 extension JSON + multi-operator campaign | `json(record)`, `report(D)`; campaign spec keys pass through `campaign_spec_text` untouched | `extension_report(...)`; new spec keys need no console change |
| G9 `ι` | reserved names | `iota(H)`, `sign_split` |
| G10 cone / `H^*_c` | reserved names | `compact_support(H)`, `long_exact_sequence(H)`; per OC-1 (decided 2026-09-16, [C] `open:ell2`, [OD §OC-1]) and the per-complex rule of `[E]` §7, the cone-cohomology object exposes **all four** degree members `.q_max`, `.truncated`, `.q_max_source`, `.degrees` beside `.h(q)` — `q_max` derived on a finite model, `q_max_source = "set"` only where `truncated` (E9) — and so do `Cohomology`, `BoundaryCohomology` and the pair complex, each its own (§3.6). The campaign's reported-degree list is a separate field and keeps its meaning |
| G11 boundary Hecke | reserved names | `hecke(boundary_cohomology(H), p)` overload |
| G12 canonical submodules | `intersect`, `contains`, `restrict` | `L_map`, `H1_shriek`, `dickson_classes` |
| G13 atlas | `bernoulli_mod` **bound** (v3.3, slot-5 WP-10; `glover_factors` with it), `run_campaign` | `Atlas` type, `atlas(ell)` |
| G14 `D_k` | reserved name | `divided_power(K, n, ell)` |
| G15 second model | `sl2z_model(name)` already takes a descriptor name (`HeckeModelDescriptor.h:74`) | `"gamma2"` descriptor |
| G16 Heilbronn `T_q` | `hecke(H, p, method = …)` keyword reserved | the overload |
| G17 native `F_{ℓ^r}` `Elt` | **not recommended** (`[I §4.3]`); the console's `GF(p, r)` is an `F_ℓ[X]/(π)` algebra on `FpPolyT`, never an `Elt` | `GF`, `GFElt`, `MatrixQ` on the small algebra layer only |

---

## 15. Implementation order: a split order

**What the audit changed.** Version 1 recommended "console first (C0–C2), then the engine".
The audit's counter-arguments (§5 there) hold on inspection of `[I]`: the engine's critical path
is **Stage 0** — boundary groups, `H^*_c` / the cone, `ι`, `T_q` on all six `X_i`, the second
model (`[I §1 Stage 0]`, all ✗) — which is C++ the console cannot prototype; `[S Stage 2]`'s
simultaneous refinement is already shipped (`ComputeMultiOp`, `[I §2.3]`), so scripting it buys
less than claimed; and `[S Stage 7]`'s `k ∼ 10^4` regime is out of the cochain model's reach
(`[I §1 Stage 7]`: ~140 GB extrapolated), so the engine may bind a *different* `H^1` substrate for
scale, leaving the `HeckeOperatorOnK` bindings as the cross-check route rather than the
foundation. What survives intact is the strongest argument: **scripts as the engine's test
format from day one**, which needs only C0 + C1.

**Recommended order.**

1. **Now, in parallel:** console **C0 + C1** (≈ 3.5 AU, the usable milestone, with the §3.5
   linear-algebra verbs that need no new substrate) and engine **Stage 0** (`[I G3, G9, G10,
   G11]`). They do not interact: C0 needs nothing from the pipeline, and C1 binds only shipped
   classes. **As executed** (v3): C0 landed in slot 1 of the extension stage, alongside E0a / E1s /
   E4a rather than a literal "Stage 0"; Lane C's slot 2 went to the four document revisions; C1a
   starts in slot 3, after E0b. The *split* the audit argued for held — the engine's critical path
   was never waiting on the console — but the console's own start slipped one slot behind the
   documents, which is the schedule table in §10 and owner confirmation 4 of `[S2]` §6.
2. **Then:** engine Stages 1–2 (`[I G2, G4]`) written with `.oc` scripts as their validation
   format; Stage 3–5 prototypes (`[I G5–G7]`) scripted on the §3.5 surface, with early partial C5
   bindings as Stage 0's objects land.
3. **C2** (settings, harness verbs, bench/campaign in-session) after that — it duplicates
   `--bench` / `--campaign` / `<Name>` for in-session use and has no substrate edit anything
   else waits on.
4. **C4** before C5 is declared closed; **C3** only on owner demand.

**For the record, the arguments both ways.** *Console first:* Stages 3–5 on `H^1` are exactly
`matrix → poly → factor → kernel → subspace` over `family(H).T(p)`, prototypable as scripts; the
shipped substrate is frozen by 66 validations (77 today); scripts give the engine its regression tests for
free; C0–C1 is small and front-loaded. *Engine first:* API stability (answered: only the
registry contract and value model are fixed now, both engine-agnostic); Stage 0 objects do not
exist (true — reserved names only); opportunity cost (answered by the split: C0–C1 runs in
parallel with Stage 0 and does not block it); feature creep (mitigated by the phase gates). The
split order keeps the engine's critical path unblocked, delivers the script-based test format
early, and defers ≈ 2.25 AU of console work (C2, C4) whose value is independent of the engine.

---

## 16. Appendix — open questions for the owner (plan-changing only)

| # | Question | Plan's default |
|---|---|---|
| Q1 | Should `./hacs` with **no arguments** open the REPL when stdin is a terminal? Today it runs the legacy benchmark verbatim (`kernel.cu:76-110`, "preserve the pre-existing default behaviour verbatim"). | **No** — keep it; require `--console`/`-i`. |
| Q2 | User-defined functions (`def f(a, b) { … }`) in the first release? | **No**; reserved keyword, grammar slot kept. Script parameters and `include` cover `[S Stage 9]` parametrisation. |
| Q3 | Commission the termios line editor (optional C3, 1 AU), or rely on `rlwrap`? | **`rlwrap`**; C3 stays specified and gated, unscheduled. |
| ~~Q4~~ | *withdrawn* (version 1 asked for runtime overrides of `backend_is_legacy()` and `requested_device()`; neither is needed — audit E7/E8, §2 C4). | — |
| Q5 | History file location (`~/.cohomology_history` vs cwd) — only relevant if C3 is commissioned. | `$OC_HISTORY`, else `~/.cohomology_history`; `--no-history` opts out. |
| Q6 | Are `.expected` files checked in per script (like `GoldenReference.inc`) and is `ConsoleScriptValidation` part of `--all` (fast tier)? | **Yes** and **yes**. |
| Q7 | Should the console's `Int` be arbitrary precision (hand-rolled bignum, ~600 lines)? The known need is `[S Stage 6.4]`'s `p \| num(B_w/w)` for `2 < w ≤ p−1`. | **No** — re-examined for v3 against `[X]` v1.5.1 and unchanged: `bernoulli_mod(w, p)` (§3.5) answers that test in `F_p` arithmetic, and E8's composite ring is `Z/ell^k` with `ell^k < 2^64`, i.e. still inside `uint32_t`/`uint64_t`, so the one phase that could have needed a bignum does not. `[WP3]`'s Sturm bound likewise forms its `q`-expansions mod `ell` as it goes and needs none. Revisit only if a phase needs integers beyond `int64_t` outside `F_p`. |
| Q7′ | *(v3.9.)* Does the digit route (`ell^k ≥ 2^64`, slot-11 WP-18c) change Q7's answer? | **No**: a residue beyond `int64` crosses the console as a **String** (`[E]` (g)'s residue form), and no console arithmetic needs it; the digit planes are engine words (`[C]` `obl:backend`(iv), its scope sentence). |
| Q9 | *(v3.9; open, the owner's.)* The console keeps the native route's `uint32_t` limit below `2^64` (`[E]` v1.12.0 `sec:ring`, the per-cell rule (i)), so it refuses `Z/5^k` for `14 ≤ k ≤ 27` and `Z/691^k` for `4 ≤ k ≤ 6` while serving `k ≥ 28` and `k ≥ 7` there by the digit route; the campaign serves every `k`. Close the gap — the console's `uint64_t` instantiation of the native pipeline, or the digit route below `2^64` at the console — or record it as intended? | **Open** (slot-11 WP-14 pass 2, m-4; WP-18c finding 3a). The plan takes no default; until the owner rules, the gap is the recorded behaviour and `ConsoleErrorValidation` pins it. *v3.9.3*: **Decided (a)** (owner, 2026-09-26): the console's `uint64_t` instantiation of the native pipeline, the campaign job loop's own route — built in slot-12 WP-17 (§3.6 "Wide handles"), pinned by `ConsoleErrorValidation` arm (Q9). (v3.9's "`ConsoleErrorValidation` pins it" was not so: no arm pinned the gap; WP-17 found none to change.) |
| Q8 | May `print_usage` (`--help`, `kernel.cu:60-72`) change at all to mention the console? | **No** — byte-identical; console usage via `--console --help`; `ConsoleCliPreservationValidation` freezes it. The cost is discoverability; the owner may relax it. |

### 16.4 Follow-ups recorded, not scheduled

* A `Pipeline` static library (re-homing the ~40 pipeline TUs out of the executable) — would let
  the bindings become part of `ConsoleCore`'s sibling library and shorten link times; no
  functional gain (§2 C8).
* A cooperative cancellation point in `run_concurrently` / the pool regions (R11, G11).
* Templating `HeckeOperatorFamily` / `HeckeModuleDecomposition` / `HeckeReport` on `Elt` (G6) —
  not needed by the engine (`[I §1 Stage 0]`).
* `history(x)` — the "minimal rebuild script" walker over the keep-alive graph (provenance
  through rebound loop variables is non-trivial; `--log` already gives replayability).
* A freshness gate `help --markdown == docs/console/console.md` as a validation. *(v3.6: the generator ships as `help_markdown()`, and `docs/console/gen_console_md.sh --check` is the gate's tool; the gate itself stays unscheduled.)*
* *(v3.7-pre.1.)* **The member-getter position wrap**, for the next authorised `Console/Core/`
  batch: `Evaluator::object_member` to wrap a C++ exception raised by a member getter as a method
  call's is wrapped, with the member access's `file:line:col` (§2 C7). One `try` / `catch`; exit
  codes are already right. `[WP9-12]` §4 item 1. *(v3.8-pre.1: **scheduled** — slot 10, WP-12, the "C5 leftovers" row of §10, under `[S10]` decision 6 (i) (A); with the type-level `resume` refusal as its second site, §2 C7.)* *(v3.8: **done** — slot-10 WP-12, `3c96d63`; §2 C7's as-built note.)*
* `--script` running a *transcript* (`--log` output) directly.
* Deleting the dead `cuda::requested_device()` / `device_enabled()` pair (`CudaCtx.cpp:116-125`).

---

## 17. Audit response (`docs/console/01-console-plan-audit.md`)

**v3 status of the audit.** All sixteen amendments were dispositioned in v2 and are now *built or
scheduled*, so the audit is **closed** except for the one item v2 contested. Its "overriding
concern" — that A1–A3 (the settings model, the absence of a guard stack, and lazy compute /
failure / settings capture) must land **before any `.expected` file is frozen** — is discharged
the way it asked: C0 shipped the settings layer with no RAII stack, the snapshot taken at
*creation*, and the `declared → computed | failed`-never-retried machine, and **no `.expected`
file exists yet** (`ConsoleC0Validation` asserts that none does). The contested item, A3(c)
"eager construction in script mode", stays **not adopted** for the reasons v2 gave; C0 shipped the
creation-site recording that solves the problem A3(c) aimed at, and nothing since has argued the
other way. Two amendments are re-pointed by v3: **A4**'s `Util/Fnv.h` is
`src/ModArithmetic/Fnv.h` (shipped) and its `Util/GoldenLookup.h` is
`Golden/GoldenHarness.h`; **A7**'s frozen `--list` is compared modulo appended names (§11), because
every slot of the extension stage registers validations.

Every amendment, its disposition, and where it landed. Factual errors E1–E12, contradictions
I1–I5 and the §1.4 offsets are all corrected in place (E1 → §1, §2 C1, §5, §14.1 re-derived from
the 184-line `CampaignSpec.h`; E2/E3 → §5, §14.1; E4 → §3.6 `cochain_complex`; E5 → §5
`single_job(spec, job, output)`; E6–E8, E12 → §2 C4; E9 → §2 C5, G5, R13; E10 → §2 C5, §3.4;
E11 → §2 C1, §6; I1 → C3/C8/§3.3–3.4/§9/C0; I2 → §2 C2 dual-representation `Matrix`; I3/I5 → §2 C2,
C7, §4.2, §8; I4 → C3, §9).

| # | Disposition | Where |
|---|---|---|
| A1 settings model | **ADOPTED** | §2 C4 (table rewritten; G2/G3 withdrawn; `set device` = `PassOptions` only; `set backend` = the three existing switches, supported from C2); §14.2; C2 acceptance (b) unconditional; Q4 withdrawn; R1 |
| A2 no RAII stack | **ADOPTED** | §2 C4 "The session model"; `ConsoleSettingsValidation` interleave arm (C2 (f), §11) |
| A3 lazy compute / failure / settings capture | **ADOPTED (a)(b)(d)(e); (c) CONTESTED** | (a) §2 C2 "Settings are captured at creation"; (b) §2 C2 "Failure is a bound state", §4.2, §8; (d) C4 acceptance (b), §11; (e) §2 C7 catch order. **(c) — eager construction in script mode — is not adopted**: it would make the same script behave differently under `--script f` and `--script f --console`, compute objects a script declares but never uses, and split the object model into two semantics. The problem (c) solves — an error that names the wrong line — is solved instead by recording the **creation site** in every handle and printing both the access site and the creation site (§2 C7, §8). |
| A4 `hash()` per kind + pin target | **ADOPTED**; re-pointed in v3 | §2 C5; G5 **closed** (`src/ModArithmetic/Fnv.h`, shipped), G13 (`GoldenLookup` in `Golden/GoldenHarness.h`, C1a), verb `golden(point, object)`; §6 pins as `dim_H^q` scalars; C1a acceptance (b), which v3 extends with "at the default mathematical configuration" |
| A5 flagship example + print order | **ADOPTED** | §2 C1 rewritten at `(10, 691)`; `n = 8` kept unpinned; §2 C5 / §3.4: text high → low, `coeffs`/`json`/`hash` low → high, no agreement claimed |
| A6 ConsoleCore contents | **ADOPTED**; refined by what C0 built | C3, C8, §3.3 vs §3.4, §9, C0 (b); `Fp`/`Poly`/`Matrix` are bindings; `Platform/` holds the editor; one `kernel.cu` branch calling two symbols. v3: the validation TU sits *outside* `Core/`, `ScriptRunner` is inside it and `ConsoleCli` is C1a, and `Core/` carries its own `CONSOLE_CHECK` |
| A7 CLI-preservation gate | **ADOPTED**; amended in v3 | `ConsoleCliPreservationValidation` (§11, C1a (c), C2 (e)); Q8 with default "no `--help` change"; §5 states the `-c`/`-i`/`-` meaning change explicitly; **`--list` modulo appended names**, since a byte-frozen `--list` would fail at the next registration by anyone |
| A8 automation surface | **ADOPTED** | (a) parameters §6; (b) `include` §3.2/§6; (c) `timed`, `bench_line` §2 C5/§5; (d) overrides lifted for in-session harness verbs §5, R6; (e) `rss()` documented §5 |
| A9 linear-algebra surface | **ADOPTED (extended)** | §3.5 enumerates every verb with its `[S]`/`[I]` consumer, including `bernoulli_mod` (Q7 resolved without a bignum) and G14 for the two file-local helpers; §14.3 maps `[I G1–G17]` to console support |
| A10 crosswalk + reserved names | **ADOPTED** | normative table at the top; `divided_power`, `L_map`, `sign_split`/`H_plus`/`H_minus`, `iota`, `H1_shriek`, `long_exact_sequence`, `method = "heilbronn"` in §3.6 |
| A11 descope the editor | **ADOPTED** | C6 rewritten; §7 keeps the design as optional C3; `ConsoleLineReaderValidation` marked optional in §11; `history(x)` and the docs gate moved to §16.4; Q3 default `rlwrap` |
| A12 ownership table | **ADOPTED** | §4.1 rewritten edge by edge (`HeckeTauTable.h:298-300`; `Decomposition` keeps sources + `q`; `Family` "logically immutable, internally caching" in §2 C2) |
| A13 re-estimate | **ADOPTED** | C2 → 1.5 AU; scheduled total ≈ 6.75–7.25 AU with C3 outside it; usable milestone ≈ 3.5 AU (C0 grew slightly with `include`/`args`/JSON escaping) |
| A14 decouple C5 from open mathematics | **ADOPTED** | C5 acceptance (a) = "runs to completion"; predicted outcomes are the engine's gate |
| A15 additional risks | **ADOPTED** | R15 (`ProgramCache` cap), R16 (`cerr`), R17 (`rdbuf` global) |
| A16 citation fixes | **ADOPTED** | throughout; two audit offsets re-checked against the tree and kept as the tree has them: `campaign.md:199` (the `n = 8` row; the audit says `:198`) and `GoldenHarness.cpp:207-215` (the constants start at `:207`) |
| Order (audit §5) | **ADOPTED** | §15 rewritten to the split order; the version-1 arguments are kept on record |

---

## 18. The served console — `hacs --serve`, protocol `oc-serve/1` (v3.10; specification only, slot-19 NB-1)

**Status: built (v3.10.1, NB-2; as-built record §18.14).** Built by slot-19 NB-2 (`--serve`, `PrintJson`, the `read_only` tags and
the two validations of §18.11), guarded by the CMake option `OC_BUILD_NOTEBOOK` (`OFF` for a plain
configure: nothing of this section is compiled, probed or required). Consumed by NB-3 (the stdlib-only
Python gateway and the page). Sources: `docs/implementation/slot18/WP-19d_notebook_design_note.md` §0
(owner decisions, 2026-10-03) and §2–§5, §7, §10; slot-19 plan v1.0, NB-1. **Normative for NB-2 and
NB-3; nothing of §1–§17 moves** (no verb, type, member, setting, exit code, canonical printer or `.expected`
transcript changes; `Console/Core/` is untouched — §18.3 explains why no exception is needed).

### 18.1 Scope, and what the owner fixed

1. The binary gains **one** CLI token, `--serve`. One process = one session = one `ConsoleCore` `Session`
   (§2 C4) driven by **newline-delimited JSON on stdio** (NDJSON, UTF-8, one object per `\n`-terminated
   line, no blank lines). stdout carries frames only; stderr is the process log and carries no protocol.
2. **LaTeX is rendered only in the notebook.** The binary emits structured JSON (`PrintJson`, §18.5, in
   `Console/Bindings/` and compiled only under `OC_BUILD_NOTEBOOK`); there is **no TeX printer** anywhere in
   the C++ tree. The page maps typed JSON to TeX; a type with no page renderer shows its `canonical` text.
3. The gateway (network exposure, source filter, token, process lifecycle) is **not part of the binary**
   and not specified here beyond what the binary must tell it (§18.2, §18.9, §18.10). The binary never opens
   a socket. The LAN rules of design note §0.1 (configurable bind, default loopback; private-source filter
   RFC 1918 / `fc00::/7` / `fe80::/10` / loopback; per-session random token ≥ 128 bit, constant-time
   compare; refuse to start on a public bind; no TLS in v1) are **gateway requirements** (NB-3); §18.12
   states them once so that NB-3's conformance list is complete.
4. **Read-only means** (design note §1): the session computes and displays; it writes no tracked file, no
   golden, census or campaign output, and cannot reach an owner-gated emitter (CLAUDE.md, "Owner-gated
   emitters and env interlocks"). It is a safety rail against accidents, **not a sandbox**: OC is a full
   language and a LAN peer holding the token is trusted (design note §4).
5. Opt-in/out: `OC_BUILD_NOTEBOOK=OFF` ⇒ `--serve` is an unknown token (exit 1, the usage text of §6);
   `ConsoleServeValidation` and `ConsoleReadOnlyTagValidation` print `[SKIP] <name>: OC_BUILD_NOTEBOOK=OFF`
   and return 0 (never a silent pass; counted like the `EFFECTIVE` lines). The `read_only` tag itself and
   the manual's tag column are **not** guarded (they are registry data, always built).

### 18.2 Launch, handshake, lifecycle

`hacs --serve [--set key=value]… [--rss-cap-mib N] [--max-reply-bytes N]`

* `--set` obeys §6 (exit 1 on refusal, 5 on a legal-but-unexecutable value) and is restricted to the
  *settable* keys of §18.8; `--rss-cap-mib` default **0 = off** (the gateway always passes one);
  `--max-reply-bytes` default 1 048 576 (the frame cap of §18.4). Every other CLI token (`--log`,
  `--script`, `-c`, `-`, `--console`, `--bench`, `--campaign`, `--atlas`, validation names, `<name=value>`
  parameters) together with `--serve` is **exit 1**. Nothing is read from a file at launch.
* **Environment gate** (§18.9) runs first. **Process hardening** (§18.9) runs second. Then the session is
  created with `verbose = false` (the §7 chatter switch: pipeline `cout`/`cerr` is captured into frames,
  never interleaved with the protocol) and the first frame is written:

```
{"kind":"hello","proto":"oc-serve/1","json_version":1,"oc_format":1,"console":"3.10",
 "build":{"commit":"<hex or unknown>","config":"RelWithDebInfo","cuda":false,"pid":123},
 "read_only":true,"counts":{"verbs":N,"overloads":M,"types":T},"limits":{"rss_cap_mib":R,"max_reply_bytes":B,"max_request_bytes":8388608,"confirm_wall_s":T},
 "settable":["print_max_entries","locality", …]}
```
  `proto` / `json_version` are the two version numbers of §18.4 / §18.5. `cuda` is the *effective*
  device state (`ENGINE_CUDA_DISABLE`). `build.pid` is volatile (excluded from every comparison).
* **Requests are processed strictly one at a time, in arrival order.** A reader thread reads stdin
  continuously: an `interrupt` is acted on at once, every other request is queued (the queue is bounded:
  64 requests; the 65th is answered `done` with `status:"rejected"`, `error.kind:"busy"`).
* **Session lifecycle.** `hello` → any number of requests → end. The session **never ends because of an
  error in a cell**; it ends on (a) stdin EOF (clean, exit 0), (b) a `close` request (reply
  `{"kind":"bye"}`, exit 0), (c) `SIGTERM` (finishes the current frame, exit 0), (d) a `fatal` frame (§18.10;
  exit 70), (e) being killed by the gateway. Bindings, handles, settings and the program cache persist
  across cells exactly as in the REPL (§7); there is **no** reset op in v1 (the gateway restarts the
  process — a fresh `hello` — and that is the only way to drop state).
* One session per process; the `rdbuf` swap is process-global (R17) and that is acceptable here.

### 18.3 Requests (`op`)

Every request is a JSON object with `op` and, except `interrupt` and `close`, an `id` (a client-chosen
string of 1–64 printable ASCII characters, unique among in-flight requests; the binary does not interpret
it). Unknown `op` or malformed JSON ⇒ `done` with `status:"rejected"`, `error.kind:"protocol"`, `exit:1`,
and the session continues (a line that is not parseable JSON has no `id`: the `done` carries `id:null`).

| `op` | fields | meaning |
|---|---|---|
| `eval` | `src` (string, ≤ 8 MiB), `args` (optional object name → literal), *(v3.15.0-pre.3)* `confirm` (optional list of at most 16 tokens, strings of 1–64 printable ASCII characters, from earlier `confirm_required` replies; §18.19; a malformed list is `rejected` / `protocol`, exit 1, nothing runs) | run `src` as **one program**: the whole text is parsed first (§6: a parse error runs nothing), then executed statement by statement in the session's global frame, as `include` would. `args` binds `args.name` for this cell only (literals as the CLI's `name=value` rule, §6); a missing `args.name` read is a runtime error as in a script. |
| `complete` | `prefix` (string) | reply `{"kind":"completions","id",…,"items":[{"text","kind":"verb"|"type"|"member"|"variable"|"setting","sig"?}]}` computed from the *filtered* registry (§18.8) and the session's variables; no evaluation, never forces a handle. |
| `help` | `topic` (string, a verb / type / setting name, or `""`) | reply `{"kind":"help","id",…,"topic","verbs":[…],"types":[…],"settings":[…]}` from the live registry (signatures, descriptions, members, the `read_only` flag); only served verbs appear. |
| `describe` | `name` (a bound variable) | `describe(x)` as data: `{"kind":"described","id",…,"value":<§18.5 envelope>,"state","created_at":{line,col},"members":[…]}`; never forces a handle. |
| `interrupt` | — (no `id`; applies to the running `eval`, if any) | §18.6. |
| `close` | — | end the session (§18.2). |

(`op:"atlas"` of the design note §2 is **not** part of `oc-serve/1`; the atlas browser path is NB-4 and got
its own `oc-serve-atlas/1` section, §18.16 (v3.11).)

`eval` is the only op that runs OC. The statements it may contain are the grammar of §3.2 **minus**
`include`, `quit`, and a bare `exit(...)` call (§18.8): a cell containing one is **rejected before any
statement runs** (`status:"rejected"`, `error.kind:"forbidden"`, `exit:1`, the position of the offender;
`include` is refused because it reads a file named by the request — the notebook has no file system
and gets shared definitions from its own cells).

### 18.4 Replies — frames

Every frame is a JSON object with a `kind` and, if it answers a request, that request's `id`; frames
carry a per-session monotone `seq` (integer, from 1; `hello` is `seq:0`). Key order is as listed here
(fixed, not sorted); no insignificant whitespace; nothing but `\n` between frames.

| `kind` | when | fields |
|---|---|---|
| `out` | statement output | `id`, `seq`, `stream` (`"stdout"` — what the REPL prints; `"log"` — captured pipeline chatter, normally empty because `verbose=false`), `text` (one or more complete lines, `\n`-terminated, each frame ≤ `max_reply_bytes`; a longer line is split with `cont:true` on all but the last piece) |
| `progress` | a `#~ ` line (the transcript-excluded annotation channel of §6, which includes `annotate(...)`, `bench_line` and `predictions = annotate`); *(v3.15.0-pre.3)* the heartbeat of a confirmed run (§18.19) | `id`, `seq`, `text` (the line **without** the `#~ ` prefix and without `\n`); a heartbeat adds `confirmed` (`{call, verb, model, wall_s, wall_hi, rss_mib, rss_hi, elapsed_s, resident_mib}`) |
| `value` | each expression statement whose result the REPL would echo, and (v3.14.0-pre.2) each argument of a `display(...)` call, after the call forced it | `id`, `seq`, `stmt` (0-based statement index in the cell), `line`, `col` (of the statement; for `display`, of the call), `value` (§18.5 envelope) |
| `done` | **exactly once per request**, last frame of that request | `id`, `seq`, `status` (`"ok" \| "error" \| "interrupted" \| "rejected"`, *(v3.15.0-pre.3)* `\| "confirm_required"`), `exit` (§18.7), `error` (null or §18.7 object), *(v3.15.0-pre.3, only with `confirm_required`)* `confirm` (§18.19), `statements` (number executed), `perf` (`{"elapsed_ms":int,"rss_mib":int,"peak_rss_mib":int}`, volatile) |
| `completions`, `help`, `described` | replies to `complete`, `help`, `describe`; each followed by its `done` |
| `bye` | reply to `close` | `seq` |
| `fatal` | the process is about to exit (§18.10) | `reason`, `detail`, `seq`; last frame |

* `out` text, concatenated in `seq` order over one `eval`, **is** the REPL's stdout for that cell: the
  ConsoleDet-pinned canonical printer is not touched, and `ConsoleServeValidation` compares it byte for
  byte with the transcript (§18.11 (B)). `progress` lines are exactly the lines that every transcript
  comparison already ignores (`#~ `), so splitting them off changes nothing.
* **Frame cap.** No frame exceeds `max_reply_bytes` (default 1 MiB, design note §6). `out` is split at
  line boundaries as above. A `value` whose envelope would exceed the cap is replaced by its **truncated
  form** (§18.5): the cap never makes a frame invalid, and the full value stays reachable through the
  session (`show(x)`, `hash(x)`, member access).
* **Back-pressure.** The binary blocks on a full stdout pipe; it never drops a frame.
* Frames of different requests never interleave (one `eval` at a time); `progress`/`out`/`value` frames of a
  cell appear in program order.

### 18.5 `PrintJson` — the value envelope (`json_version` 1)

**Envelope.** Every value is rendered as an object

```
{"t":"<TypeName>","canonical":"<PrintCanonical text>","hash":"0x…"|null,"v":<per-type tree>}
```
* `t` is the registered type name (`Int`, `Bool`, `String`, `Nil`, `List`, `Record`, or one of the 30 of the
  manual's type table), exactly `type(x)`.
* `canonical` is the §4.3 **canonical** rendering (what `show` / `repr` print; the display rendering is not
  offered). For a value larger than `print_max_entries` it is the *summary form*, as in the REPL (§4.3); the
  envelope then carries `"truncated":true` and `v` is a **shape-only** tree (dimensions, counts, no entries).
* `hash` is `hash(x)`'s text (the golden-identical FNV of the per-kind rule, §2 C5), or `null` where the
  kind has no hash (never a made-up value).
* **Order of keys** in the envelope: `t`, `canonical`, `hash`, `v`, then, when present, `truncated`,
  `length`, `generic`, `state`, `hint` (v3.14.0-pre.1). Within `v` the order is the table's order below.
* **No TeX** appears in any field. **No float** is ever produced (the console has no float type; a
  `timed()` record's decimal fields are the canonical printer's `String`s and stay Strings).
* **Integers.** An integer is a JSON number when `|x| ≤ 2^53 − 1` and a decimal **String** otherwise (the
  console's `Int` is 64-bit; the wide band's entries `> 2^63` are already Strings, §3.6 v3.9.3). A schema
  field of type *int\** below means "number or decimal string"; a consumer must accept both. Residues are
  canonical (`[0, p)`, §4.3).
* **Order labels, never silent.** `Poly` carries `"order":"low_to_high"` on its coefficient list — the
  machine order of `coeffs` / `json`, §2 C5 — while its `canonical` text is HIGH → LOW; the page is
  responsible for presenting the mathematically conventional form, the binary never unifies the two.
* **Handles** (every lazily computed type: `LocalSystem`, `Cohomology`, `HeckeOperator`, `Family`, …):
  rendering **never forces** a `declared` handle (same rule as the canonical printer, §4.3 / §2 C2);
  `state` is `"declared" | "computed" | "failed"` (§4.2) and `v` then holds only the *structural* members the
  creation already fixed; for `computed` handles `v` additionally holds the **computed members that §3.6's
  canonical form already shows** (so the JSON never costs more than the text).
* **Determinism.** Same value ⇒ byte-identical JSON in every run, thread count, device and program-cache
  state (the same axes as ConsoleDet, §11); the volatile exceptions are exactly the `perf` / `build.pid`
  fields of §18.4 and the `wall_*` / `*_rss_*` / `alloc*` members of `timed()` and `rss()` records
  (named `volatile` in the table; `ConsoleServeValidation` excludes only these).
* **Evolution.** `json_version` bumps when a field's meaning or type changes or a field is removed; adding
  a field at the *end* of a `v` object is allowed within a version. Consumers ignore unknown fields. A
  type that has no dedicated schema yet is rendered by the **generic form** `{"t","canonical","hash","v":
  {"members":{<name>:<envelope>,…}},"generic":true,"state"}`, where `members` are the structural members of
  the manual's member table (not the computed ones unless the handle is `computed`). NB-2 ships a dedicated
  schema for every row of the table below marked **D**; the others (**G**) use the generic form in
  `json_version` 1 and acquire dedicated schemas additively. Completeness is gated (§18.11 (E)).

| Type | Form | `v` (in order) |
|---|---|---|
| `Nil` | D | `null` |
| `Bool` | D | `true` / `false` |
| `Int` | D | *int\** |
| `String` | D | the string (JSON-escaped; `canonical` carries the quoted form) |
| `List` | D | `[<envelope>,…]` (elements are full envelopes; beyond `print_max_entries` elements: `truncated`, `"length":int`, first `print_max_entries` elements only) |
| `Record` | D | `[[<key>,<envelope>],…]` — **an array of pairs**, keys in the record's order (a JSON object would not preserve it for every consumer) |
| `Fp` | D | `{"p":*int*,"value":*int*}` |
| `Poly` | D | `{"ell":*int*,"deg":int,"order":"low_to_high","coeffs":[*int*,…]}` (zero polynomial: `deg:-1`, `coeffs:[]`) |
| `Matrix` | D | `{"rows":int,"cols":int,"p":*int*,"entries":[[*int*,…],…]}` row-major, all rows present up to `print_max_entries` entries, else `entries` omitted and `truncated:true` |
| `Model` | D | `{"name":str,"dims":[int,…],"vertices":int}` |
| `Complex` | D | `{"name":str,"dim":int,"euler":int,"dims":[int,…],"simplices":[[[int,…],…],…]}` (`simplices[q]` = the q-simplices; omitted above the cap) |
| `LocalSystem` | D | `{"n":int,"p":*int*,"d_V":int,"coefficient_ring":str}` (+ `"relations":int` when computed) |
| `Cohomology` | D | `{"ell":*int*,"d_V":int,"coefficient_ring":str}` structural; computed adds `"dims":[int,…]`, `"degrees":[int,…]`, `"q_max":int`, `"truncated":false`, and over `Z/ell^k` `"lengths":[int,int,int]`, `"ladic_type_certified":bool` |
| `GF` | D | `{"ell":*int*,"r":int,"polynomial":{<Poly v>}}` |
| `GFElt` | D | `{"ell":*int*,"r":int,"coeffs":[*int*,…],"order":"low_to_high"}` (coefficients of the representative in the powers of `Y`) |
| `Block` | D | `{"json": <the existing .json text parsed as a tree>}` — **no re-encoding of a report the engine already emits** |
| `Decomposition` | D | `{"q":int,"blocks":int,"json":<existing .json tree>}` (design note §3: "Block/Decomposition → existing `.json`") |
| `Report` | D | `{"schema":"hecke_report/v2","json":<the record>}` |
| `ExtRecord` | D | `{"schema":"hecke_ext/v5","json":<the record>}` |
| `Settings` | D | `{"entries":[[<key>,<envelope>],…],"fingerprint":"0x…"}` |
| `HeckeOperator`, `Pairing`, `MaximalIdeal`, `HeckeAlgebra`, `LoewyProfile`, `ExtensionClass`, `BoundaryCohomology`, `ConeCohomology`, `DicksonLES`, `DescentRecord` | D-m | (v3.14.0-pre.1) the **member form**: `{"members":{<name>:<envelope>,…},"calls":[[<method>,[<arg>],<envelope>],…]}` — `members` exactly as in the generic form (never forcing), `calls` the per-type method calls below, each made only where the method may be read (no call on a declared handle for a computed method), at most 16 per object: `HeckeOperator` `A(q)` for every degree of `dims` (and `charpoly(A)` beside it for a field Matrix with ≤ 64 rows, through the `charpoly` verb); `Pairing` `perfect(t)`, t = 0 .. 2; `MaximalIdeal` `character(p)` and `t(p)` for p in `operator_primes`; `LoewyProfile` `jordan(p)` for p in `primes`; `ExtensionClass` `matrix(p)` for p in `active`; the others none. No `generic` flag. |
| `Involution`, `Family`, `ContragredientLocalSystem`, `CampaignSpec`, `Sturm`, `Atlas`, `Presentation` | G | generic form (promoted to **D** / **D-m** additively when the page needs a renderer) |

**Render hints** (v3.14.0-pre.1, `hint`). A List of `Int` (or of decimal `String`s) often IS a polynomial, a
q-series or a group, which its type cannot say. The twin tables `Console/serve/render_hints.tsv` and
`PrintJson.cpp`'s `kHintRows` (checked row for row by `ConsoleReadOnlyTagValidation` arm (H)) give, per
*(Record `schema` or type name, path)*, a `kind` and attributes; the envelope at that path then carries
`"hint":{"kind":…,…}` after `state`. Paths: `.` between keys / member names, `[]` every List element, `*`
any Record key, `m()` the calls of a D-m object. Kinds: `poly` (`order` = `low_to_high` | `high_to_low`,
checked per verb — the descent's `char_Z` is high → low, every other one low → high; `var`; `ring` =
`F_ell` | `Z/ell^k` | `Z` with `ell` and `k` resolved from the enclosing Records' or the object's `Int`
fields, left out when not resolvable), `qexp` (a_0, a_1, …; `ring`), `abgroup` (`{free_rank, torsion:
[[p, k, mult], …]}` = Z^free_rank ⊕ ⊕ (Z/p^k)^mult), `hilbert`, `layers` (`units`), `partition` (a Jordan
type; `units`). A hint never changes `v` or `canonical`; a consumer that ignores it loses nothing. The
rows of record: `level_n/v1`, `nebentypus/v1`, `forms_algebra/v1` `ops[].charpoly` (and `basis[]` as
`qexp`), `hida_lambda/v1` `ops[].charpoly` (ring `Z/ell^W`), `hida_tower/v1` `levels[].charpoly.*` /
`levels[].free_charpoly.*` (ring `Z/ell^e`), `kummer_unit/v1` `coefficients` (in ζ_ell, over Z),
`lfunction/v1` `coefficients` (in T, ring `Z/ell^R`), `DescentRecord` `groups_inv[]`, `pair_inv.*[]`,
`charpoly[].coefficients`, `HeckeOperator` `charpoly_free.coeffs`, `HeckeAlgebra` `hilbert`,
`LoewyProfile` `loewy`, `socle`, `jordan()`.
(v3.14.0-pre.2) Three more kinds: `cyclic` (the exponents e_i of ⊕_i Z/ell^{e_i}; `ell`), `eigen` (a
character value P_p(w), a `Poly`, in the residue field F_ell[w]/(π_w) ≅ F_{ell^f}; `var`, `f`) and `lesmap`
(a `Matrix` that is one map of the Dickson long exact sequence; `map` ∈ {`theta0`, `pi0`, `delta`,
`theta1`, `pi1`}, `n`, `n_up`). An attribute written `key=@name` is the `Int` field or member `name`,
resolved like the ring parameters (left out when not resolvable). A `nil` at a hinted path (an optional
field left out) carries no hint. Rows: `hecke_ring_algebra/v1` `blocks[].torsion` (`cyclic`),
`blocks[].A1_hilbert`, `blocks[].AK_hilbert` (`hilbert`); `MaximalIdeal` `character()` (`eigen`);
`DicksonLES` `maps.theta0`, `maps.pi0`, `maps.delta`, `maps.theta1`, `maps.pi1` (`lesmap`).
(v3.14.0-pre.3) The kind `factored`: a product of polynomials with multiplicities, a `List` of Records
`{coefficients, multiplicity, ...}` (`order`, `var`, `ring`); row `DescentRecord` `charpoly_factored[].factors`
(char_Z(T_p) factored over Z).

**Coverage** (v3.14.0-pre.2). `Console/serve/render_coverage.tsv` has one row per core kind, per
registered type and per Record `schema` set in the verb sources (`HeckeExt/`, `Console/Bindings/`,
`Integral/`), saying how the page renders it: `tex` (a `toTeXRaw` case of `notebook/page/render.js`),
`hint` (at least one row of `render_hints.tsv`), `table` (the Record / List structure) or `allow` (the
canonical text, an explicit decision; the reason column says why). `ConsoleReadOnlyTagValidation` arm (R)
checks both directions: every kind, type and literal schema site has a row and every row names one; a
non-literal schema site needs a schema row too (counted); every `toTeXRaw` case of a type is marked
`tex`; every hinted name is marked `hint`; every hint kind has a `hintTeX` case. A new type or schema
therefore fails until its rendering is decided.

`Cohomology` over `Z/ell^k` (v3.14.0-pre.1) appends `"invariant_factors":[[e_1,…],…]` (per degree, the
exponents of `.invariant_factors(q)`), when readable.

The envelope of a value inside a `Record` or `List` is the full envelope (the recursion is the whole
design: the page can render any value by walking `t`). The `json(x)` **verb** of §4.3 is unchanged, and
is a separate, older feature; `PrintJson` is not callable from OC.

**`display` and the page's actions** (v3.14.0-pre.2). A served `display(x, ...)` sends what the bare
statement `x` would, per argument, after forcing; its frames point at the call. The page uses the frame's
`line` / `col` and the cell's source to recover the statement (`OCRender.stmtSource`, up to the first
`;`, newline or `#` outside brackets and strings; `display(e)` unwraps to `e`). A **declared** value gets
a *compute* button that evaluates `display(<statement>)` beside it (an identifier forces the same handle;
an expression is re-evaluated). A **shape-only** `Matrix` (over `print_max_entries`) gets a *show all*
button when its size is at most 100 000 entries: the page reads `settings().print_max_entries.value`,
evaluates `set print_max_entries = <rows·cols>; display(<statement>)`, and then sets the old value back,
whatever the status. Both are ordinary `eval` requests; nothing new crosses the protocol.

### 18.6 Interrupt and resource guard (cooperative)

* `{"op":"interrupt"}` sets a session-wide atomic flag. It is checked **at every statement boundary** and at
  the existing budget / `ResumableState` points (§7; `resume`). *(v3.15.0-pre.5, NBCONFIRM S5)* It also raises the
  evaluator's cancel request (§7.2), so a verb already running stops at its **next cancellation point** — inside the
  long verbs: per Hecke prime, torsion prime, level, stage — with the same `done` as below; the interrupted statement's own binding is not made (earlier effects stay, as with any error) and
  a lazy handle it was computing stays `declared`. SIGTERM does the same. A step with no point inside (one engine kernel, a
  driver verb) still finishes first, so the gateway must still expect latency and, when it is not acceptable, **kill the
  process** (state lost; the documented hard cancel, design note §3; the page's "Kill session").
* On acting on the flag the cell stops: `done` with `status:"interrupted"`, `exit:3`, `error.kind:"interrupted"`;
  the session continues; bindings made before the stop persist; a handle that was being computed in a
  cut-off budgeted verb is left resumable (§4.2).
* An `interrupt` with no running `eval` is ignored (no frame). The flag is cleared at the start of each `eval`.
* The per-cell **CPU-time limit** and wall clock are the gateway's (kill); the binary has none.
* *(v3.15.0-pre.3, NBCONFIRM S4)* **Heartbeat.** While a confirmed run (§18.19) is in progress the binary sends a
  `progress` frame with a `confirmed` member at its start and then every 10 s (a thread of its own; it is disarmed before
  the cell's `done`, so no heartbeat follows it). *(v3.15.0-pre.4, audit N2)* Ordering: only the **start** frame flushes the
  cell's pending `out` text first; a periodic frame comes from the heartbeat thread and may precede `out` text the call
  printed before it (presentation only; the frame stream of a cell without a confirmed run is unchanged). The interrupt stays cooperative, so a confirmed verb that is already
  running finishes first; the page therefore offers **"Kill session"** (the gateway's `restart`) when no `done` arrives
  within 10 s of an Interrupt, and says that every binding of the session is lost.

### 18.7 Errors and exit codes as structured replies

The session **keeps running** after every outcome below (as the REPL, §7: "in the REPL every error leaves
the session usable"). A cell stops at its first error; statements after it do not run; earlier effects stay.

| §6 / §8 exit | `done.status` | `done.exit` | `error.kind` | produced by |
|---|---|---|---|---|
| 0 | `ok` | 0 | — | the cell ran to its end |
| 1 | `rejected` | 1 | `forbidden` (static: `include` / `quit` / `exit` statement, or a verb name with **no** read-only overload; nothing ran), `protocol` (bad JSON / op / field), `busy` | request-level refusal — "usage" in the §6 sense; nothing from the cell executed |
| 2 | `error` | 2 | `parse` | `console::ParseError` (the whole cell is parsed first; nothing ran) |
| 3 | `error` | 3 | `runtime` (any C7 row: `ENGINE_CHECK`, contract violation, `HeckeOverflow`, `bad_alloc`, lazy failure), `type` (`console::TypeError`), `forbidden_overload` (dynamic: the *resolved overload* is not read-only, or `set` of a non-settable key, §18.8; nothing of that call ran), `interrupted` | the C7 error model |
| 4 | `error` | 4 | `assertion` | `console::AssertionFailure` (`assert`; an `expect_error` whose body did not fail) |
| 5 | `error` | 5 | `not_implemented` | `hecke::NotImplementedInThisBuild` (token `not_implemented_in_this_build:`) |

`done.error` is `null` for `ok`, else
`{"kind":"…","message":"<the C7 message, verbatim, first line>","detail":"<remaining lines, the creation-site and caused-by lines of §2 C7, or \"\">","at":{"line":int,"col":int}|null,"created_at":{"line":int,"col":int}|null,"verb":"<name>"|null}`.
Positions are 1-based **within the cell's `src`** (the served pseudo-file is named `<cell>` in the verbatim
message text, so `<cell>:14:7: error: …` replaces `script.oc:14:7: error: …`; nothing else in the message differs).
A failed handle is bound `failed` and rethrown on every later access, never retried — unchanged (§8).
There is **no** exit code 6; `interrupted` is exit 3 with its own `kind`; the process's own exit status is
0 / 1 (launch refusal, §18.2) / 70 (`fatal`, §18.10).

### 18.8 The `read_only` tag

**Semantics.** Every registered verb **overload** (the manual's table lists 154 verbs / 166 overloads at
the slot-18 close) carries a boolean `read_only`, stored in the verb registry beside the signature
(single source of truth; `Console/Core` is not touched: the tag is a field the binding registers through
the registry's existing metadata seam, §2 C3, and an untagged registration means `false` — **a new verb is
excluded until audited**). *Tagged* means: the overload performs **pure computation on in-memory objects
and session state**; it opens no file for reading by a name the request supplies or for writing at all,
writes no file, reads no environment variable it did not already read at process start, spawns no process,
runs no validation, benchmark or campaign, and reaches no emitter. Filtering is **by registry tag at
dispatch**, never by string match on the source.

**Served view.** `--serve` dispatches only tagged overloads. `verbs()`, `help`, `complete` and the
`counts.verbs` of `hello` show the **served view** only; an untagged overload is invisible there and
refused if called (§18.7: `forbidden` when no overload of the name is tagged — checked statically at parse
time over every call's callee name — and `forbidden_overload` when the resolved overload is not). The
gateway independently enforces the same list from the JSON table twin of design note §5 (a 20th generated
artefact, `read_only_verbs.json`, emitted beside the manual tables and gated by
`CliManualCoverageValidation` — NB-2 + NB-3); the binary's check is authoritative.

**Manual.** The generated verb table (`docs/latex/cli_manual/verbs.tex`) shows the tag as a column, one
mark per overload, and `counts.tex` gains `\CMNumReadOnly` / `\CMNumReadOnlyVerbs`; regenerated in NB-2's
commit (`gen_cli_manual_tables.sh`; a registered verb, type, setting or CLI token without a regeneration fails
`CliManualCoverageValidation`, CLAUDE.md). The new CLI token `--serve` and the `oc-serve/1` summary page of
the manual (a short chapter) are part of NB-2's manual commit.

**Which overloads are tagged — specification (from the registry as of the slot-18 close; NB-2 audits each
against the definition above and may only *remove* a tag on evidence, any addition needs a [P] amendment).**

| Group (manual) | **Tagged** | **Not tagged** (reason) |
|---|---|---|
| core | `print`, `show`, `describe`, `str`, `repr`, `json`, `annotate`, `len`, `keys`, `range` (both), `abs`, `min`, `max`, `type`, `assert` (both), `vars`, `verbs`, `types`, `settings`, `reset_settings`, `script_args`, `compute`, `state`, `resume` (both), `display` (v3.14.0-pre.2) | `exit` (both) — ends the process; session end is `close` (§18.2) |
| arithmetic | **all 47 overloads** (`Fp` … `eval_at`: pure arithmetic and linear algebra; `random_*` take a mandatory seed) | — |
| pipeline | all but one: `sl2z_model` (both), `models`, the presets, `complex`, `symmetric_power`, `cohomology`, `dickson_*`, `hecke` (both), `family`, `dual`, `pairing`, `decompose`, `crosschecks`, `*_scalar`, `*_unipotent` | `report` — its single registered signature carries `path`, a file writer; a read-only split into a pathless overload is a NB-2 option (then tagged) |
| reproducibility | `hash`, `hash_int`, `golden`, `golden_has`, `golden_size`, `fingerprint`, `math_settings`, `save_state(x)` | `save_state(x, path)` — writes a file |
| harness | `validations` (both: lists names), `bench_line` (both), `rss`, `timed`, `golden_subset`, `campaign_spec_text`, `campaign_plan` | `run_validation` (runs the suite's emitter-capable code in process), `bench`, `micro` (timing runs, process-global state), `campaign_spec` (reads a file by request-supplied name), `run_campaign` (writes `output`) |
| reference | `help_markdown` | — |
| extension | all (`sturm_bound`, `u_ell_decision`, `bernoulli_mod`, `glover_factors`, `canonical_field_polynomial`, `nilpotent_part`, `radical`, `tangent_space`, `socle`, …, `check_identities`, `L_map`, `ext_record`, `local_algebra`, `module_structure`, `presentation`, `atlas(ell)`, `GF`, `gf_*`, `settings_snapshot`, `iota`, `boundary`, `cone`, `dickson_les`, `hecke_ring_algebra`, `theta`) — in-process objects only; `atlas(ell)` is the in-process `ell ∈ {5,7,11,13}` constructor, **not** the Σ(691) store | — |
| statements | `set` (for the *settable* keys below), `for`, `if`, assignment, `expect_error`, `help`, `?x` | `include` (file read), `quit` (process end), `set` of a non-settable key |

Totals to be recorded by NB-2 in the report and pinned by the fixture of §18.11 (D): the expected tagged /
untagged overload counts are **157 / 9** at the slot-18 close registry (untagged: `exit` ×2, `report`,
`save_state` 2-arg, `run_validation`, `bench`, `micro`, `campaign_spec`, `run_campaign` — a count the
validation recomputes, so the figure here is a forecast, not a pin: **if the audit moves it, NB-2 amends this
table in the same commit**).

**Settable keys** (`set` statement and `--serve --set`): `print_max_entries`, `lean`, `program_cache`, *(v3.15.0-pre.3)*
`confirm_wall_s` (the threshold T of §7.1; policy only, never a value; **`confirm` itself is not settable**: in a served
session every expensive call goes through its per-cell token, §18.19), and the
eleven *mathematical* settings (`locality`, `u_ell`, `sturm`, `sturm_unavailable`, `commutant_budget`,
`final_mode`, `field_polynomial`, `split_field_report`, `presentation`, `predictions`, `coefficient_ring`;
they change the record's hash input, CLAUDE.md "Two families of switches" — the served session shows that
in `settings()` and `describe` exactly as the REPL does). **Not settable**: `verbose` (forced `false`),
`threads`, `backend`, `device`, `batch`, `ksplit`, `arena`, `cse`, `fuse`, `layout` (process-global engine
knobs, owned by the gateway through its env whitelist) and every env-only key (`host_threads`, `tile_*`,
`spin`, `elim_base`, `cuda_*`, `trace_*` — they cannot be `set` in any mode, §2 C4). None of the `ENGINE_*`
variables can change a value; the mathematical settings may, and **only their defaults are golden**.

### 18.9 Environment scrubbing and process hardening

The gateway builds the child's environment from a **fixed whitelist**; the binary independently verifies it.

* **Whitelist** (gateway sets; the binary accepts): `ENGINE_THREADS`, `ENGINE_CUDA_DISABLE`,
  `ENGINE_CUDA_DEVICE`, `ENGINE_HOST_THREADS`, and the inert process variables `PATH`, `HOME`, `LANG`,
  `LC_ALL`, `TMPDIR`. The notebook offers **no environment editor**; CLAUDE.md's rule — never set an env
  hook to make something pass — binds the gateway as it binds an agent.
* **Gate (binary, first act of `--serve`).** If the environment contains any variable that is **not** on
  the whitelist **and** matches one of `GOLDEN_*`, `CONSOLE_*`, `CLI_MANUAL_*`, `HECKE_*`, `ENGINE_*`
  (other than the four above), `OC_*`, `ASAN_OPTIONS`, `UBSAN_OPTIONS`, `TSAN_OPTIONS`, the binary writes
  **nothing to stdout**, prints `serve: refused: environment variable <NAME> is not permitted in a served
  session` to stderr and exits **1**. It does **not** unset-and-continue: a silently ignored hook is the
  vacuous-arm lesson (the `EFFECTIVE` convention) turned inside out. The names the owner-gated emitters and
  hooks use (`GOLDEN_EMIT`, `GOLDEN_OUT`, `GOLDEN_DUMP`, `CONSOLE_EMIT_EXPECTED`, `HECKE_DUMP_TAU`,
  `HECKE_DUMP_SAT_CERT`, `HECKE_DUMP_SAT_CERT_CELLS`, `CLI_MANUAL_EMIT`, `GOLDEN_STRICT`,
  `HECKE_LOCALITY_PROBE`, `HECKE_HIDA_HEAVY`, `HECKE_HIDA_HEAVY_CELLS`, every `HECKE_*_ALL` / `_CELLS` /
  `_U_ELL` / `_RECORDS` / `_JOIN_ONLY`, `HECKE_NEBENTYPUS_*`, `HECKE_SAT_DEFECT_*`, `HECKE_LEVEL_N_*`, the
  rollback arms `HECKE_U_ELL_LOW_RANK`, `HECKE_COSET_STREAM`, `HECKE_PARALLEL_SETUP`,
  `HECKE_RANK1_CLOSED_FORM`, `ENGINE_LADIC_WIDTH`, `ENGINE_BACKEND`, `ENGINE_DEVICE`, …) are all covered by
  the pattern rule — the list is illustrative, the **pattern** is normative, so a hook added in a later
  slot is refused without an edit.
* **Unreachable by construction.** The emitters are registered *validations* (`GoldenEmit`, `GoldenDump`,
  `ConsoleScriptEmit`, `HeckeTauDumpValidation`, `HeckeSatCertDumpValidation`, `CliManualCoverageValidation`);
  `run_validation` is untagged, no CLI validation name is accepted with `--serve` (§18.2), and the gate
  above removes their interlocks. The `--campaign`, `--bench`, `--atlas --close` writers are CLI tokens and
  are likewise refused.
* **Process hardening** (after the gate, before `hello`; each failure is `fatal`-free exit 1 with a stderr
  line): `setrlimit(RLIMIT_CORE, 0)`; `setrlimit(RLIMIT_FSIZE, 0)` with `SIGXFSZ` ignored (every attempt to
  extend a regular file fails with `EFBIG` — defence in depth behind the tag; stdout must be a pipe or a
  socket, which `RLIMIT_FSIZE` does not affect — if it is a regular file the binary refuses, exit 1);
  `prctl(PR_SET_NO_NEW_PRIVS)` on Linux; the gateway starts the child in an **empty scratch working
  directory** it owns. `RLIMIT_AS` is **not** set (it breaks the CUDA driver).
* `ENGINE_DEVICE=cpu` is the default and the golden path and is not overridable (`device` is not a settable
  key and `ENGINE_DEVICE` is refused); the GPU is therefore never enabled in a served session. A `hello`
  with `"cuda":true` means only that the device is *present*.

### 18.10 RSS cap and the `fatal` frame

* **Prediction first (rule 19).** The gateway refuses to start a session whose predicted peak exceeds the
  cap it was given (the per-`n` RSS tables are in `docs/performance-reference.md`); an interactive cell can
  still overshoot, hence the guards below. The binary never *predicts*.
* `--rss-cap-mib N` (N > 0) starts a **watchdog thread** in the binary reading `/proc/self/statm` every
  250 ms and at every statement boundary. At resident > N MiB it writes
  `{"kind":"fatal","reason":"rss_cap","detail":"resident <r> MiB > cap <N> MiB","seq":…}` and calls
  `_exit(70)`: no unwinding, no flush of anything but that frame (a partially written reply frame is not
  completed; the gateway treats a stream cut mid-line as `killed`). `bad_alloc` that *is* thrown is the
  ordinary C7 row (exit 3, session continues).
* The **gateway has its own watchdog** (it owns the process: `SIGKILL` on the cap with a margin, per-cell
  CPU-time and wall limits). The binary's cap is the first line, the gateway's the last; on a 16 GB
  Jetson-class host the gateway's cap is the one that matters because a fast allocator can outrun 250 ms.
* Other `fatal` reasons: `internal` (an exception escaping the dispatcher, i.e. a bug — the session cannot
  be trusted), `stdin` (a read error), `protocol_overflow` (a request line over `max_request_bytes`).
  After `fatal` the process exits 70; the gateway restarts it (a new `hello`).
* `rss()` / `timed()` are served verbs and report the **process** resident set, so the notebook can show it.
* *(v3.15.0-pre.3, NBCONFIRM S4)* **Per-cell prediction.** The binary now does predict, per call outside a verb's silent
  envelope (§7.1, §18.19): the session's `--rss-cap-mib` is R_cap of rule 1, so a call whose `rss_hi` exceeds
  min(cap, 0.8 · MemAvailable) is refused **before** it runs (`RuntimeError`, exit 3, no token). The watchdog above is
  unchanged and stays the guard against an under-estimate; nothing a client sends can raise the cap.

### 18.11 Conformance tests (NB-2 implements; NB-3 reuses the fixtures)

Two registered validations, both guarded by `OC_BUILD_NOTEBOOK` (`[SKIP] … OC_BUILD_NOTEBOOK=OFF`,
returns 0), each printing the `EFFECTIVE <name> arm=<X> cells=<k>` convention line so that a vacuous arm is
visible. They live in `Registry/Slot19/` + `cmake/slot19/` (the slot's pair of fragments, §10 pattern) and
register after WP-1's names. They need no GPU and no network, and run with `ENGINE_CUDA_DISABLE=1`
semantics where a device would be probed.

**`ConsoleReadOnlyTagValidation` — `fast`**
* **(A) registry ⇄ fixture, both directions.** `Console/serve/read_only_verbs.tsv` (a reviewed fixture:
  `name<TAB>signature<TAB>read_only<TAB>audit`, one row per **overload**, `audit` a one-line justification
  for every `true` row: *"no I/O"*, *"pure"*, …) lists every registered overload. The registry must equal
  the fixture: an overload with no row, a row with no overload, or a tag that differs, fails and names the
  overload. (A new verb therefore fails until its row is added — the "excluded until audited" rule made a
  check.)
* **(B) completeness of the default.** The set of overloads whose tag was never explicitly written is
  empty (the registrar API takes the flag as a required argument in `OC_BUILD_NOTEBOOK`-independent code;
  the check counts `registered == explicitly_tagged`), i.e. "default false" is a safety net, not a way to
  forget.
* **(C) no tagged overload reaches a writer or emitter.** (C1) a *source* audit: the files listed in the
  fixture's `audit` column are not enough, so the validation also greps the binding sources of every tagged
  overload's registration TU for the writer entry points (`std::ofstream`, `fopen`, `open(`, `std::filesystem`
  mutators, `getenv`, `system(`, `popen`) and requires an allow-listed, content-keyed exception (the
  `label_census.allow` style: an entry matching nothing is STALE and fails) — the exceptions being exactly
  the process-start reads that already exist; (C2) a *dynamic* audit: every tagged overload is called at least
  once in the conformance run of `ConsoleServeValidation (B)` with the process under `RLIMIT_FSIZE = 0`, the
  working directory empty before and after, and `git status --porcelain` of the source tree unchanged
  (probed, not required: skipped with an `EFFECTIVE … git=absent` line if the tree is not a checkout).
* **(D) manual.** The generated verb table's tag column equals the registry's (a read of
  `docs/latex/cli_manual/verbs.tex`'s marks, as `CliManualCoverageValidation` already reads that file), and
  `\CMNumReadOnly` equals the count.
* **(E) type coverage.** Every registered type has a `PrintJson`: a dedicated one or the generic form, and
  the set of **D** types equals the §18.5 table's (a type added without either fails).

**`ConsoleServeValidation` — `standard`** (drives the real binary: it `fork`/`exec`s its own `argv[0]` with
`--serve` and a whitelist environment, over pipes; the harness is a C++ NDJSON client; no Python).
* **(A) handshake.** `hello` is the first frame, `seq:0`, with `proto:"oc-serve/1"`, `json_version:1`, the
  field set of §18.2; `counts.verbs` / `overloads` equal the registry's tagged counts; `settable` equals
  §18.8's list. Every frame parses as JSON; no line is blank; `seq` is strictly increasing by 1.
* **(B) the transcripts — the ConsoleDet guard.** For every numbered script of `Console/scripts/` the
  harness sends its text (`include` statements flattened textually by the harness, cycle-checked; `args.*`
  passed in `args`) as one `eval` and requires: `done.status == "ok"`, `done.exit == 0`; the concatenation of
  the `out.text` frames, **byte for byte equal to the script's `.expected` body** (the part after
  `#! oc-format 1`, `#~` lines excluded, exactly as `ConsoleScriptValidation` compares); the `progress`
  frames equal the `#~` lines of the REPL run, in order; no frame exceeds `max_reply_bytes`. Scripts that
  call an untagged overload (`022_harness`, `048_c5c_ring_campaign`, and any other the audit finds —
  recomputed, not listed here as a pin) are **not** in this arm; each is in an explicit exempt table
  `{script, first untagged call, expected kind}` and is **required to be rejected** exactly as stated in
  arm (D) (an exempt script that *passes* fails: the table must stay minimal). The `EFFECTIVE` line prints
  `scripts=<k> exempt=<j>`.
* **(C) values.** For every `value` frame of arm (B): the envelope parses; `t == type(x)`; `canonical`
  equals what `repr`/`show` prints for that value; `hash` equals `hash(x)` when the kind has one; every §18.5
  schema invariant holds (integer rule, `Poly.order`, `Matrix` dimensions consistent with `entries`, a
  `Record` is an array of pairs, key order as the table). Plus a **determinism** arm: the arm-(B) frame
  stream (volatile fields stripped, §18.5) hashes identically at `ENGINE_THREADS` 1 / 2 / 8, program cache
  on / off — the served twin of ConsoleDet's grid; the **digest of ConsoleDet C4 (a)
  (`0xf6ed04bbe8e6b60a`)** and the **golden** (`GOLDEN_STRICT=1 GoldenRegressionValidation`: A 11827 / B 6231)
  are unchanged by NB-2 and re-checked in its close commit.
* **(D) error mapping.** One cell per row of §18.7, each asserting `status`, `exit`, `error.kind`, the
  `<cell>:line:col` prefix and — for a lazy failure — `created_at`; and **the session survives each**: the
  next `eval` returns a correct value (`print(1+1)` → `out "2\n"`), including after a `failed` handle is
  re-accessed (it rethrows, never retried), after an `assert` failure, after a `not_implemented` (a legal
  non-default `coefficient_ring` setting), after a parse error (nothing ran), after `bad_alloc` if inducible
  (else skipped with `EFFECTIVE … bad_alloc=skipped`), and after an interrupt. Also: `include`, `quit`, `exit`
  cells ⇒ `rejected/forbidden/exit 1`; an untagged overload under a tagged name ⇒ `forbidden_overload/exit 3`
  with the *call not executed* (the cell's `print` before it ran; a sentinel file path proves no write).
* **(E) interrupt.** An `eval` of a loop over a cheap verb receives `interrupt` ⇒ `done` `interrupted/3`
  within one statement; the session continues; a second `eval` sees the bindings of the first.
* **(F) protocol robustness.** Malformed JSON, unknown `op`, missing `id`, an `eval` whose `src` is not a
  string, a request line over `max_request_bytes` (⇒ `fatal protocol_overflow`, exit 70), the 65th queued
  request (`busy`), `close` (`bye`, exit 0), stdin EOF (exit 0, no `bye`).
* **(G) environment & hardening.** One child launched with each of `GOLDEN_EMIT=1`, `CONSOLE_EMIT_EXPECTED=1`,
  `HECKE_NEBENTYPUS_NB3_FULL=1`, `ENGINE_DEVICE=gpu`, `ASAN_OPTIONS=…`: **exit 1, empty stdout, the stderr
  line of §18.9** — and the emitter's would-be output path (a path in the harness's scratch) does not
  exist afterwards; with the whitelist only: starts. `RLIMIT_FSIZE`, `RLIMIT_CORE` read back from the child's
  `/proc/<pid>/limits`; a regular-file stdout is refused.
* **(H) RSS cap.** A child with `--rss-cap-mib` just above its baseline and a cell that allocates (a large
  `zero(p, r, c)`) ⇒ a `fatal rss_cap` frame and exit 70 within the stated interval, **or** an ordinary
  `bad_alloc` exit-3 `done` (both are acceptable outcomes; a silent exit or a hang is not); the harness
  cap is small (≤ 512 MiB above baseline) so the test never approaches the box's limits.
* **(I) chatter capture.** A cell that makes the pipeline print (a verb known to write to `cout`/`cerr` with
  `verbose=true`, with `verbose` forced `false`) produces **no** non-frame byte on stdout (every stdout line
  parses as a frame); and a `set verbose = true` cell is `forbidden_overload` (not settable).
* **(J) completion / help.** `complete("hec")` contains `hecke`; no untagged name (`run_campaign`) appears
  in any `complete`, `help`, `verbs()` result; `help("")` lists the served verbs.

**NB-2 acceptance gates (beyond the two validations):** ConsoleDet digest unchanged; **zero change to any
`.expected`** and to `cli_frozen/`; golden untouched (`'*GoldenReference.inc'`); the CLI manual's tables
regenerated in the same commit (`CliManualCoverageValidation` green; `--serve` appears in `tokens_console`);
`console.md` regenerated (`gen_console_md.sh --check` current); `check_console_includes.sh` clean
(`Console/Core` unchanged: it is STL-only and gets no JSON dependency — the JSON writer is a small
hand-rolled emitter in `Console/Bindings/`, with the escaper of §4.3's `json`, and the JSON *reader* for
requests is a minimal hand-written parser for the request grammar of §18.3, again no external library);
`--all` / `--all-full` totals changed by exactly the two names; the standing performance gates unaffected
(the served path is not on the engine's path).

**NB-3 gateway conformance** (listed here so the contract is one document; NB-3's own test suite is its
deliverable, in Python's `unittest`, no pip): the bind/`source filter`/`token`/`public bind refused` rules of
§18.12; the child's environment equals the whitelist exactly; the read-only list read from
`read_only_verbs.json` equals the binary's `hello.counts`; per-cell kill on CPU / wall limit and on the
RSS cap; restart after `fatal`/kill gives a fresh `hello`; one session per notebook; no request reaches the
binary without a valid token; frames are relayed unmodified.

### 18.12 LAN-exposure rules (gateway requirements, owner decision 2026-10-03)

Recorded once, here, from the design note §0.1: (1) **never beyond the local network, reachable from other
LAN devices**: a configurable `--bind` (default `127.0.0.1` / `::1`); (2) the gateway accepts only
connections whose **peer address** is loopback, RFC 1918 (`10/8`, `172.16/12`, `192.168/16`), link-local
(`169.254/16`, `fe80::/10`) or unique-local (`fc00::/7`) and drops others at `accept`; (3) a **per-session
random access token**, ≥ 128 bit, printed once at startup, sent as a header or as the first WebSocket frame,
compared in constant time; (4) the gateway **refuses to start** if the bind address is public, or is the
unspecified address (`0.0.0.0` / `::`) on a host with a public route; (5) **no TLS in v1** — the LAN
traffic is cleartext and the token travels in it, documented in the gateway's README; (6) the allow-list of
§18.8 is a safety rail, not a sandbox, and a token holder is trusted. The binary's side is only §18.9 and
that it never listens. A TLS (self-signed) promotion, persistence and multi-user access are R-U1b (design
note §8, owner open items (i), (ii)).

### 18.13 What §18 deliberately does not do

No TeX printer (§18.1.2); no persistence of sessions or notebooks; no atlas queries (NB-4); no campaign
launch; no file upload/download; no editing of the environment; no `Console/Core/` change; no new exit
code; no new canonical printer, so no `.expected` and no ConsoleDet movement; no new verb (the existing `json`
verb is untouched, and `PrintJson` is not a verb). Open for NB-2 to report rather than decide: the exact
registry metadata seam for the tag (§18.8); whether `report`'s path can be split off; whether the 250 ms RSS
watchdog needs a faster poll on the Jetson; the final tagged / untagged count.

### 18.14 As built (v3.10.1, slot-19 NB-2)

The open points of §18.13, and every place the build fixes what the text left free. Code: `Console/Bindings/{Serve,PrintJson,
ServeJson,ReadOnlyTags}.{h,cpp}`, the `kernel.cu` branch (before `RegisterAllValidations`, so a served process registers no
validation and probes no device), `Console/{ConsoleReadOnlyTag,ConsoleServe}Validation.cpp`, fixtures `Console/serve/`
(`read_only_verbs.tsv`, `read_only_sources.allow`, `coverage.oc`); fragments `Registry/Slot19/NB2.cpp`, `cmake/slot19/NB2.cmake`.

(a) **The registry seam (open point 1).** The tag is a binding-side table, `serve_tags::ReadOnlyTagTable()`
(`Console/Bindings/ReadOnlyTags.cpp`), keyed by *(verb, `Signature::to_string(verb)`)* — the text the manual and `help` print —
always compiled (the manual's column does not depend on the switch). Core's `Overload` gets no field. Filtering *at dispatch* needs
the registry itself to hold only the served view while every `TypeInfo` keeps its address (the extension layer keys its type
tables by `TypeInfo*`, and `==` on objects goes through the type): a copied registry broke both, so Core gained ONE additive method,
`Registry::transform_overloads(f)` (rewrite / drop overloads in place, drop an emptied verb; types untouched), called once by
`--serve` and by nothing else. With it the served process's registry holds: every tagged overload wrapped (interrupt check +
coverage flag), a **refuser** in place of an untagged overload whose verb has a tagged sibling (`save_state(x, path)` →
`forbidden_overload`, nothing of the call runs), and no entry for a verb with no tagged overload (`forbidden` statically, at parse
time). `verbs()`, `help`, `complete` and `hello.counts` therefore show the served view. One residue: the in-language `help save_state`
statement lists the refuser's signature, its doc prefixed `[not served: read_only = false]`; the protocol `help` op omits it.
Check (B) is "every registered overload has a row" (`CensusOf`), the registrar API being unchanged.

(b) **`report`'s path (open point 2).** *Superseded by (g) in v3.10.2: split.* As built in v3.10.1: not split; `report` stayed untagged (the forecast 157 / 9). A split is feasible —
a pathless `report(D, level_a = false)` registered *before* the 3-arg overload keeps every legal call's resolution, and the one
pinned failure text (`014_expect_error`'s `"argument 'path' expects String"`) is a substring the two-overload `TypeError` still
contains — but it adds an overload to the manual and to every failed-resolution message; an owner decision. Its effect would be
to bring `006_flagship` and `012_report_schema` into arm (B). `Report.write(path)` is unreachable (no served verb makes a Report).

(c) **The RSS poll (open point 3).** 250 ms (`kWatchdogPollMs`) plus a check at every top-level statement boundary and after each
cell. Arm (H) on the reference box: `random_matrix(7, 9000, 9000, 1)` (≈ 309 MiB) under a cap of baseline + 256 MiB ends in
`fatal rss_cap` / exit 70 at ≈ 323 MiB resident. A 16 GB Jetson needs no faster poll **for the binary**: within 250 ms an
allocator can outrun any binary-side poll (≈ 2–5 GB at memset speed), which is why the gateway's own cap (§18.10) is the one that
matters there; a shorter poll buys little and costs a wake-up per 250 ms. Not measured on a Jetson (none attached).

(d) **The tagged count (open point 4).** 157 tagged / 9 untagged overloads; 147 of 154 verbs served (`exit`, `report`,
`run_validation`, `bench`, `micro`, `campaign_spec`, `run_campaign` are not; `save_state` is served by its 1-arg overload).
`\CMNumReadOnly` = 157, `\CMNumReadOnlyVerbs` = 147.

(e) **Arm (B) exempt table (recomputed; v3.10.1 figures, see (g) for v3.10.2).** Six of the 38 numbered scripts: `006_flagship` and `012_report_schema` and
`014_expect_error` (`report`, `forbidden`), `021_settings_resume` (`set threads`, `forbidden_overload`), `022_harness`
(`run_validation`, `forbidden`), `048_c5c_ring_campaign` (`run_campaign`, `forbidden`). The other **32** serve their `.expected`
body byte for byte; the served determinism grid (default, `ENGINE_THREADS` 1 / 2 / 8, `program_cache=false`) gives one digest.

(f) **Smaller points fixed by the build.** `hello` carries `"seq":0` right after `kind`. `cuda` is the build switch and
`ENGINE_CUDA_DISABLE` (not probed). The env gate's sanitizer rule is the suffix `*SAN_OPTIONS` (LSan included). `set` of an
existing non-settable key is refused (`forbidden_overload`) when the top-level statement containing it is about to run (earlier
statements of the cell have run). The cooperative interrupt is checked at every top-level statement and at every served verb call
(so a loop over a cheap verb stops within one call). `args` of an `eval` are bound for the cell but stay bound afterwards (Core has
no unbind; a later cell sees them). A cell's error is reported only in `done.error` (not echoed into `out`). `perf.peak_rss_mib` is
`VmHWM`. Process stdout is re-pointed to stderr after the protocol stream is duplicated, so stray `printf` / `std::cout` of the
pipeline lands in the log; pipeline `cout`/`cerr` during a cell is captured into `out` frames `stream:"log"` (none seen in the
conformance run). **PrintJson**: a `declared` handle shows only members its type registers as *structural* — `Cohomology.ell` /
`d_V` are registered computed, so a declared Cohomology shows `coefficient_ring` alone; `Block` has no `.json` of its own, so its
`v.json` is the record of its members (basis excepted); nested objects deeper than 3 levels are reference envelopes
(`v:null, truncated:true`); the generic form never reads a `verify` member; integer literals inside embedded `.json` trees obey
the 2^53 rule. The CLI token `--serve` is a row of `tokens_top` (the scan of `kernel.cu`), its modifiers a new table
`tokens_serve` (the scan of `Serve.cpp`); `read_only_verbs.json` is the 21st generated artefact.

(g) **`report` split (v3.10.2, slot-19 NB-report; owner-approved 2026-10-04).** Registered in this order: `report(D: Decomposition, level_a: Bool = false)` (**tagged `read_only`**: computes the `hecke_report/v2` record in memory) and `report(D: Decomposition, level_a: Bool = false, path: String = "")` (the former signature, text unchanged, **untagged**, a refuser in the served view). Resolution is first-match, so every call without a path resolves to the tagged overload and `report(D, path = "x")` / `report(D, false, "x")` to the writer. Because a Report is now obtainable in a served session, the method `Report.write(path)` (file writer) throws `RuntimeError` there (`bind::ForbidReportWrite()`, called once by `--serve`). Counts: **158 tagged / 9 not**, 167 overloads, 148 of 154 verbs served; `\CMNumReadOnly` = 158, `\CMNumReadOnlyVerbs` = 148. Arm (B): exempt table now `014_expect_error` (`report`, `forbidden_overload`), `021_settings_resume`, `022_harness`, `048_c5c_ring_campaign`; the other **34** scripts serve their `.expected` body byte for byte. Unchanged: every `.expected` transcript, the ConsoleDeterminism digest, golden.

### 18.15 As built (NB-3, slot 19): the gateway and the page

`notebook/gateway/oc_gateway.py` (stdlib-only Python 3), `notebook/page/` (`index.html`, `app.js`, `render.js`,
`style.css`), `notebook/vendor/katex/` (katex 0.19.0 from the npm registry, MIT `LICENSE`, `PROVENANCE.txt` with the tarball's
sha256 / sha1 / sha512, `SHA256SUMS`; `.woff2` faces only), `notebook/gateway/README.md` (the §18.12 (5) no-TLS note), the
self-test `notebook/gateway/test_gateway.py` (`unittest`, 14 tests against a real `--serve` binary). Points the text left free:
(a) **transport**: a minimal RFC 6455 WebSocket in the gateway (no long-poll), one per tab; the token is the first frame
(`{"op":"auth","token","tab"}`) or a `Bearer` header; static files carry no secret and are served without it; a cross-origin
upgrade is refused. (b) **Peer filter**: exactly §18.12 (2); `100.64/10` (RFC 6598) is *not* accepted. The unspecified bind is
accepted only when every host address is non-public (Linux `/proc` enumeration; else refused). (c) **Gateway ⇄ page**: the
child's frames are relayed unmodified; the gateway's own messages are `{"kind":"gw","event":…}` (no `seq`, so the binary's `seq`
stays strictly +1). (d) **Read-only, second line**: a session is refused when `hello.counts` ≠ `read_only_verbs.json`; a cell
calling a verb with no read-only overload is refused lexically by the gateway (`gw rejected`, `forbidden`); overload-level
refusals stay the binary's. (e) **Limits**: binary cap `--rss-cap-mib N` (default 4096), gateway kill at `N + max(64, N/10)`
MiB, per-request wall (1800 s) / CPU (off) limits, idle close (3600 s), one request in flight per session (`busy`), a session
refused when `MemAvailable` < N; no per-session prediction beyond that (the binary never predicts, §18.10). (f) **Page**: TeX
is produced only in `render.js`, from validated integers and fixed macros (`Int`, `Fp`, `Poly` HIGH → LOW from the
`low_to_high` list, `Matrix` ≤ 900 entries, `GF`, `GFElt`, `LocalSystem`, computed `Cohomology`, lists of these); every
other type shows `canonical` (+ a record table / the generic members / a JSON view); no session string reaches TeX or
`innerHTML`. The atlas panel is a stub that only inserts an `atlas(ell)` cell. (g) Not a registered validation (the gateway
is outside the C++ build; `--all` must not need Python); run by hand on a notebook build. Nothing of §1–§18.14 changes.
(h) (v3.14.0-pre.2) Run at every slot close: one `OC_BUILD_NOTEBOOK=ON` build, `test_gateway.py --binary <it>` reading
`GATEWAY_TEST … verdict=OK` and `node notebook/gateway/test_render.mjs` reading `RENDER_TEST … verdict=OK`
(`docs/implementation/slot-close-notebook.md`). The page's *compute* and *show all* buttons are §18.5's "`display` and the
page's actions".

### 18.16 The atlas sidecar and `--serve-atlas`, protocol `oc-serve-atlas/1` (v3.11, slot-20 NB-4)

**Status: specified v3.11 and built by slot-20 NB-4 (as-built points: (k)).** Sources: design note §6 (the owner accepted the
index sidecar and the read-only mmap, 2026-10-03), slot-20 plan v1.0 row NB-4 and ruling O12. It replaces the forward references
"(NB-4)" of §18.3 and §18.13: **`oc-serve/1` is unchanged** (no `op:"atlas"` in it); the atlas is a separate process mode with a
separate protocol. Nothing of §1–§18.15 moves: no verb, type, member, setting, exit code, canonical printer, `.expected`
transcript, `read_only` tag or ConsoleDet digest.

(a) **Scope and the owner's rules.** A browser reads a `hecke_atlas/v1` store — in practice the Σ(691) store
(`hecke_atlas_ell691.json`, 451 875 793 bytes, FNV-1a-64 `0x73c7210047a81b97`, out of git by owner ruling) — through *queries*:
the store header, a page of cells, one cell with its occurrences, one system by id, a filtered page of systems. **The store is
never sent to the browser, never written, never rewritten**, and its path comes from the gateway's launch configuration, **never
from a request**. LAN-only, read-only and the gateway rules of §18.12 apply unchanged; the environment gate of §18.9 is reused,
not weakened (the same function, the same pattern rule).

(b) **The sidecar `oc-atlas-index/1`.** A compact byte-offset index of one store, kept *beside* the store (not in git), keyed to
the store by its size and FNV, so that a stale index is detected and never used.
* **Written only by** `hacs --atlas --index <store.json> [--out <path>]` — the owner's one-off, a token of the
  `--atlas` family: not reachable from `--serve` or `--serve-atlas` (both refuse every other token) and never invoked by the
  gateway. Default `<path>` = `<store.json>.ocidx`. Refused (exit 1, nothing written): an output that is the store itself (same
  `realpath`), that lies inside the source tree, or under `docs/matrix-engine/results/`. The store is opened `O_RDONLY` and
  mapped `PROT_READ`; the index is written to `<path>.tmp.<pid>` and renamed. Prints one line `ATLAS_INDEX store_bytes=…
  store_fnv=0x… cells=… systems=… occurrences=… index_bytes=… index_fnv=0x… out=…`; exit 0, 1 (usage / refusal) or 3 (the
  store is unreadable or not indexable).
* **Format** (ASCII, `\n`-terminated lines, fields separated by one TAB, integers decimal, hashes `0x` + 16 lower-case hex):

```
#oc-atlas-index/1
store_name	<basename of the store>
store_bytes	<size>
store_fnv	0x<FNV-1a-64 of the store bytes>
schema	hecke_atlas/v1
ell	<ell>
n_max	<n_max>
cells	<k>
systems	<N>
occurrences	<m>
head	<off>	<len>        the bytes before "cells" (the header's first keys, through "fields")
tail	<off>	<len>        the bytes after the systems array (chi_count, chi_in_sigma, s_sep, s0_anemic, the final brace)
C	<n>	<off>	<len>      k lines, ascending n: one cell object each
S	<off>	<len>	<r>	<e|c>	<collected 0|1>	<base>	<twist>   N lines; the row index is the system id
O	<n>	<ideal>	<id>      m lines, ascending (n, ideal): the occurrences of the collected systems
end	0x<FNV-1a-64 of every preceding byte of the index>
```
* **Indexable store.** The scanner accepts exactly the layout `AtlasStore::to_json` writes: the header keys, `"cells":[` with one
  object per line, `"systems":[` with one object per line in the key order `id, r, eigenvalues, type, chi, base, twist, collected,
  in_H1, occurrences`, ids `0 … N−1` in order, cells strictly ascending in `n`; anything else is "not indexable" (exit 3 of the
  writer, a launch refusal of the server). `info` re-parses `head` + `"cells":[],"systems":[]` + `tail` as one JSON object.
* **Validity, checked at every open by `--serve-atlas`**: the magic line; the `end` hash; `store_bytes` = the file's size;
  `store_fnv` = the FNV of the mapped store (always recomputed at open); and every header field and `C` / `S` / `O` line equal to
  what the scanner derives from the store — the index is a cache of a pure function of the store bytes, so it is compared field
  by field, never trusted. Any difference is a **launch refusal** (`stale or corrupt index`), never a silent rebuild. With no
  index (`--index` not given and `<store>.ocidx` absent) the same table is built in memory at open and `atlas_hello` says
  `"index":{"source":"memory"}`; the replies are byte-identical either way.

(c) **Launch.** `hacs --serve-atlas --store <store.json> [--index <path>] [--expect-fnv 0x<16 hex>]
[--max-reply-bytes N] [--rss-cap-mib N]` — only with `OC_BUILD_NOTEBOOK=ON` (otherwise an unknown token, exit 1). Dispatched in
`kernel.cu` before the validation registry: no validation, no verb, no device probe. Order: (1) the §18.9 **environment gate**,
the same `EnvNameRefused` rule as `--serve` (refuse, never scrub); (2) the command line (any other token, a repeated or valueless
option: exit 1); (3) the §18.9 **process hardening** — stdout not a regular file, `RLIMIT_CORE = 0`, `RLIMIT_FSIZE = 0` with
`SIGXFSZ` ignored, `PR_SET_NO_NEW_PRIVS`, the protocol stream a private duplicate of stdout and fd 1 re-pointed to stderr;
(4) open the store `O_RDONLY | O_CLOEXEC` (a regular file), map it `PROT_READ`, `MAP_PRIVATE`, compute its FNV (then
`MADV_DONTNEED`: the store's pages are not kept resident) and compare it with `--expect-fnv` when given; (5) load and check the
index (b), or build it; (6) write `atlas_hello`. A refusal at any step writes nothing to stdout and one
`serve-atlas: refused: <reason>` line to stderr, exit 1. There is no write path: the store's descriptor is read-only, its mapping
has no `PROT_WRITE`, and the process cannot extend any file.

(d) **Frames** (NDJSON as §18.4; `seq` from 0, strictly +1; keys in the order listed; no frame exceeds `max_reply_bytes`, default
1 048 576, at least 4096). Every kind carries the prefix `atlas_`, so a relayed atlas frame can never be taken for an `oc-serve/1`
frame.
* `{"kind":"atlas_hello","seq":0,"proto":"oc-serve-atlas/1","read_only":true,"build":{"commit","config","pid"},
  "store":{"name","bytes","fnv","schema","ell","n_max","cells","systems","occurrences"},"index":{"source":"sidecar"|"memory",
  "fnv"},"limits":{"max_reply_bytes","max_request_bytes":65536,"page_max":1000,"rss_cap_mib"},"open_ms"}` — the store's *name*,
  never its path; `build.pid` and `open_ms` are volatile.
* **Exactly one** `{"kind":"atlas_reply","id","seq","op","status":"ok"|"error"|"rejected","error":null|{"kind","message"},
  "store":"0x<fnv>","result":{…}|null,"perf":{"elapsed_us"}}` per request (`perf` volatile), so every displayed object carries
  the store hash.
* `{"kind":"atlas_bye","seq"}` (reply to `close`, exit 0); `{"kind":"atlas_fatal","reason","detail","seq"}` and exit 70 (reasons
  `rss_cap`, `protocol_overflow` — a request line over 65 536 bytes —, `stdin`, `internal`). Stdin EOF: exit 0.

(e) **Requests.** One JSON object per line with `op` and (except `close`) `id` (the §18.3 `id` rule); an unknown field is an error.

| `op` | fields | `result` |
|---|---|---|
| `info` | — | `{"header":<the store's header object: schema, ell, n_max, settings_fingerprint, primes, fields, chi_count, chi_in_sigma, s_sep, s0_anemic>,"cells","systems","occurrences","collected","types":{"eisenstein","cuspidal"},"r_profile":[[r,count],…]}` |
| `cells` | `offset` (default 0), `limit` (1 … 1000, default 50) | `{"total","offset","items":[<cell object>,…],"next":int|null}` |
| `cell` | `n` | `{"cell":<cell object>,"occurrences":[{"ideal","sid"},…]}` |
| `system` | `sid` | `{"system":<system object>}` |
| `systems` | `filter` (object; every key optional: `r` int, `type` `"eisenstein"` / `"cuspidal"`, `collected` bool, `base` int, `twist` int, `n` int = occurs at cell `n`), `offset`, `limit` | `{"total":<number of matches>,"offset","items":[<system object>,…],"next":int|null}` |
| `close` | — | `atlas_bye` |

A *cell object* / *system object* is the store's own row, parsed and re-emitted by the §18.4 writer (the 2^53 integer rule; no
other re-encoding). A page holds at most `limit` items and is cut earlier when the next item would push the frame over
`max_reply_bytes`; `next` is then the offset to continue from (`null` at the end). A page holds at least one item unless that
item alone exceeds the cap (`error` / `too_large`). Errors (an `atlas_reply`; the process continues): `rejected` / `protocol` (not
JSON, not an object, unknown `op`, bad `id`, an unknown, missing or ill-typed field, `limit` or `offset` out of range);
`error` / `not_found` (no cell `n`, no system `sid`); `error` / `too_large`. Replies are a pure function of the store bytes and the
request sequence (volatile: `perf`, `build.pid`, `open_ms`).

(f) **Gateway** (NB-3's `oc_gateway.py`, extended; still stdlib-only). `--atlas-store <store.json>` (optional; without it the
atlas panel stays the in-process stub of §18.15 (f)), `--atlas-index <path>`, `--atlas-expect-fnv 0x…`, `--atlas-rss-cap-mib N`
(default 1024; the gateway kills at `N + max(64, N/10)` MiB), `--atlas-wall-s` (default 60, per request). Per session (tab)
**one** `--serve-atlas` child, started lazily at the session's first atlas request, with the §18.9 whitelist environment (the
inert variables only), its own empty working directory and process group, ended with the session. Page → gateway:
`{"op":"atlas","id","query":<an op of (e) but close>, …its fields}`; the gateway checks `query`, the field names and their JSON
types and forwards `{"op":<query>,"id",…}`; frames come back **unmodified**; one atlas request in flight per session (`busy`).
No page message has a field that could carry a path. The `session` event gains `"atlas":{"configured":bool,"store":<basename>|null}`.

(g) **Page.** The atlas panel shows the store header (name, bytes, FNV, ell, counts, S_sep), a paged cell list (n, dims, ideals,
the `U_ell` verdict; a cell opens its occurrences), a system view and a filtered, paged system list. TeX is made only in
`render.js`, from validated integers: an eigenvalue `a_q ∈ F_{ell^r}` as a polynomial in `Y` modulo `C_{ell,r}` (from
`header.fields`), `chi_{a,b}`, `theta^j ⊗ #base`. Every object shows the store FNV and a **copy request** button (the
`oc-serve-atlas/1` request line that reproduces it); for an in-process `ell ∈ {5, 7, 11, 13}` an `atlas(ell)` cell can still be
inserted (§18.15 (f)). No store string reaches TeX or `innerHTML`.

(h) **`ConsoleServeAtlasValidation` — `standard`**, registered in `Registry/Slot20/NB4.cpp` (sources `cmake/slot20/NB4.cmake`),
always registered (the `--list` count is switch-independent); in a default build `[SKIP] ConsoleServeAtlasValidation:
OC_BUILD_NOTEBOOK=OFF`, exit 0. It builds Σ(23) in process (`BuildAtlas`: cuspidal and Eisenstein systems, `r ∈ {1, 2}`, twists)
and Σ(13) as a second store, writes their texts into a scratch directory under `$HACS_DATA/scratch`
(removed afterwards) and drives the real binary over pipes (no Python, no network, `ENGINE_CUDA_DISABLE=1`). Arms: **(A)** the
sidecar writer: exit 0, the `ATLAS_INDEX` line, the file equal to the in-process index of the same bytes, the store's bytes and
`mtime` unchanged; the refusals of (b). **(B)** handshake, with the sidecar and with the memory index: `atlas_hello` fields, the
store FNV = `FnvBytes` of the text, counts = `ParseAtlasStore`'s. **(C)** queries against the oracle (`ParseAtlasStore` of the same
text): `info`; every cell; every system by id (`id, r, type, chi, base, twist, collected, in_H1`, the eigenvalues, the
occurrences); `systems` under each filter key and combinations, equal to the oracle's filter; paging concatenates to the full
list; the sidecar and memory runs give byte-identical reply streams (volatile fields stripped). **(D)** errors, one per row of
(e), the process surviving each; `close` → `atlas_bye`, exit 0; EOF → exit 0; an over-long line → `atlas_fatal
protocol_overflow`, exit 70. **(E)** frame cap: `--max-reply-bytes 4096` cuts pages (`next`), no frame over the cap. **(F)** stale
and corrupt indexes refused: the index of the other store, an edited `S` line with a re-computed `end` hash, a broken `end` hash,
a wrong `--expect-fnv` — each exit 1 with an empty stdout. **(G)** environment gate and hardening: `GOLDEN_EMIT=1`,
`HECKE_ATLAS_OUT=<scratch>`, `ENGINE_DEVICE=gpu`, `ASAN_OPTIONS=…`, `OC_X=1` each exit 1 with an empty stdout and the §18.9 stderr
line; a regular-file stdout and an extra token (`--set`, a validation name) refused; `RLIMIT_FSIZE` / `RLIMIT_CORE` read back from
`/proc/<pid>/limits` as 0; the store's descriptor read back from `/proc/<pid>/fdinfo` as `O_RDONLY` and its mapping in
`/proc/<pid>/maps` without `w`. **(H)** read-only: the stores' bytes and `mtime`s, the empty working directory and `git status
--porcelain` (probed) unchanged after the run. **(R)** optional, read-only: with `HECKE_ATLAS_IN=<dir>` (the existing pointer to the
real store's directory, arm K of `HeckeAtlasValidation`) one child on `<dir>/hecke_atlas_ell691.json` with `--expect-fnv
0x73c7210047a81b97` (346 cells, 1 002 225 systems; systems 0 and 1 002 224 and cell 690 checked; the store unchanged); otherwise
`real=absent`. Prints `EFFECTIVE ConsoleServeAtlasValidation arm=ALL cells=<k> systems=<k> queries=<k> real=<absent|sidecar|memory>`.

(i) **Manual.** `--serve-atlas` is a row of `tokens_top`, its modifiers a new table `tokens_serve_atlas` (the scan of
`Console/Bindings/ServeAtlas.cpp`), `--index` / `--out` rows of `tokens_atlas`, `usage_atlas` regenerated — all in NB-4's
commit (`gen_cli_manual_tables.sh`). No verb, type or setting is added, so `console.md` and `read_only_verbs.json` / `.tsv` do not
change (regenerated and checked current).

(j) **Not done.** No `op:"atlas"` in `oc-serve/1`; no OC verb reads a store (a request-named file read would break §18.8's
definition of read-only); no other store (census editions, `ext_*`, `hida_towers/` follow the same pattern later, design note
§6); no full-text search; no TLS, persistence or multi-user access (R-U1b).

(k) **As built (NB-4).** Code: `Util/AtlasIndex.{h,cpp}` (the scanner, the sidecar format and the read-only mapping; STL + POSIX,
always compiled, shared by the writer and the server), `HeckeExt/HeckeAtlasCli.cpp` (`--index`), `Console/Bindings/ServeAtlas.{h,cpp}`
(the server; `OC_BUILD_NOTEBOOK` only), the `kernel.cu` branch, `Console/ConsoleServeAtlasValidation.{h,cpp}`,
`notebook/gateway/oc_gateway.py` + `test_gateway.py` (the atlas tests), `notebook/page/` (the panel). Report:
`docs/implementation/slot20/NB-4_report.md`. Points the text left free: (1) **the sidecar is a cross-check, not a
speed-up**: the scanner runs at every open anyway (the field-by-field comparison of (b)), and on Σ(691) it costs about as much
as the FNV pass — open ≈ 1.0 s with the store in the page cache, peak resident ≈ 0.47 GiB during that one pass (the mapped
store's pages, released by `MADV_DONTNEED` before `atlas_hello`), then ≈ 42–53 MiB steady; a query takes 0.01–14 ms (a 1 MiB
page of r = 54 systems the most). The Σ(691) sidecar (30 145 126 bytes, FNV `0xec4f97afa9382808`) was written beside the store
by NB-4 (`--atlas --index`; the store's `sha256sum -c SHA256SUMS` OK before and after). (2) The store's *name* (in the sidecar and in
`atlas_hello`) is its `realpath`'s basename; the writer and the server both resolve symlinks, and the default sidecar path is
`<realpath>.ocidx`. (3) A blank request line is
ignored (no frame), as in `--serve`. (4) The gateway option `--atlas-hello-timeout-s` (default 300) bounds the child's open. (5) With
`OC_BUILD_NOTEBOOK=OFF` the token falls, exactly like `--serve`, to the validation-name loop: one `[FAIL] Unknown validation:` line
per argument and a nonzero exit equal to their number (3 for `--serve-atlas --store x`), which is what "unknown token, exit 1"
means in (c) and in §18.1 item 5.

### 18.17 Page themes (client-side only; slot-22 WP-NBT, FR-1; v3.12.0-pre.1)

The page's colours are thirteen CSS custom properties (`bg fg muted line panel accent ok err warn code katex sel focus`). The page offers the presets `light`, `dark`, `high-contrast-light`, `high-contrast-dark` and `auto` (the default: `light` or `dark` after `prefers-color-scheme`), and a user-defined theme edited in the page (*Theme…*: a colour picker per token, live preview, name and base, reset to preset). A theme is exchanged as JSON `{"schema":"oc-notebook-theme/1","name":…,"base":"light"|"dark","tokens":{<token>:"#rrggbb",…}}`: unknown keys are ignored, missing tokens come from `base`, any value not matching `#rrggbb` refuses the theme (a malformed import changes nothing; file import ≤ 64 KiB, local `FileReader`). The choice is kept in the browser's `localStorage` (`oc-notebook-theme`) only; the gateway and the binary never receive it (no route, no verb, no setting, no CLI token, no change to the read-only tag set or to §18.12's exposure rules); without storage the page works and the theme lasts until the tab closes. Switching or editing a theme changes custom properties and `color-scheme` on `<html>` only: no reload, the session untouched. The page computes the WCAG 2.x contrast ratio of 19 pairs listed in `themes.js` (text 4.5 : 1: `fg` on `bg`/`panel`/`code`/`sel`, `muted` on `bg`/`panel`/`code`, `accent`/`ok`/`err`/`warn`/`katex` on `bg` and `panel`; focus ring 3 : 1 on `bg`/`panel`; `line` is decorative and not checked) and warns (header badge, marked rows), without blocking, below AA; every preset meets AA. KaTeX output, code panes, transcripts and error frames follow the theme; vendored KaTeX is not modified. CSP unchanged; `themes.js` is a blocking `<head>` script served by the existing `/static/` route, so a stored theme applies before the first paint.

**As built and verified (`nbtheme_report.md`).** Presets and data: `notebook/page/themes.js` (strict-JSON block between `OC-THEME-DATA` markers, also read by Python); user documentation `notebook/page/README.md`. Gateway self-test `GATEWAY_TEST ran=22 failures=0 errors=0 verdict=OK`, with `THEME_CONTRAST presets=4 pairs=19 checked=76 below_aa=0`; headless Chromium over CDP `CDP_THEME checks=21 failed=0`. **Not automated, an owner / lead action** (O14), recorded when done: the second-browser half of the persistence check and the file-download / file-picker dialogs. **Not done:** per-cell or per-output colours, user fonts.

### 18.18 The notebook file: `.oc` with `# %%` cells (client-side; slot-24 NB-FILE; v3.14.0-pre.5)

The page loads and saves a notebook as a plain OC script whose cells are separated by lines in the *percent* convention of Jupytext and VS Code. It is **client-side only**: no protocol, binary, value, transcript or golden change; the one gateway addition is the read-only example listing of (f). The code is `notebook/page/ocfile.js` (pure functions) and `makeNotebook` in `notebook/page/cellbox.js`; tests `notebook/gateway/test_render.mjs`.

(a) **Syntax.** A line that is exactly `# %%`, or `# %%` followed by white space and a title, starts a cell: `# %% Hecke operators`. `# %% [md] title` starts a **text cell** (not executed), whose body lines must all start with `#` (the text is the line without that `#` and one following space; a blank line is allowed on input and becomes `#`). Not separators: `#%%`, `# %%%`, an indented `# %%`. A text cell with a non-comment body line is refused with its line number. **Everything before the first separator is the preamble** (a license header, a description): kept with the notebook and written back first, **not a cell**; it is not shown, except that *Insert file* turns a non-empty preamble into a first untitled cell so nothing is lost. A file without any separator loads as **one** cell (the whole text, no preamble); an empty file as one empty cell. The title is one line (trimmed) and is shown, editable, in the cell bar; a code title cannot start with `[md]`. A code line that itself starts with `# %%` would start a cell on reload.

(b) **Still a script.** `#` begins an OC comment, so every separator and every text-cell line is a comment: `hacs --script nb.oc` runs the code cells in order, text cells contribute nothing. Checked by `Console/scripts/057_s24_notebook_file.oc` (+ `.expected`) and by running the notebook tour files and `tour_all.oc` with `--script`.

(c) **Canonical form and round trip.** LF line ends (CRLF and a lone CR are converted; a leading BOM is dropped); blank lines at both ends of the preamble and of every cell are dropped; the preamble, if any, is followed by one blank line; each cell is its separator line then its body; **exactly one blank line between cells**; one final newline. `serialise(parse(x)) = x` byte for byte when `x` is canonical, and `canonical` is idempotent. Outputs are never saved (the JSON export `oc-notebook-export/1`, which also gains the per-cell `kind` and `title`, is the way to keep them). *Export code* leaves text cells out.

(d) **Page actions.** *Open notebook…* (a file chooser; drag and drop on the page outside a cell does the same) replaces every cell, drops the queue, **restarts the session** and resets the execution count; with unsaved changes the page asks first. *Insert file as cell…* (drop on a cell) inserts the file's cells below the current cell, the session untouched. *Save notebook (.oc)* downloads the canonical file, from the current sources and titles; it clears the unsaved mark. *Restart session* now also resets the execution count (as Colab does). Files are read locally (`FileReader`, ≤ 1 MiB, nothing uploaded).

(e) **Text cells** show their text (text nodes only, never HTML; *Edit* / *Done*), have no *Run*, are skipped by *Run all*, and are saved as `# %% [md]`. *(v3.15.0-pre.8, slot-26 NBMATH A1)* With LaTeX on, the text is typeset: a blank line ends a block; `$…$` is inline and `$$…$$` display math (KaTeX, `trust: false`, `throwOnError: false`; `\$` is a literal dollar, an unmatched `$` stays text); `- ` starts a list item, `> ` a statement box, `| a | b |` a table row (a row continues over lines that do not start with `|` until it ends with `|` and has the first row's number of cells; a dash row after the first row makes it the header); `**bold**` and `` `code` ``. Built with text nodes and KaTeX only, so no text can inject markup or a link. With LaTeX off (or without KaTeX) the source is shown verbatim; *Copy*, the exports and *Save* always carry the source. A text cell whose title starts with `Reading` is a **reading panel**: it folds (closed by default; open when the notebook was opened from a file named `showcase_*.oc`). The example notebooks hold one two-column table per reading panel, and every formula of every example text cell typesets under KaTeX with `throwOnError: true` (`test_render.mjs`, `texcells=`).

(f) **Examples (gateway).** `GET /examples/index.json` lists, and `GET /examples/<name>.oc` serves, the files of **one fixed flat directory** (`--examples-dir`, default `notebook/examples/notebook/`, installed under `<prefix>/share/oc-notebook/examples`), read-only, as `text/plain` under `default-src 'none'`. Safety is by construction: a request is served only if its name *equals a name of the directory listing* (regular file, not a symlink, ≤ 256 KiB, name `[A-Za-z0-9][A-Za-z0-9_-]*\.oc`); the URL is never joined to a path, so `..`, separators, encodings and other extensions all give 404, and no directory structure is shown. Like the other static files it needs no token (they carry no secret; the session itself still does). The page offers the list as *Examples…* when it is non-empty.

(g) *(v3.15.0-pre.8, slot-26 NBMATH; owner question 8)* **Certified orders in decimal.** A `String` value that is exactly `certified:` followed by a signed lower-case hexadecimal integer (`certified:0x2b3`; the HeckeZ record's `hex=canonical_signed`) is shown with LaTeX on as `certified: 691`, the stored form on hover. Presentation only: nothing reaches TeX, and the canonical text (*text*, *copy*, the exports) is the stored string. Typed rendering of the whole record is stage B (`NBMATH_plan.md` §4 B1).

### 18.19 The cost confirmation of a served cell (v3.15.0-pre.3, pre.4; NBCONFIRM S4)

*Normative. Design `docs/console/NBCONFIRM_design.md` §2.5–2.6; owner ruling 2026-11-06 Q4; report
`docs/console/NBCONFIRM_S4_report.md`.*

* **The rule.** A served session has no terminal; its prompt is the protocol. Under `confirm = ask` (the only value a
  served session can have: `confirm` is not settable, §18.8) a call outside its silent envelope gets rules 1–4 of §7.1,
  exactly as on a terminal REPL: `confirm_wall_s` is T (settable per session; `hello.limits.confirm_wall_s` is the value at
  launch), the session's `--rss-cap-mib` is R_cap, and MemAvailable, the C: rules, the CPU count of the affinity mask and
  the device profile are read as in §7.1 (the gateway passes no `HACS_*` variable, so a gateway child uses the default
  profile path). *(v3.15.0-pre.4, audit L2)* The validations' host-probe fixture `HACS_HOST_PROBE_FIXTURE` is honoured by
  `--serve` only when the session's parent process is the same binary (a validation harness that forks and execs it);
  launched by anything else (a shell, the gateway) a session carrying it is refused at the environment gate of §18.9. Rule 1 is a hard refusal (`status:"error"`, kind `runtime`, exit 3, **no token**); rule 4 runs silently;
  rules 2–3 stop the cell **at the call** with `done`: `status:"confirm_required"`, `exit:3`, `error` =
  `{kind:"confirm_required", message:"<cell>:L:C: confirm: <verb> is outside its silent envelope (<the pre-S3 refusal
  text>); …", detail: the estimate, the strong reasons, the notes; at; verb}`, and the member `confirm` =
  `{token, level ("normal" | "strong"), verb, who, call, site {line, col}, bound, wall_s, wall_hi, rss_mib, rss_hi,
  mem_limit_mib (null when unknown), threads, extrapolated, x_factor, low_confidence, model, calibration, reasons [..],
  notes [..], kill_wall_s (the owner-Q4 limit at the gateway defaults; null when none), text}`.
  Inside an `expect_error` block nothing asks (§7.1): the pre-S3 refusal, so a served script's expected refusal reads the
  same on every machine.
* **The token** is `0x` + 16 lowercase hex digits: FNV-1a-64 (`ModArithmetic/Fnv.h`, every string length-prefixed) over
  `oc-confirm/1`, a per-process nonce, the cell text, the call site (line, col), the verb's signature, the call text, the
  estimator's verb, its arguments, its model id, T_eff, the level and the text of every setting in force. It is valid for
  that one call, with those argument values, in that one cell text, in that session: an edited cell, another argument value
  at the same site (a variable read by the call), a changed setting (`confirm_wall_s` included), another estimate level or
  a restarted session all give a new token. A cell with several expensive calls takes one round trip per call; each re-send
  carries every token so far. A token that matches nothing is ignored (the reply is `confirm_required` again).
  *(v3.15.0-pre.4)* A token is not single-use: the same cell text with the same token runs again on every re-send in that
  session. It binds no execution count either: **one token confirms every execution of the same call (same site, same
  argument values) in that cell run**, e.g. every iteration of `for i in [1, 2, 3] { q = descent(1, 62) }`; the estimate
  shown is for one run of the call, and the whole cell is bounded by the gateway's wall limit of a confirmed cell (at most
  `--cell-wall-max-s`).
* **Re-sending.** The client re-sends the same `eval` with `"confirm":[…]`. Statements before the confirmation point have
  already run when the cell stopped; their bindings persist (as after an interrupt). *(v3.15.0-pre.4, correcting pre.3's
  "only time is lost")* The re-send **re-executes** them, with the bindings the stopped run left: their side effects happen
  again (`x = x + 1` increments `x` twice), and every earlier confirmed call of the cell runs again in full on each later
  round (a cell with k expensive calls runs the first one k times). A cell that rebinds a variable it reads is therefore
  not idempotent: in `k = k + 2; r = descent(1, 60 + k)` every round changes the call's argument, hence its token, and the
  confirmation can never succeed. The stopped call bound nothing. A client must not loop: the page asks **at most once per
  call site per cell run** — when the same site asks again after its confirmation (with a new token), it stops the cell as
  `not run` and explains (compute the arguments in an earlier cell; one expensive call per cell). The same holds for a loop
  over changing arguments at one site.
* **Read-only guarantee unchanged.** The token is not a setting, writes nothing and is looked at only by a cost gate: the
  served registry (§18.8), the static scan (`include`, `quit`, `exit`, unserved verbs) and the non-settable keys are
  unchanged, and a `confirm` list lets none of them through.
* **Heartbeat** (§18.6): `progress` frames with `confirmed` at the start of the confirmed work and every 10 s. A lazy verb
  (`descent`, which confirms in its constructor) announces its estimate again when its work starts at the first member read,
  possibly in a later cell (text `running <call> (lazy work): …`).
* **The gateway** (`notebook/gateway/oc_gateway.py`) forwards `confirm` after checking its shape (≤ 16 strings of 1–64
  printable ASCII characters). The wall limit of a confirmed cell is **max(`--cell-wall-s`, 3 · wall_hi + 60)**, at most
  **`--cell-wall-max-s`** (default 21600 s = 6 h; 0 = a confirmed cell keeps `--cell-wall-s`; with `--cell-wall-s 0` there
  is no wall limit at all), where wall_hi is **the child's own estimate**, taken *(v3.15.0-pre.4)* **only** from the
  `confirmed` member of the child's `progress` frame for the in-flight request — the child sends it at the start of every
  confirmed run, before any of the call's work, so it marks exactly the calls the child accepted a token for (it also
  covers the lazy case). Presenting a token raises nothing (pre.3 also raised on a token the child had offered in the
  session, which let a stale token lift an unconfirmed cell's limit). A value sent by the page is never used. The gateway tells the page
  with `{"kind":"gw","event":"cell_wall","id","cell_wall_s","reason":"confirmed"}`; its `session` event lists
  `cell_wall_max_s` among the limits. The RSS cap is the start-up flag `--rss-cap-mib` only; nothing a page sends raises it.
* **The page** shows a modal dialog for `confirm_required`: the call, the crossed bound, the estimate (central and upper
  edge, memory and its limit, threads, model, calibration, extrapolation, low confidence), the notes and the session wall
  limit, and two fixed notes *(v3.15.0-pre.4)*: Run re-sends the whole cell (its earlier statements run again), and a call
  the cell repeats runs every time under this one confirmation; Run / Cancel (Escape = Cancel). A strong warning shows a red banner with its reasons and enables Run only after a
  checkbox. On Run the cell is re-sent with the tokens so far (its output box is cleared first); on Cancel the cell ends as
  `not run` (and "Run all" stops there). While a confirmed run is in progress one live progress line shows elapsed and
  estimated time, the resident set and the gateway's wall limit; the Interrupt button gains the "Kill session" fallback of
  §18.6. The LaTeX toggle, themes and the rest of the page are unchanged.
