# Audit of stage-01.md — defects only

## F1 — critical — stage-01.md §2–§7 (WP headers) / OVERVIEW.md §1
**Problem:** At least 38 detailed WP blocks omit mandatory schema fields required by `OVERVIEW.md §1` (all fields mandatory: id, track, goal, inputs, outputs, acceptance check, difficulty, model (+ verifier), est. agent wall, est. build wall, deps). Automated scan shows missing explicit `Acceptance` blocks for `S01-X5, S01-M1–M6, S01-L1–L13, S01-L15, S01-C1–C7, S01-H1, S01-T2` and several `Inputs`/`Outputs` sections are absent or collapsed into prose. The summary table (§1) contains them but `OVERVIEW.md §1` requires one table row *or block* per WP with all fields; the detailed blocks are the binding spec and are incomplete.
**Fix:** Expand every WP block to the full schema row/block; copy agent/build/deps from the summary table into the block; add explicit `Inputs`/`Outputs`/`Acceptance` sub-lines. Fail the plan audit until `grep -c "Acceptance:"` ≥ number-of-WPs.

## F2 — critical — stage-01.md §4 (S01-L9, S01-L5a, S01-M2, S01-M4, S01-M0, S01-C1, S01-H1) citing labels
**Problem:** Five labels cited in `stage-01.md` Inputs/Outputs do not exist in `stage.tex` (31 labels): `lem:s01-Upconv`, `lem:s01-dictionary`, `rem:s01-diamond`, `rem:s01-nu-hecke`, `rem:s01-stab-lean`. They are new M1/M5 rem/lem promises but the plan treats them as already-defined `stage.tex` labels, breaking the invariant "every Lean WP cites the statement it formalizes (stage-tex label ...) ; the statement must exist before the WP starts" (`OVERVIEW.md §1, §6`). Example: `S01-M1` "plus the new `rem:s01-stab-lean`" — no such label exists to reference.
**Fix:** Either add those labels to `stage.tex` (`\label{rem:s01-stab-lean}` etc.) or reclassify them as `mathematics/chapters/s01/...` outputs and change the WP Inputs to `def:s01-levels`/`lem:s01-stab` only, with Outputs listing the new labels.

## F3 — critical — stage-01.md §8 (Dependency DAG)
**Problem:** DAG is advertised as complete but omits required edges. Examples verified by usage scan:
- `S01-C2` output `|S_s|` and `Δ_s` freeness uses `thm:s01-mass`(d) and `prop:s01-finite` via `S01-M2`/`S01-M1`, yet DAG has no `M→C` edge; downstream `C2` must depend on `M2` or stub the count.
- `S01-L4c` `card_XB_Utower` uses `Hyp.EichlerMass` defined in `S01-L1` facade and `massW_level_change` from `S01-L6`; edge `L1→L4c` missing (only `L6`/`L5b`/`L4b` listed).
- `S01-L14` integration claims to build `LanglandscapeTests` collecting all core `examples`; its deps list `core L` expands to `{L2,L5c,L8b,L10,L11,L13}` only — missing `L1, L3a–L3d, L6, L7` which contribute files/tests.
- `S01-M7` chapter audit text says "with C2/C5 results where they exist" but DAG has no `C→M7` edge; either the audit depends on `C2` or the text is misleading.
- `S01-X5` experiment setup is said to need `X1` but `EXPERIMENT_PROTOCOL.md §1.4` says `deps X0`; the plan silently reinterprets as `X1` (`Q3`) without updating the protocol exception (`O2`). Missing `OVERVIEW §2` exception for `plan/implementation/experiments/**`.
**Fix:** Add the edges, or explicitly justify why no edge is needed (e.g., numeric-only reuse) in §8 and document the stub hypothesis. Fix `S01-L14` deps to enumerate all core L-WPs. Resolve `X0`/`X1` and add the `Overview §2` exception for `experiments/**`.

## F4 — major — stage-01.md §8 (Critical path)
**Problem:** Stated critical path `X1→L1→L6→L7→L8a→L8b→L14→L15→L16 = 420 min` is inconsistent with the DAG and estimates. Using the table's agent estimates (X1 30, L1 40, L6 45, L7 60, L8a 50, L8b 60, L14 30, L15 50, L16 45) the path through `L16` sums to 410 min without `X1` double-count or 455 min with `X1→L16`; the plan's arithmetic (40+40+45+60+50+60+30+50+45 = 420) uses `X1=40` (confusing `V: +45` variant) and drops `L8b→L16` slack analysis. Longest-path DP from the declared edges ends at `L16` = 455 min, not 420 min; alternative path `X1→L1→L3b→L3d→L11→L14→L15→L16` = 365 min, so slack figures are misstated.
**Fix:** Recompute longest path from the edge list with the definitive estimates (define whether X1 is 30 or 75); publish the DP table in §8; correct E1 slack (L9→L10 90 min, not 165 min under the worker schedule) and E7 slack; note that `L16` is conditional and should not be on the "stage-01 done" critical path.

## F5 — major — stage-01.md §4 (S01-L15, S01-M7) / OVERVIEW.md §4 + EXPERIMENT_PROTOCOL.md §1.5
**Problem:** Resource limits are violated by the schedule in §9.
- `OVERVIEW.md §4`: ≤2 local Lean builds, ≤3 TITAN, ≤3 Claude subagents per coordinator. `EXPERIMENT_PROTOCOL.md §1.5`: at most 1 local slot for experiment `lfile.sh`, at most 1 Claude subagent for experiment overhead. §9 schedule runs 3 concurrent Lean workers each doing `lbuild`/`lfile` (W1 CP + W2 side + W3 Lean-when-idle) plus up to 2 opencode Lean jobs counting double — up to 5 Lean slots, exceeding 2.
- `S01-M7` "Fable alone: no other subagent runs" is correct but the preceding line `muse → fable (5+50)` counts as 2 concurrent audits; while Fable runs, W2/W3 are claimed to pause but the DAG shows `M1–M6→M7` blocking the Lean core, lengthening the wall beyond the stated 420 min.
- Experiment strands `E1–E8` each need an Opus audit (`≈7 min`) counted as Claude slot; with 8 audits the ≤1 experiment slot budget (§1.5) is exceeded when parallelized with production L15.
**Fix:** Rewrite §9 to a feasible schedule: at most 2 concurrent Lean processes (gate `flock lean.lock` shared + slot.N); cap opencode Lean jobs to 1 at a time; serialize the two Fable audits; model experiment audits as consuming the single experiment Claude slot and show they interleave without delaying L15.

## F6 — major — stage-01.md §3–§5 (Acceptance checks)
**Problem:** Acceptance checks are not mechanical and not sufficient per `OVERVIEW.md §1`.
- `M1–M6` common acceptance (`latexmk` exit 0 + label defined once + `lit` present) does not check proof correctness, factor-2 case, or `lem:s01-Up`(d) derivation; correctness is deferred to `M7` Fable, but `M7` itself has no mechanical criterion (only "verdict line present").
- `L1–L13` acceptance `tools/check_wp.sh` (one `lbuild` + no `sorry` + docstring label present) does not verify statement faithfulness against `stage.tex` (interface name/signature, `w_x` vs `|Γ_x|` factor 2, `N_{Up}` vs `U'_p`). The plan admits this for `S01-L13` ("quality shows only as faithfulness in the audit") — i.e., the mechanical check is vacuous.
- `C6` "U_p eigenvalues vs a5" acceptance is `pytest` pass but the spec allows "record which normalisation matches" with no table; a wrong sign would still pass if the test only checks existence.
- `T1–T2` `grep -c 'results/s01' ≥1` is insufficient (comment could be fake).
**Fix:** Strengthen each check: M: add `chktex` + `grep -n "TODO"` absence + `python check_labels.py --strict`; L: add `audit interface_fidelity` script checking declared names/signatures against the verbatim stage-01.md block; C6: assert the expected normalisation (`N_{Up}` ↔ classical `U_p`) as a value, not "record"; T: assert numbers equal the JSON values via `pytest` reading `code/results/s01/*.json`.

## F7 — major — stage-01.md §1 (Model choices)
**Problem:** Several model assignments contradict `OVERVIEW.md §5` defaults and the difficulty definitions.
- `S01-L1` (mechanical facade, critical-path head, 15 WP dependents) assigned `sonnet` (correct) but justification says "rather than muse/haiku because at head of critical path" — yet `S01-L3a` (routine, also on CP via `L3a→L3c→...`) is `sonnet` while `S01-X3` (mechanical vendoring) is `haiku` with `sonnet` fallback, which inverts the cost order: a failing haiku on X3 blocks L2 (hard) and the whole Lean track.
- `S01-M5` conceptual (`dictionary seed↔import`) assigned `opus` but `S01-M7` conceptual audit assigned `muse → fable`; `muse` is explicitly "weak at conceptual maths: never haiku for M-track proofs" but muse is allowed for M-track conceptual work despite P1 59% rejection rate.
- `S01-C4` hard (exact `Sym^n` over `ℚ(√a)`, error-prone invariants) is `opus` — plausible — but `S01-C6` hard (PARI `mfinit` with characters) is also `opus` with no fallback, while `OVERVIEW.md §5` says Python/CAS → `mistral` or `sonnet`; `opus` is wasted on plumbing.
- `S01-X4` model `TITAN (via global master)` is not a model code from `OVERVIEW.md §1` (`muse/haiku/mistral/sonnet/opus/fable`).
**Fix:** Move `S01-X3` to `sonnet` (mechanical but blocks hard WPs); keep `L1`/`L3a` as `sonnet`; add verifier `sonnet` for `M5`; change `S01-M7` first pass to `sonnet`; change `S01-X4` to `opus` with note "executed via TITAN"; or document explicit deviation from `OVERVIEW.md §5`.

## F8 — major — stage-01.md §4 (Mathematical / Lean-technical errors)
**Problem:** WP descriptions contain mathematical inaccuracies that would cause Lean or LaTeX failures:
- `S01-L2` claims `QuatAlg.isCentral` "proved by computing commutant of i and j" — but `i²=a, j²=b, ij=-ji` with `a,b<0` in `ℚ` does not imply centrality over `ℚ` without `NeZero (2:ℚ)` and `a≠0, b≠0`; the statement as written omits the `[Field ℚ]` instance and conflicts with `Stacks` universe.
- `S01-L5a` `card_Gam_dvd_24` cites `card_unitGroup_dvd_24` but that import result includes the spurious `8` case (Lipschitz order, non-maximal, D=2) — the plan's own `prop:s01-finite` excludes 8 for maximal orders, so the lemma must strengthen the import; as stated it proves a superset.
- `S01-L9` `relIndex_K1_succ : (K1 p (s+1)).relIndex (K1 p s) = p²` contradicts `lem:s01-Up` proof text which says `[K_s:K_{s+1}]=p² (c and d each lose one power)` — the index is `[K_s:K_{s+1}]=p²` but the quotient claimed is `K1(p,s) / K1(p,s+1)` vs `relIndex` direction is reversed; the WP states the reciprocal.
- `S01-L8b` `normMap_heckeT (ν ∘ T_g = T_{g⁻¹} ∘ ν)` is stated for all `g` but `prop:s01-adjoint`(b) holds only for `g` supported away from `p` or trivial coefficients; the WP omits the restriction, so the Lean statement would be false for `U_p`.
- `S01-L4b` fallback "keep Ψ-levels for all index statements" contradicts `if:s01-mass` which promises the `U1(N)` level change with exact constants.
**Fix:** Correct `L2` docstring to include `[NeZero 2]`; strengthen `L5a` proof to exclude 8 using maximality; fix `L9` index direction to `(K_s).relIndex (K_{s+1}) = p²`; restrict `L8b` to `g` disjoint from `p`; remove the `L4b` fallback or add a `SORRIES.md` entry and mark `if:s01-mass` as stubbed.

## F9 — minor — stage-01.md §8 (Missing edges, wave assignment)
**Problem:** Wave table (W0–W8) lists `S01-X5` nowhere and places `M0` in W0 but `S01-M4` in W3 despite `M0→M4` (W1). `S01-L13` feeds `L14` at 325 but is scheduled at 365–410, so it is on the verge of the critical path but E5 is claimed "off critical path, slack ≥60". Inconsistency between DAG waves and §9 worker schedule.
**Fix:** Add `X5` to W2 (after X1), move `M4` to W2, and either move `L13` to W3 or increase its slack estimate to 0 and mark E5 as `merged-first` risk.

## F10 — minor — stage-01.md §2 (S01-X1) / OVERVIEW.md §3.5
**Problem:** X1 output lists `lean-toolchain` as byte copy of import's but `OVERVIEW.md §3.3` requires the lakefile to declare `maxSynthPendingDepth = 3` for `LanglandscapeVendorStacks` and the V libraries with `AlgJLVendor` leanOptions — the lakefile content described in X1 omits those options and omits the `titan/<job-id>` branch naming convention from `OVERVIEW.md §2`.
**Fix:** Update X1 outputs to include the exact `lakefile.toml` snippet from `OVERVIEW.md §3.3` (including leanOptions) and note the `titan/` branch prefix.

## F11 — minor — EXPERIMENT_PROTOCOL.md §1.3 / stage-01.md Strands
**Problem:** Strand table `E3` (`S01-C1` mistral vs sonnet) is labeled `code-routine mistral/sonnet` but the WP difficulty in §1 is `routine` while the code track default per `OVERVIEW.md §5` is `mistral` or `sonnet`; the cell therefore does not distinguish models. Also `E6` and `E7` share cell `mech mistral/haiku` with n=2 but are in different tracks (Lean-infra vs LaTeX) — track is part of the cell definition (`(track,difficulty,model pair)`), so they are not the same cell; n=1 each. `E7` condition "math-track slack ≥30" is checked against §9 which is not written yet (O5).
**Fix:** Split E6/E7 into two cells or define cell as `(difficulty,model pair)` only; mark E3 as exploratory; make E7 unconditional or tie it to the dependency slack (250 min) rather than the schedule slack.

## F12 — minor — EXPERIMENT_PROTOCOL.md §1.5 / §7.2
**Problem:** Lean slot accounting is contradictory: §1.5 says "at most 1 local slot is used by experiment lfile.sh" but §7.2 wrapper `exp_lean_loop.sh` does `flock exp.lock; our project's lfile.sh` which internally takes a node-wide slot via `lfile.sh` — the extra `exp.lock` does not enforce the "other slot stays with production" guarantee under the `OVERVIEW.md §3.4` lock model (`lean.lock` shared + per-checkout exclusive). No deadlock analysis for `lean.lock` shared + `exp.lock` + per-checkout lock ordering.
**Fix:** Specify lock ordering (`exp.lock` → `slot.N` → per-checkout) and that experiment checks never take `lean.lock` exclusive; add a timeout and `queue_min` handling for the deadlock case.

