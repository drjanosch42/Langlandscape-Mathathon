<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Slot-27 session resume file, 2026-11-13

Supersedes `slot26/HANDOVER_1112b.md`. Slot 26 is closed (owner sign-off 2026-11-12); **slot 27 is open**, plan `00-slot27-plan.md` v0.2.
Dev branch `hecke-extensions` (pushed). Owner rulings of this session: Q1 = yes (θ default flips to `lex_then_greedy` at the slot-27 end, HeckeZ
edition 4, G27 changed=15); LEV-K runs approved; HACS 0.2.1 public release **deferred to the owner's decision on 2026-11-14** (no release
candidate prepared, owner 08:15 UTC: "prioritise all implementation"). Nothing was pushed to the public `hacs` / `hacs-data` repos.

## Done this session (merged + pushed on `hecke-extensions`)

| Card | Commit(s) | Gate |
|---|---|---|
| TS-D design v0.2 + Fable audit | `TS_design.md`, `TS_design_audit.md` | audit B1 (CertVal false-certified) → TS-FIX |
| EXW-D design v0.2 + Fable audit | `EXW_design.md`, `EXW_design_audit.md` | M1–M5 applied |
| BIGNTT-D design v0.2 + audit | `BIGNTT_design.md`, `BIGNTT_design_audit.md` | B1 Garner ≈40 h, B2 pool → M1 |
| LEV-K design, audit, fixes, runs | `LEVK_*.md`, `docs/cluster/local/levk/`, `run5_levers.sh` | SAT-107 500/500, R-L23 30/30 (max 14.17 GiB): SAT_PERF, FORMS_NTT_CACHE, L23_RING2K/MOD3K/F3L qualify; MT/LEAN_PEAK/VNNI2 second reading; TILE_WORK, HOST_ELIM → RUN5; AVX2_PAIR → owner host-B ℓ=919 (`LEVK_runs.md` §3, now pushed) |
| TS-FIX (`GPIsBound`, KNOWN_ISSUES) | `58a85dd0` | `ED3_GP … verdict=NEUTRAL`, roster 291 |
| L691 (lattice arm (L), v_691(det)=1) | `764b0a93` | 897 checks |
| TS (θ order `lex` \| `lex_then_greedy`, default **lex**) | `c26b01af` | `TS_OLDORDER records=98 mismatch=0`, `TS_EXPLICIT_LEX records=18 mismatch=0` |
| EXW (free-block read under rule (α), HZ-EISUP attribution ℓ < 2^63) | `88b5f306`, `a0501530` | `HECKEZ_EXW … verdict=OK`, roster 292; one non-golden pin moved: (8,10,anemic) in `HeckeZRecordExpected.inc` |
| BIGNTT M1 (NTT product + Barrett, persistent pool; untrusted finder only) | `36300e81`, `a38478f5` | merged-tip `--all` 245/245, roster 293 |
| Code audits | `TSFIX_L691_code_audit.md`, `TS_EXW_code_audit.md`, `BIGNTT_M1_code_audit.md` | all ACCEPT / ACCEPT WITH FIXES, no B |
| EXW audit fixes M-EXW1 (per-set refusals) + M-EXW2 (`rss_lanes=16`) | `8ad383c6` | `--all` 244/244, `HECKEZ_EXW arms=11 … verdict=OK` |
| Z3b-F (F6, F7, arm (Tau)) | `1c4e365d` | `HECKEZ_XHOM_ORACLE arms=8 … teeth=291/291 verdict=OK` |
| **C128: [C] 1.28.0-pre.1 draft** (θ-SEARCH, HZ-EISUP (b), EXW, Q6 note) | merge `544b0235` | referee ACCEPT-WITH-CHANGES (0 B / 3 M / 10 m) all applied; 736 pp; **not signed** |
| JL side requests (Task 0, v6 Task 1) | out of tree: `$JL_EXCHANGE/` | delivered |

Golden untouched throughout (18385 / 12154 / 6231, `git diff 6508fd0c HEAD -- '*GoldenReference.inc'` empty).

## State at handover

- Tip `hecke-extensions` = see `git log -1` (≥ `563c9af4`). Roster **293** (`--all` 245). Merged-tip gate on `563c9af4` (TS+EXW+fixes+BIGNTT M1+Z3b-F+C128): `All validations PASSED (245/245)`, golden tier A 12154/0, tier B 6231/0, `LABEL_CENSUS … unresolved=0 stale=0`. Later merges on top (`6f36b47d`, LEV-K runs, HANDOVER) are docs only.
- **Branches not merged** (all on origin unless noted):
  - `s27-wip-eisupb` (`794160f3` code, `3e0be348` predictions + `eisupb_neutral.py`, `2b3151c0` gate 2: `--all` 246/246, golden 0/0; roster 294).
    **Merge gate running detached**: 85-record neutrality re-run, started 15:59:55 UTC, ETA ~20:00 UTC, log
    `$HACS_DATA/s27/eisupb/rerun/logs/chain.log`, verdict line in `rerun/logs/neutral.txt` — merge iff
    `EISUPB_NEUTRAL … moved_outside_rule=0`. Base is `2e3374a5`: re-run `--all` on the merged tip after merging (roster 294).
  - `s27-wip-bigm1b` (`ef248110`, base `544b0235`, pushed): BIGNTT M1b — per-worker invitation pool (pass cost T=16: 135 → 41–48 µs, independent of
    pool size), audit m1–m5 (m6 deferred to concurrent-θ). **Not gated**: needs `--all` (245) + GOLDEN_STRICT + `BigIntNttValidation`. Barrett step
    gains only 10–12 % at T=8/16; the remaining lever is serial work (carry, zero-fill, alloc) + concurrent θ (§13.1). Build dir
    `s27/bigm1b/build` kept for the gate.
- Open owner items: `docs/OWNER_TODO.md` — sign [C] 1.28.0-pre.1 (after EISUPb merges), Q7 ([LP] one-line `tb_mat` note, rec. yes), host-B ℓ=919 run
  (command block `LEVK_runs.md` §3), HACS 0.2.1 decision.

## START HERE (in this order)

1. Read `eisupb/rerun/logs/neutral.txt`. `moved_outside_rule=0` → merge `s27-wip-eisupb`, `--all` + GOLDEN_STRICT on the merged tip (expect
   roster 294 / `--all` 246), push; then an Opus code audit of EISUPb.
2. Gate + merge `s27-wip-bigm1b` (if not merged).
3. **Edition-4 path:** cut `s27-run5` = tip + the one flip commit (default `lex_then_greedy`, `kHZDefaultFingerprint` `0x325b510edad11c8d`, pins
   per `TS_design.md` flip list incl. audit M3, `TS_OLDORDER_FLIP records=41`); `run5_levers.sh`; teach `mk_hecke_dataset.py` the new keys
   (EXW G10 `…exw`; EISUPb `theta_poly`, `U_<p>.charpoly`, `psi_cond`, `psi_order`); `RUN5_predictions.md` (measure (26,12), (341,0)).
   Then R2089 ∥ RUN5 → edition 4 → G27 (changed=15, referee) → owner signs [C] 1.28.0 → release 0.3.0.
4. Deferred decisions: `HeckeZExportWordValidation` ≈131 s on a loaded box — measure in a quiet window; > 100 s → arms (E)(F)(J)(K) to a slow
   sibling. EXW env arm on the nine class-A level-1 records n ≥ 166 (2–4 h) before RUN5. BIGNTT M2 (Garner memo + prefix cover).
5. Remaining slot-27 cards: NB-B, TOOLS, XPL, LEV27 (retire levers after RUN5), R2089.

## Box, disk, peers

- TRACE FORMULA Lean window of 12:05 ended early at 14:46 UTC. Box rule: ≤ 2 heavy C++ jobs; during a TF window ≤ 10 GiB total, both
  `s27/build.lock` and `s27/gate.lock` for any heavy job. Disk `/mnt/c` ≈ 155 GB free.
- Detached at handover: the EISUPb re-run (4 threads, ≤ 9.5 GiB watchdog, ETA ~20:00 UTC).
- **TRACE FORMULA window 18:10 – ~22:10 UTC (2026-11-13)** (full audit, ≤ 16 GiB): no new heavy job of ours until TF's "ends"; the EISUPb
  re-run (≤ 9.5 GiB) was acknowledged to TF as inside our ≤ 10 GiB budget.

## Process lessons

- Agents often finish without messaging, or miss their own build-done event (z3bf, exwfix, eisupb this session): poll `ls -t` of their scratch
  logs and `git log` of their branch at every check-in; nudge after 30 min of silence.
- A merged-tip gate after each pair of merges caught nothing this session but is cheap insurance; run it when two packages share files
  (roster counts, CLAUDE.md, catalogue).

## Addendum 21:05 UTC — EISUPb merge-gate result

`EISUPB_NEUTRAL records=85 expected=85 neutral=82 contract_moved=85 provenance_diffs=652 in_scope=0 missing=0 moved_outside_rule=3
verdict=FAIL` (chain done 20:13:53 UTC; `s27/eisupb/rerun/logs/neutral.txt`). The three violations are exactly the EXW full records
`(167,0)`, `(173,0)`, `(197,0)` full: `G2.ell=<ℓ>.generation.status` `refused(export_word)` → `certified` (route `saturation`,
`decomposed_by theta=(1 0 0 0)`), `G0.status` pending → final. These are **EXW's rule-(α) moves** (EXW env arm `HECKEZ_EXW_ALL cells=3 final=3`,
`a0501530`), present because the EISUPb branch base `2e3374a5` already contains EXW; `in_scope=0` — no (b) record moved. The gate tool
`eisupb_neutral.py` compares against edition 3 without EXW's diff rule. **Next:** teach `eisupb_neutral.py` EXW's §5 diff table (attribute
first to EXW, then EISUPb, as `EXW_design.md` §5.1 prescribes) and re-evaluate the existing outputs (no re-run needed); expect
`moved_outside_rule=0`. Then merge as in START HERE 1. TRACE FORMULA's 18:10 window ended 21:00 UTC (rc 0).
