<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Slot 27 — plan v0.2 (2026-11-12)

**Status: v0.2, planning stage 2** (staged planning, owner 2026-11-03: a fresh agent per stage, an audit between stages). v0.1 (`a92845a1`,
merged `007e8045`) was written from the seed `00-slot27-seed.md` v0.1 (`cae1c769`), `slot26/CLOSE_report.md` §7–§9, `slot26/HANDOVER_1112b.md`,
`docs/OWNER_TODO.md` (Q5, Q6 ruled 2026-11-12), the θ-SEARCH stub of `slot26/00-slot26-plan.md` §2.2 and `slot26/THETACAP_diag.md`,
`slot26/HZEISUPb_design.md` v0.4 + `HZEISUPb_C_draft.tex` v0.4, `slot26/Z3b_report.md` / `Z3b_code_audit.md`, `slot26/NBMATH_plan.md`,
`slot26/F3_scout.md`, `slot26/LEVERS26_report.md`, `docs/integral_census/results/hecke_ed3/README.md`, `slot26/R4_report.md`. **v0.2 applies every
finding of the plan audit `00-slot27-plan_audit.md` (ACCEPT WITH FIXES: B1, M1–M6, m1–m10) as the audit proposes; the response table is §8.**
Docs only; nothing was built or run for this plan (a peer holds the box). Everything not marked **[OWNER]** is **taken at the recommendation**
(§6 lists each such decision). Next: wave 0, then wave 1.

**Starting state (from `CLOSE_report.md`; owner signed the slot-26 close 2026-11-12).**

| fact | value | source |
|---|---|---|
| close tree / binary of record = **slot-27 REF** | `5bd70691`; `$HACS_DATA/s26/close/build/hacs`, sha256 `0629ad13428172fa9b61b3b2aa66b870db24727f381e5418484b62475c206e8a` (keep it and `s26/close/src`) | `CLOSE_report.md` §1 |
| roster | **290** = 75 / 167 / 48, `--all` 242, `EXPECT_NAMES` 290 | CLAUDE.md |
| golden | **18 385 / 12 154 / 6 231**, R0 **`6ca88605`**; HZ settings fingerprint `0x8ffc29730c4f9672` (`kHZDefaultFingerprint`, `GoldenHarness.cpp:2710`) | CLAUDE.md, `GoldenHarness.cpp` |
| digests | EngineDet `0x3dddd2ef9a8efd`, ExtDet `0xaef77d786b4f29b4` (heavy `0x9ed8b83a2fb26622`), ConsoleDet C4 (a) `0xf6ed04bbe8e6b60a`, Smoke `COMPLETED and CERTIFIED` | CLAUDE.md |
| Lean | `decls=3971`, replay 297/297 `verdict=OK` | `CLOSE_report.md` §5 |
| contracts | [C] 1.27.0, [E] 1.25.3, [U] 0.8.1; [CLI] 1.5.14, [PG] 1.5.5, [EX] 1.5.0-pre.5; [P] 3.15.0-pre.8 (NBMATH stage A, merged `764205d7`) | `HANDOVER_1112b.md`, `764205d7` |
| NBMATH | stage A **merged** (`764205d7`, branch tip `e9978793`); **not** in the merge: C1 "Copy as LaTeX", the stage audit, `notebook_close_check.sh` on the merged tip, `--all` on the merged tree | audit M1 |
| HZ-DS | edition 3: 226 records (56 level-1 `full`, 85 `full` N > 1, 85 `anemic`), 3 pending (`refused(export_word)`, N = 167, 173, 197); not computed (2089, 0) anemic (finished on `21a00a01` as `0x413643d80b5153a8`, not accepted), (2089, 0) full (≈ 50 GiB, extrapolated from one point), (1, 484), (1, 700), (1, 702) | `hecke_ed3/README.md` |
| shared binary | `s26/bin/hacs` is still rc3; **`s27/bin/` does not exist** | `HANDOVER_1112b.md` |

**Headline outcomes.** (1) The θ search of `HeckeZRational` stops failing on structure: the 19 + 2 `open(cap)` probe cells of HZ-EISUP (b) become
reachable, and the ψ ≠ 1 Eisenstein systems (HZ-EISUP (b)) exist over Z, under [C] 1.28.0-pre.1. (2) The 20 `refused(export_word)` records get a
route (at-root read for ℓ ≥ 46341). (3) **Frontier (standing goal "push the limits"):** the level-1 HeckeZ wall moves — the NTT big-integer finder
of F3 rows 2–4 brings (1, 484) from 160–360 h toward hours and makes (1, 700) / (1, 702) plannable; (2089, 0) anemic is recomputed in its own lane;
(2089, 0) full gets a measured basis for a kit. (4) One integral re-run under the new settings: HZ-DS edition 4, one owner-gated golden event
(`changed=15`). (5) The notebook finishes NBMATH stage A (C1, audit, checks on the merged tip), then B1/B2. (6) The 11 deferred rollback levers
and `ENGINE_VNNI2_FLOOR` get runs that **can** retire them (LEV-K makes the `EFFECTIVE` lines exist first); each retires at the close on such a
run or defers to slot 28 with the reason stated.

## 0. Rules for every wave (carried from slot 26 §0; changes marked)

- **Agents.** ≤ **5 concurrent subagents**, ≤ **3 if one of them is Fable** (lead's brief 2026-11-12; audits and referees count). One fresh agent
  per package; TaskStop on completion; check a background agent's output within 30–60 min. Opus implements; mechanical packages Sonnet; audits
  Opus adversarial; **Fable only for the three audits marked "Fable-preferred" below, and only if its quota allows** (else Opus).
- **Priority rule (new, audit m7).** When agents or the box are short, the order is: critical path (TS-D → TS → C128 → EISUPb → RUN5 → G27) and
  LEV-K, then **BIGNTT and EXW** (frontier), then NB-A′ / NB-B, XPL, TOOLS, Z3b-F, L691. An audit takes the agent slot of the package it audits
  (it starts when that package returns).
- **Box.** C++ ≤ 12 GB host summed: ≤ **two heavy jobs** (a `-j8` build 3.2–3.8 GiB, or an `--all` ≤ 6.3 GiB) under `s27/build.lock` /
  `s27/gate.lock`; other runs ≤ 3 GiB unless a card predicts more (rule 19). A detached run counts toward the 12 GB. `disk_guard.sh` before each
  configure; C: warn ≤ 20 GB, pause ≤ 10 GB. Every heavy run gets a start and an end line in `$HACS_RUN_LOG` **in UTC** (`date -u`; slot-26
  lesson 1); timing verdicts only in a quiet window granted through the lead.
- **Lean** (only if a package touches `lean/`): `flock -x $HOME/.cache/gl2tf/lean.lock` (shared with TRACE FORMULA), ≤ 22 GiB, plain
  `lake build`, never `lake update`, `lean_census.sh --emit` in the same commit. No slot-27 card plans Lean work; [C] 1.28.0-pre.1 adds no LEAN marker.
- **Scratch** `$HACS_DATA/s27/<pkg>/`, one build dir per agent, deleted after merge. Shared or long-running binaries from
  the detached checkout `s27/src`, never a worktree.
- **`s27/bin` refresh.** `s27/src` re-detached at, and `s27/bin/hacs` rebuilt from, every merge that changes a record, a dump emitter or a
  validation; one row per refresh in `s27/bin/SHA256_LEDGER.md` (merge commit, `s27/src` HEAD, sha256, date, trigger). Relative symlink
  `cohomology_app -> hacs` (copy with `cp -P`). Consumers name the ledger row. Never refreshed while a detached run reads it (that run has its own
  checkout `s27/run/src`).
- **Run provenance (new, audit M4).** Every detached record-writing run (RUN5, R2089, (1, 484)) is built from **a commit on a pushed branch**, never
  from a dirty tree (slot-26 F9); the commit is named in the run's `*_predictions.md` and its kit.
- **Registration.** `src/hacs/Registry/Slot27/<Name>.cpp` (`RegisterSlot27<Name>()`, tail of `RegisterAllValidations()`) + `cmake/slot27/<Name>.cmake`;
  the first package creates both and `Registry/Slot27/README.md`. Roster changes merge one at a time under `s27/merge.lock`, with
  `gen_cli_manual_tables.sh`, `EXPECT_NAMES` and the catalogue entry in the same commit. Each later branch rebases and regenerates before its merge.
  After each merged package `hecke-extensions` is pushed (push on milestone).
- **HeckeZ brief rule.** Every new integral computation (θ-SEARCH, EISUPb, EXW, BIGNTT) states its parallel decomposition (RNS over word primes,
  rank, entries; AVX-512 / AVX2 / CUDA; GPU opt-in, CPU = golden path; sparse mod-ℓ / Dixon, no dense HNF over Z beyond a small core) and ships a
  **route bit-identity validation** (threaded vs serial, every ISA / device route vs the portable one).
- **HZ hash invariance — changed for slot 27.** On `hecke-extensions` every package on a HeckeZ path reads the two lines of slot 26 (fingerprint
  `0x8ffc29730c4f9672` unchanged; the 15 `HZ_N1_n<n>_full` lines byte-identical) **until the G27 landing**. TS merges with the old order as the
  default and with the **old-order value serialising to the edition-1–3 settings text byte for byte** (TS-D's text rule, §2.1), so TS's own merge
  keeps both lines too. The default flips only on the branch `s27-run5` (§2.1 RUN5) and lands on `hecke-extensions` only in G27 (§5 K3). After G27
  the new fingerprint is the invariant.
- **"Every C++ package" row:** `git diff <base> -- '*GoldenReference.inc'` empty; `GOLDEN_STRICT=1 ./hacs GoldenRegressionValidation` → tier A
  **12154 failing 0**, tier B **6231 mismatching 0**; the digests above; `LABEL_CENSUS … unresolved=0 stale=0`; `ADD_SPDX_CHECK … verdict=OK`;
  `LicenceGuardValidation … verdict=OK`; `--all` green (242 + the package's names); `CliManualCoverageValidation`, `ConsoleScriptValidation` PASS.
- **Contract first** (06 §1 rule 1, owner-signed 2026-11-04). A package implementing a new statement of `sec:heckeZ` / record item 8 merges only
  after the [C] pre-release carrying it is refereed ACCEPT; code may start on the draft. Slot 27 has **one** [C] pre-release line, 1.28.0-pre.k
  (§2, C128), carrying θ-SEARCH, HZ-EISUP (b), EXW's words (if any) and the Q6 note.
- Per package: `<PKG>_predictions.md` (before any run), `_report.md`, `_code_audit.md` / `_referee.md` in `slot27/`, each committed the turn it returns.
- **Slot-26 process lessons carried:** `cross_config.sh` per-arm `*.out` copied out before the `rm -rf`; a lever retires only on a run whose
  `EFFECTIVE` lines were read (no repeat of the (R-a) deviation); a CLAUDE.md restructure is audited for lost qualifiers; commit early.

## 1. Wave 0 — lead (no subagent)

1. Sign-off edit in CLAUDE.md "Slots" (slot 26 closed, slot 27 open, this plan); `docs/OWNER_TODO.md`: tick Q4 (explorer licence, **ruled
   2026-11-08**: code LGPL-3.0-only WITH LicenseRef-CUDA-exception, data CC-BY-4.0, `.cxf` field at the next export, Cite-as until a DOI — the
   OWNER_TODO line 20 is stale) and move the θ-SEARCH "Decide" line to this plan.
2. If not done before the sign-off: the **C6 addendum** (7 + `legacy-vnni-off` `cross_config.sh` arms with `*.out` kept,
   `HANDOVER_1112b.md` START HERE 1), recorded as an addendum to the slot-26 close report; a failure reopens that close.
3. **P0 (seed item 9).** `s27/` locks (`build`, `gate`, `gate.wait`, `merge`); detached `s27/src` at the slot-26 close commit (or the merged tip if
   only docs differ); `s27/bin/hacs` + `.sha256`, `cohomology_app -> hacs`, `SHA256_LEDGER.md` first row. Retire `s26/bin` (rc3) from use.
4. **Seed item 8.** `pg_census_check.py`: default the data root to `$HACS_DATA`, falling back to `$HACS_DATA`, with a
   one-line usage note (tooling only; a lead commit or the first Sonnet package).
5. Standing line in `$HACS_RUN_LOG`: slot 27's heavy-job rule and the pass-5 sum (§4).
6. Brief the owner on **Q1 only** (§6), with this plan and its audit. The run questions (old Q2) are **not** asked in this round: they are asked
   after LEV-K returns, with its costs (§6, "Asked later").

## 2. Work packages

Sizes: S ≤ 1 agent-session, M 2–4, L 5+. Columns of the impact table (§2.0): **G** golden moves, **ID** record ids move, **R** roster changes,
**C** [C] text changes.

### 2.0 Overview (in order of work)

| # | pkg | one line | size | tier / audit | G | ID | R | C |
|---|---|---|---|---|---|---|---|---|
| 1 | **NB-A′** | finish NBMATH stage A: C1 "Copy as LaTeX" (page only), the stage audit, `notebook_close_check.sh` on the merged tip, `--all` on the merged tree | S | Sonnet (C1 + checks); Opus audit | no | no | no | no |
| 2 | **TS-D** | θ-SEARCH design note + [C] text draft (order at **both** implementation sites, settings mechanism and text rule, impact count from a grep, landing mechanics) | M | Opus; **design audit Fable-preferred** | — | — | — | draft |
| 3 | **EXW-D** | at-root read for ℓ ≥ 46341 (`refused(export_word)`, 20 records) — design | S | Opus; Opus audit | — | — | — | draft if new words |
| 4 | **BIGNTT-D** | F3 rows 2–4: NTT big-integer finder + sub-quadratic CRT / radix at level 1 — design (names the CUDA home) | M | Opus; Opus audit | — | — | — | no |
| 5 | **L691** | assert the index-691 lattice at (10, 691) over Z/691² (det 415291 = 601 · 691) | S | Sonnet; Opus code audit | no | no | arm only | no |
| 6 | **LEV-K** | **new (audit B1):** make the lever runs able to retire levers: per-lever `EFFECTIVE` table, the line made to exist, host-B kit re-pinned and sized, the `ENGINE_VNNI2_FLOOR` run named or deferred, owner of the returns | S–M | Opus; Opus audit | no | no | 0–1 | no |
| 7 | **TS** | θ-SEARCH code (critical path), old order default, new order selectable | M | Opus; Opus code audit | no (flip at G27) | no (flip at G27) | +1 | via C128 |
| 8 | **EXW** | the at-root read route, code | M | Opus; Opus code audit | no (until RUN5) | no | +1 | via C128 if any |
| 9 | **BIGNTT** | NTT big-integer finder, Garner / radix, GPU opt-in | L | Opus; Opus code audit | no | no | +1 | no |
| 10 | **C128** | [C] 1.28.0-pre.1: θ-SEARCH text + HZ-EISUP (b) (draft v0.4) + EXW words + Q6 legacy-only note | M | Opus editor; **referee Fable-preferred** | no | no | no | **yes** |
| 11 | **EISUPb** | HZ-EISUP (b) code, ψ ≠ 1 (after TS merged and C128 refereed); merge gate = the 85-record neutrality re-run | M | Opus; Opus code audit | no (until RUN5) | no | +1 or arms | via C128 |
| 12 | **NB-B** | NBMATH B1 (HeckeZ record typed hints) then B2 (`les` hint) | M | Sonnet/Opus; Opus audit | no | no | no (data rows) | no |
| 13 | **Z3b-F** | Z3b audit F6 (M≠0 counter), F7 (reset globals); the τ follow-up oracle π(R T^× g_i) ≡ τ π(R g_i) on the socle | S–M | Opus; Opus audit | no | no | arms | no |
| 14 | **TOOLS** | `box_watch.sh` per-sample CPU delta (slot-25 audit S2) | S | Sonnet | no | no | no | no |
| 15 | **XPL** | census explorer into `hacs-data` (local; push is the owner's) | M | Sonnet; Opus release audit | no | no | no | no |
| 16 | **RUN5** | HZ-RUN pass 5 on the pushed branch `s27-run5` (TS flipped) → **HZ-DS edition 4** (226 recomputed + EXW finals + new (b) cells; + R2089 if it finishes); incl. the overlay-root tool | M (run) | Opus; Opus dataset audit | feeds G27 | **yes** | no | no |
| 17 | **R2089** | **new lane (audit M6):** (2089, 0) anemic, detached, first and in parallel with RUN5; does **not** block edition 4 | S (run) | Opus (RUN5's agent); dataset audit with RUN5 | no | yes (that record) | no | no |
| 18 | **LEV27** | retire the 11 deferred levers + `ENGINE_VNNI2_FLOOR` on the runs LEV-K made qualifying, or defer each with the reason | S–M | Opus; Opus lever audit | no | no | arms out | Q6 note only (in C128) |
| 19 | **G27** | golden event: **`changed=15`** (the `HZ_N1_n<n>_full` set, new fingerprint), `added=0` | S | Opus; **referee Fable-preferred** | **yes** | — | no | no |

Stretch (§2.4): (2089, 0) full basis + kit; the (C3) K = 1 route (`refused(k1_route)`, 2 records); [PG] C2 (`print` → `display`); H4 Hida rung
route; `legacy-shadow` under `--all`. Tracked, not carded: the quaternion stage with TRACE FORMULA (Conv v1 recheck m2–m7, M8 Shimizu weights;
`QCONV_tools/qconv_check.py`; Lean pins differ, shared `lean.lock`).

**Predicted roster after the slot (audit m9):** 290 + TS 1 + EXW 1 + BIGNTT 1 + EISUPb 0–1 + LEV-K 0–1 = **293–295** (L691, Z3b-F, NB-B add arms or
data rows only; LEV27 removes none: retired arms keep their validation names). TS's order key is a `RationalSettings` field (§2.1, mechanism (a)), so
**no** console setting, no [P] change and no CLI-table row comes from it; if TS-D finds (a) unreachable from the campaign spec and chooses (b), add
the console setting, [P], [X] and the CLI tables to TS's scope and say so in the design audit.

### 2.1 Core — the integral line

#### NB-A′ — finish NBMATH stage A (replaces NB-A; audit M1)

- **Goal.** NBMATH stage A is merged (`764205d7`, 2026-11-12). What the merge did not carry, and nothing else owns:
  (i) **C1 "Copy as LaTeX"** (`NBMATH_plan.md:180`): a button per value and per text cell exporting the TeX the page already builds — page only
  (`notebook/page/`), not in the merge today; (ii) **the stage audit** of `NBMATH_plan.md:190` (no audit file exists): Opus, on the merged state
  plus C1; (iii) `docs/matrix-engine/tools/notebook_close_check.sh` on an `OC_BUILD_NOTEBOOK=ON` build of the **merged tip** (the recorded
  `GATEWAY_TEST` / `RENDER_TEST` lines are from the branch tip `87b49057`); (iv) `--all` on the merged tree (the merge message defers it).
- **Work.** C1 by a Sonnet agent on a branch (page only); (iii) and (iv) run on that branch's tip (it contains the merge); the audit reads the
  branch. NBMATH questions 1–8 stay taken at the recommendations (§6).
- **Acceptance.** `GATEWAY_TEST … verdict=OK`, `RENDER_TEST … verdict=OK` (read the lines) on the merged tip + C1; `--all` 242/242; no `src/`,
  roster, transcript, golden, [PG] or CLI-table change (`git diff --stat` shows `notebook/`, `docs/console/` only); KaTeX `throwOnError: true` on all
  formulas; C1 copies the same TeX the page renders (a fixture per cell kind in `test_render.mjs`); audit verdict ACCEPT (or its fixes applied).
- **Parallel.** With everything; **not** a wave gate (the wave-1 gate no longer names it).

#### TS-D → TS — θ-SEARCH (critical path)

- **Goal.** Replace the lexicographic θ search by one that cannot spend the cap on a low-dimensional span. Owner ruling 2026-11-12 (Q1 of
  HZ-EISUP (b)): a separate card; HZ-EISUP (b) code waits for it.
- **Two implementation sites (audit M2).** (1) `RationalStep` (`Integral/HeckeZRational.cpp` l. 1256–1311; `theta_cap = 64`,
  `theta_coeff_max = binom(d,2)`, settings text l. 463); (2) **`Integral/HeckeZRecord.cpp` l. 611–712**, which re-implements "the first θ of
  theta_search's order" for `heckez.maximal_ideals` (loops l. 697, 708; uses l. 1430, 1559–1567) with a **different predicate** (the reduction mod ℓ
  generates A′₁), where "maximise deg Rad" has no direct meaning. **TS-D defines the new order at both sites, or states why site (2) keeps the old
  order**, and what the settings line then says.
- **The design note must meet the five requirements of `THETACAP_diag.md` §4**: (1) an order that does not fill the cap on one span (ℓ¹-weight over
  all operators, `f1_l1.py`); (2) evaluate the **cap-free greedy per-operator search** (θ_i = θ_{i−1} + c_i o_i, c_i ≤ binom(d,2)+1, complete in
  ≤ m(binom(d,2)+1) charpoly tests) and choose its stopping rule; (3) predict with **all d systems, cusp included** ("17 of 21" is an Eisenstein-only
  upper bound), or by re-running a scratch build; (4) count the e^an = 1 `open(cap)` records of edition 3 that the new order moves; (5) acceptance on
  (25, 2) → θ = T_3 + U_5, (45, 0) → T_7 + U_3 + U_5 (under ℓ¹; the greedy's θ if chosen), and the four cells certified today ((9,0), (18,0),
  (25,0), (49,0)), with the settings fingerprint moving.
- **Third candidate to evaluate (audit M2).** **Old order first, greedy continuation only when the cap is reached.** Every record that certifies
  today keeps its θ and every hashed word except the settings line, so the 15 golden changes and the final records of edition 3 are explained by one
  sentence ("only the settings line moved"). TS-D compares the three candidates on cost and on the size of the explanation.
- **Recommendation for the design (to be confirmed by TS-D).** The old-order-first candidate if it reaches the 19 + 2 `open(cap)` cells at ≤ 2× the
  old search's typical cost on edition 3 (smallest explanation); otherwise the greedy per-operator search (provably complete, bounded worst case);
  the ℓ¹ order is the fallback.
- **Settings mechanism and text rule (audit M2).** The new order is selected by **(a) a field of `RationalSettings`** (text `hz_rat/v1;…`,
  `HeckeZRational.cpp:463`) reachable from the campaign spec — taken at the recommendation; not (b) a twelfth `MathSettings` key (console `set`,
  CLI tables, [P], [X], served `settings` JSON). Either way **the old-order value serialises to the edition-1–3 settings text byte for byte** (no new
  key printed at that value). Under (b) `MathSettings::canonical_text()` omits keys at default (`HeckeSettings.cpp:546`), so after the flip the new
  default would print nothing and the old order a new line — the wrong way round; (a) avoids that. Without this rule "editions 1–3 stay reproducible by
  their settings line" and "TS merges with golden unmoved" would both be false.
- **Impact the note states before any code** (every item a count, **taken from a grep, not from memory**): which hashed words of the 226 edition-3
  records change besides the settings line (θ, `G1.theta_ops`, `p0`, components, maximal ideals, `open(cap)` → `certified`); the 15
  `HZ_N1_n<n>_full` golden objects (all move: the object hashes the whole record, settings text included, `GoldenHarness.cpp:2691–2697`);
  `kHZDefaultFingerprint` (`GoldenHarness.cpp:2710`); **the validation pins**: `HeckeHidaEisLambdaValidation.cpp:86`,
  `HeckeZUpValidation.cpp:458, 479, 529`, `HeckeZEisUpValidation.cpp:312, 421` (l. 421 compares against embedded edition-1 record hashes);
  **the scripts**: `hz_dataset_verify.py` `PINS` / `PINS_ED2`, `docs/cluster/local/heckez/mk_heckez_run.py:51–55`, `mk_hecke_dataset.py`; any console
  transcript or ConsoleDet arm that prints an HZ record id (arm (c) throws on a fingerprint mismatch); **the [C] sites**: `gl2_contract.tex`
  l. 16949–16980, 17166–17173, 17261, 17282, the caps text frozen with v1 (l. 83), and **l. 16974, which states the fingerprint
  `0x8ffc29730c4f9672` in binding text** — hence the C128 text. (The fingerprint in the change-log paragraphs l. 33838 ff. is historical and stays.)
  The G27 flip commit's list of touched files is this grep's output.
- **Landing mechanics (audit M4).** TS merges with the **old order still the default** and the new one selectable and validated. The flip — default,
  `kHZDefaultFingerprint`, the validation and script pins, [C] l. 16974's word (as C128 words it) — is **one commit on the pushed branch
  `s27-run5`** (= TS, EXW, EISUPb merged + that commit). RUN5 and R2089 are built from `s27-run5`; the G27 scratch emission is made from it; the
  in-tree emission is the G27 landing commit on `hecke-extensions`; **nothing of `s27-run5` is merged before the landing** (§5 K3).
- **Merge gate of TS (audit M3).** On the TS branch binary with the **old default**: (i) re-compute **every edition-3 level-N record that ends
  `open(cap)`** and the **80-record P4b class** (≈ 1.6 h, ≤ 3.4 GiB, `HZEISUP_rerun.md:48`), each `record_fnv1a64` byte-identical to edition 3
  (`TS_oldorder_identity.tsv`, a gate line `TS_OLDORDER … mismatch=0`); (ii) the "every C++ package" row (golden unmoved, fingerprint unchanged).
- **Validation.** `HeckeZThetaSearchValidation` (standard): the six acceptance cells under the new order, `open(cap)` → `certified` where predicted,
  the old order reproducing edition 3's θ on the four certified cells; both implementation sites covered; route bit-identity (threads 1 vs 16).
- **Parallel decomposition.** The candidate tests are independent charpoly evaluations over the 3 probe primes: parallel over (candidate, prime)
  in batches, first-success by index (deterministic). Cost note in `TS_predictions.md`, including the workspace RSS of parallel candidate batches
  (several charpoly workspaces live at once; audit m3).
- **Contract.** [C] item 8 (d′) words change → contract first: the flip (on `s27-run5`, landing in G27) needs C128 refereed ACCEPT; TS's merge with
  the old default does not, **because of the text rule above** (no written word or byte changes at the default).
- **Audit.** Design audit **Fable-preferred** (it decides a settings event that moves every record id); Opus code audit.

#### EXW-D → EXW — at-root read for ℓ ≥ 46341

- **Goal.** A route for `refused(export_word)`: the level-N EXPORT has no 64-bit word for ℓ ≥ 46341 (`HZLOC_report.md` l. 123–127); 17 non-full
  records of edition 1 plus the 3 `full` N > 1 records N = 167 (ℓ = 5103536431379173), 173 (ℓ = 5608385124289), 197 (ℓ = 35217676193989), each with
  (C1) `certified` and one ℓ-field (`C126pre9_referee.md` l. 155). F3 row 6.
- **Design note decides:** the at-root read (the read of T_ℓ at the root of the ℓ-adic tower without a 64-bit export word: u64 / two-limb word,
  RNS over word primes, or the HZ-LOC 64-bit item's precedent, `HZLOC_report.md` §0); whether it writes new words ([C] item 8 → C128) or only
  turns `refused(export_word)` into the existing final words; the (C3) K = 1 route for `refused(k1_route)` (2 records, ℓ ∈ [2^31.5, 2^63)) as
  in-scope or stretch.
- **Acceptance.** The 3 full records final on a scratch run (values cross-checked against an independent modulus where one exists); route
  bit-identity; the HZ hash-invariance reading (no record outside the 20 changes a byte).
- **Records** are written only in RUN5 (under the new settings), not by EXW itself.

#### BIGNTT-D → BIGNTT — the level-1 frontier (standing goal)

- **Goal.** F3's top frontier lever (`F3_scout.md` §0 item 1, rows 2–4): HZ-RAT's untrusted finder `BigProbablePrime` (12 MR bases + isqrt,
  schoolbook `nf::BigInt`, O(bits³)) and the O(K²) Garner / radix conversions dominate level 1 at K ≳ 3·10⁴ word primes. Today (1, 484) ≈ 160–360 h,
  (1, 700) / (1, 702) ≈ 3 200–10 000 h each (`HZRATPERF_report.md:133–135`). Target (derived in F3): (1, 700) ≈ 3–10 h each after rows 2 + 4.
- **Design.** NTT multiplication over word primes (RNS; AVX-512 butterflies; the CUDA route opt-in, CPU golden), Montgomery / Barrett on top,
  product-tree CRT and sub-quadratic radix conversion (row 4). `NumberField` stays **STL only** (`check_numberfield_includes.sh`), no `__int128`
  without `-DNF_NO_INT128`, no external bignum (owner 2026-10-03). **The CUDA NTT cannot live in `NumberField` (audit m5):** BIGNTT-D names its home
  (recommended: `EngineCuda`, reached from `NumberField` through a registered function-pointer hook that is null in CPU-only builds, so
  `NumberField` keeps no CUDA include) and states the include-guard consequence (`check_numberfield_includes.sh` unchanged; a stub in
  `CudaStub.cpp`). The finder is untrusted (its output is certified downstream), so records are byte-identical by construction; the validation proves it.
- **Acceptance.** `BigIntNttValidation` (standard): NTT product = schoolbook product on random and adversarial sizes, every ISA route vs portable,
  GPU vs CPU where built; HZ records (1, 138), (1, 174), (1, 268) byte-identical to edition 3; the measured wall law at (1, 174) / (1, 268) and the
  extrapolation to (1, 484), (1, 700), (1, 702) in the report (frontier movement stated, rule of the standing goal). HZ hash invariance (both readings).
- **Size L**: may finish in slot 28; its design note splits it into a mergeable first half (NTT multiplication + finder) and a second (Garner / radix).
- **Runs (decoupled from RUN5, audit m6).** (1, 484) runs as **its own detached cell** whenever BIGNTT's first half has merged, on a pushed commit
  that contains the flip (under Q1 = yes: `s27-run5` rebased onto that merge, or a later run branch), with its own prediction; it joins edition 4 as an
  **addendum** through the overlay-root tool (RUN5 item), not by waiting for RUN5. (1, 700), (1, 702) only with a kit and an owner launch.

#### C128 — [C] 1.28.0-pre.1

- **Content.** (a) θ-SEARCH: the item 8 (d′) words of the search, the caps text, and l. 16974's fingerprint sentence (from TS-D; the words valid
  after the flip); (b) HZ-EISUP (b): `HZEISUPb_C_draft.tex` v0.4 (`prop:heckeZeisupchar`, the (d′)(ii) paragraph, the (d′)(vii) per-binary sentence,
  (ix), the status row; referee and confirm read ACCEPT-WITH-CHANGES already applied); (c) EXW's words if EXW-D says so; (d) **Q6 note** (owner
  2026-11-12): one line, "env rollbacks live only in `OC_ENABLE_LEGACY=ON` builds", legacy-only.
- **Order (audit m8).** Drafted once **TS-D's text and EXW-D are audited**; referee (**Fable-preferred**) on the θ-SEARCH and EXW parts (the (b) part
  has had its referee; a confirm read suffices); PDF rebuilt, committed, mirrored to `gdrive:…/refs/latex/original-pdfs/` (md5 verified). Signing
  1.28.0 is the owner's.
- **Gates.** `LABEL_CENSUS … unresolved=0 stale=0`, 0 undefined refs, LEAN markers 229 on 88 unchanged.

#### EISUPb — HZ-EISUP (b) code (ψ ≠ 1)

- **Goal / design.** As `HZEISUPb_design.md` v0.4 D1–D8 (Galois-orbit products over Z, the cut E = ker P^Eis_{q0}(T_{q0}), certification by exact
  multiplication; records per binary `G10.contract`). After **TS merged** (owner ruling) and **C128 refereed**.
- **Scope note.** Edition 3 has **0** records in scope (D7); with the new θ search the four certified probe kinds plus whichever of the 21
  `open(cap)` probes TS certifies become in scope. Their entry into the census grid is RUN5's choice (§2.1 RUN5).
- **Validation.** `HeckeZEisUpCharValidation` (standard, ≤ 60 s, ≤ 0.4 GiB, design §7) or new arms of `HeckeZEisUpValidation`; route bit-identity.
- **Merge gate: neutrality re-run (audit M3).** The design's own re-run (§8 of `HZEISUPb_design.md`): the **85 `full` N > 1 records** on the
  **EISUPb branch binary with the old default**, ≈ 4.0 h, peak ≤ 8.0 GiB (rule 19, announced), each record byte-identical to edition 3 except
  `G10.contract` (design §5.5, l. 441–443), gate line `EISUPB_NEUTRAL … moved_outside_rule=0`. (It cannot be read on RUN5's records: RUN5 runs the
  flipped default, so no `record_fnv1a64` equals edition 3.)

#### RUN5 — HZ-RUN pass 5 → HZ-DS edition 4

- **Goal.** One re-run of the integral census under the new default settings (TS flipped, EISUPb, EXW; BIGNTT if merged), detached from
  `s27/run/src` checked out at the **pushed branch `s27-run5`** (= TS, EXW, EISUPb merged + the one flip commit; §0 run provenance), giving
  **edition 4**: every record id new; the 20 `export_word` records final where EXW reaches them; new grid cells with cond(ψ)² | N (9 | N, 16 | N,
  25 | N …) chosen by the design note of TS-D / EISUPb at ≤ the probes' cost. (2089, 0) anemic is **not** part of RUN5: it is the lane R2089.
- **Edition 4 is a re-issue, not a correction:** edition 3 (226 records) stays in the tree and in the published `hacs-data` 0.2.0 with its ids,
  valid under its own settings line.
- **Cost (rule 19, from measured runs of the same class; old search only — audit m3).** 85 `full` N > 1 ≈ 4.0 h (P4c 8 635 s, ≤ 8.0 GiB at
  (883, 0)); the 141 non-full records = **56 level-1 `full` + 85 `anemic`** ≈ 5.7 h (P4a 20 504 s, 612 MiB) — a phase predicted 9.5× too low in
  slot 26 (`HZEISUP_rerun.md:53–56`). Old-search sum ≈ 9.7 h wall. `RUN5_predictions.md` replaces this with **the new search's cost and RSS at
  (883, 0)** (parallel candidate batches hold several charpoly workspaces), EXW's per-record figure and the new grid cells' cost. Watchdog caps
  4.5 / 9.5 GiB as pass 4.
- **Tool item (audit M6): the overlay root with its own binary.** `mk_hecke_dataset.py` gains an overlay whose records were computed by a
  different binary than the build's base (`DS3_report.md:119–120`: not implemented), with that binary's sha256 recorded per overlay and
  `hz_dataset_verify.py --binary` run per overlay. Needed in both branches of Q1: for R2089, for the (1, 484) addendum, and under Q1 = no for
  accepting the finished `21a00a01` record. Owned by RUN5's agent; done before the run (wave 3).
- **Lever readings (LEV-K, audit M2).** RUN5 (and R2089) qualify `HECKE_MODULE_MT`, `_LEAN_PEAK`, `_TILE_WORK`, `ENGINE_VNNI2_FLOOR`,
  `ENGINE_HOST_ELIM_HOOK` only if (a) `s27-run5` contains `2cbed44c` (and `295c999b`), (b) the launch shell sources
  `docs/cluster/local/heckez/run5_levers.sh <RUN5 checkout>` (the four exports; it refuses a checkout without both commits), (c) `threads = 4`.
  First-cell check before the pass goes on: the three `EFFECTIVE HECKE_MODULE_*` lines with `source=env`, and where reached
  `ENGINE_VNNI2_FLOOR floor=1048576` / `ENGINE_HOST_ELIM_HOOK mode=on source=default`. A pass launched without it cannot be repeated for the levers.
- **Dataset.** `mk_hecke_dataset.py` build of `hecke_ed4/`; `hz_dataset_verify.py` with new pins (`PINS_ED4`), selftest regenerated;
  `HZDS_VERIFY … verdict=OK`; **a diff gate between editions 3 and 4 in the `HZEISUP_DIFF` style** (every record's word diff classed by TS-D's
  predicted rule; `moved_outside_rule=0`); Opus dataset audit; **[OWNER]** signs edition 4.
- **hacs-data.** Edition 4 joins the local `hacs-data` (R4 pattern); the push is the owner's.

#### R2089 — (2089, 0) anemic, its own lane (audit M6)

- **Why separate.** Under Q1 = yes nothing is re-accepted: the finished record (`0x413643d80b5153a8`) has the old fingerprint, so this is a **23.8 h
  recomputation** on 16 threads (`Z4_report.md:66`), with **no checkpoint inside a record** (`Z4_report.md:17`), on a host with three forced restarts
  since 2026-09-30. It would be ≈ 70 % of RUN5's wall and on the critical path to G27.
- **How.** Detached (`setsid`), **started first** from `s27-run5` (its own checkout `s27/run2089/src`), in parallel with RUN5; ≤ 2 GiB (fits the
  pass-5 sum, §4). It joins edition 4 through the overlay tool when it finishes; **edition 4's build does not wait for it**: if it fails or is still
  running, edition 4 carries it as `planned_not_finished` (as edition 2 did) and it joins as an addendum.
- **Under Q1 = no.** No recomputation: the `21a00a01` record is accepted through the overlay root with its own binary.

### 2.2 Core — the rest

#### L691 — the index-691 lattice, asserted (seed item 7)

- **Goal.** At (10, 691) over Z/691², assert in a validation what [EX] `ex:m0` (`hecke_examples.tex` l. 799–815) records: the three generators'
  determinant is 415291 = 601 · 691, i.e. the lattice has index exactly 691 in H¹. Prefer an arm of `HeckeLadicCellValidation` (the cell's existing
  owner) over a new name; the arm prints its line in the catalogue's form.
- **Acceptance.** The arm fails on a tampered generator (a tooth); catalogue entry updated; no golden or roster change.

#### LEV-K — make the lever runs qualify (new, wave 1; audit B1)

- **Why.** The rule (owner 2026-10-30; Q5 ruling 2026-11-12) retires a lever only on a default-route census or cluster run **whose `EFFECTIVE`
  lines were read**. As v0.1 planned them the runs cannot do that: the levers print an `EFFECTIVE` line **only when their variable is set**
  (`ENGINE_AVX2_PAIR` `src/ModArithmetic/Kernels.cpp:296–299`; `HECKE_SAT_PERF` `src/hacs/HeckeExt/HeckeSaturationDefect.cpp:615`;
  `HECKE_MODULE_MT` / `_LEAN_PEAK` / `_TILE_WORK` `src/ModArithmetic/DenseElim.cpp:146–153, 662`; `HECKE_FORMS_NTT_CACHE`
  `HeckeFormsHeckeAlgebra.cpp:43`; `ENGINE_VNNI2_FLOOR` `Kernels.cpp:208–223`), and the C1K runner's case env sets none of them
  (`slot24/C1K_b2_return_report.md:46`); `ENGINE_HOST_ELIM_HOOK` is **silent by policy** (`src/Engine/EngineRuntime.cpp:214–216`,
  `DenseElim.cpp:680`); the host-B kit is pinned to `70bcd5c9` (2026-10-28), before `295c999b`; host-B measured 2.6–4.6× the box's wall on the
  2026-11-03 anchor (not 1.2–1.5×) and is dedicated to SDEQ ("start no COHOMOLOGY jobs there without asking").
- **Work (S–M, Opus; Opus audit).**
  1. **One table, per lever**: its reader (file:line), the reach of the planned cell class on that route (the `LEVERS25_brief.md` §2 pattern),
     and the exact `EFFECTIVE` line the run will print.
  2. **Make the line exist.** Taken at the recommendation: **(a)** for every lever with a default-on value, the kit's case env sets the lever to
     that value (`HECKE_SAT_PERF=1`, `ENGINE_AVX2_PAIR=1`, …) — it prints the line and stays on the default route, no code change; LEV-K proves per
     lever (code reading + one anchor-cell run) that the set value **is** the default route; **(b)** for `ENGINE_HOST_ELIM_HOOK`, a small code change
     printing one `EFFECTIVE … source=default` line with the hook's bind count on stderr in campaign runs (cf. catalogue l. 3278) — the "every C++
     package" row applies, and the kit needs a new pin.
  3. **Re-pin the host-B kit** to a slot-27 commit (`b2_pins.py`, anchor, `EXPECT_NAMES` of that commit), dry-run the gate on the anchor cell
     (on the box, ≤ 3 GiB), and size the batch as **the smallest band that is a real census batch**, with the 4× host-B factor, in days.
     Same for the L23 run (ℓ = 2, 3, default settings): the smallest qualifying band, the machine named, in days.
  4. **`ENGINE_VNNI2_FLOOR` (audit m4).** Name a run on an AVX-512-VNNI host with a ≥ `295c999b` binary that reaches the two-limb GEMM above the
     floor with the variable set to `1048576` (RUN5 on the box qualifies only if a HeckeZ record reaches it — LEV-K checks reach), **or** state now
     that it defers to slot 28. What retires: **the `=0` rollback reading**; the knob itself is **reclassified as a selector** (the
     `HECKE_DESCENT_SMITH_PANEL` precedent), so "the knob stays" in the register remains true.
  5. **LEV-K owns the returns**: per run, the gate, the ingest into census 4.x, the `EFFECTIVE` lines quoted with counts (`LEVK_returns.md`). LEV27
     reads only that file.
- **Output.** `LEVK_report.md` with the table, the costs, and the plain-language text of the run questions (§6, "Asked later"). The owner is asked
  for no run before LEV-K's audit returns.

#### LEV27 — rollback levers at the close (Q5 ruling)

- **Levers.** Deferred to the slot-27 close (`LEVERS26_report.md` l. 23–26, 159): `ENGINE_AVX2_PAIR`; `HECKE_SAT_PERF`, `HECKE_FORMS_NTT_CACHE`,
  `HECKE_FORMS_NTT3`, `HECKE_MODULE_MT`, `HECKE_MODULE_LEAN_PEAK`, `HECKE_MODULE_TILE_WORK`; `L23_RING2K`, `L23_MOD3K`, `L23_F3L`;
  `ENGINE_HOST_ELIM_HOOK`; due by the register: `ENGINE_VNNI2_FLOOR` (its `=0` reading; the knob becomes a selector, LEV-K item 4).
  (`HECKEZ_LOCAL_PAR` is due at the slot-28 close.)
- **Qualifying runs.** Only the runs LEV-K made qualifying, with their `EFFECTIVE` lines read in `LEVK_returns.md`: (i) the host-B C1K-b2 batch
  (`ENGINE_AVX2_PAIR`, the `HECKE_SAT_*` / `FORMS_NTT*` / `MODULE_*` group, `ENGINE_HOST_ELIM_HOOK` where LEV-K shows reach); (ii) the L23
  default-route run (the `L23_*` group); (iii) the `ENGINE_VNNI2_FLOOR` run LEV-K names. A lever whose run did not happen, or whose line was not
  read, **defers to the slot-28 close with that reason**; it is never retired on a substitute reading.
- **Work.** Retire per the slot-25/26 pattern (OFF builds refuse the literal, ON builds keep it in `legacy/`), catalogue register rows, cross-config
  arms adjusted; Opus lever audit.

#### Z3b-F, TOOLS, XPL

- **Z3b-F.** F6: print, beside `nonzero_23`, the units at ℓ ∈ {2, 3} with M ≠ 0; F7: reset all globals at the top of `Run()` (and drop the dead
  `skipped=`); the τ follow-up (`Z3b_report.md` l. 38, design Q4): an arm checking π(R T^× g_i) ≡ τ π(R g_i) on the socle, the one link still without
  a T̃_Iso-independent oracle. Gate-line change → catalogue and [CLI] tables in the same commit. No value moves.
- **TOOLS.** `box_watch.sh` `foreign_heavy` from the per-sample delta of utime + stime (`/proc/<pid>/stat`), the 60 s age rule dropped
  (`slot25/CLOSE_audit.md` S2); `window_overlap.py` re-checked on a recorded window.
- **XPL.** The census explorer (`notebook/census-explorer/`) into the local `hacs-data` under the 2026-11-08 licence ruling (code LGPL-3.0-only WITH
  LicenseRef-CUDA-exception, data CC-BY-4.0, `.cxf` licence field at the next export, Cite-as kept); REUSE and `LEDGER_CMP` lines as R4; Q9
  (hosting) stays the owner's and is not needed for the local repository.

#### NB-B — NBMATH B1, B2

- **B1.** Hint rows for `integral_hecke_structure/v1` (`C_T` → `cyclic` / `abgroup`, BigInt-parsed, decimal shown, stored hex on hover; residue
  polys → `poly`; `local_type.hilbert`; a G6 verdict table; possibly `fibreproduct`); `render_coverage.tsv:66` `allow` → `hint+table`.
  **B2.** A `les` hint kind for `ConeCohomology.les` and `DicksonLES`. Touches `PrintJson.cpp` (`kHintRows`), `render_hints.tsv`,
  `render_coverage.tsv`, `render.js`, fixtures, `test_render.mjs`, [P] §18.5, `ConsoleReadOnlyTagValidation` arms (H)/(R), `ConsoleServeValidation`.
- **Acceptance.** The twin tables in lockstep; `GATEWAY_TEST` / `RENDER_TEST` `verdict=OK`; no transcript, golden or ConsoleDet move (re-verified);
  CLI tables regenerated if anything registered changes. After G27 the B1 fixtures re-capture with edition-4 ids.

### 2.3 Not in slot 27 (reasons)

- HZ-EISUP anemic records with e^an ≠ 1 stay `not_run` (final) (HZ-EISUP (b) Q5 ruling).
- F4 (GPU Dixon / CRT): F3 ranks it low; the GPU goes to BIGNTT's NTT instead.
- Golden `added=k` for newly final HZ records (audit M4): every added HZ point is recomputed in every golden pass (ConsoleDet threshold 70 s), and no
  selection rule or cost exists yet. G27 is `changed=15` only; an add-only HZ event with a fixed list, a predicted golden-pass wall and
  `--tier-a 12154 + k` is a slot-28 seed item.

### 2.4 Stretch (briefed only if a lane is free)

| pkg | goal | gate |
|---|---|---|
| (2089, 0) full | first a **measured intermediate prime level on the box** (one `full` record with N ≈ 1 300–1 500, predicted ≤ 24 GiB, announced; rule 19), giving wall, RSS and the partition limit; then a cluster-A / cluster-B kit from the flipped commit, `EXPECT_NAMES` of that commit; no checkpoint inside a record is stated in the kit note; agents write the kit, the owner alone submits | the measured record; **[OWNER]** launch (asked later, §6) |
| K1R | the (C3) K = 1 word route for `refused(k1_route)` (2 records) if EXW-D leaves it out | route bit-identity; C128 if new words |
| PG-C2 | gallery snippets `print` → `display`, [PG] transcripts re-baselined (`gen_phenomena_outputs.sh --check`) | separate card, not near the close |
| H4 | Hida rung k* = 55086 route (short-series truncation + dense Fitting mod 547³, GPU opt-in), ≈ 1 GPU-h on host-B | **[OWNER]** commission (slot-26 Q3 still open) |
| shadow | `legacy-shadow` under `--all` (≈ 9.5 h, nice 10) at the close | never in the gate hour |

## 3. Waves

| wave | packages (≤ 5 agents; ≤ 3 with a Fable agent) | audit after | gate to the next wave |
|---|---|---|---|
| 0 | lead (§1) | — | `s27/bin` ledger row 1; owner briefed on Q1 |
| 1 | **TS-D** ∥ **LEV-K** ∥ **EXW-D** ∥ **BIGNTT-D** ∥ **NB-A′**; **L691** takes the first free slot (six packages, ≤ 5 at once; TS-D, EXW-D, BIGNTT-D read-only) | **TS-D design audit (Fable-preferred: run it with ≤ 2 others)**; LEV-K, EXW-D, BIGNTT-D audits; NB-A′ stage audit; L691 code audit | **TS-D audited; LEV-K audited** (then the run questions go to the owner); EXW-D audited; L691 merged |
| 2 | **TS** ∥ **EXW** ∥ **BIGNTT** ∥ **NB-B** ∥ **Z3b-F** / **TOOLS**; C128 drafted by the lead (or a Sonnet editor) once TS-D and EXW-D are audited | TS, EXW, BIGNTT code audits; **C128 referee (Fable-preferred)** | merges TS (with its M3 gate) → EXW → (BIGNTT first half) under `merge.lock`; C128 referee ACCEPT |
| 3 | **EISUPb** (with its 85-record gate) ∥ **XPL** ∥ BIGNTT (second half) ∥ RUN5 tool item (overlay root) ∥ owner runs for LEV27 (as asked after LEV-K) | EISUPb code audit | EISUPb merged; `RUN5_predictions.md` filled; owner Q1 answered → `s27-run5` cut and pushed |
| 4 | **R2089** (first) ∥ **RUN5** (detached, `s27-run5`) ∥ (1, 484) when BIGNTT's first half is in ∥ stretch | dataset audit | **[OWNER]** edition 4 sign-off |
| close | **LEV27**, **G27** (K3), fold, W1-27, cross-config | lever audit; **G27 referee (Fable-preferred)**; close audit | §5 close conditions |

- **Wave-2 order (audit m1).** Five implementers start as wave 1's audits free their slots, in the priority order of §0 (TS first, then EXW, BIGNTT,
  then NB-B, Z3b-F / TOOLS). Each code audit takes the slot of the package it audits. The C128 Fable referee runs with **≤ 2 others** (BIGNTT may be
  one); the C128 editor is the lead or a Sonnet agent in a free slot.
- **Critical path:** TS-D → TS-D design audit → TS → TS merge gate (≈ 1.6 h + open(cap) records, old default) → C128 referee ACCEPT → EISUPb →
  EISUPb neutrality gate (≈ 4.0 h) → **owner Q1** → `s27-run5` (flip commit, pushed) → RUN5 (≈ 9.7 h old-search basis, new figure in
  `RUN5_predictions.md`) → edition 4 → G27. **Q1 gates only `s27-run5`, RUN5 and G27** (audit m2): TS and EISUPb merge with the old default in either
  branch. R2089 (≈ 24 h) runs beside RUN5 and is **not** on the path (it may join edition 4 as an addendum).
- **If owner Q1 is "no":** TS merges as a non-default setting only; EISUPb merges on the old order (it then moves at most the four certified kinds);
  RUN5 shrinks to the EXW records + any new grid cells under the old fingerprint; the `21a00a01` (2089, 0) anemic record is accepted through the
  overlay root; G27 does not happen (no golden event).
- The LEV27 runs are asked **after LEV-K** (end of wave 1) and wanted in waves 2–3 (owner launches); the close does not wait for them: a lever
  without its run defers to slot 28.
- BIGNTT is off the critical path: whatever has merged runs; (1, 484) is its own cell; the rest continues into slot 28.

## 4. Large runs on the shared box

Shared with SDEQ and TRACE FORMULA (`$HACS_RUN_LOG`, UTC): > 40 GB alone and announced; > ~24 GB announced to TRACE FORMULA; in a timing
window peers keep to no GPU, ≤ 4 niced cores, ≤ 10 GB, MemAvailable ≥ 16 GB.

| run | when | host RSS | wall / CPU-h | announcement |
|---|---|---|---|---|
| builds / `--all` (≤ 2 heavy jobs) | every wave | 3.8 / 6.3 GiB | 10–20 / 26 min | standing line |
| NB-A′ / NB-B `OC_BUILD_NOTEBOOK=ON` build + `notebook_close_check.sh` | waves 1, 2 | 3.8 GiB | ≈ 25 min | standing line |
| LEV-K anchor-cell dry run (re-pinned kit) | wave 1 | ≤ 3 GiB | ≤ 1 h | courtesy line |
| TS-D / EISUPb probes (scratch build, single cells) | waves 1–3 | ≤ 0.5 GiB | seconds each (`THETACAP_diag.md`: < 10 s at 4 threads) | courtesy line |
| **TS merge gate** (open(cap) level-N records + P4b class, old default) | wave 2 | ≤ 3.4 GiB | ≈ 1.6 h + the open(cap) records (figure in `TS_predictions.md`) | courtesy line |
| **EISUPb merge gate** (85 `full` N > 1, old default) | wave 3 | ≤ 8.0 GiB peak ((883, 0)) | ≈ 4.0 h | courtesy line; no `--all` in its (883, 0) window |
| BIGNTT measured law ((1, 174), (1, 268)) | waves 2–3 | ≤ 1.5 GiB | (1, 268) 5 228 s today | courtesy line |
| **R2089** (2089, 0) anemic | wave 4, first, `setsid`, own checkout | ≤ 2 GiB | ≈ 23.8 h on 16 threads, no checkpoint | courtesy line + ETA; owner told (> 24 h possible) |
| **RUN5** pass 5 | wave 4, `setsid`, own checkout | ≤ 8.0 GiB peak ((883, 0)) on the old search; new figure in `RUN5_predictions.md` | ≈ 9.7 h old-search basis (to be replaced) | courtesy line + ETA |
| (1, 484) under BIGNTT | when BIGNTT's first half merged | ≈ 1 GB (F3) | from BIGNTT's law | courtesy line + ETA; owner told if > 24 h |
| (2089, 0) full intermediate record (stretch) | if a lane is free | ≤ 24 GiB predicted | from the prediction | announced to TRACE FORMULA |
| **W1-27** value + timing | close | ≤ 6.5 GiB | 2.5–3 h | timing window |
| cross-config set + addendum arms, `*.out` kept | close | ≤ 32 GB summed | ≈ 2 days | to TRACE FORMULA (> 24 GB) |

**Pass-5 sum.** RUN5 ≤ 8.0 GiB + R2089 ≤ 2 GiB = 10.0 GiB: **in the (883, 0) window of RUN5 no heavy C++ job runs beside them**; outside it
(RUN5 ≤ 3.4 GiB) one heavy job runs at ≤ 3.8 GiB (a build, not an `--all`: 3.4 + 2 + 3.8 = 9.2 GiB). `RUN5_predictions.md` names the (883, 0)
window and replaces the 8.0 GiB with the new search's figure; if that exceeds 10 GiB, R2089 and RUN5's heavy lane are serialised. No GPU arm of
ours on the box; the BIGNTT CUDA route is validated in short runs only.

## 5. Close protocol (slot-26 `CLOSE_plan.md` pattern; `docs/agent-guides/slot-close.md`; all conditions must hold)

| # | step | gate |
|---|---|---|
| K0 | box + disk snapshot; announce | warn ≤ 20 GB, pause ≤ 10 GB |
| K1 | every core package merged or carried with a reason; LEV27 merged with each lever's qualifying run named (`EFFECTIVE` line quoted from `LEVK_returns.md`) or deferred to slot 28 with the reason | merge verified before any branch delete |
| K2 | fold `Registry/Slot27/*.cpp` → `Registry/Slot27.cpp`, `cmake/slot27/*.cmake` → `cmake/sources/*.cmake` | `--list` diff empty |
| K3 | **G27 golden event** (owner-gated; only under Q1 = yes). (1) The flip commit and its re-pins exist **only on the pushed branch `s27-run5`** (its touched-file list = TS-D's grep); (2) ledger `slot27/golden_ledger.md`; **scratch emission from `s27-run5`** (`GOLDEN_OUT`); `golden_ref_diff.py --expect` **`changed=15`** (the `HZ_N1_n<n>_full` set, nothing else) **`added=0` `removed=0`**; (3) **every changed line explained**: per line, the record JSON diff against the edition-3 member (the procedure of `GoldenHarness.cpp:2697–2701`), classed by TS-D's predicted rule, in the ledger; (4) ConsoleDet wall vs 70 s; (5) referee (**Fable-preferred**) → **[OWNER]** go; (6) **the landing commit** = merge of `s27-run5` into `hecke-extensions` + the in-tree `GOLDEN_EMIT`; nothing of `s27-run5` merged before it; the landed flip commit's `src/` diff is identical to the flip commit on `s27-run5` (`git diff <flip>^ <flip> -- src/` compared, empty difference), so the emitted reference belongs to the landed code; `golden_landing_check.sh 6ca88605` → CLAUDE.md golden defaults, `--tier-a 12154`, next R0 = the landing | strict A 12154 / 0, B 6231 / 0 at the new fingerprint |
| K4 | close tree `s27/close/src` at the folded, landed tip; `s27/close/build` (RelWithDebInfo, `-j8`) | sha256 recorded |
| K5 | W1-27 value pass (`slot27_close_window.sh`, copied from slot 26's with re-pins: REF = `s26/close/build/hacs` `0629ad13…6e8a`, REF_SRC `5bd70691`, R0 = G27's landing, roster, Lean decls, digests): golden strict, digests, `--all`, `--all-full`, `HECKE_NEBENTYPUS_NB3_FULL=1`, arms, licence guard; **`hz_dataset_verify.py hecke_ed4 --binary <close binary>` → `accepted=N/N`** (edition 4 re-accepted by the binary of record, audit M4) | every `MATCH` / `OK`, `EFFECTIVE` read, `refused=0`, `fallback:0` |
| K6 | W1-27 timing pass (quiet): hecke ≤ 0.470 s, decomp ≤ 0.109 s, `standing_gate_h2h.sh --gate` ≤ 1.04 vs REF (`pool_placement_check.sh` → `SAME` first), exponent ≤ 3.2, ext H2H default route ≤ 1.04 | MET, or INDICATIVE ≤ 1.04 |
| K7 | cross-config default set (minus the arms LEV27 retires) **with every arm's `*.out` copied to `s27/close/xcfg/out/<arm>/`** | golden clean in every arm |
| K8 | Lean: `LEAN_CENSUS … verdict=OK`, `LEAN_REPLAY … verdict=OK` (shared flock) | no `lake update`, no `native_decide` |
| K9 | guards: `LABEL_CENSUS … unresolved=0 stale=0`, `ADD_SPDX_CHECK … verdict=OK`, CLI tables, `wc -c CLAUDE.md` ≤ 30 000, `claude_md_moved_check.py … verdict=OK`; `pg_census_check.py` with `HACS_DATA` | read the text lines |
| K10 | `slot27/CLOSE_report.md`, `EXPECT_NAMES` = `--list`, slot-28 seed (incl. the add-only HZ golden item, §2.3), `docs/OWNER_TODO.md`; PDFs rebuilt and mirrored (md5) | — |
| K11 | close audit (Opus adversarial) → fix round → guards on the final commit → push | — |
| K12 | handover, memory update | — |

**Close conditions.** K5 all `MATCH`, golden as landed, suites passed, NB3_FULL `verdict=OK`, `accepted=N/N`; K6 MET / INDICATIVE ≤ 1.04,
exponent ≤ 3.2; K7 golden-clean with outputs kept; K8 / K9 `verdict=OK`; `golden_landing_check.sh <G27 landing or 6ca88605>` clean after K3.

## 6. Owner gates and questions

**[OWNER] gates.** Q1 below; the run questions after LEV-K (below); edition 4 sign-off; the G27 go; [C] 1.28.0 signature (at a later release);
pushes to `<user>/hacs` / `hacs-data`; explorer hosting (Q9); H4 commission.

### Question for the owner now

1. **May the new θ search become the default, with the integral data re-issued?**
   *What it is.* To describe the Hecke algebra over Z, the program looks for one Hecke operator that "generates" it. It tries candidates in a fixed
   order and gives up after 64 tries. On many level-N cells it gives up only because that order wastes its tries on unhelpful candidates (diagnosed
   in slot 26); a better order fixes this, and the new Eisenstein records (HZ-EISUP (b)) need it.
   *What changes if you say yes.* The search order is part of every integral record's settings line, so **every integral record gets a new id**.
   The integral data set is re-issued as **edition 4** (about 10 hours of computing on this box, plus, in parallel, a 24-hour **recomputation** of
   the largest record (2089, 0), which joins later if it is not done in time). In the same event, at the end of the slot, **the 15 integral entries
   of the regression reference change** (same mathematics, new hash), **the stored expected values of five checks change**, and **one sentence of
   the contract [C] changes** (the one that quotes the old settings fingerprint).
   *What does not change.* The published edition 3 (in `hacs-data` 0.2.0) keeps its ids and stays valid; edition 4 is a **re-issue under new
   settings, not a correction**. The old order stays available as a setting, so editions 1–3 remain reproducible. Records the old search already
   found keep their mathematical content.
   *If you say no.* The new order is added as an option only; nothing in the reference or the data moves; the cells that fail today stay open, and
   the new Eisenstein records exist only for the four kinds the old order already reaches.
   *Recommendation: yes — one event at the end of the slot, under the usual protocol (a dry run, an exact-difference check that exactly the 15
   entries change and each change is explained, a referee, your go at the landing), bundled with the new records so the data move only once.*

### Asked later (not in this round)

2. **Runs only you can launch** — asked **after LEV-K** returns and is audited (end of wave 1), because as planned in v0.1 these runs could not
   retire a single switch (the switches print their check line only when set; LEV-K makes the line appear first). LEV-K's report gives the costs;
   what is known now: (a) a **C1K-b2 batch on host-B**: host-B ran 2.6–4.6× slower than this box on its anchor cell and is reserved for SDEQ, so one
   6 000-cell batch is ≈ 10 days; LEV-K sizes the smallest real census band (C1K-b2 has 48 089 cells open, so it is also frontier work); (b) an
   **ℓ = 2, 3 census run** — this is the still-open slot-26 Q2 (4–10 days of a whole machine), asked with a named machine; (c) **(2089, 0) full**
   (≈ 50 GiB, an extrapolation from one point; the earlier anemic run took 23.8 h against a 0.5–1.2 h prediction, and a record cannot be resumed
   halfway): asked only after a measured intermediate record on this box (stretch, §2.4), as a cluster kit from the flipped commit.

### Decided at the recommendation (informational; overrule if you disagree)

- NBMATH questions 1–8 (`slot26/NBMATH_plan.md` §5) all as recommended (TeX in text cells, assert per fact, tours + showcases, the gallery left
  `print`-based until its own card, merge as the first slot-27 package — done, names folded in the right column, decimal `C_T` with the hex on hover).
- NB-A replaced by NB-A′ (C1 + stage audit + checks on the merged tip); not a wave gate.
- θ-SEARCH design: TS-D compares three orders (old-order-first with greedy continuation; greedy per-operator; ℓ¹); recommended the old-order-first
  candidate if it reaches the 19 + 2 cells at ≤ 2× cost, else the greedy search; ℓ¹ as fallback. Both implementation sites are covered.
- The order is selected by a `RationalSettings` field (not a console setting); the old-order value serialises to the edition-1–3 text byte for byte.
- TS merges with the old default and a byte-identity gate (open(cap) records + P4b class); EISUPb merges with the 85-record neutrality gate.
- The flip lives on the pushed branch `s27-run5` until the G27 landing; RUN5, R2089 and the G27 scratch emission are built from it.
- (2089, 0) anemic is its own lane (R2089), recomputed in parallel, not blocking edition 4; the overlay-root tool is built for it, for (1, 484) and
  for the Q1 = no branch.
- G27 is `changed=15` only (`added=0`); an add-only HZ golden event is a slot-28 seed item.
- Edition 4 is re-accepted by the close binary in K5; editions 3 and 4 get a diff gate (`moved_outside_rule=0`).
- LEV-K is a wave-1 package; the lever check lines are made by setting the default-on value in the kit's env (no code change), plus one small print
  for `ENGINE_HOST_ELIM_HOOK`; `ENGINE_VNNI2_FLOOR`'s `=0` reading retires and the knob becomes a selector (or it defers to slot 28 if LEV-K names
  no qualifying run).
- BIGNTT is core (standing goal "push the limits"; F3 ranks it first); it may run into slot 28; GPU opt-in in `EngineCuda` behind a hook, CPU golden,
  no external bignum; (1, 484) is decoupled from RUN5 and joins edition 4 as an addendum.
- Priority rule when short of agents or box: critical path and LEV-K, then BIGNTT and EXW, then the rest.
- The explorer licence (OWNER_TODO Q4) is already ruled (2026-11-08); OWNER_TODO is corrected in wave 0.
- [C] 1.28.0-pre.1 carries θ-SEARCH, HZ-EISUP (b), EXW (if any words) and the Q6 note in one pre-release line, drafted after TS-D and EXW-D are audited.
- A lever without its qualifying run defers to slot 28 (no substitute reading; Q5 ruling).

## 7. Seed v0.1 → plan v0.2

| seed # | item | here |
|---|---|---|
| 1 | NBMATH (A first; B1/B2) | A merged (`764205d7`); NB-A′ (wave 1), NB-B (wave 2) |
| 2 | θ-SEARCH card | TS-D, TS; owner Q1 |
| 3 | HZ-EISUP (b) code + [C] 1.28.0-pre.1 (+ Q6) | EISUPb, C128 |
| 4 | three `export_word` records | EXW-D, EXW (all 20), RUN5 writes them |
| 5 | lever retirement at the close | LEV-K (wave 1), LEV27; run questions after LEV-K |
| 6 | Z3b F6; τ follow-up | Z3b-F (+ F7) |
| 7 | index-691 lattice | L691 |
| 8 | `pg_census_check.py` data root | wave 0 item 4; K9 |
| 9 | shared research binary | wave 0 item 3 (P0) |
| 10 | explorer into hacs-data | XPL |
| 11 | quaternion stage | tracked, not carded (§2.0) |
| 12 | slot-25 S2; addendum arms; `legacy-shadow` | TOOLS; wave 0 item 2; stretch |
| — | standing goal (frontier) | BIGNTT (F3 rows 2–4) + (1, 484) cell; R2089; (2089, 0) full basis (stretch); the run questions (a), (b) as census frontier work |

## 8. Audit response (`00-slot27-plan_audit.md`, plan v0.1 at `007e8045`)

| finding | response in v0.2 | where |
|---|---|---|
| **B1** lever runs cannot retire a lever | new wave-1 package **LEV-K**: per-lever `EFFECTIVE` table; line made by (a) default-on value in the kit env, (b) a print for `ENGINE_HOST_ELIM_HOOK`; host-B kit re-pinned, dry-run, sized with the 4× factor; `ENGINE_VNNI2_FLOOR` run named or deferred; LEV-K owns the returns; no run asked before LEV-K's audit | §2.2 LEV-K, LEV27; §3 wave 1; §6 |
| **M1** NB-A stale | NB-A replaced by **NB-A′** = C1 + stage audit + `notebook_close_check.sh` on the merged tip + `--all` on the merged tree; dropped from the wave-1 gate | §2.0 #1, §2.1 NB-A′, §3 |
| **M2** θ-SEARCH scope | second site `HeckeZRecord.cpp:611–712` in scope; [C] sites incl. l. 16974; the five validation pins + `mk_heckez_run.py` + `mk_hecke_dataset.py` listed, flip list from a grep; mechanism (a) `RationalSettings` with byte-identical old-order serialisation; third candidate "old order first, greedy at the cap" | §2.1 TS-D → TS, C128; §6 |
| **M3** verification gaps | EISUPb merge gate = the 85-record neutrality re-run on the branch binary, old default; TS merge gate = all edition-3 level-N `open(cap)` records + the P4b class, byte-identical, old order | §2.1 TS, EISUPb; §3 critical path; §4 |
| **M4** RUN5 / G27 provenance and protocol | pushed branch `s27-run5` (TS + EXW + EISUPb + one flip commit) for RUN5, R2089 and the scratch emission; K5 `hz_dataset_verify.py hecke_ed4 --binary` → `accepted=N/N`; K3 the landed flip commit's `src/` diff identical to `s27-run5`'s; per-line JSON diff explanation; ed. 3 → 4 diff gate `moved_outside_rule=0`; **`added=0`** (add-only HZ event → slot 28); commit order stated once (flip on branch → scratch → referee → go → landing; nothing merged between) | §0, §2.1 RUN5, §2.3, §5 K3, K5 |
| **M5** Q2 not owner-scoped | Q2 removed from this round; asked after LEV-K with costs; known facts stated (host-B ≈ 4×, SDEQ, ≈ 10 days; (b) = slot-26 Q2, 4–10 days; (c) only after a measured intermediate record, no in-record checkpoint, kit from the flipped commit) | §1 item 6; §2.4; §6 "Asked later" |
| **M6** (2089, 0) anemic in RUN5 | own lane **R2089**, first, in parallel, ≤ 2 GiB, not blocking edition 4 (`planned_not_finished` if needed); "recomputed" in Q1; overlay-root tool built in both branches | §2.1 R2089, RUN5; §3; §4; §6 Q1 |
| m1 wave-2 order | audits take their package's slot; Fable referee with ≤ 2 others | §3 |
| m2 Q1 does not gate wave 2 | removed from the wave-1 gate; Q1 gates only `s27-run5`, RUN5, G27; TS-D audit and M3 gates on the critical path | §3 |
| m3 cost of the non-full phase | "141 non-full" = 56 level-1 `full` + 85 `anemic`; 9.5× under-prediction noted; `RUN5_predictions.md` adds the new search's cost and RSS at (883, 0) | §2.1 RUN5, TS |
| m4 `ENGINE_VNNI2_FLOOR` | the `=0` reading retires; the knob is reclassified as a selector | §2.2 LEV-K item 4, LEV27 |
| m5 CUDA NTT home | BIGNTT-D names it (recommended `EngineCuda` behind a hook) and the include-guard consequence | §2.1 BIGNTT |
| m6 (1, 484) tied to RUN5 | decoupled: own detached cell when BIGNTT's first half merges, joins edition 4 as an addendum via the overlay tool | §2.1 BIGNTT, RUN5; §3 |
| m7 priority rule | stated in §0 | §0 |
| m8 C128 order | drafted once TS-D **and EXW-D** are audited | §2.1 C128; §3 |
| m9 roster | LEV-K 0–1 added (293–295); TS's order key registers no console setting under (a) | §2.0 |
| m10 Q1 text | edition 3 keeps its ids and stays valid, edition 4 is a re-issue; the five validations' pins and the [C] sentence change in the same event; "(2089, 0) is recomputed" | §6 Q1 |
