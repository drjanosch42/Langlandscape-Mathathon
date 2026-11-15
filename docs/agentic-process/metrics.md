<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

All times PST (UTC−8). Source logs: all machines on Berlin time (CET, UTC+1), report sources in UTC; converted.

# Metrics (state 2026-11-14 ~18:10 PST, after stage 6 and HACS Lanes A/B)

"(not recorded)" = no source records it. Counts marked *recounted* were taken on branch `final/agentic` (= `main` ffb527c plus this
folder) with the same commands as the 2026-11-14 version of this file.

## 1. Repository
| Quantity | Value | Source |
|---|---|---|
| commits on `main` | 2058 (471 first-parent), of which 405 merge commits (state 2026-11-14 13:00 PST: 590 / 136 / 123) | `git rev-list --count [--first-parent \| --merges] main`, recounted |
| phase/stage merges into `main` (first-parent) | P1 2277355, P3/P4 a4efa59, S1 9aba3c7, re-plan 0c31df4, S2 13ae47c, S3 2e54ed8, HACS plan 08200a4, S4 fafd783, S5 1ce44eab, HACS Lane A 0024903a, S6 aed93c37 | `git log --first-parent --merges main` |
| commits added per stage (`git rev-list A..B`, includes side-branch commits) / merges among them | S1 244 / 80; S2 215 / 28; S3 327 / 59; S4 502 / 82; S5 284 / 48; S6 376 / 99 | recounted between the stage-merge commits |
| remote branches (2026-11-14 ~18:10 PST) | 107 `titan/*`, 68 `conceptd/*`, 129 `impl/*`, 37 `abhijit/*`, 3 `doc/*`, `wip-*` ×6, `main`, `HEAD` | `git ls-remote origin` |
| cross-node messages | 134 files: 83 in `agents/messages/fabian/archive/` (from Abhijit's node), 50 archived + 1 unprocessed in `agents/messages/abhijit/` (from Fabian's node); 7 work batches sent (batch 8 announced in `…fabian_s06-closed`, not yet sent) | `ls agents/messages/*/archive` (recounted; 2026-11-14 13:00 PST: 39) |
| `experiments/LOG.md` table rows | 35 (incl. headers) | `grep -c '^|'` |
| agent session transcripts (`supplementary/agent-logs/`, redacted) | 726: localhost 565 (frozen 2026-11-15 08:38 PST), TITAN 1 (08:38 PST), CONCEPTD 88 (2026-11-14 22:36 PST), Abhijit's node 72 (2026-11-15 08:56 PST) | `supplementary/agent-logs/README.md` (manifest rows per node) |
| local `exp/*` strand branches | 25 (S01 15, S02 4, S03 2, S04 2, S05 2) | `git branch --list 'exp/*'` |

## 2. Work packages
| Stage | WPs planned | Notes (source) |
|---|---|---|
| 1 | 51 (P3 plan), ≈ 56 executed | closure s01 |
| 2 | 36 | `REPLAN-S02-06.md`; `runs/s02.md` |
| 3 | 34 (X 2, M 9, L 14, C 5, H 1, T 3); executed adds L10b, L13 (audit fixes), M9 | `REPLAN-S02-06.md`; `runs/s03.md` rows |
| 4 | 43 planned; added at execution: E1M/E1L, L10b, MOD, IMP, L17a/b/c | `runs/s04-deviations.md`, `runs/s04.md` |
| 5 | 31 rows (27 scheduled); added: E1, M10, LT, L4g, L11a/b/c, M9a/b/c, M8b | `runs/s05.md` |
| 6 | 53 rows (48 planned); added: MODH, FD, HS, S05FIX, M5d, THACS, L15a/b | `runs/s06.md` |

## 3. Lean at each final gate (all `#print axioms` lines standard: propext / Classical.choice / Quot.sound subsets)
| Quantity | S1 0492baa | S2 c45f2e8 | S3 5aa765a | S4 71576d1c | S5 9ddd83e | S6 4405815 | 2323a252 (RamNrdSurj) | 28d2b091 (submission bundle) | final c70ef3a9 (BrandtStabFree discharge) |
|---|---|---|---|---|---|---|---|---| --- |
| `PrintAxioms` lines | 161 | 195 | **519** | **592** | **747** | **836** | 840 | **950** | **955** |
| gate-1 / pregate lines | 151 | 191 | 516 | 558 | pregate 709 | pregate 786, gate-1 833 | — | — | — |
| `sorry` in our code | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| only `sorry` anywhere | | the import's `Instances.lean:1815` | same | same | same | "the import's 1" | the import's 1 | the import's 1 | the import's 1 |
| from-scratch build wall | 3842 jobs | (not recorded for final) | 180 s | 251 s | 273 s | TITAN 319 s / CONCEPTD 5:21, 4194 jobs | TITAN 321 s, 4198 jobs | TITAN 323 s, 4199 jobs | TITAN 346 s, 4205 jobs (VendorStacks 1955 jobs), unseeded worktree |
| CONCEPTD cross-check | — | PASS | 519, 3:16 | 592, 3:50 | PASS (closure addendum) | 836, 5:21 | quick check ramnrd-3: 840, PASS | subl-gate-1x fresh checkout: 950, 341 s, PASS | — (none) |
| linter warnings (`Langlandscape/` / tests) | 80 | 84 | 171 / 42 | 169 / 47 | 183 (closure: carried lint debt) | 181 / 71 overall, 0 in S06 files | 187 / 71 (6 module-system import notices in the 2 new files) | 187 / 71, 0 in `Uncond.lean` | 204 / 71 |
| library / Hyp / test modules (stage) | | | 13 / 3 / 8 | 20 / 5 / 20 | 9 lib + 6 test | 32 files via `check_wp` (S06) | 5 files via `check_wp` | `Uncond.lean` via `check_wp` | 6 new files (`Quat/StabFree/*`, `Hyp/BrandtStabFreeDischarge.lean`) and the test file |

Sources: `runs/s0N.md`, `*_milestone-closure-s0N.md`. The S03, S04, S05, S06 counts were verified in the closure files and `runs/`
(S03: closure line "519/519 axiom lines standard"; S04 "PrintAxioms 592/592 standard"; S05 "598 -> 747 rows"; S06 "836/836,
nonstandard 0"; `2323a252`: TITAN `titan/ramnrd-final-2` `c-axcount.log` "printed=840 expected=840 nonstandard=0"; final: TITAN `titan/subl-gate-1` `c-axcount.log` "printed=950 expected=950 nonstandard=0"; final: TITAN `titan/bsf-gate-1` (logs fa755069) `c-axcount.log` "printed=955 expected=955 nonstandard=0", CONCEPTD `conceptd/subl-gate-1x` `c-axcount.txt` the same). Registered hypotheses: 29 registered / 26 in the table,
12 instances (commit 63328fbb; `mathematics/` hyp table); after the `RamNrdSurj` discharge (2323a252): 2 discharged (`PadicOrdDecomp`,
`RamNrdSurj`), 1 conditionally discharged (`ResidualBurnside`), 13 table rows with an instance or proof. After the `BrandtStabFree` discharge (c70ef3a9): 3 discharged (`PadicOrdDecomp`, `RamNrdSurj`, `BrandtStabFree`), 1 conditionally discharged.

Whole-library size at `main` (recounted): 195 non-vendored `.lean` files under `lean/Langlandscape/` (library + tests), ≈ 37 980 lines,
≈ 1975 `theorem`/`lemma` and ≈ 610 `def`/`structure`/`instance`/`abbrev`/`class`/`inductive` declarations
(`git grep`; approximate, counts declaration keywords at line start). Per-stage numbers for stages 3–5 were not recomputed.

## 4. Maths, code, talk
| Quantity | S1 | S2 | S3 | S4 | S5 | S6 |
|---|---|---|---|---|---|---|
| `mathematics/main.pdf` pages | 29 | 55 | 74–87 (87 at M9, log) | 106 | 140 | **170** |
| talk PDF pages | | | 9 | 11 | 13 | **17** |
| pytest | 231 passed, 3 skipped | 313 → 330 | 341 → 354 → 371 | (not recorded here) | (not recorded here) | HACS Lane A closure: 483 passed, 3 skipped (full Python suite) |

Sources: STATE.md ("PDFs mirrored (106 pp, 11 pp)", "(140 pp, 13 pp)", "(170 pp, 17 pp, Hsieh note 4 pp, hypotheses report)"),
`runs/s03.md` (87 pp at M9), earlier log lines. Code results: `code/results/` has 120 tracked files (recounted).

## 5. Remote packages (Abhijit's node), batches 1–9
| Batch | Sent (PST; file name in UTC) | Content (from the batch files and STATE.md) |
|---|---|---|
| 1 | 11:40 PST (`20261114-194045Z`) | S06-L1–L3 (Lean), S06 chapter, S03 chapter, q ≡ −1 second reader |
| 2 | 12:16 PST | S04 chapter, S06-L13/L17/L4, literature (S06-M11, S04-M5) |
| 3 | 12:51 PST | S05 chapter, S05 literature + R1, S06-L5a/L10a, S06-L7/L6/L14/L6b |
| 4 | 13:02 PST | C1 S04-L7 / L13a (Mathlib-only Lean), C2–C4 blind cross-account reviews of s03, s01, s02, C5 literature |
| 5 | 13:39 PST | D1 S05-L6, D2 S05-L8 algebraic half, D3 S05 chapter open items, D4 literature |
| 6 | 14:47 PST | (content not summarised in this file; see `agents/messages/abhijit/archive/20261114-224725Z_fabian_batch6.md`) |
| 7 | 16:47 PST | F1 blind cross-account review of the S05 chapter, F2 S06-M5 second reader (parts A and B), F4 PARI check of T4/H3 |
| 8 | 18:15 PST (`20261115-021557Z`) | cross-account review of the final report and talk; answered 18:29 PST (`20261115-022937Z_abhijit_xr-final-report.md`; W = 32, 0 crit, 7 maj) |
| 9 | 2026-11-14 22:57 / 22:58 PST (`20261115-065740Z`, `…065825Z`) | H1 cross-account review of the submission report, H2 of the talk; reminder 2026-11-15 02:46 PST; **never answered** ("not done on this node", 08:57 PST); replaced by the fallback Fable audits ([lessons.md](lessons.md) 46) |
Accepted Lean from Abhijit's node entered `main` only after a CONCEPTD or TITAN acceptance build (`acc-b34-1`, `acc-b5-1`; `conceptd-acc-*` outbox files).

## 6. Audits (added since the 2026-11-14 version)
| Audit | Auditor | Verdict / findings | Source |
|---|---|---|---|
| S03 Lean L12, chapter M8 | Fable | PASS WITH REMARKS; M8: 0 crit / 8 required / 6 minor | `runs/s03.md` |
| S04 Lean (3 parts), chapter, cross-account review | Fable, Abhijit's node | PASS WITH REMARKS; fixes L17a/b/c | `runs/s04.md` |
| S05 Lean L10 (3 parts), chapter M8 | Fable | parts: 2 / 6 / 3 required; chapter 0/3/11, follow-up 0/0/8 | closure s05 |
| S06 Lean part 1, part 2 | Fable | 0/0/9; 0/2/11 (+7 optional); part 2 found `Hyp.FreeRankTwo` ≡ conclusion of its use | closure s06 |
| S06 chapter parts 1–3 | Fable | 0/2/12; FAIL for M > 1 then PASS WITH REMARKS 0/2/4; 0/0/7 | closure s06 |
| cross-account | Abhijit's node ↔ ours | s03, s01, s02, s05 (W = 14) blind reviews; S06-M5 second reader (counterexample B2) | closure s06; batches 4, 7 |
| HACS Lane A WP audits | Opus ×3, Fable ×1 | FAIL r0 → fixed (HJ-0, A1, A3, B0), PASS (A2) | Lane A closure |
| HACS Lane B reviews | fresh Opus ×2 | HJ-6-min PASS (1 major wording, 8 minor), HJ-6b ACCEPT (0 crit/maj, 6 minor) | Lane B closure |

## 7. Build nodes and models
| Node | Result branches s01…s06 | Notes |
|---|---|---|
| TITAN (3 slots) | 16, 19, 20, 30, 11, 10 = 106 (+1 other) | outbox file names `*_titan-s0N-*`: 18, 19, 30, 51, 24, 17 |
| CONCEPTD (2 slots) | 0, 1, 11, 25, 13, 13 = 63 (+5 acceptance/other) | most CONCEPTD specs are filed under `titan-…` names; 3 `conceptd-s06-*` |
Counts: `git ls-remote origin 'refs/heads/titan/s0N*'` / `conceptd/s0N*`, 2026-11-15; branch total 107 / 68.
Models used (sources: `runs/`, closures, `model-selection.md`): Opus (global master, all stage/planning masters, hard Lean and hard
LaTeX writers, rescue writers, WP auditors, HACS lane masters and reviewers), Sonnet (routine Lean/LaTeX/code writers, HACS PC2 prep
and one Lane B implementer), Haiku (logging, polling, vendoring, axiom lists), Fable (Lean and chapter audits, adversarial audits),
Muse Spark Open and Mistral Large 4 (stage 1–P3 audits and strands only). Token counts and costs: not recorded in the repo (apart from the
`cost_idx` of the experiment strands in `LOG.md`).

## 8. HACS lanes
| Item | Value | Source |
|---|---|---|
| Lane A | 22 commits on `impl/hacs-laneA`; 5 WPs (HJ-0, A1, A2, A3, B0); 86 Lane A tests; full Python suite 483 passed / 3 skipped (178 s); strict golden tier A 12154/0, tier B 6231/0 (at build) | Lane A closure |
| Lane B | 8 subagents (≤ 4 at once: Opus ×3 + Sonnet ×1 implementers, 2 Opus reviewers, 1 Sonnet PC2 prep); 5 deliverables; HJ-1/2 self-test 8084/0 | Lane B closure |
| HACS release | v0.2.1 (DOI 10.5281/zenodo.24231446); data v0.2.0 (DOI 10.5281/zenodo.24147012) | STATE.md |
| Python bridge results | `code/results/s05/gl2_dnew.json`, `s06/definite_local.json`, `s06/T4_betti.json`, `laneB/congruence_k.json`, `laneB/py_reference.json` | closures |
