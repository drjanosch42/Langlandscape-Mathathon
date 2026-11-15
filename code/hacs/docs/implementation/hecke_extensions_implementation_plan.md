# Hecke Extension Engine — Implementation Plan (September 2026)

**Version 1.28 — 2026-10-26** (documents-only: the `coefficient_ring` row of §5 follows [C] v1.23.0-pre.37 — `Z` un-reserved for the integral descent only, D6 audit M2; no plan statement otherwise moves). Previous: **Version 1.27 — 2026-10-12. Slot 22, CLOSE-T (the theory / documents half of the split close); non-normative.**
**Status: RELEASE CANDIDATES prepared; NOT owner-signed (owner sign-off is step T8 of `slot22/slot22_split_close_plan.md`). CLOSE-R (the W1-22 figures, the odd-pass and ingests) is carried into slot 23 as a run lane; the slot-22 suite-status figures are PENDING W1-22.**
(1) **Outcome at HEAD.** Roster **217 = 70 fast / 128 standard / 19 slow** (`--all` 198; `docs/cluster/noctua2/EXPECT_NAMES` = 217). **One golden event (G-EVT)**: `1569cd12`, Fable referee F2g `cea5a60e`, add-only, 59 tier-A lines
(G1 8, G2 16, G7 8, G4 27; 0 changed, 0 removed): **18 117 entries, tier A 11 886, tier B 6231** (`slot22/golden_ledger.md`, `G-EVT_report.md`); R0 of slot 22 = the slot-21 close commit `15b0d596`; **R0 of slot 23 = the CLOSE-T commit**
(split plan §1.5). Lean: `LEAN_CENSUS decls=2776 proved=2711 … verdict=OK` (LR-Y phase 5); **M5 met in the cut form** (`M5_cut.md`, `M5_report.md`: M5-E and M5-T met, M5-C = [C] `thm:classical` in [C]'s sense cut to M6, branch P; F5 done),
**M6 orbifold item MET** (F-MP3, conditions C1-C3 discharged at [LP] v1.6). (2) **Packages:** §8 "Slot 22, the outcome (v1.27)". (3) **Documents at CLOSE-T** (header / `\date` / changelog only; no statement, label, tag or marker moves; referee records:
`slot22/release_referee_coverage.md`, `slot22/F-T1_release_referee.md` — Fable, ACCEPT on every gap, BLOCKER 0 / MAJOR 0 / MINOR 2 / NIT 15, the MINORs and the wording NITs applied at b2edd3c2): [C] **v1.22.0** (from 1.22.0-pre.17; 222 markers on 86 labels: 208 `\LEAN`, 14 `\LEANlit`; none on `thm:classical`, `eq:corconjres`, `eq:fullop`),
[E] **1.22.0** (from pre.3), [U] **0.6.0** (from pre.3), [X] **v1.27**, [LP] **v1.7**; non-binding: [P] 3.12.0, [CLI] 1.4.0, [L37] 0.5.2, [RC] 0.2.0, [MPT] 0.3.1 (already a version), [PG] 1.1.0 (unchanged), [LG] 0.1.5, [EX] 1.4.1 (unchanged). Gates at the commit:
`LABEL_CENSUS labels_defined=743 … unresolved=0 stale=0`; `ADD_SPDX_CHECK … verdict=OK`; PDFs out of tree (`$HACS_DATA/s22/closet/pdf/`), 0 undefined references / citations. The text of NIT-5, -6, -7, -13 of the T1 referee is deliberately not applied (they change the scope of a statement or need a `.bib` entry; slot 23).
(4) **Runs still open (CLOSE-R, split plan §2):** ℓ = 2, 3 even pass `l23even4-1..4` (ETA ≈ 2026-10-13 08:30), then the odd pass (350 cells), the ℓ = 2, 3 ingest with `lean_dims`, host-B `sat_run2` ingest, [PG] examples, the cluster runs (owner), then **W1-22**
(`slot22_close_window.sh`, from a detached checkout of the CLOSE-T commit; expected figures: `--all` 198/198, `--all-full` 217/217, golden A 11886 / B 6231, digests unchanged). (5) **Slot-23 cut:** `docs/implementation/slot23/00-slot23-plan.md`.
(Numbering: v1.27.1 will be slot 23's day zero.)

**Version 1.26 — 2026-10-06. Slot 21, close (C-6 release commit; W1 done); non-normative.**
**Status: slot-21 release released and signed off by the owner 2026-10-07. W1 correctness MET and timing MET** (`slot21_close_window.sh --run`, 2026-10-06 13:59:14 → 15:26:57 UTC, 5264.7 s (no Lean replay inside the window), on the
release commit `15b0d596`, NEW sha256 `a07b9d2a…`, REF = the slot-20 close binary (code of `df24fd35`, sha256 `46cf855a…`), R0 `931ff32f`, placement SAME,
`QUIET foreign_heavy=0`, `PREWINDOW foreign_count=0`, `OVERLAP watch_rows=2620 lean_gt5pct_rows=0 foreign_heavy_rows=0`, every round `state=clean`, exit 0;
`docs/implementation/slot21/W1_report.md`): hecke 256 new_min **0.4636 s** (REF 0.4669), paired ratio **0.995**, absolute gate 0.470 s met with **1.4 %** headroom
(flag `WITHIN_3PCT_OF_GATE`) — **the whole box ran ≈ 15 % slower than at the slot-20 W1** (the same REF binary: 0.4669 s now vs 0.4025 s then), so the narrow absolute
margin is the machine's, and the paired ratio is the regression guard; decomp 128 new_min 0.0952 s (REF 0.0963), ratio 0.990, headroom 12.7 %; `verdict_changes=0`;
T2 `(10, 691)` 0.9967, `(160, 691)` 1.0103 MET; T-C4 3.067 s ≤ 5 s MET; ConsoleDet 40.8 s (T_C4_INFO, not gated); `--all` **176/176** 1112.4 s, `--all-full`
**193/193** 1747.8 s; `DIGESTS compared=33 differ=0 verdict=MATCH` (EngineDet `0x3dddd2ef9a8efd`, ExtDet `0xaef77d786b4f29b4`, ConsoleDet C4 (a) `0xf6ed04bbe8e6b60a`,
smoke CERTIFIED); golden 18 058, A 11 827 / 0, B 6231 / 0; `NB3FULL verdict=OK` (132 cells, 4231 checks, 891.2 s, 2.32 GB peak; slot 20: 836.6 s, 1.07 GB); nine
env arms rc 0 with their `EFFECTIVE` lines read (`ARMS verdict=OK`); `LICENCE_GUARD … pending=0 … known_third_party_pdfs=0 … verdict=OK`; `LEAN_CENSUS_COMMITTED
decls=1303 proved=1238 proved_mod_lit=37 stated=0 … planned=0 sorries=0 … verdict=OK`; `LABEL_CENSUS labels_defined=635 files_scanned=1596 … sites=3058 … unresolved=0
stale=0`. `LEAN_REPLAY modules=150 ok=150 failed=0 peak_rss_gib=13.76 … verdict=OK` from C-4 (2026-10-06, outside the window). Close checks (`cross_config.sh`,
`CheckThread`, the gateway self-test, the `Check` re-verification of the `rss()` fix): **DONE** — seven arms golden-clean, `CheckThread` 0 warnings + GPU-visible `ours=0`, gateway `ran=22 failures=0`, `rss()` fix verified under `Check` (`docs/implementation/slot21/WP-18_close_report.md` §4).
(1) **Outcome.** Roster at the close **193 = 68 / 108 / 17** (`--all` 176; 192 slot-21 names + `HeckeLevelNCurveValidation` of early slot 22, LN23): slot 21 added
`NumberFieldLllValidation` (T1), `LicenceGuardValidation` (WP-LIC) (fast); `HeckeLambdaQExpValidation` (P7), `NumberFieldRibetFieldValidation` (T2),
`HeckeLambdaModSymValidation` (P8), `HeckeLambdaTwoVarValidation` (P9), `HeckeLValueCoefficientRingValidation` (P3), `HeckeLValueEisensteinMeasureValidation` (P2),
`HeckeLValueWildCharacterValidation` (P4), `HeckeLValueIwasawaInvariantsValidation` (P5) (standard). **No golden event** (no `*GoldenReference.inc` change since R0
`931ff32f`). Lean: FLT vendoring L21-V done (25 modules, 2958 lines, byte-identical; replay 150 / 150); C-4 full re-emit `LEAN_CENSUS … verdict=OK` (the emitted
`census.tsv` byte-identical to the committed one), `LEAN_REPLAY modules=150 ok=150 … verdict=OK` (2026-10-06); Q5 decided (all four as recommended); R20-L done;
the M5 cut text not written (carried). (2) **Packages:** §8 "Slot 21, the outcome (v1.26)". (3) **Documents at the close** (the release commits of C-6, 2026-10-06,
owner decision D16 accepted as recommended; header / `\date` / changelog only, no tag upgraded): [C] **v1.21.0** (140 markers on 65 labels unchanged), [E] **1.21.0**,
[U] **0.5.0**, [L37] **0.5.1**, [RC] **0.1.0** (new, not binding), [LG] **0.1.5**, [EX] **1.4.1**, [CLI] **1.3.0**, [PG] 1.0.0 (unchanged), [P] v3.11.1, [LP] v1.4;
SPDX CC-BY-4.0 headers on the last 9 `docs/latex` files (`pending_tex_headers.txt` empty; `LICENCE_GUARD … verdict=OK`). PDFs of the released versions: committed by
the packaging pass after W1 (PENDING; the last PDF commit is `d4875f55`, pre-release versions of 2026-10-06 06:23). (4) **Runs at the close:** LAT37A 10 / 10 (`slot21/LAT37A_report.md`); census 3.2 kit ready, not submitted (cluster down); A-cl withdrawn (`acl_audit.md`).
(5) **Slot-22 cut:** `docs/implementation/slot22/` plan v0.2 (early slot-22 packages LN23, WP-VERB-2, FR-1, WP-LIC2, S044 already on the branch).
(Numbering: v1.26.1 will be slot 22's day zero.)

**Version 1.25 — 2026-10-05. Slot 20, close (WP-18); non-normative.**
**Status: W1 correctness MET and timing MET on a quiet box** (`slot20_close_window.sh`, 2026-10-05 01:33:03 → 02:53:24 UTC, 4823.0 s incl. the Lean replay, on the
release commit `568cc357` (code of `df24fd35`), REF = the kept slot-19 close binary (code of `2e4c26b7`), R0 `2e4c26b7`, placement SAME, `foreign_count=0`,
`foreign_heavy_rows=0`, exit 0): hecke 256 new_min 0.3948 s, ratio 0.988; decomp 128 0.0909 s, ratio 1.004; `verdict_changes=0`; T2 1.0308 / 1.0079; T-C4 3.044 s;
ConsoleDet 41.1 s; `HeckeRingLoewyValidation` 63.0 s (owner target 64 s, met); `--all` 165/165 946.6 s, `--all-full` 182/182 1563.8 s; `DIGESTS compared=33 differ=0
verdict=MATCH`; golden 18 058, A 11 827 / 0, B 6231 / 0; `NB3FULL verdict=OK` (132 cells, 4231 checks, 836.6 s); `LEAN_CENSUS_COMMITTED decls=1303 proved=1238
proved_mod_lit=37 stated=0 … planned=0 sorries=0 … verdict=OK`; `LEAN_REPLAY modules=125 ok=125 failed=0 peak_rss_gib=13.76 … verdict=OK`; `LABEL_CENSUS … unresolved=0
stale=0`; close checks: `cross_config.sh` seven arms golden-clean (one flaky ASan check in `022_harness.oc`'s `rss()` assertion, a read-order race, carried), the notebook
arm's gateway self-test `verdict=OK`, `CheckThread` 3 / 3 clean and the first GPU-visible TSan run (`ours=0`, C12 closed); `docs/implementation/slot20/WP-18_close_report.md`.
(1) **Outcome.** Roster **182 = 66 / 99 / 17** (`--all` 165): `HeckeLValueMeasureValidation` (WP-MEAS + S1 / S2, standard), `ConsoleServeAtlasValidation` (NB-4,
standard). **No golden event** (O4; `slot20/golden_ledger.md`, which also carries the add-only candidate list G1–G7 for slot 21); digests unchanged. **Lean milestone M4
met** (F3 ACCEPT WITH REPAIRS, 0 B / 1 M / 9 m, repaired; M4-f in the weak form; `planned = 0`); the Q5 brief delivered; L20-H: 107/107 FLT modules build on v4.33.0, the
vendoring set 25 modules / 2958 lines (approved for slot 21). (2) **Packages:** §8 "Slot 20, the outcome (v1.25)". (3) **Documents at the close** (`568cc357` + the close
commit): [C] **v1.20.0** (the milestone-M4 markers: 42 new, 140 on 65 labels; no marker on `thm:classical`, `eq:corconjres`, `eq:fullop`; every `\LEANlit` "locator
unverified (R20-L)"), [E] **1.20.0**, [U] **0.4.0**, [L37] **0.5.0** (not binding; PDF committed), [CLI] **1.2.0**, [P] v3.11.1, [LP] v1.3, [EX] 1.4.0, [LG] 0.1.4,
[PG] 1.0.0. (4) **Runs at the close:** none running; `(1372, 37)` confirmed `conj:swappedsat` at b = 5 (all five cells at 37); LAT37A 3 of 10 (7 carried, PAUSE).
(5) **Slot-21 cut**: §8 "Slot 21, re-cut from the slot-20 outcome" (`docs/implementation/slot21/00-slot21-plan.md` v0.1, a draft; owner questions open).
(Numbering: v1.25.1 will be slot 21's day zero.)

**Version 1.24.1 — 2026-10-04. Slot 20, day zero (WP-1); non-normative.** §8 "Slot 20" now mirrors `docs/implementation/slot20/00-slot20-plan.md` **v1.0**
(`deafab02`): the owner's rulings O1–O13 (all at the recommendation, O7 yes capped, O8 Shimura scans; new WP-JET: Jetson build + notebook server, agents may connect to
`arm-board`), the stale items of v0.1 corrected, the disk rule of 2026-10-04 (warn ≤ 20 GB free on `C:`, pause ≤ 10 GB). **Q** (the quiet re-measure owed since slot 17) is
done (`bff70807`, all gates MET); L20-0 done (`8b81c901`, [LP] v1.3). WP-1: `Registry/Slot20/` + `cmake/slot20/` stubs (WPLV3, WPMEAS, NB4; all empty, `fa224b3e`),
both include-guard allow-lists, `slot20_close_window.sh` (REF / R0 = the slot-19 close `2e4c26b7`; golden 18 058 / 11 827 / 6231; roster 180 / 163, forecast 181 with WP-MEAS and
182 with NB-4), the shared binary `s20/bin/` from the persistent detached checkout `s20/src`, `s20/windows.txt` + `windows.lock` (the one launcher state, §0.3), the O11 clean-up of
the kept `s18/wp18` binaries. No normative rule changes; roster unchanged at 180 = 66 / 97 / 17. (The slot-20 close is **v1.25**.)

**Version 1.24 — 2026-10-04. Slot 19, close (WP-18); non-normative.**
**Status: W1 correctness MET; timing not a verdict (the box carried our own runs in flight — `(1184, 37)` and the WP-RC chain — declared;
correctness is the verdict, the quiet re-measure Q is carried to slot 20 after the owner's restart onto `memory=80GB swap=8GB`)** (`slot19_close_window.sh`, 2026-10-04 02:27:52 → 03:57:38 UTC, 5387.6 s incl. the Lean replay, head `e296a84b` (the release
commit `02f417fd` changes only documents; its document-reading validations re-run, close report §1.4), REF = the kept slot-18 close binary (the code of
`deab1af`), R0 `deab1af`, placement SAME, `--force`, exit 0): every timing gate MET on the loaded box — hecke 256 new_min 0.4686 s (REF 0.4684), ratio 1.006;
decomp 128 0.1032 s, ratio 0.992; `verdict_changes=0`; T2 0.9898 / 0.9869; T-C4 3.080 s —, `--all` 163/163 991.9 s, `--all-full` 180/180 1680.3 s;
`DIGESTS compared=33 differ=0 verdict=MATCH`; golden 18 058, A 11 827 / 0, B 6231 / 0; `NB3FULL verdict=OK` (132 cells, 4231 checks, 1013.1 s);
`LEAN_CENSUS_COMMITTED decls=1136 … planned=16 sorries=0 … verdict=OK`; `LEAN_REPLAY modules=113 ok=113 failed=0 peak_rss_gib=13.81 … verdict=OK`;
`LABEL_CENSUS … unresolved=0 stale=0`; post-W1: `cross_config.sh` PASS in seven arms (+ CPU-only, + notebook), `CheckThread` 3 / 3 clean;
`docs/implementation/slot19/WP-18_close_report.md`.
(1) **Outcome.** Roster **180 = 66 / 97 / 17** (`--all` 163, 114 `Hecke*`): `NumberFieldValidation` (WP-NF, fast; the seventh target `NumberField`),
`HeckeLValueValidation` (WP-LV, standard; extended by WP-LV2, WP-LIN, WP-BIL), `HeckeLatticeModuleValidation` (WP-LC, registered standard, slow by the
owner's ruling of 2026-10-03), `ConsoleReadOnlyTagValidation` (NB-2, fast), `ConsoleServeValidation` (NB-2, standard), `HeckeLambdaValidation` (WP-HL,
standard). **No golden event** (O4; `docs/implementation/slot19/golden_ledger.md`); digests unchanged. **Lean milestone M3 met** (F3 ACCEPT WITH REPAIRS,
0 B / 0 M / 8 m, all repaired by Lean generalisations); the M4 skeleton (16 `planned` rows). (2) **Packages:** §8 "Slot 19, the outcome (v1.24)".
(3) **Documents at the close** (the release commit + the close commit): [C] **v1.19.0** (the milestone-M3 `\LEAN` / `\LEANlit` markers, clause by clause per
`L19-6_F3_audit.md` §8 as amended by `L19-6_repairs.md` §3 and `L19-4_report.md` §3; Shimura's locators still marked unverified), [E] **1.19.0**,
[U] **0.3.0**, [L37] **0.4.0** (not binding), [CLI] **1.1.0** (PDF committed), [EX] 1.4.0 unchanged, [P] v3.10.2, [LP] v1.1. (4) **[OD] S19** additions
S19-N1 … N4: §8. (5) **Runs at the close** (`(1184, 37)` and E2 ×2 ended during W1 and are evaluated in `WP-RC_report.md`; the 691 level-3 Coates–Wiles run done after W1, P-NF2-7 confirmed (`nf691_run.md`); the θ-socle chain waiting)
→ slot 20's WP-RC20. (6) **Slot-20 re-cut**: §8, "Slot 20, re-cut from the slot-19 outcome" (`docs/implementation/slot20/00-slot20-plan.md` v0.1; its owner
questions O1–O13 open). (Numbering: v1.24.1 is slot 20's day zero (WP-1), the slot-20 close is **v1.25**.)

**Version 1.23.1 — 2026-10-03. Slot 19, day zero (WP-1); non-normative.** §8 "Slot 19" now mirrors `docs/implementation/slot19/00-slot19-plan.md` **v1.0**: the owner's rulings of 2026-10-03
(**all of O1-O15 accepted as recommended**; the `thm:welldef`(c) erratum confirmed, in [C] 1.18.0), L19-0's edits (L19-3 `model7_acyclic` central 210 min (band 130-480) with an early second Λ seat; Lean critical chain ≈ 5.5 h;
M3 acceptance by M3-a ... M3-g, `stated = 0`), the WP-LV interface amendment (`kind = linear | bilinear | congruence`, [E] `def:lvroute` at `1e2836a`) and the state of play: R19-1 done (`d4c7949`),
WP-2 done (`8722c45`) with F1 ACCEPT WITH REPAIRS (`b601bd4`, repairs running), L19-0 done (`01ad877`), L19-1 done (`stablecert_ES`), **L19-3 done: `model7_acyclic` proved in full** (`stated = 0`, `sorries = 0`), L19-2 running,
WP-RC paused (the lead watches the LAT37 cells). WP-1: `Registry/Slot19/` + `cmake/slot19/` stubs (WPNF, WPLC, WPLV, NB0, NB2, WPHL), `slot19_close_window.sh` (REF / R0 = `deab1af`, golden 18 058 / 11 827 / 6231, roster 174 / 158),
`EXPECT_NAMES` 174, shared binary `s19/bin/`. No normative rule changes; roster unchanged at 174 = 64 / 94 / 16. (The slot-19 close is **v1.24**.)

**Version 1.23 — 2026-10-03. Slot 18, close (WP-18); non-normative.**
**Status: W1 correctness MET; timing not a verdict (owner ruling of 2026-10-03: W1 under the declared load of our own three LAT37 cells)**
(`slot18_close_window.sh`, 2026-10-03 16:32:06 → 17:56:37 UTC, 5242.3 s incl. the REF build and the Lean replay, head `c044f64`, REF / R0 `dcd0c30`,
placement SAME, `--force` (prewindow `foreign_count=3`: the LAT37 cells), loaded box (3 LAT37 cells) plus another session's `rqaudit`): hecke 256 new_min
0.4878 s (REF 0.4933 s on the same box) abs MISS, paired ratio 0.987 MET; decomp 128 0.1034 s, ratio 0.998, MET; `verdict_changes=0`; T2 1.0294 / 1.0020 MET;
T-C4 3.166 s MET; `--all` 158/158 995.5 s, `--all-full` 174/174 1562.2 s; `DIGESTS compared=33 differ=0 verdict=MATCH`; golden 18 058, A 11 827 / 0,
B 6231 / 0; `NB3FULL verdict=OK` (132 cells, 4231 checks, 961.1 s); `LEAN_CENSUS_COMMITTED decls=823 … hyp_bad=0 … verdict=OK`; `LEAN_REPLAY modules=105
ok=105 failed=0 peak_rss_gib=13.80 … verdict=OK`; `LABEL_CENSUS … unresolved=0 stale=0`; `docs/implementation/slot18/WP-18_close_report.md`.
(1) **Outcome.** Roster **174 = 64 / 94 / 16** (`--all` 158): `CliManualCoverageValidation` (WP-M, fast), `HeckeLadicSplitValidation` (WP-19b) and
`EngineElimSessionValidation` (WP-19a, both standard). **One golden event, R1** (WP-4, owner O2, add-only, +302, F2 ACCEPT WITH REPAIRS); digests unchanged.
**Lean milestone M2 met** (F3 ACCEPT WITH REPAIRS). (2) **Packages:** §8 "Slot 18, the outcome (v1.23)". (3) **Documents at the close** (`c044f64` + the close
commit): [C] **v1.18.0** (81 `\LEAN` markers on 42 labels; the `thm:welldef`(c) proof erratum, confirmed by F3 and the owner), [E] **1.18.0**, [EX] **1.4.0**,
[L37] **0.3.0**, [CLI] **1.0.0** (PDF committed), [U] 0.2.1 unchanged, [P] v3.9.3, [LP] v1.1. (4) **[OD] S18** additions S18-N1 … N6: §8. (5) **Runs in flight at
the close** (LAT37 690 / 692 / 694; R18-3's E1 and sat cells; WP-5's E2; the quiet re-measure) → slot 19's WP-RC. (6) **Slot-19 re-cut**: §8, "Slot 19,
re-cut from the slot-18 outcome" (`docs/implementation/slot19/00-slot19-plan.md`).

---

**Version 1.22.1 — 2026-10-03. Slot 18, day zero (WP-1); non-normative.** §8 "Slot 18" now mirrors `docs/implementation/slot18/00-slot18-plan.md` **v1.0**: the owner's rulings of 2026-10-03
(**all of O1–O11 accepted as recommended**; O11 moot), the new core package **WP-M** (the command-line / console LaTeX-PDF user manual, generator + coverage validation, Fable referee F-M between F2 and F3,
PDF built at the close by WP-18), the wave table and budget (≈ 54 h of agent time). Roster forecast 171 → 172 (WP-M's `CliManualCoverageValidation`, fast). No normative rule changes. (Numbering: the slot-17 practice, v1.21.1 at day zero
then v1.22 at the close; the slot-18 close is **v1.23**.)

**Version 1.22 — 2026-10-02. Slot 17, close (WP-18); non-normative.**
**Status: W1 correctness MET; timing gate hecke 256 MISSED under foreign load, owner-accepted as environmental (owner ruling of 2026-10-02, relayed by the lead: timings not critical this slot; a quiet re-measure is carried to slot 18's W1)** (`slot17_close_window.sh`, 2026-10-02 18:54:56 → 19:59:26 UTC, 4059.5 s incl. the REF build, head `410d4e4`, REF / R0 `6863260`, placement SAME, **not a quiet box** (a foreign Lean build and a headless-chrome test of other sessions ran throughout: `OVERLAP watch_rows=1924 foreign_heavy_rows=1309`)): hecke 256 new_min 0.4782 s (REF 0.4624 s on the same box) **abs_gate MISS** (0.470), paired median ratio 0.997 ratio_guard MET; decomp 128 new_min 0.1018 s (REF 0.1006), ratio 1.004, MET; `verdict_changes=0`; T2 (10, 691) 1.0072, (160, 691) 0.9928 MET; T-C4 3.110 s MET;
`--all` 155/155 1011.6 s, `--all-full` 171/171 1556.5 s; `DIGESTS compared=33 differ=0 verdict=MATCH`, golden `COUNT golden_entries printed=17756 expected=17756 MATCH`, A 11 821 / 0, B 5935 / 0; `NB3FULL rc=0 wall_s=965.0 peak_rss_kb=806888 … arm=NB3_FULL cells=132 … 4036 checks, 0 failing` → `NB3FULL verdict=OK`; `LEAN_CENSUS_COMMITTED decls=440 proved=383 proved_mod_lit=20 stated=13 … hyp_bad=0 sorries_vs_stated=eq leanfile=PASS verdict=OK`; `LABEL_CENSUS … unresolved=0 stale=0`; `docs/implementation/slot17/WP-18_close_report.md`.
(1) **Outcome.** Roster **171 = 63 fast / 92 standard / 16 slow** (169 = 61 / 92 / 16 at the slot-16 close), **109 `Hecke*`** names, `--all` 155. Two names
added, both `fast`: `HeckeSatCertDumpValidation` (L17-2, an env-interlocked scratch emitter, `HECKE_DUMP_SAT_CERT`) and `HeckeSmallCarriesValidation`
(WP-8, refusal tests; 53 checks after WP-17). **One golden event, R1** (WP-4, owner O2, add-only, Fable F2 ACCEPT WITH REPAIRS 0 B / 0 M / 7 m): expect set
`e2c075b`, emission `1d0be42` (single parent), +168 entries at 18 new points (six `LEVELN`, six certified `LOEWY_RING`, six `NEB`), 0 changed, 0 removed;
**17 756** entries, tier A **11 821** / 0, tier B **5935** / 0; the four digests unchanged; `golden_landing_check.sh 6863260` → `LANDING merges=0 orphans=0
verdict=OK`; `docs/implementation/slot17/golden_ledger.md`. Label census `unresolved=0 stale=0` (read from the text). Lean census of record
`LEAN_CENSUS decls=440 proved=383 proved_mod_lit=20 stated=13 planned=0 sorries=13 global_axioms=0 unresolved=0 stale=0 lit_hyp=24 native=0
gl2_consts=3637 escapes=0 modlit_bad=0 hyp_bad=0 verdict=OK` — **Lean milestone M1 met** (F3 ACCEPT WITH REPAIRS, 0 B / 4 M / 9 m, repaired).
(2) **Packages landed** (details in §8 "Slot 17, the outcome (v1.22)"): WP-1 day zero; WP-2 / WP-3 the contract drafts and the Fable referee F1; WP-4 the golden
event R1; WP-5 level `N` beyond `5.5·10^4` (`__int128` cocycles); WP-6 nebentypus at scale ((a) sparse cokernel with a character, (b) `T_{p^ν}`); WP-7 the
isotropy model's open halves; WP-8 small carries; WP-9 census 3.2 **staged, not published** (owner-gated; `sat_cells_done=1073 of 1459`, the 386 cells
`610 ≤ n ≤ 700` in the November kit); WP-17 audit repairs; WP-C21 the November kit (`docs/cluster/noctua2/LAUNCH_2026-11.md`); R17-1 … R17-4 research;
L17-0 … L17-6 the Lean lane (M1); LAT37 locally (`(700, 37)`, `(698, 37)`, `(696, 37)`; 694 / 692 / 690 carried to slot 18); [L37] v0.2.0-pre.2 (F4).
**Not run:** WP-6c (Galois ring `d ≥ 2`), L17-7 (FLT closure build), WP-19a / b / c, WP-C20 (no cluster return in the slot).
(3) **Binding documents at the close.** [C] **v1.17.0** released with the first **`\LEAN` markers** (42 clause-scoped markers on 20 labels, per
`slot17/lean_taggable_labels.md`), [E] **1.17.0**, [U] **0.2.1**, [EX] **1.3.0** (not binding) — all under the owner's O3 on F1's ACCEPT WITH REPAIRS (B-1 settled
by the owner's ruling of 2026-10-02: (R) restated on congruence-free classes; (NB4)(c) `\PROVED`); commit `410d4e4`. [P] v3.9.3, [LP] v1.0 (+ L17-0's
v1.1 proposal), [L37] **0.2.0-pre.2** (not binding, F4 ACCEPT WITH REPAIRS, repaired).
(4) **The [OD] S17 register** (owner rulings O1–O10 of 2026-10-01 and the rulings of 2026-10-02): §8 below.
(5) **Slot-18 re-cut**: §8, "Slot 18, re-cut from the slot-17 outcome" — it points at `docs/implementation/slot18/00-slot18-plan.md` v0.1, whose owner
questions O1–O11 are open.

---

**Version 1.21.1 — 2026-10-02. Slot 17, day zero (WP-1); non-normative pointer.** §8 gains one line: "Slot 17's packages and waves: `docs/implementation/slot17/00-slot17-plan.md` v1.x". No normative rule changes.

**Version 1.21 — 2026-10-01. Slot 16, close (WP-18; part A the documents, part B window W1 and the census-3.1 publication); non-normative.**
**Status: W1 MET** (part B, 2026-10-02 01:55 → 02:51 UTC, head `edba09c`, REF `b8a196d`, placement SAME, quiet box): hecke 256 new_min 0.4230 s (REF 0.4317), paired median ratio 0.994, headroom 10.0 %; decomp 128 new_min 0.0897 s (REF 0.0921), ratio 1.000, headroom 17.7 %, verdict MET on both,
`verdict_changes=0`; T2 (10, 691) 1.0251, (160, 691) 1.0040 MET; T-C4 2.323 s MET; `--all` 153/153 863.6 s, `--all-full` 169/169 1359.6 s; `DIGESTS compared=33 differ=0 verdict=MATCH`; `NB3FULL rc=0 wall_s=845.5 peak_rss_kb=6712544 … arm=NB3_FULL cells=132 … 3808 checks, 0 failing` → `NB3FULL verdict=OK`; census 3.1 published (`sat_cells_done=897 of 1459`); `docs/implementation/slot16/WP-18_close_report.md` §1.
(1) **Outcome.** Roster **169 = 61 fast / 92 standard / 16 slow** (163 = 59 / 88 / 16 at the slot-15 close after S15-O1), **108 `Hecke*`** names, `--all` 153
(derived from the source at `7f36871`; WP-15's `--list` read the same). Six names added, each through its own `Registry/Slot16/<name>.cpp` pair:
`LeanCensusFileValidation` (L16-0, `fast`), `HeckeTauDumpValidation` (L16-4, `fast`, env-interlocked scratch emitter), `HeckeSaturationDefectValidation`
(WP-5), `HeckeNebentypusValidation` (WP-10, + WP-11's arms), `HeckeHidaCMValidation` (WP-15, stretch), `HeckeIsotropyModelEllValidation` (WP-16, stretch; all
`standard`). Plan §7 forecast 166 core / ≤ 167 with WP-16; the extra names are L16-4's dump hook (a name, not an arm) and the stretch WP-15. **Zero golden
events** (owner O3): R0 = R1 = `b8a196d`, 17 588 entries, tiers 11 687 / 5901, the reference byte-identical (sha256 `828dfaff…ec124df5`),
`golden_landing_check.sh b8a196d` → `LANDING merges=0 orphans=0 verdict=OK`; the four digests unchanged at every package gate (W1 re-compares them);
`docs/implementation/slot16/golden_ledger.md`. Label census `unresolved=0 stale=0` (read from the text). Lean census of record `decls=258 proved=194
proved_mod_lit=16 stated=32 sorries=32 global_axioms=0 unresolved=0 stale=0 verdict=OK`.
(2) **Packages landed** (details in §8 "Slot 16, the outcome (v1.21)"): WP-1 day zero; WP-2 carry fixes ((R3m)); WP-3 census joins by eigen-system and the
per-source-set `u_ell`; WP-4 census 3.1 (staged; **published at the close by owner default**, part B); WP-5 the saturation-defect Tor package; WP-6 console verb
`hecke_ring_algebra` + script 029; WP-8 open citations; WP-9 / 9b (NB5) / (NB6) transcription; WP-10 / WP-11 nebentypus code, (NB4) sharp form, `m = 2`;
WP-12 / WP-14 the contract drafts and the Fable referee; WP-13 general `N` (`κ_N`, `α_d` on the presentation, `N = 30030`); WP-15 [U] part 2 in code; WP-16 the
ℓ-local isotropy model at `ell = 3`; WP-17 audit repairs; WP-C19 / C19b / C19c the October kit; L16-0 … L16-6 the Lean lane; the [L37] report.
**Not run:** WP-19a (GPU G1), WP-19b (`p ≠ ell` digit split), WP-19c (Proposition M landing); WP-C20 (no cluster return in the slot).
(3) **Binding documents at the close.** [C] **v1.16.0** released (owner O2; WP-14 ACCEPT WITH REPAIRS, 0 blocking, 16 / 16 confirmed), [U] **0.2.0**
owner-signed with **0.1.1 signed** (O2), [E] **1.16.2** (one locator), [EX] **1.2.2** (not binding), [P] v3.9.3, Lean plan v1.0; [L37] v0.1.0-pre.2
(not binding); `docs/implementation/slot16/contract_release_report.md`.
(4) **The [OD] S16 register** (owner rulings O1–O8 and the lead notes of 2026-10-01): §8 below.
(5) **Slot-17 re-cut**: §8, "Slot 17, re-cut from the slot-16 outcome".

---

**Version 1.20.3 — 2026-10-01. Slot 16, day zero (WP-1); non-normative pointer.** §8 gains one line: "Slot 16's packages and waves: `docs/implementation/slot16/00-slot16-plan.md` v1.x" (carry note: that plan's §10). No normative rule changes.

**Version 1.20.2 — 2026-10-01. Slot 15, post-close (census edition 3, WP-C18, the slot-16 additions); non-normative.** What this version records:
(1) **WP-C18 done** (`docs/implementation/slot15/WP-C18_noctua2_rb_report.md`): cluster-A RB1–RB4 (jobs 34573807–10, build `2ed349a`) all PASS,
3015 / 3015 records, `verify()` = 0, 51 143 ideals all final; **C1b (`ell = 61 … 103`, every even `n ≤ 700`) complete, 3500 / 3500**; six-cell
cross-commit spot check identical modulo `commit`. Science (CMPD): max Loewy(A) = 2 at all ten primes, (R) 0 violations on the 2165 non-reduced rows,
Kummer 40 713 / 40 713, F9 24 / 24, I-8's k2 law 174 / 174, Proposition D's rationality clause exact at 71 / 79 / 83 / 103; the onset law predicts no
Loewy-4 cell inside `n ≤ 700` and none is seen (its positive half untested there). Cost: 2427.8 core-h, ×1.10 of "expected"; the overrun is the `T_2`
job loop after the ext pass (`jobs = 11 × threads = 3`).
(2) **Census edition 3 published (WP-15, C3-1 / C3-2;** `docs/implementation/slot15/WP-15_report.md`**)** in
`docs/matrix-engine/results/congruence_census/edition3/`, `hecke_census_dataset/v2`, beside edition 2 (owner request of 2026-10-01 in place of data
condition D1): 80 293 rows (edition 2 + 77 008 at `ell = 17 … 103`), complete at 61 … 103, **partial at 17 … 59** (3064 of 7350 C1 cells missing,
`missing.txt`) — the missing cells, RA1–RA2 and RS1–RS3, become **edition 3.1, add-only**. `saturated` / `mult_one` on 976 rows only (arm (T) dropped on 230
cells, see (4)); C-F9 held 155 / 155 evaluable new rows.
(3) **Documentation**: [E] **v1.16.1** (a patch: `sec:census`'s edition-3 paragraph, one evidence row in `pr:latticesplit`, one sentence in
`pr:kfonset`; no statement change), [EX] **1.2.1** (subsection `s15:census3`). **S15-O1 landed**: arm (C3) is `HeckeRingLoewyDigitSlowValidation`
(`slow`, roster 163 = 59 / 88 / 16), and the owner set `HeckeRingLoewyValidation`'s target to **64 s** on 2026-10-01 (63.8 s after the
validation-local module cache).
(4) **Slot-16 additions** (the re-cut table in §8): the **saturation-defect Tor package** (owner-approved 2026-10-01); **arm (T)'s `u_ell` fix**, then
census **3.1**; the console verb **`hecke_ring_algebra` + script 029** (Q6, split from the census row); `HeckeCensusLatticeValidation`'s `u_ell`
budget / eigen-system id matching; for the October cluster plan **WP-C19**: RA1–RA2, RS1–RS3 and the 17 `ell = 37` lattice cells, the **`T_2` job loop at
`jobs = 40`** in the cluster kit, and the October quota inference (**≥ 3584 core-h** enforced limit, from four 7 h × 128-core jobs admitted at once).
No code, golden, digest, record or roster change in this version. Companion versions: [C] v1.15.0, [E] **v1.16.1**, [EX] **1.2.1**, [U] v0.1.0
(0.1.1-pre.6 in the tree), [P] v3.9.3, Lean plan v1.0.

**Version 1.20.1 — 2026-10-01. Slot 15, post-close (the owner's rulings); non-normative.** The owner agreed on 2026-10-01 to **all** open items
and recommendations of `docs/implementation/slot15/WP-18_close_report.md` (S15-O1 … O5) and to **all** recommendations Q1–Q14 of the Lean
programme plan. What this version records (the [OD] S15 register below carries the rulings):
(1) **S15-O1 ruled**: `HeckeRingLoewyValidation`'s arm (C3) (the beyond-`2^64` digit cell, `ell = 5`, `K = 28`) moves to the `slow` tier or behind
an env hook, as recommended; the code change is a slot-16 item (not made here; the roster stays 162 = 59 / 88 / 15 until it lands).
(2) **S15-O2 ruled, and done**: [E] `pr:latticesplit` is **refuted as stated** at `ell = 37` (the 18 certified C1a records `eis(a, a+5)`,
`n = 654 … 700`, `loewy_A = 4`, Hilbert `[1,1,1,1]`, module Loewy `[3,2,2,1]`; the forms side; WP-13's `Z/37²` lattice at `(654, 37)` ideal 8,
`status=failed`, `first_fail=(2,2)`) and restated under its label as the conjecture (R) with the Kummer–Frobenius exclusion past the onset weight
`ℓw + t(ℓ+1)`, with its evidence table; the onset is the new `\CONJ` `pr:kfonset` ([E] 1.15.1-pre.7). Then, per Q13, **[E] v1.16.0 released**
(changelog of pre.1 … pre.7) and **[EX] 1.2.0 released** (pre.14: WP-12's entries A, A′, A″, B–E and WP-9's proposal A–D applied). **[U] untouched**
(Q13: as is; binding v0.1.0, 0.1.1-pre.6 in the tree): WP-12's (U-1) is a `\CONJ` remark, not a pure pointer, so it goes to slot 16 with
[E]'s (E-2) (the `\CONJ` Frobenius-layer Prediction F1) and (E-3) (the I-8 tag note, if [E] ever names `twisted_eis_*`).
(3) **S15-O3 ruled**: the Lean plan `docs/implementation/lean/00-lean-programme-plan.md` is **v1.0 (approved)**; Q1–Q14 RULED at the
recommendation (§5 of the plan), which unblocks L16-0 … L16-6 (the row "The Lean programme" of the slot-16 re-cut no longer waits).
(4) **S15-O4 ruled**: the **17 remaining `ell = 37` Loewy-4 lattice cells** (`n = 656 … 676, 690 … 700`; ≈ 116 core-h, ≈ 8.5 GB each; WP-13's
case env) are **assigned to WP-C19** (cluster).
(5) **S15-O5 ruled**: the October cluster re-plan (WP-C19's re-chunk, WP-C20's sheet) **waits for RB1–RB4** to return and their quota to be read.
No code, golden, digest, record or roster change. Companion versions: [C] v1.15.0, [E] **v1.16.0**, [EX] **1.2.0**, [U] v0.1.0 (0.1.1-pre.6 in the
tree), [P] v3.9.3, Lean plan **v1.0**.

**Version 1.20 — 2026-10-01. Slot 15, close (WP-18); non-normative.** **Status: W1 DONE 2026-10-01** (quiet box confirmed by the owner; head `804aca7`, REF `7557127`, placement SAME; hecke 256 0.4232 s ratio 0.996, decomp 128 0.0910 s ratio 1.003, both MET, `verdict_changes=0`; T2 1.0067 / 1.0123 MET; T-C4 2.285 s MET; `--all` 147/147 754.0 s, `--all-full` 162/162 1249.8 s; `DIGESTS compared=33 differ=0 MATCH`; `docs/implementation/slot15/WP-18_close_report.md` §1).
(1) **Outcome.** Roster **162 = 59 fast / 88 standard / 15 slow** (159 = 59 / 85 / 15 at the slot-14 close), **102 `Hecke*`** names, `--all` 147. Three names added,
each through its own `Registry/Slot15/WP<n>.cpp` pair, all `standard`: `HeckeHidaComponentsValidation` (WP-6), `HeckeLevelNHeilbronnValidation` (WP-7),
`HeckeLevelNSparseValidation` (WP-8); WP-5, WP-9, WP-17 and WP-20 added arms only. **Zero golden events** (Q9): R0 = R1 = `7557127`, 17 588 entries, tiers
11 687 / 5901, the reference byte-identical (sha256 `828dfaff…ec124df5`, as at slot-13 R2), `golden_landing_check.sh 7557127` OK; **all four digests
unchanged** (EngineDet `0x3dddd2ef9a8efd`, ExtDet `0xaef77d786b4f29b4`, heavy `0x9ed8b83a2fb26622`, ConsoleDet `0xf6ed04bbe8e6b60a`);
`docs/implementation/slot15/golden_ledger.md`. Label census `unresolved=0 stale=0` (read from the text). Forecast ([S15] §7) was 161; the extra name is
WP-8's own validation (the plan had WP-8 adding arms to WP-7's).
(2) **Packages landed.** WP-1 day zero (`0696e52`, `8385ae4`; the `build_ref` stdout fix, whose `--selftest-ref-capture` PASSED before W1 and whose REF
build ran clean in W1); WP-2 slot-14 doc debt (`284adc1`); **WP-3 / WP-4** [C] `sec:nebentypus` (general `N`, `chi` into `F_q^x`, no layering; contract
only) and `sec:saturation` (P15, P17, P18, P20, `prop:cohforms`), Fable referee ACCEPT WITH REPAIRS, 0 blocking, repairs at pre.2 (`170a8aa`, `e1978f9`,
`255505d`); **WP-5** `stable` as a certificate (`CertifyStable`, `cor:stablecert` in the B1 form, field `stable_cert=certified|reading|none`) and the
digit route for `ell^K >= 2^64` (`1d07a57` … `cf5a4fd`), Fable audit ACCEPT WITH REPAIRS, M1–M6 repaired (`e0487c5`); **WP-6** `HeckeHidaComponents`
(bignum-free `B_k/k mod ell^K`, [U] (U1)–(U3) readings; `a7c8144`); **WP-7** Heilbronn–Merel `H_{N,p}` on the cokernel presentation, (LN3) closed on
both halves (`5f38617`); **WP-8** the sparse cokernel (natural RREF, sparse = dense entrywise), level-change fibre maps, degeneracy specs on the model,
the cost model (`36f7e7f`, `fad65a8`); **WP-9** (R3) at scale: 1881 Merel-candidate cells, prime `N <= 10^4`, weight 2, `e >= 3` = Wake–Wang-Erickson
Table 1 exactly (`6947612`, `0686f74`; `WP-9_r3.tsv`); **WP-12** desk research (two passes; the `ell = 37` counterexample to [E] `pr:latticesplit`,
the F1 onset law, Proposition D's rationality clause, S4 at `(59, 16)`, Bellaïche–Khare closed); **WP-13** C-F9 FAILS at `(654, 37)` ideal 8 (the
Loewy-4 ideal; 6.8 h, 8.5 GB), `nx_l37` 29 / 29; **WP-14** census edition 3 step C3-0 (schema + builder, `EDITION1_NATIVE` / `EDITION2_NATIVE`
reproduced; nothing published); **WP-17** audit repairs (WP-8 LOW 1–4, WP-9 items 1–4, [C] pre.3's WP-8 sentence, documentation); **WP-19** forms-side
proofs (`cl:mkfaithful` PROVED, `cl:formsF9` with its torsion term; [E] pre.4, [EX] pre.13); **WP-20** forms-side code (F9 torsion guard, the
corrected F9 gated on every `H^1` row, `saturated` / `mult_one`); the Lean programme plan draft (`docs/implementation/lean/00-lean-programme-plan.md`,
planning only). **Not run:** WP-15 (data condition D1 not met), WP-C18 (no tarball returned inside the slot), WP-C19 (waits for RB1–4, Q7), WP-16a
/ WP-16c (stretch; no time). WP-10 / WP-11 are slot 16's by Q3.
(3) **Binding documents at the close.** [C] **v1.15.0 released** (owner Q2: release at the close on WP-4's ACCEPT; `10da91a`, no git tag). The WP-17 sentence of
pre.3 (`sec:levelN`'s scope: fibre maps on the cokernel presentation by naturality; `alpha_d`, `d > 1`, on the model only) **was not refereed**: it is
listed in the release changelog as such, for the slot-16 referee. [E] stays **1.15.1-pre.6** and [EX] **1.2.0-pre.13**: Q13's release targets
([E] 1.16.0, [EX] 1.2.0) **wait for the owner's ruling on the `pr:latticesplit` edit** (WP-12's [E] proposal E-1, the counterexample entry A′ / A″ of
`WP-12_EX_proposal.md`, WP-9's [EX] proposal); recorded as **pending owner sign-off**, not released here. [U] stays binding at 0.1.0 with 0.1.1-pre.6 in
the tree (Q13: as is). [P] v3.9.3 unchanged.
(4) **Open owner questions at the close** (the [OD] S15 register below): **S15-O1** `HeckeRingLoewyValidation` runs ≈ 85 s against the 60 s target of a
`standard` name (W1: 81.9 s inside `--all`); recommendation: move arm (C3) (the beyond-`2^64` digit cell at `ell = 5`, `K = 28`) to the `slow` tier, or behind an
env hook; **not changed** here. **S15-O2** the `pr:latticesplit` edit and the [E] 1.16.0 / [EX] 1.2.0 releases. **S15-O3** the Lean programme's
questions Q1–Q14 (plan §5), which gate the slot-16 Lean packages L16-0 … L16-6. **S15-O4** the 17 remaining `ell = 37` Loewy-4 lattice cells as cluster
candidates (≈ 116 core-h, ≈ 8.5 GB each). **S15-O5** the October cluster re-plan (Q7) once RB1–4 have returned.
(5) **Slot-16 re-cut**: §8, "Slot 15, the outcome (v1.20)" and "Slot 16, re-cut from the slot-15 outcome".

---

**Version 1.19.1 — 2026-09-30. Slot 15, day zero (WP-1); non-normative carry note** (`docs/implementation/slot15/00-slot15-plan.md` §10). No normative rule changes.
(1) **The slot-15 plan and its shape:** contract-first nebentypus plus the Loewy saturation statements ([C] v1.15.0-pre.1, WP-3 / WP-4); level `N` at scale (WP-7, WP-8, WP-9);
WP-14c in C++ (WP-6); findings (WP-12); the cluster track; census edition 3 as a conditional track. (2) **Model-staffing rule** (owner, relayed 2026-09-30): Sonnet for
easy / standard implementation, Opus for long or delicate work, **Fable only for critical audits** (contract sections, certificate soundness, golden events), every other
audit cross-model (Opus <-> Sonnet); this refines the slot-7 rule "Fable for audits". (3) **Concurrency rule** unchanged (<= 5 agents, <= 3 while a Fable agent runs, <= 3 builds,
exclusive memory windows, W1 alone). (4) **Cluster rule refinement:** walls up to 24 h are planned as claimable (owner, 2026-09-30); `MaxWall` is read in each sheet's step 0;
rule 23 as amended (kits only, the owner submits) stands. (5) **Census edition 3:** column set signed off 2026-09-30 as `hecke_census_dataset/v2`, its build conditional on data.
(6) **P12** owner-signed 2026-09-30 (`noctua2_section_m/`, [E] 1.15.1-pre.3); the legacy-arm fix `c0566e2`. (7) **§8's slot-15 section** replaces v1.19 (6)'s one-line re-cut with the
plan's WP list. **Owner rulings of 2026-09-30 (answers to plan §11; record `s15/owner_rulings_0930.md`), recorded as lead rulings:** **Q1** the shape of §1 (about 10 h wall ceiling for the
core, model column, cross-model audits; Fable only WP-4, the WP-5 audit, golden events). **Q2** [C] `sec:nebentypus` for **general `N`**, characters `chi: (Z/N)^x -> F_q^x`, `q = ell^d`
a general finite coefficient field, `ord chi | q - 1`; **no layering** (no `Gamma_0(ell)`-first, no `F_ell`-first stage); [C] v1.15.0 released at the close if WP-4 accepts.
**Q3** nebentypus code (WP-10, WP-11) moves to **slot 16** (so `Registry/Slot15/` has no WP-10 / WP-11 pair). **Q4** yes: a certified `stable` field on P15 / P17 ACCEPT; [E] may change
"readings, not certificates" for that verdict. **Q5** `N <= 10^4` at weight 2 suffices for slot 15; more general `N` and [U] part 2 go to slot 16. **Q6** census edition 3 *beside*
edition 2 (siblings); console verb `hecke_ring_algebra` and script 029 approved; data condition D1 as stated. **Q7** the October cluster plan is redone once RB1-4 have returned;
WP-C19 waits. **Q8** Bellaiche-Khare and Swinnerton-Dyer papers read-only under `<private-library>`, never written or copied into
the tree; Gross (companion forms) unavailable until about 2026-10-07; agents may fetch arXiv / open-access copies into scratch. **Q9** zero-golden-event slot. **Q10** GPU G1 as a stretch.
**Q11** `ell`-local isotropy model to slot 16. **Q12** findings land everywhere ([EX], and [U] / [E] proposals). **Q13** [E] 1.16.0 and [EX] 1.2.0 at the close; [U] 0.1.1 as is.
**Q14** carries kept, WP-16c a stretch. **Q15** as recommended (torsion guard for F9; weaken the `M_k` claim only if no proof; census columns saturated / mult_one added), with the
torsion-aware wording of plan WP-19 (c) (`c1b45cd`). **WP-1 (day zero) landed:** `Registry/Slot15/` + `cmake/slot15/` stubs for WP-5, 6, 7, 8, 16a (empty; roster stays
159 = 59 / 85 / 15), both include guards allow-list `Registry/Slot15/*.cpp`, and `slot15_close_window.sh` with the `build_ref` stdout-capture bug fixed (`say` / `summ` inside the
command substitution now go to stderr; `--selftest-ref-capture` checks it).

---

**Version 1.19 — 2026-09-29. Slot 14, close (WP-17); non-normative.** **Status: W1 DONE 2026-09-29** (quiet box confirmed by the owner; head `31d31b9`, REF `e8ec72d`, placement SAME; hecke 256 0.3951 s ratio 0.983, decomp 128 0.0906 s ratio 0.976, both MET, `verdict_changes=0`; T2 0.5619 / 0.9372 MET; T-C4 2.330 s MET; `--all` 702.1 s, `--all-full` 1240.3 s; `WP-17_report.md` §6). (1) **Outcome.** `--all-full` passes **159/159**; roster **159 = 59 fast / 85 standard / 15 slow**
(155 = 58 / 82 / 15 at the slot-13 close), 99 `Hecke*` names, `--all` 144. Four names added, each through its own `Registry/Slot14/WP<n>.cpp` pair:
`ValidationHarnessCatchValidation` (WP-2, `fast`), `HeckeRingLoewyValidation` (WP-6, `standard`), `HeckeUEllStreamValidation` (WP-10 + G0, `standard`),
`HeckeLevelNValidation` (WP-12, `standard`). **Zero golden events** (Q14): R0 = R1 = `e8ec72d`, 17 588 entries, tiers 11 687 / 5901, the reference
byte-identical, `golden_landing_check.sh e8ec72d` OK; **all four digests unchanged** from slot 13's R2 (EngineDet `0x3dddd2ef9a8efd`, ExtDet
`0xaef77d786b4f29b4`, heavy `0x9ed8b83a2fb26622`, ConsoleDet `0xf6ed04bbe8e6b60a`); `docs/implementation/slot14/golden_ledger.md`. The five guards clean
(`raw_mod_calls` 208 / 0 outside), label census `unresolved=0 stale=0`. (2) **Packages landed.** WP-1 day zero; WP-2 harness catch path and kit hygiene
(`e8dea2f`); WP-3 G1 / G2 and device release (`bc35e61`); WP-6 the `Z/ell^K` Hecke-algebra route (`732c8aa`, [M1]'s route R1 in C++); WP-10 streaming +
parallel setup and G0's rank-one closed form (`3580160`, `a249a6d`, `714e553`), **default-on** (Q8); WP-12 level `N` on the model, gated by Q4
(`7a5158d`, `8feb6bc`, review repairs S-1..S-3, M-1..M-3, M-5, M-7, M-8; [C] v1.14.2 `sec:levelN` built); WP-14b (`e3eb68f`), WP-14c (Python; C++ deferred to
slot 15), WP-15 / WP-16 audit and repairs (`3addab3`); document packages WP-4, 5, 7, 8, 9, 13 ([C] v1.14.0, [E] v1.15.0, [EX] 1.1.0 released; [U] v0.1.0
binding). (3) **Rulings recorded.** Owner Q4 (WP-12 runs), Q8 (levers default-on) and the audit rulings **Q-A ... Q-H** of v1.18.3 (Q-A [U] binding; Q-B run-2
data signed off, L1-L4 to [C] v1.14.1, L5 to [U]; Q-C [E] carries the `Z/ell^K` route as *readings, not certificates*; Q-D the frozen `u_ell_rss/v2-2026-09-17`
model kept; Q-E P18 / P20 to the slot-15 referee; Q-F the WP-12 flip is a Z bump; Q-G the interim entry; Q-H the lever lemma enters [C]) stand as recorded in
v1.18.3. (4) **Cluster and data packages** WP-C2 ... C16 (run-1 and September cluster-B analyses, (Hi11) / (Hi12) held, the weight-shift run, the residual classifier
I-2, the I-3+ implementation plan (planning only, WP-C14), the dihedral-over-`F_{ell^r}` plan (WP-C16)), WP-L1 / L2, WP-Q1 / Q2, WP-U1, WP-F1, WP-M1: no C++,
no golden line, no registration. Rule 23 as amended in v1.18.2 (cluster-A owner-submitted only) is unchanged. (5) **Pending, explicitly.** (Window W1 was run 2026-09-29, see the status line.) **P12's cluster half** ([E]), which needs the owner's sign-off of the section-M data — **applied 2026-09-30** (owner sign-off that day: the data set `docs/matrix-engine/results/noctua2_section_m/` published, [E] v1.15.1-pre.3 `pr:latticesplit`'s *Evidence*, tag CONJ); [C] pre.2's and [U]'s code maps ([C] / [U]
edits, other agents); the cross-config line and `CheckThread` on the four new names (lead follow-up, as in slots 12 and 13). (6) **Slot-15 re-cut (carried):**
the Heilbronn-Merel action `H_{N,p}` and the sparse cokernel route, composite-`N` degeneracies; I-3+ (WP-C14) and census edition 3 (owner: no dataset v2
before it); nebentypus (owner Q-b); the digit route for `ell^K >= 2^64` in the Hecke-algebra route; P15 / P17 / P18 / P20 refereeing; WP-14c's C++.

---

**Version 1.18.3 — 2026-09-29. Slot 14, interim (owner rulings of 2026-09-29 and the contract-currency audit); non-normative.**
Audit: `docs/implementation/slot14/AUDIT_contract_currency_2026-09-29.md` (Fable, `7afd7f0`), §3.3. The owner's answers to [S14] §9
(2026-09-28/29) **supersede v1.18.2's lead rulings** (its Q2/Q3/Q4/Q5/Q8 lines below are STALE and stand only as history): **Q2/Q3** — run-1 data
published (`noctua2_run1/`), [C] v1.14.0, [E] v1.15.0, [EX] 1.1.0 **released** (WP-13, `e459579`); **Q5** — [U] v0.1.0 is **binding**
(`611c565`; [U] joins the binding documents: CLAUDE.md's list, this plan's, cited by label; current tree text 0.1.1-pre.4, unsigned);
**Q8** — all three WP-10 levers (low-rank `Auto`, coset streaming, parallel serial phase) and G0's closed form are **default-on** with opt-outs
(`3580160`, `714e553`; env `HECKE_U_ELL_LOW_RANK=0`, `HECKE_COSET_STREAM=0`, `HECKE_PARALLEL_SETUP=0`, `HECKE_RANK1_CLOSED_FORM=0`);
**Q4** — WP-12 (level-`N` code) **approved 2026-09-29**. Landed code: WP-2 (`e8dea2f`, `ValidationHarnessCatchValidation` — closes v1.18.1 (3)),
WP-3 (`bc35e61`, G1/G2, device release), WP-6 (`732c8aa`, `HeckeRingLoewyValidation`), WP-10 (`3580160`), WP-14b (`e3eb68f`), WP-16 (`3addab3`),
G0 (`a249a6d`, `714e553`); roster **158 = 59 fast / 84 standard / 15 slow**, `--all` 143/143, golden 11687/0 and 5901/0, four digests unchanged,
zero golden events so far (Q14). Non-code packages WP-4/5/7/8/9/11/13/14a/15, WP-C1…C16, WP-L1/L2, WP-Q1/Q2, WP-U1, WP-14c (Python) as listed in
[S14] §0 and `HANDOVER.md`. **Owner rulings Q-A…Q-H of the audit, 2026-09-29 (all eight recommendations accepted):** **Q-A** [U] is binding.
**Q-B** the cluster-B second-run data is signed off: L1–L4 enter [C] as `\COMP` sentences in v1.14.1, L5 enters [U] (not yet applied). **Q-C** [E]
carries the audit's §3.2 text for WP-6's `Z/ell^K` Hecke-algebra route — *readings, not certificates* (applied: [E] v1.15.1-pre.2); P15 / P17
are refereed in slot 15. **Q-D** the frozen `u_ell` RSS model `u_ell_rss/v2-2026-09-17` is **kept** (conservative `u_ell_over_budget`; a re-fit
would be a value change and must bump the version); recorded in [E] v1.15.1-pre.2 at the (d1) cost cap. **Q-E** P18 and P20 go to the slot-15
referee. **Q-F** WP-12's flip of "not built at v1.14.0" is a Z bump, [C] v1.14.1, no X-type change. **Q-G** this interim entry. **Q-H** the
lever lemma (rank claim) enters [C] (not yet applied). Also applied with this entry: ENGINE_API G1/G2 paragraph, `Hecke/README.md` R1–R3, the
catalogue entry for `HeckeRingLoewyValidation`, CLAUDE.md's binding list. Open: Q1, Q6, Q9, Q10–Q13 at their defaults. Not applied here ([C], [U],
[EX] belong to other agents): L1–L4, Q-H's lemma, the WP-12 flip.

---

**Version 1.18.2 — 2026-09-28. Slot 14, WP-1 (day zero); non-normative.** (1) **§0's pre-plan packages
recorded as slot-14 work** ([S14] `docs/implementation/slot14/00-slot14-plan.md` §0): the cluster-A /
cluster-B cluster kit (WP-C1, C1b, C1m, C1r, C5, `b5de984` … `7e37e76`), the LMFDB / literature frontier
map (WP-L1, `1313d51`), the `(2420, 2411)` overflow / loudness audit (WP-C2, SAFE, guards G1 / G2
proposed, `cf6ffad`), the Loewy note (WP-M1, `07f413f`), cluster-A run 1's analysis (WP-C3 / WP-C4, no
value mismatch, (Hi12) `(2420, 2411)` held, seven harness findings, `9f6b3aa`, `db976db`) and [EX]
1.1.0-pre.2 + proposals P1–P11 (WP-D1, `c85cd15`, `db976db`). No source file, golden line, digest or
registration moved by any of them. (2) **Rule 23 amended** (owner, this session, Q1): **cluster-A is an
owner-submitted host only** — agents write kits (`docs/cluster/noctua2/`) and read the tarballs the
owner returns (into scratch, never the tree), but **no agent connects to cluster-A or any other roadmap
host**; the owner alone submits. This narrows, and does not lift, the "no contact with the roadmap
hosts" clause of rule 23 (v1.15 §S11-4, S11-13). (3) **The concurrency rule of [S14] §3 recorded**: at
most 5 agents at once, at most 3 while a Fable agent runs, at most 3 concurrent builds (C: 15 GB
floor), exclusive memory windows for any run measuring RSS, W1 runs alone, one worktree/build per
agent removed only after its agent is stopped and its branch merged. (4) **CLAUDE.md wording fix**
(pointed out by [S14] §1 headline 4 lead-in): the env-table row for `HECKE_CENSUS_LATTICE_CELLS` reads
"the cell list wins" — this is **false** for that validation, since `CELLS` only *filters inside* the
`_ALL` arm rather than standing alone ([C3] §5); WP-2 fixes the runtime behaviour, this entry flags the
sentence for CLAUDE.md's slot-14 pass. (5) **[S14] §9 owner questions Q1–Q14: the owner has not
answered.** Every bracketed `[Default]` is applied as written, and is recorded here as a **lead ruling,
ratification pending** — i.e. slot 14 proceeds on the conservative default, not the plan's
`*Recommended*` line, until the owner rules otherwise:
- Q1 (shape/ceiling/concurrency/rule 23): **core only**, concurrency as proposed in §3 (see (3) above).
- Q2 (sign-offs of run-1 data): **staged, unpublished**; P1–P4, P8 left out of the binding drafts.
- Q3 (P1–P11 routing / release): **drafts only, no release** ([C] / [E] stay at their slot-13-close
  versions unless a package's own gate requires otherwise).
- Q4 (level-`N` code in slot 14, WP-12): **deferred to slot 15**; WP-12 does not run this slot unless
  the owner says otherwise.
- Q5 (the Hida-universal document [U]): **pre.2, non-binding** even if WP-8 / WP-9 land.
- Q6 (literature sources / PDFs / arXiv fetch): **unverified** *VERIFY* locators stand (rule A2); no
  PDF placement, no arXiv fetch, until the owner answers.
- Q7 (G1 widen vs guard): **widen** to `size_t` (the plan's own recommendation *is* the default here).
- Q8 (WP-10 defaults): **both the parallel serial phase and streaming stay opt-in** (not default-on).
- Q9 (GPU): **study only if time remains** (WP-14a, stretch); **no** standing cluster gate on
  `ENGINE_DEVICE=gpu --all`.
- Q10 (the October campaign / cadence): **kit only, no submission implied** by this ruling — **except**
  that the owner **did in fact submit** cluster-A section M (cpu3, job **34551683**) directly, which
  this entry records under Q10 as an owner action taken independently of the plan's default; its
  analysis is WP-11's when it returns. §7's monthly-cadence rule is **not yet adopted** as standing.
- Q11 (Proposition M / `p ≠ ell` split / (C2) extensions): **carried** (unchanged from the plan text).
- Q12 (line 2): **carried**.
- Q13 (Loewy code scope, WP-6): **C++ only**, no console verb this slot.
- Q14 (golden): **zero-golden-event slot** confirmed as the working assumption; any level-`N` /
  `LOEWY_RING` golden points stay slot-15 candidates.

Sources: this package's own work; `docs/implementation/slot14/00-slot14-plan.md` §0, §3, §9;
`$HACS_DATA/HANDOVER.md`; the lead's relay of the owner's cluster-A section-M
submission (job 34551683) and the rule-23 amendment.

---

**Version 1.18.1 — 2026-09-27. Slot 13 close, the owner's ratification and the open items' close-out;
non-normative.** (1) The owner **ratified** [OD] S13's in-slot rulings **S13-L1 … L3** on 2026-09-27 (WP-11
carried to a referee and a response package inside the slot, WP-12 kept under the extended ceiling; the [C]
`def:hidalattice` amendment (A3) left by WP-14 to the close; [E] left at v1.14.0-pre.3, the plan scheduling no
release). (2) The slot-13 open items (v1.18 §"Open items", 1–4) are **closed**: **Q7** — the Hida tower catalogue
is **published** at `docs/matrix-engine/results/hida_towers/` (the staged `hida_towers.tsv`, `hida_level_ell.tsv`,
`mk_catalogue.py` copied with sha256 unchanged from
`$HACS_DATA/s13/hida_towers/SHA256SUMS`; `README.md` marked "Published 2026-09-27, owner
sign-off", its own sha256 the only one that moved, `SHA256SUMS` regenerated; `docs/matrix-engine/results/README.md`
§7 gained the row); **[E] v1.14.0 released** (from v1.14.0-pre.3, no further normative edit — the three
pre-releases' text stands, only the `pre.N` suffix dropped; `docs/latex/hecke_extensions.tex` + its tracked PDF
rebuilt, 104 pages, 0 undefined references, 0 undefined citations, 0 multiply-defined labels); the **push** of the
slot-13 close commits (the lead's, immediately after this package); the **cross-config + CheckThread follow-up**
(open item 4) is **done**, `58ea869`
(`docs/implementation/slot13/WP-15_crossconfig.md`, `WP-16_report.md`): golden clean (tier A/B 0/0) and the `gemm
512` / `rref 1677 1419 258` checksums identical across all five configurations (`RelWithDebInfo`, `Bench`, `Check`,
`+HECKE_PURE_INTEGER=ON`, `@ENGINE_BACKEND=legacy`); the one finding this line captured —
`HeckeUEllLowRankValidation` SIGABRT under the legacy backend at the tested tip `26addf0` — was already fixed,
after capture, by **S13 WP-16** (`8030671`/`62ce55e`: the legacy arm now materialises the `U_ell` lever's factored
blocks as `U V`, exact by construction so values are unchanged, and `ValidationRegistry::run` / `run_all` now
catch an escaping exception and report it as `[FAIL]` instead of reaching `std::terminate`); CheckThread on the
three tower / level-`ell` / lever runners (`HeckeUEllLowRankValidation`, `HeckeHidaControlValidation`,
`HeckeHidaLevelEllValidation`, tip `62ce55e`) found **0 ThreadSanitizer warnings**; the legacy-backend run of
`HeckeHidaLevelEllValidation`, let finish under the "no premature kill" rule, took **7682.99 s** (≈ 128 min, ≈ 183×
the default-engine figure), 2906 checks, 0 failing. (3) **Carried to slot 14**: WP-16's harness hardening
(`ValidationRegistry::run` / `run_all` wrapping every validation so an escaping exception is reported as that
validation's own `[FAIL]` rather than aborting the process, per CLAUDE.md's `ENGINE_CHECK` contract) has **no test
of its own** — no validation exercises the catch path itself (e.g. one engineered to throw and checked to come
back `[FAIL]` rather than abort). No code, no golden, no digest, no record moves. Sources: this package's own
work (the catalogue copy, the [E] release build, this entry), `docs/implementation/slot13/WP-15_crossconfig.md`,
`docs/implementation/slot13/WP-16_report.md`, the owner's 2026-09-27 sign-off (relayed by the lead).

---

**Version 1.18 — 2026-09-27. Slot 13 close ([S13] WP-15): full Hida at level one as far as the box allows —
[C] `sec:hidafull` written, refereed and released (v1.13.0, owner-signed under Q14); level `ell` on the fixed model
by Shapiro, the old space and the integral stabilisation tested against an independent group-cocycle route; towers
mod `ell³`, the finite-level lattice datum on two lattices, `T_5` / `T_7`; the `U_ell` memory lever (≈ 5× smaller);
the heavy cell `(700, 691)` computed over `F_691` and `Z/691²` ((Hi11) held); (d1) re-derivable from the record
(`hecke_ext/v5`) and the ext record sets re-emitted and published under it; C-F9 held on 654 / 654 census rows; the
`mixed` finality case argued (Proposition M) and refereed, specified only. Two golden events (R1 add-only, R2 schema).**
The owner answered the slot-13 plan's Q1–Q14 on 2026-09-26 (**every recommendation accepted**, with two amendments:
Q2 — Hida's papers are read-only at `<private-library>`, nothing in `docs/literature/`;
level `Γ_0(N)` by the Shapiro route on the fixed model with scalability tracked) and extended the time ceiling in
the slot (WP-11 and WP-12 kept). Sources: the slot-13 plan `docs/implementation/slot13/00-slot13-plan.md` [S13]
(§9 the owner decisions), the package reports `docs/implementation/slot13/WP-{1,2,4,5,6,7,8,9,10,12,14}_report.md`,
the Fable referees `WP-3_referee.md` ([C] pre.1: ACCEPT WITH REPAIRS, 0 B / 2 M / 10 m) and `WP-11_referee.md`
(Proposition M: ACCEPT WITH REPAIRS, 0 B / 5 M / 8 m), the responses `WP-3_response.md`, `WP-11_response.md`, the
Fable code audit `WP-13_audit.md` (ACCEPT WITH REPAIRS, 0 B / 0 M / 2 m, 12 notes), the golden ledger
`docs/implementation/slot13/golden_ledger.md` and the close report `docs/implementation/slot13/WP-15_report.md`
(with window W1).

**Golden moved twice, each event owner-approved and its own single-parent commit** (the ledger): **R1** `9d58b87`,
the first Hida emission, **add-only** (Q5): 21 entries at nine new `HIDA n=<n> ell=<ell>` points, 17 567 → **17 588**
(tier A 11 666 → **11 687**, tier B **5901**), no digest moved; **R2** `6cc867e`, `hecke_ext/v4 → v5` (Q3, FIN_audit
G2), **changed-line**: the 62 `ext_json_*` lines, the schema string only (A 31, B 31; under the harness's
`u_ell = off` no (d1) passes, so no `boundary_data` reaches golden). Three digests re-pinned at R2:
`EngineDeterminismValidation` `0x22f0b543ba203b79 → 0x003dddd2ef9a8efd` (printed `0x3dddd2ef9a8efd`; 8 arms × 1279
records), `HeckeExtDeterminismValidation` `0xbd8508b97a1df740 → 0xaef77d786b4f29b4`, heavy
`0x774b967f88fd5ad7 → 0x9ed8b83a2fb26622`; `ConsoleDeterminismValidation` **unchanged** `0xf6ed04bbe8e6b60a`.
`golden_landing_check.sh 032c27c` → `LANDING merges=0 orphans=0 verdict=OK` (every package `--ff-only`). No
`.expected` file moved; `tau_table_p2.txt`, `Hecke/HeckeReport.{h,cpp}`, `cli_frozen/` byte-identical. Final:
`GOLDEN_STRICT=1` tier A 11 687 / 0, tier B 5901 / 0; `--all` **140 / 140** (15 `slow` skipped); `--all-full`
**155 / 155** (the roster: **155 = 58 fast / 82 standard / 15 slow**, 96 `Hecke*`; seven names appended in
fragment order, no re-tier).

Changelog:

* **The contract first** (rules 20, 21; WP-2 `83376c5`, WP-3 `7ff1c81` / `8801128`). [C] **v1.13.0-pre.1** → Fable
  referee (0 B / 2 M / 10 m, all twelve applied, the scalability assessment the owner asked for) → **v1.13.0-pre.2**
  → **v1.13.0** (WP-15, **owner-signed under Q14**: the referee ACCEPT with 0 blocking and WP-6's arms held). §27
  `sec:hidafull`: `def:levelellmodel` (the level-`N` model = the induced local system on the fixed `(K, Rel)`,
  monomial relation matrices), `prop:levelcorrespondence` (every `[A g B]` as one block formula reading only the
  level-1 τ-table; level change as fibre maps, degeneracies as Hecke-type correspondences), `prop:levelellU` (no new
  coset or τ-table), `prop:oldspace`, `prop:levelorbit`, `rmk:levelcost` + `rmk:levelscaling` (the two regimes,
  obstacles **(O1)–(O6)**, the Manin–Merel Heilbronn action named by pointer), `lem:levelelltorsion`,
  `prop:stabilisation` (**`e_ell ∘ dg_ell`, not Hida's `e ∘ res`, is the integral stabilisation in this
  convention**; `rmk:stabconvention`), `thm:hidacontrol` / `thm:hidaweight` (literature, **locators verified** against
  the owner's read-only PDFs), `def:hidalattice` with variant (H) on Hida's lattice `L_n = D`-conjugate of `Sym^n`,
  predictions **(Hi7)–(Hi12)**. At v1.13.0 one sentence of `def:hidalattice` is amended (WP-13 audit A3: the module
  route's Nakayama basis on `L_n`) and the code maps read "built". [C] 372 pages, 0 undefined.
* **The `U_ell` memory lever — BUILT, opt-in** (WP-4 `657c0f9`, `3015a53`, `6be7502`; audit repairs WP-14):
  step 0 attributed the footprint object by object (the `ρ_n` of singular-mod-`ell` blocks: 193 of 238 B per entry
  per coset; the floor, 34 B, is the coset tables' full-rank `ρ_n`); `Hecke/HeckeLowRank.h` and
  `HeckeOperatorOptions::ScopedUEllLowRank` (thread-local, no fingerprint — it cannot change a value), the rank claim
  `ENGINE_CHECK`ed per block. ≈ **5× smaller, ≈ 1.8× faster**; the frozen `u_ell` model not re-fitted.
  `HeckeUEllLowRankValidation` (`standard`, 233 after WP-14). Predictions: `(700, 691)` 14.7 GiB (band 16.9);
  `(2420, 2411)` 540 GiB (band 647).
* **Hida code part 2 — BUILT; every (Hi7)–(Hi9) item held** (WP-5 `d7945e6`, `728f246`): towers mod `ell³` ((Hi7) at
  5 in the suite, at 7 measured once), the lattice datum and (Hi8)'s decision procedure on `Sym^n` and on `L_n`
  (`FibreRepresentation::HidaLatticeH`; 130 `Tw_1` + 15 `Tw_2` pairs isomorphic with verified certificates; `D_*` an
  isomorphism on 45 / 45 cells at `m = 1, 2`), (Hi9) `T_5`, `T_7` 157 / 157, the pre-pass beyond `2^64` by
  `engine::ladic`. The module route's Nakayama-basis fallback (value-preserving). `HeckeHidaControlValidation`
  (`standard`, 1134). **Golden R1** (above).
* **`Γ_0(ell)` on the model by Shapiro — BUILT** (WP-6 `3423726`, `60891be`): `Hecke/HeckeLevelEll`
  (`hecke::level`): `eq:levelcorr` as one routine for `U^{(ell)}`, `dg_ell`, `T_p^{(ell)}`, `T_ell`, `dg_1`, `ω`; the
  second model route `eq:Ulevellmodel`; block terms, the det-`ell` blocks factored; general-`N` plug points.
  `HeckeHidaLevelEllValidation` (`standard`, 2906): `eq:Ulevell` **held** against an independent group-cocycle route
  (its first numerical test), `prop:oldspace` (1), (2) as cochain maps, `prop:stabilisation` mod `ell`, `ell²`,
  `ell³`, **(Hi10) on 92 / 92 cells**.
* **FIN_audit G2 closed — `hecke_ext/v5`** (WP-7 `9e04a44`, `d117832`, `6cc867e`, `a38215c`; Q3): [E]
  **v1.14.0-pre.1** spec first; per ideal `boundary_data = {rank_r1, r1, t}` iff (d1) passed; `verify()` code 32
  re-derives (H1), (H2) from the record; G5's synthetic `failed:<class>`. **Golden R2** (above).
* **The ext record sets re-emitted and published** (WP-8 `76c694a`, window W2; Q4; published `9526242`, owner sign-off
  2026-09-26): `ext_first_v5` (505 cells), `ext_census_l7l11_v5` (112), `ext_u691_v5` (45) as sibling sets, the v3 sets
  byte-frozen; every value other than the finality keys and `boundary_data` byte-identical to v3; `EDITION2_NATIVE
  rows=3285 identical=3285` (census edition 2's overlay is now a verified identity; no new edition); arm (H) 376 / 376.
  `ext_sturm_l5` not re-emitted.
* **C-F9, the lattice test — HELD on 654 / 654** (WP-9 `e2d3f53`, `2f3d5a7`; Q8): `HeckeExt/HeckeCensusLattice`,
  `HeckeCensusLatticeValidation` (`standard`, 69); at `ell ≥ 5` the lattice statement *is* `loewy(A) ≤ 2`; the
  Serre-weight mechanism of the finality proposal §7 **not** confirmed (Loewy length of `V` 2 everywhere, 89 rows
  against the distinct-weights bound). Entered [E] as the `\CONJ` Prediction `pr:latticesplit` (**v1.14.0-pre.2**;
  its Dickson-type extrapolation marked unevidenced at **pre.3**, referee M4).
* **The heavy cells** (WP-10 `ae07369`, `70b5eab`, window W3; Q6): `HeckeHidaHeavyCellProbe` (`slow`, interlocked
  `HECKE_HIDA_HEAVY=1`, cells `HECKE_HIDA_HEAVY_CELLS`). The ladder tracked the lever fit; **`(700, 691)` over `F_691`:
  (Hi11) HELD** (`h_ord = 3`, `χ^ord ≡ (X − (1 + p^{11}))^3 mod 691`, 13.65 GiB, 61 s); **over `Z/691²`** (a ladder
  first, band 38.7 GB ≤ 40): `h_ord = 3`, 33.45 GiB, 47 min. **`(2420, 2411)` deferred to the cluster roadmap**
  (band 647 GiB; (Hi12) stays `\CONJ`, its Eisenstein half proved).
* **The `mixed` finality case — ARGUED, REFEREED, SPECIFIED ONLY** (WP-11 `8a2808b` … `b5159e2`; Q10): proposal
  (Proposition M, (d2) "Dickson-mixed") → Fable referee ACCEPT WITH REPAIRS (0 B / 5 M / 8 m) → v2, every finding
  applied; `HeckeMixedFinalityValidation` (`slow`, opt-in scan `HECKE_MIXED_FINALITY_CELLS`) and
  `HeckeBocksteinCuspValidation` (`fast`, 1447 — (H4′) certified cell by cell). No non-injective Dickson-type block
  exists on any computed range (`ell = 7`, `n ≤ 400`; `ell ∈ {11, 13}`, `n ≤ 300`; none at 5). Not landed.
* **Carries** (WP-12 `f7d9e63`): digit-handle time booking fixed and a same-`p` cache; review leftovers m-3, m-4,
  m-10, m-14, the normaliser, slot-11 m-1, m-5, m-6, m-8 closed; A14 at two of three sites. Re-carried below.
* **Audit and repairs** (WP-13 `a0cc761`, WP-14 `f3bd334`): Fable read WP-4 … WP-12 — 0 B / 0 M; A1 (three lever
  guards untested → arm (E)), A2 (the digit-cache key) repaired; A3 (the Nakayama fallback correct; the [C] sentence
  amended at v1.13.0), A4–A14 notes. TSan on the lever: 0 reports.
* **Documents.** [C] v1.12.1 → v1.13.0-pre.1 → pre.2 → **v1.13.0** (owner-signed). [E] v1.13.1 → **v1.14.0-pre.3**
  (pre.1 WP-7, pre.2 / pre.3 WP-9 / WP-11) — **not released; owner item**. [P] v3.9.3, [EX] 1.0.0, `ENGINE_API.md`
  unchanged. [X] v1.17.1 (WP-1) → **v1.18** (this).
* **The standing gates** ([OD] S7-G, `--gate`; W1 at this close, REF `032c27c`): hecke 256 new_min 0.4077 s (REF 0.4051), paired median ratio 0.997, headroom 13.3 %; decomp 128 new_min 0.0923 s (REF 0.0926), ratio 1.002, headroom 15.3 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `032c27c`: (10, 691) 1.0007 MET, (160, 691) 0.9934 MET; T-C4 2.241 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; 2026-09-27 W1, quiet box).
* **Not changed**: everything else; v1.17's and v1.17.1's text stands except where this version supersedes it
  (v1.17.1's "one open finding" G2 is **closed** by WP-7).

**Open items at the slot-13 close — deferred to the owner** (recorded, not ruled):

1. **The Hida tower catalogue** (Q7: publish at the close if every `\PROVED` item held, owner-signed). Every
   `\PROVED` item held (and every tested `\CONJ` item). **Staged, not published**:
   `$HACS_DATA/s13/hida_towers/` (`hida_tower/v1` TSV, README, `SHA256SUMS`) — the owner's
   sign-off moves it to `docs/matrix-engine/results/hida_towers/`.
2. **[E] v1.14.0 release** (from v1.14.0-pre.3: `cert:boundary` / `sec:schema` for `hecke_ext/v5`,
   `pr:latticesplit`). The slot-13 plan does not schedule it; the owner's.
3. **Ratification** of the slot's in-slot rulings ([OD] S13, below) and the time-ceiling extension as used.
4. **The cross-config line and CheckThread** on the slot's new names (the plan: the lead's follow-up, as slot 12's
   WP-15).
5. **Proposition M's landing** (Q10: specified-only until a campaign produces a non-final `mixed` row; bundle it with
   the next record event).
6. **[EX] next edition** (Q9: slot 14, after the tower catalogue is signed).
7. Unchanged: the census `Z/ell²` depth window above `n = 64` and `ext_sturm_l5` in an edition (Q11); line 2 (Q12,
   OD-3); rule 23's hosts.

### `[OD]` — slot 13's rulings, as a register (owner answers of 2026-09-26; in-slot lead rulings marked)

Source: [S13] §8 (Q1–Q14) and §9 (the owner's answers and amendments); in-slot rulings from the lead's briefs.

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S13-Q1** | Shape (full Hida headline; record line second; research third) accepted; ceiling ≈ 10 h, **extended in the slot** (WP-11, WP-12 kept); S12-L1 … L15 **ratified** as recorded in v1.17 | the slot's 15 packages |
| **S13-Q2** | Hida's sources: **amended** — read-only at `<private-library>`, cited by path, never written / moved / copied; nothing in `docs/literature/`; `\LIT` locators verified in WP-2 / WP-3 | [C] `thm:hidacontrol`, `thm:hidaweight` verified (Ann. ENS 19, Invent. 85); *Elementary theory* Ch. 7, Shimura, Atkin–Lehner not verified |
| **S13-Q3** | FIN_audit G2: **do it** before the re-emission | WP-7, `hecke_ext/v5`, golden R2 |
| **S13-Q4** | Re-emit `ext_first`, `ext_u691`, `ext_census_l7l11` under the final schema as sibling sets; edition 2 unchanged if the identity holds; `ext_sturm_l5` not re-emitted | WP-8 (W2); **published `9526242`** (owner sign-off 2026-09-26); identity held |
| **S13-Q5** | The first Hida golden emission, add-only | WP-5, golden R1 (+21) |
| **S13-Q6** | Heavy cells only if the band's top ≤ 50 GB and the ladder tracked the fit | `(700, 691)` ran (bands 16.9 GiB, 38.7 GB); `(2420, 2411)` **deferred to the cluster roadmap** |
| **S13-Q7** | The tower catalogue published at the close if every `\PROVED` item held, owner-signed | **staged** at the close (open item 1), sign-off pending |
| **S13-Q8** | C-F9 into [E] as a `\CONJ` remark if it held | [E] `pr:latticesplit` (v1.14.0-pre.2 / pre.3) |
| **S13-Q9** | [EX] next edition in slot 14 | carried |
| **S13-Q10** | The `mixed` case specified-only | WP-11 proposal v2; not landed |
| **S13-Q11**, **Q12** | Depth window, `ext_sturm_l5`, line 2: not in slot 13 | carried |
| **S13-Q13** | WP-3's referee may run beside WP-4 | used |
| **S13-Q14** | [C] v1.13.0 released at the close if the referee is ACCEPT with 0 blocking and WP-6's arms held | both held → **[C] v1.13.0** (WP-15), with WP-13's `def:hidalattice` amendment |
| **S13-A1** *(amendment)* | Level `Γ_0(N)` by **Shapiro on the fixed model** (`Ind_{Γ_0(N)}^{SL_2(Z)} Sym^{k−2}`), exploiting the monomial / orbit structure; level change as fibre maps; a cost model; the referee assesses scalability; `N = ell` built, general `N` not precluded | [C] `rmk:levelcost`, `rmk:levelscaling` (O1)–(O6); `Hecke/HeckeLevelEll`'s plug points |
| **S13-L1** *(in slot, lead)* | WP-11 carried to a referee (Fable) and a response package inside the slot; WP-12 kept (the ceiling extension) | WP-11 v2, `HeckeBocksteinCuspValidation` |
| **S13-L2** *(in slot, lead)* | The [C] `def:hidalattice` amendment (A3) left by WP-14 to the close | [C] v1.13.0 |
| **S13-L3** *(in slot, lead)* | [E] left at v1.14.0-pre.3 (the plan schedules no release) | open item 2 |

---

**Version 1.17.1 — 2026-09-26. Slot 13, WP-1 (day zero); non-normative.** (1) The console `uint32_t` gap
([P] Q9) is **struck from the owner items**: decided (a) by the owner 2026-09-26 and built post-close by S12
WP-17 (`8fcad8d`, `bind::GateTypeOnWide`); the rows of v1.17 that still read "untouched (L5)" / "not touched (L5,
owner)" are superseded by this line. (2) **FIN_audit G2** (`docs/implementation/slot12/FIN_audit.md`: (d1) is not
re-derivable from the record; the deviation from the finality proposal's F8 item 3 unlisted) is recorded as **the
one open finding**: it is a listed deviation until the owner-gated slot-13 WP-7 (owner question Q3, answered yes on
2026-09-26 by acceptance of the recommendation) lands `hecke_ext/v5`; [E] v1.13.1 documents the in-process form.
(3) The slot-13 owner answers are in `docs/implementation/slot13/00-slot13-plan.md` §9. No code, no golden, no
digest, no record moves.

**Version 1.17 — 2026-09-26. Slot 12, S12-FIN (owner-approved 2026-09-26): the finality certificates land.**
(d0) "dickson" (Proposition D, [C] `prop:heckeH0`(1)) and (d1) "boundary" (Proposition F′, [C]
`prop:bdrytranscription` + `lem:bdrytorus`, unconditional since [C] v1.12.0) are specified in [E] v1.13.0
(`cert:dickson`, `cert:boundary`, `sec:schema` item (i); v1.13.1 after the Fable audit: (d1)'s stream cost
cap, `not_run:budget`, tied to the `u_ell` budget — R3's budget rule, no new key), built (`HeckeExt/HeckeFinalityRoutes`, run by
`HeckeExtDriver` in Stage 4 only where (a)–(c) fail), and the record is **`hecke_ext/v4`**
(`certificate_routes.d0` / `.d1`, `boundary_reps`, certificate names `dickson` / `boundary`, `verify()` codes
30–31). §1.3.1 R3.2's `true` and its name list are extended below. **One golden event** (R1, the slot-12
ledger): the 62 `ext_json_*` lines, text only (the harness runs `u_ell = off`, so no route passes there),
`docs/matrix-engine/rebaseline-2026-09-26-hecke-ext-v4-finality.md`; EngineDet `0x22f0b543ba203b79`, ExtDet
`0xbd8508b97a1df740`, heavy `0x774b967f88fd5ad7` re-pinned, ConsoleDet unchanged. The deferred item "the 184
heuristic `ell = 5` ideals" / "Finality landing" is **DONE** (tables below). Report
`docs/implementation/slot12/FIN_report.md`.

**Version 1.16 — 2026-09-26. Slot 12 close ([S12] WP-9): the foundation of Hida theory at level one —
[C] `sec:hida` written and refereed first (v1.12.0-pre.2: the torsion pre-pass `prop:torsionprepass`, the
certified working precision `cor:ordprecision`, the projector exponent `lem:ordexponent`, `def:hidatower`,
predictions (Hi1)–(Hi6)); the pre-pass and `U^{N_ord}` in code, checked against the slot-11 digit route; the
first weight towers at `ell ∈ {5, 7, 11, 13}` (mod `ell` and mod `ell²`) and the non-ordinary cell
`(10, 2411)`; census edition 2 built and staged (unpublished); the forms-side Hecke algebra in tree and over
all 655 non-reduced census rows; a boundary finality argument for the 184 (and all 376) heuristic ideals,
refereed, with its validation — the certificate itself not landed; the console θ verbs. No golden event.**
**The owner was unavailable for the whole slot**: every ruling below marked `L<n>` is the lead's, made on the
owner's behalf where [X] or a standing rule left a default, **ratification pending** ([OD] S12). Sources: the
slot-12 plan `docs/implementation/slot12/00-slot12-plan.md` [S12] (draft; its §5 ruling register, §6 deferred
list), the package reports `docs/implementation/slot12/WP-{1,2,4,5,6,7,8,11,12,14}_report.md`, the Fable
referees `WP-3_referee.md` ([C] pre.1: 0 B / 0 M / 10 m) and `WP-13_referee.md` (the finality proposal:
ACCEPT WITH REPAIRS, F1 blocking for (d1) only), the Fable code audit `WP-10_audit.md` (0 B / 0 M / A1–A15),
the golden ledger `docs/implementation/slot12/golden_ledger.md` and the close report
`docs/implementation/slot12/WP-9_report.md` (with window W1, run at the close by WP-9).

**The slot moved golden nowhere** (L2; the ledger): R0 = R1 = **17 567** entries (tier A **11 666**, tier B
**5901**); `git log 9d08a30..HEAD -- '*GoldenReference.inc'` is empty, every package merged `--ff-only` (no
merge commit in the slot), and `golden_landing_check.sh 9d08a30` prints `LANDING merges=0 orphans=0 verdict=OK`. **All four digests are
unchanged**: `EngineDeterminismValidation` `0xe501ca19ee7815e1` (8 arms × 1279 records),
`HeckeExtDeterminismValidation` `0x03b4f07c14555fec` (printed `0x3b4f07c14555fec`), heavy `0x498147a50c6c1e30`,
`ConsoleDeterminismValidation` `0xf6ed04bbe8e6b60a` (24 / 24 arms). `tau_table_p2.txt`,
`Hecke/HeckeReport.{h,cpp}`, the 35 slot-11 transcripts, `cli_frozen/` are byte-identical to `9d08a30`; one
transcript added (`027_dickson_theta`, first freeze); `docs/matrix-engine/results/` unchanged (nothing
published, L4). Final `GOLDEN_STRICT=1`: tier A 11 666 / 0, tier B 5901 / 0; `--all` **135 / 135** (13 `slow`
skipped); `--all-full` **148 / 148** (the roster: **148 = 57 fast / 78 standard / 13 slow**, 89 `Hecke*`;
seven names appended in fragment order, no re-tier).

Changelog:

* **The contract first** (rule 21; WP-2 `30e5b69`, WP-3 `dce4ab0` / `b73a292`). [C] **v1.12.0-pre.1** → Fable
  referee (0 B / 0 M / 10 m, all applied) → **v1.12.0-pre.2**: §26 `sec:hida` — `prop:torsionprepass`
  (`H^0(Γ; V/ell^e) ≅ H^1(Γ; V)[ell^e]`, the `ell`-adic elementary divisors of `J_n = [ρ_n(S) − 1; ρ_n(T) − 1]`
  are the torsion exponents, `e_max` by a stopping rule, valid at every prime; the **precision use** refused at
  `ell ∈ {2, 3}`, clause (6)); `cor:ordprecision` (the ordinary part needs **no** extra precision; the full free
  quotient needs `K = e' + e_max`, computable before the run); `lem:ordexponent` (`N_ord(𝔤, K) =
  ell^{K−1+⌈log_ell 𝔤⌉} ∏_{f ≤ 𝔤}(ell^f − 1)`, `U^{N_ord} = e_ord(U)`); `rmk:ordexponentuse`; `def:hidatower`;
  `rmk:hidacheckable` (Hi1)–(Hi6), committed before the code (rule 20). `open:ordprecision` carries a pre-release
  note "answered at `ell ≥ 5`, `n ≥ 1`"; its status macro stays `\OPENSTAT` (L3). Census 502 labels.
* **The certified ordinary projector — BUILT** (WP-4 `b5551c7`, `78099d0`): `Hecke/HeckeOrdinaryPart`
  (`TorsionExponentPrepass`, `CertifiedWorkingPrecision`, `OrdinaryExponent` kept as factors, `U^N` never
  materialised, `OrdinaryProjector`, `ApplyTpOnH0`); `LadicCell`'s **opt-in** `precision_source = prepass`
  (default route byte-identical; ` prepass=1` appended to the record text only on that route, reached from no
  emitter). `HeckeOrdinaryPrecisionValidation` (`standard`, 916 after WP-11): (Hi1) the pre-pass `e_max` equals
  the certified word-size K-mode's on 20 cells incl. every `ell²`/`ell³`-torsion locus — **no disagreement**;
  (Hi2) `U^{N_ord}` equals WP-18c's certified idempotent at `(10, 691)`, `(30, 5)`, `(20, 5)`; negative controls
  showing no term of `N_ord` can be dropped. Deferred: the pre-pass beyond `2^64` (refused by name; every grid
  cell has `e_max ≤ 3`).
* **The first Hida towers — BUILT, every prediction held** (WP-5 `fe82f41`, `1831bed`): `HeckeExt/HeckeHidaTower`
  (per cell `H_K` by the shipped module route at `K = 2 + e_max`, the ordinary part read on `H_{e'}` and on the free
  block, `χ^ord(T_2)`, `χ^ord(T_3)` by a Nakayama basis and Berkowitz). `HeckeHidaTowerValidation` (`standard`,
  5222 after WP-11; even `n ≤ 80` + named `Tw_2` partners) and `HeckeHidaTowerSlowValidation` (`slow`, 11 722;
  `n ≤ 120` at 5, 7, 11, `n ≤ 200` at 13; ≈ 160 s, ≈ 4 GB). (Hi2)–(Hi6): no PROVED and no CONJ item failed —
  (Hi3) the ordinary ranks (1 at 5, 7; 3 on the rank-3 classes at 11, 13), (Hi4) `χ^ord` constant on `Tw_1` mod
  `ell` and on `Tw_2` mod `ell²` (e.g. `(10, 11) ↔ (120, 11)`, `(10, 13) ↔ (166, 13)`), (Hi5) the Eisenstein root,
  (Hi6) `(10, 2411)` over `Z/2411^{1,2,3}`: ordinary rank 1, Δ's block non-ordinary, `τ(2411) ≡ 0, 150·2411,
  9 539 365 011` confirmed by the model. `U_2411` at `2411³` was served by the `uint64_t` route (no fallback).
* **Census edition 2 — BUILT, STAGED, NOT PUBLISHED** (WP-6 `2781b39`, `2df8e08`; L4): the cell-list option
  (`HeckeExt/HeckeCensusCellList`, `HECKE_CENSUS_SPLIT_CELLS`, `HECKE_THETA_IMAGE_CELLS`,
  `HeckeCensusCellListValidation` `fast`); the split (684 lines, 17 m 54 s, 4.6 GB) and θ-image (684 lines) over
  the 112 W2 cells; `congruence_census.py --edition 2` (edition 1 reproduced byte for byte, 7 / 7 files) →
  3285 rows staged at `$HACS_DATA/s12/census_edition2/` (sha256s in
  `docs/implementation/slot12/WP-6_edition2_staged.sha256`, draft README beside it). Findings: all 794 `mixed`
  rows Eisenstein-labelled, P4 holds, identity 6 0 mismatches, no Loewy length ≥ 3. The `Z/ell²` depth window
  above `n = 64` not run (L6).
* **The forms-side Hecke algebra — BUILT; the [EX] `RCOMP` datum reproduced** (WP-7 `260735f`; WP-12 `bf64498`):
  `HeckeExt/HeckeFormsHeckeAlgebra` (pipeline-free: Miller bases of `S_k` and — WP-12 — `M_k` mod `ell`, `T_p` on
  `q`-expansions to the Sturm range, localisation at `A`'s full system, invariants by `HeckeAlgebraInvariants`).
  `(82, 7)`: `T_m/7` embdim 3; `(142, 7)`: Hilbert `(1, 3, 2)`, Loewy length 3; the cohomological `A` a quotient
  (with `U_7` ↔ forms `T_7`). `HeckeFormsHeckeAlgebraValidation` (`standard`, 163). **The forms census** (WP-12,
  655 non-reduced rows of the staged edition 2, via `HECKE_FORMS_CENSUS_CELLS`): on `M_k`, `A = T_m/ell` on 309,
  a proper quotient on 345, one out-of-scope row (`(120, 5)`'s `H^0` ideal); `A`'s Hilbert function always of
  length 2 while `T_m/ell` reaches Loewy length 6; TSV staged in `docs/implementation/slot12/WP-12_forms_census/`.
* **Finality of the heuristic ideals — ARGUED, REFEREED, EVIDENCED; NOT LANDED** (WP-12, WP-13 `92da7d5`, WP-14
  `ff66bf5` / `262f9b0`): the forms side certifies 0 of 184 by itself (the obstruction lives in the torsion
  image); the boundary does. Proposal v2 (`docs/implementation/slot12/WP-12_finality_proposal.md`): certificate
  **(d0) "dickson"** on the 36 `X_1` ideals via [C] `prop:heckeH0` (unconditional) and **(d1) "boundary"** on the
  148 `X_4` ideals via Lemma B′ + Proposition F′, **conditional on Proposition T** (the Shapiro transcription in
  degree 1; a proof sketch, unrefereed — the referee's one blocking finding F1). `HeckeBoundaryFinalityValidation`
  (`standard`, 13 332, ≈ 9 s): Lemma B′ on 1628 shipped boundary operators, the Eichler–Shimura dimension
  identity, the `mixed` negative control; under `HECKE_BOUNDARY_FINALITY_ALL=1` on the staged edition 2:
  **376 / 376 heuristic rows certified** (184 at 5, 150 at 7, 37 at 11, 5 at 13; 999 s). The code change
  (route (d) in the generation certificates, `is_final`, schema) would move golden and the ExtDet heavy digest
  (`(128, 5)` carries two of the 184) — owner-gated.
* **Console θ verbs — BUILT** (WP-8 `2e02560`, `ef1fbf0`; [P] **v3.9.2**): `dickson_les(n, ell)` → `DicksonLES`,
  `theta(H, H_up)`, in `HeckeExt/RegisterHeckeExtensionVerbs.cpp` (the plan's `Console/Bindings/DicksonTheta.cpp`
  would break `check_heckeext_includes.sh`; [P] was followed); `ConsoleErrorValidation` arm (T) → 347; script
  `027_dickson_theta` (first freeze; 36 scripts); ConsoleDet `0xf6ed04bbe8e6b60a` unchanged. Q9 not touched (L5).
* **Carries** (WP-1 `4cb6a44`, `4e88d32`): `Registry/Slot12/` + `cmake/slot12/`; F-1 — `QuotientL`'s relation list
  and fibre builder refuse a ring through named guards, `HeckeThetaCensusRingRefusalValidation` (`fast`, 15);
  **open item 8 closed**: `label_census.sh` exits 1 on a failing census (bare; the slot-11 observation was a
  pipe's status); two content-keyed allow-list entries (8 allowed); `slot12_close_window.sh`.
* **Audit and repairs** (lead-added WP-10 `937a297`, WP-11 `a3d3d5e` … `4082f56`): Fable read WP-4 … WP-8 line by
  line — no blocking, no major; A1–A15 about the strength of the claims (A1 (Hi2) tautological at `e_max = 0` →
  gated on the 58 / 110 `e_max > 0` cells; A2 (Hi5)'s pair clause was index arithmetic → a model check; A5, A6
  forms controls given teeth; A7 a determinism arm; A13 script 027's self-comparison replaced, no re-freeze).
  A14 left (pre-existing). No `.expected` file changed.
* **Documents.** [C] v1.11.1 → v1.12.0-pre.2 → **v1.12.0** (owner-signed release, 2026-09-26; post-close, not
  a WP of this changelog block — see the open items below). [P] v3.9.1 → **v3.9.2**. [E] v1.12.1,
  [EX] 1.0.0, `ENGINE_API.md` unchanged.
* **The standing gates** ([OD] S7-G, `--gate`; W1 at this close, REF `9d08a30`): hecke 256 new_min 0.4095 s (REF 0.4037), paired median ratio 1.004, headroom 12.9 %; decomp 128 new_min 0.0926 s (REF 0.0912), ratio 1.013, headroom 15.0 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `9d08a30`: (10, 691) 1.0109 MET, (160, 691) 1.0170 MET; T-C4 1.480 s ≤ 5 s MET (placement `SAME`, a = b = 0; all 13 + 13 + 5 + 5 rounds clean; 2026-09-26 W1, quiet box).
* **Not changed**: everything else; the v1.15 changelog below stands, except where this version supersedes it
  (v1.15's open items 3 — Hida: foundation in slot 12, the rest slot 13 (L1) — 7 — the 184: argued, landing
  owner-gated — and 8 — closed by WP-1 — are resolved or restated below).

**Open items at the slot-12 close — deferred to the owner** (recorded, not ruled; [S12] §6):

1. ~~**Census edition 2 publication** (WP-6, staged): copy to `results/congruence_census/edition2/`, its index row
   and sign-off~~ **DONE** (owner sign-off 2026-09-26; S12-census2, `docs/implementation/slot12/census2_report.md`):
   published at `results/congruence_census/edition2/`, 3285 rows, regenerated so its finality columns are
   `hecke_ext/v4`'s (every row final: 36 `dickson`, 340 `boundary`). **Still open**: whether `ext_sturm_l5` ever
   enters an edition; the `Z/ell²` depth window above `n = 64`.
2. ~~**[C] v1.12.0 release** (`sec:hida`) and **`open:ordprecision`'s status change** to answered (at
   `ell ≥ 5`, `n ≥ 1`)~~ **DONE** (owner sign-off 2026-09-26): [C] is **v1.12.0**; `open:ordprecision` is
   retitled "ANSWERED 2026-09-26", tag `OPENSTAT` → `PROVED`, discharged by `cor:ordprecision`. ~~**Still
   open**: [C]'s `sec:hida` code map still reads "not built"~~ **DONE** by [C] **v1.12.1** (non-normative,
   S12-census2): the code map names `Hecke/HeckeOrdinaryPart` and `HeckeExt/HeckeHidaTower`, and
   `sec:codemap` names `HeckeExt/HeckeFinalityRoutes`.
3. **The finality certificates**: (d0) "dickson" (unconditional; ready to specify in [E] and land), (d1)
   "boundary" (needs **Proposition T** refereed and in [C] first — the WP-13 F1 condition), and the golden /
   ExtDet-heavy movement their landing causes (an owner-signed event). **DONE (v1.17, S12-FIN, owner-approved
   2026-09-26).**
4. **The first Hida golden emission** (add-only): the candidate list in the ledger, unexecuted (L2).
5. **[EX] next edition**: the `RCOMP` rows are now pipeline data (WP-7), and the forms census (WP-12).
6. ~~**[P] Q9**, the console `uint32_t` gap (`Z/5^14 … Z/5^27`, `Z/691^4 … Z/691^6`) — untouched (L5).~~ **DONE** (owner (a) 2026-09-26; S12 WP-17, `8fcad8d`; v1.17.1).
7. **CLAUDE.md-worthy env hooks** (recorded at this close; all read-only, none an emitter):
   `HECKE_CENSUS_SPLIT_CELLS`, `HECKE_THETA_IMAGE_CELLS`, `HECKE_FORMS_CENSUS_ALL` / `_CELLS` / `_TSV`,
   `HECKE_FORMS_FINALITY_ALL` / `_ELLS`, `HECKE_BOUNDARY_FINALITY_ALL`.
8. **Ratification of L1–L11** and the lead-added packages (WP-10 … WP-14) — still owner-pending. **The
   cross-config line and the CheckThread run are DONE** (WP-15, this close's follow-up, mirroring slot-11
   WP-17): `cross_config.sh RelWithDebInfo Bench Check RelWithDebInfo+HECKE_PURE_INTEGER=ON
   RelWithDebInfo@ENGINE_BACKEND=legacy --validations HeckeThetaCensusRingRefusalValidation,
   HeckeOrdinaryPrecisionValidation,HeckeHidaTowerValidation,HeckeCensusCellListValidation,
   HeckeFormsHeckeAlgebraValidation,HeckeBoundaryFinalityValidation` — five rows, golden 0/0 on every row,
   `gemm 512` / `rref 1677 1419 258` checksums identical across all five, all six named validations exit 0
   on every row; a sixth, supplementary row (`RelWithDebInfo` alone, all **seven** new names including the
   `slow`-tier `HeckeHidaTowerSlowValidation`) is likewise golden 0/0, checksums identical, all seven exit 0.
   **CheckThread**: one `CheckThread` build, `ENGINE_CUDA_DISABLE=1 setarch x86_64 -R ./cohomology_app
   HeckeHidaTowerValidation HeckeOrdinaryPrecisionValidation` — both `[PASS]` (5222 + 916 checks, 0 failing),
   **0 ThreadSanitizer reports** on the concurrent Hida tower runner (165 cells computed concurrently).
   Full matrix and gate lines: `docs/implementation/slot12/WP-15_crossconfig.md`.
9. Unchanged from v1.15: `obl:coneexact`(vii) sentence 3 over the ring; ExtDet's wall / CheckThread with a live
   device; rule 23's hosts (no go-ahead).

### `[OD]` — slot 12's rulings, as a register (**lead rulings on the owner's behalf; ratification pending**)

Source: [S12] §5 (L1–L11), and the lead's in-slot decisions (L12–L15).

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S12-L1** | Hida **foundation** in slot 12, full Hida in slot 13 (uses [OD] S11-12's leave) | WP-2 … WP-5 |
| **S12-L2** | **No golden event**, not even add-only | the ledger: R0 = R1 |
| **S12-L3** | [C] to **v1.12.0-pre.2** only; `open:ordprecision` keeps `\OPENSTAT` with a pre-release note | WP-2 / WP-3 |
| **S12-L4** | **No publication** under `results/`; edition 2, tower lines, forms census staged | WP-6, WP-12 |
| **S12-L5** | Console `uint32_t` gap (Q9) not touched (superseded: WP-17 built it post-close; v1.17.1) | WP-8 |
| **S12-L6** | **No campaign window** (no W2, no `Z/ell²` survey above `n = 64`, no W3); W1 only if time allows | W1 run at the close (WP-9) |
| **S12-L7** | The 184, C-1 / E-1, (C2) extensions, digit-handle costs, line 2, review leftovers → slot 13 | the 184 were nevertheless taken up by lead-added WP-12 … WP-14 (L13) as argument + evidence, not landed |
| **S12-L8** | `Registry/Slot12/` + `cmake/slot12/` kept | kept at the close |
| **S12-L9** | Fable once (WP-3) | **superseded by L12 / L14**: Fable also for the code audit (WP-10) and the finality referee (WP-13) — audits / referees, the owner's economy rule |
| **S12-L10** | Strictly serial, `--ff-only` merges | held (no merge commit in `9d08a30..HEAD`) |
| **S12-L11** | Tower primes `{5, 7, 11, 13}` + 2411 | WP-5 |
| **S12-L12** *(in slot)* | A Fable code audit of WP-4 … WP-8 (WP-10) and its repairs (WP-11) before the close | 0 B / 0 M; A1–A13 repaired, A14 left |
| **S12-L13** *(in slot)* | WP-12: the forms side over every non-reduced census row and a finality argument for the 184 | `WP-12_report.md`, proposal |
| **S12-L14** *(in slot)* | WP-13 Fable referee of the proposal; WP-14 the response (v2) and `HeckeBoundaryFinalityValidation` (a new name, the fragment pair `WP14` created by the package with two one-line shared edits) | proposal v2; 376 / 376 |
| **S12-L15** *(in slot)* | WP-8 followed [P] (`RegisterHeckeExtensionVerbs.cpp`) over the plan's file line | the include guard kept |

---


**Version 1.15 — 2026-09-25. Slot 11 close ([S11] WP-17): multiplication by the Dickson invariant is
θ, computed and certified cohomologically (Part VII of [C]: `Q_n`, the six-term long exact sequence,
`ker θ = im δ`, the Dickson ring on `H^0`, θ's twisted Hecke equivariance and `U_ell θ = 0`); the
congruence census classifies every published maximal ideal (edition 1, owner-signed) and the W2 ext
campaign extends it to `n = 300` at `ell = 7, 11` (owner-signed); arbitrary `k` is built by the (C2)
`ell`-adic digit induction over the three native word widths, with a per-cell certified precision
bound and the ordinary idempotent on the digit route; M-3 closes X7 on the free model; the examples
document [EX] is published at 1.0.0 (owner-signed). No golden event.** Sources: the slot-11 plan
`hecke_extensions_slot11_plan.md` [S11] (revision 2, its audit `hecke_extensions_slot11_plan_audit.md`
and the owner's rulings of its §10, 2026-09-25), the package reports
`docs/implementation/slot11/WP-{1,2,4,5,6,7,8,11,12,15,18a,18b,18c,19}_report.md`, the Fable referees
`WP-3_referee.md` ([C] pre.1), `WP-20_referee.md` ([EX]) and `WP-15_referee.md` (the documents), the
Fable review `WP-14_review.md` / `WP-14_review_pass2.md`, the golden ledger
`docs/implementation/slot11/golden_ledger.md` and the close report
`docs/implementation/slot11/WP-17_report.md`. **The closing window W1 is the lead's**: every figure only
W1 gives is marked `[WINDOW W1: …]` in the report (its §10 has the command).

**The slot moved golden nowhere** ([S11] §4.4, decision 6 (A); the ledger): R0 = R1 = **17 567**
entries (tier A **11 666**, tier B **5901**); `git log a3ca7b4..HEAD -- '*GoldenReference.inc'` is
empty and `golden_landing_check.sh` prints `LANDING merges=0 orphans=0 verdict=OK` on both `a3ca7b4`
and `54bc2b5`. **All four digests are unchanged**: `EngineDeterminismValidation` `0xe501ca19ee7815e1`
(8 arms × 1279 records), `HeckeExtDeterminismValidation` `0x03b4f07c14555fec` (printed
`0x3b4f07c14555fec`), heavy `0x498147a50c6c1e30`, `ConsoleDeterminismValidation` `0xf6ed04bbe8e6b60a`
(24 / 24 arms). `tau_table_p2.txt`, `Hecke/HeckeReport.{h,cpp}`, the 35 console transcripts,
`cli_frozen/`, `prelude.oc`, `cli_params.oc` are byte-identical to `a3ca7b4`; `docs/matrix-engine/results/`
gained only the slot's four owner-signed sets and §7's rows. Final `GOLDEN_STRICT=1`: tier A 11 666 / 0,
tier B 5901 / 0; `--all` **129 / 129** (12 `slow` skipped); `--all-full` **141 / 141** (the roster:
**141 = 55 fast / 74 standard / 12 slow**, 82 `Hecke*`; eleven names appended in fragment order, no
re-tier).

Changelog:

* **The contract first** ([OD] S11-1, rule 21). [C] **v1.11.0-pre.1** (WP-2, merged `3a0bbbf`) wrote
  Part VII before any θ claim was committed in code: `sec:dicksontheta` (`def:dicksoninv`,
  `lem:dicksontwist` — the det twist on all of `M_2`, singular included; `prop:dicksonH0`;
  **`prop:heckeH0`** — `T_p` on `L^a D^b` is `(1+p)p^a`, `U_ell` has rank `≤ 1` and square zero on
  `H^0`, and is **not** zero at `n = ell³ − ell` (`U_5 D⁶ = −L²⁰` at `(120, 5)`), refuting the plan's
  "`U_ell = 0` on all of `H^0`"; `lem:heckefibre`; `def:Qn` with a fixed basis; `lem:Qnfunctions`;
  `def:theta`; `prop:thetatwist` — `T_p θ = p θ T_p`, `U_ell θ = 0` already on cochains;
  `thm:thetales` — the LES, its termination at `H^1(Q_n)`, `rank δ = [(ell−1) | n+2] −
  [ell(ell−1) | n+ell+1]`, the closed forms and the multiplicity inequality; `rmk:thetacheckable`
  (C1)–(C9)), `sec:ordinary` (`def:ordinary`, `prop:ordinary` — Fitting, canonical, exact, compatible
  with reduction; `cor:thetanonordinary`; `open:ordprecision`), and `prop:relationsmodel` (the
  `thm:relations` recursion on the free model for every ring). WP-3's Fable referee (0 B / 1 M / 9 m;
  `prop:heckeH0` confirmed independently) → **pre.2** (`fb9dcbf`). WP-15 → **v1.11.0** (`a8e0afb`); its
  referee (0 B / 2 M / 6 m) → **v1.11.1** at this close (the provenance of (C1)–(C9)'s predictions
  restated; **`rmk:ordtorsionfree`** — at `ell ≥ 5`, `n ≥ 1` the ordinary part of `H^1 ⊗ Z_ell` is
  torsion-free at level 1 and equals the free quotient's, which answers half of `open:ordprecision`).
* **The Dickson/θ line — ACCEPTED** ([S11] exit item 4; WP-5 merged `a6c9273`, WP-6 merged `dc8ddd5`).
  `FibreRepresentation::QuotientL` (`ρ_{Q_n}` for every 2×2 matrix, singular included; its relation
  list; `HeckeOperatorOnK` on it with its own program-cache tag); `hecke_ext::DicksonThetaCell` (the
  six terms and five maps in the stored bases, `δ` by the snake construction, exactness at all six
  spots as subspaces, `H^2 = 0` on the three terms, the Dickson span); `HeckeDicksonThetaHecke` (the
  Hecke operators on the three terms; `P0`: the τ datum is not keyed on `n`). On 108 standard and 404
  slow cells (`ell ∈ {5, 7, 11, 13}`, even `n ≤ 200`) every closed form held; `T_p θ = p θ T_p`
  entrywise with the untwisted identity failing wherever it can; `U_ell θ = 0`; `ker θ = im δ` is the
  Eisenstein line; `U_ell` on `H^0` exactly as `prop:heckeH0` (the `(120, 5)` exception entrywise);
  (C3)–(C9) confirmed, each matched against `Σ(ell)` and its twist; (C7)'s open alternative decided by
  the model (`p²τ(p)` first at `n = 14` at `ell = 13`); (C9) cell by cell; the θ-image column over the
  384 census cells (1934 ideals, every block matched one-to-one). Validations
  `HeckeDicksonThetaValidation` (979), `HeckeDicksonThetaCoverageSlowValidation` (`slow`, 3590),
  `HeckeDicksonThetaHeckeValidation` (5482; 34 337 under `HECKE_THETA_IMAGE_ALL=1`),
  `HeckeDicksonThetaHeckeCoverageSlowValidation` (`slow`, 3836). Rule 20 held with one recorded
  deviation (WP-5: two closed forms checked on their first run; [C] v1.11.1 M-1).
* **The congruence census — ACCEPTED** (exit item 5; WP-7 merged `b294827`, WP-8 merged `92e8fcb`).
  `HeckeExt/HeckeCensusSplit` computes per `H^1` ideal the boundary split (`rank r^1` on the block:
  `eisenstein` / `cuspidal` / `mixed`), the `±` content and the Glover reconciliation (identity 6);
  `HeckeCensusSplitValidation` (117; 5643 under `HECKE_CENSUS_SPLIT_ALL=1`); the tool
  `docs/matrix-engine/tools/congruence_census.py` reproduces [CEN]'s category table cell-exactly
  (55 / 55). **Edition 1** (`results/congruence_census/edition1/`, 2569 rows, **owner-signed `bb7c860`**):
  every non-reduced Eisenstein-labelled ideal at `ell ∈ {7, 11, 13}` is `mixed`; 592 `mixed` rows at
  the regular primes; no Loewy length ≥ 3; the largest local algebra length 4 at `ell = 7`;
  `H^1_!(F_5) = 0` at every `n ≤ 200`. **W2** (2026-09-25, 19:01–19:10 UTC, ≈ 6 min of the 60-min
  consent): `results/ext_census_l7l11/` (112 cells, `ell = 7, 11`, `n ≤ 300`; no Loewy length ≥ 3, no
  algebra longer than 4, no cusp–cusp congruence at 7 or 11) and `results/ext_sturm_l5/` (101 cells
  under `sturm = cap=1000`, not golden-comparable: **0 of the 184 heuristic ideals finalised — the
  `sturm` cap is not the finality lever**), with the data set `congruence_census/w2_dataset/`
  (`hecke_census_dataset/v1`, 1243 rows); **owner-signed `63f2191`**. The curated second edition moved
  to slot 12 ([OD] S11-9).
* **Arbitrary `k` — BUILT by the (C2) digit induction** ([OD] S11-3; WP-18a merged `2b0df4f`, WP-18b
  `e920544`, WP-18c `afd9db0` + repairs `f1c0928`). **18a**: the native `u128` engine layer
  (`ModCtxU128.h`: `ModCtx<u128>`, `U128_Montgomery`, composite-only, `ell^k < 2^127`; `u256`;
  kernels and the §13.6 entry points instantiated; `ref::naive128`) and the width abstraction
  `engine::DigitWord<W>`, `W ∈ {u32, u64, u128}`; `EngineU128CompositeValidation` (26 587). **18b**:
  `engine::ladic` (`LadicInduction.h`, header-only) — the precision-split lemma (L1) with its proof in
  `ENGINE_API.md` §13.11.3, the level driver (word-native pivot search per window, replay at `K`), the
  canonical forms of §13.5–§13.6 at any `K`, and the **owner's width oracle matrix** (2 × 32 vs native
  `u64`; 4 × 32 and 2 × 64 vs native `u128`; cross-width agreement beyond `2^127`; an independent
  base-`ell` oracle `LadicRef.h`); `EngineLadicInductionValidation` (1888). **18c**: the pipeline route
  `Hecke/LadicCell` at `ell^k ≥ 2^64`, `ell ≥ 5` — the **per-cell certified precision bound**
  `K = k + e_max` (`e_max` from the shipped `K`-mode at word size; uncertified → `PrecisionInsufficient`,
  exit 5, resumable), `Θ_g` both routes, `A^{(q)}`, the free charpoly to precision `k`, and at `p = ell`
  the **ordinary idempotent** (Fitting, four certificates; certified at `(10, 691)` and at `(30, 5)`,
  a genuine split); [E] v1.12's grammar `Z/ell^k`, **`k ≤ 4096`**, with the per-cell rule; campaign
  digit jobs (`route`, `precision`, textual `modulus`, `hida`) and console digit handles;
  `HeckeLadicCellValidation` (891: the M-0 charpoly at `(10, 691)` beyond `2^127`, O5, UCT, cross-width,
  truncation, native `u128`, the bound at `e_max > 0`, cross-`K`). Every `ell^k < 2^64` keeps the
  shipped route bit for bit. Old L1-X step 2 (the `u128` pipeline instantiation) is **not** built:
  superseded. `obl:backend`(iv)'s digit-plane reading admitted ([OD] S11-10).
* **M-3 — ACCEPTED** (exit item 6; WP-11 merged `7649ac5`): `Integral/Model/StrictLift` for
  `diag(1, p²)`, `diag(1, p³)` and `pI` (`p ∈ {2, 3}`; `p = 5` at `ν = 2`), certified exactly over
  `Z[Γ″]`; `T(p, p) = p^n` on `H^q(C_I ⊗ R)`; **X7 in full** — `T_{p^{ν+1}} = T_p T_{p^ν} − p^{n+1}
  T_{p^{ν−1}}`, `ν ∈ {1, 2}`, on `H^q`, `q ≤ 5`, at 2 and 3 (with `p = ell`) and at good primes, with the
  `err:e1` / `rmk:relcoeff` controls; under [C] `prop:relationsmodel`(2);
  `HeckeStrictLiftRelationsValidation` (3619).
* **Engine carries F-1, F-2 — DONE** (exit item 7; WP-12 merged `696f784`): F-1 the Montgomery-64
  `mul_prep` / `mul_prepped` pair on the composite row updates (≈ 1.35–1.5× on `u64` Howell,
  indicative; `ModCtx::mul` itself unchanged); F-2 the ring travels as `(ell, k)`
  (`declare_coefficient_ring`), `ExactKthRoot` by deterministic Miller–Rabin, and a latent UB
  (`1 << 65` at `k = 1`) fixed; `ModCtxMontgomeryPairValidation`, `CoefficientRingKthRootValidation`
  (`fast`). **C-1 and E-1 (a/s) not shipped** (C-1 risks E5 (d)'s 3.5 % memory headroom; E-1 needs a
  quiet T2 window).
* **The examples document [EX] — PUBLISHED, 1.0.0** (exit item 13; WP-19 merged `c5b7e8e`, WP-20's
  Fable referee 0 B / 3 M / 11 m, repairs `a0d4206`; owner sign-off 2026-09-25, recorded at this
  close): `docs/latex/hecke_examples.tex` — the catalogue of 14 examples with exact data, record paths
  and certificate status, background, interpretation boxes, and eight talk slides; 21 pages, 0
  undefined. The referee's forms-side datum (the **full** Hecke algebra at `(142, 7)` has Loewy length
  3; the cohomological `A` is a quotient of it) is recorded as referee data, `RCOMP`, not pipeline output.
* **At this close (WP-17)**: the WP-15 referee's repairs ([C] v1.11.1, [E] v1.12.1, [P] v3.9.1); the
  referee's F-2 ruling applied in code — `DicksonThetaCell` refuses `ell ∈ {2, 3}` by `ENGINE_CHECK_MSG`
  naming `lem:h2torsion` (exit 3, as [E] `sec:thetaobj` (h) specifies), not `NotImplementedInThisBuild`;
  the five results READMEs record the owner's sign-offs; `results/README.md` §7 gains the slot's four
  sets; `slot11_close_window.sh`'s expectations (129 / 141; the census verdict read from its text).
* **Documents.** [C] v1.11.0-pre.1 → pre.2 → v1.11.0 → **v1.11.1**. [E] v1.12.0-pre.1 (WP-4) →
  pre.2 (WP-18c, spec first) → v1.12.0 → **v1.12.1**. [P] v3.9-pre.1 → v3.9 → **v3.9.1** (the θ verbs
  specified, not built). [EX] 0.1.0-pre.1 → pre.2 → **1.0.0**. [IB] erratum items 17–19.
  `ENGINE_API.md` §13.11 (the (C2) contract, rewritten by WP-18b before its code), §13.11.11 (the
  pipeline consumer), §13.12.9 (the `u128` layer as built). WP-14's review (pass 1: 0 B / 0 M / 10 m,
  all five packages accepted; pass 2: WP-18c M-1 / M-2 repaired, WP-7 accepted) disposed of.
* **The standing gates** ([OD] S7-G, `--gate`): hecke 256 new_min 0.4434 s (REF 0.4476), paired median ratio 1.007, headroom 5.7 %; decomp 128 new_min 0.0948 s (REF 0.0940), ratio 1.011, headroom 13.0 %; abs_gate MET, ratio_guard MET, verdict MET on both; `verdict_changes=0`; T2 against `a3ca7b4`: (10, 691) 1.0011 MET, (160, 691) 0.9923 MET; T-C4 1.452 s ≤ 5 s MET; walls `--all` 408.6 s, `--all-full` 756.3 s. Indicative in-slot pairs: none taken as verdicts
  (rule 5); the placement check `SAME` wherever it was run (WP-1, WP-12, WP-18a, WP-18b).
* **Not changed**: everything else; the v1.14 / v1.14.1 changelog below stands, except where this
  version supersedes it (v1.14's open item 2 — the L1-X question — is closed by [OD] S11-3; item 4,
  `thm:relations` on the model, closed by M-3).

**Open items at the slot-11 close** (owner items are **recorded, not ruled**):

1. **W1** (T1 against `a3ca7b4`, T2, T-C4, R-E8, the suite walls, the overlap table, the placement
   check) is the lead's window, not yet run at this version's writing (`WP-17_report.md` §10).
2. **The five-configuration `cross_config.sh` line** of exit item 2 (with every new slot-11 name) and
   **CheckThread on F-1's composite path** (`ENGINE_CUDA_DISABLE=1`) — the lead's; not run by WP-17
   (one build per agent). WP-12 ran `Check` (ASan / UBSan) on F-1 / F-2, 0 findings.
3. **Hida: slot 12, or slot 13** — the owner allows moving it to slot 13 ([OD] S11-12); the slot-12
   re-cut below prices it as slot 12's headline.
4. ~~**The console's `uint32_t` gap**~~ **[DONE, v1.17.1: S12 WP-17]** below `2^64` (`Z/5^k`, `14 ≤ k ≤ 27`; `Z/691^k`, `4 ≤ k ≤ 6`
   refuse at the console while larger `k` is served) — [P] Q9, the owner's.
5. **`open:ordprecision`**, narrowed at [C] v1.11.1 to a per-cell precision computable **before** the run
   (the torsion half is `rmk:ordtorsionfree`).
6. **`obl:coneexact`(vii) sentence 3 over the ring** and **`HeckeExtDeterminismValidation`'s wall /
   CheckThread with a live device**: as in v1.14 (unchanged).
7. **The 184 heuristic `ell = 5` ideals** need a new finality argument (W2's Q2: the `sturm` cap does
   not reach `proof_range`, which is decided over the anemic pool).
8. **`label_census.sh`'s exit code**: the lead observed a failing census exiting 0; the script
   `exec`s `label_census.py`, which returns 1 on an unresolved or stale site (`label_census.py:359`), so
   the observed 0 is most likely a pipeline's status (`… | tail`). Until slot 12 settles it, every gate
   reads the **text** (`unresolved=0 stale=0`), as `slot11_close_window.sh` now does.

### `[OD]` — the owner rulings of slot 11, as a register

Source: [S11] §10 (2026-09-25: *"All at recommendation"*, decision 3 re-ruled twice), the owner's later
rulings of 2026-09-25 as relayed by the lead, and the lead's defaults (marked).

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S11-1** | The cut **(A)**: the Dickson/θ headline (must) with the contract first (WP-2 + Fable referee WP-3); the census lane (WP-7, WP-8 in W2, WP-19 + WP-20 [EX]) all must; M-3, F-1 / F-2, the leftovers; full Hida → slot 12 | WP-2 … WP-8, WP-11, WP-12, WP-19, WP-20 — all accepted |
| **S11-2** | No slot-12 head start **(A)**: WP-9 and WP-10 not run; **2b**: tower primes `{5, 7, 11, 13}` whenever a tower runs | WP-9, WP-10 not run; 2b carried into the slot-12 re-cut |
| **S11-3** | L1-X: **(A′)** *"engine step now"* → re-ruled **(B)** *full L1-X in slot 11* (*"This fractured state is actually a good reason to do general k as early as possible"*) → **clarified**: arbitrary `k` by the **(C2) `ell`-adic digit induction in slot 11**, generic over `w ∈ {32, 64, 128}`, native `u32` / `u64` / `u128` as the oracles (2 × 32 vs `u64`; 4 × 32, 2 × 64 vs `u128`; cross-width beyond `2^127`) — the owner's binding design requirement; native `u128` built as the third width and oracle, not as the mechanism | WP-18a / 18b / 18c (1.60 AU); old step 2 not built; [E] grammar `k ≤ 4096` |
| **S11-4** | Process **(A)**: rules 1–18 carried; 19 (memory > 40 GB needs the owner; CUDA-safe `prlimit`; VmHWM watchdog), 20 (predictions committed first), 21 (contract first), 22 (placement check), 23 (no contact with the roadmap hosts) | every package; rule 20's one deviation recorded (WP-5); rule 21 checked by the lead (`3a0bbbf` before every θ claim commit) |
| **S11-5** | Engine levers and console **(A)**: F-1 / F-2 must; C-1 / E-1 a/s; WP-16 a/s | F-1 / F-2 done; C-1 / E-1 not shipped; WP-16 not built (gave way) |
| **S11-6** | Golden **(A)**: no event in slot 11; the first Hida emission is slot 12's | no event (the ledger) |
| **S11-7** | W2 **(A)**: WP-8's spec, ≤ 60 min, predicted time and RSS in the spec | ran 2026-09-25 (≈ 6 min; 13.4 GB peak) |
| **S11-8** | Ratifications: S10-D1 … S10-D5 ratified; [X] v1.14 open items 5–7 stay as recorded | — |
| **S11-9** | **Give-way ruling (i)**: *"Accept ~4.9 AU, keep all"* — WP-11 (M-3) stays in slot 11 (already built); only the census catalogue's second edition (≈ 0.05 AU) moves to slot 12 | WP-11 merged; edition 2 → slot 12; the W2 data set published instead |
| **S11-10** | **Ruling (ii), `obl:backend`(iv)**: the fixed-width digit-plane route of the (C2) induction is admitted explicitly; every operation stays in native words, so OD-3 (c)'s no-bignum intent is kept | [C] v1.11.0-pre.2 (M-1 of WP-3) → v1.11.0 worded to the route as built; `ENGINE_API.md` §13.11.8 |
| **S11-11** | **Publication sign-offs (2026-09-25)**: congruence census edition 1 (`bb7c860`); the W2 publications `ext_census_l7l11`, `ext_sturm_l5`, `congruence_census/w2_dataset` (`63f2191`); **[EX] 1.0.0** (the examples document, after WP-20's referee and repairs) | recorded in the five READMEs, `results/README.md` §7 and [EX]'s versioning section at WP-17 |
| **S11-12** | **Hida → slot 12, with the owner's leave to move it to slot 13** | the slot-12 re-cut below; open item 3 |
| **S11-13** | Rule 23: **no host go-ahead given** | no agent touched any §12 host (the lead states it in the exit table) |
| **S11-D1** *(referee ruling, applied)* | F-2 of WP-15: [E] `sec:thetaobj` (h)'s specification stands — `ell < 5` is a mathematical precondition, exit 3 — and the build changes | WP-17: `ENGINE_CHECK_MSG` naming `lem:h2torsion`; `HeckeDicksonThetaValidation`'s arm (X) asserts the kind and the name |
| **S11-D2** *(lead default)* | WP-18's split into 18a / 18b / 18c with the fragment `WP18.cpp` delegating to `WP18a/b/c.cpp`; WP-18c's edits to shared files (`Campaign/*`, `Console/Bindings/*`, `HeckeSettings.*`'s cap) accepted under its section | WP-18c finding 1 |
| **S11-D3** *(lead default)* | Two worktrees merged `hecke-extensions` mid-package (WP-7 took WP-6's merge, WP-18b took WP-18a's), each before any gate | `a373b11`, `7963f4d` |

---

**Version 1.14.1 — 2026-09-25. Slot-10 window W2 (packages WP-4 and WP-5, owner's consent after
W1): the two optional publications of [OD] S10-8 ran.** A status revision of v1.14; nothing else in
v1.14 moves. (1) **WP-4, the `ell`-adic survey under `Z/ell²`**: `docs/matrix-engine/results/ring_survey_l2/`
(`hecke_ring_report/v1`, `ell ∈ {2, 3, 5, 7, 11, 13, 691}`, even `n ≤ 64`, `p ∈ {2, 3}`: 462 jobs,
0 failed, 2.4 s); `ell²`-torsion exactly at `(30, 5)`, `(60, 5)`, `(56, 7)` — the loci of [C]
`rmk:bocksteinexp`(2) in the grid; O4 holds; 164 objects at the five `Z/ell²` E8 points equal
golden; analysis by the new `docs/matrix-engine/tools/ring_survey_analysis.py`. (2) **WP-5,
`ext_u691`**: `docs/matrix-engine/results/ext_u691/` — the 45 `u_ell_over_budget` cells of
`ext_first` at `u_ell = budget_mb=8192`, `ext_jobs = 6`: 0 failed, 0 over budget, every ideal final,
ext pass 216 s at 32.7 GB peak; all 189 ideals labelled uniquely from Σ(691); with `U_691` the
ideals, local algebras and certificates are those of `ext_first` at every cell. (3) Open item 3
below closed; `[OD]` S10-1 / S10-8 (and S9-9) effects updated. No golden event, no digest moved
(`--all` 120 / 120, `GOLDEN_STRICT=1` 11 666 / 0, 5901 / 0 on the publication build). Reports
`docs/implementation/slot10/WP-4_report.md`, `WP-5_report.md`. [E] v1.11.1 records the survey.

**Version 1.14 — 2026-09-25. Slot 10 close ([S10] WP-17): line 2 acts — the strict lift `τ_Iso`
and the periodicity class `e` built and certified exactly over `Z[Γ″]` / `Z[Γ]` (L2-1b), M1(a) the
first integral Hecke action (basis-free, a/s, accepted with X7 = commutativity); E8 complete —
`obl:coneexact`(vii) sentences 1–2 over `Z/ell^k` at every E8 point; the T2 `(10, 691)` miss
attributed and fixed; two value-preserving levers; arbitrary `k` designed, not built. No golden
event.** Sources: the slot-10 plan `hecke_extensions_slot10_plan.md` [S10] (revision 2, its audit
`hecke_extensions_slot10_plan_audit.md` and the owner's rulings of its §10, 2026-09-25), the package
reports `docs/implementation/slot10/WP-{1,2,3,6,7,8,9,10,11,12,13,15}_report.md`, WP-16's audit
(`docs/implementation/slot10/WP-16_audit.md`), the Fable review `docs/implementation/slot10/WP-14_review.md`
(passes 1–2), the Fable referee `docs/implementation/slot10/WP-15_referee_phase1.md`, the golden
ledger `docs/implementation/slot10/golden_ledger.md` and the close report
`docs/implementation/slot10/WP-17_report.md`. **The closing window W1 is the lead's**: every figure
only W1 gives is marked `[WINDOW W1: …]` in the report (§10 has the command).

**The slot moved golden nowhere** ([S10] §4.4; the ledger): R0 = R1 = **17 567** entries (tier A
**11 666**, tier B **5901**); `git log 2ac9ee8..HEAD -- '*GoldenReference.inc'` is empty, and
`golden_landing_check.sh 2ac9ee8` prints `LANDING merges=0 orphans=0 verdict=OK` — the first slot
since slot 7 without the "reference inside a merge" deviation, and now a checked rule. **All four
digests are unchanged from R0**, across WP-3's ring cross-routes, WP-6's pool layout, WP-7's levers,
WP-8's ninth fingerprint bit and every line-2 package: `EngineDeterminismValidation`
`0xe501ca19ee7815e1` (8 arms × 1279 records), `HeckeExtDeterminismValidation` `0x03b4f07c14555fec`
(printed `0x3b4f07c14555fec`), heavy `0x498147a50c6c1e30`, `ConsoleDeterminismValidation`
`0xf6ed04bbe8e6b60a` (24 / 24 arms). `tau_table_p2.txt`, `Hecke/HeckeReport.{h,cpp}`, the 34
pre-existing console transcripts, `cli_frozen/` and `docs/matrix-engine/results/` are byte-identical
to `2ac9ee8`. Final `GOLDEN_STRICT=1`: tier A 11 666 / 0, tier B 5901 / 0; `--all` 120 / 120 (10
`slow` skipped); `--all-full` 130 / 130 (the roster: **130 = 53 fast / 67 standard / 10 slow**, 75
`Hecke*`).

Changelog:

* **Line 2, L2-1b — DONE** ([OD] S10-2a). **(1) the strict lift** (WP-10, merged `cb1c3c4`):
  `Integral/Model/StrictLift` — `τ_Iso` of [C] `prop:strictlift`(1) for `T_2`, `T_3`, `T_5` in
  degrees `0 … q_max + 1 = 6`, by `lem:strictlifting`'s induction, boundary summands first; `y_0`
  read off the `BoundaryStrict` table and `k` by the closed-form column homotopies — **no linear
  solve** (a correction of the method, not of the theorem; [IB] erratum item 10, [C]
  `rmk:strictliftbuilt`); certificates (T1) on Schreier generators of `Γ″` (definitional on the free
  basis — bookkeeping), (T2), (T3), (S) `ε τ_Iso = τ^s ε` strictly, (B) `τ_Iso(R_∂) ⊆ R_∂` and
  `ε τ^∂_Iso = τ_∂ ε`, all exact; the coset transport `Θ̂_g` over any `ModCtx` a cochain map; the
  strict compatibility `ε^* Θ^s_g = Θ̂_g ε^*` entrywise on 359 cells of the eight rings with a shipped
  `Θ^s_g`; `Θ̂_g` on `H^1` equal to the shipped `A^{(1)}(T_p)` (canonical `τ`) on 26 cells at
  `ell ≥ 5`; O5 on 21 cells. **K1 did not materialise**: coefficients ≤ 3, entries ≤ `p`, ≤ 26 terms
  per value. `HeckeStrictLiftValidation` (1824 checks). **(2) the class `e`** (WP-13, merged
  `3e371a2`): `Integral/Model/PeriodicityClass` — `e ∈ Hom_{Z[Γ]}(R_2, Z)` as the Bockstein of
  `χ = ζ_+` (order 12, O2), `E = e ∪ −` as a certified chain map `R_{•+2} → R_•` with
  `aug E_0 = e`, `E_q^*` over any `ModCtx`, the Mayer–Vietoris connecting cochains through the
  Bass–Serre tree; every clause of `lem:bulkperiodic`(2) on 126 ring cells, equal to M0's groups;
  `HeckePeriodicityClassValidation` (2483 checks after WP-8's M-2 / m-9). The fallback route (R-1)
  was not needed and does not exist.
* **M1(a) — ACCEPTED (a/s)** ([OD] S10-2b; WP-11, merged `8f82016`): `Integral/Model/IntegralHecke`
  — `T_p` = `Θ̂_g` on `C_I ⊗ R`, read on cohomology with no integral basis (`induces_zero`, the UCT
  torsion readings (sub) / (quot) / (lat), a division-free charpoly); [IB] §6.2 M1(a) items 1, 2, 4,
  5 in full (O6 at 8 good primes; the 691-congruence module `Z/691` on line 1 and line 2 by two
  readings, `ι`-free; `Λ^1 ⊗ Z_ell` at 2, 3 split; X1), **item 3 without the `thm:relations`
  identities** — X7 = commutativity; the `T_{p^ν}` recursion needs `StrictLift` for `diag(1, p²)` /
  `diag(p, p)` (M-3, slot 11). Hosts `HeckeFreeModelValidation`'s tests (4) (arm (3c), X6) and (5)
  (arm (3d)); test (3) is WP-13's. `HeckeIntegralActionValidation` (4601 checks). M1(b) out
  (OD-3 (c) stands, S10-2c).
* **E8 — COMPLETE**: `obl:coneexact`(vii) **sentences 1–2** over `Z/ell^k` ([OD] S10-3; WP-3, merged
  `c9684e9`): `HeckeConeStrictPairRoute`, `HeckeConeRelativeRoute` and `EquivariantCohomologyOnK`'s
  relative sub-complex constructor honour the ring at `ell ≥ 5`, `ell^k < 2^32`; both cross-routes
  give `A_c` entrywise equal to route 1's at the seven E8 points in every degree (route 3 with no
  inverse over the ring: `M` and an explicit `N`, `M N = N M = I`); above `2^32` the uint32
  cross-routes refuse by the ring context's named regime refusal; at `ell ∈ {2, 3}` all three refuse
  by name. **Sentence 3** (the PD adjointness gate of `prop:coneroutes`(3)) is **recorded unavailable
  over the ring** — the pairing and the contragredient refuse a composite ring (WP-14 M-1; [C]
  v1.10.0 (vii), [E] v1.11.0 (b1) / (f)). `F_ell` cone byte-identical (`cone_output_diff.sh` 0
  hunks). `HeckeConeCrossRouteRingValidation` (431 checks with WP-8's m-12 asserts).
* **T2 `(10, 691)` — ATTRIBUTED AND FIXED** ([OD] S10-9; WP-6, merged `2e5f073`): not code on the
  path — slot 9's WP-4 merge `8c9faf4` moved `ThreadPool::global()`'s static pool from 32 to 0 mod 64
  in `.bss`, splitting the registry mutex across two cache lines; the cell runs 52 558 parallel
  regions per repeat, so it read ≈ 4 % slower with identical work (proved by `ENGINE_TRACE_NODES`,
  `ENGINE_THREADS=1`, and a controlled placement experiment). Fix: `alignas(64)` on `slots_` and
  `regions_` (layout only). **The placement lesson**: a head-to-head of two binaries is valid only
  when both place the global pool alike (`nm -S … | grep …ThreadPool6globalEvE4pool`).
* **Levers** ([OD] S10-11; WP-7, merged `4560624`): the cone / `ι` profile at `(160, 691)`
  (the sign split 1.80 s did not scale with threads; the cone's `ConeCertificate::verify` is 70 % of
  the cone); **I-1** `obl:iota`(iii)'s checks and `prop:iotasplit`'s splits as host tasks in the
  serial order (1.80 → 0.79 s); **L4** route 2's block rows on the consumer pool (`U_10007` `n = 0`
  route 2 1.26 → 0.25 s; T2's `(10, 691)` ≈ −24 %). Both byte-identical (`cone_output_diff` 0/0,
  84 / 84 ext records, `bench_identity` 45 / 0, CheckThread 0). C-1 (the certificate's span tests)
  recorded for slot 11.
* **Carries** (WP-8, merged `7551dcc`): **the ninth fingerprint bit** ([OD] S10-10) — bit 256 iff
  `effective_policy() == Gpu`, the fold shift `<< 56 → << 55`; `hybrid` and `gpu` no longer share a
  cache slot; `EngineFingerprintDeviceBitValidation` (`fast`, 8); `EngineElimPassOptionsValidation`
  18 → 19; four digests unchanged. WP-11's **m-6 / m-7** (`HeckeFreeModelValidation`: (T6) refuses
  on the object's 3 degrees; arm (R) dropped; 803 → 801). The review's **M-2** (an oriented disc,
  `fill_x1` reaches round 2), **m-9**, **m-12**, **m-16**. `slot10_close_window.sh` (REF `2ac9ee8`,
  REF2 `bd6d1bb` for T2-D, the landing check, the disk guard).
* **Console leftovers** ([OD] S10-6; WP-12, merged `6726075`): the one named `Console/Core/`
  exception at **two sites** (`Evaluator::object_member`'s wrap; the core `resume` verb's position),
  the five structural ring-handle members honour (`LocalSystem.n / .d_V / .coefficient_ring` — the
  last a new member — `HeckeOperator.p / .r`), the campaign verbs' handler (`NotImplementedInThisBuild`
  → exit 5; no input reaches it at the base, recorded); `ConsoleErrorValidation` arm (W) 218 → 294;
  script `026` (first freeze); `console.md` regenerated. [P] v3.8.
* **Arbitrary `k`, designed** ([OD] S10-7; WP-9, merged `4664b40`): `ENGINE_API.md` §13.12 — L1-X,
  a composite-only `u128` element type (`U128_Montgomery`, `ell^k < 2^127`), **specified, not
  built**; §13.11's trigger restated (T-1 / T-2 / T-3); a scratch-only probe (`u128` Howell ≈ 3.6×
  the tree's `u64`); findings F-1 (the `u64` `ModCtx::mul` is `__umodti3`: a Montgomery-64 pair ≈
  1.45× on Howell) and F-2 (`ExactKthRoot`'s trial division, a blocker for L1-X).
* **Process** (WP-1, WP-16): `Registry/Slot10/` + `cmake/slot10/` (kept, the pattern);
  `disk_guard.sh` (every building package ran it); `golden_landing_check.sh` (negative control on
  `3e7abbc`: `merges=2 verdict=FAIL`); persistent scratch `$HACS_DATA/s10`;
  WP-16's read-only worktree / disk audit (≈ 20 GB reclaimable; removals owner-approved per row).
* **Documents.** [E] **v1.11.0-pre.1** (WP-2, before any lift commit) → **v1.11.0-pre.2** →
  **v1.11.0** (WP-15 phases 1–2). [P] **v3.8-pre.1** → **v3.8**. [C] **v1.10.0** (WP-15, `X`:
  `rmk:strictliftbuilt`, `rmk:bredonhecke`, `lem:bulkperiodic` Step 0's sign pinned, (vii) as built)
  → **v1.10.1** (the referee's M-1, M-2, m-1 … m-4). [IB] erratum items 10–16. `ENGINE_API.md`
  §10.6 (WP-8), §13.11–§13.12 (WP-9). WP-14's review (passes 1–2: B 0 / M 3 / m 17) and WP-15's referee
  (B 0 / M 2 / m 6) disposed of: M-1 and M-3 in the documents, M-2 in WP-8, the minors applied or
  carried below.
* **The standing gates** ([OD] S7-G, `--gate`): W1 (2026-09-25): hecke 256 new_min 0.4419 s (ratio 0.985) / decomp
  128 new_min 0.0947 s (ratio 0.976) against a 2ac9ee8 binary, both MET; T2 (10, 691) 0.7365 / (160, 691) 0.9744 MET; T2-D against
  bd6d1bb 0.7594 / 0.9808 (reported); `verdict_changes=0`. Indicative in-slot pairs (WP-3, WP-6, WP-7; shared box): ratio guard met throughout
  (0.988–1.015).
* **Not changed**: everything else; the v1.13 changelog below stands, except where this version
  supersedes it (v1.13's open items 1, 2, 4, 5 and 6 closed here — W1 ran in slot 9; item 3 carried as open item 3 below, items 7–8 as open item 6, item 9 as open item 7).

**Open items at the slot-10 close** (owner items are **recorded, not ruled**):

1. **W1** (T1 against `2ac9ee8`, T2 and T2-D, R-W, R-G, R-L2, the suite walls, the overlap table) is
   the lead's window, not yet run at this version's writing (`WP-17_report.md` §10 has the command).
2. **Decision 7's follow-up — build L1-X in slot 11?** WP-9's recommendation: **do not build unless
   the owner names a T-1 or T-2 computation with its cells**; alternatives (a) step 1 alone
   (0.35 AU) as infrastructure, (b) F-1 independently.
3. ~~**W2 did not run**: WP-4 (the `Z/ell²` survey, a/s) and WP-5 (`ext_u691`, optional) deferred.~~
   **Closed in v1.14.1**: W2 ran after W1 (owner's consent, 2026-09-25); both sets published
   (`results/ring_survey_l2/`, `results/ext_u691/`).
4. **`thm:relations` on the model** (M-3): the `T_{p^ν}` recursion needs `StrictLift` for
   `diag(1, p²)` and `diag(p, p)`; whether it is a theorem at 2 and 3 for `Θ_Iso,g` — [IB] §1.3
   asserts it on `H^•(Γ; V)`, [C] has no statement (WP-15 finding 6).
5. **`obl:coneexact`(vii) sentence 3 over the ring** is recorded unavailable until the pairing and
   the contragredient honour a composite ring (not scheduled).
6. **`HeckeExtDeterminismValidation`'s wall** and CheckThread with a live device: as in v1.13 open
   items 7–8 (unchanged; W1 re-measures the wall).
7. **For the owner**: v1.13's open item 9 (`rmk:bocksteinexp`(1)'s conservative scope) stays "no
   ruling asked" ([OD] S10-15).

### `[OD]` — the owner rulings of slot 10, as a register

Source: [S10] §10 (2026-09-25: *"All at recommendation."*), the owner's answers of 2026-09-25 as
relayed by the lead, and the lead's defaults (marked).

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S10-1** | Scope **(A)**: 2.75 AU must-accept + 0.85 (a/s) + 0.10 contingency, ceiling **3.70 AU** (3.95 with the cond. fallback; 4.05 with WP-5) | WP-1 … WP-3, WP-6 … WP-17; the fallback not needed; WP-4 / WP-5 run in W2 after the close (v1.14.1) |
| **S10-2** | Line 2: **2a (A)** L2-1b must-accept, split WP-10 / WP-13; **2b (A)** M1(a) (a/s) with a close-time cut-off; **2c (A)** M1(b) out, OD-3 (c) stands | WP-10, WP-13; WP-11 accepted before the cut-off, item 3 with X7 = commutativity (M-3) |
| **S10-3** | `obl:coneexact`(vii) over the ring **(A)**: WP-3 must, the three members at `ell ≥ 5`, `ell^k < 2^32`; the uint32 regime refusal above; no golden | WP-3; sentences 1–2 discharged, sentence 3 recorded unavailable (M-1); §6.2 E8's v1.14 note |
| **S10-4** | The Bredon object at `ell ∈ {2, 3}` **(A)**: lift neither the cochain map nor the operator; the refusal stays; the reason in [E] (b3) and a [C] remark; the [X] re-cut row withdrawn | [E] (b3), [C] `rmk:bredonhecke`; the v1.13 re-cut row "`HeckeOperatorOnK` over `Z/ell^K` at `ell ∈ {2, 3}`" **withdrawn** |
| **S10-5** | Process **(A)**: WP-1 day zero (fragments kept, disk guard, landing check); rule 11's cherry-pick landing; rules 14–18 | WP-1; no golden event to land |
| **S10-6** | Console leftovers **(A)**: one named Core exception (`object_member`'s wrap), the five structural members honour, the two campaign verbs exit 5 | WP-12 (with S10-D1 … D3) |
| **S10-7** | Arbitrary `k` **(A)**: design now (WP-9), build decision at the close | WP-9 "designed"; the build question is open item 2 |
| **S10-8** | W2 publications **(A)**: WP-4 (a/s) and WP-5 (optional), owner-signed, if the box is lent | **run in W2** (v1.14.1): `results/ring_survey_l2/` (WP-4), `results/ext_u691/` (WP-5) |
| **S10-9** | T2 `(10, 691)` **(A)**: WP-6 bisects (must), fix (a/s), rule text unchanged, T2-D reported in W1 | WP-6: attributed to the pool placement, fixed |
| **S10-10** | The ninth fingerprint bit **(A)**: fix, value-free | WP-8 |
| **S10-11** | Levers **(A)**: profile (must); L4 and one cone / `ι` lever (a/s, ≤ 0.20) | WP-7: I-1 and L4 shipped; C-1 → slot 11 |
| **S10-12** | [C]'s next version **(A)**: v1.10.0 `X` with a Fable referee | [C] v1.10.0 → v1.10.1 |
| **S10-13** | Windows **(A)**: W1 with T2-D; W2 per S10-8; the full protocol | `slot10_close_window.sh` (WP-8); W1 the lead's |
| **S10-14** | Disk and worktrees **(A)**: rule 14's budget; WP-16's read-only audit on day zero; removals per row on approval. **Owner's answer (2026-09-25): the WSL disk image is not sparse / unknown** — the strict disk rules apply, no compaction assumed | `disk_guard.sh` run by every building package; WP-16 |
| **S10-15** | Ratifications: S9-D1 … S9-D7 ratified; v1.13 open item 9 stays "no ruling asked" | — |
| **S10-OA1** | **The WP-16 cleanup — owner-approved 2026-09-25**, per row | executed by the lead: 39 → 18 worktrees at the close, the main tree's `build-xconfig/` (7.9 GB) removed |
| **S10-D1** *(lead default)* | WP-2's deviation 1: the named Core exception at **two sites** (`Evaluator::object_member` and the core `resume` verb's position), not "this function only" | WP-12; [P] v3.8 §2 C7 |
| **S10-D2** *(lead default)* | WP-2's deviation 2: **`LocalSystem.coefficient_ring`** added as a new structural member (it did not exist at R0), `console.md` regenerated | WP-12 |
| **S10-D3** *(lead default)* | WP-2's deviation 3: `campaign_plan` gets the explicit handler with **no test hook**; the exit-5 branch's reachability recorded (none found at the base, for either verb) | WP-12; [P] v3.8 §8 |
| **S10-D4** *(lead default)* | **WP-11's X6 ordering**: WP-11 started on `cb1c3c4` (without WP-13), wrote X6 against WP-13's API with the lead's approval, and fast-forwarded onto WP-13's merge `3e371a2` before any gate; its `--list` line precedes WP-13's (fragment call order) | WP-11 |
| **S10-D5** *(lead default)* | **Lane B parallelised**: WP-8 ran beside WP-7 (disjoint files; WP-8 on WP-6's tip) instead of the plan's `ModArithmetic/Engine/*` order WP-6 → WP-8 → WP-7 | WP-7 `4560624`, WP-8 `7551dcc` |

---

**Version 1.13 — 2026-09-25. Slot 9 close ([S9] WP-17): E8 declared complete as specified (4b by
route 1, `obl:coneexact`(vii) over the ring open), `EquivariantCohomologyOnK` over `Z/ell^k` at
`ell ∈ {2, 3}` (the Bredon object), line 2's L2-1a and M0 done, C5 done in three lanes, the engine
findings fixed, two value-preserving levers shipped.** Sources: the slot-9 plan
`hecke_extensions_slot9_plan.md` [S9] (revision 2, its audit and the owner's rulings of its §10,
2026-09-24), the package reports `docs/implementation/slot9/WP-{1,2,3,4,4t,5,6,7,8,8c,9,10,11,12,13,15}_report.md`,
the Fable review of WP-3 / WP-4 / WP-10 / WP-11 (`docs/implementation/slot9/WP-14_review.md`,
reconstructed — the original was lost in the 2026-09-25 disk-full crash), the Fable referee of
WP-15, the re-baseline note `docs/matrix-engine/rebaseline-2026-09-24-e8-4b-addonly.md`, the golden
ledger `docs/implementation/slot9/golden_ledger.md` and the close report
`docs/implementation/slot9/WP-17_report.md`. **The closing window W1 is the lead's**: every figure
only W1 gives is recorded in the report §10 (W1 ran 2026-09-25).

**The slot moved golden once, by the ruled event R1** ([S9] §2.5; the ledger): E8 item 4b's add-only
emission at the seven existing `E8 ring=…` points (`762dbc3`: **+126**, 17 441 → **17 567**, tier A
11 575 → **11 666**, tier B 5866 → **5901**; `golden_ref_diff.py --expect` set equality,
`golden_explain.py` exit 0 with no flags; re-checked at the close). It landed inside a merge commit
— slot 8's recorded deviation, repeated (the ledger). **All four digests are unchanged from R0**,
across R1 and WP-6's engine change: `EngineDeterminismValidation` `0xe501ca19ee7815e1` (8 arms × 1279
records), `HeckeExtDeterminismValidation` `0x03b4f07c14555fec` (printed `0x3b4f07c14555fec`), heavy
`0x498147a50c6c1e30`, `ConsoleDeterminismValidation` `0xf6ed04bbe8e6b60a` (24 / 24 arms).
`tau_table_p2.txt`, `Hecke/HeckeReport.{h,cpp}`, the 22 pre-existing console transcripts,
`cli_frozen/` and `docs/matrix-engine/results/` are byte-identical to `bd6d1bb`. Final
`GOLDEN_STRICT=1`: tier A 11 666 / 0, tier B 5901 / 0; `--all` 115 / 115 (10 `slow` skipped);
`--all-full` 125 / 125 (the roster: **125 = 52 fast / 63 standard / 10 slow**, 71 `Hecke*`).

Changelog:

* **§6.2 E8 — COMPLETE AS SPECIFIED: "4b by route 1; (vii) over the ring open"** (ruling 3 (iii)
  (A); §6.2 E8's v1.13 note). **Item 4b** (WP-4 `d0aca96`, merged `8c9faf4`; review repairs
  `2933b65`, `7ddb555`; R1 `762dbc3`): the boundary and `Cone(r)` over `Z/ell^k` at `ell ≥ 5`
  through a dense module route (`ModuleConeT`, `ConeModuleCertificate` item 14 —
  `obl:coneexact`(iv)'s non-field half by solves; `ModuleConeActionT` route 1; `HeckeBoundaryOperatorT`;
  the reductions and Bocksteins on both, as map equalities); the strict-pair and relative
  cross-routes and the relative sub-complex constructor keep refusing, each with an arm; the `F_ell`
  cone byte-identical (`cone_output_diff.sh` against `bd6d1bb`: 0 hunks). **Item 3 at `ell ∈ {2, 3}`**
  (WP-3 `97d0a8d`, ruling 4 (A), superseding S8-D2): `EquivariantCohomologyOnK` honours `Z/ell^k`
  there under the scoped `SmallEllPolicy::Bredon` (a lead default, [OD] S9-D1) by a flat-coordinate
  module route (lengths and invariant factors only — the Bredon object), against O7 frozen from
  `integral_line_probe.py --model-R` on 96 cells (`HeckeBredonTreeRingValidation`, 1394 checks);
  the `K`-mode, `HeckeOperatorOnK` and `HeckeReduction` refuse there by name.
* **WP-4t — the 4b checks trimmed** (owner-approved 2026-09-25, [OD] S9-OA1): `(60, 5)`'s ring arms
  move to `HeckeReductionCoverageSlowValidation` (`slow`), the implied rows dropped (41 in the `standard` tier);
  `HeckeReductionValidation` 69 122 → **68 970** checks (4b arms 458 → 306, ≈ 5.7 → ≈ 1 s), the slow
  sibling **3731**; the `(60, 5)` values stay gated in `--all` by golden R1.
* **Line 2: L2-1a DONE, M0 DONE (a/s, accepted).** L2-1a (WP-10 `3333640`, merged `d6bc839`):
  `Integral/Model/IsotropyModel` — `R`, `R_∂`, `ε` on `Xbulk` to `q_max + 1`, ranks `5, 14, 19` and
  `3, 6, 6`, `d² = 0` / `R_∂` closed / `ε` a chain map certified exactly over `Z[Γ]`, `Ĉ` over any
  `ModCtx`; `HeckeIsotropyModelValidation` (1032 checks). M0 (WP-11 `022fabe`, merged `f2e2ef6`):
  `Integral/Model/IntegralGroups` — `H^q(SL_2(Z); Sym^n Z²)`, `n ≤ 20`, `q ≤ 5`, **equal to [IB]
  Appendix A exactly on 126 / 126 cells**, `K` certified per differential ([C] `rmk:certifiedeperdiff`,
  v1.9.0); `HeckeFreeModelValidation` (`standard`, 803 checks), [IB] §6.2 M0 items 1–8.
* **C5 DONE in three lanes** (ruling 2 (A)): **C5a** (WP-12 `b3cd0d3`; follow-ups `f28a0fa`): E7's
  `ContragredientLocalSystem` / `Pairing`, E8's ring lift at `ell ≥ 5` ([E] `sec:ring` (h),
  `bind::GateTypeOnRing`), the **Core batch** — the two named `Console/Core/` exceptions of ruling 2
  (ii): the `set`-statement error position, and a legal but unexecutable `--set` value → **exit 5**
  (`ConsoleErrorValidation` (K) 1 → 5; S8-D4 superseded); scripts `023`–`025`. **C5b** (WP-13
  `80eb184`): the extension-layer bindings (`ExtRecord`, `MaximalIdeal`, `HeckeAlgebra`, `LoewyProfile`,
  `ExtensionClass`, `Presentation`, `Atlas`, `GF` / `GFElt`, `Settings`, `Involution`,
  `BoundaryCohomology`, `ConeCohomology`), the certificate-free local-algebra verbs
  (`HeckeExt/HeckeAlgebraInvariants`), `check_identities`; `HeckeExtAlgebraInvariantsValidation`;
  scripts `040`–`047`. **C5c** (WP-8 `ad65bd9`, `f4fc3d2`, merged `8853544`; ruling 6 (A)): the
  campaign job loop over `Z/ell^k` (`Campaign/CampaignRing`, the job-level schema
  `hecke_ring_report/v1` only under a non-default ring, `campaign.md` §15; the ext pass refuses;
  `(g11)`'s coefficients as **decimal strings**, a lead decision, [OD] S9-D2);
  `CampaignRingValidation` (693 checks); no campaign job id at the defaults moved. **WP-8c**
  (`cc3d30a`): `campaign_spec` / `campaign_spec_text` surface a ring refusal as exit 5
  (`ConsoleErrorValidation` arm (M)); script `048` pins C5c from the console. The 22 pre-existing
  transcripts and `cli_frozen/` are byte-unchanged; `console.md` regenerated.
* **Engine findings 2–3 fixed** (WP-6 `5689c20`, ruling 7 (A)): the tape elimination driver compiles
  under `consumer_pass_options()`; `pass_options_fingerprint()` keys the effective device policy
  (bit 128 iff `effective_policy() != Cpu`); value-free, four digests unchanged; the batch and device
  arms now reach the per-panel programs (non-vacuity by counts); walls within the stop thresholds
  (ConsoleDet 29.2 s ≤ 45, ExtDet 13.9 s ≤ 20, EngineDet 4.7 s ≤ 10, indicative) — **S8-D3's
  ratification stands**. The CUDA layer's launch counters became relaxed atomics (a pre-existing race
  WP-6 made reachable; accepted, [OD] S9-D3). `EngineElimPassOptionsValidation`.
* **In-cell levers** (WP-7 `b2941cb`, ruling 8 (A); the post-L1 profile in the report): **L3** the
  arena first-fit in `O(log L)` (every offset identical by construction; `EngineArenaFirstFitValidation`;
  cold `(18, 10007)` 25.9 → 10.8 s), **L2** the narrower `τ` lock in `build_pipelines()`
  (`HeckeFamilyConcurrentBuildValidation`; the `ell = 10007` parallel pass 53 → 16 s), **L5** the
  `--campaign-cell` timings; **L4 recorded, not shipped** (slot 10). The step-0 fix `158c0be` (the
  campaign job loop no longer names `SmallEllPolicy::Bredon`) came with it.
* **Carries** (WP-9 `fb8a63a`): `PerformanceSmokeValidation`'s floors skipped without `NDEBUG`
  (open item 6 of v1.12 closed); `RunPipelineModEll`'s named guard; `get_prime()` refuses a composite
  object (one live call site re-pointed); the slot-8 note's header; the review minors m-1, m-2, m-4 as
  three `fast` validations (`SmallEllPolicyScopeValidation`, `HeckeBredonU64FlatRouteValidation`,
  `IsotropyModelDeltaSquaredValidation`).
* **Process** (WP-1, WP-5): the per-package registration and source-list fragments
  (`Registry/Slot9/WP<n>.cpp`, `cmake/slot9/WP<n>.cmake`) used by every registering package;
  **kept, not folded**, as the slot-10 pattern ([OD] S9-11). The window instruments `box_watch.sh`,
  `prewindow_check.sh`, `window_overlap.py`, per-round timestamps in the two head-to-head harnesses,
  `slot9_close_window.sh` (updated at the close to the post-R1 expectations and 33 comparisons).
* **Documents.** [E] **v1.10.0-pre.1** (WP-2) → **v1.10.0-pre.2** / **v1.10.0** (WP-15 phases 1–2)
  → **v1.10.1** (WP-17: the referee's M-1, m-7, m-8, m-10). [P] **v3.7-pre.1** → **v3.7** →
  **v3.7.1** (m-6 and WP-8c's exit 5, m-10). [C] **v1.9.0** (WP-15, `X`: `rmk:bocksteinexp`(2) at
  every prime, `rmk:certifiedeperdiff`, `def:ringsemantics`(2) and `obl:coneexact`(iv) as built)
  → **v1.9.1** (WP-17, `Y`: M-1, M-2, m-1 … m-4). [IB] erratum block at its head (WP-15, ruling 5c;
  item 8 corrected at the close, m-5). `ENGINE_API.md` §10.6 / §10.9 (WP-6), §13.7 pointer (WP-4).
  The pre-release identifiers stand ([OD] S9-D4). **Recorded deviation**: WP-3 merged (`b53836f`)
  before [E] v1.10.0-pre.1 (`f768848`), whose text was amended to WP-3's scoped lift before its
  commit; every later lift followed the spec. WP-15's Fable referee: 0 B / 2 M / 11 m, accept
  after repairs — all repaired at this close or recorded (§8's slot-10 re-cut).
* **The standing gates** ([OD] S7-G, `--gate`): hecke 256 0.4385 s (ratio 0.995) / decomp 128 0.0937 s (ratio 1.004) against a
  bd6d1bb binary, MET on both; T2 `(10, 691)` NOT_MET at 1.054 (REF ext time 0.12 ms), `(160, 691)` MET at 1.013. Indicative in-slot pairs (WP-4, WP-6, WP-7; shared box): ratio guard met
  throughout (0.930–1.006).
* **Not changed**: everything else; the v1.12 changelog below stands, except where this version
  supersedes it (open items 2–7 and 9 of v1.12, closed here; S8-D2, D4, D5 superseded by rulings 4,
  2 (ii), 10).

**Open items at the slot-9 close** (owner items are **recorded, not ruled**):

1. **W1** (the standing gates, T2, R-E8, T-C4, the suite walls, the overlap table) is the lead's
   window, not yet run at this version's writing (`WP-17_report.md` §10 has the commands).
2. **`obl:coneexact`(vii) over `Z/ell^k`** is open (ruling 3 (iii) (A)): the strict-pair and relative
   cross-routes and the relative sub-complex constructor over the ring; ≈ 0.20 AU.
3. **WP-16, the `ext_u691` campaign** (ruling 9, optional) did not run: deferred to slot 10 with the
   owner's W2.
4. **Console leftovers**: `Evaluator::object_member` does not wrap a member getter's exception (no
   `file:line:col`; WP-12 finding 1 — the next Core batch); structural members of ring handles
   (`LocalSystem.n / .d_V / .coefficient_ring`, `HeckeOperator.p / .r`) exit 5 under (h)'s literal
   list (WP-12 finding 2, WP-15's owner question 3); `run_campaign` still wraps a
   `NotImplementedInThisBuild` as exit 3 and `campaign_plan` has no wrap (m-6's code half; WP-8c
   fixed the two spec verbs).
5. **WP-11's m-6 and m-7** (review): `HeckeFreeModelValidation`'s (T6) refuses on its own enum
   (self-referential); its arm (R) re-runs two registered names in process and inherits
   `HECKE_INTEGRAL_CAMPAIGN=1`'s ≈ 30 s.
6. **`hybrid` and `gpu` share the fingerprint's device bit** (WP-6 finding 4): a ninth bit widens
   `extra << 56` and moves every cache key (never a value).
7. **`HeckeExtDeterminismValidation`'s wall** reached 19.06 s at load 11.9 against its 20 s stop
   (WP-6 finding 1; min 13.9 s); W1 re-measures it.
8. **CheckThread with a live device** reports driver-internal `memcpy` races inside `libcuda`
   (pre-existing; not fixed, not suppressed); the protocol runs CheckThread under
   `ENGINE_CUDA_DISABLE=1`.
9. **For the owner** (WP-15 referee m-9): `rmk:bocksteinexp`(1) is prime-free as proved; its
   `ell ≥ 5` scoping is conservative. No ruling asked.

### `[OD]` — the owner rulings of slot 9, as a register

Source: [S9] §10 (2026-09-24: *"all at recommendation. You have go."*), the owner's instructions
during the slot as relayed by the lead, and the lead's defaults (marked).

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S9-1** | Scope **(A)**: 4.15 AU must-accept + 1.20 (a/s) (M0 1.00, levers 0.15, R1 0.05) + 0.10 contingency, ceiling **5.45 AU** (5.55 with the optional WP-16) | WP-1 … WP-15, WP-17; WP-4t, WP-8c added; WP-16 not run |
| **S9-2** | C5 **(i)(A)** three lanes, all must-accept; **(ii)(A)** both `Console/Core/` edits as named exceptions | WP-12 (C5a + Core batch), WP-13 (C5b), WP-8 / WP-8c (C5c) |
| **S9-3** | E8 item 4b **(A)**: must-accept, dense module route; R1 (a/s) predicate-gated at the seven points, landed by the lead after WP-14 pass 1. **(iii)(A)**: route 1 only; (vii)'s composite half open; E8 "complete as specified: 4b by route 1; (vii) over the ring open" | WP-4, R1 `762dbc3` (inside a merge — deviation, the ledger); §6.2 E8's v1.13 note |
| **S9-4** | `ell ∈ {2, 3}` **(A)**: lift for `EquivariantCohomologyOnK` only, flat-coordinate module route; `K`-mode, Hecke, reduction refuse; O7 frozen in `HeckeBredonTreeRingValidation` (supersedes S8-D2) | WP-3 |
| **S9-5** | Line 2: **5a (A)** L2-1a must-accept; **5b (A)** M0 (a/s) with a close-time cut-off; **5c (A)** an erratum block at [IB]'s head | WP-10; WP-11 (accepted before the cut-off); WP-15 |
| **S9-6** | C5c **(A)**: `hecke_ring_report/v1` only under a non-default ring; `hecke_report/v2` untouched; the ext pass refuses | WP-8 |
| **S9-7** | WP-6 **(A)**: findings 2 and 3 fixed, value-free, stated walls with stop thresholds | WP-6; no threshold crossed |
| **S9-8** | In-cell levers **(A)**: re-profile after L1, ship supported value-preserving levers | WP-7: L3, L2, L5 shipped; L4 recorded |
| **S9-9** | Second ext campaign **(A)**: `ext_u691`, optional, owner-signed, W2 | **not run** (slot 10); run in slot-10 W2 as WP-5 (v1.14.1) |
| **S9-10** | [C]'s next `X` **(A)**: v1.9.0 in WP-15 with a Fable referee | [C] v1.9.0 → v1.9.1 |
| **S9-11** | Fragments **(A)**: WP-1 on day zero; WP-17 folds or keeps them | **kept** as the slot-10 pattern (the close's choice: folding would churn two shared files for no gain; `Registry/Slot9/README.md` states the rule) |
| **S9-12** | Windows **(A)**: W1 closing, W2 optional; pre-check, watcher first, per-round timestamps, overlap table | WP-5; W1 run 2026-09-25 (gates MET; T2 (10,691) NOT_MET) |
| **S9-13** | Ratifications: S8-D1 and [WP8-13] §4 item 1 ratified; **S8-D3 ratified conditionally on WP-6 (e)** — the condition held (29.22 s ≤ 45 s); S8-D2, D4, D5 superseded by rulings 4, 2 (ii), 10 | WP-6 (e) |
| **S9-OA1** | **WP-4t, the 4b trimming — owner-approved 2026-09-25**: `(60, 5)` to the `slow` sibling, the implied rows dropped | WP-4t `45acc4f`, merged `7e379bd` |
| **S9-D1** *(lead default)* | the `ell ∈ {2, 3}` lift is **scoped** (`SmallEllPolicy::Bredon`, passed by `EquivariantCohomologyOnK` alone; the default policy still refuses), not the plan's literal global flip; enforced by `SmallEllPolicyScopeValidation` | WP-3, WP-9; `158c0be` |
| **S9-D2** *(lead default)* | `hecke_ring_report/v1`'s `(g11)` `charpoly_free.coeffs` are **decimal strings** (they exceed `2^53` at `uint64_t` cells), before v1.10.0 froze the schema | WP-8 `f4fc3d2`; [E] v1.10.0 (g11) |
| **S9-D3** *(lead default)* | WP-6's **CUDA launch counters as relaxed atomics** (an edit to an existing `EngineCuda` file no shared-file rule named) **accepted** | WP-6 |
| **S9-D4** *(lead default)* | the **pre-release version identifiers** (`1.10.0-pre.1`, `-pre.2`, `3.7-pre.1`) stand as written | WP-2, WP-15 |
| **S9-D5** *(lead default)* | **lane B parallelised**: WP-8 ran beside WP-6 (disjoint files) instead of after WP-7 | WP-8's base `5618e04` |
| **S9-D6** *(lead default)* | WP-15's binding spellings `settings_snapshot()` and the `gf_*` verbs stand (structural reasons; the referee recommends ratifying) | [P] v3.7 |
| **S9-D7** *(lead default)* | the exit-3 observation of WP-15 phase 2 fixed in a binding-only follow-up (WP-8c), not in `Console/Core/` | WP-8c `cc3d30a` |

---

**Version 1.12 — 2026-09-24. Slot 8 close ([S8] WP-14): E8 items 2, 3 and 4a accepted and emitted
add-only (R1), the line-2 starters and the integral-line chapter of [C] delivered, the ext pass
parallel and its cache bounded, C4 done.** Sources: the slot-8 plan
`hecke_extensions_slot8_plan.md` [S8] (revision 2, its audit and the owner's rulings of its §10,
2026-09-24), the package reports `docs/implementation/slot8/WP-{1,2,3,3r,4,5,6,6b,7,8,9,10,11a,11b,13,L1}_report.md`,
the Fable review of WP-12 and the referees of WP-9 and WP-13, the re-baseline note
`docs/matrix-engine/rebaseline-2026-09-24-e8-addonly.md`, the golden ledger
`docs/implementation/slot8/golden_ledger.md`, the integral-line design brief
`docs/implementation/integral_line_design_brief.md` [IB] (revision 2) with its audit, and the close
report `docs/implementation/slot8/WP-14_report.md`. **The window figures (W1, W3) were measured 2026-09-24** (`WP-14_report.md` §10); every figure is final.

**The slot moved golden once, by the ruled event R1** ([S8] §2.5; the ledger): E8 item 4a's
add-only emission (`53a1909`: **+124**, 17 317 → **17 441**, tier A 11 472 → **11 575**, tier B
5845 → **5866**; `golden_ref_diff.py --expect` set equality, `golden_explain.py` exit 0 with no
flags). **Registering `coefficient_ring` moved nothing** (WP-3: a fresh `GoldenEmit` byte-identical,
`ConsoleScriptEmit` no change). **Both determinism digests are unchanged from R0**, as predicted by
construction: `EngineDeterminismValidation` `0xe501ca19ee7815e1` (8 arms × 1279 records),
`HeckeExtDeterminismValidation` `0x03b4f07c14555fec` (printed `0x3b4f07c14555fec`), heavy
`0x498147a50c6c1e30`. `tau_table_p2.txt`, the 22 console transcripts, `cli_frozen/` and
`docs/matrix-engine/results/` are byte-identical to `3e7abbc`; `Hecke/HeckeReport.cpp` gained one
refusal line (WP-3), the emitted `hecke_report/v2` text did not move. Final `GOLDEN_STRICT=1`:
tier A 11 575 / 0, tier B 5866 / 0; `--all` 104 / 104 (10 `slow` skipped); `--all-full` 114 / 114.

Changelog:

* **§6.2 E8 — items 2 and 3 ACCEPTED, item 4a ACCEPTED (a/s), item 4b → slot 9** (§6.2 E8's v1.12
  note). Item 2 (WP-1 `9e02013`, merged `3ab190f`): the composite `ModCtx`, the §13.3 guards, the
  §13.7 replay check, `elim::howell` / `kernel_module` / `image_module` / `solve_multi_rhs_module`
  / `length` / `invariant_factors` (Smith step), `ref::howell`, `HeckeReductionValidation`. Item 3
  (WP-3 `9071ab0`, merged `99877a6`; the WP-3 × WP-10 follow-ups `06bebdc`; WP-3r `28fdb73`, merged
  `5d0b867`): the module routes of `EquivariantCohomologyOnK` and `HeckeOperatorOnK` over
  `Z/ell^k`, E8-P5's `ComputeSymmetricPowerMatrixRing`, the M3 basis rule, the certified `K`-mode
  (P2), `charpoly` on the free quotient at certified levels (P4), `coefficient_ring` registered with
  its refusal closure. Item 4a (WP-4 `d96d89d`, merged with R1 at `53a1909`): `Hecke/HeckeReduction`
  (the reductions and the Bockstein as map equalities, `higher_torsion_count`), the identity
  `bockstein_rank^0 + higher_torsion_count == dim H^0(F_ell)` on every stated cell, P3's controls
  exact (`(30, 5)`: `Z/25`; `(60, 5)`: `Z/25 ⊕ Z/5`), `HeckeReductionCoverageSlowValidation`
  (`slow`). **The Fable review** (WP-12): pass 1 on §13 ACCEPT (three pointer repairs, applied at
  this close); pass 2 on WP-3 ACCEPT AFTER REPAIRS (M-1 the basis-rule arm, M-2 the `U64_Wide`
  cast), both repaired by WP-3r before R1 froze the tier-B `red_H^q` hashes.
* **§6.2 E8 — the wording repairs** ([S8] §2.3 item 11, WP-1 scope 5): item 1 (i)'s field-only list
  drops `inv` (F1: unit-only); item 3's "`kernel_module` / `image_module` / `factor_basis`" reads
  "`kernel_module` / `solve_multi_rhs_module` / §13.6's `invariant_factors` with M3's basis rule"
  (`blk::` / `tape::factor_basis` declare a field by their signature); M1's arm is restated in
  §13.6's column convention (the `2 × 1` column `[[2], [1]]`, `image_module`'s pivots `(1, 1)`);
  the entry points `solve_multi_rhs_module` and `length` are adopted (m11); §13.7's decision is
  **the `ModCtx` overload** on `BlockMat` / `BlockBuilder`; `elim::howell` stays scalar (no blocked
  form was needed).
* **§1.5 — ELEVEN keys**: `coefficient_ring` registered (slot-8 WP-3) at the tail by the four-edit
  rule, grammar `F_ell | Z/ell^<k>` (`2 ≤ k ≤ 63`), **key-additive** (no golden line, no campaign job
  id); `Z` and `Z/<m>` reserved and **refused inside `set()`** by `NotImplementedInThisBuild`
  (the lead's default, decision 4 (A)); every other text `invalid_argument`. **Refusal first, over
  the closure** (decision 4 (A); [E] `sec:ring` (b1)): `EquivariantCohomologyOnK`,
  `HeckeOperatorOnK`, `HeckeReductionValidation` and the harness's E8 points honour a non-default
  ring; every other construction site refuses by name (exit 5), `refusal_arm()` has 36 members;
  `ell ∈ {2, 3}` is **refused under a composite ring** (the honouring context; [C]
  `prop:certifiede`'s scope clause); campaign and record support are slot 9's, with C5.
* **§1.5 — OD-10's cost line, narrowed to the grammar** ([S8] §2.3 item 4; ruling 6d): extending
  `coefficient_ring`'s grammar to admit `Z` costs **no** golden line (key-additivity, v1.11); the
  record keys OD-10 (a) adds (`q_max`, `truncated`, `q_max_source`, `object`) cost the 62
  `ext_json_*` lines and the ext digest **unless emitted only under `coefficient_ring = Z`**, which
  ruling 6d fixes. L2-4 stays add-only.
* **§0.4 C-A5, §6.2 E9, §6.3 R20, §5 `HeckeFreeModelValidation` — the line-2 re-cut** (rulings 6b,
  6c, 6d: [IB] OD-7 (a), OD-8 (a)). C-A5 is **DISCHARGED** by [C] v1.8.0 `sec:integral` (WP-9, an
  `X` bump, refereed on Fable: 0 B / 0 M / 6 m), re-scoped onto the **unrefined** `Xbulk`
  (`def:isomodel`, `prop:isomodel`, `rmk:cafive`; ranks `5, 14, 19` per `n + 1`, correcting [IB]'s
  `7, 18, 23`); OD-T1 is answered **"not needed"**. **E9 is absorbed into line 2**: items 1–2 →
  L2-1a on `Xbulk`, item 3 → L2-3, item 4's tests re-hosted ((1), (2), (6) in M0; (3), (4), (5) in
  M1(a); the `oc1c` report in L2-3). **R20 is retired** (there is no refinement). Line 2's phases
  and gates (§8, the slot-9 re-cut): **M-0 DONE** (WP-7), **V-B DONE** (WP-8), **L2-C DONE** (WP-9);
  L2-1a (0.5, gate L2-C — met); M0 (≈ 1.0, gates L2-1a and E8 items 2–3 — the latter met); L2-1b
  (1.0, gate M0); M1 (0.75: M1(a) basis-free after L2-1b; M1(b) integer matrices, additionally
  OD-11 (a) and OD-3); L2-3 (1.0, gate M1(a)); L2-4 (0.5, gate M1(a), OD-9, OD-10). E9's 2.5 AU are
  absorbed; line 2's core is ≈ 5.0 AU, net ≈ 2.5 AU over v1.11.
* **E8 item 4b is recorded** (decision 3 (A)): the boundary and the cone over `Z/ell^k`,
  `obl:coneexact`(iv)'s "over `Z/ell^e` by a solve exhibiting each kernel generator as an image"
  (the non-field half, still unchecked in [C]), ≈ 0.35 AU, **slot 9**.
* **The ext pass** (WP-5, WP-6, WP-6b, WP-L1). **WP-5** (`bf5e6b7`): the between-cells program-cache
  release (`Campaign/ProgramCacheRelease`, thresholds 512 / 2048, `malloc_trim`), in the ext pass,
  the job loop and `--atlas`; [KI] §4c **RESOLVED** (open item 1 of v1.11 closed);
  `ProgramCacheReleaseValidation`. **WP-6** (`f66b5e0`): `ext_jobs` cells at once under
  memory-aware LPT admission (`ext_memory_mb`, default 40 000), both scheduling-only, the
  `EXT_PASS` timing line; byte identity serial vs parallel on `ext_compare_mini.spec`, a
  non-default-setting arm and `HeckeExtCampaignValidation` arm 10; the engine `g_stats` and
  `PredicateStats` counters race-free (per thread); the in-cell profile report with levers L1–L5.
  **WP-L1** (`5c70e95`, **owner-approved 2026-09-24**, "adopt in slot 8"): route 2's program-cache
  key rank from a Fenwick tree instead of `std::distance` over the `ops2` map, keys bit-identical;
  `U_10007` at `n = 0` **256 s → 8.7 s** (indicative), which changes T-P's premise (W_ser ≈ 3500 s
  → a few hundred seconds). **WP-6b** (`735c571`, the owner's optional addition, a/s, **accepted**):
  the opt-in synchronous CPU + GPU cell dispatch (`ext_gpu = off | on | force`, `ext_gpu_cells`),
  `engine::tape::ScopedThreadDevice` (a thread-local device override), records bit-identical (also
  under `-DENGINE_VERIFY_DEVICE=ON`); **measured no speed-up** (indicative: ≈ 9 % slower on the mini
  spec), so **`ext_gpu` stays `off`**. **T-P** (decision 7): serial 292.4 s, parallel 55.4 s, ratio **0.1896**, records identical, RSS 2.2 / 9.3 GB, GPU arm 57.4 s; **reported as measured, not judged against 0.35** (owner ruling 2026-09-24: after WP-L1 the serial pass is ≈ 5 min); WP-6's post-L1 prediction was ≈ 0.13–0.2.
* **C4 DONE** (WP-10 `e8aeeb4`): [P] §10 C4 (a)–(c) met (`ConsoleDeterminismValidation`'s
  threads × program_cache × device product, one digest `0xf6ed04bbe8e6b60a`; `ConsoleErrorValidation`,
  `fast`, 107 checks at the close; `cross_config.sh` over the console names; CheckThread), (d)
  T-C4 0.311 s against 5 s, MET (W3); `docs/console/console.md` generated by
  `help_markdown()`. `ConsoleDeterminismValidation` **stays `standard`** (≈ 20–30 s; the lead's
  default on WP-13's item 2, the referee concurring).
* **Carries.** WP-11a (`7f62ad0`): `standing_gate_h2h.sh` prints `abs_gate=` / `ratio_guard=` /
  `verdict=` and gates on `--gate`. WP-11b (`19d235b`): `resume_u_ell` stamps `source = spec` in the
  campaign (decision 9 (A)); [KI] §4d RESOLVED (open item 2 of v1.11 closed). The F-A remark
  `rmk:bocksteinexp` beside `cl:bockstein` (decision 10 (A), in WP-9).
* **Documents.** [E] **v1.9.0-pre.1** (WP-2, before WP-3 registered the key) → **v1.9.0** (WP-13)
  → **v1.9.1** (WP-13's Fable referee: 0 B / 2 M / 7 m, repaired). [P] **v3.6** → **v3.6.1** (same
  referee). [C] **v1.8.0** (WP-9, `X`) → **v1.8.1** (WP-14, `Y`: the WP-9 referee's m-1 … m-5, the
  changelog's v1.7.2–v1.7.4 entries and hashes, status). `ENGINE_API.md` §13 amended (WP-1),
  reviewed (WP-12), its pointers repaired (WP-14). [X] **v1.12** (this).
* **The standing gates** ([OD] S7-G, with WP-11a's `--gate`): hecke 256 0.4393 s / 0.994, decomp 128 0.0967 s / 0.983, both MET, against a `3e7abbc` binary; T2 MET (0.4746 / 1.0049); R-E8 0.177 / 0.361 / 0.900 s (reported). Indicative in-slot runs (WP-3, WP-6b, WP-L1): ratio
  guard met throughout (0.956–1.011).
* **Not changed**: everything else; the v1.11 changelog below stands, except where this version
  supersedes it (§6.2 E8's "PENDING OWNER", C-A5's slot-8 scheduling, E9 as written, R20, open items
  1, 2, 8, 9, 10 of v1.11).

**Open items at the slot-8 close** (owner items are **recorded, not ruled**):

1. **T-P's verdict** (W1) and **the standing gates** (W3) are the lead's windows, not yet run at
   this version's writing. W1 should run on a binary with L1 (it does: `5c70e95` onward).
2. **C5 + the Core batch** (slot 9): the console's `set`-statement error position (the one
   `file:line:col` exception) and **a legal but unexecutable `--set` value → exit 5** (today
   exit 1; the lead's default, with C5, [P] v3.6.1 §6), decided and implemented in one Core edit.
3. **E8 item 4b** (slot 9, above).
4. **L2-1a** (slot 9; its gate L2-C is met): `R`, `R_∂`, `ε` on `Xbulk`, with the ranks `5, 14, 19`
   (not [IB]'s); [IB] §2.5(b) / K10 / §1.4 need the same correction at their next touch.
5. **WP-6b's findings 2–3** (pre-existing, value-free): the elimination driver ignores the
   process-wide `ScopedPassOptions` override (`TapeElim.cpp` calls `from_env()`), so the console's
   `set device` / `set batch` and the determinism arms never reach the per-panel programs; and
   `HeckeExtDeterminismValidation`'s `device = gpu` arms set only `PassOptions::policy`, so their
   programs share cache slots with the CPU arms. Each fix is a behaviour change (cache keys, never
   a value): slot 9, for the owner.
6. **`PerformanceSmokeValidation`'s speed floors on non-`NDEBUG` builds**: under `Check` the GEMM
   floor (4.0 Gmodmul/s) misses on an unchanged checksum, pre-existing at R0 (WP-1 §5, WP-3). The
   validation should skip its floors when `NDEBUG` is unset. Slot 9.
7. **`[C]` `rmk:bocksteinexp`(2) at every `ell`** — at [C]'s next `X` bump (the lead's default on
   the WP-9 referee's recommendation): clause (2) only; (1) and the summand count stay at `ell ≥ 5`.
   **Part VI's placement is kept.**
8. **WP-6's in-cell levers L2–L5** (L1 shipped): reported, not scheduled (decision 7 (A)); a second
   ext campaign under the parallel pass is not scheduled.
9. **Minor, recorded.** `EquivariantCohomologyOnK::get_prime()` returns `ell^k` on a composite
   object (WP-12 m-10); `RunPipelineModEll (Integral)` refuses structurally, not by a named guard
   (WP-12 m-5); the re-baseline note's header still says "CANDIDATE" (landed at `53a1909`, the
   ledger records it).

### `[OD]` — the owner rulings of slot 8, as a register

Source: [S8] §10 (2026-09-24: "all at recommendation (and include optional synchronous CPU + GPU
parallelism for cells)"), the owner's instructions during the slot as relayed by the lead, and the
lead's defaults (marked).

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S8-1** | Scope **(A)**: 4.60 AU must-accept + WP-4 (E8 item 4a, a/s, 0.50) + 0.10 contingency, ceiling 5.20 AU; + WP-6b (optional, 0.25), ceiling incl. optional 5.45 AU | WP-1 … WP-14, WP-3r, WP-6b, WP-L1 |
| **S8-2** | E8 strategy **(A)**: P1–P5 adopted (P1 per `ENGINE_API.md` §13, §13 wins; P2 the Bockstein bookkeeping identity; P3 the controls `(30, 5)`, `(60, 5)`; P4 `charpoly` only at a certified `(cell, K)`; P5 the `ρ_n` repair) | §6.2 E8 (v1.12 note); WP-1, WP-3, WP-4 |
| **S8-3** | E8 item 4 **(A)**: split — 4a (a/s) in slot 8, 4b (boundary and cone) to slot 9 | 4a accepted; 4b recorded (above) |
| **S8-4** | `coefficient_ring` **(A)**: refusal first over the grep-derived closure (exit 5, named), grammar `F_ell \| Z/ell^<k>`, `Z` reserved; E8 golden objects console-unreachable in slot 8; campaign / record support in slot 9 with C5 | §1.5; WP-3; [E] `sec:ring` (b) |
| **S8-5** | R1 **(A)**: predicate-gated, seven `E8 ring=…` points, primes `{2, 3, 5}` at `(10, 691)`, `{2, 3}` at `ell = 5`; tier A / B as decision 5 (A); both digests unchanged by construction | R1 `53a1909`; the ledger |
| **S8-6a** | Line 2 **(A)**: M-0 (WP-7) and V-B (WP-8) in slot 8 | `HeckeIntegralCharpolyValidation`, `HeckeBredonTreeValidation` |
| **S8-6b** | L2-C **(A)**: must-accept, at [IB]'s OD-1 / OD-2 / OD-8 / OD-12, no arbitrary-precision re-scoping | [C] v1.8.0 |
| **S8-6c** | C-A5 **(A)**: re-scoped into L2-C on the unrefined `Xbulk`; OD-T1 "not needed"; [X] v1.12 rewrites E9, C-A5, R20 | §0.4, §6.2 E9, §6.3 R20, §5 (this version) |
| **S8-6d** | [IB]'s OD-3 (c), OD-4 (a), OD-6 (a), OD-7 (a), OD-9 (a), OD-10 (a) (record keys only under `coefficient_ring = Z`), OD-11 (b) / (a) confirmed; WP-9's referee verifies [IB] §8 | [C] v1.8.0; §1.5 (OD-10's cost line) |
| **S8-7** | T-P **(A)**: `W_par / W_ser`, same binary, one window, `sweep_full.spec` ext on, one pair (a second if within 10 %), constant **≤ 0.35**; the in-cell profile a report only | W1 (`slot8_w1_window.sh` → `ext_pass_tp.sh`) |
| **S8-8** | C4 / C5 **(A)**: C4 in slot 8, C5 in slot 9 binding E7's and E8's types | WP-10; §8 slot-9 row |
| **S8-9** | `resume_u_ell` stamp **(A)**: `spec` | WP-11b |
| **S8-10** | F-A remark **(A)**: beside `cl:bockstein` in WP-9's [C] pass | `rmk:bocksteinexp` |
| **S8-11** | Windows **(A)**: W1 and W3 with the owner; W2 (Σ(691) with the hook) optional, overnight | `slot8_w1_window.sh`, `slot8_close_window.sh` |
| **S8-+** | **WP-6b**, synchronous CPU + GPU parallelism across cells, opt-in, accepted-if-shipped | shipped, **accepted, no speed-up, `ext_gpu = off`** |
| **S8-L1** | **WP-L1 adopted in slot 8** (2026-09-24): route 2's key rank in `O(log)` | `5c70e95`; `U_10007` `n = 0` 256 s → 8.7 s |
| **S8-D1** *(lead default)* | `coefficient_ring = Z` (and `Z/<m>`) **refused inside `set()`** by `NotImplementedInThisBuild` | WP-3; [E] v1.9.1 |
| **S8-D2** *(lead default)* | `ell ∈ {2, 3}` **refused under a composite ring** | `CoefficientRingContext`; [C] `prop:certifiede` |
| **S8-D3** *(lead default)* | `ConsoleDeterminismValidation` **stays `standard`** | WP-13 item 2 |
| **S8-D4** *(lead default)* | a legal but unexecutable `--set` value → **exit 5, with C5** (exit 1 until then) | slot 9 |
| **S8-D5** *(lead default)* | `rmk:bocksteinexp`(2) stated for every `ell` at [C]'s next `X`; **Part VI's placement kept** | open item 7 |


**Version 1.11 — 2026-09-23. Slot 7 close ([S7] WP-14): E7 accepted and emitted add-only, the
one staged re-baseline landed in seven explained commits, the root finder fixed, E6 declared, the
first ext campaign published, C2b and E8 item 1 done.** Sources: the slot-7 plan
`hecke_extensions_slot7_plan.md` [S7] (revision 2, its audit [S7A] and the owner's rulings of its
§10), the package records (`git log d7f1549..79b178f`; WP-10's review and WP-13's referee in
`docs/implementation/slot7/`, WP-7's `WP-7_e6_dossier.md`, WP-4's `WP-4_rmax_ell691.tsv`), the two
re-baseline notes `docs/matrix-engine/rebaseline-2026-09-23-e7-addonly.md` and
`…-hecke-ext-staged.md`, the lead's windows W1 and W2, the Fable E8 investigation
`docs/implementation/e8_ladic_investigation.md` (merged `c9829a9`), and the close report
`docs/implementation/slot7/WP-14_report.md`. Every figure is final: the gate results
since the close's commit 2, W3's since 3a, W4's since 3. No phase changes its mathematics.

**The slot moved golden on purpose, eight times, each move a ledger event** ([S7] §2.5; the close
report §2 quotes the ledger): **stage 0**, E7's add-only emission (R1 `596a47b`: **+651**,
16 666 → **17 317**, tier A 10 914 → **11 472**, tier B 5752 → **5845**, explain exit 0 with no
flags); **stage 1 (1)**, the path-scoped `settings → {fingerprint}` recipe (R2 `97dbf9b`: the 62
`ext_json_*` lines, allow-list the eight `settings.<key>` paths), with **stage 1 (2)** at zero
movement; **stage 2**, items 3–7, each owner-signed on its `golden_ref_diff.py` sets (R3a
`7932c6e` … R3e `d28f7b4`); **stage 3**, the schema string `hecke_ext/v2 → hecke_ext/v3` (R4
`9f4ea8d`, allow-list `schema`). **One value changed**: item 3 flips golden cell `(24, 5)` ideal 1
`final true → false` (`sturm_heuristic`), with `ext_ideals` / `ext_certify` there — slot-6 WP-9's
predicted flip. Everything else the stages changed is record **text**. `hecke_report/v2`,
`tau_table_p2.txt` and `Hecke/HeckeReport.{h,cpp}` are byte-identical to `ff68c55`; the 21
pre-existing console transcripts and `cli_frozen/` are unchanged. **Both determinism digests are
re-pinned once, bare**: `EngineDeterminismValidation` **`0xe501ca19ee7815e1`** (8 arms × 1279
records), `HeckeExtDeterminismValidation` **`0x03b4f07c14555fec`** (printed without the leading
zero, `0x3b4f07c14555fec`), its heavy cell `(128, 5)` **`0x498147a50c6c1e30`**; every intermediate
value is in the ledger with its argument. Final `GOLDEN_STRICT=1` on the close tree:
tier A 11 472 / 0, tier B 5845 / 0; `--all` 99 / 99, `--all-full` 108 / 108.

Changelog:

* **§6.2 E7 — ACCEPTED** (WP-1). (a) green; (b) `cl:pd`(1)–(2) hold on **all 54 cells of the E2
  case list at `ell ≥ 5`**, coverage stated (E7b's 20; `HeckeDualityValidation` arm A16 on 34 —
  102 / 102 cone and 68 / 68 circle pairs perfect, 272 PD-gate pairs failing 0, 106 / 106 twisted
  controls rejected; the new `slow` `HeckeDualityCoverageSlowValidation` on `(58, 7)`, `(58, 5)`,
  `(82, 7)`; `(160, 691)` and `(198, 691)` read-only under `HECKE_DUALITY_COVERAGE_LARGE=1`, 40 gate
  pairs failing 0) — no finding against [C]'s OPEN `cl:pd`, which stays OPEN; (c) discharged in
  slot 6. **The stage-0 emission is made** (R1).
* **§1.5 — TEN keys; registration is key-additive since stage 1.** Stage 1 (1) reduces the record's
  **top-level** `settings` member to `{fingerprint}` in every golden text and in
  `HeckeExtDeterminismValidation` (decision 2 (ii)) — a depth-1 member walk, not `RedactJsonKeys`,
  so the top-level `u_ell` verdict is untouched. Proven additive by a scratch arm that registered a
  dummy key at its default: `GoldenDump`, the emitted reference and the ext digest byte-identical.
  Stage 1 (2) registered **`presentation`** (`off | on`, consumer shipped: the per-ideal
  `presentation` object of [E] `sec:schema` (e), `verify()` code 24) and **`predictions`**
  (`annotate | assert`, consumer `predictions_mode`, item 7) at zero golden movement. The
  **source argument** ships: `ScopedUEll(u, src)`, `ScopedMathSettings(s, src)`; the golden
  harness stamps **`spec`** (confirmation 13). Only a setting *in force* moves a golden text now,
  through `settings.fingerprint` (rule 1). `coefficient_ring` (E8) will cost no golden line.
* **§1.6 — the recipe, and "E1–E9 add entries only" settled.** The golden `ext_json_*` texts see
  `{"fingerprint": …}` in place of the key list. After stage 3 the default record is
  `hecke_ext/v3` with nine keys more than v2 (`anemic_pool`, `s_sep`, `label`, `split`,
  `predictions_mode`, `predictions`, `predicted`, `confirmed`, `unpredicted`); E8 and E9 add
  entries, and a key they register moves nothing at its default.
* **§6.2 E2 — COMPLETE** (WP-2, WP-6, W3). (a) **in full**: `HeckeExtCampaignValidation` arm 8
  **asserts** `ext_json_canonical` and `ext_json_full` equal to the reference at `(10, 691)` and
  `(4, 13)`, and the campaign's full `settings` block equal to the harness's; the `presentation`
  key and its hash-invariance arm (`HeckePresentationValidation` (k1)–(k5)) shipped. **(e′)**:
  `c = 1.25` **confirmed by the owner before the measurement** (decision 5 (B)); `T_cell` is the
  campaign cell's own computation (`--bench ext … --campaign-cell [--u-ell V]`, WP-6), over the
  cells the ext pass drove, three pairs, base `sweep_full.spec`: **MET in W3** — `W_ext − W_0 =
  3504.27 s` against `1.25 × Σ T_cell = 4209.10 s` (ratio **1.041**), 189 cells; the old (e) text
  is a recorded MISS (1048×), superseded.
* **§6.2 E6 — DECLARED, item by item** ((a)–(d) met; §6.2 E6's v1.11 note). **(d)'s cell list and
  failure rule are written into (d)**: the 23 cells plus every first-campaign cell with
  `canonical_field_r_max ≥ 10` in `WP-4_rmax_ell691.tsv` (**the threshold 10 is pinned here**:
  it was WP-4's reading of ruling 4's "highest-`r` cells", [E] v1.8.1 m-2), 41 gating cells;
  `(210, 691)` and `(256, 134217757)` reported only; rule **(Z)** replaces the automatic flip.
  **W1's verdict: MET**, worst gating cell `(170, 691)` at **0.0104**; **W4 confirms** (41 / 0,
  worst `(170, 691)` 0.0107).
  **Process deviation, recorded** ([S7] §4.3; WP-13 m-6): the list was to be written into [X] by
  the lead **before** W1; it was pinned before W1 by the committed table and `e6_measure.sh
  --cells-from` (`cab4e38`) and by ruling 4 in [S7] §10, but [X] stayed at v1.10 until this close.
  **The root finder**: WP-4's operation count gave verdict (ii) — the route sat at its own
  `O(r^5 log ell)` `F_ell`-multiplications, no defect; the fix (the Frobenius as a precomputed
  `F_ell`-linear map, a flat quotient-ring product) takes `r = 19` from 144.1 M to 12.1 M
  (`ell = 691`), every value exact and every `hecke_canonical_split/v1` text byte-identical.
  **`conway`** raises `NotImplementedInThisBuild` from every production entry point (open item 4 of
  v1.10, closed). **The first ext campaign is published** (`results/ext_first/`, 505 cells,
  0 failed, W2) with `analysis.txt`; Σ(691) by hash and build command only (owner amendment to
  confirmation 14).
* **§6.2 E8 — item 1 DONE and reviewed; the findings disposed of** (§6.2 E8's v1.11 note): F1
  (`inv` unit-only), F2 (Smith step), F3 (module / map equalities), **F4 / M2 as an implementation
  limit** (`ρ_n` is integral; the current builder is prime-only), M1 (the `[[2],[1]]` arm), M3
  (the cyclic-basis rule), and the entry points `solve_multi_rhs_module` and `length`. **E8's
  strategy investigation is delivered** (Fable, `docs/implementation/e8_ladic_investigation.md`,
  merged `c9829a9`); its six recommendations are recorded as **proposals E8-P1 … P6, pending the
  owner**: build direct per §13 (u32 below `2^32` at `F_ell`'s cost below `2^30.5`, u64 to
  `2^63`); the certified `K`-mode with `bockstein_rank^0 == dim H^0(F_ell)` and
  `higher_torsion_count`; the positive controls `(30, 5)` and `(60, 5)`; `charpoly` over
  `Z/ell^k` on the free quotient; the `ρ_n` repair (unit fast path, division-free Pascal oracle,
  `diag(ell, 1)` split for `U_ell`); and the `ell`-adic induction (C2) — **restated by the owner
  (2026-09-23) from the investigation's "non-goal" to a deferred future requirement (arbitrary
  `k`, Hida), design recorded**, a slot-8+ line item. **Owner direction, 2026-09-23: two
  computational lines in one tree** — line 1 truly mod `ell^k` at word size for all arithmetic
  including the Hecke action (E8 builds on it), line 2 truly integral over `Z` (`Z[1/6]` on the
  current model, `Z_2` / `Z_3` on a finer orbifold model, glued by descent); line 2's design brief
  `docs/implementation/integral_line_design_brief.md` is incoming (then a Fable audit), not
  pre-empted here.
* **The standing gates, restated by the owner at the close ([OD] S7-G)**: `hecke 256 ≤ 0.470 s`
  (was 0.460 s) plus a paired-ratio guard (median NEW/REF ≤ 1.04 against the previous slot's
  reference binary); W4 meets both gates under it (0.4604 s, ratio 0.999; `decomp 128` 0.1003 s,
  ratio 0.991). W4 also confirmed E6 (d) (41 / 0), T2 (1.0257 / 1.0065) and 21 / 21 digests.
* **§8 — the slot-7 outcome and the slot-8 re-cut.**
* **Documents.** [E] **v1.8.0-pre.1** (WP-12a, spec first: `sec:schema` specified every stage-2
  key before WP-3 emitted it) → **v1.8.0** (WP-12) → **v1.8.1** (WP-13, referee, `Y`) →
  **v1.8.2** (WP-14, status). [P] **v3.5** (WP-12; accepted as written by WP-13) + the slot-7 close
  status block. [C] **v1.7.4** (WP-14, status only). `ENGINE_API.md` §13 (WP-9, reviewed by
  WP-10). [X] **v1.11** (this).
* **WP-10's proposals (3)–(8) of v1.10 are ADOPTED** ([S7] §10 decision 7 (A)), and bind from this version
  as stated here (no clause text elsewhere is rewritten): (3) the driver head-to-head rule (`ext_driver_h2h.sh`, median `total_s` NEW/REF
  `≤ 1.04` at `(10, 691)` and `(160, 691)`, `ext_s` gated only at `(160, 691)` and only if its REF
  min `≥ 1 ms`) is **standing** for driver packages; (4) `ENGINE_THREADS=16` is part of E1 (d)'s
  and E6 (d)'s pinned invocations; (5) E5 (d)'s reduction is "five interleaved rounds, met iff the
  **median** per-round ratio `≤ 2.0`, the worst cross-pairing reported"; (6) §5's "`--all` grows by
  ≈ 40 s" is an estimate, not a bound; (7) an acceptance clause that repeats the `u_ell` admitted
  range means "where `UEllDecision` admits it"; (8) `docs/matrix-engine/campaign.md` §10's
  wall-clock estimates are pre-Phase-4/5, superseded by §13.
* **Not changed**: everything else; the v1.10 changelog below stands, except where this version
  supersedes it (§1.5's "registering any key moves 62 golden lines", §1.6's pending events, E6's
  open verdict, E7's pending acceptance, E2 (e′)'s unconfirmed constant, and v1.10's open items 1,
  3, 4, 5, 7, 9).

**Open items at the slot-7 close** (owner items are **recorded, not ruled**):

1. **The engine's process-wide program cache is unbounded** (WP-5, WP-7) — now also the
   prerequisite of the owner-requested **ext-pass parallelism** candidate (§8, slot-8 re-cut). The Σ(691) build's RSS
   grows ≈ 16 GB across cells and the ext pass never releases RSS (6.87 GB at its end, peak
   10.35–10.58 GB in the job loop). `HeckeExt` cannot clear it (`check_heckeext_includes.sh`
   forbids `Engine/`); the repair is a between-cells hook in `kernel.cu` / the campaign driver.
   Bounded at this scale. [KI] §4c.
2. **`resume_u_ell` in the campaign stamps `source = "console"`** (WP-2): `CampaignExt.cpp:515`
   scopes `ScopedUEll(u_old)` with the default source; `spec` is arguably right. A settings-text
   item, not a value (fingerprint `0`). [KI] §4d.
3. **E2 (e′)**: **MET** in W3 (1.041 against `c = 1.25`). Independently of it, the owner requested (2026-09-23) the
   **ext-pass parallelism** candidate for slot 8 (§8's re-cut): W3 showed one thread busy and 32
   idle through the whole ext pass (3771 s / 3508 s per `ext = true` `sweep_full` run).
4. **The default path's new cost at `ell ≤ 13`** (WP-3, reported, never gated): the cell-local
   `proof_range` and the in-process atlas label compute the anemic pool (7–8 streamed `T_q`) at
   every `ell ≤ 13` cell — ext cells ≈ 0.12 s against ≈ 0.015 s; the golden run ≈ 5.7 → ≈ 12.5 s
   (stage 0) → ≈ 16–18 s emit wall (stage 2); `EngineDeterminismValidation` ≈ 2.3 → ≈ 4.6 s.
   W4: golden 13.9 s, `EngineDeterminismValidation` 4.9 s, `--all` 308 s, `--all-full` 590 s. Not paid at `ell ≥ 691`: T2 MET (WP-3,
   indicative: medians 1.0270 / 0.9781).
5. **Identity 6 is not evaluated at `ell = 691`**: Σ(691) exists (WP-5) but is not published and
   not built in any validation; the record carries `atlas_unavailable` there by ruling 3b (B). A
   validation over the published store's hash is an E6 follow-up, not an acceptance item.
6. **The ell = 691 tangent pairs are deferred** beyond `n = 1000` (every cuspidal system); the
   `ell ≤ 31` scope of [E] Stage 6 is met at `ell ∈ {5, 7, 11, 13}`.
7. **Minor.** `HeckeInvolution`'s consumer tag `"hecke_ext/v2"` deliberately left (it names the
   family, not the schema key); `streamed()` versus `pool_streamed()` (item 5) keeps
   `HeckeExtRamanujanValidation` arm 3's pin on the Sturm route; `HeckeCanonicalFieldValidation`
   arm H costs ≈ 0.5 s in a `fast` name; `HeckeDualityCoverageSlowValidation` stays `slow`
   (≈ 28 s, the lead's ruling).
8. **C-A5** — deferred to slot 8 (decision 8 (B)); it gates E9.
9. **E8's strategy** — the Fable investigation is delivered (`e8_ladic_investigation.md`,
   `c9829a9`); proposals E8-P1 … P6 (§6.2 E8's v1.11 note) are **pending the owner**, before E8
   item 2 starts. Its finding F-A (`ell²`-torsion at `n = ell · m`, unbounded exponent along
   `n = ell^j m`) is a candidate remark for [C] `cl:bockstein`. P6 is restated by the owner
   (a deferred future requirement, not a non-goal).
10. **The integral line (line 2)** — owner direction of 2026-09-23: its design brief
    `docs/implementation/integral_line_design_brief.md` is being written, then audited on Fable;
    incoming, not pre-empted by this version.

### `[OD]` — the owner rulings of slot 7, as a register

Source: [S7] §10 (2026-09-23) and the owner's instructions during the slot, as relayed by the lead.

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S7-1** | Scope **(B)**: 5.20 AU must-accept + 0.10 contingency, ceiling **5.30 AU**, no WP-15 | the slot ran WP-1 … WP-14 and WP-12a |
| **S7-2** | Gating **(B)**: stages 0, 1 (1) and 3 land on their `golden_ref_diff.py` predicate; each stage-2 item owner-signed; `HeckeExtDeterminismValidation` takes the same `settings` reduction | the ledger; R2 moved the ext digest once for the recipe |
| **S7-3a** | `proof_range` **(A)**: cell-local at every golden cell, `ell ≥ 691` included, measured first | item 3 (R3a); 0 flips at `ell ≥ 691` (`H^0 = 0` there) |
| **S7-3b** | Atlas labels and `S_sep` at `ell ≥ 691` **(B)**: `atlas_unavailable`; golden self-contained | items 4, 5 |
| **S7-4** | E6 (d): cells **(C1)** = the campaign's highest-`r` cells, gating; `(210, 691)`, `(256, 134217757)` reported; rule **(Z)**: a W1 miss goes to the owner, never flips automatically. **During the slot: "highest-`r`" = every campaign cell with `r_max ≥ 10`** | §6.2 E6 (d) (this version); W1 MET |
| **S7-5** | E2 (e′) **(B)**: `c = 1.25` confirmed; `T_cell` the campaign cell's own computation; `--repeat 1` above 60 s; **three pairs**; W3 its own session. **During the slot: W3 runs on `sweep_full.spec`** | §6.2 E2 (e′); W3 |
| **S7-6** | Transcript 014 **(A)**: kept; [P] (h)'s no-op restated at engine level | [P] v3.5 |
| **S7-7** | WP-10's proposals (3)–(8) **(A)**: adopted | changelog above |
| **S7-8** | C-A5 **(B)**: deferred to slot 8 | §8 |
| **S7-9 … 15** | Confirmations at their defaults: campaign spec; the schema-bump rule; no LMFDB lookup; C4 to slot 8; the harness stamps `spec`; atlas stores copied into `results/` with the guard kept; `presentation` uses block-basis indices. **Amendment to 14 during the slot: Σ(691) is published as a hash + pointer only** | WP-2, WP-3, WP-7 |
| **S7-items** | **Stage-2 items 3–7 signed** (2026-09-23), each on its sets; **the item-7 reading of [E] `sec:schema` (d) confirmed** | R3a–R3e |
| **S7-F** | **Audits, reviews and referees run on Fable** from now on (supersedes [S7] §10's "Fable: none") | the E8 strategy investigation |
| **S7-F4** | F4 / M2 is an **implementation** limit: `ρ_n` has integer entries and reduces mod `ell^k`; the Lucas / factorial tables and the division by `a` / `b` are the current code's, valid only mod a prime | §6.2 E8 (this version) |
| **S7-2L** | **Two computational lines in one tree** (2026-09-23): line 1 truly mod `ell^k` at word size for all arithmetic including the Hecke action (E8 builds on it); line 2 true integral computation over `Z` (`Z[1/6]` on the current model, `Z_2` / `Z_3` on a finer honest orbifold model, glued by descent, the Hecke action over `Z` at the end). **And `mod ell^k` for arbitrarily large `k`** (the descent; Hida families): the investigation's (C2) is **not** a non-goal — E8-P6 restated as a deferred future requirement, design recorded | §6.2 E8 (v1.11 note), §8 slot-8+ rows; line 2's design brief `docs/implementation/integral_line_design_brief.md` **incoming** (then a Fable audit) |
| **S7-G** | **The standing gates, restated at the slot-7 close** (2026-09-23): W4 measured `--bench hecke 256 134217757 2` at **0.4604 s** against `≤ 0.460 s` (`OVER_GATE` by 0.1 %), the REF `d7f1549` binary at 0.4638 s in the same 13 rounds, paired median ratio **0.999**, the window opened at load 6.8 / 11.1 / 14.2; the owner declined a quiet re-run (the box in use). **`hecke 256` gate loosened to `≤ 0.470 s`**; **a paired-ratio regression guard added**: median NEW/REF per-round ratio `≤ 1.04` against the previous slot's reference binary, on both standing benchmarks. `decomp 128 ≤ 0.109 s` unchanged | CLAUDE.md's standing gates; [S7] §2.4 T1 superseded for later slots; W4 then MEETS both gates (0.4604 s, ratio 0.999; 0.1003 s, ratio 0.991) |


**Version 1.10 — 2026-09-22. Slot 6 close ([S6] WP-14): E7a and E5's cross-routes shipped, the
PD gate asserted, E2 declared item by item, the E6 gate restated and moved into §6.2 E6 (d), and
the record text held frozen.** Sources: `docs/implementation/slot6/` (the WP-2, WP-7, WP-8, WP-9,
WP-10, WP-12 and WP-13 reports and the close report `WP-14_report.md`; WP-1, WP-3, WP-4, WP-5,
WP-6 and WP-11 are recorded by their commit messages, `git log 38a5240..a8cc49a`), the slot-6
plan `hecke_extensions_slot6_plan.md` [S6] with its audit and the owner's rulings of its §10,
`docs/implementation/e6_gate_brief.md` [BR6] with its two owner decisions E6-1 / E6-2, and the
close's own gate run. No phase changes its mathematics.

**The slot moved no golden value and emitted no golden entry.** `git diff --stat bd84016 --
'*GoldenReference.inc'` is empty; `GOLDEN_STRICT=1 GoldenRegressionValidation` gives tier A
10 914 / 0 failing and tier B 5752 / 0 mismatching (16 666 objects); `EngineDeterminismValidation`
reads `0xa81480950dffb0d2` on all 8 arms; `docs/implementation/tau_table_p2.txt` and
`Hecke/HeckeReport.{h,cpp}` are byte-identical to `bd84016`; **no mathematical-settings key was
registered** (`MathSettings::keys()` still has eight). The one printed digest that moved is
`HeckeExtDeterminismValidation`'s, **once**, by WP-6's `commit` redaction: it is now
**`0xfb71e225e4185be7`, reproducible bare** — the `digest@SHA` convention of v1.9 is retired for
it (it stays harmless for `EngineDeterminismValidation`, which never carried a commit).

Changelog:

* **§6.2 E6 — acceptance item (d) is INSERTED** ([OD] E6-1 / E6-2, [BR6] §6.1's text verbatim;
  §2.2 Stage 6 and §0.3 are re-pointed at it, so the gate has **one** authoritative statement).
  The gate is `canonical_field_s ≤ 0.10 × total_s` on the 23 cells, protocol pinned; the
  `≤ 2 × own_field_s` half is deleted and `own_field_s` is a reported column. **The owner's
  measurement condition is discharged**: (a) `(10, 691)`'s `total_s` and (b) cells with
  `canonical_field_r_max ≥ 11` were measured in the lead's quiet window — see §6.2 E6 (d)'s v1.10
  note for the figures. **Verdict on the 23 cells: 23 / 23 MET** in the closing window (worst `(198, 691)`
  0.0315; `(10, 691)` `total_s` 0.7168 s, ratio 0.00002). **Off the list, both high-`r` cells fail the bound**: `(210, 691)` at
  `r = 14` gives **0.264** and `(256, 134217757)` at `r = 19` gives **1.119** (closing window;
  0.262 / 1.14 in the early one). [BR6] §6.1's headroom argument ("fires at roughly `r ≤ 13–14`") is therefore
  **refuted as a safety margin**, and slot-6 WP-8 located the cost: root finding
  (`FindCanonicalRoot`, `alg:split` step 1) is **≥ 96 %** of it at every `r ≥ 10`, growing
  ≈ `r^5`–`r^6` between `r = 14` and `19`, against the `O(r^3 log ell)` of [E] after `alg:split`.
  **E6 is not declared** (it is slot 7's, §8). **Owner ruling of 2026-09-22 ([OD] E6-3, at the
  recommendation)**: a **small slot-7 package diagnoses and fixes the canonical-field root finder**
  (`FindCanonicalRoot`); meanwhile **`split_field_report = canonical` stays the default and the
  gate text is unchanged**; **E6's gate verdict stays open until after the fix**, and **the gate's
  cell list gains a high-`r` cell** (written with the fix, slot 7).
* **§6.2 E2 — DECLARED, item by item** (slot-6 plan §1.3 item 4; §6.2 E2's v1.10 note has the
  evidence): **(a) MET, with the `ext_json_*` clause booked with the source fix** —
  `HeckePresentationValidation` built (WP-2) and `HeckeExtCampaignValidation`'s golden arm
  implemented over the settings-independent ext objects (`ext_ideals`, `ext_certify`,
  `sturm_bound`; WP-6, owner ruling 5); **(b)–(d) and M1 re-verified** on the close tree;
  **(e) measured in the lead's window under ruling 2's protocol (A) with ONE pair (`--pairs 1`)
  instead of three — a recorded deviation, owner ruling of 2026-09-22 ([OD] S6-2″): WP-10 predicts
  a ≈ 680× miss, so the verdict cannot depend on the sample count: **MISS — `W_0` 2.990 s,
  `W_ext` 3106.6 s, ratio 1039 against 3.0**; the ext pass is 3103.75 s of it (157 `u_ell`
  cells), the job loop 2.8 s** — WP-10 predicted a miss by ≈ 680× (a lower bound: nine
  `U_10007` cells at ≈ 356 s each, run sequentially, against a `3 × W_0 ≈ 14 s` bound). **(e) is
  RESTATED by the owner** (2026-09-22) to the form WP-10 §4.1 calls (e′): *bound the campaign's
  overhead over the sum of its per-cell timings* — §6.2 E2 (e′). Three items are **booked into
  slot 7's re-baseline, not unmet**: the `presentation` settings key, its hash-invariance arm, and
  the campaign's `ext_json_*` equality. **E2 is therefore declared: (a)–(d) met, M1 met, (e)
  restated with the miss under the old text recorded.**
* **§6.2 E5 — `obl:coneexact`(vii) implemented, sentence by sentence.** (1) The strict-pair route
  (WP-4, `HeckeConeStrictPairRoute`, `TauVertexPolicy::BoundaryStrict`): `A_c^s == A_c` on
  212 / 212 operators (636 degrees), asserted on 138 at `6 ∈ R^×`, recorded on 74 at
  `ell ∈ {2, 3}` with 0 recorded disagreements; `η^s ≡ 0`; 4650 int64 fills, 0 widened (the
  widened tier forced on three cells gives identical tables). (2) Route 3 (WP-5,
  `HeckeConeRelativeRoute`): `M A' M^{-1} == A_c` on 212 / 212, asserted at every `ell`.
  (3) **The PD gate for `X_3`** (WP-3, `Hecke/HeckePairing`, an (a/s) package, **accepted**):
  `cl:pd`(1) perfect on 60 / 60 cone and 40 / 40 circle pairings, `A_c^T G = G A(D_n)` for
  `p ∈ {2, 3, 5, 7}` on 160 (operator, `t`) pairs over 20 cells, failing 0, the `p^n`-twisted
  controls 65 / 65 rejected — "recorded as unavailable" becomes **asserted**. `cl:pd` stays OPEN
  in [C]: the gate tests it. `docs/matrix-engine/tools/cone_output_diff.sh` (WP-4) is the evidence
  behind every "cone output unchanged" statement of the slot.
* **§6.2 E7 — E7a DONE, E7b DONE ((a/s), accepted); E7 acceptance is slot 7's.** WP-1:
  `Mat22::adj`, `ρ_n^∨ = ρ_n(adj ·)^T`, the contragredient relation list, `Φ_n`, the coefficient
  pairing, `H^•(D_n)` and `A(D_n)(T_p)^q`; the intertwining asserted **untwisted** (exponent 0,
  `lem:symdual`) and the `p^{±n}`-twisted relations asserted to fail on 20 non-vacuous
  `(cell, p, q)`. WP-3: the pairings at cochain and cohomology level, perfectness and adjointness
  certificates, and socle ↔ Loewy as `HeckeIdentityCertificate` **item 7** (19 / 19, 10 tamper
  rejections); the `ι`-pairing sign recorded, `−(−1)^n` on 21 / 21. The golden objects are
  **defined, not emitted** — slot 7's separate add-only emission.
* **§6.2 E6 *cont.*, part 1 — DONE.** The atlas (WP-8, `HeckeExt/HeckeAtlas`, `Σ(ell)` for
  `ell ≤ 13`, the store `hecke_atlas/v1`, write-gated, outside `results/` — the canonical split
  field's **first consumer**); identity 6 (WP-9, certificate **item 6**, 108 / 108 cells at
  `ell ∈ {5, 7, 11}`, the contragredient reading failing on all 63 cells where it is
  distinguishable — **the `det`-twist convention gate is now backed by a test**); `S_sep` / Stage
  2(3) as the opt-in `ExtDriverOptions::s_sep` (vacuous at `ell ≤ 13` on the subgrid and M1, acts
  on constructed one-prime `S_0'`); the `proof_range` comparison (§ "Open items" below).
* **§1.6 — "E1–E9 add entries only" is CORRECTED** ([S6] §2.3 item 2). After slot 5's emission the
  default `hecke_ext/v2` text is 62 golden lines (31 tier A `ext_json_canonical` + 31 tier B
  `ext_json_full`). E6's record integration (atlas labels, the canonical split in the record,
  `predictions_mode`, an atlas-decided `proof_range`, `S_sep` in the default Stage 2(3)) changes
  that text, so for E6 the sentence was **false**; E7 and E8 add entries, but any key they
  register moves the same 62 lines (next item). The sentence now reads as §1.6 says at v1.10.
* **§1.5 — the registration refrain is CORRECTED.** "Each appended with its default unchanged, so
  … no golden value or job id moved" was true **before** slot 5's emission and is **false after
  it**: `MathSettings::to_json()` prints every registered key with its value and `source`, inside
  all 62 `ext_json_*` texts, so **registering any key moves 62 golden lines** (and
  `EngineDeterminismValidation`'s digest). Hence no key was registered in slot 6, and the
  `presentation` key waits for slot 7's recipe change (a path-scoped redaction of the top-level
  `settings` object to `{fingerprint}`, §8's re-baseline stage 1).
* **§2.2 Stage 5 — two wording fixes from slot-6 WP-2.** (1) "The relation count equals
  `dim_F(ker / m_S ker)`" counts `A_S`-generators only at `f = 1`; the count is
  `dim_F(ker / m_S ker) / f`, i.e. over the residue field `K`, and WP-2's `f = 2` arm pins it
  (one relation, `F`-dimension 2). (2) The least-index Nakayama lift is taken in the **block's
  own basis** (`PrimaryBlock::basis_columns` coordinates), not the stored `H^q` basis, so
  generator indices are block-basis indices (at the unsplit `(10, 691)` block: `{0, 1}`); the
  slot-7 record key must say so or carry the generators as `H^q`-columns.
* **§6.2 E7 / §5 — "identity 5" is CORRECTED to certificate item 7** ([S6] §2.3 item 8, §2.5).
  Slot-5 WP-8 shipped Dickson `L·` as `HeckeIdentityCertificate` item 5; a certificate's item
  codes are its tamper vocabulary, so socle ↔ Loewy is **item 7** (WP-3) and the residue-atlas
  identity **item 6** (WP-9). The one numbering, [S6] §2.5's table, is:

  | [E] §5.1 item | E1 identity class | `HeckeIdentityCertificate` item | status (v1.10) |
  |---|---|---|---|
  | 1 (`cl:dimH1`, dimensions, exactness) | 1 | item 1 (Eichler–Shimura) | shipped |
  | 2 (commutativity, equivariance) | 2 | item 2 | shipped |
  | — (`d_2 = 0`) | 3 | item 3 | shipped |
  | — (`thm:relations`, full `T_{p^2}`) | 4 | item 4 | shipped |
  | 6, the `L·` half | 5 | item 5 (Dickson `L·`) | shipped (slot-5 WP-8) |
  | 6, the atlas half ("identity 6", `cl:glover`'s convention) | 6 | **item 6** | shipped (slot-6 WP-9) |
  | 5 (Poincaré duality, socle ↔ Loewy) | 7 | **item 7** | shipped (slot-6 WP-3) |
  | 3, 4, 7 (boundary characters, Kummer, Loewy sums) | — | not a certificate item | unchanged |
* **The correction of [WP5-13] §8 item 8** ("two cone digests re-pinned"). No cone digest ever
  depended on `A_c`'s tier: the harness's `ExtTierFor` override already published `A_c(T_p)^q`
  as tier B, and `0xedbff302058416f3` is **`HeckeConeValidation`'s grid digest** over
  `EquivariantMappingCone::golden_digest()`, whose `golden_objects()` contains no `A_c`. WP-5
  relabelled the unit to `'B'`, removed the override and its false comment, and moved only
  `HeckeConeAction::golden_digest()`, which is printed nowhere (`0xb298009e1c80c9fb →
  0xba258de7a334d5e0` at `(10, 691)`, `p = 2`, `ν = 1`). **Nothing was re-pinned.**
* **`sec:reportfield` → `sec:field`** at this plan's v1.9 changelog (the `own_field_s` sentence of
  the E6 bullet): `sec:reportfield` never existed in [E] (`git log -S` finds no definition; [E]
  v1.7.0 item 3, [BR6] §9 item 1). The same repoint is made in `docs/architecture-detail.md` and
  `HeckeExt/README.md` by the close.
* **The campaign's extension-identity gap is CLOSED** (WP-6, owner confirmation 9): the ext record
  file carries `_x<16 hex>` = the FNV-1a-64 of `ExtSpec::signature_tag()`, so two campaigns
  differing only in `family` no longer share a record file or resume key; `Job::id()` is
  unchanged, and with `ext = false` every job id, file name and header is byte-identical
  (`n16_ell5_p2_r1` included).
* **`cross_config.sh`'s `Check` arm** runs under `ENGINE_CUDA_DISABLE=1` (WP-7), so the WSL CUDA
  driver's LeakSanitizer false positive (v1.9 operational finding 3) no longer reaches it —
  **completed by the close**: WP-7's variable reached the golden run and the validations but not
  the `--bench micro` runs, whose logs still carried the LSan report while the runner (which reads a
  bench's checksum, never its exit code) printed `PASS`. The unchecked bench exit code is recorded
  for the next tool edit.
* **Console C2a DONE** (WP-13; [P] v3.4 §10 C2a (f), (g), (h)): engine knobs as `set` keys, the
  session baseline restored at session end, `resume` refusing a changed non-budget setting,
  `ConsoleSettingsValidation` (fast, 179 checks), script `021` with a first-freeze transcript; the
  exit-5 arm back in C2 on `field_polynomial = conway`. C2b is slot 7's.
* **Documents.** [E] **v1.7.0** (WP-11, `X`: the E6 gate restated in `sec:field` and reduced to a
  pointer, the §8.2 separation repair, `sec:reportfield` recorded as never having existed) →
  **v1.7.1** (WP-12, the referee's three repairs, `Y`) → **v1.7.2** (WP-14, status). [P]
  **v3.4** (WP-11: C2 split into C2a / C2b, C2 (g) derived from `keys()`, C4 (d) / C5 (c) restated)
  → status at the close. [C] **v1.7.3** (WP-14, status only: `sec:contragredient` implemented,
  `obl:coneexact`(vii) implemented, counts 106 / 60). [X] **v1.10** (this).
* **The ratio-criterion audit (WP-10) — its proposals, AS PROPOSALS for the owner** (31 clauses,
  5 defective): (1) **E2 (e)** — restated by the owner to (e′), above and §6.2 E2; (2) **[P] C2 (g)
  "twelve"**, **C4 (d) "< 5 s"**, **C5 (c) "identities 1–6"** — taken by [P] v3.4 (WP-11);
  (3) **[S6]'s driver head-to-head** had no verdict rule — WP-10 §4.5's rule (median `total_s`
  NEW/REF ≤ 1.04 at `(10, 691)` and `(160, 691)`, `ext_s` gated only at `(160, 691)` and only if
  its REF min ≥ 1 ms) was shipped in `ext_driver_h2h.sh` and applied by WP-2 and WP-9 — **proposed**
  as the standing rule for driver packages; (4) **`ENGINE_THREADS=16`** in E1 (d)'s and E6 (d)'s
  pinned invocations (hygiene; 1.2 % on E1 (d); the slot-6 window pins it) — **proposed**;
  (5) **E5 (d)'s reduction**: "five interleaved rounds, met iff the **median** per-round ratio is
  `≤ 2.0`, the worst cross-pairing reported" — **proposed** (what the acceptance did; the worst
  pairing had 0.2 % margin); (6) §5's "`--all` grows by ≈ 40 s" to say "(estimate, not a bound)"
  so that E6 (b) cannot inherit it — **proposed**; (7) wherever an acceptance clause repeats the
  `u_ell` admitted range, say "where `UEllDecision` admits it" — **proposed**; (8)
  `docs/matrix-engine/campaign.md` §10's wall-clock estimates marked "pre-Phase-4/5, superseded by
  §13" — **proposed**; (9) CLAUDE.md's fitted-exponent guard to name its `n`-set
  `{64, 96, 128}` — applied by the close (CLAUDE.md is not a normative document). None of (3)–(8)
  is written into a clause here: restating a clause is the owner's.
* **Not changed**: everything else; the v1.9 changelog below stands, except where this version
  supersedes it (the E6 gate's placement and denominator, the §1.5 refrain, §1.6's "add entries
  only", "identity 5", the `digest@SHA` rule for the ext digest, and [WP5-13] §8 item 8).

**Open items at the slot-6 close** (owner items are **recorded, not ruled**):

1. **The E6 high-`r` cost — RULED by the owner ([OD] E6-3).** `(210, 691)` 0.262,
   `(256, 134217757)` 1.14 at `r = 14 / 19`; root finding ≥ 96 %, ≈ `r^5`–`r^6`, against
   `alg:split`'s `O(r^3 log ell)`; WP-8's suspect is the equal-degree splitting over `F`
   (`FqPowMod` with exponent ≈ `ell^r`). **A small slot-7 package diagnoses and fixes
   `FindCanonicalRoot`**; `split_field_report = canonical` stays the default meanwhile; the gate
   text is unchanged; the gate verdict stays open until after the fix; the gate gains a high-`r`
   cell. E6 acceptance stays slot 7's.
2. **[E] v1.7.1 finding B-1 — ACCEPTED by the owner ([OD] S6-B1, 2026-09-22).** The referee
   reworded the `(160, 691)` separation sentence away from the text [S6] §3 WP-11 prescribed — an
   **owner-approved departure** — because the
   `SEPARATION_SINGLE` measurement refutes the prescribed text: [E] now reads "the block partition
   at `(160, 691)`, with its residue degrees, is already `T_2`'s (and `T_3`'s); `T_5` alone gives
   the same partition and under-reports one residue degree". A different formulation is a
   one-sentence change at two sites.
3. **E2 (e)**: measured with one pair ([OD] S6-2″, a recorded deviation from ruling 2's three);
   restated by the owner to (e′) (§6.2 E2). Its constant and its first measurement are slot 7's.
4. **The `conway` silent fall-back** (WP-13 finding 1). `MathSettings::set` accepts `conway`;
   only `FieldPolynomialFromSettings` rejects it. `CanonicalField(ell, r)` and
   `SplitInCanonicalField(ell, …)` (e.g. `Bench/BenchDriver.cpp`, the atlas) call
   `CanonicalFieldPolynomial` directly, so under `conway` they silently use `least` while the
   settings block says `conway` — the fall-back the key's contract forbids. Latent (no report
   consumer yet); **the E6 report layer must route through `FieldPolynomialFromSettings`** (slot 7).
5. **Transcript 014's resume refusal versus [P] (h)'s "strict no-op"** (WP-13 finding 2). A resume
   on a *complete* handle stays a typed refusal because the frozen `014_expect_error.expected`
   pins it; the engine-level `resume_locality` on a complete state is a strict no-op, asserted.
   Changing 014 is an **owner-gated transcript re-baseline**.
6. **`build-tsan/Makefile`** — a generated file that was tracked (`/build-tsan/` is git-ignored);
   **untracked by the close** (`git rm --cached`).
7. **`proof_range`: 4 `true → false (sturm_heuristic)` flips** an atlas-decided `proof_range`
   would cause (WP-9 §4): subgrid `(24, 5)` ideal 1 — **a golden cell**, so feeding it back moves
   golden values — and M1 `(58, 7)` ideal 3, `(58, 5)` ideal 1, `(82, 7)` ideal 1. Slot 7's staged
   re-baseline, stage 2 item 3. **WP-9's method caveat**: evaluating the flip by calling `is_final`
   with only `sturm_proof_range` changed reports **no** flips, which is wrong — `proof_range`
   reaches `final` through the Sturm sweep's outcome (`Heuristic`), so any consumer of the atlas
   decision must **re-run the driver**, as WP-9's validation does.
8. **WP-2's two wording fixes** — applied to §2.2 Stage 5 above.
9. **Minor findings.** WP-4: `HeckeTauTable::to_string_offset` prints the policy
   `GeometricNearestLegacy` as `"FixedV6"` (a two-way ternary over three pre-slot-6 values;
   `tau_table_p2.txt` is a `GeometricNearest` table and is unaffected) — fix when the file is next
   touched, checking every frozen text first. WP-5: the **η-provenance check** — the cross-routes
   consume the normative action's derived `h` / `η` as given; a check that it is the certified
   `η`-table's `η̃` (and not any cochain with the right boundary) is recorded for the next cone
   package. WP-12 m-1: `HeckeCanonicalField.h`'s header still stated the pre-restatement gate —
   **fixed by the close** (comment only). WP-12 M-1: `HeckeExtSeparationValidation.cpp`'s
   "same dimension multiset, so the same partition" comment — **reworded by the close** (comment
   only: the partition identity follows from refinement plus equal block counts). WP-12 m-3:
   [P] C4 (d)'s analogy pointer — recorded in [P]'s close status block.
10. **[C] status** — `sec:contragredient` implemented (WP-1) and `obl:coneexact`(vii) implemented,
    in [C] v1.7.3; the stale `sec:reportfield` citations repointed (this plan, `architecture-detail.md`,
    `HeckeExt/README.md`); the slot-5 and slot-6 package reports that quote it are history and
    are not edited.

### `[OD]` — the owner rulings of slot 6, as a register

Source: `docs/implementation/e6_gate_brief.md` "Owner decisions (2026-09-22)" and
`hecke_extensions_slot6_plan.md` §10, plus the owner's instructions to the close.

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **E6-1** | **RESTATE the E6 gate, option (a)**: `canonical_field_s ≤ 0.10 × total_s` on the 23 cells, protocol pinned as [BR6] §6.1, the `≤ 2 × own_field_s` half deleted, `own_field_s` a reported column; **condition**: slot 6 measures `(10, 691)`'s `total_s` and at least one high-`r` cell before E6 acceptance may be declared against it. | WP-7 (code comments, print line, `e6_measure.sh`), WP-11 ([E] v1.7.0), this version (§6.2 E6 (d)). Condition **discharged** in the lead's window; the high-`r` cells **fail** — open item 1 |
| **E6-2** | **One authoritative statement**: the gate moves into §6.2 E6 as item (d); §2.2 Stage 6 and [E] `sec:field` become pointers. | This version; [E] v1.7.0 / v1.7.2 |
| **S6-1** | E7 starts on day one on E2's substantive state; WP-2 / WP-6 close E2 formally. | E2 declared by this close |
| **S6-2** | E2 (e)'s pinned protocol **(A)**: fresh `--output` per run, resume only within a run, both arms, `jobs = 16` / `threads = 2`, after the ext-identity fix, in the lead's window; `3.0` kept, marked unjustified; a miss is recorded, not restated. | `e2e_measure.sh` (WP-6); the window |
| **S6-2″** | **E2 (e) is measured with ONE pair** (`e2e_measure.sh --pairs 1`), not the three ruling 2 pinned — a **recorded deviation** from S6-2, because WP-10 predicts a ≈ 680× miss, so the verdict cannot depend on the sample count. | `slot6_close_window.sh --with-e2e`; §6.2 E2 |
| **E6-3** | **The high-`r` canonical-field cost** (WP-7 / WP-10 cells, WP-8's diagnosis), at the recommendation: **a small slot-7 package diagnoses and fixes `FindCanonicalRoot`** (≈ `r^5`–`r^6` against `alg:split`'s `O(r^3 log ell)`); meanwhile **`split_field_report = canonical` stays the default**, the **gate text is unchanged**, **E6's gate verdict stays open until after the fix**, and **the gate gains a high-`r` cell**. | §6.2 E6 (d)'s v1.10 note; §8's slot-7 re-cut |
| **S6-B1** | **[E] v1.7.1 finding B-1 ACCEPTED**: the referee's reworded `(160, 691)` separation sentence stands; the departure from [S6] §3 WP-11's prescribed wording is **owner-approved**. | [E] v1.7.1 / v1.7.2 |
| **S6-2′** | **E2 (e) RESTATED** (owner, 2026-09-22, after WP-10's audit): bound the campaign's **overhead over the sum of its per-cell timings** (WP-10 §4.1 form (e′)). | §6.2 E2 (e′) |
| **S6-3** | **(A)**: the record text is frozen in slot 6 (no emission); slot 7 makes a **separate E7 add-only emission** at E7 acceptance plus **one staged changed-line re-baseline** (recipe → keys / source at zero movement → each value-changing item its own explained commit). | §1.6, §8's slot-7 re-cut |
| **S6-4** | Atlas scope: the slot-5 proposal + `Σ(11)`, `Σ(13)`; consumer = the atlas; store write-gated, outside `results/`; no tangent pair. | WP-8 (shed line not used) |
| **S6-5** | E2 (a)'s golden arm on settings-independent objects only; `ext_json_*` equality booked with the source fix in slot 7. | WP-6 arm 8 |
| **S6-6** | **The first ext campaign is deferred to slot 7**, after the re-baseline — a recorded deviation from v1.9 §8's slot-6 B2 row. | §8 |
| **S6-7** | C2 split into C2a (slot 6) and C2b (slot 7). | WP-13; [P] v3.4 |
| **S6-8** | WP-3 (E7b) as (a/s). | WP-3 ran and was **accepted** (the PD gate passed) |
| **S6-9** | The ext-identity fix = the ext tag in the ext record **file's** name. | WP-6 |
| **S6 ceiling** | 5.50 AU authorised (4.90 must-accept + 0.60 (a/s)); the 5.30 AU shed line not applied up front. | No package used its shed line |


**Version 1.9 — 2026-09-22. Slot 5 close ([S5] WP-13): the stage's one add-only golden emission
made, E5 acceptance MET, M1 declared, and four acceptance criteria tested against reality.**
Sources: `docs/implementation/slot5/` (WP-1 … WP-12a reports, fourteen packages), the slot-5 plan
`hecke_extensions_slot5_plan.md` [S5] with its audit, `slot4_open_items_brief.md` with its
appended owner decisions of 2026-09-22, and the close's own gate run on `d362c71`. No phase changes
its mathematics.

**The slot ADDED golden entries and CHANGED none.** `golden_explain.py before after` reports
**0 changed, 0 removed**, with no `--allow-keys` file and no `--accept-split`; the single deleted
line of `Orbifold_Cohomology_of_GL2/Golden/GoldenReference.inc` is the header comment
`// Entries: 14049`. Entries 14 049 → **16 666**, tier A 9446 → **10 914**, tier B 4603 →
**5752**, both failing 0 under `GOLDEN_STRICT=1`. `docs/implementation/tau_table_p2.txt` and
`Orbifold_Cohomology_of_GL2/Hecke/HeckeReport.{h,cpp}` are byte-identical to `2b1b339`'s — the
extension record remains a separate writer. The re-baseline note is
`docs/matrix-engine/rebaseline-2026-09-22-hecke-ext-v2.md`.
`EngineDeterminismValidation`'s digest moved **`0xe446b3bd2d28bd6e` → `0xa81480950dffb0d2`**
(966 → 1216 records per arm) **as a consequence of that emission, not of the engine**: three of its
four golden-grid cells are in the extension subgrid. Every arm still agrees and every record still
equals the reference. **Later slots hold the new value.**

Changelog:

* **§6.2 E5 acceptance (d) is RESTATED and MET.** [OD] slot-4 close-out 1 (below) replaces the
  clause: numerator `M_cone` = the `VmHWM` of a process that builds exactly one
  `EquivariantMappingCone` at `n_sym = 256`, `ell = 134217757` and calls `ConeCertificate::verify()`
  once; denominator `M_base` = the `rss_mb` of `./cohomology_app --bench hecke 256 134217757 2
  --repeat 1` in a separate process in the same session; **met iff `M_cone ≤ 2.0 · M_base`**. WP-5
  put the cone's `Z / B / H / P` and the certificate's span inclusions on the tape and measured
  **510.8–524.1 MB against 262.6–275.5 MB over five interleaved rounds — 1.90–1.95×, median
  1.93×** (it was 2.17–2.19× before), met at every `n` of the grid (1.58 / 1.81 / 1.86 / 1.89 /
  1.93× at `n = 64 / 128 / 160 / 200 / 256`) and at the worst cross-pairing of the five rounds,
  1.996×. Nothing was sampled, relaxed or moved out of `compute()`. **E5 is ACCEPTED**: (a)–(c)
  re-verified on the final tree, (d) measured and met, the record fields WP-1's. Reported, not
  gated: cone + action **1275.8 MB = 4.86×** at `n = 256`, up 33 MB, because the tape's program
  cache and per-worker arenas are retained under the action's own peak.
* **Two slot-4 findings superseded by WP-5's measurement.** [WP4-4] finding 5, "`verify()` runs
  ~20 % *below* the cone's high-water mark", **no longer holds**: after the tape the construction
  peaks at 450.2 MB and the certificate takes the cone to 511.4 MB, so `verify()` is 13.6 % *above*
  the construction peak and **is** the binding item. And the input floor at `n = 256` is **0.80×**,
  not 0.85×. Any future text repeating either figure must be re-checked against this tree.
* **§1.4, §7 — the record schema is `hecke_ext/v2`** (WP-1, the owner's fifth ruling of
  2026-09-22, taken *before* the first emission): the `u_ell` verdict is the **cell's** with a
  single `resumable` (`resumable_items()` counts a refused `U_ell` **once** on a four-ideal cell,
  against v1's four); an ideal carries its `sign` and a `groups` list naming the ambient groups
  Stage 2 matched it across; the `boundary`, `pair` and cone complex objects are **computed**, each
  with its own `q_max` / `truncated` / `q_max_source` / `degrees` and `les_maps` per reported spot;
  the per-sign (E3) objects carry `iota_sign`; the reserved keys `phi_flat_identity` and
  `residual_flat_zero` are **emitted**; and the two schemas are distinguishable by their `schema`
  key alone. `verify()` gained **code 22** (WP-11a: a `q_max_source = "set"` on a *derived* complex
  is refused, [C] `sec:recordschema` item 5) and **code 23** with the record-level
  `iota_exact_comparison` (WP-12a, [OD] 2026-09-22 Q3). `HeckeExt/HeckeExtComplexRecords` is the one
  translation layer between the E3 / E4b / E5 objects and the record.
* **§1.5 — the campaign carries the record** (WP-2): the spec takes `ext`, `family`, `sign` and
  `ext_groups`; with `ext = true` the driver runs once per `(n_sym, ell)` **cell**, sequentially on
  the campaign's main thread and before the job loop (it builds its tessellation tables outside
  `hecke::tau_construction_mutex()` and so may not run on a job thread, while holding that lock
  around `run()` would deadlock on its own re-entry), attaching the record to the cell's first job
  in plan order. With `ext = false` every byte of the campaign's output is unchanged. The
  record-level `u_ell` resume of §1.3.1 R3.3 item 4 is implemented. The seam is
  `Campaign/CampaignExt.{h,cpp}`.
* **§1.6 — the emission, and four corrections to §1.6 itself** (WP-3). The harness runs the ext
  subgrid (`n > 0` even, `5 ≤ ell < 2^32`; 31 cells) under a scoped `u_ell = off` and the family
  `{T_2, T_3, T_5}`, with one tier-A `ext_excluded` on every other cell and on every 64-bit point.
  (i) **The `^q` suffixes are dropped** from `ext_ideals`, `ext_certify`, `ext_json_canonical` and
  `ext_json_full` — they are a v1 spelling, from when a record was about one degree; a `v2` record
  is about one **cell** and its ideals carry a `groups` list, not a degree. The tiering OP7 fixes is
  preserved exactly. (ii) The three tier-B names `ext_algebra_basis^q`, `ext_loewy_bases^q` and
  `ext_structure_maps^q` **have no shipped collector**; their content is pinned through
  `ext_json_full`, and they are struck rather than invented at the point of no return. (iii)
  `A_c(T_p)^q` is **tier B**, as OP7 fixes it; `HeckeConeAction::golden_objects()` labels it `'A'`
  and the harness applies OP7's tier at emission, because the label feeds a digest slot-4 WP-4
  pinned — relabelling in the unit and re-pinning is a later slot's, at zero golden cost. (iv) The
  golden subgrid's `S_0` is `{2, 3}` at `ell = 5`, so on `(22, 5)` and `(32, 5)` route (c) is
  `unavailable` and **four ideals are published `final = false`, reason `closure_unreachable`** —
  **the first `final = false` rows the programme has published**, a consequence of the harness's
  own settings.
* **§4.4 / the WP-3 acceptance clause — an internal contradiction of [S5], recorded.** [S5] §4.4
  exempts WP-3 from the standing `EngineDeterminismValidation` digest gate; WP-3's own acceptance
  (c) restates it. Since that validation digests the record set of four golden-grid cells, three of
  them in the ext subgrid, the digest **cannot** be preserved by any emission touching those
  cells — (c) is unsatisfiable by construction. **The gate is restated here, for every future
  slot**, as: *every arm agrees with arm 0 and every record equals the reference*, with the digest
  carried as a **value** that an emission may update and a non-emitting package may not.
* **§6.2 E6 — the performance gate is DEFECTIVE AS WRITTEN and is an owner question** (WP-7 §4;
  structurally the same defect [X] v1.8 recorded for E5 (d), and the second such found this slot).
  The gate is `canonical_field_s ≤ 0.10 × ext_s` **and** `canonical_field_s ≤ 2 × own_field_s`.
  Measured on all 23 cells: **not met on either half, on any cell.** (1) The second half **is not
  attainable by any implementation**: `own_field_s` is, by [E] `sec:field`'s own words (v1.10: this said `sec:reportfield`, a label
  that never existed), "zero
  new arithmetic" — 1–6 µs of string formatting — so the clause demands that root finding in
  `F_{ell^r}` cost no more than twice a `sprintf`; the ratio is 6–11× on every small cell *even
  when the absolute cost is 9 µs*. (2) The first half is a ratio against a denominator that is
  itself microseconds on 20 of the 23 cells (`ext_s` prints as `0.0000` at `ell ≤ 13`). (3) Only
  `(160, 691)` and `(198, 691)` cost anything real — 2.0 ms and 14.8 ms, i.e. **0.68 % and 2.92 %
  of `total_s`**. **If the gate is restated against `total_s`, or against `pipeline_s + decomp_s`
  (the denominator §6.2 E1 (d) already uses), at the same 0.10 threshold, all 23 cells pass**, the
  worst at 2.9 % against 10 %. WP-7 measured and did **not** flip `split_field_report`'s default;
  restating the gate is the owner's, and E6 acceptance is slot 6's.
* **§1.5 — two more mathematical keys** (WP-7): **`field_polynomial`** (`least | conway`, default
  `least`; `conway` parses and round-trips but raises the named
  `hecke::NotImplementedInThisBuild` — the `locality = strict` precedent, inverted in time) and
  **`split_field_report`** (`canonical | own_field`, default `canonical` per [OD] OQ10; **no
  consumer in this build**, the `u_ell` pattern of slot-3 WP-1). **Eight keys** are now registered,
  each appended with its default unchanged, so the all-defaults fingerprint is still `0` and no
  golden value or job id moved. Since WP-10 `canonical_text()`, `to_json()` and `text(key)` are one
  loop over `keys()` on a single per-key view: a key is spelled in one place, adding one is four
  edits, and a key added to the registry without a `view_of` arm **throws** instead of silently
  emitting an empty value.
* **§5, §8 Lane B1 — M1 is DECLARED** (WP-8): every case of [E] §8 that lives in `H^0`/`H^1` is
  computed as a record on `X_1 ⊕ X_4` — **23 cells, 62 maximal ideals**, each with a `final`
  tri-state whose reason is a member of §1.3.1 R3.2's fixed list and a `B'(k, ell)` column. **At
  the shipped default settings all 62 are `final = true`**, including on the Dickson loci where
  §6.2 E2 predicts `final = false` / `sturm_heuristic`, for a structural reason that is itself a
  finding: **`ExtDriverOptions::proof_range` is an unverified caller input defaulting to `true`**,
  and nothing in the tree can decide the range until E6's residue atlas exists. The owner approved
  emitting it as-is with the qualification recorded; each record carries `"proof_range": true`
  beside `"proof_range_source": "dickson_count"`. `HeckeExtSmallEllValidation` arm 5 exhibits the
  `false` / `"heuristic"` branches on the same cells under the one input that controls them, and
  the golden emission publishes four genuine `final = false` rows for the independent reason above.
* **§6.2 E1 identity class 5 is DISCHARGED** (WP-8): `HeckeExt/HeckeDicksonMultiplication` ships
  `L· : Sym^{n−ell−1} → Sym^n`, an `(n+1) × (n−ell)` matrix with entries in `{0, ±1}`, with a
  certificate that re-derives its entries by an independent convolution and the det-twisted
  intertwining `ρ_n(A) L = det(A) L ρ_m(A)`; `HeckeIdentityCertificate` gains item 5, the
  cohomology-level `A^{(1)}_n(T_p) L_* = p L_* A^{(1)}_m(T_p)`, with the untwisted identity asserted
  to FAIL so the exponent is pinned. Classes 6 (the residue atlas) and 7 (socle/Loewy duality)
  remain open and are slot 6's.
* **§8.2 of [E] is REFUTED by measurement** (WP-8 finding 1): the separation sentence does not hold
  of the shipped `ComputeMultiOp`. Recorded in [E] v1.6.2 and in `HeckeExtSeparationValidation`,
  which measures the claim rather than asserting it.
* **§5 — the tier of `HeckeExtKummerValidation` is `slow`**, not `standard`. [S5] §3 WP-8 says
  `standard` and this plan's §5 says `slow ≈ 40 s`; the measurement settles it — **37.5 s at the
  default settings, of which `U_3617` at `(14, 3617)` alone is 33.9 s**. The plan text is corrected
  here. The `slow` tier now holds **six** names.
* **§2.3 item 6 of [S5] rested on a stale premise, and nothing was done on its account** (WP-11
  finding 1, confirmed independently by WP-12 observation O2): all three [E] repairs it books
  already existed at [E] v1.5.0 / v1.5.1. **This version does not re-book them.**
* **§1.3.1 R3.3 item 4** — the record-level `u_ell` resume is implemented (WP-2). Its settings rule:
  a resume may not lower the budget, is a strict no-op over an included verdict, and may not reuse
  a record built without the object being asked for.
* **Documents.** [C] **v1.7.0** (WP-11, the slot's one `X`: `obl:coneexact`(iii)'s carve-out
  dropped **with the proof that clause (i) implies the `r`-half** written in, the `sec:recordschema`
  items for `hecke_ext/v2`, and the four items [WP4-8] §4 deferred) → **v1.7.1** (WP-12, the
  referee's eight repairs, `Y`) → **v1.7.2** (WP-13, status only). [E] **v1.6.0** (WP-11, the
  `det`-twist convention fixed normatively — **this gates E7**) → **v1.6.1** (WP-12) →
  **v1.6.2** (WP-13, status). [P] **v3.3** (WP-11) → status at the close. [X] **v1.9** (WP-13).
* **§8 — the slot-5 outcome, and the deviations from v1.8's slot-5 row, recorded.** Delivered:
  the must-accept set (WP-1 … WP-5, WP-7, WP-8, WP-10 … WP-12) plus **WP-6** (the pipeline-wide
  `ρ_n` memo) and two follow-on packages created inside the slot, **WP-11a** (the
  `sec:recordschema` item-5 gap WP-11 left in the code) and **WP-12a** (the two owner rulings on
  WP-12's Q2 and Q3). **Deviations**: the **atlas driver skeleton (WP-9) was DEFERRED by the owner
  and did not run** — it returns as slot 6's; the **E3 record integration** landed inside WP-1 and
  WP-12a rather than as a Lane B2 item of its own; and **E5 acceptance was declared by the close**,
  on WP-5's dossier and WP-1's record fields, rather than by a package.
* **Operational findings.** (1) **The pathspec `Golden/GoldenReference.inc` matches nothing** — the
  file is `Orbifold_Cohomology_of_GL2/Golden/GoldenReference.inc` — so several packages' and the
  lead's "golden untouched" checks were **vacuous**. The conclusion held (re-verified with
  `'*GoldenReference.inc'`, and by `GOLDEN_STRICT=1` content checks throughout), but the *check*
  was not evidence. **Future slots use `'*GoldenReference.inc'`.** (2) **`HeckeExtDeterminismValidation`'s
  digest is not reproducible bare**: it hashes the whole record text, which contains the `commit`
  key, baked in by `CMakeLists.txt:1172` from `rev-parse HEAD` at configure time, so it moves on
  every commit including a documents-only one. **Every digest is written `digest@SHA` from now on**;
  at the close tree it is `0x415f73f051702a71@d362c71`. The repair — redact `commit` before
  digesting, as the golden objects do, then re-pin once — is slot 6's. (3) **`cross_config.sh`'s `Check` arm is not usable with a device-probing validation.** The
  exit-item-2 run is clean in all five configurations — tier A / tier B 0 failing everywhere
  against the new reference, both micro checksums identical — and the runner nonetheless reports
  `FAIL`, on one cell: `HeckeExtDeterminismValidation` under `Check`. The validation **passes**
  (`failing_arms = 0`, the same digest); what fails is LeakSanitizer, on 50 960 bytes in 5
  allocations whose stacks are **entirely inside `/usr/lib/wsl/lib/libcuda.so.1`** — the WSL CUDA
  driver's one-time probe. `ENGINE_CUDA_DISABLE=1` makes the same binary exit 0, and the
  **pre-existing** `CudaTransferValidation` reproduces the identical five allocations, so this is
  a property of the environment and not of the slot. **Repair, slot 6**: the `Check` arm should
  set `ENGINE_CUDA_DISABLE=1` or carry a suppression for `libcuda.so.1`. (4) Worktrees are still
  created off a stale commit, so every package still had to reset onto the integration head.
* **Not changed**: everything else; the v1.8 changelog below stands, except where this version
  supersedes it (E5 (d), the [WP4-4] findings above, the schema version, the settings-key count and
  the `HeckeExtKummerValidation` tier).

### `[OD]` — the owner rulings of 2026-09-22, as a register

Recorded here so that no later slot re-litigates them. Source in every case:
`docs/implementation/slot4_open_items_brief.md`, its appended "Owner decisions (2026-09-22)"
section, and the owner's answers to WP-12's referee questions of the same date.

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **slot-4 close-out 1** | **§6.2 E5 acceptance (d): RESTATE.** Numerator = the **cone object alone** (`VmHWM` of a process that builds one cone at `n_sym = 256`, `ell = 134217757` and calls `ConeCertificate::verify()` once and does nothing else); denominator = `rss_mb` of `./cohomology_app --bench hecke 256 134217757 2 --repeat 1` in a separate process in the same session; bound **2.0×**. The cone + action ratio and the `n = 200` ratio are **measured and reported, not gated**. | Written into §6.2 E5 (d). **MET** by WP-5: 1.90–1.95×, median 1.93× |
| **slot-4 close-out 2 (OI-2)** | **APPROVED.** `ConeCertificate` item **11** evaluates the **first** `eq:conedims` identity without consulting `H2_zero`, **keeping item code 11**, each identity under its own minimal guard (Option A). | WP-4, value-preservingly; [C] v1.7.0 |
| **slot-4 close-out 3 (OI-3)** | **APPROVED.** `obl:coneexact`(iii)'s `r`-half is asserted at **every** `ell` — the `ell ∈ {2, 3}` carve-out is dropped (Option A) — and the proof that clause (i) implies it is written into the contract. | WP-4 (code), [C] v1.7.0 (the proof), WP-12a (the record's `restriction_equivariance_asserted` made honest, certificate item 12) |
| **slot-4 close-out 4 (OI-4)** | **RATIFIED as a standing rule.** A referee may repair a self-contradiction of the version under review as a pointers-only `Y` bump, without an `X`. | Applied by WP-12; carried here as the standing rule |
| **slot-4 close-out 5** | **The `u_ell` per-ideal → per-cell repair ships as `hecke_ext/v2`, BEFORE the first emission.** | WP-1, merged strictly before WP-3 |
| **2026-09-22 Q1** | **Reading A.** `obl:taubdry`(vii) is a **distinct, weaker clause**, not a pointer to `obl:coneexact`(iii). | [C] v1.7.1 (WP-12 F1(a)) stands as drafted |
| **2026-09-22 Q2** | **Fix now.** `hecke_cone_action/v1`'s `restriction_equivariance_asserted` must report the assertion the run performs, not the carve-out the code dropped. | WP-12a: the field made honest, plus `ConeActionCertificate` **item 12** to refuse a record that says otherwise |
| **2026-09-22 Q3** | **Emit in `hecke_ext/v2`.** `obl:iota`(ii)'s rider gets an emitted record. | WP-12a: the record-level `iota_exact_comparison` (`ran` / `relation_rows` / `rows_with_exact` / `rows_compared`) and `verify()` code 23 |
| **2026-09-22, the emission** | **APPROVE, add-only**, and **M1's `proof_range` is emitted as-is with the qualification recorded.** | WP-3; the qualification is in the re-baseline note §4.1, in the catalogue's `GoldenRegressionValidation` entry, and above |
| **2026-09-22, WP-9** | **DEFERRED.** The atlas driver skeleton does not run in slot 5. | Slot 6 |


**Version 1.8 — 2026-09-22. Slot 4 close ([S4] WP-11): the slot-4 outcome recorded, the
schedule re-cut from it, and one acceptance clause recorded as DEFECTIVE.** Sources:
`docs/implementation/slot4/` (WP-1 … WP-8 reports), the WP-9 referee report
`docs/implementation/referee_report_2026-09-22_contract_v1_6_0.md`, the slot-4 plan
`hecke_extensions_slot4_plan.md` [S4] with its audit, and the close's own gate run. No phase
changes its mathematics. **The slot moved no golden value and emitted no golden entry**:
`git diff 9ae1d7a` is empty for `Golden/GoldenReference.inc`, for
`docs/implementation/tau_table_p2.txt` and for `Hecke/HeckeReport.{h,cpp}`; tier A 9446/0 and
tier B 4603/0 under `GOLDEN_STRICT=1`; digest `0xe446b3bd2d28bd6e` on all 8 determinism arms.
Changelog:

* **§6.2 E5 acceptance (d) is recorded as NOT DECIDABLE AS WRITTEN, and not met on any
  reading.** This is the sharpest item of the slot. WP-4's measurement shows the clause pins
  neither its denominator's protocol (`--repeat 1` vs `--repeat 5` differ by **1.42×** at
  `n = 256`, so the same tree reads **2.19×** or **1.54×**) nor which E5 object its numerator is
  (cone alone **573.2 MB**, cone + action **1243.0 MB** — **2.2×** apart), and the `--repeat 5`
  denominator's own sample spread (±10 % at `n = 256`, **±28 %** at `n = 160`) is **larger than
  the 4 %** by which the cone misses. A **proposed restatement** is written into §6.2 beside the
  clause — **as a proposal, not a decision**: restating (d) is the owner's, and under the
  proposal the cone still fails at 2.19×, which is the honest consequence. WP-4 did not change
  (d) and neither does this version; WP-8 correctly declined to touch it, [C] and [E] stating no
  cost bound anywhere. Engineering default if unanswered ([S4] §6): (d) unchanged, the cone on
  the tape in slot 5.
* **§6.2 E1 acceptance (d) is RESOLVED and MET.** [OD] slot-3 close-out 2 records that its
  baseline was never an owner question; [S4] §2.3 item 2 fixed it as an engineering choice and
  WP-2 measured it: `ext_s ≤ 0.20 × (pipeline_s + decomp_s)` at `n = 256` with family
  `{2, 3, 5}`, **measured 0.1357 / 0.1370 / 0.1366** over three quiet rounds, **0.1644** with a
  prime forced outside `S_0`, `sturm_bound_s = 0.0041 s`. **Both readings of the old wording are
  recorded**, as [S4] asks: the literal one-prime baseline (38 % on slot-3 numbers) and
  [WP3-2]'s same-family reading (20.1 %).
* **§1.5**: `commutant_budget` registered (slot-4 WP-1), and `final_mode` with it — v1.7's table
  gave `final_mode` the consumer "`is_final` (E2)" while [S4] §3 WP-1 scoped only
  `commutant_budget`; since `is_final` shipped, so did its key ([WP1] finding 6). **Six keys are
  now registered**, each appended with its default unchanged, so the all-defaults fingerprint is
  still `0`. Two of the table's key names are **not** the registered spellings (`sturm.cap` is
  `sturm`, `sturm.unavailable` is `sturm_unavailable`) and the rows now say so.
* **§1.3.1 R3.1 item 6 — two defects, both found by shipping it.** (i) The sidecar name
  `<record-stem>.state.<kind>.json` is **not injective**: one record may carry several oversize
  states of the *same* kind (one `commutant` per ideal). E2a keeps the literal name for the first
  and appends `.<i>` to the rest; the disambiguator should be stated ([WP1] finding 2).
  (ii) `resumable.state_ref.path` should be stated to be **relative to the directory holding the
  record** — the two shipped certificate writers emit whatever the caller's stem was, absolute
  stem included, while the record-level writer emits the basename ([WP1] finding 3).
* **§1.3.1 R3.2 / §1.5 — `certificate_failed:<code>` is not what the code emits.** The shipped
  `generation_verdict` emits the literal `certificate_failed:sturm`, a certificate *name*,
  because no `verify()` failed there: the sweep succeeded and its answer was "no". The reason
  should read `certificate_failed:<code or certificate name>` over the closed list
  `{cyclic, commutant, sturm, locality, module, identity}` ([WP1] finding 1; [C] v1.6.0 item 6(d)
  and [E] §7 have taken it).
* **§1.3.1 R3.3 item 4 — an unspecified field that DECIDES A FINGERPRINT.** The clause does not
  say what a **resumed** run's `settings` block contains. If a resume installs
  `u_ell = budget_mb=<M>`, the resumed record's settings text and fingerprint differ from a fresh
  `auto` run's *even when the verdict is identical*, so "resume equals a fresh run" would be
  false at the record level. E2b installs `auto` when `M == kDefaultUEllBudgetMb` and
  `budget_mb=<M>` otherwise, which makes `resume(2048) == a fresh auto run` true **byte for byte,
  fingerprint included** (asserted). The rule must be stated ([WP2] finding 4; [C] v1.6.0 item
  6(a) has taken it).
* **The `u_ell` verdict is per CELL but the record carries it per IDEAL.** `HeckeExtRecord` has
  `UEllRecord` only inside `IdealRecord`, so a four-ideal cell emits the same `u_ell` object —
  and, when refused, the same `resumable` — four times, and `resumable_items()` counts one
  cell-level decision once per ideal. [E] §7's own example shows `u_ell` at record level. E2b
  followed the shipped struct rather than inventing a field. **Open**: either [E] §7 states it is
  per ideal, or slot 5's integration adds a record-level `u_ell` and `resumable_items()` stops
  multiplying ([WP2] finding 5 — normative, and it moves a *counted quantity*).
* **§2.2 Stage 4(c)** needs a **per-cell memoisation clause**: the sweep asks for `T_q|_V` per
  block, so a naive streamed wiring builds the same pipeline once per block — measured 2 at
  `(22, 5)` and, unfixed, 4 at `(256, 134217757)`. The streamed `A^{(q)}(T_q)` is memoised per
  `(degree, q)` at the **driver** level; the pipeline is still destroyed inside the supplier, so
  "one pipeline alive at a time" is preserved ([WP2] finding 2).
* **§2.2 Stage 3** — "`ŵ` and the `P_p` consumed from the locality verdict" was **not
  implementable through the shipped API**. It needed a new option
  (`LocalAlgebraOptions::precomputed_locality`) *and* a reconstruction of `ŵ`, the one field a
  `PrimaryBlock` does not store (the `k = 1` analytic path deliberately never forms it); E2b
  rebuilds it by `hecke::FrobeniusPower` from the block's own witness. Stage 3 should name `ŵ` as
  that field and the reconstruction as the driver's job — or `PrimaryBlock` gains `w_hat` on the
  non-analytic path in a later slot ([WP2] finding 3). Measured effect: `ext_s` 0.1610 → 0.1296 s
  at `n = 256`.
* **§2.2's E6 file map omits `GloverFactors.{h,cpp}`** ([WP7] F1): the E6 line lists
  `HeckeAtlas`, `HeckePredictions`, `HeckeCanonicalField`; the Glover unit shipped as a file of
  its own, because it does no modular arithmetic at all and mixing it into `HeckePredictions`
  would have made one TU that consumes `ModCtx` and one concern that does not.
* **§1.1 placements** (all shipped): `Hecke/HeckeInvolution` + `HeckeExt/HeckeSignSplit` (E3, the
  production `ι^*`, in `Hecke/` and the ext layer respectively — the split follows the guard's
  rule 1, exactly as `HeckeConeAction`'s placement did); `HeckeExt/HeckeExtFinal.h`,
  `HeckeExt/HeckeExtRecord.h`, `HeckeExt/HeckeExtReport`, `HeckeExt/HeckeExtDriver` (E2);
  `HeckeExt/HeckePredictions`, `HeckeExt/GloverFactors` (E6);
  `HeckeExt/RegisterHeckeExtensionVerbs` (console C1b) — **the one place the extension layer
  includes `Console/`**, admitted by one exact-path entry in each of the two guards' rule 2
  ([OD] slot-4 confirmation 4), rule 1 of each untouched.
* **§5 — the duplicate row is resolved.** v1.7 listed `HeckeExtRecordValidation` twice, for two
  different bodies of work. They shipped as **`HeckeExtRamanujanValidation`** (standard, 295
  checks, the Claim 8.1 arm through the driver, WP-2) and **`HeckeExtRecordValidation`** (fast,
  381 checks, the schema arm, WP-1). `HeckeInvolutionValidation` shipped at 2954 checks.
* **§8 — the slot-4 outcome and the slot-5 re-cut.** Delivered: E2a + E2b (Lane B1), E3 (Lane A),
  E5 cost (Lane A), console C1b (Lane C), the content-keyed census and the first two E6 units
  (Lane B2), and the document chain [C] v1.6.0 → v1.6.1 → v1.6.2, [E] v1.5.0 → v1.5.1 → v1.5.2,
  [P] v3.2. **Deviations from v1.7 §8's slot-4 row, recorded**: `HeckePresentation`, the campaign
  per-cell integration, the add-only golden emission, the atlas driver skeleton and
  `HeckeCanonicalField` all **moved to slot 5** — the last two by the [S4] audit, because the
  canonical field's performance gate needs `--bench ext` and the skeleton drives
  `HeckeExtDriver`, both of which land late in slot 4 ([S4] §3 WP-10, [OD] slot-4 confirmation
  3). WP-10 of the slot-4 plan therefore did not run and is slot 5's, as planned.
  **Slot 5** carries: E2 *cont.* (campaign integration with `ext` / per-cell grouping /
  `summary.tsv` columns, `HeckeExtDeterminismValidation`, `HeckeExtCampaignValidation`, the E3 /
  E4b / E5 complex objects and `les_maps`, `DicksonMultiplication`, the add-only golden emission,
  M1); Lane B2 = the atlas driver skeleton, the E3 record integration, `HeckeCanonicalField`, E6
  *cont.*, and the [C] / [E] normative findings this version records that WP-8 did not take;
  Lane A = E5 acceptance, including whatever the owner decides about (d) and, if it stands, the
  cone on the tape; Lane C = C5's early scripts.
* **Open, and nobody's to decide but the owner** (carried from the WP-9 referee report, §4):
  (1) `ConeCertificate` item C11 gates **both** identities of `eq:conedims` on a stored
  `H²_eq = 0` while [C] clause (v) says the first may not be conditional — the clause is not
  false (the unconditional identity is assigned to the validation arm, and
  `HeckeConeValidation`'s G5 arm asserts it on all 74 cells), but splitting C11 so the
  certificate itself carries it is **slot-5 code**; (2) `obl:coneexact`(iii)'s `ℓ ∈ {2,3}`
  carve-out is weaker than clause (i) already proves, so asserting the `r`-half at every `ℓ` is a
  candidate for the next `X`; (3) whether WP-9's B1 pointer repair belonged to that pass —
  **decided by the slot lead: B1 stays**, minimal and pointers-only, and [C] v1.6.2 completes it.
* **Operational findings** (real, and they cost time in this slot): worktrees are created off a
  **stale commit** (`584a06e`), so every package had to `git reset --hard` to the integration head
  before starting; `docs/latex/build_gl2_contract.sh` needs `BIBINPUTS=docs/latex:` for an
  out-of-tree `outdir`; and a citation *fragment* written into a report or a plan is itself a
  citation site, so a document that discusses the census can self-trigger it — which bit WP-6
  twice.
* **Not changed**: everything else; the v1.7 changelog below stands.

**Version 1.7 — 2026-09-17. Slot 3 close ([S3] WP-11): the slot-3 outcome recorded, the schedule
re-cut from it, the stale figures the packages measured corrected.** Sources:
`docs/implementation/slot3/` (WP-1, 2, 3, 5, 6, 7, 8, 10 reports, the WP-9 referee report, the
WP-11 close), the slot-3 plan `hecke_extensions_slot3_plan.md` [S3] with its audit. No phase changes
its mathematics. Changelog:
* **§9.3**: the slot-3 verdicts — WP-1's **diagnosis** (the site is `alg:tau` step 1, not the coset
  construction), **reach** (`ℓ ≤ 23170`, `certify()` clause (e)), **frozen constants** and admission
  table; WP-2's measured costs and acceptance (d)'s two readings; WP-3's `(2, 30)` timing and the
  per-mode sub-block order; WP-5 / WP-6's clause verdicts and the `(10, 691)` numbers; C1a; the
  census; the documents; the post-slot-3 performance reference.
* **§0.4 C-A3, §5 `HeckeConeValidation`, §6.2 E5 (c)**: `dim X_3 = 3` and
  `Hom(ker r^1, coker r^0) ≅ F^2` at `(10, 691)` (measured, `rank r^1 = 1`), replacing `4` / `F^3`.
* **§1.5, §2.2 Stage 1, §6.2 E2 (e), E6, R14**: the `u_ell` constants frozen as
  `(ell+1)(0.123152 + 2.24985·10^{−4}(n+1)²)` (`u_ell_rss/v2-2026-09-17`); the admitted ranges
  shrink — `ell ≤ 13` to `n ≤ 804`, `ell = 691` to `n ≤ 110`, `ell = 10007` to `n ≤ 18`; the Kummer
  verdicts unchanged (WP-1 finding 3).
* **§6.2 E1 (d)**: recorded at 20.1 % of the same-family run / 38 % of the one-prime baseline; the
  reading is an owner confirmation for slot 4 (WP-2 §7 item 2).
* **§1.1 placements**: `HeckeConeAction` in **`Hecke/`**, with the corrected reason (the guard's
  rules 1–2, not a shared helper); the restriction `r^•` lifted pipeline-side as
  `Hecke/SL2ZBoundaryPair`; `EquivariantMappingCone`, `HeckeExt/HeckeSturmSweep`,
  `HeckeExt/HeckeUEllBudget.h`, `QuadPointT<I>` shipped; `HeckeSettings` with `strict` implemented
  and `u_ell` / `sturm` / `sturm_unavailable` registered.
* **§5 names** as registered: `HeckeConeValidation` (the complex) + `HeckeConeActionValidation`
  (the action) beside `HeckePairHomotopyValidation`; `HeckeExtSturmSweepValidation` (the real-block
  arms of `HeckeExtAlgebraValidation`'s row); `HeckeUEllReachValidation`, `HeckeUEllReachSlow`,
  `HeckeUEllBudgetValidation`; `ConsoleScriptValidation` and `ConsoleCliPreservationValidation`
  (C1a); `ContractCensusValidation`; `HeckeLocalityValidation`'s strict arms shipped. The
  single-entry `h` tamper cannot fail *exactly* (v); the `ξ` arm carries that (WP-6 finding 5).
* **§8 (the schedule re-cut)**: slot-3 outcomes per lane; **E2 starts in slot 4**, not slot 3, and
  carries the `u_ell` resume (R3.3 item 4) moved out of E1b ([S3] §2.3 items 1–2, §6 item 3);
  **E3 moved to slot 4, head of Lane A**, ahead of E5 core *cont.* ([S3] §6 item 4); Lane B2 of
  slot 3 ran the contract revision; M1 (slot 5) unmoved.
* **Not changed**: everything else; the v1.6 changelog below stands.

**Version 1.6 — 2026-09-16. Slot 2 close (WP-13): the slot-2 outcome recorded, the schedule re-cut
from it, the wording corrections the packages asked for.** Sources: `docs/implementation/slot2/`
(WP-1, 2, 4, 5, 7, 8 reports; the WP-9/10/11/12 document reports), the slot-2 plan
`hecke_extensions_slot2_plan.md` [S2] with its audit. No phase changes its mathematics; what
moved is *when* and *under which name*. Changelog:
* **§9.3**: the slot-2 verdicts — the **re-baseline record** (exactly the 384 predicted
  `report_*` lines, 0 elsewhere, 0 splits; digest `0x2fa804dae5e9d98d → 0xe446b3bd2d28bd6e`;
  ten allow-listed key paths), WP-1's **performance numbers** and the split-branch **coverage
  statement**, WP-7's **diagnostics' verdicts** (`cochain_commutes` and `eta_zero` false on all
  315 pairs; the Eisenstein joint eigenspace **2-dimensional at every Kummer cell**; Harder
  `consistent` on 37/37; **`H^1_! ≠ H^1` at every Kummer cell**; the "`≥` at Dickson loci"
  expectation refuted on 3 of 6), WP-8's **`η`-table verdict** (non-zero on 5 266 of 7 504
  slots, `eta_zero` false on all 152 tables), and the **`U_ell` entry unchanged**: WP-3 did not
  run, so the reach limit stands as recorded and the RSS constants are **not frozen**.
* **§8 / §6.2 (the schedule re-cut)**: E0b split into WP-1 (the loop, `HeckeSettings`), WP-2
  (the re-baseline) and **WP-6 (strict mode), which moves to the head of Lane B2 in slot 3** —
  `locality = strict` is accepted and throws `hecke::NotImplementedInThisBuild` meanwhile
  ([S2] §6 item 3, owner-confirmed); **E1b-0** (the `U_ell` reach repair + RSS re-fit) was pulled
  into slot 2 as WP-3, **did not run**, and returns to slot 3 at the head of Lane B1 ahead of
  E1b proper; **E5 core** started in slot 2 with the `η`-table (WP-8, accepted), the cone is
  slot 3's; **Lane C ran the four document packages** ([C] v1.4.0/v1.4.1/v1.4.2, [E] v1.4.0,
  [P] v3) in slot 2, so **console C1 starts in slot 3** as C1a (WP-14) and runs through slot 4,
  possibly 5, cut behind E0b per [P] v3 §10 — Track C gates no engine phase, so M1 and the slot-5
  deliverable do not move; `label_census.sh` (WP-15) is a slot-3 filler.
* **§5 (validation names that deviate from this plan's, recorded per [S2] WP-13 step 8)**:
  `HeckeBoundaryValidation` is **three registered names** (`HeckeBoundaryTauValidation`,
  `HeckeBoundaryOperatorValidation`, `HeckeBoundaryParabolicValidation`); the `η`-table's arms of
  `HeckeConeValidation` are **`HeckePairHomotopyValidation`**, the cone's will be a second name;
  `HeckeExtAlgebraValidation`'s row is split into the arms done (WP-4, WP-5) and the real-block
  arms (E1b); `HeckeLocalityValidation` is `standard` (≈ 6.4 s), its strict-mode arms WP-6's.
  The names `HeckeUEllReachValidation` / `HeckeUEllBudgetValidation` of [S2] WP-3 were never
  registered (WP-3 did not run).
* **§1.1**: the `HeckeExt/` namespace is **`hecke_ext`** (WP-5 deviation 8 — `HeckeIdentityCertificate`
  moved from `heckeext`; the name is in no emitted text, value-preserving); the placement table
  marks what shipped (`HeckeSettings`, `HeckeBoundaryDiagnostics`, `HeckePairHomotopy` +
  `HeckeIntegerSolve`, `HeckeExt/HeckeBoundary`, `HeckeLocalAlgebra`, `HeckeGenerationCertificates`).
* **§1.3 `CommutantCertificate`**: `verify()` **must not pin the RCF basis** — any valid `R`
  verifies (a rescaled cyclic block is another RCF basis and passes; a perturbed image column or a
  swapped column inside a cyclic block fails clause 12) (WP-5 §4). `kCommutantBudget = 2·10^10`
  is a **named constant, not a setting** (R3.3's closing sentence; a setting only if a consumer
  asks, and then a mathematical one under R1) (WP-5 item 6).
* **§1.3.1**: R3.2 — a *computed* `dim C > dim A_S` is equally a proof that (b) fails and carries
  the same reason `closure_unreachable` (WP-5 item 5); the tri-state is one type in the record
  layer — `HeckeGenerationCertificates` reuses `SturmFinal` until E2 owns `Final` (WP-5 item 4).
  R3.3 item 2's record column — a block surviving the budget is `final = false` with reason
  **`budget_exhausted:locality`**, not `not_local`: budget mode never *proves* non-locality (a
  genuinely non-local block splits), so `not_local` is reachable only from strict mode's
  interruption path (WP-1 finding 3).
* **§1.6**: `e0b.keys` holds **ten** paths — `degrees` joins as the fourth per-complex field
  ([S2] §2.3 item 1, owner confirmation 1(b)); `HeckeReportInput::num_degrees` is **required** by
  the writer (throws on 0), so E2's `hecke_ext/v1` writer must supply the complex it describes;
  `P` is emitted **keyed by prime**; `resumable` is **not** in the report; `level_c.locality`
  carries the value and source, **not** the `MathSettings` fingerprint (that is the ext record's
  and the job id's, E2) (WP-2 findings 3–5).
* **§3.1 step 3**: the budget caps the **candidate sequence of R3.3 item 2, trivial witnesses
  included** — one sequence, one attempt index, so `run(64) + resume(128) == run(128)` is a
  prefix property (WP-1 finding 1; no value changes: every golden block certifies at index 0).
* **Not changed**: everything else; the v1.5.1 changelog below stands.

**Version 1.5.1 — 2026-09-16. Slot 1 close (WP-7): the verdicts written, four wording repairs the
packages asked for.** No phase, effort, default or schedule changes. Changelog:
* **§9.3**: the three verdicts WP-7 owns this slot are written in — the E0a **grid-locality
  verdict** (every block on the golden grid local, `witness_changes = 0`, so E0b's re-baseline is
  exactly the 384 allow-listed report lines and owner confirmation 5 is moot), the **`(160, 691)`
  probe verdict** (seven blocks, all local, the *first* alternative of §3.4), the **`U_ell` RSS
  measurements** with the two fits and the **exact-integer overflow** finding (the `(16, 43867)`
  point cannot be run; threshold between `ell = 3617` and `5003` at `nu = 1`), and the **E0a-binary
  performance reference** for E0b's ±5 % gate.
* **§1.1**: `HeckeSturmBound`'s include list is `SubspaceOps`, `FpPoly`, `Matrix`, `ModArithmetic`,
  **`EngineCheck`** and **`Fnv`** (both dependency-free; the first because the assertion policy of
  CLAUDE.md forbids a bare `assert`, the second because R3.1 item 6's integrity hash is the one
  FNV) — the rule `check_heckeext_includes.sh` enforces (WP-3 deviation 2, WP-2/WP-3 integration).
* **§1.2**: the `SturmBound` row says what the certificate stores on a `none_at_cap` outcome (the
  primes `≤ cap`, there being no `B'`; `verify()` clause 4 checks exactly that list) (WP-3 item 4).
* **§1.3.1 R3.1**: item 3 says explicitly that "the same state, entrywise" means *modulo
  `budget_history`* — item 4 makes `[b_1, b_2]` versus `[b_2]` unavoidable, and the validation
  asserts both the agreement modulo the history and the difference of the histories (WP-3 item 1);
  item 6 says who sets the sidecar stem (E2, the record layer; WP-3 provides the field and the
  writer, and inlines with `state_oversize` when no stem is set) (WP-3 item 3). The `state_ref` /
  `state_fnv64` hash is `engine::FnvBytes` from the **standard** FNV-1a-64 offset basis
  `0xcbf29ce484222325` (WP-7 switched it from WP-3's historical seed; nothing had pinned a value).
* **§2.2 Stage 4(c)**: `B'(258, 691) = 2` joins the recorded values (measured, 1.4 ms — the
  `k ≤ 258` anchor of §6.2 E1 acceptance (d)) (WP-3 item 5).
* **§3.1**: the `k = 1` analytic character is `P = X mod π_w` — the constant `α` at `f = 1` — not the
  unreduced `X`, so that `deg P < f` holds and the analytic and matrix paths agree at `f = 1`
  (WP-1 finding 3; `[E] cl:resfield` and §7 say the same since [E] v1.3.3).
* **Not changed**: everything else; the v1.5 changelog below stands.

**Version 1.5 — 2026-09-16. The consequential revision: the owner's OQ1–OQ18 decisions and the
eleven slot-1 confirmations applied (WP-6 of `hecke_extensions_slot1_plan.md`).** Applies [OD]'s
"Consequential revisions pending" items 3–8 and 11 and the corrections of the slot 1 plan §2.3 (its
audit's WP-6 items included). Every owner-dependent default of v1.4 is now a **decision** — the owner
answered all eleven slot-1 confirmations "yes" on 2026-09-16 ([OD] "Slot 1 confirmations") — and is
recorded as such, not as open. The binding contract is the unified `docs/latex/gl2_contract.tex`
(**[C]**, v1.3.2; `hecke_action.tex` is frozen inside it since v1.0.0), cited by label only. §1.3.1
(the resumable-state contract, R3) landed in a first commit of its own so that WP-3 could start; a
standalone copy is `docs/implementation/slot1/WP-6_resumable_state_excerpt.md`. Changelog, section
by section:
* **Header / status / evidence base**: branch `hecke-extensions` @ `0fb142d` (68 registered
  validations, 29 `Hecke*`); [C] = `gl2_contract.tex` v1.3.2; [E] v1.3.2; the sources [OD], [V],
  [B], [R], [SP] (the slot 1 plan) and [SPA] (its audit) named.
* **§0.2**: E7 is **scheduled** (OQ4), with the pairing map at three levels; two new phases **E8**
  (`Z/ell^k` coefficient rings, OQ18) and **E9** (the free `Γ`-model — the OP4 / OC-1 construction,
  host of the six tests of [R §5]); the E4 row names the split E4a / E4b and the recorded
  circle-model flags (confirmation 11).
* **§0.3**: the `Z/ell²` non-goal **replaced** by the stated first extent of E8 (the reduction
  `Z/ell^{k+1} → Z/ell^k` and the `a = b = 1` Bockstein; D6's socle semantics stays the published
  one until an E8 run exists — confirmation 9a); the `F_{ell^r}` element-type non-goal
  **re-examined for OQ10 and kept**, with the E6 performance gate as the only trigger to reopen it;
  the reach reframed as hardware-bounded (OQ12), the first ext campaign at `n ≤ 200`
  (confirmation 9b); the bit-identity bullet names the one re-baseline of slot 2.
* **§0.4**: retitled to the unified contract, with the C-A1…C-A4 → [C] label map and every gate
  marked **met**; the OC-1 construction pointed at E9.
* **§1.1**: `SubspaceOps`, the boundary datum / operator and the `η`-table live in **`Hecke/`**
  ([SP §2.3] items 5, 7); `Fnv.h` is **`ModArithmetic/ModArithmetic/Fnv.h`** ([SP §2.3] item 6),
  and WP-1's golden lookup is the one `GoldenLookup` console C1 consumes (in `Golden/`, not
  `Util/`); `Hecke/HeckeSettings.{h,cpp}` (R1) placed; the two migration-guard allow-lists named
  as shared, append-only files.
* **§1.2**: rows `MathSettings` (R1), the `resumable` objects (R3), `ContragredientLocalSystem` /
  `Pairing` (R4), and the `q_max` / `truncated` / `q_max_source` / `degrees` fields (OC-1) on
  `ConeCohomology` and on the report; `coefficient_ring` admits `Z/ell^k`.
* **§1.3**: `is_final` restated as the tri-state of §1.3.1 R3.2, with the fixed reason list and the
  default-mode disposition (confirmation 8); **§1.3.1** (R3) as delivered in the first commit.
* **§1.4 / §1.5**: the **settings layer** (R1) — the table of mathematical settings with campaign
  keys, record keys, values and the **decided** defaults (confirmations 4, 6, 7, 8); golden objects
  pin the default configuration; a non-default setting changes the hash input and the campaign job
  id (`_s<fingerprint>` suffix; the default id is unchanged); the new campaign keys `final_mode`,
  `sturm_unavailable`, `locality`, `field_polynomial`, `split_field_report`, `coefficient_ring`,
  `predictions`, `presentation`, `integral_fallback`, `q_max`.
* **§1.6 / §3.3 / §3.4**: E0b's re-baseline **batches the oc1a record fields** (`q_max`,
  `truncated`, `q_max_source`) and the `level_c.locality` settings object (confirmation 3, a `Y`
  bump of [C]); the `golden_explain.py` allow-list keys named; the prediction is 384 lines in
  exactly two kinds; `hecke_report/v2` is the **one** re-baseline of the stage (slot 2); the
  `file:line` drift of [SP §2.3] item 8 repaired (`GoldenHarness.cpp` `:363`, `:488-510`, `:620`,
  `:165-173`); `tau_table_p2.txt:13-15,35` (the file regenerated by [RB §4]) — the claim "the
  shipped `τ` is not a map of pairs" still holds.
* **§2.2**: Stage 4(c) gains the **heuristic-sweep mode** (OQ15); Stage 5 the **on-request
  presentation** `presentation(m, group)` (OQ11) with its algorithm; Stage 6 the **canonical field
  as the default report form** with the **performance gate** and its fallback (OQ10).
* **§3.1 / §3.2**: the **strict locality mode** (OQ16, confirmation 7): after the linear family, a
  **terminating** route — the Berlekamp subalgebra of `A_S / rad A_S` (Frobenius is `F_ell`-linear)
  splits deterministically until every block is local, then a residue witness is searched over the
  *whole* residue field, which its proper subfields never cover — with the proof sketch, the cost,
  the constructed `(ell, f) = (2, 30)` arm where every linear witness lies in a proper subfield, and
  the rule that strict mode is byte-identical to budget mode wherever the latter certifies (so the
  golden reference is the same in both modes).
* **§4**: item 5 restated with the tri-state; new item 7 (a setting is part of what a value means).
* **§5**: `HeckeLocalityValidation` strict arms; `HeckeSturmBoundValidation` both
  `sturm.unavailable` modes and the resume-invariance arm; `HeckeExtRecordValidation` tri-state
  `final`, `settings`, `resumable`, the oc1a fields; `HeckeExtAlgebraValidation` commutant resume;
  the OQ14 **asserted** prediction cases named (`(10, 691)`, the ten Kummer cells, `(6, 5)`,
  `(12, 5)`, `(8, 7)`) and the `predictions = assert` switch; new rows
  **`HeckePresentationValidation`** (E2), **`HeckeDualityValidation`** (E7),
  **`HeckeReductionValidation`** (E8), **`HeckeFreeModelValidation`** (E9: the six tests of [R §5],
  test 6 as the negative control).
* **§6.1 / §6.2**: E4 **split E4a / E4b** (E4a in slot 1 as WP-4a/4b; `HeckeBoundaryValidation`
  registered by E4a and extended by E4b; E4b's golden objects ride E2's add-only emission); E7
  **re-priced 1.25 AU** (the pairing map at three levels, the perfectness / adjointness
  certificates) and unconditional; **E8 2.0 AU**, whose **first item** is the `ENGINE_API.md`
  composite-modulus / non-field-elimination section (what it must contain is stated); **E9 2.5 AU**
  with its contract prerequisite **C-A5** (the concrete refinement of OD-T1 and a free model
  satisfying [C] `G1`–`G4`, an `X` bump by a contract author) and the six [R §5] tests at
  `truncated = true`, `q_max ≥ 5`; effort table and totals recomputed: **18.5 AU / ≈ 31.5 k lines**
  (E0–E9); the six-group record (E0–E5) unchanged at 11.0 AU, M1 at 5.25 AU.
* **§6.3**: R1 (HPC / device memory, OQ12), R4 residual (ii) → E9, R11 (`Z/ell²` is no longer scope
  creep), R15 (what remains), new **R19** (strict-mode cost), **R20** (E9's triangulation is a
  direction, not a construction), **R21** (E8's non-field elimination must not touch the `F_ell`
  path).
* **§6.4**: rewritten — every question decided; the eleven slot-1 confirmations listed; what is
  still owed (OQ13's LMFDB lookup at E6; C-A5; the E6 gate's verdict; the proposal *not* to reopen
  the `F_{ell^r}` non-goal).
* **§6.5**: `Z/ell²` removed (it is E8); `Z/n` general, Conway (tied to `field_polynomial`), and the
  `F_{ell^r}` type (only if the E6 gate fails) recorded.
* **§7**: types `ContragredientLocalSystem`, `Pairing`, `Presentation`; verbs `dual`, `pairing`,
  `presentation`, `resume`; the mathematical settings through the registry; `ConeCohomology`
  exposes `q_max` / `truncated` / `degrees` / `q_max_source`; the `Fnv.h` / `GoldenLookup` pointers
  for [P] (the [P] revision itself stays out of scope, [SP §5]).
* **§8**: the schedule **re-cut from today** — slot 1 as [SP §4.1]'s lanes (E0a, E1s, E4a, C0, this
  revision), E0b + the one re-baseline in slot 2, E5 core in slots 2–5 (accepted in slot 5), the
  cross-routes in slot 6, **E7 slots 6–7, C-A5 slot 7, E8 slots 7–9, E9 slots 8–9**; the spec
  freeze gated on the probe (OQ17: WP-7 writes the verdict into [E §8.2] in slot 1; the [E] v1.4
  revision of slot 2 is the freeze candidate).
* **§9.2**: every "default assumed" replaced by the decision and the section where it now stands;
  the slot-1 confirmations table added.
* **§11**: pointer from the OC-1 construction to E9.
* **Not changed**: §9.3 (WP-7 owns it this slot), §10, §11.1–§11.2, and every historical changelog
  entry below this one (they keep their own `file:line`s and paths, e.g. `Util/Fnv.h`, as written).

**Version 1.4 — 2026-09-15. The owner's OQ2 decisions applied; §11 is now a decision record.** The
owner has **decided all eight open points** of the OQ2 verdict [V §8], following its recommendation
on every one with **three amendments**: **OP3** commits **both** cone cross-routes (not one),
**OP5** fixes the boundary group as `Γ_∞ = ⟨T⟩ × ⟨−I⟩` (the Borel option, *infinite in degree at
`ell = 2`*), and **OP6** is confirmed as already applied. Every inline OQ2 open-point tag is **gone**: each
passage v1.3 had written to keep both answers reachable is collapsed to the decided answer (§0.4
C-A2(i)/(ii), C-A3(ii.2)/(ii.3)/(ii.6)/(ii.7)/(iii)(6), §1.2, §1.6, §5, §6.2, §6.3 R4, §6.4, §8,
§9.2, §9.3), and **§11 is rewritten as the decision record** (one row per point: decision, date,
followed/amended, where it is now stated). Substantive consequences: OP5's `ell = 2` case is stated
in full (`H^q(Γ_∞; V) ≠ 0` for every `q` when `2 ∉ R^×`, so the boundary, the bulk and the cone are
all unbounded above and (3.1) is a *window*), and the truncation policy it needs is recorded as the
**open construction item OC-1**, explicitly *to be determined in the contract* and not invented here
(§0.4 C-A2(i)) — **decided there on 2026-09-16** as `oc1a` ([C] v1.3.0 `open:ell2`, [OD §OC-1];
pointers at §0.4 C-A2(i), §6.3 R4, §11 OP5, §11.1). OP3's amendment forces an honest re-cut of **E5 to 3.25 AU** (`2.5` core `+ 0.5`
strict pair `+ 0.25` relative complex, derived part by part in §6.2), hence totals of
**12.75 AU / ≈ 22 k lines** and a slot-7 Lane A that is committed rather than optional. Two
mathematical errata found by the 2026-09-15 corpus survey are recorded: **§11.1 item 5** ([V §2.8]'s
`T_p^2 = T_{p^2} + (p+1)p^n` — the coefficient is `p`, verified three ways; the same error in the
working note `hecke_extensions_mathematics.md:63` is **fixed in place**), and the new **§11.2**
([C]'s `obl:algebra` and oracle 6 prescribe comparing the *primitive* double coset against the
*full* operator, off by `p^n I`; the code is right, [C] is **not** edited and the erratum **must** be
carried into the forthcoming unified contract).

**Version 1.3.1 — 2026-09-15. Audit of the OQ2 revision applied.** An independent audit of v1.3 /
spec v1.2 (1 blocking, 5 should-fix, 5 nits) found no error in the mathematics and none in the
transcription of [V]'s *results*, but four defects worth naming: the spec claimed the **bulk** `τ`
exists over `Z` for every `ell` (it does not — only `τ_∂` and `η` do; **F1**, fixed in spec v1.2.1);
§1.6 and §5 claimed the **cone bases move** under a change of `η` or `τ_∂` (they cannot — `D` involves
neither, so §5 prescribed an assertion that would fail; **F2**); E4's gate was stated three ways
(**F3**, now `C-A2 + C-A3` in §6.1, §6.2 and §8 alike); and §11's completeness claim was false —
seven untagged passages *apply* the OP1 decision and one applies OP4, so they are now listed
(**F6**). Also: the topological hypothesis on `X` that carries the whole theorem is stated
(§0.4 C-A3(ii.1), **F5**); the effort table is relabelled v1.3 (**F7**); OP4 gains a deadline
(§6.4, **F8**); two stale sentences and the OP8/OP3 mix-up are fixed (**F9**, **F11**); the OP5
passage now records that [V]'s *argument* section leans the other way than its §8 (audit §5 item 1); R15
records that C-A3 acceptance is now a **slot-2 blocker for both E4 and E5** (audit §5 item 5); and
**§11.1 is new** — an errata list for the four loose arguments *inside* [V], so a contract author
copying [V]'s arguments is warned. [V] itself is a published review document and is **not** edited.

**Version 1.3 — 2026-09-15. The OQ2 consequential revision.** Applies the independent verdict on
Owner Question 2 (the Hecke action on the mapping cone),
`docs/implementation/hecke_extensions_OQ2_verdict.md` (**[V]**, CONFIRM WITH AMENDMENTS), section by
section per its §7. **Nothing outside the OQ2 consequences has been changed**; the other
"Consequential revisions pending" of [OD] are still pending.

**Changelog v1.2.1 → v1.3** (every item keyed to [V §7]):
* **§0.4 C-A3(ii)–(iii) replaced** by [V §3]'s drop-in text. The formulation is **(b\*)**: the Hecke
  datum of the pair is the triple `(τ, τ_∂, η)` **over `Z`** — the bulk `τ`, a `g`-twisted chain datum
  `τ_∂` on `∂X`, and a certified **pair homotopy** `η: C_*(∂X) → C_{*+1}(X)` with
  `∂η + η∂ = jτ_∂ − τj` — and the cochain homotopy is **derived**, `h := η̃`. Well-definedness is now
  a **theorem**, not an obligation: (b1) holds with the recipe and its proof ([V §2.4]–[V §2.5],
  PROVED over `Z` for all `ell`), (b2) is dropped, and the operator is the geometric one on the
  Borel–Serre pair for `6 ∈ R^×` ([V §2.6]). The v1.2 **sign stands** (`dh + hd = Θ_g^∂ r − rΘ_g`,
  `Φ_g(a,b) = (Θ_g a, Θ_g^∂ b + h a)`) — and [XA §3.6]'s opposite sign was **wrong** (§10.2 M6).
* **The [Q2] branch rule is withdrawn.** The entrywise cochain identity `rΘ_g = Θ_g^∂ r` does **not**
  license `h = 0` ([V §2.7]); `h = 0` is admissible **iff** `η ≡ 0`, i.e. `τj = jτ_∂`, which the
  shipped `τ` fails (`tau_table_p2.txt:14-15,35`). The identity and the cusp-support walk become
  **recorded diagnostics that gate nothing** (§0.4 C-A3(iii)(5), §5, §6.2 E4).
* **§0.4 C-A2(ii):** the boundary datum is the **`Γ`-level `τ_∂` on `∂X`** (same `s_i`, `δ_i` as the
  bulk); the left-coset `(τ_∞, δ_∞, δ_j)` operator is its **Shapiro transcription** and route A of
  `HeckeBoundaryValidation`.
* **§1.2 data model:** new rows `HeckePairDatum` (the three tables over `Z`, degree-generic, on an
  abstract `Γ`-pair; `solve_regime` per table; **no cochain-level `h` is ever stored**) and
  `ConeCohomology` (with `coefficient_ring` and the diagnostics); the integrality caveat on
  `HeckeTauTable`'s mod-`ell` fill fallback (`HeckeTauTable.h:76-88`) recorded — R-Z, R-ring, R-red,
  R-LES and R-resume are all reachable from it.
* **§1.3 certificates:** `TauBoundaryCertificate` stores `τ_∂`, not `τ_∞`; **new**
  `PairHomotopyCertificate` (over `Z` — *this* is what pins the operator) and `ConeActionCertificate`
  (over `R`); `ConeCertificate` extended and explicitly labelled as **silent about the Hecke module
  `X_3`**.
* **§5 validations:** `HeckeConeValidation` gains the certificate arms, the two-`η`/two-`τ_∂`
  independence arm and the **tampered-`h` negative control** (passes every matrix identity and the
  whole `ConeCertificate`, changes `A_c^{(1)}` at `(10, 691)`, fails `ConeActionCertificate`);
  `HeckeBoundaryValidation`'s decision test becomes the two diagnostics.
* **§6.2:** E4 delivers `τ_∂` and records the diagnostics (acceptance (d) rewritten); **E5 is
  2.5 AU** (+0.5 for an optional cross-route), so the totals fall to **12.0 AU / ≈ 21 k lines**.
  **§6.3 R4** re-rated **medium/medium**. **§8** re-cut: **C-A3 is finalised in slot 2**, the
  "[Q2] test → C-A3 final" gate is gone, E5 starts in slot 4 and ends in slot 6 — the long pole
  shortens by one slot.
* **§9.2 Q2** is `resolved`; **§10.2 M6** and **§10.4 item 4** record the resolution (including that
  the audit's sign was wrong and that the `Hom(ker r^1, coker r^0)` ambiguity is *real* for a free
  cochain-level `h` and *eliminated* by the `η`-construction); §1.6 fixes the golden tiers; §7 gives
  `ConeCohomology` its new members.
* **Eight points of [V §8] were still the owner's at v1.3** (all eight decided in v1.4, §11).
  They are applied here as **stated working
  assumptions**, every decision-dependent passage carries an inline OQ2 open-point tag, and **§11
  is the flip-list** with every site. (Both are superseded by v1.4: the points are decided, the
  tags are gone and §11 is the decision record.)

**Version 1.2.1 — 2026-09-14.** Owner decisions on OQ1–OQ18 recorded in
`docs/implementation/hecke_extensions_owner_decisions.md` (authoritative where it contradicts this
plan); §9.2's table gains a decision column. OQ2 remains open (Fable brief
`hecke_extensions_fable_brief_OQ2.md`). **The consequential plan revision is pending** — its task
list is the decision record's "Consequential revisions pending"; nothing else in this document has
been changed.

**Version 1.2 — 2026-09-14.** Applies the independent plan audit
`docs/implementation/hecke_extensions_plan_audit.md` (**[XA]**: ACCEPT WITH AMENDMENTS; 3 blocking,
7 major, 19 minor). Every item was re-derived against the spec and the tree before it was applied;
the item-by-item response is **§10**. v1.1 (same day) reconciled the plan with
`hecke_extensions.tex` **v1.1** (the audit response, [E App. B]) and
`hecke_extensions_open_questions.md` (OQ1–OQ18); v1.0 was written against spec v1.0.

**Changelog v1.1 → v1.2** (item-by-item in §10):
* **B1 — no commutant certificate at `(10, 691)`.** `dim C_{M_3}(E_31) = 5 ≠ dim A_S = 2`, and
  `dim V/m_S V = 2 ≠ f`, so neither (a) nor (b) can hold; the unsplit record is final **only** via
  `sturm(2)`. Re-derived here, together with a general **socle bound** (§2.2 Stage 4(b)):
  `dim_F End_{A_S}(V) ≥ dim A_S + f·t·s − dim_F soc A_S` (`t`, `s` = top and socle dimension over
  `F`), so (b) can succeed only where `f·t·s ≤ dim_F soc A_S` — **never for a non-cyclic module over a
  Gorenstein `A_S`**, hence never at any Eisenstein–cuspidal Kummer block nor at any
  multiplicity-≥2 block with `A_S` a field. `B'(k, ell)` recomputed **= 2 on all ten Kummer cells**
  of [E Claim 1.8] (§5), so they are all final via `sturm(2)` with no `U_ell`. Every pinned
  `certificate` value was re-checked (§10 B1).
* **B2 — `CommutantCertificate` is now a certificate.** `verify()` re-derives `dim C` (RCF check of a
  fixed cyclic-most element, deterministic rebuild of the `End_{F_ell[a]}(V)` basis, rank of the
  stored linear system); (b) is attempted only when the socle bound admits it and the system fits a
  fixed modmul budget, otherwise it records `excluded_by_socle_bound` / `over_budget` — never a
  silent naive fallback. Honest cost `O(k·D²·u²)`, `u ≤ m·D` (§2.2 4(b)).
* **B3 — `U_ell` coset budget.** A deterministic RSS model `cosets·(0.11 + 5.8·10^{−5}(n+1)²) MB`
  (fitted on [I §3.4], re-fitted in E0a) with campaign key `u_ell = auto | off | budget_mb=<M>`
  (default 2048 MB); the Sturm **proof** sweep contains `ell` only when `ell ≤ B'` ([E Claim 2.10]
  already covers `T_ell` on non-Dickson `m` of `X_4`); `U_ell` is removed from the default campaign
  family at large `ell`, from the golden ext objects, from E2 acceptance (e) and from the `ell = 691`
  atlas above `n ≈ 220`.
* **M1/M2 — E0 split into E0a and E0b.** E0a is value-preserving (`GoldenDump`, `golden_explain.py`,
  a read-only `CertifyLocality` arm asserting all **four** decomposition hashes
  `_invariants/_certify/_witness/_U` on every grid cell with `dim H^1 > 0`, `Util/Fnv.h`,
  `DicksonInvariantCount`, the `(160, 691)` probe, the `U_ell` RSS measurement); E0b is the fix and
  the re-baseline. The golden-visible change site is **`HeckeReport.cpp`**, not
  `HeckeModuleDecomposition::to_json` (which is unhashed and bumps separately to
  `hecke_module_decomposition/v2`); the second false note at `HeckeModuleDecomposition.cpp:980-983`
  is fixed too.
* **M3** ext golden objects and identity gates only on `n > 0` even, `5 ≤ ell < 2^32`; `excluded`
  elsewhere. **M4** resource numbers corrected (cohomology once per cell; `(16, 43867)` ≈ 5.6 GB with
  `U_ell`). **M5** cross-block identity of ideals by an evaluation test with either block's own
  witness. **M6** (**superseded in v1.3**: the [Q2] branch rule is withdrawn, §10.2 M6) the [Q2] decision
  is the entrywise cochain identity `r^•∘Θ_g = Θ_g^∂∘r^•` (end of E4); C-A3(ii)(b) drafted from day one with degree, sign (corrected: `dh + hd = Θ^∂r − rΘ`, cone map
  `(a, b') ↦ (Θa, Θ^∂b' + ha)`) and the `h`-ambiguity `Hom(ker r^1, coker r^0)` as an explicit
  obligation. **M7** units for [E §5.1] identity 6 (Glover / Ash–Stevens), "image of `W` in each
  layer", Stage 2(3)'s re-run with `S_sep`, Stage 6's per-`ρ̄` pair for `ell ≤ 31`.
* Minors m1–m19 applied (§10). New risks R14–R18. §8 is now one explicit day-one schedule (≤ 4
  concurrent agents per slot). Effort recomputed: **12.5 AU / ≈ 21.5 k lines** (13.5 AU with E7),
  **M1 = 5.25 AU**.

**Changelog v1.0 → v1.1** (details and the spec-change → plan-section map in §9):
* Certificate (c) is no longer "primes `≤ B(k)`": it needs a per-`(k, ell)` **computed and recorded
  bound `B'(k, ell)`** ([E Def. 2.8], [E Claim 2.9], [E Cert. 5.7]), which may not exist. New unit
  `HeckeSturmBound` (E1), new `SturmBoundCertificate`, a fourth `GenerationCertificate` outcome
  `unavailable`, `is_final` re-defined (§1.3), campaign key `sturm = auto | off | cap=<B_max>` (§1.5),
  new `HeckeSturmBoundValidation` (§5), the Sturm counterexamples `(22, 5)`, `(26, 7)` and `(32, 131)`
  pinned (§5). OQ7 is moot; OQ15 replaces it.
* The locality certificate and Stage 3 use the **Teichmüller lift `ŵ = w^{ell^N}`** ([E Claim 3.3],
  [E Cert. 5.2], [E Alg. 5.4]): `n_p = t_p − P_p(ŵ)` for **every** `p`, the witness direction
  included; `P_p` by the deterministic `ker π_p(t_p) ∩ ker π_w(w)` solve; `m_S = (n_p)_p` with no
  separate `π_w(w)` generator; the tangent test is a **`K`-span** test. §1.2, §1.3, §2.2 Stage 3, §3.1,
  §3.2, §5 (`HeckeLocalityValidation`, `HeckeExtAlgebraValidation`) rewritten accordingly.
* The Stage 2 refinement loop is **bounded** (64 witnesses per block, then `"local": false`,
  `"final": false`; [E Alg. 5.1(2)]) — the existing `kResidueWitnessMaxAttempts = 64` is the budget
  (§3.1, OQ16).
* The boundary Hecke operator uses the **left-coset representatives** `δ_∞ = diag(1, p)`,
  `δ_j = (p j; 0 1)` ([E (A1)]), **not** `β_j`; boundary characters `χ_b` on the monomials
  `x^{n−bℓ}N^b` of `H^0(∂)`, the **same multiset** on `H^1(∂)`, `[y^n] ↦ χ_0 = 1 + p^{n+1}`, both
  groups `χ_0` for `n < ell` ([E Claim 1.7]). C-A2 (ii)/(v), `HeckeBoundaryValidation`, R9 rewritten;
  the E4 "convention probe" is gone — the spec settles it and the validation asserts it at once.
* D3 Jordan types are in **units of `f`** (nullities of `π_p(t_p)^s` ÷ `f`, [E Claim 6.1] / [E D3]);
  D6's Eisenstein line is **`soc(X⁺_{4,m})` when one-dimensional over `F`, undefined otherwise**
  ([E D6], OQ18); Poincaré duality reverses **socle ↔ Loewy** ([E Pred. 4.6], identity 5 — v1.10: certificate item 7).
* Schema `hecke_ext/v1` gained `local`, `coefficient_field` (`w_hat_exponent`, `P`), `sturm`
  (`B_prime`, `cap`, `closure_dim`, `dim_M_k`), structure-map `matrices`, `commit`, `model`,
  `iota_sign`, `convention_check` ([E §7]); the `hecke_report/v2` keys and the re-baseline allow-list
  follow the spec's names (`local`, `witness_poly`, `coefficient_field`).
* New verified test data: `(10, 691)`: `U_691 = I + 221·E_31`, `c_691 = 542`,
  `3(U_691 − 1) = −542(T_2 + 24)`, `T_691` **active**, `H1_shriek = all`, Eisenstein line = bottom
  Loewy layer ([E Claim 8.1], [E §7]); the Kummer list gains `(22, 103)`, `(22, 2294797)`
  ([E Claim 1.8]); `(160, 691)` is **unverified** (OQ17) and becomes a probe, not an assertion;
  `691 ∥ num(B_200/200)` (OQ13, arithmetic half settled).
* Spec numbering re-keyed to v1.1 (Def. 2.8 / Claims 2.9–2.12 / Claim 3.1 (gap) / Claim 3.3 /
  Certs. 5.5–5.7 / Alg. 5.8 / Claim 5.9); §9 rewritten as the real reconciliation; the owner-question
  table extended to OQ15–OQ18; effort revised (§6.2: **10.25 AU**, M1 **4.5 AU**); one `file:line`
  drift fixed (`HeckeOperatorFamily.h:253`).

**Status:** binding for slots 1–3 of the hecke-extensions stage (v1.5), in agreement with spec [E]
v1.3.2, the unified contract [C] v1.3.2, [OD] (2026-09-14/15/16, slot-1 confirmations included) and
the slot 1 plan [SP]. Branch `hecke-extensions` @ `0fb142d` (2026-09-16; the tree is `main` =
`matrix-engine` @ `584a06e` plus the slot-1 planning documents; matrix-engine Phases 0–6 closed;
Hecke action S0–S14 complete; **68** registered validations, 29 of them `Hecke*`; the campaign of
2745 points published under `hecke_report/v1`). The spec-side consequences of the audit response are
still listed in §10.4 for the spec author; the [E] consequential revision is a slot-2 task ([SP §5]).

**Evidence base.** The mathematical specification `docs/latex/hecke_extensions.tex` **v1.3.2** (cited
**[E]**; its claims by their v1.1 numbers, which v1.2–v1.3.2 preserved, its stages as [E Stage n], its definitions (D1)–(D7), its audit
response as [E App. B]); the audit `docs/latex/hecke_extensions_audit.md` (**[EA]**, items B1–B2,
M1–M5, minor 1–11, amendments §7 1–9); the owner's notes `hecke_extensions_mathematics.md` (**[M]**)
and `hecke_extensions_computational_strategy.md` (**[S]**); the verified capability inventory
`hecke_extensions_capability_inventory.md` (**[I]**, gap list G1–G17); the owner's open questions
`hecke_extensions_open_questions.md` (**[Q]**, Q1–Q18; Q7 moot, Q13 half-settled, Q15–Q18 added in
v1.1); the console plan `docs/console/00-console-interface-plan.md` (**[P]**) and its audit
`01-console-plan-audit.md` (**[PA]**, amendments A1–A16); the audit of this plan
`hecke_extensions_plan_audit.md` (**[XA]**, B1–B3, M1–M7, m1–m19); the binding **unified** contract
`docs/latex/gl2_contract.tex` **v1.3.2** (**[C]**, cited by label only — `hecke_action.tex` and
`monodromy_v5.tex` are frozen inside it since v1.0.0; a `[C, label]` citation in the historical
changelog entries and in §0.4's body refers to the same labels, which the unified contract
preserved); `docs/latex/monodromy_v5.tex` (**[v5]**); the owner's decision record
`hecke_extensions_owner_decisions.md` (**[OD]**, authoritative where it contradicts this plan until
the revision that applies it — v1.5 applies its items 3–8 and 11); the OQ2 verdict
`hecke_extensions_OQ2_verdict.md` (**[V]**); the OC-1 brief `oc1_decision_brief.md` (**[B]**); the
referee report `referee_report_2026-09-16_bulkperiodic.md` (**[R]**); the re-baseline note
`docs/matrix-engine/rebaseline-2026-09-16-iota-symmetric-tau.md` (**[RB]**); the slot 1 plan
`hecke_extensions_slot1_plan.md` (**[SP]**) and its audit `hecke_extensions_slot1_plan_audit.md`
(**[SPA]**);
the matrix-engine plan `docs/matrix-engine/00-implementation-plan.md` (**[ME]**, the model for
rigour and phase discipline) and the Hecke plan + audit (`hecke_action_implementation_plan.md`,
`hecke_action_plan_audit.md`, the precedent of a plan-and-audit pair). Every claim about the code
below carries a `file:line` verified on the tree above (re-verified 2026-09-16 for v1.5 on `0fb142d`
at every site the v1.5 changelog names; 2026-09-14 for v1.1: 45 spot checks over `HeckeModuleDecomposition.*`, `FpPoly.*`, `HeckeOperatorFamily.*`, `HeckeReport.*`,
`GoldenHarness.*`, `CMakeLists.txt`, `HeckeOperatorOnK.h`, `HeckeTauTable.h`); paths are relative to
`Orbifold_Cohomology_of_GL2/` unless they start with `ModArithmetic/` or `docs/`.

**Notation** (binding, [Q1] default; [PA A10] asks for exactly this table): `ell` = the coefficient
prime ([M]/[S] `p`); `p` / `p_hecke` = the Hecke prime ([M]/[S] `q`); `n` / `n_sym` = the
symmetric-power degree ([M]/[S] `k`), weight `k = n + 2`; `q` = the cohomological degree;
`U_ell` = [S]'s `T_p` = `hecke(H, p = ell)`. `D := d_m = dim_{F_ell} H_m`, `f = r_m` the residue
degree, `S` the operator set, `A_S ⊆ End(H_m)` the local algebra, `m_S = rad A_S`, `K = F_ell[ŵ]`
the coefficient field of `A_S` ([E Rmk. 3.2]), `ŵ = w^{ell^N}` the Teichmüller lift of the residue
witness `w` (`f | N`, `ell^N ≥ D`, [E Claim 3.3]), `B'(k, ell)` the computed Sturm bound of
[E Def. 2.8].

**Effort unit.** 1 AU = one engineer-agent workstream of the size the matrix-engine and console phases
were cut into: ≈ 2–4 k lines including its validation and documentation, one review cycle
([P §10]). Line counts are estimates of new code, validations included.

---

## 0. Scope and non-goals

### 0.1 The deliverable

A **certified record of all extension classes for `(n, ell)`** in the sense of [E §4.2] (D1)–(D7): for
every maximal ideal `m` of the Hecke algebra acting on the computable cohomology groups, the local
algebra `T_m` with its invariants, the Loewy / socle series of every group at `m`, the Jordan types
(in units of `f`), the structure maps with their matrices and active tangent directions (over `K`),
the positions of the canonical submodules, and the predictions confirmed / refuted — each statement
carrying a deterministic certificate that a third party can re-verify from the emitted data alone,
and each record hashed into the golden harness and the campaign driver. It is a *record* that
exhibits the modules, not an isomorphism classification into a finite list ([E §4.2]: wild for
embedding dimension ≥ 2, Loewy length ≥ 3, Drozd / Ringel; [Q11] default).

### 0.2 Which cohomologies, in which phase

| Phase | Groups with Hecke action | New mathematics in the contract? |
|---|---|---|
| E0–E2 | `X_1 = H^0(Γ)`, `X_4 = H^1(Γ)` (and `H^2(Γ) = 0`, asserted as the `0 × 0` block, [I §3.3]) — the two groups the pipeline computes today (`EquivariantCohomologyOnK.h:123, 173`; `HeckeOperatorOnK.h:231`) | **none** — Stages 2–5 of [E §5] are `F_ell`-linear algebra on the stored `A^{(q)}(T_p)`; the Sturm bound `B'(k, ell)` is `F_ell`-linear algebra on the Miller basis, independent of the pipeline |
| E3 | the same, split by the involution `ι` into `H^±` ([E Stage 0 (A3)]) | **yes** — amendment C-A1 (§0.4) |
| E4 = **E4a** + **E4b** | `X_2 = H^0(∂)`, `X_5 = H^1(∂)`, the restriction maps `r^0, r^1`, the boundary Hecke action ([E (A1)], left-coset representatives), `H^1_! = ker r^1`. **E4a** ([SP] WP-4a/4b, slot 1): the certified `Γ`-level `τ_∂`, `Θ^∂_g`, its routes and oracles, `r^q`-equivariance — computed for **every** `ell` and recording `boundary_model = circle`, `boundary_is_group_cohomology = (2 ∈ R^×)` (confirmation 11: at `ell = 2` the circle model computes the bounded orbifold-model boundary analogue of [C] `rmk:ell2window`(1), and the record says so; never a refusal). **E4b** (slot 2): the diagnostics, `H^1_!`, Harder, the golden objects (emitted with E2, add-only), record integration | **yes** — C-A2 = [C] `sec:boundarydatum` (**met**) |
| E5 | `X_3 = H^1_c`, `X_6 = H^2_c`, the sequence (3.1) and the Hecke action on the cone ([E (A2)]) | **yes** — C-A3, in the formulation (b\*) the OQ2 verdict [V] settles (§0.4; [Q2] is no longer a branch to be decided in E4) |
| E6 | the per-`ell` atlas `Σ(ell)`, `S_sep(ell)`, labels, predictions, the canonical split field | none (report layer) |
| **E7** (scheduled — OQ4 **DECIDED**, [OD §OQ4]; slots 6–7) | `D_n` as a **first-class contragredient local system** (`ρ_n^∨(g) = ρ_n(adj g)^T`, [C] `def:contragredient`), the **pairing map** at cochain and cohomology level — bulk, boundary (E4) and compact support (E5) — with its perfectness certificate ([C] `prop:pairing`(2): Gram matrix `= I` in the stored bases), the PD adjointness `⟨T_p x, y⟩ = ⟨x, T_p y⟩` ([C] `cl:pd`(2), the acceptance gate for `X_3` at `ell ≥ 5`, OP3), the socle ↔ Loewy duality ([E Pred. 4.6], [C] `cl:pd`(3)) and the `ι`-pairing sign of [C] `rmk:iotapairing` (`+` pairs with `−`, recorded) | **yes** — C-A4 = [C] `sec:contragredient` (`def:contragredient`, `prop:pairing`, `lem:symdual`, `rmk:divided`) and `cl:pd` (**met as specification**; `cl:pd`'s cohomological content is OPEN in [C] and is what E7's oracles test) |
| **E8** (new in v1.5 — OQ18 **DECIDED**, [OD §OQ18]; slots 7–9) | the same groups over **`Z/ell^k`**: the reduction maps `Z/ell^{k+1} → Z/ell^k` on cochains and cohomology, the Bockstein of `0 → Z/ell → Z/ell² → Z/ell → 0` (`a = b = 1`), both Hecke-equivariant on the nose ([C] `sec:cone`'s integrality statement, C-A3(ii.6)); the `Z/ell²` refinement of D6's Eisenstein line as the first consumer | **none** — the objects are the reductions of the integral data already in [C]; what E8 needs is an **engine** contract: the `ENGINE_API.md` composite-modulus / non-field-elimination section (§6.2 E8, first item) |
| **E9** (new in v1.5 — OP4 / OC-1 / OD-T1; slots 8–9; **v1.12: absorbed into line 2**, [OD] S8-6c — see §6.2 E9's v1.12 note) | the **free `Γ`-model** of [C] `sec:orbifoldmodel` (`def:borelmodel`, `thm:specialisation`) on a refinement of the 7-vertex triangulation (OD-T1), degree-generic to `q_max + 1`, with its `τ`, `τ_∂`, `η` tables and the truncated pair at `ell ∈ {2, 3}` under `open:ell2` (`oc1a`); the host of the **six tests of [R §5]** (`lem:bulkperiodic` observed on the computed bulk column at `q_max ≥ 5`) | **yes** — **C-A5**, a new chapter fixing the concrete refinement and the model's `G1`–`G4` (an `X` bump; [C] `thm:specialisation`'s closing note: "that is the deferred construction") |

`H^2(Γ; M) = 0` for `ell ≥ 5` and every `n` ([E Claim 1.1]: `12`-torsion; measured `dim H^2 = 0` on
every campaign row, [I §3.3]) so "all computable degrees" for the bulk group means `q ∈ {0, 1}`; the
engine runs over `q ∈ {0, 1}` and asserts `d_2 = 0`. Until E4/E5 land, the record carries
`X_2, X_3, X_5, X_6` as `null` with `"status": "unavailable"` and reports the extension classes "in
the cone" as *predicted* from `r^1` ([E §1.3 decision box]).

### 0.3 Non-goals (binding; each needs an owner decision to reopen)

* **No `F_{ell^r}` element type in the engine** (G17, [I §4.3], [E §6 decision box]) — **re-examined
  for OQ10 in v1.5 and kept.** [OD §OQ10] decides the canonical split field as the default report
  form *provided it creates no downstream performance bottleneck*, and records the owner's
  expectation that an optimised field representation may even be faster. The non-goal is **not
  reopened by this revision**: every certified computation stays over `F_ell` in `uint32_t`; the
  residue field is `F_ell[X]/(π_w)` through `FpPolyT` (`Hecke/FpPoly.h:47-106`), acting on `D`-sized
  blocks through the coefficient field `K = F_ell[ŵ]` ([E Claim 3.3]) — no element type, only
  matrix polynomials in `ŵ`; and the split form of [E Alg. 6.4] is univariate arithmetic over
  `F_ell[Y]/(C)` on top of `FpPolyT`, confined to the report layer (§2.2 Stage 6). The **only
  trigger to reopen it** is E6's performance gate (§6.2 E6 (d), §2.2 Stage 6; v1.10): if the
  canonical-field route exceeds `0.10 × total_s` on any of that gate's cells, the owner is asked to choose between the own-field default and an `F_{ell^r}`
  element type (a Zech-log or a `k_max`-aware polynomial-basis type on `ModCtx`, §6.5); nothing
  before E6 depends on the answer. Reason for not reopening now: the split computation is
  `dim ≤ 84` × `deg ≤ ~200` polynomial arithmetic per cell — orders of magnitude below the
  pipeline's wall — so the bottleneck the decision guards against is not expected, and an element
  type would touch the engine's bit-identity contract for no measured gain.
* **Coefficient rings `F_ell`, `Z/ell^k` and `Z/n` are in the architecture** (OQ18, [OD §OQ18];
  replaces v1.4's "no `Z/ell²` coefficient ring"): `F_ell` is what is implemented; `Z/ell^k` is
  preferred over a generic `Z/n` if faster (the owner's condition — and it is: a prime-power
  modulus keeps Barrett / Montgomery reduction and needs only *valuation* pivoting, whereas a
  general `Z/n` needs a full Howell form with gcd steps, §6.2 E8); `Z/n` is reserved. **The first
  extent, fixed here, is phase E8** (§6.2): the reduction map `Z/ell^{k+1} → Z/ell^k` on cochains
  and on cohomology (bulk, and boundary / cone once E4 / E5 exist), and the connecting map
  (Bockstein) of `0 → Z/ell^a → Z/ell^{a+b} → Z/ell^b → 0` for **`a = b = 1`**, both
  Hecke-equivariant on the nose (C-A3(ii.6), [V §6.2]); the long exact sequences for general
  `(a, b)`, the `ell`-adic spectral sequence pages and the general-`n` ring are **not** pushed now
  ("do not push far in this direction now") but nothing in the data model may preclude them
  (§1.2, [V §6.4]). The Eisenstein line stays the mod-`ell` object `soc(X⁺_{4,m})` of [E D6] as the
  **published semantics until an E8 run exists** (slot-1 confirmation 9(a), DECIDED); E8 adds the
  `Z/ell²`-based definition as D6's *refinement*, never as a replacement of the mod-`ell` one.
* **No Heilbronn / Manin-symbol `H^1` model, no `Γ(2)` model** (G15, G16; OQ12 **DECIDED**: keep the
  current model — it is the blueprint for higher-rank groups). The reach statement is **reframed**
  ([OD §OQ12]): `n ≤ 1000` is a *hardware-bounded* limit on the reference machine (peak RSS
  `≈ n²`, `1.4 GB` at `n = 1000`, CLAUDE.md), **not a design limit** — the target hardware includes
  HPC nodes with enough RAM / VRAM to push it (R1); and nothing in the extension layer may assume
  the 7-vertex model's specifics beyond what [C] binds (E9 replaces the triangulation, and the
  layer must not notice). The **first ext campaign is bounded at `n ≤ 200`** (slot-1 confirmation
  9(b), DECIDED; §6.2 E6). The Manin model stays a follow-up (§6.5), downgraded: it is not the
  direction.
* **No optimisation of `HeckeModuleDecomposition` / `FpPoly` beyond what E0 needs** — they were
  explicitly left alone by the matrix-engine programme (`raw_mod_calls.allow` PERMANENT section;
  `CMakeLists.txt:641-642`). §2.3 measures where that assumption breaks.
* **No console code**: the engine registers types and verbs through the registry [P §2 C3]
  (§7) and never includes `Console/`.
* **No third-party dependency** ([ME §2 D6]); the JSON writer is hand-rolled like `HeckeReport.cpp`;
  the Sturm bound's `q`-expansions are computed mod `ell` (no bignum, §2.2 Stage 4(c)).
* **Bit-identity of everything that exists today**: no value of any golden object changes except
  by the **one** owner-gated re-baseline of this stage — E0b's `hecke_report/v2`, which also
  carries the oc1a record fields (slot 2; §1.6, §3.3, [SP §4.2]) — proved mechanically by
  `golden_explain.py`; every later phase only *adds* golden objects. The two mathematical-settings
  defaults of §1.5 are what the golden reference pins (R1); a non-default setting is never run by
  the harness.

### 0.4 The contract amendments C-A1…C-A4, as chapters of the unified contract [C]

**Retitled in v1.5.** v1.1–v1.4 wrote this section as "contract amendments `hecke_action.tex` must
gain". `hecke_action.tex` is **frozen** (V4, [C] v1.0.0, `b456448`), and every amendment below is
now a **chapter or section of the unified contract** `docs/latex/gl2_contract.tex` — drafted, refereed
and accepted ahead of the schedule of v1.4 §8 ([SP §2.1], [SPA] Q1). The body of this section is
kept as the record of *what was required and why*, with each decision written in where it fell; the
binding statements are the [C] labels in the map below, and a phase's validation cites the label.
Where the body still says "must gain" or "the contract is silent", read it as historical.

| Amendment | [C] labels (v1.3.2) | Status | Gate for |
|---|---|---|---|
| **C-A1** — the involution `ι` | `sec:involution`: `def:iota` (with (iv) negated at v1.2.0), `lem:iotamodel`, `obl:iota` (i)–(v), `rmk:iotasign`, `rmk:iotapairing` | **DONE** (`7beceb2` v0.12.0; OQ3 resolved `c823f3a` v1.2.0; `ι`-symmetric canonical `τ` re-baselined `a047147`, [RB]). Validation-built `ι^*` exists (`HeckeIotaSignValidation`, `HeckeIotaTauSymmetryValidation`); no *production* `ι^*` yet ([C] `sec:notimplemented`) | **E3 — met** |
| **C-A2** — the boundary datum | `sec:boundarydatum`: `def:bdrygroup`, `prop:circlemodel`, `prop:bdrycosets`, `def:taubdry`, `lem:bdrycomponent`, `lem:taubdryexists`, `def:bdryop`, `prop:bdrychar`, `obl:taubdry` (i)–(vii); `open:ell2` (**OC-1, DECIDED** `oc1a`, `b1c0aaa` v1.3.0) with `lem:ell2unbounded`, `rmk:ell2window`, `lem:bulkperiodic`, `rmk:bulkperiodicscope` | **DONE as specification** (`01b4b75` v0.14.0 … v1.3.2); **unimplemented** until E4a (slot 1, [SP] WP-4a/4b) | **E4 — met** |
| **C-A3** — the pair homotopy, the cone, the orbifold model | `sec:cone`: `def:pair`, `def:pairhomotopy`, `lem:etaexists`, `prop:coneroutes`, `obl:eta`, `obl:coneexact` (i)–(viii); `sec:orbifoldmodel`: `def:borelmodel`, `thm:specialisation`, `rmk:borelfree`, `rmk:mpcaveat` | **DONE as specification** (`0ae11d3` v0.15.0, `44c355e` v0.17.0); the well-definedness theorem is [C]'s; unimplemented until E5 | **E5 — met** (E5 additionally needs E4a's `τ_∂`); **E4 — met** (`τ_∂` is defined there) |
| **C-A4** — `D_n` and the pairing | `sec:contragredient`: `def:contragredient`, `prop:pairing` (1)–(5), `lem:symdual`, `rmk:divided`; `cl:pd` (**OPEN** in [C]: its coefficient-level input is proved, its cohomological content is owner OQ4's and is what E7's oracles test); `rmk:iotapairing` (`+` pairs with `−` since v1.3.2) | **DONE as specification**; not built ([C] `sec:codemap`: "the contragredient `D_n` and the pairing of `prop:pairing` are **not** built") | **E7 — met as specification**; PD adjointness is an *oracle* and the acceptance gate for `X_3` (OP3), never a definition |
| the [X §11.2] erratum (primitive vs full `T_{p^ν}`) | `err:e1`; `obl:algebra` (three entry points) | **DONE** (carried into [C]) | — |
| **C-A5** — the concrete free `Γ`-model (new in v1.5) | *to be written*: the refinement of the 7-vertex triangulation (OD-T1) and a model satisfying [C] `G1`–`G4` of `sec:orbifoldmodel`, its boundary `∂Y`, its stabiliser inventory, its `τ` / `τ_∂` / `η` tables' existence in every degree `≤ q_max + 1`, and the truncation instance of `open:ell2` on it | ~~OPEN; scheduled as a contract task in slot 7 (§8)~~ **DISCHARGED (v1.12)** by [C] v1.8.0 `sec:integral` (slot-8 WP-9, an `X` bump, Fable referee 0 B / 0 M / 6 m): **re-scoped onto the unrefined `Xbulk`** ([OD] S8-6c) — `def:isomodel`, `prop:isomodel` (ranks `5, 14, 19` per `n + 1`), `prop:strictlift`, `rmk:cafive`; OD-T1 answered **"not needed"** | ~~E9~~ line 2 (L2-1a onward) |

E3 and E4 are formula-level additions ([E Stage 0]); the cone needed a **definition**, fixed by the
OQ2 verdict ([E §0], spec v1.2) and now [C] `sec:cone`. What follows is the requirement record.

**C-A1 — the involution `ι` (gates E3).** In [C, sec:model] (`hecke_action.tex:214`): (i) the
simplicial automorphism `ι_K` of the 7-vertex model induced by `z ↦ −z̄`: vertices `0↔3`, `1↔2`,
`4↔5`, `6` fixed (the vertex layout at `LocalSystemSL2Z.cpp:120-122` and `hecke_action.tex:226-232`:
`0..3` on the cusp line with `Re` from `−1/2` to `+1/2`, `4 = ρ²`, `5 = ρ`, `6 = i`), with the
orientation sign of every edge and triangle under `ι_K` (the five faces at
`LocalSystemSL2Z.cpp:31-36` map `{0,1,4}↔{2,3,5}`, `{1,2,6}` to itself, `{1,4,6}↔{2,5,6}`); (ii)
`ρ_n(ι) = diag((−1)^{n−j})_j` in the basis `u_j = x^{n−j}y^j` of [C, def:rhon] and the
conjugation table `ιTι^{−1} = T^{−1}`, `ιSι^{−1} = S^{−1}`, `ι(ST)ι^{−1} = (TS)^{−1}`,
`ι(TS)ι^{−1} = (ST)^{−1}` on the generator multiset `𝒢` of [C, sec:model]; (iii) the statement that
`(ι_K, ρ_n(ι))` is an automorphism of the local system `(K, R, L)` — it maps each `SimplexRelation`
`f(s_lhs) = ρ_n(g_r) f(s_rhs)` to a relation of the same list **up to inversion** with
`g_r ↦ ι g_r ι^{−1}` (e.g. `f(v_3) = ρ(T) f(v_0)` goes to `f(v_0) = ρ(T^{−1}) f(v_3)`, the
equivalent inverted relation, [XA m7]) — hence an
involution of `C^•_eq` commuting with `d`; (iv) `[ι, T_{ΓgΓ}] = 0` on cohomology, because `ι`
normalises `Γ` and fixes `g = diag(1, N)`, so it permutes the coset representatives of
[C, prop:cosets]; (v) a contract box fixing the sign convention ([Q3] default: the Eisenstein
class of [C, obl:oracle] lies in `H^1_+`) — **now a record field**, `"iota_sign":
"eisenstein_in_H1_plus"` ([E §7]), so the box must exist before the first ext campaign (§6.2 E6,
[Q18] last sentence). **Done, [C] v1.2.0 (2026-09-16):** the box is [C, def:iota](iv), which
*defines* `ι^* := −ι^*_geo` (the geometric pullback `(ι^*_geo f)(σ) = ρ_n(ι) f(ι_K σ)` negated) so
that `H^1_+` is by definition the Eisenstein side — the v1.1.1 check had found the Eisenstein class in
the `−1`-eigenspace of `ι^*_geo` on every cell (`docs/implementation/oq3_iota_sign_verification.md`),
and the owner negated the definition; cost in `docs/implementation/oq3_resolution.md` (constants odd,
`ι^*` = geometric involution twisted by `det`). `iota_sign` now *names that normalisation*, and the
production `ι^*` of E3 must implement `−ρ_n(ι)` per block (sign of [C, lem:iotamodel] negated);
(vi) an obligation: `[ι, T_p] = 0` and `ι² = 1` are runtime assertions, **so is "Eisenstein class in
`H^1_+`" since [C] v1.2.0 (a definition-consistency gate, [C, obl:iota](v))**, and
the oracle `dim H^1_+ = dim M_k`, `dim H^1_- = dim S_k` for `ell ≥ 5` off the Dickson locus of
[C, rmk:dickson] ([M §5]) is recorded; (vii) the definition of the **Eisenstein line at `m`** as `soc(X⁺_{4,m})`
when that socle is one-dimensional over `F = T_m/m`, undefined otherwise ([E D6]; the reductions
of the integral Eisenstein and cuspidal eigenlines are not mod-`ell` Hecke data — at `(10, 691)`
both lie in the same 2-dimensional socle of the unsplit `H^1_m`).

**C-A2 — the boundary datum (gates E4).** A new subsection after [C, sec:chainlevel]: (i) the
boundary group `Γ_∞ = ⟨T⟩ × ⟨−I⟩` and the **definition** `H^•(∂; V_R) := H^•(Γ_∞; V_R)`
— the Borel reading, **decided** by the owner on 2026-09-15 (OP5, §11), in agreement with [E
§1.1]'s own definition of the six groups and with [V §5.5]'s argument section; the circle model
`K_∂` (the path `0–1–2–3` with the single relation `v_3 = T·v_0` that
`TestSL2Z_To_S1Cusp_RestrictionMorphism` already builds, `LocalSystemSL2Z.cpp:882-896`) and the
inclusion `j: K_∂ → K` as a `SimplicialComplexMorphism` (`:902`) compute `H^•(⟨T⟩; V_R)`, and
the contract must state that this **is** the boundary cohomology **exactly when `2 ∈ R^×`**: for
`n` even `−I` acts trivially on `V_R`, so `H^•(Γ_∞; V_R) = H^•(⟨T⟩; V_R)^{−I} = H^•(⟨T⟩; V_R)`
when `2` is invertible. The circle model is therefore the *specialisation* of the boundary datum
at `2 ∈ R^×`, exactly as the 7-vertex complex is the specialisation of the orbifold model at
`6 ∈ R^×` (C-A3(ii.7)).

**The `ell = 2` consequence, stated because it is substantive and not a flag.** `Γ_∞ ≅ Z × Z/2`,
and the Lyndon–Hochschild–Serre sequence of `1 → ⟨−I⟩ → Γ_∞ → ⟨T⟩ → 1` is the short exact
sequence

> `0 → H^{q−1}(Z/2; V_R)_T → H^q(Γ_∞; V_R) → H^q(Z/2; V_R)^T → 0`

(`⟨T⟩ ≅ Z` has cohomological dimension 1, so only the two columns `s = 0, 1` survive). When
`2 ∈ R^×` the terms with `q ≥ 1` on `Z/2` vanish and this returns `H^0 = V_R^T`, `H^1 = (V_R)_T`,
`H^q = 0` for `q ≥ 2` — the circle model. At `ell = 2`, however, `−I` acts trivially and
`H^q(Z/2; V_{F_2}) ≅ V_{F_2}` for **every** `q ≥ 0`, so `H^q(Γ_∞; V_R) ≠ 0` for every `q ≥ 0`:
**`H^•(∂)` is unbounded above in degree**. The bulk is no better — the 12-torsion argument of
[E cl:amalgam] fails at `ell = 2` and `H^q(Γ; V_{F_2}) ≠ 0` for every `q` — and hence neither is
the cone. So at `ell = 2` the boundary complex, the bulk complex and `C(r)` are **not finite in the
naive sense**, and the six-term sequence (3.1) is a *window* of a long exact sequence that does not
terminate, not the whole of it: `X_2, X_3, X_5, X_6` are the degree-`≤ 2` members of infinite
families, and `H^0_c = 0` / `H^2(K) = 0` — which hold for `6 ∈ R^×`, `n` even — are exactly the
hypotheses that fail there.

> **Construction item OC-1 (`ell = 2` truncation policy) — DECIDED in the contract on 2026-09-16
> (`oc1a`), [C] v1.3.0 `open:ell2`; [OD §OC-1].** What the implementation computes at
> `ell ∈ {2, 3}` is the pair in degrees `q ≤ q_max` from complexes truncated at `q_max + 1` —
> legitimate, because `H^q` of a cochain complex depends only on its degrees `≤ q + 1` — and the
> four things this box listed as open are now fixed: **`q_max` is an explicit, recorded run
> parameter, default 2**, *derived* on a finite model and settable only where `truncated = true`;
> the record carries `q_max`, `truncated` and the reported-degree list (§1.2, E5); the certificate
> obligations at the top of the truncation are [C] `obl:coneexact`(iv) as narrowed (composites
> asserted zero only where both end terms are reported); and exactness is asserted at every spot
> all three of whose terms are reported. Non-normative: `q_max ≥ 4` is recommended at `ell ∈ {2, 3}`.
> The *construction* of the free `Γ`-model of C-A3(ii.7) (OP4) is **phase E9** (§6.2, slots 8–9,
> behind the contract chapter C-A5); the model and the
> truncation are one piece of work, and nothing in E4/E5 may hard-code `q ∈ {0, 1, 2}` (§1.2's
> degree-generic data model is now the standing *requirement*, not a mitigation). The bulk half of
> the stabilisation alternative `oc1c` is the theorem [C] `lem:bulkperiodic` (2-periodicity of
> `H^q(Γ; V_R)` for `q ≥ 2`, Hecke-equivariant); what remains of it is [C] `rmk:bulkperiodicscope`(3).
> The `6 ∈ R^×` pipeline this plan builds is unaffected: there the truncation is vacuous.

Continuing C-A2:
(ii) the set `B_p := {δ ∈ Γ diag(1,p) Γ : δ upper triangular}` and its **left-coset**
decomposition `B_p = δ_∞ Γ_∞ ⊔ ⊔_{j=0}^{p−1} δ_j Γ_∞`, `δ_∞ = diag(1, p)`, `δ_j = (p j; 0 1)` —
the cusp analogue of `δ_i = s_i^{−1} g` in [C, alg:assembly], with `T δ_∞ = δ_∞ T^p`,
`T δ_j = δ_{j+1}`, `T δ_{p−1} = δ_0 T` ([E (A1)]); an explicit statement that the upper-triangular
**right**-coset representatives `β_j = (1 j; 0 p)`, `β_∞ = diag(p, 1)` of [C, prop:cosets(1)]
represent `Γ_∞ \ B_p` and give the `det`-twisted (transposed) operator, `χ_{b+1}` in place of
`χ_b` — they are **not** to be used ([EA M1]); **the `g`-twisted chain datum `τ_∂` on `∂X` of
C-A3(ii.2)** — the normative boundary datum, at `Γ`-level with the **same `s_i`, `δ_i` as the bulk**,
certified over `Z` exactly as [C, alg:tau] / [C, obl:tau] — **whose Shapiro transcription is a
one-dimensional datum `τ_∞` on the line**, and which is what makes the left-coset operator below a
*transcription* rather than a second, independently certified object (without it E5 would need a
fourth certified table, a boundary homotopy between two boundary cochain maps; [V §7] item 2) —
**decided** by the owner on 2026-09-15 (OP1, §11): the `Γ`-level `τ_∂` is the normative boundary
datum, and `τ_∞` with the `(δ_∞, δ_j)` left-coset operator is its Shapiro transcription and
route A of `HeckeBoundaryValidation`, a validation route only; (iii) the
definition `T_p^∂ := Θ_g^∂` on `H^•(K_∂; L|_{K_∂})` by [C, eq:heckechain] with `Γ_∞` in place of `Γ`
and the `δ_i` above, and its explicit group-cohomology form — `m ↦ Σ_i ρ_n(δ_i) m` on `M^T` and
`m ↦ ρ_n(δ_∞)(Σ_{a<p} ρ_n(T)^a) m + ρ_n(δ_0) m` on `M_T` (the cocycle rule `f(gh) = f(g) + g·f(h)`
with `f(T) = m`; [EA §3.1]) — the validation oracle of §5; (iv) the **equivariance statements**
`r^q ∘ T_p = T_p^∂ ∘ r^q` on cohomology, `q = 0, 1` — which **replace** the prose item
"Restriction compatibility" at `hecke_action.tex:1604-1609`, an item that speaks of "the boundary
Hecke action" no code implements ([I §1 0.5]); (v) the boundary characters `χ_b(p) = p^b + p^{n+1−b}`
of [E Claim 1.7] as a new oracle family in [C, obl:oracle]: on `H^0(∂) = M^T` the monomials
`x^{n−bℓ}N^b`, `0 ≤ b ≤ ⌊n/ell⌋`, are `T_p^∂`-eigenvectors with character `χ_b` (`δ_∞` scales by
`p^b`, each `δ_j` by `p^{n−b}`); `H^1(∂) = M_T` carries the **same multiset**, the class of `y^n`
carrying `χ_0(p) = 1 + p^{n+1}` — the Eisenstein eigenvalue of [C, obl:oracle]; for `n < ell` both
groups carry `χ_0`. The [M §4] convention warning is thereby settled by [C]'s own oracle: `r^1` is
equivariant for `1 + p^{n+1}` only with the left-coset operator.

**C-A3 — the equivariant mapping cone and its Hecke action (gates E5).** **Revised 2026-09-15 by the
OQ2 verdict** `hecke_extensions_OQ2_verdict.md` (**[V]**, CONFIRM WITH AMENDMENTS): (ii)–(iii) below
are [V §3]'s drop-in replacement text, adopted verbatim in substance with the plan's formatting, and
**with the owner's decisions on [V §8]'s eight points (2026-09-15) written in as decided** — the
decision record, including the three amendments, is §11. (i) The cone of
`r^•: C^•_eq(K) → C^•_eq(K_∂)` in the convention of [v5 §sec:mappingconeandles]
(`monodromy_v5.tex:1148-1162`: `C(f)^n = C_1^{n+1} ⊕ C_2^n`, `D(a, b') = (−d a, d b' + f(a))`),
`H^n_c := H^{n−1}(C(r))`, and the exact sequence (3.1) of [E Claim 1.5] with its connecting maps
written in the stored bases. **[Q2] is answered**: the formulation is **(b\*)** — the homotopy is
*derived* from a certified **pair homotopy `η` one level below the cochains, where `τ` lives**
([V §1], [V §2.3]). Branch (a) of v1.2 survives only as the special case `η ≡ 0`; the entrywise
cochain identity `rΘ_g = Θ_g^∂ r` is **not** a decision procedure for `h = 0` ([V §2.7], PROVED),
and v1.2's branch rule is withdrawn.

**C-A3(ii) — The Hecke datum of the pair and the cone action.**

*(ii.1) The pair.* `X := K̃` is the `Γ`-tessellation of the truncated upper half plane of
[C, rmk:orbifold] (`hecke_action.tex:200-212`); `∂X := Γ·i(K_∂) ⊂ X` the `Γ`-subcomplex of horocycle
lines, `K_∂` the cusp path `0–1–2–3` with `v_3 = T v_0` (C-A2(i), `LocalSystemSL2Z.cpp:882-896`);
`j: ∂X ↪ X`. `X` is **contractible and two-dimensional** (it is `Γ`-equivariantly the Borel–Serre
bordification of `H`; STANDARD), so `Z_1(X) = B_1(X)` and `Z_2(X) = 0` — which is what makes the
fills of (ii.3) exist and the `M` of (ii.3) unique. Every simplex of `∂X` has stabiliser `{±I}`,
acting trivially on `X` ([C, rmk:negI] `hecke_action.tex:261-289`). All chain data below are over `Z`; `R` denotes the
coefficient ring (`F_ell`, `Z/ell^k`, `Z/m`) and `V_R := Sym^n(Z^2) ⊗ R`.
`C^•_eq(K; V_R) = Hom_Γ(C_*(X), V_R)`, `C^•_eq(K_∂; V_R) = Hom_Γ(C_*(∂X), V_R)`, and `r := j^*`,
which is **surjective** ([V §0]: `∂X` is `Γ`-stable, so extension by zero of a boundary cochain is
equivariant).

*(ii.2) The boundary datum.* A **`g`-twisted chain datum on `∂X`** is an additive
`τ_∂: C_*(∂X) → C_*(∂X)` satisfying (T1) for `Γ'' = Γ_0(p)` with the twist `h ↦ g^{−1}hg`, (T2), and
(T3) on every component. [(T1) forces the component map: the line at `∞` goes to itself, the line at
`0` to itself, and the other lines follow.] It exists over `Z` for every `ell`, and any two are twisted-homotopic over `Z`, for **every** `ell`,
by the explicit argument and **not** by the abstract comparison theorem (whose relative-projectivity
hypothesis is exactly what forces `ell ≥ 5` in [C, lem:tauexists] — see the errata at §11.1): for
`τ_∂, τ_∂'` put `N_0(x) :=` the **unique** 1-chain of the (contractible, one-dimensional) component
of `∂X` containing the two images, with `∂N_0(x) = (τ_∂ − τ_∂')(x)`; `N_1 = 0` because
`Z_1(∂X) = 0`; and the (T1)-extension of `N_0` off the orbit representatives is well defined because
the stabilisers are central and act trivially ([V §2.6.1], PROVED over `Z`). `Θ_g^∂` is defined on `C^•_eq(K_∂; V_R)` by
[C, eq:heckechain] with `τ_∂` in place of `τ` and **the same `s_i`, `δ_i`** as the bulk. Unpacking the
`p+1` terms through `C^•_eq(K_∂) ≅ Hom_{Γ_∞}(C_*(line_∞), V_R)` (Shapiro) yields the left-coset form
of C-A2(ii)–(iii) with representatives `δ_i γ_i ∈ B_p` (`γ_i ∈ Γ` moving the image component back to
`line_∞`), one per left coset `B_p/Γ_∞`; the explicit `M^T`/`M_T` formulas of C-A2(iii) are the
**validation oracle**, not the definition. The operator `T_p^∂` on `H^•(K_∂; V_R)` is independent of
`τ_∂` and of the `s_i`. The `Γ`-level `τ_∂` on `∂X` (same `s_i`, `δ_i` as the bulk) is the
**normative** boundary datum and the left-coset `(τ_∞, δ_∞, δ_j)` operator is its Shapiro
transcription and a validation route only — owner decision OP1, 2026-09-15 (§11).

*(ii.3) The pair homotopy.* A **pair homotopy** is an additive degree-`+1` map
`η: C_*(∂X) → C_{*+1}(X)` with (T1) and

> `∂η + η∂ = j τ_∂ − τ j`.

It exists over `Z` for **every** `ell` — paths for boundary vertices, forced fills for boundary
edges; [C, alg:tau] steps 2–3 with `∂X` as source; no stabiliser order is ever inverted, because the
`Γ''`-stabiliser of every boundary simplex is `{±I}` ([V Lemma 2.3.1], PROVED) — and is unique up to
`∂M − M∂` for a **unique** `M: C_0(∂X) → C_2(X)` ([V Lemma 2.4.1], PROVED). The **cochain homotopy is
derived**, never chosen:

> `(h c)(σ) := Σ_{i=1}^{m} ρ_n(δ_i) φ_c(η(s_i · i(σ)))`, `σ ∈ o_{q−1}(K_∂)`, `c ∈ C^q_eq(K; V_R)`,

i.e. `h^q: C^q_eq(K; V_R) → C^{q−1}_eq(K_∂; V_R)`, and it satisfies `dh + hd = Θ_g^∂ r − r Θ_g`
([V Lemma 2.3.2], PROVED). Degrees: `K_∂` is one-dimensional, so `h^1` comes from `η_0` (paths) and
`h^2` from `η_1` (fills); `h^0 = h^3 = 0`. **`h` is never chosen freely at cochain level.**

The **sign convention is fixed once and for all** by owner decision OP6, 2026-09-15 (§11),
confirming what v1.3 had already applied throughout: `∂η + η∂ = jτ_∂ − τj`, hence `h = η̃`
**with no sign**. (The opposite convention would have given `h = −η̃`; it is not used anywhere.)
The cochain identity `dh + hd = Θ_g^∂ r − rΘ_g` and the cone map are *not* moved by this choice —
they are fixed by [v5]'s `D` — see (ii.4) and §10.2 M6.

*(ii.4) The cone action.* `C(r)^n := C^{n+1}_eq(K; V_R) ⊕ C^n_eq(K_∂; V_R)`,
`D(a, b) := (−d a, d b + r a)`, `H^n_c(K, K_∂; V_R) := H^{n−1}(C(r))`, and

> `Φ_g(a, b) := (Θ_g a, Θ_g^∂ b + h a)`.

`T_{ΓgΓ}` on `H^•_c` is the map induced by `Φ_g`; its matrix `A_c^{(q)}` in the stored basis is
assembled by [C, alg:assembly] on `C(r)`. The sign is the one v1.2 re-derived and [V §2.1]
re-derived independently: `DΦ − ΦD = (0, (dh + hd + rΘ − Θ^∂r) a)`, so `Φ` is a cochain map **iff**
`dh + hd = Θ^∂ r − rΘ` (PROVED; [XA §3.6]'s `dh + hd = rΘ − Θ^∂r` had the wrong sign, §10.2 M6).
The long exact sequence is that of `0 → C^•_eq(K_∂) → C(r) → C^•_eq(K)[1] → 0`, with
`Φ_g ι = ι Θ_g^∂` and `π Φ_g = Θ_g π`; it reads
`… → H^{q−1}(K_∂) → H^q_c → H^q(K) →^{r^q} H^q(K_∂) → H^{q+1}_c → …` in all degrees, and reduces to
(3.1) of [E cl:les] when `H^0_c = 0` and `H^2(K) = 0`, i.e. for `6 ∈ R^×` and `n` even. **Every map of
(3.1) is equivariant as soon as `Φ_g` is a cochain map — that is not a separate obligation**
([V §2.1]).

*(ii.5) Theorem (well-definedness).* (a) `Φ_g` is a cochain map of complexes of `R`-modules, so every
map of the long exact sequence intertwines `(T_p^∂, T_p^c, T_p)`. (b) The induced map on `H^•_c` is
**independent of `η`** — over `Z`, for every `ell` ([V §2.5], PROVED: two `η` give cone-homotopic
`Φ`, by the integral filtration-preserving homotopy `Ψ(a, b) = (0, −m̃ a)`). (c) For `6 ∈ R^×` it is
independent of `τ`, `τ_∂`, of the `s_i` and of `g ∈ ΓgΓ`, and equals the operator of the Hecke
correspondence on the Borel–Serre pair `(Γ\H̄, ∂)`, i.e. `cor ∘ (c_g)_* ∘ res` on
`H^•(Γ; C^•(X, ∂X) ⊗ V_R)` ([V §2.6.1–2.6.3], PROVED glue on STANDARD inputs: Borel–Serre 1973;
Harder, Invent. Math. 89 (1987) §§1–2; Ash–Stevens 1986); in particular the Hecke relations hold on
`H^•_c` **on the nose** ([V §2.8], STANDARD), and `T_p` is adjoint to `T_p` on `H^{2−•}(K; D_n)`
under Poincaré duality (C-A4). (d) `η ≡ 0` **iff** `τ j = j τ_∂` (a strict map of pairs); then
`Φ_g = (Θ_g, Θ_g^∂)`. **The cochain identity `r Θ_g = Θ_g^∂ r` alone does not license `h = 0`**
([V §2.7]; the shipped `τ` is not strict, `tau_table_p2.txt:13-15,35`). (e) For `ell ∈ {2, 3}` on the
7-vertex model, `T_p^c` is *defined* as the output with the canonical `(τ, τ_∂, η)`; (b) holds, (c) is
not asserted — exactly as for `T_p` itself ([C] contract box after lem:tauexists,
`hecke_action.tex:640-647`).

*(ii.6) Integrality.* `τ`, `τ_∂`, `η` are tables of integer chains, independent of `R` and `n`; `ρ_n`
is integral; hence `Θ_g`, `Θ_g^∂`, `h`, `r`, `D`, `Φ_g` over `R` are the reductions of **one integral
cochain map `Φ_{g,Z}`** on `C(r)_Z`, a complex of free `Z`-modules. For `6 ∈ R^×`,
`C(r)_Z ⊗ R = C(r)_R`. The reduction maps `Z/ell^{k+1} → Z/ell^k` and the connecting maps of
`0 → Z/ell^a → Z/ell^{a+b} → Z/ell^b → 0` (Bockstein) are `T_p^c`-equivariant on the nose, and the
pages of the `ell`-adic spectral sequence of `C(r)_Z` carry a `T_p^c`-action independent of
`(τ, τ_∂, η)` for `ell ≥ 5` ([V §6.2], PROVED). **Tables once, matrices per `R`**: the matrices
`Θ_g, Θ_g^∂, h` over `Z` have entries of size `~p^n` and are never stored; they are formed over
`R = Z/m` from the tables and `ρ_n(g γ_k) mod m` ([V §6.1]). A table solved only mod `m` ([C, alg:tau]
step 3 fallback, `HeckeTauTable.h:76-88`, `used_mod_ell_solve()`) defines `Φ_g` over `Z/m` only, and
the record **must say so**. **Integrality policy, decided by the owner on 2026-09-15 (OP2,
§11): the mod-`m` fill fallback is *forbidden by default*** — the integer tier is widened instead,
since the fallback exists only because of `int64` and never for a mathematical reason. It remains
reachable behind an explicit setting, and a cell that uses it then carries `integral = false`; but
`integral = false` is **not** the default escape from a hard fill, and a record claiming R-Z must
have `solve_regime = Z` on all three tables.

*(ii.7) Torsion primes.* For `6 ∉ R^×` the same definitions (ii.2)–(ii.6) apply **verbatim** to a free
`Γ`-model of the pair (the Borel construction `(X, ∂X) × EΓ`, or its isotropy-resolution model), whose
equivariant cohomology is the orbifold cohomology `H^•_Γ(X, ∂X; V_R)`; there existence and homotopy
uniqueness of `τ`, `τ_∂`, `η` hold over `Z` for every `ell` ([V §5.3], PROVED given the model, from
Brown I.7.4 / Weibel 2.2.6), and (ii.5)(c) holds over `Z`. The complex `C^•_eq(K; V_R)` of this
contract is the `q = 0` row of the isotropy spectral sequence of that model and coincides with it when
`6 ∈ R^×` ([V §5.1], STANDARD: Brown VII.7, VII.7.10; Moerdijk–Pronk's own identification with the
Borel construction, `simplicial.tex:72-75`). Moerdijk–Pronk's `S(T)` is one *computational model* of
it, not the normative definition: their charts are **effective** (`simplicial.tex:125,148`) while
`[SL_2(Z)\H]` is not, and they omit the independence proofs for `μ` (`:772, :811-815`) — so
[OD §OQ2]/R-MP's "their complex does the job in general" is plausible but **CONJECTURAL as a
citation** ([V §5.2]).

**This whole subsection enters the contract now, as definitions, with the construction deferred**
— owner decision OP4, 2026-09-15 (§11). That is what makes "the 7-vertex complex is a
specialisation" a *theorem* rather than a slogan: the general model is stated, the specialisation
at `6 ∈ R^×` is proved ([V §5.1], [V §5.3]), and only the construction of the free `Γ`-model and
its tables is postponed. The boundary half of the same statement is C-A2(i): the boundary group is
`Γ_∞ = ⟨T⟩ × ⟨−I⟩` (OP5, decided), the circle model is its `2 ∈ R^×` specialisation, and the
`ell = 2` truncation policy is the construction item **OC-1** recorded there — **decided
2026-09-16** (`oc1a`, [C] v1.3.0 `open:ell2`, [OD §OC-1]). The OC-1 *policy* is settled; OC-1's
*construction* and this subsection's deferred construction are one piece of work — **phase E9**
(§6.2), gated on the contract chapter C-A5 that fixes the concrete model.

**C-A3(iii) — Obligations.** (1) `τ_∂` certified exactly over `Z` (structural, (T3) per component,
(T2), (T1) bookkeeping over all stored transporters) like [C, obl:tau]; a failing table aborts.
(2) `η` certified exactly over `Z`: `∂η + η∂ = jτ_∂ − τj` on every stored representative, both sides
evaluated through the shared (T1) helper; (T1) bookkeeping; a failing table aborts. (3) Over `R`,
re-derived from the stored matrices: `dh + hd = Θ_g^∂ r − rΘ_g`, `DΦ_g = Φ_g D`, `D² = 0`, the bases
of `H^•_c`, exactness of the long exact sequence with rank (field) or length (`Z/ell^k`) bookkeeping
— `dim X_3 = dim X_2 − dim X_1 + dim ker r^1`, `dim X_6 = dim X_5 − rank r^1` when it reduces to
(3.1) — and the intertwining of every map by `(A_∂^{(q)}, A_c^{(q)}, A^{(q)})`. (4) Consistency
assertions (theorems, checked): `[A_c(T_p), A_c(T_q)] = 0`, the `T_{p^2}` recursion on `H^•_c`,
`H^0_c = 0` and `H^2(K) = 0` for `6 ∈ R^×`, `n` even. (5) **Diagnostics recorded, never branched on**:
`eta_zero := (η ≡ 0)`, `cochain_commutes := (rΘ_g = Θ_g^∂ r entrywise)`, `solve_regime ∈ {Z, mod_m}`
for each of the three tables. (6) **Cross-routes — both committed** (owner decision OP3,
2026-09-15, §11, which *amends* [V §8] item 3's "one of the two"): a strict-pair `τ^s` ([V Prop. 2.6.2], PROVED
by construction) must give the same `A_c^{(q)}`; the relative-complex route ([V §2.10], "route 3":
`Θ' := Θ + dE + Ed` with `E := ext_0 ∘ h`, which satisfies `rΘ' = Θ^∂ r` on the nose and computes the
cone operator on `ker r`) must give the same `A_c^{(q)}`; with C-A4, Poincaré adjointness
`⟨A_c^{(1)}(M_n) x, y⟩ = ⟨x, A^{(1)}(D_n) y⟩` for `6 ∈ R^×` ([V §2.9], STANDARD — a *complete
independent pin* of `A_c^{(1)}`, and an oracle, never a definition) — **PD adjointness is the
acceptance gate for `X_3` at `ell ≥ 5` once E7 exists**, and **both** cross-routes are built as
validation arms (§5, §6.2 E5: `+0.5 AU` for the strict pair, `+0.25 AU` for the relative complex).
Neither is a definition; the cone of [v5 §8] remains normative.

The v1.2 obligation "(b1) fix `h` by an explicit recipe and prove its `k_*` vanishes, or (b2) declare
the operator defined modulo `Hom(ker r^1, coker r^0)`" is **discharged, not carried**: (b1) holds with
the recipe `h := η̃` and the proof [V Lemma 2.4.1] + [V §2.5]; (b2) is unnecessary — and would have
been unacceptable, since **over a field** **every** element of `Hom(ker r^1, coker r^0)` is realised
by some degree-`−1` chain map `k` (the construction splits the cochain groups, so it is stated for
`R = F_ell` and is *not* claimed over `Z/ell^k` or `Z/m`; §11.1), so a *free* cochain-level `h`
leaves the operator on `H^1_c` genuinely undetermined ([V §2.2], PROVED over a field; at `(10, 691)`, `ker r^1 = X_4`, `coker r^0 = X_2 ≅ F_691`,
`dim X_3 = 4` and `Hom(ker r^1, coker r^0) ≅ F^3 ≠ 0` — **(v1.7) measured instead**: `rank r^1 = 1`, so
`ker r^1` is 2-dimensional, `dim X_3 = 3` and `Hom(ker r^1, coker r^0) ≅ F^2 ≠ 0`, the conclusion
unchanged; [C] v1.5.0 `rmk:coneambiguity691`, `HeckeConeValidation`).

**C-A4 — `D_n` (gates E7; OQ4 = **yes**, DECIDED, so E7 is scheduled — [C] `sec:contragredient`,
`cl:pd`).** The contragredient monoid action
`g ↦ adj(g) = det(g)·g^{−1}` on `D_n = (Sym^n)^∨`, `ρ_n^∨(g) = ρ_n(adj g)^T`, the local system
`(K, R, D_n)` and the statement that its Hecke operator is the transpose of `T_p` under the perfect
pairing of [E Claim 1.6] (`T_p` self-adjoint for the adjugate structure), with the duality statement
in its corrected form: the Loewy layers of `H^{2−i}(Γ; D_n)_m` are the **socle** layers of
`H^i_c(Γ; M_n)_m` in reverse order (`rad^i(V^∨) = (soc^i V)^⊥`, [E Pred. 4.6]) — not the reversed
Loewy series, which agree only for rigid modules.

Housekeeping, not contract: the comment "e.g., by the Cone class" at `EquivariantCohomologyOnK.h:115`
names a class that does not exist ([I §1 0.3]); E5 either uses that protected constructor or
deletes the comment.

---

## 1. Architecture

### 1.1 Placement and dependency rule

```
Orbifold_Cohomology_of_GL2/Hecke/             the contract-chapter machinery the ext layer consumes ONE-WAY (v1.5 placements, [SP §2.3] items 5, 7)
  SubspaceOps.{h,cpp}                         deterministic subspace lattice on MatrixT<uint32_t> (E0a/WP-1): SolveColumnsExact, HStack,
                                              PrimaryRCFBasis moved verbatim, algebra_closure, frobenius_kernel (strict mode, §3.1)
  HeckeSettings.{h,cpp}                       the mathematical-settings layer (R1, §1.5): values, defaults, validation, JSON, fingerprint;
                                              SHIPPED with its first consumer, E0b's `locality` (slot-2 WP-1); `strict` IMPLEMENTED (v1.7,
                                              slot-3 WP-3); `u_ell` (slot-3 WP-1), `sturm`, `sturm_unavailable` (slot-3 WP-2) registered
  HeckeBoundaryDatum.{h,cpp}                  B_N/Gamma_inf table, the Gamma-level tau_bd (C-A3(ii.2)) certified in the constructor (E4a)
  HeckeBoundaryOperator.{h,cpp}               Theta^bd on the circle model (a library call lifted from LocalSystemSL2Z.cpp:843-922), routes A/B,
                                              r^q, the recorded boundary_model / boundary_is_group_cohomology flags (E4a)
  HeckeBoundaryDiagnostics.{h,cpp}            the two RECORDED diagnostics cochain_commutes / eta_zero (the cusp-support walk) of
                                              [C] rmk:conestrict(2) (E4b, slot-2 WP-7); here because it consumes HeckeOperatorOnK
  HeckePairHomotopy.{h,cpp}                   the eta-table (C-A3(ii.3)) over Z + PairHomotopyCertificate: HeckeTauTable's step-2/3 machinery,
                                              the shared (T1) helper and certification pattern with dX as source (E5) -- beside HeckeTauTable,
                                              because it shares that helper, which must not be exported across the guard.
                                              SHIPPED (slot-2 WP-8, E5-1): obl:eta (i)-(iv) certified in the constructor, no mod-m path;
                                              EtaVertexPolicy + table_fnv64() (v1.7, slot-3 WP-6, for obl:coneexact(viii)(a))
  QuadPoint.{h,cpp}, ExactInt.{h,cpp}         (v1.7, slot-3 WP-1, E1b-0) QuadPointT<I>, I in {int64_t, __int128}; alg:tau step 1 through
                                              escalate_on_overflow (int64 first, widened per operation); ScopedExactTier
  SL2ZBoundaryPair.{h,cpp}                    (v1.7, slot-3 WP-5, E5-2) the restriction r^* built PIPELINE-side, lifted verbatim out of
                                              HeckeExt/HeckeBoundary (value-preserving), so that the cone does not consume HeckeExt/
  HeckeConeAction.{h,cpp}                     (v1.7, slot-3 WP-6, E5-3) h = eta~ by coset transport, Phi_g, A_c^(q), ConeActionCertificate,
                                              ConeRelationsCertificate, record hecke_cone_action/v1 -- HERE, not HeckeExt/ (see below);
                                              HeckeBoundaryDatum gains TauBoundaryVertexPolicy + table_fnv64() + the tie counter
  HeckeIntegerSolve.{h,cpp}                   the ONE integer solver of [C] alg:tau step 3, moved verbatim out of HeckeTauTable.cpp so that the
                                              eta fills use it (slot-2 WP-8; value-preserving)
Orbifold_Cohomology_of_GL2/HeckeExt/          compiled INTO cohomology_app (no new library); namespace `hecke_ext` (v1.6, decided:
                                              WP-5 moved HeckeIdentityCertificate from `heckeext`; the name is in no emitted text)
  HeckeLocalAlgebra.{h,cpp}                   A_S, w-hat, P_j, n_j, m_S, powers, socle, Hilbert, K-span tangent test (E1a; SHIPPED slot-2 WP-4)
  HeckeSturmBound.{h,cpp}                     B'(k, ell): q-expansions mod ell, Miller basis, T_q on M_k(F_ell), closure, certificate (E1s; shipped slot 1)
  HeckeGenerationCertificates.{h,cpp}         cyclicity, commutant (structured + naive oracle, the socle bound, CommutantState) (E1a; SHIPPED
                                              slot-2 WP-5); the Sturm sweep to B' is E1b's
  HeckeSturmSweep.{h,cpp}                     (v1.7, SHIPPED slot-3 WP-2, E1b) certificate (c) on real blocks: SturmOperatorSource /
                                              BlockRestrictionSource / FamilyOperatorSupplier, both sturm_unavailable modes,
                                              generation_verdict_with_sweep, Stage 1's S_0 with the u_ell admission
  HeckeUEllBudget.h                           (v1.7, SHIPPED slot-3 WP-1, E1b-0) header-only, pure: the FROZEN RSS model
                                              u_ell_rss/v2-2026-09-17, UEllDecision / UEllVerdict (no `resumable`: that is E2's)
  HeckeBoundary.{h,cpp}                       the ext-layer consumer of HeckeBoundaryDatum/Operator: H^1_! = ker r^1 with its Hecke action, the
                                              joint eigenspace, Harder, the split, golden collectors defined and never emitted (E4b; SHIPPED
                                              slot-2 WP-7)
  HeckeModuleStructure.{h,cpp}                Loewy / socle series, Jordan types (units of f), structure maps + matrices, canonical positions (E2)
  HeckeExtRecord.{h,cpp}                      the per-(n, ell) record, is_final(), per-kind FNV hashing (E2)
  HeckeExtReport.{h,cpp}                      hand-rolled JSON, schema hecke_ext/v1 (E2)
  HeckeExtDriver.{h,cpp}                      Stage 1-5 orchestration from a computed cohomology + family (E2)
  HeckeInvolution.{h,cpp}                     iota as an EquivariantCochainComplexMorphismOnK, sign split, Eisenstein line (E3; slot 4, v1.7)
  HeckeBoundary.{h,cpp}                       the ext-layer CONSUMER of Hecke/HeckeBoundaryDatum + HeckeBoundaryOperator: H^1_!, the Harder
                                              criterion, X_2 / X_5 in the record and in Stage 5's canonical positions (E4b)
  (HeckeConeAction -- MOVED to Hecke/ at v1.7, as shipped by slot-3 WP-6; the ext layer consumes it one-way. What stays here for
                                              E5 is the record integration: positions in (3.1), q_max / truncated / degrees in hecke_ext/v1, E2)
  HeckeContragredient.{h,cpp}, HeckePairing.{h,cpp}     rho_n^dual, the contragredient local system, the pairing map at three levels + certificates (E7)
  HeckePresentation.{h,cpp}                   generators and relations of X_{i,m} over T_m, on request (E2, OQ11)
  HeckeReduction.{h,cpp}                      Z/ell^{k+1} -> Z/ell^k reduction maps and the a = b = 1 Bockstein, Hecke-equivariance certificates (E8)
  HeckeAtlas.{h,cpp}, HeckePredictions.{h,cpp}, HeckeCanonicalField.{h,cpp}                            (E6)
  *Validation.{h,cpp}, README.md (file -> [E] section map, like Hecke/README.md)
Orbifold_Cohomology_of_GL2/EquivariantMappingCone.{h,cpp}   the cone of r^• as a cohomology-layer object (E5; SHIPPED slot-3 WP-5, generic,
                                                           no Hecke include, ConeCertificate = obl:coneexact(iv),(v) + Dcone^2 = 0)
Orbifold_Cohomology_of_GL2/FreeGammaModel/                 the free Gamma-model of [C] sec:orbifoldmodel on the C-A5 refinement: the triangulation
                                                           data, the degree-generic tables, the truncated pair (E9; a sibling of Hecke/, consumed one-way)
ModArithmetic/ModArithmetic/Fnv.h                          the ONE byte-wise FNV-1a-64 (G5 of [P §14.2] / [PA A4]) (E0a/WP-2, sole owner) -- in the
                                                           ModArithmetic library, NOT Orbifold_Cohomology_of_GL2/Util/ ([SP §2.3] item 6, below)
Orbifold_Cohomology_of_GL2/Golden/GoldenHarness.h          GoldenLookup(point, object) -- the ONE read-only lookup over GoldenReference.inc (E0a/WP-1);
                                                           console C1's G13 consumes it, no Util/GoldenLookup.h is created
docs/matrix-engine/tools/check_heckeext_includes.sh          one-way guard, run by HeckeExtArchitectureValidation
```

**Placements decided in v1.5, and why** (each is a correction of v1.4, [SP §2.3] items 5–7, [SPA] Q4):
* **`Hecke/SubspaceOps`, not `HeckeExt/SubspaceOps`.** E0b's refinement loop lives inside
  `Hecke/HeckeModuleDecomposition.cpp` (OQ5 placement (a), slot-1 confirmation 2, DECIDED) and calls
  the `P_p` solve and the kernel intersections; the guard below forbids `#include` of `HeckeExt/`
  from `Hecke/`. v1.4 was internally inconsistent; the guard stays one-way (`HeckeExt → Hecke`) and
  `HeckeSturmBound`'s "includes only `SubspaceOps`, `FpPolyT`, `MatrixT`, `ModArithmetic`" rule holds
  with the new path — **plus `EngineCheck.h` and `Fnv.h`** (v1.5.1): both are dependency-free
  (`<stdexcept>`/`<string>`, `<cstdint>`/`<string>`), the first is what the assertion policy of
  CLAUDE.md requires in place of a bare `assert` (deleted by `NDEBUG` in every non-`Check` build),
  the second is R3.1 item 6's one FNV; `check_heckeext_includes.sh` rule 3 admits exactly these
  six, with the reason written into the script.
* **The boundary datum, the boundary operator and the `η`-table in `Hecke/`.** [C]
  `sec:boundarydatum`'s code map specifies a unit "beside `hecke::HeckeCosetTables`" that reuses
  `HeckeTauTable`'s (T1) helper and its constructor-time certification; the `η`-table reuses the
  same step-2/3 machinery and the *same* (T1) helper with `∂X` as source ([V §7] item 5). A helper
  shared across the `Hecke/` ↔ `HeckeExt/` boundary would have to be exported through the guard;
  keeping all three tables beside `HeckeTauTable` keeps it file-local. The ext layer consumes them
  one-way (`HeckeExt/HeckeBoundary`). **(v1.7)** `HeckeConeAction` lives in `Hecke/` too, as shipped
  (slot-3 WP-6; [S3] §2.3 item 4): the reason is not the shared helper but the guard's rules —
  rule 2 forbids `ModArithmetic/Engine/` inside `HeckeExt/`, and rule 1 forbids the pipeline, which
  E2 consumes, from depending on the extension layer — and the restriction `r^•` it needs was
  lifted pipeline-side as `Hecke/SL2ZBoundaryPair` (slot-3 WP-5), out of `HeckeExt/HeckeBoundary`,
  which now consumes it.
* **`ModArithmetic/ModArithmetic/Fnv.h`, not `Util/Fnv.h`.** One of the three FNV copies is
  `ModArithmetic/ModArithmetic/PerformanceSmokeValidation.cpp:90` (the `Fnv` class), compiled into
  the `ModArithmetic` static library (`CMakeLists.txt:195`); a header under
  `Orbifold_Cohomology_of_GL2/Util/` would be an **upward** include. A dependency-free header in
  `ModArithmetic/ModArithmetic/` is reachable from all three sites and from console C1. [P] C1 (G5)
  and [PA A4] plan the `Util/` path and are stale on this point — recorded here as a pointer; the
  [P] revision is a slot-2 task ([SP §5]).
* **One `GoldenLookup`.** WP-1's four-hash grid arm needs read access to the frozen reference by
  key; it exposes `GoldenLookup(point, object) -> const GoldenEntry*` from `Golden/GoldenHarness.h`
  (never a copied constant). That is the lookup [P] C1's G13 consumes — one lookup, not two, and no
  `Util/GoldenLookup.h`.
* **`Hecke/HeckeSettings`** because its first consumer, `locality` (E0b, slot 2), lives in `Hecke/`;
  every other key's consumer is in `HeckeExt/` or `Campaign/` and includes it one-way (§1.5).
* **The two migration guards are shared, append-only files.** `check_matrix_includes.sh`'s
  allow-list (`MatrixRetirementValidation`) admits `Matrix.h` only in `ModArithmetic/*`,
  `*Validation.*`, `Hecke/HeckeModuleDecomposition.*`, `Hecke/FpPoly.*`, `Golden/GoldenHarness.cpp`,
  `Bench/BenchDriver.cpp`; every new `MatrixT`-typed TU of this plan (`Hecke/SubspaceOps.*`,
  `HeckeExt/*`, `Hecke/HeckeBoundary*` where it touches `MatrixT`) is **added with a reason** — the
  decision "`MatrixT<uint32_t>` for everything in `HeckeExt/` except the cone" (§2.3) is that
  reason — in the same package, one block per package; likewise `raw_mod_calls.allow`
  (`ConsumerMigrationValidation`) for a moved function that carries raw `mod_*` calls ([SPA] Q7).

**Why TUs in the executable and not a static library.** The layer consumes `MatrixT`, `FpPolyT`,
`HeckeModuleDecomposition`, `HeckeOperatorFamily`, `EquivariantCohomologyOnK` and
`EquivariantCochainComplexMorphismOnK`, all of which are compiled straight into `cohomology_app`
(`CMakeLists.txt:342-620`; the S10 placement note at `:540-551` is the precedent: "consume
ModArithmetic's Matrix … so they are compiled into cohomology_app, NOT into the pure-integer
HeckeCore"). A `HeckeExt` library would first need the `Pipeline` library refactor the console plan
records as an unscheduled follow-up ([P §16.4]). The one-way dependency is enforced instead by a
grep guard in the style of `check_matrix_includes.sh` (`MatrixRetirementValidation`, CLAUDE.md
"Migration tools"): **no `#include` of `HeckeExt/` outside `HeckeExt/`, `Campaign/`, `Golden/`,
`Bench/`, `kernel.cu`, `*Validation.*` and `ValidationRegistry.cpp`** (which includes
`HeckeExt/*Validation.h` and matches no other pattern, [XA m9]), and no include of `Console/`,
`Cuda/`, `Engine/` internals or `BlockFlatMatrix.h` inside `HeckeExt/`. `HeckeSturmBound` is the one
unit that consumes **nothing** of the pipeline (only `SubspaceOps`, `FpPolyT`, `MatrixT` and
`ModArithmetic`): it is pure modular-form arithmetic on the Miller basis and can be built and
validated in isolation (§8). Its algebra closure is therefore `SubspaceOps::algebra_closure`, shared
with `HeckeLocalAlgebra` — not a `HeckeLocalAlgebra` member, which would drag
`HeckeModuleDecomposition` into it ([XA m16]); the guard asserts that `HeckeSturmBound.*` includes
nothing but those four (`Hecke/SubspaceOps.h` since v1.5). `ModArithmetic/ModArithmetic/Fnv.h` has
**one owner, E0a** (WP-2, §6.2); console C1 consumes it ([PA A4], [XA m18]).

**What it consumes** (the public API only): `HeckeOperatorFamily::T_p / prepare`
(`Hecke/HeckeOperatorFamily.h:120, 247`) for the level-(b) matrices; `HeckeModuleDecomposition`
(`Hecke/HeckeModuleDecomposition.h:157-183`) after the E0 fix; `FpPolyT` and its certificates
(`Hecke/FpPoly.h:125-177`); `MatrixT` products / RREF / kernel / image / inverse
(`ModArithmetic/ModArithmetic/Matrix.h:90-108`); `EquivariantCohomologyOnKT`'s block and `_fm`
accessors (`EquivariantCohomologyOnK.h:148-173`); the general block-row constructor of
`EquivariantCochainComplexMorphismOnK` (`EquivariantCochainComplexMorphismOnK.h:146-150`) and its
induced maps (`:155, 185`); `engine::elim` on `FlatMatrix` (`ModArithmetic/ModArithmetic/DenseElim.h:111-158`)
for the cone (E5) only; `ComputeSymmetricPowerMatrixFM` (`ModArithmetic/ModArithmetic/FlatMatrix.h:204`)
for `ρ_n(δ_j)` and `ρ_n(ι)`. The `L·` map (multiplication by the Dickson invariant
`L`, `Sym^{n−ell−1} → Sym^n`) is **not** a symmetric-power matrix: it is a new primitive
`DicksonMultiplicationMatrix(n, ell)` in `HeckeExt/` ([I G12], [XA m10], §2.1).

**What it must NOT depend on:** `HeckeCrossChecks` (an oracle whose induced systems have fibre
dimension `(p+1)(n+1)` — `hecke 10 691 691 --cross-checks` reached 14 GB and did not finish, [I §2.6];
validations may call it, the engine never); `BarCocycleH1` (validation-only by its own header,
`Hecke/BarCocycleH1.h:5-10`); the tape / CUDA layers (the ext layer is `Matrix`-sized and
single-threaded, §2.3); `Console/`; the deprecated `Matrix` alias — spell `MatrixT<uint32_t>` so the
new TUs do not depend on the temporary `-Wno-deprecated-declarations` (`CMakeLists.txt:632-650`).
The engine is `uint32_t` only, like the whole level (b)/(c) layer (`HeckeOperatorFamily.h:253`
`uint32_t ell_`, `HeckeModuleDecomposition.h:187` `uint32_t ell_`, constructor parameter at `:157`);
`ell < 2^32` covers every case of [E §8] and [E Claim 1.8] (`ell ≤ 2294797`). The golden harness's
64-bit points (`GoldenHarness.cpp:171-173`) are therefore outside the ext layer (§1.6).

### 1.2 Data model (all over `F_ell`, `MatrixT<uint32_t>`, `D ≤ ~200`)

| Type | Contents | [E] |
|---|---|---|
| `MaximalIdealBlock` | the certified-local `PrimaryBlock` of E0 (`basis_columns`, per-`p` `char_poly` / `min_poly` / `jordan_partition`, `residue_degree`, `residue_witness`, **new:** `local_certified` (schema key `local`), `witness_poly` `π_w`, `w_hat_exponent` `N`, `character` `{p ↦ P_p ∈ F_ell[X]_{<f}}`), plus the group it lives in and its cross-group identity by the evaluation test of §2.2 Stage 2, and the restrictions `t_p\|_V` (`D×D`, stored so every certificate re-verifies from emitted data, [XA m15]) | Stage 2, Claim 3.1, Claim 3.3 |
| `ResidueField` | `π_w`, `f`, `N`; optionally the canonical `C_{ell,f}`, `ρ_can`, the Frobenius orbit (E6) | §6.2, Def. 6.2 |
| `LocalAlgebra` | an `F_ell`-basis of `A_S` as `D×D` matrices *and* as a `dim A_S × D²` coordinate matrix (RREF form, so membership is one solve); the coefficient field `K = F_ell[ŵ]` as the matrix `ŵ = w^{ell^N}` (with `π_w(ŵ) = 0` exactly); the generators `n_p = t_p − P_p(ŵ)` for **every** `p ∈ S` (the witness direction `n_w = w − ŵ = Σ c_p n_p` included); bases of `m_S^i` for `i ≤ ν`, `m_S = (n_p)_p` (no separate `π_w(w)` generator); `ν`; `soc A_S`; `hilbert[i]`; `gorenstein`; the tangent table `{p ↦ active/inactive}` **over `K`** (the `K`-span of `n̄_p` is the `F_ell`-span of `ŵ^i n̄_p`, `0 ≤ i < f`) and the minimal active subset; `embdim = dim_{F_ell}(m_S/m_S²)/f` | Stage 3, §3.3, Claim 3.3, Alg. 5.4 |
| `SturmBound` (per `(k, ell)`, not per `m`) | `k`, `ell`, `dim M_k`, the cap `B_max` (default `12·B(k)`), the outcome `B' ∈ ℕ ∪ {none}`, the closure dimension reached, and the matrices `T_q mod ell` on the Miller basis for `q ≤ B'` prime (`dim M_k × dim M_k`) — on a `none_at_cap` outcome, for the primes `q ≤ cap` instead (there is no `B'`), and `verify()` clause 4 checks exactly that list (v1.5.1, WP-3) | Def. 2.8, Claim 2.9 |
| `GenerationCertificate` | `kind ∈ {cyclic, commutant, sturm(B'), unavailable}`, the data re-verified by `verify()` (§1.3), `S_m` (the certified generating set), the swept prime list, and the per-route outcome `{a: passed/failed, b: passed/failed/excluded_by_socle_bound/over_budget/not_needed, c: passed/failed/unavailable/not_needed}` with the numbers that decided it (`t, s, f, dim_F soc A_S`, `u`) | Stage 4 |
| `ModuleStructure` (per `X_i` at `m`) | Loewy bases `m^j V`, socle bases `soc^j V`, layer dims (in `F_ell` units and divided by `f`), `jordan[p]` = the Jordan type of `n_p` on `V` **in units of `f`** (nullities of `π_p(t_p)^s = ker n_p^s` divided by `f`; equals the S10 partition with every multiplicity divided by `f/deg π_p`), structure maps `θ_j: m_S/m_S² → Hom_F(top_j, bottom_j)` as `F_ell`-matrices **stored** (rows: bottom-layer basis, columns: top-layer basis, one per generator `n_p`) with `rank / f`, `active` subsets over `K`, `cyclic`, `free`, `min_generators` | Stage 5, (D2)–(D5), Claim 6.1, Claim 5.9 |
| `CanonicalPosition` | for `W ⊆ V` with `W ∈ {H^1_! ⊆ X_4, Eis := soc(X⁺_{4,m}) ⊆ X⁺_4 (E3, only when `dim_F = 1`, else "undefined"), r^0 X_1 ⊆ X_2 (E4), L·H^1(M_{n−ell−1}) ⊆ X_4, ker/im of (3.1) in their ambient group}` — `X_1` itself is *not* a subspace of `X_4`; it is reported through its own Loewy series and through `r^0 X_1 ⊆ X_2` ([E D6], [XA m11]): `dim(W ∩ m^j V)` per `j` **and the image of `W` in each layer**, `dim((W ∩ m^j V + m^{j+1}V)/m^{j+1}V)` ([E Alg. 5.8(4)], [XA M7]), and the verdict `layer(j)` (`W ⊆ m^jV` and `W ∩ m^{j+1}V = 0`) / `sum_of_layers` (`W` is the direct sum of its layer images) / `skew` (neither) / `undefined` | (D6) |
| `HeckePairDatum` (E4/E5, **over `Z`**) | the three chain tables of C-A3(ii): `tau` (the shipped bulk `τ`), `tau_boundary` (`τ_∂` on `∂X`, `Γ`-level, same `s_i`/`δ_i`), `eta` (the pair homotopy `η: C_*(∂X) → C_{*+1}(X)`), each as `ChainTerm`s `(n_k, γ_k, σ_k)` in the `HeckeTauTable` pattern (`Hecke/HeckeTauTable.h:23-26`) on an **abstract `Γ`-pair** — orbit representatives, stabilisers, transporters, (P4) bookkeeping — and **degree-generic** (not the `q ∈ {0,1,2}` of `HeckeTauTable`), so the free-`Γ`-model of C-A3(ii.7) needs no refactor; plus `solve_regime[3] ∈ {Z, mod_m}` per table and the derived flag `integral` (all three `Z`). **Nothing stores a cochain-level `h` as primary data**: `h_flat` is derived per `R` by coset transport ([V §7] item 3) | C-A3(ii.2)–(ii.6), [V §3], [V §7] 3 |
| `ConeCohomology` (E5) | `coefficient_ring` (`F_ell` today; `Z/ell^k` from E8; the type admits `Z/m`), `D`, the cone bases (`Z^q(C(r))`, `B^q(C(r))`, `H^q(C(r))`), `les_maps` (the maps of the long exact sequence as matrices in the stored bases, one per reported spot — six on the model complexes), `Phi(q)`, `A_c(q)`, the four certificates of §1.3, the **diagnostics** `eta_zero`, `cochain_commutes` (recorded, never branched on, C-A3(iii)(5)), and — OC-1 `oc1a`, [C] `sec:recordschema` item 5 — **`q_max`, `truncated`, `q_max_source ∈ {derived, set}` and the reported-degree list `degrees`**: on the model complexes the constants `2` / `false` / `derived` / `{0, 1, 2}` (rider (i): `q_max` is *derived* on a finite model and settable only where `truncated = true`), on E9's truncated free model the bound of the box; `truncated = true` may never report a vanishing above `q_max` | C-A3(ii.4), [V §7] 3, [C] `open:ell2`, `obl:coneexact`(iv) |
| `MathSettings` (**R1**, `Hecke/HeckeSettings.h`, v1.5) | the values in force of every mathematical setting of §1.5 (`final_mode`, `sturm.unavailable`, `sturm.cap`, `locality`, `field_polynomial`, `split_field_report`, `coefficient_ring`, `predictions`, `presentation`, `u_ell`, `integral_fallback`, `q_max` where settable), their `source ∈ {default, spec, console}`, and the **fingerprint** (FNV-1a-64 of the canonical key = value text of the *non-default* entries; `0` when all are default) that enters every hash input and the campaign job id (§1.5). Engine-owned: defaults and validation live here, the console and the campaign only *set* through it ([OD] R1). Thread-local scoped override in the `Scoped*` pattern of `HeckeOperatorOnK.h:375` / `EquivariantCohomologyOnK.h:226`, propagated onto `run_concurrently` tasks like the engine's own options | [OD] R1, [P] C4 |
| `resumable` objects (**R3**, §1.3.1) | per budgeted computation its `XState` and the `"resumable"` record object of R3.1 — `SturmState` (E1s/WP-3), `LocalityState` (E0b), `CommutantState` (E1a), the `u_ell` decision (E1b), `FillState` (E5); `resumable_items` at record level | [OD] R3 |
| `ContragredientLocalSystem` (**R4**, E7) | the local system `(K, R, D_n)` with relation matrices `ρ_n^∨(γ) = ρ_n(adj γ)^T` from the same `SL2ZRelationDatum` list (a second relation generator beside `GenerateSL2ZRelationsWithGroupData`, `LocalSystemSL2Z.h:63-64`); its `EquivariantCohomologyOnK`; the comparison map `Φ_n` of [C] `lem:symdual` (antidiagonal, `(−1)^t t!(n−t)!`) as a `FiberBlockTable` morphism, an isomorphism iff `n < ell` | [C] `def:contragredient`, `lem:symdual` |
| `Pairing` (**R4**, E7) | the evaluation pairing `⟨·,·⟩` **over `Z`** ([C] `prop:pairing`: Gram matrix `I` in the bases `(u_j)`, `(u_j^∨)`), its cochain-level form on `C^•_eq(K; M_n) × C^•_eq(K; D_n)` (and on `∂`, and on the cone), the cohomology-level pairings `H^t_c(M_n) × H^{2−t}(D_n)` and `H^t(∂; M_n) × H^{1−t}(∂; D_n)` as matrices in the stored bases, the **perfectness certificate** (Gram `= I` at coefficient level, asserted; full rank at cohomology level, [C] `cl:pd`(1), asserted at `ell ≥ 5`, `n` even), the **adjointness certificate** `⟨A_c(T_p) x, y⟩ = ⟨x, A(D_n)(T_p) y⟩` ([C] `cl:pd`(2), *no* determinant factor; the acceptance gate for `X_3`, OP3), and the recorded `ι`-sign `⟨ι^*x, ι^*y⟩ = ε·⟨x, y⟩` with `ε` predicted `−(−1)^n` by [C] `rmk:iotapairing` (`+` pairs with `−`) | [C] `prop:pairing`, `cl:pd`, `rmk:iotapairing`, [OD] R4 |
| `PredictionEntry` | text, kind, `predicted`, `confirmed ∈ {true, false, unavailable}` | (D7), §4.3 |
| `HeckeExtRecord` | `ell, n, weight, sign`, `commit`, `model`, `iota_sign`, `convention_check` (`tau_mod_ell_ok`, `eis_eigenvalue_ok`), **`settings`** (the `MathSettings` in force with their sources and the fingerprint, R1), `coefficient_ring`, **`q_max`, `truncated`, `q_max_source`, `degrees`** (constants on the model complexes), `groups[6]` (dims or `unavailable`), `les` (E5), `operators_computed`, `u_ell` (`{included, reason ∈ {within_budget, u_ell_over_budget, off}, predicted_mb, budget_mb, resumable}`, §2.2 Stage 1), `sturm` (the `SturmBound` with its `mode` and `resumable`), `ideals[]` = the seven per-`m` items above, each with **`final ∈ {true, false, "heuristic"}`** and its reason (§1.3.1 R3.2), `presentation` (present only under `presentation = on`, OQ11), `identities` (§5.1 counts), `predictions_mode`, `certificates_ran`, **`resumable_items`**, `hashes` (every hash input carries the settings fingerprint) | §7 schema, [OD] R1/R3 |

**Two rows are not over `F_ell`** (the heading's "all over `F_ell`" predates the OQ2 verdict):
`HeckePairDatum` is a table of **integer** chains, independent of `R` and of `n`, and `ConeCohomology`
carries its coefficient ring as a field. This is the R-Z / R-ring requirement of [OD R2] made
concrete: *tables once, matrices per `R`* ([V §6.1]). The one obstacle is the mod-`ell` fill fallback
of [C, alg:tau](3) (`HeckeTauTable.h:76-88`, `used_mod_ell_solve()`): a table solved mod `ell` defines
the datum over `Z/ell` only, so [OD R2]'s "`τ` already is integral and exactly certified" holds
**exactly when that flag is clear** ([V Appendix]). The data model therefore records the regime per
table rather than assuming it. **Per the owner's OP2 decision (2026-09-15, §11) a record claiming
R-Z requires `solve_regime = Z` on all three tables**: the integer tier is widened rather than
falling back. The fallback remains available behind an explicit setting and then sets
`integral = false` on the cell, which is a *recorded failure to reach `Z`*, not the default route.
Nothing here precludes R-red (reduction maps), R-LES (Bockstein) or R-resume: the only budgeted steps
in the cone construction are the finite-neighbourhood integer fills (`τ` step 3 and `η_1`), whose
`rings_used`, current neighbourhood `N`, partial system and integer tier are what a `state`/`resume`
contract persists; `τ_∂` and `η_0` are closed-form, and **certification is never budgeted**
([V §7] item 11). There is **no** search for a canonical `h` and none for a boundary-compatible `τ`.

The residue-field data of a block are the polynomials `π_w` and `P_p` — never numeric roots
(the `F_ell`-form is the default reporting form, [E §6.1 tier (i)]; the tuple `(P_p(X̄))_p` *is*
the character `a(m)` in the coordinates `F_ell[X]/(π_w)`, [E Claim 3.3]); the split form of
[E Alg. 6.4] is an E6 option on the report. `P_p` is defined through `ŵ`, not `w`: for
`A_S = F[ε]/(ε²)`, `t = α + ε`, `w = t`, one has `t − P(w) = 0` with `P = X` although the
nilpotent part of `t` is `ε ≠ 0`; with `ŵ = α` one gets `n_t = ε` ([E Claim 3.3], [EA B2]) — the
E0 validation pins exactly this example (§3.2).

### 1.3 Certificates — one C++ type per named certificate

Each is a `struct` holding exactly the data a third party needs, with a deterministic
`uint32_t verify() const` returning `0` on success and a nonzero code naming the first failing
clause — the convention of `HeckeModuleDecomposition::certify()` (`.h:177-180`, return codes 1–24 in
`.cpp:792-953`) and `CertifyIrreducible` (`FpPoly.h:161-165`). Verification never re-runs a search.

| Certificate | Stored data | `verify()` re-derives | [E] |
|---|---|---|---|
| `LocalityCertificate` | block basis, `w = Σ c_p t_p`, `N`, `π_w`, `{P_p}` | `π_w` = squarefree part of `minpoly(w\|_V)`, `CertifyIrreducible(π_w) = 0`, `deg π_w = f = lcm deg π_p`, `f \| N` and `ell^N ≥ D`; `ŵ := w^{ell^N}` by `N` successive `ell`-th powers and `π_w(ŵ) = 0` exactly; `deg P_p < f`; and `n_p = t_p − P_p(ŵ)` nilpotent on `V` (`n_p^D = 0` by `⌈log₂ D⌉` squarings, [XA m4]) for every `p`. For `k = 1` the certificate is **analytic** (no matrix power): `P = X`, `π_w = π`, and `N` recorded; `ŵ` is not formed ([XA m17]) | Cert. 5.2, Claim 3.3 |
| `ExhaustivenessCertificate` | the block list of one group (each block with its own `c`, `π_w`, `N`, `{P_p}` and `t_p\|_V`) | `Σ dim = d`; `U` invertible, every `U^{−1} A_p U` block-diagonal (= `certify() == 0`); locality on every block; and **pairwise distinctness by evaluation** ([XA M5]): for blocks `B ≠ B'`, with `B`'s `c`, `π_w`, `{P_p}` and `N' :=` the least multiple of `f` with `ell^{N'} ≥ dim B'`, `ŵ' := (Σ c_p t_p\|_{B'})^{ell^{N'}}`, it is **not** the case that `π_w(w\|_{B'})` and every `t_p\|_{B'} − P_p(ŵ')` are nilpotent. No "up to Galois" clause is needed: the test passes exactly when `B'`'s character is `B`'s or a Frobenius conjugate of it, i.e. the same maximal ideal of `T_S` (a character `φ'` with `φ'(w)` a root of `π_w` and `φ'(t_p) = P_p(φ'(w))` has kernel `m_B`) | Cert. 5.3 |
| `CyclicityCertificate` | `m_S` basis, a generator `v ∉ m_S V` | `dim V/m_S V = f` (Nakayama) and `A_S v = V` | Cert. 5.5(a) |
| `CommutantCertificate` | the socle-bound numbers `(t, s, f, dim_F soc A_S)`; if attempted: the chosen element `a` (its index in the fixed candidate list of §2.2 4(b)), the RCF change of basis `R` and invariant factors `g_1 \| … \| g_m` of `a` on `V`, and the rank of the structured system | **re-derives `dim C`**, deterministically and without the search: `R^{−1} a R` equals the companion blocks of `(g_i)` entrywise; the `u = Σ_{i,i'} deg gcd(g_i, g_{i'})` basis matrices of `End_{F_ell[a]}(V)` are **rebuilt** from `(g_i)` and `R` by the fixed formula and checked to commute with `a` and be independent; the system `X t_p = t_p X` over that basis is formed and row-reduced; its nullity `= dim C` must equal `dim A_S`; the `A_S` basis lies in `C`. A truncated or wrong list cannot pass: `dim C` is recomputed, not read. The socle bound is re-checked from `V`, `m_S` and `A_S` ([XA B2]). **(v1.6) `verify()` must not pin the RCF basis: any valid `R` verifies** — a rescaled cyclic block of `R` is another rational canonical basis and passes; a perturbed image column or two columns swapped inside a cyclic block break the companion relation and fail clause 12 (WP-5 §4; the tamper arm is written accordingly, with the rescaling as a positive control). `kCommutantBudget = 2·10^10` is a named constant, not a setting (WP-5 item 6) | Cert. 5.6(b) |
| `SturmBoundCertificate` | `k`, `ell`, `dim M_k`, `B_max`, `B'` or `none`, `closure_dim`, the Miller-basis matrices `T_q mod ell`, `q ≤ B'` | the matrices are re-derived from the `q`-expansions mod `ell` (deterministic, not a search); the `F_ell`-algebra they generate has dimension `dim M_k` (`B'` exists) — or, for `none`, the closure at `B_max` has dimension `< dim M_k`; `B'` is minimal (the closure of the primes `< B'` has dimension `< dim M_k`) | Def. 2.8, Claim 2.9 |
| `SturmCertificate` | the `SturmBoundCertificate` it relies on, the prime list, per prime the stored `T_q\|_V` and its coefficients in the `A_S` basis | `T_q\|_V − Σ coeff·basis = 0` for every listed `q`; the list covers every prime `≤ B'`; `B'` exists. **Proof range** (non-Dickson `m` of `X_4`): the list is exactly the primes `≤ B'` — `ell` is in it iff `ell ≤ B'` — because [E Claim 2.10] writes *every* `T_q`, `T_ell` included, as `F_q(T_{q' ≤ B'}) + ell·t'` with `t' = 0` there ([XA B3]). **Heuristic range** (Dickson-type `m`, `X_2, X_3, X_5, X_6`): the list additionally carries `S_sep(ell)` (from E6) and `ell` when `U_ell` is within the coset budget; the record is flagged *heuristic*. **`unavailable`** when `B'` does not exist | Cert. 5.7(c), Claim 2.10 |
| `ModuleCertificate` | Loewy / socle bases, Jordan types, structure-map matrices | `m_S·(m^j V) = m^{j+1} V` (span equality both ways), `soc^{j+1}/soc^j = soc(V/soc^j)`, layer dims sum to `dim V`, every layer dim `≡ 0 mod f`, `ν_V ≥` largest Jordan part of every `n_p` ([E §5.1 item 7]), the nullity sequence of every `n_p^s` divisible by `f` and equal to the rescaled S10 partition, `rank_{F_ell} θ_j ≡ 0 mod f`, the stored `θ_j` matrices reproduce `n_p·b` on the layer bases | Stage 5, Claim 5.9, Claim 6.1 |
| `IdentityCertificate` | the seven identity classes of [E §5.1] with the values found, and the applicability verdict per identity | each identity recomputed from the record's own data (dimension formula with `DicksonInvariantCount`, commutation `[A_p, A_{p'}] = 0`, boundary dims and characters, exactness, socle↔Loewy duality (E7), and from E6 **identity 6**: the multiset of residue characters of `H^1` (with multiplicities) equals the union over the Glover factors `Sym^{n_i} ⊗ det^{j_i}` of `Sym^n(F_ell^2)` of the `θ^{j_i}`-twisted atlas systems of weight `n_i + 2`, plus the `H^0`-corrections, [XA M7]). **Applicability** ([XA M3]): Eichler–Shimura and `d_2 = 0` gate only on `n > 0` even and `5 ≤ ell < 2^32`; elsewhere the identity is reported `not_applicable`, never `passed` | §5.1 |
| `EquivarianceCertificate` (E3–E5) | the matrices of `ι`, `r^q`, the (3.1) maps | `[ι, A_p] = 0`, `ι² = I`, `r^q A_p = A_p^∂ r^q`, each (3.1) map intertwines | (A1)–(A3) |
| `TauBoundaryCertificate` (E4) — **over `Z`**; stores `τ_∂`, **not** `τ_∞` ([V §4], [V §7] 4) | the `τ_∂`-table: for each `Γ''`-orbit representative `(i, σ)`, `σ ∈ K_∂`, the chain `Σ n_k γ_k · i(σ_k)` with `σ_k ∈ K_∂`, in canonical form; `solve_regime`; the derived `τ_∞` transcription if used | `det γ_k = 1`; every `σ_k` a boundary simplex; (T3) per component; (T2) on every stored edge slot through the shared (T1) helper; (T1) bookkeeping over all stored transporters (the [C, obl:tau] list, `Hecke/HeckeTauTable.h:260-281`); image components as forced by (T1) | (A1), C-A3(ii.2), C-A3(iii)(1) |
| `PairHomotopyCertificate` (E5, **new**) — **over `Z`**; this is the certificate that **pins the operator** ([V §2.5], [V §4]) | the `η`-table: for each `Γ''`-orbit representative of a boundary **vertex** a 1-chain of `X`, of a boundary **edge** a 2-chain of `X`, in canonical form; `solve_regime`; `rings_used` | `∂η(x) = (jτ_∂ − τj)(x)` on every vertex slot and `∂η(e) + η(∂e) = (jτ_∂ − τj)(e)` on every edge slot, **both sides evaluated only through the shared (T1)/(P1)/(P4) helper** from the stored `τ`- and `τ_∂`-tables; (T1) bookkeeping; `det γ_k = 1`; the bound `B_tab` recount ([C, lem:bounds](5)). Ring: `Z`, or `Z/m` for slots whose `τ`/`η` fill used the fallback — then recorded, and the record is non-integral | C-A3(ii.3), C-A3(iii)(2) |
| `ConeActionCertificate` (E5, **new**) — over `R`; a consequence of the two above, re-checked | `Θ^∂_flat`, `h_flat` (both **derived** per `R`), `Φ_g` on the cone cocycle basis, `A_c^{(q)}`; the bases of `Z^q(C(r))`, `B^q(C(r))`, `H^q(C(r))`; `D` | `h_flat` equals the **coset transport of the stored `η`-table**, recomputed from `ρ_n(g γ_k) mod m` and the `ω`-row (the analogue of `HeckeTauTable::certify()(f)`, `Hecke/HeckeTauTable.h:277-279`); `dh + hd = Θ^∂ r − rΘ` as matrices; `DΦ_g = Φ_g D`; `Φ_g` maps the stored cocycle basis into `Z^•(C(r))` and projects to `A_c^{(q)}` ([C, alg:assembly] step 2 recomputed). **A tampered `h' = h + k` passes every matrix identity and fails here** (§5) | C-A3(ii.4), C-A3(iii)(3) |
| `ConeCertificate` (E5, **extended** per [V §4]) | `D`, the six (3.1) maps as matrices in the stored bases, `A^{(q)}`, `A_∂^{(q)}`, `A_c^{(q)}` | `D² = 0`; each composite of consecutive maps is `0`; rank (field) / length (`Z/ell^k`, by a Howell/Smith form) bookkeeping — `dim X_3 = dim X_2 − dim X_1 + dim ker r^1`, `dim X_6 = dim X_5 − rank r^1`, the homology of the stored sequence zero; each map intertwines `(A_∂^{(q)}, A_c^{(q)}, A^{(q)})`; `im(X_3 → X_4) = ker r^1`. **It is certificate-grade but says nothing about the Hecke module `X_3`** — any `Φ_h` of [V §2.2] passes it ([V §4]) | (A2), C-A3(iii)(3) |

**Assertions, not certificates** (theorems re-checked, C-A3(iii)(4), [V §4]): `[A_c(T_p), A_c(T_q)] = 0`,
the `T_{p^2}` recursion on `X_3`, `X_6`, `H^0_c = 0` and `dim H^2(K) = 0` (`6 ∈ R^×`, `n` even),
`eta_zero ⇒ cochain_commutes`, and — once E7 exists — Poincaré adjointness, which for `6 ∈ R^×` is a
**complete independent pin** of `A_c^{(1)}` ([V §2.9]).

`HeckeExtRecord::is_final(m)` is *defined* as ([E §7], last paragraph): `local == true` **and** every
certificate above that applies verifies with `0`, **and** `GenerationCertificate::kind ∈ {cyclic,
commutant}`, or `sturm(B')` **with `B'(k, ell)` existing** on a non-Dickson `m` of `X_4` (the range
of [E Claim 2.10]) — then `final = true`. **Since v1.5 `final` is the tri-state
`{true, false, "heuristic"}` of §1.3.1 R3.2** (OQ8 / OQ15, DECIDED-CONFIGURABLE; defaults by slot-1
confirmations 6 and 8): `"heuristic"` only under the user-selected modes `final_mode =
sturm_heuristic` or `sturm.unavailable = heuristic`, when the ideal's only generation evidence is a
recorded heuristic sweep; otherwise the ideal is emitted with `"final": false` and a reason string
from the fixed list `{not_local, sturm_unavailable (B' > cap or ell | [T^sat : T_Z(M_k)]),
sturm_heuristic (Dickson m / boundary or cone group), closure_unreachable (the socle bound proves
(b) fails, (a) fails, and (c) is off its proof range), certificate_failed:<code>,
budget_exhausted:<kind>, interrupted}` — **published, flagged, listed in `analysis.txt`, with its
resumable state where a budget was involved, never withheld** (confirmation 8, DECIDED). A `U_ell`
omitted by the coset budget (`u_ell.reason = u_ell_over_budget`) never makes a proof-range record
non-final (the proof list is the primes `≤ B'`, §1.3); it is recorded, and it matters only on the
heuristic range, which is non-final in the default mode anyway.
Consequence of the socle bound (§2.2 4(b)), re-derived for [XA B1]: on the **unsplit** `X_4`
every block whose module is not cyclic over a Gorenstein `A_S` — every multiplicity-≥2 cuspidal
block, every Eisenstein–cuspidal block of the `(10, 691)` shape — is final **only** via `sturm(B')`
until E3 splits it by sign.

### 1.3.1 Resumable budgeted computations (R3)

[OD] R3 (owner's general note; OQ8, OQ15, OQ16, [XA B2] `over_budget`, [XA B3] `u_ell`) requires
that **every computation a budget can cut off — with a result that is incomplete or heuristic —
stores its iteration counts and intermediate state, so that the user can resume it, and possibly
complete it, with a higher budget.** This block is the contract every such computation implements;
it is *designed now and implemented by the consuming phases* (WP-3 / E1s for the Sturm bound; E0b
for the locality loop; E1a for the commutant; E1b for `U_ell`; E0b's strict mode for interruption;
E5 for the fills). Nothing here changes a value: a computation run to completion under a budget it
never hits is byte-identical to one that has no budget at all.

#### R3.1 The contract, common to every instance

1. **State type.** A budgeted computation `X` has a plain `struct XState` — serialisable to JSON
   with a fixed key order, no pointers, no hash containers, `uint32_t`/`uint64_t` and
   `MatrixT<uint32_t>` / `FpPoly` members only — and exposes
   `const XState& state() const` after every run, complete or not. The state is a **deterministic
   function of the inputs and the budget**: two runs of the same inputs under the same budget on
   any thread count, backend or device produce byte-identical states (they consume only
   `A^{(q)}(T_p)`-level objects and fixed-seed sequences; §4 items 1–2, 4).
2. **Resume.** `Outcome resume(const Budget& new_budget)` continues **from `state()`**, never from
   scratch. A resume with `new_budget` *below* what the state has already reached is refused with
   a named error (`ENGINE_CHECK_MSG`, "resume: budget below reached state"); a resume on a
   complete state is a no-op that returns the same outcome and the same certificate.
3. **Resume-invariance (the gating property).** For every instance, `run(b_1)` followed by
   `resume(b_2)` produces the **same outcome, the same certificate and the same state,
   entrywise — the state modulo its `budget_history`**, which item 4 makes `[b_1, b_2]` against
   `[b_2]` and which is therefore the one member that *must* differ (a validation asserts both the
   agreement modulo the history and the difference of the histories; v1.5.1, WP-3) — as `run(b_2)`
   from scratch, for every `b_1 ≤ b_2`. This holds because every
   budget below is a *prefix cut* of one fixed, deterministic iteration (a prime sequence, a
   seeded witness sequence, an operator order, a neighbourhood radius): the budget decides *where
   the iteration stops*, never *what it does*. Each consuming phase's validation carries a
   resume-invariance arm (§5), and a consuming phase that cannot make its iteration a prefix cut
   must say so and is not resumable.
4. **Budget history.** The state carries `budget_history[]`, one entry per `run`/`resume` with the
   budget in force; the *record* reports the **last** budget as the setting in force and the
   history beside it. A resume with a changed budget is therefore a **new recorded setting** in
   the sense of [OD] R1 — the record's `settings` block and its hash input change — and a resume
   with a changed *non-budget* setting is **refused** (it would not be the same computation; the
   user starts a new one). [P] C2/C5 mirror this on the console side (see the pointer in §7 and
   the WP-6 report for the console lane): a resumed handle keeps its creation-time settings
   snapshot and appends to `budget_history`; `?x` prints both.
5. **Certificates on partial results.** A certificate emitted for an incomplete state verifies
   **what was reached** (e.g. "the closure at the primes `≤ B_reached` has dimension `c`"), never
   the final claim; `verify()` on a partial certificate returns `0` for the partial statement and
   the record's `final` field is what says the claim is not established (R3.2). No certificate is
   ever emitted for an `in_progress` state (an interruption mid-step, R3.3 item 5), only the state.
6. **Where the state lives.** In the record, inline, as the object below, if its JSON is
   `≤ 64 KiB`; otherwise in a sidecar `<record-stem>.state.<kind>.json` referenced by relative path
   **and** FNV-1a-64 hash (`ModArithmetic/ModArithmetic/Fnv.h`, the one byte-wise FNV, from its
   standard offset basis `0xcbf29ce484222325`) from the record. **The record stem is set by the
   record layer (E2)**, the only place that knows it; an instance's certificate writer provides the
   field and the sidecar writer, and when no stem is set it inlines the state regardless of size
   and flags `state_oversize: true` with the state's hash, rather than emitting a path that names no
   file (v1.5.1, WP-3 deviation 5). The console keeps the state in the handle ([P] C2, "handles, not copies") and writes
   the same JSON on `save`. The campaign driver's own `resume` (job-level, keyed on the completion
   trailer, `docs/matrix-engine/campaign.md` §4) is **not** this mechanism: it decides whether a
   *job* re-runs; R3 decides whether an *incomplete computation inside a job's record* can be
   continued, and a campaign re-run with a higher budget is a new job (different settings
   fingerprint, hence a different job id — §1.5, R1).

**The record field.** Every budgeted item writes, at its own site in the record,

```
"resumable": { "kind": "<sturm_bound|locality|commutant|u_ell|fill>",
               "complete": <bool>,
               "budget": { ...the budget in force... },
               "reached": { ...the instance's progress counters... },
               "budget_history": [ {...}, ... ],
               "state": { ...inline XState... } | "state_ref": { "path": "...", "fnv64": "..." } }
```

and the top-level record carries `"resumable_items": <count of incomplete items>`. `final`
(R3.2) never reads `resumable`; `resumable` never licenses anything (rule [C] `A6`: a record
field is not branched on by the pipeline that wrote it).

#### R3.2 `final` is tri-state, and what an incomplete item does to it

`final ∈ {true, false, "heuristic"}` per ideal ([OD] OQ8 / OQ15, DECIDED-CONFIGURABLE; the
defaults are the slot-1 confirmations 6 and 8 of 2026-09-16):

* `true` — as before: `local == true`, every applicable certificate verifies with `0`, and the
  generation certificate is `cyclic` / `commutant`, or `sturm(B')` with `B'` existing on a
  non-Dickson `m` of `X_4` ([E] §7 last paragraph, [E] `cl:sturmmodl`); **(v1.17, `hecke_ext/v4`) or
  `dickson` / `boundary`**: the finality certificate (d0) passed on an `X_1` block or (d1) on an `X_4` block
  ([E] v1.13.0 `cert:dickson`, `cert:boundary`), run only where (a)–(c) did not pass; a passed route is
  `true` in every mode (it proves the same predicate, [E] `cl:gen`(b)); a failed one falls through to the
  reason (a)–(c) produced. `certificate_failed:` also admits the names `dickson`, `boundary`.
* `"heuristic"` — only under the user-selected modes `final_mode = sturm_heuristic` (heuristic
  range: Dickson-type `m`, `X_2, X_3, X_5, X_6`) or `sturm.unavailable = heuristic` (`B'` missing or
  cap hit): the ideal's only generation evidence is a **heuristic sweep**, recorded with the
  primes actually swept (`sturm_primes`) and the mode. Never in the default configuration.
* `false` — everything else, with a **reason** from the fixed list
  `{not_local, sturm_unavailable, sturm_heuristic, closure_unreachable, certificate_failed:<code>,
  budget_exhausted:<kind>, interrupted}`; `closure_unreachable` is the socle-bound proof that
  (b) fails together with (a) failing, i.e. the ideal *cannot* reach cyclic/commutant closure
  (§2.2 4(b)) and (c) is not on its proof range — **(v1.6) or, equally, a *computed*
  `dim C > dim A_S`**, which is as much a proof that (b) fails as the bound is; the
  implementation uses the same reason for both (WP-5 item 5). The tri-state is **one type**:
  `HeckeGenerationCertificates` reuses `SturmFinal` until E2's record layer owns `Final`, to
  which both units then migrate (WP-5 item 4).

**Disposition in the default mode (`final_mode = closure`, `sturm.unavailable = nonfinal`),
DECIDED by slot-1 confirmation 8:** an ideal that cannot reach closure is **emitted** with
`final = false`, its reason, and — where a budget was involved — its `resumable` object; it is
listed in the campaign's `analysis.txt`; it is **never withheld**. A `budget_exhausted:<kind>`
reason always comes with `resumable.complete = false`; `closure_unreachable` and
`sturm_heuristic` are not budget outcomes and carry no state.

#### R3.3 The instances

| # | Computation (owner) | `XState` — what is persisted | `resume(budget)` continues by | Why it is a prefix cut (resume-invariance) | Record site |
|---|---|---|---|---|---|
| 1 | **Sturm bound** `B'(k, ell)` — `HeckeExt/HeckeSturmBound` (**WP-3 / E1s**; the shape WP-3 implements) | `k, ell, dim_M_k`; `cap` (budget) and `budget_history`; `B_reached` (the largest prime processed) and `primes_done[]`; `precision` `L` (the series length in force, `L ≥ q·dim_M_k` for every processed `q`); the echelon Miller basis to precision `L` (or the `(E_4, E_6, Δ)` expansions it is regenerated from — deterministic either way, the choice is WP-3's); the **closure basis** — the RREF coordinate matrix (`closure_dim × dim_M_k²` rows) of the `F_ell`-algebra generated by `{T_q : q ≤ B_reached}`; `closure_dim`; the `T_q` cache (`q ↦ dim_M_k × dim_M_k` matrix, `q ≤ B_reached`); `outcome ∈ {found(B'), none_at_cap, in_progress}` | if `outcome = found`: no-op. Else: the next prime after `B_reached`, growing `L` lazily to `q·dim_M_k`, extending the closure by the new generator (one `algebra_closure` step on the stored basis), until `closure_dim = dim_M_k` (⇒ `B' = q`) or `q > cap` (⇒ `none_at_cap`) | the algebra generated by `{T_q : q ≤ B}` is a function of `(k, ell, B)` alone; `T_q` does not depend on `L` beyond `L ≥ q·dim_M_k`; the primes are processed in ascending order — so the state after the primes `≤ B` is the same whether reached in one run or two | the record's `sturm` object: `{B_prime | null, cap, closure_dim, dim_M_k, mode, resumable{…}}`; a `none_at_cap` outcome is `final = false` with reason `sturm_unavailable` (default) or `final = "heuristic"` (mode `heuristic`) |
| 2 | **Locality loop** — `Hecke/HeckeModuleDecomposition` (**E0b**) | `mode ∈ {budget(N), strict}`, `budget_history`; the **current partition** (the block list with `basis_columns` `U`, per block `local ∈ {true, unknown}`, and the per-block certificate data where local); per non-local block the **attempt index** into the fixed-seed witness sequence (`kResidueWitnessSeed ^ 0x9E37…·(dim+1) ^ ell`, `HeckeModuleDecomposition.cpp:695`) and, for auditability, the `c` vectors tried; in strict mode the phase reached (`linear`, `berlekamp`, `residue_search`, §3.1) | per non-local block, from its attempt index, with the new budget (or with `strict`, which continues into the terminating route of §3.1 after the linear family) | the witness sequence is a fixed function of `(dim, ell, seed, attempt)`; splits are inserted at the parent's position in `CanonicalLess` order (§3.1 step 2) and each split re-seeds by the sub-block's `dim`, so the partition after `N` attempts is a function of `N`; `run(64) + resume(128) == run(128)` | `level_c.locality = {mode, budget, resumable{…}}`; per block `local`; **(v1.6, WP-1 finding 3)** a block that survives the budget is `final = false` with reason **`budget_exhausted:locality`** — budget mode never *proves* non-locality (a genuinely non-local block **splits** and never survives the loop; what survives is a block whose locality is unknown under the budget), so `not_local` is reachable only from strict mode's interruption path; strict mode never emits `local = false` except by interruption (item 5) |
| 3 | **Commutant certificate (b), `over_budget`** — `HeckeExt/HeckeGenerationCertificates` (**E1a**) | the socle-bound numbers `(t, s, f, dim_F soc A_S)`; the chosen cyclic-most `a` (its index in the fixed candidate list, §2.2 4(b) step 2), its RCF data `R`, `(g_i)`; the **structured system assembled so far** — rows in the fixed order "operators ascending `p`, then row index" — and the row count reached; `modmul_spent`; `budget` (`kCommutantBudget`) and `budget_history` | forming the remaining rows and reducing, from the row reached | the system's rows are a fixed sequence; reduction of a prefix is the RREF of that prefix, which the full reduction extends without changing earlier pivots (row-echelon on a fixed row order) | `certificate_routes.b = over_budget` with `resumable{…}`; the ideal falls through to (c) meanwhile; `final` as (c) decides |
| 4 | **`U_ell` budget skip** — Stage 1 of `HeckeExtDriver` (**E1b**) | the decision inputs `(n, ell, predicted_mb, budget_mb)`, the frozen constants' version, the verdict `reason ∈ {within_budget, u_ell_over_budget, off}` | re-running Stage 1 with `U_ell` attached to the *same* `HeckeOperatorFamily` (its cache is keyed by `(p, r)`, `HeckeOperatorFamily.h:263-270`, so the other operators and the cohomology are reused), then Stages 2–5 on the enlarged family | the decision is a pure function of `(n, ell, budget_mb)` (§1.5, §2.2 Stage 1); the enlarged run is `run(S_0 ∪ {ell})`, which the fixed operator order makes the same whether `ell` was there from the start or added — Stage 2's `ComputeMultiOp` orders operators by ascending prime | `u_ell = {included, reason, predicted_mb, budget_mb, resumable{…}}`; on the proof range an omitted `U_ell` never makes a record non-final (§1.3 `SturmCertificate`) |
| 5 | **Interrupted strict loops** — the strict locality mode of §3.1 (**E0b**), and every loop above when a cooperative cancellation ([P §16.4], R11) fires | as item 2 (or the item interrupted), plus `interrupted = true` and the step boundary reached | as the item's own `resume` | interruption is only honoured **at a step boundary** (between witnesses, primes, rows, neighbourhoods — never inside an elimination), so the state is exactly a prefix state | the item's `resumable{…}` with `complete = false`; `final = false`, reason `interrupted` |
| 6 | **Integer fills of the pair datum** — `τ` step 3 and `η_1` (**E5**; the R-resume note of §1.2) | per unfilled slot: the neighbourhood radius `N` reached, the integer tier in force (`int64` → the widened tier of [OD] OP2), the partial linear system, `rings_used` | widening the tier (the default route, OP2) or the neighbourhood, from the slot reached | the fill of a slot is the *first* solution in a fixed enumeration order of the neighbourhood; a wider tier or radius only lengthens the enumeration; certification is **never budgeted** ([V §7] item 11) | `solve_regime[3]`, `integral`, `resumable{kind: fill}` on the cell; a record claiming R-Z has all three tables at `Z` and no incomplete fill |

Items 1–3 and 6 are the ones with non-trivial state; 4 and 5 exist so that the record's answer to
"can this be continued?" is uniform. The `HeckeSettings` keys that budget them are `sturm.cap`,
`locality`, `u_ell` and the commutant's `kCommutantBudget` (a named constant today, a setting
only if a consumer asks); `integral_fallback` (OP2) is the fill tier's knob (§1.5).

#### R3.4 What WP-3 implements, exactly

`HeckeExt/HeckeSturmBound.{h,cpp}` ships `struct SturmState` with the members of R3.3 item 1,
`SturmBound::state()`, `SturmBound::resume(uint32_t new_cap)`, the `budget_history`, the
`"resumable"` object in `SturmBoundCertificate`'s JSON, and the refusal of a cap below
`B_reached`. Its validation (`HeckeSturmBoundValidation`, §5) has the resume-invariance arm:
`none` under a forced `cap = 3` at `(24, 5)`, then `resume(cap = 12·B(k))` reaches `B' = 5` with a
`SturmBoundCertificate` **entrywise equal** to a fresh run's — matrices, `closure_dim`, primes and
the state — and a `resume(cap = 2)` on that state is refused with the named error. The
`sturm.unavailable` mode is *consumed* by E1b's `SturmCertificate` / `is_final`, not by WP-3:
WP-3 records `none_at_cap` and the state; which `final` value that becomes is R3.2's business.

### 1.4 The report writer

`HeckeExtReport.{h,cpp}`: `BuildHeckeExtReportJson(const HeckeExtRecord&)` and a streamed
`StreamHeckeExtReportJson(std::ostream&, …)`, hand-rolled exactly like `HeckeReport.cpp` (no
escaper needed: the writer emits only literals, numbers and enumerated strings), schema
`"hecke_ext/v1"`, keys and nesting **verbatim from [E §7] v1.1**, with the conventions of
`hecke_report/v1` kept (`"poly_coeff_order":"low->high degree (A-N4)"`, `HeckeReport.cpp:113`;
matrices as arrays of rows; `residue_degree` vs `residue_degree_lower_bound` never conflated). The
v1.1 keys that make a record reproducible by a third party ([E §7]) are all emitted: top-level
`commit` (the git hash baked in by CMake, like `OC_SOURCE_DIR`), `model` (`"sl2z_7vertex"`),
`iota_sign`, `convention_check`, `sturm`; per ideal `local`, `witness_poly`, `coefficient_field
{w_hat_exponent, P}`, `certificate ∈ {"cyclic","commutant","sturm(B')","unavailable"}`,
`generators_certified`, `sturm` — **verbatim the [E §7] object** `{B_prime, cap, closure_dim,
dim_M_k}` — with the swept list under a separate key `sturm_primes` and the route outcomes under
`certificate_routes` ([XA m13]), `tangent` (over `K`), and per module `structure_maps[].matrices`
(rows = bottom-layer basis, columns = top-layer basis, one matrix per generator) beside `rank`.
The unavailable groups are `null` with `"status":"unavailable"`; predictions are annotations
(`predicted / confirmed / unpredicted`), never gates ([Q14] default). The report is embedded in the
campaign per-job JSON as `"extensions": {…}` and written standalone by
`WriteHeckeExtReport(json, path)` with the default path `hecke_ext_ell<ell>_n<n>.json`.

### 1.5 Campaign integration

The spec grammar (`Campaign/CampaignSpec.h:16-55`; key parsing `CampaignSpec.cpp:256-304`, unknown
key = spec error at `:304`) gains campaign-wide keys:

```
ext      = true | false           # run the extension engine per (n, ell) cell (default false: today's campaign byte-identical)
family   = 2,3,5,7,ell            # the operator set S_0 ([E Stage 1]); `ell` is the literal token for U_ell,
                                  # admitted only through the u_ell budget below
u_ell    = auto | off | budget_mb=<M>   # [XA B3]: auto = include U_ell iff the frozen RSS model
                                  # (ell+1)*(0.123152 + 2.24985e-4*(n+1)^2) MB <= M (default M = 2048; v1.7:
                                  # FROZEN as u_ell_rss/v2-2026-09-17 by slot-3 WP-1, so the decision is a pure
                                  # function of (n, ell, M)); off = never; the verdict is recorded as u_ell{}
sturm    = auto | off | cap=<B>   # certificate (c): auto = compute B'(k, ell) with the default cap 12*B(k) ([E Def. 2.8])
                                  # and sweep primes <= B' where (a)/(b) leave room; cap=<B> overrides B_max;
                                  # the outcome (B' or none, cap, closure_dim) is recorded either way
sign     = all | plus | minus     # E3: run per iota-sign (default all = both signs and the unsplit record)
ext_groups = bulk | bulk+bd | all # E4/E5: which of the six groups (default: everything available)
```

**The settings layer (R1, v1.5).** [OD] R1 adds a second family of settings beside the engine knobs
of [P §2 C4]: **mathematical settings**, which are part of what a result *means*. They are one
struct, `Hecke/HeckeSettings.h` (`MathSettings`, §1.2), engine-owned — the engine owns the defaults
and the validation of values, the campaign spec and the console only *set* them, through the
registry of §7 — and **every record and every console handle stores the values in force**. The
table is [OD] R1's, with the defaults **decided** on 2026-09-16 (slot-1 confirmations 4, 6, 7, 8).
**(v1.8) Registration status.** Six keys are registered in `Hecke/HeckeSettings`, in fingerprint
order: `locality` (slot-2 WP-1), `u_ell` (slot-3 WP-1), `sturm` and `sturm_unavailable`
(slot-3 WP-2), and `commutant_budget` and `final_mode` (slot-4 WP-1). Each was **appended with
its default unchanged**, so the all-defaults fingerprint is still `0` and no golden value or
campaign job id has moved. Two of this table's key names are **not** the registered spellings —
`sturm.cap` is registered as `sturm` and `sturm.unavailable` as `sturm_unavailable` — and the
rows now say so ([WP1] finding 4; [E] §7's example carries the same slip and is booked there).
The rest of the table is unregistered and arrives with its consumer.
**(v1.10) Eight keys are registered** (slot-5 WP-7 added `field_polynomial` and
`split_field_report`); **slot 6 registered none.** The refrain "each appended with its default
unchanged, so no golden value or job id moved" was true **before** slot 5's emission and is
**false after it**: the record's `settings` object is `MathSettings::to_json()`, which prints
**every** registered key with its value and `source`, and it sits inside all 62 golden
`ext_json_*` texts (31 tier A + 31 tier B). **Registering any key now moves 62 golden lines** and
`EngineDeterminismValidation`'s digest. The next key (`presentation`, then `predictions`,
`coefficient_ring`, …) therefore waits for slot 7's recipe change — a path-scoped redaction of the
record's **top-level** `settings` object to `{fingerprint}` (not `RedactJsonKeys`, which also
matches the top-level `u_ell` verdict) — after which registration at the default is
key-additive again (§8, the slot-7 re-baseline, stage 1).
**(v1.11) Ten keys are registered, and registration is key-additive since slot-7 stage 1.**
Stage 1 (1) (slot-7 WP-2, R2 `97dbf9b`) reduces the record's top-level `settings` member to
`{"fingerprint": …}` in both golden `ext_json_*` texts and in `HeckeExtDeterminismValidation`
(a depth-1 member walk, `ReduceSettingsToFingerprint`, exposed once as
`GoldenReduceSettingsToFingerprint`); a scratch arm registering a dummy key at its default moved
nothing (dump, reference and ext digest byte-identical). Stage 1 (2) then appended **`presentation`**
(`off | on`) and **`predictions`** (`annotate | assert`) by the four-edit rule at zero golden
movement — `keys()` = 10, all-defaults fingerprint `0`. The **source argument** exists:
`ScopedUEll(u, src = Console)`, `ScopedMathSettings(s, src)` (via `MathSettings::with_source`); a
value at its default is always stamped `default`, the golden harness stamps `spec` (slot-7
confirmation 13), every other caller `console`. Rule (2) below still holds for the **record**
(the full block with every value and `source` is emitted); only the golden texts and the ext
digest see the fingerprint alone. The per-job campaign JSON's `settings` block **does** move on a
registration — never an id, a file name, an ext tag or a header (`campaign.md`, WP-2).

| Setting | Campaign key | Values (**default**) | Record key | Consumer (phase) | Decided by |
|---|---|---|---|---|---|
| `final_mode` | `final_mode = closure \| sturm_heuristic` | **`closure`** | `settings.final_mode`; per ideal `final ∈ {true, false, "heuristic"}` | `is_final` (E2) | OQ8; disposition: confirmation 8 |
| `sturm.unavailable` — **registered as `sturm_unavailable`** (v1.8) | `sturm_unavailable = nonfinal \| heuristic` | **`nonfinal`** | `sturm.mode` | `SturmCertificate` (E1b) | OQ15; confirmation 6 |
| `sturm.cap` — **registered as `sturm`** (v1.8) | `sturm = auto \| off \| cap=<B>` (existing) | **`12·B(k)`** | `sturm.cap`, `sturm.resumable.budget_history` | `HeckeSturmBound` (E1s/WP-3) | OQ15; confirmation 6 |
| `commutant_budget` (**v1.8**, slot-4 WP-1) | `commutant_budget = <N>` | **`2·10^10`** (`kCommutantBudget`, whose one definition moved to `Hecke/HeckeSettings.h`, `CommutantRoute::kCommutantBudget` a `constexpr` alias) | `settings.commutant_budget`; `resumable.budget_history` on the commutant state | `CommutantRoute` (E1a / E2a) | [S4] §2.3 item 3, [OD] slot-3 confirmation 3 |
| `locality` | `locality = budget=<N> \| strict` | **`budget=64`** | `level_c.locality = {mode, budget, resumable}`; per block `local` | the refinement loop (E0b) | OQ16; confirmation 7 |
| `field_polynomial` | `field_polynomial = least \| conway` | **`least`** (`conway` reserved: parsed, rejected as "not implemented"; v1.10: parsed and validated as a setting, the consumer `FieldPolynomialFromSettings` raises `NotImplementedInThisBuild` — and two production entry points bypass it, open item 4 of v1.10; **v1.11: routed** — `CanonicalField(ell, r)` and `CertifyCanonicalSplit` clause 3 take the polynomial from `FieldPolynomialFromSettings`, so under `conway` the constructor, `--bench ext`, the certificate, the atlas and the record consumer all raise it, slot-7 WP-4 arm I) | `field_polynomial` | `HeckeCanonicalField` (E6) | OQ9 |
| `split_field_report` | `split_field_report = canonical \| own_field` | **`canonical`** (subject to E6's performance gate, §6.2 E6 (d) since v1.10; raised to the owner at the slot-6 close, open item 1; **v1.11: the gate is MET** (W1) and the consumer ships — the per-ideal `split` of `hecke_ext/v3`, slot-7 WP-3 item 6) | `split_field_report` | the report layer (E6) | OQ10 |
| `coefficient_ring` | `coefficient_ring = F_ell \| Z/ell^<k>` (`Z/<n>` reserved; **v1.12**: `2 ≤ k ≤ 63`, and `Z` reserved for line 2 — [IB] OD-10 (a), no golden cost; **v1.28: `Z` un-reserved for the integral descent only**, [C] `def:ringsemantics`(3), `sec:recordschema` item 7) | **`F_ell`** (**v1.12: registered**, slot-8 WP-3, the eleventh key, key-additive; `Z/<m>` refused inside `set()` by `NotImplementedInThisBuild` (**v1.28**: `Z` is stored and honoured by the integral descent only, every other consumer refuses it by name, exit 5; D6 audit M2); **refusal first** over the closure, [OD] S8-4: `EquivariantCohomologyOnK`, `HeckeOperatorOnK`, `HeckeReductionValidation` and the harness's E8 points honour a non-default ring, every other site refuses by name, exit 5; `ell ∈ {2, 3}` refused under a composite ring) | `coefficient_ring` (**record and campaign support: slot 9, with C5**; OD-10 (a)'s record keys only under `coefficient_ring = Z`, [OD] S8-6d) | the whole pipeline (E8) | OQ18 |
| `predictions` | `predictions = annotate \| assert` | **`annotate`** (`assert` is the debug switch of OQ14: a refuted prediction fails the run; **v1.11: registered**, slot-7 WP-2 stage 1 (2), consumer `predictions_mode` since item 7) | `predictions_mode` | `HeckePredictions` (E6); the validations of §5 | OQ14 |
| `presentation` | `presentation = off \| on` | **`off`** | `presentation` object present only when `on` | `HeckePresentation` (E2; v1.10: the unit shipped in slot-6 WP-2 **without** this key, reached through `ExtDriverOptions::with_presentation`; the key and the record object are booked for slot 7's re-baseline, stage 1; **v1.11: registered with its consumer**, slot-7 WP-2 stage 1 (2) — the per-ideal `{generator_basis: "block", relation_basis: "algebra_rref", fragment}` object of [E] `sec:schema` (e), `verify()` code 24) | OQ11 |
| `u_ell` | `u_ell = auto \| off \| budget_mb=<M>` (existing) | **`auto`, `M = 2048`** | `u_ell{…}` | Stage 1 (E1b) | [XA B3]; confirmation 4 |
| `integral_fallback` | `integral_fallback = forbid \| allow` | **`forbid`** | `solve_regime[3]`, `integral` | the fills of `τ` / `η` (E5) | OP2 |
| `q_max` | `q_max = <int>` (E9 only; a spec error on a finite model) | **derived** (`num_degrees() − 1`); settable only where `truncated = true` | `q_max`, `truncated`, `q_max_source`, `degrees` | E9 | OC-1 rider (i) |

Three rules bind every consumer. (1) **Golden objects pin the default configuration**: the harness,
`--bench` and every validation arm that compares against `GoldenReference.inc` run with every
setting at its default, and the **fingerprint** of the non-default settings (`0` at the defaults)
is part of every ext hash input — so a setting that changes a published value changes the hash,
and a golden mismatch can never be explained by "a different setting". (2) **A setting is recorded,
never inferred**: the record's `settings` block carries every value with its `source`, and the
campaign per-job JSON carries the same block; a resume with a changed budget is a new setting
(§1.3.1 R3.1 item 4). (3) **Job identity**: a job whose mathematical settings differ from the
defaults gets the suffix `_s<first 8 hex of the fingerprint>` on its `Job::id()` (the `_q…`
convention of `docs/matrix-engine/campaign.md` §4 — the default id is unchanged, so every published
file name stays), and the `shape_signature` string gains `s=<fingerprint>`; the campaign's own
`resume` is thereby keyed on the settings too. The keys are parsed in `CampaignSpec.cpp` beside the
existing ones (unknown key = spec error, `:304`) and validated by `HeckeSettings`, never twice.

With `u_ell = auto` and `M = 2048` the **frozen** model (v1.7; slot-3 WP-1 §4.3 — the v1.6 ranges
below were the placeholder constants' and are superseded) admits `U_ell` at every `ell ≤ 13` for
**`n ≤ 804`** (v1.6: `n ≤ 1000`), at `ell = 691` for **`n ≤ 110`** (v1.6: `n ≤ 220`), at
`ell = 3617` (`n = 14`, predicted 0.63 GB) and at `ell = 10007` only for **`n ≤ 18`** (v1.6:
`n ≤ 38`); it excludes `(16, 43867)` (8255 MB), `(22, 2294797)`, `(24, 657931)` and every
`ell = 134217757` cell. None of the excluded cells needs `U_ell` for a proof-range certificate
(`B' = 2` there, §5).

The ext record is **per `(n, ell)` cell, not per job** ([XA m14]): a campaign job is
`(n, ell, p, r)`, and running the engine inside `RunOneJob` would rebuild the same record once per
`p`. The driver therefore groups the planned jobs by `(n, ell)` (after `plan_campaign`,
`CampaignSpec.cpp`), runs `HeckeExtDriver` once per cell on the cell's first job's cohomology and a
`HeckeOperatorFamily` over `family ∪ {p of the cell's jobs}` (cohomology computed **once**; each
extra prime costs cosets + τ + Θ only, `HeckeOperatorFamily.h:112-113`, [XA M4]), and attaches the
`"extensions"` object to that cell's first job in the plan order — so the `jobs × threads`
determinism contract is unchanged. The shape signature (`CampaignSpec.h:120-130`: `n_sym, p, r,
degrees, model`) is extended by the family's prime set; the ext call follows the level-(c) loop at
`Campaign/CampaignDriver.cpp:634-677`; the per-job JSON gains `"extensions"` and
the object list (`EmitObjectsJson`, `:427`) gains the ext hashes; `summary.tsv` (`:1195`) gains the
columns `ideals`, `max_embdim`, `max_loewy`, `nonsplit_ideals`, `nonlocal_ideals`, `sturm_B_prime`,
`ext_certificate`, `ext_final`. `CampaignSmokeValidation`'s contract — the same spec at four
`jobs × threads` splits yields the same objects in the same order — extends to the ext objects
verbatim (§5, `HeckeExtCampaignValidation`). The `--bench` driver gains `ext <n> <ell> [family]`
(`Bench/BenchDriver.cpp` next to `RunDecomp`, `:424`) so the ext layer's time and RSS are on the
`BENCH` line, with the Sturm-bound time split out (`sturm_bound_s=`).

### 1.6 Golden-harness integration

**What gets hashed** (`Golden/GoldenHarness.cpp`, the per-kind FNV of `:217-261`, collectors at
`:288-320`; the grid `:165-173`). New objects per `(n, ell)` cell of the **ext subgrid** — `n > 0`
even and `5 ≤ ell < 2^32`, i.e. `n ∈ {2, 4, 10, 16, 22, 24}` × `ell ∈ {5, 13, 691, 10007,
134217757}` plus `(32, 5)` ([XA M3]: outside it Eichler–Shimura and `d_2 = 0` do not hold, and the
engine is `uint32_t`-only) — computed from the same `{T_2, T_3, T_5}` family the harness already
decomposes at `:614-620`, with the Sturm sweep's primes `≤ B'` taken from that family's cache when
they lie in it and streamed otherwise, and with **`u_ell = off`** (the golden harness never builds
`U_ell`: no proof-range certificate on the subgrid needs it, and `U_10007` would cost ≈ 1.5 GB per
cell at `-O0`; [XA B3]). Every other grid cell (and every 64-bit point) gets one tier-A text object
`ext_excluded` naming the violated condition, exactly as the harness already records shipped
predicates (the `dickson` scalar of `GoldenHarness.cpp:363`):

* tier A: `ext_ideals^q` — FNV over (ideal count; per ideal: dims per group, `f`, `N`, `π_w`, every
  `P_p`, `local`, `dim A_S`, `embdim`, `ν`, `dim soc`, `hilbert`, `gorenstein`, the `K`-tangent table,
  Loewy and socle layer dims per group, Jordan partitions (units of `f`) per generator,
  structure-map ranks, `certificate.kind`, `final`); `ext_certify^q` (the aggregate `verify()`
  code); `ext_json_canonical^q` (the report with bases and matrices redacted, via `RedactJsonKeys`,
  `:426`); **`sturm_bound`** per `(n, ell)` (FNV over `k, ell, dim M_k, B_max, B' | none,
  closure_dim`, and the Miller-basis matrices `T_q mod ell`, `q ≤ B'`); from E3: `charpoly_iota^q`,
  `rank_iota^q`, `dim_Hplus^q`, `eisenstein_line_defined`; from E4: `dim_H0_bd`, `dim_H1_bd`,
  `rank_r^q`, `charpoly_A_bd(T_p)^q`, the `χ_b` multiset; from E5: `dim_H1c`, `dim_H2c`,
  `les_exact`, and **`charpoly_A_c(T_p)^q`, `rank_A_c(T_p)^q`, `trace_A_c(T_p)^q`** — canonical for
  `ell ≥ 5` because the cone operator is independent of `(τ, τ_∂, η)` there (C-A3(ii.5)(b)/(c),
  [V §2.5], [V §2.6.1]) — plus the diagnostics `eta_zero`, `cochain_commutes` and the three
  `solve_regime` values.
* tier B: `ext_algebra_basis^q`, `ext_loewy_bases^q`, `ext_structure_maps^q`, `iota^q`, `r^q`,
  `A_bd(T_p)^q`, `A_c(T_p)^q`, `ext_json_full^q`; from E5 additionally `Theta_bd_flat^q`,
  `h_flat^q`, the cone bases (`Z^q(C(r))`, `B^q(C(r))`, `H^q(C(r))`) and the three table hashes
  (`tau_boundary`, `eta`, and the bulk `τ` as it is already stored) — all of them choice-dependent,
  but in **two different senses**, which §5's arm must keep apart: `A_c(T_p)^q`, `iota^q`, `r^q` and
  the cone bases are **stored-basis**-dependent (the D5b elimination rules), and a different `η` or
  `τ_∂` leaves them **bit-identical**, because `D(a, b) = (−da, db + ra)` involves neither `τ_∂` nor
  `η`; what a different `η` or `τ_∂` actually moves is `Theta_bd_flat^q`, `h_flat^q` and the three
  table hashes — and **not** the tier-A objects, which is exactly what `HeckeConeValidation`'s
  two-`η`/two-`τ_∂` arm asserts (§5).

**Existing tier A/B objects are untouched by E4/E5**: the bulk `τ` and `Θ_flat` do not change
([V §7] item 6).

**The tiering above is the owner's decision OP7, 2026-09-15** (§11; [V §7] item 6's proposal
accepted as proposed): `dim X_3`, `dim X_6` and `A_c` char-poly / rank / trace in **tier A**;
`Θ^∂_flat`, `h_flat`, the cone bases and the three table hashes in **tier B**. The alternative —
keeping the choice-dependent objects out of the golden reference entirely — is not taken. Note the
distinction the paragraph above draws, which the v1.3.1 audit's finding **F2** forced and which
the decision preserves: the
cone bases are in tier B because they are *stored-basis*-dependent, **not** because a change of
`η` or `τ_∂` moves them — it does not.

**The re-baseline the E0 fix forces, and how it is explained.** The reference
(`Golden/GoldenReference.inc`, 14049 entries) stores hashes, not texts, so "explain every changed
line object by object" (CLAUDE.md, `GoldenEmit`) needs the old texts. `GoldenDump` — owner-gated
like `GoldenEmit` (`Golden/GoldenHarness.h:25-39`: a no-op unless `GOLDEN_DUMP=<dir>` is set) —
writes every *text* object (`report_full^q`, `report_canonical^q`, `op_json_full`) **and every
decomposition's block list** (per block: `dim`, `residue_degree`, `char_poly` / `min_poly` /
`jordan_partition` per operator, `residue_degree_certified`, `residue_witness`, and the
`change_of_basis` columns — exactly the inputs of the four hashes `_invariants`, `_certify`,
`_witness`, `_U` of `CollectDecomposition`, `GoldenHarness.cpp:488-510`, plus `certify()`) to files.
**It lands in E0a, a value-preserving commit of its own**, so that the "before" dump is taken by a
binary that already contains it ([XA M2]; v1.1 ran it "on the pre-E0 binary", which would not have
had it). The protocol:

1. **E0a** lands (value-preserving: `GOLDEN_STRICT=1 GoldenRegressionValidation` unchanged, tier A
   9446 / tier B 4603 mismatching 0). On it: `GOLDEN_DUMP=before ./cohomology_app GoldenDump`.
2. **E0b** lands. `GOLDEN_DUMP=after ./cohomology_app GoldenDump`; `GoldenRegressionValidation` now
   lists the mismatching entries.
3. `docs/matrix-engine/tools/golden_explain.py before after` does two things and fails on either:
   (i) for every mismatching **text** entry it prints the JSON key paths that differ and fails unless
   every difference lies in the allow-listed set for this re-baseline — read from a file
   (`--allow-keys e0b.keys`, [SP] WP-1 scope 4), which for E0b holds **ten** paths (v1.6; the
   shipped `docs/matrix-engine/tools/e0b.keys`) `{schema,
   level_c.blocks[].multiplicity_note, level_c.blocks[].local, level_c.blocks[].witness_poly,
   level_c.blocks[].coefficient_field, level_c.locality, q_max, truncated, q_max_source,
   degrees}` — `degrees` being the slot-2 plan's addition under owner confirmation 1(b), the
   complex's own degree list `[0 .. q_max]`, derived ([S2] §2.3 item 1) — G1's
   corrected note text, the schema bump `hecke_report/v1 → v2`, the three new block keys named as
   in [E §7], the `locality` settings object of §1.5, and **the three oc1a record fields batched
   into this same re-baseline** (slot-1 confirmation 3, DECIDED: `q_max`, `truncated` and the
   derived/set marker `q_max_source` of [C] `sec:recordschema` item 5 land at record level in
   `Hecke/HeckeReport.{h,cpp}` beside the per-degree `degree` of `HeckeReport.h:91`, as the constants
   `2` / `false` / `"derived"` on the 7-vertex model; `Campaign/CampaignDriver.cpp:723-724`, which
   already emits `"degrees":[…]`, emits the same three, un-hashed; [C]'s "not implemented now"
   sentence becomes a `Y` bump). **As shipped (v1.6, slot-2 WP-2, 2026-09-16):** the four fields
   per complex, derived from `HeckeReportInput::num_degrees`, **which the writer now requires**
   (throws on 0 — E2's `hecke_ext/v1` writer must supply the complex it describes rather than
   rediscover this from an exception); `P` emitted as an object **keyed by prime**; `resumable`
   **not** emitted in the report; `level_c.locality` carries the `locality` value and its
   source, **not** the `MathSettings` fingerprint (that lands in the ext record and the job id,
   E2). The re-baseline: **384 lines, 0 elsewhere, 0 splits**, `golden_explain.py` exit 0 with no
   `--accept-split`; digest `0x2fa804dae5e9d98d → 0xe446b3bd2d28bd6e` (30 of the 966 records of
   `GoldenSubset32` are `report_*`); note
   `docs/matrix-engine/rebaseline-2026-09-16-hecke-report-v2.md`; `e0b.keys` stays in the tree
   as the record of what was allowed and is **not** reused by a future re-baseline; [C]
   `sec:recordschema` item 5 says "implemented" since [C] v1.4.2; (ii) it diffs the
   dumped **block lists** and fails on **any** difference in any input of `_invariants`, `_certify`,
   `_witness` or `_U`, unless that decomposition is named in an owner-accepted split list passed on
   the command line (`--accept-split "<point> <object>"`), which the commit then quotes.
4. `GOLDEN_EMIT=1 ./cohomology_app GoldenEmit`; the commit carries the script's summary (count per
   key path, and the accepted splits, if any) as the object-by-object explanation.

Which entries move is *predictable*: `report_canonical^q` (tier A, **192** entries on `0fb142d`) and
`report_full^q` (tier B, **192** entries) — **all 384 lines**, because the schema string occurs in
every report text ([SPA] Q3; [RB §3]'s "190" was the count *changed* by the τ move, not the
population), and **0 lines in the other 47 kinds** — the JSON text changes, and it changes **only
because E0b edits `HeckeReport.cpp`**, which is where `BuildHeckeReportJson` writes the schema
(`:109`) and the `level_c.blocks` keys (`:189-230`) that the golden texts are made of
(`GoldenHarness.cpp:601-604`); `HeckeModuleDecomposition::to_json` is hashed nowhere ([XA M1]), and
`op_json_full` is written by `HeckeOperatorOnK::to_json` (`GoldenHarness.cpp:566`), not by
`HeckeReport`. **This is the one re-baseline of the stage** ([SP §4.2]): slot 1 changes no golden
value, E0b's emission in slot 2 is the only mutating one, and E1–E9 add entries only.
**(v1.10) Corrected: that last clause is false for E6, and conditional for the rest.** After slot
5's add-only emission the default `hecke_ext/v2` text is 62 golden lines; E6's record integration
(atlas labels, the canonical split in the record, `predictions_mode`, an atlas-decided
`proof_range`, `S_sep` in the default Stage 2(3)) **changes** that text, and any phase that
registers a settings key moves the same 62 lines (§1.5, v1.10). E7's objects are add-only. The
programme's remaining golden events are therefore **one separate E7 add-only emission and one
staged, owner-gated, changed-line re-baseline, both in slot 7** ([OD] S6-3, §8).
**(v1.11) Both events are made** (slot 7; the ledger is quoted in
`docs/implementation/slot7/WP-14_report.md` §2). **The recipe**: `ext_json_canonical` /
`ext_json_full` are `RedactJsonKeys(ReduceSettingsToFingerprint(j), {…})` — the top-level
`settings` member reduced to `{fingerprint}`, the `commit` (and `t_p`) redaction as before — so a
key registered at its default moves no golden line, and a setting in force moves every text
through the fingerprint. **The instruments**: `golden_ref_diff.py BEFORE.inc AFTER.inc --expect
FILE` (slot-7 WP-1; the `(point, object, tier)` added / changed / removed sets, gate = set
equality with the pre-stated sets) beside `golden_explain.py` (the key paths of each changed text);
a changed raw object is explained through its cell's `ext_json_*` diff, and one that the text diff
cannot explain is a stop. **The record at the close is `hecke_ext/v3`** (stage 3), 17 317 entries
(A 11 472, B 5845). The remaining golden events of the programme are **add-only** (E8's `Z/ell²`
objects, E9's) plus whatever an owner ruling adds; a key registration is not one.
**None of the four decomposition hashes moves** unless a non-local block exists on the grid: they
hash only the existing `PrimaryBlock` fields (`:490-506`), and E0b **must not add its new fields
(`local_certified`, `witness_poly`, `w_hat_exponent`, `character`) to `CollectDecomposition`** — they
reach the golden reference through the report texts (above) and the new ext objects (E2). §3.3
turns "none moves" into a proof over all four hashes. E1–E5 only *add* entries (new object names),
which is the trivially explained case.

The published campaign records under `docs/matrix-engine/results/` (2745 per-job JSONs carrying
`hecke_report/v1`) become **stale by schema** after E0b. They are not regenerated by E0b; its commit
message and `docs/matrix-engine/results/README.md`'s first line say so, and the first ext campaign
(E6) republishes under v2 ([XA m18]).

---

## 2. Stage-by-stage mapping of [E §5] to code

### 2.1 The primitive inventory

| Primitive | Exists? | Where | Used by |
|---|---|---|---|
| dense product, RREF, pivots, rank, inverse, kernel, image on `MatrixT` | ✓ | `ModArithmetic/ModArithmetic/Matrix.h:90-108` (`kernel` `Matrix.cpp:434`, `image` `:466`) | everything in `HeckeExt/` |
| exact restriction `B X = A B` (invariance certificate) | ✓ but file-local | `HeckeModuleDecomposition.cpp:68-94` `SolveColumnsExact` | E0a moves it to `SubspaceOps.h` (`restrict_to_invariant_subspace`) — [PA A9]'s `restrict` |
| primary decomposition, Jordan partitions, RCF within a block | ✓ | `HeckeModuleDecomposition.cpp:386-518` (single), `:525-768` (multi), `PartitionFromNullities` `:180`, `PrimaryRCFBasis` `:224` | Stage 2, (D3) |
| charpoly (Berkowitz, `O(d⁴)`), minpoly (Krylov), `P(A)` | ✓ | `FpPoly.cpp:332, 402, 385` (`EvalPolyAtMatrix`) | witness, `P_p(ŵ)`, locality, nilpotency |
| irreducibility / factorization certificates, squarefree, `powmod`, Frobenius | ✓ | `FpPoly.cpp:598, 617, 589`; `FpPoly.h:97-100` | locality, residue field, E6 |
| `CanonicalLess` | ✓ | `FpPoly.h:114-115` | ideal ordering, `C_{ell,r}` |
| the Teichmüller lift `ŵ = w^{ell^N}` (a `D×D` matrix raised to `ell` `N` times, square-and-multiply) | ✓ (products only) | `Matrix.h:90-108` | Stage 3.2, `LocalityCertificate` — `N·⌈log₂ ell⌉` products, `O(N D³ log ell)` |
| truncated power series mod `ell`, `E_4`, `E_6`, `Δ` `q`-expansions mod `ell`, the Miller basis of `M_k(F_ell)`, `T_q` on it | ✗ | **new** `HeckeSturmBound` (`ModPowerSeries`, ≈ 300 lines) | Stage 4(c), `B'(k, ell)` |
| `hstack`, `vstack`, `vec`/`unvec`, column space, sum, intersection, preimage, quotient complement | ✗ (an `HStack` helper is file-local at `HeckeModuleDecomposition.cpp:96`) | **new** `SubspaceOps` | Stages 3, 5 |
| algebra closure (span of monomials in commuting generators until stable) | ✗ | **new** `SubspaceOps::algebra_closure` (used by `HeckeLocalAlgebra` on `D`-sized and by `HeckeSturmBound` on `dim M_k`-sized matrices; in `SubspaceOps` so the Sturm unit stays pipeline-free, [XA m16]) | Stage 3.1, Stage 4(c) |
| radical / nilpotency test / powers of an ideal / annihilator (socle) | ✗ | **new** `HeckeLocalAlgebra` | Stage 3.2 |
| commutant of a set of matrices: the socle-bound pre-test, the structured system over `End_{F_ell[a]}(V)` for a fixed cyclic-most `a`, and the naive oracle | ✗ | **new** `HeckeGenerationCertificates` (the rational canonical form of one operator on a primary block reuses `PrimaryRCFBasis`, `HeckeModuleDecomposition.cpp:224-317`, promoted to `SubspaceOps`) | Stage 4(b) |
| membership of a matrix in a subalgebra (one solve against the RREF coordinate basis) | ✗ | **new** | Stage 4(c) |
| seeded deterministic pseudo-random elements | ✓ | `SplitMix64` `HeckeModuleDecomposition.cpp:48-58`, seeds `:26, :31`, `FpPoly.h:177` | §4: **no new randomised search in production** |
| symmetric power `ρ_n` of any `2×2` mod `ell` (monoid, `det ≠ 1` included) | ✓ | `ModArithmetic/ModArithmetic/FlatMatrix.h:204` (`FlatMatrix.cpp:1944`) | `ρ_n(δ_j)`, `ρ_n(ι)` (E4/E3) |
| the Dickson multiplication `L·: Sym^{n−ell−1} → Sym^n`, `L = x^ell y − x y^ell` (an `(n+1) × (n−ell)` matrix with entries in `{0, ±1}` in the monomial basis; `L(g·(x, y)) = det(g)·L(x, y)` for every `2×2` `g` over `F_ell`, hence Hecke-equivariant up to the `det`-twist of [E Claim 2.12]) | ✗ ([I G12]) | **new** `HeckeExt/DicksonMultiplication.{h,cpp}` (≈ 100 lines; the `det`-twisted intertwining with `ρ_n` and `ρ_{n−ell−1}` checked entrywise on seeded `g`, in the action convention of [C, def:rhon]) | the `L·H^1` canonical position (E2) |
| `DicksonInvariantCount(n, ell) = #{(a, b) : a(ell+1) + b(ell² − ell) = n}` | ✗ (three file-local copies of the boolean `IsDicksonExceptional`: `HeckeOracleValidation.cpp:237`, `HeckeEndToEndValidation.cpp:98`, `GoldenHarness.cpp:363`) | **new** public `Hecke/DicksonCount.h` (E0a); the three copies become `count > 0` for `n > 0`, the golden `dickson` tier-A entry unchanged ([XA m2]) | identity 1, `IdentityCertificate` |
| per-simplex block-row cochain morphism + induced maps on cohomology | ✓ | `EquivariantCochainComplexMorphismOnK.h:34-48, 146-150, 155, 185` | `ι` (E3), `r^q` (E4), `L·` (E2) |
| cusp circle local system and the restriction demo | ✓ (demo only) | `LocalSystemPresets.h:15` `CreateS1Generic`; `LocalSystemSL2Z.cpp:843-923` | E4 lifts the demo (G3) |
| mapping cone for plain `CochainComplex` | ✓ (trivial coefficients) | `SimplicialCohomology.h:217-227`, `.cpp:832, 937, 985` | the template E5 ports |
| `τ`-table construction: orbit walk, step-2 path search, step-3 integer fill, the (T1) helper and `certify()` | ✓ | `Hecke/HeckeTauTable.h:23-26, 76-88, 233, 260-281` | the **`η`-table builder** (E5) reuses all of it with `∂X` as source ([V §7] item 5); `used_mod_ell_solve()` is the `solve_regime` flag of §1.2 |
| `engine::elim` `rref / kernel_basis / image_basis / solve_multi_rhs / complement_basis` on `FlatMatrix` | ✓ | `ModArithmetic/ModArithmetic/DenseElim.h:111-158` | the cone (E5) |
| Bernoulli numbers mod `ell` | ✗ | **new** `HeckePredictions` (`bernoulli_mod(w, ell)`: the `F_ell` recursion `Σ_j C(w+1, j) B_j = 0`, valid for `w < ell − 1` by von Staudt–Clausen; no bignum needed — this settles [PA A9]'s Bernoulli question) | E6 |

### 2.2 Stage → code unit

**Stage 1 — base operators** ([E Stage 1]): `HeckeOperatorFamily::prepare({(p,1)})` + `T_p(p)` for
`S_0 = {2, 3, 5, 7} ∪ {ell if the U_ell budget admits it}` (`Hecke/HeckeOperatorFamily.h:247, 120`;
`U_ell` is the same path, `:114-120`). **The `U_ell` coset budget** ([XA B3]): `U_ell` has `ell + 1`
cosets and its RSS is ≈ linear in cosets with an `n`-independent per-coset term (the coset / τ
tables) and an `n²` term; on the measurements of [I §3.4] (`hecke 10 691 691`: 98 MB, 1.29 s;
`128 5 401`: 503 MB; `256 5 97`: 722 MB) the fit is
`predicted_mb(n, ell) = (ell + 1)·(0.11 + 5.8·10^{−5}(n + 1)²)`, giving ≈ 5.6 GB at `(16, 43867)`
(v1.1's "≈ 1 GB" was wrong, [XA M4]) and ≈ 19 GB at `(690, 691)`. **(v1.7) Frozen by slot-3 WP-1 on
16 measured points** as `(ell + 1)·(0.123152 + 2.24985·10^{−4}(n + 1)²)` MB,
`kUEllRssModelVersion = "u_ell_rss/v2-2026-09-17"`, residual band `+17.9 % / −15.9 %` asserted both
ways (two three-parameter forms rejected: no better under-prediction, one with a negative
coefficient); 8255 MB at `(16, 43867)`, ≈ 74 GB at `(690, 691)`. E0a re-measures `(16, 43867)`,
`(128, 691)` and `(256, 131)` once, re-fits the two constants, and **freezes them in code**, so
`include U_ell ⇔ predicted_mb ≤ budget_mb` (default 2048, campaign key `u_ell`, §1.5) is a pure
function of `(n, ell, budget)` and records stay reproducible. Where `U_ell` is omitted the record
says so (`operators_computed`, `u_ell.reason = u_ell_over_budget`). The consequences are stated where
they bite: the proof-range Sturm certificate never needs `U_ell` unless `ell ≤ B'` (§1.3), and when
`ell ≤ B'` the prime is small and the budget admits it at every `n ≤ 1000` measured
(`ell ≤ 13` ⇒ `≤ 0.82 GB`; **v1.7**: at `n ≤ 804` under the frozen constants, which is still every
`n` a proof-range certificate at `ell ≤ 13` has needed so far). `IdentityCertificate` runs at once: `[A_p, A_{p'}] = 0` explicitly (today
only implicit through the exact solve, [I §1 Stage 1]), `dim H^1 = dim M_k + dim S_k + dim H^0` with
`dim H^0 = DicksonInvariantCount(n, ell) = #{a(ell+1) + b(ell²−ell) = n}` — a **new public count**
(§2.1): the existing predicate `IsDicksonExceptional` is a boolean ("exists `(a, b)`, `n > 0`")
with three file-local copies, not the count ([XA m2]) — `d_2 = 0`, and the `p²` recursion of
[C, thm:relations]; all of them only on `n > 0` even, `5 ≤ ell < 2^32` (§1.3). **Cost** ([XA M4]):
the cohomology run is paid **once per `(n, ell)`** — `HeckeOperatorFamily` takes the computed
`cohomL` (`HeckeOperatorFamily.h:112-113`) — and each prime adds cosets + τ + Θ: at `n = 128`,
`T_2` ≈ 0.03 s on top of `cohom 128`'s 0.09 s (CLAUDE.md), `T_401` ≈ 12× `T_2` ([I §3.4]). v1.1's
"each extra prime costs a full `cohom`" misread [E Stage 1] and overstated the sweep by ≈ 2×.

**Stage 2 — maximal ideals** ([E Alg. 5.1]): `HeckeModuleDecomposition::ComputeMultiOp` per group
(`X_4` then `X_1`; per sign from E3), **with the E0 locality refinement** (§3), whose loop is
**bounded**: 64 linear witnesses per block, then `local = false` and the record is not final
([E Alg. 5.1(2)]; the linear witnesses provably suffice when `f` has at most `ell` distinct prime
factors and, for separation, when `min(f, f') ≤ ell` — automatic for `ell ≥ 5`, `f < 30030`,
[E Cert. 5.2]). Cross-group identity of ideals (the spec's `T_∞ ⊆ End(H_tot)`): the per-group
decompositions are matched by an **evaluation test with one block's own witness** ([XA M5]):
blocks `B` (witness `w = Σ c_p t_p`, `π_w`, `{P_p}`) and `B'` carry the same `m` iff `π_w(w|_{B'})`
and every `t_p|_{B'} − P_p(ŵ')` are nilpotent, where `ŵ' := (Σ c_p t_p|_{B'})^{ell^{N'}}` with `B`'s
`c` and `N'` the least multiple of `f` with `ell^{N'} ≥ dim B'` (the exponent must bound the
nilpotency index on `B'`, not on `B`). This is deterministic, needs no shared candidate sequence —
v1.1's "first entry of the deterministic candidate sequence that is a witness in both" was
ill-defined, because the sequence is seeded by the block dimension
(`HeckeModuleDecomposition.cpp:695`) — and needs no "up to Galois": a Frobenius-conjugate character
passes (it is the same maximal ideal) and a different one fails (§1.3 `ExhaustivenessCertificate`,
which uses the same test for pairwise distinctness within a group). Matching runs `B` over `X_4`'s
blocks in their fixed order and `B'` over the other group's. A joint decomposition of `⊕ X_i` under
the block-diagonal operators is kept as the *oracle* in `HeckeExtAlgebraValidation` (it is the
literal definition but costs `O((Σ d_i)⁴)` per charpoly). The label (cuspidal / Eisenstein-type /
both) is E6. **Stage 2(3)** ([E Alg. 5.1(3)], [XA M7]): once the atlas exists (E6), if it does not
certify that `S_0` separates `Σ(ell) ∪ {χ_a}`, the driver adds `S_sep(ell)` to `S_0` and **re-runs
Stage 2** (not only the Sturm sweep); the record lists both operator sets and the blocks that split
in the re-run (a split there is a finding: two systems that `S_0` did not separate).

**Stage 3 — the local algebra** ([E Alg. 5.4]): `HeckeLocalAlgebra::Compute(block, {t_p})`:
1. `A_S`: start from `{I}`, multiply the current basis by each `t_p`, `vec` into rows of a
   `dim × D²` matrix, RREF, stop when the rank is stable. Commutativity bounds the products to
   monomials of degree `< ν ≤ D`. The RREF coordinate matrix is kept — membership (Stage 4(c)) and
   coordinates of any element are one solve.
2. **The coefficient field and the `P_p`** ([E Claim 3.3], [E Cert. 5.2]): `N :=` the least multiple
   of `f` with `ell^N ≥ D`; `ŵ := w^{ell^N}` by `N` successive `ell`-th powers; assert `π_w(ŵ) = 0`
   exactly (Frobenius is a ring endomorphism of `A_S`, so this is an identity, and its failure is a
   bug, not a finding). For every `p ∈ S`: `U := ker π_p(t_p) ∩ ker π_w(w)` (an `A_S`-submodule
   containing `soc V`, hence nonzero when `V` is local — computed as `ker [π_p(t_p); π_w(w)]`, one
   stacked kernel); `v :=` its first D5b kernel-basis vector; solve `t_p v = Σ_{i<f} c_i ŵ^i v` —
   one `D × f` system, consistent with a unique solution when `V` is local (`v, ŵv, …, ŵ^{f−1}v`
   are independent because `F_ell[w]|_{ker π_w(w)}` is a field); `P_p := Σ c_i X^i`;
   `n_p := t_p − P_p(ŵ)`; **certificate**: `n_p` nilpotent on all of `V` (`n_p^D = 0` by
   `⌈log₂ D⌉` squarings, `O(D³ log D)`, [XA m4]). Inconsistency or non-nilpotency ⇒ the block was not local ⇒ E0's refinement
   (§3.1). The witness direction is included automatically (`n_w = w − ŵ = Σ c_p n_p`), and for a
   trivial single-operator witness `w = t_j` this gives `n_j = t_j − ŵ`, **not** `0`.
   `m_S :=` the ideal generated by the `n_p` inside `A_S` (span of generators × basis, RREF; **no
   separate `π_w(w)` generator** — `π_w(w) ∈ (n_w)` already); `m_S^i` iteratively; `ν`;
   `soc A_S = Ann_{A_S}(m_S)` (kernel of `a ↦ (a·n_p)_p`); `dim_{F_ell} soc = f` ⇔ Gorenstein;
   `hilbert[i] = dim(m_S^i / m_S^{i+1}) / f`.
3. **Tangent test over `K`** ([E Alg. 5.4(3)]): the images `n̄_p` in `m_S/m_S²`, which is a
   `K`-vector space through `ŵ`; the `K`-span of a set of `n̄_p` is the `F_ell`-span of
   `{ŵ^i n̄_p : 0 ≤ i < f}`; `active[p]` and the minimal subset of `S` whose `K`-span is all of
   `m_S/m_S²` (greedy in ascending `p`, deterministic); `embdim = dim_{F_ell}(m_S/m_S²)/f`. Over
   `F_ell` one direction would count as `f` directions, and with `P_p(w)` in place of `P_p(ŵ)` the
   witness's own direction is lost ([EA B2]) — both are pinned by `HeckeExtAlgebraValidation`'s
   `f = 2` arms (§5).

**Stage 4 — certifying `A_S = T_m`** ([E §5 Stage 4]), in the practical order (a) → (b) → (c):
* (a) `CyclicityCertificate`: `dim V/m_S V = f` — **deterministic**, no random vectors ([E Cert. 5.5]
  improves on [S Stage 4(a)]'s random `v`); a generator is the first standard basis vector not in
  `m_S V`.
* (b) `CommutantCertificate` — **v1.2 rework** ([XA B2]). v1.1 built the structured system on the
  RCF of the residue witness `w` and let `verify()` check only the listed elements. Both were wrong:
  for `f = 1` the code's witness is the trivial `w = t_{p_min}` (`HeckeModuleDecomposition.cpp:687-693`),
  which is often semisimple, hence scalar on the block, so `End_{F_ell[w]}(V)` has `D²` unknowns —
  the naive system, in exactly the large-`D` regime R7 claimed to solve; and a truncated list passed.
  The route is now three deterministic steps, and each outcome is recorded:
  1. **When (b) is needed at all — the socle bound** (derived for this revision). Let
     `t := dim_F(V/m_S V)` (= `min_generators`), `s := dim_F soc V`, both in units of `f`. Every
     `F_ell`-linear `V → V/m_S V → soc V ↪ V` whose middle map is `K`-linear is `A_S`-linear (both
     ends are `A_S/m_S`-modules), so `End_{A_S}(V) ⊇ Hom_K(top V, soc V)`, of `F_ell`-dimension
     `f·t·s`; and `A_S ∩ Hom_K(top, soc) ⊆ {a : a·m_S V = 0} = soc A_S` (`V` is faithful). Hence
     `dim C ≥ dim A_S + f·t·s − dim_F soc A_S`, and **`dim C = dim A_S` requires
     `f·t·s ≤ dim_F soc A_S`**. For cyclic `V` (`t = 1`, `V ≅ A_S`) this is an equality and (a)
     already certifies. For non-cyclic `V` (`t ≥ 2`) it forces `dim_F soc A_S ≥ 2f`, i.e. `A_S`
     **not Gorenstein** (so embdim `≥ 2`). Consequences: (b) is never attempted on a field, on any
     `F[ε]/ε²`, on any Gorenstein `A_S` — in particular never at `(10, 691)` (`t = s = 2`, `f = 1`,
     `dim soc A_S = 1`: the bound gives `dim C ≥ 2 + 4 − 1 = 5`, the exact value of [XA B1]) nor at
     any Kummer block — and it can succeed without (a) only on co-cyclic-like modules over
     non-Gorenstein `A_S`, e.g. `V = A_S^∨` for `A_S = F[x, y]/(x, y)²` (`t = 2, s = 1`,
     `dim soc A_S = 2`, `End_{A_S}(A_S^∨) = A_S`), which `HeckeExtAlgebraValidation` pins. Outcome
     `excluded_by_socle_bound` is a **proof that (b) fails**, with the four numbers recorded.
  2. **The structured system on a fixed cyclic-most element.** Candidates, in this fixed order: the
     RREF basis elements `b_1, …, b_{dim A_S}` of `A_S`, then the prefix sums `b_1 + b_2`,
     `b_1 + b_2 + b_3`, …; take the first candidate `a` whose minimal polynomial on `V` (Krylov over
     the standard basis, deterministic) has maximal degree. The choice affects the cost, never the
     verdict. Since (a) failed, no candidate is cyclic on `V`, so `a` has `m ≥ 2` invariant factors
     `g_1 | … | g_m`. RCF of `a` on `V` via the `PrimaryRCFBasis` machinery
     (`HeckeModuleDecomposition.cpp:224-317`, a local block is primary for `a`); the explicit basis of
     `End_{F_ell[a]}(V)` has `u = Σ_{i,i'} deg gcd(g_i, g_{i'}) ≤ m·D` elements; solve
     `X t_p = t_p X` for the `t_p ∈ S` inside it (`k·D²` equations, `u` unknowns).
     **Honest cost:** `O(k·u·D³)` to form the system plus `O(k·D²·u²)` to reduce it; `u` can reach
     `D²` when `m ≈ D`. Attempted only if `k·D²·u² ≤ kCommutantBudget = 2·10^10` modmul (a named
     constant; for `k = 5`: `u ≤ 371` at `D = 170`, `u ≤ 988` at `D = 64`, the naive `u = D²` at `D ≤ 24`),
     otherwise `over_budget` — **never a silent naive fallback**.
  3. **`verify()`** recomputes `dim C` from stored data (§1.3): the RCF by conjugation, the
     `End_{F_ell[a]}(V)` basis rebuilt by formula, the system re-formed and its rank recomputed.
  The **naive** commutant (kernel of `X ↦ (X t_p − t_p X)_p`, `D²` unknowns, `O(k·D⁶)`) is the
  validation oracle only, for `D ≤ 24`. Where (b) is not attempted, the ideal falls through to (c),
  which on the proof range is the certificate the dominant `m` at `n ≫ ell` will actually get
  ([E Stage 4]).
* (c) `SturmCertificate` — **two parts** ([E Cert. 5.7], [E Def. 2.8], [E Claim 2.9], [E Claim 2.10]):
  1. **The bound `B'(k, ell)`** (`HeckeSturmBound`, independent of the pipeline): `q`-expansions of
     `E_4, E_6, Δ` **mod `ell`** (the coefficients `240σ_3(m)`, `−504σ_5(m)` and the `Δ` product
     reduced as they are formed — the `F_ell`-algebra of [E Def. 2.8] is a statement about
     `M_k(Z) ⊗ F_ell`, so no bignum is ever needed; `Z[E_4, E_6, Δ]_k` has the monomials
     `E_4^a E_6^b Δ^j` with leading term `q^j` as a `Z`-basis, and their RREF mod `ell` is the
     reduction of the Miller basis), the matrix of `T_q` on `M_k(F_ell)` from
     `a_m(T_q f) = a_{qm}(f) + q^{k−1} a_{m/q}(f)` read off in the echelon basis (precision
     `q·dim M_k`, grown lazily as `q` increases), and the algebra closure of `{T_q : q ≤ B prime}`
     (`SubspaceOps::algebra_closure` on `dim M_k`-sized matrices) for `B = 2, 3, 5, …` until the
     dimension reaches `dim M_k` (⇒ `B' = B`) or the cap `B_max` (default `12·B(k)`, campaign key
     `sturm = cap=<B>`, [Q15]) is passed (⇒ `B' = none`, certificate (c) **unavailable** for this
     `(k, ell)`). Recorded as a `SturmBoundCertificate` in the record's `sturm` field (`B_prime`,
     `cap`, `closure_dim`, `dim_M_k`). Pinned values ([E Claim 2.9] proof, [E §8.3]): `B' = 2` at
     `(12, 691)` and `(34, 131)`; `B' = 5` at `(24, 5), (30, 5), (32, 5), (36, 5)`; `B' = 7` at
     `(28, 7)`; at `(24, 5)` and `(28, 7)` the algebra of `{T_2, T_3}` has dimension `2 < 3`.
     Recomputed for v1.2 by an independent script (Miller-type basis `E_4^a E_6^b Δ^j` mod `ell`,
     `T_q` from `a_{qm} + q^{k−1}a_{m/q}`, `F_ell`-closure): all of the above reproduce, and
     **`B' = 2` on all ten Kummer cells** of [E Claim 1.8] — `(k, ell) = (12, 691), (16, 3617),
     (18, 43867), (20, 283), (20, 617), (22, 131), (22, 593), (24, 103), (24, 2294797),
     (26, 657931)` — and at `(162, 691)`, `(200, 691)` (the `(160, 691)` / `(198, 691)` rows);
     `B' = 5` at `(60, 5)` (the `(58, 5)` row), `B' = 3` at `(36, 7)`; and, measured by the shipped
     `HeckeExt/HeckeSturmBound` (v1.5.1, WP-3), **`B'(258, 691) = 2`** in 1.4 ms — the `k ≤ 258`
     anchor of §6.2 E1 acceptance (d), recorded, not pinned.
     `B'` exists iff `ell ∤ [T^sat : T_Z(M_k)]` ([E Claim 2.9]); a `none` outcome is therefore a
     *finding about `(k, ell)`*, reported in `analysis.txt` by the campaign.
  2. **The sweep.** Prime list ([XA B3]): on the **proof range** (non-Dickson `m` of `X_4`) exactly
     the primes `q ≤ B'(k, ell)` — `ell` among them iff `ell ≤ B'` — because [E Claim 2.10] writes
     every `T_q`, `q = ell` included, as `F_q(T_{q' ≤ B'}) + ell·t'` with `t'` acting as `0` there, so
     `T_ell` needs no membership test; on the **heuristic range** additionally `ell` (if within the
     `U_ell` budget) and `S_sep(ell)` once the atlas exists (E6). v1.1 added `ell` unconditionally,
     scheduling `1.3·10^8`-coset `U_ell` runs it never needed. Where `ell ≤ B'` (the measured cases:
     `(24, 5)`, `(28, 7)`, `(58, 5)`), `ell` is small and the budget admits `U_ell`; were it ever
     refused there, (c) is `unavailable` with reason `u_ell_over_budget`. **Reuse before streaming**
     ([XA m12]): a listed `q` already in `S_0` takes its `A^{(q)}(T_q)` from the family's cache (in
     practice `B' ∈ {2, 3, 5, 7}` on every cell computed, so the sweep usually streams nothing). A
     `q ∉ S_0` is streamed: build `HeckeCosetTables(q, 1, ell, n)` →
     `HeckeTauTable` (under `tau_construction_mutex()`, `Hecke/HeckeOperatorFamily.h:100`) →
     `HeckeOperatorOnK::compute()` on the **already computed** cohomology **in a local scope under
     `ScopedThetaEqCertification(false)` + `ScopedMemoryLean(true)`** (`Hecke/HeckeOperatorOnK.h:376,
     407`), restrict `A^{(q)}(T_q)` to every surviving `H_m` by the exact solve, test membership in
     `A_S` (one solve against the RREF coordinate basis), and discard the pipeline. The streamed
     primes deliberately do **not** go through `HeckeOperatorFamily`, whose `pipeline_cache_`
     (`:271`) never evicts — several extra pipelines at `n = 1000` (up to `≈ 1.4 GB` each, CLAUDE.md
     `hecke 1000 --lean`) would not fit. On the range of
     [E Claim 2.10] (non-Dickson `m` of `X_4`, `B'` existing) membership of every `T_q`, `q ≤ B'`,
     **proves** `A_S = T_m` — and, since `A_S` is local, that the `T_{S_0}`-block `V` is a single
     `T_∞`-maximal ideal; on Dickson-type `m` and on `X_2, X_3, X_5, X_6` it is a heuristic and
     recorded as such. **The sweep must never use `B(k) = ⌊k/12⌋ + 1`**: at `(22, 5)` and `(26, 7)`
     the primes `≤ B(k) = 3` generate a proper subalgebra of `T_Z(M_k) ⊗ F_ell` on the pipeline's own
     `H^1` and the naive certificate would have accepted a false record ([E Claim 2.7(b)],
     [E §8.3]; pinned in §5). `B(k)` survives only as the seed of the default cap.

**Heuristic-sweep mode (OQ15, DECIDED-CONFIGURABLE; v1.5).** Two settings of §1.5 change what
(c) does *outside* its proof range, and only there. Under `sturm.unavailable = heuristic` a `none`
outcome (cap hit, or `B'` non-existent by [E Claim 2.9]) no longer leaves the ideal to (a)/(b)
alone: the sweep runs over the primes `≤ cap` **and** `ell` (within the `U_ell` budget), plus
`S_sep(ell)` once E6 exists, tests membership of every `T_q|_V` in `A_S`, and — if every one lies in
`A_S` — the ideal is emitted **`final = "heuristic"`** with `sturm.mode = heuristic`, `sturm_primes`
the list actually swept and `B_prime = null`; a single non-member is a *finding* (the algebra is not
`T_m`; the ideal is `final = false`, reason `sturm_unavailable`, and `analysis.txt` names the prime).
Under `final_mode = sturm_heuristic` the same mode applies to the **heuristic range** of
[E Cert. 5.7] — Dickson-type `m` of `X_4`, and every `m` of `X_2, X_3, X_5, X_6` — where the sweep
of the primes `≤ B'` (existing) `∪ S_sep(ell) ∪ {ell}` is a heuristic with a large margin and
[E Claim 2.10] proves nothing: `final = "heuristic"` instead of `false`. The **defaults are
`nonfinal` and `closure`** (slot-1 confirmation 6, DECIDED), under which neither mode runs and (c)
behaves exactly as v1.4 wrote it; the heuristic sweep is never run by the golden harness. What a
`"heuristic"` record claims is stated in the record itself: "every listed operator lies in `A_S`",
nothing more. A `none_at_cap` state is resumable (§1.3.1 R3.3 item 1) in either mode.

**Stage 5 — module structure** ([E Alg. 5.8]): `HeckeModuleStructure::Compute(V, A_S, m_S)` per group
and `m`: Loewy series `m^{j+1} V = Σ_a n_a (m^j V)` (spans + RREF); socle series `soc V = ∩_a ker n_a`
(one stacked kernel), `soc^{j+1} V` = preimage of `soc(V / soc^j V)` (quotient via
`complement`-style bases, then preimage); **Jordan type of each `n_p` on `V` in units of `f`**
([E D3], [E Claim 6.1]): the nullity sequence of `n_p^s` over `F_ell` (`= ker π_p(t_p)^s`, since
`π_p(t_p) = n_p · u` with `u` a unit of `A_S`) divided by `f`, fed to `PartitionFromNullities`
(reused), and cross-checked against the S10 partition of `t_p` w.r.t. `π_p` with every multiplicity
divided by `f/deg π_p` — the two coincide only when `deg π_p = f`, which is exactly the case the
S10 report already covers; structure maps `θ_j: m_S/m_S² → Hom_F(top_j, bottom_j)` as the
`F_ell`-matrix of `n ↦ (b̄ ↦ n b)` in the chosen layer bases, **stored per generator** (rows:
bottom-layer basis, columns: top-layer basis, [E §7]), `rank / f` by [E Claim 5.9]; the active
subset of `S_m` over `K`; `cyclic ⇔ dim V/m_S V = f`, `free ⇔ cyclic ∧ dim V = dim A_S`,
`min_generators = dim(V/m_S V)/f`. Canonical positions (D6): `dim(W ∩ m^j V)` by intersection **and
the image of `W` in each layer** (`dim` of `(W ∩ m^jV + m^{j+1}V)/m^{j+1}V`, one preimage per layer;
the `sum_of_layers` / `skew` verdicts are read off these, [E Alg. 5.8(4)], [XA M7]) for every
available `W ⊆ V` in its own ambient group (E2: `L·H^1(M_{n−ell−1}) ⊆ X_4` via a second
`(n−ell−1, ell)` run and the `DicksonMultiplication` map as a one-entry `FiberBlockTable`; E3: the
**Eisenstein line `soc(X⁺_{4,m})`** when its `F`-dimension is `1` (`"undefined"` otherwise, and
`"unavailable"` before E3 — the unsplit socle at `(10, 691)` is 2-dimensional and contains both
reductions, [E D6]); E4: `H^1_! ⊆ X_4`, `r^0 X_1 ⊆ X_2`; E5: `ker/im` of (3.1)). `X_1` is not a
subspace of `X_4`: its own Loewy series is reported, and its position is `r^0 X_1 ⊆ X_2` ([XA m11]).

**On-request presentation (OQ11, DECIDED; v1.5).** No full `T_m`-module isomorphism via a canonical
form is computed (the deliverable stays (D1)–(D7)); **generators and relations of `X_{i,m}` over
`T_m` are computed only when asked** — the verb `presentation(m, group)` (§7), the campaign key
`presentation = on` (§1.5), the record key `presentation` absent by default. Algorithm
(`HeckeExt/HeckePresentation`, E2, deterministic, `MatrixT`-sized): a **minimal generating set** is
a lift `v_1, …, v_t` of a basis of `V / m_S V` (`t = min_generators`, the first standard basis
vectors not in `m_S V`, Nakayama); the **relation module** is `ker(A_S^t → V)`,
`(a_1, …, a_t) ↦ Σ a_i v_i`, computed as the `F_ell`-kernel of a `D × (t · dim A_S)` matrix (columns
`b_j v_i` over the RREF basis `b_j` of `A_S`) and then reduced to a **minimal `A_S`-generating set of
relations** by Nakayama again (`ker / m_S · ker`, via `m_S`'s action on `A_S^t`); the output is the
pair (generators as columns of `V`, relations as `t`-tuples of elements of `A_S` in the `b_j`
coordinates) and the two dimensions. Certificate: every relation evaluates to `0` on the
generators, the generators span `V` over `A_S` (their `A_S`-span has dimension `D`), and the
relation count equals `dim_F(ker / m_S ker)` — re-derived by `verify()`. **(v1.10, slot-6 WP-2
finding 1)**: that is an `F`-dimension; the number of minimal relations is
`dim_F(ker / m_S ker) / f`, counted over the residue field `K`, and equals the `F`-dimension only
at `f = 1` (WP-2's `f = 2` arm: one relation, `F`-dimension 2). **(WP-2 finding 2)**: the
least-index lift is taken in the **block's own basis** (`PrimaryBlock::basis_columns`), so
generator indices are block-basis indices, not stored-`H^q` indices; the slot-7 record key must
say so or carry the generators as `H^q`-columns. Pinned by
`HeckePresentationValidation` (§5): at `(10, 691)` `H^1_+ ≅ T_m` is free of rank one (one
generator, **no** relation) and the unsplit `H^1_m` has `t = 2` with the relation module recorded
(`(e_31, 0)`-type, one minimal relation over `A_S = F[ε]/ε²`); the constructed algebras of
`HeckeExtAlgebraValidation` give known presentations (`A_S^∨` for `A_S = F[x, y]/(x, y)²`: two
generators, relations `x·g_1 = y·g_2`, `y·g_1 = 0`, `x·g_2 = 0` up to the stored basis).

**Stage 6 — atlas** (E6): `HeckeAtlas`: run E0–E2 for all even `n ≤ ell − 1` (weight `ell + 1`
**included** — `Δ mod 11` is a cuspidal weight-12 system that is neither Eisenstein-congruent nor
a twist of a lower weight, [E Stage 6]; feasible for `ell ≤ ~1000`: `346` runs at `ell = 691`
(even `n ≤ 690`), each ≈ 4 s per operator at the top of the range (`hecke 256` 0.56 s scaled by the
measured exponent 2.05) and ≤ 0.7 GB **with the anemic family only**; [XA M4]/[XA B3]: with
`U_691` in `S_0` the same scaling gives ≈ 1 min and ≈ 19 GB per run at `n ≈ 690`, so the atlas
applies the `U_ell` budget like every other consumer — `U_691` is computed for `n ≤ 110` (v1.7; v1.6: `n ≤ 220`) and
omitted above, where the system's `a_ell` is stored as `unknown` with reason `u_ell_over_budget`
(the θ-twist closure on the anemic coordinates does not need it; the `a_ell`-dependent labels of
[Q6] are then `unknown`, never guessed). Collect `(π_w, {P_p})` per ideal with `a_ell` where
computed, close under `θ`-twist `a_q ↦ q^j a_q` (on the polynomial data: `P_p ↦ p^j P_p mod π_w`),
greedy `S_sep(ell)`, persistent store as JSON under `docs/matrix-engine/results/atlas/`.
**Per-`ρ̄` generating pair** ([E Stage 6], [XA M7]): for each cuspidal `ρ̄ ∈ Σ(ell)` of weight `w`,
`dim m/m²` and a generating pair of anemic operators are computed in the multiplicity-≥2 weight
`n = w − 2 + ell² − 1` **only where that `n` is within the model's reach `n ≤ 1000`**, i.e.
`ell² + ell ≲ 1000`, `ell ≤ 31` — computed for the E6 campaign's `ell ∈ {5, 7, 11, 13}` — and
**deferred** (recorded `"tangent_pair": "deferred: n = … > 1000"`) otherwise, `ell = 691` included;
the stored pair is a default `S_m`, never a certificate (Stage 4 still certifies).
`HeckePredictions`: `bernoulli_mod`, Kummer/Ribet condition, `χ_a ≡ χ_{a'}` coincidences
(`a ≡ a'` or `a ≡ n + 1 − a' mod ell − 1`, [E Claim 1.7]), Dickson counts, `θ^{ell−1}`/`V`
doublings, Harder's `r^1 = 0`; predictions are **annotations** (`predicted / confirmed /
unpredicted`) unless `predictions = assert` (§1.5, OQ14: the debug switch that promotes every
annotation to an assertion, used by the validations of §5 on the named cases and never by a
campaign). `HeckeCanonicalField`: `C_{ell,r}` by enumeration in `CanonicalLess`
order + `CertifyIrreducible` ([E Def. 6.2]) — the **degree-lexicographically least** irreducible,
OQ9 DECIDED; `field_polynomial = conway` is reserved (parsed, rejected, the record names the
convention in force) and Conway tables are a follow-up tied to that key (§6.5); root finding of
`π_w` in `F_ell[Y]/(C)` with the *fixed* candidate sequence of [E Alg. 6.4] — the only new
arithmetic (univariate polynomials over `F_ell[Y]/(C)`, `≈ 200` lines on top of `FpPolyT`),
confined to the report. **The canonical split field is the default report form** (OQ10 DECIDED,
`split_field_report = canonical`; the own-field form `F_ell[X]/(π_w)` + `P_p` is the secondary form
behind `own_field` and is always emitted as `coefficient_field`, so nothing is lost either way) —
**conditional on a performance gate, which E6's acceptance runs as §6.2 E6 (d)**: `--bench ext`
at the atlas cells `ell ∈ {5, 7, 11, 13}` (every even `n ≤ ell − 1`) and at `(10, 691)`,
`(160, 691)`, `(198, 691)`, splitting out `canonical_field_s=`; the gate is
**`canonical_field_s ≤ 0.10 × total_s` on every cell**, with the protocol, the numerator and the
denominator as §6.2 E6 (d) pins them, and `own_field_s` reported beside it rather than bounded.
(v1.10: the pre-v1.10 wording also required `canonical_field_s ≤ 2 × own_field_s`, against
`ext_s`; slot-5 WP-7 measured both halves on all 23 cells and neither was met, the second not
meetable by any admissible implementation — `[WP5-7]` §4, `[WP5-13]` §5.2, `[E]` v1.6.2's version
block. The owner restated the gate on 2026-09-22 at the recommendation of
`docs/implementation/e6_gate_brief.md`, [OD] E6-1 / E6-2.) If it holds, the default stands; if it
fails, the default flips to `own_field` for the first ext campaign, the measurement goes to the
owner, and the `F_{ell^r}` element type of §6.5 is the reopening question (§0.3) — the owner's own
expectation is that an optimised field representation is *faster*, which the gate measures rather
than assumes.

**Stage 7 — scaling in `n`** (E6): a `--campaign` spec per residue class mod `ell − 1` and a
comparison tool `docs/matrix-engine/tools/ext_compare.py` that aligns records `m` by `m` across
`n, n + ell − 1, n + ell + 1` by character; a regression test, not a validation.

### 2.3 Sizes, and why `MatrixT` is acceptable for the decomposition layer

Measured ([I §3.3, §4.2]): `d_1 = dim H^1 = 47` at `n = 256`, `≈ 170` at `n = 1000`
(Eichler–Shimura, `≈ n/6`); a local block `D ≤ d_1`, and the dominant ideals at small `ell` are
already `D = 22` (`n = 128, ell = 5`, `T_5`); after the `ι` split every `D` halves. Algebra-closure
vectors have length `D² ≤ 2.9·10^4`; `dim A_S ≤ D` in practice (`≤ D²/4 + 1` by Schur). Berkowitz
is `O(D⁴)`: `8·10^8` modmul at `D = 170`, seconds on naive `Matrix` loops; the whole level-(c) layer
was `21.7 ms` at `d = 43` (`n = 256, ell = 134217757`, [I §3.4]) and is `< 4 %` of the wall. The
ext layer multiplies that by the number of operators (`5`) and stages (`≈ 4` charpolys per block per
operator, plus the `ŵ` powers and `k` nilpotency checks, `O(D³ log D)` each): still `≪` the
pipeline's `0.56 s` at `n = 256`, and of the order of the pipeline's `14 s` at `n = 1000`. The
Sturm bound is `dim M_k`-sized (`≤ 84` at `n = 1000`) and its `q`-expansion products are
`O(L²)` at precision `L = q · dim M_k` — `≈ 5·10^5` at `q = 7`, trivial; only a `none` outcome at the
default cap costs more: at `n = 1000` the cap is `12·B(k) = 1008`, `L ≈ 8.5·10^4`, i.e.
`≈ 7·10^9` modmul per series product and ≈ 84 basis forms — **minutes**, not seconds ([XA m12];
v1.1 said seconds). That is why the precision grows lazily with `q`, and why a `none` outcome is
worth its cost only once per `(k, ell)`: the campaign computes `SturmBound` once per cell and reuses
it across signs and groups. The `U_ell` coset budget (§2.2 Stage 1) is the other size bound the ext
layer adds. The locality certificate runs on **every** decomposition, including the single-operator
ones of the campaign, the golden harness and `--bench decomp`; there `ŵ` would cost `N·⌈log₂ ell⌉`
`D×D` products (27 squarings at `ell = 134217757`, of the order of a whole `hecke 256` at `D = 47`),
so the `k = 1` certificate is **analytic** (§3.1, [XA m17]) and E0b carries a performance gate. **Decision: `MatrixT<uint32_t>` for everything in `HeckeExt/` except the cone**; E1's
acceptance measures the ratio (§6) and the fallback — swapping the products inside
`CharPolyBerkowitz` / `EvalPolyAtMatrix` for `FlatMatrix` kernels, bit-identical by construction —
is listed in the risk table, not scheduled. The cone (E5) is *engine*-sized (`dim C^1_eq ≈ 5·10³` at
`n = 1000`, `D^0` a `≈ 5000²` `FlatMatrix`, RREF `≈ 1.3·10^11` modmul, seconds on `engine::elim`) and
uses `FlatMatrix` + `engine::elim` with the D5b basis rules, never `MatrixT`.

### 2.4 The `SubspaceOps` contract

All bases are **canonical functions of the input** (no hash containers, no thread dependence):
column spaces are the pivot columns of the input's RREF, kernels are the D5b kernel basis
(`Matrix::kernel`, `Matrix.cpp:434`), sums are `column_space(hstack)`, intersections are read off
`ker [A | −B]`, quotient complements take the first non-pivot standard vectors, preimages are
exact solves. This is what makes every ext object hashable at tier B and the console verbs of
[PA A9] (`solve, hstack/vstack, submatrix, column_space, intersect, sum_spaces, restrict, vec/unvec,
commutant, nullity, random_vector(seed)`) a 1:1 image of this header (§7).

---

## 3. The locality bug fix (Phase E0)

### 3.1 The defect and the fix

`ComputeMultiOp` stops refining when every operator has a single irreducible factor on the block
(`HeckeModuleDecomposition.cpp:574-611`: `any_split_this_pass` is set only when `FactorPoly` returns
`> 1` factor, `:590-591`), and then certifies the residue degree by a witness whose charpoly's
squarefree part is *one* irreducible of degree `f = lcm deg π_p` (`:680-723`; the trivial
single-operator witness is accepted first, `:687-693`). The header's claim that one pass "already
reaches the MaxSpec(T) fixed point" (`.h:40-45`) holds only when all residue degrees are `1`:
[E Claim 3.1] / [I §2.3.4] exhibit `t_1 = (α, α^ell)`, `t_2 = (α, α)` on `F_{ell²}²` — each with
minimal polynomial the same irreducible `π` — where the block passes `certify()`
(`:792-953` re-checks only per-operator primality and the lcm) yet `T_S/rad ≅ F_{ell²} × F_{ell²}`.
A single-irreducible witness does **not** certify locality either (`w = t_1` has charpoly `π²`,
and `t_2 = (α, α)` has irreducible squarefree minimal polynomial of degree `f = 2`); what does is
[E Cert. 5.2], **both clauses**: `π_w` irreducible of degree `f` **and** every `t_p − P_p(ŵ)`
nilpotent, with `ŵ` the Teichmüller lift ([E Claim 3.3]).

**Fix (in `HeckeModuleDecomposition` itself — [Q5] default (a)), in two commits** ([XA M2]):
**E0a** adds the certificate as a free function `CertifyLocality(block, ops, ell)` next to the class
(declared in `HeckeModuleDecomposition.h`, nothing calls it from `compute()`), so it can be run
*read-only* over every existing decomposition while the tree is still value-identical; **E0b** calls
it inside the refinement loop. After the fixed point, per block:

1. run the existing witness search (`:694-723`, same seed `0x510C0FFEE5EED042`, `:31`) but require
   the full certificate: `π_w := sfd[0]`; `N :=` the least multiple of `f` with `ell^N ≥ D`;
   `ŵ := w^{ell^N}`; `P_p` by the `U = ker π_p(t_p) ∩ ker π_w(w)` solve of §2.2 Stage 3.2;
   `n_p := t_p − P_p(ŵ)` nilpotent (`n_p^D = 0` by `⌈log₂ D⌉` squarings, `O(D³ log D)`) for every
   `p`, the trivial single-operator witness included (`n_j = t_j − ŵ`, not `0`);
2. if a candidate `w_c` has `≥ 2` distinct irreducible factors, **split** the block by the primary
   decomposition of `w_c` (the existing single-operator machinery, `:386-518`, applied to `w_c|_V`),
   inserting the sub-blocks **at the parent's position, in `CanonicalLess` order of `w_c`'s
   irreducible factors** (deterministic; it is the order the existing loop already uses for its own
   splits, `:592-606`), and go back to the refinement loop — every split strictly reduces dimensions,
   so this terminates;
   an inconsistent `P_p` system or a non-nilpotent `n_p` is the same signal (the block is not local)
   and triggers the next witness;
3. if the budget (`kResidueWitnessMaxAttempts = 64`, `:32` — **already the spec's default**,
   [E Alg. 5.1(2)], [Q16]; **v1.6, as shipped by WP-1: the budget caps the candidate sequence of
   §1.3.1 R3.3 item 2, trivial witnesses included** — one sequence, one attempt index, so that
   `run(64) + resume(128) == run(128)` is a prefix property; on every golden block the first
   candidate certifies, so no value moved) is exhausted with no certificate and no split, the block is emitted with
   `local_certified = false` (schema `"local": false`), `residue_degree_lower_bound`, and the
   `NOTE` at `:724-732` names locality as well — never silently, and **the loop never spins**.
   That is the **budget mode** `locality = budget=<N>`, the **default** with `N = 64` (OQ16, slot-1
   confirmation 7, DECIDED); the outcome is encoded in `local` and the loop state is resumable
   (§1.3.1 R3.3 item 2).

**Strict mode (`locality = strict`, OQ16 DECIDED-CONFIGURABLE; v1.5).** Strict mode continues until
locality is certified everywhere — so it **must terminate**, and it cannot rely on the linear
witnesses `w = Σ c_p t_p`, which [E Cert. 5.2] guarantees only when `f` has at most `ell` distinct
prime factors and, for separation, when `min(f, f') ≤ ell` (automatic at `ell ≥ 5` for the
existence half since `f ≤ D ≤ ~200 < 30030`; **not** automatic for separation at small `ell`, and
not at all at `ell ∈ {2, 3}`). The terminating route, run **only after the budget-mode loop has
exhausted its `N` linear witnesses on a block** — so that wherever budget mode certifies, strict mode
is **byte-identical** to it and the golden reference is the same in both modes — is linear algebra
with no search:
1. **Compute `A_S` and its radical.** `A_S` by `SubspaceOps::algebra_closure` on the `t_p|_V` (Stage
   3.1; `dim A_S ≤ D²/4 + 1`). On a commutative `F_ell`-algebra the Frobenius `x ↦ x^ell` is
   **`F_ell`-linear** (`(x + y)^ell = x^ell + y^ell`, `(cx)^ell = c x^ell` for `c ∈ F_ell`), so
   `rad A_S = {x : x nilpotent} = ker(Frob^N)` with `ell^N ≥ D` — a kernel of an explicit
   `dim A_S × dim A_S` matrix (`SubspaceOps::frobenius_kernel`: `N` successive Frobenius matrices,
   each column `b_i ↦ b_i^ell` by square-and-multiply on `D × D` matrices, `O(dim A_S · D³ · log ell)`
   per Frobenius, `N ≤ ⌈log_ell D⌉`). The trace form is **not** usable here (it vanishes identically
   on `F_ell[x]/(x^ell)`, a local algebra of dimension `ell`), which is why the radical is computed
   through Frobenius.
2. **The Berlekamp subalgebra decides and splits.** `Ā := A_S / rad A_S` is commutative semisimple,
   `Ā ≅ ∏_{i=1}^{m} F_{ell^{f_i}}` with `m` = the number of maximal ideals of `A_S` on `V`; the
   Frobenius-fixed subalgebra `B := ker(Frob_Ā − id) = ∏ F_ell = F_ell^m` has **`dim_{F_ell} B = m`**
   (Berlekamp). So `V` is local iff `dim B = 1`. If `dim B ≥ 2`, take the **first non-scalar RREF
   basis element `b̄` of `B`** (a fixed choice), lift it to any `w ∈ A_S` with residue `b̄`: `b̄` has
   `≥ 2` distinct coordinates in `F_ell^m`, so the semisimple part of `w` has `≥ 2` distinct
   eigenvalues in `F_ell`, `minpoly_V(w) = ∏ (X − λ_i)^{e_i}` with `≥ 2` distinct `λ_i`, and the
   **primary decomposition of `w` on `V`** (the existing single-operator machinery of `:386-518`,
   applied as in step 2 above, sub-blocks inserted at the parent's position in `CanonicalLess`
   order of the `λ_i`) splits `V` into `≥ 2` **non-zero** blocks — non-zero because `V` is faithful
   over `A_S`, so no primitive idempotent of `Ā` lifts to an element acting as `0`. Recurse on each
   sub-block. **Termination**: every split strictly reduces dimension. **No witness is searched** at
   this stage.
3. **A residue witness for the certificate, over the whole residue field.** With `dim B = 1`, `Ā` is a
   field, `f := dim_{F_ell} Ā`, and [E Cert. 5.2] needs a `w ∈ A_S` whose residue generates `Ā`
   (`π_w` irreducible of degree `f`), then the `P_p` solve and the nilpotency checks — which **are
   guaranteed to succeed** since `V` is local ([E Claim 3.3]). The linear family failed because the
   `F_ell`-span of the `t̄_p` can lie in a union of proper subfields; the residues of **all of `A_S`**
   cannot: `Ā = F_{ell^f}` is never the union of its proper subfields
   (`Σ_{r | f prime} ell^{f/r} ≤ ω(f) · ell^{f/2} < ell^f` for every `f ≥ 2`, `ell ≥ 2`). So the
   witness is drawn from `Ā` itself — its coordinate vectors in the RREF basis of `Ā`, lifted to
   `A_S` by the same coordinates — by the **fixed-seed sequence** (`kResidueWitnessSeed`, mixed with
   `(f, ell)`), each candidate tested by `deg minpoly_Ā(w̄) = f` (a `f × f` Krylov computation, not a
   `D × D` one); a candidate fails with probability `≤ ω(f) · ell^{−f/2}`, so the expected number of
   trials is `≈ 1`. The **terminating guarantee** is the deterministic fallback after `N` seeded
   trials: enumerate the coordinate vectors of `Ā` in lexicographic order — finite (`ell^f`
   elements), guaranteed to contain a generator, and in practice never entered. The witness found
   is then used exactly as in step 1 of the budget loop (`π_w`, `N`, `ŵ`, `P_p`, `n_p`), and the
   certificate is the same `LocalityCertificate` (§1.3) — strict mode changes *how the witness is
   found*, never what is certified.
4. **What strict mode records.** `level_c.locality = {mode: strict, budget: N (the linear phase's),
   phase_reached ∈ {linear, berlekamp, residue_search}}` per block, `local = true` on every block
   (the only way to a `local = false` under strict mode is an **interruption**, §1.3.1 R3.3 item 5,
   at a step boundary — between witnesses or between splits — which leaves a resumable
   `LocalityState`), and the `resumable` object. Strict mode is **never the default** and is never
   run by the golden harness, `--bench decomp` or the campaign unless the spec says `locality =
   strict`; the golden `decomp_*` hashes therefore pin the budget mode, and `HeckeLocalityValidation`
   asserts (§3.2) that strict mode reproduces them bit for bit on the whole grid — the branch of
   steps 1–3 is entered on no golden cell if WP-1's grid arm is clean.
5. **Cost.** Step 1 is `O(dim A_S · D³ · N log ell)` with `dim A_S ≤ D²/4 + 1`, i.e. at most
   `O(D⁵ log D · log ell)` per block — `≈ 10^{11}` modmul at `D = 170`, `ell = 691`, **minutes on
   `MatrixT`** in the worst case (R19); it is entered only after 64 failed linear witnesses, which on
   every computed cell has never happened, and the `Frob` matrices are formed once per block and
   reused across the recursion's sub-blocks by restriction.
6. **Separation.** Two blocks that the budget loop could not separate (residue degrees `f, f'` both
   `> ell`, non-conjugate characters) are one block with `dim B = 2` in step 2 and are split there;
   the cross-group evaluation test of §2.2 Stage 2 is unchanged. **This is the specification
   [OD §OQ16] asks for in [E Alg. 5.1(2)] / [E Cert. 5.2]** — the spec revision of slot 2 ([SP §5])
   transcribes it: "strict mode: Berlekamp-subalgebra refinement on `A_S / rad A_S`, then a residue
   witness over `Ā`; terminates because every split reduces `dim V` and `F_{ell^f}` is not a union of
   proper subfields".

For `k = 1` nothing changes and **nothing is computed** ([XA m17]): a single operator with charpoly
`π^m` generates `F_ell[t]/(π^e)`, which is local, so `ŵ` is the semisimple part of `t`,
`P = X mod π_w` (v1.5.1, WP-1: the *reduced* representative of degree `< f` — the constant `α` at
`f = 1`, `X` itself only when `deg π ≥ 2` — so that the analytic and the matrix path agree at
`f = 1`; `HeckeLocalityValidation`'s twin arm pins it), `n = t − ŵ`, and the certificate holds
analytically — E0b sets `local_certified = true`, `witness_poly = π`, `w_hat_exponent = N`
(arithmetic only), `character = {p ↦ X mod π_w}` and never forms
`ŵ` (which would cost `N·⌈log₂ ell⌉` `D×D` products on every single-operator decomposition of the
campaign, the golden harness and `--bench decomp`). `certify()`'s code for `k = 1` re-checks the
same arithmetic, not a matrix power. The S10 semantics (`:468-469`) are untouched (`n ≠ 0` when
`e ≥ 2` is the *correct* Jordan datum, not a change of verdict). Splitting order and the basis of
unsplit blocks are unchanged, so tier-B `_U` hashes move only where a split happens. **Performance
gate (E0b acceptance):** `--bench hecke 256 134217757 2 --repeat 5` (min) and `--bench decomp 128
134217757 2 --repeat 5` within 5 % of the E0a binary on a quiet box.

New `PrimaryBlock` fields (`.h:129-150`): `bool local_certified`, `FpPoly witness_poly` (`π_w`),
`uint32_t w_hat_exponent` (`N`), `std::map<uint64_t, FpPoly> character` (`P_p`, `deg < f`) — **not**
added to `GoldenHarness.cpp`'s `CollectDecomposition` nor to `CampaignDriver.cpp`'s
`CollectDecompositionInvariants` (§1.6). `certify()` gains codes 25–29 (`π_w` irreducible of degree
`f`; `f | N` and `ell^N ≥ dim`; `π_w(ŵ) = 0`; `deg P_p < f`; `n_p` nilpotent for every `p`;
`local_certified` consistent with the witness). **Change sites of the text** ([XA M1]; v1.1
attributed the golden-visible keys to the wrong writer):
* **`Hecke/HeckeReport.cpp`** — the golden-visible one. `BuildHeckeReportJson` writes the schema
  (`:109`, `hecke_report/v1 → v2`) and the `level_c.blocks` keys **itself** (`:189-230`); it gains
  `"local"`, `"witness_poly"`, `"coefficient_field": {"w_hat_exponent", "P"}` (the key names of
  [E §7]) and the G1 text fix of the `multiplicity_note` at `:200-214` (which calls a non-semisimple
  block "a genuinely irreducible T-module of this multiplicity, NOT further separable …", both
  false, [I §2.3]): the new note states multiplicity, semisimplicity (all partitions `(1,…,1)`?)
  and whether the family is a single operator. The golden `report_*^q` texts come from here
  (`GoldenHarness.cpp:601-604`).
* **`Hecke/HeckeModuleDecomposition.cpp`** — `to_json()` (`:1004`ff., hashed nowhere) emits the same
  three keys and bumps **its own** schema `hecke_module_decomposition/v1 → v2` (`:1008`); the
  **second copy** of the false wording in `to_string_offset` (`:980-983`: "genuinely irreducible as
  a T-module, NOT further separable by more Hecke operators") gets the same corrected note; the
  `HeckeModuleDecomposition.h:40-45` and `:72-80` comments are rewritten accordingly.
* **`Campaign/CampaignDriver.cpp:666-667`** — the `level_a` omission text ([I G1]); campaign-only,
  not golden-visible.

### 3.2 Validation

`HeckeLocalityValidation` (**fast**, `≈ 0.3 s`): constructed truths in the style of
`HeckeDecompositionSmokeValidation` (fixed-seed reconstruction). Over `ell ∈ {5, 13, 691}`,
`f ∈ {2, 3}`, multiplicities `{1, 2}`, with and without nilpotent parts: build
`t_1 = C_π ⊕ C_{π}^{Frob}`-type pairs and `t_2 = C_π ⊕ C_π` (companion blocks conjugated by a seeded
random invertible `U`) — the [E Claim 3.1] shape — plus genuinely local blocks (`F_{ell^f}[ε]/ε²`,
`F_{ell^f}[x,y]/(x,y)²`), **plus the [E Claim 3.3] trap**: `A_S = F_{ell^f}[ε]/(ε²)` presented by
the *single* operator `t = α + ε` (so the trivial witness `w = t` is accepted, `min_V(w) = π²`):
assert `ŵ = α` (i.e. `π_w(ŵ) = 0`, `ŵ ≠ w`), `P_t = X`, `n_t = t − ŵ = ε ≠ 0`, Jordan `(2)` over
`F`, and — as the negative control — that the v1.0 recipe `t − P_t(w)` returns `0`. Assert,
entrywise: the fixed code splits the non-local families into the right number of blocks with
`local_certified = true` and the right `(π_w, N, P_p)`; the local ones are not split;
`certify() == 0`; a frozen copy of the *pre-fix* acceptance predicate (kept inside the validation,
like `BarCocycleSolverValidation`'s frozen solver body) accepts the non-local block — so the
validation proves the defect existed and is gone; the bounded loop: a constructed block on which
every linear witness fails (`f` with more than `ell` distinct prime factors is out of reach, so
the budget is forced to `1` through a test-only hook) ends with `local_certified = false`, the
`NOTE` printed, and no spin. Plus the grid regression of §3.3.

**Strict-mode arms (E0b, v1.5; OQ16).** (i) **The covering example `(ell, f) = (2, 30)`**, a local
block on which *every* linear witness lies in a proper subfield: `V = F_{2^{30}}` as a 30-dimensional
`F_2`-space, `t_1 = ` multiplication by `a`, `t_2 = ` multiplication by `b`, where `a ∈ F_{2^{15}}`,
`b = a + c ∈ F_{2^{10}}`, `c ∈ F_{2^{6}}` — such a triple exists: choose `0 ≠ x ∈ F_8` with
`Tr_{F_8/F_2}(x) = 0`, solve `a^{2^{10}} − a = x` in `F_{2^{15}}` (a coset of `F_{2^5}`; pick `a ∉ F_8`)
and `c − c^{2^4} = x` in `F_{2^6}` (pick `c ∉ F_8`); then `b^{2^{10}} = b`, `F_2(a) = F_{2^{15}}`,
`F_2(c) = F_{2^6}`, so `F_2(a, b) = F_{2^{30}}` and `A_S = F_{2^{30}}` is a field (`f = 30 = 2·3·5`,
three prime factors `> ell = 2`), while the three non-zero linear witnesses `a, b, a + b = c` have
residue degrees `15, 10, 6`. Assert: budget mode (`N = 64`) emits the block `local = false` with
`residue_degree_lower_bound = 30` (the lcm) — the *correct* budget-mode verdict, pinned so that a
later "fix" cannot silently change it — and strict mode certifies it `local = true`, `f = 30`,
`phase_reached = residue_search`, `dim B = 1`, with a `π_w` of degree 30 and every `n_p` nilpotent;
the `k = 2` `P_p` solve is consistent. (ii) **The split path**: on every non-local family of the
[E Claim 3.1] arms (where `dim B = 2` in step 2), strict mode reaches the same final partition as
the fixed budget loop does through its witnesses, entrywise, and `phase_reached = berlekamp` on the
block that the budget loop split by a witness with `≥ 2` factors is asserted only when the linear
family was *forced* to fail by the test hook (budget `1`). (iii) **Grid identity**: strict mode over
every golden-grid decomposition (the arm of §3.3, re-run with `locality = strict`) gives the same
four hashes and `phase_reached = linear` everywhere — strict and budget mode are byte-identical
wherever the budget mode certifies. (iv) **Interruption**: a cancellation raised by the test hook
between two witnesses leaves a `LocalityState` from which `resume(strict)` completes with the same
partition and certificate as an uninterrupted run (resume-invariance, §1.3.1 R3.1 item 3).

### 3.3 The re-baseline story, proved

`CollectDecomposition` (`GoldenHarness.cpp:488-510`) emits **four** objects per decomposition, for
every single-operator `decomp_A(T_p)^q` **and** for the one multi-operator object
`decomp_sim{2,3,5}^1` (`:620`, on every cell with `dim H^1 > 0`, `ell ∈ {2, 3}` and `n = 1`
included): `_invariants` (tier A: dims, `residue_degree`, charpolys, minpolys, partitions),
`_certify` (tier A: the scalar `certify()` code), `_witness` (tier B: `residue_degree_certified` and
the witness combination) and `_U` (tier B: the change of basis). v1.1's proof covered only
`_invariants` ([XA M2]).

**Claim.** If every block of every decomposition on the grid is local, none of the four moves.
*Proof.* `k = 1` blocks are local and untouched (§3.1). For `k ≥ 2`: on a local block the old
refinement's accepted witness `w` has `π_w` irreducible of degree `f`, so `w̄` generates the residue
field, `ŵ = w^{ell^N}` is its Teichmüller lift, and every `t_p − P_p(ŵ)` is nilpotent ([E Claim 3.3]):
the new certificate accepts **the same first witness**, so the loop takes no new branch — no split
(`_invariants`, `_U` unchanged), the same `residue_witness` and `residue_degree_certified`
(`_witness` unchanged), and codes 25–29 do not fire (`_certify` unchanged, still `0`). The new fields
are not hashed (§1.6). Conversely a non-local block changes at least `_invariants` (it splits) or
`_certify`/`_witness` (it is emitted `local = false`). ∎

**E0a decides which case holds, before the reference is touched:** its grid arm (in
`HeckeLocalityValidation`) recomputes every decomposition the harness builds — the grid is
`kGridNSym × kGridEll ∪ kExtraCells` (`GoldenHarness.cpp:165-168`; `GoldenSubset32` takes its cells
as a parameter and has no list of its own, [XA m3]), `p ∈ kGridP` for `decomp_A(T_p)^q` and
`{T_2, T_3, T_5}` for `decomp_sim` — runs the read-only `CertifyLocality` on every block, and
**asserts all four hashes** against `GoldenReference.inc` together with `local == true` on every
block. If it passes, nothing but the report texts of §1.6 moves and E0b's re-baseline is exactly the
allow-listed text; if it fails on a cell, that cell's split is a **finding** reported to the owner
before E0b starts, and E0b's `golden_explain.py` run must name it in `--accept-split`. No other
evidence is claimed: the published 2745-row campaign table decomposes **one operator per job**
(`CampaignDriver.cpp:637`, `ops = {{job.p, A1[q]}}`), and single-operator blocks are always local,
so it says nothing about multi-operator locality ([XA m1]; v1.1 cited it as evidence). The
re-baseline then follows §1.6; `GOLDEN_STRICT=1 GoldenRegressionValidation` returns `0` afterwards in
every arm of CLAUDE.md's acceptance table.

Alternative if the owner prefers not to move any tier-A hash: keep `hecke_report/v1` byte-identical,
emit the corrected note and the new keys only in `hecke_ext/v1`. Recommendation: **re-baseline** —
a report that calls a `(2,1)` block "genuinely irreducible" should not stay frozen as the reference.

### 3.4 E0a and E0b: what lands where

**E0a — value-preserving** (golden unchanged, `GOLDEN_STRICT=1` tier A/B mismatching 0; no emitted
text changes anywhere): `GoldenDump` + `golden_explain.py` (§1.6); the read-only
`CertifyLocality` free function and `HeckeLocalityValidation`'s constructed-truth arms that do not
need the fix (the trap arm, the frozen pre-fix predicate) plus the four-hash grid arm (§3.3); G2
(`HeckeIdentityChecks` → the `IdentityCertificate` of §1.3, incl. explicit commutation) and
`HeckeIdentityValidation`; G9 as `DicksonInvariantCount` (§2.1: the three boolean copies become
`count > 0`, the golden `dickson` entry unchanged); `SolveColumnsExact`, `HStack`,
`PrimaryRCFBasis` and the new `algebra_closure` in `Hecke/SubspaceOps.h` (WP-1 / WP-3);
**`ModArithmetic/ModArithmetic/Fnv.h`** (sole owner, WP-2; console C1 consumes it) unifying the
byte-wise FNV-1a-64 of `Golden/GoldenHarness.cpp:220-233`, `Campaign/CampaignDriver.cpp:151-160` and
the `Fnv` class of `ModArithmetic/ModArithmetic/PerformanceSmokeValidation.cpp:90-106` ([PA E9]; the
word-wise `BlockPool.h` hash and `Program.h`'s `fnv_mix` stay), proved identical by
`CampaignSmokeValidation` and `GoldenRegressionValidation` remaining green; the **`U_ell` RSS measurement** (`(16, 43867)`,
`(128, 691)`, `(256, 131)`, one `--bench hecke` each) that fixes the two frozen constants of §2.2
Stage 1 before any `HeckeExtKummerValidation` arm is written ([XA M4]); and **the `(160, 691)`
probe** ([Q17]): one **pre-fix** `ComputeMultiOp` run on `{T_2, T_3, T_5}` at `(160, 691)` with
`CertifyLocality` on every block (seconds), whose verdict — `T_5`'s `4:1` block is two
`F_691`-rational systems merged at `a_5` (then the existing per-operator refinement already splits
it, `T_2`/`T_3` having `2:1` blocks) or is `T_2`'s `4:2` block with an `F_691`-rational `a_5` (then it
does not split, and must certify local) — is written into §9 and becomes the asserted outcome of
`HeckeExtSeparationValidation` (§5).

**E0b — the fix and the re-baseline**: the refinement loop of §3.1 calling `CertifyLocality`, the
`k = 1` analytic path, `PrimaryBlock` fields, `certify()` codes 25–29, **the `locality` setting with
its strict mode and `LocalityState`** (§1.3.1, §1.5, §3.1 — `Hecke/HeckeSettings.h` lands here),
the text changes at the three change sites of §3.1, **the oc1a record fields** `q_max` /
`truncated` / `q_max_source` in `HeckeReport.{h,cpp}` and `CampaignDriver.cpp` (batched, §1.6), the
remaining `HeckeLocalityValidation` arms (splits, bounded exit, strict mode), the re-baseline of §1.6
with its two-part `golden_explain.py` check, the performance gate, and the stale-schema note on the
published campaign records. **Slot 2**, after WP-7 has recorded the E0a-binary performance
reference and the grid verdict ([SP] WP-7 items 3–4).

---

## 4. Determinism and certification policy

1. **No new randomised search in production.** The ext layer's only pseudo-random sequences are the
   ones that exist: the residue-witness candidates (`kResidueWitnessSeed = 0x510C0FFEE5EED042`,
   `HeckeModuleDecomposition.cpp:31`, mixed with `(dim, ell)` at `:695`, bounded by
   `kResidueWitnessMaxAttempts = 64`, `:32`), the RCF functionals (`kRcfSeed = 0x510B10CBA5150001`,
   `:26`) and Cantor–Zassenhaus (`0x510C0FFEE5EED123`, `FpPoly.h:177`). The `P_p` are found by a
   deterministic solve (no candidate vectors), cyclicity is Nakayama (deterministic), the commutant
   is a linear system, the Sturm bound is an enumeration, the Sturm test is a solve, the canonical
   field is enumerated, the root of `π_w` uses a fixed candidate list. Validations may use seeded
   RNG for constructed truths; every seed is a named constant and the record stores the witness
   combination `c` and the exponent `N` it used.
2. **Fixed orders everywhere.** Operators by ascending prime (`std::map`, as `PrimaryBlock`'s maps);
   factors by `CanonicalLess`; ideals by `(CanonicalLess(π_w), lexicographic on (P_p)_p)`; layers by
   index; the minimal active subset greedy in ascending `p`; no `unordered_*` on any result path
   ([ME §2 D4 audit item 6.5(5)]).
3. **Every result carries a certificate** (§1.3) whose `verify()` reads only emitted data, and the
   record's `certificates_ran` lists them; `final` is a defined predicate (§1.3), never a mood.
4. **Bit-identity across engine settings is inherited, then asserted.** The ext layer is
   single-threaded and consumes `A^{(q)}(T_p)`, which is identical across `ENGINE_THREADS`,
   `ENGINE_BATCH`, `ENGINE_DEVICE` and `ENGINE_BACKEND=legacy` (CLAUDE.md "Validation suite status";
   `EngineDeterminismValidation`); `HeckeExtDeterminismValidation` (§5) hashes the whole record under
   those arms in one process through `ScopedConsumerPool` / `ScopedPassOptions`
   (`ModArithmetic/Engine/EngineRuntime.h:69-92`).
5. **"Certified record of all extension classes for `(n, ell)`" in code** is a `HeckeExtRecord` whose
   `ExhaustivenessCertificate` verifies on every available group (`Σ_m dim X_{i,m} = dim X_i`), whose
   every ideal has `LocalityCertificate`, `ModuleCertificate` and a `GenerationCertificate` verifying
   with `0`, whose `IdentityCertificate` reports `failed = 0`, and whose `final` flags are the
   tri-state of §1.3.1 R3.2 — the four unavailable groups counted as `unavailable`, never as passed;
   a `none` Sturm bound, a non-local block and an ideal that cannot reach closure are *published and
   flagged*, with their resumable state, never hidden (OQ8, OQ15, OQ16 as DECIDED with the slot-1
   confirmations 6–8); `"heuristic"` appears only under a user-selected mode and says exactly what
   was swept.
6. **Predictions are annotations, identities are gates** (OQ14 DECIDED): a refuted prediction sets
   `confirmed = false` and is printed; a failed identity is a validation failure; the selected cases
   of §5 are asserted **inside validations** through `predictions = assert`, never in a campaign.
7. **A setting is part of what a value means** ([OD] R1): every record carries the mathematical
   settings in force (§1.5), the golden reference pins the defaults, and a non-default setting
   changes every hash input and the job id. There is no path by which a setting changes a value
   silently — which is the same discipline the engine's `ENGINE_*` switches obey in the other
   direction (they may change *nothing*).

---

## 5. Validations to add

All registered in `ValidationRegistry.cpp` (explicit table, `ValidationRegistry.h:43-57`),
`uint32_t Name()` returning `0`, exact equality only, every basis compared **entrywise** (plan D5b).

| Name | Tier | Phase | Pins / oracles |
|---|---|---|---|
| `HeckeLocalityValidation` | **standard**, ≈ 8.1 s as shipped (v1.7: 1500 checks, the strict-mode arm 7 shipped by slot-3 WP-3; v1.6: 1356 checks; the grid arm recomputes the harness's decompositions and `certify()` codes 27/29 form `ŵ` on the 79 multi-operator blocks) | E0a (trap, frozen pre-fix predicate, read-only grid arm) / E0b (splits, bounded exit) | §3.2: constructed non-local families split and certified; local ones untouched; the `ŵ`-vs-`w` trap of [E Claim 3.3]; the frozen pre-fix predicate accepts the defect; the bounded loop exits; `k = 1` analytic path equals the matrix computation on constructed blocks; **the grid arm of §3.3: `CertifyLocality` on every golden-grid decomposition (`decomp_A(T_p)^q` and `decomp_sim{2,3,5}^1`, `ell ∈ {2, 3}` and `n = 1` included) and all four hashes `_invariants`, `_certify`, `_witness`, `_U` equal to `GoldenReference.inc`** through the harness's `GoldenLookup`, never a copied constant; the `(160, 691)` probe as its own `slow`-tier name `HeckeLocalityProbe` or env-gated (`HECKE_LOCALITY_PROBE=1`), recorded, never asserted ([SPA] Q7); **since v1.5 (E0b): the four strict-mode arms of §3.2** — the `(2, 30)` covering example (budget mode `local = false`, strict mode `local = true`, `f = 30`), the split path, grid identity under `locality = strict`, and interruption + `resume(strict)` — plus the resume-invariance arm `run(budget = 8) + resume(64) == run(64)` entrywise on the constructed families. **Status v1.6**: the budget-mode arms — splits at the default budget, the bounded exit at a forced budget of one candidate (the frozen pre-fix predicate still accepts, the certificate still rejects), the `k = 1` analytic path against the matrix path and against what `compute()` stored, the `HeckeSettings` arm (defaults, parsing, fingerprint, the named strict-mode error, propagation onto `run_concurrently()` tasks), `run(1) + resume(64) == run(64)` modulo `budget_history`, and the grid arm with `loop_disagreements = 0` — **shipped with slot-2 WP-1**; the four strict-mode arms are **WP-6's (slot 3)**. **Status v1.7**: all four **shipped** (slot-3 WP-3, arm 7): the `(2, 30)` example from a certified degree-30 irreducible (0.10 s), the Berlekamp split path on 9 cells (the same partition in 9/9, the same *order* in 6/9 — the order is per-mode, a finding for [E]), grid identity under `strict` (`LOCALITY_GRID_STRICT … nonlinear_phase=0 hashes=944 failing=0`), interrupt + `resume_locality()`; plus the fingerprint, the lexicographic fallback, a five-way tamper on codes 20/23/25/26/30 and a concurrent budget-vs-strict arm |
| `HeckeIdentityValidation` | fast | E0a | `IdentityCertificate` on a small grid (`n ≤ 32` **even, `n > 0`**, `ell ∈ {5, 7, 13, 691}`): Eichler–Shimura + `DicksonInvariantCount` against the tabulated `#{a(ell+1)+b(ell²−ell)=n}` **and** against the three `IsDicksonExceptional` copies (`count > 0`), `[A_p, A_{p'}] = 0`, `d_2 = 0`, the `p²` recursion, the campaign rows of [I §3.3] as fixed expectations; and `not_applicable` (never `passed`) on `n ∈ {0, 1}`, `ell ∈ {2, 3}` ([XA M3]) |
| `HeckeExtArchitectureValidation` | fast | E1 (first `HeckeExt/` TU) | `check_heckeext_includes.sh` (one-way dependency with `ValidationRegistry.cpp` allow-listed; `HeckeSturmBound.*` includes only `SubspaceOps`, `FpPolyT`, `MatrixT`, `ModArithmetic`; no `unordered_`), via `std::system` like `MatrixRetirementValidation` |
| `HeckeSturmBoundValidation` | fast, ≈ 0.5 s | E1 | `HeckeSturmBound` alone, no pipeline: the `q`-expansions mod `ell` against `σ_3`, `σ_5` and `τ(m)` (`τ(2..7) = −24, 252, −1472, 4830, −6048, −16744`) for `ell ∈ {5, 7, 131, 691, 134217757}`; `dim M_k` against the closed form; the Miller basis echelon; `T_q` on `M_12(F_691)` with eigenvalues `σ_11(q)`, `τ(q) mod 691` and `T_q ≡` scalar `+ c_q ε` (the [E Claim 8.1] algebra seen from the modular-form side); the pinned bounds `B' = 2` at `(12, 691), (34, 131)`, `5` at `(24, 5), (30, 5), (32, 5), (36, 5)`, `7` at `(28, 7)`, and closure dimension `2 < 3` for `{T_2, T_3}` at `(24, 5), (28, 7)`; `B' = 2` on all ten Kummer `(k, ell)` of [E Claim 1.8] and at `(162, 691), (200, 691)`, `B' = 5` at `(60, 5)`, `B' = 3` at `(36, 7)` (the v1.2 recomputation, §2.2 4(c)); the `none` outcome under a forced cap (`cap = 3` at `(24, 5)`) recorded, not thrown; `SturmBoundCertificate::verify() == 0`; minimality of `B'`; **v1.5 (WP-3): the resume-invariance arm** — from that `none_at_cap` state, `resume(cap = 12·B(k))` reaches `B' = 5` with a certificate and a `SturmState` **entrywise equal** to a fresh run's (§1.3.1 R3.4), `resume(cap = 2)` on it is refused with the named error, and a resume on a `found` state is a no-op; the `budget_history` lists both caps; **both `sturm.unavailable` modes** (E1b): `nonfinal` (the default) leaves a `none` ideal `final = false` with reason `sturm_unavailable`, `heuristic` sweeps the primes `≤ cap` and `ell` and emits `final = "heuristic"` with `sturm_primes` — on the forced-cap `(24, 5)` case with the real `A^{(1)}(T_q)`, where the sweep's members are all in `A_S` and the record says so; a tampered certificate (a dropped `T_q`, or `closure_dim` decremented) fails `verify()` |
| `HeckeExtAlgebraValidation` | standard, 0.10 s as shipped (v1.6: 4930 checks) | E1a (**shipped**, slot-2 WP-4 + WP-5) / E1b (the real-block arms) | constructed local algebras with known invariants conjugated by seeded `U`: `F[ε]/ε²` (embdim 1, Gorenstein), `F[x,y]/(x,y)²` (embdim 2, socle dim 2, not Gorenstein), `F[x]/(x³)` (`ν = 3`), `F_{ell²}[ε]/ε²` (`f = 2`: **embdim `1`, not `2`** — the `K`-span test; and with the single operator `t = α + ε`, `active = {t}` — the witness direction is not lost), `F_{ell²}[x,y]/(x,y)²` (`f = 2`, embdim 2), over `ell ∈ {5, 13, 691, 134217757}`; `dim A_S`, `ŵ`, `m_S`, `ν`, socle, Hilbert function, tangent table entrywise; **commutant (b)** ([XA B2]): the socle bound `dim C ≥ dim A_S + f·t·s − dim_F soc A_S` checked against the naive `dim C` on every constructed case with `D ≤ 24`; `excluded_by_socle_bound` on every Gorenstein non-cyclic case (`F[ε]/ε² ⊕ F`, the `(10, 691)` shape: `dim C = 5`, bound `5`); the positive non-cyclic case `V = A^∨`, `A = F[x,y]/(x,y)²` (`t = 2, s = 1`, `dim C = dim A = 3`, `commutant` passes where `cyclic` fails); structured `dim C` == naive `dim C` wherever both run; a `CommutantCertificate` whose stored rank is decremented, or whose RCF basis is perturbed, **fails** `verify()` (the certificate re-derives, it does not read); `over_budget` under a forced tiny budget, never a naive fallback, **and (v1.5) its `CommutantState` resumes**: `run(tiny) + resume(kCommutantBudget)` gives the same system, rank and verdict as a fresh run (§1.3.1 R3.3 item 3); cyclicity vs an explicit `A_S v` closure; Sturm membership on real `A^{(1)}(T_q)` at `(10, 691)`, `q ≤ 11` with the recorded `B' = 2`; the joint decomposition of `X_1 ⊕ X_4` equals the character-matched per-group one; the cross-block evaluation test of §2.2 Stage 2 on constructed Frobenius-conjugate (must match) and distinct same-`π_w` (must not match) pairs with `dim B ≠ dim B'` ([XA M5]). **Status v1.6 (the row split, WP-4 §7 item 4 / WP-5 §8 item 8)**: the constructed-truth arms, the `[XA B2]` negative control, the `[XA M5]` cross-block test and the ten-way tamper — **done (WP-4)**; the socle bound against the independent naive `dim C` and a closed form on all nine cases (`D ≤ 24`), `V = A^∨`, the `(10, 691)` shape `excluded_by_socle_bound`, structured == naive == closed form, the `CommutantState` arms interrupted at **every** reachable row count and resumed entrywise equal, the `final = false` emission arm, the sixteen-way tamper with the RCF positive control — **done (WP-5)**; the real-block arms — Sturm membership on `A^{(1)}(T_q)` at `(10, 691)` with `B' = 2`, the joint `X_1 ⊕ X_4` decomposition — **E1b, slot 3**, **registered (v1.7) under their own name `HeckeExtSturmSweepValidation`** (slot-3 WP-2; standard, 2.37 s, 274 checks; the joint `X_1 ⊕ X_4` arm runs at `(12, 5)`, being vacuous at `(10, 691)` where `dim H^0 = 0`; `S_sep(ell)` is not swept — it needs E6's atlas — and the certificate records the prime list it used) |
| `HeckeExtRamanujanValidation` — **this row's name as registered (v1.8)**; v1.7 listed it as a second `HeckeExtRecordValidation`, so §5 carried the name twice for two different bodies of work. The two shipped in slot 4 as **`HeckeExtRamanujanValidation`** (standard, 295 checks, 4.0 s — this row, the Claim 8.1 arm, WP-2) and **`HeckeExtRecordValidation`** (fast, 381 checks, 0.04 s — the schema row below, WP-1) | standard, 4.0 s as shipped | E2 | [E Claim 8.1] in full, the first acceptance test: at `(10, 691)` one ideal, `local = true`, `T_m ≅ F_691[ε]/ε²`, **primary (basis-independent) checks first** ([XA m19]): the **four** matrix identities `3(T_3−252) = 256(T_2+24)`, `3(T_5−4830) = 174(T_2+24)`, `3(T_7+16744) = 137(T_2+24)`, **`3(U_691−1) = −542(T_2+24)`** exactly in `M_3(F_691)` (`U_691` is within the budget: 692 cosets at `n = 10`, ≈ 81 MB predicted, 98 MB measured), the ratios `c'_q/c'_2 ≡ c_q/c_2` (`546, 58, 276`, and `221 ≡ 542·23·(−3)^{−1}`), the eigenvalues `a_q = 667, 252, 684, 531, 1`; **then the basis-dependent pins**, labelled as such — the stored matrices `T_q = a_q I + c'_q E_31` with `c'_q = 23, 120, 643, 129, 221` for `q = 2, 3, 5, 7, 691` depend on the stored `H^1` basis, a tier-B object that the golden reference already gates, so they are asserted in this tree but documented as a basis pin; `dim A_S = 2`, embdim `1`, `ν = 2`, Gorenstein, `w_hat_exponent = 1`, Jordan `(2,1)` for every `T_q − τ(q)` (`q = 691` included), Loewy `(2,1)`, socle dim `2`, not cyclic, **every** `T_q ∈ {2,3,5,7,691}` active; **generation** ([XA B1]): route (a) fails (`dim V/m_S V = 2 ≠ f = 1`), route (b) `excluded_by_socle_bound` (`t = s = 2`, `dim soc A_S = 1`) and the naive oracle confirms `dim End_{A_S}(H^1_m) = 5 ≠ dim A_S = 2`, so the record is **`certificate = "sturm(B')"`, `sturm = {B_prime: 2, cap: 24, closure_dim: 2, dim_M_k: 2}`, `sturm_primes = [2]`, `generators_certified = [2]`, `final = true`** (non-Dickson `m` of `X_4`, [E Claim 2.10]; v1.1's `certificate = commutant` was impossible); JSON round-trip through a from-scratch mini parser (the `HeckeSimultaneousValidation` pattern) with the [E §7] example values `"H1_shriek": "all"` (E4) and `"eisenstein": "bottom layer (soc)"` (E3) asserted once those phases exist |
| `HeckeExtSeparationValidation` | standard, ≈ 1 s | E2 | `(160, 691)`: `ComputeMultiOp` on `{T_2, T_3, T_5}` — the outcome the E0a probe found ([Q17], §3.4, recorded in §9) is asserted: **either** the `4:1` block of `T_5` splits into `2:1 + 2:1` (two `F_691`-rational systems, every `T_m` a field) **or** it coincides with `T_2`'s `4:2` block (`f = 2`, multiplicity 2, cyclic per sign); in both cases every block local and semisimple, and — since every block has multiplicity 2 on the unsplit `X_4` and `A_S` a field — every unsplit record `sturm(2)` (`B'(162, 691) = 2`), `cyclic` per sign from E3; `(198, 691)`: the `3:1` block non-split with Loewy `(2,1)` **recorded** (`691 ∥ num(B_200/200)` recomputed, uniqueness of the congruent eigenform still open, [Q13]); the `20:10` block one Galois orbit of residue degree `10` with multiplicity `2` |
| `HeckeExtSmallEllValidation` | standard, ≈ 3 s | E2 | Dickson loci `(6,5), (8,7), (12,11)`: `dim H^0 = 1`, `H^0` carries `χ_1` (`T_2 ↦ 2+2^6 ≡ 1`, `T_3 ↦ 2`, `T_5 ↦ 0` at `(6,5)`, [I §3.3]); `(12, 5)`: the character **multiset** of `H^0` recorded and asserted as values (`χ_3 ≡ χ_2` as functions mod 5, exponents mod 4, so an index label is not distinguishable, [XA §5.3]); `(34, 5)`: `T_2` and `T_5` semisimple on `H^1` ([I Stage 9]) and the `Δ` ideal's split/non-split verdict **recorded** (expected split, [E §8.3]); `(58, 5)`: `T_5` Jordan block of size `2` at `Δ`'s ideal **recorded**, with `B'(60, 5) = 5 = ell` — the one measured case where the proof sweep contains `U_ell` (6 cosets, within budget); **the Sturm counterexamples** ([E Claim 2.7(b)], [E §8.3]): at `(22, 5)` and `(26, 7)`, `dim H^1 = 5`, the `F_ell`-algebra generated by `A^{(1)}(T_2), A^{(1)}(T_3)` has dimension `2`, the one generated by all `A^{(1)}(T_q)`, `q ≤ 13`, has dimension `3 = dim M_k`, `B' = 5` resp. `7`, and a `SturmCertificate` built with the prime list `{2, 3}` **fails** `verify()` (its list does not cover `B'`) while the list of primes `≤ B'` passes — the naive `B(k) = 3` sweep would have certified falsely; `(32, 131)`: `B' = 2` and the algebra generated by `A^{(1)}(T_2)` alone **recorded** (expected everything) |
| `HeckeExtKummerValidation` | slow, ≈ 40 s | E2 | **all ten** cells of [E Claim 1.8] with `n < ell − 1`, `k ≤ 26`: `(n, ell) = (10, 691), (14, 3617), (16, 43867), (18, 283), (18, 617), (20, 131), (20, 593), (22, 103), (22, 2294797), (24, 657931)` (v1.1 omitted `(24, 657931)`, the `k = 26` case, without comment, [XA m6]; `(10, 691)` is also `HeckeExtRamanujanValidation`): exactly one non-split Eisenstein–cuspidal ideal on `X_4` with Loewy `(2,1)`; all others semisimple; **generation** ([XA B1]): `B' = 2` on every cell (§2.2 4(c)), the non-split block `excluded_by_socle_bound` for (b) and not cyclic, so it is **final only via `sturm(2)`**, as is every multiplicity-2 cuspidal block on the unsplit `X_4`; after E3, `cyclic` on `H^1_+` and `H^1_−`. **`U_ell` by the frozen budget** (§2.2 Stage 1, [XA B3]/[XA M4]): included at `ell ∈ {691, 3617, 283, 617, 131, 593, 103}` (≤ 0.45 GB), **omitted** at `(16, 43867)` (≈ 5.6 GB predicted — the arm is fixed only after E0a's measurement), `(22, 2294797)` and `(24, 657931)`, recorded `u_ell_over_budget`; none of the omitted cells needs it (`ell > B' = 2`) |
| `HeckeExtRecordValidation` — **shipped** (slot-4 WP-1): fast, **381 checks**, 0.04 s | fast | E2 | schema `hecke_ext/v1` keys of [E §7] v1.1 (`commit`, `model`, `iota_sign`, `convention_check`, per-ideal `sturm` **exactly** `{B_prime, cap, closure_dim, dim_M_k}` plus its `mode` and `resumable`, with the swept list under `sturm_primes` ([XA m13]), `certificate_routes`, `u_ell`, `local`, `witness_poly`, `coefficient_field`, `structure_maps[].matrices`, the stored `t_p\|_V`), `null`/`unavailable`, **the tri-state `final`** (§1.3.1 R3.2): the truth table of `is_final()` over `final_mode × sturm.unavailable × {proof range, heuristic range, none}` with every reason of the fixed list (`not_local`, `sturm_unavailable`, `sturm_heuristic`, `closure_unreachable`, `certificate_failed:<code>`, `budget_exhausted:<kind>`, `interrupted`) reached by a constructed record, `"heuristic"` never produced under the defaults, and an ideal that cannot reach closure **present** in the record (never withheld) and listed by the `analysis.txt` writer; **the `settings` block** with every key of §1.5, its `source`, the fingerprint `0` at the defaults and non-zero otherwise, and the fingerprint's presence in every hash input; **the `resumable` objects** of §1.3.1 R3.1 (inline below 64 KiB, sidecar + FNV above, `resumable_items` count); **`q_max = 2`, `truncated = false`, `q_max_source = "derived"`, `degrees = [0,1,2]`** on the 7-vertex model and a spec setting `q_max` there rejected as a spec error; `coefficient_ring = "F_ell"`; **every certificate re-verified from the parsed JSON alone** ([XA m15]), hashes per kind equal to `ModArithmetic/ModArithmetic/Fnv.h` |
| `HeckeExtDeterminismValidation` | standard, ≈ 12 s | E2 | record digest identical under `ENGINE_THREADS ∈ {1, 4, 16, 32}` × `ENGINE_BATCH ∈ {0, 1}` on `(10, 691), (34, 5), (24, 7)`, plus `device = gpu` at threads `{1, 16}` on the same three cells (it **runs** on the reference RTX 5070 Ti and prints `[SKIP]` only without a device, [XA m8]), plus `(128, 5)` on the `cpu` arms at threads `{1, 16}` only (v1.1's ≈ 3 s for 8 arms × `(128, 5)` with five operators was optimistic) |
| `HeckeExtCampaignValidation` | standard, ≈ 2 s | E2 | a spec with `ext = true` at four `jobs × threads` splits: same jobs, same order, the ext record attached once per `(n, ell)` cell to its first job ([XA m14]), same ext objects (`sturm_bound` included) and `summary.tsv` columns; `u_ell` verdicts identical across splits; ext hashes of golden-grid ext-subgrid cells equal `GoldenReference.inc` |
| `HeckeInvolutionValidation` — **shipped** (slot-4 WP-3): standard, **2954 checks**, 2.2 s, the production `Hecke/HeckeInvolution` + `HeckeExt/HeckeSignSplit` accepted **entrywise** against `HeckeIotaSignValidation`'s independent construction (exported value-preservingly as `hecke::iota_oracle`) | standard, 2.2 s as shipped | E3 | `ι² = I`, `[ι, A_p] = 0`; `dim H^1_± = dim M_k / dim S_k` for `ell ≥ 5` off the Dickson locus (recorded); Eisenstein class in `H^1_+` ([Q3]; **gating** since [C] v1.2.0, where `ι^* := −ι^*_geo` makes it true by definition — the production `ι^*` must agree entrywise with the validation-built one of the shipped `HeckeIotaSignValidation`, whose `IOTA_SIGN eisenstein=plus (geometric=minus)` line is the reference) and `iota_sign` in the record; `(10, 691)`: `H^1_+ ≅ T_m` free of rank one, `H^1_- ≅ F_691`, `certificate = cyclic` on both signs, the Eisenstein line `soc(H^1_+) = m H^1_+` **defined** (dimension `1` over `F`) and in the bottom Loewy layer; the unsplit `H^1_m` socle 2-dimensional ⇒ `"undefined"` there |
| `HeckeBoundaryValidation` — **registered as three names (v1.6)**: `HeckeBoundaryTauValidation` (slot-1 WP-4a, (i)–(iv)), `HeckeBoundaryOperatorValidation` (slot-1 WP-4b, (v)–(vii)), `HeckeBoundaryParabolicValidation` (slot-2 WP-7, E4b: `H^1_!`, Harder, the diagnostics — ≈ 4.7 s, 4966 checks on 75 cells) | standard | **E4a** (registered by WP-4a with the certification and tampered-chain arms; extended by WP-4b with the route, character, negative-control, equivariance and model-recording arms — [SP] WP-4a/4b) / E4b (diagnostics, Harder, `H^1_!`) | **certification** `obl:taubdry`(i)–(iv) over `Z` for `p ∈ {2, 3, 5, 7}` and `p^ν ∈ {4, 9}`, a tampered `τ_∂` chain failing; **model recording** (slot-1 confirmation 11, DECIDED: compute for every `ell`, never refuse): at `ell = 2` the object reports `boundary_model = circle`, `boundary_is_group_cohomology = false` and `dim H^q` equal to `dim V^T` / `dim (V)_T` of [C] `prop:circlemodel`(2) — never the `lem:ell2unbounded` values — and at `ell ∈ {5, 13}` the flag is `true`; `r^q`-equivariance **asserted** at `ell ≥ 5` and **recorded** at `ell ∈ {2, 3}`; then: `dim X_2 = dim X_5 = ⌊n/ell⌋ + 1`; route A (the `τ_∞` Shapiro transcription with the left-coset `δ_i`) == route B (the explicit `M^T`/`M_T` formulas of C-A2 (iii)) entrywise; `r^q A_p = A_p^∂ r^q`; **the boundary characters asserted at once** ([E Claim 1.7]): the monomials `x^{n−bℓ}N^b` are `T_p^∂`-eigenvectors of `M^T` with `χ_b`, `M_T` carries the same multiset, `[y^n] ↦ 1 + p^{n+1}`, both `χ_0` for `n < ell`, on the eleven cells `(4,5), (6,5), (8,5), (10,5), (12,5), (14,5), (8,7), (10,7), (16,7), (6,11), (12,11)` with `p ∈ {2, 3}` ([EA §3.1]; e.g. `(6,5,2)`: `{4, 1}`, `(16,7,3)`: `{6, 0, 1}`); **negative control**: the operator built from the right-coset `β_j` gives `{χ_{b+1}}` (`(6,5,2)`: `{1, 1}`) and breaks `r^1`-equivariance with `1 + p^{n+1}`; Harder: `r^1 = 0` on the Eisenstein class **asserted** iff `ell \| num(B_k/k)` on the Kummer list (all `n < ell − 1`, the hypothesis of [E Claim 1.8]); at `(10, 5)` and `(10, 7)` — outside that hypothesis — the rank of `r^1` on the Eisenstein class is **recorded**, not asserted ([XA m5]) — **as shipped (v1.6, WP-7)**: "the Eisenstein class" at a Kummer cell is read as the **joint `1 + p^{n+1}` eigenspace `E` of `{T_2, T_3}`**, which is **2-dimensional** on all ten Kummer cells (the integral Eisenstein and cuspidal eigenlines reduce into the same socle; [E] v1.4.0 D6 / `cl:harder`) and a line on every off-Dickson non-Kummer cell; `r^1 = 0` on all of `E` asserted there, verdict `consistent` on all 37 applicable cells, an `inconclusive` state for `0 < rank(r^1 E) < dim E` reachable in principle and never observed; and **`H^1_! ≠ H^1` at every Kummer cell** (`dim H^1_! = dim H^1 − 1 = 2 dim S_k`, the class restricting non-trivially being the top of the non-split block, not its socle) — [E] `sec:tests`' "`H^1_! = H^1`" was refuted and corrected in [E] v1.4.0; `TauBoundaryCertificate` on the **`Γ`-level `τ_∂`** over `Z` (C-A3(ii.2), §1.3), and the **Shapiro transcription equality**: the `τ_∞` / `(δ_∞, δ_j)` operator of route A equals the `τ_∂` operator entrywise on every cell; **the entrywise cochain identity `r^•∘Θ_g = Θ_g^∂∘r^•` (`p ∈ {2, 3, 5, 7}`) and the cusp-support walk of the bulk `τ` are run and recorded as the diagnostics `cochain_commutes` / `eta_zero` and gate nothing whatsoever** — they are *not* a decision procedure for `h = 0` ([V §2.7], PROVED; C-A3(ii.5)(d): `h = 0` is admissible iff `τj = jτ_∂` exactly, and the shipped `τ` fails that, `tau_table_p2.txt:13-15,35`); `solve_regime` recorded for `τ_∂` |
| `HeckeConeValidation` — **split (v1.6)**: the `η`-table's arms are registered as **`HeckePairHomotopyValidation`** (slot-2 WP-8, E5-1; standard, 0.32 s, 113 596 checks on 152 tables: `PairHomotopyCertificate` = `obl:eta`(i)–(iv) re-derived independently, 27 tampered chains rejected, `lem:etaunique` on two vertex-chain policies, `eta_zero` agreeing slot by slot with the WP-7 walk and false everywhere); the cone's arms below will be a **second registered name** (slot 3), not an extension of this one. **(v1.7) As registered in slot 3, two names**: **`HeckeConeValidation`** (slot-3 WP-5, E5-2; standard, 1.9 s, 5350 checks on 74 cells — the complex arms: `ConeCertificate`, `Dcone² = 0`, exactness at every spot, `im π^1 = ker r^1`, `H^0_c = 0`, `eq:conedims`, the per-complex degree fields, the truncated branch on a declared truncation, a three-way tamper) and **`HeckeConeActionValidation`** (slot-3 WP-6, E5-3; standard, 11.9 s, 123 634 checks on 63 cells / 212 operators — `ConeActionCertificate`, `ConeRelationsCertificate`, both `(viii)` arms). Not yet: the two cross-routes (slot 6), the PD prediction (E7). A single-entry tamper of `h` fails `obl:eta`(v) **and** the cochain-map clause; only the `ξ` of `prop:coneambiguity` fails **exactly** (v), so "a tamper arm on the stored `h` failing exactly (v)" is carried by the `ξ` arm (WP-6 finding 5) | standard, ≈ 6 s (v1.7: 1.9 s + 11.9 s) | E5 | **The certificate arms** (§1.3, [V §4]): `PairHomotopyCertificate::verify() == 0` over `Z` — `∂η(x) = (jτ_∂ − τj)(x)` on every vertex slot, `∂η(e) + η(∂e) = (jτ_∂ − τj)(e)` on every edge slot, both sides only through the shared (T1) helper — and `ConeActionCertificate::verify() == 0` over `R` (`h_flat` **is** the coset transport of the stored `η`-table; `dh + hd = Θ_g^∂ r − rΘ_g` as matrices — **v1.7: on the stored `C^q_eq` basis; flat, recorded (29 of 424 degrees), WP-6 finding 1, for the next [C] `X`** —; `DΦ_g = Φ_g D`; `Φ_g` maps the stored cocycle basis into `Z^•(C(r))` and projects to `A_c^{(q)}`), and `ConeCertificate::verify() == 0` (`D² = 0`; exactness of (3.1) with the bookkeeping of Claim 1.5; `im(X_3 → X_4) = ker r^1`; every map intertwines). **The independence arm**: two different `η` (two path policies for `η_0`) and two different `τ_∂` give **bit-identical** `A_c^{(q)}` and bit-identical tier-A objects, while `h_flat`, `Θ^∂_flat` and the three table hashes move — the cone bases `Z^q(C(r))`, `B^q(C(r))`, `H^q(C(r))` and `D` are independent of the triple (`D` involves only `d` and `r`) and must come out **bit-identical** too, so they are asserted equal, not asserted to move — the computational face of C-A3(ii.5)(b)/(c) ([V §2.5], [V §2.6.1]). **The tampered-`h` negative control** ([V §4], the arm that proves the cochain identity is not a certificate): `h' := h + k` with `k` a random degree-`−1` chain map built as in [V §2.2] (split `A^i = B^i(A) ⊕ H̃^i ⊕ W^i`, put `k = λ` on `H̃^1` and `0` elsewhere) **passes** `dh' + h'd = Θ_g^∂ r − rΘ_g`, `DΦ' = Φ'D` and the whole `ConeCertificate`, **changes** `A_c^{(1)}` at `(10, 691)`, and **fails** `ConeActionCertificate` — `h'` is not the coset transport of the stored `η`. Plus: the diagnostics `eta_zero`, `cochain_commutes`, `solve_regime[3]` recorded and asserted consistent (`eta_zero ⇒ cochain_commutes`); the assertions of §1.3 (`[A_c(T_p), A_c(T_q)] = 0`, the `T_{p^2}` recursion on `X_3, X_6`, `H^0_c = 0` and `dim H^2(K) = 0` on `6 ∈ R^×`, `n` even); at `(10, 691)`, `dim X_3 = 3` (v1.7: measured, `rank r^1 = 1`; v1.6 had `4`) and `X_3` glues the boundary class ([V §2.2], [E §8.1]); **both cross-routes of C-A3(iii)(6), which are committed work** (owner decision OP3, 2026-09-15, §11): the strict-pair `τ^s` arm (a `TauVertexPolicy::BoundaryStrict` table, certified in its own right, [V Prop. 2.6.2]) **and** the relative-complex route 3 arm (`Θ' := Θ + dE + Ed`, `E := ext_0 ∘ h`, run through `EquivariantCohomologyOnK` on `ker r`, [V §2.10]) must each give the **same `A_c^{(q)}`** as the normative cone — two independent computational confirmations of the independence theorem, on top of the two-`η`/two-`τ_∂` arm, which is why the owner took both rather than one; and the PD prediction (**socle** layers of `X_3` ↔ Loewy layers of `H^1(D_n)` reversed, [E Pred. 4.6]) **recorded** until E7, then **asserted as the acceptance gate for `X_3` at `ell ≥ 5`** |
| `HeckePresentationValidation` | fast | E2 | the on-request presentation of §2.2 Stage 5 (OQ11): `(10, 691)` `H^1_+ ≅ T_m` free (one generator, no relation), the unsplit `H^1_m` with `t = 2` and its one minimal relation recorded; the constructed algebras of `HeckeExtAlgebraValidation` (`A^∨` over `F[x, y]/(x, y)²`, cyclic `F[x]/(x³)`) against their known presentations up to the stored basis; `verify()` re-derives the span and the relation count; the `presentation` key **absent** under the default `presentation = off` and the record hash unchanged by turning it on (the presentation is not a hash input — it is a derived object of the stored bases). **v1.10: shipped by slot-6 WP-2, `fast`, 995 checks, without the key — the key arm is booked for slot 7's re-baseline, stage 1; the record texts are asserted byte-identical with the driver option on and off** |
| `HeckeDualityValidation` | standard, ≈ 3 s | **E7** (OQ4) | **coefficient level, asserted** ([C] `prop:pairing`, `lem:symdual`): `ρ_n^∨(g) = ρ_n(adj g)^T` is a monoid homomorphism on seeded `g`, the Gram matrix of `⟨·,·⟩` is `I` over every `ell` of the Phase-0 boundary set, `⟨ρ_n(g) v, φ⟩ = ⟨v, ρ_n^∨(adj g) φ⟩` (no determinant factor), `Φ_n` intertwines `ρ_n` and `ρ_n^∨` and is an isomorphism iff `n < ell`; **cohomology level** at `ell ≥ 5`, `n` even, on the E2 case list and the eleven boundary cells: the pairings `H^t_c(M_n) × H^{2−t}(D_n) → F_ell` and `H^t(∂; M_n) × H^{1−t}(∂; D_n)` are **perfect** ([C] `cl:pd`(1) — OPEN in [C], so this is the oracle that tests it; a failure is a *finding*, reported, not worked around) and `⟨A_c(T_p) x, y⟩ = ⟨x, A(D_n)(T_p) y⟩` for `p ∈ {2, 3, 5, 7}` ([C] `cl:pd`(2)) — **the acceptance gate for `X_3`** (OP3, `obl:coneexact`(vii)); the **socle ↔ Loewy** duality ([E Pred. 4.6], [E §5.1] item 5 = `HeckeIdentityCertificate` **item 7** since v1.10 — item 5 is Dickson `L·`) asserted at `(10, 691)` and on the Kummer cells (`rad^i(V^∨) = (soc^i V)^⊥`); the `ι`-pairing sign `⟨ι^*x, ι^*y⟩ = ε⟨x, y⟩` **recorded** with `ε` compared to `−(−1)^n` and the `+ ↔ −` matching of [C] `rmk:iotapairing` (a prediction in [C], asserted nowhere); the `dual(L)` relation list is the `adj`-transposed one of `symmetric_power` relation by relation; golden objects (add-only): tier A `dim_H(D_n)^q`, `charpoly_A(D_n)(T_p)^q`, `pairing_perfect^t`, `pd_adjoint^t`; tier B `pairing_matrix^t` |
| `HeckeReductionValidation` | standard, ≈ 4 s (**v1.13**: 68 970 checks, ≈ 3.3 s — slot-9 WP-3's `ell ∈ {2, 3}` rows of arm (X) (66 members), WP-4's item-4b arms (306 checks after WP-4t; `(60, 5)`'s ring arms in the `slow` sibling, which has 3731); **v1.12: shipped**, ≈ 2.4 s, 68 632 checks — WP-1's elimination arms, WP-3's (K)/(B)/(P)/(C)/(T)/(U)/(X), WP-3r's (M), WP-4's item-4a arms; its `slow` sibling `HeckeReductionCoverageSlowValidation` runs (d) over the E2 case list at `ell ≥ 5`; the text of this row is v1.10's, read with §6.2 E8's v1.11 and v1.12 notes — F3: the reductions are map equalities, never "reducing to the `F_ell` matrix") | **E8** (OQ18) | **the `F_ell` path untouched**: `GOLDEN_STRICT=1 GoldenRegressionValidation` and the whole existing suite green on the E8 tree (E8's code path is selected only by `ModCtx::prime_power(ell, k)`; the `ModCtx(p)` constructor and every kernel it reaches are unchanged, R21), `cross_config.sh` over the CLAUDE.md arms; **the ring**: `ModCtx` over `Z/ell^k` for `(ell, k) ∈ {(5, 2), (5, 3), (691, 2), (134217757, 2)}` (u32 where `ell^k < 2^32`, u64 otherwise), `mul/add/sub/reduce` against `ModArithmetic` on `10^6` fixed-seed samples, `inv` only on units and a named error on a non-unit, `valuation(x)`; **Howell-form elimination** (`engine::elim::howell`) against a naive reference on fixed-seed and structured matrices: the form is unique, `kernel`/`image` correct as `Z/ell^k`-modules (length bookkeeping), `solve_multi_rhs` exact; **the pipeline over `Z/ell²`**: `EquivariantCohomologyOnK` on the SL(2,Z) model at `(n, ell) ∈ {(10, 691), (6, 5), (16, 5)}` with `coefficient_ring = Z/ell^2`, `dim`s replaced by lengths and the invariant-factor decomposition recorded; **the reduction map** `Z/ell² → Z/ell` on cochains and cohomology equal to the `F_ell` run's objects entrywise after reduction, and `A^{(q)}(T_p)` over `Z/ell²` reducing to the `F_ell` matrix; **the Bockstein** `β: H^q(F_ell) → H^{q+1}(F_ell)` from `0 → Z/ell → Z/ell² → Z/ell → 0` computed from the stored bases, `β ∘ A(T_p) = A(T_p) ∘ β` **asserted** at `ell ≥ 5` (C-A3(ii.6) — on the nose because the tables are integral), `β² = 0`, and the exactness of the coefficient long exact sequence with length bookkeeping; **the D6 refinement**: at `(10, 691)` over `Z/691²` the Eisenstein and cuspidal eigenlines separate (the socle of the unsplit `H^1_m ⊗ F_691` is 2-dimensional and the `Z/691²`-run distinguishes the two reductions) — **recorded**, and the published Eisenstein line stays `soc(X⁺_{4,m})` (confirmation 9(a)) |
| `HeckeFreeModelValidation` | slow, ≈ 1 min (**v1.14**: 801 checks, ≈ 1.2 s — slot-10 WP-8 closed m-6 / m-7 ((T6) refuses on the object's 3 degrees; arm (R) dropped); test (3) hosted by `HeckePeriodicityClassValidation` (WP-13), tests (4) / (5) by `HeckeIntegralActionValidation` arms (3c) / (3d) (WP-11); **v1.13: shipped `standard`**, ≈ 4 s, 803 checks — slot-9 WP-11, M0 on `C_I`: tests (1), (2), (6) and [IB] §6.2 M0 items 1–8; review minors m-6 / m-7 open) | **E9** (OP4 / OC-1 / OD-T1; C-A5). **v1.12 ([OD] S8-6c, [IB] OD-8 (a)): re-hosted in line 2 on the unrefined `Xbulk`** — tests (1), (2) and the negative control (6) in M0, tests (3), (4), (5) in M1(a), the `oc1c` stabilisation report in L2-3; its golden objects move under [IB] OD-9 (one add-only emission at L2-4). The text below is v1.10's | the **six tests of [R §5]** on the *computed bulk column of the free model* at `truncated = true`: (1) `dim H^q(Γ; F_2) = 1` for `q = 0 … q_max` and `dim H^q(Γ; F_3) = 1` at `n = 0`; (2) `dim H^q = dim H^{q+2}` for `2 ≤ q ≤ q_max − 2` at `ell ∈ {2, 3}` (so `q_max ≥ 5`, both instances `H^2 ≅ H^4`, `H^3 ≅ H^5`); (3) the class `e ∈ H^2(Γ; Z) ≅ Z/12` as a 2-cocycle of the central extension ([C] `lem:bulkperiodic`, clause (1)), cup with it as `E_q: H^q → H^{q+2}`: invertible for `q ≥ 2`, `E_1` surjective with kernel `∂(N_{−I} V)` — injective at `ell = 2`, `n` even; kernel `= ∂(V)` at `ell = 3`, `n` even; (4) `A^{(q+2)}(T_p) E_q = E_q A^{(q)}(T_p)` for `q ≥ 2`, `p ∈ {2, 3, 5, 7}`, and the char-poly form `charpoly A^{(q)}(T_p) = charpoly A^{(q+2)}(T_p)` for `q ≥ 2` (the form the record carries beside the dimensions); (5) `charpoly A^{(3)}(T_p) | charpoly A^{(1)}(T_p)`; (6) **negative control**: the harness refuses to run 1–5 on the shipped 7-vertex model (`truncated = false`) and asserts nothing there ([C] `rmk:ell2window`(1)); plus the truncation contract of [C] `open:ell2` / `obl:coneexact`(iv) on the free model (exactness asserted at every fully reported spot, only the incoming composite at `H^{q_max}(∂)`, `coker r^{q_max}` recorded), `q_max_source = set`, a `q_max` below 4 refused by the validation (not by the pipeline), the specialisation `thm:specialisation`(4): at `6 ∈ R^×` the free model's `dim`s, `A^{(q)}(T_p)` char-polys and `Θ`-level objects equal the 7-vertex model's (golden), and `tau_table_p2.txt` unchanged; golden objects (add-only, `ell ∈ {2, 3}` only): tier A `free_dim_H^q`, `free_charpoly_A(T_p)^q`, `free_periodic`, `free_e_rank^q`; tier B the table hashes |
| `HeckeAtlasValidation` | slow, ≈ 5 min | E6 | `Σ(5)`, `Σ(7)`, `Σ(11)` closed under `θ`-twist and containing weight `ell + 1` (`Δ mod 11 ∈ Σ(11)`); `S_sep` separates; `bernoulli_mod` against the Kummer table (`691 \| B_12`, `3617 \| B_16`, `103·2294797 \| B_24`, `657931 \| num(B_26/26)`, …); **Glover factors** of `Sym^n(F_ell^2)` (`Sym^{n_i} ⊗ det^{j_i}`, `0 ≤ n_i ≤ ell − 1`, `n_i + 2j_i ≡ n`) against the Brauer character of `ρ_n` on `SL_2(F_ell)` for every `n ≤ 3ell` at `ell ∈ {5, 7}`; the per-`ρ̄` tangent pair computed at `ell ∈ {5, 7}` and `"deferred"` recorded at `ell = 691` ([XA M7]); predictions attached and their `confirmed` flags on the E2 cases |
| `HeckeExtEndToEndValidation` | slow, ≈ 3 min | E6 | the acceptance gate: the whole of [E §5.1] (identities 1–7, hard, on the applicable range `n > 0` even, `5 ≤ ell < 2^32`; **identity 6** — the residue-character multiset of `H^1` equals the `θ^{j_i}`-twists of the atlas systems over the Glover factors plus the `H^0`-corrections — on `ell ∈ {5, 7, 11}`, `n ≤ 200`; identity 5 in its socle↔Loewy form once E7 exists — v1.10: certificate item 7, asserted on 8 cells by slot-6 WP-9; identity 6 = item 6, 108 / 108 cells, `slow`, 5135 checks) and [E §8] (predictions, recorded) over every case listed there that the phases so far make available; aggregate failing = `0` |

**The OQ14 asserted cases** (DECIDED: annotations, plus selected assertions for validation /
debugging). The predictions asserted **inside validations**, through `predictions = assert` — never
in a campaign, where every prediction is an annotation — are at least: the `(10, 691)` Ramanujan
block ([E Claim 8.1], `HeckeExtRamanujanValidation`); the **ten Kummer cells** of [E Claim 1.8]
(`HeckeExtKummerValidation`: exactly one non-split Eisenstein–cuspidal ideal, Loewy `(2, 1)`); the
Dickson loci **`(6, 5)`, `(12, 5)`, `(8, 7)`** (`HeckeExtSmallEllValidation`: `dim H^0`, the `χ_1`
character, the `(12, 5)` multiset); and, once E4/E7 exist, the boundary characters `χ_b` on the
eleven cells and Harder's `r^1 = 0` on the Kummer list (`HeckeBoundaryValidation`), the socle ↔
Loewy duality at `(10, 691)` (`HeckeDualityValidation`). Every other prediction of [E §4.3] stays an
annotation whose `confirmed` flag is *recorded* by `HeckeExtEndToEndValidation`.

**Acceptance gate** (the analogue of the Hecke feature's `HeckeEndToEndValidation +
HeckeBadPrimeValidation + HeckeBenchmarkSmoke`): `HeckeExtEndToEndValidation` +
`HeckeExtRamanujanValidation` + `GOLDEN_STRICT=1 GoldenRegressionValidation` (tier A **and** B) +
`./cohomology_app --all` green, and `docs/matrix-engine/tools/cross_config.sh RelWithDebInfo Bench
Check RelWithDebInfo+HECKE_PURE_INTEGER=ON RelWithDebInfo@ENGINE_BACKEND=legacy --validations
HeckeExtRamanujanValidation,HeckeExtDeterminismValidation,HeckeSturmBoundValidation,HeckeLocalityValidation`
green. `--all` grows by `≈ 40 s` (v1.1: ≈ 27 s; the re-scoped determinism arms and the four-hash
grid arm are the difference); `HeckeExtKummerValidation`, `HeckeAtlasValidation` and
`HeckeExtEndToEndValidation` are `slow`, i.e. `--all-full` only.

---

## 6. Phasing, effort, dependencies, risks

### 6.1 Dependency graph

```
E0a (value-preserving: GoldenDump, read-only CertifyLocality, 4-hash grid arm, Fnv.h, (160,691) probe, U_ell RSS fit)  [slot 1: WP-1, WP-2]
 ├──> E0b (fix, strict mode, HeckeSettings, hecke_report/v2 + oc1a fields: THE re-baseline) ──> E1b ──> E2 record + campaign + golden ──> E6 atlas / predictions / identity 6 / first ext campaign (n <= 200)
 └──> E1a (HeckeLocalAlgebra, certificates (a)/(b), commutant resume) ──────────────────────┘        │                                        │
HeckeSturmBound (E1s, pipeline-free, resumable state per §1.3.1; slot 1: WP-3) ───────────────────────┘        │                                        │
C-A1 [C] sec:involution (MET) ──────────────────────────> E3 iota (production iota^* = -rho_n(iota) per block; record integration after E2) ┤
C-A2 [C] sec:boundarydatum (MET) ──┬─> E4a (slot 1: tau_bd, Theta^bd, r^q, model recording) ──> E4b (slot 2: diagnostics, H^1_!, Harder) ──> E5 core ──> E5 cross-routes
C-A3 [C] sec:cone + sec:orbifoldmodel (MET) ──┘                                                                                                   │
C-A4 [C] sec:contragredient + cl:pd (MET as specification) ──> E7 D_n + pairing (after E2 for the socle/Loewy checks, after E5 for the H_c pairing; the PD gate for X_3)
OQ18 ──> ENGINE_API.md §13 (composite modulus, non-field elimination; first item of E8) ──> E8 Z/ell^k: reduction maps, Bockstein a = b = 1 (after E2; boundary/cone halves after E5)
OD-T1 + OP4 + OC-1 (oc1a) ──> C-A5 (contract: the concrete refinement and free model, slot 7) ──> E9 free Gamma-model, truncated pair, the six [R §5] tests (after E5; hosts nothing of E0-E8)
Console C0 (slot 1) ──> C1 (no decomposition transcript/hash frozen before E0b) ──> C2 settings (the mathematical settings via the registry) ──> C4 ──> C5 after E5's schema freeze
```

### 6.2 Phases

**E0a — Value-preserving groundwork** (§3.4, [XA M2]). Scope: `GoldenDump` + `golden_explain.py`
(both parts), `CertifyLocality` as a read-only free function, `HeckeLocalityValidation`'s trap /
frozen-predicate / four-hash grid arms, G2 + `HeckeIdentityValidation`, `DicksonInvariantCount`,
`Hecke/SubspaceOps` seed (`SolveColumnsExact`, `HStack`, `PrimaryRCFBasis`, `algebra_closure`),
`ModArithmetic/ModArithmetic/Fnv.h` (sole owner), the `U_ell` RSS measurement and constant fit, the
`(160, 691)` probe. **Slot 1: [SP] WP-1 (Opus, L) then WP-2 (Sonnet, M), Lane B1.**
Acceptance: (a) the new validations `0`; (b) `GOLDEN_STRICT=1 GoldenRegressionValidation` tier A
9446 failing 0 **and** tier B 4603 mismatching 0 — the reference is not touched; (c)
`CampaignSmokeValidation` green and `summary.tsv` byte-identical outside timing columns (the FNV
unification is value-preserving); (d) the grid arm's verdict — every block local, or the list of
non-local cells — and the probe's verdict reported to the owner and written into §9; (e) the two
`U_ell` constants recorded with their three measurements. **0.5 AU, ≈ 0.9 k lines.**

**E0b — The locality fix and the re-baseline** (§3.1–§3.3). Gate: E0a accepted, [Q5], and the owner's
acceptance of any non-local cell E0a reported. Scope: the refinement loop with `ŵ`, the deterministic
`P_p` recipe, deterministic split order and the bounded loop; the `k = 1` analytic path;
`PrimaryBlock` fields; `certify()` codes 25–29; the text at the three change sites
(`HeckeReport.cpp` schema v2 + keys + note, `HeckeModuleDecomposition.cpp` `to_json` v2 + the
`to_string_offset` note, the campaign `level_a` text); the remaining `HeckeLocalityValidation` arms;
the re-baseline; the stale-schema note on the published campaign records. Acceptance: (a)
validations `0`; (b) `GOLDEN_STRICT=1 GoldenRegressionValidation` `0` after the re-baseline, with
`golden_explain.py` confirming every text difference lies in the allow-list **and** no decomposition
block list changed outside the owner-accepted splits; (c) the performance gate of §3.1 (`hecke 256`
and `decomp 128` within 5 % of E0a); (d) `--all` green on `RelWithDebInfo` and `Check`, and
`cross_config.sh` over the CLAUDE.md acceptance arms green on the golden validation. **0.75 AU,
≈ 1.3 k lines.** E0 total **1.25 AU / ≈ 2.2 k** (v1.1: 1.0 / 1.8 k — the split, the second change
site, the four-hash arm and block-list diff, the `k = 1` path and its gate).

**E1 — Local algebra, Sturm bound and generation certificates on `X_1, X_4`** (Stages 3–4), in three
workstreams that §8 runs partly in parallel:
* **E1s — `HeckeSturmBound`** (`ModPowerSeries`, Miller basis, `T_q mod ell`,
  `SubspaceOps::algebra_closure`, `SturmBoundCertificate`) + `HeckeSturmBoundValidation`. Gate:
  none (pipeline-free; `algebra_closure` is written here if E0a has not landed it yet and moved into
  `SubspaceOps` by whichever lands second). **0.5 AU, ≈ 1 k lines.**
* **E1a — `HeckeLocalAlgebra`** (with `K`, the `K`-span tangent test) and certificates (a)/(b)
  (socle bound, structured system, re-deriving `verify()`, naive oracle) on **constructed truths**,
  the cross-block evaluation test, `HeckeExtArchitectureValidation`, the bulk of
  `HeckeExtAlgebraValidation`. Gate: E0a (`SubspaceOps`, `CertifyLocality`). **1.0 AU, ≈ 2 k lines.**
* **E1b — certificate (c) and integration**: the Sturm sweep to `B'` with family-cache reuse and
  streaming, the `U_ell` budget and its record field, the real-block arms of
  `HeckeExtAlgebraValidation`. Gate: E0b, E1a, E1s. **0.75 AU, ≈ 1.5 k lines.**

Acceptance: (a) validations `0`; (b) at `(10, 691)` the algebra is `F_691[ε]/ε²`, (a) fails,
(b) `excluded_by_socle_bound` with the naive `dim C = 5`, and the record is `sturm(B')` with
`B' = 2`, `generators_certified = [2]`, `final = true` ([XA B1]; v1.1's "`certificate = commutant`"
was unpassable); (c) at `(22, 5)`, `(26, 7)` the `{2, 3}` sweep is rejected and the `B'` sweep
accepted; (d) the ext layer adds `≤ 20 %` to `--bench hecke 256 134217757 2`'s wall on the
`{2, 3, 5}` family (measured by the new `--bench ext`), the Sturm bound `≤ 0.1 s` at `n ≤ 256`
— **(v1.7) recorded by slot-3 WP-2, not gated**: at `n = 256` the ext layer (Stage 3 + 4(c)) is
0.164 s, **20.1 %** of the same `{2, 3, 5}` pipeline run but **38 %** of the literal one-prime
`hecke 256` baseline; which baseline (d) means is an **owner confirmation for slot 4** (the
recommended reading: the same-family run, or move the gate to E2's `--bench ext`).
**(v1.8) RESOLVED and MET.** [OD] slot-3 close-out 2 records that the baseline was never
understood as an owner question; the slot-4 plan §2.3 item 2 fixed it as an *engineering*
choice, and slot-4 WP-2 measured it. The gate as it now reads:
**`ext_s ≤ 0.20 × (pipeline_s + decomp_s)`** at `n = 256`, `ell = 134217757`, family
`{2, 3, 5}`, `--repeat 5`, **each phase's min over the repeats and the ratio formed from
those mins** — the denominator being "the wall of the same run without the ext layer",
which is what "adds ≤ 20 % to the wall" means. Measured on the slot-4 tree by
`--bench ext 256 134217757 2,3,5 --repeat 5`: **ratio 0.1357 / 0.1370 / 0.1366** over
three quiet rounds against the gate 0.20, and **0.1644** with a prime forced outside `S_0`
(so the streamed route is measured too); `sturm_bound_s = 0.0041 s` against the `≤ 0.1 s`
half. **Both readings of the old wording are recorded, as the slot-4 plan asks**: [X]'s
literal one-prime `--bench hecke 256 134217757 2` baseline gave 38 % on slot-3 numbers, and
[WP3-2] §7's recommended same-family reading gave 20.1 %; v1.8's denominator adds the
Stage-2 decomposition (a campaign job computes it anyway) **and** widens the numerator from
Stage 3 + 4(c) to Stages 3–5. The widening was paid for by WP-2's Stage-3 fast path, which
consumes the decomposition's certified `PrimaryBlock` locality data instead of re-running
`CertifyLocality`: `ext_s` 0.1610 → 0.1296 s at `n = 256`, −19.5 %;
(e) ASan/UBSan clean. **E1 total 2.25 AU, ≈ 4.5 k lines** (v1.1: 2.0 / 4 k — the reworked
commutant with its re-deriving `verify()` and socle bound, the cache reuse, the `U_ell` budget).

**E2 — Module structure, record, report, campaign, golden** (Stages 5, 8). Scope:
`HeckeModuleStructure` (Jordan types in units of `f`, structure-map matrices), `HeckeExtRecord`,
`HeckeExtReport` (v1.1 keys, `sturm` verbatim + `sturm_primes`, stored `t_p|_V`), `HeckeExtDriver`,
`DicksonMultiplication` (`L·`), `CanonicalPosition` with layer images, campaign keys (`ext`, `u_ell`,
`sturm`, …), per-cell grouping and columns, `--bench ext`, golden objects on the ext subgrid
(`sturm_bound` included, `ext_excluded` elsewhere, `u_ell = off`), eight validations of §5.
Gate: E1 (all three). Acceptance: (a) all `0`; (b) `HeckeExtRamanujanValidation` passes
[E Claim 8.1] in full, `U_691` included (within budget), with the generation outcome of E1 (b);
(c) golden re-emitted with *added* lines only; (d) `HeckeExtDeterminismValidation` identical digests
in every arm; (e) the campaign `sweep_full` spec (`n ≤ 40`, the nine `ell` of
`docs/matrix-engine/results/specs/sweep_full.spec`) with `ext = true` and the default
`u_ell = auto` runs in `≤ 3×` its current wall (cells with `ell < 5` or odd `n` carry an
`excluded` ext object, as in the golden harness); `U_ell` is computed exactly where the frozen model
admits it (`ell ≤ 13`, `ell = 691` at `n ≤ 110`, and `ell = 10007` at `n ≤ 18` — v1.7, the frozen constants) and every other cell carries
`u_ell_over_budget` — **no `ell = 134217757` `U_ell` is ever built** ([XA B3]; v1.1's (e) implied
`1.3·10^8`-coset runs). **Milestone M1: records on `X_1 ⊕ X_4` for every case of [E §8] that lives
in `H^0/H^1`, each ideal either certified final or flagged with a reason from the fixed list of §1.3
— Dickson-type ideals are `sturm_heuristic` by [E Claim 2.10], i.e. published `final = false`, not
certified ([XA §6]) — with `B'(k, ell)` recorded on every row.** **1.75 AU, ≈ 3.5 k lines** (v1.1:
1.5 / 3 k — per-cell grouping, layer images, the ext subgrid, the stored restrictions).

> **(v1.10) E2 IS DECLARED, item by item, by the slot-6 close** (WP-14; [OD] S6-1, S6-2, S6-2′,
> S6-5). Evidence on the close tree (`docs/implementation/slot6/WP-14_report.md` §3):
>
> * **(a) MET, with the `ext_json_*` clause booked with the source fix.** Every E2 validation of
>   §5 returns 0 (`--all` / `--all-full` green), `HeckePresentationValidation` included (WP-2,
>   `fast`, 995 checks). `HeckeExtCampaignValidation`'s golden arm (WP-6, arm 8) compares the
>   **settings-independent** ext objects — `ext_ideals`, `ext_certify`, `sturm_bound` — against
>   `GoldenReference.inc` on `(10, 691)` and `(4, 13)` with the harness's own install
>   (`u_ell = off`, `family = 2,3,5`), and **records** that `ext_json_canonical` differs by exactly
>   the one `source` substring (`"spec"` vs `"console"`). The per-ideal E3 / E4b / E5 collectors
>   are recorded as not compared (the campaign exposes the record, not the driver). **Booked
>   for slot 7's re-baseline, not unmet**: the `ext_json_*` equality, the `presentation` key and
>   its hash-invariance arm.
> * **(b) MET** — `HeckeExtRamanujanValidation` green in `--all`.
> * **(c) MET** — slot 5's emission was add-only (`golden_explain.py` exit 0 with no
>   `--allow-keys`); slot 6 moved no line (`git diff --stat bd84016 -- '*GoldenReference.inc'`
>   empty).
> * **(d) MET** — `HeckeExtDeterminismValidation` `failing_arms=0`, digest **`0xfb71e225e4185be7`,
>   bare** since WP-6's `commit` redaction.
> * **M1 MET** — re-verified: `HeckeExtKummerValidation`, `HeckeExtSmallEllValidation`,
>   `HeckeExtSeparationValidation` green under `--all-full`.
> * **(e) measured under ruling 2's protocol (A)** (`docs/matrix-engine/tools/e2e_measure.sh`,
>   fresh `--output` per run, `jobs = 16` / `threads = 2`, after the ext-identity fix) **with ONE
>   pair (`--pairs 1`) instead of three — a recorded deviation from ruling 2, owner ruling of
>   2026-09-22 ([OD] S6-2″)**, because the predicted miss is ≈ 680× and the verdict cannot depend
>   on the sample count: **MISS**: `E2E pairs=1 baseline_min_s=2.990 ext_min_s=3106.564 ratio=1038.98 gate=3.0 verdict=MISS ext_pass_min_s=3103.75 job_loop_min_s=2.814 u_ell_cells=157` — the
>   whole cost is the sequential ext pass (3103.75 of 3106.6 s); the job loop is unchanged
>   (2.8 s against the baseline's 3.0 s).
>   WP-10 §4.1 predicted a miss by **≥ ≈ 680×**: nine `sweep_full` cells build `U_10007`
>   (≈ 356 s each on a quiet box, [KI] §3), the ext pass is sequential, and `3 × W_0 ≈ 14 s`, so
>   no parallelisation of the pass can reach the bound (one cell alone is ≈ 25× it). Per ruling
>   2 the miss is **recorded**, and the `3.0` constant was kept, marked unjustified.
>
> **(e′) — the restatement the owner decided (2026-09-22, [OD] S6-2′), replacing (e) from slot 7
> on.** Let `W_0` be the wall of `sweep_full` with `ext = false` and `W_ext` the wall of the same
> spec with `ext = true`, each measured as ruling 2's protocol (A) pins it; let `T_cell` be each
> ext cell's `--bench ext` `total_s`, measured in **separate processes** under §6.2 E6 (d)'s
> protocol (`--repeat 3`, min, `ENGINE_THREADS=16`). **(e′) bounds the campaign's overhead over the
> sum of its per-cell timings: `W_ext − W_0 ≤ c · Σ_cells T_cell`.** The numerator never contains
> its denominator (`W_0` is a separate run; `Σ T_cell` comes from separate processes). The form is
> the owner's; **the constant `c` is WP-10's proposal, `c = 1.25`** (the pass is sequential, so its
> overhead is file I/O plus the job loop), to be confirmed or replaced by the owner **before** the
> first measurement under (e′), which is slot 7's.
>
> **(v1.11) E2 is COMPLETE** (slot 7; `docs/implementation/slot7/WP-14_report.md` §4). **(a) in
> full**: `HeckeExtCampaignValidation` arm 8 **asserts** the campaign's `ext_json_canonical` and
> `ext_json_full` equal to the reference at `(10, 691)` and `(4, 13)`, and its full `settings`
> block equal to the harness's install (WP-2; the `source` difference vanished under stage 1 (1)
> and the `spec` stamp). The **`presentation` key** and its **hash-invariance arm**
> (`HeckePresentationValidation` (k1)–(k5): `ext_ideals`, `ext_certify` and the record's `hashes`
> unchanged under `on`, the fingerprint moving, on-text minus the objects equal to the off-text)
> are shipped. **(e′)**: the constant **`c = 1.25` was confirmed by the owner before the
> measurement** ([S7] §10 decision 5 (B)). Protocol as ruled: `W_0` / `W_ext` by ruling S6-2's
> protocol (A), **three alternating pairs**, base spec **`sweep_full.spec`** (the lead's ruling:
> `ext_first.spec` already sets `ext = true`); `T_cell` = the **campaign cell's own computation**,
> `--bench ext <n> <ell> --campaign-cell [--u-ell V]` (slot-7 WP-6: `with_cone`, `with_sign_split`,
> family `{2, 3, 5, 7} ∪ {p}`, the record's canonical split and rendering inside `run()`),
> `--repeat 3`, min, `ENGINE_THREADS=16`, `--repeat 1` once a cell's first run exceeds 60 s, over
> the cells the ext pass drove, enumerated from its own record files
> (`e2e_measure.sh --e2prime`). Measured in the lead's window **W3** (2026-09-23T11:21:49Z–
> 15:26:39Z, head `79b178f`, binary from `c2ddbb6`):
> `E2E_PRIME cells=189 w0_min_s=3.347 wext_min_s=3507.616 delta_s=3504.269000
> sum_t_cell_s=3367.277300 c=1.25 bound_s=4209.096625 verdict=MET` — **(e′) is MET**,
> `(W_ext − W_0) / Σ T_cell = 1.041` against `c = 1.25`; the ten `U_10007` cells are 98.8 % of
> `Σ T_cell`. The pairs' `W_ext`: 3771.3, 3507.6, 3813.4 s; `W_0` min 3.347 s. The old text (e)
> reads `ratio=1047.99` against `3.0`: a MISS, recorded and superseded ([OD] S6-2′). W3's
> quietness: one matching process at the open and, for ≈ 30 min, light documents-only work and
> the Fable probes; the margin does not depend on it. **E2 is COMPLETE.**

**E3 — The involution `ι`** (A3; needs C-A1 and [Q3]). Scope: `HeckeInvolution` as an
`EquivariantCochainComplexMorphismOnK` with the automorphism `ι_K`, the orientation signs carried
combinatorially (the `transporter_vertex_perms` pattern, `Hecke/SL2ZTessellationTables.h:93-94`,
invariant I8: never geometric) and `ρ_n(ι)`; `sign_split` on `H^q` and on every stored object; the
per-sign records; the Eisenstein line `soc(X⁺_{4,m})` and its `CanonicalPosition`; `iota_sign` in
the record; `HeckeInvolutionValidation`; golden `iota^q`. Acceptance: (a) `0`; (b) `(10, 691)`:
cyclic on each sign, Eisenstein line defined and in the bottom layer; (c) the unsplit record is the
sum of the two per-sign records ideal by ideal. **1.0 AU, ≈ 1.5 k lines.**

**E4 — Boundary** (A1; needs C-A2 **and C-A3** — **both met**, [C] `sec:boundarydatum` /
`sec:cone`). **Split in v1.5 into E4a (slot 1, [SP] WP-4a + WP-4b, Lane A, Fable) and E4b (slot 2)**
— the split paragraph follows the scope. Scope: `Hecke/HeckeBoundaryDatum` + `Hecke/HeckeBoundaryOperator`
+ `HeckeExt/HeckeBoundary` (G3: `ComputeCuspRestriction` lifting
`LocalSystemSL2Z.cpp:843-923` into a library call returning the boundary cohomology object and
`r^0, r^1` as matrices in the stored bases; the **left-coset** representatives `δ_∞, δ_j`; **the
`Γ`-level `τ_∂` over `Z` with its `TauBoundaryCertificate`** (C-A3(ii.2)) **and its Shapiro
transcription `τ_∞`**; `Θ_g^∂`; route B as the oracle; the `β_j` negative control), `H^1_!`, the
Harder criterion, `X_2, X_5` in the record and in Stage 5's canonical positions, and **the two
diagnostics** of C-A3(iii)(5) — the entrywise cochain identity `r^•∘Θ_g = Θ_g^∂∘r^•` on `C^q_eq(K)`
for `p ∈ {2, 3, 5, 7}` (it needs exactly the `Θ_g^∂` E4 builds and the shipped `Θ_block` and
restriction morphism, so it costs one comparison per cell) and the cusp-support walk of the bulk `τ`
(`HeckeTauTable::tau(i, q, σ)`, `Hecke/HeckeTauTable.h:233`) — **recorded, never branched on**: after
the OQ2 verdict they select nothing ([V §7] item 7; the decision procedure of v1.2 is withdrawn,
[V §2.7]). Also records `solve_regime` for `τ_∂`. `HeckeBoundaryValidation`; golden entries. Gate:
C-A2 **and C-A3** accepted (C-A3 because `τ_∂` is *defined* in C-A3(ii.2)) — **met on 2026-09-16**
([C] v1.3.2, [SP §2.1]), which is why E4a was pulled into slot 1 (slot-1 confirmation 1, DECIDED);
its record integration waits for E2's record type, like E3's.
Acceptance: (a) `0`; (b) the `χ_b` characters and the `y^n` oracle asserted (no longer "recorded
until the convention is fixed": v1.1 fixes it); (c) Harder's criterion asserted on the Kummer list
and recorded at `(10, 5)`, `(10, 7)`; (d) `τ_∂` certified over `Z` and the route-A/route-B and
Shapiro-transcription equalities entrywise, with `cochain_commutes` / `eta_zero` and the walk's
verdict **written into §9 as findings** — they gate nothing and no longer select a C-A3 branch.
**1.5 AU, ≈ 2.5 k lines** (unchanged: `τ_∂` at `Γ`-level costs what `τ_∞` would have, and the
transcription is the validation route that was already planned). **The split** ([SP] WP-4 "Size",
[SPA] Q5 — ≈ 1.0 AU is too large for one agent session):
* **E4a** (≈ 1.0 AU, **slot 1**, Lane A, Fable) = **WP-4a** (≈ 0.5 AU: the boundary subcomplex data in
  `Hecke/SL2ZTessellationTables` (additive), the `B_N/Γ_∞` table, the certified `τ_∂`-table over `Z`
  in `HeckeTauTable`'s `ChainTerm` format with **one** shared (T1∂) helper for construction and
  certification, degree-generic (no `q < 3` literal), coefficients in `{0, ±1}`, solve regime `Z` for
  every `ell` with a failing table aborting — `def:bdrygroup`, `prop:bdrycosets`(1)–(3), `def:taubdry`,
  `lem:bdrycomponent`, `lem:taubdryexists`, `obl:taubdry`(i)–(iv); `HeckeBoundaryValidation`
  registered with its certification and tampered-chain arms) **then WP-4b** (≈ 0.5 AU: `Θ^∂_g` on
  the circle model as a library call lifted from `LocalSystemSL2Z.cpp:843-922`, routes A (Shapiro
  transcription) and B (the `M^T` / `M_T` formulas), `r^q`, the `β_j` negative control, the
  characters `χ_b`, `obl:taubdry`(v)–(vii), `prop:bdrycosets`(4), `sec:oraclesnew` (A), and the
  **model recording**: the operator is built for **every `ell`** and records `boundary_model =
  circle`, `boundary_is_group_cohomology = (2 ∈ R^×)` — `false` at `ell = 2`, where by [C]
  `prop:circlemodel`(3) it computes the bounded orbifold-model boundary analogue of
  `rmk:ell2window`(1) and *not* `H^•(∂; V)` — never a refusal (slot-1 confirmation 11, DECIDED;
  [SPA] F1)). E4a adds **no golden entry** and changes no golden value; its acceptance is [SP]
  WP-4's (a)–(d) with the `-DHECKE_PURE_INTEGER=ON` arm and `tau_table_p2.txt` byte-identical.
* **E4b** (≈ 0.5 AU, **slot 2**, Lane A) = the two diagnostics, `H^1_!`, the Harder criterion,
  `X_2, X_5` in the record and in Stage 5's canonical positions, and the golden objects
  `dim_H0_bd`, `dim_H1_bd`, `rank_r^q`, `charpoly_A_bd(T_p)^q`, the `χ_b` multiset (tier A) and
  `r^q`, `A_bd(T_p)^q` (tier B) — **defined here, emitted with E2's add-only ext-subgrid emission**
  ([SP §4.2], so that slot 2's one mutating re-baseline stays E0b's pure text-schema diff); record
  integration after E2. If only WP-4a lands in slot 1, [C]'s roster row for `obl:taubdry` reads
  "partial: (i)–(iv)" and WP-4b carries over with E4b.

**E5 — Equivariant mapping cone** (A2; needs C-A3 — **met** — and E4a's `τ_∂`). Scope: `EquivariantMappingCone` on
`FlatMatrix` + `engine::elim` (port of `CochainComplexMorphism::ConeComplex`,
`SimplicialCohomology.cpp:832-1010`, onto the block objects `C_eq_block / Z_eq_block / B_eq_block`
of both complexes); the maps of (3.1); **`HeckePairHomotopy` — the `η`-table over `Z`** built by
`HeckeTauTable`'s step-2/3 machinery with `∂X` as source (paths for boundary vertices, forced fills
for boundary edges; [V Lemma 2.3.1]) with its `PairHomotopyCertificate`; `HeckeConeAction` assembling
`Φ_g(a, b) = (Θ_g a, Θ_g^∂ b + h a)` from `Θ_eq` (`Hecke/HeckeOperatorOnK.h:227` — which is empty in
the memory-lean level, so the cone runs with `ScopedThetaEqCertification(true)` or recomputes
`Θ_block · C_eq_block`), `Θ^∂` and the **derived** `h := η̃` (coset transport, never a free cochain
object) with its `ConeActionCertificate`; `X_3, X_6` in the record; `HeckeConeValidation`; golden
entries; the record carries `q_max`, `truncated`, `q_max_source`, `degrees` (the constants
`2` / `false` / `derived` / `{0,1,2}` here) and `les_maps` per reported spot, and nothing in E5
hard-codes `q ∈ {0, 1, 2}` (§1.2). Gate: C-A3 accepted (**met**), E4a's `τ_∂` (slot 1) — the core
starts in Lane A in slot 2, once E4b's diagnostics are in (§8). Acceptance: (a) `0`; (b) exactness and bookkeeping on the
whole E2 case list; (c) at `(10, 691)`, `X_3` glues the boundary class as [E §8.1] states, with
`dim X_3 = 3` (v1.7: measured by `HeckeConeValidation`; v1.6's `4` assumed `r^1 = 0`), and the `Hom(ker r^1, coker r^0) ≅ F^2` ambiguity — real for a *free* cochain-level `h`
([V §2.2]) and non-zero there — **discharged by construction**, exhibited by the two-`η` arm and by
the tampered-`h` negative control (§5); **(d) Peak memory** — restated by the owner on 2026-09-22
([OD] slot-4 close-out 1), replacing v1.2's "RSS at `n = 256` within `1.5×` of `hecke 256`":

> **(d) Peak memory.** Let `M_cone` be the `VmHWM` of a process that constructs exactly one
> `EquivariantMappingCone` at `n_sym = 256`, `ell = 134217757` on the SL(2,Z) 7-vertex model, calls
> `ConeCertificate::verify()` once on it, and does nothing else. Let `M_base` be the `rss_mb`
> reported by `./cohomology_app --bench hecke 256 134217757 2 --repeat 1` in a separate process on
> the same box in the same session. **(d) is met iff `M_cone ≤ 2.0 · M_base`.** The same ratio for
> a process that additionally constructs the `HeckeConeAction`, and the same ratio at
> `n_sym = 200` (the first campaign's bound), are **measured and reported, not gated.**

> **(v1.9) (d) IS MET, and E5 IS ACCEPTED.** Slot-5 WP-5 put the cone's `Z / B / H / P` loop and
> `ConeCertificate`'s C2 / C3 / C5 span inclusions on the `engine::tape` and measured, under
> exactly the protocol above, over five interleaved rounds against a pre-package binary:
> **`M_cone` 510.8–524.1 MB against `M_base` 262.6–275.5 MB, i.e. 1.90–1.95×, median 1.93×**
> (the pre-package tree read 2.17–2.19×). Met at every `n` of the [WP4-4] grid — 1.58 / 1.81 /
> 1.86 / 1.89 / 1.93× at `n = 64 / 128 / 160 / 200 / 256` — and at the worst cross-pairing of the
> five rounds (largest numerator 524.1 with smallest denominator 262.6), 1.996×. **Nothing was
> sampled, relaxed or moved out of `compute()`**; value preservation is proved by a
> whole-printed-output and collector-digest diff. Reported, not gated: cone + action **1275.8 MB
> = 4.86×** (up 33 MB — the tape's program cache and per-worker arenas are retained under the
> action's own, much higher, peak), and `n = 200` at **1.889×**. **Two slot-4 findings are
> superseded**: `verify()` is no longer ~20 % *below* the cone's high-water mark — after the tape
> the construction peaks at 450.2 MB and the certificate takes it to 511.4 MB, so `verify()` is
> 13.6 % *above* and **is** the binding item; and the input floor at `n = 256` is **0.80×**, not
> 0.85×. The next lever below ~1.7× is a `--lean`-style release of the bulk intermediates the cone
> does not read twice — a change to `EquivariantCohomologyOnK`'s retention contract, not
> attempted. **The v1.8 defect record below is kept as history.**

> **(v1.8, HISTORICAL — superseded by the restatement above) (d) IS NOT DECIDABLE AS WRITTEN,
> AND ON EVERY READING IT IS NOT MET. THIS IS A DEFECT IN THIS CLAUSE, RECORDED HERE; THE
> RESTATEMENT BELOW IS A PROPOSAL, NOT A DECISION.** Slot-4 WP-4 measured the cone and the cone action at
> `n ∈ {64, 128, 160, 200, 256}` against a same-round `--bench hecke n 134217757 2`,
> interleaved against a `9ae1d7a` binary on a quiet box
> (`docs/implementation/slot4/WP-4_report.md` §3).
>
> * **The clause pins no measurement protocol for its denominator.** `--bench hecke 256
>   … --repeat 1` peaks at **262.0 MB** and `--repeat 5` at **372.7 MB** (samples 364.7 /
>   372.7 / 421.5) — the two differ by **1.42×**, so *the same tree* reads **2.19×** or
>   **1.54×**. `--repeat 5` is not more work; it is allocator high-water accumulated across
>   five teardown/rebuild cycles. It is also not reproducible to better than **±10 %** at
>   `n = 256` and **±28 %** at `n = 160`, whereas `--repeat 1` reproduces to ±1 %. **That
>   spread is larger than the 4 % by which the cone misses the gate.**
> * **The clause does not say which E5 object the numerator is.** The cone alone is
>   **573.2 MB** at `n = 256`; the cone together with its Hecke action — also E5 — is
>   **1243.0 MB**. They differ by **2.2×**.
> * **The verdict, on every reading.** Cone alone: **2.19×** (`--repeat 1`) or **1.54×**
>   (`--repeat 5`) at `n = 256`; the best ratio anywhere on the grid is 1.69× / 1.28×, at
>   `n = 64`; **not met at `n = 256` and not met at any `n ≤ 200`** under `--repeat 1`.
>   Cone + action: **4.74×** / **3.34×**, not met under either, by a wide margin.
> * **What WP-4 did about it.** Three *value-preserving* reductions, with **no clause
>   sampled, relaxed or moved out of `compute()`** (the rank-identity span inclusions, the
>   released per-degree buffers, the batched standard-basis sweep): the cone 620 → 573 MB at
>   `n = 256`, i.e. **71 % of the gap slot 3 recorded**, 1.66× → 1.54× under the `--repeat 5`
>   denominator. The action's wall fell 122 → 75 s (−38 %) with RSS unchanged. **WP-4 did not
>   change (d) and neither does this version.**
> * **Proposed restatement, for the owner to accept or reject at slot 5's E5 acceptance**:
>   *"(d) `VmHWM` of `EquivariantMappingCone::compute()` + `verify()` at `n = 256`,
>   `ell = 134217757`, measured in a process that does nothing else, within `1.5×` of
>   `--bench hecke 256 134217757 2 --repeat 1`'s `rss_mb` measured the same way; the cone
>   Hecke action is measured and reported but not gated."* That pins both free variables and
>   picks the reproducible denominator — and **under it the cone is 2.19× and still fails**,
>   which is the honest consequence: the next lever is the cone on the tape (slot 5 Lane A,
>   ≈ 0.75 AU), not a rewording. **The engineering default if the owner does not answer**
>   ([S4] §6): (d) unchanged, the cone on the tape planned for slot 5.
>
> **(v1.9) The owner answered on 2026-09-22 and took a variant of this proposal** — same
> numerator and same denominator protocol, bound **2.0×** rather than 1.5× — and slot-5 WP-5
> built the lever this paragraph named. Both halves of the prediction held: the restatement alone
> would not have carried the clause (the cone was 2.19× under it), and the tape did (1.93×).
**3.25 AU, ≈ 5.2 k lines**, in three parts (owner decisions OP8 and OP3, 2026-09-15, §11 — OP8
accepted the verdict's `3.0 → 2.5` re-cut of the *core*, OP3 **amended** its "one cross-route" to
**both**, so the optional `+0.5 AU` placeholder is replaced by a committed, honestly re-cut figure):

| part | AU | lines | why that number |
|---|---|---|---|
| **core E5** (cone, `η`-table, `Φ_g`, certificates, record, golden) | **2.5** | 4 k | v1.2 priced 3.0 / 4.5 k; [XA §6] estimated 2.5–3.0 and the *lower* end is now right — the (b1)-proof risk that priced the upper end is gone (well-definedness is a theorem, [V §2.4]–[V §2.5], PROVED over `Z` for all `ell`) and the `η`-table is a fixed construction with no search |
| **cross-route 1 — strict pair `τ^s`** ([V Prop. 2.6.2]) | **0.5** | 0.8 k | a `TauVertexPolicy::BoundaryStrict` in the `τ` builder, a **second certified integer table** with its own `TauCertificate` run and its own fill search, then a full re-assembly of `η ≡ 0`, `Φ^s` and `A_c^{(q)}` for comparison. This is the 0.5 AU [V §7] item 5 priced, and nothing about it got cheaper |
| **cross-route 2 — relative complex ([V §2.10], "route 3")** | **0.25** | 0.4 k | strictly cheaper than route 1, and that is the whole reason the re-cut is not `+1.0`: it introduces **no new certified table and no search**. `E := ext_0 ∘ h` and `Θ' := Θ + dE + Ed` are formed from objects E5 already holds, and `ker r` is the shipped `EquivariantCohomologyOnK` on the bulk model with the seven boundary simplices' cochain values forced to zero. What is actually new is the `ker r` sub-complex constructor, the `Θ'` assembly, the basis correspondence `H^•(\ker r) ↔ H^•_c`, and the validation arm |

Gate for both cross-routes: the core E5 accepted. They are **validation arms, not definitions**,
and they do **not** move the record schema — which is why the core can still be accepted (and C5's
schema frozen) before they land.

> **(v1.10) The two cross-routes landed, and with them the PD gate** — `obl:coneexact`(vii) is
> implemented in all three sentences. **Cross-route 1** (slot-6 WP-4): `HeckeConeStrictPairRoute`
> on `TauVertexPolicy::BoundaryStrict`, fills over `Z` only (int64, then `__int128`), its own
> `certify()` with strictness clause (g); `A_c^s == A_c` on 212 / 212 operators (636 degrees),
> asserted on 138 at `6 ∈ R^×`, recorded on 74 at `ell ∈ {2, 3}` with 0 disagreements;
> `η^s ≡ 0`; 4650 int64 fills, 0 widened. **Cross-route 2** (WP-5): `HeckeConeRelativeRoute`
> (`E = ext_0 h`, `Θ' = Θ + dE + Ed`, `ker r` by `EquivariantCohomologyOnK`'s new relative
> sub-complex constructor): `M A' M^{-1} == A_c` on 212 / 212, aborting at every `ell`.
> **The PD gate** (WP-3, E7b, below). Both arms are validation arms of
> `HeckeConeActionValidation` (A14, A15) with their own logs, so every pre-existing printed line is
> unchanged — `docs/matrix-engine/tools/cone_output_diff.sh` (WP-4) is the proof. WP-5 also
> relabelled `A_c(T_p)^q` tier `'B'` in the unit and removed the harness override; no golden value
> and no printed digest moved.

**E6 — Atlas, predictions, canonical field, scaling** (Stages 6–7, [E §6.2]). Scope:
`HeckeAtlas` (with the `U_ell` budget: `U_691` for `n ≤ 110` only — v1.7), `HeckePredictions`,
`HeckeCanonicalField`, labels in the record, `S_sep(ell)` added to the heuristic sweep **and Stage
2(3)'s re-decomposition with `S_0 ∪ S_sep(ell)`**, the **Glover-factor unit and identity 6**
([E §5.1] item 6: `GloverFactors(n, ell)` and the comparison of `H^1`'s residue-character multiset
with the `θ`-twisted atlas systems), the per-`ρ̄` tangent pair for `ell ≤ 31` (deferred above), the
split form option, `ext_compare.py`, `HeckeAtlasValidation`, `HeckeExtEndToEndValidation`, the first
ext campaign (`ell ∈ {5, 7, 11, 13, 691}`, `n ≤ 200`) and its table under
`docs/matrix-engine/results/` — republished under `hecke_report/v2` — with `iota_sign` fixed by
the owner beforehand ([Q3], [Q18]). Gate: E2, E3 (sign), [Q3]. Acceptance: (a) `0`; (b) the
acceptance gate of §5; (c) the campaign table published with `analysis.txt` listing every
`unpredicted` entry, every `"local": false` block, every `(k, ell)` with `B' = none`, every
`u_ell_over_budget` cell and every Stage 2(3) split. **1.75 AU, ≈ 2.8 k lines** (v1.1: 1.25 / 2 k;
[XA §6] 1.5 — plus identity 6's unit, the Stage 2(3) re-run and the per-`ρ̄` pairs, which the audit
listed but did not price separately).

**(d) The canonical-field performance gate** (v1.10; [OD] E6-1 / E6-2, text of
`docs/implementation/e6_gate_brief.md` §6.1 verbatim). Let the **numerator** `canonical_field_s`
be the wall time of producing the canonical split form — `alg:split` step 1's root finding in
`F_ell[Y]/(C_{ell,r})` plus the rendering of `hecke_canonical_split/v1` — for **every
certified-local ideal of the cell's record**, and the **denominator** `total_s` the wall time of
the same cell's `HeckeExtDriver::run()`, as `--bench ext` prints both. **(d) is met iff
`canonical_field_s ≤ 0.10 × total_s` on every one of the 23 cells** — the atlas cells
`ell ∈ {5, 7, 11, 13}`, every even `n ≤ ell − 1`, and `(10, 691)`, `(160, 691)`, `(198, 691)`.
**Protocol**, pinned: `./cohomology_app --bench ext <n> <ell> 2,3,5 --repeat 3` per cell on the
reference machine (CLAUDE.md), default build, **each column's min over the repeats and the ratio
formed from those mins**. The measurement harness times the two report forms **outside**
`total_s`; if a later revision moves the canonical split inside the timed run, the denominator is
`total_s − canonical_field_s`, so that the numerator is never part of its own denominator.
**`own_field_s` is measured and reported beside it — the `--bench` comparison against the
own-field route that `[OD]` OQ10 asks for — and is not a bound**; so are
`canonical_field_ideals`, `canonical_field_ok` and `canonical_field_r_max`.
*Rationale for the constant.* `0.10` is the constant the gate has carried since `[E]` v1.4.0;
this restatement changes the denominator only, as v1.8 did for §6.2 E1 (d). The worst cell
measured is `(198, 691)` at **2.92 %** (`[WP5-7]` §4), so the bound budgets the report layer
**3.4×** its present cost. What that headroom buys is stated rather than assumed: the numerator
grows like `r³–r⁴` in the maximum residue degree (`[WP5-7]` §4 obs. 3) and the denominator like
`n^{1.72}–n^{2.05}` (CLAUDE.md), so at a `(198, 691)`-shaped cell the bound admits a maximum
residue degree of roughly `r ≤ 13–14` before it fires, and it fires on any regression costing
more than 3.4×. The `≤ 2 × own_field_s` half of the pre-v1.9 wording is **deleted**: its
denominator is tier (i)'s rendering, which `[E]` `sec:field` defines as "zero new arithmetic", so
the clause demanded that certified root finding cost no more than twice a `sprintf` — it failed
6.1–11.4× even on the 21 cells where `r = 1` and the numerator's mathematics is empty, and the
only ways to satisfy it are to slow the denominator down (`[WP5-7]` §4, `[WP5-13]` §5.2).
**If (d) fails**, the default `split_field_report = canonical` flips to `own_field` for the first
ext campaign, the measurement goes to the owner, and the `F_{ell^r}` element type of §6.5 is the
reopening question (§0.3). **If (d) holds, the default stands** and §0.3's non-goal is not
reopened.

> **(v1.10) The owner's measurement condition, discharged at the slot-6 close; E6 is NOT
> declared** (slot 7, §8). (a) `(10, 691)`'s `total_s`: **0.7168 s**, `canonical_field_s` 14 µs,
> ratio 0.00002 (closing window). (b) Cells with `canonical_field_r_max ≥ 11`:
> WP-7's scan hit `(210, 691)` at `r_max = 14` on its first point, and WP-10 found
> `(256, 134217757)` at `r_max = 19`. **The 23-cell verdict: 23 / 23 MET** in the closing window, worst
> `(198, 691)` at 0.0315. **Both high-`r` cells
> FAIL the bound** in the lead's early quiet window: `(210, 691)` **0.262**, `(256, 134217757)`
> **1.14** (closing window: **0.264** at `r = 14`, **1.119** at `r = 19`). So the gate holds on its own
> cells and fails off them, and the rationale's "`r ≤ 13–14`" is refuted as a safety margin: the
> numerator grew ≈ 90× from `r = 10` to `r = 19`, and slot-6 WP-8 located it — root finding
> (`FindCanonicalRoot`) is ≥ 96 % of `canonical_field_s` at every `r ≥ 10`, growing ≈
> `r^5`–`r^6` between `r = 14` and `19`, steeper than `alg:split`'s `O(r^3 log ell)`; field
> construction, certificate and reuse of one field per `(ell, r)` are negligible levers. **Owner ruling
> ([OD] E6-3, 2026-09-22, at the recommendation):** a small slot-7 package diagnoses and fixes
> `FindCanonicalRoot`; meanwhile `split_field_report = canonical` **stays the default** and the
> text of (d) above is **unchanged**; **the verdict of (d) stays open until after the fix**; and
> (d)'s cell list **gains a high-`r` cell**, written with the fix (the two measured cells are the
> candidates). The first campaign's `ell = 691`, `n ≤ 200` cells lie in exactly this regime, which
> is why the fix precedes E6 acceptance.

> **(v1.11) (d)'s cell list and failure rule, written into (d)** ([OD] S7-4 = [S7] §10 decision 4,
> with the owner's reading of "highest-`r`"). **The gating cells** are the 23 above **plus every
> cell of the first ext campaign whose `canonical_field_r_max` is `≥ 10`** in the deterministic
> table `docs/implementation/slot7/WP-4_rmax_ell691.tsv` (scope `campaign`), read by
> `e6_measure.sh --cells-from` — the 19 cells `n ∈ {130, 132, 134, 138, 156, 162, 166, 168, 170,
> 172, 174, 176, 180, 184, 186, 188, 190, 198, 200}` at `ell = 691` (`r_max` 10–15); with
> `(198, 691)` in both lists, **41 gating cells**. **The threshold `10` is pinned here** (it was
> slot-7 WP-4's reading, `e6_measure.sh --r-min`'s default; [E] v1.8.1 m-2). `(210, 691)`
> (`n > 200`) and `(256, 134217757)` (not a campaign prime) are **reported only**. **Failure rule
> (Z)**, replacing "flips to `own_field`" above: a miss in the verdict window goes to the owner
> before the campaign's publication run and never flips the report form by itself; the owner then
> chooses among flipping the campaign, holding `canonical` with (d) recorded not met, or delaying
> the campaign for a stronger lever; a miss on a reported cell flips nothing. **The denominator**:
> since slot-7 WP-3 item 6 the canonical split runs inside `run()` (the record's `split`), so
> `total_s` contains it and (d)'s own rule applies — the ratio is `canonical_field_s /
> (total_s − canonical_field_s)`; `--bench ext` prints `total_minus_canonical_field_s=` and
> `canonical_field_net_ratio=`, and `e6_measure.sh` uses them when present. `ENGINE_THREADS=16` is
> part of the pinned invocation (WP-10 proposal (4), adopted). The near-margin rule: a ratio in
> `[0.09, 0.11]` is re-measured once with `--repeat 5`.
> **Process deviation, recorded** ([S7] §4.3; slot-7 WP-13 m-6): this text was to be written into
> [X] by the lead's instruction **before** W1. It was not; the list was nonetheless pinned before
> W1 (06:18Z, head `3a40f68`) by the committed table and `--cells-from` (`cab4e38`), and the rule by
> [S7] §10. **Verdict, W1 (2026-09-23T06:18:30Z–06:19:18Z, head `3a40f68`, the split timed outside
> `run()`): `E6D_VERDICT gating_cells=41 not_met=0 verdict=MET`** — worst gating cell
> **`(170, 691)`, `r_max = 14`, 0.0104**; no ratio in the near-margin band; reported:
> `(210, 691)` 0.0062, `(256, 134217757)` 0.0151 (slot 6: 0.264 and 1.119). **The default
> `split_field_report = canonical` stands and §0.3's non-goal is not reopened.** W4 confirms:
> **W4 (2026-09-23T16:39:28Z–16:58:04Z, head `d6ea91e`): `E6D_VERDICT gating_cells=41 not_met=0
> verdict=MET`**, worst gating cell `(170, 691)` at **0.0107** (denominator `total_s −
> canonical_field_s`), reported `(210, 691)` 0.0061, `(256, 134217757)` 0.0148 — no reversal.
>
> **(v1.11) The root finder** (slot-7 WP-4, `fa829c7`, `cab4e38`). A deterministic operation
> counter (`CanonicalFieldOpCounts`, `HeckeCanonicalFieldValidation` arm H) found verdict **(ii)**:
> the pre-WP-4 route sat at its own count, `O(r^5 log ell)` `F_ell`-multiplications (fitted
> exponent 4.8–5.6 over `r = 10..20` at `fa829c7`), with no defect above it; [E] `alg:split`'s
> `O(r^3 log ell)` is right **in `F`-operations**, and its "negligible" was refuted at `r = 14` and
> `19` ([E] v1.8.0 / v1.8.1). The fix keeps [E]'s candidate sequence and every gcd outcome and
> changes only how the splitting polynomial is evaluated: `u ↦ u^ell` in `F[X]/(f)` as a
> precomputed `F_ell`-linear map, a flat allocation-free quotient-ring product with delayed
> accumulation, and the Frobenius orbit through the same matrix. `F_ell`-multiplications at
> `r = 19`: **144.1 M → 12.1 M** (`ell = 691`), 437.4 M → 27.7 M (`ell = 134217757`). Every value
> is exact: 629 `hecke_canonical_split/v1` texts (`r ≤ 54`, `candidates_used` included) and the
> four atlas stores are byte-identical to a `d7f1549` binary.
>
> **(v1.11) E6 is DECLARED**, item by item (evidence: `docs/implementation/slot7/WP-7_e6_dossier.md`,
> W1, W2; the close report §6). **(a) MET**: the suite green, the two E6 `slow` names by hand
> (`HeckeExtEndToEndValidation` 5271 checks, 0 failing; `HeckeAtlasValidation` 15 963, 0 failing,
> arm (K) on the Σ(691) store — which `SKIP`s without `HECKE_ATLAS_IN=<dir>`, since Σ(691) is not
> published). **(b) MET**: the §5 gate, aggregate failing 0. **(c) MET**: the first ext campaign
> published in the lead's window W2 (2026-09-23T10:57:50Z–11:21:13Z, head `c2ddbb6`, committed as
> `79b178f`): `EXT_FIRST_PUBLISH cells=505 ran=505 failed=0 wall_s=1319.2 ext_pass_s=1294.15
> peak_rss_mb=10575.8 analysis_identical=1 stores=4 atlas691_ok=1 git_clean=1 verdict=PASS`;
> `results/ext_first/` holds 505 `hecke_ext/v3` records, `index.json`, `summary.tsv`,
> `analysis.txt` and the four `ell ≤ 13` atlas stores; Σ(691) (451 875 793 bytes, FNV
> `0x73c7210047a81b97`) is recorded by size, hash and build command only (owner amendment to
> confirmation 14). `analysis.txt` lists 45 `u_ell_over_budget` cells, 0 `local = false` blocks,
> 0 `B' = none`, **270 `final != true` ideals** (all `sturm_heuristic`, exactly the Dickson-type
> ideals of the cell-local `proof_range`), 453 `unpredicted` entries with 0 refuted predictions,
> 0 Stage 2(3) splits, and the labels (in the record at `ell ≤ 13`, from the store at 691).
> **(d) MET** in W1 (above), W4 confirming. Delivered with E6 *cont.*, part 2 (slot-7 WP-5): Σ(691)
> — 1 002 225 systems from 1626 collected, `S_sep(691) = {5, 17, 29}`, byte-identical across two
> builds (≈ 2.6–3.2 h and ≤ 19.5 GB peak each, indicative, outside the suite via `--atlas`); the per-`ρ̄`
> tangent pairs at `ell ≤ 13` (at 691 every cuspidal system is deferred beyond `n = 1000`); and
> `ext_compare.py`.

**E7 — `D_n` and the pairing** (C-A4 = [C] `sec:contragredient`, `cl:pd`; **OQ4 DECIDED, unconditional
since v1.5**; [OD] R4). Scope: `ρ_n^∨(g) = ρ_n(adj g)^T` beside `ComputeSymmetricPowerMatrixFM` (an
`adj` on `Mat22` — today the adjugate is spelled out inline in `HeckeTauTable.cpp` and
`BarCocycleH1.cpp`, [C] `sec:contragredient` code map); the **contragredient local system** as a
second relation generator beside `GenerateSL2ZRelationsWithGroupData` (`LocalSystemSL2Z.h:63-64`)
producing the same `SimplexRelation` list with `ρ_n^∨(γ)`; the comparison map `Φ_n` of [C]
`lem:symdual` as a `FiberBlockTable` morphism; **the pairing map at three levels** — the
coefficient-level evaluation pairing over `Z` ([C] `prop:pairing`, Gram `= I`), the cochain-level
pairing on `C^•_eq(K; M_n) × C^•_eq(K; D_n)`, on the boundary (E4) and on the cone (E5), and the
cohomology-level pairings `H^t_c(M_n) × H^{2−t}(D_n)`, `H^t(∂; M_n) × H^{1−t}(∂; D_n)` as matrices in
the stored bases — with the **perfectness certificate** ([C] `cl:pd`(1)) and the **adjointness
certificate** `⟨A_c(T_p) x, y⟩ = ⟨x, A(D_n)(T_p) y⟩` ([C] `cl:pd`(2), no determinant factor; **the
acceptance gate for `X_3` at `ell ≥ 5`**, OP3 / `obl:coneexact`(vii)); the socle ↔ Loewy checks of
[E §5.1 item 5] in the form of [E Pred. 4.6] / [C] `cl:pd`(3) as `IdentityCertificate` identity 5 (v1.10: **item 7** — item 5 is Dickson `L·`, [S6] §2.5);
the `ι`-pairing sign of [C] `rmk:iotapairing` recorded; `HeckeDualityValidation` (§5); golden
objects (add-only, tier A `dim_H(D_n)^q`, `charpoly_A(D_n)(T_p)^q`, `pairing_perfect^t`,
`pd_adjoint^t`; tier B `pairing_matrix^t`); the console types `ContragredientLocalSystem`,
`Pairing` and verbs `dual`, `pairing` (§7). Everything integral (R2): the pairing on `Sym^n × D_n`
is the perfect one over `Z`, its reduction commutes with E8's coefficient-change maps
([C] `prop:pairing`(2)). Gate: E2 (the record and the Loewy / socle data), E4a/E4b (boundary
pairing), E5 core (the `H_c` pairing and the PD gate). Acceptance: (a) `0`; (b) `cl:pd`(1)–(2) hold
on the E2 case list at `ell ≥ 5` — a failure is a **finding** about [C]'s OPEN claim, reported to
the owner, never worked around; (c) the PD gate discharges `obl:coneexact`(vii)'s "recorded as
unavailable" into asserted. **1.25 AU, ≈ 2.0 k lines** (v1.4: 1.0 / 1.5 k as "predictions only";
the extra 0.25 is the pairing map at three levels with its two certificates — the "plus the
pairing-map work" of [OD §OQ4]).

> **(v1.10) E7a and E7b are DONE; E7 acceptance is slot 7's.** Slot-6 WP-1 (E7a): `Mat22::adj`,
> `ComputeContragredientPowerMatrixFM` = `ρ_n(adj ·)^T` with the dispatcher `ComputeFibreMatrixFM`,
> `GenerateSL2ZContragredientRelationsWithGroupData`, `HeckeOperatorOnK`'s `FibreRepresentation`
> argument (default `SymN` = the pre-slot-6 operator byte for byte), `Hecke/HeckeContragredient`
> (`Φ_n`, the coefficient pairing); `HeckeDualityValidation` asserts the intertwining
> **untwisted** — exponent 0, as `lem:symdual` gives it — with the `p^{±n}`-twisted relations
> failing on 20 non-vacuous `(cell, p, q)`. Slot-6 WP-3 (E7b, (a/s), **accepted**):
> `Hecke/HeckePairing` — the relative fundamental 2-chain, the cone-level and circle pairings,
> `PairingCertificate`, `PairingAdjoint`; `cl:pd`(1) perfect on 60 / 60 cone and 40 / 40 circle
> pairings, (2) the PD gate on 160 pairs, failing 0 (**acceptance (c) discharged**:
> `obl:coneexact`(vii)'s third sentence is asserted), (3) socle ↔ Loewy as certificate **item 7**,
> 19 / 19; the `ι`-pairing sign recorded, `−(−1)^n` on 21 / 21. **(b) holds on every computed
> cell** — no finding against [C]'s OPEN claim. The golden objects are defined and **not emitted**
> ([OD] S6-3: a separate add-only emission at E7 acceptance). Not done: the console types
> `ContragredientLocalSystem` / `Pairing` and verbs `dual` / `pairing` (C4 / C5).
>
> **(v1.11) E7 is ACCEPTED** (slot-7 WP-1). (a) green. **(b) holds on the whole E2 case list at
> `ell ≥ 5`, coverage stated**: 54 cells — E7b's 20, `HeckeDualityValidation` arm A16's 34 (the 29
> ext-subgrid cells E7b did not cover and the M1 cells `(8, 7)`, `(12, 11)`, `(34, 5)`, `(26, 7)`,
> `(32, 131)`; 102 / 102 cone and 68 / 68 circle pairs perfect, 272 PD-gate pairs failing 0,
> 106 / 106 twisted controls rejected), `HeckeDualityCoverageSlowValidation`'s 3 (`(58, 7)`,
> `(58, 5)`, `(82, 7)`, `slow`, ≈ 28 s), and `(160, 691)` / `(198, 691)` read-only under
> `HECKE_DUALITY_COVERAGE_LARGE=1` (40 gate pairs, 0 failing; ≈ 6 min, not in any tier). No
> failure, so no finding against [C]'s OPEN `cl:pd`, which stays OPEN (a test, not a proof).
> (c) discharged in slot 6. **The add-only emission is made** (stage 0, R1 `596a47b`): 651 entries
> on the 31 ext-subgrid cells at `p ∈ {2, 3, 5}` under the point suffix ` e7` —
> `charpoly_A_Dn(T_p)^q` 279, `dim_H_Dn^q` 93, `pairing_perfect^q` 93, `pd_adjoint^q` 93 (tier A),
> `pairing_matrix^q` 93 (tier B); `pairing_perfect^t = pd_adjoint^t = 1` on 93 / 93;
> `golden_explain.py` exit 0 with no flags. The console types remain C4 / C5's (slot 8).

**E8 — `Z/ell^k` coefficient rings** (new in v1.5; **OQ18 DECIDED**, [OD §OQ18], R2; the first extent of
§0.3). Scope, in order:
1. **The `ENGINE_API.md` section first** — a new **§13 "Composite modulus and non-field
   elimination"** of `ModArithmetic/ModArithmetic/ENGINE_API.md`, written and reviewed *before* any
   kernel is touched, stating: (i) `ModCtx<Elt>::prime_power(ell, k)` as a **declared** ring
   (`is_field() == false`, `ell`, `k`, `ell^k = p`); the existing `ModCtx(p)` constructor and every
   kernel of §3–§6 are **unchanged** — Barrett / Shoup / Montgomery reduction and the `k_max`
   overflow bound of §5 are statements about the *modulus* `p = ell^k` and carry over verbatim
   (so GEMM / GEMV / TRMM / transpose and the whole tape need no change), while `inv`, `batch_inv`,
   `pow`-by-negative and every §8 elimination primitive are **field-only** and `ENGINE_CHECK` on a
   composite context; (ii) the arithmetic a composite context adds: `valuation(x)` (the `ell`-adic
   valuation, `0 ≤ v ≤ k`, `v = k` for `0`), `unit_part(x)` with `x = ell^v · u`, `inv` defined on
   units only (`std::runtime_error` otherwise, like `mod_inv(0)`), `divide_exact(x, ell^v)`;
   (iii) **non-field elimination** `engine::elim::howell(ctx, A)` — the Howell form over `Z/ell^k`
   (the unique canonical form that plays the role of the RREF: row-echelon with pivots `ell^{v}`,
   `v` minimal in the column, entries above a pivot reduced modulo `ell^{v}`, and the *Howell
   closure* rows `ell^{k−v}·row` added so that every row of the row space with a given leading
   column is generated) with **valuation pivoting** (the leftmost column, then the row of minimal
   valuation, then the topmost such row — the legacy rule with valuation as the first key), and
   the derived `kernel_module`, `image_module`, `solve_multi_rhs` (exact, over `Z/ell^k`),
   `invariant_factors` (the Smith-type lengths `k_1 ≥ k_2 ≥ …` of a submodule, from the Howell form
   of the row space); every result is a **unique function of the input**, stated with the rule, so
   the bit-identity discipline of §8 applies; (iv) the **bit-identity guarantee of the `F_ell`
   path**: the composite path is selected by `ctx.is_field()` alone, the field path is untouched
   byte for byte (R21), asserted by the whole existing suite and `cross_config.sh` on the E8 tree;
   (v) the CUDA layer (§11) is **not** extended (the ext layer and the elimination are CPU;
   `gemm` over a composite modulus already works because it is modulus-only); (vi) the oracle
   `engine::ref::howell` (naive, `RefLinAlg`) and the validation `HeckeReductionValidation`'s
   elimination arms. **0.25 AU** (the document and its review).
2. `ModCtx` composite context, `valuation`, units, the `ENGINE_CHECK`s on the field-only
   primitives, and `ModContextValidation` arms; the Howell elimination in `engine::elim` on
   `DenseView`, `kernel_module` / `image_module` / `solve_multi_rhs` / `invariant_factors`, against
   `ref::howell`; **0.75 AU**.
3. `EquivariantCohomologyOnK` over `Z/ell^k`: the `A_Cq` / `A_Zq` assembly is modulus-only
   (unchanged); `C_eq`, `Z_eq`, `B_eq`, `H_eq` by the Howell-form `kernel_module` /
   `image_module` / `factor_basis` with **length** bookkeeping in place of dimensions; `H_eq` as
   `Z_eq / B_eq` presented by its invariant factors and a basis of each cyclic summand; `P_q`
   accordingly; `coefficient_ring` in the record; `HeckeOperatorOnK` over `Z/ell^k` needs nothing
   (the `Θ` assembly is modulus-only; `Θ_eq`'s certification solve becomes a Howell solve);
   `A^{(q)}(T_p)` over `Z/ell^k` as a matrix on the cyclic summands; **0.5 AU**.
4. **The functorialities**: the reduction map `Z/ell^{k+1} → Z/ell^k` on cochains (entrywise) and
   on cohomology (in the stored bases, a `HeckeReduction` object), the **Bockstein**
   `β: H^q(F_ell) → H^{q+1}(F_ell)` of `0 → Z/ell → Z/ell² → Z/ell → 0` (`a = b = 1`) from the
   stored bases, both with **Hecke-equivariance certificates** (`A(T_p) ∘ red = red ∘ A(T_p)`,
   `β ∘ A(T_p) = A(T_p) ∘ β`, asserted at `ell ≥ 5` — on the nose, since the tables are integral,
   C-A3(ii.6) / [V §6.2]) and the exactness of the coefficient long exact sequence with length
   bookkeeping; on the boundary and the cone once E4b / E5 exist (`obl:coneexact`(iv)'s "over
   `Z/ell^e` by a solve exhibiting each kernel generator as an image" becomes checkable here —
   until then [C] records the non-field case as unchecked); the **D6 refinement**: over `Z/ell²`
   the integral Eisenstein and cuspidal eigenlines at `(10, 691)` separate, recorded as the
   refinement of the Eisenstein line, while the *published* semantics stays `soc(X⁺_{4,m})`
   (confirmation 9(a)); `HeckeReductionValidation` (§5); the campaign key `coefficient_ring`
   (§1.5); golden objects add-only at `(10, 691)`, `(6, 5)`, `(16, 5)` over `Z/ell²` (tier A
   `lengths_H^q`, `charpoly_A(T_p)^q` over `Z/ell²`, `bockstein_rank^q`; tier B the reduction
   matrices); **0.5 AU**.
Gate: E2 (the record); the boundary / cone halves of item 4 after E4b / E5. Explicitly **not** in E8
("do not push far in this direction now"): general `(a, b)`, the `ell`-adic spectral sequence
pages, a general `Z/n`, the CUDA layer, `uint64_t`-only moduli beyond `ell² < 2^64`. Acceptance:
(a) `0`; (b) the standing golden gate and `--all` green on `RelWithDebInfo` and `Check` **before
and after** each of items 2–4 (the `F_ell` path is untouched); (c) `cross_config.sh RelWithDebInfo
Bench Check RelWithDebInfo+HECKE_PURE_INTEGER=ON RelWithDebInfo@ENGINE_BACKEND=legacy --validations
HeckeReductionValidation,ModContextValidation` green; (d) the Bockstein and reduction equivariance
asserted on the E2 case list. **2.0 AU, ≈ 3.5 k lines.** Preferred over a general `Z/n` because a
prime-power modulus keeps every reduction primitive and needs only valuation pivoting (the owner's
"if `Z/ell^k` allows higher performance than a generic modulus `n`, go for `ell^k`").

> **(v1.11) Item 1 is DONE and reviewed** (slot-7 WP-9 `e9ec5d4`, `ENGINE_API.md` §13; WP-10
> `82b9e59`, `docs/implementation/slot7/WP-10_review.md`: **ACCEPT**, 0 blocking / 3 major /
> 11 minor, three pointer repairs applied). The review's findings amend items 1–4 as follows —
> **binding for items 2–4**; the text of items 1–4 above is kept as v1.10's record:
>
> * **F1 — `inv` is unit-only, not field-only.** Item 1 (i)'s field-only list is `batch_inv`,
>   `pow` by an exponent `≥ p − 1` (the reduction mod `p − 1` is a no-op below it; §13.3 guards it
>   wholesale), and every §8 elimination primitive; `inv` is **defined on units** (the extended
>   Euclid of `mod_inv_w`, which throws on a non-unit), as (ii) already says.
> * **F2 — invariant factors need a Smith step.** Item 1 (iii)'s `invariant_factors` is **not**
>   read off the Howell form's pivot valuations (`rowspan[[2, 1]] ≅ Z/4` over `Z/4` has pivot
>   valuations `(1, 1)`); it is §13.6's Smith rule (minimal-valuation pivoting over the local
>   principal ideal ring, the diagonal sorted to `e_1 ≥ e_2 ≥ …`).
> * **M1 — the `invariant_factors` arm** of `HeckeReductionValidation` uses the **`2 × 1` column
>   `[[2], [1]]`** over `Z/4` (the column module is §13.6's convention; `[[2, 1]]`'s column span
>   contains the unit `1` and would pass a wrong implementation), with the negative assertion that
>   its Howell pivot valuations are `(1, 1)`.
> * **F3 — reductions compare as modules and maps, not as bases.** Item 4: the **cochain-level**
>   matrices (the differentials, `Θ`) reduce entrywise; on cohomology the reduction
>   `H^q(Z/ell^k) ⊗ F_ell → H^q(F_ell)` is injective with a Tor cokernel (universal coefficients),
>   so "`A(T_p)` over `Z/ell²` reduces to the `F_ell` matrix" fails even up to a change of basis;
>   the certificates are the map equalities `A(T_p) ∘ red = red ∘ A(T_p)` and
>   `β ∘ A(T_p) = A(T_p) ∘ β`, as item 4 writes them.
> * **F4 / M2 — `ρ_n` over `Z/ell^k`: an IMPLEMENTATION limit, not a mathematical one** (owner
>   wording, 2026-09-23). `ρ_n(g)` has **integer** entries — sums of products of binomial
>   coefficients — and reduces mod `ell^k` like any integer matrix. The current builder,
>   `ComputeSymmetricPowerMatrixFM` (`FlatMatrix.cpp` ≈ 1934, 2015, 2030; the recurrences at
>   ≈ 2041, 2072), computes the binomials **mod `p`** through Lucas's theorem with factorial /
>   inverse-factorial tables, and **divides** by the entry `a` (resp. `b`) in the [R1] / [R2]
>   branches — both valid only when `p` is prime. On a bare `ell^k` it **throws** (a non-unit
>   factorial or pivot), never returning a wrong value. **Item 3 therefore builds `ρ_n` over `Z`**
>   (from the exact `Mat22`, reduced mod `ell^k`) **or by a Pascal-only, division-free route**
>   (`mod_nCr_small`'s `n ≥ p` fallback is exact for any modulus). Two of the three E8 golden cells,
>   `(6, 5)` and `(16, 5)`, have `n ≥ ell` and need it.
> * **M3 — the cyclic-summand bases need a rule before tier B.** Item 3 adopts: the full Smith
>   elimination with §13.6 step 2's pivot rule, the row cleared first and the column second, each by
>   the `divide_exact` quotient, no normalisation beyond scaling the pivot to `ell^σ`; the basis of
>   each cyclic summand = the images of the Howell generators of `N` under the accumulated column
>   transform — a deterministic function of the input matrices `(G, Rl)`, as the D5b bases are.
> * **m11 — two entry points adopted**: `solve_multi_rhs_module` (an overload of
>   `solve_multi_rhs`'s signature would dispatch on `is_field()`, which §13.8 forbids) and
>   `length` (the bookkeeping item 3 already requires). The remaining minor findings (m1–m10, m12,
>   m13) are §13 wording for item 2's author.
>
> **E8's strategy: the investigation is delivered, its recommendations are PENDING OWNER.** A
> Fable investigation (the owner's rule since slot 7: audits and reviews run on Fable) compared
> direct elimination over `Z/ell^k`, `ell`-adic induction `ell^{k−1} → ell^k` through the
> coefficient long exact sequence / the cone, and an integer / `Z_(ell)` route:
> `docs/implementation/e8_ladic_investigation.md` with the exact probe
> `docs/implementation/e8_ladic_probe.py` (`cbc60be`, merged `c9829a9`, documents only). Its
> findings, in one line each: the engine's arithmetic is modulus-only, so a word-sized `Z/ell^k`
> costs what `F_ell` costs in the same width regime (the u32 delayed regime below `2^30.5`); an
> inductive scheme cannot be "mod `ell` only" (the Bockstein data are lifts mod `ell^k`), and
> §13's valuation-pivoting Howell elimination already *is* the induction in one pass; "over `Z`
> once" is excluded by the `ρ_n` entry sizes (`C(n, n/2) ≈ 2^124` at `n = 128`) and invariant I5;
> the model has `ell²`-torsion in `H^1(Γ; Sym^n Z²)` at `n = ell · m`, `m` a Dickson degree
> (`(30, 5)`, `(56, 7)`; `Z/125 ⊕ Z/5 ⊕ Z/5` at `(150, 5)`). **Its recommendations, recorded here
> as proposals — NOT owner-ruled; each is pending the owner's decision before item 2 starts:**
>
> 1. **Build E8 direct, as §13 specifies** (proposal E8-P1): Howell / Smith elimination over a
>    word-sized `Z/ell^k` — `uint32_t` for `ell^k < 2^32`, `uint64_t` below `2^63` — the `F_ell`
>    path untouched. Below `2^30.5` it costs the same as `F_ell`; u64 covers every E8 use to
>    `2^63` (`Z/5^27`, `Z/691^6`, `Z/134217757^2`).
> 2. **The certified `K`-mode** (E8-P2, item 3): under `coefficient_ring = Z/ell^k`, also report
>    the `Z_(ell)`-type `(r_q, e^q_1 ≥ e^q_2 ≥ …)` of every `H^q` when the count certificate holds
>    (`r_K(d^0) = dim C^0_eq`, `r_K(d^1) = dim C^2_eq`), else `ladic_type_certified = false` with
>    the two counts (resumable, R3); **and the check `bockstein_rank^0 == dim H^0(F_ell)`**
>    (⇔ no `Z/ell^{≥2}` summand), recording **`higher_torsion_count = dim H^0(F_ell) −
>    bockstein_rank^0`**, asserted equal to `#{e_i ≥ 2}` wherever the `K`-mode certifies (item 4).
> 3. **Positive controls `(30, 5)` and `(60, 5)`** (E8-P3, F-B): they carry `Z/ell²` torsion at
>    `n = ell · m` (`(30, 5)`: `Z/25`; `(60, 5)`: `Z/25 ⊕ Z/5`, `higher_torsion_count = 1`). All
>    three E8 cells planned above — `(10, 691)`, `(6, 5)`, `(16, 5)` — have `e_max ≤ 1` and so
>    cannot see the phenomenon; both controls are u32 at every `k ≤ 13`.
> 4. **`charpoly` over `Z/ell^k` defined on the free quotient** (E8-P4, F-C; joins M3):
>    `charpoly_A(T_p)^q` over `Z/ell^k` is not an invariant of a non-free module, so it is defined
>    on `H^q(Z/ell^{k + e_max}) / (ell^{e_max}`-torsion`)`, or a basis rule is stated; the lengths
>    and invariant factors stay the tier-A objects.
> 5. **The `ρ_n` repair** (E8-P5, refining F4 / M2 above): a **unit fast path** (the [R1] / [R2]
>    recurrences are exact whenever the divisor is a unit; the branch test becomes
>    `valuation(a) == 0`), a **division-free Pascal oracle** (`entry(i, j) = Σ_t C(j, t) C(n−j,
>    i−t) b^t d^{j−t} a^{n−j−i+t} c^{i−t}` over a Pascal table mod `ell^k`, `O(d_V³)`, the
>    fallback and the fast path's validation oracle), and a **`diag(ell, 1)` split for `U_ell`**
>    (`g = diag(ell, 1) · g'`, `ρ_n(diag)` diagonal, `O(d_V²)`); `mod_nCr` over a composite
>    modulus never consults the thread-local factorial table.
> 6. **The `ell`-adic induction (C2) — a DEFERRED FUTURE REQUIREMENT (arbitrary `k`, Hida),
>    design recorded** (E8-P6, **restated by the owner direction of 2026-09-23**; the
>    investigation proposed it as a non-goal, which the owner **rejected**). The owner will want
>    `mod ell^k` for **arbitrarily large `k`**: for the descent of the integral line (below) and
>    for `ell`-adic modular forms (Hida families and their generalisations). So (C2) — base
>    `ell^m` with `m` word-maximal, `⌈k/m⌉` word-sized levels, the residuals as digit-convolution
>    GEMMs, per-level valuation pivoting with look-ahead (`e8_ladic_investigation.md` §4.3, §5.2) —
>    is **not** a non-goal: its design is recorded here, it is not built in E8, and it is a
>    **slot-8+ line item** (§8), with E8's direct word-sized route (P1) as its oracle. Whether
>    the investigation's `ell^k ≥ 2^63` remains the trigger or it is built on demand is the owner's.
>
> **(v1.11) Owner direction, 2026-09-23 — TWO computational lines, kept live in ONE tree.**
> **Line 1** computes **truly mod `ell^k`** wherever `ell^k` fits a machine word, for **all**
> arithmetic including the Hecke action; E8 builds on it (P1 is that line's first step).
> **Line 2** is **true integral computation over `Z`**. The owner's idea for line 2: `Z[1/6]` on
> the current model, plus `Z_2` and `Z_3` on a finer honest orbifold model, glued by descent, with
> the Hecke action over `Z` at the end. Its design brief,
> `docs/implementation/integral_line_design_brief.md`, is **being written** and will then be
> audited on Fable; **this plan does not pre-empt it** — it is referenced as incoming, and line 2's
> phases, gates and its relation to C-A5 / E9 (the finer model) are whatever the brief and the
> owner fix. The investigation's finding that "over `Z` once" is excluded by the `ρ_n` entry
> sizes and invariant I5 (F-D) concerns a single integral elimination on the present
> representation; it is an input to the brief, not a ruling on line 2.
>
> The investigation's other findings — F-A (a remark on the torsion exponents for [C]
> `cl:bockstein`), F-D (the integral option's entry sizes), F-E (the CPU u64 GEMM, 1.2 G vs
> 27 G modmac/s, an engine item) — are recorded for the owner with the proposals. Items 2–4 above
> stand as v1.10 wrote them until the owner rules.

> **(v1.12) The owner ruled (2026-09-24, [OD] S8-2 … S8-5): P1–P5 adopted, item 4 split. E8 is
> declared item by item:**
>
> * **Item 1 — DONE** (slot 7; reviewed). Its pointers were repaired at the slot-8 close
>   (WP-12 pass 1, m-1 … m-3).
> * **Item 2 — ACCEPTED** (slot-8 WP-1, `9e02013`, merged `3ab190f`): the composite `ModCtx`
>   (`prime_power`, `valuation`, `unit_part`, `divide_exact`, the `ell^v` table; 208 / 608 bytes),
>   the §13.3 guards, the §13.7 replay check, `elim::howell`, `kernel_module`, `image_module`,
>   `solve_multi_rhs_module`, `length`, `invariant_factors` by §13.6's Smith step, `ref::howell`;
>   M1's arm on the column `[[2], [1]]`. Acceptance (a) `HeckeReductionValidation` 0 failing;
>   (b) golden 0 / 0 and `--all` green before and after; (c) `cross_config.sh` with
>   `HeckeReductionValidation,ModContextValidation` PASS, checksums equal to R0's.
> * **Item 3 — ACCEPTED** (slot-8 WP-3 `9071ab0`, merged `99877a6`; `06bebdc`; WP-3r `28fdb73`,
>   merged `5d0b867`): the module routes of `EquivariantCohomologyOnK` and `HeckeOperatorOnK` over
>   `Z/ell^k` (`C^q = kernel_module(A_Cq)` asserted free, `X_q` by `solve_multi_rhs_module`,
>   `H^q = cyclic_decomposition(Z^q, B^q)` in `C^q_eq` coordinates, the certified `K`-mode — P2 —
>   with `ladic_type^q` against the invariant factors by universal coefficients, `Θ` fused and
>   route 2 asserted equal over the ring); **P5** `ComputeSymmetricPowerMatrixRing` (unit
>   recurrences, a division-free Pascal route, the `diag(ell, 1)` split for `U_ell`); **M3**'s basis
>   rule ([E] `sec:ring` (c1)–(c5)); **P4** `charpoly` on the free quotient at certified levels only,
>   over `Z/ell^{K − e_max}`; §13.7's `ModCtx` overload; `coefficient_ring` with its refusal closure
>   ([E] `sec:ring` (b1), 36 members). **Wording repairs to items 1–3, binding**: item 1 (i)'s
>   field-only list drops `inv` (F1); item 3's "`kernel_module` / `image_module` / `factor_basis`"
>   is §13.6's `invariant_factors` plus M3's rule (`blk::` / `tape::factor_basis` declare a field
>   by their signature, §13.3); M1's arm is stated in §13.6's column convention; the entry points
>   `solve_multi_rhs_module` and `length` are adopted (m11); `elim::howell` stays scalar. The Fable
>   review (WP-12) disposed of: pass 2's M-1 (a direct arm on the basis rule, `H_class_coordinates
>   = I` per cell and level) and M-2 (the `int64_t` cast on the `U64_Wide` half, a `(10,
>   4294967291)` cell) repaired by WP-3r, m-6 (a composite local system under `F_ell` refused) and
>   m-7 (D6's `(x − 2049)(x + 24)²` asserted) as well.
> * **Item 4a — ACCEPTED (a/s)** (slot-8 WP-4 `d96d89d`, R1 at `53a1909`): `Hecke/HeckeReduction` —
>   `red_H^q` and the Bockstein as **map equalities** (F3), Hecke-equivariance asserted at
>   `ell ≥ 5`; `bockstein_rank^0 + higher_torsion_count == dim H^0(F_ell)` on every stated cell,
>   `higher_torsion_count` `0` at `(10, 691)`, `(6, 5)`, `(16, 5)` and `1` at `(30, 5)`, `(60, 5)`,
>   `== #{e_i ≥ 2}` wherever the `K`-mode certifies; **P3 exact** (`(30, 5)`: `Z/25`; `(60, 5)`:
>   `Z/25 ⊕ Z/5`); the D6 refinement as a validation arm (the 1 + 2 split asserted, the index 691
>   recorded); acceptance (d) on the bulk over the E2 case list at `ell ≥ 5` where `Z/ell²` is
>   admitted (`HeckeReductionCoverageSlowValidation`, `slow`; `(160, 691)`, `(198, 691)` under
>   `HECKE_REDUCTION_COVERAGE_LARGE=1`); the golden objects add-only at the seven `E8 ring=…`
>   points (R1: +124, A 103 / B 21).
> * **Item 4b — slot 9** ([OD] S8-3): the boundary and the cone over `Z/ell^k`, `obl:coneexact`(iv)'s
>   non-field half (still recorded as unchecked in [C]), ≈ 0.35 AU. Gate: items 2–4a (met), E4b / E5
>   (met).
> * **Not in E8** (unchanged): general `(a, b)`, a general `Z/n`, the CUDA layer. **(C2)** stays a
>   deferred requirement with its trigger ([IB] OD-6 (a): a `u128` element type, L1-X, when a family
>   computation needs it).

> **(v1.13) E8 is COMPLETE AS SPECIFIED: "4b by route 1; (vii) over the ring open"** ([OD] S9-3,
> [E] v1.10.1 `sec:ring` (f); the declaration's long form is [E]'s status paragraph):
>
> * **Item 4b — ACCEPTED** (slot-9 WP-4 `d0aca96`, merged `8c9faf4`; WP-14 pass 1 repairs
>   `2933b65`, `7ddb555`; R1 `762dbc3`; trimmed by WP-4t `45acc4f`): at `ell ≥ 5` the boundary
>   complex and `Cone(r)` over `Z/ell^k` through the dense module route (`ModuleConeT`, templated
>   over the three word regimes; the four classes `uint32_t`-instantiated); `ConeModuleCertificate`
>   item 14 discharges [C] `obl:coneexact`(iv)'s **non-field half** (every Howell generator of
>   `ker(out)` exhibited as an image by a solve, the witnesses re-derived by `verify()`); the cone's
>   long exact sequence exact with length bookkeeping (`cone_les_im_lengths`); the reductions and the
>   Bockstein on the boundary and the cone as map equalities, Hecke-equivariant; (vi) partial — the
>   commutator asserted, the `ν = 2` recursion not computed over the ring. Every [E] (f) prediction
>   held (`m = 1` at `(16, 5)`). The refusal closure re-derived by grep, template spellings included
>   (guard sites in 28 files, construction sites in 13 TUs; (X4b) 21 rows).
> * **`obl:coneexact`(vii) over `Z/ell^k` — OPEN** (ruling 3 (iii) (A)): `HeckeConeStrictPairRoute`,
>   `HeckeConeRelativeRoute` and the relative sub-complex constructor refuse the ring, each with an
>   arm. Slot 10's re-cut carries alternative (B).
> * **Item 3 at `ell ∈ {2, 3}` — ACCEPTED** (slot-9 WP-3; [OD] S9-4): the Bredon object by the
>   flat-coordinate module route, lengths and invariant factors only, against O7 (96 cells); the
>   `K`-mode, `HeckeOperatorOnK` and `HeckeReduction` refuse there by name.
> * **Campaign and console** (C5c, C5a): the ring reaches the campaign job loop
>   (`hecke_ring_report/v1`) and the console's `symmetric_power` / `cohomology` / `hecke(H, p)` at
>   `ell ≥ 5`; 4b stays console-unreachable (the C5b verbs refuse a non-default ring).
> * **Not in E8** (unchanged): general `(a, b)`, a general `Z/n`, the CUDA layer; (C2) with its
>   trigger (not fired).

> **(v1.14) E8 is COMPLETE** ([OD] S10-3, [E] v1.11.0 `sec:ring` (b1) / (f), [C] v1.10.0
> `obl:coneexact`(vii) as built): **`obl:coneexact`(vii) sentences 1–2 over `Z/ell^k` — DISCHARGED**
> at `ell ≥ 5`, `ell^k < 2^32`, at every E8 point (slot-10 WP-3 `a4abc39`, merged `c9684e9`; review
> WP-14 pass 1 accepted; m-12's asserts in WP-8): `HeckeConeStrictPairRoute` (`Θ^s` by the honouring
> `HeckeOperatorOnK` on the `BoundaryStrict` table, `η^s = 0`, `A^s_c` by route 1 on `ModuleConeT`'s
> generators), `HeckeConeRelativeRoute` (the relative sub-complex constructor's module route, `M`
> and an explicit `N` with `M N = N M = I`, no inverse over the ring) give `A_c` entrywise equal to
> route 1's in every degree; above `2^32` they refuse by the ring context's named uint32 regime
> refusal; at `ell ∈ {2, 3}` all three members refuse by name; `HeckeConeCrossRouteRingValidation`
> (431 checks). **Sentence 3** (the PD adjointness gate) is **recorded unavailable over the ring**
> (the pairing and the contragredient refuse a composite ring; WP-14 M-1). The v1.13 note's "(vii)
> over the ring open" is superseded.

> **(v1.12) E9 is ABSORBED INTO LINE 2** ([OD] S8-6c, [IB] OD-7 (a) / OD-8 (a)). C-A5 is discharged
> by [C] v1.8.0 `sec:integral` on the **unrefined** `Xbulk` (§0.4), so there is no refinement and
> no second model descriptor for one. Items 1–2 become **L2-1a** (`R`, `R_∂`, `ε` on `Xbulk`,
> degree-generic to `q_max + 1`, ranks `5, 14, 19` per `n + 1`; value-preserving on the 7-vertex
> model); item 3 (the truncated pair under `open:ell2`, `q_max` set) goes into **L2-3**; item 4's
> tests are re-hosted (§5's `HeckeFreeModelValidation` row). E9's 2.5 AU are absorbed by line 2's
> ≈ 5.0 AU core (net ≈ 2.5 AU over v1.11). The text below is v1.10's, kept as the record; R20
> is retired.

**E9 — The free `Γ`-model** (new in v1.5; **OP4** / **OC-1** `oc1a` / **OD-T1**; [C]
`sec:orbifoldmodel`, `open:ell2`; the host of [R §5]'s six tests). **Contract prerequisite C-A5**
(§0.4): a chapter, by a contract author, fixing the **concrete refinement** of the 7-vertex
triangulation that OD-T1 expects ("a refinement of the current triangulation") and a model
`(Y, ∂Y)` satisfying [C] `G1`–`G4` — stabiliser inventory, boundary, the existence of `τ`, `τ_∂`,
`η` in every degree `≤ q_max + 1` — refereed like `lem:bulkperiodic` ([R]); an `X` bump. [C]
`thm:specialisation`'s closing note says exactly what is not asserted today: "that a model
satisfying `G1`–`G4` … exists for a *refinement* of `(K, R)`, or that one can be built effectively.
That is the deferred construction." Scope, given C-A5:
1. `Orbifold_Cohomology_of_GL2/FreeGammaModel/`: the refined triangulation data (vertices, edges,
   triangles, the relation table, the stored simplex order — everything [OD] OD-T1 lists as
   "recomputed per refinement": `N_0, N_1, N_2`, `χ`, `|R|`, the orbit representatives, `lem:bounds`)
   as a **second `SimplicialModelDescriptor`** beside `SL2Z7VertexModel()`
   (`Hecke/HeckeModelDescriptor.h:69-74`; the campaign's `model` key already selects a descriptor),
   with `num_degrees() = q_max + 2` on the truncated model; **0.5 AU**.
2. The **degree-generic `τ`-table**: `HeckeTauTable`'s per-degree construction step
   (`build_triangles()` / `construct_triangle()` implement `alg:tau`(3) for `q = 2` only;
   `face_simplex_index` is an explicit `q == 1` / `q == 2` branch; 9 literal `q < 3` loop bounds
   and `records_.assign(3, {})` / `xi_.assign(3, {})` at `HeckeTauTable.cpp:330-331`; 17
   `std::array<uint8_t, 3>` vertex-permutation sites in `SL2ZTessellationTables.*` — [B §4.5]'s
   census, re-verified on `0fb142d`) generalised to degrees `≤ q_max + 1`, **value-preserving on
   the 7-vertex model** (the standing golden gate and `tau_table_p2.txt` byte-identical are the
   proof) — this is the cost [B §4.5] names as "identical under `oc1a` and `oc1b`" and attributes to
   the free model; `τ_∂` and `η` on the refined model through the same machinery (E4a / E5's
   units, degree-generic by construction); **1.0 AU**.
3. The **truncated pair** under `open:ell2`: complexes built to `q_max + 1`, cohomology reported to
   `q_max`, `q_max` **set** (rider (i): settable here and only here), `truncated = true`, the
   exactness contract of `obl:coneexact`(iv) as narrowed, `coker r^{q_max}` recorded; the Hecke
   action in every reported degree; `thm:specialisation`(4) asserted at `6 ∈ R^×` (the refined
   model reproduces the 7-vertex model's canonical objects); **0.5 AU**.
4. **The six tests of [R §5]** as `HeckeFreeModelValidation` (§5) at `ell ∈ {2, 3}`, `n = 0` and `n`
   even, `q_max ≥ 5` (both periodicity instances), including the class `e` as a cochain and
   `E_q = e ∪ −` as a matrix, and the negative control that the harness never runs them on the
   7-vertex model; golden objects add-only at `ell ∈ {2, 3}`; the record of the observed
   stabilisation for the owner's `oc1c` question ([C] `rmk:bulkperiodicscope`(3)); **0.5 AU**.
Gate: C-A5 accepted; E5 core accepted (the pair datum and the cone on which the tests run); E8 is
**not** a gate (the tests are over `F_2`, `F_3`). Nothing of E0–E8 depends on E9. Acceptance:
(a) `0`; (b) the standing golden gate on the 7-vertex model throughout (value-preserving
generalisation); (c) tests 1–5 pass on the free model at `q_max = 5`, test 6 holds; (d) the
observed `H^2 ≅ H^4`, `H^3 ≅ H^5` and the Hecke char-poly periodicity reported to the owner
together with what [R §5] said they would decide. **2.5 AU, ≈ 4.0 k lines.** Effort risk: R20.

**Effort table (v1.5; the v1.4, v1.3 and v1.2 cuts are preserved in the earlier columns and in the
totals line below).**

| Phase | v1.1 | [XA §6] | v1.3 | v1.4 | **v1.5** | lines (v1.5) | what moved it |
|---|---|---|---|---|---|---|---|
| E0 (E0a + E0b) | 1.0 | 1.25 | 1.25 | 1.25 | **1.25** (0.5 + 0.75) | 2.3 k | v1.5: E0b also carries the `locality` setting, strict mode + `LocalityState`, `HeckeSettings.h` and the oc1a fields — inside the 0.75 (three record fields and a settings struct; the strict route is linear algebra on existing primitives) |
| E1 (E1s + E1a + E1b) | 2.0 | 2.25 | 2.25 | 2.25 | **2.25** (0.5 + 1.0 + 0.75) | 4.5 k | v1.5: E1s ships `SturmState` / `resume` (inside the 0.5: WP-3 sizes it M); E1a the `CommutantState`; E1b the two `sturm.*` modes and the `u_ell` resume |
| E2 | 1.5 | 1.5 | 1.75 | 1.75 | **1.75** | 3.6 k | v1.5: the tri-state `final`, the `settings` block, `HeckePresentation` (small), E4b's golden objects in the add-only emission |
| E3 | 1.0 | 1.0 | 1.0 | 1.0 | **1.0** | 1.5 k | production `ι^* = −ρ_n(ι)` per block, agreeing entrywise with `HeckeIotaSignValidation` |
| E4 (E4a + E4b) | 1.5 | 1.5 | 1.5 | 1.5 | **1.5** (1.0 + 0.5) | 2.5 k | v1.5: split, E4a in slot 1; the model recording replaces a refusal (no cost) |
| E5 | 2.0 | 2.5–3.0 | 2.5 (+0.5 opt.) | 3.25 | **3.25** (2.5 + 0.5 + 0.25) | 5.2 k | unchanged from v1.4 (OP3 / OP8); the record fields `q_max` / `truncated` / `q_max_source` land with E0b, not here |
| E6 | 1.25 | 1.5 | 1.75 | 1.75 | **1.75** | 2.8 k | v1.5: the canonical-field default with its performance gate; `predictions = assert` in the validations only; the first ext campaign at `n ≤ 200` |
| **Six-group record (E0–E6)** | **10.25** | **≈ 11.5–12** | 12.0 (+0.5 opt.) | 12.75 | **12.75 AU** | **≈ 22.4 k** | |
| E7 `D_n` + pairing | 1.0 (opt.) | — | 1.0 (opt.) | 1.0 (opt.) | **1.25** (scheduled) | 2.0 k | OQ4: the pairing map at three levels, the perfectness and adjointness certificates, the PD gate for `X_3` |
| **E8** `Z/ell^k` | — | — | — | — | **2.0** (0.25 + 0.75 + 0.5 + 0.5) | 3.5 k | OQ18: the `ENGINE_API.md` section, the composite context and Howell elimination, the pipeline over `Z/ell^k`, the reduction maps and the `a = b = 1` Bockstein |
| **E9** free `Γ`-model | — | — | — | — | **2.5** (0.5 + 1.0 + 0.5 + 0.5) | 4.0 k | OP4 / OC-1 / OD-T1: the refined descriptor, the degree-generic tables (the cost [B §4.5] names), the truncated pair, the six [R §5] tests |
| **Total (E0–E9)** | | | | 13.75 with E7 | **18.5 AU** | **≈ 31.9 k** | |

**Total: 18.5 AU, ≈ 31.9 k lines (E0–E9).** The six-group record (E0–E5) is **11.0 AU** as in v1.4
and the deliverable of the stage; **M1 (E0–E2) is 5.25 AU** and has no contract dependency; E6
closes the record at 12.75; E7–E9 are the three phases the owner's decisions added (OQ4, OQ18, the
free model), 5.75 AU together, and none of E0–E6 waits on them (§6.1). Not in AU: the contract
author's C-A5 (§8 slot 7), the [E] and [P] consequential revisions (slot 2, [SP §5]) and WP-7's
slot-close work, which §8 schedules explicitly.

### 6.3 Risk table

| # | Risk | L / I | Mitigation |
|---|---|---|---|
| R1 | **Memory at large `n`**: peak RSS `≈ n²` (`1.4 GB` at `n = 1000`, CLAUDE.md), and a Sturm sweep needs one pipeline per prime `≤ B'(k, ell)` (typically 2–7; up to `π(12·B(k))` only if the closure is slow). **OQ12 (v1.5):** `n ≤ 1000` is the reference machine's bound, not a design limit — the target hardware includes HPC nodes; the layer's memory scales with one pipeline per node (the campaign's `jobs × threads` split already is that) and, for the pipeline itself, with the device memory the tape's residency pass manages (`ENGINE_API.md` §12.2) — no ext-layer object is ever larger than `D²` | certain / high | streaming Sturm driver (§2.2 4(c)): one pipeline alive at a time, lean + no `Θ_eq`, only the `D×D` restrictions kept; primes already in `S_0` reused from the family cache, only `q ∉ S_0` streamed ([XA m12]); `HeckeOperatorFamily`'s non-evicting cache (`:271`) is not used for streamed primes; the cohomology is computed **once per cell** and each extra prime costs cosets + τ + Θ (`HeckeOperatorFamily.h:112-113`; v1.1's "a full `cohom` per prime" misread [E Stage 1], [XA M4]) |
| R2 | **Cross-check blow-up**: `HeckeCrossChecks` builds fibre dimension `(p+1)(n+1)`; `hecke 10 691 691 --cross-checks` reached 14 GB and never finished ([I §2.6]) | certain if used / high | the engine never calls it; `certify = sampled` in campaigns. (The `U_ell` cost that v1.1 filed here — "≈ 1 GB at `(16, 43867)`" — was wrong by ≈ 5×; it is now R14.) |
| R3 | **Wildness of the classification**: for embdim `≥ 2`, Loewy length `≥ 3` no finite invariant list determines the module | certain / medium | the deliverable is the record (D1)–(D7), [Q11]; the record *exhibits* the modules (bases, structure-map matrices) so any finer invariant can be computed later from the emitted data |
| R4 | **Cone Hecke action needs a homotopy** (OQ2, **answered**): `Θ_g` and `Θ_g^∂` commute with `r^•` only up to homotopy, and the shipped `τ` is not a map of pairs (`tau_table_p2.txt:13-15,35`) | **medium / medium** (re-rated 2026-09-15 per [V §7] item 8; was high/high) | **The well-definedness risk is eliminated by theorem**: `h := η̃` is derived from a certified pair homotopy, and the operator on `H^•_c` is independent of `η` over `Z` for every `ell` ([V §2.4]–[V §2.5], PROVED), of `(τ, τ_∂)`, of the `s_i` and of `g` for `6 ∈ R^×` ([V §2.6]) — C-A3(ii.5). The residual risks are (i) **integrality of the fills** (int64 overflow forcing the mod-`m` fallback — now *forbidden by default* by owner decision OP2, so the mitigation is the widened integer tier, with the knob and the recorded `solve_regime` as the fallback of last resort, §1.2), (ii) **the boundary at `ell = 2`**: OP5 decides the boundary group is `Γ_∞ = ⟨T⟩ × ⟨−I⟩`, so the circle model is the `2 ∈ R^×` specialisation and **at `ell = 2` the boundary, the bulk and the cone are all unbounded above in degree** — the risk is no longer "which group?" but the construction item **OC-1** (the truncation policy, §0.4 C-A2(i)) — its *policy* **decided 2026-09-16** (`oc1a`, [C] v1.3.0 `open:ell2`, [OD §OC-1]), its *construction* **scheduled as E9** (slots 8–9, behind C-A5); the standing mitigation is §1.2's degree-generic data model, which nothing in E4/E5 may bypass, and E9's value-preserving generalisation of `HeckeTauTable` is gated on the golden reference, (iii) **an `η`-table whose certificate fails** — a bug in the (T1) helper, not a mathematical risk. E5 is still the last phase, so nothing else waits on it |
| R5 | **Golden re-baseline discipline**: E0 moves `≈ 2 × #cells` text hashes | certain / medium | §1.6 protocol, split E0a (dump on a value-identical binary) / E0b (fix); `golden_explain.py` checks the text allow-list **and** fails on any change to the inputs of `_invariants`, `_certify`, `_witness`, `_U` outside owner-accepted splits; all four hashes proved unmoved on local grids (§3.3) and asserted by E0a's grid arm |
| R6 | **`Matrix`-layer cost at `n → 1000`**: Berkowitz `O(D⁴)` at `D = 170`, `≈ 5` operators × `≈ 4` charpolys, plus `k` nilpotency checks and the `ŵ` powers | medium / medium | E1 acceptance (d) measures it; fallback (unscheduled): route `CharPolyBerkowitz` / `EvalPolyAtMatrix` products through `FlatMatrix` kernels — bit-identical by construction — or `MinPolyKrylov` where only the minpoly is needed |
| R7 | **Commutant (b) infeasible or useless at large `D`**: naive `O(k·D⁶)`; the structured system on `End_{F_ell[a]}(V)` has `u ≤ m·D` unknowns and degenerates to `D²` when `m ≈ D` | certain / medium | the socle bound (§2.2 4(b)) excludes (b) — as a proof — on every Gorenstein `A_S` and every field, i.e. on all the pinned cases; where it is admitted, a fixed cyclic-most element and a modmul budget (`over_budget` recorded, never a naive fallback); (c) is the route for the dominant `m` at `n ≫ ell`; naive kept as a `D ≤ 24` oracle only ([XA B2]) |
| R8 | **Small `ell` starves the witness / `P_p` search** (`ell = 5`: `≤ 4` nonzero coefficients per term; linear witnesses are only guaranteed when `f` has `≤ ell` distinct prime factors and `min(f, f') ≤ ell`, [E Cert. 5.2]) | low / low | the bounded loop (64 attempts, [E Alg. 5.1(2)]) and the same fallback as today (`residue_degree_lower_bound`, now also `"local": false`), never silent and never spinning; `HeckeExtSmallEllValidation` covers `ell = 5`; [Q16] |
| R9 | **Boundary coset side**: the left-coset `δ_i` and the right-coset `β_j` differ by the `det`-twist (transpose), i.e. `χ_b` vs `χ_{b+1}` on `H^0(∂)` — and the Dickson classes cannot tell them apart (`χ_1 ≡ χ_2` on every Dickson locus, [E Claim 1.7]) | medium / high (every prediction shifts by one twist) | the spec now fixes the side ([E (A1)], [EA M1]); route A vs route B equality, the explicit monomial eigenvectors `x^{n−bℓ}N^b ↦ χ_b`, the `β_j` negative control, the Eisenstein value `1 + p^{n+1}` on `[y^n] ∈ H^1(∂)` pinned as the oracle in C-A2, `r^1`-equivariance with the certified bulk operator — all in `HeckeBoundaryValidation` |
| R10 | **Order dependence creeping in** (hash containers, thread-dependent accumulation) | low / high | `SubspaceOps` canonical bases (§2.4); `HeckeExtDeterminismValidation`; `check_heckeext_includes.sh` also greps for `unordered_` |
| R11 | **Scope creep** (Heilbronn model, `F_{ell^r}` engine type, `Γ(2)` model, isomorphism classification, general `(a, b)` Bocksteins and the spectral sequence beyond E8's first extent, a general `Z/n`) | high / medium | §0.3 non-goals; each needs an owner decision; the follow-ups are recorded in §6.5. `Z/ell²` is **no longer** on this list: it is phase E8 with a stated first extent |
| R12 | **Atlas cost at large `ell`** (`Σ(ell)` needs all even `n ≤ ell − 1`) | certain for `ell > ~1000` / low | atlas limited to `ell ≤ 1000` in E6; beyond it Stage 4(c) is the certificate and `label = unknown` |
| R13 | **`B'(k, ell)` does not exist** (`ell \| [T^sat : T_Z(M_k)]`, [E Claim 2.9]) or exceeds the cap, so certificate (c) is unavailable and the dominant `m` at `n ≫ ell` — exactly where (c) is needed ([E Stage 4], "in the regime `n ≫ ell` the dominant `m` will need (c)") — end `final = false` | low frequency (no `none` on any `(k, ell)` computed: the pinned cells, the ten Kummer cells, `(162, 691)`, `(200, 691)`, and [XA §5.2]'s probes up to `k = 202` all give `B' ≤ ell`) / medium | (a) then (b) first; the `ι`-split (E3) raises the cyclicity yield; the outcome is *recorded* per `(k, ell)` (`sturm.B_prime = null`, `cap`, `closure_dim`) and the campaign's `analysis.txt` lists every such cell; the owner decides whether a flagged `S_sep ∪ {ell}` sweep may be published ([Q15]); a larger cap is one campaign key away |
| R14 | **`U_ell` coset budget** ([XA B3], [XA M4]): RSS `≈ (ell+1)·(0.11 + 5.8·10^{−5}(n+1)²)` MB (**v1.7: frozen as `(ell+1)·(0.123152 + 2.24985·10^{−4}(n+1)²)`, slot-3 WP-1; the figures that follow are the placeholder's**) — `≈ 5.6 GB` at `(16, 43867)`, `≈ 19 GB` per atlas run at `(690, 691)`, `≈ 1.5 GB` per golden cell at `ell = 10007`, and unbuildable at `ell = 134217757` | certain if scheduled / high | the frozen budget model and `u_ell` key (§1.5, §2.2 Stage 1), re-fitted once in E0a; the proof sweep contains `ell` only when `ell ≤ B'` (then `ell` is small); golden `u_ell = off`; atlas `U_691` for `n ≤ 220` only; every omission recorded (`u_ell_over_budget`) |
| R15 | **Decision latency** of the contract author and the owner on C-A1–C-A3, [Q3], [Q5], [Q15]–[Q18], the `U_ell` budget and — since v1.3 — the eight OQ2 open points of [V §8]: E3–E6 wait on people, not code | **low / medium** (re-rated 2026-09-15: was high/high) | §8 starts every contract draft on day one and lists each owner answer with the slot that needs it. **The eight OQ2 open points are all DECIDED (2026-09-15, §11)**, so the largest block of this risk has been discharged: C-A3's acceptance no longer waits on any of them, and a contract author has settled text at every site. **v1.5: nothing decision-shaped remains.** OQ3 is resolved ([C] v1.2.0), OQ4 / OQ5 / OQ8 / OQ12 / OQ15 / OQ16 / OQ18 and the `U_ell` budget are decided with their defaults (the eleven slot-1 confirmations, §6.4), and C-A1–C-A4 are accepted chapters of [C] — E3, E4 and E5 are gated on nothing but code. What R15 still covers: OQ13's LMFDB lookup (with the first `ell = 691` campaign, E6, non-blocking); the **C-A5 chapter** (slot 7), on which only E9 waits; the [E] and [P] consequential revisions of slot 2 (on which E0b's strict mode and E1b wait for their *spec* text, not their code); and the owner's verdict on any non-local golden cell WP-1 reports (confirmation 5: accepted as findings) |
| R16 | **Re-baseline collisions**: console C1 freezing `.expected` transcripts or hashes of decomposition JSON (or pinning `decomp_*` objects) against `hecke_report/v1`, and the 2745 published campaign records going stale by schema | high if unsequenced / medium | C1 freezes no decomposition transcript before E0b lands (§8); `ModArithmetic/ModArithmetic/Fnv.h` has one owner (E0a); the published records are marked stale in E0b and republished by E6 |
| R17 | **Certificate completeness**: a `verify()` that checks only the data it lists (v1.1's `CommutantCertificate` was an instance) passes truncated or wrong data | medium / high | §1.3 rule: every `verify()` **re-derives** its key quantity (a rank, a dimension, a nilpotency) from stored inputs; each certificate validation carries a tampered-data arm that must fail (§5, `HeckeExtAlgebraValidation`, `HeckeExtRecordValidation`) |
| R18 | **Basis-dependent pins**: absolute matrix entries such as `(10, 691)`'s `c'_q` depend on the stored `H^1` basis (tier B) | certain / low | intrinsic quantities (identities, ratios, eigenvalues, dimensions) are the primary assertions; basis pins are labelled as such and valid only while tier B gates the bases ([XA m19]) |
| R19 | **Strict-mode cost** (v1.5, §3.1): the Frobenius-kernel radical and the Berlekamp subalgebra are `O(dim A_S · D³ · N log ell)` with `dim A_S ≤ D²/4 + 1`, i.e. up to `O(D⁵ log D log ell)` per block — minutes on `MatrixT` at `D ≈ 170` | low (entered only after 64 failed linear witnesses, never on any computed cell) / medium | strict mode is opt-in and never the golden path; the linear phase runs first so the expensive route is a last resort; the `Frob` matrices are formed once per block; a `phase_reached` record and a cooperative cancellation point (§1.3.1 R3.3 item 5) make an over-long strict run interruptible and resumable, never a hang |
| R20 | **E9's triangulation is a direction, not a construction** (OD-T1: "in my opinion … a refinement of the current triangulation"): [C] `thm:specialisation` asserts nothing about the existence of a model satisfying `G1`–`G4` on a refinement, and the deferred construction may need a triangulation that is *not* a subdivision | medium / high for E9 (E0–E8 unaffected) | C-A5 is a **contract** task with a referee pass before any E9 code (§8 slot 7); its author reports if a subdivision does not satisfy `G1`–`G4`, and the owner decides the model then; E9's item 2 (the degree-generic tables) is value-preserving on the 7-vertex model and useful whatever the refinement, so it can proceed on the 7-vertex model first. **v1.12: RETIRED** — C-A5 is discharged on the unrefined `Xbulk` ([C] v1.8.0 `rmk:cafive`, OD-T1 "not needed"), so there is no refinement to construct |
| R21 | **E8's non-field elimination touches the engine's bit-identity contract**: a Howell form is a new algorithm class, and a careless retrofit could reach the `F_ell` path | low / very high | the `ENGINE_API.md` §13 section is written and reviewed **before** any kernel (E8 item 1); the composite path is selected by `ctx.is_field()` alone and the field path is untouched byte for byte; the whole existing suite, `GOLDEN_STRICT=1` and `cross_config.sh` gate every E8 item (§6.2 E8 acceptance (b)/(c)); the CUDA layer is not extended |

### 6.4 Owner decisions — all decided (v1.5)

**Every question this plan ever put to the owner is decided.** OQ1–OQ18 on 2026-09-14 ([OD]), the
eight OQ2 open points on 2026-09-15 (§11), OQ3's resolution and OC-1 on 2026-09-16 ([OD §OQ3],
[OD §OC-1]), and the **eleven slot-1 confirmations on 2026-09-16** ([OD] "Slot 1 confirmations" —
all "yes", with the recommended defaults), which settle every default v1.4 had to assume:

| # | Confirmation ([SP §6]) | Decision (2026-09-16) | Where it stands in v1.5 |
|---|---|---|---|
| 1 | Pull E4a into slot 1 | **yes** | §6.2 E4 split, §8 slot 1 Lane A |
| 2 | OQ5 placement (a): the locality fix inside `HeckeModuleDecomposition` | **yes** | §3.1; `Hecke/SubspaceOps` (§1.1) |
| 3 | Batch the oc1a record fields into E0b's single re-baseline, `Y` bump of [C] | **yes** | §1.6, §3.4 E0b, [SP §4.2] |
| 4 | `u_ell = auto`, `budget_mb = 2048`, constants re-fitted by WP-2 and frozen by E1b | **yes** | §1.5, §2.2 Stage 1 |
| 5 | Non-local golden cells (if any) accepted as findings named in `--accept-split` | **yes** | §3.3, §1.6 |
| 6 | OQ15: `sturm.unavailable = nonfinal` default, `heuristic` selectable; cap `12·B(k)` | **yes** | §1.5, §2.2 Stage 4(c), §1.3.1 R3.2 |
| 7 | OQ16: `locality = budget=64` default, `strict` selectable with the terminating route | **yes** | §1.5, §3.1 strict mode |
| 8 | OQ8: in the default `closure` mode an ideal that cannot reach closure is emitted `final = false` with a reason and resumable state, listed in `analysis.txt`, never withheld | **yes** | §1.3, §1.3.1 R3.2 |
| 9 | OQ18 / OQ12: (a) D6's socle semantics stays published until an E8 run exists; (b) the first ext campaign is bounded at `n ≤ 200` | **yes, yes** | §0.3, §6.2 E6 / E8 |
| 10 | Console C0 in slot 1 | **yes** | §8 slot 1 Lane C |
| 11 | The circle model at `ell = 2`: compute for every `ell` and record `boundary_model` / `boundary_is_group_cohomology`, never refuse | **yes** | §6.2 E4a, §5 `HeckeBoundaryValidation` |

**What is still owed, and by whom — none of it a decision this plan waits on:**
* **OQ13's LMFDB sub-question** stays with whoever runs the first `ell = 691` campaign (E6); until
  then the `(198, 691)` record documents the possible ambiguity (uniqueness of the congruent
  eigenform not checked), per [OD §OQ13].
* **C-A5**, the contract chapter fixing the concrete free `Γ`-model on the OD-T1 refinement — a
  contract author's task in slot 7 (§8), refereed; the owner confirms the refinement then (R20).
* **The E6 performance gate's verdict** on the canonical field (§2.2 Stage 6): OQ10 is decided
  *conditionally*; the measurement decides the default for the first campaign, and only a failed
  gate reopens the `F_{ell^r}` non-goal (§0.3) — **this plan proposes not to reopen it**, and puts
  the question to the owner only with the measurement in hand.
* **The verdicts WP-1 / WP-7 record in slot 1** (§9.3): the grid-locality verdict, the `(160, 691)`
  probe (OQ17 — the spec freeze is gated on it: WP-7 writes it into [E §8.2]), the `U_ell`
  constants. These are findings, not decisions, and confirmation 5 already says what happens to a
  non-local cell.
* **The [E] consequential revision** ([OD] item 1: tri-state `final`, the cap as a setting,
  strict-mode termination in Alg. 5.1(2) / Cert. 5.2 as §3.1 specifies it, `D_n` computed, the D6
  refinement, the canonical-field default, §8.2 / Stage 7 wording) and **the [P] revision**
  ([OD] item 10) are slot-2 documentation tasks ([SP §5]); this plan's text binds the code meanwhile.

The day-one list of v1.4 (`[Q5]`, the `U_ell` budget, `[Q3]`, `[Q15]`–`[Q18]`, the re-baseline
choice of §3.3, the acceptance of C-A1–C-A3) is thereby **closed in full**; `[Q7]` is moot (v1.1).

### 6.5 Follow-ups recorded, not scheduled

A Manin-sized `H^1` model seeded by `BarCocycleH1` with explicit `r^1` (G15/G16; OQ12 DECIDED: not
the direction — downgraded); a `Pipeline` static library so `HeckeExt` can become a library
([P §16.4]); `FlatMatrix`-backed Berkowitz (R6); **Conway polynomials** where tabulated, behind the
reserved `field_polynomial = conway` (OQ9: "prepare for optional Conway polynomials as a future
configuration option" — the key exists, the tables do not); an **`F_{ell^r}` element type** (a
Zech-log or a `k_max`-aware polynomial-basis type on `ModCtx`) **only if** E6's performance gate
fails (§0.3, §2.2 Stage 6); a **general `Z/n`** and general-`(a, b)` coefficient sequences, the
`ell`-adic spectral sequence pages and the CUDA layer over a composite modulus — everything E8's
first extent leaves out (§6.2 E8); the boundary periodicity and the cone half of `oc1c` ([C]
`rmk:bulkperiodicscope`(3)) once E9 has *observed* them; an `n ~ 10^4` regime (needs both the
Manin model and a fast charpoly, [I G16]). (`Z/ell²` itself is no longer a follow-up: it is E8.)

---

## 7. Console integration

The engine ships `HeckeExt/RegisterHeckeExtensionVerbs.cpp`, called from the one `kernel.cu` branch
the console adds ([PA A6]); it never edits `Console/Core/`. Types (each a `TypeInfo` with
`describe / print / show / hash` in the per-kind FNV of `ModArithmetic/ModArithmetic/Fnv.h`, [PA A4]; every handle
keeps alive what it borrows, [P §2 C2]):

| Type | Wraps | Members |
|---|---|---|
| `MaximalIdeal` | `MaximalIdealBlock` | `.dim`, `.residue_degree`, `.local`, `.witness_poly`, `.w_hat_exponent`, `.character(p)`, `.basis`, `.jordan(p)` (units of `f`) |
| `LocalAlgebra` | `LocalAlgebra` | `.dim`, `.embdim`, `.nilpotency`, `.socle_dim`, `.gorenstein`, `.hilbert`, `.basis`, `.radical`, `.w_hat`, `.n(p)`, `.tangent(p)`, `.active_set` |
| `SturmBound` | `SturmBound` | `.k`, `.ell`, `.B_prime` (or `none`), `.cap`, `.closure_dim`, `.dim_M_k`, `.T(q)` (the Miller-basis matrix), `.verify()` |
| `GenerationCertificate` | §1.3 | `.kind`, `.generators`, `.primes_swept`, `.bound` (the `SturmBound`), `.verify()` |
| `ModuleStructure` | per group | `.loewy`, `.socle`, `.layer(j)`, `.structure_map(j)` (with `.matrix(p)`, `.rank`), `.active(j)`, `.cyclic`, `.free`, `.min_generators`, `.position(name)` |
| `ExtRecord` | `HeckeExtRecord` | `.ideals`, `.groups`, `.identities`, `.sturm`, `.final`, `.json`, `.hash` |
| `Involution` (E3) | `HeckeInvolution` | `.matrix(q)`, `.plus(q)`, `.minus(q)`, `.eisenstein_line(m)` |
| `BoundaryCohomology` (E4) | `HeckeBoundary` | `.dims`, `.r(q)`, `.A(p, q)`, `.characters` (the `χ_b` multiset per group), `.cosets(p)` (the `δ_i`), `.tau_boundary` (the `Γ`-level `τ_∂` table and its certificate), `.solve_regime` |
| `ConeCohomology` (E5) | `EquivariantMappingCone` + action | `.dims`, `.les`, `.A(p, q)`, `.H1_shriek`, and — per [V §7] item 12 — `.h(q)` (**derived**, not stored), `.pair_homotopy` (the `η`-table and its `PairHomotopyCertificate`), `.eta_zero`, `.cochain_commutes`, `.solve_regime`, `.coefficient_ring`, and — OC-1, [P §14.3] G10 — **`.q_max`, `.truncated`, `.q_max_source`, `.degrees`** |
| `Atlas` (E6) | `HeckeAtlas` | `.systems`, `.separating_primes`, `.lookup(character)` |
| `ContragredientLocalSystem` (E7, R4) | the `(K, R, D_n)` local system | `.p`, `.d_V`, `.relations` (the `adj`-transposed list), `.Phi_n` (the comparison map, `lem:symdual`), `.is_iso` (`n < ell`) |
| `Pairing` (E7, R4) | `HeckePairing` | `.level ∈ {coefficient, cochain, cohomology}`, `.matrix(t)` (in the stored bases), `.perfect`, `.adjoint(p)` (the PD adjointness verdict), `.iota_sign` (recorded), `.verify()` |
| `Presentation` (E2, OQ11) | `HeckePresentation` | `.generators`, `.relations` (as `t`-tuples over the `A_S` basis), `.min_generators`, `.min_relations`, `.verify()` |
| `Settings` (R1) | `MathSettings` | every key of §1.5 with its `source`, `.fingerprint`; `set final_mode = "closure"`, `set locality = "strict"`, `set sturm_cap = 24`, … go **through the registry** into `HeckeSettings` — the console never re-implements a default or a validation ([OD] R1); `?x` prints the snapshot with the mathematical keys beside the engine ones ([P] C2/C4) |
| resumable handles (R3) | `XState` | every budgeted object above exposes `.resumable` (`complete`, `budget`, `reached`, `budget_history`) and the verb **`resume(x, budget = …)`** returns a **new handle** computed from `x.state()` under the new budget, keeping `x`'s settings snapshot and appending to `budget_history` (§1.3.1 R3.1 item 4; a resume with a changed non-budget setting is a typed error) |

Verbs: `maximal_ideals(F, q [, family])`, `local_algebra(m)`, `coefficient_field(m)`,
`sturm_bound(k, ell [, cap])`, `certify_generation(m, mode = "auto" | "cyclic" | "commutant" |
"sturm", cap = …)`, `module_structure(m, group)`, `ext_record(H, family = […], sign = …, sturm = …)`,
`ext_report(rec, path = …)`, `iota(H)`, `sign_split(x, iota)` / `H_plus` / `H_minus`
([PA A10]'s reserved names), `eisenstein_line(H_plus, m)`, `boundary(H)`, `restriction(H)`,
`cone(H)`, `atlas(ell)`, `predict(n, ell)`, `bernoulli_mod(w, ell)`, `canonical_field(ell, r)`,
**`dual(L)`** (the contragredient local system), **`pairing(X, Y)`** (E7), **`presentation(m, group)`**
(E2, OQ11), **`resume(x, budget = …)`** (R3), **`reduce(H, k)`** / **`bockstein(H)`** (E8), and
the linear-algebra verbs of [PA A9] as thin wrappers over `SubspaceOps` (`solve`, `hstack`,
`vstack`, `submatrix`, `column_space`, `intersect`, `sum_spaces`, `restrict`, `vec`, `unvec`,
`commutant`, `nullity`, `algebra_closure`, `is_nilpotent`, `teichmuller(w, ell, N)`,
`random_vector(p, n, seed)`). Overloads added, never edited: `charpoly` / `minpoly` on
`MaximalIdeal`-restricted operators, `hash` on every type above. The console plan's G6 row
([P §14.2]: "`in_span` + `family(H).T(p)` for the Sturm sweep") is subsumed: the sweep's prime list
comes from `sturm_bound`, never from a hard-coded `B(k)`.

**Two pointers for the [P] revision** (slot 2, [SP §5]; the console plan is not edited by this
plan): (1) `Fnv.h` is `ModArithmetic/ModArithmetic/Fnv.h`, not `Orbifold_Cohomology_of_GL2/Util/Fnv.h`
as [P] C1 (G5), [P §9]'s TU layout and [PA A4] write it (§1.1); (2) WP-1's `GoldenLookup(point,
object)` from `Golden/GoldenHarness.h` **is** the lookup [P] C1's G13 consumes — one lookup, not two,
and no `Util/GoldenLookup.h`. Both are recorded in `docs/implementation/slot1/WP-6_report.md` for the
console lane, together with the C2/C4 (mathematical settings) and C2/C5 (resumed handles) text the
[P] revision needs.

Scripts that become test cases (`Console/scripts/`, `.oc` + `.expected`, `ConsoleScriptValidation`):
`ext_10_691.oc` ([E Claim 8.1], `U_691` included, pinning `hash(rec)` — `(10, 691)` is on the golden
grid), `sturm_22_5.oc` (the counterexample: `sturm_bound(24, 5).B_prime == 5`, the `{2, 3}` closure
`2 < 3`), `ext_160_691.oc`, `ext_198_691.oc`, `ext_34_5.oc`, `ext_dickson_6_5.oc`,
`ext_kummer_18_283.oc`, `identities.oc` ([E §5.1], run by `HeckeExtEndToEndValidation` through the
registry once C1 exists — until then the same checks live in C++). Per [PA A14], whether a
*predicted outcome* holds is this engine's acceptance, not the console's; the scripts assert
certificates and identities and print predictions.

---

## 8. Implementation order: engine, console, or split

**The console planner's case for console-first** ([P §15]): Stages 1–5 are an interactive workflow
best prototyped as scripts; the substrate is stable; scripts are free tests. **The auditor's
verdict** ([PA §5]): split — console C0 + C1 in parallel with engine Stage 0 (boundary, cone, `ι`),
because Stage 0 is the critical path and cannot be prototyped in the console, and Stage 2 is already
shipped.

**This plan's verdict: split, with a different critical path.** Two corrections to the auditor's
picture:

1. *The engine's first certified results do not wait on Stage 0.* E0–E2 are pure `F_ell`-linear
   algebra on the shipped `A^{(q)}(T_p)` plus the pipeline-independent Sturm bound; they deliver
   the [E Claim 8.1] record at `(10, 691)` (`U_691` included), the separation case, the small-`ell`
   cases with the Sturm counterexamples, and the Kummer list on `X_4` with **no contract
   amendment**. That is the earliest owner-visible value (M1, 5.25 AU) and the auditor's "Stage 0
   first" would delay it behind the cone. [XA §7.2] agrees.
2. *Stage 0 is three phases with three different blockers*, not one: `ι` (E3) needs only C-A1 and
   [Q3] and is cheap; the boundary (E4) needs C-A2 **and C-A3** (whose coset side v1.1 has
   settled, and whose boundary datum the OQ2 verdict has now packaged as the `Γ`-level `τ_∂` —
   *defined* in C-A3(ii.2), which is why C-A3 gates E4 too, so E4 has no open convention left); the cone (E5) needs C-A3 — whose contract text is the slowest item of all, so
   it starts on day one ([XA §7.2] item 3, [XA M6]) — but **no longer waits on an E4 verdict**: the
   OQ2 verdict answers [Q2] in advance, so C-A3 is finalisable in slot 2 and the gate
   "[Q2] test → C-A3 final" is gone ([V §7] item 9). Serialising them as "Stage 0" would still put
   the cone in front of the boundary's certain value.

The v1.1 spec changes and the v1.2 audit changes do **not** move the critical path
(E0 → E1 → E2 → E3/E4 → E5); they re-cut it. The audit's three schedule changes are adopted
([XA §7.3], amendment 12): **E0a** (value-preserving) and **`HeckeSturmBound`** start on day one as
two engine workstreams; the **contract author starts the C-A3(ii) homotopy draft on day one**
(with C-A2 and C-A1) — and since the OQ2 verdict fixes the formulation (b\*) in advance, that draft
now runs **to acceptance in slot 2** rather than waiting for an E4 test; and **console C1
freezes no decomposition transcript or hash until E0b lands**. The plan adds one refinement of its
own: E1 is cut into E1s / E1a / E1b so that the second engine workstream is never idle while E0b
runs.

**The schedule, re-cut from today (v1.5, 2026-09-16).** The v1.4 table below this paragraph is
**superseded**; it is kept only in the changelog's memory. What changed since it was written: the
contract drafting of C-A1–C-A3 (and C-A4) is **done** ahead of schedule ([SP §2.1]), so Lane A
starts the long pole with E4a in slot 1 (confirmation 1); OQ3 is resolved, so E3 has no gate but
code; E7, E8 and E9 exist; and slot 1 is the four lanes of [SP §4.1] — the re-cut keeps [SP]'s
lanes, its merge order and its one re-baseline in slot 2 verbatim. Four lanes, **at most four
concurrent agents in any slot** (a lane runs one agent at a time; Lane A hands over between the
contract author and the geometry engineers, never overlapping). A slot is ≈ 1 AU of one
workstream; an item longer than its slot continues in the same lane (*cont.*). Per the owner rule,
every agent is stopped the moment its item is accepted. "Gate" is what must be accepted before the
item **starts**.

| Slot | Lane | Item | Gate (to start) | Effort | In parallel with |
|---|---|---|---|---|---|
| **1 (now)** | B1 engine | **E0a** = [SP] **WP-1** (`Hecke/SubspaceOps` seed, read-only `CertifyLocality`, `GoldenDump` + `golden_explain.py`, `GoldenLookup`, the four-hash grid arm, the `(160, 691)` probe) → **WP-2** (`DicksonInvariantCount`, `IdentityCertificate`, `ModArithmetic/ModArithmetic/Fnv.h`, the `U_ell` RSS fit) → **WP-7** (slot close: merges, `--all-full`, `cross_config.sh`, the E0a performance reference, §9.3, [E] v1.3.3 and [C] v1.3.3 `Y` bumps, CLAUDE.md) | none; WP-7 after WP-1/2/3/4/6 accepted | 0.5 AU + close | E1s, E4a, C0, this revision |
| 1 | B2 engine / docs | **this revision (WP-6)**, §1.3.1 first → **E1s** = **WP-3** (`HeckeSturmBound` with `SturmState` / `resume`, the `HeckeExt/` include guard, `HeckeSturmBoundValidation`) | WP-6 §1.3.1 committed | docs + 0.5 AU | E0a, E4a, C0 |
| 1 | A geometry | **E4a** = **WP-4a** (the certified `τ_∂`) then **WP-4b** (`Θ^∂_g`, routes, oracles, `r^q`, model recording) | confirmation 1 (given); WP-4b after WP-4a accepted; confirmation 11 (given) before WP-4b | 1.0 AU | E0a, E1s, C0 |
| 1 | C console | **C0** — language core ([P] Phase C0 as amended by [PA] A1–A16) | none (confirmation 10, given) | 1.5 AU (slots 1–2) | E0a, E1s, E4a |
| **2** | B1 | **E0b** — the locality fix with `CertifyLocality` in the loop, the `k = 1` analytic path, `Hecke/HeckeSettings.h` with `locality` (budget / **strict**, `LocalityState`), `hecke_report/v2` with the block keys **and the oc1a fields**, `level_c.locality`, **the one re-baseline** of the stage with `golden_explain.py --allow-keys e0b.keys` (384 lines predicted, §1.6), the performance gate, the stale-schema note. **Outcome (v1.6)**: split as [S2] WP-1 (the loop, `HeckeSettings`, budget mode — **accepted**) + WP-2 (the re-baseline, **384 lines exactly, accepted**) + WP-6 (strict mode — **slot 3**, head of B2; `strict` throws the named error meanwhile); E1b-0 = WP-3 (the `U_ell` reach repair) was pulled into this lane and **did not run** | E0a accepted; WP-7's performance reference and grid verdict; owner verdict on any non-local cell (confirmation 5: accepted as findings) | 0.75 AU | E1a, E4b → E5, C0 → C1, the [E]/[P] revisions |
| 2 | B2 | **E1a** — `HeckeLocalAlgebra`, certificates (a)/(b) with the socle bound and `CommutantState`, the cross-block test, `HeckeExtAlgebraValidation`. **Outcome (v1.6)**: WP-4 + WP-5 **accepted** (constructed-truth arms; the real-block arms are E1b's); namespace `hecke_ext` decided | E0a accepted (`SubspaceOps`, `CertifyLocality`) | 1.0 AU | E0b, E4b/E5, the document packages |
| 2 | A | **E4b** (diagnostics, `H^1_!`, Harder, the golden objects defined for E2's emission; record integration deferred to E2) → **E5 core starts** (the `η`-table and its certificate on E4a's `τ_∂`). **Outcome (v1.6)**: WP-7 **accepted** (`HeckeExt/HeckeBoundary`, `HeckeBoundaryDiagnostics`, `HeckeBoundaryParabolicValidation`; the verdicts in §9.3), WP-8 **accepted** (`HeckePairHomotopy` + `HeckeIntegerSolve`, `obl:eta`(i)–(iv), `HeckePairHomotopyValidation`) — E5 core's first 0.5 AU is done, the cone (slot 3) next | E4a accepted | 0.5 AU + E5 core (2.5 AU, slots 2–5) | E0b, E1a, the document packages |
| 2 | C | ~~C0 *cont.* → **C1**~~ **Re-cut (v1.6, [S2] §2.3 item 3, owner-confirmed non-blocking)**: Lane C's slot 2 was the **four document packages** — WP-9 ([C] v1.4.0, the nine deferred boundary-chapter points), WP-10 (referee, [C] v1.4.1), WP-11 ([E] v1.4.0), WP-12 ([P] v3) — each a single-editor agent, so C1 did **not** start; it starts in slot 3 as **C1a** (WP-14) | C0 accepted; E0a | docs | E0b, E1a, E5 |
| 2 | docs (no lane, one editor each) | the **[E] consequential revision** ([OD] item 1 — the freeze candidate after WP-7's probe verdict, OQ17), the **[P] revision** ([OD] item 10, with the two §7 pointers and the C2/C4/C5 text of the WP-6 report), `label_census.sh` ([C] `sec:machinery` item 2, a filler). **Outcome (v1.6)**: [E] v1.4.0 and [P] v3 delivered in Lane C (row above); `label_census.sh` (WP-15) **not done** — a slot-3 filler, it needs WP-10's labels | WP-7 accepted ([E] and [C] are single-editor documents) | docs | everything |
| **3** | B1 | **E1b-0 first (v1.6)** — the `U_ell` exact-integer reach repair and the RSS re-fit ([S2] WP-3, which did not run in slot 2; [KI] §3) — then **E1b** — the Sturm sweep to `B'` (cache reuse + streaming), both `sturm.*` modes, the `U_ell` budget with its resume, real-block arms; then **E2** starts. **Outcome (v1.7)**: [S3] WP-1 (E1b-0) **accepted** — the site was `alg:tau` step 1, the reach is `ℓ ≤ 23170`, the constants frozen — and WP-2 (E1b) **accepted** — without the `U_ell` resume (moved to E2, [S3] §2.3 item 2) and without the streaming route for `q ∉ S_0` (E2's `HeckeExtDriver`); **E2 did not start** ([S3] §6 item 3, owner-confirmed: slot 4) | E0b, E1a, E1s accepted (all three are) | 0.25 + 0.75 AU + E2 | E3, E5, C1a |
| 3 | B2 | **WP-6 strict locality mode first (v1.6, E0b-S: Frobenius radical, Berlekamp subalgebra, residue witness over `Ā`, `phase_reached`, the strict-mode arms of `HeckeLocalityValidation`, `HeckeSettings` accepting `strict` without the named error)** → **E3** — production `ι^* = −ρ_n(ι)` per block, the sign split, `HeckeInvolutionValidation` (agreeing entrywise with `HeckeIotaSignValidation`); record integration waits for E2. **Outcome (v1.7)**: strict mode = [S3] WP-3 **accepted**; **E3 moved to slot 4, head of Lane A** ([S3] §6 item 4, owner-confirmed), and Lane B2 ran the contract revision instead — [C] v1.5.0 (WP-8, with [E] v1.4.1) and its referee pass v1.5.1 (WP-9) — plus the `label_census.sh` filler (WP-10, accepted) | E0b accepted (it is); C-A1 (met), OQ3 (resolved) — **no gate but code** | 0.4 + 1.0 AU (0.75 here) | E1b/E2, E5, C1a |
| 3 | A | **E5 core** *cont.* — the cone complex, the (3.1) maps, exactness, `Φ_g` from `Θ_g`, `Θ^∂_g` and the derived `h = η̃`, `A_c^{(q)}`, the `ConeActionCertificate`. **Outcome (v1.7)**: [S3] WP-5 (the cone, E5-2) and WP-6 (the action, E5-3) **both accepted**; what E5 core has left is the record integration, `les_maps`, the golden emission and acceptance with the `1.5×` RSS gate (WP-5 measured `compute()` + `verify()` at `n = 256` at 1.7× `hecke 256`'s VmHWM — the gate is at risk and `verify()`'s solve-based inclusions are the first lever) | — | — | E1b/E2, E3, C1 |
| 3 | C | **C1a** (v1.6; [P] v3 §10, [S2] WP-14) — bindings, the CLI branch, `GoldenLookup` in `Golden/GoldenHarness.h`, `hash` / `golden`, `ConsoleCliPreservationValidation` (`--list` compared modulo appended names), first pins with fingerprint `0` → **C1b** — the decomposition surface, the ≥ 12-script set frozen against `hecke_report/v2`, `ConsoleScriptValidation` (slot 3 → 4). **Outcome (v1.7)**: C1a = [S3] WP-7 **accepted**, with `ConsoleScriptValidation` registered **in C1a** (the C1a arms) beside `ConsoleCliPreservationValidation`; C1b is slot 4's | [P] v3 accepted; E0b merged (both are) | 1.0 + 1.0 AU | E1b/E2, E3, E5 |
| **4** | B1 | **E2** *starts* (v1.7: not *cont.* — it did not start in slot 3; **with the `u_ell` resume of R3.3 item 4**, moved here from E1b) — module structure, `HeckePresentation`, record with the tri-state `final` / `settings` / `resumable`, report, campaign per cell with the new keys, `--bench ext`, the **add-only** golden emission (ext subgrid, `sturm_bound`, E4b's boundary objects) | E1b accepted | 1.75 AU (slots 3–5) | E6 units, E5, C1 |
| 4 | B2 | **E6 pre-record units** — `bernoulli_mod`, `HeckeCanonicalField` (+ the performance-gate bench), `GloverFactors`, atlas driver skeleton | E1b accepted | 0.75 of 1.75 AU | E2, E5, C1 |
| 4 | A | **E3 first (v1.7, moved from slot 3 Lane B2, [S3] §6 item 4)** — production `ι^*`, the sign split, `HeckeInvolutionValidation` (the slot-3 plan's item 8 text is its acceptance) — then **E5 core** *cont.* (the cone record, `les_maps`, golden emission; acceptance in slot 5) | C-A1 (met), OQ3 (resolved) | 1.0 AU + E5 | E2, E6 units, C1 |
| 4 | C | C1b *cont.* → C1 accepted (possibly slot 5; Track C gates no engine phase — v1.6) | — | — | E2, E6 units, E5 |
| **5** | B1 | E2 *cont.* → **M1**. **Outcome (v1.9): DONE.** `hecke_ext/v2` (WP-1), the campaign integration with the record-level `u_ell` resume (WP-2), **the stage's one add-only golden emission** (WP-3), `DicksonMultiplication` + identity class 5 + **M1 declared** — 23 cells, 62 ideals, every one with a `final` tri-state and a `B'(k, ell)` column (WP-8) | — | — | E3 integration, E5, C scripts |
| 5 | B2 | **E3 record integration** (per-sign records, Eisenstein line), then **E6** *cont.* **Outcome (v1.9): PARTLY DONE, and re-cut.** The E3 record integration landed **inside WP-1 and WP-12a** rather than as a lane item of its own; `HeckeCanonicalField` shipped (WP-7) **with its performance gate measured and found defective as written**; the **atlas driver skeleton (WP-9) was DEFERRED by the owner and did not run**, and with it E6 *cont.* — both are slot 6's | E2's record type | 0.25 + 1.0 AU | E2, E5, C |
| 5 | A | **E5 core** *cont.* → **accepted**. **Outcome (v1.9): ACCEPTED.** WP-4's two contract tightenings, WP-5's cone on the tape, and acceptance (d) **restated by the owner and MET at 1.93×**; (a)–(c) re-verified on the final tree; the record fields are WP-1's. **Acceptance was declared by the close (WP-13)**, not by a package | — | — | E2, E3/E6, C |
| 5 | C | engine `.oc` scripts for the E0–E2 cases (early partial **C5**). **Outcome (v1.9): DONE** — WP-10 bound `bernoulli_mod` / `glover_factors` and added scripts `017`–`020`, with the 16 pre-existing `.expected` files byte-unchanged | C1 accepted; E0b | 0.5 AU | E2, E3/E6, E5 |
| 5 | (extra) | **WP-6** — the pipeline-wide `ρ_n` memo (`Hecke/RhoMemo.h`), an (a/s) package with no acceptance criterion of its own beyond value preservation: the cone action's `n = 256` build 74.5 → 42.6 s for ~3.2 MB. **WP-11a** and **WP-12a** are follow-on packages created inside the slot, for the `sec:recordschema` item-5 gap and the two owner rulings on the referee's Q2 / Q3 | — | — | — |
| **6** | B1 | **E7** — `D_n`, the contragredient local system, the pairing at three levels, `HeckeDualityValidation`, **the PD gate for `X_3`**. **(v1.9) Its gates are now all met**: E2, E4b and E5 are accepted (all three landed in slots 4–5) **and [E] v1.6.0 fixed the `det`-twist convention normatively**, which was the remaining one. **Outcome (v1.10): E7a (WP-1) and E7b (WP-3, (a/s), accepted) DONE**, the PD gate asserted; E7 acceptance and its add-only emission are slot 7's. (v1.10 correction: E2 was **not** accepted at v1.9 — it is declared by the slot-6 close; E7 started on E2's substantive state by [OD] S6-1) | E2, E4b, E5 core accepted; C-A4 (met); **[E]'s `det`-twist convention (met, v1.6.0)** | 1.25 AU (slots 6–7) | E6, E5 arms, C2 |
| 6 | B2 | **E6** *cont.* → **first ext campaign** (`ell ∈ {5, 7, 11, 13, 691}`, **`n ≤ 200`** — confirmation 9(b); `hecke_report/v2`; the canonical-field default per the gate's verdict). **(v1.9) Carries three items slot 5 did not**: the **atlas driver skeleton** (deferred WP-9), **E6's performance gate restated** by the owner (this version's changelog gives the measurement it would be restated from — the clause as written is unmeetable by any implementation), and `HeckeCanonicalField`'s **report consumer**, which does not exist yet. **Outcome (v1.10): part 1 DONE** — the atlas for `ell ≤ 13` with the canonical split field's first consumer (WP-8), identity 6, `S_sep` opt-in, the `proof_range` comparison (WP-9), the gate restated into §6.2 E6 (d) with the owner's measurement condition discharged (WP-7, the window) — **and the first ext campaign DEFERRED to slot 7** ([OD] S6-6, a recorded deviation). The high-`r` cells fail the restated bound: [OD] E6-3 books the root-finder fix into slot 7 | E2, E3 accepted | — | E7, E5 arms, C2 |
| 6 | (new) | **The slot-5 carry-over list**: `HeckeExtCampaignValidation`'s **golden arm** ([X] §5; possible only since WP-3's emission — it **must** install `u_ell = off` **and** `good_primes = {2, 3, 5}`, or it compares two different computations); the **`Job::id()` gap** (WP-2: the id carries no extension key, so two campaigns differing only in `family` share a resume key); the **`HeckeExtDeterminismValidation` `commit` redaction** and its one re-pin (WP-3 finding 3); relabelling `A_c(T_p)^q` tier `'A' → 'B'` in `HeckeConeAction::golden_objects()` with the two cone digests re-pinned (WP-3 finding 5, zero golden cost); and `ScopedUEll`'s `source` reading `"console"` when the setter is the harness (WP-3 finding 7, cosmetic). **Outcome (v1.10)**: the golden arm (over the settings-independent objects), the ext-identity fix and the redaction **DONE** (WP-6); the relabel **DONE** at zero golden and zero printed cost (WP-5 — "two cone digests re-pinned" was wrong, nothing was); the `source` fix is **not** cosmetic (it is inside all 62 `ext_json_*` texts) and is booked into slot 7's re-baseline, stage 1 | — | — | — |
| 6 | A | **E5 cross-route arms** — the strict-pair `τ^s` route and the relative-complex route 3, each asserted to give the same `A_c^{(q)}` (OP3, committed). **Outcome (v1.10): DONE** (WP-4, WP-5), 212 / 212 operators each; with WP-3's PD gate, `obl:coneexact`(vii) is implemented in full | E5 core accepted (slot 5) | 0.75 AU | E7, E6, C2 |
| 6 | C | **C2** — settings / harness verbs, **the mathematical settings through the registry** (§1.5). **Outcome (v1.10): C2a DONE** (WP-13, [P] v3.4 (f)–(h)); C2b is slot 7's | C1 accepted | 1.5 AU (slots 6–7) | E7, E6, E5 arms |
| **7** | B1 | E7 *cont.* → accepted; then **E8 item 1**: the `ENGINE_API.md` §13 section (composite modulus, non-field elimination), reviewed. **Outcome (v1.11): DONE** — E7 accepted with its add-only emission (WP-1), §13 written (WP-9) and accepted by an independent review (WP-10) | E7 done | 0.25 of 2.0 AU | E6 close, C-A5, C2 → C4 |
| 7 | B2 | E6 *cont.* → **accepted** (the campaign table published, `analysis.txt` with every `unpredicted`, `local = false`, `B' = none`, `u_ell_over_budget`, Stage 2(3) split and every `final = false` ideal); then B2 is **stopped**. **Outcome (v1.11): DONE** — E6 declared; the campaign published in W2 | — | — | E7/E8, C-A5, C2 → C4 |
| 7 | A contract author | **C-A5** — the concrete refinement (OD-T1) and the free `Γ`-model satisfying [C] `G1`–`G4`, with its referee pass (an `X` bump). **Outcome (v1.11): NOT STARTED** — deferred to slot 8 by the owner ([OD] S7-8) | E5 accepted (so the chapter can cite the shipped pair datum); the owner's refinement | contract work (not AU) | E7/E8, E6, C2 → C4 |
| 7 | C | C2 *cont.* → **C4** hardening. **Outcome (v1.11): C2b DONE** (WP-8); **C4 moved to slot 8** ([OD] S7-9 … 15, confirmation 12) | C2 accepted | 0.75 AU | E7/E8, C-A5 |
| **8** | B1 | **E8** items 2–4 — the composite `ModCtx`, the Howell elimination, the pipeline over `Z/ell^k`, the reduction maps and the `a = b = 1` Bockstein, `HeckeReductionValidation` | E8 item 1 reviewed; E2 (E5 for the cone half) | 1.75 of 2.0 AU (slots 8–9) | E9, C5 |
| 8 | A geometry | **E9** — the refined descriptor, the **degree-generic `τ`-table** (value-preserving on the 7-vertex model), `τ_∂` / `η` on the refinement | C-A5 accepted; E5 accepted | 2.5 AU (slots 8–9) | E8, C5 |
| 8 | C | **C5** full, after E5's record-schema freeze (`.pair_homotopy`, `.h(q)` derived, `.q_max`, `.truncated`, `.degrees`, `.coefficient_ring`, the E7 / E8 types) | E5 accepted (slot 5); C4 | 1–1.5 AU | E8, E9 |
| **9** | B1 | E8 *cont.* → **accepted** | — | — | E9 |
| 9 | A | E9 *cont.* → the **truncated pair** at `ell ∈ {2, 3}`, **the six [R §5] tests** (`HeckeFreeModelValidation`), the observed stabilisation reported to the owner; then Lane A is **stopped** | — | — | E8 |

Concurrency check: slots 1–6 run exactly four agents (B1, B2, A, C; the slot-2 documentation
editors are the single-editor rule of [SP §4.3], not a fifth lane — they run when WP-7 has
released [E] and [P], sequentially); slot 7 runs four (B1, B2 closing, the C-A5 author in Lane A,
C); slot 8 runs three; slot 9 two. The long pole is still Lane A — now **E4a → E4b → E5 core → E5
arms → C-A5 → E9**, ≈ 7.25 AU of engineering plus one contract chapter — which is why E4a starts
today. **The deliverable** — the six-group record — lands in **slot 5**, one slot earlier than
v1.4's slot 6, because E4a is pulled into slot 1 and E5 core starts in slot 2; the cross-route arms
follow in slot 6 (v1.4: slot 7). M1 is unmoved (slot 5). E7–E9 extend the schedule to slot 9; none
of E0–E6 waits on them.

**The one re-baseline, restated** ([SP §4.2]): slot 1 changes no golden value (every package gated
on `GOLDEN_STRICT=1` tier A 9446/0, tier B 4603/0 against the unchanged reference; E4a adds no
golden object); **slot 2's E0b is the only mutating emission** (the schema text, the block keys,
`level_c.locality` and the oc1a fields: 384 lines in two kinds, explained by `golden_explain.py`,
classified in `docs/matrix-engine/rebaseline-<date>-hecke-report-v2.md`); E2, E4b, E5, E7, E8 and
E9 **add** entries only, which is the trivially explained case. **(v1.10) Superseded for E6 and
for any key registration** (§1.6, v1.10): the programme's remaining golden events are slot 7's
separate E7 add-only emission and its one staged changed-line re-baseline, below.

**The slot-6 outcome and the slot-7 re-cut (v1.10).** Slot 6 ran fourteen packages (WP-1 … WP-14)
within the authorised 5.50 AU ceiling; no package used its shed line and the (a/s) package WP-3
was accepted. **Delivered**: E7a and E7b (WP-1, WP-3), both E5 cross-routes (WP-4, WP-5),
`HeckePresentation` (WP-2), E2's close-out (WP-6), the E6-1 code side and the owner's two
measurements (WP-7), the atlas for `ell ≤ 13` (WP-8), identity 6 / `S_sep` / the `proof_range`
comparison (WP-9), the ratio audit (WP-10), [E] v1.7.0 / v1.7.1 and [P] v3.4 (WP-11, WP-12),
console C2a (WP-13) and this close (WP-14). **Deviations, recorded**: the first ext campaign did
**not** run — deferred to slot 7 by the owner ([OD] S6-6), a deviation from v1.9's slot-6 B2 row;
E6 was not declared (it never was slot 6's); the record text did not move ([OD] S6-3).

**Slot 7, re-cut from the slot-6 outcome** (supersedes the slot-7 rows of the table above where
they differ; the owner's ceiling for slot 7 is not yet set):

| Item | Content | Gate | AU (order of magnitude, [S6] §6 decision 6's sketch) |
|---|---|---|---|
| **E7 acceptance** | (a)–(c) re-verified on the slot-7 tree; the console types / verbs of §7 if C4 is reached | E7a, E7b done (they are) | 0.25 |
| **The E7 add-only emission** (stage 0 below) | `dim_H(D_n)^q`, `charpoly_A(D_n)(T_p)^q`, `pairing_perfect^t`, `pd_adjoint^t` (A), `pairing_matrix^t` (B) | E7 accepted; owner-gated | with the next row: 0.50 |
| **The staged changed-line re-baseline** (stages 1–3 below) | one owner-gated event, each stage its own commit with its own `golden_explain.py` summary | the owner's go per stage | (in the 0.50 above) |
| **The canonical-field root-finder fix** ([OD] E6-3) | diagnose and fix `FindCanonicalRoot` (≈ `r^5`–`r^6` against `alg:split`'s `O(r^3 log ell)`; WP-8's suspect: the equal-degree splitting over `F`); re-measure the two high-`r` cells; add a high-`r` cell to §6.2 E6 (d)'s list | none (ruled) | ≈ 0.25 (small package) |
| **E6 *cont.*, part 2** | the `ell = 691` atlas + per-`ρ̄` tangent pairs + `ext_compare.py` | — | ≈ 0.55 |
| **The first ext campaign** + `analysis.txt` | `ell ∈ {5, 7, 11, 13, 691}`, `n ≤ 200`, after stages 1–2, published under the re-baselined record text, `split_field_report = canonical` | re-baseline stages 1–2 landed; the root-finder fix (so the gate verdict is decidable) | ≈ 0.40 |
| **E6 acceptance** | the gate (§6.2 E6 (d), with its new high-`r` cell) re-run with a report consumer after the fix; (a)–(c) | the campaign table; the root-finder fix | ≈ 0.15 |
| **E2 (e′)** | its constant confirmed, then measured | owner | (in the campaign) |
| **E8 item 1** | `ENGINE_API.md` §13, reviewed | E7 done | 0.25 |
| **C2b** | harness verbs, the bench extraction, [P] §10 C2 (a)–(e) | C2a accepted (it is) | ≈ 0.90 |
| the ext-pass parallelisation | **only if** the owner keeps a whole-sweep ratio — WP-10 shows it cannot close (e) | owner | ≈ 0.30 |
| **C-A5** | the concrete refinement and the free `Γ`-model (contract work) | E5 accepted (it is) | not AU |

**Total ≈ 3.25 AU (≈ 4.15 at worst)** with the root-finder package ([S6] §6 decision 6's sketch,
3.0 / 3.9, plus [OD] E6-3's ≈ 0.25), inside one slot at the slot-4/5 scale (4.75–5.05), with room
for E8's continuation.

**Slot 7's golden events, item by item** ([OD] S6-3; [S6] §4.4):

* *Stage 0 — separate, add-only, not part of the changed-line event*: E7's golden objects (above),
  emitted at E7's acceptance. **Proof**: `golden_explain.py before after` exits 0 with **no
  `--allow-keys` and no `--accept-split`**, as slot 5's WP-3. Consequence:
  `EngineDeterminismValidation`'s digest moves (it digests golden-grid records) — the v1.9
  restated gate, "every arm agrees with arm 0 and every record equals the reference", applies.
* *Stage 1 — the recipe and the text-only items, the 62 `ext_json_*` lines only*:
  1. **the recipe change** — a **path-scoped** redaction reducing the record's **top-level**
     `settings` object to `{fingerprint}` (not `RedactJsonKeys`, which works at any nesting and
     would also redact the top-level `u_ell` verdict); the explain summary must show **only the
     settings block** changed, on exactly 62 lines;
  2. then, under the new recipe and with **zero** golden movement (proven by the gate): the
     `presentation` key and its hash-invariance arm (WP-2), the `predictions` key, the harness's
     `source` stamp (`ScopedMathSettings` / `ScopedUEll` with a source argument), and the
     campaign's `ext_json_*` equality arm ([OD] S6-5).
* *Stage 2 — value-bearing items, each its own commit, each explained object by object*:
  3. an **atlas-decided `proof_range`** — changes `final` flags: the 4 flips of WP-9 §4, of which
     `(24, 5)` ideal 1 is on the golden subgrid; the consumer must **re-run the driver** (WP-9
     finding 4, open item 7);
  4. **`S_sep` in the default Stage 2(3)** — vacuous at `ell ≤ 13` on the subgrid and M1 (WP-9
     §3), undecided at `ell ≥ 691` until the atlas reaches there;
  5. atlas labels in the record;
  6. the canonical split as the default report form in the record (the default stays `canonical`,
     [OD] E6-3);
  7. `predictions_mode` (E6).

  Items 3 and 4 move `ext_ideals`, `ext_certify` and the per-ideal E3 / E4b / E5 objects, not just
  the 62 JSON lines; items 5–7 are expected to move only the JSON lines, and the explain summary
  proves or refutes that.
* *Stage 3*: 8. whether the schema string moves to `hecke_ext/v3`.

**The slot-7 outcome (v1.11).** Slot 7 ran fifteen packages (WP-1 … WP-14 and the spec-first
WP-12a) inside the owner's 5.30 AU ceiling; WP-15 (C-A5) was not authorised. **Delivered**: E7
accepted and its add-only emission (WP-1, with the reference-level diff tool `golden_ref_diff.py`);
the staged re-baseline — stage 1 (WP-2), stage-2 items 3–7 and stage 3 (WP-3), each landed by the
lead after its gate, items 3–7 owner-signed; the root finder diagnosed by operation count and fixed
value-preservingly, `conway` routed (WP-4); the atlas at `ell = 691`, the tangent pairs,
`ext_compare.py` (WP-5); E2 (e′)'s `T_cell` and its measurement script (WP-6); the first ext
campaign published with the E6 dossier (WP-7); console C2b (WP-8); `ENGINE_API.md` §13 and its
review (WP-9, WP-10); the tool and minor-finding hygiene (WP-11); [E] v1.8.0-pre.1 / v1.8.0 /
v1.8.1 and [P] v3.5 (WP-12a, WP-12, WP-13); this close (WP-14). **Windows**: W1 (E6 (d) verdict,
MET), W2 (the campaign's publication run, PASS), W3 (E2 (e′), MET: 1.041 against `c = 1.25`), W4 (the closing window: T1 met under the
owner's ruling below, E6 (d) confirmed 41 / 0, T2 MET, 21 / 21 digests matched). **Deviations, recorded**: the E6 (d) cell list was not pre-written into [X] before W1
(pinned by a committed table instead; §6.2 E6 (d)'s v1.11 note); the lead's ledger file
`docs/implementation/slot7/golden_ledger.md` was never created (its rows are in the two re-baseline
notes and the close report §2); item 4's ledger row predicted six changed texts and one unchanged
ext digest, and all 62 texts and the digest moved — stated before the dump, because [E] makes
`s_sep` always present. Not a deviation, but a consequence the plan named in advance: item 6 moved
the split inside `run()`, so E6 (d)'s denominator is now `total_s − canonical_field_s`, by (d)'s
own rule.

**Slot 8, re-cut from the slot-7 outcome** (supersedes the slot-8 rows of the table above where they
differ; the owner sets the ceiling):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **E8's strategy decision** | the owner's ruling on proposals E8-P1 … P5 of the Fable investigation `docs/implementation/e8_ladic_investigation.md` (delivered, `c9829a9`; recommendation: direct per §13 — line 1 of the owner's two-line direction); P6 already restated by the owner | the investigation delivered (it is) | owner |
| **E8 item 2** | the composite `ModCtx` (`prime_power`, `is_field`, `valuation`, `unit_part`, `divide_exact`, a trivially copyable `ell^v` table), the Howell elimination on `DenseView` against `ref::howell`, `kernel_module` / `image_module` / `solve_multi_rhs_module` / `length` / `invariant_factors` (Smith rule, F2), the `[[2],[1]]` arm (M1), §13's minor wording (m1–m13) and (C2)'s design paragraph in §13 as a deferred requirement (P6 as restated) | the decision above; §13 reviewed (it is) | 0.75 |
| **E8 item 3** | the pipeline over `Z/ell^k`, **with the `ρ_n` repair** (F4 / M2 — an implementation limit of today's prime-only builder; P5: unit fast path, division-free Pascal oracle, `diag(ell, 1)` split), the cyclic-summand basis rule (M3), `charpoly` on the free quotient (P4), the certified `K`-mode (P2), `coefficient_ring` registered (key-additive, no golden line) | item 2 | 0.5 |
| **E8 item 4** | the reductions and the `a = b = 1` Bockstein as **map equalities** (F3), `bockstein_rank^0 == dim H^0(F_ell)` and `higher_torsion_count` (P2), the add-only golden objects at `(10, 691)`, `(6, 5)`, `(16, 5)` over `Z/ell²` **plus the positive controls `(30, 5)`, `(60, 5)`** (P3), `HeckeReductionValidation` | item 3 | 0.5 (slot 9 if the ceiling moves it) |
| **C-A5** | the concrete refinement and the free `Γ`-model (contract, with a referee) | the owner's refinement | not AU |
| **E9** | the refined descriptor, the degree-generic `τ`-table | C-A5 accepted | 2.5 (slots 8–9) |
| **C4** | hardening, `ConsoleErrorValidation`, every determinism arm, documentation | C2b accepted (it is) | 0.75 |
| **C5** | the extension bindings after E5's schema freeze, E7's console types (`dual`, `pairing`), the E8 types | C4 | 1–1.5 |
| **The engine program-cache hook** | a between-cells release in `kernel.cu` / the campaign driver (open item 1); **the prerequisite of (or bundled with) the ext-pass parallelism row below** | — | ≈ 0.1 |
| **`ell`-adic induction beyond a word (C2)** — slot 8+ | `mod ell^k` for arbitrary `k` (the descent of line 2; Hida families): base `ell^m` word-maximal, `⌈k/m⌉` levels, digit-convolution residuals, per-level valuation pivoting (design: `e8_ladic_investigation.md` §4.3); E8's word-sized direct route as its oracle | E8 items 2–3 (the oracle); the owner's go | not priced (owner) |
| **The integral line (line 2)** — slot 8+ | true computation over `Z`: `Z[1/6]` on the current model, `Z_2` / `Z_3` on a finer honest orbifold model, glued by descent, the Hecke action over `Z` — **as `docs/implementation/integral_line_design_brief.md` (incoming, then a Fable audit) and the owner fix it** | the brief, its audit, the owner | not priced (owner) |
| **Ext-pass parallelism** — **owner-requested candidate (2026-09-23)**; supersedes the conditional "E2 (e′) follow-up" of [S7] §3.16, which is no longer conditional on W3 | **Observation** (the lead, window W3): in the campaign's ext pass **one thread runs at 100 % while 32 sit idle** (≈ 1/32 of the box, ≈ 7 % CPU; the GPU idle by design, `ENGINE_DEVICE=cpu`); the job loop uses `jobs × threads` (`sweep_full`: 16 × 2) but takes only 3–4 s; the ext pass walks cells **sequentially**, and inside a cell the hot path — the `U_ell` coset tables at `ell = 10007`, the Sturm sweeps, the streamed `T_q` pipelines — is **host-serial**, not engine kernels; each `ext = true` `sweep_full` run took **3771 s / 3508 s** in W3. **Scope**: (1) parallelise the ext pass **across cells** (cells are independent; reuse the campaign's `jobs` / `threads` model) — expected gain close to an order of magnitude, bounded below by the slowest single `U_10007` cell (≈ 6–11 min) and by memory; (2) **the program-cache hook above**, prerequisite or bundled — the serial pass already reaches ≈ 8 GB RSS (open item 1, [KI] §4c); (3) **profile the serial hot path inside a `U_ell` cell** and move what can go onto the engine or run concurrently. **Acceptance**: output **byte-identity** with the serial run (every ext record and `analysis.txt` identical), and a **pinned, non-noise wall-time ratio** (numerator, denominator, invocation, reduction and constant stated before the measurement, per [S7] §2.4's five elements). **Relation to E2 (e′)**: (e′) bounds the pass's *overhead* over `Σ T_cell`, not the sum; this row attacks the sum and the idle cores — it is scheduled on the owner's request whatever W3's verdict, and W3's numbers (ext pass 3504.49 s; `Σ T_cell` 3367.28 s, of which the ten `U_10007` cells 3327.66 s) are its baseline | the hook (or bundled); W3's baseline | not priced (≈ 0.5–0.8, order of magnitude) |


**Slot 8, the outcome (v1.12).** Every row of the slot-8 re-cut above was scheduled by [S8] under
the owner's rulings of 2026-09-24 ([OD] S8-1 … S8-11, S8-+, S8-L1):

| Item | Outcome (v1.12) |
|---|---|
| E8's strategy decision | **RULED**: P1–P5 at the recommendation ([OD] S8-2) |
| E8 item 2 | **ACCEPTED** (WP-1) |
| E8 item 3 | **ACCEPTED** (WP-3, WP-3r; WP-12 review disposed of) |
| E8 item 4 | **4a ACCEPTED** (WP-4, R1); **4b → slot 9** |
| C-A5 | **DISCHARGED** as [C] v1.8.0 `sec:integral` (WP-9), on the unrefined `Xbulk` |
| E9 | **ABSORBED** into line 2 (§6.2 E9's v1.12 note) |
| C4 | **DONE** (WP-10); (d) in W3 |
| C5 | **slot 9** ([OD] S8-8) |
| The program-cache hook | **DONE** (WP-5); [KI] §4c RESOLVED |
| (C2) | not scheduled (trigger-based, [IB] OD-6 (a)) |
| The integral line | **M-0 DONE** (WP-7: `char_Z(T_p \| Λ^1)` by CRT, `HeckeIntegralCharpolyValidation`), **V-B DONE** (WP-8: `HeckeBredonTreeValidation`), **L2-C DONE** (WP-9) |
| Ext-pass parallelism | **DONE** (WP-6: `ext_jobs`, `ext_memory_mb`; byte identity shown); **WP-L1** (owner-approved) removed the `U_10007` walk; **WP-6b** accepted, no gain, off; T-P measured (W1): ratio 0.1896, reported not judged |

**Slot 9, re-cut from the slot-8 outcome** (supersedes the slot-9 rows of the table above; the owner
sets the ceiling):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **C5 + the Core batch** | the extension bindings (`.pair_homotopy`, `.h(q)`, `.q_max`, `.truncated`, `.degrees`, `.coefficient_ring`), E7's console types (`dual`, `pairing`), **E8's types** ([E] `sec:ring` (d)'s objects), and campaign / record support for `Z/ell^k` ([OD] S8-4); with it, one Core edit for the `set`-statement error position and **exit 5 for a legal but unexecutable `--set` value** ([OD] S8-D4) | C4 (done) | 1–1.5 (+ 0.25 for the campaign / record support) |
| **E8 item 4b** | the boundary and the cone over `Z/ell^k`, `obl:coneexact`(iv)'s non-field half | E8 items 2–4a (done) | ≈ 0.35 |
| **L2-1a** | `R`, `R_∂`, `ε` on `Xbulk` (ranks `5, 14, 19` per `n + 1`), degree-generic to `q_max + 1`; `Ĉ` assembly over any `ModCtx` | L2-C (done) | 0.5 |
| M0 | the groups over `Z` at 2 and 3, tests (1), (2), (6) | L2-1a; E8 items 2–3 (done) | ≈ 1.0 (slot 9 or 10) |
| The in-cell levers L2–L5 | from WP-6's profile report (L1 shipped) | the owner's go | ≈ 0.1–0.3 |
| A second ext campaign | under the parallel pass, if wanted | W1's verdict | — |
| Engine findings (WP-6b 2–3) | the elimination driver and `ScopedPassOptions`; the ext-determinism `gpu` arms' cache keys | the owner (cache keys move, never a value) | ≈ 0.1 |
| `PerformanceSmokeValidation` | skip its speed floors when `NDEBUG` is unset (the `Check` miss) | — | < 0.05 |

Line 2 after slot 9: L2-1b (1.0, gate M0), M1 (0.75; M1(a) after L2-1b, M1(b) additionally
[IB] OD-11 (a) and OD-3), L2-3 (1.0, gate M1(a)), L2-4 (0.5, gates M1(a), OD-9, OD-10) — slots
10–11, [IB] §6.1.

**Slot 9, the outcome (v1.13).** Every row of the slot-9 re-cut above was scheduled by [S9] under
the owner's rulings of 2026-09-24 ([OD] S9-1 … S9-13) and the approval S9-OA1:

| Item | Outcome (v1.13) |
|---|---|
| C5 + the Core batch | **DONE** in three lanes: C5a (WP-12, with the two named Core exceptions), C5b (WP-13), C5c (WP-8, WP-8c) |
| E8 item 4b | **ACCEPTED** (WP-4, route 1; R1 `762dbc3`); `obl:coneexact`(vii) over the ring **open** (ruling 3 (iii)); trimmed by WP-4t |
| E8 at `ell ∈ {2, 3}` (new in [S9]) | **ACCEPTED** (WP-3): `EquivariantCohomologyOnK` only, the Bredon object, against O7 |
| L2-1a | **DONE** (WP-10) |
| M0 | **DONE** (WP-11, a/s, accepted): 126 / 126 cells equal Appendix A |
| The in-cell levers | **L3, L2, L5 shipped** (WP-7); L4 recorded |
| A second ext campaign | **not run** (WP-16 optional; → slot 10 with W2) |
| Engine findings (WP-6b 2–3) | **FIXED** (WP-6), value-free |
| `PerformanceSmokeValidation` | **DONE** (WP-9) |

**Slot 10, re-cut from the slot-9 outcome** (supersedes the slot-10 rows above where they differ; the
owner sets the ceiling):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **L2-1b** | `τ̂` degree-generic, the strict lift, `Θ̂_g`, the class `e` ([IB] §6.1) | M0 (done) | 1.0 |
| **M1** | the integral Hecke action: M1(a) basis-free after L2-1b; M1(b) integer matrices (additionally [IB] OD-11 (a), OD-3); hosts `HeckeFreeModelValidation`'s tests (3)–(5) | L2-1b | 0.75 |
| **`HeckeOperatorOnK` over `Z/ell^K` at `ell ∈ {2, 3}`** | the Hecke action on the Bredon object (M1's need; refused since WP-3) | M1(a) | with M1(a) |
| **`obl:coneexact`(vii) over `Z/ell^k`** | the strict-pair and relative cross-routes and the relative sub-complex constructor over the ring (ruling 3 (iii)'s alternative (B)); E8 then complete without qualification | E8 4b (done) | ≈ 0.20 |
| **An `ell`-adic survey campaign under `Z/ell²`** | a published ring campaign on C5c's job loop | WP-8 (done) | ≈ 0.1 + a window |
| **`ext_u691`** | WP-16 as planned: the 45 over-budget `ell = 691` cells at `u_ell = budget_mb=8192`, an owner-signed publication in W2 | the owner lends the box | 0.10 |
| **The route-2 lever L4** | route 2's block rows on the consumer pool: single-cell latency only (`--bench ext`, the serial pass; ≈ 20–24 % of a cold `U_10007` cell), ≈ nothing on the parallel pass | the owner's go | ≈ 0.1 |
| **Cone / `ι` profiling** | at `(160, 691)` the cone (1.49 s) and the sign split (1.77 s) are 89 % of the cell and no lever reaches them: profile inside `EquivariantMappingCone` / `HeckeSignSplit` | — | ≈ 0.1 (report) |
| **C5 leftovers (a console package)** | the Core batch's `object_member` exception wrap (member-getter errors with `file:line:col`, and the type-level `resume` refusal); the structural members of ring handles if the owner lists them ([E] (h) amendment + binding); `run_campaign` / `campaign_plan` mapping `NotImplementedInThisBuild` uniformly to exit 5 | the owner (the Core edit is a named exception) | ≈ 0.15 |
| **WP-11's m-6 / m-7** | (T6) refusing on an object property instead of its own enum; arm (R) dropped (cite the two names' own lines) or the `HECKE_INTEGRAL_CAMPAIGN` coupling documented | — | < 0.05 |
| **The `hybrid` / `gpu` cache-key bit** | a ninth fingerprint bit (every cache key moves, never a value) | the owner | < 0.05 |
| **The fragments** | keep `Registry/Slot<n>/` + `cmake/slot<n>/` as the pattern (slot 10 opens `Slot10/`), or fold slot 9's into the central files at a quiet point | — | < 0.05 |
| **The golden landing rule** | land an add-only emission as a plain commit before its merge, or restate [S] §3.0 rule 11 to the lead's practice (two slots of the same deviation) | — | process |
| **(C2) / L1-X** | trigger-based; **the trigger has not fired** (no family computation needs `ell^k ≥ 2^64`) | the trigger | not priced |

Line 2 after slot 10: L2-3 (1.0, gate M1(a)), L2-4 (0.5, gates M1(a), OD-9, OD-10) — slots 11+,
[IB] §6.1.

**Slot 10, the outcome (v1.14).** Every row of the slot-10 re-cut above was scheduled by [S10] under
the owner's rulings of 2026-09-25 ([OD] S10-1 … S10-15) and the approval S10-OA1:

| Item | Outcome (v1.14) |
|---|---|
| L2-1b | **DONE** (WP-10 the strict lift `τ_Iso` / `Θ̂_g`; WP-13 the class `e` / `E_q`), certified exactly over `Z[Γ″]` / `Z[Γ]`; K1 did not materialise; no fallback |
| M1 | **M1(a) ACCEPTED** (WP-11, a/s): items 1, 2, 4, 5 in full, item 3 with X7 = commutativity (the `thm:relations` recursion → slot 11, M-3); tests (3)–(5) hosted. **M1(b) out** (OD-3 (c)) |
| `HeckeOperatorOnK` over `Z/ell^K` at `ell ∈ {2, 3}` | **WITHDRAWN** ([OD] S10-4: neither the cochain map nor the operator is lifted; [E] (b3), [C] `rmk:bredonhecke`) |
| `obl:coneexact`(vii) over `Z/ell^k` | **sentences 1–2 DISCHARGED** at `ell^k < 2^32`, every E8 point (WP-3); sentence 3 recorded unavailable over the ring (M-1); **E8 complete** |
| The `ell`-adic survey under `Z/ell²` | **not run** (W2 not lent; WP-4 a/s) |
| `ext_u691` | **not run** (W2 not lent; WP-5 optional) |
| The route-2 lever L4 | **SHIPPED** (WP-7), with the `ι` lever I-1 |
| Cone / `ι` profiling | **DONE** (WP-7): the sign split serial `FlatMatrix` elimination (→ I-1); the cone 70 % `ConeCertificate::verify` (→ C-1, slot 11) |
| C5 leftovers | **DONE** (WP-12): the Core exception at two sites, five members, the campaign handler |
| WP-11's m-6 / m-7 | **DONE** (WP-8) |
| The `hybrid` / `gpu` cache-key bit | **DONE** (WP-8, the ninth bit) |
| The fragments | **kept**: `Registry/Slot10/` opened by WP-1 |
| The golden landing rule | **checked mechanically** (`golden_landing_check.sh`, WP-1); no event to land |
| (C2) / L1-X | **DESIGNED** (WP-9, `ENGINE_API.md` §13.12, specified not built); the build is an owner question (open item 2) |
| T2 `(10, 691)` (new in [S10]) | **ATTRIBUTED AND FIXED** (WP-6): `ThreadPool`'s `.bss` placement; `alignas(64)` |

**Slot 11, re-cut from the slot-10 outcome** (supersedes the slot-11 rows above where they differ; the
owner sets the ceiling):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **M-3: `thm:relations` on the model** | `StrictLift` for the double cosets `diag(1, p²)` and `diag(p, p)` (`Γ_0(p²)`-type `Γ″`, the same induction and certificates); then X7 in full: `T_{p^{ν+1}} = T_pT_{p^ν} − p^{n+1}T_{p^{ν−1}}` on `H^q(C_I ⊗ R)`, `q ≤ 5`, at 2 and 3 (and whether it is a theorem there for `Θ_Iso,g` — [IB] §1.3 vs [C], WP-15 finding 6: a [C] statement first) | L2-1b, M1(a) (done) | ≈ 0.3 |
| **L2-3** | the pair and the cone over `Z` on the free model; the `oc1c` stabilisation report | M1(a) (done) | 1.0 |
| **L2-4** | `coefficient_ring = Z`, the record fields, the one add-only golden emission ([IB] OD-9) | M1(a), OD-9, OD-10 | 0.5 |
| M1(b) | integer Hecke matrices | [IB] OD-3 (a) / (b) and a [C] amendment (OD-3 (c) stands) | ≈ 0.5 (owner) |
| **L1-X** | the `u128` element type of `ENGINE_API.md` §13.12, four gated steps (engine 0.35, pipeline 0.50, grammar / campaign / console 0.10, validation + review 0.15). **Recommendation (WP-9): do not build unless the owner names a T-1 or T-2 computation with its cells**; alternatives: step 1 alone (0.35) as infrastructure | the owner's named computation; [E] v1.12's grammar; F-2 fixed first | ≈ 1.1 |
| **F-1** | `ModCtx<uint64_t>::mul` (`__umodti3`) → a Montgomery-64 `prep` / `mulp` pair in the composite row updates; value-preserving by construction (canonical in and out); ≈ 1.45× on the `u64` Howell | — | 0.05–0.10 |
| **F-2** | `hecke::ExactKthRoot`'s trial division (`CoefficientRing.cpp`): carry the ring as `(ell, k)` or a deterministic Miller–Rabin; a blocker for L1-X, harmless below `2^64` | with L1-X | < 0.05 |
| **C-1, the cone-certificate lever** | `ConeCertificate::verify`'s 12 span tests as host tasks (same shape as I-1); ≈ −12 to −15 % at `(160, 691)`, where the cone is now the largest phase (1.5 of 2.7 s) | the owner's go | ≈ 0.1 |
| C-2 | share `rank(X)` between `obl:iota`(iii) and the split — changes which certificate discharges (iii): a proof edit, needs a contract-level review | a [C] reading | ≈ 0.1 |
| E-1 | pad `ThreadPool::Slot` (heap back-to-back, ≈ 100 B) to a cache line — WP-6's candidate for region-bound cells, unevaluated | — | < 0.05 |
| **The `ell`-adic survey under `Z/ell²`** (WP-4) | a published ring campaign on C5c's job loop, owner-signed, in a W2 | the owner lends the box | ≈ 0.1 + a window |
| **`ext_u691`** (WP-5) | the 45 over-budget `ell = 691` cells at `u_ell = budget_mb=8192`, owner-signed, in a W2 | the owner lends the box | 0.10 |
| `(10, 691)`'s residual `ext_s` | ≈ +6 µs (1.04–1.08 against both REFs), 0.12 ms absolute, ungated, not bisected ([WP10-6] §5) | — | report only |
| Review / referee leftovers | **m-2** one `Integral/Model/PeriodicColumn.h` for the three copies of `decompose` / `dF_coeff` / the column homotopy (`IsotropyModel.cpp`, `StrictLift.cpp`, `PeriodicityClass.cpp`); **m-3** `ENGINE_CHECK(s_1 = I)` in the Schreier check; **m-4** a comment on the `W`-coordinates' uniqueness; **m-10** `PeriodicityClass.cpp`'s 64-element conjugator cap (drop or say what it proves); **m-11** `HeckeConeAction.h`: the well-definedness of `N` on classes; **m-12**'s stronger half, a route-3 negative seam (`E` forced to 0 must fail R3.3); **m-14** merge the two `RequireRingRegime` statics; **m-18** label X7's cyclic-coordinate check a consistency check; `cone_output_diff.sh`'s normaliser learns `seconds=` / `wall_s=` ([WP10-7] finding 7) | — | < 0.1 together |
| **The placement lesson** (process) | a head-to-head of two binaries compares like with like only when both place `ThreadPool::global()`'s pool alike (`nm -S <bin> \| grep _ZZN6engine4tape10ThreadPool6globalEvE4pool`); since `ce73c71` the layout is pinned, but a REF older than `ce73c71` is not | — | process |
| `obl:coneexact`(vii) sentence 3 over the ring | the pairing and the contragredient over `Z/ell^k` | not scheduled | — |

Line 2 after slot 10: M-3 (≈ 0.3), L2-3 (1.0, gate M1(a) — met), L2-4 (0.5, gates M1(a), OD-9,
OD-10) — slots 11+, [IB] §6.1.

**Slot 11, the outcome (v1.15).** Every row of the slot-11 re-cut above was scheduled by [S11] under
the owner's rulings of 2026-09-25 ([OD] S11-1 … S11-13):

| Item | Outcome (v1.15) |
|---|---|
| The Dickson/θ line (new in [S11], the headline) | **ACCEPTED** (WP-5, WP-6), under [C] v1.11.0's Part VII written and refereed first; every checkable item of `rmk:thetacheckable` held |
| The congruence census (new in [S11]) | **ACCEPTED**: edition 1 published and owner-signed (WP-7); W2's campaigns and data set published and owner-signed (WP-8); **edition 2 → slot 12** ([OD] S11-9) |
| The examples document [EX] (new in [S11]) | **PUBLISHED 1.0.0**, refereed (WP-20) and owner-signed |
| M-3: `thm:relations` on the model | **DONE** (WP-11): lifts for `diag(1, p²)`, `diag(1, p³)`, `pI`; X7 in full on `H^q(C_I ⊗ R)`, `q ≤ 5` |
| L2-3, L2-4, M1(b) | not scheduled in slot 11 (carried) |
| L1-X | **superseded** by the (C2) digit induction ([OD] S11-3): step 1 (the native `u128` layer) **BUILT** as the third width and oracle (WP-18a); arbitrary `k` **BUILT** by (C2) (WP-18b engine, WP-18c pipeline, precision bound, grammar `k ≤ 4096`, campaign, console); old step 2 not built |
| F-1 | **DONE** (WP-12) |
| F-2 | **DONE** (WP-12) |
| C-1, the cone-certificate lever | **not shipped** (a/s; E5 (d)'s 3.5 % memory headroom; needs a memory measurement and CheckThread) |
| C-2 | not scheduled (a [C] reading first) |
| E-1 | **not shipped** (a/s; needs a quiet T2 window with the placement check) |
| The `ell`-adic survey under `Z/ell²`, `ext_u691` | done in slot 10's W2 (v1.14.1) |
| `(10, 691)`'s residual `ext_s` | report only (W1's T2) |
| Review / referee leftovers (WP-13) | **re-carried** (WP-13 did not run: the give-way of the (B) re-ruling) |
| The placement lesson | **checked mechanically**: `pool_placement_check.sh` (WP-1), step 0 of `slot11_close_window.sh` |
| `obl:coneexact`(vii) sentence 3 over the ring | not scheduled |
| WP-16, console θ verbs (a/s) | **not built** (gave way); [P] v3.9 records the phase as specified |
| Hida (decision 2) | not started (no head start, [OD] S11-2); `rmk:ordtorsionfree` ([C] v1.11.1) and WP-18c's certified ordinary idempotent on the digit route are its first bricks |

**Slot 12, re-cut from the slot-11 outcome** (supersedes the slot-12 rows above where they differ; the
owner sets the ceiling; **Hida may move to slot 13 by the owner's leave**, [OD] S11-12):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **L1-H: the Hida chapter** | [C] `sec:hida` (Part VII's successor): the ordinary projector on `H^•(Γ; Sym^n ⊗ Z/ell^m)`, control, weight independence along `k ≡ k' (mod (ell−1)ell^{m−1})`, the level-1 versus `Γ_0(ell)` stabilisation, the lattice; contract first, Fable referee | [C] v1.11.1 (`def:ordinary`, `prop:ordinary`, `rmk:ordtorsionfree`, `rmk:ordinaryeis`) | ≈ 0.5 |
| **The ordinary projector with the certified precision bound** | `open:ordprecision`'s remaining half: an exponent computable **from the cell, before the run**; the corrected exponent of the plan (the `ell`-part `ell^{K−1} · ell^{⌈log_ell r⌉}`, not `r!`; [S11] line 1232, WP-14 pass 2); WP-18c's route supplies `K = k + e_max` and the certified idempotent | L1-H | ≈ 0.3 |
| **Towers at `ell ∈ {5, 7, 11, 13}`** ([OD] S11-2 2b) | ordinary parts across weights mod `(ell−1)ell^{m−1}`: 5 and 7 the Eisenstein check alone (`U_ell` nilpotent on `H^0`), 11 and 13 the cuspidal ordinary towers in `n ≤ 200`; the owner's congruences across weights (project note, 2026-09-25) | L1-H; the digit route (built) | ≈ 0.3 + a window |
| **`(700, 691)`, weight 702** | over `F_691` with **the `U_ell` memory lever** (WP-10 of [S11], not run: measure first, then rank-`≤ m` blocks); over `Z/691²` a/s after a ladder `n = 100, 200, 300`; rule 19 (memory > 40 GB needs the owner) | the lever; W3 | ≈ 0.4 + W3 |
| **`ell = 2411`, non-ordinary** | `(10, 2411)` over `Z/2411^{1,2,3}` (`U_2411` ≈ 0.36 GB by the model); optionally `(2420, 2411)` | L1-H | ≈ 0.1 |
| **Census edition 2** ([OD] S11-9) | `HeckeCensusSplit` and WP-6's θ-image over the W2 cells (a cell-list option on the `HECKE_CENSUS_SPLIT_ALL` arm), the Glover columns; `congruence_census.py` over `ext_first` + `ext_u691` + `ext_census_l7l11` into `edition2/`; **`Z/ell^k` depth above `n = 64`** (a `Z/ell²` survey of the new cells; 212 rows read `not_surveyed`); owner-signed | W2's data (published) | ≈ 0.1 + a window |
| **The 184 heuristic `ell = 5` ideals** | a new finality argument for Eisenstein systems that meet `H^0` (the `sturm` cap is not the lever — W2's Q2); a [C] / [E] statement first | a contract statement | ≈ 0.2 (research) |
| **The full-Hecke-algebra Loewy-length-3 datum in-tree** | the WP-20 referee's forms-side datum (`(142, 7)`: the forms' Hecke algebra has Hilbert `(1, 3, 2)`, Loewy length 3; `(82, 7)`: embdim 3) reproduced by a registered validation, so [EX]'s `RCOMP` rows become pipeline data | a forms-side Hecke algebra (the cohomological `A` is its quotient) | ≈ 0.2 |
| **WP-15 F-1: the θ / census ring refusals** | each closure member of [E] `sec:ring` (b1) refusing a ring by a named guard naming itself, with an arm (`HeckeCensusSplit` through the driver's guard; `QuotientL` through the "contragredient" guard; the relation list and fibre builder unguarded) | — | < 0.1 |
| **The console `uint32_t` gap** | `Z/5^14 … Z/5^27`, `Z/691^4 … Z/691^6` at the console ([P] Q9) | **decided (a), owner 2026-09-26; built post-close by S12 WP-17 (`8fcad8d`, `bind::GateTypeOnWide`)** | done (struck from the owner items, v1.17.1) |
| **Digit-handle costs** | `hecke(H, p)` on a digit handle recomputes the cell per operator (WP-14 pass 2 m-2); `RunDigitPipeline` books the Hecke time into `t_cohomology` | — | < 0.1 |
| **(C2) extensions** | the digit route over the cone, the boundary, the pairing and the ext driver; the recorded levers (AVX-512 digit GEMMs, a blocked / parallel replay, `ENGINE_API.md` §13.11.9) if 18c's measurements ask | the Hida chapter's needs | ≈ 0.3–0.6 |
| **C-1, E-1** | as in the slot-11 re-cut (not shipped) | memory measurement + CheckThread; a quiet T2 window | ≈ 0.1 |
| **WP-16, console θ verbs** | `dickson_les(n, ell)` → `DicksonLES`, `theta(H, H_up)`; script `027_`; one `ConsoleErrorValidation` arm; [P] v3.9's rows (`ell < 5` exit 3 — the build now agrees) | — | ≈ 0.15 |
| **Review leftovers** | slot 10's (WP-13, re-carried: m-2, m-3, m-4, m-10, m-11, m-12's route-3 negative seam, m-14, m-18, `cone_output_diff.sh`'s normaliser) and slot 11's (WP-14 m-1 unused `tmp`, m-2 arm (C)'s extra oracle checks beyond `2^127`, m-5's code half, m-6 the JSON reader's escapes, m-7 the explicit target-system check, m-8 `StrictLift`'s central `N_`, m-9 the per-cell aggregate; pass 2 m-6 the class-level Glover sum) | — | ≈ 0.1 together |
| **`label_census.sh`'s exit code** | confirm or refute the observed "exit 0 on a failing census" (open item 8); make every gate pipe-safe | — | < 0.05 |
| **Line 2** | L2-3 (1.0, the pair and the cone over `Z` on the free model), L2-4 (0.5, `coefficient_ring = Z`, [IB] OD-9's add-only emission), M1(b) (owner, OD-3) | M1(a), M-3 (done) | 1.5 |

**Slot 12, the outcome (v1.16).** The slot ran under the lead's rulings on the owner's behalf ([OD] S12-L1 …
L15, ratification pending); strictly serial, fourteen packages (WP-1 … WP-8 planned, WP-10 … WP-14 lead-added,
WP-9 the close):

| Item | Outcome (v1.16) |
|---|---|
| L1-H: the Hida chapter | **foundation WRITTEN, refereed** ([C] v1.12.0-pre.2 `sec:hida`; **released as v1.12.0, owner sign-off 2026-09-26**); control / weight independence as theorems, `Γ_0(ell)`, the lattice → slot 13 |
| The ordinary projector with the certified precision bound | **BUILT** (WP-4): the pre-pass (`e_max` before the run), `N_ord`, `U^{N_ord}` = WP-18c's idempotent; `open:ordprecision` answered at `ell ≥ 5`, `n ≥ 1`, pending release |
| Towers at `ell ∈ {5, 7, 11, 13}` | **BUILT** (WP-5), mod `ell` and mod `ell²`; every (Hi) prediction held |
| `(700, 691)` | not run (> 40 GB, rule 19; the `U_ell` memory lever not measured) |
| `ell = 2411`, non-ordinary | **DONE** at `(10, 2411)` over `Z/2411^{1,2,3}`; `(2420, 2411)` not run |
| Census edition 2 | **PUBLISHED** (WP-6 built; S12-census2 regenerated for `hecke_ext/v4` and published, owner-signed 2026-09-26); the depth window owner-gated |
| The 184 heuristic `ell = 5` ideals | **ARGUED** (WP-12 proposal v2, refereed WP-13): (d0) unconditional, (d1) conditional on Proposition T; 376 / 376 certified as evidence (WP-14); **LANDED (v1.17, S12-FIN)**: [C] v1.12.0 proves Proposition T; (d0) / (d1) in the driver, `hecke_ext/v4`, one golden event |
| The full-Hecke-algebra datum in tree | **DONE** (WP-7), extended to the 655-row forms census (WP-12) |
| WP-15 F-1 (θ / census ring refusals) | **DONE** (WP-1) |
| The console `uint32_t` gap | ~~not touched (L5, owner)~~ **DONE** (S12 WP-17, `8fcad8d`; v1.17.1) |
| Digit-handle costs, (C2) extensions, C-1, E-1 | not scheduled (carried) |
| WP-16, console θ verbs | **BUILT** (WP-8) |
| Review leftovers (slots 10, 11) | re-carried |
| `label_census.sh`'s exit code | **CLOSED** (WP-1: exits 1, bare) |
| Line 2 | not scheduled (carried) |

**Slot 13, re-cut from the slot-12 outcome** (supersedes the slot-13+ rows above where they differ; the owner
sets the ceiling and ratifies [OD] S12 first):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **Owner sign-offs first** | ~~[C] v1.12.0 release (`sec:hida`, `open:ordprecision` → answered)~~ **DONE** (owner sign-off 2026-09-26); census edition 2 publication **DONE** (owner sign-off 2026-09-26, S12-census2); still owner-gated: [EX] next edition, the first Hida emission (add-only, the ledger's list) | the owner | — |
| **Full Hida, contract** | [C] `sec:hida` part 2: control and weight independence as theorems at level 1 (the `\LIT` locators verified against a source in `docs/literature/`), the `Γ_0(ell)` stabilisation, the lattice; towers mod `ell³`; Fable referee | [C] v1.12.0 | ≈ 0.5 |
| **Full Hida, code** | towers mod `ell³` and `T_p`, `p > 3`; `Γ_0(ell)` on the model (or the level-1 ↔ level-`ell` comparison); the pre-pass beyond `2^64` via `engine::ladic`; `HIDA_TOWER` catalogue (publication owner-signed) | the contract | ≈ 0.4 |
| **`(700, 691)`, weight 702** | the `U_ell` memory lever measured first, then rank-`≤ m` blocks; rule 19 (> 40 GB needs the owner); W3 | the lever | ≈ 0.4 + W3 |
| **`(2420, 2411)`** | the non-ordinary example at large weight | the lever | ≈ 0.1 |
| **Finality landing** | ~~Proposition T refereed → [C]; [E] certificate routes (d0) / (d1); the code; the golden event~~ **DONE** (S12-FIN, owner-approved 2026-09-26): [E] v1.13.0, `HeckeExt/HeckeFinalityRoutes`, `hecke_ext/v4`, golden event R1 (62 `ext_json_*` lines), ExtDet re-pinned | — | done |
| **C-F9** | the conjecture candidate `m_A² = 0` (proposal §7): the Loewy length of `V` on the `±` parts against the Serre weights of `ρ̄_m` | the census | ≈ 0.2 (research) |
| **Console Q9** | **closed**: owner ruled (a) 2026-09-26, built by S12 WP-17 (`8fcad8d`) | — | done |
| **Carried** | digit-handle costs; (C2) extensions (cone, boundary, pairing, ext driver); C-1, E-1; review leftovers (slots 10, 11; WP-10 A14); the cross-config line with slot 12's names; CheckThread on the tower runner | — | ≈ 0.5 together |
| **Line 2** | L2-3, L2-4, M1(b) (owner, OD-3) | M1(a), M-3 (done) | 1.5 |

The roadmap rows below (R-C1 … R-U1b) are unchanged; rule 23 binds.

**Slot 13, the outcome (v1.18).** The slot ran on the owner's answers of 2026-09-26 (Q1–Q14 accepted, two
amendments; [OD] S13); strictly serial apart from Q13's WP-3 ∥ WP-4; fifteen packages (WP-1 … WP-15; WP-11 grew a
referee and a response inside the slot):

| Item | Outcome (v1.18) |
|---|---|
| Owner sign-offs first | [EX] next edition carried (Q9); the first Hida emission **DONE** (golden R1, Q5) |
| Full Hida, contract | **WRITTEN, refereed, RELEASED**: [C] `sec:hidafull`, v1.13.0-pre.1 → pre.2 → **v1.13.0** (Q14); control / weight independence as verified literature, level `ell` by Shapiro, the stabilisation, the lattice, (Hi7)–(Hi12) |
| Full Hida, code | **BUILT**: towers mod `ell³`, `T_5` / `T_7`, the lattice datum on `Sym^n` and on Hida's `L_n` with a decision procedure, the pre-pass beyond `2^64` (WP-5); `Γ_0(ell)` on the model, the old space, the stabilisation (WP-6); every tested (Hi7)–(Hi11) item held; the `HIDA_TOWER` catalogue **staged**, publication owner-signed (Q7) |
| `(700, 691)`, weight 702 | **DONE** behind the lever (WP-4, WP-10): over `F_691` 13.65 GiB / 61 s and `Z/691²` 33.45 GiB / 47 min; (Hi11) held |
| `(2420, 2411)` | **deferred to the cluster roadmap** (lever band 647 GiB; the coset tables' full-rank `ρ_n` is the floor) |
| FIN_audit G2 | **CLOSED** (WP-7): `hecke_ext/v5`, `boundary_data`, `verify()` code 32; golden R2 |
| Re-emission of the record sets | **DONE, PUBLISHED** (WP-8, `9526242`): three `_v5` sibling sets; `EDITION2_NATIVE` 3285 / 3285 |
| C-F9 | **HELD** 654 / 654 (WP-9); [E] `pr:latticesplit` `\CONJ`; the Serre-weight mechanism not confirmed |
| The `mixed` finality case | **ARGUED, REFEREED** (WP-11, Proposition M, v2); specified only (Q10) |
| Carries | partly done (WP-12); the rest re-carried below |
| Line 2 | not scheduled (Q12) |

**Slot 14, re-cut from the slot-13 outcome** (supersedes the slot-14+ rows above where they differ; the owner sets
the ceiling and signs the open items first):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **Owner sign-offs first** | the Hida tower catalogue (staged, Q7); [E] v1.14.0 release; [EX] next edition with the towers (Q9); ratification of [OD] S13's in-slot rulings | the owner | — |
| **General level `N`, contract (O1 / O2)** | the **Manin–Merel Heilbronn-matrix route**: transcribe the Hecke action on the cokernel (Manin-symbol) presentation of `prop:levelorbit`(2) into [C]'s conventions and prove it agrees with `prop:levelcorrespondence`(4)(d) — the contract task of the size of `def:cosetreps` that `rmk:levelscaling` (O2) records; locators (Manin, Merel §2, Stein, Cremona) verified; Fable referee (scalability again) | [C] v1.13.0 | ≈ 0.5 |
| **Composite-`N` coset tables (O3)** | `HeckeCosetTables` at composite `N` (CRT + `SL_2(Z) → SL_2(Z/N)`, [C] `def:levelellmodel` as amended by m2); the monomial / orbit-wise `Ind` of `rmk:levelcost`(2)–(5) behind `HeckeLevelEll`'s plug points; `Γ_0(N)` at small composite `N` against the group-cocycle route | O2's contract | ≈ 0.5 |
| **Proposition M's landing** | (d2) "Dickson-mixed" in the driver, bundled with the next record event (Q10); only when a campaign produces a non-final `mixed` row, or on the owner's word | the owner | ≈ 0.3 |
| **The `p ≠ ell` digit-cell split** | `RunCell` split at the Hecke step (an incremental API on `DigitCell`), so a digit handle's `hecke(H, p)` for a different `p` shares the cell (WP-12's re-carry) | — | ≈ 0.2 |
| **`(2420, 2411)`** | on the cluster roadmap (R-C3), after a streaming lever for the coset tables' unimodular `ρ_n` (the 34 B / entry / coset floor) and the `n = 2420` cohomology (≈ 26 GiB); rule 23 binds | R-C1 … R-C3, the owner | — |
| **Hida catalogue, mod `ell³` at 7 in the suite** | the `ell = 7` (Hi7) pair (187 s) into a `slow` arm if the owner admits > 3 min; [EX] tower pages | Q7, Q9 | ≈ 0.1 |
| **Carried (re-carried by WP-12)** | review leftovers slot-10 m-2 (the three periodic-column helper copies), m-11, m-12, m-18; slot-11 m-2, m-7, m-9; pass-2 m-6 (class-level Glover sum); A14 at `symmetric_power`; (C2) extensions (cone, boundary, pairing, ext driver); C-1, E-1; the census `Z/ell²` depth window above `n = 64`; `ext_sturm_l5` in an edition; the cross-config line + CheckThread on slot 13's names | — | ≈ 0.6 together |
| **Line 2** | L2-3, L2-4, M1(b) (owner, OD-3) | M1(a), M-3 (done) | 1.5 |

The roadmap rows below (R-C1 … R-U1b) are unchanged; `(2420, 2411)` joins R-C3's named cells; rule 23 binds.

**Slot 15, the outcome (v1.20).** The slot ran on the owner's rulings of 2026-09-30 (Q1–Q15, all at the recommendation, Q2 / Q3 / Q5 / Q7 / Q11
as ruled; `s15/owner_rulings_0930.md`); the waves of [S15] §3, at most five agents, the two Fable windows (WP-4, the WP-5 audit) apart:

| Item | Outcome (v1.20) |
|---|---|
| Nebentypus, contract (C-3) | **WRITTEN, refereed, RELEASED**: [C] `sec:nebentypus` (general `N`, `chi : (Z/N)^x -> F_q^x`, `q = ell^d`, Teichmüller lift over `W_K(F_q)`, no layering), v1.15.0-pre.1 → pre.2 → **v1.15.0** (Q2); (NB4)–(NB6) `\CONJ`; **not built** (slot 16, Q3) |
| Saturation statements (P15, P17, P18, P20) | **PROVED, refereed, RELEASED**: [C] `sec:saturation` (`prop:saturation`, `prop:satdefect`, `lem:heckerankone`, `lem:freepart`, `cor:stablecert`, `prop:cohforms`, `prop:hidaalgconst`, `rmk:thetaforms`) |
| Certified `stable` | **BUILT** (WP-5, Q4): `stable_cert=certified` on `cor:stablecert`'s B1 form; Fable audit ACCEPT WITH REPAIRS, repaired; `HeckeRingLoewyValidation` 181 checks |
| Digit route of the `Z/ell^K` Hecke algebra | **BUILT** (WP-5): `ell^K >= 2^64` through `LadicCell::RunCell` at `K`; `u64` = digit lines on three cells |
| WP-14c in C++ | **BUILT** (WP-6): `HeckeHidaComponents`, bignum-free `B_k/k mod ell^K`, (U1)–(U3) readings; `HeckeHidaComponentsValidation` 157; Washington Thm 7.10's locator still VERIFY-loc |
| Level `N` at scale | **BUILT**: `H_{N,p}` (WP-7, (LN3) both halves), the sparse cokernel and the level-change maps (WP-8), (R3) at scale over 1881 cells, `N <= 10^4` (WP-9; `e >= 3` = WWE Table 1) |
| Forms side | **PROVED and GATED** (WP-19, WP-20): `cl:mkfaithful`, `cl:formsF9` with its torsion term; the corrected F9 gated on every `H^1` row; `saturated` / `mult_one` |
| Campaign findings | (WP-12, WP-13) **`pr:latticesplit` refuted as stated** at `ell = 37` (C-F9 fails at `(654, 37)` ideal 8, three-way: records, forms side, lattice run); the F1 onset law (24 / 24 on existing data; CONJ); Prop. D rationality PROVED; S4 at `(59, 16)` literature; Bellaïche–Khare closed (Vandiver verified below `2^31`) |
| Census edition 3 | **C3-0 only** (WP-14: schema and builder, editions 1 / 2 reproduced); C3-1 / C3-2 wait for D1 |
| Cluster | RB1–RB4 submitted by the owner 2026-09-30; nothing returned inside the slot; WP-C18 / WP-C19 not run (Q7) |
| Stretch | WP-16a (GPU G1), WP-16c (carries): **not run** |

Slot 16's packages and waves: `docs/implementation/slot16/00-slot16-plan.md` v1.x.

**Slot 16, re-cut from the slot-15 outcome** (supersedes the slot-16+ rows above where they differ; the owner sets the ceiling and answers
the open questions S15-O1 … O5 first):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **Owner sign-offs first** | **done 2026-10-01 (v1.20.1)**: the `pr:latticesplit` edit, [E] 1.16.0 and [EX] 1.2.0 released, the Lean questions Q1–Q14 ruled; S15-O1's code change **landed** (v1.20.2: `HeckeRingLoewyDigitSlowValidation`, `slow`; target 64 s, owner 2026-10-01); left for slot 16: the [U] / [E] CONJ proposals (U-1), (E-2), (E-3) of `slot15/WP-12_U_E_proposals.md` | the owner (ruled) | 0.1 |
| **Nebentypus code (WP-10 of [S15])** | `Hecke/HeckeNebentypus`: the `chi`-twisted fibre on `Gamma0LevelN`, `<d>`, `T_p` with `chi(p)`, `U_p`, over `F_q` and `W_K(F_q)`; `HeckeNebentypusValidation` ((NB1)–(NB3), (NB5), (NB6), an independent group-cocycle route with a character); `HECKE_NEBENTYPUS_CELLS`; validation-only. Its (NB5) first run fixes the `S_k(N, chi)` / `S_k(N, chi-bar)` dictionary **against the Lean bridge statement** (L16-2) | [C] v1.15.0 (released) | 1.0 |
| **Weight shift on cohomology; `m = 2` (WP-11 of [S15])** | (NB4) at level `ell` with `omega^i`; WP-C16's SPEC items (`m = 2` on non-ordinary dihedral blocks, `H^1_m = A_W^2`) on the certified `Z/ell^K` route | the nebentypus code | 0.7 |
| **General `N`** | level `N` beyond `N <= 10^4` at weight 2 (Q5): higher weight, composite `N` at scale, `alpha_d` (`d > 1`) on the cokernel presentation (pre.3's unrefereed sentence to the referee first), the pinned `kappa_N` as code (an entrywise model = presentation comparison) | the referee of pre.3's sentence | 1.0 |
| **[U] part 2** | CM components, CM ∩ GL(2), CM ∩ Eisenstein at tame `N >= 3` (Q5) | [C] `sec:nebentypus` released | contract 0.5 |
| **The `ell`-local isotropy model** | [Q1n] §4 at `ell = 3`, beside the Moerdijk–Pronk refined model (Q11); contract first | — | 0.7 |
| **Census edition 3, C3-1 / C3-2** | **DONE 2026-10-01 (v1.20.2; slot-15 WP-15)**: published beside edition 2, 80 293 rows, complete at 61 … 103, partial at 17 … 59 (3064 / 7350 C1 cells missing). **Left: edition 3.1**, add-only — RA1–RA2 / RS1–RS3 once returned, plus the cells arm (T) dropped (next row); rerun `wp15/runs/stage.sh` + `build.sh` with the new sets appended | the cluster returns; the arm-(T) fix | 0.3 |
| **Arm (T)'s `u_ell` (→ census 3.1)** | `HeckeFormsHeckeAlgebraValidation` arm (T) re-runs the driver at the default `u_ell`; on 230 cells at 61 … 103, `n ≥ 302` it drops `U_ell` (the records used `budget_mb=16384`), the anemic algebra differs from the row's and the census checks fail (rc 1). Fix: a `u_ell` setting / the row source set's budget for arm (T) (C++); then `saturated` / `mult_one` on those cells and at `n > 500` (≈ 40 CPU-h for all of `n ≤ 700`), filled into census 3.1 | — | 0.3 |
| **Console verb `hecke_ring_algebra` + script 029** | the `Z/ell^K` Hecke-algebra route (`HeckeRingHeckeAlgebra`) as a console verb, script 029 with a first-freeze transcript, `console.md` regenerated (Q6; deferred from WP-15) | — | 0.3 |
| **Saturation-defect Tor term (new package, owner-approved 2026-10-01)** | on torsion-free blocks `I_m := Tor_1^{Z_ell}(T^sat/T_m, F_ell) = (T_m ∩ ell T^sat)/ell T_m = ker(T_m/ell → End(Λ_m/ell))`: dim, minimal generators as polynomials in `T_q − a_q`, first radical layer, Loewy length, socle, annihilator, principal?; the length of `T^sat/T_m` with its `ell^j`-filtration via `A_K = T_m/(T_m ∩ ell^K T^sat)` (`HeckeRingHeckeAlgebra`); over `F_ell` the kernel of the joint-algebra projection in `HeckeFormsHeckeAlgebraValidation`. Checks: WP-12's hidden-chain cells (`I = m`), the `ell = 37` Kummer blocks (`I = 0`). Census columns. Torsion blocks treated separately. Distinct from `Tor_1^{T_m}(Λ_m, k)` (freeness, `mult_one`). A Lean target candidate | [C] `sec:saturation` (v1.15.0) | 1.0 |
| **`HeckeCensusLatticeValidation`'s operator set** | take the `u_ell` budget from the TSV row's source set (np sets: 16384; today only the `ext_u691` set gets one, so np rows run without `U_ell` and their ideal ids shift), or join rows by eigen-system instead of by id; print the operator set on the `EFFECTIVE` line (WP-12 §8.1: locally `u_ell = off` merges cluster ideals 17 / 18 and shifts every later id). Needed before C-F9 runs on census-3 rows beyond the cheap ones | — | 0.2 |
| **The 17 `ell = 37` Loewy-4 lattice cells** | `n = 656 … 676, 690 … 700`, C-F9 on the cluster (≈ 116 core-h, ≈ 8.5 GB each; WP-13's case env) | **WP-C19** (S15-O4, ruled 2026-10-01); the re-plan waits for RB1–4 (S15-O5) | cluster |
| **Cluster** | **WP-C18 done for RB1–RB4** (v1.20.2; C1b complete). **WP-C19, the October plan**: RA1–RA2 (C1a `ell = 37 … 59`, 1736 cells, ≈ 1183 core-h planned, ≈ 1300 at RB's ×1.10), RS1–RS3 (`ell = 17 … 31`, 1750 cells, ≈ 2100 planned, ≈ 2300 at ×1.10), the 17 `ell = 37` lattice cells (≈ 116 core-h, previous row); kit fix: the `T_2` job loop after the ext pass at **`jobs = 40`** (it ran 11 × 3 of 128 cores, 0.61–0.67 h against 0.25 h; ≈ 58 core-h saved per chunk) or 0.70 h in the allowance; walls × 1.10, RSS margin × 1.3 kept (it held, peak / model ≤ 1.242). **Quota inference**: four 7 h × 128-core jobs admitted at once at 00:03 CEST 2026-10-01 put October's enforced limit at **≥ 3584 core-h** (WP-C12 proved only 3200); October already carries RB's 2428 core-h if the reset is at local midnight; if the nominal 5000 holds, ≈ 2570 remain — enough for RA1 + RA2, not also RS1–RS3 (≈ 800 short). To be confirmed by `sacct` / `scontrol show assoc_mgr` on the login node (owner). WP-C20's sheet follows | the owner submits (rule 23) | 0.3 per return |
| **Open citations** | Washington Thm 7.10's locator (WP-6, scanned PDF without a text layer); Serre LNM 350 (WP-4 §7.1); Haberland (WP-12 §8.4); the (107, 28) S4 proof; the curvilinearity argument at 37; Gross (companion forms, from ≈ 2026-10-07) for F1's post-drop reading | the sources | 0.3 |
| **The Lean programme, packages L16-0 … L16-6** | `docs/implementation/lean/00-lean-programme-plan.md` §4.1: L16-0 toolchain and skeleton, L16-1 FLT harvest survey, L16-2 the convention layer (Fable audit), L16-3 the literature register, L16-4 the first differential oracle and checker, L16-5 Fable audit, L16-6 (stretch) statement skeletons; at most two Lean seats | the plan's Q1–Q14, **ruled 2026-10-01 at the recommendation** (plan v1.0) | ≈ 2.5 |
| **Stretch / carried** | GPU G1 (Q10); the `p != ell` digit split and the (C2) extensions (Q14); Proposition M's landing; line 2 (OD-3); the review leftovers re-carried by slot-14 WP-12; add-only golden candidates (level-`N` points, certified `LOEWY_RING` lines; each owner-gated) | — | — |

**[OD] S15 — the slot-15 decision register.** Owner decisions: **S15-Q1 … Q15** of 2026-09-30, as recorded in v1.19.1 (each at the
recommendation; Q2, Q3, Q5, Q7, Q11 as ruled). Lead rulings inside the slot, for ratification: **S15-L1** one C-F9 confirmation at `(654, 37)`
suffices locally; the other 17 Loewy-4 cells go to the cluster list (WP-13). **S15-L2** WP-8's validation is its own name
(`HeckeLevelNSparseValidation`), so the roster is 162, not the forecast 161. **S15-L3** [C] v1.15.0 is released at the close with pre.3's
unrefereed WP-8 sentence listed as such (it adds no statement and moves no tag). **S15-L4** [E] / [EX] are not released at the close: the
`pr:latticesplit` edit is the owner's. **S15-L5** `HeckeRingLoewyValidation`'s tier is left as is (S15-O1 to the owner). Open questions for the
owner: **S15-O1 … O5** (v1.20 (4)).
**Ruled 2026-10-01 (v1.20.1)**, every item at the recommendation, and the lead rulings S15-L1 … L5 thereby ratified:
**S15-O1** ruled — arm (C3) of `HeckeRingLoewyValidation` to the `slow` tier or behind an env hook (slot-16 code item);
**S15-O2** ruled — the `pr:latticesplit` edit made ([E] 1.15.1-pre.7: refuted as stated, restated as (R), `pr:kfonset`), [E] **v1.16.0** and [EX]
**1.2.0** released, [U] untouched (its (U-1) to slot 16);
**S15-O3** ruled — the Lean plan **approved, v1.0**, Q1–Q14 at the recommendation;
**S15-O4** ruled — the 17 `ell = 37` Loewy-4 lattice cells **assigned to WP-C19** (cluster);
**S15-O5** ruled — the October re-plan **waits for RB1–RB4**.

**Slot 16, the outcome (v1.21).** The slot ran on the owner's rulings of 2026-10-01 (O1–O8, `s16/owner_rulings_1001.md`), the waves of [S16] §3, at most
five agents, the three Fable windows F1 (L16-2's audit), F2 (WP-14) and F3 (L16-5) apart, plus a fourth Fable referee for the owner-requested [L37] report:

| Item | Outcome (v1.21) |
|---|---|
| Nebentypus, code (WP-10, WP-11) | **BUILT** after the Lean convention (L16-2, F1 audited) and the LMFDB predictions (WP-9 / 9b, audited 771 / 771): `Hecke/HeckeNebentypus`, `HeckeNebentypusValidation` (2434 checks): (NB1) 1668 cells, (NB2) bit for bit, (NB3) 79 cells (132 under `NB3_FULL`, 3808 checks, 947 s, 6.5 GB — **run at every close**, owner ruling), (NB5) **20 / 20 non-real cases read `[psi]`** (the χ / χ̄ dictionary observed as [GT] states it), (NB6) 377 / 377, three independent routes; **(NB4)'s sharp form at `n = 0` held 132 / 132** (`Sym^i` untwisted); `m = 2` and `H^1_m ≅ A_W²` on the non-ordinary dihedral blocks; `Λ_m ≇ T_m²` on the F1 hidden blocks for the full algebra. Sonnet audit ACCEPT WITH REPAIRS, repaired (`056b348`). **Deviations (carried):** the dense cap `D ≤ 4096` (no sparse route with a character), no `T_{p^ν}`, `ν ≥ 2`, no Galois-ring cohomology at `d ≥ 2`; no `FibreRepresentation` value (accepted) |
| General `N` (WP-13) | **BUILT** on [C] v1.16.0-pre.3 `sec:levelNdegsec` (WP-14 ACCEPT on (a), (c)): `κ_N` as code, `α_d` on the cokernel presentation, (LN7) / (LN8) gated, (LN9) reported, `U_p` at `d = p \| M`; composite `N` at `k > 2` to **`N = 30030`** (`D_N = 290 304`, 3.14 GB). Audit ACCEPT WITH REPAIRS, F1–F9 repaired by WP-17 (`06e40da`). **F-1 (carried):** the level-`N` table's int64 cocycles overflow at composite `N ≈ 5.5·10^4` (loud); **F-3:** the fitted sparse-fill law underestimates at composite `N`, `k > 2` by 1.5–6.8× (a [C] `rmk:levelNscale`(4) caveat, deferred) |
| Saturation defect (WP-5) | **BUILT** (owner-approved Tor package): `HeckeExt/HeckeSaturationDefect`, `HeckeSaturationDefectValidation` (299); hidden chains `I = m`, `T^sat/T = Z/ell` (3 / 3 + the default `(168, 13)`); the `ell = 37` Kummer blocks `I = 0` (saturated, 4 / 4); the ℓ = 7 demonstration (445 rows, 0 inconsistent); `rmk:sattor` proposed for [C] (deferred to slot 17, referee) |
| Census joins (WP-3) | **FIXED**: per-source-set `u_ell` in arm (T) and the lattice arm, the join by eigen-system (`HeckeExt/HeckeCensusJoin.h`), `JOIN_ONLY` pre-flight; the slot-15 `(654, 37)` 17 / 18 merge gone; audit repairs `447439b` (verified joins, loud record roots, arm (J)) |
| Census 3.1 (WP-4) | **PUBLISHED 2026-10-02 at the close by owner default** (part B, merge `edba09c`): arm (T) on 230 + 669 cells (`saturated` / `mult_one` on 2544 rows, add-only proof `violations=0 verdict=OK`), WP-5's three columns (O5) partial: `sat_cells_done=897 of 1459` (every cell `n ≤ 544` plus `(546, 59)`; `SAT_COLUMNS … saturated_inconsistent=0`; the rest `not_computed:no_log`); the cluster cells (RA / RS / LAT37) are census 3.2 |
| Console (WP-6) | **BUILT**: `hecke_ring_algebra`, script 029 (first freeze), `ConsoleErrorValidation` (HR) 562; audit ACCEPT (W6-1 … W6-4 LOW / INFO carried) |
| Contracts (WP-12, WP-14) | [C] v1.16.0-pre.1 → Fable referee ACCEPT WITH REPAIRS (0 B / 1 M / 8 m) → pre.3 → **v1.16.0 released**; [U] 0.2.0-pre.1 (part 2: CM components, CM ∩ GL(2), CM ∩ Eisenstein at tame `N ≥ 3`, (U8)–(U10); (U-1) folded in) → ACCEPT WITH REPAIRS (0 B / 1 M / 6 m) → pre.2 → **0.2.0 owner-signed**, **0.1.1 signed**; [E] 1.16.2, [EX] 1.2.2 (locators, WP-8) |
| [U] part 2 in code (WP-15, stretch) | **BUILT**: `HeckeExt/HeckeHidaCM`, `HeckeHidaCMValidation` (1376): (C0) 25 cells, (U9) 403 pairs no CM, (U8) 146 / 146, (U10) 10 / 10 with the excess pinned, the `h_K = 2` negative example (U-1). Sonnet audit (M1, M2, m1–m6) repaired (`3d2ce03`) |
| ℓ-local isotropy model (WP-16, stretch) | **BUILT at `ell = 3`** ([C] v1.16.0 `sec:isomodelell`): `Integral/Model/IsotropyModelEll`, `HeckeIsotropyModelEllValidation` (5655); (IL1)–(IL4) partial (see the carries); the averaging (C-1) is a no-op on `d`, load-bearing in `Ψ_ell` ((NC): 22 / 25) — [C]'s code map now names the comparison map's well-definedness check |
| Open citations (WP-8) | Washington 1st ed. p. 122 + Thm 7.10 (WP-6's citation re-pointed), Serre LNM 350 n° 1.3 Th. 1 p. 198, Haberland via Kiming–Verrill, `(107, 28)` projective image `S_4` **proved**, WWE locators for (LN5), (LN6) — applied at the releases. **Gross** (companion forms) not before ≈ 2026-10-07 |
| Lean lane (L16-0 … L16-6) | **all seven ran**; [LP] §4.1's exit criteria 1–7 met (CLAUDE.md "Lean lane"): toolchain v4.33.0 / mathlib `db584cd` (deviation from v4.33.1 recorded), one shared `lean-deps`; the census gate with seven negative controls; the convention layer incl. `conv:nebentypus` (F1 audit ACCEPT WITH REPAIRS, repaired); 13 literature structures (12 quoted); the `ρ_n` oracle and the `obl:tau` checker on real C++ output; G10 / G3 skeletons (32 `stated` rows); L16-5 Fable audit ACCEPT WITH REPAIRS (0 B / 2 M / 9 m), repaired (`9bbdbc3`). Census of record `decls=258 proved=194 proved_mod_lit=16 stated=32 lit_hyp=16 sorries=32 global_axioms=0 verdict=OK` |
| [L37] (owner request) | `docs/latex/l37_loewy4_example.tex` v0.1.0-pre.2 (not binding): the `ell = 37` Loewy-4 example on cohomology and forms, ordinarity (non-ordinary on every cell; ordinary would need `a ≡ 0, 31 (mod 36)`), saturation at all 24 cells, the dimension formula `m_1 + 3 m_2`, the end of the curvilinear window (`(1, 2, 2, 1)` at `k = 1412`, 1450: [E] `pr:kfonset` "from `k` on" fails on forms; `conj:window` for `1 ≤ a ≤ 30` proposed); Fable referee ACCEPT WITH REPAIRS (2 B / 8 M / 10 m), repaired at pre.2 |
| Cluster (WP-C19 / b / c) | the October kit (`docs/cluster/noctua2/october/`, `LAUNCH_2026-10-02.md`): RA1–RA2, PF37 → LAT37A/B (the 17 lattice cells with `U_37`, join by system, 17 `np_ext_a` records shipped), LX1, RS1–RS3 (November unless ≥ 2300 core-h remain), NP5RB / O1R at 24 h; the Opus audit's stop-ship C1 / C2 repaired (`c44f788`); `EXPECT_NAMES` 169 at the close. A local `lat37_656` wall measurement (`U_37` present) ran for C4. **Nothing returned inside the slot** (WP-C20 not run) |
| Stretch not run | WP-19a GPU G1, WP-19b the `p ≠ ell` digit split, WP-19c Proposition M's landing |

**[OD] S16 — the slot-16 decision register.** Owner rulings of **2026-10-01** (answers to [S16] §11, recorded in `s16/owner_rulings_1001.md`):

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S16-O1** | Ceiling as recommended: the core + WP-13 as upper core; WP-4 / WP-8 / WP-C20 conditional; stretch order L16-6, WP-16, WP-15, WP-19b, WP-19a, WP-19c | the core and WP-13 ran; WP-4, WP-8 ran; WP-C20 had no return; stretch L16-6, WP-16, WP-15 ran, WP-19b / a / c not |
| **S16-O2** | Release [C] v1.16.0 and [U] 0.2.0 at the close if WP-14 accepts; sign [U] 0.1.1 (approved now) | WP-14 ACCEPT WITH REPAIRS, 16 / 16 confirmed; **released** with [E] 1.16.2, [EX] 1.2.2 (`94f3eed`, `contract_release_report.md`) |
| **S16-O3** | A zero-golden-event slot; the add-only candidates batched into one slot-17 event | held: R0 = R1 = `b8a196d` (`golden_ledger.md`) |
| **S16-O4** | (E-3) yes; (E-2) yes as `\CONJ`; (U-1) deferred into WP-12's [U] draft for the referee | the [UE] proposal (U-1) refereed and landed in [U] 0.2.0 (re-tagged `\PROVED` for `θ^j`-images, referee item U-5; distinct from the referee's own U-1, the `h_K = 1` hypothesis of `prop:u-cmeis`(2)); **(E-2), (E-3) not yet applied to [E]** — they belong to [E]'s owner's next patch (carried) |
| **S16-O5** | WP-5's three census columns go into census 3.1 only if WP-5 merges before integration | WP-5 merged first; the columns are in 3.1, partial |
| **S16-O6** | ≤ 2 concurrent C++ builds; s14 scratch **not** pruned | held |
| **S16-O7** | Census 3.1 at `n > 500` locally overnight in checkpointed shards | done: 669 / 669 cells in 2 h 16 min (predicted 6–7 h) |
| **S16-O8** | October cluster: RA1–RA2 + the 17 `ell = 37` lattice cells first, then LX1; RS1–RS3 to November unless `sacct` shows ≥ 2300 core-h left after RA | the kit's order (WP-C19); submission is the owner's (rule 23) |
| **S16-N1** (lead note, owner-relayed) | LAT37 held until WP-3's fix and the C19b kit (`U_37` present, records shipped, RSS +3.7 GB / cell); then held again until the C19c repairs (PF37 wall, `--mem` to the 90 % budget, `EXPECT_NAMES` re-measured at the pushed commit) | both holds **lifted** (`70a0bbe`, `c44f788`); `EXPECT_NAMES` 169 at the close |
| **S16-N2** (owner, 2026-10-01) | `HECKE_NEBENTYPUS_NB3_FULL=1` (132 cells, 947 s, 6.5 GB) **at every slot close**, as a close-window step | `slot16_close_window.sh` step 6 (WP-18a); future close windows inherit it |
| **S16-N3** (owner, 2026-10-01) | A dedicated LaTeX report on the `ell = 37` Loewy-4 example (cohomology vs forms, ordinarity, Eisenstein vs cuspidal, θ / Kummer, the Galois-cohomological reading), Opus author, Fable referee | [L37] v0.1.0-pre.2 (`5de5852`, `f381637`, `7d6f480`) |
| **S16-N4** (owner, 2026-10-01) | Census 3.1 is **published at the close by default** (refresh from the sat shards first; WP-5's columns partial, unfinished cells `not_computed`); only a contrary owner word stops it | part B (runbook) |
| **S16-N5** (owner, ≈ 21:00) | Close schedule: prepare the close documents now; after the local LAT37 run (≈ 02:00) let each sat shard finish its current cell, then stop the shards; refresh + publish 3.1; then W1 alone on the quiet box; then NB3_FULL, `CheckThread` + cross-config on the new names; push | WP-18a (this version) + part B |
| **S16-N6** (lead) | WP-17's queue: the WP-13 audit F1–F9, the WP-16 audit, WP-8's locator edits, and the proposals of WP-5 (`rmk:sattor`) and WP-11 ([C] / [EX] / [U]) for the release owners; [C]'s code-map sentence on (IL1) names `Ψ_ell`'s well-definedness check | code repairs `06e40da`, `406bea6`; the locators and the (IL1) sentence at the releases; **the proposals deferred** (new mathematics, need a referee) |

Slot 17's packages and waves: `docs/implementation/slot17/00-slot17-plan.md` v1.x.

**Slot 17, re-cut from the slot-16 outcome** (supersedes the slot-17+ rows above where they differ; the owner sets the ceiling):

| Item | Content | Gate | AU (order of magnitude) |
|---|---|---|---|
| **The golden event** | one owner-gated add-only event (O3): level-`N` points (now with `α_d` / `κ_N`), certified `LOEWY_RING` lines, nebentypus points; an `expect` set first, single-parent commit, Fable audit, `golden_landing_check.sh` | the owner's yes | 0.5 |
| **Deferred contract items** (`contract_release_report.md` §4) | [C] `rmk:sattor` (WP-5, PROVED in the note); WP-11's [C] `rmk:nebcheckable` (NB4) proposals (the `n = 0` sharp form as DATA with its orientation, the `n > 0` reading with the `H^0` correction, a `\PROVED` candidate by the JH sequence), [EX]'s WP-C16 subsection (SPEC → DATA, the F1 sentence), [U]'s F1 sentence beside `prop:u-loewy`; [L37]'s window bound for [E] `pr:kfonset`; WP-13 F-3's composite-`N` / `k > 2` caveat to `rmk:levelNscale`(4); [E]'s (E-2) (`\CONJ` F1 Frobenius-layer Prediction) and (E-3) (the I-8 tag note) per S16-O4; [U]'s two remaining Washington `\VERIFYloc` sites (old l. 550, 698); [EX]'s `\PROVED{}` tag on the `(107, 28)` sentence (observation); the `slot15/WP-6_report.md` citations row | a Fable referee (one window) | 1.0 |
| **Level `N` beyond `5.5·10^4`** | WP-13 F-1: `__int128` or residue-only cocycles in `Gamma0LevelN::cocycle` / `MonomialOf` (as done for `H` and `D`) | — | 0.5 |
| **Nebentypus at scale** | WP-10's carries: the sparse cokernel with a character (lift the `D ≤ 4096` dense cap; WP-13's `N` ladder), `T_{p^ν}` for `ν ≥ 2` (`thm:nebrelations`(2)), Galois-ring cohomology at `d ≥ 2` (`rmk:nebcost`(4)) | — | 1.0 |
| **The isotropy model's open halves** | WP-16: (IL3)'s level-`N` clause (`M = Ind_{Γ_0(N)}^Γ V_R` on the model), (IL4) over `Z/3^e`, the pair / cone half of `prop:isomodelell`(5), the refinement half of `rmk:isomodellmp` (a synthetic refined descriptor); [C] marks IL3 / IL4 `\COMP^a` partial | — | 0.8 |
| **Census 3.1 remainder → 3.2** | the WP-5 sat-defect cells left `not_computed:no_log` at the close (cost grows steeply beyond `n ≈ 400`; per-cell serial module runs); RA1–RA2 / RS1–RS3 / the 17 LAT37 cells / LX1 on return (WP-C20); the WP-5 hidden-chain cells and the ℓ = 37 Kummer cells stay **hook-only** expectations (not in the default suite) | the cluster returns | 0.5 per return |
| **The ℓ = 37 programme ([L37] §8)** | `(1410, 37)` the second window on cohomology (census algebra and saturation, predicted ≤ 30 GB — a cluster item, predict RSS first); the reducibility congruence module `e`; the θ-image at `(258, 37)`; the 17 C-F9 cells (predicted `failed`); the onset law for all `n`; other Kummer classes; the local Massey computation; the slope law; `pr:kfonset`'s window | owner; cluster for `(1410, 37)` | 1.0 |
| **LAT37 risk** | the LAT37 wall is extrapolated from one cell without `U_37` (C19 audit C4); **measured (WP-18 part B):** the local `lat37_656` run (with `U_37`, `ENGINE_THREADS=1`, on a loaded box, 2026-10-01 18:00 → 2026-10-02 03:18) took **9:18:02 wall, peak RSS 8 945 588 kB (8.5 GiB)**, exit 0, `[PASS]`, `LATTICE_RC=0`; `EFFECTIVE … operators=with_U_ell:1,without_U_ell:0 u_ell=source_set{budget_mb=16384:1} join=system:8,witness:1,refused:0,fallback:0`; `CENSUS_LATTICE_SUMMARY rows=9 held=7 failed=1 not_evaluated=1`, the C-F9 finding at ideal 15 (dim 8, Loewy 4, layers 4:2:2:1; `cell_s` 33 422 s); 9.3 h > 8.5 h, so LAT37B's 24 h wall does **not** hold for `n ≥ ≈ 696` — **the six `n ≥ 690` cells run locally in slot 17; LAT37B is not submitted as is**; at a memory weight ≠ 0.255 recompute billed-h (C5) | the local measurement; the owner's `sacct` | — |
| **Literature** | Gross (companion forms, from ≈ 2026-10-07) for F1's post-drop reading; Jochnowitz TAMS 270 (1982), both papers; Medvedovsky's thesis; a query to Deo / Medvedovsky ([L37] `pb:jochnowitz`) | the sources | 0.3 |
| **Lean, milestone M1** ([LP] §4.2) | G1 complete; the compiled checker on the full golden τ grids; G10 saturation **proved** from L16-6's skeleton (its `stated` rows among the 32) + the stable-certificate checker on WP-5's certificates; the L1 register to ≈ 25 (`SturmLevelOne` and L16-6's two structures still unquoted); [C] gains `\LEAN` tags; **the velocity re-estimate** ([LP] §4.3) from slot 16's measured figures (194 proved + 16 `proved_mod_lit` over seven packages, two seats) | the owner (ceiling) | 2.5 |
| **Small carries** | WP-2 audit W2-1 (an entrywise `P`-conjugation check in (R3m)), W2-2 (wording); WP-6 audit W6-1 (`K_cls` vs `kmax` guard), W6-2 (exact `PowFit` boundary), W6-3 (029's comment at the next owner-gated re-freeze), W6-4 (help string: `kmax` default 3); WP-13 audit nits beyond F9 (none open) | — | 0.3 |
| **Stretch (re-carried)** | WP-19a GPU G1 (session-scoped residency, never default), WP-19b the `p ≠ ell` digit split, WP-19c Proposition M's landing (only with a non-final `mixed` row); line 2 (OD-3); the review leftovers re-carried by slot-14 WP-12 | — | — |

**Slot 17, the outcome (v1.22).** The slot ran on the owner's rulings of 2026-10-01 (O1–O10, `s17/owner_rulings_1001.md`) and of 2026-10-02, the waves
of [S17] §3, at most five agents, the Fable windows F1 (WP-3), F2 (WP-4), F3 (L17-6) and the optional F4 ([L37]) apart:

| Item | Outcome (v1.22) |
|---|---|
| Golden event R1 (WP-4) | **LANDED**: expect set `e2c075b`, emission `1d0be42`, +168 entries (LEVELN 68 A + 34 B, LOEWY_RING 25 A, NEB 41 A), predicted = observed; F2 ACCEPT WITH REPAIRS (7 minors, documentation); digests unchanged; W1 confirms 11 821 / 0, 5935 / 0 |
| Level `N` at scale (WP-5) | **BUILT**: `__int128` attempt-then-escalate cocycles (`cocycle_wide`): `N = 90 090` at `k = 2`, `60 060` at `k = 4` (`D = 580 608`), prime `100 003`; audit ACCEPT WITH REPAIRS (text). **W5-F1**: `99330` blew past the 8 GB watchdog (fill law off by > 5×) → slot 18 |
| Nebentypus at scale (WP-6) | **BUILT** (a) the sparse cokernel with a character (to `D = 290 304`), (b) `T_{p^ν}`, `ν ≥ 2` against Merel's `Mer_{p^ν}`, NB3_FULL on the sparse route; audit ACCEPT. **Not run:** (c) = WP-6c (Galois ring `d ≥ 2`) |
| Isotropy model (WP-7) | **BUILT**: (IL3N) at level `N` over `F_3`, (IL4e) over `Z/3^e`, the pair / cone half, a synthetic refined descriptor (REF, a descriptor round trip); audit ACCEPT; [C] IL3 / IL4 stay `\COMP^a` partial for the next referee |
| Small carries (WP-8) + repairs (WP-17) | strict hook grammars and the rule-19 pre-run refusal; WP-17's calibrated `hook_rss/v1` and `HECKE_LEVEL_N_HOOK_RSS_CAP_GIB`; `HeckeSmallCarriesValidation` (53); console `hecke_ring_algebra` `u_ell` gate (R17-2's 45.8 GB model); F1 m-C2 gated |
| Census (WP-9) | **3.2 STAGED, not published** (owner-gated): +176 sat-defect cells (all `546 ≤ n ≤ 608`), `sat_cells_done=1073 of 1459`, add-only vs 3.1 `violations=0`; one non-trivial defect at `(602, 43)`; the 386 cells `610 ≤ n ≤ 700` → November kit SD1 / SD2 |
| Contracts (WP-2, WP-3) | F1: [C] ACCEPT WITH REPAIRS (0 B / 1 M / 5 m), [E] ACCEPT WITH REPAIRS — not releasable as written (B-1, B-2), [U] / [EX] ACCEPT WITH REPAIRS; repairs at pre.3; owner 2026-10-02: (R) on congruence-free classes (B-1), (NB4)(c) `\PROVED` (M-1); R17-4's locators at pre.5; **released at the close**: [C] v1.17.0 (+ `\LEAN`), [E] 1.17.0, [U] 0.2.1, [EX] 1.3.0 |
| Lean (L17-0 … L17-6) | **M1 met**: G10 saturation proved (L17-1), the sat-cert checker on 19 dumped certificates (L17-2), G1 complete (L17-3), the τ / ρ checkers on the golden grid kernel-only, `native_decide` removed (L17-4), the literature register (L17-5); F3 ACCEPT WITH REPAIRS (two false-as-written statements repaired); census `decls=440 … hyp_bad=0 verdict=OK` |
| Research (R17-1 … R17-4) | the Bernoulli / onset scan and Theorem 4.1 (the dimension formula at every ℓ); (R) **refuted on cohomology** at `(608, 547)`; the swapped meeting; B-1 at `ℓ = 67, 131, 139` (forms side); 691 "is 37 again" (forms side); [L37] v0.2.0-pre.2 (`conj:law`, the field-extension reading; F4 ACCEPT WITH REPAIRS); the literature locators |
| LAT37 (local) | `(700, 37)` PASS 10:35:52 / 9.68 GiB, `(698, 37)` PASS 11:42:38 / 9.63 GiB, `(696, 37)` 10:52:12 / 9.57 GiB with 5 environmental (J1) / (J2) failures (a source path baked into a binary whose worktree was removed); C-F9 **failed** at one ideal in each cell (Loewy 4), as [L37] predicts; **694 / 692 / 690 carried to slot 18** (owner) |
| Cluster | nothing returned; the November kit (WP-C21, audit ACCEPT WITH REPAIRS): SW1 `(1410, 37)` pilot, SD1 / SD2, LAT37F, C2210 / C2574 gated on SW1, RS, NP5RB / O1R; `EXPECT_NAMES` = 171 |
| Not run | WP-6c, L17-7, WP-19a / b / c, WP-C20 |

**[OD] S17 — the slot-17 decision register.** Owner rulings of **2026-10-01** (answers to [S17] §11, `s17/owner_rulings_1001.md`) and of 2026-10-02:

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S17-O1** | Ceiling: the core, WP-7 upper core; WP-9, WP-C20, WP-C21, R17-3 conditional; stretch WP-6c → L17-7 → WP-19b / a / c | core + WP-7 ran; WP-9, WP-C21, R17-3 ran; WP-C20 had no return; no stretch ran |
| **S17-O2** | One add-only golden event, all three families, ≤ 6 cells each | R1 `1d0be42` (`golden_ledger.md`) |
| **S17-O3** | Releases on F1's accept: [C] v1.17.0 (with the `\LEAN` tags), [E] 1.17.0, [U] 0.2.1, [EX] 1.3.0; `pr:kfonset`'s window as a `\CONJ` restatement | released at the close (`410d4e4`) |
| **S17-O4** | [L37] v0.2: a Sonnet audit only, Fable only if a statement goes into [E] | the owner requested F4 for R17-3's widened v0.2.0-pre.1 (ACCEPT WITH REPAIRS, repaired at pre.2) |
| **S17-O5** | No cluster FLT build; local closure build as stretch | not run |
| **S17-O6** | LAT37 per [S17] §5.1 | local wall 9:18 h > 8.5 h → the six `n ≥ 690` cells locally; 700, 698, 696 done; 694 stopped, 692 / 690 not started → slot 18 |
| **S17-O7** | The 691 test forms-side only, after the 37 mirrored-configuration test | R17-2 (forms side: curvilinear `F_691[x]/x^4` at `(8982, 691)`) |
| **S17-O8** | The Deo / Medvedovsky query drafted for the owner; no agent contacts anyone | drafted (R17-4); sending is the owner's |
| **S17-O9** | November cluster: RS1–RS3 first, then `(1410, 37)` with RSS predicted first | the November kit's order (WP-C21) |
| **S17-O10** | Pre-start packages during slot 16's close | ran (WP-2, R17-1, L17-0, L17-5) |
| **S17-N1** (owner, 2026-10-02) | Insert ℓ = 547 (`k = 610, 486, 1158`) into R17-2's forms-side order | done |
| **S17-N2** (owner, 2026-10-02) | (R) restated on **congruence-free** classes (F1 B-1); (NB4)(c) **`\PROVED`** given one `\STD` input (F1 M-1) | [E] 1.17.0-pre.4, [C] 1.17.0-pre.4 → released |
| **S17-N3** (owner, 2026-10-02) | LAT37 694 / 692 / 690 carried to slot 18 (run locally 2–3 at a time); census 3.2 staged, not published (completed after the cluster returns) | [S18] §0.2 |
| **S17-N4** (lead) | Shared research binaries are built from a persistent detached checkout under `$DATA_ROOT` (never a `.claude` worktree), since the source path is baked into the binary; never remove a worktree whose binary still runs | `lead_carry.md`; slot-18 WP-1; the WP-18 close build followed it |
| **S17-N5** (owner, 2026-10-02, at the close) | W1's timings are not critical this slot: measured under foreign load (`OVERLAP … foreign_heavy_rows=1309` of 1924), hecke 256 abs-gate MISS with the paired ratio 0.997 MET **accepted as environmental**; no quiet re-run in slot 17 | a quiet re-measure in slot 18's W1 (`slot17/WP-18_close_report.md` §1.3) |

Slot 18's packages and waves: `docs/implementation/slot18/00-slot18-plan.md` (**v1.0**, 2026-10-03; owner questions O1–O11 **all answered, as recommended**).

**Owner rulings of 2026-10-03 on [S18]** (register entries S18-O1 … S18-O11, S18-M):

| ID | Ruling |
|---|---|
| S18-O1 | the core of [S18] §1.1, WP-7 upper core in, conditional / stretch orders as recommended |
| S18-O2 | a second add-only golden event: `p ≠ 2` τ / `τ_∂` tables + one `d = 2` NEB cell only (F2) |
| S18-O3 | releases at the close: [C] v1.18.0 (F3's `\LEAN` tags), [E] 1.18.0, [EX] 1.4.0 on F1 ACCEPT |
| S18-O4 | [LP] v1.1 as a forecast; M2 + G3's 10 rows planned (G4 stretch); stay on mathlib `db584cd` |
| S18-O5 | F4 only on a new statement or a contradicted prediction |
| S18-O6 | LAT37A locally in slot 19; slot 18 finishes 690 / 692 / 694 |
| S18-O7 | census 3.2 held, staged at the close, published on completion (add-only) |
| S18-O8 | Deo / Medvedovsky query sent; scans provided; Glover first |
| S18-O9 | PARI/GP in `$HACS_DATA/tools/`, research scripts only |
| S18-O10 | WP-19d notebook design note (no code) |
| S18-O11 | moot (slot 17 closed; everything opens with wave A) |
| **S18-M** | **new core package WP-M**: `docs/latex/cli_manual.tex` → PDF covering every CLI flag, the OC language, all verbs / types / settings, exit codes, env hooks, worked examples tested against the frozen transcripts; a generator (`docs/console/gen_cli_manual.sh`) keeping the reference tables in sync with the binary; a coverage validation (`CliManualCoverageValidation`, fast, `Registry/Slot18/WPM.cpp`); Opus writes, **Fable referees (F-M, not overlapping F1 / F2 / F3)**; wave A; closed by WP-18 (PDF built at the close) |

Wave and budget deltas of v1.0 over v0.1: four Fable windows in the order F1, F2, F-M, F3 (F4 optional); WP-M takes the seat WP-1 frees in wave A and continues to F-M; `--all` forecast 156 and `--all-full` 172 at the
close if nothing else registers (`EXPECT_NAMES` 172 with WP-M's commit); wave H carries F-M's repairs and the PDF.

Lean amendments (L18-0 §6, folded in by the lead 2026-10-03): L18-1 central 120 min (M2-a … M2-d, 150-min fallback), L18-2 central 150 min (M2-e first), L18-3 75 + 90 min (+ 60 repair per half), L18-4 `stated` ≤ 1 with G3 first, the Lean chain ≈ 6.75 h central, M2's exit = M2-a … M2-h of `slot18/L18-0_velocity.md` §3, Q12 = stay on `db584cd`; **[LP] v1.1** (forecast). Disk figure corrected: C: ≈ 74 GB free.

**Slot 18, re-cut from the slot-17 outcome** (supersedes the slot-18+ rows above where they differ; [S18] is the authority for packages and waves; the owner sets
the ceiling):

| Item | Content | Gate |
|---|---|---|
| **[LP] M2** | the `K^u` key model tied to `TauCheck.TauData` and the orientation; the `τ_∂` / η checkers (L17-4 §6); F3 MINOR-11 (`lem:freepart`(2)) and the lean4checker kernel replay; L17-0's v1.1 re-estimate (M2 + M3 in slot 18) | owner O4 of [S18] |
| **`(1410, 37)` and the 691 cohomology question** | the November kit's SW1 pilot (`(1410, 37)`, RSS predicted first), then C2210 / C2574 gated on SW1's wall; `(8982, 691)` on cohomology not before the cost is known | cluster (rule 23) |
| **LAT37 694 / 692 / 690** | locally, 2–3 at a time (≈ 10.5 h, ≈ 10 GB each), from a binary built on a persistent detached checkout; the LAT37 report finished in slot 18; (696)'s (J1) / (J2) re-checked by a `JOIN_ONLY` run only if needed | the owner's ruling of 2026-10-02 |
| **WP-6c** | Galois-ring nebentypus at `d ≥ 2` (`W_K(F_q)`), a model-route `T_{p^2}` | — |
| **Census 3.2** | completed after SD1 / SD2 return; the census-3.2 pointer for [E] at its publication | owner O7 of [S18] |
| **[L37] → [E]** | v0.2's statements proposed for [E] (`pr:kfonset`'s generalisation to the swapped family and `g ≥ 2`, the window, `conj:law` as `\CONJ` only if R18-1 holds), R17-1's Theorem 4.1 as a statement (F1 m-E5) | the next referee window |
| **Next referee window** | WP-2 → F1 → repairs for [C] v1.18.0 / [E] 1.18.0 / [EX] 1.4.0 (with the M2 `\LEAN` tags) | owner O3 of [S18] |
| **Level `N` at scale II** | W5-F1's structure-aware fill model, the `CokernelCostModel` re-fit, `99330` and `90090:2` in an exclusive window (`HECKE_LEVEL_N_HOOK_RSS_CAP_GIB=12`), `contains_wide` / `HeilbronnChi` on `cocycle_wide` | exclusive window |
| **Golden O2 of [S18]** | the `p ≠ 2` τ / `τ_∂` tables, a `d ≥ 2` NEB cell, WP-4's alternatives | the owner's yes |
| **Timing** | W1 on a loaded box: hecke 256 abs gate MISS (paired ratio MET), ConsoleDet 44.0 s (threshold 45 s), the re-time of `HeckeRingLoewyValidation` (target 64 s) — owner-accepted as environmental (2026-10-02); the quiet re-measure is part of slot 18's W1 | — |


**Slot 18, the outcome (v1.23).** The slot ran on the owner's rulings of 2026-10-03 (O1–O11 as recommended, the new core package WP-M) and the
close ruling of the same evening (close now with the runs in flight carried; W1 under the declared load of our own three LAT37 cells, correctness is
the verdict), the waves of [S18] §3, at most five agents, the Fable windows F1 (WP-3), F2 (WP-4), F-M (WP-M), F3 (L18-6) and F4 ([L37], O5) apart:

| Item | Outcome (v1.23) |
|---|---|
| Golden event R1 (WP-4) | **LANDED**: predicate `d641512`, emission `4ee627c` (single parent), +302 entries (EXT_TAU 296 B: `tau` / `tau_bd` table hashes at `(p, ν) ∈ {(3,1),(5,1),(7,1),(2,2),(3,2)}`; NEB_d2 6 A at `N = 7`, `χ = 7.2`, `k = 4`, `ℓ = 5`, `F_25`), 0 changed, 0 removed; **18 058** entries, A **11 827** / 0, B **6231** / 0; digests unchanged; F2 ACCEPT WITH REPAIRS (0 B / 0 M / 5 m, documents; the six tier-A values re-derived from LMFDB data over `F_25`) |
| Contracts (WP-2, WP-3) | F1: ACCEPT WITH REPAIRS (0 B / 2 M / 10 m), 9 / 9 referee forms-side cells held incl. the `g = 2` meeting `(34460, 547)` = `F_547[x]/x^6`; repairs at pre.2; **released at the close**: [C] v1.18.0 (M2 `\LEAN` markers, 81 on 42 labels; the `thm:welldef`(c) erratum, confirmed by F3 and by the owner), [E] 1.18.0 (`sec:dimblock`, `pr:kfonset` (A)–(C), `pr:depth`; WP-19b / WP-19c texts), [EX] 1.4.0; [U] stays 0.2.1 |
| Level `N` at scale II (WP-5) | **BUILT**: the value-free generator order of the sparse elimination (W5-F1's root cause: the fill at `99330`, `k = 2`, is 54.45 M, an order effect), `Gamma1LevelN::contains_wide`, `HeilbronnChi` on `cocycle_wide`; the structure-aware fill model **failed** its ×1.5 rule (a finding; `hook_rss/v1` stays); **window E2 (`99330:0:13`, `90090:2:17`) not run** (LAT37 + the disk emergency) → slot 19 WP-RC |
| Nebentypus (WP-6) | **BUILT**: `Hecke/HeckeNebentypusGalois` (`W_K(F_q)`, `K ≤ 3`, `d ≤ 4`, dense + sparse Howell routes), the model-route `T_{p^2}` (= the recursion entrywise), the `D = 193 536` ladder cell on a second route; WP-6c of slot 17 thereby done |
| Isotropy model (WP-7) | **BUILT**: the strict lift on a synthetic refined descriptor (`Integral/Model/RefinedStrictLift`), IL5 run (`\COMP^a`), IL3 over `F_9` / `Z/9`; [C] IL3 / IL4 moved to `\COMP^a` (F1 C-4) |
| CLI / console manual (WP-M) | **RELEASED** [CLI] **1.0.0** (59 pp., committed PDF): generator `gen_cli_manual_tables.sh`, `CliManualCoverageValidation` (fast); F-M ACCEPT WITH REPAIRS (11), R1–R9, R11 repaired, R10 carried (C7); three exit-code statements verified on the close binary |
| Lean (L18-0 … L18-7, WP-17) | **M2 met**: G2 (the `X_bulk` descriptor, `model7`, H4 over the model, Ψ, `thm:welldef` first bullet / (a) / (c) transported), G3's 10 cone rows, the τ_∂ / η checkers, `heckerankone` `proved_mod_lit` over `EichlerShimuraLevelOne`, the census sources hash and the kernel replay (`LEAN_REPLAY modules=103 ok=103 … verdict=OK`, peak 13.81 GiB); F3 ACCEPT WITH REPAIRS (0 B / 2 M / 9 m; MAJOR 2 → slot 19 C1); L18-7 G4's abstract projective reduction (6 rows). Census `decls=823 proved=764 proved_mod_lit=34 stated=1 sorries=1 … hyp_bad=0 verdict=OK` |
| Research (R18-1 … R18-5) | `conj:law` (C-1) **refuted as stated** (50 second-window cells at 37), (C-1') held 548 / 548 at 7 primes and ℓ-adically; `e = 2 + v(K − e_i)` at the last cells; Jochnowitz 601 / 601; explicit Kummer generators `X^37 − η_32`, `X^37 − η_6`, `X^1369 − η_284` (R18-2, in-house); the literature report and the Deo / Medvedovsky draft (R18-4); [L37] **0.3.0** (F4 ACCEPT WITH REPAIRS, 0 B / 2 M / 13 m, repaired); R18-3: `pb:thetaimage` answered (8 cells, all predictions held), E1 `(1220, 37)` and the sat cells `(944, 59)`, `(1184, 37)` **not run** → slot 19 WP-RC |
| Stretch (WP-19a … d) | WP-19a GPU G1 session residency (`EngineElimSessionValidation`, never default); WP-19b the `p ≠ ℓ` digit split (`HeckeLadicSplitValidation`); WP-19c Proposition M **not landed** (64-cell probe, no `K ≠ 0 ≠ S_V` block); WP-19d the notebook design note (owner decisions 2026-10-03) |
| LAT37 (local, WP-L37) | `(690, 37)`, `(692, 37)`, `(694, 37)` **running at the close** (started 2026-10-03 10:16 CEST on the slot-18 shared binary, `ENGINE_THREADS=1`, peak HWM ≈ 9.4 GiB each) → slot 19 WP-RC with the LAT37 report |
| Census | 3.2 **staged, held** (O7: published on the return that completes it); no cluster return in the slot |
| Not run | WP-8 (its timing part is the close's W1, loaded, and slot 19's Q; its `census.tsv` reader item was done by L18-5), WP-9 (no return), WP-C22 (no return), WP-C23 |

**[OD] S18 — the slot-18 decision register.** The owner rulings of 2026-10-03 are entries S18-O1 … S18-O11 and S18-M above (as recommended); added at
the close:

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S18-N1** (owner, 2026-10-03) | No external CAS (PARI / Sage / Magma); in-house number-field code, HPC-capable; supersedes O9 | R18-2 in-house; slot-19 number-field core |
| **S18-N2** (owner, 2026-10-03) | WP-19d notebook decisions: LAN-reachable with a private-source filter and a session token, a portable stdlib gateway, LaTeX only in the notebook, a `read_only` verb tag, opt-out CMake switches, an aarch64 build item | `WP-19d_notebook_design_note.md` §0; `lead_carry.md` C8 |
| **S18-N3** (owner, 2026-10-03) | `hrank` from `heckerankone` (F3 MAJOR 2) goes to slot 19 (M3's first item) | `lead_carry.md` C1; [LP] v1.1 |
| **S18-N4** (owner, 2026-10-03, evening) | **Close slot 18 now**; the runs in flight (LAT37 690 / 692 / 694, R18-3's E1, WP-5's E2) become a slot-19 package; W1 under the declared load of our own three LAT37 cells — correctness is the verdict, every timing labelled "loaded box (3 LAT37 cells)", the quiet re-measure carried again | the slot-18 close report; slot 19 WP-RC |
| **S18-N5** (owner, 2026-10-03) | Releases at the close: [C] 1.18.0 with F3's tags and the `thm:welldef`(c) erratum recorded in the changelog — **the erratum confirmed by the owner** (2026-10-03, with the slot-19 rulings) —, [E] 1.18.0, [EX] 1.4.0, [L37] 0.3.0, [CLI] 1.0.0; [U] 0.2.1 unless something requires a bump | commit `c044f64` |
| **S18-N6** (owner, 2026-10-03) | L-value triangle with an abstract interface for Birch modular symbols and Hida's GL2×GL2 pairing (C9); slot-19 proposals C3–C6 | `lead_carry.md` C3–C6, C9 |

Slot 19's packages and waves: `docs/implementation/slot19/00-slot19-plan.md` (**v1.0** since slot-19 WP-1, see v1.23.1; was v0.1, `e1eeab7`; **the owner accepted its recommendations O1–O15 on
2026-10-03**; the lead promotes it to v1.0 after this close lands). The rulings, as mirrored here: (O1) the ceiling as drafted (≈ 64 h); (O2) python-flint
in research scripts only, with an in-house cross-check; (O3) an own BigInt, no GMP; (O4) zero golden movement; (O5) the [U] Λ-adic statement now, its code
upper core; (O6) [E] `sec:lvalue` for the L-value interface (C9); (O7) run order LAT37 → E1 → `(1184, 37)` → E2 → the owner's `wsl --shutdown` → the quiet
re-measure Q; (O8) LAT37A locally, two at a time; (O9) `model7_acyclic` by an explicit contracting homotopy; (O10) M3 in slot 19, M4 in slot 20; (O11)
notebook NB-0 … NB-2 core, NB-3 upper core, NB-4 stretch, no TLS, the Jetson kit owner-run; (O12) Fable windows F1 → F4 → F3; (O13) swap = 8 GB in
`.wslconfig` at the shutdown; (O14) `(258, 37)` q-expansions exact to the Sturm bound and mod `37^4` to `q^1000`; (O15) census 3.2 held, Proposition M
closed as SPEC, Glover first. Also confirmed with them: the [C] `thm:welldef`(c) erratum.

**Slot 19, re-cut from the slot-18 outcome** (from `docs/implementation/slot18/lead_carry.md` C1–C9 and the close carries; [S19] is the authority for packages
and waves; the owner sets the ceiling):

| Item | Content | Gate |
|---|---|---|
| **Run completion (WP-RC)** | LAT37 690 / 692 / 694 to their end and the LAT37 report (all seven local cells against `pb:lattice`); R18-3's E1 `(1220, 37)` + side chain, `(1184, 37)`, `(944, 59)` sat ([R183] §2 recipe); WP-5's E2 `99330:0:13`, `90090:2:17` (`HECKE_LEVEL_N_HOOK_RSS_CAP_GIB=12`); then the owner's `wsl --shutdown`; **Q**, the quiet re-measure (hecke 256 vs 0.470 s, decomp 128, ConsoleDet vs 45 s, RingLoewy vs 64 s, Nebentypus vs 60 s) with the slot-18 close binary and REF `dcd0c30` | the runs end; a quiet box |
| **C1** `stablecert_ES` | `hrank` discharged from `heckerankone`; `cor:stablecert` `proved_mod_lit` over `hES` only | M3's first item (S18-N3) |
| **C2** | `EtaSpec → Cone.IsPairHomotopy` over `model7` (needs `X_∂`) | M3 |
| **C3** | the Λ-adic Hida algebra | owner proposal |
| **C4** | `(258, 37)`: the exact Hecke-module structure and the q-expansions | owner proposal |
| **C5** | Ribet 691 via the `Z/691²`-equivariant route | owner proposal |
| **C6** | Heisenberg / adjoint-Selmer fields as SPEC (continuing R18-2) | spec only |
| **C7** | WP-M's R10 token-table nits (`level_a` `off`; `--atlas` range; `-` with `--console`) | code + regenerate the manual |
| **C8** | the notebook R-U1a, NB-0 … NB-5 (NB-0, the build switches and aarch64, first) | owner decisions S18-N2 |
| **C9** | the L-value triangle behind an abstract interface (Eisenstein / Bernoulli instance first) | owner S18-N6 |
| **Lean G4 remainder** | the bridge `C_q(X_bulk) ⊗ R` as a `ChainComplex (Rep R SL(2,ℤ))`, then `rmk:orbifold` / `lem:tauexists`(2) / `thm:welldef`(b) on the model (needs `model7_acyclic`) | M3 |
| **Census 3.2** | held (O7) until SD1 / SD2 return (`sat_cells_done=1459`) | the November kit's returns |
| **LAT37A** | `n = 658 … 676` locally after Q | S18-O6 |
| **Close-window debts** | TSan coverage of `EngineElimSessionValidation` (device-only; SKIPs under `ENGINE_CUDA_DISABLE=1`): a `libcuda` suppression file (`lead_carry.md` C12); cross_config PASS and the other slot-18 names TSan-clean at the close | — |

**Slot 19, the outcome (v1.24).** The slot ran on the owner's rulings of 2026-10-03 (O1–O15 as recommended; the `thm:welldef`(c) erratum confirmed),
grew by a third mid-way (WP-NF2, WP-LV2, WP-LIN, WP-BIL, R19-7 … R19-9, sat1220, isign, F1-delta, all added after v1.0, each with its predictions committed
first), and closed on the owner's instruction of 2026-10-04 (relayed by the lead: proceed autonomously; close as slot 18 closed — W1 now, the runs in flight
carried into slot 20). Fable windows: F1 (WP-3), F4 (R19-6), F3 (L19-6), F1-delta (the close delta of the contracts).

| Item | Outcome (v1.24) |
|---|---|
| Golden | **no event** (O4); reference byte-identical to R0 `deab1af` (18 058 = 11 827 / 6231); `golden_landing_check.sh deab1af` OK |
| Contracts (WP-2, WP-3, F1, F1-delta) | F1: [U] 0.3.0-pre.1 part 3 and [E] 1.19.0-pre.1 ACCEPT WITH REPAIRS (M-1 `cl:lveis`(3) stable ≠ saturated, M-2 `def:lvroute`'s kind set `{linear, bilinear, congruence}`), [C] ACCEPT; the fold-ins pre.3 … pre.6; **F1-delta** (pre.3 → pre.6): [E] / [C] / [L37] ACCEPT WITH REPAIRS, [U] ACCEPT, 0 B / 1 M (the (H) constant's PROVED rests on Haberland, RECALLED → STD + CMPD) / 7 m, repaired at `166ae476` (m-U1 optional, not applied). **Released at the close**: [C] v1.19.0, [E] 1.19.0, [U] 0.3.0, [L37] 0.4.0, [CLI] 1.1.0 |
| Number fields (WP-NF, WP-NF2) | **BUILT**: the seventh target `NumberField` (STL only: `BigInt`, Bernoulli numbers, `Z[ζ_{ℓ^k}]` exactly and mod `ℓ^M`, cyclotomic units, the Kummer tests incl. the equivariant `Z/ℓ²` layer, `Q(α)`, Newton polygons, Hensel), `NumberFieldValidation` (fast); WP-NF2 the Coates–Wiles layer route `CwLayer` (62-bit NTT) and the fitted cost model `nf::cw_predict`: 691 at `m = 3` is local (31.9 GB, ≈ 1.1–1.6 h at 8 threads), `m ≥ 4` out of reach |
| L-value line (WP-LV, WP-LV2, WP-LIN, WP-BIL) | **All three kinds of [E] `def:lvroute` built**: congruence (WP-LV: Eisenstein / Bernoulli, leg (c); WP-LV2: twisted `B_{k,ω^j}` on the character model over `Z/ℓ^K`, free part at finite precision, deep rungs `(282, 37)`, `(226, 103)`: `#Q_m = ℓ^{min(m,2)}`; its torsion and RSS predictions refuted and reported), linear (WP-LIN: `BirchModularSymbolRoute` on `H^1_c` of the C++ cone, (L1) at depth 1, (L2), the `(258, 37)` isign facts), bilinear (WP-BIL: `HidaPairingRoute`, (H1), (H2) at depth 1, (H3) at `(258, 37)`); all in `HeckeLValueValidation` |
| `(258, 37)` and lattices (R19-1, WP-LC, isign) | R19-1: `T_m = Z_37[t]`, `T̃/T_m = F_37[ε]/ε²`, `Λ_m ≅ T_m ⊕ m` (10 / 10 predictions held), q-expansions; WP-LC `HeckeLatticeModuleValidation` (`chk:latcmp` at `M ≤ 4`, 585 checks in the full arm); isign: WP-LC's `H^1` plus-free and R19-8's `H^1_c` minus-free are both correct (`m` residually Eisenstein) |
| Hida (R19-2, WP-HL) | the truncated `Λ`-adic ordinary algebra: R19-2's prototype at `(37, 32)`, `(103, 24)`, `(691, 12)`, `(691, 200)`; WP-HL `HeckeHidaLambda` + `HeckeLambdaValidation` (standard; q-expansion input arm primary); [U] 0.3.0 `sec:u-lambda` ((U13) PROVED at `(37, 32)`, `(103, 24)`) |
| Research (R19-3, R19-4, R19-7 … R19-9, sat1220) | R19-3: Ribet 691 at `Z/691²`, unique unramified lifts `κ_0 = 342252`, `342440` (CMPD), Heisenberg / adjoint-Selmer as SPEC; R19-4: legs (a) Coates–Wiles and (b) Leopoldt; R19-7: the triangle at `ℓ²` and the level-3 / level-4 measures at 37 / 103; R19-8 / R19-9: the linear and bilinear prototypes; F4 ACCEPT WITH REPAIRS (0 B / 1 M / 18 m, repaired at pre.3); sat1220: `(1220, 37)` **not saturated** (`T^sat/T ≅ Z/37`, `I = m³`), the L-F1 rung mechanism, `conj:swappedsat` ([L37] 0.4.0) |
| Notebook (NB-0 … NB-3, NB-report) | **BUILT**: NB-0 the build switches `OC_ENABLE_CUDA` / `OC_BUILD_DOCS` / `OC_BUILD_NOTEBOOK`, presets, CPU-only, the Jetson Orin kit; NB-1 [P] v3.10 (→ v3.10.2 by NB-report); NB-2 `--serve` (`oc-serve/1`), `read_only` tags, two validations; NB-3 the stdlib gateway + page, vendored KaTeX 0.19.0, gateway self-test. NB-4 / NB-5 open |
| Lean (L19-0 … L19-6) | **M3 met**: L19-1 `stablecert_ES` (C1), L19-3 `model7_acyclic` (`stated = 0`), L19-2 the bridge, `rmk:orbifold` on the model, `lem:tauexists`(2), `thm:welldef`(b); F3 ACCEPT WITH REPAIRS (0 B / 0 M / 8 m), all repaired by Lean generalisations (`τ` over `R`, the `(G, Γ, Δ, e, ρ)` form, generic descriptors, `heckeRel_indep_tau`, `heckeTilde_indep_g`, the `-uncond` / `-aux` row split); L19-4 (C2) `X_∂`, `PairHyp` on the model with no hypothesis, `EtaSpec.toIsPairHomotopy`; L19-5 the M4 skeleton (16 `planned` rows). Census of record `LEAN_CENSUS decls=1136 proved=1077 proved_mod_lit=19 stated=0 planned=16 sorries=0 … verdict=OK` |
| Runs (WP-RC) | LAT37 690 / 692 / 694 done and the LAT37 report (six local cells, C-F9 failed on all, layer pattern `k = (n − 688)/2`); E1 `(1220, 37)` + side chain done; `(944, 59)` done; `(1184, 37)` (P7 confirmed) and E2 ×2 (in range) ended during the close's W1 (`WP-RC_report.md`; E1's R18-3 prediction 1 partly refuted, P8 confirmed); 691 `m = 3` done after W1 (`nf691_run.md`: P-NF2-7 confirmed; 31.1 GB, 1:14:34); the θ-socle chain waiting; **Q not run** (never a quiet box) |
| Not run / carried | Q; LAT37A; C7 (R10); C12 (TSan suppressions); NB-4 / NB-5; (H2) / (L1) at depth ≥ 2; the change-of-lattice constant; the measure reading; `ι` over `Z/ℓ^k`; `(37; ω^6, 62)` (killed at 7.3 GiB) — `docs/implementation/slot19/lead_carry.md` |

**[OD] S19 — the slot-19 decision register.** The owner rulings of 2026-10-03 are entries S19-O1 … S19-O15 (as recommended; mirrored under "Slot 18,
the outcome" above); added during the slot and at the close:

| # | Ruling | Effect, and where it landed |
|---|---|---|
| **S19-N1** (owner, 2026-10-03) | `HeckeLatticeModuleValidation` moves `standard` → `slow` | `9dceb384`; roster 177 = 65 / 95 / 17 at the time |
| **S19-N2** (owner, 2026-10-03) | Never run `lake update` (it can delete the shared mathlib through the packages symlink) | CLAUDE.md Lean lane (`e3dd3112`) |
| **S19-N3** (owner, 2026-10-04, relayed) | Direction for slot 20: the cyclotomic-units ↔ L-values ↔ modular-symbols line as far as reasonable; no external CAS (python-flint in research scripts only, cross-checked); Lean M4; the FLT harvest feasibility question; the Shimura scan request | the slot-20 plan v0.1 §0.2 |
| **S19-N4** (owner, 2026-10-04, relayed) | Proceed autonomously through slot 19; close it as slot 18 closed — W1 now under the declared load of our own runs, correctness the verdict, the runs in flight and Q carried into slot 20 | this close; WP-RC20 |

**Slot 20, re-cut from the slot-19 outcome** (from `docs/implementation/slot19/lead_carry.md`; `docs/implementation/slot20/00-slot20-plan.md` **v0.1
(draft)** is the authority for packages and waves; **its owner questions O1–O13 are open**; if this re-cut differs from the plan, the re-cut is the source of
record and the plan is revised to v0.2 before the owner rules):

| Item | Content | Gate |
|---|---|---|
| **Run completion (WP-RC20)** | the chain tail (the θ-socle vs [SAT] §3; `(1184, 37)`, E2, E1, `(944, 59)` evaluated in `WP-RC_report.md`, 691 `m = 3` in `nf691_run.md`); the owner's `wsl --shutdown` onto `memory=80GB swap=8GB`; **Q first on the fresh box** (NEW = the slot-19 close vs REF = the slot-18 close `deab1af`, and the slot-18 close vs `dcd0c30`); the N windows (37 `m = 5`, 103 `m = 4`); LAT37A 3 at a time | O2, O3, O11 |
| **WP-LV3** | the L-value code at depth 2: a generic `m_Eis` reader, (H2) / (L1) at depth 2, the change-of-lattice constant, `ι` over `Z/ℓ^k` | owner direction 1 |
| **WP-MEAS** | the measure route vs Kubota–Leopoldt (MTT); no new `kind` (a `measure()` accessor on `linear` routes) | O5 |
| **WP-SW** | `conj:swappedsat` at 37 `b = 2, 3, 4`; the 103 cells as kit addenda; no 691 attempt | O10 |
| **Lean (L20-0 … L20-6)** | M4 (the 16 `planned` rows; branch H on Shimura Thm 3.24) | O8 (the scan) |
| **L20-H** | the FLT harvest feasibility, isolated and capped, port-vs-bump table only | **O7, the owner's answer pending** |
| **Notebook** | NB-4 (atlas sidecar, `--serve-atlas`), NB-5 spec | O12 |
| **Fable** | F1, F4, F3, F1′ scheduled from the start | O6 |
| **Golden** | zero movement; the add-only candidate list for slot 21 | O4 |
| **Standing** | census 3.2 hold, Proposition M closed as SPEC, the Deo / Medvedovsky query, scans (Shimura first, then Glover, Gross, Haberland, Kohnen–Zagier), R10 and C12 in WP-8 | O13 |
| **Process** | one launcher calendar `s20/windows.txt` + `flock`; measured RSS growth curves for new shapes; post-merge [CLI] regeneration | slot-20 plan §0.3 |
| **Memory ceiling** | summed watchdogs ≤ 60 GB on the 80 GB box (default ≤ 56 GB) | O3 |

**Slot 20, the outcome (v1.25)** (`docs/implementation/slot20/WP-18_close_report.md` §6 is the exit-criteria table; `00-slot20-plan.md` v1.1 the plan):

| Package | Outcome |
|---|---|
| WP-RC20 | Q MET (`bff70807`); TS `(1220, 37)` 18.0 GB, θ`V_src` is not the socle (mechanism refuted, defect untouched); N windows 3 / 3 MET (`RC20_levelm_report.md`); LAT37A 3 / 10 (`LAT37A_report.md`) |
| WP-SW | `conj:swappedsat` CMPD at b = 2, 3, 4 and (follow-up) b = 5 `(1372, 37)`: all five cells of the range at 37 |
| WP-LV3 | the generic `m`-block reader; cross-kind gate at 4 cells; `(258, 37)` bit-identical; `c_f` computed; `ι` over `Z/ℓ^k` (script 049); K62 `(37; ω^6, 62)` run (16.43 GB) |
| WP-MEAS, S1, S2 | `HeckeLValueMeasureValidation` (220 checks); `lfunction/v1` + the `lfunction` verb; the 691 arm (Δ vs Kubota–Leopoldt) |
| S3, S4, S5 | `η_12` / `η_200` at 691 (outside git); Termux recipe (no clang build); [PG] 1.0.0 |
| R20-1 / 2 / 3, R20-5 / 6 | MTT measure with `ℓ^{k−2}`; Frobenius shadows; `c_f = e·v_ℓ(n!) − d_f`; [L37] `app:ribetdata`; F4 ACCEPT WITH REPAIRS |
| Lean | M4 met (weak M4-f); Q5 brief; L20-H stages 1 and 2; R20-L not run (no scan) |
| Notebook | NB-4 (sidecar, `--serve-atlas`); WP-JET (Orin build, gateway on its LAN IP, no patches) |
| Contracts | F1, F4, F1′ ACCEPT WITH REPAIRS, repaired; releases at WP-18 |

**[OD] S20 additions:**

| # | Decision |
|---|---|
| **S20-N1** (owner, 2026-10-04) | Licences: `lean/` Apache-2.0; C++ / CUDA LGPL-3.0-only + the NVIDIA CUDA Toolkit exception; documents CC-BY-4.0; FLT vendoring approved for slot 21 (`slot20/owner_rulings_1004.md`) |
| **S20-N2** (owner, 2026-10-04) | Slot 21 = "talk first" (the 691 story), then the two-variable Hida `ℓ`-adic L-function track (P2–P9) |
| **S20-N3** (owner, 2026-10-04) | The Drive sync is a close-window step; the set includes [CLI], [PG] and the [GT] blueprint PDF; the S3 691 files and the 37 Kummer polynomials go to `data/ribet/` |
| **S20-N4** (owner, 2026-10-04) | After the slot-20 close, `main` is fast-forwarded to `hecke-extensions` (never force-pushed) |

**Slot 21, re-cut from the slot-20 outcome** (`docs/implementation/slot21/00-slot21-plan.md` **v0.1 (draft)**; its owner questions are open):

| Item | Content | Gate |
|---|---|---|
| **Talk (first)** | in-house LLL (`NumberField`), the degree-691 field polynomial with a certificate, the talk pack (691 measure, Hida tower) | owner direction |
| **Cluster** | A-cl `(3460, 691)`, `(4150, 691)` (largemem; the owner submits); the November kit | owner |
| **ℓ-adic track** | P2–P5, P7 → P8 ([U] part 4, contract first) → P9 | after the talk items |
| **Licence** | WP-LIC: licence files, SPDX headers, `NOTICE`, history scan, a guard | S20-N1 |
| **Lean** | FLT vendoring (25 modules), the M5 cut, the Q5 decision, R20-L on the scans | Q5, the scans |
| **Runs** | LAT37A 7 cells (remove PAUSE) | — |
| **Console** | read-only verbs from [PG] `sec:pg-missing`; the `rss()` read-order fix | — |
| **Golden** | zero, or one add-only event (G1/G2/G4/G7) | owner |

**Slot 21, the outcome (v1.26)** (`docs/implementation/slot21/slot21_status_and_close_plan.md` v1.2 §1 is the package table; the close report's exit-criteria table: `docs/implementation/slot21/WP-18_close_report.md` §1):

| Package | Outcome |
|---|---|
| WP-1 | day zero; `Registry/Slot21/` + `cmake/slot21/`; `slot21_close_window.sh` (C-3, `484faea1`), rehearsal `e0718952` |
| T1, T2, T3 | in-house LLL (`NumberFieldLllValidation`); the degree-ℓ Ribet field polynomial DONE at 37, PARTIAL at 691 by plan (F4 ACCEPT WITH REPAIRS); the talk deck |
| P2, P2x | Eisenstein measure exactly in Λ (F4m ACCEPT WITH REPAIRS, repaired); P2x (10, 691) at level 2 |
| P3 | coefficient rings (F4m ACCEPT) |
| P4, P4x | wild characters on the L-side (F4m ACCEPT WITH REPAIRS; root number derived, not calibrated); P4x `(226, 103)` by 128-bit arithmetic |
| P5 | (b), (c) DONE (`HeckeLValueIwasawaInvariantsValidation`); (a) = P9's V12 |
| P6 | CARRIED to slot 22 (needs level-`N` modular symbols) |
| P7, P8, P9 | Λ-adic `q`-expansions; ordinary cohomology as a Λ-module ([U] part 4 first; F4 ACCEPT WITH REPAIRS); two-variable measure by interpolation |
| WP-KIT21 | A-cl WITHDRAWN (`acl_audit.md`); A-cl2 optional |
| WP-LIC | licence texts, `REUSE.toml`, `NOTICE`, `THIRD_PARTY.md`, SPDX sweep, `LicenceGuardValidation`; the 9 pending headers at the release commit |
| Lean | L21-V FLT vendoring DONE; Q5 DONE; R20-L DONE (`hcl` unverified → slot 22); C-4 census re-emit + replay OK; M5 cut text NOT written (carried) |
| Console | 3 read-only verbs (`pow`, `kummer_unit`, `hida_tower`; scripts 050 / 051); the `rss()` read-order fix (`64602a59`; `Check` re-verification: PASSED, the `cross_config.sh` `Check` arm) |
| Runs | LAT37A 10 / 10; census 3.2 kit ready, not submitted; Calegari–Emerton probe (computable half) DONE |
| Other | S4 clang PARTIAL (Termux fix merged; local clang → slot 22); Jetson: no slot-21 run; catalogue refreshed |
| Contracts | releases at C-6 (see the v1.26 header); P2x / P4x / P5 / P5′ text released with its stated referee status, no tag upgraded |

**Slot 22, the outcome (v1.27)** (`docs/implementation/slot22/00-slot22-plan.md` v0.2.x §3 is the package list; `slot22_split_close_plan.md` the close; the exit-criteria table is the plan's §7, to be filled by CLOSE-R's `slot22/WP-18_close_report.md`). Read from the commit log and the reports of the slot; the W1-22 figures are pending:

| Package | Outcome |
|---|---|
| G-EVT | one add-only golden event: 59 tier-A lines (18 117 / 11 886 / 6231); Fable F2g ACCEPT |
| WAKE-1, WAKE-3 | `GammaHLevelN`, `HeckeTameFamilyValidation` (V1 + V2); the survey arm: 25 cells, all case (ii), no finding; F-T referee, repairs R1-R3 |
| NF-PRANK, NF-Q1 | `NumberFieldPRankValidation` (`p = 5`; CE1 / CE2 `rank_upper ≥ 2` at all 12 cells, no counterexample); the 1747-vs-2143 class-group question with adversarial audit |
| LN23-F, DOC22 | the family certificate (Mazur good primes + stabilisation + curvilinear signature), `rmk:levelNcurvefamily`(1) "sufficient, not necessary"; document repairs |
| P10-C, P10, P6 | [C] `sec:nebwildsec` / [U] part 5 (F-U5 ACCEPT WITH REPAIRS); the real Hida tower and wild characters in code (`HeckeLambdaTowerValidation`, `HeckeNebentypusWildValidation`; G11 at ℓ = 13 retargeted to `k = 132`, erratum E1); P6 `HeckeLValueShapiroValidation` (F-T ACCEPT WITH REPAIRS) |
| LES-0, LES-1, LES-C | level-change cone sequence: spec, `CongruenceLevel` / fibre maps / `HeckeLevelNormalityValidation`, [C] `sec:nebles` (Fable referee, repairs R1-R6) |
| MP lane (MP-0 … MP-4, MPT, MPCT) | the Moerdijk–Pronk model: descriptor and rules, nerve, comparison, boundary / level cone, Hecke operators (`OrbifoldMP*Validation`s), [C] `sec:mpmodel`, the non-binding [MPT] 0.3.1 |
| L23 (L23-0 … L23-4, BIN-1/2/3) | ℓ = 2, 3 orbifold census: odd-n theory ([C] pre.10), native F_2 arithmetic, the Z/2^k ladder, the degree-1 amalgam reader, the orbifold record and driver, calibration; even pass launched (4 shards), odd pass prepared |
| G1, G2, PERF1, FQ-PERF | int8 IMMA GEMM and device-resident elimination (`ENGINE_GPU_IMMA`, `ENGINE_GPU_ELIM`; read-only switches); cone / Sturm / iota speed-ups ((13, 700) 435 → 245 s); the `fq.py` trace route (63× on the ingest, RSS 11.5 → 1.2 GB, byte-identical on 49 pieces) |
| Lean | M5 (cut form), MP-L1 … MP-L3 (the M6 orbifold item), LR-Y phases 1-5 (the tree resolution and the Mayer–Vietoris sequence in group-cohomology terms), LV-0 … LV-2 (`dim H^q(SL₂(ℤ); Sym^n F_ℓ²)`, ℓ = 2, 3, every n ≤ 700); [C] markers 140 → 222 on 65 → 86 labels |
| Census | 3.2 refresh (saturation 1459 / 1459); 3.3 signed off 2026-10-08; 3.4-pre.3 (9455 cells, C1 grid complete for 27 primes to n = 700); host-B `sat_run2` running |
| Console / manual / tools | VERB-3 (`--atlas --query`, [PG] 1.1.0), FR-1 themes, [CLI] 1.4.0, census explorer fork and the untrusted-data split (WP-0 … WP-8) |
| Not done / carried | `slot22_close_window.sh` (WP-0's item) only landed at CLOSE-T (T5); C-5 publication deferred (owner 2026-10-07); P11-C, WAKE-4 / 5, NF-K3 stretch not scheduled; W1-22 and the CLOSE-R runs → slot 23 |

**Roadmap rows (slot 12+, recorded, not scheduled; [S11] §12; rule 23 binds — no agent connects to any
host below without the owner's explicit go-ahead):**

| Row | Content | Needs |
|---|---|---|
| **R-C1 — portability** | an aarch64 build (scalar / NEON kernel dispatch beside AVX-512, per-host `CMAKE_CUDA_ARCHITECTURES`: Orin `87`, 2080 Super `75`), `--all` and `GOLDEN_STRICT=1` green on each host type; `cross_config.sh` with a host column; `__int128` verified per site | the owner's go-ahead per host; a build recipe per host; disk / memory rules per host (Jetson 4–8 GB shared) |
| **R-C2 — multi-node search** | the campaign split across hosts by job id (a partition of the grid, one `--output` per host, a merge checking every id once and every `index.json` / `summary.tsv` row byte-equal to a single-host run on an overlap set); LPT admission per host | R-C1 |
| **R-C3 — multi-device per computation** | one large cell (`(700, 691)`, `(2420, 2411)`) over several GPUs / nodes: the tape's device assignment across devices and a host boundary, transfers in the residency pass; ≈ 80–94 GB VRAM aggregate | R-C1, R-C2's merge discipline, an `ENGINE_API.md` multi-device section, the measured `U_ell` lever |
| **R-U1a — the read-only notebook** | a local server wrapping the console (one session per notebook), KaTeX / MathJax on a LaTeX side-channel (a printer mode, no frozen transcript moves), an atlas browser reading the store directly | a [P] section; ConsoleDet unchanged; no new `Console/Core/` exception without the owner |
| **R-U1b — the working notebook** | persistent notebooks, the catalogue and [EX] as linked pages, campaign launch (through R-C2 when it exists), export to LaTeX | R-U1a; the owner's decision on hosting and authentication |

**The spec freeze.** OQ17 gates it: [E] cannot be frozen before the `(160, 691)` verdict is written
into [E §8.2] and `app:claims` — WP-7 does that in slot 1 (a `Y` bump to v1.3.3, resolving the
`\VERIFY` at `hecke_extensions.tex:537`; the `cl:chi` `\VERIFY` at `:1152` stays until
`obl:taubdry`(vi) proves it, [SPA] F6). The **[E] consequential revision of slot 2** ([OD] item 1)
is then the freeze candidate; E0b's strict mode and E1b's `sturm.*` modes are *implemented* from
§3.1 / §2.2 of this plan and *specified* by that revision, so a slip of the revision costs the code
nothing.

**Gates, restated:** E0a → E0b → E1b → E2 → {E3 integration, E6, E7, E8, C5}; E0a → E1a → E1b;
E1s → E1b; C-A1 (met) → E3; C-A2 + C-A3 (met) → E4a → E4b → E5 core → E5 arms; E2 + E4b + E5 → E7;
E8 item 1 → E8; C-A5 + E5 → E9; E0a's grid verdict + WP-7's performance reference → E0b; E0b → C1's
decomposition transcripts; E2 + E3 → the first campaign (`n ≤ 200`). Track C never gates Track B:
the engine's validations are C++ from day one and become scripts additionally, so a slip in the
console costs the engine nothing. E3's *value* (cyclicity per sign, halved matrices, the Eisenstein
line) is why it is scheduled before the boundary's *record integration* despite being lower on the
inventory's dependency list (G9 after G3, [I §6]); the boundary's *geometry* (E4a) is first because
it is the long pole.

**The v1.4 schedule (superseded, kept for the record)** put the contract drafts in slots 1–2, E4 in
slots 3–4, E5 core in slots 4–6 and its arms in slot 7, E7 conditional in slot 6, and had no E8 / E9;
its "What the OP8 re-cut and the OP3 amendment do to the long pole" paragraph is now history: the
deliverable's date moved from slot 6 to slot 5 for the reason above, and the arms from slot 7 to 6.

---

## 9. Reconciliation with the LaTeX audit (spec v1.1)

The audit ([EA]) was answered in spec v1.1, [E App. B]; every item was adopted (none contested). Each
row below was checked against the v1.1 text itself, not against the audit's amendment list: the
section, definition, claim or certificate named in the first column is the one that now carries
the statement. "Plan sections" are the places this document changed in v1.1.

### 9.1 Spec change → plan change

| # | Spec v1.1 change (where it landed) | What changed, precisely | Plan sections touched |
|---|---|---|---|
| 1 | **B1 Sturm bound** — [E Claim 2.7] (a)/(b), **[E Def. 2.8]** `B'(k, ell)`, **[E Claim 2.9]** (`B'` exists iff `ell ∤ [T^sat : T_Z(M_k)]`; pinned values `2, 2, 5, 5, 5, 5, 7`), **[E Claim 2.10]** (what Sturm certifies, given a recorded `B'`), **[E Cert. 5.7]** | `B(k) = ⌊k/12⌋ + 1` is a `Z`-module statement that is **false** at primes `≥ 5` (`(24, 5)`, `(28, 7)`, `(34, 131)`); the certificate sweeps primes `≤ B'(k, ell)`, defined through the **`F_ell`-algebra** generated by `T_q mod ell` on the Miller basis (not the `Z`-span of `T_m`), computed per `(k, ell)` with a cap (default `12·B(k)`), recorded with its certificate, and **unavailable** when `B'` does not exist; `S_sep(ell)` replaces the undefined `S_Eis(ell)`; `(22, 5)`, `(26, 7)` break the naive certificate on the pipeline's own `H^1`, `(32, 131)` breaks only the `Z`-module statement | §0.3 (no bignum), §1.1 (`HeckeSturmBound`), §1.2 (`SturmBound`, `GenerationCertificate::unavailable`), §1.3 (`SturmBoundCertificate`, `SturmCertificate`, `is_final`), §1.4 (`sturm` key), §1.5 (`sturm = auto \| off \| cap=<B>`, `sturm_B_prime` column), §1.6 (`sturm_bound` golden object), §2.1, §2.2 Stage 4(c), §2.3 (cost), §5 (`HeckeSturmBoundValidation`, `HeckeExtSmallEllValidation`, `HeckeExtAlgebraValidation`, gate), §6.2 E1 (+0.5 AU), §6.3 R1/R13, §6.4, §7 (`sturm_bound` verb, `SturmBound` type), §8 (parallel sub-track), §9.2 (Q7 moot, Q15) |
| 2 | **B2 coefficient field** — **[E Rmk. 3.2]**, **[E Claim 3.3]** (`ŵ = w^{ell^N}`, `f \| N`, `ell^N ≥ D`; `P_j` unique; `n_j = t_j − P_j(ŵ)` for all `j`; the `F[ε]/ε²`, `t = α + ε` counterexample), **[E Cert. 5.2]** (the deterministic `P_j` recipe via `U = ker π_j(t_j) ∩ ker π_w(w)`; the witness-range remark `≤ ell` prime factors / `min(f, f') ≤ ell`), **[E Alg. 5.4(2)–(3)]** (`m_S = (n_j)_j`, no `π_w(w)` generator; `K`-span tangent test), **[E D4]** | v1.0's `n_p = t_p − P_p(w)` loses the witness's own direction whenever `min_V(w) = π_w^e`, `e ≥ 2`, and an `F_ell`-span counts one `K`-direction as `f`; both are fixed by the Teichmüller lift and the `K`-span | §1.2 (`MaximalIdealBlock`, `LocalAlgebra`), §1.3 (`LocalityCertificate`), §2.1 (`ŵ` primitive), §2.2 Stage 3 (rewritten), §3.1 (fix steps, `PrimaryBlock` fields, `certify()` codes 25–29), §3.2 (the trap arm), §4 item 1, §5 (`HeckeLocalityValidation`, `HeckeExtAlgebraValidation` `f = 2` arms), §6.2 E0 (+0.25 AU), §7 (`.w_hat`, `coefficient_field`, `teichmuller`) |
| 3 | **Bounded locality loop** — **[E Alg. 5.1(2)]** (default 64 witnesses per block, then `"local": false`, record not final), [E Cert. 5.2] last sentence | the v1.0 "repeat until every block passes" is now bounded; the existing `kResidueWitnessMaxAttempts = 64` is the budget | §2.2 Stage 2, §3.1 step 3, §3.2 (bounded-exit arm), §4 items 1 and 5, §6.3 R8, §9.2 (Q16) |
| 4 | **M1 boundary** — **[E (A1)]** (`B_q`, left cosets `δ_∞ = diag(1,q)`, `δ_j = (q j; 0 1)`, `Tδ_∞ = δ_∞T^q`, `Tδ_j = δ_{j+1}`, `Tδ_{q−1} = δ_0T`; **not** the `β_j`), **[E Claim 1.7]** (`χ_b` on `x^{n−bℓ}N^b` in `H^0(∂)`, the same multiset on `H^1(∂)`, `[y^n] ↦ χ_0`, both `χ_0` for `n < ell`; coincidence rule) | v1.0's C-A2 prescribed the right-coset `β_j` (the `det`-twisted operator, `χ_{b+1}`) and left the `H^0(∂)`/`H^1(∂)` assignment to an E4 probe; v1.1 settles both | §0.2, §0.4 C-A2 (ii)/(iii)/(v), §1.1 (`ρ_n(δ_j)`), §2.2 Stage 6 (coincidence rule), §5 (`HeckeBoundaryValidation` rewritten: monomial eigenvectors, eleven cells, `β_j` negative control), §6.2 E4 (acceptance (b)), §6.3 R9, §7 (`.cosets(p)`) |
| 5 | **M2 duality** — [E Claim 1.6] (adjugate structure, `rad^i(V^∨) = (soc^i V)^⊥`), **[E Pred. 4.6]**, identity 5 of [E §5.1] (v1.10: `HeckeIdentityCertificate` item 7) | "reversed Loewy series" → the Loewy layers of one are the **socle** layers of the other in reverse order (agree only for rigid modules) | §0.2 E7 row, §0.4 C-A4, §1.3 (`IdentityCertificate`), §5 (`HeckeConeValidation`, `HeckeExtEndToEndValidation`), §6.2 E7 |
| 6 | **M3 Jordan units** — **[E Claim 6.1]** (statement and proof), **[E D3]** | the Jordan type of `t_j − a_j` over `F` is the nullity sequence of `π_j(t_j)^s` divided by `f` (S10's partition with multiplicities divided by `f/deg π_j`), not S10's partition itself | §0.1, §1.2 (`ModuleStructure.jordan`), §1.3 (`ModuleCertificate`), §2.2 Stage 5, §7 (`.jordan(p)`) |
| 7 | **M4 Eisenstein class** — **[E D6]** (the Eisenstein line at `m` is `soc(X⁺_{4,m})` when one-dimensional over `F`, undefined otherwise; option (b) of [EA §3.5]), [E Alg. 5.8(4)], schema `eisenstein` | the reductions of the integral Eisenstein and cuspidal eigenlines are not mod-`ell` Hecke data (at `(10, 691)` both lie in the same 2-dimensional socle); a `Z/ell²` run is [Q18] | §0.3 (no `Z/ell²`), §0.4 C-A1 (vii), §1.2 (`CanonicalPosition`), §2.2 Stage 5, §5 (`HeckeInvolutionValidation`, `HeckeExtRamanujanValidation`), §6.2 E3, §6.5, §7 (`eisenstein_line`), §9.2 (Q18) |
| 8 | **M5 schema** — **[E §7]**: example corrected (`"691": "active"`, `"H1_shriek": "all"`, `"eisenstein": "bottom layer (soc)"`); added `local`, `coefficient_field` (`w_hat_exponent`, `P`), structure-map `matrices` (rows: bottom, columns: top), `sturm` (`B_prime`, `cap`, `closure_dim`, `dim_M_k`), `commit`, `model`, `iota_sign`, `convention_check`; the `final` rule restated with `sturm(B')` | the record is now reproducible by a third party from its own text | §1.2 (`HeckeExtRecord`), §1.4, §1.6 (allow-list names `local`, `witness_poly`, `coefficient_field`), §3.1 (`to_json` keys), §3.3, §5 (`HeckeExtRecordValidation`), §7 |
| 9 | **Am. 8 `U_691`** — **[E Claim 8.1]** and its "Verified" paragraph: `c_691 ≡ 542`, `3(U_691 − 1) = −542(T_2 + 24)`, `A^{(1)}(U_691) = I + 221·E_31`, `221 ≡ 542·23·(−3)^{−1}`, Jordan `(2,1)`, `T_691` active | the strongest single test (exercises `U_ell` and `τ(691)`) | §5 (`HeckeExtRamanujanValidation`, `HeckeSturmBoundValidation`), §6.2 E2 acceptance (b), §7 (`ext_10_691.oc`), §8 |
| 10 | **minor 2 Kummer list** — [E Claim 1.8], [E §8.3]: `(24, 103)`, `(24, 2294797)` added (`k = 24`, `n = 22`) | two more cells; `ell = 2294797 < 2^32` but `U_ell` there is out of budget (v1.2: the frozen `U_ell` model, R14; `(26, 657931)` added too, [XA m6]) | §1.1 (`ell ≤ 2294797`), §5 (`HeckeExtKummerValidation`, `HeckeAtlasValidation`), §6.3 R2/R14 |
| 11 | **minor 4 / OQ17 `(160, 691)`** — [E Claim 2.11] (`T_2` alone generates at `(10, 691)`; "for `n ≫ ell`"), [E §8.2] table: the `4:1 → 2:1 + 2:1` reading is **unverified**; one `ComputeMultiOp` run decides | v1.0's `HeckeExtSeparationValidation` asserted the split; v1.1 makes it a probe whose verdict is asserted | §3.4 (the probe in E0), §5 (`HeckeExtSeparationValidation`), §6.2 E0 acceptance (e), §8 slot 1, §9.2 (Q17) |
| 12 | **minor 5 Stage 6** — [E Stage 6]: weight `ell + 1` must be included (`Δ mod 11`) | the atlas range `n ≤ ell − 1` already includes it; made explicit | §2.2 Stage 6, §5 (`HeckeAtlasValidation`) |
| 13 | **minor 6** — [E Cert. 5.7]: `S_sep(ell)` in place of the undefined `S_Eis(ell)` | the sweep's extra primes are `S_sep(ell) ∪ {ell}`; `S_sep` exists only from E6, so E1 sweeps primes `≤ B'` and `ell` and the record lists the set actually swept | §1.3, §2.2 Stage 4(c), §6.2 E6 |
| 14 | **minor 8 / Claim 3.1** — [E Claim 3.1]: both clauses required for the "iff" (`t_2 = (α, α)` has an irreducible squarefree minimal polynomial of degree `f` and is not a locality witness) | v1.0 cited this as "Claim 3.4"; the argument in §3.1 now names both clauses | §3.1 |
| 15 | **minor 11 Stage 1 cost** — [E Stage 1]: `Θ` cost plus the fixed cohomology cost | affects the Sturm sweep's per-prime cost estimate. **v1.2 correction** ([XA M4]): v1.1 read this as "a full `cohom` per prime"; the cohomology is paid once per cell (`HeckeOperatorFamily` takes a computed `cohomL`), each prime costs cosets + τ + Θ | §2.2 Stage 1, §6.3 R1 |
| 16 | **minor 1, 3, 7, 9, 10, §2.2 items, §6 concision** — [E Claim 1.3] `n > 0`; Brown VII.9; Stage 7 `d ≈ n/3` for all six groups and both signs; [E Rmk. 3.2] referenced from Claims 2.2, 4.2, 6.1; Drozd / Ringel; the 7-vertex complex named as the substitute for the `Γ(2)` model; `(198, 691)` and `(160, 691)` merged into one table | no plan consequence beyond citations | §0.1 (Drozd / Ringel), §9.1 |
| 17 | **OQ13** — [E §8.2]: `691 ∥ num(B_200/200)` recomputed (`≡ 217665 mod 691²`; the audit's `259816` does not reproduce, same conclusion) | the index-one *arithmetic* is settled; uniqueness of the congruent eigenform is not | §5 (`HeckeExtSeparationValidation`), §9.2 (Q13) |
| 18 | **Spec renumbering** (v1.0 → v1.1): Def. 2.8 inserted (so v1.0's "Claim 2.8" is now Claim 2.10); Rmk. 3.2 inserted (the gap claim is Claim 3.1, the witness claim Claim 3.3); the certificates (a)/(b)/(c) are Certs. 5.5/5.6/5.7, the Stage 5 algorithm Alg. 5.8, the rank claim Claim 5.9; predictions are 4.3–4.8 | every [E] citation in this plan re-keyed; one v1.0 miscitation ("Claim 3.4" for the gap) corrected | throughout |

No v1.1 change was found that the list above does not cover: [E §1.3] (what the code computes today),
[E §4.1], [E Claims 2.1–2.6], [E Cert. 5.3], [E Certs. 5.5–5.6], [E §6.2] / [E Alg. 6.4] and
[E Stage 7]'s reach statement are textually unchanged from v1.0 apart from cross-references, and the
plan's sections built on them (§0.2, §0.3, §2.2 Stages 2 and 4(a)/(b), §2.4, Stage 6's canonical
field) stand as written.

### 9.2 Owner questions (current numbering), the default this plan assumes, and the owner decision

| [Q] | Status | Affects | Default assumed here | Owner decision (2026-09-14; [OD] = `hecke_extensions_owner_decisions.md`) |
|---|---|---|---|---|
| Q1 notation | open | every identifier | `ell / n_sym / p_hecke / q` as [E]; the crosswalk at the head of this document | **Decided**: confirmed — no plan change [OD §OQ1] |
| Q2 cone action | **resolved** (v1.3), **decided** (v1.4) | E5, C-A3, C-A2, R4, §8 | **v1.3**: the formulation is **(b\*)** of the OQ2 verdict `hecke_extensions_OQ2_verdict.md` (**[V]**, CONFIRM WITH AMENDMENTS): the homotopy lives one level below the cochains, where `τ` lives — the datum is the triple `(τ, τ_∂, η)` over `Z` with `∂η + η∂ = jτ_∂ − τj` certified exactly, and `h := η̃` is **derived** by coset transport. Then (i) the v1.2 sign `dh + hd = Θ_g^∂ r − rΘ_g` and cone map `Φ_g(a,b) = (Θ_g a, Θ_g^∂ b + h a)` **stand** ([V §2.1]; [XA §3.6]'s opposite sign was wrong, §10.2 M6); (ii) the `Hom(ker r^1, coker r^0)` ambiguity is **real for a free cochain-level `h`** — every element of that `Hom` is realised ([V §2.2], PROVED) — and **vanishes identically for an `η`-derived `h`** ([V §2.4]–[V §2.5], PROVED over `Z` for all `ell`), so (b1) holds *with a proof* and (b2) is dropped; (iii) the operator is independent of `(τ, τ_∂, η)` and equals the geometric operator of the Hecke correspondence on the Borel–Serre pair for `6 ∈ R^×` ([V §2.6]); (iv) branch (a) is the special case `η ≡ 0`, i.e. `τj = jτ_∂`, which the shipped `τ` fails — **and the entrywise cochain identity `rΘ_g = Θ_g^∂ r` does not license `h = 0`** ([V §2.7]), so v1.2's branch rule is **withdrawn** and the test becomes a recorded diagnostic. Plan changes: §0.4 C-A2/C-A3, §1.2, §1.3, §1.6, §2.1, §5, §6.2 E4/E5, §6.3 R4, §8, §10.2, §10.4, §11 | **DECIDED 2026-09-15** — the owner accepts [V] and has answered all **eight** of its §8 open points, following the recommendation on every one with three amendments (OP3 both cross-routes; OP5 the Borel boundary group; OP6 confirmed as already applied). The decisions are stated at their sites and recorded in **§11**; the owner record is [OD §OQ2]. [OD §OQ2]'s "branch rule suspended" is superseded (it is *withdrawn*), and its "no E5 code before the verdict is accepted" is **lifted** — E5 is gated on C-A3's acceptance only. One construction item remains open and is *not* a decision: **OC-1**, the `ell = 2` truncation policy (§0.4 C-A2(i)) — **decided 2026-09-16** (`oc1a`, [C] v1.3.0, [OD §OC-1]) |
| Q3 `ι` sign | **resolved** ([C] v1.2.0) — a record field (`iota_sign`) that *names the normalisation* | E3, C-A1, the first campaign | Eisenstein class in `H^1_+` (`H^1_+ ≅ M_k`, `H^1_- ≅ S_k`); `"iota_sign": "eisenstein_in_H1_plus"` emitted from a build-time constant until the contract box exists | **Decided 2026-09-14** (confirmed as an assertion), **checked 2026-09-16** (false for the geometric pullback: Eisenstein in `H^1_−` on 74/74 signed cells), **resolved 2026-09-16** by the owner: [C, def:iota](iv) negated, `ι^* := −ι^*_geo`, so the statement holds by definition and gates ([C, obl:iota](v)); constants odd, `ι^*` = geometric involution twisted by `det`; cost in `docs/implementation/oq3_resolution.md`. Plan change: C-A1(v)/(vi) and the `HeckeInvolutionValidation` row above [OD §OQ3] |
| Q4 `D_n` | **decided, applied (v1.5)** | E7, C-A4 | predictions only (socle↔Loewy form); E7 unscheduled | **Decided**: contragredient local system **plus pairing map**; E7 scheduled at 1.25 AU (slots 6–7) with the pairing at three levels and the PD gate — §0.2, §0.4 (C-A4 = [C] `sec:contragredient`, `cl:pd`), §1.2 (R4 rows), §5 `HeckeDualityValidation`, §6.2 E7, §7, §8 [OD §OQ4] |
| Q5 locality placement | **decided, applied (v1.5)** | E0, §3 | (a) inside `HeckeModuleDecomposition`, so the campaign and every consumer are protected; re-baseline per §3.3 | **Decided**: add refinement + locality certificate; **placement (a) confirmed** (slot-1 confirmation 2) — §3.1 unchanged, `Hecke/SubspaceOps` placed accordingly (§1.1) [OD §OQ5] |
| Q6 `T_ell` in `T_∞` | open | Stage 2 labels, E6 | ideals indexed by full systems `(a_q)_q ∪ {a_ell}`; the atlas stores `a_ell` per twist | **Decided**: full systems confirmed — no plan change [OD §OQ6] |
| Q7 Sturm constant | **moot** (v1.1) | — | no constant: `B'(k, ell)` computed and recorded per cell (row 1 of §9.1); `B(k)` survives only as the seed of the default cap `12·B(k)` | moot; joint answer recorded under Q15 [OD §OQ7] |
| Q8 `sturm`-only records on `∂`/cone and Dickson `m` | **decided, applied (v1.5)** | `is_final` | published with `final = false` + reason `sturm_heuristic` (§1.3) | **Decided-configurable**: closure (cyclic/commutant) required by default; `"final": "heuristic"` via Sturm selectable (`final_mode`, §1.5); **the default-mode disposition is decided** (slot-1 confirmation 8): emitted `final = false` with reason and resumable state, listed in `analysis.txt`, never withheld — §1.3, §1.3.1 R3.2, §2.2 Stage 4(c), §5 Record row [OD §OQ8] |
| Q9 canonical field | **decided, applied (v1.5)** | E6 | `C_{ell,r}` = `CanonicalLess`-least irreducible; Conway named additionally where tabulated | **Decided**: deg-lex least by default; `field_polynomial = conway` reserved (parsed, rejected), no Conway output, the record names the convention — §1.5, §2.2 Stage 6, §6.5 [OD §OQ9] |
| Q10 eigenvalues in the split field | **decided, applied (v1.5)** | E6 report | default the block's own field `F_ell[X]/(π_w)` + `P_p` (now the `coefficient_field` key); split form behind a report option | **Decided**: canonical split field by default (`split_field_report = canonical`), **conditional on the E6 performance gate** (`canonical_field_s ≤ 0.10 × ext_s` and `≤ 2 × own_field_s`); the `F_{ell^r}` non-goal re-examined and **kept**, reopened only by a failed gate — §0.3, §1.5, §2.2 Stage 6, §6.4 [OD §OQ10] |
| Q11 meaning of "all extension classes" | **decided, applied (v1.5)** | §0.1 | the certified record (D1)–(D7) | **Decided**: (D1)–(D7) confirmed; no canonical form; **generators and relations on request** — `presentation(m, group)`, `presentation = on`, `HeckePresentation` with its algorithm and certificate — §1.5, §2.2 Stage 5, §5 `HeckePresentationValidation`, §7 [OD §OQ11] |
| Q12 model reach | **decided, applied (v1.5)** | §0.3, R1 | `n ≤ 1000`; Manin model a follow-up (§6.5) | **Decided**: keep the cochain model (higher-rank blueprint; HPC targets); the reach reframed as hardware-bounded, the first ext campaign at `n ≤ 200` (confirmation 9(b)) — §0.3, §6.2 E6, §6.3 R1, §6.5 [OD §OQ12] |
| Q13 `(691, 200)` index | **decided, applied (v1.5)**; arithmetic half settled (`691 ∥ num(B_200/200)`) | `HeckeExtSeparationValidation` | the computed record is the evidence; the `F[ε]/ε²` prediction is annotated "index one: arithmetic verified, uniqueness of the congruent eigenform assumed", not asserted | **Decided**: uniqueness not a concern now; the record documents the **possible ambiguity** ("uniqueness not checked", no longer "assumed"); the LMFDB lookup is a to-do for whoever runs the first `ell = 691` campaign (E6) — §5 Separation row, §6.4 [OD §OQ13] |
| Q14 predictions as gates | **decided, applied (v1.5)** | §4 item 6 | annotations; [E §5.1] identities are the only hard assertions | **Decided**: annotations, plus the selected cases asserted inside validations (`(10, 691)`, the ten Kummer cells, `(6, 5)`, `(12, 5)`, `(8, 7)`, the boundary characters and Harder once E4 exists) through `predictions = assert` — §1.5, §2.2 Stage 6, §4 item 6, §5 "The OQ14 asserted cases" [OD §OQ14] |
| Q15 `B'` cap and non-existence | **decided, applied (v1.5)** | Stage 4(c), `is_final`, R13, campaign key | cap `B_max = 12·B(k)` (overridable by `sturm = cap=<B>`); `B' = none` ⇒ certificate (c) **unavailable**, the ideal falls back to (a)/(b) and is otherwise `final = false` with reason `sturm_unavailable`, published and listed in `analysis.txt`; the alternative flagged `S_sep ∪ {ell}` sweep is **not** implemented until the owner asks | **Decided-configurable**: both modes implemented, `sturm.unavailable = nonfinal` the **default** and the cap `12·B(k)` (slot-1 confirmation 6); the heuristic sweep behind `heuristic`; the cap-hit state resumable — §1.3.1 R3.3 item 1, §1.5, §2.2 Stage 4(c), §5 SturmBound row [OD §OQ15] |
| Q16 locality loop budget | **decided, applied (v1.5)** | §3.1, R8 | budget = the existing `kResidueWitnessMaxAttempts = 64`; non-local blocks are **published flagged** (`"local": false`, `final = false`, the `NOTE`), the run never aborts | **Decided-configurable**: `locality = budget=64` the **default**, `strict` selectable (slot-1 confirmation 7) with the **terminating** route of §3.1 (Berlekamp subalgebra, residue witness over the whole residue field); resumable in both modes — §1.3.1 R3.3 item 2, §1.5, §3.1, §3.2, §5, R19 [OD §OQ16] |
| Q17 `(160, 691)` multi-operator run | **decided** (v1.1 → applied) | §3.4, `HeckeExtSeparationValidation` | run it in **E0a** on the pre-fix code with the read-only `CertifyLocality` (seconds); the validation asserts the verdict found; the spec row stays \VERIFY until then | **Decided**: run before the spec is frozen — WP-1 runs it in slot 1 (recorded, its own `slow` name or env-gated), WP-7 writes the verdict into §9.3 and [E §8.2]; the spec freeze is gated on it (§8) [OD §OQ17] |
| Q18 Eisenstein line and a mod-`ell²` run | **decided, applied (v1.5)** | D6, E3, §0.3 | the socle definition `soc(X⁺_{4,m})` (undefined when `dim_F > 1`) is the published semantics; `Z/ell²` coefficients are out of scope (§0.3, §6.5); the `ι` sign must be fixed before the first campaign | **Decided**: `Z/ell^k` (preferred) / `Z/n` in the architecture with the first extent fixed as **phase E8** (reduction maps, the `a = b = 1` Bockstein; `ENGINE_API.md` §13 first); D6's socle semantics stays published until an E8 run exists (slot-1 confirmation 9(a)); the `ι` sign is fixed by [C] v1.2.0 — §0.2, §0.3, §1.2, §5 `HeckeReductionValidation`, §6.2 E8, §6.5 [OD §OQ18] |

**The eleven slot-1 confirmations** (2026-09-16, all "yes" with the recommended defaults; [OD] "Slot
1 confirmations") are listed with their sites in §6.4. They are decisions, and this plan records them
as such; none is open.

### 9.3 What would move this plan again

**The verdicts, written 2026-09-16 (slot 1 close, WP-7; sources
`docs/implementation/slot1/WP-1_report.md`, `WP-2_report.md`, `WP-7_report.md`):**

* **E0a grid-locality verdict — every block is local.** `HeckeLocalityValidation`'s grid arm
  recomputes every decomposition the golden harness builds (236 decompositions, 348 blocks; 269 on
  the `k = 1` analytic path, 79 through the matrix certificate) and certifies all 348 local with
  `witness_changes = 0` — the first witness carrying a full certificate is bit-for-bit the witness
  the shipped search accepted — and re-checks all 944 golden `decomp_*` hashes through a lookup:
  `LOCALITY_GRID decompositions=236 blocks=348 analytic=269 nonlocal=0 witness_changes=0 hashes=944
  failing=0 []`. Consequences: §3.3's Claim applies unconditionally; **E0b's re-baseline is exactly
  the 384 allow-listed report lines of §1.6** (192 `report_canonical^q` + 192 `report_full^q`, 0
  in the other 47 kinds), no `--accept-split` entry is needed, and slot-1 confirmation 5 is moot.
* **The `(160, 691)` probe — the first alternative, and only the first.** `HECKE_LOCALITY_PROBE=1
  ./cohomology_app HeckeLocalityProbe` (≈ 8 s): `dim H^1 = 27`; `T_2` and `T_3` alone each give
  `2:1 1:1 2:1 2:1 4:2 6:3 10:5`, `T_5` alone `4:1 2:1 2:1 2:1 1:1 6:3 10:5`; the simultaneous
  decomposition on `{T_2, T_3, T_5}` has **7 blocks, `2:1 1:1 2:1 2:1 4:2 6:3 10:5` in that order,
  every one local, `certify() = 0`**. `T_5`'s `4:1` *is* two `F_691`-rational systems merged at
  `a_5`, and the shipped per-operator refinement already splits it; `T_2`'s `4:2` is a genuine
  residue-degree-2 system on which all three operators agree, and it certifies local with `f = 2`.
  There is no block on which the shipped predicate and the full certificate disagree. **This is the
  value `HeckeExtSeparationValidation` (§5, E2) asserts.** Recorded, not asserted, by the probe
  itself; [E] `cl:bk` and §8.2 carry it since [E] v1.3.3.
* **`U_ell` RSS — two of the three plan points measured, the third cannot run.** Reference box
  (32 cores, 62 GB): `--bench hecke 128 691 691` 5.09 s / **2716.7 MB**; `--bench hecke 256 131 131`
  2.48 s / **1677.1 MB**; `--bench hecke 16 43867 43867` **fails** with `hecke: exact multiply
  overflow` (`Hecke/ExactInt.h`, `__builtin_mul_overflow`) in `U_ell`'s coset construction —
  independent of `n` (`n ∈ {2, 4, 8, 16}` all fail), specific to `p = ell` (`hecke 16 43867 2` runs
  in 9 ms / 12 MB). Bisected at `n = 16`, `p = ell`: `ell = 691` 1.06 s / 118.9 MB, `1009` 1.96 s /
  171.1 MB, `2003` 8.71 s / 360.6 MB, `3617` 33.6 s / 659.1 MB; `5003`, `7001`, `10007` overflow.
  **The `int64` tier of [C] `thm:backend` is exhausted by `U_ell`'s coset data between `ell = 3617`
  and `5003` at `nu = 1`** — a known limitation of the exact-integer coset backend, recorded in
  [C] v1.3.3 (`sec:heckedatum`'s `U_ell` paragraph), [E] v1.3.3 §2.3 and `docs/KNOWN_ISSUES.md`
  §3, not repaired (a wider tier is E1b's or an owner call, separate from the budget question
  `u_ell = auto` answers). The `(16, 43867) ≈ 5.6 GB` figure of §1.5 was a placeholder-model
  prediction, never a measurement. **The fits** of `rss_mb = (ell + 1)(c0 + c1 (n + 1)^2)`: exact
  through the two plan points `c0 ≈ 0.9689`, `c1 ≈ 1.777e-4`; least squares over all six measured
  points `c0 ≈ 0.2197`, `c1 ≈ 1.910e-4` — `c1` agrees, `c0` disagrees 4.4×, and the per-coset
  ratio drifts `0.172 → 0.182` over `ell = 691 → 3617`, so the two-parameter model is rough.
  Either fit extrapolates `(16, 43867)` far past `budget_mb = 2048` (12.1 GB / 44.8 GB), so
  `u_ell = auto` excludes it either way. **Not frozen**: E1b re-fits on a wider grid inside
  `ell ≲ 3600` before choosing `(c0, c1)` (slot-1 confirmation 4).
* **The E0a-binary performance reference for E0b's ±5 % gate** (§3.1): measured on the slot-1
  close tree (the E0a binary — `SubspaceOps`, `CertifyLocality`, `GoldenDump`, `DicksonCount`,
  `Fnv.h` all in it), `RelWithDebInfo`, quiet box, 16 threads, `--repeat 5`, minimum — see
  `WP-7_report.md` §4 for the two `BENCH` lines (`--bench hecke 256 134217757 2` and
  `--bench decomp 128 134217757 2`); WP-1's earlier measurement on its own binary was
  `total_s = 0.5443` / `0.1357`. `--bench decomp` is the sensitive one: it is the single-operator
  case where the `k = 1` analytic path must keep `ŵ` unformed.

**The verdicts, written 2026-09-16 (slot 2 close, WP-13; sources
`docs/implementation/slot2/WP-1_report.md`, `WP-2_report.md`, `WP-4_report.md`, `WP-5_report.md`,
`WP-7_report.md`, `WP-8_report.md`, `WP-13_report.md`):**

* **The re-baseline record (E0b, WP-2).** `git diff 4010bec -- Golden/GoldenReference.inc`
  after the emit: **384 insertions, 384 deletions**, every line a `report_canonical^q` or
  `report_full^q` (192 tier A + 192 tier B), **0 elsewhere**; `golden_explain.py before after
  --allow-keys e0b.keys` exit 0 with **no `--accept-split`** (ten key paths, §1.6);
  `tau_table_p2.txt` byte-identical; `GOLDEN_STRICT=1 GoldenRegressionValidation` tier A 9446/0,
  tier B 4603/0 against the new reference; `EngineDeterminismValidation` digest
  **`0x2fa804dae5e9d98d → 0xe446b3bd2d28bd6e`**, identical on all eight arms (30 of the 966
  records of `GoldenSubset32` are `report_*`); `CampaignSmokeValidation` green with **no pin
  edited** (it hashes no report text). Note:
  `docs/matrix-engine/rebaseline-2026-09-16-hecke-report-v2.md`; the stale-schema banner is
  written into `docs/matrix-engine/results/README.md`. The prediction of §3.3 / [S2] §1 held
  exactly.
* **E0b performance (WP-1, WP-2, close).** The loop with the certificate inside it costs nothing
  measurable on the pipeline's own shapes: interleaved with the E0a binary on a loaded box,
  `hecke 256` ratio 1.003, `decomp 128` ratio 0.980 (WP-1 §3); on a quiet box WP-2 measured
  **0.4284 s / 0.1042 s** against the gates `≤ 0.460` / `≤ 0.109`, and the close tree (WP-13)
  **0.4298 s / 0.1009 s** (`--repeat 5`, min, 16 threads). What did get more expensive and is
  not gated: `GOLDEN_STRICT=1 GoldenRegressionValidation` 3.6 → 3.5–3.9 s and
  `HeckeLocalityValidation` 5.2 → ≈ 6.4 s, both because `certify()` codes 27 and 29 now form `ŵ`
  on the grid's 79 multi-operator blocks — the price of an unconditional certificate.
* **Coverage statement (WP-1 finding 4).** `--bench decomp` and the golden harness are
  single-operator, so the E0b matrix path is exercised on the golden grid only through
  `decomp_sim{2,3,5}^1` (79 of 348 blocks), and **the split branch is exercised nowhere on the
  grid** — by design, that is exactly §3.3's Claim — so its only coverage is
  `HeckeLocalityValidation`'s 48 constructed non-local families, which `compute()` now splits
  into their two maximal ideals at the default budget.
* **E4b diagnostics (WP-7).** `BOUNDARY_DIAG cells=315 cochain_commutes=0/315 eta_zero=0/315
  cusp_supported=0/315 implication_ok=315/315`: on every `(cell, p, ν)` pair of the grid the
  cochain identity `r^• Θ_g = Θ_g^∂ r^•` **fails** and the shipped bulk `τ` is **not a map of
  pairs** — at `p = 2` the cusp-support walk finds 10 of 12 vertex slots and 5 of 9 edge slots
  leaving the boundary (and 11 of 12 / 6 of 9 slots with `τ j ≠ j τ_∂`, the count of non-zero
  `η` slots; [C] `rmk:conestrict`(1) had the pre-v1.1.0 table's 8 / 2 and is corrected at [C]
  v1.4.2), 17 of 28 at `p = 3`, 18 of 42 at `p = 5`, 26 of 56 at `p = 7`, 24 of 42 at `(2, 2)`,
  `ℓ`- and `n`-independent; `eta_zero ⇒ cochain_commutes` holds on 315/315, vacuously. As [C]
  `rmk:conestrict` predicts: **`h = 0` is admissible nowhere and the `η`-table is needed on
  every cell.**
* **The Eisenstein class mod `ℓ` at a Kummer cell (WP-7).** On all ten Kummer cells of [E]
  Claim 1.8 the joint `1 + p^{n+1}` eigenspace of `{T_2, T_3}` (and `T_5` where stacked) on
  `H^1` is **2-dimensional** (`eis_undefined_kummer = 10`); it is a line on every off-Dickson
  non-Kummer cell with `k ≤ 26` (43 cells). [E] D6 made precise: the integral Eisenstein and
  cuspidal eigenlines reduce into the same socle `E` of the non-split block, and only a
  mod-`ℓ²` run (E8) separates them; a "route (a) Eisenstein line" **does not exist** at a
  Kummer cell (`HeckeIotaSignValidation`'s grid never met one). `HeckeExt/HeckeBoundary` decides
  on `E`, with an `inconclusive` state for `0 < rank(r^1 E) < dim E` — never observed.
* **Harder (WP-7).** `harder_applicable=37 harder_consistent=37 harder_inconclusive=0`: `r^1`
  vanishes on the **whole** 2-dimensional `E` at every Kummer cell and restricts a non-Kummer
  line non-trivially on all 27 applicable cells. **But `H^1_! ≠ H^1` at every Kummer cell**:
  `rank r^1 = 1`, `dim H^1_! = dim H^1 − 1 = 2 dim S_k` (`(10, 691)`: `3 / 2 / 1`; `(22, 103)`:
  `5 / 4 / 1`), because `r^1` factors through the **top** of the non-split block, not its socle.
  [E] `sec:tests`' "`H^1_! = H^1` at a Kummer prime" was refuted and corrected in [E] v1.4.0;
  consequently `X_6 = 0` and `dim X_3 = dim H^1` at a Kummer cell, and [C]
  `rmk:coneambiguity691`'s "`r^1 = 0`" arithmetic is stale (flagged for the next [C] `X`,
  recorded at [C] v1.4.2). `(10, 5)`, `(10, 7)` recorded: `H^1_! = 0` and `dim H^1_! = 1`.
* **Dimensions off the classical range (WP-7).** `classical = 37/37` (`dim H^1_! = 2 dim S_{n+2}`,
  `rank r^1 = 1` wherever `ℓ > n + 1`). [S2] WP-7 scope 4's "`≥` at Dickson loci" is **refuted
  on 3 of 6** (`(16,7)`: `1 < 2`; `(20,5)`, `(24,5)`: `0 < 2`): for `ℓ ≤ n + 1`, `dim H^1(∂) =
  ⌊n/ℓ⌋ + 1 ≥ 2` and `rank r^1` reaches it, so `dim H^1_! = dim H^1 − rank r^1` with
  `rank r^1 ≤ ⌊n/ℓ⌋ + 1` is the whole statement (25 such cells recorded); `dim H^1_!` even on
  all 39 cells with `ℓ > n`. At `ℓ ∈ {2, 3}`, `n ≥ 2`: `rank r^1 = dim H^1`, **`H^1_! = 0`**
  (18 cells), the identities recorded and holding on all 90 operator instances.
* **The `η`-table (WP-8).** `PAIR_HOMOTOPY tables=152 checks=113596 failures=0 slots=7504
  nonzero=5266 eta_zero=0/152 fills=3216 max_rings=0 max_coeff=1 policies_differ=2342
  walk_compared=140 tamper_cases=27`: `obl:eta`(i)–(iv) re-derived independently on every table
  (`(p, ν) ∈ {(2,1),(3,1),(5,1),(7,1),(11,1),(2,2),(3,2)}` × `ℓ ∈ {2,3,5,691,134217757}` ×
  `n ∈ {0,2}` at u32, three cells at u64, both vertex-chain policies); the table is
  `ℓ`/`n`/width-independent term for term; every one of the 3 216 edge fills solved on its
  initial neighbourhood with coefficients in `{±1}` (`max_rings = 0`: the ring budget 12 and the
  int64 tier were never approached, `B = 4N² ≤ 576`); the two policies differ on 2 342 slots,
  every difference `∂Λ − Λ∂` for the unique degree-2 `Λ` (`lem:etaunique`); no `FillState` /
  R3 state was needed. **Consequence for the cone (slot 3)**: `η` is non-zero in boundary
  degrees 0 and 1 on every level, so `h^1` and `h^2` will both be non-zero.
* **E1a (WP-4, WP-5).** The whole 56-cell grid plus every trap and tamper arm costs **13 ms**
  (WP-4), the commutant arms **0.10 s** (WP-5); on a real block Stage 3 is `O(k · dim A_S · D³)`
  with `dim A_S ≤ D²/4 + 1` and Stage 4(b) `O(k·u·D³) + O(k·D²·u²)` with `u ≤ m·D` — both far
  under a millisecond at `D = 20`, and on the proof range route (b) is **almost never entered**:
  the socle bound excludes it on every Gorenstein non-cyclic block, `(10, 691)` included (bound
  `2 + 4 − 1 = 5` = the exact `dim C`), i.e. on the whole Kummer list.
* **`U_ell` reach and RSS — unchanged (WP-3 did not run).** The slot-1 entry below stands: the
  `int64` tier is exhausted between `ℓ = 3617` and `5003` at `ν = 1`; **the RSS constants are
  not frozen**, the re-fit is E1b-0's (slot 3, head of Lane B1); [KI] §3 stays OPEN with the
  slot-3 booking; [S2] WP-3's "`ℓ = 10007` at `n ≤ 38`" reach statement was never measured.
* **The document revisions.** [C] v1.4.0 (WP-9, the nine deferred boundary-chapter points, an
  `X` bump) → v1.4.1 (WP-10, the referee's `Y` bump, all nine accepted) → v1.4.2 (WP-13, status
  only); [E] v1.4.0 (WP-11: the two refutations corrected with evidence, tri-state `final`, the
  settings / resumable / per-complex schema, strict locality mode, the socle bound as a clause of
  `cert:comm`); [P] v3 (WP-12: C0 as built, the C1a/C1b re-cut behind E0b, the twelve
  mathematical settings, the R3 resumable handles). The findings the code packages handed to
  the next [C] `X` revision are listed in [C] Appendix E's v1.4.2 entry and in
  `WP-13_report.md`.

**The verdicts, written 2026-09-17 (slot 3 close, [S3] WP-11; sources
`docs/implementation/slot3/WP-1, 2, 3, 5, 6, 7, 8, 10_report.md`, `WP-9_referee_report.md`,
`WP-11_report.md`). The slot made no golden re-baseline and no golden emission** (the reference and
`tau_table_p2.txt` byte-identical to `b391a3a`, digest `0xe446b3bd2d28bd6e`):

* **`U_ell` reach and RSS (E1b-0, WP-1) — repaired; the diagnosis corrected.** The overflow at
  `ℓ ≥ 5003` was never in the coset construction ([KI] §3's and v1.6's attribution, and [S2A] Q5's
  τ-transport suspicion, are both refuted): it was `QuadPoint::moebius` inside [C] `alg:tau` step 1's
  fundamental-domain reduction, whose point coordinates reach `≈ 144.8 N²` so that the Möbius step's
  products die in `int64` at `N ≥ ≈ 4580`. `lem:bounds` did not fail (the certified `B = 4N²` was
  inside its tier) — it had no clause for step 1, which [C] v1.5.0 added as `lem:bounds`(6). The
  repair escalates step 1 per operation to `__int128`, bit-identically wherever `int64` completes.
  **The new reach is `ℓ ≤ 23170`** (largest prime 23167): `certify()` clause (e), `4N² ≤ 2³¹ − 1`;
  at `ℓ = 43867` the τ-table builds without overflow and is refused by that clause (code 51, 20 s).
  Lifting it is a *storage* change (`Mat22W` transporters), an L package nothing needs. Measured:
  `(16, 5003)` 73.1 s / 950 MB, `(16, 10007)` 612 s / 1.9 GB. **The RSS constants are frozen**
  (`u_ell_rss/v2-2026-09-17`, 16 points, §2.2 Stage 1 and §1.5 above); the ten Kummer verdicts are
  unchanged (seven admitted, three refused); `UEllDecision(16, 43867, 2048)` is pinned refused at
  8255 MB. [KI] §3 is RESOLVED with the new limit recorded.
* **E1b (WP-2).** `HeckeExtSturmSweepValidation` 274 checks in 2.37 s. `B' ∈ {2, 3, 5, 7}` on every
  cell measured, so the sweep's primes lie in `S_0` or the family's `(p, r)` cache and no streaming
  pipeline was needed (E2's). At `(10, 691)` the record of E1 (b) holds in full; at `(n, ℓ) = (22, 5)`,
  `(26, 7)` the `{2, 3}` sweep is rejected on a block failing `T_5` resp. `T_7`. Acceptance (d),
  recorded: the ext layer is 0.164 s at `n = 256`, **20.1 %** of the `{2, 3, 5}` pipeline, **38 %** of
  a one-prime `hecke 256` — an owner confirmation for slot 4 (§6.2 E1 (d)).
* **Strict locality (E0b-S, WP-3).** The `(2, 30)` covering example in 0.10 s; the golden grid
  identical under `strict` with `nonlinear_phase = 0` (the terminating route is dead code on every
  computed cell); the split path gives the same partition as budget mode on 9/9 cells and the same
  sub-block *order* on 6/9 — the order is per-mode, a finding for [E]; a latent resume defect of
  slot-2 WP-1 (a carried certified block lost its certificate) fixed, value-preserving.
* **The cone (E5-2, WP-5).** 74 cells, 5350 checks, 1.9 s. `(10, 691)`: `dim H^q_c = [0, 3, 0]`,
  `rank r^0, r^1 = 0, 1`, `dim H^1_! = 2` — **`dim X_3 = 3`**, v1.6's `4` corrected at §0.4, §5 and
  §6.2 E5 (c); the ten Kummer cells `dim H^1_c = 1 + 2 dim S_{n+2}`, `H^2_c = 0`; `H^0_c = 0` on
  74/74; every spot exact (592/592); at `ℓ ∈ {2, 3}` `H^2_c = coker r^1 ≠ 0` where
  `dim H^1(∂) = ⌊n/ℓ⌋ + 1 > rank r^1`. At `n = 256` `compute()` is dominated by `verify()` (11.5 s,
  VmHWM 621 MB = 1.7× `hecke 256`): E5 acceptance (d)'s `1.5×` gate is at risk.
* **The cone action (E5-3, WP-6).** 63 cells, 212 operators, 123 634 checks, 11.9 s. The cone
  identity holds on the stored `C^q_eq` basis in 424/424 degrees and on the full flat space in only
  29 (`DΦ = ΦD` flat on 1/212 operators) — the coset transport uses `φ`'s Γ-equivariance, so this is
  expected and is WP-6's first normative finding for the next [C] `X`; `r^q A = A_∂ r^q` on 424/424
  pairs (74 operators at `ℓ ∈ {2, 3}`, recorded there); `obl:coneexact`(vi) on 335/335 with the full
  `T_{p²}`; (viii)(a) four policy arms bit-identical in `A_c^{(q)}` with both table hashes moving;
  (viii)(b) failing exactly `obl:eta`(v) and moving `A_c^{(1)}` at `(10, 691)`; `eta_zero` and
  `cochain_commutes` false on 212/212; 189 `τ_∂` nearest-vertex ties over the grid; `n = 64` action
  2.1 s / 94 MB (the `O(flat_dim²)` basis sweep of `verify()`).
* **Console C1a (WP-7).** Nine types, 68 verbs, the CLI branch, `GoldenLookup`; exit code 5;
  `ConsoleScriptValidation` 174 checks, `ConsoleCliPreservationValidation` 39; no `HeckeExt/`
  binding (the guard's rule 1) — where the extension layer's verbs register is an owner confirmation
  for slot 4.
* **The citation census (WP-10).** `ContractCensusValidation`: 429 labels, 1408 sites in 121 files,
  0 unresolved at the close.
* **The document revisions.** [C] v1.5.0 (WP-8, the seven deferred items and `lem:bounds`(6), an `X`
  bump) → v1.5.1 (WP-9, the referee's `Y` bump: six arithmetic and proof defects of the `U_ell` item
  and one stale quotation repaired) → v1.5.2 (WP-11, status only); [E] v1.4.1 (WP-8, `cert:cyclic`'s
  canonical generator) → v1.4.2 (WP-11, status); [P] v3.1 (WP-11, status: C1a implemented); this
  v1.7. The normative findings that arrived after WP-8 started (WP-6's four) and the points WP-8 /
  WP-9 did not apply are listed in [C] Appendix E's v1.5.2 entry for the next `X` (slot 5, with E5
  acceptance).
* **Performance reference after slot 3** (`--repeat 5`, min, 16 threads, the best of three rounds
  on the close's tree): `--bench hecke 256 134217757 2` **0.4307 s**, `--bench decomp 128
  134217757 2` **0.1029 s** (rounds 0.4594 / 0.4405 / 0.4307 and 0.1078 / 0.1029 / 0.1051; slot-2
  close: 0.4298 / 0.1009; gates `≤ 0.460` / `≤ 0.109` — met in every round, the `hecke 256` margin
  thin in the first). Slot 3 changed no default code path those two benches run, WP-1 / WP-3 having
  measured their own head-to-heads within noise.

Any change to [E Def. 2.8]'s cap semantics or to [E Claim 2.10]'s range moves §1.3 `is_final` and
Stage 4(c); any change to [E Cert. 5.2]'s witness bound moves §3.1 step 3 and R8; any change to
[E (A1)]'s coset side moves C-A2 and `HeckeBoundaryValidation`'s pinned multisets; any change to
[E D6] moves the `CanonicalPosition` semantics and the `eisenstein` key; any correction to
[E Claim 8.1]'s constants (`c_q`, the `(a_q, c'_q)` pairs, `221`) moves `HeckeExtRamanujanValidation`
and `HeckeSturmBoundValidation`; the `(160, 691)` probe's verdict (§3.4), E0a's four-hash grid
verdict (§3.3), the re-fitted `U_ell` constants (§2.2 Stage 1) and E4's recorded diagnostics
`cochain_commutes` / `eta_zero` and cusp-support walk (§0.4 C-A3(iii)(5), §6.2 E4) are written here
when known. **[V §8]'s eight open points are no longer among them**: they were decided by the owner
on 2026-09-15 and applied at every site, and §11 is now the decision record rather than a flip-list.
What *would* move this plan again on the OQ2 axis is the resolution of the open construction item
**OC-1** (the `ell = 2` degree bound / truncation policy, §0.4 C-A2(i)) — it moves §1.2's data model,
the `ConeCertificate`'s exactness obligation and the record schema — and the construction of the
free `Γ`-model of C-A3(ii.7), with which OC-1 is deferred. **Resolved 2026-09-16** (`oc1a`, [C]
v1.3.0, [OD §OC-1]): the three moves are now concrete — §1.2 gains `q_max` / `truncated` / the
reported-degree list as record fields (E5, `Hecke/HeckeReport.{h,cpp}`, `Campaign/CampaignDriver.cpp`),
the `ConeCertificate`'s exactness obligation is [C] `obl:coneexact`(iv) as narrowed, and the record
identity must include the degree list (the `Job::id()` fix, a separate slot). The substantive
re-cut of §1.2 / §6.2 E5 is pending; this note is the pointer.

**The verdicts, written 2026-09-22 (slot 4 close, [S4] WP-11; sources
`docs/implementation/slot4/WP-1_report.md` … `WP-8_report.md` and the WP-9 referee report):**

* **E5 cost — the slot-3 open point was measured and is FALSE as it was recorded, and the
  acceptance clause it pointed at is defective.** Slot 3 recorded "at `n = 256` `compute()`'s
  `verify()` dominates (11.5 s, VmHWM 621 MB = 1.7× `hecke 256`)". WP-4 measured: `verify()` is
  **half** the cone's wall (4.34 s build + 4.31 s verify) and runs **~20 % below** the cone's
  VmHWM, which is set inside `compute()`'s `Z / B / H / P` elimination loop — and since (d) is an
  **RSS** gate, no amount of certificate work can move it. For the action, `verify()` is ~9 % of
  the wall and **88 % of `compute()` is the standard-basis sweep**, which is not in the
  certificate at all. Measured grid (`Bench`, interleaved against a `9ae1d7a` binary, REF → NEW):
  cone VmHWM 49.1 → 46.1 / 160.5 → 153.8 / 274.5 → 250.2 / 395.6 → 358.8 / **620.0 → 573.2 MB** at
  `n = 64 / 128 / 160 / 200 / 256`; action wall 1.99 → 1.29 / 15.46 → 9.99 / 30.86 → 18.86 /
  57.90 → 36.13 / **122.4 → 75.4 s**. `HeckeConeValidation` 1.9 → 1.7 s,
  `HeckeConeActionValidation` 11.9 → 10.0 s. **Value-preserving**: `A_c^{(q)}` bit-identical, both
  validations' whole printed output byte-identical, all 403 tamper item-set lines identical by
  direct diff, collector digest `0x4ecd2e429ec3b49` and grid digest `0xedbff302058416f3`
  unchanged. Lever 2 of [S4] was **not taken, with the number that says why**: the certificate's
  copies of the inputs' `H` / `P` bases are **0.39 MB at `n = 160` and 0.92 MB at `n = 256`**,
  not the "few MB" [WP3-5] §10.3 assumed, and releasing them would break the certificate's
  "re-derives from the stored matrices alone" contract. The (d) verdict itself is in §6.2.
* **E2 — the record and the driver, and E1 (d) met.** The extension record `hecke_ext/v1` is
  written by a separate writer and `Hecke/HeckeReport.{h,cpp}` was not edited at all, which is a
  **stronger proxy than the golden gate** and it held: no shared helper had to be extracted, the
  ext writer duplicating nothing of `HeckeReport.cpp` beyond four-line list/matrix emitters.
  [E] Claim 8.1 reproduces **through the driver** at `(10, 691)`: `U_691` admitted at 104.06 MB
  predicted against the 2048 budget, `S_0 = {2,3,5,7,691}`, one local ideal with
  `T_m ≅ F_691[ε]/ε²`, and the **four** exact identities in `M_3(F_691)` including
  `3(U_691 − 1) = −542(T_2 + 24)`, the strongest single test in [E] because it exercises `U_ell`
  and `τ(691)`. The streamed route at `(22, 5)` and `(26, 7)` produces a **byte-identical
  record**; the `u_ell` resume reproduces a fresh `auto` run **byte for byte, fingerprint
  included**. `--bench ext` measures E1 (d) at **0.1357–0.1370** against 0.20.
* **E3 — the production involution, accepted entrywise against an independent construction.**
  `HeckeInvolutionValidation` (2954 checks) compares `Hecke/HeckeInvolution` +
  `HeckeExt/HeckeSignSplit` with `HeckeIotaSignValidation`'s own builders — exported
  value-preservingly as `hecke::iota_oracle`, that validation's printed lines
  (`checks=4104267 gating_failures=0` included) byte-identical — and reproduces its reference
  line field for field: `IOTA_SIGN_PRODUCTION eisenstein=plus (geometric=minus) cells=77
  signed=74 route_a=74 route_b=53 both=53 split_match=66/66 split_mirror=0/66 dickson=11
  h0_anchor=-1 (geometric=+1)`. At `(10, 691)`: `dim H^1_± = (2, 1)`, cyclic on both signs, the
  Eisenstein line defined and in the bottom Loewy layer while the unsplit socle is
  2-dimensional ⇒ `"undefined"`; `dim H^q_{c,±} = (1, 2)`, the **mirror** of `H^1`'s `(2, 1)`,
  confirming [C] `rmk:iotapairing`. `[ι_c, A_c^{(1)}]= 0` is **recorded, never asserted**: it
  needs `ι h = h ι` on the stored `C_eq`, which no [C] statement provides.
* **E6 — the first two units, and one bound disproved.** `bernoulli_mod` reconstructs
  `HeckeBoundary`'s pinned `num(B_k/k)` table (`k ≤ 26`) **as an integer**, by CRT over four
  `2^30` primes, **13 of 13 entrywise**, and agrees with an independent Worpitzky/Stirling closed
  form on 1819 values. `GloverFactors` is checked **against the Brauer character of the real
  `ρ_n`** on 3848 `(class, n)` cells — two `F_ℓ[G]`-modules with equal Brauer characters have
  equal composition factors, so that comparison is a proof cell by cell. The WP-9 referee
  **disproved** the raw-factor bound both [E] v1.5.0 and `GloverFactors.h` carried
  (`2⌊n/(ℓ+1)⌋+1`, which gives 1 at `n = ℓ` where the recursion emits 2); the correct bound is
  `2⌊(n+1)/(ℓ+1)⌋+1`, repaired in [E] v1.5.1 and — by this close — in the header comment.
  `HeckeBoundary`'s pinned table is **deliberately not rewired** to `bernoulli_mod`: that moves
  its recorded `harder_applicable` for `k > 26` and belongs with slot 5's record integration.
* **Console C1b, and the guard question closed.** 16 numbered scripts with frozen `.expected`
  transcripts, every hash pinned through `golden(...)` at fingerprint `0`; the mathematical
  settings become `set` keys through a third registry seam, so a key a later slot appends needs
  no console edit. The "open for slot 4" guard question is closed **without widening rule 1**:
  `HeckeExt/RegisterHeckeExtensionVerbs.cpp` registers the extension verbs itself, at the cost of
  one exact-path entry in each guard's rule 2. C1a's preservation guarantee survived: the frozen
  CLI forms are byte-identical, with **one authorised re-capture** (`--bench --help`, because
  `--bench ext` is a new mode and the frozen text enumerates the modes).
* **The census is content-keyed** (`relpath|<fragment>`), a stale entry now **fails**, and the
  retired `relpath:line` form is rejected by name. At the close: 429 labels defined, 1575 sites
  in 128 of 471 files, 4 allow-listed, 0 unresolved, 0 stale.
* **The post-slot-4 performance reference**, and the margin question [S4] §6 asked. Five
  interleaved rounds against a `9ae1d7a` binary, `--repeat 5`, min, 16 threads, quiet box:
  `--bench hecke 256 134217757 2` **0.4327 s** (reference binary 0.4283 s in the same rounds) and
  `--bench decomp 128 134217757 2` **0.0953 s** (reference 0.0928 s), against the standing gates
  `≤ 0.460` / `≤ 0.109` — met in **every round of both arms**, with 5–13 % headroom. **There is
  no drift**: a tighter 12-pair alternating study of `decomp` gives a mean ratio of **1.009** with
  the paired deltas straddling zero (NEW > REF in 8 of 12 pairs, per-arm spread ~4 %), i.e. inside
  the noise. WP-1's "~12 % slower box" was box load, not the tree — it saw the *same* slowness on
  the reference binary — and WP-8's quieter 0.4169 / 0.1016 and this close's 0.4327 / 0.0953 are
  two samples of the same unchanged tree on a box of slightly different load. **No package's
  merge is rejected on performance.**

---

## 10. Audit response (`hecke_extensions_plan_audit.md`, [XA])

Verdict of [XA]: ACCEPT WITH AMENDMENTS. **Every item was re-derived before it was applied** —
against spec v1.1 and the tree at `fbe0765` — and none was applied silently. Evidence gathered for
this response:

* **Tree.** `HeckeReport.cpp:109` (`hecke_report/v1`) and `:204-205` (the false note);
  `HeckeModuleDecomposition.cpp:981-982` (the second copy) and `:1008`
  (`hecke_module_decomposition/v1`); `GoldenHarness.cpp:478-501` (four hashes per decomposition),
  `:590-594` (report texts from `BuildHeckeReportJson`), `:603-612` (`decomp_sim`), `:160-167` (grid,
  64-bit points), `:353` (a **third** `IsDicksonExceptional` copy, pinned as `dickson`);
  `HeckeModuleDecomposition.cpp:687-693, 695`; `CampaignDriver.cpp:637`; `HeckeOperatorFamily.h:112-113`;
  `docs/matrix-engine/results/specs/sweep_full.spec` (`n ≤ 40`, nine `ell`).
* **Mathematics.** `dim C_{M_3}(E_31) = 5` by hand; the socle bound
  `dim End_{A_S}(V) ≥ dim A_S + f·t·s − dim_F soc A_S` (§2.2 4(b)); the cone-map sign and the
  homotopy ambiguity `Hom(ker r^1, coker r^0)` (§0.4 C-A3); the evaluation test's Galois behaviour
  (§1.3). **Computation.** An independent script (Miller-type basis mod `ell`, `T_q`, `F_ell`-closure)
  reproduced every pinned `B'` and gave `B' = 2` on all ten Kummer cells, `(162, 691)` and
  `(200, 691)`, `B' = 5` at `(60, 5)`, `B' = 3` at `(36, 7)`.

**Counts: 29 items — 22 ADOPTED, 7 ADOPTED WITH CHANGE (B2, B3, M5, M6, M7, m2, m17), 0 CONTESTED.** No finding was wrong; the
seven changes sharpen a fix the audit left open or replace a proposed bound that does not work at
this tree's sizes.

### 10.1 Blocking

| # | Verdict | Re-derivation | Where it landed |
|---|---|---|---|
| **B1** `(10, 691)` cannot be `commutant` | **ADOPTED** | `A_S = ⟨I, E_31⟩`; `X E_31 = E_31 X` forces `X e_3 = λe_3`, `e_1^T X = λe_1^T` ⇒ 5 free entries ⇒ `dim C = 5 ≠ 2`; `dim V/m_S V = 2 ≠ f` ⇒ (a) fails too; only `sturm(2)` (`B'(12, 691) = 2`, non-Dickson `m` of `X_4`). Generalised: by the socle bound (b) can never succeed on a non-cyclic module over a Gorenstein `A_S` — so the same holds at **every** Kummer block (all `F[ε]/ε²`-shaped) and at every multiplicity-2 block with `A_S` a field. **Every other pinned certificate re-checked:** `HeckeInvolutionValidation` `cyclic` per sign at `(10, 691)` ✓ (`H^1_+ ≅ T_m` free, `H^1_- ≅ F`); `HeckeExtSeparationValidation` "cyclic per sign" ✓, its unsplit records now `sturm(2)` (`B'(162, 691) = 2`); `HeckeExtKummerValidation` "(a)/(b)" ✗ → `sturm(2)` on all ten cells; no other row pins a certificate kind. The spec's own schema example is affected (§10.4) | §1.3 (`is_final` note), §2.2 4(b)/(c), §5 Ramanujan / Kummer / Separation / SturmBound rows, §6.2 E1 (b) |
| **B2** `CommutantCertificate` not a certificate; structured form degenerates | **ADOPTED WITH CHANGE** | Confirmed both halves: `verify()` read `dim C`, and the trivial witness `w = t_{p_min}` (`:687-693`) is often semisimple ⇒ scalar on the block ⇒ `u = D²`. Adopted: a fixed cyclic-most element; `verify()` recomputes the rank of the stored structured system; no silent naive fallback. **Changes:** (i) a **socle-bound pre-test** that *proves* (b) fails where it applies and states exactly when (b) is needed (non-cyclic `V` over a non-Gorenstein `A_S`); (ii) the admission bound is a **modmul budget** `k·D²·u² ≤ 2·10^10`, not `u ≤ D²/4` — at `D = 170`, `u = D²/4 = 7225` is `≈ 1.9·10^13` modmul, as infeasible as the naive system; (iii) the candidate list is fixed as basis elements then prefix sums (a "lexicographically first combination" is not a finite rule without an enumeration order); (iv) the naive oracle runs only at `D ≤ 24`: [XA §3.3]'s "`D ≤ 64` ≈ `7·10^10`, seconds" is `D⁶` for `k = 1`; with `k = 5` operators it is `≈ 3.4·10^11`, minutes on `MatrixT` | §1.2 `GenerationCertificate`, §1.3 `CommutantCertificate`, §2.1, §2.2 4(b), §5 `HeckeExtAlgebraValidation`, R7, R17 |
| **B3** `U_ell` without a coset budget | **ADOPTED WITH CHANGE** | Confirmed: v1.1 put `ell` into the default family, into the Sturm sweep unconditionally (hence into the golden cells at `ell ∈ {10007, 134217757}`), into E2 (e) and into the `ell = 691` atlas. [E Claim 2.10] writes every `T_q`, `q = ell` included, as `F_q(T_{q' ≤ B'}) + ell·t'` with `t' = 0` on non-Dickson `m` of `X_4`, so the proof never needs `U_ell` unless `ell ≤ B'`. **Changes:** (i) the budget is a frozen **RSS model in `(n, ell)`**, not `ell + 1 ≤ U_max` — a coset count alone cannot express the atlas (692 cosets are ≈ 81 MB at `n = 10` and ≈ 19 GB at `n = 690`); (ii) the **proof** list contains `ell` iff `ell ≤ B'`, whereas [XA]'s "iff `ell ≤ B'` or within budget" would add a membership test that Claim 2.10 already proves; a within-budget `U_ell` still enters `S_0` (Stage 1/2, labels, heuristic range) | §1.2 `u_ell`, §1.3 `SturmCertificate` + `is_final`, §1.5 `u_ell` key, §1.6 (`u_ell = off`), §2.2 Stages 1, 4(c), 6, §5 Ramanujan / Kummer / SmallEll, §6.2 E2 (e), E6, §6.4, R14 |

### 10.2 Major

| # | Verdict | Re-derivation | Where it landed |
|---|---|---|---|
| **M1** wrong writer for golden keys; second note | **ADOPTED** | `BuildHeckeReportJson` writes `hecke_report/v1` (`HeckeReport.cpp:109`) and the block keys itself; the golden texts come from it (`GoldenHarness.cpp:590-594`); `HeckeModuleDecomposition::to_json` is `hecke_module_decomposition/v1` (`:1008`) and unhashed; the second false note is at `:981-982` | §3.1 (three change sites), §1.6, §3.4 E0b, §6.2 E0b |
| **M2** E0 not executable in order; proof covers one hash of four | **ADOPTED** | `GoldenDump` must exist in the "before" binary ⇒ E0a / E0b; `CollectDecomposition` emits `_invariants`, `_certify`, `_witness`, `_U` (`:478-501`); proof extended to all four (§3.3) — it needs one extra condition the audit did not state and v1.2 makes binding: **the new `PrimaryBlock` fields must not be added to the existing hash collectors**, or every decomposition hash moves; `golden_explain.py` diffs the dumped block lists; the grid arm runs on `ell ∈ {2, 3}` and `n = 1` too | §1.6, §3.3, §3.4, §5 `HeckeLocalityValidation`, §6.1, §6.2 E0a/E0b, R5 |
| **M3** ext golden / identity gates outside the claims' range | **ADOPTED** | The grid has `n ∈ {0, 1}`, `ell ∈ {2, 3}` and 64-bit points (`GoldenHarness.cpp:160-167`); Eichler–Shimura and `d_2 = 0` need `n > 0` even, `ell ≥ 5` | §1.3 `IdentityCertificate` (applicability), §1.6 ext subgrid + `ext_excluded`, §2.1 `DicksonInvariantCount`, §5 `HeckeIdentityValidation`, `HeckeExtEndToEndValidation` |
| **M4** resource estimates | **ADOPTED** | `HeckeOperatorFamily` takes a computed `cohomL` (`.h:112-113`): cohomology once, primes cost cosets + τ + Θ; a two-term fit of [I §3.4] (per-coset `0.11 MB` + `5.8·10^{−5}(n+1)²` MB) reproduces all three measured points and gives ≈ 5.6 GB at `(16, 43867)` (inside [XA]'s 5–13 GB) and ≈ 19 GB per atlas run at `n ≈ 690` ([XA]: ≈ 20 GB); measured in E0a before the Kummer arms are fixed | §2.2 Stages 1, 6, §1.5, §3.4 E0a, §5 Kummer, §9.1 row 15, R1, R2, R14 |
| **M5** cross-block matching ill-defined | **ADOPTED WITH CHANGE** | Confirmed: the candidate sequence is seeded by `block.dim` (`:695`), so "the first witness in both" has no meaning across blocks of different size. Adopted: the evaluation test with one block's own witness. **Change:** the Teichmüller exponent is taken for the *tested* block (`ell^{N'} ≥ dim B'`), since nilpotency on `B'` needs it; and a short proof is recorded that a Frobenius-conjugate character passes (same maximal ideal) and a different one fails, so no "up to Galois" clause remains | §1.3 `ExhaustivenessCertificate`, §2.2 Stage 2, §5 `HeckeExtAlgebraValidation` |
| **M6** [Q2] probe cannot decide; C-A3(b) under-specified | **ADOPTED WITH CHANGE** in v1.2; **partly superseded in v1.3** | v1.2 adopted: decide by `r^•Θ_g = Θ_g^∂r^•` entrywise at the end of E4; branch (b) drafted from day one; the walk kept as a necessary pre-check. v1.2's changes: the audit left the sign open ("with its sign"); v1.2 derived `dh + hd = Θ^∂r − rΘ`, cone map `(a, b') ↦ (Θa, Θ^∂b' + ha)` in [v5]'s convention — v1.1's `∂h + h∂ = Θ_g r − r Θ_g^∂` composed in the wrong order. **v1.3, on the OQ2 verdict [V]:** (1) the audit's own statement of the identity, `dh + hd = rΘ_g − Θ_g^∂ r` (**[XA §3.6]**, `hecke_extensions_plan_audit.md:271-274`), **has the wrong sign — plan v1.2's `dh + hd = Θ_g^∂ r − rΘ_g` is right**, re-derived independently at [V §2.1] (PROVED); the audit file now carries a correction note. (2) The audit's "proof obligation that `H^•_c`'s operator is independent of `h`" is, as v1.2 said, **not true for a free cochain-level `h`** — and [V §2.2] sharpens that to: *every* element of `Hom(ker r^1, coker r^0)` is realised, so a free `h` leaves `X_3` undetermined as a Hecke module. (3) But the obligation **is discharged** once `h` is *derived* from a certified pair homotopy `η`: `h := η̃` and [V §2.4]–[V §2.5] prove the ambiguity vanishes over `Z` for all `ell`. So (b1) holds with a proof, (b2) is dropped, and the entrywise identity is demoted to a diagnostic ([V §2.7]) | §0.4 C-A2 / C-A3, §1.2, §1.3, §1.6, §2.1, §5 Boundary / Cone rows, §6.2 E4, E5, §6.3 R4, §8, §9.2 Q2, §10.4 item 4, §11 |
| **M7** dropped spec items | **ADOPTED WITH CHANGE** | Confirmed all four against [E §5.1] item 6, [E Alg. 5.8(4)], [E Alg. 5.1(3)], [E Stage 6]. **Change:** Stage 6's per-`ρ̄` pair is within reach wherever `n = w − 2 + ell² − 1 ≤ 1000`, i.e. `ell ≤ 31` — not only `ell ≤ 7` as [XA] proposed (`hecke 128` runs in 0.12 s, so `ell = 11, 13` at `n ≤ 180` are cheap); deferred above | §1.2 `CanonicalPosition`, §1.3 `IdentityCertificate`, §2.2 Stages 2, 5, 6, §5 Atlas / EndToEnd rows, §6.2 E6 |

### 10.3 Minor

| # | Verdict | Where it landed (with the re-derivation where it is not a pure citation fix) |
|---|---|---|
| m1 campaign evidence is single-operator | ADOPTED | §3.3 — `CampaignDriver.cpp:637` confirmed; the claim is removed, E0a's grid arm is the only evidence |
| m2 `IsDicksonExceptional` is a boolean | **ADOPTED WITH CHANGE** | §2.1, §2.2 Stage 1, §5 Identity row — there are **three** copies, not two (`GoldenHarness.cpp:353` is a verbatim third, pinned tier A as `dickson`); `DicksonInvariantCount(0, ell) = 1` is the correct `dim H^0` for trivial coefficients, the boolean keeps `n > 0`, and the golden `dickson` entry must stay unchanged |
| m3 `GoldenSubset32` has no cell list | ADOPTED | §3.3 (`GoldenHarness.cpp:160-163`) |
| m4 `⌈log₂ D⌉` squarings | ADOPTED | §1.3 `LocalityCertificate`, §2.2 Stage 3, §3.1 |
| m5 Harder outside `n < ell − 1` | ADOPTED | §5 Boundary row (recorded at `(10, 5)`, `(10, 7)`), §6.2 E4 (c) |
| m6 `(24, 657931)` omitted | ADOPTED | §5 Kummer row (all ten cells; `B'(26, 657931) = 2` computed; `U_657931` over budget) |
| m7 relations up to inversion | ADOPTED | §0.4 C-A1 (iii) |
| m8 `gpu` arm runs; ≈ 3 s optimistic | ADOPTED | §5 Determinism row (re-scoped arms, ≈ 12 s) |
| m9 `ValidationRegistry.cpp` allow-list | ADOPTED | §1.1, §5 Architecture row |
| m10 `L·` is a new primitive | ADOPTED | §1.1, §2.1 (`DicksonMultiplication`, with the `det`-twisted equivariance `L(g·(x, y)) = det(g)·L` checked by expansion), §2.2 Stage 5 |
| m11 `X_1` is not inside `X_4` | ADOPTED | §1.2 `CanonicalPosition`, §2.2 Stage 5 |
| m12 cache reuse; `none` costs minutes | ADOPTED | §2.2 4(c), §2.3, R1 |
| m13 per-ideal `sturm` object | ADOPTED | §1.4 (`sturm` verbatim, `sturm_primes`, `certificate_routes`), §5 Record row |
| m14 per-cell ext records | ADOPTED | §1.5, §5 Campaign row |
| m15 verify from emitted data | ADOPTED | §1.2 (restrictions `t_p\|_V` stored), §1.3 `SturmCertificate`, §5 Record row — v1.2 stores the data rather than weakening §0.1's claim |
| m16 `algebra_closure` into `SubspaceOps` | ADOPTED | §1.1, §2.1, §2.2 4(c), §3.4 |
| m17 `k = 1` short-circuit + perf gate | **ADOPTED WITH CHANGE** | §1.3, §2.3, §3.1, §6.2 E0b (c) — the gate uses `--bench hecke 256 134217757 2` and `--bench decomp 128 134217757 2` (min of 5); `CampaignSmokeValidation`'s ≈ 0.9 s wall was dropped as a gate because 5 % of it (≈ 45 ms) is below a validation run's noise |
| m18 stale published records; `Fnv.h` owner | ADOPTED | §1.1, §1.6, §3.4 (E0a sole owner), §8 slot 2 (C1 consumes), R16 |
| m19 basis-dependent `c'_q` | ADOPTED | §5 Ramanujan row (intrinsic checks first, basis pins labelled), R18 |

Also adopted, from the body of [XA] without a number: the deterministic split order of new
sub-blocks (§4.1 → §3.1 step 2); the E2 milestone reworded to "certified or flagged" (amendment 11 →
§6.2 E2); risks R14–R18 (§6.3); the `(12, 5)` Dickson label recorded as a character multiset
(§5.3 → §5 SmallEll row); and the day-one schedule (amendment 12 → §8, as one table with gates,
effort, parallelism and ≤ 4 agents per slot). The effort table is recomputed in §6.2:
**12.5 AU / ≈ 21.5 k lines, M1 = 5.25 AU** ([XA]: 11.5–12 AU, M1 ≈ 5); the difference is E5 at the
top of the audit's range and E2/E6 +0.25 AU each for the items the audit listed but did not price.
(Those are the **v1.2** figures this section responded to. §6.2 now reads **12.75 AU / ≈ 22 k**
after the OQ2 verdict's `3.0 → 2.5` re-cut of the E5 core and the owner's OP3 amendment, §11.)

### 10.4 Consequences for the spec (for the spec author; this plan does not edit `hecke_extensions.tex`)

1. **[E §7] schema example.** `"certificate": "cyclic"` with `"generators_certified": [2]` at
   `(10, 691)` is correct only for a per-sign record; the unsplit record (`"sign": "all"`) must read
   `"certificate": "sturm(B')"` (B1). The example's `"sign": "+|-|all"` should be pinned to one value.
2. **[E Cert. 5.6].** "`O(m²D)` unknowns" should read `Σ_{i,i'} deg gcd(g_i, g_{i'}) ≤ m·D`, which is
   `D²` when `m ≈ D`; and the socle bound (§2.2 4(b)) could be stated: (b) adds nothing over (a)
   unless `A_S` is non-Gorenstein.
3. **[E Cert. 5.7].** On the range of Claim 2.10, "`q ∈ S_sep(ell) ∪ {ell}`" is redundant for
   `ell > B'`; it serves the heuristic range only (B3).
4. **[E (A2)] / Open Question 2.** **Closed in spec v1.2 (2026-09-15).** The homotopy formulation has
   an ambiguity `Hom(ker r^1, coker r^0)` on `H^1_c` that spec v1.1 did not mention (M6) — and it is
   **real**: every element of that `Hom` is realised by some degree-`−1` chain map, so a *free*
   cochain-level `h` leaves `X_3` undetermined as a Hecke module ([V §2.2], PROVED). It is
   **eliminated** by the `η`-based construction: `h := η̃` derived from a certified pair homotopy
   `η: C_*(∂X) → C_{*+1}(X)` with `∂η + η∂ = jτ_∂ − τj`, whose own ambiguity is `∂M − M∂` for a
   unique `M` and therefore a *cone* homotopy ([V §2.4]–[V §2.5], PROVED over `Z` for all `ell`).
   Spec v1.2 states both halves in (A2), in the §2.3 decision box and in `pr:cone`; the plan states
   them in §0.4 C-A3. Also closed there: [V]'s wording correction to (A2)'s "or the cone must be
   built from an `r^•` that commutes with the chosen `Θ_g` on the nose" — it is `τ`, not `r`, that
   one could change.
5. **[E §8.3] Kummer bullet** lists eight cells (`k ≤ 24`) against Claim 1.8's ten (`k ≤ 26`), and
   its "certificate" expectation should follow B1.

---

## 11. OQ2 open points — the owner's decisions (decision record)

**All eight open points of [V §8] were decided by the owner on 2026-09-15.** This section is no
longer a flip-list: v1.3 wrote every decision-dependent passage so that both answers stayed
reachable and tagged each one `[OQ2-OP<k>: …]`; v1.4 has **collapsed every one of those passages to
the decided answer and removed every tag**. What follows is the record of what was decided, by whom
and where the decision now lives. The strings `[OQ2-OP<k>]` survive nowhere in this plan or in the
spec outside this section and §11.1, and there only as historical references.

The owner followed [V]'s recommendation on **every** point, with **three amendments**, marked
**AMENDED** below. [V] itself is a published review document and is **not** edited (§11.1 records
the errata a contract author must not inherit from it).

| # | Point ([V §8]) | Owner's decision, 2026-09-15 | vs. [V]'s recommendation | Where it is now stated |
|---|---|---|---|---|
| **OP1** | Packaging of the boundary datum | The `Γ`-level `τ_∂` on `∂X` (same `s_i`, `δ_i` as the bulk) **is** the normative boundary datum; the one-dimensional `τ_∞` of the left-coset construction is its **Shapiro transcription** and a validation route only | **followed** | §0.4 C-A2(ii) and C-A3(ii.2); applied at §1.3 (`TauBoundaryCertificate` stores `τ_∂`), §2.1 (`HeckeBoundary`), §5 (`HeckeBoundaryValidation` route A), §6.2 E4, §7 (`BoundaryCohomology.tau_boundary`), §8 slot 3; [E (A2)] first bullet and [E App. OQ2] |
| **OP2** | Integrality policy | The mod-`m` fill fallback is **forbidden by default**; the integer tier is widened instead. It stays reachable behind an explicit setting and then sets `integral = false` on the cell — but **`integral = false` is not the default escape**, and a record claiming R-Z must have `solve_regime = Z` on all three tables | **followed** | §0.4 C-A3(ii.6); §1.2 (data model); §6.3 R4 residual risk (i); [E App. OQ2] |
| **OP3** | Second routes; PD adjointness as the gate | PD adjointness (after E7) **is** the acceptance gate for `X_3` at `ell ≥ 5`. **AMENDED:** **both** cross-routes are built as validation arms — the strict-pair `τ^s` route **and** the relative-complex route 3 — not one of the two. They are therefore **committed work**, not an option | **AMENDED** ([V] recommended the PD gate plus *one* route) | §0.4 C-A3(iii)(6); §5 `HeckeConeValidation`; §6.2 E5 (the three-part re-cut, `2.5 + 0.5 + 0.25 = 3.25 AU`); §8 slot 7 |
| **OP4** | Orbifold definitions in the contract now | **Yes** — the general orbifold model (the Borel construction of the pair; twisted chain data on a free `Γ`-model) enters the contract **now, as definitions**, with the construction deferred. That is what makes "the 7-vertex complex is a specialisation" a theorem rather than a slogan | **followed** | §0.4 C-A3(ii.7); [E (A2)] closing paragraph and [E App. OQ2] |
| **OP5** | The boundary group at `ell = 2` | **AMENDED / DECIDED: the Borel option.** The boundary group is `Γ_∞ = ⟨T⟩ × ⟨−I⟩` and `H^•(∂; V_R) := H^•(Γ_∞; V_R)`; the circle model `⟨T⟩` is its **specialisation at `2 ∈ R^×`** (`n` even). The owner's own note: **this is infinite in degree at `ell = 2`** — `H^q(Γ_∞; V) ≠ 0` for every `q ≥ 0` when `2` is not invertible. The mathematics of that is stated in full at the site; the *policy* consequence is the construction item **OC-1**, **decided 2026-09-16** as `oc1a` ([C] v1.3.0 `open:ell2`, [OD §OC-1]; the bulk periodicity above the vcd is [C] `lem:bulkperiodic`) | **AMENDED** ([V §8] gave no recommendation; [V §5.5]'s argument section said `Γ_∞` — the owner decided with the argument section) | §0.4 C-A2(i), including **OC-1**; §0.4 C-A3(ii.7); §6.3 R4 residual risk (ii); [E §1.1] (already defined `H^•(∂) := H^•(Γ_∞; M)`), [E (A1)], [E (A2)] closing paragraph, [E App. OQ2] |
| **OP6** | Sign convention | `∂η + η∂ = jτ_∂ − τj`, hence `h = η̃` **with no sign**. **Confirmed as already applied**: v1.3 had adopted exactly this convention throughout because a convention was needed to write anything down, so the decision changes no text — it removes the caveat | **followed** (confirming what was applied) | §0.4 C-A3(ii.3); the identity it does *not* move is §0.4 C-A3(ii.4) and §10.2 M6; [E (A2)] second bullet and [E App. OQ2] |
| **OP7** | Golden tiers for the new objects | As proposed in [V §7] item 6: `dim X_3`, `dim X_6` and `A_c^{(q)}` char-poly / rank / trace → **tier A**; `Θ^∂_flat`, `h_flat`, the cone bases and the three table hashes → **tier B**. The alternative (keeping the choice-dependent objects out of the golden reference) is not taken | **followed** | §1.6; §5 `HeckeConeValidation`'s independence arm |
| **OP8** | E5 effort re-cut and the §8 slot shift | Accepted — and **superseded in part by the OP3 amendment**: the `3.0 → 2.5` re-cut of the E5 **core** stands and the one-slot shortening of the *deliverable* stands, but the `+0.5` option becomes a committed `+0.5 + 0.25` for the two cross-routes, so **E5 = 3.25 AU / ≈ 5.2 k lines** and the totals are **12.75 AU / ≈ 22 k lines** | **followed**, re-cut under OP3 | §6.2 E5 (the part-by-part table) and the §6.2 effort table + totals; §8 slots 6–7 and the concurrency check |

**Consistency of the OP3/OP8 re-cut** (the three numbers that must agree, and do): §6.2's E5 entry
prices `2.5 + 0.5 + 0.25 = 3.25 AU`; the §6.2 effort table's E5 row reads **3.25** and its totals
read **12.75 AU / ≈ 22 k** (E0–E6) with no optional remainder, `13.75 / ≈ 23.5 k` including E7, M1
unchanged at 5.25 AU and the six-group record at **11.0 AU**; §8 spends `2.5` of it over slots 4–6
(core, accepted in slot 6) and `0.75` in slot 7 (the two arms), with the concurrency check reading
two agents in slot 7 unconditionally.

**Where a decision did *not* settle everything — the one open construction item.** OP5 fixes the
boundary *group*; it does not fix what the implementation does at `ell = 2`, where the boundary,
the bulk and the cone are all unbounded above in degree. **OC-1** (§0.4 C-A2(i)) records that the
contract must fix a degree bound / truncation policy — `q_max`, its place in the record schema, the
certificate obligations at the top of the truncation, and what "exactness of (3.1)" asserts there
— and that this is **to be determined in the contract**, deferred with the free `Γ`-model of
C-A3(ii.7) (OP4). No policy has been invented here. **Decided in the contract on 2026-09-16**
(`oc1a`: `q_max` a recorded run parameter, default 2, derived on a finite model and settable only
where `truncated = true`; [C] v1.3.0 `open:ell2`, [OD §OC-1]); the bulk is now known to be
2-periodic above degree 2, Hecke-equivariantly ([C] `lem:bulkperiodic`), so the stabilisation
alternative `oc1c` is half a theorem. Nothing in the `6 ∈ R^×` programme depends on it; the
standing requirement on E4/E5 is that §1.2's data model stay degree-generic and that the record
carry the three fields — which E0b's re-baseline lands (§1.6, confirmation 3). **The construction
itself is phase E9** (§6.2, slots 8–9, behind the contract chapter C-A5), and the six tests of
[R §5] that would *observe* the remaining half of `oc1c` on the computed bulk column are its
`HeckeFreeModelValidation` (§5) — the referee's "phase E5" is E9 in this plan's numbering
([SP §2.3] item 10).

**What was never an open point, because [V] settles it and v1.3 applied it**: the formulation
itself (b\*), the sign `dh + hd = Θ_g^∂ r − rΘ_g`, the cone map `Φ_g(a,b) = (Θ_g a, Θ_g^∂ b + h a)`,
the withdrawal of the entrywise-identity branch rule, the discharge of the (b1)/(b2) obligation, the
certificate split (`τ_∂` / `η` over `Z`, the matrix identities over `R`), and the integral
functoriality of §0.4 C-A3(ii.6). Those are §9.2 Q2's "resolved".

### 11.1 Errata to [V] as transcribed

[V] is a review document and stands as published; it is **not** edited. But **five** of its
statements are defective, and a contract author drafting C-A3 by copying [V]'s *arguments* would
inherit them. Items 1–4 are loose arguments whose results are unaffected; **item 5 is a wrong
formula** and must not be copied. Where the defect reached this plan or the spec, it has been
repaired at the sites named.

1. **[V §2.2], "`H^0(B) = Z^0(B) = B^0` (no coboundaries in degree 0)".** The second equality is
   wrong in general: `Z^0(B) = ker(d: B^0 → B^1) ⊆ B^0`, with equality only when `d^0 = 0`. The
   construction only ever needs values in `Z^0(B)`, so the theorem stands. Not transcribed into
   either document; nothing to repair.
2. **[V §2.2]'s realisation theorem is proved over a field.** "Every element of
   `Hom(ker r^1, coker r^0)` is realised" uses a splitting of the cochain groups and is stated for
   `R = F` a field; it is **not** claimed over `Z/ell^k` or `Z/m`. This matters now that [OD §OQ18]
   has put those rings into the architecture and C-A3(ii.6) states the cone over them. **Repaired**
   at §0.4 C-A3 (the (b1)/(b2) discharge paragraph) and at [E (A2)]'s third bullet, both of which
   now carry the hypothesis.
3. **[V §2.6.1] argues homotopy-uniqueness of `τ_∂` from "the comparison theorem".** That theorem's
   relative-projectivity hypothesis is precisely what forces `ell ≥ 5` in [C, lem:tauexists], so
   citing it would make the conclusion conditional on exactly the hypothesis it is supposed to avoid.
   The **conclusion is right over `Z` for every `ell`**, but by the explicit argument: `N_0(x)` is
   the unique 1-chain of the (contractible, one-dimensional) component with
   `∂N_0(x) = (τ_∂ − τ_∂')(x)`; `N_1 = 0` because `Z_1(∂X) = 0`; and the (T1)-extension is well
   defined because the boundary stabilisers are central and act trivially. **Repaired** at
   §0.4 C-A3(ii.2), which now states that argument rather than citing the abstract one.
4. **[V §2.3.1], "`η_0(x) :=` an edge path in `X` from `τ(jx)` to `jτ_∂(x)` (both are vertices)".**
   `τ(jx)` is a 0-chain of augmentation 1, not necessarily a single vertex. The construction survives
   — `X` is connected and the difference `jτ_∂(x) − τ(jx)` has augmentation `0` (both (T3)s give
   `ε = 1`), so it is a boundary — but the wording is loose and should not be copied verbatim into a
   contract. Not transcribed; C-A3(ii.3) states the identity, not the recipe.
5. **[V §2.8], “`T_p^2 = T_{p^2} + (p+1)p^n` with `T(p,p) = p^n` on `Sym^n`, [C] Corollary on
   `T_{p^2}`” — WRONG COEFFICIENT, and attributed to [C], which does not say it.** Found by the
   corpus survey of 2026-09-15 (finding **D2**), at `hecke_extensions_OQ2_verdict.md:278`. The
   correct relation is

   > `T_p^2 = T_{p^2} + p·T(p,p) = T_{p^2} + p^{n+1}`,

   i.e. the coefficient is `p`, **not** `p + 1`. Three independent confirmations, all re-derived
   here before recording:
   * **[C] itself** has it right: `hecke_action.tex:507-516` (`thm:relations`(1)) states
     `T_{p^{r+1}} = T_p T_{p^r} − p·T(p,p)·T_{p^{r−1}} = T_p T_{p^r} − p^{n+1} T_{p^{r−1}}` for the
     **full** operators, which at `r = 1` (with `T_{p^0} = I`) is `T_p^2 = T_{p^2} + p^{n+1}`; its
     own caveat at `:515-518` names the `T_{p^2} = T_{Δ^prim_{p^2}} + p^n I` gap that §11.2 is
     about. The spec has it right too: [E §0.2], `hecke_extensions.tex:158`.
   * **The classical statement**: `T_p^2 = T_{p^2} + p^{k−1}⟨p⟩` in weight `k`; here `k = n + 2`, so
     `p^{k−1} = p^{n+1}`, and `⟨p⟩ = T(p,p)` acts on `Sym^n` by `p^n` — `p·p^n = p^{n+1}`. ✓
   * **The degree count**, which settles it without any convention: `Δ_p = Γ diag(1,p) Γ` has `p + 1`
     cosets, so `deg T_p^2 = (p+1)^2 = p^2 + 2p + 1`; the **full** `Δ_{p^2}` has
     `σ(p^2) = 1 + p + p^2` cosets and `T(p,p)` has `1`; hence
     `(p+1)^2 − (1 + p + p^2) = p`. The coefficient is `p`. `(p+1)` is the *number of cosets of
     `Δ_p`*, a different quantity, which is presumably how it got in.
   Not transcribed anywhere: this plan and the spec both carry the correct relation, so **nothing
   needed repair here**. The same error also stood in the working note
   `hecke_extensions_mathematics.md:63` (“`T(1,q)^2 = T(1,q^2) + (q+1)T(q,q)`”), which is **not** a
   published review document and **has been fixed in place** on 2026-09-15. [V §2.8]'s *conclusion*
   — that the Hecke relations hold on the nose on `H^•_c` — is unaffected; only the displayed
   instance of a relation is wrong.

### 11.2 Errata to the binding contract [C] (`docs/latex/hecke_action.tex`)

`docs/latex/hecke_action.tex` is the **binding contract** and is **not edited by this plan** — it is
also about to be superseded by a unified contract. The defect below is therefore recorded here, and
**it MUST be carried into that forthcoming unified contract**; until then, a reader of [C] must
apply this erratum.

1. **[C] contradicts itself on `T_{p^2}`: two numbered prescriptions are off by `p^n·I`.** Found by
   the corpus survey of 2026-09-15 (finding **D1**).
   * **What [C] gets right.** `hecke_action.tex:456-491` (`def:operators`, `eq:fullassembly` and
     the contract box that follows) is explicit: the `P^1(Z/p^r)` coset tables enumerate the
     **primitive** double coset `Δ^prim_{p^r}`, and for `r ≥ 2` the standard operator is the
     **full** one, with `T_{p^2} = T_{Δ^prim_{p^2}} + p^n I`.
   * **Site 1 — `hecke_action.tex:1443-1444`** (`obl:algebra`, a *numbered correctness
     obligation*): “compute `T_{Γ diag(1,p^2) Γ}` by the same pipeline with its `p^2 + p` cosets
     and compare with `T_p^2 − p^{n+1}`”. `p^2 + p` cosets **is** the primitive coset; `T_p^2 −
     p^{n+1}` **is** the full `T_{p^2}` (by §11.1 item 5). The two sides differ by exactly `p^n I`.
   * **Site 2 — `hecke_action.tex:1595-1596`** (oracle 6 of the validation plan): “`A^{(q)}(T_4) =
     A^{(q)}(T_2)^2 − 2^{n+1} I` with `T_4` computed independently from `Γ diag(1,4) Γ` (**6
     cosets**)”. `6 = 2^2 + 2` — the primitive coset again, compared against the full operator.
   * **The correct statement** at both sites: either compare the **full** `T_{p^2}` (the primitive
     operator **plus `p^n I`**) with `T_p^2 − p^{n+1} I`, or compare the **primitive** operator with
     `T_p^2 − p^{n+1} I − p^n I`. Concretely at `p = 2`:
     `A^{(q)}(T_4^{full}) = A^{(q)}(T_2)^2 − 2^{n+1} I` and
     `A^{(q)}(T_4^{prim}) = A^{(q)}(T_2)^2 − 2^{n+1} I − 2^n I`.
   * **The code is right, and this is a documentation defect only.** `Hecke/README.md:75` records
     the shipped witness `T_p_pow_direct = T_p_pow_primitive_direct + p^n I`, and
     `docs/implementation/hecke_action_implementation_plan.md:45` already carried the erratum for
     S14 (“`hecke_action.tex` §`sec:heckedatum` must be reworded — its `P^1(Z/p^r)` reps give the
     primitive coset; the standard `T_{p^r}` of `thm:relations` is the full operator”).
     `§sec:heckedatum` **was** reworded — that is where `eq:fullassembly` came from — but
     `§sec:obligations` and `§sec:example` were not. Read literally, [C]'s own `obl:algebra` and
     oracle 6 would today fail against a correct implementation.
   * **Action required**: carry the corrected wording of both sites into the forthcoming unified
     contract. This plan's own text is unaffected (it never quotes either site), and the [OD R2]
     note that `τ` is integral is a separate matter (§11.1 is not involved).
