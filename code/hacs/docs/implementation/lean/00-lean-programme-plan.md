# The Lean programme: plan v1.10, signed by the owner 2026-11-06 (v1.0 approved; v1.1, v1.2 and v1.3 forecasts; v1.4 wording; v1.5 the M5 line; v1.6 the M6 orbifold item; v1.7 the slot-22 close; v1.8 the M6 line; v1.9 the HeckeZ block; v1.10 the EXPORT data route)

**Status.** **v1.0, approved by the owner on 2026-10-01**: every owner question of §5 (Q1–Q14) was ruled at its
recommendation (slot-15 close item S15-O3), which unblocks L16-0 … L16-6 for slot 16. The text below is draft v0.1
unchanged except for the §5 rulings. Nothing below has run yet. No Lean code, Lake project or blueprint exists yet.
Draft v0.1 was written 2026-09-30 on `hecke-extensions` at `c017710`.

**v1.1 (2026-10-03, owner ruling O4 of slot 18).** The owner approved the re-estimate **as a forecast**:
- L17-0's paragraph in §4.3, refined by L18-0 (`docs/implementation/slot18/L18-0_velocity.md`);
- the v1.1 column of §4.2.

Slot 18 is planned as **M2 + G3's 10 rows**, with G4 as the stretch package L18-7. **Q12: stay on mathlib `db584cd`** unless a slot-18
package names a missing lemma. §4.2's v1.0 targets are kept for the record, and nothing else in v1.0 changed.

**M2 record (slot 18, WP-17).** Q12 = **stay on `db584cd`** (recorded in §5, Q12). **M3's first item** (F3-18 MAJOR 2, carried to
slot 19): instantiate `cor:stablecert` / `chk:stablecert-sound` at `T_e = eT^𝕃` acting on `range e` (`stablecert_ES` /
`stable_of_spec_ES`), so that `hrank` is discharged by `GL2.Sat.heckerankone` and the certified `stable` route is
`proved_mod_lit` over `hES` only. Also in M3: `EtaSpec → Cone.IsPairHomotopy` once the boundary descriptor `X_∂` exists
(F3-18 MINOR 5).

**v1.2 (2026-10-03, slot-19 L19-0; owner rulings O9 / O10 of slot 19).** A forecast, written by L19-0
(`docs/implementation/slot19/L19-0_velocity.md`):
- **M2 was met in slot 18** (F3-18 ACCEPT WITH REPAIRS). G3 and G4's abstract half (L18-7) were also done. M3's remainder (C1
  `stablecert_ES`, the bridge `C(X_bulk) ⊗ R → ChainComplex (Rep R SL(2,ℤ)) ℕ`, `model7_acyclic`) closes in **slot 19** by the
  checkable criterion M3-a … M3-g (L19-0 §4).
- **M4 moves to slot 20** (O10), because slot 19's code lanes take the seats, not because of velocity. M5 → 21, M6 → 22–23.
- **O9:** `model7_acyclic` is to be proved (`stated = 0`). L19-0 §2 finds that the statement concerns the **infinite** cover
  `X_bulk`, so `decide` checks only the local tables and a finite base case, and the global step is induction on `SL(2, ℤ)`
  (connectivity and `Z_2 = 0`: generation by `S`, `T`; `H_1 = 0`: a Euclidean descent). The forecast is 210 min with
  P(`stated = 0`) ≈ 0.5. The fallback leaves exactly one `stated` row, `model7_contract1`, reported as "M3 met modulo H4(ii)-(1)".
- §4.2 gains a v1.2 column and §4.3 a "Revised by L19-0" paragraph. Nothing else changed.

**v1.3 (2026-10-04, slot-20 L20-0; owner rulings O7 / O8 of slot 20).** A forecast, written by L20-0
(`docs/implementation/slot20/L20-0_velocity_recut.md`):
- **M3 was met in slot 19** (F3-19 ACCEPT WITH REPAIRS, 0 B / 0 M / 8 m, repaired). `model7_acyclic` is proved, so `stated = 0`
  and O9's fallback was not needed. The M4 skeleton (16 `planned` rows) also landed in slot 19 (L19-5).
- **Slot-19 velocity:** the implementers took ≤ 147 min (birth-time based; upper bound 314) against L19-0's 525 central (×0.28) and
  780 bottom-up (×0.19). This is the fourth slot at ≈ ×0.2. The ×1.0 rule for "no finite skeleton" is retired: `model7_acyclic` ran
  at ×0.20. F3-19 took 82 min and is now the longest Lean item.
- **M4 in slot 20 by branch H** for M4-c / M4-d / M4-e / M4-f. There are four Part-L rows: `hTp` (Shimura Thm 3.24 / Prop 3.30),
  `hcop`, `hcomm` (Prop 3.8) and `hecke-classical` (Brown III.9–10, Ash–Stevens §1). Each is stated on the model's `Tdc` in this
  project's notation, and the Shimura locators are `\VERIFYloc` until R20-L reads the owner's scan (O8). Branch P is a stretch.
- `cosetData_nonempty_stmt` is **not** narrowed: mathlib `db584cd` has `exists_Gamma_le_conj`.
- P(M4 in slot 20) ≈ 0.85. M5 is slot 21, and M6 slots 22–23 (band 22–25), unchanged.
- §4.2 gains a v1.3 column and §4.3 a "Revised by L20-0" paragraph with the velocity table. Nothing else changed.

**v1.4 (2026-10-05, slot 21; owner ruling Q5-2).** Wording only (`docs/implementation/slot21/owner_rulings_Q5_1005.md`, Q5-2; brief
`docs/implementation/slot20/L20-6_Q5_brief.md` §5.2): the owner accepted **"M4 met, M4-f in the weak form"** as [LP]'s M4 line. The branch-P alternative
(`cor` on the bar complex) is M6 scope; `thm:classical` stays with [C]. Nothing else changed.

**M4 record (slot 20, L20-6).** F3-20 (`docs/implementation/slot20/L20-6_F3_audit.md`): ACCEPT WITH REPAIRS, 0 B / 1 M / 9 m,
repaired in `docs/implementation/slot20/L20-6_repairs.md`. **M4 is met, with M4-f in the weak form**: `thm:classical-model`
states that `T_{ΓgΓ}` has the shape `cor ∘ (c_g)_* ∘ res` for *some* `cor` with `cor ∘ res = [Γ : Γ'']` (hypothesised,
`lit:hecke-classical`), which does not identify `cor` with the corestriction. [C] `thm:classical` stays open in [C]'s sense and
carries no `\LEAN` / `\LEANlit` marker, nor does `eq:corconjres`. `def:m4-hecke` is a `proved` definition row: `Tfull` is defined
by the assembled form `eq:fullassembly`, and `eq:fullop` gets no marker (the elementary-divisor enumeration is an M5 item). So
`planned = 0`. The Shimura, Brown and Ash–Stevens locators, including the nebentypus Thm 3.34 / 3.35 / §3.3, stay unverified
until R20-L. M4 may be met with them unverified (O8); supersession (Q5) may not.

**v1.5 (2026-10-09, slot 22, package M5).** The M5 line. M5 is the item set the owner's Q5 rulings (slot 21, Q5-2 / Q5-4) and
the slot-22 plan §3 put into M5, not §4.2's original M5 row (G7 Dickson invariants, G11 finality, L3-b(3)/(4)), which stays
open for a later milestone (to be re-planned with M6-B). The cut is `docs/implementation/slot22/M5_cut.md`, the record
`docs/implementation/slot22/M5_report.md`; [GT] Part M5 (`lean/blueprint/src/gt_part_M5.tex`, 14 rows, all `proved`), Lean
`lean/GL2/M5/{Smith,FullOp,Transport}.lean`. Nothing else in the plan changed.

**M5 record (slot 22).** **M5 is met in the cut form, F5 pending**:
- **M5-E (met).** The elementary-divisor enumeration (`thm:m5-dc-enum`: every integral `δ` of determinant `p^ν` lies in exactly
  one `Γ p^j diag(1, p^{ν−2j}) Γ`, `0 ≤ 2j ≤ ν`), `T_{ΓgΓ}` depends only on the double coset for `τ` over `R`
  (`prop:m5-tdc-dc`), and **[C] `eq:fullop` = [GT] `Tfull`** on the model for every complete irredundant system of
  representatives (`thm:m5-fullop`). `eq:fullop` keeps no marker (Q5-4).
- **M5-T (met).** The corestriction in every degree from the vendored `Cores.corFin` (`def:m5-corH`), the classical operator
  `Tcls g n = cor ∘ (c_g)_* ∘ res` with the genuine `cor` (at a chosen transversal; independence proved for n = 0, 1 only), `Θ` as an isomorphism and the transport `TclsM g n = Θ⁻¹ Tcls Θ ∈
  End(H^n)` (`def:m5-Tcls`); FLT's `heckeH1` / `heckeInv` are its degree-1 / degree-0 members for every transversal
  (`thm:m5-heckeH1`, `thm:m5-delta0`), and `Tcls 1 ∘ δ = δ ∘ Tcls 0` for short exact sequences of `Δ`-modules.
- **M5-C (cut to M6).** [C] `thm:classical` in [C]'s sense (`Θ ∘ T_{ΓgΓ} = Tcls ∘ Θ`) is not proved: `Θ` natural and
  `δ`-compatible (through mathlib's Ext isomorphism), `δ`-compatibility in every degree and effaceability among `Δ`-modules
  remain. `thm:classical` and `eq:corconjres` keep no marker; `thm:classical-model` (weak form) is unchanged. M6 with branch P.
- Census and replay lines: `M5_report.md` §3.

**v1.6 (2026-10-10, slot 22, F-MP3 conditions C1-C3).** The M6 "orbifold" item is recorded as met (§4.2's M6 row). Nothing else in the plan changed.

**M6 orbifold item (slot 22): MET (F-MP3, 2026-10-10)**, with conditions C1-C3 discharged by this edit. The item is L0-L10 of [MP] §8.2, L6
included, before `thm:classical` (owner Q5, 2026-10-09). Reports: `docs/implementation/slot22/MPL1_report.md`,
`docs/implementation/slot22/MPL3_report.md`; gate `docs/implementation/slot22/F-MP3_gate.md` (Fable: MET WITH CONDITIONS, then C1-C3 applied).
Lean `lean/GL2/MP/`, [GT] `lean/blueprint/src/gt_part_MP.tex`; census at `e236ed62`: `decls=1987 proved=1922 sorries=0 global_axioms=0
unresolved=0 stale=0 verdict=OK`, replay `modules=176 ok=176`.
- **Scope (C2).** L0-L10 proved: the comparison is unconditional on `M₇` and `R_ℤ` over every commutative ring, normalised and
  unnormalised; naturality, refinement invariance and the Bredon "if" are on the unnormalised complex `C^•_un` (the normalised `u^*` is not
  stated); label independence is on cohomology only; `prop:mpbredon`(2) is the "if" only and (3) is open; the predicates live on `MPDatum`.
  Not proved: `prop:mpbredon`(2) "not only if", `prop:mpbredon`(3), the label chain homotopy, L11-L16.
- **Open items, none gating M6-orbifold.** `mpComparisonNat = mpComparison` (later rows use `mpComparisonNat` only); the "not only if" witness;
  the label chain homotopy; L11-L16.

**v1.7 (2026-10-12, slot-22 CLOSE-T).** The close record; nothing is re-planned and no milestone changes status.
- **M5 stays "met in the cut form"** (`M5_report.md` m4): M5-E and M5-T met; M5-C ([C] `thm:classical` in [C]'s sense) is M6 scope, branch P. `thm:classical`, `eq:corconjres` and `eq:fullop` carry no `\LEAN` marker in [C] 1.22.0.
- **The M6 brief** is `docs/implementation/slot22/M6B_brief.md` (v1.0, 2026-10-12): the core is A (the strong M4-f on the bar complex: A1-A3) + A-T (the tree resolution instance) + C-w (the "not only if" witness) + the `TreeCyclic` split, ≈ 4 agent-days nominal (band 3-6) plus a Fable audit F6; Hida theory ([U]) and G7 / G11 are not in M6 and are re-planned from it. Its owner question (may [GT] supersede [C] wholesale at M6?) is answered **no, by recommendation** (no chapter of [C] meets the supersession checklist); it is the owner's.
- **The O-6 lane** (`L23_master_plan.md` §6): LG-1 … LG-4 (the general theorems for ℓ = 2, 3) and LV (the per-cell checks to the O-6 bounds) are placed in **slot 23** (`slot23/00-slot23-plan.md`); LH (Hecke per cell) in **slot 24**. LG-2's general form may need Dickson's theorem for `GL₂(F₂)` (not in Lean; slot-23 risk K4).
- **Slot-22 Lean state:** `LEAN_CENSUS decls=2776 proved=2711 … verdict=OK` (LR-Y phase 5, `HANDOVER_1012.md` §2); [C] 1.22.0 carries 222 markers on 86 labels. LR-Y open items: `e∪−` and the `q = 1` clause (cup products), `mvConn` as mathlib's connecting map, bar-vs-Ext comparison.

**v1.8 (2026-10-20, slot 24, LEAN "M6 close"; plan `slot24/00-slot24-plan.md` item 10; report `slot24/LEAN_M6_report.md`).** The M6 line, in
the explicit form of `slot23/F6_M6A_audit.md` §5 criterion 7 (never a bare "M6 met"):
- **M6 met (core, `M6B_brief.md` D1): [C] `thm:classical` in [C]'s sense for M4's `Θ` (= `Θ_can`, A-Θ), every degree; the Hecke operator
  does not depend on the resolution (A1); `cor` transversal-independent and `cor ∘ res = index` in every degree (A3); the tree-resolution
  instance, every ring (A-T); `hcl` retired (`lit_hyp` 28 → 27); the `prop:mpbredon`(2) "not only if" witness (C-w, slot 24:
  [GT] `thm:mp-bredon-zero`, `thm:mp-epsmp-witness`, `GL2.MP.BredonWitness`, through LG-1's `thm:lg-exp2`).** The `TreeCyclic` split is
  **dropped** (cpre13 lowered `TreeCyclic` to 7.31 GiB, so the split buys no replay headroom). The orbifold item was met in slot 22 (v1.6).
- **Not in M6, re-planned:** Hida theory / [U] mirrored / G8 and the G6 integral line → **M8**; branch P (the ring half, option B) and G7 / G11
  (option G) → M7; cup products (option D) after M7; `mvConn` (E) backlog; A-MP and `prop:mpbredon`(3) (C) stretch, open.
- **Owner-gated (D5, not applied):** the clause-scoped [C] `\LEAN` markers on `thm:classical`, `eq:corconjres` (degree-`n` form) and the
  witness sentence of `prop:mpbredon`(2) are **proposed** in `slot24/LEAN_M6_report.md` §4; [C] is unchanged by this package.
- **Census and replay of record (slot 24, LEAN M6):** `LEAN_CENSUS decls=3279 proved=3217 proved_mod_lit=35 stated=0 planned=0 sorries=0 global_axioms=0 unresolved=0 stale=0 lit_hyp=27 native=0 gl2_consts=12242 escapes=0 modlit_bad=0 hyp_bad=0 sources_hash=OK verdict=OK`; `LEAN_REPLAY modules=224 ok=224 failed=0 peak_rss_gib=13.79 peak_module=GL2.Checkers.TauP2 cap_gib=16 rc=0 killed=0 … verdict=OK` (`GL2.MP.BredonWitness` alone 7.25 GiB).

**v1.9-draft (2026-11-05, slot 25, wave 0; for owner sign-off with the 1.24.0 RC (RC124); ruling Q18 of `slot24/heckez/06-work-packages.md`, audit
finding F8 of `slot25/PLAN_audit.md`).** Not signed: until the owner signs, v1.8 stays the version of record. The HeckeZ block, and nothing else:
- **Scope.** One block of work, the HeckeZ lane (`slot24/heckez/07-lean-plan.md` v0.4, `GL2.HeckeZ.*`): 21 LEAN-CORE items, twelve checkers
  (K1, K1′, K2g, K2ℓ, K3–K7, K9 certificate checkers; K8, K10 consistency checks `orc:`), nine hypothesis structures
  (`hES_N`, `hES_N_an`, `hSturm`, `hSemisimple_an`, `hScalar23`, `hTellRank`, `hMazurEis`, `hHidaControl`, `hEmertonEis`), ≈ 4 800–8 000 lines.
  It is orthogonal to M1–M8 of §4.2 and does not move them; [C] stays the contract and no `\LEAN` marker on a `sec:heckeZ` label is
  set before WP Z0 has landed `sec:heckeZ` (after release).
- **Milestones (07 §10, as defined there).**
  | M | content | Lean WPs | C++ input |
  |---|---|---|---|
  | **M-HZ1** | Ramanujan 691: `T1_691` (Prop. 5.3), `proved_mod_lit` over `hES` only | L-HZ0 | none (existing `HECKE_DUMP_SAT_CERT`; descent JSON). **Met in slot 24** (`slot24/heckez/MHZ1-report.md`; merge status per the slot-25 plan) |
  | **M-HZ2** | Thm. 4.1 at level 1 on T1, T2, S1 (31 cells); the congruence module's ℓ-part exact only at Eisenstein primes < 2^31.5 | L-HZ1 | χ / f, saturation certificates (data route below) |
  | **M-HZ3** | 03 at level 1, ℓ ∈ {2,3}: LB-1 … LB-6, K5–K8 | L-HZ2 | descent record, 03's `s03` dumps |
  | **M-HZ4a** | Mazur cells (prime level, weight 2): K2ℓ + `hMazurEis` + K10, K10′ | L-K10 (after H3, LIT) | HZ-RAT only |
  | **M-HZ4b** | level N, anemic in general | L-HZ3 | the export of H^1_(ℓ)/ℓ^K |
  | **M-HZ5, M-HZ6** | full algebra (after U_p over Z); scale and deferred | L-HZ4, L-HZ5, L-H0 | later (slot 26+) |
  K9 (`hHidaControl`, `hEmertonEis`) is package L-K9, after H1's data. Q18's one milestone is M-HZ1 together with the level-1 certificates
  (M-HZ2); M-HZ3 … M-HZ6 are listed for the record and are signed as part of the lane, not as additional exit criteria of v1.9.
- **Data route (F8.2).** Cell data (χ, f, Pratt trees, saturation certificates) come from the ed.1 descent records and the shared slot-25
  binary `$HACS_DATA/s25/bin/cohomology_app` with `HECKE_DUMP_SAT_CERT[_CELLS]` into scratch `s25/lhz1/` (a scratch emitter,
  outside the tree), through a generator under `lean/tools/` with a sha256 ledger (as `heckez/mhz1-data/`); `HECKE_DUMP_HZ_CERT` (HZ-EMIT)
  replaces the generator route once it lands. Committed data modules import `HZExec` only (never Mathlib).
- **Trusted C++ outputs (Q10(a)).** Exactly three, each named in every theorem's statement: (1) the dumped matrices of the Hecke operators
  (`tb_mat`, dump sha256s); (2) the integral characteristic polynomials of the descent (`tb_chi`; certified by the descent's CRT bound and
  cross-checked in Lean modulo the certifying prime); (3) for K9 only, B_k/k mod ℓ² (`tb_B`). `tb_int` (M-HZ5) enters with that milestone.
  Nothing else is trusted; a certificate field the record does not carry is not emitted.
  **(v1.10) `tb_mat` is served by two emitters**, `HECKE_DUMP_SAT_CERT` and the slot-25 EXPORT (`DescentRecord.module(ℓ, K)` / `ExportModule`
  dumps on the shared slot binary); both are allowed data routes. On the EXPORT route `tb_mat` comprises the generators' kinds and exponents
  and the adapted-basis claim (which generators are torsion, that they generate tors_ℓ, that the free generators are a basis of L/ℓ^e), not only
  the operator entries; the EXPORT reads are still `tb_mat`, a dumped Hecke matrix, and not a fourth trusted output. Every theorem that uses
  such a read names the dump file and its sha256. M-HZ3's K6 and K7 reads (5 of 5 theorems) and 13 of M-HZ2's 39 Prop. 5.6 reads rest on the
  EXPORT alone.
- **Caps and rules (07 §9, F8.1, F8.6).** ≤ 22 GiB summed RSS per wave, under the shared lock
  `$HACS_DATA/lean-deps/.lane.lock` (`flock`) and a joint ≤ 40 GiB with the trace-formula Lean session, inside the ≤ 48 GB
  summed-watchdog rule; **at most 3 new theorem modules per `lake build` invocation**, waves named explicitly, never a bare `lake build` of
  the lane while another Lean job runs; data modules ≤ 30 cells and ≤ 120 s modelled (≤ 4.7 GiB); a batch ≤ 3 data + 1 theorem module
  (≈ 21.6 GiB); an RSS watchdog per `lake` process; `disk_guard.sh --min-free-gb 15` first; plain `lake build` (no `-j`), never `lake update`,
  never beside a ≥ 20 GB C++ run; replay one module per process, cap 16 GiB (needs ≥ 22 GB free); **no `native_decide`**.
- **Acceptance, every HeckeZ milestone.** `LEAN_CENSUS … sorries=0 global_axioms=0 native=0 unresolved=0 stale=0 verdict=OK`; `LEAN_REPLAY … verdict=OK`;
  `census.tsv` by `lean_census.sh --emit` in the same commit; new rows `proved` / `proved_mod_lit` with `lit_hyps` ⊆ the nine; one
  tampered-certificate negative control per checker; `LeanCensusFileValidation` (fast) green; `add_spdx.py --check` and `LicenceGuardValidation`
  `verdict=OK` (Apache-2.0 headers in `lean/`); an adversarial Opus audit of the statements against 01/03/05 at each milestone.
- **Sign-off.** The owner signs v1.9 with RC124; until then the HeckeZ Lean work proceeds under the slot-25 plan wave 0 as a draft. Nothing in
  `lean/` is changed by this text.

**v1.9 (2026-11-05, slot 25): signed by the owner 2026-11-05**, together with the release of [C] v1.24.0 and [E] 1.24.0. The text of
v1.9-draft above, unchanged (header and this entry only); v1.9 replaces v1.8 as the version of record. The draft's sentence "Not signed: until the
owner signs, v1.8 stays the version of record" and its "Sign-off" item are kept as history.

**v1.10 (2026-11-06, slot 25): signed by the owner 2026-11-06** ("I agree with the export"; audit findings A1 of `slot25/LC11_audit.md` and B3 of
`slot25/MHZ3_audit.md`). The data-route item "Trusted C++ outputs (Q10(a))" of v1.9 gains one sentence block (marked "(v1.10)"): `tb_mat` is
served by two emitters, `HECKE_DUMP_SAT_CERT` and the EXPORT, and every theorem names the dump file and sha256. Q10(a)'s three trusted outputs are
unchanged; nothing else in the text changes; v1.10 replaces v1.9 as the version of record. Nothing in `lean/` is changed by this text.

**Commission.** The owner, 2026-09-30, verbatim in substance: *"We often encounter minor inaccuracies, literature gaps
and potential normalization and convention conflicts in various sources and code sections. Build on the existing full
Lean formalization of Fermat's Last Theorem and formalize all essential mathematical statements — both statements we
use (literature) and our own arguments and algorithmic approaches. Plan it for slot 16 next to the postponed WPs; it
will need several dedicated slots. In parallel build a clean mathematical LaTeX document reflecting the Lean
development, referenced by all other documents as theoretical ground truth."* A correction followed the same day: the
base is **Anthropic's complete FLT formalization on mathlib4**, not the Imperial FLT project.

**Cited as.**
- [LP] is this plan.
- [LA] is `docs/implementation/lean_formalization_assessment.md` (2026-09-16, against [C] v1.0.0).
- [C], [E], [U] and [EX] are the binding and example documents named in CLAUDE.md.
- [GT] is the new ground-truth document proposed in §2.4.
- [S15] is `docs/implementation/slot15/00-slot15-plan.md`.
- [EUC] is the owner's own Lean project `~/dev/lean/euclids_elements` (method v1.5.0). The plan reuses its process
  lessons (§1.3, §6).

**Companion file.** `docs/implementation/lean/statement_inventory_v0.tsv` is the first-cut statement inventory. It has
341 rows and was generated mechanically by `$HACS_DATA/lean-plan/inventory.py` (§3.0).

---

## 0. What was verified (2026-09-30), and where

Each claim below is marked **V** (verified: I read the source), **L** (verified locally on this box) or **U**
(unverified; it rests on a search snippet or on a summarising fetch).

### 0.1 Anthropic's FLT formalization, the base the owner names

| Fact | Status | Source |
|---|---|---|
| A complete, machine-checked proof of FLT in Lean 4, announced 2026-09-04. About 13M lines and about 29.5k theorems, written by Claude agents in about 11 days. | V | https://www.anthropic.com/research/formalizing-fermats-last-theorem ; Buzzard, https://xenaproject.wordpress.com/2026/09/04/flt-anthropic-has-beaten-me-to-it/ |
| The repository is `github.com/anthropics/fermats-last-theorem`, licensed **Apache-2.0**. It adapts pieces of Imperial FLT and flt-regular (106 attributed files, with a `NOTICE` and an `ATTRIBUTION.md`). | V | README |
| It uses only `propext`, `Classical.choice` and `Quot.sound`. It has no `sorry`, no added `axiom` and no `native_decide`. `FinalCheck.lean` enforces this, and the proof was re-checked by `comparator` and by the independent kernel `nanoda`. | V | README |
| Toolchain **`leanprover/lean4:v4.33.1`**; **mathlib `v4.33.0`**, pinned at rev `db584cd6d46c92f209a44c0f1c829460d327499d`. | V | raw `lean-toolchain`, `lake-manifest.json` |
| **"Not designed as a Lake dependency"** and **"Not maintained and not accepting contributions."** A build takes about 5.5 h at 96 jobs, about 5 GB RAM per job (peak about 153 GB), about 67 GB under `.lake/`, plus about 220 GB of transient C files. | V | README |
| Layout: `Definitions/` (about 1450 files named `Def_<Area>_<Concept>.lean`), `Theorems/`, `P2M/Sol/`, `FinalCheck.lean`, `PROOF-PATH.md`, and `html/` (about 29.5k theorem pages). | V | README; directory listing (truncated at 1000 entries) |
| Proof route: Frey–Serre–Ribet–Wiles–Taylor–Wiles, following Darmon–Diamond–Taylor. Ribet's step is `FreyPackage.level_lowering_to_two` (via Čerednik–Drinfeld), stated only for the Frey representation at squarefree levels. Mazur's step is `FreyPackage.Mazur_Frey` (`p ≥ 17` via the Eisenstein quotient of `J_0(N)`). Langlands–Tunnell covers only the octahedral case. R = T covers two level-conditioned semistable statements at `p ∈ {3, 5}`. A Deligne–Serre lifting lemma is used. `ModularForm.S2_Gamma0_2_eq_zero` is proved. The weight-2 Hecke/Galois datum is `CuspForm.HeckeGaloisRepDatum`. | V (names read in `PROOF-PATH.md` through a summarising fetch; declarations not read) | `PROOF-PATH.md` |
| `PROOF-PATH.md` states what is **not** formalized: general Ribet, general Mazur isogeny and torsion, general Langlands–Tunnell, modularity lifting without level conditions, modular parametrisations, L-functions. | V | `PROOF-PATH.md` |
| **Eichler–Shimura** (in the cohomological sense of Shimura Ch. 8), **group cohomology of `SL_2(Z)`**, **Serre weights**, **Hida theory**, **Bernoulli / Kummer congruences** and **nebentypus** do **not** appear in `PROOF-PATH.md`. A directory search of `Definitions/` found `Def_AbstractHeckeOperator.lean`, `Def_AlgebraicCurve_FrobeniusEndo*.lean` and `Def_AlgebraicCurve_JacobianH1Autoduality.lean`, and nothing matching ModularSymbol / Eichler / Gamma0 / Bernoulli. | V for `PROOF-PATH.md`; **U** for `Definitions/`, whose listing was truncated | as above |
| **No clone on this box.** `find ~ <private-library> -maxdepth 7` finds no FLT project except `flt-regular`, a stripped copy (no `lean-toolchain`, broken `.git`). `~/.elan/known-projects` lists none. | L | `find`, `~/.elan/known-projects` |

**What this means for us.** Anthropic's FLT is complete and kernel-checked. Its coverage is the weight-2 Γ₀(N) world
of FLT: Jacobians, the Eisenstein quotient, Galois representations of weight-2 eigenforms, R = T at `p = 3, 5`.
Ours is `H^•(SL_2(Z); Sym^n)` at general weight `k = n + 2`, level 1 and level `N`, mod `ℓ^K`, the cone and compact
supports, Dickson/θ, and Hida theory. The overlap is real but narrow:
- Mazur's Eisenstein ideal at prime level, weight 2, which [C] `sec:levelN` (R3) uses;
- the Deligne–Serre lifting lemma ([E] cites `deligne_serre`);
- the weight-2 Γ₀(N) Hecke algebra and its Galois datum;
- Frobenius and Galois-representation infrastructure for [U] and the Galois note;
- an abstract Hecke-operator definition.

It cannot be a Lake dependency: the authors say so, and a build needs about 150 GB RAM and 67 GB of `.lake` against
this box's 62 GB RAM and ≈ 48 GB free on C:. §2.2 therefore plans for **mathlib at FLT's pin plus a harvest**
(vendored, provenance-tracked copies of chosen FLT files), not for a `require`.

### 0.2 Imperial FLT, for comparison

| Fact | Status | Source |
|---|---|---|
| Ongoing, not complete: `FLT/Proof.lean` ends in `theorem B4_proof : B4 := sorry`. EPSRC funding runs to 2029, and Buzzard says the project continues toward the modern proof and mathlib contributions. | V | raw `FLT/Proof.lean`, README, Xena blog |
| Hecke operators on totally definite quaternion algebras: `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/{Abstract,Concrete,Local}.lean`. | V (file names) | GitHub tree |
| Toolchain `v4.35.0-rc3`, mathlib `3cb72cfd…`, Apache-2.0. | V | raw files |

### 0.3 mathlib4

Local checkout `$DATA_ROOT/mathlib4_v4310`: toolchain **v4.31.0**, HEAD `fabf563a` (2026-06-15), built
`.lake` 6.8 GB (**L**). It is two minor versions behind FLT's v4.33.0. `~/.elan/toolchains` holds v4.30.0 and
v4.31.0 only (**L**). Against that checkout (**L**, by `ls` / `grep`):

| Area | Present | Absent |
|---|---|---|
| Group cohomology | `groupCohomology` over `Rep k G`, `groupCohomologyIsoExt` (`Basic.lean:206`), `LowDegree`, `LongExactSequence` (δ), `Shapiro` (`coindIso`), `Functoriality` (`res`), `FiniteCyclic`, `Hilbert90`; `ProjectiveResolution` | corestriction / transfer; a named inflation–restriction sequence; spectral sequences |
| Modular forms | `ModularForm`, `CuspForm`, `SlashActions`, `CongruenceSubgroups` (Γ, Γ₀, Γ₁), `ArithmeticSubgroups`, `Cusps`, `QExpansion`, `EisensteinSeries/*` (with q-expansions and `E2`), `Delta`, `DedekindEta`, `Petersson`, `LevelOne/DimensionFormula`, `LevelOne/GradedRing`; `NumberTheory/Modular` (fundamental domain, stabilisers) | **Hecke operators on modular forms** (grep: none); Eichler–Shimura; modular symbols; mod-ℓ modular forms |
| Numbers | `bernoulli` **and** `bernoulli'` (**two B₁ conventions**, a convention hazard, §3.1), `vonStaudt_clausen`, `lucas_theorem`, `PadicInt`, Dirichlet characters (with Gauss sums and orthogonality) | Kummer congruences; an Iwasawa algebra; the Teichmüller *character* (only Witt-vector Teichmüller) |
| Linear algebra | `SymmetricPower` (`Sym[R] ι M`; the grading and polynomial link are still TODO per [LA] §3.1), Smith normal form over a PID (existential, noncomputable), `Matrix.rank` (noncomputable) | computable RREF / Howell form; Dickson invariants; `ℙ¹(Z/N)` |

[LA]'s record of 2026-09-16 (§6 there) matches this, with one change: `FiniteCyclic` group cohomology now exists.
Online mathlib docs newer than v4.31.0 were **not** re-checked (**U**).

### 0.4 The box

- The Lean toolchain (elan, lake 5.0.0 for Lean 4.31.0) is installed (**L**). `leanblueprint` / `plasTeX` are
  **not** installed (**L**).
- Disk: C: shows **48 GB free** (`df /mnt/c`), against the 15 GB floor. The WSL disk image lives on C:, so `/`'s
  apparent 671 GB free is not usable headroom (CLAUDE.md, the disk-crash lesson).
- 62 GB RAM, 32 hardware threads.
- The owner runs other Lean workloads here: `euclids_elements` and a tokenizer corpus on `/mnt/g`.

---

## 1. Goals and non-goals, and what formalization will and will not guarantee

### 1.1 Goals

1. **A convention layer pinned in Lean** (L0). Every normalisation the project uses is a Lean definition. Each is
   paired with a *bridge lemma* to the literature's normalisation it is compared with.
2. **A literature register** (L1). Every external statement the documents use appears once, in one of three forms:
   - imported from mathlib;
   - harvested from Anthropic FLT (kernel-checked upstream);
   - stated as a named hypothesis with its exact locator and a verbatim quotation of the source.

   No document may state a literature fact differently from the register.
3. **Our own theorems** (L2), in [C] / [E] / [U] order of value (§3.5). Each is stated in Lean first (statements
   before proofs), then proved.
4. **Algorithmic correctness and certificate checking** (L3):
   - a Lean specification of what the C++ computes (RREF / Howell bases, τ / η tables, the `stable` certificate, the
     digit induction's precision lemma);
   - checkers with **proved soundness** that re-check emitted C++ outputs.
5. **[GT], the ground-truth LaTeX document.** It mirrors the Lean development statement for statement (a blueprint).
   Every other document cites it by label for anything formalized.

### 1.2 Non-goals

- Verifying the C++ source code. No C++ semantics is modelled; §1.4 closes the gap by certificates instead.
- Re-proving deep literature that has no local footprint: Eichler–Shimura over ℂ, Hida's control theorem,
  Borel–Serre, Harder's Eisenstein cohomology, Deligne's construction of Galois representations. These stay
  hypotheses (§3.2).
- Upstreaming to mathlib as a goal. It is opportunistic only (Q10).
- Formalizing [EX]. It is non-binding; it cites [GT] and [C] and is not mirrored.
- Formalizing `\CONJ` and `\OPENSTAT` items beyond their **statements**. A conjecture is stated as a Lean `Prop`, so
  that its hypotheses are type-checked, and is never assumed.

### 1.3 What a formalization guarantees, and what it does not

**What it catches.**

- **Statement defects.** A false or mis-hypothesised statement cannot be proved. [LA] §8.1: 15 of [C]'s 23
  superseded-corpus errata would have been caught (E1, E2, E3, E4, E5, E6, E8, E12, E13, E15, E19, E20, E21, E22,
  E23).
- **Hidden hypotheses.** Lean refuses to proceed without them:
  - [LA] F4, the elliptic-point import;
  - slot-15 WP-5 M4, `S` a set of primes, which is not checked;
  - WP-5 H2, `n > 0` even.
- **Internal consistency of conventions.** One definition of `ρ_n`, of `T_p` and of `ι` is used everywhere.

**What it does not catch, and how the plan closes each gap.**

| Gap | Example from this project | Closure in this plan |
|---|---|---|
| **A wrong but consistent convention.** Lean proves whichever convention is defined. | E9 (corestriction convention unmarked); `χ` vs `χ̄` in `sec:nebentypus` ([S15] WP-4 referee §6 Q2: "the first run fixes the sign"); B₁ = ±½ (mathlib has both `bernoulli` and `bernoulli'`); E1 (primitive vs full `T_{p^ν}`) | **Bridge lemmas** (§3.1): each convention is proved equivalent, up to an explicit named transformation, to the literature's. For example: our `⟨d⟩` equals Diamond–Shurman's `⟨d⟩` or its inverse; our `T_p` on `H^1` corresponds under a stated `q`-expansion normalisation. Where the literature side is itself only a hypothesis, the bridge is to the **hypothesis's statement**, and the quotation audit covers it. |
| **The C++ implements a different convention than the Lean one.** | The code's `ρ_n` transposed; `ε_K` computed as `K·dim(A_K/ℓ) − length` while [E] (i) said `K·rank_{Z_ℓ}(B_K) − length` ([S15] WP-5 audit M2) | **Differential oracles** (L3-a): executable Lean definitions of `ρ_n`, the double-coset matrices and small Hecke matrices. Each carries a proof that it meets its specification and is compared entrywise with golden C++ objects at tiny cells. **Certificate checkers** (L3-b): the C++ emits a certificate, and a Lean program with a kernel-checked soundness theorem `check c = true → Spec c` re-checks it. |
| **Pointer errors.** The statement is true but the citation points to the wrong theorem. | `prop:strictpair` cited Serre's "Thm 2" until v0.16.0; Serre's Théorème 1 locator in `cl:mkfaithful` is still **VERIFY** ([S15] WP-4 §7.1) | Every L1 hypothesis carries a **verbatim quotation** and a locator (page and theorem number), checked against the scanned source by a second agent. Where FLT or mathlib proves the statement, the pointer becomes the Lean name, and the problem disappears. |
| **Axioms masking errors.** A false axiom proves anything. | [EUC] Book I: `False` was derivable in eight lines behind a green build, and every headline theorem was vacuous. | **No global `axiom`s** (§2.6). Literature statements are *hypothesis structures* passed as arguments, so a false one cannot contaminate an unrelated theorem. Each is **inhabited or sanity-instantiated in the same commit** where possible ([EUC] invariant 5). `#print axioms` is censused per theorem. |
| **The model is the wrong model.** | That the 7-vertex complex *is* `SL_2(Z)\ℍ` (H4, [LA] §5.4) | Milestone M2 defines `X_bulk` combinatorially and proves the H4 consequences. Until then, theorems are stated over an abstract Γ-complex with H4 as a named hypothesis, and [GT] says so. |
| **Computations** (`\COMP`). | 21 `\COMP` items in [C] | These are not proofs. Under L3-b a `\COMP^r` item can be upgraded to "checked certificate" when its data is small enough, never to `\PROVED`. |

---

## 2. Architecture

### 2.1 The Lake project: location (owner question Q2)

**Recommendation: in this repository**, as the subdirectory `lean/` (library `GL2`), not a separate repository.
Reasons:

1. **Atomic changes.** A convention fix touches [C], [GT], the Lean statement and sometimes the C++ comment. One
   commit and one label census cover all four.
2. **One citation census.** `label_census.py` already resolves `[C, <label>]` across 1006 files. Extending it to
   `[GT, label]`, and to "the `\lean{}` name of a `[GT]` label exists", is one script, not a cross-repo protocol.
3. **The slot process.** The Registry and cmake fragments, the close windows and the worktrees already live here.

**The disk cost of worktrees is the objection, and it is avoidable.** An in-repo Lake project checked out in every
agent worktree would otherwise put a mathlib build (≈ 5–7 GB) in each worktree's `.lake/packages`. The plan
therefore puts **one** shared, read-only dependency tree at `$HACS_DATA/lean-deps/` and points
every worktree's packages at it. The mechanism is Lake's `packagesDir` setting, or a symlinked `.lake/packages`; it is
**[believed]** workable and is verified in WP L16-0. Only the project's own `.lake/build` stays per worktree
(expected < 1 GB at M1).

The alternative, a separate repository `orbifold-cohomology-of-gl2-lean`, keeps C++ agents' checkouts free of
Lean. Its costs are a cross-repo pin, since [GT] must cite a Lean commit, and a second label-census protocol.

### 2.2 The dependency: mathlib at FLT's pin, and FLT by harvest (Q1, Q3, Q12)

- **mathlib pinned to `v4.33.0` (`db584cd6…`) with Lean `v4.33.1`**, exactly FLT's pin. Harvested FLT files then
  compile unchanged, and "imported from FLT" means the same statement over the same library.
- **No `require` of the FLT repository.** It is not designed as a dependency and does not fit this box (§0.1).
- **The harvest.** For each L1 statement the survey (WP L16-1) finds in FLT:
  - **(H) harvest.** Copy the file and its dependency closure into `lean/Vendor/AnthropicFLT/`, byte-identical.
    Add a provenance manifest (`Vendor/AnthropicFLT/MANIFEST.tsv`: upstream commit, path, sha256, our consumer
    labels) and carry `NOTICE` / `ATTRIBUTION` as Apache-2.0 requires. This is only possible when the closure is
    small (for example `S2_Gamma0_2_eq_zero`, or an abstract Hecke-operator file).
  - **(A) FLT-attested.** The closure is too large to build here (anything through `J_0(N)` or Néron models). We
    state the result ourselves as a hypothesis whose statement is the FLT theorem's, restated over our definitions.
    The census class is `flt_attested`, and it records the FLT declaration name. Optionally (Q7) a cluster job builds
    FLT once and runs FLT's own `comparator` to certify that our restatement matches the upstream type. Until then,
    the class counts as a literature hypothesis with a kernel-checked upstream proof.
- **The local v4.31.0 checkout** (`$DATA_ROOT/mathlib4_v4310`, built) can serve as a *path* dependency for the L16-0 spike
  at zero download. It is the default if Q3 (the download) is not approved; harvested files would then need a
  two-version port.
- **Following upstream (Q12).** FLT is unmaintained, so its pin never moves. Recommendation: **freeze at v4.33.0
  until the harvest is complete** (target: slot 18). After that, bump in a dedicated WP at most once per two slots,
  re-porting `Vendor/` (the harvest manifest makes the port set explicit). Reason to bump at all: mathlib may gain
  Hecke operators on modular forms (TauCeti PRs #9800 / #6374 exist downstream, **U**) and Kummer congruences.

### 2.3 Layout

```
lean/
  lean-toolchain                 leanprover/lean4:v4.33.1
  lakefile.toml                  require mathlib @ db584cd; packagesDir → shared lean-deps (L16-0 verifies)
  GL2.lean                       root import
  GL2/Conventions/               L0: SymPow (ρ_n, u_j = x^{n−j} y^j, column convention), Semigroup Δ,
                                 Contragredient, DetTwist, HeckeNormalisation (T_p, T_{p^ν} full vs primitive,
                                 T(p,p), U_ℓ), Involution (ι^* := −ι^*_geo), Dickson (L, D, θ), Teichmuller,
                                 Nebentypus (χ(a_γ), ⟨d⟩), Bernoulli (the B₁ choice), Cone (sign), Bridges/
  GL2/Literature/                L1: one file per source cluster; hypothesis structures with a quotation docstring
  GL2/Framework/  GL2/Model/  GL2/Hecke/  GL2/Cone/  GL2/Level/  GL2/Dickson/  GL2/Ring/  GL2/Hida/   L2
  GL2/Algorithms/                L3-a specs + executable oracles; L3-b checkers with soundness theorems
  GL2/Census.lean                prints #print-axioms classes for every [GT]-linked declaration
  Vendor/AnthropicFLT/           harvested files, MANIFEST.tsv, NOTICE, ATTRIBUTION
  blueprint/                     [GT] source (leanblueprint / plasTeX); web + PDF builds are git-ignored
  tools/lean_census.sh           the gate (§2.5)
```

### 2.4 [GT], the ground-truth document (Q4, Q5, Q9)

**Name.** `lean/blueprint/src/gl2_groundtruth.tex` (PDF title: *The Mathematics of Orbifold Cohomology of GL(2):
Formal Ground Truth*). **Citation key `[GT]`.** `[G]` is already in use in the tree (33 occurrences); `[GT]` has none.
It is built with **leanblueprint** (plasTeX), in the usual Lean-community style: every statement carries
`\lean{GL2.Decl}`, `\leanok` when the Lean statement exists and compiles, `\uses{…}` for the dependency graph, and a
proof marked `\leanok` when proved. The standard `checkdecls` step verifies that every `\lean{}` name exists.

**Label scheme.**
- A statement mirrored from [C] / [E] / [U] keeps **the same label, verbatim** (`thm:welldef`, `prop:symconv`,
  `cor:stablecert`, …). `[C, <label>]` and `[GT, <label>]` then name the same mathematical statement, and a code comment can move
  from `[C, <label>]` to `[GT, <label>]` by editing one token. This is [C]'s own no-prefix decision (`00-unified-contract-architecture.md`
  §1.3).
- New kinds: `conv:` (a pinned convention), `bridge:` (a convention-to-literature lemma), `lit:` (a literature
  hypothesis, e.g. `lit:shimura-3.24`), `inf:` (Lean infrastructure with no [C] counterpart), `chk:` (a certificate
  checker and its soundness theorem).
- The label census gains three checks:
  1. every `[GT, label]` resolves in [GT];
  2. every `[GT]` statement with `\lean{}` names an existing declaration;
  3. a label present in both [C] and [GT] must carry a `% mirrors [C] vX.Y` line, so drift between the two texts is
     visible.

**Precedence (Q5).**
- [C], [E] and [U] stay binding.
- **For a statement proved in Lean, [GT] is authoritative.** If [C]'s text of that statement differs in substance,
  [C] is in error; it gets an erratum and a pointer to [GT].
- A statement that is only *stated* in Lean (`sorry`) gives [GT] no authority over [C]. The statement is still
  type-checked, and that alone has caught defects ([EUC] invariant 2).
- **Supersession** is a later owner decision, proposed for review at milestone M4 (§4.2). From there [C]'s
  mathematical chapters could shrink to "see [GT]" plus the implementation notes (Part V, `sec:implementation`). Until
  then, nothing is deleted.

**Status vocabulary.** Per statement, `lean_status` ∈ {`planned`, `stated` (compiles with `sorry`), `proved`,
`proved_mod_lit` (proved from named L1 hypotheses only), `lit_mathlib`, `lit_flt_harvest`, `lit_flt_attested`,
`lit_hyp` (a quoted literature hypothesis), `conj_stated`, `checker_sound`}. Q9 proposes one new [C] tag,
`\LEAN{label}`: "formally verified; see [GT]". It is added beside `\PROVED` once a statement reaches `proved` or
`proved_mod_lit`, the second printing the hypotheses it rests on.

### 2.5 CI and the census

`lean/tools/lean_census.sh` runs `lake build`, then `lake exe gl2census` (from `GL2/Census.lean`), then
`leanblueprint checkdecls`. It prints one line, and the slot-11 lesson applies: **read the text, not the exit code**.

```
LEAN_CENSUS decls=<n> gt_labels=<n> stated=<n> proved=<n> proved_mod_lit=<n> sorry=<n> lit_hyp=<n>
            flt_harvest=<n> flt_attested=<n> native=<n> global_axioms=0 unresolved=0 stale=0 verdict=OK|FAIL
```

`FAIL` fires on:
- any `axiom` outside the empty-by-policy `GL2/Literature/Quarantine.lean`;
- any `sorry` in a declaration tagged `proved`;
- `native_decide` (`Lean.ofReduceBool`) outside `GL2/Algorithms/`;
- a stale `\lean{}` name.

The census also writes `lean/census.tsv`, one row per [GT] label, the analogue of `docs/latex/label_census.tsv`.

- **The C++ harness is not made to depend on Lean.** `--all` must stay Lean-free. An optional `fast` validation,
  `LeanCensusFileValidation`, only checks the committed `census.tsv` against [GT]'s label set, as
  `ContractCensusValidation` does for [C].
- **Mutation-testing the instrument** ([EUC] invariant 3): the census ships with negative controls (a planted
  `sorry`, a planted `axiom`, a stale `\lean{}`), each expected to print `verdict=FAIL`.
- **As implemented (slot 16, after the L16-5 audit repairs; a record, not a plan change).** The tool is
  `lean/tools/lean_census.py` (no `lake exe`); its line is
  `LEAN_CENSUS decls= proved= proved_mod_lit= stated= planned= sorries= global_axioms= unresolved= stale= lit_hyp=
  native= gl2_consts= escapes= modlit_bad= verdict=`. `lit_hyp` rows (the `hypothesis` environments of [GT] Part L) are
  no longer `stated`, so `sorries ≤ stated` has no slack; `sorries` counts `sorry`, `admit`, `stop`; the per-constant
  scan `lean/tools/CensusScan.lean` computes the axioms of **every** constant defined in a `GL2` module and fails
  (`escapes`) on an undeclared `sorryAx` and on a native axiom outside `GL2.Algorithms.*` (on Lean v4.33 `native_decide` declares an auxiliary axiom `<decl>._native.native_decide.ax_…`, which the census treats as native); `\gtmodlit` rows declare
  their hypotheses by `\gtlithyp{…}` and `census.tsv` records them (column `lit_hyps`). `gt_labels`, `flt_harvest`,
  `flt_attested` are not implemented yet (no FLT rows exist). **`leanblueprint checkdecls` is not run:
  `unresolved=0` replaces it** (every `\lean{}` name is resolved by `#print axioms`). The selftest has seven controls
  (the three above plus an unlinked `admit`, an unlinked `native_decide`, and a `(h : False)` theorem tagged
  `\gtmodlit` without and with `\gtlithyp{h}`).
- **As implemented (slot 17, L17-4 repair; a record, not a plan change; lead ruling 2026-10-02).** L17-4 first exempted
  native axioms on linked rows in both gates; the audit (`docs/implementation/slot17/L17-4_audit.md`, BLOCKING-1) showed
  the exemption unscoped, and it was **reverted to the slot-16 behaviour**: a native axiom on any **linked** row (`chk:`,
  `thm:`, a `hypothesis` row, …) counts in `global_axioms` (live gate) and in `nonstd_axioms` (committed gate,
  `lean_census_committed.py`), so `proved=` means kernel-checked. An **unlinked** native constant stays legal inside
  `GL2.Algorithms.*` only (the bullet above; whether it should be is an open owner/plan point). The tree holds **no**
  `native_decide` (`native=0`): every checker runs by `decide +kernel`. The live selftest has **eleven** controls (the
  seven above plus `linked_native_thm`, `linked_native_chk`, `native_on_lithyp`, `linked_native_outside`, each re-emitted
  and run through both gates); the committed gate has its own lake-free `--selftest` (four controls: a native axiom on a
  `chk:` proved, a `thm:` proved, a `lit_hyp` and a `proved_mod_lit` row). A future native checker needs a scoped marker
  first (the audit's `\gtnative` / `proved_native` design), not an exemption.

### 2.6 The axiom and hypothesis policy (Q6)

1. **No `axiom` declarations.** A literature statement is a `structure` / `class` (for example
   `Lit.EichlerShimuraLevelOne (ℓ n : ℕ) : Prop`) and a hypothesis argument of every theorem that uses it.
   `#print axioms` then shows only the three standard axioms, and the literature dependence is visible **in the
   theorem's type**.
2. **Every hypothesis structure carries:**
   - a docstring with the verbatim quotation and locator;
   - the scan path (`<private-library>`, read-only);
   - the date and the verifying agent;
   - the census class.
3. **Sanity instantiation.** Where the hypothesis has a decidable finite instance, it is instantiated at that
   instance in the same commit. For example, the Sturm bound at weight 12 via the level-one dimension formula
   mathlib has, or Dickson's `F_5[x,y]^{SL_2(F_5)}` in low degree by `decide`. That catches a transcription that is
   false on its face.
4. **`native_decide`** is permitted **only** in `GL2/Algorithms/` (certificate runs on large tables). It is censused
   as `native`, and the trusted base (the Lean compiler) is stated in [GT]. Every *soundness* theorem is
   kernel-checked with no `native_decide`.

### 2.7 Disk, CPU and cluster

| Item | Estimate | Basis |
|---|---|---|
| mathlib v4.33.0 source + `lake exe cache get` oleans | ≈ 6–7 GB, **once**, shared | the local v4.31.0 build is 6.8 GB (**L**) |
| Our own `.lake/build` | < 0.5 GB at M1, < 2 GB at M4 | [EUC]'s `.lake` is 7 MB with zero dependencies; ours imports mathlib, but builds only its own oleans |
| plasTeX / leanblueprint in a venv under `$DATA_ROOT` | < 0.3 GB | |
| Build RAM | ≈ 2–5 GB per `lake` job; cap `-j 8` (≤ 40 GB) and never alongside a ≥ 20 GB C++ run | FLT README (≈ 5 GB/job on much larger files) |
| Incremental build per WP | minutes | |

**The disk budget** is one shared copy against C:'s ≈ 48 GB free and the 15 GB floor. The rules:
- `disk_guard.sh` runs before every `lake` step;
- **no per-worktree mathlib**;
- a Lean WP's worktree holds only `.lake/build`, and the agent deletes it at hand-off, as the one-build rule already
  requires.

**The cluster** is not needed for routine work. It helps in exactly one place: **Q7, an optional one-time FLT build
plus `comparator`** on an cluster-B / cluster-A CPU node, to promote `flt_attested` restatements to machine-matched ones.
FLT quotes ≈ 5.5 h × 96 jobs ≈ 530 core-h and ≈ 150 GB RAM. On cluster-B express's 1000 billing-h/month that is half a
month's quota, so it is recommended only after the survey shows which statements it would attest. The owner submits;
agents write the kit (rule 23).

---

## 3. The statement inventory: first cut

### 3.0 Size, from the mechanical extraction

`statement_inventory_v0.tsv` has one row per labelled theorem-like environment of [C], its notation chapter, [E] and
[U]:
- appendices are excluded;
- untagged remarks are excluded;
- columns: `doc`, `label`, `kind`, `section`, `tags`, `cites`, `layer`, `lean_status_planned`.

Its layer is a first-cut guess from the section and the tags, to be adjudicated in WP L16-3 ([EUC] invariant 1:
census before statements).

| | [C] | [E] | [U] | Total |
|---|---|---|---|---|
| Rows | 263 | 42 | 36 | **341** |
| L0 (conventions sections) | 21 | — (see §3.1: [E] `sec:conv`'s items are cited, not restated) | — | 21 + ≈ 20 new `conv:` / `bridge:` |
| L1 (a `\STD` tag and no `\PROVED`) | 12 | 8 | 2 | 22 statements; **85 statements carry at least one `\STD`**, citing ≈ 50 works |
| L2 | 195 | 17 | 34 | 246 |
| L3 (algorithms, obligations, certificates, Part V) | 35 | 17 | — | 52 |
| Planned status: `define` / `prove` / `import-or-axiomatise` / `certificate-check` / `state-only` / `triage` | 50 / 164 / 11 / 10 / 5 / 23 | 2 / 24 / 5 / 0 / 7 / 4 | 5 / 23 / 2 / 2 / 3 / 1 | 57 / 211 / 18 / 12 / 15 / 28 |

[C] alone has 610 labels, 136 `\STD` occurrences, 504 `\PROVED`, 83 `\CONJ`, 223 `\COMP` and 49 `\OPENSTAT`
occurrences (raw `grep`), and **79 distinct `\STD` citation pointers**. [LA] counted 33 `\STD` at v1.0.0; the
document has grown about 2.4× since, through Parts VI–VII, `sec:levelN`, `sec:nebentypus` and `sec:saturation`.

**Most-cited works** among the 85 `\STD`-carrying statements: brown 28, shimura 22, weibel 13, ash_stevens 10,
serre_cours 8, cremona 6, hida_invent 5, hida_ens 5, deng 5, washington 4, hatcher 4, harder3 4, swinnerton_dyer 3,
then ≈ 35 works cited once or twice. Among those: mazur, merel, merel96, ribet77, ribet_nebentypus, jochnowitz, sturm,
serre_bourbaki416, deligne_formes, wiles_ordinary, emerton_eis, gross, edixhoven, glover, dickson1911, wilkerson,
lucas1878, katz1977, bk, deo, borel_serre and harder_eisenstein.

### 3.1 L0: conventions and normalisations

Each convention is a Lean definition in `GL2/Conventions/` plus a `[GT] conv:` statement. Where the literature is
involved there is also a `bridge:` lemma. The **why** column is the error history that makes it worth pinning.

| # | Convention | Where fixed today | Why pin it (history) | Bridge to |
|---|---|---|---|---|
| C1 | `Sym^n` basis `u_j = x^{n−j} y^j`, `ρ_n` by the closed form (`eq:rhondef`), the **column convention**, extension to the monoid Δ | [C] `def:rhon`, `prop:symconv` | E19 (β not a morphism); the most cited definition in the C++ | mathlib `SymmetricPower` / `MvPolynomial.homogeneousComponent`; Shimura's `ρ_n` |
| C2 | Contragredient `ρ_n^∨ = ρ_n(adj ·)^T`, the pairing, the det-twist | `def:contragredient`, `prop:pairing`, `lem:symdual`, `lem:detsym` | slot-14 legacy-arm regression (`c0566e2`: the contragredient read the SymN τ pool) | the dual representation in mathlib `Rep` |
| C3 | `T_p` as the double coset `Γ diag(1,p) Γ`; `T_{p^ν}` **full** vs primitive; `T(p,p) = p^n`; `U_ℓ` | `def:hecke`, `thm:relations`, `cor:ulrecursion` | **E1** (primitive vs full, off by `p^n I`), **E6** (coefficient `p` vs `p+1`), memory note `hecke-Tpr-primitive-vs-full` | Shimura 3.24's `T(1,p^ν)`; the `q`-expansion action on `M_k` ([E] `cl:mkfaithful`) |
| C4 | Left vs right cosets on the boundary; the corestriction convention | `prop:bdrychar`(2), `sec:boundarydatum` | **E9**, **E14** | Brown III.9 `cor` |
| C5 | `ι^* := −ι^*_geo`; "+" is the Eisenstein side **by definition** | `def:iota`(iv), `rmk:iotasign` | the OQ3 claim was **false** (the memory note `three-open-items`) | Eichler–Shimura's complex-conjugation convention |
| C6 | The mapping-cone sign | `sec:cone` | **E13** | mathlib `CochainComplex.mappingCone` ([LA] §4.3: re-derive) |
| C7 | Dickson `L = x^ℓ y − x y^ℓ`, `D`, θ and the short exact sequence `0 → Sym^n ⊗ det → Sym^{n+ℓ+1} → Q_n → 0` | `sec:dicksontheta`, `def:Qn` | **E21** ("χ₁ ≡ χ₂ at every Dickson locus" refuted at `(12, 5)`) | Dickson 1911 / Wilkerson |
| C8 | The Teichmüller character `ω`, `χ` valued in `F_q^×`, `V(χ)` via `χ(a_γ)`, `⟨d⟩ = χ(d)` | `sec:nebentypus` (`lem:teichmuller`, `def:nebdata`) | [S15] WP-4 Q2: **the `S_k(N,χ)` vs `S_k(N,χ̄)` dictionary is unasserted**; the first run fixes the sign | Diamond–Shurman / Shimura `⟨d⟩`; mathlib `DirichletCharacter` |
| C9 | Bernoulli: `B_k` with `B_1 = ∓½`; `B_k/k mod ℓ^K`; Kummer | [E] `bernoulli_mod`, WP-14c | mathlib carries **both** `bernoulli` and `bernoulli'`; the shipped `bernoulli_mod` works mod `ℓ` only | mathlib `bernoulli`, Washington |
| C10 | Weight `k = n + 2`; the cohomological degree; `H^1_! = ker r^1` | [C] Part IV, [E] `sec:coh` | the census `eisenstein` / `cuspidal` / `mixed` split relies on it | Eichler–Shimura |
| C11 | The `Z/ℓ^K` algebra readings: `ε_K`, `A_K`, the Hilbert function, `⌈f/2⌉` | [E] `sec:ring` (i)–(ii), [C] `sec:saturation` | **[S15] WP-5 M2**: [E] (i)'s `ε_K := K·rank_{Z_ℓ}(B_K) − length` contradicted (ii)(6) and the code; M3: "Hilbert function certified" overstated | none (our own; fix it as one definition) |
| C12 | The ordinary projector `e = lim U^{N!}`, `N_ord`, the precision `K = e' + e_max` | `def:ordinary`, `prop:torsionprepass` | slot-12 open `ordprecision` | Hida's `e` |
| C13 | Level `N` by Shapiro: `def:cosetrepsN`, the transversal, induced relations, `Γ_0(N)` vs `Γ^0(N)` | `sec:levelN` | this is where the Moerdijk–Pronk and general-`N` work will land | mathlib `Gamma0`, `Rep.coind` |

Size: ≈ 40 statements, 2.5–4k lines of Lean. C1–C3 overlap [LA]'s T2a.

### 3.2 L1: the literature register

The ≈ 50 cited works, grouped into source clusters. Disposition key:
- **M**: import from mathlib;
- **F-H**: harvest from Anthropic FLT;
- **F-A**: FLT-attested;
- **P**: prove in-house (bounded cost);
- **H**: a quoted hypothesis;
- **S**: statement only (`\CONJ`, or cited as context).

| Cluster | Works | Used by (examples) | Disposition | Risk if axiomatised | Count |
|---|---|---|---|---|---|
| Homological algebra | brown III.1 / III.6 / I.7.4, weibel 1.3.1 / 2.2.6 / §1.5 / §3.6 | `lem:tauexists`, `lem:conerelative`, `cl:bockstein`, Shapiro | **M** after [LA] §5.1's projectivity reduction at `6 ∈ R^×` | — | ≈ 12 |
| Finite-group cohomology facts | brown III.10.2 (`\|G\|` kills `H^{≥1}`), brown VII.6 (LHS for a product), brown V.3 | `cl:amalgam`(3)(4), `prop:bdrycohom`, `lem:h2torsion` | **P**: the cyclic cases, via mathlib `FiniteCyclic` | — | ≈ 6 |
| Restriction, corestriction, transfer | brown III.9–10, ash_stevens §§1–3 | `thm:classical`, `obl:algebra`, `prop:barformula` | **P**, 3–6 PM ([LA] §5.2); not in mathlib, not in FLT | low as a statement | ≈ 8 |
| The Hecke ring | shimura Ch. 3 (§3.1, Thm 3.24, 3.29, 3.34–3.35) | `def:operators`, `thm:relations`, `prop:cosets`(1) | **P** preferred (6–18 PM, [LA] §5.3), else **H** with the `p^n I` difference as a *theorem* (not assumed); watch FLT `Def_AbstractHeckeOperator` and Imperial `HeckeOperators/Abstract` (**F-H** candidate for the abstract ring) | **medium**: exactly the E1 / E6 class | ≈ 8 |
| `SL_2(Z)` geometry | serre_cours VII §1.2 Thm 1–2, VII §3 (`d_k`), VII §5; serre_trees I §4; hatcher | `lem:model7coincidences`, `prop:strictpair`, `cl:amalgam` | fundamental domain and stabilisers: **M**; `d_k`: **M** (mathlib `LevelOne/DimensionFormula`, **V** present); amalgam: **P** via `(eq:treeses)` as definition; hatcher: avoided | medium (`d_k` transcription) | ≈ 10 |
| Eichler–Shimura (cohomological) | shimura Ch. 8, Thm 8.4; cremona Ch. 2; manin; deng; harder3 | `cl:dimH1`, `obl:oracle`, `obl:iota`, `thm:classical` | **H**. Not in mathlib; **not in FLT** (`PROOF-PATH.md`: absent). Manin's trick: **P**. deng / harder3: **H** with an explicit "no locator" flag | **high**: it fixes every oracle's normalisation | ≈ 8 |
| Mod-`ℓ` modular forms | serre (Bourbaki 416 Thm 1), serre_bourbaki416, jochnowitz, jochnowitz_local, sturm, swinnerton_dyer, katz1977, edixhoven, gross, coleman_voloch | [E] `cl:mkfaithful`, `cl:sturmmodl`, `cl:bprime`, Stage 3 finality | sturm: **P** on mathlib's `q`-expansions (medium); swinnerton_dyer's congruences: **P** (identities in `M_k`); serre / jochnowitz / katz / gross / edixhoven: **H** | medium (the Serre locator is still VERIFY) | ≈ 12 |
| Eisenstein ideal, level `N` | mazur, merel, merel96, wwe, ribet77, ribet, cohen_oesterle, atkin_lehner | [C] `sec:levelN` (R3), `sec:nebentypus` (NB1–NB6), [U] `sec:u-eis` | mazur's Eisenstein ideal at prime `N`, weight 2: **F-A / F-H candidate** (FLT's Eisenstein quotient of `J_0(N)`, **U** until the survey); deligne_serre lifting: **F-H candidate**; merel / wwe / ribet_nebentypus / cohen_oesterle: **H** | medium | ≈ 10 |
| Hida theory | hida_invent (Thm 3.1, Prop 4.7, Thm 6.6), hida_ens (Thm 3.1), hida_book, hida_aif2, wiles_ordinary, mazur_wiles, ohta_cong, emerton_eis, mazur_tilouine | [C] `sec:hida`, `sec:hidafull` (Hi7–Hi12), all of [U] | **H**. The control theorem is research-scale; our finite-level consequences are **P** from it (`proved_mod_lit`) | **high**: [C] v1.13 marks control "verified literature"; exact normalisations matter | ≈ 12 |
| Dickson invariants | dickson1911, wilkerson | `sec:dicksontheta`, `cl:dimH1`(2), `prop:heckeH0` | **P**: pure commutative algebra, `F_ℓ[x,y]^{SL_2(F_ℓ)} = F_ℓ[L, D]` (medium, ≈ 1–2 PM) | — | 3 |
| Bernoulli, Kummer, Herbrand–Ribet | washington (Kummer congruences; Herbrand–Ribet), washington1st, glover, lucas1878 | [E] `HeckePredictions`, `GloverFactors`, WP-14c | lucas: **M**; Kummer congruences: **P** (not in mathlib; medium); Herbrand–Ribet: **H** | low / medium | ≈ 6 |
| Galois side | deligne_formes, deligne_serre, bk (Bellaïche–Khare), deo, ribet_nebentypus, wiles_flt, and the Galois note's ≈ 25 works | [U] `sec:u-cm`, [E] `pr:*`, the Galois note | **S / H**; FLT's Galois-representation and Frobenius infrastructure is **F-H** for *definitions*; bk is a **GAP (VERIFY)** ([S15] WP-12) | high where used as mechanism | ≈ 10 |
| Out of scope | borel_serre, harder_eisenstein, harder_pink | `thm:conewelldef`(c′), `rmk:conesteinberg`(iii) | **S**: [C] already downgrades these to `\CONJ` | — | 3 |

**Re-estimate of the axiom (hypothesis) count.**
- [LA] found 20 of 33 `\STD` pointers needing axioms at v1.0.0.
- On today's ≈ 80 pointers and ≈ 50 works, the first cut gives about:
  - 25–30 % **M** (homological algebra, Shapiro, LES, the fundamental domain, level-one `d_k`, Dirichlet, Lucas,
    von Staudt);
  - 25–30 % **P** (cyclic cohomology, transfer, the Hecke ring, Dickson, Kummer, Sturm, Manin, amalgam);
  - **≤ 10 % from FLT**: Mazur's Eisenstein-ideal ingredients, Deligne–Serre lifting, the weight-2 Γ₀(N) Hecke
    datum, `S_2(Γ_0(2)) = 0`, and Galois / Frobenius definitions, all **U** until WP L16-1 reads the declarations;
  - **≈ 35 % H**.
- That is **≈ 25 hypothesis structures** (± 5), concentrated in Eichler–Shimura, Hida, mod-`ℓ` forms (Serre /
  Jochnowitz / Katz) and the Eisenstein ideal at level `N`.
- **FLT reduces the count by about 3–6, not dramatically**: its world is weight 2, geometric (Jacobians) and aimed
  at FLT, while ours is weight `n + 2`, cohomological, and mod `ℓ^K`.

**Revised by L16-1 (2026-10-01, `docs/implementation/slot16/L16-1_report.md` §5; survey
`lean/survey/flt_harvest_survey.tsv`).** The count above underestimated FLT. FLT *does* contain cohomological Eichler–Shimura
(`Sym^n`, `Γ0(N)`, Hecke-equivariant) and Ash–Stevens weight reduction mod p. It also contains corestriction and transfer, and
weight-2 nebentypus with diamonds. After L16-1:
- ≈ 20 `lit_hyp` plus ≈ 5 `lit_flt_attested` hypotheses;
- ≈ 4–5 statements harvested (`lit_flt_harvest`);
- FLT's share ≈ 25–30 % of the L1 needs;
- the transfer cluster moves from P to F-H.

The §0.1 sentence "Eichler–Shimura … do not appear" is right about `PROOF-PATH.md` only.

The larger value of FLT to this programme is indirect:
- it proves that an agent-driven formalization at this depth is achievable, which revises [LA]'s person-month
  estimates;
- it supplies patterns (the abstract Hecke operator, Galois representations, Frobenius);
- its per-theorem HTML pages are a searchable index of what exists.

### 3.3 L2: our own theorems

Grouped by [C] Part and companion; ≈ 246 statements. Effort is in [LA]'s person-months (PM) where [LA] estimated.
§4.3 converts to slots.

| Group | Scope (labels) | Rows | Prerequisites | [LA] estimate | Value note |
|---|---|---|---|---|---|
| G1 Coefficient and coset algebra (T2a) | `prop:symconv`, `lem:detsym`, `prop:pairing`, `prop:cosets`, `lem:cocycle`, `prop:tworoutes`, `prop:mu`, `lem:bounds`, `prop:bdrycosets`, `prop:bdrychar`(1)(2) | ≈ 30 | L0 C1–C4 | 3–6 PM | the two bit-identities; the exact FP bounds (E22) |
| G2 Framework, model and operator (T0 + T2b) | `def:relationdatum` … `thm:explicit_complex_equiv`(1) (Ψ), `def:tau`, `thm:welldef`, `thm:xi`, `prop:diamond`, `lem:tauexists`(1), `prop:iotacommutes` | ≈ 60 | G1, the combinatorial `X_bulk` ([LA] F1) | 8–16 PM (T0 + T2b) | Ψ is cited by six C++ files |
| G3 The cone and compact supports (T3) | `sec:cone`, `sec:six`: `lem:conerelative` … `cl:les`, `prop:coneintegral` | ≈ 33 | G2's equivariance only | 3–6 PM | [LA]'s top pick: no independent check exists anywhere |
| G4 Projective reduction and comparison (T4 §5.1) | `lem:tauexists`(2), `thm:cohom_equiv`(1), `rmk:orbifold`, `thm:specialisation` | ≈ 8 | G2, mathlib `ProjectiveResolution`, `groupCohomologyIsoExt` | 3–6 PM | turns "`6 ∈ R^×` via the fundamental lemma" into mathlib theorems |
| G5 The Hecke ring and relations | `thm:relations`, `obl:algebra`, `thm:classical` | ≈ 8 | L1 Hecke-ring cluster, transfer | 6–18 PM (or **H**) | the E1 / E6 class |
| G6 Integral line (Part VI) | `sec:integral` (21 rows): isotropy model, `prop:strictlift`, `lem:bulkperiodic`, `prop:certifiede` | ≈ 21 | G2, G4 | not estimated in [LA] (post-v1.0.0); ≈ 4–8 PM | Moerdijk–Pronk readiness |
| G7 Dickson, θ, ordinary (Part VII, first half) | `sec:dicksontheta`, `sec:ordinary`, `prop:heckeH0`, `thm:thetales` | ≈ 18 | L1 Dickson (**P**), G2 | ≈ 3–5 PM | E21 lived here |
| G8 Hida at level one and level `ℓ` | `sec:hida`, `sec:hidafull` (Hi7–Hi12), [U] | ≈ 20 + 34 | L1 Hida (**H**), G7 | ≈ 4–8 PM, `proved_mod_lit` | [U] is binding since v0.1.0; high literature risk |
| G9 Level `N`, nebentypus | `sec:levelN` (LN1–LN6, `prop:levelorbit`, `prop:heilbronn`), `sec:nebentypus` (NB1–NB6, `prop:nebcorr`, `prop:neborbit`) | ≈ 24 | G2, mathlib Shapiro | ≈ 3–6 PM | slot-16 code (WP-10) and the general-`N` work land here |
| G10 Saturation and the `Z/ℓ^K` algebra | `sec:saturation` (P15 `prop:saturation`, P17 `prop:satdefect`, `lem:heckerankone`, `lem:freepart`, `cor:stablecert`, `prop:cohforms`, P18, P20); [E] `sec:ring` | ≈ 9 + 6 | commutative algebra (mathlib-rich) | ≈ 2–4 PM | **the most Lean-friendly high-value group**: pure finite commutative algebra, just refereed with repairs (WP-4 B1; WP-5 M1–M4) |
| G11 [E] finality and extension classes | `sec:ext`, `sec:hecke`, `sec:primary`, `cl:mkfaithful`, `cl:formsF9`, `cert:dickson`, `cert:boundary`, `pr:latticesplit` (refuted, stated as a negated `Prop` with its counterexample) | ≈ 25 | G7, G10, L1 mod-`ℓ` forms | ≈ 3–6 PM | the finality certificates reach published records |

### 3.4 L3: algorithmic correctness and certificate checkers

**L3-a: specifications and executable oracles.** Each is an executable Lean definition with a proof that it meets its
specification:
- `ρ_n(g)` over `ZMod m`;
- the double-coset representatives and `prop:cosets`;
- `P¹(Z/N)` and `def:cosetrepsN`;
- the Heilbronn–Merel set `H_{N,p}`;
- tiny `H^1(SL_2(Z); Sym^n F_ℓ)` via the amalgam presentation (`n ≤ 12`, `ℓ ≤ 13`), and `T_p` on it.

They are compared entrywise with the C++ golden objects at 3–5 cells (the **differential oracle**). This is what
catches C1 / C8-type mismatches between code and definition.

**L3-b: checkers with kernel-checked soundness.** In order of value:
1. **`obl:tau` / `obl:taubdry` / `obl:eta`**, the chain-level predicates ([LA] T1). The `p = 2` table
   (`ex:t2tau`, 69 chains) is feasible by `decide`; the 10 764-slot grids need compiled checking.
2. **The `stable` certificate** of `cor:stablecert` (B1 form): the algebraic identities `e² = e`, `eT = Te`, the
   Smith / torsion multiset, and `dim A'_K/ℓ = ⌈f/2⌉` on emitted matrices over `ZMod ℓ^K`. This is fresh from WP-5,
   with hypothesis H3 (`S` primes) unchecked in C++ (M4).
3. **RREF / Howell bases and the stored-basis rule** ([LA] F2): a specification of ENGINE_API §8's rule as a Lean
   definition, and a checker that an emitted basis is that basis.
4. **The digit-induction precision-split lemma (L1)** (ENGINE_API §13.11.3, "proved" in prose): prove it in Lean
   (small, number-theoretic).
5. **The sparse cokernel and Heilbronn–Merel** (slot-15 WP-7 / WP-8): checkers once the certificates exist.

Count: ≈ 52 L3 rows plus ≈ 10 `chk:` items; ≈ 4–8 PM in total.

### 3.5 Priority: value × cost

"Value" means where errors actually occurred:
- [C] Appendix A's 23 errata (E1, E6, E9, E13, E14, E19, E21, E22, E23 were mathematical);
- slot 14's `c0566e2` (contragredient × low-rank);
- slot 15's findings: WP-4 Q2 (`χ` vs `χ̄`), WP-5 M2 / M3 / M4 (`ε_K`, the Hilbert scope, unchecked `S`), the Serre
  locator VERIFY, the Bellaïche–Khare GAP, `pr:latticesplit` refuted, Proposition D refuted at 47 (a missing
  rationality clause).

| Rank | Item | Value | Cost | Why now |
|---|---|---|---|---|
| 1 | L0 C1–C3, C8, C9, C11 + bridges | very high: E1, E6, E19, `χ/χ̄`, B₁, `ε_K` | low (≈ 1 slot) | the nebentypus code (slot-16 WP-10) must not fix `χ`'s sign by accident |
| 2 | L1 register, top ≈ 12 hypotheses (Hecke ring, Eichler–Shimura, Serre / Sturm, Hida control, Mazur / Merel) with verbatim quotations | very high: pointer errors, VERIFY items | low / medium | cheap; closes the "literature gaps" the owner names |
| 3 | G10 saturation + L3-b(2) the stable-certificate checker | high: just refereed with repairs, certificates reach records | medium | mathlib-rich, self-contained |
| 4 | G1 (T2a) | high: bit-identities, FP bounds | medium | prerequisite of G2 / G3 |
| 5 | G3 cone (T3) | high: no independent check | medium | [LA]'s recommendation |
| 6 | G9 level `N` / nebentypus | high: the active front | medium | lands beside the code |
| 7 | G7, G11 | medium-high: E21, the finality certificates | medium | |
| 8 | G2, G4 | medium: well-tested by 159 validations | high (T0's `X_bulk`) | infrastructure for 5–7 |
| 9 | G5, G8 | medium: the literature carries the risk | high, or **H** | `proved_mod_lit` suffices |
| 10 | G6, L3-b(3)–(5) | medium | medium | |

---

## 4. The multi-slot roadmap

### 4.1 Slot 16's Lean portion

The staffing rule applies: Sonnet for standard work, Opus for long or delicate work, Fable only for critical audits;
Opus and Sonnet audit each other. **At most 5 agents run at once, at most 3 of them Fable, across the whole slot.**
The Lean lane holds **at most 2 concurrent seats**, so slot 16's deferred code WPs keep three. Estimates are agent
wall time, excluding audits.

| # | Title | Model | Auditor | Est. | Depends | Wave | Output |
|---|---|---|---|---|---|---|---|
| **L16-0** | Toolchain and skeleton. `lean/` Lake project: `lean-toolchain` v4.33.1, mathlib at `db584cd` (or the local v4.31.0 path dependency if Q3 is declined), and the **shared `lean-deps` packages directory**, verified from two worktrees with one mathlib copy. `GL2.lean` root; `GL2/Census.lean`; `tools/lean_census.sh` with its three negative controls; the leanblueprint venv under `$DATA_ROOT`; a [GT] skeleton that builds (web + PDF, git-ignored outputs). `disk_guard.sh` before every step. | Sonnet | Opus | 90 min (+ one ≈ 6 GB cache download if Q3) | owner Q1–Q3 | A | a compiling empty project; `LEAN_CENSUS … verdict=OK`; negative controls `FAIL` |
| **L16-1** | **FLT harvest survey** (read-only, web). For each L1 cluster of §3.2 and each G9 / G11 literature need: search Anthropic FLT's `Theorems/`, `Definitions/` and `html/` pages (and Imperial FLT, TauCeti) and read the actual declarations. Output `flt_harvest_survey.tsv`: our label, FLT declaration, statement verbatim, dependency-closure estimate (files, lines), verdict **F-H / F-A / none**. Settles every **U** in §0.1. | Opus | Sonnet | 120 min | — | A | the survey; a revised §3.2 count |
| **L16-2** | **The convention layer (L0)** in Lean and [GT] Part 0. C1–C3, C8, C9, C11 as definitions, with `prop:symconv`(2)(3), `lem:detsym`, `lem:symdual`, `prop:pairing` proved. The bridges: `T_{p^ν}` full = primitive + `p^n`-term ([C] `obl:algebra`(ii)); `⟨d⟩` vs Diamond–Shurman; `bernoulli` vs `bernoulli'`; `ε_K` as one definition. Statements before proofs. | Opus | **Fable** (critical: conventions become ground truth) | 180 min + 60 min audit | L16-0 | B | `GL2/Conventions/*`; [GT] Part 0; census shows ≈ 25 `proved` |
| **L16-3** | **The literature register (L1)** and the inventory adjudication. Hypothesis structures for the top ≈ 12 (§3.5 rank 2), each with the verbatim quotation and locator read from the scan (the read-only Hida folder; library scans). Sanity instances where decidable. [GT] Part L. Adjudicate `statement_inventory_v0.tsv`'s `triage` rows (28) and layer guesses, producing `_v1`. Mark the Serre locator and Bellaïche–Khare explicitly. | Sonnet | Opus | 150 min | L16-0, L16-1 (for dispositions) | B | `GL2/Literature/*`; inventory v1 |
| **L16-4** | **The first differential oracle and the first checker** (L3-a / L3-b(1)). Executable `ρ_n` over `ZMod m` against golden `ρ_n` objects at 3 cells; the `obl:tau` predicate as a decidable `Prop` with the soundness theorem "predicate ⇒ (T1)–(T3) on generators", run on the `p = 2` table emitted by the C++ (read from a file, `decide` / kernel). No C++ change beyond an optional table-dump env hook, which is validation-only. | Opus | Sonnet | 150 min | L16-2 | C | the first `chk:` item green on real C++ output |
| **L16-5** | **Fable audit** of the axiom / hypothesis policy (§2.6), L16-3's quotations (a sample of ≥ 50 %) and L16-4's soundness statement. It checks that no hypothesis is vacuous or inconsistent, that each quotation matches its locator, and that the checker's soundness theorem says what [GT] claims. | Fable | — | 60 min | L16-3, L16-4 | D | an audit report; repairs by the authors |
| L16-6 (stretch) | Statement skeletons (`sorry`) for G10 (saturation) and G3 (cone), full clause coverage, [GT] chapters mirrored; census shows them `stated` | Opus | Sonnet | 120 min | L16-2 | D | ≈ 40 `stated` rows |

**Fable count** in the Lean lane: 2 (L16-2's audit, L16-5), not concurrent. Together with the code lane's critical
audits the slot stays within 3.

**How the Lean lane interleaves with slot 16's deferred code WPs** ([S15] "Deferred to slot 16"):
- **Nebentypus code (WP-10).** L16-2 pins C8 (`χ(a_γ)`, `⟨d⟩ = χ(d)`) and the bridge to the `S_k(N, χ)` / `S_k(N, χ̄)`
  dictionary **in wave B**. WP-10 starts in wave B or C, **cites `[GT, conv:nebentypus]`**, and its (NB5) first run
  records the sign against the Lean bridge statement ([S15] WP-4 Q2's requested `\COMP^a` remark). This is the one hard
  ordering: WP-10's validation must not be the place the convention is decided.
- **Weight shift / `m = 2` (WP-11), general `N`, the ℓ-local isotropy model, [U] part 2, census edition 3.** These have
  no ordering constraint with the Lean lane in slot 16. Their new statements enter `statement_inventory_v1.tsv` as
  `planned` rows (rule: a new [C] / [U] statement is added to the inventory in the same commit, like rule 20's
  label-first discipline).
- **Disk.** The Lean lane's one shared mathlib copy (≈ 6–7 GB) is booked at slot planning against C:'s budget. With
  ≈ 48 GB free, the 15 GB floor and ≈ 5 GB per C++ build, three concurrent C++ builds and the Lean deps fit; four do
  not.
- **RAM.** `lake build -j 8` (≤ 40 GB) never runs alongside a ≥ 20 GB C++ verification run. The Lean seat checks
  `box_watch.sh` first.

**Slot-16 exit criteria (Lean lane):**
1. the `LEAN_CENSUS` line reads `global_axioms=0 unresolved=0 stale=0 verdict=OK`;
2. [GT] builds (web and PDF) and passes `checkdecls`;
3. L0's C1, C2, C3, C8, C9 and C11 are `proved`, their bridges `proved` or `proved_mod_lit`;
4. ≥ 12 L1 hypothesis structures carry quotations;
5. one checker is green on real C++ output;
6. the Fable audit is ACCEPT or ACCEPT WITH REPAIRS, with repairs applied;
7. `label_census.py` resolves `[GT, …]`.

### 4.2 Slots 17 and later: milestones

| Milestone | Target slot (v1.0) | v1.1 forecast | v1.2 forecast | **v1.3 forecast** | Content | Exit |
|---|---|---|---|---|---|---|
| **M1** coefficients and certificates | 17 | **17, met** (F3 ACCEPT WITH REPAIRS) | **17, met** | **17, met** | G1 (T2a) complete; L3-b(1) on the full golden τ grids (compiled checker); G10 saturation **proved** + the L3-b(2) stable-certificate checker run on the WP-5 certificates; L1 register complete (≈ 25) | [C] gains `\LEAN` tags on ≈ 40 statements (Q9) |
| **M2** model and operator | 18 | **18**; exit made checkable as M2-a … M2-h (L18-0 §3); harvest = survey complete, F-H closures on demand; Q12 = stay | **18, met** (F3-18 ACCEPT WITH REPAIRS; H4(ii) the one `stated` row) | **18, met** | T0's combinatorial `X_bulk`, Ψ (`thm:explicit_complex_equiv`(1)), G2's `thm:welldef` equivariance; the harvest finished; decide the mathlib bump (Q12) | H4 consequences stated over the combinatorial model |
| **M3** cone and comparison | 19 | **18–19**: G3 in 18 (L18-4), G4 in 18 only as stretch L18-7 | **19**: G3 and G4's abstract half done in 18; C1, the bridge, `model7_acyclic` in 19 by M3-a … M3-g (L19-0 §4); conditional form if `model7_contract1` stays `stated` | **19, met** (F3-19 ACCEPT WITH REPAIRS; `stated = 0`, `model7_acyclic` proved) | G3 (T3) proved; G4 (§5.1 projective reduction) with mathlib `groupCohomologyIsoExt` | `rmk:orbifold` and `lem:tauexists`(2) proved; the cone chapter `\LEAN` |
| **M4** Hecke ring, level `N`, nebentypus | 20 | **19** (19–20) | **20** (O10; skeleton as stretch L19-5) | **20**, branch H for M4-c … M4-f, P ≈ 0.85; cut M4-a … M4-j (`slot19/L19-5_M4_skeleton.md` §3, re-cut by L20-0 §2); Shimura locators `\VERIFYloc` until R20-L | G5 (the Hecke ring proved, or **H** plus the `p^n I` difference proved); G9 level `N` and nebentypus; L3-a Heilbronn–Merel oracle | owner review of **[C] → [GT] supersession** (Q5) |
| **M5** Dickson, θ, ordinary, finality | 21–22 | **20** (20–21) | **21** (21–22) | **21** (21–22) | G7 with Dickson invariants proved; G11 finality certificates; L3-b(3) the stored-basis rule; L3-b(4) the digit lemma | [E] `sec:alg` certificates mirrored (slot 22: met in the cut form; thm:classical → M6) |
| **M6** Hida and [U] | 23+ | **21–22** (band 21–24) | **22–23** (band 22–25) | **22–23** (band 22–25) | G8 `proved_mod_lit` over the Hida hypotheses; [U] mirrored; G6 integral line | [U] cites [GT] throughout; **orbifold item (L0-L10) MET, F-MP3 2026-10-10** (`MPL1_report.md`, `MPL3_report.md`, `F-MP3_gate.md`; scope: unnormalised `u^*`, label independence on cohomology only, `prop:mpbredon`(2) "if" only, (3) open); **v1.8: M6 met in the re-scoped core (slot 24): A, A-T, A-Θ, C-w; Hida / [U] / G8 / G6 → M8** |

### 4.3 Effort, in slots

[LA]'s person-month figures assumed an experienced *human* mathlib contributor, with a ×0.5–×3 band. Anthropic's FLT
shows that agent swarms can go much faster: 13M lines in 11 days with dozens of agents. This programme runs **≤ 2
agents at a time**, on a single box, beside a production codebase. Planning figure: **one milestone per slot for
M1–M4, two slots each for M5 and M6**, so **≈ 8 slots to M6**. This carries **±50 %** uncertainty, dominated by agent
Lean proficiency (risk R4). The plan is re-estimated at the slot-16 close from measured velocity: statements proved
per agent-hour in L16-2 and lines per proved statement.

**Revised by L17-0 (2026-10-01, `docs/implementation/slot17/L17-0_report.md`; a v1.1 proposal for the owner; §4.2 is
not rewritten).** Slot 16's Lean packages (L16-0 … L16-4, L16-6) took **≤ 199 agent-minutes** against 810 planned
(×0.25). With the audit repairs that is **311 min**, and the two Fable audits took 33 min against 120. The rates
measured:
- ≈ 180 declarations per agent-hour in the convention layer;
- ≈ 25 per hour for checker work that includes a C++ hook;
- ≈ 125 `proved` per hour in L16-6's mixed package;
- 14.6 hand-written lines per declaration, 18 per proved one.

The three "2–3 h" hard closures took ≤ 16 min. One of the two `stated` rows closed in slot 16 was false as stated. F3's
repairs cost 0.9× the audited implementer time (census tooling, a first-time cost). The planning rule is 0.5×, with a
60-min floor.

These rates come from the easiest layer. For the unmeasured hard categories (G10's commutative algebra, G1, G2's
`X_bulk`, G5) the factor is raised to ≈ 0.5. On that basis:
- M1 fits slot 17 with room to spare (central ≈ 11 h against ≈ 17 h);
- **M2 and M3 merge into slot 18**;
- M4 lands in slot 19, M5 in slot 20, and M6 in slots 21–22.

That is **≈ 6 slots to M6 (band 21–24), not ≈ 8**. Agent throughput is not the binding constraint: slot 16 used
≈ 5.75 of ≈ 20 Lean seat-hours. What binds is the one Fable window per slot, the serial repairs, the false-statement
work and the owner gates (Q12, Q5). The next re-estimate is at the slot-17 close, from L17-1's and L17-3's actuals,
which are the first hard-proof data.

**Revised by L18-0 (2026-10-03, `docs/implementation/slot18/L18-0_velocity.md`; approved by the owner as a forecast, O4).**
Slot 17's Lean implementers took **≤ 244 agent-minutes** against 1035 planned, a factor of **×0.24**, the same as slot 16.
The first hard categories ran no slower than the convention layer:
- G10 closed 20 `stated` rows in ≤ 40 min, about 2 min per row;
- G1 produced 150 declarations in ≤ 61 min.

Both had a clause-level skeleton and mathlib cover. G2 (`X_bulk`) has neither, so its factor stays ≈ 0.5.

F3's repairs took **0.30×** the audited time. The planning rule becomes 0.3× with a 60-min floor; checker packages keep a
60-min audit-repair reserve, after L17-4's REPAIR BEFORE MERGE.

The cumulative false-as-written rate is **3 in ≈ 36** closed or audited skeleton rows. Two of the three are rows that carry a
literature hypothesis, so the planning figure is ≈ 10 % in general and ≈ 30 % for literature-bound rows.

Consequences:
- the slot-18 Lean critical path is ≈ 6.75 h central (L18-1 → L18-2 → F3 → repairs);
- M2 is met in slot 18 by the checkable criterion M2-a … M2-h (L18-0 §3), with H4(ii) as the only row allowed to stay
  `stated`;
- M3 splits: G3 in slot 18, and G4 in slot 18 only if the stretch runs, else slot 19;
- M4 lands in slot 19, M5 in slot 20, M6 in slots 21–22 (band 21–24), unchanged from L17-0.

The binding constraints are still the Fable window, the serial repairs, false statements and the owner gates. Throughput is
not one of them. **Q12** is affirmed: stay on `db584cd`. FLT is pinned there, the harvest's F-H closures have not run, and
everything M2–M4 needs is present: `groupCohomologyIsoExt` and the Shapiro files for M3–M4, the rest for M2. Earliest bump
is a dedicated WP in slot 20, on a named missing lemma. The next re-estimate is at the slot-18 close, from L18-1 / L18-2
(G2's actuals).

**Revised by L19-0 (2026-10-03, `docs/implementation/slot19/L19-0_velocity.md`; a forecast, owner rulings O9 / O10 of slot 19).**
Slot 18's Lean implementers (L18-1 … L18-5) took **≤ 251 agent-minutes** against L18-0's central 630 (×0.40) and the plan's 1080 (×0.23).
That is the third slot in a row at ≈ ×0.24 of the plan. G2, the first category without a skeleton or mathlib cover, ran at **×0.19** of
L18-0's central (≤ 51 min for L18-1 + L18-2), so the 0.5 factor for new categories is retired. F3 took 64 min, and its repairs took 31 min
(0.12×; the 60-min floor stays). The skeleton's false-as-written rate fell to ≈ 6 % (3 in ≈ 50). The one false statement slot 18 found
was in [C] (`thm:welldef`(c)), confirmed by the owner.

Planning rules for slot 19:
- ×0.4 of the slot plan's figure for items with a skeleton or a carried design;
- ×1.0 of a bottom-up figure for items without a finite skeleton;
- F3 at 60 min, repairs at 0.3× with a 60-min floor.

The one such item is `model7_acyclic`. Its statement is about the infinite `X_bulk`, so `decide` covers only the local tables and a
base case, and `H_1 = 0` needs a Euclidean descent (mathlib has `SL2Z_generators` and `FixedDetMatrix.reduce_rec`, but no
presentation of `SL(2, ℤ)`).

Consequences:
- core Lean ≈ 8.75 h central;
- the critical path is ≈ 5.5 h (band 4.5–10 h), with the bridge and `model7_acyclic` in parallel;
- M3 is met in slot 19 iff M3-a … M3-g hold with `stated = 0`, or met modulo `model7_contract1`, reported to the owner as not met;
- M4 slot 20, M5 slot 21, M6 slots 22–23 (band 22–25), one slot later than v1.1 by O10's seat decision, not by velocity.

The binding constraints are still the Fable window, the serial repairs and the owner gates, now joined by the first statement whose
proof is open design (`contract1`). Q12 is unchanged: stay on `db584cd`, and nothing M3 needs is missing. The next re-estimate is at
the slot-19 close, from L19-2 / L19-3.

**Revised by L20-0 (2026-10-04, `docs/implementation/slot20/L20-0_velocity_recut.md`; a forecast, owner rulings O7 / O8 of slot 20).**
Each start is the birth time of the package's scratch directory, a late start, so the actual is a lower bound. The upper bound runs
from the event that freed the seat.

| Package | Actual (min) | L19-0 central | Bottom-up | ÷ central | ÷ bottom-up |
|---|---|---|---|---|---|
| L19-1 C1 | 20 (20–23) | 45 | 120 | ×0.44 | ×0.17 |
| L19-3 `model7_acyclic` | 24 (24–33) | 210 | 120 | ×0.11 | ×0.20 |
| L19-2 bridge, `rmkOrbifold` | 56 (56–71) | 120 | 240 | ×0.47 | ×0.23 |
| L19-4 C2 | 34 (34–151) | 90 | 180 | ×0.38 | ×0.19 |
| L19-5 M4 skeleton | 13 (13–36) | 60 | 120 | ×0.22 | ×0.11 |
| **Implementers** | **147** | **525** | **780** | **×0.28** | **×0.19** |
| F3-19 | 82 | 60 | — | ×1.37 | — |
| Repairs | 30–34 | 60 | — | — | 0.20× audited |

Slot 19 is the fourth slot in a row at ≈ ×0.2 of the bottom-up figures: ×0.25, ×0.24, ×0.23, ×0.19. The one item forecast at ×1.0
("no finite skeleton", `model7_acyclic`, P(`stated = 0`) ≈ 0.5) ran at ×0.20. That rule is retired. No false-as-written row was
found in slot 19 (≤ 6 % cumulative). The ≈ 30 % figure for literature-bound rows has no new data, and it now matters, because
M4's branch H adds four Part-L rows.

Planning rules for slot 20:
- ×0.25 of bottom-up for every item, with a 20-min floor and a band of ×0.15–×1.0;
- F3 at 0.55 × the audited implementer minutes, floor 60;
- repairs at 0.3× with a 60-min floor.

Consequences:
- M4 implementers ≈ 220 min central, ≈ 6.7 h with F3 (≈ 120) and repairs;
- the critical path with two Λ seats is ≈ 5.2 h (band 4–11 h): L20-1 → L20-2 → L20-5 beside L20-3 → L20-4, then F3 and repairs;
  with one seat (L20-H holding the other) it is ≈ 6.7 h;
- **P / H:** H for M4-c, d, e and f. P needs a Hecke ring and a corestriction, and `db584cd` has neither. Branch P (L20-2′,
  ≈ 90 min central, 720 tail) is a stretch that would discharge `hTp` / `hcop`;
- `cosetData_nonempty_stmt` stays as frozen, by `exists_Gamma_le_conj` + `instFiniteIndexGamma`;
- P(M4 in slot 20) ≈ 0.85;
- **supersession (Q5) should be conditional on R20-L's verification** of the Shimura locators (Thm 3.24, Props 3.8, 3.30) and of
  the `T(1, p^ν)` notation question (L19-5 §5.1).

The binding constraints are now the audit (the longest Lean item), the owner's scan and the owner's Q5 time. Throughput is not
one of them. **Q12** is unchanged: stay on `db584cd`, and M4 names no missing lemma. L20-H (O7) only measures the cost of a later
harvest. The next re-estimate is at the slot-20 close, from L20-1 … L20-5. Each package should create its scratch directory
first, so that the birth time is the start time.

---

## 5. Owner questions

Each question has a recommendation and a default that applies if the owner does not answer. **All fourteen were RULED on
2026-10-01 by the owner, every one at the recommendation** (slot-15 close item S15-O3; [X] v1.20.1 [OD] S15). The
questions stand as asked; the ruling follows each.

1. **Q1: the base.** Should the project depend on mathlib pinned to Anthropic FLT's pin (Lean v4.33.1, mathlib
   v4.33.0 `db584cd`)? FLT itself would be reused only by harvesting vendored, provenance-tracked files (Apache-2.0
   NOTICE carried) or by FLT-attested restatements, never by a Lake `require` (FLT says it is not a dependency, and it
   needs ≈ 150 GB RAM and 67 GB). *Recommended:* yes. *Default:* yes.
    **RULED 2026-10-01: yes: mathlib pinned to Anthropic FLT's pin (Lean v4.33.1, mathlib v4.33.0 `db584cd`); FLT reused only by harvest or FLT-attested restatement, never by a Lake `require`.** (owner, at the recommendation.)
2. **Q2: location.** In-repo `lean/`, with one shared dependency tree for all worktrees, or a separate repository?
   *Recommended:* in-repo. *Default:* in-repo.
    **RULED 2026-10-01: in-repo `lean/`, one shared dependency tree for all worktrees.** (owner, at the recommendation.)
3. **Q3: disk.** Approve **one** download of mathlib v4.33.0 source + oleans cache (≈ 6–7 GB on C:) into
   `$HACS_DATA/lean-deps/`, shared by every worktree? *Recommended:* yes. *Default:* **no
   download**; L16-0 uses the local v4.31.0 checkout as a path dependency, and harvesting waits.
    **RULED 2026-10-01: yes: one download of mathlib v4.33.0 source + oleans cache (≈ 6–7 GB on C:) into `$HACS_DATA/lean-deps/`, shared by every worktree (`disk_guard.sh` first, 15 GB floor).** (owner, at the recommendation.)
4. **Q4: the ground-truth document.** Name `gl2_groundtruth.tex`, key **[GT]**, built as a leanblueprint with the
   label scheme of §2.4 (mirror labels verbatim; new kinds `conv:`, `bridge:`, `lit:`, `inf:`, `chk:`)?
   *Recommended:* yes. *Default:* yes.
    **RULED 2026-10-01: yes: `gl2_groundtruth.tex`, key [GT], a leanblueprint with §2.4's label scheme.** (owner, at the recommendation.)
5. **Q5: precedence and supersession.** [GT] is authoritative for Lean-proved statements now, and [C] carries an
   erratum on any conflict. Full supersession of [C]'s mathematical chapters by [GT] is reviewed at M4.
   *Recommended:* yes. *Default:* yes (no supersession before M4).
    **RULED 2026-10-01: yes: [GT] authoritative for Lean-proved statements now, [C] carries an erratum on any conflict; full supersession reviewed at M4, none before.** (owner, at the recommendation.)
6. **Q6: the axiom policy.** No `axiom` keyword. Literature enters as hypothesis structures carrying quotations and
   is sanity-instantiated where decidable. `native_decide` is allowed only in checkers, and censused. *Recommended:*
   yes. *Default:* yes.
    **RULED 2026-10-01: yes: no `axiom`; literature as hypothesis structures with quotations, sanity-instantiated where decidable; `native_decide` only in checkers, censused.** (owner, at the recommendation.)
7. **Q7: a cluster FLT build.** One cluster-B / cluster-A CPU job (≈ 530 core-h, ≈ 150 GB RAM) to build Anthropic FLT and run
   `comparator`, turning FLT-attested restatements into machine-matched ones? *Recommended:* not in slot 16; decide
   after L16-1 shows how many statements it would attest. *Default:* no.
    **RULED 2026-10-01: not in slot 16; decided after L16-1 shows how many statements it would attest.** (owner, at the recommendation.)
8. **Q8: the Lean share of slot 16.** At most 2 concurrent Lean seats, WPs L16-0 … L16-5 (L16-6 a stretch), Fable twice.
   *Recommended:* yes. *Default:* yes.
    **RULED 2026-10-01: yes: at most 2 concurrent Lean seats, L16-0 … L16-5 (L16-6 a stretch), Fable twice.** (owner, at the recommendation.)
9. **Q9: a new [C] tag.** Add `\LEAN{label}` ("formally verified; see [GT]"; the `proved_mod_lit` variant lists its
   hypotheses) beside `\PROVED`, from M1? *Recommended:* yes. *Default:* yes, from M1.
    **RULED 2026-10-01: yes: `\LEAN{label}` (with the `proved_mod_lit` variant) beside `\PROVED`, from M1.** (owner, at the recommendation.)
10. **Q10: upstreaming.** Offer generic pieces (the `ρ_n` / `Sym^n` matrix API, Dickson invariants, Kummer
    congruences, cyclic-group cohomology) to mathlib? *Recommended:* opportunistic only, never on the critical path.
    *Default:* no.
    **RULED 2026-10-01: opportunistic only, never on the critical path.** (owner, at the recommendation.)
11. **Q11: [EX] and the Galois note.** Are they mirrored? *Recommended:* no. They cite [GT] and [C] by label, and
    their `\PROVED` interpretive claims are formalized only if promoted into [C] / [E] / [U]. *Default:* no.
    **RULED 2026-10-01: no: [EX] and the Galois note are not mirrored; they cite [GT] and [C] by label; their `\PROVED` interpretive claims are formalized only if promoted into [C] / [E] / [U].** (owner, at the recommendation.)
12. **Q12: following mathlib upstream.** Freeze at v4.33.0 until the harvest is done (≈ slot 18), then bump at most
    once per two slots in a dedicated WP? *Recommended:* yes. *Default:* yes.
    **RULED 2026-10-01: yes: frozen at v4.33.0 until the harvest is done (≈ slot 18), then at most one bump per two slots in a dedicated WP.** (owner, at the recommendation.)
    **Recorded at milestone M2 (slot 18, WP-17; F3-18 MINOR 7): stay on `db584cd`.** L18-0 §5 recommended STAY, the
    slot-18 plan's O4 recorded "stay unless L18-1 names a missing lemma", and neither L18-1 nor L18-2 named one; M2 was
    met on `db584cd` (F3-18, ACCEPT WITH REPAIRS). Earliest bump: a dedicated WP in slot 20, on a named missing lemma.
13. **Q13: the C++ harness.** Keep `--all` Lean-free, with only an optional `fast` `LeanCensusFileValidation` reading
    the committed `census.tsv`, and make the `LEAN_CENSUS` line a slot-close-window step? *Recommended:* yes.
    *Default:* yes.
    **RULED 2026-10-01: yes: `--all` stays Lean-free; an optional `fast` `LeanCensusFileValidation` reads the committed `census.tsv`; the `LEAN_CENSUS` line is a slot-close-window step.** (owner, at the recommendation.)
14. **Q14: C++ hooks for certificates.** May Lean WPs add validation-only, env-interlocked **table-dump** hooks to
    the C++ (for example `HECKE_DUMP_TAU=<dir>`)? They would be read-only for the tree and emit into scratch, with no
    record, golden or setting change. *Recommended:* yes. *Default:* yes, each one listed in the WP report.
    **RULED 2026-10-01: yes: validation-only, env-interlocked table-dump hooks, read-only for the tree, emitting into scratch, no record / golden / setting change, each listed in the WP report.** (owner, at the recommendation.)

---

## 6. Risks

| # | Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|---|
| R1 | **mathlib churn.** Names move; our code breaks on a bump. | high (on bump) | medium | pin (Q12); bump only in a dedicated WP; the harvest manifest bounds the port |
| R2 | **FLT pin drift.** FLT is unmaintained; its v4.33.0 falls behind mathlib, so harvested files become a port burden. | certain over time | low–medium | harvest only small closures (**F-H**); the rest is **F-A** (statement-level, version-independent); keep the upstream commit in the manifest |
| R3 | **Disk.** A per-worktree mathlib (≈ 7 GB each) would breach the 15 GB floor within two worktrees. | high without mitigation | high (the 2026-09-25 crash) | one shared `lean-deps` tree, verified in L16-0 before any second worktree builds; `disk_guard.sh` before every `lake` step; build dirs deleted at hand-off |
| R4 | **Agents' Lean proficiency.** Proofs stall and velocity is ≪ plan. | medium | high (schedule) | statements before proofs (the statement itself has value); Opus on proofs; measure velocity in slot 16 and re-plan; FLT is evidence that Claude agents can do this at depth |
| R5 | **Axioms / hypotheses mask errors.** A mis-transcribed Eichler–Shimura or Hida statement is consistent but false, or an inconsistent pair of hypotheses makes theorems vacuous ([EUC] Book I). | medium | high | hypothesis structures, not axioms (a false one taints only its consumers); verbatim quotations audited by a second model (L16-5); sanity instances; normalisation *differences* proved as theorems ([LA] §8.3's pattern); FLT-attested where possible |
| R6 | **A convention pinned wrongly in Lean** then propagates as "ground truth". | low–medium | high | Fable audit of L16-2; bridge lemmas to at least one literature normalisation per convention; the differential oracle against the C++ |
| R7 | **[GT] drifts from [C].** Two texts of one statement diverge. | medium | medium | the `% mirrors [C] vX.Y` line and the census check; the precedence rule (Q5) |
| R8 | **CPU / RAM contention** with C++ verification runs on a shared 62 GB box. | medium | medium | the `-j 8` cap, a `box_watch.sh` check, no Lean builds during close windows W1 |
| R9 | **`native_decide` trust.** Large certificate runs rely on the compiler. | certain where used | low | confined to `GL2/Algorithms/`, censused; soundness theorems kernel-only; small instances re-run by `decide` |
| R10 | **Scope creep toward research-scale formalization** (Eichler–Shimura, Hida control). | medium | high | these stay **H** by plan (§1.2); only the owner can promote one to **P** |

---

*Planning only. No Lean code, Lake project, dependency download or build was made. The only files written are this
plan and `statement_inventory_v0.tsv` (generator in scratch at `$HACS_DATA/lean-plan/`).*
