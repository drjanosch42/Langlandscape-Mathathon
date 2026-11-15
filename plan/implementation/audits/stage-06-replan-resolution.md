# Resolution of the stage-06 re-plan audit (`audits/stage-06-replan-audit.md`, A1–A23)

Reviser: Opus, 2026-11-14. Subject: `stage-06.md` rev. 1 (0285aba) → **rev. 2** (this commit). Every finding was re-checked
against the stage tex, the Lean project (read-only), `tools/titan_batch.sh`, `lakefile.toml`, the current `OVERVIEW.md`
(4deb009) and the frozen Mathlib `/home/janosch/data/mathlib4_v4350` (grep/read only; no build, no lake).
Also handled: stage-04 audit items A1, A2, A12 (cross-stage 06, relayed by the coordinator; S04 A11 is a 04/05 seam with no S06
side).

**Counts: ACCEPT 16 · MODIFY 7 · REJECT 0** (23 findings).

| id | verdict | what was done | evidence |
|---|---|---|---|
| A1 (crit) | MODIFY (option ii, strengthened) | §0 `if:s06-lemD` block rewritten as Lean text: all duality isos are `≃ₗ[A]`; S-equivariance and the map itself are pinned by exported `bEquivDualQuot_apply` (`e b (mk s) = ℓ (b * s)`), `bEquivDualQuot_smul` (`e (s • b) = e b ∘ₗ mulLeft A (mk s)`), same for `aEquivDualQuot`, plus `quotAEquivDualB_mk`. No new instance (option i rejected: a `Module S (Module.Dual A M)` instance is a non-defeq diamond with `LinearMap.module` at `S := A`). Exact argument lists for (c) (`hb`, and `hℓ` where needed), `NewOldData` without unused instance params, concrete `split_iff` signature (stage 05 uses it). New "fixed decision" bullet records why. | Mathlib v4.35: `Module.Dual` is `abbrev … := M →ₗ[R] R` (`LinearAlgebra/Dual/Defs.lean:61`); `LinearMap.module` needs `[Module S M₂] [SMulCommClass R₂ S M₂]` with `M₂ = A` (`Algebra/Module/LinearMap/Defs.lean:946–948`), i.e. `Module S A`, absent; precomposition only `Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M')` (`Algebra/Module/LinearMap/Basic.lean:109`); `LinearAlgebra/Dual/Defs.lean` instances: only `Inhabited`, `IsReflexive`. `Submodule.module'` (`Submodule/Defs.lean:296`) gives `Module A ↥𝔟`; `LinearMap.mulLeft` (`LinearMap/Defs.lean:1018`) needs only `SMulCommClass A (S⧸𝔞) (S⧸𝔞)`, from `Ideal.Quotient.algebra` (`Ideal/Quotient/Operations.lean:365`). Tex `lem:s06-D`(b) "β ↦ ℓ(β·) gives S-isomorphisms": the `_apply` lemma is exactly this map. |
| A2 (maj) | ACCEPT | L7 `squeeze` gets `[IsLocalRing 𝒪] [IsLocalHom P]`; `Defect.Setting` has `P_surj` (structural: `𝒪_P = I/P`) and L8a proves `Setting.isLocalHom_P`; L12 item (9), M3 note. | Counterexample re-checked: `ℤ_(p) ⊂ ℚ`, `𝔱 = (p)`, `h = 1` satisfies all rev.-1 hypotheses. Tex step (5) uses `𝔡 ⊄ 𝔪_I ⇒ 𝔡 = I` after `P(𝔡) = 𝒪_P`, which needs `P` local (`IsLocalHom`, `Algebra/Group/Units/Hom.lean:270`). |
| A3 (maj) | MODIFY | `Defect.Setting` fixed in §0 over `Λ, I, T, 𝒪, G` with `𝔞Λ 𝔟Λ : Ideal T`, `lamΛ : T →ₐ[Λ] I`; `R := I ⊗[Λ] T` is an `abbrev` (no field + equivalence `e`), `𝔞 := 𝔞Λ.map includeRight`, `lam := AlgHom.liftEquiv Λ I T I lamΛ`, `quotient_baseChange` from `tensorQuotientEquiv`. `gor_new` moved to new WP L8c. | Tex `def:s06-rings`: `R := T ⊗_Λ I_F`, "keep the names 𝔞, 𝔟 for 𝔞R, 𝔟R". Mathlib: `AlgHom.liftEquiv` (`RingTheory/TensorProduct/Basic.lean:716`), `Algebra.TensorProduct.tensorQuotientEquiv` (`RingTheory/TensorProduct/Quotient.lean:96`). Defining `R` avoids an extra hypothesis-like field. |
| A4 (maj) | MODIFY (derive, no 9th Hyp of that kind) | L9b: the fixed-weight (Gor) is `IsGorenstein.baseChange` (L13) of `Hyp.HsiehGorFull` along `P`, applied to `𝒪 ⊗[I] D.R`; the identification with `T_k(N)_𝔪` is stated as part of `Hyp.HidaControlGL2` (table in §0). L12 item (9) checks it is not hidden. | Tex step (3) already uses control `T/P ≅ T_k^ord ≅ T_k(N)_𝔪` (p-stabilisation); Gorensteinness of a finite free algebra is stable under base change (that is L13). A separate `Hyp.KOGorenstein` would duplicate a consequence of (Gor_R) + control. The KO Prop 5.1(1) citation stays in the maths (M3). |
| A5 (maj) | ACCEPT | (a) M1, M4 → hard, opus (+pf). (b) L2 → hard, opus (+pf). (c) L8a = Setting + Hyp statements, conceptual, opus; new L8c = `gor_new`, opus (+pf). (d) budgets on every row (`—` for conceptual/stage master; L1 opus (+pf); H1 opus (+pf); L11 sonnet +bf for edits). (e) X1 sonnet (+bf). | Brief A / OVERVIEW §5.1 table; "every WP row names model + fix-round budget". |
| A6 (maj) | ACCEPT | New **S06-L18** early-lane Fable Lean audit on `s06-gate1-1` (precondition of the hand-over merge); row group **S06-AW-<wp>** (opus WP audits for L1, L2, L3, L4, L5a, L5b, L6b, L13, L8a, L8c, L9a, L9b, C1, C4, C5, C7; fable for strands); DAG edge `AW → merge`; +6 min on the critical path. Maths hard WPs are covered by M9 + M6. | OVERVIEW §5.3 "WP-level audit … before merge for every hard/conceptual WP". |
| A7 (maj) | ACCEPT | L11 trigger = all non-optional L WPs green (list in the row); CP text and row agree; optional WPs merging later get a delta check before L16 (§3.2). | Rev.-1 L11 row vs CP "int2b (L9b green) → gate-1" contradiction confirmed. |
| A8 (maj) | ACCEPT | Comment moved to its own line in the spec; "no trailing comments" (`awk '$1 !~ /^#/ && /#/'` empty) in X0/X1 acceptance; §3 general rule. | `titan_batch.sh` l. 10–12: `case "$wp" in ''|\#*|AXIOMS) continue`, then `for f in $rest` word-splits the rest into modules. |
| A9 (maj) | ACCEPT (recomputed with OVERVIEW §4.4 method) | A: 12+12+20+6×7+5+8+15+5+5+6 = **130 min ≈ 2.2 h (1.6–2.9)**; mixed +10–15; B: 12+20+15+9×7+5+8+15+5+5+6 = **154 ≈ 2.6 h (1.8–3.4)**; early lane ≈ 2.0 h. X1 stubs the §0 Setting and Hyp names (SORRIES on int branch only). L15 counted once (incl. its round). Two draft waves in B (≤ 8 subagents). Cross-check stated. | OVERVIEW §4.4 (R × 4–8 min all-in, upper half for hard; no double count), F12. |
| A10 (maj) | ACCEPT | E1′ moved to **S06-L5b** (leaf); auditor fable; trigger rule incl. stage-04's E1′ (one E1′ per project); L5b held until the S04 status is known (§5). | DAG: L5b has no consumer except gates; L5a → L9b. OVERVIEW §5.2 "E1 → fable WP audit". |
| A11 (maj) | MODIFY | New local **S06-XM0** (sonnet +bf, 8 min) creates standalone/driver/NOTES; M WPs depend on XM0, not X1; per-WP files `chapters/s06/s06-<wp>.tex` + `bib/s06-<wp>.bib`; remote M WPs use the **package branch `abhijit/s06-math`** with one writer (OVERVIEW §6.1 O13, which postdates the audit); M6 remote output `mathematics/litnotes/s06-m6-levM.md` (inside the allowed `litnotes/*` set); fallback-model column and M6 re-run rule added. | OVERVIEW §6.1 (package structure, file names, "local fallback model" column, re-run rule). Rev.-1 M11 and X1 both created `bib/s06.bib` (confirmed). |
| A12 (maj) | ACCEPT | §3.1 hand-over merge: X0 does no tools edit and depends on S02-X1; source = clean `impl/s06-early` (`.titan/` grep = 0); the **global master** merges at a stage boundary (recommended 04→05) with the three aggregator files' lines in the merge commit; merge gate = stage k+1's `int1`; outbox hand-over file. | `lakefile.toml`: `[[lean_lib]] name = "Langlandscape"` without `globs` (only `LanglandscapeVendorStacks` has globs); OVERVIEW §2 (only the stage master merges into `wip-implementation`, `.titan/` grep); S02-X1 widens `check_wp.sh` to `s[0-9][0-9]-` (stage-02 plan l. 70, 93, 222). |
| A13 (min) | ACCEPT | L6b proves only `surjective_groupAlgebra_of_absIrred` (no `Hyp` import); new stretch **L6c** (after L8a) does the one-line discharge; GL2TF-free grep restricted to the explicit early file list (§0). | Rev.-1 L6b "discharge `Hyp.ResidualBurnside`" requires importing `Langlandscape.Hyp.ResidualBurnside`, violating the CommAlg-only import rule. |
| A14 (min) | ACCEPT | L13 `congruenceIdeal_baseChange` takes `(hℓ : IsGorensteinWith A S ℓ)` and `[IsLocalHom (algebraMap A A')]`; Lean form of `μ ⊗ A'` fixed as `AlgHom.liftEquiv A A' S A' ((Algebra.ofId A A').comp μ)`. | Tex `lem:s06-S` states base change for Gorenstein `S` and local `φ`; `ann (ker μ)` is a kernel of a map of free modules, which does not commute with non-flat base change in general. |
| A15 (min) | MODIFY | L1 adds `isGorenstein_iff_cyclic` (`S^∨` cyclic over `S` ⇔ the trace map is bijective, via the Orzech property), not "`S^∨` free over `S`", because that would need the non-existent `S`-module structure (A1). Tests moved to `LanglandscapeTests/S06/Gorenstein.lean`. | `RingTheory/OrzechProperty.lean:90` `bijective_of_surjective_of_injective`; tex `lem:s06-G` proof ("cyclic … then a surjection of free modules of equal rank"). |
| A16 (min) | MODIFY | No new grammar requested: the early lane uses the O16 kinds (`int1`–`int4`, `gate1`), in-stage continues at `int5`/`gate2` (A) or starts at `int1` (B); job ids `s06-<job>-<n>`; spec `.titan/spec-int<k>.txt`; axiom files `.titan/s06_<wp>_axioms.lean` (one per WP); X2 runs from `int1`. | OVERVIEW §4.3 "Grammar (O16)" and spec format `AXIOMS <.titan/sNN_<wp>_axioms.lean>`. |
| A17 (min) | ACCEPT | Tests in `LanglandscapeTests/S06/{Gorenstein,Toy,Hyp}.lean`; grep list uses them. | Stage-1 layout `LanglandscapeTests/S01/`. |
| A18 (min) | ACCEPT | X1 writes name-only placeholder rows; L8a's report carries the final text (stage master applies). | — |
| A19 (min) | ACCEPT | L12 checklist items (8) def/structure docstrings, (9) A2/A4 checks, (10) diff of `if:s06-lemD` and `Hyp.HsiehGor` against the stage-05/04 quotes. | OVERVIEW §3.6 l. 329 (def/structure docstrings not machine-checked). |
| A20 (min) | ACCEPT | §0 states "no locality of `S`" and the file split; seam note to stage 05 is a cross-stage item below (incl. `split_iff` signature, file of `NewOldData`, L6F scope). | Stage-05 §0 seam (48f585a) quotes the old `≃ₗ[S]` signature and `s06-eint1`/`s06-egate-1`. |
| A21 (min) | MODIFY | No new labels required: toy cites `ss:s06-ca`, Burnside step cites `prop:s06-galois` (proof); M1/M4 *may* add `ex:s06-toy`, `lem:s06-burnside`, docstrings switch only after merge. | OVERVIEW §6.1 "labels exactly as in the stage tex" — mandatory new labels would conflict for remote M WPs. |
| A22 (min) | ACCEPT | X0 worktree list complete (incl. L10a, L14, L17); B edges `X1→{L1,L6,L7,L14}`; Mermaid includes L5b, L14, X2, L17, L18, L8c, L6c; `{…}(green)->L11/L16` written out. | — |
| A23 (min) | ACCEPT | Mixed scenario defined (+1–2 runs, ≈ +10–15 min); lead time ≥ 1 stage, recommended start ≤ stage 03 so that the merge lands at the 04→05 boundary; risk 5 names the S02 E1-pair slot saturation. | OVERVIEW §4.3 O7 (round + pair = 3 slots). |

## Stage-04 audit items with an S06 side (relayed by the coordinator)
| S04 id | verdict on the S06 side | what S06 does |
|---|---|---|
| A1 (crit) | ACCEPT | S06-L8a registers `Hyp.HsiehGor` with the §0 signature (generic base ring `A`, `TB`, module `M`); `Hyp.HsiehEta` is not in Lean. |
| A2 (maj) | ACCEPT (S06 picks up the η-principle) | New early WP **S06-L17** `CommAlg/EtaPrinciple.lean` (sonnet +bf, stacked on L2, `int2`); rev.-1 lines 38/180/209 removed; export edge `L17 docstring ⇒ S04-M6`. |
| A12 (min) | ACCEPT | One E1′ per project: S04's runs first; S06's E1′ (now on L5b) only if S04's did not decide the cell (§5). |

## Cross-stage items (not applied here; owners apply them)

**X-1. Stage 05 (`stage-05.md` §0 seam, S05-L6/L6F/L8; owner: stage-05 reviser).**
(a) Replace the bullet "**Files and namespace.** … `NewOldData.bEquivDualQuot (hℓ : IsGorensteinWith A S ℓ) : D.𝔟 ≃ₗ[S] Module.Dual A
(S ⧸ D.𝔞)` (+ `aEquivDualQuot`), and (c)." by the verbatim copy of the `lean` block "Interface `if:s06-lemD` — FIXED signature
(rev. 2)" in `stage-06.md` §0, preceded by: "Quoted from `stage-06.md` §0 rev. 2. The duality isos are `A`-linear (Mathlib v4.35
has no `Module S (Module.Dual A M)`); `S`-equivariance is `bEquivDualQuot_smul`, the map is `bEquivDualQuot_apply`." One-line
form: `NewOldData.bEquivDualQuot (D : NewOldData A S) {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) : D.𝔟 ≃ₗ[A]
Module.Dual A (S ⧸ D.𝔞)` (+ `_apply`, `_smul`).
(b) `NewOldData.split_iff` now has a concrete signature: `theorem NewOldData.split_iff [IsDomain A] (𝔞 𝔟 : Ideal S) : (∃ c : A,
c ≠ 0 ∧ algebraMap A S c ∈ 𝔞 ⊔ 𝔟) ↔ (𝔞 ⊔ 𝔟).map (Algebra.TensorProduct.includeRight : S →ₐ[A] FractionRing A ⊗[A] S) = ⊤`
(no `tf_*` hypotheses needed). S05-L6 builds the `split` field with it.
(c) S05-L8 row: "`bEquivDualQuot` ⇒ `H[𝔞] ≃ T'`" → "`bEquivDualQuot` (A-linear) + `bEquivDualQuot_smul` (T-equivariance) ⇒ `H[𝔞] ≃
T'`".
(d) Job names: `s06-eint1` → `s06-int1` (early lane), `s06-egate-1` → `s06-gate1-1`, "`s06-int1` of stage 06" in scenario B stays;
the announcement is the outbox file `<UTC>_s06-early-handover.md`, and the merge is done by the **global master at a stage
boundary** (recommended 04→05, i.e. before S05-X1), not by a stage master (stage-05 §0 states 1–2, l. ~307, ~452, ~476).
(e) S05-L6F (fallback) must write the full rev.-2 block incl. `_apply`/`_smul`; `NewOldData` is in `CommAlg/Gorenstein.lean`
(S06-L1); `S` need not be local.

**X-2. Stage 04 (`stage-04.md`; owner: stage-04 reviser).**
(a) §0.4 row `Langlandscape.Hyp.HsiehGor`: replace "(… one signature, over abstract `Λ`, `I`, `T`, `λ : T →ₐ[I] I`, via
`CommAlg.IsGorenstein`, the same text in both plans)" by "(registered by stage 06, S06-L8a, file `Hyp/HsiehGor.lean`; signature
`def Langlandscape.Hyp.HsiehGor (A TB M : Type*) [CommRing A] [CommRing TB] [Algebra A TB] [AddCommGroup M] [Module TB M] :
Prop := CommAlg.IsGorenstein A TB ∧ Nonempty (M ≃ₗ[TB] TB)`; the eigenline clause of `thm:s04-Gor` follows by Lemma S)".
(b) D-eta (iii) and S04-M6: replace "the η-principle Lean WP is owned by stage 06 (`CommAlg/EtaPrinciple.lean`, early lane,
stacked on S06-L2); … "maths only (M6)" if stage 06 does not take the WP" by "the η-principle Lean WP is **S06-L17**
(`CommAlg/EtaPrinciple.lean`, `EtaPrinciple.congruenceIdeal_eq_span_pairing`, early lane, stacked on S06-L2)". S04-M6 acceptance:
"TEXCHK; the statement text equals the docstring of `Langlandscape.CommAlg.EtaPrinciple.congruenceIdeal_eq_span_pairing`
(S06-L17), checked by the stage master at merge (not an input of the WP); if S06-L17 is not yet drafted, the M6 text is the
reference and S06-L17's docstring copies it." Drop the clause "if stage 06 does not take the WP, status stays `\sttoprove`".
(c) §5 (l. ~329): "the stage-06 E1′ (on S06-L5a) is not triggered if this one decides it" → "the stage-06 E1′ (on **S06-L5b**) is
not triggered if this one decides it".
(d) S04-L14a / int3 spec: registers only `Hyp.{HidaControl, HsiehCR}` (+ `MordLambdaFree`, `InvLimExact` where the S04 plan puts
them); no `Hyp/HsiehGor.lean`, no `Hyp/HsiehEta.lean` in any S04 spec line (already so in the working-tree draft; keep).
(e) Ownership: `congruenceIdeal`, `IsGorenstein`, `IsGorensteinWith` = S06-L1 (`CommAlg/Gorenstein.lean`); every Lean statement
using them (`Hyp.HsiehGor`, η-principle) = stage 06. Stage 04 has no Lean file importing `Langlandscape.CommAlg.*`.

**X-3. `tools/check_wp.sh` (owner: S02-X1).** Already done in S02-X1 (`ok = re.search(r's[0-9][0-9]-', doc) is not None`).
Stage 06 makes **no** tools edit (rev.-1 X0 step removed) and only checks the widened regex on its base. No change to stage 02.

**X-4. OVERVIEW (owner: global master).**
(a) §7 table, S06 wall: "3.5 h ± 1.0" → "2.2 h (1.6–2.9) with early lane; 2.6 h (1.8–3.4) cold"; in the provisional sentence
"S06 1.7 / 2.3 h" → "S06 2.2 / 2.6 h". S04 Lean column: "`Hyp.HidaControl`, `Hyp.HsiehGor/Eta`" → "`Hyp.HidaControl`, `Hyp.HsiehCR`
(`HsiehGor` registered in S06; `HsiehEta` not in Lean)"; S06 Lean column add "η-principle (from S04), `Hyp.HsiehGor`".
(b) §2 (or §6): add the early-lane rule "a Mathlib-only early lane of a later stage (S06 CommAlg) runs at priority 3 on
`impl/s06-int<k>` off a clean `impl/s06-early`; the **global master** merges `impl/s06-early` into `wip-implementation` at a stage
boundary after its gate and Fable audit; the aggregator lines go in that merge commit; the next stage's `int1` is its merge gate"
(stage-06 Q1).
(c) §4.3: no grammar change needed (early lane uses `int<k>`/`gate<m>`; in-stage continues the numbering).
(d) §5.2 strand table S04–S06 row: add "one E1′ per project: S04-L6 first, S06-L5b only if S04's did not decide the cell".
