<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Stage 06 launch note (step 0: final pass before launch)

Status: **binding amendments to `stage-06.md`** (brief s06-common rule 2: this note wins where they differ). Written 2026-11-15
≈ 00:55–01:05Z by the S06 step-0 planner (Opus), read-only on `wip-implementation` 46ccec41…4a92a44d, `impl/s06-int1` 9d5e3153,
the `abhijit/*` heads, `conceptd/acc-b34-1`. Nothing was built. Status words: *green* = passed a TITAN/CONCEPTD round (sha cited);
*merged* = on `wip-implementation`; *draft* = on a branch, no round yet.

## 0. Scenario and job ids
We are in the **mixed scenario**: most of the early lane (L1–L3) was merged at 1a4c740 (green in s03-int1-1), and the rest (L4, L5a, L6,
L6b, L7, L10a, L13, L14, L17) is in the first in-stage round now. The stage master has already numbered in-stage jobs from
`s06-int1-1` (outbox 20261115T005304Z). **So job ids follow scenario B:** `s06-int1…`, early full gate = **`s06-gate1-1`** (the plan's
"gate2"), `s06-final-1`. The early-lane L18 Fable audit was never run: it **is merged into L12** (one Fable audit, both checklists,
in parts, §5).

## 1. WP state (≈ 01:00Z)
| WP | state | where / evidence |
|---|---|---|
| X0, XM0 | superseded | early lane ran on Abhijit's node (batches 1–3); chapter package `abhijit/s06-math` had its own writer |
| X1 | **in progress** | maths merged 2b1b8a45; T1 merged ee257154; Lean X-merge = `impl/s06-int1` (job s06-int1-1 sent); `code/results/s06/`, `talk/slides/s06-{defect,caveats}` stubs, HYPOTHESES placeholders: **not yet** |
| X2 | partly | CommAlg PrintAxioms rows + 9 `.titan/s06_*_axioms.lean` in aa153656 / 9d5e3153; Defect/Hyp part to do |
| L1 Gorenstein, L2 LemmaS, L3 NewOld | **merged, green** | 1a4c740 (s03-int1-1, 52/52 std); `Tests/S06/Gorenstein.lean` merged |
| L4 ThmE | green (acc. build 2026-11-14 20:37Z, TITAN; again acc-b34-1) | `abhijit/s06-l4` 4ac6651 ⊂ fc94c35; in s06-int1 |
| L5a DVR | green (acc-b34-1, 2/2) | e525beb ⊂ fc94c35; in s06-int1 |
| **L5b LemmaG** | **not started** (no `LemmaG.lean` on any branch) | E1′ trigger fails (Lean-hard cell decided by S04 E1′) → plain WP, §5 |
| L6 TraceForm, L6b Burnside, L7 Squeeze, L14 TwoByTwo | green (acc-b34-1: 2/2, 4/4, 1/1, 8/8) | 9fdecab, 2498613, 8b62a15, 842e7e1 ⊂ fc94c35; in s06-int1 |
| L10a Toy | green (acc-b34-1, 21/21) | 4f1e828 ⊂ fc94c35; in s06-int1 |
| L13 BaseChange, L17 EtaPrinciple | green (acc. build 20:37Z, TITAN) | `abhijit/s06-l13` d2c96f1, `s06-l17` 85e1815; in s06-int1 (8ee8be7c, 4f3bd8a0) |
| conversion of the 9 merged files | **in s06-int1-1** | aa153656 (header, `module`, public/private split): first build as modules, Burnside/DVR/BaseChange/Toy at risk |
| L6c | not started | §5: run (cheap) |
| L8a Setting + 9 Hyp | **in progress** | `impl/s06-l8a` (4d11e957 = base + *unconverted* `abhijit/s06-l13`, see A9) |
| L8b, L8c, L9a, L9b, L10b | to do | stack on the L8a skeleton (§5) |
| L11 / L12 / L15 / L16 / L18 | to do | L18 ⊂ L12 |
| M1–M4, M7, M8 | **merged** | `abhijit/s06-math` d8b08ab in 2b1b8a45 (`chapters/s06/s06-m{1,2,3,4,7,8}.tex`); M8 (optional) done |
| M6 | **merged**, verdict **GAP** | `litnotes/s06-m6-levM.md` (34a9730): CONFIRMED for `M = 1`, repairs R1–R5 for `M > 1` |
| M11 | **merged** | `litnotes/{hi86a,hi86b,hsieh2017,ko}.md` (a4d9b4d) |
| M5 | **in progress** (local) | `impl/s06-m5` (merges of s06-math, s06-m6 only); main.tex has 9 undefined refs (`prop:s06-levM`, `rem:s06-minus1`) until M5 |
| M9, M10 | to do | `impl/s06-m9` empty; M9 needs M5 |
| C1–C4, C6, C7 | to do | no `code/python/langlandscape/defect/`, no `results/s06/` |
| C5 | branch only | `impl/s06-c5` empty |
| H1 | drop (§5) | — |
| T1 | **merged** | `talk/slides/s06-thmE.tex` (ee257154) |
| T2, T3 | to do | `talk/main.tex` already has `\IfFileExists` hooks |
| AW-L1…L13 (early) | not run | covered by L12 part 1 (§5) |

## 2. Amendments vs `stage-06.md` (binding)
**A1 — exported names: the §0/§1 rows hold, with these additions/deviations** (all *verified* by reading the files):
- `CommAlg/Gorenstein.lean`: §0 block exact (l. 47 `IsGorensteinWith`, 52 `IsGorenstein`, 55 `ann`, 58 `congruenceIdeal`, 65
  `NewOldData`, 126 `NewOldData.split_iff`, 174/193 `of_algEquiv`, 201 `isGorenstein_iff_cyclic`); extra: `mem_ann` (84), `ann_anti`
  (90), `mulDual` (+`_apply`, `_apply_apply`), `IsGorensteinWith.{bijective,eq_zero_of_forall,exists_eq}` (107–118).
- `CommAlg/LemmaS.lean`: `ℓ` implicit, `hℓ`, `μ` explicit: `LemmaS.theta hℓ μ` (36), `trace_theta_mul` (39), `theta_unique`,
  `theta_mem_ann_ker`, `ann_ker_eq_span` (71), `ann_ker_restrictScalars_eq_span`, `trace_theta` (88), `congruenceIdeal_eq_span` (99).
- `CommAlg/NewOld.lean`: §0 names exact; every decl takes `{ℓ} (hℓ)` (and `hb`) explicitly, `D` from the section variable with
  `[IsDomain A] [IsNoetherianRing A] [IsLocalRing A]` (l. 129). Helpers `quotLift`, `idealSubtype`, `dualQuot`(+`_bijective`),
  `toDualB`, `exists_section_b`, `exists_retraction_b`, `ann_eq_of_inf_eq_bot`.
- `CommAlg/SubQuot.lean` (stage 05) and `Comparison/XIso.lean:98 xiso_of_gorenstein` consume `split_iff`'s **RHS form** (`hsplit`),
  not the `NewOldData.split` field: L12 item (10) diffs against these two consumers.
- `ThmE.lean`: §1 names + `ThmE.lam D lam' : S →ₐ[A] A := lam'.comp (mkₐ A D.𝔞)` (l. 34), `eta_eq_c_mul_of_isGorenstein D hℓ lam'
  hS'` (150); all identities have the form `congruenceIdeal (lam D lam') = D.𝔟.map (lam D lam') * congruenceIdeal lam'`.
- `DVR.lean:180 ThmE.eta_eq_c_mul_of_dvr (D : NewOldData 𝒪 S) (hS : IsGorenstein 𝒪 S) lam'`, `[IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]`.
- `BaseChange.lean:125 LemmaS.congruenceIdeal_baseChange hℓ μ [IsLocalHom (algebraMap A A')]` (instance **unused**, kept for the fixed
  signature: watch the unused-instance linter in the warning count; if it fires, L15 drops it, consumer L9b only); extra
  `IsGorensteinWith.of_surjective`, `IsGorensteinWith.baseChange`, `theta_baseChange`, `liftEquiv_tmul_apply`.
- `EtaPrinciple.lean:84 congruenceIdeal_eq_span_pairing` exactly as the L17 row (`hm₀` as an `↔` with `span A {m₀}`).
- `Squeeze.lean:42 squeeze P [IsLocalHom P] h𝔱 hPh hP`; `TraceForm.lean:59 eq_one_of_trace_mul_eq ρ hsurj σ …` and
  `Burnside.lean:118 surjective_groupAlgebra_of_absIrred f [IsLocalHom f] ρ hirr` share the surjectivity form
  `Function.Surjective (MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G ((Units.coeHom _).comp ρ))` (see A5).

**A2 — `Hyp.LambdaJL` actual signature** (`Hyp/LambdaJL.lean`, non-module, Mathlib-only imports):
`LambdaJL (D M p : ℕ) (Λ TGL TB) [CommRing ×3] [Algebra Λ TGL] [Algebra Λ TB] (genGL : LambdaJLGen → TGL) (genB : LambdaJLGen → TB)
(newIdeal : Ideal TGL) : Prop := ∃ φ, (Surjective φ ∧ T/U/dia/Π clauses) ∧ RingHom.ker φ.toRingHom = newIdeal`. So L8c/L9a take
**`(Dq M p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB) (hJL : Hyp.LambdaJL Dq M p Λ T TB genGL genB D.𝔞Λ)`**
(name `Dq`, not `D`: `D` is the `Setting`); only surjectivity and the kernel are used (as `hypotheses.tex` l. 205 says). `[Algebra Λ TB]`
is an extra binder of `gor_new`.

**A3 — no stage-04 `Hyp.HsiehGor` exists** (grep of `Langlandscape/`, `LanglandscapeTests/`: none); stage 04 defined
`Hyp.HidaControl` (`Hyp/HidaControl.lean`, schematic, definite side, mod `p^s`). L8a creates `Hyp/HsiehGor.lean` with the §0 text
**unchanged** (cross-stage row 12: byte-identical with the stage-04 quote).

**A4 — `Defect.Setting` changes (owned by stage 06 only, no foreign quote; L8a writes them):**
1. *Specialisation as an instance:* add the parameter `[Algebra I 𝒪]` and replace the field `P` by `abbrev Setting.P : I →+* 𝒪 :=
   algebraMap I 𝒪`; keep `P_surj : Function.Surjective (algebraMap I 𝒪)`. Reason: `𝒪 ⊗[I] D.R` (L9b, `KimOta`, `HidaControlGL2`) needs
   `Algebra I 𝒪`; a `P.toAlgebra` `letI` in statements is the instance-glue risk 9. `isLocalHom_P` from
   `IsLocalHom.of_surjective` (`RingTheory/LocalRing/RingHom/Basic.lean:116`, needs `Nontrivial 𝒪` = from `IsDomain`).
2. *λ_F factors through the new quotient:* replace `lamΛ : T →ₐ[Λ] I` by **`lamΛ' : (T ⧸ 𝔞Λ) →ₐ[Λ] I`**; define
   `Setting.lam' : D.R ⧸ D.𝔞 →ₐ[I] I := (AlgHom.liftEquiv Λ I (T ⧸ D.𝔞Λ) I D.lamΛ').comp D.quotient_baseChange.toAlgHom` and
   `Setting.lam := lam'.comp (Ideal.Quotient.mkₐ I D.𝔞)`. Then `lam = ThmE.lam (D.newOld h) D.lam'` holds by `rfl` (A4.3), which L9a needs
   for `ThmE.eta_eq_c_mul_of_isGorenstein`. Without it `𝔞 ⊆ ker λ` is not in the data and `η^B_F` cannot be formed.
   `quotient_baseChange := (Algebra.TensorProduct.tensorQuotientEquiv I T I D.𝔞Λ).symm` (explicit args `S T A`, `Quotient.lean:96`).
3. *`OldDecomp` without dependent-type transport:* state `Hyp.OldDecomp D` as the **conjunction of the `NewOldData` fields for
   `D.𝔞`, `D.𝔟` plus `Module.Free I (D.R ⧸ D.𝔟)`** (not `∃ N : NewOldData, N.𝔞 = D.𝔞 ∧ …`), and add
   `noncomputable def Setting.newOld (h : Hyp.OldDecomp D) : NewOldData I D.R` with `𝔞 := D.𝔞`, `𝔟 := D.𝔟` definitionally
   (`@[simp] newOld_𝔞 : (D.newOld h).𝔞 = D.𝔞 := rfl`). This avoids `S ⧸ N.𝔞` vs `S ⧸ D.𝔞` casts (S04 lesson 3).
4. *Weight-k new/old data:* `cor_fixed` applies `ThmE.eta_eq_c_mul_of_dvr` to a `NewOldData 𝒪 (𝒪 ⊗[I] D.R)`; base change does
   **not** preserve `inf_eq_bot`/torsion-freeness, so this must come from a hypothesis. It is the Lean content of
   `Hyp.HidaControlGL2` (control for `T′` and `𝔟` at `P`, tex step (3)): the `NewOldData` fields for `D.𝔞.map includeRight`,
   `D.𝔟.map includeRight` in `𝒪 ⊗[I] D.R`, plus `Module.Free 𝒪 (_ ⧸ _𝔟)`; same conjunction shape and a `Setting.newOldAt` def.
   The identification with `T_k(N)_𝔪` is docstring only (not representable on abstract data). `cq` specialises by
   `Ideal.map_map` (no hypothesis).
5. `ResidualBurnside D := Function.Surjective (MonoidAlgebra.lift I (Matrix (Fin 2) (Fin 2) I) G ((Units.coeHom _).comp D.ρ))`
   **literally** (= `TraceForm` `hsurj` = `Burnside` conclusion), so that L8b is a direct application and L6c is one line.

**A5 — module status.** Every new `Defect/*.lean` and `Hyp/{9 new}.lean` imports only Mathlib, `CommAlg.*`, `Defect.*`, `Hyp.*`. All
are `module` **iff `Hyp/LambdaJL.lean` is a module**; it is not (only importer: the root, `Langlandscape.lean:22`). **New WP S06-MODH
(stage master, mechanical, ~3 min): convert `Hyp/LambdaJL.lean` to the module layout** in the L8a skeleton round (its own commit;
lean.md "a conversion is its own WP"). Then all S06 Defect/Hyp files are modules (brief rule 4). If MODH fails the round, only
`Defect/{Gorenstein,Main,Corollaries}.lean` stay non-module.

**A6 — the GL2TF-free grep** (§0) is extended to the 9 files of s06-int1; the L8a/L9 files import `Hyp.*` by design and are
not in the list.

**A7 — job ids**: §0 (scenario B numbering); TITAN spec of the Defect round = §3.2 block verbatim + `S06-L5b
Langlandscape/CommAlg/LemmaG.lean` if drafted + `AXIOMS .titan/s06_l5b_axioms.lean`.

**A8 — cross-stage-consistency** (rows 12, 13, 15, 16, 35): all *ok* for S06 as shipped; row 13's stage-05 quote is satisfied (see
A1); no open S06 flag. OVERVIEW §7 wall (2.2/2.6 h) stays.

**A9 — L8a base.** `impl/s06-l8a` merged the *unconverted* `abhijit/s06-l13`. When s06-int1-1 returns, the writer **merges
`impl/s06-int1~1` (= aa153656 + spec-free)**, not the abhijit heads, so that every CommAlg import is a module (plain `git merge`,
no rebase; brief rule 10). If int1-1 is red, merge the fix letter's `~1`.

## 3. `Hyp.HidaControlGL2` vs HACS `GL2.Literature.HidaEns32` (diamond normalisation)
*Facts.* HACS `code/hacs/lean/GL2/Literature/Hida.lean`: `Iw p = ℤ_[p]⟦T⟧`, `γ = 1+p ↦ 1+T`, `Pk p k = (1+T) − (1+p)^k` (l. 19, Hida ENS
p. 250 "P_k = (1+X) − (1+p)^k"); `HidaEns32` (l. 54) = (3.3 b) as a ring iso `h/(P_k) ≃+* hk k`, guards `5 ≤ p`, `p ∣ N` (level
`N₀p`), and an extra `k ≡ a mod p−1`. Ours (`plan/staged/stage-06-integral-defect.tex` §`ss:s06-setting` l. 33–38): on the **GL₂
side Λ acts by classical diamonds and `P_k = ker([u] ↦ u^{k−2})`**; the definite side uses adelic diamonds, inverse to the
classical ones, with `P^ad_k = ker([u] ↦ u^{2−k})` (stage 04 D1); `Hyp.LambdaJL` encodes the inverse as
`φ ⟨d⟩_GL * ⟨d⟩_B = 1` (X1 erratum). `T`, `𝔟`, `I_F`, `P` of `Defect.Setting` are on the GL₂ side.
*Verdict.* `HidaControlGL2` lives entirely on the GL₂ side, so **our inverse-diamond convention does not enter it** (it enters
only through `LambdaJL` in `gor_new`). But HidaEns32 is **not** a drop-in: (i) HACS's `Pk p k` (character `γ ↦ γ^k`) is our
`P_{k+2}` if read literally against our `u^{k−2}`; whether Hida ENS twists the Λ-action so that his `P_k` is weight `k` is
**unverified** (survey §4(ii)); (ii) HidaEns32 is at level `N₀p` (`p ∣ N`); ours is `T_k(N)_𝔪`, `p ∤ N = qM`, via
p-stabilisation and (P2); (iii) it is for the whole cuspidal ordinary algebra, not `T′`, `𝔟`. **The statement needs no change in
Lean** (it is over abstract `P`, A4.4); **the docstring must pin the normalisation.** Exact sentence for `Hyp/HidaControlGL2.lean`:
> Normalisation: `P = algebraMap I 𝒪` is an arithmetic point of weight `k ≥ 2` for the GL₂-side Λ-structure of `T` (classical
> diamonds, `P_k = ker([u] ↦ u^{k-2})`, `ss:s06-setting`); the definite side's adelic diamonds (`P^ad_k = ker([u] ↦ u^{2-k})`) enter
> only through the inverse-diamond clause of `Hyp.LambdaJL` and are not used here. The cited source is Hida [Hi86b, Cor. 3.2
> (3.3 b), p. 250] at level `N₀p` with `P_k = (1+X) − (1+p)^k`, plus p-stabilisation `T^ord_k(Np)_𝔪 ≅ T_k(N)_𝔪` and (P2); the
> matching of Hida's `P_k` with ours (weight shift `k` vs `k − 2`) is not verified, and HACS's `GL2.Literature.HidaEns32` is not a
> substitute for this hypothesis without an explicit bridge (`plan/hacs/HACS-LEAN-HYP-SURVEY.md` §4(ii)).

## 4. Hypothesis registry (rows written by the stage master from L8a's report; no vacuous instances)
Collisions: **none by name** (grep of `Hyp/`, HYPOTHESES.md, `hypotheses.tex`). Overlaps to state in the rows:
`HidaControlGL2` ≠ stage-04 `Hyp.HidaControl` (definite, mod `p^s`, schematic); `HsiehGor` and `Hyp.X.iso` both cite Hsieh Thm 4.5
(different content: Gorenstein + `M ≅ T_B` vs the comparison iso; `xiso_of_gorenstein` is the bridge); `HsiehGorFull` and
`Hyp.X.iso` both cite Helm Cor 8.11; `HsiehCR` stays unconsumed (its row already says so); `OldDecomp`/`HidaControlGL2` share
Hi86b Thm 3.1/Cor 3.2 with HACS `HidaEns31/32` (row note only). `hypotheses.tex` l. 556–575 (planned table) becomes the M10 source.
| new `Hyp.*` | used by (planned decl) | instance (L10b) or reason | status |
|---|---|---|---|
| `HsiehGor Λ TB M` | `Setting.gor_new` → `defect_formula` | toy `TB = ℤ_[p]`, `M = TB` (`isGorenstein_self`) — satisfiable, not vacuous | open, cited (Hs Thm 4.5) |
| `OldDecomp D` | `Setting.newOld`, `defect_formula` | toy Setting from L10a (`Λ = I = ℤ_[p]`, `T = Toy`), via `TensorProduct.lid`; else reason | open, maths (M2 `lem:s06-decomp`) |
| `HsiehGorFull D` | `defect_formula`, `cor_fixed` (via `IsGorenstein.baseChange`), `cor_allweights` | toy, from L10a + `IsGorenstein.baseChange` | open, cited |
| `FreeRankTwo D` | `Defect.galois` | reason: needs a Galois rep with Chebotarev data; a toy (trivial `G`) makes the trace clause vacuous → **forbidden**, write the sentence | open, cited |
| `ResidualBurnside D` | `Defect.galois` | **discharged from abs. irreducibility by L6c** (`residualBurnside_of_absIrred`), status "proved modulo `IsIrreducible` of the residual rep" | proved (conditional) if L6c green |
| `TamSpec D` | `defect_formula` | toy (`t = 0`, `tq = ⊤`) only if not vacuous for its shape; else reason | open, maths only |
| `HidaControlGL2 D` | `cor_fixed`, `cor_allweights` (A4.4) | optional toy with `𝒪 = I`, `P = id`; else reason | open, cited (docstring §3) |
| `KimOta D` | `defect_formula` (∨), `cor_fixed` | reason: KO Thm 1.1 needs GL₂ Galois deformation data | open, cited |
| `KimOtaRT D` | `defect_formula` (∨) | reason as `KimOta`; docstring: **inclusion only**, `M = 1` confirmed by M6, `M > 1` per decision D1 | open, cited |
Every row: Lean name with arguments, file, label (`s06-…`), source page, `used by`, discharge plan "cited, post-hackathon" (or
"maths"), and the `LambdaJL` row's "Used by" updated to `Setting.gor_new`, `defect_formula`.

## 5. Remaining schedule (now ≈ 01:00Z; target final gate ≈ 03:15Z, closure ≈ 03:30Z, far inside 12:00/14:00Z)
**Critical path:** s06-int1-1 (+ ≤ 2 fix letters for the module conversion, 7–15 min) ∥ L8a statements (opus, ≈ 01:15Z) →
**int2-1 = L8a skeleton one-file compile check + MODH** (S05 lesson 1; ≈ 01:25Z) → L8b, L8c, L9a, L9b, L10b drafts stacked on the
skeleton, 5 writers in parallel (≈ 20 min) → int3-1 + letters (R ≈ 3–4 × 7) → **gate1-1** (≈ 02:30Z) → L12 last part + M9 delta →
L15 + int4 (≈ 15) → **final-1 TITAN + CONCEPTD cross-check `s06-final-1x`** (≈ 03:15Z) → X3 closure.
| lane | WPs (model) | start → done (Z) | notes |
|---|---|---|---|
| L-core | L8a (opus, running) → L8c, L9a (opus +pf), L8b, L10b (sonnet +bf), L9b (opus +pf), L6c (sonnet) | 01:00 → 02:30 | all 5 writers get this note + A4; rescue writer for L9a only if int3-1 has > 10 errors (S04 lesson 9) |
| L5b | LemmaG (sonnet first + 1 opus fix, model-selection Lean-hard prior; off path) | 01:05 → 02:00 | leaf; if not green by gate1, **drop and register** (`lem:s06-G` stays `\stproved`, `\leanplanned`) |
| Lean audit | **L12 part 1** = L18 checklist + L12 items 1, 2, 7, 8, 10 on the CommAlg layer, on the green s06-int1 sha (fable); **part 2** items 3–6, 9 on int3 Defect/Hyp; **part 3** delta on gate1 | 01:20 / 02:10 / 02:35 | fixes L15a/b in-stage (S04 lesson 10, S05 lesson 7: last part before or at gate1) |
| AW | AW-L8a, AW-L8c, AW-L9a, AW-L9b (opus, 6 min each, parallel to the next round) | per green | early AWs covered by L12 part 1 |
| M | M5 (opus +pf, running; applies D1) → M9 Fable chapter audit (incl. "M5 step (4) = M6 verdict") → M10 (sonnet) | 01:00 → 02:45 | slack ≈ 30 min |
| C | C1 (opus +pf) ∥ C5 (opus +pf) → C2, C3, C4 (opus), C7 (opus) → C6 → AW-C1/C4/C5/C7 | 01:05 → 02:35 | C7 `(13,7,4)…` are `M = 1` cases (M6-confirmed) |
| T | T2 after M3 (merged) + C2, C3, C6; T3 after C7 + D1 | 02:35 → 02:55 | T3: `q ≡ −1` only for `M = 1` (unless D1 = adopt) |
| X | X2 Defect part (haiku) with the int2/int3 specs; L11 aggregator lines; X3 | — | HYPOTHESES rows (§4) at gate1 |
**Optional items.** M8: done (merged). L6b, L14: green, keep (merge with the stage). L6c: **run** (10 min, turns `ResidualBurnside`
into a conditional discharge). L5b: run as above, drop if late. H1: **drop and register** (HACS is in `code/hacs/` now, but it has no
Betti-side `coker(Ψ*Ψ)` computation; T4 Betti side stays open in the closure).
**Experiment strands: none.** E1′ on L5b is not triggered (Lean-hard decided, S04); the only undecided cell (LaTeX hard single
comparison) has no clean candidate left (M1–M4, M7 are merged; M5 is on the M path and depends on the M6 corrections; M10 is routine).

## 6. Open decisions for Fabian (default in brackets; work proceeds on the default)
- **D1 (`q ≡ −1`, M6 GAP).** M6 (`litnotes/s06-m6-levM.md`): (Lev_M) CONFIRMED for `M = 1`; for `M > 1` step (4) is false as worded
  (Σ⁻ ≠ ∅); repairs R1 (level `M = N(ρ̄)·M₀`, one-way map), R2 (Σ⁺ := P_ρ̄), R3 (`U_ℓ`, `T_p` matching), R4 (full Σ⁻-new algebra,
  sign caveat at ℓ ≡ −1), R5. Adopt R1–R5 in M5 as corrected (Lev′_M)? [**M5 writes `prop:s06-levM` with R1–R5 applied, every
  repaired step `\provisional`; `\stproved` only for `M = 1`; T3 and `if:s06-defect` state `q ≡ −1` for `M = 1` only;
  `KimOtaRT` docstring says the same**]
- **D2 (`Defect.Setting` shape, A4.1–A4.5).** Accept the changes to the §0 rev.-2 `Setting` block (instance `[Algebra I 𝒪]`, `lamΛ'`
  on `T ⧸ 𝔞Λ`, conjunction-shaped `OldDecomp`/`HidaControlGL2` with `newOld`/`newOldAt`)? No foreign stage quotes `Setting`.
  [yes]
- **D3 (MODH).** Convert `Hyp/LambdaJL.lean` to a module (A5)? [yes, stage master, own commit]
- **D4 (L5b).** Run Lemma G as a plain WP, drop if not green by gate1? [yes]
- **D5 (HACS).** Port `HidaEns32` as the cited antecedent of `HidaControlGL2`? [no; docstring cross-reference only (§3), post-hackathon]
- **D6 (H1).** Drop the T4 Betti side? [yes; registered in the closure]
- 01:16Z lesson candidate (lean.md): `A ⧸ J ≃ₐ[R] B` parses as `A ⧸ (J ≃ₐ[R] B)` (⧸ binds looser than ≃ₐ); always parenthesise `(A ⧸ J) ≃ₐ[R] B`; →ₐ unaffected (s06-int2e-1).
- L12 part-2 checklist (global master 01:20Z): cor_allweights docstring + chapter \\lean pointer must not claim the ord-formula at P′ unconditionally: either add the non-vanishing (newform) hypothesis or say "needs 𝔠 ≠ 0 at both points (newform condition), not assumed here"; module docstring of Corollaries.lean already says so; check the theorem docstring and the chapter.
- L12 part-2 checklist: Hida P_k normalisation second-reader item (L8a reading: Hida P_k = our P_k; HACS HidaEns32 = our P_{k+2}?).
- M10 final pass: mathematics/report/hypotheses.tex hand-written counts (l.113), 'Projected hypotheses' section and date line are stale after the S06 rows (registry worker 01:27Z); ResidualBurnside 'discharged' is conditional on absolute irreducibility.
- T3 brief items: q ≡ −1 claim stated for M = 1 (stpmc) [+ F1 only if Fabian lifts]; H3 honest caveat (F4: 5 non-vacuous t = 2 cases with equality, all N(ρ̄) > 1 = evidence in the open region, F1 numerically untested); [Hs] sign line already in s06-caveats.tex (FD); trivial primes (BKM). T1 fix: Thm E(iii) DVR half is formalized (CommAlg/DVR.lean eta_eq_c_mul_of_dvr) → \stformal. C7: covered by F4 supplement.
- T-track binding (global master 01:35Z): any talk claim that defect_formula / thm:s06-defect is formalized must read "formalized modulo registered hypotheses, including the Galois half (Hyp.FreeRankTwo)"; toy instances of HidaControlGL2/KimOta/KimOtaRT = consistency (non-vacuity) only, not evidence. T3 q ≡ −1 sentence: "q ≡ −1 for M = 1, and for squarefree M with ρ̄ unramified at all ℓ | M; open for N(ρ̄) > 1".
- M10 final pass: wherever the chapter states the Eisenstein (h) ⊇ 𝔠_q regression (seed C4(i)), add 'O_v a DVR / S_m Gorenstein' (C2: fails in 5/46 non-DVR rows at p = 2, 3); cite results/s06/C4i.json as partial (131/319).
- Closure deviations/hygiene (global master 01:5xZ): linter.overlappingInstances suppressed locally on 3 headlines (cor_fixed, defect_formula, cor_allweights); the overlap is inherent in Defect.Setting's IsDomain + IsLocalRing binders; post-Mathathon fix: restructure the Setting binders.
