# Adversarial audit of the revised stage-04 plan (`stage-04.md` @ 562488f)

Auditor: Opus, 2026-11-14. Read only. Inputs: `briefs/replan-s02-06.md` (A–F + structure), `OVERVIEW.md` (§4.3, §4.4, §5,
§6.1, §9), `stage-04.md`, `audits/stage-04-replan-notes.md`, `plan/staged/stage-04-lambda-adic.tex`, `SPLIT.md`, the old
plan (`7ce2a3e:plan/implementation/stage-04.md`) + `audits/stage-04-{muse,resolution}.md`, `stage-02/03/05/06.md` (working
tree), `runs/s01.md`, the s01 closure, `experiments/SUMMARY.md`, `EXPERIMENT_PROTOCOL.md` §9, `lean/Langlandscape/` and the
frozen Mathlib `/home/janosch/data/mathlib4_v4350`.

**Verified, no finding:**
- Every stage-1 declaration in §0.3 exists with the stated file and namespace. I grepped 53 names: `Up`, `UpHom`,
  `Up_apply`, `UpHom_single`, `towerMap/Push/Pull`, `Up_comm_push/pull`, `Utower_succ_le`, `heckeT(Hom)`, `dcSet`, `conjSub`,
  `brandtPairing_heckeTHom`, `pushforward`, `trace`, `levelMap`, `normMap_pushforward`, `ZX(dual)`, `brandtPairing`,
  `evalPairing_perfect`, `normMap(_bijective)`, `brandtModule(TrivEquiv)`, `K0`, `K1`, `Iw`, `varpi*`, `diagOneP`,
  `K1_mul_varpi_mul_K1`, `exists_varpi_inv_mul`, `reps_indep`, `diag1p_reps`, `relIndex_K1_succ`, `Utower`, `U0q`, `U1`,
  `Utower_antitone`, `finite_XB_Utower`, `card_XB_Utower`, `deltaElt`, `diamondAct(_mul/_free)`, `Gam_eq_bot_of_le_U1`,
  `rightMulXB`, `diamond(_apply_eq_diamondAct)`, `Up_comm_diamond(_self)`, `Up_comm_Tl`, `Up_comm_rightTranslate`.
- `Up` is defined only at `Utower`, which is correct. The `check_wp.sh` docstring test is `'s01-' in doc`, also correct.
- The Mathlib names exist: `LinearMap.eventually_isCompl_ker_pow_range_pow` (`RingTheory/Artinian/Module.lean:308`),
  `Module.free_of_flat_of_isLocalRing` (`RingTheory/LocalRing/Module.lean:299`), `LinearMap.IsPerfPair`,
  `Submodule.linearProjOfIsCompl` and `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]`. There is no `IsLocalRing (MonoidAlgebra …)`.
- The definitions in D-e are sound. `nilPart` is a submodule because `p^k M` is `T`-stable. `⨅ range T^n` is the ordinary
  part for f.g. `ℤ_p`-modules: Krull on the topologically nilpotent summand. The projection is natural for equivariant maps,
  so `ordPart_exact` holds.
- The Lean shapes of L6, L7 and L8 match the tex: `Kpp ⧸ K1(s+1) ≅ ker(Δ_{s+1}→Δ_s)` has order p, `Δ_s` is cyclic for
  p ≥ 3, and `v_p|X_s| ≥ 2s−2` follows from the `card_XB_Utower` formula.
- §9 lessons D1–D6 all appear as steps. The `.titan/` files are only on the integration branch. The WP count of 40 adds up.
  The critical-path sum is arithmetically 167.

## Findings

**A1 (crit; §0.2 D-eta, §0.4, S04-L14; cross-stage 06).** D-eta moves the η-principle out because "stage 04 must not stub
another stage's definitions". `Hyp.HsiehGor` and `Hyp.HsiehEta` still stay in S04-L14, and their statements need exactly
those definitions: `thm:s04-Gor` says "`T_m` is Gorenstein", and `η^B_F = λ(Ann ker λ)` is a congruence ideal. The plan
leaves two options open, and both break the ownership rule:
- import `CommAlg/Gorenstein.lean`, which S06-L1 owns and which is not scheduled before S04-int3; or
- inline a second Gorenstein/η notion in `Hyp/*.lean`.

Stage 06 expects the shape `Hyp.HsiehGor` "via `CommAlg.IsGorenstein`": S06-L8a derives `gor_new` from it, and stage-06
risk 4 adds a bridging lemma (+1 round) otherwise. The shape is fixed in neither plan.
*Fix:*
- Preferred: move the Lean registration of `Hyp.HsiehGor` to S06-L8a, which already writes 8 `Hyp/*.lean` files. Stage 04
  keeps the maths (M4).
- Drop `Hyp.HsiehEta` from Lean entirely. Stage 06 states it is not used in Lean. Keep `thm:s04-etaB` as cited maths only.
- S04-L14 then registers only `MordLambdaFree`, `HidaControl`, `HsiehCR` (+ `InvLimExact`).
- Alternative: make S06-L1 green in the stage-06 early lane (Mathlib-only, planned to run during 02–05) a hard input of
  S04-L14, with a stub of the S06 §0 signatures on `impl/s04-int3` only (SORRIES row).
- Either way, write the exact signature of `HsiehGor` once, over abstract `Λ`, `I`, `T` and `λ : T →ₐ[I] I`, and use the
  same text in both plans.

**A2 (maj; §0.2 D-eta, M6; cross-stage 06).** The η-principle Lean WP is **orphaned**. Stage 06 does not pick it up:
- `stage-06.md` l. 38 still says "stage-04 η-principle … import[s] it, never define[s] it";
- the export edge "`L1(green) => stage-04 eta-principle`" (l. 180) and the Mermaid node `S04[stage-04 eta-principle]` (l. 209)
  still point at a stage-04 WP that no longer exists;
- no S06 WP proves "free rank one over Gorenstein + perfect equivariant pairing ⇒ congruence ideal = self-pairing". S06-L2
  `LemmaS.congruenceIdeal_eq_span` is the algebraic core, not this statement.

The tex marks the principle `\sttoprove`, "Lean-friendly". M6 also has an unsatisfiable acceptance. It asks for a
"statement text identical to the stage-06 tex import block". That block is `if:s04-etaB`, a cited Hsieh statement, not the
commutative-algebra lemma. It also makes the stage-06 tex an input, outside the remote-WP condition (§6.1).
*Fix:* stage 06 adds an explicit early-lane WP, `CommAlg/EtaPrinciple.lean`, stacked on S06-L2 (opus, Mathlib-only). If it
does not, both plans record "maths only (M6)" and the tex status stays `\sttoprove`. Delete the stage-06 lines 38/180/209
references. Change M6 acceptance to "statement = the docstring of the stage-06 η-principle WP, or the M6 text is the
reference".

**A3 (maj; §0.2 D-Λ, §0.4, L14).** `Hyp.MordLambdaFree` has no statement. D-Λ says Λ is not defined in Lean. A legitimate
`def … : Prop` (lean.md) then has two possible forms, and both are wrong:
- an existential or abstract `Λ`, which is unfaithful and easily vacuous;
- the finite-level compatible-basis form, which is provable, is L13's stretch target, and is therefore not a hypothesis.

The D-lim device fixes this cheaply.
*Fix:*
- In L13, define `Ordinary.Lam` as the subring of compatible families in `Π s, MonoidAlgebra ℤ_[p] (Δ s)`, the same pattern as
  `Mord`. Give `Mord U` its `Lam`-module structure from the levelwise diamonds.
- State `Hyp.MordLambdaFree U : Prop := ∃ r, Nonempty (Mord U ≃ₗ[Lam] (Fin r → Lam)) ∧` the control isomorphisms.
- The docstring cites `Lam ≅ 𝒪[[1+pℤ_p]]` (tex: "`Λ = lim 𝒪[Δ_s]`") and gives the non-vacuity reason.
- Because it needs `Mord`, the Prop belongs to int4 with L13, not to int3 (see A5).

**A4 (maj; §0.2 F-e, L10/L12/L13, M10; cross-stage 05).** The `ZMod (p^m)` fallback is not stated honestly. F-e says "tower
statements over `ZMod (p^m)` for every m" but leaves three gaps:
- It does not say what L12/L13 state under F-e. `Mord` and `lim_exact` are ℤ_p objects, and `ord_compatible_basis` needs
  ℤ_p as well.
- It does not say how labels change: the closure, HYPOTHESES and the `\leanplanned → \stformal` upgrades in M10.
- Stage 05 (S05-L7, `ordPart (G.X s ⊗ ℤ_p)`) consumes the ℤ_p objects.

Taking `(h : HasOrdDecomp T)` as an ordinary argument is fine for abstract lemmas. On the tower instances, an undischarged
`h` would be an unregistered hypothesis.
*Fix:* define F-e as follows:
- the ℤ_p tower theorems L10/L12/L13 take `(hdec : Hyp.PadicOrdDecomp …)`, a registered, true, provable `def … : Prop`
  owned by L3/ext;
- the `ZMod (p^m)` instances are proved unconditionally;
- the docstrings say "formalized modulo `Hyp.PadicOrdDecomp`";
- M10 must not mark `thm:s04-control`(a) `\stformal` without qualification;
- the closure and the stage-05 seam note state it.

**A5 (maj; §2, §3, §4).** The placement of gate-1 contradicts itself:
- Prose and the §3 table: X3 runs at ≈ t 100 on the core, before int4 (≈ 105, L13).
- DAG: X3 requires `L14` green, and `L13→L14(d)`.
- Critical path: `int4 + int4b → X3`.
- §3: L14 is in int3, but it needs L13's `Mord` signature, which only arrives in int4.

As written, the Fable Lean audit L16 may never see `Ordinary/Limit.lean`, `MordLambdaFree` or `InvLimExact`, the riskiest new
files.
*Fix:* split L14 into L14a (int3: `HidaControl`, `HsiehCR`) and L14b (int4 with L13: `MordLambdaFree`, `InvLimExact`). Then
choose one of:
- (a) gate-1 after int4b, which matches the summed path; or
- (b) gate-1 on the core plus an L16b Fable pass on L13/L14b before L17.

Delete the other version.

**A6 (maj; §2 DAG).** `{L1..L12,L14,L15a,L15b green} -> X3` makes the ext WPs L15a/L15b preconditions of the early gate.
§1 says they "may continue into stage 05/06", and risk 6 says their interface may not fit `brandtModule`. A red ext WP would
block X3, L16 and the critical path.
*Fix:* remove L15a/L15b from the X3 precondition. They join gate-1 if green, otherwise they are carried over. The
`HidaControl` schematic fallback (Q3) is decided at int3 by the stage master.

**A7 (maj; §2 critical path, range).** The sum 167 is arithmetically right but optimistic, and the range is off-centre.
- (i) Only 15 min of TITAN rounds are costed for a 4-deep serial stack of hard opus WPs (L1 → L8 → L10 → L13). Under OVERVIEW
  §4.4 (upper half for hard WPs; 2–3 rounds each, pipelined), L10 is green at about int3b (≈ 95–100) and L13 at about
  int4b/c (≈ 120–130). That gives ≈ 175–185 min.
- (ii) The low end of 2.0 h is unreachable. L13's draft cannot end before ≈ t 100, and the fixed tail after it is ≥ 52 min,
  so the minimum is ≈ 2.5 h.
- (iii) The F-e switch is decided at int3 (≈ 80), after L13 has started (≈ 75) on L10's `ℤ_[p]` signatures. That rework is
  not costed.

*Fix:*
- Split L13 into L13a, an abstract ℕ-indexed inverse-system layer: compatible-family submodules, lifting along surjective
  transitions, `lim_exact`, `Lam`. It is Mathlib-only and goes in W1/int1 with no deps. L13b instantiates it on the Ribet
  systems (int4). This takes L13 off the critical path.
- Decide F-e at int2.
- Restate the estimate as 3.0 h, range 2.5–3.8 h, or show the shortened path after the split.

**A8 (min; §0.2 D-lim, L13).** "split exactness + five lemma" is the wrong argument for surjectivity of `eH1_{s+1} → eH1_s`.
The right one is the snake lemma: `ker(B_{s+1}→B_s) = I·B_{s+1}` (I = augmentation ideal of `ker(Δ_{s+1}→Δ_s)`, by control)
maps onto `I·C_{s+1}` because α is surjective. This needs control at **both** levels U and `U0q U`, and needs α to be
Δ-equivariant. *Fix:* reword D-lim. Make L10 deliver control for `U` and `U0q q U`, and add `alpha_comm_diamond` to L12.

**A9 (min; §0.2 connectivity; cross-stage 02).** The alternative argument `Hyp.SA ∧ Hyp.HS` does not give `BGConnected` in
the stage-02 Lean. There, (i) ⇒ (iii) is `BGConnected_of_surj (hBT : Hyp.BTtree q)`, and it also needs `IsQAdmissible`
(`NrdSurj`). `BGConnected` itself takes `hU : IsQLevel`. *Fix:* L12/L13 take only `∀ s ≥ 1, BGConnected … (isQLevel_Utower …)`.
State the SA route as a corollary that also lists `Hyp.BTtree` and `NrdSurj`, and only if stage 02 exports it.

**A10 (min; §0.3 upstream, L12; cross-stage 03).** Stage 03 exports `Ribet.ribet_exact` over ℤ (deg-0 parts). "With
coefficients" exists only for `ihara_ker_const`. L12 assumes "over ℤ and with coefficients". The `UpAt`-equivariance of
`s0_*`/`s1_*` is also new: stage 02 commutes `heckeT g` for g away from q, but `UpAt` is a stage-04 object (L9). *Fix:* make
the L12 goal include `ribet_exact_baseChange` (flat `ℤ → ℤ_[p]`) and `UpAt_comm_s0/s1` (stage-02 commutation at `g = ϖ`).
Cost +1 round and name it in risk 4.

**A11 (min; §4 partial exports; cross-stage 05).** S05-L7 needs `if:s04-ekills`(a) at Brandt level (`e ℤ_p[S_s]⁰ = e ℤ_p[S_s]`)
and expects it in `Ordinary/EKills.lean`. Stage 04 puts the abstract lemma there and the instance in `Tower.lean` (L10,
int3), and lists only (d) as a partial export. *Fix:* name the exported instance and its file, add (a) to the partial
exports, and send the seam note to stage 05. FYI for stage 05: Weil vendoring is dropped (D-lim), so S05-L3's "unless stage
04 vendored Weil" resolves to the toy.

**A12 (min; §5 strand; cross-stage 06).** The conditional E1′ on S04-L6 has several problems:
- The auditor is "opus, alternating with fable", but OVERVIEW §5.2 says E1 → fable audit, because opus is in the pair.
- "Reference S04-L6 (opus, merged)" runs in priority-1 int rounds with normal relays, while the challenger gets a
  priority-2 slot. That is not the equal regime, and "`S04-L6@sonnet`" puts a model name in the id.
- L6 → L9 → L12 has only ≈ 10 min slack (65 vs 75), so it is not clearly off the critical path.
- The plan says "≈ 9 Lean-hard WPs", but there are 11.
- S06 names the same cell (E1′ on S06-L5a).

*Fix:*
- Run both strands as `s04-l6-a/b` with neutral refs and verbatim relays, and have fable audit them.
- Say "the S06 E1′ is not triggered if S04's E1′ decides the cell".
- Correct the count.

**A13 (min; §1 models, brief A).** Fix-round budgets are missing on M5, T1, T2 and H1. C1 and C4 are `hard` code with a
"budgeted" opus fix. §5.1 has no class for hard code; use `opus (+1 planned opus fix)`, as S06-C1 does.

**A14 (min; §6 remote, OVERVIEW §6.1).** The table lacks the required column "local fallback model". M1 and M3 cite
`if:s02-*`/`if:s03-*`. With the acceptance "no undefined refs" in `standalone-s04.tex`, those citations need the s02/s03
chapters merged at the base sha, which contradicts "M WPs can run any number of stages ahead". *Fix:* add the column, cite
foreign interfaces as `\texttt{if:…}` text (or state "base sha after stage 03 merged"), and drop the stage-06 tex input
from M6 (see A2).

**A15 (min; §0.5 carry-overs).** Two `runs/s01.md` maths corrections are missing:
- the mass level-change factor-2 wording, used directly by M2's factor-2 paragraph;
- `prop:s01-relations`(c), the direction of `R_g`.

The new `Up_comm_Tl'` (no free `hfin`) is the lemma L12 should cite. *Fix:* add both rows and the name.

**A16 (min; §4 gates).** The `check_wp.sh` docstring test covers only `theorem`/`lemma`, including test files (OVERVIEW §4.3).
Public `def`s such as `ordPart`, `HasOrdDecomp`, `ordProj`, every `Hyp.*`, `Kpp` and `UtowerP` are not machine-checked.
*Fix:* add "docstrings of public defs/structures" to the L16 checklist. Tell writers that test theorems need `s04-` docstrings.

**A17 (min; §2 waves, Mermaid).**
- W2 lists L12, which stacks on L9, also in W2.
- L3 is in W3 (t ≈ 55), but its spec line is in int2 (≈ 55), when it cannot yet be drafted. It needs only L1/L2, so it belongs
  in W2.
- M9 appears in W4 and in W5.
- The Mermaid graph omits X2, M7, `L15b→X3` and the upstream edges.

*Fix:* make the waves consistent with the edge list.

**A18 (min; §0.2 coefficient ring, labels).** The tex works over `𝒪_E`, but the plan fixes `ℤ_[p]` without calling it the
specialisation E = ℚ_p. *Fix:* say so in §0.2, in the L10/L12/L13 docstrings and in the M10 status upgrades.

**A19 (min; L5).** `UpStar := heckeTHom … (varpiDiag⁻¹)` must use `(localEmbedGL d p hp (varpiDiag p))⁻¹`, as `Up` does, and
needs its own `relIndex ≠ 0` lemma (the `hfin'` of `brandtPairing_heckeTHom`). `U_p^* = ⟨p⟩_M U'_p` involves the idele
`p^{(p)}`, so the exponent sign of `⟨p⟩_M` should be fixed numerically by C3 before L5 is drafted. *Fix:* add both to the
L5 goal and let C3 run first (it is quick).

## Counts and verdict
crit 1 (A1); maj 6 (A2–A7); min 12 (A8–A19). Cross-stage: A1, A2 (stage 06 must edit l. 38/180/209 or add a WP), A4, A11
(stage 05), A9 (stage 02), A10 (stage 03), A12 (stage 06 strand).

**Verdict: NOT READY — revise.** Conventions A–F and the structure are largely followed, and the stage-1 inputs are accurate.
A1–A7 must be fixed before the final pass:
- the ownership of `HsiehGor`/`HsiehEta` and of the η-principle, agreed with stage 06;
- a faithful `Hyp.MordLambdaFree`;
- an honest F-e fallback;
- consistent placement of gate-1 and L14;
- no ext WP gating X3;
- a recalibrated critical path, best done with the L13a split.

The minor findings can be fixed in the same pass.
