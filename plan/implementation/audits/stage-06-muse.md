# Audit of stage-06.md — Implementation Plan for the Integral Jacquet–Langlands Defect

Date: 2026-11-14 — Auditor: Muse Spark Open (automated check against OVERVIEW.md, stage.tex, SPLIT.md)

Scope: checks (1)–(8) as requested. Only defects reported. Each finding: `F<n>` severity location problem fix.

---

## (1) WP schema completeness

- **F1 major `stage-06.md:73,75-104` WP schema — `inputs` field uses free-form text not stage-tex labels** Several WPs list inputs as `tex`, `tex L1`, `seed C4(i)`, `KO §3`, `M4 proof`, `S03-C1 Smith form` — these are not stage-tex labels (`def:s06-…`, `if:s06-…`) nor `GL2TF.*` nor vendored sources as required by OVERVIEW §1 `inputs (stage-tex labels such as def:s01-brandt …)`. Mechanical check of label existence impossible.
  *Fix:* Normalize every input to a `label:s06-…`/`if:sNN-…` or explicit `GL2TF.*`/`Vendor/...`; put bibliographic references in a separate `sources` note.

- **F2 minor `stage-06.md:89` S06-L1 `outputs` lists `CommAlg/Gorenstein.lean` but §0 states the file is shared with S04-L10** The WP claims exclusive creation while §0 says “whichever stage runs first creates the file”. Either ownership is ambiguous or two WPs will race to create the same path, violating “WP branches change only their track directory plus files explicitly assigned”.
  *Fix:* Make S06-L1’s output `CommAlg/Gorenstein.lean (primary owner)` and add a conditional dependency `S04-L10 (if merged first, L1 becomes read-only)` with a coordination gate in `§3 Entry conditions`.

- **F3 minor `stage-06.md:94` S06-L6 `deps` = `L1 (+ L8 for Defect/Galois)`** The parenthesised conditional dependency is not a parseable `deps` entry per OVERVIEW schema (`deps.` must list WP ids). The DAG block (`stage-06.md:131`) omits the `L8 → L6` edge entirely.
  *Fix:* Split S06-L6 into `S06-L6a TraceForm.lean (deps L1)` and `S06-L6b Galois (deps L8)` or list `S06-L8` explicitly in deps and add `L8 → L6` to DAG.

- **F4 minor `stage-06.md:97` S06-L8 `outputs` concatenates 9 files in one cell** OVERVIEW “one topic per file: `Langlandscape/<Area>/<Topic>.lean`” — bundling `Hyp/{8 files}.lean` into a single WP hides 8 distinct Lean declarations and makes `LCHK` non-atomic. Size estimate 60 min agent wall for 8 hypotheses + `Defect.Setting` is optimistic.
  *Fix:* Split into `S06-L8a Setting` and `S06-L8b Hyp registrations` or keep one WP but list each `Hyp/*.lean` as separate output row and raise estimate to 90–120 min or mark `hard`.

## (2) Cited labels vs `stage.tex`

- **F5 major `stage-06.md:89,109` citations `def:s06-rings (η)`, `§ss:s06-ca`, `def:s06-{rings,ctam}`** `stage.tex` defines `def:s06-rings`, `def:s06-ctam`, `def:s06-tam`, `ss:s06-ca` etc. Citations use brace expansion `def:s06-{rings,ctam}` and plain `tex L1`, `tex; if:s01-{targets,hecke}` which are not resolvable labels. No WP cites `if:s01-hecke` with exact string (stage.tex exports `if:s01-hecke`, `if:s01-targets` etc.) but `stage-06.md:76` writes `` `if:s01-{targets,hecke}` `` — grep for `if:s01-hecke` in stage-06.md returns 0 literal matches; only the expanded form appears. Tooling that greps labels will report missing.
  *Fix:* Expand all shorthands to literal labels in inputs, e.g. `if:s01-targets, if:s01-hecke, if:s04-Mord`.

- **F6 minor `stage-06.md:70,121-123` external WP citations `S01-M0`, `S01-X1`, `S01-T0`, `S01-C0`, `S01-H0`, `S03-C1`, `S03-C5`, `S04-L9`, `S01-L13`** None of these labels appear in `stage.tex` nor in `SPLIT.md` interfaces; their existence cannot be verified from the attached context. `S01-M0` is described as “mathematics skeleton” in OVERVIEW §3.2 but no WP with that id is defined in `stage-06.md`.
  *Fix:* Attach or reference the stage-01/03/04 plan files that define these ids, or restate them as `if:s01-…` interfaces rather than WP deps. For audit purposes mark them `external — unverified`.

- **F7 minor `stage-06.md:75` S06-M1 inputs `lem:s06-{S,G,D}`, `thm:s06-E`** Shorthand with braces; literal labels `lem:s06-S`, `lem:s06-G`, `lem:s06-D`, `thm:s06-E` all exist in `stage.tex:154,161,170,186` but the literal string `lem:s06-{S,G,D}` does not match. Same for `cor:s06-{fixed,allweights}` in S06-L9b.
  *Fix:* Same expansion as F5.

## (3) Dependency DAG — acyclicity, completeness, critical path

- **F8 critical `stage-06.md:131-135` DAG completeness — missing edges for WPs that use another WP’s output**

  | consumer | uses output of | current deps | missing edge |
  |---|---|---|---|
  | S06-M6 (second reader) | S06-M5 (`minus1.tex`) | `M5` ✅ but DAG has `M5→M6` correct | — |
  | S06-C3 (T4 Hecke) | S06-M7 `prop:s06-betti` (Betti formula `det Ψ*Ψ`, `δ`) | `C1, S03-C5` | **`M7 → C3`** missing |
  | S06-C3 | S06-L9b/Cor allweights is cited as input `cor:s06-allweights` but not depended on; acceptable if cited-only | — | note |
  | S06-L6 `Defect/Galois.lean` | S06-L8 `Defect/Setting.lean` | `L1 (+ L8)` informal, DAG `L1→L6` only | **`L8 → L6`** missing (see F3) |
  | S06-L6b | S06-M4 proof of `prop:s06-galois` | `L6` only | **`M4 → L6b`** missing (table lists `M4 proof` as input) |
  | S06-L10 toy | S06-M1 toy example | `L4, L8` | **`M1 → L10`** missing |
  | S06-L14 `TwoByTwo.lean` | S06-M7 `prop:s06-betti(a)` | `S01-X1` | **`M7 → L14`** missing (optional but input cites it) |
  | S06-T1 | `thm:s06-E` (M1) and `L4` | `S01-T0` only | **`M1 → T1`, `L4 → T1`** missing |
  | S06-T2 | `thm:s06-defect` (M3) and `C2` numbers | `S01-T0, C3, C6` | **`M3 → T2`, `C2 → T2`** missing (description says numbers from `results/s06/*.json`) |
  | S06-C1 | `lem:s06-S` (L2) conceptually | `S03-C1, S01-C0` | borderline — if toolkit formalises Lemma S, add `L2 → C1` or clarify “uses statement only” |

  OVERVIEW §6: “a WP using an output of another must depend on it.”
  *Fix:* Add the edges above to both the `deps` column and the `DAG`/`graph LR` blocks. Re-toposort to confirm acyc.

- **F9 major `stage-06.md:131,160-162` DAG vs Waves inconsistency** Wave W1 lists `M6 (after M5)` as runnable in W1, but `M6 → M9` and `M9` blocks `M10`; wave text also puts `M1–M5,M7` in W0 and `M8` in W2 — yet DAG omits `M3→M9`, `M4→M9` edges (written as `{M1..M5,M7,(M8)}→M9` shorthand not expanded). The shorthand is ambiguous for tooling.
  *Fix:* Expand `{M1..M5,M7,(M8)}→M9` to explicit edges `M1→M9, M2→M9, M3→M9, M4→M9, M5→M9, M7→M9, M8→M9 (optional)` in the DAG text.

- **F10 major `stage-06.md:166-168` critical path claim is accurate in length but mischaracterises slack** Computed longest path (agent wall only, internal S06 edges) = 470 min: `L1(60)→L3(90)→L4(90)→L5(90)→L9b(60)→L11(30)→L12(50)` = 470. An equally long path `L1→L3→L4→L9a→L9b→L11→L12` (90+90 vs 90+90) ties, so the critical path is not unique. Text states “`L2 ∥ L3; L5 ∥ L9a; L6,L7,L8 ∥ L3–L4, each with ≥1h slack`” — but `L5` is on the critical path (zero slack), not parallel to `L9a`. `L5→L9b` vs `L9a→L9b` creates a join; delaying either delays `L9b`.
  *Fix:* State both tied critical paths; correct slack table: `L2` has 45 min slack vs `L3`; `L5` and `L9a` are both on/beside critical path (slack 0); `L6/L7/L8` have slack only until `L9a` is ready.

- **F11 minor `stage-06.md:166` merge-gate accounting** Critical path adds “7 merge gates ×10 ≈ 70 min” but the path `L1→L3→L4→L5→L9b→L11→L12` has 6 internal edges + final merge to `wip-implementation` = 7 gates, correct. However `L1` itself needs a gate after `S01-X1` if early-started on a stale `wip-implementation`; not counted. Also each `→` between S06 WPs is counted as 10 min, but OVERVIEW §2 “re-run acceptance check on merged result (for Lean: `lbuild.sh` of touched targets)” costs build wall (8–12 min per gate), not just 10 min agent wall. Underestimation.
  *Fix:* Count gates as `build wall` as well or state total wall = 470 agent + ~60–80 build for gates.

## (4) Acceptance checks — mechanical and sufficient

- **F12 major `stage-06.md:75-84` M-track `TEXCHK` is insufficiently mechanical** `TEXCHK(labels)` is defined as existence of `\label` in `mathematics/chapters/s06/*.tex`; it does not require `latexmk -pdf` exit 0 nor “no undefined refs” as mandated by OVERVIEW §1. Only `S06-X1` lists `latexmk exit 0`. All other M WPs would pass with a file that contains the label string but does not compile.
  *Fix:* Change every M WP acceptance to `latexmk -pdf mathematics/main.tex exit 0 && grep -c 'undefined references' ==0 && TEXCHK(labels)`.

- **F13 major `stage-06.md:80` S06-M6 acceptance `verdict CONFIRMED / GAP (gates T3 and the q≡−1 claim)`** The verdict is a human judgment by `fable` (model) on a mathematical argument (KO §3 matching of anemic vs full Hecke algebras, distinctness of Frobenius roots). No mechanical criterion (e.g. checklist of 4 points l.291–294 checked, page refs quoted) is given, so the gate “`q≡−1` claim only if M6 CONFIRMED” is subjective and can be gamed.
  *Fix:* Make acceptance a table of 4 check-boxes (level `N^+_{ρ,Σ⁺}N⁻` matches `M`; `P_{ρ̄}⊆Σ`; `U_ℓ` vs anemic algebra noted; Hensel distinctness cited) plus `fable` sign-off; failure = `GAP` blocks `if:s06-defect` export of the `q≡−1` clause.

- **F14 major `stage-06.md:111` S06-C3 acceptance `mismatch = finding, not failure`** The PYCHK table lists `ord_17 𝔠_3 = 1,1,1,1,2 (prediction; k≥28 stexp); mismatch = finding, not failure`. By definition the WP never fails, even if the computed length is wrong. This violates “Acceptance checks must be mechanical where possible … numbers equal a stated table” — here the table is a prediction, not a mechanical oracle.
  *Fix:* Split into `C3a compute table (always pass, record *computed*)` and `C3b compare vs prediction (record match/mismatch as separate finding field)`; make `C3a`’s PYCHK assert that the script ran, produced JSON with provenance, and `rk T'_{k,m}` is finite.

- **F15 major `stage-06.md:80,103,116` non-mechanical T/H acceptances** `S06-M7 TEXCHK` only; `S06-L12 verdict PASS` (Fable alone, no mechanical `lfile/lbuild` or `print axioms` re-check); `S06-H1 ≅ (T(1)_m/δ)² at k=12 (seed: (ℤ/17)²)` — seed value is illustrative, not a test oracle. No `lbuild`/`pytest` gate is defined for audit WPs M9, L12.
  *Fix:* M9: `audit script exit 0 + every listed fix has a commit`; L12: `lbuild rc 0 on wip-implementation && print axioms ⊆ {propext, funext, Classical.choice} && audit checklist PASS`.

- **F16 minor `stage-06.md:89-104` L-track `LCHK` lacks explicit `print axioms` coverage** Only `L4` lists “`#print axioms` std three”; other L WPs on the critical path (`L3` NewOld, `L9a` defect) also introduce new axioms risks (e.g. `Classical.choice` via `Module.Free` of quotients). OVERVIEW requires `grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide' empty` for every Lean WP (unless declared stub) — LCHK definition in `§0` says it includes this, but table rows just write `LCHK` without expanding, so a reviewer cannot tell whether the audit re-ran it on `wip-implementation`.
  *Fix:* Expand every L-row acceptance to `LCHK = lfile each && lbuild batch && grep sorries/axioms empty && (where noted) print axioms`.

- **F17 minor `stage-06.md:113` S06-C5 acceptance `py­chk: dim = q-new dim (JL check); η^B unit-equivalent under both weight choices`** The check “unit-equivalent” is not defined (units in `ℤ/p^m` vs `ℤ_p`); no tolerance for `p≥5` factor 2 is given, despite §0 warning about `w_x` vs `|Γ_x|`.
  *Fix:* State explicit assert: `assert dim_def == dim_new` and `assert (gram_det_w / gram_det_Gamma).unit?` with script `defect/gram.py --weight {w,Gamma} --check-units`.

## (5) Model choices vs difficulty

- **F18 major `stage-06.md:81` S06-M7 `hard` → `opus` vs `stage.tex` status `stproved` for Prop betti(a)** M7 claims “Prop betti (a), (c) proofs; (b) from Ihara's lemma + Dia89” as `hard` requiring `opus`. But `stage.tex:359` marks `(a) sttoprove (linear algebra … independent of T'_q/T''_q choice)` as routine linear algebra; assigning `opus` to a 75-min linear-algebra WP is overkill per OVERVIEW §5 “Pick the cheapest model that does not lengthen wall time” (critical path is Lean, not M7).
  *Fix:* Downgrade M7 to `routine` / `sonnet` with `muse` draft, keep `opus` only for M5 (conceptual) and M3 (hard control).

- **F19 minor `stage-06.md:75` S06-M1 `routine` vs `hard` content** M1 covers “Gorenstein/trace, Lemmas S (incl. base change), G, D(a)–(c), Thm E(i)–(iv), where each Gorenstein hypothesis is used, toy example” — this is the entire commutative-algebra foundation (6 lemmas/theorems). Tagging it `routine` (60 min, sonnet/muse draft) underestimates elaboration (quotient modules `S ⧸ 𝔞`, `Module.Dual`).
  *Fix:* Split M1 into `M1a Lemmas S,G,D (routine, 60)` and `M1b Thm E (hard, 90, opus)` or raise M1 to `hard`/`opus`.

- **F20 minor `stage-06.md:93` S06-L5 `routine` → `TBD (default: opus; sonnet if E2/E1 show it)`** Difficulty `routine` but model `opus` contradicts OVERVIEW §5 “routine Lean → sonnet, with muse fan-out” and “hard → opus”. Either difficulty is wrong or model is.
  *Fix:* If PID structure theorem plumbing is `hard`, change difficulty to `hard`; if truly `routine`, default to `sonnet`.

- **F21 minor `stage-06.md:104` S06-L14 `routine` → `muse` (verifier `sonnet`)** `muse` is cheapest per OVERVIEW cost order, but `muse` for Lean boilerplate is only sanctioned with a named verifier; this row correctly names `verifier sonnet`, so it complies, but the difficulty `routine` for a 2×2 matrix cokernel over a local ring is borderline `mechanical`.
  *Fix:* No fix needed or downgrade to `mechanical`/`muse`.

## (6) Resource limits (≤2 local Lean builds, ≤3 TITAN, ≤3 Claude agents)

- **F22 critical `stage-06.md:160-162` Waves violate ≤3 Claude agents** W0 proposes concurrent `X1, L1, L14, M1–M5, M7` = 9 WPs at once. OVERVIEW §4 “Stage parallelism: ≤3 Claude subagents per coordinator (Fable alone); a stage master runs ≤3 WP workers, each worker ≤2 opencode jobs.” Even with time-slicing, 9 parallel workers exceeds the limit by 3×. The “Mitigation: CommAlg core scheduled during stages 1–4 as background work” admits the violation persists during stages 1–4, competing with those stages’ own 3-worker budgets.
  *Fix:* Re-phase waves to ≤3 concurrent WPs: e.g. W0a `L1→L3` (2 workers) + `M2` (1 worker); W0b `M1,M3,M4` after L1 gate; state that background CommAlg work counts against the stage that is active at that time and requires global-master throttling.

- **F23 major `stage-06.md:165` Build batching vs ≤2 local Lean processes** Batch W1 “`+CommAlg.LemmaS +CommAlg.NewOld +CommAlg.TraceForm +CommAlg.Squeeze` (one process)” is 1 slot, compliant. But the plan also says “Slot 1 = critical path (L3→L4→L9a), slot 2 = lfile iteration of parallel leaves” while waves W1–W2 list up to 4 L WPs (`L2,L3,L6,L7`) plus `C1` building via `lbuild` — at least 2 concurrent `lbuild` would need 2 slots, leaving no slot for `lfile` iteration. Under `V` (vendored) each fresh worktree needs ~25 min build (OVERVIEW §3.2) — the “Mathlib-only so they build in any worktree right after S01-X1” claim is false under V.
  *Fix:* Annotate each WPs build wall as `P-only / V (+25 min first build)` and cap concurrent L builds to 1 `lbuild` + 1 `lfile` (2 slots total). Move `L13, L6b` to a background wave.

- **F24 minor `stage-06.md:103` S06-L11 `TITAN cand.` with `30 / 20 (TITAN cand.)`** OVERVIEW §4 “TITAN: ≤3 (`SLOTS=3`); jobs only via global master (`SendMessage` to TITAN, job id `sNN-<wp>-<n>`)”. No WP lists a TITAN job id, nor does the DAG reserve the 5–10 min coordination cost. Claiming “TITAN candidate” without a `titan/s06-…` branch violates §2 branch naming.
  *Fix:* Either remove TITAN tag (no file >5 min locally expected, per §2) or add explicit job `titan/s06-l11-b1` with `SLOTS=3` and count it against the ≤3 TITAN limit.

## (7) Mathematical or Lean-technical errors in WP descriptions

- **F25 critical `stage-06.md:30` Shared definitions `CommAlg/Gorenstein.lean` — trace vs `Module.Dual` encoding unsound for non-free `S`** The design `(i) IsGorensteinWith A S ℓ : S finite free over A and s ↦ ℓ∘ mulLeft s bijective` uses `Module.Dual A S := S →ₗ[A] A`. For non-local `A` this map is `S`-linear only if `S` is commutative (it is), but bijectivity is not equivalent to `S^∨` free of rank 1 over `S` when `S` is not local (e.g. `S = A×A` is Gorenstein but `ℓ = (1,0)` projection does not give an `S`-isomorphism). The stage’s `S = {(x,y): x≡y mod ϖ^t}` (L10) is not local; the definition will fail for it.
  *Fix:* Define `IsGorenstein A S := Module.Free A S ∧ ∃ (e: S ≃ₗ[S] Module.Dual A S)` or keep `IsGorensteinWith ℓ` but prove equivalence lemma and test on product ring toy.

- **F26 major `stage-06.md:30` Field-free encoding of `S_K` splitting** The encoding `∃ c ≠0, algebraMap A S c ∈ 𝔞 ⊔ 𝔟` with `𝔞 ⊓ 𝔟 = ⊥` is equivalent to `S_K = (S/𝔞)_K × (S/𝔟)_K` only when `A` is a domain and `S` is torsion-free over `A`. The WP lists it as “equivalent given 𝔞⊓𝔟=⊥ and torsion-freeness” but the Lean structure `NewOldData` in S06-L1 does not include `S` torsion-free as a field; without it the side lemma is false (counterexample `A=ℤ_p, S=ℤ_p×ℤ/p`).
  *Fix:* Add `S` torsion-free (or `Module.Free A S`) to `NewOldData` hypotheses, or prove the encoding under the actual hypotheses from `lem:s06-decomp` (which does give torsion-freeness).

- **F27 major `stage-06.md:92,186` Thm E(iv) “𝔠 principal ⇔ (Gor_{S′})”** `stage.tex:203` (Thm E(iv)) states `𝔠 ≅ fb ≅ S'^∨`, so `𝔠` principal in `S'` iff `S'^∨` is cyclic over `S'`, i.e. iff `S'` is Gorenstein — but this holds only when `S/𝔟` is `A`-free (Lemma D(c) hypothesis). The WP description in S06-L4 omits that hypothesis, making the Lean theorem statement `IsGorenstein A S' ↔ Principal (𝔠)` false without it.
  *Fix:* Add `Module.Free A (S ⧸ 𝔟)` (i.e. `S''` free) to the `ThmE.lean` (iv) statement and mirror it in the Lean docstring.

- **F28 major `stage-06.md:93` S06-L5 “Thm E(iii) DVR case (no hypothesis on S') + Lemma G (Nakayama over semilocal S)”** The proof cited in `stage.tex:172` for Lemma G assumes `S` finite over local `A` so semilocal; Nakayama over semilocal ring requires Jacobson radical condition, which Mathlib’s `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` does not provide for `S` semilocal (it is for `A` local). The WP underestimates Mathlib gap (stage-06.md:191 even flags it as Risk 3).
  *Fix:* Change difficulty to `hard` or split off a Mathlib-gap WP that proves `IsLocalRing` of each localisation of `S` and applies Nakayama there.

- **F29 major `stage-06.md:113` S06-C5 Hsieh weight vs `|Γ_x|` “unit-equivalent under both weight choices (p≥5)”** The WP asserts that `η^B` is unit-equivalent for `w_x = |Γ_x|/|±1|` vs `|Γ_x|`. This is false at `p=2` and misleading at `p≥5` when `M>1` and level `U` contains `-1` — the factor 2 is not a unit in `ℤ_p` for `p=2`, but the stage assumes `p≥5` so the claim is vacuously true. The real issue is whether Hsieh’s `B_N` (Atkin–Lehner twisted) vs `w_x δ_{xy}` gives the same congruence ideal up to `ℤ_p^×` — stage.tex S3 proves it does, but the WP’s acceptance “unit-equivalent under both weight choices” does not test `B_N`.
  *Fix:* Change acceptance to compare `gram.py --hisheh-weights` vs `gram.py --naive-weights` and assert ratio ∈ `ℤ_p^×` via `v_p(ratio)=0`.

- **F30 minor `stage-06.md:30` Notation `c ∈ 𝔞 ⊔ 𝔟`** In Lean `⊔` on `Ideal S` is sum of ideals, not supremum of submodules; `algebraMap A S c ∈ 𝔞 ⊔ 𝔟` is not well-typed (`c : A`, `algebraMap c : S`, `𝔞 ⊔ 𝔟 : Ideal S` expects `S`). Needs coercion `↑(algebraMap c) ∈ (𝔞 ⊔ 𝔟 : Ideal S)`.
  *Fix:* Fix notation in WP description to `algebraMap A S c ∈ (𝔞 ⊔ 𝔟 : Set S)`.

- **F31 minor `stage-06.md:111` S06-C3 formula `δ = 16 − 3^{2−k}T_3²`** For `k` even, `3^{2−k}` is not integral; the WP says “normalised” but does not give integral normalisation (`3^{k-2}δ = 16·3^{k-2} − T_3²`). PARI `mf` works integrally, so the formula as written will produce fractions and `length T(1)_m/(δ)` will be miscomputed.
  *Fix:* Write `δ := (q+1)² − q^{2−k}T_q²` in `ℤ_p`-normalised form `(q+1)² q^{k-2} − T_q²` divided by `q^{k-2}` as unit (since `q∤p`).

## (8) EXPERIMENT_PROTOCOL for stage 01

- **F32 minor `stage-06.md:4` Reference to `plan/implementation/EXPERIMENT_PROTOCOL.md` with no file attached** OVERVIEW §5 calibration “comes from `plan/implementation/EXPERIMENT_PROTOCOL.md` (stage-1 observational study)”. No `EXPERIMENT_PROTOCOL.md` was provided for audit, so coherence of stage-06 model choices (`TBD-after-S01 (default: sonnet)`) with experiment metrics cannot be verified. The plan correctly defers `TBD` but does not record where metrics are stored (`plan/implementation/runs/sNN.md` per OVERVIEW §2).
  *Fix:* Add a note “EXPERIMENT_PROTOCOL not attached; model defaults per OVERVIEW §5 used; to be replaced after S01 per §4” and ensure `runs/s06.md` will log wall/build times.

---

### Summary counts

- Critical: 3 (F8, F22, F25)
- Major: 13 (F1, F5, F9, F10, F12–F15, F18, F23, F26–F29)
- Minor: 16 (F2–F4, F6, F7, F11, F16, F17, F19–F21, F24, F30–F32)

*End of audit — no endorsements implied. All findings require revision of `stage-06.md` (and corresponding updates to `stage.tex`/`OVERVIEW.md` where noted) before implementation.*

