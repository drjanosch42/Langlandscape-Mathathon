# Adversarial audit of the stage-06 re-plan (`plan/implementation/stage-06.md`, revision 1 post stage 1)

Auditor: Opus, 2026-11-14, read only. Subject at `wip-plan` 0285aba. Read: `briefs/replan-s02-06.md` (A–F + structure),
`OVERVIEW.md` §4.3, §4.4, §5, §6.1, §9, `stage-06.md`, `audits/stage-06-replan-notes.md`, `plan/staged/stage-06-integral-defect.tex`,
`plan/staged/SPLIT.md`, the coarse plan (`7ce2a3e:plan/implementation/stage-06.md`) with `audits/stage-06-{muse,resolution}.md`,
`runs/s01.md`, `experiments/SUMMARY.md`, `stage-04.md`/`stage-05.md` (seams), `lean/Langlandscape/` (tree, `lakefile.toml`,
`Hyp/LambdaJL.lean`, `tools/{titan_batch,check_wp}.sh`, `Audit/PrintAxioms.lean`), and the frozen Mathlib
`/home/janosch/data/mathlib4_v4350` (to check the API named in §0).

## What holds (checked, no finding)
- Structure §0–§7 is as the brief requires. The WP table has the columns `model (+fix)`, `remote` and `TITAN round`, plus `early`.
  Muse and mistral are gone. Fable runs L12 ∥ M9. Lessons D1–D6 each appear as a step: L11 early gate, X2, the docstring
  check inside TCHK, rebasing after each round, the outbox, and no hints in relays. There is a final unseeded gate (L16), and
  the stage is stated launchable without Abhijit.
- Every `lem/thm/cor/prop/def/hyp/rem/conj/ss/if:s06-…` label the plan cites exists in the stage tex (checked by grep);
  `thm:s04-Gor` exists in the stage-04 tex.
- Existing project items are as claimed: `Langlandscape/Hyp/LambdaJL.lean` (`∃ φ : TGL →ₐ[Λ] TB`, surjective, `ker = newIdeal`);
  `tools/{titan_batch,check_wp,check_frozen,new_wp}.sh`; `check_wp.sh` hard-codes `'s01-' in doc` (l. 87); no `CommAlg/`,
  `Defect/` yet; stage-1 code `brandt.py`, `symn.py`, `pari.py`, `padic.py`, `results.py`.
- Mathlib API in §0 exists in v4.35: `Submodule.colon (N) (S : Set M)`, `bot_colon`, `Module.IsTorsionFree`
  (`Algebra/Module/Torsion/Free.lean:45`), `Module.free_of_finite_type_torsion_free'`, `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`,
  `Ideal.quotientKerAlgEquivOfSurjective`. The only "Gorenstein" is `GroupTheory/Focal.lean`.
- The DAG edge list has no cycle. The scenario-A critical-path sum is arithmetically right (104). So is B's (136). WP count 47/43 is right.
- Mathematics of `NewOldData`: the field-free `split` together with `inf_eq_bot` and `tf_*` is equivalent to the tex hypotheses
  of `lem:s06-D`. Part (a) needs only `tf_b`/`tf_a` and `split`, as the tex says. `IsGorensteinWith` (bijectivity of `s ↦ ℓ(s·)`)
  is "`S^∨` free of rank one over `S`". `congruenceIdeal` is `def:s06-rings`' `η(S,μ)`.

## Findings

### A1 — crit — §0 (`if:s06-lemD` shape), L3
**Problem.** The frozen export `NewOldData.bEquivDualQuot (hℓ) : D.𝔟 ≃ₗ[S] Module.Dual A (S ⧸ D.𝔞)` (and `aEquivDualQuot`)
does not elaborate in Mathlib v4.35, because there is no `Module S (Module.Dual A (S ⧸ 𝔞))` instance. Precomposition makes
`M →ₗ[A] A` a module only over `Sᵈᵐᵃ`: `instance … : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M')` in
`Mathlib/Algebra/Module/LinearMap/Basic.lean:109`, and `LinearAlgebra/Dual/*` adds no `S`-module instance. §0 declares this
signature FIXED, and says a change needs the stage-05 master's written OK. Stage 05 has already copied it verbatim (stage-05.md
§0, used by S05-L8). The L3 writer would have to invent an instance mid-WP, which might be a diamond-prone global instance,
and that would silently change the interface.
**Fix (before stage 05 freezes its import).** Fix one encoding in §0 and tell stage 05 in the outbox. Either:
(i) L1 owns a named, scoped instance in `CommAlg/Gorenstein.lean`, e.g. `CommAlg.dualModule : Module S (Module.Dual A M)` for
`[Module S M] [IsScalarTower A S M]` (via `Module.compHom` along `DomMulAct.mk`, `S` commutative), plus a simp lemma
`dualModule_smul_apply`. The signature names it explicitly (`open scoped CommAlg`).
Or (ii) make it `D.𝔟 ≃ₗ[A] Module.Dual A (S ⧸ D.𝔞)` together with an exported `bEquivDualQuot_smul : e (s • b) = (e b).comp
(LinearMap.mulLeft …)`. This is less elegant but needs no instance.
Option (ii) is safer for stage 05's `xiso_of_gorenstein`. Record the choice in `lem:s06-D`'s docstring form.

### A2 — maj — §1 L7 (squeeze)
**Problem.** The stated `squeeze` is false. Its hypotheses are: `I` a local domain, `𝔱 ≤ span {h}`, `P : I →+* 𝒪` with `𝒪` a
domain, `P h ≠ 0`, and `span (P '' 𝔱) ≥ span {P h}`. Counterexample: `I = ℤ_(p)`, `𝒪 = ℚ`, `P` the inclusion, `𝔱 = (p)`, `h = 1`.
All hypotheses hold, but `𝔱 ≠ (1)`. The tex step (5) uses `𝔡 ⊄ 𝔪_I ⇒ 𝔡 = I`, and that needs `P(𝔪_I) ⊆ 𝔪_𝒪`, i.e. a local
homomorphism to a local ring (an arithmetic specialisation `I → 𝒪_P` is one).
**Fix.** Add `[IsLocalRing 𝒪] [IsLocalHom P]` (or `P` surjective onto a local `𝒪`) to the L7 row and to `Defect.Setting`'s `P`.
Make L12 check it.

### A3 — maj — §0 (`Defect` layer), L8a
**Problem.** `Defect.Setting` as described consists of Λ, `I` finite free over Λ, an abstract finite free `I`-algebra `R`,
ideals `𝔞 𝔟`, `λ`, `G`, `Iq`, `ρ`, `P` and `t`. It has no Λ-algebra `T` and no identification `R ≅ T ⊗_Λ I` (`def:s06-rings`:
`R := T ⊗_Λ I_F`, `𝔞 := 𝔞 R`). `Hyp.HsiehGor` (stage 04, abstract finite flat Λ-algebra data) and `Hyp.LambdaJL` (over Λ:
`TGL →ₐ[Λ] TB`, `ker = newIdeal`) both live over Λ. So `Defect.Setting.gor_new : IsGorenstein I R′` cannot be derived from them
for an arbitrary `R`. One needs `R′ = R/𝔞 ≅ (T/𝔞_Λ) ⊗_Λ I`, i.e. right exactness of `⊗`, and then `IsGorenstein.baseChange`.
Without that field, either L8a fails, or the writer adds an unflagged hypothesis tying `R` to `T`.
**Fix.** Add to `Setting` the fields `T`, `[Algebra Λ T]`, `𝔞Λ : Ideal T`, `e : R ≃ₐ[I] I ⊗[Λ] T` and `𝔞 = 𝔞Λ.map …`, with the
`LambdaJL` data on `T`. Add the lemma `quotient_baseChange` (`(I ⊗ T) ⧸ 𝔞Λ.map ≃ₐ I ⊗ (T ⧸ 𝔞Λ)`; Mathlib has the tensor–quotient
equivalences) to L13 or L8a. Alternatively, answer Q3 with a `Hyp.HsiehGorI` over `I`. Either way this is design work: see A5(c).

### A4 — maj — §0 Hyp table, L9b (`cor_fixed`)
**Problem.** `cor:s06-fixed` uses that `T_k(N)_𝔪` is Gorenstein ([KO, Prop. 5.1(1)], citing Dim09) before it applies Thm E(iii)
over the DVR. Thm E(iii) needs (Gor_S) for the full algebra even in the DVR case. None of the 8 new `Hyp.*` states this
fixed-weight Gorenstein property, and the L9b row ("`Hyp.KimOta` + DVR case") does not say where (Gor_S) comes from. It must
either be derived (`HsiehGorFull` + base change along `P` + the control identification `T/P ≅ T_k(N)_𝔪`, which is not what
`HidaControlGL2` states) or become a hypothesis. Otherwise it ends up as a hidden extra argument, which is exactly what L12
item (3) is meant to prevent.
**Fix.** In the L9b row, name the source: derive it (state the extra control field), or register `Hyp.KOGorenstein`
(`[KO, Prop. 5.1(1)]`) as a 9th row. Update the §0 table, X1/L8a and the L12 checklist.

### A5 — maj — §1 model assignments (brief A / OVERVIEW §5.1)
**Problem.**
(a) M1 (full proofs of Lemmas S, G, D and Thm E (i)–(iv)) and M4 (Prop galois "in full") are "LaTeX hard (full proofs)" under
brief A, so they should be opus (+pf), not sonnet (+bf). SUMMARY gives LaTeX-routine as undecided, and M1 is the text of record
for the frozen interface and for every CommAlg docstring.
(b) L2 (Lemma S: build `θ` from the trace isomorphism; `ann (ker μ)` free of rank one) is labelled routine/sonnet. It is the
root of both spines, L2→L4→L9a and L2→L13→L8a. The E1 prior and OVERVIEW §5.1 say hard work on the critical path goes to
opus. Take L2 as hard, opus (+pf).
(c) L8a defines `Defect.Setting` and states 8 hypotheses faithfully to the tex (the A3 design). That is "conceptual (design,
interfaces)", so opus. Split it: L8a = Setting + Hyp statements (opus); L8c = `gor_new` (opus +pf).
(d) Several rows name no fix budget: L1, M6, M8, C7, H1, L11, L15, X3. "Every WP row names model + fix-round budget": write "—
(conceptual)" or the budget. L1 includes the nontrivial `split_iff` proof, so give it a planned fix.
(e) X1 (haiku) writes 8 HYPOTHESES rows with source and discharge plan. That is mechanical-with-meaning, so sonnet (+bf); compare
S02-X1 and S05-X1, which are sonnet.

### A6 — maj — §4 Gates and audits (OVERVIEW §5.3)
**Problem.** OVERVIEW §5.3 requires a WP-level audit (opus, or fable for adversarial work) before merge for every hard or
conceptual WP. §4 plans none: not for L1, L3, L4, L5a, L5b, L13, L9a, L9b, M2, M3, M5, M7, C1, C4, C5 or C7. The gap matters most
for the early lane. The CommAlg layer, including the frozen `if:s06-lemD` and `IsGorensteinWith`, is merged into
`wip-implementation` and consumed by S04-L10 and S05-L6/L8 stages before any Lean faithfulness review. L12 checklist items (1)
and (2) run only in stage 06, after two stages have built on the encoding.
**Fix.** Add an early-lane Fable Lean audit (`lean_audit.md`, about 6 min) on the `s06-egate-1` sha, with L12 items (1), (2)
and (7) plus the def/structure docstrings, as a precondition for the hand-over merge. Add opus WP audits (about 5–8 min each, in
parallel, off the path when stacked) for the listed WPs, and put them in the DAG and the times.

### A7 — maj — §1 L11, §2 critical path, §3.2 (internal contradiction / audit coverage)
**Problem.** L11 triggers `s06-gate-1` when L3, L4, L8a and L9a are green, but the scenario-A path has "int2b (L9b green) →
gate-1". On the actual trigger, the gate-1 sha that L12 audits may lack L9b (`cor_fixed`, `cor_allweights`), L10b (Hyp non-vacuity,
L12 item 6), L5a and L6b. L16 depends on all of L1..L10b, so WPs merged after gate-1 reach the final gate without any Fable
review.
**Fix.** Trigger gate-1 when all non-optional L WPs are green (L1–L5b, L6, L7, L8a, L8b, L9a, L9b, L10a, L10b, L13). Or add a
delta audit (Fable, about 5 min) for WPs merged after gate-1, before L16. Make the CP text and the L11 row agree.

### A8 — maj — §3.1 (spec file `.titan/spec-s06-eint1.txt`)
**Problem.** The line `S06-L3  Langlandscape/CommAlg/NewOld.lean          # (a) only in eint1` breaks the round.
`titan_batch.sh` skips only lines whose *first* token starts with `#` (l. 11, 20), then word-splits `rest` (l. 12). So `#`,
`(a)`, `only`, `in`, `eint1` become the modules `+#`, `+(a)`, … for `lbuild.sh`, and arguments of `check_wp.sh`. The whole
batched build fails, not just L3.
**Fix.** Put the comment on its own line (`# S06-L3: part (a) only in eint1`). Add to X0/X1 acceptance: "spec files have no
trailing comments; `awk '$1 !~ /^#/ && /#/'` empty".

### A9 — maj — §2 critical path and stage wall (brief F, OVERVIEW §4.4)
**Problem.**
(a) Scenario A uses the lower ends: 3 rounds at 8–10 min, L9a draft 20. §4.4 says R = 3–6, upper half for hard/conceptual. In
stage 1, hard opus Lean WPs took 45–80 min wall (runs/s01.md). The defect layer has 2 hard opus WPs stacked on the new A3 design.
(b) L9a "stacked on L8a/L8b" cannot start at X1+0. §0 gives no Lean signatures for `Setting` or the `Hyp.*`, unlike the CommAlg
layer, and X1 writes no signature stubs (S05-X1 step 6 does). That adds a serial L8a signature step of about 12 min.
(c) L15 is taken as 13 "incl. its TITAN round" per §4.4, and int3 8 is then added on top: a double count. It partly offsets (a).
(d) Scenario B drafts 17 Lean WPs at once, but the stage master may run at most 8 subagents (F12). So there are two waves,
+15–20 min.
(e) There is no cross-check. OVERVIEW §7 gives S06 as 3.5 h ± 1.0, and revision 1 gives 9 h × 0.25–0.35 = 2.3–3.2 h.
Scenario A (1.7 h) is 51 % below OVERVIEW §7 without explanation (§4.4 requires one above 50 %).
**Fix.** Recompute. A: X1 10 → L8a signatures 12 → L9a draft 20 → 4 rounds × 13 → gate-1 6 → L12 8 → L15 13 (incl. round) → L16 6
→ X3 5 ≈ **132 min ≈ 2.2 h (1.6–2.9)**. B: ≈ **2.7 h (1.9–3.5)** with two draft waves and 6 rounds × 13. State the cross-check and
ask the global master to update OVERVIEW §7 (or explain the gap by the early lane). Let X1 write `sorry` stubs with the declared
L8a signatures on `impl/s06-int1` only, listed in SORRIES (stage-05 pattern).

### A10 — maj — §5 (conditional strand E1′ on L5a)
**Problem.**
(i) In scenario A, L5a runs in the early lane. By the plan's own rule the strand is then "not triggered", so the argument about
slack in A is moot.
(ii) In scenario B, L5a feeds L9b (`cor_fixed`, `cor_allweights`), which the CP and L16 need. A strand pair is merged only after
the decision and the audits, so L9b cannot merge earlier. The strand therefore sits on the path in exactly the scenario where it
runs.
(iii) "Blind Opus audits" for an opus-vs-sonnet pair repeat the S01 self-preference confound (SUMMARY §4). OVERVIEW §5.2 says
"E1, E4 → fable WP audit".
**Fix.** Move E1′ to **S06-L5b** (Lemma G). It is hard, Mathlib-only and has a fixed statement, and it has no consumer in the
DAG, so it is a leaf in both scenarios. L6b is a second choice. Make the strand auditor Fable. Keep the "not triggered if already
run early" rule.

### A11 — maj — §1 Track M deps, §6 remote table (brief E, OVERVIEW §6.1)
**Problem.**
(a) M1–M8 and M11 are marked `early` and "at any time (remote or local)", yet their deps are X1, which needs stage 04 merged.
M1 says "or own stub", and the others say nothing.
(b) There are file collisions. X1 creates `bib/s06.bib`, and M11 (remote, new files only) creates it again. M1–M8 need bib
entries but cannot edit that file. The "first remote WP" that creates `standalone-s06.tex`/`NOTES.md` is a race between
concurrent remote WPs.
(c) M6's remote output `mathematics/audits/s06-levM-abhijit.md` is outside the new-file set of brief E.
(d) The remote table lacks the "local fallback model" column required by OVERVIEW §6.1. It does not say that M6 (preferred
remote, on the M path, slack about 25 min) is re-run locally by Fable if it is undelivered when M9 is ready, which costs about 20 min.
**Fix.** Add a local early kickoff `S06-XM0` (sonnet, about 8 min; it may be part of X0) that creates `standalone-s06.tex`, the
`chapters/s06.tex` driver with `\InputIfFileExists` per section, `NOTES.md`, and one bib file per WP, `bib/s06-<wp>.bib` (the
stage-05 pattern). The M WPs then depend on XM0, not X1. Rename M6's remote output to `mathematics/chapters/s06/NOTES-levM-abhijit.md`,
or get brief E amended. Add the fallback column (M1/M4 opus after A5; M2/M3/M5/M7 opus; M6 Fable; M11 sonnet) and the M6
re-run rule.

### A12 — maj — §3.1 early-lane merge mechanics (Q1)
**Problem.**
(a) "One `--no-ff` merge (new files only)" is not true. `lean_lib Langlandscape` has no globs (`lakefile.toml`), so
`lbuild Langlandscape` builds only the modules reachable from `Langlandscape.lean`. The merge must therefore edit
`Langlandscape.lean`, `LanglandscapeTests.lean` and `Audit/PrintAxioms.lean`, and X0 also edits `tools/check_wp.sh`. Without the
root lines, no later stage's gate builds the CommAlg files.
(b) The merge source is unspecified. `impl/s06-early-int<k>` carries `.titan/` (A0.1), so it must not be the branch merged.
(c) X0's regex change (`s0[1-6]-`) collides with S02-X1's widening (`s[0-9][0-9]-`) on the same line.
(d) OVERVIEW §2 says that only the active stage master merges into `wip-implementation`. Merging foreign code mid-stage puts
unreviewed modules (see A6) into that stage's final from-scratch gate and audit scope.
**Fix.**
- X0 drops the tools edit and depends on S02-X1 being merged.
- The merge source is a clean branch `impl/s06-early`, with WP commits only and no `.titan/` (checked by
  `git ls-tree -r … | grep .titan` empty).
- The global master merges it at a stage boundary, after stage k merges to `main` and before stage k+1's X1. The three
  aggregator lines go in the merge commit, and the merge gate is stage k+1's `int1`, which includes the CommAlg spec lines
  once.
- The early coordinator announces it in the outbox to the stage-04/05 masters.
- Write this into §3.1 as the proposed answer to Q1.

### A13 — min — §0 GL2TF-free gate, L6b
The grep covers all of `CommAlg/`, including stage 04's `EtaPrinciple.lean` and stage 05's `SubQuot.lean` (fine today, but they
are other stages' files). L6b is supposed to "discharge `Hyp.ResidualBurnside`", which means importing
`Langlandscape.Hyp.ResidualBurnside` (L8a, not early). That violates the gate and the `early` tag. Fix: L6b proves
`CommAlg.surjective_groupAlgebra_of_absIrred` only. The one-line discharge lemma for `Hyp.ResidualBurnside` goes in
`Defect/Galois.lean` or `LanglandscapeTests/S06/` after L8a (edge L8a→L6b′). Restrict the grep to the files of the 12 early WPs.

### A14 — min — §1 L13
`LemmaS.congruenceIdeal_baseChange` is false without the Gorenstein hypothesis: `Ann` does not commute with non-flat base change,
e.g. `A → A/𝔭`. The tex states it for Gorenstein `S` and a local `φ`. Fix: add `(hℓ : IsGorensteinWith A S ℓ)` and fix the Lean
form of `μ ⊗ A′` (`Algebra.TensorProduct.lift`/`map`) in the row.

### A15 — min — §1 L1
L12 item (2) ("`IsGorensteinWith` = `S^∨` free of rank one over `S`") is checked only by reading. Add an equivalence lemma
`isGorenstein_iff_dual_free` (or its forward direction) to L1, so the encoding is checked in Lean. The tests `isGorenstein_self`
and `congruenceIdeal_id` have no file: put them in `LanglandscapeTests/S06/Gorenstein.lean`.

### A16 — min — §3, X2 (naming and timing)
- The job kinds `s06-eint<k>` and `s06-egate-1` and the branch `impl/s06-early-int<k>` are not in the §4.3 grammar. The job ids
  lack `-<n>`. Spec names (`spec-s06-int1.txt`) differ from `spec-int<k>.txt`/`spec-<job>.txt`. Axiom file names differ too:
  `axioms-s06.lean` in X2 versus `axioms-s06-eint1.lean` in §3.
- X2's round is "int2 onwards", but the eint1/int1 specs already list `AXIOMS` files. That is a hand-written int1 scratch file,
  which is exactly the s01-int3 failure mode.
- Fix: register the early-lane grammar in OVERVIEW §4.3 (global master), unify the names, and run X2 from eint1/int1.

### A17 — min — §1 test-file layout
`LanglandscapeTests/CommAlg/Toy.lean` and `LanglandscapeTests/Hyp/S06.lean` deviate from the `LanglandscapeTests/S0N/` layout
of stages 01–04. A generic `Toy.lean` invites collisions. Fix: `LanglandscapeTests/S06/{Gorenstein,Toy,Hyp}.lean`, and the
GL2TF-free grep on `LanglandscapeTests/S06/{Gorenstein,Toy}.lean`.

### A18 — min — X1 vs L8a (HYPOTHESES rows)
X1 writes the 8 HYPOTHESES rows "open" before the statements exist, and L8a also delivers the rows. That is two owners of the
same registry lines. Fix: X1 writes the name-only placeholder rows, and L8a's report replaces them with the final text (stage
master applies).

### A19 — min — §4 L12 checklist
The checklist misses three things: the review of `def`/`structure` docstrings, which `check_wp.sh` does not cover (OVERVIEW §4.3
tooling note); the A2 locality and A4 Gorenstein-source checks; and a diff of the exported `if:s06-lemD` signatures against the
stage-05 import list. Add them.

### A20 — min — cross-stage seam text (05/06)
The stage-05 §0 seam lists `S` as "finite free **local**". Stage 06's `NewOldData` has no such field, which is harmless but should
be stated. Stage 05 also does not know that `NewOldData` lives in `Gorenstein.lean`: its fallback S05-L6F writes only
`NewOld.lean`. Fix: an outbox note to the stage-05 reviser together with the A1 decision.

### A21 — min — statement interfaces
L6b's input "M4 proof" is not a stage-tex label: the Burnside/Nakayama step sits unlabelled inside the proof of `prop:s06-galois`.
The L10a toy exists only in the plan row. Fix: M1/M4 add labelled statements (`ex:s06-toy`, `lem:s06-burnside`) so that
docstrings can cite labels. Until then, cite `prop:s06-galois` (proof).

### A22 — min — DAG presentation
- X0 lists worktrees for "L1–L7/L13" but omits L10a and L14.
- The edge list has no B-variant edges `X1→{L1,L6,L7,L14}`.
- The Mermaid graph omits L5b, L14 and X2.
- `{L1..L10b}(green)->L16` hides L5b and L13.
- Fix: write out the edges.

### A23 — min — §2 early lane wall, mixed scenario
The early-lane estimate of 80–90 min assumes free TITAN slots. During S02, the E1 strand pair plus the integration round fill
all 3 builds, so priority-3 jobs starve. The plan also has no "mixed" scenario, in which only part of the CommAlg layer is green
at stage start. Fix: say that scenario A needs the early lane to start at least one stage before S06, or define the mixed case
(the remaining early lines join `int1`, which costs about 1–2 rounds).

## Counts
crit 1 (A1) · maj 11 (A2–A12) · min 11 (A13–A23) · total 23.

## Verdict
**REVISE before launch; the structure conforms.** A1 must be fixed now, before stage 05 freezes its import of `if:s06-lemD`.
A2–A4 (false or underdetermined Lean statements), A8 (spec bug) and A12 (merge mechanics) must be fixed before the early lane
starts. A5–A7 and A9–A11 must be fixed in the pre-launch pass. The minors can go into that same pass. The early-lane idea itself
is sound and plausible: the CommAlg layer needs only Mathlib v4.35 and no GL2TF, as checked against the existing project and
the frozen Mathlib. That holds once it gets its own audit (A6) and a defined merge (A12).
