# Audit of stage-02.md

## F1 — critical — stage-02.md §2 Waves / §4 Resources — Claude-agent limit exceeded
**Severity:** critical
**Location:** `stage-02.md:90-100` (Waves W0 list, Throughput bound), `OVERVIEW.md:4` (Resources)
**Problem:** OVERVIEW §4 limits stage parallelism to ≤3 Claude subagents per coordinator. Wave W0 lists 8 WPs that “may start” together (X1, M1, M2, M3, M5, L8, L1, C4); W4 similarly lists ~7 L/C WPs in parallel. The plan notes “with ≤3 workers ≈12h” but does not constrain W0/W4 to 3. As written the wave schedule violates the resource policy.
**Suggested fix:** Restate waves as eligibility, not concurrency: cap active workers to 3; serialize W0 into e.g. (X1) → (M1,M2,M3) → (L1,L8,C4) → (M5) with explicit priority to critical-path L-chain; or add second coordinator explicitly approved by global master and counted separately.

## F2 — major — stage-02.md:43 S02-M2, stage-02.md:44 S02-M3 — acceptance check insufficient for hard maths
**Severity:** major
**Location:** `stage-02.md:30` (Track M table, acceptance TEXCHK), `OVERVIEW.md:1` Schema
**Problem:** S02-M2 and S02-M3 are `hard` (90–120 min) and deliver Prop s02-BG and Prop s02-quot/coh with signs, index factors and SA-free vs SA+HS distinctions. Acceptance is only `TEXCHK(labels)` (latexmk exit 0, no undefined refs). OVERVIEW requires non-mechanical parts name the reviewer. TEXCHK cannot detect a false proof.
**Suggested fix:** Add reviewer gate: e.g. “TEXCHK + reviewer M6/Fable sign-off on proofs of Prop s02-BG (i⇔iii) and sign table of Prop s02-coh” or split into mechanical (labels present) and non-mechanical (named reviewer) as per schema.

## F3 — major — stage-02.md:45 S02-M4 — soft dependency makes acceptance non-mechanical
**Severity:** major
**Location:** `stage-02.md:31` S02-M4 row `deps: X1, (C4 soft)`, `stage-02.md:118` H02.2
**Problem:** S02-M4 acceptance requires numbers equal `results/s02/torsion.json` from S02-C4, but deps mark C4 as “soft: write with sketch first”. The plan allows M4 to merge before C4, leaving the chapter in *sketch* status while claiming D1 fix. Mechanical check “numbers equal torsion.json” is then not enforceable.
**Suggested fix:** Make C4 a hard dep for M4 final merge; allow an interim M4a (sketch) WP with distinct acceptance “TEXCHK sketch”, and block M4 PASS until C4 JSON exists. Update DAG edge C4→M4 to hard.

## F4 — major — stage-02.md:55 S02-L1 / stage-02.md:56 S02-L2 — inconsistent tree model (GL₂ vs SL₂)
**Severity:** major
**Location:** `stage-02.md:20` (Lean conventions, coset form), `stage-02.md:55-56` L1/L2 outputs
**Problem:** Conventions state tree is in coset form `GL₂(ℚ_q)/(ℚ_q^×·GL₂(ℤ_q))` / `/(ℚ_q^×·Iw_q)`. L2 outputs `Tree.Vert q` as `SL₂(ℚ_q)/SL₂(ℤ_q) ⊔ SL₂(ℚ_q)/K1` and `Tree.Edge q` as `SL₂(ℚ_q)/(SL₂∩Iw)`. The two models coincide only after proving `GL = Z·SL·K` decomposition; stage.tex Def s02-tree uses GL₂ with scalars, while L2 uses SL₂ without scalars. API mismatch will break L4a (`GammaU` action via `localComponent q`).
**Suggested fix:** Choose one model in conventions and carry through: either define `Vert/Edge` as `GL₂/(ℚ_q^×·K)` and derive SL₂ transitivity as lemma, or define `Vert` as `SL₂/(SL₂∩K)` and add explicit norm-1 restriction lemma linking to Def s02-tree; make L4a depend on that bridge lemma.

## F5 — major — stage-02.md:62 S02-L6 — missing dependency on L1 (index_Iw)
**Severity:** major
**Location:** `stage-02.md:62` S02-L6 deps, `stage-02.md:55` S02-L1 outputs `index_Iw = q+1`
**Problem:** S02-L6 goal includes “`Prop s02-free(b) count |XB(U0q U)| = (q+1)|XB U|` at a free level” which uses `index_Iw = q+1` from L1 (Projectivization card). Declared deps are `L5b, S01-L5b` only; transitive path L1→L4b→L5b→L6 exists in the edge list, but L1 is not a direct input of L6 and the DAG completeness rule “a WP using an output of another must depend on it” is violated if the transitive edge is removed via the proposed parallelisation (L4a ∥ L2). Early-start fallback would break the chain.
**Suggested fix:** Add explicit dep `L1 → L6` (or `L1 → L6` for `index_Iw`) and keep it even when L4a is parallelised.

## F6 — major — stage-02.md:67 S02-L10 — non-vacuity claim contradicts §0 hypothesis policy
**Severity:** major
**Location:** `stage-02.md:18` table (Hyp.SA/HS/BTtree cannot be instantiated), `stage-02.md:67` S02-L10 outputs
**Problem:** §0 states Hyp.SA/HS/BTtree “cannot be instantiated in stage 02 (that would be the theorem); the registry row says so.” L10 output promises a `Fintype` certificate proving `BGConnected` for `(B₃,U₁(5),2)` relative to `Hyp.BGData` and `decide` succeeds. This is a per-instance discharge of SA, contradicting the “cannot be instantiated” note and relying on uncertified class-set enumeration (import sorry `III.qcls.ex:eichler-mass-instances-small`).
**Suggested fix:** Reword §0: Hyp.SA cannot be proved in general, but per-instance `BGConnected` certificates are allowed relative to `Hyp.BGData`; add explicit disclaimer that `Hyp.BGData` remains open and SORRIES entry for the class-set enumeration is required.

## F7 — minor — stage-02.md:58 S02-L3 — difficulty/model underestimates hypothesis-faithfulness risk
**Severity:** minor
**Location:** `stage-02.md:58` S02-L3 `mechanical / TBD(default:sonnet; haiku if S01-L13 strand passes)`
**Problem:** Registering 3 hypothesis files with docstrings is marked `mechanical`, but the plan itself flags hypothesis faithfulness as a top risk (Risk 3) requiring Fable audit in L12. A haiku model for this WP (conditional on S01-L13) is inconsistent with OVERVIEW guidance “conceptual maths never haiku” and with the need to copy shapes exactly from tex and L–M names.
**Suggested fix:** Raise difficulty to `routine`, set model to `sonnet` (or `opus` for verification), remove haiku option; keep `mechanical` only for file creation, not shape validation.

## F8 — minor — stage-02.md:64 S02-L8 — acceptance example incomplete
**Severity:** minor
**Location:** `stage-02.md:64` S02-L8 acceptance, `stage.tex:def:s02-indef` / `prop:s02-free`
**Problem:** Acceptance test “B₂, q=7 graph (1+1 vertices, 2 edges) has rank 1” is the C3 T2 case, not the L8 generic construction. L8 defines `Graph.BipMultigraph (E ⇉ V₀⊔V₁)` with rank `|E|-|V|+#components` over ℤ and over a field, but the test does not check the field case nor decidable connectivity for `Fintype` data, which L10 relies on.
**Suggested fix:** Expand acceptance to two checks: (i) B₂,q=7 example over ℤ (rank 1), (ii) same graph over `ZMod p` rank equals ℤ rank, (iii) `decide` connectivity on a 2-vertex example.

## F9 — minor — stage-02.md:74 S02-C2 — model assignment vs verification policy
**Severity:** minor
**Location:** `stage-02.md:74` S02-C2 `TBD(default: mistral, verifier sonnet)`
**Problem:** Mistral is cheapest but OVERVIEW §5 defaults Python/CAS routine to mistral or sonnet with sonnet verification. The plan names verifier sonnet but does not count the verifier against the ≤3 Claude-agent limit nor state that the launching worker re-runs `pytest` and checks provenance.
**Suggested fix:** State “mistral draft, launching worker (sonnet) re-runs PYCHK and verifies provenance; verifier counts as worker slot”.

## F10 — minor — stage-02.md:81-88 Resource batching — TITAN slot accounting
**Severity:** minor
**Location:** `stage-02.md:88` Build batching, `OVERVIEW.md:3.4` SLOTS
**Problem:** Plan lists TITAN candidates L11 full rebuild and L12 audit build, plus “any fresh-worktree first build under outcome V, ~25 min locally”. Under P, no TITAN use is needed, but under V the first build of `LanglandscapeVendorGL2TF` is ~7 min on TITAN and could run concurrently with L2’s 5-min lfile offload, totalling 3 TITAN jobs if W5 full library also queued. The text claims “≤3 TITAN via global master” but does not serialize them.
**Suggested fix:** Cap concurrent TITAN jobs to 2 (leave 1 slot for stage-master merge gate); sequence V first build before L11 full rebuild.
