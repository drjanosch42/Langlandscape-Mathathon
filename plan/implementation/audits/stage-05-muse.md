# Audit of `stage-05.md` (P3 implementation plan) against OVERVIEW.md, SPLIT.md, stage.tex

Date: 2026-11-14 — Auditor: Muse Spark Open (model: meta/muse-spark-open)
Scope: `stage-05.md` vs `OVERVIEW.md` (schema, branches, Lean layout, resources), `SPLIT.md` (interfaces), `stage.tex` (label existence), DAG completeness/critical-path, acceptance/mechanical checks, model plausibility, Lean/math errors. Only defects reported.

---

## F1 — Critical — `stage-05.md:§1 M4` — Missing dependency edge (DAG completeness)

**Problem:** `S05-M4` inputs list `if:s06-lemD` (Lemma D) and goal is `prop:s05-subquot` proved via Lemma D(a). Deps column lists `X1` only (`stage-05.md:1` table row S05-M4). By OVERVIEW §1/§6 a WP using an output/interface of another must depend on it. The producer is `S06-L(D)` (stage 06) or fallback `S05-L6a`. No edge `S06-L(D) -> M4` / `L6a -> M4` is present; DAG diagram `stage-05.md:2` also lacks it. This makes the DAG incomplete and allows unsound scheduling (M4 merged before Lemma D exists).

**Fix:** Add `S05-L6a ∨ S06-L(D)` (or stub) to `S05-M4` deps with note "via `if:s06-lemD`". Update DAG text and Mermaid edges. Alternatively declare M4 as blocked until `if:s06-lemD` interface merged.

---

## F2 — Major — `stage-05.md:§1 L6b` — Ill-formed deps field (schema violation)

**Problem:** `S05-L6b` deps column is `L6a ∨ S06-L(D) (stub allowed)` (`stage-05.md:1` Lean table). OVERVIEW §1 schema requires `deps` to be a concrete list of WP ids present before start. Disjunction + free-text "stub allowed" is not a valid id and breaks dependency resolution / batching logic. §0 text describes ownership rule but table must list the resolvable predecessor(s).

**Fix:** Write deps as `S05-L6a` with footnote "rebinds to `S06-L(D)` if that merges first; stub `CommAlg/NewOld.lean` with exact signature `ann_eq_of_newold` allowed on branch only, see §0". Create explicit stub WP if needed; remove `∨`.

---

## F3 — Major — `stage-05.md:§1 multiple WPs + stage.tex` — Cited labels not in `stage.tex`

**Problem:** Requirement (2) demands every `inputs` label exist in `stage.tex`. The following appear in WP `inputs` but have no `\label{…}` in `stage.tex` (verified by grep):

- `prop:s01-relations` (`S05-M1`, `S05-L1` inputs — stage-01 proposition, not in this stage file)
- `lem:s06-D` (`S05-L6a` inputs — belongs to stage 06; stage 05 file references it as `lem:s06-D(a)` but `stage.tex:1` only defines `sec:stage-05` … `if:s05-subquot`)
- Cross-stage interfaces `if:s01-hecke`, `if:s03-amalgam`, `if:s04-ekills`, `if:s04-Mord`, `if:s06-lemD` (`S05-M3/M4/L2/L6/L7/L8` inputs). None have `\label{if:s…}` in `stage.tex`; they are imported interfaces defined in `SPLIT.md:Interfaces`.

While `SPLIT.md` authorises importing via `if:` labels, the plan's own rule (OVERVIEW §1: every Lean WP cites the statement it formalizes via stage-tex label or `mathematics/` label; statement must exist before WP starts) is violated for `prop:s01-relations` and `lem:s06-D` which should point to `mathematics/` or `lean/` declarations, not bare stage-tex labels.

**Fix:** Replace cross-stage `if:` citations with the corresponding `mathematics/chapters/sNN/*.tex` labels once those chapters exist, or cite them as `SPLIT.md:if:sNN-…` with status `imported`. For `prop:s01-relations` cite `S01-L11` declaration `GL2TF.…` / `mathematics/chapters/s01/…`; for `lem:s06-D` cite `S06-L(D)` output file `CommAlg/NewOld.lean:ann_eq_of_newold` and treat `if:s06-lemD` as interface export, not tex label.

---

## F4 — Major — `stage-05.md:§1 X1/M1–M9 + §2 DAG` — Inconsistent / incomplete acceptance checks (non-mechanical, insufficient)

**Problem:** OVERVIEW §1/§3.6 mandates mechanical acceptance where possible: `latexmk -pdf` exit 0 **and** no undefined refs; `tools/lfile.sh OK` + `grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide'` empty; `pytest` pass; numbers equal stated table. The plan uses abbreviations `LCHK`, `TEXCHK`, `PYCHK` "as in stage-02.md §0" but never defines them in this file. Concrete rows:

- `S05-X1`: `latexmk exit 0` only — omits undefined-refs check required by OVERVIEW §1.
- `S05-M1–M7`: `TEXCHK(…)` with "every `\lit` page checked (list in report)" — manual page verification is not mechanical; no `latexmk` undef-ref clause, no reviewer named for non-mechanical part.
- `S05-M8`: `verdict PASS or fix list` — entirely non-mechanical with no named reviewer (Fable alone is track, not reviewer name) and no measurable criterion.
- `S05-L1–L8`: `LCHK` — never expanded to `tools/lfile.sh … && grep …` and `lbuild` target list; lacks sorry/axiom grep mandated for Lean WPs.
- `S05-C1–C4/H1`: `PYCHK: values equal …` — no `pytest` invocation, no table file/column spec, no provenance (script hash, params, runtime) required by OVERVIEW §6 / `code.md`.

This leaves Lean vacuity and LaTeX undefined refs undetectable by CI.

**Fix:** Expand abbreviations in §0 with exact shell commands referencing OVERVIEW: `TEXCHK := cd mathematics && latexmk -pdf main.tex && ! grep -q "undefined" main.log`; `LCHK := tools/lfile.sh <file> && ! grep -rnE '\bsorry\b|\badmit\b|^axiom' …`; `PYCHK := pytest code/python/… && python -m langlandscape.comparison.check --expected code/results/s05/…`. For M8 name reviewer (Fable coordinator) and define PASS criteria (e.g., ε/e/δ checklist closed).

---

## F5 — Major — `stage-05.md:§2 DAG text vs Mermaid + §3 Entry conditions` — DAG inconsistency and missing edges (completeness)

**Problem:**

- Text DAG line `M1->M6(soft)` (`stage-05.md:2`) claims a soft edge, but the table gives `S05-M6` deps = `X1` only, and Mermaid graph `stage-05.md:2` omits `M1→M6` entirely. If M6 literature search depends on M1's table being contested (as `S05-M6` model column hints "opus if M1 finds table contested"), the edge must be present; otherwise `M1..M7->M8` alone is insufficient for ordering.
- `S05-L2` lists soft input `S03-L1/L3` but DAG marks it `(soft)` — soft edges are not real deps; however completeness rule "a WP using an output of another must depend on it" would require a hard edge if `DRBridge.lean` actually imports `S03-L1` outputs. Ambiguous.
- `S05-L5` uses `S01-L8b` but DAG shows `S01-L8b->L5` — correct, but `S05-L1` also uses `S01-L3c Utower` not shown in DAG (only `S01-L10/L11` shown).

**Fix:** Remove soft edges from DAG or promote to hard deps with justification. Add `M1 -> M6` to table/Mermaid if the contested-table path is real. Add `S01-L3c -> L1` edge; either add `S03-L3 -> L2` hard edge or explicitly state L2's bridge is copy-not-import (no file dependency).

---

## F6 — Major — `stage-05.md:§2 Critical path + §4 Throughput bound` — Resource limit violation (≤3 Claude agents, ≤2 local Lean builds)

**Problem:** OVERVIEW §4 caps **≤3 Claude subagents per coordinator** and **≤2 concurrent Lean processes node-wide** (`SLOTS=2`; TITAN `SLOTS=3` via global master only). `stage-05.md:2` states stage 05 ∥ 06 after stage 04 (SPLIT §7) and recommends "one stage master for 05∥06 Lean with ≤3 workers, a second coordinator for 05/06 M + C + T" (`stage-05.md:2`). This is 2 coordinators × ≤3 workers = up to 6 concurrent Claude agents, double the per-node limit, plus each worker may spawn ≤2 opencode jobs (→ up to 12 opencode processes). Build batching `stage-05.md:2` assumes slot 1 for stage 06 critical path and slot 2 for stage 05, but with two stages running simultaneously the node-wide 2-slot cap is already saturated; any M-track `latexmk` or C-track Python that spawns a Lean check would exceed it. No TITAN throttling is defined for the 4 Lean WPs that claim "TITAN candidate" (`S05-L9` etc.) against the ≤3 TITAN concurrent limit.

**Fix:** Revise resource plan to respect hard caps: at most one active coordinator (≤3 workers total) or time-multiplex 05/06 waves explicitly. State slot allocation as node-wide (e.g., "max 2 local `lbuild`/`lfile` slots shared by 05+06; M/C WPs must not invoke Lean tools while slots occupied"). Enforce ≤3 TITAN jobs via global master queue and list which WPs are TITAN-eligible.

---

## F7 — Minor — `stage-05.md:§2 Critical path calculation` — Slack overstatement

**Problem:** Plan claims "L5, L6a/b have ≥3 h slack" (`stage-05.md:2`). Computed longest-path values (agent wall only, per table):

- Critical: L1 75 → L2 90 → L3 90 → L4 45 → L9 30 → L10 50 = **380 min**.
- L6 chain: L6a 75 → L6b 60 → L9 30 → L10 50 = 215 min (or via L8 75 → 290 min). Slack = 380−215 = 165 min (≈2.75 h), or 90 min via L8, not ≥3 h. Merge-gate cost (+5×10 min) was added to critical path but not to alternative paths, inflating apparent slack.

**Fix:** Recompute slack including identical gate costs on all paths (or state agent-wall-only slack). Correct to "L6a/b slack ≈2.7 h (1.5 h if L8 included)".

---

## F8 — Major — `stage-05.md:§1 L9 + §0 Aggregator files` — Branch/aggregator hygiene breach

**Problem:** OVERVIEW §1/§2 declares aggregator files (`Langlandscape.lean`, `LanglandscapeTests.lean`, `SORRIES.md`, `HYPOTHESES.md`, `mathematics/main.tex`, `code/results/INDEX.md`) are edited **only by the stage master** on `wip-implementation` when merging; WPs deliver one-line additions in final report. `S05-L9` lists `outputs: aggregator edits (stage master)` yet assigns them as WP outputs with ` | stage master` in model column and lists deps `L1–L7 (L8 if done)` — mixing master duties into worker WP table and implying a WP branch will edit aggregators. Conversely `S05-L4` outputs `LanglandscapeTests/Hyp/S05.lean` (a file under the `LanglandscapeTests` lib whose root `LanglandscapeTests.lean` is an aggregator) without clarifying that only the subdirectory file is worker-owned.

**Fix:** Move L9 out of WP table into a §5 "Merge point" checklist owned by stage master; remove aggregator files from `outputs` column (write "report: one-line `Langlandscape.lean` addition `import Langlandscape.Comparison.…`"). Clarify `S05-L4` output is `LanglandscapeTests/Hyp/S05.lean` (non-aggregator lib file) — root file remains master-only.

---

## F9 — Minor — `stage-05.md:§0 Lean conventions + §1 L1` — Inconsistent file/namespace naming

**Problem:** §0 table maps `Langlandscape.Hyp.X.char` → `Hyp/HypX.lean`, namespace `Langlandscape.Hyp.X` (per OVERVIEW §3.6). `S05-L1` goal mentions `S01-L3c Utower` and `S01-L7 ZX` but `stage-01.md` names are `Utower` vs `UTower` / `ZX` vs `Z[X]` — import will fail if names diverge. `S05-L2` outputs `Hyp/HypX.lean` and `Comparison/DRBridge.lean` but diagram Mermaid shows `L2->L4` bypassing L3; file naming `DRBridge` vs `Dictionary` inconsistent with `D3` bridge lemma description.

**Fix:** Cross-check Lean declaration names against `stage-01.md` outputs and import declaration registry; normalize `Utower`/`ZX` spelling. Keep directory `Comparison/` for all comparison modules.

---

## F10 — Minor — `stage-05.md:§1 C2` — Informative pair selection incompleteness (mathematical risk)

**Problem:** `S05-C2` restricts to informative pairs `(13,5)` and `(11,7)` because `11≡1 mod5` and `13≡−1 mod7` are uninformative (correct). However inputs list `S01-C2` (`U_1(N)` class sets) and `S01-C3` without stating that `S01-C2` must have produced class sets for `B_q` (not just `B_D` with D odd) — stage-01 scope is `B` ramified at ∞ and primes dividing D (squarefree, ω odd); `B_q` with D=q is in scope, but `q=11,13` with N=5,7 needs explicit confirmation that those `U_1(N)` class sets exist (M coprime to pqD check).

**Fix:** Add explicit precondition to C2: "requires `S01-C2` outputs for `B_q` with `q∈{11,13}` and `N∈{5,7}` verified `(M,pqD)=1` (p≥5)" or split C2 into setup + compute.

---

