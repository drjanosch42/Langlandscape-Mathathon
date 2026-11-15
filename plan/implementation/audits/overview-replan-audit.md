# Audit: OVERVIEW revision 2 (commit 3d7faf8), adversarial (Opus)

Read: `briefs/replan-s02-06.md` (A–F), `OVERVIEW.md` @ 3d7faf8 (+ diff), `audits/overview-replan-notes.md`,
`agents/rules/{resources,orchestration,lean,frozen,git}.md`, `lean/Langlandscape/tools/{titan_batch.sh,check_wp.sh}`,
`outbox/*titan-s01-*.md`, `runs/s01.md`, `experiments/SUMMARY.md`, `agents/status/master_log.md` l. 40–100; also the
TITAN result branches `origin/titan/s01-{int2f-1,int3-1,final-1}` (`.titan/out/*`) to test the script semantics, and
`agents/status/abhijit_candidates.md` §4 for the remote protocol. Line numbers refer to `OVERVIEW.md` @ 3d7faf8.

Summary: conventions A, B, D and F are encoded faithfully (the tables of A and B match the brief cell by cell; all six
lessons of D are present as steps). C is encoded, but the job-spec material is **not yet self-sufficient**: a stage
master copying it would produce a spec that breaks the script (O1), would trust an axiom counter that misses primed
names (O2), would skip the downstream build stage 1 actually ran (O3), and has no allowed place for `.titan/` files of
single-WP and strand jobs (O4, O5). E is encoded, but is not workable on a 16 GB node as written (O12, O13).

## Findings

**O1 (maj) — §4.3 spec-file format, l. 372–376.** The format block shows trailing `# …` comments on the spec lines.
`titan_batch.sh` skips only lines whose *first* token starts with `#` (l. 11, 20). On any other line every token after
the WP id is taken as a file: a copied line `L3 A.lean   # library + test files …` gives the modules `+#`, `+library`, …
to `lbuild.sh` and gives `check_wp.sh` a non-`.lean` argument (exit 1). *Fix:* move the explanations out of the code
block and state the rules: whitespace-separated, no trailing comments, paths relative to `lean/Langlandscape/`, one
line per WP, no `Vendor/` paths (O18).

**O2 (maj) — §4.3 caveats, l. 383–386 ("after joining wrapped lines").** I checked the counter against real logs
(`titan/s01-final-1:.titan/out/c-axioms.log`) and a test file. (a) **False negative:** Lean prints a primed name as
`'Langlandscape.Brandt.Tl_selfAdjoint_U0'' depends on axioms: …`. The pattern `'[^']+' depends on axioms` never matches
that line, so the line is not counted at all, *even if it contains `sorryAx`*. The test file confirms it: a primed line
with `sorryAx` gave count 0. Stage 1 already has four primed headline declarations (`Tl_adjoint'`, `Tl_selfAdjoint_U0'`,
`Tl_selfAdjoint_units'`, `Up_comm_Tl'`), and §1 l. 19 uses one as its example. (b) **False positive:** wrapped output is
`[propext,\n Classical.choice,\n Quot.sound]`. `tr '\n' ' '` turns it into `[propext,  Classical.choice,  Quot.sound]`
with double spaces. That does not match `propext, Classical.choice, Quot.sound\]$`, so the line counts as non-standard.
So the OVERVIEW's statement that the join is handled is wrong in both directions. *Fix:* add an S02-X1 tooling item
(§4.3 l. 439–441) to patch `titan_batch.sh`. Normalise whitespace (`tr -s '[:space:]' ' '`), match `depends on axioms:
\[[^]]*\]` without the name, and print `printed=<k> expected=<#print lines>`. Until int1 verifies the patch, the stage
master reads `axioms-*.log` by hand. Correct the caveat text.

**O3 (maj) — job-spec template, l. 397–415; merge gate §2 l. 64–67.** `titan_batch.sh` builds only the modules on the
spec lines. Stage-1 practice for fix rounds was to follow the batch with `tools/lbuild.sh Langlandscape
LanglandscapeTests` ("downstream … must still build": `s01-l16b-1`, `s01-int3-1`, which reports `FULL lbuild … rc=0
wall=12s`). The template drops this. A fix WP that changes an upstream file can therefore break unlisted, already
merged modules, and nothing detects it before the gate. The template also does not say *which* WPs go into a round's
spec. Stage-1 practice listed only the WPs that were not yet green (int2f: L17, L4c). *Fix:* add a mandatory step
"(2) `tools/lbuild.sh Langlandscape LanglandscapeTests` (seeded, ≈ 12 s); report rc, error lines and the sorry count".
State: "spec = all WPs of the round that are not yet green, plus fix WPs".

**O4 (maj) — `.titan/` homes, l. 358–360, 416–420, 434–437 vs §2 l. 53, §5.2 l. 509.** (a) The job grammar allows
single-WP jobs `<wp>` (stage 1: `l12`, `l16b`; `spec-l16b.txt` sat on `impl/s01-l16b`, which is exactly finding A0.1).
But `.titan/` may exist only on `impl/sNN-int<k>` and on strand commits, so a single-WP job has no legal home for its
spec. (b) The strand variant says the strand's spec and axiom files "sit on the strand commit, which is never merged".
Yet §2 and §5.2 let the stage master merge one strand. The merged strand would then carry `.titan/` and fail the
merge-gate grep. *Fix:* one rule for every job. TITAN always gets a throwaway commit whose **top commit contains only
`.titan/`**, on top of the integration tree, WP head or strand head. Push it as `impl/sNN-int<k>` or as
`titan-in/<job-id>`. Merge the commit's parent, never the commit itself. The §2 grep then applies to strands as well.

**O5 (maj) — §9 lesson 4, l. 619–621; §2 table l. 51, 53.** "Rebase open strands and WP branches onto the fixed
integration tree" pulls the integration branch's `.titan/` commits and its *non-green* drafts into WP branches. That
breaks the merge-gate grep (l. 66–67) and the rule that only green WPs are merged. The `exp/` row still gives its base
as `wip-implementation`, which ignores stacking. *Fix:* define the base as "the fixed upstream WP head(s), or
`wip-implementation` once the upstream fix is merged". If the integration tree is the base, use `impl/sNN-int<k>~1`
(the parent of the `.titan`-only top commit, O4). When the base contains unmerged upstream drafts, the merge gate
compares `git diff --name-only` against the WP's declared files only.

**O6 (maj) — merge gate §2 l. 64–67, §4.3 flow step 5 l. 363.** The rule is "merge green WP branches", and a WP is
green when its own spec line passes. Under stacking, a WP can be green while its upstream draft is built but not green
(for example, the upstream fails only the docstring or axiom check). Merging the downstream WP alone leaves
`wip-implementation` importing a module that is not there, or produces a merged subset that no build has seen.
`lean.md` (l. 23) requires the build to pass *before* every merge. *Fix:* merge a WP only together with, or after, all
its upstream WPs. The next round, or the step added in O3, builds `Langlandscape LanglandscapeTests` on the merged
`wip-implementation` sha.

**O7 (maj) — priorities, l. 366–368; §5.2 l. 501.** Priority 1 covers the integration round *and* the gates, and TITAN
runs ≤ 3 builds. A round plus `gate-1` plus the two E1 strands needs 4 slots. The promise of "one slot per strand per
integration round, equal latency" therefore cannot be kept, and E1 is confounded again, which is the very confound it
is meant to remove. *Fix:* both strands of a pair go in one outbox file, as two jobs that start together or wait
together. A gate is not dispatched while a strand pair is waiting for its round. Ext/single-WP jobs drop to priority 3
while a pair is active. Log the TITAN start time of each strand job in `events.tsv`.

**O8 (maj) — docstring gate, §9.3 l. 615–618, §3.6 l. 312–313, §4.3 l. 439–441.** `check_wp.sh` (l. 51–92) fails
*every* `theorem`/`lemma` that lacks an immediately preceding `/-- … -/` containing `s01-`. That includes `private`
ones (the `MOD` prefix) and test files. It ignores `def`/`structure`. The OVERVIEW instead tells workers "main theorems
reference their label" and "every public declaration has a docstring". A worker who follows the OVERVIEW fails CHECK_WP
(the L8a case again), and public defs go unchecked. *Fix:* state the exact rule in §4.3 and §9.3 ("every theorem/lemma,
including private ones and tests: `/-- … sNN-label … -/`; public defs: docstring, reviewed in the WP audit"). For the X1
change, decide whether `LanglandscapeTests/**` is exempt. The `s[0-9][0-9]-` pattern must also accept earlier stages'
labels (a stage-03 lemma may cite `lem:s02-…`).

**O9 (maj) — rule conflicts, §4.3 flow l. 342–355, §8 F11/F13.** `resources.md` TEMPORARY (l. 15–16) still prescribes
"SendMessage 'main': job spec", which is the very failure mode behind F11. `git.md` l. 9 has no `plan` area and does not
cover `wip-implementation`. `global_master.md`/`coordinator.md` and CLAUDE.md still route leaf work to opencode
muse/mistral. `EXPERIMENT_PROTOCOL.md` l. 96 still says "≤ 3 subagents, Fable alone", and `common.md` l. 31 says the
same. `lean.md` l. 22 says "main theorem docstring references `mathematics/`", while the tool requires a label in every
lemma. The notes file lists some of these for the global master, but the OVERVIEW neither states its precedence nor
makes the rule updates a launch condition, so a stage master who reads the rules first will follow the old flow.
*Fix:* add **F18 — rule updates before S02 launch** (global master, on `main`), as F9 did for `lean.md`. It lists:
`resources.md` TEMPORARY job flow → outbox file; `git.md` areas + `plan`, + `wip-implementation`; opencode text in the
roles and CLAUDE.md marked "not used as implementer"; the `lean.md` docstring line per O8. Also state that the OVERVIEW
overrides EXPERIMENT_PROTOCOL §1 (limits, slots) and §7 (opencode strands).

**O10 (maj) — §4.4 table and method, l. 447–465; §1 l. 38.** Comparison with `master_log.md` (local time = Z + 1 h):
- TITAN relay→report times were int1 2, int2a 6, int2b 5, int2c 3, int2d 3, int2e 2, int2f 1, int3 1 min, so **1–6
  min**, not 3–8.
- Successive letters followed every ≈ 4 min including the fix dispatch (int2c 18:03 → 2d 18:07 → 2e 18:11 → 2f 18:15).
  int1 → int2f was **7 runs in ≈ 26 min (3.7 min per run, all-in)**.

The method charges R × (round trip 3–8 + fix 2–10) = 5–18 min per round. That double-counts, because the measured 3–8
already contains the fix. It also takes R = 3–6 "rounds", while stage 1 had 8 runs (int1, int2a–f, int3) if letters
count. The units are mixed and the result is biased upward by ≈ 1.5–2×. "Agent-active 10–20" is not in `runs/s01.md`;
SUMMARY has stage-master *estimates* (E1 ~12/~16) and E5 drafts of 0.8/2.7 min, so it should be labelled *estimate*,
not *measured*. "Local short WP 3–17" should be 2–17 (X6 2, L16c 2). The other rows match `runs/s01.md` (Lean 33–80,
M 52, C/T 28, Fable 6, fixes 2–13, final gate ≈ 3–5, stage 2.2 h). *Fix:* let R = the number of TITAN runs (letters
count; expect 5–9). Cost each at 4–8 min all-in. Add fix time only for a `hard` fix that is itself on the critical path
(+5–10).

**O11 (min) — §7 table, l. 557–569.** The stage plans revised in parallel already disagree with §7:
- S03 2.4 h (1.8–3.3) vs 3.0 ± 0.8;
- S04 2.8 h (2.0–3.8) vs 3.0 ± 1.0;
- S05 2.0 h (1.5–3.0) vs 2.5 ± 0.8;
- S06 1.7 / 2.3 h vs 3.5 ± 1.0;
- S03 has 33 WPs vs 29.

*Fix:* mark §7 *provisional* and regenerate it from the audited stage plans, using the O10 method. The
"× 0.25–0.35" cross-check has n = 1 (measured 0.25); say so.

**O12 (maj) — §6.1 node conditions, l. 539–554 (workability, check 5).**
- (a) `resources.md` applies to all workers: keep ≥ 12 GB available and budget 2 GB per agent. On a 16 GB notebook that
  allows ≤ 1 agent, against the "5–8 Opus" of l. 540 and the "≤ 6 Opus workers" of `abhijit_candidates.md`. No
  node-specific budget exists.
- (b) The acceptance check needs TeX Live with `biblatex`/`biber` (`preamble.tex` l. 12) and `latexmk`. These are not
  stated as node prerequisites.
- (c) §2 l. 71–72 says only the global master pushes, but remote WPs need Abhijit to push `abhijit/*`. That is Q5, which
  is still open, so there is no transport channel. Literature is Q2, also open.

*Fix:*
- Add a node row to `resources.md` (global master; e.g. keep ≥ 3 GB free, ≤ 4 concurrent agents, latexmk ≈ 0.5 GB).
- List the TeX prerequisites.
- Make "Q5 approved, and Q2 settled for the WP's sources" an explicit precondition for assigning any WP remote. Until
  then every WP is local.

**O13 (maj) — §6.1 new-files list and branches, l. 544–550.** E gives one branch per WP (`abhijit/<wp-id>`), but
`standalone-sNN.tex`, `bib/sNN.bib` and `chapters/sNN/NOTES.md` are per-stage files that every M WP of the stage would
create. That means several writers, add/add merge conflicts, and a breach of `git.md` "one writer per file". The chapter
file `mathematics/chapters/sNN.tex` is missing from the list, although `main.tex` uses `\input{chapters/s01}` and s01
has `chapters/s01.tex`. "No undefined refs" fails as soon as one WP cites a label from a sibling WP that is not yet
written. The X1 kickoff creates maths stubs, which collides with "new files only" (`abhijit_candidates.md` §4: X1 must
skip them). The standalone driver structure (`\input{preamble}`, `\addbibresource{bib/sNN.bib}`,
`\input{chapters/s01}` for `if:s01-*`, `\providecommand` macros listed in NOTES) appears only in
`abhijit_candidates.md`. *Fix:* either bundle a stage's remote M WPs into one package branch `abhijit/sNN-math` with one
writer for the driver files (the candidates' model), or give one designated WP ownership of the driver/bib/NOTES files,
with per-WP `bib/sNN-<wp>.bib` and `NOTES-<wp>.md`. Allow undefined refs only for labels of the listed sibling WPs.
X1 skips stubs for WPs assigned remote. Encode the driver structure in §6.1.

**O14 (min) — §6.1 tag scope, l. 542–543.** "Tag on all M WPs" contradicts the conditions for M WPs whose inputs include
code results (e.g. S02-M4 "sketch until S02-C4") and for audit-fix M WPs, which edit existing files. *Fix:* "M,
literature and review WPs that satisfy all conditions; never audit-fix WPs".

**O15 (min) — axiom files, l. 344, 382–390, 393–394.** The naming is inconsistent: `.titan/<wp>_axioms.lean` in the
flow, `.titan/s01_l16a_axioms.lean` in the example, and a shared `l17_l4c_axioms.lean` in s01-int2f. "Its AXIOMS line"
needs a 1:1 map between WP and axioms file. `lfile.sh` builds nothing, so every module imported by an axioms file must
be on a spec line. A Hyp-def WP always yields a strict-subset line (`Hyp.LambdaJL` → `[propext, Quot.sound]`), so
`nonstandard=0` can never be met mechanically, which contradicts the green rule at l. 382. *Fix:* use
`.titan/sNN_<wp>_axioms.lean`, one per WP, with its imports covered by the spec. Green = every line ⊆ standard, by the
patched counter (O2), or by the stage master for subset lines.

**O16 (min) — job-id grammar, l. 358–365, 421, 605–608.** `sNN-<job>-<n>` with `<job> = gate-<m>` gives `s02-gate-1-1`,
but §4.3 and §9.1 write `sNN-gate-1` and `sNN-final-1`. It is also unspecified whether the first run of round k is
`int<k>` or `int<k>a` (stage 1: int1, int2a, int3). *Fix:* give one grammar, e.g. the first run is `int<k>`, re-runs
are `int<k>a, b…`, gates are `sNN-gate<m>-<n>` and `sNN-final-<n>`.

**O17 (min) — summary.txt semantics, l. 380–382.** The script lists `Built|Building|Replayed` lines (l. 18). Since a
`Building` line without a following `Built` is the failure signal, the OVERVIEW's `Built|Replayed` omits exactly the
informative case. `grep -c FAIL` also counts `check_wp: FAILED`, so only the value 0 has a meaning. *Fix:* correct the
text.

**O18 (min) — vendor files.** `check_wp.sh` strips `Vendor/AxiomStacks/` when it maps files to modules (l. 25–27);
`titan_batch.sh` does not (l. 12), so a vendor file on a spec line gives a wrong module. S04 plans "small Weil
vendoring". That needs a new `lean_lib`, a `lakefile.toml` change with `pins.sha256` in the same commit (stage master)
and an `lbuild.sh` allowlist entry, and none of this has a procedure. *Fix:* add an X1 tooling item for the mapping, and
a §3.4 note on adding a vendor lib (stage master, pins updated, checked in a round).

**O19 (min) — stale text presented as current.**
- l. 233 "opencode jobs may only call … (counted double, §4)": opencode is dropped, and §4 has no such rule.
- l. 147–150 "must be updated by the global master … before stage 1" is an imperative, but F9 is DONE.
- §1 l. 20–21 "est. build wall (min, Lean only)" means nothing under batched TITAN.

*Fix:* mark the first two as history. Replace the field with "agent-active (min) / TITAN runs".

**O20 (min) — haiku and file ownership, §5.1 l. 486 vs §9.2 l. 612–614, §8 F17 l. 600–602, §2 l. 52 vs §4.3 l. 437.**
"Haiku never for … Lean beyond copy/vendoring" conflicts with the haiku axiom-list WP, which writes `.lean` scratch
files, and with a "haiku/sonnet hygiene WP" that edits Lean to fix 80 linter warnings. "Integration branch: stage
master only" conflicts with "(or the haiku axiom-list WP) writes the files". *Fix:* the haiku WP returns the list in
its report and the stage master writes the files. The hygiene WP is sonnet (+ opus fix).

**O21 (min) — §5.2 l. 503.** "Strand WPs always run locally" is ambiguous next to "no local Lean". *Fix:* "on Fabian's
node (never remote-eligible); Lean checks via TITAN as for all WPs".

**O22 (min) — gate variant, l. 421–427.** No expected axiom-line count is given. Silently missing lines in
`Audit/PrintAxioms.lean` (the L14 failure mode) are caught only if TITAN compares printed and expected counts. *Fix:*
the gate spec states `expected = <# of #print axioms lines>` and TITAN reports printed vs expected.

## Check results
1. Conventions A–F: A ✓, B ✓ (but O7), C partly (O1–O6), D ✓ in text (O8 on D3, O5 on D4), E encoded but not workable
   as is (O12–O14), F ✓ in text with calibration errors (O10).
2. Template and spec format vs script and stage-1 practice: not yet sufficient on its own (O1–O4, O15–O17).
3. Contradictions, stale text and rule conflicts: O4–O6, O9, O19, O20.
4. Wall calibration vs `runs/s01.md`: the table matches apart from the round-trip and agent-active rows; the method
   double-counts (O10, O11).
5. Remote-eligible definition for a 16 GB node without Lean: not workable until O12 and O13 are fixed.

Counts: 0 crit, 12 maj (O1–O10, O12, O13), 10 min (O11, O14–O22).

## Verdict
**PASS WITH REQUIRED FIXES.** No critical findings. The major findings must be fixed before stage 02 launches:
- O1–O8 (TITAN spec, template, `.titan/` homes, merge and strand rules, docstring gate) are mandatory, because S02-X1
  writes the int1 spec from this text.
- O9 needs the global master's rule updates on `main`.
- O12 and O13 must be fixed before any WP is assigned to Abhijit.
- O10 should be fixed before the stage walls are final.
