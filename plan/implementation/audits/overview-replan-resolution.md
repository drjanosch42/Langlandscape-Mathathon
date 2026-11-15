# Resolution: OVERVIEW replan audit (O1–O22)

Reviser: Sonnet. Audit: `audits/overview-replan-audit.md`. Result: `OVERVIEW.md` (sections §4.3, §4.4, §5, §5.2, §6.1, §9 keep their names).
Each finding was re-verified against `lean/Langlandscape/tools/{titan_batch.sh,check_wp.sh}`, the TITAN logs on `origin/titan/s01-{final-1,int3-1}`, the outbox files and the rules.
Tool and rule changes are **not** made here; they are named kickoff items "S02-X1 tool fix: …" / "global-master rule edit: …" in OVERVIEW and listed below.

| id | verdict | what was done | evidence |
|---|---|---|---|
| O1 | ACCEPT | §4.3 format block without trailing comments; rules stated (no trailing comments, relative paths, one line per WP, no `Vendor/`) | `titan_batch.sh` l. 11/20: only a first token starting with `#` is skipped; `for f in $rest` turns `# …` into modules `+#…` |
| O2 | ACCEPT | Caveat rewritten (both defects); kickoff item "S02-X1 tool fix: axiom counter" (normalise whitespace, drop name from pattern, ⊆-standard test, printed/expected); stage master reads `axioms-*.log` by hand until int1 verifies | Reproduced on `titan/s01-final-1:.titan/out/c-axioms.log`: primed lines (`Tl_adjoint''`) exist and the pattern cannot match them; wrapped lines have a leading space, the counter gives 3 false positives on the real log |
| O3 | ACCEPT | Template: step (2) `tools/lbuild.sh Langlandscape LanglandscapeTests` after the batch; rule "spec = WPs of the round not yet green + fix WPs"; (needs no tool change, it is part of the job command) | `titan_batch.sh` builds only spec modules; `outbox/*s01-l16b-1.md` and `*s01-int3-1.md` run the extra lbuild |
| O4 | ACCEPT | One rule for every job: `.titan/`-only throwaway top commit on top of the integration tree / single-WP head / strand head, pushed as `impl/sNN-int<k>` or `titan-in/<job-id>`; merge the parent; §2 table and grep updated | Stage-1 A0.1 (`spec-l16b.txt` on `impl/s01-l16b`); §2 permitted a merged strand that carried `.titan/` |
| O5 | ACCEPT | Base of WP and strand branches = fixed upstream WP head(s) or `wip-implementation`; `impl/sNN-int<k>~1` if the integration tree is the base; diff vs declared files; §2 rows and §9.4 | Rebasing onto the integration branch imports its `.titan/` commit and non-green drafts, contradicting the §2 grep |
| O6 | ACCEPT | §2 merge gate: merge a WP only with or after its upstream WPs; build `Langlandscape LanglandscapeTests` on the merged sha before the next merge | `lean.md` requires a build before every merge; a green WP can sit on a non-green upstream draft |
| O7 | ACCEPT | §4.3 priorities: strand pair in one outbox file, start/wait together, no gate while a pair waits, ext jobs to priority 3, log TITAN start times in `events.tsv`; §5.2 updated | TITAN ≤ 3 builds (round + gate + 2 strands = 4) |
| O8 | ACCEPT | Exact rule in §3.6 and §9.3 (every theorem/lemma incl. private and tests: `/-- … s<NN>-… -/`; defs reviewed in audit); kickoff item "S02-X1 tool fix: docstring pattern" (`s[0-9][0-9]-`; tests not exempt by default); rule edit for `lean.md` l. 22 | `check_wp.sh` python block: DECL matches `private`/any theorem/lemma, requires `'s01-' in doc`, ignores def/structure; `lean.md` l. 22 says only "main theorem" |
| O9 | ACCEPT | Header precedence clause (overrides EXPERIMENT_PROTOCOL §1/§7, `common.md` l. 31; does not override `agents/rules/*`); new decision **F18** (rule updates before S02 launch: resources, git, opencode text, lean.md) | `resources.md` TEMPORARY still says "SendMessage 'main'"; `git.md` area list lacks `plan`; `global_master.md` l. 22, CLAUDE.md l. 34 and `EXPERIMENT_PROTOCOL.md` l. 96–98, 106 still describe opencode/≤ 3 subagents. (The audit cited protocol l. 96 for "Fable alone": confirmed at l. 96.) |
| O10 | ACCEPT | §4.4 table and method rewritten: R = number of TITAN runs (5–9, letters count) at 4–8 min all-in, no double count, fix time only for critical-path `hard` fixes; relay→report 1–6, all-in ≈ 4, local WP 2–17, agent-active marked *estimate*, final gate 3–5; §1 and §4.3 text aligned | `master_log.md` times (relay→report 1–6 min; int2c→2d→2e→2f ≈ 4 min); `runs/s01.md` has no agent-active figures (grep) |
| O11 | MODIFY | §7 marked provisional, divergences from the stage-plan drafts listed, n = 1 caveat for the 0.25–0.35 cross-check. Not regenerated here, because the stage plans are still being audited in parallel; the global master regenerates it from the final plans | Stage-plan walls: S02 2.5 ± 0.7 h, S03 2.4 h (1.8–3.3) with 33 WPs, S04 2.8 h, S05 2.0 h, S06 1.7/2.3 h (`stage-NN.md`) vs §7 |
| O12 | ACCEPT | §6.1: TeX prerequisites; 16 GB budget; precondition "Q5 approved and Q2 settled for the WP's sources, otherwise every WP is local"; rule edit for a `resources.md` node row (F18) | `resources.md` (≥ 12 GB free, 2 GB/agent ⇒ ≤ 1 agent on 16 GB); `preamble.tex` l. 12 `backend=biber`; §2 "only the global master pushes" |
| O13 | ACCEPT (option 1) | §6.1: package branch `abhijit/sNN-math` with one writer for driver/bib/NOTES; chapter driver `chapters/sNN.tex` listed; per-WP files `chapters/sNN/<wp>.tex`; sibling-WP undefined refs tolerated; driver structure encoded; X1 makes no stubs for remote WPs | `abhijit_candidates.md` §4; `main.tex` uses `\input{chapters/s01}`; per-stage files would otherwise have several writers (`git.md` one writer per file) |
| O14 | ACCEPT | §6.1 tag rule: only M/literature/review WPs satisfying all conditions; never audit-fix WPs or WPs needing unmerged code results | Audit-fix WPs edit existing files, contradicting "new files only" |
| O15 | ACCEPT | One axioms file per WP, `.titan/sNN_<wp>_axioms.lean`, imports on spec lines; green = ⊆ standard (patched counter or stage-master reading) | `titan_batch.sh` ties `AXIOMS` lines to files 1:1 and `lfile.sh` builds nothing; strict subsets are counted as non-standard by the current script |
| O16 | ACCEPT | Grammar in §4.3: first run `int<k>`, re-runs `int<k>a…`, gates `sNN-gate<m>-<n>`, `sNN-final-<n>`; §9.1 updated | Outbox names `int1-1`, `int2a-1`, `int3-1`, `gate-1` in stage 1 |
| O17 | ACCEPT | Text corrected: `Built|Building|Replayed`; FAIL count includes `check_wp: FAILED`, only 0 meaningful | `titan_batch.sh` l. 18 pattern; `grep -c FAIL` |
| O18 | ACCEPT | Kickoff item "S02-X1 tool fix: vendor path mapping"; rule "no `Vendor/` paths on spec lines"; §3.4 note "Adding a vendor lib" (lakefile, pins.sha256 same commit, allowlist, round check) | `check_wp.sh` l. 25–27 strips `Vendor/AxiomStacks/`, `titan_batch.sh` l. 12 does not; `lbuild.sh` l. 164 allowlist |
| O19 | ACCEPT | §3.4 opencode sentence marked history; §3.2 "must be updated" turned into history (F9 DONE); §1 schema field replaced by "est. agent-active / est. TITAN runs" | F9 DONE in §8; opencode dropped (§5.1) |
| O20 | ACCEPT | Haiku axiom-list WP returns the list in its report, stage master writes files (§5.1, §9.2, §2 row, §4.3); hygiene WP = sonnet (+1 opus fix) (§5.1, F17) | §2 "integration branch: stage master only" vs §4.3 "(or the haiku WP) writes the files" |
| O21 | ACCEPT | §5.2: "on Fabian's node (never remote-eligible); Lean checks via TITAN as for all WPs" | §4.2 "no local Lean" |
| O22 | ACCEPT | Gate spec states `expected = <# of #print axioms lines>` and TITAN reports printed vs expected; covered mechanically for batches by the counter tool fix | Stage-1 L14 failure (12 unqualified names) |

Counts: 21 ACCEPT, 1 MODIFY (O11), 0 REJECT.

## Actions outside plan/
Tool changes (named kickoff items of the stage-02 X1 WP, done on its impl branch, verified in `int1`; `lean/Langlandscape/tools/`):
1. S02-X1 tool fix: axiom counter in `titan_batch.sh` (O2, O15, O22).
2. S02-X1 tool fix: docstring pattern in `check_wp.sh` (`s[0-9][0-9]-`; decide test exemption, default none) (O8).
3. S02-X1 tool fix: vendor path mapping in `titan_batch.sh` (O18, low priority until stage 04).

Global-master rule edits on `main` (F18 in OVERVIEW §8; launch condition for S02):
4. `agents/rules/resources.md`: TEMPORARY job flow -> file outbox; Abhijit 16 GB node row and budget (O9, O12).
5. `agents/rules/git.md`: add area `plan`, branch `wip-implementation` and the `impl/ exp/ titan-in/ titan/ abhijit/` families (O9).
6. `agents/roles/global_master.md`, `agents/roles/coordinator.md`, `CLAUDE.md`: opencode/muse/mistral marked "not used as implementer" (O9).
7. `agents/rules/lean.md` l. 22: docstring line per OVERVIEW §3.6 (O8, O9).
8. (Optional) edit `plan/implementation/EXPERIMENT_PROTOCOL.md` §1/§7 and `briefs/common.md` l. 31; the OVERVIEW header already overrides them.
