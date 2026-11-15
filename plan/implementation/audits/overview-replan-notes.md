# OVERVIEW revision 2 (re-planning after stage 1) — change notes

Brief: `briefs/replan-s02-06.md` (conventions A–F). Drafter: OVERVIEW re-planning drafter (Opus), 2026-11-14.
- Header: revision 2; stage-1 text kept as history, marked DONE (stage 1).
- §1: schema gains `model (+fix)`, `TITAN round`, `remote-eligible`; model set {haiku, sonnet, opus, fable} (muse/mistral
  dropped as implementers); Lean acceptance = green `CHECK_WP` + `AXIOMS` lines in an integration round; calibrated sizes;
  aggregator list + `Audit/PrintAxioms.lean`, `references.bib`, `talk/main.tex`.
- §2: branch table adds `impl/sNN-int<k>` (never merged), `titan-in/<job-id>`, `abhijit/<wp>`; `.titan/` merge-gate grep;
  outbox added to the plan/ exceptions; `plan`, `msg` commit areas; old seeding/opencode text removed (lean.md keeps it).
- §3: content unchanged; status lines only: P with seeding regime (a) settled (X1a 9f49151), X1b DONE, §3.5 history;
  §3.6 docstring bullet generalised to sNN labels.
- §4 restructured: 4.1 resources + ≤ 8 subagents + Fable parallel; 4.2 no local Lean (F10), build mechanics, TITAN
  times; **4.3 TITAN** (convention C): outbox flow (5 steps), job-id grammar, int1/int2a/… rounds, priorities, full
  `titan_batch.sh` spec format + summary.txt semantics + nonstandard-counter caveats, axiom-file format, job-spec template
  (from s01 int2* specs) + strand/gate/final variants, what TITAN reports, `.titan/` never on WP branches, X1 tooling
  items (`check_wp.sh` hard-codes `s01-`); **4.4 wall calibration** (convention F): measured table + estimation method.
- §5: **5.1** binding model table (A) + ladders; **5.2** experiment strands (B): E1/E4 in S02, E8 in S03, one conditional
  strand each in S04–S06, equal TITAN regime, local only, neutral refs, no fix hints, auditor ≠ strand model; 5.3 audits.
- §6: stacking, closure file; **6.1** remote-eligible WPs (E): 16 GB node, no Lean, `abhijit/<wp>`, new files only,
  aggregator lines in the report, every stage launchable without Abhijit, local fallback.
- §7: S01 row DONE (measured 2.2 h); 02–06 WP counts + calibrated walls (3.0/3.0/3.0/2.5/3.5 h, ± 0.8–1.0).
- §8: F1 settled, F2/F9 DONE, F3 used, F4 superseded, F5 open, F6/F7 in force; new F10 no local Lean, F11 file outbox,
  F12 8 subagents, F13 model table, F14 stacking, F15 Abhijit, F16 HACS 0.2.1, F17 audit remarks + hygiene carry-over.
- §9: lessons D1–D6 as concrete steps, each with its stage-1 evidence.
Conflicts with rule files (for the global master; rules not edited):
- `resources.md` TEMPORARY job flow = SendMessage "main" with the job spec; brief/F11 = committed outbox file.
- `git.md` commit areas lack `plan` (brief and OVERVIEW use `plan:`).
- `CLAUDE.md`/`opencode.md` present muse/mistral as bottom-of-tree tools; brief drops them as implementers.
- `lean.md` "docstring references mathematics/" vs `check_wp.sh` accepting only `s01-` docstrings (tool gap).
