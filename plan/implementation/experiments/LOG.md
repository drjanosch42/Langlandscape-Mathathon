# Experiment log — stage 01 model-comparison strands

Protocol: `plan/implementation/EXPERIMENT_PROTOCOL.md`. Raw events: `events.tsv` (append-only). Rows are rendered from
events.tsv by the Haiku logger when a WP is decided, one row per strand; never edit a row except to append to `notes`.

Column conventions
- `strand` = `s01-<wp>-<model>` (branch `exp/s01-<wp>-<model>`); `lbl` = blind audit letter; `base` = start sha (7 chars).
- Times: UTC `HH:MM:SSZ` (date in the stage header line below); `impl` = start–end; `audits` = `r0 s–e; r1 s–e; …`;
  `fixes` = `f1 model s–e; f2 …` (empty if none); `pass` = time of the passing audit's end, or `—`.
- `wall` / `build` / `queue` in minutes (one decimal). `esc` = `none` or `muse→sonnet@r1,…`.
- `f@0` = crit/maj/min of audit r0; `W0` = 3·crit+2·maj+min at r0; `Q0`, `Qf` = rubric 0–10 at r0 / at pass.
- `rnd` = fix rounds; `cost` = cost_idx/class (e.g. `34/A`); `tok` = in/out/reasoning in k (opencode sum of all
  step_finish; Claude task notification total), `—` if unavailable.
- `outcome` ∈ {`winner`, `loser`, `winner(not merged)`, `merged-first`, `timeout`, `failed`, `all-fail`, `stopped`}.
- `sha` = final sha of the strand (7 chars); losers also have `patches/<strand>.patch`.

Stage 01 — date: 2026-11-14 — stage master: stage1-master (Opus) — wip-implementation base: 23eaabb (t=0 15:32Z)

| strand | lbl | wp | track/diff | model | base | impl | audits | fixes | pass | wall | build | queue | esc | f@0 | W0 | Q0 | Qf | rnd | cost | tok | outcome | sha | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s01-x3-haiku | B | E6 | Lean infra / mechanical | haiku | 60da904 | 15:34:51Z–15:36:54Z | r0 15:46:40Z–15:49:26Z | | 15:49:26Z | 14.6 | 1.3 | 0.0 | none | 0/0/4 | 4 | 10 | 10 | 0 | 32/A | — | winner | c23f98d | merged first at b73efd6; active=4.8; vendored Stacks files, acceptance rc 0 |
| s01-x3-mistral | D | E6 | Lean infra / mechanical | mistral | 60da904 | 15:34:44Z–15:41:21Z | r0 15:46:40Z–15:49:16Z | | 15:49:16Z | 14.5 | 0.4 | 0.0 | none | 0/0/2 | 2 | 10 | 10 | 0 | 46/B | 152.3/9.6/16.0 | loser | c3b1914 | no patch (E6 exception); file list `.exp/x3-mistral-files.txt` (git hash-object blob shas); tag `exp-archive/s01-x3-mistral`; active=9.2 |
| s01-l5a-sonnet | F | E2 | Lean / routine | sonnet | 92c7fc3 | 15:34:51Z–15:36:54Z | r0 15:49:57Z–15:51:54Z | | 15:51:54Z | 17.1 | 1.1 | 0.0 | none | 0/0/3 | 3 | 9 | 9 | 0 | 28/A | — | winner | 6417192 | merged first at de06bd0; active=4.0 |
| s01-l5a-muse | D | E2 | Lean / routine | muse | 92c7fc3 | 15:34:44Z–15:45:47Z | r0 15:49:57Z–15:51:54Z | | — | 17.2 | 2.8 | 0.0 | none | 2/0/4 | 10 | 3 | — | 0 | 31/A | 698.8/36.0/50.4 | failed | 1a04b80 | stopped after r0: 2 critical (red check); decision decisive; fix rounds skipped under the no-local-Lean directive; active=13.0; patch `patches/s01-l5a-muse.patch` |

| s01-l9-opus | F | E1 | Lean / hard | opus | c5f10f2 | 15:46:40Z–17:03:42Z | r0 17:03:49Z–17:05:59Z | | 17:05:59Z | 79.3 | — | — | none | 0/1/2 | 4 | 9 | 9 | 0 | 182/C | — | winner | 26dd24b | pass on adjusted audit (A0.1 `.titan` scratch file = stage-master artefact, "adj": W_adj=2, M_adj=0); 1 remote TITAN round; agent time ~16 min (stage master) + audit 2.2; impl window includes TITAN waits; cost from agent time; acceptance check by TITAN, no local Lean |
| s01-l9-sonnet | A | E1 | Lean / hard | sonnet | c5f10f2 | 15:46:40Z–17:03:42Z | r0 17:03:49Z–17:06:27Z | | — | 79.8 | 0.9 | 0.0 | none | 0/1/4 | 6 | 9 | — | 0 | 74/B | — | loser | d326c72 | W_adj=4 (A0.1 not counted), 4 minors >3: not a pass; 4 TITAN rounds (builds 36 s, 10 s, 9 s remote, errs 25/6/3, last ok pending); agent time ~12 min vs opus ~16 (remote latency confound); stopped as decisive, fix round skipped; master fix hints stripped from relays; patch `patches/s01-l9-sonnet.patch` |
| s01-l9-muse | — | E1 | Lean / hard | muse | c5f10f2 | 15:46:40Z–15:51:14Z | | | — | 77.0 | — | — | none | — | — | — | — | 0 | — | — | stopped | — | cancelled: no-local-Lean directive (loop needs local lfile); opencode i1 left running, partial `patches/s01-l9-muse-i1-UpCosets.lean.txt`; no audit; no cost/tokens recorded |
| s01-l13-sonnet | C | E5 | Lean / mechanical | sonnet | eb21aad | 16:21:07Z–17:13:46Z | r0 17:14:14Z–17:15:48Z | | 17:15:48Z | 54.7 | — | — | none | 0/0/1 | 1 | 10 | 10 | 0 | — | — | winner | 2368064 | draft 0.8 min (uncompiled), then 4 TITAN rounds; rounds 1-3 failed on upstream modules (stacked on unverified L11a), own errors: Nat.Prime import, U0 field; agent time not recorded (active and cost n/a); patch restricted to own files; audit 1.6 |
| s01-l13-haiku | F | E5 | Lean / mechanical | haiku | eb21aad | 16:21:07Z–17:14:14Z | r0 17:14:14Z–17:16:10Z | | — | 55.0 | — | — | none | 0/1/3 | 5 | 8 | — | 0 | — | — | loser | 271f496 | draft 2.7 min (uncompiled), 3 TITAN rounds; major finding; stopped as decisive, fix round skipped; agent time not recorded; patch restricted to own files; patch `patches/s01-l13-haiku.patch`; audit 1.9 |
| s01-c1-sonnet | C | E3 | code / routine | sonnet | 1fe260b | 16:53:43Z–16:57:27Z | r0 16:58:02Z–17:00:14Z; r1 17:02:29Z–17:05:17Z | f1 opus 17:00:18Z–17:02:25Z | 17:05:17Z | 11.6 | — | — | sonnet→opus@r0 | 0/0/6 | 6 | 9 | 10 | 1 | 86/B | — | winner | be793d7 | merged first at e6c79ba (pytest 5 passed, sha ae8c4e1); auditor verdict PASS at r0, protocol fail (minor 6>3); active=10.8 |
| s01-c1-mistral | A | E3 | code / routine | mistral | 1fe260b | 16:53:42Z–17:23:43Z | r0 17:24:02Z–17:24:40Z; r1 17:29:26Z–17:32:21Z; r2 17:36:37Z–17:40:02Z | f1 sonnet 17:24:40Z–17:29:25Z; f2 opus 17:32:21Z–17:36:35Z | 17:40:02Z | 46.3 | 0.0 | 0.0 | mistral→sonnet@r0,sonnet→opus@r1 | 4/1/0 | 14 | 0 | 10 | 2 | 221/C | 517.1/11.1/84.5 | loser | ec6edad | impl red: opencode rc=124 at both iterations, empty patch (errs 1, no change); ladder run to opus, passed r2 (W 3, Q 10); active=46.0; patch `patches/s01-c1-mistral.patch` |
| s01-m2-sonnet | C | E4 | LaTeX / routine | sonnet | 49ec93b | 16:56:45Z–16:58:48Z | r0 16:59:20Z–17:01:16Z; r1 17:02:44Z–17:05:00Z | f1 opus 17:01:16Z–17:02:41Z | 17:05:00Z | 8.3 | — | — | sonnet→opus@r0 | 0/0/8 | 8 | 10 | 10 | 1 | 64/B | — | winner | 6f58196 | merged first at 461fc19, follow-up 6f58196 merged; auditor verdict PASS at r0, protocol fail (minor 8>3); active=7.7 |
| s01-m2-muse | A | E4 | LaTeX / routine | muse | 49ec93b | 16:56:47Z–16:58:31Z | r0 17:07:05Z–17:09:39Z | | — | 12.9 | 0.0 | 0.0 | muse→sonnet@r0 (not run) | 2/5/3 | 19 | 2 | — | 0 | 27/A | 95.9/7.0/13.3 | failed | 15f7de5 | impl red (errs 2, no change at iter 2); escalation to sonnet recorded, fix rounds not run (sonnet already passed); active (to r0)=4.3; patch file MISSING from `patches/` |
| s01-m4-opus | F | E8 | LaTeX / hard | opus | 49ec93b | 16:56:45Z–17:06:24Z | r0 17:06:30Z–17:11:09Z | | — | 14.4 | — | — | none | 0/1/4 | 6 | 9 | 9 | 0 | 143/B | — | failed | 86baf11 | top rung, W0=6>5 -> ladder opus→fail (M team report; m.log says active=13); merged first at 86baf11 (M4 6213f20), findings fixed in production as s01-m4fix (8fad90e); active=14.3 |
| s01-m4-sonnet | A | E8 | LaTeX / hard | sonnet | 49ec93b | 16:56:45Z–17:02:12Z | r0 17:02:22Z–17:07:05Z | f1 opus from 17:09:39Z (no end event) | — | 20.1 | — | — | sonnet→opus@r0 | 0/2/6 | 10 | 7 | — | 0 | 69/B | — | stopped | b21dd2e | escalated to opus at r0; fix_end/audit r1 events MISSING (m.log: "still finishing, no production impact"); active (to r0)=10.2; cost excludes the fix; patch file MISSING from `patches/` |

Deviations (stage 01, complete):
- 8-agent limit: more than one experiment Claude slot ran concurrently (Fabian 2026-11-14).
- From about 15:52Z no local Lean: all Lean checks ran on TITAN with round trips of minutes; strands (E5) were stacked on unverified upstream drafts (L11a). Stage master ran strand acceptance builds.
- Fable ran in parallel (late directive).
- Opus audits audited Opus strands (E1, E8 reference): self-preference confound.
- L13 strand patches were restricted to the strands' own files (upstream fixes were merged into them by the stage master).
- The global master's fix hints were stripped from relays (E1 sonnet r2/r3).
- Missing data: agent time per strand for E5 and for E1 (stage-master estimate only); E8 sonnet fix round and audit r1; patches for s01-m2-muse and s01-m4-sonnet; tokens for Claude strands.

Decisions of the stage master (reasons)
- E6 (X3): haiku wins over mistral. Both passed; haiku within tau and cheaper (32/A vs 46/B).
- E2 (L5a): sonnet wins. muse failed r0 with 2 critical findings; fix rounds skipped because the result was decisive.
- E1 (L9): opus wins. Opus passed with 1 remote round; sonnet needed 4 TITAN rounds, audit r0 W_adj 4 with 4 minors (no pass), stopped as decisive. Confound: sonnet agent time ~12 min vs opus ~16 min; remote build latency under the no-local-Lean directive penalises iterative models. muse cancelled (loop needs local Lean). Finding A0.1 (committed `.titan` scratch) was an artefact of the stage master's instructions, not counted ("adj").
- E5 (L13): sonnet wins over haiku. sonnet passed r0 (W 1, Q 10); haiku had a major finding (W 5, Q 8); stopped as decisive.
- E3 (C1): sonnet wins. mistral's opencode iterations timed out (rc 124) with empty patches; mistral only passed after escalation to sonnet and opus (active 46 vs 11).
- E4 (M2): sonnet wins (only passing strand; muse W 19, 2 critical).
- E8 (M4): PROPOSED (stage master to confirm): all-fail / no winner under protocol 4.3. opus (reference) failed at the top rung (W0 6 > 5, findings fixed in production as s01-m4fix); sonnet W0 10, Q 7, escalated, no result recorded.

Stage 02 — date: 2026-11-14 — strand base: ca91787 (setup 18:54:12Z) — stage master: not recorded in events.tsv. Audits by Fable (weight 20).

| strand | lbl | wp | track/diff | model | base | impl | audits | fixes | pass | wall | build | queue | esc | f@0 | W0 | Q0 | Qf | rnd | cost | tok | outcome | sha | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s02-l1-sonnet | D | E1 | Lean / hard | sonnet | ca91787 | 18:54:29Z–19:17:05Z | r0 19:25:12Z–19:26:59Z; r1 19:33:01Z–19:34:26Z | relay sonnet 19:22:35Z–19:22:56Z; f1 sonnet 19:26:59Z–19:27:27Z | 19:34:26Z | 40.0 | — | — | none | 0/0/5 | 5 | 9 | 9 | 1 | 158/C | — | winner(not merged) | a5c78d0 | winner=s02-l1-sonnet, merged=s02-l1-opus; active=26.62 (impl 22.60 + audit 3.20 + fix 0.82); relay fix counted in fix_min, not as a round; passed off-regime (challenger sent alone at t+30, see Deviations); impl_end→audit_start gap 8.1 min unassigned (TITAN waits) |
| s02-l1-opus | F | E1 | Lean / hard | opus | ca91787 | 18:54:29Z–19:23:32Z | r0 19:25:12Z–19:27:10Z; r1 19:33:01Z–19:34:51Z | f1 opus 19:27:10Z–19:30:29Z (planned opus fix, stage plan; not an escalation) | 19:34:51Z | 40.4 | — | — | none | 0/0/6 | 6 | 9 | 10 | 1 | 400/C | — | loser | 283e3a0 | merged-first at c6900a9, follow-up da02f28 (merged; downstream WPs built on it); decision winner=s02-l1-sonnet, merged=s02-l1-opus; active=36.17 (impl 29.05 + audit 3.80 + fix 3.32); impl_end→audit_start gap 1.7 min unassigned (TITAN waits) |
| s02-m1-sonnet | E | E4 | LaTeX / routine | sonnet | ca91787 | 18:54:29Z–18:57:16Z | r0 18:57:28Z–18:59:39Z; r1 19:00:50Z–19:02:47Z | f1 opus 18:59:39Z–19:00:47Z (escalated sonnet→opus@r1) | 19:02:47Z | 8.3 | — | — | sonnet→opus@r1 | 0/1/4 | 6 | 9 | 10 | 1 | 105/B | — | winner | 6688575 | merged 8ea1a57; sole passing strand; active=8.05 (impl 2.78 + audit 4.13 + fix 1.13) |
| s02-m1-opus | C | E4 | LaTeX / routine | opus | ca91787 | 18:54:29Z–18:59:26Z | r0 18:59:28Z–19:02:21Z | — | — | 7.9 | — | — | none | 0/0/6 | 6 | 9 | — | 0 | 107/B | — | failed | 1faf46d | challenger, single shot, no fix; stop reason=fail at r0 (minor 6 > 3); active=7.83 (impl 4.95 + audit 2.88); wall = stop − impl start; loser patch not written in this run |

Deviations (stage 02):
- E1 regime not paired in round 1: challenger s02-l1-sonnet sent alone at t+30 (note 19:20:57Z, global-master decision that the experiment must not block the critical path); reference's first TITAN job one round later (b-1 19:25:02Z vs a-1 19:22:35Z). The challenger's pass event is flagged off-regime.
- TITAN build events carry no `s=` / `queue=` values, so build and queue are `—`. Build waits are excluded from active. The gaps between impl_end and audit_start (sonnet 8.1 min, opus 1.7 min) contain them and are in no phase, so they enter wall only.
- E1 sonnet's relay fix (pre-audit, 0.35 min) is counted in fix_min but is not an audit round; rnd = audit rounds only.
- Audit minutes are Fable audits (weight 20) and are included in active and cost_idx for every strand.

Decisions (stage 02)
- E1 (S02-L1): winner = s02-l1-sonnet by §4.1. active sonnet 26.62 (A); τ = max(0.15·26.62, 5) = 5.00; opus 36.17 > 31.62, so sonnet wins on speed alone. Cost 158/C vs 400/C agrees (quality not needed: Qf 9 vs 10). Merged = s02-l1-opus (merged first at c6900a9, follow-up da02f28), because downstream WPs had built on it; no challenger merge.
- E4 (S02-M1): challenger s02-m1-opus failed r0 (single shot, minor 6 > 3). s02-m1-sonnet is the only passing strand and wins (active 8.05, cost 105/B); merged 8ea1a57.

Stage 03 — date: 2026-11-14 — strand base: 7ac603f (setup 20:21:25Z) — stage master: S03 M-track sub-coordinator (Opus). Audits by Opus (weight 10); confound: Opus audits an Opus strand.

| strand | lbl | wp | track/diff | model | base | impl | audits | fixes | pass | wall | build | queue | esc | f@0 | W0 | Q0 | Qf | rnd | cost | tok | outcome | sha | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s03-m2-opus | D | S03-M2 | LaTeX / hard | opus | 7ac603f | 20:21:25Z–20:33:11Z | r0 20:34:03Z–20:38:38Z; r1 20:40:02Z–20:43:37Z | f1 opus 20:38:38Z–20:39:59Z | 20:43:37Z | 22.2 | — | — | none | 0/0/5 | 5 | 9 | 9 | 1 | 213/C | 257.9k | winner | f01aec5 | protocol deviation (approved by stage master): external-check.md (C3, code/results/s03/T2.json acceptance_note: coker αα† = 5 only on degree-0 part) added to every blind audit input; auditors' self-declared PASS overridden by protocol rule (minor ≤ 3). Audit reports: plan/implementation/experiments/audits-s03-m2/ on impl/s03-m. r0 FAIL W=5 (0/0/5) → f1 → r1 PASS W=3 (0/0/3), 5 prior RESOLVED; remaining 3 minors → S03-M9. |
| s03-m2-fable | A | S03-M2 | LaTeX / hard | fable | 7ac603f | 20:21:25Z–20:28:52Z | r0 20:37:58Z–20:41:29Z | | — | 20.1 | — | — | none | 0/0/4 | 4 | 10 | — | 0 | 184/C | 144.1k | failed | ec9e94f | protocol deviation (approved by stage master): external-check.md (C3, code/results/s03/T2.json acceptance_note: coker αα† = 5 only on degree-0 part) added to every blind audit input; auditors' self-declared PASS overridden by protocol rule (minor ≤ 3). Audit reports: plan/implementation/experiments/audits-s03-m2/ on impl/s03-m. r0 W=4 (0/0/4), Q0=10; would pass with one fix round; decision §4.3: exactly one passing strand → opus wins. |

Decision S03-M2 (E8): winner=opus, merged=opus. Cell LaTeX hard: opus + planned fix passes; fable single-shot fails on minor count only (Q0 10 vs 9).

Stage 04 — date: 2026-11-14 — E1′ (S04-L6), strand base: 0031e78 (setup 21:31:50Z) — stage master: S04 master. Audits by Fable (weight 20), blind labels D = opus strand, B = sonnet strand. TITAN waits are not agent-active; no build/queue events (`—`).

| strand | lbl | wp | track/diff | model | base | impl | audits | fixes | pass | wall | build | queue | esc | f@0 | W0 | Q0 | Qf | rnd | cost | tok | outcome | sha | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s04-l6-opus | D | S04-L6 | Lean / hard | opus | 0031e78 | 21:31:50Z–21:47:07Z | r0 22:15:30Z–22:19:13Z; r1 22:32:33Z–22:33:49Z | relay f 21:55:28Z–21:56:20Z, 22:10:51Z–22:11:15Z; f1 opus 22:19:13Z–22:24:00Z | 22:33:49Z | 62.0 | — | — | none | 0/0/4 | 4 | 9 | 9 | 1 | 313/C | — | loser (merged) | a289461 | winner=s04-l6-sonnet, merged=s04-l6-opus (a289461, before the decision, deviation 5); active=26.32 (impl 15.28 + relay fixes 1.27 + audit 4.99 + fix 4.78; estimates, see notes); 3 remote rounds (10 errors; lib green + 3 test errors; PASS); r0 auditor PASS, protocol FAIL (minor 4>3), same-model fix; r1 PASS W=2 (0/0/2), Q 9; final sha of fix = 79fa5a3, merged head a289461 is the round-2 green head (see Notes) |
| s04-l6-sonnet | B | S04-L6 | Lean / hard | sonnet | 0031e78 | 21:31:50Z–21:41:17Z | r0 22:15:30Z–22:16:50Z; r1 22:32:33Z–22:33:59Z | relay f 21:55:28Z–21:56:20Z, 22:10:51Z–22:11:05Z; f1 opus 22:19:13Z–22:24:00Z | 22:33:59Z | 62.2 | — | — | sonnet→opus@r0 | 0/0/6 | 6 | 9 | 10 | 1 | 145/B | — | winner(not merged) | b0552f3 | active=18.09 (impl 9.45 + relay fixes 1.10 + audit 2.76 + fix 4.78); 3 remote rounds (2 errors; lib green + 1 test error; PASS); r0 auditor PASS, protocol FAIL (minor 6, W=6>=6) so escalated sonnet→opus; r1 PASS W=3 (0/0/3), Q 10; cost = sonnet 10.55 min x4 + opus fix 4.78 x10 + Fable audits 2.76 x20; patch not written (strand a is the merged artefact; sonnet sha b0552f3 is the strand head) |

Notes (E1′ S04-L6):
- Setup 21:31:50Z, both strands same minute, brief_sha 738389f1, identical brief; regime E1prime (paired, TITAN remote builds).
- Agent-active minutes are ESTIMATES from event timestamps. impl = impl_start→impl_end (first declared draft; the opus draft ends 5.8 min later than the sonnet draft). Relay fixes (round 1/2) have only a relay and a fix_end event, so the window relay→fix_end is counted in fix_min (as the S02-L1 relay fix); these are short (a 0.87 + 0.40, b 0.87 + 0.23). The audit-driven fix (f1) is 22:19:13Z–22:24:00Z for both (4.78 min), run by opus in both strands. TITAN waits (impl_end→remote_result, relay→remote_result, fix_end→remote_result) are in wall only, not in active.
- Remote rounds (TITAN): a: r1 rc=1 10 errors, r2 rc=1 3 errors (library builds), r3 PASS 22:15:05Z, r4 (post-fix) PASS 22:32:03Z. b: r1 2 errors, r2 1 error (library builds), r3 PASS 22:15:05Z, r4 PASS 22:32:03Z. Both strands thus needed the same number of remote rounds to first green; sonnet had fewer errors per round.
- Audit r0: both auditors PASS, protocol FAIL on minors (a: 0/0/4 W=4 Q=9; b: 0/0/6 W=6 Q=9). Ladder §2.4: a same-model fix (crit 0, W 4 <= 5, r=0); b escalated sonnet→opus (W 6 >= 6). Audit r1: a PASS W=2 (0/0/2) Q 9 (correctness 4, maintainability 1: `_mk` proofs by rfl/rw, residual A1.1 open); b PASS W=3 (0/0/3) Q 10 (maintainability 2). All r0 findings of b RESOLVED, one finding of a (A0.2) OPEN; Round 4 acceptance (TITAN) PASS for both.
- Audit r0 durations differ (a 3.72 min, b 1.33 min) although both started at the same second; both are counted in active as logged.
- Cost (nominal weights, protocol §3; audits are Fable, weight 20): opus strand 313/C = (impl 15.28 + relay 1.27 + fix 4.78) x10 + audit 4.99 x20; sonnet strand 145/B = (impl 9.45 + relay 1.10) x4 + opus fix 4.78 x10 + audit 2.76 x20. Escalation credited per §2.4: quality to the strand, cost to all models used.
- Merged artefact: strand a head a289461 (round-2 green head, opus) was merged as production L6 before the decision (deviation 5; precedent S02-E1) because L9/L10/L12 were blocked on L6. The sha column of s04-l6-opus therefore shows the merged head a289461; the post-audit fix commit is 79fa5a3 (fix_end r=1). Verify at merge-follow-up that the follow-up carries 79fa5a3 (not decided here).
- Tokens: not recorded for either Claude strand.

Decision E1′ (S04-L6): winner = s04-l6-sonnet (escalated sonnet→opus@r0), merged = s04-l6-opus (a289461); both passed. §4.1: A = sonnet active 18.09; τ = max(0.15 x 18.09 = 2.71, 5) = 5.00; opus active 26.32 > 18.09 + 5.00 = 23.09, so sonnet wins on speed alone. Quality equivalence is not needed but holds anyway: |Qf 10 − 9| = 1, correctness 4 = 4, both mechanical checks ok, no sorry, standard axioms only; no open debt flagged major. Cost 145/B vs 313/C agrees. Sensitivity: excluding audits (impl + fixes only) sonnet 15.3 vs opus 21.3, still outside τ (>20.3); the margin is dominated by the implementation draft (9.5 vs 15.3 min). Merged ≠ winner: production consumed the opus strand before the decision (the experiment outcome and the merged artefact are kept apart, §4.4).

Confounds (E1′ S04-L6):
- Production L6 rescue writer (opus, impl/s04-l6, started ~22:02Z, deviation 1; no strand code read, so no contamination of code) ran in parallel from round 1: a confound for wall and for TITAN latency/queue (more concurrent jobs), not for code or quality; wall (62.0 vs 62.2) is not interpretable and the decision uses active.
- Merged ≠ winner (deviation 5): the opus head was merged before the decision, so the sonnet strand was never the production artefact; it wins on the protocol only.
- Active minutes are estimates from event timestamps (no per-agent timers); the opus draft time includes the interval between the sonnet and opus first-draft ends; the relay fix windows are short and coarse; no build/queue/tokens data (TITAN, `—`).
- Auditor Fable (weight 20), not Opus: no self-preference for the Opus strand, but the auditors are not the S01 auditors; both strands got the same auditor model and the same template; blind labels D/B.
- Audit-r0 durations differ between the two audits (3.72 vs 1.33 min), which enters active and cost; the audit order and the "PASS refers to exactly this patch" caveat of audit D (check output could not be tied to the patch) apply to D only.
- r0 protocol FAIL on minor count for both (auditor PASS, minors > 3); the sonnet strand's win relies on an opus fix round (planned in stage plan; escalation by W=6 rule), so the winner is "sonnet + one opus fix", not sonnet alone.
- n = 1 comparison for this WP; Lean hard WPs in S04 may differ in difficulty (L6: index/quotient algebra over Z_p, Mathlib only; cf. L9).

Stage 05 — E5′ (S05-L4), strand base: a46532bb (strands started together, impl_start 23:53:36Z sonnet / 23:53:45Z opus, 2026-11-14) — stage master: not recorded in events.tsv. Lean mech.-with-meaning, stacked on unverified drafts; paired remote builds on CONCEPTD. Audits by Fable (weight 20), blind labels B = sonnet strand, D = opus strand. Remote r1/r2 and audit r0 times are not in events.tsv (untimed; see notes). Brief: S05-L4 row + `plan/implementation/briefs/s05-common.md`.

| strand | lbl | wp | track/diff | model | base | impl | audits | fixes | pass | wall | build | queue | esc | f@0 | W0 | Q0 | Qf | rnd | cost | tok | outcome | sha | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| s05-l4-sonnet | B | S05-L4 | Lean / mech.-with-meaning | sonnet | a46532b | 23:53:36Z–00:08:52Z | r0 Fable (untimed); remote r1 s05-e5-B-1 FAIL (4 errors) | opus 00:12:33Z–00:14:02Z (37228dcf) | untimed (remote r2 s05-e5-B-2 PASS 24/24) | — | — | — | sonnet→opus@r1 | 0/0/3 | 3 | 6 | 6 | 1 | — | — | winner | 37228dc | active=16.8 (impl 15.27 + opus fix 1.48; audits and remote builds not timed, excluded); merged before the decision as first green head 37228dc (deviation, see notes); r0 audit PASS W 3 (0/0/3), Q 6; cost not computed (audit time untimed) |
| s05-l4-opus | D | S05-L4 | Lean / mech.-with-meaning | opus | a46532b | 23:53:45Z–00:20:23Z | r0 Fable (untimed); remote r1 s05-e5-D-1 FAIL (2 errors) | opus (same model) 00:24:20Z–00:25:12Z (f24c43eb) | untimed (remote r2 s05-e5-D-2 PASS 38/38) | — | — | — | none | 0/0/2 | 2 | 7 | 7 | 1 | — | — | loser | f24c43e | active=27.5 (impl 26.63 + fix 0.87; audits and remote builds not timed, excluded); not merged; r0 audit PASS W 2 (0/0/2), Q 7; cost not computed (audit time untimed) |

Decision E5′ (S05-L4): both strands passed (remote r2 green, blind audit r0 PASS). winner = s05-l4-sonnet (sonnet + one opus fix round), merged = s05-l4-sonnet (37228dc, merged at that head before the decision as the first green head; "merged ≠ winner" was not in play here). §4.1: A = sonnet active 16.8; τ = max(0.15 x 16.8 = 2.52, 5) = 5.00; opus active 27.5 > 16.8 + 5.00 = 21.8, so sonnet wins on speed. Quality comparable: Q 6 vs 7, W 3 vs 2; both within the pass criterion (no crit/maj, ≤ 3 minor). Sensitivity: impl + fix only (the basis here, since audits and remote builds are untimed) gives the same ranking.

Confounds (E5′ S05-L4):
- n = 1 comparison for this WP.
- Production rescue writer (opus, impl/s05-l4) ran in parallel with both strands; it is not part of the experiment, but it adds load on the remote builds and the agents' wall time. Wall and build/queue are not recorded (`—`); the decision uses active.
- Both instances are conditional on unverified upstream definitions (ToyTateData / ToyTateInput); the auditor counted these as minor. The auditor read "witnessed" as a hard requirement, so both strands would fail under that reading and the ranking is unchanged.
- Active minutes are estimates from event timestamps: impl + fix only. Audit and remote-build times are not in events.tsv, so they are excluded for both strands; the cost index is not computed for the same reason.
- No tokens recorded for either strand.
- Merge timing: the sonnet head was merged before the decision (first green), which is the usual precedent for stacked production WPs; the decision does not rely on it.
- Event log: remote r1/r2 and audit r0 times were not passed to the logger, so they are not in events.tsv; the `pass` line for s05-l4-b was written with the fix_end timestamp as a placeholder and corrected by a following `note` event (same timestamp, reason stated).
