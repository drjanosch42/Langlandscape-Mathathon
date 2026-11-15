# Re-plan of stages 02–06 after stage 1: summary

Date 2026-11-14, branch `wip-plan`. Brief: `briefs/replan-s02-06.md` (conventions A–F). Binding results: `OVERVIEW.md`
(rev. 2 + cross-stage integration), `stage-02.md` (rev. 3, **ready to launch**), `stage-03..06.md` (concrete; final pass before
each launch), `EXPERIMENT_PROTOCOL.md` (stage-02+ amendments). Consistency record: `audits/cross-stage-consistency.md`.

## 1. Process
| step | who | result |
|---|---|---|
| drafters | 6 × Opus (OVERVIEW, stages 02–06) | revised plans + `audits/*-replan-notes.md` |
| adversarial audits | 6 × Opus | OVERVIEW PASS WITH REQUIRED FIXES (0 crit, 22); S02 GO WITH FIXES (1 crit, 13 maj, 12 min); S03 FAIL pre-launch / PASS WITH REQUIRED CHANGES as draft (1 crit, 11 maj, 8 min); S04 NOT READY (1 crit, 6 maj, 12 min); S05 PASS WITH REQUIRED FIXES (0 crit, 10 maj, 15 min); S06 REVISE (1 crit, 11 maj, 11 min) |
| revisers | Sonnet: OVERVIEW, S03, S04, S05; **Opus: S02, S06** (crit/launch-critical findings: S02 launch order A1, S06 `if:s06-lemD` A1) | ACCEPT/MODIFY/REJECT: OVERVIEW 21/1/0, S02 16/10/0 (+ own N1–N11, incl. 1 crit: edge orientation `EdgeO`), S03 15/5/0, S04 18/1/0, S05 24/1/0, S06 16/7/0; total 110/25/0 of 135 |
| integrator | Opus | 30 cross-stage edits, 6 checks, 1 flag (S05-L2b level) |

## 2. Per stage
| stage | WPs | critical path | wall (± range) | strands | remote-eligible | early-startable |
|---|---|---|---|---|---|---|
| 02 | 36 (X 4, L 17, M 8, C 5, T 2; H1 cond.) | 144 min: X1→L4a→L4b→L5b→L6→int4/4a→gate1→L12→L13a→int5→final→X4 | 2.5 h (1.8–3.2) | E1 on L1, E4 on M1 | M2, M3, M5, M8 | — (launch stage) |
| 03 | 34 (X 2, M 9, L 14, C 5, H 1, T 3) | 171 min: X1→L1→L3→L4/L6→gate1→L12→L13+int4→final | 2.85 h (2.2–3.6) | E8 on M2 | M1, M3–M7 | M6 (no deps); L1/L3/L5/L10 only if Q-H |
| 04 | 43 (X 4, M 10, L 20, C 6, H 1, T 2) | ≈ 175 min: X1→L1→L8→L10→L13b→int4b/c→gate1→L16→L17→X4 | 3.0 h (2.6–3.8) | E1′ on L6 (cond.) | M1–M8; += S04-L7, L13a (global master 2026-11-14, Abhijit batch 4) | (L13a Mathlib-only; not planned early) |
| 05 | 31 rows, 27 scheduled | 126 min: X1→L1→L2/L3 skeletons→int1/2a/2b→merge→G1→L10→L11→int3→G2 | 2.1 h (1.5–3.2) | E8′ on M3 (cond.) | M1–M7, R1; += S05-L6, S05-L8 (algebraic half) (global master 2026-11-14, Abhijit batch 5) | — |
| 06 | 53 rows (AW = 16 audits), 48 planned | A 130 min (X1→L8a→L9a→6 runs→gate2→L12→L15→L16); B 154 min | A 2.2 h (1.6–2.9), B 2.6 h (1.8–3.4) | E1′ on L5b (cond., only if S04's undecided) | M1–M8, M11; += S06-L1, L2, L3 (global master 2026-11-14, Abhijit batch 1) | early lane (now started in stage 02, (global master 2026-11-14, Abhijit batch 1)) 2.0 h: X0, XM0, L1–L4, L5a, L5b, L6, L6b, L7, L10a, L13, L14, L17, L18; M1–M8, M11 |
Total ≈ 12.7 h sequential, ≈ 10.6 h with 05 ∥ 06. Every stage: early full gate, Fable Lean ∥ chapter audit, final gate from
scratch, outbox closure; "launchable without Abhijit".

## 3. Model mix (WP rows, all stages; strand pairs and stage-master steps separate)
| | S02 | S03 | S04 | S05 | S06 | total |
|---|---|---|---|---|---|---|
| sonnet (+1 opus fix) | 16 | 21 | 18 | 15 | 19 | **89** |
| opus (+1 planned fix or —) | 13 | 9 | 20 | 12 | 27 | **81** |
| fable (audits, S06-M6 alt.) | 2 | 2 | 2 | 2 | 3 | **11** |
| haiku (axiom lists, C3 pointer) | 1 | 1 | 1 | 2 | 1 | **6** |
| stage master | 3 | — | 2 | — | 3 | **8** |
| strand pair | 2 (L1, M1) | 1 (M2) | — | — | — | **3** |
(S02 counts H1; S06-AW = 1 row of 16 opus audits.) muse/mistral: 0 (dropped as implementers).

## 4. Main changes per stage
- **OVERVIEW:** remote-only Lean via TITAN file outbox, stacking + batched rounds, job-id grammar O16, spec rules (no trailing
  comments, one AXIOMS file per WP), `.titan/` only in a throwaway top commit; §4.4 calibration (factor 0.25, R × 4–8 min);
  §5.1 model table; §5.2 strands; §6.1 remote package branches; F18 rule edits; §7 final; merge-order rule (§4.3).
- **S02:** SA-free Lean core with oriented-edge fix `EdgeO`; trivial-coefficient `partialHom`/two-term complex; per-level
  `SAat`; `BGConnected_of_SA_HS` export; L7 split (L7a/L7b); four-step X1 with all tool fixes before branches; E1 deadline D.
- **S03:** coefficient layer S03-L14 (`alphaV`, `CoeffData`); Ribet/Ihara over any `CommRing R`; `Ψ*Ψ` normalisation fixed;
  no Stacks Frontier vendoring; E8 with protocol override; re-bound to S02 §4.1.
- **S04:** projector design D-e with `Hyp.PadicOrdDecomp` (true, provable) as argument; D-lim (snake lemma, no Weil); `Lam`;
  L13a/b and L14a/b splits; `HsiehGor` and η-principle moved to S06; C3a sign pin.
- **S05:** `Hyp.X.char/gal/iso` shapes (one family φ, FD1 transpose clause); Lemma-D seam with four states; skeleton-first L1–L3.
- **S06:** Mathlib-only CommAlg early lane (from stage 03, merged by the global master before S05-X1); `if:s06-lemD` A-linear
  with `_apply`/`_smul`; `Defect.Setting` data-only; `Hyp.HsiehGor` (L8a), η-principle (L17); WP-audit rows AW.

## 5. Stage-1 lessons and where they are encoded
| lesson | OVERVIEW | stage plans |
|---|---|---|
| early full gates, final from scratch | §9.1, §4.3 gate variant (a)–(f) | S02 L11/L14, S03 gate-1/final-1, S04 X3/X4, S05 G1/G2, S06 gate1+gate2/L16 |
| axiom scratch files (qualified, imports, line join, one per WP) | §4.3, §9.2, S02-X1 `axcount.sh` | S02-X2 `gen_axioms.py`; X2 of S03–S06 (haiku returns text) |
| docstring gate in the round | §3.6, §9.3, S02-X1 `check_wp.sh` `s[0-9][0-9]-` | every plan §0; def/structure docstrings in WP/Fable audits |
| stale strand/WP bases | §9.4, §5.2 | rebase onto fixed heads or `int<k>~1` (S02 §3.2, S03 §3.1, S04 §3, S05 §3, S06 §3) |
| outbox, never SendMessage-only | §4.3 flow, F11, §9.5 | every TITAN section; S06 hand-over file; S02 exports note |
| no fix hints in strand relays | §5.2, §4.3 step 4 | S02 §5, S03 §5.2, S04 §5, S05 §5, S06 §5 |
| `.titan/` never on WP branches (A0.1) | §2, §4.3 (O4) | merge-gate grep in every plan |
| wall calibration 0.25 | §4.4 | every critical path summed with R × 4–8 min |

## 6. Experiment strands
E1 (S02-L1, Lean hard, opus vs sonnet, equal TITAN regime, deadline D ≈ t+58, fable blind audit); E4 (S02-M1, LaTeX
routine, sonnet + budgeted fix vs opus single shot); E8 (S03-M2, LaTeX hard, opus + one planned fix vs fable single shot,
cap 45 min, opus blind audit). Conditional (global master approves per protocol §9): E1′ S04-L6; E8′ S05-M3; E1′ S06-L5b only if
E1 and S04's E1′ leave the cell undecided (one E1′ per project). All strands local, neutral ids `sNN-<wp>-<a|b>-<n>`, neutral
merge message, events incl. `stop reason=deadline` and `build s=;queue=;job=`; tooling: generalised `exp_prepare_audit.sh`.

## 7. Stage-02 launch checklist
1. F18 rule edits (1)–(4) on `main`.
2. `wip-plan` merged to `main` (carries `stage-02.md` rev. 3, the protocol edits and the generalised `exp_prepare_audit.sh` =
   former item 3); `…-wt/impl` fast-forwarded; `plan` worktree removed (`git worktree list` ≤ 3).
3. TITAN idle, `SLOTS=3`, pins unchanged; `origin/titan/s01-final-1` and `origin/impl/s01-int2f` fetched (X1/X2 acceptance).
4. `free -g` ≥ 12 GB + 2 GB per planned agent; no other stage holds TITAN slots.
5. Fabian's defaults stand or are answered; every WP local (O12c).
6. Stage master has §3.3 spec blocks and §3.4 PrintAxioms block ready verbatim; X1 step 1 tool fixes before any branch.

## 8. Actions outside plan/ (global master; details in `audits/cross-stage-consistency.md`)
F18 rule edits (`resources.md`, `git.md`, opencode text in roles/`CLAUDE.md`, `lean.md` l. 22); S02-X1 tool fixes in
`lean/Langlandscape/tools/` (`check_wp.sh`, `axcount.sh`/`titan_batch.sh`, vendor mapping) and S02-X2 `gen_axioms.py`;
merge `wip-plan` → `main`; OK for the S06 early lane by stage 03 and its hand-over merge before S05-X1; the S02→S03 exports
outbox note at S02-X1 step 5; Abhijit stays idle until Q-C is settled.

## 9. Open questions for Fabian (defaults in brackets; full list in the consistency record)
Q-A FD1 μ_N-model [yes; needed before S05-L3 merges] · Q-B FD2 Hsieh erratum [yes, no letter] · Q-C Abhijit transport and
literature [all local until settled] · Q-D strand rules (E1 deadline, E8 merge, one E1′) [yes] · Q-E no new vendoring [drop] ·
Q-F "formalized modulo" hypotheses [yes] · Q-G scope cuts [as planned] · Q-H worktree cap 16, S03 early start [keep 12; no] ·
Q-I licence [open].

*Q-C settled (global master 2026-11-14, Abhijit batch 1):* Fabian gave the early-lane OK and delegated remote implementation to Abhijit (push rights to `abhijit/*` granted; literature transferred out of band). Q-H's "no S03 early start" concerns local worktrees and TITAN slots only; remote maths before S03-X1 uses neither (global master confirms).

