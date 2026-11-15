<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

All times PST (UTC−8). Source logs: all machines on Berlin time (CET, UTC+1), report sources in UTC; converted.

# The agentic process of team Langlandscape

Team Langlandscape (Abhijit A J, Fabian Januszewski) works on the Jacquet–Langlands correspondence at Caltech × SAIR Mathathon 2026:
mathematics (LaTeX), a Lean 4 formalization (Lean v4.35.0, frozen Mathlib), computations (Python/PARI, HACS) and a talk.
This folder documents **how** the work is done: by a hierarchy of Claude Code agents across four machines, coordinated
through git. It is written for later documentation and for presenting the process itself (slides, write-up).

## Summary (state: 2026-11-14, ~18:10 PST)
A single **global master** session on Fabian's node runs the project autonomously from 2026-11-14 01:20 PST. It delegates every task
to subagents (Opus coordinators; Sonnet/Haiku/Opus workers; Fable auditors). Two helper sessions on other machines (TITAN,
CONCEPTD) run all Lean builds, and Abhijit's node (a separate Claude account) takes work packages and cross-account reviews over a git
message channel. The work went through a staged mathematical plan (6 stages, audited by Muse Spark Open and then by Fable), detailed
implementation plans (audited the same way), and then stage-by-stage execution. In stage execution, work packages (WPs) are
stacked on unverified drafts, checked in batched integration rounds on the remote Lean nodes, and closed by an early full gate,
parallel Fable Lean and chapter audits, and a from-scratch final gate on TITAN with a cross-check on CONCEPTD.
**Outcome:** all six stages are complete and merged on `main`. Final gates from scratch PASS with only standard axioms and 0 `sorry` in our code:
161 / 195 / 519 / 592 / 747 / 836 `#print axioms` lines (stages 1–6); after stage 6, the discharge of `Hyp.RamNrdSurj` (an external
contribution, see [workflow.md](workflow.md)) was gated from scratch at `2323a252`: 840/840; the Lean submission bundle (tree `28d2b091`, gate commit `dc61af50`, TITAN from scratch, CONCEPTD fresh checkout) passed 950/950; the final gate, after the `Hyp.BrandtStabFree` discharge (tree `c70ef3a9`, TITAN bsf-gate-1 from scratch in an unseeded worktree, logs `fa755069`), is **955/955**. Stage walls: 2.2 / 1.3 / 1.1 / 2.2 / 1.1 / ≈ 1.2 h against plans of
8.8 / 2.5 / 2.85 / 3.0 / 2.1 / 2.2–2.6 h. Stage 6's headline theorem `Defect.defect_formula` is *formalized modulo registered hypotheses*,
including the Galois half (`Hyp.FreeRankTwo`), which is disclosed as equivalent to the conclusion of its use. HACS ran as two 1-hour lanes under
a **relaxed protocol** with eight disclosed deviations, all results *computed*, none certified. `main` has ≈ 2058 commits (405 merges). A
model-vs-task study (Haiku/Sonnet/Opus/Fable/Muse/Mistral; five stages of strands, 25 `exp/*` branches) set the model policy in
`agents/rules/model-selection.md`. The **final integration** (report, this folder, talk consistency pass, release notes) was launched at
≈ 18:01 PST on 2026-11-14; the submission deadline is ≈ 2026-11-15 11:45 PST.

## Index
| File | Content |
|---|---|
| [architecture.md](architecture.md) | nodes, agent hierarchy, communication channels, branch families, diagram |
| [workflow.md](workflow.md) | the phases from seed to stage execution; the per-stage loop; frozen-toolchain guards |
| [timeline.md](timeline.md) | dated milestones, wall times per phase/stage (plan vs actual), jobs, gate results |
| [model-study.md](model-study.md) | the model-vs-task experiment: design, results per cell, resulting policy |
| [lessons.md](lessons.md) | incidents: symptom → cause → fix, with dates |
| [hacs.md](hacs.md) | HACS lanes A/B, Fabian's decisions, the relaxed protocol and its disclosed deviations D1–D8 |
| [agentic-process.html](agentic-process.html) | all of the above concatenated in reading order (generated with pandoc) |
| [metrics.md](metrics.md) | counts (commits, merges, WPs, Lean, tests, pages, remote packages, audits), each with source |
| [pst-conversion-log.md](pst-conversion-log.md) | log of the conversion of all clock times to PST (original, zone, evidence, result) |

## Conventions
- All clock times in this folder are **PST (UTC−8)**. Sources: `agents/status/master_log.md` and the git commit times of Fabian's
  node, TITAN, CONCEPTD and Abhijit's node are Berlin time (CET, UTC+1; PST = CET − 9 h); run reports, outbox/inbox file names and message
  file names use **UTC** (suffix `Z`; PST = UTC − 8 h). File names, commit hashes and job ids that contain a UTC stamp are kept
  verbatim. Undated times fall on 2026-11-14 (PST); the conversion is logged in [pst-conversion-log.md](pst-conversion-log.md).
- "(not recorded)" marks a quantity no source records. Numbers carry their source.
- Main sources: `agents/status/master_log.md`, `agents/status/STATE.md`, `agents/roles/`, `agents/rules/`, `plan/staged/`,
  `plan/implementation/`, and on the implementation worktree (`…-wt/impl/plan/implementation/`): `runs/`, `outbox/`, `inbox/`,
  `experiments/`.
- Maintained by the global master; update at each stage closure. Stages 3–6 and HACS were written up on 2026-11-15 by the final-integration lane from the closures, `runs/`, STATE.md and git; quantities no source records are marked "(not recorded)".
- Combined document: regenerate with `pandoc -s --toc -H style-header.html README.md architecture.md workflow.md timeline.md hacs.md model-study.md lessons.md metrics.md -o agentic-process.html --metadata title="The agentic process of team Langlandscape"` (run in this folder).
