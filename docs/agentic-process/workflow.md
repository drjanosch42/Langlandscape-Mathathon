<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

All times PST (UTC−8). Source logs: all machines on Berlin time (CET, UTC+1), report sources in UTC; converted.

# Workflow

## 1. Phases (master_log.md "Phase plan")
| Phase | What | Who | Output |
|---|---|---|---|
| P0 | test the opencode CLI with Muse Spark Open | Haiku, replaced by Sonnet | `agents/rules/opencode.md` |
| P1 | **staged mathematical plan** from the frozen seed `plan/seed/`: coarse split into 6 stages → parallel Opus stage drafts with literature checks → one **Muse Spark Open audit per stage** → Sonnet/Opus revisers judge each finding (confirmed / partial / rejected) → integration | planning master (Opus), branch `wip-plan` | `plan/staged/` (SPLIT.md, 6 stage tex files, main.pdf 61 pp), `literature/MISSING_LITERATURE.md` |
| P2 | **global Fable seam audit** of all stages (alone), then fixes; read-only Lean scouting (3 Opus scouts via `gh api`) | Fable; seam-fixer (Opus); scout coordinator | `plan/staged/audits/global-fable-*.md`; merge `wip-plan → main` |
| P3 | **implementation plans** for all stages: OVERVIEW (conventions, branches, Lean project layout), per-stage WP tables with DAG and critical path, experiment protocol; Muse audits + revisers | impl-plan master (Opus) | `plan/implementation/` |
| P4 | **Fable audit of the stage-1 implementation plan** (alone), fixes | Fable; stage1-plan-fixer (Opus) | merge `wip-plan → main` |
| P5… | **stage execution**, one stage master per stage; after stage 1 a **re-plan** of stages 2–6 with stage-1 priors | stage masters (Opus); replan master | `wip-implementation → main` per stage |

Human decisions that the agents could not take were applied **provisionally** (marked `\provisional` / "PROVISIONAL global
master") and listed for Fabian in `agents/status/STATE.md`.

## 2. Work packages
WP ids `S<NN>-<T><k>` with track T ∈ {X infra, M maths, L Lean, C code, H HACS, T talk} (OVERVIEW §1). Every WP row names its
inputs, outputs, acceptance check, difficulty class, model and fix-round budget. Tracks are **decoupled**: maths may run ahead of
Lean; the only coupling is that a statement must exist before it is formalized (`orchestration.md`).

## 3. The per-stage loop
1. **Kickoff (X1)**: sync `wip-implementation` from `main`, stubs, aggregator files, drivers, strand briefs.
2. **WPs in parallel** (≤ 8 agents per delegating agent), each in its own worktree on `impl/sNN-<wp>`. Lean WPs **stack on
   unverified drafts** of their upstream WPs instead of waiting (F14).
3. **Batched integration rounds**: the stage master merges several drafts into `impl/sNN-int<k>`, adds a `.titan/` spec commit,
   and writes an outbox file. The global master relays it to TITAN or CONCEPTD (warmest build, free slot). Results come back as
   inbox files with verbatim errors and goal states. Fixed drafts go into the next lettered round (`int1 → int1a → int1b …`).
   One round per cycle amortises the remote round trip of a few minutes.
4. **Merge gate**: a WP is merged into `wip-implementation` only after its spec line passed **on the merged tree**, and only
   with or after its upstream WPs (stacking rule O6).
5. **Early gate (`sNN-gate1`)** as soon as the core Lean WPs are green: all targets, `Audit/PrintAxioms.lean`
   (every declaration's axioms ⊆ {propext, Classical.choice, Quot.sound}), forbidden-token grep, `check_frozen.sh`.
6. **Parallel Fable audits** on the early-gate commit: Lean audit (`agents/roles/lean_audit.md`) ∥ chapter audit
   (`agents/roles/mathematics_chapter_audit.md`). Required remarks become audit-fix WPs in the same stage (F17).
7. **Final gate from scratch** (`sNN-final-1`, unseeded build) after the audit fixes; cross-check on the second node.
8. **Closure** (`agents/roles/milestone_closure.md`): outbox file `…_milestone-closure-sNN.md` (delivered / verification /
   open issues / request) and `runs/sNN.md` (per-WP times, rounds, deviations).
9. **Merge and mirror** (global master): push `wip-implementation`, `git merge --no-ff` into `main` (checks: no `literature/`,
   no `.lake`, no file > 10 MB, frozen paths unchanged), push, fast-forward `wip-implementation`, remove worktrees, then
   `rclone copy` the milestone PDFs to Drive (copy only) and launch the next stage master.

Experiment strands (model study) run inside this loop on 1–2 WPs per stage; see [model-study.md](model-study.md).
Remote WPs for Abhijit's node are sent as batches of packages; Lean drafts from there are accepted only by a build on TITAN or
CONCEPTD (`master_resume.md` §3).

## 4. Frozen-toolchain guards
The Lean toolchain (v4.35.0) and Mathlib (rev `56a00585…`) are frozen on every node (`agents/rules/frozen.md`).
- **Forbidden** for all agents: `lake update`, `lake clean`, `lake exe cache get`, manifest/toolchain edits, writes into the
  frozen Mathlib or its dependency farm. Dependencies are symlinks into the frozen copy.
- **Wrappers only** (`tools/lbuild.sh`, `lfile.sh`, `check_frozen.sh`, `link_deps.sh`, `titan_batch.sh`): they take locks,
  cap memory and check the frozen trees. Nobody calls `lake` directly.
- **Pin guard**: every wrapper checks `tools/pins.sha256` (sha256 of `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`)
  and the absence of `.lake/package-overrides.json` before any `lake` call, and exits **99** on failure; exit 99 means stop and
  alert the global master (`agents/rules/lean.md`). Reason: a missing manifest would make Lake run a full update through the
  frozen farm symlinks.
- **`check_frozen.sh`**: verifies that the frozen trees are untouched; part of every gate. It caught the bad import of
  2026-11-14 12:23 PST (see [lessons.md](lessons.md)).
- Worktree seeding only by `cp -a --reflink=auto` (never hard links); removal only by `git worktree remove` (never `rm -rf`).
- Single exception: Abhijit's node may run a direct `lean` draft check of Mathlib-only files, outputs outside the repo,
  followed by a `find <frozen tree> -newer <marker>` check (`frozen.md`).

## 5. Changes to the loop in stages 3–6 (from `runs/s03.md` … `runs/s06.md`)
- **Pregate**: from S05 on, a full six-step gate on the merged tree *without* the still-open WPs runs at t ≈ 35 min (709/709 in S05, 786/786 in S06), so gate-1 is a short round (S05 6 min, S06 7 min).
- **Audits in parts**: Fable Lean audits run while WPs are still open (S04 three parts, S05 three, S06 two), with in-stage fix WPs (L17a/b/c, L11a/b/c, L15a/b); the final gate is on the tree after the last fix.
- **Rescue writers** for hard WPs at fix-round 2–3 (S03-L2, S04-L6/L12/L4) and escalation to Opus after two failed Sonnet rounds; insurance, never decisive.
- **Two build nodes** from S03: single-WP lettered rounds in parallel; speculative supersets only when a node is free.
- **Cross-account review** as a stage deliverable: batches to Abhijit's node include blind reviews of finished chapters and second readers for conceptual claims.
- **Closure artefacts** unchanged: `…_milestone-closure-sNN.md` plus `runs/sNN.md`; S06 closure and `runs/s06.md` merged post-gate (587ee503, `lean/` unchanged vs 4405815).
- **After stage 6**: a final-integration master (≈ 18:01 PST) works on branch `wip-final` with no Lean changes; target ≈ 2026-11-15 00:00 PST, submission deadline ≈ 2026-11-15 11:45 PST (STATE.md).
- Process decisions by Fabian are recorded in STATE.md "Decisions by Fabian" and applied provisionally until then (FD1, FD2, `q ≡ −1`, HACS).

## 6. External contributions
One Lean result entered the library from outside the agent process, after stage 6. The disclosure, verbatim:

> The discharge of Hyp.RamNrdSurj was drafted by an external model (mistral-large-4-0 via opencode), run by Fabian Januszewski on Abhijit A J's machine, outside our agent process (where opencode is Q&A-only); it was integrated into the library, independently audited (Fable, PASS WITH REMARKS) and gated from scratch by the Langlandscape agents.

Result: `Langlandscape.Hyp.ramNrdSurj_holds (d : DefiniteData) : Hyp.RamNrdSurj d` (*formalized*; standard axioms only), with
`Hyp.ramNrdSurj_of_local`, `Local.exists_nrd_eq_unit_of_ne_two`, `Local.exists_nrd_eq_unit_two`; final gate TITAN
`ramnrd-final-2` at `2323a252`, 840/840 (see [timeline.md](timeline.md), [metrics.md](metrics.md)). Open follow-ups: the `AlgJL`
import in the two `Local/QuatNrd*` files is not minimised; the two files use the non-module layout (their dependencies are not
modules); stale "hypothesis" wording in the docstrings of `Quat/LevelNrd.lean:26` and `Tree/Admissible.lean:48–59`.
