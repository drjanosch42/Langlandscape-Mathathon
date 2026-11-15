# Langlandscape — Jacquet–Langlands @ Caltech × SAIR Mathathon 2026

Team: **Abhijit** and **Fabian**. Topic: the Jacquet–Langlands correspondence — mathematics,
Lean 4 formalization, computations (Python / CAS / HACS), and the final talk.

## Who you are
- If you are the top-level session started by a human, you are the **global master**:
  read `agents/roles/global_master.md` *before doing anything else* and follow it.
- If you were spawned as a coordinator, read `agents/roles/coordinator.md` plus the role file you were pointed to.
- Every agent reads the rule file(s) in `agents/rules/` for each directory it touches.

## Repository layout
| Path | Purpose | Work branch | Rules |
|---|---|---|---|
| `plan/` | implementation planning (maths, Lean, HACS); `plan/seed/` is **frozen** | `wip-plan` | `agents/rules/plan.md` |
| `mathematics/` | mathematical development, LaTeX documents | `wip-mathematics` | `agents/rules/mathematics.md` |
| `lean/` | Lean 4 (toolchain `leanprover/lean4:v4.35.0`) formalization; `lean/trace-formula-project-import/` = curated fork of GL(2)/ℚ + quaternion-algebra material (LaTeX, Lean, LaTeX back-translation) from our GL(2) trace formula project | `wip-lean` | `agents/rules/lean.md` |
| `code/` | computations: `hacs/` (HACS snapshot + JL transfer), `python/`, `cas/`, `examples/`, `results/` | `wip-code` | `agents/rules/code.md` |
| `talk/` | slides / talk material | `wip-talk` | `agents/rules/talk.md` |
| `summary/` | colour-coded six-stage plan/status overview (tex, PDF, HTML); maintained by Abhijit's node on `abhijit/summary`, merged by the global master | `abhijit/summary` | — |
| `docs/` | documentation; `docs/agentic-process/` = the process write-up, kept current by the global master | `main` | — |
| `agents/roles/` | prompts and prompt templates for recurring tasks | `main` | — |
| `agents/rules/` | rules per folder and per procedure | `main` | — |
| `literature/` | literature — **git-ignored, never commit** (repo goes public incl. history) | — | `agents/rules/frozen.md` |
| `agents/messages/{fabian,abhijit}/` | cross-node agent-to-agent inboxes | `main` | `agents/rules/messages.md` |

## Branching (summary — details in `agents/rules/git.md`)
- `main` is the integrated, consistent state. Only the global master merges into `main`.
- Parallel work happens on `wip-mathematics`, `wip-lean`, `wip-code`, `wip-talk`; each branch
  changes **only its own subdirectory** (plus files it is explicitly assigned).
- Parallel work also on `wip-plan` (`plan/`).
- `agents/` changes and messages are committed directly on `main`.

## Tooling
- Claude subagents: Haiku (mechanical), Sonnet (normal), Opus (long-horizon/hard), Fable (audits, Opus failures). Model-vs-task policy and evidence: `agents/rules/model-selection.md`.
- opencode with **Muse Spark Open** and **Mistral Large 4** for bottom-of-tree work: see `agents/rules/opencode.md`. **Not used as implementers (stage-1 study, OVERVIEW §5.1); Q&A only.**
- Lean: `v4.35.0` + matching Mathlib are **fixed and frozen** on each node. `lake update`, `lake clean`,
  `lake exe cache get` and any toolchain/manifest change are **forbidden** for all agents: `agents/rules/frozen.md`.

## Universal conventions
- Never commit secrets, large binaries (> 10 MB) or build artefacts (`.lake/`, `__pycache__/`, LaTeX aux files).
- Licensing (CC-BY-4.0 prose, GPL-3.0-or-later WITH CUDA exception code, SPDX headers, acknowledgments): `agents/rules/licensing.md`.
- State claims with their status: *proved* / *formalized* / *computed* / *conjectural* / *cited (with reference)*.
- Commit messages: `<area>: <imperative summary>`, e.g. `lean: prove local character identity for GL2`.
