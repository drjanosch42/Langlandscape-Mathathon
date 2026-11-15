<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S06 common brief (every stage-06 worker reads this first)

Stage master: stage-6 implementation master. Integration branch `wip-implementation` (worktree /home/janosch/dev/Langlandscape-wt/impl,
stage master only). Read files of other branches with `git show <branch>:<path>`; never cd into or edit another worktree.

1. **Work only in your assigned worktree and branch.** Never push, never merge into `wip-implementation`, never touch the
   worktrees `acc-b34`, `hacsA`, `impl`, `s06-int`, any other agent's worktree, or the main checkout. Commit on your branch:
   `<area>: <imperative summary>` + trailer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` (or your model).
2. Read: `CLAUDE.md`; `agents/rules/{lean,frozen,licensing}.md` (Lean) or `{mathematics,code,talk}.md`; `plan/implementation/stage-06.md`
   (§0, your row in §1, §1 "Signatures"); the launch note `plan/implementation/stage-06-launch.md` once it exists (binding amendments;
   it overrides stage-06.md where they differ); the maths in `plan/staged/stage-06-integral-defect.tex` and the chapter
   `mathematics/chapters/s06*` (on `abhijit/s06-math` d8b08ab until X1 merges it).
3. **Lean: NO local builds** (no `lake`, no `tools/lbuild.sh`/`lfile.sh` on localhost: resources.md TEMPORARY). Acceptance is the
   TITAN/CONCEPTD integration round (TCHK). Draft carefully: check every Mathlib name/signature by grepping the frozen Mathlib sources
   (`/home/janosch/data/mathlib4_v4350/Mathlib`, read-only) and our tree; never guess lemma names. Frozen-tree rules: never write there.
4. **Frozen Lean conventions (this stage):** exact Mathlib-style header (lean.md); module layout: header, `module`, imports, `/-! … -/`,
   `@[expose] public section`, `namespace …`, if every import is a module (files importing GL2TF/AlgJL, directly or transitively via a
   non-module file, stay non-module: check the imported files' first lines); public/private import split (proof-only deps = plain
   `import`); **minimal imports** (no umbrella imports; import the narrowest files that provide what you use; list them in the report);
   docstring layout (docstring directly before the declaration, attributes between, `include … in` above, no docstring line starting
   with `theorem`/`lemma`/`def`); every theorem/lemma (also private, also tests) has a `/-- … -/` containing a label `s06-…`
   (the `mathematics/` label); public defs/structures have docstrings; no `sorry`/`admit`/`axiom`/`native_decide` in the final commit
   (a skeleton commit with `sorry` stubs is allowed on your impl branch only, declared as "skeleton" in its message); hypotheses are
   `def … : Prop` in `Langlandscape/Hyp/`, explicit arguments, never instances.
5. Test files (`LanglandscapeTests/…`): fully qualify or `open` every namespace used, re-check every binder/hypothesis name against
   the library statement (S04 lesson 1: test scope errors cost four rounds).
6. Do NOT edit: root aggregators `Langlandscape.lean`/`LanglandscapeTests.lean`, `HYPOTHESES.md`, `SORRIES.md`, `tools/`, `.titan/`,
   lakefile/manifest, import lines of pre-existing files (the stage master owns them). Tell the stage master what to add.
7. Avoid S04 pitfalls: never unfold `BG`/`ZX`/`ordPart` by `rfl`/`whnf`-heavy `exact`; state generic `Submodule` lemmas first; avoid
   quotients of coerced submodules.
8. Report (final message, short): branch + sha; files; every new declaration fully qualified (for the axiom files); the import list
   per file; module or not; open risks. Long material goes to a file on your branch.
9. Pre-checks before every commit: `plan/implementation/briefs/s04-worker-lean.md` (pre-check list, incl. 7 tests, 8; deprecated/
   version-dependent eliminators: S05 lesson 9 — `TensorProduct.induction_on` has no `zero` arm in this Mathlib, `push_neg`, `haveI`,
   unknown constants: grep each one). No unfolding of `BG`/`ZX`/`ordPart`; use the named bridge lemmas.
10. Create your worktree yourself with `git -C /home/janosch/dev/Langlandscape-wt/impl worktree add <path> -b <branch> <base>`
    under `/home/janosch/dev/Langlandscape-wt/` (path and branch given in your brief); no `.lake` seeding needed (no local builds).
    Never `git rebase`, never `git pull --rebase`; integrate with plain `git merge`.
