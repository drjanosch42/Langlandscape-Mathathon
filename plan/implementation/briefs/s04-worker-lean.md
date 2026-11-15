<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Common brief: stage-04 Lean WP worker (S04-L*)

You implement one Lean work package (WP) of stage 04 of team Langlandscape (Jacquet–Langlands formalization:
ordinary projector, Hida control, Λ-adic Ribet sequence).

**Where.** Your worktree `/home/janosch/dev/Langlandscape-wt/s04-<wp>` on branch `impl/s04-<wp>` (created from
`BASE_S04` = the sha in your task message; it contains stages 1–3 and the merged s04 chapter). Work and commit only there.
**Work ONLY inside your assigned worktree path; if it does not exist, STOP and report — never fall back to another
checkout (in particular never the main checkout /home/janosch/dev/Langlandscape).** Never switch branches, never push,
never merge, never rebase.

**Read first.** `CLAUDE.md`; `agents/rules/lean.md`, `agents/rules/frozen.md`, `agents/rules/licensing.md`;
`plan/implementation/stage-04.md` §0.2 (fixed decisions D-e, D-lim, D-Λ, coefficient ring, connectivity, layout — binding),
§0.3 (stage-1 API, upstream exports), §0.4 (hypotheses), and **your WP row(s) in §1** (binding: file names, declaration
names, argument order, statement shapes); `plan/implementation/audits/stage-04-final-pass.md` (re-bound upstream names, if
present); the tex statements in `plan/staged/stage-04-lambda-adic.tex` and the merged chapter `mathematics/chapters/s04/*.tex`
(cite its labels). Upstream WPs you stack on: read their files on the branches your task message names (drafts may change; the
names and shapes in §1 are binding — code against the declared §1 signature, not against draft internals).

**Rules.**
- No local Lean: **never run `lake`, `lbuild.sh`, `lfile.sh`, `check_wp.sh`, or `lean`** (all builds run on the remote build
  nodes through the stage master). Write carefully against Mathlib/upstream API by reading source: Mathlib at
  `/home/janosch/data/mathlib4_v4350` (read-only; grep it to confirm every name and signature you use), our code in
  `lean/Langlandscape/Langlandscape/**`, the import in `lean/trace-formula-project-import/lean/**` (read-only).
- **Create exactly the file(s) of your §1 row**; create no other module; do not edit `Langlandscape.lean`,
  `LanglandscapeTests.lean`, `SORRIES.md`, `HYPOTHESES.md`, `Audit/PrintAxioms.lean`, tools, or another WP's file.
- No `sorry`, `admit`, `axiom`, `native_decide`, no global instances for hypotheses; hypotheses are explicit `Hyp.*`
  arguments. Never `open Graph` (clash with Mathlib's `_root_.Graph`).
- **Docstring rule (exact, machine-checked):** every `theorem`/`lemma`, including `private` ones and those in
  `LanglandscapeTests/`, has an immediately preceding `/-- … -/` containing a label `s04-…` (or `s01-…` for carry-over
  items), e.g. "`lem:s04-ekills`(a) (`s04-ekills`)". Public `def`/`structure`/`instance`/`abbrev` also get one (audited).
- **Pre-check before every commit (lessons of stage 3 — each one cost rounds):**
  1. every `import Mathlib.X.Y` exists as `/home/janosch/data/mathlib4_v4350/Mathlib/X/Y.lean` (check with `ls`); every
     `import Langlandscape.…` exists in the tree or is a declared upstream WP file;
  2. `noncomputable` on every def that uses `Classical`, `Finsupp`/`MonoidAlgebra` lifts, `linearProjOfIsCompl`, inverses, …
     (or `noncomputable section`);
  3. propositionally equal levels/subgroups/types are transported explicitly (`▸`, `Equiv.cast`, a stated `Eq` lemma), never
     assumed defeq; no `Nonempty.casesOn`/`Nonempty.some` into data without `Classical`; `DecidableEq` instances provided;
  4. a docstring sits *directly* before its declaration (attributes like `@[simp]` go between docstring and declaration); `include … in` goes **above** the docstring;
  5. do not mix the `BG`-typed (`Tree.BG`, `Graph.WGraph`) and `ZX`-typed (`Brandt.ZX`, `X →₀ R`) modules without an explicit bridge;
  6. names you use exist with the argument order you assume (grep the declaration, read its binders).
  7. **tests** (4 S04 rounds were lost on this): the test file is built in the same round as the library; fully qualify or `open` the
     library namespace (e.g. `Langlandscape.Tree.BG`, not `Tree.BG`, outside `namespace Langlandscape`); every hypothesis used only
     inside a test proof is bound explicitly (theorem argument or `include h in` above the docstring); `open Pointwise` for `•` on sets;
  8. never let `rfl`/`decide`/`simp`/`exact` unfold `Tree.BG`, `ZX`, `deg0` or `ordPart` (whnf timeouts); bridge BG↔ZX only by named lemmas
     used with `rw`; give explicit `(R := …) (M := …)` where a submodule-of-submodule is involved; give every `def` its full type.
- Keep proofs robust (no raised heartbeats without reason; prefer explicit `rw`/`simp only`/`exact`). If a binding signature
  in §1 cannot be stated as written, keep the name, make the minimal change, and report it (the stage master re-binds).
- **Header (agents/rules/lean.md, new):** every new Lean file starts exactly with
  ```
  /-
  Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Fabian Januszewski, Abhijit A J
  -/
  ```
  (no SPDX lines). Imports: import what your file needs, never `import Mathlib` or other umbrella imports; minimised imports are a merge gate (done by the separate WP S04-IMP, not by you). No docstring line may start with
  `theorem`/`lemma`/`def`. Files stay non-`module` (the module conversion is a separate WP).
- Commit: `git add <your files> && git commit -m "lean: S04-<WP> <summary>"` (only your files; never `git add -A`).

**Fix rounds.** When done, report and stop. The stage master runs your WP on a build node in an integration round and may
send you the error log (path + verbatim errors); then fix, commit, report again.

**Report (≤ 15 lines):** commit sha; declarations delivered (names); deviations from the §1 row; risky spots (names you were
unsure of). Plus: (a) your spec line exactly (`S04-<WP> <file.lean> ...`, paths relative to `lean/Langlandscape/`);
(b) the content of your axiom scratch file (`import` per module + one `#print axioms <fully qualified name>` per public
theorem you deliver); (c) the root-import lines to add (`import Langlandscape.<...>`, `import LanglandscapeTests.S04.<...>`);
(d) a HYPOTHESES.md row if your WP registers a hypothesis ("used by", instances with reason; never a vacuous instance).
