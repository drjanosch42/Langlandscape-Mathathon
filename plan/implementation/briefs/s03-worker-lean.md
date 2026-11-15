# Common brief: stage-03 Lean WP worker (S03-L*)

You implement one Lean work package (WP) of stage 02 of team Langlandscape (Jacquet–Langlands formalization).

**Where.** Your worktree `/home/janosch/dev/Langlandscape-wt/s03-<wp>` on branch `impl/s03-<wp>` (created from
`BASE_S03 = 7ac603f`). Work and commit only there. **Work ONLY inside your assigned worktree path; if it does not exist, STOP and report — never fall back to another checkout (in particular never the main checkout /home/janosch/dev/Langlandscape).** Never switch branches, never push, never merge.

**Read first.** `CLAUDE.md`; `agents/rules/lean.md` and `agents/rules/frozen.md`; `plan/implementation/stage-03.md` §0.2
(fixed decisions, binding: layout §0.2.3, sign §0.2.4, coefficients §0.2.7), §0.3 (stage-1 API), §0.4 (stage-02 exports; all names
*verified* present at 7ac603f; note `Tree.BG` is in `Tree/BrandtGraph.lean`), and **your WP row(s) in §1** (binding: file names,
declaration names, argument order, statement shapes); the tex statements in `plan/staged/stage-03-ribet-ihara.tex` and the merged chapter `mathematics/chapters/s03/*.tex` (cite its labels) for the
labels of your row. Upstream WPs you stack on: read their files on the branches your brief names (drafts may change;
the names and shapes in §1 are binding).

**Rules.**
- No local Lean: **never run `lake`, `lbuild.sh`, `lfile.sh`, `check_wp.sh` builds, or `lean`** (localhost is reserved;
  all builds run on TITAN through the stage master). Write carefully against Mathlib/stage-1 API by reading source:
  Mathlib at `/home/janosch/data/mathlib4_v4350` (read-only, grep it to confirm names and signatures), stage-1 code in
  `lean/Langlandscape/Langlandscape/**`, the import in `lean/trace-formula-project-import/lean/**` (read-only).
- **Create exactly the file(s) of your §1 row** (no stubs exist); create no other module; do not edit `Langlandscape.lean`,
  `LanglandscapeTests.lean`, `SORRIES.md`, `HYPOTHESES.md`, `Audit/PrintAxioms.lean`, tools, or another WP's file.
- No `sorry`, `admit`, `axiom`, `native_decide`, no global instances for hypotheses; hypotheses are explicit `Hyp.*`
  arguments. Never `open Graph` (clash with Mathlib's `_root_.Graph`).
- **Docstring rule (exact, machine-checked):** every `theorem`/`lemma`, including `private` ones and those in
  `LanglandscapeTests/`, has an immediately preceding `/-- … -/` containing a label `s03-…` (e.g.
  "`lem:s03-bip`(a) (`s03-bip`)"). Public `def`/`structure`/`instance` also get a docstring.
- Keep proofs robust (no raised heartbeats without reason; prefer explicit `rw`/`simp only`/`exact` over fragile
  automation where a name is uncertain). If a binding signature in §1 cannot be stated as written, keep the name,
  make the minimal change, and report it (the stage master re-binds downstream).
- Commit: `git add <your files> && git commit -m "lean: S03-<WP> <summary>"`.

**Fix rounds.** When done, report and stop. The stage master runs your WP on TITAN in an integration round and may
send you the error log verbatim; then fix, commit, report again.

**Report (≤ 15 lines):** commit sha; declarations delivered (names); any deviation from the §1 row; names you were
unsure of (risky spots for the TITAN round).

**Stage-03 additions.** Your report also gives (a) your TITAN spec line exactly
(`S03-<WP> <file.lean> ...`, paths relative to `lean/Langlandscape/`), (b) the content of your axiom scratch file
(`import` per module + one `#print axioms <fully qualified name>` per public theorem/def you deliver), (c) the root-import
lines to add (`import Langlandscape.<...>` for `Langlandscape.lean`, `import LanglandscapeTests.S03.<...>` for
`LanglandscapeTests.lean`), (d) a HYPOTHESES.md row if your WP registers a hypothesis (owner per §0.2.2; include
"used by" and "instances: none" with the reason; never a vacuous instance).

**Licensing (agents/rules/licensing.md, new 2026-11-14).** Every new file starts (before the imports) with
`-- SPDX-License-Identifier: Apache-2.0` and
`-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team`. Files already written without it get it in
a mechanical pass by the stage master before gate-1; add it yourself in your next commit if you touch the file anyway.
