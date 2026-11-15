# Common brief: stage-02 Lean WP worker (S02-L*)

You implement one Lean work package (WP) of stage 02 of team Langlandscape (Jacquet–Langlands formalization).

**Where.** Your worktree `/home/janosch/dev/Langlandscape-wt/s02-<wp>` on branch `impl/s02-<wp>` (created from
`BASE_S02`). Work and commit only there. Never switch branches, never push, never merge.

**Read first.** `CLAUDE.md`; `agents/rules/lean.md` and `agents/rules/frozen.md`; `plan/implementation/stage-02.md` §0.3
(Lean conventions, binding), §0.4 (stage-1 API you reuse), and **your WP row(s) in §1** (binding: file names,
declaration names, argument order, statement shapes); the tex statements in `plan/staged/stage-02-*.tex` for the
labels of your row. Upstream WPs you stack on: read their files on the branches your brief names (drafts may change;
the names and shapes in §1 are binding).

**Rules.**
- No local Lean: **never run `lake`, `lbuild.sh`, `lfile.sh`, `check_wp.sh` builds, or `lean`** (localhost is reserved;
  all builds run on TITAN through the stage master). Write carefully against Mathlib/stage-1 API by reading source:
  Mathlib at `/home/janosch/data/mathlib4_v4350` (read-only, grep it to confirm names and signatures), stage-1 code in
  `lean/Langlandscape/Langlandscape/**`, the import in `lean/trace-formula-project-import/lean/**` (read-only).
- **Fill your stub file(s)** (X1 created them); create no other module; do not edit `Langlandscape.lean`,
  `LanglandscapeTests.lean`, `SORRIES.md`, `HYPOTHESES.md`, `Audit/PrintAxioms.lean`, tools, or another WP's file.
- No `sorry`, `admit`, `axiom`, `native_decide`, no global instances for hypotheses; hypotheses are explicit `Hyp.*`
  arguments. Never `open Graph` (clash with Mathlib's `_root_.Graph`).
- **Docstring rule (exact, machine-checked):** every `theorem`/`lemma`, including `private` ones and those in
  `LanglandscapeTests/`, has an immediately preceding `/-- … -/` containing a label `s02-…` (e.g.
  "`lem:s02-tree`(d) (`s02-tree`)"). Public `def`/`structure`/`instance` also get a docstring.
- Keep proofs robust (no raised heartbeats without reason; prefer explicit `rw`/`simp only`/`exact` over fragile
  automation where a name is uncertain). If a binding signature in §1 cannot be stated as written, keep the name,
  make the minimal change, and report it (the stage master re-binds downstream).
- Commit: `git add <your files> && git commit -m "lean: S02-<WP> <summary>"`.

**Fix rounds.** When done, report and stop. The stage master runs your WP on TITAN in an integration round and may
send you the error log verbatim; then fix, commit, report again.

**Report (≤ 15 lines):** commit sha; declarations delivered (names); any deviation from the §1 row; names you were
unsure of (risky spots for the TITAN round).
