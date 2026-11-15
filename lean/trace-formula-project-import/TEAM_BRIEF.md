# Team brief: fork `algebraic_jl/` (lead decisions, 2026-11-14)

Mission: a self-contained forked volume of the NON-ANALYTIC material usable for an algebro-geometric/topological
approach to Jacquet–Langlands (no trace formula): all of Vol III (quaternion algebras over ℚ, orders, class sets,
Brandt/Hecke, Eichler mass) plus the algebraic split-GL₂/ℚ material of Vol I/II (p-adic and real group structure,
adeles/ideles as algebraic objects, decompositions, maximal compacts, double cosets, strong approximation, algebraic
Hecke algebras, Satake, congruence subgroups, parabolic/centralizer/conjugacy algebra). Strip: measures, integration,
L², automorphic forms, Eisenstein series, kernels, trace formula, spectral theory.
Scout manifest: `algebraic_jl/MANIFEST_SCOUT.md` (read it; its keep/drop lists are name-based, re-check per decl).

## Lead decisions
- D-a: keep the explicit-formula chapter `ef` (finite arithmetic) as a final chapter/appendix.
- D-b: keep the smooth-representation files (PrincipalSeries, Jacquet, SphericalEigen) to the extent they are
  algebraic (no integration / measure); drop analytic declarations.
- D-c: copy scripts into `algebraic_jl/tools/` (approved). Lake package name stays `GL2TF` so `lake-manifest.json`
  and `lean-toolchain` are byte copies; library roots `AlgJL` and `AlgJLTests`. Declaration names (`GL2TF.*`) and
  `tf_id`/`tf_aux` IDs stay UNCHANGED (traceability B≅C). `Meta/Tag.lean` copied verbatim (as `AlgJL/Meta/Tag.lean`).
- D-d: `normAbs` etc. built on Mathlib's Haar character are copied verbatim (Mathlib measure theory is fine as a
  Mathlib dependency; what we strip is OUR analytic development).
- Self-contained: nothing in `algebraic_jl/` may import, \input, \uses or path-reference anything outside
  `algebraic_jl/` (Mathlib via the frozen farm is fine). Cross-references to dropped items are removed or turned
  into plain remarks citing the literature.
- Do NOT edit anything outside `algebraic_jl/` (the main repo is untouched). Do NOT commit.

## Layout
```
algebraic_jl/
  README.md            (lead / integrator)
  tools/               (copied scripts, owner L-A)
  lean/                lakefile.toml, lean-toolchain, lake-manifest.json, AlgJL/**, AlgJLTests/**, Vendor/**
  latex/
    shared/            sty, notation.tex, refs.bib, hypotheses.tex (owner T-A)
    items/             snippet files, same relative paths as tex/items (owner T-A)
    readable/          A edition (owner T-A)
    backtranslation/   B edition incl. generated/ frozen filtered copy (owner T-B)
  KEPT_IDS/<agent>.txt one ID per line, written by each Lean agent for the decls it kept
```
Module path mapping: `lean/GL2TF/X/Y.lean` → `algebraic_jl/lean/AlgJL/X/Y.lean`, imports `GL2TF.X.Y` → `AlgJL.X.Y`;
`GL2TFTests.*` → `AlgJLTests.*`; Vendor stays `Vendor.*` under `algebraic_jl/lean/Vendor/` (keep attribution files).

## Ownership (no one edits another's files; send needs to the lead in your final report)
- L-A (Opus): tools/, Lake skeleton, Meta, Common, local/adelic base files (LocalField, Adeles, Ideles,
  RestrictedProduct, TopGroups, Conventions, Vendor) + their tests. Also INTEGRATOR: final build of the fork.
- L-B (Opus): Decompositions, Spherical, Satake, HeckeModule, HeckeBasis, Reduction, Quotient, Parabolic,
  Centralizer, KernelClasses, TruncationCosets, smooth-rep files, ef Lean files (if Vol II/III Lean) + tests.
- L-C (Sonnet): all Vol III Lean modules + their tests (mechanical copy, import rename).
- T-A (Opus): latex/shared, latex/items, latex/readable (A).
- T-B (Sonnet): latex/backtranslation (B).

## Lean rules (CLAUDE.md HARD RULES apply verbatim)
- Lean runs ONLY via `algebraic_jl/tools/lbuild.sh` / `lfile.sh` (copied scripts, same locks/caps), after L-A
  reports the skeleton ready (file `algebraic_jl/tools/READY` exists). Never `lake update/clean/cache get`;
  never write into frozen trees; run the copied `check_frozen.sh` before the first build.
- Targeted builds only (`+AlgJL.X.Y`); the full fork build is run once by L-A as integrator.
- No axioms, no new sorry (the two existing Vol III sorries may stay, listed in README as open).
