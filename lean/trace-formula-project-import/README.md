# algebraic_jl: a non-analytic fork of the GL(2) / quaternion material

A self-contained fork, made from parent commit `84818d0` on 2026-11-14. It collects the algebraic, arithmetic and topological
material that an algebro-geometric or topological approach to Jacquet–Langlands, one that does not use the trace formula,
can build on:

- **Vol III, whole:** quaternion algebras over ℚ, orders and maximal orders, local structure, adelic class sets,
  Eichler mass, quaternionic forms, Hecke operators, Brandt matrices and the Brandt pairing, and the trace of T_n computed
  by counting fixed points.
- **Vol I/II, algebraic part of split GL₂/ℚ:**
  - p-adic and real group structure;
  - adeles and ideles as algebraic or topological objects;
  - Iwasawa, Cartan and Bruhat decompositions;
  - maximal compact subgroups and congruence-type open compact subgroups;
  - strong approximation;
  - reduction theory, the Siegel covering and the topology of G(ℚ)\G(𝔸)^1;
  - the algebraic Hecke algebra, the spherical Hecke algebra, Satake and Hecke modules;
  - the algebraic parts of smooth representations, the principal series and Jacquet modules;
  - parabolic subgroups, centralizers and conjugacy classes.
- **Appendix:** the finite arithmetic of the explicit-formula chapter (`ef`).

**Stripped:** Haar-measure integration, L², convolution Hecke algebras of C_c^∞, automorphic forms, Eisenstein series,
kernels, the trace formula and spectral theory. Mathlib's own measure theory stays available as a library dependency;
for example, `normAbs` is defined through Mathlib's Haar character.

## Layout
- `lean/`: the Lake project. The package name is `GL2TF`; the libraries are `AlgJL`, `AlgJLTests` and `Vendor`.
  - `lean-toolchain` and `lake-manifest.json` are byte copies of the parent's (Lean v4.35.0, Mathlib `v4.35.0`).
  - Declaration names (`GL2TF.*`) and `tf_id`/`tf_aux` IDs are unchanged from the parent; only module paths moved
    from `GL2TF.*` to `AlgJL.*`.
  - The project has 110 files and about 36k lines.
- `tools/`: copies of the parent's build scripts, with the same locks, memory caps and frozen-tree checks.
  - Build with `tools/lbuild.sh AlgJL AlgJLTests`.
  - Check a single file with `tools/lfile.sh <file>`.
  - Never call `lake` directly. Never run `lake update`, `lake clean` or `lake exe cache get`.
- `latex/`: the two LaTeX editions; build with `latex/build.sh A|B|all`, output in `latex/build/{A,B}/algjl.pdf`.
  - `readable/` is edition A, `backtranslation/` is edition B.
  - `shared/` holds the style file, notation table, `refs.bib` and the hypothesis registry.
  - `items/` holds the single source of all 526 statement snippets.
  - B is regenerated with `python3 latex/backtranslation/tools/mkB.py final`. Its `generated/` folder is a frozen
    filtered copy of the parent's generated files and is not recomputed.
- `latex/EDITS.md`: every edit made relative to the parent, covering statements, proofs, dropped items and chapter
  structure.
- `KEPT_IDS/`: the per-agent lists of kept and dropped IDs from the extraction; these are historical records.
- `MANIFEST_SCOUT.md` and `TEAM_BRIEF.md`: the extraction plan and the decisions behind it.

## Status at extraction (2026-11-14)
- **Lean:** the full build of `AlgJL` and `AlgJLTests` passes, and the frozen-tree check was clean.
  - No axioms, `native_decide` or `unsafe`.
  - `#print axioms` on the headline theorems spot-checked (`satake_isomorphism`, `localHeckeEmbedding_hom`,
    `strong_approximation`, `mass_level_change`) shows only `propext`, `Classical.choice` and `Quot.sound`.
- **Invariants:** the 526 Lean tags equal B's items; A's 324 items are contained in B; the other 202 items are B-only.
- **Hypothesis:** exactly one, `Hyp.EichlerMass`.
- **Open `sorry`s:** two, both in examples that were already open in the parent and are not done items:
  - `lean/AlgJL/VolIII/P2/Instances.lean:1815` (`III.qcls.ex:eichler-mass-instances-small`);
  - `lean/AlgJL/VolIII/Brandt/BrandtInstances.lean:783` (`III.brandt.ex:hecke-d11-weight4`).
- **Proof changed in the fork:** `I.quot.lem:automorphic-right-action-continuous-instance` now has a measure-free
  proof, so its hash differs from the parent's; `generated/` notes this.
- **Sign-offs:** none were re-run. The audit status shown in B is inherited from the parent at `84818d0`.
- **Dropped statements:** four whose statements involve integrals or kernels (see `EDITS.md`), plus
  `rat_quotient_compact`, whose statement normalizes a Haar measure.
- **Fork-new items (2026-11-14):** one, `I.adele.thm:rat-quotient-compact-top` (`rat_quotient_compact_top`):
  ℚ\𝔸 is compact Hausdorff, without measures. It replaces the topological part of `rat_quotient_compact`.
  - Its B block is hand-written in `latex/backtranslation/tools/fork_new.tex`, and `mkB.py` inserts it.
  - It has no parent hash and no audit; `EDITS.md` §6 records it.
  - Compactness statements that were already present: `I.adele.thm:norm-one-quotient` (𝔸^1/ℚ^× ≅ Ẑ^×, compact),
    `I.quot.thm:torus-quotient-compact`, `I.red.thm:siegel-truncation-compact` and `I.red.thm:compactness-criterion`.
- **Missing material:** no SL₂(ℤ) generators and no combinatorial (measure-free) fundamental domain; neither existed
  in the parent.
