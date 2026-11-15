# Manifest: fork `algebraic_jl/` (non-analytic Vol III + algebraic GL(2) material of Vol I/II)

Scout report, 2026-11-14, read-only survey of `main` @ 84818d0. Line counts are `wc -l`. "an" counts come from a crude scan
for measure, integral, L², limit or derivative tokens in declaration bodies (scripts in the scratchpad: `classify.py`, `reach2.py`,
`decls.json`). The copy agents must re-check every declaration they drop or keep. Nothing is built yet; no Lean was run.

## 0. Headline findings
- **Vol III (Lean, 25 modules, 17,168 lines) is entirely algebraic or arithmetic.** It has no measure, integral, trace formula or kernel. The analytic Vol III
  (the JL trace identity, D26) is not formalized yet. Everything to strip sits in the **Vol I/II/Common dependencies**.
- Vol III imports 5 non-Vol-III project modules directly: `VolI.P0.{Adeles,Ideles,Conventions}`, `VolI.P1.HeckeBasis`,
  `Common.HeckeModule`. HeckeBasis pulls in `VolI.P0.Haar` (4,004 lines) and `VolI.P0.Hecke`, both analytic, and Vol III uses neither.
- Some algebraic notions are *defined* through Mathlib measure theory. `normAbs` (LocalField) = `distribHaarChar`, and `ideleNorm`
  is built from `normAbs`. Recommendation: **keep such definitions verbatim**, since a Mathlib import is not project analysis. Redefining them
  would change sem-hashes and break B≅C. Strip only project declarations whose *content* is analytic.
- Vol III has 3 `sorry`s that are not done items: `III.brandt.ex:hecke-d11-weight4` (BrandtInstances:794),
  `III.qcls.ex:eichler-mass-instances-small` (Instances:1832), and the stage note in JLFormulaGen (a comment only). Copy them as they are.

## 1. Vol III Lean modules (`lean/GL2TF/VolIII/**`): all KEEP
| module | lines | content | class |
|---|---|---|---|
| P1/Arith | 205 | arithmetic functions, signed divisor sums, class numbers of forms, P_k | arith, keep |
| P1/Normalization | 161 | local factors, Cohen/Eichler expressions (defs) | arith, keep |
| P1/CohenLocal | 923 | Cohen's μ locally, Eichler sum form (D2) | arith, keep |
| P1/Boundary | 146 | boundary sums, Eisenstein *expression* (finite formula) | arith, keep |
| P1/JLFormula | 433 | formula-level JL identity (finite rational identity) | arith, keep* |
| P1/JLFormulaGen | 372 | the same with general parameters | arith, keep* |
| P2/QuatAlg | 59 | definite quaternion algebras over ℚ, ℝ | alg, keep |
| P2/Ramification | 212 | RamifiedExactly, Pizer algebras | alg, keep |
| P2/Orders | 1123 | orders, maximal/Eichler orders, level structures, discriminants, units | alg, keep |
| P2/LocalStructure | 1142 | completions of lattices/orders, local splitting | alg, keep |
| P2/Adelic | 624 | finite-adelic B̂, completions, local–global for lattices | alg/top, keep |
| P2/ClassSet | 1023 | class sets, stabilizers, Minkowski bound, finiteness | alg, keep |
| P2/MassDefs | 31 | mass of an order (def) | alg, keep |
| P2/Mass | 952 | mass under change of level (uses Hyp.EichlerMass) | alg, keep |
| P2/Compact | 526 | B^×(𝔸), discreteness, compactness of B^×\B^×(𝔸)^1 | topological, keep |
| P2/Instances | 1834 | Hurwitz/Pizer orders, closed EichlerMass instances | alg, keep |
| Brandt/SymPower | 558 | Sym^m of the standard rep of M₂(K) (algebraic) | keep |
| Brandt/Coefficients | 157 | splittings, coefficient modules V_k | keep |
| Brandt/Forms | 271 | quaternionic forms M_k(O; s) | keep |
| Brandt/Hecke | 983 | Hecke operators T_n via `heckeAct` | keep |
| Brandt/HeckeLocal | 2170 | local Hecke embedding from the spherical Hecke algebra, recursion, commutativity | keep |
| Brandt/Pairing | 722 | norm-weighted pairing, self-adjointness, Eisenstein line | keep |
| Brandt/Trace | 352 | fixed-point trace of T_n (counting, not the analytic TF) | keep |
| Brandt/Brandt | 1393 | Brandt matrices | keep |
| Brandt/BrandtInstances | 796 | D=11 instances | keep |
*The `ef` chapter is the arithmetic layer of the trace identity: finite expressions with no analysis (its own A overview says so). Keep it unless the lead
wants to scope it out. It is self-contained (P1 imports only Meta.Tag and Mathlib, except that P2/Mass imports P1.Arith).
Also keep: `Common/QuaternionNorm` (137), `Common/QuaternionHilbert` (661), `Hyp/EichlerMass` (34).
Tags: 137 tf_id + 36 tf_aux in Vol III.

## 2. Vol I / Vol II / Common classification (scope extensions 1+2: split GL₂/ℚ algebra; congruence subgroups / SL₂(ℤ))
Legend: K = keep whole, P = partial (drop the listed analytic declarations, cut the analytic imports), S = strip. "alg/an" = tag counts by the scan.
| module | lines | alg/an tags | verdict and what to drop |
|---|---|---|---|
| Meta/Tag | 194 | – | K. Imports only `Lean`; copy it (see §3) |
| Common/MatrixGL2 | 86 | 3/2 | K. Topological GL_n; the measurable-space instances are harmless, keep them |
| Common/MatrixCalculus | 77 | 4/2 | P. Keep `matrix-pi to-pi det-ne-zero-set gl-extension`; drop `real-lie-derivative exp-gl`. Decompositions imports it |
| Common/RestrictedProduct | 898 | 2/17 | P. Keep second countability and the box compact/open lemmas (topology); drop restricted-product measures (`*-measure*`, `*-borel*`) |
| Common/HeckeModule | 231 | 3/0 | K (`X.hmod`, the algebraic Hecke action) |
| Common/UnipNormOne | 32 | 0/1 | K optional (n(u) ∈ G(𝔸)^1, algebraic; only needed if KernelClasses is kept) |
| Common/Unimodular, DiscreteQuotient, WeilFormula, QuotientTower, IntegralOperators, Operators, Averaging, Schur, MeroContinuation | – | – | S. Needed only as imports of partial files: cut those imports |
| Common/RestrictedTensor | 1999 | 11/1 | S (tensor products of representations; not requested) |
| VolI/P0/Conventions | 663 | 34/2 | K. B, T, N, w, center, opposite Borel, normalizer of T, 𝔞_B, roots, chambers, max compacts K_p, O(2), rotations |
| VolI/P0/LocalField | 1792 | 11/21 | P. Keep NALF interface, ℚ_p instance, uniformizer, residue cardinality, `normalized-abs`, `abs-multiplicative`, `abs-padic-eq`, `abs-uniformizer`, `unit-uniformizer-decomposition` (Vol III uses them). Drop additive/multiplicative Haar, `vol-*`, `haar-*`, standard character, Schwartz–Bruhat, Fourier. `measure_smul_normAbs`/`measure_integer_eq_q_mul` are proof dependencies of `normAbs` facts: keep them (B-only) or re-prove |
| VolI/P0/Adeles | 1439 | 15/13 | P. Keep 𝔸_f model, Ẑ, 𝔸, ℚ ↪ 𝔸 (`rat-embedding*`), topology/local compactness/second countability, `rat-discrete`, `zhat-units-explicit`, `primes-fact-instance`. Drop Haar, characters, Fourier, Poisson, `adele-fundamental-domain`, `rat-quotient-compact` (topological: optional keep), Schwartz–Bruhat. Imports Vendor `FLT.NumberField.Padics.RestrictedProduct` |
| VolI/P0/Ideles | 2126 | 23/15 | P. Keep 𝕀, idele norm, product formula, `idele-inf-fin`, decomposition, norm-one ideles, Ẑ^× compactness/reduction, `zhat-characters-finite-order`, `hecke-character` (def: optional). Drop idele Haar, `l2-*`, `dirichlet-pair`, `hecke-character-classification`, Borel instances (unless needed) |
| VolI/P0/TopGroups | 1543 | 40/2 | K. GL₂ over ℚ_p/ℝ/𝔸 as topological groups, K_f, G(𝔸)^1, mirabolic, **congruence subgroups** (`congruence-subgroups`, `congruence-k1`, `congruence-kf`, `-explicit`, GL₂(Ẑ) reduction), `sl2-reduction-surjective`, **`sl2-strong-approximation`, `strong-approximation`**, `double-coset-det` |
| VolI/P0/Decompositions | 1529 | 14/5 | K (P optional). Bruhat, Iwasawa (local/real/adelic), Cartan, `double-coset-index`, height map. Only `iwasawa-real-smooth` is analytic (smoothness): drop it to cut the MatrixCalculus calculus |
| VolI/P0/Haar | 4004 | 3/48 | S. Move the 3 algebraic declarations into the fork's TopGroups/Conventions: `max-compact-local-compact-instance`, `borel-coordinates`, `norm-one-locally-compact-instance` (check users) |
| VolI/P0/Hecke | 647 | 0/12 | S (convolution of C_c^∞ by Haar measure; `hecke-algebra-level` is measure-defined). The algebraic Hecke algebra is the Vendor `HeckePair` |
| VolI/P0/Reduction | 2087 | 7/12 | P. Keep `siegel-set*`, `primitive-norm`, `primitive-vector-finiteness`, `det-max-compact-fin`, `adelic-hadamard`. Drop volume, measurable fundamental domain, finite volume, height lemma and compactness criterion (topological: optional). Imports Quotient → cut it |
| VolI/P0/ReductionFiniteness | 166 | 0/1 | S (Siegel finiteness; P if the lead wants it, since it is mostly combinatorial) |
| VolI/P0/Quotient | 1244 | 10/9 | P. Keep `unipotent-rat torus-rat borel-rat torus-quotient-compact gl2-rat-norm-one(-discrete) idele-pos-units automorphic-right-action`. Drop measures and L² |
| VolI/P0/HeckeGlobal | 2866 | 18/12 | S by default (test-function spaces). Optional P: `gl2-padic-totally-disconnected`, `k-infinity-*`, `norm-one-coset-decomposition`, `finite-det-norm` |
| VolI/P0/{Tate, QuotientVolume, HaarBigCell, ConvolutionTensor, Reps, RepsAdelicModule, RepsAutomorphic, Spectral} | – | – | S |
| VolI/P1/Spherical | 104 | 3/1 | K (spherical Hecke algebra = `HeckePair.HeckeAlgebra`, Gelfand trick, commutativity: algebraic; the scan's "an" flag is a false positive) |
| VolI/P1/HeckeBasis | 916 | 8/3 | P. Drop lines ≈853–909: `totallyDisconnectedSpace_gl2_of` (keep it if wanted), `hecke_mem_smoothCompact`, `spherical_convolution_haar` (I.satake.thm:spherical-convolution-haar); drop `import VolI.P0.Haar`, `VolI.P0.Hecke` (check `𝐊[F]` notation and smoothCompact provenance). `hecke-polynomial` / `hecke-t-squared` are algebraic: keep |
| VolI/P1/Satake | 1105 | 14/2 | K (Satake isomorphism, algebraic). The 2 flagged declarations are probably false positives: check them |
| VolI/P1/PrincipalSeries, Jacquet, SphericalEigen | 731/1379/294 | 13/1, 8/1, 3/2 | Optional (smooth reps of GL₂(ℚ_p) are algebraic, but they are "representations"). PrincipalSeries imports Haar (modulus δ): S by default; lead decides |
| VolI/P1/{Intertwining, GL2R, GL2RUnitary, ArchInduced*} | – | – | S |
| VolI/P2/Dictionary | 2319 | 4/5 | Optional P (congruence): `lift-decomposition`, `adelic-lift`, `holomorphic-dictionary-level-n` concern automorphic forms → S by default. The congruence-subgroup *group theory* is in TopGroups (keep) |
| VolI/P2/CuspFiniteDim and all other P2 | – | – | S (automorphic) |
| VolII/Parabolic | 393 | 10/9 | P. Keep `standard-parabolics`, Levi/parabolic fintype, `weyl-action-a`, `parabolic-height`, `coroot`, `theta`, `y-vector`. Drop the (G,T)-family values, derivatives and weight (analytic) |
| VolII/Centralizer | 853 | 21/4 | P. Keep elliptic elements, centralizers (explicit, ℚ-points, closed, norm-one splitting), `conjugates-meeting-compact-finite`, `centralizer-compact-fundamental-set`. Drop `centralizer-unimodular`, `elliptic-volume-finite` (and cut `Common.WeilFormula`). `elliptic-centralizer-compact` is topological: optional keep |
| VolII/KernelClasses | 890 | 5/10 | P. Keep `geometric-class class-polynomial class-types class-trichotomy finitely-many-classes` (+`semisimple-class-conjugacy` if its proof is algebraic). Drop every kernel. Cut `import VolII.Kernel` |
| VolII/TruncationCosets | 349 | 8/2 | P. Keep `borel-cosets`, `coset-height`, `weyl-height-zero`, `t-zero`, `coset-sum-finite`, chamber functions. Drop `height-continuous` (optional) and the QuotientTower import |
| all other VolII modules | – | – | S (kernels, orbital integrals, truncation L², spectral, final TF) |

**SL₂(ℤ) / congruence material found:** only the group-theoretic part in `VolI/P0/TopGroups` (Γ(N)-type K_f(N), K₀/K₁, GL₂(Ẑ) → GL₂(ℤ/N)
surjectivity, SL₂ strong approximation, `double-coset-det`) and `VolI/P0/Decompositions` (`double-coset-index`). There is
**no SL₂(ℤ) generators / Farey / fundamental-domain-combinatorics material**: the fundamental domains are measure-theoretic (`I.red`, `I.quot`, `X.quot`) → S.
Congruence groups in Dictionary/Spectral/Eisenstein are automorphic → S.

## 3. Import closure and module plan
Vol III-only closure (module level): Meta/Tag, Common/{QuaternionNorm, QuaternionHilbert, HeckeModule, MatrixGL2, MatrixCalculus,
RestrictedProduct, Unimodular}, Hyp/EichlerMass, VolI/P0/{Conventions, LocalField, Adeles, Ideles, TopGroups, Decompositions, Hecke, Haar},
VolI/P1/{Spherical, HeckeBasis}; Vendor: `Definitions.Def_LocalLanglands_HeckePair` (495), `…_GelfandInvolution` (161),
`FLT.NumberField.Padics.RestrictedProduct` (161; Mathlib-only imports, no `import Mathlib`).
Declaration-level reachability (approximate, by name) from Vol III: Hecke 0/54 and Haar 0/279 declarations used → both strip after the imports are cut;
Adeles 17/83, Ideles 26/94, LocalField 30/82, Decompositions 68/111, TopGroups 2/109, HeckeBasis 24/60, Spherical 5/5,
HeckeModule 10/10, Conventions 7/48, RestrictedProduct 0/53 (needed only via the Adeles import).
With the extension (Conventions, LocalField, Adeles, Ideles, TopGroups, Decompositions, Spherical, HeckeBasis, Satake, Reduction-P,
Quotient-P, Parabolic-P, Centralizer-P, KernelClasses-P, TruncationCosets-P), the import graph also reaches DiscreteQuotient, WeilFormula, QuotientTower,
Kernel, Haar and Unimodular. **All of them are to be cut at the import level**, which is why those files are P. Algebraic declarations needed from cut files:
Haar's 3 (above), and `QuotientTower.discreteTopology_of_le` (6 lines, move it).

Proposed fork layout: `algebraic_jl/lean/AlgJL/{Meta,Common,Local,Adelic,Group,Quaternion,Explicit,Brandt}/…` or simply mirror the
original paths (`AlgJL/VolI/P0/…`, `AlgJL/VolIII/…`). **Recommendation: mirror the paths under a new root `AlgJL`**, so that `import GL2TF.X.Y` becomes
`import AlgJL.X.Y` mechanically, and **keep declaration namespaces (`GL2TF.*`) and every tf_id/tf_aux ID unchanged** in phase 1.
Then the Lean names in B's `\lean{}` and in the frozen `signatures.tex` stay valid, and B≅C stays traceable to the parent. A namespace rename
can come later as one scripted step with a mapping file. Trimmed files should get a header line naming the source file, its commit (84818d0) and the dropped declarations.

**tf_id/tf_aux:** both come from `GL2TF/Meta/Tag.lean` (194 lines, `import Lean` only; namespace `GL2TF.Meta`, env extension
`tagExt`). Recommendation: copy it verbatim as `AlgJL/Meta/Tag.lean` and keep the attribute names `tf_id`/`tf_aux` and the ID
grammar (vol ∈ {I, II, III, X}). Do **not** strip the attributes, because they are the only C-side anchor of B≅C. It is a separate project, so
there is no attribute-name clash. If the fork must not carry the `GL2TF` namespace at all, rename it to `AlgJL.Meta` in one file only:
the attribute syntax stays the same.

Vendor: copy the 3 files into `algebraic_jl/lean/Vendor/{AnthropicFLT,ImperialFLT}/` byte-identical (module names `Definitions.*`,
`FLT.*`), with LICENSE, NOTICE, ATTRIBUTION.md, PROVENANCE.md and the matching MANIFEST.tsv rows (rule 13). Use the same two `lean_lib`
stanzas (srcDir and leanOptions as in `lean/lakefile.toml`). They are not "import Mathlib" files and they are small.

## 4. Hypotheses
Only `Hyp.EichlerMass` (`III.qcls.hyp:eichler-mass`), used by P2/Mass (`eichlerOrder_mass`) and by P2/Instances (closed instances for
D = 2, 11). It imports VolIII.P2.{Ramification, MassDefs} only. No other Hyp is reachable from the kept set (H1–H4 and H2a/b are all in stripped modules).
Copy its `\tfhypentry` block (`tex/shared/hypotheses.tex` lines 113–126) into the fork's hypotheses.tex.

## 5. TeX
**A/B chapters for Vol III** (all algebraic; keep whole): `tex/{readable,backtranslation}/vol3/ch-iii-01-explicit` (A 919 / B 1048),
`ch-iii-06-quatalg` (447/515), `ch-iii-07-orders` (756/1336), `ch-iii-08-brandt` (665/1223). One stray sentence refers to
`II.cpt.thm:compact-trace-formula` (texttt only; A 07-orders:567, B :1208): reword it.
**Items:** `tex/items/III/{ef 55, qalg 22, qcls 46, qform 25, qord 21, brandt 24}` = 193 files, 913 lines.
**Cross-volume refs from Vol III** (via xr to vol1.aux): I.adele.* (17 IDs), I.cartan.* (6), I.conv.* (3), I.lf.* (12),
I.satake.* (7), I.topgrp.def:congruence-subgroups, X.hmod.* (3), X.hpair.* (7). In the fork they become local items, typeset in the new
prerequisite chapters below.
**Vol I/II chapters (scope extension):**
- K: `vol1/ch-0-01-conventions` (A 285/B 586), `ch-0-04-top-groups` (418/779), `ch-0-05-decompositions` (347/400; drop the smooth-Iwasawa item).
- P: `ch-0-02-local-field` (418/674): §1 NALF, §2 normalized abs (drop Haar items); drop §3 (characters/Fourier).
  `ch-0-03-adeles` (842/1402): keep §1 adele ring and §3 ideles; drop §2 characters/Poisson and §5 Tate; §4 Ẑ^× characters and Hecke characters: keep the defs, drop the classification.
  `ch-0-07-quotient` (662/1011): only §1 discrete subgroups + the algebraic parts of §2. `ch-0-08-reduction` (306/388): Siegel sets only.
  `ch-1-01-spherical` (545/921): §1–3 keep (drop the item `spherical-convolution-haar`), §4 characters keep.
  `vol2/ch-02-parabolic` (158/322): §1 only. `ch-03-kernel` (616/722): §2 classes only. `ch-04-orbital` (876/1362): §1 + §2 without volumes.
  `ch-06-truncation` (768/795): §§1–2.
- Optional: `ch-1-02-smooth` §§1–3 (principal series, Jacquet; reps). S: ch-0-06 haar, 0-09 hecke, 0-10, 0-11, 1-03..1-05, all of ch-2-*, the rest of vol2.
- Items of these areas: I/conv 36, lf 32, adele 85, topgrp 44, decomp 11, cartan 8, satake 32, red 20, quot 27; II/par 19, kernel 35,
  orb 64, trunc 37; X/hmod 3, hpair 12, topgrp 10. Copy only the IDs of kept declarations (filter by the tf_id list of the trimmed Lean).
**Shared:** `gl2tf.sty` (489) is needed. Fork edits in the copy: the `\tf@import` lines for vol2/vol3 (xr to `../../build/tex/*/vol1.aux`) go,
the `\tf@generateddir` and `\tf@itempath` paths stay relative (texbuild sets `TEXINPUTS=.:tex:tex/shared`), and `\tf@checkid` keeps
I/II/III/X. `notation.tex` (518; copy whole, prune later), `refs.bib` (705; copy whole), `hypotheses.tex`: only the EichlerMass entry.
**Generated files:** `tex/backtranslation/generated/{status,signatures,binders,axioms}.tex` (1.5k/1.5k/7k/1.5k lines) are written by
`tools/status.py` from a tfaudit run and loaded by `\AtBeginDocument` if present (`\tfsetstatus`, `\tfsetsignature{ID}{LeanName}{sem_hash}{type}`,
`\tfsetbinder`, `\tfsetaxioms`). B's `tfformal` blocks print the signature and compare `\tfsem` against the hash. **Fork:** carry a *frozen filtered
copy* (grep the lines whose first argument is a kept ID) under `algebraic_jl/latex/backtranslation/generated/`, with a header naming the parent
commit and the tfaudit stamp (2026-11-13T22:36:14Z, lean tree e209793e…). The hashes stay valid for verbatim-copied declarations only. For trimmed files
the semantic hashes are unchanged as long as the bodies of the kept declarations and their dependencies are byte-identical (moving a declaration between files does not
change the sem_hash; renaming the namespace would). Status lines (`audited …`) must be rewritten as "inherited from parent @84818d0" or dropped,
because the fork has no signoffs registry.

## 6. GL2TFTests coverage (copy into `algebraic_jl/lean/AlgJLTests/…`; drop tests of stripped declarations)
Vol III: `GL2TFTests/VolIII/**` = 1,295 lines (Brandt 9 files incl. Exits 141; P1 6 files; P2 13 files incl. Exits 126).
Quaternion Common files are tested inside VolIII/P2 (QuatAlg, Ramification). Closed instance of EichlerMass: P2/Instances (+P2/Exits).
Base: Common/{HeckeModule 28, MatrixGL2 20, RestrictedProduct 63 (P)}; VolI/P0/{Conventions 92, LocalField 80 P, Adeles 55 P,
Ideles 190 P, TopGroups 103, Decompositions 28, Reduction 209 P, Quotient 68 P}; VolI/P1/{Spherical 67, HeckeBasis 99 P, Satake 98};
VolII/{Parabolic 72 P, Centralizer 351 P, KernelClasses 278 P, TruncationCosets 23}. Optional: PrincipalSeries 179, Jacquet 44, SphericalEigen 26.

## 7. Lake project and scripts
- `lean/lakefile.toml`: package `GL2TF`; one `[[require]] mathlib` (git URL plus rev `56a00585…`); libs GL2TF, GL2TFTests, GL2TFPrintAxioms,
  GL2TFVendor (srcDir `Vendor/AnthropicFLT`), GL2TFVendorImperial (srcDir `Vendor/ImperialFLT`), exe tfaudit. `lean-toolchain` = `leanprover/lean4:v4.35.0`.
  `lake-manifest.json`: name "GL2TF", 9 git packages (mathlib + 8 inherited), `packagesDir .lake/packages`.
- **Every script hard-codes `repo=$(dirname $0)/..` and `lean=$repo/lean`** (link_deps, check_frozen, lfile, lbuild,
  prune_stale_build → stale_build.py; deps_load reads `$repo/tools/deps.conf`, `deps.local.conf`, `load_profiles.conf`). `lfile.sh` refuses
  files outside `$repo/lean`. `lbuild.sh` allows only the targets `GL2TF|GL2TFTests|…|+GL2TF.*|+GL2TFTests.*|+Audit.*|vendored`. None of them can be pointed at
  another project directory.
- **Safest approach (needs lead/user approval: a new script copy in the rule-7 sense):** create `algebraic_jl/tools/` as a *copy* of
  `deps.conf, deps_load.sh, load_profiles.conf, link_deps.sh, check_frozen.sh, lfile.sh, lbuild.sh, prune_stale_build.sh, stale_build.py`
  (stale_build.py is stdlib-only and defaults to `parent/../lean`). Because `repo` resolves to `algebraic_jl/`, they then operate on `algebraic_jl/lean` unchanged, with
  **the same LOCK_DIR `/home/janosch/.cache/gl2tf` (the same lean.lock and slots, so rules 7–8 hold globally), the same DEPS_TREE, FROZEN_TREES, caps and
  checks.** The only edit needed is the `allowed_target` case list in the lbuild copy (add `AlgJL|AlgJLTests|+AlgJL.*|+AlgJLTests.*`) plus the
  error text. Never use `--audit`, because the fork has no `Audit/`.
  Alternative with zero script edits: name the fork's libs `GL2TF`/`GL2TFTests` with module roots `GL2TF.*`. This is technically self-contained but
  confusing, so it is not recommended.
- Lake files for the fork: `lean-toolchain` = byte copy. `lake-manifest.json` = **byte copy** (the same rev and URL for all 9 packages, so Lake never
  re-resolves). Keep the root package `name = "GL2TF"` in the fork's lakefile so that the manifest stays byte-identical. Renaming the package is possible
  but then needs the manifest `name` field edited, a `link_deps --verify` and a dry `--no-build` check first. Recommendation: do not rename in phase 1.
  `lakefile.toml`: `[leanOptions]` as in the parent, `[[require]] mathlib` identical, `[[lean_lib]] AlgJL`, `AlgJLTests`, the two vendor libs.
  `.lake/packages` is created **only** by the copied `link_deps.sh` (it verifies the rev and URL against the farm read-only, then writes relative symlinks into
  `algebraic_jl/lean/.lake/packages/`). Add `algebraic_jl/lean/.lake/` to .gitignore.
- Build order: copied `lbuild.sh +AlgJL.<module>` (exclusive lock, 8G cap), then the copied `lfile.sh` for single files. Ask the user before any Lean CPU work
  (memory note). Rule 5 dry check: the copied `check_frozen.sh` scans `algebraic_jl/lean` imports, then runs `find -newer` on the same FROZEN_TREES.
- Risks: a second `.lake/build` tree means Mathlib oleans are read from the frozen farm (no rebuild if the toolchain and rev match); the project oleans are
  rebuilt from scratch (~30k lines of project code: modest). Never run `lake update` in the fork, and never let Lake see a manifest/URL mismatch.

## 8. Sizes and partition (4 agents, ≤ 5 per session)
| agent | scope | Lean lines (src + tests) | TeX lines |
|---|---|---|---|
| L-A "local/adelic base" | Meta/Tag, Common/{MatrixGL2, MatrixCalculus-P, RestrictedProduct-P, HeckeModule}, VolI/P0/{LocalField-P, Adeles-P, Ideles-P, TopGroups, Conventions}, 3 Vendor files + attribution, Lake skeleton (lakefile, manifest, toolchain; script copies only after approval) | ≈ 9.0k → ~5.5k after trimming; tests ~0.6k | – |
| L-B "group theory/Hecke" | VolI/P0/{Decompositions, Reduction-P, Quotient-P, Haar → 3 moved declarations}, VolI/P1/{Spherical, HeckeBasis-P, Satake, opt. PrincipalSeries/Jacquet/SphericalEigen}, VolII/{Parabolic-P, Centralizer-P, KernelClasses-P, TruncationCosets-P} | ≈ 10.4k → ~6.5k; tests ~1.3k | – |
| L-C "Vol III copy" | all 25 VolIII modules + Common/Quaternion* + Hyp/EichlerMass + VolIII tests: mechanical `import GL2TF.`→`import AlgJL.` (no trimming) | 18.0k + 1.3k | – |
| T "LaTeX A+B" | `algebraic_jl/latex/{readable,backtranslation,items,shared}`: Vol III chapters verbatim (A 2.8k, B 4.1k), items III (193 files); prerequisite chapters trimmed from vol1 ch-0-01/02/03/04/05/07/08, ch-1-01 and vol2 ch-02/03/04/06 (A ≈ 5.5k, B ≈ 8.0k before trimming); item subset (~400 files); sty/notation/bib/hypotheses; filtered generated/*.tex; one master `algjl.tex` per edition | – | ≈ 20k in, ~12k out |
Dependencies: L-C can copy right away (names unchanged). Compiling needs L-A, then L-B. T needs the final kept-ID list from L-A and L-B to filter
items and generated files; it can start with Vol III chapters and items right away. If a fifth slot is free, split T into A and B (B is the larger part).
A shared deliverable for all: `algebraic_jl/KEPT_IDS.txt` (ID ↦ Lean name ↦ source file@84818d0), the single filter for items, generated and B.
