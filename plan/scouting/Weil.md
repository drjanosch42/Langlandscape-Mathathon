# Scouting report: AxiomMath/Weil

Scouted 2026-11-14 through the GitHub API only (repo metadata, recursive tree, about 35 individual files fetched raw,
code search). Nothing was cloned or built. Upstream commit inspected: `27cdb2049be62ee2911429b47f54774078450e32`
(`main`, 2026-11-06, "One library: WeilFrontier renamed to Weil").

**Bottom line.** Weil does not close any gap of the staged plan. In particular it has **no strong approximation for B¹**
(stage 02, `if:s02-SA`, L02.SA). It has no quaternion algebras, adeles, GL₂/SL₂, trees, group (co)homology, Hecke
algebras or Gorenstein/congruence-ideal material. It is an étale-cohomology library for the Weil conjectures. What
can be reused is a handful of small, Mathlib-only linear-algebra and ℓ-adic files, useful at the edges of stages
04–06 (Λ-adic limits, ℤ_p-linearity of maps between torsion modules, traces on ℤ_p-lattices, continuous ℤ_p[G]-modules).

## 1. License and attribution

- **License:** Apache-2.0 (`LICENSE` at the repo root, the unmodified Apache text. Its appendix copyright line is the
  unfilled template `Copyright [yyyy] [name of copyright owner]`).
- **No `NOTICE` file**, so Apache §4(d) adds nothing.
- **No per-file copyright headers.** Files start directly with `module`. The README says the library has "about 980
  modules written by AI agents … not yet been reviewed by humans".
- **Copyright holder for our ATTRIBUTION row:** the GitHub owner **AxiomMath** (Axiom Math, https://axiommath.ai/).
  All three commits are by Tony Yue Yu (GitHub `tonyyueyu`). Suggested row text: "no per-file header upstream;
  Copyright AxiomMath (repository owner), Apache-2.0; commits by Tony Yue Yu".
- **Obligations when vendoring** (same scheme as `lean/trace-formula-project-import/lean/Vendor/`): copy the file into
  `Vendor/AxiomWeil/…`, ship the Apache LICENSE (already present in `Vendor/LICENSE`), add one row each to
  `MANIFEST.tsv` (upstream URL, rev `27cdb2049be6…`, path, sha256) and `ATTRIBUTION.md`, and add a paragraph to
  `Vendor/NOTICE`. Any change (for example stripping `@[weil "…"]` attributes or the `Weil.Attr` import) needs a change
  notice at the top of the file (§4(b)) and `modified = yes`.
- **Transitive:** many files import `StacksFrontier.*` from https://github.com/AxiomMath/Stacks (also Apache-2.0).
  None of the files recommended below do.

## 2. Toolchain and Mathlib

| | Weil | ours |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` | `leanprover/lean4:v4.35.0` |
| Mathlib rev | `16edf57de7933555826307a3d81b4391a3657a09` (2026-09-01) | `56a005855ea17e0b0958f73ec801ae140b0a1679` (2026-10-13) |
| other deps | `AxiomMath/Stacks` @ `012108f61d7f…` (lib `StacksFrontier`) | — |

Our Mathlib is a strict descendant of theirs (GitHub compare: ahead by 1019 commits, behind by 0), so API drift is
about six weeks. Both use the Lean module system (`module` / `public import`), the same as our frozen Mathlib.
Weil files use the custom attribute `@[weil "label"]` from `Weil/Attr.lean` (33 lines, `meta` syntax, no effect on
elaboration). Either vendor `Weil/Attr.lean` too or delete the attributes; deleting them is a modification.

## 3. Overview of contents (987 blobs)

| Area | Files (approx.) | Content |
|---|---|---|
| `AlgebraicGeometry/EtaleCohomology/` | 283 | étale cohomology, constructible sheaves, proper/smooth base change, Poincaré duality, curves (Kummer, Picard), trace formula, zeta function, Deligne (via Stacks' `LAdicSheaf.weightBound`) |
| `Defs/AlgebraicGeometry`, `AlgebraicGeometry/{Sites,Topologies,Morphisms,Descent,FundamentalGroup,…}` | ~290 | sites, fpqc descent, étale morphisms, π₁^ét, Nagata compactification |
| `AlgebraicGeometry/ComplexPoints/` | 32 | analytification, GAGA for curves, Artin comparison, Betti numbers |
| `CategoryTheory/`, `Algebra/Homology/` | ~160 | derived categories, right-derived functors, Serre classes, Artin–Rees categories of ℓ-adic systems |
| `RingTheory/` | ~60 | Henselian rings and (strict) henselisation, étale/smooth/unramified algebras, adic completion |
| `LinearAlgebra/` | ~12 | twisted-equivariant ("Frobenius") dualities, char-poly functional equations, alternating forms, power sums |
| `Geometry/Manifold`, `Analysis/Complex`, `Topology/` | ~35 | Riemann surfaces, Dolbeault, sheaf cohomology of spaces |

Main theorems (README): the four Weil conjectures (`AlgebraicGeometry.exists_mul_zetaSeries_eq`,
`Weil.prod_aeval_inv_rationalFrobeniusCharpolyReverse_zpow_eq`, `Weil.satisfiesWeilEstimate`,
`Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber`, `LeanEval…weil_conjectures`); axioms only
`propext`, `Classical.choice`, `Quot.sound`. The README says there is no `sorry` and no `native_decide`.

Search for our vocabulary (tree grep plus API code search): `quaternion`, `QuaternionAlgebra`, `adele`,
`FiniteAdeleRing`, `strong approximation`, `Bruhat`, `SpecialLinearGroup`, `groupHomology`, `Gorenstein`,
`IsLattice`, `Brandt` all give **0 hits**. `Hecke` appears nowhere in the paths. Caveat: GitHub code search may index
a new repo only partly, but the tree listing confirms there are no files on these topics.

## 4. Match table

Effort: **S** means vendoring one or two files, Mathlib-only imports (plus `Weil.Attr`), < 1 day. **M** means
vendoring a small chain or extracting and adapting (1–3 days). **L** means a large chain or a Stacks dependency.
"n/u" means not usable.

| Our need (stage / label) | Their declaration (file : name) | Match | Dependencies | Port effort |
|---|---|---|---|---|
| s02 `if:s02-SA`, L02.SA: SA for B¹ at S={∞,q}; sub-steps (a)–(f) (weak approx., Hensel openness, Hasse–Minkowski / local–global for embeddings, Skolem–Noether, Fujisaki) | — | **none** | — | n/u (gap stays open) |
| s02 L02.1 Bruhat–Tits tree, lattices | — | none | — | n/u |
| s02 L02.5/L02.6 H_1(Γ_U,V), Serre II.2.8, Shapiro | — (only sheaf/étale cohomology) | none | — | n/u |
| s03 L1–L3 weighted bipartite multigraphs; index of a full-rank sublattice = \|det\| | `LinearAlgebra/Matrix/BilinearForm.lean`: `Matrix.det_eq_zero_of_alternating_of_odd` | related only (determinants of alternating matrices, not lattice index) | Mathlib | n/u for L3 |
| s04 L1 ordinary idempotent e = lim U_p^{n!} on finite modules; exactness of e | `LinearAlgebra/Eigenspace/Zero.lean`: `LinearMap.BilinForm.injective_restrict_maxGenEigenspace`, `even_finrank_maxGenEigenspace_of_sq_eq` (Fitting decomposition argument) | related (fields only; the e-construction is not there) | `Weil.Defs.LinearAlgebra.PerfectPairing.Basic`, `Weil.LinearAlgebra.Matrix.BilinearForm`, Mathlib | n/u (use Mathlib's Fitting lemmas directly) |
| s04 Λ-adic passage: ℤ_p-module structure on ℤ/p^m-level Brandt modules; Hecke maps that are additive are ℤ_p-linear | `Algebra/Module/LAdicRankOfInverseSystem.lean`: `PadicInt.moduleOfTorsion`, `PadicInt.linearMapOfTorsion`, `linearEquivOfTorsion`, `map_smul_of_pow_smul_eq_zero`, `smul_eq_zsmul_of_eq_add_pow_mul`, `exists_eq_intCast_add_pow_mul`, `inverseSystemOfTorsion` | **adaptable** (generic in ℓ; states exactly "additive map out of a ℤ_ℓ-module killed by ℓ^N is ℤ_ℓ-linear") | Mathlib only + `Weil.Attr` | **S** (507 lines, vendor whole file) |
| s04 rank of lim over levels; ℚ_p ⊗ lim | same file: `PadicInt.rationalLimit`, `finrank_rationalLimit`, `finrank_rationalLimit_eq_of_addEquiv`, `finrank_rationalLimit_eq_finrank_of_bockstein`, `AddCommGroup.exists_basis_mod_torsion` | adaptable (Bockstein-shaped hypothesis; fits "H/p^m H ↪ A_m" control statements) | same | S (same file) |
| s04 Thm λ-adic Ribet: passing exact sequences of finite levels to the inverse limit (Mittag-Leffler) | `CategoryTheory/CofilteredSystem.lean`: `CategoryTheory.Functor.isMittagLeffler_of_isArtinian` (cofiltered systems of Artinian modules are ML) | **adaptable** (the general theorem is exactly what is needed; Mathlib has `IsMittagLeffler` but not this criterion, checked by grep in our frozen Mathlib) | first theorem: Mathlib only; the rest of the file uses `Weil.Defs…ShiftNaturalMap` → `ShiftedSystem` | **S** if only `isMittagLeffler_of_isArtinian` is extracted (about 30 lines, modified); M for the whole file |
| s04 M ≅ lim M/p^n M for finite ℤ_p-modules | `RingTheory/AdicCompletion/FiniteModuleLAdicallyComplete.lean`: `ProjectiveSystem.toLimOfModule` | related | imports `StacksFrontier.RingTheory.AdicCompletion.Basic` | n/u (Mathlib's `AdicCompletion` / `IsAdicComplete` suffices) |
| s04/s06 `if:s04-Mord`: projective system (M/p^{n+1}M)_n of a f.g. module has surjective transitions, finite length levels | `RingTheory/AdicCompletion/Basic.lean`: `ProjectiveSystem.isFiniteLength_quotient_pow_smul_top`, `isLAdicSystem_ofModule_padicInt` | related | `Weil.Defs.CategoryTheory.ObjectProperty.LAdicSystem` → `StacksFrontier` | L (Stacks chain); only the lemma `isFiniteLength_quotient_pow_smul_top` is worth re-proving locally |
| s01/s04 Brandt pairing, perfectness, `hecke_self_adjoint`; s04 `if:s04-etaB` pairings | `Defs/LinearAlgebra/PerfectPairing/Basic.lean`: `LinearMap.IsFrobeniusDuality` (B(fx,gy)=c·B(x,y), ↔ `IsPerfPair`); `LinearAlgebra/PerfectPairing/Basic.lean`: `finrank_eq`, `charpoly_map_eq_prod_roots` | related (a twisted-equivariance shape over fields; our adjointness is B(Tx,y)=B(x,Ty), over ℤ_p) | Mathlib only + `Weil.Attr` | S, but low value |
| s05 sign ε / eigenvalue of Π_q (Atkin–Lehner-type involution) | `LinearAlgebra/PerfectPairing/SelfDualityDeterminant.lean`: `LinearMap.IsFrobeniusDuality.det_eq_neg_one_pow_mul_pow`, `Multiset.prod_eq_neg_one_pow_count_mul_pow_card` | related (det = (−1)^{N₋}γ^b for self-dualities) | the PerfectPairing chain (3 files) | S–M; only if a determinant-sign statement is formalized |
| s05 `Hyp.X.gal`: `TateModuleData` (ℤ_p-module with a continuous G_{Q_q}-action) | `Defs/RepresentationTheory/Rep/Basic.lean`: `Rep.IsContinuousAdic`, `ContinuousZlModule l π`, `ContinuousZlModule.of`, `homMk`; `Topology/Algebra/Nonarchimedean/AdicTopology.lean`: `continuous_smul_iff_isOpen_setOf_smul_sub_mem_pow_smul_top` | **adaptable** (a ready "f.g. ℤ_ℓ-module with continuous action" category; the hypothesis structure can use it instead of the ⟨Frob, τ⟩ model) | Mathlib only + `Weil.Attr` | **S** (215 + 141 lines) |
| s06 / s01 trace of Hecke operators on ℤ_p-lattices with torsion (trace comparisons, `hecke_trace_fixed_point` transfer) | `Defs/LinearAlgebra/Trace.lean`: `LinearMap.ladicTrace` (+ `_add`, `_mul_comm`, `_one`, `_eq_algebraMap_trace`, `_conj`) | adaptable (trace after ⊗ℚ_ℓ, linear and cyclic) | Mathlib only + `Weil.Attr` | S (126 lines) |
| s06 L4 Galois half: tr ρ(gσ)=tr ρ(g) ⇒ ρ(σ)=1; "eigenvalue systems determined by traces" | `LinearAlgebra/Vandermonde/PowerSums.lean`: `Multiset.eq_of_forall_ge_sum_map_pow_eq` | related (multisets in char 0 determined by power sums of large exponent; not the A[G]→M₂(A) argument) | Mathlib only | S (79 lines), optional |
| s06 L1–L3 `IsGorensteinAlg`, `congruenceIdeal`, Lemmas S, G, D, Thm E | — | none | — | n/u |
| s05 geometric route (seed §4): character groups of Néron models, Jacobians of Shimura curves, Eichler–Shimura | étale cohomology of curves over finite fields (`EtaleCohomology/Curves/*`, `Trace/*`) | related in spirit only (no Shimura curves, no Néron models, no reduction of curves over ℚ) | the whole library + Stacks | n/u at hackathon scale |

## 5. Top recommendations

1. **Do not expect help on SA(B¹).** Keep `Hyp.SA` / `Hyp.HS` registered as planned (stage 02 L02.2). Weil confirms
   only that there is no such development in this ecosystem.
2. **Vendor `Weil/Algebra/Module/LAdicRankOfInverseSystem.lean`** (S) for the stage 04 Λ-adic track. `moduleOfTorsion`
   and `linearMapOfTorsion` turn ℤ/p^m-level Brandt/Hecke data into ℤ_p-linear data without hand-written instances.
   `finrank_rationalLimit*` covers rank statements in the limit.
3. **Extract `CategoryTheory.Functor.isMittagLeffler_of_isArtinian`** (S, about 30 lines, modified) for taking limits of
   finite-level exact sequences in the λ-adic Ribet theorem (stage 04) and in `if:s04-Mord`.
4. **Vendor `Weil/Defs/RepresentationTheory/Rep/Basic.lean` (+ `Topology/Algebra/Nonarchimedean/AdicTopology.lean`)**
   (S) if stage 05's `Hyp.X.gal` uses a real continuous Galois module rather than the ⟨Frob, τ⟩ toy model.
5. Optional: `Defs/LinearAlgebra/Trace.lean` (`ladicTrace`) for trace identities over ℤ_p. Vendor it only if a trace
   statement over ℤ_p (not ℚ_p) is actually formalized.
6. Vendor `Weil/Attr.lean` with any of these, or strip the `@[weil …]` attributes and record the change. The first
   keeps the files byte-identical (`modified = no`).

## 6. What is NOT there

Quaternion algebras, orders, class sets, Brandt matrices; adeles / restricted products; GL₂, SL₂, Iwahori/Bruhat;
strong or weak approximation in any form; Hasse–Minkowski, local–global for embeddings, Skolem–Noether; Bruhat–Tits
trees, lattices in Q_p², graphs of groups; group homology H_*(Γ,V) and Shapiro; modular forms, Hecke operators or
algebras, Hida theory, ordinary projectors; Gorenstein rings, congruence ideals; Galois representations of number
fields, Néron models, Shimura curves, Jacobians. The ℓ-adic infrastructure (strict ℓ-adic systems, Artin–Rees
categories) is tied to the Stacks `LAdicSheaf` framework and is too heavy for us.
