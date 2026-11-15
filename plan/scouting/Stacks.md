# Scouting report: AxiomMath/Stacks

I scouted the repo on 2026-11-14 through the GitHub API only: repo metadata, the recursive tree (per sub-directory,
because the root tree is truncated), about 60 individual files fetched raw, and code search. Nothing was cloned or
built. I inspected upstream commit `c496df0d9beea9deaeabcea8492605f9a0a2313b` (`main`, 2026-11-11, "feat: refine
existing formalizations (#17)").

**Bottom line.** Stacks does **not** close the stage-02 gap. It has no strong approximation for B¹, no weak
approximation for algebras, no Hasse–Minkowski or Hasse–Schilling, no Bruhat–Tits tree, no SL₂(ℤ)/amalgams and no
quaternion algebras. Two things are worth taking:

1. **Skolem–Noether, human-reviewed (StacksCore).** The staged plan says it is missing from our frozen Mathlib (that is
   correct). Here it is a closed set of 8 files (893 lines) that import only Mathlib, with the same Lean and the same
   Mathlib rev as ours. It covers sub-milestone L02.SA(e) exactly. It sits next to the rest of the central-simple-algebra
   theory: the double centralizer theorem, maximal subfields, splitting fields, the Brauer group and Wedderburn–Artin.
2. **Weighted-graph lattice algebra (StacksFrontier, Semistable Reduction chapter).** This is a weighted multigraph
   model `src tgt : E → V`, `w : E → ℤ`, with:
   - the incidence map and its weighted adjoint;
   - connectivity stated as a cut condition;
   - rank formulas for the kernel;
   - "cuts^⊥ = cycles";
   - the discriminant group `M⁺/M` of an integral lattice, and the 0C6W iso: torsion of coker(d*d) ≅ the discriminant
     group of im d.

   This is the same shape as stage 03's Lean milestones L1–L3 (`X(G)`, `Φ^comb`, Lemma bip), and the closure is
   Mathlib-only (2.8k lines). Many of the useful graph lemmas are `private`, so they must be vendored with a small
   modification.

## 1. License and attribution

- **License: Apache-2.0.** `LICENSE` at the root is the unmodified Apache text, with the appendix template line
  `Copyright [yyyy] [name of copyright owner]` left unfilled. `formalization.yaml` repeats `license: "Apache-2.0"`.
- **There is no `NOTICE` file**, so Apache §4(d) adds nothing.
- **No file has a copyright header.** Files start directly with `module`.
- **Authors.** `formalization.yaml` lists Kenny Lau, Brian Nugent, Ashvin A. Swaminathan and Yunzhou Xie as authors and
  maintainers. It says the formalization was "generated collaboratively between human formalisers at Axiom Math and
  AxiomProver". The commits are by Ashvin A. Swaminathan and Kenny Lau.
- **Suggested ATTRIBUTION row:** "no per-file header upstream; Copyright AxiomMath (Axiom Math, https://axiommath.ai/),
  Apache-2.0; authors per upstream formalization.yaml: Kenny Lau, Brian Nugent, Ashvin A. Swaminathan, Yunzhou Xie
  (with AxiomProver)".
- **Source text.** The statements come from the Stacks Project, which is GFDL-licensed: "Statements taken from the
  Stacks project at commit a5811b23…". We copy only Lean code and Stacks tag numbers, never Stacks LaTeX, so the GFDL
  does not reach us. If we quote Stacks prose in `mathematics/` or `talk/`, the GFDL applies to that prose.
- **Tiers.** `StacksCore` is human-reviewed and brought to Mathlib standards. `StacksFrontier` is written by AI agents
  and not yet reviewed, but upstream says it is kernel-checked and axiom-clean. Treat Frontier statements with the usual
  care. One example: the file `DiagonallyDominant.lean` records that Stacks 0C5V *as printed* is false and adds a
  symmetry hypothesis.
- **Obligations when vendoring.** Follow the existing `lean/trace-formula-project-import/lean/Vendor/` scheme:
  - copy the files to `Vendor/AxiomStacks/StacksCore/…` (and `…/StacksFrontier/…`), keeping the upstream module paths;
  - the Apache LICENSE is already in `Vendor/LICENSE`;
  - add one row per file to `MANIFEST.tsv` (upstream URL, rev `c496df0d9bee…`, path, sha256 values) and to
    `ATTRIBUTION.md`, and a paragraph to `Vendor/NOTICE`;
  - any change (for example making a `private` lemma public, or trimming imports) needs a change notice at the top of
    the file (§4(b)) and `modified = yes`.

## 2. Toolchain and Mathlib

| | Stacks | ours |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.35.0` | `leanprover/lean4:v4.35.0` |
| Mathlib rev (`lake-manifest.json`) | `56a005855ea17e0b0958f73ec801ae140b0a1679` (`inputRev v4.35.0`) | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| other deps | only Mathlib's own (plausible, LeanSearchClient, importGraph, ProofWidgets, aesop, Qq, batteries) | same |

- **The match is exact. There is zero API drift.** The README still says "v4.34.0-rc2", but that is stale: commit #7
  bumped the project to v4.35.0.
- Files use the Lean module system (`module`, `public import`, `@[expose] public section`), like our frozen Mathlib. A
  non-module file in `AlgJL` can import a vendored module file.
- Upstream `lakefile.toml` sets `maxSynthPendingDepth = 3`, `autoImplicit = false` and a few weak linter options. A
  vendored library should set `maxSynthPendingDepth = 3`, as `AlgJLVendorImperial` already does.
- **A new `lean_lib` (for example `AlgJLVendorStacks`, `srcDir = "Vendor/AxiomStacks"`, globs `StacksCore.+`,
  `StacksFrontier.+`) is a lakefile edit.** The import's lakefile header forbids editing it. This needs master approval,
  or the libraries go in the main `lean/` project instead.
- `@[stacks TAG]` is Mathlib's attribute, but most files import `StacksCore.Tactic.StacksAttribute`, which imports
  `StacksCore.Tactic.EgaSgaAttribute` (78 + 210 lines, Lean/Mathlib only) for `@[ega …]`, `@[sga …]` and
  `stacks_fixed`. Vendor these two files as they are. That is simpler than stripping the attributes, and it keeps the
  other files byte-identical.

## 3. Overview of contents

- **Size.** About 49.8k `.lean` files, which upstream counts as about 63,000 modules including generated ones.
  - `StacksCore`: 445 files, human-reviewed. Mostly the algebra prerequisites, from category theory, ring theory and
    field theory through to central simple algebras.
  - `StacksFrontier`: about 44.6k files under `AlgebraicGeometry/`, about 19k elsewhere. AI-written.
- **Coverage.** The library is a formalization of every formalizable Stacks tag, organised by chapter:
  - schemes, cohomology, algebraic spaces and stacks;
  - étale cohomology, Brauer groups (via Galois cohomology), curves and semistable reduction;
  - commutative algebra: Fitting ideals, Gorenstein rings, dualizing complexes, Mittag-Leffler, completions;
  - simplicial methods.
- **Number-theory odds and ends** that are not Stacks chapters as such:
  - `StacksFrontier/NumberTheory/Adeles/*`: GL₂/GLₙ unramified cusp forms and Hecke operators over a *general field*
    whose places are valuation subrings. In effect these are function fields; the archimedean place is not modelled.
  - `NumberTheory/Drinfeld/*`: lattices in K_v², the q_v+1 Hecke sublattices, shtukas.
  - `NumberTheory/TraceFormula/*`: Grothendieck–Lefschetz style.
  - `NumberTheory/Padics/LAdic*`.

## 4. Match table

The status column uses three values:
- **exact**: the declaration proves our statement as it is;
- **adaptable**: same mathematics, but it needs a wrapper or a specialisation;
- **related**: same circle of ideas, but not directly usable.

Effort S/M/L is the cost of vendoring the files under `Vendor/` (Mathlib-only closure, rev-identical) plus adapting
them. Line counts are the transitive Stacks-internal import closure, which I computed by walking `import` lines over the
API.

| Our need (stage / label) | Their declaration (file : name) | Match | Dependencies (Stacks-internal closure) | Port effort |
|---|---|---|---|---|
| 02 / L02.SA(e): Skolem–Noether for elements (Voight Cor. 7.7.3): α₁, α₂ ∈ B with the same minimal polynomial are conjugate | `StacksCore/RingTheory/SkolemNoether.lean : skolemNoether` (Tag 074Q): `∀ f g : B →ₐ[K] A`, with B simple and A finite-dimensional central simple, `∃ x : Aˣ, ∀ b, g b = x * f b * x⁻¹`; `skolemNoether'` (074R): every automorphism is inner | **exact** (apply it to `K = ℚ`, `B = ℚ[x]/(m)`, a field and hence simple, and `A` = our quaternion algebra, given `Algebra.IsCentral ℚ A` and `IsSimpleRing A`) | 8 files, 893 lines: `Morita/SimpleRing`, `SimpleRing/{DivisionRing,TensorProduct}`, `TwoSidedIdeal/{Operations,SpanAsSum}`, `ModuleCat/Basic`, `Dimension/Finite`. Mathlib only, and **no** attribute files | **S** (vendor as is). Extra glue: instances `IsCentral`/`IsSimpleRing` for the import's `QuatAlg a b`. Mathlib has `IsSimpleRing` for division rings, and `IsCentral` for `ℍ[R,a,b,c]` may need a short proof |
| 01 / local structure, L1: inner automorphisms of B and M₂(ℚ_q); "every automorphism of B_q ≅ M₂(ℚ_q) is conjugation" (used for ι_q-independence and for normalisers of orders) | same file : `skolemNoether'` | **adaptable** | as above | S |
| 01 / L1, 02 / Lemma normone: maximal commutative subalgebras of B are quadratic fields, `dim C_B(L)·dim L = dim B`, `C_B(C_B(L)) = L` | `StacksCore/RingTheory/SimpleRing/Centralizer.lean : Subalgebra.centralizer_isSimple`, `finrank_centralizer_mul_finrank`, `centralizer_centralizer` (074T), `isMaximal_comm_iff_finrank` (074V/074W) | **adaptable** (general CSA; for quaternions this gives "commutative ⟹ dim ≤ 2") | part of the 52-file / 5.5k-line CSA closure below, which includes the attribute files | M (vendor the whole CSA block once) |
| 02 / L02.SA(d) support: a quadratic field L ⊂ B splits B (`L ⊗ B ≅ M₂(L)`); splitting fields embed (Voight 14.6.x direction "L ↪ B ⟸ L splits B") | `StacksCore/Algebra/Split/{Basic,Finrank,Embedding,DivisionRing,CentralSimple}.lean : Algebra.IsSplit` (074Y), `IsCentralSimple.split_of_finrank` (074Z "(2)⇒(1)"), `IsSplit.exists_embedding` / `isSplit_iff_exists_similar` (074Z), `isSplit_of_maximal_comm` (0750), `exists_separable_maxSubfield` (0752, Koethe), `isCentralSimple_tfae` (0753) | **related** (field-theoretic half only; the hard *local–global* part (d), Hasse–Minkowski, is **not** here) | CSA closure: 52 files, 5,497 lines, Mathlib + the 2 attribute files | M |
| 01 / Hyp layer: degree of a CSA, `dim = d²`; the Brauer group (only if Brauer-class language is wanted, for example "B_D determined by its ramification") | `StacksCore/Algebra/Split/Basic.lean : isSquare_finrank` (074N), `degree`; `StacksCore/Algebra/BrauerGroup/{Basic,BaseChange}.lean : BrauerGroup` `CommGroup` (074L), `baseChange` | **related** (no local invariants, so no classification of B_D) | CSA closure | M, low value |
| 01: Wedderburn–Artin (B a division algebra, or B ≅ M₂(ℚ)) | `StacksCore/RingTheory/SimpleModule/WedderburnArtin.lean` (074K (ii),(iii)); Mathlib already has `IsSimpleRing.exists_algEquiv_matrix_divisionRing(_finite)` | related; Mathlib already suffices | — | not needed |
| 03 / Def. `def:s03-graph`, L1: weighted multigraph `(V,E,s,t,w)`, `∂ : ℤ[E] → ℤ[V]`, `⟨e,e'⟩_w = w_e δ` | `StacksFrontier/AlgebraicGeometry/SemistableReduction/LinearAlgebra/CycleRank.lean` (private): `incidenceMap src tgt : (V→ℤ) →ₗ (E→ℤ)` (coboundary, x ↦ x∘src − x∘tgt), `weightedAdjoint src tgt w : (E→ℤ) →ₗ (V→ℤ)` (∂∘W), `weightedDotForm w` (with `_isSymm`, `_pos`), `incidence_weighted_adjoint` (the adjunction) | **adaptable** (same data and conventions as ours, multigraphs allowed, not `SimpleGraph`; the sign convention must be matched to α = (−s₀*, s₁*)) | CycleRank → DiscriminantGroup → attribute files: 4 files, about 2.07k lines, Mathlib only | **S–M** (vendor; change notice: make about 10 `private` lemmas public, or copy them) |
| 03 / Lemma `lem:s03-bip`(a) rank: `rk H₁ = \|E\| − \|V\| + 1` for connected G | CycleRank.lean (private) `finrank_ker_weightedAdjoint`: `rk ker(∂W) + \|V\| = 1 + \|E\|` under positive weights and the cut-connectivity hypothesis; `finrank_ker_incidence_eq_one` (over any domain: ker δ = constants, rank 1) | **adaptable** (with w = 1 this is the H₁ rank formula; the weighted version is the same rank) | as above | S–M |
| 03 / Lemma bip(b): ker ∂^∨ is the diagonal; Cor. ihara(ii) shape | CycleRank.lean `finrank_ker_incidence_eq_one`; `DiagonallyDominant.lean : dotProduct_mulVec_eq_zero_iff_of_positive_kernel` (0C5X: the quadratic form of a connected Laplacian vanishes only on the line of the kernel vector) | **adaptable** (over a field or domain; for an arbitrary abelian group A, our (b) needs a separate, easy argument) | DiagonallyDominant: 393 lines + attribute files, Mathlib only (it imports `Mathlib.Tactic` wholesale: trim it) | S |
| 03 / Def. Φ^comb := coker(X(G) → Hom(X(G),ℤ)) | `…/LinearAlgebra/DiscriminantGroup.lean : LinearMap.BilinForm.SubmoduleDiscriminantGroup form A` = `Dual ℤ A ⧸ range (form.restrict A)` | **exact as a definition** (take `A = X(G) = ker ∂ ⊂ ℤ[E]` and `form = ⟨,⟩_w`) | 384 lines + attribute files, Mathlib only | **S** |
| 03 / Prop. `prop:s03-phi`, Thm ribet: Φ^comb versus the vertex-side cokernel; "cuts^⊥ = cycles" | DiscriminantGroup.lean : `torsionCokernelEquiv_discriminantGroup_range` (0C6W): for adjoint d, d* of positive-definite lattices with a unimodular source, `torsion(L₀/ im d*d) ≃ SubmoduleDiscriminantGroup form₁ (range d)`; `exists_injective_to_discriminantGroup_{left,orthogonal}` (0C6V); CycleRank (private) `range_incidenceMap_orthogonal_eq_ker_weightedAdjoint` | **adaptable** (0C6W with d = δ gives the *cut* lattice's discriminant group; to get Φ^comb on cycles use 0C6V with `A = range δ`, `A^⊥ = ker ∂W`; the comparison is exact for w = 1 because ℤ[E] is then unimodular, but not in general) | as above | M (the glue is a page of lemmas; the substance is there) |
| 03 / L3: \|ℤ^E / (Wℤ[E]⁰ + ℤ1)\| as \|det\| | none in Stacks. **Mathlib** has `AddSubgroup.index_eq_natAbs_det`, `Submodule.natAbs_det_basis_change` (`Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean`) | — | — | use Mathlib |
| 03 / Prop. mazur, 05 / Rem. grothendieck: component group of a semistable model as a lattice cokernel | `…/SemistableReduction/PicardGroup/Defs.lean : NumericalType.picardGroup` (0C7H), `picardGroup_embeds_intersectionCokernel` (0CE7); `NumericalType/Defs.lean : NumericalType` (0C6Z); `CycleRank.lean : Matrix.finrank_torsionBy_matrixCokernel_le_cycleRank` (0C6X) | **related** (vocabulary for the "Φ^comb = component group" remark only; we do not formalize that dictionary) | about 360 lines + attribute files | S, low value |
| 02 / L02.1 Lemma tree(b)–(d): the neighbours of a vertex [Λ] are the q+1 index-q sublattices, in bijection with P¹(F_q); stabiliser of O_q² is GL₂(O_q) | `StacksFrontier/NumberTheory/Drinfeld/Lattice/Hecke.lean : IsHeckeSublattice`, `isHeckeSublattice_stdLattice_iff`, `heckeLine_bijective` (`q_v + 1` sublattices ↔ lines of κ_v²); `…/Lattice/Local.lean : translate_stdLattice_eq_iff` (stabiliser = GL₂(O_v)), `exists_eq_translate_stdLattice` | **adaptable in content, not in packaging**: `v : Place K` is a valuation subring of a general field `K` and `K_v` is `v.1.valuation.Completion`, not Mathlib's `ℚ_[q]` | **157 files, 66k lines** (it pulls in `GlobalFunctionField.HeckeData` and from there much of Frontier) | **L to vendor; M to re-prove** following their proof for `ℤ_[q] ⊂ ℚ_[q]` (about 950 lines of their proofs to mine). Alternative: Ludwig–Merten (see `bruhat-tits.md`) |
| 04 / Def. M^ord := lim_s e ℤ_p[S_s]: exactness of lim on Mittag-Leffler towers (control and limit arguments) | `StacksFrontier/Algebra/MittagLeffler/InverseSystem.lean : invLimit_exact` (Tag 0598: lim is exact on ML systems of abelian groups over a countable directed set) | **adaptable** | 765 lines + `EgaSgaAttribute`; Mathlib only, **but it has about 30 spurious Mathlib imports** (UpperHalfPlane, Bernstein, LucasLehmer …), so trim them | S |
| 04 / L1: ordinary projector e = lim U_p^{n!} on finite modules | none in Stacks. **Mathlib:** the Fitting decomposition `LinearMap.eventually_isCompl_ker_pow_range_pow` (`Mathlib/RingTheory/Artinian/Module.lean`) | — | — | use Mathlib |
| 06 / Def. A-Gorenstein (Hom_A(S,A) free of rank one over S), Lemmas S, G, D | `StacksFrontier/RingTheory/Dualizing/Gorenstein.lean : IsGorensteinLocalRing` (0DW7, through dualizing complexes), `isGorensteinLocalRing_iff_residueField_ext_vanishing` (0BJI) | **related, not usable** (a ring-theoretic Gorenstein notion; the comparison with our relative notion for a finite flat S over regular Λ is not formalized) | large (Dualizing chapter) | not usable |
| 06: Fitting ideals (only if 𝔠_q or 𝔱_q are phrased through Fitt₀) | `StacksFrontier/RingTheory/Fitting/Basic.lean : fittingIdeal` (07Z9), `fittingIdeal_basic_properties` (07ZA) | **related** | **451 files, 41.8k lines** | L, not usable. Mathlib v4.35.0 has no `fittingIdeal`; re-prove the few lines we need |
| 02 / Prop. coh (Shapiro, group homology) | `StacksFrontier/AlgebraicGeometry/EtaleCohomology/GroupCohomology/Shapiro.lean : shapiroIso` (for *profinite* G, discrete modules, via Ext) | related, not usable (wrong setting) | big | not usable. **Mathlib** has `RepresentationTheory/Homological/GroupHomology/Shapiro.lean` and `LowDegree.lean` |
| 01/02: adeles, GL₂(𝔸), Hecke operators T_v | `StacksFrontier/NumberTheory/Adeles/{UnramifiedCuspForm,HeckeEigenform}.lean : Stacks.Adeles.Place`, `AdeleRing`, `heckeOperator` | related, not usable: places are valuation subrings (for ℚ: finite places only), and there is no diagonal map K → 𝔸 for a general field. Our import's `FinAdele` (restricted product, as in ImperialFLT) is better | — | not usable |

## 5. Top recommendations

1. **Vendor the Skolem–Noether closure now** (8 files, 893 lines, Mathlib-only, rev-identical; no attribute files
   needed). It discharges L02.SA(e) unconditionally and gives inner automorphisms for stage 01. Add the two instance
   proofs `Algebra.IsCentral ℚ (QuatAlg a b)` and `IsSimpleRing (QuatAlg a b)` (or use the division-ring instance in
   the definite case). This is the cheapest real win in the repo. It does **not** remove `Hyp.SA`; the dominant cost
   L02.SA(d) remains.
2. **Vendor the semistable-reduction linear algebra for stage 03**:
   - `DiscriminantGroup.lean`, `CycleRank.lean` and `DiagonallyDominant.lean`, plus `StacksCore/Tactic/{StacksAttribute,
     EgaSgaAttribute}.lean`: about 2.8k lines, Mathlib only;
   - define `Φ^comb := SubmoduleDiscriminantGroup ⟨,⟩_w (ker ∂)` directly;
   - take Lemma bip's rank formula and the connectivity lemmas from CycleRank's (currently `private`) incidence
     lemmas. Vendor with a change notice "private → public" (`modified = yes`) rather than copying by hand, so the
     provenance stays clean.
3. **Optionally, the whole StacksCore CSA block** (centralizers, splitting fields, Koethe: 52 files, 5.5k lines),
   but only if someone actually starts L02.SA(d) or a Lemma normone proof. Otherwise the cost is not worth it during the
   hackathon.
4. **For the tree (L02.1(b)–(d)),** do not vendor the Drinfeld lattice files (66k-line closure). Use
   `Drinfeld/Lattice/{Local,Hecke}.lean` as a proof blueprint for `ℤ_[q] ⊂ ℚ_[q]`, or follow the Ludwig–Merten route
   already scouted in `bruhat-tits.md`.
5. **`MittagLeffler/InverseSystem.lean : invLimit_exact`** is a cheap pickup for stage 04 if an exact-lim step appears.
   Vendor it with the import list trimmed (a modification).
6. **Process.** Any vendoring needs a new `lean_lib` in a lakefile. The import's lakefile is frozen by its header, so
   this needs a master decision: either a new library in the import with approval, or the main `lean/` project. Nothing
   else changes: same Lean, same Mathlib rev, no new dependencies.

## 6. What is NOT there

These are absent (checked by tree and path grep and by code search):
- quaternion algebras by name;
- reduced norm or trace for CSAs;
- strong approximation (any group) and weak approximation for algebras;
- Hasse–Minkowski, Hasse–Schilling and local–global principles;
- local class field theory and Hasse invariants of local Brauer groups;
- B¹ = [B^×, B^×];
- orders, class sets, Eichler orders and mass formulas;
- the Bruhat–Tits tree, buildings and Serre's trees (amalgams, graphs of groups, quotient graphs);
- SL₂(ℤ) generators;
- group homology of discrete groups (Frontier has the profinite and Galois version only; Mathlib has the discrete one);
- Hecke algebras of double cosets for ℚ;
- Hida theory, Λ = O[[T]]-specific results, and ordinary projectors;
- congruence ideals, and Gorenstein in the relative sense of stage 06;
- Néron models, character groups of tori, Grothendieck's monodromy pairing (only the combinatorial numerical-type and
  Picard-group shadow, 0C6Z–0C7H);
- modular curves and Shimura curves, and Čerednik–Drinfeld;
- Jacquet–Langlands in any form.

The `NumberTheory/Adeles` and `Drinfeld` material is for function fields (places = valuation subrings, no archimedean
place). It cannot stand in for our ℚ-adeles.
