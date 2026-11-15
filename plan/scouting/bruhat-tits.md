# Scouting report: chrisflav/bruhat-tits (Ludwig–Merten, Bruhat–Tits tree of GL₂)

Scope: what we can reuse for stage 02 (`plan/staged/stage-02-tree-quotients.tex`, Lemma `lem:s02-tree`, Prop. `prop:s02-harm`,
milestone L02.1), and what is missing. Method: read-only (GitHub API, single-file fetches only; no clone, no build).
Scouted 2026-11-14 at upstream commit `1d61dd553feb2d1ed35c249298304b818765779c` (branch `master`, last push 2026-02-17).
Companion paper: `literature/ludwig-merten_2026_formalising-the-bruhat-tits-tree.pdf`.

## 1. License and attribution
- **License: Apache-2.0** (top-level `LICENSE`, the standard text; the appendix placeholder `Copyright {yyyy} {name}` is
  not filled in). The repository has **no `NOTICE` file**, so §4(d) of the license (reproducing NOTICE) does not apply.
- Every `.lean` file (25 of 25) has the same header:
  `Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved. Released under Apache 2.0 license as
  described in the file LICENSE. Authors: Judith Ludwig, Christian Merten`.
- Our obligations if we vendor files (this is the same scheme as `lean/trace-formula-project-import/lean/Vendor/`):
  1. Ship a copy of Apache-2.0 next to the files (`Vendor/<Name>/LICENSE`).
  2. Keep each file's copyright/author header unchanged.
  3. Each file we modify (and that will be nearly all of them, see §4) needs a prominent change notice
     (Apache-2.0 §4(b)) and must be marked `modified = yes` in `MANIFEST.tsv`, with upstream URL, rev, path and sha256.
  4. Add a section to `Vendor/NOTICE` and `Vendor/ATTRIBUTION.md` naming the project, the authors, the URL and the commit.
  5. Scholarly attribution: cite Ludwig–Merten (the paper above) in the docstrings of the theorems we build on, and
     in `mathematics/` and the talk wherever Lemma tree (a) is credited as formalised.
- Apache-2.0 is compatible with our repository going public. No copyleft constraints.

## 2. Toolchain and Mathlib
- `lean-toolchain`: `leanprover/lean4:v4.19.0`.
- `lakefile.toml`: Mathlib `rev = "v4.19.0"`; `lake-manifest.json` pins Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
  (about April 2025).
- Ours: Lean v4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (2026-10-13). That is 16 minor versions and
  about 18 months of Mathlib drift. **Nothing builds as is.** Any reuse is a port, file by file.
- Drift we confirmed by grep in the frozen Mathlib tree (`/home/janosch/data/mathlib4_v4350`):
  - `Doset.doset` / `Doset.mem_doset` (used in `Cartan/Uniqueness.lean`) no longer exist; they are now
    `DoubleCoset.doubleCoset` (`Mathlib/GroupTheory/DoubleCoset.lean`).
  - The fields of `SimpleGraph.IsTree` are now `connected` and `isAcyclic` (they use `isConnected` and `IsAcyclic` in `BTtree`).
  - Their `_root_.IsLattice` (fields `isFG`, `spans`) is the pre-upstream version of Mathlib's
    `Submodule.IsLattice` (`Mathlib/Algebra/Module/Lattice.lean`, fields `fg`, `span_eq_top`, with `A` an `outParam`).
    A port should switch to Mathlib's class rather than keep a duplicate.
  - `Basis` is now `Module.Basis` (354 occurrences). There are 22 uses of `induction'`, and `erw` appears often.
  - Several helper lemmas were upstreamed by the authors themselves (Mathlib PRs #17433 GL map lemmas, #19808
    projectivization cardinality, #19812 swap matrices, #19902 R-lattices, #23046 `Tuple.unique_antitone`). A crude name
    scan finds about 40 declaration names in `Utils/` that also occur in Mathlib v4.35 (some are false positives). Expect
    duplicate-declaration errors in `Utils/RingHom.lean` (`GL.map_*`), `Utils/Matrix.lean` and `Utils/ValuationRings.lean`.
- Three files use a bare `import Mathlib` (`Cartan/Existence.lean`, `Utils/LinearAlgebra.lean`, `Utils/ValuationRings.lean`).
  Vendor/ replaced these with specific imports before, and we should do the same here (memory and build time).
- No `sorry` in the repository (grep). No axioms declared.

## 3. Overview of contents (25 files, 8257 lines; namespace `BruhatTits`)
The setting is generic: `K` a field, `R : Subring K` with `[IsDiscreteValuationRing R] [IsFractionRing R K]`; regularity
needs `[Finite (ResidueField R)]`. For us, `R := 𝒪[ℚ_[q]]` works as is: in Mathlib v4.35, `𝒪[K]` is `Valuation.integer
(valuation K)`, a `Subring K`. It has `IsDiscreteValuationRing 𝒪[K]` for local fields (`NumberTheory/LocalField/Basic.lean`)
and `IsFractionRing v.integer K` (`RingTheory/Valuation/ValuationRing.lean`). The import's `ℚ_[p]` is an `IsNALF` with
`ValuativeRel`, so its `𝒪[F]` notation matches. Note that `ℤ_[q]` itself is a separate type, not a subring.

| Folder | Content | Lines |
|---|---|---|
| `Cartan/` | Cartan decomposition for **GL_n(K)**, existence (`cartan_decomposition`, `cartan_decomposition'`) and uniqueness (`cartan_decomposition_unique`, `_uniformizer`), double-coset partition (`iUnion₂_doset_cartanDiag_eq_univ`, `disjoint_doset_cartanDiag_of_ne`) | 945 |
| `Lattice/` | `IsLattice`, `structure Lattice` (a lattice in `Fin 2 → K`), homothety `IsSimilar` and its setoid, `GL₂(K)` and `Kˣ` actions, basis "twists" `twist₂`/`ntwist₂` (= diag(ϖ^n, ϖ^m)·basis), `Lattice.standard`, elementary divisors `signature`, distance `dist`, the quotient `L/ϖL` as an `𝓀`-space | 2442 |
| `Graph/` | `Vertices R` (homothety classes), `inv` (distance), `IsNeighbour`, chains, `BTgraph : SimpleGraph (Vertices R)`, connectedness, acyclicity, **`BTtree`**, **`btgraph_regular`** (degree `#𝓀+1`), the neighbours ≃ `ℙ(𝓀, L/ϖL)`, the `GL₂(K)` action (transitive, a graph action), the **stabilisers** of a vertex and of a segment of length n, parity (`IsEven`/`IsOdd`), and the fact that SL₂ preserves parity | 2170 |
| `Harmonic/` | For any `SimpleGraph` with a vertex weight `w : V → Aˣ`: the Laplacian `f ↦ (v ↦ w v • Σ_{e∋v} f e)` on unoriented edges, `IsHarmonic`, **surjectivity of the Laplacian on trees with all degrees ≥ 2** (also as a `G`-equivariant hom), and the BT application `BTlaplace_surjective` with the parity weight | 885 |
| `Utils/` | `GraphAction` class (G acting by graph automorphisms, induced action on `edgeSet`), GL/matrix/valuation helpers, `embDiagonal`, `upperTriangularSubgroup` (in `Utils/Matrix.lean`) | 1815 |

Dependency closures (counted with an import-graph script on the fetched files):
- `Graph.Tree` (BTtree): 21 files, 6765 lines.
- `Graph.Regular`: 22 files, 7055 lines.
- `Graph.GroupAction` (stabilisers): 20 files, 6550 lines.
- `Graph.Orientation` (types): 21 files, 6745 lines.
- `Lattice.Distance`: 9 files, 3072 lines.
- `Cartan.Uniqueness`: 7 files, 2187 lines.
- `Harmonic.Basic`: **2 files, 947 lines** (it depends only on `Utils.GraphAction`). It is independent of the lattice
  machinery.

## 4. Reuse table

Statement match: **exact** means it can be used directly after porting. **adaptable** means a short bridge lemma gives
our statement. **related** means it helps but our statement still needs its own proof.

| Our need (stage / label) | Their declaration (file:name) | Match | Dependencies | Port effort |
|---|---|---|---|---|
| 02 `lem:s02-tree`(a): T_q is a tree | `Graph/Tree.lean:BTtree` (`SimpleGraph.IsTree (BTgraph (R := R))`) | exact (with `R = 𝒪[ℚ_[q]]`); adjacency is `inv = 1`, so to match `def:s02-tree` (qL ⊊ L' ⊊ L) use `isNeighbour_iff` / `IsStandardNeighbour` | Tree closure, 21 files | **L** (about 6.8k lines of drift port); otherwise not usable. The alternative is the registered `Hyp.BTtree` |
| 02 `lem:s02-tree`(a): (q+1)-regular | `Graph/Regular.lean:btgraph_regular`, `btgraph_degree` (degree `Nat.card (ResidueField R) + 1`) | adaptable: we also need `Nat.card (ResidueField 𝒪[ℚ_[q]]) = q`, a small bridge | Regular closure, 22 files | L (included in the tree port) + S (bridge) |
| 02 `lem:s02-tree`(a): neighbours ↔ ℙ¹(L/qL) | `Graph/Regular.lean:neighborSetEquivProjectivization`, `neighborsEquivLines` | exact | same as above | in the L port |
| 02 `def:s02-tree`: vertices = homothety classes, GL₂ action | `Graph/Vertices.lean:Vertices`, `Graph/GroupAction.lean:instance MulAction (GL (Fin 2) K) (Vertices R)`, `IsPretransitive`, `adj_smul_smul_iff_adj`, `GraphAction` instance | exact | Vertices closure (Lattice + Cartan) | M–L |
| 02 `def:s02-tree`: type τ = ord det mod 2 | `Graph/Orientation.lean:Lattice.valuation`, `Lattice.IsEven`, `IsEven`/`IsOdd` (vertices), `BTweight` | exact (they define parity via the det of an R-basis, which equals ord det g for L = gR²) | Orientation closure | in the L port |
| 02 `lem:s02-tree`(b): SL₂ preserves types / acts without inversion | `Graph/Orientation.lean:isEven_specialLinearGroup_smul_iff`, `isOdd_specialLinearGroup_smul_iff`, `GraphAction (SpecialLinearGroup (Fin 2) K) BTgraph` | adaptable: this is only the SL₂ direction. "g preserves types ⇔ ord det g even" and "every edge joins the two types" are **not** there (S, after the port) | Orientation closure | L + S |
| 02 `lem:s02-tree`(c): Stab(v₀) | `Graph/GroupAction.lean:stabilizer_standard_eq_range_map_subtype` (Stab of the lattice R² = GL₂(R)), `stabilizer_mk_standard_eq_sup` (Stab of the vertex = Kˣ·GL₂(R)), `stabilizer_mk_eq_sup`, `stabilizer_smul_standard_eq_map_conj_subtype_range` | adaptable: intersect with SL₂ to get SL₂(ℤ_q) (S) | GroupAction closure | L + S |
| 02 `lem:s02-tree`(c),(d): edge stabiliser = Iwahori; Iw_q = GL₂(ℤ_q) ∩ αGL₂(ℤ_q)α⁻¹ | `Graph/GroupAction.lean:stabilizer_fun_ntwist₂_eq_sup_comap_upperTriangularSubgroup` (pointwise Stab of the lattice chain L₀,…,Lₙ, Lᵢ = (e₀, ϖⁱe₁), = matrices in GL₂(R) upper triangular mod ϖⁿ), `stabilizer_fun_mk_ntwist₂_eq_sup_comap_upperTriangularSubgroup` (vertex version: Kˣ·Iₙ) | adaptable: n = 1 is the edge e₀ = {v₀, v₁} with our convention c ≡ 0 (same base edge, see `rem:s02-treeconv`). (d) follows from the lattice-level n = 1 statement together with the Stab of αR² by conjugation | GroupAction closure; `Utils/Matrix.lean:upperTriangularSubgroup` | L + S |
| 02 `lem:s02-tree`(c): SL₂ transitive on each type and on edges | — (only GL₂ is transitive on vertices: `IsPretransitive`). `Utils/GraphAction.lean` gives a pretransitive action on `edgeSet` *from* a pretransitive action on `Sym2 V`, which is not proved for BT | related | — | we prove it (S–M, the argument in `ss:s02-proofs`) |
| 02 Cartan decomposition (used in Lemma tree / Hecke) | `Cartan/Existence.lean:cartan_decomposition`, `cartan_decomposition'`; `Cartan/Uniqueness.lean:cartan_decomposition_unique` (GL_n over any DVR) | related: **already in our import** for GL₂ over an NALF (`AlgJL/VolI/P0/Decompositions.lean:cartan_decomposition`, `cartan_unique`, using `DoubleCoset`) | 7 files | not needed (use the import) |
| 02 `prop:s02-harm`: harmonic cochains | `Harmonic/Basic.lean:SimpleGraph.laplace`, `IsHarmonic`, `laplaceLinearMap`, `laplaceSMulHom` (G-equivariant), `laplace_surjective` (trees, min degree ≥ 2); `Harmonic/Application.lean:BTlaplace_surjective` | related: these are unoriented edges with a ±1 vertex weight. Per `rem:s02-treeconv` their `ker Δ` equals our oriented harmonic cochains on the tree, but our Prop. harm is about **Γ_U-invariant** cochains and the q-new kernel on the **finite quotient**. Surjectivity, equivariant, gives the exact sequence 0 → Harm → C(E) → C(V) → 0 of Γ_U-modules on T_q, a possible ingredient for L02.6 | `Harmonic.Basic` + `Utils.GraphAction` only (947 lines) | **S–M** to vendor `Harmonic/Basic.lean` alone (graph-generic, mild drift). The BT application needs the L port |
| 02 graph actions (L02.2/L02.3 incidence structures) | `Utils/GraphAction.lean:GraphAction`, the `MulAction G X.edgeSet` instance | related: `SimpleGraph`-based. Our quotient graphs need quivers or E ⇉ V (loops, multi-edges) | none (Mathlib only) | S (100 lines). Mainly a design pattern |
| 02 lattice distance / elementary divisors | `Lattice/Distance.lean:dist`, `signature`, `exists_normal_basis` | related (needed only for the tree proof) | 9 files | M (only together with the tree) |

## 5. Top recommendations
1. **Do not port the tree for the hackathon.** As `stage-02` L02.1 already says, tree-ness is not needed for the SA-free core
   (L02.3) or for the free case over the finite graph (L02.5). Register `Hyp.BTtree` (shaped like their `BTtree` +
   `btgraph_regular` + `neighborSetEquivProjectivization`, over `R = 𝒪[ℚ_[q]]` and their definitions) and cite
   Ludwig–Merten. This keeps our statement aligned with their API, so a later port can discharge the hypothesis.
2. **If a port is attempted** (after the hackathon, or by a dedicated long-horizon agent), port the 21-file closure of
   `Graph/Tree.lean` + `Graph/Regular.lean` + `Graph/Orientation.lean` + `Graph/GroupAction.lean` (about 7k lines) into
   `Vendor/LudwigMerten/`, with `modified = yes` and change notices. Do it in this order: replace `IsLattice` by Mathlib's
   `Submodule.IsLattice`; delete the `Utils` lemmas that are now upstream; rename `Doset`→`DoubleCoset` and `Basis`→`Module.Basis`;
   fix `IsTree` fields. Then the stabiliser lemmas give Lemma tree (c),(d) for GL₂ almost for free. Estimate **L**
   (several agent-days). Skip `Cartan/` where possible (the import has GL₂ Cartan), but the lattice distance depends on it
   (`Lattice/Distance.lean` imports `Cartan.Uniqueness`), so it cannot be dropped without rewriting `Distance`.
3. **Cheap win:** vendor `Harmonic/Basic.lean` + `Utils/GraphAction.lean` (947 lines, no BT dependency). This gives a
   generic, equivariant Laplacian on graphs with surjectivity on trees, for the harmonic-cochain / H¹ side (L02.6, Prop.
   harm on T_q). Effort S–M. Worth it only if L02.6 is actually scheduled.
4. Reuse their **conventions** even without code: base edge (e₀, ϖe₁) with I₁ = upper triangular mod ϖ (c ≡ 0), parity
   via ord det. These already agree with `def:s02-tree` and `rem:s02-treeconv`.
5. Lemma tree (b) (GL₂ direction, edges join opposite types) and (c) (SL₂ transitivity) must be proved by us in any case.
   Both are short and should be phrased so that they plug into their `IsEven` / `stabilizer_*` API.

## 6. What is NOT there
- Anything quaternionic: no B, B¹, orders, S-arithmetic groups Γ_U = O_U[1/q]¹, and **no strong approximation** (neither
  for B¹ nor for SL₂). The stage-02 gap `if:s02-SA` / L02.SA is **not** closed by this repository.
- No quotient graphs Γ\T, graphs of groups, fundamental domains, or amalgams (Serre I.4, II.1.4). No free-action ⇒ free-group
  result (Serre I.3.3). No Ihara/Serre II.1.5.
- No group (co)homology of groups acting on the tree, no two-term complex (`prop:s02-coh`), no Γ-invariant harmonic
  cochains, no Hecke operators on the tree.
- No oriented edges or quiver structure. Edges are `SimpleGraph.edgeSet` (unordered `Sym2`).
- No SL₂ / PGL₂-specific results beyond "SL₂ preserves parity": no transitivity of SL₂ on the types or on edges, no
  SL₂-stabilisers, no PGL₂ action.
- No specialisation to ℚ_q / ℤ_q, and no computation of `#ResidueField = q`.
- No higher-rank buildings (only GL₂). Cartan is GL_n, but only GL₂ is used downstream.
- No other branches with extra material. The single PR (#1, "compute stabilizer of an edge") is already merged.
