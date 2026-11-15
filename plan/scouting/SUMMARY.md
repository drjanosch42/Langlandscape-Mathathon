# Lean scouting summary (Stacks, Weil, bruhat-tits)

All three repositories are **Apache-2.0**, with no NOTICE file. Reports were read-only (GitHub API only); status of every claim: *cited* from the per-repo reports.

| Repo | License / copyright holder to name | Lean / Mathlib | Port effort |
|---|---|---|---|
| AxiomMath/Stacks | Apache-2.0; AxiomMath, authors per `formalization.yaml` (Lau, Nugent, Swaminathan, Xie, AxiomProver) | v4.35.0 / `56a005855ea1` (**identical to ours**) | none (API-compatible) |
| AxiomMath/Weil | Apache-2.0; AxiomMath (no file headers) | v4.34.0-rc2 / `16edf57` (ours is 1019 commits ahead) | S per file |
| chrisflav/bruhat-tits | Apache-2.0; every file "© 2024 Judith Ludwig, Christian Merten" | v4.19.0 / `c44e0c8` (Apr 2025) | L (about 21 files, 7k lines); Laplacian only about 947 lines |

**Licensing for publication.** Apache-2.0 is compatible with publishing our repo. Obligations when vendoring: copy LICENSE, keep file headers, add change notices for modified files, add MANIFEST/ATTRIBUTION rows (as in the existing `Vendor/`), and cite the sources. For Stacks and Weil the notice names the repo owner, because the files carry no headers.

## Best source per planned item

| Item (stage / label) | Best source | Match | Effort |
|---|---|---|---|
| Skolem–Noether (L02.SA(e), inner automorphisms of quaternion algebras) **STAGE-1** | Stacks: `skolemNoether`, `skolemNoether'` (Tags 074Q/074R; 8 files, 893 lines, Mathlib only) | exact | S; still need instances saying our `QuatAlg` is central simple |
| Strong approximation for B¹ (stage 02) | **nobody** | none | stays `Hyp.SA`/`Hyp.HS` |
| Bruhat–Tits tree, (q+1)-regularity, stabilisers, Iwahori, parity (stage 02) | bruhat-tits: `BTtree`, `btgraph_regular` and others; Stacks Drinfeld files as a blueprint only | exact | L; keep `Hyp.BTtree` for now |
| Generic Laplacian, surjective on trees (L02.6) | bruhat-tits, Laplacian file plus one dependency | adaptable | M |
| Lemma tree (b) for GL₂, SL₂ transitivity (c) | nobody | – | prove ourselves (short) |
| Φ^comb, weighted-graph lattice algebra, discriminant groups (stage 03) | Stacks: `SubmoduleDiscriminantGroup`, CycleRank, 0C6V/0C6W (about 2.8k lines; AI-written; many `private` lemmas) | adaptable | M (private→public notices) |
| Mittag-Leffler / `invLimit_exact` (stage 04) | Weil `isMittagLeffler_of_isArtinian`; Stacks `invLimit_exact` | exact / adaptable | S |
| ℤ_p-module structure on p^N-torsion, ladic ranks (stages 04–05) | Weil `LAdicRankOfInverseSystem.lean` | exact | S |
| Continuous ℤ_p-module with Galois action (`Hyp.X.gal`) | Weil `ContinuousZlModule`, `AdicTopology` | adaptable | S |
| Fitting ideals, dualizing-complex Gorenstein, function-field adeles | not usable (42k-line closure, wrong notion) | – | – |
| Hecke operators, quaternion algebras, adeles, GL₂/SL₂ | none in any of the three | – | – |

## Items affecting stage 1 of the implementation plan
- **STAGE-1** Skolem–Noether from Stacks: vendor the 8 files. Add the instances that `QuatAlg` is central and simple.
- **STAGE-1** Open master decision: vendoring needs a new `lean_lib`, and the lakefile header of the import forbids editing it. Either approve the edit or place the library in the main `lean/` project.
- **STAGE-1** The identical toolchain and Mathlib rev of Stacks means no porting drift, so Stacks is the only repo to vendor from in stage 1.
- **STAGE-1** Strong approximation for B¹ is not available anywhere. Keep it as the registered hypothesis `Hyp.SA`.

## Recommendations
1. Vendor Stacks Skolem–Noether now.
2. Vendor the small Weil files when stages 04–05 start.
3. Keep `Hyp.BTtree`; do a bruhat-tits port (several agent-days) only after the hackathon.
4. Vendor the Stacks lattice algebra for stage 03 only if Φ^comb is scheduled.

Per-repo details: `Stacks.md`, `Weil.md`, `bruhat-tits.md` in this directory.
