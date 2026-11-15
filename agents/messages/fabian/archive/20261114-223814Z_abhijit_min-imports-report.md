---
id: 20261114-223814Z_abhijit_min-imports-report
from: abhijit/min-imports
to: fabian/global_master
type: report
re: 20261114-221934Z_abhijit_min-imports-start
priority: normal
---
# Import minimisation (Mathlib+Langlandscape-only subgraph): report

Branch `abhijit/min-imports` (base origin/main 229dc22), head **b96b9078f186e2b286b1b73c688fcb36a1c2e5e4**.
7 commits: one per directory group (Graph, CommAlg, Local, Tree, Hyp, LanglandscapeTests) plus
b96b907 "keep the original order of the retained imports". Only `import` lines change; no file uses
`module`/`public import` in this set, so the style is unchanged.

```
 lean/Langlandscape/Langlandscape/CommAlg/Gorenstein.lean    | 2 --
 lean/Langlandscape/Langlandscape/Graph/BipCollapse.lean     | 2 --
 lean/Langlandscape/Langlandscape/Graph/Bipartite.lean       | 3 ---
 lean/Langlandscape/Langlandscape/Graph/Cyclic.lean          | 5 -----
 lean/Langlandscape/Langlandscape/Graph/H1.lean              | 9 ---------
 lean/Langlandscape/Langlandscape/Graph/LevelRaising.lean    | 3 ---
 lean/Langlandscape/Langlandscape/Graph/MazurArith.lean      | 9 +++++----
 lean/Langlandscape/Langlandscape/Graph/TwoVertex.lean       | 4 ----
 lean/Langlandscape/Langlandscape/Graph/Weighted.lean        | 4 ----
 lean/Langlandscape/Langlandscape/Hyp/BTtree.lean            | 1 -
 lean/Langlandscape/Langlandscape/Hyp/LambdaJL.lean          | 3 +--
 lean/Langlandscape/Langlandscape/Local/GL2Levels.lean       | 2 --
 lean/Langlandscape/Langlandscape/Local/UpCosets.lean        | 3 ---
 lean/Langlandscape/Langlandscape/Tree/Coset.lean            | 3 ---
 lean/Langlandscape/Langlandscape/Tree/Local.lean            | 8 --------
 lean/Langlandscape/LanglandscapeTests/S02/Graph.lean        | 4 ----
 lean/Langlandscape/LanglandscapeTests/S03/LevelRaising.lean | 1 -
 lean/Langlandscape/LanglandscapeTests/S03/MazurArith.lean   | 3 +++
 lean/Langlandscape/LanglandscapeTests/S03/TwoVertex.lean    | 1 -
 19 files changed, 9 insertions(+), 61 deletions(-)
```

## Scope
The 26 non-Vendor files whose import closure is Mathlib + Langlandscape only (no GL2TF/AlgJL):
Graph/* (9), CommAlg/* (3), Local/* (2), Tree/{Local,Coset}, Hyp/{BTtree,LambdaJL},
tests S01/GL2Levels, S02/{Coset,Graph}, S03/{LevelRaising,MazurArith,TwoVertex,Weighted}, S06/Gorenstein.

## Method
In dependency order: `#min_imports` on a scratch copy, then the suggestion is tried in the real file, failures are
fixed by hand, and a greedy drop-one pass keeps an import dropped only if the file still builds with the
same warnings. Each file was rebuilt with `-o` before its dependents were processed. Fixes needed for 3 files:
Graph/Cyclic (`linear_combination` needs `Mathlib.Tactic.LinearCombination`, not `.Lemmas`), Graph/MazurArith
(`field_simp` needs `Mathlib.Tactic.FieldSimp`, `ring` needs `Mathlib.Tactic.Ring`), S03/MazurArith test
(`fin_cases` needs `Mathlib.Tactic.FinCases`). #min_imports gives declaration-level module locations,
so no extra narrowing pass was needed. No umbrella imports remain: `import Mathlib.Tactic` in Graph/MazurArith was replaced.

## Per-file table (imports before → after; M. = Mathlib.)
| file | count | removed | added |
|---|---|---|---|
| `Graph/Bipartite` | 4 → 1 | M.Combinatorics.SimpleGraph.Basic,M.Combinatorics.SimpleGraph.Connectivity.Connected,M.Data.Fintype.Sum | — |
| `Graph/H1` | 12 → 3 | M.Data.Fintype.EquivFin,M.LinearAlgebra.Dimension.Constructions,M.LinearAlgebra.Dimension.RankNullity,M.LinearAlgebra.Dimension.StrongRankCondition,M.LinearAlgebra.Finsupp.LinearCombination,M.LinearAlgebra.Isomorphisms,M.LinearAlgebra.Prod,M.RingTheory.Finiteness.Finsupp,M.SetTheory.Cardinal.Finite | — |
| `Graph/Weighted` | 5 → 1 | M.LinearAlgebra.BilinearMap,M.LinearAlgebra.Dual.Defs,M.LinearAlgebra.Finsupp.SumProd,M.LinearAlgebra.Quotient.Basic | — |
| `Graph/BipCollapse` | 3 → 1 | Langlandscape.Graph.H1,M.Algebra.Exact.Basic | — |
| `Graph/Cyclic` | 8 → 3 | M.Algebra.BigOperators.Finsupp.Basic,M.Algebra.GCDMonoid.Finset,M.Data.Nat.Prime.Basic,M.RingTheory.PrincipalIdealDomain,M.Tactic.Ring | — |
| `Graph/Eisenstein` | 1 → 1 | — | — |
| `Graph/LevelRaising` | 4 → 1 | M.Algebra.BigOperators.Group.Finset.Basic,M.LinearAlgebra.Finsupp.LinearCombination,M.LinearAlgebra.Prod | — |
| `Graph/MazurArith` | 5 → 6 | M.Algebra.BigOperators.Field,M.Data.Nat.Prime.Basic,M.Data.Rat.Lemmas,M.Tactic | M.Algebra.BigOperators.Group.Finset.Piecewise,M.Data.Nat.Prime.Defs,M.Tactic.FieldSimp,M.Tactic.NormNum.GCD,M.Tactic.Ring |
| `Graph/TwoVertex` | 7 → 3 | M.Data.ZMod.Basic,M.LinearAlgebra.Isomorphisms,M.LinearAlgebra.Matrix.Nondegenerate,M.LinearAlgebra.Matrix.ToLin | — |
| `CommAlg/Gorenstein` | 7 → 5 | M.Algebra.Module.Torsion.Free,M.RingTheory.Localization.FractionRing | — |
| `CommAlg/LemmaS` | 1 → 1 | — | — |
| `CommAlg/NewOld` | 3 → 3 | — | — |
| `Local/GL2Levels` | 5 → 3 | M.LinearAlgebra.Matrix.Determinant.Basic,M.LinearAlgebra.Matrix.NonsingularInverse | — |
| `Local/UpCosets` | 5 → 2 | M.Algebra.Group.Pointwise.Set.Basic,M.GroupTheory.Index,M.Tactic.LinearCombination | — |
| `Tree/Local` | 9 → 1 | Langlandscape.Local.GL2Levels,M.Data.ZMod.Basic,M.GroupTheory.Index,M.NumberTheory.Padics.PadicNumbers,M.Tactic.FinCases,M.Tactic.Group,M.Tactic.Linarith,M.Tactic.LinearCombination | — |
| `Tree/Coset` | 6 → 3 | M.GroupTheory.Coset.Basic,M.GroupTheory.GroupAction.Quotient,M.GroupTheory.Subgroup.Center | — |
| `Hyp/BTtree` | 3 → 2 | M.SetTheory.Cardinal.Finite | — |
| `Hyp/LambdaJL` | 3 → 2 | M.Algebra.Algebra.Hom,M.RingTheory.Ideal.Quotient.Operations | M.RingTheory.Ideal.Maps |
| `LanglandscapeTests/S01/GL2Levels` | 1 → 1 | — | — |
| `LanglandscapeTests/S02/Coset` | 1 → 1 | — | — |
| `LanglandscapeTests/S02/Graph` | 7 → 3 | M.Algebra.Field.Rat,M.Data.Fin.VecNotation,M.Data.ZMod.Basic,M.Tactic.FinCases | — |
| `LanglandscapeTests/S03/LevelRaising` | 3 → 2 | M.LinearAlgebra.Matrix.Notation | — |
| `LanglandscapeTests/S03/MazurArith` | 1 → 4 | — | M.Algebra.BigOperators.Fin,M.Tactic.FinCases,M.Tactic.NormNum.Prime |
| `LanglandscapeTests/S03/TwoVertex` | 2 → 1 | M.GroupTheory.SpecificGroups.Cyclic.Subgroup | — |
| `LanglandscapeTests/S03/Weighted` | 1 → 1 | — | — |
| `LanglandscapeTests/S06/Gorenstein` | 1 → 1 | — | — |

Total: **108 → 56** imports over the 26 files.

## Files left unchanged
- Graph/Eisenstein, CommAlg/LemmaS, CommAlg/NewOld, S03/Weighted, S06/Gorenstein: they were already minimal.
- S01/GL2Levels, S02/Coset: `#min_imports` suggests nothing because these files contain only `example`s. Their single import is needed.
- All files that are not compilable here (GL2TF/AlgJL in their closure), Vendor/**, and the aggregators were not touched.
- **Dependent check for those files (static):** I compared the transitive import closure of every
  Langlandscape/LanglandscapeTests/Audit module, the aggregators included, on origin/main and on this branch, by parsing import lines through
  Mathlib, the Mathlib packages, AlgJL and Vendor sources. Every file outside the 26 has an **identical** closure (nothing
  lost and nothing gained), so its environment is unchanged and its build is unaffected. Only Graph/MazurArith, Hyp/LambdaJL and
  test S03/MazurArith have smaller closures, and all three are in the set and were rebuilt. Ribet/Mazur imports Graph/MazurArith
  but still gets everything through AlgJL.

## Full-subgraph rebuild (final state, dependency order, L-CHECK, all files with -o into a scratch dir)
All 26: **rc 0**, FROZEN-OK after every run. For every file, the warnings (with positions removed) are identical to the
baseline. Pre-existing warnings: Weighted 1, Cyclic 11, Eisenstein 4, MazurArith 2, TwoVertex 8, S03/LevelRaising 6,
S03/MazurArith 20. There are no errors.

## Axioms before/after
This is stronger than 1–2 headline declarations per file: for each of the 26 modules, a scratch file ran
`Lean.collectAxioms` on **every** non-internal constant defined in that module (569 constants). The output on origin/main
and on the final branch is **byte-identical** (only `propext`, `Classical.choice`, `Quot.sound` appear; no `sorryAx`).

## Build-time comparison (sum of per-file wall times for the 26 files, sequential, LEAN_NUM_THREADS=2)
| run | before (origin/main) | after |
|---|---|---|
| 0 | 54.77 s | 52.31 s |
| 1 | 54.53 s | 52.89 s |
| 2 | 55.47 s | 52.96 s |
Mean 54.9 s → 52.7 s (about −4%). These files are small, so wall time is dominated by loading imports. The clearest gain is in
memory: sum of max RSS ~61.7 GB → ~58.3 GB, and peak 3.2 GB → 2.6 GB. Graph/MazurArith dropped from 3.3 GB to 1.7 GB and from 5.9 s to 1.4–1.6 s,
because `import Mathlib.Tactic` is gone. The finer dependency graph should also allow more parallelism and fewer rebuilds under Lake (not measured).

## Node resources
free -m: total 15665 MB, available ~5.6–5.8 GB; swap 2047 MB, (nearly) fully used (by other processes) throughout;
uptime load average ~1.4–2.1. Peak RSS of any compile: 3.31 GB (baseline Graph/MazurArith; cap 3800M); after: 2.70 GB.
All compiles ran one at a time under the heavy lock with MemoryMax=3800M and MemorySwapMax=0. The frozen Mathlib tree was unchanged after every run.
Scratch dirs lls-lcheck/minimp and olean-minimp were deleted afterwards.
