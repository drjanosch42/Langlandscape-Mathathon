<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Blind WP audit — S03-L2 (`lem:s03-bip`, bipartite collapse, any `CommRing R`)

- Auditor: blind WP audit (OVERVIEW §5.3), read-only; no Lean build run.
- Code: `lean/Langlandscape/Langlandscape/Graph/BipCollapse.lean` at commit `c404b12` (worktree `Langlandscape-wt/s03-l2`;
  byte-identical to the copy in `s03-int`).
- Spec: `stage-03.md` §1 row S03-L2, §0.2 items 3, 4, 6, 7; maths `lem:s03-bip` (`mathematics/chapters/s03/3-ribet.tex`);
  upstream S03-L1 `Graph/Weighted.lean` (`deg0`, `collapse2`, `boundary_ofBip`) and stage-02 `Graph/H1.lean`
  (`boundary`, `H1`, `aug`, `range_boundary_of_connected`, `finrank_H1_of_connected`), `Graph/Bipartite.lean`; `agents/rules/lean.md`.

**Verdict: PASS WITH REMARKS** (0 critical, 0 major, 5 minor).

## 1. Faithfulness to `lem:s03-bip`

| tex | Lean | hypotheses | match |
|---|---|---|---|
| (a) `ker ∂ ⊆ R[E]⁰` | `bip_ker_le_deg0 : H1 G R ≤ deg0 G.E R` | none (no connectivity) | yes; stronger than the tex, which assumes connected throughout |
| (a) `∂ : R[E]⁰ ↠ R[V₀]⁰ ⊕ R[V₁]⁰` | `bip_surj_deg0 : (deg0 G.E R).map (boundary G R) = deg0Prod G R` | `[Finite V₀] [Finite V₁]`, `G.Connected` | yes (equality of submodules = into + onto) |
| (a) exact `0 → H₁ → R[E]⁰ → R[V₀]⁰⊕R[V₁]⁰ → 0` | `bip_exact`: `Injective H1toDeg0 ∧ Exact H1toDeg0 boundaryDeg0 ∧ Surjective boundaryDeg0` | same | yes, any `CommRing R` (A2) |
| (a) `rk H₁ = |E|−|V₀|−|V₁|+1` over ℤ | `bip_rank` (ℤ), `bip_rank_of_isDomain` (any domain, incl. ℚ) | `+ [Finite E]` | yes; the domain version matches the tex's last paragraph |
| (b) `ker ∂^∨ = {(c𝟏, c𝟏)}` for every abelian `A` | `bip_ker_dual A hc f : boundaryDual G A f = 0 ↔ ∃ c, f = (fun _ => c, fun _ => c)` | `G.Connected`; no finiteness | yes, any `AddCommGroup A` |
| (c) connecting map of `0 → K_• → C_•(G) → C_•(G^{(2)}) → 0` is `∂|_{R[E]⁰}` | `collapseDelta := SnakeLemma.δ' …`, `bip_collapse_connecting : δ y = ∂ y` | none | yes |
| (c) `H₁(G^{(2)}) = R[E]⁰`, `H₁(G) → H₁(G^{(2)}) →δ K₀` exact | `H1_collapse2`, `ker_collapseBoundary`, `bip_collapse_exact` | none | yes |

Checked by hand:

- Sign (C1): `boundary` is stage 02's `(−s₀*, s₁*)`; the degree lemmas `degMap_boundary_fst = −deg`, `degMap_boundary_snd = deg` are
  correct for `boundary_single = (−[s₀e], [s₁e])`. The proof of `bip_ker_le_deg0` uses the second component, as in the tex.
- `boundaryDual f e = f.2 (s₁ e) − f.1 (s₀ e)`, which is the tex's `s₁^*f₁ − s₀^*f₀`. The proof (constancy along
  `Relation.ReflTransGen` of `toSimpleGraph.Adj`, then `Connected.preconnected`) is the tex proof.
- Snake diagram for (c), against the frozen `Mathlib/Algebra/Module/SnakeLemma.lean` signature
  (`i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁`): top row `⊥ → R[E] →id R[E]` (`K₁ = 0`, `π₁` is the identity of
  `R[E]`); bottom row `K₀ ↪ R[V₀]×R[V₁] →collapseVert R[Bool]`; verticals `0`, `∂_G`, `∂_{G^{(2)}} = collapseBoundary`;
  `ι₃ = ker(collapseBoundary).subtype`; `π₁ = id_{K₀}` (coker of `0 : K₁ → K₀`). All arguments are in the right slots. The
  commuting squares (`collapse_comm_left/right`) and row exactness (`collapse_exact_top/bot`) are the right ones. `collapseVert`
  `(a,b) ↦ deg a·[0] + deg b·[1]` is the vertex map of the collapse `π`. `δ'_eq` is applied with lift `y` (the same chain) and
  `z = ∂y`, exactly as in the tex computation.
- `G^{(2)}` is modelled by `collapseBoundary : R[E] → R[Bool]` and linked to L1's `WGraph.boundary (collapse2 G) R` by
  `collapseBoundary_eq`. `C₀(G)` is `R[V₀] × R[V₁]` (stage 02), which is `R[V₀ ⊕ V₁]` of `ofBip` by L1's `boundary_ofBip`. Acceptable.

Hypotheses beyond the tex: none. The tex's `E ≠ ∅` in (c) is not needed for `δ = ∂|` or for exactness at `H₁(G^{(2)})`, and Lean
drops it, which is a strengthening. `Finite` instances replace the tex's "finite". Consumers (`Ribet/Sequence.lean` in s03-l6/l8/l9/int)
use `bip_exact hc`, `bip_rank hc`, `bip_ker_dual A hc f` as stated.

## 2. Docstrings

All 32 `theorem`s have an immediately preceding docstring containing `s03-bip` (checked with a script that mirrors `check_wp.sh`
item (3)). No `sorry`/`admit`/`axiom`/`native_decide`. Public defs (`degMap`, `deg0Prod`, `H1toDeg0`, `boundaryDeg0`, `boundaryDual`,
`collapseBoundary`, `collapseVert`, `collapseDelta`, `H1toCollapse`) are all documented, and the main theorems name their tex part
((a)/(b)/(c)).

## 3. Compile risks (no build run)

Low. Lemma names used were checked in the frozen Mathlib (`SnakeLemma.δ'`, `δ'_eq`, `LinearMap.exact_subtype_ker_map`,
`Submodule.injective_subtype`, `Finsupp.induction_linear` with cases `zero/add/single`, `SimpleGraph.reachable_iff_reflTransGen`,
`Mathlib/Algebra/Exact/Basic.lean`). Points that depend on elaboration:
`rcases` through `SimpleGraph.fromRel` adjacency in `bip_ker_dual` (the same pattern is used in stage-02 `H1.lean`, which is green);
`omega` with `ℕ → ℤ` casts in `bip_rank_of_isDomain` (supported). The commit message says it fixes the int3-1 errors, but I
saw no recorded green build of `c404b12`. LCHK decides.

## 4. Findings

| # | class | finding | required fix |
|---|---|---|---|
| m1 | minor | The tex's (c) conclusion, "the sequence in (a) *is* the long exact sequence", also includes `δ` onto (`H₀(K) → H₀(G)` is 0). Lean has `δ = ∂|`, exactness at `H₁(G^{(2)})` and the injectivity, but `δ` onto is only implicit (via `bip_exact`). | Add `bip_collapse_delta_surjective (hc : G.Connected) : Function.Surjective (collapseDelta G R)`, a one-liner from `bip_exact` and `bip_collapse_connecting`, or say in the `bip_collapse_exact` docstring that surjectivity is `bip_exact`.2.2. |
| m2 | minor | `boundaryDual` is defined by its formula. Nothing proves it is the transpose of `boundary` (tex: `∂^∨`), or that it agrees with stage-02 `Tree.deltaCoh` on the Brandt graph. The tex defines `∂^∨` by the same formula, so this is not a faithfulness gap. | Add one sentence to the docstring ("transpose of `boundary` under `Σ_e f(e) y_e`; not proved here"), or add the pairing lemma. The cross-check with `deltaCoh` belongs to S03-L9/L12. |
| m3 | minor | General helpers live in this file under generic names: `degMap`, `degMap_single`, `mem_deg0_iff`, `aug_apply`, `mem_H1_iff`. S03-L3 restates the same fact as `twoVertex_mem_deg0_iff`. No name clash in any s03 worktree today (grep). | At the L12 cleanup, move `degMap`/`mem_deg0_iff` to `Weighted.lean` (next to `deg0`) and let L3 reuse them. |
| m4 | minor | `H1_collapse2` and `ker_collapseBoundary` repeat the same proof. | Derive one from the other via `collapseBoundary_eq` (cosmetic). |
| m5 | minor | Module docstring line 23 is 139 characters (> 100). This file has an SPDX header and the other `Graph/` files from L1, L3 and stage 02 do not. Neither is required by `lean.md`. | Wrap the line. Make SPDX consistent across `Graph/` at the stage merge. |

No critical or major findings. The statements are faithful to `lem:s03-bip` (a)–(c) over any `CommRing R`, with the rank over ℤ
and over any domain, and (b) for every `AddCommGroup A`.
