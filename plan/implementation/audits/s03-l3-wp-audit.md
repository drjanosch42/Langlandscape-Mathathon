<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Blind WP audit — S03-L3 (`prop:s03-phi`, two-vertex weighted graphs)

- Auditor: blind WP audit (OVERVIEW §5.3), read-only; no Lean build run.
- Code: `lean/Langlandscape/Langlandscape/Graph/TwoVertex.lean`, `lean/Langlandscape/LanglandscapeTests/S03/TwoVertex.lean` at
  commit `f7faaee` (worktree `Langlandscape-wt/s03-l3`). The branch head is now `61a3ab1` ("fix int5 errors", 1+/3− in
  `TwoVertex.lean` only, merged into `s03-int`). It is covered in finding M1.
- Spec: `stage-03.md` §1 row S03-L3, §0.1 item 1, §0.2 items 3, 6; maths `prop:s03-phi`, `def:s03-graph` and facts (1)–(3)
  (`mathematics/chapters/s03/1-graphs.tex`); upstream S03-L1 `Graph/Weighted.lean` (`WGraph`, `X`, `deg0`, `wPairing`, `wDualMap`,
  `phiComb`); `agents/rules/lean.md`.

**Verdict: PASS WITH REMARKS** (0 critical, 1 major (already fixed on the branch head, needs a re-check), 6 minor).

## 1. Faithfulness to `prop:s03-phi`

| tex | Lean | hypotheses | match |
|---|---|---|---|
| `X(G) = ℤ[E]⁰` | `twoVertex_X_eq_deg0 : G.X = deg0 G.E ℤ` | `[Fintype E]`, `v₀ ≠ v₁`, `hsrc : ∀ e, src e = v₀`, `htgt : ∀ e, tgt e = v₁` | yes (see H1) |
| `Φ^comb = ℤ^E/(W·ℤ[E]⁰ + ℤ𝟏)` | `phiComb_twoVertex_equiv : G.PhiComb ≃ₗ[ℤ] (E → ℤ) ⧸ twoVertexRel G.w`, with `twoVertexRel w = (deg0).map (wMul w) ⊔ span{𝟏}` | `+ [DecidableEq E] [Nonempty E]` | yes |
| `|Φ^comb| = Σ_e ∏_{e'≠e} w_{e'}` | `card_phiComb_twoVertex : Nat.card G.PhiComb = ∑ e, ∏ e' ∈ univ.erase e, G.w e'` | same | yes |
| all `w_e = 1` ⇒ `Φ^comb ≅ ℤ/|E|` | `phiComb_twoVertex_unit : G.PhiComb ≃+ ZMod (Fintype.card G.E)` | `+ h1 : ∀ e, G.w e = 1` | yes |

Checked by hand:

- Presentation. `twoVertexRestr_surjective` (preimage `e ↦ ψ(𝟏_e − 𝟏_{e₀})`) and `twoVertexRestr_eq_zero_iff` (kernel `ℤ𝟏`) are the
  tex's "restriction is onto with kernel `ℤ𝟏`". `wDualMap_eq_restr` is "`x ↦ ⟨x,·⟩_w` is the class of `Wx`". `ker_twoVertexProj`
  assembles them. Correct.
- Order. The tex uses the Gram matrix `D + w_n uuᵀ` in the basis `e_i − e_n`. Lean instead uses the injective endomorphism
  `twoVertexMap y = W(y − (Σy)𝟏_{e₀}) + (Σy)𝟏` of `ℤ^E`. Its range is `W·ℤ[E]⁰ + ℤ𝟏` (`range_twoVertexMap`, both inclusions
  checked), and its matrix is `diag(w) + u𝟏ᵀ` with `u = 𝟏 − w_{e₀}𝟏_{e₀}` (`twoVertexMap_matrix_cast`; entry
  `w_eδ_{ej} − w_e[e=e₀] + 1`, correct). By the determinant lemma, `det = ∏w·(1 + Σ(1 − [i=e₀]w_i)/w_i) = ∏w·Σ1/w_i`
  (`twoVertex_det_identity`, correct). The index comes from `Submodule.natAbs_det_basis_change`, the submodule form of the
  specified `AddSubgroup.index_eq_natAbs_det`. This is a different but equivalent route to the specified one, and acceptable.
- Unit weights. `ker (Σ mod |E|) = ℤ[E]⁰ + ℤ𝟏` (`ker_sumZMod`, both directions correct: `Σy = c|E|` ⇒ `y = (y − c𝟏) + c𝟏`), and
  `sumZMod` is onto because `E ≠ ∅`.

Hypotheses beyond the tex:

- **H1 (orientation, `hsrc`/`htgt`).** The tex allows every edge to join the two vertices in either direction, and reduces to the
  `v₀ → v₁` case WLOG by fact (3). Lean assumes that orientation and does not formalize fact (3). This is a genuine restriction of
  the statement. It does not weaken any use in the plan: `collapse2`, `ofBip`-type graphs and the DR graph are oriented `0 → 1`
  by (C1), and the consumer S03-L6 (`Ribet/Mazur.lean`) discharges `hsrc`/`htgt` for `DRgraph d`. → minor m1.
- **Two vertices.** Lean does not require `V` to have exactly two elements, only `v₀ ≠ v₁` with every edge between them, so
  isolated extra vertices are allowed. This is a strengthening.
- **H2 (`Nonempty E`).** This is necessary, not a weakening. For `E = ∅`, `Φ^comb = 0` has order 1 while the empty sum is 0, and
  `ZMod 0 = ℤ`. The tex proof's parenthesis "for `E = ∅` all groups are 0 and the empty sum is 0" is therefore misleading: the
  order formula and the unit case are **false** for `E = ∅`. The Lean hypothesis is right and the tex should state `E ≠ ∅`.
  → minor m2 (a maths fix).
- `twoVertex_X_eq_deg0` correctly needs neither `Nonempty` nor `DecidableEq`.

## 2. Tests (`LanglandscapeTests/S03/TwoVertex.lean`)

Meaningful. `G222`/`G23` are honest `WGraph`s (`V = Bool`, edges `false → true`) that go through the main theorems, not through
internal helpers:

- `card_G222 : Nat.card G222.PhiComb = 12` and `card_G23 : … = 5` rewrite with `card_phiComb_twoVertex` and then evaluate
  `Σ∏` (2·2·3 = 12; 3 + 2 = 5, correct).
- `not_isAddCyclic_G222`: `6 • x = 0` for all `x` (by `six_nsmul_mem`, `6y = W(3y − (Σy)𝟏) + 2(Σy)𝟏`, verified, transported through
  `phiComb_twoVertex_equiv`), together with order 12, gives that no element has order 12. A real use of both the presentation and
  the cardinality.
- `X_G222` exercises `twoVertex_X_eq_deg0`.
- No `native_decide` (grep). Every test theorem has an `s03-phi` docstring.

Weak spots: the unit-weight `example` only typechecks `phiComb_twoVertex_unit` for one edge (`ℤ/1`) → m3. The tex's
`≅ ℤ/2 × ℤ/6` is not tested, only "order 12, not cyclic", which is what the spec asks for → m6.

## 3. Docstrings

All theorems in both files have an immediately preceding docstring with an `s03-` label (`s03-phi`, `s03-graph`), checked with a
script that mirrors `check_wp.sh` (3). Public defs (`wMul`, `twoVertexRel`, `cochainPairing`, `twoVertexRestr`, `twoVertexProj`,
`phiCombDeg0Equiv`, `twoVertexMap`, `sumZMod`, `phiCombCongr`, `phiComb_twoVertex_equiv`, `phiComb_twoVertex_unit`) are all
documented. The module docstring states the `[Nonempty E]` hypothesis. It does not state the orientation hypothesis as a
restriction (m1).

## 4. Compile risks (no build run)

- At `f7faaee`, `natCard_quot_range` ends with `congr 1; funext j; simp [bN]`. The final `congr 1` already closes the goal
  (`Subtype.val ∘ bN = f ∘ b` holds by `rfl`), so `funext` fails with "no goals". `Finset.mul_prod_erase _ _ (Finset.mem_univ e)`
  does not elaborate the function argument. Commit `61a3ab1` ("fix int5 errors") removes exactly these two points → M1.
- Tests: `decide` evaluates `∑ e : Fin 3, ∏ e' ∈ univ.erase e, 2` and the `![2,3]` analogue in the kernel. This is small and
  should reduce, but it depends on `Finset.erase`/`List.finRange` reducing in the kernel → m4.
- The Mathlib names used were checked in the frozen tree: `Matrix.vecMulVec_eq`, `det_one_add_replicateCol_mul_replicateRow`,
  `Submodule.natAbs_det_basis_change`, `Basis.det_comp`/`det_self`, `Matrix.mulVec_injective_of_det_ne_zero`,
  `LinearMap.toMatrix'_mulVec`, `Int.cast_det`, `Finsupp.univ_sum_single`, `ZMod.intCast_zmod_eq_zero_iff_dvd`,
  `orderOf_eq_card_of_forall_mem_zpowers` (additive form) with `Nat.card`.
- Names: no clash with any other s03 worktree (grep over `s03-*`). The rename to `twoVertex_mem_deg0_iff` avoided the clash with
  L2's `mem_deg0_iff`.

## 5. Findings

| # | class | finding | required fix |
|---|---|---|---|
| M1 | major | The audited commit `f7faaee` does not compile (two errors in `natCard_quot_range` and `twoVertex_det_identity`, §4). | Already done in `61a3ab1`. Accept `61a3ab1`, not `f7faaee`, after LCHK on it (its diff is only these two lines, so no re-audit is needed). |
| m1 | minor | The orientation hypothesis `hsrc`/`htgt` restricts the tex statement (fact (3) is not formalized). It is harmless for every planned use. | State it in the docstrings of the four main results ("edges oriented `v₀ → v₁`; orientation independence, fact (3), not formalized"). Optional later: an orientation-flip lemma. |
| m2 | minor (maths) | `prop:s03-phi`'s proof claims that the `E = ∅` case is consistent. It is not (`|0| = 1 ≠ 0 = Σ_∅`; `ℤ/0 = ℤ`). | In `1-graphs.tex`, add `E ≠ ∅` to the statement and fix the parenthesis. Route to S03-M1 / the stage master. The Lean code is unaffected. |
| m3 | minor | The unit-weight test is trivial (`E = Unit`, `ℤ/1`). | Add a test with `|E| = 3`, unit weights: `Nat.card = 3` via `card_phiComb_twoVertex`, or `IsAddCyclic` via `phiComb_twoVertex_unit`. |
| m4 | minor | `decide` on `Finset` sums and products over `Fin n` in `card_G222`/`card_G23` is a kernel-reduction risk. | If LCHK fails there, use `simp [Finset.sum_erase…]` / `rfl`, or `norm_num [Fin.sum_univ_three, Fin.prod_univ_two]` after `Finset.prod_erase`. |
| m5 | minor | Generic linear-algebra helpers sit in `Langlandscape.Graph` under general names (`natCard_quot_range`, `det_diagonal_add_vecMulVec`, `cochainPairing`, `wMul`, `sumZMod`). There is no clash today. | At L12, consider prefixing them (`twoVertex…`) or making them `private`/`protected`. |
| m6 | minor | The tex's `w = (2,2,2) ⇒ ℤ/2 × ℤ/6` is not formalized, only "order 12, not cyclic". | Say so in the test docstring (status of the `ℤ/2 × ℤ/6` claim: *proved* in tex only). |

The statements are faithful to `prop:s03-phi`: `X = deg⁰`, the quotient presentation, the cardinality `Σ_e ∏_{e'≠e} w_{e'}` and the
unit-weight `ℤ/|E|`. The only restriction is the fixed orientation (m1). `Nonempty E` is required by the mathematics.
