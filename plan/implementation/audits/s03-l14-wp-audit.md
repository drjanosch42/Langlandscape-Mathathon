<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Blind WP audit — S03-L14 (coefficient two-term complex)

- Auditor: blind WP audit (OVERVIEW §5.3), read-only; no Lean build run.
- Code: `lean/Langlandscape/Langlandscape/Ribet/Coeff.lean`, `lean/Langlandscape/LanglandscapeTests/S03/Coeff.lean`
  at commit `53026f8` (worktree `Langlandscape-wt/s03-l14`).
- Spec: `stage-03.md` §1 row S03-L14, risk (9) §7; maths `def:s02-Mhom`(iii),(iv) (`s02/3-cohomology.tex`),
  (C1), (C3) of `ss:s03-conv` and `thm:s03-iharaH0` (`s03/4-ihara.tex`), `thm:s03-ribet`(b) (`s03/3-ribet.tex`);
  `agents/rules/lean.md`.

**Verdict: PASS WITH REMARKS** (0 critical, 0 major, 5 minor).

## 1. Faithfulness of the maps

The convention of `brandtModule` (Brandt/Module.lean:31) is `f(γ x u) = (ρ u)⁻¹ f(x)`: left `B^×`-invariant, right `U`-action,
with the inverse. All maps checked by hand against `def:s02-Mhom`(iii),(iv) and (C3):

| Lean | Lean formula | maths | match |
|---|---|---|---|
| `s0PullV` (= `restrictV`) | `f ↦ f` | `(s_0^*f)(y) = f(y)` | yes |
| `s1PullV` | `f ↦ f(· α)` | `(s_1^*f)(y) = f(yα)` | yes |
| `s0TrV` (= `traceV U' U`) | `x ↦ Σ_{c∈U/U'} ρ(c.out) f(x·c.out)` | `(tr_0 f)(x) = Σ_{u∈U/U'} u_p f(xu)` | yes (`ρ(u)` = `u_p`) |
| `s1TrV` (= `traceV (α⁻¹U'α) U ∘ transV`) | `x ↦ Σ_{c∈U/α⁻¹U'α} ρ(c.out) f(x·c.out·α⁻¹)` | `(tr_1 f)(x) = Σ_{u∈U/U'_α} u_p f(xuα⁻¹)` | yes |
| `alphaV` | `(−s0TrV, s1TrV)` | (C1) `α = (−s_{0*}, s_{1*})` | yes |
| `alphaVee` | `(f₀,f₁) ↦ s1PullV f₁ − s0PullV f₀` | (C1) `α^∨(f₀,f₁) = s_1^*f₁ − s_0^*f₀` | yes |

Side/inverse check. Changing a representative `u ↦ uv`, `v ∈ U'`, gives `ρ(u)ρ(v)ρ(v)⁻¹f(xu)`, so the sum does not depend on the
representatives. This is the `hτ` step of `traceVRaw_mul_right`. Equivariance: `(tr f)(xw) = Σ ρ(u) f(xwu) = ρ(w)⁻¹ Σ ρ(u') f(xu')` after
reindexing `u' = wu`. This is `coset_finsum_translate` plus `(ρ w).injective`. The sign `(ρ w)⁻¹` is the one `brandtModule` needs.
`s1PullV`: `f(xuα) = f(xα·α⁻¹uα) = ρ(α⁻¹uα)⁻¹ f(xα)`, which equals `ρ(u)⁻¹ f(xα)` by `hα`. This is what the code does.
`transV`: the symmetric step with `αvα⁻¹ ∈ U'`, using `hα` at `u = αvα⁻¹`. Correct.

(C3) writes the traces without the factor `u_p` because it takes representatives with `u_p = 1`. The Lean form with `ρ(c.out)`
and arbitrary `Quotient.out` representatives is the representative-free version of `def:s02-Mhom`(iv), and it agrees with (C3) on such
representatives. Faithful.

`s0TrV_comp_s0PullV` (`= [U:U'] • id`) is correct: each term is `ρ(u)ρ(u)⁻¹ f(x) = f(x)`.

## 2. `CoeffData.hα`

`hα : ∀ u : U, ↑u ∈ U0q U → ∀ h : α⁻¹uα ∈ U, ρ⟨α⁻¹uα, h⟩ = ρ u`. This is exactly the condition used, and used only, in
`s1PullV` (at `u ∈ U'`) and `transV` (at `αvα⁻¹ ∈ U'`). It is neither too weak nor stronger than needed. Binding the membership
proof `h` (instead of requiring `IsQLevel`) is harmless: for a `q`-level, `h` always exists (`alphaElt_inv_conj_mem`).

- *Non-vacuity:* `CoeffData.triv` (`hα := rfl`) proves the structure is inhabited for every `d, q, U, R`. The tests use it.
- *True when ρ factors through the p-component, p ≠ q:* the condition is mathematically correct, since `α` is supported at `q`.
  It is plainly satisfiable in Lean (via `localComponent_localEmbedGL_of_ne`, Brandt/Corollaries.lean:557, or for any
  `ρ = χ ∘ Nrd`). But it is **only claimed in docstrings, not formalized**, and no non-trivial instance exists (finding m1).

## 3. `alphaV_triv` / `alphaVee_triv`: genuine, not rigged

- `brandtModuleTrivEquiv` is the stage-01 equivalence (Brandt/Module.lean:133, `f ↦ (c ↦ f(c.out))`). This WP does not redefine it.
- `trivEquivU0q` is `LinearEquiv.ofEq` (the identity on values, along `ρ' = 1`, `triv_ρ'`) followed by the stage-01 equivalence.
  It is not an ad-hoc equivalence built so that the theorem holds.
- The right-hand sides are stage 02's `s0Tr`/`s1Tr` (built from `Brandt.trace` and `translateLin`, Tree/TwoTerm.lean) and
  `deltaCoh` (`s1Pull ∘ snd − s0Pull ∘ fst`). The proofs go through the independent evaluation lemmas `s0Tr_apply_mk`,
  `s1Tr_apply_mk`, `s0_mk`, `s1_mk` and the representative lemma `brandtModuleTrivEquiv_apply_mk`, which is proved from
  `DoubleCoset.mk_out_eq_mul` and the Brandt invariance. So the bridge is a real statement: the coefficient sums with `ρ = 1` agree
  with stage 02's `ZXdual` sums over classes.
- The sign in `alphaV_triv` (`−s0Tr`) matches (C1) and `partialHom`'s transpose. `alphaVee_triv` matches `deltaCoh` exactly.

## 4. Docstrings

- Every `theorem` in both files has an immediately preceding docstring with an `s0N-` label (checked mechanically). Every
  theorem in `Coeff.lean` carries `thm:s03-ribet` or `s03-conv`. Every public `def`/`structure`/`abbrev` is documented, and so
  are the `CoeffData` fields. Labels resolve: `thm:s03-ribet` (s03/3-ribet.tex:86), `ss:s03-conv`, `thm:s03-iharaH0`,
  `def:s01-brandt`, `def:s02-Mhom`. The tex pointer in `thm:s03-ribet` ("coefficient layer for (b): Ribet.CoeffData,
  Ribet.alphaV (S03-L14)") is consistent.
- The test `instance fact_prime_seven` has a docstring without a label. Instances are outside the rule (nit, m4).
- No `sorry`/`admit`/`axiom`.

## 5. Compile risks (read, not built)

All referenced names exist in the frozen Mathlib / project: `DoubleCoset.out_eq'`, `DoubleCoset.mk_out_eq_mul`,
`AddEquivClass.map_finsum` (to_additive of `MulEquivClass.map_finprod`), `LinearEquiv.coe_inv`, `LinearEquiv.mul_apply`,
`LinearEquiv.map_smul`, `Nat.cast_smul_eq_nsmul`, `Subgroup.index_eq_card`, `Fintype.card_eq_nat_card`, `Subgroup.coe_mul`,
`Nat.prime_seven`, `GL2TF.HeckeModule.coset_finsum_translate`, `finite_quotient_of_relIndex`, `relIndex_U0q(_ne_zero)`,
`relIndex_s1Level_ne_zero`, `s1Level_le`, `alphaElt_inv_conj_mem`, `conj_mem_of_mem_rightConj`, `isQLevel_Ohat`.
There are no build artefacts for these modules in the WP worktree, so the LCHK result is the gate. Spots to watch are listed in m3.

## Findings

| id | sev | finding | required fix |
|---|---|---|---|
| m1 | minor (prerequisite for L11) | The claim "`hα` holds when `ρ` factors through the `p`-component, `p ≠ q`" (docstrings of `CoeffData`, module header, spec row) is not formalized, and no `CoeffData` with non-trivial `ρ` exists. The `ℤ_[p]` "shape test" also uses the trivial action, so `hα` is exercised only by `rfl`. | Add `CoeffData.ofLocal` (given `p ≠ q`, `ρp : GL₂(ℤ_p)-image →* (V ≃ₗ V)`, set `ρ := ρp ∘ localComponent p`, with `hα` from `map_mul`/`map_inv` and `localComponent_localEmbedGL_of_ne`), or at least a test instance `ρ = χ ∘ Nrd`. Do this before L11 consumes `alphaV` with a `U_p`-module `V`. |
| m2 | minor (downstream) | `CoeffData` allows any `ρ : U →* Aut V`. `thm:s03-iharaH0` and (C6) need `V` to be a `U_p`-module (the action factors through `u ↦ u_p`) for `[τ(x)]` and `ε`. Not this WP's scope, but L11 cannot use `CoeffData` alone. | Record it in the L11 brief: L11 adds a factorisation hypothesis or field, or uses the m1 constructor. |
| m3 | minor (compile risk) | (a) In `s0TrV_triv`/`s1TrV_triv`/`alphaVee_triv`, `rw [brandtModuleTrivEquiv_apply_mk]` must unify an argument of type `brandtModule U R R (CoeffData.triv …).ρ` with one of type `brandtModule U R R 1`. That needs `CoeffData.triv` to unfold, which may fail at `rw`'s transparency. (b) In `s0TrV_comp_s0PullV` the final `rfl` relies on `rw` leaving the `index` = `relIndex` goal open. That is expected, since `relIndex` is not reducible. | If LCHK fails there: mark `CoeffData.triv` `@[reducible]` (or `abbrev`), or add `CoeffData.triv_ρ : (triv …).ρ = 1 := rfl` and route through `LinearEquiv.ofEq` as for `ρ'`. No action if LCHK is green. |
| m4 | minor (nit) | The test `instance fact_prime_seven` docstring has no label. | Optional: add `(test data, s03-ribet)`. |
| m5 | minor (process) | The module is not yet imported from `Langlandscape.lean` / `LanglandscapeTests.lean`. Per the rules this is the stage master's job. | The stage master registers both files at the int1 merge. |

Spec conformance (row S03-L14): all named defs and lemmas are present, with well-definedness and linearity inside the defs. The tests
are as specified: the trivial instance, `alphaV_triv`/`alphaVee_triv` on `B₂`, `q = 7`, `U = Ô^×`, the `ℤ_[p]` shape test, and
additionally `s0TrV ∘ s0PullV = (q+1) • id`.
