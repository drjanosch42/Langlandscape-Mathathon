---
id: 20261114-215345Z_abhijit_d2-statement
from: abhijit/d1-s05-lean
to: fabian/global_master
type: info
re: 20261114-213920Z_fabian_batch5
priority: normal
---
D2 (S05-L8, algebraic half) statement. Branch `abhijit/s05-l8` @ 986b640, stacked on `abhijit/s05-l6` @ 68cd096 (L6 got one
docstring-only commit after the d1-statements info: `T` local *is* used, for `Nontrivial T`; statements unchanged). New file only
`lean/Langlandscape/Langlandscape/Comparison/XIso.lean`, namespace `Langlandscape.Comparison`, single import
`Langlandscape.CommAlg.SubQuot` (gate grep empty). Proof already in the commit (no sorry); report follows. No `Hyp.X.iso` line (yours).
Same convention as D1: Mathlib-style header; non-`module` file, since a `module` cannot import the non-module CommAlg files.

Section variables: `{A T : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing T] [Algebra A T]`.
```lean
/-- `prop:s05-Xiso` (`s05-Xiso`), algebraic half of `def:s05-Xiso`: let `A` be a Noetherian local
domain, `T` a local `A`-algebra which is `A`-Gorenstein with trace `ℓ` (in particular finite free),
`𝔞 𝔟` ideals as in `prop:s05-subquot` (`T/𝔞`, `T/𝔟` torsion-free, `𝔞 ⊓ 𝔟 = ⊥`, splitting over
`Frac A`), and `T' = T/𝔞` `A`-Gorenstein. If `H` is free of rank one over `T`, then
`H[𝔞] ≃ₗ[T] T'` (non-canonically: the iso depends on a basis of `H`). -/
theorem xiso_of_gorenstein [IsLocalRing T] {𝔞 𝔟 : Ideal T} {ℓ : Module.Dual A T}
    (hℓ : IsGorensteinWith A T ℓ)
    (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞)) (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟))
    (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hT' : IsGorenstein A (T ⧸ 𝔞))
    {H : Type*} [AddCommGroup H] [Module T H] [Module.Free T H] [Module.Finite T H]
    (hrank : Module.finrank T H = 1) :
    Nonempty (torsionBySet T H 𝔞 ≃ₗ[T] T ⧸ 𝔞) := …
```
Hypotheses: (i) of `prop:s05-Xiso` = `hℓ` (T Gorenstein; it also supplies `Module.Free A T`, `Module.Finite A T`) + `hrank` (H free of rank
one); (ii) = `htf_a htf_b hinf hsplit` (as in `subquot_kernel`); (iii) only its consequence "T' Gorenstein" = `hT'`.
Proof: `subquot_kernel` (r = 1) gives `H[𝔞] ≃ₗ[T] (Fin 1 → 𝔟)`, `LinearEquiv.funUnique` gives `𝔟`; then the public
`bEquivQuotOfGorenstein (D : NewOldData A T) (hℓ) (hℓ' : IsGorensteinWith A (T ⧸ D.𝔞) ℓ') : D.𝔟 ≃ₗ[T] T ⧸ D.𝔞`, built from
`NewOldData.bEquivDualQuot` (A-linear) and the inverse of `mulDual ℓ'`; its `T`-linearity is `bEquivDualQuot_smul` + the helper
`mulDual_symm_comp_mulLeft`. Characterisation `bEquivQuotOfGorenstein_spec : ℓ' (φ β * mk s) = ℓ (β * s)`.
Edge cases: 𝔞 = ⊥ ⇒ 𝔟 = ⊤, statement is `H ≃ T`; 𝔟 = ⊥ ⇒ 𝔞 = ⊤, T' = 0, `H[⊤] = 0`; both covered without a case split. Rank is fixed
to one (as in the row).
