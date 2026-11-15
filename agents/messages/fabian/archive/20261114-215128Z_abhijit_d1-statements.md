---
id: 20261114-215128Z_abhijit_d1-statements
from: abhijit/d1-s05-lean
to: fabian/global_master
type: info
re: 20261114-213920Z_fabian_batch5
priority: normal
---
D1 (S05-L6) statements. Branch `abhijit/s05-l6` @ 242f020 (on 0e24ba5; contains s06-l3, no merge needed). File only
`lean/Langlandscape/Langlandscape/CommAlg/SubQuot.lean`, namespace `Langlandscape.CommAlg`. Proofs are already in this commit
(no sorry); the full report follows after the self-audit. L-CHECK rc 0, frozen-tree find empty, axioms standard.

**Convention (Abhijit, binding for SubQuot/XIso):** Mathlib-style header (`Copyright (c) 2026 Fabian Januszewski, Abhijit A J ...
Released under Apache 2.0 ... Authors: ...`). The `module` / `public import` form was tried and fails:
`error: cannot import non-\`module\` Langlandscape.CommAlg.NewOld from \`module\`` (Gorenstein/NewOld are not module files; not
ours to edit). So the file is a non-module file with the new header. Imports minimised: only `import Langlandscape.CommAlg.NewOld`
(all used Mathlib API is transitive; each Mathlib import was tested redundant). Gate grep empty.

Hypothesis shape: `A` Noetherian local domain, `T` local (seam shape; unused in the proofs), finite free over `A`; the splitting is
taken in the field form of `NewOldData.split_iff` and turned into a `NewOldData` by `subquotData` (via `split_iff`, no own lemma);
`ann 𝔞 = 𝔟` comes from `NewOldData.ann_a`. `H[𝔞]` := `Submodule.torsionBySet T H 𝔞`, `𝔞H` := `𝔞 • ⊤`. Rank `r` := `Module.finrank T H = r`
with `[Module.Free T H] [Module.Finite T H]`; `𝔟^r` := `Fin r → 𝔟`. Reduction to coordinates via `Module.finBasisOfFinrankEq`.

Section variables of the headline section:
```lean
variable {A T : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Free A T] [Module.Finite A T]
  {𝔞 𝔟 : Ideal T}
  {H : Type*} [AddCommGroup H] [Module T H] [Module.Free T H] [Module.Finite T H] {r : ℕ}
```
Headline declarations (verbatim, docstrings included):
```lean
/-- `prop:s05-subquot` (`s05-subquot`): the `NewOldData A T` of the subquot setting, built from the
splitting `T_K = (T/𝔞)_K × (T/𝔟)_K` (in the form `(𝔞 ⊔ 𝔟) K⊗T = ⊤`) by stage 06's
`NewOldData.split_iff` (`if:s06-lemD`). -/
def subquotData (𝔞 𝔟 : Ideal T) (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤) :
    NewOldData A T where …

/-- `prop:s05-subquot` (`s05-subquot`), kernel: for `H` free of rank `r` over `T`,
`H[𝔞] = 𝔟 • H` and `H[𝔞] ≃ₗ[T] 𝔟^r`. Uses `NewOldData.ann_a` (`if:s06-lemD`(a)) on
`subquotData`. For `r = 0` both sides are `0`. -/
theorem subquot_kernel (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    torsionBySet T H 𝔞 = 𝔟 • (⊤ : Submodule T H) ∧
      Nonempty (torsionBySet T H 𝔞 ≃ₗ[T] (Fin r → 𝔟)) := …

/-- `prop:s05-subquot` (`s05-subquot`), quotient: for `H` free of rank `r` over `T`,
`H/𝔞H ≃ₗ[T] (T/𝔞)^r`. Needs only that `H` is free of rank `r`. -/
theorem subquot_quot (𝔞 : Ideal T) (hr : Module.finrank T H = r) :
    Nonempty ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ≃ₗ[T] (Fin r → T ⧸ 𝔞)) := …

/-- `prop:s05-subquot` (`s05-subquot`), injectivity: for `H` free of finite rank over `T`, the
natural map `H[𝔞] → H/𝔞H` is injective (its kernel is `𝔟H ∩ 𝔞H = (𝔞 ⊓ 𝔟)H = 0`). -/
theorem subquot_injective (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤) :
    Function.Injective (subquotMap 𝔞 H) := …

/-- `prop:s05-subquot` (`s05-subquot`), cokernel: for `H` free of rank `r` over `T`, the cokernel
of `H[𝔞] → H/𝔞H` is `≃ₗ[T] (T/(𝔞 ⊔ 𝔟))^r`. For `r = 0` it is `0`. -/
theorem subquot_coker (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    Nonempty (((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) ≃ₗ[T]
      (Fin r → T ⧸ (𝔞 ⊔ 𝔟))) := …

/-- `prop:s05-subquot` (`s05-subquot`): the cokernel of `H[𝔞] → H/𝔞H` is killed by every
`t ∈ 𝔞 ⊔ 𝔟`, in particular by the image of the `c ≠ 0` of `NewOldData.split`. -/
theorem subquot_coker_smul_eq_zero (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    {t : T} (ht : t ∈ 𝔞 ⊔ 𝔟)
    (x : (H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) : t • x = 0 := …

/-- `prop:s05-subquot` (`s05-subquot`), edge case `𝔞 ⊔ 𝔟 = ⊤` (e.g. `A` a field): the cokernel of
`H[𝔞] → H/𝔞H` is `0`. -/
theorem subquot_coker_subsingleton (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (htop : 𝔞 ⊔ 𝔟 = ⊤) :
    Subsingleton ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) := …
```
Also public: `subquotMap 𝔞 H : torsionBySet T H 𝔞 →ₗ[T] H ⧸ 𝔞 • ⊤` (= mkQ ∘ subtype) with `subquotMap_apply`; general forms (any `CommRing T`,
basis `b : Module.Basis (Fin r) T H`, hypothesis `hann : ann 𝔞 = 𝔟`): `mem_smul_top_iff_basis`, `mem_torsionBySet_iff_basis`,
`torsionBySet_eq_smul_top`, `torsionBySetEquiv`, `quotSmulTopEquiv`, `subquotMap_injective` (+ `hinf`), `cokerMap`, `ker_cokerMap`,
`cokerEquiv`; edge-case lemmas on any `D : NewOldData A S`: `subquot_b_eq_top_of_a_eq_bot` (`D.𝔞 = ⊥ → D.𝔟 = ⊤`),
`subquot_a_eq_top_of_b_eq_bot`.

Edge cases: r = 0 — all statements hold uniformly (`Fin 0 → _` trivial), no case split; 𝔞 = ⊥ / 𝔟 = ⊥ — allowed by `NewOldData`, force
the other ideal to be ⊤ (lemmas above); 𝔞 + 𝔟 = ⊤ — cokernel 0 (`subquot_coker_subsingleton`). Deviation: `subquot_kernel` bundles the
equality and the iso as a conjunction (the row writes "H[𝔞] = 𝔟 • H ≃ 𝔟^r"); isos are `Nonempty` (non-canonical, basis-dependent), the
explicit equivs are the general-form defs. Next: D2 (`Comparison/XIso.lean`, statement info to follow).
