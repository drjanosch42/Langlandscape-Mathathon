/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.HypX
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Hypothesis `Hyp.X.gal`: the Galois clause (X4) of `Hyp.X` (S05-L3)

`mathematics/chapters/s05/hypX.tex`, `hyp:s05-X` (X4) (`s05-X`), `rem:s05-hypX-lean` (`s05-hypX-lean`),
`rem:s05-Xstatus` (`s05-Xstatus`, row 1 of the Frobenius table); stage tex
`plan/staged/stage-05-comparison-hypothesis.tex`, `hyp:s05-X`.

* `TateModuleData M q p` : an abstract stand-in for the family `T_pJ_s` (`s ≥ 0`) with its `G_{ℚ_q}`- and
  `ℋ_s`-structure: free f.g. `ℤ_[p]`-modules `T s`, an arithmetic Frobenius `frob s`, a tame generator `tau s` with
  `frob τ frob⁻¹ = τ ^ q`, a `HeckeSym`-action commuting with `frob` and `tau`, the filtration `Tt s ≤ TI s ≤ ⊤`
  (`T_t ⊆ T^{I_q} ⊆ T_pJ_s`, `thm:s05-G`(v)) and the monodromy operator `N s`.
* `Hyp.X.gal G φ T` : (X4) for all `s`, for a character-group datum `G` (S05-L2) and **a given family**
  `φ s : G.X s ≃ₗ[ℤ] degZero (S s) ℤ` (it presupposes the `φ_s`, `rem:s05-hypX-lean`).

**Toy model, decided.** Stage 04 dropped Weil vendoring (`stage-04.md`, "Dropped vs. coarse: Weil vendoring"): there is
no `ContinuousZlModule` and no Galois group here. `G_{ℚ_q}` enters only through the two operators `frob` (arithmetic
Frobenius) and `tau` (a topological generator of tame inertia), with the one tame relation. The Tate twist
`ℤ_p(1)` of the bottom piece is not a separate module: it is recorded only by the factor `q` in the Frobenius clause.

The claim "`T` *is* `T_pJ_s` with its Galois and Hecke action" stays outside Lean (hypothesis registry), like the claim
"`G` is the character group of `J_s`" for `Hyp.X.char`.

Status: *hypothesis* (`\sthyp`), never an axiom; registered in `HYPOTHESES.md`. Non-vacuity: an unconditional toy instance for all
`s` (direct-sum model, middle piece `0`): `LanglandscapeTests.Hyp.S05.toyTate_gal_uncond` (S05-L4, discharged by
S05-L4g `Comparison/ThetaAdj.lean`), parametric in the context `(d, …, Pq, hPq)`.
-/

set_option autoImplicit false

open TensorProduct

namespace Langlandscape.Hyp.X

open Langlandscape.Brandt Langlandscape.Comparison

/-- `hyp:s05-X` (X4) (`s05-X`), data part: an abstract Tate-module datum standing for `T_pJ_s`, `s ≥ 0`
(toy model, decided: no `ContinuousZlModule`, `G_{ℚ_q}` only through `frob` and `tau`).
Per `s`: a free f.g. `ℤ_[p]`-module `T s`; the arithmetic Frobenius `frob s`; a tame generator `tau s` with
`frob τ frob⁻¹ = τ ^ q`; a `HeckeSym M p q s`-action `act s` commuting with `frob s` and `tau s`; the filtration
`Tt s ≤ TI s` (`T_t ⊆ T^{I_q}`, `thm:s05-G`(v)); the monodromy operator `N s`. -/
structure TateModuleData (M q p : ℕ) [Fact p.Prime] where
  /-- `T_pJ_s`. -/
  T : ℕ → Type
  /-- The additive group structure of `T s`. -/
  [addCommGroup : ∀ s, AddCommGroup (T s)]
  /-- The `ℤ_[p]`-module structure of `T s`. -/
  [module : ∀ s, Module ℤ_[p] (T s)]
  /-- `T s` is free over `ℤ_[p]`. -/
  free : ∀ s, Module.Free ℤ_[p] (T s)
  /-- `T s` is finitely generated over `ℤ_[p]`. -/
  finite : ∀ s, Module.Finite ℤ_[p] (T s)
  /-- The arithmetic Frobenius `Frob_q`. -/
  frob : ∀ s, T s ≃ₗ[ℤ_[p]] T s
  /-- A topological generator `τ` of tame inertia at `q`. -/
  tau : ∀ s, T s ≃ₗ[ℤ_[p]] T s
  /-- The tame relation `Frob τ Frob⁻¹ = τ ^ q`. -/
  frob_tau : ∀ s, (frob s).toLinearMap ∘ₗ (tau s).toLinearMap ∘ₗ (frob s).symm.toLinearMap =
    ((tau s).toLinearMap : Module.End ℤ_[p] (T s)) ^ q
  /-- The action of the Hecke symbols `HeckeSym M p q s` (S05-L1). -/
  act : ∀ s, HeckeSym M p q s → Module.End ℤ_[p] (T s)
  /-- The Hecke action commutes with `Frob_q`. -/
  act_frob : ∀ s h, act s h ∘ₗ (frob s).toLinearMap = (frob s).toLinearMap ∘ₗ act s h
  /-- The Hecke action commutes with `τ`. -/
  act_tau : ∀ s h, act s h ∘ₗ (tau s).toLinearMap = (tau s).toLinearMap ∘ₗ act s h
  /-- The toric part `T_t`. -/
  Tt : ∀ s, Submodule ℤ_[p] (T s)
  /-- The inertia invariants `T^{I_q}`. -/
  TI : ∀ s, Submodule ℤ_[p] (T s)
  /-- `T_t ⊆ T^{I_q}`. -/
  Tt_le_TI : ∀ s, Tt s ≤ TI s
  /-- The monodromy operator `N`. -/
  N : ∀ s, Module.End ℤ_[p] (T s)

attribute [instance] TateModuleData.addCommGroup TateModuleData.module

/-- `hyp:s05-X` (X2), (X4) (`s05-X`): the Brandt pairing `⟨[e],[e']⟩_w = w_e δ_{ee'}` restricted to
`ℤ[S]⁰ = degZero U ℤ` and base-changed to `ℤ_[p]`, a bilinear form on `ℤ_[p] ⊗[ℤ] ℤ[S]⁰`. In (X4) it gives the
monodromy operator `N : x ↦ ⟨x,·⟩_w` and the `⟨,⟩_w`-adjoint `θ(h)*` of the top piece. -/
noncomputable def wPairingZp (p : ℕ) [Fact p.Prime] {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) :
    LinearMap.BilinForm ℤ_[p] (ℤ_[p] ⊗[ℤ] degZero U ℤ) :=
  LinearMap.BilinForm.baseChange ℤ_[p]
    ((brandtPairing U ℤ).compl₁₂ (degZero U ℤ).subtype (degZero U ℤ).subtype)

/-- `hyp:s05-X` (X4) (`s05-X`; `HypXgal(M;q)`), on an abstract Tate-module datum `T : TateModuleData M q p`, for the
data of `Hyp.X.char` (`d`, `d.D = q`, `S s = X_B(U_1(M p^s))` = `d.Utower M p s (hN s)`, `θ_s = theta …`,
`def:s05-theta`) and a **given family** `φ s : G.X s ≃ₗ[ℤ] ℤ[S_s]⁰` (`Hyp.X.gal` presupposes the `φ_s`,
`rem:s05-hypX-lean`; it is meant together with `Hyp.X.char … G` witnessed by the same `φ`).

For all `s ≥ 0` the filtration `T_t ⊆ T^{I_q} ⊆ T_pJ_s` (`Tt s ≤ TI s ≤ ⊤`) has, as `𝓗_s`-modules (with `Frob_q` on the bottom piece only), the
graded pieces (`thm:s05-G`(v), (G4): `T/T^{I} ≅ X_q(J^∨) ⊗ ℤ_p ≅ X_q(J) ⊗ ℤ_p` via the principal polarisation,
`T_t = Hom(X_q(J), ℤ_p(1))`), given by `πX : T s → ℤ_[p] ⊗ X s` (surjective, kernel `TI s`) and
`ιX : Hom(ℤ_[p] ⊗ X s, ℤ_[p]) → T s` (injective, image `Tt s`) and transported to `ℤ[S_s]⁰` by `φ_s`:
`πTop := (φ_s ⊗ ℤ_p) ∘ πX : T s → ℤ_[p] ⊗ ℤ[S_s]⁰` and `ιBot := ιX ∘ (φ_s ⊗ ℤ_p)ᵀ : Hom(ℤ_[p] ⊗ ℤ[S_s]⁰, ℤ_[p]) → T s`
(written out inline below; `(φ_s ⊗ ℤ_p) = LinearMap.baseChange ℤ_[p] (φ s)`). The `ℤ`-module `Hom(ℤ[S_s]⁰, ℤ_p)` is
written as the `ℤ_[p]`-dual of the base change, so the transpose of `θ_s(h)` is the `dualMap` of its base change.
* bottom `T_t`: `Hom(ℤ[S_s]⁰, ℤ_p(1))` (written `Module.Dual ℤ_[p] (ℤ_[p] ⊗ ℤ[S_s]⁰)`), with the **transpose**
  action `h ↦ θ_s(h)ᵀ` (`dualMap` of the base change of `theta h`);
* middle `T^{I_q}/T_t`: `T_pJ_1(Mp^s)^{⊕2}` (via the two degeneracies), **opaque**: not constrained here;
* top `T/T^{I_q}`: `ℤ[S_s]⁰ ⊗ ℤ_p` with the Rosati-twisted action `h ↦ θ_s(h^Ros)`, read as the `⟨,⟩_w`-adjoint
  `θ_s(h)*` (Brandt adjoint; stated by the adjunction identity against `wPairingZp`);
* **FD1 clause (decided, Fabian, 2026-11-15).** The arithmetic `Frob_q` acts on the bottom (Hom-) piece as
  `q • (theta Uq).dualMap`, i.e. `q U_q` as the transpose of the endomorphism `θ_s(U_q) = +Π_q` of `ℤ[S_s]⁰`
  (stated on the Hom-piece, never on the top piece); `μ_N`-model with Picard functoriality, row 1 of the table of
  `rem:s05-Xstatus` (`σ_q = U_q⁻¹`, Frobenius permutation `Π_q⁻¹`). With the naive model it would
  read `q ⟨q⟩⁻¹ U_q`. The factor `q` is the Tate twist `ℤ_p(1)`;
* the monodromy operator `N` from the top to the bottom piece is `x ↦ ⟨x,·⟩_w` (via (X2); positive normalisation,
  `rem:s05-illusie`): `N t = ιBot ⟨πTop t, ·⟩_w`.

Data as in `hyp:s05-X`, except that `p ≥ 5` is not assumed (deviation; consumers add it). `h` ranges over `HeckeSym`
(no `U_ℓ` for `ℓ ∣ M`).

**Not constrained (toy model):** (a) `tau` is not used by `gal` (`tau`, `frob_tau`, `act_tau` are never referenced), so `tau = id`
with `N ≠ 0` is admissible and `N` is not tied to `τ` (e.g. `τ = 1 + N`); (b) `TI s` is constrained only as `ker πX`, not as the
`τ`-invariants; (c) Frobenius on the top and the middle piece, and Frobenius-stability of `TI s`; (d) the transport to
`H¹_par(Γ_s, ℤ_p)(1)` of the last sentence of (X4).

Toy model (no Galois group, no `ContinuousZlModule`); the claim "`T` is `T_pJ_s`" stays outside Lean.
Status: *hypothesis*; non-vacuity for all `s` by a direct-sum toy instance, unconditional
(`LanglandscapeTests.Hyp.S05.toyTate_gal_uncond`, S05-L4 + S05-L4g; parametric in the context `(d, …, Pq, hPq)`). -/
def gal (d : Langlandscape.Quat.DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
    (Pq : (Langlandscape.Quat.QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)
    (G : CharGroupData M q p) (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (T : TateModuleData M q p) : Prop :=
  ∀ s, ∃ (πX : T.T s →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] G.X s)
      (ιX : Module.Dual ℤ_[p] (ℤ_[p] ⊗[ℤ] G.X s) →ₗ[ℤ_[p]] T.T s),
    -- top piece `T / T^{I_q} ≅ ℤ_p ⊗ X s`
    Function.Surjective πX ∧ LinearMap.ker πX = T.TI s ∧
    -- bottom piece `T_t ≅ Hom(X s, ℤ_p(1))`
    Function.Injective ιX ∧ LinearMap.range ιX = T.Tt s ∧
    -- top: `πTop ∘ h = θ_s(h)* ∘ πTop` (Rosati twist, `⟨,⟩_w`-adjoint)
    (∀ (h : HeckeSym M p q s) (t : T.T s) (z : ℤ_[p] ⊗[ℤ] degZero (d.Utower M p s (hN s)) ℤ),
      wPairingZp p (d.Utower M p s (hN s))
          (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap (πX (T.act s h t))) z =
        wPairingZp p (d.Utower M p s (hN s)) (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap (πX t))
          (LinearMap.baseChange ℤ_[p] (theta d M p q s (hN s) hp hM hpM hD Pq hPq h) z)) ∧
    -- bottom: transpose action `h ∘ ιBot = ιBot ∘ θ_s(h)ᵀ`
    (∀ h : HeckeSym M p q s,
      T.act s h ∘ₗ ιX ∘ₗ LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap) =
        ιX ∘ₗ LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap) ∘ₗ
          LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (theta d M p q s (hN s) hp hM hpM hD Pq hPq h))) ∧
    -- FD1 clause (decided): `Frob_q = q • (theta Uq).dualMap` on the bottom (Hom-) piece
    ((T.frob s).toLinearMap ∘ₗ ιX ∘ₗ LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap) =
        ιX ∘ₗ LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap) ∘ₗ
          ((q : ℤ_[p]) • LinearMap.dualMap
            (LinearMap.baseChange ℤ_[p] (theta d M p q s (hN s) hp hM hpM hD Pq hPq HeckeSym.Uq)))) ∧
    -- monodromy: `N t = ιBot ⟨πTop t, ·⟩_w`
    (∀ t : T.T s,
      T.N s t = ιX (LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap)
        (wPairingZp p (d.Utower M p s (hN s)) (LinearMap.baseChange ℤ_[p] (φ s).toLinearMap (πX t)))))

end Langlandscape.Hyp.X
