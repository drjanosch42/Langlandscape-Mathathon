/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.TwoTerm

/-!
# The two-term complex with coefficients (S03-L14)

`mathematics/chapters/s03/3-ribet.tex` (`thm:s03-ribet`(b), coefficient layer) and
`mathematics/chapters/s03/4-ihara.tex` (`ss:s03-conv`, conventions (C1) and (C3)); generalises stage 02's
trivial-coefficient `partialHom`/`deltaCoh`/`s0Tr`/`s1Tr` (`if:s02-coh`, `def:s02-Mhom`) to the stage-1 Brandt modules
`brandtModule U R V ρ = {f : B̂^× → V | f(γ x u) = ρ(u)⁻¹ f(x)}`.

Fix a prime `q ∤ D`, a `q`-level `U`, `U' = U_0(q)U` and `α = ι_q^{-1} diag(1, q)` (`Tree.alphaElt`).

* `CoeffData d q hq U R V` : an action `ρ : U →* (V ≃ₗ[R] V)` with `ρ(α⁻¹ u α) = ρ(u)` for `u ∈ U'` (true when `ρ`
  factors through the `p`-component, `p ≠ q`); `ρ'` its restriction to `U'`.
* generic layer: `resRho`, `restrictV` (restriction of functions), `traceVRaw`/`traceV`
  (`(tr f)(x) = ∑_{u ∈ U/U'} ρ(u) f(x u)`, independent of the representatives).
* `s0PullV f = f`, `s1PullV f = f(· α)`, `s0TrV`, `s1TrV f = tr(f(· α⁻¹))` (from `α⁻¹U'α` to `U`).
* `alphaV = (−s0TrV, s1TrV)`, `alphaVee (f₀, f₁) = s1PullV f₁ − s0PullV f₀` (signs (C1)).
* `s0TrV_comp_s0PullV` : `s0TrV ∘ s0PullV = [U : U'] • id`.
* `alphaV_triv`, `alphaVee_triv` : for `V = R`, `ρ = 1`, under `brandtModuleTrivEquiv` these are stage 02's
  `(−s0Tr, s1Tr)` and `deltaCoh`.

Status: *formalized*.
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree

/-! ### Generic layer: restriction and trace with coefficients -/

section Generic

variable {a b : ℤ} {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- `thm:s03-ribet`(b), (C3): the restriction `ρ|_{U'}` of a coefficient action to a smaller level `U' ≤ U`. -/
noncomputable def resRho {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) (ρ : U →* (V ≃ₗ[R] V)) :
    U' →* (V ≃ₗ[R] V) :=
  ρ.comp (Subgroup.inclusion hle)

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `ρ|_{U'}(u) = ρ(u)`. -/
theorem resRho_apply {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) (ρ : U →* (V ≃ₗ[R] V)) (u : U') :
    resRho hle ρ u = ρ ⟨(u : (GL2TF.Quat.BHat a b)ˣ), hle u.2⟩ :=
  rfl

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): an element of a Brandt module satisfies `f(x u) = ρ(u)⁻¹ f(x)`. -/
theorem brandt_apply_mul {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {ρ : U →* (V ≃ₗ[R] V)}
    {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U R V ρ) (x : (GL2TF.Quat.BHat a b)ˣ) (u : U) :
    f (x * (u : (GL2TF.Quat.BHat a b)ˣ)) = (ρ u)⁻¹ (f x) := by
  simpa only [map_one, one_mul] using hf 1 x u

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): an element of a Brandt module satisfies `f(γ x) = f(x)`. -/
theorem brandt_apply_left {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {ρ : U →* (V ≃ₗ[R] V)}
    {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U R V ρ) (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ)
    (x : (GL2TF.Quat.BHat a b)ˣ) : f (iotaU a b γ * x) = f x := by
  simpa using hf γ x 1

/-- `thm:s03-ribet`(b), (C3): restriction of functions `Brandt(U, V) → Brandt(U', V)` for `U' ≤ U`, `f ↦ f`. -/
noncomputable def restrictV {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) (ρ : U →* (V ≃ₗ[R] V)) :
    brandtModule U R V ρ →ₗ[R] brandtModule U' R V (resRho hle ρ) where
  toFun f := ⟨f.1, by
    intro γ x u
    exact f.2 γ x ⟨(u : (GL2TF.Quat.BHat a b)ˣ), hle u.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `thm:s03-ribet`(b), (C3): the trace on lifts with coefficients, `x ↦ ∑_{u ∈ U/U'} ρ(u) f(x u)`. -/
noncomputable def traceVRaw (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (ρ : U →* (V ≃ₗ[R] V))
    (f : (GL2TF.Quat.BHat a b)ˣ → V) (x : (GL2TF.Quat.BHat a b)ˣ) : V :=
  ∑ᶠ c : ↥U ⧸ U'.subgroupOf U,
    ρ (Quotient.out c) (f (x * ((Quotient.out c : U) : (GL2TF.Quat.BHat a b)ˣ)))

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `traceVRaw f` is invariant under left translation by `B^×`. -/
theorem traceVRaw_left {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {ρ : U →* (V ≃ₗ[R] V)}
    {ρ' : U' →* (V ≃ₗ[R] V)} {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U' R V ρ')
    (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    traceVRaw U' U ρ f (iotaU a b γ * x) = traceVRaw U' U ρ f x := by
  unfold traceVRaw
  refine finsum_congr fun c => ?_
  rw [mul_assoc, brandt_apply_left hf]

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `traceVRaw f (x w) = ρ(w)⁻¹ traceVRaw f (x)` for `w ∈ U`
(independence of the coset representatives and reindexing `u ↦ w u`). -/
theorem traceVRaw_mul_right {U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ} (hle : U' ≤ U) {ρ : U →* (V ≃ₗ[R] V)}
    {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U' R V (resRho hle ρ))
    (x : (GL2TF.Quat.BHat a b)ˣ) (w : U) :
    traceVRaw U' U ρ f (x * (w : (GL2TF.Quat.BHat a b)ˣ)) = (ρ w)⁻¹ (traceVRaw U' U ρ f x) := by
  have hτ : ∀ z : U, ∀ v ∈ U'.subgroupOf U,
      ρ (z * v) (f (x * ((z * v : U) : (GL2TF.Quat.BHat a b)ˣ))) =
        ρ z (f (x * (z : (GL2TF.Quat.BHat a b)ˣ))) := by
    intro z v hv
    have hv' : ((v : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ U' := Subgroup.mem_subgroupOf.mp hv
    have h1 : f (x * (z : (GL2TF.Quat.BHat a b)ˣ) * (v : (GL2TF.Quat.BHat a b)ˣ)) =
        (ρ v)⁻¹ (f (x * (z : (GL2TF.Quat.BHat a b)ˣ))) :=
      brandt_apply_mul hf (x * (z : (GL2TF.Quat.BHat a b)ˣ)) ⟨_, hv'⟩
    rw [Subgroup.coe_mul, ← mul_assoc, h1, map_mul, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply]
  have key := GL2TF.HeckeModule.coset_finsum_translate (U := U'.subgroupOf U)
    (τ := fun z : U => ρ z (f (x * (z : (GL2TF.Quat.BHat a b)ˣ)))) hτ w
  apply (ρ w).injective
  rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  refine Eq.trans ?_ key
  unfold traceVRaw
  rw [AddEquivClass.map_finsum (ρ w)]
  refine finsum_congr fun c => ?_
  simp only [map_mul, LinearEquiv.mul_apply, Subgroup.coe_mul, mul_assoc]

/-- `thm:s03-ribet`(b), (C3): the trace with coefficients `tr : Brandt(U', V) → Brandt(U, V)`,
`(tr f)(x) = ∑_{u ∈ U/U'} ρ(u) f(x u)`, for `U' ≤ U` of finite index. -/
noncomputable def traceV (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (ρ : U →* (V ≃ₗ[R] V)) : brandtModule U' R V (resRho hle ρ) →ₗ[R] brandtModule U R V ρ where
  toFun f := ⟨traceVRaw U' U ρ f.1, by
    intro γ x u
    rw [traceVRaw_mul_right hle f.2, traceVRaw_left f.2]⟩
  map_add' f g := by
    have := finite_quotient_of_relIndex U' U hrel
    have := Fintype.ofFinite (↥U ⧸ U'.subgroupOf U)
    apply Subtype.ext
    funext x
    show traceVRaw U' U ρ (f + g).1 x = traceVRaw U' U ρ f.1 x + traceVRaw U' U ρ g.1 x
    simp only [traceVRaw, finsum_eq_sum_of_fintype, Submodule.coe_add, Pi.add_apply, map_add,
      Finset.sum_add_distrib]
  map_smul' r f := by
    have := finite_quotient_of_relIndex U' U hrel
    have := Fintype.ofFinite (↥U ⧸ U'.subgroupOf U)
    apply Subtype.ext
    funext x
    show traceVRaw U' U ρ (r • f).1 x = r • traceVRaw U' U ρ f.1 x
    simp only [traceVRaw, finsum_eq_sum_of_fintype, Submodule.coe_smul, Pi.smul_apply,
      LinearEquiv.map_smul, Finset.smul_sum]

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(tr f)(x) = ∑_{u ∈ U/U'} ρ(u) f(x u)`. -/
theorem traceV_apply (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (ρ : U →* (V ≃ₗ[R] V)) (f : brandtModule U' R V (resRho hle ρ)) (x : (GL2TF.Quat.BHat a b)ˣ) :
    (traceV U' U hle hrel ρ f).1 x = traceVRaw U' U ρ f.1 x :=
  rfl

/-- `def:s01-brandt`, `thm:s03-ribet`(b) (`s03-conv`): for trivial coefficients,
`brandtModuleTrivEquiv f [y] = f(y)` for every representative `y`. -/
theorem brandtModuleTrivEquiv_apply_mk {U : Subgroup (GL2TF.Quat.BHat a b)ˣ}
    (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R))) (y : (GL2TF.Quat.BHat a b)ˣ) :
    brandtModuleTrivEquiv U R f (DoubleCoset.mk (globalUnits a b) U y) = f.1 y := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U y
  show f.1 (Quotient.out (DoubleCoset.mk (globalUnits a b) U y)) = f.1 y
  rw [he]
  have h2 := f.2 k y ⟨v, hv⟩
  simp at h2
  exact h2

end Generic

/-! ### Coefficient data -/

section Data

/-- `thm:s03-ribet`(b), `thm:s03-iharaH0`, (C3): coefficient data at a `q`-level `U`: an `R`-linear action
`ρ : U →* (V ≃ₗ[R] V)` with `ρ(α⁻¹ u α) = ρ(u)` for `u ∈ U_0(q)U` (true when `ρ` factors through the
`p`-component, `p ≠ q`, since `α` is supported at `q`). -/
structure CoeffData (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] where
  /-- the action of `U` on `V` -/
  ρ : U →* (V ≃ₗ[R] V)
  /-- invariance under conjugation by `α`: `ρ(α⁻¹ u α) = ρ(u)` for `u ∈ U_0(q)U` -/
  hα : ∀ u : U, (u : (BHat d.a d.b)ˣ) ∈ d.U0q q (coprime_of_not_dvd hq) U →
    ∀ h : (alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq ∈ U,
      ρ ⟨(alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq, h⟩ = ρ u

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- `thm:s03-ribet`(b), (C3): the restricted action `ρ' = ρ|_{U_0(q)U}`. -/
noncomputable abbrev CoeffData.ρ' (c : CoeffData d q hq U R V) :
    d.U0q q (coprime_of_not_dvd hq) U →* (V ≃ₗ[R] V) :=
  resRho (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) c.ρ

/-- `thm:s03-ribet`(b), (C3): the restricted action `ρ|_{α⁻¹ U' α}` on the level `s1Level = α⁻¹ (U_0(q)U) α`. -/
noncomputable abbrev CoeffData.ρα (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    s1Level d q hq U →* (V ≃ₗ[R] V) :=
  resRho (s1Level_le hU) c.ρ

variable (d q hq U R) in
/-- `thm:s03-ribet`(b), (C3): trivial coefficients `V = R`, `ρ = 1`. -/
noncomputable def CoeffData.triv : CoeffData d q hq U R R where
  ρ := 1
  hα _ _ _ := rfl

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `α = ι_q^{-1} diag(1, q)` has trivial `p`-component for `p ≠ q`. -/
theorem localComponent_alphaElt_of_ne {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ d.D) (hpq : p ≠ q) :
    localComponent d p hp (alphaElt d q hq) = 1 :=
  localComponent_localEmbedGL_of_ne (hp := hq) (hq := hp) (alphaq q) hpq

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): conjugation by `α` does not change `p`-components, `p ≠ q`:
`(α⁻¹ u α)_p = u_p`. -/
theorem localComponent_alphaElt_conj {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ d.D) (hpq : p ≠ q)
    (u : (BHat d.a d.b)ˣ) :
    localComponent d p hp ((alphaElt d q hq)⁻¹ * u * alphaElt d q hq) = localComponent d p hp u := by
  rw [map_mul, map_mul, map_inv, localComponent_alphaElt_of_ne hp hpq, inv_one, one_mul, mul_one]

variable (d q hq U) in
/-- `thm:s03-ribet`(b), `thm:s03-iharaH0`, (C3): coefficient data from a representation `ρ_p` of `GL₂(ℚ_p)`,
`p ≠ q`, `p ∤ D`: `ρ(u) = ρ_p(u_p)`; the condition `hα` holds since `α` is supported at `q`
(`localComponent_alphaElt_conj`). -/
noncomputable def CoeffData.ofLocal (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (hpq : p ≠ q)
    (ρp : GL (Fin 2) ℚ_[p] →* (V ≃ₗ[R] V)) : CoeffData d q hq U R V where
  ρ := ρp.comp ((localComponent d p hp).comp U.subtype)
  hα u _ _ :=
    congrArg (fun g => ρp g) (localComponent_alphaElt_conj (hq := hq) hp hpq (u : (BHat d.a d.b)ˣ))

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(CoeffData.ofLocal … ρ_p).ρ u = ρ_p(u_p)`. -/
theorem CoeffData.ofLocal_ρ_apply (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (hpq : p ≠ q)
    (ρp : GL (Fin 2) ℚ_[p] →* (V ≃ₗ[R] V)) (u : U) :
    (CoeffData.ofLocal d q hq U p hp hpq ρp).ρ u = ρp (localComponent d p hp (u : (BHat d.a d.b)ˣ)) :=
  rfl

end Data

/-! ### The maps `s_j^*`, `s_{j*}` and `α`, `α^∨` with coefficients -/

section Maps

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- `thm:s03-ribet`(b), (C3): `s_0^* : Brandt(U, V) → Brandt(U_0(q)U, V)`, `(s_0^* f)(y) = f(y)` (restriction). -/
noncomputable def s0PullV (c : CoeffData d q hq U R V) :
    brandtModule U R V c.ρ →ₗ[R] brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' :=
  restrictV (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) c.ρ

/-- `thm:s03-ribet`(b), (C3): `s_1^* : Brandt(U, V) → Brandt(U_0(q)U, V)`, `(s_1^* f)(y) = f(y α)`
(uses `α⁻¹ U' α ⊆ U` and `ρ(α⁻¹ u α) = ρ(u)`). -/
noncomputable def s1PullV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule U R V c.ρ →ₗ[R] brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' where
  toFun f := ⟨fun x => f.1 (x * alphaElt d q hq), by
    intro γ x u
    have hm : (alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq ∈ U :=
      alphaElt_inv_conj_mem hU u.2
    have hα' : c.ρ ⟨(alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq, hm⟩ = c.ρ' u :=
      c.hα ⟨(u : (BHat d.a d.b)ˣ), DefiniteData.U0q_le q (coprime_of_not_dvd hq) U u.2⟩ u.2 hm
    calc f.1 (iotaU d.a d.b γ * x * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq)
        = f.1 (iotaU d.a d.b γ * (x * alphaElt d q hq) *
            ((alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq)) := by
          congr 1
          group
      _ = (c.ρ ⟨(alphaElt d q hq)⁻¹ * (u : (BHat d.a d.b)ˣ) * alphaElt d q hq, hm⟩)⁻¹
            (f.1 (x * alphaElt d q hq)) := f.2 γ (x * alphaElt d q hq) ⟨_, hm⟩
      _ = (c.ρ' u)⁻¹ (f.1 (x * alphaElt d q hq)) := by rw [hα']⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `thm:s03-ribet`(b), (C3): right translation by `α⁻¹`, `Brandt(U_0(q)U, V) → Brandt(α⁻¹ U' α, V)`,
`f ↦ f(· α⁻¹)` (uses `ρ(α v α⁻¹) = ρ(v)` for `v ∈ α⁻¹ U' α`). -/
noncomputable def transV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' →ₗ[R]
      brandtModule (s1Level d q hq U) R V (c.ρα hU) where
  toFun f := ⟨fun x => f.1 (x * (alphaElt d q hq)⁻¹), by
    intro γ x v
    have hw : alphaElt d q hq * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹ ∈
        d.U0q q (coprime_of_not_dvd hq) U :=
      conj_mem_of_mem_rightConj _ _ _ v.2
    have hvU : (v : (BHat d.a d.b)ˣ) ∈ U := s1Level_le hU v.2
    have e : (alphaElt d q hq)⁻¹ * (alphaElt d q hq * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹) *
        alphaElt d q hq = (v : (BHat d.a d.b)ˣ) := by group
    have hmem : (alphaElt d q hq)⁻¹ * (alphaElt d q hq * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹) *
        alphaElt d q hq ∈ U := by
      rw [e]
      exact hvU
    have h2 : (⟨(alphaElt d q hq)⁻¹ * (alphaElt d q hq * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹) *
        alphaElt d q hq, hmem⟩ : U) = ⟨(v : (BHat d.a d.b)ˣ), hvU⟩ := Subtype.ext e
    have key : c.ρ' ⟨_, hw⟩ = c.ρα hU v :=
      (c.hα ⟨_, DefiniteData.U0q_le q (coprime_of_not_dvd hq) U hw⟩ hw hmem).symm.trans
        (congrArg (fun w : U => c.ρ w) h2)
    calc f.1 (iotaU d.a d.b γ * x * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)
        = f.1 (iotaU d.a d.b γ * (x * (alphaElt d q hq)⁻¹) *
            (alphaElt d q hq * (v : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)) := by
          congr 1
          group
      _ = (c.ρ' ⟨_, hw⟩)⁻¹ (f.1 (x * (alphaElt d q hq)⁻¹)) := f.2 γ (x * (alphaElt d q hq)⁻¹) ⟨_, hw⟩
      _ = (c.ρα hU v)⁻¹ (f.1 (x * (alphaElt d q hq)⁻¹)) := by rw [key]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `thm:s03-ribet`(b), (C3): the trace `s_{0*} : Brandt(U_0(q)U, V) → Brandt(U, V)`,
`(s_{0*} f)(x) = ∑_{u ∈ U/U'} ρ(u) f(x u)`. -/
noncomputable def s0TrV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' →ₗ[R] brandtModule U R V c.ρ :=
  traceV (d.U0q q (coprime_of_not_dvd hq) U) U (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U)
    (relIndex_U0q_ne_zero hU) c.ρ

/-- `thm:s03-ribet`(b), (C3): the trace `s_{1*} : Brandt(U_0(q)U, V) → Brandt(U, V)`,
`(s_{1*} f)(x) = ∑_{u ∈ U/α⁻¹U'α} ρ(u) f(x u α⁻¹)`: translate by `α⁻¹`, then trace from `α⁻¹ U' α` to `U`. -/
noncomputable def s1TrV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' →ₗ[R] brandtModule U R V c.ρ :=
  (traceV (s1Level d q hq U) U (s1Level_le hU) (relIndex_s1Level_ne_zero hU) c.ρ).comp (transV c hU)

/-- `thm:s03-ribet`(b), (C1), (C3): the coefficient differential
`α = (−s_{0*}, s_{1*}) : Brandt(U_0(q)U, V) → Brandt(U, V)²`. -/
noncomputable def alphaV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' →ₗ[R]
      brandtModule U R V c.ρ × brandtModule U R V c.ρ :=
  (-(s0TrV c hU)).prod (s1TrV c hU)

/-- `thm:s03-ribet`(b), (C1), (C3): the transpose `α^∨(f₀, f₁) = s_1^* f₁ − s_0^* f₀ :
Brandt(U, V)² → Brandt(U_0(q)U, V)`. -/
noncomputable def alphaVee (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    brandtModule U R V c.ρ × brandtModule U R V c.ρ →ₗ[R]
      brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ' :=
  (s1PullV c hU).comp (LinearMap.snd R _ _) - (s0PullV c).comp (LinearMap.fst R _ _)

/-! #### Evaluation formulas -/

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(s_0^* f)(y) = f(y)`. -/
theorem s0PullV_apply (c : CoeffData d q hq U R V) (f : brandtModule U R V c.ρ) (y : (BHat d.a d.b)ˣ) :
    (s0PullV c f).1 y = f.1 y :=
  rfl

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(s_1^* f)(y) = f(y α)`. -/
theorem s1PullV_apply (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) (f : brandtModule U R V c.ρ)
    (y : (BHat d.a d.b)ˣ) : (s1PullV c hU f).1 y = f.1 (y * alphaElt d q hq) :=
  rfl

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(s_{0*} f)(x) = ∑_{u ∈ U/U'} ρ(u) f(x u)`. -/
theorem s0TrV_apply (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ') (x : (BHat d.a d.b)ˣ) :
    (s0TrV c hU f).1 x =
      ∑ᶠ u : ↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U,
        c.ρ (Quotient.out u) (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ))) :=
  rfl

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `(s_{1*} f)(x) = ∑_{u ∈ U/α⁻¹U'α} ρ(u) f(x u α⁻¹)`. -/
theorem s1TrV_apply (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ') (x : (BHat d.a d.b)ˣ) :
    (s1TrV c hU f).1 x =
      ∑ᶠ u : ↥U ⧸ (s1Level d q hq U).subgroupOf U,
        c.ρ (Quotient.out u) (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)) :=
  rfl

/-- `thm:s03-ribet`(b), (C1) (`s03-conv`): `α f = (−s_{0*} f, s_{1*} f)`. -/
theorem alphaV_apply (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R V c.ρ') :
    alphaV c hU f = (-(s0TrV c hU f), s1TrV c hU f) :=
  rfl

/-- `thm:s03-ribet`(b), (C1) (`s03-conv`): `α^∨(f₀, f₁) = s_1^* f₁ − s_0^* f₀`. -/
theorem alphaVee_apply (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U)
    (f : brandtModule U R V c.ρ × brandtModule U R V c.ρ) :
    alphaVee c hU f = s1PullV c hU f.2 - s0PullV c f.1 :=
  rfl

/-! #### The index relation -/

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): `s_{0*} ∘ s_0^* = [U : U_0(q)U] • id` on `Brandt(U, V)`. -/
theorem s0TrV_comp_s0PullV (c : CoeffData d q hq U R V) (hU : IsQLevel d q hq U) :
    s0TrV c hU ∘ₗ s0PullV c =
      (((d.U0q q (coprime_of_not_dvd hq) U).relIndex U : ℕ) : R) • LinearMap.id := by
  have := finite_quotient_of_relIndex _ U (relIndex_U0q_ne_zero hU)
  have := Fintype.ofFinite (↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U)
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  show ∑ᶠ u : ↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U,
      c.ρ (Quotient.out u) (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ))) =
    (((d.U0q q (coprime_of_not_dvd hq) U).relIndex U : ℕ) : R) • f.1 x
  have hterm : ∀ u : ↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U,
      c.ρ (Quotient.out u) (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ))) = f.1 x := by
    intro u
    rw [brandt_apply_mul f.2, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul R]
  rfl

end Maps

/-! ### Comparison with stage 02 (trivial coefficients) -/

section Triv

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R]

variable (d q hq U R) in
/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): for trivial data the restricted action `ρ'` is trivial. -/
theorem CoeffData.triv_ρ' : (CoeffData.triv d q hq U R).ρ' = 1 :=
  MonoidHom.ext fun _ => rfl

variable (d q hq U R) in
/-- `thm:s03-ribet`(b), (C3) (`s03-conv`): for trivial data the action `ρ` is trivial. -/
theorem CoeffData.triv_ρ : (CoeffData.triv d q hq U R).ρ = 1 :=
  rfl

variable (d q hq U R) in
/-- `def:s01-brandt`, `thm:s03-ribet`(b): the identification `Brandt(U, R)` (trivial `ρ`) `≃ R^{X(U)}`,
`f ↦ (f(c.out))_c` (stage 1's `brandtModuleTrivEquiv`, transported along `ρ = 1`). -/
noncomputable def trivEquivU :
    brandtModule U R R (CoeffData.triv d q hq U R).ρ ≃ₗ[R] ZXdual U R :=
  (LinearEquiv.ofEq _ _ (congrArg (brandtModule U R R) (CoeffData.triv_ρ d q hq U R))).trans
    (brandtModuleTrivEquiv U R)

/-- `def:s01-brandt`, `thm:s03-ribet`(b) (`s03-conv`): `trivEquivU f [y] = f(y)`. -/
theorem trivEquivU_apply_mk (f : brandtModule U R R (CoeffData.triv d q hq U R).ρ) (y : (BHat d.a d.b)ˣ) :
    trivEquivU d q hq U R f (DoubleCoset.mk (globalUnits d.a d.b) U y) = f.1 y :=
  brandtModuleTrivEquiv_apply_mk
    (LinearEquiv.ofEq _ _ (congrArg (brandtModule U R R) (CoeffData.triv_ρ d q hq U R)) f) y

variable (d q hq U R) in
/-- `def:s01-brandt`, `thm:s03-ribet`(b): the identification `Brandt(U_0(q)U, R)` (trivial `ρ'`) `≃ R^{X(U_0(q)U)}`,
`f ↦ (f(c.out))_c` (stage 1's `brandtModuleTrivEquiv` after `ρ' = 1`). -/
noncomputable def trivEquivU0q :
    brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R (CoeffData.triv d q hq U R).ρ' ≃ₗ[R]
      ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R :=
  (LinearEquiv.ofEq _ _
    (congrArg (brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R) (CoeffData.triv_ρ' d q hq U R))).trans
    (brandtModuleTrivEquiv _ R)

/-- `def:s01-brandt`, `thm:s03-ribet`(b) (`s03-conv`): `trivEquivU0q f [y] = f(y)`. -/
theorem trivEquivU0q_apply_mk
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R (CoeffData.triv d q hq U R).ρ')
    (y : (BHat d.a d.b)ˣ) :
    trivEquivU0q d q hq U R f (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y) =
      f.1 y :=
  brandtModuleTrivEquiv_apply_mk
    (LinearEquiv.ofEq _ _
      (congrArg (brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R) (CoeffData.triv_ρ' d q hq U R)) f) y

/-- `thm:s03-ribet`(b), `if:s02-coh` (`s03-conv`): for `V = R`, `ρ = 1`, `s0TrV` is stage 02's `tr_0 = s0Tr`. -/
theorem s0TrV_triv (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R (CoeffData.triv d q hq U R).ρ') :
    trivEquivU d q hq U R (s0TrV (CoeffData.triv d q hq U R) hU f) =
      s0Tr d q hq U R hU (trivEquivU0q d q hq U R f) := by
  funext cl
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = cl := ⟨_, DoubleCoset.out_eq' cl⟩
  rw [trivEquivU_apply_mk, s0Tr_apply_mk hU]
  show ∑ᶠ u : ↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U,
      (CoeffData.triv d q hq U R).ρ (Quotient.out u) (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ))) = _
  refine finsum_congr fun u => ?_
  exact (trivEquivU0q_apply_mk f _).symm

/-- `thm:s03-ribet`(b), `if:s02-coh` (`s03-conv`): for `V = R`, `ρ = 1`, `s1TrV` is stage 02's `tr_1 = s1Tr`. -/
theorem s1TrV_triv (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R (CoeffData.triv d q hq U R).ρ') :
    trivEquivU d q hq U R (s1TrV (CoeffData.triv d q hq U R) hU f) =
      s1Tr d q hq U R hU (trivEquivU0q d q hq U R f) := by
  funext cl
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = cl := ⟨_, DoubleCoset.out_eq' cl⟩
  rw [trivEquivU_apply_mk, s1Tr_apply_mk hU]
  show ∑ᶠ u : ↥U ⧸ (s1Level d q hq U).subgroupOf U,
      (CoeffData.triv d q hq U R).ρ (Quotient.out u)
        (f.1 (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)) = _
  refine finsum_congr fun u => ?_
  exact (trivEquivU0q_apply_mk f _).symm

/-- `thm:s03-ribet`(b), `if:s02-coh`, (C1) (`s03-conv`): for `V = R`, `ρ = 1`, under `trivEquivU`/`trivEquivU0q`
(stage 1's `brandtModuleTrivEquiv` after `ρ = 1`), `alphaV = (−s0Tr, s1Tr)` (stage 02's trivial-coefficient traces). -/
theorem alphaV_triv (hU : IsQLevel d q hq U)
    (f : brandtModule (d.U0q q (coprime_of_not_dvd hq) U) R R (CoeffData.triv d q hq U R).ρ') :
    (trivEquivU d q hq U R (alphaV (CoeffData.triv d q hq U R) hU f).1,
        trivEquivU d q hq U R (alphaV (CoeffData.triv d q hq U R) hU f).2) =
      (-(s0Tr d q hq U R hU (trivEquivU0q d q hq U R f)), s1Tr d q hq U R hU (trivEquivU0q d q hq U R f)) := by
  refine Prod.ext ?_ ?_
  · show trivEquivU d q hq U R (-(s0TrV (CoeffData.triv d q hq U R) hU f)) =
      -(s0Tr d q hq U R hU (trivEquivU0q d q hq U R f))
    rw [map_neg, s0TrV_triv]
  · exact s1TrV_triv hU f

/-- `thm:s03-ribet`(b), `if:s02-coh`, (C1) (`s03-conv`): for `V = R`, `ρ = 1`, under `trivEquivU`/`trivEquivU0q`
(stage 1's `brandtModuleTrivEquiv` after `ρ = 1`), `alphaVee = deltaCoh`
(stage 02's `δ(f₀, f₁) = s_1^* f₁ − s_0^* f₀`). -/
theorem alphaVee_triv (hU : IsQLevel d q hq U)
    (f : brandtModule U R R (CoeffData.triv d q hq U R).ρ × brandtModule U R R (CoeffData.triv d q hq U R).ρ) :
    trivEquivU0q d q hq U R (alphaVee (CoeffData.triv d q hq U R) hU f) =
      deltaCoh d q hq U R (trivEquivU d q hq U R f.1, trivEquivU d q hq U R f.2) := by
  funext cl
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y = cl :=
    ⟨_, DoubleCoset.out_eq' cl⟩
  rw [trivEquivU0q_apply_mk]
  show (alphaVee (CoeffData.triv d q hq U R) hU f).1 y =
    trivEquivU d q hq U R f.2 (s1 d q hq U
        (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y)) -
      trivEquivU d q hq U R f.1 (s0 d q hq U
        (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y))
  rw [s0_mk, s1_mk hU, trivEquivU_apply_mk, trivEquivU_apply_mk]
  rfl

end Triv

end Langlandscape.Ribet
