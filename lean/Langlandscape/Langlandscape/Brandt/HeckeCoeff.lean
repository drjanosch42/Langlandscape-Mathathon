/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.DoubleCoset

/-!
# Hecke operators with coefficients (S04-L15a, carry-over of `def:s01-hecke`)

`mathematics/chapters/s01/4-hecke.tex`, `def:s01-hecke`: for `g ∈ B̂^×` and `U g U = ⊔ᵢ gᵢ U`,
`(T_g f)(x) = ∑ᵢ gᵢ · f(x gᵢ)` on `brandtModule U R V ρ = {f | f(γ x u) = ρ(u)⁻¹ f(x)}`.

Encoding of "`ρ` extends to a monoid `Σ ∋ g`": the stage-1 `ρ : U →* (V ≃ₗ[R] V)` lives on `U` only, so we bundle
a submonoid `Σ ≤ B̂^×` containing `U`, an action `ρΣ : Σ →* Module.End R V` (not necessarily invertible, as for
`Σ_p = M₂(ℤ_p) ∩ GL₂(ℚ_p)` acting on `V_k`) and the compatibility `ρΣ|_U = ρ` (`HeckeExt U R V ρ`).

* `HeckeExt U R V ρ` : the extension data `(Σ, ρΣ, U ⊆ Σ, ρΣ|_U = ρ)`; `HeckeExt.rhoExt` : `ρΣ` extended by `0`.
* `IsDcReps U g T` : `T` is a finite system of representatives of the left cosets `yU ⊆ U g U`;
  `exists_dcReps`, `IsDcReps.mul_left`.
* `heckeTVRaw E g f x = ∑_{c ∈ B̂^×/U, c ⊆ UgU} ρΣ(c.out) f(x c.out)`; `heckeTVRaw_eq_sum`
  (well-definedness: any system of representatives computes it), `heckeTVRaw_mem`.
* `heckeTV E g hg hfin : brandtModule U R V ρ →ₗ[R] brandtModule U R V ρ`; `heckeTV_apply_reps`.
* `heckeTV_triv` : for `V = R`, `ρ = 1`, `ρΣ = 1`, `heckeTV` is `heckeT` under `brandtModuleTrivEquiv`.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

variable {a b : ℤ}

section Ext

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (V : Type*) [AddCommGroup V] [Module R V]

/-- `def:s01-hecke` with coefficients (`s01-hecke`, `s04-L15a`): an extension of the coefficient action
`ρ : U →* (V ≃ₗ[R] V)` to a submonoid `Σ ⊇ U` of `B̂^×`, as an action by (not necessarily invertible)
endomorphisms, with `ρΣ(u) = ρ(u)` for `u ∈ U`. -/
structure HeckeExt (ρ : U →* (V ≃ₗ[R] V)) where
  /-- the submonoid `Σ ⊆ B̂^×` -/
  Sig : Submonoid (GL2TF.Quat.BHat a b)ˣ
  /-- the action of `Σ` on `V` by endomorphisms -/
  rhoSig : Sig →* Module.End R V
  /-- `U ⊆ Σ` -/
  U_le : ∀ u ∈ U, u ∈ Sig
  /-- `ρΣ` extends the `U`-action: `ρΣ(u) = ρ(u)` for `u ∈ U` -/
  compat : ∀ u : U, rhoSig ⟨(u : (GL2TF.Quat.BHat a b)ˣ), U_le _ u.2⟩ = ((ρ u : V ≃ₗ[R] V) : V →ₗ[R] V)

variable {U R V} {ρ : U →* (V ≃ₗ[R] V)}

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `ρΣ` extended by `0` to all of `B̂^×`. -/
noncomputable def HeckeExt.rhoExt (E : HeckeExt U R V ρ) (y : (GL2TF.Quat.BHat a b)ˣ) : Module.End R V :=
  if h : y ∈ E.Sig then E.rhoSig ⟨y, h⟩ else 0

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): on `Σ`, `rhoExt` is `ρΣ`. -/
theorem HeckeExt.rhoExt_of_mem (E : HeckeExt U R V ρ) {y : (GL2TF.Quat.BHat a b)ˣ} (h : y ∈ E.Sig) :
    E.rhoExt y = E.rhoSig ⟨y, h⟩ := by
  unfold HeckeExt.rhoExt
  exact dite_eq_left h

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `ρΣ(u y) = ρ(u) ρΣ(y)` for `u ∈ U`, `y ∈ Σ`. -/
theorem HeckeExt.rhoExt_mul_left (E : HeckeExt U R V ρ) (u : U) {y : (GL2TF.Quat.BHat a b)ˣ}
    (hy : y ∈ E.Sig) :
    E.rhoExt ((u : (GL2TF.Quat.BHat a b)ˣ) * y) = ((ρ u : V ≃ₗ[R] V) : V →ₗ[R] V) * E.rhoExt y := by
  rw [E.rhoExt_of_mem (E.Sig.mul_mem (E.U_le _ u.2) hy), E.rhoExt_of_mem hy, ← E.compat u]
  have hm := map_mul E.rhoSig ⟨(u : (GL2TF.Quat.BHat a b)ˣ), E.U_le _ u.2⟩ ⟨y, hy⟩
  rw [Submonoid.mk_mul_mk] at hm
  exact hm

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `ρΣ(y u) = ρΣ(y) ρ(u)` for `y ∈ Σ`, `u ∈ U`. -/
theorem HeckeExt.rhoExt_mul_right (E : HeckeExt U R V ρ) {y : (GL2TF.Quat.BHat a b)ˣ} (hy : y ∈ E.Sig)
    (u : U) :
    E.rhoExt (y * (u : (GL2TF.Quat.BHat a b)ˣ)) = E.rhoExt y * ((ρ u : V ≃ₗ[R] V) : V →ₗ[R] V) := by
  rw [E.rhoExt_of_mem (E.Sig.mul_mem hy (E.U_le _ u.2)), E.rhoExt_of_mem hy, ← E.compat u]
  have hm := map_mul E.rhoSig ⟨y, hy⟩ ⟨(u : (GL2TF.Quat.BHat a b)ˣ), E.U_le _ u.2⟩
  rw [Submonoid.mk_mul_mk] at hm
  exact hm

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `U g U ⊆ Σ` when `U ⊆ Σ` and `g ∈ Σ`. -/
theorem HeckeExt.dcSet_subset (E : HeckeExt U R V ρ) {g : (GL2TF.Quat.BHat a b)ˣ} (hg : g ∈ E.Sig) :
    dcSet U g ⊆ E.Sig := by
  rintro y ⟨u, hu, v, hv, rfl⟩
  exact E.Sig.mul_mem (E.Sig.mul_mem (E.U_le u hu) hg) (E.U_le v hv)

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): the trivial extension `ρΣ = 1` of the trivial coefficients
`V = R`, `ρ = 1`, to any submonoid `Σ ⊇ U`. -/
noncomputable def HeckeExt.triv (Sig : Submonoid (GL2TF.Quat.BHat a b)ˣ) (hU : ∀ u ∈ U, u ∈ Sig) :
    HeckeExt U R R (1 : U →* (R ≃ₗ[R] R)) where
  Sig := Sig
  rhoSig := 1
  U_le := hU
  compat _ := LinearMap.ext fun _ => rfl

end Ext

section Reps

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `T` is a finite system of representatives of the left cosets
`yU ⊆ U g U` (contained in `U g U`, meeting every such coset, exactly once); the hypotheses of
`heckeT_apply_reps`. -/
abbrev IsDcReps (T : Finset (GL2TF.Quat.BHat a b)ˣ) : Prop :=
  (∀ s ∈ T, s ∈ dcSet U g) ∧
    (∀ y ∈ dcSet U g, ∃ s ∈ T,
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s) ∧
    Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑T

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): a finite system of representatives of `U g U / U` exists when
`[U : U ∩ g U g⁻¹] < ∞`. -/
theorem exists_dcReps (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    ∃ T : Finset (GL2TF.Quat.BHat a b)ˣ, IsDcReps U g T := by
  have hF := finite_cosets_dcSet U g hfin
  refine ⟨hF.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨y, hy, rfl⟩ := hF.mem_toFinset.1 hc
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U y
    rw [hh]
    exact (mul_mem_dcSet_iff_right U g h.2).2 hy
  · intro y hy
    refine ⟨Quotient.out (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U), ?_, (QuotientGroup.out_eq' _).symm⟩
    exact Finset.mem_image.2 ⟨_, hF.mem_toFinset.2 ⟨y, hy, rfl⟩, rfl⟩
  · intro s hs t ht hst
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    have hcd : c = d := by
      have h1 := hst
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    rw [hcd]

variable {U g}

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): left translation by `u ∈ U` permutes the cosets in `U g U / U`,
so `u T` is again a system of representatives. -/
theorem IsDcReps.mul_left {T : Finset (GL2TF.Quat.BHat a b)ˣ} (hT : IsDcReps U g T)
    {u : (GL2TF.Quat.BHat a b)ˣ} (hu : u ∈ U) :
    IsDcReps U g (T.image (fun x => u * x)) := by
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact (mul_mem_dcSet_iff_left U g hu).2 (h1 t ht)
  · intro y hy
    obtain ⟨t, ht, he⟩ := h2 (u⁻¹ * y) ((mul_mem_dcSet_iff_left U g (U.inv_mem hu)).2 hy)
    refine ⟨u * t, Finset.mem_image.2 ⟨t, ht, rfl⟩, ?_⟩
    rw [QuotientGroup.eq] at he ⊢
    have e : y⁻¹ * (u * t) = (u⁻¹ * y)⁻¹ * t := by group
    rw [e]
    exact he
  · intro s hs s' hs' hss'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs')
    have hm : (QuotientGroup.mk (u * t) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk (u * t') := hss'
    have hm' : (QuotientGroup.mk t : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk t' := by
      rw [QuotientGroup.eq] at hm ⊢
      have e : t⁻¹ * t' = (u * t)⁻¹ * (u * t') := by group
      rw [e]
      exact hm
    show u * t = u * t'
    rw [h3 (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht') hm']

end Reps

section Operator

variable {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V] {ρ : U →* (V ≃ₗ[R] V)}

/-- `def:s01-brandt` (`s01-brandt`, `s04-L15a`): `f(x u) = ρ(u)⁻¹ f(x)` on the Brandt module. -/
private theorem brandt_mul' {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U R V ρ)
    (x : (GL2TF.Quat.BHat a b)ˣ) (u : U) :
    f (x * (u : (GL2TF.Quat.BHat a b)ˣ)) = (ρ u)⁻¹ (f x) := by
  simpa only [map_one, one_mul] using hf 1 x u

/-- `def:s01-brandt` (`s01-brandt`, `s04-L15a`): `f(γ x) = f(x)` on the Brandt module. -/
private theorem brandt_left' {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U R V ρ)
    (γ : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) : f (iotaU a b γ * x) = f x := by
  simpa using hf γ x 1

variable (E : HeckeExt U R V ρ) (g : (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-hecke` with coefficients (`s01-hecke`, `s04-L15a`): the raw Hecke sum on functions `B̂^× → V`,
`x ↦ ∑_{c ∈ B̂^×/U, c ⊆ U g U} ρΣ(c.out) f(x c.out)`. -/
noncomputable def heckeTVRaw (f : (GL2TF.Quat.BHat a b)ˣ → V) (x : (GL2TF.Quat.BHat a b)ˣ) : V :=
  ∑ᶠ c : (GL2TF.Quat.BHat a b)ˣ ⧸ U,
    (dcSet U g).indicator (fun y => E.rhoExt y (f (x * y))) (Quotient.out c)

variable {E g}

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), well-definedness: for `f` in the Brandt module,
`heckeTVRaw f x = ∑_{s ∈ T} ρΣ(s) f(x s)` for any system `T` of representatives of `U g U / U`
(independent of the choice). -/
theorem heckeTVRaw_eq_sum (hg : g ∈ E.Sig) {f : (GL2TF.Quat.BHat a b)ˣ → V}
    (hf : f ∈ brandtModule U R V ρ) {T : Finset (GL2TF.Quat.BHat a b)ˣ} (hT : IsDcReps U g T)
    (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeTVRaw E g f x = ∑ s ∈ T, E.rhoExt s (f (x * s)) := by
  obtain ⟨h1, h2, h3⟩ := hT
  unfold heckeTVRaw
  have hsupp : Function.support (fun c : (GL2TF.Quat.BHat a b)ˣ ⧸ U =>
      (dcSet U g).indicator (fun y => E.rhoExt y (f (x * y))) (Quotient.out c)) ⊆
      ↑(T.image (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U)) := by
    intro c hc
    have hmem : (Quotient.out c : (GL2TF.Quat.BHat a b)ˣ) ∈ dcSet U g := by
      by_contra hn
      exact (Function.mem_support.mp hc) (Set.indicator_of_notMem hn _)
    obtain ⟨s, hs, hsc⟩ := h2 _ hmem
    rw [QuotientGroup.out_eq'] at hsc
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨s, hs, hsc.symm⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image h3]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U s
  have hsS : s ∈ E.Sig := E.dcSet_subset hg (h1 s hs)
  rw [hh, Set.indicator_of_mem ((mul_mem_dcSet_iff_right U g h.2).2 (h1 s hs))]
  show E.rhoExt (s * (h : (GL2TF.Quat.BHat a b)ˣ)) (f (x * (s * (h : (GL2TF.Quat.BHat a b)ˣ)))) = _
  rw [← mul_assoc, E.rhoExt_mul_right hsS h, brandt_mul' hf (x * s) h, Module.End.mul_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), well-definedness: `heckeTVRaw f` lies again in the Brandt module
(`B^×`-invariance on the left, `ρ(u)⁻¹`-equivariance on the right). -/
theorem heckeTVRaw_mem (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    {f : (GL2TF.Quat.BHat a b)ˣ → V} (hf : f ∈ brandtModule U R V ρ) :
    heckeTVRaw E g f ∈ brandtModule U R V ρ := by
  obtain ⟨T, hT⟩ := exists_dcReps U g hfin
  refine (mem_brandtModule U R V).2 fun γ x u => ?_
  have hTu := hT.mul_left u.2
  rw [heckeTVRaw_eq_sum hg hf hT (iotaU a b γ * x * u), heckeTVRaw_eq_sum hg hf hTu x,
    Finset.sum_image (mul_right_injective (u : (GL2TF.Quat.BHat a b)ˣ)).injOn, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsS : s ∈ E.Sig := E.dcSet_subset hg (hT.1 s hs)
  rw [E.rhoExt_mul_left u hsS, Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply]
  simp only [mul_assoc]
  rw [brandt_left' hf]

variable (E g)

/-- `def:s01-hecke` with coefficients (`s01-hecke`, `s04-L15a`): the Hecke operator `T_g = [U g U]` on
`brandtModule U R V ρ`, `(T_g f)(x) = ∑ᵢ ρΣ(gᵢ) f(x gᵢ)` for `U g U = ⊔ᵢ gᵢ U`, `g ∈ Σ`,
`[U : U ∩ g U g⁻¹] < ∞`. -/
noncomputable def heckeTV (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    brandtModule U R V ρ →ₗ[R] brandtModule U R V ρ where
  toFun f := ⟨heckeTVRaw E g f.1, heckeTVRaw_mem hg hfin f.2⟩
  map_add' f f' := by
    obtain ⟨T, hT⟩ := exists_dcReps U g hfin
    apply Subtype.ext
    funext x
    show heckeTVRaw E g (f + f').1 x = heckeTVRaw E g f.1 x + heckeTVRaw E g f'.1 x
    rw [heckeTVRaw_eq_sum hg (f + f').2 hT, heckeTVRaw_eq_sum hg f.2 hT, heckeTVRaw_eq_sum hg f'.2 hT,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' r f := by
    obtain ⟨T, hT⟩ := exists_dcReps U g hfin
    apply Subtype.ext
    funext x
    show heckeTVRaw E g (r • f).1 x = r • heckeTVRaw E g f.1 x
    rw [heckeTVRaw_eq_sum hg (r • f).2 hT, heckeTVRaw_eq_sum hg f.2 hT, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `(heckeTV f)(x) = heckeTVRaw f x`. -/
theorem heckeTV_apply (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f : brandtModule U R V ρ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    (heckeTV E g hg hfin f).1 x = heckeTVRaw E g f.1 x :=
  rfl

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `(T_g f)(x) = ∑_{s ∈ T} ρΣ(s) f(x s)` for any system `T` of
representatives of the left cosets in `U g U` (well-definedness). -/
theorem heckeTV_apply_reps (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    {T : Finset (GL2TF.Quat.BHat a b)ˣ} (hT : IsDcReps U g T) (f : brandtModule U R V ρ)
    (x : (GL2TF.Quat.BHat a b)ˣ) :
    (heckeTV E g hg hfin f).1 x = ∑ s ∈ T, E.rhoExt s (f.1 (x * s)) :=
  heckeTVRaw_eq_sum hg f.2 hT x

end Operator

section Triv

variable {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R]

/-- `def:s01-brandt` (`s01-brandt`, `s04-L15a`): `brandtModuleTrivEquiv f [y] = f(y)` for every representative
`y`. -/
private theorem trivEquiv_apply_mk' (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R)))
    (y : (GL2TF.Quat.BHat a b)ˣ) :
    brandtModuleTrivEquiv U R f (DoubleCoset.mk (globalUnits a b) U y) = f.1 y := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U y
  show f.1 (Quotient.out (DoubleCoset.mk (globalUnits a b) U y)) = f.1 y
  rw [he]
  have h2 := f.2 k y ⟨v, hv⟩
  simp at h2
  exact h2

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), `heckeTV_triv`: for trivial coefficients `V = R`, `ρ = 1` and an
extension with `ρΣ = 1`, the Hecke operator with coefficients is stage 1's `heckeT` under
`brandtModuleTrivEquiv : brandtModule U R R 1 ≃ₗ[R] ZXdual U R`. -/
theorem heckeTV_triv (E : HeckeExt U R R (1 : U →* (R ≃ₗ[R] R))) (hE : E.rhoSig = 1)
    (g : (GL2TF.Quat.BHat a b)ˣ) (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R))) :
    brandtModuleTrivEquiv U R (heckeTV E g hg hfin f) = heckeT U g R hfin (brandtModuleTrivEquiv U R f) := by
  obtain ⟨T, hT⟩ := exists_dcReps U g hfin
  have key : ∀ y : (GL2TF.Quat.BHat a b)ˣ,
      brandtModuleTrivEquiv U R (heckeTV E g hg hfin f) (DoubleCoset.mk (globalUnits a b) U y) =
        heckeT U g R hfin (brandtModuleTrivEquiv U R f) (DoubleCoset.mk (globalUnits a b) U y) := by
    intro y
    rw [heckeT_apply_reps U g R hfin T hT.1 hT.2.1 hT.2.2, trivEquiv_apply_mk' (heckeTV E g hg hfin f) y,
      heckeTV_apply_reps E g hg hfin hT f y]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [trivEquiv_apply_mk' f (y * s), E.rhoExt_of_mem (E.dcSet_subset hg (hT.1 s hs)), hE]
    rfl
  funext c
  have hc : DoubleCoset.mk (globalUnits a b) U (Quotient.out c) = c := Quotient.out_eq c
  have := key (Quotient.out c)
  rwa [hc] at this

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`): `heckeTV_triv` for the trivial extension `HeckeExt.triv`. -/
theorem heckeTV_triv' (Sig : Submonoid (GL2TF.Quat.BHat a b)ˣ) (hU : ∀ u ∈ U, u ∈ Sig)
    (g : (GL2TF.Quat.BHat a b)ˣ) (hg : g ∈ Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R))) :
    brandtModuleTrivEquiv U R (heckeTV (HeckeExt.triv (R := R) Sig hU) g hg hfin f) =
      heckeT U g R hfin (brandtModuleTrivEquiv U R f) :=
  heckeTV_triv _ rfl g hg hfin f

end Triv

end Langlandscape.Brandt
