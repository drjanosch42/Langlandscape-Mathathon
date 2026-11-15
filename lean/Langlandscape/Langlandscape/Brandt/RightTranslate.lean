/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.DoubleCoset
import Langlandscape.Quat.LocalEmbed

/-!
# Right translation, the Atkin–Lehner operators `Π_ℓ` (`ℓ ∣ D`) and commutation with `T_t` (S01-L11b)

`plan/staged/stage-01-quaternion-foundations.tex`: `def:s01-hecke` (`Π_ℓ`), `prop:s01-relations` (b) second half
(`Π_ℓ` does not depend on the choice of `Π_ℓ`), (c) (operators supported away from `q` commute with right translation
by `B_q^×`). Trivial coefficients (`R^X`). Convention `U_ℓ ↦ +Π_ℓ` (no sign).

## Generic right translation
* `rightConj U g` : the subgroup `g⁻¹ U g` (`x ∈ g⁻¹ U g ↔ g x g⁻¹ ∈ U`).
* `translateMap U V g : X(U) → X(V)`, `[x] ↦ [x g]`; well defined when `g⁻¹ U g ⊆ V` (`translateMap_mk`).
* `rightTranslate U g : X(U) ≃ X(g⁻¹ U g)`, `[x] ↦ [x g]`.
* `translateLin U V g R : R^{X(V)} →ₗ R^{X(U)}`, `(R_g f)[x] = f[x g]`; `rightTranslateLin U g R` for `V = g⁻¹ U g`.
  (The tex writes `R_g : Brandt(U) → Brandt(g⁻¹Ug)`, `f ↦ f(·g)`; on right-`U`-invariant `f` the function `f(·g)` is
  right-`gUg⁻¹`-invariant, so the formula `f ↦ f(·g)` goes from level `g⁻¹Ug` to level `U`, which is what is formalized.)
* `exists_heckeReps` : `U t U` has a finite system of left-coset representatives.
* `heckeT_comm_translate` : if `g` commutes with `t` and `g⁻¹ U g = V`, then `T_t ∘ R_g = R_g ∘ T_t`;
  `heckeT_comm_rightTranslate`, and `heckeT_comm_rightTranslate_localEmbed` for `g ∈ B_q^×`, `t_q = 1`
  (`prop:s01-relations` (c), second half). `relIndex_rightConj_ne_zero` transports the finiteness hypothesis.

## Atkin–Lehner operators at `ℓ ∣ D`
* `localOrder d ℓ = 𝒪_ℓ`; `mem_localOrder_iff_nrd` : for `ℓ ∣ D`, `𝒪_ℓ = {x | nrd x ∈ ℤ_ℓ}` (the import's
  `division_maximalOrder`).
* `PiEll_normalizes` : `Π 𝒪_ℓ Π⁻¹ = 𝒪_ℓ` for every `Π ∈ B_ℓ^×` (`nrd` is multiplicative); `PiEll_normalizes_units`;
  globally `conj_mem_Ohat_iff` (`localEmbed ℓ Π` normalises `Ô^×`).
* `IsMaximalAt d ℓ U` : `U` is normalised by `localEmbed ℓ (B_ℓ^×)` and contains `localEmbed ℓ (𝒪_ℓ^×)`;
  `isMaximalAt_Ohat`, `isMaximalAt_levelAt`, `isMaximalAt_U0`, `isMaximalAt_U1`, `isMaximalAt_Utower`, `.inf`.
* `PiEll d U ℓ hℓ Π R` : `(Π_ℓ f)[x] = f[x · localEmbed ℓ Π]` (`PiEll_apply`);
  `PiEll_indep` : equal for `Π, Π'` with `‖nrd Π‖ = ‖nrd Π'‖` (e.g. `v(nrd Π) = v(nrd Π') = 1`);
  `heckeT_comm_PiEll` : `Π_ℓ` commutes with every `T_t` with `t_ℓ = 1`.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open GL2TF.Quat (localLattice nrd)

/-! ### Generic right translation -/

section Translate

variable {a b : ℤ}

/-- `prop:s01-relations` (c): the conjugate subgroup `g⁻¹ U g = {x | g x g⁻¹ ∈ U}`. -/
noncomputable def rightConj (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    Subgroup (GL2TF.Quat.BHat a b)ˣ :=
  conjSub U g⁻¹

/-- `prop:s01-relations` (c) (`s01-relations`): `x ∈ g⁻¹ U g ↔ g x g⁻¹ ∈ U`. -/
theorem mem_rightConj (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    {x : (GL2TF.Quat.BHat a b)ˣ} : x ∈ rightConj U g ↔ g * x * g⁻¹ ∈ U := by
  rw [rightConj, mem_conjSub, inv_inv]

/-- `prop:s01-relations` (c) (`s01-relations`): `u ∈ U → g⁻¹ u g ∈ g⁻¹ U g`. -/
theorem conj_mem_rightConj (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    ∀ u ∈ U, g⁻¹ * u * g ∈ rightConj U g := by
  intro u hu
  rw [mem_rightConj]
  have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
  rw [e]
  exact hu

/-- `prop:s01-relations` (c) (`s01-relations`): `v ∈ g⁻¹ U g → g v g⁻¹ ∈ U`. -/
theorem conj_mem_of_mem_rightConj (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    ∀ v ∈ rightConj U g, g * v * g⁻¹ ∈ U :=
  fun _ hv => (mem_rightConj U g).1 hv

/-- `prop:s01-relations` (c): the map `X(U) → X(V)`, `[x] ↦ [x g]`, computed on the representative `c.out`; it is
well defined when `g⁻¹ U g ⊆ V` (`translateMap_mk`). -/
noncomputable def translateMap (U V : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (c : XB U) : XB V :=
  DoubleCoset.mk (globalUnits a b) V (Quotient.out c * g)

/-- `prop:s01-relations` (c) (`s01-relations`): if `g⁻¹ U g ⊆ V` then `translateMap U V g [x] = [x g]`. -/
theorem translateMap_mk {U V : Subgroup (GL2TF.Quat.BHat a b)ˣ} {g : (GL2TF.Quat.BHat a b)ˣ}
    (h : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (x : (GL2TF.Quat.BHat a b)ˣ) :
    translateMap U V g (DoubleCoset.mk (globalUnits a b) U x) =
      DoubleCoset.mk (globalUnits a b) V (x * g) := by
  obtain ⟨γ, hγ, u, hu, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
  rw [translateMap, he, DoubleCoset.eq]
  exact ⟨γ⁻¹, (globalUnits a b).inv_mem hγ, g⁻¹ * u⁻¹ * g, h _ (U.inv_mem hu), by group⟩

/-- `prop:s01-relations` (c): right translation `X(U) ≃ X(g⁻¹ U g)`, `[x] ↦ [x g]` (inverse `[y] ↦ [y g⁻¹]`). -/
noncomputable def rightTranslate (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    XB U ≃ XB (rightConj U g) where
  toFun := translateMap U (rightConj U g) g
  invFun := translateMap (rightConj U g) U g⁻¹
  left_inv c := by
    obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
    have h2 : ∀ v ∈ rightConj U g, g⁻¹⁻¹ * v * g⁻¹ ∈ U := by
      intro v hv
      rw [inv_inv]
      exact conj_mem_of_mem_rightConj U g v hv
    rw [translateMap_mk (conj_mem_rightConj U g), translateMap_mk h2, mul_inv_cancel_right]
  right_inv c := by
    obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) (rightConj U g) x = c :=
      ⟨_, DoubleCoset.out_eq' c⟩
    have h2 : ∀ v ∈ rightConj U g, g⁻¹⁻¹ * v * g⁻¹ ∈ U := by
      intro v hv
      rw [inv_inv]
      exact conj_mem_of_mem_rightConj U g v hv
    rw [translateMap_mk h2, translateMap_mk (conj_mem_rightConj U g), inv_mul_cancel_right]

/-- `prop:s01-relations` (c) (`s01-relations`): `rightTranslate U g [x] = [x g]`. -/
theorem rightTranslate_mk (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (x : (GL2TF.Quat.BHat a b)ˣ) :
    rightTranslate U g (DoubleCoset.mk (globalUnits a b) U x) =
      DoubleCoset.mk (globalUnits a b) (rightConj U g) (x * g) :=
  translateMap_mk (conj_mem_rightConj U g) x

variable (R : Type*) [CommRing R]

/-- `prop:s01-relations` (c): pull-back along `translateMap`, `(R_g f)[x] = f[x g]`, from `R^{X(V)}` to `R^{X(U)}`. -/
noncomputable def translateLin (U V : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    ZXdual V R →ₗ[R] ZXdual U R :=
  LinearMap.funLeft R R (translateMap U V g)

/-- `prop:s01-relations` (c) (`s01-relations`): `(R_g f)[x] = f[x g]` when `g⁻¹ U g ⊆ V`. -/
theorem translateLin_mk {U V : Subgroup (GL2TF.Quat.BHat a b)ˣ} {g : (GL2TF.Quat.BHat a b)ˣ}
    (h : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (f : ZXdual V R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    translateLin R U V g f (DoubleCoset.mk (globalUnits a b) U x) =
      f (DoubleCoset.mk (globalUnits a b) V (x * g)) := by
  rw [translateLin, LinearMap.funLeft_apply, translateMap_mk h]

/-- `prop:s01-relations` (c): `R_g : R^{X(g⁻¹Ug)} →ₗ R^{X(U)}`, `f ↦ f(· g)` (pull-back along `rightTranslate`). -/
noncomputable def rightTranslateLin (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) :
    ZXdual (rightConj U g) R →ₗ[R] ZXdual U R :=
  translateLin R U (rightConj U g) g

/-- `prop:s01-relations` (c) (`s01-relations`): `R_g f = f ∘ rightTranslate U g`. -/
theorem rightTranslateLin_apply (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (f : ZXdual (rightConj U g) R) (c : XB U) :
    rightTranslateLin R U g f c = f (rightTranslate U g c) :=
  rfl

/-- `prop:s01-relations` (c) (`s01-relations`): `(R_g f)[x] = f[x g]`. -/
theorem rightTranslateLin_mk (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
    (f : ZXdual (rightConj U g) R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    rightTranslateLin R U g f (DoubleCoset.mk (globalUnits a b) U x) =
      f (DoubleCoset.mk (globalUnits a b) (rightConj U g) (x * g)) :=
  translateLin_mk R (conj_mem_rightConj U g) f x

/-- `def:s01-hecke` (`s01-hecke`): `U t U` has a finite system `S` of representatives of its left cosets `yU`
(`S ⊆ U t U`, every coset met exactly once), when `[U : U ∩ t U t⁻¹] < ∞`. -/
theorem exists_heckeReps (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (t : (GL2TF.Quat.BHat a b)ˣ)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    ∃ S : Finset (GL2TF.Quat.BHat a b)ˣ, (∀ s ∈ S, s ∈ dcSet U t) ∧
      (∀ y ∈ dcSet U t, ∃ s ∈ S,
        (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s) ∧
      Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S := by
  classical
  have hQf := finite_cosets_dcSet U t hfin
  refine ⟨hQf.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨y, hy, rfl⟩ := hQf.mem_toFinset.1 hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U y
    rw [hk]
    exact (mul_mem_dcSet_iff_right U t k.2).2 hy
  · intro y hy
    refine ⟨Quotient.out (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U),
      Finset.mem_image.2 ⟨_, hQf.mem_toFinset.2 ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    rw [QuotientGroup.out_eq']
  · intro s1 hs1 s2 hs2 h
    obtain ⟨q1, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs1)
    obtain ⟨q2, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs2)
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]

/-- `prop:s01-relations` (c) (`s01-relations`): a group identity used for commuting conjugations. -/
theorem conj_conj_of_commute {G : Type*} [Group G] {g t : G} (hgt : Commute g t) (x : G) :
    g * (t⁻¹ * x * t) * g⁻¹ = t⁻¹ * (g * x * g⁻¹) * t := by
  calc g * (t⁻¹ * x * t) * g⁻¹ = (g * t⁻¹) * x * (t * g⁻¹) := by group
    _ = (t⁻¹ * g) * x * (g⁻¹ * t) := by rw [hgt.inv_right.eq, ← hgt.inv_left.eq]
    _ = t⁻¹ * (g * x * g⁻¹) * t := by group

/-- `prop:s01-relations` (c) (`s01-relations`): if `g` commutes with `t` and `[U : U ∩ t U t⁻¹] < ∞`, then also
`[g⁻¹Ug : g⁻¹Ug ∩ t (g⁻¹Ug) t⁻¹] < ∞` (conjugation by `g` carries one pair to the other). -/
theorem relIndex_rightConj_ne_zero (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g t : (GL2TF.Quat.BHat a b)ˣ)
    (hgt : Commute g t) (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    (rightConj U g ⊓ conjSub (rightConj U g) t).relIndex (rightConj U g) ≠ 0 := by
  let φ : (GL2TF.Quat.BHat a b)ˣ →* (GL2TF.Quat.BHat a b)ˣ :=
    MonoidHom.mk' (fun x => g * x * g⁻¹) (fun x y => by group)
  have e1 : rightConj U g = U.comap φ := by
    ext x
    exact mem_rightConj U g
  have e2 : rightConj U g ⊓ conjSub (rightConj U g) t = (U ⊓ conjSub U t).comap φ := by
    ext x
    rw [Subgroup.mem_inf, mem_rightConj, mem_conjSub, mem_rightConj]
    show _ ↔ g * x * g⁻¹ ∈ U ∧ t⁻¹ * (g * x * g⁻¹) * t ∈ U
    rw [conj_conj_of_commute hgt x]
  rw [e2, e1]
  exact Subgroup.relIndex_comap_ne_zero φ hfin

/-- `prop:s01-relations` (c) (`s01-relations`): let `g⁻¹ U g = V` (in the form `g⁻¹ U g ⊆ V`, `g V g⁻¹ ⊆ U`) and let
`g` commute with `t`. Then `T_t ∘ R_g = R_g ∘ T_t`, where `R_g f = f(· g)`: if `U t U = ⊔ sU` then
`V t V = ⊔ (g⁻¹ s g) V`, and both sides send `f` to `[x] ↦ ∑_s f[x s g]`. -/
theorem heckeT_comm_translate (U V : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g t : (GL2TF.Quat.BHat a b)ˣ)
    (hUV : ∀ u ∈ U, g⁻¹ * u * g ∈ V) (hVU : ∀ v ∈ V, g * v * g⁻¹ ∈ U) (hgt : Commute g t)
    (hfinU : (U ⊓ conjSub U t).relIndex U ≠ 0) (hfinV : (V ⊓ conjSub V t).relIndex V ≠ 0) :
    (heckeT U t R hfinU).comp (translateLin R U V g) =
      (translateLin R U V g).comp (heckeT V t R hfinV) := by
  classical
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U t hfinU
  have hc : g * t * g⁻¹ = t := by rw [hgt.eq, mul_inv_cancel_right]
  have hc' : g⁻¹ * t * g = t := by rw [mul_assoc, ← hgt.eq, inv_mul_cancel_left]
  have hconj : Set.InjOn (fun s => g⁻¹ * s * g) ↑S := by
    intro s1 _ s2 _ e
    have e' : g⁻¹ * s1 * g = g⁻¹ * s2 * g := e
    calc s1 = g * (g⁻¹ * s1 * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * s2 * g) * g⁻¹ := by rw [e']
      _ = s2 := by group
  have hS' : ∀ s ∈ S.image (fun s => g⁻¹ * s * g), s ∈ dcSet V t := by
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hs'
    obtain ⟨u, hu, v, hv, e⟩ := (mem_dcSet U t).1 (hS s hs)
    refine (mem_dcSet V t).2 ⟨g⁻¹ * u * g, hUV u hu, g⁻¹ * v * g, hUV v hv, ?_⟩
    show g⁻¹ * s * g = g⁻¹ * u * g * t * (g⁻¹ * v * g)
    rw [e]
    calc g⁻¹ * (u * t * v) * g = g⁻¹ * u * (g * t * g⁻¹) * v * g := by rw [hc]; group
      _ = g⁻¹ * u * g * t * (g⁻¹ * v * g) := by group
  have hcov' : ∀ y ∈ dcSet V t, ∃ s ∈ S.image (fun s => g⁻¹ * s * g),
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ V) = QuotientGroup.mk s := by
    intro y hy
    obtain ⟨v1, hv1, v2, hv2, e⟩ := (mem_dcSet V t).1 hy
    have hmem : g * y * g⁻¹ ∈ dcSet U t := by
      refine (mem_dcSet U t).2 ⟨g * v1 * g⁻¹, hVU v1 hv1, g * v2 * g⁻¹, hVU v2 hv2, ?_⟩
      rw [e]
      calc g * (v1 * t * v2) * g⁻¹ = g * v1 * (g⁻¹ * t * g) * v2 * g⁻¹ := by rw [hc']; group
        _ = g * v1 * g⁻¹ * t * (g * v2 * g⁻¹) := by group
    obtain ⟨s, hs, hys⟩ := hcov _ hmem
    refine ⟨g⁻¹ * s * g, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [QuotientGroup.eq] at hys ⊢
    have e2 : y⁻¹ * (g⁻¹ * s * g) = g⁻¹ * ((g * y * g⁻¹)⁻¹ * s) * g := by group
    rw [e2]
    exact hUV _ hys
  have hinj' : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ V)
      ↑(S.image (fun s => g⁻¹ * s * g)) := by
    intro s1' hs1' s2' hs2' e
    obtain ⟨s1, hs1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs1')
    obtain ⟨s2, hs2, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs2')
    have e1 : (QuotientGroup.mk (g⁻¹ * s1 * g) : (GL2TF.Quat.BHat a b)ˣ ⧸ V) =
        QuotientGroup.mk (g⁻¹ * s2 * g) := e
    have e' : (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s2 := by
      rw [QuotientGroup.eq] at e1 ⊢
      have h2 := hVU _ e1
      have e3 : g * ((g⁻¹ * s1 * g)⁻¹ * (g⁻¹ * s2 * g)) * g⁻¹ = s1⁻¹ * s2 := by group
      rw [e3] at h2
      exact h2
    show g⁻¹ * s1 * g = g⁻¹ * s2 * g
    rw [hinj (Finset.mem_coe.2 hs1) (Finset.mem_coe.2 hs2) e']
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, heckeT_apply_reps U t R hfinU S hS hcov hinj,
    translateLin_mk R hUV, heckeT_apply_reps V t R hfinV _ hS' hcov' hinj', Finset.sum_image hconj]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [translateLin_mk R hUV]
  have e : x * g * (g⁻¹ * s * g) = x * s * g := by group
  rw [e]

/-- `prop:s01-relations` (c), second half (`s01-relations`): for `g` commuting with `t`, right translation
`R_g = f ↦ f(· g)` intertwines `T_t` at level `g⁻¹ U g` with `T_t` at level `U`. -/
theorem heckeT_comm_rightTranslate (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g t : (GL2TF.Quat.BHat a b)ˣ)
    (hgt : Commute g t) (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    (heckeT U t R hfin).comp (rightTranslateLin R U g) =
      (rightTranslateLin R U g).comp
        (heckeT (rightConj U g) t R (relIndex_rightConj_ne_zero U g t hgt hfin)) :=
  heckeT_comm_translate R U (rightConj U g) g t (conj_mem_rightConj U g) (conj_mem_of_mem_rightConj U g) hgt
    hfin _

/-- `prop:s01-relations` (c), second half (`s01-relations`): operators `T_t` supported away from `q` (`t_q = 1`)
commute with right translation by `g = localEmbed q y ∈ B_q^×`. -/
theorem heckeT_comm_rightTranslate_localEmbed (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) {q : ℕ} [Fact q.Prime]
    (y : (QuatAlg ℚ_[q] a b)ˣ) (t : (GL2TF.Quat.BHat a b)ˣ) (ht : localProjUnits a b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    (heckeT U t R hfin).comp (rightTranslateLin R U (localEmbed a b q y)) =
      (rightTranslateLin R U (localEmbed a b q y)).comp
        (heckeT (rightConj U (localEmbed a b q y)) t R
          (relIndex_rightConj_ne_zero U _ t
            (commute_localEmbed_of_commute y (by rw [ht]; exact Commute.one_right y)) hfin)) :=
  heckeT_comm_rightTranslate R U _ t
    (commute_localEmbed_of_commute y (by rw [ht]; exact Commute.one_right y)) hfin

end Translate

/-! ### The local maximal order at `ℓ ∣ D` -/

section LocalOrder

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `def:s01-hecke` (`s01-hecke`): `nrd` is multiplicative on `B_ℓ`. -/
theorem nrd_mul_local {a b : ℤ} (x y : QuatAlg ℚ_[ℓ] a b) : nrd (x * y) = nrd x * nrd y :=
  by simp [GL2TF.Quat.nrd]; ring

/-- `def:s01-hecke` (`s01-hecke`): `nrd 1 = 1` on `B_ℓ`. -/
theorem nrd_one_local {a b : ℤ} : nrd (1 : QuatAlg ℚ_[ℓ] a b) = 1 := by
  simp [GL2TF.Quat.nrd]

/-- `def:s01-hecke` (`s01-hecke`): `nrd x · nrd x⁻¹ = 1` for `x ∈ B_ℓ^×`. -/
theorem nrd_units_mul_inv_local {a b : ℤ} (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    nrd (x : QuatAlg ℚ_[ℓ] a b) * nrd ((x⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b) = 1 := by
  rw [← nrd_mul_local, Units.mul_inv, nrd_one_local]

/-- `def:s01-hecke` (`s01-hecke`): `‖nrd x⁻¹‖ · ‖nrd x‖ = 1` for `x ∈ B_ℓ^×`. -/
theorem norm_nrd_inv_mul_local {a b : ℤ} (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    ‖nrd ((x⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b)‖ * ‖nrd (x : QuatAlg ℚ_[ℓ] a b)‖ = 1 := by
  rw [← norm_mul, mul_comm, nrd_units_mul_inv_local, norm_one]

/-- `def:s01-hecke` (`s01-hecke`): `nrd (Π z Π⁻¹) = nrd z`. -/
theorem nrd_conj_local {a b : ℤ} (P : (QuatAlg ℚ_[ℓ] a b)ˣ) (z : QuatAlg ℚ_[ℓ] a b) :
    nrd ((P : QuatAlg ℚ_[ℓ] a b) * z * ((P⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b)) = nrd z := by
  rw [nrd_mul_local, nrd_mul_local]
  calc nrd (P : QuatAlg ℚ_[ℓ] a b) * nrd z * nrd ((P⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b) =
      nrd z * (nrd (P : QuatAlg ℚ_[ℓ] a b) * nrd ((P⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b)) := by
        ring
    _ = nrd z := by rw [nrd_units_mul_inv_local, mul_one]

/-- `def:s01-hecke`: the local order `𝒪_ℓ = O ⊗ ℤ_ℓ ⊆ B_ℓ` of the chosen maximal order. -/
noncomputable abbrev localOrder (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] : Submodule ℤ_[ℓ] (QuatAlg ℚ_[ℓ] d.a d.b) :=
  localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra)

variable {d : DefiniteData}

/-- `def:s01-hecke` (`s01-hecke`): for `ℓ ∣ D`, `𝒪_ℓ = {x ∈ B_ℓ | nrd x ∈ ℤ_ℓ}` (the import's
`division_maximalOrder`). -/
theorem mem_localOrder_iff_nrd (hℓ : ℓ ∣ d.D) (z : QuatAlg ℚ_[ℓ] d.a d.b) :
    z ∈ localOrder d ℓ ↔ nrd z ∈ PadicInt.subring ℓ :=
  Set.ext_iff.mp ((GL2TF.Quat.division_maximalOrder d.hD ℓ hℓ).2.2 d.O) z

/-- `def:s01-hecke`, `prop:s01-relations` (b) (`s01-hecke`): for `ℓ ∣ D` and every `Π ∈ B_ℓ^×`,
`Π 𝒪_ℓ Π⁻¹ = 𝒪_ℓ` (`𝒪_ℓ` is the set of elements of integral reduced norm). -/
theorem PiEll_normalizes (hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (z : QuatAlg ℚ_[ℓ] d.a d.b) :
    (P : QuatAlg ℚ_[ℓ] d.a d.b) * z * ((P⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈
      localOrder d ℓ ↔ z ∈ localOrder d ℓ := by
  rw [mem_localOrder_iff_nrd hℓ, mem_localOrder_iff_nrd hℓ, nrd_conj_local]

/-- `def:s01-hecke` (`s01-hecke`): for `ℓ ∣ D`, `Π 𝒪_ℓ^× Π⁻¹ = 𝒪_ℓ^×`, elementwise. -/
theorem PiEll_normalizes_units (hℓ : ℓ ∣ d.D) (P x : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    (((P * x * P⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ ∧
      (((P * x * P⁻¹)⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ) ↔
    ((x : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ ∧
      ((x⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ) := by
  have e : (P * x * P⁻¹)⁻¹ = P * x⁻¹ * P⁻¹ := by group
  rw [e]
  simp only [Units.val_mul]
  rw [PiEll_normalizes hℓ P, PiEll_normalizes hℓ P]

/-- `def:s01-hecke` (`s01-hecke`): a group identity: if `E` commutes with `u W⁻¹`, then
`E u E⁻¹ = (u W⁻¹) (E W E⁻¹)`. -/
theorem conj_eq_of_commute {G : Type*} [Group G] (E W u : G) (hc : Commute E (u * W⁻¹)) :
    E * u * E⁻¹ = u * W⁻¹ * (E * W * E⁻¹) := by
  calc E * u * E⁻¹ = E * (u * W⁻¹) * W * E⁻¹ := by group
    _ = u * W⁻¹ * E * W * E⁻¹ := by rw [hc.eq]
    _ = u * W⁻¹ * (E * W * E⁻¹) := by group

/-- `def:s01-hecke` (`s01-hecke`): for `ℓ ∣ D` and `Π ∈ B_ℓ^×`, conjugation by `localEmbed ℓ Π` preserves `Ô^×`. -/
theorem conj_mem_Ohat (hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) {u : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hu : u ∈ d.Ohat) :
    localEmbed d.a d.b ℓ P * u * (localEmbed d.a d.b ℓ P)⁻¹ ∈ d.Ohat := by
  obtain ⟨y, hy⟩ : ∃ y, localProjUnits d.a d.b ℓ u = y := ⟨_, rfl⟩
  have hy1 : (y : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ := by
    rw [← hy]
    exact localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hu.1 ℓ
  have hy2 : ((y⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ := by
    rw [← hy, ← map_inv]
    exact localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hu.2 ℓ
  have hw : localEmbed d.a d.b ℓ y ∈ d.Ohat :=
    (localEmbed_mem_orderCompletionUnits_iff d.O.1 y).2 ⟨hy1, hy2⟩
  have hu' : u * (localEmbed d.a d.b ℓ y)⁻¹ ∈ d.Ohat := mul_mem hu (inv_mem hw)
  have hc : Commute (localEmbed d.a d.b ℓ P) (u * (localEmbed d.a d.b ℓ y)⁻¹) := by
    refine commute_localEmbed_of_commute P ?_
    rw [map_mul, map_inv, localProjUnits_localEmbed, hy, mul_inv_cancel]
    exact Commute.one_right P
  have hPy : localEmbed d.a d.b ℓ P * localEmbed d.a d.b ℓ y * (localEmbed d.a d.b ℓ P)⁻¹ ∈ d.Ohat := by
    have e : localEmbed d.a d.b ℓ (P * y * P⁻¹) =
        localEmbed d.a d.b ℓ P * localEmbed d.a d.b ℓ y * (localEmbed d.a d.b ℓ P)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← e]
    exact (localEmbed_mem_orderCompletionUnits_iff d.O.1 _).2 ((PiEll_normalizes_units hℓ P y).2 ⟨hy1, hy2⟩)
  rw [conj_eq_of_commute _ _ u hc]
  exact mul_mem hu' hPy

/-- `def:s01-hecke` (`s01-hecke`): for `ℓ ∣ D`, `localEmbed ℓ Π` normalises `Ô^×`. -/
theorem conj_mem_Ohat_iff (hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (u : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    localEmbed d.a d.b ℓ P * u * (localEmbed d.a d.b ℓ P)⁻¹ ∈ d.Ohat ↔ u ∈ d.Ohat := by
  refine ⟨fun h => ?_, conj_mem_Ohat hℓ P⟩
  have h2 := conj_mem_Ohat hℓ P⁻¹ h
  rw [map_inv, inv_inv] at h2
  have e : (localEmbed d.a d.b ℓ P)⁻¹ * (localEmbed d.a d.b ℓ P * u * (localEmbed d.a d.b ℓ P)⁻¹) *
      localEmbed d.a d.b ℓ P = u := by group
  rw [e] at h2
  exact h2

end LocalOrder

/-! ### Levels maximal at `ℓ ∣ D` and the operators `Π_ℓ` -/

section PiEll

/-- `def:s01-hecke`: `U` is maximal at the prime `ℓ`: it is normalised by `localEmbed ℓ (B_ℓ^×)` and contains
`localEmbed ℓ (𝒪_ℓ^×)`. All levels of S01-L3c are maximal at every `ℓ ∣ D` (`isMaximalAt_levelAt`). -/
structure IsMaximalAt (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) :
    Prop where
  /-- `localEmbed ℓ (B_ℓ^×)` normalises `U`. -/
  conj_mem : ∀ (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) {u : (GL2TF.Quat.BHat d.a d.b)ˣ}, u ∈ U →
    localEmbed d.a d.b ℓ P * u * (localEmbed d.a d.b ℓ P)⁻¹ ∈ U
  /-- `localEmbed ℓ (𝒪_ℓ^×) ⊆ U`. -/
  localEmbed_mem : ∀ w : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ, (w : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ →
    ((w⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ → localEmbed d.a d.b ℓ w ∈ U

variable {d : DefiniteData} {ℓ : ℕ} [Fact ℓ.Prime]

/-- `def:s01-hecke` (`s01-hecke`): for `U` maximal at `ℓ`, `(localEmbed ℓ Π)⁻¹ U localEmbed ℓ Π ⊆ U`. -/
theorem IsMaximalAt.inv_conj_mem {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    ∀ u ∈ U, (localEmbed d.a d.b ℓ P)⁻¹ * u * localEmbed d.a d.b ℓ P ∈ U := by
  intro u hu
  have h := hU.conj_mem P⁻¹ hu
  rw [map_inv, inv_inv] at h
  exact h

/-- `def:s01-hecke` (`s01-hecke`): `Ô^×` is maximal at every `ℓ ∣ D`. -/
theorem isMaximalAt_Ohat (hℓ : ℓ ∣ d.D) : IsMaximalAt d ℓ d.Ohat :=
  ⟨fun P {_} hu => conj_mem_Ohat hℓ P hu,
    fun w h1 h2 => (localEmbed_mem_orderCompletionUnits_iff d.O.1 w).2 ⟨h1, h2⟩⟩

/-- `def:s01-hecke` (`s01-hecke`): maximality at `ℓ` is stable under `⊓`. -/
theorem IsMaximalAt.inf {U V : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (hV : IsMaximalAt d ℓ V) : IsMaximalAt d ℓ (U ⊓ V) :=
  ⟨fun P {_} hu => Subgroup.mem_inf.2 ⟨hU.conj_mem P (Subgroup.mem_inf.1 hu).1,
      hV.conj_mem P (Subgroup.mem_inf.1 hu).2⟩,
    fun w h1 h2 => Subgroup.mem_inf.2 ⟨hU.localEmbed_mem w h1 h2, hV.localEmbed_mem w h1 h2⟩⟩

/-- `def:s01-hecke` (`s01-hecke`): the generic level `levelAt d N hN K` (`(N, D) = 1`) is maximal at every
`ℓ ∣ D`: its local conditions sit at primes `q ∣ N`, `q ≠ ℓ`, where `localEmbed ℓ` has component `1`. -/
theorem isMaximalAt_levelAt (hℓ : ℓ ∣ d.D) {N : ℕ} {hN : N.Coprime d.D}
    {K : (q : ℕ) → [Fact q.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[q])} :
    IsMaximalAt d ℓ (d.levelAt N hN K) := by
  have hne : ∀ (q : ℕ), ¬ q ∣ d.D → q ≠ ℓ := fun q hD h => hD (by rw [h]; exact hℓ)
  refine ⟨fun P {u} hu => ?_, fun w h1 h2 => ?_⟩
  · rw [DefiniteData.mem_levelAt_iff] at hu ⊢
    refine ⟨conj_mem_Ohat hℓ P hu.1, fun q _ hq hD => ?_⟩
    rw [map_mul, map_mul, map_inv, localComponent_localEmbed_of_ne P (hne q hD), one_mul, inv_one, mul_one]
    exact hu.2 q hq hD
  · rw [DefiniteData.mem_levelAt_iff]
    refine ⟨(localEmbed_mem_orderCompletionUnits_iff d.O.1 w).2 ⟨h1, h2⟩, fun q _ hq hD => ?_⟩
    rw [localComponent_localEmbed_of_ne w (hne q hD)]
    exact one_mem _

/-- `def:s01-hecke` (`s01-hecke`): `U_0(N)` is maximal at every `ℓ ∣ D`. -/
theorem isMaximalAt_U0 (hℓ : ℓ ∣ d.D) {N : ℕ} {hN : N.Coprime d.D} : IsMaximalAt d ℓ (d.U0 N hN) :=
  isMaximalAt_levelAt hℓ

/-- `def:s01-hecke` (`s01-hecke`): `U_1(N)` is maximal at every `ℓ ∣ D`. -/
theorem isMaximalAt_U1 (hℓ : ℓ ∣ d.D) {N : ℕ} {hN : N.Coprime d.D} : IsMaximalAt d ℓ (d.U1 N hN) :=
  isMaximalAt_levelAt hℓ

/-- `def:s01-hecke` (`s01-hecke`): the tower levels `U_s = U_1(M p^s)` are maximal at every `ℓ ∣ D`. -/
theorem isMaximalAt_Utower (hℓ : ℓ ∣ d.D) {M p s : ℕ} {hN : (M * p ^ s).Coprime d.D} :
    IsMaximalAt d ℓ (d.Utower M p s hN) :=
  isMaximalAt_levelAt (hN := hN) hℓ

variable (R : Type*) [CommRing R]

/-- `def:s01-hecke`: the Atkin–Lehner operator `Π_ℓ` at `ℓ ∣ D` on `R^{X(U)}`,
`(Π_ℓ f)[x] = f[x · localEmbed ℓ Π]` (no sign, `U_ℓ ↦ +Π_ℓ`), for `Π ∈ B_ℓ^×` (meant: `v(nrd Π) = 1`); for `U`
maximal at `ℓ` it is well defined (`PiEll_apply`) and independent of `Π` up to `‖nrd Π‖` (`PiEll_indep`). -/
noncomputable def PiEll (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : ZXdual U R →ₗ[R] ZXdual U R :=
  translateLin R U U (localEmbed d.a d.b ℓ P)

/-- `def:s01-hecke` (`s01-hecke`): `(Π_ℓ f)[x] = f[x · localEmbed ℓ Π]` for `U` maximal at `ℓ`. -/
theorem PiEll_apply (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (f : ZXdual U R) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    PiEll R d U ℓ hℓ P f (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      f (DoubleCoset.mk (globalUnits d.a d.b) U (x * localEmbed d.a d.b ℓ P)) :=
  translateLin_mk R (hU.inv_conj_mem P) f x

/-- `prop:s01-relations` (b), second half (`s01-relations`): `Π_ℓ` does not depend on the choice of `Π`: any two
`Π, Π' ∈ B_ℓ^×` with `‖nrd Π‖ = ‖nrd Π'‖` (e.g. `v(nrd Π) = v(nrd Π') = 1`) give the same operator on `R^{X(U)}`, for
`U` maximal at `ℓ ∣ D` (`Π⁻¹Π' ∈ 𝒪_ℓ^×` since `𝒪_ℓ = {nrd ∈ ℤ_ℓ}`). -/
theorem PiEll_indep (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P P' : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)
    (hPP' : ‖nrd (P : QuatAlg ℚ_[ℓ] d.a d.b)‖ = ‖nrd (P' : QuatAlg ℚ_[ℓ] d.a d.b)‖) :
    PiEll R d U ℓ hℓ P = PiEll R d U ℓ hℓ P' := by
  have n1 : ‖nrd (((P⁻¹ * P' : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)) : QuatAlg ℚ_[ℓ] d.a d.b)‖ = 1 := by
    rw [Units.val_mul, nrd_mul_local, norm_mul, ← hPP', norm_nrd_inv_mul_local]
  have n2 : ‖nrd (((P'⁻¹ * P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)) : QuatAlg ℚ_[ℓ] d.a d.b)‖ = 1 := by
    rw [Units.val_mul, nrd_mul_local, norm_mul, hPP', norm_nrd_inv_mul_local]
  have h1 : (((P⁻¹ * P' : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ :=
    (mem_localOrder_iff_nrd hℓ _).2 ((PadicInt.mem_subring_iff ℓ).2 n1.le)
  have h2 : ((((P⁻¹ * P')⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)) : QuatAlg ℚ_[ℓ] d.a d.b) ∈ localOrder d ℓ := by
    have e : (P⁻¹ * P')⁻¹ = P'⁻¹ * P := by group
    rw [e]
    exact (mem_localOrder_iff_nrd hℓ _).2 ((PadicInt.mem_subring_iff ℓ).2 n2.le)
  have hw : localEmbed d.a d.b ℓ (P⁻¹ * P') ∈ U := hU.localEmbed_mem _ h1 h2
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [PiEll_apply R hℓ hU, PiEll_apply R hℓ hU]
  have e : localEmbed d.a d.b ℓ P' = localEmbed d.a d.b ℓ P * localEmbed d.a d.b ℓ (P⁻¹ * P') := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  rw [e]
  congr 1
  rw [DoubleCoset.eq]
  exact ⟨1, one_mem _, localEmbed d.a d.b ℓ (P⁻¹ * P'), hw, by group⟩

/-- `prop:s01-relations` (c) (`s01-relations`): `Π_ℓ` (`ℓ ∣ D`, `U` maximal at `ℓ`) commutes with every Hecke
operator `T_t` whose element has trivial `ℓ`-component (`t_ℓ = 1`). -/
theorem heckeT_comm_PiEll (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (t : (GL2TF.Quat.BHat d.a d.b)ˣ) (ht : localProjUnits d.a d.b ℓ t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    (heckeT U t R hfin).comp (PiEll R d U ℓ hℓ P) = (PiEll R d U ℓ hℓ P).comp (heckeT U t R hfin) :=
  heckeT_comm_translate R U U _ t (hU.inv_conj_mem P) (fun _ hv => hU.conj_mem P hv)
    (commute_localEmbed_of_commute P (by rw [ht]; exact Commute.one_right P)) hfin hfin

end PiEll

end Langlandscape.Brandt
