/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.BrandtGraph
import Langlandscape.Tree.HeckeLevel

/-!
# Hecke operators on the Brandt graph — S02-L7b

Tex labels: `prop:s02-quot`(c) (`s_j^*`, `s_{j*}` commute with the Hecke operators), `if:s01-hecke`.

Let `U` be a `q`-level (`IsQLevel d q hq U`), `U_0(q)U = U0q U`, and `t` supported away from `q`
(`localProjUnits d.a d.b q t = 1`). Then:

* `heckeT_comm_s0Pull` : `T_t ∘ s_0^* = s_0^* ∘ T_t` (`s_0 = π`: `L7a` with `K = GL₂(ℤ_q)`, `K' = Iw_q`);
* `s1Pull_eq` : `s_1^* = R_α ∘ π_{s1Level}^*` (`R_α = rightTranslateLin`, `α = alphaElt`), and
  `heckeT_comm_s1Pull` : `T_t ∘ s_1^* = s_1^* ∘ T_t` (`L7a` at the level `s1Level = α⁻¹ (U_0(q)U) α`, whose
  `q`-factor is `K' = α⁻¹ Iw_q α`, and `S01` `heckeT_comm_rightTranslate` for `α`, which commutes with `t`);
* `heckeTHom_comm_s0Push`, `heckeTHom_comm_s1Push` : the transposed statements on `R[X]`;
* corollaries `Tl_comm_s1Pull`, `Sl_comm_s1Pull`, `diamond_comm_s1Pull`, `varpi_comm_s1Pull`.

Status: *formalized*.
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt
open scoped Classical

section Aux

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-quot`(c) (`s02-quot`): a `q`-level is `U = U ⊓ ι_q⁻¹ GL₂(ℤ_q)`. -/
private theorem s02_U_eq_inf (hU : IsQLevel d q hq U) :
    U = U ⊓ (GL2Zl q).comap (localComponent d q hq) := by
  ext u
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  exact ⟨fun h => ⟨h, localComponent_mem_of_isQLevel hU h⟩, fun h => h.1⟩

/-- `prop:s02-quot`(c) (`s02-quot`): `U_0(q)U = U ⊓ ι_q⁻¹ Iw_q` for a `q`-level `U`. -/
private theorem s02_U0q_eq_inf (hU : IsQLevel d q hq U) :
    d.U0q q (coprime_of_not_dvd hq) U = U ⊓ (Iw q).comap (localComponent d q hq) := by
  ext u
  rw [mem_U0q_iff_of_isQLevel hU, Subgroup.mem_inf, Subgroup.mem_comap]

/-- `prop:s02-quot`(c) (`s02-quot`): `Iw_q ≤ GL₂(ℤ_q)`. -/
private theorem s02_Iw_le : Iw q ≤ GL2Zl q := fun _ hx => Local.K0_le_GL2Zl 1 hx

/-- `prop:s02-quot`(c) (`s02-quot`): the `q`-factor `α⁻¹ Iw_q α = {k | α k α⁻¹ ∈ Iw_q}` of `s1Level`. -/
private noncomputable def s02K1 (q : ℕ) [Fact q.Prime] : Subgroup (GL (Fin 2) ℚ_[q]) :=
  (Iw q).comap (MulAut.conj (alphaq q)).toMonoidHom

/-- `prop:s02-quot`(c) (`s02-quot`): `k ∈ α⁻¹ Iw_q α ↔ α k α⁻¹ ∈ Iw_q`. -/
private theorem mem_s02K1 {k : GL (Fin 2) ℚ_[q]} : k ∈ s02K1 q ↔ alphaq q * k * (alphaq q)⁻¹ ∈ Iw q := by
  first
  | exact Iff.rfl
  | simp only [s02K1, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-- `prop:s02-quot`(c) (`s02-quot`): `α⁻¹ Iw_q α ≤ GL₂(ℤ_q)`. -/
private theorem s02K1_le : s02K1 q ≤ GL2Zl q := by
  intro k hk
  have h := alphaq_inv_conj_mem_GL2Zl (mem_s02K1.1 hk)
  have e : (alphaq q)⁻¹ * (alphaq q * k * (alphaq q)⁻¹) * alphaq q = k := by group
  rwa [e] at h

/-- `prop:s02-quot`(c) (`s02-quot`): `α` commutes with `t` when `t_q = 1`. -/
private theorem commute_alphaElt_of_away {t : (BHat d.a d.b)ˣ} (ht : localProjUnits d.a d.b q t = 1) :
    Commute (alphaElt d q hq) t := by
  unfold alphaElt
  rw [localEmbedGL_apply]
  exact commute_localEmbed_of_commute _ (by rw [ht]; exact Commute.one_right _)

/-- `prop:s02-quot`(c) (`s02-quot`): `ι_q(α)` has `q`-component `α_q`. -/
private theorem localComponent_alphaElt : localComponent d q hq (alphaElt d q hq) = alphaq q :=
  localComponent_localEmbedGL _

/-- `prop:s02-quot`(c) (`s02-quot`): `s1Level = U ⊓ ι_q⁻¹(α⁻¹ Iw_q α)` for a `q`-level `U`. -/
private theorem s02_s1Level_eq (hU : IsQLevel d q hq U) :
    s1Level d q hq U = U ⊓ (s02K1 q).comap (localComponent d q hq) := by
  have hlc : ∀ x : (BHat d.a d.b)ˣ, localComponent d q hq (alphaElt d q hq * x * (alphaElt d q hq)⁻¹) =
      alphaq q * localComponent d q hq x * (alphaq q)⁻¹ := by
    intro x
    rw [map_mul, map_mul, map_inv, localComponent_alphaElt]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_s02K1]
  constructor
  · intro hx
    have hxU := s1Level_le hU hx
    have h := (mem_U0q_iff_of_isQLevel hU).1 ((Brandt.mem_rightConj _ _).1 hx)
    refine ⟨hxU, ?_⟩
    have h2 := h.2
    rwa [hlc] at h2
  · rintro ⟨hxU, hxK⟩
    refine (Brandt.mem_rightConj _ _).2 ((mem_U0q_iff_of_isQLevel hU).2 ⟨?_, ?_⟩)
    · have hc : Commute (awayAt d q hq x) (alphaElt d q hq) :=
        commute_awayAt_localEmbedGL (hp := hq) x (alphaq q)
      have hαa : alphaElt d q hq * awayAt d q hq x = awayAt d q hq x * alphaElt d q hq := hc.symm.eq
      have he : alphaElt d q hq * localEmbedGL d q hq (localComponent d q hq x) * (alphaElt d q hq)⁻¹ =
          localEmbedGL d q hq (alphaq q * localComponent d q hq x * (alphaq q)⁻¹) := by
        unfold alphaElt
        simp only [map_mul, map_inv]
      have hx2 : alphaElt d q hq * x * (alphaElt d q hq)⁻¹ =
          awayAt d q hq x * localEmbedGL d q hq (alphaq q * localComponent d q hq x * (alphaq q)⁻¹) := by
        rw [← he]
        calc alphaElt d q hq * x * (alphaElt d q hq)⁻¹
            = alphaElt d q hq * (awayAt d q hq x * localEmbedGL d q hq (localComponent d q hq x)) *
                (alphaElt d q hq)⁻¹ := by rw [awayAt_mul_localEmbedGL]
          _ = (alphaElt d q hq * awayAt d q hq x) * localEmbedGL d q hq (localComponent d q hq x) *
                (alphaElt d q hq)⁻¹ := by group
          _ = (awayAt d q hq x * alphaElt d q hq) * localEmbedGL d q hq (localComponent d q hq x) *
                (alphaElt d q hq)⁻¹ := by rw [hαa]
          _ = awayAt d q hq x * (alphaElt d q hq * localEmbedGL d q hq (localComponent d q hq x) *
                (alphaElt d q hq)⁻¹) := by group
      rw [hx2]
      exact mul_mem (awayAt_mem_of_isQLevel hU hxU) (localEmbedGL_mem_of_isQLevel hU (s02_Iw_le hxK))
    · rw [hlc]
      exact hxK

/-- `prop:s02-quot`(c) (`s02-quot`): `s_1^* = R_α ∘ π^*`, where `π : X(α⁻¹ (U_0(q)U) α) → X(U)` is the level map
and `R_α` the right translation `f ↦ f(· α)`. -/
theorem s1Pull_eq (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) :
    s1Pull d q hq U R =
      (rightTranslateLin R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)).comp
        (levelPull (s1Level d q hq U) U R) := by
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  have h1 := levelPull_mk R (s1Level_le hU) f (x * alphaElt d q hq)
  have h2 := rightTranslateLin_mk R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)
    (levelPull (s1Level d q hq U) U R f) x
  rw [s1Pull_apply, s1_mk hU]
  exact h1.symm.trans h2.symm

end Aux

section Main

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-quot`(c) (`s02-quot`): `T_t ∘ s_0^* = s_0^* ∘ T_t` on `R^{X(U)}` for `t` supported away from `q`
(`s_0 = π : X(U_0(q)U) → X(U)`; `U = U ⊓ ι_q⁻¹ GL₂(ℤ_q)`, `U_0(q)U = U ⊓ ι_q⁻¹ Iw_q`). -/
theorem heckeT_comm_s0Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) :
    (heckeT (d.U0q q (coprime_of_not_dvd hq) U) t R hfin').comp (s0Pull d q hq U R) =
      (s0Pull d q hq U R).comp (heckeT U t R hfin) :=
  heckeT_comm_levelPull_of_eq R (V := U) (K := GL2Zl q) (K' := Iw q) (isInvariantAt_of_isQLevel hU)
    s02_Iw_le le_rfl (s02_U_eq_inf hU) (s02_U0q_eq_inf hU) t ht hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`): `T_t ∘ s_1^* = s_1^* ∘ T_t` on `R^{X(U)}` for `t` supported away from `q`
(`s_1^* = R_α ∘ π^*`, `α` commutes with `t`, and `π^*` commutes with `T_t` at the level `s1Level`). -/
theorem heckeT_comm_s1Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) :
    (heckeT (d.U0q q (coprime_of_not_dvd hq) U) t R hfin').comp (s1Pull d q hq U R) =
      (s1Pull d q hq U R).comp (heckeT U t R hfin) := by
  have hα : Commute (alphaElt d q hq) t := commute_alphaElt_of_away ht
  have hfin1 : (s1Level d q hq U ⊓ conjSub (s1Level d q hq U) t).relIndex (s1Level d q hq U) ≠ 0 :=
    relIndex_rightConj_ne_zero _ _ t hα hfin'
  have hT : (heckeT (d.U0q q (coprime_of_not_dvd hq) U) t R hfin').comp
      (rightTranslateLin R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)) =
      (rightTranslateLin R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)).comp
        (heckeT (s1Level d q hq U) t R hfin1) :=
    heckeT_comm_rightTranslate R _ _ t hα hfin'
  have hL : (heckeT (s1Level d q hq U) t R hfin1).comp (levelPull (s1Level d q hq U) U R) =
      (levelPull (s1Level d q hq U) U R).comp (heckeT U t R hfin) :=
    heckeT_comm_levelPull_of_eq R (V := U) (K := GL2Zl q) (K' := s02K1 q) (isInvariantAt_of_isQLevel hU)
      s02K1_le le_rfl (s02_U_eq_inf hU) (s02_s1Level_eq hU) t ht hfin hfin1
  have key : ∀ g, s1Pull d q hq U R g =
      rightTranslateLin R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)
        (levelPull (s1Level d q hq U) U R g) :=
    fun g => LinearMap.congr_fun (s1Pull_eq R hU) g
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, key, key]
  exact (LinearMap.congr_fun hT _).trans
    (congrArg (fun g => rightTranslateLin R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq) g)
      (LinearMap.congr_fun hL f))

/-- `prop:s02-quot`(c) (`s02-quot`): `s_{0*} ∘ T_t^t = T_t^t ∘ s_{0*}` on `R[X]` (finite class sets). -/
theorem heckeTHom_comm_s0Push (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0)
    [Finite (XB U)] [Finite (XB (d.U0q q (coprime_of_not_dvd hq) U))] :
    (s0Push d q hq U R).comp (heckeTHom (d.U0q q (coprime_of_not_dvd hq) U) t R hfin') =
      (heckeTHom U t R hfin).comp (s0Push d q hq U R) :=
  heckeTHom_comm_levelPush_of_eq R (V := U) (K := GL2Zl q) (K' := Iw q) (isInvariantAt_of_isQLevel hU)
    s02_Iw_le le_rfl (s02_U_eq_inf hU) (s02_U0q_eq_inf hU) t ht hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`): `⟨s_{1*} a, f⟩ = ⟨a, s_1^* f⟩` for the evaluation pairing. -/
theorem evalPairing_s1Push (R : Type*) [CommRing R] (x : ZX (d.U0q q (coprime_of_not_dvd hq) U) R)
    (f : ZXdual U R) :
    evalPairing U R (s1Push d q hq U R x) f =
      evalPairing (d.U0q q (coprime_of_not_dvd hq) U) R x (s1Pull d q hq U R f) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]
  | single c r => rw [s1Push_single, evalPairing_single, evalPairing_single, s1Pull_apply]

/-- `prop:s02-quot`(c) (`s02-quot`): `s_{1*} ∘ T_t^t = T_t^t ∘ s_{1*}` on `R[X]` (finite class sets), the
transpose of `heckeT_comm_s1Pull`. -/
theorem heckeTHom_comm_s1Push (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) (t : (BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓ conjSub (d.U0q q (coprime_of_not_dvd hq) U) t).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0)
    [Finite (XB U)] [Finite (XB (d.U0q q (coprime_of_not_dvd hq) U))] :
    (s1Push d q hq U R).comp (heckeTHom (d.U0q q (coprime_of_not_dvd hq) U) t R hfin') =
      (heckeTHom U t R hfin).comp (s1Push d q hq U R) := by
  have hcomm := heckeT_comm_s1Pull R hU t ht hfin hfin'
  refine LinearMap.ext fun x => Finsupp.ext fun c => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    ← evalPairing_pi_single U R (s1Push d q hq U R (heckeTHom _ t R hfin' x)) c,
    ← evalPairing_pi_single U R (heckeTHom U t R hfin (s1Push d q hq U R x)) c,
    evalPairing_s1Push, heckeTHom_transpose, heckeTHom_transpose, evalPairing_s1Push]
  exact congrArg (evalPairing (d.U0q q (coprime_of_not_dvd hq) U) R x)
    (LinearMap.congr_fun hcomm (Pi.single c (1 : R)))

end Main

section Named

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `prop:s02-quot`(c) (`s02-quot`): `T_ℓ` (`ℓ ≠ q`, `ℓ ∤ D`) commutes with `s_1^*`. -/
theorem Tl_comm_s1Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D) (hℓq : ℓ ≠ q)
    (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓
      conjSub (d.U0q q (coprime_of_not_dvd hq) U) (elemT d ℓ hℓ)).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) :
    (Tl d (d.U0q q (coprime_of_not_dvd hq) U) ℓ hℓ R hfin').comp (s1Pull d q hq U R) =
      (s1Pull d q hq U R).comp (Tl d U ℓ hℓ R hfin) :=
  heckeT_comm_s1Pull R hU _
    (localProjUnits_localEmbedGL_of_ne (d := d) (p := ℓ) (hp := hℓ) _ hℓq.symm) hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`): `S_ℓ` (`ℓ ≠ q`, `ℓ ∤ D`) commutes with `s_1^*`. -/
theorem Sl_comm_s1Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D) (hℓq : ℓ ≠ q)
    (hfin : (U ⊓ conjSub U (elemS d ℓ hℓ)).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓
      conjSub (d.U0q q (coprime_of_not_dvd hq) U) (elemS d ℓ hℓ)).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) :
    (Sl d (d.U0q q (coprime_of_not_dvd hq) U) ℓ hℓ R hfin').comp (s1Pull d q hq U R) =
      (s1Pull d q hq U R).comp (Sl d U ℓ hℓ R hfin) :=
  heckeT_comm_s1Pull R hU _
    (localProjUnits_localEmbedGL_of_ne (d := d) (p := ℓ) (hp := hℓ) _ hℓq.symm) hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`): the local diamond operator at `ℓ ≠ q` (`ℓ ∤ D`) commutes with `s_1^*`. -/
theorem diamond_comm_s1Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D) (hℓq : ℓ ≠ q) (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U)
    (hn' : ∀ x ∈ d.U0q q (coprime_of_not_dvd hq) U,
      (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.U0q q (coprime_of_not_dvd hq) U) :
    (diamond d (d.U0q q (coprime_of_not_dvd hq) U) ℓ hℓ R t hn').comp (s1Pull d q hq U R) =
      (s1Pull d q hq U R).comp (diamond d U ℓ hℓ R t hn) :=
  heckeT_comm_s1Pull R hU _
    (localProjUnits_localEmbedGL_of_ne (d := d) (p := ℓ) (hp := hℓ) _ hℓq.symm)
    (relIndex_ne_zero_of_normalizing U _ hn) (relIndex_ne_zero_of_normalizing _ _ hn')

/-- `prop:s02-quot`(c) (`s02-quot`): `U_p`-type operator `[U t U]` with `t = ι_p⁻¹ diag(p, 1)` (`p ≠ q`,
`p ∤ D`) commutes with `s_1^*` (replaces the ill-typed `Up_comm_s1Pull`). -/
theorem varpi_comm_s1Pull (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ d.D) (hpq : p ≠ q)
    (hfin : (U ⊓ conjSub U (localEmbedGL d p hp (varpiDiag p))).relIndex U ≠ 0)
    (hfin' : (d.U0q q (coprime_of_not_dvd hq) U ⊓
      conjSub (d.U0q q (coprime_of_not_dvd hq) U) (localEmbedGL d p hp (varpiDiag p))).relIndex
      (d.U0q q (coprime_of_not_dvd hq) U) ≠ 0) :
    (heckeT (d.U0q q (coprime_of_not_dvd hq) U) (localEmbedGL d p hp (varpiDiag p)) R hfin').comp
        (s1Pull d q hq U R) =
      (s1Pull d q hq U R).comp (heckeT U (localEmbedGL d p hp (varpiDiag p)) R hfin) :=
  heckeT_comm_s1Pull R hU _
    (localProjUnits_localEmbedGL_of_ne (d := d) (p := p) (hp := hp) _ hpq.symm) hfin hfin'

end Named

end Langlandscape.Tree
