/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Langlandscape.Ordinary.EKills
import Langlandscape.Ordinary.Fitting
import Langlandscape.Ordinary.ControlAbstract
import Langlandscape.Ordinary.KppTower
import Langlandscape.Brandt.UpAdjoint
import Langlandscape.Hyp.PadicOrdDecomp

/-!
# Instantiation on Brandt towers (S04-L10)

`mathematics/chapters/s04/ordinary.tex`, `lem:s04-ekills`(a),(d); `mathematics/chapters/s04/control.tex`,
`lem:s04-hida`(c),(d), `thm:s04-control`(a) (finite-level part). Specialisation `𝒪_E = ℤ_p`, `E = ℚ_p`.

* `Xs`, `Xs'`: the finite sets `X_s = X_B(U_s)`, `X'_s = X_B(U'_s)` (`U_s = Utower M p s`, `U'_s = UtowerP`).
* ekills (a) at Brandt level: `deg_comp_UpHom` (`deg ∘ U_p = p • deg`), `ekillsA_tower`
  (`e ℤ_[p][X_s]⁰ = e ℤ_[p][X_s]`, the **stage-05 input**, formalized modulo `Hyp.PadicOrdDecomp`) and the unconditional
  `ekillsA_tower_zmod` over `ZMod (p ^ m)`.
* ekills (d) at Brandt level: `brandtPairing_eq_deltaPairing` (`w_x = 1` for `s ≥ 1`, `p ≥ 5`),
  `perfect_ordPart_pairing_tower` (`e × e* → R` perfect, `U_p^* = UpStar` of S04-L5), with `ℤ_[p]` and
  `ZMod (p ^ m)` forms.
* control (`lem:s04-hida`(d), finite part of `thm:s04-control`(a)): for three levels `U₂ ≤ U₁ ≤ U₀` with `p`-components
  `·`, `Kpp p s`, `K1 p s` (S04-L9 `IsUpLevel`) the pushforward `π_* : e R[X(U₂)] → e R[X(U₀)]` is
  **surjective** and its kernel is `e R[X(U₂)] ∩ ker (π''_* : R[X(U₂)] → R[X(U₁)])` (`ord_control_of_levels`,
  `ker_ordPush`; the quotient isomorphism `e R[X(U₂)] ⧸ (e ∩ ker π''_*) ≃ e R[X(U₀)]` is not stated as a `def`). The
  identification of `e ∩ ker π''_*` with `I · e R[X_{s+1}]` (`I` the augmentation ideal of `ker(Δ_{s+1} → Δ_s)`), hence
  the tensor form `e R[X_{s+1}] ⊗_{R[Δ_{s+1}]} R[Δ_s] ≃ e R[X_s]`, is proved in the tex (`lem:s04-hida`(c),(d)) and
  **not formalized** (S04-L9 `piPP_eq_iff` is a statement about sets only). Instances: the tower `UU_s` (`ord_control_finite`,
  `ord_control_finite_zmod`) **and** `U0q q UU_s` (`ord_control_finite_U0q`, `ord_control_finite_U0q_zmod`),
  as D-lim needs.

Status: the `ℤ_[p]` statements are *formalized modulo `Hyp.PadicOrdDecomp`* (argument `hdec`; for `E = ℚ_p`); the
`hdec` argument is discharged in `Ordinary/TowerUncond.lean` (`<name>_uncond`, S04-L3). The `ZMod (p ^ m)` statements are *formalized* unconditionally (S04-L2 Fitting).
-/

set_option autoImplicit false

open Langlandscape.Local Langlandscape.Quat Langlandscape.Brandt

namespace Langlandscape.Ordinary

open scoped Classical

noncomputable section

/-! ### The finite sets of the tower -/

section Sets

variable (d : DefiniteData) (M p s : ℕ) [Fact p.Prime]

/-- `lem:s04-hida` (`s04-hida`), notation: `X_s = X_B(U_s)`, `U_s = U_1(M p^s)` (`Utower`). -/
abbrev Xs (hN : (M * p ^ s).Coprime d.D) : Type :=
  XB (d.Utower M p s hN)

/-- `lem:s04-hida` (`s04-hida`), notation: `X'_s = X_B(U'_s)`, `U'_s = UtowerP` (`Kpp p s` at `p`). -/
abbrev Xs' (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) : Type :=
  XB (UtowerP d M p s hN hp)

end Sets

/-! ### Separatedness of the coefficient rings, finiteness -/

/-- `lem:s04-ekills`(d) (`s04-ekills`): `ℤ_[p]` is `p`-adically separated, `⋂ₖ pᵏ ℤ_p = 0` (the `hsep` of
`perfect_ordPart_pairing`). -/
theorem padicInt_sep (p : ℕ) [Fact p.Prime] (r : ℤ_[p])
    (h : ∀ k : ℕ, ∃ c : ℤ_[p], r = (p : ℤ_[p]) ^ k * c) : r = 0 := by
  by_contra hr
  obtain ⟨c, hc⟩ := h (r.valuation + 1)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hr (by rw [hc, mul_zero])
  have hv := congrArg PadicInt.valuation hc
  rw [PadicInt.valuation_p_pow_mul _ _ hc0] at hv
  omega

/-- `lem:s04-ekills`(d) (`s04-ekills`): `ZMod (p ^ m)` is `p`-adically separated (`p ^ m = 0`). -/
theorem zmodPow_sep (p m : ℕ) (r : ZMod (p ^ m))
    (h : ∀ k : ℕ, ∃ c : ZMod (p ^ m), r = ((p : ℕ) : ZMod (p ^ m)) ^ k * c) : r = 0 := by
  obtain ⟨c, hc⟩ := h m
  rw [hc, natCast_pow_eq_zero, zero_mul]

/-- `def:s04-e` (`s04-e`), finite case: `ZMod (p ^ m)` is finite for a prime `p`. -/
theorem finite_zmodPow (p m : ℕ) [Fact p.Prime] : Finite (ZMod (p ^ m)) := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  infer_instance

/-- `def:s04-e` (`s04-e`), finite case: `ZMod (p ^ m)[X]` is finite for finite `X`. -/
theorem finite_finsupp_zmodPow (X : Type*) [Finite X] (p m : ℕ) [Fact p.Prime] :
    Finite (X →₀ ZMod (p ^ m)) := by
  have := finite_zmodPow p m
  exact Finite.of_equiv _ Finsupp.equivFunOnFinite.symm

/-! ### Pushforwards between levels -/

section Push

variable {d : DefiniteData}

/-- `lem:s04-hida`(d) (`s04-hida`): `π ∘ π'' = π` for `U₂ ≤ U₁ ≤ U₀` on double cosets. -/
theorem levelMap_levelMap {U₂ U₁ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (h21 : U₂ ≤ U₁)
    (h10 : U₁ ≤ U₀) (c : XB U₂) : levelMap U₁ U₀ (levelMap U₂ U₁ c) = levelMap U₂ U₀ c := by
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U₂ x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [levelMap_mk h21, levelMap_mk h10, levelMap_mk (h21.trans h10)]

variable (R : Type*) [CommRing R]

/-- `lem:s04-hida`(d) (`s04-hida`): `π_* = π'_* ∘ π''_*` for `U₂ ≤ U₁ ≤ U₀`. -/
theorem pushforward_comp_pushforward {U₂ U₁ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (h21 : U₂ ≤ U₁)
    (h10 : U₁ ≤ U₀) : pushforward U₁ U₀ R ∘ₗ pushforward U₂ U₁ R = pushforward U₂ U₀ R := by
  apply Finsupp.lhom_ext
  intro c r
  rw [LinearMap.comp_apply, pushforward_single, pushforward_single, pushforward_single,
    levelMap_levelMap h21 h10]

/-- `lem:s04-hida`(c) (`s04-hida`): `π_* : R[X(U')] → R[X(U)]` is surjective for `U' ≤ U`. -/
theorem pushforward_surjective {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hle : U' ≤ U) :
    Function.Surjective (pushforward U' U R) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := R) (levelMap_surjective hle) y
  exact ⟨x, hx⟩

end Push

/-! ### `lem:s04-ekills`(a) at Brandt level -/

section EKillsA

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s04-ekills`(a) (`s04-ekills`): on `R[X_s]`, `deg ∘ U_p = p • deg` (`U_p [x] = ∑_{j < p} [x ϖ_j]`). -/
theorem deg_comp_UpHom (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    (deg (Xs d M p s hN) R).comp (UpHom d M p s hN hp hM hpM hs R) = (p : R) • deg (Xs d M p s hN) R := by
  apply Finsupp.lhom_ext
  intro c r
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, UpHom_single hM hpM hs, map_sum, LinearMap.smul_apply]
  simp only [deg_single, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]

/-- `lem:s04-ekills`(a), `if:s04-ekills`(a) at Brandt level (`s04-ekills`), **stage-05 export**: for `s ≥ 1`,
`e ℤ_[p][X_s]⁰ = e ℤ_[p][X_s]`, i.e. the ordinary part of `U_p` on the degree-zero part `ker deg` is the whole ordinary
part of `U_p` on `ℤ_[p][X_s]`. For `E = ℚ_p`; formalized modulo `Hyp.PadicOrdDecomp`. -/
theorem ekillsA_tower (hdec : Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])))
          (UpKer (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (p : ℤ_[p]) (deg_comp_UpHom ℤ_[p] hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]) :=
  ordPart_ker_deg _ _ (deg_comp_UpHom ℤ_[p] hM hpM hs)
    (hdec (ZX (d.Utower M p s hN) ℤ_[p]) (UpHom d M p s hN hp hM hpM hs ℤ_[p]))
    (hdec ℤ_[p] (LinearMap.lsmul ℤ_[p] ℤ_[p] (p : ℤ_[p])))

/-- `lem:s04-ekills`(a) (`s04-ekills`), unconditional `ZMod (p ^ m)` form of `ekillsA_tower`:
`e (ℤ/p^m)[X_s]⁰ = e (ℤ/p^m)[X_s]`. -/
theorem ekillsA_tower_zmod (m : ℕ) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) (ZMod (p ^ m)))).subtype
        (ordPart (R := ZMod (p ^ m)) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) (ZMod (p ^ m)))))
          (UpKer (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) ((p : ℕ) : ZMod (p ^ m))
            (deg_comp_UpHom (ZMod (p ^ m)) hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) := by
  have := finite_zmodPow p m
  have := finite_finsupp_zmodPow (XB (d.Utower M p s hN)) p m
  exact ordPart_ker_deg _ _ (deg_comp_UpHom (ZMod (p ^ m)) hM hpM hs)
    (hasOrdDecomp_zmodPow p m (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))))
    (hasOrdDecomp_zmodPow p m (LinearMap.lsmul (ZMod (p ^ m)) (ZMod (p ^ m)) ((p : ℕ) : ZMod (p ^ m))))

end EKillsA

/-! ### `lem:s04-ekills`(d) at Brandt level -/

section EKillsD

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s04-ekills`(d) (`s04-ekills`), N2: at `U_s`, `s ≥ 1`, `p ≥ 5`, all weights are `w_x = 1`
(`Γ_x` trivial, `Gam_eq_bot_of_le_U1`). -/
theorem wx_Utower_eq_one (hp : ¬ p ∣ d.D) (h5 : 5 ≤ p) (hM : M ≠ 0) (hs : 1 ≤ s)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : wx (d.Utower M p s hN) x = 1 := by
  have hpD : p.Coprime d.D := (Fact.out : p.Prime).coprime_iff_not_dvd.2 hp
  have h := Gam_eq_bot_of_le_U1 d (Fact.out : p.Prime) h5 hpD
    (DefiniteData.Utower_le_U1p hs hM (Fact.out : p.Prime).ne_zero hN hpD) x
  simp only [wx, h, bot_inf_eq, Subgroup.card_bot, Nat.div_one]

/-- `lem:s04-ekills`(d), `def:s01-pairing` (`s04-ekills`): if all weights are `1`, the Brandt pairing is the pairing
`⟨[x],[y]⟩ = δ_{xy}` of S04-L4. -/
theorem brandtPairing_eq_deltaPairing {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (R : Type*) [CommRing R]
    (hw : ∀ c : XB U, wx U (Quotient.out c) = 1) : brandtPairing U R = deltaPairing (XB U) R := by
  refine Finsupp.lhom_ext fun c r => Finsupp.lhom_ext fun c' t => ?_
  rw [brandtPairing_single_single, deltaPairing_single_left, hw c, Finsupp.single_apply]
  by_cases h : c = c'
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

/-- `lem:s04-ekills`(d) (`s04-ekills`) at Brandt level, any `p`-adically separated coefficient ring: for `s ≥ 1`,
`p ≥ 5`, the pairing `⟨[x],[y]⟩ = δ_{xy}` on `R[X_s]` restricts to a perfect pairing
`e R[X_s] × e* R[X_s] → R`, `e` for `U_p`
(`UpHom`) and `e*` for its adjoint `U_p^*` (`UpStar`, S04-L5). -/
theorem perfect_ordPart_pairing_tower {R : Type*} [CommRing R] (h5 : 5 ≤ p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (hsep : ∀ r : R, (∀ k : ℕ, ∃ c : R, r = (p : R) ^ k * c) → r = 0)
    (hdec : HasOrdDecomp (p : R) (UpHom d M p s hN hp hM hpM hs R))
    (hdect : HasOrdDecomp (p : R) (UpStar d M p s hN hp hM hpM hs R)) :
    ((deltaPairing (Xs d M p s hN) R).domRestrict₁₂ (ordPart (UpHom d M p s hN hp hM hpM hs R))
      (ordPart (UpStar d M p s hN hp hM hpM hs R))).IsPerfPair :=
  perfect_ordPart_pairing (p : R) hsep _ _ (fun x y => by
      have h := brandtPairing_UpHom_UpStar (R := R) (hp := hp) hM hpM hs x y
      rwa [brandtPairing_eq_deltaPairing (U := d.Utower M p s hN) R
        (fun c => wx_Utower_eq_one hp h5 hM hs _)] at h)
    hdec hdect

/-- `lem:s04-ekills`(d) (`s04-ekills`) over `ℤ_[p]` (for `E = ℚ_p`): `e ℤ_[p][X_s] × e* ℤ_[p][X_s] → ℤ_[p]` is perfect.
Formalized modulo `Hyp.PadicOrdDecomp`. -/
theorem perfect_ordPart_pairing_tower_padic (hdec : Hyp.PadicOrdDecomp p) (h5 : 5 ≤ p) (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ((deltaPairing (Xs d M p s hN) ℤ_[p]).domRestrict₁₂ (ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]))
      (ordPart (UpStar d M p s hN hp hM hpM hs ℤ_[p]))).IsPerfPair :=
  perfect_ordPart_pairing_tower h5 hM hpM hs (padicInt_sep p)
    (hdec (ZX (d.Utower M p s hN) ℤ_[p]) (UpHom d M p s hN hp hM hpM hs ℤ_[p]))
    (hdec (ZX (d.Utower M p s hN) ℤ_[p]) (UpStar d M p s hN hp hM hpM hs ℤ_[p]))

/-- `lem:s04-ekills`(d) (`s04-ekills`), unconditional `ZMod (p ^ m)` form: `e × e* → ℤ/p^m` is perfect on `X_s`. -/
theorem perfect_ordPart_pairing_tower_zmod (m : ℕ) (h5 : 5 ≤ p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ((deltaPairing (Xs d M p s hN) (ZMod (p ^ m))).domRestrict₁₂
      (ordPart (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))))
      (ordPart (UpStar d M p s hN hp hM hpM hs (ZMod (p ^ m))))).IsPerfPair := by
  have := finite_finsupp_zmodPow (XB (d.Utower M p s hN)) p m
  exact perfect_ordPart_pairing_tower h5 hM hpM hs (zmodPow_sep p m)
    (hasOrdDecomp_zmodPow p m (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))))
    (hasOrdDecomp_zmodPow p m (UpStar d M p s hN hp hM hpM hs (ZMod (p ^ m))))

end EKillsD

/-! ### Control for three levels `U₂ ≤ U₁ ≤ U₀` (`lem:s04-hida`(c),(d)) -/

section Control

variable {d : DefiniteData} {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `lem:s04-hida`(d), `thm:s04-control`(a) (`s04-control`): the restriction `e R[X(U₂)] → e R[X(U₀)]` of the
pushforward `π_*` (`U₂ ≤ U₀`, both levels where `U_p` is defined, `IsUpLevel`). -/
def ordPush {U₂ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K₂ K₀ : Subgroup (GL (Fin 2) ℚ_[p])}
    (h₂ : IsUpLevel d p hp U₂ K₂) (h₀ : IsUpLevel d p hp U₀ K₀) (h20 : U₂ ≤ U₀) (R : Type*) [CommRing R]
    [Finite (XB U₂)] [Finite (XB U₀)] :
    ordPart (UpAt U₂ h₂ R) →ₗ[R] ordPart (UpAt U₀ h₀ R) :=
  ordRestrict (pushforward U₂ U₀ R) (UpAt_comm_pushforward h₂ h₀ h20)

/-- `lem:s04-hida`(d) (`s04-control`): `ordPush x = π_* x`. -/
theorem ordPush_apply {U₂ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K₂ K₀ : Subgroup (GL (Fin 2) ℚ_[p])}
    (h₂ : IsUpLevel d p hp U₂ K₂) (h₀ : IsUpLevel d p hp U₀ K₀) (h20 : U₂ ≤ U₀) (R : Type*) [CommRing R]
    [Finite (XB U₂)] [Finite (XB U₀)] (x : ordPart (UpAt U₂ h₂ R)) :
    (ordPush h₂ h₀ h20 R x : ZX U₀ R) = pushforward U₂ U₀ R x :=
  rfl

/-- `lem:s04-hida`(c),(d), `thm:s04-control`(a) (`s04-control`), abstract three-level form: let `U₂ ≤ U₁ ≤ U₀`,
`U₁` with `p`-component `Kpp p s`, `U₀` with `p`-component `K1 p s` and the same away part (`haway`), `s ≥ 1`, and let
`U_p` have
ordinary decompositions at the three levels. Then `π_* : e R[X(U₂)] → e R[X(U₀)]` is surjective, and `π_* x = 0` iff
`π''_* x = 0` (`π'' : X(U₂) → X(U₁)`); i.e. `e π_*` induces `e R[X(U₂)] ⧸ (e ∩ ker π''_*) ≃ e R[X(U₀)]`. -/
theorem ord_control_of_levels {R : Type*} [CommRing R] {U₂ U₁ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    {K₂ : Subgroup (GL (Fin 2) ℚ_[p])} {s : ℕ} (hs : 1 ≤ s) (h₂ : IsUpLevel d p hp U₂ K₂)
    (h₁ : IsUpLevel d p hp U₁ (Kpp p s)) (h₀ : IsUpLevel d p hp U₀ (K1 p s)) (h21 : U₂ ≤ U₁) (h10 : U₁ ≤ U₀)
    (haway : ∀ u ∈ U₀, awayAt d p hp u ∈ U₁) [Finite (XB U₂)] [Finite (XB U₁)] [Finite (XB U₀)]
    (hd₂ : HasOrdDecomp (p : R) (UpAt U₂ h₂ R)) (hd₁ : HasOrdDecomp (p : R) (UpAt U₁ h₁ R))
    (hd₀ : HasOrdDecomp (p : R) (UpAt U₀ h₀ R)) :
    Function.Surjective (ordPush h₂ h₀ (h21.trans h10) R) ∧
      ∀ x : ordPart (UpAt U₂ h₂ R),
        ordPush h₂ h₀ (h21.trans h10) R x = 0 ↔ pushforward U₂ U₁ R (x : ZX U₂ R) = 0 := by
  let E := ordPartEquivOfSurjective (p : R) (pushforward U₁ U₀ R) (pushforward_surjective R h10)
    (UpAt_comm_pushforward h₁ h₀ h10)
    (fun x hx => UpAt_ker_pushforward_eq_zero hs h₁ h₀ h10 haway x hx) hd₁ hd₀
  have hE : ∀ z : ordPart (UpAt U₁ h₁ R), ((E z : ordPart (UpAt U₀ h₀ R)) : ZX U₀ R) =
      pushforward U₁ U₀ R (z : ZX U₁ R) := fun _ => rfl
  have hcomp : ∀ w : ZX U₂ R, pushforward U₁ U₀ R (pushforward U₂ U₁ R w) = pushforward U₂ U₀ R w :=
    fun w => by rw [← LinearMap.comp_apply, pushforward_comp_pushforward R h21 h10]
  refine ⟨fun y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hz : ((E.symm y : ordPart (UpAt U₁ h₁ R)) : ZX U₁ R) ∈
        (ordPart (UpAt U₂ h₂ R)).map (pushforward U₂ U₁ R) := by
      rw [map_ordPart_eq_of_surjective (p : R) (pushforward U₂ U₁ R) (pushforward_surjective R h21)
        (UpAt_comm_pushforward h₂ h₁ h21) hd₂ hd₁]
      exact (E.symm y).2
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.1 hz
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [ordPush_apply, ← hcomp, hwz, ← hE, E.apply_symm_apply]
  · have hmem : pushforward U₂ U₁ R (x : ZX U₂ R) ∈ ordPart (UpAt U₁ h₁ R) :=
      ordPart_map _ (UpAt_comm_pushforward h₂ h₁ h21) x.2
    have hx' : pushforward U₁ U₀ R (pushforward U₂ U₁ R (x : ZX U₂ R)) = 0 := by
      rw [hcomp, ← ordPush_apply h₂ h₀ (h21.trans h10) R x, hx, Submodule.coe_zero]
    have h0 : E ⟨_, hmem⟩ = E 0 := by
      apply Subtype.ext
      rw [map_zero, hE]
      exact hx'
    exact congrArg Subtype.val (E.injective h0)
  · apply Subtype.ext
    rw [ordPush_apply, ← hcomp, hx, map_zero, Submodule.coe_zero]

/-- `lem:s04-hida`(d), `thm:s04-control`(a) (`s04-control`), abstract three-level form: the kernel of
`e π_* : e R[X(U₂)] → e R[X(U₀)]` is `e R[X(U₂)] ∩ ker π''_*` (hypotheses of `ord_control_of_levels`). -/
theorem ker_ordPush {R : Type*} [CommRing R] {U₂ U₁ U₀ : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    {K₂ : Subgroup (GL (Fin 2) ℚ_[p])} {s : ℕ} (hs : 1 ≤ s) (h₂ : IsUpLevel d p hp U₂ K₂)
    (h₁ : IsUpLevel d p hp U₁ (Kpp p s)) (h₀ : IsUpLevel d p hp U₀ (K1 p s)) (h21 : U₂ ≤ U₁) (h10 : U₁ ≤ U₀)
    (haway : ∀ u ∈ U₀, awayAt d p hp u ∈ U₁) [Finite (XB U₂)] [Finite (XB U₁)] [Finite (XB U₀)]
    (hd₂ : HasOrdDecomp (p : R) (UpAt U₂ h₂ R)) (hd₁ : HasOrdDecomp (p : R) (UpAt U₁ h₁ R))
    (hd₀ : HasOrdDecomp (p : R) (UpAt U₀ h₀ R)) :
    LinearMap.ker (ordPush h₂ h₀ (h21.trans h10) R) =
      Submodule.comap (ordPart (UpAt U₂ h₂ R)).subtype (LinearMap.ker (pushforward U₂ U₁ R)) :=
  Submodule.ext fun x => by
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply]
    exact (ord_control_of_levels hs h₂ h₁ h₀ h21 h10 haway hd₂ hd₁ hd₀).2 x

end Control

/-! ### Control on the tower `UU_s` and on `U0q q UU_s` -/

section TowerControl

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `lem:s04-hida` (`s04-hida`): `U_s` and `U'_s` have the same away part: `awayAt u ∈ U'_s` for `u ∈ U_s`. -/
theorem awayAt_mem_UtowerP_of_mem {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    {u : (GL2TF.Quat.BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) : awayAt d p hp u ∈ UtowerP d M p s hN hp := by
  refine mem_UtowerP_iff.2 ⟨(((isUpLevel_Utower (hp := hp) hM hpM hs).factor u).1 hu).1, ?_⟩
  rw [localComponent_awayAt]
  exact one_mem _

/-- `lem:s04-hida` (`s04-hida`): `U_0(q) ·` is monotone. -/
theorem U0q_le_U0q {q : ℕ} (hq : q.Coprime d.D) {U V : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (h : U ≤ V) :
    d.U0q q hq U ≤ d.U0q q hq V := fun _ hu =>
  Subgroup.mem_inf.2 ⟨h (Subgroup.mem_inf.1 hu).1, (Subgroup.mem_inf.1 hu).2⟩

/-- `lem:s04-hida` (`s04-hida`): `U_0(q) U_s` and `U_0(q) U'_s` have the same away part at `p`. -/
theorem awayAt_mem_U0q_UtowerP_of_mem {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) {q : ℕ} (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors) {u : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hu : u ∈ d.U0q q hq (d.Utower M p s hN)) :
    awayAt d p hp u ∈ d.U0q q hq (UtowerP d M p s hN hp) := by
  have h := (((isUpLevel_U0q_Utower (hp := hp) (hN := hN) hM hpM hs hq hpq).factor u).1 hu).1
  refine Subgroup.mem_inf.2 ⟨mem_UtowerP_iff.2 ⟨(Subgroup.mem_inf.1 h).1, ?_⟩, (Subgroup.mem_inf.1 h).2⟩
  rw [localComponent_awayAt]
  exact one_mem _

/-- `lem:s04-hida`(d), `thm:s04-control`(a) (`s04-control`) on the tower, any coefficient ring with ordinary
decompositions at the three levels `U_{s+1} ≤ U'_s ≤ U_s`: `π_* : e R[X_{s+1}] → e R[X_s]` is surjective with kernel
`e R[X_{s+1}] ∩ ker π''_*`. (Its identification with `I · e R[X_{s+1}]`, `I` the augmentation ideal of
`ker(Δ_{s+1} → Δ_s)`, is proved in the tex and not formalized.) -/
theorem ord_control_tower {R : Type*} [CommRing R] {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    [Finite (XB (UtowerP d M p s hN hp))]
    (hd₂ : HasOrdDecomp (p : R)
      (UpAt (d.Utower M p (s + 1) hN') (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s)) R))
    (hd₁ : HasOrdDecomp (p : R) (UpAt (UtowerP d M p s hN hp) (isUpLevel_UtowerP hM hpM hs) R))
    (hd₀ : HasOrdDecomp (p : R) (UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R)) :
    Function.Surjective (ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
        (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) R) ∧
      ∀ x, ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
          (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) R x = 0 ↔
        piPP_push d M p s hN hN' hp R (x : ZX (d.Utower M p (s + 1) hN') R) = 0 :=
  ord_control_of_levels hs _ (isUpLevel_UtowerP hM hpM hs) _ (Utower_succ_le_UtowerP hN hN' hM hpM)
    (UtowerP_le_Utower hN) (fun _ hu => awayAt_mem_UtowerP_of_mem hM hpM hs hu) hd₂ hd₁ hd₀

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), over `ℤ_[p]` (for `E = ℚ_p`; formalized modulo
`Hyp.PadicOrdDecomp`): `π_* : e ℤ_[p][X_{s+1}] → e ℤ_[p][X_s]` is surjective with kernel `e ∩ ker π''_*`
(`ker_ordPush`). The tensor form `e ℤ_p[X_{s+1}] ⊗_{ℤ_p[Δ_{s+1}]} ℤ_p[Δ_s] ≃ e ℤ_p[X_s]` is not formalized. -/
theorem ord_control_finite (hdec : Hyp.PadicOrdDecomp p) {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Function.Surjective (ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
        (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) ℤ_[p]) ∧
      ∀ x, ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
          (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) ℤ_[p] x = 0 ↔
        piPP_push d M p s hN hN' hp ℤ_[p] (x : ZX (d.Utower M p (s + 1) hN') ℤ_[p]) = 0 := by
  have := finite_XB_UtowerP (hp := hp) (hN := hN) (hN' := hN') hM hpM
  exact ord_control_tower hM hpM hs (hdec _ _) (hdec _ _) (hdec _ _)

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), unconditional over `ZMod (p ^ m)`:
`π_* : e (ℤ/p^m)[X_{s+1}] → e (ℤ/p^m)[X_s]` is surjective with kernel `e ∩ ker π''_*`. -/
theorem ord_control_finite_zmod (m : ℕ) {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Function.Surjective (ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
        (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) (ZMod (p ^ m))) ∧
      ∀ x, ordPush (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s))
          (isUpLevel_Utower (hp := hp) hM hpM hs) (Utower_succ_le hN hN' hM) (ZMod (p ^ m)) x = 0 ↔
        piPP_push d M p s hN hN' hp (ZMod (p ^ m)) (x : ZX (d.Utower M p (s + 1) hN') (ZMod (p ^ m))) = 0 := by
  have := finite_XB_UtowerP (hp := hp) (hN := hN) (hN' := hN') hM hpM
  have := finite_finsupp_zmodPow (XB (d.Utower M p (s + 1) hN')) p m
  have := finite_finsupp_zmodPow (XB (UtowerP d M p s hN hp)) p m
  have := finite_finsupp_zmodPow (XB (d.Utower M p s hN)) p m
  exact ord_control_tower hM hpM hs (hasOrdDecomp_zmodPow p m _) (hasOrdDecomp_zmodPow p m _)
    (hasOrdDecomp_zmodPow p m _)

/-- `lem:s04-hida`(d), `thm:s04-control`(a) (`s04-control`) at the levels `U_0(q) UU_s` (`p ∤ q`; the middle term of
the Ribet sequence, D-lim), any coefficient ring with ordinary decompositions: `π_* : e R[X(U_0(q) U_{s+1})] →
e R[X(U_0(q) U_s)]` is surjective with kernel `e ∩ ker π''_*` (`π'' : X(U_0(q) U_{s+1}) → X(U_0(q) U'_s)`). -/
theorem ord_control_U0q {R : Type*} [CommRing R] {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {q : ℕ}
    (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors)
    [Finite (XB (d.U0q q hq (d.Utower M p (s + 1) hN')))] [Finite (XB (d.U0q q hq (UtowerP d M p s hN hp)))]
    [Finite (XB (d.U0q q hq (d.Utower M p s hN)))]
    (hd₂ : HasOrdDecomp (p : R) (UpAt (d.U0q q hq (d.Utower M p (s + 1) hN'))
      (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq) R))
    (hd₁ : HasOrdDecomp (p : R) (UpAt (d.U0q q hq (UtowerP d M p s hN hp))
      ((isUpLevel_UtowerP hM hpM hs).U0q hq hpq) R))
    (hd₀ : HasOrdDecomp (p : R) (UpAt (d.U0q q hq (d.Utower M p s hN))
      (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq) R)) :
    Function.Surjective (ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
        (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
        (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) R) ∧
      ∀ x, ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
          (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) R x = 0 ↔
        pushforward (d.U0q q hq (d.Utower M p (s + 1) hN')) (d.U0q q hq (UtowerP d M p s hN hp)) R
          (x : ZX (d.U0q q hq (d.Utower M p (s + 1) hN')) R) = 0 :=
  ord_control_of_levels hs _ ((isUpLevel_UtowerP hM hpM hs).U0q hq hpq) _
    (U0q_le_U0q hq (Utower_succ_le_UtowerP hN hN' hM hpM)) (U0q_le_U0q hq (UtowerP_le_Utower hN))
    (fun _ hu => awayAt_mem_U0q_UtowerP_of_mem hM hpM hs hq hpq hu) hd₂ hd₁ hd₀

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), at `U_0(q) UU_s` over `ℤ_[p]` (for `E = ℚ_p`;
formalized modulo `Hyp.PadicOrdDecomp`): `π_*` on the ordinary parts is surjective with kernel `e ∩ ker π''_*`. -/
theorem ord_control_finite_U0q (hdec : Hyp.PadicOrdDecomp p) {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {q : ℕ}
    (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors)
    [Finite (XB (d.U0q q hq (d.Utower M p (s + 1) hN')))] [Finite (XB (d.U0q q hq (UtowerP d M p s hN hp)))]
    [Finite (XB (d.U0q q hq (d.Utower M p s hN)))] :
    Function.Surjective (ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
        (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
        (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) ℤ_[p]) ∧
      ∀ x, ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
          (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) ℤ_[p] x = 0 ↔
        pushforward (d.U0q q hq (d.Utower M p (s + 1) hN')) (d.U0q q hq (UtowerP d M p s hN hp)) ℤ_[p]
          (x : ZX (d.U0q q hq (d.Utower M p (s + 1) hN')) ℤ_[p]) = 0 :=
  ord_control_U0q hM hpM hs hq hpq (hdec _ _) (hdec _ _) (hdec _ _)

/-- `lem:s04-hida`(d), `thm:s04-control`(a), finite part (`s04-control`), at `U_0(q) UU_s`, unconditional over
`ZMod (p ^ m)`. -/
theorem ord_control_finite_U0q_zmod (m : ℕ) {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {q : ℕ}
    (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors)
    [Finite (XB (d.U0q q hq (d.Utower M p (s + 1) hN')))] [Finite (XB (d.U0q q hq (UtowerP d M p s hN hp)))]
    [Finite (XB (d.U0q q hq (d.Utower M p s hN)))] :
    Function.Surjective (ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
        (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
        (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) (ZMod (p ^ m))) ∧
      ∀ x, ordPush (isUpLevel_U0q_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) hq hpq)
          (isUpLevel_U0q_Utower (hp := hp) hM hpM hs hq hpq)
          (U0q_le_U0q hq (Utower_succ_le hN hN' hM)) (ZMod (p ^ m)) x = 0 ↔
        pushforward (d.U0q q hq (d.Utower M p (s + 1) hN')) (d.U0q q hq (UtowerP d M p s hN hp)) (ZMod (p ^ m))
          (x : ZX (d.U0q q hq (d.Utower M p (s + 1) hN')) (ZMod (p ^ m))) = 0 := by
  have := finite_finsupp_zmodPow (XB (d.U0q q hq (d.Utower M p (s + 1) hN'))) p m
  have := finite_finsupp_zmodPow (XB (d.U0q q hq (UtowerP d M p s hN hp))) p m
  have := finite_finsupp_zmodPow (XB (d.U0q q hq (d.Utower M p s hN))) p m
  exact ord_control_U0q hM hpM hs hq hpq (hasOrdDecomp_zmodPow p m _) (hasOrdDecomp_zmodPow p m _)
    (hasOrdDecomp_zmodPow p m _)

end TowerControl

end

end Langlandscape.Ordinary
