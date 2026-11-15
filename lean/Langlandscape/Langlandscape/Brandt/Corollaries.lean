/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Adjoint
import Langlandscape.Brandt.Hecke
import Langlandscape.Brandt.RightTranslate
import Langlandscape.Brandt.Up

/-!
# Corollaries: `p`-adic bijectivity of the norm map, `U_p` commutation, adjoints (S01-L17)

`plan/staged/stage-01-quaternion-foundations.tex`: `def:s01-pairing`, `prop:s01-adjoint`(b) ("in particular"),
`lem:s01-Up`(e), `if:s01-hecke`. Trivial coefficients.

* `normMap_bijective_padic` : for `U ≤ Ô^×`, `p ≥ 5`, the norm map `ν : ℤ_p[X] → ℤ_p^X` is bijective
  (`w_x ∣ |Γ_x| ∣ 24`, `lem:s01-stab`(c)).
* `Up_comm_heckeT`, `Up_comm_Tl`, `Up_comm_Sl`, `Up_comm_diamond`, `Up_comm_PiEll`, `Up_comm_rightTranslate` :
  `U_p` commutes with the operators supported at split primes `ℓ ≠ p`, including `ℓ ∣ M` (`splitAt_Utower_of_split`),
  and with Atkin–Lehner/right translations (`lem:s01-Up`(e)). `Up_comm_diamond_self` : `U_p` commutes with the
  diamond operator at `p` itself (`δ_t` normalises `U_s` and commutes with `ϖ`). Hence `U_p` commutes with every
  local factor of `⟨d⟩`, `d ∈ (ℤ/Mp^s)^×`; the product `⟨d⟩` itself is not assembled (see `Brandt.diamond`).
* Central double cosets: `heckeT_central_apply`, `heckeT_central_mul`, `heckeT_central_comm`,
  `heckeT_congr_dcSet`, `heckeTHom_comp`.
* Adjoints for the Brandt pairing on `R[X]` (from `brandtPairing_heckeTHom` with `g⁻¹`):
  `Tl_adjoint` (`T_ℓ^* = S_ℓ^{-1} T_ℓ`), `diamond_adjoint` (`⟨t⟩^* = ⟨t⁻¹⟩`), `PiEll_adjoint`
  (`Π_ℓ^* = Π_ℓ^{-1}`), `Tl_selfAdjoint_of_SlInvHom`, `SlInvHom_U0` (`S_ℓ = 1` at `U_0(M)`) and `Tl_selfAdjoint_U0`.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical
open Langlandscape.Local (matGL diagGL intUnit matGL_val diagGL_val GL2Zl matGL_mem_GL2Zl_iff K1)

/-! ### `p`-adic bijectivity of the norm map -/

/-- `def:s01-pairing`, `lem:s01-stab`(c) (`s01-pairing`): for `U ≤ Ô^×`, a prime `p ≥ 5` and finite `X_B(U)`, the
norm map `ν : ℤ_p[X] → ℤ_p^X` is bijective, since every weight `w_x` divides `|Γ_x| ∣ 24` and is prime to `p`. -/
theorem normMap_bijective_padic (d : DefiniteData) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hU : U ≤ d.Ohat) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) [Finite (XB U)] :
    Function.Bijective (normMap U ℤ_[p]) := by
  refine normMap_bijective U ℤ_[p] fun c => ?_
  have hnd : ¬ p ∣ wx U (Quotient.out c) := by
    intro h
    have h1 : wx U (Quotient.out c) ∣ Nat.card (Gam U (Quotient.out c)) := by
      unfold wx
      exact Nat.div_dvd_of_dvd (Subgroup.card_dvd_of_le inf_le_left)
    exact not_dvd_card_Gam d.ha d.hb d.O.1 hU _ (Fact.out : p.Prime) hp (h.trans h1)
  have hnd' : ¬ ((p : ℤ) ∣ ((wx U (Quotient.out c) : ℕ) : ℤ)) := by exact_mod_cast hnd
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hnd' ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd (p := p) ((wx U (Quotient.out c) : ℕ) : ℤ)).1 (by simpa using hlt)

/-! ### Central double cosets and double-coset invariance -/

section Central

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `def:s01-hecke` (`s01-hecke`): if all the cosets of `U g U` are the single coset `s U`, then
`(T_g f)[x] = f[x s]`. -/
theorem heckeT_apply_singleton (g s : (GL2TF.Quat.BHat a b)ˣ) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (hs : s ∈ dcSet U g)
    (hall : ∀ y ∈ dcSet U g, (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s)
    (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeT U g R hfin f (DoubleCoset.mk (globalUnits a b) U x) =
      f (DoubleCoset.mk (globalUnits a b) U (x * s)) := by
  have h := heckeT_apply_reps U g R hfin {s}
    (fun t ht => by
      rw [Finset.mem_singleton] at ht
      rw [ht]
      exact hs)
    (fun y hy => ⟨s, Finset.mem_singleton_self s, hall y hy⟩)
    (by rw [Finset.coe_singleton]; exact Set.injOn_singleton _ _) f x
  rw [Finset.sum_singleton] at h
  exact h

/-- `def:s01-hecke` (`s01-hecke`): for a central `z`, `(T_z f)[x] = f[x z]`. -/
theorem heckeT_central_apply (z : (GL2TF.Quat.BHat a b)ˣ) (hz : ∀ x, Commute z x)
    (hfin : (U ⊓ conjSub U z).relIndex U ≠ 0) (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    heckeT U z R hfin f (DoubleCoset.mk (globalUnits a b) U x) =
      f (DoubleCoset.mk (globalUnits a b) U (x * z)) := by
  refine heckeT_apply_singleton U R z z hfin ((mem_dcSet U z).2 ⟨1, U.one_mem, 1, U.one_mem, by simp⟩) ?_ f x
  intro y hy
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U z).1 hy
  rw [QuotientGroup.eq]
  have hc : z⁻¹ * u⁻¹ * z = u⁻¹ := by
    rw [mul_assoc, ← (hz u⁻¹).eq, inv_mul_cancel_left]
  have e : (u * z * v)⁻¹ * z = v⁻¹ * (z⁻¹ * u⁻¹ * z) := by group
  rw [e, hc]
  exact U.mul_mem (U.inv_mem hv) (U.inv_mem hu)

/-- `def:s01-hecke` (`s01-hecke`): `g U g⁻¹` is unchanged when `g` is multiplied by a central element. -/
theorem conjSub_mul_central (z g : (GL2TF.Quat.BHat a b)ˣ) (hz : ∀ x, Commute z x) :
    conjSub U (z * g) = conjSub U g := by
  ext x
  rw [mem_conjSub, mem_conjSub]
  have hc : z⁻¹ * x * z = x := by
    rw [mul_assoc, ← (hz x).eq, inv_mul_cancel_left]
  have e : (z * g)⁻¹ * x * (z * g) = g⁻¹ * (z⁻¹ * x * z) * g := by group
  rw [e, hc]

/-- `def:s01-hecke` (`s01-hecke`): `T_{z g} = T_z ∘ T_g` for a central `z`. -/
theorem heckeT_central_mul (z g : (GL2TF.Quat.BHat a b)ˣ) (hz : ∀ x, Commute z x)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfinz : (U ⊓ conjSub U z).relIndex U ≠ 0)
    (hfinzg : (U ⊓ conjSub U (z * g)).relIndex U ≠ 0) :
    heckeT U (z * g) R hfinzg = heckeT U z R hfinz ∘ₗ heckeT U g R hfin := by
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U g hfin
  have hS' : ∀ t ∈ S.image (fun s => z * s), t ∈ dcSet U (z * g) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨u, hu, v, hv, e⟩ := (mem_dcSet U g).1 (hS s hs)
    refine (mem_dcSet U (z * g)).2 ⟨u, hu, v, hv, ?_⟩
    rw [e]
    have h1 := (hz u).eq
    calc z * (u * g * v) = (z * u) * g * v := by group
      _ = (u * z) * g * v := by rw [h1]
      _ = u * (z * g) * v := by group
  have hcov' : ∀ y ∈ dcSet U (z * g), ∃ t ∈ S.image (fun s => z * s),
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk t := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U (z * g)).1 hy
    have hmem : z⁻¹ * (u * (z * g) * v) ∈ dcSet U g := by
      refine (mem_dcSet U g).2 ⟨u, hu, v, hv, ?_⟩
      have h1 := (hz u).eq
      calc z⁻¹ * (u * (z * g) * v) = z⁻¹ * (u * z) * g * v := by group
        _ = z⁻¹ * (z * u) * g * v := by rw [h1]
        _ = u * g * v := by group
    obtain ⟨s, hs, hys⟩ := hcov _ hmem
    refine ⟨z * s, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [QuotientGroup.eq] at hys ⊢
    have e2 : (u * (z * g) * v)⁻¹ * (z * s) = (z⁻¹ * (u * (z * g) * v))⁻¹ * s := by group
    rw [e2]
    exact hys
  have hinj' : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U)
      ↑(S.image (fun s => z * s)) := by
    intro t1 ht1 t2 ht2 e
    obtain ⟨s1, hs1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht1)
    obtain ⟨s2, hs2, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht2)
    have e' : (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s2 := by
      have e1 : (QuotientGroup.mk (z * s1) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk (z * s2) := e
      rw [QuotientGroup.eq] at e1 ⊢
      have e3 : (z * s1)⁻¹ * (z * s2) = s1⁻¹ * s2 := by group
      rwa [e3] at e1
    show z * s1 = z * s2
    rw [hinj (Finset.mem_coe.2 hs1) (Finset.mem_coe.2 hs2) e']
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, heckeT_central_apply U R z hz hfinz,
    heckeT_apply_reps U g R hfin S hS hcov hinj f (x * z),
    heckeT_apply_reps U (z * g) R hfinzg _ hS' hcov' hinj' f x,
    Finset.sum_image (fun s _ s' _ h => mul_left_cancel h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc]

/-- `def:s01-hecke` (`s01-hecke`): a central `T_z` commutes with every `T_g`. -/
theorem heckeT_central_comm (z g : (GL2TF.Quat.BHat a b)ˣ) (hz : ∀ x, Commute z x)
    (hfinz : (U ⊓ conjSub U z).relIndex U ≠ 0) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    heckeT U z R hfinz ∘ₗ heckeT U g R hfin = heckeT U g R hfin ∘ₗ heckeT U z R hfinz := by
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U g hfin
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, heckeT_central_apply U R z hz hfinz,
    heckeT_apply_reps U g R hfin S hS hcov hinj f (x * z),
    heckeT_apply_reps U g R hfin S hS hcov hinj (heckeT U z R hfinz f) x]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : x * z * s = x * s * z := by rw [mul_assoc, mul_assoc, (hz s).eq]
  rw [heckeT_central_apply U R z hz hfinz f (x * s), e]

/-- `def:s01-hecke` (`s01-hecke`): `T_g` depends only on the double coset `U g U`. -/
theorem heckeT_congr_dcSet {g g' : (GL2TF.Quat.BHat a b)ˣ} (h : dcSet U g = dcSet U g')
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U ⊓ conjSub U g').relIndex U ≠ 0) :
    heckeT U g R hfin = heckeT U g' R hfin' := by
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U g hfin
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [heckeT_apply_reps U g R hfin S hS hcov hinj f x,
    heckeT_apply_reps U g' R hfin' S (fun s hs => by rw [← h]; exact hS s hs)
      (fun y hy => hcov y (by rw [h]; exact hy)) hinj f x]

/-- `def:s01-hecke` (`s01-hecke`): `U (u g v) U = U g U` for `u, v ∈ U`. -/
theorem dcSet_conj_eq (g u v : (GL2TF.Quat.BHat a b)ˣ) (hu : u ∈ U) (hv : v ∈ U) :
    dcSet U (u * g * v) = dcSet U g := by
  ext y
  constructor
  · intro hy
    obtain ⟨u1, hu1, v1, hv1, rfl⟩ := (mem_dcSet U _).1 hy
    exact (mem_dcSet U g).2 ⟨u1 * u, U.mul_mem hu1 hu, v * v1, U.mul_mem hv hv1, by group⟩
  · intro hy
    obtain ⟨u1, hu1, v1, hv1, rfl⟩ := (mem_dcSet U g).1 hy
    exact (mem_dcSet U _).2 ⟨u1 * u⁻¹, U.mul_mem hu1 (U.inv_mem hu), v⁻¹ * v1,
      U.mul_mem (U.inv_mem hv) hv1, by group⟩

/-- `def:s01-hecke` (`s01-hecke`): extensionality of `R[X]` through the evaluation pairing. -/
theorem zx_ext_of_evalPairing {x y : ZX U R}
    (h : ∀ f : ZXdual U R, evalPairing U R x f = evalPairing U R y f) : x = y := by
  ext c
  have := h (Pi.single c (1 : R))
  rwa [evalPairing_pi_single, evalPairing_pi_single] at this

/-- `def:s01-hecke` (`s01-hecke`): `T_g^t` depends only on the element `g` (transport along `g = g'`). -/
theorem heckeTHom_congr [Finite (XB U)] {g g' : (GL2TF.Quat.BHat a b)ˣ} (h : g = g')
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U ⊓ conjSub U g').relIndex U ≠ 0) :
    heckeTHom U g R hfin = heckeTHom U g' R hfin' := by
  subst h
  rfl

/-- `def:s01-hecke` (`s01-hecke`): if `T_h = T_{g₁} ∘ T_{g₂}` on `R^X` then `T_h^t = T_{g₂}^t ∘ T_{g₁}^t`
on `R[X]`. -/
theorem heckeTHom_comp [Finite (XB U)] (h g₁ g₂ : (GL2TF.Quat.BHat a b)ˣ)
    (hfinh : (U ⊓ conjSub U h).relIndex U ≠ 0) (hfin₁ : (U ⊓ conjSub U g₁).relIndex U ≠ 0)
    (hfin₂ : (U ⊓ conjSub U g₂).relIndex U ≠ 0)
    (hcomp : heckeT U h R hfinh = heckeT U g₁ R hfin₁ ∘ₗ heckeT U g₂ R hfin₂) :
    heckeTHom U h R hfinh = heckeTHom U g₂ R hfin₂ ∘ₗ heckeTHom U g₁ R hfin₁ := by
  refine LinearMap.ext fun x => zx_ext_of_evalPairing U R fun f => ?_
  simp only [LinearMap.comp_apply, heckeTHom_transpose, hcomp]

end Central

/-! ### Explicit elements of `GL₂(ℚ_ℓ)`: the Weyl element -/

section Local

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `def:s01-hecke` (`s01-hecke`): the Weyl element `!![0, 1; 1, 0] ∈ GL₂(ℤ_ℓ)`. -/
noncomputable def weylGL (ℓ : ℕ) [Fact ℓ.Prime] : GL (Fin 2) ℚ_[ℓ] :=
  matGL 0 1 1 0 (by simp)

/-- `def:s01-hecke` (`s01-hecke`): the Weyl element lies in `GL₂(ℤ_ℓ)`. -/
theorem weylGL_mem : weylGL ℓ ∈ GL2Zl ℓ :=
  (matGL_mem_GL2Zl_iff _ _ _ _ _).2 ⟨by simp, by simp, by simp, by simp, by simp⟩

/-- `def:s01-hecke` (`s01-hecke`): `w² = 1`. -/
theorem weylGL_mul_self : weylGL ℓ * weylGL ℓ = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- `def:s01-hecke` (`s01-hecke`): `w⁻¹ = w`. -/
theorem weylGL_inv : (weylGL ℓ)⁻¹ = weylGL ℓ :=
  inv_eq_of_mul_eq_one_right (weylGL_mul_self (ℓ := ℓ))

/-- `def:s01-hecke` (`s01-hecke`): `diag(c, c) = w diag(c, 1) w⁻¹ diag(c, 1)`. -/
theorem diagGL_eq_weyl (c : ℚ_[ℓ]ˣ) :
    diagGL c c = weylGL ℓ * diagGL c 1 * (weylGL ℓ)⁻¹ * diagGL c 1 := by
  rw [weylGL_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- `def:s01-hecke` (`s01-hecke`): `diag(c, 1)⁻¹ = diag(c, c)⁻¹ · (w diag(c, 1) w⁻¹)`, i.e. `ϖ⁻¹ = z⁻¹ · ϖ'`
with `ϖ' = diag(1, c)` conjugate to `ϖ` by the Weyl element. -/
theorem diagGL_inv_eq_weyl (c : ℚ_[ℓ]ˣ) :
    (diagGL c 1)⁻¹ = (diagGL c c)⁻¹ * (weylGL ℓ * diagGL c 1 * (weylGL ℓ)⁻¹) := by
  rw [diagGL_eq_weyl c]
  group

/-- `def:s01-hecke` (`s01-hecke`): `diag(c, c)` is central in `GL₂(ℚ_ℓ)`. -/
theorem diagGL_scalar_comm (c : ℚ_[ℓ]ˣ) (m : GL (Fin 2) ℚ_[ℓ]) : diagGL c c * m = m * diagGL c c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `def:s01-hecke` (`s01-hecke`): `diag(1, a⁻¹) = diag(1, a)⁻¹`. -/
theorem diagGL_one_inv (a : ℚ_[ℓ]ˣ) : diagGL 1 a⁻¹ = (diagGL 1 a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `def:s01-hecke` (`s01-hecke`): `intUnit` is a group homomorphism. -/
theorem intUnit_inv (t : ℤ_[ℓ]ˣ) : intUnit t⁻¹ = (intUnit t)⁻¹ :=
  map_inv (Units.map (PadicInt.Coe.ringHom (p := ℓ)).toMonoidHom) t

end Local

/-! ### The elements `ϖ_ℓ`, `z_ℓ`, `δ_t` of `B̂^×` -/

section Elements

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-hecke` (`s01-hecke`): the central idele `z_ℓ` commutes with all of `B̂^×`. -/
theorem elemS_commute (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : Commute (elemS d ℓ hℓ) x := by
  unfold elemS
  rw [localEmbedGL_apply]
  refine commute_localEmbed_of_commute _ ?_
  unfold Commute SemiconjBy
  apply (d.iotaGL ℓ hℓ).injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact diagGL_scalar_comm _ _

/-- `def:s01-hecke` (`s01-hecke`): `ϖ_ℓ⁻¹ = z_ℓ⁻¹ · (w ϖ_ℓ w⁻¹)` in `B̂^×` (`w` the Weyl element at `ℓ`). -/
theorem elemT_inv_eq :
    (elemT d ℓ hℓ)⁻¹ = (elemS d ℓ hℓ)⁻¹ *
      (localEmbedGL d ℓ hℓ (weylGL ℓ) * elemT d ℓ hℓ * (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹) := by
  have h2 := congrArg (localEmbedGL d ℓ hℓ) (diagGL_inv_eq_weyl (padicUnit ℓ))
  unfold elemT elemS
  simpa only [map_inv, map_mul] using h2

/-- `def:s01-hecke` (`s01-hecke`): `δ_{t⁻¹} = δ_t⁻¹`. -/
theorem diamondElt_inv (t : ℤ_[ℓ]ˣ) : diamondElt d ℓ hℓ t⁻¹ = (diamondElt d ℓ hℓ t)⁻¹ := by
  show localEmbedGL d ℓ hℓ (diagGL 1 (intUnit t⁻¹)) = (localEmbedGL d ℓ hℓ (diagGL 1 (intUnit t)))⁻¹
  rw [intUnit_inv, diagGL_one_inv, map_inv]

end Elements

/-! ### `Tl_adjoint` -/

section TlAdjoint

variable (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : ¬ ℓ ∣ d.D) (R : Type*) [CommRing R]

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): `S_ℓ^{-1} = [U z_ℓ⁻¹ U]` on `R[X]` (the transpose of `T_{z_ℓ⁻¹}`). -/
noncomputable def SlInvHom [Finite (XB U)] : ZX U R →ₗ[R] ZX U R :=
  heckeTHom U (elemS d ℓ hℓ)⁻¹ R
    (relIndex_ne_zero_of_commute U _ fun x => (elemS_commute d ℓ hℓ x).inv_left)

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): at a level invariant at `ℓ`, `T_{ϖ_ℓ⁻¹} = T_{ϖ_ℓ} ∘ T_{z_ℓ⁻¹}` on `R^X`
(`ϖ_ℓ⁻¹ = z_ℓ⁻¹ · w ϖ_ℓ w⁻¹` and `w ∈ GL₂(ℤ_ℓ) ⊆ U`). -/
theorem heckeT_inv_elemT (hU : IsInvariantAt d ℓ hℓ U)
    (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0)
    (hfin' : (U ⊓ conjSub U (elemT d ℓ hℓ)⁻¹).relIndex U ≠ 0) :
    heckeT U (elemT d ℓ hℓ)⁻¹ R hfin' = heckeT U (elemT d ℓ hℓ) R hfin ∘ₗ
      heckeT U (elemS d ℓ hℓ)⁻¹ R
        (relIndex_ne_zero_of_commute U _ fun x => (elemS_commute d ℓ hℓ x).inv_left) := by
  have hzi : ∀ x, Commute (elemS d ℓ hℓ)⁻¹ x := fun x => (elemS_commute d ℓ hℓ x).inv_left
  have hfinzi : (U ⊓ conjSub U (elemS d ℓ hℓ)⁻¹).relIndex U ≠ 0 := relIndex_ne_zero_of_commute U _ hzi
  have hw : localEmbedGL d ℓ hℓ (weylGL ℓ) ∈ U := by
    have h := hU 1 U.one_mem (weylGL ℓ) weylGL_mem
    rwa [one_mul] at h
  have hfinzT : (U ⊓ conjSub U ((elemS d ℓ hℓ)⁻¹ * elemT d ℓ hℓ)).relIndex U ≠ 0 := by
    rw [conjSub_mul_central U _ _ hzi]
    exact hfin
  have hkey : (elemT d ℓ hℓ)⁻¹ = localEmbedGL d ℓ hℓ (weylGL ℓ) *
      ((elemS d ℓ hℓ)⁻¹ * elemT d ℓ hℓ) * (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by
    rw [elemT_inv_eq d ℓ hℓ]
    have hc := (hzi (localEmbedGL d ℓ hℓ (weylGL ℓ))).eq
    calc (elemS d ℓ hℓ)⁻¹ * (localEmbedGL d ℓ hℓ (weylGL ℓ) * elemT d ℓ hℓ *
          (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹)
        = ((elemS d ℓ hℓ)⁻¹ * localEmbedGL d ℓ hℓ (weylGL ℓ)) * elemT d ℓ hℓ *
          (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by group
      _ = (localEmbedGL d ℓ hℓ (weylGL ℓ) * (elemS d ℓ hℓ)⁻¹) * elemT d ℓ hℓ *
          (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by rw [hc]
      _ = _ := by group
  have hdc : dcSet U (elemT d ℓ hℓ)⁻¹ = dcSet U ((elemS d ℓ hℓ)⁻¹ * elemT d ℓ hℓ) := by
    rw [hkey, dcSet_conj_eq U _ _ _ hw (U.inv_mem hw)]
  rw [heckeT_congr_dcSet U R hdc hfin' hfinzT,
    heckeT_central_mul U R _ _ hzi hfin hfinzi hfinzT]
  exact heckeT_central_comm U R _ _ hzi hfinzi hfin

/-- `prop:s01-adjoint`(b) (`s01-adjoint`, "in particular"): for a level `U` invariant at `ℓ ∤ D` (so containing
`GL₂(ℤ_ℓ)` at `ℓ`), `T_ℓ^* = S_ℓ^{-1} T_ℓ` for the Brandt pairing, on `R[X]` (`T_ℓ` as `heckeTHom` of `ϖ_ℓ`;
`hfin'` is the finiteness for `ϖ_ℓ⁻¹`). -/
theorem Tl_adjoint [Finite (XB U)] (hU : IsInvariantAt d ℓ hℓ U)
    (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0)
    (hfin' : (U ⊓ conjSub U (elemT d ℓ hℓ)⁻¹).relIndex U ≠ 0) (x y : ZX U R) :
    brandtPairing U R (heckeTHom U (elemT d ℓ hℓ) R hfin x) y =
      brandtPairing U R x (SlInvHom d U ℓ hℓ R (heckeTHom U (elemT d ℓ hℓ) R hfin y)) := by
  have h := heckeTHom_comp U R (elemT d ℓ hℓ)⁻¹ (elemT d ℓ hℓ) (elemS d ℓ hℓ)⁻¹ hfin' hfin
    (relIndex_ne_zero_of_commute U _ fun x => (elemS_commute d ℓ hℓ x).inv_left)
    (heckeT_inv_elemT d U ℓ hℓ R hU hfin hfin')
  have hh : heckeTHom U (elemT d ℓ hℓ)⁻¹ R hfin' y =
      SlInvHom d U ℓ hℓ R (heckeTHom U (elemT d ℓ hℓ) R hfin y) := LinearMap.congr_fun h y
  rw [brandtPairing_heckeTHom U (elemT d ℓ hℓ) R hfin hfin' x y, hh]

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): if `S_ℓ^{-1}` acts trivially on `R[X]`, then `T_ℓ` is self-adjoint for the
Brandt pairing. -/
theorem Tl_selfAdjoint_of_SlInvHom [Finite (XB U)] (hU : IsInvariantAt d ℓ hℓ U)
    (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0)
    (hfin' : (U ⊓ conjSub U (elemT d ℓ hℓ)⁻¹).relIndex U ≠ 0)
    (hS : ∀ z : ZX U R, SlInvHom d U ℓ hℓ R z = z) (x y : ZX U R) :
    brandtPairing U R (heckeTHom U (elemT d ℓ hℓ) R hfin x) y =
      brandtPairing U R x (heckeTHom U (elemT d ℓ hℓ) R hfin y) := by
  rw [Tl_adjoint d U ℓ hℓ R hU hfin hfin' x y, hS]

end TlAdjoint

/-! ### `S_ℓ = 1` at level `U_0(M)` -/

section Scalar

variable {a b : ℤ}

/-- `def:s01-hecke` (`s01-hecke`): the unit `u ∈ ℚ^×` seen in `ℚ_q^×`. -/
noncomputable def ratUnit (q : ℕ) [Fact q.Prime] (u : ℚˣ) : ℚ_[q]ˣ :=
  Units.map (algebraMap ℚ ℚ_[q]).toMonoidHom u

/-- `def:s01-hecke` (`s01-hecke`): the unit `u ∈ ℚ^×` seen as a scalar in `B^×`. -/
noncomputable def scalarUnit (a b : ℤ) (u : ℚˣ) : (GL2TF.Quat.QuatAlg ℚ a b)ˣ :=
  Units.map (algebraMap ℚ (GL2TF.Quat.QuatAlg ℚ a b)).toMonoidHom u

/-- `def:s01-hecke` (`s01-hecke`): the rational unit `ℓ`. -/
noncomputable def ellUnit (ℓ : ℕ) [Fact ℓ.Prime] : ℚˣ :=
  Units.mk0 (ℓ : ℚ) (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)

/-- `def:s01-hecke` (`s01-hecke`): `ratUnit ℓ (ellUnit ℓ) = ℓ ∈ ℚ_ℓ^×`. -/
theorem ratUnit_ellUnit (ℓ : ℕ) [Fact ℓ.Prime] : ratUnit ℓ (ellUnit ℓ) = padicUnit ℓ :=
  Units.ext (by simp [ratUnit, ellUnit, padicUnit])

/-- `def:s01-hecke` (`s01-hecke`): `‖ℓ‖_q = 1` for a prime `q ≠ ℓ`. -/
theorem norm_ratUnit_ellUnit {q ℓ : ℕ} [Fact q.Prime] [Fact ℓ.Prime] (h : q ≠ ℓ) :
    ‖((ratUnit q (ellUnit ℓ) : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
  have e : ((ratUnit q (ellUnit ℓ) : ℚ_[q]ˣ) : ℚ_[q]) = (ℓ : ℚ_[q]) := by simp [ratUnit, ellUnit]
  rw [e, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : ℓ.Prime)).2 h

/-- `def:s01-hecke` (`s01-hecke`): `‖ℓ⁻¹‖_q = 1` for a prime `q ≠ ℓ`. -/
theorem norm_ratUnit_ellUnit_inv {q ℓ : ℕ} [Fact q.Prime] [Fact ℓ.Prime] (h : q ≠ ℓ) :
    ‖((ratUnit q (ellUnit ℓ)⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
  have e : ratUnit q (ellUnit ℓ)⁻¹ = (ratUnit q (ellUnit ℓ))⁻¹ :=
    map_inv (Units.map (algebraMap ℚ ℚ_[q]).toMonoidHom) _
  rw [e, Units.val_inv_eq_inv_val, norm_inv, norm_ratUnit_ellUnit h, inv_one]

/-- `def:s01-hecke` (`s01-hecke`): `ι(u⁻¹) = ι(u)⁻¹` for scalars. -/
theorem iotaU_scalarUnit_inv (u : ℚˣ) :
    iotaU a b (scalarUnit a b u⁻¹) = (iotaU a b (scalarUnit a b u))⁻¹ := by
  unfold scalarUnit
  simp only [map_inv]

/-- `def:s01-hecke` (`s01-hecke`): base change of a rational scalar of `B` is the scalar of `B_p`. -/
theorem baseChange_scalarUnit (p : ℕ) [Fact p.Prime] (u : ℚˣ) :
    GL2TF.Quat.baseChange a b (algebraMap ℚ ℚ_[p])
        ((scalarUnit a b u : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) : GL2TF.Quat.QuatAlg ℚ a b) =
      algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] a b) (ratUnit p u : ℚ_[p]) := by
  ext <;> simp [GL2TF.Quat.baseChange, scalarUnit, ratUnit, QuaternionAlgebra.algebraMap_eq]

/-- `def:s01-hecke` (`s01-hecke`): the `p`-component of the scalar `ι(u)` is the scalar `u ∈ ℚ_p`. -/
theorem localProj_iotaU_scalar (p : ℕ) [Fact p.Prime] (u : ℚˣ) :
    localProj a b p ((iotaU a b (scalarUnit a b u) : (GL2TF.Quat.BHat a b)ˣ) : GL2TF.Quat.BHat a b) =
      algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] a b) (ratUnit p u : ℚ_[p]) := by
  show localProj a b p (GL2TF.Quat.finEmbed a b
    ((scalarUnit a b u : (GL2TF.Quat.QuatAlg ℚ a b)ˣ) : GL2TF.Quat.QuatAlg ℚ a b)) = _
  rw [localProj_finEmbed, baseChange_scalarUnit]

/-- `def:s01-hecke` (`s01-hecke`): the scalar `ι(u)` is central in `B̂^×`. -/
theorem commute_iotaU_scalar (u : ℚˣ) (w : (GL2TF.Quat.BHat a b)ˣ) :
    Commute (iotaU a b (scalarUnit a b u)) w := by
  unfold Commute SemiconjBy
  refine Units.ext (bhat_ext_local fun p => ?_)
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul, localProj_iotaU_scalar]
  exact Algebra.commutes _ _

/-- `def:s01-hecke` (`s01-hecke`): a rational scalar in `ℤ_p` lies in every local order. -/
theorem scalar_mem_localLattice (O : GL2TF.Quat.QOrder a b) (p : ℕ) [Fact p.Prime] (c : ℚ_[p])
    (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] a b) c ∈
      GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  have h : algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] a b) c =
      (⟨c, hc⟩ : ℤ_[p]) • (1 : GL2TF.Quat.QuatAlg ℚ_[p] a b) := by
    have hs : ((⟨c, hc⟩ : ℤ_[p]) • (1 : ℚ_[p])) = c := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [QuaternionAlgebra.algebraMap_eq]
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · exact hs.symm
    · exact (smul_zero _).symm
    · exact (smul_zero _).symm
    · exact (smul_zero _).symm
  rw [h]
  exact Submodule.smul_mem _ _ (one_mem_localLattice O p)

/-- `def:s01-hecke` (`s01-hecke`): `localProj` of a unit with trivial local unit component. -/
theorem localProj_val_eq_one {p : ℕ} [Fact p.Prime] {x : (GL2TF.Quat.BHat a b)ˣ}
    (h : localProjUnits a b p x = 1) : localProj a b p (x : GL2TF.Quat.BHat a b) = 1 := by
  simpa using congrArg Units.val h

/-- `def:s01-hecke` (`s01-hecke`): `diag(x, x) ∈ K_0(q^e)` if `‖x‖ = 1`. -/
theorem diagGL_mem_K0 {q : ℕ} [Fact q.Prime] (x : ℚ_[q]ˣ) (hx : ‖(x : ℚ_[q])‖ = 1) (e : ℕ) :
    diagGL x x ∈ Langlandscape.Local.K0 q e := by
  rw [Langlandscape.Local.mem_K0_iff]
  refine ⟨(matGL_mem_GL2Zl_iff _ _ _ _ _).2 ⟨hx.le, by simp, by simp, hx.le, ?_⟩, ?_⟩
  · simp [norm_mul, hx]
  · have h0 : (Units.val (diagGL x x)) 1 0 = 0 := by simp [diagGL_val]
    rw [h0, norm_zero]
    positivity

/-- `def:s01-hecke` (`s01-hecke`): `localComponent_p ι(u) = diag(u, u)`. -/
theorem localComponent_iotaU_scalar (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (u : ℚˣ) :
    localComponent d p hp (iotaU d.a d.b (scalarUnit d.a d.b u)) = diagGL (ratUnit p u) (ratUnit p u) := by
  apply Units.ext
  refine (localComponent_finEmbed (d := d) (ℓ := p) (hℓ := hp) (scalarUnit d.a d.b u)).trans ?_
  rw [baseChange_scalarUnit, AlgEquiv.commutes]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL_val, Matrix.algebraMap_matrix_apply]

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-hecke` (`s01-hecke`): `e_ℓ = ι(ℓ) · z_ℓ⁻¹ ∈ B̂^×` (`ℓ` away from `ℓ`, `1` at `ℓ`). -/
noncomputable def scalarE : (GL2TF.Quat.BHat d.a d.b)ˣ :=
  iotaU d.a d.b (scalarUnit d.a d.b (ellUnit ℓ)) * (elemS d ℓ hℓ)⁻¹

/-- `def:s01-hecke` (`s01-hecke`): the `ℓ`-component of `z_ℓ`. -/
theorem localProjUnits_elemS :
    localProjUnits d.a d.b ℓ (elemS d ℓ hℓ) = (d.iotaGL ℓ hℓ).symm (diagGL (padicUnit ℓ) (padicUnit ℓ)) := by
  unfold elemS
  rw [localEmbedGL_apply, localProjUnits_localEmbed]

/-- `def:s01-hecke` (`s01-hecke`): the `ℓ`-component of `ι(ℓ)`. -/
theorem localProjUnits_iotaU_ell :
    localProjUnits d.a d.b ℓ (iotaU d.a d.b (scalarUnit d.a d.b (ellUnit ℓ))) =
      (d.iotaGL ℓ hℓ).symm (diagGL (padicUnit ℓ) (padicUnit ℓ)) := by
  apply (d.iotaGL ℓ hℓ).injective
  rw [MulEquiv.apply_symm_apply, ← localComponent_apply, localComponent_iotaU_scalar, ratUnit_ellUnit]

/-- `def:s01-hecke` (`s01-hecke`): `e_ℓ ∈ Ô^×`. -/
theorem scalarE_mem_Ohat : scalarE d ℓ hℓ ∈ d.Ohat := by
  refine (mem_orderCompletionUnits_iff_local d.O.1 _).2 fun p => ?_
  by_cases h : (p : ℕ) = ℓ
  · subst h
    have h1 : localProjUnits d.a d.b p (scalarE d p hℓ) = 1 := by
      unfold scalarE
      rw [map_mul, map_inv, localProjUnits_iotaU_ell d p hℓ, localProjUnits_elemS d p hℓ, mul_inv_cancel]
    have h2 : localProjUnits d.a d.b p (scalarE d p hℓ)⁻¹ = 1 := by rw [map_inv, h1, inv_one]
    refine ⟨?_, ?_⟩
    · rw [localProj_val_eq_one h1]
      exact one_mem_localLattice _ _
    · rw [localProj_val_eq_one h2]
      exact one_mem_localLattice _ _
  · have hSun : localProjUnits d.a d.b p (elemS d ℓ hℓ) = 1 := by
      unfold elemS
      exact localProjUnits_localEmbedGL_of_ne _ h
    have hSi : localProjUnits d.a d.b p (elemS d ℓ hℓ)⁻¹ = 1 := by rw [map_inv, hSun, inv_one]
    have e1 : localProj d.a d.b p ((scalarE d ℓ hℓ : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) =
        algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] d.a d.b) (ratUnit p (ellUnit ℓ) : ℚ_[p]) := by
      unfold scalarE
      rw [Units.val_mul, map_mul, localProj_iotaU_scalar, localProj_val_eq_one hSi, mul_one]
    have e2 : localProj d.a d.b p (((scalarE d ℓ hℓ)⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) :
        GL2TF.Quat.BHat d.a d.b) =
        algebraMap ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] d.a d.b) (ratUnit p (ellUnit ℓ)⁻¹ : ℚ_[p]) := by
      have e : (scalarE d ℓ hℓ)⁻¹ =
          elemS d ℓ hℓ * iotaU d.a d.b (scalarUnit d.a d.b (ellUnit ℓ)⁻¹) := by
        unfold scalarE
        rw [mul_inv_rev, inv_inv, iotaU_scalarUnit_inv]
      rw [e, Units.val_mul, map_mul, localProj_iotaU_scalar, localProj_val_eq_one hSun, one_mul]
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact scalar_mem_localLattice d.O.1 p _ (norm_ratUnit_ellUnit h).le
    · rw [e2]
      exact scalar_mem_localLattice d.O.1 p _ (norm_ratUnit_ellUnit_inv h).le

end Scalar

/-- `def:s01-hecke` (`s01-hecke`): `e_ℓ ∈ U_0(M)` for `ℓ ∤ D M`. -/
theorem scalarE_mem_U0 (d : DefiniteData) {M : ℕ} (hM : M.Coprime d.D) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓD : ¬ ℓ ∣ d.D) (hℓM : ¬ ℓ ∣ M) : scalarE d ℓ hℓD ∈ d.U0 M hM := by
  refine DefiniteData.mem_U0_iff.2 ⟨scalarE_mem_Ohat d ℓ hℓD, fun q _ hq hD => ?_⟩
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    exact hℓM (Nat.dvd_of_mem_primeFactors hq)
  have hS : localComponent d q hD (elemS d ℓ hℓD)⁻¹ = 1 := by
    rw [map_inv]
    unfold elemS
    rw [localComponent_localEmbedGL_of_ne _ hqℓ, inv_one]
  unfold scalarE
  rw [map_mul, hS, mul_one, localComponent_iotaU_scalar]
  exact diagGL_mem_K0 _ (norm_ratUnit_ellUnit hqℓ) _

section SlInv

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `def:s01-hecke` (`s01-hecke`): a central `g = c · e` with `c ∈ B^×` central and `e ∈ U` acts trivially on `R^X`. -/
theorem heckeT_eq_id_of_global_central (g c : (GL2TF.Quat.BHat a b)ˣ) (hg : ∀ x, Commute g x)
    (hc : ∀ x, Commute c x) (hcg : c ∈ globalUnits a b) (he : c⁻¹ * g ∈ U)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) : heckeT U g R hfin = LinearMap.id := by
  refine LinearMap.ext fun f => funext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = y := ⟨_, DoubleCoset.out_eq' y⟩
  rw [heckeT_central_apply U R g hg hfin, LinearMap.id_apply]
  congr 1
  rw [DoubleCoset.eq]
  refine ⟨c⁻¹, (globalUnits a b).inv_mem hcg, (c⁻¹ * g)⁻¹, U.inv_mem he, ?_⟩
  have hx : c⁻¹ * x * c = x := by rw [mul_assoc, ← (hc x).eq, inv_mul_cancel_left]
  calc x = c⁻¹ * x * c := hx.symm
    _ = c⁻¹ * (x * g) * (c⁻¹ * g)⁻¹ := by group

/-- `def:s01-hecke` (`s01-hecke`): if `T_g = 1` on `R^X` then `T_g^t = 1` on `R[X]`. -/
theorem heckeTHom_eq_id_of_heckeT [Finite (XB U)] (g : (GL2TF.Quat.BHat a b)ˣ)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (h : heckeT U g R hfin = LinearMap.id) :
    heckeTHom U g R hfin = LinearMap.id :=
  LinearMap.ext fun x => zx_ext_of_evalPairing U R fun f => by
    simp only [heckeTHom_transpose, h, LinearMap.id_apply]

end SlInv

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): at level `U_0(M)` and `ℓ ∤ D M`, `S_ℓ⁻¹ = 1` on `R[X]`: `z_ℓ⁻¹` is the
product of the global central scalar `ι(ℓ)⁻¹` and `e_ℓ ∈ U_0(M)`. -/
theorem SlInvHom_U0 (d : DefiniteData) {M : ℕ} (hM : M.Coprime d.D) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D * M) (R : Type*) [CommRing R] [Finite (XB (d.U0 M hM))]
    (z : ZX (d.U0 M hM) R) :
    SlInvHom d (d.U0 M hM) ℓ (fun h => hℓ (h.mul_right M)) R z = z := by
  have hD : ¬ ℓ ∣ d.D := fun h => hℓ (h.mul_right M)
  have hM' : ¬ ℓ ∣ M := fun h => hℓ (h.mul_left d.D)
  have hzi : ∀ x, Commute (elemS d ℓ hD)⁻¹ x := fun x => (elemS_commute d ℓ hD x).inv_left
  have hc : ∀ x, Commute (iotaU d.a d.b (scalarUnit d.a d.b (ellUnit ℓ)))⁻¹ x := fun x =>
    (commute_iotaU_scalar _ x).inv_left
  have h1 := heckeT_eq_id_of_global_central (d.U0 M hM) R (elemS d ℓ hD)⁻¹
    (iotaU d.a d.b (scalarUnit d.a d.b (ellUnit ℓ)))⁻¹ hzi hc
    ((globalUnits d.a d.b).inv_mem (MonoidHom.mem_range.2 ⟨_, rfl⟩))
    (by rw [inv_inv]; exact scalarE_mem_U0 d hM ℓ hD hM')
    (relIndex_ne_zero_of_commute _ _ hzi)
  exact LinearMap.congr_fun (heckeTHom_eq_id_of_heckeT (d.U0 M hM) R _ _ h1) z

/-- `prop:s01-adjoint`(b) (`s01-adjoint`, "in particular"): at the level `U_0(M)` and a prime `ℓ ∤ D M`, `T_ℓ` is
self-adjoint for the Brandt pairing (trivial coefficients; `S_ℓ = 1` there, `SlInvHom_U0`). -/
theorem Tl_selfAdjoint_U0 (d : DefiniteData) {M : ℕ} (hM : M.Coprime d.D) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D * M) (R : Type*) [CommRing R] [Finite (XB (d.U0 M hM))]
    (hfin : (d.U0 M hM ⊓ conjSub (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M)))).relIndex
      (d.U0 M hM) ≠ 0)
    (hfin' : (d.U0 M hM ⊓ conjSub (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M)))⁻¹).relIndex
      (d.U0 M hM) ≠ 0)
    (x y : ZX (d.U0 M hM) R) :
    brandtPairing (d.U0 M hM) R
        (heckeTHom (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M))) R hfin x) y =
      brandtPairing (d.U0 M hM) R x
        (heckeTHom (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M))) R hfin y) := by
  have hD : ¬ ℓ ∣ d.D := fun h => hℓ (h.mul_right M)
  have hℓM : ℓ ∉ M.primeFactors := by
    intro h
    exact hℓ ((Nat.mem_primeFactors.1 h).2.1.mul_left d.D)
  exact Tl_selfAdjoint_of_SlInvHom d (d.U0 M hM) ℓ hD R
    (isInvariantAt_levelAt (hp := hD) (K := fun ℓ _ e => Langlandscape.Local.K0 ℓ e) hℓM) hfin hfin'
    (SlInvHom_U0 d hM ℓ hℓ R) x y

/-! ### `diamond_adjoint` -/

section Diamond

variable (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : ¬ ℓ ∣ d.D) (R : Type*) [CommRing R]

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): `⟨t⟩^* = ⟨t⟩⁻¹ = ⟨t⁻¹⟩` for the Brandt pairing, on `R[X]` (`⟨t⟩` as
`heckeTHom` of `δ_t`, `δ_t` normalizing `U` in the sense of `diamond`). -/
theorem diamond_adjoint [Finite (XB U)] (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U)
    (hn' : ∀ x ∈ U, (diamondElt d ℓ hℓ t⁻¹)⁻¹ * x * diamondElt d ℓ hℓ t⁻¹ ∈ U) (x y : ZX U R) :
    brandtPairing U R
        (heckeTHom U (diamondElt d ℓ hℓ t) R (relIndex_ne_zero_of_normalizing U _ hn) x) y =
      brandtPairing U R x
        (heckeTHom U (diamondElt d ℓ hℓ t⁻¹) R (relIndex_ne_zero_of_normalizing U _ hn') y) := by
  have e : diamondElt d ℓ hℓ t⁻¹ = (diamondElt d ℓ hℓ t)⁻¹ := diamondElt_inv d ℓ hℓ t
  have hfin' : (U ⊓ conjSub U (diamondElt d ℓ hℓ t)⁻¹).relIndex U ≠ 0 :=
    relIndex_ne_zero_of_normalizing U _ (fun x hx => by
      have h := hn' x hx
      rwa [e] at h)
  rw [brandtPairing_heckeTHom U (diamondElt d ℓ hℓ t) R _ hfin' x y,
    heckeTHom_congr U R e.symm hfin' (relIndex_ne_zero_of_normalizing U _ hn')]

/-- `def:s01-hecke`, `prop:s01-relations` (c) (`s01-hecke`): the diamond operator is the right translation
`translateLin U U δ_t`, `f ↦ f(· δ_t)`. -/
theorem diamond_eq_translateLin (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U) :
    diamond d U ℓ hℓ R t hn = translateLin R U U (diamondElt d ℓ hℓ t) := by
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [diamond_apply, translateLin_mk R hn]

/-- `lem:s01-stab` (b), `prop:s01-relations` (c) (`s01-stab`): the right translation `Quat.rightMulXB U g` of
`X_B(U)` is `translateMap U U g` (audit R7: one map, two names). -/
theorem rightMulXB_eq_translateMap (g : (GL2TF.Quat.BHat d.a d.b)ˣ) : rightMulXB U g = translateMap U U g :=
  rfl

end Diamond

/-! ### Tower maps are the generic level maps (audit R7) -/

section TowerGeneric

variable (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hN' : (M * p ^ (s + 1)).Coprime d.D)

omit [Fact (Nat.Prime p)] in
/-- `lem:s01-Up` (`s01-Up`): `towerMap` is the generic `levelMap` between `U_{s+1}` and `U_s` (audit R7: one map,
two names). -/
theorem towerMap_eq_levelMap :
    towerMap d M p s hN hN' = levelMap (d.Utower M p (s + 1) hN') (d.Utower M p s hN) :=
  rfl

omit [Fact (Nat.Prime p)] in
/-- `lem:s01-Up` (`s01-Up`): `towerPush` is the generic `pushforward` (audit R7), so `Up_comm_push` and
`normMap_pushforward` compose after rewriting with this lemma. -/
theorem towerPush_eq_pushforward (R : Type*) [CommRing R] :
    towerPush d M p s hN hN' R = pushforward (d.Utower M p (s + 1) hN') (d.Utower M p s hN) R :=
  rfl

end TowerGeneric

/-! ### `PiEll_adjoint` -/

section PiEllAdjoint

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `prop:s01-adjoint` (`s01-adjoint`): `Γ_{x g}(U) = Γ_x(U)` if `g` normalizes `U` (both inclusions). -/
theorem Gam_mul_normalizing (g : (GL2TF.Quat.BHat a b)ˣ) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (hg' : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (x : (GL2TF.Quat.BHat a b)ˣ) : Gam U (x * g) = Gam U x := by
  ext δ
  rw [mem_Gam_iff, mem_Gam_iff]
  constructor
  · intro h
    have h1 := hg' _ h
    have e : g * ((x * g)⁻¹ * iotaU a b δ * (x * g)) * g⁻¹ = x⁻¹ * iotaU a b δ * x := by group
    rwa [e] at h1
  · intro h
    have h1 := hg _ h
    have e : g⁻¹ * (x⁻¹ * iotaU a b δ * x) * g = (x * g)⁻¹ * iotaU a b δ * (x * g) := by group
    rwa [e] at h1

/-- `prop:s01-adjoint` (`s01-adjoint`): `w_{x g} = w_x` if `g` normalizes `U`. -/
theorem wx_mul_normalizing (g : (GL2TF.Quat.BHat a b)ˣ) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (hg' : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (x : (GL2TF.Quat.BHat a b)ˣ) : wx U (x * g) = wx U x := by
  rw [wx, wx, Gam_mul_normalizing U g hg hg' x]

/-- `prop:s01-adjoint` (`s01-adjoint`): the pushforward `R[X] → R[X]`, `[x] ↦ [x g]`, along `translateMap U U g`. -/
noncomputable def translateHom (g : (GL2TF.Quat.BHat a b)ˣ) : ZX U R →ₗ[R] ZX U R :=
  Finsupp.lmapDomain R R (translateMap U U g)

/-- `prop:s01-adjoint` (`s01-adjoint`): `translateHom (r [c]) = r [c g]`. -/
theorem translateHom_single (g : (GL2TF.Quat.BHat a b)ˣ) (c : XB U) (r : R) :
    translateHom U R g (Finsupp.single c r) = Finsupp.single (translateMap U U g c) r := by
  rw [translateHom, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- `prop:s01-adjoint` (`s01-adjoint`): transposition of `translateHom` and `translateLin`:
`⟨g_* a, f⟩ = ⟨a, f(· g)⟩` for the evaluation pairing. -/
theorem evalPairing_translateHom (g : (GL2TF.Quat.BHat a b)ˣ) (x : ZX U R) (f : ZXdual U R) :
    evalPairing U R (translateHom U R g x) f = evalPairing U R x (translateLin R U U g f) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | single c r =>
    rw [translateHom_single, evalPairing_single, evalPairing_single]
    rfl

/-- `prop:s01-adjoint` (`s01-adjoint`): for `g` normalizing `U`, `[x] ↦ [x g]` is adjoint to `[x] ↦ [x g⁻¹]` for the
Brandt pairing (the weights `w_x` are invariant under `x ↦ x g`). -/
theorem brandtPairing_translateHom (g : (GL2TF.Quat.BHat a b)ˣ) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (hg' : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (x y : ZX U R) :
    brandtPairing U R (translateHom U R g x) y = brandtPairing U R x (translateHom U R g⁻¹ y) := by
  have hg'' : ∀ u ∈ U, g⁻¹⁻¹ * u * g⁻¹ ∈ U := fun u hu => by
    rw [inv_inv]
    exact hg' u hu
  have hφψ : ∀ c : XB U, translateMap U U g⁻¹ (translateMap U U g c) = c := by
    intro c
    obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
    rw [translateMap_mk hg, translateMap_mk hg'', mul_inv_cancel_right]
  have hψφ : ∀ c : XB U, translateMap U U g (translateMap U U g⁻¹ c) = c := by
    intro c
    obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
    rw [translateMap_mk hg'', translateMap_mk hg, inv_mul_cancel_right]
  have hw : ∀ c : XB U, wx U (Quotient.out (translateMap U U g c)) = wx U (Quotient.out c) := by
    intro c
    have e : translateMap U U g c = DoubleCoset.mk (globalUnits a b) U (Quotient.out c * g) := rfl
    rw [e, wx_out, wx_mul_normalizing U g hg hg']
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single c r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single c' s =>
      rw [translateHom_single, translateHom_single, brandtPairing_single_single,
        brandtPairing_single_single]
      by_cases h : translateMap U U g c = c'
      · have h2 : c = translateMap U U g⁻¹ c' := by rw [← h, hφψ]
        rw [if_pos h, if_pos h2, hw]
      · have h2 : ¬ c = translateMap U U g⁻¹ c' := fun h2 => h (by rw [h2, hψφ])
        rw [if_neg h, if_neg h2]

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `def:s01-hecke` (`s01-hecke`): the Atkin–Lehner operator `Π_ℓ` on `R[X]`, `[x] ↦ [x · localEmbed ℓ Π]` (the
transpose of `PiEll`, see `evalPairing_translateHom`). -/
noncomputable def PiEllHom (hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)
    (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) : ZX U R →ₗ[R] ZX U R :=
  translateHom U R (localEmbed d.a d.b ℓ P)

/-- `def:s01-hecke` (`s01-hecke`): `⟨Π_ℓ a, f⟩ = ⟨a, Π_ℓ f⟩` for the evaluation pairing (`PiEll` on `R^X`). -/
theorem PiEllHom_transpose (hℓ : ℓ ∣ d.D) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ)
    (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (x : ZX U R) (f : ZXdual U R) :
    evalPairing U R (PiEllHom R d ℓ hℓ P U x) f = evalPairing U R x (PiEll R d U ℓ hℓ P f) :=
  evalPairing_translateHom U R _ x f

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): `Π_ℓ^* = Π_ℓ^{-1}` for the Brandt pairing, at every level `U` maximal
at `ℓ ∣ D`, on `R[X]`. -/
theorem PiEll_adjoint (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (x y : ZX U R) :
    brandtPairing U R (PiEllHom R d ℓ hℓ P U x) y = brandtPairing U R x (PiEllHom R d ℓ hℓ P⁻¹ U y) := by
  unfold PiEllHom
  rw [map_inv]
  exact brandtPairing_translateHom U R (localEmbed d.a d.b ℓ P) (hU.inv_conj_mem P)
    (fun u hu => hU.conj_mem P hu) x y

end PiEllAdjoint

/-! ### `Up_comm_*`: commutation of `U_p` with the operators away from `p` -/

section UpComm

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hp : ¬ p ∣ d.D} (R : Type*) [CommRing R]

/-- `lem:s01-Up`(e) (`s01-Up`): the tower level `U_s` splits at every split prime `ℓ ∤ M p`. -/
theorem splitAt_Utower_of_ne {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    SplitAt (d.Utower M p s hN) ℓ := by
  have hpN : ℓ ∉ (M * p ^ s).primeFactors := by
    intro h
    obtain ⟨-, hd, -⟩ := Nat.mem_primeFactors.1 h
    rcases (Fact.out : ℓ.Prime).dvd_mul.1 hd with h1 | h1
    · exact hℓM h1
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).1
        ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h1))
  exact splitAt_levelAt_of_notMem (K := fun ℓ _ e => K1 ℓ e) (hN := hN) hpN hℓ

omit [Fact (Nat.Prime p)] in
/-- `lem:s01-Up`(e) (`s01-Up`): the tower level `U_s = U_1(M p^s)` splits at every split prime `ℓ`: at
`ℓ ∣ M p` by `splitAt_U1`, at `ℓ ∤ M p` by `splitAt_levelAt_of_notMem`. -/
theorem splitAt_Utower_of_split {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) :
    SplitAt (d.Utower M p s hN) ℓ := by
  by_cases h : ℓ ∈ (M * p ^ s).primeFactors
  · exact splitAt_U1 (hN := hN) h hℓ
  · exact splitAt_levelAt_of_notMem (K := fun ℓ _ e => K1 ℓ e) (hN := hN) h hℓ

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with `T_g` for `g` supported at a split prime `ℓ ≠ p` (including
`ℓ ∣ M`). -/
theorem Up_comm_heckeT {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓp : ℓ ≠ p)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {g : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hg : g ∈ (localEmbed d.a d.b ℓ).range)
    (hfin : (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) g).relIndex (d.Utower M p s hN) ≠ 0) :
    Up d M p s hN hp hM hpM hs R ∘ₗ heckeT (d.Utower M p s hN) g R hfin =
      heckeT (d.Utower M p s hN) g R hfin ∘ₗ Up d M p s hN hp hM hpM hs R :=
  heckeT_comm_of_disjoint (d.Utower M p s hN) R hℓp.symm (splitAt_Utower hM hpM hs hp)
    (splitAt_Utower_of_split hℓ) (localEmbedGL_mem_range _) hg (Up_relIndex_ne_zero hM hpM hs) hfin

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with `T_ℓ` (`ℓ ∤ M p D`) and with `U_ℓ` (`ℓ ∣ M`, same element),
`ℓ ≠ p`. -/
theorem Up_comm_Tl {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓp : ℓ ≠ p)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (hfin : (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemT d ℓ hℓ)).relIndex
      (d.Utower M p s hN) ≠ 0) :
    Up d M p s hN hp hM hpM hs R ∘ₗ Tl d (d.Utower M p s hN) ℓ hℓ R hfin =
      Tl d (d.Utower M p s hN) ℓ hℓ R hfin ∘ₗ Up d M p s hN hp hM hpM hs R :=
  Up_comm_heckeT (hp := hp) R hℓ hℓp hM hpM hs (localEmbedGL_mem_range _) hfin

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with `S_ℓ`, `ℓ ∤ p D`. -/
theorem Up_comm_Sl {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓp : ℓ ≠ p)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (hfin : (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemS d ℓ hℓ)).relIndex
      (d.Utower M p s hN) ≠ 0) :
    Up d M p s hN hp hM hpM hs R ∘ₗ Sl d (d.Utower M p s hN) ℓ hℓ R hfin =
      Sl d (d.Utower M p s hN) ℓ hℓ R hfin ∘ₗ Up d M p s hN hp hM hpM hs R :=
  Up_comm_heckeT (hp := hp) R hℓ hℓp hM hpM hs (localEmbedGL_mem_range _) hfin

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with the local factor `⟨t⟩ = diamond … ℓ … t` of the diamond
operators at a split prime `ℓ ≠ p`. The interesting case is `ℓ ∣ M` (`hn` from `diamondElt_inv_normalizes_U1`);
for `ℓ ∤ M p` the operator is the identity (`diamond_eq_id_of_mem`). For `ℓ = p` see `Up_comm_diamond_self`. -/
theorem Up_comm_diamond {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓp : ℓ ≠ p)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ d.Utower M p s hN,
      (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.Utower M p s hN) :
    Up d M p s hN hp hM hpM hs R ∘ₗ diamond d (d.Utower M p s hN) ℓ hℓ R t hn =
      diamond d (d.Utower M p s hN) ℓ hℓ R t hn ∘ₗ Up d M p s hN hp hM hpM hs R :=
  Up_comm_heckeT (hp := hp) R hℓ hℓp hM hpM hs (localEmbedGL_mem_range _)
    (relIndex_ne_zero_of_normalizing _ _ hn)

/-- `lem:s01-Up`(e) (`s01-Up`): `diag(1, t)` commutes with `ϖ = diag(p, 1)` in `GL₂(ℚ_p)`. -/
theorem deltaLoc_commute_varpiDiag (t : ℤ_[p]ˣ) : Commute (deltaLoc p t) (Langlandscape.Local.varpiDiag p) := by
  show deltaLoc p t * Langlandscape.Local.varpiDiag p = Langlandscape.Local.varpiDiag p * deltaLoc p t
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deltaLoc, Langlandscape.Local.varpiDiag, Matrix.mul_apply, Fin.sum_univ_two]

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with the diamond operator `⟨t⟩` at `p` itself, `t ∈ ℤ_p^×`
(`hn` from `diamondElt_inv_normalizes_Utower`): `δ_t` normalises `U_s` and commutes with `ϖ`, so
`heckeT_comm_translate` applies to `⟨t⟩ = translateLin U_s U_s δ_t` (`diamond_eq_translateLin`). -/
theorem Up_comm_diamond_self (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : ℤ_[p]ˣ)
    (hn : ∀ x ∈ d.Utower M p s hN,
      (diamondElt d p hp t)⁻¹ * x * diamondElt d p hp t ∈ d.Utower M p s hN) :
    Up d M p s hN hp hM hpM hs R ∘ₗ diamond d (d.Utower M p s hN) p hp R t hn =
      diamond d (d.Utower M p s hN) p hp R t hn ∘ₗ Up d M p s hN hp hM hpM hs R := by
  rw [diamond_eq_translateLin]
  exact heckeT_comm_translate R (d.Utower M p s hN) (d.Utower M p s hN) (diamondElt d p hp t)
    (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p)) hn
    (fun _ hu => deltaElt_normalizes hM hpM hs t hu)
    ((deltaLoc_commute_varpiDiag t).map (localEmbedGL d p hp))
    (Up_relIndex_ne_zero hM hpM hs) (Up_relIndex_ne_zero hM hpM hs)

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with the Atkin–Lehner operators `Π_ℓ`, `ℓ ∣ D`. -/
theorem Up_comm_PiEll {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ∣ d.D)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    Up d M p s hN hp hM hpM hs R ∘ₗ PiEll R d (d.Utower M p s hN) ℓ hℓ P =
      PiEll R d (d.Utower M p s hN) ℓ hℓ P ∘ₗ Up d M p s hN hp hM hpM hs R := by
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact hp hℓ
  exact heckeT_comm_PiEll R hℓ (isMaximalAt_Utower hℓ) P _
    (localProjUnits_localEmbedGL_of_ne (hp := hp) _ hℓp) (Up_relIndex_ne_zero hM hpM hs)

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with right translation by `g = localEmbed q y ∈ B_q^×`, `q ≠ p`
(`hfinV` is the finiteness of `ϖ` at the conjugated level `g⁻¹ U g`). -/
theorem Up_comm_rightTranslate {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (y : (QuatAlg ℚ_[q] d.a d.b)ˣ)
    (hfinV : (rightConj (d.Utower M p s hN) (localEmbed d.a d.b q y) ⊓
        conjSub (rightConj (d.Utower M p s hN) (localEmbed d.a d.b q y))
          (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p))).relIndex
      (rightConj (d.Utower M p s hN) (localEmbed d.a d.b q y)) ≠ 0) :
    (Up d M p s hN hp hM hpM hs R).comp (rightTranslateLin R (d.Utower M p s hN) (localEmbed d.a d.b q y)) =
      (rightTranslateLin R (d.Utower M p s hN) (localEmbed d.a d.b q y)).comp
        (heckeT (rightConj (d.Utower M p s hN) (localEmbed d.a d.b q y))
          (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p)) R hfinV) :=
  heckeT_comm_rightTranslate_localEmbed R (d.Utower M p s hN) y _
    (localProjUnits_localEmbedGL_of_ne (hp := hp) _ hqp) (Up_relIndex_ne_zero hM hpM hs)

end UpComm

end Langlandscape.Brandt
