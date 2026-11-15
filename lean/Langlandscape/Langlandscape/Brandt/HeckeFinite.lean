/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Corollaries
import Langlandscape.Brandt.ImportDictionary
import Langlandscape.Quat.LevelFinite

/-!
# Finiteness of the double cosets of `T_ℓ` at the standard levels (S01-L16a, audit fix R1)

`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-hecke`, `prop:s01-adjoint`(b).

The operators `T_ℓ = [U ϖ_ℓ U]` (`Tl`, `heckeTHom … (elemT …)`) take the finiteness hypothesis
`[U : U ∩ ϖ_ℓ U ϖ_ℓ⁻¹] ≠ 0`; here it is proved, for `ϖ_ℓ` and `ϖ_ℓ⁻¹`, at every level `U ≤ Ô^×` invariant at the
split prime `ℓ` (`IsInvariantAt`), so at `Ô^×`, `levelAt d N hN K` (`ℓ ∤ N`), `U_0(N)`, `U_1(N)` (`ℓ ∤ N`) and the tower
`U_s` (`ℓ ∤ M`, `ℓ ≠ p`).

* `Local.cartanRep`, `Local.exists_cartanRep_inv_mul` : `GL₂(ℤ_ℓ) ϖ ⊆ ⋃_{j ∈ Option (Fin ℓ)} r_j GL₂(ℤ_ℓ)` with
  `r_j = !![ℓ, j; 0, 1]` and `r_none = diag(1, ℓ)` (half of the Cartan decomposition, `ϖ = diag(ℓ, 1)`).
* `relIndex_ne_zero_of_cover` : if `U g ⊆ ⋃_{j ∈ ι} r_j U` with `ι` finite, then `[U : U ∩ g U g⁻¹] ≠ 0`;
  `cover_conj_central` : the same for `w (z g) w⁻¹` (`w ∈ U`, `z` central).
* `relIndex_elemT_ne_zero`, `relIndex_elemT_inv_ne_zero` and the instances `…_Ohat`, `…_levelAt`, `…_U0`, `…_U1`,
  `…_Utower`.
* Consumers without a free `hfin`: `Tl_adjoint'`, `Tl_selfAdjoint_U0'`, `Tl_selfAdjoint_units'`, `Up_comm_Tl'`.

Not covered: `U_ℓ` at a level with `ℓ ∣ N` (the local level there is `K0`/`K1`, not `GL₂(ℤ_ℓ)`).

Status: *formalized*.
-/

open Matrix

namespace Langlandscape.Local

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (ℓ) in
/-- The representatives of `GL₂(ℤ_ℓ) diag(ℓ, 1) GL₂(ℤ_ℓ) / GL₂(ℤ_ℓ)`: `some j ↦ !![ℓ, j; 0, 1]`,
`none ↦ diag(1, ℓ)` (`def:s01-hecke`). -/
noncomputable def cartanRep : Option (Fin ℓ) → GL (Fin 2) ℚ_[ℓ]
  | none => diagOneP ℓ
  | some j => varpi ℓ j

/-- `def:s01-hecke` (`s01-hecke`): for `k ∈ GL₂(ℤ_ℓ)` there is a representative `r` with
`r⁻¹ k diag(ℓ, 1) ∈ GL₂(ℤ_ℓ)`. -/
theorem exists_cartanRep_inv_mul {k : GL (Fin 2) ℚ_[ℓ]} (hk : k ∈ GL2Zl ℓ) :
    ∃ j : Option (Fin ℓ), (cartanRep ℓ j)⁻¹ * (k * varpiDiag ℓ) ∈ GL2Zl ℓ := by
  have hkdet : ‖(Units.val k).det‖ = 1 := (mem_GL2Zl_iff.1 hk).2
  obtain ⟨a, b, c, d, hM, -⟩ := mem_GL2Zl_iff_exists.1 hk
  by_cases hd : IsUnit d
  · obtain ⟨j, β, hβ⟩ := exists_fin_dvd d b hd
    have hb : b = (ℓ : ℤ_[ℓ]) * β + ((j : ℕ) : ℤ_[ℓ]) * d := by linear_combination hβ
    subst hb
    have H : Units.val (varpi ℓ j) *
        !![((a - ((j : ℕ) : ℤ_[ℓ]) * c : ℤ_[ℓ]) : ℚ_[ℓ]), (β : ℚ_[ℓ]);
          (((ℓ : ℤ_[ℓ]) * c : ℤ_[ℓ]) : ℚ_[ℓ]), (d : ℚ_[ℓ])] = Units.val (k * varpiDiag ℓ) := by
      rw [Units.val_mul, hM]
      simp only [varpi, varpiDiag, matGL_val, Matrix.mul_fin_two]
      refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
    have hdet : ‖(Units.val (varpi ℓ j)).det‖ = ‖(Units.val (k * varpiDiag ℓ)).det‖ := by
      rw [Units.val_mul, Matrix.det_mul, norm_mul, hkdet, one_mul]
      simp [varpi, varpiDiag, Matrix.det_fin_two_of]
    refine ⟨some j, ?_⟩
    show (varpi ℓ j)⁻¹ * (k * varpiDiag ℓ) ∈ GL2Zl ℓ
    exact mem_GL2Zl_of_entries _ _ _ _ (val_inv_mul_eq H) (isUnit_of_mul_eq H hdet)
  · have hpd : (ℓ : ℤ_[ℓ]) ∣ d := by
      by_contra h
      exact hd ((isUnit_iff_not_dvd d).2 h)
    obtain ⟨δ, rfl⟩ := hpd
    have H : Units.val (diagOneP ℓ) *
        !![(((ℓ : ℤ_[ℓ]) * a : ℤ_[ℓ]) : ℚ_[ℓ]), (b : ℚ_[ℓ]); (c : ℚ_[ℓ]), (δ : ℚ_[ℓ])] =
        Units.val (k * varpiDiag ℓ) := by
      rw [Units.val_mul, hM]
      simp only [diagOneP, varpiDiag, matGL_val, Matrix.mul_fin_two]
      refine mat_eq ?_ ?_ ?_ ?_ <;> push_cast <;> ring
    have hdet : ‖(Units.val (diagOneP ℓ)).det‖ = ‖(Units.val (k * varpiDiag ℓ)).det‖ := by
      rw [Units.val_mul, Matrix.det_mul, norm_mul, hkdet, one_mul]
      simp [diagOneP, varpiDiag, Matrix.det_fin_two_of]
    refine ⟨none, ?_⟩
    show (diagOneP ℓ)⁻¹ * (k * varpiDiag ℓ) ∈ GL2Zl ℓ
    exact mem_GL2Zl_of_entries _ _ _ _ (val_inv_mul_eq H) (isUnit_of_mul_eq H hdet)

end Langlandscape.Local

namespace Langlandscape.Brandt

open Langlandscape.Quat
open Langlandscape.Local (GL2Zl K0 K1 diagGL varpiDiag cartanRep exists_cartanRep_inv_mul)
open scoped Classical

/-! ### Finiteness from a finite covering by cosets -/

section Cover

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-hecke` (`s01-hecke`): if `U g ⊆ ⋃_{j ∈ ι} r_j U` for a finite family `r`, then
`[U : U ∩ g U g⁻¹] ≠ 0` (the cosets `u (U ∩ g U g⁻¹)` are separated by the index `j` of `r_j U ∋ u g`). -/
theorem relIndex_ne_zero_of_cover (g : (GL2TF.Quat.BHat a b)ˣ) {ι : Type*} [Finite ι]
    (r : ι → (GL2TF.Quat.BHat a b)ˣ) (hr : ∀ u ∈ U, ∃ j, (r j)⁻¹ * (u * g) ∈ U) :
    (U ⊓ conjSub U g).relIndex U ≠ 0 := by
  have hcov : ∀ u : ↥U, ∃ j, (r j)⁻¹ * ((u : (GL2TF.Quat.BHat a b)ˣ) * g) ∈ U :=
    fun u => hr u u.2
  choose F hF using hcov
  have hfin : Finite (↥U ⧸ (U ⊓ conjSub U g).subgroupOf U) := by
    refine Finite.of_injective (β := ι) (fun q => F (Quotient.out q)) ?_
    intro q q' hqq'
    have hqq'' : F (Quotient.out q) = F (Quotient.out q') := hqq'
    have h1 := hF (Quotient.out q)
    have h2 := hF (Quotient.out q')
    rw [hqq''] at h1
    have h3 := conj_inv_mul_mem_of_inv_mul_mem h1 h2
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (Quotient.out q).2) (Quotient.out q').2, ?_⟩
    exact (mem_conjSub _ _).2 h3
  exact Subgroup.index_ne_zero_of_finite (hH := hfin)

/-- `def:s01-hecke` (`s01-hecke`): a covering `U g ⊆ ⋃ r_j U` gives the covering
`U (w (z g) w⁻¹) ⊆ ⋃ (w (z r_j) w⁻¹) U` for `w ∈ U` and `z` central. -/
theorem cover_conj_central (g w z : (GL2TF.Quat.BHat a b)ˣ) (hw : w ∈ U) (hz : ∀ x, Commute z x)
    {ι : Type*} (r : ι → (GL2TF.Quat.BHat a b)ˣ) (hr : ∀ u ∈ U, ∃ j, (r j)⁻¹ * (u * g) ∈ U) :
    ∀ u ∈ U, ∃ j, (w * (z * r j) * w⁻¹)⁻¹ * (u * (w * (z * g) * w⁻¹)) ∈ U := by
  intro u hu
  have hv : w⁻¹ * u * w ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hw) hu) hw
  obtain ⟨j, hj⟩ := hr _ hv
  refine ⟨j, ?_⟩
  have hz' : z⁻¹ * (w⁻¹ * u * w) * z = w⁻¹ * u * w := by
    rw [(hz (w⁻¹ * u * w)).inv_left.eq, inv_mul_cancel_right]
  have e : (w * (z * r j) * w⁻¹)⁻¹ * (u * (w * (z * g) * w⁻¹)) =
      w * ((r j)⁻¹ * (z⁻¹ * (w⁻¹ * u * w) * z * g)) * w⁻¹ := by group
  rw [e, hz']
  exact U.mul_mem (U.mul_mem hw hj) (U.inv_mem hw)

end Cover

/-- `def:s01-hecke` (`s01-hecke`), group identity: if `u K⁻¹` commutes with `R`, then
`R⁻¹ (u P) = (u K⁻¹) (R⁻¹ (K P))`. -/
theorem inv_mul_mul_eq_of_commute_aux {G : Type*} [Group G] {u K R P : G} (hc : Commute (u * K⁻¹) R) :
    R⁻¹ * (u * P) = u * K⁻¹ * (R⁻¹ * (K * P)) := by
  have hc' : u * K⁻¹ * R⁻¹ = R⁻¹ * (u * K⁻¹) := hc.inv_right.eq
  calc R⁻¹ * (u * P) = R⁻¹ * (u * K⁻¹) * K * P := by group
    _ = u * K⁻¹ * R⁻¹ * K * P := by rw [hc']
    _ = u * K⁻¹ * (R⁻¹ * (K * P)) := by group

/-! ### `ϖ_ℓ` and `ϖ_ℓ⁻¹` at a level invariant at `ℓ` -/

/-- `def:s01-hecke` (`s01-hecke`): `diag(ℓ, 1) = ϖ` (`varpiDiag`, the element of S01-L9). -/
theorem diagGL_padicUnit_one {ℓ : ℕ} [Fact ℓ.Prime] : diagGL (padicUnit ℓ) 1 = varpiDiag ℓ := by
  exact Units.ext rfl

section ElemT

variable (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-hecke` (`s01-hecke`): `ϖ_ℓ = ι_ℓ⁻¹ diag(ℓ, 1)` is `localEmbedGL ℓ (varpiDiag ℓ)`. -/
theorem elemT_eq_localEmbedGL_varpiDiag : elemT d ℓ hℓ = localEmbedGL d ℓ hℓ (varpiDiag ℓ) :=
  congrArg (localEmbedGL d ℓ hℓ) (diagGL_padicUnit_one (ℓ := ℓ))

/-- `def:s01-hecke` (`s01-hecke`): `ϖ_ℓ⁻¹ = w (z_ℓ⁻¹ ϖ_ℓ) w⁻¹` with `w` the Weyl element at `ℓ`. -/
theorem elemT_inv_conj :
    (elemT d ℓ hℓ)⁻¹ = localEmbedGL d ℓ hℓ (weylGL ℓ) *
      ((elemS d ℓ hℓ)⁻¹ * elemT d ℓ hℓ) * (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by
  have hzi : ∀ x, Commute (elemS d ℓ hℓ)⁻¹ x := fun x => (elemS_commute d ℓ hℓ x).inv_left
  rw [elemT_inv_eq d ℓ hℓ]
  have hc := (hzi (localEmbedGL d ℓ hℓ (weylGL ℓ))).eq
  calc (elemS d ℓ hℓ)⁻¹ * (localEmbedGL d ℓ hℓ (weylGL ℓ) * elemT d ℓ hℓ *
        (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹)
      = ((elemS d ℓ hℓ)⁻¹ * localEmbedGL d ℓ hℓ (weylGL ℓ)) * elemT d ℓ hℓ *
        (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by group
    _ = (localEmbedGL d ℓ hℓ (weylGL ℓ) * (elemS d ℓ hℓ)⁻¹) * elemT d ℓ hℓ *
        (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹ := by rw [hc]
    _ = _ := by group

/-- `def:s01-hecke` (`s01-hecke`): at a level `U ≤ Ô^×` invariant at `ℓ`, `U ϖ_ℓ ⊆ ⋃_j ι_ℓ⁻¹(r_j) U` for the
`ℓ + 1` representatives `cartanRep ℓ j`. -/
theorem elemT_cover (hU : IsInvariantAt d ℓ hℓ U) (hO : U ≤ d.Ohat) :
    ∀ u ∈ U, ∃ j : Option (Fin ℓ),
      (localEmbedGL d ℓ hℓ (cartanRep ℓ j))⁻¹ * (u * elemT d ℓ hℓ) ∈ U := by
  intro u hu
  have hk : localComponent d ℓ hℓ u ∈ GL2Zl ℓ := localComponent_mem_GL2Zl (hℓ := hℓ) (hO hu)
  obtain ⟨j, hj⟩ := exists_cartanRep_inv_mul hk
  refine ⟨j, ?_⟩
  have haway : awayAt d ℓ hℓ u ∈ U := hU u hu _ (inv_mem hk)
  have hc : Commute (u * (localEmbedGL d ℓ hℓ (localComponent d ℓ hℓ u))⁻¹)
      (localEmbedGL d ℓ hℓ (cartanRep ℓ j)) := by
    have h := commute_awayAt_localEmbedGL (hp := hℓ) u (cartanRep ℓ j)
    rwa [awayAt, map_inv] at h
  have e : (localEmbedGL d ℓ hℓ (cartanRep ℓ j))⁻¹ * (u * elemT d ℓ hℓ) =
      awayAt d ℓ hℓ u *
        localEmbedGL d ℓ hℓ ((cartanRep ℓ j)⁻¹ * (localComponent d ℓ hℓ u * varpiDiag ℓ)) := by
    rw [awayAt, elemT_eq_localEmbedGL_varpiDiag d ℓ hℓ]
    simp only [map_mul, map_inv]
    exact inv_mul_mul_eq_of_commute_aux hc
  rw [e]
  exact hU _ haway _ hj

/-- `def:s01-hecke` (`s01-hecke`): `[U : U ∩ ϖ_ℓ U ϖ_ℓ⁻¹] ≠ 0` (it is at most `ℓ + 1`) for every level `U ≤ Ô^×`
invariant at the split prime `ℓ`; the finiteness hypothesis of `T_ℓ`. -/
theorem relIndex_elemT_ne_zero (hU : IsInvariantAt d ℓ hℓ U) (hO : U ≤ d.Ohat) :
    (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0 :=
  relIndex_ne_zero_of_cover U (elemT d ℓ hℓ) (fun j => localEmbedGL d ℓ hℓ (cartanRep ℓ j))
    (elemT_cover d U ℓ hℓ hU hO)

/-- `def:s01-hecke` (`s01-hecke`): `[U : U ∩ ϖ_ℓ⁻¹ U ϖ_ℓ] ≠ 0` for every level `U ≤ Ô^×` invariant at the split
prime `ℓ` (from `ϖ_ℓ⁻¹ = w (z_ℓ⁻¹ ϖ_ℓ) w⁻¹`, `w ∈ U`). -/
theorem relIndex_elemT_inv_ne_zero (hU : IsInvariantAt d ℓ hℓ U) (hO : U ≤ d.Ohat) :
    (U ⊓ conjSub U (elemT d ℓ hℓ)⁻¹).relIndex U ≠ 0 := by
  have hw : localEmbedGL d ℓ hℓ (weylGL ℓ) ∈ U := by
    have h := hU 1 U.one_mem (weylGL ℓ) weylGL_mem
    rwa [one_mul] at h
  have hzi : ∀ x, Commute (elemS d ℓ hℓ)⁻¹ x := fun x => (elemS_commute d ℓ hℓ x).inv_left
  rw [elemT_inv_conj d ℓ hℓ]
  exact relIndex_ne_zero_of_cover U _
    (fun j => localEmbedGL d ℓ hℓ (weylGL ℓ) *
      ((elemS d ℓ hℓ)⁻¹ * localEmbedGL d ℓ hℓ (cartanRep ℓ j)) * (localEmbedGL d ℓ hℓ (weylGL ℓ))⁻¹)
    (cover_conj_central U (elemT d ℓ hℓ) _ _ hw hzi (fun j => localEmbedGL d ℓ hℓ (cartanRep ℓ j))
      (elemT_cover d U ℓ hℓ hU hO))

end ElemT

/-! ### The standard levels -/

section Levels

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ` at `Ô^×`. -/
theorem relIndex_elemT_ne_zero_Ohat : (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)).relIndex d.Ohat ≠ 0 :=
  relIndex_elemT_ne_zero d d.Ohat ℓ hℓ (isInvariantAt_Ohat (hp := hℓ)) le_rfl

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ⁻¹` at `Ô^×`. -/
theorem relIndex_elemT_inv_ne_zero_Ohat :
    (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)⁻¹).relIndex d.Ohat ≠ 0 :=
  relIndex_elemT_inv_ne_zero d d.Ohat ℓ hℓ (isInvariantAt_Ohat (hp := hℓ)) le_rfl

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ` at a generic level `levelAt d N hN K`, `ℓ ∤ N`. -/
theorem relIndex_elemT_ne_zero_levelAt {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hℓN : ℓ ∉ N.primeFactors) :
    (d.levelAt N hN K ⊓ conjSub (d.levelAt N hN K) (elemT d ℓ hℓ)).relIndex (d.levelAt N hN K) ≠ 0 :=
  relIndex_elemT_ne_zero d _ ℓ hℓ (isInvariantAt_levelAt (hp := hℓ) hℓN)
    fun _ hu => (DefiniteData.mem_levelAt_iff.1 hu).1

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ⁻¹` at a generic level `levelAt d N hN K`, `ℓ ∤ N`. -/
theorem relIndex_elemT_inv_ne_zero_levelAt {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hℓN : ℓ ∉ N.primeFactors) :
    (d.levelAt N hN K ⊓ conjSub (d.levelAt N hN K) (elemT d ℓ hℓ)⁻¹).relIndex (d.levelAt N hN K) ≠ 0 :=
  relIndex_elemT_inv_ne_zero d _ ℓ hℓ (isInvariantAt_levelAt (hp := hℓ) hℓN)
    fun _ hu => (DefiniteData.mem_levelAt_iff.1 hu).1

omit [Fact (Nat.Prime ℓ)] in
/-- `def:s01-hecke` (`s01-hecke`): `ℓ ∤ N` gives `ℓ ∉ N.primeFactors`. -/
theorem notMem_primeFactors_of_not_dvd_aux {N : ℕ} (hℓN : ¬ ℓ ∣ N) : ℓ ∉ N.primeFactors :=
  fun h => hℓN (Nat.dvd_of_mem_primeFactors h)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ` at `U_0(N)`, `ℓ ∤ D N`. -/
theorem relIndex_elemT_ne_zero_U0 {N : ℕ} {hN : N.Coprime d.D} (hℓN : ¬ ℓ ∣ N) :
    (d.U0 N hN ⊓ conjSub (d.U0 N hN) (elemT d ℓ hℓ)).relIndex (d.U0 N hN) ≠ 0 :=
  relIndex_elemT_ne_zero_levelAt d ℓ hℓ (N := N) (hN := hN)
    (K := fun ℓ _ e => Langlandscape.Local.K0 ℓ e) (notMem_primeFactors_of_not_dvd_aux ℓ hℓN)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ⁻¹` at `U_0(N)`, `ℓ ∤ D N`. -/
theorem relIndex_elemT_inv_ne_zero_U0 {N : ℕ} {hN : N.Coprime d.D} (hℓN : ¬ ℓ ∣ N) :
    (d.U0 N hN ⊓ conjSub (d.U0 N hN) (elemT d ℓ hℓ)⁻¹).relIndex (d.U0 N hN) ≠ 0 :=
  relIndex_elemT_inv_ne_zero_levelAt d ℓ hℓ (N := N) (hN := hN)
    (K := fun ℓ _ e => Langlandscape.Local.K0 ℓ e) (notMem_primeFactors_of_not_dvd_aux ℓ hℓN)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ` at `U_1(N)`, `ℓ ∤ D N`. -/
theorem relIndex_elemT_ne_zero_U1 {N : ℕ} {hN : N.Coprime d.D} (hℓN : ¬ ℓ ∣ N) :
    (d.U1 N hN ⊓ conjSub (d.U1 N hN) (elemT d ℓ hℓ)).relIndex (d.U1 N hN) ≠ 0 :=
  relIndex_elemT_ne_zero_levelAt d ℓ hℓ (N := N) (hN := hN)
    (K := fun ℓ _ e => Langlandscape.Local.K1 ℓ e) (notMem_primeFactors_of_not_dvd_aux ℓ hℓN)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ⁻¹` at `U_1(N)`, `ℓ ∤ D N`. -/
theorem relIndex_elemT_inv_ne_zero_U1 {N : ℕ} {hN : N.Coprime d.D} (hℓN : ¬ ℓ ∣ N) :
    (d.U1 N hN ⊓ conjSub (d.U1 N hN) (elemT d ℓ hℓ)⁻¹).relIndex (d.U1 N hN) ≠ 0 :=
  relIndex_elemT_inv_ne_zero_levelAt d ℓ hℓ (N := N) (hN := hN)
    (K := fun ℓ _ e => Langlandscape.Local.K1 ℓ e) (notMem_primeFactors_of_not_dvd_aux ℓ hℓN)

/-- `def:s01-hecke` (`s01-hecke`): `ℓ ∤ M`, `ℓ ≠ p` (primes) give `ℓ ∤ M p^s`. -/
theorem not_dvd_mul_pow_aux {M p s : ℕ} [Fact p.Prime] (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    ¬ ℓ ∣ M * p ^ s := by
  intro hd
  rcases (Fact.out : ℓ.Prime).dvd_mul.1 hd with h1 | h1
  · exact hℓM h1
  · exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).1
      ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h1))

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ` at the tower level `U_s`, `ℓ ∤ D M`, `ℓ ≠ p`. -/
theorem relIndex_elemT_ne_zero_Utower {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
    (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemT d ℓ hℓ)).relIndex (d.Utower M p s hN) ≠ 0 :=
  relIndex_elemT_ne_zero_U1 d ℓ hℓ (N := M * p ^ s) (hN := hN) (not_dvd_mul_pow_aux ℓ hℓM hℓp)

/-- `def:s01-hecke` (`s01-hecke`): the finiteness for `ϖ_ℓ⁻¹` at the tower level `U_s`, `ℓ ∤ D M`, `ℓ ≠ p`. -/
theorem relIndex_elemT_inv_ne_zero_Utower {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
    (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemT d ℓ hℓ)⁻¹).relIndex
      (d.Utower M p s hN) ≠ 0 :=
  relIndex_elemT_inv_ne_zero_U1 d ℓ hℓ (N := M * p ^ s) (hN := hN) (not_dvd_mul_pow_aux ℓ hℓM hℓp)

end Levels

/-! ### Consumers without a free `hfin` -/

section Consumers

variable (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : ¬ ℓ ∣ d.D) (R : Type*) [CommRing R]

/-- `prop:s01-adjoint`(b) (`s01-adjoint`): `T_ℓ^* = S_ℓ^{-1} T_ℓ` for the Brandt pairing at every level `U ≤ Ô^×`
invariant at `ℓ`, with the finiteness discharged (`Tl_adjoint`, `relIndex_elemT_ne_zero`). -/
theorem Tl_adjoint' [Finite (XB U)] (hU : IsInvariantAt d ℓ hℓ U) (hO : U ≤ d.Ohat) (x y : ZX U R) :
    brandtPairing U R (heckeTHom U (elemT d ℓ hℓ) R (relIndex_elemT_ne_zero d U ℓ hℓ hU hO) x) y =
      brandtPairing U R x
        (SlInvHom d U ℓ hℓ R (heckeTHom U (elemT d ℓ hℓ) R (relIndex_elemT_ne_zero d U ℓ hℓ hU hO) y)) :=
  Tl_adjoint d U ℓ hℓ R hU _ (relIndex_elemT_inv_ne_zero d U ℓ hℓ hU hO) x y

/-- `prop:s01-adjoint` (`s01-adjoint`, `U = Ô^×`, `ℓ ∤ D`): `T_ℓ` is self-adjoint for the Brandt pairing, with the
finiteness discharged (`Tl_selfAdjoint_units`, `relIndex_elemT_ne_zero_Ohat`). -/
theorem Tl_selfAdjoint_units' (x y : ZX d.Ohat R) :
    brandtPairing d.Ohat R (heckeTHom d.Ohat (elemT d ℓ hℓ) R (relIndex_elemT_ne_zero_Ohat d ℓ hℓ) x) y =
      brandtPairing d.Ohat R x (heckeTHom d.Ohat (elemT d ℓ hℓ) R (relIndex_elemT_ne_zero_Ohat d ℓ hℓ) y) :=
  Tl_selfAdjoint_units d ℓ hℓ R _ x y

end Consumers

/-- `prop:s01-adjoint`(b) (`s01-adjoint`, "in particular"): at `U_0(M)` and a prime `ℓ ∤ D M`, `T_ℓ` is self-adjoint
for the Brandt pairing; finiteness of `X_B` and of the double cosets discharged (`Tl_selfAdjoint_U0`). -/
theorem Tl_selfAdjoint_U0' (d : DefiniteData) {M : ℕ} (hM : M.Coprime d.D) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ℓ ∣ d.D * M) (R : Type*) [CommRing R] (x y : ZX (d.U0 M hM) R) :
    brandtPairing (d.U0 M hM) R
        (heckeTHom (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M))) R
          (relIndex_elemT_ne_zero_U0 d ℓ (fun h => hℓ (h.mul_right M)) (fun h => hℓ (h.mul_left d.D))) x)
        y =
      brandtPairing (d.U0 M hM) R x
        (heckeTHom (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M))) R
          (relIndex_elemT_ne_zero_U0 d ℓ (fun h => hℓ (h.mul_right M)) (fun h => hℓ (h.mul_left d.D))) y) :=
  Tl_selfAdjoint_U0 d hM ℓ hℓ R _
    (relIndex_elemT_inv_ne_zero_U0 d ℓ (fun h => hℓ (h.mul_right M)) (fun h => hℓ (h.mul_left d.D))) x y

/-- `lem:s01-Up`(e) (`s01-Up`): `U_p` commutes with `T_ℓ` at the tower level, `ℓ ∤ M p D`, with the finiteness of `T_ℓ`
discharged (`relIndex_elemT_ne_zero_Utower`; proved like `Up_comm_Tl`, independent of its signature). -/
theorem Up_comm_Tl' {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
    {hp : ¬ p ∣ d.D} (R : Type*) [CommRing R] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (hℓM : ¬ ℓ ∣ M)
    (hℓp : ℓ ≠ p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Up d M p s hN hp hM hpM hs R ∘ₗ
        Tl d (d.Utower M p s hN) ℓ hℓ R (relIndex_elemT_ne_zero_Utower d ℓ hℓ hℓM hℓp) =
      Tl d (d.Utower M p s hN) ℓ hℓ R (relIndex_elemT_ne_zero_Utower d ℓ hℓ hℓM hℓp) ∘ₗ
        Up d M p s hN hp hM hpM hs R :=
  heckeT_comm_of_disjoint (d.Utower M p s hN) R hℓp.symm (splitAt_Utower hM hpM hs hp)
    (splitAt_Utower_of_ne hℓ hℓM hℓp) (localEmbedGL_mem_range _) (localEmbedGL_mem_range _)
    (Up_relIndex_ne_zero hM hpM hs) _

end Langlandscape.Brandt
