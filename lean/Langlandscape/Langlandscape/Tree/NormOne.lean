/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Admissible
import Langlandscape.Hyp.HS
import Langlandscape.Quat.Stab
import AlgJL.VolIII.Brandt.Pairing

/-!
# Norm reduction `X^1(U) → X_B(U)` (S02-L5a)

`plan/staged/stage-02-tree-quotients.tex`: `lem:s02-normone` (and `def:s02-Xone`).

* `XBone_toXB_injective` (a): for `U ≤ Ô^×` the map `X^1(U) → X_B(U)` is injective. Uses only that `B` is
  definite (`Nrd(B^×) ⊆ ℚ_{>0}`, import `nrd_definite`) and `Nrd(Ô^×) ⊆ Ẑ^×` (import
  `nrd_mem_zhat_of_mem_completion`, `rat_isInt_of_mem_zhat`).
* `GammaOne_eq_Gam` (a), second half: for `x ∈ B̂^1`, `B^1 ∩ x U^1 x⁻¹ = Γ_x(U)`
  (as sets of elements of `B^×`; `γ ∈ x U^1 x⁻¹ ↔ x⁻¹ ι(γ) x ∈ U ∩ B̂^1`).
* `XBone_toXB_bijective` (b): under `Hyp.HS d` (Hasse–Schilling, cited) and `NrdSurj d U`, bijective.
  Uses `𝔸_f^× = ℚ_{>0} · Ẑ^×` (import `exists_ratIdele_mul_ideleInfFin`).

Status: *formalized* modulo the explicit hypothesis `Hyp.HS d` in (b).
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local
open GL2TF.Quat (nrd)
open GL2TF (FinAdele Zhat)

section Aux

variable {a b : ℤ}

/-- `lem:s02-normone` (`s02-normone`): `nrd(ι γ) = nrd γ ∈ ℚ ⊆ 𝔸_f` for `γ ∈ B^×`. -/
theorem nrdHat_iotaU_val (γ : (QuatAlg ℚ a b)ˣ) :
    ((nrdHat a b (iotaU a b γ) : FinAdeleˣ) : FinAdele) =
      algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) :=
  ((GL2TF.Quat.nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) γ).1

/-- `lem:s02-normone` (`s02-normone`): `nrd γ = 1` implies `nrd (ι γ) = 1`. -/
theorem nrdHat_iotaU_eq_one {γ : (QuatAlg ℚ a b)ˣ} (h : nrd (γ : QuatAlg ℚ a b) = 1) :
    nrdHat a b (iotaU a b γ) = 1 := by
  apply Units.ext
  rw [nrdHat_iotaU_val, h, map_one, Units.val_one]

/-- `lem:s02-normone` (`s02-normone`): rational core of (a). If `r > 0` is rational, `w, w' ∈ Ẑ` with
`w w' = 1` and `r w = 1` in `𝔸_f`, then `r = 1` and `w = 1`. -/
private theorem rat_unit_aux {r : ℚ} (hr : 0 < r) {w w' : FinAdele} (hw : w ∈ Zhat) (hw' : w' ∈ Zhat)
    (hww : w * w' = 1) (h : algebraMap ℚ FinAdele r * w = 1) : r = 1 ∧ w = 1 := by
  have hr' : algebraMap ℚ FinAdele r = w' := by
    linear_combination (-(algebraMap ℚ FinAdele r)) * hww + w' * h
  have h1 : algebraMap ℚ FinAdele r⁻¹ * algebraMap ℚ FinAdele r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  have hinv : algebraMap ℚ FinAdele r⁻¹ = w := by
    linear_combination (-(algebraMap ℚ FinAdele r⁻¹)) * h + w * h1
  have hAr : algebraMap ℚ FinAdele r ∈ Zhat := by rw [hr']; exact hw'
  have hAri : algebraMap ℚ FinAdele r⁻¹ ∈ Zhat := by rw [hinv]; exact hw
  obtain ⟨k, hk⟩ := GL2TF.Quat.rat_isInt_of_mem_zhat r hAr
  obtain ⟨k', hk'⟩ := GL2TF.Quat.rat_isInt_of_mem_zhat r⁻¹ hAri
  have hkk : k * k' = 1 := by
    have h3 : ((k * k' : ℤ) : ℚ) = 1 := by
      push_cast
      rw [← hk, ← hk', mul_inv_cancel₀ hr.ne']
    exact_mod_cast h3
  have hr1 : r = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkk with h4 | h4
    · rw [hk, h4]; norm_num
    · rw [hk, h4] at hr; norm_num at hr
  refine ⟨hr1, ?_⟩
  rw [hr1, map_one, one_mul] at h
  exact h

/-- `lem:s02-normone`(a) (`s02-normone`): if `γ ∈ B^×`, `u ∈ Ô^×` and `nrd(ι γ) · nrd(u) = 1`, then
`nrd γ = 1` and `nrd u = 1` (`Nrd(B^×) ⊆ ℚ_{>0}` for definite `B`, `Nrd(Ô^×) ⊆ Ẑ^×`). -/
theorem nrd_eq_one_of_nrdHat_mul_eq_one (ha : a < 0) (hb : b < 0) (O : GL2TF.Quat.QOrder a b)
    {u : (BHat a b)ˣ} (hu : u ∈ GL2TF.Quat.orderCompletionUnits O) (γ : (QuatAlg ℚ a b)ˣ)
    (h : nrdHat a b (iotaU a b γ) * nrdHat a b u = 1) :
    nrd (γ : QuatAlg ℚ a b) = 1 ∧ nrdHat a b u = 1 := by
  have hrpos : 0 < nrd (γ : QuatAlg ℚ a b) := by
    have hγne : (γ : QuatAlg ℚ a b) ≠ 0 := Units.ne_zero γ
    have hd := (GL2TF.Quat.nrd_definite ha hb).1 (γ : QuatAlg ℚ a b)
    exact lt_of_le_of_ne (le_trans (by positivity) hd.1) (Ne.symm (mt hd.2.mp hγne))
  have h1 : ((nrdHat a b u : FinAdeleˣ) : FinAdele) ∈ Zhat :=
    GL2TF.Quat.nrd_mem_zhat_of_mem_completion O hu.1
  have h2 : ((nrdHat a b u⁻¹ : FinAdeleˣ) : FinAdele) ∈ Zhat :=
    GL2TF.Quat.nrd_mem_zhat_of_mem_completion O hu.2
  have hww : ((nrdHat a b u : FinAdeleˣ) : FinAdele) * ((nrdHat a b u⁻¹ : FinAdeleˣ) : FinAdele) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hmain : algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) * ((nrdHat a b u : FinAdeleˣ) : FinAdele) = 1 := by
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_one, nrdHat_iotaU_val] at h'
    exact h'
  obtain ⟨hr1, hw1⟩ := rat_unit_aux hrpos h1 h2 hww hmain
  exact ⟨hr1, Units.ext (by rw [Units.val_one]; exact hw1)⟩

/-- `lem:s02-normone`(b) (`s02-normone`): `𝔸_f^× = ℚ_{>0} · Ẑ^×`: every `ν ∈ 𝔸_f^×` is `r z` with `r ∈ ℚ`,
`r > 0`, `z ∈ Ẑ^×` (from the import's `idele_decomposition` helper `exists_ratIdele_mul_ideleInfFin`). -/
theorem exists_pos_rat_mul_zhat (ν : FinAdeleˣ) :
    ∃ (r : ℚ) (z : GL2TF.Zhatˣ), 0 < r ∧
      (ν : FinAdele) = algebraMap ℚ FinAdele r * ((z : Zhat) : FinAdele) := by
  obtain ⟨q, r, u, hr, hx⟩ := GL2TF.exists_ratIdele_mul_ideleInfFin
    ((MulEquiv.prodUnits (M := ℝ) (N := FinAdele)).symm ((1 : ℝˣ), ν) : GL2TF.Idele)
  have hv := congrArg (fun x : GL2TF.Idele => (x : GL2TF.Adele)) hx
  simp only [Units.val_mul, GL2TF.ratIdele_val, GL2TF.ideleInfFin_val hr.ne'] at hv
  have h1 : (1 : ℝ) = (((q : ℚˣ) : ℚ) : ℝ) * r := congrArg Prod.fst hv
  have h2 : (ν : FinAdele) = algebraMap ℚ FinAdele ((q : ℚˣ) : ℚ) * ((u : Zhat) : FinAdele) :=
    congrArg Prod.snd hv
  have hq : (0 : ℝ) < (((q : ℚˣ) : ℚ) : ℝ) := by
    by_contra hneg
    have hneg' := not_lt.1 hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' hr.le
    linarith
  have hqpos : (0 : ℚ) < ((q : ℚˣ) : ℚ) := by exact_mod_cast hq
  exact ⟨((q : ℚˣ) : ℚ), u, hqpos, h2⟩

/-- `lem:s02-normone` (`s02-normone`): `z⁻¹ z = 1` in `𝔸_f` for `z ∈ Ẑ^×`. -/
private theorem zhat_unit_inv_mul' (z : GL2TF.Zhatˣ) :
    (((z⁻¹ : GL2TF.Zhatˣ) : Zhat) : FinAdele) * ((z : Zhat) : FinAdele) = 1 := by
  have := congrArg (fun w : Zhat => (w : FinAdele)) z.inv_mul
  simpa only [Subring.coe_mul, Subring.coe_one] using this

end Aux

section Main

variable {d : DefiniteData} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `lem:s02-normone`(a) (`s02-normone`): for `U ≤ Ô^×` the natural map `X^1(U) → X_B(U)` is injective. -/
theorem XBone_toXB_injective (hU : U ≤ d.Ohat) : Function.Injective (XBone.toXB d U) := by
  intro c₁ c₂ hc
  induction c₁ using Quotient.inductionOn' with
  | h x =>
    induction c₂ using Quotient.inductionOn' with
    | h x' =>
      have h1 := XBone.toXB_mk (U := U) x
      have h2 := XBone.toXB_mk (U := U) x'
      have h3 : DoubleCoset.mk (globalUnits d.a d.b) U (x : (BHat d.a d.b)ˣ) =
          DoubleCoset.mk (globalUnits d.a d.b) U (x' : (BHat d.a d.b)ˣ) :=
        h1.symm.trans (hc.trans h2)
      obtain ⟨g, hg, k, hk, hxx⟩ := DoubleCoset.eq.1 h3
      obtain ⟨γ, rfl⟩ := hg
      have hx : nrdHat d.a d.b (x : (BHat d.a d.b)ˣ) = 1 := x.2
      have hx' : nrdHat d.a d.b (x' : (BHat d.a d.b)ˣ) = 1 := x'.2
      have hprod : nrdHat d.a d.b (iotaU d.a d.b γ) * nrdHat d.a d.b k = 1 := by
        have := congrArg (nrdHat d.a d.b) hxx
        rw [hx', map_mul, map_mul, hx, mul_one] at this
        exact this.symm
      obtain ⟨hr1, hk1⟩ := nrd_eq_one_of_nrdHat_mul_eq_one d.ha d.hb d.O.1
        (hU hk : k ∈ GL2TF.Quat.orderCompletionUnits d.O.1) γ hprod
      have hγ1 : iotaU d.a d.b γ ∈ BHatOne d := nrdHat_iotaU_eq_one hr1
      have hk1' : k ∈ BHatOne d := hk1
      refine (DoubleCoset.eq (H := (globalUnits d.a d.b).subgroupOf (BHatOne d))
        (K := U.subgroupOf (BHatOne d))).2
        ⟨(⟨iotaU d.a d.b γ, hγ1⟩ : BHatOne d), ?_, (⟨k, hk1'⟩ : BHatOne d), ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩
      · exact Subgroup.mem_subgroupOf.2 hk
      · exact Subtype.ext hxx

/-- `lem:s02-normone`(a) (`s02-normone`): for `x ∈ B̂^1` and `U ≤ Ô^×`, `B^1 ∩ x U^1 x⁻¹ = Γ_x(U)`, i.e. for
`γ ∈ B^×`: `nrd γ = 1 ∧ x⁻¹ ι(γ) x ∈ U ∩ B̂^1` holds iff `γ ∈ Γ_x(U)` (`Quat.Gam`). -/
theorem GammaOne_eq_Gam (hU : U ≤ d.Ohat) {x : (BHat d.a d.b)ˣ} (hx : x ∈ BHatOne d) :
    {γ : (QuatAlg ℚ d.a d.b)ˣ | nrd (γ : QuatAlg ℚ d.a d.b) = 1 ∧
        x⁻¹ * iotaU d.a d.b γ * x ∈ U ⊓ BHatOne d} = (Gam U x : Set (QuatAlg ℚ d.a d.b)ˣ) := by
  have hx' : nrdHat d.a d.b x = 1 := hx
  ext γ
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨-, h⟩
    exact (mem_Gam_iff U x γ).2 (Subgroup.mem_inf.1 h).1
  · intro h
    have hn : nrd (γ : QuatAlg ℚ d.a d.b) = 1 :=
      nrd_eq_one_of_mem_Gam d.ha d.hb d.O.1 (hU : U ≤ GL2TF.Quat.orderCompletionUnits d.O.1) h
    refine ⟨hn, Subgroup.mem_inf.2 ⟨(mem_Gam_iff U x γ).1 h, ?_⟩⟩
    have hι : nrdHat d.a d.b (iotaU d.a d.b γ) = 1 := nrdHat_iotaU_eq_one hn
    show nrdHat d.a d.b (x⁻¹ * iotaU d.a d.b γ * x) = 1
    simp only [map_mul, map_inv, hx', hι, inv_one, one_mul]

/-- `lem:s02-normone`(b) (`s02-normone`): if `Nrd U = Ẑ^×` (`Quat.NrdSurj d U`), `U ≤ Ô^×`, and
`Nrd(B^×) = ℚ_{>0}` (`Hyp.HS d`, Hasse–Schilling, cited), then `X^1(U) → X_B(U)` is bijective. -/
theorem XBone_toXB_bijective (hHS : Hyp.HS d) (hN : Langlandscape.Quat.NrdSurj d U) (hU : U ≤ d.Ohat) :
    Function.Bijective (XBone.toXB d U) := by
  refine ⟨XBone_toXB_injective hU, ?_⟩
  intro c
  induction c using Quotient.inductionOn' with
  | h y =>
    obtain ⟨r, z, hr, hz⟩ := exists_pos_rat_mul_zhat (nrdHat d.a d.b y)
    obtain ⟨γ, hγ⟩ := hHS r⁻¹ (inv_pos.2 hr)
    have hv : (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom) z⁻¹ ∈ zhatUnits :=
      (MonoidHom.mem_range).2 ⟨z⁻¹, rfl⟩
    obtain ⟨u, huU, hu⟩ := hN _ hv
    have hu' : ((nrdHat d.a d.b u : FinAdeleˣ) : FinAdele) = (((z⁻¹ : GL2TF.Zhatˣ) : Zhat) : FinAdele) :=
      congrArg Units.val hu
    have hxmem : iotaU d.a d.b γ * y * u ∈ BHatOne d := by
      show nrdHat d.a d.b (iotaU d.a d.b γ * y * u) = 1
      apply Units.ext
      have h1 : algebraMap ℚ FinAdele r⁻¹ * algebraMap ℚ FinAdele r = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
      have h2 := zhat_unit_inv_mul' z
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_one, nrdHat_iotaU_val, hγ, hz, hu']
      linear_combination ((z : Zhat) : FinAdele) * (((z⁻¹ : GL2TF.Zhatˣ) : Zhat) : FinAdele) * h1 + h2
    refine ⟨(DoubleCoset.mk ((globalUnits d.a d.b).subgroupOf (BHatOne d)) (U.subgroupOf (BHatOne d))
      (⟨iotaU d.a d.b γ * y * u, hxmem⟩ : BHatOne d) : XBone d U), ?_⟩
    rw [XBone.toXB_mk]
    symm
    exact DoubleCoset.eq.2 ⟨iotaU d.a d.b γ, ⟨γ, rfl⟩, u, huU, rfl⟩

end Main

end Langlandscape.Tree
