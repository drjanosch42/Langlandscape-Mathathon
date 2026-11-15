/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.HeckeCoeff
import Langlandscape.Ordinary.Tower

/-!
# The Hecke dictionary `θ` on the degree-zero Brandt module (S05-L1)

Tex: `def:s05-theta` (`plan/staged/stage-05-comparison-hypothesis.tex`, `mathematics/chapters/s05/`).
Status: *formalized* (definitions and the degree compatibilities).

* `degZero U R := ker (Ordinary.deg (XB U) R)` on `ZX U R = R[X_B(U)]`; the degree map is stage 04's
  `Ordinary.deg` (`Ordinary/EKills.lean`), no new degree map is introduced.
* `deg_heckeTHom` : `deg (T_g x) = [U : U ∩ g U g⁻¹] · deg x`; `degZero_stable` : an endomorphism `f` with
  `deg ∘ f = c • deg` preserves `degZero`; `restrictDeg` the restriction.
* `HeckeSym M p q s` : the Hecke symbols `T ℓ` (`ℓ ∤ Mpq`), `Up` (`s ≥ 1`), `Tp` (`s = 0`), `dia u`
  (`u ∈ (ℤ/Mp^s)ˣ`), `Uq`.  **No `U ℓ` for `ℓ ∣ M`** (decision rule of S05-L1: the `K1`-coset finiteness
  `[U_s : U_s ∩ ϖ_ℓ U_s ϖ_ℓ⁻¹] ≠ 0` for `ℓ ∣ M` is not in Lean and is not a ≤ 40-line lemma; carried-over item (a)
  of `plan/implementation/stage-05.md` §0 stays open; recorded for HYPOTHESES).
* `diaZX` : the product diamond `⟨u⟩ = ∏_{ℓ ∣ Mp^s} ⟨t_ℓ⟩` (carried-over item (c)), assembled as an ordered product over
  `(M * p ^ s).primeFactors.toList`, `t_ℓ = localUnit ℓ u ∈ ℤ_ℓ^×` the image of the integer representative of `u`.
* `theta d M p q s hN hp hM hpM hD Pq hPq : HeckeSym M p q s → Module.End ℤ (degZero (d.Utower M p s hN) ℤ)`,
  the dictionary of `def:s05-theta`, with the normalisations
  - `T ℓ ↦ heckeTHom (elemT ℓ)` (homological `T_ℓ`, `def:s05-theta`);
  - `Up ↦ UpHom` (`U_p ↦ N_{U_p}`, `def:s05-theta`);
  - `Tp ↦ heckeTHom (elemT p)` at `s = 0` (`def:s05-theta`);
  - `dia u ↦ diaZX u⁻¹` (`⟨d⟩ ↦ ⟨d⟩⁻¹`, `def:s05-theta`);
  - `Uq ↦ + PiEllHom Pq` (sign `ε = +1`, `+Π_q`, `def:s05-theta`, `rem:s05-hsieh`).
-/

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

set_option autoImplicit false

namespace Langlandscape.Comparison

noncomputable section

/-! ### Degree zero -/

section DegZero

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `def:s05-theta` (`s05-theta`): the degree-zero part `R[X_B(U)]⁰ = ker (deg : R[X_B(U)] → R)`, with stage 04's
`Ordinary.deg`. -/
abbrev degZero : Submodule R (ZX U R) :=
  LinearMap.ker (Ordinary.deg (XB U) R)

variable {U R}

/-- `def:s05-theta` (`s05-theta`): membership in `degZero`. -/
theorem mem_degZero {x : ZX U R} : x ∈ degZero U R ↔ Ordinary.deg (XB U) R x = 0 :=
  LinearMap.mem_ker

/-- `def:s05-theta` (`s05-theta`): an endomorphism with `deg ∘ f = c • deg` preserves `degZero`. -/
theorem degZero_stable (f : Module.End R (ZX U R)) (c : R)
    (hf : (Ordinary.deg (XB U) R).comp f = c • Ordinary.deg (XB U) R) {x : ZX U R}
    (hx : x ∈ degZero U R) : f x ∈ degZero U R := by
  rw [mem_degZero] at hx ⊢
  have h := LinearMap.congr_fun hf x
  rw [LinearMap.comp_apply, LinearMap.smul_apply, hx, smul_zero] at h
  exact h

/-- `def:s05-theta` (`s05-theta`): the restriction of an endomorphism with `deg ∘ f = c • deg` to `degZero`. -/
def restrictDeg (f : Module.End R (ZX U R)) (c : R)
    (hf : (Ordinary.deg (XB U) R).comp f = c • Ordinary.deg (XB U) R) : Module.End R (degZero U R) :=
  f.restrict (fun _ hx => degZero_stable f c hf hx)

/-- `def:s05-theta` (`s05-theta`): `restrictDeg f` acts as `f`. -/
@[simp] theorem restrictDeg_apply (f : Module.End R (ZX U R)) (c : R)
    (hf : (Ordinary.deg (XB U) R).comp f = c • Ordinary.deg (XB U) R) (x : degZero U R) :
    ((restrictDeg f c hf x : degZero U R) : ZX U R) = f x :=
  rfl

end DegZero

/-! ### Degree compatibilities -/

section DegHecke

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)

/-- `def:s05-theta` (`s05-theta`), helper: a system of representatives of `U g U / U` has
`[U : U ∩ g U g⁻¹]` elements. -/
theorem card_of_isDcReps {T : Finset (GL2TF.Quat.BHat a b)ˣ} (hT : IsDcReps U g T) :
    T.card = (U ⊓ conjSub U g).relIndex U := by
  obtain ⟨hS, hcov, hinj⟩ := hT
  have key : ∀ u u' : ↥U, (QuotientGroup.mk ((u : (GL2TF.Quat.BHat a b)ˣ) * g) :
      (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk ((u' : (GL2TF.Quat.BHat a b)ˣ) * g) ↔
      u⁻¹ * u' ∈ (U ⊓ conjSub U g).subgroupOf U := by
    intro u u'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_conjSub]
    have e : ((u : (GL2TF.Quat.BHat a b)ˣ) * g)⁻¹ * ((u' : (GL2TF.Quat.BHat a b)ˣ) * g) =
        g⁻¹ * ((u⁻¹ * u' : ↥U) : (GL2TF.Quat.BHat a b)ˣ) * g := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact ⟨fun h => ⟨(u⁻¹ * u').2, h⟩, fun h => h.2⟩
  let φ : (↥U ⧸ (U ⊓ conjSub U g).subgroupOf U) → (GL2TF.Quat.BHat a b)ˣ ⧸ U :=
    fun c => QuotientGroup.mk (((Quotient.out c : ↥U) : (GL2TF.Quat.BHat a b)ˣ) * g)
  have hφ : ∀ u : ↥U, φ (QuotientGroup.mk u) =
      QuotientGroup.mk ((u : (GL2TF.Quat.BHat a b)ˣ) * g) := by
    intro u
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((U ⊓ conjSub U g).subgroupOf U) u
    show (QuotientGroup.mk
        ((((QuotientGroup.mk u : ↥U ⧸ (U ⊓ conjSub U g).subgroupOf U).out : ↥U) :
          (GL2TF.Quat.BHat a b)ˣ) * g) : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = _
    rw [hw]
    refine (key _ _).2 ?_
    have e : (u * (w : ↥U))⁻¹ * u = (w : ↥U)⁻¹ := by group
    rw [e]
    exact inv_mem w.2
  have hinjφ : Function.Injective φ := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hφ] at hxy
    exact QuotientGroup.eq.2 ((key u u').1 hxy)
  have hrange : Set.range φ = QuotientGroup.mk '' (T : Set (GL2TF.Quat.BHat a b)ˣ) := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hφ]
      obtain ⟨t, ht, htc⟩ := hcov _
        ((mem_dcSet U g).2 ⟨(u : (GL2TF.Quat.BHat a b)ˣ), u.2, 1, U.one_mem, by rw [mul_one]⟩)
      exact ⟨t, Finset.mem_coe.2 ht, htc.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, hu, v, hv, e⟩ := (mem_dcSet U g).1 (hS t (Finset.mem_coe.1 ht))
      refine ⟨QuotientGroup.mk ⟨u, hu⟩, ?_⟩
      rw [hφ, e, QuotientGroup.eq]
      show (u * g)⁻¹ * (u * g * v) ∈ U
      have e3 : (u * g)⁻¹ * (u * g * v) = v := by group
      rw [e3]
      exact hv
  rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_range_of_injective hinjφ, hrange,
    Nat.card_coe_set_eq, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset]

/-- `def:s05-theta` (`s05-theta`): `deg (T_g x) = [U : U ∩ g U g⁻¹] · deg x` for the homological `T_g`. -/
theorem deg_heckeTHom [Finite (XB U)] (x : ZX U R) :
    Ordinary.deg (XB U) R (heckeTHom U g R hfin x) =
      ((U ⊓ conjSub U g).relIndex U : R) * Ordinary.deg (XB U) R x := by
  have : Fintype (XB U) := Fintype.ofFinite _
  obtain ⟨T, hT⟩ := exists_dcReps U g hfin
  rw [← card_of_isDcReps U g hT]
  have hdeg : ∀ f : ZX U R, Ordinary.deg (XB U) R f = ∑ c, f c := by
    intro f
    rw [Ordinary.deg, Finsupp.lsum_apply]
    exact Finsupp.sum_fintype _ _ (fun _ => by simp)
  have h1 : ∀ z : XB U, ∑ c' : XB U, (Pi.single c' (1 : R) : XB U → R) z = 1 := by
    intro z
    simp [Pi.single_apply]
  have hsingle : ∀ c : XB U,
      Ordinary.deg (XB U) R (heckeTHom U g R hfin (Finsupp.single c 1)) = (T.card : R) := by
    intro c
    obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk (globalUnits a b) U y = c := ⟨_, DoubleCoset.out_eq' c⟩
    rw [hdeg]
    simp only [heckeTHom_single_apply, one_mul]
    simp only [heckeT_apply_reps U g R hfin T hT.1 hT.2.1 hT.2.2]
    rw [Finset.sum_comm]
    simp only [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
  | single c r =>
    have e : Finsupp.single c r = r • Finsupp.single c (1 : R) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e]
    simp only [map_smul, hsingle, Ordinary.deg_single, smul_eq_mul]
    ring

/-- `def:s05-theta` (`s05-theta`): `deg ∘ T_g = [U : U ∩ g U g⁻¹] • deg`. -/
theorem deg_comp_heckeTHom [Finite (XB U)] :
    (Ordinary.deg (XB U) R).comp (heckeTHom U g R hfin) =
      ((U ⊓ conjSub U g).relIndex U : R) • Ordinary.deg (XB U) R := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, deg_heckeTHom, smul_eq_mul]

/-- `def:s05-theta` (`s05-theta`): `T_g` preserves `degZero`. -/
theorem heckeTHom_mem_degZero [Finite (XB U)] {x : ZX U R} (hx : x ∈ degZero U R) :
    heckeTHom U g R hfin x ∈ degZero U R :=
  degZero_stable _ _ (deg_comp_heckeTHom U g R hfin) hx

/-- `def:s05-theta` (`s05-theta`): for `g` normalizing `U`, `deg ∘ T_g = deg`. -/
theorem deg_comp_heckeTHom_of_normalizing [Finite (XB U)] (hn : ∀ x ∈ U, g⁻¹ * x * g ∈ U) :
    (Ordinary.deg (XB U) R).comp (heckeTHom U g R (relIndex_ne_zero_of_normalizing U g hn)) =
      (1 : R) • Ordinary.deg (XB U) R := by
  rw [deg_comp_heckeTHom]
  have h : U ⊓ conjSub U g = U := inf_eq_left.2 fun x hx => (mem_conjSub U g).2 (hn x hx)
  rw [h, Subgroup.relIndex_self, Nat.cast_one]

/-- `def:s05-theta` (`s05-theta`): right translation preserves the degree, `deg ∘ R_g = deg`. -/
theorem deg_comp_translateHom :
    (Ordinary.deg (XB U) R).comp (translateHom U R g) = (1 : R) • Ordinary.deg (XB U) R := by
  apply Finsupp.lhom_ext
  intro c r
  rw [LinearMap.comp_apply, translateHom_single, LinearMap.smul_apply, Ordinary.deg_single,
    Ordinary.deg_single, one_smul]

/-- `def:s05-theta` (`s05-theta`), helper: a product of degree-preserving endomorphisms preserves the degree. -/
private theorem deg_comp_list_prod {L : List (Module.End R (ZX U R))}
    (hL : ∀ f ∈ L, (Ordinary.deg (XB U) R).comp f = (1 : R) • Ordinary.deg (XB U) R) :
    (Ordinary.deg (XB U) R).comp L.prod = (1 : R) • Ordinary.deg (XB U) R := by
  induction L with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, LinearMap.comp_id, one_smul]
  | cons f L ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hL f (by simp), one_smul,
      ih (fun h hh => hL h (by simp [hh])), one_smul]

end DegHecke

/-! ### Uniformisers at `q` and the product diamond -/

/-- `def:s05-theta` (`s05-theta`): `P ∈ (B ⊗ ℚ_q)ˣ` is a uniformiser element: `q ∣ D` and `v_q(Nrd P) = 1`. -/
def IsUniformiserElt (d : DefiniteData) (q : ℕ) [Fact q.Prime] (P : (QuatAlg ℚ_[q] d.a d.b)ˣ) : Prop :=
  q ∣ d.D ∧ (GL2TF.Quat.nrd (P : QuatAlg ℚ_[q] d.a d.b)).valuation = 1

/-- `def:s05-theta` (`s05-theta`): `q ∣ D` from a uniformiser element. -/
theorem IsUniformiserElt.dvd {d : DefiniteData} {q : ℕ} [Fact q.Prime] {P : (QuatAlg ℚ_[q] d.a d.b)ˣ}
    (h : IsUniformiserElt d q P) : q ∣ d.D :=
  h.1

/-- `def:s05-theta` (`s05-theta`): for `ℓ ∣ N`, the unit `t_ℓ ∈ ℤ_ℓ^×` given by the integer representative
`u.val ∈ [0, N)` of `u ∈ (ℤ/N)ˣ` (it lifts `u mod ℓ^{v_ℓ(N)}`). -/
def localUnit (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ} (hℓ : ℓ ∣ N) (u : (ZMod N)ˣ) : ℤ_[ℓ]ˣ :=
  (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
    ((Nat.Coprime.coprime_dvd_right hℓ (ZMod.val_coe_unit_coprime u)).symm))).unit

/-- `def:s05-theta` (`s05-theta`): `localUnit ℓ u` is the image of `u.val`. -/
@[simp] theorem coe_localUnit (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ} (hℓ : ℓ ∣ N) (u : (ZMod N)ˣ) :
    ((localUnit ℓ hℓ u : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = ((u : ZMod N).val : ℤ_[ℓ]) :=
  rfl

section Diamond

variable (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D) (R : Type*) [CommRing R]

/-- `def:s05-theta` (`s05-theta`), helper: the normaliser obligation of the local diamond at `ℓ ∣ Mp^s` on
`U_s = U_1(M p^s)`: `δ_t⁻¹ U_s δ_t ⊆ U_s` (stage 01's `diamondElt_inv_normalizes_U1`, `Utower` being `U1` by
definition). -/
theorem diamondElt_inv_normalizes_Utower_of_mem_primeFactors (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (t : ℤ_[ℓ]ˣ) :
    ∀ x ∈ d.Utower M p s hN, (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) t)⁻¹ * x *
      diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) t ∈ d.Utower M p s hN :=
  diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ t

/-- `def:s05-theta` (`s05-theta`): the local factor at `ℓ ∣ Mp^s` of the homological diamond `⟨u⟩` on
`R[X_B(U_s)]`: `T_{δ_t}` with `t = t_ℓ = localUnit ℓ u`. -/
def diaLocal (ℓ : ℕ) (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (u : (ZMod (M * p ^ s))ˣ) :
    Module.End R (ZX (d.Utower M p s hN) R) :=
  haveI : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  heckeTHom (d.Utower M p s hN)
    (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)) R
    (relIndex_ne_zero_of_normalizing _ _ (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ _))

/-- `def:s05-theta` (`s05-theta`): the homological diamond `⟨u⟩ = ∏_{ℓ ∣ Mp^s} ⟨t_ℓ⟩_ℓ` on `R[X_B(U_s)]`, the ordered
product over `(M * p ^ s).primeFactors.toList` (carried-over item (c); the local factors commute, but the ordered
product needs no commutation proof). -/
def diaZX (u : (ZMod (M * p ^ s))ˣ) : Module.End R (ZX (d.Utower M p s hN) R) :=
  ((M * p ^ s).primeFactors.toList.attach.map
    (fun ℓ => diaLocal d M p s hN R ℓ.1 (Finset.mem_toList.1 ℓ.2) u)).prod

/-- `def:s05-theta` (`s05-theta`): each local diamond preserves the degree. -/
theorem deg_comp_diaLocal (ℓ : ℕ) (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (u : (ZMod (M * p ^ s))ˣ) :
    (Ordinary.deg (XB (d.Utower M p s hN)) R).comp (diaLocal d M p s hN R ℓ hℓ u) =
      (1 : R) • Ordinary.deg (XB (d.Utower M p s hN)) R := by
  haveI : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  unfold diaLocal
  exact deg_comp_heckeTHom_of_normalizing (d.Utower M p s hN)
    (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)) R
    (diamondElt_inv_normalizes_Utower_of_mem_primeFactors d M p s hN ℓ hℓ _)

/-- `def:s05-theta` (`s05-theta`): the product diamond preserves the degree, `deg ∘ ⟨u⟩ = deg`. -/
theorem deg_comp_diaZX (u : (ZMod (M * p ^ s))ˣ) :
    (Ordinary.deg (XB (d.Utower M p s hN)) R).comp (diaZX d M p s hN R u) =
      (1 : R) • Ordinary.deg (XB (d.Utower M p s hN)) R := by
  unfold diaZX
  refine deg_comp_list_prod _ _ fun f hf => ?_
  obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hf
  exact deg_comp_diaLocal d M p s hN R _ _ u

end Diamond

/-! ### Hecke symbols and the dictionary -/

/-- `def:s05-theta` (`s05-theta`): the Hecke symbols at level `U_s = U_1(M p^s)` of `B_q`:
`T ℓ` (`ℓ` prime, `ℓ ∤ M p q`), `Up` (`s ≥ 1`), `Tp` (`s = 0`), `dia u` (`u ∈ (ℤ/Mp^s)ˣ`), `Uq`.
Restriction: **no `U ℓ` for `ℓ ∣ M`** (the `K1`-level finiteness for `ℓ ∣ M` is not in Lean; S05-L1 decision rule,
carried-over item (a); recorded in HYPOTHESES). -/
inductive HeckeSym (M p q s : ℕ) : Type
  /-- `T_ℓ`, `ℓ` prime, `ℓ ∤ M p q`. -/
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M * p * q)
  /-- `U_p`, `s ≥ 1`. -/
  | Up (hs : 1 ≤ s)
  /-- `T_p`, `s = 0`. -/
  | Tp (hs : s = 0)
  /-- the diamond `⟨u⟩`, `u ∈ (ℤ/Mp^s)ˣ`. -/
  | dia (u : (ZMod (M * p ^ s))ˣ)
  /-- `U_q`. -/
  | Uq

section Theta

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `def:s05-theta` (`s05-theta`), helper: `ℓ ∤ Mpq`, `D = q` give `ℓ ∤ D`. -/
theorem not_dvd_D_of_T (d : DefiniteData) (M p q : ℕ) {ℓ : ℕ} (hD : d.D = q) (hℓN : ¬ ℓ ∣ M * p * q) :
    ¬ ℓ ∣ d.D := by
  intro h
  rw [hD] at h
  exact hℓN (dvd_mul_of_dvd_right h _)

/-- `def:s05-theta` (`s05-theta`), helper: `ℓ ∤ Mpq` gives `ℓ ∤ M`. -/
theorem not_dvd_M_of_T (M p q : ℕ) {ℓ : ℕ} (hℓN : ¬ ℓ ∣ M * p * q) : ¬ ℓ ∣ M :=
  fun h => hℓN (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h p) q)

/-- `def:s05-theta` (`s05-theta`), helper: `ℓ ∤ Mpq` gives `ℓ ≠ p`. -/
theorem ne_p_of_T (M p q : ℕ) {ℓ : ℕ} (hℓN : ¬ ℓ ∣ M * p * q) : ℓ ≠ p := by
  rintro rfl
  exact hℓN (dvd_mul_of_dvd_left (dvd_mul_left _ _) q)

/-- `def:s05-theta` (`s05-theta`), helper: at `s = 0`, `p ∤ M p^s` (from `p ∤ M`). -/
theorem not_dvd_of_s_eq_zero (M p s : ℕ) (hpM : ¬ p ∣ M) (hs : s = 0) : ¬ p ∣ M * p ^ s := by
  rw [hs, pow_zero, mul_one]
  exact hpM

/-- `def:s05-theta` (`s05-theta`): the operator `θ(h)` on `ℤ[X_B(U_s)]` (before restriction to degree zero):
`T ℓ ↦ T_ℓ = heckeTHom (elemT ℓ)`, `Up ↦ N_{U_p} = UpHom`, `Tp ↦ heckeTHom (elemT p)` (`s = 0`),
`dia u ↦ ⟨u⟩⁻¹ = diaZX u⁻¹`, `Uq ↦ +Π_q = PiEllHom Pq` (sign `+`, `rem:s05-hsieh`). -/
def thetaZX : HeckeSym M p q s → Module.End ℤ (ZX (d.Utower M p s hN) ℤ)
  | .T ℓ hℓ hℓN =>
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    heckeTHom (d.Utower M p s hN) (elemT d ℓ (not_dvd_D_of_T d M p q hD hℓN)) ℤ
      (relIndex_elemT_ne_zero_Utower d ℓ _ (not_dvd_M_of_T M p q hℓN) (ne_p_of_T M p q hℓN))
  | .Up hs => UpHom d M p s hN hp hM hpM hs ℤ
  | .Tp hs => heckeTHom (d.Utower M p s hN) (elemT d p hp) ℤ
      (relIndex_elemT_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) (not_dvd_of_s_eq_zero M p s hpM hs))
  | .dia u => diaZX d M p s hN ℤ u⁻¹
  | .Uq => PiEllHom ℤ d q hPq.dvd Pq (d.Utower M p s hN)

/-- `def:s05-theta` (`s05-theta`): the degree factor of `θ(h)`: `deg ∘ θ(h) = thetaDeg h • deg`
(`ℓ + 1`-type index for `T ℓ`, `p` for `Up`, `1` for `dia` and `Uq`). -/
def thetaDeg : HeckeSym M p q s → ℤ
  | .T ℓ hℓ hℓN =>
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    ((d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemT d ℓ (not_dvd_D_of_T d M p q hD hℓN))).relIndex
      (d.Utower M p s hN) : ℤ)
  | .Up _ => (p : ℤ)
  | .Tp _ => ((d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (elemT d p hp)).relIndex (d.Utower M p s hN) : ℤ)
  | .dia _ => 1
  | .Uq => 1

/-- `def:s05-theta` (`s05-theta`): `deg ∘ θ(h) = thetaDeg h • deg`. -/
theorem deg_comp_thetaZX (h : HeckeSym M p q s) :
    (Ordinary.deg (XB (d.Utower M p s hN)) ℤ).comp (thetaZX d M p q s hN hp hM hpM hD Pq hPq h) =
      thetaDeg d M p q s hN hp hD h • Ordinary.deg (XB (d.Utower M p s hN)) ℤ := by
  cases h with
  | T _ _ _ => exact deg_comp_heckeTHom _ _ _ _
  | Up hs => exact Ordinary.deg_comp_UpHom ℤ hM hpM hs
  | Tp _ => exact deg_comp_heckeTHom _ _ _ _
  | dia u => exact deg_comp_diaZX d M p s hN ℤ u⁻¹
  | Uq => exact deg_comp_translateHom _ _ _

/-- `def:s05-theta` (`s05-theta`): the dictionary `θ : HeckeSym M p q s → End_ℤ(ℤ[X_B(U_s)]⁰)`, the restriction of
`thetaZX` to `degZero`. Normalisations (one per line, `def:s05-theta`):
`T ℓ ↦ T_ℓ` (homological, `[x] ↦ ∑ [x gᵢ]`);
`Up ↦ N_{U_p}` (`UpHom`);
`Tp ↦ T_p` at `s = 0`;
`dia u ↦ ⟨u⟩⁻¹` (`diaZX u⁻¹`);
`Uq ↦ +Π_q` (`PiEllHom Pq`, `ε = +1`, `rem:s05-hsieh`). -/
def theta (h : HeckeSym M p q s) : Module.End ℤ (degZero (d.Utower M p s hN) ℤ) :=
  restrictDeg (thetaZX d M p q s hN hp hM hpM hD Pq hPq h) (thetaDeg d M p q s hN hp hD h)
    (deg_comp_thetaZX d M p q s hN hp hM hpM hD Pq hPq h)

/-- `def:s05-theta` (`s05-theta`): `θ(h)` acts on `degZero` as `thetaZX h`. -/
@[simp] theorem theta_apply (h : HeckeSym M p q s) (x : degZero (d.Utower M p s hN) ℤ) :
    ((theta d M p q s hN hp hM hpM hD Pq hPq h x : degZero (d.Utower M p s hN) ℤ) : ZX (d.Utower M p s hN) ℤ) =
      thetaZX d M p q s hN hp hM hpM hD Pq hPq h x :=
  rfl

end Theta

end

end Langlandscape.Comparison
