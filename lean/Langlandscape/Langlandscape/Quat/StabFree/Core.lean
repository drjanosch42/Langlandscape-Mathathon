/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.ImportDictionary

/-!
# `BrandtStabFree` part B, piece G (tex step (vi), globalisation + assembly): `stabFree_core`

This file proves `stabFree_core`, taking the
local core (piece F, `local_pi`) as the explicit hypothesis `hlocal`.

Math (tex step (vi)): given `π = p(γ) ∈ ℤ[γ]` with `nrd π = ℓ` and the local condition at `ℓ`,
set `u := y⁻¹ * x⁻¹ * ι(π) * x`. Show `u ∈ Ô^×` place by place (`mem_orderCompletionUnits_iff_local`):
- at `ℓ`: `localComponent d ℓ hℓD u ∈ GL2Zl ℓ` (from `hlocal`), and
  `localComponent ∈ GL2Zl ℓ ↔` both `ι_ℓ(u_ℓ), ι_ℓ(u_ℓ)⁻¹` have entries in `ℤ_ℓ`
  (`mem_localLattice_iff_iota`, `iota_image_localLattice`), so `u_ℓ, u_ℓ⁻¹ ∈ 𝒪_ℓ`;
- at `q ≠ ℓ`: `y_q ∈ 𝒪_q^×` (from `y ∈ Ô` and `nrd y = ℓ·w` a unit at `q`; `y_q⁻¹ = conj(y_q)/(ℓ w_q)`,
  `𝒪_q` star-closed since `conj z = trd z - z` and `trd` is integral on orders), and
  `x_q⁻¹ ι_q(π) x_q = p(x_q⁻¹ ι_q(γ) x_q) ∈ 𝒪_q^×` (from `γ ∈ Γ_x` the conjugate is in `Ô^×`;
  `𝒪_q` a subalgebra; unit since `nrd π = ℓ ∈ ℤ_q^×`). Hence `u_q ∈ 𝒪_q^×`.
Then `x * y = ι(π) * x * u` and `mk(x*y) = mk(x)` via `DoubleCoset.mk_mem_mul` (`ι π ∈ globalUnits`,
`π ∈ B^×` since `nrd π = ℓ ≠ 0`, `B` division: `eq_zero_of_nrd_eq_zero`) and
`DoubleCoset.mk_mul_mem` (`u ∈ Ô^×`).

Provenance: draft by mistral-large-4-0 via opencode (external, user-run; branch `abhijit/brandtstabfree`,
c170335d), integrated and audited by the Langlandscape agents.
-/

set_option autoImplicit false

namespace Langlandscape.StabFree.Core

open GL2TF Langlandscape.Quat Langlandscape.Local Polynomial

variable {a b : ℤ}

/-- H1: star (conjugation) preserves the local lattice of an order. (`s03-stabfree`) -/
theorem star_mem_localLattice {p : ℕ} [Fact p.Prime] {O : GL2TF.Quat.QOrder a b}
    {z : QuatAlg ℚ_[p] a b}
    (hz : z ∈ GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra)) :
    star z ∈ GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  unfold GL2TF.Quat.localLattice at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : star (GL2TF.Quat.baseChange a b (algebraMap ℚ ℚ_[p]) y) =
        GL2TF.Quat.baseChange a b (algebraMap ℚ ℚ_[p]) (star y) := by
      ext <;> simp [GL2TF.Quat.baseChange]
    rw [h1]
    exact Submodule.subset_span ⟨star y, GL2TF.Quat.star_mem_order O hy, rfl⟩
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hprobe : star (algebraMap ℤ_[p] (QuatAlg ℚ_[p] a b) c) =
        algebraMap ℤ_[p] (QuatAlg ℚ_[p] a b) c := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (QuatAlg ℚ_[p] a b) c]
      exact QuaternionAlgebra.star_coe _
    rw [Algebra.smul_def, star_mul, hprobe, ← Algebra.commutes, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hx

/-- H2: the local lattice of an order is a `ℤ_[p]`-subalgebra. (`s03-stabfree`) -/
theorem localLattice_subalgebra {p : ℕ} [Fact p.Prime] (O : GL2TF.Quat.QOrder a b) :
    ∃ S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b),
      Subalgebra.toSubmodule S =
        GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra) :=
  (GL2TF.Quat.localLattice_basic p (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top).2.2.2
    O

/-- H3: the inverse of a unit with `ℤ_[p]`-unit reduced norm stays in the local lattice of an order. (`s03-stabfree`) -/
theorem inv_mem_localLattice_of_nrd {p : ℕ} [Fact p.Prime] {O : GL2TF.Quat.QOrder a b}
    {u : (QuatAlg ℚ_[p] a b)ˣ}
    (hu : (u : QuatAlg ℚ_[p] a b) ∈
      GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra))
    {v : ℤ_[p]ˣ}
    (hv : GL2TF.Quat.nrd (u : QuatAlg ℚ_[p] a b) = algebraMap ℤ_[p] ℚ_[p] (v : ℤ_[p])) :
    ((u⁻¹ : (QuatAlg ℚ_[p] a b)ˣ) : QuatAlg ℚ_[p] a b) ∈
      GL2TF.Quat.localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  have hv' : ((Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom v : ℚ_[p]ˣ) : ℚ_[p]) =
      GL2TF.Quat.nrd (u : QuatAlg ℚ_[p] a b) := hv.symm
  have hkey := (GL2TF.Quat.isUnit_iff_isUnit_nrd (R := ℚ_[p]) (a := a) (b := b)).2 u
    (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom v) hv'
  rw [hkey]
  have hcast : (((Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom v)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) =
      algebraMap ℤ_[p] ℚ_[p] ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    have h1 : (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom v)⁻¹ =
        Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (v⁻¹) := (map_inv _ _).symm
    rw [h1]
    rfl
  rw [hcast]
  have hsmul : ∀ (c : ℤ_[p]) (w : QuatAlg ℚ_[p] a b),
      (algebraMap ℤ_[p] ℚ_[p] c : ℚ_[p]) • w = c • w := by
    intro c w
    rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] _ c]
  rw [hsmul]
  exact Submodule.smul_mem _ _ (star_mem_localLattice hu)

/-- H4: `aeval` commutes with a ring hom fixing the integers. (`s03-stabfree`) -/
theorem aeval_map_intCast {A B : Type*} [Ring A] [Ring B] (φ : A →+* B)
    (hφ : ∀ n : ℤ, φ ((n : ℤ) : A) = ((n : ℤ) : B)) (w : A) (p : ℤ[X]) :
    aeval (φ w) p = φ (aeval w p) := by
  have hcomp : φ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext fun n => hφ n
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂ p (algebraMap ℤ A) φ w, hcomp]

/-- H5: `baseChange` commutes with `aeval` of an integer polynomial. (`s03-stabfree`) -/
theorem baseChange_aeval {a b : ℤ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : QuatAlg R a b) (p : ℤ[X]) :
    GL2TF.Quat.baseChange a b f (aeval x p) = aeval (GL2TF.Quat.baseChange a b f x) p := by
  have hφ : ∀ n : ℤ, GL2TF.Quat.baseChange a b f ((n : ℤ) : QuatAlg R a b) =
      ((n : ℤ) : QuatAlg S a b) := fun n => map_intCast _ n
  exact (aeval_map_intCast (GL2TF.Quat.baseChange a b f) hφ x p).symm

/-- H6: `aeval` commutes with conjugation by units. (`s03-stabfree`) -/
theorem aeval_conj_units {A : Type*} [Ring A] (X W : Aˣ) (p : ℤ[X]) :
    aeval (((X⁻¹ * W * X : Aˣ) : A)) p = ((X⁻¹ : Aˣ) : A) * aeval (W : A) p * (X : A) := by
  have hpow : ∀ i : ℕ, (((X⁻¹ * W * X : Aˣ) : A)) ^ i =
      ((X⁻¹ : Aˣ) : A) * (W : A) ^ i * (X : A) := by
    intro i
    have h := conj_pow (a := (X⁻¹ : Aˣ)) (b := W) (i := i)
    rw [inv_inv] at h
    have h' := congrArg (fun u : Aˣ => (u : A)) h
    simpa using h'
  rw [aeval_def, aeval_def, eval₂_eq_sum_range, eval₂_eq_sum_range, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpow i]
  have h : ((X⁻¹ : Aˣ) : A) * (algebraMap ℤ A (p.coeff i) * ((W : A) ^ i * (X : A))) =
      algebraMap ℤ A (p.coeff i) * (((X⁻¹ : Aˣ) : A) * ((W : A) ^ i * (X : A))) := by
    rw [← mul_assoc, (Algebra.commutes (p.coeff i) ((X⁻¹ : Aˣ) : A)).symm, mul_assoc]
  simp only [mul_assoc]
  exact h.symm

/-- H7: `aeval` of an integer polynomial at an element of a subalgebra stays in the subalgebra. (`s03-stabfree`) -/
theorem aeval_int_mem {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) (p : ℤ[X]) : aeval x p ∈ S := by
  rw [← Polynomial.aeval_map_algebraMap R x p, aeval_def, eval₂_eq_sum_range]
  refine S.sum_mem fun i _ => ?_
  rw [Polynomial.coeff_map]
  exact S.mul_mem (S.algebraMap_mem _) (S.pow_mem hx i)

/-- H8: reduced norm commutes with `localProj` (copy of `LevelNrd.nrd_localProj`, not in scope here). (`s03-stabfree`) -/
theorem nrd_localProj' {a b : ℤ} {p : ℕ} [Fact p.Prime] (z : BHat a b) :
    GL2TF.Quat.nrd (localProj a b p z) = adeleProj p (GL2TF.Quat.nrd (z : QuatAlg FinAdele a b)) :=
  ((GL2TF.Quat.nrd_trd_basic (R := FinAdele) (a := a) (b := b)).2.2.2 ℚ_[p] (adeleProj p) z).1

/-- **Piece G: `stabFree_core`** (tex steps (i)–(vi) of `lem:s03-stabfree`, globalisation (vi)).
Given the local core `hlocal` (piece F): an `ℓ`-neighbour `y` of `x` stabilised by
`γ ∈ Γ_x \ {±1}` lies in the same double coset: `mk (x*y) = mk x`. -/
theorem stabFree_core (d : DefiniteData) {ℓ : ℕ} [Fact ℓ.Prime] (hℓD : ¬ ℓ ∣ d.D)
    (hlocal : ∀ {x y : (BHat d.a d.b)ˣ}, y ∈ GL2TF.Quat.normNSet d.O.1 ℓ →
      ∀ {γ : (QuatAlg ℚ d.a d.b)ˣ}, γ ∈ Gam d.Ohat x → γ ∈ Gam d.Ohat (x * y) → γ ∉ pmOne →
      ∃ (t : ℤ) (p : ℤ[X]) (π : (QuatAlg ℚ d.a d.b)ˣ),
        GL2TF.Quat.nrd (π : QuatAlg ℚ d.a d.b) = (ℓ : ℚ) ∧
        (π : QuatAlg ℚ d.a d.b) = Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p ∧
        localComponent d ℓ hℓD
          (y⁻¹ * (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x)) ∈ GL2Zl ℓ) :
    ∀ (x y : (BHat d.a d.b)ˣ), y ∈ GL2TF.Quat.normNSet d.O.1 ℓ →
      ∀ γ ∈ Gam d.Ohat x, γ ∉ pmOne → γ ∈ Gam d.Ohat (x * y) →
        DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (x * y) =
          DoubleCoset.mk (globalUnits d.a d.b) d.Ohat x := by
  intro x y hy γ hγx hpm hγxy
  obtain ⟨_, p, π, hnrd, hπ, hloc⟩ := hlocal hy hγx hγxy hpm
  set u : (BHat d.a d.b)ˣ := y⁻¹ * (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x) with hu_def
  have hloc' : localComponent d ℓ hℓD u ∈ GL2Zl ℓ := by
    rw [hu_def]
    exact hloc
  have hℓcase : localProj d.a d.b ℓ ((u : (BHat d.a d.b)ˣ) : BHat d.a d.b) ∈
      GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
    localProj d.a d.b ℓ (((u⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈
      GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) := by
    obtain ⟨h1, h2⟩ := hloc'
    refine ⟨(d.mem_localLattice_iff_iota ℓ hℓD _).2 fun i j => ?_,
      (d.mem_localLattice_iff_iota ℓ hℓD _).2 fun i j => ?_⟩
    · rw [← localComponent_val]
      exact h1 i j
    · have h2' : (localComponent d ℓ hℓD u)⁻¹ = localComponent d ℓ hℓD (u⁻¹) := (map_inv _ _).symm
      rw [← localComponent_val, ← h2']
      exact h2 i j
  have hu_loc : ∀ q : Nat.Primes,
      localProj d.a d.b (q:ℕ) ((u : (BHat d.a d.b)ˣ) : BHat d.a d.b) ∈
        GL2TF.Quat.localLattice (q:ℕ) (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
      localProj d.a d.b (q:ℕ) (((u⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈
        GL2TF.Quat.localLattice (q:ℕ) (Subalgebra.toSubmodule d.O.1.toSubalgebra) := by
    intro q
    by_cases hq : (q : ℕ) = ℓ
    · have hq' : q = primeIdx ℓ := Subtype.ext hq
      subst hq'
      exact hℓcase
    · -- q ≠ ℓ
      obtain ⟨S, hS⟩ := localLattice_subalgebra (p := (q : ℕ)) d.O.1
      have mem_iff : ∀ z : QuatAlg ℚ_[(q:ℕ)] d.a d.b,
          z ∈ GL2TF.Quat.localLattice (q:ℕ) (Subalgebra.toSubmodule d.O.1.toSubalgebra) ↔ z ∈ S := by
        intro z
        rw [← hS, Subalgebra.mem_toSubmodule]
      have hzY : localProj d.a d.b (q:ℕ) ((y : (BHat d.a d.b)ˣ) : BHat d.a d.b) ∈ S :=
        (mem_iff _).1 (localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hy.1 (q:ℕ))
      obtain ⟨w, hw⟩ := hy.2
      obtain ⟨v, hv⟩ := (zhat_units_explicit (((w : Zhat) : FinAdele))).1 ⟨w, rfl⟩ q
      have hnrdY : GL2TF.Quat.nrd (localProj d.a d.b (q:ℕ) ((y : (BHat d.a d.b)ˣ) : BHat d.a d.b)) =
          (ℓ : ℚ_[(q:ℕ)]) * ((v : ℤ_[(q:ℕ)]) : ℚ_[(q:ℕ)]) := by
        rw [nrd_localProj', hw, map_mul, map_natCast]
        have he : adeleProj (q:ℕ) (((w : Zhat) : FinAdele)) = ((v : ℤ_[(q:ℕ)]) : ℚ_[(q:ℕ)]) := hv.symm
        rw [he]
      have hℓu : IsUnit (ℓ : ℤ_[(q:ℕ)]) := by
        have key : IsUnit (ℓ : ℤ_[(q:ℕ)]) ↔ ¬ ((q:ℕ) : ℤ_[(q:ℕ)]) ∣ (ℓ : ℤ_[(q:ℕ)]) := by
          rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.not_isUnit_iff, not_not]
        rw [key, ← PadicInt.norm_lt_one_iff_dvd]
        have hcast : (ℓ : ℤ_[(q:ℕ)]) = ((ℓ : ℤ) : ℤ_[(q:ℕ)]) := by norm_cast
        rw [hcast, PadicInt.norm_int_lt_one_iff_dvd]
        intro h
        have h' : (q:ℕ) ∣ ℓ := by exact_mod_cast h
        have hdvd : ℓ = (q:ℕ) :=
          (Fact.out : ℓ.Prime).dvd_iff_eq (a := (q:ℕ)) q.2.ne_one |>.mp h'
        exact hq hdvd.symm
      obtain ⟨v', hv'⟩ := hℓu.mul v.isUnit
      have hnrdYv : GL2TF.Quat.nrd (localProj d.a d.b (q:ℕ) ((y : (BHat d.a d.b)ˣ) : BHat d.a d.b)) =
          algebraMap ℤ_[(q:ℕ)] ℚ_[(q:ℕ)] (v' : ℤ_[(q:ℕ)]) := by
        rw [hnrdY, hv', map_mul, map_natCast, PadicInt.algebraMap_apply]
      have hzYinv : localProj d.a d.b (q:ℕ) (((y⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈ S := by
        have h1 : localProj d.a d.b (q:ℕ) (((y⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
            ((((localProjUnits d.a d.b (q:ℕ) y)⁻¹ : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ)) :
              QuatAlg ℚ_[(q:ℕ)] d.a d.b) := by
          rw [← localProjUnits_val, map_inv]
        rw [h1]
        exact (mem_iff _).1 (inv_mem_localLattice_of_nrd
          (u := localProjUnits d.a d.b (q:ℕ) y) (v := v')
          (by rw [localProjUnits_val]; exact (mem_iff _).2 hzY)
          (by rw [localProjUnits_val]; exact hnrdYv))
      -- the conjugate wγ := x⁻¹ * ι γ * x is in Ô
      have hwγ : x⁻¹ * iotaU d.a d.b γ * x ∈ d.Ohat := (mem_Gam_iff d.Ohat x γ).1 hγx
      obtain ⟨hg, _⟩ := (mem_orderCompletionUnits_iff_local d.O.1 (x⁻¹ * iotaU d.a d.b γ * x)).1 hwγ q
      have hgS : localProj d.a d.b (q:ℕ) (((x⁻¹ * iotaU d.a d.b γ * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈ S :=
        (mem_iff _).1 hg
      have hXu : localProj d.a d.b (q:ℕ) ((x : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
          ((localProjUnits d.a d.b (q:ℕ) x : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) :=
        (localProjUnits_val x).symm
      have hXui : localProj d.a d.b (q:ℕ) (((x⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
          ((((localProjUnits d.a d.b (q:ℕ) x)⁻¹ : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ)) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) := by
        rw [← localProjUnits_val, map_inv]
      have hιπ : localProj d.a d.b (q:ℕ) ((Units.map (finEmbed d.a d.b).toMonoidHom π : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
          aeval (localProj d.a d.b (q:ℕ) ((iotaU d.a d.b γ : (BHat d.a d.b)ˣ) : BHat d.a d.b)) p := by
        have h0 : ((Units.map (finEmbed d.a d.b).toMonoidHom π : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
            finEmbed d.a d.b (π : QuatAlg ℚ d.a d.b) := rfl
        have h1 : ((iotaU d.a d.b γ : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
            finEmbed d.a d.b (γ : QuatAlg ℚ d.a d.b) := rfl
        rw [h0, hπ, h1, localProj_finEmbed, baseChange_aeval, ← localProj_finEmbed]
      have hιγU : localProjUnits d.a d.b (q:ℕ) (iotaU d.a d.b γ) =
          localProjUnits d.a d.b (q:ℕ) x * localProjUnits d.a d.b (q:ℕ) (x⁻¹ * iotaU d.a d.b γ * x) *
            (localProjUnits d.a d.b (q:ℕ) x)⁻¹ := by
        have hconj : (iotaU d.a d.b γ : (BHat d.a d.b)ˣ) = x * (x⁻¹ * iotaU d.a d.b γ * x) * x⁻¹ := by group
        conv_lhs => rw [hconj]
        rw [map_mul, map_mul, map_inv]
      have hιγ : localProj d.a d.b (q:ℕ) ((iotaU d.a d.b γ : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
          ((localProjUnits d.a d.b (q:ℕ) x : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) *
            ((localProjUnits d.a d.b (q:ℕ) (x⁻¹ * iotaU d.a d.b γ * x) : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) :
              QuatAlg ℚ_[(q:ℕ)] d.a d.b) *
            ((((localProjUnits d.a d.b (q:ℕ) x)⁻¹ : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ)) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) := by
        rw [← localProjUnits_val, hιγU, Units.val_mul, Units.val_mul]
      have hW : ((localProjUnits d.a d.b (q:ℕ) (x⁻¹ * iotaU d.a d.b γ * x) : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) :
          QuatAlg ℚ_[(q:ℕ)] d.a d.b) =
          localProj d.a d.b (q:ℕ) (((x⁻¹ * iotaU d.a d.b γ * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b) :=
        (localProjUnits_val _).symm
      have hkey : localProj d.a d.b (q:ℕ) (((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
          aeval (localProj d.a d.b (q:ℕ) (((x⁻¹ * iotaU d.a d.b γ * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b)) p := by
        rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hXui, hXu, hιπ, hιγ, ← hW]
        have h6 := aeval_conj_units ((localProjUnits d.a d.b (q:ℕ) x)⁻¹)
          (localProjUnits d.a d.b (q:ℕ) (x⁻¹ * iotaU d.a d.b γ * x)) p
        rw [inv_inv, Units.val_mul, Units.val_mul] at h6
        rw [h6]
        have hXX : (((localProjUnits d.a d.b (q:ℕ) x)⁻¹ : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) :
              QuatAlg ℚ_[(q:ℕ)] d.a d.b) *
            ((localProjUnits d.a d.b (q:ℕ) x : (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) = 1 :=
          (localProjUnits d.a d.b (q:ℕ) x).inv_val
        simp only [mul_assoc]
        rw [hXX, mul_one, ← mul_assoc, hXX, one_mul]
      have hzπS : localProj d.a d.b (q:ℕ) (((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈ S := by
        rw [hkey]
        exact aeval_int_mem S hgS p
      -- the reduced norm of the w-part is ℓ (an adelic unit at q)
      have hπn : GL2TF.Quat.nrd (((Units.map (finEmbed d.a d.b).toMonoidHom π : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
          (ℓ : FinAdele) := by
        have h0 : ((Units.map (finEmbed d.a d.b).toMonoidHom π : (BHat d.a d.b)ˣ) : BHat d.a d.b) =
            finEmbed d.a d.b (π : QuatAlg ℚ d.a d.b) := rfl
        have hbc : GL2TF.Quat.nrd (finEmbed d.a d.b (π : QuatAlg ℚ d.a d.b)) =
            algebraMap ℚ FinAdele (GL2TF.Quat.nrd (π : QuatAlg ℚ d.a d.b)) :=
          ((GL2TF.Quat.nrd_trd_basic (R := ℚ) (a := d.a) (b := d.b)).2.2.2 FinAdele
            (algebraMap ℚ FinAdele) (π : QuatAlg ℚ d.a d.b)).1
        rw [h0, hbc, hnrd, map_natCast]
      have hnrdw : GL2TF.Quat.nrd (((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
          (ℓ : FinAdele) := by
        have hmul : ∀ u v : BHat d.a d.b,
            GL2TF.Quat.nrd (u * v) = GL2TF.Quat.nrd u * GL2TF.Quat.nrd v :=
          (GL2TF.Quat.nrd_trd_basic.{0, 0} (R := FinAdele) (a := d.a) (b := d.b)).2.1
        have hnrd1 : GL2TF.Quat.nrd (1 : BHat d.a d.b) = 1 := by
          show GL2TF.Quat.nrd (⟨1, 0, 0, 0⟩ : BHat d.a d.b) = 1
          simp [GL2TF.Quat.nrd]
        have hx1 : ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b) * ((x : (BHat d.a d.b)ˣ) : BHat d.a d.b) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [Units.val_mul, Units.val_mul, hmul, hmul, hπn, mul_assoc,
          mul_comm (ℓ : FinAdele) (GL2TF.Quat.nrd ((x : (BHat d.a d.b)ˣ) : BHat d.a d.b)),
          ← mul_assoc, ← hmul, hx1, hnrd1, one_mul]
      obtain ⟨vℓ, hvℓ⟩ := hℓu
      have hnrdW : GL2TF.Quat.nrd (localProj d.a d.b (q:ℕ) (((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x : (BHat d.a d.b)ˣ)) : BHat d.a d.b)) =
          algebraMap ℤ_[(q:ℕ)] ℚ_[(q:ℕ)] (vℓ : ℤ_[(q:ℕ)]) := by
        rw [nrd_localProj', hnrdw, map_natCast, PadicInt.algebraMap_apply]
        have hc : (ℓ : ℚ_[(q:ℕ)]) = ((ℓ : ℤ_[(q:ℕ)]) : ℚ_[(q:ℕ)]) := by norm_cast
        rw [hc, ← hvℓ]
      have hzwinv : localProj d.a d.b (q:ℕ) ((((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x)⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) ∈ S := by
        have h1 : localProj d.a d.b (q:ℕ) ((((x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x)⁻¹ : (BHat d.a d.b)ˣ)) : BHat d.a d.b) =
            (((localProjUnits d.a d.b (q:ℕ) (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x))⁻¹ :
              (QuatAlg ℚ_[(q:ℕ)] d.a d.b)ˣ) : QuatAlg ℚ_[(q:ℕ)] d.a d.b) := by
          rw [← localProjUnits_val, map_inv]
        rw [h1]
        exact (mem_iff _).1 (inv_mem_localLattice_of_nrd
          (u := localProjUnits d.a d.b (q:ℕ) (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x))
          (v := vℓ)
          (by rw [localProjUnits_val]; exact (mem_iff _).2 hzπS)
          (by rw [localProjUnits_val]; exact hnrdW))
      refine ⟨?_, ?_⟩
      · rw [hu_def, Units.val_mul, map_mul]
        exact (mem_iff _).2 (S.mul_mem hzYinv hzπS)
      · have huinv_eq : (u⁻¹ : (BHat d.a d.b)ˣ) =
            (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x)⁻¹ * y := by
          rw [hu_def]
          group
        rw [huinv_eq, Units.val_mul, map_mul]
        exact (mem_iff _).2 (S.mul_mem hzwinv hzY)
  have hu : u ∈ d.Ohat := (mem_orderCompletionUnits_iff_local d.O.1 u).2 hu_loc
  have hgu : Units.map (finEmbed d.a d.b).toMonoidHom π ∈ globalUnits d.a d.b := ⟨π, rfl⟩
  have hxy : x * y = Units.map (finEmbed d.a d.b).toMonoidHom π * (x * u⁻¹) := by
    rw [hu_def]
    group
  rw [hxy, DoubleCoset.mk_mem_mul ⟨_, hgu⟩, DoubleCoset.mk_mul_mem ⟨u⁻¹, Subgroup.inv_mem _ hu⟩]

end Langlandscape.StabFree.Core
