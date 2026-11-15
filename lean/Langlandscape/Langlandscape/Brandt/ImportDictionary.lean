/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Hecke
import AlgJL.VolIII.Brandt.Brandt

/-!
# Dictionary with the import at level `Ô^×`, weight `2` (S01-L12)

`plan/staged/stage-01-quaternion-foundations.tex`, `rem:s01-dictionary` (at `U = Ô^×`, trivial coefficients),
`def:s01-pairing`, `prop:s01-adjoint`.

* `mem_normNSet_iff` : `x ∈ Ô_ℓ ↔ ι_ℓ(x_ℓ) ∈ K t_{1,0} K` and `x_q ∈ 𝒪_q^×` for `q ≠ ℓ` (from the import's public
  `localHeckeEmbedding_hom` at the trivial level structure of level `1`).
* `dcSet_elemT_eq_normNSet` : `Ô^× ϖ_ℓ Ô^× = Ô_ℓ` for `ℓ ∤ D` (Cartan decomposition at `ℓ`, through the import).
* `Tl_eq_heckeOperator` : our `T_ℓ` on lifts is the import's `heckeOperator O ℓ`.
* `Tl_matrix_eq_brandtMatrix` : `(T_ℓ 1_{c'})(c) = B(ℓ)_{cc'}` (import `brandtMatrix`).
* `brandtPairing_eq_import` : `⟨a, b⟩ = 2 · weightedPairing(ν a, ν b)` for `k = 2` (factor `2` since `-1 ∈ Ô^×`).
* `Tl_selfAdjoint_units` : `T_ℓ^t` is self-adjoint for `⟨,⟩` on `R[X]`, from the import's `brandt_weighted_symmetry`.

Re-proofs of private import helpers (risk R6) carry a source comment.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical Pointwise ValuativeRel GL2TF

/-! ### Generic helpers -/

section Helpers

variable {a b : ℤ}

/-- `def:s01-B` (`s01-B`): equal `q`-components of units give equal `q`-components of the units and their inverses
in `B_q`. -/
theorem localProj_eq_of_localProjUnits_eq {q : ℕ} [Fact q.Prime] {u v : (GL2TF.Quat.BHat a b)ˣ}
    (h : localProjUnits a b q u = localProjUnits a b q v) :
    localProj a b q (u : GL2TF.Quat.BHat a b) = localProj a b q (v : GL2TF.Quat.BHat a b) ∧
      localProj a b q ((u⁻¹ : (GL2TF.Quat.BHat a b)ˣ) : GL2TF.Quat.BHat a b) =
        localProj a b q ((v⁻¹ : (GL2TF.Quat.BHat a b)ˣ) : GL2TF.Quat.BHat a b) := by
  have h1 := congrArg Units.val h
  have h2 : localProjUnits a b q u⁻¹ = localProjUnits a b q v⁻¹ := by rw [map_inv, map_inv, h]
  have h3 := congrArg Units.val h2
  exact ⟨h1, h3⟩

/-- `def:s01-B` (`s01-B`): an order is determined by its underlying subalgebra. Re-proof of the import's private
`bi_qorder_ext` (`AlgJL/VolIII/Brandt/BrandtInstances.lean`). -/
theorem qorder_ext {O O' : GL2TF.Quat.QOrder a b} (h : O.toSubalgebra = O'.toSubalgebra) : O = O' := by
  cases O; cases O'; cases h; rfl

end Helpers

/-! ### `Ô_ℓ` through the local Hecke embedding -/

section NormNSet

variable (d : DefiniteData)

/-- `rem:s01-dictionary` (`s01-dictionary`): the trivial level structure `O → M₂(ℤ/1)` (copied from the import's
`hurwitz_eisenstein`, `AlgJL/VolIII/Brandt/BrandtInstances.lean`). -/
def trivialLevel : GL2TF.Quat.LevelStructure d.O.1 1 :=
  { toRingHom :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    surjective := fun _ => ⟨0, Subsingleton.elim _ _⟩ }

/-- `rem:s01-dictionary` (`s01-dictionary`): the Eichler order of the trivial level structure is `O` (as in the
import's `hurwitz_eisenstein`). -/
theorem eichlerOrder_trivialLevel : GL2TF.Quat.eichlerOrder (trivialLevel d) = d.O.1 := by
  apply qorder_ext
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `rem:s01-dictionary` (`s01-dictionary`): the set of `x ∈ B̂^×` with `x_q, x_q⁻¹ ∈ 𝒪_q` for every prime `q ≠ ℓ`
(the set `R` of the import's `localHeckeEmbedding`). -/
def awaySet : Set (GL2TF.Quat.BHat d.a d.b)ˣ :=
  {x | ∀ q : Nat.Primes, q ≠ primeIdx ℓ →
    localProj d.a d.b q (x : GL2TF.Quat.BHat d.a d.b) ∈
        GL2TF.Quat.localLattice q (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
      localProj d.a d.b q ((x⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) ∈
        GL2TF.Quat.localLattice q (Subalgebra.toSubmodule d.O.1.toSubalgebra)}

/-- `rem:s01-dictionary` (`s01-dictionary`): membership in `awaySet`. -/
theorem mem_awaySet_iff {x : (GL2TF.Quat.BHat d.a d.b)ˣ} :
    x ∈ awaySet d ℓ ↔ ∀ q : Nat.Primes, q ≠ primeIdx ℓ →
      localProj d.a d.b q (x : GL2TF.Quat.BHat d.a d.b) ∈
          GL2TF.Quat.localLattice q (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
        localProj d.a d.b q ((x⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) ∈
          GL2TF.Quat.localLattice q (Subalgebra.toSubmodule d.O.1.toSubalgebra) :=
  Iff.rfl

variable (hℓ : ¬ ℓ ∣ d.D)

/-- `rem:s01-dictionary` (`s01-dictionary`): `Ô_ℓ = {x : ι_ℓ(x_ℓ) ∈ K t_{1,0} K, x_q ∈ 𝒪_q^× (q ≠ ℓ)}`, where
`t_{1,0} = diag(ϖ, 1)` is the import's Cartan element and `K = GL₂(ℤ_ℓ)`. From the import's public
`localHeckeEmbedding_hom` (part `Θ(c_{1,0}) = 1_{Ô_ℓ}`) at the trivial level structure. -/
theorem mem_normNSet_iff (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    x ∈ GL2TF.Quat.normNSet d.O.1 ℓ ↔
      localComponent d ℓ hℓ x ∈
          DoubleCoset.doubleCoset (GL2TF.Local.cartanElement ℚ_[ℓ] 1 0) 𝐊[ℚ_[ℓ]] 𝐊[ℚ_[ℓ]] ∧
        x ∈ awaySet d ℓ := by
  have hpM : ¬ ((primeIdx ℓ : Nat.Primes) : ℕ) ∣ 1 := (Fact.out : ℓ.Prime).not_dvd_one
  have key := (GL2TF.Quat.localHeckeEmbedding_hom d.O d.hD (trivialLevel d) (primeIdx ℓ) hℓ hpM).2.2.2.1 1
  have hx0 := congrFun key x
  simp only [GL2TF.Quat.localHeckeEmbedding, eichlerOrder_trivialLevel, pow_one, Nat.reduceDiv,
    zero_add, Finset.sum_range_one, Nat.sub_zero, Nat.cast_one, Nat.cast_zero] at hx0
  have hx : ((GL2TF.Local.heckeBasis ℚ_[ℓ] 1 0 : GL2TF.Local.sphericalHeckeAlgebra ℚ_[ℓ]) :
        GL (Fin 2) ℚ_[ℓ] → ℂ) (localComponent d ℓ hℓ x) *
        (awaySet d ℓ).indicator (fun _ => (1 : ℂ)) x =
      (GL2TF.Quat.normNSet d.O.1 ℓ).indicator (1 : (GL2TF.Quat.BHat d.a d.b)ˣ → ℂ) x := hx0
  constructor
  · intro hN
    rw [Set.indicator_of_mem hN] at hx
    refine ⟨?_, ?_⟩
    · by_contra hK
      rw [GL2TF.Local.heckeBasis_apply_of_notMem hK, zero_mul] at hx
      exact zero_ne_one hx
    · by_contra hR
      rw [Set.indicator_of_notMem hR, mul_zero] at hx
      exact zero_ne_one hx
  · rintro ⟨hK, hR⟩
    rw [GL2TF.Local.heckeBasis_apply_of_mem hK, Set.indicator_of_mem hR, one_mul] at hx
    by_contra hN
    rw [Set.indicator_of_notMem hN] at hx
    exact one_ne_zero hx

end NormNSet

/-! ### Local facts at `ℓ` -/

section Local

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `rem:s01-dictionary` (`s01-dictionary`): the import's `K_ℓ = 𝐊[ℚ_ℓ]` is our `GL₂(ℤ_ℓ)`. -/
theorem mem_K_iff_GL2Zl (g : GL (Fin 2) ℚ_[ℓ]) : g ∈ 𝐊[ℚ_[ℓ]] ↔ g ∈ Langlandscape.Local.GL2Zl ℓ := by
  refine (GL2TF.mem_Kp_iff (primeIdx ℓ) g).trans ?_
  rw [Langlandscape.Local.mem_GL2Zl_def]
  constructor
  · intro h
    exact ⟨fun i j => (PadicInt.mem_subring_iff ℓ).1 (h i j).1,
      fun i j => (PadicInt.mem_subring_iff ℓ).1 (h i j).2⟩
  · rintro ⟨h1, h2⟩ i j
    exact ⟨(PadicInt.mem_subring_iff ℓ).2 (h1 i j), (PadicInt.mem_subring_iff ℓ).2 (h2 i j)⟩

/-- `rem:s01-dictionary` (`s01-dictionary`): `diag(ℓ, 1) = t_{1,0} k` with `k ∈ GL₂(ℤ_ℓ)` (`ϖ = ℓ · unit`; the
argument of the import's private `hl_norm_unif`, `AlgJL/VolIII/Brandt/HeckeLocal.lean`). -/
theorem diag_eq_cartan_mul :
    ∃ k ∈ Langlandscape.Local.GL2Zl ℓ,
      Langlandscape.Local.diagGL (padicUnit ℓ) 1 = GL2TF.Local.cartanElement ℚ_[ℓ] 1 0 * k := by
  have hset := GL2TF.Local.padic_unif_zpow_smul_integer (p := ℓ) 1
  simp only [zpow_one] at hset
  have hp0 : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨A, hA, hAeq⟩ : ((GL2TF.Local.unif ℚ_[ℓ] : 𝒪[ℚ_[ℓ]]) : ℚ_[ℓ]) ∈
      (ℓ : ℚ_[ℓ]) • (PadicInt.subring ℓ : Set ℚ_[ℓ]) := by
    rw [← hset]; exact ⟨1, Subring.one_mem _, by simp⟩
  obtain ⟨B, hB, hBeq⟩ : (ℓ : ℚ_[ℓ]) ∈
      ((GL2TF.Local.unif ℚ_[ℓ] : 𝒪[ℚ_[ℓ]]) : ℚ_[ℓ]) • (𝒪[ℚ_[ℓ]] : Set ℚ_[ℓ]) := by
    rw [hset]; exact ⟨1, Subring.one_mem _, by simp⟩
  simp only [smul_eq_mul] at hAeq hBeq
  have hB' : ‖B‖ ≤ 1 := (GL2TF.padic_mem_integer_iff (primeIdx ℓ) B).mp hB
  have hA' : ‖A‖ ≤ 1 := (PadicInt.mem_subring_iff ℓ).mp hA
  have hAB : A * B = 1 := by
    have : (ℓ : ℚ_[ℓ]) * (A * B) = (ℓ : ℚ_[ℓ]) * 1 := by
      rw [mul_one, ← mul_assoc, hAeq, hBeq]
    exact mul_left_cancel₀ hp0 this
  have hnB : ‖B‖ = 1 := by
    have h1 : ‖A‖ * ‖B‖ = 1 := by rw [← norm_mul, hAB, norm_one]
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
    nlinarith
  obtain ⟨Bu, hBu⟩ : ∃ Bu : ℚ_[ℓ]ˣ, (Bu : ℚ_[ℓ]) = B :=
    ⟨⟨B, A, by rw [mul_comm]; exact hAB, hAB⟩, rfl⟩
  refine ⟨Langlandscape.Local.diagGL Bu 1, ?_, ?_⟩
  · rw [Langlandscape.Local.diagGL, Langlandscape.Local.matGL_mem_GL2Zl_iff]
    refine ⟨?_, by simp, by simp, by simp, ?_⟩
    · rw [hBu]; exact hB'
    · simp [hBu, hnB]
  · apply Units.ext
    rw [Units.val_mul, GL2TF.Local.cartanElement_val, Langlandscape.Local.diagGL_val,
      Langlandscape.Local.diagGL_val, hBu]
    simp [padicUnit, hBeq]

end Local

/-! ### `Ô^× ϖ_ℓ Ô^× = Ô_ℓ` -/

section DoubleCosetEq

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `rem:s01-dictionary` (`s01-dictionary`): `ϖ_ℓ` has all components `1` away from `ℓ`. -/
theorem elemT_mem_awaySet : elemT d ℓ hℓ ∈ awaySet d ℓ := by
  refine (mem_awaySet_iff d ℓ).2 fun q hq => ?_
  have hne : (q : ℕ) ≠ ℓ := fun h => hq (Subtype.ext h)
  have h1 : localProjUnits d.a d.b q (elemT d ℓ hℓ) = localProjUnits d.a d.b q 1 := by
    rw [elemT, localProjUnits_localEmbedGL_of_ne _ hne, map_one]
  obtain ⟨e1, e2⟩ := localProj_eq_of_localProjUnits_eq h1
  rw [e1, e2, inv_one, Units.val_one, map_one]
  exact ⟨one_mem_localLattice _ _, one_mem_localLattice _ _⟩

/-- `rem:s01-dictionary` (`s01-dictionary`): if `x_q ∈ 𝒪_q^×` for all `q ≠ ℓ`, then the `ℓ`-away part of `x` lies in
`Ô^×`. -/
theorem awayAt_mem_Ohat {x : (GL2TF.Quat.BHat d.a d.b)ˣ} (hx : x ∈ awaySet d ℓ) :
    awayAt d ℓ hℓ x ∈ d.Ohat := by
  refine (mem_orderCompletionUnits_iff_local d.O.1 _).2 fun p => ?_
  by_cases hp : p = primeIdx ℓ
  · subst hp
    have h1 : localProjUnits d.a d.b ℓ (awayAt d ℓ hℓ x) = localProjUnits d.a d.b ℓ 1 := by
      rw [localProjUnits_awayAt, map_one]
    obtain ⟨e1, e2⟩ := localProj_eq_of_localProjUnits_eq h1
    have key : localProj d.a d.b ℓ ((awayAt d ℓ hℓ x : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) ∈
          GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
        localProj d.a d.b ℓ (((awayAt d ℓ hℓ x)⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) ∈
          GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) := by
      rw [e1, e2, inv_one, Units.val_one, map_one]
      exact ⟨one_mem_localLattice _ _, one_mem_localLattice _ _⟩
    exact key
  · have hne : (p : ℕ) ≠ ℓ := fun h => hp (Subtype.ext h)
    obtain ⟨e1, e2⟩ := localProj_eq_of_localProjUnits_eq (localProjUnits_awayAt_of_ne (hp := hℓ) x hne)
    rw [e1, e2]
    exact (mem_awaySet_iff d ℓ).1 hx p hp

/-- `rem:s01-dictionary` (`s01-dictionary`): `diag(ℓ, 1) ∈ K t_{1,0} K`. -/
theorem diag_mem_cartan :
    Langlandscape.Local.diagGL (padicUnit ℓ) 1 ∈
      DoubleCoset.doubleCoset (GL2TF.Local.cartanElement ℚ_[ℓ] 1 0) 𝐊[ℚ_[ℓ]] 𝐊[ℚ_[ℓ]] := by
  obtain ⟨k, hk, hdiag⟩ := diag_eq_cartan_mul ℓ
  refine DoubleCoset.mem_doubleCoset.2 ⟨1, Subgroup.one_mem _, k, (mem_K_iff_GL2Zl ℓ k).2 hk, ?_⟩
  rw [one_mul]
  exact hdiag

/-- `rem:s01-dictionary` (`s01-dictionary`, Cartan decomposition at `ℓ ∤ D`): `Ô^× ϖ_ℓ Ô^× = Ô_ℓ`, the import's
`normNSet O ℓ`. -/
theorem dcSet_elemT_eq_normNSet : dcSet d.Ohat (elemT d ℓ hℓ) = GL2TF.Quat.normNSet d.O.1 ℓ := by
  have hmem := diag_mem_cartan ℓ
  have hdc := DoubleCoset.doubleCoset_eq_of_mem hmem
  have hϖ : elemT d ℓ hℓ ∈ GL2TF.Quat.normNSet d.O.1 ℓ := by
    rw [mem_normNSet_iff d ℓ hℓ]
    refine ⟨?_, elemT_mem_awaySet d ℓ hℓ⟩
    rw [elemT, localComponent_localEmbedGL]
    exact hmem
  have hNb := GL2TF.Quat.normNSet_basic d.O.1 ℓ (Fact.out : ℓ.Prime).pos
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet _ _).1 hy
    exact hNb.1 _ hϖ u hu v hv
  · intro hy
    obtain ⟨hloc, haway⟩ := (mem_normNSet_iff d ℓ hℓ y).1 hy
    rw [← hdc] at hloc
    obtain ⟨k1, hk1, k2, hk2, he⟩ := DoubleCoset.mem_doubleCoset.1 hloc
    refine (mem_dcSet _ _).2 ⟨awayAt d ℓ hℓ y * localEmbedGL d ℓ hℓ k1,
      d.Ohat.mul_mem (awayAt_mem_Ohat d ℓ hℓ haway)
        (localEmbedGL_mem_Ohat ((mem_K_iff_GL2Zl ℓ k1).1 hk1)),
      localEmbedGL d ℓ hℓ k2, localEmbedGL_mem_Ohat ((mem_K_iff_GL2Zl ℓ k2).1 hk2), ?_⟩
    calc y = awayAt d ℓ hℓ y * localEmbedGL d ℓ hℓ (localComponent d ℓ hℓ y) :=
          (awayAt_mul_localEmbedGL y).symm
      _ = awayAt d ℓ hℓ y * localEmbedGL d ℓ hℓ (k1 * Langlandscape.Local.diagGL (padicUnit ℓ) 1 * k2) := by
          rw [he]
      _ = awayAt d ℓ hℓ y * localEmbedGL d ℓ hℓ k1 * elemT d ℓ hℓ * localEmbedGL d ℓ hℓ k2 := by
          simp only [map_mul, elemT, mul_assoc]

end DoubleCosetEq

/-! ### `T_ℓ` and the Brandt matrix -/

section Hecke

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (R : Type*) [CommRing R]
  (hfin : (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)).relIndex d.Ohat ≠ 0)

/-- `rem:s01-dictionary` (`s01-dictionary`, `U = Ô^×`, `k = 2`, trivial coefficients): our `T_ℓ` on `R^X`, read on
the lift `x ↦ f(B^× x Ô^×)`, is the import's `heckeOperator O ℓ`. -/
theorem Tl_eq_heckeOperator (f : ZXdual d.Ohat R) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    Tl d d.Ohat ℓ hℓ R hfin f (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat x) =
      GL2TF.Quat.heckeOperator d.O.1 ℓ (liftFun d.Ohat R f) x := by
  have hEq := dcSet_elemT_eq_normNSet d ℓ hℓ
  rw [Tl_eq_heckeT, heckeT_apply_mk]
  simp only [GL2TF.Quat.heckeOperator, GL2TF.HeckeModule.heckeAct]
  refine finsum_congr fun c => ?_
  rw [coe_heckeFun]
  by_cases h : Quotient.out c ∈ dcSet d.Ohat (elemT d ℓ hℓ)
  · have h' : Quotient.out c ∈ GL2TF.Quat.normNSet d.O.1 ℓ := by rw [← hEq]; exact h
    rw [heckeCoeff_of_mem d.Ohat (elemT d ℓ hℓ) R h, one_smul, Set.indicator_of_mem h', Pi.one_apply, one_smul]
  · have h' : Quotient.out c ∉ GL2TF.Quat.normNSet d.O.1 ℓ := by rw [← hEq]; exact h
    rw [heckeCoeff_of_notMem d.Ohat (elemT d ℓ hℓ) R h, zero_smul, Set.indicator_of_notMem h', zero_smul]

/-- `rem:s01-dictionary` (`s01-dictionary`): the predicate counted by the Brandt matrix entry `B(ℓ)_{cc'}`, on left
cosets `q = y Ô^×`. -/
abbrev brandtPred (c c' : XB d.Ohat) (q : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat) : Prop :=
  Quotient.out q ∈ GL2TF.Quat.normNSet d.O.1 ℓ ∧
    DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c * Quotient.out q) = c'

/-- `rem:s01-dictionary` (`s01-dictionary`): the matrix of `T_ℓ` at level `Ô^×` is the import's Brandt matrix,
`(T_ℓ 1_{c'})(c) = B(ℓ)_{cc'}`. -/
theorem Tl_matrix_eq_brandtMatrix (c c' : XB d.Ohat) :
    Tl d d.Ohat ℓ hℓ R hfin (Pi.single c' (1 : R)) c = (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : R) := by
  have hNb := GL2TF.Quat.normNSet_basic d.O.1 ℓ (Fact.out : ℓ.Prime).pos
  have hNright : ∀ y ∈ GL2TF.Quat.normNSet d.O.1 ℓ, ∀ u ∈ d.Ohat, y * u ∈ GL2TF.Quat.normNSet d.O.1 ℓ := by
    intro y hy u hu
    have := hNb.1 y hy 1 (Subgroup.one_mem _) u hu
    rwa [one_mul] at this
  have hcard : GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' = Nat.card {q // brandtPred d ℓ c c' q} := by
    simp only [GL2TF.Quat.brandtMatrix]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    constructor
    · rintro ⟨y, hy, rfl, hc⟩
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul d.Ohat y
      refine ⟨?_, ?_⟩
      · rw [hu]; exact hNright y hy u u.2
      · rw [hu, ← mul_assoc]
        have e : DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c * y * (u : (GL2TF.Quat.BHat d.a d.b)ˣ)) =
            DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c * y) := by
          rw [DoubleCoset.eq]
          exact ⟨1, (globalUnits d.a d.b).one_mem, (u : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹, d.Ohat.inv_mem u.2,
            by group⟩
        exact e.trans hc
    · rintro ⟨h1, h2⟩
      exact ⟨Quotient.out q, h1, QuotientGroup.out_eq' q, h2⟩
  have hfinS : {q | brandtPred d ℓ c c' q}.Finite :=
    hNb.2.2.2.1.subset fun q hq => ⟨Quotient.out q, (show brandtPred d ℓ c c' q from hq).1, QuotientGroup.out_eq' q⟩
  have hL : Tl d d.Ohat ℓ hℓ R hfin (Pi.single c' (1 : R)) c =
      ∑ᶠ q : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat, if brandtPred d ℓ c c' q then (1 : R) else 0 := by
    have h0 := Tl_eq_heckeOperator d ℓ hℓ R hfin (Pi.single c' (1 : R)) (Quotient.out c)
    rw [DoubleCoset.out_eq'] at h0
    rw [h0]
    simp only [GL2TF.Quat.heckeOperator, GL2TF.HeckeModule.heckeAct]
    refine finsum_congr fun q => ?_
    by_cases h1 : Quotient.out q ∈ GL2TF.Quat.normNSet d.O.1 ℓ
    · rw [Set.indicator_of_mem h1, Pi.one_apply, one_smul]
      simp only [liftFun]
      by_cases h2 : DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c * Quotient.out q) = c'
      · rw [if_pos (And.intro h1 h2 : brandtPred d ℓ c c' q), h2, Pi.single_eq_same]
      · rw [if_neg (fun h => h2 h.2), Pi.single_eq_of_ne h2]
    · rw [Set.indicator_of_notMem h1, zero_smul, if_neg (fun h => h1 h.1)]
  have hsupp : Function.support (fun q : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat =>
      if brandtPred d ℓ c c' q then (1 : R) else 0) ⊆ ↑hfinS.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hq (if_neg h)
  have hs : ∑ q ∈ hfinS.toFinset, (if brandtPred d ℓ c c' q then (1 : R) else 0) =
      ∑ _q ∈ hfinS.toFinset, (1 : R) :=
    Finset.sum_congr rfl fun q hq => if_pos (hfinS.mem_toFinset.1 hq)
  rw [hL, hcard, finsum_eq_sum_of_support_subset _ hsupp, hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_card_finite_toFinset hfinS]
  rfl

end Hecke

/-! ### Pairings and self-adjointness -/

section Pairing

variable {a b : ℤ}

/-- `def:s01-pairing` (`s01-pairing`): `⟨x, y⟩ = ∑_c x_c w_c y_c` for finite `X`. -/
theorem brandtPairing_eq_sum {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R] [Fintype (XB U)]
    (x y : ZX U R) : brandtPairing U R x y = ∑ c, x c * (wx U (Quotient.out c) : R) * y c := by
  rw [brandtPairing_eq_evalPairing_normMap, evalPairing_apply, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [normMap_apply]
  ring

/-- `def:s01-hecke` (`s01-hecke`): `(T_g^t x)(c'') = ∑_c x_c (T_g 1_{c''})(c)` for finite `X`. -/
theorem heckeTHom_apply_eq_sum {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {g : (GL2TF.Quat.BHat a b)ˣ} {R : Type*}
    [CommRing R] {hfin : (U ⊓ conjSub U g).relIndex U ≠ 0} [Fintype (XB U)] (x : ZX U R) (c'' : XB U) :
    heckeTHom U g R hfin x c'' = ∑ c, x c * heckeT U g R hfin (Pi.single c'' (1 : R)) c := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh =>
    rw [map_add, Finsupp.add_apply, hf, hh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.add_apply, add_mul]
  | single c r =>
    rw [heckeTHom_single_apply]
    simp [Finsupp.single_apply, ite_mul]

variable (d : DefiniteData)

/-- `def:s01-classset` (`s01-classset`): `-1 ∈ Ô^×`. -/
theorem negOne_mem_Ohat : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) ∈ d.Ohat := by
  refine (mem_orderCompletionUnits_iff_local d.O.1 _).2 fun p => ?_
  have h1 : ((negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) : GL2TF.Quat.BHat d.a d.b) = -1 := by simp [negOne]
  have hinv : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹ = negOne := by
    rw [inv_eq_iff_mul_eq_one]
    ext
    simp [negOne]
  have h2 : (((negOne : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) :
      GL2TF.Quat.BHat d.a d.b) = -1 := by rw [hinv]; exact h1
  rw [h1, h2, map_neg, map_one]
  exact ⟨neg_mem (one_mem_localLattice _ _), neg_mem (one_mem_localLattice _ _)⟩

/-- `prop:s01-finite` (`s01-finite`): `X_B(Ô^×)` is finite. -/
theorem finite_XB_Ohat : Finite (XB d.Ohat) :=
  XB_finite d le_rfl d.Ohat_isOpen

variable (K : Type*) [Field K]

/-- `rem:s01-dictionary` (`s01-dictionary`): a scalar as a constant of `V_0 = Sym⁰ = K`, the coefficient module of
the import's weight-`2` forms. -/
noncomputable def const0 (r : K) : GL2TF.Quat.symPowerModule K (2 - 2) :=
  ⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ r)⟩

/-- `rem:s01-dictionary` (`s01-dictionary`): the pairing `β_0` of the import on constants is multiplication. -/
theorem symPowerPairing_const0 (r s : K) :
    GL2TF.Quat.symPowerPairing K (2 - 2) (const0 K r) (const0 K s) = r * s := by
  simp [GL2TF.Quat.symPowerPairing, const0, GL2TF.Quat.symExp, MvPolynomial.coeff_C,
    LinearMap.compl₁₂_apply, MvPolynomial.lcoeff_apply]

/-- `rem:s01-dictionary` (`s01-dictionary`): a function on `X_B(Ô^×)` as an import weight-`2` form,
`z ↦ f(B^× z Ô^×) ∈ V_0`. -/
noncomputable def formOf (f : ZXdual d.Ohat K) (z : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    GL2TF.Quat.symPowerModule K (2 - 2) :=
  const0 K (f (DoubleCoset.mk (globalUnits d.a d.b) d.Ohat z))

/-- `def:s01-pairing` (`s01-pairing`): the import's `weightedPairing` for `k = 2` on lifts of functions,
`∑_c |Γ_c|⁻¹ f_c g_c` with `|Γ_c| = 2 w_c` (`-1 ∈ Ô^×`). -/
theorem weightedPairing_formOf (f g : ZXdual d.Ohat K) :
    GL2TF.Quat.weightedPairing d.O.1 2 (formOf d K f) (formOf d K g) =
      ∑ᶠ c : XB d.Ohat, (2 * (wx d.Ohat (Quotient.out c) : K))⁻¹ * (f c * g c) := by
  unfold GL2TF.Quat.weightedPairing
  refine finsum_congr fun c => ?_
  have hc : DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c) = c := DoubleCoset.out_eq' c
  have hw : Nat.card (GL2TF.Quat.classStabilizer (GL2TF.Quat.orderCompletionUnits d.O.1) (Quotient.out c)) =
      2 * wx d.Ohat (Quotient.out c) := (two_mul_wx (negOne_mem_Ohat d) _).symm
  simp only [formOf]
  rw [hc, symPowerPairing_const0, hw]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.cast_mul, Nat.cast_ofNat] ; rfl

/-- `rem:s01-dictionary`, `def:s01-pairing` (`s01-dictionary`, `k = 2`, `U = Ô^×`): our pairing on `K[X]` is twice
the import's `weightedPairing` of the norm images, `⟨x, y⟩ = 2 ⟨ν x, ν y⟩_imp` (factor F-w: `|Γ_c| = 2 w_c`). -/
theorem brandtPairing_eq_import [CharZero K] [Finite (XB d.Ohat)] (x y : ZX d.Ohat K) :
    brandtPairing d.Ohat K x y =
      2 * GL2TF.Quat.weightedPairing d.O.1 2 (formOf d K (normMap d.Ohat K x)) (formOf d K (normMap d.Ohat K y)) := by
  have e1 : brandtPairing d.Ohat K x y = ∑ᶠ c : XB d.Ohat, x c * (wx d.Ohat (Quotient.out c) : K) * y c := by
    rw [brandtPairing_eq_evalPairing_normMap, evalPairing_apply]
    refine finsum_congr fun c => ?_
    rw [normMap_apply]
    ring
  rw [e1, weightedPairing_formOf, mul_finsum]
  refine finsum_congr fun c => ?_
  rw [normMap_apply, normMap_apply]
  by_cases hw0 : (wx d.Ohat (Quotient.out c) : K) = 0
  · rw [hw0]; simp
  · have key : (2 : K) * (2 * (wx d.Ohat (Quotient.out c) : K))⁻¹ * (wx d.Ohat (Quotient.out c) : K) = 1 := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, inv_mul_cancel₀ hw0]
    linear_combination (-((wx d.Ohat (Quotient.out c) : K) * x c * y c)) * key

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) (R : Type*) [CommRing R]
  (hfin : (d.Ohat ⊓ conjSub d.Ohat (elemT d ℓ hℓ)).relIndex d.Ohat ≠ 0)

/-- `prop:s01-adjoint` (`s01-adjoint`), from the import's `brandt_weighted_symmetry`:
`B(ℓ)_{cc'} w_{c'} = w_c B(ℓ)_{c'c}`. -/
theorem brandtMatrix_mul_wx (c c' : XB d.Ohat) :
    (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : R) * (wx d.Ohat (Quotient.out c') : R) =
      (wx d.Ohat (Quotient.out c) : R) * (GL2TF.Quat.brandtMatrix d.O.1 ℓ c' c : R) := by
  have hN : wx d.Ohat (Quotient.out c') * GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' =
      wx d.Ohat (Quotient.out c) * GL2TF.Quat.brandtMatrix d.O.1 ℓ c' c := by
    have h := GL2TF.Quat.brandt_weighted_symmetry d.ha d.hb d.O.1 ℓ (Fact.out : ℓ.Prime).pos c c'
    have e1 : 2 * wx d.Ohat (Quotient.out c) =
        Nat.card (GL2TF.Quat.classStabilizer (GL2TF.Quat.orderCompletionUnits d.O.1) (Quotient.out c)) :=
      two_mul_wx (negOne_mem_Ohat d) _
    have e2 : 2 * wx d.Ohat (Quotient.out c') =
        Nat.card (GL2TF.Quat.classStabilizer (GL2TF.Quat.orderCompletionUnits d.O.1) (Quotient.out c')) :=
      two_mul_wx (negOne_mem_Ohat d) _
    have h2 : 2 * wx d.Ohat (Quotient.out c') * GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' =
        2 * wx d.Ohat (Quotient.out c) * GL2TF.Quat.brandtMatrix d.O.1 ℓ c' c := by
      rw [e1, e2]
      exact h
    rw [mul_assoc, mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have h3 := congrArg (fun n : ℕ => (n : R)) hN
  simp only [Nat.cast_mul] at h3
  rw [mul_comm (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : R)]
  exact h3

/-- `prop:s01-adjoint` (`s01-adjoint`, `U = Ô^×`, `ℓ ∤ D`): `T_ℓ` (on `R[X]`, the transpose `heckeTHom`) is
self-adjoint for the Brandt pairing, `⟨T_ℓ x, y⟩ = ⟨x, T_ℓ y⟩`; from the import's `brandt_weighted_symmetry` through
`Tl_matrix_eq_brandtMatrix`. -/
theorem Tl_selfAdjoint_units [Finite (XB d.Ohat)] (x y : ZX d.Ohat R) :
    brandtPairing d.Ohat R (heckeTHom d.Ohat (elemT d ℓ hℓ) R hfin x) y =
      brandtPairing d.Ohat R x (heckeTHom d.Ohat (elemT d ℓ hℓ) R hfin y) := by
  have : Fintype (XB d.Ohat) := Fintype.ofFinite _
  have hB : ∀ c c' : XB d.Ohat, heckeT d.Ohat (elemT d ℓ hℓ) R hfin (Pi.single c' (1 : R)) c =
      (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : R) := fun c c' => Tl_matrix_eq_brandtMatrix d ℓ hℓ R hfin c c'
  rw [brandtPairing_eq_sum, brandtPairing_eq_sum]
  simp only [heckeTHom_apply_eq_sum, hB, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c'' _ => ?_
  linear_combination (x c * y c'') * brandtMatrix_mul_wx d ℓ R c c''

end Pairing

end Langlandscape.Brandt
