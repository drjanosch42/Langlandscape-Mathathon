/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Cyclicity of `Φ^comb` of a two-vertex graph — S03-L4

For a two-vertex weighted graph `G` (all edges `a → b`, `a ≠ b`) with finitely many edges,
put `c_e = W / w_e = ∏_{e' ≠ e} w_{e'}` and `n = Σ_e c_e`. The homomorphism
`λ(x) = Σ_e c_e x_e` induces `λ̄ : Φ^comb(G) → ℤ/n`. It is defined directly on
`Hom(X, ℤ)` by `φ ↦ Σ_{e ≠ e₀} c_e φ(e − e₀)` (independent of any lift of `φ` to `ℤ^E`).
It is surjective iff `gcd_e c_e = 1`, and bijective when the weights are pairwise coprime
(given `|Φ^comb| = n`, which is `card_phiComb_twoVertex` of S03-L3, passed as `hcard`).

Tex label: `lem:s03-cyclic` (`s03-cyclic`). Status: formalized (modulo `hcard`, from S03-L3).
Never `open Graph` (clash with `_root_.Graph`).
-/

namespace Langlandscape.Graph

open Finsupp

/-- A two-vertex weighted graph: all edges have the same source and the same target, and
source and target differ (`prop:s03-phi`, `s03-cyclic`). -/
structure WGraph.IsTwoVertex (G : WGraph) : Prop where
  /-- all edges have the same source -/
  src_const : ∀ e e' : G.E, G.src e = G.src e'
  /-- all edges have the same target -/
  tgt_const : ∀ e e' : G.E, G.tgt e = G.tgt e'
  /-- source and target differ -/
  src_ne_tgt : ∀ e : G.E, G.src e ≠ G.tgt e

section

variable {G : WGraph} [Fintype G.E] [DecidableEq G.E]

/-- `c_e = W / w_e = ∏_{e' ≠ e} w_{e'}` (`lem:s03-cyclic`). -/
def cycCoeff (G : WGraph) [Fintype G.E] [DecidableEq G.E] (e : G.E) : ℕ :=
  ∏ e' ∈ Finset.univ.erase e, G.w e'

/-- `n = Σ_e W / w_e` (`lem:s03-cyclic`; equals `|Φ^comb|` for two-vertex graphs). -/
def cycMod (G : WGraph) [Fintype G.E] [DecidableEq G.E] : ℕ :=
  ∑ e, cycCoeff G e

/-- `λ(x) = Σ_e (W/w_e) x_e` on `ℤ[E]` (`lem:s03-cyclic`). -/
noncomputable def lambdaMap (G : WGraph) [Fintype G.E] [DecidableEq G.E] :
    (G.E →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun e => (cycCoeff G e : ℤ)

/-- `λ` on a basis vector (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem lambdaMap_single (e : G.E) (a : ℤ) :
    lambdaMap G (Finsupp.single e a) = a * (cycCoeff G e : ℤ) := by
  simp [lambdaMap, Finsupp.linearCombination_single, smul_eq_mul]

/-- `c_e w_e = W` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem cycCoeff_mul_w (e : G.E) : cycCoeff G e * G.w e = ∏ e', G.w e' := by
  unfold cycCoeff
  exact Finset.prod_erase_mul Finset.univ G.w (Finset.mem_univ e)

/-- `c_e w_e = W` over `ℤ` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem cycCoeff_mul_w_int (e : G.E) :
    (cycCoeff G e : ℤ) * (G.w e : ℤ) = ((∏ e', G.w e' : ℕ) : ℤ) := by
  rw [← Nat.cast_mul, cycCoeff_mul_w]

/-- `c_e > 0` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem cycCoeff_pos (e : G.E) : 0 < cycCoeff G e :=
  Finset.prod_pos fun e' _ => G.hw e'

/-- `n > 0` for a nonempty edge set (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem cycMod_pos (e0 : G.E) : 0 < cycMod G :=
  lt_of_lt_of_le (cycCoeff_pos e0)
    (Finset.single_le_sum (f := fun e => cycCoeff G e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e0))

/-- Cast of `n` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem cycMod_cast : (cycMod G : ℤ) = ∑ e, (cycCoeff G e : ℤ) := by
  simp [cycMod]

/-- `d = gcd_e c_e` divides `n` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem gcd_dvd_cycMod : Finset.univ.gcd (cycCoeff G) ∣ cycMod G :=
  Finset.dvd_sum fun e _ => Finset.gcd_dvd (Finset.mem_univ e)

/-- Pairing of `x` with `e − e₀` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem wPairing_sub_single (w : G.E → ℕ) (x : G.E →₀ ℤ) (e e0 : G.E) :
    wPairing w x (Finsupp.single e 1 - Finsupp.single e0 1) =
      (w e : ℤ) * x e - (w e0 : ℤ) * x e0 := by
  have key : ∀ a : G.E, wPairing w x (Finsupp.single a 1) = (w a : ℤ) * x a := by
    intro a
    conv_lhs => rw [← Finsupp.univ_sum_single x]
    rw [map_sum, LinearMap.sum_apply]
    simp only [wPairing_single]
    rw [Finset.sum_eq_single a]
    · simp only [Finsupp.single_eq_same, mul_one]
      ring
    · intro i _ hi
      simp [Finsupp.single_apply, Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [map_sub, key, key]

variable (h : G.IsTwoVertex) (e0 : G.E)

include h e0 in
/-- Degree zero: for `x ∈ X(G)` of a two-vertex graph, `Σ_e x_e = 0`
(`lem:s03-cyclic`, `s03-cyclic`). -/
theorem X_sum_eq_zero (x : G.X) : ∑ e, x.1 e = 0 := by
  classical
  have ht : ∀ e, G.tgt e = G.tgt e0 := fun e => h.tgt_const e e0
  have hne : ∀ e, G.src e ≠ G.tgt e0 := fun e => by
    rw [h.src_const e e0]; exact h.src_ne_tgt e0
  have hb : WGraph.boundary G ℤ x.1 = 0 := x.2
  have hterm : ∀ i, (WGraph.boundary G ℤ (Finsupp.single i (x.1 i))) (G.tgt e0) = x.1 i := by
    intro i
    rw [WGraph.boundary_single, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_pos (ht i), if_neg (hne i), sub_zero]
  have h2 := congrArg (fun f => f (G.tgt e0)) hb
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [← Finsupp.univ_sum_single x.1, map_sum, Finsupp.finset_sum_apply] at h2
  simpa only [hterm] using h2

/-- The basis vector `e − e₀` of `X(G)` (`lem:s03-cyclic`). -/
noncomputable def bX (e : G.E) : G.X :=
  ⟨Finsupp.single e 1 - Finsupp.single e0 1, by
    show WGraph.boundary G ℤ (Finsupp.single e 1 - Finsupp.single e0 1) = 0
    rw [map_sub, WGraph.boundary_single, WGraph.boundary_single, h.src_const e e0,
      h.tgt_const e e0]
    exact sub_self _⟩

/-- Coordinates of `bX` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem bX_val (e : G.E) : (bX h e0 e).1 = Finsupp.single e 1 - Finsupp.single e0 1 := rfl

/-- `λ` on `Hom(X, ℤ)`: `φ ↦ Σ_{e ≠ e₀} c_e φ(e − e₀)` mod `n` (`lem:s03-cyclic`). -/
noncomputable def lambdaDual : Module.Dual ℤ G.X →ₗ[ℤ] ZMod (cycMod G) where
  toFun φ := ∑ e ∈ Finset.univ.erase e0, (((cycCoeff G e : ℤ) * φ (bX h e0 e) : ℤ) : ZMod (cycMod G))
  map_add' φ ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [LinearMap.add_apply, mul_add, Int.cast_add]
  map_smul' r φ := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
    push_cast
    ring

/-- Unfolding `lambdaDual` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem lambdaDual_apply (φ : Module.Dual ℤ G.X) :
    lambdaDual h e0 φ =
      ((∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) * φ (bX h e0 e) : ℤ) :
        ZMod (cycMod G)) := by
  show (∑ e ∈ Finset.univ.erase e0, (((cycCoeff G e : ℤ) * φ (bX h e0 e) : ℤ) : ZMod (cycMod G))) = _
  rw [Int.cast_sum]

/-- `λ` kills the image of `X → X^∨` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem lambdaDual_wDualMap (x : G.X) :
    lambdaDual h e0 (wDualMap G.w G.X x) = 0 := by
  rw [lambdaDual_apply]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hv : ∀ e, wDualMap G.w G.X x (bX h e0 e) = (G.w e : ℤ) * x.1 e - (G.w e0 : ℤ) * x.1 e0 :=
    fun e => wPairing_sub_single G.w x.1 e e0
  simp only [hv]
  have h1 : ∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) *
        ((G.w e : ℤ) * x.1 e - (G.w e0 : ℤ) * x.1 e0) =
      ((∏ e', G.w e' : ℕ) : ℤ) * (∑ e ∈ Finset.univ.erase e0, x.1 e) -
        (G.w e0 : ℤ) * x.1 e0 * (∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := cycCoeff_mul_w_int (G := G) e
    linear_combination (x.1 e) * this
  have hS : ∑ e ∈ Finset.univ.erase e0, x.1 e = - x.1 e0 := by
    have := Finset.add_sum_erase Finset.univ (fun e => x.1 e) (Finset.mem_univ e0)
    have h0 := X_sum_eq_zero h e0 x
    linear_combination this + h0
  have hC : ∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) =
      (cycMod G : ℤ) - (cycCoeff G e0 : ℤ) := by
    have := Finset.add_sum_erase Finset.univ (fun e => (cycCoeff G e : ℤ)) (Finset.mem_univ e0)
    rw [cycMod_cast]
    linear_combination this
  refine ⟨-((G.w e0 : ℤ) * x.1 e0), ?_⟩
  rw [h1, hS, hC]
  have := cycCoeff_mul_w_int (G := G) e0
  linear_combination (x.1 e0) * this

/-- `λ̄ : Φ^comb(G) → ℤ/n` (`lem:s03-cyclic`). -/
noncomputable def lambdaBar : G.PhiComb →ₗ[ℤ] ZMod (cycMod G) :=
  Submodule.liftQ _ (lambdaDual h e0) (by
    rintro _ ⟨x, rfl⟩
    exact lambdaDual_wDualMap h e0 x)

/-- `λ̄` on representatives (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem lambdaBar_mk (φ : Module.Dual ℤ G.X) :
    lambdaBar h e0 (Submodule.Quotient.mk φ) = lambdaDual h e0 φ := rfl

/-- Dual elements with prescribed values on `e − e₀` (`lem:s03-cyclic`, `s03-cyclic`). -/
noncomputable def dualOfCoeffs (a : G.E → ℤ) : Module.Dual ℤ G.X where
  toFun x := ∑ e ∈ Finset.univ.erase e0, a e * x.1 e
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Submodule.coe_add, Finsupp.add_apply, mul_add]
  map_smul' r x := by
    rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Submodule.coe_smul, Finsupp.smul_apply, smul_eq_mul]
    ring

/-- Values of `dualOfCoeffs` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem dualOfCoeffs_bX (a : G.E → ℤ) (e : G.E) (he : e ≠ e0) :
    dualOfCoeffs e0 a (bX h e0 e) = a e := by
  show ∑ e' ∈ Finset.univ.erase e0, a e' * ((Finsupp.single e 1 - Finsupp.single e0 1 : G.E →₀ ℤ) e') = a e
  rw [Finset.sum_eq_single e]
  · simp [Finsupp.single_apply, he.symm]
  · intro e' he' hne
    have h0 : e' ≠ e0 := Finset.ne_of_mem_erase he'
    simp [Finsupp.single_apply, hne, Ne.symm h0]
  · intro hn
    exact absurd (Finset.mem_erase.mpr ⟨he, Finset.mem_univ e⟩) hn

/-- `lem:s03-cyclic`: `λ̄` is surjective iff `gcd_e (W/w_e) = 1` (`s03-cyclic`). -/
theorem lambdaBar_surjective_iff :
    Function.Surjective (lambdaBar h e0) ↔ Finset.univ.gcd (cycCoeff G) = 1 := by
  have hsurj : Function.Surjective (lambdaBar h e0) ↔ Function.Surjective (lambdaDual h e0) := by
    constructor
    · intro hs k
      obtain ⟨q, hq⟩ := hs k
      obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨φ, hq⟩
    · intro hs k
      obtain ⟨φ, hφ⟩ := hs k
      exact ⟨Submodule.Quotient.mk φ, hφ⟩
  rw [hsurj]
  constructor
  · intro hs
    obtain ⟨φ, hφ⟩ := hs 1
    rw [lambdaDual_apply] at hφ
    set d := Finset.univ.gcd (cycCoeff G) with hd
    set m : ℤ := ∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) * φ (bX h e0 e) with hm
    have hdm : (d : ℤ) ∣ m :=
      Finset.dvd_sum fun e _ =>
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Finset.gcd_dvd (Finset.mem_univ e))) _
    have hdn : (d : ℤ) ∣ (cycMod G : ℤ) := Int.natCast_dvd_natCast.mpr gcd_dvd_cycMod
    have h1 : ((1 : ℤ) : ZMod (cycMod G)) = (m : ZMod (cycMod G)) := by
      rw [Int.cast_one]; exact hφ.symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 : (d : ℤ) ∣ m - 1 := dvd_trans hdn h1
    have h3 : (d : ℤ) ∣ 1 := by
      have := dvd_sub hdm h2
      simpa using this
    have h4 : (d : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg d) h3
    exact_mod_cast h4
  · intro hg k
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    set gz := Finset.univ.gcd (fun e => ((cycCoeff G e : ℕ) : ℤ)) with hgz
    obtain ⟨g, hg1⟩ := Finset.gcd_eq_sum_mul (R := ℤ) Finset.univ (fun e => ((cycCoeff G e : ℕ) : ℤ))
    have hnat : gz.natAbs = 1 := by
      have hdv : gz.natAbs ∣ Finset.univ.gcd (cycCoeff G) := by
        apply Finset.dvd_gcd
        intro e _
        have := Int.natAbs_dvd_natAbs.mpr (Finset.gcd_dvd (f := fun e => ((cycCoeff G e : ℕ) : ℤ))
          (Finset.mem_univ e))
        simpa using this
      rw [hg] at hdv
      exact Nat.dvd_one.mp hdv
    have hs1 : ∃ s : G.E → ℤ, ∑ e, (cycCoeff G e : ℤ) * s e = 1 := by
      rcases Int.natAbs_eq gz with h' | h' <;> rw [hnat] at h'
      · exact ⟨g, by rw [← hg1]; simpa using h'⟩
      · refine ⟨fun e => - g e, ?_⟩
        have : ∑ e, (cycCoeff G e : ℤ) * - g e = - (∑ e, (cycCoeff G e : ℤ) * g e) := by
          simp [mul_neg, Finset.sum_neg_distrib]
        rw [this, ← hg1, ← hgz, h']
        norm_num
    obtain ⟨s, hs⟩ := hs1
    refine ⟨dualOfCoeffs e0 (fun e => m * (s e - s e0)), ?_⟩
    rw [lambdaDual_apply]
    have hv : ∀ e ∈ Finset.univ.erase e0,
        (cycCoeff G e : ℤ) * dualOfCoeffs e0 (fun e => m * (s e - s e0)) (bX h e0 e) =
          (cycCoeff G e : ℤ) * (m * (s e - s e0)) := by
      intro e he
      rw [dualOfCoeffs_bX h e0 _ e (Finset.ne_of_mem_erase he)]
    rw [Finset.sum_congr rfl hv]
    have e1 : ∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) * (m * (s e - s e0)) =
        m * (∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) * s e) -
          m * s e0 * (∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    have hA := Finset.add_sum_erase Finset.univ (fun e => (cycCoeff G e : ℤ) * s e)
      (Finset.mem_univ e0)
    have hC := Finset.add_sum_erase Finset.univ (fun e => (cycCoeff G e : ℤ)) (Finset.mem_univ e0)
    rw [hs] at hA
    rw [← cycMod_cast] at hC
    have e2 : ∑ e ∈ Finset.univ.erase e0, (cycCoeff G e : ℤ) * (m * (s e - s e0)) =
        m + (cycMod G : ℤ) * (-(m * s e0)) := by
      rw [e1]
      linear_combination m * hA - (m * s e0) * hC
    rw [e2]
    push_cast
    simp [ZMod.natCast_self]

/-- Pairwise coprime weights give `gcd_e (W/w_e) = 1` (`lem:s03-cyclic`, `s03-cyclic`). -/
theorem gcd_cycCoeff_eq_one_of_pairwise_coprime
    (hcop : Pairwise fun e e' : G.E => Nat.Coprime (G.w e) (G.w e')) (e0 : G.E) :
    Finset.univ.gcd (cycCoeff G) = 1 := by
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hrc : ∀ e, r ∣ cycCoeff G e := fun e =>
    dvd_trans hrd (Finset.gcd_dvd (Finset.mem_univ e))
  have hW : r ∣ ∏ e', G.w e' := by
    rw [← cycCoeff_mul_w e0]
    exact Dvd.dvd.mul_right (hrc e0) _
  obtain ⟨e1, _, h1⟩ := (Prime.dvd_finsetProd_iff hr.prime G.w).mp hW
  have h2 : r ∣ ∏ e' ∈ Finset.univ.erase e1, G.w e' := hrc e1
  obtain ⟨e2, he2, h2'⟩ := (Prime.dvd_finsetProd_iff hr.prime G.w).mp h2
  have hne12 : e2 ≠ e1 := Finset.ne_of_mem_erase he2
  have := Nat.dvd_gcd h2' h1
  rw [Nat.Coprime.gcd_eq_one (hcop hne12)] at this
  exact hr.one_lt.ne' (Nat.dvd_one.mp this)

/-- `lem:s03-cyclic`: if `gcd_e (W/w_e) = 1` and `|Φ^comb| = n` (S03-L3's
`card_phiComb_twoVertex`), then `λ̄` is bijective (`s03-cyclic`). -/
theorem lambdaBar_bijective_of_gcd_eq_one (hg : Finset.univ.gcd (cycCoeff G) = 1)
    (hcard : Nat.card G.PhiComb = cycMod G) :
    Function.Bijective (lambdaBar h e0) := by
  have hsurj : Function.Surjective (lambdaBar h e0) :=
    (lambdaBar_surjective_iff h e0).mpr hg
  have : NeZero (cycMod G) := ⟨(cycMod_pos e0).ne'⟩
  have : Finite G.PhiComb := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (cycMod_pos e0).ne')
  refine Function.Surjective.bijective_of_nat_card_le (f := lambdaBar h e0) hsurj ?_
  rw [hcard, Nat.card_zmod]

/-- `lem:s03-cyclic`: for pairwise coprime weights (any number of `1`'s), `λ̄` is an
isomorphism `Φ^comb(G) ≃ ℤ/n`, given `|Φ^comb| = n` (S03-L3) (`s03-cyclic`). -/
theorem lambdaBar_bijective_of_pairwise_coprime
    (hcop : Pairwise fun e e' : G.E => Nat.Coprime (G.w e) (G.w e'))
    (hcard : Nat.card G.PhiComb = cycMod G) :
    Function.Bijective (lambdaBar h e0) :=
  lambdaBar_bijective_of_gcd_eq_one h e0 (gcd_cycCoeff_eq_one_of_pairwise_coprime hcop e0) hcard

end

end Langlandscape.Graph
