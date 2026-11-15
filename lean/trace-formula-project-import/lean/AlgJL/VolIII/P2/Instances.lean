import AlgJL.Meta.Tag
import AlgJL.VolIII.P2.Ramification
import AlgJL.VolIII.P2.Orders
import AlgJL.VolIII.P2.ClassSet
import AlgJL.VolIII.P2.MassDefs
import AlgJL.Hyp.EichlerMass
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.Prime
import Mathlib.LinearAlgebra.Matrix.Notation
import AlgJL.VolIII.P2.Mass

/-!
# Instances: the Hurwitz order, Pizer's orders, the closed instances of `Hyp.EichlerMass` (Q2 U7, items 61–64)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §7 (items 61–64 of `docs/sprints/Q2-plan.md` §1.2). W1: the orders
are fully defined; W3 (L4T): items 61–63 are proved from the upstream items (plan traps 8–9; certificates
`docs/notes/Q2-titan/q2_instances.json`, §4 below), item 64 (stretch) is open.

* `hurwitzOrder`: `O_H = ℤ(1+i+j+k)/2 + ℤi + ℤj + ℤk ⊆ (−1, −1)_ℚ`.
* `pizerOrderI b`: `ℤ(1+j)/2 + ℤ(i+k)/2 + ℤj + ℤk ⊆ (−1, b)_ℚ` for `b ≡ 1 (mod 4)` (Pizer's order for `b = −p`,
  `p ≡ 3 (mod 4)`; `O₁₁ = pizerOrderI (−11)`).
* `pizerOrderII b`: `ℤ(1+j+k)/2 + ℤ(i+2j+k)/4 + ℤj + ℤk ⊆ (−2, b)_ℚ` for `b ≡ 3 (mod 8)` (Pizer's order for `b = −p`,
  `p ≡ 5 (mod 8)`).
Each order is the ℤ-span of an explicit basis; closure under multiplication comes from its integral multiplication
table (proved by computation), and `1, i, j, k` lie in the span. The Hyp clauses quantify over the maximality proof
(`∀ h : IsMaximalOrder O, Hyp.EichlerMass a b D ⟨O, h⟩`), so the statements do not depend on their own proof; the
registry instances `GL2TFTests.eichlerMass_d2`, `GL2TFTests.eichlerMass_d11` are derived in `GL2TFTests`.
Owner: L3T (statements, W1); L4T (proofs, W3).
-/

set_option autoImplicit false

open scoped Quaternion

namespace GL2TF.Quat

open GL2TF

/-! ## §1 Orders from a basis with an integral multiplication table -/

/-- Proof helper: the ℤ-span of `v₀, …, v₃` is closed under multiplication if the structure constants are integral. -/
theorem mul_mem_span_of_table {A : Type*} [Ring A] [Algebra ℚ A] (v : Fin 4 → A) (T : Fin 4 → Fin 4 → Fin 4 → ℤ)
    (hT : ∀ i j, v i * v j = ∑ k, (T i j k : ℚ) • v k) {x y : A}
    (hx : x ∈ Submodule.span ℤ (Set.range v)) (hy : y ∈ Submodule.span ℤ (Set.range v)) :
    x * y ∈ Submodule.span ℤ (Set.range v) := by
  have hle : Submodule.span ℤ (Set.range v) * Submodule.span ℤ (Set.range v) ≤
      Submodule.span ℤ (Set.range v) := by
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show v i * v j ∈ _
    rw [hT]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact hle (Submodule.mul_mem_mul hx hy)

/-- Proof helper: a ℤ-combination of the `v k` lies in their span. -/
theorem sum_smul_mem_span {A : Type*} [AddCommGroup A] [Module ℚ A] (v : Fin 4 → A) (c : Fin 4 → ℤ) :
    ∑ k, (c k : ℚ) • v k ∈ Submodule.span ℤ (Set.range v) :=
  Submodule.sum_mem _ fun k _ => by
    rw [Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Proof helper: if `1, i, j, k` lie in a set `S ⊆ B`, then `ℚ S = B`. -/
theorem span_rat_eq_top_of_basis_mem {a b : ℤ} (S : Set (QuatAlg ℚ a b))
    (h1 : (⟨1, 0, 0, 0⟩ : QuatAlg ℚ a b) ∈ S) (hi : (⟨0, 1, 0, 0⟩ : QuatAlg ℚ a b) ∈ S)
    (hj : (⟨0, 0, 1, 0⟩ : QuatAlg ℚ a b) ∈ S) (hk : (⟨0, 0, 0, 1⟩ : QuatAlg ℚ a b) ∈ S) :
    Submodule.span ℚ S = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = x.re • (⟨1, 0, 0, 0⟩ : QuatAlg ℚ a b) + x.imI • ⟨0, 1, 0, 0⟩ +
      x.imJ • ⟨0, 0, 1, 0⟩ + x.imK • ⟨0, 0, 0, 1⟩ := by
    ext <;> simp
  rw [hx]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span h1)) (Submodule.smul_mem _ _ (Submodule.subset_span hi)))
    (Submodule.smul_mem _ _ (Submodule.subset_span hj))) (Submodule.smul_mem _ _ (Submodule.subset_span hk))

/-- Proof helper: the ℤ-span of a basis with an integral multiplication table and with `1, i, j, k` in its span
contains `1`, is closed under multiplication and spans `B` over `ℚ`. -/
theorem orderOfTable_aux {a b : ℤ} (v : Fin 4 → QuatAlg ℚ a b) (T : Fin 4 → Fin 4 → Fin 4 → ℤ)
    (hT : ∀ i j, v i * v j = ∑ k, (T i j k : ℚ) • v k) (c1 ci cj ck : Fin 4 → ℤ)
    (h1 : (⟨1, 0, 0, 0⟩ : QuatAlg ℚ a b) = ∑ k, (c1 k : ℚ) • v k)
    (hi : (⟨0, 1, 0, 0⟩ : QuatAlg ℚ a b) = ∑ k, (ci k : ℚ) • v k)
    (hj : (⟨0, 0, 1, 0⟩ : QuatAlg ℚ a b) = ∑ k, (cj k : ℚ) • v k)
    (hk : (⟨0, 0, 0, 1⟩ : QuatAlg ℚ a b) = ∑ k, (ck k : ℚ) • v k) :
    (1 : QuatAlg ℚ a b) ∈ Submodule.span ℤ (Set.range v) ∧
    (∀ x y, x ∈ Submodule.span ℤ (Set.range v) → y ∈ Submodule.span ℤ (Set.range v) →
      x * y ∈ Submodule.span ℤ (Set.range v)) ∧
    Submodule.span ℚ (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ a b)) = ⊤ := by
  refine ⟨?_, fun x y hx hy => mul_mem_span_of_table v T hT hx hy, ?_⟩
  · have : (1 : QuatAlg ℚ a b) = ⟨1, 0, 0, 0⟩ := rfl
    rw [this, h1]; exact sum_smul_mem_span v c1
  · refine span_rat_eq_top_of_basis_mem _ ?_ ?_ ?_ ?_
    · rw [h1]; exact sum_smul_mem_span v c1
    · rw [hi]; exact sum_smul_mem_span v ci
    · rw [hj]; exact sum_smul_mem_span v cj
    · rw [hk]; exact sum_smul_mem_span v ck

/-! ## §2 The Hurwitz order -/

/-- Proof helper: the multiplication table of the Hurwitz basis `(1+i+j+k)/2, i, j, k`. -/
theorem hurwitz_table (i j : Fin 4) :
    (![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → QuatAlg ℚ (-1) (-1)) i *
      (![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → QuatAlg ℚ (-1) (-1)) j =
    ∑ k, (((![
      ![![-1, 1, 1, 1], ![-1, 1, 1, 0], ![-1, 0, 1, 1], ![-1, 1, 0, 1]],
      ![![-1, 1, 0, 1], ![-2, 1, 1, 1], ![0, 0, 0, 1], ![0, 0, -1, 0]],
      ![![-1, 1, 1, 0], ![0, 0, 0, -1], ![-2, 1, 1, 1], ![0, 1, 0, 0]],
      ![![-1, 0, 1, 1], ![0, 0, 1, 0], ![0, -1, 0, 0], ![-2, 1, 1, 1]]] : Fin 4 → Fin 4 → Fin 4 → ℤ) i j k : ℤ) : ℚ) •
      (![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → QuatAlg ℚ (-1) (-1)) k := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_four, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk,
      QuaternionAlgebra.mk_mul_mk]

/-- Proof helper: the Hurwitz span is an order. -/
theorem hurwitz_aux :
    let v : Fin 4 → QuatAlg ℚ (-1) (-1) := ![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]
    (1 : QuatAlg ℚ (-1) (-1)) ∈ Submodule.span ℤ (Set.range v) ∧
    (∀ x y, x ∈ Submodule.span ℤ (Set.range v) → y ∈ Submodule.span ℤ (Set.range v) →
      x * y ∈ Submodule.span ℤ (Set.range v)) ∧
    Submodule.span ℚ (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ (-1) (-1))) = ⊤ := by
  intro v
  refine orderOfTable_aux v _ hurwitz_table ![2, -1, -1, -1] ![0, 1, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1]
    ?_ ?_ ?_ ?_ <;>
    norm_num [v, Fin.sum_univ_four, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk]

/-- The Hurwitz order `O_H = ℤ(1+i+j+k)/2 + ℤi + ℤj + ℤk` of `B = (−1, −1)_ℚ`. -/
@[tf_aux "III.qcls.def:hurwitz-order"]
noncomputable def hurwitzOrder : QOrder (-1) (-1) where
  toSubalgebra := (Submodule.span ℤ (Set.range
    (![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → QuatAlg ℚ (-1) (-1)))).toSubalgebra
    hurwitz_aux.1 hurwitz_aux.2.1
  fg := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := hurwitz_aux.2.2

/-! ## §3 Pizer's orders -/

/-- Proof helper: the multiplication table of `(1+j)/2, (i+k)/2, j, k` in `(−1, 4q+1)_ℚ`. -/
theorem pizerI_table (q : ℤ) (i j : Fin 4) :
    (![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-1) (4 * q + 1)) i *
      (![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-1) (4 * q + 1)) j =
    ∑ k, (((![
      ![![1 + 2 * q, 0, -q, 0], ![0, -2 * q, 0, q], ![1 + 4 * q, 0, -2 * q, 0], ![0, -1 - 4 * q, 0, 1 + 2 * q]],
      ![![0, 1 + 2 * q, 0, -q], ![2 * q, 0, -q, 0], ![0, 1 + 4 * q, 0, -2 * q], ![1 + 4 * q, 0, -1 - 2 * q, 0]],
      ![![1 + 4 * q, 0, -2 * q, 0], ![0, -1 - 4 * q, 0, 2 * q], ![2 + 8 * q, 0, -1 - 4 * q, 0],
        ![0, -2 - 8 * q, 0, 1 + 4 * q]],
      ![![0, 1 + 4 * q, 0, -2 * q], ![1 + 4 * q, 0, -2 * q, 0], ![0, 2 + 8 * q, 0, -1 - 4 * q],
        ![2 + 8 * q, 0, -1 - 4 * q, 0]]] : Fin 4 → Fin 4 → Fin 4 → ℤ) i j k : ℤ) : ℚ) •
      (![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-1) (4 * q + 1)) k := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.mk.injEq] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

/-- Proof helper: for `b ≡ 1 (mod 4)` the span of `(1+j)/2, (i+k)/2, j, k` in `(−1, b)_ℚ` is an order. -/
theorem pizerI_aux (b : ℤ) (hb : b % 4 = 1) :
    let v : Fin 4 → QuatAlg ℚ (-1) b := ![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]
    (1 : QuatAlg ℚ (-1) b) ∈ Submodule.span ℤ (Set.range v) ∧
    (∀ x y, x ∈ Submodule.span ℤ (Set.range v) → y ∈ Submodule.span ℤ (Set.range v) →
      x * y ∈ Submodule.span ℤ (Set.range v)) ∧
    Submodule.span ℚ (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ (-1) b)) = ⊤ := by
  intro v
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, b = 4 * q + 1 := ⟨b / 4, by omega⟩
  refine orderOfTable_aux v _ (pizerI_table q) ![2, 0, -1, 0] ![0, 2, 0, -1] ![0, 0, 1, 0] ![0, 0, 0, 1]
    ?_ ?_ ?_ ?_ <;>
    norm_num [v, Fin.sum_univ_four, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk]

/-- Pizer's order `ℤ(1+j)/2 + ℤ(i+k)/2 + ℤj + ℤk` of `(−1, b)_ℚ` for `b ≡ 1 (mod 4)` (for `b = −p`, `p ≡ 3 (mod 4)`
prime, Pizer's maximal order; `O₁₁ = pizerOrderI (−11) _`). -/
@[tf_aux "III.qcls.def:pizer-order-minus-one"]
noncomputable def pizerOrderI (b : ℤ) (hb : b % 4 = 1) : QOrder (-1) b where
  toSubalgebra := (Submodule.span ℤ (Set.range
    (![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → QuatAlg ℚ (-1) b))).toSubalgebra
    (pizerI_aux b hb).1 (pizerI_aux b hb).2.1
  fg := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := (pizerI_aux b hb).2.2

set_option maxHeartbeats 1000000 in
/-- Proof helper: the multiplication table of `(1+j+k)/2, (i+2j+k)/4, j, k` in `(−2, 8q+3)_ℚ`. -/
theorem pizerII_table (q : ℤ) (i j : Fin 4) :
    (![⟨1 / 2, 0, 1 / 2, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-2) (8 * q + 3)) i *
      (![⟨1 / 2, 0, 1 / 2, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-2) (8 * q + 3)) j =
    ∑ k, (((![
      ![![5 + 12 * q, 0, -2 - 6 * q, -2 - 6 * q], ![3 + 8 * q, 2 + 4 * q, -2 - 6 * q, -2 - 5 * q],
        ![3 + 8 * q, 6 + 16 * q, -4 - 12 * q, -3 - 8 * q], ![6 + 16 * q, -6 - 16 * q, 0, -1 - 4 * q]],
      ![![3 + 8 * q, -1 - 4 * q, -1 - 2 * q, -1 - 3 * q], ![2 + 6 * q, 0, -1 - 3 * q, -1 - 3 * q],
        ![3 + 8 * q, 3 + 8 * q, -3 - 8 * q, -2 - 6 * q], ![3 + 8 * q, -6 - 16 * q, 1 + 4 * q, 0]],
      ![![3 + 8 * q, -6 - 16 * q, 2 + 4 * q, 0], ![3 + 8 * q, -3 - 8 * q, 0, -1 - 2 * q],
        ![6 + 16 * q, 0, -3 - 8 * q, -3 - 8 * q], ![0, -12 - 32 * q, 6 + 16 * q, 3 + 8 * q]],
      ![![6 + 16 * q, 6 + 16 * q, -6 - 16 * q, -4 - 12 * q], ![3 + 8 * q, 6 + 16 * q, -4 - 12 * q, -3 - 8 * q],
        ![0, 12 + 32 * q, -6 - 16 * q, -3 - 8 * q], ![12 + 32 * q, 0, -6 - 16 * q, -6 - 16 * q]]] :
        Fin 4 → Fin 4 → Fin 4 → ℤ) i j k : ℤ) : ℚ) •
      (![⟨1 / 2, 0, 1 / 2, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
        Fin 4 → QuatAlg ℚ (-2) (8 * q + 3)) k := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.mk.injEq] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

/-- Proof helper: for `b ≡ 3 (mod 8)` the span of `(1+j+k)/2, (i+2j+k)/4, j, k` in `(−2, b)_ℚ` is an order. -/
theorem pizerII_aux (b : ℤ) (hb : b % 8 = 3) :
    let v : Fin 4 → QuatAlg ℚ (-2) b :=
      ![⟨1 / 2, 0, 1 / 2, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]
    (1 : QuatAlg ℚ (-2) b) ∈ Submodule.span ℤ (Set.range v) ∧
    (∀ x y, x ∈ Submodule.span ℤ (Set.range v) → y ∈ Submodule.span ℤ (Set.range v) →
      x * y ∈ Submodule.span ℤ (Set.range v)) ∧
    Submodule.span ℚ (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ (-2) b)) = ⊤ := by
  intro v
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, b = 8 * q + 3 := ⟨b / 8, by omega⟩
  refine orderOfTable_aux v _ (pizerII_table q) ![2, 0, -1, -1] ![0, 4, -2, -1] ![0, 0, 1, 0] ![0, 0, 0, 1]
    ?_ ?_ ?_ ?_ <;>
    norm_num [v, Fin.sum_univ_four, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk]

/-- Pizer's order `ℤ(1+j+k)/2 + ℤ(i+2j+k)/4 + ℤj + ℤk` of `(−2, b)_ℚ` for `b ≡ 3 (mod 8)` (for `b = −p`,
`p ≡ 5 (mod 8)` prime, Pizer's maximal order). -/
@[tf_aux "III.qcls.def:pizer-order-minus-two"]
noncomputable def pizerOrderII (b : ℤ) (hb : b % 8 = 3) : QOrder (-2) b where
  toSubalgebra := (Submodule.span ℤ (Set.range
    (![⟨1 / 2, 0, 1 / 2, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] :
      Fin 4 → QuatAlg ℚ (-2) b))).toSubalgebra
    (pizerII_aux b hb).1 (pizerII_aux b hb).2.1
  fg := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := (pizerII_aux b hb).2.2

end GL2TF.Quat

/-! ## §4 Proof infrastructure for the instances (W3, L4T; certificates `docs/notes/Q2-titan/q2_instances.json`) -/

namespace GL2TF.Quat.Inst

theorem mem_span4 {a b : ℤ} (v : Fin 4 → QuatAlg ℚ a b) (x : QuatAlg ℚ a b) :
    x ∈ Submodule.span ℤ (Set.range v) ↔ ∃ c : Fin 4 → ℤ, x = ∑ k, (c k : ℚ) • v k := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [Int.cast_smul_eq_zsmul ℚ]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem linIndep_of_sum {a b : ℤ} (v : Fin 4 → QuatAlg ℚ a b)
    (h : ∀ c : Fin 4 → ℤ, ∑ k, (c k : ℚ) • v k = 0 → ∀ k, c k = 0) : LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine h g ?_
  simpa only [Int.cast_smul_eq_zsmul ℚ] using hg

/-- The Hurwitz basis. -/
abbrev vH : Fin 4 → QuatAlg ℚ (-1) (-1) := ![⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem sum_vH (c : Fin 4 → ℚ) : ∑ k, c k • vH k = ⟨c 0 / 2, c 0 / 2 + c 1, c 0 / 2 + c 2, c 0 / 2 + c 3⟩ := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, QuaternionAlgebra.smul_mk,
    QuaternionAlgebra.mk_add_mk, smul_eq_mul, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem mem_hurwitz {x : QuatAlg ℚ (-1) (-1)} : x ∈ hurwitzOrder.toSubalgebra ↔
    ∃ c : Fin 4 → ℤ, x = ⟨c 0 / 2, c 0 / 2 + c 1, c 0 / 2 + c 2, c 0 / 2 + c 3⟩ := by
  show x ∈ Submodule.span ℤ _ ↔ _
  rw [mem_span4]
  exact exists_congr fun c => by rw [sum_vH fun k => (c k : ℚ)]

theorem linIndep_vH : LinearIndependent ℤ vH := by
  refine linIndep_of_sum _ fun c hc => ?_
  rw [sum_vH fun k => (c k : ℚ)] at hc
  simp only [QuaternionAlgebra.ext_iff] at hc
  obtain ⟨h0, h1, h2, h3⟩ := hc
  simp only [QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero, QuaternionAlgebra.imJ_zero,
    QuaternionAlgebra.imK_zero] at h0 h1 h2 h3
  have e0 : (c 0 : ℚ) = 0 := by linarith
  have e1 : (c 1 : ℚ) = 0 := by linarith
  have e2 : (c 2 : ℚ) = 0 := by linarith
  have e3 : (c 3 : ℚ) = 0 := by linarith
  intro k; fin_cases k <;> simp_all

noncomputable def basisH : Module.Basis (Fin 4) ℤ (Subalgebra.toSubmodule hurwitzOrder.toSubalgebra) :=
  Module.Basis.span linIndep_vH

theorem basisH_apply (k : Fin 4) : (basisH k : QuatAlg ℚ (-1) (-1)) = vH k := by
  show ((Module.Basis.span linIndep_vH k : Submodule.span ℤ (Set.range vH)) : QuatAlg ℚ (-1) (-1)) = vH k
  rw [Module.Basis.span_apply]

theorem discriminant_hurwitz : discriminant hurwitzOrder = 4 := by
  rw [(discriminant_basic hurwitzOrder).1 basisH]
  simp only [basisH_apply]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, trd, Fin.succAbove]
  norm_num

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem int_dvd_of_zmod {n : ℕ} {z : ℤ} (h : (z : ZMod n) = 0) : (n : ℤ) ∣ z :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp h

theorem zmod4_sumsq : ∀ t c₁ c₂ c₃ : ZMod 4,
    t ^ 2 + (t + c₁) ^ 2 + (t + c₂) ^ 2 + (t + c₃) ^ 2 = 0 → 2 * c₁ = 0 ∧ 2 * c₂ = 0 ∧ 2 * c₃ = 0 := by
  decide

theorem prime_eq_of_sq_dvd {p : ℕ} (hp : p.Prime) {d : ℕ} (hd : d.Prime) {n : ℤ}
    (h : ((d : ℚ) ^ 2) = (p : ℚ) ^ 2 * n) : p = d := by
  have h1 : ((d : ℤ) ^ 2) = (p : ℤ) ^ 2 * n := by exact_mod_cast h
  have h2 : (p : ℤ) ∣ (d : ℤ) ^ 2 := ⟨p * n, by rw [h1]; ring⟩
  have h3 : p ∣ d ^ 2 := by exact_mod_cast h2
  have h4 : p ∣ d := hp.dvd_of_dvd_pow h3
  exact (Nat.prime_dvd_prime_iff_eq hp hd).mp h4

theorem isMaximal_hurwitz : IsMaximalOrder hurwitzOrder := by
  refine isMaximalOrder_of_criterion _ fun p hp ⟨n, hn⟩ x hpx hx ⟨⟨t, ht⟩, ⟨m, hm⟩⟩ => hx ?_
  rw [discriminant_hurwitz, show (4 : ℚ) = ((2 : ℕ) : ℚ) ^ 2 by norm_num] at hn
  obtain rfl := prime_eq_of_sq_dvd hp Nat.prime_two hn
  rw [mem_hurwitz] at hpx ⊢
  obtain ⟨c, hc⟩ := hpx
  have e0 : ((2 : ℕ) : ℚ) * x.re = c 0 / 2 := congrArg QuaternionAlgebra.re hc
  have e1 : ((2 : ℕ) : ℚ) * x.imI = c 0 / 2 + c 1 := congrArg QuaternionAlgebra.imI hc
  have e2 : ((2 : ℕ) : ℚ) * x.imJ = c 0 / 2 + c 2 := congrArg QuaternionAlgebra.imJ hc
  have e3 : ((2 : ℕ) : ℚ) * x.imK = c 0 / 2 + c 3 := congrArg QuaternionAlgebra.imK hc
  push_cast at e0 e1 e2 e3
  simp only [trd] at ht
  simp only [nrd] at hm
  have hc0 : (c 0 : ℚ) = 2 * t := by linarith
  have hc0' : c 0 = 2 * t := by exact_mod_cast hc0
  have hE : ((t ^ 2 + (t + c 1) ^ 2 + (t + c 2) ^ 2 + (t + c 3) ^ 2 : ℤ) : ℚ) = ((4 * m : ℤ) : ℚ) := by
    have hx0 : x.re = t / 2 := by linarith
    have hx1 : x.imI = (t + c 1) / 2 := by linarith
    have hx2 : x.imJ = (t + c 2) / 2 := by linarith
    have hx3 : x.imK = (t + c 3) / 2 := by linarith
    rw [hx0, hx1, hx2, hx3] at hm
    push_cast at hm ⊢
    linear_combination 4 * hm
  have hE' : t ^ 2 + (t + c 1) ^ 2 + (t + c 2) ^ 2 + (t + c 3) ^ 2 = 4 * m := by exact_mod_cast hE
  have hz : ((t ^ 2 + (t + c 1) ^ 2 + (t + c 2) ^ 2 + (t + c 3) ^ 2 : ℤ) : ZMod 4) = 0 := by
    rw [hE']; push_cast; rw [show (4 : ZMod 4) = 0 from rfl, zero_mul]
  push_cast at hz
  obtain ⟨h1, h2, h3⟩ := zmod4_sumsq _ _ _ _ hz
  have d1 := int_dvd_of_zmod (n := 4) (z := 2 * c 1) (by push_cast; exact h1)
  have d2 := int_dvd_of_zmod (n := 4) (z := 2 * c 2) (by push_cast; exact h2)
  have d3 := int_dvd_of_zmod (n := 4) (z := 2 * c 3) (by push_cast; exact h3)
  obtain ⟨k1, hk1⟩ : (2 : ℤ) ∣ c 1 := by omega
  obtain ⟨k2, hk2⟩ : (2 : ℤ) ∣ c 2 := by omega
  obtain ⟨k3, hk3⟩ : (2 : ℤ) ∣ c 3 := by omega
  refine ⟨![t, k1, k2, k3], ?_⟩
  have q1 : (c 1 : ℚ) = 2 * k1 := by exact_mod_cast hk1
  have q2 : (c 2 : ℚ) = 2 * k2 := by exact_mod_cast hk2
  have q3 : (c 3 : ℚ) = 2 * k3 := by exact_mod_cast hk3
  ext <;> simp <;> linarith

/-! units -/

theorem card_unitGroup_eq {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (f : (Fin 4 → ℤ) → QuatAlg ℚ a b) (hf : Function.Injective f) (S : Finset (Fin 4 → ℤ))
    (hS : {x | x ∈ O.toSubalgebra ∧ nrd x = 1} = f '' S) : Nat.card (unitGroup O) = S.card := by
  have h1 := (unitGroup_eq_nrd_one_finite ha hb O).1
  rw [hS] at h1
  calc Nat.card (unitGroup O)
      = Nat.card (((↑) : (QuatAlg ℚ a b)ˣ → QuatAlg ℚ a b) '' (unitGroup O : Set (QuatAlg ℚ a b)ˣ)) := by
        rw [Nat.card_image_of_injective Units.val_injective]; rfl
    _ = Nat.card (f '' (S : Set (Fin 4 → ℤ))) := by rw [h1]
    _ = S.card := by rw [Nat.card_image_of_injective hf]; simp

/-- Coordinates of the Hurwitz order. -/
def fH (c : Fin 4 → ℤ) : QuatAlg ℚ (-1) (-1) := ⟨c 0 / 2, c 0 / 2 + c 1, c 0 / 2 + c 2, c 0 / 2 + c 3⟩

theorem fH_injective : Function.Injective fH := by
  intro c d h
  simp only [fH, QuaternionAlgebra.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 : (c 0 : ℚ) = d 0 := by linarith
  have e1 : (c 1 : ℚ) = d 1 := by linarith
  have e2 : (c 2 : ℚ) = d 2 := by linarith
  have e3 : (c 3 : ℚ) = d 3 := by linarith
  have i0 : c 0 = d 0 := by exact_mod_cast e0
  have i1 : c 1 = d 1 := by exact_mod_cast e1
  have i2 : c 2 = d 2 := by exact_mod_cast e2
  have i3 : c 3 = d 3 := by exact_mod_cast e3
  funext k; fin_cases k <;> assumption

theorem units_hurwitz : Nat.card (unitGroup hurwitzOrder) = 24 := by
  rw [card_unitGroup_eq (by norm_num) (by norm_num) hurwitzOrder fH fH_injective
    ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
      (fun c => c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4))]
  · decide
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨c, rfl⟩ := mem_hurwitz.mp hx
    have hq : ((c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      simp only [nrd] at hn; push_cast at hn ⊢; linear_combination 4 * hn
    have hq' : c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4 := by
      exact_mod_cast hq
    refine ⟨c, ⟨fun k => ?_, hq'⟩, rfl⟩
    have s0 := sq_nonneg (c 0)
    have s1 := sq_nonneg (c 0 + 2 * c 1)
    have s2 := sq_nonneg (c 0 + 2 * c 2)
    have s3 := sq_nonneg (c 0 + 2 * c 3)
    have b0 : -2 ≤ c 0 := by nlinarith
    have b0' : c 0 ≤ 2 := by nlinarith
    have b1 : -2 ≤ c 0 + 2 * c 1 := by nlinarith
    have b1' : c 0 + 2 * c 1 ≤ 2 := by nlinarith
    have b2 : -2 ≤ c 0 + 2 * c 2 := by nlinarith
    have b2' : c 0 + 2 * c 2 ≤ 2 := by nlinarith
    have b3 : -2 ≤ c 0 + 2 * c 3 := by nlinarith
    have b3' : c 0 + 2 * c 3 ≤ 2 := by nlinarith
    fin_cases k <;> simp <;> constructor <;> omega
  · rintro ⟨c, ⟨-, hq⟩, rfl⟩
    refine ⟨mem_hurwitz.mpr ⟨c, rfl⟩, ?_⟩
    have hq' : ((c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      exact_mod_cast hq
    simp only [nrd, fH]; push_cast at hq' ⊢; linear_combination hq' / 4

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-! class sets -/

/-- every `x ∈ B` has a positive multiple in `O` (copy of a private helper of `ClassSet.lean`). -/
theorem exists_nsmul_mem_order' {a b : ℤ} (O : QOrder a b) (x : QuatAlg ℚ a b) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) • x ∈ Subalgebra.toSubmodule O.toSubalgebra := by
  have hx : x ∈ Submodule.span ℚ (O.toSubalgebra : Set (QuatAlg ℚ a b)) := by
    rw [O.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, h₁, hy⟩ := hy
    obtain ⟨N₂, h₂, hz⟩ := hz
    refine ⟨N₁ * N₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((N₁ * N₂ : ℕ) : ℤ) • (y + z) = (N₂ : ℤ) • ((N₁ : ℤ) • y) + (N₁ : ℤ) • ((N₂ : ℤ) • z) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; rw [mul_comm (N₂ : ℤ)]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hz)
  | smul q y _ hy =>
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨q.den * N, Nat.mul_pos q.den_pos hN, ?_⟩
    have : ((q.den * N : ℕ) : ℤ) • (q • y) = q.num • ((N : ℤ) • y) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        smul_smul]
      congr 1
      push_cast
      linear_combination (N : ℚ) * Rat.mul_den_eq_num q
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- a finitely generated `J ⊆ B` has a positive multiple `N J ⊆ O`. -/
theorem exists_nsmul_le_order' {a b : ℤ} (O : QOrder a b) (J : Submodule ℤ (QuatAlg ℚ a b)) (hJ : J.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ j ∈ J, (N : ℤ) • j ∈ Subalgebra.toSubmodule O.toSubalgebra := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose N hN hNx using exists_nsmul_mem_order' O
  refine ⟨∏ g ∈ s, N g, Finset.prod_pos fun g _ => hN g, fun j hj => ?_⟩
  set P := (Subalgebra.toSubmodule O.toSubalgebra).comap
    ((∏ g ∈ s, N g : ℕ) • LinearMap.id : QuatAlg ℚ a b →ₗ[ℤ] QuatAlg ℚ a b)
  have hle : Submodule.span ℤ (s : Set (QuatAlg ℚ a b)) ≤ P := by
    rw [Submodule.span_le]
    intro g hg
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_coe.mp hg)
    show (∏ g ∈ s, N g : ℕ) • g ∈ Subalgebra.toSubmodule O.toSubalgebra
    have h := hNx g
    rw [natCast_zsmul] at h
    rw [hm, mul_comm, mul_smul]
    exact Submodule.smul_of_tower_mem _ m h
  have := hle hj
  simp only [P, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at this
  rwa [natCast_zsmul]

/-- If `O ⊆ J` with `J` finitely generated, then `[J : O]` is finite. -/
theorem relIndex_ne_zero_of_le {a b : ℤ} (O : QOrder a b) (J : Submodule ℤ (QuatAlg ℚ a b)) (hJ : J.FG)
    (hOJ : Subalgebra.toSubmodule O.toSubalgebra ≤ J) :
    (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup ≠ 0 := by
  classical
  obtain ⟨N, hN, hNJ⟩ := exists_nsmul_le_order' O J hJ
  -- `J/O` is a finitely generated torsion abelian group
  obtain ⟨s, hs⟩ := hJ
  have hfin : Finite (J.toAddSubgroup ⧸
      (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.addSubgroupOf J.toAddSubgroup) := by
    -- representatives `Σ_{g ∈ s} c_g g` with `0 ≤ c_g < N`
    have hsJ : ∀ g : s, (g : QuatAlg ℚ a b) ∈ J := fun g => hs ▸ Submodule.subset_span g.2
    let rep : (s → Fin N) → J.toAddSubgroup := fun c =>
      ⟨∑ g : s, ((c g : ℕ) : ℤ) • (g : QuatAlg ℚ a b),
        Submodule.sum_mem J fun g _ => Submodule.smul_mem J _ (hsJ g)⟩
    refine Finite.of_surjective (fun c : (s → Fin N) =>
      (QuotientAddGroup.mk (rep c) : J.toAddSubgroup ⧸
        (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.addSubgroupOf J.toAddSubgroup)) ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H j =>
      have hj : (j : QuatAlg ℚ a b) ∈ Submodule.span ℤ (s : Set (QuatAlg ℚ a b)) := hs ▸ j.2
      rw [Submodule.mem_span_finset'] at hj
      obtain ⟨f, hf⟩ := hj
      have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
      refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
      · have h0 := Int.emod_nonneg (f g) hN'
        have h1 := Int.emod_lt_of_pos (f g) (show (0 : ℤ) < N by exact_mod_cast hN)
        omega
      · rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        show -(∑ g : s, (((f g % N).toNat : ℕ) : ℤ) • (g : QuatAlg ℚ a b)) + (j : QuatAlg ℚ a b) ∈
          Subalgebra.toSubmodule O.toSubalgebra
        rw [← hf, neg_add_eq_sub, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun g _ => ?_
        have h0 := Int.emod_nonneg (f g) hN'
        have : f g • (g : QuatAlg ℚ a b) - (((f g % N).toNat : ℕ) : ℤ) • (g : QuatAlg ℚ a b) =
            (f g / N) • ((N : ℤ) • (g : QuatAlg ℚ a b)) := by
          rw [Int.toNat_of_nonneg h0, ← sub_smul, smul_smul]
          congr 1
          have := Int.emod_add_mul_ediv (f g) N
          linarith
        rw [this]
        exact Submodule.smul_mem _ _ (hNJ _ (hsJ g))
  exact AddSubgroup.index_ne_zero_of_finite

theorem finiteIdeleLattice_one {a b : ℤ} (O : QOrder a b) :
    finiteIdeleLattice O 1 = Subalgebra.toSubmodule O.toSubalgebra := by
  have h := (lattice_local_global a b).1 (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  ext z
  constructor
  · rintro ⟨y, hy, hz⟩
    rw [Units.val_one, one_mul] at hz
    have : z ∈ finEmbed a b ⁻¹' (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) := by
      show finEmbed a b z ∈ (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))
      rw [hz]; exact hy
    rw [h] at this
    exact this
  · intro hz
    exact ⟨finEmbed a b z, Submodule.subset_span ⟨z, hz, rfl⟩, by rw [Units.val_one, one_mul]⟩

/-- If `β⁻¹ L_x = O`, then `[x] = [1]`. -/
theorem mk_eq_one_of_lattice {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) (β : (QuatAlg ℚ a b)ˣ)
    (h : (finiteIdeleLattice O x).map (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) =
      Subalgebra.toSubmodule O.toSubalgebra) :
    (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x : classSet O) =
      DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) 1 := by
  refine (classSet_right_ideals O).2.2.1 x 1 β ?_
  rw [finiteIdeleLattice_one, ← h, ← Submodule.map_comp]
  conv_lhs => rw [← Submodule.map_id (finiteIdeleLattice O x)]
  congr 1
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.id_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, ← mul_assoc, Units.mul_inv,
    one_mul]

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-- Minkowski reduction of a class. -/
theorem minkowski_class {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (x : (BHat a b)ˣ) :
    ∃ β : (QuatAlg ℚ a b)ˣ,
      Subalgebra.toSubmodule O.toSubalgebra ≤
        (finiteIdeleLattice O x).map (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) ∧
      (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
        ((finiteIdeleLattice O x).map
          (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup ≠ 0 ∧
      Real.pi ^ 2 * ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
        ((finiteIdeleLattice O x).map
          (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup : ℝ) ≤
        8 * Real.sqrt (discriminant O : ℝ) := by
  obtain ⟨hFG, hspan, -⟩ := (lattice_local_global a b).2.1 O x
  obtain ⟨β, -, hle, hidx⟩ := minkowski_bound ha hb O (finiteIdeleLattice O x) hFG hspan
    ((classSet_right_ideals O).1 x)
  exact ⟨β, hle, relIndex_ne_zero_of_le O _ (hFG.map _) hle, hidx⟩

/-- Class number one from the Minkowski bound `8 √d(O) < 2π²`. -/
theorem mk_eq_one_of_small {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (hd : 8 * Real.sqrt (discriminant O : ℝ) < 2 * Real.pi ^ 2) (x : (BHat a b)ˣ) :
    (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x : classSet O) =
      DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) 1 := by
  obtain ⟨β, hle, hne, hidx⟩ := minkowski_class ha hb O x
  refine mk_eq_one_of_lattice O x β (le_antisymm ?_ hle)
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have h1 : ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
      ((finiteIdeleLattice O x).map
        (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup : ℝ) < 2 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have h2 : (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
      ((finiteIdeleLattice O x).map
        (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup = 1 := by
    have : ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
      ((finiteIdeleLattice O x).map
        (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup) < 2 := by
      exact_mod_cast h1
    omega
  exact fun z hz => AddSubgroup.relIndex_eq_one.mp h2 hz

/-- `Γ_1 = O^×`. -/
theorem classStabilizer_one {a b : ℤ} (O : QOrder a b) :
    classStabilizer (orderCompletionUnits O) 1 = unitGroup O := by
  have h := (lattice_local_global a b).1 (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  have hmem : ∀ z : QuatAlg ℚ a b, finEmbed a b z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ↔
      z ∈ O.toSubalgebra := fun z => by
    have : z ∈ finEmbed a b ⁻¹' (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ↔
        z ∈ ((Subalgebra.toSubmodule O.toSubalgebra : Submodule ℤ (QuatAlg ℚ a b)) : Set (QuatAlg ℚ a b)) := by
      rw [h]
    exact this
  ext u
  simp only [classStabilizer, Subgroup.mem_comap, Subgroup.mem_map, map_one, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, hvu⟩
    have hvu' : v = Units.map (finEmbed a b).toMonoidHom u := by simpa using hvu
    subst hvu'
    refine ⟨(hmem _).mp hv, (hmem _).mp ?_⟩
    simpa [← map_inv] using hv'
  · rintro ⟨hu, hu'⟩
    refine ⟨Units.map (finEmbed a b).toMonoidHom u, ⟨(hmem _).mpr hu, ?_⟩, by simp⟩
    simpa [← map_inv] using (hmem _).mpr hu'

/-- `|Γ_{out [x]}| = |Γ_x|`. -/
theorem card_classStabilizer_out {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) :
    Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out
      (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x : classSet O))) =
      Nat.card (classStabilizer (orderCompletionUnits O) x) := by
  obtain ⟨h, ⟨γ, rfl⟩, k, hk, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x
  have hout' : Quotient.out
      (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x : classSet O) =
      Units.map (finEmbed a b).toMonoidHom γ * x * k := hout
  rw [hout', (stabilizer_units O x).2.1 γ k hk]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem classSet_hurwitz_eq (c : classSet hurwitzOrder) :
    c = DoubleCoset.mk (Units.map (finEmbed (-1) (-1)).toMonoidHom).range (orderCompletionUnits hurwitzOrder) 1 := by
  induction c using Quotient.inductionOn with
  | h x =>
    refine mk_eq_one_of_small (by norm_num) (by norm_num) hurwitzOrder ?_ x
    rw [discriminant_hurwitz]
    have := Real.pi_gt_three
    norm_num [sqrt_four]
    nlinarith

theorem mass_hurwitz : mass hurwitzOrder = 1 / 24 := by
  rw [mass]
  refine (finsum_eq_single (fun c : classSet hurwitzOrder => (1 : ℚ) /
      (Nat.card (classStabilizer (orderCompletionUnits hurwitzOrder) (Quotient.out c)) : ℚ))
    (DoubleCoset.mk (Units.map (finEmbed (-1) (-1)).toMonoidHom).range (orderCompletionUnits hurwitzOrder) 1)
    (fun c hc => absurd (classSet_hurwitz_eq c) hc)).trans ?_
  rw [card_classStabilizer_out, classStabilizer_one, units_hurwitz]
  norm_num

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-! ## D = 11 -/

/-- Pizer's basis for `b = −11`. -/
abbrev v11 : Fin 4 → QuatAlg ℚ (-1) (-11) := ![⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- `O₁₁`. -/
noncomputable abbrev O11 : QOrder (-1) (-11) := pizerOrderI (-11) (by norm_num)

theorem sum_v11 (c : Fin 4 → ℚ) : ∑ k, c k • v11 k = ⟨c 0 / 2, c 1 / 2, c 0 / 2 + c 2, c 1 / 2 + c 3⟩ := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, QuaternionAlgebra.smul_mk,
    QuaternionAlgebra.mk_add_mk, smul_eq_mul, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Coordinates of `O₁₁`. -/
def f11 (c : Fin 4 → ℤ) : QuatAlg ℚ (-1) (-11) := ⟨c 0 / 2, c 1 / 2, c 0 / 2 + c 2, c 1 / 2 + c 3⟩

theorem mem_O11 {x : QuatAlg ℚ (-1) (-11)} : x ∈ O11.toSubalgebra ↔ ∃ c : Fin 4 → ℤ, x = f11 c := by
  show x ∈ Submodule.span ℤ _ ↔ _
  rw [mem_span4]
  exact exists_congr fun c => by rw [sum_v11 fun k => (c k : ℚ)]; rfl

theorem f11_eq_sum (c : Fin 4 → ℤ) : f11 c = ∑ k, (c k : ℚ) • v11 k := by
  rw [sum_v11]; rfl

theorem f11_injective : Function.Injective f11 := by
  intro c d h
  simp only [f11, QuaternionAlgebra.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have i0 : c 0 = d 0 := by exact_mod_cast (show (c 0 : ℚ) = d 0 by linarith)
  have i1 : c 1 = d 1 := by exact_mod_cast (show (c 1 : ℚ) = d 1 by linarith)
  have i2 : c 2 = d 2 := by exact_mod_cast (show (c 2 : ℚ) = d 2 by linarith)
  have i3 : c 3 = d 3 := by exact_mod_cast (show (c 3 : ℚ) = d 3 by linarith)
  funext k; fin_cases k <;> assumption

theorem linIndep_v11 : LinearIndependent ℤ v11 := by
  refine linIndep_of_sum _ fun c hc => ?_
  have h : f11 c = f11 0 := by
    rw [show f11 c = ∑ k, (c k : ℚ) • v11 k from (sum_v11 fun k => (c k : ℚ)).symm, hc]
    ext <;> simp [f11]
  intro k
  exact congrFun (f11_injective h) k

noncomputable def basis11 : Module.Basis (Fin 4) ℤ (Subalgebra.toSubmodule O11.toSubalgebra) :=
  Module.Basis.span linIndep_v11

theorem basis11_apply (k : Fin 4) : (basis11 k : QuatAlg ℚ (-1) (-11)) = v11 k := by
  show ((Module.Basis.span linIndep_v11 k : Submodule.span ℤ (Set.range v11)) : QuatAlg ℚ (-1) (-11)) = v11 k
  rw [Module.Basis.span_apply]

theorem discriminant_O11 : discriminant O11 = 121 := by
  rw [(discriminant_basic O11).1 basis11]
  simp only [basis11_apply]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, trd, Fin.succAbove]
  norm_num

theorem zmod11_sumsq : ∀ u v : ZMod 11, u ^ 2 + v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide

theorem zmod11_sumsq4 : ∀ u v : ZMod 11, 4 * u ^ 2 + 4 * v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide

theorem isMaximal_O11 : IsMaximalOrder O11 := by
  refine isMaximalOrder_of_criterion _ fun p hp ⟨n, hn⟩ x hpx hx ⟨_, ⟨m, hm⟩⟩ => hx ?_
  have h11 : Nat.Prime 11 := by norm_num
  rw [discriminant_O11, show (121 : ℚ) = ((11 : ℕ) : ℚ) ^ 2 by norm_num] at hn
  obtain rfl := prime_eq_of_sq_dvd hp h11 hn
  rw [mem_O11] at hpx ⊢
  obtain ⟨c, hc⟩ := hpx
  have e0 : ((11 : ℕ) : ℚ) * x.re = c 0 / 2 := congrArg QuaternionAlgebra.re hc
  have e1 : ((11 : ℕ) : ℚ) * x.imI = c 1 / 2 := congrArg QuaternionAlgebra.imI hc
  have e2 : ((11 : ℕ) : ℚ) * x.imJ = c 0 / 2 + c 2 := congrArg QuaternionAlgebra.imJ hc
  have e3 : ((11 : ℕ) : ℚ) * x.imK = c 1 / 2 + c 3 := congrArg QuaternionAlgebra.imK hc
  push_cast at e0 e1 e2 e3
  simp only [nrd] at hm
  have hx0 : x.re = c 0 / 22 := by linarith
  have hx1 : x.imI = c 1 / 22 := by linarith
  have hx2 : x.imJ = (c 0 + 2 * c 2) / 22 := by linarith
  have hx3 : x.imK = (c 1 + 2 * c 3) / 22 := by linarith
  rw [hx0, hx1, hx2, hx3] at hm
  have hE : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ℚ) =
      ((484 * m : ℤ) : ℚ) := by
    push_cast at hm ⊢
    linear_combination 484 * hm
  have hE' : c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 484 * m := by
    exact_mod_cast hE
  have hz : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ZMod 11) = 0 := by
    rw [hE']; push_cast; rw [show (484 : ZMod 11) = 0 from rfl, zero_mul]
  push_cast at hz
  rw [show (11 : ZMod 11) = 0 from rfl] at hz
  simp only [zero_mul, add_zero] at hz
  obtain ⟨z0, z1⟩ := zmod11_sumsq _ _ hz
  obtain ⟨d0, hd0⟩ := int_dvd_of_zmod (n := 11) z0
  obtain ⟨d1, hd1⟩ := int_dvd_of_zmod (n := 11) z1
  push_cast at hd0 hd1
  rw [hd0, hd1] at hE'
  have hE2 : 11 * (d0 ^ 2 + d1 ^ 2) + (11 * d0 + 2 * c 2) ^ 2 + (11 * d1 + 2 * c 3) ^ 2 = 44 * m := by
    linarith
  have hz2 : ((11 * (d0 ^ 2 + d1 ^ 2) + (11 * d0 + 2 * c 2) ^ 2 + (11 * d1 + 2 * c 3) ^ 2 : ℤ) : ZMod 11) = 0 := by
    rw [hE2]; push_cast; rw [show (44 : ZMod 11) = 0 from rfl, zero_mul]
  push_cast at hz2
  rw [show (11 : ZMod 11) = 0 from rfl] at hz2
  have hz2' : 4 * (c 2 : ZMod 11) ^ 2 + 4 * (c 3 : ZMod 11) ^ 2 = 0 := by
    linear_combination hz2
  obtain ⟨z2, z3⟩ := zmod11_sumsq4 _ _ hz2'
  obtain ⟨d2, hd2⟩ := int_dvd_of_zmod (n := 11) z2
  obtain ⟨d3, hd3⟩ := int_dvd_of_zmod (n := 11) z3
  push_cast at hd2 hd3
  refine ⟨![d0, d1, d2, d3], ?_⟩
  have q0 : (c 0 : ℚ) = 11 * d0 := by exact_mod_cast hd0
  have q1 : (c 1 : ℚ) = 11 * d1 := by exact_mod_cast hd1
  have q2 : (c 2 : ℚ) = 11 * d2 := by exact_mod_cast hd2
  have q3 : (c 3 : ℚ) = 11 * d3 := by exact_mod_cast hd3
  ext <;> simp [f11] <;> linarith

theorem units_O11 : Nat.card (unitGroup O11) = 4 := by
  rw [card_unitGroup_eq (by norm_num) (by norm_num) O11 f11 f11_injective
    ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
      (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4))]
  · decide
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨c, rfl⟩ := mem_O11.mp hx
    have hq : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      simp only [nrd, f11] at hn; push_cast at hn ⊢; linear_combination 4 * hn
    have hq' : c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 := by
      exact_mod_cast hq
    refine ⟨c, ⟨fun k => ?_, hq'⟩, rfl⟩
    have s0 := sq_nonneg (c 0)
    have s1 := sq_nonneg (c 1)
    have s2 := sq_nonneg (c 0 + 2 * c 2)
    have s3 := sq_nonneg (c 1 + 2 * c 3)
    have b0 : -2 ≤ c 0 := by nlinarith
    have b0' : c 0 ≤ 2 := by nlinarith
    have b1 : -2 ≤ c 1 := by nlinarith
    have b1' : c 1 ≤ 2 := by nlinarith
    have b2 : -1 ≤ c 0 + 2 * c 2 := by nlinarith
    have b2' : c 0 + 2 * c 2 ≤ 1 := by nlinarith
    have b3 : -1 ≤ c 1 + 2 * c 3 := by nlinarith
    have b3' : c 1 + 2 * c 3 ≤ 1 := by nlinarith
    fin_cases k <;> simp <;> constructor <;> omega
  · rintro ⟨c, ⟨-, hq⟩, rfl⟩
    refine ⟨mem_O11.mpr ⟨c, rfl⟩, ?_⟩
    have hq' : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      exact_mod_cast hq
    simp only [nrd, f11]; push_cast at hq' ⊢; linear_combination hq' / 4

theorem ramified_d11 : RamifiedExactly (-1) (-11) 11 := by
  have := pizer_algebras.2.1 11 (by norm_num) (by norm_num)
  simpa using this

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-! ## Level structures on `O₁₁` -/

/-- The multiplication table of `v11`. -/
def T11 : Fin 4 → Fin 4 → Fin 4 → ℤ :=
  ![![![-5, 0, 3, 0], ![0, 6, 0, -3], ![-11, 0, 6, 0], ![0, 11, 0, -5]],
    ![![0, -5, 0, 3], ![-6, 0, 3, 0], ![0, -11, 0, 6], ![-11, 0, 5, 0]],
    ![![-11, 0, 6, 0], ![0, 11, 0, -6], ![-22, 0, 11, 0], ![0, 22, 0, -11]],
    ![![0, -11, 0, 6], ![-11, 0, 6, 0], ![0, -22, 0, 11], ![-22, 0, 11, 0]]]

theorem f11_add (c d : Fin 4 → ℤ) : f11 (c + d) = f11 c + f11 d := by
  simp only [f11, QuaternionAlgebra.mk_add_mk, Pi.add_apply, QuaternionAlgebra.mk.injEq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem f11_zero : f11 0 = 0 := by
  ext <;> simp [f11]

theorem f11_one : f11 ![2, 0, -1, 0] = 1 := by
  ext <;> simp [f11]

theorem f11_mul (c d : Fin 4 → ℤ) :
    f11 c * f11 d = f11 (fun r => ∑ k, ∑ l, c k * d l * T11 k l r) := by
  simp only [f11, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk.injEq]
  simp only [Fin.sum_univ_four, T11, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Integer coordinates of an element of `O₁₁`. -/
noncomputable def coord11 (x : O11.toSubalgebra) : Fin 4 → ℤ := Classical.choose (mem_O11.mp x.2)

theorem coord11_spec (x : O11.toSubalgebra) : (x : QuatAlg ℚ (-1) (-11)) = f11 (coord11 x) :=
  Classical.choose_spec (mem_O11.mp x.2)

theorem coord11_eq {x : O11.toSubalgebra} {c : Fin 4 → ℤ} (h : (x : QuatAlg ℚ (-1) (-11)) = f11 c) :
    coord11 x = c :=
  f11_injective ((coord11_spec x).symm.trans h)

theorem table_mul {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (X : Fin 4 → A)
    (T : Fin 4 → Fin 4 → Fin 4 → ℤ) (hX : ∀ k l, X k * X l = ∑ r, ((T k l r : ℤ) : R) • X r)
    (c d : Fin 4 → R) :
    (∑ k, c k • X k) * (∑ l, d l • X l) = ∑ r, (∑ k, ∑ l, c k * d l * (T k l r : R)) • X r := by
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, hX, Finset.smul_sum, smul_smul, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- A level structure on `O₁₁` from images of the basis satisfying the multiplication table. -/
noncomputable def level11 (M : ℕ) [NeZero M] (X : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod M))
    (hX : ∀ k l, X k * X l = ∑ r, ((T11 k l r : ℤ) : ZMod M) • X r)
    (h1 : ∑ k, (((![2, 0, -1, 0] : Fin 4 → ℤ) k : ℤ) : ZMod M) • X k = 1)
    (hs : ∀ Y, ∃ m : Fin 4 → ZMod M, ∑ k, m k • X k = Y) : LevelStructure O11 M where
  toRingHom :=
    { toFun := fun x => ∑ k, ((coord11 x k : ℤ) : ZMod M) • X k
      map_one' := by
        show ∑ k, ((coord11 1 k : ℤ) : ZMod M) • X k = 1
        rw [coord11_eq (c := ![2, 0, -1, 0]) (by rw [f11_one]; rfl)]
        exact h1
      map_mul' := fun x y => by
        show ∑ k, ((coord11 (x * y) k : ℤ) : ZMod M) • X k =
          (∑ k, ((coord11 x k : ℤ) : ZMod M) • X k) * (∑ k, ((coord11 y k : ℤ) : ZMod M) • X k)
        rw [table_mul X T11 hX, coord11_eq (c := fun r => ∑ k, ∑ l, coord11 x k * coord11 y l * T11 k l r)
          (by rw [← f11_mul, ← coord11_spec, ← coord11_spec]; rfl)]
        push_cast
        rfl
      map_zero' := by
        show ∑ k, ((coord11 0 k : ℤ) : ZMod M) • X k = 0
        rw [coord11_eq (c := 0) (by rw [f11_zero]; rfl)]
        simp
      map_add' := fun x y => by
        show ∑ k, ((coord11 (x + y) k : ℤ) : ZMod M) • X k =
          ∑ k, ((coord11 x k : ℤ) : ZMod M) • X k + ∑ k, ((coord11 y k : ℤ) : ZMod M) • X k
        rw [coord11_eq (c := coord11 x + coord11 y) (by rw [f11_add, ← coord11_spec, ← coord11_spec]; rfl)]
        simp [add_smul, Finset.sum_add_distrib] }
  surjective := fun Y => by
    obtain ⟨m, hm⟩ := hs Y
    refine ⟨⟨f11 fun k => ((m k).val : ℤ), mem_O11.mpr ⟨_, rfl⟩⟩, ?_⟩
    show ∑ k, ((coord11 _ k : ℤ) : ZMod M) • X k = Y
    rw [coord11_eq (c := fun k => ((m k).val : ℤ)) rfl, ← hm]
    simp

def X3 : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![!![1, 0; 0, 0], !![0, 0; 1, 0], !![1, 0; 0, 2], !![0, 1; 1, 0]]

def X2 : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![!![0, 1; 1, 1], !![1, 0; 1, 1], !![1, 0; 0, 1], !![1, 1; 0, 1]]

theorem X3_table : ∀ k l, X3 k * X3 l = ∑ r, ((T11 k l r : ℤ) : ZMod 3) • X3 r := by decide
theorem X2_table : ∀ k l, X2 k * X2 l = ∑ r, ((T11 k l r : ℤ) : ZMod 2) • X2 r := by decide
theorem X3_one : ∑ k, (((![2, 0, -1, 0] : Fin 4 → ℤ) k : ℤ) : ZMod 3) • X3 k = 1 := by decide
theorem X2_one : ∑ k, (((![2, 0, -1, 0] : Fin 4 → ℤ) k : ℤ) : ZMod 2) • X2 k = 1 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem X3_surj : ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod 3), ∃ m : Fin 4 → ZMod 3, ∑ k, m k • X3 k = Y := by decide
theorem X2_surj : ∀ Y : Matrix (Fin 2) (Fin 2) (ZMod 2), ∃ m : Fin 4 → ZMod 2, ∑ k, m k • X2 k = Y := by decide

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-! ## Generic span lemmas -/

theorem mem_span_of_eq {a b : ℤ} (u : Fin 4 → QuatAlg ℚ a b) {z : QuatAlg ℚ a b} (e : Fin 4 → ℤ)
    (h : z = ∑ k, (e k : ℚ) • u k) : z ∈ Submodule.span ℤ (Set.range u) :=
  (mem_span4 u z).mpr ⟨e, h⟩

/-- Products of spans from a table. -/
theorem mul_mem_span_table {a b : ℤ} (u v w : Fin 4 → QuatAlg ℚ a b) (M : Fin 4 → Fin 4 → Fin 4 → ℤ)
    (hM : ∀ k l, u k * v l = ∑ r, (M k l r : ℚ) • w r) {y z : QuatAlg ℚ a b}
    (hy : y ∈ Submodule.span ℤ (Set.range u)) (hz : z ∈ Submodule.span ℤ (Set.range v)) :
    y * z ∈ Submodule.span ℤ (Set.range w) := by
  have hle : Submodule.span ℤ (Set.range u) * Submodule.span ℤ (Set.range v) ≤
      Submodule.span ℤ (Set.range w) := by
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    show u k * v l ∈ _
    rw [hM]
    exact sum_smul_mem_span w _
  exact hle (Submodule.mul_mem_mul hy hz)

/-- Left multiplication of a span from a table. -/
theorem mul_mem_span_left {a b : ℤ} (γ : QuatAlg ℚ a b) (u w : Fin 4 → QuatAlg ℚ a b) (M : Fin 4 → Fin 4 → ℤ)
    (hM : ∀ k, γ * u k = ∑ r, (M k r : ℚ) • w r) {z : QuatAlg ℚ a b}
    (hz : z ∈ Submodule.span ℤ (Set.range u)) : γ * z ∈ Submodule.span ℤ (Set.range w) := by
  obtain ⟨c, rfl⟩ := (mem_span4 u z).mp hz
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [mul_smul_comm, hM, Int.cast_smul_eq_zsmul ℚ]
  exact Submodule.smul_mem _ _ (sum_smul_mem_span w _)

/-! ## The second class of `O₁₁` -/

/-- The right ideal `J₂ ⊇ O₁₁` of index 4 (certificate `index4_right_ideals[1]`). -/
abbrev w2 : Fin 4 → QuatAlg ℚ (-1) (-11) := ![⟨1 / 4, 0, 3 / 4, 1 / 2⟩, ⟨0, 1 / 4, 1 / 2, 1 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- Its left order (certificate `left_order_basis`). -/
abbrev lo2 : Fin 4 → QuatAlg ℚ (-1) (-11) := ![⟨1 / 2, 0, 1 / 2, 1⟩, ⟨0, 1 / 4, 1 / 2, 5 / 4⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 2⟩]

theorem sum_w2 (c : Fin 4 → ℚ) : ∑ k, c k • w2 k =
    ⟨c 0 / 4, c 1 / 4, 3 * c 0 / 4 + c 1 / 2 + c 2, c 0 / 2 + c 1 / 4 + c 3⟩ := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, QuaternionAlgebra.smul_mk,
    QuaternionAlgebra.mk_add_mk, smul_eq_mul, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem sum_lo2 (c : Fin 4 → ℚ) : ∑ k, c k • lo2 k =
    ⟨c 0 / 2, c 1 / 4, c 0 / 2 + c 1 / 2 + c 2, c 0 + 5 * c 1 / 4 + 2 * c 3⟩ := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, QuaternionAlgebra.smul_mk,
    QuaternionAlgebra.mk_add_mk, smul_eq_mul, QuaternionAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `J₂ O₁₁ ⊆ J₂`. -/
theorem w2_table : ∀ k l, w2 k * v11 l = ∑ r, (((![
    ![![-16, -11, 18, 11], ![-11, 17, 0, 1], ![-33, -22, 36, 22], ![-22, 33, 0, 3]],
    ![![-11, -5, 11, 7], ![-6, 11, -1, 0], ![-22, -11, 22, 14], ![-11, 22, -3, 0]],
    ![![-22, 0, 17, 11], ![0, 22, -11, -6], ![-44, 0, 33, 22], ![0, 44, -22, -11]],
    ![![0, -22, 11, 6], ![-22, 0, 17, 11], ![0, -44, 22, 11], ![-44, 0, 33, 22]]] :
    Fin 4 → Fin 4 → Fin 4 → ℤ) k l r : ℤ) : ℚ) • w2 r := by
  intro k l
  rw [sum_w2]
  fin_cases k <;> fin_cases l <;> norm_num [QuaternionAlgebra.mk_mul_mk]

/-- `lo₂ J₂ ⊆ J₂`. -/
theorem lo2_table : ∀ k l, lo2 k * w2 l = ∑ r, (((![
    ![![-38, -22, 40, 25], ![-22, -16, 25, 15], ![-22, -44, 39, 22], ![-44, 22, 22, 17]],
    ![![-44, -30, 48, 30], ![-25, -22, 30, 18], ![-22, -55, 44, 25], ![-55, 22, 30, 22]],
    ![![-33, 22, 14, 11], ![-22, 11, 11, 8], ![-44, 0, 33, 22], ![0, 44, -22, -11]],
    ![![-44, -66, 66, 39], ![-22, -44, 39, 22], ![0, -88, 44, 22], ![-88, 0, 66, 44]]] :
    Fin 4 → Fin 4 → Fin 4 → ℤ) k l r : ℤ) : ℚ) • w2 r := by
  intro k l
  rw [sum_w2]
  fin_cases k <;> fin_cases l <;> norm_num [QuaternionAlgebra.mk_mul_mk]

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-- `z ∈ ι⁻¹(xÔx⁻¹)` iff `z L_x ⊆ L_x`. -/
theorem mem_conj_iff {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) (z : QuatAlg ℚ a b) :
    z ∈ finEmbed a b ⁻¹' ((fun y : BHat a b ↦ (x : BHat a b) * y * ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
      (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))) ↔
    ∀ w ∈ finiteIdeleLattice O x, z * w ∈ finiteIdeleLattice O x := by
  constructor
  · rintro ⟨o, ho, hzo⟩ w ⟨o', ho', hw⟩
    refine ⟨o * o', mul_mem_orderCompletion O ho ho', ?_⟩
    rw [map_mul, hw, ← hzo]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · intro h
    have hc := ((lattice_local_global a b).2.1 O x).2.2
    have hx : (x : BHat a b) ∈ (latticeCompletion (finiteIdeleLattice O x) : Set (BHat a b)) := by
      rw [hc]
      exact ⟨1, one_mem_orderCompletion O, show (x : BHat a b) * 1 = x from mul_one _⟩
    have hmul : ∀ y ∈ latticeCompletion (finiteIdeleLattice O x),
        finEmbed a b z * y ∈ latticeCompletion (finiteIdeleLattice O x) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        exact Submodule.subset_span ⟨z * w, h w hw, map_mul _ _ _⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ hy hy' => rw [mul_add]; exact Submodule.add_mem _ hy hy'
      | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    have h1 := hmul _ hx
    have h2 : finEmbed a b z * (x : BHat a b) ∈ (latticeCompletion (finiteIdeleLattice O x) : Set (BHat a b)) :=
      h1
    rw [hc] at h2
    obtain ⟨o, ho, hxo⟩ := h2
    refine ⟨o, ho, ?_⟩
    show (x : BHat a b) * o * ((x⁻¹ : (BHat a b)ˣ) : BHat a b) = finEmbed a b z
    have hxo' : (x : BHat a b) * o = finEmbed a b z * x := hxo
    rw [hxo', mul_assoc, Units.mul_inv, mul_one]

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-- Coordinates in the left order `lo₂`. -/
def flo (d : Fin 4 → ℤ) : QuatAlg ℚ (-1) (-11) :=
  ⟨d 0 / 2, d 1 / 4, d 0 / 2 + d 1 / 2 + d 2, d 0 + 5 * d 1 / 4 + 2 * d 3⟩

theorem flo_injective : Function.Injective flo := by
  intro c d h
  simp only [flo, QuaternionAlgebra.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have i0 : c 0 = d 0 := by exact_mod_cast (show (c 0 : ℚ) = d 0 by linarith)
  have i1 : c 1 = d 1 := by exact_mod_cast (show (c 1 : ℚ) = d 1 by linarith)
  have i2 : c 2 = d 2 := by exact_mod_cast (show (c 2 : ℚ) = d 2 by linarith)
  have i3 : c 3 = d 3 := by exact_mod_cast (show (c 3 : ℚ) = d 3 by linarith)
  funext k; fin_cases k <;> assumption

theorem flo_mem (d : Fin 4 → ℤ) : flo d ∈ Submodule.span ℤ (Set.range lo2) :=
  mem_span_of_eq lo2 d (by rw [sum_lo2]; rfl)

/-- The units of `lo₂`, in coordinates. -/
def S6 : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun k => (![Finset.Icc (-2) 2, Finset.Icc (-4) 4, Finset.Icc (-3) 3, Finset.Icc (-3) 3] :
      Fin 4 → Finset ℤ) k).filter
    (fun d => 4 * d 0 ^ 2 + d 1 ^ 2 + 11 * (2 * d 0 + 2 * d 1 + 4 * d 2) ^ 2 +
      11 * (4 * d 0 + 5 * d 1 + 8 * d 3) ^ 2 = 16)

-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem S6_card : S6.card = 6 := by decide

theorem mem_S6 {d : Fin 4 → ℤ} : d ∈ S6 ↔ (∀ k, d k ∈ (![Finset.Icc (-2) 2, Finset.Icc (-4) 4, Finset.Icc (-3) 3,
    Finset.Icc (-3) 3] : Fin 4 → Finset ℤ) k) ∧ 4 * d 0 ^ 2 + d 1 ^ 2 + 11 * (2 * d 0 + 2 * d 1 + 4 * d 2) ^ 2 +
      11 * (4 * d 0 + 5 * d 1 + 8 * d 3) ^ 2 = 16 := by
  simp only [S6, Finset.mem_filter, Fintype.mem_piFinset]

set_option maxHeartbeats 1000000 in
theorem card_stab_x2 (x : (BHat (-1) (-11))ˣ)
    (hx : Submodule.span ℤ (Set.range w2) = finiteIdeleLattice O11 x) :
    Nat.card (classStabilizer (orderCompletionUnits O11) x) = 6 := by
  obtain ⟨Ox, hOx, hΓ⟩ := (stabilizer_units O11 x).1
  have hmem : ∀ z, z ∈ Ox.toSubalgebra ↔
      ∀ w ∈ Submodule.span ℤ (Set.range w2), z * w ∈ Submodule.span ℤ (Set.range w2) := by
    intro z
    rw [hx, ← mem_conj_iff O11 x z, ← hOx]
    rfl
  rw [hΓ, card_unitGroup_eq (by norm_num) (by norm_num) Ox flo flo_injective
    S6]
  · exact S6_card
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, mem_S6]
  constructor
  · rintro ⟨hz, hn⟩
    have h := (hmem z).mp hz
    obtain ⟨n0, e0⟩ := (mem_span4 w2 _).mp (h _ (Submodule.subset_span ⟨0, rfl⟩))
    obtain ⟨n1, e1⟩ := (mem_span4 w2 _).mp (h _ (Submodule.subset_span ⟨1, rfl⟩))
    obtain ⟨n2, e2⟩ := (mem_span4 w2 _).mp (h _ (Submodule.subset_span ⟨2, rfl⟩))
    obtain ⟨n3, e3⟩ := (mem_span4 w2 _).mp (h _ (Submodule.subset_span ⟨3, rfl⟩))
    rw [sum_w2] at e0 e1 e2 e3
    obtain ⟨z0, z1, z2, z3⟩ := z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.mk.injEq] at e0 e1 e2 e3
    obtain ⟨a00, a01, a02, a03⟩ := e0
    obtain ⟨a10, a11, a12, a13⟩ := e1
    obtain ⟨a20, a21, a22, a23⟩ := e2
    obtain ⟨a30, a31, a32, a33⟩ := e3
    let d : Fin 4 → ℤ := ![-198 * n0 3 + 495 * n1 0 + 379 * n1 1 + 594 * n1 3 - 441 * n2 1 - 377 * n3 3,
      7 * n1 0 + 3 * n1 1 + 11 * n1 3 - 2 * n2 1 - 3 * n3 3,
      -2 * n1 0 - n1 1 - 4 * n1 3,
      -9 * n0 3 + 20 * n1 0 + 16 * n1 1 + 22 * n1 3 - 20 * n2 1 - 17 * n3 3]
    have hzd : (⟨z0, z1, z2, z3⟩ : QuatAlg ℚ (-1) (-11)) = flo d := by
      simp only [flo, d, QuaternionAlgebra.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
      push_cast at *
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    rw [hzd] at hn ⊢
    have hq : ((4 * d 0 ^ 2 + d 1 ^ 2 + 11 * (2 * d 0 + 2 * d 1 + 4 * d 2) ^ 2 +
        11 * (4 * d 0 + 5 * d 1 + 8 * d 3) ^ 2 : ℤ) : ℚ) = 16 := by
      simp only [nrd, flo] at hn; push_cast at hn ⊢; linear_combination 16 * hn
    have hq' : 4 * d 0 ^ 2 + d 1 ^ 2 + 11 * (2 * d 0 + 2 * d 1 + 4 * d 2) ^ 2 +
        11 * (4 * d 0 + 5 * d 1 + 8 * d 3) ^ 2 = 16 := by exact_mod_cast hq
    refine ⟨d, ⟨fun k => ?_, hq'⟩, rfl⟩
    have s0 := sq_nonneg (d 0)
    have s1 := sq_nonneg (d 1)
    have s2 := sq_nonneg (2 * d 0 + 2 * d 1 + 4 * d 2)
    have s3 := sq_nonneg (4 * d 0 + 5 * d 1 + 8 * d 3)
    have b0 : -2 ≤ d 0 := by nlinarith
    have b0' : d 0 ≤ 2 := by nlinarith
    have b1 : -4 ≤ d 1 := by nlinarith
    have b1' : d 1 ≤ 4 := by nlinarith
    have b2 : -1 ≤ 2 * d 0 + 2 * d 1 + 4 * d 2 := by nlinarith
    have b2' : 2 * d 0 + 2 * d 1 + 4 * d 2 ≤ 1 := by nlinarith
    have b3 : -1 ≤ 4 * d 0 + 5 * d 1 + 8 * d 3 := by nlinarith
    have b3' : 4 * d 0 + 5 * d 1 + 8 * d 3 ≤ 1 := by nlinarith
    fin_cases k <;> simp <;> constructor <;> omega
  · rintro ⟨d, ⟨-, hq⟩, rfl⟩
    have hL : ∀ w ∈ Submodule.span ℤ (Set.range w2), flo d * w ∈ Submodule.span ℤ (Set.range w2) :=
      fun w hw => mul_mem_span_table lo2 w2 w2 _ lo2_table (flo_mem d) hw
    refine ⟨(hmem _).mpr hL, ?_⟩
    have hq' : ((4 * d 0 ^ 2 + d 1 ^ 2 + 11 * (2 * d 0 + 2 * d 1 + 4 * d 2) ^ 2 +
        11 * (4 * d 0 + 5 * d 1 + 8 * d 3) ^ 2 : ℤ) : ℚ) = 16 := by exact_mod_cast hq
    simp only [nrd, flo]; push_cast at hq' ⊢; linear_combination hq' / 16

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

section Local

variable {p : ℕ} [Fact p.Prime] {a b : ℤ}

theorem bc_smul (q : ℚ) (z : QuatAlg ℚ a b) :
    baseChange a b (algebraMap ℚ ℚ_[p]) (q • z) = (q : ℚ_[p]) • baseChange a b (algebraMap ℚ ℚ_[p]) z := by
  ext <;> simp [baseChange]

theorem zp_smul (r : ℤ_[p]) (y : QuatAlg ℚ_[p] a b) : r • y = (r : ℚ_[p]) • y := by
  ext <;> exact (Algebra.smul_def r _).trans rfl

/-- `ℤ_p`-span inclusion from `p`-integral coordinates. -/
theorem span_bc_le (u v : Fin 4 → QuatAlg ℚ a b) (γ : QuatAlg ℚ a b) (m : Fin 4 → Fin 4 → ℤ) (s : ℚ)
    (hs : ‖(s : ℚ_[p])‖ ≤ 1) (h : ∀ k, u k = γ * ∑ l, ((m k l : ℚ) * s) • v l) :
    Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range u) : Set (QuatAlg ℚ a b))) ≤
      (Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ a b)))).map
        (LinearMap.mulLeft ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) γ)) := by
  rw [Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    rw [h k, map_mul, map_sum]
    refine ⟨_, Submodule.sum_mem _ fun l _ => ?_, rfl⟩
    have hn : ‖(((m k l : ℚ) * s : ℚ) : ℚ_[p])‖ ≤ 1 := by
      push_cast
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (Padic.norm_int_le_one _) hs (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [bc_smul, show (((m k l : ℚ) * s : ℚ) : ℚ_[p]) = ((⟨_, hn⟩ : ℤ_[p]) : ℚ_[p]) from rfl]
    rw [← zp_smul (⟨_, hn⟩ : ℤ_[p])]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v l, Submodule.subset_span ⟨l, rfl⟩, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul n z _ hz => rw [map_zsmul]; exact Submodule.smul_of_tower_mem _ n hz

/-- `ℤ_p`-span inclusion from a global inclusion `γ V ⊆ U`. -/
theorem span_bc_ge (u v : Fin 4 → QuatAlg ℚ a b) (γ : QuatAlg ℚ a b)
    (h : ∀ z ∈ Submodule.span ℤ (Set.range v), γ * z ∈ Submodule.span ℤ (Set.range u)) :
    (Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range v) : Set (QuatAlg ℚ a b)))).map
        (LinearMap.mulLeft ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) γ)) ≤
      Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range u) : Set (QuatAlg ℚ a b))) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨γ * z, h z hz, by rw [map_mul]; rfl⟩

end Local

/-- `β₀ = (−3 − 2i − j)/4 ∈ J₂`, `nrd β₀ = 3/2`. -/
def β0 : (QuatAlg ℚ (-1) (-11))ˣ where
  val := ⟨-3 / 4, -1 / 2, -1 / 4, 0⟩
  inv := ⟨-1 / 2, 1 / 3, 1 / 6, 0⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

theorem span_v11_le_w2 : Submodule.span ℤ (Set.range v11) ≤ Submodule.span ℤ (Set.range w2) := by
  rw [Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  refine mem_span_of_eq w2 ((![![2, 0, -1, -1], ![0, 2, -1, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] :
    Fin 4 → Fin 4 → ℤ) l) ?_
  rw [sum_w2]
  fin_cases l <;> norm_num

theorem p2_local (p : ℕ) [Fact p.Prime] (hp : p = 2) :
    Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range w2) : Set (QuatAlg ℚ (-1) (-11)))) =
      (Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range v11) : Set (QuatAlg ℚ (-1) (-11))))).map
        (LinearMap.mulLeft ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) (β0 : QuatAlg ℚ (-1) (-11)))) := by
  refine le_antisymm (span_bc_le w2 v11 _
    ![![-9, 6, 3, -3], ![-6, 2, 2, -1], ![-11, 0, 4, 1], ![0, 11, -1, -7]] ((3 : ℕ) : ℚ)⁻¹ ?_ ?_)
    (span_bc_ge w2 v11 _ fun z hz => mul_mem_span_left _ v11 w2
      ![![4, -1, -3, -2], ![1, -7, 3, 1], ![11, 0, -9, -6], ![0, -11, 6, 2]] ?_ hz)
  · subst hp
    refine Padic.norm_rat_le_one ?_
    rw [Rat.inv_natCast_den]
    decide
  · intro k
    rw [sum_v11]
    simp only [β0]
    fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]
  · intro k
    rw [sum_w2]
    simp only [β0]
    fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]

theorem odd_local (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range w2) : Set (QuatAlg ℚ (-1) (-11)))) =
      Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range v11) : Set (QuatAlg ℚ (-1) (-11)))) := by
  refine le_antisymm ?_ (Submodule.span_mono (Set.image_mono span_v11_le_w2))
  have h := span_bc_le (p := p) w2 v11 1
    ![![1, 0, 1, 1], ![0, 1, 1, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]] ((2 : ℕ) : ℚ)⁻¹ ?_ ?_
  · rwa [map_one, LinearMap.mulLeft_one, Submodule.map_id] at h
  · refine Padic.norm_rat_le_one ?_
    rw [Rat.inv_natCast_den]
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by simpa using hd))
  · intro k
    rw [one_mul, sum_v11]
    fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]


/-- The idele `x₂` of the second class: `L_{x₂} = J₂` (item 43(d) with `S = {2}`). -/
theorem exists_x2 : ∃ x : (BHat (-1) (-11))ˣ, Submodule.span ℤ (Set.range w2) = finiteIdeleLattice O11 x := by
  have hfg : (Submodule.span ℤ (Set.range w2)).FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span ℚ (Submodule.span ℤ (Set.range w2) : Set (QuatAlg ℚ (-1) (-11))) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← O11.span_eq_top]
    exact Submodule.span_mono (fun z hz => span_v11_le_w2 hz)
  have hLO : ∀ y z : QuatAlg ℚ (-1) (-11), y ∈ Submodule.span ℤ (Set.range w2) → z ∈ O11.toSubalgebra →
      y * z ∈ Submodule.span ℤ (Set.range w2) :=
    fun y z hy hz => mul_mem_span_table w2 v11 w2 _ w2_table hy hz
  have hS : ∀ p ∈ ({⟨2, Nat.prime_two⟩} : Finset Nat.Primes),
      Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range w2) : Set (QuatAlg ℚ (-1) (-11)))) =
      (Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (O11.toSubalgebra : Set (QuatAlg ℚ (-1) (-11))))).map (LinearMap.mulLeft ℤ_[p]
          ((Units.map (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p])).toMonoidHom β0 :
            (QuatAlg ℚ_[p] (-1) (-11))ˣ) : QuatAlg ℚ_[p] (-1) (-11))) := by
    intro p hp
    have h2 : (p : ℕ) = 2 := by
      rw [Finset.eq_of_mem_singleton hp]
    rw [Units.coe_map]
    exact p2_local p h2
  have hS' : ∀ p : Nat.Primes, p ∉ ({⟨2, Nat.prime_two⟩} : Finset Nat.Primes) →
      Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (Submodule.span ℤ (Set.range w2) : Set (QuatAlg ℚ (-1) (-11)))) =
      Submodule.span ℤ_[p] (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p]) ''
        (O11.toSubalgebra : Set (QuatAlg ℚ (-1) (-11)))) := by
    intro p hp
    have h2 : (p : ℕ) ≠ 2 := fun h => hp (by
      have : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h
      rw [this]; exact Finset.mem_singleton_self _)
    exact odd_local p h2
  obtain ⟨x, -, -, hx⟩ := (classSet_right_ideals O11).2.2.2 _ hfg hsp hLO {⟨2, Nat.prime_two⟩}
    (fun p => Units.map (baseChange (-1) (-11) (algebraMap ℚ ℚ_[p])).toMonoidHom β0) hS hS'
  exact ⟨x, hx⟩

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

def rho (k : Fin 4) (g : Fin 4 → ZMod 4) : Fin 4 → ZMod 4 := fun r => ∑ l, g l * ((T11 l k r : ℤ) : ZMod 4)

def G1 : Finset (Fin 4 → ZMod 4) := {0, ![2, 2, 0, 0], ![0, 0, 2, 2], ![2, 2, 2, 2]}
def G2 : Finset (Fin 4 → ZMod 4) := {0, ![2, 0, 2, 2], ![0, 2, 2, 0], ![2, 2, 0, 2]}
def G3 : Finset (Fin 4 → ZMod 4) := {0, ![2, 0, 0, 2], ![0, 2, 2, 2], ![2, 2, 2, 0]}

-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem lemA : ∀ g : Fin 4 → ZMod 4, 2 • g ≠ 0 →
    ({0, g, 2 • g, 3 • g} : Finset (Fin 4 → ZMod 4)).card = 4 ∧
    ∃ k, rho k g ∉ ({0, g, 2 • g, 3 • g} : Finset (Fin 4 → ZMod 4)) := by decide

def E2 : Finset (Fin 4 → ZMod 4) := Finset.univ.filter fun g => 2 • g = 0

-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
theorem lemB : ∀ g ∈ E2, ∀ h ∈ E2, g ≠ 0 → h ≠ 0 → h ≠ g →
    ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4)).card = 4 ∧
    ((∀ k, rho k g ∈ ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4)) ∧
        rho k h ∈ ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4))) →
      ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4)) = G1 ∨ ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4)) = G2 ∨
        ({0, g, h, g + h} : Finset (Fin 4 → ZMod 4)) = G3) := by decide


theorem mem_E2 {g : Fin 4 → ZMod 4} : g ∈ E2 ↔ 2 • g = 0 := by simp [E2]

/-- Combinatorial classification of the residue sets. -/
theorem classify_residues (R : Set (Fin 4 → ZMod 4)) (hR : R.ncard = 4) (h0 : (0 : Fin 4 → ZMod 4) ∈ R)
    (hadd : ∀ g ∈ R, ∀ h ∈ R, g + h ∈ R) (hrho : ∀ g ∈ R, ∀ k, rho k g ∈ R) :
    R = ↑G1 ∨ R = ↑G2 ∨ R = ↑G3 := by
  have hfin : R.Finite := Set.finite_of_ncard_ne_zero (by rw [hR]; norm_num)
  have hnsmul : ∀ g ∈ R, ∀ n : ℕ, n • g ∈ R := by
    intro g hg n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul]; exact hadd _ ih _ hg
  have heq : ∀ S : Finset (Fin 4 → ZMod 4), S.card = 4 → (↑S : Set (Fin 4 → ZMod 4)) ⊆ R →
      (↑S : Set (Fin 4 → ZMod 4)) = R := by
    intro S hS hSR
    exact Set.eq_of_subset_of_ncard_le hSR (by rw [hR, Set.ncard_coe_finset, hS]) hfin
  have hA : ∀ g ∈ R, 2 • g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨hc, k, hk⟩ := lemA g hne
    have hS := heq _ hc (by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h0
      · exact hg
      · exact hnsmul g hg 2
      · exact hnsmul g hg 3)
    exact hk (by rw [← Finset.mem_coe, hS]; exact hrho g hg k)
  obtain ⟨g, hg, hg0⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hR]; norm_num) (0 : Fin 4 → ZMod 4)
  obtain ⟨h, hh, hh'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := ({0, g} : Set (Fin 4 → ZMod 4)))
    (t := R) (by rw [hR]; exact (Set.ncard_insert_le _ _).trans_lt (by rw [Set.ncard_singleton]; norm_num))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hh'
  obtain ⟨hh0, hhg⟩ := hh'
  obtain ⟨hc, hcl⟩ := lemB g (mem_E2.mpr (hA g hg)) h (mem_E2.mpr (hA h hh)) hg0 hh0 hhg
  have hS := heq _ hc (by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h0
      · exact hg
      · exact hh
      · exact hadd _ hg _ hh)
  have hcl' := hcl fun k => ⟨by rw [← Finset.mem_coe, hS]; exact hrho g hg k,
    by rw [← Finset.mem_coe, hS]; exact hrho h hh k⟩
  rw [← hS]
  rcases hcl' with h1 | h1 | h1 <;> rw [h1] <;> simp

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem f11_four (e : Fin 4 → ℤ) : f11 (fun k => 4 * e k) = (4 : ℚ) • f11 e := by
  simp only [f11, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk.injEq, smul_eq_mul]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

section Phi

variable (J : Submodule ℤ (QuatAlg ℚ (-1) (-11))) (hJ : ∀ z ∈ J, (4 : ℚ) • z ∈ O11.toSubalgebra)

/-- The residue map `J → (ℤ/4)⁴`, `z ↦ (coordinates of 4z) mod 4`. -/
noncomputable def phiJ : J.toAddSubgroup →+ (Fin 4 → ZMod 4) where
  toFun z := fun k => ((coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩ k : ℤ) : ZMod 4)
  map_zero' := by
    funext k
    rw [coord11_eq (c := 0) (by rw [f11_zero]; exact smul_zero _)]
    simp
  map_add' z z' := by
    funext k
    rw [coord11_eq (c := coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩ +
      coord11 ⟨(4 : ℚ) • (z' : QuatAlg ℚ (-1) (-11)), hJ z' z'.2⟩)
      (by rw [f11_add, ← coord11_spec, ← coord11_spec]; exact smul_add _ _ _)]
    simp

theorem phiJ_spec (z : J.toAddSubgroup) :
    (4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)) =
      f11 (coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩) ∧
    phiJ J hJ z = fun k => ((coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩ k : ℤ) : ZMod 4) :=
  ⟨coord11_spec (⟨_, hJ z z.2⟩ : O11.toSubalgebra), rfl⟩

theorem phiJ_eq_zero_iff (z : J.toAddSubgroup) :
    phiJ J hJ z = 0 ↔ (z : QuatAlg ℚ (-1) (-11)) ∈ O11.toSubalgebra := by
  set c := coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩
  have hc : (4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)) = f11 c := coord11_spec (⟨_, hJ z z.2⟩ : O11.toSubalgebra)
  constructor
  · intro h
    have hk : ∀ k, (4 : ℤ) ∣ c k := fun k => by
      have := congrFun h k
      exact_mod_cast int_dvd_of_zmod (n := 4) this
    choose e he using hk
    refine mem_O11.mpr ⟨e, ?_⟩
    have : (4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)) = (4 : ℚ) • f11 e := by
      rw [hc, ← f11_four]; congr 1; funext k; exact he k
    exact smul_right_injective _ (by norm_num : (4 : ℚ) ≠ 0) this
  · intro h
    obtain ⟨e, he⟩ := mem_O11.mp h
    have : c = fun k => 4 * e k := coord11_eq (by show (4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)) = _; rw [he, f11_four])
    funext k
    show ((c k : ℤ) : ZMod 4) = 0
    rw [this]
    push_cast
    rw [show (4 : ZMod 4) = 0 from rfl, zero_mul]

theorem phiJ_rho (hJO : ∀ y z, y ∈ J → z ∈ O11.toSubalgebra → y * z ∈ J) (z : J.toAddSubgroup) (k : Fin 4) :
    rho k (phiJ J hJ z) = phiJ J hJ ⟨(z : QuatAlg ℚ (-1) (-11)) * v11 k,
      hJO _ _ z.2 (Submodule.subset_span ⟨k, rfl⟩)⟩ := by
  set c := coord11 ⟨(4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)), hJ z z.2⟩
  have hc : (4 : ℚ) • (z : QuatAlg ℚ (-1) (-11)) = f11 c := coord11_spec (⟨_, hJ z z.2⟩ : O11.toSubalgebra)
  have hv : v11 k = f11 (Pi.single k 1) := by
    fin_cases k <;> ext <;> simp [f11]
  have h2 : coord11 ⟨(4 : ℚ) • ((z : QuatAlg ℚ (-1) (-11)) * v11 k),
      hJ _ (hJO _ _ z.2 (Submodule.subset_span ⟨k, rfl⟩))⟩ =
      fun r => ∑ i, ∑ l, c i * (Pi.single k 1 : Fin 4 → ℤ) l * T11 i l r := by
    refine coord11_eq ?_
    show (4 : ℚ) • ((z : QuatAlg ℚ (-1) (-11)) * v11 k) = _
    rw [← smul_mul_assoc, hc, hv, f11_mul]
  funext r
  show ∑ l, ((c l : ℤ) : ZMod 4) * ((T11 l k r : ℤ) : ZMod 4) = ((coord11 _ r : ℤ) : ZMod 4)
  rw [h2]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  push_cast
  rfl

end Phi

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem f11_sub (c d : Fin 4 → ℤ) : f11 c - f11 d = f11 (c - d) := by
  rw [eq_comm, eq_sub_iff_add_eq, ← f11_add, sub_add_cancel]

/-- An index-4 right `O₁₁`-ideal over `O₁₁` has one of three residue sets. -/
theorem residues_of_index (J : Submodule ℤ (QuatAlg ℚ (-1) (-11)))
    (hOJ : Subalgebra.toSubmodule O11.toSubalgebra ≤ J)
    (hJO : ∀ y z, y ∈ J → z ∈ O11.toSubalgebra → y * z ∈ J)
    (hidx : (Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup = 4) :
    ∃ G : Finset (Fin 4 → ZMod 4), (G = G1 ∨ G = G2 ∨ G = G3) ∧
      (∀ z ∈ J, ∃ c : Fin 4 → ℤ, (4 : ℚ) • z = f11 c ∧ (fun k => (c k : ZMod 4)) ∈ G) ∧
      (∀ c : Fin 4 → ℤ, (fun k => (c k : ZMod 4)) ∈ G → ∀ z, (4 : ℚ) • z = f11 c → z ∈ J) := by
  have hJ : ∀ z ∈ J, (4 : ℚ) • z ∈ O11.toSubalgebra := by
    intro z hz
    have h := AddSubgroup.nsmul_relIndex_mem (Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup
      (K := J.toAddSubgroup) (g := z) hz
    rw [hidx] at h
    have e : (4 : ℚ) • z = (4 : ℕ) • z := by
      rw [← Nat.cast_smul_eq_nsmul ℚ]; norm_num
    rw [e]
    exact h
  set R := Set.range (phiJ J hJ) with hRdef
  have hR : R.ncard = 4 := by
    have h1 : (phiJ J hJ).ker =
        (Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.addSubgroupOf J.toAddSubgroup := by
      ext z
      rw [AddMonoidHom.mem_ker, phiJ_eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      rfl
    have h2 := AddSubgroup.index_ker (phiJ J hJ)
    rw [h1, ← AddSubgroup.relIndex, hidx] at h2
    rw [hRdef, ← Nat.card_coe_set_eq, ← AddMonoidHom.coe_range]
    exact h2.symm
  have hcl := classify_residues R hR ⟨0, map_zero _⟩
    (by rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩; exact ⟨z + z', map_add _ _ _⟩)
    (by rintro _ ⟨z, rfl⟩ k; exact ⟨_, (phiJ_rho J hJ hJO z k).symm⟩)
  have key : ∀ G : Finset (Fin 4 → ZMod 4), R = ↑G →
      (∀ z ∈ J, ∃ c : Fin 4 → ℤ, (4 : ℚ) • z = f11 c ∧ (fun k => (c k : ZMod 4)) ∈ G) ∧
      (∀ c : Fin 4 → ℤ, (fun k => (c k : ZMod 4)) ∈ G → ∀ z, (4 : ℚ) • z = f11 c → z ∈ J) := by
    intro G hG
    refine ⟨fun z hz => ?_, fun c hc z hz => ?_⟩
    · refine ⟨coord11 ⟨_, hJ z hz⟩, coord11_spec (⟨_, hJ z hz⟩ : O11.toSubalgebra), ?_⟩
      rw [← Finset.mem_coe, ← hG]
      exact ⟨⟨z, hz⟩, rfl⟩
    · rw [← Finset.mem_coe, ← hG] at hc
      obtain ⟨z', hz'⟩ := hc
      have hc' := coord11_spec (⟨_, hJ z' z'.2⟩ : O11.toSubalgebra)
      set c' := coord11 (⟨_, hJ z' z'.2⟩ : O11.toSubalgebra)
      have hk : ∀ k, (4 : ℤ) ∣ c k - c' k := fun k => by
        have := congrFun hz' k
        have h4 := int_dvd_of_zmod (n := 4) (z := c k - c' k) (by
          push_cast
          rw [sub_eq_zero]
          exact this.symm)
        exact_mod_cast h4
      choose e he using hk
      have hzz : z - (z' : QuatAlg ℚ (-1) (-11)) ∈ O11.toSubalgebra := by
        refine mem_O11.mpr ⟨e, ?_⟩
        refine smul_right_injective _ (by norm_num : (4 : ℚ) ≠ 0) ?_
        show (4 : ℚ) • (z - (z' : QuatAlg ℚ (-1) (-11))) = (4 : ℚ) • f11 e
        rw [smul_sub, hz, show (4 : ℚ) • (z' : QuatAlg ℚ (-1) (-11)) = f11 c' from hc', f11_sub, ← f11_four]
        congr 1
        funext k
        exact he k
      have := J.add_mem (hOJ hzz) z'.2
      simpa using this
  rcases hcl with h | h | h
  exacts [⟨G1, Or.inl rfl, key G1 h⟩, ⟨G2, Or.inr (Or.inl rfl), key G2 h⟩, ⟨G3, Or.inr (Or.inr rfl), key G3 h⟩]

/-- From residues to an explicit lattice `γ T`. -/
theorem lattice_eq_of_residues (J : Submodule ℤ (QuatAlg ℚ (-1) (-11))) (G : Finset (Fin 4 → ZMod 4))
    (hJ1 : ∀ z ∈ J, ∃ c : Fin 4 → ℤ, (4 : ℚ) • z = f11 c ∧ (fun k => (c k : ZMod 4)) ∈ G)
    (hJ2 : ∀ c : Fin 4 → ℤ, (fun k => (c k : ZMod 4)) ∈ G → ∀ z, (4 : ℚ) • z = f11 c → z ∈ J)
    (t : Fin 4 → QuatAlg ℚ (-1) (-11)) (γ : (QuatAlg ℚ (-1) (-11))ˣ) (P Q : Fin 4 → Fin 4 → ℤ)
    (hP : ∀ k, ((γ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * v11 k = ∑ l, (P k l : ℚ) • t l)
    (hQ : ∀ l, (4 : ℚ) • ((γ : QuatAlg ℚ (-1) (-11)) * t l) = ∑ r, (Q l r : ℚ) • v11 r)
    (hPG : ∀ g ∈ G, ∀ l, ∑ k, g k * ((P k l : ℤ) : ZMod 4) = 0)
    (hQG : ∀ e : Fin 4 → ZMod 4, (fun r => ∑ l, e l * ((Q l r : ℤ) : ZMod 4)) ∈ G) :
    J = (Submodule.span ℤ (Set.range t)).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ (-1) (-11))) := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · intro hz
    obtain ⟨c, hc, hcG⟩ := hJ1 z hz
    have hm : ∀ l, (4 : ℤ) ∣ ∑ k, c k * P k l := fun l => by
      have := hPG _ hcG l
      exact_mod_cast int_dvd_of_zmod (n := 4) (z := ∑ k, c k * P k l) (by push_cast; exact this)
    choose m hm using hm
    refine ⟨((γ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * z, ?_, ?_⟩
    · refine mem_span_of_eq t m ?_
      have hz' : z = (1 / 4 : ℚ) • ∑ k, (c k : ℚ) • v11 k := by
        rw [← f11_eq_sum, ← hc, smul_smul]; norm_num
      rw [hz', mul_smul_comm, Finset.mul_sum]
      simp only [mul_smul_comm, hP, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul, ← Finset.mul_sum]
      congr 1
      have := hm l
      have hq : (∑ k, (c k : ℚ) * (P k l : ℚ)) = 4 * (m l : ℚ) := by exact_mod_cast this
      rw [hq]; ring
    · show (γ : QuatAlg ℚ (-1) (-11)) * (((γ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * z) = z
      rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨e, rfl⟩ := (mem_span4 t y).mp hy
    refine hJ2 (fun r => ∑ l, e l * Q l r) ?_ _ ?_
    · have := hQG (fun l => (e l : ZMod 4))
      simpa using this
    · show (4 : ℚ) • ((γ : QuatAlg ℚ (-1) (-11)) * ∑ k, (e k : ℚ) • t k) = _
      rw [f11_eq_sum, Finset.mul_sum, Finset.smul_sum]
      simp only [mul_smul_comm, smul_comm (4 : ℚ) (e _ : ℚ), hQ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_smul]
      push_cast
      rfl

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

/-- `γ₁ = (−1 + i)/2`, `J₁ = γ₁ O₁₁`. -/
def γ1 : (QuatAlg ℚ (-1) (-11))ˣ where
  val := ⟨-1 / 2, 1 / 2, 0, 0⟩
  inv := ⟨-1, -1, 0, 0⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

/-- `γ₃ = (−1 − 2i − j)/4`, `J₃ = γ₃ J₂`. -/
def γ3 : (QuatAlg ℚ (-1) (-11))ˣ where
  val := ⟨-1 / 4, -1 / 2, -1 / 4, 0⟩
  inv := ⟨-1 / 4, 1 / 2, 1 / 4, 0⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hPG1 : ∀ g ∈ G1, ∀ l, ∑ k, g k * (((![![-1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, -1, -1], ![0, 0, 1, -1]] :
    Fin 4 → Fin 4 → ℤ) k l : ℤ) : ZMod 4) = 0 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hQG1 : ∀ e : Fin 4 → ZMod 4, (fun r => ∑ l, e l * (((![![-2, 2, 0, 0], ![-2, -2, 0, 0], ![0, 0, -2, 2],
    ![0, 0, -2, -2]] : Fin 4 → Fin 4 → ℤ) l r : ℤ) : ZMod 4)) ∈ G1 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hPG2 : ∀ g ∈ G2, ∀ l, ∑ k, g k * (((![![2, 0, -1, -1], ![0, 2, -1, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] :
    Fin 4 → Fin 4 → ℤ) k l : ℤ) : ZMod 4) = 0 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hQG2 : ∀ e : Fin 4 → ZMod 4, (fun r => ∑ l, e l * (((![![2, 0, 2, 2], ![0, 2, 2, 0], ![0, 0, 4, 0],
    ![0, 0, 0, 4]] : Fin 4 → Fin 4 → ℤ) l r : ℤ) : ZMod 4)) ∈ G2 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hPG3 : ∀ g ∈ G3, ∀ l, ∑ k, g k * (((![![-6, 1, 4, 3], ![-1, 5, -2, -1], ![-11, 0, 8, 6],
    ![0, 11, -6, -3]] : Fin 4 → Fin 4 → ℤ) k l : ℤ) : ZMod 4) = 0 := by decide
-- `decide` over a finite certificate search space needs a deep recursion (no `native_decide`)
set_option maxRecDepth 100000 in
theorem hQG3 : ∀ e : Fin 4 → ZMod 4, (fun r => ∑ l, e l * (((![![16, -12, -8, 4], ![12, -6, -6, 2],
    ![22, 0, -12, -2], ![0, -22, 2, 10]] : Fin 4 → Fin 4 → ℤ) l r : ℤ) : ZMod 4)) ∈ G3 := by decide

/-- The three index-4 right ideals over `O₁₁`. -/
theorem index4_cases (J : Submodule ℤ (QuatAlg ℚ (-1) (-11)))
    (hOJ : Subalgebra.toSubmodule O11.toSubalgebra ≤ J)
    (hJO : ∀ y z, y ∈ J → z ∈ O11.toSubalgebra → y * z ∈ J)
    (hidx : (Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup = 4) :
    J = (Submodule.span ℤ (Set.range v11)).map (LinearMap.mulLeft ℤ (γ1 : QuatAlg ℚ (-1) (-11))) ∨
    J = (Submodule.span ℤ (Set.range w2)).map
      (LinearMap.mulLeft ℤ ((1 : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11))) ∨
    J = (Submodule.span ℤ (Set.range w2)).map (LinearMap.mulLeft ℤ (γ3 : QuatAlg ℚ (-1) (-11))) := by
  obtain ⟨G, hG, hJ1, hJ2⟩ := residues_of_index J hOJ hJO hidx
  rcases hG with rfl | rfl | rfl
  · refine Or.inl (lattice_eq_of_residues J G1 hJ1 hJ2 v11 γ1 _ _ ?_ ?_ hPG1 hQG1)
    · intro k; rw [sum_v11]; simp only [γ1]; fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]
    · intro l; rw [sum_v11]; simp only [γ1]; fin_cases l <;> norm_num [QuaternionAlgebra.mk_mul_mk]
  · refine Or.inr (Or.inl (lattice_eq_of_residues J G2 hJ1 hJ2 w2 1 _ _ ?_ ?_ hPG2 hQG2))
    · intro k; rw [sum_w2]; fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]
    · intro l; rw [sum_v11]; fin_cases l <;> norm_num [QuaternionAlgebra.mk_mul_mk]
  · refine Or.inr (Or.inr (lattice_eq_of_residues J G3 hJ1 hJ2 w2 γ3 _ _ ?_ ?_ hPG3 hQG3))
    · intro k; rw [sum_w2]; simp only [γ3]; fin_cases k <;> norm_num [QuaternionAlgebra.mk_mul_mk]
    · intro l; rw [sum_v11]; simp only [γ3]; fin_cases l <;> norm_num [QuaternionAlgebra.mk_mul_mk]

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem sqrt_121 : Real.sqrt (121 : ℝ) = 11 := by
  rw [show (121 : ℝ) = 11 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Every class of `O₁₁` is `[1]` or `[x₂]`. -/
theorem class_O11 (x2 : (BHat (-1) (-11))ˣ) (hx2 : Submodule.span ℤ (Set.range w2) = finiteIdeleLattice O11 x2)
    (x : (BHat (-1) (-11))ˣ) :
    (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x :
        classSet O11) = DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) 1 ∨
    (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x :
        classSet O11) = DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x2 := by
  obtain ⟨β, hle, hne, hidx⟩ := minkowski_class (by norm_num) (by norm_num) O11 x
  set J := (finiteIdeleLattice O11 x).map
    (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11))) with hJ
  set y := Units.map (finEmbed (-1) (-11)).toMonoidHom β⁻¹ * x * 1 with hy
  have hLy : finiteIdeleLattice O11 y = J := (classSet_right_ideals O11).2.1 β⁻¹ x 1 (Subgroup.one_mem _)
  have hxy : (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x :
      classSet O11) = DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
        (orderCompletionUnits O11) y :=
    DoubleCoset.eq.mpr ⟨_, ⟨β⁻¹, rfl⟩, 1, Subgroup.one_mem _, rfl⟩
  rw [hxy]
  -- the index is `1` or `4`
  have hsq : IsSquare ((Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup) := by
    rw [← hLy]
    exact index_square O11 y (by rw [hLy]; exact hle)
  have hle8 : (Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup < 9 := by
    rw [discriminant_O11] at hidx
    have hpi := Real.pi_gt_d2
    have h121 : (((121 : ℚ) : ℝ)) = 121 := by norm_num
    rw [h121, sqrt_121] at hidx
    have : ((Subalgebra.toSubmodule O11.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup : ℝ) < 9 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    exact_mod_cast this
  obtain ⟨r, hr⟩ := hsq
  have hr3 : r ≤ 2 := by
    by_contra hc
    rw [not_le] at hc
    have : 9 ≤ r * r := Nat.mul_le_mul hc hc
    omega
  interval_cases r
  · exact absurd hr hne
  · -- index 1
    left
    rw [← hxy]
    refine mk_eq_one_of_lattice O11 x β (le_antisymm (fun z hz => ?_) hle)
    exact AddSubgroup.relIndex_eq_one.mp hr hz
  · -- index 4
    have hJO : ∀ y' z, y' ∈ J → z ∈ O11.toSubalgebra → y' * z ∈ J := by
      rw [← hLy]; exact (classSet_right_ideals O11).1 y
    rcases index4_cases J hle hJO hr with h | h | h
    · left
      refine (classSet_right_ideals O11).2.2.1 y 1 γ1 ?_
      rw [hLy, h, finiteIdeleLattice_one]
      rfl
    · right
      refine (classSet_right_ideals O11).2.2.1 y x2 1 ?_
      rw [hLy, h, hx2]
    · right
      refine (classSet_right_ideals O11).2.2.1 y x2 γ3 ?_
      rw [hLy, h, hx2]

/-- The class set, the second class and the mass of `O₁₁`. -/
theorem O11_classes :
    Nat.card (classSet O11) = 2 ∧
    (∃ x : (BHat (-1) (-11))ˣ,
      (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x :
        classSet O11) ≠ DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
          (orderCompletionUnits O11) 1 ∧
      Nat.card (classStabilizer (orderCompletionUnits O11) x) = 6) ∧
    mass O11 = 5 / 12 := by
  classical
  obtain ⟨x2, hx2⟩ := exists_x2
  have hΓ2 := card_stab_x2 x2 hx2
  have hΓ1 : Nat.card (classStabilizer (orderCompletionUnits O11) 1) = 4 := by
    rw [classStabilizer_one, units_O11]
  set c1 : classSet O11 :=
    DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) 1 with hc1
  set c2 : classSet O11 :=
    DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O11) x2 with hc2
  have hne : c2 ≠ c1 := by
    intro h
    have h1 := card_classStabilizer_out O11 x2
    have h2 := card_classStabilizer_out O11 1
    rw [← hc2, h, hc1, h2] at h1
    rw [hΓ1, hΓ2] at h1
    exact absurd h1 (by norm_num)
  have hall : ∀ c : classSet O11, c = c1 ∨ c = c2 := by
    intro c
    induction c using Quotient.inductionOn with
    | h x => exact class_O11 x2 hx2 x
  refine ⟨Nat.card_eq_two_iff.mpr ⟨c1, c2, hne.symm, ?_⟩, ⟨x2, hne, hΓ2⟩, ?_⟩
  · ext c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact hall c
  · rw [mass, finsum_eq_sum_of_support_subset (s := {c1, c2}) _ (fun c _ => by
      rcases hall c with rfl | rfl <;> simp)]
    rw [Finset.sum_pair hne.symm]
    have e1 := card_classStabilizer_out O11 1
    have e2 := card_classStabilizer_out O11 x2
    rw [← hc1] at e1
    rw [← hc2] at e2
    rw [e1, e2, hΓ1, hΓ2]
    norm_num

end GL2TF.Quat.Inst

namespace GL2TF.Quat.Inst

theorem mass_O11 : mass O11 = 5 / 12 := O11_classes.2.2

end GL2TF.Quat.Inst

namespace GL2TF.Quat

open Inst

/-! ## §5 The instances -/

/-- **The Hurwitz order.** (a) `O_H` is maximal and `d(O_H) = 4`; (b) `|X(O_H)| = 1` and `|O_H^×| = 24`;
(c) `Mass(O_H) = 1/24`; (d) `Hyp.EichlerMass (−1) (−1) 2 O_H`. -/
@[tf_id "III.qcls.ex:hurwitz-order-mass"]
theorem hurwitz_order_mass :
    IsMaximalOrder hurwitzOrder ∧ discriminant hurwitzOrder = 4 ∧
    Nat.card (classSet hurwitzOrder) = 1 ∧ Nat.card (unitGroup hurwitzOrder) = 24 ∧
    mass hurwitzOrder = 1 / 24 ∧
    ∀ h : IsMaximalOrder hurwitzOrder, Hyp.EichlerMass (-1) (-1) 2 ⟨hurwitzOrder, h⟩ := by
  refine ⟨isMaximal_hurwitz, discriminant_hurwitz, Nat.card_eq_one_iff_exists.mpr ⟨_, classSet_hurwitz_eq⟩,
    units_hurwitz, mass_hurwitz, fun _ _ => ?_⟩
  show mass hurwitzOrder = _
  rw [mass_hurwitz, Nat.prime_two.primeFactors]
  norm_num

/-- **The instance `D = 11`** (exit), `O₁₁ = ℤ(1+j)/2 + ℤ(i+k)/2 + ℤj + ℤk ⊆ (−1, −11)_ℚ`: (a) `RamifiedExactly (−1) (−11) 11`;
(b) `O₁₁` is maximal and `d(O₁₁) = 121`; (c) `|X(O₁₁)| = 2`, `|Γ_1| = |O₁₁^×| = 4`, and the other class `[x]` has
`|Γ_x| = 6`; (d) `Mass(O₁₁) = 5/12`; (e) `Hyp.EichlerMass (−1) (−11) 11 O₁₁`. -/
@[tf_id "III.qcls.ex:eichler-mass-instance-d11"]
theorem eichler_mass_instance_d11 :
    RamifiedExactly (-1) (-11) 11 ∧
    (IsMaximalOrder (pizerOrderI (-11) (by norm_num)) ∧ discriminant (pizerOrderI (-11) (by norm_num)) = 121) ∧
    (Nat.card (classSet (pizerOrderI (-11) (by norm_num))) = 2 ∧
      Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) 1) = 4 ∧
      Nat.card (unitGroup (pizerOrderI (-11) (by norm_num))) = 4 ∧
      ∃ x : (BHat (-1) (-11))ˣ,
        (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
            (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) x : classSet (pizerOrderI (-11) (by norm_num))) ≠
          DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
            (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) 1 ∧
        Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) x) = 6) ∧
    mass (pizerOrderI (-11) (by norm_num)) = 5 / 12 ∧
    ∀ h : IsMaximalOrder (pizerOrderI (-11) (by norm_num)),
      Hyp.EichlerMass (-1) (-11) 11 ⟨pizerOrderI (-11) (by norm_num), h⟩ := by
  obtain ⟨hcard, hx, hmass⟩ := O11_classes
  refine ⟨ramified_d11, ⟨isMaximal_O11, discriminant_O11⟩,
    ⟨hcard, by rw [classStabilizer_one, units_O11], units_O11, hx⟩, hmass, fun _ _ => ?_⟩
  show mass O11 = _
  rw [hmass, (show Nat.Prime 11 by norm_num).primeFactors]
  norm_num

/-- Level structures of levels `2` and `3` on `O₁₁` exist, and `Mass(O₁₁(2; φ₂)) = 5/4`, `Mass(O₁₁(3; φ₃)) = 5/3`. -/
@[tf_id "III.qord.ex:eichler-order-d11-levels"]
theorem eichler_order_d11_levels :
    (∃ φ : LevelStructure (pizerOrderI (-11) (by norm_num)) 2, mass (eichlerOrder φ) = 5 / 4) ∧
    (∃ φ : LevelStructure (pizerOrderI (-11) (by norm_num)) 3, mass (eichlerOrder φ) = 5 / 3) := by
  refine ⟨⟨level11 2 X2 X2_table X2_one X2_surj, ?_⟩, ⟨level11 3 X3 X3_table X3_one X3_surj, ?_⟩⟩
  · rw [(mass_level_change (by norm_num) (by norm_num) O11 _).2, mass_O11,
      GL2TF.Explicit.dedekindPsi_nat_mul_prime.2.2 2 Nat.prime_two]
    norm_num
  · rw [(mass_level_change (by norm_num) (by norm_num) O11 _).2, mass_O11,
      GL2TF.Explicit.dedekindPsi_nat_mul_prime.2.2 3 Nat.prime_three]
    norm_num

/-- **Small instances** (stretch), Pizer's orders for `(a, b, D) = (−1, −3, 3), (−2, −5, 5), (−1, −7, 7), (−2, −13, 13)`:
(a) the order is maximal, `|X(O)| = 1`, and `|O^×| = 12, 6, 4, 2`; (b) `Hyp.EichlerMass a b D O`. -/
@[tf_id "III.qcls.ex:eichler-mass-instances-small"]
theorem eichler_mass_instances_small :
    (IsMaximalOrder (pizerOrderI (-3) (by norm_num)) ∧ Nat.card (classSet (pizerOrderI (-3) (by norm_num))) = 1 ∧
      Nat.card (unitGroup (pizerOrderI (-3) (by norm_num))) = 12 ∧
      ∀ h : IsMaximalOrder (pizerOrderI (-3) (by norm_num)),
        Hyp.EichlerMass (-1) (-3) 3 ⟨pizerOrderI (-3) (by norm_num), h⟩) ∧
    (IsMaximalOrder (pizerOrderII (-5) (by norm_num)) ∧ Nat.card (classSet (pizerOrderII (-5) (by norm_num))) = 1 ∧
      Nat.card (unitGroup (pizerOrderII (-5) (by norm_num))) = 6 ∧
      ∀ h : IsMaximalOrder (pizerOrderII (-5) (by norm_num)),
        Hyp.EichlerMass (-2) (-5) 5 ⟨pizerOrderII (-5) (by norm_num), h⟩) ∧
    (IsMaximalOrder (pizerOrderI (-7) (by norm_num)) ∧ Nat.card (classSet (pizerOrderI (-7) (by norm_num))) = 1 ∧
      Nat.card (unitGroup (pizerOrderI (-7) (by norm_num))) = 4 ∧
      ∀ h : IsMaximalOrder (pizerOrderI (-7) (by norm_num)),
        Hyp.EichlerMass (-1) (-7) 7 ⟨pizerOrderI (-7) (by norm_num), h⟩) ∧
    (IsMaximalOrder (pizerOrderII (-13) (by norm_num)) ∧ Nat.card (classSet (pizerOrderII (-13) (by norm_num))) = 1 ∧
      Nat.card (unitGroup (pizerOrderII (-13) (by norm_num))) = 2 ∧
      ∀ h : IsMaximalOrder (pizerOrderII (-13) (by norm_num)),
        Hyp.EichlerMass (-2) (-13) 13 ⟨pizerOrderII (-13) (by norm_num), h⟩) := by
  sorry

end GL2TF.Quat
