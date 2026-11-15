import AlgJL.Common.QuaternionNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Hilbert symbol by isotropy, split versus division, local values (Q2 U2, items 9–13)

Lean counterpart of `vol3/ch-iii-06-quatalg.tex` §2, first half (items 9–13 of `docs/sprints/Q2-plan.md` §1.2).

* `hilbertSymbol F a b ∈ {1, −1}` (Serre's definition by isotropy of `z² = a x² + b y²`), for every field `F` and all
  `a b : F` (for `a = 0` or `b = 0` the value is `1`: junk, the plan defines it for `a, b ∈ F^×` only).
  The local symbol `(a, b)_p` is written inline as `hilbertSymbol ℚ_[p] a b`; no separate constant.
* The symbol is noncomputable (an `∃` over `F³`, plan trap 2): every value used downstream comes from items 11–13.
* Item 10 is stated for `a, b ∈ F^×` on Mathlib's `ℍ[F, a, 0, b]`, with the reduced norm written out (the snippet's
  `B_F(a, b)` with `a, b ∈ F`); for integer `a, b` it is `QuatAlg F a b` and `nrd` definitionally.
* Exponents of `−1` are taken through `Int.natAbs` (only the parity matters); `ε(u) = (u − 1)/2`,
  `ω(u) = (u² − 1)/8` are written inline.

Owner: L1T (Q2).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open scoped Classical in
/-- The Hilbert symbol `(a, b)_F := 1` if `z² = a x² + b y²` has a solution `(x, y, z) ≠ 0` in `F³`, else `−1`
(Serre's definition). The local symbol `(a, b)_p` is `hilbertSymbol ℚ_[p] a b`. -/
@[tf_id "III.qalg.def:hilbert-symbol"]
noncomputable def hilbertSymbol (F : Type*) [Field F] (a b : F) : ℤ :=
  if ∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 then 1 else -1

private theorem hilbertSymbol_eq_one_iff {F : Type*} [Field F] (a b : F) : hilbertSymbol F a b = 1 ↔
    ∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' h⟩

private theorem hilbertSymbol_eq_neg_one_iff {F : Type*} [Field F] (a b : F) : hilbertSymbol F a b = -1 ↔
    ¬ ∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h h'⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

/-- Symmetry of the Hilbert symbol: `(a, b)_F = (b, a)_F` (swap `x` and `y`). Used by item 15 for the pairs
`(−2, −p)`, which have the shape `(2u, v)`. -/
@[tf_aux "III.qalg.lem:hilbert-symbol-symm"]
theorem hilbertSymbol_symm (F : Type*) [Field F] (a b : F) : hilbertSymbol F a b = hilbertSymbol F b a := by
  have key : ∀ a b : F, (∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) →
      (∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = b * x ^ 2 + a * y ^ 2) := by
    rintro a b ⟨x, y, z, hne, h⟩
    refine ⟨y, x, z, ?_, by rw [h]; ring⟩
    simp only [ne_eq, Prod.mk.injEq, not_and] at hne ⊢
    tauto
  by_cases h : ∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2
  · rw [(hilbertSymbol_eq_one_iff a b).2 h, (hilbertSymbol_eq_one_iff b a).2 (key a b h)]
  · rw [(hilbertSymbol_eq_neg_one_iff a b).2 h,
      (hilbertSymbol_eq_neg_one_iff b a).2 (fun h' => h (key b a h'))]

private theorem qmul_star {F : Type*} [Field F] (a b : F) (x : QuaternionAlgebra F a 0 b) :
    x * star x = algebraMap F _ (x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2) ∧
    star x * x = algebraMap F _ (x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2) := by
  constructor <;> ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> ring

private theorem qunit {F : Type*} [Field F] (a b : F) (x : QuaternionAlgebra F a 0 b)
    (h : x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 with hn
  have h1 : x * (n⁻¹ • star x) = 1 := by
    rw [mul_smul_comm, (qmul_star a b x).1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]
  have h2 : (n⁻¹ • star x) * x = 1 := by
    rw [smul_mul_assoc, (qmul_star a b x).2, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]
  exact ⟨⟨x, _, h1, h2⟩, rfl⟩

private theorem isotropic_iff {F : Type*} [Field F] (a b : F) :
    (∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
    ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧
        x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 = 0 := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨⟨z, x, y, 0⟩, ?_, by simp; linear_combination h⟩
    intro h0
    apply hne
    simp [QuaternionAlgebra.ext_iff] at h0
    simp [h0.1, h0.2.1, h0.2.2]
  · rintro ⟨q, hq, h⟩
    by_cases hn : q.imJ ^ 2 - a * q.imK ^ 2 = 0
    · by_cases h23 : q.imJ = 0 ∧ q.imK = 0
      · refine ⟨q.imI, 0, q.re, ?_, ?_⟩
        · intro h0
          simp only [Prod.mk.injEq] at h0
          exact hq (QuaternionAlgebra.ext h0.2.2 h0.1 h23.1 h23.2)
        · rw [h23.1, h23.2] at h; linear_combination h
      · refine ⟨q.imK, 0, q.imJ, ?_, by linear_combination hn⟩
        intro h0
        simp only [Prod.mk.injEq] at h0
        exact h23 ⟨h0.2.2, h0.1⟩
    · refine ⟨q.imI * q.imJ - q.re * q.imK, q.imJ ^ 2 - a * q.imK ^ 2,
        q.re * q.imJ - a * q.imI * q.imK, ?_, ?_⟩
      · intro h0; simp only [Prod.mk.injEq] at h0; exact hn h0.2.1
      · linear_combination (q.imJ ^ 2 - a * q.imK ^ 2) * h

private theorem equiv_of_basis {F : Type*} [Field F] {a b : F}
    (q : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) a 0 b)
    (hinj : ∀ c0 c1 c2 c3 : F, algebraMap F _ c0 + c1 • q.i + c2 • q.j + c3 • q.k = 0 →
      c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  have hi : Function.Injective q.liftHom := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨h0, h1, h2, h3⟩ := hinj x.re x.imI x.imJ x.imK hx
    ext <;> simp [h0, h1, h2, h3]
  have hs : Function.Surjective q.liftHom.toLinearMap := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi
    rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]
    simp
  exact ⟨AlgEquiv.ofBijective q.liftHom ⟨hi, hs⟩⟩

private theorem split_of_isotropic {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0)
    (hb : b ≠ 0) (x y z : F) (hne : (x, y, z) ≠ (0, 0, 0)) (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      rintro rfl
      subst hy
      have : z = 0 := by simpa using h
      exact hne (by simp [this])
    set s := z / x with hs
    have hsa : s ^ 2 = a := by
      rw [hs, div_pow, h, hy]; field_simp; ring
    have hs0 : s ≠ 0 := by rintro h0; rw [h0] at hsa; exact ha (by simpa using hsa.symm)
    let q : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) a 0 b :=
      { i := !![s, 0; 0, -s]
        j := !![0, b; 1, 0]
        k := !![s, 0; 0, -s] * !![0, b; 1, 0]
        i_mul_i := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [← hsa, pow_two]
        j_mul_j := by
          ext i j; fin_cases i <;> fin_cases j <;> simp
        i_mul_j := rfl
        j_mul_i := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm] }
    refine equiv_of_basis q fun c0 c1 c2 c3 hc => ?_
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e10 := congrFun (congrFun hc 1) 0
    have e11 := congrFun (congrFun hc 1) 1
    simp [q, Matrix.algebraMap_matrix_apply] at e00 e01 e10 e11
    have hc0 : c0 = 0 := by
      have : 2 * c0 = 0 := by linear_combination e00 + e11
      simpa [h2] using this
    have hc1 : c1 = 0 := by
      have : (2 * s) * c1 = 0 := by linear_combination e00 - e11
      simpa [h2, hs0] using this
    have hc3 : c3 = 0 := by
      have : (b * (2 * s)) * c3 = 0 := by linear_combination e01 - b * e10
      simpa [h2, hs0, hb] using this
    exact ⟨hc0, hc1, by linear_combination e10 + s * hc3, hc3⟩
  · obtain ⟨u, hu⟩ : ∃ u, u = z / y := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = x / y := ⟨_, rfl⟩
    have huv : u ^ 2 - a * v ^ 2 = b := by
      rw [hu, hv, div_pow, div_pow]; field_simp; linear_combination h
    let q : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) a 0 b :=
      { i := !![0, a; 1, 0]
        j := !![u, -(a * v); v, -u]
        k := !![0, a; 1, 0] * !![u, -(a * v); v, -u]
        i_mul_i := by
          ext i j; fin_cases i <;> fin_cases j <;> simp
        j_mul_j := by
          ext i j; fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination huv
        i_mul_j := rfl
        j_mul_i := by
          ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring }
    refine equiv_of_basis q fun c0 c1 c2 c3 hc => ?_
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e10 := congrFun (congrFun hc 1) 0
    have e11 := congrFun (congrFun hc 1) 1
    simp [q, Matrix.algebraMap_matrix_apply] at e00 e01 e10 e11
    have hc0 : c0 = 0 := by
      have : 2 * c0 = 0 := by linear_combination e00 + e11
      simpa [h2] using this
    have hc1 : c1 = 0 := by
      have : (2 * a) * c1 = 0 := by linear_combination e01 + a * e10
      simpa [h2, ha] using this
    have P : c2 * v + c3 * u = 0 := by linear_combination e10 - hc1
    have Q : c2 * u + c3 * a * v = 0 := by linear_combination e00 - hc0
    have hc3 : b * c3 = 0 := by linear_combination u * P - v * Q - c3 * huv
    have hc2 : b * c2 = 0 := by linear_combination u * Q - a * v * P - c2 * huv
    exact ⟨hc0, hc1, by simpa [hb] using hc2, by simpa [hb] using hc3⟩

/-- `F` a field with `2 ≠ 0`, `a, b ∈ F^×`: `(a, b)_F = 1` iff some `x ≠ 0` in `B_F(a, b) = ℍ[F, a, 0, b]` has
`nrd(x) = x₀² − a x₁² − b x₂² + ab x₃² = 0` iff `B_F(a, b) ≃ M₂(F)` as `F`-algebras. Otherwise every nonzero element of
`B_F(a, b)` is a unit. (Here `a, b ∈ F`, as in the snippet: the carrier is Mathlib's `ℍ[F, a, 0, b]` and the reduced
norm is written out; for `a, b ∈ ℤ` this is `QuatAlg F a b` and `nrd`, definitionally.) -/
@[tf_id "III.qalg.thm:split-iff-isotropic"]
theorem split_iff_isotropic {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    List.TFAE [hilbertSymbol F a b = 1,
      ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧
        x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 = 0,
      Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)] ∧
    (hilbertSymbol F a b = -1 → ∀ x : QuaternionAlgebra F a 0 b, x ≠ 0 → IsUnit x) := by
  refine ⟨?_, fun h x hx => ?_⟩
  · tfae_have 1 ↔ 2 := (hilbertSymbol_eq_one_iff a b).trans (isotropic_iff a b)
    tfae_have 3 → 2 := by
      rintro ⟨e⟩
      refine ⟨e.symm !![1, 0; 0, 0], ?_, ?_⟩
      · intro h0
        have := congrArg e h0
        simp only [AlgEquiv.apply_symm_apply, map_zero] at this
        have := congrFun (congrFun this 0) 0
        simp at this
      · by_contra hn
        have hu := (qunit a b _ hn).map e
        rw [AlgEquiv.apply_symm_apply, Matrix.isUnit_iff_isUnit_det] at hu
        simp [Matrix.det_fin_two] at hu
    tfae_have 2 → 3 := by
      intro h
      obtain ⟨x, y, z, hne, hxyz⟩ := (isotropic_iff a b).2 h
      exact split_of_isotropic h2 a b ha hb x y z hne hxyz
    tfae_finish
  · rw [hilbertSymbol_eq_neg_one_iff, isotropic_iff] at h
    exact qunit a b x fun hn => h ⟨x, hx, hn⟩

private theorem padic_sq_of_hensel {p : ℕ} [Fact p.Prime] (c k : ℤ_[p])
    (h : ‖k ^ 2 - c‖ < ‖2 * k‖ ^ 2) : ∃ s : ℤ_[p], s ^ 2 = c := by
  have hF : Polynomial.aeval k (Polynomial.X ^ 2 - Polynomial.C c) = k ^ 2 - c := by simp
  have hF' : Polynomial.aeval k (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C c)) = 2 * k := by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_sq,
      Polynomial.derivative_X, mul_one, map_mul, Polynomial.aeval_X]
    simp
  have h' : ‖Polynomial.aeval k (Polynomial.X ^ 2 - Polynomial.C c)‖ <
      ‖Polynomial.aeval k (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C c))‖ ^ 2 := by
    rw [hF, hF']; exact h
  obtain ⟨s, hs, -⟩ := hensels_lemma h'
  exact ⟨s, by simpa [sub_eq_zero] using hs⟩

/-- an integer `c` with `p ∣ k² - c`, `p ∤ 2k` is a square in `ℤ_p`. -/
private theorem padic_sq_of_int {p : ℕ} [Fact p.Prime] (c k : ℤ) (hc : (p : ℤ) ∣ k ^ 2 - c)
    (hk : ¬ (p : ℤ) ∣ 2 * k) : ∃ s : ℤ_[p], s ^ 2 = (c : ℤ_[p]) := by
  refine padic_sq_of_hensel (c : ℤ_[p]) (k : ℤ_[p]) ?_
  have h1 : ‖((k ^ 2 - c : ℤ) : ℤ_[p])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 hc
  have h2 : ‖((2 * k : ℤ) : ℤ_[p])‖ = 1 := by
    have := PadicInt.norm_le_one ((2 * k : ℤ) : ℤ_[p])
    have h3 : ¬ ‖((2 * k : ℤ) : ℤ_[p])‖ < 1 := fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd _).1 h)
    linarith [not_lt.1 h3]
  push_cast at h1 h2
  rw [h2]; simpa using h1

/-- For a prime `p ∤ 2ab`: `(a, b)_p = 1`. -/
@[tf_id "III.qalg.thm:hilbert-symbol-unramified"]
theorem hilbertSymbol_unramified (p : ℕ) [Fact p.Prime] (a b : ℤ) (h : ¬ (p : ℤ) ∣ 2 * a * b) :
    hilbertSymbol ℚ_[p] a b = 1 := by
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h' => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h' _) _)
  have hpa : ((a : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h' => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h' _) _)
  have hpb : ((b : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h' => h (dvd_mul_of_dvd_right h' _)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | h2
    · exact absurd (by rw [h2]; norm_num) hp2
    · exact h2
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C ((a : ZMod p)) * Polynomial.X ^ 2)
    (g := Polynomial.C ((b : ZMod p)) * Polynomial.X ^ 2 - 1)
    (by rw [Polynomial.degree_C_mul_X_pow 2 hpa]; rfl)
    (by rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
          rw [Polynomial.degree_C_mul_X_pow 2 hpb] <;> simp)
    hodd
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one] at hxy
  set X : ℤ := (x.val : ℤ)
  set Y : ℤ := (y.val : ℤ)
  have hdvd : (p : ℤ) ∣ 1 ^ 2 - (a * X ^ 2 + b * Y ^ 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [X, Y, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_one,
      Int.cast_natCast, ZMod.natCast_zmod_val]
    linear_combination -hxy
  obtain ⟨s, hs⟩ := padic_sq_of_int (a * X ^ 2 + b * Y ^ 2) 1 hdvd (by simpa using hp2)
  rw [hilbertSymbol_eq_one_iff]
  refine ⟨X, Y, s, ?_, ?_⟩
  · intro h0
    simp only [Prod.mk.injEq] at h0
    have : s = 0 := Subtype.ext h0.2.2
    rw [this] at hs
    have h3 : (p : ℤ) ∣ a * X ^ 2 + b * Y ^ 2 := by
      rw [← PadicInt.norm_int_lt_one_iff_dvd, ← hs]; simp
    exact hp2 (by
      have h4 : (p : ℤ) ∣ 1 := by
        have := dvd_add h3 hdvd
        ring_nf at this
        exact this
      exact dvd_trans h4 (one_dvd 2))
  · have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hs
    push_cast at this
    exact this

/-- Scaling a nontrivial solution of `z² = A x² + B y²` in `ℚ_p` to a primitive one in `ℤ_p`. -/
private theorem exists_primitive {p : ℕ} [Fact p.Prime] (A B : ℤ) (x y z : ℚ_[p])
    (hne : (x, y, z) ≠ (0, 0, 0)) (h : z ^ 2 = A * x ^ 2 + B * y ^ 2) :
    ∃ x' y' z' : ℤ_[p], z' ^ 2 = A * x' ^ 2 + B * y' ^ 2 ∧ (‖x'‖ = 1 ∨ ‖y'‖ = 1 ∨ ‖z'‖ = 1) := by
  have scale : ∀ w : ℚ_[p], w ≠ 0 → ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ → ‖z‖ ≤ ‖w‖ →
      ∃ x' y' z' : ℤ_[p], z' ^ 2 = A * x' ^ 2 + B * y' ^ 2 ∧ (x' : ℚ_[p]) = w⁻¹ * x ∧
        (y' : ℚ_[p]) = w⁻¹ * y ∧ (z' : ℚ_[p]) = w⁻¹ * z := by
    intro w hw hx hy hz
    have hn : ∀ t : ℚ_[p], ‖t‖ ≤ ‖w‖ → ‖w⁻¹ * t‖ ≤ 1 := by
      intro t ht
      rw [norm_mul, norm_inv]
      exact inv_mul_le_one_of_le₀ ht (norm_nonneg _)
    obtain ⟨x', cx⟩ : ∃ x' : ℤ_[p], (x' : ℚ_[p]) = w⁻¹ * x := ⟨⟨_, hn x hx⟩, rfl⟩
    obtain ⟨y', cy⟩ : ∃ y' : ℤ_[p], (y' : ℚ_[p]) = w⁻¹ * y := ⟨⟨_, hn y hy⟩, rfl⟩
    obtain ⟨z', cz⟩ : ∃ z' : ℤ_[p], (z' : ℚ_[p]) = w⁻¹ * z := ⟨⟨_, hn z hz⟩, rfl⟩
    refine ⟨x', y', z', ?_, cx, cy, cz⟩
    apply Subtype.ext
    push_cast
    rw [cx, cy, cz]
    linear_combination (w⁻¹ ^ 2) * h
  have one : ∀ w : ℚ_[p], w ≠ 0 → ‖w⁻¹ * w‖ = 1 := fun w hw => by rw [inv_mul_cancel₀ hw]; simp
  have nz : ∀ w : ℚ_[p], ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ → ‖z‖ ≤ ‖w‖ → w ≠ 0 := by
    intro w hx hy hz hw
    rw [hw, norm_zero] at hx hy hz
    exact hne (by simp [norm_le_zero_iff.1 hx, norm_le_zero_iff.1 hy, norm_le_zero_iff.1 hz])
  rcases le_total ‖y‖ ‖x‖ with hxy | hxy <;> rcases le_total ‖z‖ ‖x‖ with hxz | hxz <;>
    rcases le_total ‖z‖ ‖y‖ with hyz | hyz
  all_goals first
    | (have hw := nz x le_rfl (by linarith) (by linarith)
       obtain ⟨x', y', z', he, h1, -, -⟩ := scale x hw le_rfl (by linarith) (by linarith)
       exact ⟨x', y', z', he, Or.inl (by rw [PadicInt.norm_def, h1, one x hw])⟩)
    | (have hw := nz y (by linarith) le_rfl (by linarith)
       obtain ⟨x', y', z', he, -, h1, -⟩ := scale y hw (by linarith) le_rfl (by linarith)
       exact ⟨x', y', z', he, Or.inr (Or.inl (by rw [PadicInt.norm_def, h1, one y hw]))⟩)
    | (have hw := nz z (by linarith) (by linarith) le_rfl
       obtain ⟨x', y', z', he, -, -, h1⟩ := scale z hw (by linarith) (by linarith) le_rfl
       exact ⟨x', y', z', he, Or.inr (Or.inr (by rw [PadicInt.norm_def, h1, one z hw]))⟩)

private theorem hilbertSymbol_congr {F : Type*} [Field F] {a b a' b' : F}
    (h : (∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
      (∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a' * x ^ 2 + b' * y ^ 2)) :
    hilbertSymbol F a b = hilbertSymbol F a' b' := by
  by_cases h' : ∃ x y z : F, (x, y, z) ≠ (0, 0, 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2
  · rw [(hilbertSymbol_eq_one_iff a b).2 h', (hilbertSymbol_eq_one_iff a' b').2 (h.1 h')]
  · rw [(hilbertSymbol_eq_neg_one_iff a b).2 h',
      (hilbertSymbol_eq_neg_one_iff a' b').2 (fun h'' => h' (h.2 h''))]

/-- `(a t², b)_F = (a, b)_F` for `t ≠ 0`. -/
private theorem hilbertSymbol_mul_sq_left {F : Type*} [Field F] (a b t : F) (ht : t ≠ 0) :
    hilbertSymbol F (a * t ^ 2) b = hilbertSymbol F a b := by
  apply hilbertSymbol_congr
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨t * x, y, z, ?_, by rw [h]; ring⟩
    intro h0
    simp only [Prod.mk.injEq, mul_eq_zero, ht, false_or] at h0
    exact hne (by simp [h0.1, h0.2.1, h0.2.2])
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x / t, y, z, ?_, by rw [h]; field_simp⟩
    intro h0
    simp only [Prod.mk.injEq, div_eq_zero_iff, ht, or_false] at h0
    exact hne (by simp [h0.1, h0.2.1, h0.2.2])

/-- `(a, b)_F = (a, −ab)_F` for `a ≠ 0`. -/
private theorem hilbertSymbol_neg_mul {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) :
    hilbertSymbol F a b = hilbertSymbol F a (-(a * b)) := by
  apply hilbertSymbol_congr
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨z, y, a * x, ?_, by linear_combination (-a) * h⟩
    intro h0
    simp only [Prod.mk.injEq, mul_eq_zero, ha, false_or] at h0
    exact hne (by simp [h0.1, h0.2.1, h0.2.2])
  · rintro ⟨X, Y, Z, hne, h⟩
    refine ⟨Z, a * Y, a * X, ?_, by linear_combination (-a) * h⟩
    intro h0
    simp only [Prod.mk.injEq, mul_eq_zero, ha, false_or] at h0
    exact hne (by simp [h0.1, h0.2.1, h0.2.2])

private theorem toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (w : ℤ_[p]) :
    PadicInt.toZMod w = 0 ↔ ‖w‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/-- For odd `p` and `u, v` prime to `p`: `(pu, v)_p = (v/p)`. -/
private theorem hilbertSymbol_p_mul (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (u v : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v) :
    hilbertSymbol ℚ_[p] (((p : ℤ) * u : ℤ) : ℚ_[p]) (v : ℚ_[p]) = legendreSym p v := by
  have hv0 : ((v : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    have : p ∣ 2 := by exact_mod_cast h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  rcases legendreSym.eq_one_or_neg_one p hv0 with hL | hL
  · rw [hL, hilbertSymbol_eq_one_iff]
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hv0).1 hL
    have hr0 : r ≠ 0 := by rintro rfl; apply hv0; rw [hr]; ring
    have hdvd : (p : ℤ) ∣ (r.val : ℤ) ^ 2 - v := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hr]; ring
    have h2k : ¬ (p : ℤ) ∣ 2 * (r.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact mul_ne_zero h20 hr0
    obtain ⟨s, hs⟩ := padic_sq_of_int v (r.val : ℤ) hdvd h2k
    refine ⟨0, 1, s, by simp, ?_⟩
    have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hs
    push_cast at this
    rw [this]; ring
  · rw [hL, hilbertSymbol_eq_neg_one_iff]
    rintro ⟨x, y, z, hne, h⟩
    obtain ⟨x', y', z', he, hunit⟩ := exists_primitive ((p : ℤ) * u) v x y z hne h
    have he' := congrArg PadicInt.toZMod he
    simp only [map_pow, map_add, map_mul, map_intCast, Int.cast_mul, Int.cast_natCast] at he'
    simp only [map_natCast, ZMod.natCast_self, zero_mul, zero_add] at he'
    have hy : PadicInt.toZMod y' = 0 := by
      by_contra hy
      apply (legendreSym.eq_neg_one_iff p).1 hL
      refine ⟨PadicInt.toZMod z' / PadicInt.toZMod y', ?_⟩
      field_simp
      linear_combination -he'
    have hz : PadicInt.toZMod z' = 0 := by
      have : PadicInt.toZMod z' ^ 2 = 0 := by rw [he', hy]; ring
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have ny := (toZMod_eq_zero_iff y').1 hy
    have nz := (toZMod_eq_zero_iff z').1 hz
    rcases hunit with hx1 | hy1 | hz1
    · obtain ⟨y1, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd y').1 ny
      obtain ⟨z1, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z').1 nz
      have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have he2 : (p : ℤ_[p]) * z1 ^ 2 = u * x' ^ 2 + p * v * y1 ^ 2 := by
        apply mul_left_cancel₀ hp0
        push_cast at he
        linear_combination he
      have he3 := congrArg PadicInt.toZMod he2
      simp only [map_pow, map_add, map_mul, map_intCast, map_natCast, ZMod.natCast_self, zero_mul,
        add_zero] at he3
      have hx : PadicInt.toZMod x' = 0 := by
        have : (u : ZMod p) * PadicInt.toZMod x' ^ 2 = 0 := he3.symm
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd h1 hu0
        · exact pow_eq_zero_iff two_ne_zero |>.1 h1
      linarith [(toZMod_eq_zero_iff x').1 hx]
    · linarith
    · linarith

/-- `L^n = L^(n % 2)` when `L² = 1`. -/
private theorem pow_mod_two_of_sq_eq_one (L : ℤ) (h : L ^ 2 = 1) (n : ℕ) : L ^ n = L ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, h, one_pow, mul_one]

/-- Serre's formula for odd `p`: for `a = p^α u`, `b = p^β v` with `u, v ∈ ℤ` prime to `p`,
`(a, b)_p = (−1)^{αβ(p−1)/2} (u/p)^β (v/p)^α`. -/
@[tf_id "III.qalg.thm:hilbert-symbol-odd"]
theorem hilbertSymbol_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (α β : ℕ) (u v : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) :
    hilbertSymbol ℚ_[p] (((p : ℤ) ^ α * u : ℤ) : ℚ_[p]) (((p : ℤ) ^ β * v : ℤ) : ℚ_[p]) =
      (-1) ^ (α * β * ((p - 1) / 2)) * legendreSym p u ^ β * legendreSym p v ^ α := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hv0 : ((v : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsplit : ∀ (α : ℕ) (w : ℤ), ((((p : ℤ) ^ α * w : ℤ)) : ℚ_[p]) =
      (((p : ℤ) ^ (α % 2) * w : ℤ) : ℚ_[p]) * ((p : ℚ_[p]) ^ (α / 2)) ^ 2 := by
    intro α w
    push_cast
    conv_lhs => rw [← Nat.mod_add_div α 2]
    rw [pow_add, pow_mul]; ring
  rw [hsplit α u, hilbertSymbol_mul_sq_left _ _ _ (pow_ne_zero _ hp0), hilbertSymbol_symm, hsplit β v,
    hilbertSymbol_mul_sq_left _ _ _ (pow_ne_zero _ hp0), hilbertSymbol_symm]
  have hLu := legendreSym.sq_one p hu0
  have hLv := legendreSym.sq_one p hv0
  rw [pow_mod_two_of_sq_eq_one _ hLu β, pow_mod_two_of_sq_eq_one _ hLv α,
    pow_mod_two_of_sq_eq_one (-1) (by norm_num) (α * β * ((p - 1) / 2))]
  have hmod : α * β * ((p - 1) / 2) % 2 = (α % 2) * (β % 2) * ((p - 1) / 2) % 2 := by
    simp [Nat.mul_mod]
  rw [hmod]
  have hp2' : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  rcases Nat.mod_two_eq_zero_or_one α with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one β with hb | hb <;>
    rw [ha, hb]
  · -- (0, 0)
    simp only [pow_zero, one_mul, zero_mul, Nat.zero_mod, mul_one]
    apply hilbertSymbol_unramified
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact hp2' h
      · exact hu h
    · exact hv h
  · -- (0, 1)
    simp only [pow_zero, one_mul, zero_mul, Nat.zero_mod, pow_one, mul_one]
    rw [hilbertSymbol_symm]
    exact_mod_cast hilbertSymbol_p_mul p hp v u hv hu
  · -- (1, 0)
    simp only [pow_zero, one_mul, zero_mul, Nat.zero_mod, pow_one, mul_one, mul_zero]
    exact_mod_cast hilbertSymbol_p_mul p hp u v hu hv
  · -- (1, 1)
    simp only [pow_one, one_mul]
    have hpu : ((((p : ℤ) * u : ℤ)) : ℚ_[p]) ≠ 0 := by
      have hu' : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
      push_cast; exact mul_ne_zero hp0 (by exact_mod_cast hu')
    rw [hilbertSymbol_neg_mul _ _ hpu]
    have e : -((((p : ℤ) * u : ℤ) : ℚ_[p]) * (((p : ℤ) * v : ℤ) : ℚ_[p])) =
        ((-(u * v) : ℤ) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 := by push_cast; ring
    rw [e, hilbertSymbol_symm, hilbertSymbol_mul_sq_left _ _ _ hp0, hilbertSymbol_symm,
      hilbertSymbol_p_mul p hp u (-(u * v)) hu (by
        rw [dvd_neg]; intro h
        rcases hpZ.dvd_or_dvd h with h | h
        · exact hu h
        · exact hv h)]
    rw [show -(u * v) = (-1) * u * v by ring, legendreSym.mul, legendreSym.mul,
      legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp))]
    have hk : (p - 1) / 2 = p / 2 := by
      have := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp); omega
    rw [hk, ← pow_mod_two_of_sq_eq_one (-1) (by norm_num) (p / 2)]

/-- A unit of `ℤ_2` is odd modulo `8`. -/
private theorem unit_odd_mod_eight (w : ℤ_[2]) (hw : ‖w‖ = 1) :
    (PadicInt.toZModPow 3 w : ZMod 8).val % 2 = 1 := by
  by_contra hc
  set k := (PadicInt.toZModPow 3 w : ZMod 8).val with hk
  have hk2 : 2 ∣ k := by omega
  have hmem : w - (k : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast]
    exact sub_eq_zero.2 (ZMod.natCast_zmod_val _).symm
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  have h2w : (2 : ℤ_[2]) ∣ w := by
    have h1 : (2 : ℤ_[2]) ∣ (k : ℤ_[2]) := by
      have := Nat.cast_dvd_cast (α := ℤ_[2]) hk2
      simpa using this
    have h2 : (2 : ℤ_[2]) ∣ ((2 : ℕ) : ℤ_[2]) ^ 3 := by
      exact dvd_pow (by norm_num) (by norm_num)
    have := dvd_add (dvd_trans h2 hmem) h1
    simpa using this
  have := (PadicInt.norm_lt_one_iff_dvd w).2 (by exact_mod_cast h2w)
  linarith

private theorem two_adic_neg (A B : ℤ) (r s : ℤ) (hr : A % 8 = r) (hs : B % 8 = s)
    (h8 : ∀ x y z : ZMod 8, (x.val % 2 = 1 ∨ y.val % 2 = 1 ∨ z.val % 2 = 1) →
      z ^ 2 ≠ (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2) :
    hilbertSymbol ℚ_[2] A B = -1 := by
  rw [hilbertSymbol_eq_neg_one_iff]
  rintro ⟨x, y, z, hne, h⟩
  obtain ⟨x', y', z', he, hu⟩ := exists_primitive A B x y z hne h
  have hA : ((A : ℤ) : ZMod 8) = (r : ZMod 8) := by
    rw [← hr]; simpa using (ZMod.intCast_mod A 8).symm
  have hB : ((B : ℤ) : ZMod 8) = (s : ZMod 8) := by
    rw [← hs]; simpa using (ZMod.intCast_mod B 8).symm
  have he' := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) he
  simp only [map_pow, map_add, map_mul, map_intCast] at he'
  refine h8 (PadicInt.toZModPow 3 x') (PadicInt.toZModPow 3 y') (PadicInt.toZModPow 3 z') ?_ ?_
  · rcases hu with h1 | h1 | h1
    · exact Or.inl (unit_odd_mod_eight x' h1)
    · exact Or.inr (Or.inl (unit_odd_mod_eight y' h1))
    · exact Or.inr (Or.inr (unit_odd_mod_eight z' h1))
  · rw [← hA, ← hB]; exact he'

private theorem two_adic_pos (A B x y : ℤ) (h : (A * (x * x) + B * (y * y)) % 8 = 1) :
    hilbertSymbol ℚ_[2] A B = 1 := by
  have hdvd : ((2 : ℕ) : ℤ) ^ 3 ∣ 1 ^ 2 - (A * x ^ 2 + B * y ^ 2) := by
    have : (1 ^ 2 - (A * x ^ 2 + B * y ^ 2)) % 8 = 0 := by
      have : A * x ^ 2 + B * y ^ 2 = A * (x * x) + B * (y * y) := by ring
      omega
    exact Int.dvd_of_emod_eq_zero (by simpa using this)
  have hn := (PadicInt.norm_int_le_pow_iff_dvd (p := 2)).2 hdvd
  obtain ⟨s, hs⟩ := padic_sq_of_hensel (p := 2) ((A * x ^ 2 + B * y ^ 2 : ℤ) : ℤ_[2]) 1 (by
    have h2 : ‖(2 : ℤ_[2]) * 1‖ = 2⁻¹ := by
      rw [mul_one]; exact_mod_cast PadicInt.norm_p (p := 2)
    rw [h2]
    have he : (1 : ℤ_[2]) ^ 2 - ((A * x ^ 2 + B * y ^ 2 : ℤ) : ℤ_[2]) =
        ((1 ^ 2 - (A * x ^ 2 + B * y ^ 2) : ℤ) : ℤ_[2]) := by push_cast; ring
    rw [he]
    calc _ ≤ _ := hn
      _ < (2⁻¹) ^ 2 := by norm_num)
  rw [hilbertSymbol_eq_one_iff]
  refine ⟨x, y, s, ?_, ?_⟩
  · intro h0
    simp only [Prod.mk.injEq] at h0
    have h00 : s = 0 := Subtype.ext h0.2.2
    rw [h00] at hs
    have hc' : ((A * x ^ 2 + B * y ^ 2 : ℤ) : ℤ_[2]) = 0 := by rw [← hs]; ring
    have hc : A * x ^ 2 + B * y ^ 2 = 0 := by exact_mod_cast hc' 
    have : A * (x * x) + B * (y * y) = 0 := by linear_combination hc
    omega
  · have := congrArg ((↑) : ℤ_[2] → ℚ_[2]) hs
    push_cast at this
    exact this

private theorem neg_one_pow_natAbs (n : ℤ) : (-1 : ℤ) ^ n.natAbs = if n % 2 = 0 then 1 else -1 := by
  split_ifs with h
  · exact Even.neg_one_pow (Int.natAbs_even.2 (Int.even_iff.2 h))
  · exact Odd.neg_one_pow (Int.natAbs_odd.2 (Int.odd_iff.2 (by omega)))

private theorem omega_parity (u : ℤ) (hu : u % 2 = 1) :
    ((u ^ 2 - 1) / 8) % 2 = if u % 8 = 3 ∨ u % 8 = 5 then 1 else 0 := by
  have h16 : u ^ 2 % 16 = (u % 16) * (u % 16) % 16 := by rw [sq, Int.mul_emod]
  have h0 : 0 ≤ u % 16 := Int.emod_nonneg _ (by norm_num)
  have h1 : u % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
  have h8 : u % 8 = u % 16 % 8 := by omega
  generalize u % 16 = r at h16 h0 h1 h8
  interval_cases r <;> norm_num at h16 h8 ⊢ <;> omega

private theorem rhs_one (u v : ℤ) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    (-1 : ℤ) ^ ((u - 1) / 2 * ((v - 1) / 2)).natAbs = if u % 4 = 3 ∧ v % 4 = 3 then -1 else 1 := by
  rw [neg_one_pow_natAbs, Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one ((u - 1) / 2) with h1 | h1 <;>
    rcases Int.emod_two_eq_zero_or_one ((v - 1) / 2) with h2 | h2 <;>
    rw [h1, h2] <;> norm_num <;> omega

private theorem rhs_two (u v : ℤ) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    (-1 : ℤ) ^ ((u - 1) / 2 * ((v - 1) / 2) + (u ^ 2 - 1) / 8).natAbs =
      if ((u % 4 = 3 ∧ v % 4 = 3) ↔ (u % 8 = 3 ∨ u % 8 = 5)) then 1 else -1 := by
  rw [neg_one_pow_natAbs, Int.add_emod, Int.mul_emod, omega_parity u hu]
  rcases Int.emod_two_eq_zero_or_one ((u - 1) / 2) with h1 | h1 <;>
    rcases Int.emod_two_eq_zero_or_one ((v - 1) / 2) with h2 | h2 <;>
    rw [h1, h2] <;> split_ifs <;> norm_num <;> omega

/-- The cases `v₂(a) + v₂(b) ≤ 1` at `p = 2`: for odd `u, v`, `(u, v)_2 = (−1)^{ε(u)ε(v)}` and
`(u, 2v)_2 = (−1)^{ε(u)ε(v) + ω(u)}`, with `ε(u) = (u − 1)/2`, `ω(u) = (u² − 1)/8` (only their parity matters). -/
@[tf_id "III.qalg.thm:hilbert-symbol-two"]
theorem hilbertSymbol_two (u v : ℤ) (hu : Odd u) (hv : Odd v) :
    hilbertSymbol ℚ_[2] u v = (-1) ^ ((u - 1) / 2 * ((v - 1) / 2)).natAbs ∧
    hilbertSymbol ℚ_[2] u ((2 * v : ℤ) : ℚ_[2]) =
      (-1) ^ ((u - 1) / 2 * ((v - 1) / 2) + (u ^ 2 - 1) / 8).natAbs := by
  have hu2 : u % 2 = 1 := Int.odd_iff.1 hu
  have hv2 : v % 2 = 1 := Int.odd_iff.1 hv
  rw [rhs_one u v hu2 hv2, rhs_two u v hu2 hv2]
  have hu8 : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
  have hv8 : v % 8 = 1 ∨ v % 8 = 3 ∨ v % 8 = 5 ∨ v % 8 = 7 := by omega
  rcases hu8 with hu8 | hu8 | hu8 | hu8 <;> rcases hv8 with hv8 | hv8 | hv8 | hv8 <;>
  · have h2v : (2 * v) % 8 = (2 * (v % 8)) % 8 := by omega
    rw [hv8] at h2v
    norm_num at h2v
    refine ⟨?_, ?_⟩
    all_goals first
      | rw [ite_eq_left (by omega)]
      | rw [ite_eq_right (by omega)]
    all_goals first
      | exact two_adic_pos _ _ 0 1 (by omega)
      | exact two_adic_pos _ _ 1 0 (by omega)
      | exact two_adic_pos _ _ 1 1 (by omega)
      | exact two_adic_pos _ _ 2 1 (by omega)
      | exact two_adic_pos _ _ 1 2 (by omega)
      | exact two_adic_neg _ _ _ _ hu8 hv8 (by decide +kernel)
      | exact two_adic_neg _ _ _ _ hu8 h2v (by decide +kernel)

end GL2TF.Quat
