import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.SymPower
import AlgJL.VolIII.P2.LocalStructure
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Splittings and the coefficient modules `V_k` (Q3 U1, items 7–10)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §1, end (items 7–10 of `docs/sprints/Q3-plan.md` §1.2).

Design (plan §1.1 item 1, user decision Q3-U3):
* a *splitting* of `B = (a, b)_ℚ` over a field `K` of characteristic `0` is a `ℚ`-algebra homomorphism
  `s : B →ₐ[ℚ] M₂(K)` (data, no Prop); `ρ_k^s(γ) := ρ_{k−2}(s(γ))` on `V_{k−2}(K)` (`k − 2` is truncated subtraction:
  for `k < 2` the module is `V_0`; theorems that need `k ≥ 2` say so);
* model (c) (`standardSplitting`) needs `s₀ ∈ K` with `s₀² = a`; model (a) (`ellAdicSplitting`) composes Q2's local
  splitting `ι_ℓ` (`III.qalg.thm:maximal-order-local-split`, chosen by `Classical.choose`) with `B → B_ℓ`.

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-- A splitting of `B = (a, b)_ℚ` over a field `K` (of characteristic `0`): a `ℚ`-algebra homomorphism `B → M₂(K)`. -/
@[tf_id "III.qform.def:splitting"]
abbrev Splitting (K : Type*) [Field K] [CharZero K] (a b : ℤ) : Type _ :=
  QuatAlg ℚ a b →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K

/-- The coefficient representation `ρ_k^s(γ) := ρ_{k−2}(s(γ)) ∈ End_K(V_{k−2}(K))` of a splitting `s`. -/
@[tf_id "III.qform.def:splitting-representation"]
noncomputable def splitRep {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b) (k : ℕ)
    (γ : QuatAlg ℚ a b) : Module.End K (symPowerModule K (k - 2)) :=
  symPowerAction K (k - 2) (s γ)

theorem splitting_trace_aux {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b)
    (u v : QuatAlg ℚ a b) (c : ℚ) (hc : c ≠ 0) (h1 : u * v * v = c • u) (h2 : v * u * v = -(u * v * v)) :
    (s u).trace = 0 := by
  have h3 : (s (u * v * v)).trace = 0 := by
    have e1 : (s (u * v * v)).trace = (s (v * u * v)).trace := by
      simp only [map_mul]
      rw [Matrix.trace_mul_comm, ← mul_assoc]
    rw [h2, map_neg, Matrix.trace_neg] at e1
    linear_combination e1 / 2
  rw [h1, map_smul, Matrix.trace_smul, smul_eq_zero] at h3
  exact h3.resolve_left hc

theorem det_fin_two_eq_trace {K : Type*} [Field K] [CharZero K] (M : Matrix (Fin 2) (Fin 2) K) :
    M.det = (M.trace ^ 2 - (M * M).trace) / 2 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- For `a, b ≠ 0`, every splitting `s` and `x ∈ B`: `det s(x) = nrd x`, `tr s(x) = trd x`, `s(x̄) = adj s(x)`; and `s`
is injective. -/
@[tf_id "III.qform.lem:splitting-norm-trace"]
theorem splitting_norm_trace {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : Splitting K a b) :
    (∀ x : QuatAlg ℚ a b, (s x).det = ((nrd x : ℚ) : K)) ∧
    (∀ x : QuatAlg ℚ a b, (s x).trace = ((trd x : ℚ) : K)) ∧
    (∀ x : QuatAlg ℚ a b, s (star x) = (s x).adjugate) ∧
    Function.Injective s := by
  set i : QuatAlg ℚ a b := ⟨0, 1, 0, 0⟩ with hi
  set j : QuatAlg ℚ a b := ⟨0, 0, 1, 0⟩ with hj
  set k : QuatAlg ℚ a b := ⟨0, 0, 0, 1⟩ with hk
  have ha' : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have ti : (s i).trace = 0 :=
    splitting_trace_aux s i j b hb' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tj : (s j).trace = 0 :=
    splitting_trace_aux s j i a ha' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tk : (s k).trace = 0 :=
    splitting_trace_aux s k i a ha' (by ext <;> simp [hi, hk]) (by ext <;> simp [hi, hk])
  have hdec : ∀ x : QuatAlg ℚ a b,
      x = algebraMap ℚ (QuatAlg ℚ a b) x.re + x.imI • i + x.imJ • j + x.imK • k := by
    intro x
    ext <;> simp [hi, hj, hk, QuaternionAlgebra.algebraMap_eq]
  have htr : ∀ x : QuatAlg ℚ a b, (s x).trace = ((trd x : ℚ) : K) := by
    intro x
    conv_lhs => rw [hdec x]
    simp only [map_add, map_smul, AlgHom.commutes, Matrix.trace_add, Matrix.trace_smul, ti, tj, tk, smul_zero,
      add_zero]
    simp [trd, Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]
  have hstar : ∀ x : QuatAlg ℚ a b, star x = algebraMap ℚ (QuatAlg ℚ a b) (trd x) - x := by
    intro x
    ext <;> simp [trd, QuaternionAlgebra.algebraMap_eq] <;> ring
  refine ⟨fun x => ?_, htr, fun x => ?_, ?_⟩
  · rw [det_fin_two_eq_trace, ← map_mul, htr, htr]
    have hq : nrd x = (trd x ^ 2 - trd (x * x)) / 2 := by
      simp only [nrd, trd, QuaternionAlgebra.re_mul]
      ring
    rw [hq]
    push_cast
    ring
  · have h := htr x
    rw [Matrix.trace_fin_two] at h
    rw [hstar, map_sub, AlgHom.commutes]
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [Matrix.adjugate_fin_two, Matrix.algebraMap_eq_diagonal, Matrix.diagonal, ← h]
  · refine (injective_iff_map_eq_zero s).mpr fun x hx => ?_
    have h0 : ∀ y : QuatAlg ℚ a b, trd (x * y) = 0 := by
      intro y
      have h := htr (x * y)
      rw [map_mul, hx, zero_mul, Matrix.trace_zero] at h
      exact_mod_cast h.symm
    clear hdec
    have e1 : (2 : ℚ) * x.re = 0 := by refine Eq.trans ?_ (h0 1); simp [trd]
    have e2 : ((2 : ℚ) * a) * x.imI = 0 := by refine Eq.trans ?_ (h0 i); simp [trd, hi]; ring
    have e3 : ((2 : ℚ) * b) * x.imJ = 0 := by refine Eq.trans ?_ (h0 j); simp [trd, hj]; ring
    have e4 : ((-2 : ℚ) * a * b) * x.imK = 0 := by refine Eq.trans ?_ (h0 k); simp [trd, hk]; ring
    ext
    · exact (mul_eq_zero.mp e1).resolve_left two_ne_zero
    · exact (mul_eq_zero.mp e2).resolve_left (mul_ne_zero two_ne_zero ha')
    · exact (mul_eq_zero.mp e3).resolve_left (mul_ne_zero two_ne_zero hb')
    · exact (mul_eq_zero.mp e4).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) ha') hb')

/-- The images `diag(s₀, −s₀)`, `(0 b; 1 0)`, `(0 bs₀; −s₀ 0)` of `i`, `j`, `k` under model (c), as a quaternion basis
of `M₂(K)` (B-only plumbing of `III.qform.def:standard-splitting`). -/
@[tf_aux "III.qform.def:standard-splitting-basis"]
noncomputable def standardSplittingBasis (K : Type*) [Field K] [CharZero K] (a b : ℤ) (s₀ : K)
    (hs₀ : s₀ ^ 2 = (a : K)) : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) (a : ℚ) 0 (b : ℚ) where
  i := !![s₀, 0; 0, -s₀]
  j := !![0, (b : K); 1, 0]
  k := !![0, (b : K) * s₀; -s₀, 0]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hs₀, sq, Rat.smul_def]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Rat.smul_def]
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Model (c): for `s₀ ∈ K` with `s₀² = a`, the splitting `1 ↦ I`, `i ↦ diag(s₀, −s₀)`, `j ↦ (0 b; 1 0)`,
`k ↦ (0 bs₀; −s₀ 0)`. -/
@[tf_id "III.qform.def:standard-splitting"]
noncomputable def standardSplitting (K : Type*) [Field K] [CharZero K] (a b : ℤ) (s₀ : K) (hs₀ : s₀ ^ 2 = (a : K)) :
    Splitting K a b :=
  (standardSplittingBasis K a b s₀ hs₀).liftHom

/-- Model (a): for a maximal order `O` of `B`, `B` ramified exactly at the primes dividing `D`, and a prime `ℓ ∤ D`,
the splitting `s_ℓ := ι_ℓ ∘ (B → B_ℓ)` over `ℚ_ℓ`, with `ι_ℓ : B_ℓ ≃ M₂(ℚ_ℓ)` the isomorphism of
`III.qalg.thm:maximal-order-local-split` (`ι_ℓ(O_ℓ) = M₂(ℤ_ℓ)`). -/
@[tf_id "III.qform.def:ell-adic-splitting"]
noncomputable def ellAdicSplitting {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hD : RamifiedExactly a b D) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓD : ¬ ℓ ∣ D) : Splitting ℚ_[ℓ] a b :=
  RingHom.toRatAlgHom
    ((Classical.choose (maximalOrder_local_split O hD ℓ hℓD)).toRingEquiv.toRingHom.comp
      (baseChange a b (algebraMap ℚ ℚ_[ℓ])))

end GL2TF.Quat
