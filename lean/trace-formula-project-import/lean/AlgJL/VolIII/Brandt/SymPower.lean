import AlgJL.Meta.Tag
import AlgJL.VolIII.P1.Arith
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Symmetric powers `V_m = Sym^m` of the standard representation of `M₂(K)` (Q3 U1, items 1–6)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §1 (items 1–6 and 4a of `docs/sprints/Q3-plan.md` §1.2).

Design (plan §1.1 item 1, conventions row N3):
* `V_m(K)` is the degree-`m` homogeneous component of `K[x, y] = MvPolynomial (Fin 2) K` (`x = X 0`, `y = X 1`);
  the basis vectors are `u_t = x^{m−t} y^t`, `0 ≤ t ≤ m`.
* `ρ_m(A)` is the substitution `x ↦ A₁₁x + A₂₁y`, `y ↦ A₁₂x + A₂₂y` ([C] `def:rhon`, column convention, **no**
  determinant twist), restricted to `V_m`. Here `A₁₁ = A 0 0`, `A₂₁ = A 1 0`, `A₁₂ = A 0 1`, `A₂₂ = A 1 1`.
* `β_m(u_s, u_t) = δ_{s+t,m} (−1)^s / C(m, s)`, built from the coefficient functionals (no proof obligations).
* `P_k` over an arbitrary commutative ring (`heckePolyRing`, item 4a) has the recursion of
  `III.ef.def:hecke-polynomial`; item 4 records the compatibility with the integer-valued `heckePoly`.

No project notation. Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open MvPolynomial

/-- The Hecke polynomials over a commutative ring `R`: `P_0 = P_1 = 0`, `P_2 = 1`,
`P_{k+1}(t, n) = t P_k(t, n) − n P_{k−1}(t, n)` (`k ≥ 2`), for `t, n ∈ R`. -/
@[tf_id "III.qform.def:hecke-polynomial-ring"]
def heckePolyRing {R : Type*} [CommRing R] : ℕ → R → R → R
  | 0, _, _ => 0
  | 1, _, _ => 0
  | 2, _, _ => 1
  | k + 3, t, n => t * heckePolyRing (k + 2) t n - n * heckePolyRing (k + 1) t n

/-- `V_m(K)`: the homogeneous polynomials of degree `m` in `K[x, y]` (`x = X 0`, `y = X 1`). -/
@[tf_id "III.qform.def:sym-power-module"]
abbrev symPowerModule (K : Type*) [Field K] (m : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K m

/-- The linear substitution of a matrix `A`: `x ↦ A₁₁x + A₂₁y`, `y ↦ A₁₂x + A₂₂y` (B-only plumbing of
`III.qform.def:sym-power-action`). -/
@[tf_aux "III.qform.def:linear-substitution"]
noncomputable def linSubst {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) : Fin 2 → MvPolynomial (Fin 2) K :=
  fun i => C (A 0 i) * X 0 + C (A 1 i) * X 1

theorem linSubst_isHomogeneous {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    (linSubst A i).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)

theorem aeval_linSubst_mem {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (m : ℕ) :
    ∀ P ∈ symPowerModule K m, (aeval (linSubst A)).toLinearMap P ∈ symPowerModule K m := by
  intro P hP
  have h := (hP : P.IsHomogeneous m).aeval (linSubst A) (linSubst_isHomogeneous A)
  rw [one_mul] at h
  exact h

/-- `ρ_m(A) ∈ End_K(V_m(K))` for `A ∈ M₂(K)`: `(ρ_m(A)P)(x, y) = P(A₁₁x + A₂₁y, A₁₂x + A₂₂y)`. -/
@[tf_id "III.qform.def:sym-power-action"]
noncomputable def symPowerAction (K : Type*) [Field K] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K) :
    Module.End K (symPowerModule K m) :=
  (aeval (linSubst A)).toLinearMap.restrict (aeval_linSubst_mem A m)

/-- The exponent of the monomial `u_t = x^{m−t} y^t` (B-only plumbing). -/
@[tf_aux "III.qform.def:sym-power-exponent"]
noncomputable def symExp (m t : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m - t) + Finsupp.single 1 t

theorem symExp_apply_one (m t : ℕ) : symExp m t 1 = t := by
  simp [symExp]

theorem symExp_apply_zero (m t : ℕ) : symExp m t 0 = m - t := by
  simp [symExp]

theorem symExp_degree (m t : ℕ) (ht : t ≤ m) : (symExp m t).degree = m := by
  rw [symExp, map_add, Finsupp.degree_single, Finsupp.degree_single]
  omega

theorem monomial_symExp (K : Type*) [Field K] (m t : ℕ) :
    monomial (symExp m t) (1 : K) = X 0 ^ (m - t) * X 1 ^ t := by
  rw [symExp, ← one_mul (1 : K), ← monomial_mul_monomial, X_pow_eq_monomial, X_pow_eq_monomial]

theorem symMonomial_mem (K : Type*) [Field K] (m : ℕ) (t : Fin (m + 1)) :
    (X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ) : MvPolynomial (Fin 2) K) ∈ symPowerModule K m := by
  have h := (isHomogeneous_X_pow (R := K) (0 : Fin 2) (m - (t : ℕ))).mul (isHomogeneous_X_pow (1 : Fin 2) (t : ℕ))
  rwa [Nat.sub_add_cancel (Nat.lt_succ_iff.mp t.2)] at h

theorem symPower_basis_exists (K : Type*) [Field K] (m : ℕ) :
    ∃ e : Module.Basis (Fin (m + 1)) K (symPowerModule K m),
      (∀ t : Fin (m + 1), (e t : MvPolynomial (Fin 2) K) = X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ)) ∧
      ∀ (P : symPowerModule K m) (t : Fin (m + 1)), e.repr P t = (P : MvPolynomial (Fin 2) K).coeff (symExp m t) := by
  classical
  set v : Fin (m + 1) → symPowerModule K m := fun t => ⟨_, symMonomial_mem K m t⟩ with hvdef
  have hv : ∀ t, (v t : MvPolynomial (Fin 2) K) = monomial (symExp m t) 1 := by
    intro t
    rw [monomial_symExp]
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (symPowerModule K m).subtype
    have hinj : Function.Injective (fun t : Fin (m + 1) => symExp m t) := by
      intro t t' h
      have h1 := congrArg (fun d => d 1) h
      simp only [symExp_apply_one] at h1
      exact Fin.ext h1
    have h2 := (MvPolynomial.basisMonomials (Fin 2) K).linearIndependent.comp _ hinj
    convert h2 using 1
    funext t
    simp [hv, MvPolynomial.coe_basisMonomials]
  have hexp : ∀ P : symPowerModule K m,
      P = ∑ t : Fin (m + 1), (P : MvPolynomial (Fin 2) K).coeff (symExp m t) • v t := by
    intro P
    have hP : (P : MvPolynomial (Fin 2) K) =
        ∑ t : Fin (m + 1), (P : MvPolynomial (Fin 2) K).coeff (symExp m t) • (v t : MvPolynomial (Fin 2) K) := by
      ext d
      simp only [coeff_sum, coeff_smul, hv, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hd : d.degree = m
      · have hd' : d 0 + d 1 = m := by
          rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
          exact hd
        have h1 : d 1 < m + 1 := by omega
        have hsd : symExp m (d 1) = d := by
          ext i
          fin_cases i
          · simp [symExp_apply_zero]
            omega
          · simp [symExp_apply_one]
        rw [Finset.sum_eq_single ⟨d 1, h1⟩]
        · simp [hsd]
        · intro t _ ht
          rw [ite_eq_right_iff]
          intro h
          exfalso
          apply ht
          ext
          simp [← h, symExp_apply_one]
        · simp
      · rw [(P.2 : (P : MvPolynomial (Fin 2) K).IsHomogeneous m).coeff_eq_zero hd]
        symm
        apply Finset.sum_eq_zero
        intro t _
        rw [ite_eq_right_iff]
        rintro rfl
        exact absurd (symExp_degree m t (Nat.lt_succ_iff.mp t.2)) hd
    apply Subtype.ext
    conv_lhs => rw [hP]
    rw [Submodule.coe_sum]
    rfl
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro P -
    rw [hexp P]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  refine ⟨Module.Basis.mk hli hspan, fun t => by rw [Module.Basis.mk_apply], fun P t => ?_⟩
  conv_lhs => rw [hexp P]
  simp only [← Module.Basis.mk_apply hli hspan, map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem aeval_linSubst_mul {K : Type*} [Field K] (A B : Matrix (Fin 2) (Fin 2) K) (P : MvPolynomial (Fin 2) K) :
    aeval (linSubst A) (aeval (linSubst B) P) = aeval (linSubst (A * B)) P := by
  have h : (aeval (linSubst A)).comp (aeval (linSubst B)) = aeval (linSubst (A * B)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    simp only [linSubst, map_add, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply,
      Fin.sum_univ_two, C_add, C_mul]
    ring
  rw [← h, AlgHom.comp_apply]

theorem linSubst_one {K : Type*} [Field K] : linSubst (1 : Matrix (Fin 2) (Fin 2) K) = X := by
  funext i
  fin_cases i <;> simp [linSubst, Matrix.one_apply]

theorem linSubst_scalar {K : Type*} [Field K] (c : K) (i : Fin 2) :
    linSubst (Matrix.scalar (Fin 2) c) i = C c * X i := by
  fin_cases i <;> simp [linSubst, Matrix.diagonal_apply]

/-- `V_m(K)` has the basis `u_t = x^{m−t} y^t` (`0 ≤ t ≤ m`), so `dim V_m = m + 1`; `ρ_m` is multiplicative and unital;
`ρ_m(c·1) = c^m`; and `ρ_m(−1) = 1` for `m` even. -/
@[tf_id "III.qform.lem:sym-power-basic"]
theorem symPower_basic (K : Type*) [Field K] (m : ℕ) :
    (∃ e : Module.Basis (Fin (m + 1)) K (symPowerModule K m),
        ∀ t : Fin (m + 1), (e t : MvPolynomial (Fin 2) K) = X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ)) ∧
    Module.finrank K (symPowerModule K m) = m + 1 ∧
    (∀ A B : Matrix (Fin 2) (Fin 2) K, symPowerAction K m (A * B) = symPowerAction K m A * symPowerAction K m B) ∧
    symPowerAction K m 1 = 1 ∧
    (∀ c : K, symPowerAction K m (Matrix.scalar (Fin 2) c) = c ^ m • (1 : Module.End K (symPowerModule K m))) ∧
    (Even m → symPowerAction K m (-1) = 1) := by
  obtain ⟨e, he, -⟩ := symPower_basis_exists K m
  have hmul : ∀ A B : Matrix (Fin 2) (Fin 2) K,
      symPowerAction K m (A * B) = symPowerAction K m A * symPowerAction K m B := by
    intro A B
    refine LinearMap.ext fun P => Subtype.ext ?_
    show aeval (linSubst (A * B)) (P : MvPolynomial (Fin 2) K) =
      aeval (linSubst A) (aeval (linSubst B) (P : MvPolynomial (Fin 2) K))
    rw [aeval_linSubst_mul]
  have hone : symPowerAction K m 1 = 1 := by
    refine LinearMap.ext fun P => Subtype.ext ?_
    show aeval (linSubst 1) (P : MvPolynomial (Fin 2) K) = (P : MvPolynomial (Fin 2) K)
    rw [linSubst_one, aeval_X_left_apply]
  have hscal : ∀ c : K,
      symPowerAction K m (Matrix.scalar (Fin 2) c) = c ^ m • (1 : Module.End K (symPowerModule K m)) := by
    intro c
    refine e.ext fun t => ?_
    apply Subtype.ext
    show aeval (linSubst (Matrix.scalar (Fin 2) c)) (e t : MvPolynomial (Fin 2) K) = c ^ m • (e t : MvPolynomial (Fin 2) K)
    have hc : c ^ m = c ^ (m - (t : ℕ)) * c ^ (t : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp t.2)]
    rw [he, hc, map_mul, map_pow, map_pow, aeval_X, aeval_X, linSubst_scalar, linSubst_scalar,
      MvPolynomial.smul_eq_C_mul, mul_pow, mul_pow, C_mul, C_pow, C_pow]
    ring
  refine ⟨⟨e, he⟩, ?_, hmul, hone, hscal, fun hm => ?_⟩
  · rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  · have h := hscal (-1)
    rw [hm.neg_one_pow, one_smul, map_neg, map_one] at h
    exact h

theorem heckePoly_cast (K : Type*) [Field K] :
    ∀ (k : ℕ) (t : ℤ) (n : ℕ), ((GL2TF.Explicit.heckePoly k t n : ℤ) : K) = heckePolyRing k (t : K) (n : K)
  | 0, _, _ => by simp [GL2TF.Explicit.heckePoly, heckePolyRing]
  | 1, _, _ => by simp [GL2TF.Explicit.heckePoly, heckePolyRing]
  | 2, _, _ => by simp [GL2TF.Explicit.heckePoly, heckePolyRing]
  | k + 3, t, n => by
    simp only [GL2TF.Explicit.heckePoly, heckePolyRing]
    push_cast
    rw [heckePoly_cast K (k + 2), heckePoly_cast K (k + 1)]

theorem heckePolyRing_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    ∀ (k : ℕ) (t n : R), f (heckePolyRing k t n) = heckePolyRing k (f t) (f n)
  | 0, _, _ => by simp [heckePolyRing]
  | 1, _, _ => by simp [heckePolyRing]
  | 2, _, _ => by simp [heckePolyRing]
  | k + 3, t, n => by
    simp only [heckePolyRing, map_sub, map_mul]
    rw [heckePolyRing_map f (k + 2), heckePolyRing_map f (k + 1)]

theorem symPower_trace_eq_sum (K : Type*) [Field K] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.trace K (symPowerModule K m) (symPowerAction K m A) =
      ∑ t : Fin (m + 1), (aeval (linSubst A) (X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ) : MvPolynomial (Fin 2) K)).coeff
        (symExp m t) := by
  classical
  obtain ⟨e, he, hrepr⟩ := symPower_basis_exists K m
  rw [LinearMap.trace_eq_matrix_trace K e, Matrix.trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hrepr, ← he t]
  rfl

theorem symPower_trace_sum_map {K L : Type*} [Field K] [Field L] (f : K →+* L) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) K) :
    f (∑ t : Fin (m + 1), (aeval (linSubst A) (X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ) : MvPolynomial (Fin 2) K)).coeff
        (symExp m t)) =
      ∑ t : Fin (m + 1), (aeval (linSubst (A.map f))
        (X 0 ^ (m - (t : ℕ)) * X 1 ^ (t : ℕ) : MvPolynomial (Fin 2) L)).coeff (symExp m t) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [linSubst, Matrix.map_apply]

theorem coeff_aeval_upper {K : Type*} [Field K] (T : Matrix (Fin 2) (Fin 2) K) (hT : T 1 0 = 0) (m t : ℕ) :
    (aeval (linSubst T) (X 0 ^ (m - t) * X 1 ^ t : MvPolynomial (Fin 2) K)).coeff (symExp m t) =
      T 0 0 ^ (m - t) * T 1 1 ^ t := by
  classical
  have h0 : linSubst T 0 = C (T 0 0) * X 0 := by simp [linSubst, hT]
  have h1 : linSubst T 1 = C (T 0 1) * X 0 + C (T 1 1) * X 1 := rfl
  obtain ⟨Q, hQ⟩ : (X 0 : MvPolynomial (Fin 2) K) ∣
      (C (T 0 1) * X 0 + C (T 1 1) * X 1) ^ t - (C (T 1 1) * X 1) ^ t := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ t)
    rw [add_sub_cancel_right]
    exact dvd_mul_left _ _
  have hexp : aeval (linSubst T) (X 0 ^ (m - t) * X 1 ^ t : MvPolynomial (Fin 2) K) =
      C (T 0 0 ^ (m - t) * T 1 1 ^ t) * monomial (symExp m t) 1 +
        monomial (Finsupp.single 0 (m - t + 1)) 1 * (C (T 0 0) ^ (m - t) * Q) := by
    rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, h0, h1, monomial_symExp, eq_add_of_sub_eq' hQ,
      ← X_pow_eq_monomial]
    simp only [C_mul, C_pow]
    ring
  have hnot : ¬ Finsupp.single (0 : Fin 2) (m - t + 1) ≤ symExp m t := by
    intro h
    have := h 0
    rw [symExp_apply_zero, Finsupp.single_eq_same] at this
    omega
  rw [hexp, MvPolynomial.coeff_add, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one, coeff_monomial_mul', if_neg hnot,
    add_zero]

theorem sum_pow_mul_pow_eq_heckePolyRing {K : Type*} [Field K] (α δ : K) :
    ∀ m : ℕ, ∑ t ∈ Finset.range (m + 1), α ^ (m - t) * δ ^ t = heckePolyRing (m + 2) (α + δ) (α * δ) := by
  have hrec : ∀ m : ℕ, ∑ t ∈ Finset.range (m + 2), α ^ (m + 1 - t) * δ ^ t =
      α * ∑ t ∈ Finset.range (m + 1), α ^ (m - t) * δ ^ t + δ ^ (m + 1) := by
    intro m
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [Nat.sub_add_comm ht', pow_succ]
    ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [heckePolyRing]
    | 1, _ => simp [heckePolyRing, Finset.sum_range_succ]
    | m + 2, ih =>
      rw [show m + 2 + 2 = (m + 1) + 3 from rfl, heckePolyRing, ← ih (m + 1) (by omega), ← ih m (by omega),
        show m + 2 + 1 = (m + 1) + 2 from rfl, hrec (m + 1), hrec m]
      ring

open Matrix in
theorem symPower_trace_algClosed (L : Type*) [Field L] [IsAlgClosed L] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) L) :
    LinearMap.trace L (symPowerModule L m) (symPowerAction L m A) = heckePolyRing (m + 2) A.trace A.det := by
  classical
  have hbasic := symPower_basic L m
  obtain ⟨α, hα⟩ : ∃ α : L, α ^ 2 - A.trace * α + A.det = 0 := by
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
      (Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (-A.trace) * Polynomial.X + Polynomial.C A.det)
      (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
    refine ⟨α, ?_⟩
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at hα
    linear_combination hα
  have hdet : (A - α • (1 : Matrix (Fin 2) (Fin 2) L)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero, sub_zero]
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hα
    linear_combination hα
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = α • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  set c : L := if v 0 = 0 then 1 else 0 with hc
  set d : L := if v 0 = 0 then 0 else 1 with hd
  set g : Matrix (Fin 2) (Fin 2) L := !![v 0, c; v 1, d] with hgdef
  have hgdet : g.det ≠ 0 := by
    rw [hgdef, Matrix.det_fin_two_of]
    by_cases h : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv0
        ext i
        fin_cases i <;> simp [h, h1]
      simp [hc, hd, h, h1]
    · simp [hc, hd, h]
  have hg : IsUnit g.det := isUnit_iff_ne_zero.mpr hgdet
  set T := g⁻¹ * A * g with hTdef
  have hge : g *ᵥ Pi.single 0 1 = v := by
    ext i
    fin_cases i <;> simp [hgdef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hT10 : T 1 0 = 0 := by
    have h : T *ᵥ Pi.single 0 1 = α • Pi.single 0 1 := by
      rw [hTdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hge, hAv, Matrix.mulVec_smul, ← hge,
        Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg, Matrix.one_mulVec]
    have h1 := congrFun h 1
    rw [Matrix.mulVec_single_one] at h1
    simpa using h1
  have htrρ : LinearMap.trace L _ (symPowerAction L m T) = LinearMap.trace L _ (symPowerAction L m A) := by
    rw [hTdef, hbasic.2.2.1, hbasic.2.2.1, LinearMap.trace_mul_comm, ← hbasic.2.2.1, ← hbasic.2.2.1,
      ← mul_assoc, Matrix.mul_nonsing_inv g hg, one_mul]
  have htr : T.trace = A.trace := by
    rw [hTdef, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv g hg, one_mul]
  have hdetT : T.det = A.det := by
    rw [hTdef, Matrix.det_mul, Matrix.det_mul, mul_comm (g⁻¹.det), mul_assoc, ← Matrix.det_mul,
      Matrix.nonsing_inv_mul g hg, Matrix.det_one, mul_one]
  rw [← htrρ, ← htr, ← hdetT, symPower_trace_eq_sum]
  simp only [coeff_aeval_upper T hT10]
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, hT10, mul_zero, sub_zero, ← sum_pow_mul_pow_eq_heckePolyRing,
    Fin.sum_univ_eq_sum_range (fun t => T 0 0 ^ (m - t) * T 1 1 ^ t) (m + 1)]

/-- `tr ρ_m(A) = P_{m+2}(tr A, det A)` for every `A ∈ M₂(K)`; and `P_k` over `K` is the image of the integer `P_k`. -/
@[tf_id "III.qform.thm:sym-power-trace"]
theorem symPower_trace (K : Type*) [Field K] :
    (∀ (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K),
      LinearMap.trace K (symPowerModule K m) (symPowerAction K m A) = heckePolyRing (m + 2) A.trace A.det) ∧
    (∀ (k : ℕ) (t : ℤ) (n : ℕ),
      ((GL2TF.Explicit.heckePoly k t n : ℤ) : K) = heckePolyRing k (t : K) (n : K)) := by
  refine ⟨fun m A => ?_, heckePoly_cast K⟩
  set f := algebraMap K (AlgebraicClosure K) with hf
  apply f.injective
  rw [symPower_trace_eq_sum, symPower_trace_sum_map f, ← symPower_trace_eq_sum,
    symPower_trace_algClosed, heckePolyRing_map]
  congr 1
  · simp [Matrix.trace_fin_two, Matrix.map_apply]
  · simp [Matrix.det_fin_two, Matrix.map_apply]

/-- The pairing `β_m(u_s, u_t) = δ_{s+t,m} (−1)^s / C(m, s)` on `V_m(K)`, extended bilinearly:
`β_m(v, w) = Σ_{s=0}^m (−1)^s C(m, s)^{−1} v_s w_{m−s}` with `v_s` the coefficient of `u_s`. -/
@[tf_id "III.qform.def:sym-power-pairing"]
noncomputable def symPowerPairing (K : Type*) [Field K] (m : ℕ) :
    symPowerModule K m →ₗ[K] symPowerModule K m →ₗ[K] K :=
  ∑ s ∈ Finset.range (m + 1), ((-1 : K) ^ s / (m.choose s : K)) •
    (LinearMap.mul K K).compl₁₂ ((lcoeff K (symExp m s)).comp (symPowerModule K m).subtype)
      ((lcoeff K (symExp m (m - s))).comp (symPowerModule K m).subtype)

theorem linPow_mem (K : Type*) [Field K] (m : ℕ) (α β : K) :
    ((C α * X 0 + C β * X 1) ^ m : MvPolynomial (Fin 2) K) ∈ symPowerModule K m := by
  have h := ((isHomogeneous_C_mul_X (R := K) α (0 : Fin 2)).add (isHomogeneous_C_mul_X β (1 : Fin 2))).pow m
  rwa [one_mul] at h

theorem linPow_expand (K : Type*) [Field K] (m : ℕ) (α β : K) :
    ((C α * X 0 + C β * X 1) ^ m : MvPolynomial (Fin 2) K) =
      ∑ s ∈ Finset.range (m + 1), monomial (symExp m s) ((m.choose s : K) * α ^ (m - s) * β ^ s) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_one ((m.choose s : K) * α ^ (m - s) * β ^ s), ← C_mul_monomial, monomial_symExp]
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem linPow_coeff (K : Type*) [Field K] (m : ℕ) (α β : K) (t : ℕ) (ht : t ≤ m) :
    ((C α * X 0 + C β * X 1) ^ m : MvPolynomial (Fin 2) K).coeff (symExp m t) =
      (m.choose t : K) * α ^ (m - t) * β ^ t := by
  classical
  rw [linPow_expand, coeff_sum, Finset.sum_eq_single t]
  · rw [coeff_monomial, if_pos rfl]
  · intro s _ hst
    rw [coeff_monomial, if_neg]
    intro h
    apply hst
    have h1 := congrArg (fun d => d 1) h
    simpa [symExp_apply_one] using h1
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le ht)) h

theorem symPowerPairing_linPow (K : Type*) [Field K] [CharZero K] (m : ℕ) (α β γ δ : K) :
    symPowerPairing K m ⟨_, linPow_mem K m α β⟩ ⟨_, linPow_mem K m γ δ⟩ = (α * δ - β * γ) ^ m := by
  simp only [symPowerPairing, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', LinearMap.comp_apply, Submodule.subtype_apply, lcoeff_apply, smul_eq_mul]
  rw [sub_eq_neg_add, add_pow (-(β * γ)) (α * δ)]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [linPow_coeff K m α β s hs', linPow_coeff K m γ δ (m - s) (Nat.sub_le m s), Nat.sub_sub_self hs',
    Nat.choose_symm hs']
  have hc : (m.choose s : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hs').ne'
  have hneg : (-(β * γ)) ^ s = (-1) ^ s * β ^ s * γ ^ s := by
    rw [neg_eq_neg_one_mul, mul_pow, mul_pow, mul_assoc]
  rw [hneg, mul_pow]
  field_simp

theorem symPowerAction_linPow (K : Type*) [Field K] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (α β : K) :
    symPowerAction K m A ⟨_, linPow_mem K m α β⟩ =
      ⟨_, linPow_mem K m (α * A 0 0 + β * A 0 1) (α * A 1 0 + β * A 1 1)⟩ := by
  have h1 : ((symPowerAction K m A ⟨_, linPow_mem K m α β⟩ : symPowerModule K m) : MvPolynomial (Fin 2) K) =
      aeval (linSubst A) ((C α * X 0 + C β * X 1) ^ m) := rfl
  have h2 : aeval (linSubst A) (C α * X 0 + C β * X 1 : MvPolynomial (Fin 2) K) =
      C (α * A 0 0 + β * A 0 1) * X 0 + C (α * A 1 0 + β * A 1 1) * X 1 := by
    simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_eq, linSubst]
    ring
  exact Subtype.ext (h1.trans (by rw [map_pow, h2]))

theorem linPow_span (K : Type*) [Field K] [CharZero K] (m : ℕ) :
    Submodule.span K (Set.range fun p : K × K => (⟨_, linPow_mem K m p.1 p.2⟩ : symPowerModule K m)) = ⊤ := by
  classical
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨e, he, hrepr⟩ := symPower_basis_exists K m
  apply hf0
  have hval : ∀ t : K, ∑ s : Fin (m + 1), ((m.choose s : K) * f (e s)) * t ^ (s : ℕ) = 0 := by
    intro t
    have hmem : f ⟨_, linPow_mem K m 1 t⟩ = 0 := hle (Submodule.subset_span ⟨(1, t), rfl⟩)
    rw [← e.sum_repr ⟨_, linPow_mem K m 1 t⟩, map_sum] at hmem
    rw [← hmem]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, hrepr, smul_eq_mul]
    rw [linPow_coeff K m 1 t s (Nat.lt_succ_iff.mp s.2), one_pow, mul_one]
    ring
  set Q : Polynomial K := ∑ s : Fin (m + 1),
    Polynomial.C ((m.choose s : K) * f (e s)) * Polynomial.X ^ (s : ℕ) with hQdef
  have hQ : Q = 0 := Polynomial.funext fun t => by
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    exact hval t
  refine e.ext fun s => ?_
  have hc := congrArg (fun q => Polynomial.coeff q (s : ℕ)) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single s] at hc
  · rw [if_pos rfl] at hc
    rw [LinearMap.zero_apply]
    exact (mul_eq_zero.mp hc).resolve_left (Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp s.2)).ne')
  · intro s' _ hs'
    rw [if_neg]
    intro h
    exact hs' (Fin.ext h.symm)
  · simp

theorem symPowerPairing_ext (K : Type*) [Field K] [CharZero K] (m : ℕ)
    {B₁ B₂ : symPowerModule K m →ₗ[K] symPowerModule K m →ₗ[K] K}
    (h : ∀ α β γ δ : K, B₁ ⟨_, linPow_mem K m α β⟩ ⟨_, linPow_mem K m γ δ⟩ =
      B₂ ⟨_, linPow_mem K m α β⟩ ⟨_, linPow_mem K m γ δ⟩) : B₁ = B₂ :=
  LinearMap.ext_on_range (linPow_span K m) fun p =>
    LinearMap.ext_on_range (linPow_span K m) fun q => h p.1 p.2 q.1 q.2

/-- `β_m(ρ_m(A)v, w) = β_m(v, ρ_m(adj A)w)`; `β_m` is nondegenerate, and symmetric for `m` even;
`β_m(ρ_m(A)v, ρ_m(A)w) = det(A)^m β_m(v, w)`. (`K` of characteristic `0`, so that `C(m, s) ≠ 0`.) -/
@[tf_id "III.qform.lem:sym-power-pairing-adjoint"]
theorem symPowerPairing_adjoint (K : Type*) [Field K] [CharZero K] (m : ℕ) :
    (∀ (A : Matrix (Fin 2) (Fin 2) K) (v w : symPowerModule K m),
      symPowerPairing K m (symPowerAction K m A v) w = symPowerPairing K m v (symPowerAction K m A.adjugate w)) ∧
    (symPowerPairing K m).SeparatingLeft ∧
    (Even m → ∀ v w : symPowerModule K m, symPowerPairing K m v w = symPowerPairing K m w v) ∧
    (∀ (A : Matrix (Fin 2) (Fin 2) K) (v w : symPowerModule K m),
      symPowerPairing K m (symPowerAction K m A v) (symPowerAction K m A w) = A.det ^ m * symPowerPairing K m v w) := by
  refine ⟨fun A v w => ?_, ?_, fun hm v w => ?_, fun A v w => ?_⟩
  · have h := symPowerPairing_ext K m (B₁ := (symPowerPairing K m).comp (symPowerAction K m A))
      (B₂ := (symPowerPairing K m).compl₂ (symPowerAction K m A.adjugate)) (fun α β γ δ => by
        simp only [LinearMap.comp_apply, LinearMap.compl₂_apply]
        rw [symPowerAction_linPow, symPowerAction_linPow, symPowerPairing_linPow, symPowerPairing_linPow,
          Matrix.adjugate_fin_two]
        congr 1
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        ring)
    exact LinearMap.congr_fun₂ h v w
  · intro v hv
    classical
    obtain ⟨e, he, hrepr⟩ := symPower_basis_exists K m
    refine e.ext_elem fun t => ?_
    rw [map_zero, Finsupp.zero_apply, hrepr]
    have ht : (t : ℕ) ≤ m := Nat.lt_succ_iff.mp t.2
    have h := hv (e ⟨m - t, by omega⟩)
    simp only [symPowerPairing, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      LinearMap.mul_apply', LinearMap.comp_apply, Submodule.subtype_apply, lcoeff_apply, smul_eq_mul] at h
    rw [he, ← monomial_symExp, Finset.sum_eq_single (t : ℕ)] at h
    · rw [coeff_monomial, if_pos rfl, mul_one] at h
      have hc : (m.choose t : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos ht).ne'
      have hne : (-1 : K) ^ (t : ℕ) / (m.choose t : K) ≠ 0 := div_ne_zero (pow_ne_zero _ (by norm_num)) hc
      exact (mul_eq_zero.mp h).resolve_left hne
    · intro s hs hst
      have hs' : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [coeff_monomial, if_neg, mul_zero, mul_zero]
      intro h'
      have h1 := congrArg (fun d => d 1) h'
      simp only [symExp_apply_one] at h1
      omega
    · intro h'
      exact absurd (Finset.mem_range.mpr t.2) h'
  · have h := symPowerPairing_ext K m (B₁ := symPowerPairing K m) (B₂ := (symPowerPairing K m).flip)
      (fun α β γ δ => by
        rw [LinearMap.flip_apply, symPowerPairing_linPow, symPowerPairing_linPow, ← hm.neg_pow]
        congr 1
        ring)
    exact LinearMap.congr_fun₂ h v w
  · have h := symPowerPairing_ext K m
      (B₁ := (symPowerPairing K m).compl₁₂ (symPowerAction K m A) (symPowerAction K m A))
      (B₂ := A.det ^ m • symPowerPairing K m) (fun α β γ δ => by
        rw [LinearMap.compl₁₂_apply, symPowerAction_linPow, symPowerAction_linPow, symPowerPairing_linPow,
          LinearMap.smul_apply, LinearMap.smul_apply, symPowerPairing_linPow, smul_eq_mul, ← mul_pow]
        congr 1
        rw [Matrix.det_fin_two]
        ring)
    exact LinearMap.congr_fun₂ h v w

end GL2TF.Quat
