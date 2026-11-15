import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Reduction
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Group.Basic

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolII/Centralizer.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (5): `centralizerGL_borelSpace`, `centralizerNormOne_borelSpace`, `centralizer_unimodular`, `elliptic_volume_finite`, `isUnimodular_of_comm`.
Dropped tagged IDs: `II.orb.lem:centralizer-borel-instance`, `II.orb.lem:centralizer-norm-one-borel-instance`, `II.orb.lem:centralizer-unimodular`, `II.orb.thm:elliptic-volume-finite`. -/

/-!
# Elliptic elements and their centralizers (M3e, units U1–U2)

Lean counterpart of `vol2/ch-04-orbital.tex` §§1–2: elliptic elements of `GL₂(K)`, the centralizers `G_γ(R)` of rational
elements, the norm-one part `G_γ(𝔸)^1`, the height bound for elliptic `γ`, compactness of `G_γ(ℚ)\G_γ(𝔸)^1` and finiteness
of its volume (D9 route (β); D-ELL, D-CENT, D-ROUTE, D-VOL of `docs/sprints/M3e-plan.md`). Owner: L1.

Design: `IsElliptic γ` is irreducibility of `Matrix.charpoly γ` (D-ELL). `G_γ(R)` is `Subgroup.centralizer` of the single
element `ι_R(γ)`, `G_γ(𝔸)^1` its `subgroupOf normOneGroup`, and `G_γ(ℚ)` inside `G_γ(𝔸)^1` is the B-only
`centralizerRatNormOne γ` (the trace of `gl2RatNormOne`), as for `gl2RatNormOne` in M3. Quotients are
`MulAction.orbitRel.Quotient` as in M3/M4.
-/

open MeasureTheory Polynomial
open scoped ENNReal

namespace GL2TF

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### §1 Elliptic elements and their centralizers (U1) -/

section Elliptic

variable {K : Type*} [Field K]

/-- `γ ∈ GL₂(K)` is elliptic if its characteristic polynomial `P_γ = det(X·1 − γ) = X² − tr(γ) X + det γ` is
irreducible in `K[X]`. -/
@[tf_id "II.orb.def:elliptic"]
def IsElliptic (γ : GL (Fin 2) K) : Prop :=
  Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) K))

namespace OrbAux

theorem charpoly_natDegree_two (M : Matrix (Fin 2) (Fin 2) K) : M.charpoly.natDegree = 2 := by
  simp [Matrix.charpoly_natDegree_eq_dim]

theorem isElliptic_iff_no_root (γ : GL (Fin 2) K) :
    IsElliptic γ ↔ ∀ x : K, ¬ (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) K)).IsRoot x := by
  constructor
  · intro h x hx
    have h1 := degree_eq_one_of_irreducible_of_root h hx
    have h2 := charpoly_natDegree_two (γ : Matrix (Fin 2) (Fin 2) K)
    rw [degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero, h2] at h1
    exact absurd h1 (by decide)
  · intro h
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ h
    rw [charpoly_natDegree_two]; decide

theorem det_rows_eq_zero_iff (v w : Fin 2 → K) (hv : v ≠ 0) :
    Matrix.det (Matrix.of ![v, w]) = 0 ↔ ∃ c : K, w = c • v := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1; apply hv; ext i; fin_cases i <;> simp [h0, h1]
      refine ⟨w 1 / v 1, ?_⟩
      have hw0 : w 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
        exact (mul_eq_zero.mp h).resolve_left h1
      ext i; fin_cases i
      · simp [h0, hw0]
      · simp; field_simp
    · refine ⟨w 0 / v 0, ?_⟩
      ext i; fin_cases i
      · simp; field_simp
      · simp; field_simp; linear_combination h
  · rintro ⟨c, rfl⟩
    simp; ring

theorem isRoot_iff_eigen (γ : GL (Fin 2) K) (c : K) :
    (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) K)).IsRoot c ↔
      ∃ v : Fin 2 → K, v ≠ 0 ∧ Matrix.vecMul v (γ : Matrix (Fin 2) (Fin 2) K) = c • v := by
  rw [IsRoot, Matrix.eval_charpoly, ← Matrix.exists_vecMul_eq_zero_iff]
  refine exists_congr fun v ↦ and_congr_right fun _ ↦ ?_
  rw [Matrix.vecMul_sub, sub_eq_zero, eq_comm]
  have : Matrix.vecMul v (Matrix.scalar (Fin 2) c) = c • v := by
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [this]

theorem not_elliptic_iff_eigen (γ : GL (Fin 2) K) :
    ¬ IsElliptic γ ↔ ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ c : K, Matrix.vecMul v (γ : Matrix (Fin 2) (Fin 2) K) = c • v := by
  rw [isElliptic_iff_no_root]
  push Not
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨v, hv, h⟩ := (isRoot_iff_eigen γ c).mp hc
    exact ⟨v, hv, c, h⟩
  · rintro ⟨v, hv, c, h⟩
    exact ⟨c, (isRoot_iff_eigen γ c).mpr ⟨v, hv, h⟩⟩

theorem not_elliptic_of_scalar (γ : GL (Fin 2) K) (c : K) (h : (γ : Matrix (Fin 2) (Fin 2) K) = c • 1) :
    ¬ IsElliptic γ := by
  rw [isElliptic_iff_no_root]
  push Not
  refine ⟨c, ?_⟩
  rw [IsRoot, Matrix.eval_charpoly, h]
  simp [Matrix.smul_one_eq_diagonal]

end OrbAux

open OrbAux

/-- For `γ ∈ GL₂(K)`: (a) `γ` elliptic ⇔ (b) `P_γ` has no root in `K` ⇔ (c) for every row vector `v ≠ 0` the matrix with
rows `v`, `vγ` has non-zero determinant; and an elliptic `γ` is not central. -/
@[tf_id "II.orb.thm:elliptic-iff-no-eigenvector"]
theorem elliptic_iff_no_eigenvector (γ : GL (Fin 2) K) :
    (IsElliptic γ ↔ ∀ x : K, ¬ (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) K)).IsRoot x) ∧
      (IsElliptic γ ↔ ∀ v : Fin 2 → K, v ≠ 0 →
        Matrix.det (Matrix.of ![v, Matrix.vecMul v (γ : Matrix (Fin 2) (Fin 2) K)]) ≠ 0) ∧
      (IsElliptic γ → γ ∉ center K) := by
  refine ⟨isElliptic_iff_no_root γ, ?_, ?_⟩
  · rw [← not_iff_not, not_elliptic_iff_eigen]
    push Not
    refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
    rw [det_rows_eq_zero_iff v _ hv]
  · rintro h ⟨u, rfl⟩
    refine not_elliptic_of_scalar _ (u : K) ?_ h
    simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

namespace OrbAux

theorem row_conj (δ γ : GL (Fin 2) K) :
    Matrix.vecMul ((δ : Matrix (Fin 2) (Fin 2) K) 1) (γ : Matrix (Fin 2) (Fin 2) K) =
      Matrix.vecMul (((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1) (δ : Matrix (Fin 2) (Fin 2) K) := by
  have h : ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (δ : Matrix (Fin 2) (Fin 2) K) =
      (δ : Matrix (Fin 2) (Fin 2) K) * (γ : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  have h1 := congrFun (congrArg (fun M ↦ M 1) h)
  ext j
  have := h1 j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  linear_combination -this

end OrbAux

open OrbAux

/-- `γ` is elliptic iff `δγδ⁻¹ ∉ B(K)` for every `δ ∈ GL₂(K)`; ellipticity is invariant under conjugation. -/
@[tf_id "II.orb.thm:elliptic-iff-not-borel-conjugate"]
theorem elliptic_iff_not_borel_conjugate (γ : GL (Fin 2) K) :
    (IsElliptic γ ↔ ∀ δ : GL (Fin 2) K, δ * γ * δ⁻¹ ∉ borel K) ∧
      (IsElliptic γ → ∀ δ : GL (Fin 2) K, IsElliptic (δ * γ * δ⁻¹)) := by
  refine ⟨⟨fun h δ hb ↦ ?_, fun h ↦ ?_⟩, fun h δ ↦ ?_⟩
  · -- e₂δ is an eigenvector of γ
    apply (not_elliptic_iff_eigen γ).mpr _ h
    have hb0 : ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
    refine ⟨(δ : Matrix (Fin 2) (Fin 2) K) 1, ?_, ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1, ?_⟩
    · intro h0
      have hd := (Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit
      rw [Matrix.det_fin_two] at hd
      have e0 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := congrFun h0 0
      have e1 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := congrFun h0 1
      rw [e0, e1] at hd; simp at hd
    · rw [row_conj]
      ext j
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb0, zero_mul, zero_add, Pi.smul_apply, smul_eq_mul]
  · by_contra hne
    obtain ⟨v, hv, c, hc⟩ := (not_elliptic_iff_eigen γ).mp hne
    -- complete `v` to a basis `(u, v)`
    obtain ⟨u, hu⟩ : ∃ u : Fin 2 → K, u 0 * v 1 - u 1 * v 0 ≠ 0 := by
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := by
          intro h1; apply hv; ext i; fin_cases i <;> simp [h0, h1]
        exact ⟨![1, 0], by simpa [h0] using h1⟩
      · exact ⟨![0, 1], by simpa using h0⟩
    let δ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of ![u, v])
      (by rw [Matrix.det_fin_two]; simpa using hu)
    have hδ1 : (δ : Matrix (Fin 2) (Fin 2) K) 1 = v := rfl
    have hδ0 : (δ : Matrix (Fin 2) (Fin 2) K) 0 = u := rfl
    apply h δ
    show ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    have hr := row_conj δ γ
    rw [hδ1, hc] at hr
    set M := ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    have e0 := congrFun hr 0
    have e1 := congrFun hr 1
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
    rw [← hδ0, ← hδ1] at hu
    have : M 1 0 * ((δ : Matrix (Fin 2) (Fin 2) K) 0 0 * (δ : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (δ : Matrix (Fin 2) (Fin 2) K) 0 1 * (δ : Matrix (Fin 2) (Fin 2) K) 1 0) = 0 := by
      rw [← hδ1] at e0 e1
      linear_combination (δ : Matrix (Fin 2) (Fin 2) K) 1 0 * e1 - (δ : Matrix (Fin 2) (Fin 2) K) 1 1 * e0
    exact (mul_eq_zero.mp this).resolve_right hu
  · unfold IsElliptic at h ⊢
    have : ((δ * γ * δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (δ : Matrix (Fin 2) (Fin 2) K) * (γ : Matrix (Fin 2) (Fin 2) K) * (δ : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    rw [this, Matrix.charpoly_units_conj]
    exact h

namespace OrbAux

theorem sq_eq_trace_det (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
  rw [sq] at h
  rw [← sub_eq_zero, ← h]
  simp only [smul_mul_assoc, one_mul]
  abel

theorem aeval_mem_span (γ : Matrix (Fin 2) (Fin 2) K) (p : K[X]) :
    ∃ a b : K, aeval γ p = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • γ := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨c, d, h'⟩ := hq
    exact ⟨a + c, b + d, by rw [map_add, h, h', add_smul, add_smul]; abel⟩
  | monomial n a h =>
    obtain ⟨c, d, h⟩ := h
    refine ⟨-(d * γ.det), c + d * γ.trace, ?_⟩
    rw [pow_succ, ← mul_assoc, map_mul, h, aeval_X, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
      sq_eq_trace_det, smul_sub, smul_smul, smul_smul, add_smul, neg_smul]
    abel

end OrbAux

open OrbAux

/-- For `γ` elliptic, `E = K[γ] = {a·1 + bγ}` is a subring of `M₂(K)` which is a field (here: the underlying set of a
`K`-subalgebra that is a field), `1, γ` are linearly independent, `X ↦ γ` induces `K[X]/(P_γ) ≅ E`, and every non-zero
element of `E` is invertible in `M₂(K)` with inverse in `E`. -/
@[tf_id "II.orb.thm:elliptic-quadratic-field"]
theorem elliptic_quadratic_field (γ : GL (Fin 2) K) (hγ : IsElliptic γ) :
    ∃ E : Subalgebra K (Matrix (Fin 2) (Fin 2) K),
      (E : Set (Matrix (Fin 2) (Fin 2) K)) =
          {M | ∃ a b : K, M = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • (γ : Matrix (Fin 2) (Fin 2) K)} ∧
        IsField E ∧
        LinearIndependent K ![(1 : Matrix (Fin 2) (Fin 2) K), (γ : Matrix (Fin 2) (Fin 2) K)] ∧
        (∃ e : (K[X] ⧸ Ideal.span {Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) K)}) ≃ₐ[K] E,
          ∀ p : K[X], ((e (Ideal.Quotient.mk _ p) : E) : Matrix (Fin 2) (Fin 2) K) =
            aeval (γ : Matrix (Fin 2) (Fin 2) K) p) ∧
        ∀ η ∈ E, η ≠ 0 → ∃ η' ∈ E, η * η' = 1 ∧ η' * η = 1 := by
  set g : Matrix (Fin 2) (Fin 2) K := (γ : Matrix (Fin 2) (Fin 2) K) with hg
  set φ : K[X] →ₐ[K] Matrix (Fin 2) (Fin 2) K := aeval g
  set P := Matrix.charpoly g
  have hker : Ideal.span {P} = RingHom.ker φ := by
    have hmax : (Ideal.span {P}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hγ
    refine hmax.eq_of_le ?_ ?_
    · intro h
      have : (1 : K[X]) ∈ RingHom.ker φ := by rw [h]; trivial
      rw [RingHom.mem_ker, map_one] at this
      exact one_ne_zero this
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Matrix.aeval_self_charpoly g
  let e : (K[X] ⧸ Ideal.span {P}) ≃ₐ[K] φ.range :=
    (Ideal.quotientEquivAlgOfEq K hker).trans (Ideal.quotientKerEquivRange φ)
  have he : ∀ p : K[X], ((e (Ideal.Quotient.mk _ p) : φ.range) : Matrix (Fin 2) (Fin 2) K) = φ p := fun p ↦ rfl
  have hfield : IsField φ.range := by
    have : IsField (K[X] ⧸ Ideal.span {P}) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (PrincipalIdealRing.isMaximal_of_irreducible hγ)
    exact e.symm.toMulEquiv.isField this
  refine ⟨φ.range, ?_, hfield, ?_, ⟨e, he⟩, ?_⟩
  · ext M
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨a, b, h⟩ := aeval_mem_span g p
      exact ⟨a, b, h⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨C a + C b * X, by simp [φ, Algebra.algebraMap_eq_smul_one]⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      refine not_elliptic_of_scalar γ (-(s / t)) ?_ hγ
      have : t • g = -(s • 1) := eq_neg_of_add_eq_zero_right hst
      calc g = t⁻¹ • (t • g) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, neg_smul]; congr 2; field_simp
  · intro η hη hne
    have hne' : (⟨η, hη⟩ : φ.range) ≠ 0 := fun h ↦ hne (congrArg Subtype.val h)
    obtain ⟨η', hη'⟩ := hfield.mul_inv_cancel hne'
    refine ⟨η', η'.2, congrArg Subtype.val hη', ?_⟩
    rw [hfield.mul_comm] at hη'
    exact congrArg Subtype.val hη'

end Elliptic

/-- The centralizer `G_γ(R) = {g ∈ GL₂(R) : g ι_R(γ) = ι_R(γ) g}` of `γ ∈ GL₂(ℚ)`, for a commutative `ℚ`-algebra `R`,
with `ι_R = gl2Map (algebraMap ℚ R)`. -/
@[tf_id "II.orb.def:centralizer"]
def centralizerGL (R : Type*) [CommRing R] [Algebra ℚ R] (γ : GL (Fin 2) ℚ) : Subgroup (GL (Fin 2) R) :=
  Subgroup.centralizer {gl2Map (algebraMap ℚ R) γ}

namespace OrbAux

theorem gl2Map_entry {R : Type*} [CommRing R] (f : ℚ →+* R) (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((gl2Map f γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j = f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem noncentral_cases (γ : GL (Fin 2) ℚ) (hγ : γ ∉ center ℚ) :
    (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1 ≠ 0 ∨ (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ≠ 0 ∨
      (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ≠ (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := by
  by_contra h
  push Not at h
  obtain ⟨hq, hr, hps⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  rw [Matrix.det_fin_two, hq, hr, hps, mul_zero, sub_zero] at hd
  have hp : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 ≠ 0 := fun h0 ↦ by simp [h0] at hd
  apply hγ
  refine ⟨Units.mk0 _ hp, Units.ext ?_⟩
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp [hq, hr, hps]

theorem comm_lin {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (a b c d : R) :
    Commute (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • M) (c • 1 + d • M) := by
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_) <;>
    refine Commute.smul_left (Commute.smul_right ?_ _) _
  · exact Commute.one_left _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact Commute.refl _

end OrbAux

open OrbAux

/-- For `γ ∉ Z(ℚ)` and every commutative `ℚ`-algebra `R`: `G_γ(R) = {a·1 + b ι_R(γ) : a, b ∈ R} ∩ GL₂(R)`, and `G_γ(R)`
is commutative. -/
@[tf_id "II.orb.thm:centralizer-explicit"]
theorem centralizer_explicit (γ : GL (Fin 2) ℚ) (hγ : γ ∉ center ℚ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    (centralizerGL R γ : Set (GL (Fin 2) R)) =
        {g : GL (Fin 2) R | ∃ a b : R, (g : Matrix (Fin 2) (Fin 2) R) =
          a • (1 : Matrix (Fin 2) (Fin 2) R) + b • (gl2Map (algebraMap ℚ R) γ : Matrix (Fin 2) (Fin 2) R)} ∧
      ∀ g ∈ centralizerGL R γ, ∀ h ∈ centralizerGL R γ, g * h = h * g := by
  set f := algebraMap ℚ R
  have hset : (centralizerGL R γ : Set (GL (Fin 2) R)) =
        {g : GL (Fin 2) R | ∃ a b : R, (g : Matrix (Fin 2) (Fin 2) R) =
          a • (1 : Matrix (Fin 2) (Fin 2) R) + b • (gl2Map f γ : Matrix (Fin 2) (Fin 2) R)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, centralizerGL, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      have hm : (g : Matrix (Fin 2) (Fin 2) R) * (gl2Map f γ : Matrix (Fin 2) (Fin 2) R) =
          (gl2Map f γ : Matrix (Fin 2) (Fin 2) R) * g := by
        rw [← Units.val_mul, ← Units.val_mul, hc]
      have E : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) R) * (gl2Map f γ : Matrix (Fin 2) (Fin 2) R)) i j =
          ((gl2Map f γ : Matrix (Fin 2) (Fin 2) R) * g) i j := fun i j ↦ by rw [hm]
      have E00 := E 0 0
      have E01 := E 0 1
      have E10 := E 1 0
      have E11 := E 1 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, gl2Map_entry] at E00 E01 E10 E11
      set x := (g : Matrix (Fin 2) (Fin 2) R) 0 0
      set y := (g : Matrix (Fin 2) (Fin 2) R) 0 1
      set z := (g : Matrix (Fin 2) (Fin 2) R) 1 0
      set w := (g : Matrix (Fin 2) (Fin 2) R) 1 1
      set p := (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0
      set q := (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1
      set r := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0
      set s := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1
      have hinv : ∀ t : ℚ, t ≠ 0 → f t * f t⁻¹ = 1 := fun t ht ↦ by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      have key : ∀ a b : R, x = a + b * f p → y = b * f q → z = b * f r → w = a + b * f s →
          ∃ a b : R, (g : Matrix (Fin 2) (Fin 2) R) =
            a • (1 : Matrix (Fin 2) (Fin 2) R) + b • (gl2Map f γ : Matrix (Fin 2) (Fin 2) R) := by
        intro a b h1 h2 h3 h4
        refine ⟨a, b, Matrix.ext fun i j ↦ ?_⟩
        fin_cases i <;> fin_cases j <;> simp [gl2Map_entry] <;> assumption
      by_cases hq : q ≠ 0
      · have hq' := hinv q hq
        refine key (x - y * f q⁻¹ * f p) (y * f q⁻¹) (by ring) ?_ ?_ ?_
        · linear_combination (-y) * hq'
        · linear_combination (-(f q⁻¹)) * E00 - z * hq'
        · linear_combination (-(f q⁻¹)) * E01 - (w - x) * hq'
      by_cases hr : r ≠ 0
      · have hr' := hinv r hr
        refine key (x - z * f r⁻¹ * f p) (z * f r⁻¹) (by ring) ?_ ?_ ?_
        · linear_combination (f r⁻¹) * E00 - y * hr'
        · linear_combination (-z) * hr'
        · linear_combination (f r⁻¹) * E10 - (w - x) * hr'
      push Not at hq hr
      have hps : p ≠ s := by
        rcases noncentral_cases γ hγ with h | h | h
        · exact absurd hq h
        · exact absurd hr h
        · exact h
      have hps' := hinv (p - s) (sub_ne_zero.mpr hps)
      rw [map_sub] at hps'
      have hfq : f q = 0 := by rw [hq, map_zero]
      have hfr : f r = 0 := by rw [hr, map_zero]
      simp only [hfq, hfr] at E01 E10
      refine key (x - (x - w) * f (p - s)⁻¹ * f p) ((x - w) * f (p - s)⁻¹) (by ring) ?_ ?_ ?_
      · simp only [hfq]; linear_combination (-(f (p - s)⁻¹)) * E01 - y * hps'
      · simp only [hfr]; linear_combination (f (p - s)⁻¹) * E10 - z * hps'
      · linear_combination (-(w - x)) * hps'
    · rintro ⟨a, b, hab⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hab]
      have := comm_lin (gl2Map f γ : Matrix (Fin 2) (Fin 2) R) a b 0 1
      simp only [zero_smul, one_smul, zero_add] at this
      exact this.eq
  refine ⟨hset, fun g hg h hh ↦ ?_⟩
  have hg' : g ∈ (centralizerGL R γ : Set (GL (Fin 2) R)) := hg
  have hh' : h ∈ (centralizerGL R γ : Set (GL (Fin 2) R)) := hh
  rw [hset] at hg' hh'
  obtain ⟨a, b, hab⟩ := hg'
  obtain ⟨c, d, hcd⟩ := hh'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hab, hcd]
  exact (comm_lin _ a b c d).eq

/-- `G_γ(𝔸)^1 = G_γ(𝔸) ∩ G(𝔸)^1`, as a subgroup of `G(𝔸)^1`. -/
@[tf_id "II.orb.def:centralizer-norm-one"]
noncomputable def centralizerNormOne (γ : GL (Fin 2) ℚ) : Subgroup normOneGroup :=
  (centralizerGL Adele γ).subgroupOf normOneGroup

/-- `G_γ(ℚ)` as a subgroup of `G_γ(𝔸)^1`: the elements of `G_γ(𝔸)^1` that lie in `G(ℚ)` (B-only plumbing; equal to
`ι(G_γ(ℚ))` by `II.orb.thm:centralizer-rat-points`). -/
@[tf_aux "II.orb.def:centralizer-rat-norm-one"]
noncomputable def centralizerRatNormOne (γ : GL (Fin 2) ℚ) : Subgroup (centralizerNormOne γ) :=
  gl2RatNormOne.subgroupOf (centralizerNormOne γ)

namespace OrbAux

theorem gl2Map_rat_self (γ : GL (Fin 2) ℚ) : gl2Map (algebraMap ℚ ℚ) γ = γ := by
  apply Units.ext; refine Matrix.ext fun i j ↦ ?_
  rfl

theorem iota_mem_normOne (δ : GL (Fin 2) ℚ) : ι δ ∈ normOneGroup :=
  norm_one_splitting.2 ⟨δ, rfl⟩

theorem iota_mem_centralizer_iff (γ δ : GL (Fin 2) ℚ) :
    ι δ ∈ centralizerGL Adele γ ↔ δ ∈ centralizerGL ℚ γ := by
  simp only [centralizerGL, Subgroup.mem_centralizer_singleton_iff, gl2Map_rat_self, ← map_mul]
  exact gl2Rat_discrete.1.eq_iff

end OrbAux

open OrbAux

/-- (a) `ι(δ) ∈ G_γ(𝔸)` iff `δ ∈ G_γ(ℚ)`; (b) `ι(G_γ(ℚ)) ⊆ G_γ(𝔸)^1`; (c) `ι(G_γ(ℚ))` is a discrete subgroup of
`G_γ(𝔸)^1` (the subgroup `centralizerRatNormOne γ`, whose elements are exactly the `ι(δ)`, `δ ∈ G_γ(ℚ)`). -/
@[tf_id "II.orb.thm:centralizer-rat-points"]
theorem centralizer_rat_points (γ : GL (Fin 2) ℚ) :
    (∀ δ : GL (Fin 2) ℚ, ι δ ∈ centralizerGL Adele γ ↔ δ ∈ centralizerGL ℚ γ) ∧
      (∀ δ ∈ centralizerGL ℚ γ, ∃ h : ι δ ∈ normOneGroup, (⟨ι δ, h⟩ : normOneGroup) ∈ centralizerNormOne γ) ∧
      (∀ x : centralizerNormOne γ, x ∈ centralizerRatNormOne γ ↔
        ∃ δ ∈ centralizerGL ℚ γ, ι δ = ((x : normOneGroup) : GL (Fin 2) Adele)) ∧
      DiscreteTopology (centralizerRatNormOne γ) := by
  refine ⟨iota_mem_centralizer_iff γ, fun δ hδ ↦ ⟨iota_mem_normOne δ,
    Subgroup.mem_subgroupOf.mpr ((iota_mem_centralizer_iff γ δ).mpr hδ)⟩, fun x ↦ ?_, ?_⟩
  constructor
  · intro hx
    have h1 : (x : normOneGroup) ∈ gl2RatNormOne := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨δ, hδ⟩ : ((x : normOneGroup) : GL (Fin 2) Adele) ∈ gl2RatAdelic := Subgroup.mem_subgroupOf.mp h1
    have h2 : ((x : normOneGroup) : GL (Fin 2) Adele) ∈ centralizerGL Adele γ := Subgroup.mem_subgroupOf.mp x.2
    refine ⟨δ, (iota_mem_centralizer_iff γ δ).mp ?_, hδ⟩
    rw [show (ι δ) = ((x : normOneGroup) : GL (Fin 2) Adele) from hδ]
    exact h2
  · rintro ⟨δ, -, hδ⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ⟨δ, hδ⟩)
  · have := gl2RatNormOne_discrete
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : centralizerRatNormOne γ ↦ (⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩ : gl2RatNormOne))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))

/-- `G_γ(ℚ)` is discrete in `G_γ(𝔸)^1`, as an instance (B-only plumbing for `II.orb.thm:centralizer-rat-points` (c)). -/
@[tf_aux "II.orb.lem:centralizer-rat-discrete-instance"]
instance centralizerRatNormOne_discrete (γ : GL (Fin 2) ℚ) : DiscreteTopology (centralizerRatNormOne γ) := by
  have := gl2RatNormOne_discrete
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : centralizerRatNormOne γ ↦ (⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩ : gl2RatNormOne))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
  intro x y h
  have h' : x.1.1 = y.1.1 := Subtype.mk.inj h
  exact Subtype.ext (Subtype.ext h')

/-- `G_γ(𝔸)` is closed in `G(𝔸)`, `G_γ(𝔸)^1` is closed in `G(𝔸)^1`, and `G_γ(𝔸)^1` is a locally compact, Hausdorff, second
countable topological group. -/
@[tf_id "II.orb.thm:centralizer-closed"]
theorem centralizer_closed (γ : GL (Fin 2) ℚ) :
    IsClosed (centralizerGL Adele γ : Set (GL (Fin 2) Adele)) ∧
      IsClosed (centralizerNormOne γ : Set normOneGroup) ∧
      IsTopologicalGroup (centralizerNormOne γ) ∧ LocallyCompactSpace (centralizerNormOne γ) ∧
      T2Space (centralizerNormOne γ) ∧ SecondCountableTopology (centralizerNormOne γ) := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  have hA : IsClosed (centralizerGL Adele γ : Set (GL (Fin 2) Adele)) := Set.isClosed_centralizer _
  have hB : IsClosed (centralizerNormOne γ : Set normOneGroup) := hA.preimage continuous_subtype_val
  exact ⟨hA, hB, inferInstance, hB.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance,
    TopologicalSpace.Subtype.secondCountableTopology _⟩

theorem centralizerGL_adele_isClosed (γ : GL (Fin 2) ℚ) :
    IsClosed (centralizerGL Adele γ : Set (GL (Fin 2) Adele)) :=
  Set.isClosed_centralizer _

/-- `G_γ(𝔸)` is locally compact, as an instance (B-only plumbing; closed in `G(𝔸)`). -/
@[tf_aux "II.orb.lem:centralizer-locally-compact-instance"]
instance centralizerGL_locallyCompactSpace (γ : GL (Fin 2) ℚ) : LocallyCompactSpace (centralizerGL Adele γ) :=
  (centralizerGL_adele_isClosed γ).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- `G_γ(𝔸)^1` is locally compact, as an instance (B-only plumbing for `II.orb.thm:centralizer-closed`). -/
@[tf_aux "II.orb.lem:centralizer-norm-one-locally-compact-instance"]
instance centralizerNormOne_locallyCompactSpace (γ : GL (Fin 2) ℚ) : LocallyCompactSpace (centralizerNormOne γ) := by
  obtain ⟨h1, -, -⟩ := normOneGroup_topology
  have hc : IsClosed (centralizerNormOne γ : Set normOneGroup) :=
    (centralizerGL_adele_isClosed γ).preimage continuous_subtype_val
  exact hc.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- `G_γ(𝔸)^1` is second countable, as an instance (B-only plumbing for `II.orb.thm:centralizer-closed`). -/
@[tf_aux "II.orb.lem:centralizer-norm-one-second-countable-instance"]
instance centralizerNormOne_secondCountableTopology (γ : GL (Fin 2) ℚ) :
    SecondCountableTopology (centralizerNormOne γ) := by
  obtain ⟨-, -, h3⟩ := normOneGroup_topology
  exact TopologicalSpace.Subtype.secondCountableTopology _

namespace OrbAux

theorem splitComponent_comm (a : GL (Fin 2) Adele) (ha : a ∈ splitComponent) (h : GL (Fin 2) Adele) :
    a * h = h * a :=
  (Subgroup.mem_center_iff.mp (splitComponent_spec.2.1 ha) h).symm

end OrbAux

open OrbAux

/-- `A_G^+ ⊆ G_γ(𝔸)`, and `(a, g) ↦ a g` is an isomorphism of topological groups `A_G^+ × G_γ(𝔸)^1 ≅ G_γ(𝔸)` (the
restriction of the isomorphism of `I.topgrp.thm:norm-one-splitting`, which is given by the same formula). -/
@[tf_id "II.orb.thm:centralizer-norm-one-splitting"]
theorem centralizer_norm_one_splitting (γ : GL (Fin 2) ℚ) :
    splitComponent ≤ centralizerGL Adele γ ∧
      ∃ e : splitComponent × centralizerNormOne γ ≃ₜ* centralizerGL Adele γ,
        ∀ (a : splitComponent) (g : centralizerNormOne γ),
          ((e (a, g) : centralizerGL Adele γ) : GL (Fin 2) Adele) =
            (a : GL (Fin 2) Adele) * ((g : normOneGroup) : GL (Fin 2) Adele) := by
  have hle : splitComponent ≤ centralizerGL Adele γ := fun a ha ↦
    Subgroup.mem_centralizer_singleton_iff.mpr (splitComponent_comm a ha _)
  refine ⟨hle, ?_⟩
  obtain ⟨⟨e0, he0, -⟩, -⟩ := norm_one_splitting
  have hmem : ∀ (a : splitComponent) (g : centralizerNormOne γ),
      (a : GL (Fin 2) Adele) * ((g : normOneGroup) : GL (Fin 2) Adele) ∈ centralizerGL Adele γ :=
    fun a g ↦ Subgroup.mul_mem _ (hle a.2) (Subgroup.mem_subgroupOf.mp g.2)
  have hdecomp : ∀ h : GL (Fin 2) Adele,
      h = ((e0.symm h).1 : GL (Fin 2) Adele) * ((e0.symm h).2 : GL (Fin 2) Adele) := fun h ↦ by
    rw [← he0, ContinuousMulEquiv.apply_symm_apply]
  have hmem2 : ∀ h : centralizerGL Adele γ, (e0.symm (h : GL (Fin 2) Adele)).2 ∈ centralizerNormOne γ := by
    intro h
    refine Subgroup.mem_subgroupOf.mpr ?_
    have : ((e0.symm (h : GL (Fin 2) Adele)).2 : GL (Fin 2) Adele) =
        ((e0.symm (h : GL (Fin 2) Adele)).1 : GL (Fin 2) Adele)⁻¹ * h := by
      exact eq_inv_mul_of_mul_eq (hdecomp (h : GL (Fin 2) Adele)).symm
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle (e0.symm (h : GL (Fin 2) Adele)).1.2)) h.2
  let F : splitComponent × centralizerNormOne γ → centralizerGL Adele γ := fun ag ↦
    ⟨(ag.1 : GL (Fin 2) Adele) * ((ag.2 : normOneGroup) : GL (Fin 2) Adele), hmem ag.1 ag.2⟩
  let G : centralizerGL Adele γ → splitComponent × centralizerNormOne γ := fun h ↦
    ((e0.symm (h : GL (Fin 2) Adele)).1, ⟨(e0.symm (h : GL (Fin 2) Adele)).2, hmem2 h⟩)
  have hGF : ∀ ag, G (F ag) = ag := by
    rintro ⟨a, g⟩
    have : e0.symm ((a : GL (Fin 2) Adele) * ((g : normOneGroup) : GL (Fin 2) Adele)) = (a, (g : normOneGroup)) := by
      rw [← he0, ContinuousMulEquiv.symm_apply_apply]
    simp only [G, F, this]
  have hFG : ∀ h, F (G h) = h := by
    intro h
    apply Subtype.ext
    exact (hdecomp (h : GL (Fin 2) Adele)).symm
  let e : splitComponent × centralizerNormOne γ ≃* centralizerGL Adele γ :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      map_mul' := by
        rintro ⟨a, g⟩ ⟨a', g'⟩
        apply Subtype.ext
        simp only [F, Prod.mk_mul_mk, Subgroup.coe_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc ((g : normOneGroup) : GL (Fin 2) Adele),
          ← splitComponent_comm _ a'.2, mul_assoc] }
  have hFc : Continuous F := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)
  have hGc : Continuous G := by
    have h0 : Continuous fun h : centralizerGL Adele γ ↦ e0.symm (h : GL (Fin 2) Adele) :=
      e0.symm.continuous.comp continuous_subtype_val
    exact (continuous_fst.comp h0).prodMk ((continuous_snd.comp h0).subtype_mk _)
  exact ⟨{ e with continuous_toFun := hFc, continuous_invFun := hGc }, fun a g ↦ rfl⟩

namespace OrbAux

open scoped Pointwise

end OrbAux

open OrbAux

/-! ### §2 The height bound, compactness and volume (U2) -/

/-- Height bound: for `γ` elliptic and `Ω ⊆ G(𝔸)` compact there is `c` with `α(H_B(δx)) ≤ c` for all `δ ∈ G(ℚ)` and all
`x ∈ G(𝔸)^1` with `x⁻¹γx ∈ Ω`. -/
@[tf_id "II.orb.lem:elliptic-height-bound"]
theorem elliptic_height_bound (γ : GL (Fin 2) ℚ) (hγ : IsElliptic γ) (Ω : Set (GL (Fin 2) Adele))
    (hΩ : IsCompact Ω) :
    ∃ c : ℝ, ∀ δ : GL (Fin 2) ℚ, ∀ x : normOneGroup, (x : GL (Fin 2) Adele)⁻¹ * ι γ * x ∈ Ω →
      simpleRoot (heightMap (ι δ * x)) ≤ c := by
  obtain ⟨M, hM⟩ := (hΩ.image continuous_adelicEntryNorm).bddAbove
  set M' := max M 1
  refine ⟨Real.log M', fun δ x hx ↦ ?_⟩
  set y := (x : GL (Fin 2) Adele)⁻¹ * ι γ * x
  have hy : adelicEntryNorm y ≤ M' := (hM ⟨y, hx, rfl⟩).trans (le_max_left _ _)
  have hnot : δ * γ * δ⁻¹ ∉ borel ℚ := (elliptic_iff_not_borel_conjugate γ).1.mp hγ δ
  have hH := adelic_hadamard x δ (δ * γ) hnot
  have hx1 : ideleNorm (Matrix.GeneralLinearGroup.det (x : GL (Fin 2) Adele)) = 1 := x.2
  rw [hx1] at hH
  have hrow : ι (δ * γ) * x = (ι δ * x) * y := by
    simp only [y, map_mul]; group
  have hle := bottomRowNorm_mul_le (ι δ * x) y
  rw [← hrow] at hle
  set b := bottomRowNorm (ι δ * (x : GL (Fin 2) Adele))
  have hb : 0 < b := bottomRowNorm_pos _
  have hN : 0 ≤ adelicEntryNorm y := adelicEntryNorm_nonneg y
  have h1 : 1 ≤ M' * b ^ 2 := by
    calc (1 : ℝ) ≤ b * bottomRowNorm (ι (δ * γ) * x) := hH
      _ ≤ b * (adelicEntryNorm y * b) := mul_le_mul_of_nonneg_left hle hb.le
      _ ≤ b * (M' * b) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy hb.le) hb.le
      _ = M' * b ^ 2 := by ring
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlog := Real.log_le_log one_pos h1
  rw [Real.log_one, Real.log_mul hM'pos.ne' (pow_pos hb 2).ne', Real.log_pow] at hlog
  rw [simpleRoot_heightMap, ideleNorm_det_rat_mul, hx1, Real.log_one]
  push_cast at hlog
  linarith

/-- For `γ` elliptic there is `c` with `α(H_B(δx)) ≤ c` for all `x ∈ G_γ(𝔸)^1` and all `δ ∈ G(ℚ)`. -/
@[tf_id "II.orb.cor:centralizer-height-bound"]
theorem centralizer_height_bound (γ : GL (Fin 2) ℚ) (hγ : IsElliptic γ) :
    ∃ c : ℝ, ∀ x : centralizerNormOne γ, ∀ δ : GL (Fin 2) ℚ,
      simpleRoot (heightMap (ι δ * ((x : normOneGroup) : GL (Fin 2) Adele))) ≤ c := by
  obtain ⟨c, hc⟩ := elliptic_height_bound γ hγ {ι γ} isCompact_singleton
  refine ⟨c, fun x δ ↦ hc δ x ?_⟩
  have hx : ((x : normOneGroup) : GL (Fin 2) Adele) * ι γ = ι γ * ((x : normOneGroup) : GL (Fin 2) Adele) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp x.2)
  show _ = _
  rw [mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]

namespace OrbAux

theorem exists_rat_of_quot_eq (x s : normOneGroup)
    (h : Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) s =
      Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) x) :
    ∃ η : GL (Fin 2) ℚ, (x : GL (Fin 2) Adele) = ι η * s := by
  obtain ⟨η, hη⟩ := (quot_mk_eq_iff' gl2RatNormOne).mp h.symm
  obtain ⟨η₀, hη₀⟩ := gl2RatNormOne_rat η
  refine ⟨η₀, ?_⟩
  rw [hη₀, ← hη]
  rfl

end OrbAux

open OrbAux

/-- For `γ` elliptic and `Ω ⊆ G(𝔸)` compact, `p({x ∈ G(𝔸)^1 : x⁻¹γx ∈ Ω})` has compact closure in `G(ℚ)\G(𝔸)^1`. -/
@[tf_id "II.orb.thm:elliptic-support-relatively-compact"]
theorem elliptic_support_relatively_compact (γ : GL (Fin 2) ℚ) (hγ : IsElliptic γ) (Ω : Set (GL (Fin 2) Adele))
    (hΩ : IsCompact Ω) :
    IsCompact (closure (Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) ''
      {x : normOneGroup | (x : GL (Fin 2) Adele)⁻¹ * ι γ * x ∈ Ω})) := by
  obtain ⟨c, hc⟩ := elliptic_height_bound γ hγ Ω hΩ
  rw [compactness_criterion]
  refine ⟨c, fun x hx δ ↦ ?_⟩
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨η, hη⟩ := exists_rat_of_quot_eq x s hsx
  rw [hη, ← mul_assoc, ← map_mul]
  exact hc (δ * η) s hs

namespace OrbAux

theorem conj_eq_iff (γ δ δ' : GL (Fin 2) ℚ) :
    δ⁻¹ * γ * δ = δ'⁻¹ * γ * δ' ↔ δ * δ'⁻¹ ∈ centralizerGL ℚ γ := by
  rw [centralizerGL, Subgroup.mem_centralizer_singleton_iff,
    show gl2Map (algebraMap ℚ ℚ) γ = γ from Units.ext (Matrix.ext fun _ _ ↦ rfl)]
  constructor
  · intro h
    calc δ * δ'⁻¹ * γ = δ * (δ'⁻¹ * γ * δ') * δ'⁻¹ := by group
      _ = δ * (δ⁻¹ * γ * δ) * δ'⁻¹ := by rw [h]
      _ = γ * (δ * δ'⁻¹) := by group
  · intro h
    calc δ⁻¹ * γ * δ = δ⁻¹ * (γ * (δ * δ'⁻¹)) * δ' := by group
      _ = δ⁻¹ * (δ * δ'⁻¹ * γ) * δ' := by rw [h]
      _ = δ'⁻¹ * γ * δ' := by group

theorem iota_conj (γ δ : GL (Fin 2) ℚ) : (ι δ)⁻¹ * ι γ * ι δ = ι (δ⁻¹ * γ * δ) := by
  simp [map_mul, map_inv]

end OrbAux

open OrbAux

/-- For `γ ∈ G(ℚ)` and `C ⊆ G(𝔸)` compact: (a) `{δ⁻¹γδ : δ ∈ G(ℚ)} ∩ C` is finite; (b) there are `δ₁, …, δₙ ∈ G(ℚ)` with
`{δ ∈ G(ℚ) : δ⁻¹γδ ∈ C} = ⋃ᵢ G_γ(ℚ) δᵢ`. -/
@[tf_id "II.orb.lem:conjugates-meeting-compact-finite"]
theorem conjugates_meeting_compact_finite (γ : GL (Fin 2) ℚ) (C : Set (GL (Fin 2) Adele)) (hC : IsCompact C) :
    ((Set.range fun δ : GL (Fin 2) ℚ ↦ (ι δ)⁻¹ * ι γ * ι δ) ∩ C).Finite ∧
      ∃ (n : ℕ) (δs : Fin n → GL (Fin 2) ℚ),
        {δ : GL (Fin 2) ℚ | (ι δ)⁻¹ * ι γ * ι δ ∈ C} =
          {δ | ∃ i : Fin n, ∃ σ ∈ centralizerGL ℚ γ, δ = σ * δs i} := by
  obtain ⟨-, hclosed, hdisc⟩ := gl2Rat_discrete
  have hfinR : ((gl2RatAdelic : Set (GL (Fin 2) Adele)) ∩ C).Finite := by
    have hc : IsCompact (Subtype.val ⁻¹' C : Set gl2RatAdelic) :=
      hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hc.finite_of_discrete.image Subtype.val).subset ?_
    rintro g ⟨hg, hgC⟩
    exact ⟨⟨g, hg⟩, hgC, rfl⟩
  have hfin : ((Set.range fun δ : GL (Fin 2) ℚ ↦ (ι δ)⁻¹ * ι γ * ι δ) ∩ C).Finite := by
    refine hfinR.subset ?_
    rintro g ⟨⟨δ, rfl⟩, hg⟩
    exact ⟨⟨δ⁻¹ * γ * δ, (iota_conj γ δ).symm⟩, hg⟩
  refine ⟨hfin, ?_⟩
  set S := (Set.range fun δ : GL (Fin 2) ℚ ↦ (ι δ)⁻¹ * ι γ * ι δ) ∩ C
  let F := hfin.toFinset
  let enum : Fin F.card ≃ F := F.equivFin.symm
  have hmem : ∀ i : Fin F.card, (enum i : GL (Fin 2) Adele) ∈ S := fun i ↦ hfin.mem_toFinset.mp (enum i).2
  choose δs hδs0 using fun i ↦ (hmem i).1
  have hδs : ∀ i, (ι (δs i))⁻¹ * ι γ * ι (δs i) = (enum i : GL (Fin 2) Adele) := hδs0
  refine ⟨F.card, δs, Set.ext fun δ ↦ ⟨fun hδ ↦ ?_, ?_⟩⟩
  · have hS : (ι δ)⁻¹ * ι γ * ι δ ∈ S := ⟨⟨δ, rfl⟩, hδ⟩
    set i := F.equivFin ⟨_, hfin.mem_toFinset.mpr hS⟩
    have hi : (enum i : GL (Fin 2) Adele) = (ι δ)⁻¹ * ι γ * ι δ := by
      simp [enum, i]
    have heq : δ⁻¹ * γ * δ = (δs i)⁻¹ * γ * δs i := by
      apply gl2Rat_discrete.1
      rw [← iota_conj, ← iota_conj, hδs i, hi]
    exact ⟨i, δ * (δs i)⁻¹, (conj_eq_iff γ δ (δs i)).mp heq, by group⟩
  · rintro ⟨i, σ, hσ, rfl⟩
    show (ι (σ * δs i))⁻¹ * ι γ * ι (σ * δs i) ∈ C
    have heq : (σ * δs i)⁻¹ * γ * (σ * δs i) = (δs i)⁻¹ * γ * δs i :=
      (conj_eq_iff γ _ _).mpr (by rwa [mul_inv_cancel_right])
    rw [iota_conj, heq, ← iota_conj, hδs i]
    exact (hmem i).2

/-- For `γ` elliptic there is a compact `C' ⊆ G_γ(𝔸)^1` with `G_γ(𝔸)^1 = G_γ(ℚ) C'`. -/
@[tf_id "II.orb.lem:centralizer-compact-fundamental-set"]
theorem centralizer_compact_fundamental_set (γ : GL (Fin 2) ℚ) (hγ : IsElliptic γ) :
    ∃ C' : Set (centralizerNormOne γ), IsCompact C' ∧
      ∀ y : centralizerNormOne γ, ∃ σ ∈ centralizerRatNormOne γ, ∃ w ∈ C', y = σ * w := by
  obtain ⟨h1, h2, h3⟩ := normOneGroup_topology
  -- Step 1: a compact `C ⊆ G(𝔸)^1` with `G_γ(𝔸)^1 ⊆ G(ℚ) C`
  obtain ⟨c, hc⟩ := centralizer_height_bound γ hγ
  set Ωq := Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup) ''
    (Subtype.val '' (Set.univ : Set (centralizerNormOne γ)))
  have hΩq : IsCompact (closure Ωq) := by
    rw [compactness_criterion]
    refine ⟨c, fun x hx δ ↦ ?_⟩
    obtain ⟨s, ⟨y, -, rfl⟩, hsx⟩ := hx
    obtain ⟨η, hη⟩ := exists_rat_of_quot_eq x _ hsx
    rw [hη, ← mul_assoc, ← map_mul]
    exact hc y (δ * η)
  have hopen : IsOpenMap (Quotient.mk (MulAction.orbitRel gl2RatNormOne normOneGroup)) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨C, hC, hCsub⟩ := exists_compact_image_superset hopen Quotient.mk_surjective hΩq
  -- Step 2: finitely many `δᵢ`
  set Cγ : Set (GL (Fin 2) Adele) := (fun w : normOneGroup ↦ (w : GL (Fin 2) Adele) * ι γ * (w : GL (Fin 2) Adele)⁻¹) '' C
  have hCγ : IsCompact Cγ := hC.image (by fun_prop)
  obtain ⟨-, n, δs, hδs⟩ := conjugates_meeting_compact_finite γ Cγ hCγ
  have hN : ∀ i, ι (δs i) ∈ normOneGroup := fun i ↦ norm_one_splitting.2 ⟨δs i, rfl⟩
  set C' : Set (centralizerNormOne γ) :=
    ⋃ i, Subtype.val ⁻¹' ((fun w : normOneGroup ↦ (⟨ι (δs i), hN i⟩ : normOneGroup) * w) '' C)
  have hclosed : IsClosed (centralizerNormOne γ : Set normOneGroup) :=
    (centralizerGL_adele_isClosed γ).preimage continuous_subtype_val
  refine ⟨C', isCompact_iUnion fun i ↦ hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hC.image (continuous_const_mul _)), fun y ↦ ?_⟩
  obtain ⟨w, hwC, hwy⟩ := hCsub (subset_closure ⟨_, ⟨y, trivial, rfl⟩, rfl⟩)
  obtain ⟨δ, hδ⟩ := exists_rat_of_quot_eq _ _ hwy
  have hyc : ((y : normOneGroup) : GL (Fin 2) Adele) * ι γ = ι γ * ((y : normOneGroup) : GL (Fin 2) Adele) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp y.2)
  have hconj : (ι δ)⁻¹ * ι γ * ι δ ∈ Cγ := by
    refine ⟨w, hwC, ?_⟩
    have hδ' : ι δ = ((y : normOneGroup) : GL (Fin 2) Adele) * (w : GL (Fin 2) Adele)⁻¹ := by
      rw [hδ]; group
    rw [hδ']
    calc (w : GL (Fin 2) Adele) * ι γ * (w : GL (Fin 2) Adele)⁻¹
        = (w : GL (Fin 2) Adele) * (((y : normOneGroup) : GL (Fin 2) Adele)⁻¹ *
            (((y : normOneGroup) : GL (Fin 2) Adele) * ι γ)) * (w : GL (Fin 2) Adele)⁻¹ := by group
      _ = _ := by rw [hyc]; group
  have hmemδ : δ ∈ {δ : GL (Fin 2) ℚ | (ι δ)⁻¹ * ι γ * ι δ ∈ Cγ} := hconj
  rw [hδs] at hmemδ
  obtain ⟨i, σ, hσ, rfl⟩ := hmemδ
  obtain ⟨hσN, hσC⟩ := (centralizer_rat_points γ).2.1 σ hσ
  set σ' : centralizerNormOne γ := ⟨⟨ι σ, hσN⟩, hσC⟩
  have hσ' : σ' ∈ centralizerRatNormOne γ := ((centralizer_rat_points γ).2.2.1 σ').mpr ⟨σ, hσ, rfl⟩
  refine ⟨σ', hσ', σ'⁻¹ * y, Set.mem_iUnion.mpr ⟨i, w, hwC, ?_⟩, by group⟩
  apply Subtype.ext
  show ι (δs i) * (w : GL (Fin 2) Adele) = (ι σ)⁻¹ * ((y : normOneGroup) : GL (Fin 2) Adele)
  rw [hδ, map_mul]; group

/-- For `γ` elliptic, `G_γ(ℚ)\G_γ(𝔸)^1` (quotient topology) is compact. -/
@[tf_id "II.orb.thm:elliptic-centralizer-compact"]
theorem elliptic_centralizer_compact (γ : GL (Fin 2) ℚ) (hγ : IsElliptic γ) :
    CompactSpace (MulAction.orbitRel.Quotient (centralizerRatNormOne γ) (centralizerNormOne γ)) := by
  obtain ⟨C', hC', hcov⟩ := centralizer_compact_fundamental_set γ hγ
  refine ⟨(hC'.image continuous_quotient_mk').of_isClosed_subset isClosed_univ fun q _ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective q
  obtain ⟨σ, hσ, w, hw, rfl⟩ := hcov y
  exact ⟨w, hw, ((quot_mk_eq_iff' _).mpr ⟨⟨σ, hσ⟩, rfl⟩).symm⟩

end GL2TF
