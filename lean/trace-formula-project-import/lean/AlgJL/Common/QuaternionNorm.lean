import AlgJL.Meta.Tag
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Determinant

/-!
# Quaternion algebras `B_R(a, b)`, reduced norm and reduced trace (Q2 U1, items 1–6)

Lean counterpart of `vol3/ch-iii-06-quatalg.tex` §1 (items 1–6 of `docs/sprints/Q2-plan.md` §1.2).

Design (plan §1.1 items 1–2):
* `a b : ℤ` throughout; for a commutative ring `R`, `B_R(a, b) := ℍ[R, a, 0, b]` (Mathlib's `QuaternionAlgebra`, so
  `i² = a`, `j² = b`, `ij = −ji = k`); `B := B_ℚ` is written `QuatAlg ℚ a b` inline;
* base change `B_R → B_S` along a ring hom `R → S` is coordinatewise (`baseChange`, B-only plumbing);
* `nrd` and `trd` are defined once, over any commutative ring `R`; conjugation `x̄` is Mathlib's `star`.

No project notation (plan §1.3). No topology on `QuatAlg` (plan trap 3). Owner: L1T (Q2).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-- The quaternion algebra `B_R(a, b) := ℍ[R, a, 0, b]` over a commutative ring `R`, for `a b : ℤ`: basis `1, i, j, k`
with `i² = a`, `j² = b`, `ij = −ji = k`. The rational algebra is `B = QuatAlg ℚ a b`. -/
@[tf_id "III.qalg.def:quaternion-algebra"]
abbrev QuatAlg (R : Type*) [CommRing R] (a b : ℤ) : Type _ :=
  QuaternionAlgebra R (a : R) 0 (b : R)

/-- Base change `B_R(a, b) → B_S(a, b)` along a ring hom `f : R → S`, coordinatewise in the basis `1, i, j, k`. -/
@[tf_aux "III.qalg.def:quaternion-base-change"]
def baseChange {R S : Type*} [CommRing R] [CommRing S] (a b : ℤ) (f : R →+* S) :
    QuatAlg R a b →+* QuatAlg S a b where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-- The reduced norm `nrd : B_R → R`, `nrd(x) = x₀² − a x₁² − b x₂² + ab x₃²`. -/
@[tf_id "III.qalg.def:reduced-norm"]
def nrd {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) : R :=
  x.re ^ 2 - (a : R) * x.imI ^ 2 - (b : R) * x.imJ ^ 2 + (a : R) * (b : R) * x.imK ^ 2

/-- The reduced trace `trd : B_R → R`, `trd(x) = 2 x₀`. -/
@[tf_id "III.qalg.def:reduced-trace"]
def trd {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) : R :=
  2 * x.re

private theorem mul_star_eq_nrd {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) :
    x * star x = algebraMap R (QuatAlg R a b) (nrd x) := by
  ext <;> simp [nrd, QuaternionAlgebra.algebraMap_eq] <;> ring

private theorem star_mul_eq_nrd {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) :
    star x * x = algebraMap R (QuatAlg R a b) (nrd x) := by
  ext <;> simp [nrd, QuaternionAlgebra.algebraMap_eq] <;> ring

private theorem nrd_mul' {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) :
    nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

private theorem nrd_one' {R : Type*} [CommRing R] {a b : ℤ} : nrd (1 : QuatAlg R a b) = 1 := by
  simp [nrd]

/-- Basic identities: `x x̄ = x̄ x = nrd(x)`, `x + x̄ = trd(x)`, `x² − trd(x) x + nrd(x) = 0`; `nrd` is multiplicative;
`trd(xy) = trd(yx)`; `nrd` and `trd` commute with base change. -/
@[tf_id "III.qalg.lem:reduced-norm-basic"]
theorem nrd_trd_basic {R : Type*} [CommRing R] {a b : ℤ} :
    (∀ x : QuatAlg R a b,
      x * star x = algebraMap R (QuatAlg R a b) (nrd x) ∧
      star x * x = algebraMap R (QuatAlg R a b) (nrd x) ∧
      x + star x = algebraMap R (QuatAlg R a b) (trd x) ∧
      x ^ 2 - trd x • x + algebraMap R (QuatAlg R a b) (nrd x) = 0) ∧
    (∀ x y : QuatAlg R a b, nrd (x * y) = nrd x * nrd y) ∧
    (∀ x y : QuatAlg R a b, trd (x * y) = trd (y * x)) ∧
    (∀ (S : Type*) [CommRing S] (f : R →+* S) (x : QuatAlg R a b),
      nrd (baseChange a b f x) = f (nrd x) ∧ trd (baseChange a b f x) = f (trd x)) := by
  refine ⟨fun x => ⟨mul_star_eq_nrd x, star_mul_eq_nrd x, ?_, ?_⟩, nrd_mul', fun x y => ?_,
    fun S _ f x => ⟨?_, ?_⟩⟩
  · ext <;> simp [trd, QuaternionAlgebra.algebraMap_eq]; ring
  · ext <;> simp [nrd, trd, pow_two, QuaternionAlgebra.algebraMap_eq] <;> ring
  · simp [trd]; ring
  · simp [nrd, baseChange]
  · simp [trd, baseChange, map_ofNat]

/-- `x ∈ B_R` is a unit iff `nrd(x) ∈ R^×`; then `x⁻¹ = nrd(x)⁻¹ x̄`. -/
@[tf_id "III.qalg.lem:unit-iff-reduced-norm-unit"]
theorem isUnit_iff_isUnit_nrd {R : Type*} [CommRing R] {a b : ℤ} :
    (∀ x : QuatAlg R a b, IsUnit x ↔ IsUnit (nrd x)) ∧
    (∀ (u : (QuatAlg R a b)ˣ) (v : Rˣ), (v : R) = nrd (u : QuatAlg R a b) →
      ((u⁻¹ : (QuatAlg R a b)ˣ) : QuatAlg R a b) = ((v⁻¹ : Rˣ) : R) • star (u : QuatAlg R a b)) := by
  have key : ∀ (x : QuatAlg R a b) (v : Rˣ), (v : R) = nrd x →
      x * (((v⁻¹ : Rˣ) : R) • star x) = 1 ∧ (((v⁻¹ : Rˣ) : R) • star x) * x = 1 := by
    intro x v hv
    refine ⟨?_, ?_⟩
    · rw [mul_smul_comm, mul_star_eq_nrd, ← hv, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
    · rw [smul_mul_assoc, star_mul_eq_nrd, ← hv, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun u v hv => ?_⟩
  · let φ : QuatAlg R a b →* R := ⟨⟨nrd, nrd_one'⟩, nrd_mul'⟩
    exact hx.map φ
  · obtain ⟨v, hv⟩ := hx
    obtain ⟨h1, h2⟩ := key x v hv
    exact ⟨⟨x, _, h1, h2⟩, rfl⟩
  · exact (Units.eq_inv_of_mul_eq_one_left (key u v hv).1).symm

/-- Over a field `F`, left multiplication `y ↦ xy` on `B_F` has determinant `nrd(x)²`, and so has right
multiplication `y ↦ yx`. -/
@[tf_id "III.qalg.lem:left-multiplication-det"]
theorem det_mulLeft_mulRight {F : Type*} [Field F] {a b : ℤ} (x : QuatAlg F a b) :
    LinearMap.det (LinearMap.mulLeft F x) = nrd x ^ 2 ∧
    LinearMap.det (LinearMap.mulRight F x) = nrd x ^ 2 := by
  constructor
  · rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK _ _ _)]
    have h : LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (a : F) 0 (b : F))
        (QuaternionAlgebra.basisOneIJK (a : F) 0 (b : F)) (LinearMap.mulLeft F x) =
        !![x.re, a * x.imI, b * x.imJ, -(a * b) * x.imK;
           x.imI, x.re, b * x.imK, -b * x.imJ;
           x.imJ, -a * x.imK, x.re, a * x.imI;
           x.imK, -x.imJ, x.imI, x.re] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, QuaternionAlgebra.basisOneIJK]
    rw [h, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, nrd, Fin.succAbove]
    ring
  · rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK _ _ _)]
    have h : LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (a : F) 0 (b : F))
        (QuaternionAlgebra.basisOneIJK (a : F) 0 (b : F)) (LinearMap.mulRight F x) =
        !![x.re, a * x.imI, b * x.imJ, -(a * b) * x.imK;
           x.imI, x.re, -b * x.imK, b * x.imJ;
           x.imJ, a * x.imK, x.re, -a * x.imI;
           x.imK, x.imJ, -x.imI, x.re] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, QuaternionAlgebra.basisOneIJK]
    rw [h, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, nrd, Fin.succAbove]
    ring

end GL2TF.Quat
