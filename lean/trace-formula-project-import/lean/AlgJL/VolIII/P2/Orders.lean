import AlgJL.Meta.Tag
import AlgJL.Common.QuaternionNorm
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Data.Int.Interval
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Orders, maximal orders, level structures and Eichler orders (Q2 U4)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §§1–2 (items 21–33, 35, 36 of `docs/sprints/Q2-plan.md` §1.2).

* `QOrder a b`: an order of `B = QuatAlg ℚ a b = ℍ[ℚ, a, 0, b]` (a, b ∈ ℤ), bundled: a `Subalgebra ℤ B` that is finitely generated as
  a ℤ-module and spans `B` over `ℚ` (plan §1.1 item 4).
* `IsMaximalOrder`, `MaxOrder a b` (a subtype).
* `LevelStructure O M`: a surjective ring hom `O → M₂(ℤ/M)`, `M ≥ 1` (as `[NeZero M]`).
* `eichlerOrder φ`: `O(M; φ) = {x ∈ O : φ(x)₂₁ = 0}` (plan §1.1 item 5).
* `unitGroup O`: `O^×` as a subgroup of `Bˣ`.

Owner: L2T (Q2, TITAN).
-/

set_option autoImplicit false

open scoped Quaternion

namespace GL2TF.Quat

/-! ## §1 Orders -/

/-- An order of `B = ℍ[ℚ, a, 0, b]`: a subring `O ⊆ B` which is a lattice, i.e. a finitely generated ℤ-submodule with
`ℚ O = B`. Bundled data; the Prop fields `fg` and `span_eq_top` are registry fields (plan §1.3). -/
@[tf_id "III.qord.def:order"]
structure QOrder (a b : ℤ) where
  /-- The underlying subring, as a ℤ-subalgebra of `B`. -/
  toSubalgebra : Subalgebra ℤ (QuatAlg ℚ a b)
  /-- `O` is finitely generated as a ℤ-module. -/
  fg : (Subalgebra.toSubmodule toSubalgebra).FG
  /-- `O` spans `B` over `ℚ`. -/
  span_eq_top : Submodule.span ℚ (toSubalgebra : Set (QuatAlg ℚ a b)) = ⊤

/-- Proof helper: a ℤ-submodule contained in a finitely generated one is finitely generated. -/
theorem fg_of_le_fg {V : Type*} [AddCommGroup V] [Module ℤ V] {N P : Submodule ℤ V} (hP : P.FG) (h : N ≤ P) :
    N.FG := by
  exact isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian P hP) N h

/-- The ℤ-subalgebra of `B` of elements with integral coordinates in the basis `1, i, j, k`. -/
@[tf_aux "III.qord.def:standard-order-subalgebra"]
def standardSubalgebra (a b : ℤ) : Subalgebra ℤ (QuatAlg ℚ a b) where
  carrier := {x | (∃ n : ℤ, x.re = n) ∧ (∃ n : ℤ, x.imI = n) ∧ (∃ n : ℤ, x.imJ = n) ∧ (∃ n : ℤ, x.imK = n)}
  mul_mem' := by
    rintro ⟨x0, x1, x2, x3⟩ ⟨y0, y1, y2, y3⟩ ⟨⟨m0, h0⟩, ⟨m1, h1⟩, ⟨m2, h2⟩, ⟨m3, h3⟩⟩
      ⟨⟨n0, k0⟩, ⟨n1, k1⟩, ⟨n2, k2⟩, ⟨n3, k3⟩⟩
    simp only at h0 h1 h2 h3 k0 k1 k2 k3
    subst h0 h1 h2 h3 k0 k1 k2 k3
    refine ⟨⟨m0 * n0 + a * m1 * n1 + b * m2 * n2 - a * b * m3 * n3, ?_⟩,
      ⟨m0 * n1 + m1 * n0 - b * m2 * n3 + b * m3 * n2, ?_⟩,
      ⟨m0 * n2 + a * m1 * n3 + m2 * n0 - a * m3 * n1, ?_⟩,
      ⟨m0 * n3 + m1 * n2 - m2 * n1 + m3 * n0, ?_⟩⟩ <;>
    simp [QuaternionAlgebra.mk_mul_mk]
  add_mem' := by
    rintro x y ⟨⟨m0, h0⟩, ⟨m1, h1⟩, ⟨m2, h2⟩, ⟨m3, h3⟩⟩ ⟨⟨n0, k0⟩, ⟨n1, k1⟩, ⟨n2, k2⟩, ⟨n3, k3⟩⟩
    exact ⟨⟨m0 + n0, by simp [h0, k0]⟩, ⟨m1 + n1, by simp [h1, k1]⟩, ⟨m2 + n2, by simp [h2, k2]⟩,
      ⟨m3 + n3, by simp [h3, k3]⟩⟩
  algebraMap_mem' := by
    intro r
    refine ⟨⟨r, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp

/-- Proof helper: membership in the standard subalgebra. -/
theorem mem_standardSubalgebra {a b : ℤ} {x : (QuatAlg ℚ a b)} :
    x ∈ standardSubalgebra a b ↔
      (∃ n : ℤ, x.re = n) ∧ (∃ n : ℤ, x.imI = n) ∧ (∃ n : ℤ, x.imJ = n) ∧ (∃ n : ℤ, x.imK = n) :=
  Iff.rfl

/-- Proof helper: an element with integral coordinates is a ℤ-combination of `1, i, j, k`. -/
theorem standardSubalgebra_le_span (a b : ℤ) :
    Subalgebra.toSubmodule (standardSubalgebra a b) ≤
      Submodule.span ℤ ({⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩} :
        Set (QuatAlg ℚ a b)) := by
  rintro x ⟨⟨m0, h0⟩, ⟨m1, h1⟩, ⟨m2, h2⟩, ⟨m3, h3⟩⟩
  have hx : x = m0 • (⟨1, 0, 0, 0⟩ : (QuatAlg ℚ a b)) + m1 • ⟨0, 1, 0, 0⟩ + m2 • ⟨0, 0, 1, 0⟩ +
      m3 • ⟨0, 0, 0, 1⟩ := by
    ext <;> simp [h0, h1, h2, h3]
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_) <;>
  exact Submodule.subset_span (by simp)

/-- The standard order `ℤ⟨1, i, j, k⟩` of `B = ℍ[ℚ, a, 0, b]` (a, b ∈ ℤ). -/
@[tf_id "III.qord.def:standard-order"]
noncomputable def standardOrder (a b : ℤ) : QOrder a b where
  toSubalgebra := standardSubalgebra a b
  fg := fg_of_le_fg (Submodule.fg_span (Set.toFinite _)) (standardSubalgebra_le_span a b)
  span_eq_top := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hmem : ∀ y ∈ standardSubalgebra a b, y ∈ Submodule.span ℚ
        ((standardSubalgebra a b : Subalgebra ℤ (QuatAlg ℚ a b)) : Set (QuatAlg ℚ a b)) :=
      fun y hy => Submodule.subset_span hy
    have hx : x = x.re • (⟨1, 0, 0, 0⟩ : (QuatAlg ℚ a b)) + x.imI • ⟨0, 1, 0, 0⟩ +
        x.imJ • ⟨0, 0, 1, 0⟩ + x.imK • ⟨0, 0, 0, 1⟩ := by
      ext <;> simp
    rw [hx]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _ ?_))
      (Submodule.smul_mem _ _ (hmem _ ?_))) (Submodule.smul_mem _ _ (hmem _ ?_)))
      (Submodule.smul_mem _ _ (hmem _ ?_)) <;>
    exact ⟨⟨_, by simp; rfl⟩ , ⟨_, by simp; rfl⟩, ⟨_, by simp; rfl⟩, ⟨_, by simp; rfl⟩⟩

/-- Proof helper: `x² − trd(x) x + nrd(x) = 0` in `B`. -/
theorem quad_rel {a b : ℤ} (x : QuatAlg ℚ a b) :
    x ^ 2 - trd x • x + algebraMap ℚ (QuatAlg ℚ a b) (nrd x) = 0 := by
  ext <;> simp [trd, nrd, sq] <;> ring

open Polynomial in
/-- Proof helper: the proof of `trd_nrd_int_of_mem` (integrality via the minimal polynomial). -/
theorem trd_nrd_int_of_mem_aux {a b : ℤ} (O : QOrder a b) {x : QuatAlg ℚ a b} (hx : x ∈ O.toSubalgebra) :
    (∃ n : ℤ, trd x = n) ∧ (∃ n : ℤ, nrd x = n) := by
  have hint : IsIntegral ℤ x := IsIntegral.of_mem_of_fg O.toSubalgebra O.fg x hx
  have hxq : IsIntegral ℚ x := hint.tower_top
  obtain ⟨P, hPm, hP⟩ := hint
  have hdvd : minpoly ℚ x ∣ P.map (algebraMap ℤ ℚ) :=
    minpoly.dvd ℚ x (by rw [aeval_map_algebraMap, aeval_def]; exact hP)
  have hcoeff : ∀ i, ∃ n : ℤ, (minpoly ℚ x).coeff i = n := fun i => by
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (Polynomial.isIntegral_coeff_of_dvd P _ hPm (minpoly.monic hxq) hdvd i)
    exact ⟨n, by rw [← hn, eq_intCast]⟩
  by_cases hr : x ∈ (algebraMap ℚ (QuatAlg ℚ a b)).range
  · obtain ⟨q, rfl⟩ := hr
    obtain ⟨n, hn⟩ := hcoeff 0
    rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at hn
    have hq : q = ((-n : ℤ) : ℚ) := by rw [Int.cast_neg, ← hn, neg_neg]
    refine ⟨⟨2 * (-n), ?_⟩, ⟨(-n) ^ 2, ?_⟩⟩ <;> simp [trd, nrd, hq]
  · set Q : ℚ[X] := X ^ 2 - C (trd x) * X + C (nrd x) with hQ
    have hQdeg : Q.natDegree = 2 := by rw [hQ]; compute_degree!
    have hQm : Q.Monic := by rw [hQ]; monicity!
    have hQx : aeval x Q = 0 := by
      rw [hQ]; simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
      rw [← quad_rel x, Algebra.smul_def]
    have h2 : 2 ≤ (minpoly ℚ x).natDegree := (minpoly.two_le_natDegree_iff hxq).mpr hr
    have heq : Q = minpoly ℚ x :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxq) hQm (minpoly.dvd ℚ x hQx)
        (by rw [hQdeg]; exact h2)
    obtain ⟨n1, hn1⟩ := hcoeff 1
    obtain ⟨n0, hn0⟩ := hcoeff 0
    rw [← heq, hQ] at hn1 hn0
    simp at hn1 hn0
    exact ⟨⟨-n1, by rw [Int.cast_neg, ← hn1, neg_neg]⟩, ⟨n0, hn0⟩⟩


/-- Elements of an order are integral: `x ∈ O ⇒ trd(x), nrd(x) ∈ ℤ`. -/
@[tf_id "III.qord.lem:order-integral"]
theorem trd_nrd_int_of_mem {a b : ℤ} (O : QOrder a b) {x : QuatAlg ℚ a b} (hx : x ∈ O.toSubalgebra) :
    (∃ n : ℤ, trd x = n) ∧ (∃ n : ℤ, nrd x = n) := by
  exact trd_nrd_int_of_mem_aux O hx

/-- Proof helper: expansion of an element of a ℤ-submodule `L` in a ℤ-basis, in the ambient group. -/
theorem val_eq_sum_repr {V : Type*} [AddCommGroup V] {L : Submodule ℤ V} {ι : Type} [Fintype ι]
    (e : Module.Basis ι ℤ L) (x : L) :
    (x : V) = ∑ k, e.repr x k • (e k : V) := by
  have := congrArg L.subtype (e.sum_repr x)
  rw [map_sum] at this
  simp only [map_zsmul, Submodule.subtype_apply] at this
  exact this.symm

/-- Proof helper: a ℤ-basis of a ℤ-submodule `L ⊆ B` with `ℚ L = B` is a ℚ-basis of `B`. -/
theorem exists_rat_basis_of_basis {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b))
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) {ι : Type} (e : Module.Basis ι ℤ L) :
    ∃ f : Module.Basis ι ℚ (QuatAlg ℚ a b), ∀ i, f i = (e i : QuatAlg ℚ a b) := by
  have li : LinearIndependent ℤ (fun i => (e i : QuatAlg ℚ a b)) :=
    e.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have li' : LinearIndependent ℚ (fun i => (e i : QuatAlg ℚ a b)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp li
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range (fun i => (e i : QuatAlg ℚ a b))) := by
    rw [← hspan]
    refine Submodule.span_le.mpr fun x hx => ?_
    have h1 : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range e) := e.mem_span _
    have h2 := Submodule.mem_map_of_mem (f := L.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h2
  exact ⟨Module.Basis.mk li' hsp, fun i => Module.Basis.mk_apply _ _ _⟩

/-- Proof helper: a lattice `L ⊆ B` (finitely generated, `ℚ L = B`) has a ℤ-basis indexed by `Fin 4`, which is also a
ℚ-basis of `B`. -/
theorem exists_lattice_basis {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) :
    ∃ e : Module.Basis (Fin 4) ℤ L, ∃ f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b),
      ∀ i, f i = (e i : QuatAlg ℚ a b) := by
  have : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  let e0 := Module.Free.chooseBasis ℤ L
  obtain ⟨f0, hf0⟩ := exists_rat_basis_of_basis L hspan e0
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 4 := by
    rw [← Module.finrank_eq_card_basis f0]
    exact QuaternionAlgebra.finrank_eq_four _ _ _
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨e0.reindex eqv, f0.reindex eqv, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hf0]

/-- Proof helper: membership in a lattice `L` with ℤ-basis `e` (also a ℚ-basis `f`) is integrality of coordinates. -/
theorem mem_lattice_iff_repr {V : Type*} [AddCommGroup V] [Module ℚ V] {L : Submodule ℤ V}
    {ι : Type} [Fintype ι] (e : Module.Basis ι ℤ L) (f : Module.Basis ι ℚ V) (hf : ∀ i, f i = (e i : V)) (z : V) :
    z ∈ L ↔ ∀ i, ∃ n : ℤ, f.repr z i = n := by
  constructor
  · intro hz i
    refine ⟨e.repr ⟨z, hz⟩ i, ?_⟩
    have h2 : z = ∑ k, e.repr ⟨z, hz⟩ k • (e k : V) := val_eq_sum_repr e ⟨z, hz⟩
    have h3 : z = ∑ k, ((e.repr ⟨z, hz⟩ k : ℤ) : ℚ) • f k := by
      conv_lhs => rw [h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hf, Int.cast_smul_eq_zsmul]
    conv_lhs => rw [h3]
    rw [Module.Basis.repr_sum_self]
  · intro h
    choose n hn using h
    rw [← f.sum_repr z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hn i, Int.cast_smul_eq_zsmul, hf]
    exact Submodule.smul_mem _ _ (e i).2

/-- An order is a free ℤ-module of rank 4, and every ℤ-basis of `O` is a ℚ-basis of `B`. B-only. -/
@[tf_aux "III.qord.lem:order-free-rank-four"]
theorem order_free_rank_four {a b : ℤ} (O : QOrder a b) :
    Module.Free ℤ (Subalgebra.toSubmodule O.toSubalgebra) ∧
      Module.finrank ℤ (Subalgebra.toSubmodule O.toSubalgebra) = 4 ∧
      ∀ {ι : Type} [Fintype ι] (e : Module.Basis ι ℤ (Subalgebra.toSubmodule O.toSubalgebra)),
        ∃ f : Module.Basis ι ℚ (QuatAlg ℚ a b), ∀ i, f i = (e i : QuatAlg ℚ a b) := by
  have : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
  have : Module.Finite ℤ (Subalgebra.toSubmodule O.toSubalgebra) := Module.Finite.iff_fg.mpr O.fg
  obtain ⟨e, -, -⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  refine ⟨Module.free_of_finite_type_torsion_free', ?_, fun e' => exists_rat_basis_of_basis _ O.span_eq_top e'⟩
  rw [Module.finrank_eq_card_basis e, Fintype.card_fin]

/-- The discriminant `d(O) := det(trd(e_i ē_j))_{i,j}` for a ℤ-basis `(e_i)` of `O` (here the basis chosen by
`Module.Free.chooseBasis`; independence of the basis is `discriminant_basic`). A rational number; it is an integer
by `discriminant_basic`. -/
@[tf_id "III.qord.def:discriminant"]
noncomputable def discriminant {a b : ℤ} (O : QOrder a b) : ℚ :=
  letI : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
  letI : Module.Finite ℤ (Subalgebra.toSubmodule O.toSubalgebra) := Module.Finite.iff_fg.mpr O.fg
  (Matrix.of fun i j : Module.Free.ChooseBasisIndex ℤ (Subalgebra.toSubmodule O.toSubalgebra) =>
    trd ((Module.Free.chooseBasis ℤ (Subalgebra.toSubmodule O.toSubalgebra) i : QuatAlg ℚ a b) *
      star (Module.Free.chooseBasis ℤ (Subalgebra.toSubmodule O.toSubalgebra) j : QuatAlg ℚ a b))).det

/-- Proof helper: `x + x̄ = trd(x)`. -/
theorem add_star_eq_trd {a b : ℤ} (x : QuatAlg ℚ a b) : x + star x = algebraMap ℚ (QuatAlg ℚ a b) (trd x) := by
  ext <;> simp [trd, Algebra.algebraMap_eq_smul_one] <;> ring

/-- Proof helper: an order is closed under conjugation. -/
theorem star_mem_order {a b : ℤ} (O : QOrder a b) {x : QuatAlg ℚ a b} (hx : x ∈ O.toSubalgebra) :
    star x ∈ O.toSubalgebra := by
  obtain ⟨⟨n, hn⟩, -⟩ := trd_nrd_int_of_mem O hx
  have : star x = algebraMap ℤ (QuatAlg ℚ a b) n - x := by
    rw [eq_sub_iff_add_eq, add_comm, add_star_eq_trd, hn, eq_intCast, map_intCast]
  rw [this]
  exact O.toSubalgebra.sub_mem (O.toSubalgebra.algebraMap_mem n) hx

/-- Proof helper: the trace form `(x, y) ↦ trd(x ȳ)` as a ℚ-bilinear map. -/
theorem exists_trdForm (a b : ℤ) :
    ∃ β : QuatAlg ℚ a b →ₗ[ℚ] QuatAlg ℚ a b →ₗ[ℚ] ℚ, ∀ x y, β x y = trd (x * star y) := by
  refine ⟨LinearMap.mk₂ ℚ (fun x y => trd (x * star y)) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩ <;>
    intros <;> simp [trd] <;> ring

/-- Proof helper: a rational matrix with integral entries has integral determinant. -/
theorem det_isInt_of_entries {κ : Type} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℚ)
    (h : ∀ i j, ∃ n : ℤ, A i j = n) : ∃ n : ℤ, A.det = n := by
  choose N hN using h
  refine ⟨(Matrix.of N).det, ?_⟩
  have : A = (Matrix.of N).map (Int.castRingHom ℚ) := by ext i j; simp [hN]
  rw [this]; exact (RingHom.map_det (Int.castRingHom ℚ) _).symm

/-- Proof helper: change of basis for the Gram determinant of the trace form. -/
theorem det_gram_change {a b : ℤ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (f f' : Module.Basis κ ℚ (QuatAlg ℚ a b)) :
    (Matrix.of fun i j => trd (f' i * star (f' j))).det =
      (f.toMatrix f').det ^ 2 * (Matrix.of fun i j => trd (f i * star (f j))).det := by
  obtain ⟨β, hβ⟩ := exists_trdForm a b
  have h := LinearMap.toMatrix₂_mul_basis_toMatrix f f f' f' β
  have e1 : (Matrix.of fun i j => trd (f' i * star (f' j))) = LinearMap.toMatrix₂ f' f' β := by
    ext i j; simp [LinearMap.toMatrix₂_apply, hβ]
  have e2 : (Matrix.of fun i j => trd (f i * star (f j))) = LinearMap.toMatrix₂ f f β := by
    ext i j; simp [LinearMap.toMatrix₂_apply, hβ]
  rw [e1, e2, ← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Proof helper: the Gram determinant of the trace form in the basis `1, i, j, k` is `16 a² b²`. -/
theorem det_gram_basisOneIJK (a b : ℤ) :
    (Matrix.of fun i j => trd (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) i *
      star (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) j))).det = 16 * (a : ℚ) ^ 2 * (b : ℚ) ^ 2 := by
  have : (Matrix.of fun i j => trd (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) i *
      star (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) j))) =
      Matrix.diagonal ![2, -2 * (a : ℚ), -2 * (b : ℚ), 2 * (a : ℚ) * (b : ℚ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trd, QuaternionAlgebra.basisOneIJK, Module.Basis.ofEquivFun, Matrix.diagonal] <;> ring
  rw [this, Matrix.det_diagonal, Fin.prod_univ_four]
  simp
  ring

/-- The discriminant is independent of the ℤ-basis, it is an integer, and it is positive for definite `B`. -/
@[tf_aux "III.qord.lem:discriminant-basic"]
theorem discriminant_basic {a b : ℤ} (O : QOrder a b) :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℤ (Subalgebra.toSubmodule O.toSubalgebra)),
      discriminant O = (Matrix.of fun i j : ι =>
        trd ((e i : QuatAlg ℚ a b) * star (e j : QuatAlg ℚ a b))).det) ∧
    (∃ n : ℤ, discriminant O = n) ∧
    (a < 0 → b < 0 → 0 < discriminant O) := by
  have : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
  have : Module.Finite ℤ (Subalgebra.toSubmodule O.toSubalgebra) := Module.Finite.iff_fg.mpr O.fg
  set L := Subalgebra.toSubmodule O.toSubalgebra with hL
  set e0 := Module.Free.chooseBasis ℤ L with he0
  obtain ⟨f0, hf0⟩ := exists_rat_basis_of_basis L O.span_eq_top e0
  have hdisc : discriminant O = (Matrix.of fun i j => trd (f0 i * star (f0 j))).det := by
    simp only [discriminant, hf0]; rfl
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 4 := by
    rw [← Module.finrank_eq_card_basis f0]; exact QuaternionAlgebra.finrank_eq_four _ _ _
  refine ⟨fun {ι} _ _ e => ?_, ?_, fun ha hb => ?_⟩
  · have hcι : Fintype.card ι = Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
      rw [← Module.finrank_eq_card_basis e, ← Module.finrank_eq_card_basis e0]
    let σ : ι ≃ Module.Free.ChooseBasisIndex ℤ L := Fintype.equivOfCardEq hcι
    let e1 := e.reindex σ
    have hre : (Matrix.of fun i j : ι => trd ((e i : QuatAlg ℚ a b) * star (e j : QuatAlg ℚ a b))).det =
        (Matrix.of fun i j => trd ((e1 i : QuatAlg ℚ a b) * star (e1 j : QuatAlg ℚ a b))).det := by
      rw [← Matrix.det_reindex_self σ]
      congr 1
      ext i j
      simp [e1, Matrix.reindex_apply, Module.Basis.reindex_apply]
    rw [hre]
    obtain ⟨f1, hf1⟩ := exists_rat_basis_of_basis L O.span_eq_top e1
    have hg : (Matrix.of fun i j => trd ((e1 i : QuatAlg ℚ a b) * star (e1 j : QuatAlg ℚ a b))) =
        Matrix.of fun i j => trd (f1 i * star (f1 j)) := by
      ext i j; simp [hf1]
    rw [hg, det_gram_change f0 f1, hdisc]
    -- the change of basis has determinant ±1
    have hint : ∀ (g g' : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℚ (QuatAlg ℚ a b))
        (eg : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L) (_ : ∀ i, g i = (eg i : QuatAlg ℚ a b))
        (eg' : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L) (_ : ∀ i, g' i = (eg' i : QuatAlg ℚ a b)),
        ∃ n : ℤ, (g.toMatrix g').det = n := by
      intro g g' eg hg eg' hg'
      refine det_isInt_of_entries _ fun i j => ?_
      rw [Module.Basis.toMatrix_apply]
      exact (mem_lattice_iff_repr eg g hg _).mp (by rw [hg']; exact (eg' j).2) i
    obtain ⟨n, hn⟩ := hint f0 f1 e0 hf0 e1 hf1
    obtain ⟨m, hm⟩ := hint f1 f0 e1 hf1 e0 hf0
    have hnm : (n : ℚ) * m = 1 := by
      rw [← hn, ← hm, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    have hnm' : n * m = 1 := by exact_mod_cast hnm
    have hsq : (n : ℚ) ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm' with h | h <;> simp [h]
    rw [hn, hsq, one_mul]
  · rw [hdisc]
    refine det_isInt_of_entries _ fun i j => ?_
    simp only [Matrix.of_apply, hf0]
    exact (trd_nrd_int_of_mem O (O.toSubalgebra.mul_mem (e0 i).2 (star_mem_order O (e0 j).2))).1
  · rw [hdisc]
    let τ : Fin 4 ≃ Module.Free.ChooseBasisIndex ℤ L := (Fintype.equivFinOfCardEq hcard).symm
    let s := (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).reindex τ
    rw [det_gram_change s f0]
    have hs : (Matrix.of fun i j => trd (s i * star (s j))).det = 16 * (a : ℚ) ^ 2 * (b : ℚ) ^ 2 := by
      rw [← det_gram_basisOneIJK a b, ← Matrix.det_reindex_self τ.symm]
      congr 1
      ext i j
      simp [s, Matrix.reindex_apply, Module.Basis.reindex_apply]
    rw [hs]
    have hdet : (s.toMatrix f0).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip s f0)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne
    positivity

/-- Proof helper: a ℤ-submodule with ℤ-basis `e` (a ℚ-basis `f`) is the additive closure of `f`. -/
theorem toAddSubgroup_eq_closure {V : Type*} [AddCommGroup V] [Module ℚ V] {L : Submodule ℤ V} {ι : Type}
    (e : Module.Basis ι ℤ L) (f : Module.Basis ι ℚ V) (hf : ∀ i, f i = (e i : V)) :
    L.toAddSubgroup = AddSubgroup.closure (Set.range f) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  congr 1
  have h := Submodule.map_span L.subtype (Set.range e)
  rw [e.span_eq, Submodule.map_subtype_top, ← Set.range_comp] at h
  rw [h]
  congr 1
  ext x
  simp [hf]

/-- For orders `O ⊆ O'`: the index `[O' : O]` is finite and `d(O) = [O' : O]² d(O')`. -/
@[tf_id "III.qord.lem:discriminant-index"]
theorem discriminant_eq_index_sq_mul {a b : ℤ} (O O' : QOrder a b) (h : O.toSubalgebra ≤ O'.toSubalgebra) :
    (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
        (Subalgebra.toSubmodule O'.toSubalgebra).toAddSubgroup ≠ 0 ∧
    discriminant O =
      ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
        (Subalgebra.toSubmodule O'.toSubalgebra).toAddSubgroup : ℚ) ^ 2 * discriminant O' := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  obtain ⟨e', f', hf'⟩ := exists_lattice_basis _ O'.fg O'.span_eq_top
  have hrel := AddSubgroup.relIndex_eq_abs_det _ _ (fun x hx => h hx) f f'
    (toAddSubgroup_eq_closure e f hf) (toAddSubgroup_eq_closure e' f' hf')
  have hdet : f'.det f ≠ 0 :=
    ((Module.Basis.is_basis_iff_det f').mp ⟨f.linearIndependent, f.span_eq⟩).ne_zero
  have hd : discriminant O = (Matrix.of fun i j => trd (f i * star (f j))).det := by
    rw [(discriminant_basic O).1 e]; simp [hf]
  have hd' : discriminant O' = (Matrix.of fun i j => trd (f' i * star (f' j))).det := by
    rw [(discriminant_basic O').1 e']; simp [hf']
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 : (((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
        (Subalgebra.toSubmodule O'.toSubalgebra).toAddSubgroup : ℕ) : ℚ) = 0 := by rw [h0]; simp
    rw [hrel] at h1
    exact hdet (abs_eq_zero.mp h1)
  · rw [hrel, sq_abs, hd, hd', det_gram_change f' f, Module.Basis.det_apply]

/-- Proof helper: for `a, b ≠ 0` the discriminant of an order is nonzero. -/
theorem discriminant_ne_zero {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) : discriminant O ≠ 0 := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  have hd : discriminant O = (Matrix.of fun i j => trd (f i * star (f j))).det := by
    rw [(discriminant_basic O).1 e]; simp [hf]
  rw [hd, det_gram_change (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)) f,
    det_gram_basisOneIJK]
  have hdet : ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).toMatrix f).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip
      (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)) f)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  positivity

/-! ## §2 Maximal orders -/

/-- `O` is maximal: every order containing `O` equals `O`. -/
@[tf_id "III.qord.def:maximal-order"]
def IsMaximalOrder {a b : ℤ} (O : QOrder a b) : Prop :=
  ∀ O' : QOrder a b, O.toSubalgebra ≤ O'.toSubalgebra → O'.toSubalgebra = O.toSubalgebra

/-- The maximal orders of `B`, as a subtype of `QOrder a b`. -/
@[tf_aux "III.qord.def:maximal-order-subtype"]
abbrev MaxOrder (a b : ℤ) : Type := {O : QOrder a b // IsMaximalOrder O}

/-- For `a ≠ 0` and `b ≠ 0`, every order is contained in a maximal order. -/
@[tf_id "III.qord.thm:exists-maximal-order"]
theorem exists_maxOrder_ge {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) :
    ∃ O' : MaxOrder a b, O.toSubalgebra ≤ O'.1.toSubalgebra := by
  classical
  have hP : ∃ n : ℕ, ∃ O' : QOrder a b, O.toSubalgebra ≤ O'.toSubalgebra ∧
      ∃ m : ℤ, discriminant O' = m ∧ m.natAbs = n := by
    obtain ⟨m, hm⟩ := (discriminant_basic O).2.1
    exact ⟨_, O, le_rfl, m, hm, rfl⟩
  obtain ⟨O', hle, m, hm, hmn⟩ := Nat.find_spec hP
  refine ⟨⟨O', fun O'' h'' => ?_⟩, hle⟩
  obtain ⟨m'', hm''⟩ := (discriminant_basic O'').2.1
  have hmin : Nat.find hP ≤ m''.natAbs := Nat.find_min' hP ⟨O'', hle.trans h'', m'', hm'', rfl⟩
  obtain ⟨hne, hd⟩ := discriminant_eq_index_sq_mul O' O'' h''
  set k := (Subalgebra.toSubmodule O'.toSubalgebra).toAddSubgroup.relIndex
    (Subalgebra.toSubmodule O''.toSubalgebra).toAddSubgroup with hk
  have hmk : m = (k : ℤ) ^ 2 * m'' := by
    rw [hm, hm''] at hd; exact_mod_cast hd
  have hm''0 : m'' ≠ 0 := by
    intro h0; exact discriminant_ne_zero ha hb O'' (by rw [hm'', h0, Int.cast_zero])
  have habs : m.natAbs = k ^ 2 * m''.natAbs := by
    rw [hmk, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have hk1 : k = 1 := by
    have h1 : k ^ 2 * m''.natAbs ≤ 1 * m''.natAbs := by rw [← habs, hmn, one_mul]; exact hmin
    have h2 : k ^ 2 ≤ 1 := Nat.le_of_mul_le_mul_right h1 (Int.natAbs_pos.mpr hm''0)
    have h3 : k ≤ 1 := by nlinarith
    omega
  have hle' := (AddSubgroup.relIndex_eq_one).mp hk1
  exact le_antisymm (fun x hx => hle' hx) h''

/-- Maximality criterion: if for every prime `p` with `p² ∣ d(O)` no `x ∈ p⁻¹O ∖ O` has `trd(x), nrd(x) ∈ ℤ`, then `O`
is maximal. (`x ∈ p⁻¹O` is written `p x ∈ O`; `p² ∣ d(O)` is written `d(O) = p² n` with `n ∈ ℤ`.) -/
@[tf_id "III.qord.lem:maximal-criterion"]
theorem isMaximalOrder_of_criterion {a b : ℤ} (O : QOrder a b)
    (h : ∀ p : ℕ, p.Prime → (∃ n : ℤ, discriminant O = (p : ℚ) ^ 2 * n) →
      ∀ x : QuatAlg ℚ a b, (p : ℚ) • x ∈ O.toSubalgebra → x ∉ O.toSubalgebra →
        ¬ ((∃ n : ℤ, trd x = n) ∧ (∃ n : ℤ, nrd x = n))) :
    IsMaximalOrder O := by
  intro O' hle
  by_contra hne
  obtain ⟨hk0, hd⟩ := discriminant_eq_index_sq_mul O O' hle
  set H := (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup with hH
  set K := (Subalgebra.toSubmodule O'.toSubalgebra).toAddSubgroup with hK
  have hk1 : H.relIndex K ≠ 1 := by
    intro h1
    exact hne (le_antisymm (fun x hx => (AddSubgroup.relIndex_eq_one.mp h1) hx) hle)
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  have : Fact p.Prime := ⟨hp⟩
  have : (H.addSubgroupOf K).FiniteIndex := ⟨hk0⟩
  have : Finite (K ⧸ H.addSubgroupOf K) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := K ⧸ H.addSubgroupOf K) p hpk
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hpy : (p : ℤ) • (y : QuatAlg ℚ a b) ∈ O.toSubalgebra := by
    have h0 : p • (y : K ⧸ H.addSubgroupOf K) = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
    have e : ((p • y : K) : QuatAlg ℚ a b) = (p : ℤ) • (y : QuatAlg ℚ a b) := by simp
    rw [← e]; exact h0
  have hy : (y : QuatAlg ℚ a b) ∉ O.toSubalgebra := by
    intro hy
    have h0 : (y : K ⧸ H.addSubgroupOf K) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hy)
    rw [h0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  obtain ⟨k', hk'⟩ := hpk
  obtain ⟨n, hn⟩ := (discriminant_basic O').2.1
  refine h p hp ⟨(k' : ℤ) ^ 2 * n, ?_⟩ y (by rw [← Int.cast_smul_eq_zsmul ℚ] at hpy; simpa using hpy) hy
    (trd_nrd_int_of_mem O' y.2)
  rw [hd, hn, hk']
  push_cast; ring

/-! ## §3 Level structures and Eichler orders -/

/-- A level structure of level `M ≥ 1` on an order `O`: a surjective ring hom `φ : O → M₂(ℤ/M)` (bundled; the Prop
field `surjective` is a registry field, plan §1.3). -/
@[tf_id "III.qord.def:level-structure"]
structure LevelStructure {a b : ℤ} (O : QOrder a b) (M : ℕ) [NeZero M] where
  /-- The ring hom `φ : O → M₂(ℤ/M)`. -/
  toRingHom : O.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod M)
  /-- `φ` is surjective. -/
  surjective : Function.Surjective toRingHom

/-- The ℤ-subalgebra `{x ∈ O : φ(x)₂₁ = 0}` of `B`. -/
@[tf_aux "III.qord.def:eichler-order-subalgebra"]
def eichlerSubalgebra {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    Subalgebra ℤ (QuatAlg ℚ a b) where
  carrier := {x | ∃ hx : x ∈ O.toSubalgebra, φ.toRingHom ⟨x, hx⟩ 1 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨O.toSubalgebra.mul_mem hx hy, ?_⟩
    have : (⟨x * y, O.toSubalgebra.mul_mem hx hy⟩ : O.toSubalgebra) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, Matrix.mul_apply, Fin.sum_univ_two, hx0, hy0]
    simp
  add_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨O.toSubalgebra.add_mem hx hy, ?_⟩
    have : (⟨x + y, O.toSubalgebra.add_mem hx hy⟩ : O.toSubalgebra) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, Matrix.add_apply, hx0, hy0, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨O.toSubalgebra.algebraMap_mem r, ?_⟩
    have : (⟨algebraMap ℤ _ r, O.toSubalgebra.algebraMap_mem r⟩ : O.toSubalgebra) = r • (1 : O.toSubalgebra) :=
      Subtype.ext (by simp)
    rw [this, map_zsmul, map_one, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]

/-- Proof helper: `O(M; φ) ⊆ O`. -/
theorem eichlerSubalgebra_le {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    eichlerSubalgebra φ ≤ O.toSubalgebra :=
  fun _ hx => hx.1

/-- Proof helper: `M O ⊆ O(M; φ)`. -/
theorem zsmul_mem_eichlerSubalgebra {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M)
    {x : (QuatAlg ℚ a b)} (hx : x ∈ O.toSubalgebra) : ((M : ℤ) • x) ∈ eichlerSubalgebra φ := by
  refine ⟨O.toSubalgebra.toSubmodule.smul_mem (M : ℤ) hx, ?_⟩
  have : (⟨(M : ℤ) • x, O.toSubalgebra.toSubmodule.smul_mem (M : ℤ) hx⟩ : O.toSubalgebra) =
      (M : ℤ) • (⟨x, hx⟩ : O.toSubalgebra) := rfl
  rw [this, map_zsmul, Matrix.smul_apply, zsmul_eq_mul]
  simp

/-- The Eichler order `O(M; φ) := {x ∈ O : φ(x)₂₁ = 0}` of level `M` attached to a level structure `φ`. -/
@[tf_id "III.qord.def:eichler-order"]
noncomputable def eichlerOrder {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    QOrder a b where
  toSubalgebra := eichlerSubalgebra φ
  fg := fg_of_le_fg O.fg (eichlerSubalgebra_le φ)
  span_eq_top := by
    refine eq_top_iff.mpr ?_
    rw [← O.span_eq_top]
    refine Submodule.span_le.mpr fun y hy => ?_
    have hM : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
    have hy' : y = (M : ℚ)⁻¹ • ((M : ℤ) • y) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hM, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (zsmul_mem_eichlerSubalgebra φ hy))

/-- `[O : O(M; φ)] = M` and `d(O(M; φ)) = M² d(O)`. -/
@[tf_id "III.qord.lem:eichler-order-index"]
theorem eichlerOrder_index {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra).toAddSubgroup.relIndex
        (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup = M ∧
      discriminant (eichlerOrder φ) = (M : ℚ) ^ 2 * discriminant O := by
  set H := (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra).toAddSubgroup with hH
  set K := (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup with hK
  let ψ : K →+ ZMod M :=
    { toFun := fun x => φ.toRingHom ⟨x.1, x.2⟩ 1 0
      map_zero' := by
        have : (⟨(0 : K).1, (0 : K).2⟩ : O.toSubalgebra) = 0 := rfl
        rw [this, RingHom.map_zero]; rfl
      map_add' := fun x y => by
        have : (⟨(x + y : K).1, (x + y : K).2⟩ : O.toSubalgebra) = ⟨x.1, x.2⟩ + ⟨y.1, y.2⟩ := rfl
        rw [this, RingHom.map_add]; rfl }
  have hker : H.addSubgroupOf K = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    exact ⟨fun ⟨_, h0⟩ => h0, fun h0 => ⟨x.2, h0⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro c
    obtain ⟨y, hy⟩ := φ.surjective (Matrix.of fun i j => if i = 1 ∧ j = 0 then c else 0)
    refine ⟨⟨y.1, y.2⟩, ?_⟩
    change φ.toRingHom ⟨y.1, y.2⟩ 1 0 = c
    rw [hy]; simp
  have hidx : H.relIndex K = M := by
    rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    rw [AddSubgroup.card_top, Nat.card_zmod]
  refine ⟨hidx, ?_⟩
  have h := (discriminant_eq_index_sq_mul (eichlerOrder φ) O (eichlerSubalgebra_le φ)).2
  rw [h, ← hH, ← hK, hidx]

/-! ## §4 Unit groups -/

/-- The unit group `O^× = {u ∈ Bˣ : u, u⁻¹ ∈ O}` of an order, as a subgroup of `Bˣ`. -/
@[tf_id "III.qord.def:unit-group"]
def unitGroup {a b : ℤ} (O : QOrder a b) : Subgroup (QuatAlg ℚ a b)ˣ where
  carrier := {u | (u : (QuatAlg ℚ a b)) ∈ O.toSubalgebra ∧ ((u⁻¹ : (QuatAlg ℚ a b)ˣ) :
    (QuatAlg ℚ a b)) ∈ O.toSubalgebra}
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨by simpa using O.toSubalgebra.mul_mem hu hv, by simpa using O.toSubalgebra.mul_mem hv' hu'⟩
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨hu', by simpa using hu⟩

/-- Proof helper: `x x̄ = nrd(x)` and `x̄ x = nrd(x)` in `B`. -/
theorem mul_star_eq_nrd {a b : ℤ} (x : QuatAlg ℚ a b) :
    x * star x = algebraMap ℚ (QuatAlg ℚ a b) (nrd x) ∧ star x * x = algebraMap ℚ (QuatAlg ℚ a b) (nrd x) := by
  constructor <;> ext <;> simp [nrd, Algebra.algebraMap_eq_smul_one] <;> ring

/-- Proof helper: `nrd` is multiplicative on `B`. -/
theorem nrd_mul' {a b : ℤ} (x y : QuatAlg ℚ a b) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [nrd, QuaternionAlgebra.mk_mul_mk]
  ring

/-- Proof helper: for `a, b < 0` every coordinate of `x` in `1, i, j, k` has square at most `nrd(x)`. -/
theorem coord_sq_le_nrd {a b : ℤ} (ha : a < 0) (hb : b < 0) (x : QuatAlg ℚ a b) (k : Fin 4) :
    (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).repr x k ^ 2 ≤ nrd x := by
  have ha' : (a : ℚ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr ha
  have hb' : (b : ℚ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hb
  have hab : (1 : ℚ) ≤ (a : ℚ) * b := by nlinarith
  have h0 := sq_nonneg x.re
  have h1 := sq_nonneg x.imI
  have h2 := sq_nonneg x.imJ
  have h3 := sq_nonneg x.imK
  simp only [QuaternionAlgebra.coe_basisOneIJK_repr, nrd]
  fin_cases k <;> simp <;> nlinarith

/-- Proof helper: a finite family of rationals has a common denominator. -/
theorem exists_common_den {ι : Type} [Fintype ι] (q : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ j, ∃ n : ℤ, (D : ℚ) * q j = n := by
  classical
  refine ⟨∏ j, (q j).den, Finset.prod_pos fun j _ => (q j).den_pos, fun j => ?_⟩
  obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ j)
  refine ⟨t * (q j).num, ?_⟩
  rw [ht, Nat.cast_mul, mul_comm ((q j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  push_cast; ring

/-- Proof helper: for `a, b < 0`, an order has only finitely many elements of reduced norm `1`. -/
theorem finite_nrd_eq_one {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) :
    {x | x ∈ O.toSubalgebra ∧ nrd x = 1}.Finite := by
  classical
  obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  set s := QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) with hs
  obtain ⟨D, hD, hDq⟩ := exists_common_den (fun ik : Fin 4 × Fin 4 => s.repr (f ik.1) ik.2)
  have hDq' : ∀ i k, ∃ n : ℤ, (D : ℚ) * s.repr (f i) k = n := fun i k => hDq (i, k)
  let T : Set (Fin 4 → ℤ) := Set.pi Set.univ fun _ => Set.Icc (-(D : ℤ)) D
  have hT : T.Finite := Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hT.image fun v => s.equivFun.symm fun k => (v k : ℚ) / D).subset ?_
  rintro x ⟨hxO, hx1⟩
  have hint : ∀ k, ∃ m : ℤ, (D : ℚ) * s.repr x k = m := by
    intro k
    have hx := (mem_lattice_iff_repr e f hf x).mp hxO
    choose n hn using hx
    choose N hN using hDq'
    refine ⟨∑ i, n i * N i k, ?_⟩
    conv_lhs => rw [← f.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finset.mul_sum, hn]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hN i k]; ring
  choose m hm using hint
  refine ⟨m, fun k _ => ?_, ?_⟩
  · have hsq := coord_sq_le_nrd ha hb x k
    rw [hx1] at hsq
    have habs : |s.repr x k| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hsq
    have hmabs : |(m k : ℚ)| ≤ D := by
      rw [← hm k, abs_mul, Nat.abs_cast]
      calc (D : ℚ) * |s.repr x k| ≤ D * 1 := by gcongr
        _ = D := mul_one _
    have : |m k| ≤ D := by exact_mod_cast hmabs
    exact abs_le.mp this
  · simp only
    rw [LinearEquiv.symm_apply_eq]
    ext k
    rw [Module.Basis.equivFun_apply, ← hm k]
    have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    field_simp

/-- For definite `B` (`a, b < 0`): `O^× = {x ∈ O : nrd(x) = 1}`, and `O^×` is finite. -/
@[tf_id "III.qord.thm:units-finite"]
theorem unitGroup_eq_nrd_one_finite {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) :
    ((↑) : (QuatAlg ℚ a b)ˣ → QuatAlg ℚ a b) '' (unitGroup O : Set (QuatAlg ℚ a b)ˣ) =
        {x | x ∈ O.toSubalgebra ∧ nrd x = 1} ∧
      Finite (unitGroup O) := by
  have hsub : ∀ u ∈ unitGroup O, (u : QuatAlg ℚ a b) ∈ O.toSubalgebra ∧ nrd (u : QuatAlg ℚ a b) = 1 := by
    rintro u ⟨hu, hu'⟩
    refine ⟨hu, ?_⟩
    obtain ⟨-, m, hm⟩ := trd_nrd_int_of_mem O hu
    obtain ⟨-, m', hm'⟩ := trd_nrd_int_of_mem O hu'
    have h1 : nrd (u : QuatAlg ℚ a b) * nrd ((u⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
      rw [← nrd_mul', Units.mul_inv]; simp [nrd]
    rw [hm, hm'] at h1
    have h2 : m * m' = 1 := by exact_mod_cast h1
    have h3 : 0 ≤ (m : ℚ) := by
      rw [← hm]; exact (sq_nonneg _).trans (coord_sq_le_nrd ha hb _ 0)
    have h4 : 0 ≤ m := by exact_mod_cast h3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h | h
    · rw [hm, h, Int.cast_one]
    · omega
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hsub u hu
    · rintro ⟨hx, hx1⟩
      obtain ⟨h1, h2⟩ := mul_star_eq_nrd x
      rw [hx1, map_one] at h1 h2
      refine ⟨⟨x, star x, h1, h2⟩, ⟨hx, ?_⟩, rfl⟩
      exact star_mem_order O hx
  · have hfin := (finite_nrd_eq_one ha hb O).to_subtype
    refine Finite.of_injective (fun u : unitGroup O =>
      (⟨((u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b), hsub u u.2⟩ : {x | x ∈ O.toSubalgebra ∧ nrd x = 1})) ?_
    intro u v huv
    exact Subtype.ext (Units.ext (congrArg Subtype.val huv))

/-- Proof helper: the elements of `O^×` lie in `O` and have reduced norm `1` (for `a, b < 0`). -/
theorem unitGroup_val_props {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (u : (QuatAlg ℚ a b)ˣ)
    (hu : u ∈ unitGroup O) : (u : QuatAlg ℚ a b) ∈ O.toSubalgebra ∧ nrd (u : QuatAlg ℚ a b) = 1 := by
  have h := (unitGroup_eq_nrd_one_finite ha hb O).1
  have : (u : QuatAlg ℚ a b) ∈ ((↑) : (QuatAlg ℚ a b)ˣ → QuatAlg ℚ a b) '' (unitGroup O : Set (QuatAlg ℚ a b)ˣ) :=
    ⟨u, hu, rfl⟩
  rw [h] at this
  exact this

/-- Proof helper: for `a, b < 0`, `nrd(x) = 0` only for `x = 0`. -/
theorem eq_zero_of_nrd_eq_zero {a b : ℤ} (ha : a < 0) (hb : b < 0) {x : QuatAlg ℚ a b} (h : nrd x = 0) : x = 0 := by
  have hk := fun k => coord_sq_le_nrd ha hb x k
  simp only [h, QuaternionAlgebra.coe_basisOneIJK_repr] at hk
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3
  simp at h0 h1 h2 h3
  ext <;> simp <;> nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]

/-- Proof helper: for `a, b < 0`, `B` has no zero divisors. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (ha : a < 0) (hb : b < 0) {x y : QuatAlg ℚ a b}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have h' := congrArg nrd h
  rw [nrd_mul', show nrd (0 : QuatAlg ℚ a b) = 0 by simp [nrd]] at h'
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact Or.inl (eq_zero_of_nrd_eq_zero ha hb h0)
  · exact Or.inr (eq_zero_of_nrd_eq_zero ha hb h0)

/-- Proof helper: `1 ≠ −1` and `1 ≠ −2` in `B`. -/
theorem one_ne_neg_one_two {a b : ℤ} : (1 : QuatAlg ℚ a b) ≠ -1 ∧ (1 : QuatAlg ℚ a b) ≠ -2 := by
  constructor <;> intro h <;> have := congrArg QuaternionAlgebra.re h <;>
    norm_num [QuaternionAlgebra.re_ofNat] at this

/-- Proof helper: the five cases for a unit `x` of an order in a definite algebra (by `t = trd(x) ∈ {−2, …, 2}`). -/
theorem unit_cases {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) {x : QuatAlg ℚ a b}
    (hx : x ∈ O.toSubalgebra) (h1 : nrd x = 1) :
    x = 1 ∨ x = -1 ∨ x ^ 2 = -1 ∨ x ^ 2 = x - 1 ∨ x ^ 2 = -x - 1 := by
  obtain ⟨⟨t, ht⟩, -⟩ := trd_nrd_int_of_mem O hx
  have hq := quad_rel x
  rw [h1, map_one, ht] at hq
  have hsq : x ^ 2 = (t : ℚ) • x - 1 := by rw [← sub_eq_zero, ← hq]; abel
  have hre : x.re ^ 2 ≤ 1 := by
    have := coord_sq_le_nrd ha hb x 0; rw [h1] at this; simpa using this
  have htq : (t : ℚ) = 2 * x.re := by rw [← ht]; rfl
  have ht2 : (t : ℚ) ^ 2 ≤ 4 := by rw [htq]; nlinarith
  have ht2' : t ^ 2 ≤ 4 := by exact_mod_cast ht2
  have hlo : -2 ≤ t := by nlinarith
  have hhi : t ≤ 2 := by nlinarith
  interval_cases t
  · right; left
    have h0 : nrd (x + 1) = 0 := by
      have : nrd (x + 1) = nrd x + trd x + 1 := by simp [nrd, trd]; ring
      rw [this, h1, ht]; norm_num
    have := eq_zero_of_nrd_eq_zero ha hb h0
    exact eq_neg_of_add_eq_zero_left this
  · right; right; right; right
    rw [hsq]; simp
  · right; right; left
    rw [hsq]; simp
  · right; right; right; left
    rw [hsq]; simp
  · left
    have h0 : nrd (x - 1) = 0 := by
      have : nrd (x - 1) = nrd x - trd x + 1 := by simp [nrd, trd]; ring
      rw [this, h1, ht]; norm_num
    exact sub_eq_zero.mp (eq_zero_of_nrd_eq_zero ha hb h0)

/-- Proof helper: powers of a unit in the three non-trivial cases. -/
theorem unit_pow_twelve {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) {x : QuatAlg ℚ a b}
    (hx : x ∈ O.toSubalgebra) (h1 : nrd x = 1) : x ^ 12 = 1 := by
  rcases unit_cases ha hb O hx h1 with h | h | h | h | h
  · rw [h, one_pow]
  · rw [h]; norm_num
  · rw [show 12 = 2 * 6 by rfl, pow_mul, h]; norm_num
  · have h3 : x ^ 3 = -1 := by
      rw [pow_succ', h, mul_sub, ← sq, h, mul_one]; abel
    rw [show 12 = 3 * 4 by rfl, pow_mul, h3]; norm_num
  · have h3 : x ^ 3 = 1 := by
      rw [pow_succ', h, mul_sub, mul_neg, ← sq, h, mul_one]; abel
    rw [show 12 = 3 * 4 by rfl, pow_mul, h3, one_pow]

/-- Proof helper: a unit with `x⁴ = 1` is `±1` or satisfies `x² = −1`. -/
theorem unit_pow_four {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) {x : QuatAlg ℚ a b}
    (hx : x ∈ O.toSubalgebra) (h1 : nrd x = 1) (h4 : x ^ 4 = 1) : x = 1 ∨ x = -1 ∨ x ^ 2 = -1 := by
  rcases unit_cases ha hb O hx h1 with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have h3 : x ^ 3 = -1 := by rw [pow_succ', h, mul_sub, ← sq, h, mul_one]; abel
    have h4' : x ^ 4 = -x := by rw [pow_succ', h3]; simp
    rw [h4] at h4'
    have hx1 : x = -1 := by rw [← neg_neg x, ← h4']
    rw [hx1] at h; norm_num at h
    exact one_ne_neg_one_two.2 h
  · exfalso
    have h3 : x ^ 3 = 1 := by rw [pow_succ', h, mul_sub, mul_neg, ← sq, h, mul_one]; abel
    have h4' : x ^ 4 = x := by rw [pow_succ', h3, mul_one]
    rw [h4] at h4'
    rw [← h4'] at h; norm_num at h
    exact one_ne_neg_one_two.2 h

/-- Proof helper: a unit with `x³ = 1` is `1` or satisfies `x² + x + 1 = 0`. -/
theorem unit_pow_three {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) {x : QuatAlg ℚ a b}
    (hx : x ∈ O.toSubalgebra) (h1 : nrd x = 1) (h3 : x ^ 3 = 1) : x = 1 ∨ x ^ 2 + x + 1 = 0 := by
  rcases unit_cases ha hb O hx h1 with h | h | h | h | h
  · exact Or.inl h
  · exfalso; rw [h] at h3; norm_num at h3; exact one_ne_neg_one_two.1 h3.symm
  · exfalso
    have : x ^ 3 = -x := by rw [pow_succ', h]; simp
    rw [h3] at this
    have hx1 : x = -1 := by rw [← neg_neg x, ← this]
    rw [hx1] at h; norm_num at h; exact one_ne_neg_one_two.1 h
  · exfalso
    have : x ^ 3 = -1 := by rw [pow_succ', h, mul_sub, ← sq, h, mul_one]; abel
    rw [h3] at this; exact one_ne_neg_one_two.1 this
  · right; rw [h]; abel

/-- Proof helper: `x² = −1` for a unit `x` gives `x̄ = −x`. -/
theorem star_eq_neg_of_sq {a b : ℤ} {x : QuatAlg ℚ a b} (h1 : nrd x = 1) (h : x ^ 2 = -1) : star x = -x := by
  have hq := quad_rel x
  rw [h1, map_one, h] at hq
  have ht : trd x • x = 0 := by rw [← neg_eq_zero, ← hq]; abel
  have hx0 : x ≠ 0 := by intro h0; rw [h0] at h1; simp [nrd] at h1
  have ht0 : trd x = 0 := (smul_eq_zero.mp ht).resolve_right hx0
  have := add_star_eq_trd x
  rw [ht0, map_zero] at this
  exact eq_neg_of_add_eq_zero_right this

/-- Proof helper: a subgroup of `O^×` (definite `B`) of exponent dividing 4 has at most 8 elements. -/
theorem card_le_eight_of_pow_four {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (H : Subgroup (QuatAlg ℚ a b)ˣ) (hH : H ≤ unitGroup O) (h4 : ∀ u ∈ H, u ^ 4 = 1) : Nat.card H ≤ 8 := by
  classical
  have hv : ∀ u ∈ H, (u : QuatAlg ℚ a b) ∈ O.toSubalgebra ∧ nrd (u : QuatAlg ℚ a b) = 1 :=
    fun u hu => unitGroup_val_props ha hb O u (hH hu)
  have hc : ∀ u ∈ H, (u : QuatAlg ℚ a b) = 1 ∨ (u : QuatAlg ℚ a b) = -1 ∨ (u : QuatAlg ℚ a b) ^ 2 = -1 :=
    fun u hu => unit_pow_four ha hb O (hv u hu).1 (hv u hu).2 (by rw [← Units.val_pow_eq_pow_val, h4 u hu]; rfl)
  have hne : ∀ u : (QuatAlg ℚ a b)ˣ, (u : QuatAlg ℚ a b) ≠ 0 := fun u => u.ne_zero
  -- the bound via an injection into a finite set of values
  have key : ∀ T : List (QuatAlg ℚ a b), T.length ≤ 8 → (∀ u ∈ H, (u : QuatAlg ℚ a b) ∈ T) → Nat.card H ≤ 8 := by
    intro T hT hmem
    have hinj : Function.Injective (fun u : H => (⟨((u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b), List.mem_toFinset.mpr (hmem u u.2)⟩ :
        {y // y ∈ T.toFinset})) := by
      intro u v huv
      exact Subtype.ext (Units.ext (by simpa using congrArg Subtype.val huv))
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := {y // y ∈ T.toFinset}), Fintype.card_coe] at this
    exact this.trans ((List.toFinset_card_le T).trans hT)
  by_cases hall : ∀ u ∈ H, (u : QuatAlg ℚ a b) = 1 ∨ (u : QuatAlg ℚ a b) = -1
  · refine key [1, -1] (by simp) fun u hu => ?_
    rcases hall u hu with h | h <;> simp [h]
  push Not at hall
  obtain ⟨x, hxH, hx1, hxm1⟩ := hall
  set X := (x : QuatAlg ℚ a b) with hX
  have hX2 : X ^ 2 = -1 := by
    rcases hc x hxH with h | h | h
    · exact absurd h hx1
    · exact absurd h hxm1
    · exact h
  have hXs : star X = -X := star_eq_neg_of_sq (hv x hxH).2 hX2
  -- commuting elements of square `-1` are `±X`
  have hcomm : ∀ u ∈ H, (u : QuatAlg ℚ a b) * X = X * u →
      (u : QuatAlg ℚ a b) = 1 ∨ (u : QuatAlg ℚ a b) = -1 ∨ (u : QuatAlg ℚ a b) = X ∨ (u : QuatAlg ℚ a b) = -X := by
    intro u hu huX
    rcases hc u hu with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      have h0 : ((u : QuatAlg ℚ a b) - X) * ((u : QuatAlg ℚ a b) + X) = 0 := by
        have e : ((u : QuatAlg ℚ a b) - X) * ((u : QuatAlg ℚ a b) + X) =
            (u : QuatAlg ℚ a b) ^ 2 - X ^ 2 + ((u : QuatAlg ℚ a b) * X - X * u) := by noncomm_ring
        rw [e, h, hX2, huX]; abel
      rcases eq_zero_or_eq_zero_of_mul_eq_zero ha hb h0 with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  -- every element is `±1`, `±X` or anticommutes with `X`
  have hdich : ∀ u ∈ H, ((u : QuatAlg ℚ a b) = 1 ∨ (u : QuatAlg ℚ a b) = -1 ∨ (u : QuatAlg ℚ a b) = X ∨
      (u : QuatAlg ℚ a b) = -X) ∨ (u : QuatAlg ℚ a b) * X = -(X * u) := by
    intro u hu
    rcases hc u hu with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · have hw := hc (x * u) (H.mul_mem hxH hu)
      simp only [Units.val_mul] at hw
      rcases hw with hw | hw | hw
      · left; right; right; right
        have h0 : X * ((u : QuatAlg ℚ a b) + X) = 0 := by rw [mul_add, hw, ← sq, hX2]; abel
        exact eq_neg_of_add_eq_zero_left ((eq_zero_or_eq_zero_of_mul_eq_zero ha hb h0).resolve_left (hne x))
      · left; right; right; left
        have h0 : X * ((u : QuatAlg ℚ a b) - X) = 0 := by rw [mul_sub, hw, ← sq, hX2]; abel
        exact sub_eq_zero.mp ((eq_zero_or_eq_zero_of_mul_eq_zero ha hb h0).resolve_left (hne x))
      · right
        have hs := star_eq_neg_of_sq (hv (x * u) (H.mul_mem hxH hu)).2 (by simpa using hw)
        have hXs' : star (x : QuatAlg ℚ a b) = -(x : QuatAlg ℚ a b) := hXs
        simp only [Units.val_mul, star_mul, hXs', star_eq_neg_of_sq (hv u hu).2 h] at hs
        rw [neg_mul_neg] at hs
        exact hs
  by_cases hA : ∃ g ∈ H, (g : QuatAlg ℚ a b) * X = -(X * g)
  · obtain ⟨g, hgH, hgX⟩ := hA
    set G0 := (g : QuatAlg ℚ a b)
    refine key [1, -1, X, -X, G0, -G0, G0 * X, -(G0 * X)] (by simp) fun u hu => ?_
    rcases hdich u hu with h | h
    · rcases h with h | h | h | h <;> simp [h]
    · -- `g⁻¹ u` commutes with `X`
      have hw : ((g⁻¹ * u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) * X = X * ((g⁻¹ * u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
        have hgi : (((g⁻¹ : (QuatAlg ℚ a b)ˣ)) : QuatAlg ℚ a b) * X = -(X * ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) := by
          have e := congrArg (fun y => (((g⁻¹ : (QuatAlg ℚ a b)ˣ)) : QuatAlg ℚ a b) * y *
            ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) hgX
          simp only [G0, mul_assoc, Units.inv_mul_cancel_left, mul_neg, neg_mul, Units.mul_inv, mul_one] at e
          rw [e, neg_neg]
        simp only [Units.val_mul]
        rw [mul_assoc, h, mul_neg, ← mul_assoc, hgi, neg_mul, neg_neg, mul_assoc]
      rcases hdich _ (H.mul_mem (H.inv_mem hgH) hu) with h' | h'
      · have hu' : (u : QuatAlg ℚ a b) = G0 * ((g⁻¹ * u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
          simp [G0]
        rcases h' with h' | h' | h' | h' <;> rw [hu', h'] <;> simp
      · exfalso
        rw [hw] at h'
        have h2 : (2 : ℚ) • (X * ((g⁻¹ * u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) = 0 := by
          rw [two_smul]; nth_rewrite 1 [h']; abel
        have h3 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
        rcases eq_zero_or_eq_zero_of_mul_eq_zero ha hb h3 with h4 | h4
        · exact hne x h4
        · exact hne _ h4
  · push Not at hA
    refine key [1, -1, X, -X] (by simp) fun u hu => ?_
    rcases hdich u hu with h | h
    · rcases h with h | h | h | h <;> simp [h]
    · exact absurd h (hA u hu)

/-- Proof helper: a commutative subgroup of `O^×` (definite `B`) of exponent dividing 3 has at most 3 elements. -/
theorem card_le_three_of_pow_three {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (H : Subgroup (QuatAlg ℚ a b)ˣ) (hH : H ≤ unitGroup O) (h3 : ∀ u ∈ H, u ^ 3 = 1)
    (hcomm : ∀ u ∈ H, ∀ v ∈ H, u * v = v * u) : Nat.card H ≤ 3 := by
  classical
  have hv : ∀ u ∈ H, (u : QuatAlg ℚ a b) ∈ O.toSubalgebra ∧ nrd (u : QuatAlg ℚ a b) = 1 :=
    fun u hu => unitGroup_val_props ha hb O u (hH hu)
  have hc : ∀ u ∈ H, (u : QuatAlg ℚ a b) = 1 ∨ (u : QuatAlg ℚ a b) ^ 2 + u + 1 = 0 :=
    fun u hu => unit_pow_three ha hb O (hv u hu).1 (hv u hu).2 (by rw [← Units.val_pow_eq_pow_val, h3 u hu]; rfl)
  have key : ∀ T : List (QuatAlg ℚ a b), T.length ≤ 3 → (∀ u ∈ H, (u : QuatAlg ℚ a b) ∈ T) → Nat.card H ≤ 3 := by
    intro T hT hmem
    have hinj : Function.Injective (fun u : H => (⟨((u : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b), List.mem_toFinset.mpr (hmem u u.2)⟩ :
        {y // y ∈ T.toFinset})) := by
      intro u v huv
      exact Subtype.ext (Units.ext (by simpa using congrArg Subtype.val huv))
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := {y // y ∈ T.toFinset}), Fintype.card_coe] at this
    exact this.trans ((List.toFinset_card_le T).trans hT)
  by_cases hall : ∀ u ∈ H, (u : QuatAlg ℚ a b) = 1
  · exact key [1] (by simp) fun u hu => by simp [hall u hu]
  push Not at hall
  obtain ⟨x, hxH, hx1⟩ := hall
  set X := (x : QuatAlg ℚ a b) with hX
  have hX2 : X ^ 2 + X + 1 = 0 := (hc x hxH).resolve_left hx1
  refine key [1, X, X ^ 2] (by simp) fun u hu => ?_
  rcases hc u hu with h | h
  · simp [h]
  · have huX : (u : QuatAlg ℚ a b) * X = X * u := by
      have := congrArg Units.val (hcomm u hu x hxH); simpa using this
    have h0 : ((u : QuatAlg ℚ a b) - X) * ((u : QuatAlg ℚ a b) + X + 1) = 0 := by
      have e : ((u : QuatAlg ℚ a b) - X) * ((u : QuatAlg ℚ a b) + X + 1) =
          ((u : QuatAlg ℚ a b) ^ 2 + u + 1) - (X ^ 2 + X + 1) + ((u : QuatAlg ℚ a b) * X - X * u) := by
        noncomm_ring
      rw [e, h, hX2, huX]; abel
    rcases eq_zero_or_eq_zero_of_mul_eq_zero ha hb h0 with h' | h'
    · simp [sub_eq_zero.mp h']
    · have : (u : QuatAlg ℚ a b) = X ^ 2 := by
        rw [← sub_eq_zero]
        have e : (u : QuatAlg ℚ a b) - X ^ 2 = ((u : QuatAlg ℚ a b) + X + 1) - (X ^ 2 + X + 1) := by abel
        rw [e, h', hX2, sub_zero]
      simp [this]

/-- For definite `B` (`a, b < 0`): `|O^×|` is even and divides 24, so `|O^×| ∈ {2, 4, 6, 8, 12, 24}`. -/
@[tf_id "III.qord.thm:units-order-divides-24"]
theorem card_unitGroup_dvd_24 {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) :
    Even (Nat.card (unitGroup O)) ∧ Nat.card (unitGroup O) ∣ 24 ∧
      Nat.card (unitGroup O) ∈ ({2, 4, 6, 8, 12, 24} : Finset ℕ) := by
  classical
  have hfin : Finite (unitGroup O) := (unitGroup_eq_nrd_one_finite ha hb O).2
  have h12 : ∀ g : unitGroup O, g ^ 12 = 1 := by
    intro g
    obtain ⟨hgO, hg1⟩ := unitGroup_val_props ha hb O g g.2
    apply Subtype.ext; apply Units.ext
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    exact unit_pow_twelve ha hb O hgO hg1
  -- `-1 ∈ O^×` has order 2
  have hm1mem : (-1 : (QuatAlg ℚ a b)ˣ) ∈ unitGroup O := by
    refine ⟨?_, ?_⟩ <;> simp only [Units.val_neg, Units.val_one, inv_neg, inv_one] <;>
      exact O.toSubalgebra.neg_mem O.toSubalgebra.one_mem
  have hm1 : orderOf (⟨-1, hm1mem⟩ : unitGroup O) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext; apply Units.ext; simp
    · intro h
      have := congrArg (fun g : unitGroup O => ((g : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      exact one_ne_neg_one_two.1 this.symm
  have hpos : 0 < Nat.card (unitGroup O) := Nat.card_pos
  have h2 : 2 ∣ Nat.card (unitGroup O) := hm1 ▸ orderOf_dvd_natCard _
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (unitGroup O) → p = 2 ∨ p = 3 := by
    intro p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hp12 : p ∣ 12 := hg ▸ orderOf_dvd_of_pow_eq_one (h12 g)
    have hple : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp12
    interval_cases p <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hp (by decide) | exact absurd hp12 (by decide)
  -- the image of a subgroup of `O^×` in `Bˣ`
  have hmap : ∀ K : Subgroup (unitGroup O), K.map (unitGroup O).subtype ≤ unitGroup O ∧
      Nat.card (K.map (unitGroup O).subtype) = Nat.card K := by
    intro K
    refine ⟨fun u ⟨k, _, hk⟩ => hk ▸ k.2, Subgroup.card_map_of_injective (unitGroup O).subtype_injective⟩
  have h16 : ¬ 2 ^ 4 ∣ Nat.card (unitGroup O) := by
    intro hd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
    obtain ⟨hle, hcard⟩ := hmap K
    have h4 : ∀ u ∈ K.map (unitGroup O).subtype, u ^ 4 = 1 := by
      rintro u ⟨k, hk, rfl⟩
      have hk16 : (⟨k, hk⟩ : K) ^ 16 = 1 := by
        rw [show 16 = 2 ^ 4 by rfl, ← hK]; exact pow_card_eq_one'
      have hk16' : k ^ 16 = 1 := by simpa using congrArg Subtype.val hk16
      have hk4 : k ^ 4 = 1 := by
        have e : k ^ 16 = k ^ 4 * k ^ 12 := by rw [← pow_add]
        rw [e, h12 k, mul_one] at hk16'; exact hk16'
      rw [← map_pow, hk4, map_one]
    have := card_le_eight_of_pow_four ha hb O _ hle h4
    rw [hcard, hK] at this; norm_num at this
  have h9 : ¬ 3 ^ 2 ∣ Nat.card (unitGroup O) := by
    intro hd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hd
    obtain ⟨hle, hcard⟩ := hmap K
    have hcK : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
    have h3 : ∀ u ∈ K.map (unitGroup O).subtype, u ^ 3 = 1 := by
      rintro u ⟨k, hk, rfl⟩
      have hk9 : (⟨k, hk⟩ : K) ^ 9 = 1 := by
        rw [show 9 = 3 ^ 2 by rfl, ← hK]; exact pow_card_eq_one'
      have hk9' : k ^ 9 = 1 := by simpa using congrArg Subtype.val hk9
      have hk3 : k ^ 3 = 1 := by
        have e : k ^ 12 = k ^ 3 * k ^ 9 := by rw [← pow_add]
        rw [h12 k, hk9', mul_one] at e; exact e.symm
      rw [← map_pow, hk3, map_one]
    have hcomm : ∀ u ∈ K.map (unitGroup O).subtype, ∀ v ∈ K.map (unitGroup O).subtype, u * v = v * u := by
      rintro u ⟨k, hk, rfl⟩ v ⟨l, hl, rfl⟩
      have := hcK.is_comm.comm ⟨k, hk⟩ ⟨l, hl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (by simpa using congrArg Subtype.val this)
    have := card_le_three_of_pow_three ha hb O _ hle h3 hcomm
    rw [hcard, hK] at this; norm_num at this
  have hdvd : Nat.card (unitGroup O) ∣ 24 := by
    rw [← Nat.factorization_le_iff_dvd hpos.ne' (by norm_num)]
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ Nat.card (unitGroup O)
      · rcases hprime p hp hpd with rfl | rfl
        · have e1 : (Nat.card (unitGroup O)).factorization 2 ≤ 3 := by
            by_contra hc
            push Not at hc
            exact h16 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos.ne').mpr hc)
          have e2 : 3 ≤ (24 : ℕ).factorization 2 :=
            (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp (by norm_num)
          omega
        · have e1 : (Nat.card (unitGroup O)).factorization 3 ≤ 1 := by
            by_contra hc
            push Not at hc
            exact h9 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos.ne').mpr hc)
          have e2 : 1 ≤ (24 : ℕ).factorization 3 :=
            (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mp (by norm_num)
          omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]; exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _
  refine ⟨even_iff_two_dvd.mpr h2, hdvd, ?_⟩
  have hle : Nat.card (unitGroup O) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card (unitGroup O) = n at h2 hdvd hle hpos
  interval_cases n <;> simp_all

end GL2TF.Quat
