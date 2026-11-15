import AlgJL.Meta.Tag
import AlgJL.Common.QuaternionNorm
import AlgJL.VolI.P0.Adeles
import AlgJL.VolIII.P2.Orders
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The finite-adelic quaternion algebra `B̂`, completions of lattices and orders (Q2 U5, items 37–41)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §3 (items 37–41 of `docs/sprints/Q2-plan.md` §1.2).

* `BHat a b`: `B̂ := B_{𝔸_f} = ℍ[𝔸_f, a, 0, b]`, a **type synonym** (`def`, plan §1.1 item 3 and trap 3) carrying the
  product topology transported along `QuaternionAlgebra.equivTuple` (`Fin 4 → 𝔸_f`). Its ring, `𝔸_f`-algebra and
  topology instances are B-only plumbing. `B̂^×` carries Mathlib's `Units` topology (trap 4).
* `finEmbed a b : B → B̂`, coordinatewise through `ℚ → 𝔸_f` (`baseChange`).
* `latticeCompletion L`: `L̂ := Ẑ-span of ι(L)`; `orderCompletionUnits O`: `Ô^× := {u ∈ B̂^× : u, u⁻¹ ∈ Ô}`.
* `finiteIdeleLattice O x`: `L_x := ι⁻¹(xÔ)` (item 41(b); used by the class set, items 43, 50).

A lattice is a ℤ-submodule `L ⊆ B` with `L.FG` and `ℚ L = B`, written inline in binders (plan §1.2 conventions).
Owner: L2T (Q2, TITAN).
-/

set_option autoImplicit false

open scoped Quaternion Pointwise

namespace GL2TF.Quat

open GL2TF

/-! ## §1 The finite-adelic algebra -/

/-- The finite-adelic quaternion algebra `B̂ := B_{𝔸_f} = ℍ[𝔸_f, a, 0, b]`, as a type synonym of
`QuatAlg FinAdele a b` (so that the transported product topology does not clash with other instances, trap 3). -/
@[tf_id "III.qcls.def:finite-adelic-algebra"]
def BHat (a b : ℤ) : Type := QuatAlg FinAdele a b

/-- The ring structure of `B̂` (that of `ℍ[𝔸_f, a, 0, b]`). -/
@[tf_aux "III.qcls.def:finite-adelic-algebra-ring"]
noncomputable instance instRingBHat (a b : ℤ) : Ring (BHat a b) :=
  inferInstanceAs (Ring (QuatAlg FinAdele a b))

/-- The `𝔸_f`-algebra structure of `B̂` (coordinatewise scalars). -/
@[tf_aux "III.qcls.def:finite-adelic-algebra-algebra"]
noncomputable instance instAlgebraBHat (a b : ℤ) : Algebra FinAdele (BHat a b) :=
  inferInstanceAs (Algebra FinAdele (QuatAlg FinAdele a b))

/-- The topology of `B̂`: the product topology of `𝔸_f⁴`, transported along the coordinates
`QuaternionAlgebra.equivTuple` (`x ↦ (x₀, x₁, x₂, x₃)`). -/
@[tf_aux "III.qcls.def:finite-adelic-algebra-topology"]
noncomputable instance instTopologicalSpaceBHat (a b : ℤ) : TopologicalSpace (BHat a b) :=
  TopologicalSpace.induced
    (fun x : BHat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x) inferInstance

/-- The embedding `ι : B → B̂`, coordinatewise through the diagonal `ℚ → 𝔸_f`. -/
@[tf_aux "III.qcls.def:finite-adelic-embedding"]
noncomputable def finEmbed (a b : ℤ) : QuatAlg ℚ a b →+* BHat a b :=
  baseChange a b (algebraMap ℚ FinAdele)

/-- Proof helper: the coordinates `B̂ → 𝔸_f⁴` are continuous. -/
theorem continuous_bhat_coord (a b : ℤ) (k : Fin 4) :
    Continuous fun x : BHat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x k :=
  (continuous_apply k).comp continuous_induced_dom

/-- Proof helper: a map into `B̂` is continuous iff its four coordinates are. -/
theorem continuous_to_bhat_iff {a b : ℤ} {X : Type*} [TopologicalSpace X] (g : X → BHat a b) :
    Continuous g ↔ ∀ k, Continuous fun x =>
      QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) (g x) k :=
  continuous_induced_rng.trans continuous_pi_iff

/-- Proof helper: the coordinates `x ↦ (x₀, x₁, x₂, x₃)` are an open embedding `B̂ → 𝔸_f⁴` (with range everything). -/
theorem isOpenEmbedding_bhat_coords (a b : ℤ) :
    Topology.IsOpenEmbedding fun x : BHat a b =>
      QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x := by
  refine ⟨⟨⟨rfl⟩, (QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).injective⟩, ?_⟩
  have : Set.range (fun x : BHat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x) =
      Set.univ :=
    Set.range_eq_univ.mpr (QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).surjective
  rw [this]; exact isOpen_univ

/-- Proof helper: the four coordinate functions of `B̂` are continuous. -/
theorem continuous_bhat_re_im (a b : ℤ) :
    Continuous (fun x : BHat a b => (x : QuatAlg FinAdele a b).re) ∧
    Continuous (fun x : BHat a b => (x : QuatAlg FinAdele a b).imI) ∧
    Continuous (fun x : BHat a b => (x : QuatAlg FinAdele a b).imJ) ∧
    Continuous (fun x : BHat a b => (x : QuatAlg FinAdele a b).imK) :=
  ⟨continuous_bhat_coord a b 0, continuous_bhat_coord a b 1, continuous_bhat_coord a b 2,
    continuous_bhat_coord a b 3⟩

/-- Proof helper: multiplication on `B̂` is continuous. -/
theorem continuousMul_bhat (a b : ℤ) : ContinuousMul (BHat a b) := by
  obtain ⟨c0, c1, c2, c3⟩ := continuous_bhat_re_im a b
  have h0 := c0.comp (continuous_fst (X := BHat a b) (Y := BHat a b))
  have h1 := c1.comp (continuous_fst (X := BHat a b) (Y := BHat a b))
  have h2 := c2.comp (continuous_fst (X := BHat a b) (Y := BHat a b))
  have h3 := c3.comp (continuous_fst (X := BHat a b) (Y := BHat a b))
  have h0' := c0.comp (continuous_snd (X := BHat a b) (Y := BHat a b))
  have h1' := c1.comp (continuous_snd (X := BHat a b) (Y := BHat a b))
  have h2' := c2.comp (continuous_snd (X := BHat a b) (Y := BHat a b))
  have h3' := c3.comp (continuous_snd (X := BHat a b) (Y := BHat a b))
  simp only [Function.comp_def] at h0 h1 h2 h3 h0' h1' h2' h3'
  refine ⟨(continuous_to_bhat_iff _).mpr fun k => ?_⟩
  fin_cases k
  · show Continuous fun p : BHat a b × BHat a b => p.1.re * p.2.re + (a : FinAdele) * p.1.imI * p.2.imI +
      (b : FinAdele) * p.1.imJ * p.2.imJ + 0 * (b : FinAdele) * p.1.imJ * p.2.imK - (a : FinAdele) * (b : FinAdele) * p.1.imK * p.2.imK
    fun_prop
  · show Continuous fun p : BHat a b × BHat a b => p.1.re * p.2.imI + p.1.imI * p.2.re +
      0 * p.1.imI * p.2.imI - (b : FinAdele) * p.1.imJ * p.2.imK + (b : FinAdele) * p.1.imK * p.2.imJ
    fun_prop
  · show Continuous fun p : BHat a b × BHat a b => p.1.re * p.2.imJ + (a : FinAdele) * p.1.imI * p.2.imK +
      p.1.imJ * p.2.re + 0 * p.1.imJ * p.2.imI - (a : FinAdele) * p.1.imK * p.2.imI
    fun_prop
  · show Continuous fun p : BHat a b × BHat a b => p.1.re * p.2.imK + p.1.imI * p.2.imJ +
      0 * p.1.imI * p.2.imK - p.1.imJ * p.2.imI + p.1.imK * p.2.re
    fun_prop

/-- Proof helper: addition, negation and `𝔸_f`-scalars on `B̂` are continuous. -/
theorem continuous_bhat_ops (a b : ℤ) :
    ContinuousAdd (BHat a b) ∧ ContinuousNeg (BHat a b) ∧ ContinuousSMul FinAdele (BHat a b) := by
  obtain ⟨c0, c1, c2, c3⟩ := continuous_bhat_re_im a b
  refine ⟨⟨(continuous_to_bhat_iff _).mpr fun k => ?_⟩, ⟨(continuous_to_bhat_iff _).mpr fun k => ?_⟩,
    ⟨(continuous_to_bhat_iff _).mpr fun k => ?_⟩⟩
  · have := fun (f : BHat a b → FinAdele) (hf : Continuous f) =>
      (hf.comp (continuous_fst (X := BHat a b) (Y := BHat a b))).add
        (hf.comp (continuous_snd (X := BHat a b) (Y := BHat a b)))
    fin_cases k
    · exact this _ c0
    · exact this _ c1
    · exact this _ c2
    · exact this _ c3
  · fin_cases k
    · exact c0.neg
    · exact c1.neg
    · exact c2.neg
    · exact c3.neg
  · have := fun (f : BHat a b → FinAdele) (hf : Continuous f) =>
      (continuous_fst (X := FinAdele) (Y := BHat a b)).mul
        (hf.comp (continuous_snd (X := FinAdele) (Y := BHat a b)))
    fin_cases k
    · exact this _ c0
    · exact this _ c1
    · exact this _ c2
    · exact this _ c3

/-- `B̂` is a locally compact Hausdorff topological ring, and `B̂^×` (with Mathlib's `Units` topology) is a
topological group. B-only. -/
@[tf_aux "III.qcls.lem:finite-adelic-algebra-topology"]
theorem bHat_topology (a b : ℤ) :
    IsTopologicalRing (BHat a b) ∧ LocallyCompactSpace (BHat a b) ∧ T2Space (BHat a b) ∧
      IsTopologicalGroup (BHat a b)ˣ := by
  have := continuousMul_bhat a b
  obtain ⟨h1, h2, -⟩ := continuous_bhat_ops a b
  refine ⟨{ }, ?_, ?_, inferInstance⟩
  · exact (isOpenEmbedding_bhat_coords a b).locallyCompactSpace
  · exact (isOpenEmbedding_bhat_coords a b).isEmbedding.t2Space

/-! ## §2 Completions of lattices and orders -/

/-- The completion `L̂ := Ẑ-span of ι(L) ⊆ B̂` of a ℤ-submodule `L ⊆ B` (for a lattice `L`; for an order `O`, `Ô` is
`latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)`). -/
@[tf_id "III.qcls.def:order-completion"]
noncomputable def latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) : Submodule Zhat (BHat a b) :=
  Submodule.span Zhat (finEmbed a b '' (L : Set (QuatAlg ℚ a b)))

/-- Proof helper: `Ô` is closed under multiplication. -/
theorem mul_mem_orderCompletion {a b : ℤ} (O : QOrder a b) {x y : BHat a b}
    (hx : x ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra))
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    x * y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [latticeCompletion, Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨z, hz, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨z * w, O.toSubalgebra.mul_mem hz hw, map_mul _ _ _⟩

/-- Proof helper: `1 ∈ Ô`. -/
theorem one_mem_orderCompletion {a b : ℤ} (O : QOrder a b) :
    (1 : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) :=
  Submodule.subset_span ⟨1, O.toSubalgebra.one_mem, map_one _⟩

/-- The unit group `Ô^× := {u ∈ B̂^× : u, u⁻¹ ∈ Ô}` of the completion of an order. -/
@[tf_aux "III.qcls.def:order-completion-units"]
noncomputable def orderCompletionUnits {a b : ℤ} (O : QOrder a b) : Subgroup (BHat a b)ˣ where
  carrier := {u | (u : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ∧
    ((u⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)}
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact mul_mem_orderCompletion O hu hv
    · rw [mul_inv_rev, Units.val_mul]
      exact mul_mem_orderCompletion O hv' hu'
  one_mem' := ⟨by rw [Units.val_one]; exact one_mem_orderCompletion O,
    by rw [inv_one, Units.val_one]; exact one_mem_orderCompletion O⟩
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨hu', by rwa [inv_inv]⟩

section LocalGlobalHelpers

open Module

section BaseChange

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- Proof helper: base change along `ℚ → S` is `ℚ`-semilinear. -/
theorem baseChange_algebraMap_smul (a b : ℤ) (q : ℚ) (x : QuatAlg ℚ a b) :
    baseChange a b (algebraMap ℚ S) (q • x) = algebraMap ℚ S q • baseChange a b (algebraMap ℚ S) x := by
  ext <;> simp [baseChange] <;> rw [Algebra.smul_def]

/-- Proof helper: a ℚ-basis `f` of `B` base-changes to an `S`-basis of `B_S`, with coordinates of `ι(z)` the images
of the coordinates of `z`. -/
theorem exists_baseChange_basis (a b : ℤ) (f : Basis (Fin 4) ℚ (QuatAlg ℚ a b)) :
    ∃ F : Basis (Fin 4) S (QuatAlg S a b), (∀ i, F i = baseChange a b (algebraMap ℚ S) (f i)) ∧
      ∀ z i, F.repr (baseChange a b (algebraMap ℚ S) z) i = algebraMap ℚ S (f.repr z i) := by
  set v : Fin 4 → QuatAlg S a b := fun i => baseChange a b (algebraMap ℚ S) (f i) with hv
  have hdet : (QuaternionAlgebra.basisOneIJK ((a : ℤ) : S) 0 ((b : ℤ) : S)).det v =
      algebraMap ℚ S ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).det f) := by
    rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      QuaternionAlgebra.coe_basisOneIJK_repr, hv]
    fin_cases i <;> rfl
  have hq : IsUnit ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).det f) :=
    (Basis.is_basis_iff_det _).mp ⟨f.linearIndependent, f.span_eq⟩
  have hS : IsUnit ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : S) 0 ((b : ℤ) : S)).det v) := by
    rw [hdet]; exact hq.map _
  have hb := (Basis.is_basis_iff_det _).mpr hS
  let F := Basis.mk hb.1 hb.2.ge
  have hF : ∀ i, F i = v i := fun i => Basis.mk_apply _ _ _
  refine ⟨F, hF, fun z i => ?_⟩
  have hz : baseChange a b (algebraMap ℚ S) z = ∑ j, algebraMap ℚ S (f.repr z j) • F j := by
    conv_lhs => rw [← f.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [baseChange_algebraMap_smul, hF]
  rw [hz, Basis.repr_sum_self]

end BaseChange

section Span

variable {B M S R : Type*} [AddCommGroup B] [CommRing S] [AddCommGroup M] [Module S M]
  [CommRing R] [Algebra R S] [Module R M] [hRSM : IsScalarTower R S M]

/-- Proof helper: the `R`-span of `j(L)` for a ℤ-basis `e` of `L` whose image is an `S`-basis `F`: membership is
coordinatewise membership in the image of `R`. -/
theorem mem_span_image_iff_repr {L : Submodule ℤ B} (e : Basis (Fin 4) ℤ L) (j : B →+ M)
    (F : Basis (Fin 4) S M) (hF : ∀ i, F i = j (e i)) (w : M) :
    w ∈ Submodule.span R (j '' (L : Set B)) ↔ ∀ i, F.repr w i ∈ (algebraMap R S).range := by
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro i
      have hz' : j z = ∑ k, ((e.repr ⟨z, hz⟩ k : ℤ) : S) • F k := by
        change j ((⟨z, hz⟩ : L) : B) = _
        rw [val_eq_sum_repr e, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, hF, Int.cast_smul_eq_zsmul]
      rw [hz', Basis.repr_sum_self]
      exact ⟨(e.repr ⟨z, hz⟩ i : R), by simp⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨r, hr⟩ := hx i
      obtain ⟨s, hs⟩ := hy i
      exact ⟨r + s, by simp [hr, hs]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨s, hs⟩ := hx i
      refine ⟨r * s, ?_⟩
      rw [← algebraMap_smul S r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hs]
  · intro h
    choose r hr using h
    rw [← F.sum_repr w]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hr i, algebraMap_smul, hF]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (e i).2, rfl⟩)

end Span

/-! ### Item 41 -/

/-- Proof helper: `𝔸_f = ℚ + Ẑ`. -/
theorem finAdele_exists_sub_mem_zhat (c : FinAdele) : ∃ q : ℚ, c - algebraMap ℚ FinAdele q ∈ Zhat := by
  obtain ⟨q, hq⟩ := RestrictedProduct.padic_exists_sub_mem_structureSubring c
  exact ⟨q, by rw [mem_zhat]; exact RestrictedProduct.mem_structureSubring_iff.mp hq⟩

/-- Proof helper: every finite adele has a denominator. -/
theorem finAdele_exists_den (c : FinAdele) : ∃ N : ℕ, 0 < N ∧ (N : FinAdele) * c ∈ Zhat := by
  obtain ⟨q, hq⟩ := finAdele_exists_sub_mem_zhat c
  refine ⟨q.den, q.den_pos, ?_⟩
  have h : (q.den : FinAdele) * c = (q.den : FinAdele) * (c - algebraMap ℚ FinAdele q) +
      ((q.num : ℤ) : FinAdele) := by
    rw [mul_sub, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul, ← map_intCast (algebraMap ℚ FinAdele),
      mul_comm (q.den : ℚ), Rat.mul_den_eq_num]
    ring
  rw [h]
  exact Zhat.add_mem (Zhat.mul_mem (natCast_mem Zhat _) hq) (intCast_mem Zhat _)

/-- Proof helper: a rational number in `Ẑ` is an integer. -/
theorem rat_isInt_of_mem_zhat (q : ℚ) (h : algebraMap ℚ FinAdele q ∈ Zhat) : ∃ n : ℤ, q = n := by
  refine rat_isInt_of_forall_padicInt q fun p => ?_
  have := mem_zhat.mp h p
  exact (PadicInt.mem_subring_iff p.1).mp this

/-- Proof helper: membership in `Ẑ` as the range of `Ẑ → 𝔸_f`. -/
theorem mem_range_algebraMap_zhat (c : FinAdele) : c ∈ (algebraMap Zhat FinAdele).range ↔ c ∈ Zhat :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨c, h⟩, rfl⟩⟩

/-- Proof helper: the coordinates of `L̂` (for a lattice `L` with ℤ-basis `e`, ℚ-basis `f`). -/
theorem exists_bhat_basis {a b : ℤ} {L : Submodule ℤ (QuatAlg ℚ a b)} (e : Basis (Fin 4) ℤ L)
    (f : Basis (Fin 4) ℚ (QuatAlg ℚ a b)) (hf : ∀ i, f i = (e i : QuatAlg ℚ a b)) :
    ∃ F : Basis (Fin 4) FinAdele (BHat a b), (∀ i, F i = finEmbed a b (f i)) ∧
      (∀ z i, F.repr (finEmbed a b z) i = algebraMap ℚ FinAdele (f.repr z i)) ∧
      ∀ w, w ∈ latticeCompletion L ↔ ∀ i, F.repr w i ∈ Zhat := by
  obtain ⟨F, hF1, hF2⟩ := exists_baseChange_basis (S := FinAdele) a b f
  refine ⟨F, hF1, hF2, fun w => ?_⟩
  have := mem_span_image_iff_repr (R := Zhat) (hRSM := ⟨fun c d w => by
      change ((c : FinAdele) * d) • w = (c : FinAdele) • (d • w); exact mul_smul _ _ _⟩) e (finEmbed a b).toAddMonoidHom F
    (fun i => by rw [← hf]; exact hF1 i) w
  simp only [mem_range_algebraMap_zhat] at this
  exact this

/-- Item 41(a) helper: `ι⁻¹(L̂) = L`. -/
theorem preimage_latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) :
    finEmbed a b ⁻¹' (latticeCompletion L : Set (BHat a b)) = (L : Set (QuatAlg ℚ a b)) := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
  obtain ⟨F, _, hF2, hF3⟩ := exists_bhat_basis e f hf
  ext z
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [hF3, mem_lattice_iff_repr e f hf]
  simp only [hF2]
  exact ⟨fun h i => rat_isInt_of_mem_zhat _ (h i), fun h i => by
    obtain ⟨n, hn⟩ := h i; rw [hn, map_intCast]; exact intCast_mem Zhat n⟩

/-- Proof helper: `L̂` is closed under `Ẑ`-scalars written through `𝔸_f`. -/
theorem smul_mem_latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) {c : FinAdele} (hc : c ∈ Zhat)
    {w : BHat a b} (hw : w ∈ latticeCompletion L) : c • w ∈ latticeCompletion L :=
  (latticeCompletion L).smul_mem (⟨c, hc⟩ : Zhat) hw

/-- Proof helper: for a lattice `L` and `x ∈ B̂`, some `N > 0` has `N x L̂ ⊆ L̂`. -/
theorem exists_den_mul_latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (x : BHat a b) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ latticeCompletion L, (N : FinAdele) • (x * y) ∈ latticeCompletion L := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, _, hF3⟩ := exists_bhat_basis e f hf
  -- denominators of the coordinates of `x F_i`
  have hden : ∀ i k, ∃ N : ℕ, 0 < N ∧ (N : FinAdele) * F.repr (x * F i) k ∈ Zhat :=
    fun i k => finAdele_exists_den _
  choose N hN0 hN using hden
  refine ⟨∏ i, ∏ k, N i k, Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => hN0 i k, fun y hy => ?_⟩
  have hNi : ∀ i, ((∏ i, ∏ k, N i k : ℕ) : FinAdele) • (x * F i) ∈ latticeCompletion L := by
    intro i
    rw [hF3]
    intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨m, hm⟩ : N i k ∣ ∏ i, ∏ k, N i k :=
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
        (Finset.dvd_prod_of_mem (fun i => ∏ k, N i k) (Finset.mem_univ i))
    rw [hm, Nat.cast_mul, mul_comm ((N i k : ℕ) : FinAdele), mul_assoc]
    exact Zhat.mul_mem (natCast_mem Zhat _) (hN i k)
  have hy' := (hF3 y).mp hy
  rw [← F.sum_repr y, Finset.mul_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_smul_comm, smul_comm]
  exact smul_mem_latticeCompletion L (hy' i) (hNi i)

end LocalGlobalHelpers

/-- Proof helper: the coordinate maps of an `𝔸_f`-basis of `B̂` are continuous, and so is their inverse. -/
theorem continuous_basis_equivFun {a b : ℤ} (F : Module.Basis (Fin 4) FinAdele (BHat a b)) :
    Continuous F.equivFun ∧ Continuous F.equivFun.symm := by
  obtain ⟨hadd, -, hsmul⟩ := continuous_bhat_ops a b
  refine ⟨?_, LinearMap.continuous_on_pi (F.equivFun.symm : (Fin 4 → FinAdele) →ₗ[FinAdele] BHat a b)⟩
  let g : (Fin 4 → FinAdele) →ₗ[FinAdele] (Fin 4 → FinAdele) :=
    (F.equivFun : BHat a b →ₗ[FinAdele] Fin 4 → FinAdele).comp
      ((QuaternionAlgebra.linearEquivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).symm :
        (Fin 4 → FinAdele) →ₗ[FinAdele] QuatAlg FinAdele a b)
  have hg : Continuous g := LinearMap.continuous_on_pi g
  have h : (F.equivFun : BHat a b → Fin 4 → FinAdele) =
      g ∘ fun x : BHat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x := by
    funext x
    change F.equivFun x = F.equivFun ((QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).symm
      (QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) x))
    exact congrArg F.equivFun
      ((QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).symm_apply_apply x).symm
  rw [h]
  exact hg.comp continuous_induced_dom

/-- For a lattice `L`, `L̂` is compact and open in `B̂`; for an order `O`, `Ô^×` is a compact open subgroup of `B̂^×`. -/
@[tf_id "III.qcls.lem:order-completion-compact-open"]
theorem latticeCompletion_compact_open (a b : ℤ) :
    (∀ L : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      IsCompact (latticeCompletion L : Set (BHat a b)) ∧ IsOpen (latticeCompletion L : Set (BHat a b))) ∧
    (∀ O : QOrder a b, IsCompact (orderCompletionUnits O : Set (BHat a b)ˣ) ∧
      IsOpen (orderCompletionUnits O : Set (BHat a b)ˣ)) := by
  have hL : ∀ L : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      IsCompact (latticeCompletion L : Set (BHat a b)) ∧ IsOpen (latticeCompletion L : Set (BHat a b)) := by
    intro L hfg hspan
    obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
    obtain ⟨F, -, -, hF3⟩ := exists_bhat_basis e f hf
    obtain ⟨hc, hc'⟩ := continuous_basis_equivFun F
    set S : Set (Fin 4 → FinAdele) := Set.univ.pi fun _ => (Zhat : Set FinAdele) with hS
    have hpre : (latticeCompletion L : Set (BHat a b)) = F.equivFun ⁻¹' S := by
      ext w
      simp only [SetLike.mem_coe, hF3, Set.mem_preimage, hS, Set.mem_univ_pi, Module.Basis.equivFun_apply]
    have himg : (latticeCompletion L : Set (BHat a b)) = F.equivFun.symm '' S := by
      rw [hpre, LinearEquiv.image_symm_eq_preimage]
    refine ⟨?_, ?_⟩
    · rw [himg]
      exact (isCompact_univ_pi fun _ => isCompact_zhat).image hc'
    · rw [hpre]
      exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_zhat_adele).preimage hc
  refine ⟨hL, fun O => ?_⟩
  have := continuousMul_bhat a b
  have : T2Space (BHat a b) := (isOpenEmbedding_bhat_coords a b).isEmbedding.t2Space
  obtain ⟨hcpt, hopen⟩ := hL _ O.fg O.span_eq_top
  let S : Submonoid (BHat a b) :=
    { carrier := latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)
      mul_mem' := fun hx hy => mul_mem_orderCompletion O hx hy
      one_mem' := one_mem_orderCompletion O }
  have hset : (orderCompletionUnits O : Set (BHat a b)ˣ) = (S.units : Set (BHat a b)ˣ) := rfl
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact Submonoid.units_isCompact (S := S) hcpt
  · refine isOpen_induced_iff.mpr ⟨(latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ×ˢ
      (MulOpposite.unop ⁻¹' (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))),
      hopen.prod (hopen.preimage MulOpposite.continuous_unop), ?_⟩
    ext u
    rfl

/-! ## §3 Local–global for lattices -/

/-- The lattice `L_x := ι⁻¹(xÔ) ⊆ B` of `x ∈ B̂^×` and an order `O`. -/
@[tf_aux "III.qcls.def:finite-idele-lattice"]
noncomputable def finiteIdeleLattice {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) :
    Submodule ℤ (QuatAlg ℚ a b) where
  carrier := {z | ∃ y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra),
    finEmbed a b z = (x : BHat a b) * y}
  zero_mem' := ⟨0, Submodule.zero_mem _, by rw [map_zero, mul_zero]⟩
  add_mem' := by
    rintro z w ⟨y, hy, hz⟩ ⟨y', hy', hw⟩
    exact ⟨y + y', Submodule.add_mem _ hy hy', by rw [map_add, hz, hw, mul_add]⟩
  smul_mem' := by
    rintro n z ⟨y, hy, hz⟩
    refine ⟨n • y, ?_, ?_⟩
    · exact (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)).toAddSubgroup.zsmul_mem hy n
    · have h1 : finEmbed a b (n • z) = (n : BHat a b) * finEmbed a b z := by
        rw [← map_intCast (finEmbed a b) n, ← map_mul, ← zsmul_eq_mul]
      rw [h1, hz, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, Int.cast_comm]


section LocalGlobalHelpers2

open Module

/-- Item 41(b) helper. -/
theorem finiteIdeleLattice_props {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) :
    (finiteIdeleLattice O x).FG ∧
      Submodule.span ℚ (finiteIdeleLattice O x : Set (QuatAlg ℚ a b)) = ⊤ ∧
      (latticeCompletion (finiteIdeleLattice O x) : Set (BHat a b)) =
        (x : BHat a b) • (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) := by
  set L := Subalgebra.toSubmodule O.toSubalgebra with hL
  have hfg : L.FG := O.fg
  have hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ := O.span_eq_top
  obtain ⟨N1, hN1, h1⟩ := exists_den_mul_latticeCompletion L hfg hspan (x : BHat a b)
  obtain ⟨N2, hN2, h2⟩ := exists_den_mul_latticeCompletion L hfg hspan ((x⁻¹ : (BHat a b)ˣ) : BHat a b)
  have hpre := preimage_latticeCompletion L hfg hspan
  have hι : ∀ (n : ℕ) (z : QuatAlg ℚ a b), finEmbed a b (n • z) = (n : FinAdele) • finEmbed a b z := by
    intro n z; rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  have hsub : ∀ z ∈ finiteIdeleLattice O x, N1 • z ∈ L := by
    rintro z ⟨y, hy, hz⟩
    have h : finEmbed a b (N1 • z) ∈ latticeCompletion L := by
      rw [hι, hz]; exact h1 y hy
    have h' : N1 • z ∈ finEmbed a b ⁻¹' (latticeCompletion L : Set (BHat a b)) := h
    rw [hpre] at h'
    exact h'
  have hsup : ∀ z ∈ L, N2 • z ∈ finiteIdeleLattice O x := by
    intro z hz
    refine ⟨(N2 : FinAdele) • (((x⁻¹ : (BHat a b)ˣ) : BHat a b) * finEmbed a b z),
      h2 _ (Submodule.subset_span ⟨z, hz, rfl⟩), ?_⟩
    rw [hι, mul_smul_comm, Units.mul_inv_cancel_left]
  have hN1q : (N1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN1.ne'
  have hN2q : (N2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN2.ne'
  refine ⟨?_, ?_, ?_⟩
  · let g : QuatAlg ℚ a b →ₗ[ℤ] QuatAlg ℚ a b :=
      (((N1 : ℚ)⁻¹) • LinearMap.id : QuatAlg ℚ a b →ₗ[ℚ] QuatAlg ℚ a b).restrictScalars ℤ
    refine fg_of_le_fg (hfg.map g) fun z hz => ⟨N1 • z, hsub z hz, ?_⟩
    change ((N1 : ℚ)⁻¹) • (N1 • z) = z
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN1q, one_smul]
  · refine eq_top_iff.mpr ?_
    rw [← hspan]
    refine Submodule.span_le.mpr fun z hz => ?_
    have hz' : z = ((N2 : ℚ)⁻¹) • (N2 • z) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN2q, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hsup z hz))
  · ext w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨z, ⟨y, hy, hz⟩, rfl⟩ := hv
        exact ⟨y, hy, hz.symm⟩
      | zero => exact ⟨0, Submodule.zero_mem _, mul_zero _⟩
      | add v v' _ _ hv hv' =>
        obtain ⟨y, hy, rfl⟩ := hv
        obtain ⟨y', hy', rfl⟩ := hv'
        exact ⟨y + y', Submodule.add_mem _ hy hy', mul_add _ _ _⟩
      | smul c v _ hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
        change (x : BHat a b) * ((c : FinAdele) • y) = (c : FinAdele) • ((x : BHat a b) * y)
        rw [mul_smul_comm]
    · rintro ⟨y, hy, rfl⟩
      change (x : BHat a b) * y ∈ latticeCompletion (finiteIdeleLattice O x)
      obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
      obtain ⟨F, hF1, _, hF3⟩ := exists_bhat_basis e f hf
      set v := (x : BHat a b) * y with hv
      have happrox : ∀ i, ∃ q : ℚ, algebraMap ℚ FinAdele ((N2 : ℚ)⁻¹) * F.repr v i - algebraMap ℚ FinAdele q ∈ Zhat :=
        fun i => finAdele_exists_sub_mem_zhat _
      choose q hq using happrox
      set u : Fin 4 → FinAdele := fun i =>
        algebraMap ℚ FinAdele ((N2 : ℚ)⁻¹) * F.repr v i - algebraMap ℚ FinAdele (q i) with hu
      have hc : ∀ i, F.repr v i = algebraMap ℚ FinAdele (N2 * q i) + (N2 : FinAdele) * u i := by
        intro i
        simp only [hu, mul_sub, map_mul, map_natCast]
        have key : (N2 : FinAdele) * algebraMap ℚ FinAdele ((N2 : ℚ)⁻¹) = 1 := by
          rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hN2q, map_one]
        linear_combination (-(F.repr v i)) * key
      set z : QuatAlg ℚ a b := ∑ i, ((N2 : ℚ) * q i) • f i with hz
      set y' : BHat a b := ∑ i, u i • F i with hy'
      have hy'mem : y' ∈ latticeCompletion L := by
        rw [hF3]; intro i; rw [hy', Basis.repr_sum_self]; exact hq i
      have hιz : finEmbed a b z = ∑ i, algebraMap ℚ FinAdele ((N2 : ℚ) * q i) • F i := by
        rw [hz, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hF1]
        exact baseChange_algebraMap_smul a b _ _
      have hvsplit : v = finEmbed a b z + (N2 : FinAdele) • y' := by
        conv_lhs => rw [← F.sum_repr v]
        rw [hιz, hy', Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc, add_smul, smul_smul]
      have hzmem : z ∈ finiteIdeleLattice O x := by
        refine ⟨y - (N2 : FinAdele) • (((x⁻¹ : (BHat a b)ˣ) : BHat a b) * y'),
          Submodule.sub_mem _ hy (h2 y' hy'mem), ?_⟩
        rw [mul_sub, mul_smul_comm, Units.mul_inv_cancel_left, ← hv, hvsplit]
        abel
      have hN2y' : (N2 : FinAdele) • y' ∈ latticeCompletion (finiteIdeleLattice O x) := by
        rw [hy', Finset.smul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_comm]
        refine smul_mem_latticeCompletion _ (hq i) ?_
        have : (N2 : FinAdele) • F i = finEmbed a b (N2 • (e i : QuatAlg ℚ a b)) := by
          rw [hι, hF1, hf]
        rw [this]
        exact Submodule.subset_span ⟨_, hsup _ (e i).2, rfl⟩
      rw [hvsplit]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨z, hzmem, rfl⟩) hN2y'

/-- Item 41(c) helper: local containment implies containment. -/
theorem le_of_forall_padic_span {a b : ℤ} (L L' : Submodule ℤ (QuatAlg ℚ a b)) (hfg' : L'.FG)
    (hspan' : Submodule.span ℚ (L' : Set (QuatAlg ℚ a b)) = ⊤)
    (h : ∀ p : Nat.Primes, ∀ z ∈ L, baseChange a b (algebraMap ℚ ℚ_[p]) z ∈
      Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L' : Set (QuatAlg ℚ a b)))) :
    L ≤ L' := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L' hfg' hspan'
  intro z hz
  rw [mem_lattice_iff_repr e f hf]
  intro i
  refine rat_isInt_of_forall_padicInt _ fun p => ?_
  obtain ⟨F, hF1, hF2⟩ := exists_baseChange_basis (S := ℚ_[p]) a b f
  have h' := (mem_span_image_iff_repr (R := ℤ_[p]) e (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom F
    (fun i => by rw [← hf]; exact hF1 i) _).mp (h p z hz) i
  rw [hF2] at h'
  obtain ⟨t, ht⟩ := h'
  rw [← eq_ratCast (algebraMap ℚ ℚ_[p]), ← ht]
  exact PadicInt.norm_le_one t

end LocalGlobalHelpers2

/-- Local–global principle for lattices. (a) `ι⁻¹(L̂) = L` for a lattice `L`; (b) for `x ∈ B̂^×` and an order `O`,
`L_x = ι⁻¹(xÔ)` is a lattice with `L̂_x = xÔ`; (c) a lattice is determined by its localisations
`L_p = ℤ_p-span of L in B_p`, and `L̂ = L̂' ⇔ L = L'`. -/
@[tf_id "III.qcls.thm:lattice-local-global"]
theorem lattice_local_global (a b : ℤ) :
    (∀ L : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      finEmbed a b ⁻¹' (latticeCompletion L : Set (BHat a b)) = (L : Set (QuatAlg ℚ a b))) ∧
    (∀ (O : QOrder a b) (x : (BHat a b)ˣ),
      (finiteIdeleLattice O x).FG ∧
      Submodule.span ℚ (finiteIdeleLattice O x : Set (QuatAlg ℚ a b)) = ⊤ ∧
      (latticeCompletion (finiteIdeleLattice O x) : Set (BHat a b)) =
        (x : BHat a b) • (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))) ∧
    (∀ L L' : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      L'.FG → Submodule.span ℚ (L' : Set (QuatAlg ℚ a b)) = ⊤ →
      ((∀ p : Nat.Primes,
          Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) =
            Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L' : Set (QuatAlg ℚ a b)))) →
        L = L') ∧
      (latticeCompletion L = latticeCompletion L' ↔ L = L')) := by
  refine ⟨preimage_latticeCompletion, finiteIdeleLattice_props, fun L L' hfg hspan hfg' hspan' => ⟨fun h => ?_, ?_⟩⟩
  · refine le_antisymm (le_of_forall_padic_span L L' hfg' hspan' fun p z hz => ?_)
      (le_of_forall_padic_span L' L hfg hspan fun p z hz => ?_)
    · rw [← h p]; exact Submodule.subset_span ⟨z, hz, rfl⟩
    · rw [h p]; exact Submodule.subset_span ⟨z, hz, rfl⟩
  · refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    have h1 := preimage_latticeCompletion L hfg hspan
    have h2 := preimage_latticeCompletion L' hfg' hspan'
    rw [h] at h1
    exact SetLike.coe_injective (h1.symm.trans h2)

end GL2TF.Quat
