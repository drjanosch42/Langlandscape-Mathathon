import AlgJL.Meta.Tag
import AlgJL.Common.QuaternionNorm
import AlgJL.VolIII.P2.Orders
import AlgJL.VolIII.P2.Adelic
import AlgJL.VolIII.P2.QuatAlg
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Class sets, stabilizers, the Minkowski bound and finiteness (Q2 U5, items 42–50)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §4 (items 42–50 of `docs/sprints/Q2-plan.md` §1.2).

Side convention (conventions row N20, plan trap 6): `B^×` acts on the left, `Ô^×` on the right; the lattice of
`x ∈ B̂^×` is the right `O`-ideal `L_x = ι⁻¹(xÔ)` (`finiteIdeleLattice`, Adelic), and `Γ_x = {γ : ι(γ) ∈ xÔ^×x⁻¹}`.
* `classSet O`: `X(O) = B^× \ B̂^× / Ô^×` (`DoubleCoset.Quotient` of `ι(B^×)` and `Ô^×`).
* `classStabilizer U x`: `Γ_x(U) = {γ ∈ B^× : ι(γ) ∈ xUx⁻¹}` for any subgroup `U ≤ B̂^×` (snippet 49); `Γ_x = Γ_x(Ô^×)`.

`ι(B^×) ≤ B̂^×` is written inline as `(Units.map (finEmbed a b).toMonoidHom).range`. `γL` for `γ ∈ B^×` is the image of
`L` under left multiplication. Lattices (`L.FG`, `ℚL = B`) and right `O`-stability are inline binders; "definite" is
`a < 0 ∧ b < 0` inline. The localisations `L_p` of item 43(d) are written inline as `ℤ_p`-spans in `B_{ℚ_p}` (as in
item 41(c)), since `LocalStructure` is outside the vocabulary of `Hyp.EichlerMass` (`registry/hyp_imports.yaml`).
Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

open scoped Quaternion Pointwise

namespace GL2TF.Quat

open GL2TF

/-! ## §1 The class set -/

/-- The class set `X(O) = B^× \ B̂^× / Ô^×` of an order `O`: double cosets `ι(B^×) x Ô^×`, with `B^×` acting on the
left and `Ô^×` on the right. -/
@[tf_id "III.qcls.def:class-set"]
def classSet {a b : ℤ} (O : QOrder a b) : Type :=
  DoubleCoset.Quotient ((Units.map (finEmbed a b).toMonoidHom).range : Set (BHat a b)ˣ)
    (orderCompletionUnits O : Set (BHat a b)ˣ)

/-! ## Proof helpers: local description of `Ô` (item 43(d)) -/

/-- Proof helper: the evaluation `B̂ → B_{ℚ_p}` at a prime `p`. -/
private noncomputable abbrev evP (a b : ℤ) (p : Nat.Primes) : QuatAlg FinAdele a b →+* QuatAlg ℚ_[p] a b :=
  baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])

private theorem evP_finEmbed_aux {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ a b) :
    evP a b p (finEmbed a b z) = baseChange a b (algebraMap ℚ ℚ_[p]) z := by
  ext <;> rfl

private theorem evP_smul_aux {a b : ℤ} (p : Nat.Primes) (c : FinAdele) (v : QuatAlg FinAdele a b) :
    evP a b p (c • v) = (c p) • evP a b p v := by
  ext <;> simp [baseChange]

private theorem bhat_ext_aux {a b : ℤ} {v w : QuatAlg FinAdele a b} (h : ∀ p, evP a b p v = evP a b p w) : v = w := by
  apply QuaternionAlgebra.ext
  · ext p; exact congrArg QuaternionAlgebra.re (h p)
  · ext p; exact congrArg QuaternionAlgebra.imI (h p)
  · ext p; exact congrArg QuaternionAlgebra.imJ (h p)
  · ext p; exact congrArg QuaternionAlgebra.imK (h p)

private theorem mem_padicInt_range_aux (p : Nat.Primes) (x : ℚ_[p]) :
    x ∈ (algebraMap ℤ_[p] ℚ_[p]).range ↔ x ∈ PadicInt.subring p :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- Proof helper: membership in `L̂` is local. -/
private theorem mem_latticeCompletion_iff_local_aux {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (w : BHat a b) :
    w ∈ latticeCompletion L ↔ ∀ p : Nat.Primes, evP a b p w ∈
      Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, _, hF3⟩ := exists_bhat_basis e f hf
  have hloc : ∀ p : Nat.Primes, ∃ Fp : Module.Basis (Fin 4) ℚ_[p] (QuatAlg ℚ_[p] a b),
      (∀ i, Fp i = baseChange a b (algebraMap ℚ ℚ_[p]) (f i)) ∧
      ∀ i, Fp.repr (evP a b p w) i = F.repr w i p := by
    intro p
    obtain ⟨Fp, hFp1, -⟩ := exists_baseChange_basis (S := ℚ_[p]) a b f
    refine ⟨Fp, hFp1, fun i => ?_⟩
    have : evP a b p w = ∑ j, (F.repr w j p) • Fp j := by
      conv_lhs => rw [← F.sum_repr w]
      erw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [evP_smul_aux]; rw [hF1]; erw [evP_finEmbed_aux]; rw [hFp1]
    rw [this, Module.Basis.repr_sum_self]
  choose Fp hFp1 hFp2 using hloc
  rw [hF3]
  have hspan_iff : ∀ p : Nat.Primes, evP a b p w ∈ Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
      (L : Set (QuatAlg ℚ a b))) ↔ ∀ i, F.repr w i p ∈ PadicInt.subring p := by
    intro p
    refine (mem_span_image_iff_repr (R := ℤ_[p]) e (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom (Fp p)
      (fun i => by rw [← hf]; exact hFp1 p i) _).trans ?_
    simp only [hFp2, mem_padicInt_range_aux]
  simp only [hspan_iff, mem_zhat]
  exact ⟨fun h p i => h i p, fun h i p => h p i⟩

/-- Proof helper: the element of `B̂` with `p`-components `g p` (`p ∈ S`) and `1` (`p ∉ S`). -/
private noncomputable def glueAux {a b : ℤ} (S : Finset Nat.Primes) (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) :
    QuatAlg FinAdele a b :=
  (QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).symm fun k =>
    ⟨fun p => QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ_[p]) 0 ((b : ℤ) : ℚ_[p])
      (haveI := Classical.propDecidable (p ∈ S); if p ∈ S then g p else 1) k, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with p hp
      have hp' : p ∉ S := hp
      simp only [hp', ite_false]
      fin_cases k <;> simp⟩

private theorem evP_glueAux {a b : ℤ} (S : Finset Nat.Primes) (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b)
    (p : Nat.Primes) : evP a b p (glueAux S g) = if p ∈ S then g p else 1 := by
  classical
  have e : (@ite _ (p ∈ S) (Classical.propDecidable _) (g p) 1) = if p ∈ S then g p else 1 := by
    congr
  apply QuaternionAlgebra.ext
  · exact congrArg QuaternionAlgebra.re e
  · exact congrArg QuaternionAlgebra.imI e
  · exact congrArg QuaternionAlgebra.imJ e
  · exact congrArg QuaternionAlgebra.imK e

/-- Proof helper: item 43(d). -/
private theorem classSet_right_ideals_d_aux {a b : ℤ} (O : QOrder a b) :
    (∀ L : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      (∀ y z : QuatAlg ℚ a b, y ∈ L → z ∈ O.toSubalgebra → y * z ∈ L) →
      ∀ (S : Finset Nat.Primes) (β : ∀ p : Nat.Primes, (QuatAlg ℚ_[p] a b)ˣ),
      (∀ p ∈ S, Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) =
        (Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
          (O.toSubalgebra : Set (QuatAlg ℚ a b)))).map (LinearMap.mulLeft ℤ_[p] (β p : QuatAlg ℚ_[p] a b))) →
      (∀ p : Nat.Primes, p ∉ S →
        Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) =
          Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (O.toSubalgebra : Set (QuatAlg ℚ a b)))) →
      ∃ x : (BHat a b)ˣ,
        (∀ p ∈ S, baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])
          (show QuatAlg FinAdele a b from (x : BHat a b)) = (β p : QuatAlg ℚ_[p] a b)) ∧
        (∀ p : Nat.Primes, p ∉ S → baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])
          (show QuatAlg FinAdele a b from (x : BHat a b)) = 1) ∧
        L = finiteIdeleLattice O x) := by
  intro L hFG hspan _ S β hS hnS
  classical
  set gx : QuatAlg FinAdele a b := glueAux S (fun p => (β p : QuatAlg ℚ_[p] a b))
  set gy : QuatAlg FinAdele a b := glueAux S (fun p => ((β p)⁻¹ : (QuatAlg ℚ_[p] a b)ˣ))
  have hxy : gx * gy = 1 := bhat_ext_aux fun p => by
    rw [map_mul, evP_glueAux, evP_glueAux, map_one]; split_ifs <;> simp
  have hyx : gy * gx = 1 := bhat_ext_aux fun p => by
    rw [map_mul, evP_glueAux, evP_glueAux, map_one]; split_ifs <;> simp
  let x : (BHat a b)ˣ := ⟨gx, gy, hxy, hyx⟩
  have hOloc := mem_latticeCompletion_iff_local_aux (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  refine ⟨x, fun p hp => ?_, fun p hp => ?_, le_antisymm ?_ ?_⟩
  · show evP a b p gx = _
    rw [evP_glueAux]; simp [hp]
  · show evP a b p gx = _
    rw [evP_glueAux]; simp [hp]
  · intro z hz
    refine ⟨((x⁻¹ : (BHat a b)ˣ) : BHat a b) * finEmbed a b z, ?_, by rw [Units.mul_inv_cancel_left]⟩
    rw [hOloc]
    intro p
    have hzp : baseChange a b (algebraMap ℚ ℚ_[p]) z ∈
        Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) :=
      Submodule.subset_span ⟨z, hz, rfl⟩
    show evP a b p (gy * (show QuatAlg FinAdele a b from finEmbed a b z)) ∈ _
    rw [map_mul, evP_finEmbed_aux, evP_glueAux]
    split_ifs with hp
    · rw [hS p hp] at hzp
      obtain ⟨o, ho, hoe⟩ := Submodule.mem_map.mp hzp
      rw [← hoe, LinearMap.mulLeft_apply, ← mul_assoc, Units.inv_mul, one_mul]
      exact ho
    · rw [one_mul]
      have h := hnS p hp ▸ hzp
      exact h
  · refine le_of_forall_padic_span _ L hFG hspan fun p z hz => ?_
    obtain ⟨w, hw, hzw⟩ := hz
    rw [hOloc] at hw
    have h1 := congrArg (evP a b p) hzw
    rw [evP_finEmbed_aux] at h1
    rw [h1]
    show evP a b p (gx * (show QuatAlg FinAdele a b from w)) ∈ _
    rw [map_mul, evP_glueAux]
    split_ifs with hp
    · rw [hS p hp]
      exact Submodule.mem_map_of_mem (hw p)
    · rw [one_mul, hnS p hp]
      exact hw p

/-- Right ideals and the class set, for `L_x = ι⁻¹(xÔ)`: (a) `L_x O ⊆ L_x`; (b) `L_{ι(γ)xu} = γ L_x` for `γ ∈ B^×`,
`u ∈ Ô^×`; (c) `L_x = γ L_y` implies `[x] = [y]` in `X(O)`; (d) a lattice `L` with `LO ⊆ L` whose localisations are
`L_p = β_p O_p` for `p` in a finite set `S` and `L_p = O_p` otherwise equals `L_x` for the `x ∈ B̂^×` with
`p`-components `β_p` (`p ∈ S`) and `1` (`p ∉ S`). Here `L_p` is the `ℤ_p`-span of the image of `L` in `B_{ℚ_p}`. -/
@[tf_id "III.qcls.thm:class-set-right-ideals"]
theorem classSet_right_ideals {a b : ℤ} (O : QOrder a b) :
    (∀ (x : (BHat a b)ˣ) (y z : QuatAlg ℚ a b), y ∈ finiteIdeleLattice O x → z ∈ O.toSubalgebra →
      y * z ∈ finiteIdeleLattice O x) ∧
    (∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      finiteIdeleLattice O (Units.map (finEmbed a b).toMonoidHom γ * x * u) =
        (finiteIdeleLattice O x).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b))) ∧
    (∀ (x y : (BHat a b)ˣ) (γ : (QuatAlg ℚ a b)ˣ),
      finiteIdeleLattice O x = (finiteIdeleLattice O y).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) →
      (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x : classSet O) =
        DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) y) ∧
    (∀ L : Submodule ℤ (QuatAlg ℚ a b), L.FG → Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤ →
      (∀ y z : QuatAlg ℚ a b, y ∈ L → z ∈ O.toSubalgebra → y * z ∈ L) →
      ∀ (S : Finset Nat.Primes) (β : ∀ p : Nat.Primes, (QuatAlg ℚ_[p] a b)ˣ),
      (∀ p ∈ S, Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) =
        (Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
          (O.toSubalgebra : Set (QuatAlg ℚ a b)))).map (LinearMap.mulLeft ℤ_[p] (β p : QuatAlg ℚ_[p] a b))) →
      (∀ p : Nat.Primes, p ∉ S →
        Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) =
          Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (O.toSubalgebra : Set (QuatAlg ℚ a b)))) →
      ∃ x : (BHat a b)ˣ,
        (∀ p ∈ S, baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])
          (show QuatAlg FinAdele a b from (x : BHat a b)) = (β p : QuatAlg ℚ_[p] a b)) ∧
        (∀ p : Nat.Primes, p ∉ S → baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])
          (show QuatAlg FinAdele a b from (x : BHat a b)) = 1) ∧
        L = finiteIdeleLattice O x) := by
  set Oh := latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)
  -- (b), used for (c)
  have hb : ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      finiteIdeleLattice O (Units.map (finEmbed a b).toMonoidHom γ * x * u) =
        (finiteIdeleLattice O x).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) := by
    intro γ x u hu
    have hval : ∀ g : (QuatAlg ℚ a b)ˣ,
        ((Units.map (finEmbed a b).toMonoidHom g : (BHat a b)ˣ) : BHat a b) = finEmbed a b g := fun _ => rfl
    have hγ : finEmbed a b ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) * finEmbed a b (γ : QuatAlg ℚ a b) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hγ' : finEmbed a b (γ : QuatAlg ℚ a b) * finEmbed a b ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    ext z
    simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨w, hw, hz⟩
      refine ⟨((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) * z, ⟨(u : BHat a b) * w,
        mul_mem_orderCompletion O hu.1 hw, ?_⟩, ?_⟩
      · rw [map_mul, hz]
        simp only [Units.val_mul, hval, ← mul_assoc, hγ, one_mul]
      · rw [← mul_assoc, Units.mul_inv, one_mul]
    · rintro ⟨y, ⟨w', hw', hy⟩, rfl⟩
      refine ⟨((u⁻¹ : (BHat a b)ˣ) : BHat a b) * w', mul_mem_orderCompletion O hu.2 hw', ?_⟩
      rw [map_mul, hy]
      simp only [Units.val_mul, hval, ← mul_assoc, Units.mul_inv_cancel_right]
  refine ⟨?_, hb, ?_, ?_⟩
  · -- (a)
    rintro x y z ⟨w, hw, hy⟩ hz
    refine ⟨w * finEmbed a b z, mul_mem_orderCompletion O hw (Submodule.subset_span ⟨z, hz, rfl⟩), ?_⟩
    rw [map_mul, hy, mul_assoc]
  · -- (c)
    intro x y γ h
    set y' : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom γ * y * 1
    have h' : finiteIdeleLattice O x = finiteIdeleLattice O y' := by
      rw [h, hb γ y 1 (Subgroup.one_mem _)]
    have hc := congrArg (fun L => (latticeCompletion L : Set (BHat a b))) h'
    rw [((lattice_local_global a b).2.1 O x).2.2, ((lattice_local_global a b).2.1 O y').2.2] at hc
    have h1 : (y' : BHat a b) ∈ (x : BHat a b) • (Oh : Set (BHat a b)) := by
      rw [hc]; exact ⟨1, one_mem_orderCompletion O, mul_one _⟩
    have h2 : (x : BHat a b) ∈ (y' : BHat a b) • (Oh : Set (BHat a b)) := by
      rw [← hc]; exact ⟨1, one_mem_orderCompletion O, mul_one _⟩
    obtain ⟨w, hw, hw'⟩ := h1
    obtain ⟨w', hw2, hw2'⟩ := h2
    simp only [smul_eq_mul] at hw' hw2'
    have hu : x⁻¹ * y' ∈ orderCompletionUnits O := by
      constructor
      · rw [Units.val_mul, ← hw', ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      · rw [mul_inv_rev, inv_inv, Units.val_mul, ← hw2', ← mul_assoc, Units.inv_mul, one_mul]; exact hw2
    have hyx : y = (Units.map (finEmbed a b).toMonoidHom γ)⁻¹ * x * (x⁻¹ * y') := by
      simp only [y', mul_one]; group
    rw [DoubleCoset.eq]
    exact ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, Subgroup.inv_mem _ ⟨γ, rfl⟩, x⁻¹ * y', hu, hyx⟩
  · -- (d)
    exact classSet_right_ideals_d_aux O

/-- If `O ⊆ L_x`, then the index `[L_x : O]` is a perfect square. -/
@[tf_id "III.qcls.lem:index-square"]
theorem index_square {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ)
    (hx : Subalgebra.toSubmodule O.toSubalgebra ≤ finiteIdeleLattice O x) :
    IsSquare ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
      (finiteIdeleLattice O x).toAddSubgroup) := by
  classical
  set Lx := finiteIdeleLattice O x
  obtain ⟨hFG, hspan, hcomp⟩ := (lattice_local_global a b).2.1 O x
  obtain ⟨eO, fO, hfO⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  obtain ⟨eL, fL, hfL⟩ := exists_lattice_basis Lx hFG hspan
  have hidx := AddSubgroup.relIndex_eq_abs_det _ _ hx fO fL (toAddSubgroup_eq_closure eO fO hfO)
    (toAddSubgroup_eq_closure eL fL hfL)
  set q : ℚ := fL.det fO with hqdef
  have hq0 : q ≠ 0 := (fL.isUnit_det fO).ne_zero
  have hlocL := mem_latticeCompletion_iff_local_aux Lx hFG hspan
  have hlocO := mem_latticeCompletion_iff_local_aux _ O.fg O.span_eq_top
  have hloc : ∀ p : Nat.Primes, Even (padicValRat p q) := by
    intro p
    obtain ⟨FOp, hFOp1, -⟩ := exists_baseChange_basis (S := ℚ_[p]) a b fO
    obtain ⟨FLp, hFLp1, hFLp2⟩ := exists_baseChange_basis (S := ℚ_[p]) a b fL
    have hqp : ((q : ℚ) : ℚ_[p]) = FLp.det FOp := by
      rw [Module.Basis.det_apply]
      have hm : FLp.toMatrix FOp = (algebraMap ℚ ℚ_[p]).mapMatrix (fL.toMatrix fO) := by
        ext i j
        rw [Module.Basis.toMatrix_apply, hFOp1, hFLp2]
        rfl
      rw [hm, ← RingHom.map_det, hqdef, Module.Basis.det_apply]
      rfl
    set xp : (QuatAlg ℚ_[p] a b)ˣ := Units.map (evP a b p).toMonoidHom x
    set xi : QuatAlg ℚ_[p] a b := ((xp⁻¹ : (QuatAlg ℚ_[p] a b)ˣ) : QuatAlg ℚ_[p] a b)
    let φ : QuatAlg ℚ_[p] a b ≃ₗ[ℚ_[p]] QuatAlg ℚ_[p] a b :=
      LinearEquiv.ofLinear (LinearMap.mulLeft ℚ_[p] (xp : QuatAlg ℚ_[p] a b)) (LinearMap.mulLeft ℚ_[p] xi)
        (LinearMap.ext fun v => by simp [xi, ← mul_assoc]) (LinearMap.ext fun v => by simp [xi, ← mul_assoc])
    set y := FOp.map φ
    have hyO : y.det FOp = nrd xi ^ 2 := by
      rw [Module.Basis.det_map]
      have : (φ.symm : QuatAlg ℚ_[p] a b → QuatAlg ℚ_[p] a b) ∘ FOp = (LinearMap.mulLeft ℚ_[p] xi) ∘ FOp := rfl
      rw [this, Module.Basis.det_comp, Module.Basis.det_self, mul_one, (det_mulLeft_mulRight xi).1]
    -- integrality of the two change-of-basis matrices
    have hLmem : ∀ v, v ∈ Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (Lx : Set (QuatAlg ℚ a b))) →
        ∀ i, FLp.repr v i ∈ PadicInt.subring p := fun v hv i =>
      (mem_padicInt_range_aux p _).mp ((mem_span_image_iff_repr (R := ℤ_[p]) eL
        (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom FLp (fun i => by rw [← hfL]; exact hFLp1 i) v).mp hv i)
    have hOmem : ∀ v, v ∈ Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
        ((Subalgebra.toSubmodule O.toSubalgebra : Submodule ℤ (QuatAlg ℚ a b)) : Set (QuatAlg ℚ a b))) →
        ∀ i, FOp.repr v i ∈ PadicInt.subring p := fun v hv i =>
      (mem_padicInt_range_aux p _).mp ((mem_span_image_iff_repr (R := ℤ_[p]) eO
        (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom FOp (fun i => by rw [← hfO]; exact hFOp1 i) v).mp hv i)
    have hy1 : ∀ i j, (FLp.toMatrix y) i j ∈ PadicInt.subring p := by
      intro i j
      rw [Module.Basis.toMatrix_apply]
      refine hLmem _ ?_ i
      have hmem : (x : BHat a b) * finEmbed a b (fO j) ∈ latticeCompletion Lx := by
        have : ((x : BHat a b) * finEmbed a b (fO j)) ∈ (x : BHat a b) •
            (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) :=
          ⟨_, Submodule.subset_span ⟨fO j, by rw [hfO]; exact (eO j).2, rfl⟩, rfl⟩
        rw [← hcomp] at this
        exact this
      have h := (hlocL _).mp hmem p
      have e : evP a b p ((x : BHat a b) * finEmbed a b (fO j)) = y j := by
        show evP a b p (show QuatAlg FinAdele a b from (x : BHat a b)) *
          evP a b p (finEmbed a b (fO j)) = _
        rw [evP_finEmbed_aux, ← hFOp1]
        rfl
      rw [← e]; exact h
    have hy2 : ∀ i j, (y.toMatrix FLp) i j ∈ PadicInt.subring p := by
      intro i j
      rw [Module.Basis.toMatrix_apply, Module.Basis.map_repr]
      refine hOmem _ ?_ i
      obtain ⟨w, hw, hfw⟩ := (show fL j ∈ Lx by rw [hfL]; exact (eL j).2)
      have h := (hlocO w).mp hw p
      have e : (φ.symm (FLp j)) = evP a b p (show QuatAlg FinAdele a b from w) := by
        have h1 := congrArg (evP a b p) hfw
        rw [evP_finEmbed_aux, ← hFLp1] at h1
        show xi * FLp j = _
        rw [h1]
        show xi * (evP a b p (show QuatAlg FinAdele a b from (x : BHat a b)) * evP a b p w) = _
        rw [← mul_assoc]
        show xi * (xp : QuatAlg ℚ_[p] a b) * _ = _
        rw [Units.inv_mul, one_mul]
      convert h using 1
    have hdet : ∀ A : Matrix (Fin 4) (Fin 4) ℚ_[p], (∀ i j, A i j ∈ PadicInt.subring p) → ‖A.det‖ ≤ 1 := by
      intro A hA
      have : A = (PadicInt.subring p).subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hA i j⟩ : PadicInt.subring p)) := by
        ext i j; rfl
      rw [this, ← RingHom.map_det]
      exact (Matrix.of fun i j => (⟨A i j, hA i j⟩ : PadicInt.subring p)).det.2
    have hu1 := hdet _ hy1
    have hu2 := hdet _ hy2
    rw [← Module.Basis.det_apply] at hu1 hu2
    have hprod : FLp.det y * y.det FLp = 1 := by rw [Module.Basis.det_mul_det, Module.Basis.det_self]
    have hu : ‖FLp.det y‖ = 1 := by
      have := congrArg norm hprod
      rw [norm_mul, norm_one] at this
      nlinarith [norm_nonneg (FLp.det y), norm_nonneg (y.det FLp)]
    have hnorm : ‖((q : ℚ) : ℚ_[p])‖ = ‖nrd xi‖ ^ 2 := by
      rw [hqp, ← Module.Basis.det_mul_det FLp y FOp, norm_mul, hu, one_mul, hyO, norm_pow]
    have hqp0 : ((q : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hq0
    have hc0 : nrd xi ≠ 0 := by
      intro h0; rw [h0, norm_zero, zero_pow two_ne_zero, norm_eq_zero] at hnorm; exact hqp0 hnorm
    rw [Padic.norm_eq_zpow_neg_valuation hqp0, Padic.norm_eq_zpow_neg_valuation hc0, Padic.valuation_ratCast,
      ← zpow_natCast, ← zpow_mul] at hnorm
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have := zpow_right_injective₀ (by linarith : (0 : ℝ) < p) (ne_of_gt hp1) hnorm
    exact ⟨(nrd xi).valuation, by push_cast at this; linarith⟩
  have hsq : IsSquare |q| := by
    refine Rat.isSquare_iff_even_factorization.mpr ⟨abs_nonneg _, fun p hp => ?_⟩
    rcases abs_choice q with h | h
    · rw [h]; exact hloc ⟨p, hp⟩
    · rw [h, padicValRat.neg]; exact hloc ⟨p, hp⟩
  rw [← hidx] at hsq
  exact Rat.isSquare_natCast_iff.mp hsq

/-! ## Proof helpers: the Minkowski bound (item 45) -/

/-- Proof helper: the Euclidean coordinates `x ↦ (x₀, √|a| x₁, √|b| x₂, √|ab| x₃)` of `B`. -/
private noncomputable def eucl (a b : ℤ) : QuatAlg ℚ a b →+ EuclideanSpace ℝ (Fin 4) :=
  AddMonoidHom.mk' (fun x => WithLp.toLp 2 ![(x.re : ℝ), Real.sqrt (-(a : ℝ)) * (x.imI : ℝ),
      Real.sqrt (-(b : ℝ)) * (x.imJ : ℝ), Real.sqrt ((a : ℝ) * (b : ℝ)) * (x.imK : ℝ)]) (by
    intro x y
    ext i
    fin_cases i <;> simp <;> ring)

/-- Proof helper: coordinates of `eucl`. -/
private theorem eucl_apply {a b : ℤ} (x : QuatAlg ℚ a b) :
    ((eucl a b x : EuclideanSpace ℝ (Fin 4)) : Fin 4 → ℝ) = ![(x.re : ℝ), Real.sqrt (-(a : ℝ)) * (x.imI : ℝ),
      Real.sqrt (-(b : ℝ)) * (x.imJ : ℝ), Real.sqrt ((a : ℝ) * (b : ℝ)) * (x.imK : ℝ)] := rfl

/-- Proof helper: the Euclidean inner product is half the trace form. -/
private theorem eucl_inner {a b : ℤ} (ha : a < 0) (hb : b < 0) (x y : QuatAlg ℚ a b) :
    ∑ i, (eucl a b x) i * (eucl a b y) i = ((trd (x * star y) : ℚ) : ℝ) / 2 := by
  have h1 : Real.sqrt (-(a : ℝ)) * Real.sqrt (-(a : ℝ)) = -(a : ℝ) :=
    Real.mul_self_sqrt (by have : (a : ℝ) < 0 := by exact_mod_cast ha
                           linarith)
  have h2 : Real.sqrt (-(b : ℝ)) * Real.sqrt (-(b : ℝ)) = -(b : ℝ) :=
    Real.mul_self_sqrt (by have : (b : ℝ) < 0 := by exact_mod_cast hb
                           linarith)
  have h3 : Real.sqrt ((a : ℝ) * (b : ℝ)) * Real.sqrt ((a : ℝ) * (b : ℝ)) = (a : ℝ) * (b : ℝ) :=
    Real.mul_self_sqrt (by have : (a : ℝ) < 0 := by exact_mod_cast ha
                           have : (b : ℝ) < 0 := by exact_mod_cast hb
                           nlinarith)
  simp only [Fin.sum_univ_four]
  simp [eucl, trd]
  linear_combination ((x.imI : ℝ) * y.imI) * h1 + ((x.imJ : ℝ) * y.imJ) * h2 + ((x.imK : ℝ) * y.imK) * h3

/-- Proof helper: `‖eucl x‖² = nrd x`. -/
private theorem eucl_norm_sq {a b : ℤ} (ha : a < 0) (hb : b < 0) (x : QuatAlg ℚ a b) :
    ‖eucl a b x‖ ^ 2 = ((nrd x : ℚ) : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  have := eucl_inner ha hb x x
  simp only [Real.norm_eq_abs, sq_abs]
  simp only [sq]
  rw [this]
  have : trd (x * star x) = 2 * nrd x := by simp [trd, nrd]; ring
  rw [this]; push_cast; ring

/-- Proof helper: the Gram determinant of the trace form in a ℚ-basis is non-zero. -/
private theorem det_trdGram_ne_zero {a b : ℤ} (ha : a < 0) (hb : b < 0) (f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b)) :
    (Matrix.of fun i j => trd (f i * star (f j))).det ≠ 0 := by
  rw [det_gram_change (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)) f, det_gram_basisOneIJK,
    ← Module.Basis.det_apply]
  have hu := (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).isUnit_det f
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne
  exact mul_ne_zero (pow_ne_zero _ hu.ne_zero) (by positivity)

/-- Proof helper (Minkowski): a lattice `L` with ℤ-basis `e` (ℚ-basis `f`) contains `β ≠ 0` with
`π² nrd(β)² ≤ 8 √(det trd(f_i f̄_j))`. -/
private theorem exists_short_vector {a b : ℤ} (ha : a < 0) (hb : b < 0) (L : Submodule ℤ (QuatAlg ℚ a b))
    (e : Module.Basis (Fin 4) ℤ L) (f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b)) (hf : ∀ i, f i = (e i : QuatAlg ℚ a b)) :
    ∃ β ∈ L, β ≠ 0 ∧ Real.pi ^ 2 * ((nrd β : ℚ) : ℝ) ^ 2 ≤
      8 * Real.sqrt (((Matrix.of fun i j => trd (f i * star (f j))).det : ℚ) : ℝ) := by
  classical
  set T : Matrix (Fin 4) (Fin 4) ℚ := Matrix.of fun i j => trd (f i * star (f j)) with hT
  set Mm : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => (eucl a b (f j)) i with hMm
  have hgram : Mm.transpose * Mm = (1 / 2 : ℝ) • T.map (Rat.castHom ℝ) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hMm, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply,
      hT, Rat.coe_castHom, smul_eq_mul]
    rw [eucl_inner ha hb]
    ring
  have hdet : Mm.det ^ 2 = ((T.det : ℚ) : ℝ) / 16 := by
    have h := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at h
    have hmap : (T.map (Rat.castHom ℝ)).det = ((T.det : ℚ) : ℝ) := (RingHom.map_det (Rat.castHom ℝ) T).symm
    rw [sq, h, hmap]
    ring
  have hT0 : ((T.det : ℚ) : ℝ) ≠ 0 := by exact_mod_cast det_trdGram_ne_zero ha hb f
  have hM0 : Mm.det ≠ 0 := by
    intro h0; rw [h0] at hdet; apply hT0; linarith
  set b0 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis with hb0
  have hb0det : b0.det (fun j => eucl a b (f j)) = Mm.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have hbasis := (Module.Basis.is_basis_iff_det b0).mpr (by rw [hb0det]; exact hM0.isUnit)
  let bR : Module.Basis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)) := Module.Basis.mk hbasis.1 hbasis.2.ge
  have hbR : ∀ i, bR i = eucl a b (f i) := fun i => Module.Basis.mk_apply _ _ _
  have hbRfun : (⇑bR) = fun i => eucl a b (f i) := funext hbR
  have hvolF : MeasureTheory.volume (ZSpan.fundamentalDomain bR) = ENNReal.ofReal |Mm.det| := by
    rw [ZSpan.measure_fundamentalDomain bR MeasureTheory.volume b0, hbRfun, hb0det,
      MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b0 MeasureTheory.volume), hb0,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped, mul_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  set X : ℝ := 32 * |Mm.det| / Real.pi ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  set r : ℝ := Real.sqrt (Real.sqrt X) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr4 : r ^ 4 = X := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hX0]
  have hvol : MeasureTheory.volume (ZSpan.fundamentalDomain bR) * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) ≤
      MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) r) := by
    rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp), hvolF, finrank_euclideanSpace_fin]
    rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (by positivity),
      show (2 : ENNReal) ^ 4 = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [hr4, hX]
    field_simp
    norm_num
  have : Countable (Submodule.span ℤ (Set.range bR)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range bR)))
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (ZSpan.isAddFundamentalDomain' bR MeasureTheory.volume) (fun y hy => by simpa using hy)
    (convex_closedBall 0 r) (isCompact_closedBall 0 r) hvol
  have hxL : ((x : (Submodule.span ℤ (Set.range bR)).toAddSubgroup) : EuclideanSpace ℝ (Fin 4)) ∈
      L.toAddSubgroup.map (eucl a b) := by
    have h1 : (Submodule.span ℤ (Set.range bR)).toAddSubgroup = L.toAddSubgroup.map (eucl a b) := by
      rw [Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup_eq_closure e f hf, AddMonoidHom.map_closure,
        hbRfun, ← Set.range_comp]
      rfl
    rw [← h1]; exact x.2
  obtain ⟨β, hβL, hβx⟩ := hxL
  refine ⟨β, hβL, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext1
    rw [← hβx, map_zero]
    rfl
  · have hn : ‖eucl a b β‖ ≤ r := by
      rw [hβx]; simpa using hxs
    have hnrd : ((nrd β : ℚ) : ℝ) ≤ r ^ 2 := by
      rw [← eucl_norm_sq ha hb]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hnrd0 : 0 ≤ ((nrd β : ℚ) : ℝ) := by rw [← eucl_norm_sq ha hb]; positivity
    have h2 : ((nrd β : ℚ) : ℝ) ^ 2 ≤ X := by
      rw [← hr4, show r ^ 4 = (r ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ hnrd0 hnrd 2
    have habs : |Mm.det| = Real.sqrt ((T.det : ℚ) : ℝ) / 4 := by
      rw [← Real.sqrt_sq_eq_abs, hdet, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16),
        show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc Real.pi ^ 2 * ((nrd β : ℚ) : ℝ) ^ 2 ≤ Real.pi ^ 2 * X := by gcongr
      _ = 8 * Real.sqrt ((T.det : ℚ) : ℝ) := by
        rw [hX, habs]; field_simp; ring

/-- Proof helper: `trd(u x \overline{u y}) = nrd(u) trd(x ȳ)`. -/
private theorem trd_conj_aux {a b : ℤ} (u x y : QuatAlg ℚ a b) :
    trd (u * x * star (u * y)) = nrd u * trd (x * star y) := by
  obtain ⟨u0, u1, u2, u3⟩ := u
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp [trd, nrd, QuaternionAlgebra.mk_mul_mk]
  ring

/-- **Minkowski bound.** For `a, b < 0`, an order `O` and a lattice `L` with `LO ⊆ L`, there is `β ∈ L`, `β ≠ 0` (a
unit of `B`), with `O ⊆ β⁻¹L` and `π² [β⁻¹L : O] ≤ 8 √d(O)`. -/
@[tf_id "III.qcls.thm:minkowski-bound"]
theorem minkowski_bound {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (L : Submodule ℤ (QuatAlg ℚ a b))
    (hL : L.FG) (hLs : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤)
    (hLO : ∀ y z : QuatAlg ℚ a b, y ∈ L → z ∈ O.toSubalgebra → y * z ∈ L) :
    ∃ β : (QuatAlg ℚ a b)ˣ, (β : QuatAlg ℚ a b) ∈ L ∧
      Subalgebra.toSubmodule O.toSubalgebra ≤ L.map (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) ∧
      Real.pi ^ 2 * ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex
          (L.map (LinearMap.mulLeft ℤ ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))).toAddSubgroup : ℝ) ≤
        8 * Real.sqrt (discriminant O : ℝ) := by
  classical
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hL hLs
  obtain ⟨β0, hβL, hβ0, hineq⟩ := exists_short_vector ha hb L e f hf
  set β : (QuatAlg ℚ a b)ˣ := ((definite_division ha hb).1 β0 hβ0).unit with hβ
  have hβv : (β : QuatAlg ℚ a b) = β0 := rfl
  set bi : QuatAlg ℚ a b := ((β⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)
  set L' := L.map (LinearMap.mulLeft ℤ bi)
  have hle : Subalgebra.toSubmodule O.toSubalgebra ≤ L' := by
    intro o ho
    refine ⟨(β : QuatAlg ℚ a b) * o, hLO _ _ (hβv ▸ hβL) ho, ?_⟩
    simp only [LinearMap.mulLeft_apply, bi, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨β, hβL, hle, ?_⟩
  -- the ℚ-basis `g = β⁻¹ f` of `B`, a ℤ-basis of `L'`
  let φ : QuatAlg ℚ a b ≃ₗ[ℚ] QuatAlg ℚ a b := LinearEquiv.ofLinear (LinearMap.mulLeft ℚ bi)
    (LinearMap.mulLeft ℚ (β : QuatAlg ℚ a b))
    (LinearMap.ext fun x => by simp [bi, ← mul_assoc]) (LinearMap.ext fun x => by simp [bi, ← mul_assoc])
  set g : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b) := f.map φ
  have hg : ∀ i, g i = bi * f i := fun i => rfl
  obtain ⟨eO, fO, hfO⟩ := exists_lattice_basis (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  have hd : discriminant O = (Matrix.of fun i j => trd (fO i * star (fO j))).det := by
    rw [(discriminant_basic O).1 eO]
    simp only [hfO]
  have hO : (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup = AddSubgroup.closure (Set.range fO) :=
    toAddSubgroup_eq_closure eO fO hfO
  have hL' : L'.toAddSubgroup = AddSubgroup.closure (Set.range g) := by
    rw [Submodule.map_toAddSubgroup, toAddSubgroup_eq_closure e f hf, AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hidx := AddSubgroup.relIndex_eq_abs_det _ _ hle fO g hO hL'
  have hgram := det_gram_change g fO
  rw [← Module.Basis.det_apply] at hgram
  have hTg : (Matrix.of fun i j => trd (g i * star (g j))) =
      nrd bi • (Matrix.of fun i j => trd (f i * star (f j))) := by
    ext i j
    simp only [hg, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact trd_conj_aux bi (f i) (f j)
  rw [hTg, Matrix.det_smul, Fintype.card_fin] at hgram
  have hnn : nrd bi * nrd (β : QuatAlg ℚ a b) = 1 := by
    rw [← nrd_mul', show bi * (β : QuatAlg ℚ a b) = 1 from Units.inv_mul β]
    simp [nrd]
  -- in ℚ: d(O) nrd(β)⁴ = idx² dT
  set dT : ℚ := (Matrix.of fun i j => trd (f i * star (f j))).det
  set I : ℚ := ((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex L'.toAddSubgroup : ℚ)
  set n : ℚ := nrd (β : QuatAlg ℚ a b)
  have hkey : discriminant O * n ^ 4 = I ^ 2 * dT := by
    rw [hd, hgram, hidx, sq_abs]
    have : nrd bi ^ 4 * n ^ 4 = 1 := by rw [← mul_pow, hnn, one_pow]
    linear_combination ((g.det fO) ^ 2 * dT) * this
  have hD : 0 < discriminant O := (discriminant_basic O).2.2 ha hb
  have hn : 0 < n := by
    have := (nrd_definite ha hb).1 (β : QuatAlg ℚ a b)
    have hne : n ≠ 0 := fun h0 => hβ0 (by rw [← hβv]; exact (this.2.mp h0))
    exact lt_of_le_of_ne (le_trans (by positivity) this.1) (Ne.symm hne)
  have hI0 : 0 ≤ I := by positivity
  have hdT : 0 < dT := by
    have hIne : I ≠ 0 := by
      rw [hidx]; exact abs_ne_zero.mpr (g.isUnit_det fO).ne_zero
    have h1 : 0 < discriminant O * n ^ 4 := by positivity
    rw [hkey] at h1
    exact pos_of_mul_pos_right h1 (by positivity)
  -- real inequality
  have hkeyR : (discriminant O : ℝ) * (n : ℝ) ^ 4 = (I : ℝ) ^ 2 * (dT : ℝ) := by exact_mod_cast hkey
  have hDR : (0 : ℝ) < discriminant O := by exact_mod_cast hD
  have hdTR : (0 : ℝ) < dT := by exact_mod_cast hdT
  have hIR : (0 : ℝ) ≤ I := by exact_mod_cast hI0
  have hsq : (Real.pi ^ 2 * (n : ℝ) ^ 2) ^ 2 ≤ 64 * (dT : ℝ) := by
    have h0 : 0 ≤ Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
    have := pow_le_pow_left₀ h0 hineq 2
    rw [mul_pow (8 : ℝ), Real.sq_sqrt hdTR.le] at this
    linarith
  have hIcast : (((Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex L'.toAddSubgroup : ℕ) : ℝ) =
      (I : ℝ) := by simp [I]
  rw [hIcast]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow (8 : ℝ), Real.sq_sqrt hDR.le]
  have h3 : (Real.pi ^ 2 * (I : ℝ)) ^ 2 * (dT : ℝ) = (discriminant O : ℝ) * (Real.pi ^ 2 * (n : ℝ) ^ 2) ^ 2 := by
    linear_combination (Real.pi ^ 4) * hkeyR.symm
  have h4 : (Real.pi ^ 2 * (I : ℝ)) ^ 2 * (dT : ℝ) ≤ 64 * (discriminant O : ℝ) * (dT : ℝ) := by
    rw [h3]; nlinarith
  have h5 := le_of_mul_le_mul_right h4 hdTR
  linarith


/-- Proof helper: every `x ∈ B` has a positive multiple `N x ∈ O`. -/
private theorem exists_nsmul_mem_order {a b : ℤ} (O : QOrder a b) (x : QuatAlg ℚ a b) :
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

/-- Proof helper: a finitely generated `J ⊆ B` has a positive multiple `N J ⊆ O`. -/
private theorem exists_nsmul_le_order {a b : ℤ} (O : QOrder a b) (J : Submodule ℤ (QuatAlg ℚ a b)) (hJ : J.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ j ∈ J, (N : ℤ) • j ∈ Subalgebra.toSubmodule O.toSubalgebra := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose N hN hNx using exists_nsmul_mem_order O
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

/-- Proof helper: the finite set of representatives `Σ (c_g/N) g` (`0 ≤ c_g < N`, `g` in a generating set of `O`)
of `N⁻¹O / O`. -/
private theorem exists_finite_reps {a b : ℤ} (O : QOrder a b) (N : ℕ) (hN : 0 < N) :
    ∃ R : Set (QuatAlg ℚ a b), R.Finite ∧ ∀ x : QuatAlg ℚ a b,
      (N : ℤ) • x ∈ Subalgebra.toSubmodule O.toSubalgebra →
        ∃ r ∈ R, x - r ∈ Subalgebra.toSubmodule O.toSubalgebra := by
  classical
  obtain ⟨s, hs⟩ := O.fg
  refine ⟨Set.range (fun c : (s → Fin N) => ∑ g : s, (((c g : ℕ) : ℚ) / N) • (g : QuatAlg ℚ a b)),
    Set.finite_range _, fun x hx => ?_⟩
  rw [← hs, Submodule.mem_span_finset'] at hx
  obtain ⟨f, hf⟩ := hx
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨_, ⟨fun g => ⟨(f g % N).toNat, ?_⟩, rfl⟩, ?_⟩
  · have h0 := Int.emod_nonneg (f g) hN'
    have h1 := Int.emod_lt_of_pos (f g) (show (0 : ℤ) < N by exact_mod_cast hN)
    omega
  · have hx' : x = ∑ g : s, ((f g : ℚ) / N) • (g : QuatAlg ℚ a b) := by
      have : x = (N : ℚ)⁻¹ • ((N : ℤ) • x) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; rw [inv_mul_cancel₀ hNq, one_smul]
      rw [this, ← hf, Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, div_eq_inv_mul]
    have hdiff : x - ∑ g : s, ((((f g % N).toNat : ℕ) : ℚ) / N) • (g : QuatAlg ℚ a b) =
        ∑ g : s, (f g / (N : ℤ)) • (g : QuatAlg ℚ a b) := by
      rw [hx', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← sub_smul, ← Int.cast_smul_eq_zsmul ℚ]
      congr 1
      have h0 := Int.emod_nonneg (f g) hN'
      have hnat : (((f g % N).toNat : ℕ) : ℚ) = ((f g % N : ℤ) : ℚ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      rw [hnat, ← sub_div, div_eq_iff hNq]
      have := Int.emod_add_mul_ediv (f g) N
      have hq : ((f g : ℤ) : ℚ) = ((f g % N : ℤ) : ℚ) + (N : ℚ) * ((f g / N : ℤ) : ℚ) := by
        exact_mod_cast this.symm
      rw [hq]; ring
    rw [hdiff]
    refine Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_
    rw [← hs]
    exact Submodule.subset_span g.2

/-- Proof helper: if `O ⊆ J` and `N J ⊆ O` (`N > 0`), then `[J : O]` is finite, and `J = O + span (J ∩ R)` for the
finite set `R` of `exists_finite_reps`. -/
private theorem superlattice_reps {a b : ℤ} (O : QOrder a b) (N : ℕ) (R : Set (QuatAlg ℚ a b))
    (hR : ∀ x : QuatAlg ℚ a b, (N : ℤ) • x ∈ Subalgebra.toSubmodule O.toSubalgebra →
      ∃ r ∈ R, x - r ∈ Subalgebra.toSubmodule O.toSubalgebra)
    (J : Submodule ℤ (QuatAlg ℚ a b)) (hOJ : Subalgebra.toSubmodule O.toSubalgebra ≤ J)
    (hJ : ∀ j ∈ J, (N : ℤ) • j ∈ Subalgebra.toSubmodule O.toSubalgebra) (hRf : R.Finite) :
    (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup ≠ 0 ∧
      J = Subalgebra.toSubmodule O.toSubalgebra ⊔ Submodule.span ℤ ((J : Set (QuatAlg ℚ a b)) ∩ R) := by
  classical
  refine ⟨?_, ?_⟩
  · have : Finite ((J : Set (QuatAlg ℚ a b)) ∩ R : Set _) := (hRf.subset Set.inter_subset_right).to_subtype
    have hfin : Finite (J.toAddSubgroup ⧸
        (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.addSubgroupOf J.toAddSubgroup) := by
      refine Finite.of_surjective (fun r : ((J : Set (QuatAlg ℚ a b)) ∩ R : Set _) =>
        (QuotientAddGroup.mk (⟨r.1, r.2.1⟩ : J.toAddSubgroup) : _ ⧸ _)) ?_
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H j =>
        obtain ⟨r, hr, hjr⟩ := hR j (hJ j j.2)
        have hrJ : r ∈ J := by
          have : r = (j : QuatAlg ℚ a b) - (j - r) := by abel
          rw [this]; exact J.sub_mem j.2 (hOJ hjr)
        refine ⟨⟨r, hrJ, hr⟩, ?_⟩
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [neg_add_eq_sub] using hjr
    exact AddSubgroup.index_ne_zero_of_finite
  · refine le_antisymm (fun j hj => ?_) (sup_le hOJ (Submodule.span_le.mpr Set.inter_subset_left))
    obtain ⟨r, hr, hjr⟩ := hR j (hJ j hj)
    have hrJ : r ∈ J := by
      have : r = j - (j - r) := by abel
      rw [this]; exact J.sub_mem hj (hOJ hjr)
    have : j = (j - r) + r := by abel
    rw [this]
    exact Submodule.add_mem_sup hjr (Submodule.subset_span ⟨hrJ, hr⟩)

/-- For an order `O` and `K ∈ ℕ` there are only finitely many lattices `J` with `O ⊆ J` and `[J : O] ≤ K`. -/
@[tf_id "III.qcls.lem:bounded-superlattices-finite"]
theorem bounded_superlattices_finite {a b : ℤ} (O : QOrder a b) (K : ℕ) :
    {J : Submodule ℤ (QuatAlg ℚ a b) | J.FG ∧ Submodule.span ℚ (J : Set (QuatAlg ℚ a b)) = ⊤ ∧
      Subalgebra.toSubmodule O.toSubalgebra ≤ J ∧
      (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup ≤ K}.Finite := by
  classical
  obtain ⟨R, hRf, hR⟩ := exists_finite_reps O K.factorial K.factorial_pos
  refine ((hRf.finite_subsets).image fun T => Subalgebra.toSubmodule O.toSubalgebra ⊔ Submodule.span ℤ T).subset ?_
  rintro J ⟨hFG, -, hOJ, hK⟩
  obtain ⟨N, hN, hNJ⟩ := exists_nsmul_le_order O J hFG
  obtain ⟨R', hR'f, hR'⟩ := exists_finite_reps O N hN
  have hne := (superlattice_reps O N R' hR' J hOJ hNJ hR'f).1
  have hJK : ∀ j ∈ J, (K.factorial : ℤ) • j ∈ Subalgebra.toSubmodule O.toSubalgebra := by
    intro j hj
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hK
    have h1 := AddSubgroup.nsmul_relIndex_mem (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup
      (K := J.toAddSubgroup) (g := j) hj
    rw [natCast_zsmul, hm, mul_comm, mul_smul]
    exact Submodule.smul_of_tower_mem _ m (show _ ∈ Subalgebra.toSubmodule O.toSubalgebra from h1)
  exact ⟨_, Set.inter_subset_right, (superlattice_reps O K.factorial R hR J hOJ hJK hRf).2.symm⟩

/-- **Finiteness of the class set** (exit). For `a, b < 0` and an order `O`, `X(O)` is finite. -/
@[tf_id "III.qcls.thm:class-set-finite"]
theorem classSet_finite {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) : Finite (classSet O) := by
  classical
  set H : Subgroup (BHat a b)ˣ := (Units.map (finEmbed a b).toMonoidHom).range
  set K : ℕ := ⌊8 * Real.sqrt (discriminant O : ℝ) / Real.pi ^ 2⌋₊
  set S := {J : Submodule ℤ (QuatAlg ℚ a b) | J.FG ∧ Submodule.span ℚ (J : Set (QuatAlg ℚ a b)) = ⊤ ∧
      Subalgebra.toSubmodule O.toSubalgebra ≤ J ∧
      (Subalgebra.toSubmodule O.toSubalgebra).toAddSubgroup.relIndex J.toAddSubgroup ≤ K}
  have hS : S.Finite := bounded_superlattices_finite O K
  have hRI := classSet_right_ideals O
  -- every class has a representative `x'` with `L_{x'} ∈ S`
  have key : ∀ c : classSet O, ∃ x' : (BHat a b)ˣ,
      (DoubleCoset.mk H (orderCompletionUnits O) x' : classSet O) = c ∧ finiteIdeleLattice O x' ∈ S := by
    intro c
    set x : (BHat a b)ˣ := Quotient.out c
    obtain ⟨hFG, hspan, -⟩ := (lattice_local_global a b).2.1 O x
    obtain ⟨β, -, hle, hbd⟩ := minkowski_bound ha hb O (finiteIdeleLattice O x) hFG hspan (hRI.1 x)
    refine ⟨Units.map (finEmbed a b).toMonoidHom β⁻¹ * x * 1, ?_, ?_⟩
    · rw [mul_one, DoubleCoset.mk_mem_mul (⟨_, β⁻¹, rfl⟩ : H)]
      exact DoubleCoset.out_eq' c
    · have hL := hRI.2.1 β⁻¹ x 1 (Subgroup.one_mem _)
      rw [hL]
      refine ⟨?_, ?_, hle, Nat.le_floor ?_⟩
      · rw [← hL]; exact ((lattice_local_global a b).2.1 O _).1
      · rw [← hL]; exact ((lattice_local_global a b).2.1 O _).2.1
      · rw [le_div_iff₀ (by positivity), mul_comm]
        exact hbd
  choose f hf1 hf2 using key
  have hinj : Function.Injective (fun c : classSet O => (⟨finiteIdeleLattice O (f c), hf2 c⟩ : S)) := by
    intro c c' h
    have h' : finiteIdeleLattice O (f c) = finiteIdeleLattice O (f c') := congrArg Subtype.val h
    have h1 := hRI.2.2.1 (f c) (f c') 1 (by
      rw [h']
      ext z
      simp)
    rw [← hf1 c, ← hf1 c']
    exact h1
  have : Finite S := hS.to_subtype
  exact Finite.of_injective _ hinj

/-- For `a, b < 0`, an order `O` and a subgroup `U ≤ Ô^×` open in `B̂^×`, `B^× \ B̂^× / U` is finite. -/
@[tf_id "III.qcls.cor:class-set-finite-open-subgroup"]
theorem classSet_finite_of_open {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (U : Subgroup (BHat a b)ˣ)
    (hU : U ≤ orderCompletionUnits O) (hUo : IsOpen (U : Set (BHat a b)ˣ)) :
    Finite (DoubleCoset.Quotient ((Units.map (finEmbed a b).toMonoidHom).range : Set (BHat a b)ˣ)
      (U : Set (BHat a b)ˣ)) := by
  classical
  set H : Subgroup (BHat a b)ˣ := (Units.map (finEmbed a b).toMonoidHom).range
  set V : Subgroup (BHat a b)ˣ := orderCompletionUnits O
  have : IsTopologicalGroup (BHat a b)ˣ := (bHat_topology a b).2.2.2
  have hVc : CompactSpace V :=
    isCompact_iff_compactSpace.mp ((latticeCompletion_compact_open a b).2 O).1
  have hUo : IsOpen ((U.subgroupOf V : Subgroup V) : Set V) := Subgroup.subgroupOf_isOpen V U hUo
  have : Finite (V ⧸ U.subgroupOf V) := Subgroup.quotient_finite_of_isOpen _ hUo
  have : Finite (classSet O) := classSet_finite ha hb O
  let F : classSet O × (V ⧸ U.subgroupOf V) →
      DoubleCoset.Quotient (H : Set (BHat a b)ˣ) (U : Set (BHat a b)ˣ) :=
    fun cq => DoubleCoset.mk H U (Quotient.out cq.1 * ((Quotient.out cq.2 : V) : (BHat a b)ˣ))
  refine Finite.of_surjective F ?_
  intro d
  induction d using Quotient.inductionOn' with
  | h g =>
    set c : classSet O := DoubleCoset.mk H V g
    obtain ⟨h', hh', k', hk', hg⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' c)
    set q : V ⧸ U.subgroupOf V := QuotientGroup.mk (⟨k', hk'⟩ : V)
    have hq : (Quotient.out q)⁻¹ * (⟨k', hk'⟩ : V) ∈ U.subgroupOf V :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
    refine ⟨(c, q), ?_⟩
    show DoubleCoset.mk H U _ = DoubleCoset.mk H U g
    rw [DoubleCoset.eq]
    refine ⟨h', hh', ((Quotient.out q : V) : (BHat a b)ˣ)⁻¹ * k', ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hq
      simpa using hq
    · rw [hg]
      group

/-! ## §2 Stabilizers -/

/-- The stabilizer `Γ_x(U) = {γ ∈ B^× : ι(γ) ∈ x U x⁻¹}` of `x ∈ B̂^×` for a subgroup `U ≤ B̂^×`; for an order `O`,
`Γ_x = Γ_x(Ô^×)` (`classStabilizer (orderCompletionUnits O) x`). -/
@[tf_id "III.qcls.def:stabilizer"]
noncomputable def classStabilizer {a b : ℤ} (U : Subgroup (BHat a b)ˣ) (x : (BHat a b)ˣ) :
    Subgroup (QuatAlg ℚ a b)ˣ :=
  (U.map (MulAut.conj x).toMonoidHom).comap (Units.map (finEmbed a b).toMonoidHom)

/-- (a) `O_x = ι⁻¹(xÔx⁻¹)` is an order and `Γ_x = O_x^×`; (b) `Γ_{ι(γ)xu} = γ Γ_x γ⁻¹` for `γ ∈ B^×`, `u ∈ Ô^×`;
(c) for `a, b < 0`, `Γ_x` is finite with `|Γ_x| ∈ {2, 4, 6, 8, 12, 24}`. -/
@[tf_id "III.qcls.lem:stabilizer-units"]
theorem stabilizer_units {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) :
    (∃ Ox : QOrder a b,
      (Ox.toSubalgebra : Set (QuatAlg ℚ a b)) = finEmbed a b ⁻¹'
        ((fun y : BHat a b ↦ (x : BHat a b) * y * ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
          (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))) ∧
      classStabilizer (orderCompletionUnits O) x = unitGroup Ox) ∧
    (∀ (γ : (QuatAlg ℚ a b)ˣ) (u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      classStabilizer (orderCompletionUnits O) (Units.map (finEmbed a b).toMonoidHom γ * x * u) =
        (classStabilizer (orderCompletionUnits O) x).map (MulAut.conj γ).toMonoidHom) ∧
    (a < 0 → b < 0 → Finite (classStabilizer (orderCompletionUnits O) x) ∧
      Nat.card (classStabilizer (orderCompletionUnits O) x) ∈ ({2, 4, 6, 8, 12, 24} : Finset ℕ)) := by
  set V := orderCompletionUnits O
  have hA : ∃ Ox : QOrder a b,
      (Ox.toSubalgebra : Set (QuatAlg ℚ a b)) = finEmbed a b ⁻¹'
        ((fun y : BHat a b ↦ (x : BHat a b) * y * ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
          (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b))) ∧
      classStabilizer V x = unitGroup Ox := by
    classical
    set Oh := latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) with hOh
    have one : (1 : BHat a b) ∈ Oh := one_mem_orderCompletion O
    obtain ⟨N1, hN1, h1⟩ := exists_den_mul_latticeCompletion _ O.fg O.span_eq_top (x : BHat a b)
    obtain ⟨N2, hN2, h2⟩ :=
      exists_den_mul_latticeCompletion _ O.fg O.span_eq_top ((x⁻¹ : (BHat a b)ˣ) : BHat a b)
    have hconj : ∀ (g g' : BHat a b) (M M' : ℕ), (∀ y ∈ Oh, (M : FinAdele) • (g * y) ∈ Oh) →
        (∀ y ∈ Oh, (M' : FinAdele) • (g' * y) ∈ Oh) →
        ∀ w ∈ Oh, ((M * M' : ℕ) : FinAdele) • (g * w * g') ∈ Oh := by
      intro g g' M M' hg hg' w hw
      have := mul_mem_orderCompletion O (hg w hw) (hg' 1 one)
      rw [mul_one, smul_mul_assoc, mul_smul_comm, smul_smul] at this
      rwa [Nat.cast_mul]
    have hcast : ∀ (n : ℕ) (z : QuatAlg ℚ a b), finEmbed a b ((n : ℤ) • z) = (n : FinAdele) • finEmbed a b z := by
      intro n z
      rw [zsmul_eq_mul, map_mul, Int.cast_natCast, map_natCast, Algebra.smul_def, map_natCast]
    have hpre := (lattice_local_global a b).1 _ O.fg O.span_eq_top
    have hmemO : ∀ z : QuatAlg ℚ a b, finEmbed a b z ∈ Oh → z ∈ O.toSubalgebra := by
      intro z hz
      have : z ∈ finEmbed a b ⁻¹' (Oh : Set (BHat a b)) := hz
      rw [hpre] at this
      exact this
    set xi : BHat a b := ((x⁻¹ : (BHat a b)ˣ) : BHat a b)
    have hxx : (x : BHat a b) * xi = 1 := x.mul_inv
    have hxx' : xi * (x : BHat a b) = 1 := x.inv_mul
    let S : Subalgebra ℤ (QuatAlg ℚ a b) :=
      { carrier := finEmbed a b ⁻¹' ((fun y : BHat a b ↦ (x : BHat a b) * y * xi) '' (Oh : Set (BHat a b)))
        mul_mem' := by
          rintro z1 z2 ⟨w1, hw1, e1⟩ ⟨w2, hw2, e2⟩
          refine ⟨w1 * w2, mul_mem_orderCompletion O hw1 hw2, ?_⟩
          simp only [Set.mem_preimage] at e1 e2 ⊢
          rw [map_mul, ← e1, ← e2]
          simp only [mul_assoc]
          rw [← mul_assoc xi, hxx', one_mul]
        add_mem' := by
          rintro z1 z2 ⟨w1, hw1, e1⟩ ⟨w2, hw2, e2⟩
          refine ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
          simp only [Set.mem_preimage] at e1 e2 ⊢
          rw [map_add, ← e1, ← e2, mul_add, add_mul]
        algebraMap_mem' := by
          intro n
          refine ⟨(n : BHat a b), ?_, ?_⟩
          · have : (n : BHat a b) = n • (1 : BHat a b) := by rw [zsmul_eq_mul, mul_one]
            rw [this]
            exact Oh.toAddSubgroup.zsmul_mem one n
          · simp only [Set.mem_preimage]
            rw [algebraMap_int_eq, eq_intCast, map_intCast, ← Int.cast_comm, mul_assoc, hxx, mul_one] }
    have hSO : ∀ z ∈ S, ((N1 * N2 : ℕ) : ℤ) • z ∈ O.toSubalgebra := by
      rintro z ⟨w, hw, e⟩
      apply hmemO
      rw [hcast]
      simp only at e
      rw [← e]
      exact hconj _ _ N1 N2 h1 h2 w hw
    have hOS : ∀ z ∈ O.toSubalgebra, ((N2 * N1 : ℕ) : ℤ) • z ∈ S := by
      intro z hz
      have hw := hconj _ _ N2 N1 h2 h1 (finEmbed a b z) (Submodule.subset_span ⟨z, hz, rfl⟩)
      refine ⟨_, hw, ?_⟩
      simp only [Set.mem_preimage]
      rw [hcast, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ← mul_assoc, hxx, one_mul, mul_assoc, hxx,
        mul_one]
    have hSfg : (Subalgebra.toSubmodule S).FG := by
      set K : ℕ := N1 * N2
      have hK : (K : ℚ) ≠ 0 := by positivity
      refine fg_of_le_fg (O.fg.map ((LinearMap.lsmul ℚ (QuatAlg ℚ a b) (K : ℚ)⁻¹).restrictScalars ℤ)) ?_
      intro z hz
      refine ⟨((K : ℤ)) • z, hSO z hz, ?_⟩
      simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hK, one_smul]
    have hSspan : Submodule.span ℚ (S : Set (QuatAlg ℚ a b)) = ⊤ := by
      rw [eq_top_iff, ← O.span_eq_top, Submodule.span_le]
      intro z hz
      have hK : ((N2 * N1 : ℕ) : ℚ) ≠ 0 := by positivity
      have : z = ((N2 * N1 : ℕ) : ℚ)⁻¹ • (((N2 * N1 : ℕ) : ℤ) • z) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hOS z hz))
    refine ⟨⟨S, hSfg, hSspan⟩, rfl, ?_⟩
    ext δ
    simp only [classStabilizer, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨v, hv, hδ⟩
      have hδ' := congrArg Units.val hδ
      have hδi := congrArg (fun t => ((t⁻¹ : (BHat a b)ˣ) : BHat a b)) hδ
      simp only [Units.val_mul, mul_inv_rev, inv_inv] at hδ' hδi
      refine ⟨⟨v, hv.1, ?_⟩, ⟨((v⁻¹ : (BHat a b)ˣ) : BHat a b), hv.2, ?_⟩⟩
      · exact hδ'
      · rw [← mul_assoc] at hδi
        exact hδi
    · rintro ⟨⟨w, hw, e⟩, ⟨w', hw', e'⟩⟩
      let v : (BHat a b)ˣ := ⟨w, w', ?_, ?_⟩
      · refine ⟨v, ⟨hw, hw'⟩, Units.ext ?_⟩
        show (x : BHat a b) * w * xi = finEmbed a b δ
        exact e
      · have : (x : BHat a b) * (w * w') * xi = 1 := by
          have h := congrArg₂ (· * ·) e e'
          simp only at h
          rw [← map_mul, Units.mul_inv, map_one] at h
          rw [← h]; simp only [mul_assoc]; rw [← mul_assoc xi, hxx', one_mul]
        calc w * w' = xi * ((x : BHat a b) * (w * w') * xi) * x := by
              simp only [mul_assoc, hxx', mul_one]; rw [← mul_assoc, hxx', one_mul]
          _ = 1 := by rw [this, mul_one, hxx']
      · have : (x : BHat a b) * (w' * w) * xi = 1 := by
          have h := congrArg₂ (· * ·) e' e
          simp only at h
          rw [← map_mul, Units.inv_mul, map_one] at h
          rw [← h]; simp only [mul_assoc]; rw [← mul_assoc xi, hxx', one_mul]
        calc w' * w = xi * ((x : BHat a b) * (w' * w) * xi) * x := by
              simp only [mul_assoc, hxx', mul_one]; rw [← mul_assoc, hxx', one_mul]
          _ = 1 := by rw [this, mul_one, hxx']
  have hB : ∀ (γ : (QuatAlg ℚ a b)ˣ) (u : (BHat a b)ˣ), u ∈ V →
      classStabilizer V (Units.map (finEmbed a b).toMonoidHom γ * x * u) =
        (classStabilizer V x).map (MulAut.conj γ).toMonoidHom := by
    intro γ u hu
    ext δ
    simp only [classStabilizer, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨v, hv, hδ⟩
      refine ⟨γ⁻¹ * δ * γ, ⟨u * v * u⁻¹, V.mul_mem (V.mul_mem hu hv) (V.inv_mem hu), ?_⟩, by group⟩
      rw [map_mul, map_mul, map_inv, ← hδ]
      group
    · rintro ⟨ε, ⟨v', hv', hε⟩, rfl⟩
      refine ⟨u⁻¹ * v' * u, V.mul_mem (V.mul_mem (V.inv_mem hu) hv') hu, ?_⟩
      rw [map_mul, map_mul, map_inv, ← hε]
      group
  refine ⟨hA, hB, fun ha hb => ?_⟩
  obtain ⟨Ox, -, hOx⟩ := hA
  rw [hOx]
  exact ⟨(unitGroup_eq_nrd_one_finite ha hb Ox).2, (card_unitGroup_dvd_24 ha hb Ox).2.2⟩

end GL2TF.Quat
