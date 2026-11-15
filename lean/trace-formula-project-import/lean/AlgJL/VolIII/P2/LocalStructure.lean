import AlgJL.VolIII.P2.QuatAlg
import AlgJL.VolIII.P2.Ramification
import AlgJL.VolIII.P2.Orders
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Local structure: completions of lattices and orders, local splitting (Q2 U3, items 17–20, 34)

Lean counterpart of `vol3/ch-iii-06-quatalg.tex` §3 (items 17–20 of `docs/sprints/Q2-plan.md` §1.2) and of item 34
(`III.qord.thm:level-structure-exists`, stated in `vol3/ch-iii-07-orders.tex`, Lean module here by plan §1.2).

Conventions:
* `B_p = QuatAlg ℚ_[p] a b` (item 1); `B → B_p` is `baseChange a b (algebraMap ℚ ℚ_[p])`.
* `localLattice p L` is defined for every ℤ-submodule `L ⊆ B` (the lattice hypotheses enter the theorems, inline:
  `L.FG` and `ℚ L = B`).
* `B_p` carries no topology (plan trap 3): "compact open" is stated for the image of `L_p` under Mathlib's
  `QuaternionAlgebra.equivTuple` in `Fin 4 → ℚ_[p]` (product topology).
* "`ℤ_p`-order" is written inline: a `ℤ_[p]`-subalgebra of `B_p` that is compact open (in the coordinates) and spans
  `B_p` over `ℚ_p` (snippet wording).
* `[L : L']` is `L'.toAddSubgroup.relIndex L.toAddSubgroup` (`0` if infinite, so `p ∤ [L : L']` forces finiteness).
* `ℤ_p ⊆ ℚ_p` is `PadicInt.subring p`; `M₂(ℤ_p) ⊆ M₂(ℚ_p)` is the range of the entrywise map.
Owner: L1T (Q2).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-- For a lattice `L ⊆ B` and a prime `p`: `L_p` is the `ℤ_p`-span of the image of `L` in `B_p`. -/
@[tf_id "III.qalg.def:local-order"]
noncomputable def localLattice {a b : ℤ} (p : ℕ) [Fact p.Prime] (L : Submodule ℤ (QuatAlg ℚ a b)) :
    Submodule ℤ_[p] (QuatAlg ℚ_[p] a b) :=
  Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b)))

open Pointwise in
private theorem localLattice_basic_bcd {a b : ℤ} (p : ℕ) [Fact p.Prime] (L : Submodule ℤ (QuatAlg ℚ a b)) :
    (∀ e : Module.Basis (Fin 4) ℤ L, localLattice p L =
      Submodule.span ℤ_[p] (Set.range fun i => baseChange a b (algebraMap ℚ ℚ_[p]) (e i : QuatAlg ℚ a b))) ∧
    (∀ L' : Submodule ℤ (QuatAlg ℚ a b), L'.FG → Submodule.span ℚ (L' : Set (QuatAlg ℚ a b)) = ⊤ → L' ≤ L →
      ¬ p ∣ L'.toAddSubgroup.relIndex L.toAddSubgroup → localLattice p L' = localLattice p L) ∧
    (∀ O : QOrder a b, ∃ S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b),
      Subalgebra.toSubmodule S = localLattice p (Subalgebra.toSubmodule O.toSubalgebra)) := by
  set bc := baseChange a b (algebraMap ℚ ℚ_[p]) with hbc
  let φ : QuatAlg ℚ a b →ₗ[ℤ] QuatAlg ℚ_[p] a b := bc.toAddMonoidHom.toIntLinearMap
  refine ⟨fun e => ?_, fun L' _ _ hle hp => ?_, fun O => ?_⟩
  · apply le_antisymm
    · rw [localLattice, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range fun i => (e i : QuatAlg ℚ a b)) := by
        have h1 := e.mem_span ⟨x, hx⟩
        have h2 := Submodule.mem_map_of_mem (f := L.subtype) h1
        rwa [Submodule.map_span, ← Set.range_comp] at h2
      have h3 := Submodule.mem_map_of_mem (f := φ) hx'
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars ℤ ℤ_[p] _ h3
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨e i, (e i).2, rfl⟩
  · set n := L'.toAddSubgroup.relIndex L.toAddSubgroup with hn
    have hmem : ∀ x ∈ L, n • x ∈ L' := fun x hx =>
      AddSubgroup.nsmul_relIndex_mem L'.toAddSubgroup (K := L.toAddSubgroup) hx
    have hu : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      have h1 := PadicInt.norm_le_one (n : ℤ_[p])
      have h2 : ¬ ‖((n : ℤ) : ℤ_[p])‖ < 1 := fun h => hp (by
        have := (PadicInt.norm_int_lt_one_iff_dvd _).1 h
        exact_mod_cast this)
      push_cast at h2
      linarith [not_lt.1 h2]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hle)
    · rw [localLattice, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have e1 : bc x = ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • bc (n • x) := by
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, IsUnit.val_inv_mul, one_smul]
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n • x, hmem x hx, rfl⟩)
  · have hmul : ∀ x y, x ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) →
        y ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) →
        x * y ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
      intro x y hx hy
      have h1 := Submodule.mul_mem_mul hx hy
      rw [localLattice, Submodule.span_mul_span] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨u * v, O.toSubalgebra.mul_mem hu hv, map_mul bc u v⟩
    have hone : (1 : QuatAlg ℚ_[p] a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) :=
      Submodule.subset_span ⟨1, O.toSubalgebra.one_mem, map_one bc⟩
    exact ⟨Submodule.toSubalgebra _ hone hmul, rfl⟩

private theorem ls_rat_basis {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b))
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

private theorem ls_lattice_basis {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) :
    ∃ e : Module.Basis (Fin 4) ℤ L, ∃ f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b),
      ∀ i, f i = (e i : QuatAlg ℚ a b) := by
  have : Module.IsTorsionFree ℤ (QuatAlg ℚ a b) := Module.IsTorsionFree.trans ℚ
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  let e0 := Module.Free.chooseBasis ℤ L
  obtain ⟨f0, hf0⟩ := ls_rat_basis L hspan e0
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = 4 := by
    rw [← Module.finrank_eq_card_basis f0]
    exact QuaternionAlgebra.finrank_eq_four _ _ _
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨e0.reindex eqv, f0.reindex eqv, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hf0]

private theorem baseChange_smul {a b : ℤ} (p : ℕ) [Fact p.Prime] (q : ℚ) (x : QuatAlg ℚ a b) :
    baseChange a b (algebraMap ℚ ℚ_[p]) (q • x) = (q : ℚ_[p]) • baseChange a b (algebraMap ℚ ℚ_[p]) x := by
  ext <;> simp [baseChange]

private theorem localLattice_compact_open {a b : ℤ} (p : ℕ) [Fact p.Prime] (L : Submodule ℤ (QuatAlg ℚ a b)) (hL : L.FG)
    (hLs : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤)
    (hb : ∀ e : Module.Basis (Fin 4) ℤ L, localLattice p L =
      Submodule.span ℤ_[p] (Set.range fun i => baseChange a b (algebraMap ℚ ℚ_[p]) (e i : QuatAlg ℚ a b))) :
    (IsCompact (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) ''
        (localLattice p L : Set (QuatAlg ℚ_[p] a b))) ∧
      IsOpen (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) ''
        (localLattice p L : Set (QuatAlg ℚ_[p] a b))) ∧
      Submodule.span ℚ_[p] (localLattice p L : Set (QuatAlg ℚ_[p] a b)) = ⊤) := by
  set bc := baseChange a b (algebraMap ℚ ℚ_[p]) with hbc
  obtain ⟨e, f, hf⟩ := ls_lattice_basis L hL hLs
  set v : Fin 4 → QuatAlg ℚ_[p] a b := fun i => bc (e i : QuatAlg ℚ a b) with hv
  have hLp := hb e
  -- span over ℚ_p
  have hbcmem : ∀ x : QuatAlg ℚ a b, bc x ∈ Submodule.span ℚ_[p] (Set.range v) := by
    intro x
    rw [← f.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hbc, baseChange_smul, ← hbc, hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span ℚ_[p] (Set.range v) := by
    intro z _
    have hz : z = z.re • bc 1 + z.imI • bc ⟨0, 1, 0, 0⟩ + z.imJ • bc ⟨0, 0, 1, 0⟩ +
        z.imK • bc ⟨0, 0, 0, 1⟩ := by
      ext <;> simp [hbc, baseChange]
    rw [hz]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (hbcmem _)
  have li : LinearIndependent ℚ_[p] v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
  let bv := Module.Basis.mk li hspan
  have hbv : ∀ i, bv i = v i := fun i => Module.Basis.mk_apply _ _ _
  -- the lattice as an image of the unit polydisc
  set Z : Set (Fin 4 → ℚ_[p]) := Set.pi Set.univ (fun _ => Metric.closedBall 0 1) with hZ
  have hLZ : (localLattice p L : Set (QuatAlg ℚ_[p] a b)) = bv.equivFun.symm '' Z := by
    ext z
    rw [SetLike.mem_coe, hLp, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => (c i : ℚ_[p]), fun i _ => by simpa using PadicInt.norm_le_one (c i), ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbv, ← algebraMap_smul ℚ_[p] (c i) (v i)]
      rfl
    · rintro ⟨d, hd, rfl⟩
      refine ⟨fun i => ⟨d i, by simpa using hd i (Set.mem_univ _)⟩, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbv, ← algebraMap_smul ℚ_[p] _ (v i)]
      rfl
  let Φ : (Fin 4 → ℚ_[p]) ≃L[ℚ_[p]] (Fin 4 → ℚ_[p]) :=
    (bv.equivFun.symm.trans (QuaternionAlgebra.linearEquivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]))).toContinuousLinearEquiv
  have hΦ : QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) ''
      (localLattice p L : Set (QuatAlg ℚ_[p] a b)) = Φ '' Z := by
    rw [hLZ, Set.image_image]
    rfl
  have hZc : IsCompact Z := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hZo : IsOpen Z := isOpen_set_pi Set.finite_univ fun _ _ =>
    IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [hΦ]; exact hZc.image Φ.continuous
  · rw [hΦ]; exact Φ.toHomeomorph.isOpenMap Z hZo
  · refine top_le_iff.1 (le_trans hspan (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- For a lattice `L ⊆ B` and a prime `p`: (a) `L_p` is a compact open `ℤ_p`-submodule of `B_p` spanning `B_p` over
`ℚ_p`; (b) `L_p` is the `ℤ_p`-span of (the image of) any `ℤ`-basis of `L`; (c) for a lattice `L' ⊆ L` with
`p ∤ [L : L']`, `L'_p = L_p`; (d) for an order `O`, `O_p` is a subring of `B_p` (with (a), a `ℤ_p`-order). -/
@[tf_id "III.qalg.lem:local-order-basic"]
theorem localLattice_basic {a b : ℤ} (p : ℕ) [Fact p.Prime] (L : Submodule ℤ (QuatAlg ℚ a b)) (hL : L.FG)
    (hLs : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) :
    (IsCompact (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) ''
        (localLattice p L : Set (QuatAlg ℚ_[p] a b))) ∧
      IsOpen (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) ''
        (localLattice p L : Set (QuatAlg ℚ_[p] a b))) ∧
      Submodule.span ℚ_[p] (localLattice p L : Set (QuatAlg ℚ_[p] a b)) = ⊤) ∧
    (∀ e : Module.Basis (Fin 4) ℤ L, localLattice p L =
      Submodule.span ℤ_[p] (Set.range fun i => baseChange a b (algebraMap ℚ ℚ_[p]) (e i : QuatAlg ℚ a b))) ∧
    (∀ L' : Submodule ℤ (QuatAlg ℚ a b), L'.FG → Submodule.span ℚ (L' : Set (QuatAlg ℚ a b)) = ⊤ → L' ≤ L →
      ¬ p ∣ L'.toAddSubgroup.relIndex L.toAddSubgroup → localLattice p L' = localLattice p L) ∧
    (∀ O : QOrder a b, ∃ S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b),
      Subalgebra.toSubmodule S = localLattice p (Subalgebra.toSubmodule O.toSubalgebra)) := by
  have hbcd := localLattice_basic_bcd p L
  exact ⟨localLattice_compact_open p L hL hLs hbcd.1, hbcd.1, hbcd.2.1, hbcd.2.2⟩

/-! ### Proof of item 19 (private helpers; plan: `docs/notes/Q2-titan/l19-plan.md`) -/
private theorem l19_split {a b : ℤ} {D : ℕ} (hD : RamifiedExactly a b D) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ p ∣ D) : Nonempty (QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  obtain ⟨ha, hb, -, h⟩ := hD
  have hne : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) ≠ -1 := fun h' => hpD ((h p).1 h')
  have h1 : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
    unfold hilbertSymbol at hne ⊢
    split_ifs at hne ⊢ with hc
    · rfl
    · exact absurd rfl hne
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have ha' : (a : ℚ_[p]) ≠ 0 := by exact_mod_cast ha.ne
  have hb' : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb.ne
  exact ((split_iff_isotropic h2 _ _ ha' hb').1.out 1 3).1 h1

open Module in
private theorem l19_bc_basis (a b : ℤ) (p : ℕ) [Fact p.Prime] (f : Basis (Fin 4) ℚ (QuatAlg ℚ a b)) :
    ∃ F : Basis (Fin 4) ℚ_[p] (QuatAlg ℚ_[p] a b), (∀ i, F i = baseChange a b (algebraMap ℚ ℚ_[p]) (f i)) ∧
      ∀ z i, F.repr (baseChange a b (algebraMap ℚ ℚ_[p]) z) i = algebraMap ℚ ℚ_[p] (f.repr z i) := by
  set v : Fin 4 → QuatAlg ℚ_[p] a b := fun i => baseChange a b (algebraMap ℚ ℚ_[p]) (f i) with hv
  have hdet : (QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ_[p]) 0 ((b : ℤ) : ℚ_[p])).det v =
      algebraMap ℚ ℚ_[p] ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).det f) := by
    rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      QuaternionAlgebra.coe_basisOneIJK_repr, hv]
    fin_cases i <;> rfl
  have hq : IsUnit ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).det f) :=
    (Basis.is_basis_iff_det _).mp ⟨f.linearIndependent, f.span_eq⟩
  have hS : IsUnit ((QuaternionAlgebra.basisOneIJK ((a : ℤ) : ℚ_[p]) 0 ((b : ℤ) : ℚ_[p])).det v) := by
    rw [hdet]; exact hq.map _
  have hb := (Basis.is_basis_iff_det _).mpr hS
  let F := Basis.mk hb.1 hb.2.ge
  have hF : ∀ i, F i = v i := fun i => Basis.mk_apply _ _ _
  refine ⟨F, hF, fun z i => ?_⟩
  have hz : baseChange a b (algebraMap ℚ ℚ_[p]) z = ∑ j, algebraMap ℚ ℚ_[p] (f.repr z j) • F j := by
    conv_lhs => rw [← f.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, hv]
    simp only
    ext <;> simp [baseChange]
  rw [hz, Basis.repr_sum_self]

open Module in
/-- Membership in `O_p` via coordinates in a base-changed basis. -/
private theorem l19_mem_iff {a b : ℤ} (p : ℕ) [Fact p.Prime] {L : Submodule ℤ (QuatAlg ℚ a b)}
    (e : Basis (Fin 4) ℤ L) (F : Basis (Fin 4) ℚ_[p] (QuatAlg ℚ_[p] a b))
    (hF : ∀ i, F i = baseChange a b (algebraMap ℚ ℚ_[p]) (e i)) (w : QuatAlg ℚ_[p] a b) :
    w ∈ localLattice p L ↔ ∀ i, F.repr w i ∈ (algebraMap ℤ_[p] ℚ_[p]).range := by
  set j := baseChange a b (algebraMap ℚ ℚ_[p])
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro i
      have hz' : j z = ∑ k, ((e.repr ⟨z, hz⟩ k : ℤ) : ℚ_[p]) • F k := by
        change j ((⟨z, hz⟩ : L) : QuatAlg ℚ a b) = _
        rw [val_eq_sum_repr e, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, hF, Int.cast_smul_eq_zsmul]
      rw [hz', Basis.repr_sum_self]
      exact ⟨(e.repr ⟨z, hz⟩ i : ℤ_[p]), by simp⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨r, hr⟩ := hx i
      obtain ⟨s, hs⟩ := hy i
      exact ⟨r + s, by rw [map_add, hr, hs, map_add, Finsupp.add_apply]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨s, hs⟩ := hx i
      refine ⟨r * s, ?_⟩
      rw [← algebraMap_smul ℚ_[p] r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hs]
  · intro h
    choose r hr using h
    rw [← F.sum_repr w]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hr i, algebraMap_smul, hF]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (e i).2, rfl⟩)

/-- Coordinates of an order and of its completion. -/
private theorem l19_coords {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : QOrder a b) :
    ∃ f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b), ∃ F : Module.Basis (Fin 4) ℚ_[p] (QuatAlg ℚ_[p] a b),
      (∀ y, y ∈ O.toSubalgebra ↔ ∀ i, ∃ n : ℤ, f.repr y i = n) ∧
      (∀ z i, F.repr (baseChange a b (algebraMap ℚ ℚ_[p]) z) i = algebraMap ℚ ℚ_[p] (f.repr z i)) ∧
      (∀ w, w ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
        ∀ i, F.repr w i ∈ (algebraMap ℤ_[p] ℚ_[p]).range) := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  obtain ⟨F, hF1, hF2⟩ := l19_bc_basis a b p f
  refine ⟨f, F, fun y => mem_lattice_iff_repr e f hf y, hF2, fun w => ?_⟩
  exact l19_mem_iff p e F (fun i => by rw [hF1, hf]) w

/-- (P) Every element of `B_p` lands in `O_p` after multiplication by a large power of `p`. -/
private theorem l19_pow_mem {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : QOrder a b) (z : QuatAlg ℚ_[p] a b) :
    ∀ᶠ k in Filter.atTop, ((p : ℚ_[p]) ^ k) • z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨f, F, -, -, hmem⟩ := l19_coords p O
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hev : ∀ i, ∀ᶠ k in Filter.atTop, ‖((p : ℚ_[p]) ^ k) * F.repr z i‖ ≤ 1 := by
    intro i
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hp1).eventually_ge_atTop ‖F.repr z i‖] with k hk
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [inv_mul_le_iff₀ hpk, mul_one]
    exact hk
  filter_upwards [Filter.eventually_all.2 hev] with k hk
  rw [hmem]
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact ⟨⟨_, hk i⟩, rfl⟩

private theorem l19_rat_int (p : ℕ) [Fact p.Prime] (c : ℚ) (n : ℕ) (N : ℤ) (h : (p : ℚ) ^ n * c = N)
    (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ∃ m : ℤ, c = m := by
  have hN : ‖((N : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) := by
    have : ((N : ℤ) : ℚ_[p]) = (p : ℚ_[p]) ^ n * (c : ℚ_[p]) := by
      have := congrArg (fun q : ℚ => (q : ℚ_[p])) h
      push_cast at this
      exact this.symm
    rw [this, norm_mul, Padic.norm_p_pow]
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-n : ℤ) := by positivity
    nlinarith
  obtain ⟨m, hm⟩ := (Padic.norm_int_le_pow_iff_dvd N n).1 hN
  refine ⟨m, ?_⟩
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_left_cancel₀ hp0
  rw [h, hm]
  push_cast
  ring

/-- (G) `y ∈ B` with `p^n y ∈ O` and `y ∈ O_p` lies in `O`. -/
private theorem l19_descend {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : QOrder a b) (y : QuatAlg ℚ a b) (n : ℕ)
    (hn : ((p : ℚ) ^ n) • y ∈ O.toSubalgebra)
    (hy : baseChange a b (algebraMap ℚ ℚ_[p]) y ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra)) :
    y ∈ O.toSubalgebra := by
  obtain ⟨f, F, hO, hF, hmem⟩ := l19_coords p O
  rw [hO] at hn ⊢
  rw [hmem] at hy
  intro i
  obtain ⟨N, hN⟩ := hn i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at hN
  obtain ⟨t, ht⟩ := hy i
  rw [hF] at ht
  refine l19_rat_int p _ n N hN ?_
  rw [← eq_ratCast (algebraMap ℚ ℚ_[p]), ← ht]
  exact PadicInt.norm_le_one t

/-- (H) Approximation of `O_p` by `O` modulo `p^k O_p`. -/
private theorem l19_approx {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : QOrder a b) (k : ℕ) (z : QuatAlg ℚ_[p] a b)
    (hz : z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra)) :
    ∃ x ∈ O.toSubalgebra, ∃ w ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra),
      z = baseChange a b (algebraMap ℚ ℚ_[p]) x + ((p : ℤ_[p]) ^ k) • w := by
  set bc := baseChange a b (algebraMap ℚ ℚ_[p]) with hbc
  have hbcmem : ∀ x ∈ O.toSubalgebra, bc x ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) :=
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, 0, Submodule.zero_mem _, by simp [hbc]⟩
  | zero => exact ⟨0, Subalgebra.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, hx₁, w₁, hw₁, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, w₂, hw₂, rfl⟩ := h₂
    refine ⟨x₁ + x₂, Subalgebra.add_mem _ hx₁ hx₂, w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
    rw [map_add, smul_add]; abel
  | smul r z _ h =>
    obtain ⟨x, hx, w, hw, rfl⟩ := h
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k r)
    set n := r.appr k
    refine ⟨n • x, Subalgebra.nsmul_mem _ hx _, s • bc x + r • w,
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hbcmem x hx)) (Submodule.smul_mem _ _ hw), ?_⟩
    have hr : r = (n : ℤ_[p]) + s * (p : ℤ_[p]) ^ k := by rw [hs]; ring
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    nth_rewrite 1 [hr]
    rw [add_smul, mul_comm r, mul_comm s]
    abel

private theorem l19_pow_smul_mem {a b : ℤ} (p : ℕ) (O : QOrder a b) (m : ℕ) {u : QuatAlg ℚ a b}
    (hu : u ∈ O.toSubalgebra) : ((p : ℚ) ^ m) • u ∈ O.toSubalgebra := by
  have : ((p : ℚ) ^ m) • u = ((p : ℤ) ^ m) • u := by
    rw [← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
  rw [this]
  exact Subalgebra.zsmul_mem _ hu _

/-- Step 3: global maximality of `O` gives local maximality of `O_p`, in the form: a subring `S ⊇ O_p` of `B_p`
with `p^k S ⊆ O_p` equals `O_p`. -/
private theorem l19_local_max {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : MaxOrder a b) (S : Subring (QuatAlg ℚ_[p] a b))
    (hOS : ∀ z ∈ localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra), z ∈ S) (k : ℕ)
    (hk : ∀ z ∈ S, ((p : ℚ_[p]) ^ k) • z ∈ localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra)) :
    ∀ z ∈ S, z ∈ localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) := by
  set bc := baseChange a b (algebraMap ℚ ℚ_[p]) with hbc
  set Op := localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) with hOp
  have hbcmem : ∀ x ∈ O.1.toSubalgebra, bc x ∈ Op := fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  let A : Subalgebra ℤ (QuatAlg ℚ a b) :=
    { carrier := {x | bc x ∈ S ∧ ∃ n : ℕ, ((p : ℚ) ^ n) • x ∈ O.1.toSubalgebra}
      mul_mem' := by
        rintro x y ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
        refine ⟨by rw [map_mul]; exact S.mul_mem hx hy, n + m, ?_⟩
        rw [pow_add, ← smul_mul_smul_comm]
        exact Subalgebra.mul_mem _ hn hm
      add_mem' := by
        rintro x y ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
        refine ⟨by rw [map_add]; exact S.add_mem hx hy, n + m, ?_⟩
        rw [smul_add]
        have e1 : ((p : ℚ) ^ (n + m)) • x = ((p : ℚ) ^ m) • (((p : ℚ) ^ n) • x) := by
          rw [smul_smul, ← pow_add, add_comm]
        have e2 : ((p : ℚ) ^ (n + m)) • y = ((p : ℚ) ^ n) • (((p : ℚ) ^ m) • y) := by
          rw [smul_smul, ← pow_add]
        rw [e1, e2]
        exact Subalgebra.add_mem _ (l19_pow_smul_mem p O.1 m hn) (l19_pow_smul_mem p O.1 n hm)
      algebraMap_mem' := by
        intro r
        refine ⟨?_, 0, ?_⟩
        · rw [algebraMap_int_eq, eq_intCast, map_intCast]; exact intCast_mem S r
        · rw [pow_zero, one_smul]; exact Subalgebra.algebraMap_mem _ r }
  have hle : O.1.toSubalgebra ≤ A := fun x hx => ⟨hOS _ (hbcmem x hx), 0, by rw [pow_zero, one_smul]; exact hx⟩
  have hdesc : ∀ x ∈ A, ((p : ℚ) ^ k) • x ∈ O.1.toSubalgebra := by
    rintro x ⟨hx, n, hn⟩
    refine l19_descend p O.1 _ n ?_ ?_
    · rw [smul_comm]; exact l19_pow_smul_mem p O.1 k hn
    · rw [baseChange_smul]; push_cast; exact hk _ hx
  have hp0 : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let φ : QuatAlg ℚ a b →ₗ[ℤ] QuatAlg ℚ a b :=
    (((p : ℚ) ^ k)⁻¹ • (LinearMap.id : QuatAlg ℚ a b →ₗ[ℚ] QuatAlg ℚ a b)).restrictScalars ℤ
  have hfg : (Subalgebra.toSubmodule A).FG := by
    refine fg_of_le_fg (O.1.fg.map φ) fun x hx => ?_
    refine ⟨((p : ℚ) ^ k) • x, hdesc x hx, ?_⟩
    change ((p : ℚ) ^ k)⁻¹ • (((p : ℚ) ^ k) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have hspan : Submodule.span ℚ (A : Set (QuatAlg ℚ a b)) = ⊤ :=
    top_le_iff.1 (O.1.span_eq_top ▸ Submodule.span_mono hle)
  let O' : QOrder a b := ⟨A, hfg, hspan⟩
  have hAO : A = O.1.toSubalgebra := O.2 O' hle
  intro z hz
  obtain ⟨x, hx, w, hw, hxw⟩ := l19_approx p O.1 k _ (hk z hz)
  have hpK : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hw' : ((p : ℤ_[p]) ^ k) • w = ((p : ℚ_[p]) ^ k) • w := by
    rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ k) w]; simp
  rw [hw'] at hxw
  set x' := ((p : ℚ) ^ k)⁻¹ • x with hx'
  have hbx : bc x' = z - w := by
    rw [hx', hbc, baseChange_smul, ← hbc]
    have : bc x = ((p : ℚ_[p]) ^ k) • z - ((p : ℚ_[p]) ^ k) • w := by rw [hxw]; abel
    rw [this, ← smul_sub, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hpK, one_smul]
  have hx'A : x' ∈ A := by
    refine ⟨?_, k, ?_⟩
    · rw [hbx]; exact S.sub_mem hz (hOS w hw)
    · rw [hx', smul_smul, mul_inv_cancel₀ hp0, one_smul]; exact hx
  rw [hAO] at hx'A
  have := Submodule.add_mem _ (hbcmem _ hx'A) hw
  rwa [hbx, sub_add_cancel] at this


open Module in
private theorem l19_frac_basis {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] (L : Submodule R V)
    (hspan : Submodule.span K (L : Set V) = ⊤) {ι : Type*} (e : Basis ι R L) :
    ∃ f : Basis ι K V, ∀ i, f i = (e i : V) := by
  have li : LinearIndependent R (fun i => (e i : V)) :=
    e.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have li' : LinearIndependent K (fun i => (e i : V)) := (LinearIndependent.iff_fractionRing R K).mp li
  have hsp : ⊤ ≤ Submodule.span K (Set.range (fun i => (e i : V))) := by
    rw [← hspan]
    refine Submodule.span_le.mpr fun x hx => ?_
    have h1 : (⟨x, hx⟩ : L) ∈ Submodule.span R (Set.range e) := e.mem_span _
    have h2 := Submodule.mem_map_of_mem (f := L.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars R K _ h2
  exact ⟨Basis.mk li' hsp, fun i => Basis.mk_apply _ _ _⟩

open Module in
private theorem l19_mem_iff_repr {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] {L : Submodule R V} {ι : Type*} [Fintype ι]
    (e : Basis ι R L) (f : Basis ι K V) (hf : ∀ i, f i = (e i : V)) (z : V) :
    z ∈ L ↔ ∀ i, f.repr z i ∈ (algebraMap R K).range := by
  constructor
  · intro hz i
    refine ⟨e.repr ⟨z, hz⟩ i, ?_⟩
    have h2 : z = ∑ k, e.repr ⟨z, hz⟩ k • (e k : V) := by
      have := congrArg L.subtype (e.sum_repr ⟨z, hz⟩)
      rw [map_sum] at this
      simp only [map_smul, Submodule.subtype_apply] at this
      exact this.symm
    have h3 : z = ∑ k, algebraMap R K (e.repr ⟨z, hz⟩ k) • f k := by
      conv_lhs => rw [h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hf, algebraMap_smul]
    conv_rhs => rw [h3]
    rw [Basis.repr_sum_self]
  · intro h
    choose r hr using h
    rw [← f.sum_repr z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hr i, algebraMap_smul, hf]
    exact Submodule.smul_mem _ _ (e i).2

open Module Matrix in
/-- Step 4: a finitely generated `ℤ_p`-subring `Λ` of a `ℚ_p`-algebra `A ≅ M₂(ℚ_p)` is conjugated into `M₂(ℤ_p)`. -/
private theorem l19_conj (p : ℕ) [Fact p.Prime] {A : Type*} [Ring A] [Algebra ℚ_[p] A] [Module ℤ_[p] A]
    [IsScalarTower ℤ_[p] ℚ_[p] A] (Λ : Submodule ℤ_[p] A) (hfg : Λ.FG) (h1 : (1 : A) ∈ Λ)
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) (ι₀ : A ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    ∃ ι : A ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p], ∀ z ∈ Λ, ∀ i j, ι z i j ∈ (algebraMap ℤ_[p] ℚ_[p]).range := by
  have hsm : ∀ (r : ℤ_[p]) (x : A), ι₀ (r • x) = (algebraMap ℤ_[p] ℚ_[p] r) • ι₀ x := by
    intro r x
    rw [← algebraMap_smul ℚ_[p] r x, map_smul]
  let fL : (Λ × Λ) →ₗ[ℤ_[p]] (Fin 2 → ℚ_[p]) :=
    { toFun := fun xy i => ι₀ xy.1 i 0 + ι₀ xy.2 i 1
      map_add' := by
        intro x y; funext i
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro r x; funext i
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, hsm, Matrix.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply, Algebra.smul_def]
        ring }
  set L := LinearMap.range fL with hL
  have hstab : ∀ z ∈ Λ, ∀ v ∈ L, ι₀ z *ᵥ v ∈ L := by
    rintro z hz _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨(⟨z * x, hmul z hz x x.2⟩, ⟨z * y, hmul z hz y y.2⟩), ?_⟩
    funext i
    simp only [fL, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring
  have hspan : Submodule.span ℚ_[p] (L : Set (Fin 2 → ℚ_[p])) = ⊤ := by
    have m0 : fL (⟨1, h1⟩, 0) ∈ L := ⟨_, rfl⟩
    have m1 : fL (0, ⟨1, h1⟩) ∈ L := ⟨_, rfl⟩
    refine top_le_iff.1 fun v _ => ?_
    have hv : v = v 0 • fL (⟨1, h1⟩, 0) + v 1 • fL (0, ⟨1, h1⟩) := by
      funext i
      fin_cases i <;> simp [fL]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span m0))
      (Submodule.smul_mem _ _ (Submodule.subset_span m1))
  have : Module.Finite ℤ_[p] Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.IsTorsionFree ℤ_[p] (Fin 2 → ℚ_[p]) :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[p] ℚ_[p] (Fin 2 → ℚ_[p])
  let e0 := Module.Free.chooseBasis ℤ_[p] L
  obtain ⟨f0, hf0⟩ := l19_frac_basis L hspan e0
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ_[p] L) = 2 := by
    rw [← Module.finrank_eq_card_basis f0, Module.finrank_fin_fun]
  let eqv := Fintype.equivFinOfCardEq hcard
  set wL := e0.reindex eqv
  set w := f0.reindex eqv
  have hw : ∀ i, w i = (wL i : Fin 2 → ℚ_[p]) := fun i => by
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hf0]
  refine ⟨ι₀.trans (Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv w)), fun z hz i j => ?_⟩
  simp only [AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply, Matrix.toLinAlgEquiv'_apply]
  exact (l19_mem_iff_repr wL w hw _).1 (hstab z hz _ (by rw [hw]; exact (wL j).2)) i

/-- `O` maximal, `B` ramified exactly at the primes dividing `D`, `p ∤ D`: there is `ι_p : B_p ≃ₐ[ℚ_p] M₂(ℚ_p)` with
`ι_p(O_p) = M₂(ℤ_p)`. -/
@[tf_id "III.qalg.thm:maximal-order-local-split"]
theorem maximalOrder_local_split {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hD : RamifiedExactly a b D) (p : ℕ)
    [Fact p.Prime] (hpD : ¬ p ∣ D) :
    ∃ ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p],
      ι '' (localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) =
        Set.range fun m : Matrix (Fin 2) (Fin 2) ℤ_[p] => m.map (algebraMap ℤ_[p] ℚ_[p]) := by
  obtain ⟨ι₀⟩ := l19_split hD p hpD
  set Op := localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) with hOp
  obtain ⟨-, hb, -, hd⟩ := localLattice_basic p _ O.1.fg O.1.span_eq_top
  obtain ⟨Sd, hSd⟩ := hd O.1
  obtain ⟨e, -, -⟩ := exists_lattice_basis _ O.1.fg O.1.span_eq_top
  have hfg : Op.FG := by rw [hOp, hb e]; exact Submodule.fg_span (Set.finite_range _)
  have h1 : (1 : QuatAlg ℚ_[p] a b) ∈ Op := by rw [hOp, ← hSd]; exact Sd.one_mem
  have hmul : ∀ x ∈ Op, ∀ y ∈ Op, x * y ∈ Op := by
    rw [hOp, ← hSd]; intro x hx y hy; exact Sd.mul_mem hx hy
  obtain ⟨ι, hι⟩ := l19_conj p Op hfg h1 hmul ι₀
  let S : Subring (QuatAlg ℚ_[p] a b) :=
    ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix.range).comap ι.toRingEquiv.toRingHom
  have hmemS : ∀ z, z ∈ S ↔ ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], m.map (algebraMap ℤ_[p] ℚ_[p]) = ι z :=
    fun z => Iff.rfl
  have hOS : ∀ z ∈ Op, z ∈ S := by
    intro z hz
    rw [hmemS]
    exact ⟨Matrix.of fun i j => (hι z hz i j).choose, by ext i j; exact (hι z hz i j).choose_spec⟩
  have hev : ∀ ij : Fin 2 × Fin 2, ∀ᶠ k in Filter.atTop,
      ((p : ℚ_[p]) ^ k) • ι.symm (Matrix.single ij.1 ij.2 1) ∈ Op :=
    fun ij => l19_pow_mem p O.1 _
  obtain ⟨k, hk⟩ := (Filter.eventually_all.2 hev).exists
  have hbound : ∀ z ∈ S, ((p : ℚ_[p]) ^ k) • z ∈ Op := by
    intro z hz
    obtain ⟨m, hm⟩ := (hmemS z).1 hz
    have hz' : z = ∑ i, ∑ j, (algebraMap ℤ_[p] ℚ_[p] (m i j)) • ι.symm (Matrix.single i j 1) := by
      rw [← ι.symm_apply_apply z, ← hm, Matrix.matrix_eq_sum_single (m.map _), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_apply]
    rw [hz', Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hk (i, j))
  have hmax := l19_local_max p O S hOS k hbound
  refine ⟨ι, Set.ext fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact (hmemS z).1 (hOS z hz)
  · rintro ⟨m, rfl⟩
    refine ⟨ι.symm (m.map (algebraMap ℤ_[p] ℚ_[p])), hmax _ ((hmemS _).2 ⟨m, ?_⟩), ?_⟩ <;> simp

/-! ### Proof of item 20 (private helpers; plan: `docs/notes/Q2-titan/l20-plan.md`) -/
private theorem l20_mul_le_one {u v : ℝ} (hu : u ≤ 1) (hv0 : 0 ≤ v) (hv : v ≤ 1) : u * v ≤ 1 := by
  nlinarith

private theorem l20_div {a b : ℤ} {D : ℕ} (hD : RamifiedExactly a b D) (p : ℕ) [Fact p.Prime] (hpD : p ∣ D) :
    ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x := by
  obtain ⟨ha, hb, -, h⟩ := hD
  have h1 : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = -1 := (h p).2 hpD
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have ha' : (a : ℚ_[p]) ≠ 0 := by exact_mod_cast ha.ne
  have hb' : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb.ne
  exact (split_iff_isotropic h2 _ _ ha' hb').2 h1

private theorem l20_nrd_trd_scalar {a b : ℤ} (p : ℕ) [Fact p.Prime] (q : ℚ_[p]) :
    nrd (algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) q) = q ^ 2 ∧ trd (algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) q) = 2 * q := by
  constructor <;> simp [nrd, trd, QuaternionAlgebra.algebraMap_eq]

private theorem l20_norm_sub_le (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact Padic.nonarchimedean _ _

/-- Trace lemma: in the division algebra, `|nrd z| ≤ 1 ⇒ |trd z| ≤ 1`. -/
private theorem l20_trd {a b : ℤ} (p : ℕ) [Fact p.Prime] (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x)
    (z : QuatAlg ℚ_[p] a b) (hz : ‖nrd z‖ ≤ 1) : ‖trd z‖ ≤ 1 := by
  by_contra ht
  push Not at ht
  set t := trd z with htdef
  set n := nrd z with hndef
  have ht0 : t ≠ 0 := by rintro h; rw [h, norm_zero] at ht; linarith
  set c : ℚ_[p] := n / t ^ 2 with hcdef
  have hc : ‖c‖ < 1 := by
    rw [hcdef, norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  set c' : ℤ_[p] := ⟨c, hc.le⟩
  have hF : ‖Polynomial.aeval (1 : ℤ_[p]) (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c')‖ <
      ‖Polynomial.aeval (1 : ℤ_[p]) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c'))‖ ^ 2 := by
    have e1 : Polynomial.aeval (1 : ℤ_[p]) (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c') = c' := by simp
    have e2 : Polynomial.aeval (1 : ℤ_[p])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c')) = 1 := by
      simp
    rw [e1, e2, norm_one, one_pow]
    exact hc
  obtain ⟨y, hy, -⟩ := hensels_lemma hF
  have hy' : (y : ℚ_[p]) ^ 2 - y + c = 0 := by
    have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hy
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r : ℚ_[p], r = t * y := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℚ_[p], s = t - r := ⟨_, rfl⟩
  have hrs : r * s = n := by
    have : r * s = - t ^ 2 * ((y : ℚ_[p]) ^ 2 - y) := by rw [hs, hr]; ring
    rw [this]
    have hy'' : (y : ℚ_[p]) ^ 2 - y = - c := by linear_combination hy'
    rw [hy'', hcdef]
    field_simp
  have hquad := ((nrd_trd_basic.{0, 0} (R := ℚ_[p]) (a := a) (b := b)).1 z).2.2.2
  have hprod : (z - algebraMap ℚ_[p] _ r) * (z - algebraMap ℚ_[p] _ s) = 0 := by
    have e : (z - algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) r) * (z - algebraMap ℚ_[p] _ s) =
        z ^ 2 - (r + s) • z + algebraMap ℚ_[p] _ (r * s) := by
      rw [Algebra.smul_def, map_add, map_mul, sub_mul, mul_sub, mul_sub, ← Algebra.commutes s z, pow_two]
      noncomm_ring
    rw [e, hrs, show r + s = t by rw [hs]; ring]
    exact hquad
  have hscal : ∃ q : ℚ_[p], z = algebraMap ℚ_[p] _ q := by
    by_cases h0 : z - algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) r = 0
    · exact ⟨r, sub_eq_zero.1 h0⟩
    · exact ⟨s, sub_eq_zero.1 (((hdiv _ h0).mul_right_eq_zero).1 hprod)⟩
  obtain ⟨q, hq⟩ := hscal
  have hn : n = q ^ 2 := by rw [hndef, hq]; exact (l20_nrd_trd_scalar p q).1
  have htq : t = 2 * q := by rw [htdef, hq]; exact (l20_nrd_trd_scalar p q).2
  have h2 : ‖(2 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) 2
  have hq1 : 1 < ‖q‖ := by
    rw [htq, norm_mul] at ht
    nlinarith [norm_nonneg q, norm_nonneg (2 : ℚ_[p])]
  rw [hn, norm_pow] at hz
  nlinarith

private theorem l20_nrd_one_add {a b : ℤ} (p : ℕ) [Fact p.Prime] (z : QuatAlg ℚ_[p] a b) :
    nrd (1 + z) = 1 + trd z + nrd z := by
  simp [nrd, trd]; ring

private theorem l20_add {a b : ℤ} (p : ℕ) [Fact p.Prime] (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x)
    (x y : QuatAlg ℚ_[p] a b) (hx : ‖nrd x‖ ≤ 1) (hy : ‖nrd y‖ ≤ 1) : ‖nrd (x + y)‖ ≤ 1 := by
  wlog hxy : ‖nrd x‖ ≤ ‖nrd y‖ generalizing x y
  · rw [add_comm]; exact this y x hy hx (le_of_not_ge hxy)
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx
  obtain ⟨u, rfl⟩ := hdiv y hy0
  have hmul := (nrd_trd_basic.{0, 0} (R := ℚ_[p]) (a := a) (b := b)).2.1
  have hnu : nrd (u : QuatAlg ℚ_[p] a b) ≠ 0 :=
    ((isUnit_iff_isUnit_nrd (R := ℚ_[p]) (a := a) (b := b)).1 _ |>.1 u.isUnit).ne_zero
  set z := x * ((u⁻¹ : (QuatAlg ℚ_[p] a b)ˣ) : QuatAlg ℚ_[p] a b) with hz
  have hxz : x = z * u := by rw [hz, mul_assoc, Units.inv_mul, mul_one]
  have hnz : ‖nrd z‖ ≤ 1 := by
    have h1 : ‖nrd x‖ = ‖nrd z‖ * ‖nrd (u : QuatAlg ℚ_[p] a b)‖ := by rw [hxz, hmul, norm_mul]
    have h2 : 0 < ‖nrd (u : QuatAlg ℚ_[p] a b)‖ := norm_pos_iff.2 hnu
    nlinarith
  have htz := l20_trd p hdiv z hnz
  have e : x + u = (1 + z) * u := by rw [add_mul, one_mul, ← hxz, add_comm]
  rw [e, hmul, l20_nrd_one_add, norm_mul]
  have h3 : ‖1 + trd z + nrd z‖ ≤ 1 := by
    refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le ?_ htz)) hnz)
    rw [norm_one]
  calc ‖1 + trd z + nrd z‖ * ‖nrd (u : QuatAlg ℚ_[p] a b)‖ ≤ 1 * 1 :=
        mul_le_mul h3 hy (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Integral coordinates give integral reduced norm. -/
private theorem l20_nrd_int {a b : ℤ} (p : ℕ) [Fact p.Prime] (y : QuatAlg ℚ_[p] a b) (h0 : ‖y.re‖ ≤ 1)
    (h1 : ‖y.imI‖ ≤ 1) (h2 : ‖y.imJ‖ ≤ 1) (h3 : ‖y.imK‖ ≤ 1) : ‖nrd y‖ ≤ 1 := by
  rw [← PadicInt.mem_subring_iff] at h0 h1 h2 h3 ⊢
  have ha : ((a : ℤ) : ℚ_[p]) ∈ PadicInt.subring p := intCast_mem _ a
  have hb : ((b : ℤ) : ℚ_[p]) ∈ PadicInt.subring p := intCast_mem _ b
  unfold nrd
  refine add_mem (sub_mem (sub_mem (pow_mem h0 2) (mul_mem ha (pow_mem h1 2))) (mul_mem hb (pow_mem h2 2)))
    (mul_mem (mul_mem ha hb) (pow_mem h3 2))

/-- Coordinate bound on `{|nrd| ≤ 1}`. -/
private theorem l20_bound {a b : ℤ} (p : ℕ) [Fact p.Prime] (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x)
    (x : QuatAlg ℚ_[p] a b) (hx : ‖nrd x‖ ≤ 1) :
    ‖((2 * a * b : ℤ) : ℚ_[p]) * x.re‖ ≤ 1 ∧ ‖((2 * a * b : ℤ) : ℚ_[p]) * x.imI‖ ≤ 1 ∧
      ‖((2 * a * b : ℤ) : ℚ_[p]) * x.imJ‖ ≤ 1 ∧ ‖((2 * a * b : ℤ) : ℚ_[p]) * x.imK‖ ≤ 1 := by
  have hmul := (nrd_trd_basic.{0, 0} (R := ℚ_[p]) (a := a) (b := b)).2.1
  have hA : ‖((a : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one a
  have hB : ‖((b : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one b
  have hint : ∀ e : QuatAlg ℚ_[p] a b, ‖nrd e‖ ≤ 1 → ‖trd (x * e)‖ ≤ 1 := fun e he =>
    l20_trd p hdiv _ (by rw [hmul, norm_mul]; nlinarith [norm_nonneg (nrd x), norm_nonneg (nrd e)])
  have h0 := l20_trd p hdiv x hx
  have h1 := hint ⟨0, 1, 0, 0⟩ (l20_nrd_int p _ (by simp) (by simp) (by simp) (by simp))
  have h2 := hint ⟨0, 0, 1, 0⟩ (l20_nrd_int p _ (by simp) (by simp) (by simp) (by simp))
  have h3 := hint ⟨0, 0, 0, 1⟩ (l20_nrd_int p _ (by simp) (by simp) (by simp) (by simp))
  simp only [trd, QuaternionAlgebra.re_mul] at h0 h1 h2 h3
  simp at h1 h2 h3
  push_cast
  have hAB : ‖((a : ℤ) : ℚ_[p])‖ * ‖((b : ℤ) : ℚ_[p])‖ ≤ 1 := l20_mul_le_one hA (norm_nonneg _) hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc _ = (‖((a : ℤ) : ℚ_[p])‖ * ‖((b : ℤ) : ℚ_[p])‖) * ‖2 * x.re‖ := by simp only [norm_mul]; ring
      _ ≤ 1 := l20_mul_le_one hAB (norm_nonneg _) h0
  · calc _ = ‖((b : ℤ) : ℚ_[p])‖ * (‖(2 : ℚ_[p])‖ * (‖((a : ℤ) : ℚ_[p])‖ * ‖x.imI‖)) := by
          simp only [norm_mul]; ring
      _ ≤ 1 := l20_mul_le_one hB (by positivity) h1
  · calc _ = ‖((a : ℤ) : ℚ_[p])‖ * (‖(2 : ℚ_[p])‖ * (‖((b : ℤ) : ℚ_[p])‖ * ‖x.imJ‖)) := by
          simp only [norm_mul]; ring
      _ ≤ 1 := l20_mul_le_one hA (by positivity) h2
  · calc _ = ‖(2 : ℚ_[p])‖ * (‖((a : ℤ) : ℚ_[p])‖ * ‖((b : ℤ) : ℚ_[p])‖ * ‖x.imK‖) := by
          simp only [norm_mul]; ring
      _ ≤ 1 := h3

private theorem l20_nrd_smul {a b : ℤ} (p : ℕ) [Fact p.Prime] (q : ℚ_[p]) (y : QuatAlg ℚ_[p] a b) :
    nrd (q • y) = q ^ 2 * nrd y := by
  simp [nrd]; ring

private theorem l20_nrd_pow {a b : ℤ} (p : ℕ) [Fact p.Prime] (y : QuatAlg ℚ_[p] a b) (n : ℕ) :
    nrd (y ^ n) = nrd y ^ n := by
  induction n with
  | zero => simp [nrd]
  | succ n ih => rw [pow_succ, (nrd_trd_basic.{0, 0} (R := ℚ_[p]) (a := a) (b := b)).2.1, ih, pow_succ]

/-- `{x : |nrd x| ≤ 1}` is a `ℤ_p`-subalgebra. -/
private theorem l20_subalg {a b : ℤ} (p : ℕ) [Fact p.Prime] (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x) :
    ∃ S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b), ∀ x, x ∈ S ↔ ‖nrd x‖ ≤ 1 := by
  have hmul := (nrd_trd_basic.{0, 0} (R := ℚ_[p]) (a := a) (b := b)).2.1
  refine ⟨{ carrier := {x | ‖nrd x‖ ≤ 1}
            mul_mem' := fun {x y} hx hy => by
              simp only [Set.mem_ofPred_eq] at hx hy ⊢
              rw [hmul, norm_mul]; exact l20_mul_le_one hx (norm_nonneg _) hy
            add_mem' := fun {x y} hx hy => l20_add p hdiv x y hx hy
            algebraMap_mem' := fun r => by
              simp only [Set.mem_ofPred_eq]
              rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (QuatAlg ℚ_[p] a b), (l20_nrd_trd_scalar p _).1,
                norm_pow]
              exact pow_le_one₀ (norm_nonneg _) (by simpa using PadicInt.norm_le_one r) }, fun x => Iff.rfl⟩

/-- Compact, open, spanning. -/
private theorem l20_topology {a b : ℤ} (p : ℕ) [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x)
    (S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b)) (hS : ∀ x, x ∈ S ↔ ‖nrd x‖ ≤ 1) :
    IsCompact (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) '' (S : Set (QuatAlg ℚ_[p] a b))) ∧
      IsOpen (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) '' (S : Set (QuatAlg ℚ_[p] a b))) ∧
      Submodule.span ℚ_[p] (S : Set (QuatAlg ℚ_[p] a b)) = ⊤ := by
  set E := QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) with hE
  set f : (Fin 4 → ℚ_[p]) → ℚ_[p] := fun v => nrd (E.symm v : QuatAlg ℚ_[p] a b) with hfdef
  have hT : E '' (S : Set (QuatAlg ℚ_[p] a b)) = {v | ‖f v‖ ≤ 1} := by
    rw [Equiv.image_eq_preimage_symm]
    ext v
    simp only [Set.mem_preimage, SetLike.mem_coe, hS, Set.mem_ofPred_eq, hfdef]
  have hf' : f = fun v => v 0 ^ 2 - (a : ℚ_[p]) * v 1 ^ 2 - (b : ℚ_[p]) * v 2 ^ 2 +
      (a : ℚ_[p]) * (b : ℚ_[p]) * v 3 ^ 2 := rfl
  have hfc : Continuous f := by rw [hf']; fun_prop
  have hcl : IsClosed {v | ‖f v‖ ≤ 1} := isClosed_le (continuous_norm.comp hfc) continuous_const
  have hN0 : ((2 * a * b : ℤ) : ℚ_[p]) ≠ 0 := by
    have : (2 * a * b : ℤ) ≠ 0 := by positivity
    exact_mod_cast this
  have hNpos : 0 < ‖((2 * a * b : ℤ) : ℚ_[p])‖ := norm_pos_iff.2 hN0
  set C := ‖((2 * a * b : ℤ) : ℚ_[p])‖⁻¹ with hC
  have hdivC : ∀ w : ℚ_[p], ‖((2 * a * b : ℤ) : ℚ_[p]) * w‖ ≤ 1 → ‖w‖ ≤ C := by
    intro w hw
    rw [norm_mul] at hw
    calc ‖w‖ = C * (‖((2 * a * b : ℤ) : ℚ_[p])‖ * ‖w‖) := by rw [hC]; field_simp
      _ ≤ C * 1 := by gcongr
      _ = C := mul_one C
  have hsub : {v | ‖f v‖ ≤ 1} ⊆ Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℚ_[p]) C) := by
    intro v hv i _
    obtain ⟨h0, h1, h2, h3⟩ := l20_bound p hdiv (E.symm v) hv
    rw [mem_closedBall_zero_iff]
    fin_cases i
    · exact hdivC _ h0
    · exact hdivC _ h1
    · exact hdivC _ h2
    · exact hdivC _ h3
  let H : AddSubgroup (Fin 4 → ℚ_[p]) :=
    { carrier := {v | ‖f v‖ ≤ 1}
      add_mem' := fun {v w} hv hw => l20_add p hdiv (E.symm v) (E.symm w) hv hw
      zero_mem' := by simp [hf']
      neg_mem' := fun {v} hv => by
        simp only [Set.mem_ofPred_eq, hf'] at hv ⊢
        simpa using hv }
  have hZ : IsOpen (Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℚ_[p]) 1)) :=
    isOpen_set_pi (Set.finite_univ : (Set.univ : Set (Fin 4)).Finite) fun _ _ =>
      IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hZH : Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℚ_[p]) 1) ⊆ (H : Set (Fin 4 → ℚ_[p])) := by
    intro v hv
    have hv' : ∀ i, ‖v i‖ ≤ 1 := fun i => mem_closedBall_zero_iff.1 (hv i (Set.mem_univ i))
    exact l20_nrd_int p (E.symm v) (hv' 0) (hv' 1) (hv' 2) (hv' 3)
  have hHo : IsOpen (H : Set (Fin 4 → ℚ_[p])) :=
    AddSubgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset
      (hZ.mem_nhds (show (0 : Fin 4 → ℚ_[p]) ∈ _ from fun i _ => by simp)) hZH)
  refine ⟨?_, ?_, ?_⟩
  · rw [hT]
    exact (isCompact_univ_pi fun _ => isCompact_closedBall 0 C).of_isClosed_subset hcl hsub
  · rw [hT]; exact hHo
  · refine top_le_iff.1 fun z _ => ?_
    have hz : z = z.re • (1 : QuatAlg ℚ_[p] a b) + z.imI • (⟨0, 1, 0, 0⟩ : QuatAlg ℚ_[p] a b) +
        z.imJ • (⟨0, 0, 1, 0⟩ : QuatAlg ℚ_[p] a b) + z.imK • (⟨0, 0, 0, 1⟩ : QuatAlg ℚ_[p] a b) := by
      ext <;> simp
    rw [hz]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ((hS _).2
        (l20_nrd_int p _ (by simp) (by simp) (by simp) (by simp))))

private theorem l20_fg_bound {a b : ℤ} (p : ℕ) [Fact p.Prime] (π : QuatAlg ℚ_[p] a b → ℚ_[p])
    (hadd : ∀ x y, π (x + y) = π x + π y) (hsmul : ∀ (r : ℤ_[p]) x, π (r • x) = (r : ℚ_[p]) * π x)
    (h0 : π 0 = 0) (N : Submodule ℤ_[p] (QuatAlg ℚ_[p] a b)) (hN : N.FG) :
    ∀ᶠ m in Filter.atTop, ∀ y ∈ N, ‖(p : ℚ_[p]) ^ m * π y‖ ≤ 1 := by
  obtain ⟨s, rfl⟩ := hN
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hev : ∀ g ∈ s, ∀ᶠ m in Filter.atTop, ‖(p : ℚ_[p]) ^ m * π g‖ ≤ 1 := by
    intro g _
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hp1).eventually_ge_atTop ‖π g‖] with k hk
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [inv_mul_le_iff₀ hpk, mul_one]
    exact hk
  filter_upwards [(Filter.eventually_all_finset s).2 hev] with m hm
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hm x hx
  | zero => rw [h0, mul_zero, norm_zero]; exact zero_le_one
  | add x y _ _ hx hy => rw [hadd, mul_add]; exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [hsmul, mul_left_comm, norm_mul]
    exact l20_mul_le_one r.2 (norm_nonneg _) hx

/-- Integral over `ℤ_p` implies integral reduced norm. -/
private theorem l20_integral {a b : ℤ} (p : ℕ) [Fact p.Prime] (x : QuatAlg ℚ_[p] a b) (hx : IsIntegral ℤ_[p] x) :
    ‖nrd x‖ ≤ 1 := by
  have hN := hx.fg_adjoin_singleton
  have hmem : ∀ n : ℕ, x ^ n ∈ Subalgebra.toSubmodule (Algebra.adjoin ℤ_[p] {x}) := fun n =>
    Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton x)) n
  have e0 := l20_fg_bound p (fun y => y.re) (fun x y => by simp)
    (fun r x => by show r • x.re = _; rw [Algebra.smul_def]; rfl)
    (by simp) _ hN
  have e1 := l20_fg_bound p (fun y => y.imI) (fun x y => by simp)
    (fun r x => by show r • x.imI = _; rw [Algebra.smul_def]; rfl)
    (by simp) _ hN
  have e2 := l20_fg_bound p (fun y => y.imJ) (fun x y => by simp)
    (fun r x => by show r • x.imJ = _; rw [Algebra.smul_def]; rfl)
    (by simp) _ hN
  have e3 := l20_fg_bound p (fun y => y.imK) (fun x y => by simp)
    (fun r x => by show r • x.imK = _; rw [Algebra.smul_def]; rfl)
    (by simp) _ hN
  obtain ⟨m, hm0, hm1, hm2, hm3⟩ := (e0.and (e1.and (e2.and e3))).exists
  have hpos : (0 : ℝ) < (p : ℝ) ^ m := by
    have := (Fact.out : p.Prime).pos; positivity
  have hb : ∀ n : ℕ, ‖nrd x‖ ^ n ≤ (p : ℝ) ^ (2 * m) := by
    intro n
    have h := l20_nrd_int p (((p : ℚ_[p]) ^ m) • x ^ n) (by simpa using hm0 _ (hmem n))
      (by simpa using hm1 _ (hmem n)) (by simpa using hm2 _ (hmem n)) (by simpa using hm3 _ (hmem n))
    rw [l20_nrd_smul, l20_nrd_pow, norm_mul, norm_pow, norm_pow, norm_pow, Padic.norm_p, inv_pow, inv_pow,
      inv_mul_le_iff₀ (by positivity), mul_one] at h
    rw [mul_comm, pow_mul]
    exact h
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop ((p : ℝ) ^ (2 * m))).exists
  linarith [hb n]


/-- `O` maximal: `O_p = {x : |nrd x| ≤ 1}` (Step 5). -/
private theorem l20_local {a b : ℤ} (p : ℕ) [Fact p.Prime] (O : MaxOrder a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ x : QuatAlg ℚ_[p] a b, x ≠ 0 → IsUnit x)
    (S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b)) (hS : ∀ x, x ∈ S ↔ ‖nrd x‖ ≤ 1) :
    (localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) = S := by
  set Op := localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) with hOp
  have hle : Op ≤ Subalgebra.toSubmodule S := by
    rw [hOp, localLattice, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, n, hn⟩ := trd_nrd_int_of_mem O.1 hx
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, hS,
      ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).2.2.2 ℚ_[p] (algebraMap ℚ ℚ_[p]) x).1, hn]
    simpa using Padic.norm_int_le_one (p := p) n
  have hOS : ∀ z ∈ Op, z ∈ S := fun z hz => hle hz
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k0, hk0, hk1, hk2, hk3⟩ := ((l19_pow_mem p O.1 (1 : QuatAlg ℚ_[p] a b)).and
    ((l19_pow_mem p O.1 (⟨0, 1, 0, 0⟩ : QuatAlg ℚ_[p] a b)).and
    ((l19_pow_mem p O.1 (⟨0, 0, 1, 0⟩ : QuatAlg ℚ_[p] a b)).and
    (l19_pow_mem p O.1 (⟨0, 0, 0, 1⟩ : QuatAlg ℚ_[p] a b))))).exists
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hp1).eventually_ge_atTop
    ‖((2 * a * b : ℤ) : ℚ_[p])‖⁻¹).exists
  have hpm : (0 : ℝ) < (p : ℝ) ^ m := by have := (Fact.out : p.Prime).pos; positivity
  have hN : 0 < ‖((2 * a * b : ℤ) : ℚ_[p])‖ := by
    have : (2 * a * b : ℤ) ≠ 0 := by positivity
    exact norm_pos_iff.2 (by exact_mod_cast this)
  have hcoord : ∀ w : ℚ_[p], ‖((2 * a * b : ℤ) : ℚ_[p]) * w‖ ≤ 1 → ‖(p : ℚ_[p]) ^ m * w‖ ≤ 1 := by
    intro w hw
    rw [norm_mul] at hw
    have hw' : ‖w‖ ≤ (p : ℝ) ^ m := by
      calc ‖w‖ = ‖((2 * a * b : ℤ) : ℚ_[p])‖⁻¹ * (‖((2 * a * b : ℤ) : ℚ_[p])‖ * ‖w‖) := by field_simp
        _ ≤ ‖((2 * a * b : ℤ) : ℚ_[p])‖⁻¹ * 1 := by gcongr
        _ ≤ (p : ℝ) ^ m := by rw [mul_one]; exact hm
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hpm, mul_one]
    exact hw'
  have hsm : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ Op, c • v ∈ Op := fun c hc v hv => by
    have : c • v = (⟨c, hc⟩ : ℤ_[p]) • v := (algebraMap_smul ℚ_[p] (⟨c, hc⟩ : ℤ_[p]) v).symm
    rw [this]; exact Op.smul_mem _ hv
  have hbound : ∀ z ∈ S.toSubring, ((p : ℚ_[p]) ^ (m + k0)) • z ∈ Op := by
    intro z hz
    obtain ⟨h0, h1, h2, h3⟩ := l20_bound p hdiv z ((hS z).1 hz)
    have hz' : ((p : ℚ_[p]) ^ (m + k0)) • z =
        ((p : ℚ_[p]) ^ m * z.re) • (((p : ℚ_[p]) ^ k0) • (1 : QuatAlg ℚ_[p] a b)) +
        ((p : ℚ_[p]) ^ m * z.imI) • (((p : ℚ_[p]) ^ k0) • (⟨0, 1, 0, 0⟩ : QuatAlg ℚ_[p] a b)) +
        ((p : ℚ_[p]) ^ m * z.imJ) • (((p : ℚ_[p]) ^ k0) • (⟨0, 0, 1, 0⟩ : QuatAlg ℚ_[p] a b)) +
        ((p : ℚ_[p]) ^ m * z.imK) • (((p : ℚ_[p]) ^ k0) • (⟨0, 0, 0, 1⟩ : QuatAlg ℚ_[p] a b)) := by
      ext <;> simp [pow_add] <;> ring
    rw [hz']
    exact add_mem (add_mem (add_mem (hsm _ (hcoord _ h0) _ hk0) (hsm _ (hcoord _ h1) _ hk1))
      (hsm _ (hcoord _ h2) _ hk2)) (hsm _ (hcoord _ h3) _ hk3)
  have hmax := l19_local_max p O S.toSubring hOS (m + k0) hbound
  ext z
  exact ⟨fun hz => hOS z hz, fun hz => hmax z hz⟩

/-! ### Proof of item 34 (private helpers; plan: `docs/notes/Q2-titan/l20-plan.md`) -/

/-- Level `p^n` for `p ∤ D`: reduction of `ι_p : O_p ≅ M₂(ℤ_p)` modulo `p^n`. -/
private theorem l34_primePow {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hD : RamifiedExactly a b D) (p : ℕ)
    [Fact p.Prime] (hpD : ¬ p ∣ D) (n : ℕ) :
    ∃ φ : O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)), Function.Surjective φ := by
  obtain ⟨ι, hι⟩ := maximalOrder_local_split O hD p hpD
  set bc := baseChange a b (algebraMap ℚ ℚ_[p]) with hbc
  set Op := localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) with hOp
  set j : Matrix (Fin 2) (Fin 2) ℤ_[p] →+* Matrix (Fin 2) (Fin 2) ℚ_[p] := (algebraMap ℤ_[p] ℚ_[p]).mapMatrix
    with hj
  have hjinj : Function.Injective j := Matrix.map_injective (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hιj : ∀ z ∈ Op, ∃ m, j m = ι z := by
    intro z hz
    have : ι z ∈ ι '' (Op : Set (QuatAlg ℚ_[p] a b)) := ⟨z, hz, rfl⟩
    rw [hι] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩
  let g : O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    (ι : QuatAlg ℚ_[p] a b →+* Matrix (Fin 2) (Fin 2) ℚ_[p]).comp
      (bc.comp (O.1.toSubalgebra.val : O.1.toSubalgebra →+* QuatAlg ℚ a b))
  have hg : ∀ x : O.1.toSubalgebra, g x = ι (bc x) := fun x => rfl
  have hgr : ∀ x, g x ∈ j.range := by
    intro x
    obtain ⟨m, hm⟩ := hιj (bc x) (Submodule.subset_span ⟨x, x.2, rfl⟩)
    exact ⟨m, by rw [hm, hg]⟩
  let eqv : Matrix (Fin 2) (Fin 2) ℤ_[p] ≃+* j.range :=
    RingEquiv.ofBijective j.rangeRestrict
      ⟨fun x y h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective j⟩
  let φ : O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)) :=
    (PadicInt.toZModPow n).mapMatrix.comp ((eqv.symm : j.range →+* _).comp (g.codRestrict j.range hgr))
  have hφ : ∀ x m, j m = g x → φ x = (PadicInt.toZModPow n).mapMatrix m := by
    intro x m hm
    have : eqv.symm (g.codRestrict j.range hgr x) = m := by
      rw [RingEquiv.symm_apply_eq]
      exact Subtype.ext hm.symm
    simp only [φ, RingHom.comp_apply]
    exact congrArg _ this
  refine ⟨φ, fun T => ?_⟩
  set m0 : Matrix (Fin 2) (Fin 2) ℤ_[p] := T.map fun t => ((t.val : ℕ) : ℤ_[p]) with hm0
  have hm0T : (PadicInt.toZModPow n).mapMatrix m0 = T := by
    ext i k
    simp [hm0]
  have hz : j m0 ∈ ι '' (Op : Set (QuatAlg ℚ_[p] a b)) := by rw [hι]; exact ⟨m0, rfl⟩
  obtain ⟨z, hzOp, hzm⟩ := hz
  obtain ⟨x, hx, w, hw, hzw⟩ := l19_approx p O.1 n z hzOp
  obtain ⟨m1, hm1⟩ := hιj w hw
  refine ⟨⟨x, hx⟩, ?_⟩
  have hr : ∀ (r : ℤ_[p]) (v : QuatAlg ℚ_[p] a b), ι (r • v) = (algebraMap ℤ_[p] ℚ_[p] r) • ι v := by
    intro r v
    rw [← algebraMap_smul ℚ_[p] r v, map_smul]
  have hjsm : ∀ (r : ℤ_[p]) (m : Matrix (Fin 2) (Fin 2) ℤ_[p]), j (r • m) = (algebraMap ℤ_[p] ℚ_[p] r) • j m := by
    intro r m
    ext i k
    simp only [hj, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hgx : j (m0 - ((p : ℤ_[p]) ^ n) • m1) = g ⟨x, hx⟩ := by
    rw [hg, map_sub, hjsm, hm1, ← hr, ← hzm, ← map_sub, hzw, add_sub_cancel_right]
  rw [hφ _ _ hgx, map_sub, hm0T]
  have hpn : PadicInt.toZModPow (p := p) n ((p : ℤ_[p]) ^ n) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have : (PadicInt.toZModPow n).mapMatrix (((p : ℤ_[p]) ^ n) • m1) = 0 := by
    ext i k
    simp [Matrix.smul_apply, hpn]
  rw [this, sub_zero]

/-- Chinese remainder step for surjections onto `M₂(ℤ/m)`, `M₂(ℤ/n)`, `m, n` coprime. -/
private theorem l34_coprime {A : Type*} [Ring A] (m n : ℕ) (hmn : m.Coprime n)
    (hm : ∃ φ : A →+* Matrix (Fin 2) (Fin 2) (ZMod m), Function.Surjective φ)
    (hn : ∃ φ : A →+* Matrix (Fin 2) (Fin 2) (ZMod n), Function.Surjective φ) :
    ∃ φ : A →+* Matrix (Fin 2) (Fin 2) (ZMod (m * n)), Function.Surjective φ := by
  obtain ⟨φm, hφm⟩ := hm
  obtain ⟨φn, hφn⟩ := hn
  set e := ZMod.chineseRemainder hmn with he
  let P : Matrix (Fin 2) (Fin 2) (ZMod m) × Matrix (Fin 2) (Fin 2) (ZMod n) →+*
      Matrix (Fin 2) (Fin 2) (ZMod m × ZMod n) :=
    { toFun := fun X => Matrix.of fun i k => (X.1 i k, X.2 i k)
      map_one' := by
        ext i k <;> by_cases h : i = k <;> simp [Matrix.one_apply, h]
      map_mul' := fun X Y => by
        ext i k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      map_zero' := by ext i k <;> simp
      map_add' := fun X Y => by ext i k <;> simp }
  refine ⟨((e.symm : ZMod m × ZMod n →+* ZMod (m * n)).mapMatrix).comp (P.comp (φm.prod φn)), fun T => ?_⟩
  obtain ⟨xm, hxm⟩ := hφm (T.map fun t => (e t).1)
  obtain ⟨xn, hxn⟩ := hφn (T.map fun t => (e t).2)
  have hb0 : (1 : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n := by
    rw [← Nat.gcd_eq_gcd_ab, hmn.gcd_eq_one, Nat.cast_one]
  obtain ⟨A', B', hb⟩ : ∃ A' B' : ℤ, (1 : ℤ) = m * A' + n * B' := ⟨_, _, hb0⟩
  have hum : ((n * B' : ℤ) : ZMod m) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod m)) hb
    push_cast at this ⊢
    rw [ZMod.natCast_self, zero_mul, zero_add] at this
    exact this.symm
  have hvm : ((m * A' : ℤ) : ZMod m) = 0 := by push_cast; rw [ZMod.natCast_self, zero_mul]
  have hvn : ((m * A' : ℤ) : ZMod n) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod n)) hb
    push_cast at this ⊢
    rw [ZMod.natCast_self, zero_mul, add_zero] at this
    exact this.symm
  have hun : ((n * B' : ℤ) : ZMod n) = 0 := by push_cast; rw [ZMod.natCast_self, zero_mul]
  refine ⟨(n * B' : ℤ) • xm + (m * A' : ℤ) • xn, ?_⟩
  have h1 : φm ((n * B' : ℤ) • xm + (m * A' : ℤ) • xn) = T.map fun t => (e t).1 := by
    rw [map_add, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod m), ← Int.cast_smul_eq_zsmul (ZMod m), hum,
      hvm, one_smul, zero_smul, add_zero, hxm]
  have h2 : φn ((n * B' : ℤ) • xm + (m * A' : ℤ) • xn) = T.map fun t => (e t).2 := by
    rw [map_add, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod n), ← Int.cast_smul_eq_zsmul (ZMod n), hun,
      hvn, one_smul, zero_smul, zero_add, hxn]
  ext i k
  simp only [RingHom.comp_apply, RingHom.prod_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h1, h2, P,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply,
    RingEquiv.coe_toRingHom]
  rw [Prod.mk.eta, RingEquiv.symm_apply_apply]

/-- `B` ramified exactly at the primes dividing `D`, `p ∣ D`: `O_{D,p} := {x ∈ B_p : nrd(x) ∈ ℤ_p}` is a `ℤ_p`-order
that contains every element of `B_p` integral over `ℤ_p`; for every maximal order `O`, `O_p = O_{D,p}`. -/
@[tf_id "III.qalg.thm:division-maximal-order"]
theorem division_maximalOrder {a b : ℤ} {D : ℕ} (hD : RamifiedExactly a b D) (p : ℕ) [Fact p.Prime]
    (hpD : p ∣ D) :
    (∃ S : Subalgebra ℤ_[p] (QuatAlg ℚ_[p] a b),
      (S : Set (QuatAlg ℚ_[p] a b)) = {x | nrd x ∈ PadicInt.subring p} ∧
      IsCompact (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) '' (S : Set (QuatAlg ℚ_[p] a b))) ∧
      IsOpen (QuaternionAlgebra.equivTuple (a : ℚ_[p]) 0 (b : ℚ_[p]) '' (S : Set (QuatAlg ℚ_[p] a b))) ∧
      Submodule.span ℚ_[p] (S : Set (QuatAlg ℚ_[p] a b)) = ⊤) ∧
    (∀ x : QuatAlg ℚ_[p] a b, IsIntegral ℤ_[p] x → nrd x ∈ PadicInt.subring p) ∧
    (∀ O : MaxOrder a b,
      (localLattice p (Subalgebra.toSubmodule O.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) =
        {x | nrd x ∈ PadicInt.subring p}) := by
  have hdiv := l20_div hD p hpD
  obtain ⟨S, hS⟩ := l20_subalg p hdiv
  have hSset : (S : Set (QuatAlg ℚ_[p] a b)) = {x | nrd x ∈ PadicInt.subring p} := by
    ext x; exact hS x
  refine ⟨⟨S, hSset, l20_topology p hD.1.ne hD.2.1.ne hdiv S hS⟩, fun x hx => l20_integral p x hx, fun O => ?_⟩
  rw [← hSset]
  exact l20_local p O hD.1.ne hD.2.1.ne hdiv S hS

/-- `O` maximal, `B` ramified exactly at the primes dividing `D`, `M ≥ 1` prime to `D`: `O` has a level structure of
level `M`. -/
@[tf_id "III.qord.thm:level-structure-exists"]
theorem levelStructure_exists {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hD : RamifiedExactly a b D) (M : ℕ)
    [NeZero M] (hM : Nat.Coprime M D) :
    Nonempty (LevelStructure O.1 M) := by
  have key : ∀ N : ℕ, N ≠ 0 → N.Coprime D →
      ∃ φ : O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod N), Function.Surjective φ := by
    intro N
    induction N using Nat.recOnPosPrimePosCoprime with
    | prime_pow q k hq hk =>
      intro _ hcop
      have : Fact q.Prime := ⟨hq⟩
      refine l34_primePow O hD q ?_ k
      intro hqD
      exact hq.one_lt.ne' ((Nat.Coprime.coprime_dvd_left (dvd_pow_self q hk.ne') hcop).eq_one_of_dvd hqD)
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _ _
      have : Subsingleton (Matrix (Fin 2) (Fin 2) (ZMod 1)) :=
        ⟨fun A B => Matrix.ext fun i k => Subsingleton.elim _ _⟩
      exact ⟨{ toFun := fun _ => 0
               map_one' := Subsingleton.elim _ _
               map_mul' := fun _ _ => Subsingleton.elim _ _
               map_zero' := rfl
               map_add' := fun _ _ => Subsingleton.elim _ _ }, fun T => ⟨0, Subsingleton.elim _ _⟩⟩
    | coprime m n _ _ hmn ihm ihn =>
      intro hN hcop
      exact l34_coprime m n hmn (ihm (left_ne_zero_of_mul hN) (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) hcop))
        (ihn (right_ne_zero_of_mul hN) (Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) hcop))
  obtain ⟨φ, hφ⟩ := key M (NeZero.ne M) hM
  exact ⟨⟨φ, hφ⟩⟩

end GL2TF.Quat
