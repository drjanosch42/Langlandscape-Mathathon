/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.BrandtStabFree

/-!
# `BrandtStabFree` (S03-L8), part A: the `Γ_x/{±1}`-action and orbit counting

`lem:s03-stabfree` of `mathematics/chapters/s03/2-eisenstein.tex`: the reduction of
`w_e ∣ B(ℓ)_{e e'}` (`e ≠ e'`) to the *freeness core*: an element `γ ∈ Γ_x`, `γ ≠ ±1`, cannot
stabilise an `ℓ`-neighbour `y` of `x` lying in another class (tex steps (i)–(vi), the analytic
part, isolated as `stabFree_core` below).  Part A (this file's main theorem
`brandtStabFree_of_core`) is the purely group-theoretic step (vii): `Γ_x/{±1}` (order `w_x`)
acts on the neighbour cosets counted by `B(ℓ)_{cc'}` (`lem:s03-nbr`(b)), preserving classes, and
acting freely when `c' ≠ c`, whence `w_x ∣ B(ℓ)_{cc'}`.

Provenance: draft by mistral-large-4-0 via opencode (external, user-run; branch `abhijit/brandtstabfree`,
c170335d), integrated and audited by the Langlandscape agents.
-/

set_option autoImplicit false

namespace Langlandscape.StabFree.Orbit

open GL2TF Langlandscape.Quat Langlandscape.Hyp

variable (d : DefiniteData) (ℓ : ℕ)

section Aux

/-- `-1 ∈ Ô^×`. (`s03-stabfree`) -/
theorem neg_one_mem_Ohat : (-1 : (GL2TF.Quat.BHat d.a d.b)ˣ) ∈ d.Ohat := by
  have h1 : (1 : GL2TF.Quat.BHat d.a d.b) ∈
      GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule d.O.1.toSubalgebra) :=
    GL2TF.Quat.one_mem_orderCompletion d.O.1
  have hneg : (-1 : GL2TF.Quat.BHat d.a d.b) ∈
      GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule d.O.1.toSubalgebra) := by
    show -(1 : GL2TF.Quat.BHat d.a d.b) ∈ _
    exact Submodule.neg_mem _ h1
  refine ⟨hneg, ?_⟩
  have h2 : (((-1 : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹ : (GL2TF.Quat.BHat d.a d.b)ˣ) :
      GL2TF.Quat.BHat d.a d.b) = -1 := by
    simp
  rw [h2]
  exact hneg

/-- The conjugate `x⁻¹ * ι(γ) * x ∈ B̂^×`. -/
noncomputable def uOf (x : (GL2TF.Quat.BHat d.a d.b)ˣ)
    (γ : (GL2TF.Quat.QuatAlg ℚ d.a d.b)ˣ) :
    (GL2TF.Quat.BHat d.a d.b)ˣ :=
  x⁻¹ * Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ * x

/-- `γ ∈ Γ_x(U)` iff `x⁻¹ ι(γ) x ∈ U` (the existing `mem_Gam_iff`, with `uOf` unfolded). (`s03-stabfree`) -/
theorem mem_Gam_iff_uOf {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    {x : (GL2TF.Quat.BHat d.a d.b)ˣ} {γ : (GL2TF.Quat.QuatAlg ℚ d.a d.b)ˣ} :
    γ ∈ Gam U x ↔ uOf d x γ ∈ U :=
  mem_Gam_iff U x γ

/-- `classOf O` in terms of the `Langlandscape` double coset (definitional). (`s03-stabfree`) -/
theorem classOf_eq_mk (z : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    GL2TF.Quat.classOf d.O.1 z = DoubleCoset.mk (globalUnits d.a d.b) d.Ohat z := rfl

/-- The set of left cosets `q = yÔ^×` counted by the Brandt entry `B(ℓ)_{cc'}`
(`lem:s03-nbr`(a); the import's `brandtMatrix`). -/
def nbrSet (c c' : XB d.Ohat) : Type :=
  {q : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat //
    ∃ y ∈ GL2TF.Quat.normNSet d.O.1 ℓ,
      (y : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat) = q ∧
      GL2TF.Quat.classOf d.O.1 (Quotient.out c * y) = c'}

/-- `s03-stabfree`: auxiliary lemma `card_nbrSet` (`lem:s03-stabfree`). -/
theorem card_nbrSet (c c' : XB d.Ohat) :
    GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' = Nat.card (nbrSet d ℓ c c') := rfl

/-- The canonical representative of a neighbour coset is in `normNSet`, and the class
predicate holds for it. (`s03-stabfree`) -/
theorem out_mem_normNSet (hℓ : ℓ.Prime) (c c' : XB d.Ohat) (q : nbrSet d ℓ c c') :
    Quotient.out q.1 ∈ GL2TF.Quat.normNSet d.O.1 ℓ ∧
      GL2TF.Quat.classOf d.O.1 (Quotient.out c * Quotient.out q.1) = c' := by
  obtain ⟨y, hy, hmk, hcl⟩ := q.2
  have heq : ((Quotient.out q.1 : (GL2TF.Quat.BHat d.a d.b)ˣ) : _ ⧸ d.Ohat) = (y : _ ⧸ d.Ohat) :=
    (QuotientGroup.out_eq' q.1).trans hmk.symm
  rw [QuotientGroup.eq] at heq
  set w := (Quotient.out q.1)⁻¹ * y with hw
  have hwU : w ∈ d.Ohat := heq
  have hyu : y = Quotient.out q.1 * w := by
    show y = Quotient.out q.1 * ((Quotient.out q.1)⁻¹ * y)
    group
  have hout2 : Quotient.out q.1 = y * w⁻¹ := by
    rw [hyu]
    group
  have hmem : Quotient.out q.1 ∈ GL2TF.Quat.normNSet d.O.1 ℓ := by
    rw [hout2]
    simpa using (GL2TF.Quat.normNSet_basic d.O.1 ℓ hℓ.pos).1 y hy 1 (Subgroup.one_mem _)
      w⁻¹ (Subgroup.inv_mem _ hwU)
  have hcl2 : GL2TF.Quat.classOf d.O.1 (Quotient.out c * Quotient.out q.1) = c' := by
    rw [hout2, ← mul_assoc, classOf_eq_mk, DoubleCoset.mk_mul_mem ⟨w⁻¹, Subgroup.inv_mem _ hwU⟩]
    rw [classOf_eq_mk] at hcl
    exact hcl
  exact ⟨hmem, hcl2⟩

end Aux

section Action

variable (d : DefiniteData) (ℓ : ℕ)

/-- Membership part of the action on neighbour cosets: `γ • ↑y = ↑(x⁻¹ιγx · y)` stays a
neighbour in the class `c'` (`lem:s03-nbr`(b): `Γ_x` acts on `𝒩(x)` preserving classes). -/
theorem nbrSmul_mem (hℓ : ℓ.Prime) (c c' : XB d.Ohat) (γ : ↥(Gam d.Ohat (Quotient.out c)))
    (q : nbrSet d ℓ c c') :
    ∃ y ∈ GL2TF.Quat.normNSet d.O.1 ℓ,
      (y : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat) =
        QuotientGroup.mk (uOf d (Quotient.out c) γ.1 * Quotient.out q.1) ∧
      GL2TF.Quat.classOf d.O.1 (Quotient.out c * y) = c' := by
  obtain ⟨hout, hcl⟩ := out_mem_normNSet d ℓ hℓ c c' q
  have hU : uOf d (Quotient.out c) γ.1 ∈ d.Ohat := (mem_Gam_iff_uOf d).mp γ.2
  refine ⟨uOf d (Quotient.out c) γ.1 * Quotient.out q.1, ?_, rfl, ?_⟩
  · simpa using (GL2TF.Quat.normNSet_basic d.O.1 ℓ hℓ.pos).1 _ hout _ hU _ (Subgroup.one_mem _)
  · have hH : Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ.1 ∈ globalUnits d.a d.b :=
      ⟨γ.1, rfl⟩
    have hxu : Quotient.out c * (uOf d (Quotient.out c) γ.1 * Quotient.out q.1) =
        Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ.1 *
          (Quotient.out c * Quotient.out q.1) := by
      simp only [uOf]
      group
    rw [classOf_eq_mk, hxu, DoubleCoset.mk_mem_mul ⟨_, hH⟩]
    rw [classOf_eq_mk] at hcl
    exact hcl

/-- The action of `γ ∈ Γ_x` on a neighbour coset (`lem:s03-nbr`(b), `γ · hU = γhU`). -/
noncomputable def nbrSmul (hℓ : ℓ.Prime) (c c' : XB d.Ohat) (γ : ↥(Gam d.Ohat (Quotient.out c)))
    (q : nbrSet d ℓ c c') : nbrSet d ℓ c c' :=
  ⟨QuotientGroup.mk (uOf d (Quotient.out c) γ.1 * Quotient.out q.1),
    nbrSmul_mem d ℓ hℓ c c' γ q⟩

/-- `Γ_x` acts on the neighbour cosets of `x` in the class `c'`. -/
noncomputable def nbrAction (hℓ : ℓ.Prime) (c c' : XB d.Ohat) :
    MulAction ↥(Gam d.Ohat (Quotient.out c)) (nbrSet d ℓ c c') where
  smul := nbrSmul d ℓ hℓ c c'
  one_smul q := by
    apply Subtype.ext
    show QuotientGroup.mk (uOf d (Quotient.out c) (1 : ↥(Gam d.Ohat (Quotient.out c))).1 *
      Quotient.out q.1) = q.1
    have h1 : uOf d (Quotient.out c) (1 : ↥(Gam d.Ohat (Quotient.out c))).1 = 1 := by
      simp [uOf]
    rw [h1, one_mul, QuotientGroup.out_eq']
  mul_smul γ₁ γ₂ q := by
    apply Subtype.ext
    show QuotientGroup.mk (uOf d (Quotient.out c) (γ₁ * γ₂).1 * Quotient.out q.1) =
      QuotientGroup.mk (uOf d (Quotient.out c) γ₁.1 *
        Quotient.out (nbrSmul d ℓ hℓ c c' γ₂ q).1)
    have hsmul2 : (nbrSmul d ℓ hℓ c c' γ₂ q).1 =
        QuotientGroup.mk (uOf d (Quotient.out c) γ₂.1 * Quotient.out q.1) := rfl
    obtain ⟨h, hh⟩ :=
      QuotientGroup.mk_out_eq_mul d.Ohat (uOf d (Quotient.out c) γ₂.1 * Quotient.out q.1)
    have hu : uOf d (Quotient.out c) (γ₁ * γ₂).1 =
        uOf d (Quotient.out c) γ₁.1 * uOf d (Quotient.out c) γ₂.1 := by
      simp only [uOf, map_mul, Subgroup.coe_mul]
      group
    rw [hu, hsmul2, hh]
    rw [show uOf d (Quotient.out c) γ₁.1 *
        (uOf d (Quotient.out c) γ₂.1 * Quotient.out q.1 * (h : (GL2TF.Quat.BHat d.a d.b)ˣ)) =
      (uOf d (Quotient.out c) γ₁.1 * uOf d (Quotient.out c) γ₂.1 * Quotient.out q.1) *
        (h : (GL2TF.Quat.BHat d.a d.b)ˣ) by group]
    exact (QuotientGroup.mk_mul_of_mem _ h.2).symm

end Action

section Main

variable (d : DefiniteData) (ℓ : ℕ)

/-- Part A of `lem:s03-stabfree` (step (vii)): from the freeness core (tex steps (i)–(vi),
`stabFree_core` below), the divisibility `w_e ∣ B(ℓ)_{e e'}` for `e ≠ e'`. -/
theorem brandtStabFree_of_core
    (core : ∀ (x y : (GL2TF.Quat.BHat d.a d.b)ˣ), y ∈ GL2TF.Quat.normNSet d.O.1 ℓ →
      ∀ γ ∈ Gam d.Ohat x, γ ∉ pmOne → γ ∈ Gam d.Ohat (x * y) →
        DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (x * y) =
          DoubleCoset.mk (globalUnits d.a d.b) d.Ohat x) :
    BrandtStabFree d ℓ := by
  intro hℓ _hℓD _hD c c' hcc'
  rw [card_nbrSet d ℓ c c']
  letI := nbrAction d ℓ hℓ c c'
  -- finiteness of the group and of the neighbour set
  have hfinG : Finite ↥(Gam d.Ohat (Quotient.out c)) := by
    obtain ⟨Ox, -, hOx⟩ := (GL2TF.Quat.stabilizer_units d.O.1 (Quotient.out c)).1
    have h : Gam d.Ohat (Quotient.out c) = GL2TF.Quat.unitGroup Ox := hOx
    rw [h]
    exact (GL2TF.Quat.unitGroup_eq_nrd_one_finite d.ha d.hb Ox).2
  haveI : Finite ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) :=
    Finite.of_injective
      (fun h : ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) =>
        (⟨h.1, (Subgroup.mem_inf.mp h.2).1⟩ : ↥(Gam d.Ohat (Quotient.out c))))
      (by intro a b hab; exact Subtype.ext (Subtype.mk.inj hab))
  have hfinimg : ((QuotientGroup.mk : (GL2TF.Quat.BHat d.a d.b)ˣ → _ ⧸ d.Ohat) ''
      GL2TF.Quat.normNSet d.O.1 ℓ).Finite :=
    (GL2TF.Quat.normNSet_basic d.O.1 ℓ hℓ.pos).2.2.2.1
  haveI : Finite ↥(QuotientGroup.mk '' GL2TF.Quat.normNSet d.O.1 ℓ) :=
    Set.finite_coe_iff.mpr hfinimg
  have hfinS : Finite (nbrSet d ℓ c c') :=
    Finite.of_injective
      (fun q : nbrSet d ℓ c c' =>
        (⟨q.1, by
          obtain ⟨y, hy, hmk, -⟩ := q.2
          exact ⟨y, hy, hmk⟩⟩ : ↥(QuotientGroup.mk '' GL2TF.Quat.normNSet d.O.1 ℓ)))
      (by intro a b hab; exact Subtype.ext (Subtype.mk.inj hab))
  -- the stabiliser of every neighbour in the class `c' ≠ c` is exactly `Γ_x ∩ {±1}`
  have hstab : ∀ q : nbrSet d ℓ c c', MulAction.stabilizer ↥(Gam d.Ohat (Quotient.out c)) q =
      (Gam d.Ohat (Quotient.out c) ⊓ pmOne).subgroupOf (Gam d.Ohat (Quotient.out c)) := by
    intro q
    ext γ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hsm
      have hval : (QuotientGroup.mk (uOf d (Quotient.out c) γ.1 * Quotient.out q.1) :
          (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Ohat) = q.1 := congrArg Subtype.val hsm
      have hmemU : uOf d (Quotient.out c * Quotient.out q.1) γ.1 ∈ d.Ohat := by
        have hcalc : uOf d (Quotient.out c * Quotient.out q.1) γ.1 =
            (Quotient.out q.1)⁻¹ * uOf d (Quotient.out c) γ.1 * Quotient.out q.1 := by
          simp only [uOf]
          group
        rw [hcalc]
        have h1 : (uOf d (Quotient.out c) γ.1 * Quotient.out q.1)⁻¹ * Quotient.out q.1 ∈ d.Ohat :=
          QuotientGroup.eq.mp (hval.trans (QuotientGroup.out_eq' q.1).symm)
        have h2 : (Quotient.out q.1)⁻¹ * uOf d (Quotient.out c) γ.1 * Quotient.out q.1 =
            ((uOf d (Quotient.out c) γ.1 * Quotient.out q.1)⁻¹ * Quotient.out q.1)⁻¹ := by
          group
        rw [h2]
        exact Subgroup.inv_mem _ h1
      by_cases hpm : γ.1 ∈ pmOne
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨γ.2, hpm⟩)
      · exfalso
        obtain ⟨hout, hcl⟩ := out_mem_normNSet d ℓ hℓ c c' q
        have hc := core (Quotient.out c) (Quotient.out q.1) hout γ.1 γ.2 hpm
          ((mem_Gam_iff_uOf d).mpr hmemU)
        rw [classOf_eq_mk] at hcl
        have hx : DoubleCoset.mk (globalUnits d.a d.b) d.Ohat (Quotient.out c) = c :=
          DoubleCoset.out_eq' c
        rw [hx] at hc
        exact hcc' (hcl.symm.trans hc).symm
    · intro hmemK
      rw [Subgroup.mem_subgroupOf] at hmemK
      obtain ⟨-, hpm⟩ := Subgroup.mem_inf.mp hmemK
      rcases (mem_pmOne_iff γ.1).mp hpm with h1 | hm1
      · have hγ1 : γ = 1 := Subtype.ext h1
        rw [hγ1]
        exact MulAction.one_smul q
      · have hu : uOf d (Quotient.out c) γ.1 =
            (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) := by
          rw [hm1]
          show (Quotient.out c)⁻¹ * iotaU d.a d.b (-1) * Quotient.out c = negOne
          rw [iotaU_neg_one, mul_assoc, ← negOne_comm, ← mul_assoc, inv_mul_cancel, one_mul]
        apply Subtype.ext
        show QuotientGroup.mk (uOf d (Quotient.out c) γ.1 * Quotient.out q.1) = q.1
        rw [hu]
        conv_rhs => rw [← QuotientGroup.out_eq' q.1]
        refine QuotientGroup.eq.mpr ?_
        have h3 : ((negOne : (GL2TF.Quat.BHat d.a d.b)ˣ) * Quotient.out q.1)⁻¹ *
            Quotient.out q.1 = negOne := by
          rw [← negOne_comm, mul_inv_rev]
          have h4 : (negOne : (GL2TF.Quat.BHat d.a d.b)ˣ)⁻¹ = negOne := by
            apply Units.ext
            simp [negOne]
          rw [h4, mul_assoc, inv_mul_cancel, mul_one]
        rw [h3]
        exact neg_one_mem_Ohat d
  -- every orbit has cardinality `w_x = |Γ_x| / |Γ_x ∩ {±1}|`
  have horb : ∀ q : nbrSet d ℓ c c',
      Nat.card ↥(MulAction.orbit ↥(Gam d.Ohat (Quotient.out c)) q) = wx d.Ohat (Quotient.out c) := by
    intro q
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥(Gam d.Ohat (Quotient.out c)) q),
      hstab q]
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Gam d.Ohat (Quotient.out c) ⊓ pmOne).subgroupOf (Gam d.Ohat (Quotient.out c)))
    have hK : Nat.card ↥((Gam d.Ohat (Quotient.out c) ⊓ pmOne).subgroupOf
        (Gam d.Ohat (Quotient.out c))) = Nat.card ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hpos : 0 < Nat.card ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne) :=
      Nat.card_pos (α := ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne))
    show Nat.card (↥(Gam d.Ohat (Quotient.out c)) ⧸
        (Gam d.Ohat (Quotient.out c) ⊓ pmOne).subgroupOf (Gam d.Ohat (Quotient.out c))) =
      Nat.card (Gam d.Ohat (Quotient.out c)) /
        Nat.card ↥(Gam d.Ohat (Quotient.out c) ⊓ pmOne)
    refine (Nat.div_eq_of_eq_mul_right hpos ?_).symm
    rw [← hK]
    exact hcard.trans (by ring)
  -- sum over the orbits
  classical
  letI : Fintype (MulAction.orbitRel.Quotient ↥(Gam d.Ohat (Quotient.out c)) (nbrSet d ℓ c c')) :=
    Fintype.ofFinite _
  haveI : ∀ ω : MulAction.orbitRel.Quotient ↥(Gam d.Ohat (Quotient.out c)) (nbrSet d ℓ c c'),
      Finite ↥(MulAction.orbit ↥(Gam d.Ohat (Quotient.out c)) ω.out) :=
    fun ω => Set.finite_coe_iff.mpr ((Set.toFinite _).subset (Set.subset_univ _))
  have hsum : Nat.card (nbrSet d ℓ c c') =
      ∑ ω : MulAction.orbitRel.Quotient ↥(Gam d.Ohat (Quotient.out c)) (nbrSet d ℓ c c'),
        Nat.card ↥(MulAction.orbit ↥(Gam d.Ohat (Quotient.out c)) ω.out) := by
    rw [Nat.card_congr
      (MulAction.selfEquivSigmaOrbits ↥(Gam d.Ohat (Quotient.out c)) (nbrSet d ℓ c c'))]
    exact Nat.card_sigma
  rw [hsum, Finset.sum_congr rfl (fun ω _ => horb ω.out), Finset.sum_const, nsmul_eq_mul]
  exact dvd_mul_left _ _

end Main

end Langlandscape.StabFree.Orbit
