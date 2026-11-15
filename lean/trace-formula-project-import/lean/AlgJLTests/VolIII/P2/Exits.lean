import AlgJL.VolIII.P2.ClassSet
import AlgJL.VolIII.P2.Compact
import AlgJL.VolIII.P2.Instances

/-!
# Exit witnesses and supports of Q2 (R2d; `registry/exits.yaml`, CR-Q2-EXITS)

Exits `III.qcls.thm:class-set-finite` (47), `III.qcls.thm:quotient-compact` (60) and
`III.qcls.ex:eichler-mass-instance-d11` (62). Witnesses are closed theorems (no leading binders) whose value applies the
exit; supports certify that the witness data are not degenerate (`check_exit_support`: closed, not trivial, mention a
witness datum, no restatement of a witness, no GL2TFTests datum of another exit).

Data: `orderO11` (Pizer's maximal order `O₁₁ ⊆ (−1, −11)_ℚ`, the datum of 47 and 62) and `bD11 = −11` (the datum
of 60: the definite algebra `(−1, −11)_ℚ`). W3 (L4T): no local `sorry`; the witnesses inherit the status of the items.
Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat

/-- Datum of exits 47 and 62: Pizer's order `O₁₁ = ℤ(1+j)/2 + ℤ(i+k)/2 + ℤj + ℤk` of `(−1, −11)_ℚ`. -/
noncomputable def orderO11 : QOrder (-1) (-11) := pizerOrderI (-11) (by norm_num)

/-- Datum of exit 60: `b = −11`, so that `B = (−1, bD11)_ℚ` is the definite algebra ramified at `11`. -/
def bD11 : ℤ := -11

/-! ## Exit 47 -/

/-- **Witness** of exit 47: `X(O₁₁)` is finite. -/
theorem class_set_finite_witness : Finite (classSet orderO11) :=
  classSet_finite (by norm_num) (by norm_num) orderO11

/-- **Support** of exit 47: `O₁₁` is not the standard order `ℤ⟨1, i, j, k⟩` (it contains `(1+j)/2`). -/
theorem orderO11_ne_standardOrder : orderO11.toSubalgebra ≠ (standardOrder (-1) (-11)).toSubalgebra := by
  intro h
  have hmem : (⟨1 / 2, 0, 1 / 2, 0⟩ : QuatAlg ℚ (-1) (-11)) ∈ orderO11.toSubalgebra :=
    Submodule.mem_toSubalgebra.mpr (Submodule.subset_span ⟨0, rfl⟩)
  rw [h] at hmem
  obtain ⟨⟨n, hn⟩, -, -, -⟩ := hmem
  have h2 : (2 : ℚ) * n = 1 := by
    have : ((1 / 2 : ℚ)) = n := hn
    linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- **Support** of exit 47: the class set of `O₁₁` has two elements (so it is finite and not a single point). -/
theorem classSet_orderO11_card : Nat.card (classSet orderO11) = 2 :=
  eichler_mass_instance_d11.2.2.1.1

/-! ## Exit 60 -/

/-- **Witness** of exit 60: for `(a, b) = (−1, −11)`, `Γ_B` is discrete in `B_𝔸^1` and `Γ_B \ B_𝔸^1` is compact. -/
theorem quotient_compact_witness :
    DiscreteTopology (adelicDiagonal (-1) bD11) ∧
      CompactSpace (MulAction.orbitRel.Quotient (adelicDiagonal (-1) bD11) (adelicNormOne (-1) bD11)) :=
  quotient_compact (by norm_num) (by norm_num [bD11])

/-- Proof helper: the units `1 + n i` of `(−1, b)_ℚ` (`nrd = 1 + n²`). -/
noncomputable def unitOnePlusNI (b : ℤ) (n : ℕ) : (QuatAlg ℚ (-1) b)ˣ where
  val := ⟨1, n, 0, 0⟩
  inv := ⟨1 / (1 + (n : ℚ) ^ 2), -n / (1 + (n : ℚ) ^ 2), 0, 0⟩
  val_inv := by
    have : (1 + (n : ℚ) ^ 2) ≠ 0 := by positivity
    rw [QuaternionAlgebra.mk_mul_mk]
    ext <;> simp <;> field_simp; ring
  inv_val := by
    have : (1 + (n : ℚ) ^ 2) ≠ 0 := by positivity
    rw [QuaternionAlgebra.mk_mul_mk]
    ext <;> simp <;> field_simp; ring

/-- **Support** of exit 60: `Γ_B` is infinite (the discrete group is not finite, so compactness of the quotient is not
compactness of `B_𝔸^1` up to a finite group). -/
theorem adelicDiagonal_d11_infinite : Infinite (adelicDiagonal (-1) bD11) := by
  have h1 := (diagonal_discrete (-1) bD11).1
  refine Infinite.of_injective (fun n : ℕ => (⟨⟨Units.map (adelicEmbed (-1) bD11).toMonoidHom (unitOnePlusNI bD11 n),
    h1 ⟨_, rfl⟩⟩, Subgroup.mem_subgroupOf.mpr ⟨_, rfl⟩⟩ : adelicDiagonal (-1) bD11)) ?_
  intro n m h
  have h' := congrArg (fun y : adelicDiagonal (-1) bD11 => QuaternionAlgebra.imI
    (show QuatAlg Adele (-1) bD11 from
      (((y : adelicNormOne (-1) bD11) : (AdelicQuat (-1) bD11)ˣ) : AdelicQuat (-1) bD11))) h
  have h2 : algebraMap ℚ Adele (n : ℚ) = algebraMap ℚ Adele (m : ℚ) := h'
  have h'' : ((n : ℚ)) = (m : ℚ) := (algebraMap ℚ Adele).injective h2
  exact_mod_cast h''

/-! ## Exit 62 -/

/-- **Support** of exit 62: the datum `O₁₁` is Pizer's order `pizerOrderI (−11)`. -/
theorem orderO11_eq_pizerOrderI : orderO11 = pizerOrderI (-11) (by norm_num) := rfl

/-- **Witness** of exit 62: exactly the closed conclusion of `III.qcls.ex:eichler-mass-instance-d11` (CR-Q2-EXITS-3: no datum, no
GL2TFTests constant in the statement). -/
theorem eichler_mass_instance_d11_witness :
    RamifiedExactly (-1) (-11) 11 ∧
    (IsMaximalOrder (pizerOrderI (-11) (by norm_num)) ∧ discriminant (pizerOrderI (-11) (by norm_num)) = 121) ∧
    (Nat.card (classSet (pizerOrderI (-11) (by norm_num))) = 2 ∧
      Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) 1) = 4 ∧
      Nat.card (unitGroup (pizerOrderI (-11) (by norm_num))) = 4 ∧
      ∃ x : (BHat (-1) (-11))ˣ,
        (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
            (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) x : classSet (pizerOrderI (-11) (by norm_num))) ≠
          DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
            (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) 1 ∧
        Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) x) = 6) ∧
    mass (pizerOrderI (-11) (by norm_num)) = 5 / 12 ∧
    ∀ h : IsMaximalOrder (pizerOrderI (-11) (by norm_num)),
      Hyp.EichlerMass (-1) (-11) 11 ⟨pizerOrderI (-11) (by norm_num), h⟩ :=
  eichler_mass_instance_d11

/-- **Support** of exit 62 (item 61): the Hurwitz instance `D = 2`. -/
theorem hurwitz_order_mass_witness :
    IsMaximalOrder hurwitzOrder ∧ discriminant hurwitzOrder = 4 ∧
    Nat.card (classSet hurwitzOrder) = 1 ∧ Nat.card (unitGroup hurwitzOrder) = 24 ∧
    mass hurwitzOrder = 1 / 24 ∧
    ∀ h : IsMaximalOrder hurwitzOrder, Hyp.EichlerMass (-1) (-1) 2 ⟨hurwitzOrder, h⟩ :=
  hurwitz_order_mass

/-- **Support** of exit 62 (item 63): level structures of levels `2`, `3` on `O₁₁` exist, with masses `5/4`, `5/3`. -/
theorem eichler_order_d11_levels_witness :
    (∃ φ : LevelStructure orderO11 2, mass (eichlerOrder φ) = 5 / 4) ∧
    (∃ φ : LevelStructure orderO11 3, mass (eichlerOrder φ) = 5 / 3) :=
  eichler_order_d11_levels

end GL2TFTests
