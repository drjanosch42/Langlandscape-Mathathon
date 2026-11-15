import AlgJL.VolIII.P2.Instances

/-!
# Tests for `GL2TF.VolIII.P2.Instances`

Named test declarations for the orders of Q2 items 61–64 (`hurwitzOrder`, `pizerOrderI`, `pizerOrderII`) and the
**registry instances** of `Hyp.EichlerMass` (`tex/shared/hypotheses.tex`, `instdecl`): `eichlerMass_d11` and
`eichlerMass_d2`, closed and fully applied. They are derived from items 62 and 61 (proved in W3 by L4T from the
upstream items; they inherit the status of those items).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat

/-- `(1+i+j+k)/2 ∈ O_H`. -/
theorem hurwitzOrder_mem_half : (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : QuatAlg ℚ (-1) (-1)) ∈ hurwitzOrder.toSubalgebra :=
  Submodule.mem_toSubalgebra.mpr (Submodule.subset_span ⟨0, rfl⟩)

/-- `(1+j)/2 ∈ O₁₁`. -/
theorem pizerOrderI_d11_mem_half :
    (⟨1 / 2, 0, 1 / 2, 0⟩ : QuatAlg ℚ (-1) (-11)) ∈ (pizerOrderI (-11) (by norm_num)).toSubalgebra :=
  Submodule.mem_toSubalgebra.mpr (Submodule.subset_span ⟨0, rfl⟩)

/-- `(i+2j+k)/4 ∈ O^(5) ⊆ (−2, −5)_ℚ`. -/
theorem pizerOrderII_d5_mem_quarter :
    (⟨0, 1 / 4, 1 / 2, 1 / 4⟩ : QuatAlg ℚ (-2) (-5)) ∈ (pizerOrderII (-5) (by norm_num)).toSubalgebra :=
  Submodule.mem_toSubalgebra.mpr (Submodule.subset_span ⟨1, rfl⟩)

/-- **Registry instance** of `Hyp.EichlerMass` (exit `III.qcls.ex:eichler-mass-instance-d11`):
`Hyp.EichlerMass (−1) (−11) 11 O₁₁`, closed and fully applied. -/
theorem eichlerMass_d11 :
    Hyp.EichlerMass (-1) (-11) 11 ⟨pizerOrderI (-11) (by norm_num), eichler_mass_instance_d11.2.1.1⟩ :=
  eichler_mass_instance_d11.2.2.2.2 _

/-- **Support** of the `D = 2` registry instance (G1 finding L-1): the antecedent `RamifiedExactly (−1) (−1) 2` holds (item 15). -/
theorem hurwitz_ramifiedExactly : RamifiedExactly (-1) (-1) 2 := pizer_algebras.1

/-- **Registry instance** of `Hyp.EichlerMass` (`III.qcls.ex:hurwitz-order-mass`): `Hyp.EichlerMass (−1) (−1) 2 O_H`,
closed and fully applied. -/
theorem eichlerMass_d2 : Hyp.EichlerMass (-1) (-1) 2 ⟨hurwitzOrder, hurwitz_order_mass.1⟩ :=
  hurwitz_order_mass.2.2.2.2.2 _

end GL2TFTests
