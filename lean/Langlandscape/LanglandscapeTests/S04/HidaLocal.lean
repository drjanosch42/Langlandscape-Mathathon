/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.HidaLocal

/-! Non-vacuity tests for `Langlandscape.Local.HidaLocal` (S04-L6, `lem:s04-hida`(a),(b)) at `p = 5`, `s = 1`. -/

set_option autoImplicit false

namespace LanglandscapeTests.S04.HidaLocal

open Langlandscape.Local Pointwise

/-- `5` is prime (test data, `s04-hida`). -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `lem:s04-hida` (`s04-hida`), test data: `1 + 5` is a unit of `ℤ_[5]`. -/
theorem isUnit_six : IsUnit ((1 : ℤ_[5]) + ((5 : ℕ) : ℤ_[5])) := by
  rw [isUnit_iff_not_dvd]
  intro h
  have h2 : ((5 : ℕ) : ℤ_[5]) ∣ 1 := (dvd_add_left (dvd_refl _)).1 h
  exact (isUnit_iff_not_dvd ((5 : ℕ) : ℤ_[5])).1 (isUnit_of_dvd_one h2) (dvd_refl _)

/-- `lem:s04-hida` (`s04-hida`), test data: `diag(1, 6) ∈ GL₂(ℚ_5)`. -/
noncomputable def g6 : GL (Fin 2) ℚ_[5] := diagGL 1 (intUnit isUnit_six.unit)

/-- `lem:s04-hida`(c) (`s04-hida`), test: `diag(1, 6) ∈ Kpp 5 1` (`6 ≡ 1 mod 5`, `c = 0`). -/
theorem g6_mem_Kpp : g6 ∈ Kpp 5 1 := by
  refine mem_Kpp_iff.2 ⟨(one_diag_mem_K1_iff _ 1).2 ?_, one_diag_mem_K0 _ (1 + 1)⟩
  rw [IsUnit.unit_spec, add_sub_cancel_left]
  exact ⟨1, by rw [pow_one, mul_one]⟩

/-- `lem:s04-hida`(c) (`s04-hida`), test: `diag(1, 6) ∉ K1 5 2` (`6 ≢ 1 mod 25`), so `K1 5 2 < Kpp 5 1`. -/
theorem g6_not_mem_K1_two : g6 ∉ K1 5 2 := by
  intro h
  have h1 := (mem_K1_iff.1 h).2
  have e : (Units.val g6) 1 1 - 1 = ((5 : ℕ) : ℚ_[5]) := by
    show ((intUnit isUnit_six.unit : ℚ_[5]ˣ) : ℚ_[5]) - 1 = ((5 : ℕ) : ℚ_[5])
    rw [coe_intUnit, IsUnit.unit_spec, PadicInt.coe_add, PadicInt.coe_one, PadicInt.coe_natCast,
      add_sub_cancel_left]
  rw [e, Padic.norm_p, zpow_neg, zpow_natCast] at h1
  norm_num at h1

/-- `lem:s04-hida`(c) (`s04-hida`), test: `Kpp 5 1 ≠ K1 5 2`. -/
theorem Kpp_ne_K1_two : Kpp 5 1 ≠ K1 5 2 := fun h => g6_not_mem_K1_two (h ▸ g6_mem_Kpp)

/-- `lem:s04-hida` (`s04-hida`), test: `[K1 5 1 : Kpp 5 1] = 5`. -/
theorem relIndex_Kpp_five : (Kpp 5 1).relIndex (K1 5 1) = 5 := relIndex_Kpp le_rfl

/-- `lem:s04-hida`(a) (`s04-hida`), test: the double coset `Kpp 5 1 ϖ Kpp 5 1` is `⋃ j, ϖ_j Kpp 5 1`. -/
theorem Kpp_mul_varpi_mul_Kpp_five :
    (Kpp 5 1 : Set (GL (Fin 2) ℚ_[5])) * {varpiDiag 5} * Kpp 5 1 =
      ⋃ j : Fin 5, varpi 5 j • (Kpp 5 1 : Set (GL (Fin 2) ℚ_[5])) :=
  Kpp_mul_varpi_mul_Kpp le_rfl

/-- `lem:s04-hida`(b) (`s04-hida`), test: for `u = diag(1, 6) ∈ K1 5 1` and `j = 2` there are `i` and
`u_j ∈ Kpp 5 1` with `u ϖ_j = ϖ_i u_j`. -/
theorem exists_varpi_conj_five :
    ∃ i : Fin 5, ∃ uj ∈ Kpp 5 1, g6 * varpi 5 2 = varpi 5 i * uj :=
  exists_varpi_conj le_rfl g6 (Kpp_le_K1 1 g6_mem_Kpp) 2

/-- `lem:s04-hida`(c) (`s04-hida`), test: the class of `diag(1, 6)` in `Kpp 5 1 / K1 5 2` maps to
`6 mod 25`, a non-trivial element of `ker((ℤ/25)ˣ → (ℤ/5)ˣ)`. -/
theorem kppQuotEquiv_g6_ne_one :
    kppQuotEquiv (p := 5) (s := 1) le_rfl
      ((⟨g6, g6_mem_Kpp⟩ : Kpp 5 1) : Kpp 5 1 ⧸ (K1 5 (1 + 1)).subgroupOf (Kpp 5 1)) ≠ 1 := by
  intro h
  apply g6_not_mem_K1_two
  have h' : PadicInt.toZModPow (1 + 1) (entZ g6 (Kpp_le_GL2Zl 1 g6_mem_Kpp) 1 1) = 1 := by
    have h0 := congrArg Units.val (congrArg Subtype.val h)
    exact (kppQuotEquiv_mk le_rfl ⟨g6, g6_mem_Kpp⟩).symm.trans h0
  have hk : (⟨g6, g6_mem_Kpp⟩ : Kpp 5 1) ∈ (dModHom 5 1).toHomUnits.ker :=
    MonoidHom.mem_ker.2 (Units.ext (by rw [MonoidHom.coe_toHomUnits, dModHom_apply]; exact h'))
  rw [ker_dModHom, Subgroup.mem_subgroupOf] at hk
  exact hk

end LanglandscapeTests.S04.HidaLocal
