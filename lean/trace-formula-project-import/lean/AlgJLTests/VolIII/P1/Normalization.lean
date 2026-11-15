import AlgJL.VolIII.P1.Normalization

/-!
# Tests for `GL2TF.VolIII.P1.Normalization`

Kernel-checked values (`decide +kernel`; no `native_decide`, plan trap 11) of every definition of the file, including
the golden values of plan items 41 and 42 (P04 tests 1 and 2), which the statements of `JLFormula` re-prove.
-/

namespace GL2TFTests

open GL2TF.Explicit

/-- `w(−3) = 6`, `w(−4) = 4`, `w(−23) = 2`, `w(5) = 2`. -/
theorem unitNumber_values :
    unitNumber (-3) = 6 ∧ unitNumber (-4) = 4 ∧ unitNumber (-23) = 2 ∧ unitNumber 5 = 2 := by
  decide +kernel

/-- `h_w(−3) = 1/3`, `h_w(−4) = 1/2`, `h_w(−23) = 3`. -/
theorem weightedClassNumber_values :
    weightedClassNumber (-3) = 1 / 3 ∧ weightedClassNumber (-4) = 1 / 2 ∧ weightedClassNumber (-23) = 3 := by
  decide +kernel

/-- `χ_{−3}(2) = −1`, `χ_{−7}(2) = 1`, `χ_{−4}(2) = 0`, `χ_{−3}(7) = 1`, `χ_{−3}(5) = −1`, `χ_{−12}(3) = 0`. -/
theorem kroneckerPrime_values :
    kroneckerPrime (-3) 2 = -1 ∧ kroneckerPrime (-7) 2 = 1 ∧ kroneckerPrime (-4) 2 = 0 ∧
      kroneckerPrime (-3) 7 = 1 ∧ kroneckerPrime (-3) 5 = -1 ∧ kroneckerPrime (-12) 3 = 0 := by
  decide +kernel

/-- `2 ∣ cond(−16)` (`−16 = 4·(−4)`), `2 ∤ cond(−4)` (`−1` is not a discriminant), `3 ∣ cond(−27)`, `2 ∤ cond(−12)`. -/
theorem dividesConductor_values :
    dividesConductor 2 (-16) = true ∧ dividesConductor 2 (-4) = false ∧
      dividesConductor 3 (-27) = true ∧ dividesConductor 2 (-12) = true ∧ dividesConductor 3 (-12) = false := by
  decide +kernel

/-- `e_2(−16) = 1` (conductor), `e_2(−4) = 0`, `e_2(−3) = −1`, `e_7(−3) = 1`. -/
theorem eichlerSymbol_values :
    eichlerSymbol 2 (-16) = 1 ∧ eichlerSymbol 2 (-4) = 0 ∧ eichlerSymbol 2 (-3) = -1 ∧ eichlerSymbol 7 (-3) = 1 := by
  decide +kernel

/-- `m^D_2(−3) = 2`, `m^D_2(−16) = 0`, `m^D_7(−3) = 0`. -/
theorem localFactorRamified_values :
    localFactorRamified 2 (-3) = 2 ∧ localFactorRamified 2 (-16) = 0 ∧ localFactorRamified 7 (-3) = 0 := by
  decide +kernel

/-- `m^{(1)}_2(−3) = 0`, `m^{(1)}_2(−16) = 2`, `m^{(1)}_{11}(−7) = 2`. -/
theorem localFactorEichler_values :
    localFactorEichler 2 (-3) = 0 ∧ localFactorEichler 2 (-16) = 2 ∧ localFactorEichler 11 (-7) = 2 := by
  decide +kernel

/-- `μ_2(0, 1, 4) = 1 + χ_{−16}(2) = 1`, `μ_2(0, 2, 4) = 3`, `μ_3(−1, 1, 7) = 1 + χ_{−27}(3) = 1`, `μ_0 = 0`. -/
theorem cohenMu_values :
    cohenMu 2 0 1 4 = 1 ∧ cohenMu 2 0 2 4 = 3 ∧ cohenMu 3 (-1) 1 7 = 1 ∧ cohenMu 0 0 1 1 = 0 := by
  decide +kernel

/-- `c_8(0) = 4`, `c_8(1) = 2`, `c_6(3) = 4`, `c_0(0) = 0`. -/
theorem boundaryDivisorSum_values :
    boundaryDivisorSum 8 0 = 4 ∧ boundaryDivisorSum 8 1 = 2 ∧ boundaryDivisorSum 6 3 = 4 ∧
      boundaryDivisorSum 0 0 = 0 := by
  decide +kernel

/-- `Ẽis(1, 2, 2) = 3` and `Ẽis(11, 2, 2) = 6`. -/
theorem eisensteinCorrected_values : eisensteinCorrected 1 2 2 = 3 ∧ eisensteinCorrected 11 2 2 = 6 := by
  decide +kernel

/-- `Eis(1, 2, 2) = 0` and `Eis(1, 4, 2) = 9`. -/
theorem eisensteinExpr_values : eisensteinExpr 1 2 2 = 0 ∧ eisensteinExpr 1 4 2 = 9 := by
  decide +kernel

/-- `A₁(11, 2, 4) = 1`, `A₁(11, 2, 2) = 0`. -/
theorem cohenA1_values : cohenA1 11 2 4 = 1 ∧ cohenA1 11 2 2 = 0 := by
  decide +kernel

/-- `A₂(11, 2, 2) = −3`. -/
theorem cohenA2_value : cohenA2 11 2 2 = -3 := by
  decide +kernel

/-- `A₃(11, 2, 2) = −2`. -/
theorem cohenA3_value : cohenA3 11 2 2 = -2 := by
  decide +kernel

/-- `A₄(2, 2) = 3`, `A₄(4, 2) = 0`. -/
theorem cohenA4_values : cohenA4 2 2 = 3 ∧ cohenA4 4 2 = 0 := by
  decide +kernel

/-- Golden values (plan item 42, P04 test 1): `T^C(11, 2, 2) = −2`, `T^C(11, 2, 3) = −1`, `T^C(1, 12, 2) = −24`. -/
theorem cohenTraceExpr_golden :
    cohenTraceExpr 11 2 2 = -2 ∧ cohenTraceExpr 11 2 3 = -1 ∧ cohenTraceExpr 1 12 2 = -24 := by
  decide +kernel

/-- `A₂^E(2, 1; 1) = −7/12` (`t ∈ {−1, 0, 1}`, `Δ = −3, −4, −3`: `−(1/3 + 1/2 + 1/3)/2`). -/
theorem eichlerElliptic_value : eichlerElliptic 2 1 (fun _ => 1) = -7 / 12 := by
  decide +kernel

/-- Golden values (plan item 41, P04 test 2): `Λ^{ES}(1, 2, n; 1) = 1, 3, 4` and `Λ^{ES}(11, 2, n; m^{(1)}_{11}) = −2, 4, 2`
for `n = 1, 2, 3`. -/
theorem lefschetzES_golden :
    lefschetzES 1 2 1 (fun _ => 1) = 1 ∧ lefschetzES 1 2 2 (fun _ => 1) = 3 ∧ lefschetzES 1 2 3 (fun _ => 1) = 4 ∧
      lefschetzES 11 2 1 (fun Δ => (localFactorEichler 11 Δ : ℚ)) = -2 ∧
      lefschetzES 11 2 2 (fun Δ => (localFactorEichler 11 Δ : ℚ)) = 4 ∧
      lefschetzES 11 2 3 (fun Δ => (localFactorEichler 11 Δ : ℚ)) = 2 := by
  decide +kernel

/-- Golden values (plan item 41): `E^𝔹(11, 1, 2, n; 1) = 2, 1, 3` for `n = 1, 2, 3`. -/
theorem eichlerB_golden :
    eichlerB 11 1 2 1 (fun _ => 1) = 2 ∧ eichlerB 11 1 2 2 (fun _ => 1) = 1 ∧ eichlerB 11 1 2 3 (fun _ => 1) = 3 := by
  decide +kernel

end GL2TFTests
