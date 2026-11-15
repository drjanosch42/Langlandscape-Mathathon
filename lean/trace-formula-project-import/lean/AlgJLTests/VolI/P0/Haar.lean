import AlgJL.VolI.P0.Haar

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P0/Haar.lean` at commit 84818d0. Dropped tests of stripped declarations (18): `vol_cartan_cell_haarLocal`, `matAddHaar_detDensityHaar_eq`, `haarReal_haarOrthogonal_eq`, `modularCharBorel_borelCoord`, `unipotentMeasure_torusMeasure_eq`, `haarAdelic_eq`, `haarNormOne_eq`, `muStd`, `muStd_haar`, `muStd_K`, `adeleHaar_isAddHaar`, `ideleHaar_isHaar`, `iwasawa_integration_standard`, `haarFinAdelic_one_scaled_factor`, and the measure witnesses `maxCompactAdelic_compactSpace`, `kStd`, `kStd_haar`, `kStd_prob`. Added (fork): `borelCoord_zero_one_one`. -/


/-!
# Tests for `GL2TF.VolI.P0.Haar`

Non-vacuity (PLAN.md §2.3): the corollary `vol_cartan_cell` applies to the normalized Haar measure (unconditional
since M1-SC-01).
-/

open GL2TF GL2TF.Local Matrix.GeneralLinearGroup

namespace GL2TFTests

/-! ### Borel coordinates (fork: the only `I.haar` definition kept) -/

/-- `borelCoord (0, 1, 1) = 1`. -/
theorem borelCoord_zero_one_one :
    ((borelCoord ((0 : ℚ), (1 : ℚˣ), (1 : ℚˣ)) : borel ℚ) : GL (Fin 2) ℚ) = 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [borelCoord, diagElt]

end GL2TFTests
