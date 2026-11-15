/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.LevelRaising
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Tests for S03 LevelRaising — S03-L10

Tex label: `prop:s03-LRdef`. Shape test `B₁₁`, `q = 2`: `T₂ = −2` on `ℤ[X]⁰`, so
`αα† = [[3, 2], [2, 3]]` with determinant `5`; plus a non-vacuous instance of the abstract
statement (one vertex, three edges, all weights `1`: the `q = 2` shape).
-/

namespace LanglandscapeTests.S03.LevelRaising

open Langlandscape.Graph

/-- `prop:s03-LRdef` (`s03-LRdef`): the `B₁₁`, `q = 2` shape: entries `q+1 = 3`, `−T₂ = 2`,
`det = (q+1)² − T₂² = 5`. -/
theorem B11_q2_det : (!![(3 : ℤ), 2; 2, 3]).det = 5 := by
  rw [Matrix.det_fin_two_of]; norm_num

/-- `prop:s03-LRdef` (`s03-LRdef`): `(q+1)² − T_q² = 5` for `q = 2`, `T_q = −2`. -/
theorem B11_q2_det_formula : ((2 : ℤ) + 1) ^ 2 - (-2) ^ 2 = 5 := by norm_num

/-- `prop:s03-LRdef` (`s03-LRdef`): the abstract theorem applies to the one-vertex shape. -/
theorem alpha_alphaDagger_unit (v : (Unit →₀ ℤ) × (Unit →₀ ℤ)) :
    alphaMap (fun _ : Fin 3 => ()) (fun _ => ())
        (alphaDagger (fun _ : Fin 3 => ()) (fun _ => ()) (fun _ => 1) (fun _ => 1) v) =
      (((2:ℤ) + 1) • v.1 - levelT (fun _ : Fin 3 => ()) (fun _ => ()) (fun _ => 1) v.2,
       ((2:ℤ) + 1) • v.2 - levelT (fun _ : Fin 3 => ()) (fun _ => ()) (fun _ => 1) v.1) := by
  refine alpha_alphaDagger_eq _ _ _ _ 2 ?_ ?_ ?_ v
  · intro x; simp <;> norm_num
  · intro x; simp <;> norm_num
  · intro x; rfl

end LanglandscapeTests.S03.LevelRaising
