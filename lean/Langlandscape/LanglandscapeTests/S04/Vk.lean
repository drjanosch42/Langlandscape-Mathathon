/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.UpCoeff

/-!
# Tests for `Langlandscape.Quat.Vk` and `Langlandscape.Brandt.UpCoeff` (S04-L15b)

* the action `P ↦ P((X,Y) A)` is a left action (`eq:s01-Vk`);
* `ev` of `ϖ_j · P` is `ev P` (`def:s04-Pk`);
* the signatures of `UpV` and `evV_UpV_eq_Up`.
-/

namespace Langlandscape.Quat.Tests.Vk

open Langlandscape.Quat Langlandscape.Brandt MvPolynomial

/-- `eq:s01-Vk` (`s01-Vk`, `s04-L15b`), test: `(A B) · P = A · (B · P)` on `V_k`. -/
theorem symAct_mul_test {R : Type*} [CommRing R] (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) R)
    (P : homogeneousSubmodule (Fin 2) R n) :
    symAct R n (A * B) P = symAct R n A (symAct R n B P) := by
  exact congrArg (fun T => T P) (map_mul (symAct R n) A B)

/-- `eq:s01-Vk` (`s01-Vk`, `s04-L15b`), test: the identity matrix acts trivially. -/
theorem symAct_one_test {R : Type*} [CommRing R] (n : ℕ) (P : homogeneousSubmodule (Fin 2) R n) :
    symAct R n 1 P = P := by
  exact congrArg (fun T => T P) (map_one (symAct R n))

/-- `def:s04-Pk` (`s04-Pk`, `s04-L15b`), test: `ev (A · P) = P(c, d)` for `A = (a b; c d)`. -/
theorem evV_symAct_test {R : Type*} [CommRing R] (k : ℕ) (a b c d : R) (P : Vk R k) :
    evV R k (symAct R (k - 2) !![a, b; c, d] P) =
      MvPolynomial.aeval (![c, d] : Fin 2 → R) (P : MvPolynomial (Fin 2) R) := by
  have h : (fun i => (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) 1 i) = (![c, d] : Fin 2 → R) := by
    funext i
    fin_cases i <;> rfl
  rw [evV_symAct, h]

/-- `def:s04-Pk` (`s04-Pk`, `s04-L15b`), test: `ev (ϖ_j · P) = ev P` for `ϖ_j = (p j; 0 1)`. -/
theorem evV_varpi_test {R : Type*} [CommRing R] (k : ℕ) (a b : R) (P : Vk R k) :
    evV R k (symAct R (k - 2) !![a, b; 0, 1] P) = evV R k P :=
  evV_symAct_of_row k _ rfl rfl P

end Langlandscape.Quat.Tests.Vk
