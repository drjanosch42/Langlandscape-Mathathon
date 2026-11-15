/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.ImportDictionary

/-!
# Hypothesis `BrandtStabFree`: off-diagonal Brandt entries are divisible by the weight (S03-L8)

`mathematics/chapters/s03/2-eisenstein.tex`, `lem:s03-stabfree` (step (1) of the proof of `prop:s03-phieis`).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Statement, at level `U = Ô^×` (the case `M = 1` of the tex, `B = B_q`, `D = q` prime): for a prime `ℓ ∤ D` and
classes `e ≠ e'` in `X_B(Ô^×)`, `w_e ∣ B(ℓ)_{e e'}`, where `B(ℓ)` is the import's Brandt matrix
(`B(ℓ)_{cc'} = (T_ℓ 1_{c'})(c)`, `Brandt.Tl_matrix_eq_brandtMatrix`) and `w_e = Quat.wx Ô^× (e.out)`.

Reason (tex, `lem:s03-stabfree`, proof steps (i)–(vii)): `Γ_x / {±1}` (order `w_x`) acts on the `ℓ + 1`
neighbours `hU` of `x` (`lem:s03-nbr`), preserving classes. If `γ ∈ Γ_x`, `γ ≠ ±1`, fixes a neighbour `hU`, then
`A = ℤ[γ]` is `ℤ[i]` or `ℤ[ω]` (Euclidean, hence a PID), and there is `π ∈ ℤ[γ]` with `Nrd π = ℓ` and `hU = π x U`;
so `[h] = [x]`. Hence the action on the neighbours in a class `e' ≠ e` is free and `w_e ∣ B(e, e')`. The proof is
elementary (lattices over `ℤ_ℓ[γ]`, no cited result), valid for every prime `q` and every prime `ℓ ∤ q`, including
`ℓ ∈ {2, 3}`.

Status: tex *proved* (`lem:s03-stabfree`, elementary: `π ∈ ℤ[γ]`, `ℤ[γ]` Euclidean); *formalized*: discharged by
`Hyp.brandtStabFree_holds` (`Hyp/BrandtStabFreeDischarge.lean`, 2026-11-15).
Cross-reference (not needed for the proof): Ri90 Thm 3.12. The premise `D` prime is not used by the tex proof.
Discharge plan: post-stage-04 (needs the neighbour/lattice description `lem:s03-nbr` of the import's Brandt matrix
and the arithmetic of `ℤ[i]`, `ℤ[ω]` inside `B`). The statement is true (the tex proof), hence non-vacuous as a
premise.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat

/-- `lem:s03-stabfree` (`s03-stabfree`), step (1) of `prop:s03-phieis`: for `D` prime, `ℓ` prime with `ℓ ∤ D`
and `e ≠ e'` in `X_B(Ô^×)`, the weight `w_e` divides the Brandt entry `B(ℓ)_{e e'}`. Status: tex *proved*
(`lem:s03-stabfree`, elementary: `π ∈ ℤ[γ]`, `ℤ[γ]` Euclidean); not formalized (post-stage-04). Cross-reference:
Ri90 Thm 3.12. -/
def BrandtStabFree (d : DefiniteData) (ℓ : ℕ) : Prop :=
  ℓ.Prime → ¬ ℓ ∣ d.D → d.D.Prime → ∀ c c' : XB d.Ohat, c ≠ c' →
    wx d.Ohat (Quotient.out c) ∣ GL2TF.Quat.brandtMatrix d.O.1 ℓ c c'

end Langlandscape.Hyp
