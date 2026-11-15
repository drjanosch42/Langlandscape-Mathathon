/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import AlgJL.VolIII.P2.MassDefs
import AlgJL.VolIII.P2.Ramification

/-!
# Facade for the definite quaternion data (S01-L1)

Thin layer over the import (`GL2TF.Quat.*`, package `GL2TF`) with the stage-01 names
(`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-B`, `def:s01-classset`, `prop:s01-finite`,
`thm:s01-mass`).  Everything downstream of stage 01 reads only this file for the following vocabulary.

* `DefiniteData` : bundle `(a, b, D, O, hD)`: the definite algebra `B = ℍ[ℚ,a,0,b]` (`a, b < 0`), ramified exactly at
  the primes dividing `D`, with a maximal order `O`.
* `globalUnits a b` : `B^×` inside `B̂^×` (the image of `Units.map finEmbed`).
* `XB U` : `B^× \ B̂^× / U`; `Gam U x` : the stabiliser `Γ_x(U)`.
* `pmOne` : `{±1} ⊆ B^×`; `wx U x = |Γ_x / (Γ_x ∩ {±1})|`.
* `massFull U` : `∑_{c ∈ X(U)} 1/|Γ_{x_c}|` (full stabiliser; the factor 2 relative to `w_x` appears iff `-1 ∈ U`).

Status: *formalized* (definitions; `XB_finite` reuses `GL2TF.Quat.classSet_finite_of_open`).
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

/-! ### Re-exports of import names -/

/-- Re-export: the quaternion algebra `ℍ[R,a,0,b]` of the import. -/
abbrev QuatAlg (R : Type*) [CommRing R] (a b : ℤ) : Type _ := GL2TF.Quat.QuatAlg R a b

/-- Re-export: the finite adelic quaternion algebra `B̂`. -/
abbrev BHat (a b : ℤ) : Type := GL2TF.Quat.BHat a b

/-- Re-export: the diagonal embedding `B → B̂` (`def:s01-B`). -/
noncomputable abbrev finEmbed (a b : ℤ) : GL2TF.Quat.QuatAlg ℚ a b →+* GL2TF.Quat.BHat a b :=
  GL2TF.Quat.finEmbed a b

/-- Re-export: `Ô^×` for an order `O` (`def:s01-B`). -/
noncomputable abbrev orderCompletionUnits {a b : ℤ} (O : QOrder a b) : Subgroup (BHat a b)ˣ :=
  GL2TF.Quat.orderCompletionUnits O

/-- Re-export: "`B` is ramified exactly at the primes dividing `D`" (includes `a, b < 0`, `D` squarefree). -/
abbrev RamifiedExactly (a b : ℤ) (D : ℕ) : Prop := GL2TF.Quat.RamifiedExactly a b D

/-- Re-export: maximal orders of `ℍ[ℚ,a,0,b]`. -/
abbrev MaxOrder (a b : ℤ) : Type := GL2TF.Quat.MaxOrder a b

/-! ### The bundle -/

/-- `def:s01-B`: definite quaternion data. `B = ℍ[ℚ,a,0,b]` with `a, b < 0`, ramified exactly at the primes dividing
`D` (squarefree), together with a maximal order `O` (so `Ô^× = orderCompletionUnits d.O.1`). -/
structure DefiniteData where
  /-- first Hilbert-symbol parameter -/
  a : ℤ
  /-- second Hilbert-symbol parameter -/
  b : ℤ
  /-- the discriminant (product of the ramified primes) -/
  D : ℕ
  /-- a maximal order -/
  O : MaxOrder a b
  /-- `B` is ramified exactly at `D` -/
  hD : RamifiedExactly a b D

namespace DefiniteData

variable (d : DefiniteData)

/-- `a < 0` (`def:s01-B`). -/
theorem ha : d.a < 0 := d.hD.1

/-- `b < 0` (`def:s01-B`). -/
theorem hb : d.b < 0 := d.hD.2.1

/-- `D` is squarefree (`def:s01-B`). -/
theorem squarefree : Squarefree d.D := d.hD.2.2.1

/-- The quaternion algebra `B_D` of the data (over `ℚ`). -/
abbrev B : Type := GL2TF.Quat.QuatAlg ℚ d.a d.b

/-- The finite adelic algebra `B̂`. -/
abbrev Bhat : Type := GL2TF.Quat.BHat d.a d.b

/-- `Ô^×` for the chosen maximal order, as a subgroup of `B̂^×`. -/
noncomputable abbrev Ohat : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ :=
  GL2TF.Quat.orderCompletionUnits d.O.1

/-- `Ô^×` is open in `B̂^×` (`def:s01-B`, `s01-B`). -/
theorem Ohat_isOpen : IsOpen (d.Ohat : Set (GL2TF.Quat.BHat d.a d.b)ˣ) :=
  (GL2TF.Quat.latticeCompletion_compact_open d.a d.b).2 d.O.1 |>.2

end DefiniteData

/-! ### Class sets and stabilisers -/

/-- `def:s01-classset`: `B^×` as a subgroup of `B̂^×`, the image of `Units.map (finEmbed a b)`. -/
noncomputable def globalUnits (a b : ℤ) : Subgroup (GL2TF.Quat.BHat a b)ˣ :=
  (Units.map (GL2TF.Quat.finEmbed a b).toMonoidHom).range

/-- `def:s01-classset`: the double coset space `X_B(U) = B^× \ B̂^× / U`. -/
abbrev XB {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) : Type :=
  DoubleCoset.Quotient (globalUnits a b : Set (GL2TF.Quat.BHat a b)ˣ) (U : Set (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-classset`: the stabiliser `Γ_x(U) = B^× ∩ x U x⁻¹` (inside `B^×`). -/
noncomputable abbrev Gam {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) :
    Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ :=
  GL2TF.Quat.classStabilizer U x

/-- `{±1} ⊆ B^×`. -/
def pmOne {a b : ℤ} : Subgroup (GL2TF.Quat.QuatAlg ℚ a b)ˣ := Subgroup.zpowers (-1)

/-- `def:s01-classset`: the weight `w_x = |Γ_x / (Γ_x ∩ {±1})|` (note: the import's `mass` uses `|Γ_x|`). -/
noncomputable def wx {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : (GL2TF.Quat.BHat a b)ˣ) : ℕ :=
  Nat.card (Gam U x) / Nat.card ↥(Gam U x ⊓ pmOne)

/-- `thm:s01-mass`: the full mass `∑_{c ∈ X_B(U)} 1/|Γ_{x_c}|` (representatives `c.out`, full stabilisers). -/
noncomputable def massFull {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) : ℚ :=
  ∑ᶠ c : XB U, (1 : ℚ) / (Nat.card (Gam U (Quotient.out c)) : ℚ)

/-- `def:s01-classset`: at `U = Ô^×`, `XB` is the import's `classSet` (definitional). -/
theorem XB_units_eq_classSet {a b : ℤ} (O : QOrder a b) :
    XB (GL2TF.Quat.orderCompletionUnits O) = GL2TF.Quat.classSet O := rfl

/-- `thm:s01-mass` (a) at full level: `massFull Ô^× = mass O` (`s01-mass`, definitional). -/
theorem massFull_units_eq_mass {a b : ℤ} (O : QOrder a b) :
    massFull (GL2TF.Quat.orderCompletionUnits O) = GL2TF.Quat.mass O := rfl

/-- `prop:s01-finite`: for `U ≤ Ô^×` open, `X_B(U)` is finite (`s01-finite`). -/
theorem XB_finite (d : DefiniteData) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hU : U ≤ GL2TF.Quat.orderCompletionUnits d.O.1) (hUo : IsOpen (U : Set (GL2TF.Quat.BHat d.a d.b)ˣ)) :
    Finite (XB U) :=
  GL2TF.Quat.classSet_finite_of_open d.ha d.hb d.O.1 U hU hUo

end Langlandscape.Quat
