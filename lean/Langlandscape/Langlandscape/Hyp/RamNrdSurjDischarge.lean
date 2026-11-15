/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.RamNrdSurj
import Langlandscape.Local.QuatNrdOdd
import Langlandscape.Local.QuatNrdTwo
import AlgJL.VolIII.P2.LocalStructure

/-!
# Discharge of `Hyp.RamNrdSurj`: `Nrd(𝒪_ℓ^×) = ℤ_ℓ^×` at the ramified primes `ℓ ∣ D`

`mathematics/chapters/s01/1-classsets.tex`, `lem:s01-nrd` (the `ℓ ∣ D` ingredient).

* `ramNrdSurj_of_local` : reduction of `Hyp.RamNrdSurj d` to local norm surjectivity. At `ℓ ∣ D` the local order is
  `𝒪_ℓ = {x | nrd x ∈ ℤ_ℓ}` (the import's `GL2TF.Quat.division_maximalOrder`), so an
  `x ∈ B_ℓ^×` with `nrd x ∈ ℤ_ℓ^×` has `x, x⁻¹ ∈ 𝒪_ℓ`, i.e. `localEmbed ℓ x ∈ Ô^×`
  (`Quat.localEmbed_mem_orderCompletionUnits_iff`).
* The local inputs: `Local.exists_nrd_eq_unit_of_ne_two` (odd `ℓ`, `Local/QuatNrdOdd.lean`) and
  `Local.exists_nrd_eq_unit_two` (`ℓ = 2`, `Local/QuatNrdTwo.lean`); neither needs the ramification hypothesis.
* `ramNrdSurj_holds d : RamNrdSurj d` for every `DefiniteData d`.

The facts `nrd 1 = 1`, `nrd (xy) = nrd x nrd y` and `𝒪_ℓ = {x | nrd x ∈ ℤ_ℓ}` are re-proved inline (two-line proofs)
rather than taken from `Brandt.nrd_one_local`, `Brandt.nrd_mul_local`, `Brandt.mem_localOrder_iff_nrd`
(`Brandt/RightTranslate.lean`), to avoid importing the Brandt/Hecke-module chain into a `Hyp` file.

The hypothesis file `Hyp/RamNrdSurj.lean` and the signatures of its consumers (`Quat/LevelNrd.lean`,
`Tree/Admissible.lean`) are unchanged; a consumer gets the argument as `ramNrdSurj_holds d`.

Status: *formalized* (`lem:s01-nrd`, ramified part).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open GL2TF Langlandscape.Quat

/-- `lem:s01-nrd` (`s01-nrd`): reduction of the hypothesis `RamNrdSurj d` to local norm surjectivity. If at every
ramified prime `ℓ ∣ D` every unit `w ∈ ℤ_ℓ^×` is the reduced norm of some `x ∈ B_ℓ^×`, then `x` is automatically
integral (`x, x⁻¹ ∈ 𝒪_ℓ`, as `𝒪_ℓ = {y | nrd y ∈ ℤ_ℓ}`), so `localEmbed ℓ x ∈ Ô^×`. -/
theorem ramNrdSurj_of_local (d : DefiniteData)
    (hloc : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ d.D → ∀ w : ℤ_[ℓ]ˣ,
      ∃ x : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ,
        GL2TF.Quat.nrd (x : QuatAlg ℚ_[ℓ] d.a d.b) = ((w : ℤ_[ℓ]) : ℚ_[ℓ])) :
    RamNrdSurj d := by
  intro ℓ _ hℓD w
  obtain ⟨x, hx⟩ := hloc ℓ hℓD w
  -- the local lattice at a ramified prime is `{x | nrd x ∈ ℤ_ℓ}` (the import's `division_maximalOrder`)
  have hlat : (GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) :
      Set (QuatAlg ℚ_[ℓ] d.a d.b)) = {y | GL2TF.Quat.nrd y ∈ PadicInt.subring ℓ} :=
    (GL2TF.Quat.division_maximalOrder d.hD ℓ hℓD).2.2 d.O
  have memlat : ∀ y : QuatAlg ℚ_[ℓ] d.a d.b,
      y ∈ GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) ↔
        GL2TF.Quat.nrd y ∈ PadicInt.subring ℓ :=
    fun y => Set.ext_iff.mp hlat y
  -- `nrd` is multiplicative and `nrd 1 = 1`, so `nrd x * nrd x⁻¹ = 1`
  have hone : GL2TF.Quat.nrd (1 : QuatAlg ℚ_[ℓ] d.a d.b) = 1 := by
    simp [GL2TF.Quat.nrd]
  have hnrd_mul : ∀ u v : QuatAlg ℚ_[ℓ] d.a d.b,
      GL2TF.Quat.nrd (u * v) = GL2TF.Quat.nrd u * GL2TF.Quat.nrd v := by
    intro u v
    simp [GL2TF.Quat.nrd]
    ring
  have emul : (x : QuatAlg ℚ_[ℓ] d.a d.b) *
      ((x⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) = 1 :=
    Units.mul_inv x
  have hprod : GL2TF.Quat.nrd (x : QuatAlg ℚ_[ℓ] d.a d.b) *
      GL2TF.Quat.nrd ((x⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) = 1 := by
    rw [← hnrd_mul, emul, hone]
  rw [hx] at hprod
  -- in the field `ℚ_[ℓ]`: `nrd x⁻¹ = (nrd x)⁻¹ = (w : ℚ_[ℓ])⁻¹ = (w⁻¹ : ℚ_[ℓ])`
  have hmul : (((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * (((w : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
    have h : PadicInt.Coe.ringHom (p := ℓ) ((((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((w : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) = 1 := by
      rw [Units.inv_mul, map_one]
    rw [map_mul] at h
    exact h
  have hcoe : (((w : ℤ_[ℓ]) : ℚ_[ℓ]))⁻¹ = (((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  have hinv : GL2TF.Quat.nrd ((x⁻¹ : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) =
      (((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) :=
    (eq_inv_of_mul_eq_one_right hprod).trans hcoe
  -- coerced units of `ℤ_ℓ` land in `PadicInt.subring ℓ`
  have hwsub : (((w : ℤ_[ℓ]) : ℚ_[ℓ])) ∈ PadicInt.subring ℓ :=
    (PadicInt.mem_subring_iff ℓ).2 (PadicInt.norm_le_one (w : ℤ_[ℓ]))
  have hwinvsub : (((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) ∈ PadicInt.subring ℓ :=
    (PadicInt.mem_subring_iff ℓ).2 (PadicInt.norm_le_one ((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))
  refine ⟨x, ?_, hx⟩
  refine (localEmbed_mem_orderCompletionUnits_iff d.O.1 x).2
    ⟨(memlat _).2 (by rw [hx]; exact hwsub), (memlat _).2 (by rw [hinv]; exact hwinvsub)⟩

/-- `lem:s01-nrd` (`s01-nrd`), ramified part: the hypothesis `Hyp.RamNrdSurj d` holds for every definite
quaternion algebra: at every `ℓ ∣ D` the reduced norm maps `𝒪_ℓ^×` onto `ℤ_ℓ^×`. Combines `ramNrdSurj_of_local`
with `Local.exists_nrd_eq_unit_of_ne_two` (odd `ℓ`) and `Local.exists_nrd_eq_unit_two` (`ℓ = 2`); an `x ∈ B_ℓ` with
`nrd x ∈ ℤ_ℓ^×` is a unit (`GL2TF.Quat.isUnit_iff_isUnit_nrd`). The local inputs do not use `ℓ ∣ D`: the proof
gives `nrd(B_ℓ^×) ⊇ ℤ_ℓ^×` at every prime `ℓ` and for all nonzero `a, b`; the hypothesis `ℓ ∣ D` enters only through
`𝒪_ℓ = {x | nrd x ∈ ℤ_ℓ}`.

Provenance: proof drafted by mistral-large-4-0 (opencode), run by Fabian Januszewski on Abhijit A J's machine,
2026-11-15; integrated and audited by the Langlandscape agents. -/
theorem ramNrdSurj_holds (d : DefiniteData) : RamNrdSurj d := by
  refine ramNrdSurj_of_local d ?_
  intro ℓ _ _ w
  have ha : d.a ≠ 0 := ne_of_lt d.ha
  have hb : d.b ≠ 0 := ne_of_lt d.hb
  have hu : IsUnit ((w : ℤ_[ℓ]) : ℚ_[ℓ]) := (w.isUnit).map (PadicInt.Coe.ringHom (p := ℓ))
  have key : ∀ x : QuatAlg ℚ_[ℓ] d.a d.b, GL2TF.Quat.nrd x = ((w : ℤ_[ℓ]) : ℚ_[ℓ]) →
      ∃ u : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ,
        GL2TF.Quat.nrd (u : QuatAlg ℚ_[ℓ] d.a d.b) = ((w : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    intro x hx
    obtain ⟨u, hu2⟩ := (GL2TF.Quat.isUnit_iff_isUnit_nrd.1 x).mpr (by rw [hx]; exact hu)
    exact ⟨u, by rw [hu2]; exact hx⟩
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨x, hx⟩ := Langlandscape.Local.exists_nrd_eq_unit_two ha hb w
    exact key x hx
  · obtain ⟨x, hx⟩ := Langlandscape.Local.exists_nrd_eq_unit_of_ne_two ha hb ℓ h2 w
    exact key x hx

end Langlandscape.Hyp
