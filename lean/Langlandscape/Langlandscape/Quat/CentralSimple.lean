/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalComponent
import StacksCore.RingTheory.SkolemNoether
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# `B` is central simple; Skolem–Noether corollaries (S01-L2)

Tex label `def:s01-B` (the quaternion algebra `B = (a,b)_ℚ`, its local splittings `ι_ℓ`).

* `QuatAlg.isCentral`: `ℍ[K,a,0,b]` is central over any field `K` with `2 ≠ 0`, `a ≠ 0`, `b ≠ 0`
  (commutant of `i` and `j`).
* `QuatAlg.divisionRingOfDefinite`: for `a, b < 0` the rational algebra is a division ring (from the import's
  `definite_division`); its `ℚ`-smul and `ratCast` are the algebra ones (no `Algebra ℚ` diamond).
  `QuatAlg.isSimpleRing_of_definite`.
* Instances under `[Fact (a < 0)] [Fact (b < 0)]`: `DivisionRing`, `IsSimpleRing`, `Algebra.IsCentral ℚ`.
* Skolem–Noether (vendored Stacks 074Q/074R): `QuatAlg.algHom_conj`, `QuatAlg.algEquiv_inner`.
* `localSplitting_conj`: two splittings `B_ℓ ≃ M₂(ℚ_ℓ)` differ by `GL₂(ℚ_ℓ)`-conjugation;
  `DefiniteData.iota_conj` for `ι_ℓ` of S01-L3b.

Status: *formalized*.
-/

namespace Langlandscape.Quat

open GL2TF.Quat (definite_division)
open GL2TF.Quat (QuatAlg)

namespace QuatAlg

section Central

variable {K : Type*} [Field K] {a b : ℤ}

/-- `def:s01-B`: `ℍ[K,a,0,b]` is central over `K` when `2, a, b ≠ 0` in `K`: an element commuting with `i` and `j`
is a scalar (`s01-B`). The hypothesis on `b` is not needed (kept for the planned signature). -/
theorem isCentral [NeZero (2 : K)] (ha : (a : K) ≠ 0) (_hb : (b : K) ≠ 0) :
    Algebra.IsCentral K (QuatAlg K a b) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have h1 := hx ⟨0, 1, 0, 0⟩
    have h2 := hx ⟨0, 0, 1, 0⟩
    have h2K : (2 : K) ≠ 0 := NeZero.ne 2
    have e1 := congrArg QuaternionAlgebra.imJ h1
    have e2 := congrArg QuaternionAlgebra.imK h1
    have e3 := congrArg QuaternionAlgebra.imK h2
    simp only [QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] at e1 e2 e3
    have hK : x.imK = 0 := by
      have : (2 * a : K) * x.imK = 0 := by linear_combination e1
      simpa [h2K, ha] using this
    have hJ : x.imJ = 0 := by
      have : (2 : K) * x.imJ = 0 := by linear_combination e2
      simpa [h2K] using this
    have hI : x.imI = 0 := by
      have : (2 : K) * x.imI = 0 := by linear_combination -e3
      simpa [h2K] using this
    refine Algebra.mem_bot.2 ⟨x.re, ?_⟩
    ext <;> simp [QuaternionAlgebra.algebraMap_eq, hI, hJ, hK]

end Central

section Definite

variable {a b : ℤ}

/-- For `r ≠ 0`, the inverse of the scalar `r` in any group-with-zero structure on `B` is the scalar `r⁻¹`
(`def:s01-B`, `s01-B`). -/
private lemma inv_algebraMap {G : GroupWithZero (QuatAlg ℚ a b)}
    (hG : G.toMonoidWithZero = (inferInstance : MonoidWithZero (QuatAlg ℚ a b))) {r : ℚ} (hr : r ≠ 0) :
    @Inv.inv _ G.toInv (algebraMap ℚ (QuatAlg ℚ a b) r) = algebraMap ℚ (QuatAlg ℚ a b) r⁻¹ := by
  let _ := G
  have hne : algebraMap ℚ (QuatAlg ℚ a b) r ≠ 0 := by
    intro h; exact hr (by simpa using congrArg QuaternionAlgebra.re h)
  apply inv_eq_of_mul_eq_one_right
  have : (algebraMap ℚ (QuatAlg ℚ a b) r * algebraMap ℚ (QuatAlg ℚ a b) r⁻¹ : QuatAlg ℚ a b) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  convert this using 1
  · exact congrArg (fun M : MonoidWithZero (QuatAlg ℚ a b) => @HMul.hMul _ _ _ (@instHMul _ M.toMul) _ _) hG
  · exact congrArg (fun M : MonoidWithZero (QuatAlg ℚ a b) => @OfNat.ofNat _ 1 (@One.toOfNat1 _ M.toOne)) hG

/-- `def:s01-B`: for `a, b < 0` the rational quaternion algebra `B = (a,b)_ℚ` is a division ring
(import `definite_division`). The `ℚ`-actions and `ratCast` agree with those of the `ℚ`-algebra `B`. -/
@[instance_reducible]
noncomputable def divisionRingOfDefinite (ha : a < 0) (hb : b < 0) : DivisionRing (QuatAlg ℚ a b) :=
  let G : GroupWithZero (QuatAlg ℚ a b) :=
    groupWithZeroOfIsUnitOrEqZero fun x =>
      (em (x = 0)).elim Or.inr fun hx => Or.inl ((definite_division ha hb).1 x hx)
  have hG : G.toMonoidWithZero = (inferInstance : MonoidWithZero (QuatAlg ℚ a b)) := rfl
  { (inferInstance : Ring (QuatAlg ℚ a b)), G with
    nnratCast := fun q => algebraMap ℚ (QuatAlg ℚ a b) q
    ratCast := fun q => algebraMap ℚ (QuatAlg ℚ a b) q
    nnqsmul := fun q x => (q : ℚ) • x
    qsmul := fun q x => q • x
    nnratCast_def := fun q => by
      by_cases hq : (q.den : ℚ) = 0
      · exact absurd hq (by exact_mod_cast q.den_ne_zero)
      show algebraMap ℚ _ (q : ℚ) = (q.num : QuatAlg ℚ a b) * @Inv.inv _ G.toInv (q.den : QuatAlg ℚ a b)
      rw [← map_natCast (algebraMap ℚ (QuatAlg ℚ a b)) q.den, inv_algebraMap hG hq,
        ← map_natCast (algebraMap ℚ (QuatAlg ℚ a b)) q.num, ← map_mul]
      congr 1
      rw [← div_eq_mul_inv]; exact NNRat.cast_def q
    ratCast_def := fun q => by
      have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      show algebraMap ℚ _ q = (q.num : QuatAlg ℚ a b) * @Inv.inv _ G.toInv (q.den : QuatAlg ℚ a b)
      rw [← map_natCast (algebraMap ℚ (QuatAlg ℚ a b)) q.den, inv_algebraMap hG hq,
        ← map_intCast (algebraMap ℚ (QuatAlg ℚ a b)) q.num, ← map_mul, ← div_eq_mul_inv, Rat.num_div_den]
    nnqsmul_def := fun q x => by
      show (q : ℚ) • x = algebraMap ℚ _ (q : ℚ) * x
      rw [Algebra.smul_def]
    qsmul_def := fun q x => by
      show q • x = algebraMap ℚ _ q * x
      rw [Algebra.smul_def] }

/-- `def:s01-B`: for `a, b < 0` the rational quaternion algebra is a simple ring (`s01-B`). -/
theorem isSimpleRing_of_definite (ha : a < 0) (hb : b < 0) : IsSimpleRing (QuatAlg ℚ a b) :=
  @DivisionRing.isSimpleRing _ (divisionRingOfDefinite ha hb)

/-- `def:s01-B`: for `a, b < 0` the rational quaternion algebra is central over `ℚ` (`s01-B`). -/
theorem isCentral_of_definite (ha : a < 0) (hb : b < 0) : Algebra.IsCentral ℚ (QuatAlg ℚ a b) :=
  isCentral (by exact_mod_cast ha.ne) (by exact_mod_cast hb.ne)

variable [ha : Fact (a < 0)] [hb : Fact (b < 0)]

/-- `def:s01-B`: the division ring structure of a definite `B` (`Fact` form). -/
noncomputable instance instDivisionRingOfDefinite : DivisionRing (QuatAlg ℚ a b) :=
  divisionRingOfDefinite ha.out hb.out

/-- `def:s01-B`: a definite `B` is simple (`Fact` form). -/
instance instIsSimpleRingOfDefinite : IsSimpleRing (QuatAlg ℚ a b) :=
  isSimpleRing_of_definite ha.out hb.out

/-- `def:s01-B`: a definite `B` is central over `ℚ` (`Fact` form). -/
instance instIsCentralOfDefinite : Algebra.IsCentral ℚ (QuatAlg ℚ a b) :=
  isCentral_of_definite ha.out hb.out

/-- `def:s01-B` (Skolem–Noether, Stacks 074Q): two `ℚ`-algebra maps from a field `L` (more generally, a simple
`ℚ`-algebra) into a definite `B` are conjugate by a unit of `B` (`s01-B`). -/
theorem algHom_conj {L : Type} [Ring L] [Algebra ℚ L] [IsSimpleRing L] (f g : L →ₐ[ℚ] QuatAlg ℚ a b) :
    ∃ x : (QuatAlg ℚ a b)ˣ, ∀ y : L, g y = x * f y * x⁻¹ :=
  skolemNoether ℚ (QuatAlg ℚ a b) L f g

/-- `def:s01-B` (Skolem–Noether, Stacks 074R): every `ℚ`-algebra automorphism of a definite `B` is inner
(`s01-B`). -/
theorem algEquiv_inner (e : QuatAlg ℚ a b ≃ₐ[ℚ] QuatAlg ℚ a b) :
    ∃ x : (QuatAlg ℚ a b)ˣ, ∀ y, e y = x * y * x⁻¹ :=
  skolemNoether' ℚ (QuatAlg ℚ a b) e

end Definite

end QuatAlg

/-- `def:s01-B`: any two splittings `B_ℓ ≃ M₂(ℚ_ℓ)` differ by conjugation by some `g ∈ GL₂(ℚ_ℓ)`
(Skolem–Noether for the central simple algebra `M₂(ℚ_ℓ)`, Stacks 074R) (`s01-B`). -/
theorem localSplitting_conj {a b : ℤ} {ℓ : ℕ} [Fact ℓ.Prime]
    (ι ι' : QuatAlg ℚ_[ℓ] a b ≃ₐ[ℚ_[ℓ]] Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :
    ∃ g : GL (Fin 2) ℚ_[ℓ], ∀ y, ι' y = g * ι y * g⁻¹ := by
  obtain ⟨g, hg⟩ := skolemNoether' ℚ_[ℓ] (Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) (ι.symm.trans ι')
  exact ⟨g, fun y => by simpa using hg (ι y)⟩

/-- `def:s01-B`: the splitting `ι_ℓ` of S01-L3b is unique up to `GL₂(ℚ_ℓ)`-conjugation: every splitting
`ι' : B_ℓ ≃ M₂(ℚ_ℓ)` is `g ι_ℓ g⁻¹` (`s01-B`). -/
theorem DefiniteData.iota_conj (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)
    (ι' : QuatAlg ℚ_[ℓ] d.a d.b ≃ₐ[ℚ_[ℓ]] Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :
    ∃ g : GL (Fin 2) ℚ_[ℓ], ∀ y, ι' y = g * d.iota ℓ hℓ y * g⁻¹ :=
  localSplitting_conj (d.iota ℓ hℓ) ι'

end Langlandscape.Quat
