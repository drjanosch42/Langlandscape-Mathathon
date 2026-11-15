/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ribet.Coeff
import LanglandscapeTests.S01.LocalComponent

/-! Non-vacuity and shape tests for `Langlandscape.Ribet.Coeff` (S03-L14). -/

set_option autoImplicit false

namespace LanglandscapeTests.S03.Coeff

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree Langlandscape.Ribet

/-- `7` is prime (test data, `s03-ribet`). -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- `thm:s03-ribet`(b) (`s03-ribet`), test data: `7 ∤ D = 2` for the Hurwitz data (`B` of discriminant `2`). -/
theorem seven_ndvd : ¬ 7 ∣ hurwitzData.D := by decide

section Generic

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (R : Type) [CommRing R]

/-- `thm:s03-ribet`(b) (`s03-ribet`), test: the trivial coefficient data exists at level `Ô^×`. -/
theorem test_coeffData_triv : Nonempty (CoeffData d q hq d.Ohat R R) :=
  ⟨CoeffData.triv d q hq d.Ohat R⟩

/-- `thm:s03-ribet`(b), `thm:s03-iharaH0` (`s03-ribet`), shape test: coefficient data with `V = ℤ_[p]` (trivial
action) and the coefficient differential `alphaV` over `ℤ_[p]` at level `Ô^×`. -/
theorem test_coeffData_padic (p : ℕ) [Fact p.Prime] :
    Nonempty (CoeffData d q hq d.Ohat ℤ_[p] ℤ_[p]) ∧
      Nonempty (brandtModule (d.U0q q (coprime_of_not_dvd hq) d.Ohat) ℤ_[p] ℤ_[p]
          (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ' →ₗ[ℤ_[p]]
        brandtModule d.Ohat ℤ_[p] ℤ_[p] (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ ×
          brandtModule d.Ohat ℤ_[p] ℤ_[p] (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ) :=
  ⟨⟨CoeffData.triv d q hq d.Ohat ℤ_[p]⟩,
    ⟨alphaV (CoeffData.triv d q hq d.Ohat ℤ_[p]) (isQLevel_Ohat (hq := hq))⟩⟩

/-- `thm:s03-ribet`(b), `thm:s03-iharaH0` (`s03-ribet`), test: coefficient data with a (possibly non-trivial)
`p`-adic action `ρ(u) = ρ_p(u_p)`, `p ≠ q`, and its coefficient differential `alphaV` at level `Ô^×`. -/
theorem test_coeffData_ofLocal (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (hpq : p ≠ q)
    {V : Type} [AddCommGroup V] [Module R V] (ρp : GL (Fin 2) ℚ_[p] →* (V ≃ₗ[R] V)) (u : d.Ohat) :
    (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ u = ρp (localComponent d p hp (u : (BHat d.a d.b)ˣ)) ∧
      Nonempty (brandtModule (d.U0q q (coprime_of_not_dvd hq) d.Ohat) R V
          (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ' →ₗ[R]
        brandtModule d.Ohat R V (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ ×
          brandtModule d.Ohat R V (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ) :=
  ⟨CoeffData.ofLocal_ρ_apply p hp hpq ρp u,
    ⟨alphaV (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp) (isQLevel_Ohat (hq := hq))⟩⟩

/-- `thm:s03-ribet`(b), (C3) (`s03-conv`), test: `s_{0*} ∘ s_0^* = (q + 1) • id` at level `Ô^×`. -/
theorem test_s0TrV_comp_s0PullV {V : Type} [AddCommGroup V] [Module R V] (c : CoeffData d q hq d.Ohat R V) :
    s0TrV c (isQLevel_Ohat (hq := hq)) ∘ₗ s0PullV c = ((q + 1 : ℕ) : R) • LinearMap.id := by
  rw [s0TrV_comp_s0PullV, relIndex_U0q (isQLevel_Ohat (hq := hq))]

end Generic

section Hurwitz

variable (R : Type) [CommRing R]

/-- `thm:s03-ribet`(b), `if:s02-coh` (`s03-conv`), test: `alphaV_triv` for `B` of discriminant `2`, `q = 7`,
`U = Ô^×` (the Brandt graph `B₂`). -/
theorem test_alphaV_triv
    (f : brandtModule (hurwitzData.U0q 7 (coprime_of_not_dvd seven_ndvd) hurwitzData.Ohat) R R
      (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R).ρ') :
    (trivEquivU hurwitzData 7 seven_ndvd hurwitzData.Ohat R
          (alphaV (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R)
            (isQLevel_Ohat (hq := seven_ndvd)) f).1,
        trivEquivU hurwitzData 7 seven_ndvd hurwitzData.Ohat R
          (alphaV (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R)
            (isQLevel_Ohat (hq := seven_ndvd)) f).2) =
      (-(s0Tr hurwitzData 7 seven_ndvd hurwitzData.Ohat R (isQLevel_Ohat (hq := seven_ndvd))
          (trivEquivU0q hurwitzData 7 seven_ndvd hurwitzData.Ohat R f)),
        s1Tr hurwitzData 7 seven_ndvd hurwitzData.Ohat R (isQLevel_Ohat (hq := seven_ndvd))
          (trivEquivU0q hurwitzData 7 seven_ndvd hurwitzData.Ohat R f)) :=
  alphaV_triv (isQLevel_Ohat (hq := seven_ndvd)) f

/-- `thm:s03-ribet`(b), `if:s02-coh` (`s03-conv`), test: `alphaVee_triv` (`α^∨ = δ`) for `B` of discriminant `2`,
`q = 7`, `U = Ô^×`. -/
theorem test_alphaVee_triv
    (f : brandtModule hurwitzData.Ohat R R (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R).ρ ×
      brandtModule hurwitzData.Ohat R R (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R).ρ) :
    trivEquivU0q hurwitzData 7 seven_ndvd hurwitzData.Ohat R
        (alphaVee (CoeffData.triv hurwitzData 7 seven_ndvd hurwitzData.Ohat R)
          (isQLevel_Ohat (hq := seven_ndvd)) f) =
      deltaCoh hurwitzData 7 seven_ndvd hurwitzData.Ohat R
        (trivEquivU hurwitzData 7 seven_ndvd hurwitzData.Ohat R f.1,
          trivEquivU hurwitzData 7 seven_ndvd hurwitzData.Ohat R f.2) :=
  alphaVee_triv (isQLevel_Ohat (hq := seven_ndvd)) f

end Hurwitz

end LanglandscapeTests.S03.Coeff
