/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Algebra.Hom

/-!
# Targets as statements: Λ-adic Jacquet-Langlands (S01-L13)

`mathematics/chapters/s01/6-targets.tex`, `thm:s01-lambdaJL`, `if:s01-targets`.
No axiom (OVERVIEW 3.6); a theorem using `Hyp.LambdaJL` takes it as an explicit argument.

Status: *cited*, not to be discharged in this project.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

/-- Generator labels of the ordinary Λ-adic Hecke algebras (tex `thm:s01-lambdaJL`, `s01-lambdaJL`). -/
inductive LambdaJLGen
  | T (ℓ : ℕ)
  | U (ℓ : ℕ)
  | dia (d : ℕ)
  | Pi (ℓ : ℕ)

/-- `thm:s01-lambdaJL` (`s01-lambdaJL`): Λ-adic Jacquet-Langlands, `T^{ord, D-new} ≅ T_B^{ord}`: a surjection
`φ : TGL → TB` matching generators (`U_ℓ ↦ Π_ℓ` for `ℓ ∣ D`), whose kernel is `newIdeal`.

Diamond matching (X1 erratum; tex `thm:s01-lambdaJL`, `rem:s01-diamond`, `lem:s01-Upconv`): classical `⟨d⟩ ↦ seed ⟨d⟩⁻¹`.
`TB` is only a commutative ring, so the inverse is stated as `φ ⟨d⟩_GL * ⟨d⟩_B = 1` (in a commutative ring this says
exactly that `⟨d⟩_B` is a unit with inverse `φ ⟨d⟩_GL`); it avoids `Units`/`Ring.inverse` and a group-indexed generator.
The clause is required only for `d` prime to `M * p` (`Nat.Coprime d (M * p)`, S04-L17a, audit R1): for other `d`
(e.g. `d = 0`) the generator `⟨d⟩` is a junk value, typically `0`, and an unguarded unit condition would force `0 = 1`.

*Schematic interface; the GL₂ side is abstract data because Mathlib v4.35.0 has no Hecke operators on
`S_k(Γ_0(N))`; the hypothesis is JL only when `TGL`, `genGL`, `newIdeal` are instantiated by the true algebra,
generators and ideal, which cannot be checked in Lean here.* No later theorem may be advertised as "under Λ-adic JL"
without this caveat.

Source: Hida / Jacquet-Langlands; cited; not to be discharged in this project. -/
def LambdaJL (D M p : ℕ) (Λ TGL TB : Type*) [CommRing Λ] [CommRing TGL] [CommRing TB]
    [Algebra Λ TGL] [Algebra Λ TB] (genGL : LambdaJLGen → TGL) (genB : LambdaJLGen → TB)
    (newIdeal : Ideal TGL) : Prop :=
  ∃ φ : TGL →ₐ[Λ] TB,
    (Function.Surjective φ ∧
      (∀ ℓ, ℓ.Prime → ¬ ℓ ∣ D * M * p → φ (genGL (.T ℓ)) = genB (.T ℓ)) ∧
      (∀ ℓ, ℓ.Prime → ℓ ∣ M * p → φ (genGL (.U ℓ)) = genB (.U ℓ)) ∧
      (∀ d, Nat.Coprime d (M * p) → φ (genGL (.dia d)) * genB (.dia d) = 1) ∧
      (∀ ℓ, ℓ.Prime → ℓ ∣ D → φ (genGL (.U ℓ)) = genB (.Pi ℓ))) ∧
    RingHom.ker φ.toRingHom = newIdeal

end Langlandscape.Hyp
