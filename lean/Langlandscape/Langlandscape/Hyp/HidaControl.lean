/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ordinary.Projector
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.Ideal.Operations

/-!
# Hypothesis `HidaControl`: weight control for the definite ordinary module (S04-L14a, schematic)

`mathematics/chapters/s04/control.tex`, `thm:s04-control`(b); dictionary `rem:s04-controlb` (`hsieh.tex`).
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Status: *cited* (Hsieh Thm. 4.2(2); Longo–Vigni Thm. 3.7; Hida 1988 Thm. 9.4); **schematic** (OVERVIEW §8 F6, stage-04
decision Q3): the Hecke modules are abstract data. Q3 was decided at int3, before S04-L15a/b
(`Brandt/HeckeCoeff.lean`, `Brandt/UpCoeff.lean`) were green; a non-schematic form needs `UpV` at all levels `U_s`, the
`P^ad_k` quotient of the Λ-adic module and `Mord`, none of which is assembled here.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Ordinary

/-- `thm:s04-control`(b) (`s04-control`), finite-level form mod `p ^ s`, definite side, **schematic**.

Intended instantiation: `U = U₁(M)`-type levels only (`Utower M p s`; Hsieh treats only these, `rem:s04-controlb`),
and, for the integral form, only when `p ∤ φ(M)` (hypothesis `hφ`, `Nat.totient`; chapter audit M9.3).
Data: `Mk` with `Uk` stands for the weight-`k` Brandt module with coefficients `V_k ⊗ 𝒪` modulo `p ^ s` and its
`U_p`; `M2` (an `A`-module, `A` standing for `Λ/p ^ s`) with `U2` for the weight-2 module (`e 𝒪[X_s(U)]` mod `p ^ s`);
`Pk` for the arithmetic ideal `P^ad_k = ker([u] ↦ u^(2-k))` (`def:s04-Pk`); `Qk` with `π`, `Ubar` for
`M2 ⧸ Pk • M2` with the induced `U_p` (premises: `π` surjective, kernel `Pk • ⊤`, intertwining).
Conclusion: the ordinary parts are isomorphic over `ZMod (p ^ s)` (`Mord ⊗_Λ Λ/P^ad_k ≃ e·Brandt(V_k)`; stated on
modules, not on their duals).

**What is abstracted:** the identification of the data with Brandt modules / `Utower M p s` (not checked: the statement
is the true theorem only for that instantiation); compatibility with the other Hecke operators and the diamond action; the
character-piece and `Γ₀(p)`-level refinements (`k ≥ 3`, `p`-stabilisation); `k` enters only via `hk` and `Pk`.

Source: Hsieh Thm. 4.2(2); Longo–Vigni Thm. 3.7; Hida 1988 Thm. 9.4 (cited, §1.4 conventions). Discharge plan: cited,
post-hackathon; a faithful statement would build on `UpV` (S04-L15b) at all levels, the `P^ad_k` quotient and `Mord`.
Owner: S04-L14a. -/
def HidaControl (M p s k : ℕ) (hk : 2 ≤ k) (_hφ : ¬ p ∣ Nat.totient M)
    (A : Type) [CommRing A] [Algebra (ZMod (p ^ s)) A]
    (Mk : Type) [AddCommGroup Mk] [Module (ZMod (p ^ s)) Mk] (Uk : Module.End (ZMod (p ^ s)) Mk)
    (M2 : Type) [AddCommGroup M2] [Module (ZMod (p ^ s)) M2] [Module A M2] (U2 : Module.End A M2)
    (Pk : Ideal A)
    (Qk : Type) [AddCommGroup Qk] [Module (ZMod (p ^ s)) Qk] (π : M2 →ₗ[ZMod (p ^ s)] Qk)
    (Ubar : Module.End (ZMod (p ^ s)) Qk) : Prop :=
  Function.Surjective π → (∀ m, π m = 0 ↔ m ∈ (Pk • ⊤ : Submodule A M2)) →
    (∀ m, π (U2 m) = Ubar (π m)) → Nonempty (ordPart Uk ≃ₗ[ZMod (p ^ s)] ordPart Ubar)

end Langlandscape.Hyp
