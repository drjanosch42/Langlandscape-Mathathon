/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Hypothesis `FreeRankTwo`: the old-form representation modulo `𝔠_q(F)` (S06-L8a)

`mathematics/chapters/s06/s06-m4.tex`, `prop:s06-galois`, cited inputs (1)–(3) and steps 1–3 of the proof: with
`A = I_F / 𝔠_q(F)`, `λ mod 𝔠_q(F)` factors through `R″ ≅ 𝐓(M)_𝔪 ⊗ I_F`; `ρ_M = H(M) ⊗_{𝐓(M)_𝔪} A` (input (1): `H(M)` free
of rank two) is unramified at `q` (input (2)), and has the same traces as `ρ_F ⊗ A` on Frobenius elements, hence on
all of `G_ℚ` (Chebotarev and continuity, input (3)).

The Lean content is the *output* of those steps: a representation `ρM : G → GL₂(I ⧸ 𝔠_q(F))`, trivial on `I_q`, whose
trace equals `tr ρ_F mod 𝔠_q(F)`. Steps 4–5 (trace identity at `q`, Burnside, trace form) are proved in Lean
(`Defect.galois`, S06-L8b, with `Hyp.ResidualBurnside` and `CommAlg.eq_one_of_trace_mul_eq`).

Source: Hsieh (2017) §7.2, proof of Lemma 7.4, p. 68 (via Wiles 1995 Cor. 1, 2, p. 482) for (1); good reduction of
`X_1(Mp^r)` at `q` (DDT Thm 3.1(a), p. 85) for (2); Chebotarev (DDT Thm 2.3, p. 52) for (3).
Status: *cited*, not discharged. Owner: S06-L8a. Consumer: `Defect.galois` (S06-L8b).

**Disclosure.** Given `Hyp.ResidualBurnside`, `Hyp.FreeRankTwo` is equivalent to the inclusion `𝔱_q ≤ 𝔠_q`; both directions are proved in Lean (`Defect.galois`, `Defect.freeRankTwo_of_le`, packaged as `Defect.freeRankTwo_iff_le`). The Galois half is therefore not formalized independently: its arithmetic content (that the old-form representation `ρ_M` exists at level `M`, steps 1–3 of `prop:s06-galois`) is the cited hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `prop:s06-galois` (`s06-galois`), inputs (1)–(3) and proof steps 1–3: there is `ρM : G → GL₂(I_F/𝔠_q(F))` (the
old-form representation `H(M) ⊗ A`), unramified at `q` (`ρM σ = 1` for `σ ∈ I_q`), with `tr ρM = tr ρ_F mod 𝔠_q(F)`.
Source: [Hs, §7.2, proof of Lemma 7.4, p. 68], [Wi95, Cor. 1, 2, p. 482], [DDT, Thm 3.1(a), p. 85; Thm 2.3, p. 52].
Discharge: *cited*. Owner: S06-L8a. -/
def FreeRankTwo (D : Defect.Setting Λ I T 𝒪 G) : Prop :=
  ∃ ρM : G →* GL (Fin 2) (I ⧸ D.cq),
    (∀ σ ∈ D.Iq, ρM σ = 1) ∧
    ∀ g : G, Matrix.trace (ρM g : Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) =
      Ideal.Quotient.mk D.cq (Matrix.trace (D.ρ g : Matrix (Fin 2) (Fin 2) I))

end Langlandscape.Hyp
