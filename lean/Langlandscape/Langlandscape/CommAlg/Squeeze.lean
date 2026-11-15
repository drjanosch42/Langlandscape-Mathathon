/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The squeeze of the defect formula (S06-L7)

`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-defect`, step (5) (the squeeze). Secondary
reference:
`plan/staged/stage-06-integral-defect.tex`.

Let `I` be a local domain, `P : I →+* 𝒪` a local homomorphism to a local domain `𝒪`
(the arithmetic specialisation `I_F → 𝒪_P`), `𝔱 ⊆ (h)` an ideal of `I` with `P h ≠ 0`, and
assume `P(𝔱) 𝒪 ⊇ (P h)`. Then `𝔱 = (h)`.

Proof (tex step (5)): if `h ∉ 𝔱`, every `t = d h ∈ 𝔱` has `d` a non-unit (else `h = d⁻¹ t ∈ 𝔱`),
so `P d ∈ 𝔪_𝒪` because `P` is local. Hence `P(𝔱) 𝒪 ⊆ (P h) 𝔪_𝒪`, so `P h = P h · z` with
`z ∈ 𝔪_𝒪`; cancelling `P h ≠ 0` in the domain `𝒪` gives `z = 1 ∈ 𝔪_𝒪`, a contradiction.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.CommAlg

/-- **The squeeze** (`thm:s06-defect`, step (5); stage-06 row S06-L7).
Let `I` be a local domain, `𝒪` a local domain and `P : I →+* 𝒪` a local ring homomorphism.
If `𝔱 ≤ span {h}`, `P h ≠ 0` and `span (P '' 𝔱) ≥ span {P h}`, then `𝔱 = span {h}`.

The locality of `P` (`[IsLocalHom P]`, with `𝒪` local) cannot be dropped: for the inclusion
`P : ℤ_(p) → ℚ` (both local domains, `P` not local), `𝔱 = (p)` and `h = 1` we have
`𝔱 ≤ (1)`, `P 1 = 1 ≠ 0` and `span (P '' (p)) = ℚ ≥ span {1}`, but `(p) ≠ (1)`.

In the application `I = I_F`, `𝒪 = 𝒪_P = I_F / P` (so `P` is surjective, hence local),
`𝔱 = 𝔱_q(F)`, `(h) = (h_F) = 𝔠_q(F)` and `P(𝔱_q(F)) 𝒪_P = (ϖ^t) ⊇ P(𝔠_q(F)) 𝒪_P ∋ P h_F`. The
domain hypothesis on `I` is part of the stated setting and is not used by the proof. -/
theorem squeeze {I 𝒪 : Type*} [CommRing I] [IsDomain I] [IsLocalRing I]
    [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] (P : I →+* 𝒪) [IsLocalHom P]
    {𝔱 : Ideal I} {h : I} (h𝔱 : 𝔱 ≤ Ideal.span {h}) (hPh : P h ≠ 0)
    (hP : Ideal.span (P '' 𝔱) ≥ Ideal.span {P h}) :
    𝔱 = Ideal.span {h} := by
  refine le_antisymm h𝔱 ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra hh
  have key : Ideal.span (P '' 𝔱) ≤ Ideal.span {P h} * IsLocalRing.maximalIdeal 𝒪 := by
    rw [Ideal.span_le]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 (h𝔱 ht)
    refine Ideal.mem_span_singleton_mul.2 ⟨P d, ?_, by rw [map_mul, mul_comm]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu'⟩ := (isUnit_map_iff P d).1 hu
    apply hh
    have hmem : d * h * ↑u⁻¹ ∈ 𝔱 := 𝔱.mul_mem_right _ ht
    rwa [← hu', mul_comm (u : I) h, mul_assoc, Units.mul_inv, mul_one] at hmem
  have hmem : P h ∈ Ideal.span {P h} * IsLocalRing.maximalIdeal 𝒪 :=
    key (hP (Ideal.mem_span_singleton_self _))
  obtain ⟨z, hz, hz1⟩ := Ideal.mem_span_singleton_mul.1 hmem
  have hz' : z = 1 := mul_left_cancel₀ hPh (by rw [hz1, mul_one])
  rw [hz'] at hz
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 hz)

end Langlandscape.CommAlg
