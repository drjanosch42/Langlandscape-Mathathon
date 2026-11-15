/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.Defect.Setting
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Hypothesis `KimOta`: Kim–Ota's level-lowering identity at the point `P` (S06-L8a)

`mathematics/chapters/s06/s06-m3.tex`, `thm:s06-KO` for `f = F_P`, `N⁻ = q`, `N⁺ = M`, read on `R_k = 𝒪 ⊗[I] R` (the
weight-`k` Hecke algebra `𝐓_k(N)_𝔪 ⊗ 𝒪̃_P` by `Hyp.HidaControlGL2`) and its `q`-new quotient `R_k ⧸ 𝔞_k`:
`η(R_k, λ_f) = (ϖ^{t_f(q)}) · η(R_k ⧸ 𝔞_k, λ′_f)` with `η(R_k ⧸ 𝔞_k, λ′_f) ≠ 0` (KO's `ord` identity over the DVR `𝒪̃_P`,
both congruence ideals non-zero because `f` is a newform). `(ϖ^t)` is written `𝔪^t` (equal in a DVR).

Inputs of [KO, Thm 1.1] carried explicitly: (H0) (`Defect.H0 p q M`, guard) and (H0⁻) (`D.H0minus p q`, guard; KO's
condition (6)); `p ∤ N`, `(N⁺, N⁻) = 1`, `N⁻ = q` squarefree are part of (H0). Not representable on the abstract data
and stated here: `f = F_P` is a `q`-new newform of level `N = qM` and weight `2 ≤ k ≤ p - 1` (the point of (P)), and
(H2) for `ρ̄_f`.

Source: Kim–Ota (2019) Thm 1.1, p. 1 (Def. 2.11, p. 6 for the `N⁻`-new congruence ideal); at `k = 2` Pollack–Weston
(2006) Thm 6.8, p. 21. Status: *cited*, not discharged. Owner: S06-L8a. Consumers: `Defect.cor_fixed` (S06-L9b) →
`Defect.defect_formula` (S06-L9a, the (H0⁻) branch of step (4)).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `thm:s06-KO` (`s06-KO`) at the point `P` (`f = F_P`, `N⁻ = q`, `N⁺ = M`): under (H0) and (H0⁻) (explicit guards),
`η(R_k, λ_f) = 𝔪^{t_f(q)} · η(R_k ⧸ 𝔞_k, λ′_f)` and `η(R_k ⧸ 𝔞_k, λ′_f) ≠ 0`, with `R_k = 𝒪 ⊗[I] R`.
Source: [KO, Thm 1.1, p. 1; Def. 2.11, p. 6], [PW, Thm 6.8, p. 21] at `k = 2`. Discharge: *cited*. Owner: S06-L8a. -/
def KimOta (D : Defect.Setting Λ I T 𝒪 G) (p q M : ℕ) : Prop :=
  Defect.H0 p q M → D.H0minus p q →
    CommAlg.congruenceIdeal D.lamk =
        IsLocalRing.maximalIdeal 𝒪 ^ D.t * CommAlg.congruenceIdeal (A := 𝒪)
            (S := D.Rk ⧸ D.𝔞k) D.lam'k ∧
      CommAlg.congruenceIdeal (A := 𝒪) (S := D.Rk ⧸ D.𝔞k) D.lam'k ≠ ⊥

end Langlandscape.Hyp
