/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Hypothesis `KimOtaRT`: the inclusion `𝔠_q(f) ⊆ (ϖ^{t_f(q)})` under (Lev_M) (S06-L8a)

`mathematics/chapters/s06/s06-m5.tex`, `prop:s06-levM` under `hyp:s06-levMp`, output of step (4)–(5):
under (H0) and (Lev_M), `𝔠_q(f) ⊆ (ϖ^{t_f(q)})`, **inclusion only** (the squeeze of `thm:s06-defect` step (5) needs no more).
No condition `q ≢ -1 mod p` is used. `(ϖ^t)` is written `𝔪^t`; `𝔠_q(f) = D.cqk` lives on `R_k = 𝒪 ⊗[I] R`.
Inputs carried explicitly: (H0) (`Defect.H0 p q M`, guard). Not representable and stated here: (Lev_M) (`hyp:s06-H`), (H2)
for `ρ̄_f`, `f = F_P` a `q`-new newform of level `N = qM` and weight `2 ≤ k ≤ p - 1`.
Source: Kim–Ota (2019) Thm 3.14, p. 12 (refined `R = 𝐓`), via the chapter's `prop:s06-levM` under `hyp:s06-levMp`.
Scope (the (Lev) route): the inclusion `𝔠_q(f) ⊆ 𝔪^t` holds by `prop:s06-levM` for `M = 1`, for (F1) (`M` squarefree, `ρ̄`
unramified at all `ℓ ∣ M`, no `ℓ ≡ −1`) and for (F1′) (some `ℓ ≡ −1`, under our reading R4 of KO Thm 3.14, not KO's
text); it is open for `N(ρ̄) > 1`. **Inclusion only.** (Lev′_M) (`hyp:s06-levMp`) is not a Lean guard.
Status: *cited*, not discharged. Owner: S06-L8a. Consumer: `Defect.defect_formula` (S06-L9a, the (Lev_M) branch).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Hyp

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

/-- `prop:s06-levM` (`s06-levM`), the (Lev_M) route of step (4) of `thm:s06-defect`: under (H0) (explicit guard),
`𝔠_q(f) ⊆ 𝔪^{t_f(q)} = (ϖ^{t_f(q)})` — **inclusion only**. Source: [KO, Thm 3.14, p. 12]; `prop:s06-levM`
(`mathematics/chapters/s06/s06-m5.tex`, `hyp:s06-levMp`): `M = 1`, (F1), (F1′) (our reading R4 of KO Thm 3.14), open for
`N(ρ̄) > 1`.
Discharge: *cited*. Owner: S06-L8a. -/
def KimOtaRT (D : Defect.Setting Λ I T 𝒪 G) (p q M : ℕ) : Prop :=
  Defect.H0 p q M → D.cqk ≤ IsLocalRing.maximalIdeal 𝒪 ^ D.t

end Langlandscape.Hyp
