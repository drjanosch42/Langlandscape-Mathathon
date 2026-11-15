/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Hyp.PadicOrdDecomp

/-! Non-vacuity tests for `Langlandscape.Ordinary.Projector` (S04-L1): `T = p` and `T = 1` on `ℤ_[p]`. -/

@[expose] public section

set_option autoImplicit false

open scoped Pointwise

namespace LanglandscapeTests.S04.Projector

open Langlandscape.Ordinary

variable (p : ℕ) [Fact p.Prime]

/-- `def:s04-e` (`s04-e`), test data: `ℤ_[p]` is `p`-adically separated, `⋂ₖ pᵏ ℤ_[p] = 0`. -/
theorem padic_smul_top_separated :
    ⨅ k : ℕ, ((p : ℤ_[p]) ^ k) • (⊤ : Submodule ℤ_[p] ℤ_[p]) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hk := (Submodule.mem_iInf _).1 hx (x.valuation + 1)
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hk
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hy, smul_zero])
  rw [smul_eq_mul] at hy
  have hv := PadicInt.valuation_p_pow_mul (x.valuation + 1) y hy0
  rw [hy] at hv
  omega

/-- `def:s04-e` (`s04-e`), test: for `T = p` on `ℤ_[p]` (topologically nilpotent), `ordPart T = ⊥`. -/
theorem ordPart_smul_p_eq_bot :
    ordPart ((p : ℤ_[p]) • (1 : Module.End ℤ_[p] ℤ_[p])) = ⊥ := by
  refine ordPart_eq_bot_of_topNilpotent (p := (p : ℤ_[p])) (fun k => ⟨k, ?_⟩)
    (padic_smul_top_separated p)
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  rw [smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), test: for `T = p` on `ℤ_[p]`, `nilPart p T = ⊤`. -/
theorem nilPart_smul_p_eq_top :
    nilPart (p : ℤ_[p]) ((p : ℤ_[p]) • (1 : Module.End ℤ_[p] ℤ_[p])) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_nilPart]
  intro k
  refine ⟨k, ?_⟩
  rw [smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), test: `T = p` on `ℤ_[p]` has an ordinary decomposition (`⊥ ⊕ ⊤`). -/
theorem hasOrdDecomp_smul_p :
    HasOrdDecomp (p : ℤ_[p]) ((p : ℤ_[p]) • (1 : Module.End ℤ_[p] ℤ_[p])) := by
  unfold HasOrdDecomp
  rw [ordPart_smul_p_eq_bot, nilPart_smul_p_eq_top]
  exact isCompl_bot_top

/-- `def:s04-e` (`s04-e`), test: for `T = 1` on `ℤ_[p]`, `ordPart T = ⊤`. -/
theorem ordPart_one_eq_top : ordPart (1 : Module.End ℤ_[p] ℤ_[p]) = ⊤ :=
  ordPart_eq_top_of_isUnit isUnit_one

/-- `def:s04-e` (`s04-e`), test: for `T = 1` on `ℤ_[p]`, `nilPart p T = ⊥` (separatedness). -/
theorem nilPart_one_eq_bot : nilPart (p : ℤ_[p]) (1 : Module.End ℤ_[p] ℤ_[p]) = ⊥ := by
  rw [eq_bot_iff, ← padic_smul_top_separated p]
  intro x hx
  rw [Submodule.mem_iInf]
  intro k
  obtain ⟨n, hn⟩ := mem_nilPart.1 hx k
  rwa [one_pow, Module.End.one_apply] at hn

/-- `def:s04-e` (`s04-e`), test: `T = 1` on `ℤ_[p]` has an ordinary decomposition (`⊤ ⊕ ⊥`). -/
theorem hasOrdDecomp_one : HasOrdDecomp (p : ℤ_[p]) (1 : Module.End ℤ_[p] ℤ_[p]) := by
  unfold HasOrdDecomp
  rw [ordPart_one_eq_top, nilPart_one_eq_bot]
  exact isCompl_top_bot

/-- `def:s04-e` (`s04-e`), shape test: `Hyp.PadicOrdDecomp p` specialises to `ℤ_[p]` itself. -/
theorem padicOrdDecomp_self (hdec : Langlandscape.Hyp.PadicOrdDecomp p)
    (T : Module.End ℤ_[p] ℤ_[p]) : HasOrdDecomp (p : ℤ_[p]) T :=
  hdec ℤ_[p] T

end LanglandscapeTests.S04.Projector
