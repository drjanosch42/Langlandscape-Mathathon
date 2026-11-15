/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.Projector
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Finite-length instance of the ordinary decomposition (S04-L2)

`mathematics/chapters/s04/ordinary.tex`, `def:s04-e` (finite case; design D-e).

If `p ^ m = 0` in `R` and `M` is Artinian and Noetherian, then `nilPart p T = ⨆ₙ ker Tⁿ`, and Mathlib's Fitting
decomposition (`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`) gives `HasOrdDecomp p T`. For a *finite* module `M`
(e.g. over `ZMod (p ^ m)`) the projector is a power of `T`: `ordProj p T h = T ^ n` for some `n > 0`
(`ordProj_eq_pow`; `n` = a multiple of the period of `T` on `ordPart T`, at least the nilpotency index on `nilPart p T`).
Status: *formalized*, unconditional.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Ordinary

noncomputable section

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- `def:s04-e` (`s04-e`), finite case: if `p ^ m = 0` then `nilPart p T` is the generalized kernel `⨆ₙ ker Tⁿ`. -/
theorem nilPart_eq_iSup_ker {p : R} {m : ℕ} (hp : p ^ m = 0) (T : Module.End R M) :
    nilPart p T = ⨆ n : ℕ, LinearMap.ker (T ^ n) := by
  refine le_antisymm ?_ (iSup_le fun n x hx => ?_)
  · intro x hx
    obtain ⟨n, hn⟩ := mem_nilPart.1 hx m
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hn
    have h0 : (T ^ n) x = 0 := by rw [← hy, hp, zero_smul]
    exact Submodule.mem_iSup_of_mem n (LinearMap.mem_ker.2 h0)
  · rw [mem_nilPart]
    intro k
    exact ⟨n, by rw [LinearMap.mem_ker.1 hx]; exact zero_mem _⟩

/-- `def:s04-e` (`s04-e`), finite case: for a module of finite length on which `p` is nilpotent, every endomorphism
has an ordinary decomposition (Fitting). -/
theorem hasOrdDecomp_of_finiteLength {p : R} {m : ℕ} (hp : p ^ m = 0) [IsArtinian R M] [IsNoetherian R M]
    (T : Module.End R M) : HasOrdDecomp p T := by
  unfold HasOrdDecomp
  rw [nilPart_eq_iSup_ker hp T]
  exact (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow T).symm

/-- `def:s04-e` (`s04-e`), finite case: for `n` large, `nilPart p T = ker Tⁿ` (and `ordPart T = range Tⁿ`). -/
theorem exists_nilPart_eq_ker_pow {p : R} {m : ℕ} (hp : p ^ m = 0) [IsArtinian R M] [IsNoetherian R M]
    (T : Module.End R M) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      nilPart p T = LinearMap.ker (T ^ n) ∧ ordPart T = LinearMap.range (T ^ n) := by
  obtain ⟨N₁, h₁⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_iSup_ker_pow_eq T)
  obtain ⟨N₂, h₂⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_iInf_range_pow_eq T)
  refine ⟨max N₁ N₂, fun n hn => ⟨?_, ?_⟩⟩
  · rw [nilPart_eq_iSup_ker hp T]
    exact h₁ n (le_trans (le_max_left _ _) hn)
  · exact h₂ n (le_trans (le_max_right _ _) hn)

/-- `def:s04-e` (`s04-e`), finite case, auxiliary: a finite module is Noetherian. -/
theorem isNoetherian_of_finite_module [Finite M] : IsNoetherian R M := by
  haveI : Finite (Submodule R M) :=
    Finite.of_injective (fun N : Submodule R M => (N : Set M)) SetLike.coe_injective
  exact isNoetherian_iff.2 inferInstance

/-- `def:s04-e` (`s04-e`), finite case: the Fitting decomposition for a finite module on which `p` is nilpotent. -/
theorem hasOrdDecomp_of_finite {p : R} {m : ℕ} (hp : p ^ m = 0) [Finite M] (T : Module.End R M) :
    HasOrdDecomp p T := by
  haveI : IsArtinian R M := isArtinian_of_finite
  haveI : IsNoetherian R M := isNoetherian_of_finite_module
  exact hasOrdDecomp_of_finiteLength hp T

/-- `def:s04-e` (`s04-e`), finite case: the ordinary projector of a finite module (with `p` nilpotent) is a positive
power of `T`: `e_T = Tⁿ` for some `n > 0` (`n` a multiple of the order of `T` on `ordPart T` and at least the
nilpotency index of `T` on `nilPart p T`). -/
theorem ordProj_eq_pow {p : R} {m : ℕ} (hp : p ^ m = 0) [Finite M] {T : Module.End R M}
    (h : HasOrdDecomp p T) : ∃ n : ℕ, 0 < n ∧ ordProj p T h = T ^ n := by
  haveI : IsArtinian R M := isArtinian_of_finite
  haveI : IsNoetherian R M := isNoetherian_of_finite_module
  obtain ⟨N, hN⟩ := exists_nilPart_eq_ker_pow hp T
  haveI : Finite (Module.End R M) :=
    Finite.of_injective (fun f : Module.End R M => (f : M → M)) DFunLike.coe_injective
  obtain ⟨a, d, hd, had⟩ : ∃ a d : ℕ, 0 < d ∧ T ^ (a + d) = T ^ a := by
    obtain ⟨x, y, hxy, hxy'⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => T ^ k)
    have h' : T ^ x = T ^ y := hxy'
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · refine ⟨x, y - x, by omega, ?_⟩
      rw [show x + (y - x) = y by omega]
      exact h'.symm
    · refine ⟨y, x - y, by omega, ?_⟩
      rw [show y + (x - y) = x by omega]
      exact h'
  have step : ∀ k : ℕ, a ≤ k → T ^ (k + d) = T ^ k := by
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show a + t + d = (a + d) + t by omega, pow_add, had, ← pow_add]
  have hper : ∀ k : ℕ, a ≤ k → ∀ j : ℕ, T ^ (k + j * d) = T ^ k := by
    intro k hk j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.succ_mul, ← add_assoc, step (k + j * d) (le_trans hk (Nat.le_add_right _ _)), ih]
  obtain ⟨n, hnd⟩ : ∃ n : ℕ, n = (a + N + 1) * d := ⟨_, rfl⟩
  have hge : a + N + 1 ≤ n := by
    rw [hnd]
    calc a + N + 1 = (a + N + 1) * 1 := (mul_one _).symm
      _ ≤ (a + N + 1) * d := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hd)
  have han : a ≤ n := by omega
  have hNn : N ≤ n := by omega
  have hnn : T ^ (n + n) = T ^ n := by
    have := hper n han (a + N + 1)
    rwa [← hnd] at this
  refine ⟨n, by omega, LinearMap.ext fun x => ?_⟩
  have hx := ordProj_add_nil h x
  have hu : ordProj p T h x ∈ ordPart T := ordProj_apply_mem h x
  have h' : IsCompl (ordPart T) (nilPart p T) := h
  have hv : (nilPart p T).projection (ordPart T) h'.symm x ∈ nilPart p T :=
    Submodule.projection_apply_mem h'.symm x
  have h2 : (T ^ n) ((nilPart p T).projection (ordPart T) h'.symm x) = 0 := by
    have hker : (nilPart p T).projection (ordPart T) h'.symm x ∈ LinearMap.ker (T ^ n) :=
      (SetLike.ext_iff.1 (hN n hNn).1 _).1 hv
    exact LinearMap.mem_ker.1 hker
  have h1 : (T ^ n) (ordProj p T h x) = ordProj p T h x := by
    obtain ⟨z, hz⟩ := mem_ordPart.1 hu n
    rw [← hz, ← Module.End.mul_apply, ← pow_add, hnn]
  calc ordProj p T h x = (T ^ n) (ordProj p T h x) := h1.symm
    _ = (T ^ n) (ordProj p T h x) +
        (T ^ n) ((nilPart p T).projection (ordPart T) h'.symm x) := by rw [h2, add_zero]
    _ = (T ^ n) x := by rw [← map_add, hx]

end General

section ZModPow

/-- `def:s04-e` (`s04-e`), finite case: `p` is nilpotent in `ZMod (p ^ m)`, `(p : ZMod (p ^ m)) ^ m = 0`. -/
theorem natCast_pow_eq_zero (p m : ℕ) : ((p : ℕ) : ZMod (p ^ m)) ^ m = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

/-- `def:s04-e` (`s04-e`), finite case, unconditional: every endomorphism of a finite `ZMod (p ^ m)`-module has an
ordinary decomposition (with respect to `p := (p : ZMod (p ^ m))`). -/
theorem hasOrdDecomp_zmodPow (p m : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M] [Finite M]
    (T : Module.End (ZMod (p ^ m)) M) : HasOrdDecomp ((p : ℕ) : ZMod (p ^ m)) T :=
  hasOrdDecomp_of_finite (natCast_pow_eq_zero p m) T

/-- `def:s04-e` (`s04-e`), finite case: over `ZMod (p ^ m)` the ordinary projector of a finite module is a positive
power of `T`. -/
theorem ordProj_eq_pow_zmodPow (p m : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M] [Finite M]
    (T : Module.End (ZMod (p ^ m)) M) :
    ∃ n : ℕ, 0 < n ∧ ordProj ((p : ℕ) : ZMod (p ^ m)) T (hasOrdDecomp_zmodPow p m T) = T ^ n :=
  ordProj_eq_pow (natCast_pow_eq_zero p m) (hasOrdDecomp_zmodPow p m T)

end ZModPow

end

end Langlandscape.Ordinary
