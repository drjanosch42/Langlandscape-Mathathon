/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# The ordinary projector (S04-L1, design D-e)

`mathematics/chapters/s04/ordinary.tex`, `def:s04-e` (Step 5: the form used in Lean).

**Generality.** `R` is a commutative ring with a *fixed element* `p : R`, `M` an `R`-module and
`T : Module.End R M`. We put
* `ordPart T := ⨅ n, LinearMap.range (T ^ n)` (`= ⋂ₙ Tⁿ M`; independent of `p`),
* `nilPart p T := {m | ∀ k, ∃ n, (T ^ n) m ∈ (p ^ k : R) • ⊤}` (the `p`-adically topologically nilpotent part),
* `HasOrdDecomp p T := IsCompl (ordPart T) (nilPart p T)`, and, under it, the projector
  `ordProj p T h : Module.End R M` onto `ordPart T` along `nilPart p T` (`e_T` of `def:s04-e`).

Downstream instances: `R = ℤ_[p]` with `p := (p : ℤ_[p])` (f.g. modules, S04-L3, `Hyp.PadicOrdDecomp`), and
`R = ZMod (p ^ m)` with `p := (p : ZMod (p ^ m))` (finite length, S04-L2; there `p` is nilpotent, so `nilPart` is the
generalized kernel `⋃ₙ ker Tⁿ`).

Functoriality (`ordPart_map`, `nilPart_map`, `ordProj_map`, `ordProj_comm`) and exactness (`ordPart_exact`) are proved for
`T`-equivariant maps (`f ∘ₗ T = T' ∘ₗ f`) between modules **with** `HasOrdDecomp`; the decomposition itself is a theorem in
the two instances above (S04-L2, S04-L3). Status: *formalized*.
-/

@[expose] public section

set_option autoImplicit false

open scoped Pointwise

namespace Langlandscape.Ordinary

noncomputable section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]

/-! ### The two parts -/

/-- `def:s04-e` (`s04-e`), Step 5 (D-e): the ordinary part `ordPart T = ⋂ₙ Tⁿ M` of an endomorphism `T`. -/
def ordPart (T : Module.End R M) : Submodule R M :=
  ⨅ n : ℕ, LinearMap.range (T ^ n)

/-- `def:s04-e` (`s04-e`): membership in `ordPart T`: `m ∈ Tⁿ M` for every `n`. -/
theorem mem_ordPart {T : Module.End R M} {m : M} :
    m ∈ ordPart T ↔ ∀ n : ℕ, ∃ y : M, (T ^ n) y = m := by
  simp only [ordPart, Submodule.mem_iInf, LinearMap.mem_range]

/-- `def:s04-e` (`s04-e`), auxiliary: if `Tⁿ m ∈ pᵏ M` then `T^(j+n) m ∈ pᵏ M` (as `pᵏ M` is `T`-stable). -/
theorem pow_add_mem_smul_top (p : R) (T : Module.End R M) {m : M} {n k : ℕ}
    (h : (T ^ n) m ∈ (p ^ k : R) • (⊤ : Submodule R M)) (j : ℕ) :
    (T ^ (j + n)) m ∈ (p ^ k : R) • (⊤ : Submodule R M) := by
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
  rw [pow_add, Module.End.mul_apply, ← hy, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), Step 5 (D-e): the topologically nilpotent part
`nilPart p T = {m | ∀ k, ∃ n, Tⁿ m ∈ pᵏ M}` (for `p` nilpotent in `R`: the generalized kernel of `T`). -/
def nilPart (p : R) (T : Module.End R M) : Submodule R M where
  carrier := {m | ∀ k : ℕ, ∃ n : ℕ, (T ^ n) m ∈ (p ^ k : R) • (⊤ : Submodule R M)}
  add_mem' := by
    intro a b ha hb k
    obtain ⟨n₁, h₁⟩ := ha k
    obtain ⟨n₂, h₂⟩ := hb k
    refine ⟨n₂ + n₁, ?_⟩
    rw [map_add]
    refine add_mem (pow_add_mem_smul_top p T h₁ n₂) ?_
    rw [add_comm n₂ n₁]
    exact pow_add_mem_smul_top p T h₂ n₁
  zero_mem' := by
    intro k
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact zero_mem _
  smul_mem' := by
    intro c m hm k
    obtain ⟨n, h⟩ := hm k
    refine ⟨n, ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ c h

/-- `def:s04-e` (`s04-e`): membership in `nilPart p T`. -/
theorem mem_nilPart {p : R} {T : Module.End R M} {m : M} :
    m ∈ nilPart p T ↔ ∀ k : ℕ, ∃ n : ℕ, (T ^ n) m ∈ (p ^ k : R) • (⊤ : Submodule R M) :=
  Iff.rfl

/-- `def:s04-e` (`s04-e`), Step 5 (D-e): `T` has an ordinary decomposition, `M = ordPart T ⊕ nilPart p T`. This is a theorem
for modules of finite length (S04-L2) and f.g. `ℤ_[p]`-modules (S04-L3); abstract lemmas take it as an argument. -/
def HasOrdDecomp (p : R) (T : Module.End R M) : Prop :=
  IsCompl (ordPart T) (nilPart p T)

/-- `def:s04-e` (`s04-e`), D-e: the ordinary projector `e_T`, the projection onto `ordPart T` along `nilPart p T`,
as an endomorphism of `M` (Mathlib `Submodule.projection`, the non-deprecated form of `linearProjOfIsCompl`). -/
def ordProj (p : R) (T : Module.End R M) (h : HasOrdDecomp p T) : Module.End R M :=
  (ordPart T).projection (nilPart p T) h

/-! ### Basic properties of `ordProj` -/

section Proj

variable {p : R} {T : Module.End R M}

/-- `def:s04-e` (`s04-e`): `e_T m ∈ ordPart T`. -/
theorem ordProj_apply_mem (h : HasOrdDecomp p T) (m : M) : ordProj p T h m ∈ ordPart T :=
  Submodule.projection_apply_mem h m

/-- `def:s04-e` (`s04-e`): `e_T` is the identity on `ordPart T`. -/
theorem ordProj_apply_of_mem_ordPart (h : HasOrdDecomp p T) {m : M} (hm : m ∈ ordPart T) :
    ordProj p T h m = m :=
  Submodule.projection_apply_of_mem_left h hm

/-- `def:s04-e` (`s04-e`): `e_T` vanishes on `nilPart p T`. -/
theorem ordProj_apply_of_mem_nilPart (h : HasOrdDecomp p T) {m : M} (hm : m ∈ nilPart p T) :
    ordProj p T h m = 0 :=
  Submodule.projection_apply_of_mem_right h hm

/-- `def:s04-e` (`s04-e`): `ker e_T = nilPart p T`. -/
theorem ker_ordProj (h : HasOrdDecomp p T) : LinearMap.ker (ordProj p T h) = nilPart p T :=
  Submodule.ker_projection h

/-- `def:s04-e` (`s04-e`): `m = e_T m + m'` with `m' ∈ nilPart p T` (the decomposition `M = e_T M ⊕ (1 - e_T) M`). -/
theorem ordProj_add_nil (h : HasOrdDecomp p T) (m : M) :
    ordProj p T h m + (nilPart p T).projection (ordPart T) (IsCompl.symm h) m = m :=
  Submodule.projection_add_projection_eq_self h m

/-- `def:s04-e` (`s04-e`): the ordinary projector is idempotent, `e_T * e_T = e_T`. -/
theorem ordProj_idem (h : HasOrdDecomp p T) : ordProj p T h * ordProj p T h = ordProj p T h :=
  (Submodule.isIdempotentElem_projection h).eq

end Proj

/-! ### Functoriality -/

/-- `def:s04-e` (`s04-e`), auxiliary: an equivariant map `f ∘ₗ T = T' ∘ₗ f` satisfies `f (Tⁿ x) = T'ⁿ (f x)`. -/
theorem map_pow_apply {T : Module.End R M} {T' : Module.End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T = T' ∘ₗ f) (n : ℕ) (x : M) : f ((T ^ n) x) = (T' ^ n) (f x) := by
  have h := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf.symm n) x
  simp only [LinearMap.comp_apply] at h
  exact h.symm

/-- `def:s04-e` (`s04-e`), functoriality: an equivariant map `f ∘ₗ T = T' ∘ₗ f` maps `ordPart T` into `ordPart T'`. -/
theorem ordPart_map {T : Module.End R M} {T' : Module.End R N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ T = T' ∘ₗ f) : ordPart T ≤ (ordPart T').comap f := by
  intro m hm
  rw [Submodule.mem_comap, mem_ordPart]
  intro n
  obtain ⟨y, hy⟩ := mem_ordPart.1 hm n
  exact ⟨f y, by rw [← map_pow_apply hf n y, hy]⟩

/-- `def:s04-e` (`s04-e`), functoriality: an equivariant map `f ∘ₗ T = T' ∘ₗ f` maps `nilPart p T` into
`nilPart p T'`. -/
theorem nilPart_map (p : R) {T : Module.End R M} {T' : Module.End R N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ T = T' ∘ₗ f) : nilPart p T ≤ (nilPart p T').comap f := by
  intro m hm
  rw [Submodule.mem_comap, mem_nilPart]
  intro k
  obtain ⟨n, hn⟩ := mem_nilPart.1 hm k
  refine ⟨n, ?_⟩
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hn
  rw [← map_pow_apply hf n m, ← hy, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- `def:s04-e` (`s04-e`), functoriality (Step 2/3): an equivariant map commutes with the ordinary projectors,
`f ∘ₗ e_T = e_{T'} ∘ₗ f`. -/
theorem ordProj_map {p : R} {T : Module.End R M} {T' : Module.End R N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ T = T' ∘ₗ f) (h : HasOrdDecomp p T) (h' : HasOrdDecomp p T') :
    f ∘ₗ ordProj p T h = ordProj p T' h' ∘ₗ f := by
  refine LinearMap.ext fun m => ?_
  have hm := ordProj_add_nil h m
  have ha : f (ordProj p T h m) ∈ ordPart T' := ordPart_map f hf (ordProj_apply_mem h m)
  have hb : f ((nilPart p T).projection (ordPart T) (IsCompl.symm h) m) ∈ nilPart p T' :=
    nilPart_map p f hf (Submodule.projection_apply_mem (IsCompl.symm h) m)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_rhs => rw [← hm]
  rw [map_add f, map_add (ordProj p T' h'), ordProj_apply_of_mem_ordPart h' ha,
    ordProj_apply_of_mem_nilPart h' hb, add_zero]

/-- `def:s04-e` (`s04-e`): `e_T` commutes with every endomorphism `S` commuting with `T`. -/
theorem ordProj_comm {p : R} {T : Module.End R M} (h : HasOrdDecomp p T) {S : Module.End R M}
    (hS : Commute S T) : S * ordProj p T h = ordProj p T h * S :=
  ordProj_map S hS.eq h h

/-- `def:s04-e` (`s04-e`): the restriction `ordPart T →ₗ ordPart T'` of an equivariant map (`f ↦ e f`). -/
def ordRestrict {T : Module.End R M} {T' : Module.End R N} (f : M →ₗ[R] N) (hf : f ∘ₗ T = T' ∘ₗ f) :
    ordPart T →ₗ[R] ordPart T' :=
  f.restrict fun _ hx => ordPart_map f hf hx

/-- `def:s04-e` (`s04-e`): `ordRestrict f hf x = f x` in `N`. -/
theorem ordRestrict_apply {T : Module.End R M} {T' : Module.End R N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ T = T' ∘ₗ f) (x : ordPart T) : (ordRestrict f hf x : N) = f x :=
  rfl

/-! ### Exactness -/

/-- `def:s04-e` (`s04-e`), Step 4 (exactness of `M ↦ e_T M`): for a short exact sequence `0 → M → N → P → 0` of
`T`-equivariant maps between modules each having `HasOrdDecomp`, the restricted sequence
`0 → ordPart T₁ → ordPart T₂ → ordPart T₃ → 0` is short exact. -/
theorem ordPart_exact {p : R} {T₁ : Module.End R M} {T₂ : Module.End R N} {T₃ : Module.End R P}
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : f ∘ₗ T₁ = T₂ ∘ₗ f) (hg : g ∘ₗ T₂ = T₃ ∘ₗ g)
    (h₁ : HasOrdDecomp p T₁) (h₂ : HasOrdDecomp p T₂) (h₃ : HasOrdDecomp p T₃)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    Function.Injective (ordRestrict f hf) ∧ Function.Exact (ordRestrict f hf) (ordRestrict g hg) ∧
      Function.Surjective (ordRestrict g hg) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply hinj
    exact (ordRestrict_apply f hf x).symm.trans
      ((congrArg Subtype.val hxy).trans (ordRestrict_apply f hf y))
  · intro y
    constructor
    · intro hy
      have hy0 : g (y : N) = 0 :=
        (ordRestrict_apply g hg y).symm.trans ((congrArg Subtype.val hy).trans rfl)
      obtain ⟨x, hx⟩ := (hex (y : N)).1 hy0
      refine ⟨⟨ordProj p T₁ h₁ x, ordProj_apply_mem h₁ x⟩, Subtype.ext ?_⟩
      show f (ordProj p T₁ h₁ x) = (y : N)
      have hc := LinearMap.congr_fun (ordProj_map f hf h₁ h₂) x
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
      rw [hc, hx, ordProj_apply_of_mem_ordPart h₂ y.2]
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      show g (f (x : M)) = 0
      exact (hex (f (x : M))).2 ⟨(x : M), rfl⟩
  · intro z
    obtain ⟨y, hy⟩ := hsurj (z : P)
    refine ⟨⟨ordProj p T₂ h₂ y, ordProj_apply_mem h₂ y⟩, Subtype.ext ?_⟩
    show g (ordProj p T₂ h₂ y) = (z : P)
    have hc := LinearMap.congr_fun (ordProj_map g hg h₂ h₃) y
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc, hy, ordProj_apply_of_mem_ordPart h₃ z.2]

/-! ### Extreme cases -/

/-- `def:s04-e` (`s04-e`): if `T` is topologically nilpotent (`∀ k, ∃ n, Tⁿ M ⊆ pᵏ M`) and `M` is `p`-adically separated
(`⋂ₖ pᵏ M = 0`), then `ordPart T = ⊥` (e.g. `T = p` on `ℤ_[p]`). -/
theorem ordPart_eq_bot_of_topNilpotent {p : R} {T : Module.End R M}
    (hT : ∀ k : ℕ, ∃ n : ℕ, LinearMap.range (T ^ n) ≤ (p ^ k : R) • (⊤ : Submodule R M))
    (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M) = ⊥) : ordPart T = ⊥ := by
  rw [eq_bot_iff, ← hsep]
  show ⨅ n : ℕ, LinearMap.range (T ^ n) ≤ ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R M)
  refine le_iInf fun k => ?_
  obtain ⟨n, hn⟩ := hT k
  exact (iInf_le (fun n : ℕ => LinearMap.range (T ^ n)) n).trans hn

/-- `def:s04-e` (`s04-e`): if `T` is invertible then `ordPart T = ⊤`. -/
theorem ordPart_eq_top_of_isUnit {T : Module.End R M} (hT : IsUnit T) : ordPart T = ⊤ := by
  rw [eq_top_iff]
  show ⊤ ≤ ⨅ n : ℕ, LinearMap.range (T ^ n)
  refine le_iInf fun n => ?_
  exact (LinearMap.range_eq_top.2 ((Module.End.isUnit_iff _).1 (hT.pow n)).2).ge

end

end Langlandscape.Ordinary
