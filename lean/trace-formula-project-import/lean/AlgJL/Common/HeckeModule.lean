import AlgJL.Meta.Tag
import Definitions.Def_LocalLanglands_HeckePair
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.BigOperators

/-!
# The Hecke algebra acting on equivariant functions (Q3 U3, items 21, 22; area `X.hmod`)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §3 (items 21, 21a, 22 of `docs/sprints/Q3-plan.md` §1.2), generic in
a group `G`, a subgroup `U` and a group `Γ` mapping to `G` (lead decision P-L3: area `X.hmod`).

Design (plan §1.1 item 4):
* the Hecke algebra is the vendored `HeckePair.HeckeAlgebra U R₀` (tagged `X.hpair.*` in `GL2TF.VolI.P1.Spherical`):
  bi-`U`-invariant `R₀`-valued functions supported on finitely many cosets `yU`, with convolution
  `(φ₁ ∗ φ₂)(x) = Σ_{yU ∈ G/U} φ₁(y) φ₂(y⁻¹x)`;
* the action `(φ · f)(x) = Σ_{yU ∈ G/U} φ(y) f(xy)` is defined for **every** function `φ : G → R₀` and every
  `f : G → V` (representatives `Quotient.out`); it is a `finsum`, hence the junk value `0` when the support is infinite.
  The theorem `X.hmod.thm:hecke-module-action` states the module laws on equivariant functions and Hecke functions;
* equivariant functions: `f(ι(γ) x u) = ρ(γ) f(x)` for `γ ∈ Γ`, `x ∈ G`, `u ∈ U`, where `ρ : Γ → End_R(V)` is any map
  (multiplicativity of `ρ` is not needed for the module laws; `ρ(1) = 1` is a hypothesis where needed).

No project notation. Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.HeckeModule

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

/-- The `R`-submodule of functions `f : G → V` with `f(ι(γ) x u) = ρ(γ) f(x)` for all `γ ∈ Γ`, `x ∈ G`, `u ∈ U`. -/
@[tf_id "X.hmod.def:equivariant-functions"]
def equivariantFunctions (R : Type*) [CommRing R] {V : Type*} [AddCommGroup V] [Module R V] (ι : Γ →* G)
    (U : Subgroup G) (ρ : Γ → Module.End R V) : Submodule R (G → V) where
  carrier := {f | ∀ (γ : Γ) (x u : G), u ∈ U → f (ι γ * x * u) = ρ γ (f x)}
  zero_mem' := by
    intro γ x u _
    simp
  add_mem' := by
    intro f g hf hg γ x u hu
    simp [hf γ x u hu, hg γ x u hu]
  smul_mem' := by
    intro c f hf γ x u hu
    simp [hf γ x u hu]

/-- The action `(φ · f)(x) = Σ_{yU ∈ G/U} φ(y) f(xy)` of a function `φ : G → R₀` on a function `f : G → V`
(a `finsum` over `G/U`, with the representatives `Quotient.out`). -/
@[tf_id "X.hmod.def:hecke-module-action"]
noncomputable def heckeAct {U : Subgroup G} {R₀ : Type*} [CommRing R₀] {V : Type*} [AddCommGroup V] [Module R₀ V]
    (φ : G → R₀) (f : G → V) : G → V :=
  fun x => ∑ᶠ c : G ⧸ U, φ (Quotient.out c) • f (x * Quotient.out c)


section CosetSums

variable {U : Subgroup G} {M : Type*}

theorem coset_apply_out_eq_of_mul_right {τ : G → M} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (g : G) :
    τ (Quotient.out (QuotientGroup.mk g : G ⧸ U)) = τ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hτ g u u.2]

theorem coset_finsum_translate [AddCommMonoid M] {τ : G → M} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (y : G) :
    ∑ᶠ c : G ⧸ U, τ (y * Quotient.out c) = ∑ᶠ c : G ⧸ U, τ (Quotient.out c) := by
  calc ∑ᶠ c : G ⧸ U, τ (y * Quotient.out c)
      = ∑ᶠ c : G ⧸ U, τ (Quotient.out ((MulAction.toPerm y : Equiv.Perm (G ⧸ U)) c)) := by
        refine finsum_congr fun c => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, coset_apply_out_eq_of_mul_right hτ]
        obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
        rw [hu, ← mul_assoc, hτ _ u u.2]
    _ = _ := finsum_comp_equiv (MulAction.toPerm y : Equiv.Perm (G ⧸ U)) (f := fun c : G ⧸ U => τ (Quotient.out c))

end CosetSums

section ActionLemmas

variable {U : Subgroup G} {R₀ : Type*} [CommRing R₀] {V : Type*} [AddCommGroup V] [Module R₀ V]

theorem heckeAct_support_finite (φ : HeckePair.HeckeAlgebra U R₀) (f : G → V) (x : G) :
    (Function.support fun c : G ⧸ U => (φ : G → R₀) (Quotient.out c) • f (x * Quotient.out c)).Finite :=
  (HeckePair.finite_cosets φ).subset fun c hc =>
    ⟨Quotient.out c, fun h => hc (by simp [h]), QuotientGroup.out_eq' c⟩

theorem heckeAct_term_mul_right (φ : HeckePair.HeckeAlgebra U R₀) {f : G → V}
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) (x : G) :
    ∀ g, ∀ u ∈ U, (φ : G → R₀) (g * u) • f (x * (g * u)) = (φ : G → R₀) g • f (x * g) := by
  intro g u hu
  rw [HeckePair.apply_mul_right φ hu, ← mul_assoc, hf _ u hu]

theorem heckeAct_mul_right (φ : HeckePair.HeckeAlgebra U R₀) {f : G → V}
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    ∀ x, ∀ u ∈ U, heckeAct (U := U) (φ : G → R₀) f (x * u) = heckeAct (U := U) (φ : G → R₀) f x := by
  intro x u hu
  unfold heckeAct
  have h := coset_finsum_translate (U := U) (τ := fun g => (φ : G → R₀) g • f (x * g))
    (heckeAct_term_mul_right φ hf x) u
  rw [← h]
  refine finsum_congr fun c => ?_
  rw [HeckePair.apply_left_mul φ hu, mul_assoc]

theorem heckeAct_one' {f : G → V} (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) (x : G) :
    heckeAct (U := U) ((1 : HeckePair.HeckeAlgebra U R₀) : G → R₀) f x = f x := by
  unfold heckeAct
  rw [finsum_eq_single _ (QuotientGroup.mk (1 : G))]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (1 : G)
    rw [hu, one_mul, HeckePair.one_apply_of_mem u.2, one_smul, hf x u u.2]
  · intro c hc
    rw [HeckePair.one_apply_of_notMem, zero_smul]
    intro hmem
    apply hc
    rw [← QuotientGroup.out_eq' c]
    exact QuotientGroup.eq.mpr (by simpa using hmem)

theorem heckeAct_mul' (φ₁ φ₂ : HeckePair.HeckeAlgebra U R₀) {f : G → V}
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) (x : G) :
    heckeAct (U := U) ((φ₁ * φ₂ : HeckePair.HeckeAlgebra U R₀) : G → R₀) f x =
      heckeAct (U := U) (φ₁ : G → R₀) (heckeAct (U := U) (φ₂ : G → R₀) f) x := by
  classical
  set S := (HeckePair.finite_cosets φ₁).toFinset with hSdef
  have hS : QuotientGroup.mk '' Function.support (φ₁ : G → R₀) ⊆ (S : Set (G ⧸ U)) := by
    rw [hSdef, Set.Finite.coe_toFinset]
  have h1 : heckeAct (U := U) ((φ₁ * φ₂ : HeckePair.HeckeAlgebra U R₀) : G → R₀) f x =
      ∑ᶠ c : G ⧸ U, ∑ d ∈ S, HeckePair.convTerm φ₁ φ₂ (Quotient.out c) d • f (x * Quotient.out c) := by
    unfold heckeAct
    refine finsum_congr fun c => ?_
    rw [HeckePair.coe_mul, HeckePair.conv_eq_sum φ₁ φ₂ _ hS, Finset.sum_smul]
  have key : ∀ d : G ⧸ U,
      (∑ᶠ c : G ⧸ U, HeckePair.convTerm φ₁ φ₂ (Quotient.out c) d • f (x * Quotient.out c) =
        (φ₁ : G → R₀) (Quotient.out d) •
          heckeAct (U := U) (φ₂ : G → R₀) f (x * Quotient.out d)) ∧
      (Function.support fun c : G ⧸ U =>
        HeckePair.convTerm φ₁ φ₂ (Quotient.out c) d • f (x * Quotient.out c)).Finite := by
    intro d
    set y := Quotient.out d with hy
    have hd : d = QuotientGroup.mk y := (QuotientGroup.out_eq' d).symm
    set τ : G → V := fun g => ((φ₁ : G → R₀) y * (φ₂ : G → R₀) (y⁻¹ * g)) • f (x * g) with hτdef
    have hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g := by
      intro g u hu
      simp only [hτdef, ← mul_assoc, HeckePair.apply_mul_right φ₂ hu, hf _ u hu]
    have hterm : ∀ c : G ⧸ U,
        HeckePair.convTerm φ₁ φ₂ (Quotient.out c) d • f (x * Quotient.out c) = τ (Quotient.out c) := by
      intro c
      rw [hd, HeckePair.convTerm_mk]
    refine ⟨?_, ?_⟩
    · rw [finsum_congr hterm, ← coset_finsum_translate hτ y]
      have hτy : ∀ c : G ⧸ U, τ (y * Quotient.out c) =
          (φ₁ : G → R₀) y • ((φ₂ : G → R₀) (Quotient.out c) • f (x * y * Quotient.out c)) := by
        intro c
        simp only [hτdef, ← mul_assoc, inv_mul_cancel, one_mul, mul_smul]
      rw [finsum_congr hτy, heckeAct, smul_finsum' _ (heckeAct_support_finite φ₂ f (x * y))]
    · refine ((HeckePair.finite_cosets φ₂).image (fun c => y • c)).subset ?_
      intro c hc
      rw [Function.mem_support, hterm] at hc
      have h2 : (φ₂ : G → R₀) (y⁻¹ * Quotient.out c) ≠ 0 := by
        intro h0
        apply hc
        simp [hτdef, h0]
      refine ⟨QuotientGroup.mk (y⁻¹ * Quotient.out c), ⟨_, h2, rfl⟩, ?_⟩
      show y • (QuotientGroup.mk (y⁻¹ * Quotient.out c) : G ⧸ U) = c
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul, QuotientGroup.out_eq']
  rw [h1, finsum_sum_comm S _ (fun d _ => (key d).2)]
  simp_rw [fun d => (key d).1]
  show _ = ∑ᶠ d : G ⧸ U, (φ₁ : G → R₀) (Quotient.out d) •
    heckeAct (U := U) (φ₂ : G → R₀) f (x * Quotient.out d)
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro d hd
  refine hS ⟨Quotient.out d, fun h => hd ?_, QuotientGroup.out_eq' d⟩
  simp [h]

end ActionLemmas

/-- For a Hecke function `φ ∈ H(G, U; R₀)` and an equivariant `f` (with `ρ(1) = 1` and `ρ(γ)` commuting with `R₀`):
`φ · f` is again equivariant; `1 · f = f`; `(φ₁ ∗ φ₂) · f = φ₁ · (φ₂ · f)`; and `(φ, f) ↦ φ · f` is biadditive and
`R₀`-linear in `φ`. -/
@[tf_id "X.hmod.thm:hecke-module-action"]
theorem heckeAct_module (R : Type*) [CommRing R] {R₀ : Type*} [CommRing R₀] {V : Type*} [AddCommGroup V]
    [Module R V] [Module R₀ V] (ι : Γ →* G) (U : Subgroup G) (ρ : Γ → Module.End R V) (hρ1 : ρ 1 = 1)
    (hρ : ∀ (γ : Γ) (r : R₀) (v : V), ρ γ (r • v) = r • ρ γ v) :
    (∀ φ : HeckePair.HeckeAlgebra U R₀, ∀ f ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) (φ : G → R₀) f ∈ equivariantFunctions R ι U ρ) ∧
    (∀ f ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) ((1 : HeckePair.HeckeAlgebra U R₀) : G → R₀) f = f) ∧
    (∀ φ₁ φ₂ : HeckePair.HeckeAlgebra U R₀, ∀ f ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) ((φ₁ * φ₂ : HeckePair.HeckeAlgebra U R₀) : G → R₀) f =
        heckeAct (U := U) (φ₁ : G → R₀) (heckeAct (U := U) (φ₂ : G → R₀) f)) ∧
    (∀ φ₁ φ₂ : HeckePair.HeckeAlgebra U R₀, ∀ f ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) ((φ₁ + φ₂ : HeckePair.HeckeAlgebra U R₀) : G → R₀) f =
        heckeAct (U := U) (φ₁ : G → R₀) f + heckeAct (U := U) (φ₂ : G → R₀) f) ∧
    (∀ (r : R₀) (φ : HeckePair.HeckeAlgebra U R₀), ∀ f ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) ((r • φ : HeckePair.HeckeAlgebra U R₀) : G → R₀) f = r • heckeAct (U := U) (φ : G → R₀) f) ∧
    (∀ φ : HeckePair.HeckeAlgebra U R₀, ∀ f ∈ equivariantFunctions R ι U ρ, ∀ g ∈ equivariantFunctions R ι U ρ,
      heckeAct (U := U) (φ : G → R₀) (f + g) = heckeAct (U := U) (φ : G → R₀) f + heckeAct (U := U) (φ : G → R₀) g) := by
  have hinv : ∀ f ∈ equivariantFunctions R ι U ρ, ∀ x, ∀ u ∈ U, f (x * u) = f x := by
    intro f hf x u hu
    have h := hf 1 x u hu
    rwa [map_one, one_mul, hρ1, Module.End.one_apply] at h
  have hfin := fun (φ : HeckePair.HeckeAlgebra U R₀) (f : G → V) (x : G) =>
    heckeAct_support_finite (U := U) φ f x
  refine ⟨?_, fun f hf => funext fun x => heckeAct_one' (hinv f hf) x,
    fun φ₁ φ₂ f hf => funext fun x => heckeAct_mul' φ₁ φ₂ (hinv f hf) x, ?_, ?_, ?_⟩
  · intro φ f hf γ x u hu
    have hl : ∀ y, f (ι γ * y) = ρ γ (f y) := by
      intro y
      have h := hf γ y 1 (one_mem U)
      rwa [mul_one] at h
    rw [heckeAct_mul_right φ (hinv f hf) _ u hu]
    unfold heckeAct
    rw [map_finsum (ρ γ) (hfin φ f x)]
    refine finsum_congr fun c => ?_
    rw [mul_assoc, hl, hρ]
  · intro φ₁ φ₂ f _
    funext x
    unfold heckeAct
    rw [Pi.add_apply, ← finsum_add_distrib (hfin φ₁ f x) (hfin φ₂ f x)]
    refine finsum_congr fun c => ?_
    simp only [HeckePair.coe_apply_add, add_smul]
  · intro r φ f _
    funext x
    unfold heckeAct
    rw [Pi.smul_apply, smul_finsum' r (hfin φ f x)]
    refine finsum_congr fun c => ?_
    simp only [HeckePair.coe_apply_smul, mul_smul]
  · intro φ f _ g _
    funext x
    unfold heckeAct
    rw [Pi.add_apply, ← finsum_add_distrib (hfin φ f x) (hfin φ g x)]
    refine finsum_congr fun c => ?_
    simp only [Pi.add_apply, smul_add]

end GL2TF.HeckeModule
