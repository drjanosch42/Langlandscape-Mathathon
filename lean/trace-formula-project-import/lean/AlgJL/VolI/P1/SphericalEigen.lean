import AlgJL.VolI.P1.Satake
import AlgJL.VolI.P1.PrincipalSeries

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/SphericalEigen.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (3): `sphericalHeckeAction_mul`, `sphericalHeckeAction_one`, `spherical_hecke_action_algebra`.
Dropped tagged IDs: `I.smooth.thm:spherical-hecke-action-algebra`. -/

/-!
# The action of `H(G, K)` on `K`-fixed vectors and the Hecke eigenvalues of `f°_χ` (M5a, unit U2, items 26–27)

Lean counterpart of `vol1/ch-1-02-smooth.tex` §2 (second half). Owner: L1 (split out of `PrincipalSeries.lean`, plan §1.1).

`π(f)v = ∑_{gK ∈ G/K} f(g) π(g)v` is a `finsum` over `G ⧸ K` evaluated at the chosen representatives `Quotient.out`;
for `v ∈ V^K` the summand does not depend on the choice and has finite support (`sphericalHeckeAction_spec`). Off
`V^K` the value is a junk value; every statement restricts to `V^K`.
-/

open ValuativeRel GL2TF MeasureTheory

namespace GL2TF.Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- `q^{1/2} ∈ ℂ`, the positive square root (local notation). -/
local notation "√q" => ((Real.sqrt (q F : ℝ) : ℝ) : ℂ)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The action of `f ∈ H(G, K)` on a representation `(π, V)` of `G`: `π(f)v = ∑_{gK ∈ G/K} f(g) π(g)v`
(meaningful for `v ∈ V^K`). -/
@[tf_id "I.smooth.def:spherical-hecke-action"]
noncomputable def sphericalHeckeAction (π : Representation ℂ (GL (Fin 2) F) V) (f : sphericalHeckeAlgebra F)
    (v : V) : V :=
  ∑ᶠ c : GL (Fin 2) F ⧸ 𝐊[F], (f : GL (Fin 2) F → ℂ) c.out • π c.out v

section CosetSums

variable {G : Type*} [Group G] {U : Subgroup G} {M : Type*} [AddCommMonoid M]

theorem apply_out_eq_of_mul_right {τ : G → M} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (g : G) :
    τ (Quotient.out (QuotientGroup.mk g : G ⧸ U)) = τ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hτ g u u.2]

theorem finsum_coset_translate_of_mul_right {τ : G → M} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (y : G) :
    ∑ᶠ c : G ⧸ U, τ (y * c.out) = ∑ᶠ c : G ⧸ U, τ c.out := by
  calc ∑ᶠ c : G ⧸ U, τ (y * c.out)
      = ∑ᶠ c : G ⧸ U, τ ((MulAction.toPerm y : Equiv.Perm (G ⧸ U)) c).out := by
        refine finsum_congr fun c => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, apply_out_eq_of_mul_right hτ]
        obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
        rw [hu, ← mul_assoc, hτ _ u u.2]
    _ = _ := finsum_comp_equiv (MulAction.toPerm y : Equiv.Perm (G ⧸ U)) (f := fun c : G ⧸ U => τ c.out)

end CosetSums

theorem sphericalHeckeAction_term_mul_right (π : Representation ℂ (GL (Fin 2) F) V) (f : sphericalHeckeAlgebra F)
    {v : V} (hv : v ∈ fixedVectors π 𝐊[F]) (g k : GL (Fin 2) F) (hk : k ∈ 𝐊[F]) :
    (f : GL (Fin 2) F → ℂ) (g * k) • π (g * k) v = (f : GL (Fin 2) F → ℂ) g • π g v := by
  rw [HeckePair.apply_mul_right f hk, map_mul, Module.End.mul_apply, hv k hk]

theorem sphericalHeckeAction_support_finite (π : Representation ℂ (GL (Fin 2) F) V) (f : sphericalHeckeAlgebra F)
    (v : V) :
    (Function.support fun c : GL (Fin 2) F ⧸ 𝐊[F] => (f : GL (Fin 2) F → ℂ) c.out • π c.out v).Finite :=
  (HeckePair.finite_cosets f).subset fun c hc =>
    ⟨c.out, fun h => hc (by simp [h]), QuotientGroup.out_eq' c⟩

/-- For `v ∈ V^K` the summand `f(g)π(g)v` depends only on `gK` and vanishes off finitely many cosets; `π(f)v ∈ V^K`;
and `π(f)v` is `ℂ`-linear in `v ∈ V^K` and in `f` (B-only: the claims of `I.smooth.def:spherical-hecke-action`). -/
@[tf_aux "I.smooth.lem:spherical-hecke-action-spec"]
theorem sphericalHeckeAction_spec (π : Representation ℂ (GL (Fin 2) F) V) :
    ∀ v ∈ fixedVectors π 𝐊[F],
      (∀ f : sphericalHeckeAlgebra F, ∀ g, ∀ k ∈ 𝐊[F],
        (f : GL (Fin 2) F → ℂ) (g * k) • π (g * k) v = (f : GL (Fin 2) F → ℂ) g • π g v) ∧
      (∀ f : sphericalHeckeAlgebra F,
        (Function.support fun c : GL (Fin 2) F ⧸ 𝐊[F] => (f : GL (Fin 2) F → ℂ) c.out • π c.out v).Finite) ∧
      (∀ f : sphericalHeckeAlgebra F, sphericalHeckeAction π f v ∈ fixedVectors π 𝐊[F]) ∧
      (∀ (c : ℂ) (f₁ f₂ : sphericalHeckeAlgebra F),
        sphericalHeckeAction π (c • f₁ + f₂) v = c • sphericalHeckeAction π f₁ v + sphericalHeckeAction π f₂ v) ∧
      ∀ w ∈ fixedVectors π 𝐊[F], ∀ (c : ℂ) (f : sphericalHeckeAlgebra F),
        sphericalHeckeAction π f (c • v + w) = c • sphericalHeckeAction π f v + sphericalHeckeAction π f w := by
  intro v hv
  refine ⟨fun f g k hk => sphericalHeckeAction_term_mul_right π f hv g k hk,
    fun f => sphericalHeckeAction_support_finite π f v, fun f k hk => ?_, fun c f₁ f₂ => ?_, fun w _ c f => ?_⟩
  · show π k (sphericalHeckeAction π f v) = sphericalHeckeAction π f v
    unfold sphericalHeckeAction
    rw [map_finsum (π k) (sphericalHeckeAction_support_finite π f v)]
    refine (finsum_congr fun c => ?_).trans (finsum_coset_translate_of_mul_right
      (τ := fun g => (f : GL (Fin 2) F → ℂ) g • π g v)
      (fun g u hu => sphericalHeckeAction_term_mul_right π f hv g u hu) k)
    show π k ((f : GL (Fin 2) F → ℂ) c.out • π c.out v) =
      (f : GL (Fin 2) F → ℂ) (k * c.out) • π (k * c.out) v
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, HeckePair.apply_left_mul f hk]
  · unfold sphericalHeckeAction
    rw [smul_finsum' c (sphericalHeckeAction_support_finite π f₁ v),
      ← finsum_add_distrib ((sphericalHeckeAction_support_finite π f₁ v).subset fun x hx h => hx (by simp [h]))
        (sphericalHeckeAction_support_finite π f₂ v)]
    refine finsum_congr fun x => ?_
    simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul, add_smul, mul_smul]
  · unfold sphericalHeckeAction
    rw [smul_finsum' c (sphericalHeckeAction_support_finite π f v),
      ← finsum_add_distrib ((sphericalHeckeAction_support_finite π f v).subset fun x hx h => hx (by simp [h]))
        (sphericalHeckeAction_support_finite π f w)]
    refine finsum_congr fun x => ?_
    rw [map_add, map_smul, smul_add, smul_comm ((f : GL (Fin 2) F → ℂ) x.out) c]

/-- The spherical vector `f°_χ` as an element of `I(χ₁, χ₂)`, for unramified `χ₁, χ₂` (B-only). -/
@[tf_aux "I.smooth.def:spherical-vector-element"]
noncomputable def sphericalVectorPS (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    padicPrincipalSeries χ₁ χ₂ :=
  ⟨sphericalVector χ₁ χ₂, ((principal_series_spherical χ₁ χ₂).1 h₁ h₂).1⟩

local notation "ϖ" => ((unif F : 𝒪[F]) : F)

theorem deltaHalf_unif_zpow (i j : ℤ) : deltaHalf (unifUnit F ^ i) (unifUnit F ^ j) = √q ^ (j - i) := by
  have hq : (0 : ℝ) ≤ (q F : ℝ) := Nat.cast_nonneg _
  have h1 : ((unifUnit F ^ i : Fˣ) : F) / ((unifUnit F ^ j : Fˣ) : F) =
      ((1 : 𝒪[F]ˣ) : 𝒪[F]) * ϖ ^ (i - j) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, unifUnit_val, Units.val_one,
      OneMemClass.coe_one, one_mul, zpow_sub₀ (unif_ne_zero F)]
  unfold deltaHalf
  rw [h1, normAbs_unit_mul_unif_zpow, neg_sub, ← Real.rpow_intCast, ← Real.rpow_mul hq, Real.sqrt_eq_rpow,
    ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm]

theorem hmat_eq_upper_diag (i j : ℤ) (x : F) :
    hmat i j x = Matrix.GeneralLinearGroup.upperRightHom (x * ϖ ^ (-j)) * diagElt (unifUnit F ^ i) (unifUnit F ^ j) := by
  apply Units.ext
  rw [Units.val_mul, hmat_val]
  show _ = !![1, x * ϖ ^ (-j); 0, 1] * !![((unifUnit F ^ i : Fˣ) : F), 0; 0, ((unifUnit F ^ j : Fˣ) : F)]
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, unifUnit_val, Matrix.mul_fin_two]
  have h := unif_ne_zero F
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mul_assoc, inv_mul_cancel₀ (zpow_ne_zero j h)]

/-- `f°_χ(g) = ev_{α,β}(μ(g))` for the Satake weight `μ` (proof helper of item 27). -/
theorem sphericalVector_eq_laurentEval (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    (g : GL (Fin 2) F) :
    sphericalVector χ₁ χ₂ g = laurentEval (χ₁.1 (unifUnit F)) (χ₂.1 (unifUnit F)) (satakeWeight g) := by
  obtain ⟨-, hK, -⟩ := (principal_series_spherical χ₁ χ₂).1 h₁ h₂
  obtain ⟨i, j, x, hg⟩ := exists_hmat g
  have hk : (hmat i j x)⁻¹ * g ∈ 𝐊[F] := QuotientGroup.eq.mp hg.symm
  have hgk : g = hmat i j x * ((hmat i j x)⁻¹ * g) := by group
  rw [hgk, hK _ _ hk, satakeWeight_mul_right _ _ hk, satakeWeight_hmat, laurentEval_single,
    show hmat i j x = Matrix.GeneralLinearGroup.upperRightHom (x * ϖ ^ (-j)) * diagElt (unifUnit F ^ i) (unifUnit F ^ j) * 1 by
      rw [mul_one, hmat_eq_upper_diag],
    sphericalVector_spec χ₁ χ₂ h₁ h₂ _ _ _ _ (one_mem _), deltaHalf_unif_zpow]
  change ((χ₁.1 (unifUnit F ^ i) : ℂˣ) : ℂ) * ((χ₂.1 (unifUnit F ^ j) : ℂˣ) : ℂ) * √q ^ (j - i) = _
  rw [map_zpow, map_zpow, Units.val_mul]
  ring

/-- For unramified `χ₁, χ₂` with Satake parameter `(α, β) = (χ₁(ϖ), χ₂(ϖ))` and `f ∈ H(G, K)`:
`π_χ(f) f°_χ = ω_{α,β}(f) f°_χ = (𝒮f)(α, β) f°_χ`; in particular `π_χ(T_ϖ) f°_χ = q^{1/2}(α + β) f°_χ` and
`π_χ(R_ϖ) f°_χ = αβ f°_χ`. -/
@[tf_id "I.smooth.thm:spherical-hecke-eigenvalue"]
theorem spherical_hecke_eigenvalue (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (∀ f : sphericalHeckeAlgebra F,
        sphericalHeckeAction (psRep χ₁ χ₂) f (sphericalVectorPS χ₁ χ₂ h₁ h₂) =
          laurentEval (χ₁.1 (unifUnit F)) (χ₂.1 (unifUnit F)) (satake F f) • sphericalVectorPS χ₁ χ₂ h₁ h₂) ∧
      sphericalHeckeAction (psRep χ₁ χ₂) (heckeBasis F 1 0) (sphericalVectorPS χ₁ χ₂ h₁ h₂) =
        (√q * (χ₁ (unifUnit F) + χ₂ (unifUnit F))) • sphericalVectorPS χ₁ χ₂ h₁ h₂ ∧
      sphericalHeckeAction (psRep χ₁ χ₂) (heckeBasis F 1 1) (sphericalVectorPS χ₁ χ₂ h₁ h₂) =
        (χ₁ (unifUnit F) * χ₂ (unifUnit F)) • sphericalVectorPS χ₁ χ₂ h₁ h₂ := by
  obtain ⟨hmem, hK, h1, hc, -⟩ := (principal_series_spherical χ₁ χ₂).1 h₁ h₂
  have hfix : sphericalVectorPS χ₁ χ₂ h₁ h₂ ∈ fixedVectors (psRep χ₁ χ₂) 𝐊[F] := fun k hk =>
    Subtype.ext (funext fun g => by rw [psRep_apply]; exact hK g k hk)
  have hmain : ∀ f : sphericalHeckeAlgebra F,
      sphericalHeckeAction (psRep χ₁ χ₂) f (sphericalVectorPS χ₁ χ₂ h₁ h₂) =
        laurentEval (χ₁.1 (unifUnit F)) (χ₂.1 (unifUnit F)) (satake F f) • sphericalVectorPS χ₁ χ₂ h₁ h₂ := by
    intro f
    set w := sphericalHeckeAction (psRep χ₁ χ₂) f (sphericalVectorPS χ₁ χ₂ h₁ h₂) with hw
    have hwK := ((sphericalHeckeAction_spec (psRep χ₁ χ₂)) _ hfix).2.2.1 f
    obtain ⟨c, hcw⟩ := hc w hwK
    -- evaluation at `1`
    let ev1 : padicPrincipalSeries χ₁ χ₂ →+ ℂ :=
      { toFun := fun φ => φ.1 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hw1 : w.1 1 = laurentEval (χ₁.1 (unifUnit F)) (χ₂.1 (unifUnit F)) (satake F f) := by
      have hs := sphericalHeckeAction_support_finite (psRep χ₁ χ₂) f (sphericalVectorPS χ₁ χ₂ h₁ h₂)
      change ev1 w = _
      rw [hw, sphericalHeckeAction, map_finsum ev1 hs, satake,
        cosetTransform, map_finsum (laurentEval (χ₁.1 (unifUnit F)) (χ₂.1 (unifUnit F)))
          (finite_support_cosetTransform_term satakeWeight f)]
      refine finsum_congr fun C => ?_
      change (f : GL (Fin 2) F → ℂ) C.out * sphericalVector χ₁ χ₂ (1 * C.out) = _
      rw [map_smul, smul_eq_mul, one_mul, sphericalVector_eq_laurentEval χ₁ χ₂ h₁ h₂]
    have hc1 : c = w.1 1 := by
      rw [hcw, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    refine Subtype.ext ?_
    change w.1 = _
    rw [hcw, hc1, hw1]
    rfl
  refine ⟨hmain, ?_, ?_⟩
  · rw [hmain, ((hecke_characters F).1 _ _).2.1]
  · rw [hmain, ((hecke_characters F).1 _ _).2.2]

end GL2TF.Local
