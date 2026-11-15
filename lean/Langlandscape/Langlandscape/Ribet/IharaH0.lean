/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ribet.Coeff

/-!
# Ihara (iii): the norm character `τ` and the map `ε` (S03-L11)

`mathematics/chapters/s03/4-ihara.tex`, `thm:s03-iharaH0`(a), conventions (C5) (norm character) and (C6)
(coinvariants as `ℤ_p[ℤ_p^×]`-modules). Statement layer only: the theorem itself (clause (a)) is the registered
hypothesis `Langlandscape.Hyp.IharaH0` (`Langlandscape/Hyp/IharaH0.lean`).

Fix a prime `p ∤ D` (the coefficient prime).

* `detP d p hp : B̂^× →* ℚ_p^×`, `x ↦ det ι_p(x_p)` (`= Nrd(x)_p`).
* `tau d p hp x = det ι_p(x_p) · ν(x)` with `ν = GL2TF.Quat.normWeight` (`ν(x) = ‖Nrd x‖_{𝔸_f}`): (C5),
  `τ(x) = Nrd(x)_p ‖Nrd x‖`.
* `U1p d p hp U = {u ∈ U : det ι_p(u_p) = 1}`. When `ρ` factors through `U → U_p` and `U = U_p × U^{(p)}`, the
  `U1p`-coinvariants of `V` are the `U^1_p = U_p ∩ SL₂(ℤ_p)`-coinvariants of the tex.
* `coinvKer c p hp = span {ρ(u) w − w : u ∈ U1p}`, `Coinv c p hp = V ⧸ coinvKer c p hp` (`V_{U^1_p}`).
* `detSec d p hp U t` : some `u ∈ U` with `det ι_p(u_p) = t` (classical choice; junk value `1` if there is none).
* `coinvMap c p hp u : Coinv →ₗ Coinv`, the action of `ρ(u)` on coinvariants (`coinvKer` is `ρ(U)`-stable since `U1p`
  is normal in `U`: `coinvKer_le_comap`); `diamond c p hp t = coinvMap (detSec t)` is `[t]` of (C6);
  bridge `mkQ_rho : mkQ (ρ(u) v) = coinvMap u (mkQ v)`.
* `tau_mul : τ(x y) = τ(x) τ(y)`.
* `epsilonAt c p hp x (f₀, f₁) = w_x^{-1} ([τ(x)] f₀(x) + [q τ(x)] f₁(x))` (`w_x^{-1}` is `Ring.inverse`; restated
  through `diamond` in `epsilonAt_apply_diamond`), and
  `epsilon c p hp = ∑_{[x] ∈ X_B(U)} epsilonAt c p hp x_{[x]}` with the representatives `x_{[x]} = Quotient.out`.
* `EpsWellDefined c p hp` : the content of "`ε` is well defined" (`thm:s03-iharaH0`(a), proof step (a1)): the
  weights are units, `τ(x)` and `q τ(x)` lie in `det ι_p(U_p)`, and the summand only depends on `[x]`.

Junk values (`Ring.inverse` of a non-unit, `detSec` without a preimage, `finsum` over an infinite `X_B(U)`) never
occur under the hypotheses of `thm:s03-iharaH0`; `EpsWellDefined` makes the first two explicit.

Status: *formalized* (definitions only); `thm:s03-iharaH0`(a) is the hypothesis `Hyp.IharaH0`.
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree

/-! ### The norm character `τ` (C5) -/

section Tau

/-- (C5), (C6) (`thm:s03-iharaH0`): the determinant of the `p`-component, `x ↦ det ι_p(x_p) ∈ ℚ_p^×`
(`= Nrd(x)_p`), for `p ∤ D`. -/
noncomputable def detP (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) :
    (BHat d.a d.b)ˣ →* ℚ_[p]ˣ :=
  (Matrix.GeneralLinearGroup.det : GL (Fin 2) ℚ_[p] →* ℚ_[p]ˣ).comp (localComponent d p hp)

/-- (C5) (`thm:s03-iharaH0`): the norm character `τ(x) = Nrd(x)_p · ‖Nrd x‖_{𝔸_f}`, valued in `ℚ_[p]` (it is a unit
of `ℤ_p` by (C5); not proved here), with
`‖Nrd x‖ = GL2TF.Quat.normWeight x` (the `normWeight` of the import, DT p. 446) and `Nrd(x)_p = det ι_p(x_p)`.
Writing `Nrd x = r t` with `r ∈ ℚ_{>0}`, `t ∈ Ẑ^×`, this is `t_p`. -/
noncomputable def tau (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (x : (BHat d.a d.b)ˣ) : ℚ_[p] :=
  ((detP d p hp x : ℚ_[p]ˣ) : ℚ_[p]) * ((GL2TF.Quat.normWeight x : ℚ) : ℚ_[p])

/-- (C6) (`thm:s03-iharaH0`): `U^1_p` inside `U`: the kernel of `u ↦ det ι_p(u_p)` on `U`. -/
noncomputable def U1p (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    Subgroup U :=
  ((detP d p hp).comp U.subtype).ker

open Classical in
/-- (C6) (`thm:s03-iharaH0`): a chosen `u_t ∈ U` with `det ι_p((u_t)_p) = t` (junk value `1` if none exists; under
`Nrd U = Ẑ^×` one exists for every `t ∈ ℤ_p^×`). -/
noncomputable def detSec (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (t : ℚ_[p]) : U :=
  if h : ∃ u : U, ((detP d p hp (u : (BHat d.a d.b)ˣ) : ℚ_[p]ˣ) : ℚ_[p]) = t then h.choose else 1

/-- (C5) (`s03-conv`): `τ` is multiplicative, `τ(x y) = τ(x) τ(y)` (from `map_mul` and the multiplicativity of
`normWeight`, `GL2TF.Quat.normWeight_transform`). -/
theorem tau_mul (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (x y : (BHat d.a d.b)ˣ) :
    tau d p hp (x * y) = tau d p hp x * tau d p hp y := by
  unfold tau
  rw [map_mul, Units.val_mul, (GL2TF.Quat.normWeight_transform d.O.1).2.1 x y, Rat.cast_mul]
  ring

end Tau

/-! ### Coinvariants and `ε` -/

section Epsilon

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- (C6) (`thm:s03-iharaH0`): the submodule `span {ρ(u) w − w : u ∈ U^1_p}` of `V`. -/
def coinvKer (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) : Submodule R V :=
  Submodule.span R {v : V | ∃ u ∈ U1p d p hp U, ∃ w : V, v = c.ρ u w - w}

/-- (C6) (`thm:s03-iharaH0`): the coinvariants `V_{U^1_p} = V ⧸ span {ρ(u) w − w : u ∈ U^1_p}`. -/
abbrev Coinv (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) : Type _ :=
  V ⧸ coinvKer c p hp

/-- (C6) (`s03-conv`): `coinvKer` is stable under `ρ(u)` for every `u ∈ U`, since `U1p` is normal in `U`:
`ρ(u)(ρ(h) w − w) = ρ(u h u⁻¹)(ρ(u) w) − ρ(u) w`. -/
theorem coinvKer_le_comap (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (u : U) :
    coinvKer c p hp ≤ (coinvKer c p hp).comap (c.ρ u).toLinearMap := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨h, hh, w, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  have hconj : u * h * u⁻¹ ∈ U1p d p hp U :=
    (MonoidHom.normal_ker ((detP d p hp).comp U.subtype)).conj_mem h hh u
  have h1 : c.ρ (u * h * u⁻¹) (c.ρ u w) = c.ρ u (c.ρ h w) := by
    simp only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have heq : (c.ρ u).toLinearMap (c.ρ h w - w) = c.ρ (u * h * u⁻¹) (c.ρ u w) - c.ρ u w := by
    show c.ρ u (c.ρ h w - w) = _
    rw [map_sub, h1]
  have hmem : (c.ρ u).toLinearMap (c.ρ h w - w) ∈
      {v : V | ∃ u' ∈ U1p d p hp U, ∃ w' : V, v = c.ρ u' w' - w'} :=
    ⟨u * h * u⁻¹, hconj, c.ρ u w, heq⟩
  exact Submodule.subset_span hmem

/-- (C6) (`thm:s03-iharaH0`): the action of `ρ(u)`, `u ∈ U`, on the coinvariants `V_{U^1_p}`. -/
noncomputable def coinvMap (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (u : U) :
    Coinv c p hp →ₗ[R] Coinv c p hp :=
  (coinvKer c p hp).mapQ (coinvKer c p hp) (c.ρ u).toLinearMap (coinvKer_le_comap c p hp u)

/-- (C6) (`thm:s03-iharaH0`): the operator `[t]` on `V_{U^1_p}`: the action of a chosen `u_t ∈ U` with
`det ι_p((u_t)_p) = t` (`detSec`; independent of the choice up to `U1p`, which acts trivially on `Coinv`). -/
noncomputable def diamond (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (t : ℚ_[p]) :
    Coinv c p hp →ₗ[R] Coinv c p hp :=
  coinvMap c p hp (detSec d p hp U t)

/-- (C6) (`s03-conv`): the bridge `mkQ (ρ(u) v) = coinvMap u (mkQ v)`. -/
theorem mkQ_rho (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (u : U) (v : V) :
    (coinvKer c p hp).mkQ (c.ρ u v) = coinvMap c p hp u ((coinvKer c p hp).mkQ v) :=
  rfl

/-- `thm:s03-iharaH0`: evaluation `f ↦ f(x)` on `Brandt(U, V)`. -/
def evalV (c : CoeffData d q hq U R V) (x : (BHat d.a d.b)ˣ) : brandtModule U R V c.ρ →ₗ[R] V :=
  (LinearMap.proj x : ((BHat d.a d.b)ˣ → V) →ₗ[R] V).comp (brandtModule U R V c.ρ).subtype

/-- `thm:s03-iharaH0`(a): the summand of `ε` at a lift `x`,
`(f₀, f₁) ↦ w_x^{-1} ([τ(x)] f₀(x) + [q τ(x)] f₁(x)) ∈ V_{U^1_p}`. -/
noncomputable def epsilonAt (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (x : (BHat d.a d.b)ˣ) :
    brandtModule U R V c.ρ × brandtModule U R V c.ρ →ₗ[R] Coinv c p hp :=
  Ring.inverse ((wx U x : ℕ) : R) •
    ((coinvKer c p hp).mkQ ∘ₗ (c.ρ (detSec d p hp U (tau d p hp x))).toLinearMap ∘ₗ evalV c x ∘ₗ
        LinearMap.fst R _ _ +
      (coinvKer c p hp).mkQ ∘ₗ (c.ρ (detSec d p hp U ((q : ℚ_[p]) * tau d p hp x))).toLinearMap ∘ₗ
        evalV c x ∘ₗ LinearMap.snd R _ _)

/-- `thm:s03-iharaH0`(a): the map `ε : Brandt(U, V)² → V_{U^1_p}`,
`ε(f₀, f₁) = ∑_{[x] ∈ X_B(U)} w_x^{-1} ([τ(x)] f₀(x) + [q τ(x)] f₁(x))` (representatives `Quotient.out`). -/
noncomputable def epsilon (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) :
    brandtModule U R V c.ρ × brandtModule U R V c.ρ →ₗ[R] Coinv c p hp :=
  ∑ᶠ cl : XB U, epsilonAt c p hp (Quotient.out cl)

/-- `thm:s03-iharaH0`(a), proof step (a1): "`ε` is well defined": every weight `w_x` is a unit in `R`, `τ(x)` and
`q τ(x)` are determinants of elements of `U` (so `[τ(x)]`, `[q τ(x)]` are defined), and the summand
`epsilonAt x` only depends on the class `[x] = B^× x U`. -/
def EpsWellDefined (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) : Prop :=
  (∀ x : (BHat d.a d.b)ˣ, IsUnit ((wx U x : ℕ) : R)) ∧
    (∀ x : (BHat d.a d.b)ˣ, ∃ u : U, ((detP d p hp (u : (BHat d.a d.b)ˣ) : ℚ_[p]ˣ) : ℚ_[p]) = tau d p hp x) ∧
    (∀ x : (BHat d.a d.b)ˣ, ∃ u : U,
      ((detP d p hp (u : (BHat d.a d.b)ˣ) : ℚ_[p]ˣ) : ℚ_[p]) = (q : ℚ_[p]) * tau d p hp x) ∧
    (∀ (f : brandtModule U R V c.ρ × brandtModule U R V c.ρ) (x : (BHat d.a d.b)ˣ),
      ∀ γ ∈ globalUnits d.a d.b, ∀ u : U,
        epsilonAt c p hp (γ * x * (u : (BHat d.a d.b)ˣ)) f = epsilonAt c p hp x f)

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`): the summand of `ε`,
`epsilonAt x (f₀, f₁) = w_x^{-1} ([τ(x)] f₀(x) + [q τ(x)] f₁(x))`. -/
theorem epsilonAt_apply (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (x : (BHat d.a d.b)ˣ) (f : brandtModule U R V c.ρ × brandtModule U R V c.ρ) :
    epsilonAt c p hp x f =
      Ring.inverse ((wx U x : ℕ) : R) •
        ((coinvKer c p hp).mkQ (c.ρ (detSec d p hp U (tau d p hp x)) (f.1.1 x)) +
          (coinvKer c p hp).mkQ (c.ρ (detSec d p hp U ((q : ℚ_[p]) * tau d p hp x)) (f.2.1 x))) :=
  rfl

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`), via (C6): `epsilonAt x (f₀, f₁) = w_x^{-1} ([τ(x)] f̄₀(x) + [q τ(x)] f̄₁(x))`
with `[t] = diamond c p hp t` acting on the classes `f̄_j(x) ∈ V_{U^1_p}`. -/
theorem epsilonAt_apply_diamond (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (x : (BHat d.a d.b)ˣ) (f : brandtModule U R V c.ρ × brandtModule U R V c.ρ) :
    epsilonAt c p hp x f =
      Ring.inverse ((wx U x : ℕ) : R) •
        (diamond c p hp (tau d p hp x) ((coinvKer c p hp).mkQ (f.1.1 x)) +
          diamond c p hp ((q : ℚ_[p]) * tau d p hp x) ((coinvKer c p hp).mkQ (f.2.1 x))) :=
  rfl

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`): for finite `X_B(U)`, `ε(f) = ∑_{[x]} epsilonAt x_{[x]} f`. -/
theorem epsilon_apply [Finite (XB U)] (c : CoeffData d q hq U R V) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (f : brandtModule U R V c.ρ × brandtModule U R V c.ρ) :
    epsilon c p hp f = ∑ᶠ cl : XB U, epsilonAt c p hp (Quotient.out cl) f := by
  haveI := Fintype.ofFinite (XB U)
  rw [epsilon, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Epsilon

end Langlandscape.Ribet
