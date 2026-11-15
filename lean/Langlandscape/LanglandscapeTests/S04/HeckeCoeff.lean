/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.HeckeCoeff

/-!
# Tests for `Langlandscape.Brandt.HeckeCoeff` (S04-L15a, `def:s01-hecke` with coefficients)

* the trivial extension to `Σ = ⊤` and `heckeTV_triv` for it;
* `heckeTV` is `R`-linear and lands in the Brandt module (`ρ(u)⁻¹`-equivariance on the right);
* the representative formula for a general extension.
-/

namespace Langlandscape.Brandt.Tests.HeckeCoeff

open Langlandscape.Quat Langlandscape.Brandt

variable {a b : ℤ}

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), test instance: the trivial extension of `ρ = 1` to `Σ = B̂^×`. -/
noncomputable def trivTop (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R] :
    HeckeExt U R R (1 : U →* (R ≃ₗ[R] R)) :=
  HeckeExt.triv ⊤ (fun u _ => Submonoid.mem_top u)

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), test: `heckeTV_triv` for `Σ = B̂^×`, any `g`. -/
theorem heckeTV_triv_top (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
    (g : (GL2TF.Quat.BHat a b)ˣ) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f : brandtModule U R R (1 : U →* (R ≃ₗ[R] R))) :
    brandtModuleTrivEquiv U R (heckeTV (trivTop U R) g (Submonoid.mem_top g) hfin f) =
      heckeT U g R hfin (brandtModuleTrivEquiv U R f) :=
  heckeTV_triv (trivTop U R) rfl g (Submonoid.mem_top g) hfin f

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), test: `heckeTV` is additive. -/
theorem heckeTV_add {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ρ : U →* (V ≃ₗ[R] V)} (E : HeckeExt U R V ρ)
    (g : (GL2TF.Quat.BHat a b)ˣ) (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f f' : brandtModule U R V ρ) :
    heckeTV E g hg hfin (f + f') = heckeTV E g hg hfin f + heckeTV E g hg hfin f' :=
  map_add _ f f'

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), test: `(T_g f)(x u) = ρ(u)⁻¹ (T_g f)(x)` for `u ∈ U`. -/
theorem heckeTV_mul_right {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ρ : U →* (V ≃ₗ[R] V)} (E : HeckeExt U R V ρ)
    (g : (GL2TF.Quat.BHat a b)ˣ) (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0)
    (f : brandtModule U R V ρ) (x : (GL2TF.Quat.BHat a b)ˣ) (u : U) :
    (heckeTV E g hg hfin f).1 (x * (u : (GL2TF.Quat.BHat a b)ˣ)) =
      (ρ u)⁻¹ ((heckeTV E g hg hfin f).1 x) := by
  simpa only [map_one, one_mul] using (heckeTV E g hg hfin f).2 1 x u

/-- `def:s01-hecke` (`s01-hecke`, `s04-L15a`), test: the representative formula
`(T_g f)(x) = ∑_{s ∈ T} ρΣ(s) f(x s)` for a system of representatives produced by `exists_dcReps`. -/
theorem heckeTV_exists_reps {U : Subgroup (GL2TF.Quat.BHat a b)ˣ} {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ρ : U →* (V ≃ₗ[R] V)} (E : HeckeExt U R V ρ)
    (g : (GL2TF.Quat.BHat a b)ˣ) (hg : g ∈ E.Sig) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    ∃ T : Finset (GL2TF.Quat.BHat a b)ˣ, ∀ (f : brandtModule U R V ρ) (x : (GL2TF.Quat.BHat a b)ˣ),
      (heckeTV E g hg hfin f).1 x = ∑ s ∈ T, E.rhoExt s (f.1 (x * s)) := by
  obtain ⟨T, hT⟩ := exists_dcReps U g hfin
  exact ⟨T, fun f x => heckeTV_apply_reps E g hg hfin hT f x⟩

end Langlandscape.Brandt.Tests.HeckeCoeff
