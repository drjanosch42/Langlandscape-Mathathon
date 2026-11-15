/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.InvLimit

/-!
# Tests for `Langlandscape.Ordinary.InvLimit` (S04-L13a, D-lim, D-Λ)

* zero system (`M s = PUnit`): every family is compatible;
* constant system `M s = R`, `f s = id`: `Compat.proj 0` is bijective (`lim = R`);
* a split exact constant tower `0 → R → R × R → R → 0`: `lim_exact` applies;
* `Lam` for trivial groups `G s = Unit` is a commutative ring with surjective projections;
* the regular system `M s = R[G s]` with transitions induced by `π s` is equivariant, so
  `Compat` of it is a `Lam`-module.
-/

@[expose] public section

namespace Langlandscape.Ordinary.Tests

open Langlandscape.Ordinary

section Systems

variable (R : Type*) [CommRing R]

/-- `def:s04-Mord` (s04-Mord), edge case: for the zero system every family is compatible. -/
theorem compat_zero_system (f : ∀ s, (fun _ : ℕ => PUnit.{1}) (s + 1) →ₗ[R] PUnit.{1})
    (x : ∀ _ : ℕ, PUnit.{1}) : x ∈ Compat f :=
  fun _ => Subsingleton.elim _ _

/-- `def:s04-Mord` (s04-Mord): for the constant system `M s = R`, `f s = id`, a compatible family
is constant. -/
theorem compat_const_eq (x : Compat (R := R) (M := fun _ : ℕ => R) (fun _ => LinearMap.id))
    (s : ℕ) :
    (x : ∀ _ : ℕ, R) s = (x : ∀ _ : ℕ, R) 0 := by
  induction s with
  | zero => rfl
  | succ s ih => rw [← ih]; exact x.2 s

/-- `thm:s04-lambdaribet` (s04-lambdaribet): for the constant system `M s = R`, `f s = id`, the
projection `lim M → M 0` is bijective (`lim M = R`). -/
theorem compat_const_proj_bijective :
    Function.Bijective (Compat.proj (R := R) (M := fun _ : ℕ => R) (fun _ => LinearMap.id) 0) := by
  refine ⟨fun x y hxy => Subtype.ext (funext fun s => ?_), ?_⟩
  · rw [compat_const_eq R x s, compat_const_eq R y s]
    exact hxy
  · exact compat_proj_surjective _ (fun _ _ => Function.surjective_id)

/-- `thm:s04-lambdaribet`(a) (s04-lambdaribet): `lim_exact` applied to the constant split exact
tower `0 → R → R × R → R → 0` (inclusion of the first factor, second projection; identity
transitions). -/
theorem lim_exact_const_split :
    Function.Injective (Compat.map (M := fun _ : ℕ => R) (N := fun _ : ℕ => R × R)
        (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id)
        (fun _ => LinearMap.inl R R R) (fun _ => rfl)) ∧
      Function.Exact
        (Compat.map (M := fun _ : ℕ => R) (N := fun _ : ℕ => R × R)
          (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id)
          (fun _ => LinearMap.inl R R R) (fun _ => rfl))
        (Compat.map (M := fun _ : ℕ => R × R) (N := fun _ : ℕ => R)
          (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id)
          (fun _ => LinearMap.snd R R R) (fun _ => rfl)) ∧
      Function.Surjective
        (Compat.map (M := fun _ : ℕ => R × R) (N := fun _ : ℕ => R)
          (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id)
          (fun _ => LinearMap.snd R R R) (fun _ => rfl)) :=
  lim_exact _ _ _ _ (fun _ => LinearMap.inl_injective) (fun _ => Function.Exact.inl_snd)
    (fun _ => LinearMap.snd_surjective) (fun _ => Function.surjective_id)

end Systems

section LamTests

variable (R : Type*) [CommRing R]

/-- `D-Λ` (s04-Mord): `Lam` is a commutative ring (here for an arbitrary tower of commutative
groups). -/
theorem lam_commRing (G : ℕ → Type*) [∀ s, CommGroup (G s)] (π : ∀ s, G (s + 1) →* G s) :
    Nonempty (CommRing (Lam R G π)) :=
  ⟨inferInstance⟩

/-- `D-Λ` (s04-Mord), edge case: trivial groups `G s = Unit`; every projection `Λ → R[1]` is
surjective. -/
theorem lam_trivial_proj_surjective (s : ℕ) :
    Function.Surjective (Lam.proj R (fun _ => Unit) (fun _ => 1) s) :=
  Lam.proj_surjective R _ _ (fun _ _ _ => ⟨1, Subsingleton.elim _ _⟩)

variable (G : ℕ → Type*) [∀ s, CommGroup (G s)] (π : ∀ s, G (s + 1) →* G s)

/-- `def:s04-Mord` (s04-Mord, D-Λ): the regular tower `M s = R[G s]`, with the transitions
induced by `π s`, is equivariant. -/
instance regular_isEquivariant :
    Compat.IsEquivariant (M := fun s => MonoidAlgebra R (G s)) π
      (fun s => (MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap) where
  map_smul' s l m := by
    simp only [smul_eq_mul, AlgHom.toLinearMap_apply, map_mul]
    rfl

/-- `def:s04-Mord` (s04-Mord, D-Λ): `Compat` of the regular tower is a `Lam`-module, with the
levelwise action. -/
theorem regular_lam_smul (l : Lam R G π)
    (x : Compat (M := fun s => MonoidAlgebra R (G s))
      (fun s => (MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap)) (s : ℕ) :
    ((l • x : Compat (M := fun s => MonoidAlgebra R (G s))
      (fun s => (MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap)) :
        ∀ s, MonoidAlgebra R (G s)) s =
      (l : ∀ s, MonoidAlgebra R (G s)) s * (x : ∀ s, MonoidAlgebra R (G s)) s :=
  Compat.lam_smul_apply _ l x s

/-- `thm:s04-lambdaribet`(a) (s04-lambdaribet, D-Λ): the identity morphism of the regular tower
gives a `Λ`-linear map `Compat.mapLam` whose underlying function is that of `Compat.map`. -/
theorem regular_mapLam_id
    (x : Compat (M := fun s => MonoidAlgebra R (G s))
      (fun s => (MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap)) :
    Compat.mapLam (π := π) _ (fun _ => LinearMap.id) (fun _ => rfl) (fun _ _ _ => rfl) x = x :=
  rfl

/-- `def:s04-Mord` (s04-Mord, D-Λ): the square `R[G s] × R[G s]` of the regular tower is
equivariant (via `Compat.IsEquivariant.prod`), so its `Compat` is a `Lam`-module. -/
theorem regular_prod_module :
    Nonempty (Module (Lam R G π)
      (Compat (M := fun s => MonoidAlgebra R (G s) × MonoidAlgebra R (G s))
      (fun s => ((MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap).prodMap
        ((MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap)))) := by
  have := Compat.IsEquivariant.prod (π := π) (M := fun s => MonoidAlgebra R (G s))
    (fun s => (MonoidAlgebra.mapDomainAlgHom R R (π s)).toLinearMap)
  exact ⟨inferInstance⟩

/-- `D-Λ` (s04-Mord): `Lam` is an `R`-algebra, with structure map the constant families. -/
theorem lam_algebraMap (r : R) (s : ℕ) :
    ((algebraMap R (Lam R G π) r : Lam R G π) : ∀ s, MonoidAlgebra R (G s)) s =
      MonoidAlgebra.single 1 r :=
  Lam.algebraMap_apply R G π r s

end LamTests

end Langlandscape.Ordinary.Tests
