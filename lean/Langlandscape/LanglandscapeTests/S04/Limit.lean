/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Algebra.Exact.Basic
import Langlandscape.Ordinary.Limit

/-!
# Tests for `Langlandscape.Ordinary.Limit` (S04-L13b, D-lim, D-Λ)

* the snake step `surjective_of_snake` on the split sequence `R → R × R → R` with identity transitions;
* `lim_exact_of_snake` on the constant split tower;
* `Compat.lamModuleOfRep` for the trivial representation of an arbitrary tower of groups;
* the tower statements (`Mord.proj_surjective`, `lim_exact_ribet`) instantiate.
-/

namespace Langlandscape.Ordinary.Tests

open Langlandscape.Ordinary

section Abstract

variable (R : Type*) [CommRing R]

/-- `thm:s04-lambdaribet`(a), D-lim snake step (`s04-lambdaribet`): on the split sequence `R → R × R → R` with
identity transitions, `surjective_of_snake` gives the surjectivity of the kernel transition `id`. -/
theorem snake_split_id : Function.Surjective (LinearMap.id : R →ₗ[R] R) :=
  surjective_of_snake (LinearMap.inl R R R) (LinearMap.snd R R R) (LinearMap.inl R R R) (LinearMap.snd R R R)
    LinearMap.id LinearMap.id LinearMap.id rfl rfl Function.Exact.inl_snd Function.Exact.inl_snd
    LinearMap.inl_injective Function.surjective_id (fun _ hz => ⟨0, rfl, hz.symm⟩)

/-- `thm:s04-lambdaribet`(a), `lem:s04-limexact` (`s04-lambdaribet`): `lim_exact_of_snake` on the constant split
tower `0 → R → R × R → R → 0` (identity transitions). -/
theorem lim_exact_of_snake_const :
    Function.Surjective
      (Compat.map (M := fun _ : ℕ => R × R) (N := fun _ : ℕ => R)
        (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id)
        (fun _ => LinearMap.snd R R R) (fun _ => rfl)) :=
  (lim_exact_of_snake (R := R) (M := fun _ : ℕ => R) (N := fun _ : ℕ => R × R) (P := fun _ : ℕ => R)
    (f := fun _ => LinearMap.id) (g := fun _ => LinearMap.id) (h := fun _ => LinearMap.id)
    (fun _ => LinearMap.inl R R R) (fun _ => LinearMap.snd R R R) (fun _ => rfl) (fun _ => rfl)
    (fun _ => LinearMap.inl_injective) (fun _ => Function.Exact.inl_snd) (fun _ => LinearMap.snd_surjective)
    (fun _ => Function.surjective_id) (fun _ _ hz => ⟨0, rfl, by simpa using hz.symm⟩)).2.2

/-- `def:s04-Mord`, D-Λ (`s04-Mord`): the trivial representation of any tower of groups makes the limit of the
constant system `R` a `Lam`-module (`Compat.lamModuleOfRep`). -/
theorem lamModuleOfRep_trivial (G : ℕ → Type*) [∀ s, CommGroup (G s)] (π : ∀ s, G (s + 1) →* G s) :
    Nonempty (Module (Lam R G π) (Compat (R := R) (M := fun _ : ℕ => R) (fun _ => LinearMap.id))) :=
  ⟨Compat.lamModuleOfRep (R := R) (M := fun _ : ℕ => R) (π := π) (fun _ => LinearMap.id) (fun _ => 1)
    (fun _ _ => rfl)⟩

end Abstract

section Tower

variable {d : Langlandscape.Quat.DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`): the projection `M_ord(U) → e ℤ_p[X_1]` is surjective, modulo
`Hyp.PadicOrdDecomp`. -/
theorem mord_proj_zero_surjective (T : TowerHyp d M p) (hdec : Langlandscape.Hyp.PadicOrdDecomp p) :
    Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans 0) :=
  Mord.proj_surjective T hdec 0

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): `lim_exact_ribet` instantiates (surjectivity of `α` on the
limits). -/
theorem alphaLim_surjective (H : RibetHyp d q M p) (hdec : Langlandscape.Hyp.PadicOrdDecomp p)
    (hconn : ∀ s ≥ 1, Langlandscape.Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s))
      (Langlandscape.Tree.isQLevel_Utower (H.hqN s)))
    (hA : ∀ n, Function.Surjective (H.transA n)) :
    Function.Surjective (alphaLim H) :=
  (lim_exact_ribet H hdec hconn hA).2.2

end Tower

end Langlandscape.Ordinary.Tests
