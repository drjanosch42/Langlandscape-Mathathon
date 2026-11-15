/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Finiteness.Finsupp
import Langlandscape.Brandt.Corollaries
import Langlandscape.Ordinary.GroupRing
import Langlandscape.Ordinary.Tower

/-!
# Freeness of `e R[X_s]` over `R[Δ_s]` (S04-L10b)

`mathematics/chapters/s04/control.tex`, `prop:s04-freeA`; the `R[Δ_s]`-module structure used in
`thm:s04-control`(a). Specialisation `𝒪_E = ℤ_p`, `E = ℚ_p`, and the finite rings `ZMod (p ^ m)`.

* Permutation modules (abstract): for a finite commutative group `G` acting through `σ : G →* Perm X`,
  `PermMod R σ` is `R[X] = X →₀ R` with the `R[G]`-module structure `[g] · [x] = [σ g x]` (`permEnd`, `permAlg`).
  If the action is free, `R[X] ≃ (X/G) →₀ R[G]` (`orbitBasisEquiv`, via `orbitProdEquiv : X/G × G ≃ X`), so `R[X]` is
  `R[G]`-free (`permMod_free`), and `R[G]`-finite if `X` is finite (`permMod_finite`).
* If `T : End_R(R[X])` commutes with every `[g]`, then `ordPart T` and `nilPart q T` are `R[G]`-submodules
  (`ordPartG`, `nilPartG`), complementary under `HasOrdDecomp q T` (`isCompl_ordPartG`); over a local `R[G]` the
  ordinary part is then free (`free_ordPartG`) and finite (`finite_ordPartG`).
* The group: `Δ_s = (1 + pℤ_p) / (1 + p^s ℤ_p)` (`DeltaS p s`, the kernel of `(ℤ/p^s)^× → (ℤ/p)^×`; *only* `Δ_s`,
  not `(ℤ/p^s)^×`, is used, as in the tex), a finite `p`-group (`isPGroup_deltaS`, `card_deltaS`).
* The action: `deltaAct : Δ_s →* Perm X_s` from the stage-1 diamond action `Quat.diamondAct` (`[x] ↦ [x δ_t]`), free
  for `p ≥ 5` (`deltaAct_free`, from `Quat.diamondAct_free`); `U_p` commutes with it (`UpHom_comm_diamondAct`, the
  `R[X]`-transpose of the stage-1 `Brandt.Up_comm_diamond_self`).
* `prop:s04-freeA`: `ordFree_finite` (`e ℤ_p[X_s]` is a free `ℤ_p[Δ_s]`-module; formalized modulo
  `Hyp.PadicOrdDecomp`) and the unconditional `ordFree_finite_zmod` over `(ℤ/p^m)[Δ_s]`, `0 < m`; with
  `towerMod_free` (`R[X_s]` itself).

Status: *formalized* (`ZMod (p ^ m)`), *formalized modulo `Hyp.PadicOrdDecomp`* (`ℤ_[p]`; the `hdec` argument is
discharged in `Ordinary/TowerUncond.lean`, `ordFree_finite_uncond`). The rank constancy
`ordRank_const` of `thm:s04-control`(a) is **not** in this file (see the S04-L10b report).
-/

set_option autoImplicit false

open Langlandscape.Local Langlandscape.Quat Langlandscape.Brandt

namespace Langlandscape.Ordinary

open scoped Classical

noncomputable section

/-! ### Permutation modules over a group ring -/

section PermModule

variable (R : Type*) [CommRing R] {G : Type*} [CommGroup G] {X : Type*}

/-- `prop:s04-freeA` (`s04-freeA`): the permutation representation `g ↦ ([x] ↦ [σ g x])` of `G` on `R[X]`. -/
def permEnd (σ : G →* Equiv.Perm X) : G →* Module.End R (X →₀ R) where
  toFun g := Finsupp.lmapDomain R R (σ g)
  map_one' := LinearMap.ext fun v => by
    show Finsupp.mapDomain (σ 1) v = v
    rw [map_one, Equiv.Perm.coe_one, Finsupp.mapDomain_id]
  map_mul' g h := LinearMap.ext fun v => by
    show Finsupp.mapDomain (σ (g * h)) v = Finsupp.mapDomain (σ g) (Finsupp.mapDomain (σ h) v)
    rw [map_mul, Equiv.Perm.coe_mul, Finsupp.mapDomain_comp]

/-- `prop:s04-freeA` (`s04-freeA`): `permEnd R σ g = mapDomain (σ g)`. -/
theorem permEnd_apply (σ : G →* Equiv.Perm X) (g : G) :
    permEnd R σ g = Finsupp.lmapDomain R R (σ g) :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): the `R`-algebra map `R[G] → End_R(R[X])` of the permutation representation. -/
def permAlg (σ : G →* Equiv.Perm X) : MonoidAlgebra R G →ₐ[R] Module.End R (X →₀ R) :=
  MonoidAlgebra.lift R (Module.End R (X →₀ R)) G (permEnd R σ)

/-- `prop:s04-freeA` (`s04-freeA`): `permAlg (r [g]) = r • permEnd g`. -/
theorem permAlg_single (σ : G →* Equiv.Perm X) (g : G) (r : R) :
    permAlg R σ (MonoidAlgebra.single g r) = r • permEnd R σ g :=
  MonoidAlgebra.lift_single _ _ _

/-- `prop:s04-freeA` (`s04-freeA`): `R[X]` as an `R[G]`-module through `σ` (a type synonym of `X →₀ R`). -/
def PermMod (_σ : G →* Equiv.Perm X) : Type _ := X →₀ R

variable (σ : G →* Equiv.Perm X)

/-- `prop:s04-freeA` (`s04-freeA`): the additive group of `PermMod R σ` (that of `X →₀ R`). -/
instance : AddCommGroup (PermMod R σ) := inferInstanceAs (AddCommGroup (X →₀ R))

/-- `prop:s04-freeA` (`s04-freeA`): the `R`-module structure of `PermMod R σ` (that of `X →₀ R`). -/
instance : Module R (PermMod R σ) := inferInstanceAs (Module R (X →₀ R))

/-- `prop:s04-freeA` (`s04-freeA`): the `R[G]`-module structure of `PermMod R σ`, `a • v = permAlg a v`. -/
instance : Module (MonoidAlgebra R G) (PermMod R σ) :=
  Module.compHom (X →₀ R) (permAlg R σ).toRingHom

/-- `prop:s04-freeA` (`s04-freeA`): the identity `R[X] → PermMod R σ` (explicit bridge of the type synonym). -/
def PermMod.of (x : X →₀ R) : PermMod R σ := x

variable {R σ} in
/-- `prop:s04-freeA` (`s04-freeA`): the identity `PermMod R σ → R[X]` (explicit bridge of the type synonym). -/
def PermMod.val (v : PermMod R σ) : X →₀ R := v

/-- `prop:s04-freeA` (`s04-freeA`): `val (of x) = x`. -/
theorem PermMod.val_of (x : X →₀ R) : (PermMod.of R σ x).val = x :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `of (val v) = v`. -/
theorem PermMod.of_val (v : PermMod R σ) : PermMod.of R σ v.val = v :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `of 0 = 0`. -/
theorem PermMod.of_zero : PermMod.of R σ 0 = 0 :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `of (x + y) = of x + of y`. -/
theorem PermMod.of_add (x y : X →₀ R) : PermMod.of R σ (x + y) = PermMod.of R σ x + PermMod.of R σ y :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `val 0 = 0`. -/
theorem PermMod.val_zero : (0 : PermMod R σ).val = 0 :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `val (v + w) = val v + val w`. -/
theorem PermMod.val_add (v w : PermMod R σ) : (v + w).val = v.val + w.val :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `val (a • v) = permAlg a (val v)`. -/
theorem PermMod.val_smul (a : MonoidAlgebra R G) (v : PermMod R σ) :
    (a • v).val = permAlg R σ a v.val :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `a • of x = of (permAlg a x)`. -/
theorem PermMod.smul_of (a : MonoidAlgebra R G) (x : X →₀ R) :
    a • PermMod.of R σ x = PermMod.of R σ (permAlg R σ a x) :=
  rfl

/-- `prop:s04-freeA` (`s04-freeA`): `of` is bijective. -/
theorem PermMod.of_bijective : Function.Bijective (PermMod.of R σ) :=
  ⟨fun _ _ h => h, fun v => ⟨v.val, rfl⟩⟩

/-! #### Orbits of a free action -/

/-- `prop:s04-freeA` (`s04-freeA`): the orbit relation `x ~ y ↔ ∃ g, σ g x = y`. -/
def orbitSetoid : Setoid X where
  r x y := ∃ g : G, σ g x = y
  iseqv := ⟨fun _ => ⟨1, by rw [map_one, Equiv.Perm.one_apply]⟩,
    fun {x _} ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, map_inv]; exact (σ g).symm_apply_apply x⟩,
    fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by rw [map_mul, Equiv.Perm.mul_apply, hg, hh]⟩⟩

/-- `prop:s04-freeA` (`s04-freeA`): every `x` is `σ g` of the chosen representative of its orbit. -/
theorem orbitElt_exists (x : X) :
    ∃ g : G, σ g (Quotient.mk (orbitSetoid σ) x).out = x :=
  Quotient.mk_out (s := orbitSetoid σ) x

/-- `prop:s04-freeA` (`s04-freeA`): a group element moving the orbit representative of `x` to `x`. -/
def orbitElt (x : X) : G :=
  Classical.choose (orbitElt_exists σ x)

/-- `prop:s04-freeA` (`s04-freeA`): `σ (orbitElt x) (rep [x]) = x`. -/
theorem orbitElt_spec (x : X) : σ (orbitElt σ x) (Quotient.mk (orbitSetoid σ) x).out = x :=
  Classical.choose_spec (orbitElt_exists σ x)

/-- `prop:s04-freeA` (`s04-freeA`): for a free action, `X ≃ X/G × G`, `(q, g) ↦ σ g (rep q)`. -/
def orbitProdEquiv (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    Quotient (orbitSetoid σ) × G ≃ X where
  toFun qg := σ qg.2 qg.1.out
  invFun x := (Quotient.mk (orbitSetoid σ) x, orbitElt σ x)
  left_inv := by
    rintro ⟨q, g⟩
    have hq : Quotient.mk (orbitSetoid σ) (σ g q.out) = q :=
      ((Quotient.eq (r := orbitSetoid σ) (x := σ g q.out) (y := q.out)).2
        (show ∃ h : G, σ h (σ g q.out) = q.out from
          ⟨g⁻¹, by rw [map_inv]; exact (σ g).symm_apply_apply _⟩)).trans (Quotient.out_eq q)
    have hc : orbitElt σ (σ g q.out) = g := by
      have hs := orbitElt_spec σ (σ g q.out)
      rw [hq] at hs
      have h1 : σ (g⁻¹ * orbitElt σ (σ g q.out)) q.out = q.out := by
        rw [map_mul, Equiv.Perm.mul_apply, hs, map_inv]
        exact (σ g).symm_apply_apply _
      exact (inv_mul_eq_one.1 (hfree _ _ h1)).symm
    exact Prod.ext hq hc
  right_inv x := orbitElt_spec σ x

/-- `prop:s04-freeA` (`s04-freeA`): `orbitProdEquiv (q, g) = σ g (rep q)`. -/
theorem orbitProdEquiv_apply (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) (q : Quotient (orbitSetoid σ))
    (g : G) : orbitProdEquiv σ hfree (q, g) = σ g q.out :=
  rfl

/-! #### `R[X] ≃ (X/G) →₀ R[G]` -/

/-- `prop:s04-freeA` (`s04-freeA`): the `R[G]`-linear map `(X/G) →₀ R[G] → R[X]`, `[q] ↦ [rep q]`. -/
def orbitBasisMap :
    (Quotient (orbitSetoid σ) →₀ MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] PermMod R σ :=
  Finsupp.linearCombination (MonoidAlgebra R G)
    (fun q : Quotient (orbitSetoid σ) => PermMod.of R σ (Finsupp.single q.out (1 : R)))

/-- `prop:s04-freeA` (`s04-freeA`): `orbitBasisMap (r [g] · [q]) = r [σ g (rep q)]`. -/
theorem orbitBasisMap_single (q : Quotient (orbitSetoid σ)) (g : G) (r : R) :
    orbitBasisMap R σ (Finsupp.single q (MonoidAlgebra.single g r)) =
      PermMod.of R σ (Finsupp.single (σ g q.out) r) := by
  rw [orbitBasisMap, Finsupp.linearCombination_single, PermMod.smul_of, permAlg_single, LinearMap.smul_apply,
    permEnd_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `prop:s04-freeA` (`s04-freeA`): `uncurry [q ↦ [g ↦ r]] = [(q, g) ↦ r]`. -/
theorem curry_symm_single {α β : Type*} (a : α) (b : β) (r : R) :
    (Finsupp.curryLinearEquiv R).symm (Finsupp.single a (Finsupp.single b r)) = Finsupp.single (a, b) r := by
  rw [LinearEquiv.symm_apply_eq]
  exact (Finsupp.curry_single (a, b) r).symm

/-- `prop:s04-freeA` (`s04-freeA`): the `R`-linear equivalence `(X/G) →₀ R[G] ≃ (X/G × G) →₀ R ≃ X →₀ R`. -/
def orbitEquivR (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    (Quotient (orbitSetoid σ) →₀ MonoidAlgebra R G) ≃ₗ[R] (X →₀ R) :=
  (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv R)).trans
    ((Finsupp.curryLinearEquiv R).symm.trans (Finsupp.domLCongr (orbitProdEquiv σ hfree)))

/-- `prop:s04-freeA` (`s04-freeA`): `orbitEquivR (r [g] · [q]) = r [σ g (rep q)]`. -/
theorem orbitEquivR_single (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) (q : Quotient (orbitSetoid σ))
    (g : G) (r : R) :
    orbitEquivR R σ hfree (Finsupp.single q (MonoidAlgebra.single g r)) =
      Finsupp.single (orbitProdEquiv σ hfree (q, g)) r := by
  rw [orbitEquivR, LinearEquiv.trans_apply, LinearEquiv.trans_apply, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
    curry_symm_single, Finsupp.domLCongr_single]

/-- `prop:s04-freeA` (`s04-freeA`): `orbitBasisMap` and `orbitEquivR` agree as maps. -/
theorem orbitBasisMap_eq (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1)
    (v : Quotient (orbitSetoid σ) →₀ MonoidAlgebra R G) :
    orbitBasisMap R σ v = PermMod.of R σ (orbitEquivR R σ hfree v) := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, PermMod.of_zero]
  | add v w hv hw => rw [map_add, map_add, hv, hw, PermMod.of_add]
  | single q a =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [Finsupp.single_zero, map_zero, map_zero, PermMod.of_zero]
    | add a b ha hb => rw [Finsupp.single_add, map_add, map_add, ha, hb, PermMod.of_add]
    | single g r =>
      rw [orbitBasisMap_single, orbitEquivR_single, orbitProdEquiv_apply]

/-- `prop:s04-freeA` (`s04-freeA`): for a free action, `orbitBasisMap` is bijective. -/
theorem orbitBasisMap_bijective (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    Function.Bijective (orbitBasisMap R σ) := by
  have h : ⇑(orbitBasisMap R σ) = PermMod.of R σ ∘ ⇑(orbitEquivR R σ hfree) :=
    funext (orbitBasisMap_eq R σ hfree)
  rw [h]
  exact (PermMod.of_bijective R σ).comp (orbitEquivR R σ hfree).bijective

/-- `prop:s04-freeA` (`s04-freeA`): for a free action, `R[X] ≃ (X/G) →₀ R[G]` as `R[G]`-modules
(`R[X] = ⊕_i R[G] [x_i]`, one `x_i` in each orbit). -/
def orbitBasisEquiv (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    (Quotient (orbitSetoid σ) →₀ MonoidAlgebra R G) ≃ₗ[MonoidAlgebra R G] PermMod R σ :=
  LinearEquiv.ofBijective (orbitBasisMap R σ) (orbitBasisMap_bijective R σ hfree)

/-- `prop:s04-freeA` (`s04-freeA`), "freeness of `R[X_s]`": for a free action, `R[X]` is a free `R[G]`-module. -/
theorem permMod_free (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    Module.Free (MonoidAlgebra R G) (PermMod R σ) :=
  Module.Free.of_equiv (orbitBasisEquiv R σ hfree)

/-- `prop:s04-freeA` (`s04-freeA`): for a free action on a finite `X`, `R[X]` is a finite `R[G]`-module. -/
theorem permMod_finite [Finite X] (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) :
    Module.Finite (MonoidAlgebra R G) (PermMod R σ) :=
  Module.Finite.equiv (orbitBasisEquiv R σ hfree)

/-! #### The ordinary part as an `R[G]`-submodule -/

/-- `prop:s04-freeA` (`s04-freeA`), "`e` is `R[G]`-linear": if `T` commutes with every `[g]`, it commutes with every
`a ∈ R[G]`. -/
theorem permAlg_comm (T : Module.End R (X →₀ R)) (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g)
    (a : MonoidAlgebra R G) : permAlg R σ a ∘ₗ T = T ∘ₗ permAlg R σ a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_comp, LinearMap.comp_zero]
  | add a b ha hb => rw [map_add, LinearMap.add_comp, LinearMap.comp_add, ha, hb]
  | single g r => rw [permAlg_single, LinearMap.smul_comp, LinearMap.comp_smul, hT g]

/-- `prop:s04-freeA` (`s04-freeA`): `ordPart T = e R[X]` as an `R[G]`-submodule of `PermMod R σ` (for `T` commuting
with `G`). -/
def ordPartG (T : Module.End R (X →₀ R)) (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) :
    Submodule (MonoidAlgebra R G) (PermMod R σ) where
  carrier := {v | v.val ∈ ordPart T}
  add_mem' := by
    intro v w hv hw
    show (v + w).val ∈ ordPart T
    rw [PermMod.val_add]
    exact (ordPart T).add_mem hv hw
  zero_mem' := by
    show (0 : PermMod R σ).val ∈ ordPart T
    rw [PermMod.val_zero]
    exact (ordPart T).zero_mem
  smul_mem' := by
    intro a v hv
    show (a • v).val ∈ ordPart T
    rw [PermMod.val_smul]
    exact Submodule.mem_comap.1 (ordPart_map (permAlg R σ a) (permAlg_comm R σ T hT a) hv)

/-- `prop:s04-freeA` (`s04-freeA`): `nilPart q T = (1 - e) R[X]` as an `R[G]`-submodule of `PermMod R σ`. -/
def nilPartG (q : R) (T : Module.End R (X →₀ R))
    (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) :
    Submodule (MonoidAlgebra R G) (PermMod R σ) where
  carrier := {v | v.val ∈ nilPart q T}
  add_mem' := by
    intro v w hv hw
    show (v + w).val ∈ nilPart q T
    rw [PermMod.val_add]
    exact (nilPart q T).add_mem hv hw
  zero_mem' := by
    show (0 : PermMod R σ).val ∈ nilPart q T
    rw [PermMod.val_zero]
    exact (nilPart q T).zero_mem
  smul_mem' := by
    intro a v hv
    show (a • v).val ∈ nilPart q T
    rw [PermMod.val_smul]
    exact Submodule.mem_comap.1 (nilPart_map q (permAlg R σ a) (permAlg_comm R σ T hT a) hv)

/-- `prop:s04-freeA` (`s04-freeA`): membership in `ordPartG` is membership in `ordPart T`. -/
theorem mem_ordPartG (T : Module.End R (X →₀ R)) (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g)
    (v : PermMod R σ) : v ∈ ordPartG R σ T hT ↔ v.val ∈ ordPart T :=
  Iff.rfl

/-- `prop:s04-freeA` (`s04-freeA`): membership in `nilPartG` is membership in `nilPart q T`. -/
theorem mem_nilPartG (q : R) (T : Module.End R (X →₀ R))
    (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) (v : PermMod R σ) :
    v ∈ nilPartG R σ q T hT ↔ v.val ∈ nilPart q T :=
  Iff.rfl

/-- `prop:s04-freeA` (`s04-freeA`): under `HasOrdDecomp q T`, `R[X] = e R[X] ⊕ (1 - e) R[X]` is a decomposition of
`R[G]`-modules. -/
theorem isCompl_ordPartG (T : Module.End R (X →₀ R))
    (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) {q : R} (h : HasOrdDecomp q T) :
    IsCompl (ordPartG R σ T hT) (nilPartG R σ q T hT) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    have h0 : v.val = 0 := (Submodule.disjoint_def.1 (IsCompl.disjoint h)) v.val
      ((mem_ordPartG R σ T hT v).1 h1) ((mem_nilPartG R σ q T hT v).1 h2)
    rw [← PermMod.of_val R σ v, h0, PermMod.of_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v.val ∈ ordPart T ⊔ nilPart q T := by
      rw [(IsCompl.codisjoint h).eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hv
    rw [← PermMod.of_val R σ v, ← hyz, PermMod.of_add]
    exact Submodule.add_mem_sup
      ((mem_ordPartG R σ T hT _).2 (by rw [PermMod.val_of]; exact hy))
      ((mem_nilPartG R σ q T hT _).2 (by rw [PermMod.val_of]; exact hz))

/-- `prop:s04-freeA` (`s04-freeA`): for a free action on a finite `X` and a local `R[G]`, the ordinary part
`e R[X]` is a free `R[G]`-module (direct summand of a finite free module over a local ring, S04-L7). -/
theorem free_ordPartG [IsLocalRing (MonoidAlgebra R G)] [Finite X]
    (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1) (T : Module.End R (X →₀ R))
    (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) {q : R} (h : HasOrdDecomp q T) :
    Module.Free (MonoidAlgebra R G) (ordPartG R σ T hT) := by
  have := permMod_free R σ hfree
  have := permMod_finite R σ hfree
  exact free_of_isCompl (isCompl_ordPartG R σ T hT h)

/-- `prop:s04-freeA` (`s04-freeA`): for a free action on a finite `X`, the ordinary part `e R[X]` is a finite
`R[G]`-module (a direct summand of `R[X]`). -/
theorem finite_ordPartG [Finite X] (hfree : ∀ (g : G) (x : X), σ g x = x → g = 1)
    (T : Module.End R (X →₀ R)) (hT : ∀ g : G, permEnd R σ g ∘ₗ T = T ∘ₗ permEnd R σ g) {q : R}
    (h : HasOrdDecomp q T) : Module.Finite (MonoidAlgebra R G) (ordPartG R σ T hT) := by
  have := permMod_finite R σ hfree
  exact Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective (isCompl_ordPartG R σ T hT h))

end PermModule

/-! ### The group `Δ_s = (1 + pℤ_p) / (1 + p^s ℤ_p)` -/

section DeltaGroup

variable (p : ℕ) [Fact p.Prime]

/-- `prop:s04-freeA` (`s04-freeA`): the congruence subgroup `1 + p^k ℤ_p = {t ∈ ℤ_p^× | t ≡ 1 mod p^k}`. -/
def unitsCong (k : ℕ) : Subgroup ℤ_[p]ˣ where
  carrier := {t | (p : ℤ_[p]) ^ k ∣ (t : ℤ_[p]) - 1}
  one_mem' := by
    show (p : ℤ_[p]) ^ k ∣ ((1 : ℤ_[p]ˣ) : ℤ_[p]) - 1
    rw [Units.val_one, sub_self]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    show (p : ℤ_[p]) ^ k ∣ ((a * b : ℤ_[p]ˣ) : ℤ_[p]) - 1
    have e : ((a * b : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (a : ℤ_[p]) * ((b : ℤ_[p]) - 1) + ((a : ℤ_[p]) - 1) := by
      rw [Units.val_mul]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hb _) ha
  inv_mem' := by
    intro a ha
    show (p : ℤ_[p]) ^ k ∣ ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1
    have e : ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 = -(((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((a : ℤ_[p]) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e]
    exact (dvd_neg).2 (dvd_mul_of_dvd_right ha _)

/-- `prop:s04-freeA` (`s04-freeA`): reduction `1 + pℤ_p → (ℤ/p^s)^×`; its kernel is `1 + p^s ℤ_p`
(`redHom_eq_one_iff`). -/
def redHom (s : ℕ) : unitsCong p 1 →* (ZMod (p ^ s))ˣ :=
  (Units.map (PadicInt.toZModPow (p := p) s).toMonoidHom).comp (unitsCong p 1).subtype

/-- `prop:s04-freeA` (`s04-freeA`): `t ↦ 1 ∈ (ℤ/p^s)^×` iff `t ≡ 1 mod p^s`. -/
theorem redHom_eq_one_iff (s : ℕ) (t : unitsCong p 1) :
    redHom p s t = 1 ↔ (p : ℤ_[p]) ^ s ∣ ((t : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero,
    ← Units.val_eq_one]
  exact Iff.rfl

/-- `prop:s04-freeA`, `thm:s04-control` (`s04-freeA`): `Δ_s = (1 + pℤ_p) / (1 + p^s ℤ_p)`, the kernel of
`(ℤ/p^s)^× → (ℤ/p)^×`; it acts freely on `X_s` (`deltaAct_free`). A `def` (not an `abbrev`) carrying the single
group structure `instCommGroupDeltaS`, so that no second (`QuotientGroup.Quotient.group`) path is visible. -/
def DeltaS (s : ℕ) : Type := unitsCong p 1 ⧸ (redHom p s).ker

/-- `prop:s04-freeA` (`s04-freeA`): the class `[t] ∈ Δ_s` of `t ∈ 1 + pℤ_p`. -/
def DeltaS.mk (s : ℕ) (t : unitsCong p 1) : DeltaS p s :=
  (QuotientGroup.mk t : unitsCong p 1 ⧸ (redHom p s).ker)

/-- `prop:s04-freeA` (`s04-freeA`): `[·] : 1 + pℤ_p → Δ_s` is surjective. -/
theorem DeltaS.mk_surjective (s : ℕ) : Function.Surjective (DeltaS.mk p s) :=
  QuotientGroup.mk_surjective

/-- `prop:s04-freeA` (`s04-freeA`): the commutative group structure of `Δ_s` (the only one declared). -/
instance instCommGroupDeltaS (s : ℕ) : CommGroup (DeltaS p s) where
  toGroup := QuotientGroup.Quotient.group (redHom p s).ker
  mul_comm := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x * y = y * x := Subtype.ext (mul_comm (x : ℤ_[p]ˣ) y)
    exact (QuotientGroup.mk_mul (redHom p s).ker x y).symm.trans
      ((congrArg (fun z : unitsCong p 1 => (z : unitsCong p 1 ⧸ (redHom p s).ker)) hxy).trans
        (QuotientGroup.mk_mul (redHom p s).ker y x))

/-- `prop:s04-freeA` (`s04-freeA`): `[t^n] = [t]^n`. -/
theorem DeltaS.mk_pow (s : ℕ) (t : unitsCong p 1) (n : ℕ) :
    DeltaS.mk p s (t ^ n) = DeltaS.mk p s t ^ n :=
  QuotientGroup.mk_pow (redHom p s).ker t n

/-- `prop:s04-freeA` (`s04-freeA`): `[t] = 1` in `Δ_s` iff `t ≡ 1 mod p^s`. -/
theorem DeltaS.mk_eq_one_iff (s : ℕ) (t : unitsCong p 1) :
    DeltaS.mk p s t = 1 ↔ (p : ℤ_[p]) ^ s ∣ ((t : ℤ_[p]ˣ) : ℤ_[p]) - 1 :=
  ((QuotientGroup.eq_one_iff t).trans MonoidHom.mem_ker).trans (redHom_eq_one_iff p s t)

/-- `prop:s04-freeA` (`s04-freeA`): `Δ_s` is finite (it embeds into `(ℤ/p^s)^×`). -/
instance finite_deltaS (s : ℕ) : Finite (DeltaS p s) := by
  have : NeZero (p ^ s) := ⟨pow_ne_zero s (Fact.out : p.Prime).ne_zero⟩
  have hinj : Function.Injective
      (fun q : unitsCong p 1 ⧸ (redHom p s).ker =>
        ((QuotientGroup.kerLift (redHom p s) q : (ZMod (p ^ s))ˣ) : ZMod (p ^ s))) :=
    fun a b h => QuotientGroup.kerLift_injective (redHom p s) (Units.ext h)
  exact Finite.of_injective _ hinj

/-- `prop:s04-freeA` (`s04-freeA`): an element of `1 + pℤ_p` satisfies `p ∣ t - 1`. -/
theorem dvd_sub_one_of_mem (t : unitsCong p 1) : (p : ℤ_[p]) ∣ ((t : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
  have h := t.2
  change (p : ℤ_[p]) ^ 1 ∣ _ at h
  rwa [pow_one] at h

/-- `prop:s04-freeA` (`s04-freeA`), "`R[Δ_s]` is local": `Δ_s` is a `p`-group (`t^{p^s} ≡ 1 mod p^{s+1}`). -/
theorem isPGroup_deltaS (s : ℕ) : IsPGroup p (DeltaS p s) := by
  intro g
  obtain ⟨t, rfl⟩ := DeltaS.mk_surjective p s g
  refine ⟨s, ?_⟩
  rw [← DeltaS.mk_pow, DeltaS.mk_eq_one_iff]
  have h2 := dvd_sub_pow_of_dvd_sub (dvd_sub_one_of_mem p t) s
  rw [one_pow] at h2
  have he : (((t ^ p ^ s : unitsCong p 1) : ℤ_[p]ˣ) : ℤ_[p]) = ((t : ℤ_[p]ˣ) : ℤ_[p]) ^ p ^ s :=
    rfl
  rw [he]
  exact (pow_dvd_pow _ (Nat.le_succ s)).trans h2

/-- `prop:s04-freeA` (`s04-freeA`): `|Δ_s|` is a power of `p`. -/
theorem card_deltaS (s : ℕ) : ∃ n : ℕ, Nat.card (DeltaS p s) = p ^ n :=
  IsPGroup.iff_card.1 (isPGroup_deltaS p s)

end DeltaGroup

/-! ### The diamond action of `Δ_s` on `X_s` and the module `R[X_s]` -/

section Tower

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `prop:s04-freeA`, `lem:s01-stab` (b) (`s04-freeA`): the stage-1 diamond action `t ↦ ([x] ↦ [x δ_t])` of
`ℤ_p^×` on `X_s` as a group homomorphism. -/
def diamondHom (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) : ℤ_[p]ˣ →* Equiv.Perm (XB (d.Utower M p s hN)) where
  toFun := diamondAct (hp := hp) (hN := hN) hM hpM hs
  map_one' := diamondAct_eq_one (hp := hp) (hN := hN) hM hpM hs 1
    (by rw [Units.val_one, sub_self]; exact dvd_zero _)
  map_mul' := diamondAct_mul (hp := hp) (hN := hN) hM hpM hs

/-- `prop:s04-freeA` (`s04-freeA`): the action of `Δ_s` on `X_s` (`diamondAct` factors through `Δ_s`,
`Quat.diamondAct_eq_one`). -/
def deltaAct (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    DeltaS p s →* Equiv.Perm (XB (d.Utower M p s hN)) :=
  QuotientGroup.lift (redHom p s).ker
    ((diamondHom (hp := hp) (hN := hN) hM hpM hs).comp (unitsCong p 1).subtype)
    (fun t ht => (MonoidHom.mem_ker).2
      (diamondAct_eq_one (hp := hp) (hN := hN) hM hpM hs (t : ℤ_[p]ˣ)
        ((redHom_eq_one_iff p s t).1 ((MonoidHom.mem_ker).1 ht))))

/-- `prop:s04-freeA` (`s04-freeA`): `deltaAct [t] = diamondAct t`. -/
theorem deltaAct_mk (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : unitsCong p 1) :
    deltaAct (hp := hp) (hN := hN) hM hpM hs (DeltaS.mk p s t) =
      diamondAct (hp := hp) (hN := hN) hM hpM hs (t : ℤ_[p]ˣ) :=
  rfl

/-- `prop:s04-freeA`, `lem:s01-stab` (b′) (`s04-freeA`), N2: for `p ≥ 5`, `Δ_s` acts freely on `X_s`
(`Quat.diamondAct_free`). -/
theorem deltaAct_free (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) (g : DeltaS p s)
    (c : XB (d.Utower M p s hN)) (hc : deltaAct (hp := hp) hM hpM hs g c = c) : g = 1 := by
  obtain ⟨t, rfl⟩ := DeltaS.mk_surjective p s g
  rw [deltaAct_mk] at hc
  exact (DeltaS.mk_eq_one_iff p s t).2 (diamondAct_free hM hpM hs h5 _ (dvd_sub_one_of_mem p t) c hc)

/-- `prop:s04-freeA` (`s04-freeA`), auxiliary: `⟨mapDomain σ x, f⟩ = ⟨x, f ∘ σ⟩` for the evaluation pairing. -/
theorem evalPairing_mapDomain {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (R : Type*) [CommRing R]
    (σ : XB U → XB U) (x : ZX U R) (f : ZXdual U R) :
    evalPairing U R (Finsupp.mapDomain σ x) f = evalPairing U R x (f ∘ σ) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [Finsupp.mapDomain_add, hx, hy]
  | single c r => simp [evalPairing_single]

/-- `prop:s04-freeA`, `lem:s01-Up`(e) (`s04-freeA`): on `R[X_s]`, `U_p` commutes with the diamond action
`[x] ↦ [x δ_t]` (the `R[X]`-transpose of the stage-1 `Brandt.Up_comm_diamond_self`). -/
theorem UpHom_comm_diamondAct (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (t : ℤ_[p]ˣ) :
    UpHom d M p s hN hp hM hpM hs R ∘ₗ Finsupp.lmapDomain R R (diamondAct (hp := hp) (hN := hN) hM hpM hs t) =
      Finsupp.lmapDomain R R (diamondAct (hp := hp) (hN := hN) hM hpM hs t) ∘ₗ
        UpHom d M p s hN hp hM hpM hs R := by
  have hn := diamondElt_inv_normalizes_Utower (hℓ := hp) (hN := hN) hM hpM hs t
  have hcomm := Up_comm_diamond_self (hp := hp) (hN := hN) R hM hpM hs t hn
  have hT : ∀ (y : ZX (d.Utower M p s hN) R) (f : ZXdual (d.Utower M p s hN) R),
      evalPairing _ R (UpHom d M p s hN hp hM hpM hs R y) f =
        evalPairing _ R y (Up d M p s hN hp hM hpM hs R f) :=
    fun y f => heckeTHom_transpose _ _ R _ y f
  have hD : ∀ f : ZXdual (d.Utower M p s hN) R,
      diamond d (d.Utower M p s hN) p hp R t hn f = f ∘ diamondAct (hp := hp) (hN := hN) hM hpM hs t :=
    fun f => funext fun c => diamond_apply_eq_diamondAct (hℓ := hp) R hM hpM hs t hn f c
  have key : ∀ (x : ZX (d.Utower M p s hN) R) (f : ZXdual (d.Utower M p s hN) R),
      evalPairing _ R (UpHom d M p s hN hp hM hpM hs R
          (Finsupp.mapDomain (diamondAct (hp := hp) (hN := hN) hM hpM hs t) x)) f =
        evalPairing _ R (Finsupp.mapDomain (diamondAct (hp := hp) (hN := hN) hM hpM hs t)
          (UpHom d M p s hN hp hM hpM hs R x)) f := by
    intro x f
    have hc : diamond d (d.Utower M p s hN) p hp R t hn (Up d M p s hN hp hM hpM hs R f) =
        Up d M p s hN hp hM hpM hs R (diamond d (d.Utower M p s hN) p hp R t hn f) :=
      (LinearMap.congr_fun hcomm f).symm
    rw [hT, evalPairing_mapDomain, evalPairing_mapDomain, ← hD, ← hD, hc, ← hT]
  refine LinearMap.ext fun x => Finsupp.ext fun c => ?_
  have h := key x (Pi.single c (1 : R))
  rw [evalPairing_pi_single, evalPairing_pi_single] at h
  exact h

/-- `prop:s04-freeA` (`s04-freeA`): `U_p` commutes with every `[g]`, `g ∈ Δ_s`, on `R[X_s]`. -/
theorem permEnd_comm_UpHom (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (g : DeltaS p s) :
    permEnd R (deltaAct (hp := hp) (hN := hN) hM hpM hs) g ∘ₗ UpHom d M p s hN hp hM hpM hs R =
      UpHom d M p s hN hp hM hpM hs R ∘ₗ permEnd R (deltaAct (hp := hp) (hN := hN) hM hpM hs) g := by
  obtain ⟨t, rfl⟩ := DeltaS.mk_surjective p s g
  rw [permEnd_apply, deltaAct_mk]
  exact (UpHom_comm_diamondAct R hM hpM hs (t : ℤ_[p]ˣ)).symm

/-- `prop:s04-freeA` (`s04-freeA`): `R[X_s]` as an `R[Δ_s]`-module through the diamond action. -/
abbrev TowerMod (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D)
    (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) : Type _ :=
  PermMod R (deltaAct (hp := hp) (hN := hN) hM hpM hs)

/-- `prop:s04-freeA` (`s04-freeA`): `e R[X_s]` (ordinary part of `U_p`) as an `R[Δ_s]`-submodule of `R[X_s]`. -/
abbrev ordPartTower (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule (MonoidAlgebra R (DeltaS p s)) (TowerMod d M p s hN hp R hM hpM hs) :=
  ordPartG R (deltaAct (hp := hp) (hN := hN) hM hpM hs) (UpHom d M p s hN hp hM hpM hs R)
    (permEnd_comm_UpHom R hM hpM hs)

/-- `prop:s04-freeA` (`s04-freeA`): `x ∈ ordPartTower ↔ x ∈ e R[X_s] = ordPart U_p`. -/
theorem mem_ordPartTower (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (v : TowerMod d M p s hN hp R hM hpM hs) :
    v ∈ ordPartTower d M p s hN hp R hM hpM hs ↔ v.val ∈ ordPart (UpHom d M p s hN hp hM hpM hs R) :=
  Iff.rfl

/-- `prop:s04-freeA` (`s04-freeA`), "freeness of `R[X_s]`": for `p ≥ 5`, `R[X_s]` is a finite free
`R[Δ_s]`-module (any commutative `R`). -/
theorem towerMod_free (R : Type*) [CommRing R] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra R (DeltaS p s)) (TowerMod d M p s hN hp R hM hpM hs) ∧
      Module.Finite (MonoidAlgebra R (DeltaS p s)) (TowerMod d M p s hN hp R hM hpM hs) :=
  ⟨permMod_free R (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5),
    permMod_finite R (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5)⟩

/-- `prop:s04-freeA` (`s04-freeA`) over `ℤ_p` (for `E = ℚ_p`; formalized modulo `Hyp.PadicOrdDecomp`): for `s ≥ 1`,
`p ≥ 5`, `e ℤ_p[X_s]` is a finite free `ℤ_p[Δ_s]`-module. -/
theorem ordFree_finite (hdec : Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra ℤ_[p] (DeltaS p s)) (ordPartTower d M p s hN hp ℤ_[p] hM hpM hs) ∧
      Module.Finite (MonoidAlgebra ℤ_[p] (DeltaS p s)) (ordPartTower d M p s hN hp ℤ_[p] hM hpM hs) := by
  obtain ⟨n, hn⟩ := card_deltaS p s
  have : IsLocalRing (MonoidAlgebra ℤ_[p] (DeltaS p s)) := isLocalRing_monoidAlgebra_padicInt p hn
  have h := hdec (ZX (d.Utower M p s hN) ℤ_[p]) (UpHom d M p s hN hp hM hpM hs ℤ_[p])
  exact ⟨free_ordPartG ℤ_[p] (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5)
      (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (permEnd_comm_UpHom ℤ_[p] hM hpM hs) h,
    finite_ordPartG ℤ_[p] (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5)
      (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (permEnd_comm_UpHom ℤ_[p] hM hpM hs) h⟩

/-- `prop:s04-freeA` (`s04-freeA`), unconditional over `ZMod (p ^ m)`, `0 < m`: for `s ≥ 1`, `p ≥ 5`,
`e (ℤ/p^m)[X_s]` is a finite free `(ℤ/p^m)[Δ_s]`-module. -/
theorem ordFree_finite_zmod (m : ℕ) (hm : 0 < m) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (h5 : 5 ≤ p) :
    Module.Free (MonoidAlgebra (ZMod (p ^ m)) (DeltaS p s))
        (ordPartTower d M p s hN hp (ZMod (p ^ m)) hM hpM hs) ∧
      Module.Finite (MonoidAlgebra (ZMod (p ^ m)) (DeltaS p s))
        (ordPartTower d M p s hN hp (ZMod (p ^ m)) hM hpM hs) := by
  obtain ⟨n, hn⟩ := card_deltaS p s
  have : IsLocalRing (MonoidAlgebra (ZMod (p ^ m)) (DeltaS p s)) := isLocalRing_monoidAlgebra_zmod p hm hn
  have := finite_finsupp_zmodPow (XB (d.Utower M p s hN)) p m
  have h := hasOrdDecomp_zmodPow p m (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m)))
  exact ⟨free_ordPartG (ZMod (p ^ m)) (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5)
      (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) (permEnd_comm_UpHom (ZMod (p ^ m)) hM hpM hs) h,
    finite_ordPartG (ZMod (p ^ m)) (deltaAct (hp := hp) (hN := hN) hM hpM hs) (deltaAct_free hM hpM hs h5)
      (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) (permEnd_comm_UpHom (ZMod (p ^ m)) hM hpM hs) h⟩

end Tower

end

end Langlandscape.Ordinary
