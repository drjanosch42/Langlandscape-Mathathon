/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.HypX
import Langlandscape.Ordinary.TowerUncond
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# `prop:s05-Xlambda`(a) at finite level: `e (X_q(J_s) ⊗ ℤ_p) ≃ e ℤ_p[S_s]` (S05-L7)

Tex: `prop:s05-Xlambda`(a) (`s05-Xlambda`) in `mathematics/chapters/s05/hypX.tex`;
stage 04 input `if:s04-ekills`(a) (`lem:s04-ekills`(a), `s04-ekills`).
Status: *formalized* **under `Hyp.X.char`** (the finite-level part of (a); no `Hyp.PadicOrdDecomp`:
it is discharged, `Ordinary.ekillsA_tower_uncond`).

For `G : CharGroupData M q p`, a family `φ_s : X s ≃ ℤ[S_s]⁰` with (X1) (as in `Hyp.X.char G`) and a level `s`:

* `xlambdaPsi φ s`: **the** `ℤ_[p]`-linear isomorphism `Ψ_s : ℤ_[p] ⊗ X s ≃ ℤ_[p][S_s]⁰` induced by `φ_s`
  (`S_s = X_B(U_s)`, `⁰ = ker deg`, `deg = Ordinary.deg`), a definition.
* `xlambdaPsi_equivariant`: `Ψ_s ∘ (act h ⊗ 1) = F ∘ Ψ_s` for every `h ∈ ℋ_s` and every operator `F` on
  `ℤ_[p][S_s]` which is `θ(h) ⊗ ℤ_[p]` on basis vectors (hypothesis `hF`); `xlambdaPsi_Up`,
  `xlambdaPsi_comp_Up`: for `s ≥ 1`, `Ψ_s` intertwines `U_p ⊗ 1` with `UpHom` (`U_p ↦ N_{U_p}`, `def:s05-theta`).
  The identification of `F` with the natural `ℤ_[p]`-operator is formalized only for `U_p`
  (`UpHom_isBaseChange`), not for `T_ℓ`, `⟨u⟩`, `U_q`, `T_p`.
* `xlambdaOrd φ hφ s hs`: **the deliverable**, the isomorphism `e (ℤ_[p] ⊗ X s) ≃ e ℤ_[p][S_s]` induced by
  `φ_s` (`xlambdaOrd_apply`: it is `Ψ_s` on elements), `s ≥ 1`, with `e = ordPart` of `U_p ⊗ 1` on the left and
  of `UpHom` on the right (degree zero is absorbed by `lem:s04-ekills`(a): `e ℤ_[p][S_s]⁰ = e ℤ_[p][S_s]`).
* Under `Hyp.X.char G`: `xlambda_finite_iso` (`∃ Ψ`, `U_p`), `xlambda_finite` (`Nonempty`, corollary of
  `xlambdaOrd`), `xlambda_equivariant` (one `φ` with (X1) and the equivariance of `xlambdaPsi φ s` for all
  `s`, `h`, `F`).

Not formalized here (docstring remarks; `prop:s05-Xlambda` stays *proved* in the tex):
* the compatibility with `β`/`pushforward` (the transition maps of the tower): it needs (X3) in the same
  base-changed form; every statement is of the same shape as `xlambda_equivariant`;
* the `ZMod (p ^ m)` form: `ℤ/p^m` is not flat over `ℤ`, so the base-change step would need the splitting
  of `0 → ℤ[S]⁰ → ℤ[S] → ℤ → 0` (`ekillsA_tower_zmod` itself is unconditional and available);
* the limit version `Φ : lim e (X ⊗ ℤ_p) ≃ Mord` (`if:s04-Mord`, `Ordinary/Limit.lean`, a hypothesis
  there): not stated.

The file is not a `module`: it imports `Hyp/HypX.lean`, which depends on GL2TF.
-/

set_option autoImplicit false

open scoped TensorProduct Classical

namespace Langlandscape.Comparison

noncomputable section

/-! ### Generic transport of the ordinary part along an equivalence -/

section Transport

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), generic: an equivalence `e` with `e ∘ T = T' ∘ e` carries
`ordPart T` onto `ordPart T'`. -/
theorem map_ordPart_equiv (e : M ≃ₗ[R] N) {T : Module.End R M} {T' : Module.End R N}
    (hf : (e : M →ₗ[R] N) ∘ₗ T = T' ∘ₗ (e : M →ₗ[R] N)) :
    (Ordinary.ordPart T).map (e : M →ₗ[R] N) = Ordinary.ordPart T' := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.2 (Ordinary.ordPart_map _ hf)
  · have hf' : (e.symm : N →ₗ[R] M) ∘ₗ T' = T ∘ₗ (e.symm : N →ₗ[R] M) := by
      refine LinearMap.ext fun y => ?_
      apply e.injective
      have h := LinearMap.congr_fun hf (e.symm y)
      simpa using h.symm
    intro y hy
    exact ⟨e.symm y, Submodule.mem_comap.1 (Ordinary.ordPart_map _ hf' hy), by simp⟩

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), generic: `e ∘ T = T' ∘ e` gives `e ordPart T ≃ ordPart T'`
(an equivalence of the ordinary parts). -/
def ordPartEquiv (e : M ≃ₗ[R] N) {T : Module.End R M} {T' : Module.End R N}
    (hf : (e : M →ₗ[R] N) ∘ₗ T = T' ∘ₗ (e : M →ₗ[R] N)) :
    Ordinary.ordPart T ≃ₗ[R] Ordinary.ordPart T' :=
  e.ofSubmodules _ _ (map_ordPart_equiv e hf)

end Transport

/-! ### Base change of `R[X]` and of its degree-zero part along a flat `ℤ`-algebra -/

section BaseChange

variable (B : Type*) [CommRing B] (X : Type*) [DecidableEq X]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): the comparison `B ⊗_ℤ ℤ[X] ≃ B[X]`. -/
def scalarIso : B ⊗[ℤ] (X →₀ ℤ) ≃ₗ[B] (X →₀ B) :=
  TensorProduct.finsuppScalarRight ℤ B B X

variable {B X}

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `scalarIso (b ⊗ [x]^n) = (n b) [x]`. -/
theorem scalarIso_tmul_single (b : B) (x : X) (n : ℤ) :
    scalarIso B X (b ⊗ₜ Finsupp.single x n) = Finsupp.single x (n • b) := by
  simp [scalarIso, TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_single_index]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): the degree on `B ⊗ ℤ[X]` corresponds to `1 ⊗ deg`. -/
theorem deg_scalarIso (t : B ⊗[ℤ] (X →₀ ℤ)) :
    Ordinary.deg X B (scalarIso B X t) =
      TensorProduct.AlgebraTensorModule.rid ℤ B B (LinearMap.lTensor B (Ordinary.deg X ℤ) t) := by
  induction t with
  | tmul b z =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [TensorProduct.tmul_add, map_add, hf, hg]
    | single x n =>
      simp [scalarIso_tmul_single, TensorProduct.AlgebraTensorModule.rid_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `baseChange` and `lTensor` agree as functions. -/
theorem baseChange_apply_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (t : B ⊗[ℤ] M) : f.baseChange B t = f.lTensor B t := by
  induction t with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `Φ (b ⊗ f z) = F (Φ (b ⊗ z))` as soon as `F` is the base change
of `f` on the basis vectors (`hF`). -/
theorem scalarIso_comm (f : Module.End ℤ (X →₀ ℤ)) (F : Module.End B (X →₀ B))
    (hF : ∀ (x : X) (b : B),
      F (Finsupp.single x b) = scalarIso B X (b ⊗ₜ f (Finsupp.single x 1)))
    (b : B) (z : X →₀ ℤ) :
    scalarIso B X (b ⊗ₜ f z) = F (scalarIso B X (b ⊗ₜ z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, TensorProduct.tmul_add, hu, hv]
  | single x n =>
    have h1 : (Finsupp.single x n : X →₀ ℤ) = n • Finsupp.single x (1 : ℤ) := by simp
    have h2 : (Finsupp.single x (n • b) : X →₀ B) = n • Finsupp.single x b := by simp
    rw [scalarIso_tmul_single, h2, map_zsmul, hF, h1, map_zsmul, TensorProduct.tmul_smul,
      map_zsmul]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: the base change of `ι : ℤ[X]⁰ → ℤ[X]` composed with
`scalarIso`, with values in `B[X]`. -/
def degZeroMap : B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ) →ₗ[B] (X →₀ B) :=
  (scalarIso B X).toLinearMap ∘ₗ (LinearMap.ker (Ordinary.deg X ℤ)).subtype.baseChange B

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: `degZeroMap (b ⊗ k) = Φ (b ⊗ k)`. -/
theorem degZeroMap_apply (t : B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ)) :
    degZeroMap t = scalarIso B X ((LinearMap.ker (Ordinary.deg X ℤ)).subtype.lTensor B t) := by
  rw [degZeroMap, LinearMap.comp_apply, LinearEquiv.coe_coe, baseChange_apply_eq]

variable [Module.Flat ℤ B]

omit [DecidableEq X] in
/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: exactness of `B ⊗ -` on `0 → ℤ[X]⁰ → ℤ[X] → ℤ`. -/
theorem exact_lTensor_deg :
    Function.Exact ((LinearMap.ker (Ordinary.deg X ℤ)).subtype.lTensor B)
      ((Ordinary.deg X ℤ).lTensor B) :=
  Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map _)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: the image of `degZeroMap` has degree zero. -/
theorem deg_degZeroMap (t : B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ)) :
    Ordinary.deg X B (degZeroMap t) = 0 := by
  rw [degZeroMap_apply, deg_scalarIso]
  have h := (exact_lTensor_deg (B := B) (X := X)
    ((LinearMap.ker (Ordinary.deg X ℤ)).subtype.lTensor B t)).2 ⟨t, rfl⟩
  rw [h, map_zero]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: `degZeroMap` is injective (flatness). -/
theorem degZeroMap_injective : Function.Injective (degZeroMap (B := B) (X := X)) := by
  intro t t' h
  rw [degZeroMap_apply, degZeroMap_apply] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (LinearMap.ker (Ordinary.deg X ℤ)).subtype (Subtype.val_injective) ((scalarIso B X).injective h)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: every degree-zero element of `B[X]` is in the image of
`degZeroMap` (flatness: exactness in the middle). -/
theorem degZeroMap_surjective {y : X →₀ B} (hy : Ordinary.deg X B y = 0) :
    ∃ t, degZeroMap t = y := by
  have h0 : TensorProduct.AlgebraTensorModule.rid ℤ B B
      (LinearMap.lTensor B (Ordinary.deg X ℤ) ((scalarIso B X).symm y)) = 0 := by
    rw [← deg_scalarIso, LinearEquiv.apply_symm_apply, hy]
  have h1 : LinearMap.lTensor B (Ordinary.deg X ℤ) ((scalarIso B X).symm y) = 0 :=
    (LinearEquiv.map_eq_zero_iff _).1 h0
  obtain ⟨t, ht⟩ := (exact_lTensor_deg (B := B) (X := X) _).1 h1
  refine ⟨t, ?_⟩
  rw [degZeroMap_apply, ht, LinearEquiv.apply_symm_apply]

variable (B X) in
/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): for `B` flat over `ℤ`, `B ⊗_ℤ ℤ[X]⁰ ≃ B[X]⁰`
(`⁰ = ker deg`, `deg = Ordinary.deg`). -/
def degZeroBaseChange :
    B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ) ≃ₗ[B] LinearMap.ker (Ordinary.deg X B) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (LinearMap.ker (Ordinary.deg X B)) degZeroMap
      (fun t => LinearMap.mem_ker.2 (deg_degZeroMap t)))
    ⟨fun t t' h => degZeroMap_injective (congrArg Subtype.val h),
     fun y => by
      obtain ⟨t, ht⟩ := degZeroMap_surjective (LinearMap.mem_ker.1 y.2)
      exact ⟨t, Subtype.ext ht⟩⟩

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): the underlying element of `degZeroBaseChange t` is
`degZeroMap t`. -/
@[simp] theorem coe_degZeroBaseChange (t : B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ)) :
    ((degZeroBaseChange B X t : LinearMap.ker (Ordinary.deg X B)) : X →₀ B) = degZeroMap t :=
  rfl

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `degZeroBaseChange` intertwines the base change of an
endomorphism `f'` of `ℤ[X]⁰` (the restriction of `f`) with a ring-`B` operator `F` that is `f ⊗ B` on basis
vectors (`hF`). -/
theorem degZeroBaseChange_comm (f : Module.End ℤ (X →₀ ℤ)) (F : Module.End B (X →₀ B))
    (hF : ∀ (x : X) (b : B),
      F (Finsupp.single x b) = scalarIso B X (b ⊗ₜ f (Finsupp.single x 1)))
    (f' : Module.End ℤ (LinearMap.ker (Ordinary.deg X ℤ)))
    (hf' : ∀ k, ((f' k : LinearMap.ker (Ordinary.deg X ℤ)) : X →₀ ℤ) = f k)
    (t : B ⊗[ℤ] LinearMap.ker (Ordinary.deg X ℤ)) :
    ((degZeroBaseChange B X (f'.baseChange B t) : LinearMap.ker (Ordinary.deg X B)) : X →₀ B) =
      F (degZeroBaseChange B X t : X →₀ B) := by
  induction t with
  | tmul b k =>
    rw [LinearMap.baseChange_tmul, coe_degZeroBaseChange, coe_degZeroBaseChange, degZeroMap_apply,
      degZeroMap_apply, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      Submodule.subtype_apply, hf', scalarIso_comm f F hF]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

end BaseChange

/-! ### Flatness of `ℤ_[p]` over `ℤ` -/

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `ℤ_[p]` is flat over `ℤ` (torsion-free over a Dedekind domain). -/
theorem flat_padicInt (p : ℕ) [Fact p.Prime] : Module.Flat ℤ ℤ_[p] := by
  have : Module.IsTorsionFree ℤ ℤ_[p] :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => by
      rw [zsmul_eq_mul] at h
      rcases mul_eq_zero.1 h with h | h
      · left
        exact_mod_cast h
      · right
        exact h)
  infer_instance

/-! ### The theorem -/

section Main

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Hyp.X

variable (d : DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
  (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
  (hD : d.D = q) (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)
  (G : CharGroupData M q p)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), helper: the operator `U_p` on `ℤ_[p][S_s]` is the base change of
the operator `U_p` on `ℤ[S_s]` on basis vectors (`UpHom_single`). -/
theorem UpHom_isBaseChange (s : ℕ) (hs : 1 ≤ s) (c : XB (d.Utower M p s (hN s))) (b : ℤ_[p]) :
    UpHom d M p s (hN s) hp hM hpM hs ℤ_[p] (Finsupp.single c b) =
      scalarIso ℤ_[p] (XB (d.Utower M p s (hN s)))
        (b ⊗ₜ UpHom d M p s (hN s) hp hM hpM hs ℤ (Finsupp.single c 1)) := by
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s (hN s)) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  rw [UpHom_single (d := d) (hN := hN s) (hp := hp) (R := ℤ_[p]) hM hpM hs x b,
    UpHom_single (d := d) (hN := hN s) (hp := hp) (R := ℤ) hM hpM hs x 1,
    TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scalarIso_tmul_single, one_smul]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): the first factor of `Ψ`, `1 ⊗ φ_s : ℤ_[p] ⊗ X s ≃ ℤ_[p] ⊗ ℤ[S_s]⁰`
for a family `φ` as in (X1). -/
def xlambdaCong (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ) (s : ℕ) :
    ℤ_[p] ⊗[ℤ] G.X s ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] degZero (d.Utower M p s (hN s)) ℤ :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℤ_[p] ℤ_[p]) (φ s)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): **the** isomorphism `Ψ_s : ℤ_[p] ⊗ X s ≃ ℤ_[p][S_s]⁰` induced by
`φ_s`, `Ψ_s = degZeroBaseChange ∘ (1 ⊗ φ_s)` (flatness of `ℤ_[p]` over `ℤ`, `flat_padicInt`). -/
def xlambdaPsi (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ) (s : ℕ) :
    ℤ_[p] ⊗[ℤ] G.X s ≃ₗ[ℤ_[p]] degZero (d.Utower M p s (hN s)) ℤ_[p] :=
  haveI : Module.Flat ℤ ℤ_[p] := flat_padicInt p
  (xlambdaCong d M p q hN G φ s).trans (degZeroBaseChange ℤ_[p] (XB (d.Utower M p s (hN s))))

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), Hecke-equivariance of the one isomorphism `Ψ_s = xlambdaPsi φ s`:
if `φ` satisfies (X1), then for every `h ∈ ℋ_s` and every operator `F` on `ℤ_[p][S_s]` which is `θ(h) ⊗ ℤ_[p]` on
basis vectors (`hF`), `Ψ_s ∘ (act h ⊗ 1) = F ∘ Ψ_s`. `hF` is always satisfiable (conjugated base change); its
identification with the natural `ℤ_[p]`-operator is formalized only for `U_p` (`UpHom_isBaseChange`), not for
`T_ℓ`, `⟨u⟩`, `U_q`, `T_p`. -/
theorem xlambdaPsi_equivariant (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (hφ : ∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x))
    (s : ℕ) (h : HeckeSym M p q s) (F : Module.End ℤ_[p] (ZX (d.Utower M p s (hN s)) ℤ_[p]))
    (hF : ∀ (c : XB (d.Utower M p s (hN s))) (b : ℤ_[p]),
      F (Finsupp.single c b) =
        scalarIso ℤ_[p] (XB (d.Utower M p s (hN s)))
          (b ⊗ₜ thetaZX d M p q s (hN s) hp hM hpM hD Pq hPq h (Finsupp.single c 1)))
    (t : ℤ_[p] ⊗[ℤ] G.X s) :
    ((xlambdaPsi d M p q hN G φ s ((G.act s h).baseChange ℤ_[p] t) :
        degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
      F ((xlambdaPsi d M p q hN G φ s t : degZero (d.Utower M p s (hN s)) ℤ_[p]) :
        ZX (d.Utower M p s (hN s)) ℤ_[p]) := by
  have : Module.Flat ℤ ℤ_[p] := flat_padicInt p
  have hcomm : xlambdaCong d M p q hN G φ s ((G.act s h).baseChange ℤ_[p] t) =
      (theta d M p q s (hN s) hp hM hpM hD Pq hPq h).baseChange ℤ_[p] (xlambdaCong d M p q hN G φ s t) := by
    induction t with
    | tmul b x => simp [xlambdaCong, hφ]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [xlambdaPsi, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hcomm]
  exact degZeroBaseChange_comm (thetaZX d M p q s (hN s) hp hM hpM hD Pq hPq h) F hF
    (theta d M p q s (hN s) hp hM hpM hD Pq hPq h) (fun k => rfl) (xlambdaCong d M p q hN G φ s t)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): for `s ≥ 1`, `Ψ_s = xlambdaPsi φ s` carries `U_p ⊗ 1` to `U_p = UpHom`
(if `φ` satisfies (X1)). -/
theorem xlambdaPsi_Up (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (hφ : ∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x))
    (s : ℕ) (hs : 1 ≤ s) (t : ℤ_[p] ⊗[ℤ] G.X s) :
    ((xlambdaPsi d M p q hN G φ s ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p] t) :
        degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
      UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]
        ((xlambdaPsi d M p q hN G φ s t : degZero (d.Utower M p s (hN s)) ℤ_[p]) :
          ZX (d.Utower M p s (hN s)) ℤ_[p]) := by
  have : Module.Flat ℤ ℤ_[p] := flat_padicInt p
  have hcomm : xlambdaCong d M p q hN G φ s ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p] t) =
      (theta d M p q s (hN s) hp hM hpM hD Pq hPq (HeckeSym.Up hs)).baseChange ℤ_[p]
        (xlambdaCong d M p q hN G φ s t) := by
    induction t with
    | tmul b x => simp [xlambdaCong, hφ]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [xlambdaPsi, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hcomm]
  exact degZeroBaseChange_comm (UpHom d M p s (hN s) hp hM hpM hs ℤ)
    (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]) (UpHom_isBaseChange d M p hN hp hM hpM s hs)
    (theta d M p q s (hN s) hp hM hpM hD Pq hPq (HeckeSym.Up hs)) (fun k => rfl)
    (xlambdaCong d M p q hN G φ s t)

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `xlambdaPsi_Up` as an identity of linear maps,
`Ψ_s ∘ (U_p ⊗ 1) = U_p|_{ℤ_[p][S_s]⁰} ∘ Ψ_s` (`UpKer`). -/
theorem xlambdaPsi_comp_Up (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (hφ : ∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x))
    (s : ℕ) (hs : 1 ≤ s) :
    (xlambdaPsi d M p q hN G φ s : ℤ_[p] ⊗[ℤ] G.X s →ₗ[ℤ_[p]] degZero (d.Utower M p s (hN s)) ℤ_[p]) ∘ₗ
        ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p]) =
      (Ordinary.UpKer (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]) (p : ℤ_[p])
        (Ordinary.deg_comp_UpHom ℤ_[p] hM hpM hs)) ∘ₗ
        (xlambdaPsi d M p q hN G φ s :
          ℤ_[p] ⊗[ℤ] G.X s →ₗ[ℤ_[p]] degZero (d.Utower M p s (hN s)) ℤ_[p]) := by
  refine LinearMap.ext fun t => Subtype.ext ?_
  exact xlambdaPsi_Up d M p q hN hp hM hpM hD Pq hPq G φ hφ s hs t

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), finite level, **the isomorphism induced by `φ_s`**: for `s ≥ 1` and `φ`
with (X1), `e (ℤ_[p] ⊗ X_q(J_s)) ≃ e ℤ_[p][S_s]`, `e` the ordinary part of `U_p ⊗ 1` resp. `U_p = UpHom`:
the restriction of `Ψ_s = xlambdaPsi φ s` (`ordPartEquiv`, `xlambdaPsi_comp_Up`) followed by
`e ℤ_[p][S_s]⁰ = e ℤ_[p][S_s]` (`lem:s04-ekills`(a), `Ordinary.ekillsA_tower_uncond`; no `Hyp.PadicOrdDecomp`).
Compatibility with `Ψ_s`: `xlambdaOrd_apply`. -/
def xlambdaOrd (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (hφ : ∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x))
    (s : ℕ) (hs : 1 ≤ s) :
    Ordinary.ordPart ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p]) ≃ₗ[ℤ_[p]]
      Ordinary.ordPart (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]) :=
  (ordPartEquiv (xlambdaPsi d M p q hN G φ s)
      (xlambdaPsi_comp_Up d M p q hN hp hM hpM hD Pq hPq G φ hφ s hs)).trans
    ((Submodule.equivMapOfInjective
      (LinearMap.ker (Ordinary.deg (XB (d.Utower M p s (hN s))) ℤ_[p])).subtype
      (LinearMap.ker (Ordinary.deg (XB (d.Utower M p s (hN s))) ℤ_[p])).injective_subtype
      (Ordinary.ordPart (R := ℤ_[p])
        (M := ↥(LinearMap.ker (Ordinary.deg (XB (d.Utower M p s (hN s))) ℤ_[p])))
        (Ordinary.UpKer (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]) (p : ℤ_[p])
          (Ordinary.deg_comp_UpHom ℤ_[p] hM hpM hs)))).trans
      (LinearEquiv.ofEq _ _
        (Ordinary.ekillsA_tower_uncond (d := d) (p := p) (s := s) (hN := hN s) (hp := hp) hM hpM hs)))

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`): `xlambdaOrd` is induced by `Ψ_s`: on underlying elements of
`ℤ_[p][S_s]`, `xlambdaOrd x = Ψ_s x`. -/
theorem xlambdaOrd_apply (φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ)
    (hφ : ∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x))
    (s : ℕ) (hs : 1 ≤ s) (x : Ordinary.ordPart ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p])) :
    ((xlambdaOrd d M p q hN hp hM hpM hD Pq hPq G φ hφ s hs x :
        Ordinary.ordPart (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p])) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
      ((xlambdaPsi d M p q hN G φ s (x : ℤ_[p] ⊗[ℤ] G.X s) : degZero (d.Utower M p s (hN s)) ℤ_[p]) :
        ZX (d.Utower M p s (hN s)) ℤ_[p]) := by
  first
  | rfl
  | simp [xlambdaOrd, ordPartEquiv]

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), finite level: under `Hyp.X.char G`, for `s ≥ 1` there is a
`ℤ_[p]`-linear isomorphism `Ψ : ℤ_[p] ⊗ X_q(J_s) ≃ ℤ_[p][S_s]⁰` carrying `U_p ⊗ 1` to `U_p = UpHom`
(corollary of `xlambdaPsi_Up`: `Ψ = xlambdaPsi φ s` for the `φ` of `Hyp.X.char`).
Status: *formalized* (under the hypothesis `Hyp.X.char`, hence for every `G` with the properties
(X1)–(X3); `G = character group` stays outside Lean). -/
theorem xlambda_finite_iso
    (hX : Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) (s : ℕ) (hs : 1 ≤ s) :
    ∃ Ψ : ℤ_[p] ⊗[ℤ] G.X s ≃ₗ[ℤ_[p]] degZero (d.Utower M p s (hN s)) ℤ_[p],
      ∀ t : ℤ_[p] ⊗[ℤ] G.X s,
        ((Ψ ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p] t) :
            degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
          UpHom d M p s (hN s) hp hM hpM hs ℤ_[p]
            ((Ψ t : degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) := by
  obtain ⟨φ, hφ, -, -⟩ := hX
  exact ⟨xlambdaPsi d M p q hN G φ s, xlambdaPsi_Up d M p q hN hp hM hpM hD Pq hPq G φ hφ s hs⟩

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), finite level, **the deliverable** in existence form (unconditional in
`Hyp.PadicOrdDecomp`, via `Ordinary.ekillsA_tower_uncond`): under `Hyp.X.char G`, for `s ≥ 1`,
`e (ℤ_[p] ⊗ X_q(J_s)) ≃ e ℤ_[p][S_s]` as `ℤ_[p]`-modules, where `e` is the ordinary part of `U_p ⊗ 1`
on the left and of `U_p = UpHom` on the right. Corollary of the definition `xlambdaOrd` (the equivalence induced
by `φ_s`, `xlambdaOrd_apply`), which is the strong form. Status: *formalized* under `Hyp.X.char`. -/
theorem xlambda_finite
    (hX : Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) (s : ℕ) (hs : 1 ≤ s) :
    Nonempty (Ordinary.ordPart ((G.act s (HeckeSym.Up hs)).baseChange ℤ_[p]) ≃ₗ[ℤ_[p]]
      Ordinary.ordPart (UpHom d M p s (hN s) hp hM hpM hs ℤ_[p])) := by
  obtain ⟨φ, hφ, -, -⟩ := hX
  exact ⟨xlambdaOrd d M p q hN hp hM hpM hD Pq hPq G φ hφ s hs⟩

/-- `prop:s05-Xlambda`(a) (`s05-Xlambda`), Hecke-equivariance of **one** `Ψ`: under `Hyp.X.char G` there is a family
`φ` satisfying (X1) such that, for every `s`, every `h ∈ ℋ_s` and every operator `F` on `ℤ_[p][S_s]` which is
`θ(h) ⊗ ℤ_[p]` on basis vectors (`hF`; for `U_p` this is `UpHom_isBaseChange`), the isomorphism
`Ψ_s = xlambdaPsi φ s` (the `Ψ` of `xlambda_finite_iso`, and the one inducing `xlambdaOrd`) satisfies
`Ψ_s ∘ (act h ⊗ 1) = F ∘ Ψ_s`. The identification of `F` with the natural `ℤ_[p]`-operator is formalized only
for `U_p`, not for `T_ℓ`, `⟨u⟩`, `U_q`, `T_p` (`hF` is always satisfiable by the conjugated base change). -/
theorem xlambda_equivariant
    (hX : Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G) :
    ∃ φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ,
      (∀ s (h : HeckeSym M p q s) (x : G.X s),
        φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x)) ∧
      ∀ (s : ℕ) (h : HeckeSym M p q s) (F : Module.End ℤ_[p] (ZX (d.Utower M p s (hN s)) ℤ_[p])),
        (∀ (c : XB (d.Utower M p s (hN s))) (b : ℤ_[p]),
          F (Finsupp.single c b) =
            scalarIso ℤ_[p] (XB (d.Utower M p s (hN s)))
              (b ⊗ₜ thetaZX d M p q s (hN s) hp hM hpM hD Pq hPq h (Finsupp.single c 1))) →
        ∀ t : ℤ_[p] ⊗[ℤ] G.X s,
          ((xlambdaPsi d M p q hN G φ s ((G.act s h).baseChange ℤ_[p] t) :
              degZero (d.Utower M p s (hN s)) ℤ_[p]) : ZX (d.Utower M p s (hN s)) ℤ_[p]) =
            F ((xlambdaPsi d M p q hN G φ s t : degZero (d.Utower M p s (hN s)) ℤ_[p]) :
              ZX (d.Utower M p s (hN s)) ℤ_[p]) := by
  obtain ⟨φ, hφ, -, -⟩ := hX
  exact ⟨φ, hφ, fun s h F hF t =>
    xlambdaPsi_equivariant d M p q hN hp hM hpM hD Pq hPq G φ hφ s h F hF t⟩

end Main

end

end Langlandscape.Comparison
