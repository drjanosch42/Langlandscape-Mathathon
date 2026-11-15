/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Consistency
import Langlandscape.Brandt.UpAdjoint

/-!
# `⟨,⟩_w`-adjoints of `θ`, invertibility of `θ(U_q)` and commutation with `θ(U_q)` (S05-L4g)

Tex: `lem:s05-consistency`(b) (`mathematics/chapters/s05/sign.tex`, `plan/staged/stage-05-comparison-hypothesis.tex`),
`def:s05-theta`, `hyp:s05-X` (X4).  Status: *formalized*, unconditional.

These are the three facts about the Hecke dictionary `θ = theta …` (`Comparison/Dictionary.lean`) that any instance of
`Hyp.X.gal` (`Hyp/HypXGal.lean`) needs, in particular the toy direct-sum instance of S05-L4:

* **adjoints on `degZero`** (`lem:s05-consistency`(b)): `thetaAdj … h : End_ℤ(ℤ[X_B(U_s)]⁰)` with
  `thetaAdj_spec : ⟨θ(h)^* x, y⟩_w = ⟨x, θ(h) y⟩_w` for every `h : HeckeSym M p q s`; on `ℤ[X_B(U_s)]` it is
  `thetaAdjZX`: `T ℓ ↦ T_{ϖ_ℓ⁻¹}` (`= S_ℓ^{-1} T_ℓ`, `Tl_adjoint`), `Up ↦ U_p^* = UpStar`, `Tp ↦ T_{ϖ_p⁻¹}`,
  `dia u ↦` the **reversed** ordered product of the local adjoints `T_{δ_{t_ℓ}⁻¹}` of `diaZX u⁻¹`
  (`bilin_list_prod_adjoint`: the adjoint of a list product is the reversed product of the adjoints),
  `Uq ↦ Π_q^{-1} = PiEllHom Pq⁻¹`.  Each adjoint preserves `degZero` (via `heckeTHom_mem_degZero`,
  `deg_comp_translateHom`, `list_prod_apply_mem`).
* **`θ(U_q)` is invertible on `degZero`**: `thetaUqEquiv`, with inverse `θ(U_q)^* = PiEllHom Pq⁻¹`
  (right translation by `Pq⁻¹`; `PiEllHom_comp_inv`, `PiEllHom_inv_comp`).
* **commutation**: `theta_comm_Uq : θ(U_q) ∘ θ(h) = θ(h) ∘ θ(U_q)` for all `h`: every other `θ(h)` is a (product of)
  `heckeTHom U t` with `t` supported at a prime `≠ q`, and these commute with the right translation `Π_q`
  (`heckeTHom_comp_PiEllHom`, the transpose of stage 01's `heckeT_comm_PiEll`).
-/

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

set_option autoImplicit false

namespace Langlandscape.Comparison

noncomputable section

/-! ### Generic lemmas: list products of endomorphisms -/

section ListProd

/-- `lem:s05-consistency`(b) (`s05-consistency`), generic: a list product of endomorphisms each preserving a submodule
`P` preserves `P`. -/
theorem list_prod_apply_mem {R N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] (P : Submodule R N)
    (L : List (Module.End R N)) (hL : ∀ f ∈ L, ∀ x ∈ P, f x ∈ P) : ∀ x ∈ P, L.prod x ∈ P := by
  induction L with
  | nil =>
    intro x hx
    rwa [List.prod_nil, Module.End.one_apply]
  | cons f L ih =>
    intro x hx
    rw [List.prod_cons, Module.End.mul_apply]
    exact hL f (by simp) _ (ih (fun g hg => hL g (by simp [hg])) x hx)

/-- `lem:s05-consistency`(b) (`s05-consistency`), generic: for a bilinear form `B`, if `G i` is a left `B`-adjoint of
`F i` for every `i ∈ L` (`B (G i x) y = B x (F i y)`), then the **reversed** product of the `G i` is a left
adjoint of the product of the `F i`. -/
theorem bilin_list_prod_adjoint {R N ι : Type*} [CommSemiring R] [AddCommMonoid N] [Module R N]
    (B : N →ₗ[R] N →ₗ[R] R) (L : List ι) (F G : ι → Module.End R N)
    (hFG : ∀ i ∈ L, ∀ x y, B (G i x) y = B x (F i y)) :
    ∀ x y, B ((L.reverse.map G).prod x) y = B x ((L.map F).prod y) := by
  induction L with
  | nil =>
    intro x y
    simp only [List.reverse_nil, List.map_nil, List.prod_nil, Module.End.one_apply]
  | cons i L ih =>
    intro x y
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply]
    rw [ih (fun j hj => hFG j (by simp [hj])) (G i x) y, hFG i (by simp) x]

end ListProd

/-! ### Generic lemmas on `ℤ[X_B(U)]`: adjoints, inverses and commutation of right translations -/

section BrandtGeneric

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ)

/-- `lem:s05-consistency`(b) (`s05-consistency`), from stage 01 `brandtPairing_heckeTHom`: `T_{g⁻¹}` is a left
Brandt adjoint of `T_g`, `⟨T_{g⁻¹} x, y⟩ = ⟨x, T_g y⟩`. -/
theorem brandtPairing_heckeTHom_inv [Finite (XB U)] (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U ⊓ conjSub U g⁻¹).relIndex U ≠ 0) (x y : ZX U R) :
    brandtPairing U R (heckeTHom U g⁻¹ R hfin' x) y = brandtPairing U R x (heckeTHom U g R hfin y) := by
  have hfin'' : (U ⊓ conjSub U g⁻¹⁻¹).relIndex U ≠ 0 := by
    rw [inv_inv]
    exact hfin
  rw [brandtPairing_heckeTHom U g⁻¹ R hfin' hfin'' x y, heckeTHom_congr U R (inv_inv g) hfin'' hfin]

/-- `lem:s05-consistency`(b) (`s05-consistency`), helper: for `g` normalizing `U`, `[x] ↦ [x g]` is inverse to
`[x] ↦ [x g⁻¹]` on `R[X_B(U)]`. -/
theorem translateHom_comp_inv (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) (hg' : ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    translateHom U R g ∘ₗ translateHom U R g⁻¹ = LinearMap.id := by
  have hg'' : ∀ u ∈ U, g⁻¹⁻¹ * u * g⁻¹ ∈ U := fun u hu => by
    rw [inv_inv]
    exact hg' u hu
  apply Finsupp.lhom_ext
  intro c r
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, translateHom_single U R g⁻¹, translateHom_single U R g, translateMap_mk hg'',
    translateMap_mk hg, inv_mul_cancel_right, LinearMap.id_apply]

end BrandtGeneric

section PiEllGeneric

variable (R : Type*) [CommRing R] (d : DefiniteData) {ℓ : ℕ} [Fact ℓ.Prime]

/-- `lem:s05-consistency`(b) (`s05-consistency`): `Π_ℓ ∘ Π_ℓ^{-1} = id` on `R[X_B(U)]`, `U` maximal at `ℓ ∣ D`,
with `Π_ℓ^{-1} = PiEllHom P⁻¹` the right translation by `P⁻¹`. -/
theorem PiEllHom_comp_inv (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    PiEllHom R d ℓ hℓ P U ∘ₗ PiEllHom R d ℓ hℓ P⁻¹ U = LinearMap.id := by
  unfold PiEllHom
  rw [map_inv]
  exact translateHom_comp_inv U (localEmbed d.a d.b ℓ P) R (hU.inv_conj_mem P) (fun u hu => hU.conj_mem P hu)

/-- `lem:s05-consistency`(b) (`s05-consistency`): `Π_ℓ^{-1} ∘ Π_ℓ = id` on `R[X_B(U)]`, `U` maximal at `ℓ ∣ D`. -/
theorem PiEllHom_inv_comp (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hU : IsMaximalAt d ℓ U)
    (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    PiEllHom R d ℓ hℓ P⁻¹ U ∘ₗ PiEllHom R d ℓ hℓ P U = LinearMap.id := by
  have h := PiEllHom_comp_inv R d hℓ hU P⁻¹
  rwa [inv_inv] at h

/-- `lem:s05-consistency`(b) (`s05-consistency`), from stage 01 `PiEll_adjoint`: `Π_ℓ^{-1}` is a left Brandt adjoint
of `Π_ℓ`, `⟨Π_ℓ^{-1} x, y⟩ = ⟨x, Π_ℓ y⟩`, `U` maximal at `ℓ ∣ D`. -/
theorem brandtPairing_PiEllHom_inv (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hU : IsMaximalAt d ℓ U) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (x y : ZX U R) :
    brandtPairing U R (PiEllHom R d ℓ hℓ P⁻¹ U x) y = brandtPairing U R x (PiEllHom R d ℓ hℓ P U y) := by
  have h := PiEll_adjoint (d := d) (ℓ := ℓ) (R := R) hℓ hU P⁻¹ x y
  rwa [inv_inv] at h

/-- `lem:s05-consistency`(b) (`s05-consistency`), from stage 01 `heckeT_comm_PiEll` by transposition: on `R[X_B(U)]`,
`U` maximal at `ℓ ∣ D`, `Π_ℓ` commutes with every `T_t^t = heckeTHom U t` whose element has `t_ℓ = 1`. -/
theorem heckeTHom_comp_PiEllHom (hℓ : ℓ ∣ d.D) {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} [Finite (XB U)]
    (hU : IsMaximalAt d ℓ U) (P : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (t : (GL2TF.Quat.BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b ℓ t = 1) (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) :
    heckeTHom U t R hfin ∘ₗ PiEllHom R d ℓ hℓ P U = PiEllHom R d ℓ hℓ P U ∘ₗ heckeTHom U t R hfin := by
  refine LinearMap.ext fun x => zx_ext_of_evalPairing U R fun f => ?_
  have hc : heckeT U t R hfin (PiEll R d U ℓ hℓ P f) = PiEll R d U ℓ hℓ P (heckeT U t R hfin f) :=
    LinearMap.congr_fun (heckeT_comm_PiEll R hℓ hU P t ht hfin) f
  simp only [LinearMap.comp_apply, heckeTHom_transpose, PiEllHom_transpose]
  rw [hc]

end PiEllGeneric

/-! ### The adjoint of the product diamond -/

section DiaAdj

variable (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D)

/-- `lem:s05-consistency`(b) (`s05-consistency`), helper: the finiteness for `δ_t⁻¹` at `U_s`, `ℓ ∣ M p^s`. -/
theorem relIndex_diamondElt_inv_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∈ (M * p ^ s).primeFactors)
    (t : ℤ_[ℓ]ˣ) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN)
      (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) t)⁻¹).relIndex (d.Utower M p s hN) ≠ 0 := by
  refine relIndex_ne_zero_of_normalizing _ _ fun x hx => ?_
  have h := diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN)
    (hℓ := d.not_dvd_D_of_mem_primeFactors hN hℓ) hℓ t⁻¹ x hx
  rw [diamondElt_inv d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) t] at h
  exact h

/-- `lem:s05-consistency`(b) (`s05-consistency`): the Brandt adjoint `T_{δ_t⁻¹}` of the local factor
`⟨t_ℓ⟩ = diaLocal ℓ u` (`t = t_ℓ = localUnit ℓ u`) of the product diamond, on `ℤ[X_B(U_s)]`. -/
def diaAdjLocal (ℓ : ℕ) (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (u : (ZMod (M * p ^ s))ˣ) :
    Module.End ℤ (ZX (d.Utower M p s hN) ℤ) :=
  haveI : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  heckeTHom (d.Utower M p s hN)
    (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u))⁻¹ ℤ
    (relIndex_diamondElt_inv_ne_zero d M p s hN ℓ hℓ _)

/-- `lem:s05-consistency`(b) (`s05-consistency`): `⟨⟨t_ℓ⟩^* x, y⟩_w = ⟨x, ⟨t_ℓ⟩ y⟩_w` for each local factor. -/
theorem brandtPairing_diaAdjLocal (ℓ : ℕ) (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (u : (ZMod (M * p ^ s))ˣ)
    (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ (diaAdjLocal d M p s hN ℓ hℓ u x) y =
      brandtPairing (d.Utower M p s hN) ℤ x (diaLocal d M p s hN ℤ ℓ hℓ u y) := by
  have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  exact brandtPairing_heckeTHom_inv (d.Utower M p s hN)
    (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)) ℤ
    (relIndex_ne_zero_of_normalizing _ _ (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ _))
    (relIndex_diamondElt_inv_ne_zero d M p s hN ℓ hℓ _) x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): the Brandt adjoint of the product diamond `diaZX u`: the
**reversed** ordered product of the local adjoints `diaAdjLocal`. -/
def diaAdjZX (u : (ZMod (M * p ^ s))ˣ) : Module.End ℤ (ZX (d.Utower M p s hN) ℤ) :=
  ((M * p ^ s).primeFactors.toList.attach.reverse.map
    (fun ℓ => diaAdjLocal d M p s hN ℓ.1 (Finset.mem_toList.1 ℓ.2) u)).prod

/-- `lem:s05-consistency`(b) (`s05-consistency`): `⟨⟨u⟩^* x, y⟩_w = ⟨x, ⟨u⟩ y⟩_w` for the product diamond `diaZX u`
(adjoint of a list product = reversed product of the adjoints, `bilin_list_prod_adjoint`). -/
theorem brandtPairing_diaAdjZX (u : (ZMod (M * p ^ s))ˣ) (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ (diaAdjZX d M p s hN u x) y =
      brandtPairing (d.Utower M p s hN) ℤ x (diaZX d M p s hN ℤ u y) :=
  bilin_list_prod_adjoint (brandtPairing (d.Utower M p s hN) ℤ) (M * p ^ s).primeFactors.toList.attach
    (fun ℓ => diaLocal d M p s hN ℤ ℓ.1 (Finset.mem_toList.1 ℓ.2) u)
    (fun ℓ => diaAdjLocal d M p s hN ℓ.1 (Finset.mem_toList.1 ℓ.2) u)
    (fun ℓ _ x y => brandtPairing_diaAdjLocal d M p s hN ℓ.1 (Finset.mem_toList.1 ℓ.2) u x y) x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): `diaAdjZX u` is the reversed ordered product of the local
adjoints (equation lemma). -/
theorem diaAdjZX_def (u : (ZMod (M * p ^ s))ˣ) :
    diaAdjZX d M p s hN u = ((M * p ^ s).primeFactors.toList.attach.reverse.map
      (fun ℓ => diaAdjLocal d M p s hN ℓ.1 (Finset.mem_toList.1 ℓ.2) u)).prod :=
  rfl

/-- `lem:s05-consistency`(b) (`s05-consistency`): each local adjoint `T_{δ_t⁻¹}` preserves `degZero`. -/
theorem diaAdjLocal_mem_degZero (ℓ : ℕ) (hℓ : ℓ ∈ (M * p ^ s).primeFactors) (u : (ZMod (M * p ^ s))ˣ)
    {x : ZX (d.Utower M p s hN) ℤ} (hx : x ∈ degZero (d.Utower M p s hN) ℤ) :
    diaAdjLocal d M p s hN ℓ hℓ u x ∈ degZero (d.Utower M p s hN) ℤ := by
  have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  exact heckeTHom_mem_degZero (d.Utower M p s hN)
    (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u))⁻¹ ℤ
    (relIndex_diamondElt_inv_ne_zero d M p s hN ℓ hℓ _) hx

/-- `lem:s05-consistency`(b) (`s05-consistency`): the adjoint of the product diamond preserves `degZero`. -/
theorem diaAdjZX_mem_degZero (u : (ZMod (M * p ^ s))ˣ) {x : ZX (d.Utower M p s hN) ℤ}
    (hx : x ∈ degZero (d.Utower M p s hN) ℤ) : diaAdjZX d M p s hN u x ∈ degZero (d.Utower M p s hN) ℤ := by
  rw [diaAdjZX_def]
  refine list_prod_apply_mem _ _ ?_ x hx
  intro f hf z hz
  obtain ⟨ℓ, -, hℓf⟩ := List.mem_map.1 hf
  rw [← hℓf]
  exact diaAdjLocal_mem_degZero d M p s hN ℓ.1 (Finset.mem_toList.1 ℓ.2) u hz

end DiaAdj

/-! ### The adjoints `θ(h)^*`, `θ(U_q)⁻¹` and the commutation with `θ(U_q)` -/

section Theta

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `lem:s05-consistency`(b) (`s05-consistency`): the Brandt adjoint `θ(h)^*` on `ℤ[X_B(U_s)]` (before restriction to
degree zero): `T ℓ ↦ T_{ϖ_ℓ⁻¹}` (`= S_ℓ^{-1} T_ℓ`, `Tl_adjoint`), `Up ↦ U_p^* = UpStar`, `Tp ↦ T_{ϖ_p⁻¹}` (`s = 0`),
`dia u ↦ diaAdjZX u⁻¹` (reversed product of the local adjoints of `diaZX u⁻¹`), `Uq ↦ Π_q^{-1} = PiEllHom Pq⁻¹`. -/
def thetaAdjZX : HeckeSym M p q s → Module.End ℤ (ZX (d.Utower M p s hN) ℤ)
  | .T ℓ hℓ hℓN =>
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    heckeTHom (d.Utower M p s hN) (elemT d ℓ (not_dvd_D_of_T d M p q hD hℓN))⁻¹ ℤ
      (relIndex_elemT_inv_ne_zero_Utower d ℓ _ (not_dvd_M_of_T M p q hℓN) (ne_p_of_T M p q hℓN))
  | .Up hs => UpStar d M p s hN hp hM hpM hs ℤ
  | .Tp hs => heckeTHom (d.Utower M p s hN) (elemT d p hp)⁻¹ ℤ
      (relIndex_elemT_inv_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) (not_dvd_of_s_eq_zero M p s hpM hs))
  | .dia u => diaAdjZX d M p s hN u⁻¹
  | .Uq => PiEllHom ℤ d q hPq.dvd Pq⁻¹ (d.Utower M p s hN)

/-- `lem:s05-consistency`(b) (`s05-consistency`): `⟨θ(h)^* x, y⟩_w = ⟨x, θ(h) y⟩_w` on `ℤ[X_B(U_s)]`. -/
theorem thetaAdjZX_adjoint (h : HeckeSym M p q s) (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ (thetaAdjZX d M p q s hN hp hM hpM hD Pq hPq h x) y =
      brandtPairing (d.Utower M p s hN) ℤ x (thetaZX d M p q s hN hp hM hpM hD Pq hPq h y) := by
  cases h with
  | T ℓ hℓ hℓN =>
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact brandtPairing_heckeTHom_inv (d.Utower M p s hN) (elemT d ℓ (not_dvd_D_of_T d M p q hD hℓN)) ℤ
      (relIndex_elemT_ne_zero_Utower d ℓ _ (not_dvd_M_of_T M p q hℓN) (ne_p_of_T M p q hℓN))
      (relIndex_elemT_inv_ne_zero_Utower d ℓ _ (not_dvd_M_of_T M p q hℓN) (ne_p_of_T M p q hℓN)) x y
  | Up hs =>
    exact brandtPairing_heckeTHom_inv (d.Utower M p s hN)
      (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p)) ℤ
      (Up_relIndex_ne_zero hM hpM hs) (UpStar_relIndex_ne_zero hM hpM hs) x y
  | Tp hs =>
    exact brandtPairing_heckeTHom_inv (d.Utower M p s hN) (elemT d p hp) ℤ
      (relIndex_elemT_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) (not_dvd_of_s_eq_zero M p s hpM hs))
      (relIndex_elemT_inv_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) (not_dvd_of_s_eq_zero M p s hpM hs)) x y
  | dia u => exact brandtPairing_diaAdjZX d M p s hN u⁻¹ x y
  | Uq =>
    exact brandtPairing_PiEllHom_inv ℤ d hPq.dvd
      (isMaximalAt_Utower (M := M) (p := p) (s := s) (hN := hN) hPq.dvd) Pq x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(h)^*` preserves `degZero`. -/
theorem thetaAdjZX_mem_degZero (h : HeckeSym M p q s) {x : ZX (d.Utower M p s hN) ℤ}
    (hx : x ∈ degZero (d.Utower M p s hN) ℤ) :
    thetaAdjZX d M p q s hN hp hM hpM hD Pq hPq h x ∈ degZero (d.Utower M p s hN) ℤ := by
  cases h with
  | T _ _ _ => exact heckeTHom_mem_degZero (d.Utower M p s hN) _ ℤ _ hx
  | Up _ => exact heckeTHom_mem_degZero (d.Utower M p s hN) _ ℤ _ hx
  | Tp _ => exact heckeTHom_mem_degZero (d.Utower M p s hN) _ ℤ _ hx
  | dia u => exact diaAdjZX_mem_degZero d M p s hN u⁻¹ hx
  | Uq => exact degZero_stable _ _ (deg_comp_translateHom _ _ _) hx

/-- `lem:s05-consistency`(b) (`s05-consistency`): the `⟨,⟩_w`-adjoint `θ(h)^*` on `ℤ[X_B(U_s)]⁰ = degZero`, the
restriction of `thetaAdjZX h` (input of the toy `Hyp.X.gal` instance, S05-L4). -/
def thetaAdj (h : HeckeSym M p q s) : Module.End ℤ (degZero (d.Utower M p s hN) ℤ) :=
  (thetaAdjZX d M p q s hN hp hM hpM hD Pq hPq h).restrict
    (fun _ hx => thetaAdjZX_mem_degZero d M p q s hN hp hM hpM hD Pq hPq h hx)

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(h)^*` acts on `degZero` as `thetaAdjZX h`. -/
@[simp] theorem thetaAdj_apply (h : HeckeSym M p q s) (x : degZero (d.Utower M p s hN) ℤ) :
    ((thetaAdj d M p q s hN hp hM hpM hD Pq hPq h x : degZero (d.Utower M p s hN) ℤ) : ZX (d.Utower M p s hN) ℤ) =
      thetaAdjZX d M p q s hN hp hM hpM hD Pq hPq h x :=
  rfl

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(h)^*` is the `⟨,⟩_w`-adjoint of `θ(h)` on `degZero`,
`⟨θ(h)^* x, y⟩_w = ⟨x, θ(h) y⟩_w`, for every Hecke symbol `h`. -/
theorem thetaAdj_spec (h : HeckeSym M p q s) (x y : degZero (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ
        (thetaAdj d M p q s hN hp hM hpM hD Pq hPq h x : ZX (d.Utower M p s hN) ℤ) (y : ZX (d.Utower M p s hN) ℤ) =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ)
        (theta d M p q s hN hp hM hpM hD Pq hPq h y : ZX (d.Utower M p s hN) ℤ) :=
  thetaAdjZX_adjoint d M p q s hN hp hM hpM hD Pq hPq h x y

/-- `def:s05-theta` (`s05-theta`): `θ(U_q) ∘ θ(U_q)^* = id` on `degZero` (`Π_q Π_q^{-1} = 1`). -/
theorem theta_Uq_comp_thetaAdj_Uq :
    theta d M p q s hN hp hM hpM hD Pq hPq .Uq ∘ₗ thetaAdj d M p q s hN hp hM hpM hD Pq hPq .Uq = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact LinearMap.congr_fun (PiEllHom_comp_inv ℤ d hPq.dvd (U := d.Utower M p s hN)
    (isMaximalAt_Utower (M := M) (p := p) (s := s) (hN := hN) hPq.dvd) Pq) (x : ZX (d.Utower M p s hN) ℤ)

/-- `def:s05-theta` (`s05-theta`): `θ(U_q)^* ∘ θ(U_q) = id` on `degZero` (`Π_q^{-1} Π_q = 1`). -/
theorem thetaAdj_Uq_comp_theta_Uq :
    thetaAdj d M p q s hN hp hM hpM hD Pq hPq .Uq ∘ₗ theta d M p q s hN hp hM hpM hD Pq hPq .Uq = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact LinearMap.congr_fun (PiEllHom_inv_comp ℤ d hPq.dvd (U := d.Utower M p s hN)
    (isMaximalAt_Utower (M := M) (p := p) (s := s) (hN := hN) hPq.dvd) Pq) (x : ZX (d.Utower M p s hN) ℤ)

/-- `def:s05-theta` (`s05-theta`): `θ(U_q) = +Π_q` is invertible on `ℤ[X_B(U_s)]⁰ = degZero`, with inverse its
`⟨,⟩_w`-adjoint `Π_q^{-1}` (right translation by `Pq⁻¹`); input of the toy `Hyp.X.gal` instance (S05-L4). -/
def thetaUqEquiv : degZero (d.Utower M p s hN) ℤ ≃ₗ[ℤ] degZero (d.Utower M p s hN) ℤ :=
  LinearEquiv.ofLinearMap (theta d M p q s hN hp hM hpM hD Pq hPq .Uq) (thetaAdj d M p q s hN hp hM hpM hD Pq hPq .Uq)
    (theta_Uq_comp_thetaAdj_Uq d M p q s hN hp hM hpM hD Pq hPq)
    (thetaAdj_Uq_comp_theta_Uq d M p q s hN hp hM hpM hD Pq hPq)

/-- `def:s05-theta` (`s05-theta`): `thetaUqEquiv` is `θ(U_q)`. -/
@[simp] theorem thetaUqEquiv_toLinearMap :
    (thetaUqEquiv d M p q s hN hp hM hpM hD Pq hPq).toLinearMap = theta d M p q s hN hp hM hpM hD Pq hPq .Uq :=
  rfl

/-- `def:s05-theta` (`s05-theta`): the inverse of `thetaUqEquiv` is `θ(U_q)^* = Π_q^{-1}`. -/
@[simp] theorem thetaUqEquiv_symm_toLinearMap :
    (thetaUqEquiv d M p q s hN hp hM hpM hD Pq hPq).symm.toLinearMap =
      thetaAdj d M p q s hN hp hM hpM hD Pq hPq .Uq :=
  rfl

omit [Fact (Nat.Prime p)] in
include hD in
/-- `def:s05-theta` (`s05-theta`): `Π_q` commutes with the product diamond `⟨u⟩ = diaZX u` (each local factor sits at
a prime `ℓ ∣ M p^s`, `ℓ ≠ q`). -/
theorem PiEllHom_commute_diaZX (u : (ZMod (M * p ^ s))ˣ) :
    Commute (PiEllHom ℤ d q hPq.dvd Pq (d.Utower M p s hN)) (diaZX d M p s hN ℤ u) := by
  unfold diaZX
  refine Commute.list_prod_right _ _ fun f hf => ?_
  obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hf
  have hℓ : ℓ.1 ∈ (M * p ^ s).primeFactors := Finset.mem_toList.1 ℓ.2
  have : Fact ℓ.1.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  have hqℓ : q ≠ ℓ.1 := fun e =>
    d.not_dvd_D_of_mem_primeFactors hN hℓ (by rw [hD]; exact dvd_of_eq e.symm)
  have h := heckeTHom_comp_PiEllHom ℤ d hPq.dvd
    (isMaximalAt_Utower (M := M) (p := p) (s := s) (hN := hN) hPq.dvd) Pq
    (diamondElt d ℓ.1 (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ.1 (Nat.dvd_of_mem_primeFactors hℓ) u))
    (localProjUnits_localEmbedGL_of_ne (p := ℓ.1) (hp := d.not_dvd_D_of_mem_primeFactors hN hℓ) _ hqℓ)
    (relIndex_ne_zero_of_normalizing _ _ (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ _))
  unfold Commute SemiconjBy
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  exact h.symm

/-- `def:s05-theta` (`s05-theta`): `θ(U_q) ∘ θ(h) = θ(h) ∘ θ(U_q)` on `ℤ[X_B(U_s)]`, for every Hecke symbol `h`. -/
theorem thetaZX_comm_Uq (h : HeckeSym M p q s) :
    thetaZX d M p q s hN hp hM hpM hD Pq hPq .Uq ∘ₗ thetaZX d M p q s hN hp hM hpM hD Pq hPq h =
      thetaZX d M p q s hN hp hM hpM hD Pq hPq h ∘ₗ thetaZX d M p q s hN hp hM hpM hD Pq hPq .Uq := by
  have hU : IsMaximalAt d q (d.Utower M p s hN) := isMaximalAt_Utower hPq.dvd
  have hqp : q ≠ p := fun e => hp (by rw [hD]; exact dvd_of_eq e.symm)
  cases h with
  | T ℓ hℓ hℓN =>
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hqℓ : q ≠ ℓ := fun e => hℓN (by rw [← e]; exact dvd_mul_left q (M * p))
    exact (heckeTHom_comp_PiEllHom ℤ d hPq.dvd hU Pq (elemT d ℓ (not_dvd_D_of_T d M p q hD hℓN))
      (localProjUnits_localEmbedGL_of_ne (p := ℓ) (hp := not_dvd_D_of_T d M p q hD hℓN)
        (Langlandscape.Local.diagGL (padicUnit ℓ) 1) hqℓ)
      (relIndex_elemT_ne_zero_Utower d ℓ _ (not_dvd_M_of_T M p q hℓN) (ne_p_of_T M p q hℓN))).symm
  | Up hs =>
    exact (heckeTHom_comp_PiEllHom ℤ d hPq.dvd hU Pq (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p))
      (localProjUnits_localEmbedGL_of_ne (p := p) (hp := hp) (Langlandscape.Local.varpiDiag p) hqp)
      (Up_relIndex_ne_zero hM hpM hs)).symm
  | Tp hs =>
    exact (heckeTHom_comp_PiEllHom ℤ d hPq.dvd hU Pq (elemT d p hp)
      (localProjUnits_localEmbedGL_of_ne (p := p) (hp := hp) (Langlandscape.Local.diagGL (padicUnit p) 1) hqp)
      (relIndex_elemT_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) (not_dvd_of_s_eq_zero M p s hpM hs))).symm
  | dia u =>
    have e := (PiEllHom_commute_diaZX d M p q s hN hD Pq hPq u⁻¹).eq
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at e
    exact e
  | Uq => rfl

/-- `def:s05-theta` (`s05-theta`): `θ(U_q) ∘ θ(h) = θ(h) ∘ θ(U_q)` on `ℤ[X_B(U_s)]⁰ = degZero`, for every Hecke
symbol `h` (input of the toy `Hyp.X.gal` instance, S05-L4). -/
theorem theta_comm_Uq (h : HeckeSym M p q s) :
    theta d M p q s hN hp hM hpM hD Pq hPq .Uq ∘ₗ theta d M p q s hN hp hM hpM hD Pq hPq h =
      theta d M p q s hN hp hM hpM hD Pq hPq h ∘ₗ theta d M p q s hN hp hM hpM hD Pq hPq .Uq := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact LinearMap.congr_fun (thetaZX_comm_Uq d M p q s hN hp hM hpM hD Pq hPq h) (x : ZX (d.Utower M p s hN) ℤ)

end Theta

end

end Langlandscape.Comparison
