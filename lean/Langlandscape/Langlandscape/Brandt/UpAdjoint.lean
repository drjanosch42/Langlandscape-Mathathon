/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.HeckeFinite

/-!
# `U'_p`, `U_p^*` and `⟨p⟩_M` (S04-L5, carry-over of `lem:s01-Up`(c),(d))

`mathematics/chapters/s01/4-hecke.tex`, `lem:s01-Up`(c),(d), `def:s01-hecke`. Level `U_s = U_1(M p^s)`
(`Utower d M p s`), `s ≥ 1`, `p ∤ M`, `p ∤ D`; trivial coefficients. At `p` write `ϖ = diag(p, 1)`,
`η = diag(1, p)` (`diagOneP`), `z_p = diag(p, p)` (`elemS`), all placed at `p` by `localEmbedGL`.

* `UpPrime` : `U'_p = [U_s η U_s]` on `R[X]` (`UpPrimeDual` on `R^X`); finiteness `UpPrime_relIndex_ne_zero`
  (via `relIndex_ne_zero_of_cover`, `Brandt/HeckeFinite.lean`) from the representatives
  `η^{(s)}_j = !![1, 0; p^s j, p]` (`diag1p_reps`, `exists_varpiPrime_inv_mul`).
* `UpStar` : `U_p^* = [U_s ϖ⁻¹ U_s]` on `R[X]` (the same embedding as `Up`); finiteness `UpStar_relIndex_ne_zero`
  (`ϖ⁻¹ = z_p⁻¹ η` with `z_p` central, `localEmbedGL_varpiDiag_inv`).
* `brandtPairing_UpHom_UpStar` : `⟨U_p a, b⟩ = ⟨a, U_p^* b⟩` (`prop:s01-adjoint`(a) with `g = ϖ`; the weights
  `w_x` are already built into `brandtPairing_heckeTHom`, so no `w_x = 1` hypothesis is needed).
* `diamondM` : `⟨p⟩_M`, right translation `[x] ↦ [x e_p]` by the central idele `e_p = ι(p) z_p⁻¹` (`scalarE`):
  `e_p` is `p` at every `ℓ ≠ p` and `1` at `p`; at `ℓ ∣ M`, `diag(p, p) ∈ diag(1, p) K_1(ℓ^e)`, at `ℓ ∤ Mp` it lies in
  `GL₂(ℤ_ℓ)`, so `e_p ∈ (∏_{ℓ ∣ M} δ_{p,ℓ}) U_s`: this is the tex's `⟨d⟩ = ∏_{ℓ ∣ M} ⟨d⟩_ℓ` for `d ≡ p mod M`,
  `d ≡ 1 mod p^s` (`lem:s01-Up`(d), Step 3, *proved in the tex*). `diamondM` is defined via `e_p`; the comparison with
  the product of the one-prime factors `diamond` is *not formalized* (S04-L5 deviation, audit R3).
* `UpStar_eq_diamondM_UpPrime` : `U_p^* = ⟨p⟩_M U'_p` (`lem:s01-Up`(d)); sign `+1`, confirmed numerically by
  S04-C3a (`code/results/s04/H6_sign.json`, `"sign": "+1"`).
* `UpPrime_comm_trace` : `tr ∘ U'_p = U'_p ∘ tr` for `tr = tr_{s+1,s}` (trace half of `lem:s01-Up`(c)).

Status: *formalized*.
-/

open Pointwise
open Langlandscape.Local

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

/-! ### Local identities at `p` -/

section LocalId

variable {p : ℕ} [Fact p.Prime]

/-- `lem:s01-Up`(d), Step 2 (`s01-Up`): `diag(p, p) = diag(1, p) · diag(p, 1)` in `GL₂(ℚ_p)`. -/
theorem diagGL_padicUnit_eq_diagOneP_mul_varpiDiag :
    diagGL (padicUnit p) (padicUnit p) = diagOneP p * varpiDiag p := by
  apply Units.ext
  rw [Units.val_mul, diagGL_val]
  simp only [diagOneP, varpiDiag, matGL_val, Matrix.mul_fin_two, padicUnit, Units.val_mk0]
  refine mat_eq ?_ ?_ ?_ ?_ <;> ring

variable {d : DefiniteData} {hp : ¬ p ∣ d.D}

/-- `lem:s01-Up`(d), Step 2 (`s01-Up`): `ϖ⁻¹ = z_p⁻¹ η` in `B̂^×` (`ϖ = ι_p⁻¹ diag(p, 1)`, `η = ι_p⁻¹ diag(1, p)`,
`z_p = ι_p⁻¹ diag(p, p)` central). -/
theorem localEmbedGL_varpiDiag_inv :
    (localEmbedGL d p hp (varpiDiag p))⁻¹ = (elemS d p hp)⁻¹ * localEmbedGL d p hp (diagOneP p) := by
  unfold elemS
  rw [diagGL_padicUnit_eq_diagOneP_mul_varpiDiag, map_mul, mul_inv_rev, inv_mul_cancel_right]

end LocalId

/-! ### Cosets of `U_s η U_s` and finiteness -/

section Cosets

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hp : ¬ p ∣ d.D}

/-- `lem:s01-Up`(c) (`s01-Up`): for `u ∈ U_s` there is `j < p` with `(η^{(s)}_j)⁻¹ (u η) ∈ U_s`,
`η^{(s)}_j = ι_p⁻¹ !![1, 0; p^s j, p]` (globalisation of `exists_varpiPrime_inv_mul`). -/
theorem exists_varpiPrime_inv_mul_mem (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    {u : (GL2TF.Quat.BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) :
    ∃ j : Fin p, (localEmbedGL d p hp (varpiPrime p s j))⁻¹ *
      (u * localEmbedGL d p hp (diagOneP p)) ∈ d.Utower M p s hN := by
  have hfac := (mem_Utower_iff_factor_at (hp := hp) hM hpM hs u).1 hu
  obtain ⟨j, hj⟩ := exists_varpiPrime_inv_mul hs hfac.2
  refine ⟨j, ?_⟩
  have hu' : awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u) = u :=
    awayAt_mul_localEmbedGL u
  have hc := (commute_awayAt_localEmbedGL (hp := hp) u (varpiPrime p s j)).inv_right
  have e : (localEmbedGL d p hp (varpiPrime p s j))⁻¹ * (u * localEmbedGL d p hp (diagOneP p)) =
      awayAt d p hp u * localEmbedGL d p hp
        ((varpiPrime p s j)⁻¹ * (localComponent d p hp u * diagOneP p)) := by
    conv_lhs => rw [← hu']
    rw [map_mul, map_mul, map_inv]
    simp only [← mul_assoc, hc.eq]
  rw [e]
  exact mul_mem hfac.1 (localEmbedGL_mem_Utower hM hpM hs hj)

/-- `lem:s01-Up`(c) (`s01-Up`): `[U_s : U_s ∩ η U_s η⁻¹] < ∞` (it is `p`), so `U'_p = [U_s η U_s]` is defined. -/
theorem UpPrime_relIndex_ne_zero (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p))).relIndex
      (d.Utower M p s hN) ≠ 0 :=
  relIndex_ne_zero_of_cover _ _ (fun j : Fin p => localEmbedGL d p hp (varpiPrime p s j))
    (fun _ hu => exists_varpiPrime_inv_mul_mem hM hpM hs hu)

/-- `lem:s01-Up`(d) (`s01-Up`): `[U_s : U_s ∩ ϖ⁻¹ U_s ϖ] < ∞`, so `U_p^* = [U_s ϖ⁻¹ U_s]` is defined
(the `hfin'` of `brandtPairing_heckeTHom` at `g = ϖ`). -/
theorem UpStar_relIndex_ne_zero (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))⁻¹).relIndex
      (d.Utower M p s hN) ≠ 0 := by
  rw [localEmbedGL_varpiDiag_inv,
    conjSub_mul_central _ _ _ (fun x => (elemS_commute d p hp x).inv_left)]
  exact UpPrime_relIndex_ne_zero hM hpM hs

end Cosets

/-! ### The central idele `e_p` -/

/-- `lem:s01-Up`(d), Step 3 (`s01-Up`): `e_p = ι(p) z_p⁻¹` (`scalarE`) is central in `B̂^×`. -/
theorem scalarE_commute (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : Commute (scalarE d p hp) x :=
  (commute_iotaU_scalar (ellUnit p) x).mul_left (elemS_commute d p hp x).inv_left

/-! ### The operators -/

section Operators

/-- `lem:s01-Up`(c), `def:s01-hecke`: the operator `U'_p = [U_s η U_s]` on `R[X]`, `X = X_B(U_s)`,
`η = ι_p⁻¹ diag(1, p)` (the seed's literal formula), `[x] ↦ ∑_j [x η^{(s)}_j]`; `s ≥ 1`, `p ∤ M`. -/
noncomputable def UpPrime (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R]
    [Finite (XB (d.Utower M p s hN))] :
    ZX (d.Utower M p s hN) R →ₗ[R] ZX (d.Utower M p s hN) R :=
  heckeTHom (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p)) R (UpPrime_relIndex_ne_zero hM hpM hs)

/-- `lem:s01-Up`(c), `def:s01-hecke`: the operator `U'_p = [U_s η U_s]` on `R^X`, `(U'_p f)(x) = ∑_j f(x η^{(s)}_j)`
(the transpose of `UpPrime`, `heckeTHom_transpose`). -/
noncomputable def UpPrimeDual (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R] :
    ZXdual (d.Utower M p s hN) R →ₗ[R] ZXdual (d.Utower M p s hN) R :=
  heckeT (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p)) R (UpPrime_relIndex_ne_zero hM hpM hs)

/-- `lem:s01-Up`(d), `def:s01-hecke`: the Brandt-adjoint `U_p^* = [U_s ϖ⁻¹ U_s]` of `UpHom` on `R[X]`,
`ϖ = ι_p⁻¹ diag(p, 1)` the element of `Up`/`UpHom` (`brandtPairing_UpHom_UpStar`). -/
noncomputable def UpStar (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R]
    [Finite (XB (d.Utower M p s hN))] :
    ZX (d.Utower M p s hN) R →ₗ[R] ZX (d.Utower M p s hN) R :=
  heckeTHom (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))⁻¹ R (UpStar_relIndex_ne_zero hM hpM hs)

/-- `lem:s01-Up`(d), Step 3, `def:s01-hecke`: the diamond operator `⟨p⟩_M = ⟨d⟩`, `d ≡ p mod M`, `d ≡ 1 mod p^s`, on
`R[X]`: `[x] ↦ [x e_p]` for the central idele `e_p = ι(p) z_p⁻¹` (`scalarE`, `p` at `ℓ ≠ p`, `1` at `p`), which lies in
`(∏_{ℓ ∣ M} δ_{p,ℓ}) U_s` (homological convention `⟨d⟩[x] = [x δ_d]` of `Brandt.diamond`). `diamondM` is *defined* via
`e_p`; its identification with the product `∏_{ℓ ∣ M} diamond ℓ t_ℓ` of the stage-1 one-prime operators `diamond` is
*proved in the tex* (`lem:s01-Up`(d), Step 3) and *not formalized* (S04-L17a, audit R3). -/
noncomputable def diamondM (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (R : Type*) [CommRing R] [Finite (XB (d.Utower M p s hN))] :
    ZX (d.Utower M p s hN) R →ₗ[R] ZX (d.Utower M p s hN) R :=
  heckeTHom (d.Utower M p s hN) (scalarE d p hp) R
    (relIndex_ne_zero_of_commute _ _ (scalarE_commute d p hp))

end Operators

/-! ### Adjoint and `U_p^* = ⟨p⟩_M U'_p` -/

section Adjoint

variable {R : Type*} [CommRing R]
variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hp : ¬ p ∣ d.D}

/-- `lem:s01-Up`(d), `prop:s01-adjoint`(a) (`s01-Up`): `U_p^*` is the adjoint of `U_p` for the Brandt pairing on
`R[X]`, `⟨U_p a, b⟩ = ⟨a, U_p^* b⟩`. -/
theorem brandtPairing_UpHom_UpStar [Finite (XB (d.Utower M p s hN))] (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (x y : ZX (d.Utower M p s hN) R) :
    brandtPairing (d.Utower M p s hN) R (UpHom d M p s hN hp hM hpM hs R x) y =
      brandtPairing (d.Utower M p s hN) R x (UpStar d M p s hN hp hM hpM hs R y) :=
  brandtPairing_heckeTHom (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) R
    (Up_relIndex_ne_zero hM hpM hs) (UpStar_relIndex_ne_zero hM hpM hs) x y

/-- `lem:s01-Up`(d), Step 3 (`s01-Up`): on `R^X`, right translation by `z_p⁻¹` equals right translation by
`e_p = ι(p) z_p⁻¹` (the global scalar `ι(p)` acts trivially on `X = B^× \ B̂^× / U`). -/
theorem heckeT_elemS_inv_eq_scalarE (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ)
    (hz : (U ⊓ conjSub U (elemS d p hp)⁻¹).relIndex U ≠ 0)
    (he : (U ⊓ conjSub U (scalarE d p hp)).relIndex U ≠ 0) :
    heckeT U (elemS d p hp)⁻¹ R hz = heckeT U (scalarE d p hp) R he := by
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [heckeT_central_apply U R _ (fun y => (elemS_commute d p hp y).inv_left) hz,
    heckeT_central_apply U R _ (scalarE_commute d p hp) he]
  congr 1
  rw [DoubleCoset.eq]
  refine ⟨iotaU d.a d.b (scalarUnit d.a d.b (ellUnit p)), MonoidHom.mem_range.2 ⟨_, rfl⟩, 1, one_mem _, ?_⟩
  have hc := (commute_iotaU_scalar (ellUnit p) x).eq
  calc x * scalarE d p hp
      = x * (iotaU d.a d.b (scalarUnit d.a d.b (ellUnit p)) * (elemS d p hp)⁻¹) := rfl
    _ = x * iotaU d.a d.b (scalarUnit d.a d.b (ellUnit p)) * (elemS d p hp)⁻¹ := (mul_assoc _ _ _).symm
    _ = iotaU d.a d.b (scalarUnit d.a d.b (ellUnit p)) * x * (elemS d p hp)⁻¹ := by rw [hc]
    _ = iotaU d.a d.b (scalarUnit d.a d.b (ellUnit p)) * (x * (elemS d p hp)⁻¹) * 1 := by
        rw [mul_one, mul_assoc]

/-- `lem:s01-Up`(d) (`s01-Up`): `U_p^* = ⟨p⟩_M U'_p` on `R[X]`, `X = X_B(U_1(M p^s))`, `s ≥ 1`, trivial coefficients
(`ϖ⁻¹ = z_p⁻¹ η`, `[x z_p⁻¹] = [x e_p]`, `e_p` central). The exponent `+1` of `⟨p⟩_M` agrees with S04-C3a
(`H6_sign.json`). Here `⟨p⟩_M` is `diamondM`, translation by the central idele `e_p`; that it equals the product of
the stage-1 one-prime `diamond`s (so the tex's `⟨d⟩`, `d ≡ p mod M`, `d ≡ 1 mod p^s`) is *proved in the tex*
(`lem:s01-Up`(d), Step 3) and *computed* (H6), *not formalized*. -/
theorem UpStar_eq_diamondM_UpPrime [Finite (XB (d.Utower M p s hN))] (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) :
    UpStar d M p s hN hp hM hpM hs R =
      diamondM d M p s hN hp R ∘ₗ UpPrime d M p s hN hp hM hpM hs R := by
  have hzc : ∀ x, Commute (elemS d p hp)⁻¹ x := fun x => (elemS_commute d p hp x).inv_left
  have hec : ∀ x, Commute (scalarE d p hp) x := scalarE_commute d p hp
  have hS := UpStar_relIndex_ne_zero (hN := hN) (hp := hp) hM hpM hs
  have hη := UpPrime_relIndex_ne_zero (hN := hN) (hp := hp) hM hpM hs
  have he := relIndex_ne_zero_of_commute (d.Utower M p s hN) _ hec
  have hz := relIndex_ne_zero_of_commute (d.Utower M p s hN) _ hzc
  have hA : (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN)
      ((elemS d p hp)⁻¹ * localEmbedGL d p hp (diagOneP p))).relIndex (d.Utower M p s hN) ≠ 0 := by
    rw [conjSub_mul_central _ _ _ hzc]
    exact hη
  have h1 : heckeT (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))⁻¹ R hS =
      heckeT (d.Utower M p s hN) ((elemS d p hp)⁻¹ * localEmbedGL d p hp (diagOneP p)) R hA :=
    heckeT_congr_dcSet _ R (by rw [localEmbedGL_varpiDiag_inv]) hS hA
  have h2 := heckeT_central_mul (d.Utower M p s hN) R _ _ hzc hη hz hA
  have h3 := heckeT_elemS_inv_eq_scalarE (R := R) (d.Utower M p s hN) hz he
  have h4 := heckeT_central_comm (d.Utower M p s hN) R _ _ hec he hη
  have hcomp : heckeT (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))⁻¹ R hS =
      heckeT (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p)) R hη ∘ₗ
        heckeT (d.Utower M p s hN) (scalarE d p hp) R he := by
    rw [h1, h2, h3, h4]
  exact heckeTHom_comp _ R _ _ _ hS hη he hcomp

end Adjoint

/-! ### `U'_p` commutes with the trace (trace half of `lem:s01-Up`(c)) -/

section LocalTrace

variable {p : ℕ} [Fact p.Prime]

/-- `lem:s01-Up`(c), trace (`s01-Up`): if `k ∈ K_1(p^{s+1})` and `η k η⁻¹ ∈ K_1(p^s)` (`η = diag(1, p)`), then
`η k η⁻¹ ∈ K_1(p^{s+1})`: the lower row of `η k η⁻¹` is `(p c, d)` for the lower row `(c, d)` of `k`. -/
theorem diagOneP_conj_mem_K1_succ {s : ℕ} {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K1 p (s + 1))
    (hm : diagOneP p * k * (diagOneP p)⁻¹ ∈ K1 p s) :
    diagOneP p * k * (diagOneP p)⁻¹ ∈ K1 p (s + 1) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨a, b, c, d, hM, -, hc, hd⟩ := mem_K1_iff_exists.1 hk
  obtain ⟨a', b', c', d', hM', hu', -, -⟩ := mem_K1_iff_exists.1 hm
  have H : Units.val (diagOneP p * k * (diagOneP p)⁻¹) * Units.val (diagOneP p) =
      Units.val (diagOneP p) * Units.val k := by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hM', hM] at H
  have h10 : ((c' : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) * c := by
    have h := congrFun (congrFun H 1) 0
    simpa [diagOneP, Matrix.mul_apply, Fin.sum_univ_two] using h
  have h11 : ((d' : ℤ_[p]) : ℚ_[p]) * p = (p : ℚ_[p]) * d := by
    have h := congrFun (congrFun H 1) 1
    simpa [diagOneP, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hc' : c' = (p : ℤ_[p]) * c := Subtype.ext (by simpa using h10)
  have hd' : d' = d := Subtype.ext (mul_right_cancel₀ hp0 (h11.trans (mul_comm _ _)))
  refine mem_K1_of_entries a' b' c' d' hM' hu' ?_ ?_
  · rw [hc']
    exact dvd_mul_of_dvd_right hc _
  · rw [hd']
    exact hd

/-- `lem:s01-Up`(c), trace (`s01-Up`): `K_1(p^s) η ⊆ K_1(p^s) η K_1(p^{s+1})` for `s ≥ 1` (`η = diag(1, p)`):
`η k = l (η k')` with `k' = !![a, b; 0, 1] ∈ K_1(p^{s+1})` and `l = !![1, 0; p c / a, d - c b / a] ∈ K_1(p^s)`,
for `k = !![a, b; c, d]`. -/
theorem exists_diagOneP_mul_eq {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K1 p s) :
    ∃ l ∈ K1 p s, ∃ k' ∈ K1 p (s + 1), diagOneP p * k = l * (diagOneP p * k') := by
  obtain ⟨a, b, c, d, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hk
  have hpc : (p : ℤ_[p]) ∣ c := (dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans hc
  have ha : IsUnit a := by
    have hu' := hu
    rw [isUnit_iff_not_dvd] at hu' ⊢
    exact fun h => hu' (dvd_sub (dvd_mul_of_dvd_left h d) (dvd_mul_of_dvd_right hpc b))
  obtain ⟨ainv, hainv, hainvU⟩ : ∃ ainv : ℤ_[p], a * ainv = 1 ∧ IsUnit ainv :=
    ⟨_, ha.mul_val_inv, (ha.unit⁻¹).isUnit⟩
  have hainvQ : (a : ℚ_[p]) * (ainv : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, hainv, PadicInt.coe_one]
  have ha0 : (a : ℚ_[p]) ≠ 0 := fun h => by simp [h] at hainvQ
  obtain ⟨k', hk'v⟩ : ∃ k' : GL (Fin 2) ℚ_[p],
      Units.val k' = !![(a : ℚ_[p]), (b : ℚ_[p]); ((0 : ℤ_[p]) : ℚ_[p]), ((1 : ℤ_[p]) : ℚ_[p])] :=
    ⟨matGL (a : ℚ_[p]) (b : ℚ_[p]) ((0 : ℤ_[p]) : ℚ_[p]) ((1 : ℤ_[p]) : ℚ_[p])
      (by rw [PadicInt.coe_zero, PadicInt.coe_one, mul_one, mul_zero, sub_zero]; exact ha0), rfl⟩
  have hk' : k' ∈ K1 p (s + 1) :=
    mem_K1_of_entries a b 0 1 hk'v (by rw [mul_one, mul_zero, sub_zero]; exact ha) (dvd_zero _)
      (by rw [sub_self]; exact dvd_zero _)
  have H : !![((1 : ℤ_[p]) : ℚ_[p]), ((0 : ℤ_[p]) : ℚ_[p]);
      (((p : ℤ_[p]) * c * ainv : ℤ_[p]) : ℚ_[p]), ((d - c * b * ainv : ℤ_[p]) : ℚ_[p])] *
        Units.val (diagOneP p * k') = Units.val (diagOneP p * k) := by
    rw [Units.val_mul, Units.val_mul, hM, hk'v]
    simp only [diagOneP, matGL_val, Matrix.mul_fin_two]
    refine mat_eq ?_ ?_ ?_ ?_ <;>
      simp only [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_zero,
        PadicInt.coe_natCast]
    · ring
    · ring
    · linear_combination ((p : ℚ_[p]) * (c : ℚ_[p])) * hainvQ
    · ring
  have hl : Units.val (diagOneP p * k * (diagOneP p * k')⁻¹) =
      !![((1 : ℤ_[p]) : ℚ_[p]), ((0 : ℤ_[p]) : ℚ_[p]);
        (((p : ℤ_[p]) * c * ainv : ℤ_[p]) : ℚ_[p]), ((d - c * b * ainv : ℤ_[p]) : ℚ_[p])] := by
    rw [Units.val_mul (diagOneP p * k) (diagOneP p * k')⁻¹, ← H, mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]
  refine ⟨diagOneP p * k * (diagOneP p * k')⁻¹, ?_, k', hk', by group⟩
  refine mem_K1_of_entries 1 0 ((p : ℤ_[p]) * c * ainv) (d - c * b * ainv) hl ?_ ?_ ?_
  · have e : 1 * (d - c * b * ainv) - 0 * ((p : ℤ_[p]) * c * ainv) = (a * d - b * c) * ainv := by
      linear_combination (-d) * hainv
    rw [e]
    exact hu.mul hainvU
  · exact (dvd_mul_of_dvd_right hc _).mul_right _
  · have e : d - c * b * ainv - 1 = (d - 1) - c * (b * ainv) := by ring
    rw [e]
    exact dvd_sub hd (hc.mul_right _)

end LocalTrace

section TraceAbstract

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)
  (R : Type*) [CommRing R]

/-- `lem:s01-Up`(c), trace (`s01-Up`): for `U' ≤ U` of finite index, `tr ∘ T_g = T_g ∘ tr` (`tr = tr_{U'}^{U}`,
`T_g = [U' g U']` resp. `[U g U]`) as soon as `U g U = U · (U' g U')` (`hdc`) and `g U' g⁻¹ ∩ U ⊆ U'` (`hconj`): both
sides are the sum of `f(x ω)` over `ω ∈ U g U / U'`, indexed by `(gᵢ, u)` resp. `(u, g'ⱼ)`. -/
theorem trace_comp_heckeT (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U' ⊓ conjSub U' g).relIndex U' ≠ 0)
    (hdc : ∀ y ∈ dcSet U g, ∃ u ∈ U, u⁻¹ * y ∈ dcSet U' g)
    (hconj : ∀ β ∈ U', g * β * g⁻¹ ∈ U → g * β * g⁻¹ ∈ U') :
    trace U' U R hrel ∘ₗ heckeT U' g R hfin' = heckeT U g R hfin ∘ₗ trace U' U R hrel := by
  classical
  have := finite_quotient_of_relIndex U' U hrel
  let _ : Fintype (↥U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U g hfin
  obtain ⟨S', hS', hcov', hinj'⟩ := exists_heckeReps U' g hfin'
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  -- `f(x y)` depends only on `y U'`
  have hF : ∀ y : (GL2TF.Quat.BHat a b)ˣ,
      f (DoubleCoset.mk (globalUnits a b) U' (x * y)) =
        f (DoubleCoset.mk (globalUnits a b) U' (x * Quotient.out (QuotientGroup.mk y :
          (GL2TF.Quat.BHat a b)ˣ ⧸ U'))) := by
    intro y
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U' y
    rw [hh, ← mul_assoc]
    exact (liftFun_mul_right U' R f (x * y) h.2).symm
  -- injectivity of `(gᵢ, u) ↦ gᵢ u U'`
  have inj1 : Set.InjOn (fun p : (GL2TF.Quat.BHat a b)ˣ × (↥U ⧸ U'.subgroupOf U) =>
      (QuotientGroup.mk (p.1 * ((Quotient.out p.2 : U) : (GL2TF.Quat.BHat a b)ˣ)) :
        (GL2TF.Quat.BHat a b)ˣ ⧸ U'))
      ↑(S ×ˢ (Finset.univ : Finset (↥U ⧸ U'.subgroupOf U))) := by
    rintro ⟨s1, q1⟩ h1 ⟨s2, q2⟩ h2 e
    have h1' : s1 ∈ S := (Finset.mem_product.1 (Finset.mem_coe.1 h1)).1
    have h2' : s2 ∈ S := (Finset.mem_product.1 (Finset.mem_coe.1 h2)).1
    have e' : (s1 * ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ))⁻¹ *
        (s2 * ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ)) ∈ U' := QuotientGroup.eq.1 e
    have hs : s1 = s2 := by
      refine hinj (Finset.mem_coe.2 h1') (Finset.mem_coe.2 h2') ?_
      show (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s2
      rw [QuotientGroup.eq]
      have hm := U.mul_mem (U.mul_mem (Quotient.out q1).2 (hle e')) (U.inv_mem (Quotient.out q2).2)
      have eq : ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ) *
          ((s1 * ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ))⁻¹ *
            (s2 * ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ))) *
          ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ = s1⁻¹ * s2 := by group
      rwa [eq] at hm
    rw [hs] at e'
    have hq : q1 = q2 := by
      rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      have eq : (s2 * ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ))⁻¹ *
          (s2 * ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ)) =
          ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
            ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) := by group
      rwa [eq] at e'
    rw [hs, hq]
  -- injectivity of `(u, g'ⱼ) ↦ u g'ⱼ U'` (uses `hconj`)
  have inj2 : Set.InjOn (fun p : (↥U ⧸ U'.subgroupOf U) × (GL2TF.Quat.BHat a b)ˣ =>
      (QuotientGroup.mk (((Quotient.out p.1 : U) : (GL2TF.Quat.BHat a b)ˣ) * p.2) :
        (GL2TF.Quat.BHat a b)ˣ ⧸ U'))
      ↑((Finset.univ : Finset (↥U ⧸ U'.subgroupOf U)) ×ˢ S') := by
    rintro ⟨q1, s1⟩ h1 ⟨q2, s2⟩ h2 e
    have h1' : s1 ∈ S' := (Finset.mem_product.1 (Finset.mem_coe.1 h1)).2
    have h2' : s2 ∈ S' := (Finset.mem_product.1 (Finset.mem_coe.1 h2)).2
    have e' : (((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ) * s1)⁻¹ *
        (((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) * s2) ∈ U' := QuotientGroup.eq.1 e
    obtain ⟨a1, ha1, b1, hb1, hs1⟩ := (mem_dcSet U' g).1 (hS' s1 h1')
    obtain ⟨a2, ha2, b2, hb2, hs2⟩ := (mem_dcSet U' g).1 (hS' s2 h2')
    have hβ := U'.mul_mem (U'.mul_mem hb1 e') (U'.inv_mem hb2)
    have hgβ : g * (b1 * ((((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ) * s1)⁻¹ *
        (((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) * s2)) * b2⁻¹) * g⁻¹ =
        a1⁻¹ * (((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
          ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ)) * a2 := by
      rw [hs1, hs2]
      group
    have hu : ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
        ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ U :=
      U.mul_mem (U.inv_mem (Quotient.out q1).2) (Quotient.out q2).2
    have hgβU := hconj _ hβ (by
      rw [hgβ]
      exact U.mul_mem (U.mul_mem (U.inv_mem (hle ha1)) hu) (hle ha2))
    rw [hgβ] at hgβU
    have huU' : ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
        ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ U' := by
      have h3 := U'.mul_mem (U'.mul_mem ha1 hgβU) (U'.inv_mem ha2)
      have eq : a1 * (a1⁻¹ * (((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
          ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ)) * a2) * a2⁻¹ =
          ((Quotient.out q1 : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ *
            ((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) := by group
      rwa [eq] at h3
    have hq : q1 = q2 := by
      rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact huU'
    rw [hq] at e'
    have hs : s1 = s2 := by
      refine hinj' (Finset.mem_coe.2 h1') (Finset.mem_coe.2 h2') ?_
      show (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U') = QuotientGroup.mk s2
      rw [QuotientGroup.eq]
      have eq : (((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) * s1)⁻¹ *
          (((Quotient.out q2 : U) : (GL2TF.Quat.BHat a b)ˣ) * s2) = s1⁻¹ * s2 := by group
      rwa [eq] at e'
    rw [hq, hs]
  -- both images are the classes `y U'` with `y ∈ U g U`
  have hΩ1 : ∀ ω : (GL2TF.Quat.BHat a b)ˣ ⧸ U',
      ω ∈ (S ×ˢ (Finset.univ : Finset (↥U ⧸ U'.subgroupOf U))).image
          (fun p : (GL2TF.Quat.BHat a b)ˣ × (↥U ⧸ U'.subgroupOf U) =>
            (QuotientGroup.mk (p.1 * ((Quotient.out p.2 : U) : (GL2TF.Quat.BHat a b)ˣ)) :
              (GL2TF.Quat.BHat a b)ˣ ⧸ U')) ↔
        ∃ y ∈ dcSet U g, (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U') = ω := by
    intro ω
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨s, q⟩, hp, rfl⟩
      exact ⟨s * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ),
        (mul_mem_dcSet_iff_right U g (Quotient.out q).2).2 (hS s (Finset.mem_product.1 hp).1), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨s, hs, hys⟩ := hcov y hy
      have hv : s⁻¹ * y ∈ U := QuotientGroup.eq.1 hys.symm
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨s⁻¹ * y, hv⟩ : U)
      have hw' : ((w : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ U' := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨(s, QuotientGroup.mk (⟨s⁻¹ * y, hv⟩ : U)), Finset.mem_product.2 ⟨hs, Finset.mem_univ _⟩, ?_⟩
      show (QuotientGroup.mk (s * ((Quotient.out (QuotientGroup.mk (⟨s⁻¹ * y, hv⟩ : U) :
        ↥U ⧸ U'.subgroupOf U) : U) : (GL2TF.Quat.BHat a b)ˣ)) : (GL2TF.Quat.BHat a b)ˣ ⧸ U') =
          QuotientGroup.mk y
      rw [hw, QuotientGroup.eq]
      have eq : (s * ((((⟨s⁻¹ * y, hv⟩ : U) * w : U) : (GL2TF.Quat.BHat a b)ˣ)))⁻¹ * y =
          ((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ := by
        show (s * (s⁻¹ * y * ((w : U) : (GL2TF.Quat.BHat a b)ˣ)))⁻¹ * y = _
        group
      rw [eq]
      exact U'.inv_mem hw'
  have hΩ2 : ∀ ω : (GL2TF.Quat.BHat a b)ˣ ⧸ U',
      ω ∈ ((Finset.univ : Finset (↥U ⧸ U'.subgroupOf U)) ×ˢ S').image
          (fun p : (↥U ⧸ U'.subgroupOf U) × (GL2TF.Quat.BHat a b)ˣ =>
            (QuotientGroup.mk (((Quotient.out p.1 : U) : (GL2TF.Quat.BHat a b)ˣ) * p.2) :
              (GL2TF.Quat.BHat a b)ˣ ⧸ U')) ↔
        ∃ y ∈ dcSet U g, (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U') = ω := by
    intro ω
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨q, s'⟩, hp, rfl⟩
      refine ⟨((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ) * s',
        (mul_mem_dcSet_iff_left U g (Quotient.out q).2).2 ?_, rfl⟩
      obtain ⟨a', ha', b', hb', e⟩ := (mem_dcSet U' g).1 (hS' s' (Finset.mem_product.1 hp).2)
      exact (mem_dcSet U g).2 ⟨a', hle ha', b', hle hb', e⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu, hy'⟩ := hdc y hy
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨u, hu⟩ : U)
      have hw' : ((w : U) : (GL2TF.Quat.BHat a b)ˣ) ∈ U' := Subgroup.mem_subgroupOf.1 w.2
      have hy'' : ((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ * (u⁻¹ * y) ∈ dcSet U' g :=
        (mul_mem_dcSet_iff_left U' g (U'.inv_mem hw')).2 hy'
      obtain ⟨s', hs', hys'⟩ := hcov' _ hy''
      have h3 : (((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ * (u⁻¹ * y))⁻¹ * s' ∈ U' := QuotientGroup.eq.1 hys'
      refine ⟨(QuotientGroup.mk (⟨u, hu⟩ : U), s'), Finset.mem_product.2 ⟨Finset.mem_univ _, hs'⟩, ?_⟩
      show (QuotientGroup.mk (((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) :
        ↥U ⧸ U'.subgroupOf U) : U) : (GL2TF.Quat.BHat a b)ˣ) * s') : (GL2TF.Quat.BHat a b)ˣ ⧸ U') =
          QuotientGroup.mk y
      rw [hw, QuotientGroup.eq]
      have eq : ((((⟨u, hu⟩ : U) * w : U) : (GL2TF.Quat.BHat a b)ˣ) * s')⁻¹ * y =
          ((((w : U) : (GL2TF.Quat.BHat a b)ˣ)⁻¹ * (u⁻¹ * y))⁻¹ * s')⁻¹ := by
        show (u * ((w : U) : (GL2TF.Quat.BHat a b)ˣ) * s')⁻¹ * y = _
        group
      rw [eq]
      exact U'.inv_mem h3
  have hΩ : ((Finset.univ : Finset (↥U ⧸ U'.subgroupOf U)) ×ˢ S').image
        (fun p : (↥U ⧸ U'.subgroupOf U) × (GL2TF.Quat.BHat a b)ˣ =>
          (QuotientGroup.mk (((Quotient.out p.1 : U) : (GL2TF.Quat.BHat a b)ˣ) * p.2) :
            (GL2TF.Quat.BHat a b)ˣ ⧸ U')) =
      (S ×ˢ (Finset.univ : Finset (↥U ⧸ U'.subgroupOf U))).image
        (fun p : (GL2TF.Quat.BHat a b)ˣ × (↥U ⧸ U'.subgroupOf U) =>
          (QuotientGroup.mk (p.1 * ((Quotient.out p.2 : U) : (GL2TF.Quat.BHat a b)ˣ)) :
            (GL2TF.Quat.BHat a b)ˣ ⧸ U')) :=
    Finset.ext fun ω => (hΩ2 ω).trans (hΩ1 ω).symm
  -- the two double sums
  have e1 : (∑ s ∈ S, ∑ q : ↥U ⧸ U'.subgroupOf U,
      f (DoubleCoset.mk (globalUnits a b) U'
        (x * s * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ)))) =
      ∑ ω ∈ (S ×ˢ (Finset.univ : Finset (↥U ⧸ U'.subgroupOf U))).image
          (fun p : (GL2TF.Quat.BHat a b)ˣ × (↥U ⧸ U'.subgroupOf U) =>
            (QuotientGroup.mk (p.1 * ((Quotient.out p.2 : U) : (GL2TF.Quat.BHat a b)ˣ)) :
              (GL2TF.Quat.BHat a b)ˣ ⧸ U')),
        f (DoubleCoset.mk (globalUnits a b) U' (x * Quotient.out ω)) := by
    rw [Finset.sum_image inj1, Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_assoc]
    exact hF _
  have e2 : (∑ q : ↥U ⧸ U'.subgroupOf U, ∑ s' ∈ S',
      f (DoubleCoset.mk (globalUnits a b) U'
        (x * ((Quotient.out q : U) : (GL2TF.Quat.BHat a b)ˣ) * s'))) =
      ∑ ω ∈ ((Finset.univ : Finset (↥U ⧸ U'.subgroupOf U)) ×ˢ S').image
          (fun p : (↥U ⧸ U'.subgroupOf U) × (GL2TF.Quat.BHat a b)ˣ =>
            (QuotientGroup.mk (((Quotient.out p.1 : U) : (GL2TF.Quat.BHat a b)ˣ) * p.2) :
              (GL2TF.Quat.BHat a b)ˣ ⧸ U')),
        f (DoubleCoset.mk (globalUnits a b) U' (x * Quotient.out ω)) := by
    rw [Finset.sum_image inj2, Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [mul_assoc]
    exact hF _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, trace_apply_mk,
    heckeT_apply_reps U g R hfin S hS hcov hinj]
  simp only [traceRaw, trace_apply_mk, finsum_eq_sum_of_fintype,
    heckeT_apply_reps U' g R hfin' S' hS' hcov' hinj']
  refine (e2.trans ?_).trans e1.symm
  rw [hΩ]

end TraceAbstract

section TraceTower

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hN' : (M * p ^ (s + 1)).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s01-Up`(c), `def:s01-levels` (`s01-Up`): `[U_s : U_{s+1}] < ∞` (so `tr_{s+1,s}` is defined). -/
theorem relIndex_Utower_succ_ne_zero (hM : M ≠ 0) :
    (d.Utower M p (s + 1) hN').relIndex (d.Utower M p s hN) ≠ 0 := by
  have : NeZero (M * p ^ (s + 1)) :=
    ⟨mul_ne_zero hM (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  have h : (d.Utower M p (s + 1) hN').relIndex d.Ohat ≠ 0 := d.relIndex_U1_ne_zero (M * p ^ (s + 1)) hN'
  have hle : d.Utower M p s hN ≤ d.Ohat := DefiniteData.U1_le_units (d := d) _ hN
  have h2 := Subgroup.relIndex_mul_relIndex (d.Utower M p (s + 1) hN') (d.Utower M p s hN) d.Ohat
    (Utower_succ_le hN hN' hM) hle
  exact left_ne_zero_of_mul (h2.trans_ne h)

/-- `lem:s01-Up`(c), trace (`s01-Up`): `U_s η U_s = U_s · (U_{s+1} η U_{s+1})` (`η = ι_p⁻¹ diag(1, p)`, `s ≥ 1`). -/
theorem dcSet_diagOneP_succ (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ∀ y ∈ dcSet (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p)),
      ∃ u ∈ d.Utower M p s hN, u⁻¹ * y ∈ dcSet (d.Utower M p (s + 1) hN') (localEmbedGL d p hp (diagOneP p)) := by
  intro y hy
  obtain ⟨u0, hu0, v, hv, rfl⟩ := (mem_dcSet _ _).1 hy
  have hfac := (mem_Utower_iff_factor_at (hp := hp) hM hpM hs v).1 hv
  obtain ⟨l, hl, k', hk', hek⟩ := exists_diagOneP_mul_eq hs hfac.2
  refine ⟨u0 * awayAt d p hp v * localEmbedGL d p hp l,
    mul_mem (mul_mem hu0 hfac.1) (localEmbedGL_mem_Utower hM hpM hs hl), ?_⟩
  refine (mem_dcSet _ _).2 ⟨1, one_mem _, localEmbedGL d p hp k',
    localEmbedGL_mem_Utower hM hpM (Nat.le_add_left 1 s) hk', ?_⟩
  have hcomm : localEmbedGL d p hp (diagOneP p) * awayAt d p hp v =
      awayAt d p hp v * localEmbedGL d p hp (diagOneP p) :=
    (commute_awayAt_localEmbedGL (hp := hp) v (diagOneP p)).eq.symm
  have hloc : localEmbedGL d p hp (diagOneP p) * localEmbedGL d p hp (localComponent d p hp v) =
      localEmbedGL d p hp l * (localEmbedGL d p hp (diagOneP p) * localEmbedGL d p hp k') := by
    rw [← map_mul (localEmbedGL d p hp) (diagOneP p) (localComponent d p hp v), hek, map_mul, map_mul]
  have e1 : u0 * localEmbedGL d p hp (diagOneP p) * v =
      u0 * awayAt d p hp v * localEmbedGL d p hp l *
        (localEmbedGL d p hp (diagOneP p) * localEmbedGL d p hp k') := by
    calc u0 * localEmbedGL d p hp (diagOneP p) * v
        = u0 * localEmbedGL d p hp (diagOneP p) *
            (awayAt d p hp v * localEmbedGL d p hp (localComponent d p hp v)) := by
          rw [awayAt_mul_localEmbedGL]
      _ = u0 * (localEmbedGL d p hp (diagOneP p) * awayAt d p hp v) *
            localEmbedGL d p hp (localComponent d p hp v) := by
          simp only [mul_assoc]
      _ = u0 * (awayAt d p hp v * localEmbedGL d p hp (diagOneP p)) *
            localEmbedGL d p hp (localComponent d p hp v) := by
          rw [hcomm]
      _ = u0 * awayAt d p hp v * (localEmbedGL d p hp (diagOneP p) *
            localEmbedGL d p hp (localComponent d p hp v)) := by
          simp only [mul_assoc]
      _ = u0 * awayAt d p hp v * localEmbedGL d p hp l *
            (localEmbedGL d p hp (diagOneP p) * localEmbedGL d p hp k') := by
          rw [hloc, mul_assoc (u0 * awayAt d p hp v)]
  rw [e1]
  group

/-- `lem:s01-Up`(c), trace (`s01-Up`): `η β η⁻¹ ∈ U_s` and `β ∈ U_{s+1}` imply `η β η⁻¹ ∈ U_{s+1}`
(`η = ι_p⁻¹ diag(1, p)`; locally `diagOneP_conj_mem_K1_succ`, away from `p` nothing changes). -/
theorem diagOneP_conj_mem_Utower_succ (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ∀ β ∈ d.Utower M p (s + 1) hN',
      localEmbedGL d p hp (diagOneP p) * β * (localEmbedGL d p hp (diagOneP p))⁻¹ ∈ d.Utower M p s hN →
        localEmbedGL d p hp (diagOneP p) * β * (localEmbedGL d p hp (diagOneP p))⁻¹ ∈
          d.Utower M p (s + 1) hN' := by
  intro β hβ h
  have f1 := (mem_Utower_iff_factor_at (hp := hp) hM hpM (Nat.le_add_left 1 s) β).1 hβ
  have f2 := (mem_Utower_iff_factor_at (hp := hp) hM hpM hs _).1 h
  refine (mem_Utower_iff_factor_at (hp := hp) hM hpM (Nat.le_add_left 1 s) _).2 ⟨?_, ?_⟩
  · change awayAt d p hp (localEmbedGL d p hp (diagOneP p) * β * (localEmbedGL d p hp (diagOneP p))⁻¹) ∈ _
    rw [awayAt_conj]
    exact f1.1
  · have f22 := f2.2
    rw [localComponent_conj] at f22 ⊢
    exact diagOneP_conj_mem_K1_succ f1.2 f22

variable {R : Type*} [CommRing R]

/-- `lem:s01-Up`(c), trace half (`s01-Up`): `U'_p` commutes with the trace, `tr ∘ U'_p = U'_p ∘ tr` for
`tr = tr_{s+1,s} : R^{X_B(U_{s+1})} → R^{X_B(U_s)}`, `s ≥ 1` (trivial coefficients; it uses
`U_s η U_s = U_s η U_{s+1}`, `dcSet_diagOneP_succ`). -/
theorem UpPrime_comm_trace (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    trace (d.Utower M p (s + 1) hN') (d.Utower M p s hN) R (relIndex_Utower_succ_ne_zero hM) ∘ₗ
        UpPrimeDual d M p (s + 1) hN' hp hM hpM (Nat.le_add_left 1 s) R =
      UpPrimeDual d M p s hN hp hM hpM hs R ∘ₗ
        trace (d.Utower M p (s + 1) hN') (d.Utower M p s hN) R (relIndex_Utower_succ_ne_zero hM) :=
  trace_comp_heckeT (d.Utower M p (s + 1) hN') (d.Utower M p s hN) (localEmbedGL d p hp (diagOneP p)) R
    (Utower_succ_le hN hN' hM) (relIndex_Utower_succ_ne_zero hM) (UpPrime_relIndex_ne_zero hM hpM hs)
    (UpPrime_relIndex_ne_zero hM hpM (Nat.le_add_left 1 s)) (dcSet_diagOneP_succ hM hpM hs)
    (diagOneP_conj_mem_Utower_succ hM hpM hs)

end TraceTower

end Langlandscape.Brandt
