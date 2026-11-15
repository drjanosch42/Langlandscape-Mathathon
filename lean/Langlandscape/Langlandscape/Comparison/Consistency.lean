/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Dictionary

/-!
# Internal consistency of the Hecke dictionary `θ` (S05-L5)

Tex: `lem:s05-consistency`(b)-(d) (`plan/staged/stage-05-comparison-hypothesis.tex`,
`mathematics/chapters/s05/sign.tex`).  Status: *formalized* (plumbing of the stage-1 API).

* (b) Brandt adjoints of `θ(h)`, at the level of `ℤ[X_B(U_s)]` (hence on `degZero`):
  `theta_adjoint_T` (`T_ℓ^* = S_ℓ^{-1} T_ℓ`, from `Tl_adjoint`), `theta_adjoint_Tp` (`s = 0`:
  `T_p^* = S_p^{-1} T_p`, i.e. `T_p^Ros = ⟨p⟩⁻¹ T_p`, from `Tl_adjoint` at `ℓ = p`), `theta_adjoint_Uq` (`Π_q^* = Π_q^{-1}`,
  from `PiEll_adjoint`), `theta_adjoint_diaLocal` (`⟨t⟩^* = ⟨t⁻¹⟩` for each local factor of the product diamond,
  from `diamond_adjoint`), with `degZero` corollaries and the pairing `brandtPairingDeg`.
  Restriction: the adjoint of the *product* diamond `diaZX` (ordered product over the primes of `M p^s`) and the
  identification of `S_ℓ^{-1}` with `θ(⟨ℓ⟩^{-1})` are not formalized here; the statements are given in the exact
  stage-1 form (`SlInvHom`, `PiEllHom Pq⁻¹`, `heckeTHom` of the inverse diamond element).
* (c) Projection formula `⟨π_* a, b⟩_U = ⟨a, π^* b⟩_{U'}` (`projection_formula`, weights compatible, in particular
  when all `w_x = 1`: `projection_formula_of_wx_one`; at `U_s`, `s ≥ 1`, this holds for `p ≥ 5` by
  `Ordinary.wx_Utower_eq_one`), and the trace forms `projection_formula_trace` (from `normMap_pushforward`) and
  `projection_formula_two` (the factor 2 when `-1 ∈ U ∖ U'`, from `normMap_pushforward_two`).  The trace forms are
  `ν ∘ π_* = tr ∘ ν'` (resp. `tr ∘ ν' = 2 ν ∘ π_*`) paired with `b`; the adjoint sits on the function side.
  The tex's weighted pullback `π^!_w` (the Brandt adjoint of `π_*`) and the transfer `π^!` are not defined in
  Lean; `π^!_w = ½ π^!` in the factor-2 case (`s = 0`, `M ≤ 2`).
  Restriction: not formalized here are `π^!_w` itself, its integrality, `π^!_w(ℤ[S_s]⁰) ⊆ ℤ[S_{s'}]⁰`, the general
  formula `⟨π_* a, b⟩_s = ⟨a, π^!_w b⟩_{s'}`, the case `s = 0`, `M ≥ 3`, and the last clause of (c) (the
  `u`-adjoint of `β` under (X2), (X3)).
* (d) `deg_pushforward`, `pushDegZero`, `Up_comm_pushforward_degZero`: `π_*` commutes with `θ(U_p) = N_{U_p}`
  on `degZero` (`Up_comm_push`, `towerPush_eq_pushforward`).  The failure for `U_p^* = ⟨p⟩_M U'_p` is not a
  Lean statement: it is stage 01, Lemma "properties of `N_{U_p}`"(b), (c) (tex `lem:s05-consistency`(d)).
-/

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

set_option autoImplicit false

namespace Langlandscape.Comparison

noncomputable section

/-! ### The Brandt pairing on `degZero` -/

section PairingDeg

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `lem:s05-consistency` (`s05-consistency`): the Brandt pairing restricted to `degZero U R`. -/
def brandtPairingDeg : degZero U R →ₗ[R] degZero U R →ₗ[R] R :=
  (brandtPairing U R).compl₁₂ (degZero U R).subtype (degZero U R).subtype

/-- `lem:s05-consistency` (`s05-consistency`): `brandtPairingDeg x y = brandtPairing x y`. -/
@[simp] theorem brandtPairingDeg_apply (x y : degZero U R) :
    brandtPairingDeg U R x y = brandtPairing U R (x : ZX U R) (y : ZX U R) :=
  rfl

/-- `lem:s05-consistency` (`s05-consistency`), helper: `⟨[c], y⟩ = r w_c y(c)`. -/
theorem brandtPairing_single_left (c : XB U) (r : R) (y : ZX U R) :
    brandtPairing U R (Finsupp.single c r) y = r * (wx U (Quotient.out c) : R) * y c := by
  simp [brandtPairing, Finsupp.lift_apply, Finsupp.sum_single_index] <;> ring

end PairingDeg

/-! ### (b) Brandt adjoints of `θ(h)` -/

section Adjoint

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(T_ℓ)^* = S_ℓ^{-1} θ(T_ℓ)`, i.e. `T_ℓ^* = ⟨ℓ⟩ T_ℓ` in the
tex normalisation, for the Brandt pairing on `ℤ[X_B(U_s)]`, from stage 01 `Tl_adjoint` (`s01-adjoint`)
(`SlInvHom` is the stage-1 form of `S_ℓ^{-1}`). -/
theorem theta_adjoint_T (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ M * p * q) (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ
        (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) x) y =
      brandtPairing (d.Utower M p s hN) ℤ x
        (SlInvHom d (d.Utower M p s hN) ℓ (not_dvd_D_of_T d M p q hD hℓN) ℤ
          (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) y)) := by
  have hℓD := not_dvd_D_of_T d M p q hD hℓN
  have hℓM := not_dvd_M_of_T M p q hℓN
  have hℓp := ne_p_of_T M p q hℓN
  have hpN : ℓ ∉ (M * p ^ s).primeFactors := by
    intro h
    obtain ⟨-, hd, -⟩ := Nat.mem_primeFactors.1 h
    rcases (Fact.out : ℓ.Prime).dvd_mul.1 hd with h1 | h1
    · exact hℓM h1
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).1
        ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h1))
  have hinv : IsInvariantAt d ℓ hℓD (d.Utower M p s hN) :=
    isInvariantAt_levelAt (hp := hℓD) (K := fun ℓ _ e => Langlandscape.Local.K1 ℓ e) (hN := hN) hpN
  exact Tl_adjoint d (d.Utower M p s hN) ℓ hℓD ℤ hinv _
    (relIndex_elemT_inv_ne_zero_Utower (hN := hN) d ℓ hℓD hℓM hℓp) x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(U_q)^* = Π_q^{-1}` for the Brandt pairing on `ℤ[X_B(U_s)]`
(`Π_q^* = Π_q^{-1}`, stage 01 `PiEll_adjoint`; `U_s` is maximal at `q ∣ D`). -/
theorem theta_adjoint_Uq (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ
        (thetaZX d M p q s hN hp hM hpM hD Pq hPq .Uq x) y =
      brandtPairing (d.Utower M p s hN) ℤ x (PiEllHom ℤ d q hPq.dvd Pq⁻¹ (d.Utower M p s hN) y) :=
  PiEll_adjoint (d := d) (ℓ := q) (R := ℤ) hPq.dvd (isMaximalAt_Utower hPq.dvd) Pq x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(T_ℓ)^*` on `degZero`, the restriction of `theta_adjoint_T`. -/
theorem theta_adjoint_T_degZero (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ M * p * q)
    (x y : degZero (d.Utower M p s hN) ℤ) :
    brandtPairingDeg (d.Utower M p s hN) ℤ
        (theta d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) x) y =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ)
        (SlInvHom d (d.Utower M p s hN) ℓ (not_dvd_D_of_T d M p q hD hℓN) ℤ
          (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.T ℓ Fact.out hℓN) (y : ZX (d.Utower M p s hN) ℤ))) :=
  theta_adjoint_T d M p q s hN hp hM hpM hD Pq hPq ℓ hℓN x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): `θ(U_q)^* = Π_q^{-1}` on `degZero`, the restriction of
`theta_adjoint_Uq`. -/
theorem theta_adjoint_Uq_degZero (x y : degZero (d.Utower M p s hN) ℤ) :
    brandtPairingDeg (d.Utower M p s hN) ℤ
        (theta d M p q s hN hp hM hpM hD Pq hPq .Uq x) y =
      brandtPairing (d.Utower M p s hN) ℤ (x : ZX (d.Utower M p s hN) ℤ)
        (PiEllHom ℤ d q hPq.dvd Pq⁻¹ (d.Utower M p s hN) (y : ZX (d.Utower M p s hN) ℤ)) :=
  theta_adjoint_Uq d M p q s hN hp hM hpM hD Pq hPq x y

/-- `lem:s05-consistency`(b) (`s05-consistency`): at `s = 0`, `θ(T_p)^* = S_p^{-1} θ(T_p)` (`T_p^Ros = ⟨p⟩⁻¹ T_p`)
for the Brandt pairing on `ℤ[X_B(U_0)]`, from stage 01 `Tl_adjoint` at `ℓ = p` (`p ∤ M p^0`). -/
theorem theta_adjoint_Tp (hs : s = 0) (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.Tp hs) x) y =
      brandtPairing (d.Utower M p s hN) ℤ x
        (SlInvHom d (d.Utower M p s hN) p hp ℤ (thetaZX d M p q s hN hp hM hpM hD Pq hPq (.Tp hs) y)) := by
  have hpN : ¬ p ∣ M * p ^ s := not_dvd_of_s_eq_zero M p s hpM hs
  have hinv : IsInvariantAt d p hp (d.Utower M p s hN) :=
    isInvariantAt_levelAt (hp := hp) (K := fun ℓ _ e => Langlandscape.Local.K1 ℓ e) (hN := hN)
      (notMem_primeFactors_of_not_dvd_aux p hpN)
  exact Tl_adjoint d (d.Utower M p s hN) p hp ℤ hinv _
    (relIndex_elemT_inv_ne_zero_U1 d p hp (N := M * p ^ s) (hN := hN) hpN) x y

end Adjoint

section DiaAdjoint

variable (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D)

/-- `lem:s05-consistency`(b) (`s05-consistency`): the adjoint of a local factor `⟨t_ℓ⟩` of the product diamond
`diaZX` is the local factor at the inverse unit, `⟨t⟩^* = ⟨t⁻¹⟩` (stage 01 `diamond_adjoint`). -/
theorem theta_adjoint_diaLocal (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∈ (M * p ^ s).primeFactors)
    (u : (ZMod (M * p ^ s))ˣ) (x y : ZX (d.Utower M p s hN) ℤ) :
    brandtPairing (d.Utower M p s hN) ℤ (diaLocal d M p s hN ℤ ℓ hℓ u x) y =
      brandtPairing (d.Utower M p s hN) ℤ x
        (heckeTHom (d.Utower M p s hN)
          (diamondElt d ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)⁻¹)
          ℤ (relIndex_ne_zero_of_normalizing _ _
            (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ
              (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)⁻¹)) y) :=
  diamond_adjoint d (d.Utower M p s hN) ℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ) ℤ
    (localUnit ℓ (Nat.dvd_of_mem_primeFactors hℓ) u)
    (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ _)
    (diamondElt_inv_normalizes_U1 (N := M * p ^ s) (hN := hN) hℓ _) x y

end DiaAdjoint

/-! ### (c) The projection formula -/

section Projection

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `lem:s05-consistency`(c) (`s05-consistency`): the pullback `π^* : R[X_B(U)] → R[X_B(U')]`,
`(π^* b)(c') = b(π c')`. -/
def pullbackZX [Finite (XB U')] : ZX U R →ₗ[R] ZX U' R where
  toFun b := Finsupp.equivFunOnFinite.symm (fun c' => b (levelMap U' U c'))
  map_add' b b' := by
    ext c'
    simp [Finsupp.coe_equivFunOnFinite_symm]
  map_smul' r b := by
    ext c'
    simp [Finsupp.coe_equivFunOnFinite_symm]

variable {U' U R}

/-- `lem:s05-consistency`(c) (`s05-consistency`): `(π^* b)(c') = b(π c')`. -/
@[simp] theorem pullbackZX_apply [Finite (XB U')] (b : ZX U R) (c' : XB U') :
    pullbackZX U' U R b c' = b (levelMap U' U c') :=
  rfl

/-- `lem:s05-consistency`(c) (`s05-consistency`): the projection formula
`⟨π_* a, b⟩_U = ⟨a, π^* b⟩_{U'}` when the weights agree, `w_{c'} = w_{π c'}`. -/
theorem projection_formula [Finite (XB U')]
    (hw : ∀ c' : XB U', wx U' (Quotient.out c') = wx U (Quotient.out (levelMap U' U c')))
    (x : ZX U' R) (y : ZX U R) :
    brandtPairing U R (pushforward U' U R x) y = brandtPairing U' R x (pullbackZX U' U R y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | single c' r =>
    rw [pushforward_single, brandtPairing_single_left, brandtPairing_single_left, pullbackZX_apply,
      hw c']

/-- `lem:s05-consistency`(c) (`s05-consistency`): the projection formula when all weights are `1` (then
`π^!_w = π^*`). At the tower levels `U_s`, `s ≥ 1`, the hypotheses hold for `p ≥ 5` by `Ordinary.wx_Utower_eq_one`
(premises `¬ p ∣ D`, `5 ≤ p`, `M ≠ 0`, `1 ≤ s`); no instance at `d.Utower` is stated here. -/
theorem projection_formula_of_wx_one [Finite (XB U')] (hw1 : ∀ x, wx U x = 1) (hw1' : ∀ x, wx U' x = 1)
    (x : ZX U' R) (y : ZX U R) :
    brandtPairing U R (pushforward U' U R x) y = brandtPairing U' R x (pullbackZX U' U R y) :=
  projection_formula (R := R) (fun c' => (hw1' _).trans (hw1 _).symm) x y

variable (U' U R)

/-- `lem:s05-consistency`(c) (`s05-consistency`): the trace form of the projection formula,
`⟨π_* a, b⟩_U = ev(b, tr(ν' a))`, i.e. `ν ∘ π_* = tr ∘ ν'` paired with `b`, if `-1 ∈ U'` or `-1 ∉ U`
(stage 01 `normMap_pushforward`). `π^!_w` and `π^!` are not defined in Lean. -/
theorem projection_formula_trace [Finite (XB U)] (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (hneg : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U' ∨ (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U)
    (x : ZX U' R) (y : ZX U R) :
    brandtPairing U R (pushforward U' U R x) y =
      evalPairing U R y (trace U' U R hrel (normMap U' R x)) := by
  rw [brandtPairing_eq_evalPairing_normMap (U := U) (R := R),
    normMap_pushforward (U' := U') (U := U) (R := R) (hrel := hrel) hle hneg x]

/-- `lem:s05-consistency`(c) (`s05-consistency`): the projection formula with the factor 2 of `rem:s05-factor2`:
if `-1 ∈ U ∖ U'` then `2 ⟨π_* a, b⟩_U = ev(b, tr(ν' a))`, i.e. `tr ∘ ν' = 2 ν ∘ π_*` paired with `b`
(stage 01 `normMap_pushforward_two`); in the tex this is `π^!_w = ½ π^!` (`π^!_w`, `π^!` not defined in Lean). -/
theorem projection_formula_two [Finite (XB U)] (hle : U' ≤ U) (hrel : U'.relIndex U ≠ 0)
    (h1 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∈ U) (h2 : (negOne : (GL2TF.Quat.BHat a b)ˣ) ∉ U')
    (x : ZX U' R) (y : ZX U R) :
    (2 : R) * brandtPairing U R (pushforward U' U R x) y =
      evalPairing U R y (trace U' U R hrel (normMap U' R x)) := by
  rw [normMap_pushforward_two (U' := U') (U := U) (R := R) (hrel := hrel) hle h1 h2 x, map_smul,
    smul_eq_mul, brandtPairing_eq_evalPairing_normMap (U := U) (R := R)]

end Projection

/-! ### (d) `π_*` commutes with `U_p` on `degZero` -/

section PushDeg

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `lem:s05-consistency`(d) (`s05-consistency`): `π_*` preserves the degree, `deg (π_* x) = deg x`. -/
theorem deg_pushforward (x : ZX U' R) :
    Ordinary.deg (XB U) R (pushforward U' U R x) = Ordinary.deg (XB U') R x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single c r => rw [pushforward_single]; simp

/-- `lem:s05-consistency`(d) (`s05-consistency`): the pushforward `π_*` restricted to `degZero`. -/
def pushDegZero : degZero U' R →ₗ[R] degZero U R :=
  (pushforward U' U R).restrict (fun x hx => by
    rw [mem_degZero] at hx ⊢
    rw [deg_pushforward, hx])

/-- `lem:s05-consistency`(d) (`s05-consistency`): `pushDegZero` acts as `π_*`. -/
@[simp] theorem pushDegZero_apply (x : degZero U' R) :
    ((pushDegZero U' U R x : degZero U R) : ZX U R) = pushforward U' U R (x : ZX U' R) :=
  rfl

end PushDeg

section UpComm

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hN' : (M * p ^ (s + 1)).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `lem:s05-consistency`(d) (`s05-consistency`): `π_* ∘ θ(U_p) = θ(U_p) ∘ π_*` on `degZero`, `s ≥ 1`
(`θ(U_p) = N_{U_p}`; stage 01 `Up_comm_push`, `towerPush_eq_pushforward`).  The finiteness hypotheses of
`Up_comm_push` are discharged by `finite_XB_Utower`. -/
theorem Up_comm_pushforward_degZero (hs : 1 ≤ s) :
    pushDegZero (d.Utower M p (s + 1) hN') (d.Utower M p s hN) ℤ ∘ₗ
        theta d M p q (s + 1) hN' hp hM hpM hD Pq hPq (.Up (Nat.le_add_left 1 s)) =
      theta d M p q s hN hp hM hpM hD Pq hPq (.Up hs) ∘ₗ
        pushDegZero (d.Utower M p (s + 1) hN') (d.Utower M p s hN) ℤ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun
    (Up_comm_push (d := d) (M := M) (p := p) (s := s) (hN := hN) (hN' := hN') (hp := hp) (R := ℤ)
      hM hpM hs) (x : ZX (d.Utower M p (s + 1) hN') ℤ)
  exact h

end UpComm

end

end Langlandscape.Comparison
