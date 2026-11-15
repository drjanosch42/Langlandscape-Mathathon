/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.HypXGal
import Langlandscape.Comparison.ThetaAdj
import Langlandscape.Brandt.ImportDictionary
import Langlandscape.Brandt.Adjoint
import Langlandscape.Quat.LevelFinite
import Langlandscape.Quat.Stab
import Langlandscape.Quat.Weights
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.ZMod.Basic

/-!
# Non-vacuity instances for `Hyp.X.char`, `Hyp.X.gal`, `Hyp.X.iso` (S05-L4)

`mathematics/chapters/s05/hypX.tex`, `hyp:s05-X` (tex risk R6, vacuity), `def:s05-Xiso`.

* `canonicalCharData` : the canonical `CharGroupData`: `X s := ℤ[S_s]⁰` (`degZero`), `act := theta`,
  `u := brandtPairing` (restricted to `degZero`), `β := pushforward` (restricted to `degZero`).
  `canonicalCharData_char : Hyp.X.char … canonicalCharData` (witness `φ = phiId`, the identity).
  As recorded in `Hyp.X.char`'s docstring: on this `G` the statement holds *by fiat*; the point of the
  instance is that the structure `CharGroupData` and the statement `Hyp.X.char` are satisfiable
  (positivity of the weights, finiteness, freeness and `degZero`-stability are real checks).
* `toyTate`, `toyTate_gal` : `Hyp.X.gal … canonicalCharData phiId toyTate` **for all `s`**, the direct-sum
  model `T s := top ⊕ bottom` with `top = ℤ_[p] ⊗ ℤ[S_s]⁰` and `bottom = Hom(top, ℤ_[p])`, middle piece
  `0` (so the summand `0` is omitted). It is built from `ToyTateData`, which collects exactly the three
  Hecke-theoretic facts the toy needs and that are *not* in the library as one statement (and not proved
  here): (i) every `θ_s(h)` has a `⟨,⟩_w`-adjoint on `ℤ[S_s]⁰` (integral adjointness,
  `prop:s01-adjoint`, `s05-X`), (ii) `θ_s(U_q) = Π_q` is bijective, (iii) `θ_s(U_q)` commutes with all
  `θ_s(h)`. All three are true (`Π_q` is a permutation of `X_B(U_s)`; Hecke operators at distinct
  places commute); the clauses of `Hyp.X.gal` *force* them (the Frobenius on the bottom piece is
  `q θ(U_q)ᵀ` and must be an automorphism commuting with the Hecke action), so they cannot be avoided.
  `toyTate_gal` is the statement conditional on a given `D : ToyTateData`; `canonicalToyTateData` discharges
  `ToyTateData` from S05-L4g (`Comparison/ThetaAdj.lean`: `thetaAdj`, `thetaAdj_spec`, `thetaUqEquiv`,
  `theta_comm_Uq`), and `toyTate_gal_uncond` is the resulting unconditional instance (no `False` hypotheses,
  nothing empty).
* `toyXIso_holds` : a toy `Hyp.X.iso` instance (`T = ℤ`, `𝔞 = (5)`, `L = H = ℤ/5`).

**Context caveat.** All instances below are theorems quantified over the context
`(d, M, p, q, hN, hp, hM, hpM, hD : d.D = q, Pq, hPq : IsUniformiserElt d q Pq)`. No closed Lean term inhabits this
context yet: the only `DefiniteData` in the tree is `hurwitzData` (`LanglandscapeTests/S01`), and there is no
`IsUniformiserElt` witness. So "non-vacuous" means "for every admissible context"; that the context is inhabited
(e.g. `hurwitzData`, `q = 2`, `p`, `M` odd, `Pq` the image of `1 + i`, `Nrd = 2`) is true mathematically but not
formalized.

Status: *formalized* (`toyTate_gal_uncond` unconditional, relative to the context above). Test file: not a `module`,
since it imports files that depend on GL2TF.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace LanglandscapeTests.Hyp.S05

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Comparison

/-! ### Weights, pairing, degree -/

section Basic

/-- `hyp:s05-X` (X2) (`s05-X`): the weights `w_x` at the tower levels `U_1(M p^s)` are positive
(`|Γ_x(U)|` divides `24`, so it is finite and nonzero). -/
theorem wx_Utower_pos (d : DefiniteData) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : 0 < wx (d.Utower M p s hN) x := by
  have hU : d.Utower M p s hN ≤ d.Ohat := DefiniteData.U1_le_units (d := d) (M * p ^ s) hN
  have hdvd := card_Gam_dvd_24 d.ha d.hb d.O.1 hU x
  have hpos : 0 < Nat.card (Gam (d.Utower M p s hN) x) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  haveI : Finite (Gam (d.Utower M p s hN) x) := Nat.finite_of_card_ne_zero hpos.ne'
  haveI : Finite ↥(Gam (d.Utower M p s hN) x ⊓ pmOne) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hle : Nat.card ↥(Gam (d.Utower M p s hN) x ⊓ pmOne) ≤ Nat.card (Gam (d.Utower M p s hN) x) :=
    Nat.le_of_dvd hpos (Subgroup.card_dvd_of_le inf_le_left)
  unfold wx
  exact Nat.div_pos hle Nat.card_pos

/-- `hyp:s05-X` (X2) (`s05-X`): the Brandt pairing is symmetric (finite `X_B(U)`). -/
theorem brandtPairing_comm_of_finite {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) [Finite (XB U)]
    (x y : ZX U ℤ) : brandtPairing U ℤ x y = brandtPairing U ℤ y x := by
  haveI := Fintype.ofFinite (XB U)
  rw [brandtPairing_eq_sum, brandtPairing_eq_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `hyp:s05-X` (X2) (`s05-X`): the Brandt pairing is positive definite when all weights are positive
(finite `X_B(U)`). -/
theorem brandtPairing_self_pos {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) [Finite (XB U)]
    (hw : ∀ x, 0 < wx U x) (x : ZX U ℤ) (hx : x ≠ 0) : 0 < brandtPairing U ℤ x x := by
  haveI := Fintype.ofFinite (XB U)
  rw [brandtPairing_eq_sum]
  obtain ⟨c, hc⟩ : ∃ c, x c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx (Finsupp.ext fun c => by simpa using hcon c)
  have hterm : ∀ c' : XB U, 0 ≤ x c' * (wx U (Quotient.out c') : ℤ) * x c' := fun c' => by
    have h1 : (0 : ℤ) ≤ (wx U (Quotient.out c') : ℤ) := by positivity
    have e : x c' * (wx U (Quotient.out c') : ℤ) * x c' =
        (wx U (Quotient.out c') : ℤ) * (x c' * x c') := by ring
    rw [e]
    exact mul_nonneg h1 (mul_self_nonneg _)
  refine Finset.sum_pos' (fun c' _ => hterm c') ⟨c, Finset.mem_univ c, ?_⟩
  have h1 : (0 : ℤ) < (wx U (Quotient.out c) : ℤ) := by exact_mod_cast hw _
  have e : x c * (wx U (Quotient.out c) : ℤ) * x c = (wx U (Quotient.out c) : ℤ) * (x c * x c) := by
    ring
  rw [e]
  exact mul_pos h1 (mul_self_pos.2 hc)

/-- `hyp:s05-X` (X3) (`s05-X`): `π_*` preserves the degree. -/
theorem deg_pushforward {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (x : ZX U' ℤ) :
    Langlandscape.Ordinary.deg (XB U) ℤ (pushforward U' U ℤ x) =
      Langlandscape.Ordinary.deg (XB U') ℤ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single c r =>
    rw [pushforward_single, Langlandscape.Ordinary.deg_single, Langlandscape.Ordinary.deg_single]

/-- `hyp:s05-X` (X3) (`s05-X`): the pushforward `π_* : ℤ[S_{s'}]⁰ → ℤ[S_s]⁰`, the restriction of
`pushforward` to `degZero`. -/
noncomputable def pushforwardDegZero {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) :
    degZero U' ℤ →ₗ[ℤ] degZero U ℤ :=
  (pushforward U' U ℤ).restrict (fun x hx => by
    rw [mem_degZero] at hx ⊢
    rw [deg_pushforward, hx])

/-- `hyp:s05-X` (X1) (`s05-X`): `ℤ[X_B(U)]⁰` is free and finitely generated over `ℤ` when `X_B(U)` is finite
(submodule of a free module over a PID). -/
theorem degZero_free_finite {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) [Finite (XB U)] :
    Module.Free ℤ (degZero U ℤ) ∧ Module.Finite ℤ (degZero U ℤ) := by
  obtain ⟨n, bs⟩ := Submodule.basisOfPid Finsupp.basisSingleOne (degZero U ℤ)
  exact ⟨Module.Free.of_basis bs, Module.Finite.of_basis bs⟩

/-- `hyp:s05-X` (X4) (`s05-X`), helper: transfer of an adjointness identity from `ℤ[S]⁰` to `ℤ_p ⊗ ℤ[S]⁰`
for the base change of the Brandt pairing. -/
theorem wPairingZp_adjoint (p : ℕ) [Fact p.Prime] {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (f g : Module.End ℤ (degZero U ℤ))
    (hfg : ∀ x y : degZero U ℤ, brandtPairing U ℤ (f x).1 y.1 = brandtPairing U ℤ x.1 (g y).1)
    (t z : ℤ_[p] ⊗[ℤ] degZero U ℤ) :
    Langlandscape.Hyp.X.wPairingZp p U (LinearMap.baseChange ℤ_[p] f t) z =
      Langlandscape.Hyp.X.wPairingZp p U t (LinearMap.baseChange ℤ_[p] g z) := by
  unfold Langlandscape.Hyp.X.wPairingZp
  induction t with
  | tmul a x =>
    induction z with
    | tmul b y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul]
      congr 1
      exact hfg x y
    | add z1 z2 h1 h2 => simp only [map_add, h1, h2]
  | add t1 t2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]

/-- `hyp:s05-X` (X4) (`s05-X`): `q` is a unit in `ℤ_[p]`, since `p ∤ q` (from `p ∤ D`, `D = q`). -/
theorem isUnit_q_of_not_dvd (p q : ℕ) [Fact p.Prime] (n : ℕ) (hp : ¬ p ∣ n) (hD : n = q) :
    IsUnit (q : ℤ_[p]) := by
  rw [hD] at hp
  exact PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hp))

end Basic

/-! ### The canonical `CharGroupData` and `Hyp.X.char` -/

section Canonical

variable (d : DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
  (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `hyp:s05-X` (`s05-X`), non-vacuity (S05-L4, tex R6): the canonical character-group datum,
`X s := ℤ[S_s]⁰`, `act := θ_s` (`theta`), `u := ⟨,⟩_w` (`brandtPairing`, restricted), `β := π_*`
(`pushforward`, restricted). -/
noncomputable def canonicalCharData : Langlandscape.Hyp.X.CharGroupData M q p where
  X s := degZero (d.Utower M p s (hN s)) ℤ
  addCommGroup s := inferInstance
  free s := by
    haveI : Finite (XB (d.Utower M p s (hN s))) := d.finite_XB_U1 _ (hN s)
    exact (degZero_free_finite _).1
  finite s := by
    haveI : Finite (XB (d.Utower M p s (hN s))) := d.finite_XB_U1 _ (hN s)
    exact (degZero_free_finite _).2
  act s := theta d M p q s (hN s) hp hM hpM hD Pq hPq
  u s := (brandtPairing (d.Utower M p s (hN s)) ℤ).compl₁₂ (degZero (d.Utower M p s (hN s)) ℤ).subtype
    (degZero (d.Utower M p s (hN s)) ℤ).subtype
  u_symm s x y := by
    haveI : Finite (XB (d.Utower M p s (hN s))) := d.finite_XB_U1 _ (hN s)
    exact brandtPairing_comm_of_finite _ x.1 y.1
  u_pos s x hx := by
    haveI : Finite (XB (d.Utower M p s (hN s))) := d.finite_XB_U1 _ (hN s)
    exact brandtPairing_self_pos _ (wx_Utower_pos d M p s (hN s)) x.1 (fun h => hx (Subtype.ext h))
  β := @fun s s' _ => pushforwardDegZero (d.Utower M p s' (hN s')) (d.Utower M p s (hN s))

/-- `hyp:s05-X` (`s05-X`), non-vacuity (S05-L4): the identity family `φ_s = id : G.X s ≃ ℤ[S_s]⁰` for
`G = canonicalCharData` (`G.X s` is `ℤ[S_s]⁰` by definition). -/
noncomputable def phiId (s : ℕ) :
    (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ :=
  LinearEquiv.refl ℤ _

/-- `hyp:s05-X` (X1)–(X3) (`s05-X`), non-vacuity (S05-L4, tex R6): `Hyp.X.char` holds for
`canonicalCharData` with the witness `φ = phiId`; all three clauses are definitional. On this `G` the statement
holds by construction (all clauses `rfl`); see the `Hyp.X.char` docstring. -/
theorem canonicalCharData_char :
    Langlandscape.Hyp.X.char d M p q hN hp hM hpM hD Pq hPq
      (canonicalCharData d M p q hN hp hM hpM hD Pq hPq) :=
  ⟨phiId d M p q hN hp hM hpM hD Pq hPq, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- `hyp:s05-X` (X4) (`s05-X`): the base change of `phiId` is the identity (hint of S05-L3: `baseChange_id`,
`φ = refl`). -/
theorem baseChange_phiId_apply (s : ℕ) (t : ℤ_[p] ⊗[ℤ] (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).X s) :
    LinearMap.baseChange ℤ_[p] (phiId d M p q hN hp hM hpM hD Pq hPq s).toLinearMap t = t := by
  induction t with
  | tmul a x => rfl
  | add t1 t2 h1 h2 => rw [map_add, h1, h2] <;> rfl

/-- `hyp:s05-X` (X4) (`s05-X`): the dual of the base change of `phiId` is the identity. -/
theorem dualMap_baseChange_phiId (s : ℕ) :
    LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (phiId d M p q hN hp hM hpM hD Pq hPq s).toLinearMap) =
      LinearMap.id :=
  LinearMap.ext fun g => LinearMap.ext fun t => by
    rw [LinearMap.dualMap_apply, baseChange_phiId_apply]
    rfl

end Canonical

/-! ### The toy Tate module (direct-sum model) -/

section Toy

variable (d : DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
  (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `hyp:s05-X` (X4) (`s05-X`), shorthand: `θ_s(h)` as an endomorphism of `ℤ[S_s]⁰`. -/
noncomputable abbrev thetaS (s : ℕ) (h : HeckeSym M p q s) :
    Module.End ℤ (degZero (d.Utower M p s (hN s)) ℤ) :=
  theta d M p q s (hN s) hp hM hpM hD Pq hPq h

/-- `hyp:s05-X` (X4) (`s05-X`), shorthand: the top piece `ℤ_p ⊗ ℤ[S_s]⁰ = ℤ_p ⊗ G.X s` of the toy Tate module,
`G = canonicalCharData`. -/
abbrev topPiece (s : ℕ) : Type :=
  ℤ_[p] ⊗[ℤ] (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).X s

local notation "θS" => thetaS d M p q hN hp hM hpM hD Pq hPq
local notation "Atop" => topPiece d M p q hN hp hM hpM hD Pq hPq

/-- `hyp:s05-X` (X4) (`s05-X`), non-vacuity (S05-L4): the Hecke-theoretic input of the toy Tate module,
three true facts about `θ_s` that `Hyp.X.gal` forces and that are not in the library as such:
* `adj s h` is the `⟨,⟩_w`-adjoint `θ_s(h)^*` of `θ_s(h)` on `ℤ[S_s]⁰` (`⟨θ(h)^* x, y⟩ = ⟨x, θ(h) y⟩`;
  integral adjointness, `prop:s01-adjoint`: `T_ℓ^* = S_ℓ⁻¹ T_ℓ`, `U_p^*`, `⟨u⟩^* = ⟨u⟩⁻¹`, `Π_q^* = Π_q⁻¹`);
* `uqEquiv s` : `θ_s(U_q) = +Π_q` is bijective (a permutation of `X_B(U_s)`);
* `comm`: `θ_s(U_q)` commutes with every `θ_s(h)` (Hecke operators at distinct places commute).
Not proved in this file; `canonicalToyTateData` constructs it from S05-L4g (`Comparison/ThetaAdj.lean`). -/
structure ToyTateData : Type where
  /-- The adjoint `θ_s(h)^*`. -/
  adj : ∀ s, HeckeSym M p q s → Module.End ℤ (degZero (d.Utower M p s (hN s)) ℤ)
  /-- `⟨θ_s(h)^* x, y⟩_w = ⟨x, θ_s(h) y⟩_w`. -/
  adj_spec : ∀ s (h : HeckeSym M p q s) (x y : degZero (d.Utower M p s (hN s)) ℤ),
    brandtPairing (d.Utower M p s (hN s)) ℤ (adj s h x).1 y.1 =
      brandtPairing (d.Utower M p s (hN s)) ℤ x.1 (θS s h y).1
  /-- `θ_s(U_q)` as an automorphism of `ℤ[S_s]⁰`. -/
  uqEquiv : ∀ s, degZero (d.Utower M p s (hN s)) ℤ ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ
  /-- `uqEquiv s` is `θ_s(U_q)`. -/
  uqEquiv_spec : ∀ s, (uqEquiv s).toLinearMap = θS s HeckeSym.Uq
  /-- `θ_s(U_q)` commutes with `θ_s(h)`. -/
  comm : ∀ s (h : HeckeSym M p q s), θS s HeckeSym.Uq ∘ₗ θS s h = θS s h ∘ₗ θS s HeckeSym.Uq

variable (D : ToyTateData d M p q hN hp hM hpM hD Pq hPq)

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the Hecke action on `T s = top ⊕ bottom`: the adjoint `θ(h)^*` on the
top piece (Rosati-twisted action), the transpose `θ(h)ᵀ` on the bottom piece. -/
noncomputable def toyAct (s : ℕ) (h : HeckeSym M p q s) :
    Module.End ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s)) :=
  (LinearMap.baseChange ℤ_[p] (D.adj s h)).prodMap
    (LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (θS s h)))

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the Frobenius on the bottom piece, `q • θ(U_q)ᵀ` (FD1, decided). -/
noncomputable def toyFrobBotMap (s : ℕ) :
    Module.Dual ℤ_[p] (Atop s) →ₗ[ℤ_[p]] Module.Dual ℤ_[p] (Atop s) :=
  (q : ℤ_[p]) • LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq))

include D in
/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the Frobenius on the bottom piece is bijective (`q` a unit,
`θ(U_q)` bijective). -/
theorem toyFrobBotMap_bijective (s : ℕ) : Function.Bijective (toyFrobBotMap d M p q hN hp hM hpM hD Pq hPq s) := by
  obtain ⟨u, hu⟩ := isUnit_q_of_not_dvd p q d.D hp hD
  let eb : Atop s ≃ₗ[ℤ_[p]] Atop s := (D.uqEquiv s).baseChange ℤ ℤ_[p] _ _
  have hF : LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) = eb.toLinearMap := by
    rw [← D.uqEquiv_spec s]
    rfl
  have h1 : Function.Bijective (LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq))) := by
    rw [hF]
    exact eb.dualMap.bijective
  have h2 : Function.Bijective (fun g : Module.Dual ℤ_[p] (Atop s) => (q : ℤ_[p]) • g) := by
    rw [← hu]
    exact MulAction.bijective u
  exact h2.comp h1

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the arithmetic Frobenius `Frob_q = id ⊕ (q θ(U_q)ᵀ)`. -/
noncomputable def toyFrob (s : ℕ) :
    (Atop s × Module.Dual ℤ_[p] (Atop s)) ≃ₗ[ℤ_[p]] (Atop s × Module.Dual ℤ_[p] (Atop s)) :=
  (LinearEquiv.refl ℤ_[p] (Atop s)).prodCongr
    (LinearEquiv.ofBijective (toyFrobBotMap d M p q hN hp hM hpM hD Pq hPq s)
      (toyFrobBotMap_bijective d M p q hN hp hM hpM hD Pq hPq D s))

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the monodromy operator `N t = ⟨π_top t, ·⟩_w` into the bottom piece. -/
noncomputable def toyN (s : ℕ) : Module.End ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s)) :=
  (LinearMap.inr ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s))) ∘ₗ
    (Langlandscape.Hyp.X.wPairingZp p (d.Utower M p s (hN s))) ∘ₗ
    (LinearMap.fst ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s)))

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: `toyAct` commutes with `toyFrob` (by commutation of `θ(U_q)`
with `θ(h)`). -/
theorem toyAct_comm_toyFrob (s : ℕ) (h : HeckeSym M p q s) :
    toyAct d M p q hN hp hM hpM hD Pq hPq D s h ∘ₗ (toyFrob d M p q hN hp hM hpM hD Pq hPq D s).toLinearMap =
      (toyFrob d M p q hN hp hM hpM hD Pq hPq D s).toLinearMap ∘ₗ toyAct d M p q hN hp hM hpM hD Pq hPq D s h := by
  have hc : LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) ∘ₗ LinearMap.baseChange ℤ_[p] (θS s h) =
      LinearMap.baseChange ℤ_[p] (θS s h) ∘ₗ LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, D.comm s h]
  refine LinearMap.ext fun t => Prod.ext rfl ?_
  refine LinearMap.ext fun x => ?_
  show (q : ℤ_[p]) • t.2 (LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) (LinearMap.baseChange ℤ_[p] (θS s h) x)) =
    (q : ℤ_[p]) • t.2 (LinearMap.baseChange ℤ_[p] (θS s h) (LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) x))
  have hx : LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) (LinearMap.baseChange ℤ_[p] (θS s h) x) =
      LinearMap.baseChange ℤ_[p] (θS s h) (LinearMap.baseChange ℤ_[p] (θS s HeckeSym.Uq) x) :=
    LinearMap.congr_fun hc x
  rw [hx]

/-- `hyp:s05-X` (X4) (`s05-X`), toy model: the tame relation `Frob τ Frob⁻¹ = τ ^ q` for `τ = id`. -/
theorem toyFrob_tau (s : ℕ) :
    (toyFrob d M p q hN hp hM hpM hD Pq hPq D s).toLinearMap ∘ₗ
        (LinearEquiv.refl ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s))).toLinearMap ∘ₗ
        (toyFrob d M p q hN hp hM hpM hD Pq hPq D s).symm.toLinearMap =
      ((LinearEquiv.refl ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s))).toLinearMap :
        Module.End ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s))) ^ q := by
  have h1 : ((LinearEquiv.refl ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s))).toLinearMap :
      Module.End ℤ_[p] (Atop s × Module.Dual ℤ_[p] (Atop s))) = 1 := rfl
  rw [h1, one_pow]
  exact LinearMap.ext fun x => (toyFrob d M p q hN hp hM hpM hD Pq hPq D s).apply_symm_apply x

/-- `hyp:s05-X` (X4) (`s05-X`), non-vacuity (S05-L4): the toy Tate module `T s = top ⊕ bottom` with
`top = ℤ_p ⊗ ℤ[S_s]⁰`, `bottom = Hom(top, ℤ_p)`, middle piece `0` (the summand is omitted), `τ = id` (not tied to
`N`; `gal` does not use `tau`), `Frob = id ⊕ q θ(U_q)ᵀ` (`id` on the top piece), `T_t = bottom`, and
`TI := ker (T → top) = bottom` (as `gal` requires; this is not the `τ`-invariants, which are all of `T` here). -/
noncomputable def toyTate : Langlandscape.Hyp.X.TateModuleData M q p where
  T s := Atop s × Module.Dual ℤ_[p] (Atop s)
  addCommGroup s := inferInstance
  module s := inferInstance
  free s := by
    haveI := (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).free s
    haveI := (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).finite s
    infer_instance
  finite s := by
    haveI := (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).free s
    haveI := (canonicalCharData d M p q hN hp hM hpM hD Pq hPq).finite s
    infer_instance
  frob s := toyFrob d M p q hN hp hM hpM hD Pq hPq D s
  tau s := LinearEquiv.refl ℤ_[p] _
  frob_tau s := toyFrob_tau d M p q hN hp hM hpM hD Pq hPq D s
  act s h := toyAct d M p q hN hp hM hpM hD Pq hPq D s h
  act_frob s h := toyAct_comm_toyFrob d M p q hN hp hM hpM hD Pq hPq D s h
  act_tau s h := LinearMap.ext fun _ => rfl
  Tt s := LinearMap.range (LinearMap.inr ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s)))
  TI s := LinearMap.ker (LinearMap.fst ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s)))
  Tt_le_TI s := by
    rintro _ ⟨f, rfl⟩
    exact LinearMap.mem_ker.2 rfl
  N s := toyN d M p q hN hp hM hpM hD Pq hPq s

/-- `hyp:s05-X` (X4) (`s05-X`), non-vacuity (S05-L4): `Hyp.X.gal` holds **for all `s`** for the data
`canonicalCharData`, the family `phiId` and the direct-sum toy Tate module `toyTate`
(witnesses `πX = fst`, `ιX = inr`), given `D : ToyTateData` (integral Hecke adjoints, bijectivity of `Π_q`,
commutation; see `ToyTateData`). The FD1 clause is witnessed with `Frob = q θ(U_q)ᵀ` on the bottom piece.
See `toyTate_gal_uncond` for the unconditional form. -/
theorem toyTate_gal :
    Langlandscape.Hyp.X.gal d M p q hN hp hM hpM hD Pq hPq
      (canonicalCharData d M p q hN hp hM hpM hD Pq hPq) (phiId d M p q hN hp hM hpM hD Pq hPq)
      (toyTate d M p q hN hp hM hpM hD Pq hPq D) := by
  intro s
  refine ⟨LinearMap.fst ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s)),
    LinearMap.inr ℤ_[p] (Atop s) (Module.Dual ℤ_[p] (Atop s)), ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact fun a => ⟨(a, 0), rfl⟩
  · exact LinearMap.inr_injective
  · -- top: `πTop ∘ h = θ(h)* ∘ πTop`
    intro h t z
    have key : ∀ t1 : Atop s,
        Langlandscape.Hyp.X.wPairingZp p (d.Utower M p s (hN s))
          (LinearMap.baseChange ℤ_[p] (phiId d M p q hN hp hM hpM hD Pq hPq s).toLinearMap
            (LinearMap.baseChange ℤ_[p] (D.adj s h) t1)) z =
        Langlandscape.Hyp.X.wPairingZp p (d.Utower M p s (hN s))
          (LinearMap.baseChange ℤ_[p] (phiId d M p q hN hp hM hpM hD Pq hPq s).toLinearMap t1)
          (LinearMap.baseChange ℤ_[p] (θS s h) z) := fun t1 =>
      (congrArg (fun v => Langlandscape.Hyp.X.wPairingZp p (d.Utower M p s (hN s)) v z)
        (baseChange_phiId_apply d M p q hN hp hM hpM hD Pq hPq s
          (LinearMap.baseChange ℤ_[p] (D.adj s h) t1))).trans
      ((wPairingZp_adjoint p _ (D.adj s h) (θS s h) (D.adj_spec s h) t1 z).trans
        (congrArg (fun v => Langlandscape.Hyp.X.wPairingZp p (d.Utower M p s (hN s)) v
            (LinearMap.baseChange ℤ_[p] (θS s h) z))
          (baseChange_phiId_apply d M p q hN hp hM hpM hD Pq hPq s t1).symm))
    exact key (Prod.fst t)
  · -- bottom: `h ∘ ιBot = ιBot ∘ θ(h)ᵀ`
    intro h
    rw [dualMap_baseChange_phiId d M p q hN hp hM hpM hD Pq hPq s]
    refine LinearMap.ext fun f => ?_
    show (LinearMap.baseChange ℤ_[p] (D.adj s h) 0,
        LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (θS s h)) f) =
      ((0 : Atop s), LinearMap.dualMap (LinearMap.baseChange ℤ_[p] (θS s h)) f)
    exact Prod.ext (map_zero _) rfl
  · -- FD1 clause: `Frob = q • θ(U_q)ᵀ` on the bottom piece
    rw [dualMap_baseChange_phiId d M p q hN hp hM hpM hD Pq hPq s]
    exact LinearMap.ext fun f => rfl
  · -- monodromy: `N t = ιBot ⟨πTop t, ·⟩_w`
    intro t
    rw [dualMap_baseChange_phiId d M p q hN hp hM hpM hD Pq hPq s,
      baseChange_phiId_apply d M p q hN hp hM hpM hD Pq hPq s]
    rfl

/-- `hyp:s05-X` (X4) (`s05-X`), non-vacuity (S05-L11c): the toy Hecke data, discharged from S05-L4g
(`Comparison/ThetaAdj.lean`): `adj = thetaAdj`, `adj_spec = thetaAdj_spec`, `uqEquiv = thetaUqEquiv`,
`uqEquiv_spec = thetaUqEquiv_toLinearMap`, `comm = theta_comm_Uq` (`θ_s(U_q) ∘ θ_s(h) = θ_s(h) ∘ θ_s(U_q)`, the same
composition order as the `comm` field). -/
noncomputable def canonicalToyTateData : ToyTateData d M p q hN hp hM hpM hD Pq hPq where
  adj s h := thetaAdj d M p q s (hN s) hp hM hpM hD Pq hPq h
  adj_spec s h x y := thetaAdj_spec d M p q s (hN s) hp hM hpM hD Pq hPq h x y
  uqEquiv s := thetaUqEquiv d M p q s (hN s) hp hM hpM hD Pq hPq
  uqEquiv_spec s := thetaUqEquiv_toLinearMap d M p q s (hN s) hp hM hpM hD Pq hPq
  comm s h := theta_comm_Uq d M p q s (hN s) hp hM hpM hD Pq hPq h

/-- `hyp:s05-X` (X4) (`s05-X`), non-vacuity (S05-L11c): **unconditional** `Hyp.X.gal` for all `s`, for
`canonicalCharData`, `phiId` and the toy Tate module built from `canonicalToyTateData` (S05-L4g). Still
quantified over the context `(d, …, hD, Pq, hPq)`, which is not yet inhabited by a closed Lean term. -/
theorem toyTate_gal_uncond :
    Langlandscape.Hyp.X.gal d M p q hN hp hM hpM hD Pq hPq
      (canonicalCharData d M p q hN hp hM hpM hD Pq hPq) (phiId d M p q hN hp hM hpM hD Pq hPq)
      (toyTate d M p q hN hp hM hpM hD Pq hPq (canonicalToyTateData d M p q hN hp hM hpM hD Pq hPq)) :=
  toyTate_gal d M p q hN hp hM hpM hD Pq hPq (canonicalToyTateData d M p q hN hp hM hpM hD Pq hPq)

end Toy

/-! ### A toy `Hyp.X.iso` -/

/-- `def:s05-Xiso` (`s05-Xiso`), helper: the `𝔞 = (5)`-torsion of `ℤ/5` over `ℤ` is everything. -/
theorem toyXIso_top :
    Submodule.torsionBySet ℤ (ZMod 5) ((Ideal.span {(5 : ℤ)} : Ideal ℤ) : Set ℤ) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  have hdvd : (5 : ℤ) ∣ a := Ideal.mem_span_singleton.1 ha
  show a • x = 0
  rw [zsmul_eq_mul, (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).2 (by exact_mod_cast hdvd), zero_mul]

/-- `def:s05-Xiso` (`s05-Xiso`), non-vacuity (S05-L4): a toy `Hyp.X.iso` instance, `T = ℤ`, `𝔞 = (5)`,
`L = H = ℤ/5ℤ` (`H[𝔞] = H` since `𝔞` kills `H`, so `L ≃ H[𝔞]`). -/
theorem toyXIso_holds :
    Langlandscape.Hyp.X.iso (Ideal.span {(5 : ℤ)}) (ZMod 5) (ZMod 5) :=
  ⟨(LinearEquiv.ofTop _ toyXIso_top).symm⟩

end LanglandscapeTests.Hyp.S05
