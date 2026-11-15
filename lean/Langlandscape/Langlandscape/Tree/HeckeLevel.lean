/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Adjoint
import Langlandscape.Brandt.RightTranslate

/-!
# Hecke operators and level change — S02-L7a

Tex labels: `prop:s02-quot`(c) (level-change half), `if:s02-quot`.

Let `V` be invariant at the split prime `q` and `K' ≤ K ≤ GL₂(ℤ_q)`; put `U := V ⊓ K.comap ι_q`,
`U' := V ⊓ K'.comap ι_q` (so `U' ≤ U`, and `U`, `U'` agree away from `q`). For `t` with `t_q = 1`:

* `levelPull U' U R : R^{X(U)} →ₗ R^{X(U')}`, `f ↦ f ∘ π` (pullback along `π = levelMap U' U`);
  `levelPull_mk`, and the adjunction `evalPairing_pushforward` : `⟨π_* a, f⟩ = ⟨a, π^* f⟩`.
* `heckeT_comm_levelPull` : `T_t ∘ π^* = π^* ∘ T_t`. Proof: `U' t U' / U' → U t U / U`, `sU' ↦ sU`, is a bijection,
  because every `u ∈ U` is `u = a · k` with `a ∈ U'` (the `q`-away part) and `k = ι_q⁻¹(u_q)` commuting with `t`,
  and because elements of `U' t U'` have `q`-component in `K'`.
* `heckeTHom_comm_levelPush` : `π_* ∘ T_t^t = T_t^t ∘ π_*` (finite class sets), by transposition.

* `heckeT_comm_levelPull_of_eq`, `heckeTHom_comm_levelPush_of_eq` : the same for levels `U'`, `U` given up to
  equality `U = V ⊓ K.comap ι_q`, `U' = V ⊓ K'.comap ι_q` (e.g. named levels such as `U0q U`).

Trivial coefficients only (`R^X`, `R[X]`). "Supported away from `q`" is encoded as `localProjUnits d.a d.b q t = 1`.
Depends on stage 01 only. Status: *formalized*.
-/

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

section LevelPull

variable {a b : ℤ} (U' U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `prop:s02-quot`(c): the pullback `π^* : R^{X_B(U)} → R^{X_B(U')}`, `f ↦ f ∘ π`, along the projection
`π = levelMap U' U` (meaningful for `U' ≤ U`). -/
noncomputable def levelPull : ZXdual U R →ₗ[R] ZXdual U' R :=
  LinearMap.funLeft R R (levelMap U' U)

/-- `prop:s02-quot`(c) (`s02-quot`): `π^* f (c) = f (π c)`. -/
theorem levelPull_apply (f : ZXdual U R) (c : XB U') : levelPull U' U R f c = f (levelMap U' U c) :=
  rfl

variable {U' U}

/-- `prop:s02-quot`(c) (`s02-quot`): `π^* f ([x]') = f ([x])` for `U' ≤ U`. -/
theorem levelPull_mk (hle : U' ≤ U) (f : ZXdual U R) (x : (GL2TF.Quat.BHat a b)ˣ) :
    levelPull U' U R f (DoubleCoset.mk (globalUnits a b) U' x) =
      f (DoubleCoset.mk (globalUnits a b) U x) := by
  rw [levelPull_apply, levelMap_mk hle]

/-- `prop:s02-quot`(c) (`s02-quot`): `π_*` and `π^*` are adjoint for the evaluation pairing,
`⟨π_* a, f⟩ = ⟨a, π^* f⟩`. -/
theorem evalPairing_pushforward (x : ZX U' R) (f : ZXdual U R) :
    evalPairing U R (pushforward U' U R x) f = evalPairing U' R x (levelPull U' U R f) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]
  | single c r => rw [pushforward_single, evalPairing_single, evalPairing_single, levelPull_apply]

/-- `prop:s02-quot`(c) (`s02-quot`), abstract form: let `U' ≤ U`, let every `u ∈ U` be `a k` with `a ∈ U'` and
`k ∈ U` commuting with `t`, and let `y⁻¹ z ∈ U` imply `y⁻¹ z ∈ U'` for `y, z ∈ U' t U'`. Then a system of
representatives of `U' t U' / U'` is one of `U t U / U`, and `T_t ∘ π^* = π^* ∘ T_t`. -/
private theorem heckeT_comm_levelPull_aux (t : (GL2TF.Quat.BHat a b)ˣ) (hle : U' ≤ U)
    (hdec : ∀ u ∈ U, ∃ a' ∈ U', ∃ k ∈ U, Commute k t ∧ u = a' * k)
    (hback : ∀ y ∈ dcSet U' t, ∀ z ∈ dcSet U' t, y⁻¹ * z ∈ U → y⁻¹ * z ∈ U')
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) (hfin' : (U' ⊓ conjSub U' t).relIndex U' ≠ 0) :
    (heckeT U' t R hfin').comp (levelPull U' U R) = (levelPull U' U R).comp (heckeT U t R hfin) := by
  obtain ⟨S, hS, hcov, hinj⟩ := exists_heckeReps U' t hfin'
  have hS2 : ∀ s ∈ S, s ∈ dcSet U t := by
    intro s hs
    obtain ⟨u, hu, v, hv, e⟩ := (mem_dcSet U' t).1 (hS s hs)
    exact (mem_dcSet U t).2 ⟨u, hle hu, v, hle hv, e⟩
  have hcov2 : ∀ y ∈ dcSet U t, ∃ s ∈ S,
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U t).1 hy
    obtain ⟨a', ha', k, hk, hkt, rfl⟩ := hdec u hu
    have hat : a' * t ∈ dcSet U' t :=
      (mem_dcSet U' t).2 ⟨a', ha', 1, U'.one_mem, (mul_one _).symm⟩
    obtain ⟨s, hs, hse⟩ := hcov _ hat
    refine ⟨s, hs, ?_⟩
    rw [QuotientGroup.eq] at hse ⊢
    have e : (a' * k * t * v)⁻¹ * s = (k * v)⁻¹ * ((a' * t)⁻¹ * s) := by
      rw [mul_assoc a' k t, hkt.eq]
      group
    rw [e]
    exact U.mul_mem (U.inv_mem (U.mul_mem hk hv)) (hle hse)
  have hinj2 : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S := by
    intro s1 hs1 s2 hs2 e
    apply hinj hs1 hs2
    have e1 : (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s2 := e
    rw [QuotientGroup.eq] at e1
    show (QuotientGroup.mk s1 : (GL2TF.Quat.BHat a b)ˣ ⧸ U') = QuotientGroup.mk s2
    rw [QuotientGroup.eq]
    exact hback s1 (hS s1 (Finset.mem_coe.1 hs1)) s2 (hS s2 (Finset.mem_coe.1 hs2)) e1
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U' x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, heckeT_apply_reps U' t R hfin' S hS hcov hinj,
    levelPull_mk R hle, heckeT_apply_reps U t R hfin S hS2 hcov2 hinj2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [levelPull_mk R hle]

/-- `prop:s02-quot`(c) (`s02-quot`), abstract form: the transpose of `heckeT_comm_levelPull_aux`,
`π_* ∘ T_t^t = T_t^t ∘ π_*` on finite class sets, from `T_t ∘ π^* = π^* ∘ T_t`. -/
private theorem heckeTHom_comm_levelPush_aux [Finite (XB U)] [Finite (XB U')] (t : (GL2TF.Quat.BHat a b)ˣ)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) (hfin' : (U' ⊓ conjSub U' t).relIndex U' ≠ 0)
    (hcomm : (heckeT U' t R hfin').comp (levelPull U' U R) = (levelPull U' U R).comp (heckeT U t R hfin)) :
    (pushforward U' U R).comp (heckeTHom U' t R hfin') =
      (heckeTHom U t R hfin).comp (pushforward U' U R) := by
  refine LinearMap.ext fun x => Finsupp.ext fun c => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    ← evalPairing_pi_single U R (pushforward U' U R (heckeTHom U' t R hfin' x)) c,
    ← evalPairing_pi_single U R (heckeTHom U t R hfin (pushforward U' U R x)) c,
    evalPairing_pushforward, heckeTHom_transpose, heckeTHom_transpose, evalPairing_pushforward]
  exact congrArg (evalPairing U' R x) (LinearMap.congr_fun hcomm (Pi.single c (1 : R)))

end LevelPull

section Level

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}
  {V : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K K' : Subgroup (GL (Fin 2) ℚ_[q])}

/-- `prop:s02-quot`(c) (`s02-quot`): an operator supported away from `q` (`t_q = 1`) has trivial `q`-component
`ι_q(t_q) = 1`. -/
private theorem localComponent_eq_one_of_away {t : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (ht : localProjUnits d.a d.b q t = 1) : localComponent d q hq t = 1 := by
  rw [localComponent_apply, ht, map_one]

/-- `prop:s02-quot`(c) (`s02-quot`): `ι_q⁻¹(k)` (embedded at `q`) commutes with `t` when `t_q = 1`. -/
private theorem commute_localEmbedGL_of_away {t : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (ht : localProjUnits d.a d.b q t = 1) (k : GL (Fin 2) ℚ_[q]) : Commute (localEmbedGL d q hq k) t := by
  rw [localEmbedGL_apply]
  exact commute_localEmbed_of_commute _ (by rw [ht]; exact Commute.one_right _)

/-- `prop:s02-quot`(c) (`s02-quot`): for `t_q = 1`, every element of `U' t U'` (`U' = V ⊓ K'.comap ι_q`) has
`q`-component in `K'`. -/
private theorem localComponent_mem_of_mem_dcSet {t : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (ht : localProjUnits d.a d.b q t = 1) {y : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hy : y ∈ dcSet (V ⊓ K'.comap (localComponent d q hq)) t) : localComponent d q hq y ∈ K' := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet _ t).1 hy
  rw [map_mul, map_mul, localComponent_eq_one_of_away ht, mul_one]
  exact K'.mul_mem (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).2)
    (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hv).2)

/-- `prop:s02-quot`(c) (`s02-quot`), level-change half: let `V` be invariant at `q`, `K' ≤ K ≤ GL₂(ℤ_q)`,
`U = V ⊓ K.comap ι_q`, `U' = V ⊓ K'.comap ι_q`, and let `t` be supported away from `q` (`t_q = 1`). Then the pullback
`π^*` along `X_B(U') → X_B(U)` commutes with `T_t`: `T_t ∘ π^* = π^* ∘ T_t`. The map `U' t U' / U' → U t U / U`,
`sU' ↦ sU`, is a bijection because the `q`-factor of `U` commutes with `t`. -/
theorem heckeT_comm_levelPull (R : Type*) [CommRing R] (hV : IsInvariantAt d q hq V) (hK' : K' ≤ K)
    (hK : K ≤ Langlandscape.Local.GL2Zl q) (t : (GL2TF.Quat.BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : ((V ⊓ K.comap (localComponent d q hq)) ⊓ conjSub (V ⊓ K.comap (localComponent d q hq)) t).relIndex
      (V ⊓ K.comap (localComponent d q hq)) ≠ 0)
    (hfin' : ((V ⊓ K'.comap (localComponent d q hq)) ⊓
      conjSub (V ⊓ K'.comap (localComponent d q hq)) t).relIndex (V ⊓ K'.comap (localComponent d q hq)) ≠ 0) :
    (heckeT (V ⊓ K'.comap (localComponent d q hq)) t R hfin').comp
        (levelPull (V ⊓ K'.comap (localComponent d q hq)) (V ⊓ K.comap (localComponent d q hq)) R) =
      (levelPull (V ⊓ K'.comap (localComponent d q hq)) (V ⊓ K.comap (localComponent d q hq)) R).comp
        (heckeT (V ⊓ K.comap (localComponent d q hq)) t R hfin) := by
  have hle : V ⊓ K'.comap (localComponent d q hq) ≤ V ⊓ K.comap (localComponent d q hq) := fun u hu =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hu).1,
      Subgroup.mem_comap.2 (hK' (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).2))⟩
  have hdec : ∀ u ∈ V ⊓ K.comap (localComponent d q hq), ∃ a' ∈ V ⊓ K'.comap (localComponent d q hq),
      ∃ k ∈ V ⊓ K.comap (localComponent d q hq), Commute k t ∧ u = a' * k := by
    intro u hu
    have huV : u ∈ V := (Subgroup.mem_inf.1 hu).1
    have huK : localComponent d q hq u ∈ K := Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).2
    have ha : awayAt d q hq u ∈ V ⊓ K'.comap (localComponent d q hq) := by
      refine Subgroup.mem_inf.2 ⟨hV u huV _ (inv_mem (hK huK)), Subgroup.mem_comap.2 ?_⟩
      rw [localComponent_awayAt (hp := hq)]
      exact one_mem _
    exact ⟨awayAt d q hq u, ha, localEmbedGL d q hq (localComponent d q hq u),
      localEmbedGL_mem_inf_comap hV hK huK, commute_localEmbedGL_of_away ht _,
      (awayAt_mul_localEmbedGL (hp := hq) u).symm⟩
  have hback : ∀ y ∈ dcSet (V ⊓ K'.comap (localComponent d q hq)) t,
      ∀ z ∈ dcSet (V ⊓ K'.comap (localComponent d q hq)) t,
      y⁻¹ * z ∈ V ⊓ K.comap (localComponent d q hq) → y⁻¹ * z ∈ V ⊓ K'.comap (localComponent d q hq) := by
    intro y hy z hz h
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h).1, Subgroup.mem_comap.2 ?_⟩
    rw [map_mul, map_inv]
    exact K'.mul_mem (K'.inv_mem (localComponent_mem_of_mem_dcSet ht hy))
      (localComponent_mem_of_mem_dcSet ht hz)
  exact heckeT_comm_levelPull_aux R t hle hdec hback hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`), level-change half on the homological side: under the hypotheses of
`heckeT_comm_levelPull` and for finite class sets, the pushforward `π_* : R[X_B(U')] → R[X_B(U)]` commutes with the
transposed Hecke operator: `π_* ∘ T_t^t = T_t^t ∘ π_*` (by transposition via `heckeTHom_transpose`). -/
theorem heckeTHom_comm_levelPush (R : Type*) [CommRing R] (hV : IsInvariantAt d q hq V) (hK' : K' ≤ K)
    (hK : K ≤ Langlandscape.Local.GL2Zl q) (t : (GL2TF.Quat.BHat d.a d.b)ˣ)
    (ht : localProjUnits d.a d.b q t = 1)
    (hfin : ((V ⊓ K.comap (localComponent d q hq)) ⊓ conjSub (V ⊓ K.comap (localComponent d q hq)) t).relIndex
      (V ⊓ K.comap (localComponent d q hq)) ≠ 0)
    (hfin' : ((V ⊓ K'.comap (localComponent d q hq)) ⊓
      conjSub (V ⊓ K'.comap (localComponent d q hq)) t).relIndex (V ⊓ K'.comap (localComponent d q hq)) ≠ 0)
    [Finite (XB (V ⊓ K.comap (localComponent d q hq)))] [Finite (XB (V ⊓ K'.comap (localComponent d q hq)))] :
    (pushforward (V ⊓ K'.comap (localComponent d q hq)) (V ⊓ K.comap (localComponent d q hq)) R).comp
        (heckeTHom (V ⊓ K'.comap (localComponent d q hq)) t R hfin') =
      (heckeTHom (V ⊓ K.comap (localComponent d q hq)) t R hfin).comp
        (pushforward (V ⊓ K'.comap (localComponent d q hq)) (V ⊓ K.comap (localComponent d q hq)) R) :=
  heckeTHom_comm_levelPush_aux R t hfin hfin' (heckeT_comm_levelPull R hV hK' hK t ht hfin hfin')

/-- `prop:s02-quot`(c) (`s02-quot`), level-change half, for levels given up to equality: if
`U = V ⊓ K.comap ι_q` and `U' = V ⊓ K'.comap ι_q` (e.g. `U'` a named level such as `U0q U`), then
`T_t ∘ π^* = π^* ∘ T_t` (`heckeT_comm_levelPull`). -/
theorem heckeT_comm_levelPull_of_eq (R : Type*) [CommRing R] {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hV : IsInvariantAt d q hq V) (hK' : K' ≤ K) (hK : K ≤ Langlandscape.Local.GL2Zl q)
    (hU : U = V ⊓ K.comap (localComponent d q hq)) (hU' : U' = V ⊓ K'.comap (localComponent d q hq))
    (t : (GL2TF.Quat.BHat d.a d.b)ˣ) (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) (hfin' : (U' ⊓ conjSub U' t).relIndex U' ≠ 0) :
    (heckeT U' t R hfin').comp (levelPull U' U R) = (levelPull U' U R).comp (heckeT U t R hfin) := by
  subst hU hU'
  exact heckeT_comm_levelPull R hV hK' hK t ht hfin hfin'

/-- `prop:s02-quot`(c) (`s02-quot`), level-change half on the homological side, for levels given up to equality
(`U = V ⊓ K.comap ι_q`, `U' = V ⊓ K'.comap ι_q`): `π_* ∘ T_t^t = T_t^t ∘ π_*` (`heckeTHom_comm_levelPush`). -/
theorem heckeTHom_comm_levelPush_of_eq (R : Type*) [CommRing R] {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hV : IsInvariantAt d q hq V) (hK' : K' ≤ K) (hK : K ≤ Langlandscape.Local.GL2Zl q)
    (hU : U = V ⊓ K.comap (localComponent d q hq)) (hU' : U' = V ⊓ K'.comap (localComponent d q hq))
    (t : (GL2TF.Quat.BHat d.a d.b)ˣ) (ht : localProjUnits d.a d.b q t = 1)
    (hfin : (U ⊓ conjSub U t).relIndex U ≠ 0) (hfin' : (U' ⊓ conjSub U' t).relIndex U' ≠ 0)
    [Finite (XB U)] [Finite (XB U')] :
    (pushforward U' U R).comp (heckeTHom U' t R hfin') = (heckeTHom U t R hfin).comp (pushforward U' U R) := by
  subst hU hU'
  exact heckeTHom_comm_levelPush R hV hK' hK t ht hfin hfin'

end Level

end Langlandscape.Tree
