/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Admissible
import Langlandscape.Tree.Local
import Langlandscape.Graph.Bipartite
import Langlandscape.Brandt.HeckeFinite

/-!
# The Brandt graph `BG(U, q)` (S02-L4b)

`plan/staged/stage-02-tree-quotients.tex`: `def:s02-BG` (and the index/finiteness plumbing used in
`prop:s02-quot`). Fix a prime `q ∤ D` and a `q`-level `U` (`IsQLevel d q hq U`); write `U_0(q)U = U ∩ U_0(q)`
(`U0q U`) and `α = ι_q^{-1} diag(1, q) ∈ B̂^×` (`alphaElt`, supported at `q`).

* `alphaElt_inv_conj_mem` : `α⁻¹ (U_0(q)U) α ⊆ U` (from `α⁻¹ Iw_q α ⊆ GL₂(ℤ_q)`, S02-L1).
* `relIndex_U0q` : `[U : U_0(q)U] = q + 1` (from `[GL₂(ℤ_q) : Iw_q] = q + 1`, S02-L1).
* `s1Level U = α⁻¹ (U_0(q)U) α ≤ U`, `relIndex_s1Level_ne_zero` (via `α = z_q ϖ_q⁻¹`, `z_q` central, and the
  stage-1 finiteness `relIndex_elemT_ne_zero`).
* `finite_XB_of_isQLevel`, `finite_XB_U0q` : `X_B(U)` and `X_B(U_0(q)U)` are finite.
* `s0 = π : X_B(U_0(q)U) → X_B(U)`, `[y] ↦ [y]`; `s1 : X_B(U_0(q)U) → X_B(U)`, `[y] ↦ [y α]`.
* `BG d q hq U hU` : the bipartite multigraph with `V₀ = V₁ = X_B(U)`, `E = X_B(U_0(q)U)`, endpoints `s0`, `s1`;
  `BGConnected` its connectivity.
* `s0Pull`, `s1Pull` : `R^{X(U)} → R^{X(U_0(q)U)}` (pullbacks `f ↦ f ∘ s_j`); `s0Push`, `s1Push` :
  `R[X(U_0(q)U)] → R[X(U)]` (pushforwards).

Status: *formalized* (built, gate1 green; the S02-L1 local lemmas `alphaq_inv_conj_mem_GL2Zl`, `relIndex_Iw` are proved).
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local

/-! ### The element `α` and the edge level -/

section Alpha

/-- `def:s02-BG`: `α = ι_q^{-1} diag(1, q) ∈ B̂^×` (supported at `q`). -/
noncomputable def alphaElt (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) : (BHat d.a d.b)ˣ :=
  localEmbedGL d q hq (alphaq q)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-BG` (`s02-BG`): a `q`-level is invariant at `q` (`U · ι_q(GL₂(ℤ_q)) ⊆ U`). -/
theorem isInvariantAt_of_isQLevel (hU : IsQLevel d q hq U) : IsInvariantAt d q hq U := by
  obtain ⟨-, -, V, hV, rfl⟩ := hU
  intro u hu k hk
  refine Subgroup.mem_inf.2 ⟨hV u (Subgroup.mem_inf.1 hu).1 k hk, Subgroup.mem_comap.2 ?_⟩
  rw [map_mul, localComponent_localEmbedGL]
  exact mul_mem (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).2) hk

/-- `def:s02-BG` (`s02-BG`): the `q`-component of an element of a `q`-level lies in `GL₂(ℤ_q)`. -/
theorem localComponent_mem_of_isQLevel (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U) :
    localComponent d q hq u ∈ GL2Zl q := by
  obtain ⟨-, -, V, hV, rfl⟩ := hU
  exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).2

/-- `def:s02-BG` (`s02-BG`): `ι_q(GL₂(ℤ_q)) ⊆ U` for a `q`-level `U`. -/
theorem localEmbedGL_mem_of_isQLevel (hU : IsQLevel d q hq U) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ GL2Zl q) : localEmbedGL d q hq k ∈ U := by
  have h := isInvariantAt_of_isQLevel hU 1 U.one_mem k hk
  rwa [one_mul] at h

/-- `def:s02-BG` (`s02-BG`): the away-from-`q` part of an element of a `q`-level lies in the level. -/
theorem awayAt_mem_of_isQLevel (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} (hu : u ∈ U) :
    awayAt d q hq u ∈ U :=
  isInvariantAt_of_isQLevel hU u hu _ (inv_mem (localComponent_mem_of_isQLevel hU hu))

/-- `def:s02-BG` (`s02-BG`): for a `q`-level `U`, `u ∈ U_0(q)U ↔ u ∈ U ∧ u_q ∈ Iw_q`. -/
theorem mem_U0q_iff_of_isQLevel (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ} :
    u ∈ d.U0q q (coprime_of_not_dvd hq) U ↔ u ∈ U ∧ localComponent d q hq u ∈ Iw q := by
  have hqp : q.Prime := Fact.out
  rw [DefiniteData.mem_U0q_iff, DefiniteData.mem_U0_iff]
  constructor
  · rintro ⟨huU, -, h⟩
    have h0 := h q hqp.mem_primeFactors_self hq
    rw [Nat.Prime.factorization_self hqp] at h0
    exact ⟨huU, h0⟩
  · rintro ⟨huU, huI⟩
    refine ⟨huU, hU.1 huU, fun ℓ _ hℓ hD => ?_⟩
    have hℓq : ℓ = q := by
      rw [Nat.Prime.primeFactors hqp] at hℓ
      exact Finset.mem_singleton.1 hℓ
    subst hℓq
    rw [Nat.Prime.factorization_self hqp]
    exact huI

/-- `def:s02-BG` (`s02-BG`): `α⁻¹ u α = u^{(q)} · ι_q(α_q⁻¹ u_q α_q)`, where `u^{(q)} = awayAt q u`. -/
theorem alphaElt_inv_conj_eq (u : (BHat d.a d.b)ˣ) :
    (alphaElt d q hq)⁻¹ * u * alphaElt d q hq =
      awayAt d q hq u * localEmbedGL d q hq ((alphaq q)⁻¹ * localComponent d q hq u * alphaq q) := by
  have hc := (commute_awayAt_localEmbedGL (hp := hq) u (alphaq q)).inv_right
  unfold alphaElt
  conv_lhs => rw [← awayAt_mul_localEmbedGL (hp := hq) u]
  rw [map_mul, map_mul, map_inv, ← mul_assoc (localEmbedGL d q hq (alphaq q))⁻¹ (awayAt d q hq u), ← hc.eq]
  simp only [mul_assoc]

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `α⁻¹ (U_0(q)U) α ⊆ U` for a `q`-level `U`;
this makes `s_1` well defined. -/
theorem alphaElt_inv_conj_mem (hU : IsQLevel d q hq U) {u : (BHat d.a d.b)ˣ}
    (hu : u ∈ d.U0q q (coprime_of_not_dvd hq) U) :
    (alphaElt d q hq)⁻¹ * u * alphaElt d q hq ∈ U := by
  obtain ⟨huU, huI⟩ := (mem_U0q_iff_of_isQLevel hU).1 hu
  rw [alphaElt_inv_conj_eq]
  exact mul_mem (awayAt_mem_of_isQLevel hU huU)
    (localEmbedGL_mem_of_isQLevel hU (alphaq_inv_conj_mem_GL2Zl huI))

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `[U : U_0(q)U] = q + 1` for a `q`-level `U`. -/
theorem relIndex_U0q (hU : IsQLevel d q hq U) :
    (d.U0q q (coprime_of_not_dvd hq) U).relIndex U = q + 1 := by
  have e1 : d.U0q q (coprime_of_not_dvd hq) U = U ⊓ (Iw q).comap (localComponent d q hq) := by
    ext u
    rw [mem_U0q_iff_of_isQLevel hU, Subgroup.mem_inf, Subgroup.mem_comap]
  have e2 : U.map (localComponent d q hq) = GL2Zl q := by
    ext k
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact localComponent_mem_of_isQLevel hU hu
    · intro hk
      exact Subgroup.mem_map.2 ⟨_, localEmbedGL_mem_of_isQLevel hU hk, localComponent_localEmbedGL k⟩
  rw [e1, Subgroup.inf_relIndex_left, Subgroup.relIndex_comap, e2]
  exact relIndex_Iw q

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `[U : U_0(q)U] ≠ 0` for a `q`-level `U`. -/
theorem relIndex_U0q_ne_zero (hU : IsQLevel d q hq U) :
    (d.U0q q (coprime_of_not_dvd hq) U).relIndex U ≠ 0 := by
  rw [relIndex_U0q hU]
  exact Nat.succ_ne_zero q

end Alpha

/-! ### The level `α⁻¹ (U_0(q)U) α` -/

section S1Level

/-- `def:s02-BG`: the level `α⁻¹ (U_0(q)U) α` (the stabiliser level of the type-1 end of an edge). -/
noncomputable def s1Level (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) : Subgroup (BHat d.a d.b)ˣ :=
  Brandt.rightConj (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `α⁻¹ (U_0(q)U) α ≤ U`. -/
theorem s1Level_le (hU : IsQLevel d q hq U) : s1Level d q hq U ≤ U := by
  intro x hx
  have h := alphaElt_inv_conj_mem hU ((Brandt.mem_rightConj _ _).1 hx)
  have e : (alphaElt d q hq)⁻¹ * (alphaElt d q hq * x * (alphaElt d q hq)⁻¹) * alphaElt d q hq = x := by
    group
  rwa [e] at h

/-- `def:s02-BG` (`s02-BG`): `diag(1, q) · diag(q, 1) = diag(q, q)` in `GL₂(ℚ_q)`. -/
private theorem alphaq_mul_diag :
    alphaq q * diagGL (Brandt.padicUnit q) 1 = diagGL (Brandt.padicUnit q) (Brandt.padicUnit q) := by
  apply Units.ext
  rw [Units.val_mul]
  show Units.val (diagOneP q) * _ = _
  simp [diagOneP, Brandt.padicUnit, Matrix.mul_fin_two]

/-- `def:s02-BG` (`s02-BG`): `α · ϖ_q = z_q` (`ϖ_q = ι_q^{-1} diag(q, 1)`, `z_q = ι_q^{-1} diag(q, q)` central). -/
private theorem alphaElt_mul_elemT :
    alphaElt d q hq * Brandt.elemT d q hq = Brandt.elemS d q hq := by
  unfold alphaElt Brandt.elemT Brandt.elemS
  rw [← alphaq_mul_diag, map_mul]

/-- `def:s02-BG` (`s02-BG`): conjugation by `α` equals conjugation by `ϖ_q⁻¹` (since `α = z_q ϖ_q⁻¹`, `z_q`
central), so `α⁻¹ U α = ϖ_q U ϖ_q⁻¹`. -/
private theorem conjSub_alphaElt_inv :
    Brandt.conjSub U (alphaElt d q hq)⁻¹ = Brandt.conjSub U (Brandt.elemT d q hq) := by
  have hα : alphaElt d q hq = Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹ :=
    eq_mul_inv_of_mul_eq alphaElt_mul_elemT
  ext x
  rw [Brandt.mem_conjSub, Brandt.mem_conjSub, inv_inv, hα]
  have hc := (Brandt.elemS_commute d q hq ((Brandt.elemT d q hq)⁻¹ * x * Brandt.elemT d q hq)).eq
  have e : Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹ * x *
      (Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹)⁻¹ =
      (Brandt.elemT d q hq)⁻¹ * x * Brandt.elemT d q hq := by
    calc Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹ * x *
          (Brandt.elemS d q hq * (Brandt.elemT d q hq)⁻¹)⁻¹
        = Brandt.elemS d q hq * ((Brandt.elemT d q hq)⁻¹ * x * Brandt.elemT d q hq) *
            (Brandt.elemS d q hq)⁻¹ := by group
      _ = (Brandt.elemT d q hq)⁻¹ * x * Brandt.elemT d q hq * Brandt.elemS d q hq *
            (Brandt.elemS d q hq)⁻¹ := by rw [hc]
      _ = (Brandt.elemT d q hq)⁻¹ * x * Brandt.elemT d q hq := by group
  rw [e]

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `[U : α⁻¹ (U_0(q)U) α] ≠ 0` for a `q`-level `U`. -/
theorem relIndex_s1Level_ne_zero (hU : IsQLevel d q hq U) : (s1Level d q hq U).relIndex U ≠ 0 := by
  let φ : (BHat d.a d.b)ˣ →* (BHat d.a d.b)ˣ :=
    MonoidHom.mk' (fun x => alphaElt d q hq * x * (alphaElt d q hq)⁻¹) (fun x y => by group)
  have e1 : ∀ H : Subgroup (BHat d.a d.b)ˣ, Brandt.rightConj H (alphaElt d q hq) = H.comap φ := by
    intro H
    ext x
    exact Brandt.mem_rightConj H (alphaElt d q hq)
  -- `[α⁻¹ U α : α⁻¹ (U_0(q)U) α] = [U : U_0(q)U] ≠ 0`
  have h1 : (s1Level d q hq U).relIndex (Brandt.rightConj U (alphaElt d q hq)) ≠ 0 := by
    unfold s1Level
    rw [e1, e1]
    exact Subgroup.relIndex_comap_ne_zero φ (relIndex_U0q_ne_zero hU)
  -- `[U : U ∩ α⁻¹ U α] = [U : U ∩ ϖ_q U ϖ_q⁻¹] ≠ 0` (stage 1, Hecke finiteness)
  have h2 : (Brandt.rightConj U (alphaElt d q hq)).relIndex U ≠ 0 := by
    rw [← Subgroup.inf_relIndex_left (H := U) (K := Brandt.rightConj U (alphaElt d q hq))]
    show (U ⊓ Brandt.conjSub U (alphaElt d q hq)⁻¹).relIndex U ≠ 0
    rw [conjSub_alphaElt_inv]
    exact Brandt.relIndex_elemT_ne_zero d U q hq (isInvariantAt_of_isQLevel hU) hU.1
  exact Subgroup.relIndex_ne_zero_trans (hHK := h1) (hKL := h2)

end S1Level

/-! ### Finiteness -/

section Finite

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `X_B(U)` is finite for a `q`-level `U`
(A18: `U ≤ Ô^×` of finite index). -/
theorem finite_XB_of_isQLevel (hU : IsQLevel d q hq U) : Finite (XB U) :=
  XB_finite_of_relIndex hU.1 hU.2.1

/-- `def:s02-BG` (`s02-BG`), `prop:s02-quot` (`s02-quot`): `X_B(U_0(q)U)` is finite for a `q`-level `U`. -/
theorem finite_XB_U0q (hU : IsQLevel d q hq U) : Finite (XB (d.U0q q (coprime_of_not_dvd hq) U)) :=
  haveI := finite_XB_of_isQLevel hU
  XB_finite_of_relIndex (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) (relIndex_U0q_ne_zero hU)

end Finite

/-! ### The maps `s_0`, `s_1` and the graph -/

section Graph

/-- `def:s02-BG`: `s_0 = π : X_B(U_0(q)U) → X_B(U)`, `[y] ↦ [y]`. -/
noncomputable def s0 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    XB (d.U0q q (coprime_of_not_dvd hq) U) → XB U :=
  Brandt.levelMap (d.U0q q (coprime_of_not_dvd hq) U) U

/-- `def:s02-BG`: `s_1 : X_B(U_0(q)U) → X_B(U)`, `[y] ↦ [y α]` (well defined for a `q`-level, `s1_mk`). -/
noncomputable def s1 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    XB (d.U0q q (coprime_of_not_dvd hq) U) → XB U :=
  Brandt.translateMap (d.U0q q (coprime_of_not_dvd hq) U) U (alphaElt d q hq)

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-BG` (`s02-BG`): `s_0 [y] = [y]`. -/
theorem s0_mk (y : (BHat d.a d.b)ˣ) :
    s0 d q hq U (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y) =
      DoubleCoset.mk (globalUnits d.a d.b) U y :=
  Brandt.levelMap_mk (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) y

/-- `def:s02-BG` (`s02-BG`): `s_1 [y] = [y α]` for a `q`-level `U`. -/
theorem s1_mk (hU : IsQLevel d q hq U) (y : (BHat d.a d.b)ˣ) :
    s1 d q hq U (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U) y) =
      DoubleCoset.mk (globalUnits d.a d.b) U (y * alphaElt d q hq) :=
  Brandt.translateMap_mk (fun _ hu => alphaElt_inv_conj_mem hU hu) y

/-- `def:s02-BG`: the Brandt graph `BG(U, q)`: vertices `V₀ = V₁ = X_B(U)`, edges `X_B(U_0(q)U)`, the edge `[y]`
joining `s_0 [y] = [y] ∈ V₀` to `s_1 [y] = [y α] ∈ V₁`. The `q`-level hypothesis is carried for well-definedness
of `s_1` (`s1_mk`). -/
noncomputable def BG (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (_hU : IsQLevel d q hq U) : Langlandscape.Graph.BipMultigraph where
  V0 := XB U
  V1 := XB U
  E := XB (d.U0q q (coprime_of_not_dvd hq) U)
  s0 := s0 d q hq U
  s1 := s1 d q hq U

/-- `def:s02-BG`: `BG(U, q)` is connected. -/
def BGConnected (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : IsQLevel d q hq U) : Prop :=
  (BG d q hq U hU).Connected

end Graph

/-! ### Pullbacks and pushforwards along `s_0`, `s_1` -/

section Linear

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
  (R : Type*) [CommRing R]

/-- `def:s02-BG`: the pullback `s_0^* : R^{X(U)} → R^{X(U_0(q)U)}`, `f ↦ f ∘ s_0`. -/
noncomputable def s0Pull : Brandt.ZXdual U R →ₗ[R] Brandt.ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R :=
  LinearMap.funLeft R R (s0 d q hq U)

/-- `def:s02-BG`: the pullback `s_1^* : R^{X(U)} → R^{X(U_0(q)U)}`, `f ↦ f ∘ s_1`. -/
noncomputable def s1Pull : Brandt.ZXdual U R →ₗ[R] Brandt.ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R :=
  LinearMap.funLeft R R (s1 d q hq U)

/-- `def:s02-BG`: the pushforward `s_{0*} : R[X(U_0(q)U)] → R[X(U)]`, `[e] ↦ [s_0 e]`. -/
noncomputable def s0Push : Brandt.ZX (d.U0q q (coprime_of_not_dvd hq) U) R →ₗ[R] Brandt.ZX U R :=
  Finsupp.lmapDomain R R (s0 d q hq U)

/-- `def:s02-BG`: the pushforward `s_{1*} : R[X(U_0(q)U)] → R[X(U)]`, `[e] ↦ [s_1 e]`. -/
noncomputable def s1Push : Brandt.ZX (d.U0q q (coprime_of_not_dvd hq) U) R →ₗ[R] Brandt.ZX U R :=
  Finsupp.lmapDomain R R (s1 d q hq U)

variable {d q hq U R}

/-- `def:s02-BG` (`s02-BG`): `s_{0*} (r [e]) = r [s_0 e]`. -/
theorem s0Push_single (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) (r : R) :
    s0Push d q hq U R (Finsupp.single e r) = Finsupp.single (s0 d q hq U e) r := by
  rw [s0Push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- `def:s02-BG` (`s02-BG`): `s_{1*} (r [e]) = r [s_1 e]`. -/
theorem s1Push_single (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) (r : R) :
    s1Push d q hq U R (Finsupp.single e r) = Finsupp.single (s1 d q hq U e) r := by
  rw [s1Push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- `def:s02-BG` (`s02-BG`): `s_0^* f = f ∘ s_0`. -/
theorem s0Pull_apply (f : Brandt.ZXdual U R) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    s0Pull d q hq U R f e = f (s0 d q hq U e) :=
  rfl

/-- `def:s02-BG` (`s02-BG`): `s_1^* f = f ∘ s_1`. -/
theorem s1Pull_apply (f : Brandt.ZXdual U R) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    s1Pull d q hq U R f e = f (s1 d q hq U e) :=
  rfl

end Linear

end Langlandscape.Tree
