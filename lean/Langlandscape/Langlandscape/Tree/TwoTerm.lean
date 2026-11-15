/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.BrandtGraph
import Langlandscape.Graph.H1
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The two-term complex with trivial coefficients (S02-L9)

`mathematics/chapters/s02/3-cohomology.tex` (`def:s02-Mhom`, `prop:s02-Mhomprops`(d), the sign and index table
`if:s02-coh`); `plan/staged/stage-02-tree-quotients.tex`: `def:s02-Mhom`, `prop:s02-coh`(b), `prop:s02-harm`
(combinatorial part), `if:s02-coh`.

Fix a prime `q ∤ D`, a `q`-level `U`, the edge level `U' = U_0(q)U` and `U'_α = α⁻¹ U' α` (`s1Level`). Trivial
coefficients `V = R`, `R` any commutative ring.

* `partialHom = ∂ = (−s_{0*}, s_{1*}) : R[X(U')] → R[X(U)]²`, `[e] ↦ (−[s_0 e], [s_1 e])` (`partialHom_single`);
  `partialHom_eq_boundary` : it is the boundary of the Brandt graph `BG(U, q)`.
* `deltaCoh = δ : R^{X(U)} × R^{X(U)} → R^{X(U')}`, `(f_0, f_1) ↦ s_1^* f_1 − s_0^* f_0`.
* `s0Tr = tr_0`, `s1Tr = tr_1 : R^{X(U')} → R^{X(U)}`, `(tr_0 f)[x] = ∑_{u ∈ U/U'} f[x u]` and
  `(tr_1 f)[x] = ∑_{u ∈ U/U'_α} f[x u α⁻¹]` (`s0Tr_apply_mk`, `s1Tr_apply_mk`).
* `qNew = ker (tr_0, tr_1)` (the `q`-new subspace of `R^{X(U')}`, `prop:s02-harm`).
* `normMap_comp_s0Push`, `normMap_comp_s1Push` : `ν ∘ s_{j*} = tr_j ∘ ν'` (no index factor, no factor `2`:
  `-1 ∈ U` forces `-1 ∈ U'` and `-1 ∈ U'_α`).
* `qNewEquivKerPartial` : `ν'` restricts to `ker ∂ ≃ q-new` when every weight `w_x` (`x ∈ X(U)`) is a unit in `R`
  (then every weight at level `U'` is a unit too, since `w_e ∣ w_{s_0 e}`).

Signs (binding, `if:s02-coh`): `∂ = (−s_{0*}, s_{1*})`, `δ(f_0, f_1) = s_1^* f_1 − s_0^* f_0`.

Status: *formalized*.
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

/-! ### `-1` lies in every level involved -/

section NegOne

/-- `def:s02-Mhom` (`s02-Mhom`): `-1 ∈ K_0(ℓ^e)`. -/
private theorem neg_one_mem_K0 {ℓ : ℕ} [Fact ℓ.Prime] (e : ℕ) : (-1 : GL (Fin 2) ℚ_[ℓ]) ∈ K0 ℓ e := by
  refine mem_K0_of_entries (-1) 0 0 (-1) ?_ (by simp) (dvd_zero _)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {d : DefiniteData}

/-- `def:s02-Mhom` (`s02-Mhom`): `-1 ∈ U_0(N)`. -/
theorem negOne_mem_U0 {N : ℕ} {hN : N.Coprime d.D} : (negOne : (BHat d.a d.b)ˣ) ∈ d.U0 N hN := by
  refine DefiniteData.mem_U0_iff.2 ⟨negOne_mem_Ohat d, fun ℓ _ _ hD => ?_⟩
  have h : localComponent d ℓ hD negOne = -1 := by
    apply Units.ext
    rw [localComponent_val]
    simp [negOne]
  rw [h]
  exact neg_one_mem_K0 _

variable {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-Mhom` (`s02-Mhom`): `-1 ∈ U_0(q)U` or `-1 ∉ U` (the hypothesis of `normMap_pushforward` for
`U_0(q)U ≤ U`). -/
theorem negOne_mem_U0q_or (hq : ¬ q ∣ d.D) :
    (negOne : (BHat d.a d.b)ˣ) ∈ d.U0q q (coprime_of_not_dvd hq) U ∨ (negOne : (BHat d.a d.b)ˣ) ∉ U := by
  by_cases h : (negOne : (BHat d.a d.b)ˣ) ∈ U
  · exact Or.inl (DefiniteData.mem_U0q_iff.2 ⟨h, negOne_mem_U0⟩)
  · exact Or.inr h

/-- `def:s02-Mhom` (`s02-Mhom`): `-1 ∈ α⁻¹ (U_0(q)U) α` or `-1 ∉ U` (`-1` is central). -/
theorem negOne_mem_s1Level_or :
    (negOne : (BHat d.a d.b)ˣ) ∈ s1Level d q hq U ∨ (negOne : (BHat d.a d.b)ˣ) ∉ U := by
  by_cases h : (negOne : (BHat d.a d.b)ˣ) ∈ U
  · left
    show negOne ∈ rightConj (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)
    rw [mem_rightConj, negOne_comm, mul_inv_cancel_right]
    exact DefiniteData.mem_U0q_iff.2 ⟨h, negOne_mem_U0⟩
  · exact Or.inr h

end NegOne

/-! ### Weights under right translation -/

section Weights

variable {a b : ℤ}

/-- `def:s02-Mhom` (`s02-Mhom`): `Γ_{x g}(g⁻¹ U g) = Γ_x(U)`. -/
theorem Gam_rightConj_mul (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g x : (GL2TF.Quat.BHat a b)ˣ) :
    Gam (rightConj U g) (x * g) = Gam U x := by
  ext δ
  rw [mem_Gam_iff, mem_Gam_iff, mem_rightConj]
  have e : g * ((x * g)⁻¹ * iotaU a b δ * (x * g)) * g⁻¹ = x⁻¹ * iotaU a b δ * x := by group
  rw [e]

/-- `def:s02-Mhom` (`s02-Mhom`): `w_{x g}(g⁻¹ U g) = w_x(U)`. -/
theorem wx_rightConj_mul (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g x : (GL2TF.Quat.BHat a b)ˣ) :
    wx (rightConj U g) (x * g) = wx U x := by
  rw [wx, wx, Gam_rightConj_mul]

/-- `def:s02-Mhom` (`s02-Mhom`): the weight of `[x g] ∈ X(g⁻¹ U g)` is the weight of `[x] ∈ X(U)`. -/
theorem wx_out_rightTranslate (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) (z : XB U) :
    wx (rightConj U g) (Quotient.out (rightTranslate U g z)) = wx U (Quotient.out z) :=
  (wx_out (rightConj U g) (Quotient.out z * g)).trans (wx_rightConj_mul U g _)

/-- `prop:s02-Mhomprops`(d) (`s02-Mhom`): pulling back along `[y] ↦ [y g⁻¹]` intertwines the norm maps at the
levels `U` and `g⁻¹ U g`: `R_{g⁻¹}(ν [c]) = ν [c g]`. -/
theorem translateLin_normMap_single (R : Type*) [CommRing R] (U : Subgroup (GL2TF.Quat.BHat a b)ˣ)
    (g : (GL2TF.Quat.BHat a b)ˣ) (c : XB U) (r : R) :
    translateLin R (rightConj U g) U g⁻¹ (normMap U R (Finsupp.single c r)) =
      normMap (rightConj U g) R (Finsupp.single (rightTranslate U g c) r) := by
  funext y
  obtain ⟨z, rfl⟩ := (rightTranslate U g).surjective y
  have hz : translateMap (rightConj U g) U g⁻¹ (rightTranslate U g z) = z :=
    (rightTranslate U g).symm_apply_apply z
  rw [translateLin, LinearMap.funLeft_apply, hz, normMap_apply, normMap_apply,
    Finsupp.single_apply_left (rightTranslate U g).injective, wx_out_rightTranslate]

end Weights

/-! ### The two-term complex -/

section Complex

/-- `def:s02-Mhom`, `if:s02-coh`: the homological differential `∂ = (−s_{0*}, s_{1*}) : R[X(U_0(q)U)] → R[X(U)]²`. -/
noncomputable def partialHom (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] :
    ZX (d.U0q q (coprime_of_not_dvd hq) U) R →ₗ[R] ZX U R × ZX U R :=
  (-(s0Push d q hq U R)).prod (s1Push d q hq U R)

/-- `def:s02-Mhom`, `if:s02-coh`: the cohomological differential
`δ(f_0, f_1) = s_1^* f_1 − s_0^* f_0 : R^{X(U)} × R^{X(U)} → R^{X(U_0(q)U)}`. -/
noncomputable def deltaCoh (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] :
    ZXdual U R × ZXdual U R →ₗ[R] ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R :=
  (s1Pull d q hq U R).comp (LinearMap.snd R (ZXdual U R) (ZXdual U R)) -
    (s0Pull d q hq U R).comp (LinearMap.fst R (ZXdual U R) (ZXdual U R))

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R]

/-- `def:s02-Mhom` (`s02-Mhom`): `∂ a = (−s_{0*} a, s_{1*} a)`. -/
theorem partialHom_apply (a : ZX (d.U0q q (coprime_of_not_dvd hq) U) R) :
    partialHom d q hq U R a = (-(s0Push d q hq U R a), s1Push d q hq U R a) :=
  rfl

/-- `def:s02-Mhom`, `if:s02-coh` (`s02-Mhom`): `∂ (r [e]) = (−r [s_0 e], r [s_1 e])`. -/
theorem partialHom_single (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) (r : R) :
    partialHom d q hq U R (Finsupp.single e r) =
      (-(Finsupp.single (s0 d q hq U e) r), Finsupp.single (s1 d q hq U e) r) := by
  rw [partialHom_apply, s0Push_single, s1Push_single]

/-- `def:s02-Mhom`, `def:s02-indef` (`s02-Mhom`): `∂` is the boundary map of the Brandt graph `BG(U, q)`. -/
theorem partialHom_eq_boundary (hU : IsQLevel d q hq U) :
    partialHom d q hq U R = Langlandscape.Graph.boundary (BG d q hq U hU) R := by
  apply Finsupp.lhom_ext
  intro e r
  refine (partialHom_single e r).trans ?_
  exact (Langlandscape.Graph.boundary_single (G := BG d q hq U hU) e r).symm

/-- `def:s02-Mhom` (`s02-Mhom`): `a ∈ ker ∂ ↔ s_{0*} a = 0 ∧ s_{1*} a = 0`. -/
theorem mem_ker_partialHom_iff {a : ZX (d.U0q q (coprime_of_not_dvd hq) U) R} :
    a ∈ LinearMap.ker (partialHom d q hq U R) ↔ s0Push d q hq U R a = 0 ∧ s1Push d q hq U R a = 0 := by
  rw [LinearMap.mem_ker, partialHom_apply, Prod.mk_eq_zero, neg_eq_zero]

/-- `def:s02-Mhom`, `if:s02-coh` (`s02-Mhom`): `δ(f_0, f_1) = s_1^* f_1 − s_0^* f_0`. -/
theorem deltaCoh_apply (f : ZXdual U R × ZXdual U R) :
    deltaCoh d q hq U R f = s1Pull d q hq U R f.2 - s0Pull d q hq U R f.1 :=
  rfl

/-- `def:s02-Mhom`, `if:s02-coh` (`s02-Mhom`): `δ(f_0, f_1)(e) = f_1(s_1 e) − f_0(s_0 e)`. -/
theorem deltaCoh_apply_apply (f : ZXdual U R × ZXdual U R) (e : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    deltaCoh d q hq U R f e = f.2 (s1 d q hq U e) - f.1 (s0 d q hq U e) :=
  rfl

end Complex

/-! ### Traces and the `q`-new subspace -/

section Trace

/-- `def:s02-Mhom`(iv), `if:s02-coh`: the trace `tr_0 : R^{X(U_0(q)U)} → R^{X(U)}`,
`(tr_0 f)[x] = ∑_{u ∈ U/U_0(q)U} f[x u]`. -/
noncomputable def s0Tr (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) :
    ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R →ₗ[R] ZXdual U R :=
  Brandt.trace (d.U0q q (coprime_of_not_dvd hq) U) U R (relIndex_U0q_ne_zero hU)

/-- `def:s02-Mhom`(iv), `if:s02-coh`: the trace `tr_1 : R^{X(U_0(q)U)} → R^{X(U)}`,
`(tr_1 f)[x] = ∑_{u ∈ U/U'_α} f[x u α⁻¹]` with `U'_α = α⁻¹ (U_0(q)U) α` (`s1Level`): translate by `α⁻¹` to level
`U'_α`, then take the trace from `U'_α` to `U`. -/
noncomputable def s1Tr (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) :
    ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R →ₗ[R] ZXdual U R :=
  (Brandt.trace (s1Level d q hq U) U R (relIndex_s1Level_ne_zero hU)).comp
    (translateLin R (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹)

/-- `prop:s02-harm`: the `q`-new subspace `ker (tr_0, tr_1) ⊆ R^{X(U_0(q)U)}`. -/
noncomputable def qNew (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) (R : Type*) [CommRing R] (hU : IsQLevel d q hq U) :
    Submodule R (ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R) :=
  LinearMap.ker ((s0Tr d q hq U R hU).prod (s1Tr d q hq U R hU))

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}
  {R : Type*} [CommRing R]

/-- `def:s02-Mhom`(iv), `if:s02-coh` (`s02-Mhom`): `(tr_0 f)[x] = ∑_{u ∈ U/U_0(q)U} f[x u]`. -/
theorem s0Tr_apply_mk (hU : IsQLevel d q hq U) (f : ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R)
    (x : (BHat d.a d.b)ˣ) :
    s0Tr d q hq U R hU f (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      ∑ᶠ u : ↥U ⧸ (d.U0q q (coprime_of_not_dvd hq) U).subgroupOf U,
        f (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
          (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ))) :=
  trace_apply_mk (d.U0q q (coprime_of_not_dvd hq) U) U R (relIndex_U0q_ne_zero hU) f x

/-- `def:s02-Mhom`(iv), `if:s02-coh` (`s02-Mhom`): `(tr_1 f)[x] = ∑_{u ∈ U/U'_α} f[x u α⁻¹]`. -/
theorem s1Tr_apply_mk (hU : IsQLevel d q hq U) (f : ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R)
    (x : (BHat d.a d.b)ˣ) :
    s1Tr d q hq U R hU f (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      ∑ᶠ u : ↥U ⧸ (s1Level d q hq U).subgroupOf U,
        f (DoubleCoset.mk (globalUnits d.a d.b) (d.U0q q (coprime_of_not_dvd hq) U)
          (x * ((Quotient.out u : U) : (BHat d.a d.b)ˣ) * (alphaElt d q hq)⁻¹)) := by
  have hV : ∀ v ∈ s1Level d q hq U,
      (alphaElt d q hq)⁻¹⁻¹ * v * (alphaElt d q hq)⁻¹ ∈ d.U0q q (coprime_of_not_dvd hq) U := by
    intro v hv
    rw [inv_inv]
    exact conj_mem_of_mem_rightConj _ _ v hv
  show Brandt.trace (s1Level d q hq U) U R (relIndex_s1Level_ne_zero hU)
      (translateLin R (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹ f)
      (DoubleCoset.mk (globalUnits d.a d.b) U x) = _
  rw [trace_apply_mk]
  simp only [traceRaw]
  exact finsum_congr fun u => translateLin_mk R hV f _

/-- `prop:s02-harm` (`s02-harm`): `f` is `q`-new iff `tr_0 f = 0` and `tr_1 f = 0`. -/
theorem mem_qNew_iff (hU : IsQLevel d q hq U) {f : ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R} :
    f ∈ qNew d q hq U R hU ↔ s0Tr d q hq U R hU f = 0 ∧ s1Tr d q hq U R hU f = 0 := by
  simp only [qNew, LinearMap.mem_ker, LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero]

/-- `prop:s02-Mhomprops`(d), `if:s02-coh` (`s02-Mhom`): `ν ∘ s_{0*} = tr_0 ∘ ν'` (no index factor; the `-1`
condition of `normMap_pushforward` holds automatically). -/
theorem normMap_comp_s0Push (hU : IsQLevel d q hq U) :
    normMap U R ∘ₗ s0Push d q hq U R =
      s0Tr d q hq U R hU ∘ₗ normMap (d.U0q q (coprime_of_not_dvd hq) U) R :=
  LinearMap.ext fun x =>
    normMap_pushforward (d.U0q q (coprime_of_not_dvd hq) U) U R (relIndex_U0q_ne_zero hU)
      (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) (negOne_mem_U0q_or hq) x

/-- `prop:s02-Mhomprops`(d), `if:s02-coh` (`s02-Mhom`): `ν ∘ s_{1*} = tr_1 ∘ ν'` (no index factor; `s_{1*}` is
the pushforward from `U'_α` after right translation by `α`, and `ν` commutes with that translation). -/
theorem normMap_comp_s1Push (hU : IsQLevel d q hq U) :
    normMap U R ∘ₗ s1Push d q hq U R =
      s1Tr d q hq U R hU ∘ₗ normMap (d.U0q q (coprime_of_not_dvd hq) U) R := by
  apply Finsupp.lhom_ext
  intro c r
  have hle : s1Level d q hq U ≤ U := s1Level_le hU
  obtain ⟨c', hc'⟩ : ∃ c' : XB (s1Level d q hq U),
      c' = rightTranslate (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq) c := ⟨_, rfl⟩
  have key1 : s1Push d q hq U R (Finsupp.single c r) =
      pushforward (s1Level d q hq U) U R (Finsupp.single c' r) := by
    rw [s1Push_single, pushforward_single, hc']
    congr 1
    exact (levelMap_mk hle (Quotient.out c * alphaElt d q hq)).symm
  have key2 : translateLin R (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹
        (normMap (d.U0q q (coprime_of_not_dvd hq) U) R (Finsupp.single c r)) =
      normMap (s1Level d q hq U) R (Finsupp.single c' r) := by
    rw [hc']
    exact translateLin_normMap_single R (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq) c r
  rw [LinearMap.comp_apply, LinearMap.comp_apply, key1,
    normMap_pushforward (s1Level d q hq U) U R (relIndex_s1Level_ne_zero hU) hle negOne_mem_s1Level_or]
  show _ = Brandt.trace (s1Level d q hq U) U R (relIndex_s1Level_ne_zero hU)
      (translateLin R (s1Level d q hq U) (d.U0q q (coprime_of_not_dvd hq) U) (alphaElt d q hq)⁻¹
        (normMap (d.U0q q (coprime_of_not_dvd hq) U) R (Finsupp.single c r)))
  rw [key2]

/-- `prop:s02-Mhomprops`(d) (`s02-Mhom`): `ν'` maps `ker ∂` into the `q`-new subspace. -/
theorem normMap_mem_qNew (hU : IsQLevel d q hq U) :
    ∀ a ∈ LinearMap.ker (partialHom d q hq U R),
      normMap (d.U0q q (coprime_of_not_dvd hq) U) R a ∈ qNew d q hq U R hU := by
  intro a ha
  obtain ⟨h0, h1⟩ := mem_ker_partialHom_iff.1 ha
  refine (mem_qNew_iff hU).2 ⟨?_, ?_⟩
  · have h := LinearMap.congr_fun (normMap_comp_s0Push (R := R) hU) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h0, map_zero] at h
    exact h.symm
  · have h := LinearMap.congr_fun (normMap_comp_s1Push (R := R) hU) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, map_zero] at h
    exact h.symm

/-- `prop:s02-Mhomprops`(c),(e) (`s02-Mhom`): if every weight `w_x`, `x ∈ X(U)`, is a unit in `R`, so is every
weight at level `U_0(q)U` (`traceCount · w_e = w_{s_0 e}`, i.e. `w_e ∣ w_{s_0 e}`). -/
theorem isUnit_wx_U0q (hq : ¬ q ∣ d.D)
    (hw : ∀ c : XB U, IsUnit ((wx U (Quotient.out c) : ℕ) : R)) (c' : XB (d.U0q q (coprime_of_not_dvd hq) U)) :
    IsUnit ((wx (d.U0q q (coprime_of_not_dvd hq) U) (Quotient.out c') : ℕ) : R) := by
  have h : DoubleCoset.mk (globalUnits d.a d.b) U
        (Quotient.out (levelMap (d.U0q q (coprime_of_not_dvd hq) U) U c')) =
      DoubleCoset.mk (globalUnits d.a d.b) U (Quotient.out c') :=
    DoubleCoset.out_eq' _
  have hn := traceCount_mul_wx (DefiniteData.U0q_le q (coprime_of_not_dvd hq) U) (negOne_mem_U0q_or hq) h
  have hR : ((traceCount (d.U0q q (coprime_of_not_dvd hq) U) U
        (Quotient.out (levelMap (d.U0q q (coprime_of_not_dvd hq) U) U c')) (Quotient.out c') : ℕ) : R) *
        ((wx (d.U0q q (coprime_of_not_dvd hq) U) (Quotient.out c') : ℕ) : R) =
      ((wx U (Quotient.out (levelMap (d.U0q q (coprime_of_not_dvd hq) U) U c')) : ℕ) : R) := by
    rw [← Nat.cast_mul, hn]
  have hu := hw (levelMap (d.U0q q (coprime_of_not_dvd hq) U) U c')
  rw [← hR] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- `prop:s02-Mhomprops`(c),(d) (`s02-Mhom`): if all weights `w_x`, `x ∈ X(U)`, are units in `R`, then `ν'`
restricts to a bijection `ker ∂ → q-new`. -/
theorem normMap_restrict_bijective (hU : IsQLevel d q hq U)
    (hw : ∀ c : XB U, IsUnit ((wx U (Quotient.out c) : ℕ) : R)) :
    Function.Bijective
      ((normMap (d.U0q q (coprime_of_not_dvd hq) U) R).restrict (normMap_mem_qNew (R := R) hU)) := by
  have : Finite (XB U) := finite_XB_of_isQLevel hU
  have : Finite (XB (d.U0q q (coprime_of_not_dvd hq) U)) := finite_XB_U0q hU
  have hν' := normMap_bijective (d.U0q q (coprime_of_not_dvd hq) U) R (isUnit_wx_U0q hq hw)
  have hν := (normMap_bijective U R hw).1
  refine ⟨fun x y hxy => Subtype.ext (hν'.1 (congrArg Subtype.val hxy)), ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨a, rfl⟩ := hν'.2 g
  obtain ⟨hg0, hg1⟩ := (mem_qNew_iff hU).1 hg
  have h0 : s0Push d q hq U R a = 0 := by
    apply hν
    rw [map_zero]
    have h := LinearMap.congr_fun (normMap_comp_s0Push (R := R) hU) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [h, hg0]
  have h1 : s1Push d q hq U R a = 0 := by
    apply hν
    rw [map_zero]
    have h := LinearMap.congr_fun (normMap_comp_s1Push (R := R) hU) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [h, hg1]
  exact ⟨⟨a, mem_ker_partialHom_iff.2 ⟨h0, h1⟩⟩, Subtype.ext rfl⟩

/-- `prop:s02-Mhomprops`(c),(d), `prop:s02-harm`, `if:s02-coh` (`s02-Mhom`, N11): if all weights `w_x`
(`x ∈ X(U)`) are units in `R` (e.g. `R = ℤ_p`, `ZMod (p^m)`, `p ≥ 5`), the norm map `ν'` of level `U_0(q)U`
induces `ker ∂ ≃ q-new = ker (tr_0, tr_1)`. -/
noncomputable def qNewEquivKerPartial (hU : IsQLevel d q hq U)
    (hw : ∀ c : XB U, IsUnit ((wx U (Quotient.out c) : ℕ) : R)) :
    LinearMap.ker (partialHom d q hq U R) ≃ₗ[R] qNew d q hq U R hU :=
  LinearEquiv.ofBijective
    ((normMap (d.U0q q (coprime_of_not_dvd hq) U) R).restrict (normMap_mem_qNew (R := R) hU))
    (normMap_restrict_bijective hU hw)

/-- `prop:s02-Mhomprops`(d) (`s02-Mhom`): `qNewEquivKerPartial a = ν' a`. -/
theorem qNewEquivKerPartial_apply (hU : IsQLevel d q hq U)
    (hw : ∀ c : XB U, IsUnit ((wx U (Quotient.out c) : ℕ) : R)) (a : LinearMap.ker (partialHom d q hq U R)) :
    (qNewEquivKerPartial hU hw a : ZXdual (d.U0q q (coprime_of_not_dvd hq) U) R) =
      normMap (d.U0q q (coprime_of_not_dvd hq) U) R a :=
  rfl

end Trace

end Langlandscape.Tree
