import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Reduction

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolII/Parabolic.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (22): `IsGTFamily`, `gtValue`, `gt_family_derivative`, `hasDerivAt_exp_lin`, `hasDerivAt_family`, `heightMap_mul_K`, `heightMap_weyl`, `heightMap_weylInv`, `iota_neg_one`, `isGTFamily_weight`, `neg_one_mem_borel_map`, `simpleRoot_projABG`, `simpleRoot_weylAct`, `simpleRoot_yVec_sub`, `weight`, `weight_affine`, `weight_eq_y`, `weight_explicit`, `weight_invariant`, `weyl_inv_eq`, `weyl_inv_eq_neg`, `yVec_eq_smul`.
Dropped tagged IDs: `II.par.def:gt-family`, `II.par.def:gt-family-value`, `II.par.def:weight`, `II.par.thm:gt-family-derivative`, `II.par.thm:weight-affine`, `II.par.thm:weight-explicit`, `II.par.thm:weight-invariant`. -/

/-!
# Parabolic combinatorics, (G,T)-families and the weight (M7a, unit U4, items 25–35)

Lean counterpart of `vol2/ch-02-parabolic.tex` §§1–2: the index sets `𝒫 = {B, G}` and `𝒫(T) = {B, B̄}`, the height maps
`H_P` (`H_B̄(x) = w·H_B(w⁻¹x)`), the vectors `Y_P(x, T)`, the functions `θ_P` (normalization `vol(𝔞_B^G/ℤα^∨) = 1`),
(G,T)-families with a real parameter (D-GMF), their value `c_T`, and the weight `v(x, T)`. Owner: L2.

Design (W0 spike, `docs/notes/M7a-parabolic-spike.md`): `𝒫` and `𝒫(T)` are small tagged inductives with a hand-written
`Fintype` instance (`deriving Fintype` fails at the D1 pin); `Λ_λ` is extended by zero on `𝔞_G` (`Λ_λ(h) = λ·α(h)/2`);
the value `c_T` is `0` when the limit does not exist (literal convention of A); the weight is complex-valued like `c_T`,
its real value is `II.par.thm:weight-explicit`.
-/

open Filter Topology

namespace GL2TF

local notation "ι" => gl2Map (algebraMap ℚ Adele)

/-! ### §1 Parabolic subgroups and heights (items 25–27) -/

/-- The index set `𝒫 = {B, G}` of standard parabolic subgroups of `GL₂` (B-only plumbing for
`II.par.def:standard-parabolics`). -/
@[tf_aux "II.par.def:standard-parabolic-index"]
inductive ParStd
  | B
  | G
  deriving DecidableEq

/-- The index set `𝒫(T) = {B, B̄}` of parabolic subgroups with Levi component `T` (B-only plumbing for
`II.par.def:standard-parabolics`). -/
@[tf_aux "II.par.def:levi-parabolic-index"]
inductive ParT
  | B
  | Bbar
  deriving DecidableEq

/-- `𝒫(T)` is a finite type with elements `B, B̄` (hand-written: `deriving Fintype` fails at the D1 pin). -/
@[tf_aux "II.par.lem:levi-parabolic-fintype-instance"]
instance ParT.instFintype : Fintype ParT :=
  ⟨{.B, .Bbar}, fun x ↦ by cases x <;> simp⟩

/-- The subgroups: `P ∈ 𝒫 ∪ 𝒫(T)` stands for `P(R) ≤ GL₂(R)`, with `B(R)` the Borel subgroup, `B̄(R)` the opposite Borel
subgroup and `G(R) = GL₂(R)`. -/
@[tf_id "II.par.def:standard-parabolics"]
def parabolic (R : Type*) [CommRing R] : ParStd ⊕ ParT → Subgroup (GL (Fin 2) R)
  | .inl .B => borel R
  | .inl .G => ⊤
  | .inr .B => borel R
  | .inr .Bbar => oppositeBorel R

/-- The Weyl action `w(h₁, h₂) = (h₂, h₁)` on `𝔞_B` (B-only plumbing). -/
@[tf_aux "II.par.def:weyl-action-a"]
def weylAct (h : SpaceAB) : SpaceAB := ![h 1, h 0]

/-- The height maps `H_P : G(𝔸) → 𝔞_B`, `P ∈ 𝒫(T)`: `H_B = heightMap`, `H_B̄(x) = w·H_B(w⁻¹x)`. -/
@[tf_id "II.par.def:parabolic-height"]
noncomputable def heightP : ParT → GL (Fin 2) Adele → SpaceAB
  | .B, x => heightMap x
  | .Bbar, x => weylAct (heightMap ((weylElement Adele)⁻¹ * x))

/-- `Y_P(x, T) = (T_P − H_P(x))_B^G` with `T_B = T`, `T_B̄ = wT` (values in `𝔞_B`; they lie in `𝔞_B^G`,
`I.conv.def:projection-a-b-g`). -/
@[tf_id "II.par.def:y-vector"]
noncomputable def yVec (P : ParT) (x : GL (Fin 2) Adele) (T : SpaceAB) : SpaceAB :=
  projABG ((match P with
    | .B => T
    | .Bbar => weylAct T) - heightP P x)

namespace ParAux

/-- `w ∈ K`. -/
theorem weyl_mem_maxCompact : weylElement Adele ∈ maxCompactAdelic := by
  rw [mem_maxCompactAdelic_iff]
  refine ⟨?_, ?_⟩
  · have hw : compInf (weylElement Adele) = weylElement ℝ := by
      apply Units.ext; refine Matrix.ext fun i j ↦ ?_
      fin_cases i <;> fin_cases j <;> simp [compInf, gl2Map, weylElement]
    show Matrix.transpose ((compInf (weylElement Adele) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (compInf (weylElement Adele) : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [hw]; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [weylElement, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mem_maxCompactFin_iff_gl2Zhat]
    refine ⟨weylElement Zhat, ?_⟩
    apply Units.ext; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [gl2Zhat, gl2Map, compFin, weylElement]

end ParAux

open Matrix.GeneralLinearGroup in
/-- `H_B̄(n̄(u) diag(t₁, t₂) k) = (log|t₁|_𝔸, log|t₂|_𝔸)` for `k ∈ K` (B-only; remark (ii) after
`II.par.def:parabolic-height` in A). -/
@[tf_aux "II.par.lem:height-opposite-spec"]
theorem heightP_opposite_iwasawa (u : Adele) (t₁ t₂ : Idele) (k : GL (Fin 2) Adele) (hk : k ∈ maxCompactAdelic) :
    heightP .Bbar (oppositeUnipotentElt u * diagElt t₁ t₂ * k) =
      ![Real.log (ideleNorm t₁), Real.log (ideleNorm t₂)] := by
  have hwK := ParAux.weyl_mem_maxCompact
  have h1 : (weylElement Adele)⁻¹ * oppositeUnipotentElt u * diagElt t₁ t₂ =
      upperRightHom (-u) * diagElt t₂ t₁ * (weylElement Adele)⁻¹ := by
    have hinv : (weylElement Adele)⁻¹ = ⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by simp [Matrix.one_fin_two],
        by simp [Matrix.one_fin_two]⟩ := by
      rw [inv_eq_iff_eq_inv]; apply Units.ext; rfl
    rw [hinv]
    apply Units.ext; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp [oppositeUnipotentElt, diagElt, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : (weylElement Adele)⁻¹ * (oppositeUnipotentElt u * diagElt t₁ t₂ * k) =
      upperRightHom (-u) * diagElt t₂ t₁ * ((weylElement Adele)⁻¹ * k) := by
    rw [← mul_assoc, ← mul_assoc, h1, mul_assoc]
  rw [heightP, h2, heightMap_iwasawa _ _ _ _ (maxCompactAdelic.mul_mem (maxCompactAdelic.inv_mem hwK) hk)]
  funext i; fin_cases i <;> simp [weylAct]

/-! ### §2 (G,T)-families and the weight (items 28–35) -/

/-- The coroot `α^∨ = (1, −1) ∈ 𝔞_B^G` (B-only plumbing for `II.par.def:theta`). -/
@[tf_aux "II.par.def:coroot"]
def coroot : SpaceAB := ![1, -1]

/-- The linear form `Λ_λ` with `Λ_λ(α^∨) = λ`, extended by zero on `𝔞_G`: `Λ_λ(h) = λ·α(h)/2` (B-only plumbing for
`II.par.def:theta`). -/
@[tf_aux "II.par.def:lambda-form"]
noncomputable def lamForm (l : ℝ) (h : SpaceAB) : ℝ := l * (simpleRoot h / 2)

/-- `Λ_λ(α^∨) = λ` and `Λ_λ` vanishes on `𝔞_G` (B-only). -/
@[tf_aux "II.par.lem:lambda-form-spec"]
theorem lamForm_spec (l : ℝ) : lamForm l coroot = l ∧ ∀ r : ℝ, lamForm l ![r, r] = 0 := by
  refine ⟨?_, fun r ↦ ?_⟩
  · simp [lamForm, coroot, simpleRoot]
  · simp [lamForm, simpleRoot]

/-- `θ_B(λ) = λ`, `θ_B̄(λ) = −λ` (the Haar measure on `𝔞_B^G` normalized by `vol(𝔞_B^G/ℤα^∨) = 1`). -/
@[tf_id "II.par.def:theta"]
def theta : ParT → ℝ → ℝ
  | .B, l => l
  | .Bbar, l => -l

/-! ### Proof plumbing (untagged) -/

namespace ParAux

end ParAux

/-! ### Proof plumbing for item 35 (untagged): continuity of `H_B` on `G(𝔸)` -/

namespace ParAux

theorem bottomRowNorm_infEmb (g : GL (Fin 2) ℝ) :
    bottomRowNorm (infEmb g) =
      Real.sqrt ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2) := by
  have hv : ∀ p : Nat.Primes,
      max (Local.normAbs ℚ_[p] ((((infEmb g : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 0).2 p))
        (Local.normAbs ℚ_[p] ((((infEmb g : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 1).2 p)) = 1 := by
    intro p
    rw [Local.normAbs_padic, Local.normAbs_padic]
    show max ‖((1 : Matrix (Fin 2) (Fin 2) FinAdele) 1 0) p‖ ‖((1 : Matrix (Fin 2) (Fin 2) FinAdele) 1 1) p‖ = 1
    simp
  rw [bottomRowNorm, finprod_congr hv, finprod_one, mul_one]
  rfl

theorem continuous_heightMap_infEmb : Continuous fun g : GL (Fin 2) ℝ ↦ heightMap (infEmb g) := by
  have hpos : ∀ g : GL (Fin 2) ℝ,
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 :=
    fun g ↦ (bottomRowNorm_spec (infEmb g)).1
  have hs : Continuous fun g : GL (Fin 2) ℝ ↦
      Real.log (Real.sqrt ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2)) := by
    refine Continuous.log ?_ fun g ↦ (Real.sqrt_pos.mpr (hpos g)).ne'
    exact (((Units.continuous_val.matrix_elem 1 0).pow 2).add ((Units.continuous_val.matrix_elem 1 1).pow 2)).sqrt
  have hd : Continuous fun g : GL (Fin 2) ℝ ↦ Real.log (ideleNorm (Matrix.GeneralLinearGroup.det (infEmb g))) :=
    Continuous.log (ideleNorm_spec.1.comp (continuous_det_gl.comp continuous_infEmb))
      fun g ↦ (ideleNorm_spec.2.1 _).ne'
  refine continuous_pi fun i ↦ ?_
  simp only [heightMap, bottomRowNorm_infEmb]
  fin_cases i
  · exact hd.sub hs
  · exact hs

theorem heightMap_one : heightMap 1 = 0 := by
  have h := heightMap_diag 1 1
  rw [diagElt_hom.1, map_one, Real.log_one] at h
  rw [h]; funext i; fin_cases i <;> rfl

open Matrix.GeneralLinearGroup in
theorem heightMap_local (x₀ : GL (Fin 2) Adele) : ∃ c : SpaceAB, ∃ k₀ : GL (Fin 2) ℝ,
    ∀ x : GL (Fin 2) Adele, compFin (x₀⁻¹ * x) ∈ maxCompactFin →
      heightMap x = c + heightMap (infEmb (k₀ * compInf (x₀⁻¹ * x) * k₀⁻¹)) := by
  obtain ⟨b, hb, k, hk, rfl⟩ := iwasawa_adelic.1 x₀
  obtain ⟨y, t₁, t₂, rfl⟩ := borel_eq_n_t b hb
  refine ⟨heightMap (diagElt t₁ t₂), compInf k, fun x hx ↦ ?_⟩
  set a := compInf ((upperRightHom y * diagElt t₁ t₂ * k)⁻¹ * x) with ha
  set kf := compFin ((upperRightHom y * diagElt t₁ t₂ * k)⁻¹ * x) with hkf
  have h1 : (upperRightHom y * diagElt t₁ t₂ * k)⁻¹ * x = infEmb a * finEmb kf :=
    gl_adele_ext (by simp [a, compInf_infEmb, compInf_finEmb]) (by simp [kf, compFin_infEmb, compFin_finEmb])
  have h2 : k * infEmb a = infEmb (compInf k * a * (compInf k)⁻¹) * k :=
    gl_adele_ext (by simp [compInf_infEmb]) (by simp [compFin_infEmb])
  have hdec : x = upperRightHom y * diagElt t₁ t₂ * infEmb (compInf k * a * (compInf k)⁻¹) * (k * finEmb kf) := by
    calc x = (upperRightHom y * diagElt t₁ t₂ * k) * ((upperRightHom y * diagElt t₁ t₂ * k)⁻¹ * x) := by group
      _ = upperRightHom y * diagElt t₁ t₂ * (k * infEmb a) * finEmb kf := by rw [h1]; group
      _ = _ := by rw [h2]; group
  have hK : k * finEmb kf ∈ maxCompactAdelic := maxCompactAdelic.mul_mem hk
    ((mem_maxCompactAdelic_iff _).mpr ⟨by rw [compInf_finEmb]; exact maxCompactReal.one_mem,
      by rw [compFin_finEmb]; exact hx⟩)
  conv_lhs => rw [hdec]
  exact heightMap_equivariance.1 _ ⟨y, rfl⟩ _ ⟨rfl, rfl⟩ _ _ hK

theorem continuous_heightMap : Continuous heightMap := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨c, k₀, hc⟩ := heightMap_local x₀
  have hcF : Continuous (compFin : GL (Fin 2) Adele → GL (Fin 2) FinAdele) := continuous_gl2Map _ continuous_snd
  have hcI : Continuous (compInf : GL (Fin 2) Adele → GL (Fin 2) ℝ) := continuous_gl2Map _ continuous_fst
  have hU : {x | compFin (x₀⁻¹ * x) ∈ maxCompactFin} ∈ 𝓝 x₀ := by
    refine IsOpen.mem_nhds (isOpen_maxCompactFin.preimage (hcF.comp (continuous_const.mul continuous_id))) ?_
    simp [maxCompactFin.one_mem]
  refine ContinuousAt.congr ?_ (Filter.eventuallyEq_of_mem hU fun x hx ↦ (hc x hx).symm)
  refine (continuous_const.add (continuous_heightMap_infEmb.comp ?_)).continuousAt
  exact (continuous_const.mul (hcI.comp (continuous_const.mul continuous_id))).mul continuous_const

end ParAux

end GL2TF
