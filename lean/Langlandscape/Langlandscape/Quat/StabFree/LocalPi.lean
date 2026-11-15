/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.ImportDictionary

/-!
# `BrandtStabFree` part B, piece F (tex steps (i), (iii)–(v), local part at `ℓ`): the element `π`

This file proves `local_pi`, taking the global
PID core (piece E, `principality`) as the explicit hypothesis `hprin`.

Math (tex `lem:s03-stabfree`): from `γ ∈ Γ_x ∩ Γ_{xy}`, `γ ≠ ±1`, `y ∈ normNSet` (`nrd y = ℓ·w`):
- step (i): `unit_cases` (import, `AlgJL/VolIII/P2/Orders.lean`) applied to `γ ∈ unitGroup O_x`
  (`stabilizer_units`, `unitGroup_val_props`) gives `γ² = tγ - 1`, `t ∈ {-1,0,1}`.
- At `ℓ` (split, `hℓD`): put `X := localComponent d ℓ hℓD x`, `Y := localComponent d ℓ hℓD y`,
  `P := localComponent d ℓ hℓD (ι γ)`, `G := X⁻¹ * P * X`. Then `G ∈ GL2Zl ℓ` (from `γ ∈ Γ_x`,
  `localComponent_mem_GL2Zl`), `Y⁻¹ * G * Y ∈ GL2Zl ℓ` (from `γ ∈ Γ_{xy}`), `Y` has entries in
  `ℤ_ℓ` (`y ∈ Ô`: `localProj_mem_localLattice` + `iota_image_localLattice`) with
  `det Y = ℓ * (unit)` (`nrd` commutes with `localProj`; `det (ι z) = nrd z`).
- The lattice `Λ := Y • (standard ℤ_ℓ²)` is `G`-stable of index `ℓ` in `ℤ_ℓ²`. The ideal
  `𝔞 := {M ∈ 𝒪' := ℤ_ℓ[G] : M '' ℤ_ℓ² ⊆ Λ}` contains `ℓ𝒪'` and has index `ℓ`
  (`𝒪'/𝔞 ↪ End(ℤ_ℓ²/Λ) ≅ 𝔽_ℓ`, nonzero since `𝒪' '' ℤ_ℓ² = ℤ_ℓ² ⊄ Λ`). Via
  `A/ℓA ≅ 𝒪'/ℓ𝒪'` (both `≅ (ℤ/ℓ)[X]/(X²-tX+1)`, free on `1, X` resp. `1, G`) and `hprin`,
  `𝔞 = p(G)𝒪'` for some `p ∈ ℤ[X]` with `det p(G) = nrd (aeval γ p) = ℓ`. Then
  `Λ = p(G) '' ℤ_ℓ²`, so `Y⁻¹ * p(G) ∈ GL2Zl ℓ`.
- Output: `π := aeval γ p` (a unit since `nrd π = ℓ ≠ 0`), with
  `localComponent d ℓ hℓD (y⁻¹ * (x⁻¹ * ι π * x)) = Y⁻¹ * p(G) ∈ GL2Zl ℓ`.

Provenance: draft by mistral-large-4-0 via opencode (external, user-run; branch `abhijit/brandtstabfree`,
c170335d), integrated and audited by the Langlandscape agents.
-/

set_option autoImplicit false

namespace Langlandscape.StabFree.LocalPi

open GL2TF Langlandscape.Quat Langlandscape.Local Polynomial

variable {a b : ℤ}

/-- `A t := ℤ[X]/(X² - tX + 1)` (copy of `Langlandscape.StabFree.Principal.Zgam`; identified by `rfl` in the assembly). -/
abbrev Zgam (t : ℤ) : Type :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1)

/-- (copy of `Langlandscape.StabFree.Principal.Zgam.aeval_of_sq`) (`s03-stabfree`) -/
theorem Zgam.aeval_of_sq {t : ℤ} {γ : GL2TF.Quat.QuatAlg ℚ a b}
    (hg : γ ^ 2 = (t : ℚ) • γ - 1) :
    Polynomial.aeval γ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0 := by
  have hg' : γ ^ 2 = algebraMap ℚ (GL2TF.Quat.QuatAlg ℚ a b) (t : ℚ) * γ - 1 := by
    rw [Algebra.smul_def] at hg
    exact hg
  simp only [map_sub, map_add, map_pow, aeval_X, aeval_C, map_one, map_mul]
  have hcast : algebraMap ℤ (GL2TF.Quat.QuatAlg ℚ a b) t =
      algebraMap ℚ (GL2TF.Quat.QuatAlg ℚ a b) (t : ℚ) := by
    push_cast
    rfl
  rw [hcast, hg']
  abel

/-- (copy of `Langlandscape.StabFree.Principal.Zgam.toB`) Evaluation `A t → B`, `X ↦ γ`. -/
noncomputable def Zgam.toB (t : ℤ) (γ : GL2TF.Quat.QuatAlg ℚ a b)
    (h : Polynomial.aeval γ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) :
    Zgam t →+* GL2TF.Quat.QuatAlg ℚ a b :=
  Ideal.Quotient.lift (Ideal.span {Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1})
    (Polynomial.aeval γ).toRingHom (by
      intro x hx
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨q, rfl⟩ := hx
      rw [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h, zero_mul])

/-! ### Stage F helpers -/

section Helpers

/-- `aeval` of a `ℤ[X]`-polynomial commutes with ring homs. (`s03-stabfree`) -/
theorem map_aeval_ringHom {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (x : A) (p : ℤ[X]) :
    φ (Polynomial.aeval x p) = Polynomial.aeval (φ x) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c => simp [Polynomial.aeval_monomial]

/-- `aeval μ p` (over `ℤ`) as `eval₂` along `Int.castRingHom`. (`s03-stabfree`) -/
theorem aeval_int_eval₂ {S : Type*} [Ring S] (μ : S) (p : ℤ[X]) :
    Polynomial.aeval μ p = p.eval₂ (Int.castRingHom S) μ := by
  rw [Polynomial.aeval_def, algebraMap_int_eq]

/-- `Zgam.toB` on `mk p` is `aeval γ p`. (`s03-stabfree`) -/
theorem Zgam.toB_mk {t : ℤ} {γ : GL2TF.Quat.QuatAlg ℚ a b}
    (h : Polynomial.aeval γ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) (p : ℤ[X]) :
    Zgam.toB t γ h (AdjoinRoot.mk _ p) = Polynomial.aeval γ p := by
  show Ideal.Quotient.lift _ (Polynomial.aeval γ).toRingHom _ (Ideal.Quotient.mk _ p) = _
  exact (Ideal.Quotient.lift_mk _ _ _).trans rfl

/-- Step (i) of `lem:s03-stabfree`: `γ ∈ Γ_x`, `γ ≠ ±1` give `t ∈ {-1,0,1}` with `γ² = tγ - 1`. -/
theorem step_i (d : DefiniteData) {x : (BHat d.a d.b)ˣ} {γ : (QuatAlg ℚ d.a d.b)ˣ}
    (hγx : γ ∈ Gam d.Ohat x) (hpm : γ ∉ pmOne) :
    ∃ t : ℤ, (t = -1 ∨ t = 0 ∨ t = 1) ∧
      ((γ : QuatAlg ℚ d.a d.b) ^ 2 = (t : ℚ) • (γ : QuatAlg ℚ d.a d.b) - 1) := by
  obtain ⟨Ox, -, hGam⟩ := (GL2TF.Quat.stabilizer_units d.O.1 x).1
  have hγOx : γ ∈ GL2TF.Quat.unitGroup Ox := by
    rw [← hGam]; exact hγx
  obtain ⟨hγmem, hγnrd⟩ := GL2TF.Quat.unitGroup_val_props d.ha d.hb Ox γ hγOx
  rcases GL2TF.Quat.unit_cases d.ha d.hb Ox hγmem hγnrd with h1 | h2 | h3 | h4 | h5
  · exact absurd ((mem_pmOne_iff γ).2 (Or.inl (Units.ext h1))) hpm
  · exact absurd ((mem_pmOne_iff γ).2 (Or.inr (Units.ext h2))) hpm
  · exact ⟨0, Or.inr (Or.inl rfl), by simpa using h3⟩
  · exact ⟨1, Or.inr (Or.inr rfl), by simpa using h4⟩
  · exact ⟨-1, Or.inl rfl, by simpa using h5⟩

variable {K : Type*} [Field K] [CharZero K]

/-- Copy of the import's private `hl_trace_aux` (`AlgJL/VolIII/Brandt/HeckeLocal.lean`). (`s03-stabfree`) -/
theorem trace_aux' {a b : ℤ} (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (u v : QuatAlg K a b) (c : K) (hc : c ≠ 0) (h1 : u * v * v = c • u)
    (h2 : v * u * v = -(u * v * v)) :
    (s u).trace = 0 := by
  have h3 : (s (u * v * v)).trace = 0 := by
    have e1 : (s (u * v * v)).trace = (s (v * u * v)).trace := by
      simp only [map_mul]
      rw [Matrix.trace_mul_comm, ← mul_assoc]
    rw [h2, map_neg, Matrix.trace_neg] at e1
    linear_combination e1 / 2
  rw [h1, map_smul, Matrix.trace_smul, smul_eq_zero] at h3
  exact h3.resolve_left hc

/-- Copy of the import's private `hl_det_eq_nrd` (`AlgJL/VolIII/Brandt/HeckeLocal.lean`):
`det (ι x) = nrd x` for a splitting `ι`. (`s03-stabfree`) -/
theorem det_eq_nrd {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : QuatAlg K a b) :
    (s x).det = GL2TF.Quat.nrd x := by
  set i : QuatAlg K a b := ⟨0, 1, 0, 0⟩ with hi
  set j : QuatAlg K a b := ⟨0, 0, 1, 0⟩ with hj
  set k : QuatAlg K a b := ⟨0, 0, 0, 1⟩ with hk
  have ha' : (a : K) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hb' : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb
  have ti : (s i).trace = 0 :=
    trace_aux' s i j b hb' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tj : (s j).trace = 0 :=
    trace_aux' s j i a ha' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tk : (s k).trace = 0 :=
    trace_aux' s k i a ha' (by ext <;> simp [hi, hk]) (by ext <;> simp [hi, hk])
  have hdec : ∀ x : QuatAlg K a b,
      x = algebraMap K (QuatAlg K a b) x.re + x.imI • i + x.imJ • j + x.imK • k := by
    intro x
    ext <;> simp [hi, hj, hk, QuaternionAlgebra.algebraMap_eq]
  have htr : ∀ x : QuatAlg K a b, (s x).trace = 2 * x.re := by
    intro x
    conv_lhs => rw [hdec x]
    simp only [map_add, map_smul, AlgHom.commutes, Matrix.trace_add, Matrix.trace_smul, ti, tj, tk,
      smul_zero, add_zero]
    simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]
  have hdet : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = (M.trace ^ 2 - (M * M).trace) / 2 := by
    intro M
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hdet, ← map_mul, htr, htr]
  simp only [GL2TF.Quat.nrd, QuaternionAlgebra.re_mul]
  ring

/-- `nrd` commutes with base change. (`s03-stabfree`) -/
theorem nrd_baseChange' {R S : Type*} [CommRing R] [CommRing S] {a b : ℤ} (f : R →+* S)
    (x : QuatAlg R a b) :
    GL2TF.Quat.nrd (GL2TF.Quat.baseChange a b f x) = f (GL2TF.Quat.nrd x) :=
  ((GL2TF.Quat.nrd_trd_basic (R := R) (a := a) (b := b)).2.2.2 S f x).1

/-- `nrd` commutes with the `ℓ`-component projection `B̂ → B_ℓ`. (`s03-stabfree`) -/
theorem nrd_localProj' {a b : ℤ} {ℓ : ℕ} [Fact ℓ.Prime] (y : BHat a b) :
    GL2TF.Quat.nrd (localProj a b ℓ y) =
      adeleProj ℓ (GL2TF.Quat.nrd (y : QuatAlg FinAdele a b)) :=
  ((GL2TF.Quat.nrd_trd_basic (R := FinAdele) (a := a) (b := b)).2.2.2 ℚ_[ℓ] (adeleProj ℓ) y).1

end Helpers

/-! ### M2: the local matrices `X`, `Y`, `P`, `G` at `ℓ` -/

section M2

variable (d : DefiniteData) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `det (ι_ℓ z) = nrd z` at the split prime `ℓ`. (`s03-stabfree`) -/
theorem det_iota' (x : QuatAlg ℚ_[ℓ] d.a d.b) :
    (d.iota ℓ hℓ x).det = GL2TF.Quat.nrd x := by
  obtain ⟨ha, hb, -⟩ := d.hD
  exact det_eq_nrd (ne_of_lt ha) (ne_of_lt hb) (d.iota ℓ hℓ).toAlgHom x

/-- `G := X⁻¹ P X ∈ GL2Zl ℓ` (from `γ ∈ Γ_x`). (`s03-stabfree`) -/
theorem G_mem_GL2Zl {x : (BHat d.a d.b)ˣ} {γ : (QuatAlg ℚ d.a d.b)ˣ}
    (hγx : γ ∈ Gam d.Ohat x) :
    (localComponent d ℓ hℓ x)⁻¹ *
        localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) *
        localComponent d ℓ hℓ x ∈ GL2Zl ℓ := by
  have h : x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom γ * x ∈ d.Ohat :=
    (mem_Gam_iff d.Ohat x γ).1 hγx
  have h2 : localComponent d ℓ hℓ (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom γ * x) ∈
      GL2Zl ℓ := localComponent_mem_GL2Zl h
  rw [map_mul, map_mul, map_inv] at h2
  exact h2

/-- `Y⁻¹ G Y ∈ GL2Zl ℓ` (from `γ ∈ Γ_{xy}`). (`s03-stabfree`) -/
theorem YGY_mem_GL2Zl {x y : (BHat d.a d.b)ˣ} {γ : (QuatAlg ℚ d.a d.b)ˣ}
    (hγxy : γ ∈ Gam d.Ohat (x * y)) :
    (localComponent d ℓ hℓ y)⁻¹ *
      ((localComponent d ℓ hℓ x)⁻¹ *
        localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) *
        localComponent d ℓ hℓ x) * localComponent d ℓ hℓ y ∈ GL2Zl ℓ := by
  have h : (x * y)⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom γ * (x * y) ∈ d.Ohat :=
    (mem_Gam_iff d.Ohat (x * y) γ).1 hγxy
  have e : (localComponent d ℓ hℓ y)⁻¹ *
      ((localComponent d ℓ hℓ x)⁻¹ *
        localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) *
        localComponent d ℓ hℓ x) * localComponent d ℓ hℓ y
      = localComponent d ℓ hℓ ((x * y)⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom γ *
          (x * y)) := by
    simp only [map_mul, map_inv, mul_inv_rev]
    group
  rw [e]
  exact localComponent_mem_GL2Zl h

/-- Entries of `Y = localComponent y` lie in `ℤ_[ℓ]` (`y ∈ normNSet` gives `y ∈ Ô`). (`s03-stabfree`) -/
theorem Y_integral {y : (BHat d.a d.b)ˣ} (hy : y ∈ GL2TF.Quat.normNSet d.O.1 ℓ) (i j : Fin 2) :
    ‖((localComponent d ℓ hℓ y : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j‖ ≤ 1 := by
  rw [localComponent_val]
  exact (d.mem_localLattice_iff_iota ℓ hℓ _).1
    (localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hy.1 ℓ) i j

/-- `det Y = ℓ * v` for a unit `v ∈ ℤ_[ℓ]ˣ` (`nrd y = ℓ · w` with `w ∈ Ẑ^×`). (`s03-stabfree`) -/
theorem det_Y {y : (BHat d.a d.b)ˣ} (hy : y ∈ GL2TF.Quat.normNSet d.O.1 ℓ) :
    ∃ v : ℤ_[ℓ]ˣ,
      ((localComponent d ℓ hℓ y : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]).det
        = (ℓ : ℚ_[ℓ]) * ((v : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  obtain ⟨u, hu⟩ := hy.2
  obtain ⟨v, hv⟩ : ∃ v : ℤ_[ℓ]ˣ,
      ((v : ℤ_[ℓ]) : ℚ_[ℓ]) = (((u : GL2TF.Zhat) : FinAdele)) (primeIdx ℓ) :=
    (GL2TF.zhat_units_explicit (((u : GL2TF.Zhat) : FinAdele))).1 ⟨u, rfl⟩ (primeIdx ℓ)
  have hdet : ((localComponent d ℓ hℓ y : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]).det
      = adeleProj ℓ (GL2TF.Quat.nrd ((y : BHat d.a d.b) : QuatAlg FinAdele d.a d.b)) := by
    rw [localComponent_val, det_iota' d, nrd_localProj']
  have e1 : adeleProj ℓ (ℓ : FinAdele) = (ℓ : ℚ_[ℓ]) := rfl
  have e2 : adeleProj ℓ (((u : GL2TF.Zhat) : FinAdele)) = ((v : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    show (((u : GL2TF.Zhat) : FinAdele) (primeIdx ℓ) : ℚ_[ℓ]) = ((v : ℤ_[ℓ]) : ℚ_[ℓ])
    exact hv.symm
  refine ⟨v, ?_⟩
  rw [hdet, hu, map_mul, e1, e2]

/-- `det G = 1` (the reduced norm of `γ` is `1`). (`s03-stabfree`) -/
theorem det_G {x : (BHat d.a d.b)ˣ} {γ : (QuatAlg ℚ d.a d.b)ˣ}
    (hnrd : GL2TF.Quat.nrd (γ : QuatAlg ℚ d.a d.b) = 1) :
    (Units.val ((localComponent d ℓ hℓ x)⁻¹ *
        localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) *
        localComponent d ℓ hℓ x)).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj' (localComponent d ℓ hℓ x) _,
    localComponent_finEmbed, det_iota' d, nrd_baseChange', hnrd, map_one]

end M2

/-! ### M3: integrality infrastructure over `ℤ_[p]` -/

section M3

open scoped Matrix

variable {p : ℕ} [Fact p.Prime]

/-- Entrywise `ℤ_[p]`-lift of an integral matrix over `ℚ_[p]`. -/
def intMat (M : Matrix (Fin 2) (Fin 2) ℚ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => ⟨M i j, h i j⟩

/-- `s03-stabfree`: auxiliary lemma `intMat_map` (`lem:s03-stabfree`). -/
theorem intMat_map (M : Matrix (Fin 2) (Fin 2) ℚ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    (intMat M h).map (algebraMap ℤ_[p] ℚ_[p]) = M := by
  ext i j
  rfl

/-- Reduction mod `p` of a matrix over `ℤ_[p]`. -/
noncomputable def redMat (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  M.map PadicInt.toZMod

/-- `s03-stabfree`: auxiliary lemma `redMat_det` (`lem:s03-stabfree`). -/
theorem redMat_det (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) :
    (redMat M).det = PadicInt.toZMod M.det :=
  (RingHom.map_det _ _).symm

/-- Reduction mod `p` of a vector over `ℤ_[p]`. -/
noncomputable def redVec (v : Fin 2 → ℤ_[p]) : Fin 2 → ZMod p := fun i => PadicInt.toZMod (v i)

/-- `s03-stabfree`: auxiliary lemma `redVec_mulVec` (`lem:s03-stabfree`). -/
theorem redVec_mulVec (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (v : Fin 2 → ℤ_[p]) :
    redVec (M *ᵥ v) = redMat M *ᵥ redVec v :=
  funext fun i => RingHom.map_mulVec PadicInt.toZMod M v i

/-- `s03-stabfree`: auxiliary lemma `redVec_surjective` (`lem:s03-stabfree`). -/
theorem redVec_surjective : Function.Surjective (redVec (p := p)) := by
  intro w
  choose v hv using fun i => ZMod.ringHom_surjective PadicInt.toZMod (w i)
  exact ⟨v, funext hv⟩

/-- The kernel of `redVec` is exactly `p • ⊤`. (`s03-stabfree`) -/
theorem redVec_eq_zero_iff (v : Fin 2 → ℤ_[p]) :
    redVec v = 0 ↔ ∃ z : Fin 2 → ℤ_[p], v = (p : ℤ_[p]) • z := by
  have hker : RingHom.ker (PadicInt.toZMod (p := p)) = Ideal.span {(p : ℤ_[p])} := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  have hdvd : redVec v = 0 → ∀ i, (p : ℤ_[p]) ∣ v i := fun h i =>
    Ideal.mem_span_singleton.1 (hker ▸ RingHom.mem_ker.2 (funext_iff.1 h i))
  constructor
  · intro h
    obtain ⟨z, hz⟩ : ∃ z : Fin 2 → ℤ_[p], ∀ i, v i = (p : ℤ_[p]) * z i := by
      choose z hz using fun i => (show ∃ c, v i = (p : ℤ_[p]) * c from hdvd h i)
      exact ⟨z, hz⟩
    refine ⟨z, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul]
    exact hz i
  · rintro ⟨z, rfl⟩
    funext i
    show PadicInt.toZMod ((p : ℤ_[p]) • z i) = (0 : ZMod p)
    rw [smul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- Powers of an integral matrix over `ℚ_[p]` have integral entries. (`s03-stabfree`) -/
theorem norm_pow_entry_le_one {M : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (h : ∀ i j, ‖M i j‖ ≤ 1) (n : ℕ) (i j : Fin 2) : ‖(M ^ n) i j‖ ≤ 1 := by
  induction n generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp
  | succ n hn =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact norm_mul_le_one (hn i 0) (h 0 j)
      · exact norm_mul_le_one (hn i 1) (h 1 j)

/-- `aeval` of an integral matrix at a `ℤ[X]`-polynomial has integral entries. (`s03-stabfree`) -/
theorem norm_aeval_le_one {M : Matrix (Fin 2) (Fin 2) ℚ_[p]} (h : ∀ i j, ‖M i j‖ ≤ 1)
    (q : ℤ[X]) (i j : Fin 2) : ‖(Polynomial.aeval M q) i j‖ ≤ 1 := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) fun k _ => ?_
  rw [Matrix.smul_apply, zsmul_eq_mul]
  have hzk : ‖(q.coeff k : ℚ_[p])‖ ≤ 1 := by
    have e : (q.coeff k : ℚ_[p]) = ((q.coeff k : ℤ_[p]) : ℚ_[p]) := by push_cast; rfl
    rw [e]
    exact PadicInt.norm_le_one _
  exact norm_mul_le_one hzk (norm_pow_entry_le_one h k i j)

end M3

/-! ### M3b: mod-`ℓ` linear algebra over a field -/

section M3b

open scoped Matrix

variable {F : Type*} [Field F]

/-- If `G * B = B * H`, the range of `B` is stable under `G`. (`s03-stabfree`) -/
theorem range_stable (B G H : Matrix (Fin 2) (Fin 2) F) (hcomm : G * B = B * H) :
    LinearMap.range (Matrix.mulVecLin B) ≤
      (LinearMap.range (Matrix.mulVecLin B)).comap (Matrix.mulVecLin G) := by
  intro v hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hv
  rw [Submodule.mem_comap, ← hw]
  refine ⟨H *ᵥ w, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [hcomm]

/-- A nonzero singular `2×2` matrix over a field has `1`-dimensional range. (`s03-stabfree`) -/
theorem finrank_range_mulVecLin (B : Matrix (Fin 2) (Fin 2) F) (hdet : B.det = 0) (hB : B ≠ 0) :
    Module.finrank F (LinearMap.range (Matrix.mulVecLin B)) = 1 := by
  have h2 : Module.finrank F (Fin 2 → F) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hsplit := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [h2] at hsplit
  have hker : LinearMap.ker (Matrix.mulVecLin B) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    rw [Submodule.ne_bot_iff]
    exact ⟨v, LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hv0), hv⟩
  have hker1 : 1 ≤ Module.finrank F (LinearMap.ker (Matrix.mulVecLin B)) :=
    Submodule.one_le_finrank_iff.2 hker
  have hrange : LinearMap.range (Matrix.mulVecLin B) ≠ ⊥ := by
    obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hB (by ext i j; exact h i j)
    rw [Submodule.ne_bot_iff]
    refine ⟨B *ᵥ Pi.single j 1, LinearMap.mem_range.2 ⟨Pi.single j 1, ?_⟩, ?_⟩
    · rw [Matrix.mulVecLin_apply]
    · intro h
      have := congrFun h i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
      exact hij this
  have hrange1 : 1 ≤ Module.finrank F (LinearMap.range (Matrix.mulVecLin B)) :=
    Submodule.one_le_finrank_iff.2 hrange
  omega

/-- On the `1`-dimensional quotient by the range of `B`, the endomorphism induced by `G`
is a scalar. (`s03-stabfree`) -/
theorem exists_eq_smul_id_mapQ (B G H : Matrix (Fin 2) (Fin 2) F) (hdet : B.det = 0)
    (hB : B ≠ 0) (hcomm : G * B = B * H) :
    ∃ μ : F,
      (LinearMap.range (Matrix.mulVecLin B)).mapQ (LinearMap.range (Matrix.mulVecLin B))
          (Matrix.mulVecLin G) (range_stable B G H hcomm) =
        μ • (LinearMap.id : Module.End F ((Fin 2 → F) ⧸ LinearMap.range (Matrix.mulVecLin B))) := by
  set S := LinearMap.range (Matrix.mulVecLin B) with hS
  have hfin : Module.finrank F S = 1 := finrank_range_mulVecLin B hdet hB
  have h2 : Module.finrank F (Fin 2 → F) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hquot : Module.finrank F ((Fin 2 → F) ⧸ S) = 1 := by
    have h := S.finrank_quotient_add_finrank
    rw [h2, hfin] at h
    omega
  have hne : ∃ v0 : (Fin 2 → F) ⧸ S, v0 ≠ 0 := by
    have hpos : 0 < Module.finrank F ((Fin 2 → F) ⧸ S) := by rw [hquot]; norm_num
    exact Module.finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨v0, hv0⟩ := hne
  have hspan : Module.finrank F (F ∙ v0) = 1 := finrank_span_singleton hv0
  have htop : (F ∙ v0 : Submodule F ((Fin 2 → F) ⧸ S)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hspan, hquot])
  set f := S.mapQ S (Matrix.mulVecLin G) (range_stable B G H hcomm) with hf
  have hfv0 : f v0 ∈ (F ∙ v0 : Submodule F ((Fin 2 → F) ⧸ S)) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hfv0
  refine ⟨μ, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  have hx : x ∈ (⊤ : Submodule F ((Fin 2 → F) ⧸ S)) := Submodule.mem_top
  rw [← htop] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
  rw [← hc, map_smul, ← hμ, smul_comm]

/-- Powers of a scalar endomorphism. (`s03-stabfree`) -/
theorem pow_smul_id_apply {Q : Type*} [AddCommGroup Q] [Module F Q] {μ : F}
    {f : Module.End F Q} (hf : f = μ • LinearMap.id) (n : ℕ) (x : Q) :
    (f ^ n) x = μ ^ n • x := by
  induction n generalizing x with
  | zero => simp
  | succ n hn =>
      rw [pow_succ f, Module.End.mul_apply, hn, hf, LinearMap.smul_apply, LinearMap.id_apply,
        smul_smul, ← pow_succ μ]

/-- `aeval` of a scalar endomorphism is the scalar `aeval`. (`s03-stabfree`) -/
theorem aeval_smul_id_apply {Q : Type*} [AddCommGroup Q] [Module F Q] {μ : F}
    {f : Module.End F Q} (hf : f = μ • LinearMap.id) (q : ℤ[X]) (x : Q) :
    (Polynomial.aeval f q) x = (Polynomial.aeval μ q) • x := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_smul]
  | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        pow_smul_id_apply hf n x, Algebra.algebraMap_eq_smul_one (R := ℤ) (A := Module.End F Q),
        LinearMap.smul_apply, Module.End.one_apply, ← Int.cast_smul_eq_zsmul (R := F),
        ← smul_smul, algebraMap_int_eq]
      rfl

/-- Naturality of `mkQ` with `aeval`. (`s03-stabfree`) -/
theorem mkQ_pow_mulVec (B G H : Matrix (Fin 2) (Fin 2) F) (hcomm : G * B = B * H)
    (n : ℕ) (v : Fin 2 → F) :
    (LinearMap.range (Matrix.mulVecLin B)).mkQ ((G ^ n) *ᵥ v) =
      (((LinearMap.range (Matrix.mulVecLin B)).mapQ (LinearMap.range (Matrix.mulVecLin B))
        (Matrix.mulVecLin G) (range_stable B G H hcomm)) ^ n)
        ((LinearMap.range (Matrix.mulVecLin B)).mkQ v) := by
  set S := LinearMap.range (Matrix.mulVecLin B) with hS
  set f := S.mapQ S (Matrix.mulVecLin G) (range_stable B G H hcomm) with hf
  induction n generalizing v with
  | zero => simp
  | succ n hn =>
      rw [pow_succ G, ← Matrix.mulVec_mulVec, hn, pow_succ f, Module.End.mul_apply]
      have h1 : S.mkQ (G *ᵥ v) = f (S.mkQ v) := by
        rw [← Matrix.mulVecLin_apply, hf, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.mapQ_apply]
      rw [h1]

/-- Naturality of `mkQ` with `aeval` at an integer polynomial. (`s03-stabfree`) -/
theorem mkQ_aeval_mulVec (B G H : Matrix (Fin 2) (Fin 2) F) (hcomm : G * B = B * H)
    (q : ℤ[X]) (v : Fin 2 → F) :
    (LinearMap.range (Matrix.mulVecLin B)).mkQ ((Polynomial.aeval G q) *ᵥ v) =
      Polynomial.aeval
        ((LinearMap.range (Matrix.mulVecLin B)).mapQ (LinearMap.range (Matrix.mulVecLin B))
          (Matrix.mulVecLin G) (range_stable B G H hcomm)) q
        ((LinearMap.range (Matrix.mulVecLin B)).mkQ v) := by
  set S := LinearMap.range (Matrix.mulVecLin B) with hS
  set f := S.mapQ S (Matrix.mulVecLin G) (range_stable B G H hcomm) with hf
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mulVec, LinearMap.add_apply, hp, hq]
  | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      have e1 : (algebraMap ℤ (Matrix (Fin 2) (Fin 2) F) c * G ^ n) *ᵥ v
          = c • (G ^ n *ᵥ v) := by
        rw [← Algebra.smul_def, Matrix.smul_mulVec]
      have e2 : (algebraMap ℤ (Module.End F ((Fin 2 → F) ⧸ S)) c * f ^ n) (S.mkQ v)
          = c • ((f ^ n) (S.mkQ v)) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
      rw [e1, map_zsmul, mkQ_pow_mulVec B G H hcomm n v, e2]

/-- If `q(μ) = 0`, the range of `aeval G q` is contained in the range of `B`. (`s03-stabfree`) -/
theorem range_aeval_le_range (B G H : Matrix (Fin 2) (Fin 2) F) (hcomm : G * B = B * H)
    (q : ℤ[X]) (μ : F)
    (hμ : (LinearMap.range (Matrix.mulVecLin B)).mapQ (LinearMap.range (Matrix.mulVecLin B))
        (Matrix.mulVecLin G) (range_stable B G H hcomm) = μ • LinearMap.id)
    (hroot : Polynomial.aeval μ q = 0) :
    LinearMap.range (Matrix.mulVecLin (Polynomial.aeval G q)) ≤
      LinearMap.range (Matrix.mulVecLin B) := by
  intro v hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hv
  rw [← hw]
  have hkey : (LinearMap.range (Matrix.mulVecLin B)).mkQ ((Polynomial.aeval G q) *ᵥ w) = 0 := by
    rw [mkQ_aeval_mulVec B G H hcomm q w, aeval_smul_id_apply hμ q, hroot, zero_smul]
  exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (Matrix.mulVecLin B))).1
    (show Submodule.Quotient.mk ((Polynomial.aeval G q) *ᵥ w) = 0 from hkey)

end M3b

/-! ### M3b₂: extracting the scalar root from `aeval G q = 0` -/

section M3b2

open scoped Matrix

variable {F : Type*} [Field F]

/-- The quotient by the range of a nonzero singular `B` is nontrivial. (`s03-stabfree`) -/
theorem exists_ne_zero_mkQ (B : Matrix (Fin 2) (Fin 2) F) (hdet : B.det = 0) (hB : B ≠ 0) :
    ∃ v : Fin 2 → F, (LinearMap.range (Matrix.mulVecLin B)).mkQ v ≠ 0 := by
  set S := LinearMap.range (Matrix.mulVecLin B) with hS
  have hfin : Module.finrank F S = 1 := finrank_range_mulVecLin B hdet hB
  have h2 : Module.finrank F (Fin 2 → F) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hquot : Module.finrank F ((Fin 2 → F) ⧸ S) = 1 := by
    have h := S.finrank_quotient_add_finrank
    rw [h2, hfin] at h
    omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by rw [hquot]; norm_num)
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective S x
  exact ⟨v, by rw [hv]; exact hx⟩

/-- If `aeval G q = 0` and the quotient endomorphism is `μ • id`, then `aeval μ q = 0`. (`s03-stabfree`) -/
theorem aeval_root_of_mapQ (B G H : Matrix (Fin 2) (Fin 2) F) (hcomm : G * B = B * H)
    (q : ℤ[X]) (μ : F) (hdet : B.det = 0) (hB : B ≠ 0)
    (hμ : (LinearMap.range (Matrix.mulVecLin B)).mapQ (LinearMap.range (Matrix.mulVecLin B))
        (Matrix.mulVecLin G) (range_stable B G H hcomm) = μ • LinearMap.id)
    (hq : Polynomial.aeval G q = 0) :
    Polynomial.aeval μ q = 0 := by
  obtain ⟨v, hv⟩ := exists_ne_zero_mkQ B hdet hB
  have h1 := mkQ_aeval_mulVec B G H hcomm q v
  rw [hq, Matrix.zero_mulVec, map_zero] at h1
  rw [aeval_smul_id_apply hμ q] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hv

end M3b2

/-! ### M3c: lifting from mod-`p` range inclusion to `ℤ_[p]` -/

section M3c

open scoped Matrix

variable {p : ℕ} [Fact p.Prime]

/-- `redVec` respects subtraction. (`s03-stabfree`) -/
theorem redVec_sub (a b : Fin 2 → ℤ_[p]) : redVec (a - b) = redVec a - redVec b := by
  funext i
  simp only [redVec, Pi.sub_apply, map_sub]

/-- The entrywise reduction `Matrix ℤ_[p] → Matrix (ZMod p)` as a `ℤ`-algebra hom. -/
noncomputable def toZModMatAlgHom :
    Matrix (Fin 2) (Fin 2) ℤ_[p] →ₐ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p) :=
  AlgHom.mk' PadicInt.toZMod.mapMatrix fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.mapMatrix_apply,
      Matrix.map_algebraMap r PadicInt.toZMod (map_zero _)
        (by show PadicInt.toZMod (r : ℤ_[p]) = (r : ZMod p); exact map_intCast PadicInt.toZMod r)]

/-- `aeval` commutes with reduction mod `p`. (`s03-stabfree`) -/
theorem map_aeval_matrix (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (q : ℤ[X]) :
    (Polynomial.aeval M q).map PadicInt.toZMod = Polynomial.aeval (redMat M) q :=
  (Polynomial.aeval_algHom_apply toZModMatAlgHom M q).symm

/-- If `det Y' = p * v` with `v` a unit, then `p • w` lies in the range of `Y'` for every `w`. (`s03-stabfree`) -/
theorem p_smul_mem_range (Y' : Matrix (Fin 2) (Fin 2) ℤ_[p]) {v : ℤ_[p]ˣ}
    (hdet : Y'.det = (p : ℤ_[p]) * (v : ℤ_[p])) (w : Fin 2 → ℤ_[p]) :
    (p : ℤ_[p]) • w ∈ LinearMap.range (Matrix.mulVecLin Y') := by
  refine ⟨Matrix.adjugate Y' *ᵥ (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • w), ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec, hdet, smul_smul, mul_assoc, Units.mul_inv, mul_one]

/-- Lifting lemma: mod-`p` range inclusion plus `det Y' = p * v` (`v` a unit) gives the
range inclusion over `ℤ_[p]`. (`s03-stabfree`) -/
theorem mulVec_mem_range_of_red (Y' N' : Matrix (Fin 2) (Fin 2) ℤ_[p]) {v : ℤ_[p]ˣ}
    (hdet : Y'.det = (p : ℤ_[p]) * (v : ℤ_[p]))
    (hsub : LinearMap.range (Matrix.mulVecLin (redMat N')) ≤
      LinearMap.range (Matrix.mulVecLin (redMat Y')))
    (w : Fin 2 → ℤ_[p]) :
    N' *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin Y') := by
  have h1 : redVec (N' *ᵥ w) ∈ LinearMap.range (Matrix.mulVecLin (redMat N')) :=
    LinearMap.mem_range.2 ⟨redVec w, by rw [Matrix.mulVecLin_apply, ← redVec_mulVec]⟩
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hsub h1)
  obtain ⟨z, hz⟩ := redVec_surjective u
  have h2 : redVec (Y' *ᵥ z - N' *ᵥ w) = 0 := by
    rw [redVec_sub, redVec_mulVec, hz, ← hu, Matrix.mulVecLin_apply, sub_self]
  obtain ⟨c, hc⟩ := (redVec_eq_zero_iff _).1 h2
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 (p_smul_mem_range Y' hdet c)
  have ha' : Y' *ᵥ a = (p : ℤ_[p]) • c := by
    rw [← Matrix.mulVecLin_apply]; exact ha
  refine ⟨z - a, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_sub, ha', ← hc, sub_sub_cancel]

/-- `redMat` is multiplicative. (`s03-stabfree`) -/
theorem redMat_mul (A B : Matrix (Fin 2) (Fin 2) ℤ_[p]) :
    redMat (A * B) = redMat A * redMat B :=
  Matrix.map_mul

/-- `redVec` of a column is the column of `redMat`. (`s03-stabfree`) -/
theorem redVec_col (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (j : Fin 2) :
    redVec (M.col j) = (redMat M).col j :=
  funext fun _ => rfl

end M3c

/-! ### M4: conjugation and entrywise ring homs -/

section M4

/-- Conjugation by a unit, as a ring hom. -/
def conjUnit {R : Type*} [Ring R] (u : Rˣ) : R →+* R where
  toFun x := (u : R) * x * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

/-- `s03-stabfree`: auxiliary lemma `conjUnit_apply` (`lem:s03-stabfree`). -/
@[simp]
theorem conjUnit_apply {R : Type*} [Ring R] (u : Rˣ) (x : R) :
    conjUnit u x = (u : R) * x * ((u⁻¹ : Rˣ) : R) := rfl

/-- `aeval` commutes with conjugation by a unit. (`s03-stabfree`) -/
theorem aeval_conj {R : Type*} [Ring R] (u : Rˣ) (M : R) (q : ℤ[X]) :
    Polynomial.aeval (((u⁻¹ : Rˣ) : R) * M * (u : R)) q =
      ((u⁻¹ : Rˣ) : R) * Polynomial.aeval M q * (u : R) := by
  have h := map_aeval_ringHom (conjUnit u⁻¹) M q
  simp only [conjUnit_apply, inv_inv] at h
  exact h.symm

/-- `aeval` commutes with entrywise application of a ring hom. (`s03-stabfree`) -/
theorem map_aeval_matrix_gen {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 2) (Fin 2) R) (q : ℤ[X]) :
    (Polynomial.aeval M q).map f = Polynomial.aeval (M.map f) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add (Polynomial.aeval M), map_add (Polynomial.aeval (M.map f)),
        Matrix.map_add _ (map_add f), hp, hq]
  | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Matrix.map_mul, Matrix.map_pow,
        Matrix.map_algebraMap c f (map_zero _)
          (by show f (c : R) = (c : S); exact map_intCast f c)]

end M4

/-! ### M4b: evaluation `Zgam t → ZMod ℓ` at a root -/

section M4b

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Evaluation `Zgam t → ZMod ℓ` sending `X ↦ μ`. -/
noncomputable def zgamEval (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) :
    Zgam t →+* ZMod ℓ :=
  AdjoinRoot.lift (Int.castRingHom (ZMod ℓ)) μ (by rw [← aeval_int_eval₂]; exact h)

/-- `s03-stabfree`: auxiliary lemma `zgamEval_mk` (`lem:s03-stabfree`). -/
theorem zgamEval_mk (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0)
    (p : ℤ[X]) : zgamEval t μ h (AdjoinRoot.mk _ p) = Polynomial.aeval μ p := by
  rw [zgamEval, AdjoinRoot.lift_mk, aeval_int_eval₂]

/-- `s03-stabfree`: auxiliary lemma `zgamEval_surjective` (`lem:s03-stabfree`). -/
theorem zgamEval_surjective (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) :
    Function.Surjective (zgamEval t μ h) := by
  intro w
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective w
  refine ⟨(k : Zgam t), ?_⟩
  have e : zgamEval t μ h (k : Zgam t) = (k : ZMod ℓ) := by
    rw [zgamEval]
    exact AdjoinRoot.lift_of _
  rw [e, hk]

/-- `s03-stabfree`: auxiliary lemma `zgamEval_natCast` (`lem:s03-stabfree`). -/
theorem zgamEval_natCast (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0)
    (n : ℕ) : zgamEval t μ h (n : Zgam t) = (n : ZMod ℓ) :=
  map_natCast _ n

/-- `s03-stabfree`: auxiliary lemma `zgamEval_span_le_ker` (`lem:s03-stabfree`). -/
theorem zgamEval_span_le_ker (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) :
    Ideal.span ({(ℓ : Zgam t)} : Set (Zgam t)) ≤ RingHom.ker (zgamEval t μ h) := by
  rw [Ideal.span_le]
  rintro x ⟨rfl⟩
  exact RingHom.mem_ker.2 (by rw [zgamEval_natCast, ZMod.natCast_self])

/-- `s03-stabfree`: auxiliary lemma `zgamEval_card_quotient` (`lem:s03-stabfree`). -/
theorem zgamEval_card_quotient (t : ℤ) (μ : ZMod ℓ)
    (h : Polynomial.aeval μ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) = 0) :
    Nat.card (Zgam t ⧸ RingHom.ker (zgamEval t μ h)) = ℓ := by
  haveI : NeZero ℓ := ⟨Nat.Prime.ne_zero (Fact.out)⟩
  rw [Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (f := zgamEval t μ h)
      (zgamEval_surjective t μ h)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

end M4b

/-- **Piece F: the local core at `ℓ`.** Given the PID core `hprin` (piece E), `y` an `ℓ`-neighbour
(`y ∈ normNSet`, i.e. `y ∈ Ô`, `nrd y = ℓ · w`), and `γ ∈ Γ_x ∩ Γ_{xy}` with `γ ≠ ±1`:
there is `π = p(γ) ∈ ℤ[γ]`, `p ∈ ℤ[X]`, with `nrd π = ℓ` and
`localComponent d ℓ hℓD (y⁻¹ * x⁻¹ * ι(π) * x) ∈ GL2Zl ℓ` (i.e. the local factor at `ℓ` of
`u := y⁻¹ x⁻¹ ι(π) x` is integral with integral inverse). (`s03-stabfree`) -/
theorem local_pi (d : DefiniteData) {ℓ : ℕ} [Fact ℓ.Prime] (hℓD : ¬ ℓ ∣ d.D)
    (hprin : ∀ {t : ℤ} (ht : t = -1 ∨ t = 0 ∨ t = 1) {γ : QuatAlg ℚ d.a d.b}
      (hg : γ ^ 2 = (t : ℚ) • γ - 1) (m : ℕ) [Fact m.Prime]
      (I : Ideal (Zgam t)) (hspan : Ideal.span ({(m : Zgam t)} : Set (Zgam t)) ≤ I)
      (hcard : Nat.card (Zgam t ⧸ I) = m),
      ∃ π ∈ I, GL2TF.Quat.nrd (Zgam.toB t γ (Zgam.aeval_of_sq hg) π) = (m : ℚ))
    {x y : (BHat d.a d.b)ˣ} (hy : y ∈ GL2TF.Quat.normNSet d.O.1 ℓ)
    {γ : (QuatAlg ℚ d.a d.b)ˣ} (hγx : γ ∈ Gam d.Ohat x) (hγxy : γ ∈ Gam d.Ohat (x * y))
    (hpm : γ ∉ pmOne) :
    ∃ (t : ℤ) (p : ℤ[X]) (π : (QuatAlg ℚ d.a d.b)ˣ),
      GL2TF.Quat.nrd (π : QuatAlg ℚ d.a d.b) = (ℓ : ℚ) ∧
      (π : QuatAlg ℚ d.a d.b) = Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p ∧
      localComponent d ℓ hℓD
        (y⁻¹ * (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x)) ∈ GL2Zl ℓ := by
  obtain ⟨t, ht, hg⟩ := step_i d hγx hpm
  obtain ⟨Ox, -, hGam⟩ := (GL2TF.Quat.stabilizer_units d.O.1 x).1
  have hγOx : γ ∈ GL2TF.Quat.unitGroup Ox := by rw [← hGam]; exact hγx
  have hnrdγ : GL2TF.Quat.nrd (γ : QuatAlg ℚ d.a d.b) = 1 :=
    (GL2TF.Quat.unitGroup_val_props d.ha d.hb Ox γ hγOx).2
  set X := localComponent d ℓ hℓD x with hX
  set Y := localComponent d ℓ hℓD y with hY
  set P := localComponent d ℓ hℓD (Units.map (finEmbed d.a d.b).toMonoidHom γ) with hP
  set G := X⁻¹ * P * X with hG
  set H := Y⁻¹ * G * Y with hH
  have hGmem : G ∈ GL2Zl ℓ := G_mem_GL2Zl d hℓD hγx
  have hHmem : H ∈ GL2Zl ℓ := YGY_mem_GL2Zl d hℓD hγxy
  obtain ⟨hGint, -⟩ := mem_GL2Zl_iff.1 hGmem
  obtain ⟨hHint, -⟩ := mem_GL2Zl_iff.1 hHmem
  have hYint : ∀ i j, ‖(Units.val Y) i j‖ ≤ 1 := Y_integral d hℓD hy
  obtain ⟨v, hv⟩ := det_Y d hℓD hy
  have hv' : (Units.val Y).det = (ℓ : ℚ_[ℓ]) * ((v : ℤ_[ℓ]) : ℚ_[ℓ]) := hv
  have hcommU : G * Y = Y * H := by rw [hH]; group
  have hcomm : Units.val G * Units.val Y = Units.val Y * Units.val H := by
    have h := congrArg Units.val hcommU
    simpa using h
  have hPval : Units.val P =
      d.iota ℓ hℓD (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) (γ : QuatAlg ℚ d.a d.b)) :=
    localComponent_finEmbed γ
  have hiota_aeval : ∀ (z : QuatAlg ℚ_[ℓ] d.a d.b) (q : ℤ[X]),
      Polynomial.aeval (d.iota ℓ hℓD z) q = d.iota ℓ hℓD (Polynomial.aeval z q) :=
    fun z q => (map_aeval_ringHom (d.iota ℓ hℓD).toRingHom z q).symm
  have hGval : Units.val G =
      ((X⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[ℓ])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * Units.val P *
        (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) := by
    rw [hG]
    simp
  set r : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 with hr
  have hga : Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) r = 0 := Zgam.aeval_of_sq hg
  have hProot : Polynomial.aeval (Units.val P) r = 0 := by
    rw [hPval, hiota_aeval,
      ← map_aeval_ringHom (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ])), hga, map_zero,
      map_zero]
  have hGroot : Polynomial.aeval (Units.val G) r = 0 := by
    rw [hGval]
    have h : Polynomial.aeval
        (((X⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[ℓ])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * Units.val P *
          (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ])) r
        = ((X⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[ℓ])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) *
            Polynomial.aeval (Units.val P) r * (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :=
      aeval_conj X (Units.val P) r
    rw [h, hProot]
    simp
  set G' := intMat (Units.val G) hGint with hG'
  set Y' := intMat (Units.val Y) hYint with hY'
  set H' := intMat (Units.val H) hHint with hH'
  have hG'map : G'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = Units.val G := intMat_map _ _
  have hY'map : Y'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = Units.val Y := intMat_map _ _
  have hH'map : H'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = Units.val H := intMat_map _ _
  have hinj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] =>
      M.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) := by
    intro A B h
    simp only at h
    ext i j
    have h2 := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h2
    simpa using h2
  have hcomm' : G' * Y' = Y' * H' := by
    apply hinj
    show (G' * Y').map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = (Y' * H').map (algebraMap ℤ_[ℓ] ℚ_[ℓ])
    rw [Matrix.map_mul, Matrix.map_mul, hG'map, hY'map, hH'map]
    exact hcomm
  have hdet' : Y'.det = (ℓ : ℤ_[ℓ]) * (v : ℤ_[ℓ]) := by
    apply IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hY'map, hv', map_mul, map_natCast,
      PadicInt.algebraMap_apply]
  have h0map : ((0 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = 0 := by
    ext i j; simp
  have h0map2 : ((0 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ])).map PadicInt.toZMod = 0 := by
    ext i j; simp
  have hG'eval : Polynomial.aeval G' r = 0 := by
    apply hinj
    show (Polynomial.aeval G' r).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      (0 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] ℚ_[ℓ])
    rw [map_aeval_matrix_gen, hG'map, h0map]
    exact hGroot
  have hcommbar : redMat G' * redMat Y' = redMat Y' * redMat H' := by
    rw [← redMat_mul, ← redMat_mul, hcomm']
  have hdetbar : (redMat Y').det = 0 := by
    rw [redMat_det, hdet', map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  have hYbar_ne : redMat Y' ≠ 0 := by
    intro h0
    have hker : RingHom.ker (PadicInt.toZMod (p := ℓ)) = Ideal.span {(ℓ : ℤ_[ℓ])} := by
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    have hdiv : ∀ i j, ∃ c : ℤ_[ℓ], Y' i j = (ℓ : ℤ_[ℓ]) * c := by
      intro i j
      have h0ij : PadicInt.toZMod (Y' i j) = 0 := by
        have h2 : (Y'.map PadicInt.toZMod) i j = (0 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j :=
          congrFun (congrFun h0 i) j
        simpa using h2
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hker ▸ RingHom.mem_ker.2 h0ij)
      exact ⟨c, hc⟩
    choose z hz using hdiv
    have hdetZ : Y'.det = (ℓ : ℤ_[ℓ]) ^ 2 * (Matrix.of z).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [Matrix.of_apply, hz 0 0, hz 0 1, hz 1 0, hz 1 1]
      ring
    have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.ne_zero (Fact.out))
    have heq : (ℓ : ℤ_[ℓ]) * (v : ℤ_[ℓ]) =
        (ℓ : ℤ_[ℓ]) * ((ℓ : ℤ_[ℓ]) * (Matrix.of z).det) := by
      rw [← hdet', hdetZ]
      ring
    have hcancel : (v : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) * (Matrix.of z).det :=
      mul_left_cancel₀ hℓ0 heq
    have hzero : PadicInt.toZMod (v : ℤ_[ℓ]) = 0 := by
      rw [hcancel, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    exact (IsUnit.map PadicInt.toZMod v.isUnit).ne_zero hzero
  obtain ⟨μ, hμ⟩ := exists_eq_smul_id_mapQ (redMat Y') (redMat G') (redMat H') hdetbar hYbar_ne
    hcommbar
  have hGrootbar : Polynomial.aeval (redMat G') r = 0 := by
    rw [← map_aeval_matrix G' r, hG'eval, h0map2]
  have hμroot : Polynomial.aeval μ r = 0 :=
    aeval_root_of_mapQ (redMat Y') (redMat G') (redMat H') hcommbar r μ hdetbar hYbar_ne hμ
      hGrootbar
  obtain ⟨πA, hπA, hnrd⟩ := hprin ht hg ℓ (RingHom.ker (zgamEval t μ hμroot))
    (zgamEval_span_le_ker t μ hμroot) (zgamEval_card_quotient t μ hμroot)
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective πA
  have hμp : Polynomial.aeval μ p = 0 := by
    have h1 := RingHom.mem_ker.1 hπA
    rw [← hp, zgamEval_mk] at h1
    exact h1
  have hnrd' : GL2TF.Quat.nrd (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p) = (ℓ : ℚ) := by
    rw [← Zgam.toB_mk (Zgam.aeval_of_sq hg) p, hp]
    exact hnrd
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.ne_zero (Fact.out))
  have hnrdπ : GL2TF.Quat.nrd (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p) = (ℓ : ℚ) := hnrd'
  have hms := GL2TF.Quat.mul_star_eq_nrd (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p)
  rw [hnrdπ] at hms
  have h1 : Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p *
        (star (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p) *
          algebraMap ℚ (QuatAlg ℚ d.a d.b) (ℓ : ℚ)⁻¹) = 1 := by
    rw [← mul_assoc, hms.1, ← map_mul, mul_inv_cancel₀ hℓ0, map_one]
  have h2 : (star (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p) *
          algebraMap ℚ (QuatAlg ℚ d.a d.b) (ℓ : ℚ)⁻¹) *
        Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p = 1 := by
    rw [mul_assoc, Algebra.commutes, ← mul_assoc, hms.2, ← map_mul, mul_inv_cancel₀ hℓ0,
      map_one]
  set π : (QuatAlg ℚ d.a d.b)ˣ :=
    Units.mk (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p)
      (star (Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p) *
        algebraMap ℚ (QuatAlg ℚ d.a d.b) (ℓ : ℚ)⁻¹) h1 h2 with hπ
  have hπval : (π : QuatAlg ℚ d.a d.b) = Polynomial.aeval (γ : QuatAlg ℚ d.a d.b) p := rfl
  refine ⟨t, p, π, hnrdπ, hπval, ?_⟩
  set Pπ := localComponent d ℓ hℓD (Units.map (finEmbed d.a d.b).toMonoidHom π) with hPπ
  have hu : localComponent d ℓ hℓD (y⁻¹ * (x⁻¹ * Units.map (finEmbed d.a d.b).toMonoidHom π * x))
      = Y⁻¹ * (X⁻¹ * Pπ * X) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hY, ← hX, ← hPπ]
  have hPπval : Units.val Pπ =
      d.iota ℓ hℓD (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ])
        (π : QuatAlg ℚ d.a d.b)) :=
    localComponent_finEmbed π
  have hPπaeval : Units.val Pπ = Polynomial.aeval (Units.val P) p := by
    rw [hPπval, hπval, hPval, hiota_aeval,
      ← map_aeval_ringHom (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]))]
  have hGπ : Polynomial.aeval (Units.val G) p =
      ((X⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * Units.val Pπ *
        (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) := by
    have hconj : Polynomial.aeval
        (((X⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * Units.val P *
          (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ])) p
        = ((X⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) *
            Polynomial.aeval (Units.val P) p * (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :=
      aeval_conj X (Units.val P) p
    rw [hGval, hconj, ← hPπaeval]
  have hfinal : Units.val (Y⁻¹ * (X⁻¹ * Pπ * X)) =
      Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) * Polynomial.aeval (Units.val G) p := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hGπ]
  rw [hu, mem_GL2Zl_iff, hfinal]
  have hNint : ∀ i j, ‖(Polynomial.aeval (Units.val G) p) i j‖ ≤ 1 :=
    fun i j => norm_aeval_le_one hGint p i j
  set N' := intMat (Polynomial.aeval (Units.val G) p) hNint with hN'
  have hN'map : N'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = Polynomial.aeval (Units.val G) p :=
    intMat_map _ _
  have hN'aeval : N' = Polynomial.aeval G' p := by
    apply hinj
    show N'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = (Polynomial.aeval G' p).map (algebraMap ℤ_[ℓ] ℚ_[ℓ])
    rw [hN'map, map_aeval_matrix_gen, hG'map]
  have hN'bar : redMat N' = Polynomial.aeval (redMat G') p := by
    show (N'.map PadicInt.toZMod) = Polynomial.aeval (redMat G') p
    rw [← map_aeval_matrix, hN'aeval]
  have hsub : LinearMap.range (Matrix.mulVecLin (redMat N')) ≤
      LinearMap.range (Matrix.mulVecLin (redMat Y')) := by
    rw [hN'bar]
    exact range_aeval_le_range (redMat Y') (redMat G') (redMat H') hcommbar p μ hμ hμp
  have hcols : ∀ j : Fin 2, ∃ z : Fin 2 → ℤ_[ℓ],
      Matrix.mulVec Y' z = Matrix.mulVec N' (Pi.single j 1) := by
    intro j
    have hmem := mulVec_mem_range_of_red Y' N' hdet' hsub (Pi.single j 1)
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hmem
    refine ⟨z, ?_⟩
    rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply]
    exact hz
  have hdetN : (Polynomial.aeval (Units.val G) p).det = (ℓ : ℚ_[ℓ]) := by
    have hconj : Polynomial.aeval
        (((X⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * Units.val P *
          (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ])) p
        = ((X⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) *
            Polynomial.aeval (Units.val P) p * (X : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :=
      aeval_conj X (Units.val P) p
    rw [hGval, hconj, Matrix.det_units_conj' X, hPval, hiota_aeval,
      ← map_aeval_ringHom (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ])), det_iota' d,
      nrd_baseChange', hnrd', map_natCast]
  have hℓq : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.Prime.ne_zero (Fact.out))
  have hdetYinv : (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ])).det = ((Units.val Y).det)⁻¹ := by
    have h2 : (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ])).det * (Units.val Y).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    exact eq_inv_of_mul_eq_one_left h2
  have hvq : ‖((v : ℤ_[ℓ]) : ℚ_[ℓ])‖ = 1 := by
    rw [PadicInt.norm_coe]
    have h1 : ‖(v : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ‖((v⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h3 : ‖(v : ℤ_[ℓ])‖ * ‖((v⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    have h4 : 0 < ‖(v : ℤ_[ℓ])‖ := norm_pos_iff.2 (IsUnit.ne_zero v.isUnit)
    nlinarith [norm_nonneg ((v : ℤ_[ℓ])), norm_nonneg ((v⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])]
  have hdetmain : (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) * Polynomial.aeval (Units.val G) p).det
      = (((v : ℤ_[ℓ]) : ℚ_[ℓ])⁻¹) := by
    rw [Matrix.det_mul, hdetYinv, hdetN, hv', mul_inv_rev, mul_assoc, inv_mul_cancel₀ hℓq,
      mul_one]
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hcols j
    rw [Matrix.mulVec_single_one] at hz
    have hmap : Matrix.mulVec (Units.val Y) (algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ z)
        = (Polynomial.aeval (Units.val G) p).col j := by
      funext i
      have e1 := RingHom.map_mulVec (algebraMap ℤ_[ℓ] ℚ_[ℓ]) Y' z i
      have e2 : algebraMap ℤ_[ℓ] ℚ_[ℓ] ((N'.col j) i)
          = ((N'.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])).col j) i := by
        rw [Matrix.col_apply, Matrix.col_apply, Matrix.map_apply]
      rw [hY'map] at e1
      rw [hN'map, ← hz] at e2
      exact e1.symm.trans e2
    have h1 : Matrix.mulVec (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]))
          (Matrix.mulVec (Units.val Y) (algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ z))
        = algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ z := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have hcol : (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) * Polynomial.aeval (Units.val G) p).col j
        = algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ z := by
      have e : Matrix.mulVec (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) *
            Polynomial.aeval (Units.val G) p) (Pi.single j (1 : ℚ_[ℓ]))
          = algebraMap ℤ_[ℓ] ℚ_[ℓ] ∘ z := by
        rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← hmap]
        exact h1
      rw [← e, Matrix.mulVec_single_one]
    have hentry : (Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) * Polynomial.aeval (Units.val G) p) i j
        = algebraMap ℤ_[ℓ] ℚ_[ℓ] (z i) := by
      show ((Units.val (Y⁻¹ : GL (Fin 2) ℚ_[ℓ]) * Polynomial.aeval (Units.val G) p).col j) i
          = algebraMap ℤ_[ℓ] ℚ_[ℓ] (z i)
      rw [hcol, Function.comp_apply]
    rw [hentry, PadicInt.algebraMap_apply, PadicInt.norm_coe]
    exact PadicInt.norm_le_one _
  · rw [hdetmain, norm_inv, hvq, inv_one]

end Langlandscape.StabFree.LocalPi
