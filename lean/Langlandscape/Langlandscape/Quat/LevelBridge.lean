/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelIndex
import Langlandscape.Quat.Levels
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Bridge `U_1(N) = U1Psi` for the level structure induced by the `ι_ℓ` (S01-L4b)

Tex labels `def:s01-levels`, `thm:s01-mass`(c).  For `N ≥ 1` prime to `D` we build the level structure
`φ_N : O → M₂(ℤ/N)`, `z ↦ (ι_ℓ(z) mod ℓ^{v_ℓ N})_{ℓ ∣ N}` glued by the Chinese remainder theorem
(`ZMod.equivPi`), and show that the `Ψ`-levels of S01-L4a for `φ_N` are the levels of S01-L3c:

* `levelStructureOfIota d N hN : LevelStructure d.O.1 N` (surjectivity: `ℤ_ℓ`-density of `O` in `𝒪_ℓ`
  plus CRT idempotents);
* `U0_eq_U0Psi`, `U1_eq_U1Psi`;
* corollaries `relIndex_U0 : [Ô^× : U_0(N)] = ψ(N)`, `relIndex_U1 : [Ô^× : U_1(N)] = ψ(N) φ(N)`.

The comparison at a prime `ℓ ∣ N` uses the approximation `u = z + N w'` (`z ∈ O`, `w' ∈ Ô`,
import `exists_approx_latticeCompletion`), for which `levelHom u = φ_N(z)` (import `exists_level_hom`) and
`ι_ℓ(u_ℓ) ≡ ι_ℓ(z) mod ℓ^{v_ℓ N}` entrywise.

Status: *formalized*.
-/

open GL2TF Langlandscape.Local

namespace Langlandscape.Quat

/-! ### `p`-adic helpers -/

section Padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `toZModPow e x = toZModPow e y ↔ v(x - y) ≥ e` (`def:s01-levels`, helper, `s01-levels`). -/
theorem toZModPow_eq_iff (e : ℕ) (x y : ℤ_[ℓ]) :
    PadicInt.toZModPow e x = PadicInt.toZModPow e y ↔
      ‖(x : ℚ_[ℓ]) - (y : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def, PadicInt.coe_sub]

/-- `ℓ^e ∣ N` gives `v(N) ≥ e` (`def:s01-levels`, helper, `s01-levels`). -/
theorem norm_natCast_le_of_pow_dvd {e N : ℕ} (h : ℓ ^ e ∣ N) :
    ‖(N : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by
  obtain ⟨k, rfl⟩ := h
  have hmem : ((ℓ ^ e * k : ℕ) : ℤ_[ℓ]) ∈ (Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} : Ideal ℤ_[ℓ]) :=
    Ideal.mem_span_singleton.2 ⟨(k : ℤ_[ℓ]), by rw [Nat.cast_mul, Nat.cast_pow]⟩
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ e).2 hmem
  rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this

/-- Every `c ∈ ℤ_ℓ` is congruent to a natural number modulo `ℓ^e` (`def:s01-levels`, helper, `s01-levels`). -/
theorem exists_nat_approx (e : ℕ) (c : ℤ_[ℓ]) :
    ∃ n : ℕ, ‖(c : ℚ_[ℓ]) - (n : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by
  refine ⟨c.appr e, ?_⟩
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ e).2 (PadicInt.appr_spec e c)
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

/-- Ultrametric comparison (`def:s01-levels`, helper, `s01-levels`). -/
theorem norm_le_iff_of_norm_sub_le {x y : ℚ_[ℓ]} {r : ℝ} (h : ‖x - y‖ ≤ r) : ‖x‖ ≤ r ↔ ‖y‖ ≤ r := by
  constructor
  · intro hx
    have := Langlandscape.Local.norm_sub_le_of_le hx h
    rwa [sub_sub_cancel] at this
  · intro hy
    have := Langlandscape.Local.norm_add_le_of_le hy h
    rwa [add_sub_cancel] at this

/-- Ultrametric comparison, shifted by `1` (`def:s01-levels`, helper, `s01-levels`). -/
theorem norm_sub_one_le_iff_of_norm_sub_le {x y : ℚ_[ℓ]} {r : ℝ} (h : ‖x - y‖ ≤ r) :
    ‖x - 1‖ ≤ r ↔ ‖y - 1‖ ≤ r :=
  norm_le_iff_of_norm_sub_le (by rwa [sub_sub_sub_cancel_right])

/-- Entrywise coercion `M₂(ℤ_ℓ) → M₂(ℚ_ℓ)`. -/
noncomputable def coeMat (ℓ : ℕ) [Fact ℓ.Prime] :
    Matrix (Fin 2) (Fin 2) ℤ_[ℓ] →+* Matrix (Fin 2) (Fin 2) ℚ_[ℓ] :=
  (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix

/-- `coeMat` is injective (`def:s01-levels`, helper, `s01-levels`). -/
theorem coeMat_injective : Function.Injective (coeMat ℓ) := fun X Y h => by
  ext r s
  exact congrArg (fun F => F r s) h

end Padic

/-! ### CRT helpers -/

section CRT

variable {N : ℕ} [NeZero N]

/-- The components of `ZMod.equivPi` are the reductions (`def:s01-levels`, helper, `s01-levels`). -/
theorem zmod_equivPi_apply (x : ZMod N) (ℓ : N.primeFactors) :
    ZMod.equivPi N (NeZero.ne N) x ℓ =
      ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) x :=
  DFunLike.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : N.primeFactors => ZMod ((p : ℕ) ^ N.factorization p)) ℓ).comp (ZMod.equivPi N (NeZero.ne N)).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)))) x

/-- An element of `ℤ/N` is determined by its reductions modulo the `ℓ^{v_ℓ N}` (`def:s01-levels`,
helper, `s01-levels`). -/
theorem zmod_ext_iff {x y : ZMod N} :
    x = y ↔ ∀ (ℓ : ℕ) (_hℓ : ℓ ∈ N.primeFactors),
      ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod (ℓ ^ N.factorization ℓ)) x =
        ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod (ℓ ^ N.factorization ℓ)) y := by
  refine ⟨fun h _ _ => by rw [h], fun h => (ZMod.equivPi N (NeZero.ne N)).injective (funext fun ℓ => ?_)⟩
  rw [zmod_equivPi_apply, zmod_equivPi_apply]
  exact h ℓ ℓ.2

end CRT

/-! ### Matrices over a product -/

section MatPi

variable {A ι : Type*} [Ring A] {S : ι → Type*} [∀ i, Ring (S i)]

/-- Evaluation `M₂(∏ S_i) → ∏ M₂(S_i)`. -/
def matPiEval : Matrix (Fin 2) (Fin 2) (∀ i, S i) →+* ∀ i, Matrix (Fin 2) (Fin 2) (S i) :=
  RingHom.pi fun i => (Pi.evalRingHom S i).mapMatrix

/-- `matPiEval` is injective (`def:s01-levels`, helper, `s01-levels`). -/
theorem matPiEval_injective : Function.Injective (matPiEval (S := S)) := fun X Y h => by
  ext r s i
  exact congrArg (fun F => F i r s) h

/-- The underlying function of `matPiLift`. -/
def matPiLiftFun (f : A →+* ∀ i, Matrix (Fin 2) (Fin 2) (S i)) (x : A) : Matrix (Fin 2) (Fin 2) (∀ i, S i) :=
  Matrix.of fun r s i => f x i r s

/-- `matPiEval ∘ matPiLiftFun f = f` (`def:s01-levels`, helper, `s01-levels`). -/
theorem matPiEval_lift (f : A →+* ∀ i, Matrix (Fin 2) (Fin 2) (S i)) (x : A) :
    matPiEval (matPiLiftFun f x) = f x :=
  funext fun _ => Matrix.ext fun _ _ => rfl

/-- A ring hom into `∏ M₂(S_i)` as a ring hom into `M₂(∏ S_i)`. -/
def matPiLift (f : A →+* ∀ i, Matrix (Fin 2) (Fin 2) (S i)) : A →+* Matrix (Fin 2) (Fin 2) (∀ i, S i) where
  toFun := matPiLiftFun f
  map_one' := matPiEval_injective (by simp only [matPiEval_lift, map_one])
  map_mul' x y := matPiEval_injective (by simp only [matPiEval_lift, map_mul])
  map_zero' := matPiEval_injective (by simp only [matPiEval_lift, map_zero])
  map_add' x y := matPiEval_injective (by simp only [matPiEval_lift, map_add])

end MatPi

/-! ### Local reductions `O → M₂(ℤ/ℓ^e)` -/

namespace DefiniteData

variable (d : DefiniteData)

section Local

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `z ↦ ι_ℓ(z)` on `O`, with values in `M₂(ℚ_ℓ)` (`def:s01-B`). -/
noncomputable def iotaO : d.O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) ℚ_[ℓ] :=
  ((d.iota ℓ hℓ).toRingEquiv.toRingHom.comp (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]))).comp
    d.O.1.toSubalgebra.val.toRingHom

/-- Value of `iotaO` (`def:s01-B`, `s01-B`). -/
theorem iotaO_apply (z : d.O.1.toSubalgebra) :
    d.iotaO ℓ hℓ z = d.iota ℓ hℓ (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) (z : QuatAlg ℚ d.a d.b)) :=
  rfl

/-- Value of `iotaO` on `⟨z, hz⟩` (`def:s01-B`, `s01-B`). -/
theorem iotaO_mk {z : QuatAlg ℚ d.a d.b} (hz : z ∈ d.O.1.toSubalgebra) :
    d.iotaO ℓ hℓ ⟨z, hz⟩ = d.iota ℓ hℓ (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) z) :=
  rfl

/-- `ι_ℓ(O) ⊆ M₂(ℤ_ℓ)` (`def:s01-B`, `s01-B`). -/
theorem iotaO_integral (z : d.O.1.toSubalgebra) (i j : Fin 2) : ‖d.iotaO ℓ hℓ z i j‖ ≤ 1 :=
  (d.mem_localLattice_iff_iota ℓ hℓ
      (GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) (z : QuatAlg ℚ d.a d.b))).1
    (Submodule.subset_span ⟨(z : QuatAlg ℚ d.a d.b), z.2, rfl⟩) i j

/-- The underlying function of `iotaZ`. -/
noncomputable def iotaZFun (z : d.O.1.toSubalgebra) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] :=
  Matrix.of fun i j => ⟨d.iotaO ℓ hℓ z i j, d.iotaO_integral ℓ hℓ z i j⟩

/-- `coeMat ∘ iotaZFun = iotaO` (`def:s01-B`, `s01-B`). -/
theorem coeMat_iotaZFun (z : d.O.1.toSubalgebra) : coeMat ℓ (d.iotaZFun ℓ hℓ z) = d.iotaO ℓ hℓ z :=
  Matrix.ext fun _ _ => rfl

/-- `z ↦ ι_ℓ(z)` on `O`, with values in `M₂(ℤ_ℓ)` (`def:s01-B`). -/
noncomputable def iotaZ : d.O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) ℤ_[ℓ] where
  toFun := d.iotaZFun ℓ hℓ
  map_one' := coeMat_injective (by simp only [coeMat_iotaZFun, map_one])
  map_mul' x y := coeMat_injective (by simp only [coeMat_iotaZFun, map_mul])
  map_zero' := coeMat_injective (by simp only [coeMat_iotaZFun, map_zero])
  map_add' x y := coeMat_injective (by simp only [coeMat_iotaZFun, map_add])

/-- Coefficients of `iotaZ` (`def:s01-B`, `s01-B`). -/
theorem iotaZ_coe (z : d.O.1.toSubalgebra) (i j : Fin 2) :
    ((d.iotaZ ℓ hℓ z i j : ℤ_[ℓ]) : ℚ_[ℓ]) = d.iotaO ℓ hℓ z i j :=
  rfl

/-- The reduction `O → M₂(ℤ/ℓ^e)`, `z ↦ ι_ℓ(z) mod ℓ^e` (`def:s01-levels`). -/
noncomputable def redAt (e : ℕ) : d.O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ e)) :=
  (PadicInt.toZModPow (p := ℓ) e).mapMatrix.comp (d.iotaZ ℓ hℓ)

/-- Value of `redAt` (`def:s01-levels`, `s01-levels`). -/
theorem redAt_apply (e : ℕ) (z : d.O.1.toSubalgebra) (i j : Fin 2) :
    d.redAt ℓ hℓ e z i j = PadicInt.toZModPow e (d.iotaZ ℓ hℓ z i j) :=
  rfl

/-- `O` is `ℓ`-adically dense in `𝒪_ℓ`: every `y ∈ 𝒪_ℓ` is congruent to some `z ∈ O` modulo `ℓ^e`
(entrywise after `ι_ℓ`) (`def:s01-levels`, helper, `s01-levels`). -/
theorem exists_approx_local (e : ℕ) {y : QuatAlg ℚ_[ℓ] d.a d.b}
    (hy : y ∈ GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra)) :
    ∃ z : d.O.1.toSubalgebra, ∀ i j,
      ‖d.iota ℓ hℓ y i j - d.iotaO ℓ hℓ z i j‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by
  have hy' : y ∈ Submodule.span ℤ_[ℓ] ((GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ])) ''
      (Subalgebra.toSubmodule d.O.1.toSubalgebra : Set (QuatAlg ℚ d.a d.b))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨⟨x, hx⟩, fun i j => ?_⟩
    rw [iotaO_mk, sub_self, norm_zero]
    exact zpow_nonneg (Nat.cast_nonneg ℓ) _
  | zero =>
    refine ⟨0, fun i j => ?_⟩
    simp only [map_zero, Matrix.zero_apply, sub_self, norm_zero]
    exact zpow_nonneg (Nat.cast_nonneg ℓ) _
  | add x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨z1, h1⟩ := ih₁
    obtain ⟨z2, h2⟩ := ih₂
    refine ⟨z1 + z2, fun i j => ?_⟩
    have e1 : d.iota ℓ hℓ (x₁ + x₂) i j - d.iotaO ℓ hℓ (z1 + z2) i j =
        (d.iota ℓ hℓ x₁ i j - d.iotaO ℓ hℓ z1 i j) + (d.iota ℓ hℓ x₂ i j - d.iotaO ℓ hℓ z2 i j) := by
      simp only [map_add, Matrix.add_apply]
      ring
    rw [e1]
    exact Langlandscape.Local.norm_add_le_of_le (h1 i j) (h2 i j)
  | smul c x _ ih =>
    obtain ⟨z, h⟩ := ih
    obtain ⟨n, hn⟩ := exists_nat_approx e c
    refine ⟨n • z, fun i j => ?_⟩
    have hZ := d.iotaO_integral ℓ hℓ z i j
    have e1 : d.iota ℓ hℓ (c • x) i j - d.iotaO ℓ hℓ (n • z) i j =
        algebraMap ℤ_[ℓ] ℚ_[ℓ] c * (d.iota ℓ hℓ x i j - d.iotaO ℓ hℓ z i j) +
          (algebraMap ℤ_[ℓ] ℚ_[ℓ] c - (n : ℚ_[ℓ])) * d.iotaO ℓ hℓ z i j := by
      rw [← IsScalarTower.algebraMap_smul (A := ℚ_[ℓ]) c x, map_smul, map_nsmul, Matrix.smul_apply,
        Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      ring
    rw [e1]
    exact Langlandscape.Local.norm_add_le_of_le
      (Langlandscape.Local.norm_mul_le_of_le' (PadicInt.norm_le_one c) (h i j))
      (Langlandscape.Local.norm_mul_le_of_le hn hZ)

/-- `redAt` is surjective (`def:s01-levels`, helper, `s01-levels`). -/
theorem redAt_surjective (e : ℕ) : Function.Surjective (d.redAt ℓ hℓ e) := by
  intro A
  choose k hk using fun i j => ZMod.intCast_surjective (A i j)
  have hrange : (Matrix.of fun i j => ((k i j : ℤ) : ℚ_[ℓ])) ∈ (d.iota ℓ hℓ) ''
      (GL2TF.Quat.localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) : Set (QuatAlg ℚ_[ℓ] d.a d.b)) := by
    rw [d.iota_image_localLattice ℓ hℓ]
    exact ⟨Matrix.of fun i j => ((k i j : ℤ) : ℤ_[ℓ]), Matrix.ext fun i j => by simp⟩
  obtain ⟨y, hy, hyM⟩ := hrange
  obtain ⟨z, hz⟩ := d.exists_approx_local ℓ hℓ e hy
  refine ⟨z, ?_⟩
  ext i j
  rw [redAt_apply, ← hk i j, ← map_intCast (PadicInt.toZModPow (p := ℓ) e) (k i j), toZModPow_eq_iff,
    iotaZ_coe, PadicInt.coe_intCast]
  have := hz i j
  rw [hyM, Matrix.of_apply] at this
  rwa [norm_sub_rev] at this

end Local

/-! ### The level structure `φ_N` -/

variable (N : ℕ) [NeZero N] (hN : N.Coprime d.D)

/-- The family of local reductions `O → ∏_{ℓ ∣ N} M₂(ℤ/ℓ^{v_ℓ N})` (`def:s01-levels`). -/
noncomputable def redPi (hN : N.Coprime d.D) :
    d.O.1.toSubalgebra →+* ∀ ℓ : N.primeFactors, Matrix (Fin 2) (Fin 2) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) :=
  RingHom.pi fun ℓ =>
    haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
    d.redAt ℓ (d.not_dvd_D_of_mem_primeFactors hN ℓ.2) (N.factorization ℓ)

/-- The ring hom `φ_N : O → M₂(ℤ/N)`, glued from the `ι_ℓ mod ℓ^{v_ℓ N}` by CRT (`def:s01-levels`). -/
noncomputable def levelRingHom (hN : N.Coprime d.D) : d.O.1.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod N) :=
  ((ZMod.equivPi N (NeZero.ne N)).symm.toRingHom.mapMatrix).comp (matPiLift (d.redPi N hN))

/-- `φ_N mod ℓ^{v_ℓ N} = ι_ℓ mod ℓ^{v_ℓ N}` (`def:s01-levels`, `s01-levels`). -/
theorem castHom_levelRingHom (z : d.O.1.toSubalgebra) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∈ N.primeFactors)
    (hD : ¬ ℓ ∣ d.D) (r s : Fin 2) :
    ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod (ℓ ^ N.factorization ℓ)) (d.levelRingHom N hN z r s) =
      d.redAt ℓ hD (N.factorization ℓ) z r s := by
  have h := zmod_equivPi_apply ((ZMod.equivPi N (NeZero.ne N)).symm
    (fun ℓ' : N.primeFactors => d.redPi N hN z ℓ' r s)) ⟨ℓ, hℓ⟩
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- `φ_N` is surjective (`def:s01-levels`, `s01-levels`). -/
theorem levelRingHom_surjective : Function.Surjective (d.levelRingHom N hN) := by
  intro A
  have hloc : ∀ ℓ : N.primeFactors, ∃ z : d.O.1.toSubalgebra, d.redPi N hN z ℓ =
      (ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))).mapMatrix A := by
    intro ℓ
    have : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
    exact d.redAt_surjective ℓ (d.not_dvd_D_of_mem_primeFactors hN ℓ.2) (N.factorization ℓ) _
  choose z hz using hloc
  refine ⟨∑ ℓ' : N.primeFactors, (((ZMod.equivPi N (NeZero.ne N)).symm (Pi.single ℓ' 1)).val) • z ℓ', ?_⟩
  ext r s
  refine zmod_ext_iff.2 fun ℓ hℓ => ?_
  have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
  have hD := d.not_dvd_D_of_mem_primeFactors hN hℓ
  have hc : ∀ ℓ' : N.primeFactors,
      ((((ZMod.equivPi N (NeZero.ne N)).symm (Pi.single ℓ' 1)).val : ℕ) : ZMod (ℓ ^ N.factorization ℓ)) =
        (Pi.single ℓ' 1 : ∀ i : N.primeFactors, ZMod ((i : ℕ) ^ N.factorization i)) ⟨ℓ, hℓ⟩ := by
    intro ℓ'
    have h1 := zmod_equivPi_apply ((ZMod.equivPi N (NeZero.ne N)).symm (Pi.single ℓ' 1)) ⟨ℓ, hℓ⟩
    rw [RingEquiv.apply_symm_apply] at h1
    exact (ZMod.natCast_val _).trans h1.symm
  have hc1 : ((((ZMod.equivPi N (NeZero.ne N)).symm (Pi.single ⟨ℓ, hℓ⟩ 1)).val : ℕ) :
      ZMod (ℓ ^ N.factorization ℓ)) = 1 :=
    (hc _).trans (Pi.single_eq_same _ _)
  have hc0 : ∀ ℓ' : N.primeFactors, ℓ' ≠ ⟨ℓ, hℓ⟩ →
      ((((ZMod.equivPi N (NeZero.ne N)).symm (Pi.single ℓ' 1)).val : ℕ) : ZMod (ℓ ^ N.factorization ℓ)) = 0 :=
    fun ℓ' hne => (hc ℓ').trans (Pi.single_eq_of_ne hne.symm _)
  rw [d.castHom_levelRingHom N hN _ ℓ hℓ hD, map_sum, Matrix.sum_apply,
    Finset.sum_eq_single (⟨ℓ, hℓ⟩ : N.primeFactors)]
  · rw [map_nsmul, Matrix.smul_apply, nsmul_eq_mul, hc1, one_mul]
    exact congrArg (fun X => X r s) (hz ⟨ℓ, hℓ⟩)
  · intro ℓ' _ hne
    rw [map_nsmul, Matrix.smul_apply, nsmul_eq_mul, hc0 ℓ' hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `def:s01-levels`, `thm:s01-mass`(c): the level structure `φ_N : O ↠ M₂(ℤ/N)` induced by the splittings
`ι_ℓ` (`ℓ ∣ N`), reduced modulo `ℓ^{v_ℓ N}` and glued by CRT. -/
noncomputable def levelStructureOfIota (hN : N.Coprime d.D) : GL2TF.Quat.LevelStructure d.O.1 N where
  toRingHom := d.levelRingHom N hN
  surjective := d.levelRingHom_surjective N hN

/-- `(levelStructureOfIota).toRingHom = levelRingHom` (`def:s01-levels`, `s01-levels`). -/
theorem levelStructureOfIota_toRingHom :
    (d.levelStructureOfIota N hN).toRingHom = d.levelRingHom N hN :=
  rfl

/-- `φ_N(z)` is upper triangular iff all `ι_ℓ(z) mod ℓ^{v_ℓ N}` are (`def:s01-levels`, `s01-levels`). -/
theorem levelRingHom_borel_iff (z : d.O.1.toSubalgebra) :
    d.levelRingHom N hN z 1 0 = 0 ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors) (hD : ¬ ℓ ∣ d.D),
        d.redAt ℓ hD (N.factorization ℓ) z 1 0 = 0 := by
  rw [zmod_ext_iff]
  simp only [map_zero]
  constructor
  · intro h ℓ _ hℓ hD
    rw [← d.castHom_levelRingHom N hN z ℓ hℓ hD]
    exact h ℓ hℓ
  · intro h ℓ hℓ
    have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
    rw [d.castHom_levelRingHom N hN z ℓ hℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ)]
    exact h ℓ hℓ _

/-- `φ_N(z) ∈ B₁(ℤ/N)` iff all `ι_ℓ(z) mod ℓ^{v_ℓ N}` lie in `B₁` (`def:s01-levels`, `s01-levels`). -/
theorem levelRingHom_borel1_iff (z : d.O.1.toSubalgebra) :
    (d.levelRingHom N hN z 1 0 = 0 ∧ d.levelRingHom N hN z 1 1 = 1) ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors) (hD : ¬ ℓ ∣ d.D),
        d.redAt ℓ hD (N.factorization ℓ) z 1 0 = 0 ∧ d.redAt ℓ hD (N.factorization ℓ) z 1 1 = 1 := by
  rw [zmod_ext_iff, zmod_ext_iff]
  simp only [map_zero, map_one]
  constructor
  · rintro ⟨h0, h1⟩ ℓ _ hℓ hD
    rw [← d.castHom_levelRingHom N hN z ℓ hℓ hD, ← d.castHom_levelRingHom N hN z ℓ hℓ hD]
    exact ⟨h0 ℓ hℓ, h1 ℓ hℓ⟩
  · intro h
    refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
    · have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
      rw [d.castHom_levelRingHom N hN z ℓ hℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ)]
      exact (h ℓ hℓ _).1
    · have : Fact ℓ.Prime := ⟨Nat.prime_of_mem_primeFactors hℓ⟩
      rw [d.castHom_levelRingHom N hN z ℓ hℓ (d.not_dvd_D_of_mem_primeFactors hN hℓ)]
      exact (h ℓ hℓ _).2

/-! ### Comparison at a prime `ℓ ∣ N` -/

omit [NeZero N] in
/-- If `u = z + N w'` with `z ∈ O`, `w' ∈ Ô`, then `ι_ℓ(u_ℓ) ≡ ι_ℓ(z) mod ℓ^e` entrywise for `ℓ^e ∣ N`
(`def:s01-levels`, `s01-levels`). -/
theorem localComponent_sub_iotaO {u : (BHat d.a d.b)ˣ} {z : QuatAlg ℚ d.a d.b}
    (hz : z ∈ d.O.1.toSubalgebra) {w' : BHat d.a d.b}
    (hw' : w' ∈ GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule d.O.1.toSubalgebra))
    (he : (u : BHat d.a d.b) = finEmbed d.a d.b z + (N : FinAdele) • w') (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ¬ ℓ ∣ d.D) {e : ℕ} (hℓ : ℓ ^ e ∣ N) (i j : Fin 2) :
    ‖(localComponent d ℓ hD u : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j - d.iotaO ℓ hD ⟨z, hz⟩ i j‖ ≤
      (ℓ : ℝ) ^ (-(e : ℤ)) := by
  have h1 : localProj d.a d.b ℓ (u : BHat d.a d.b) =
      GL2TF.Quat.baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) z + (N : ℚ_[ℓ]) • localProj d.a d.b ℓ w' := by
    rw [he, map_add, localProj_smul, map_natCast]
    congr 1
  have hY := (d.mem_localLattice_iff_iota ℓ hD _).1
    (localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hw' ℓ) i j
  rw [localComponent_val, h1, map_add, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, iotaO_mk,
    add_sub_cancel_left]
  exact Langlandscape.Local.norm_mul_le_of_le (norm_natCast_le_of_pow_dvd hℓ) hY

/-- `ι_ℓ(u_ℓ) ∈ K_0(ℓ^e)` iff `ι_ℓ(z) mod ℓ^e` is upper triangular (`def:s01-levels`, `s01-levels`). -/
theorem mem_K0_iff_redAt {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.Ohat) {z : QuatAlg ℚ d.a d.b}
    (hz : z ∈ d.O.1.toSubalgebra) {w' : BHat d.a d.b}
    (hw' : w' ∈ GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule d.O.1.toSubalgebra))
    (he : (u : BHat d.a d.b) = finEmbed d.a d.b z + (N : FinAdele) • w') (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ¬ ℓ ∣ d.D) {e : ℕ} (hℓ : ℓ ^ e ∣ N) :
    localComponent d ℓ hD u ∈ K0 ℓ e ↔ d.redAt ℓ hD e ⟨z, hz⟩ 1 0 = 0 := by
  have h := d.localComponent_sub_iotaO N hz hw' he ℓ hD hℓ
  rw [mem_K0_iff, norm_le_iff_of_norm_sub_le (h 1 0), redAt_apply,
    ← map_zero (PadicInt.toZModPow (p := ℓ) e), toZModPow_eq_iff, iotaZ_coe, PadicInt.coe_zero, sub_zero]
  exact ⟨fun ⟨_, a⟩ => a, fun a => ⟨localComponent_mem_GL2Zl hu, a⟩⟩

/-- `ι_ℓ(u_ℓ) ∈ K_1(ℓ^e)` iff `ι_ℓ(z) mod ℓ^e ∈ B₁` (`def:s01-levels`, `s01-levels`). -/
theorem mem_K1_iff_redAt {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.Ohat) {z : QuatAlg ℚ d.a d.b}
    (hz : z ∈ d.O.1.toSubalgebra) {w' : BHat d.a d.b}
    (hw' : w' ∈ GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule d.O.1.toSubalgebra))
    (he : (u : BHat d.a d.b) = finEmbed d.a d.b z + (N : FinAdele) • w') (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ¬ ℓ ∣ d.D) {e : ℕ} (hℓ : ℓ ^ e ∣ N) :
    localComponent d ℓ hD u ∈ K1 ℓ e ↔
      d.redAt ℓ hD e ⟨z, hz⟩ 1 0 = 0 ∧ d.redAt ℓ hD e ⟨z, hz⟩ 1 1 = 1 := by
  have h := d.localComponent_sub_iotaO N hz hw' he ℓ hD hℓ
  rw [mem_K1_iff, mem_K0_iff, norm_le_iff_of_norm_sub_le (h 1 0), norm_sub_one_le_iff_of_norm_sub_le (h 1 1),
    redAt_apply, redAt_apply, ← map_zero (PadicInt.toZModPow (p := ℓ) e),
    ← map_one (PadicInt.toZModPow (p := ℓ) e), toZModPow_eq_iff, toZModPow_eq_iff, iotaZ_coe, iotaZ_coe,
    PadicInt.coe_zero, PadicInt.coe_one, sub_zero]
  exact ⟨fun ⟨⟨_, a⟩, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨⟨localComponent_mem_GL2Zl hu, a⟩, b⟩⟩

end DefiniteData

/-! ### Membership in the `Ψ`-levels -/

/-- The value of `levelHom` on an approximation `u = z + N w'` (`thm:s01-mass`(c), `s01-mass`). -/
theorem levelHom_val_of_approx {a b : ℤ} (O : GL2TF.Quat.QOrder a b) {N : ℕ} [NeZero N]
    (φ : GL2TF.Quat.LevelStructure O N) (u : orderCompletionUnits O) (z : QuatAlg ℚ a b)
    (hz : z ∈ O.toSubalgebra) (w' : BHat a b)
    (hw' : w' ∈ GL2TF.Quat.latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra))
    (he : ((u : (BHat a b)ˣ) : BHat a b) = finEmbed a b z + (N : FinAdele) • w') :
    ((levelHom O φ u : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = φ.toRingHom ⟨z, hz⟩ :=
  (Classical.choose_spec (GL2TF.Quat.exists_level_hom O φ)).2 u z hz w' hw' he

/-- Membership in `U0Psi` (`thm:s01-mass`(c), `s01-mass`). -/
theorem mem_U0Psi_iff {a b : ℤ} {O : GL2TF.Quat.QOrder a b} {N : ℕ} [NeZero N]
    {φ : GL2TF.Quat.LevelStructure O N} {u : (BHat a b)ˣ} :
    u ∈ U0Psi O φ ↔ ∃ hu : u ∈ orderCompletionUnits O,
      ((levelHom O φ ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 := by
  rw [U0Psi, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

/-- Membership in `U1Psi` (`thm:s01-mass`(c), `s01-mass`). -/
theorem mem_U1Psi_iff {a b : ℤ} {O : GL2TF.Quat.QOrder a b} {N : ℕ} [NeZero N]
    {φ : GL2TF.Quat.LevelStructure O N} {u : (BHat a b)ˣ} :
    u ∈ U1Psi O φ ↔ ∃ hu : u ∈ orderCompletionUnits O,
      ((levelHom O φ ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 ∧
      ((levelHom O φ ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 = 1 := by
  rw [U1Psi, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

/-! ### The bridge -/

namespace DefiniteData

variable (d : DefiniteData) (N : ℕ) [NeZero N] (hN : N.Coprime d.D)

/-- For `u ∈ Ô^×`: `Ψ(u) ∈ B(ℤ/N)` iff `ι_ℓ(u_ℓ) ∈ K_0(ℓ^{v_ℓ N})` for all `ℓ ∣ N` (`def:s01-levels`,
`s01-levels`). -/
theorem levelHom_borel_iff_local (u : (BHat d.a d.b)ˣ) (hu : u ∈ d.Ohat) :
    ((levelHom d.O.1 (d.levelStructureOfIota N hN) ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors) (hD : ¬ ℓ ∣ d.D),
        localComponent d ℓ hD u ∈ K0 ℓ (N.factorization ℓ) := by
  obtain ⟨z, hz, w', hw', he⟩ := GL2TF.Quat.exists_approx_latticeCompletion _ d.O.1.fg d.O.1.span_eq_top N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hu.1
  rw [levelHom_val_of_approx d.O.1 _ ⟨u, hu⟩ z hz w' hw' he, levelStructureOfIota_toRingHom,
    d.levelRingHom_borel_iff N hN]
  refine forall_congr' fun ℓ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hD => ?_
  exact (d.mem_K0_iff_redAt N hu hz hw' he ℓ hD (Nat.ordProj_dvd N ℓ)).symm

/-- For `u ∈ Ô^×`: `Ψ(u) ∈ B₁(ℤ/N)` iff `ι_ℓ(u_ℓ) ∈ K_1(ℓ^{v_ℓ N})` for all `ℓ ∣ N` (`def:s01-levels`,
`s01-levels`). -/
theorem levelHom_borel1_iff_local (u : (BHat d.a d.b)ˣ) (hu : u ∈ d.Ohat) :
    (((levelHom d.O.1 (d.levelStructureOfIota N hN) ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 ∧
      ((levelHom d.O.1 (d.levelStructureOfIota N hN) ⟨u, hu⟩ : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 = 1) ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ∈ N.primeFactors) (hD : ¬ ℓ ∣ d.D),
        localComponent d ℓ hD u ∈ K1 ℓ (N.factorization ℓ) := by
  obtain ⟨z, hz, w', hw', he⟩ := GL2TF.Quat.exists_approx_latticeCompletion _ d.O.1.fg d.O.1.span_eq_top N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hu.1
  rw [levelHom_val_of_approx d.O.1 _ ⟨u, hu⟩ z hz w' hw' he, levelStructureOfIota_toRingHom,
    d.levelRingHom_borel1_iff N hN]
  refine forall_congr' fun ℓ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun hD => ?_
  exact (d.mem_K1_iff_redAt N hu hz hw' he ℓ hD (Nat.ordProj_dvd N ℓ)).symm

/-- `def:s01-levels`, `thm:s01-mass`(c): `U_0(N) = Ψ⁻¹(B(ℤ/N))` for the level structure induced by the `ι_ℓ`
(`s01-levels`). -/
theorem U0_eq_U0Psi : d.U0 N hN = U0Psi d.O.1 (d.levelStructureOfIota N hN) := by
  ext u
  rw [mem_U0_iff, mem_U0Psi_iff]
  exact ⟨fun ⟨hu, h⟩ => ⟨hu, (d.levelHom_borel_iff_local N hN u hu).2 h⟩,
    fun ⟨hu, h⟩ => ⟨hu, (d.levelHom_borel_iff_local N hN u hu).1 h⟩⟩

/-- `def:s01-levels`, `thm:s01-mass`(c): `U_1(N) = Ψ⁻¹(B₁(ℤ/N))` for the level structure induced by the `ι_ℓ`
(`s01-levels`). -/
theorem U1_eq_U1Psi : d.U1 N hN = U1Psi d.O.1 (d.levelStructureOfIota N hN) := by
  ext u
  rw [mem_U1_iff, mem_U1Psi_iff]
  exact ⟨fun ⟨hu, h⟩ => ⟨hu, (d.levelHom_borel1_iff_local N hN u hu).2 h⟩,
    fun ⟨hu, h⟩ => ⟨hu, (d.levelHom_borel1_iff_local N hN u hu).1 h⟩⟩

/-- `thm:s01-mass`(c): `[Ô^× : U_0(N)] = ψ(N)` (`s01-mass`). -/
theorem relIndex_U0 :
    (((d.U0 N hN).relIndex d.Ohat : ℕ) : ℚ) = GL2TF.Explicit.dedekindPsi N := by
  rw [d.U0_eq_U0Psi N hN]
  exact relIndex_U0Psi d.O.1 (d.levelStructureOfIota N hN)

/-- `thm:s01-mass`(c): `[Ô^× : U_1(N)] = ψ(N) φ(N)` (`s01-mass`). -/
theorem relIndex_U1 :
    (((d.U1 N hN).relIndex d.Ohat : ℕ) : ℚ) = GL2TF.Explicit.dedekindPsi N * (Nat.totient N : ℚ) := by
  rw [d.U1_eq_U1Psi N hN]
  exact relIndex_U1Psi d.O.1 (d.levelStructureOfIota N hN)

end DefiniteData

end Langlandscape.Quat
