/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.RamNrdSurj

/-!
# Reduced norm on levels — S02-L10

Tex labels: `lem:s01-nrd` (carried over from stage 01), `lem:s02-normone`.

* `zhatUnits : Subgroup FinAdeleˣ` — the subgroup `Ẑ^×` of the import used throughout: the image of
  `Zhatˣ → FinAdeleˣ` under `Units.map (Zhat.subtype)` (the same subgroup the import's `Ẑ^×`-statements, e.g.
  `AlgJL/VolI/P0/TopGroups.lean:1443`, are phrased with).
* `nrdHat a b : (B̂)^× →* 𝔸_f^×` — the reduced norm `Units.map (nrdHom FinAdele a b)`.
* `NrdSurj d U` — `nrd(U) ⊇ Ẑ^×` (`nrdHat` maps `U` onto `Ẑ^×`).
* `det_iota` — `det (ι_ℓ x) = nrd x` (re-proof of the import's private `hl_det_eq_nrd`,
  `AlgJL/VolIII/Brandt/HeckeLocal.lean`, template: `splitting_norm_trace`).
* `exists_bhat_of_local` — a family of local lattice elements glues to an element of `B̂`.
* `Hyp.RamNrdSurj d` — **explicit hypothesis** (local surjectivity of `nrd : 𝒪_ℓ^× → ℤ_ℓ^×` at `ℓ ∣ D`,
  not provable from the available local theory; needed for every definite algebra, since `D > 1` always);
  `nrdSurj_Ohat`, `nrdSurj_U0`,
  `nrdSurj_U1`, `nrdSurj_Utower` (via `localEmbedGL (diag u 1)` at the split primes, glued).

Status: `det_iota`: *formalized*; `nrdSurj_*`: *formalized* modulo `Hyp.RamNrdSurj d` (the `ℓ ∣ D` factors).
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

/-- The subgroup `Ẑ^×` of `𝔸_f^×` (`s01-nrd`): image of `Zhatˣ` under `Units.map` of the inclusion
`Zhat ↪ FinAdele` of the import (`GL2TF.Zhat`). -/
noncomputable def zhatUnits : Subgroup FinAdeleˣ :=
  (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom).range

/-- `s01-nrd`: the reduced norm `nrd : B̂^× → 𝔸_f^×`, `Units.map (nrdHom FinAdele a b)`. -/
noncomputable def nrdHat (a b : ℤ) : (BHat a b)ˣ →* FinAdeleˣ :=
  Units.map (nrdHom FinAdele a b)

/-- `s01-nrd`: `NrdSurj d U` says that the reduced norm maps `U ⊆ B̂^×` onto `Ẑ^×`, i.e. every element of
the subgroup `zhatUnits` (the import's `Ẑ^×` inside `𝔸_f^×`) is `nrd u` for some `u ∈ U`. For `U ≤ Ô^×` this is
`lem:s01-nrd`: `Nrd(U) = Ẑ^×`. -/
def NrdSurj (d : DefiniteData) (U : Subgroup (BHat d.a d.b)ˣ) : Prop :=
  ∀ v ∈ zhatUnits, ∃ u ∈ U, nrdHat d.a d.b u = v

open Langlandscape.Local

/-! ### `det ∘ ι_ℓ = nrd` (re-proof of the import's private `hl_det_eq_nrd`) -/

/-- Helper for `lem:s01-nrd` (`s01-nrd`): trace-zero of a pure quaternion under a `K`-algebra hom to `M₂(K)`. -/
private theorem lnr_trace_aux {K : Type*} [Field K] [CharZero K] {a b : ℤ}
    (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (u v : QuatAlg K a b) (c : K) (hc : c ≠ 0) (h1 : u * v * v = c • u) (h2 : v * u * v = -(u * v * v)) :
    (s u).trace = 0 := by
  have h3 : (s (u * v * v)).trace = 0 := by
    have e1 : (s (u * v * v)).trace = (s (v * u * v)).trace := by
      simp only [map_mul]
      rw [Matrix.trace_mul_comm, ← mul_assoc]
    rw [h2, map_neg, Matrix.trace_neg] at e1
    linear_combination e1 / 2
  rw [h1, map_smul, Matrix.trace_smul, smul_eq_zero] at h3
  exact h3.resolve_left hc

/-- Helper for `lem:s01-nrd` (`s01-nrd`): `det s(x) = nrd x` for a `K`-algebra hom `s : B_K → M₂(K)` (the
`splitting_norm_trace` argument over `K`; adapted from the import's private `hl_det_eq_nrd`). -/
private theorem lnr_det_eq_nrd {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : QuatAlg K a b) : (s x).det = nrd x := by
  set i : QuatAlg K a b := ⟨0, 1, 0, 0⟩ with hi
  set j : QuatAlg K a b := ⟨0, 0, 1, 0⟩ with hj
  set k : QuatAlg K a b := ⟨0, 0, 0, 1⟩ with hk
  have ha' : (a : K) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hb' : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb
  have ti : (s i).trace = 0 :=
    lnr_trace_aux s i j b hb' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tj : (s j).trace = 0 :=
    lnr_trace_aux s j i a ha' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tk : (s k).trace = 0 :=
    lnr_trace_aux s k i a ha' (by ext <;> simp [hi, hk]) (by ext <;> simp [hi, hk])
  have hdec : ∀ x : QuatAlg K a b,
      x = algebraMap K (QuatAlg K a b) x.re + x.imI • i + x.imJ • j + x.imK • k := by
    intro x
    ext <;> simp [hi, hj, hk, QuaternionAlgebra.algebraMap_eq]
  have htr : ∀ x : QuatAlg K a b, (s x).trace = 2 * x.re := by
    intro x
    conv_lhs => rw [hdec x]
    simp only [map_add, map_smul, AlgHom.commutes, Matrix.trace_add, Matrix.trace_smul, ti, tj, tk, smul_zero,
      add_zero]
    simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]
  have hdet : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = (M.trace ^ 2 - (M * M).trace) / 2 := by
    intro M
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hdet, ← map_mul, htr, htr]
  simp only [nrd, QuaternionAlgebra.re_mul]
  ring

/-- `lem:s01-nrd` (local `det ∘ ι_ℓ = nrd`, `s01-nrd`): for `ℓ ∤ D` and `x ∈ B_ℓ`, the determinant of the
matrix `ι_ℓ(x) ∈ M₂(ℚ_ℓ)` is the reduced norm of `x`. -/
theorem det_iota {d : DefiniteData} {ℓ : ℕ} [Fact ℓ.Prime] {hℓ : ¬ ℓ ∣ d.D}
    (x : QuatAlg ℚ_[ℓ] d.a d.b) : (d.iota ℓ hℓ x).det = nrd x := by
  obtain ⟨ha, hb, -⟩ := d.hD
  exact lnr_det_eq_nrd (ne_of_lt ha) (ne_of_lt hb) (d.iota ℓ hℓ).toAlgHom x

/-! ### Gluing local lattice elements into `B̂` -/

/-- `lem:s01-nrd` (gluing, `s01-nrd`): a family `x_p ∈ L_p` of local lattice elements is the family of local
components of some `w ∈ B̂` (indeed `w ∈ L̂`). Same bases as `mem_latticeCompletion_iff_local`. -/
theorem exists_bhat_of_local {a b : ℤ} (L : Submodule ℤ (GL2TF.Quat.QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (GL2TF.Quat.QuatAlg ℚ a b)) = ⊤)
    (x : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) (hx : ∀ p : Nat.Primes, x p ∈ localLattice p L) :
    ∃ w : BHat a b, ∀ p : Nat.Primes, localProj a b p w = x p := by
  obtain ⟨e, f, hf⟩ := GL2TF.Quat.exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, -, -⟩ := GL2TF.Quat.exists_bhat_basis e f hf
  choose Fp hFp1 _hFp2 using fun p : Nat.Primes => GL2TF.Quat.exists_baseChange_basis (S := ℚ_[p]) a b f
  have hint : ∀ (p : Nat.Primes) (i : Fin 4), (Fp p).repr (x p) i ∈ PadicInt.subring p := by
    intro p i
    have h := (GL2TF.Quat.mem_span_image_iff_repr (R := ℤ_[p]) e
      (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom
      (Fp p) (fun i => by rw [← hf]; exact hFp1 p i) (x p)).1 (hx p) i
    obtain ⟨y, hy⟩ := h
    exact hy ▸ y.2
  let c : Fin 4 → FinAdele := fun i =>
    ⟨fun p => (Fp p).repr (x p) i, Filter.Eventually.of_forall fun p => hint p i⟩
  refine ⟨∑ i, c i • F i, fun p => ?_⟩
  have hc : ∀ i, localProj a b p (c i • F i) = (Fp p).repr (x p) i • Fp p i := by
    intro i
    rw [localProj_smul, hF1, localProj_finEmbed, ← hFp1 p i]
    try rfl
  rw [map_sum]
  simp only [hc]
  exact (Fp p).sum_repr (x p)

/-! ### Reduced norm of the local components -/

/-- `s01-nrd`: `nrd` commutes with the `ℓ`-component `B̂ → B_ℓ`. -/
theorem nrd_localProj {a b : ℤ} {ℓ : ℕ} [Fact ℓ.Prime] (y : BHat a b) :
    nrd (localProj a b ℓ y) = adeleProj ℓ (nrd (y : QuatAlg FinAdele a b)) :=
  ((nrd_trd_basic (R := FinAdele) (a := a) (b := b)).2.2.2 ℚ_[ℓ] (adeleProj ℓ) y).1

/-! ### The main construction -/

variable {d : DefiniteData}

/-- `lem:s01-nrd` (core, `s01-nrd`): every `v ∈ Ẑ^×` is `nrd Y` for some `Y ∈ Ô^×` whose component at every split
prime `ℓ` is `diag(w, 1)` for a `w ∈ ℤ_ℓ^×` (`localEmbedGL (diag u 1)` per prime, glued), modulo `Hyp.RamNrdSurj d`
at the primes dividing `D`. -/
theorem exists_Ohat_nrd_eq (hram : Hyp.RamNrdSurj d) (v : FinAdeleˣ) (hv : v ∈ zhatUnits) :
    ∃ Y ∈ d.Ohat, nrdHat d.a d.b Y = v ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D), ∃ w : ℤ_[ℓ]ˣ,
        localComponent d ℓ hℓ Y = diagGL (intUnit w) 1 := by
  obtain ⟨z, rfl⟩ := hv
  have hz : ∀ p : Nat.Primes, ∃ w : ℤ_[p]ˣ, ((w : ℤ_[p]) : ℚ_[p]) = ((z : Zhat) : FinAdele) p :=
    (zhat_units_explicit _).1 ⟨z, rfl⟩
  choose w hw using hz
  have key : ∀ p : Nat.Primes, ∃ x : (QuatAlg ℚ_[p] d.a d.b)ˣ,
      localEmbed d.a d.b p x ∈ d.Ohat ∧ nrd (x : QuatAlg ℚ_[p] d.a d.b) = ((w p : ℤ_[p]) : ℚ_[p]) ∧
      ∀ hp : ¬ (p : ℕ) ∣ d.D, d.iotaGL p hp x = diagGL (intUnit (w p)) 1 := by
    intro p
    by_cases hp : (p : ℕ) ∣ d.D
    · obtain ⟨x, hx1, hx2⟩ := hram p hp (w p)
      exact ⟨x, hx1, hx2, fun h => absurd hp h⟩
    · have hg : diagGL (intUnit (w p)) 1 ∈ GL2Zl (p : ℕ) :=
        K0_le_GL2Zl 0 (diag_one_mem_K0 (w p) 0)
      refine ⟨(d.iotaGL p hp).symm (diagGL (intUnit (w p)) 1), ?_, ?_, fun h => ?_⟩
      · exact localEmbedGL_mem_Ohat (d := d) (hp := hp) hg
      · have h := det_iota (d := d) (ℓ := (p : ℕ)) (hℓ := hp)
          ((d.iota p hp).symm (Units.val (diagGL (intUnit (w p)) 1)))
        refine h.symm.trans ?_
        rw [AlgEquiv.apply_symm_apply, diagGL_val, Matrix.det_fin_two_of]
        simp
      · exact MulEquiv.apply_symm_apply _ _
  choose x hx1 hx2 hx3 using key
  have hmem : ∀ p : Nat.Primes,
      (x p : QuatAlg ℚ_[p] d.a d.b) ∈ localLattice p (Subalgebra.toSubmodule d.O.1.toSubalgebra) ∧
      ((x p)⁻¹ : (QuatAlg ℚ_[p] d.a d.b)ˣ).val ∈ localLattice p (Subalgebra.toSubmodule d.O.1.toSubalgebra) :=
    fun p => (localEmbed_mem_orderCompletionUnits_iff d.O.1 (x p)).1 (hx1 p)
  obtain ⟨y, hy⟩ := exists_bhat_of_local _ d.O.1.fg d.O.1.span_eq_top
    (fun p => (x p : QuatAlg ℚ_[p] d.a d.b)) fun p => (hmem p).1
  obtain ⟨y', hy'⟩ := exists_bhat_of_local _ d.O.1.fg d.O.1.span_eq_top
    (fun p => ((x p)⁻¹ : (QuatAlg ℚ_[p] d.a d.b)ˣ).val) fun p => (hmem p).2
  have h1 : y * y' = 1 := bhat_ext_local fun p => by
    rw [map_mul, hy p, hy' p, map_one]
    exact Units.mul_inv (x p)
  have h2 : y' * y = 1 := bhat_ext_local fun p => by
    rw [map_mul, hy p, hy' p, map_one]
    exact Units.inv_mul (x p)
  let Y : (BHat d.a d.b)ˣ := ⟨y, y', h1, h2⟩
  have hYloc : ∀ p : Nat.Primes, localProjUnits d.a d.b p Y = x p := fun p => Units.ext (hy p)
  refine ⟨Y, ?_, ?_, ?_⟩
  · refine (mem_orderCompletionUnits_iff_local d.O.1 Y).2 fun p => ⟨?_, ?_⟩
    · show localProj d.a d.b p y ∈ _
      rw [hy p]
      exact (hmem p).1
    · show localProj d.a d.b p y' ∈ _
      rw [hy' p]
      exact (hmem p).2
  · refine Units.ext ?_
    have e1 : ∀ p : Nat.Primes, (nrd (y : QuatAlg FinAdele d.a d.b) : FinAdele) p =
        ((w p : ℤ_[p]) : ℚ_[p]) := by
      intro p
      have h := nrd_localProj (ℓ := (p : ℕ)) y
      rw [hy p, hx2 p] at h
      exact h.symm
    ext p
    exact (e1 p).trans (hw p)
  · intro ℓ _ hℓ
    obtain ⟨p, rfl⟩ : ∃ p : Nat.Primes, (p : ℕ) = ℓ := ⟨primeIdx ℓ, rfl⟩
    refine ⟨w p, ?_⟩
    rw [localComponent_apply]
    exact (congrArg (d.iotaGL _ hℓ) (hYloc p)).trans (hx3 p hℓ)

/-! ### Norms of the standard levels -/

/-- `lem:s01-nrd` (`s01-nrd`): `nrd(Ô^×) ⊇ Ẑ^×`, modulo `Hyp.RamNrdSurj d` at `ℓ ∣ D`. -/
theorem nrdSurj_Ohat (hram : Hyp.RamNrdSurj d) : NrdSurj d d.Ohat := fun v hv => by
  obtain ⟨Y, hY, hn, -⟩ := exists_Ohat_nrd_eq hram v hv
  exact ⟨Y, hY, hn⟩

/-- `lem:s01-nrd` (`s01-nrd`): `nrd(U_0(N)) ⊇ Ẑ^×` (`diag(u,1) ∈ K_0(ℓ^e)` at `ℓ ∣ N`). -/
theorem nrdSurj_U0 (hram : Hyp.RamNrdSurj d) (N : ℕ) (hN : N.Coprime d.D) : NrdSurj d (d.U0 N hN) :=
  fun v hv => by
    obtain ⟨Y, hY, hn, hloc⟩ := exists_Ohat_nrd_eq hram v hv
    refine ⟨Y, DefiniteData.mem_U0_iff.2 ⟨hY, fun ℓ _ _ hD => ?_⟩, hn⟩
    obtain ⟨w, hw⟩ := hloc ℓ hD
    rw [hw]
    exact diag_one_mem_K0 w _

/-- `lem:s01-nrd` (`s01-nrd`): `nrd(U_1(N)) ⊇ Ẑ^×` (`diag(u,1) ∈ K_1(ℓ^e)` at `ℓ ∣ N`). -/
theorem nrdSurj_U1 (hram : Hyp.RamNrdSurj d) (N : ℕ) (hN : N.Coprime d.D) : NrdSurj d (d.U1 N hN) :=
  fun v hv => by
    obtain ⟨Y, hY, hn, hloc⟩ := exists_Ohat_nrd_eq hram v hv
    refine ⟨Y, DefiniteData.mem_U1_iff.2 ⟨hY, fun ℓ _ _ hD => ?_⟩, hn⟩
    obtain ⟨w, hw⟩ := hloc ℓ hD
    rw [hw]
    exact diag_one_mem_K1 w _

/-- `lem:s01-nrd` (`s01-nrd`): `nrd(U_s) ⊇ Ẑ^×` for the tower `U_s = U_1(M p^s)`. -/
theorem nrdSurj_Utower (hram : Hyp.RamNrdSurj d) (M p s : ℕ) (hN : (M * p ^ s).Coprime d.D) :
    NrdSurj d (d.Utower M p s hN) :=
  nrdSurj_U1 hram (M * p ^ s) hN

end Langlandscape.Quat
