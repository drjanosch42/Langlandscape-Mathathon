/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic
import AlgJL.VolIII.Brandt.Coefficients
import Langlandscape.Local.GL2Levels

/-!
# Local components of `B̂^×` (S01-L3b)

Tex label `def:s01-B` (the splittings `ι_ℓ : B_ℓ ≃ M₂(ℚ_ℓ)`, `ι_ℓ(𝒪_ℓ) = M₂(ℤ_ℓ)` for `ℓ ∤ D`), used by
`def:s01-levels`.

* `localProj a b ℓ : B̂ →+* B_ℓ` (any prime `ℓ`, also `ℓ ∣ D`): the `ℓ`-component, coordinatewise through
  `RestrictedProduct.evalRingHom`; `localProjUnits a b ℓ : B̂^× →* B_ℓ^×`.
* `DefiniteData.iota d ℓ hℓ` (`ℓ ∤ D`): **the** choice term `Classical.choose (maximalOrder_local_split d.O d.hD ℓ hℓ)`
  of the import, so that `ellAdicSplitting` and `localHeckeEmbedding` are definitionally built from it
  (`iota_comp_baseChange_eq_ellAdicSplitting` is `rfl`; plan stage-01 §12 Q4 / F7).
* `DefiniteData.iotaGL d ℓ hℓ : B_ℓ^× ≃* GL₂(ℚ_ℓ)`.
* `localComponent d ℓ hℓ : B̂^× →* GL₂(ℚ_ℓ)`, `u ↦ ι_ℓ(u_ℓ)`; `localComponent_finEmbed`.
* `mem_latticeCompletion_iff_local` (public re-proof of the import's private ClassSet helper
  `mem_latticeCompletion_iff_local_aux`, "item 43(d)", risk R6): membership in `L̂` is local.
* `localComponent_integral`, `localComponent_inv_integral`: for `u ∈ Ô^×` the matrices `ι_ℓ(u_ℓ)^{±1}` have entries
  in `ℤ_ℓ` `localComponent_mem_GL2Zl`, `Ohat_le_comap_GL2Zl`: `localComponent d ℓ hℓ (Ô^×) ⊆ GL2Zl ℓ` (S01-L3a).

Status: *formalized*.
-/

namespace Langlandscape.Quat

open GL2TF
open GL2TF.Quat (baseChange localLattice latticeCompletion maximalOrder_local_split ellAdicSplitting)

/-! ### Evaluation at a prime -/

/-- A prime `ℓ` (given through `[Fact ℓ.Prime]`) as an index of the restricted product `𝔸_f`. -/
def primeIdx (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : Nat.Primes := ⟨ℓ, hℓ.out⟩

/-- `primeIdx ℓ` has value `ℓ` (`def:s01-B`, `s01-B`). -/
@[simp] lemma primeIdx_coe (ℓ : ℕ) [Fact ℓ.Prime] : ((primeIdx ℓ : Nat.Primes) : ℕ) = ℓ := rfl

/-- `primeIdx` of a `Nat.Primes` is itself (`def:s01-B`, `s01-B`). -/
@[simp] lemma primeIdx_val (p : Nat.Primes) : primeIdx (p : ℕ) = p := rfl

/-- `def:s01-B`: the `ℓ`-component `𝔸_f → ℚ_ℓ`. -/
noncomputable def adeleProj (ℓ : ℕ) [Fact ℓ.Prime] : FinAdele →+* ℚ_[ℓ] :=
  RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) (primeIdx ℓ)

/-- `def:s01-B`: the `ℓ`-component `B̂ → B_ℓ = ℍ[ℚ_ℓ,a,0,b]`, for every prime `ℓ` (including `ℓ ∣ D`). -/
noncomputable def localProj (a b : ℤ) (ℓ : ℕ) [Fact ℓ.Prime] : BHat a b →+* QuatAlg ℚ_[ℓ] a b :=
  baseChange a b (adeleProj ℓ)

/-- `def:s01-B`: the `ℓ`-component `B̂^× → B_ℓ^×`, for every prime `ℓ`. -/
noncomputable def localProjUnits (a b : ℤ) (ℓ : ℕ) [Fact ℓ.Prime] : (BHat a b)ˣ →* (QuatAlg ℚ_[ℓ] a b)ˣ :=
  Units.map (localProj a b ℓ).toMonoidHom

section localProj

variable {a b : ℤ} {ℓ : ℕ} [Fact ℓ.Prime]

/-- Value of `localProjUnits` (`def:s01-B`, `s01-B`). -/
@[simp] lemma localProjUnits_val (u : (BHat a b)ˣ) :
    ((localProjUnits a b ℓ u : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b) = localProj a b ℓ (u : BHat a b) :=
  rfl

/-- `localProj` on `finEmbed`: the `ℓ`-component of `ι(z)` is the base change of `z` to `ℚ_ℓ` (`def:s01-B`). -/
@[simp] theorem localProj_finEmbed (z : GL2TF.Quat.QuatAlg ℚ a b) :
    localProj a b ℓ (finEmbed a b z) = baseChange a b (algebraMap ℚ ℚ_[ℓ]) z := by
  ext <;> rfl

/-- `localProj` is `𝔸_f`-semilinear over `adeleProj` (`def:s01-B`, `s01-B`). -/
theorem localProj_smul (c : FinAdele) (v : BHat a b) :
    localProj a b ℓ (c • v) = adeleProj ℓ c • localProj a b ℓ v := by
  ext <;> simp [localProj, baseChange] <;> rfl

/-- Extensionality of `B̂` through its local components (`def:s01-B`, `s01-B`). -/
theorem bhat_ext_local {v w : BHat a b} (h : ∀ p : Nat.Primes, localProj a b p v = localProj a b p w) : v = w := by
  apply QuaternionAlgebra.ext
  · ext p; exact congrArg QuaternionAlgebra.re (h p)
  · ext p; exact congrArg QuaternionAlgebra.imI (h p)
  · ext p; exact congrArg QuaternionAlgebra.imJ (h p)
  · ext p; exact congrArg QuaternionAlgebra.imK (h p)

end localProj

/-! ### Local description of `L̂` (re-proof of the import's private item 43(d) helper, risk R6) -/

section Local

variable {a b : ℤ}

/-- Membership in `L̂` is local: `w ∈ L̂ ↔ w_p ∈ L_p` for every prime `p` (`def:s01-B`, `s01-B`).
Adapted from the import's private `GL2TF.Quat.mem_latticeCompletion_iff_local_aux` (`AlgJL/VolIII/P2/ClassSet.lean`,
"item 43(d)"). -/
theorem mem_latticeCompletion_iff_local (L : Submodule ℤ (GL2TF.Quat.QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (GL2TF.Quat.QuatAlg ℚ a b)) = ⊤) (w : BHat a b) :
    w ∈ latticeCompletion L ↔ ∀ p : Nat.Primes, localProj a b p w ∈ localLattice p L := by
  obtain ⟨e, f, hf⟩ := GL2TF.Quat.exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, _, hF3⟩ := GL2TF.Quat.exists_bhat_basis e f hf
  have hloc : ∀ p : Nat.Primes, ∃ Fp : Module.Basis (Fin 4) ℚ_[p] (GL2TF.Quat.QuatAlg ℚ_[p] a b),
      (∀ i, Fp i = baseChange a b (algebraMap ℚ ℚ_[p]) (f i)) ∧
      ∀ i, Fp.repr (localProj a b p w) i = F.repr w i p := by
    intro p
    obtain ⟨Fp, hFp1, -⟩ := GL2TF.Quat.exists_baseChange_basis (S := ℚ_[p]) a b f
    refine ⟨Fp, hFp1, fun i => ?_⟩
    have : localProj a b p w = ∑ j, (F.repr w j p) • Fp j := by
      conv_lhs => rw [← F.sum_repr w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [localProj_smul, hF1, localProj_finEmbed, hFp1]
      rfl
    rw [this, Module.Basis.repr_sum_self]
  choose Fp hFp1 hFp2 using hloc
  rw [hF3]
  have hspan_iff : ∀ p : Nat.Primes, localProj a b p w ∈ localLattice p L ↔
      ∀ i, F.repr w i p ∈ PadicInt.subring p := by
    intro p
    refine (GL2TF.Quat.mem_span_image_iff_repr (R := ℤ_[p]) e (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom
      (Fp p) (fun i => by rw [← hf]; exact hFp1 p i) _).trans ?_
    simp only [hFp2]
    exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  simp only [hspan_iff, mem_zhat]
  exact ⟨fun h p i => h i p, fun h i p => h p i⟩

/-- The `ℓ`-component of an element of `L̂` lies in `L_ℓ` (`def:s01-B`, `s01-B`). -/
theorem localProj_mem_localLattice {L : Submodule ℤ (GL2TF.Quat.QuatAlg ℚ a b)} (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (GL2TF.Quat.QuatAlg ℚ a b)) = ⊤) {w : BHat a b} (hw : w ∈ latticeCompletion L)
    (ℓ : ℕ) [Fact ℓ.Prime] : localProj a b ℓ w ∈ localLattice ℓ L :=
  (mem_latticeCompletion_iff_local L hfg hspan w).1 hw (primeIdx ℓ)

/-- Local description of `Ô^×`: `u ∈ Ô^× ↔ u_p, u_p⁻¹ ∈ 𝒪_p` for every prime `p` (`def:s01-B`, `s01-B`). -/
theorem mem_orderCompletionUnits_iff_local (O : GL2TF.Quat.QOrder a b) (u : (BHat a b)ˣ) :
    u ∈ orderCompletionUnits O ↔ ∀ p : Nat.Primes,
      localProj a b p (u : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ∧
      localProj a b p ((u⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  show _ ∧ _ ↔ _
  rw [mem_latticeCompletion_iff_local _ O.fg O.span_eq_top, mem_latticeCompletion_iff_local _ O.fg O.span_eq_top]
  exact ⟨fun h p => ⟨h.1 p, h.2 p⟩, fun h => ⟨fun p => (h p).1, fun p => (h p).2⟩⟩

end Local

/-! ### The splittings `ι_ℓ` and the local components -/

namespace DefiniteData

variable (d : DefiniteData) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-B`: the fixed splitting `ι_ℓ : B_ℓ ≃ₐ M₂(ℚ_ℓ)` with `ι_ℓ(𝒪_ℓ) = M₂(ℤ_ℓ)`, `ℓ ∤ D`. This is the import's
choice term `Classical.choose (maximalOrder_local_split …)` (the same as in `ellAdicSplitting` and
`localHeckeEmbedding`; F7). -/
noncomputable def iota : QuatAlg ℚ_[ℓ] d.a d.b ≃ₐ[ℚ_[ℓ]] Matrix (Fin 2) (Fin 2) ℚ_[ℓ] :=
  Classical.choose (maximalOrder_local_split d.O d.hD ℓ hℓ)

/-- `def:s01-B`: `ι_ℓ(𝒪_ℓ) = M₂(ℤ_ℓ)` (`s01-B`). -/
theorem iota_image_localLattice :
    (d.iota ℓ hℓ) '' (localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) : Set (QuatAlg ℚ_[ℓ] d.a d.b)) =
      Set.range fun m : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] => m.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) :=
  Classical.choose_spec (maximalOrder_local_split d.O d.hD ℓ hℓ)

/-- `def:s01-B`: `z ∈ 𝒪_ℓ ↔ ι_ℓ(z)` has entries in `ℤ_ℓ` (`s01-B`). -/
theorem mem_localLattice_iff_iota (z : QuatAlg ℚ_[ℓ] d.a d.b) :
    z ∈ localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) ↔ ∀ i j, ‖d.iota ℓ hℓ z i j‖ ≤ 1 := by
  have hι := d.iota_image_localLattice ℓ hℓ
  constructor
  · intro hz i j
    obtain ⟨m, hm⟩ : d.iota ℓ hℓ z ∈ Set.range fun m : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] =>
        m.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := hι ▸ ⟨z, hz, rfl⟩
    rw [← hm]
    exact PadicInt.norm_le_one (m i j)
  · intro h
    have : d.iota ℓ hℓ z ∈ (d.iota ℓ hℓ) ''
        (localLattice ℓ (Subalgebra.toSubmodule d.O.1.toSubalgebra) : Set (QuatAlg ℚ_[ℓ] d.a d.b)) := by
      rw [hι]
      exact ⟨fun i j => ⟨_, h i j⟩, by ext i j; rfl⟩
    obtain ⟨z', hz', hzz⟩ := this
    rwa [← (d.iota ℓ hℓ).injective hzz]

/-- `def:s01-B`, F7: the import's `ellAdicSplitting` is `ι_ℓ ∘ (B → B_ℓ)`, definitionally (`s01-B`). -/
theorem iota_comp_baseChange_eq_ellAdicSplitting :
    ellAdicSplitting d.O d.hD ℓ hℓ =
      RingHom.toRatAlgHom ((d.iota ℓ hℓ).toRingEquiv.toRingHom.comp (baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]))) :=
  rfl

/-- `def:s01-B`: `ι_ℓ` on unit groups, `B_ℓ^× ≃* GL₂(ℚ_ℓ)`. -/
noncomputable def iotaGL : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ ≃* GL (Fin 2) ℚ_[ℓ] :=
  Units.mapEquiv (d.iota ℓ hℓ).toMulEquiv

/-- Value of `iotaGL` (`def:s01-B`, `s01-B`). -/
@[simp] lemma iotaGL_val (x : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) :
    ((d.iotaGL ℓ hℓ x : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) = d.iota ℓ hℓ (x : QuatAlg ℚ_[ℓ] d.a d.b) :=
  rfl

/-- Value of `iotaGL.symm` (`def:s01-B`, `s01-B`). -/
@[simp] lemma iotaGL_symm_val (g : GL (Fin 2) ℚ_[ℓ]) :
    (((d.iotaGL ℓ hℓ).symm g : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) : QuatAlg ℚ_[ℓ] d.a d.b) =
      (d.iota ℓ hℓ).symm (g : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) :=
  rfl

end DefiniteData

variable (d : DefiniteData)

/-- `def:s01-B`, `def:s01-levels`: the local component `B̂^× → GL₂(ℚ_ℓ)`, `u ↦ ι_ℓ(u_ℓ)`, for `ℓ ∤ D`. The term is
the one used in the import's `localHeckeEmbedding` (with `p = primeIdx ℓ`). -/
noncomputable def localComponent (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D) : (BHat d.a d.b)ˣ →* GL (Fin 2) ℚ_[ℓ] :=
  Units.map ((d.iota ℓ hℓ).toRingEquiv.toRingHom.comp (localProj d.a d.b ℓ)).toMonoidHom

variable {d} {ℓ : ℕ} [Fact ℓ.Prime] {hℓ : ¬ ℓ ∣ d.D}

/-- Value of `localComponent`: `ι_ℓ(u_ℓ)` (`def:s01-B`, `s01-B`). -/
@[simp] lemma localComponent_val (u : (BHat d.a d.b)ˣ) :
    ((localComponent d ℓ hℓ u : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      d.iota ℓ hℓ (localProj d.a d.b ℓ (u : BHat d.a d.b)) :=
  rfl

/-- `localComponent = ι_ℓ ∘ (·)_ℓ` on unit groups (`def:s01-B`, `s01-B`). -/
theorem localComponent_eq_iotaGL_comp :
    localComponent d ℓ hℓ = (d.iotaGL ℓ hℓ).toMonoidHom.comp (localProjUnits d.a d.b ℓ) :=
  rfl

/-- `localComponent u = ι_ℓ(u_ℓ)` as an identity in `GL₂(ℚ_ℓ)` (`def:s01-B`, `s01-B`). -/
theorem localComponent_apply (u : (BHat d.a d.b)ˣ) :
    localComponent d ℓ hℓ u = d.iotaGL ℓ hℓ (localProjUnits d.a d.b ℓ u) :=
  rfl

/-- `def:s01-B`: on global units, `localComponent (ι(γ)) = ι_ℓ(γ)` (`s01-B`). -/
theorem localComponent_finEmbed (γ : (GL2TF.Quat.QuatAlg ℚ d.a d.b)ˣ) :
    ((localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) : GL (Fin 2) ℚ_[ℓ]) :
        Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      d.iota ℓ hℓ (baseChange d.a d.b (algebraMap ℚ ℚ_[ℓ]) (γ : GL2TF.Quat.QuatAlg ℚ d.a d.b)) := by
  rw [localComponent_val]
  exact congrArg (d.iota ℓ hℓ) (localProj_finEmbed (γ : GL2TF.Quat.QuatAlg ℚ d.a d.b))

/-- `def:s01-B`, F7: on global units, `localComponent (ι(γ))` is the import's `ellAdicSplitting` of `γ` (`s01-B`). -/
theorem localComponent_finEmbed_eq_ellAdicSplitting (γ : (GL2TF.Quat.QuatAlg ℚ d.a d.b)ˣ) :
    ((localComponent d ℓ hℓ (Units.map (finEmbed d.a d.b).toMonoidHom γ) : GL (Fin 2) ℚ_[ℓ]) :
        Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      ellAdicSplitting d.O d.hD ℓ hℓ (γ : GL2TF.Quat.QuatAlg ℚ d.a d.b) :=
  localComponent_finEmbed γ

/-! ### `Ô^×` maps into `GL₂(ℤ_ℓ)` -/

/-- `def:s01-levels`: for `u ∈ Ô^×` the matrix `ι_ℓ(u_ℓ)` has entries in `ℤ_ℓ` (`s01-levels`). -/
theorem localComponent_integral {u : (BHat d.a d.b)ˣ} (hu : u ∈ orderCompletionUnits d.O.1) (i j : Fin 2) :
    ‖((localComponent d ℓ hℓ u : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j‖ ≤ 1 :=
  (d.mem_localLattice_iff_iota ℓ hℓ _).1
    (localProj_mem_localLattice d.O.1.fg d.O.1.span_eq_top hu.1 ℓ) i j

/-- `def:s01-levels`: for `u ∈ Ô^×` the matrix `ι_ℓ(u_ℓ)⁻¹` has entries in `ℤ_ℓ` (`s01-levels`). -/
theorem localComponent_inv_integral {u : (BHat d.a d.b)ˣ} (hu : u ∈ orderCompletionUnits d.O.1) (i j : Fin 2) :
    ‖(((localComponent d ℓ hℓ u)⁻¹ : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) i j‖ ≤ 1 := by
  rw [← map_inv]
  exact localComponent_integral (inv_mem hu) i j

/-- `def:s01-levels`: `Ô^×` maps into `GL₂(ℤ_ℓ)` under `localComponent` (`s01-levels`). -/
theorem localComponent_mem_GL2Zl {u : (BHat d.a d.b)ˣ} (hu : u ∈ orderCompletionUnits d.O.1) :
    localComponent d ℓ hℓ u ∈ Langlandscape.Local.GL2Zl ℓ :=
  ⟨localComponent_integral hu, localComponent_inv_integral hu⟩

/-- `def:s01-levels`: `Ô^× ≤ localComponent⁻¹(GL₂(ℤ_ℓ))` (`s01-levels`). -/
theorem Ohat_le_comap_GL2Zl : d.Ohat ≤ (Langlandscape.Local.GL2Zl ℓ).comap (localComponent d ℓ hℓ) :=
  fun _ hu => localComponent_mem_GL2Zl hu

end Langlandscape.Quat
