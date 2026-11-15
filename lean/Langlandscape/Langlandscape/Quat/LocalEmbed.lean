/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Levels

/-!
# Local embeddings `B_ℓ^× → B̂^×` (S01-L3d)

Tex labels `def:s01-B`, `def:s01-levels` (and the factorisation of levels at a prime used in `def:s01-NUp`,
`lem:s01-Up`, `def:s01-hecke`).

* `glue g hg : B̂` — the element with local components `g p` (all but finitely many equal to `1`); adapted from the
  import's private `GL2TF.Quat.glueAux` (`AlgJL/VolIII/P2/ClassSet.lean`), risk R6/R7.
* `localEmbedHom a b ℓ : B_ℓ →* B̂` and `localEmbed a b ℓ : B_ℓ^× →* B̂^×` — component `x` at `ℓ`, `1` elsewhere. Defined
  for **every** prime `ℓ`, including `ℓ ∣ D` (no splitting needed).
* Components: `localProjUnits_localEmbed` (same prime), `localProjUnits_localEmbed_of_ne` (other primes).
* Commutation: `commute_localEmbed_of_commute`, `localEmbed_comm` (different primes commute).
* `localEmbed_mem_Ohat_iff`: `localEmbed ℓ x ∈ Ô^× ↔ x, x⁻¹ ∈ 𝒪_ℓ`.
* `localEmbedGL d p hp := localEmbed p ∘ ι_p⁻¹ : GL₂(ℚ_p) →* B̂^×` (`p ∤ D`); `localComponent_localEmbedGL`,
  `localComponent_localEmbedGL_of_ne`, `localEmbedGL_mem_Ohat_iff`.
* Factorisation at `p`: `IsInvariantAt d p hp U` (`U · localEmbedGL p (GL₂(ℤ_p)) ⊆ U`), closure lemmas
  (`isInvariantAt_Ohat`, `isInvariantAt_comap_of_ne`, `.inf`, `isInvariantAt_iInf`), the `p`-away part
  `awayAt d p hp u = u · localEmbedGL p (u_p)⁻¹` with `awayAt_mul_localEmbedGL`, and `mem_U_iff_factor_at`
  for any level of the shape `U' ⊓ K_p.comap (localComponent p)` with `U'` invariant at `p` and `K_p ≤ GL₂(ℤ_p)`.
* For the levels of S01-L3c: `mem_levelAt_iff_factor_at`, `mem_U0_iff_factor_at`, `mem_U1_iff_factor_at`,
  `mem_Utower_iff_factor_at` (`p ∣ N`), and `isInvariantAt_levelAt` (`p ∤ N`).

Status: *formalized*.
-/

namespace Langlandscape.Quat

open GL2TF
open GL2TF.Quat (localLattice)

/-! ### Gluing local components -/

section Glue

variable {a b : ℤ}

/-- `def:s01-B`: the element of `B̂` with `p`-components `g p`, where `g p = 1` for all but finitely many `p`.
Adapted from the import's private `GL2TF.Quat.glueAux` (`AlgJL/VolIII/P2/ClassSet.lean`). -/
noncomputable def glue (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) (hg : ∀ᶠ p in Filter.cofinite, g p = 1) :
    BHat a b :=
  ⟨⟨fun p => (g p).re, hg.mono fun p hp => by simp only [hp]; exact (PadicInt.subring _).one_mem⟩,
   ⟨fun p => (g p).imI, hg.mono fun p hp => by simp only [hp]; exact (PadicInt.subring _).zero_mem⟩,
   ⟨fun p => (g p).imJ, hg.mono fun p hp => by simp only [hp]; exact (PadicInt.subring _).zero_mem⟩,
   ⟨fun p => (g p).imK, hg.mono fun p hp => by simp only [hp]; exact (PadicInt.subring _).zero_mem⟩⟩

/-- The local components of `glue g hg` are the `g p` (`def:s01-B`, `s01-B`). -/
@[simp] theorem localProj_glue (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) (hg : ∀ᶠ p in Filter.cofinite, g p = 1)
    (p : Nat.Primes) : localProj a b p (glue g hg) = g p := by
  ext <;> rfl

end Glue

/-! ### The local embedding at a prime `ℓ` (any `ℓ`, also `ℓ ∣ D`) -/

section LocalEmbed

variable (a b : ℤ) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The family `p ↦ (x if p = ℓ, 1 otherwise)`. -/
noncomputable def singleFam (x : QuatAlg ℚ_[ℓ] a b) : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b :=
  Pi.mulSingle (M := fun p : Nat.Primes => QuatAlg ℚ_[p] a b) (primeIdx ℓ) x

/-- `singleFam ℓ x` at `ℓ` is `x` (`def:s01-B`, `s01-B`). -/
theorem singleFam_self (x : QuatAlg ℚ_[ℓ] a b) : singleFam a b ℓ x (primeIdx ℓ) = x :=
  Pi.mulSingle_eq_same (M := fun p : Nat.Primes => QuatAlg ℚ_[p] a b) (primeIdx ℓ) x

/-- `singleFam ℓ x` at `p ≠ ℓ` is `1` (`def:s01-B`, `s01-B`). -/
theorem singleFam_of_ne (x : QuatAlg ℚ_[ℓ] a b) {p : Nat.Primes} (h : p ≠ primeIdx ℓ) :
    singleFam a b ℓ x p = 1 :=
  Pi.mulSingle_eq_of_ne (M := fun p : Nat.Primes => QuatAlg ℚ_[p] a b) h x

/-- `singleFam ℓ x` is `1` away from `ℓ` (`def:s01-B`, `s01-B`). -/
lemma singleFam_eventually (x : QuatAlg ℚ_[ℓ] a b) : ∀ᶠ p in Filter.cofinite, singleFam a b ℓ x p = 1 :=
  Filter.eventually_cofinite.2 ((Set.finite_singleton (primeIdx ℓ)).subset fun p hp =>
    Set.mem_singleton_iff.2 (by
      by_contra h
      exact hp (singleFam_of_ne a b ℓ x h)))

/-- `def:s01-B`: `B_ℓ → B̂`, `x ↦ (x at ℓ, 1 elsewhere)`, as a monoid hom; for every prime `ℓ`. -/
noncomputable def localEmbedHom : QuatAlg ℚ_[ℓ] a b →* BHat a b where
  toFun x := glue (singleFam a b ℓ x) (singleFam_eventually a b ℓ x)
  map_one' := bhat_ext_local fun p => (localProj_glue _ _ p).trans
    ((congrFun (Pi.mulSingle_one (M := fun q : Nat.Primes => QuatAlg ℚ_[q] a b) (primeIdx ℓ)) p).trans
      (map_one (localProj a b p)).symm)
  map_mul' x y := bhat_ext_local fun p => (localProj_glue _ _ p).trans (by
    simp only [map_mul, localProj_glue]
    exact congrFun (Pi.mulSingle_mul (f := fun q : Nat.Primes => QuatAlg ℚ_[q] a b) (primeIdx ℓ) x y) p)

/-- `def:s01-B`: the local embedding `B_ℓ^× →* B̂^×` (component `x` at `ℓ`, `1` elsewhere), for every prime `ℓ`,
including `ℓ ∣ D`. -/
noncomputable def localEmbed : (QuatAlg ℚ_[ℓ] a b)ˣ →* (BHat a b)ˣ :=
  Units.map (localEmbedHom a b ℓ)

variable {a b ℓ}

/-- Value of `localEmbed` (`def:s01-B`, `s01-B`). -/
@[simp] lemma localEmbed_val (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    ((localEmbed a b ℓ x : (BHat a b)ˣ) : BHat a b) = localEmbedHom a b ℓ (x : QuatAlg ℚ_[ℓ] a b) :=
  rfl

/-- Value of `(localEmbed ℓ x)⁻¹` (`def:s01-B`, `s01-B`). -/
lemma localEmbed_inv_val (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    (((localEmbed a b ℓ x)⁻¹ : (BHat a b)ˣ) : BHat a b) =
      localEmbedHom a b ℓ ((x⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b) :=
  congrArg Units.val (map_inv (localEmbed a b ℓ) x).symm

/-- Components of `localEmbedHom` at an arbitrary prime index (`def:s01-B`, `s01-B`). -/
theorem localProj_localEmbedHom (x : QuatAlg ℚ_[ℓ] a b) (p : Nat.Primes) :
    localProj a b p (localEmbedHom a b ℓ x) = singleFam a b ℓ x p :=
  localProj_glue (singleFam a b ℓ x) (singleFam_eventually a b ℓ x) p

/-- `def:s01-B`: the `ℓ`-component of `localEmbedHom ℓ x` is `x` (`s01-B`). -/
@[simp] theorem localProj_localEmbedHom_self (x : QuatAlg ℚ_[ℓ] a b) :
    localProj a b ℓ (localEmbedHom a b ℓ x) = x :=
  (localProj_localEmbedHom x (primeIdx ℓ)).trans (singleFam_self a b ℓ x)

/-- `def:s01-B`: the `p`-component of `localEmbedHom ℓ x` is `1` for `p ≠ ℓ` (`s01-B`). -/
theorem localProj_localEmbedHom_of_ne (x : QuatAlg ℚ_[ℓ] a b) {p : Nat.Primes} (h : p ≠ primeIdx ℓ) :
    localProj a b p (localEmbedHom a b ℓ x) = 1 :=
  (localProj_localEmbedHom x p).trans (singleFam_of_ne a b ℓ x h)

/-- `def:s01-B`: the `q`-component of `localEmbedHom ℓ x` is `1` for primes `q ≠ ℓ` (`s01-B`). -/
theorem localProj_localEmbedHom_of_ne' {q : ℕ} [Fact q.Prime] (x : QuatAlg ℚ_[ℓ] a b) (h : q ≠ ℓ) :
    localProj a b q (localEmbedHom a b ℓ x) = 1 :=
  localProj_localEmbedHom_of_ne (p := primeIdx q) x fun h' => h (congrArg (fun r : Nat.Primes => (r : ℕ)) h')

/-- `def:s01-B`: the `ℓ`-component of `localEmbed ℓ x` is `x` (`s01-B`). -/
@[simp] theorem localProjUnits_localEmbed (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    localProjUnits a b ℓ (localEmbed a b ℓ x) = x :=
  Units.ext (localProj_localEmbedHom_self (x : QuatAlg ℚ_[ℓ] a b))

/-- `def:s01-B`: the `q`-component of `localEmbed ℓ x` is `1` for primes `q ≠ ℓ` (`s01-B`). -/
theorem localProjUnits_localEmbed_of_ne {q : ℕ} [Fact q.Prime] (x : (QuatAlg ℚ_[ℓ] a b)ˣ) (h : q ≠ ℓ) :
    localProjUnits a b q (localEmbed a b ℓ x) = 1 :=
  Units.ext (localProj_localEmbedHom_of_ne' (x : QuatAlg ℚ_[ℓ] a b) h)

/-- `def:s01-B`: `localEmbed ℓ x` commutes with every `u` whose `ℓ`-component commutes with `x` (`s01-B`). -/
theorem commute_localEmbed_of_commute (x : (QuatAlg ℚ_[ℓ] a b)ˣ) {u : (BHat a b)ˣ}
    (h : Commute x (localProjUnits a b ℓ u)) : Commute (localEmbed a b ℓ x) u := by
  refine Units.ext (bhat_ext_local fun p => ?_)
  simp only [Units.val_mul, map_mul, localEmbed_val, localProj_localEmbedHom]
  by_cases hp : p = primeIdx ℓ
  · subst hp
    rw [singleFam_self]
    exact congrArg Units.val h.eq
  · rw [singleFam_of_ne _ _ _ _ hp, one_mul, mul_one]

/-- `def:s01-B`: local embeddings at different primes commute (`s01-B`). -/
theorem localEmbed_comm {q : ℕ} [Fact q.Prime] (h : ℓ ≠ q) (x : (QuatAlg ℚ_[ℓ] a b)ˣ)
    (y : (QuatAlg ℚ_[q] a b)ˣ) : Commute (localEmbed a b ℓ x) (localEmbed a b q y) :=
  commute_localEmbed_of_commute x (by rw [localProjUnits_localEmbed_of_ne y h]; exact Commute.one_right x)

/-! #### Integrality -/

/-- `1 ∈ 𝒪_ℓ` (`def:s01-B`, `s01-B`). -/
theorem one_mem_localLattice (O : GL2TF.Quat.QOrder a b) (p : ℕ) [Fact p.Prime] :
    (1 : QuatAlg ℚ_[p] a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  unfold localLattice
  exact Submodule.subset_span ⟨1, O.toSubalgebra.one_mem, map_one _⟩

/-- `def:s01-B`: `localEmbed ℓ x ∈ Ô^×` iff `x, x⁻¹ ∈ 𝒪_ℓ`, for every prime `ℓ` (also `ℓ ∣ D`) (`s01-B`). -/
theorem localEmbed_mem_orderCompletionUnits_iff (O : GL2TF.Quat.QOrder a b) (x : (QuatAlg ℚ_[ℓ] a b)ˣ) :
    localEmbed a b ℓ x ∈ orderCompletionUnits O ↔
      (x : QuatAlg ℚ_[ℓ] a b) ∈ localLattice ℓ (Subalgebra.toSubmodule O.toSubalgebra) ∧
      ((x⁻¹ : (QuatAlg ℚ_[ℓ] a b)ˣ) : QuatAlg ℚ_[ℓ] a b) ∈
        localLattice ℓ (Subalgebra.toSubmodule O.toSubalgebra) := by
  rw [mem_orderCompletionUnits_iff_local]
  simp only [localEmbed_val, localEmbed_inv_val, localProj_localEmbedHom]
  constructor
  · intro h
    have h' := h (primeIdx ℓ)
    rw [singleFam_self, singleFam_self] at h'
    exact h'
  · intro h p
    by_cases hp : p = primeIdx ℓ
    · subst hp
      rw [singleFam_self, singleFam_self]
      exact h
    · rw [singleFam_of_ne _ _ _ _ hp, singleFam_of_ne _ _ _ _ hp]
      exact ⟨one_mem_localLattice O p, one_mem_localLattice O p⟩

end LocalEmbed

/-! ### Split primes: `localEmbedGL` -/

variable {d : DefiniteData}

/-- `def:s01-levels`: `GL₂(ℚ_p) →* B̂^×`, `g ↦ localEmbed p (ι_p⁻¹ g)`, for `p ∤ D`. -/
noncomputable def localEmbedGL (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) :
    GL (Fin 2) ℚ_[p] →* (BHat d.a d.b)ˣ :=
  (localEmbed d.a d.b p).comp (d.iotaGL p hp).symm.toMonoidHom

variable {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- Unfolding `localEmbedGL` (`def:s01-levels`, `s01-levels`). -/
theorem localEmbedGL_apply (g : GL (Fin 2) ℚ_[p]) :
    localEmbedGL d p hp g = localEmbed d.a d.b p ((d.iotaGL p hp).symm g) :=
  rfl

/-- `def:s01-levels`: `localComponent p ∘ localEmbedGL p = id` (`s01-levels`). -/
@[simp] theorem localComponent_localEmbedGL (g : GL (Fin 2) ℚ_[p]) :
    localComponent d p hp (localEmbedGL d p hp g) = g := by
  rw [localComponent_apply, localEmbedGL_apply, localProjUnits_localEmbed, MulEquiv.apply_symm_apply]

/-- `def:s01-levels`: the `q`-component of `localEmbed ℓ x` is `1` for split `q ≠ ℓ` (`s01-levels`). -/
theorem localComponent_localEmbed_of_ne {ℓ q : ℕ} [Fact ℓ.Prime] [Fact q.Prime] {hq : ¬ q ∣ d.D}
    (x : (QuatAlg ℚ_[ℓ] d.a d.b)ˣ) (h : q ≠ ℓ) : localComponent d q hq (localEmbed d.a d.b ℓ x) = 1 := by
  rw [localComponent_apply, localProjUnits_localEmbed_of_ne x h, map_one]

/-- `def:s01-levels`: `localComponent q ∘ localEmbedGL p = 1` for `q ≠ p` (`s01-levels`). -/
theorem localComponent_localEmbedGL_of_ne {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} (g : GL (Fin 2) ℚ_[p])
    (h : q ≠ p) : localComponent d q hq (localEmbedGL d p hp g) = 1 := by
  rw [localEmbedGL_apply]
  exact localComponent_localEmbed_of_ne _ h

/-- `def:s01-levels`: the `q`-component of `localEmbedGL p g` is `1` for every prime `q ≠ p` (also `q ∣ D`)
(`s01-levels`). -/
theorem localProjUnits_localEmbedGL_of_ne {q : ℕ} [Fact q.Prime] (g : GL (Fin 2) ℚ_[p]) (h : q ≠ p) :
    localProjUnits d.a d.b q (localEmbedGL d p hp g) = 1 := by
  rw [localEmbedGL_apply]
  exact localProjUnits_localEmbed_of_ne _ h

/-- `def:s01-levels`: local embeddings at different split primes commute (`s01-levels`). -/
theorem localEmbedGL_comm {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} (h : p ≠ q) (g : GL (Fin 2) ℚ_[p])
    (g' : GL (Fin 2) ℚ_[q]) : Commute (localEmbedGL d p hp g) (localEmbedGL d q hq g') := by
  simp only [localEmbedGL_apply]
  exact localEmbed_comm h _ _

/-- `def:s01-levels`: `localEmbedGL p g ∈ Ô^× ↔ g ∈ GL₂(ℤ_p)` (`s01-levels`). -/
theorem localEmbedGL_mem_Ohat_iff (g : GL (Fin 2) ℚ_[p]) :
    localEmbedGL d p hp g ∈ d.Ohat ↔ g ∈ Langlandscape.Local.GL2Zl p := by
  constructor
  · intro h
    simpa using localComponent_mem_GL2Zl (hℓ := hp) h
  · intro hg
    rw [localEmbedGL_apply]
    refine (localEmbed_mem_orderCompletionUnits_iff d.O.1 _).2
      ⟨(d.mem_localLattice_iff_iota p hp _).2 fun i j => ?_,
        (d.mem_localLattice_iff_iota p hp _).2 fun i j => ?_⟩
    · rw [DefiniteData.iotaGL_symm_val, AlgEquiv.apply_symm_apply]
      exact hg.1 i j
    · rw [← map_inv, DefiniteData.iotaGL_symm_val, AlgEquiv.apply_symm_apply]
      exact hg.2 i j

/-- `def:s01-levels`: `localEmbedGL p (GL₂(ℤ_p)) ⊆ Ô^×` (`s01-levels`). -/
theorem localEmbedGL_mem_Ohat {g : GL (Fin 2) ℚ_[p]} (hg : g ∈ Langlandscape.Local.GL2Zl p) :
    localEmbedGL d p hp g ∈ d.Ohat :=
  (localEmbedGL_mem_Ohat_iff g).2 hg

/-- `def:s01-levels`: right multiplication by `localEmbedGL p k` does not change the components at `q ≠ p`
(`s01-levels`). -/
theorem localComponent_mul_localEmbedGL_of_ne {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} (u : (BHat d.a d.b)ˣ)
    (k : GL (Fin 2) ℚ_[p]) (h : q ≠ p) :
    localComponent d q hq (u * localEmbedGL d p hp k) = localComponent d q hq u := by
  rw [map_mul, localComponent_localEmbedGL_of_ne k h, mul_one]

/-- `def:s01-levels`: as `localComponent_mul_localEmbedGL_of_ne`, for every prime `q ≠ p` (`s01-levels`). -/
theorem localProjUnits_mul_localEmbedGL_of_ne {q : ℕ} [Fact q.Prime] (u : (BHat d.a d.b)ˣ)
    (k : GL (Fin 2) ℚ_[p]) (h : q ≠ p) :
    localProjUnits d.a d.b q (u * localEmbedGL d p hp k) = localProjUnits d.a d.b q u := by
  rw [map_mul, localProjUnits_localEmbedGL_of_ne k h, mul_one]

/-! ### Factorisation of levels at `p` -/

/-- `def:s01-levels`: `U` is invariant at `p` if `U · localEmbedGL p (GL₂(ℤ_p)) ⊆ U`, i.e. `U` imposes at `p` at most
the condition `u_p ∈ GL₂(ℤ_p)` (e.g. `Ô^×`, or conditions at primes `q ≠ p`). -/
def IsInvariantAt (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    Prop :=
  ∀ u ∈ U, ∀ k ∈ Langlandscape.Local.GL2Zl p, u * localEmbedGL d p hp k ∈ U

/-- Invariance at `p`, as an equivalence (`def:s01-levels`, `s01-levels`). -/
theorem IsInvariantAt.mul_mem_iff {U : Subgroup (BHat d.a d.b)ˣ} (hU : IsInvariantAt d p hp U)
    (u : (BHat d.a d.b)ˣ) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ Langlandscape.Local.GL2Zl p) :
    u * localEmbedGL d p hp k ∈ U ↔ u ∈ U := by
  refine ⟨fun h => ?_, fun h => hU u h k hk⟩
  have := hU _ h k⁻¹ (inv_mem hk)
  rwa [map_inv, mul_inv_cancel_right] at this

/-- `def:s01-levels`: `Ô^×` is invariant at every split `p` (`s01-levels`). -/
theorem isInvariantAt_Ohat : IsInvariantAt d p hp d.Ohat :=
  fun _ hu _ hk => mul_mem hu (localEmbedGL_mem_Ohat hk)

/-- `def:s01-levels`: `⊤` is invariant at `p` (`s01-levels`). -/
theorem isInvariantAt_top : IsInvariantAt d p hp ⊤ := fun _ _ _ _ => Subgroup.mem_top _

/-- `def:s01-levels`: a local condition at a split prime `q ≠ p` is invariant at `p` (`s01-levels`). -/
theorem isInvariantAt_comap_of_ne {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} (h : q ≠ p)
    (H : Subgroup (GL (Fin 2) ℚ_[q])) : IsInvariantAt d p hp (H.comap (localComponent d q hq)) :=
  fun u hu k _ => by
    rw [Subgroup.mem_comap, localComponent_mul_localEmbedGL_of_ne u k h]
    exact hu

/-- `def:s01-levels`: a local condition at any prime `q ≠ p` (also `q ∣ D`) is invariant at `p` (`s01-levels`). -/
theorem isInvariantAt_comap_localProjUnits_of_ne {q : ℕ} [Fact q.Prime] (h : q ≠ p)
    (H : Subgroup (QuatAlg ℚ_[q] d.a d.b)ˣ) :
    IsInvariantAt d p hp (H.comap (localProjUnits d.a d.b q)) :=
  fun u hu k _ => by
    rw [Subgroup.mem_comap, localProjUnits_mul_localEmbedGL_of_ne u k h]
    exact hu

/-- `def:s01-levels`: invariance is stable under `⊓` (`s01-levels`). -/
theorem IsInvariantAt.inf {U V : Subgroup (BHat d.a d.b)ˣ} (hU : IsInvariantAt d p hp U)
    (hV : IsInvariantAt d p hp V) : IsInvariantAt d p hp (U ⊓ V) :=
  fun u hu k hk => ⟨hU u hu.1 k hk, hV u hu.2 k hk⟩

/-- `def:s01-levels`: invariance is stable under `⨅` (`s01-levels`). -/
theorem isInvariantAt_iInf {ι : Sort*} {U : ι → Subgroup (BHat d.a d.b)ˣ}
    (hU : ∀ i, IsInvariantAt d p hp (U i)) : IsInvariantAt d p hp (⨅ i, U i) :=
  fun u hu k hk => Subgroup.mem_iInf.2 fun i => hU i u (Subgroup.mem_iInf.1 hu i) k hk

/-- `def:s01-levels`: the `p`-away part `u · localEmbedGL p (u_p)⁻¹` of `u` (`p`-component `1`, the other components
those of `u`). -/
noncomputable def awayAt (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (u : (BHat d.a d.b)ˣ) :
    (BHat d.a d.b)ˣ :=
  u * localEmbedGL d p hp (localComponent d p hp u)⁻¹

/-- `def:s01-levels`: `u = awayAt p u · localEmbedGL p (u_p)` (`s01-levels`). -/
theorem awayAt_mul_localEmbedGL (u : (BHat d.a d.b)ˣ) :
    awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u) = u := by
  rw [awayAt, map_inv, inv_mul_cancel_right]

/-- `def:s01-levels`: the `p`-component of `awayAt p u` is `1` (`s01-levels`). -/
@[simp] theorem localComponent_awayAt (u : (BHat d.a d.b)ˣ) : localComponent d p hp (awayAt d p hp u) = 1 := by
  rw [awayAt, map_mul, localComponent_localEmbedGL, mul_inv_cancel]

/-- `def:s01-levels`: the `p`-component of `awayAt p u` is `1`, in `B_p^×` (`s01-levels`). -/
@[simp] theorem localProjUnits_awayAt (u : (BHat d.a d.b)ˣ) :
    localProjUnits d.a d.b p (awayAt d p hp u) = 1 := by
  have h := localComponent_awayAt (hp := hp) u
  rw [localComponent_apply] at h
  exact (d.iotaGL p hp).injective (h.trans (map_one _).symm)

/-- `def:s01-levels`: the components of `awayAt p u` at primes `q ≠ p` are those of `u` (`s01-levels`). -/
theorem localProjUnits_awayAt_of_ne {q : ℕ} [Fact q.Prime] (u : (BHat d.a d.b)ˣ) (h : q ≠ p) :
    localProjUnits d.a d.b q (awayAt d p hp u) = localProjUnits d.a d.b q u := by
  rw [awayAt]
  exact localProjUnits_mul_localEmbedGL_of_ne u _ h

/-- `def:s01-levels`: the split components of `awayAt p u` at `q ≠ p` are those of `u` (`s01-levels`). -/
theorem localComponent_awayAt_of_ne {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} (u : (BHat d.a d.b)ˣ) (h : q ≠ p) :
    localComponent d q hq (awayAt d p hp u) = localComponent d q hq u := by
  rw [awayAt]
  exact localComponent_mul_localEmbedGL_of_ne u _ h

/-- `def:s01-levels`: `awayAt p u` commutes with `localEmbedGL p g` (`s01-levels`). -/
theorem commute_awayAt_localEmbedGL (u : (BHat d.a d.b)ˣ) (g : GL (Fin 2) ℚ_[p]) :
    Commute (awayAt d p hp u) (localEmbedGL d p hp g) := by
  rw [localEmbedGL_apply]
  exact (commute_localEmbed_of_commute _ (by rw [localProjUnits_awayAt]; exact Commute.one_right _)).symm

/-- `def:s01-levels`: factorisation of levels at `p`. Let `U = U' ⊓ K_p.comap (localComponent p)` with `U'` invariant
at `p` and `K_p ≤ GL₂(ℤ_p)` (all levels of S01-L3c have this shape at every `p ∤ D`). Then `u ∈ U` iff its `p`-away
part `u · localEmbedGL p (u_p)⁻¹` lies in `U` and `u_p ∈ K_p` (`s01-levels`). -/
theorem mem_U_iff_factor_at {U' : Subgroup (BHat d.a d.b)ˣ} {Kp : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU' : IsInvariantAt d p hp U') (hK : Kp ≤ Langlandscape.Local.GL2Zl p) (u : (BHat d.a d.b)ˣ) :
    u ∈ U' ⊓ Kp.comap (localComponent d p hp) ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ U' ⊓ Kp.comap (localComponent d p hp) ∧
        localComponent d p hp u ∈ Kp := by
  have hc : localComponent d p hp (u * localEmbedGL d p hp (localComponent d p hp u)⁻¹) = 1 :=
    localComponent_awayAt u
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, hc, one_mem, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hU' u h1 _ (inv_mem (hK h2)), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hU'.mul_mem_iff u (inv_mem (hK h2))).1 h1, h2⟩

/-- `def:s01-levels`: for `U = U' ⊓ K_p.comap (localComponent p)` as in `mem_U_iff_factor_at`,
`localEmbedGL p (K_p) ⊆ U` (`s01-levels`). -/
theorem localEmbedGL_mem_inf_comap {U' : Subgroup (BHat d.a d.b)ˣ} {Kp : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU' : IsInvariantAt d p hp U') (hK : Kp ≤ Langlandscape.Local.GL2Zl p) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ Kp) : localEmbedGL d p hp k ∈ U' ⊓ Kp.comap (localComponent d p hp) := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h := hU' 1 (one_mem _) k (hK hk)
    rwa [one_mul] at h
  · show localComponent d p hp (localEmbedGL d p hp k) ∈ Kp
    rw [localComponent_localEmbedGL]
    exact hk

/-! ### The levels of S01-L3c -/

section Levels

open Langlandscape.Local

/-- `def:s01-levels`: factorisation of the generic level `levelAt d N hN K` at a prime `p ∣ N`: `u ∈ U` iff its
`p`-away part `u · localEmbedGL p (u_p)⁻¹` lies in `U` and `u_p ∈ K p (v_p N)` (`s01-levels`). -/
theorem mem_levelAt_iff_factor_at {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])}
    (hK : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ), K ℓ e ≤ GL2Zl ℓ) (hpN : p ∈ N.primeFactors)
    (u : (BHat d.a d.b)ˣ) :
    u ∈ d.levelAt N hN K ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ d.levelAt N hN K ∧
        localComponent d p hp u ∈ K p (N.factorization p) := by
  have hw1 : localComponent d p hp (awayAt d p hp u) = 1 := localComponent_awayAt u
  change u ∈ d.levelAt N hN K ↔ awayAt d p hp u ∈ d.levelAt N hN K ∧ _
  simp only [DefiniteData.mem_levelAt_iff]
  constructor
  · rintro ⟨hO, hloc⟩
    have hup : localComponent d p hp u ∈ K p (N.factorization p) := hloc p hpN hp
    refine ⟨⟨isInvariantAt_Ohat (hp := hp) u hO _ (inv_mem (localComponent_mem_GL2Zl (hℓ := hp) hO)),
      fun ℓ _ hℓ hD => ?_⟩, hup⟩
    by_cases hℓp : ℓ = p
    · subst hℓp
      have : localComponent d ℓ hD (awayAt d ℓ hp u) = 1 := hw1
      rw [this]
      exact one_mem _
    · rw [localComponent_awayAt_of_ne u hℓp]
      exact hloc ℓ hℓ hD
  · rintro ⟨⟨hO, hloc⟩, hup⟩
    refine ⟨?_, fun ℓ _ hℓ hD => ?_⟩
    · rw [← awayAt_mul_localEmbedGL (hp := hp) u]
      exact isInvariantAt_Ohat (hp := hp) _ hO _ (hK p _ hup)
    · by_cases hℓp : ℓ = p
      · subst hℓp
        exact hup
      · rw [← localComponent_awayAt_of_ne (hp := hp) u hℓp]
        exact hloc ℓ hℓ hD

/-- `def:s01-levels`: the generic level `levelAt d N hN K` is invariant at every split `p ∤ N` (`s01-levels`). -/
theorem isInvariantAt_levelAt {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hpN : p ∉ N.primeFactors) :
    IsInvariantAt d p hp (d.levelAt N hN K) := by
  refine fun u hu k hk => ?_
  rw [DefiniteData.mem_levelAt_iff] at hu ⊢
  refine ⟨isInvariantAt_Ohat u hu.1 k hk, fun ℓ _ hℓ hD => ?_⟩
  have hℓp : ℓ ≠ p := fun h => hpN (h ▸ hℓ)
  rw [localComponent_mul_localEmbedGL_of_ne u k hℓp]
  exact hu.2 ℓ hℓ hD

/-- `def:s01-levels`: factorisation of `U_0(N)` at `p ∣ N` (`s01-levels`). -/
theorem mem_U0_iff_factor_at {N : ℕ} {hN : N.Coprime d.D} (hpN : p ∈ N.primeFactors) (u : (BHat d.a d.b)ˣ) :
    u ∈ d.U0 N hN ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ d.U0 N hN ∧
        localComponent d p hp u ∈ K0 p (N.factorization p) :=
  mem_levelAt_iff_factor_at (K := fun ℓ _ e => K0 ℓ e) (fun _ _ e => K0_le_GL2Zl e) hpN u

/-- `def:s01-levels`: factorisation of `U_1(N)` at `p ∣ N` (`s01-levels`). -/
theorem mem_U1_iff_factor_at {N : ℕ} {hN : N.Coprime d.D} (hpN : p ∈ N.primeFactors) (u : (BHat d.a d.b)ˣ) :
    u ∈ d.U1 N hN ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ d.U1 N hN ∧
        localComponent d p hp u ∈ K1 p (N.factorization p) :=
  mem_levelAt_iff_factor_at (K := fun ℓ _ e => K1 ℓ e) (fun _ _ e => K1_le_GL2Zl e) hpN u

/-- `def:s01-levels`: factorisation of the tower level `U_s = U_1(M p^s)` at `p` (`p ∤ M`, `s ≥ 1`): the local
condition at `p` is `K1 p s` (`s01-levels`). -/
theorem mem_Utower_iff_factor_at {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (u : (BHat d.a d.b)ˣ) :
    u ∈ d.Utower M p s hN ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ d.Utower M p s hN ∧
        localComponent d p hp u ∈ K1 p s := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpN : p ∈ (M * p ^ s).primeFactors :=
    Nat.mem_primeFactors.2 ⟨Fact.out, (dvd_pow_self p (by omega)).mul_left M,
      mul_ne_zero hM (pow_ne_zero _ hp0)⟩
  have hv : (M * p ^ s).factorization p = s := by
    rw [Nat.factorization_mul hM (pow_ne_zero _ hp0), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpM, Nat.Prime.factorization_pow (Fact.out : p.Prime),
      Finsupp.single_eq_same, zero_add]
  have h := mem_U1_iff_factor_at (hp := hp) (hN := hN) hpN u
  rw [hv] at h
  exact h

end Levels

end Langlandscape.Quat
