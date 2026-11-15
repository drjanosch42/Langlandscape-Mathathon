/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.DoubleCoset
import Langlandscape.Quat.Stab

/-!
# Named Hecke operators `T_ℓ`, `S_ℓ`, `U_ℓ`, `⟨d⟩` and commutation (S01-L11a)

`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-hecke` and `prop:s01-relations`(c), first half
(trivial coefficients).

* `padicUnit ℓ : ℚ_[ℓ]ˣ` the unit `ℓ`; `elemT`, `elemS`, `diamondElt` : the elements of `B̂^×` at which the
  operators are double cosets (`ϖ_ℓ = ι_ℓ⁻¹ diag(ℓ,1)`, the central idele `z_ℓ`, `ι_p⁻¹ diag(1,t)`).
* `diamond` is the local factor at *one* prime `ℓ` of the tex's `⟨d⟩` (`d ∈ (ℤ/Mp^s)^×`); the product over
  `ℓ ∣ Mp` is not assembled. Section `Diamond`: its `hn` at `U_0(N)`, `U_1(N)` (`ℓ ∣ N`), `U_s` (`ℓ = p`),
  `ℓ ∤ N` (`diamondElt_inv_normalizes_*`), `diamond_eq_id_of_mem`, `diamond_apply_eq_diamondAct` (S01-L16b).
* `Tl`, `Sl`, `Ul`, `diamond` : `heckeT U g R _` for these elements (L8a), the finiteness hypothesis
  `[U : U ∩ g U g⁻¹] ≠ 0` being an explicit argument (it holds automatically for `diamond`, `Sl`: see
  `relIndex_ne_zero_of_normalizing`, `relIndex_ne_zero_of_commute`).
* `SplitAt U ℓ` : every `u ∈ U` is a product of an element of `U` commuting with `B_ℓ^×` and an element of
  `U` supported at `ℓ`; it holds at every split prime for all levels of S01-L3c (`splitAt_levelAt_of_notMem`,
  `splitAt_U0`, `splitAt_U1`, `splitAt_Utower`).
* `exists_supported_reps` : for `g` supported at `ℓ`, the cosets of `U g U` have representatives supported at `ℓ`.
* `heckeT_comm_of_reps`, `heckeT_comm_of_disjoint`, `heckeT_comm_localEmbedGL`, `Tl_comm_Tl` : operators supported at
  different primes commute.

Status: *formalized*.
-/

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

variable {a b : ℤ}

/-! ### Cosets of `U g U` -/

section Cosets

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ)

/-- `def:s01-hecke` (`s01-hecke`): the set of left cosets `yU` contained in `U g U`. -/
def dcCosets : Set ((GL2TF.Quat.BHat a b)ˣ ⧸ U) :=
  QuotientGroup.mk '' (dcSet U g)

/-- `def:s01-hecke` (`s01-hecke`): membership in `dcCosets`. -/
theorem mem_dcCosets {c : (GL2TF.Quat.BHat a b)ˣ ⧸ U} :
    c ∈ dcCosets U g ↔ ∃ y ∈ dcSet U g, (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = c :=
  Iff.rfl

/-- `def:s01-hecke` (`s01-hecke`): `dcCosets` is finite when `[U : U ∩ g U g⁻¹] < ∞`. -/
theorem dcCosets_finite (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) : (dcCosets U g).Finite :=
  finite_cosets_dcSet U g hfin

/-- `def:s01-hecke` (`s01-hecke`): if `g` normalizes `U` (in the sense `g⁻¹ U g ⊆ U`), then
`[U : U ∩ g U g⁻¹] = 1 ≠ 0`. -/
theorem relIndex_ne_zero_of_normalizing (hn : ∀ x ∈ U, g⁻¹ * x * g ∈ U) :
    (U ⊓ conjSub U g).relIndex U ≠ 0 := by
  have h : U ⊓ conjSub U g = U := inf_eq_left.2 fun x hx => (mem_conjSub U g).2 (hn x hx)
  rw [h, Subgroup.relIndex_self]
  exact one_ne_zero

/-- `def:s01-hecke` (`s01-hecke`): a central element `g` (commuting with all of `B̂^×`) has
`[U : U ∩ g U g⁻¹] ≠ 0`. -/
theorem relIndex_ne_zero_of_commute (hg : ∀ x : (GL2TF.Quat.BHat a b)ˣ, Commute g x) :
    (U ⊓ conjSub U g).relIndex U ≠ 0 := by
  refine relIndex_ne_zero_of_normalizing U g fun x hx => ?_
  have h : g⁻¹ * x = x * g⁻¹ := (hg x).inv_left.eq
  rw [h, mul_assoc, inv_mul_cancel, mul_one]
  exact hx

end Cosets

/-! ### Representatives supported at one prime -/

section Supported

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `def:s01-hecke` (`s01-hecke`): the level `U` *splits at `ℓ`*: every `u ∈ U` is `c * w` with `c ∈ U` commuting
with the whole local embedding of `B_ℓ^×`, and `w ∈ U` supported at `ℓ`. -/
def SplitAt : Prop :=
  ∀ u ∈ U, ∃ c ∈ U, ∃ w ∈ U, w ∈ (localEmbed a b ℓ).range ∧
    (∀ y ∈ (localEmbed a b ℓ).range, Commute c y) ∧ u = c * w

variable {U ℓ}

/-- `def:s01-hecke` (`s01-hecke`): if `U` splits at `ℓ` and `g` is supported at `ℓ`, then the cosets in `U g U` have
representatives supported at `ℓ` (a finite system `S`, as required by `heckeT_apply_reps`). -/
theorem exists_supported_reps (hsp : SplitAt U ℓ) {g : (GL2TF.Quat.BHat a b)ˣ}
    (hg : g ∈ (localEmbed a b ℓ).range) (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) :
    ∃ S : Finset (GL2TF.Quat.BHat a b)ˣ, (∀ s ∈ S, s ∈ dcSet U g) ∧
      (∀ y ∈ dcSet U g, ∃ s ∈ S,
        (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s) ∧
      Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S ∧
      ∀ s ∈ S, s ∈ (localEmbed a b ℓ).range := by
  classical
  have hT : (dcCosets U g).Finite := dcCosets_finite U g hfin
  have key : ∀ c ∈ dcCosets U g, ∃ s : (GL2TF.Quat.BHat a b)ˣ,
      (s ∈ dcSet U g ∧ s ∈ (localEmbed a b ℓ).range) ∧
        (QuotientGroup.mk s : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = c := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := (mem_dcCosets U g).1 hc
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U g).1 hy
    obtain ⟨c0, hc0, w, hw, hwr, hcomm, rfl⟩ := hsp u hu
    have hwg : w * g ∈ (localEmbed a b ℓ).range := (localEmbed a b ℓ).range.mul_mem hwr hg
    refine ⟨w * g, ⟨(mem_dcSet U g).2 ⟨w, hw, 1, U.one_mem, by rw [mul_one]⟩, hwg⟩, ?_⟩
    rw [QuotientGroup.eq]
    have h1 : c0 * (w * g) = (w * g) * c0 := (hcomm _ hwg).eq
    have e : (w * g)⁻¹ * (c0 * w * g * v) = c0 * v := by
      have h2 : c0 * w * g = w * g * c0 :=
        calc c0 * w * g = c0 * (w * g) := mul_assoc _ _ _
          _ = w * g * c0 := h1
      rw [h2]
      group
    rw [e]
    exact U.mul_mem hc0 hv
  choose! r hr hrc using key
  refine ⟨hT.toFinset.image r, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact (hr c (hT.mem_toFinset.1 hc)).1
  · intro y hy
    have hc : (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) ∈ dcCosets U g := ⟨y, hy, rfl⟩
    exact ⟨r _, Finset.mem_image.2 ⟨_, hT.mem_toFinset.2 hc, rfl⟩, (hrc _ hc).symm⟩
  · intro s1 hs1 s2 hs2 h
    obtain ⟨c1, hc1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs1)
    obtain ⟨c2, hc2, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs2)
    have e1 := hrc c1 (hT.mem_toFinset.1 hc1)
    have e2 := hrc c2 (hT.mem_toFinset.1 hc2)
    have hc : c1 = c2 := e1.symm.trans (h.trans e2)
    rw [hc]
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact (hr c (hT.mem_toFinset.1 hc)).2

end Supported

/-! ### Commutation -/

section Commute

variable (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]

/-- `prop:s01-relations`(c) (`s01-relations`, first half): if the double cosets `U g U`, `U g' U` have systems of
representatives `S`, `S'` (in the sense of `heckeT_apply_reps`) whose elements commute pairwise, then `T_g` and
`T_{g'}` commute. -/
theorem heckeT_comm_of_reps (g g' : (GL2TF.Quat.BHat a b)ˣ)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U ⊓ conjSub U g').relIndex U ≠ 0)
    (S S' : Finset (GL2TF.Quat.BHat a b)ˣ)
    (hS : ∀ s ∈ S, s ∈ dcSet U g)
    (hcov : ∀ y ∈ dcSet U g, ∃ s ∈ S,
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s)
    (hinj : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S)
    (hS' : ∀ s ∈ S', s ∈ dcSet U g')
    (hcov' : ∀ y ∈ dcSet U g', ∃ s ∈ S',
      (QuotientGroup.mk y : (GL2TF.Quat.BHat a b)ˣ ⧸ U) = QuotientGroup.mk s)
    (hinj' : Set.InjOn (QuotientGroup.mk : (GL2TF.Quat.BHat a b)ˣ → (GL2TF.Quat.BHat a b)ˣ ⧸ U) ↑S')
    (hc : ∀ s ∈ S, ∀ s' ∈ S', Commute s s') :
    heckeT U g R hfin ∘ₗ heckeT U g' R hfin' = heckeT U g' R hfin' ∘ₗ heckeT U g R hfin := by
  apply LinearMap.ext
  intro f
  funext c
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits a b) U x = c := ⟨c.out, DoubleCoset.out_eq' c⟩
  simp only [LinearMap.comp_apply]
  have h1 : heckeT U g R hfin (heckeT U g' R hfin' f) (DoubleCoset.mk (globalUnits a b) U x) =
      ∑ s ∈ S, ∑ s' ∈ S', f (DoubleCoset.mk (globalUnits a b) U (x * s * s')) := by
    rw [heckeT_apply_reps U g R hfin S hS hcov hinj]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact heckeT_apply_reps U g' R hfin' S' hS' hcov' hinj' f (x * s)
  have h2 : heckeT U g' R hfin' (heckeT U g R hfin f) (DoubleCoset.mk (globalUnits a b) U x) =
      ∑ s' ∈ S', ∑ s ∈ S, f (DoubleCoset.mk (globalUnits a b) U (x * s' * s)) := by
    rw [heckeT_apply_reps U g' R hfin' S' hS' hcov' hinj']
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact heckeT_apply_reps U g R hfin S hS hcov hinj f (x * s')
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' hs' => Finset.sum_congr rfl fun s hs => ?_
  have e : x * s * s' = x * s' * s := by
    rw [mul_assoc x s s', mul_assoc x s' s, (hc s hs s' hs').eq]
  rw [e]

/-- `prop:s01-relations`(c) (`s01-relations`, first half): Hecke operators `T_g`, `T_{g'}` with `g` supported at `ℓ`,
`g'` supported at `ℓ' ≠ ℓ`, on a level `U` splitting at both `ℓ` and `ℓ'`, commute. -/
theorem heckeT_comm_of_disjoint {ℓ ℓ' : ℕ} [Fact ℓ.Prime] [Fact ℓ'.Prime] (hne : ℓ ≠ ℓ')
    (hU : SplitAt U ℓ) (hU' : SplitAt U ℓ')
    {g g' : (GL2TF.Quat.BHat a b)ˣ} (hg : g ∈ (localEmbed a b ℓ).range)
    (hg' : g' ∈ (localEmbed a b ℓ').range)
    (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) (hfin' : (U ⊓ conjSub U g').relIndex U ≠ 0) :
    heckeT U g R hfin ∘ₗ heckeT U g' R hfin' = heckeT U g' R hfin' ∘ₗ heckeT U g R hfin := by
  obtain ⟨S, hS, hcov, hinj, hsupp⟩ := exists_supported_reps hU hg hfin
  obtain ⟨S', hS', hcov', hinj', hsupp'⟩ := exists_supported_reps hU' hg' hfin'
  refine heckeT_comm_of_reps U R g g' hfin hfin' S S' hS hcov hinj hS' hcov' hinj' ?_
  intro s hs s' hs'
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 (hsupp s hs)
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 (hsupp' s' hs')
  exact localEmbed_comm hne x y

end Commute

/-! ### The split primes: levels of S01-L3c -/

section SplitLevels

variable {d : DefiniteData} {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `def:s01-levels` (`s01-levels`): `localEmbedGL p g` is supported at `p`. -/
theorem localEmbedGL_mem_range (g : GL (Fin 2) ℚ_[p]) :
    localEmbedGL d p hp g ∈ (localEmbed d.a d.b p).range :=
  MonoidHom.mem_range.2 ⟨_, (localEmbedGL_apply g).symm⟩

/-- `def:s01-hecke` (`s01-hecke`): `U` splits at the split prime `p` as soon as the `p`-away part and the `p`-part of
every `u ∈ U` lie in `U`. -/
theorem splitAt_of_mem {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hc : ∀ u ∈ U, awayAt d p hp u ∈ U)
    (hw : ∀ u ∈ U, localEmbedGL d p hp (localComponent d p hp u) ∈ U) : SplitAt U p := by
  intro u hu
  refine ⟨awayAt d p hp u, hc u hu, localEmbedGL d p hp (localComponent d p hp u), hw u hu,
    localEmbedGL_mem_range _, ?_, (awayAt_mul_localEmbedGL u).symm⟩
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
  exact (commute_localEmbed_of_commute x
    (by rw [localProjUnits_awayAt]; exact Commute.one_right _)).symm

/-- `def:s01-hecke` (`s01-hecke`): `U` splits at `p` if it is invariant at `p` and its `p`-components are integral. -/
theorem splitAt_of_isInvariantAt {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hU : IsInvariantAt d p hp U)
    (hloc : ∀ u ∈ U, localComponent d p hp u ∈ Langlandscape.Local.GL2Zl p) : SplitAt U p := by
  have hc : ∀ u ∈ U, awayAt d p hp u ∈ U := fun u hu =>
    hU u hu (localComponent d p hp u)⁻¹ (inv_mem (hloc u hu))
  refine splitAt_of_mem hc fun u hu => ?_
  have h := U.mul_mem (U.inv_mem (hc u hu)) hu
  have e : (awayAt d p hp u)⁻¹ * u = localEmbedGL d p hp (localComponent d p hp u) := by
    rw [inv_mul_eq_iff_eq_mul]
    exact (awayAt_mul_localEmbedGL u).symm
  rwa [e] at h

/-- `def:s01-hecke` (`s01-hecke`): `U` splits at `p` if it has a factorisation at `p` with local condition `K`
(shape of `mem_U1_iff_factor_at` etc.). -/
theorem splitAt_of_factor {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (K : Subgroup (GL (Fin 2) ℚ_[p]))
    (hfac : ∀ u, u ∈ U ↔
      u * localEmbedGL d p hp (localComponent d p hp u)⁻¹ ∈ U ∧ localComponent d p hp u ∈ K) :
    SplitAt U p := by
  refine splitAt_of_mem (fun u hu => ((hfac u).1 hu).1) fun u hu => (hfac _).2 ⟨?_, ?_⟩
  · rw [localComponent_localEmbedGL, map_inv, mul_inv_cancel]
    exact U.one_mem
  · rw [localComponent_localEmbedGL]
    exact ((hfac u).1 hu).2

/-- `def:s01-levels` (`s01-levels`): the generic level splits at every split prime `p ∤ N`. -/
theorem splitAt_levelAt_of_notMem {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hpN : p ∉ N.primeFactors)
    (hp : ¬ p ∣ d.D) :
    SplitAt (d.levelAt N hN K) p :=
  splitAt_of_isInvariantAt (hp := hp) (isInvariantAt_levelAt (hp := hp) hpN) fun _ hu =>
    localComponent_mem_GL2Zl (hℓ := hp) ((DefiniteData.mem_levelAt_iff.1 hu).1)

/-- `def:s01-levels` (`s01-levels`): `U_0(N)` splits at `p ∣ N`. -/
theorem splitAt_U0 {N : ℕ} {hN : N.Coprime d.D}
    (hpN : p ∈ N.primeFactors) (hp : ¬ p ∣ d.D) :
    SplitAt (d.U0 N hN) p :=
  splitAt_of_factor (hp := hp) (Langlandscape.Local.K0 p (N.factorization p))
    fun u => mem_U0_iff_factor_at (hp := hp) hpN u

/-- `def:s01-levels` (`s01-levels`): `U_1(N)` splits at `p ∣ N`. -/
theorem splitAt_U1 {N : ℕ} {hN : N.Coprime d.D}
    (hpN : p ∈ N.primeFactors) (hp : ¬ p ∣ d.D) :
    SplitAt (d.U1 N hN) p :=
  splitAt_of_factor (hp := hp) (Langlandscape.Local.K1 p (N.factorization p))
    fun u => mem_U1_iff_factor_at (hp := hp) hpN u

/-- `def:s01-levels` (`s01-levels`): the tower level `U_s` splits at `p` (`p ∤ M`, `s ≥ 1`). -/
theorem splitAt_Utower {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s)
    (hp : ¬ p ∣ d.D) : SplitAt (d.Utower M p s hN) p :=
  splitAt_of_factor (hp := hp) (Langlandscape.Local.K1 p s)
    fun u => mem_Utower_iff_factor_at (hp := hp) hM hpM hs u

end SplitLevels

/-! ### The named operators -/

section Named

/-- `def:s01-hecke` (`s01-hecke`): the unit `ℓ ∈ ℚ_ℓ^×`. -/
noncomputable def padicUnit (ℓ : ℕ) [Fact ℓ.Prime] : ℚ_[ℓ]ˣ :=
  Units.mk0 (ℓ : ℚ_[ℓ]) (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)

variable (d : DefiniteData) (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hℓ : ¬ ℓ ∣ d.D)

/-- `def:s01-hecke` (`s01-hecke`): `ϖ_ℓ = ι_ℓ⁻¹ diag(ℓ, 1)` as an element of `B̂^×` (supported at `ℓ`);
the element of `T_ℓ` (`ℓ ∤` level) and `U_ℓ` (`ℓ ∣ M`). -/
noncomputable def elemT : (GL2TF.Quat.BHat d.a d.b)ˣ :=
  localEmbedGL d ℓ hℓ (Langlandscape.Local.diagGL (padicUnit ℓ) 1)

/-- `def:s01-hecke` (`s01-hecke`): the central idele `z_ℓ = ι_ℓ⁻¹ diag(ℓ, ℓ)` (`ℓ` at `ℓ`, `1` elsewhere). -/
noncomputable def elemS : (GL2TF.Quat.BHat d.a d.b)ˣ :=
  localEmbedGL d ℓ hℓ (Langlandscape.Local.diagGL (padicUnit ℓ) (padicUnit ℓ))

/-- `def:s01-hecke` (`s01-hecke`): `δ_t = ι_ℓ⁻¹ diag(1, t)` for `t ∈ ℤ_ℓ^×` (placed at the single prime `ℓ`), the
element of the diamond operator `diamond`. An abbreviation of `Quat.deltaElt` (`Quat/Stab.lean`), the only
definition of `δ_t`. -/
noncomputable abbrev diamondElt (t : ℤ_[ℓ]ˣ) : (GL2TF.Quat.BHat d.a d.b)ˣ :=
  deltaElt d ℓ hℓ t

variable (R : Type*) [CommRing R]

/-- `def:s01-hecke` (`s01-hecke`): `T_ℓ = [U ϖ_ℓ U]` on `R^X`.

The side condition `ℓ ∤ DMpq` of the mathematical `T_ℓ` is a *convention, not hypothesis*: the only hypotheses are
`¬ ℓ ∣ d.D` (needed to embed `ϖ_ℓ`) and the finiteness `hfin`. Statements about `Tl` (e.g. `Tl_comm_Tl`) hold for any
primes satisfying their stated hypotheses, whatever the level. -/
noncomputable def Tl (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0) :
    ZXdual U R →ₗ[R] ZXdual U R :=
  heckeT U (elemT d ℓ hℓ) R hfin

/-- `def:s01-hecke` (`s01-hecke`): `S_ℓ = [U z_ℓ U]` on `R^X` (`z_ℓ` the central idele `ℓ` at `ℓ`). -/
noncomputable def Sl (hfin : (U ⊓ conjSub U (elemS d ℓ hℓ)).relIndex U ≠ 0) :
    ZXdual U R →ₗ[R] ZXdual U R :=
  heckeT U (elemS d ℓ hℓ) R hfin

/-- `def:s01-hecke` (`s01-hecke`): `U_ℓ = [U ϖ_ℓ U]` on `R^X` for `ℓ ∣ M` (same element as `T_ℓ`; the name records
that `ℓ` divides the level).

The side condition `ℓ ∣ M` is a *convention, not hypothesis*: it is not assumed anywhere, and `Ul = Tl` by `rfl`
(`Ul_eq_Tl`); the name is only a mnemonic for the case `ℓ ∣ M`. -/
noncomputable def Ul (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0) :
    ZXdual U R →ₗ[R] ZXdual U R :=
  heckeT U (elemT d ℓ hℓ) R hfin

/-- `def:s01-hecke` (`s01-hecke`): the *local factor at one prime `ℓ`* of the diamond operator:
`diamond … ℓ … t = [U δ_t U]` on `R^X`, `δ_t = ι_ℓ⁻¹ diag(1, t)` at `ℓ`, `t ∈ ℤ_ℓ^×`, for `δ_t` normalizing `U`
(`hn : δ_t⁻¹ U δ_t ⊆ U`). The tex's `⟨d⟩`, `d ∈ (ℤ/Mp^s)^×`, has `δ_d` with lower-right entry `≡ d` at *all*
`ℓ ∣ Mp`; it is the product `⟨d⟩ = ∏_{ℓ ∣ Mp} diamond ℓ t_ℓ` (`t_ℓ ∈ ℤ_ℓ^×` lifting `d`), which is **not
assembled** in Lean. `hn` is discharged by `diamondElt_inv_normalizes_U0` (every split `ℓ`),
`diamondElt_inv_normalizes_U1` (`ℓ ∣ N`), `diamondElt_inv_normalizes_Utower` (`ℓ = p`),
`diamondElt_inv_normalizes_levelAt_of_notMem` (`ℓ ∤ N`; there `diamond = id`, `diamond_eq_id_of_mem`). -/
noncomputable def diamond (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U) :
    ZXdual U R →ₗ[R] ZXdual U R :=
  heckeT U (diamondElt d ℓ hℓ t) R (relIndex_ne_zero_of_normalizing U _ hn)

/-- `def:s01-hecke` (`s01-hecke`): `T_ℓ` is `heckeT` of `ϖ_ℓ` (unfolding). -/
theorem Tl_eq_heckeT (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0) :
    Tl d U ℓ hℓ R hfin = heckeT U (elemT d ℓ hℓ) R hfin := rfl

/-- `def:s01-hecke` (`s01-hecke`): `U_ℓ` and `T_ℓ` are given by the same element `ϖ_ℓ`. -/
theorem Ul_eq_Tl (hfin : (U ⊓ conjSub U (elemT d ℓ hℓ)).relIndex U ≠ 0) :
    Ul d U ℓ hℓ R hfin = Tl d U ℓ hℓ R hfin := rfl

/-- `def:s01-hecke` (`s01-hecke`): the diamond operator is a right translation,
`(⟨t⟩ f)[x] = f[x δ_t]` (when `δ_t` also satisfies `δ_t U δ_t⁻¹ ⊆ U`, i.e. `U δ_t U = δ_t U`; here in the form
`hn' : ∀ x ∈ U, δ_t⁻¹ x δ_t ∈ U`, which is all that is needed). -/
theorem diamond_apply (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U)
    (f : ZXdual U R) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    diamond d U ℓ hℓ R t hn f (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      f (DoubleCoset.mk (globalUnits d.a d.b) U (x * diamondElt d ℓ hℓ t)) := by
  set δ := diamondElt d ℓ hℓ t with hδ
  have h := heckeT_apply_reps U δ R (relIndex_ne_zero_of_normalizing U δ hn) {δ}
    (fun s hs => by
      rw [Finset.mem_singleton] at hs
      rw [hs]
      exact (mem_dcSet U δ).2 ⟨1, U.one_mem, 1, U.one_mem, by simp⟩)
    (fun y hy => by
      obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet U δ).1 hy
      refine ⟨δ, Finset.mem_singleton_self _, ?_⟩
      rw [QuotientGroup.eq]
      have e : (u * δ * v)⁻¹ * δ = v⁻¹ * (δ⁻¹ * u⁻¹ * δ) := by group
      rw [e]
      exact U.mul_mem (U.inv_mem hv) (hn _ (U.inv_mem hu)))
    (by rw [Finset.coe_singleton]; exact Set.injOn_singleton _ _) f x
  rw [Finset.sum_singleton] at h
  exact h

end Named

/-! ### The diamond operators at the standard levels (S01-L16b) -/

section Diamond

variable {d : DefiniteData} {ℓ : ℕ} [Fact ℓ.Prime] {hℓ : ¬ ℓ ∣ d.D}

/-- `def:s01-hecke` (`s01-hecke`): the `hn` of `diamond` at `U_0(N)`, for every split `ℓ` (`δ_t ∈ U_0(N)`). -/
theorem diamondElt_inv_normalizes_U0 {N : ℕ} {hN : N.Coprime d.D} (t : ℤ_[ℓ]ˣ) :
    ∀ x ∈ d.U0 N hN, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.U0 N hN :=
  fun _ hx => deltaElt_inv_normalizes_U0 (hp := hℓ) t hx

/-- `def:s01-hecke` (`s01-hecke`): the `hn` of `diamond` at `U_1(N)`, `ℓ ∣ N`. -/
theorem diamondElt_inv_normalizes_U1 {N : ℕ} {hN : N.Coprime d.D} (hℓN : ℓ ∈ N.primeFactors) (t : ℤ_[ℓ]ˣ) :
    ∀ x ∈ d.U1 N hN, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.U1 N hN :=
  fun _ hx => deltaElt_inv_normalizes_U1 (hp := hℓ) hℓN t hx

/-- `def:s01-hecke` (`s01-hecke`): the `hn` of `diamond` at the tower level `U_s = U_1(M ℓ^s)` at `ℓ = p` itself
(`ℓ ∤ M`, `s ≥ 1`). At `ℓ ∣ M` use `diamondElt_inv_normalizes_U1` (`U_s` is `U_1(M ℓ'^s)` by definition). -/
theorem diamondElt_inv_normalizes_Utower {M s : ℕ} {hN : (M * ℓ ^ s).Coprime d.D} (hM : M ≠ 0)
    (hℓM : ¬ ℓ ∣ M) (hs : 1 ≤ s) (t : ℤ_[ℓ]ˣ) :
    ∀ x ∈ d.Utower M ℓ s hN, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.Utower M ℓ s hN :=
  fun _ hx => deltaElt_inv_normalizes (hp := hℓ) hM hℓM hs t hx

/-- `def:s01-hecke` (`s01-hecke`): the `hn` of `diamond` at a generic level `levelAt d N hN K`, `ℓ ∤ N`
(`δ_t ∈ U`). -/
theorem diamondElt_inv_normalizes_levelAt_of_notMem {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hℓN : ℓ ∉ N.primeFactors) (t : ℤ_[ℓ]ˣ) :
    ∀ x ∈ d.levelAt N hN K, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.levelAt N hN K := by
  have hδ : diamondElt d ℓ hℓ t ∈ d.levelAt N hN K := deltaElt_mem_levelAt_of_notMem hℓN t
  exact fun x hx => mul_mem (mul_mem (inv_mem hδ) hx) hδ

variable (R : Type*) [CommRing R]

/-- `def:s01-hecke` (`s01-hecke`): if `δ_t ∈ U`, the diamond operator is the identity (e.g. at `U_0(N)`,
`deltaElt_mem_U0`, at `ℓ ∤ N`, `deltaElt_mem_levelAt_of_notMem`, and at `U_s` for `t ≡ 1 mod ℓ^s`,
`deltaElt_mem_Utower`). -/
theorem diamond_eq_id_of_mem (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ U, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ U) (hδ : diamondElt d ℓ hℓ t ∈ U) :
    diamond d U ℓ hℓ R t hn = LinearMap.id := by
  refine LinearMap.ext fun f => funext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) U x = c := ⟨_, DoubleCoset.out_eq' c⟩
  rw [diamond_apply, LinearMap.id_apply]
  congr 1
  exact DoubleCoset.eq.2 ⟨1, one_mem _, (diamondElt d ℓ hℓ t)⁻¹, inv_mem hδ, by group⟩

/-- `def:s01-hecke`, `lem:s01-stab` (b) (`s01-hecke`): on `U_s` at `ℓ = p`, the diamond operator is the pull-back
along the permutation `Quat.diamondAct t` of `X_B(U_s)`: `(diamond t f) c = f (diamondAct t c)`. -/
theorem diamond_apply_eq_diamondAct {M s : ℕ} {hN : (M * ℓ ^ s).Coprime d.D} (hM : M ≠ 0)
    (hℓM : ¬ ℓ ∣ M) (hs : 1 ≤ s) (t : ℤ_[ℓ]ˣ)
    (hn : ∀ x ∈ d.Utower M ℓ s hN, (diamondElt d ℓ hℓ t)⁻¹ * x * diamondElt d ℓ hℓ t ∈ d.Utower M ℓ s hN)
    (f : ZXdual (d.Utower M ℓ s hN) R) (c : XB (d.Utower M ℓ s hN)) :
    diamond d (d.Utower M ℓ s hN) ℓ hℓ R t hn f c = f (diamondAct (hp := hℓ) hM hℓM hs t c) := by
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M ℓ s hN) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  rw [diamondAct_mk (hp := hℓ) hM hℓM hs t x]
  exact diamond_apply d _ ℓ hℓ R t hn f x

end Diamond

/-! ### Commutation of the named operators -/

section NamedComm

variable {d : DefiniteData} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {hp : ¬ p ∣ d.D} {hq : ¬ q ∣ d.D}
  (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (R : Type*) [CommRing R]

/-- `prop:s01-relations`(c) (`s01-relations`, first half): operators `[U g U]`, `[U g' U]` with `g ∈ GL₂(ℚ_p)`,
`g' ∈ GL₂(ℚ_q)` embedded at different split primes commute, on a level splitting at `p` and `q`
(all levels of S01-L3c; see `splitAt_levelAt_of_notMem`, `splitAt_U0`, `splitAt_U1`, `splitAt_Utower`). -/
theorem heckeT_comm_localEmbedGL (hne : p ≠ q) (hU : SplitAt U p) (hU' : SplitAt U q)
    (g : GL (Fin 2) ℚ_[p]) (g' : GL (Fin 2) ℚ_[q])
    (hfin : (U ⊓ conjSub U (localEmbedGL d p hp g)).relIndex U ≠ 0)
    (hfin' : (U ⊓ conjSub U (localEmbedGL d q hq g')).relIndex U ≠ 0) :
    heckeT U (localEmbedGL d p hp g) R hfin ∘ₗ heckeT U (localEmbedGL d q hq g') R hfin' =
      heckeT U (localEmbedGL d q hq g') R hfin' ∘ₗ heckeT U (localEmbedGL d p hp g) R hfin :=
  heckeT_comm_of_disjoint U R hne hU hU' (localEmbedGL_mem_range g) (localEmbedGL_mem_range g') hfin hfin'

/-- `prop:s01-relations`(c) (`s01-relations`, first half): `T_p` and `T_q` commute for `p ≠ q`. -/
theorem Tl_comm_Tl (hne : p ≠ q) (hU : SplitAt U p) (hU' : SplitAt U q)
    (hfin : (U ⊓ conjSub U (elemT d p hp)).relIndex U ≠ 0)
    (hfin' : (U ⊓ conjSub U (elemT d q hq)).relIndex U ≠ 0) :
    Tl d U p hp R hfin ∘ₗ Tl d U q hq R hfin' = Tl d U q hq R hfin' ∘ₗ Tl d U p hp R hfin :=
  heckeT_comm_localEmbedGL U R hne hU hU' (Langlandscape.Local.diagGL (padicUnit p) 1)
    (Langlandscape.Local.diagGL (padicUnit q) 1) hfin hfin'

end NamedComm

end Langlandscape.Brandt
