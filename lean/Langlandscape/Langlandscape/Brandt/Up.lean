/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.DoubleCoset
import Langlandscape.Quat.LocalEmbed
import Langlandscape.Local.UpCosets

/-!
# The global operator `U_p` in the normalisation `N_{U_p}` (S01-L10)

`plan/staged/stage-01-quaternion-foundations.tex`, `def:s01-NUp`, `lem:s01-Up` (a), (b).

Let `U_s = U_1(M p^s)` (`Utower d M p s`), `s ≥ 1`, `p ∤ M`, `p ∤ D`, and `ϖ = ι_p⁻¹ diag(p, 1)` placed at `p`
(`localEmbedGL d p hp (varpiDiag p)`).

* `Up d M p s … R := heckeT U_s ϖ R _` on `R^X`, `X = X_B(U_s)`; the finiteness `[U_s : U_s ∩ ϖ U_s ϖ⁻¹] < ∞`
  is `Up_relIndex_ne_zero`.
* `Up_apply`: `(U_p f)[x] = ∑_{j < p} f[x ϖ_j]` with `ϖ_j = ι_p⁻¹ !![p, j; 0, 1]`, from the local decomposition
  `K1_mul_varpi_mul_K1` (S01-L9) and the factorisation of `U_s` at `p` (`mem_Utower_iff_factor_at`, S01-L3d).
* `UpHom` : the transpose on `R[X]`, `[x] ↦ ∑_j [x ϖ_j]` (`UpHom_single`).
* `towerMap : X_B(U_{s+1}) → X_B(U_s)` (the projection `π`), `towerPull = π^*`, `towerPush = π_*`.
* `Up_comm_pull` : `U_p ∘ π^* = π^* ∘ U_p`; `Up_comm_push` : `π_* ∘ U_p = U_p ∘ π_*` (`lem:s01-Up`(b)).

The normalisation is the one fixed by `def:s01-NUp` (risk R1); it is the one for which (b) holds.

Status: *formalized*.
-/

open Pointwise
open Langlandscape.Local

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

/-- Auxiliary group identity: if `A⁻¹ (x g), A⁻¹ (y g) ∈ U` then `g⁻¹ (x⁻¹ y) g ∈ U` (`lem:s01-Up`, `s01-Up`). -/
theorem conj_inv_mul_mem_of_inv_mul_mem {G : Type*} [Group G] {U : Subgroup G} {A x y g : G}
    (h1 : A⁻¹ * (x * g) ∈ U) (h2 : A⁻¹ * (y * g) ∈ U) : g⁻¹ * (x⁻¹ * y) * g ∈ U := by
  have h3 := U.mul_mem (U.inv_mem h1) h2
  have e : (A⁻¹ * (x * g))⁻¹ * (A⁻¹ * (y * g)) = g⁻¹ * (x⁻¹ * y) * g := by group
  rwa [e] at h3

section Cosets

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hp : ¬ p ∣ d.D}

/-- `def:s01-levels`/`def:s01-NUp` (`s01-NUp`): `localEmbedGL p (K1 p s) ⊆ U_s` (`p ∤ M`, `s ≥ 1`). -/
theorem localEmbedGL_mem_Utower (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ K1 p s) : localEmbedGL d p hp k ∈ d.Utower M p s hN := by
  rw [mem_Utower_iff_factor_at (hp := hp) hM hpM hs, localComponent_localEmbedGL, map_inv,
    mul_inv_cancel]
  exact ⟨one_mem _, hk⟩

/-- `def:s01-NUp` (`s01-NUp`): each `ϖ_j` (placed at `p`) lies in the double coset `U_s ϖ U_s`. -/
theorem localEmbedGL_varpi_mem_dcSet (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (j : Fin p) :
    localEmbedGL d p hp (varpi p j) ∈
      dcSet (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) := by
  have hj : varpi p j ∈ ⋃ i : Fin p, varpi p i • (K1 p s : Set (GL (Fin 2) ℚ_[p])) :=
    Set.mem_iUnion.2 ⟨j, Set.mem_smul_set.2
      ⟨1, SetLike.mem_coe.2 (one_mem (K1 p s)), by rw [smul_eq_mul, mul_one]⟩⟩
  rw [← K1_mul_varpi_mul_K1 (p := p) hs] at hj
  obtain ⟨z, hz, k', hk', he⟩ := Set.mem_mul.1 hj
  obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.1 hz
  rw [Set.mem_singleton_iff] at hw
  subst hw
  refine (mem_dcSet _ _).2 ⟨localEmbedGL d p hp k,
    localEmbedGL_mem_Utower hM hpM hs (SetLike.mem_coe.1 hk), localEmbedGL d p hp k',
    localEmbedGL_mem_Utower hM hpM hs (SetLike.mem_coe.1 hk'), ?_⟩
  rw [← he, map_mul, map_mul]

/-- `def:s01-NUp`, `lem:s01-Up`(a) (`s01-NUp`): every `y ∈ U_s ϖ U_s` lies in some `ϖ_j U_s`. -/
theorem exists_varpi_inv_mul_mem (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    {y : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hy : y ∈ dcSet (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))) :
    ∃ j : Fin p, (localEmbedGL d p hp (varpi p j))⁻¹ * y ∈ d.Utower M p s hN := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet _ _).1 hy
  have hfac := (mem_Utower_iff_factor_at (hp := hp) hM hpM hs u).1 hu
  have hmem : localComponent d p hp u * varpiDiag p ∈
      (K1 p s : Set (GL (Fin 2) ℚ_[p])) * {varpiDiag p} * K1 p s := by
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.2 hfac.2)
      (Set.mem_singleton (varpiDiag p))) (SetLike.mem_coe.2 (one_mem (K1 p s)))
    rwa [mul_one] at h
  rw [K1_mul_varpi_mul_K1 (p := p) hs] at hmem
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
  obtain ⟨k, hk, hke⟩ := Set.mem_smul_set.1 hj
  rw [smul_eq_mul] at hke
  have hu' : awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u) = u :=
    awayAt_mul_localEmbedGL u
  have e : u * localEmbedGL d p hp (varpiDiag p) =
      localEmbedGL d p hp (varpi p j) * (awayAt d p hp u * localEmbedGL d p hp k) := by
    calc u * localEmbedGL d p hp (varpiDiag p)
        = awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u) *
            localEmbedGL d p hp (varpiDiag p) := by rw [hu']
      _ = awayAt d p hp u * localEmbedGL d p hp (varpi p j * k) := by
            rw [hke, map_mul, mul_assoc]
      _ = localEmbedGL d p hp (varpi p j) * (awayAt d p hp u * localEmbedGL d p hp k) := by
            rw [map_mul, ← mul_assoc (awayAt d p hp u),
              (commute_awayAt_localEmbedGL (hp := hp) u (varpi p j)).eq, mul_assoc]
  refine ⟨j, ?_⟩
  rw [e, mul_assoc, inv_mul_cancel_left]
  exact mul_mem (mul_mem hfac.1
    (localEmbedGL_mem_Utower (hN := hN) hM hpM hs (SetLike.mem_coe.1 hk))) hv

/-- `def:s01-NUp`, `lem:s01-Up`(a) (`s01-NUp`): the cosets `ϖ_j U_s` are pairwise distinct. -/
theorem varpi_cosets_injective (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {j j' : Fin p}
    (h : (QuotientGroup.mk (localEmbedGL d p hp (varpi p j)) :
        (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Utower M p s hN) =
      QuotientGroup.mk (localEmbedGL d p hp (varpi p j'))) : j = j' := by
  by_contra hne
  rw [QuotientGroup.eq, ← map_inv, ← map_mul] at h
  have h2 := ((mem_Utower_iff_factor_at (hp := hp) hM hpM hs _).1 h).2
  rw [localComponent_localEmbedGL] at h2
  exact varpi_inv_mul_not_mem (p := p) (s := s) hne h2

/-- `def:s01-NUp` (`s01-NUp`): `[U_s : U_s ∩ ϖ U_s ϖ⁻¹] < ∞` (it is `p`), so `U_p = [U_s ϖ U_s]` is defined. -/
theorem Up_relIndex_ne_zero (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))).relIndex
      (d.Utower M p s hN) ≠ 0 := by
  have hcov : ∀ u : ↥(d.Utower M p s hN), ∃ j : Fin p,
      (localEmbedGL d p hp (varpi p j))⁻¹ *
        ((u : (GL2TF.Quat.BHat d.a d.b)ˣ) * localEmbedGL d p hp (varpiDiag p)) ∈ d.Utower M p s hN :=
    fun u => exists_varpi_inv_mul_mem hM hpM hs
      ((mem_dcSet _ _).2 ⟨u, u.2, 1, one_mem _, by rw [mul_one]⟩)
  choose F hF using hcov
  have hfin : Finite (↥(d.Utower M p s hN) ⧸
      (d.Utower M p s hN ⊓ conjSub (d.Utower M p s hN)
        (localEmbedGL d p hp (varpiDiag p))).subgroupOf (d.Utower M p s hN)) := by
    refine Finite.of_injective (β := Fin p) (fun q => F (Quotient.out q)) ?_
    intro q q' hqq'
    have hqq'' : F (Quotient.out q) = F (Quotient.out q') := hqq'
    have h1 := hF (Quotient.out q)
    have h2 := hF (Quotient.out q')
    rw [hqq''] at h1
    have h3 := conj_inv_mul_mem_of_inv_mul_mem h1 h2
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (Quotient.out q).2) (Quotient.out q').2, ?_⟩
    exact (mem_conjSub _ _).2 h3
  exact Subgroup.index_ne_zero_of_finite (hH := hfin)

end Cosets

section Operator

/-- `def:s01-NUp`, `def:s01-hecke`: the operator `U_p = [U_s ϖ U_s]` on `R^X`, `X = X_B(U_s)`,
`U_s = U_1(M p^s)`, with `ϖ = ι_p⁻¹ diag(p, 1)` at `p` (normalisation `N_{U_p}`); `s ≥ 1`, `p ∤ M`. -/
noncomputable def Up (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R] :
    ZXdual (d.Utower M p s hN) R →ₗ[R] ZXdual (d.Utower M p s hN) R :=
  heckeT (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) R (Up_relIndex_ne_zero hM hpM hs)

/-- `def:s01-NUp`: the transpose `U_p` on `R[X]` (for finite `X`), `[x] ↦ ∑_j [x ϖ_j]`. -/
noncomputable def UpHom (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D)
    (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R]
    [Finite (XB (d.Utower M p s hN))] :
    ZX (d.Utower M p s hN) R →ₗ[R] ZX (d.Utower M p s hN) R :=
  heckeTHom (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) R (Up_relIndex_ne_zero hM hpM hs)

variable {R : Type*} [CommRing R]
variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D}
  {hp : ¬ p ∣ d.D}

/-- `def:s01-NUp`, `lem:s01-Up`(a) (`s01-NUp`): `(U_p f)[x] = ∑_{j < p} f[x ϖ_j]`,
`ϖ_j = ι_p⁻¹ !![p, j; 0, 1]` at `p`. -/
theorem Up_apply (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (f : ZXdual (d.Utower M p s hN) R)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    Up d M p s hN hp hM hpM hs R f (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) =
      ∑ j : Fin p, f (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN)
        (x * localEmbedGL d p hp (varpi p j))) := by
  have hS : ∀ y ∈ Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j)),
      y ∈ dcSet (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact localEmbedGL_varpi_mem_dcSet hM hpM hs j
  have hcov : ∀ y ∈ dcSet (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)),
      ∃ t ∈ Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j)),
        (QuotientGroup.mk y : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Utower M p s hN) = QuotientGroup.mk t := by
    intro y hy
    obtain ⟨j, hj⟩ := exists_varpi_inv_mul_mem hM hpM hs hy
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ j), (QuotientGroup.eq.2 hj).symm⟩
  have hinj : Set.InjOn
      (QuotientGroup.mk : (GL2TF.Quat.BHat d.a d.b)ˣ → (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Utower M p s hN)
      ↑(Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j))) := by
    intro y hy y' hy' hyy'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy')
    rw [varpi_cosets_injective hM hpM hs hyy']
  have hinj' : Set.InjOn (fun j : Fin p => localEmbedGL d p hp (varpi p j)) ↑(Finset.univ : Finset (Fin p)) :=
    fun j _ j' _ hjj' => varpi_cosets_injective (hN := hN) hM hpM hs
      (congrArg (fun z => (QuotientGroup.mk z : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Utower M p s hN)) hjj')
  rw [Up, heckeT_apply_reps _ _ R _ _ hS hcov hinj f x]
  exact Finset.sum_image hinj'

/-- `def:s01-NUp` (`s01-NUp`): `U_p [x] = ∑_{j < p} [x ϖ_j]` on `R[X]`. -/
theorem UpHom_single [Finite (XB (d.Utower M p s hN))] (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) (r : R) :
    UpHom d M p s hN hp hM hpM hs R
        (Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) r) =
      ∑ j : Fin p, Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN)
        (x * localEmbedGL d p hp (varpi p j))) r := by
  ext c'
  have h := heckeTHom_single_apply (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) R
    (Up_relIndex_ne_zero hM hpM hs) (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) c' r
  have h2 : heckeT (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p)) R
      (Up_relIndex_ne_zero hM hpM hs) (Pi.single c' (1 : R))
        (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) =
      ∑ j : Fin p, (Pi.single c' (1 : R) : ZXdual (d.Utower M p s hN) R)
        (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN)
          (x * localEmbedGL d p hp (varpi p j))) :=
    Up_apply (d := d) (M := M) (p := p) (s := s) (hN := hN) (hp := hp) (R := R) hM hpM hs
      (Pi.single c' (1 : R)) x
  rw [UpHom, h, h2, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN)
      (x * localEmbedGL d p hp (varpi p j)) = c'
  · simp [hc]
  · simp [hc]

end Operator

section Tower

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime]

/-- `def:s01-levels` (`s01-levels`): `U_{s+1} ≤ U_s`. -/
theorem Utower_succ_le (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (hM : M ≠ 0) : d.Utower M p (s + 1) hN' ≤ d.Utower M p s hN :=
  DefiniteData.Utower_antitone (d := d) (Nat.le_succ s) hM (Fact.out : p.Prime).ne_zero hN hN'

variable (d M p s) in
/-- `lem:s01-Up`: the projection `π = π_{s+1,s} : X_B(U_{s+1}) → X_B(U_s)`, `[x] ↦ [x]`. -/
noncomputable def towerMap (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D) :
    XB (d.Utower M p (s + 1) hN') → XB (d.Utower M p s hN) :=
  fun c => DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) (Quotient.out c)

/-- `lem:s01-Up` (`s01-Up`): `π [x] = [x]`. -/
theorem towerMap_mk {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D}
    (hM : M ≠ 0) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    towerMap d M p s hN hN' (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x := by
  obtain ⟨g, hg, k, hk, he⟩ :=
    DoubleCoset.mk_out_eq_mul (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x
  show DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN)
      (Quotient.out (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x)) = _
  rw [he, DoubleCoset.eq]
  exact ⟨g⁻¹, (globalUnits d.a d.b).inv_mem hg, k⁻¹,
    (d.Utower M p s hN).inv_mem (Utower_succ_le hN hN' hM hk), by group⟩

variable (d M p s) in
/-- `lem:s01-Up`(b): the pullback `π^* : R^{X(U_s)} → R^{X(U_{s+1})}`, `f ↦ f ∘ π`. -/
noncomputable def towerPull (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (R : Type*) [CommRing R] :
    ZXdual (d.Utower M p s hN) R →ₗ[R] ZXdual (d.Utower M p (s + 1) hN') R :=
  LinearMap.funLeft R R (towerMap d M p s hN hN')

variable (d M p s) in
/-- `lem:s01-Up`(b): the pushforward `π_* : R[X(U_{s+1})] → R[X(U_s)]`, `[x] ↦ [π x]`. -/
noncomputable def towerPush (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (R : Type*) [CommRing R] :
    ZX (d.Utower M p (s + 1) hN') R →ₗ[R] ZX (d.Utower M p s hN) R :=
  Finsupp.lmapDomain R R (towerMap d M p s hN hN')

variable {R : Type*} [CommRing R]

omit [Fact (Nat.Prime p)] in
/-- `lem:s01-Up`(b) (`s01-Up`): `(π^* f)(c) = f(π c)`. -/
theorem towerPull_apply {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D}
    (f : ZXdual (d.Utower M p s hN) R) (c : XB (d.Utower M p (s + 1) hN')) :
    towerPull d M p s hN hN' R f c = f (towerMap d M p s hN hN' c) :=
  rfl

omit [Fact (Nat.Prime p)] in
/-- `lem:s01-Up`(b) (`s01-Up`): `π_* (r [c]) = r [π c]`. -/
theorem towerPush_single {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D}
    (c : XB (d.Utower M p (s + 1) hN')) (r : R) :
    towerPush d M p s hN hN' R (Finsupp.single c r) = Finsupp.single (towerMap d M p s hN hN' c) r := by
  rw [towerPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D} {hp : ¬ p ∣ d.D}

/-- `lem:s01-Up`(b) (`s01-Up`): `U_p ∘ π^* = π^* ∘ U_p` on `R^{X(U_s)} → R^{X(U_{s+1})}`, `s ≥ 1`
(normalisation `N_{U_p}`; the same `ϖ_j` represent both levels). -/
theorem Up_comm_pull (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Up d M p (s + 1) hN' hp hM hpM (Nat.le_add_left 1 s) R ∘ₗ towerPull d M p s hN hN' R =
      towerPull d M p s hN hN' R ∘ₗ Up d M p s hN hp hM hpM hs R := by
  apply LinearMap.ext
  intro f
  funext c
  rw [← DoubleCoset.out_eq' c]
  simp only [LinearMap.comp_apply, Up_apply, towerPull_apply, towerMap_mk hM]

/-- `lem:s01-Up`(b) (`s01-Up`): `π_* ∘ U_p = U_p ∘ π_*` on `R[X(U_{s+1})] → R[X(U_s)]`, `s ≥ 1`
(normalisation `N_{U_p}`). -/
theorem Up_comm_push [Finite (XB (d.Utower M p s hN))] [Finite (XB (d.Utower M p (s + 1) hN'))]
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    towerPush d M p s hN hN' R ∘ₗ UpHom d M p (s + 1) hN' hp hM hpM (Nat.le_add_left 1 s) R =
      UpHom d M p s hN hp hM hpM hs R ∘ₗ towerPush d M p s hN hN' R := by
  apply Finsupp.lhom_ext
  intro c r
  rw [← DoubleCoset.out_eq' c]
  simp only [LinearMap.comp_apply, UpHom_single, map_sum, towerPush_single, towerMap_mk hM]

end Tower

end Langlandscape.Brandt
