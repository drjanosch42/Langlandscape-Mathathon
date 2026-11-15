/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LevelFinite
import Langlandscape.Quat.LevelNrd

/-!
# q-levels, `Γ_U`, the norm-one class set and `SA_U` (S02-L4a)

`plan/staged/stage-02-tree-quotients.tex`: `def:s02-GU`, `def:s02-Xone`, `thm:s02-SA` (the shape (SA_U)),
`lem:s02-normone`. Statement layer only; the theorems about these objects are in `Tree/NormOne.lean`,
`Tree/QuotientCore.lean` and `Tree/Quotient.lean`.

Fix a prime `q ∤ D` (`hq : ¬ q ∣ d.D`) and write `lc = localComponent d q hq : B̂^× → GL₂(ℚ_q)` for `u ↦ ι_q(u_q)`.

* `coprime_of_not_dvd hq : q.Coprime d.D` (to feed the stage-01 API, e.g. `d.U0q q _ U`).
* `HasFactorAt d q hq K U` : `U = V ⊓ lc⁻¹(K)` with `V` invariant at `q` (`IsInvariantAt`), i.e. `U = K × U^{(q)}`.
* `IsQLevel d q hq U` : `U ≤ Ô^×`, `[Ô^× : U] < ∞`, and `HasFactorAt d q hq GL₂(ℤ_q) U`.
* `IsQAdmissible d q hq U` : `IsQLevel` and `Nrd(U) = Ẑ^×` (`Quat.NrdSurj`, S02-L10, gives `Ẑ^× ⊆ Nrd(U)`; the
  inclusion `Nrd(U) ⊆ Ẑ^×` comes from `U ≤ Ô^×`, part of `IsQLevel`).
* `det_localComponent_finEmbed` : `det ι_q(γ) = nrd γ` for `γ ∈ B^×` (from the import's `splitting_norm_trace`).
* `BHatOne d = B̂^1 = ker(nrd : B̂^× → 𝔸_f^×)`; `GammaU d q hq U = Γ_U`; `XBone d U = B^1 \ B̂^1 / U^1`,
  `XBone.toXB d U : X^1(U) → X_B(U)`.
* `SAat d q hq U` : the statement (SA_U) `B̂^1 = B^1 (B^1_q × U^{1,(q)})` for one level.

## Faithfulness (audit notes)

* **`IsQLevel` vs "compact open, `U = U_q × U^{(q)}` with `U_q = ι_q^{-1} GL₂(ℤ_q)`".** The product condition is
  `HasFactorAt d q hq (GL2Zl q) U`: `u ∈ U ↔ u ∈ V ∧ u_q ∈ GL₂(ℤ_q)` with `V · ι_q(GL₂(ℤ_q)) ⊆ V`; by
  `mem_U_iff_factor_at` and `localEmbedGL_mem_inf_comap` this says exactly `U = ι_q^{-1}GL₂(ℤ_q) × U^{(q)}`.
  "Compact open" is replaced by `U ≤ Ô^×` and `[Ô^× : U] < ∞` (A18). An open subgroup of the compact group `Ô^×` has
  finite index, so every tex level is a `IsQLevel`; the converse fails in general, so the Lean notion is *weaker*,
  and every theorem with hypothesis `IsQLevel` is at least as general as its tex version. **Binding note:** consumers
  of `IsQLevel` may use only `U ≤ Ô^×`, `[Ô^× : U] < ∞` and `HasFactorAt`, never `IsOpen U`. The only place where the
  weaker notion strengthens a statement is the antecedent of `Hyp.SA`. There the condition (SA_U) only involves
  `U^1 = U ∩ B̂^1`, and `[Ô^1 : U^1] ≤ [Ô^× : U] < ∞`; `HasFactorAt` gives `U^1 = U^1_q × {u ∈ U^1 : u_q = 1}`.
  Now `Ô^1 ≅ SL₂(Ẑ^{(D)}) × ∏_{ℓ ∣ D} 𝒪_ℓ^1`; the first factor is topologically finitely generated since
  `SL₂(ℤ) ↠ SL₂(ℤ/N)` for every `N`, and the others are finitely many compact `ℓ`-adic analytic groups, so `Ô^1` is
  topologically finitely generated. By Nikolov–Segal (Ann. of Math. 165 (2007), Thm. 1.1) every finite-index subgroup
  of `Ô^1` is open, so `U^1` is open in `Ô^1`. What the proof of (SA_U) uses is that
  `U^{1,(q)} = {u ∈ U^1 : u_q = 1}` is open in `B̂^{1,(q)}`: `U^{1,(q)} = U^1 ∩ Ô^{1,(q)}` is open in the closed
  subgroup `Ô^{1,(q)} = {u ∈ Ô^1 : u_q = 1}` of `Ô^1`, and `Ô^{1,(q)}` is open in `B̂^{1,(q)}`. Hence `Hyp.SA` with the
  weaker antecedent is still a consequence of `thm:s02-SA` (*cited*, not formalized); its truth then also rests on
  Nikolov–Segal (which uses the classification of finite simple groups). For the levels of the project (`Ô^×`,
  `U_0(N)`, `U_1(N)`, `U_s`) the question does not arise: they are open.
* **Admissibility of the standard levels needs `Hyp.RamNrdSurj`.** `isQAdmissible_Ohat`, `isQAdmissible_U0`,
  `isQAdmissible_U1`, `isQAdmissible_Utower` take `Hyp.RamNrdSurj d` (through `Quat.nrdSurj_*`). Every definite `B`
  has `D > 1` (an odd number of ramified finite primes, product formula; not proved in Lean), so this hypothesis is
  needed for every `DefiniteData`; it has no instance. Consumers of these levels that also take `Hyp.SA`, `Hyp.HS`
  therefore depend on `Hyp.RamNrdSurj` as well.
* **`GammaU`.** `γ ∈ Γ_U ↔ nrd γ = 1 ∧ awayAt q (ι(γ)) ∈ U`. `awayAt q (ι γ)` has `q`-component `1` and components
  `γ_ℓ` at `ℓ ≠ q`; for `U = U_q × U^{(q)}` its membership in `U` is `γ^{(q)} ∈ U^{(q)}`, i.e. `γ_ℓ ∈ U_ℓ` for
  `ℓ ≠ q`. This is the tex's `Γ_U = B^1 ∩ (B^1_q × U^{(q)})`.
* **`SAat`.** `y = ι(β) · localEmbedGL q g · u` with `nrd β = 1` (`β ∈ B^1`), `det g = 1` (`g ∈ B^1_q ≅ SL₂(ℚ_q)`),
  `u ∈ U ∩ B̂^1` with `u_q = 1` (`u ∈ U^{1,(q)}`). This is (SA_U) of `thm:s02-SA`, quantified over `y ∈ B̂^1`.

Status: definitions and the lemmas below *formalized*; `isQAdmissible_*` *formalized* modulo `Hyp.RamNrdSurj d`.
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat Langlandscape.Local
open GL2TF.Quat (nrd)

section Basic

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime]

/-- `def:s02-GU` (`s02-GU`): a prime `q ∤ D` is coprime to `D`. -/
theorem coprime_of_not_dvd (hq : ¬ q ∣ d.D) : q.Coprime d.D :=
  (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hq

end Basic

/-! ### q-levels -/

section Levels

/-- `def:s02-GU`: `U` has the factor `K` at `q`, i.e. `U = V ⊓ lc⁻¹(K)` with `V` invariant at `q`
(`V · ι_q(GL₂(ℤ_q)) ⊆ V`); for `K ≤ GL₂(ℤ_q)` this is `U = ι_q^{-1}(K) × U^{(q)}`. -/
def HasFactorAt (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (K : Subgroup (GL (Fin 2) ℚ_[q]))
    (U : Subgroup (BHat d.a d.b)ˣ) : Prop :=
  ∃ V : Subgroup (BHat d.a d.b)ˣ, IsInvariantAt d q hq V ∧ U = V ⊓ K.comap (localComponent d q hq)

/-- `def:s02-GU`: `U` is a `q`-level: `U ≤ Ô^×` of finite index (the Lean form of "compact open", A18; see the module
docstring) with `U = ι_q^{-1}GL₂(ℤ_q) × U^{(q)}`. -/
def IsQLevel (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) : Prop :=
  U ≤ d.Ohat ∧ U.relIndex d.Ohat ≠ 0 ∧ HasFactorAt d q hq (GL2Zl q) U

/-- `def:s02-GU`: `U` is `q`-admissible: a `q`-level with `Nrd(U) = Ẑ^×` (`Quat.NrdSurj` gives `Ẑ^× ⊆ Nrd(U)`; the
reverse inclusion holds because `U ≤ Ô^×` by `IsQLevel`). -/
def IsQAdmissible (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) :
    Prop :=
  IsQLevel d q hq U ∧ Quat.NrdSurj d U

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}

/-- `def:s02-GU` (`s02-GU`): a subgroup `U ≤ Ô^×` invariant at `q` has the factor `GL₂(ℤ_q)` at `q`. -/
theorem hasFactorAt_GL2Zl_of_invariant {U : Subgroup (BHat d.a d.b)ˣ} (hU : IsInvariantAt d q hq U)
    (hle : U ≤ d.Ohat) : HasFactorAt d q hq (GL2Zl q) U :=
  ⟨U, hU, (inf_eq_left.2 (hle.trans (Ohat_le_comap_GL2Zl (d := d) (ℓ := q) (hℓ := hq)))).symm⟩

/-- `def:s02-GU` (`s02-GU`): `Ô^×` is a `q`-level. -/
theorem isQLevel_Ohat : IsQLevel d q hq d.Ohat := by
  refine ⟨le_rfl, ?_, hasFactorAt_GL2Zl_of_invariant isInvariantAt_Ohat le_rfl⟩
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

omit [Fact q.Prime] in
/-- `def:s02-GU` (`s02-GU`): `q ∤ N` means `q` is not a prime factor of `N`. -/
private theorem not_mem_primeFactors_of_not_dvd {N : ℕ} (hqN : ¬ q ∣ N) : q ∉ N.primeFactors :=
  fun h => hqN (Nat.dvd_of_mem_primeFactors h)

/-- `def:s02-GU` (`s02-GU`): `U_0(N)` is a `q`-level for `q ∤ N`. -/
theorem isQLevel_U0 {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) : IsQLevel d q hq (d.U0 N hN) := by
  have hN0 : N ≠ 0 := fun h => hqN (h ▸ dvd_zero q)
  have : NeZero N := ⟨hN0⟩
  refine ⟨DefiniteData.U0_le_units N hN, d.relIndex_U0_ne_zero N hN, ?_⟩
  exact hasFactorAt_GL2Zl_of_invariant
    (isInvariantAt_levelAt (K := fun ℓ _ e => K0 ℓ e) (not_mem_primeFactors_of_not_dvd hqN))
    (DefiniteData.U0_le_units N hN)

/-- `def:s02-GU` (`s02-GU`): `U_1(N)` is a `q`-level for `q ∤ N`. -/
theorem isQLevel_U1 {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) : IsQLevel d q hq (d.U1 N hN) := by
  have hN0 : N ≠ 0 := fun h => hqN (h ▸ dvd_zero q)
  have : NeZero N := ⟨hN0⟩
  refine ⟨DefiniteData.U1_le_units N hN, d.relIndex_U1_ne_zero N hN, ?_⟩
  exact hasFactorAt_GL2Zl_of_invariant
    (isInvariantAt_levelAt (K := fun ℓ _ e => K1 ℓ e) (not_mem_primeFactors_of_not_dvd hqN))
    (DefiniteData.U1_le_units N hN)

/-- `def:s02-GU` (`s02-GU`): the tower level `U_s = U_1(M p^s)` is a `q`-level for `q ∤ M p^s` (N3). -/
theorem isQLevel_Utower {M p s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hqN : ¬ q ∣ M * p ^ s) :
    IsQLevel d q hq (d.Utower M p s hN) :=
  isQLevel_U1 (N := M * p ^ s) hqN

/-- `def:s02-GU` (`s02-GU`; "the standard levels are `q`-admissible"): `Ô^×` is `q`-admissible, modulo
`Hyp.RamNrdSurj d` (needed for every definite `B`, since `D > 1`; see the module docstring). -/
theorem isQAdmissible_Ohat (hram : Langlandscape.Hyp.RamNrdSurj d) : IsQAdmissible d q hq d.Ohat :=
  ⟨isQLevel_Ohat, nrdSurj_Ohat hram⟩

/-- `def:s02-GU` (`s02-GU`): `U_0(N)` is `q`-admissible for `q ∤ N`, modulo `Hyp.RamNrdSurj d` (needed for every
definite `B`, since `D > 1`). -/
theorem isQAdmissible_U0 (hram : Langlandscape.Hyp.RamNrdSurj d) {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) :
    IsQAdmissible d q hq (d.U0 N hN) :=
  ⟨isQLevel_U0 hqN, nrdSurj_U0 hram N hN⟩

/-- `def:s02-GU` (`s02-GU`): `U_1(N)` is `q`-admissible for `q ∤ N`, modulo `Hyp.RamNrdSurj d` (needed for every
definite `B`, since `D > 1`). -/
theorem isQAdmissible_U1 (hram : Langlandscape.Hyp.RamNrdSurj d) {N : ℕ} {hN : N.Coprime d.D} (hqN : ¬ q ∣ N) :
    IsQAdmissible d q hq (d.U1 N hN) :=
  ⟨isQLevel_U1 hqN, nrdSurj_U1 hram N hN⟩

/-- `def:s02-GU` (`s02-GU`): the tower level `U_s = U_1(M p^s)` is `q`-admissible for `q ∤ M p^s` (N3), modulo
`Hyp.RamNrdSurj d` (needed for every definite `B`, since `D > 1`). -/
theorem isQAdmissible_Utower (hram : Langlandscape.Hyp.RamNrdSurj d) {M p s : ℕ} {hN : (M * p ^ s).Coprime d.D}
    (hqN : ¬ q ∣ M * p ^ s) : IsQAdmissible d q hq (d.Utower M p s hN) :=
  ⟨isQLevel_Utower hqN, nrdSurj_Utower hram M p s hN⟩

/-- `def:s02-GU` (`s02-GU`): for a `q`-level `U`, the edge level `U_0(q)U = U ∩ U_0(q)` has the factor `Iw_q` at
`q`: `U_0(q)U = ι_q^{-1}(Iw_q) × U^{(q)}`. -/
theorem hasFactorAt_U0q {U : Subgroup (BHat d.a d.b)ˣ} (hU : IsQLevel d q hq U) :
    HasFactorAt d q hq (Iw q) (d.U0q q (coprime_of_not_dvd hq) U) := by
  obtain ⟨hle, -, V, hV, rfl⟩ := hU
  refine ⟨V, hV, ?_⟩
  have hqp : q.Prime := Fact.out
  ext u
  rw [DefiniteData.mem_U0q_iff, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_comap]
  constructor
  · rintro ⟨⟨huV, -⟩, hu0⟩
    refine ⟨huV, ?_⟩
    have h0 := (DefiniteData.mem_U0_iff.1 hu0).2 q (hqp.mem_primeFactors dvd_rfl hqp.ne_zero) hq
    rw [Nat.Prime.factorization_self hqp] at h0
    exact h0
  · rintro ⟨huV, huI⟩
    have huU : u ∈ V ⊓ (GL2Zl q).comap (localComponent d q hq) :=
      Subgroup.mem_inf.2 ⟨huV, Subgroup.mem_comap.2 (K0_le_GL2Zl 1 huI)⟩
    refine ⟨Subgroup.mem_inf.1 huU, DefiniteData.mem_U0_iff.2 ⟨hle huU, fun ℓ _ hℓ hD => ?_⟩⟩
    have hℓq : ℓ = q := by
      rw [Nat.Prime.primeFactors hqp] at hℓ
      exact Finset.mem_singleton.1 hℓ
    subst hℓq
    rw [Nat.Prime.factorization_self hqp]
    exact huI

end Levels

/-! ### `det ∘ ι_q = nrd` on `B^×` -/

section Det

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}

/-- `def:s02-GU` (`s02-GU`; A8): for `γ ∈ B^×`, `det ι_q(γ) = nrd γ` in `ℚ_q`. From the import's
`splitting_norm_trace` applied to the splitting `ellAdicSplitting` (= `ι_q ∘ (B → B_q)`). -/
theorem det_localComponent_finEmbed (γ : (QuatAlg ℚ d.a d.b)ˣ) :
    ((Matrix.GeneralLinearGroup.det (localComponent d q hq (iotaU d.a d.b γ)) : ℚ_[q]ˣ) : ℚ_[q]) =
      ((nrd (γ : QuatAlg ℚ d.a d.b) : ℚ) : ℚ_[q]) := by
  have h := localComponent_finEmbed_eq_ellAdicSplitting (d := d) (ℓ := q) (hℓ := hq) γ
  exact (congrArg Matrix.det h).trans ((GL2TF.Quat.splitting_norm_trace d.ha.ne d.hb.ne _).1 _)

end Det

/-! ### The away-from-`q` part is multiplicative -/

section Away

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D}

/-- `def:s02-GU` (`s02-GU`): `awayAt q 1 = 1`. -/
theorem awayAt_one : awayAt d q hq 1 = 1 := by
  simp only [awayAt, map_one, inv_one, one_mul]

/-- `def:s02-GU` (`s02-GU`): `awayAt q` is multiplicative (the `q`-component of `awayAt q y` is `1`, so it commutes
with `localEmbedGL q`). -/
theorem awayAt_mul (x y : (BHat d.a d.b)ˣ) :
    awayAt d q hq (x * y) = awayAt d q hq x * awayAt d q hq y := by
  have hc : Commute (awayAt d q hq y) (localEmbedGL d q hq (localComponent d q hq x)⁻¹) :=
    commute_awayAt_localEmbedGL y _
  calc awayAt d q hq (x * y)
      = x * (y * localEmbedGL d q hq (localComponent d q hq y)⁻¹) *
          localEmbedGL d q hq (localComponent d q hq x)⁻¹ := by
        simp only [awayAt, map_mul, mul_inv_rev, mul_assoc]
    _ = x * (awayAt d q hq y * localEmbedGL d q hq (localComponent d q hq x)⁻¹) := mul_assoc _ _ _
    _ = x * (localEmbedGL d q hq (localComponent d q hq x)⁻¹ * awayAt d q hq y) := by rw [hc.eq]
    _ = awayAt d q hq x * awayAt d q hq y := (mul_assoc _ _ _).symm

/-- `def:s02-GU` (`s02-GU`): `awayAt q u⁻¹ = (awayAt q u)⁻¹`. -/
theorem awayAt_inv (x : (BHat d.a d.b)ˣ) : awayAt d q hq x⁻¹ = (awayAt d q hq x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← awayAt_mul, inv_mul_cancel, awayAt_one])

end Away

/-! ### `Γ_U` -/

section Gamma

/-- `def:s02-GU`: `Γ_U = B^1 ∩ (B^1_q × U^{(q)}) = {γ ∈ B^× : nrd γ = 1, γ_ℓ ∈ U_ℓ (ℓ ≠ q)}`, as a subgroup of
`B^×`, for `U` with `HasFactorAt d q hq (GL2Zl q) U` (e.g. `IsQLevel`); the condition away from `q` is
`awayAt q (ι γ) ∈ U` (see the module docstring). -/
noncomputable def GammaU (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) : Subgroup (QuatAlg ℚ d.a d.b)ˣ where
  carrier := {γ | nrd (γ : QuatAlg ℚ d.a d.b) = 1 ∧ awayAt d q hq (iotaU d.a d.b γ) ∈ U}
  one_mem' := by
    show nrd ((1 : (QuatAlg ℚ d.a d.b)ˣ) : QuatAlg ℚ d.a d.b) = 1 ∧
      awayAt d q hq (iotaU d.a d.b 1) ∈ U
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact GL2TF.Quat.nrdHom_one_aux
    · rw [map_one, awayAt_one]
      exact U.one_mem
  mul_mem' := by
    intro γ δ hγ hδ
    obtain ⟨hγ1, hγ2⟩ := hγ
    obtain ⟨hδ1, hδ2⟩ := hδ
    show nrd ((γ * δ : (QuatAlg ℚ d.a d.b)ˣ) : QuatAlg ℚ d.a d.b) = 1 ∧
      awayAt d q hq (iotaU d.a d.b (γ * δ)) ∈ U
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, GL2TF.Quat.nrdHom_mul_aux, hγ1, hδ1, one_mul]
    · rw [map_mul, awayAt_mul]
      exact U.mul_mem hγ2 hδ2
  inv_mem' := by
    intro γ hγ
    obtain ⟨hγ1, hγ2⟩ := hγ
    show nrd ((γ⁻¹ : (QuatAlg ℚ d.a d.b)ˣ) : QuatAlg ℚ d.a d.b) = 1 ∧
      awayAt d q hq (iotaU d.a d.b γ⁻¹) ∈ U
    refine ⟨?_, ?_⟩
    · have h := GL2TF.Quat.nrdHom_mul_aux ((γ⁻¹ : (QuatAlg ℚ d.a d.b)ˣ) : QuatAlg ℚ d.a d.b)
        (γ : QuatAlg ℚ d.a d.b)
      rw [Units.inv_mul, GL2TF.Quat.nrdHom_one_aux, hγ1, mul_one] at h
      exact h.symm
    · rw [map_inv, awayAt_inv]
      exact U.inv_mem hγ2

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-GU` (`s02-GU`): membership in `Γ_U`. -/
theorem mem_GammaU_iff {γ : (QuatAlg ℚ d.a d.b)ˣ} :
    γ ∈ GammaU d q hq U ↔ nrd (γ : QuatAlg ℚ d.a d.b) = 1 ∧ awayAt d q hq (iotaU d.a d.b γ) ∈ U :=
  Iff.rfl

/-- `def:s02-GU` (`s02-GU`): elements of `Γ_U` have reduced norm `1`. -/
theorem nrd_eq_one_of_mem_GammaU {γ : (QuatAlg ℚ d.a d.b)ˣ} (h : γ ∈ GammaU d q hq U) :
    nrd (γ : QuatAlg ℚ d.a d.b) = 1 :=
  (mem_GammaU_iff.1 h).1

/-- `def:s02-GU` (`s02-GU`): for `γ ∈ Γ_U`, the `q`-away part of `ι(γ)` lies in `U`. -/
theorem awayAt_mem_of_mem_GammaU {γ : (QuatAlg ℚ d.a d.b)ˣ} (h : γ ∈ GammaU d q hq U) :
    awayAt d q hq (iotaU d.a d.b γ) ∈ U :=
  (mem_GammaU_iff.1 h).2

/-- `def:s02-GU` (`s02-GU`): `Γ_U` is antitone in `U`. -/
theorem GammaU_mono {U' : Subgroup (BHat d.a d.b)ˣ} (hle : U' ≤ U) : GammaU d q hq U' ≤ GammaU d q hq U :=
  fun _ h => mem_GammaU_iff.2 ⟨(mem_GammaU_iff.1 h).1, hle (mem_GammaU_iff.1 h).2⟩

end Gamma

/-! ### Norm one: `B̂^1`, `X^1(U)` -/

section NormOne

/-- `def:s02-Xone`: `B̂^1 = ker(nrd : B̂^× → 𝔸_f^×)` (`Quat.nrdHat`, S02-L10). -/
noncomputable def BHatOne (d : DefiniteData) : Subgroup (BHat d.a d.b)ˣ :=
  (Quat.nrdHat d.a d.b).ker

/-- `def:s02-Xone`: the norm-one class set `X^1(U) = B^1 \ B̂^1 / U^1`, with `B^1 = B^× ∩ B̂^1` and
`U^1 = U ∩ B̂^1`, both as subgroups of `B̂^1`. -/
abbrev XBone (d : DefiniteData) (U : Subgroup (BHat d.a d.b)ˣ) : Type :=
  DoubleCoset.Quotient (((globalUnits d.a d.b).subgroupOf (BHatOne d) : Subgroup (BHatOne d)) : Set (BHatOne d))
    ((U.subgroupOf (BHatOne d) : Subgroup (BHatOne d)) : Set (BHatOne d))

/-- `def:s02-Xone`, `lem:s02-normone`: the natural map `X^1(U) → X_B(U)`, `[x]^1 ↦ [x]` (see `XBone.toXB_mk`). -/
noncomputable def XBone.toXB (d : DefiniteData) (U : Subgroup (BHat d.a d.b)ˣ) : XBone d U → XB U :=
  fun c => DoubleCoset.mk (globalUnits d.a d.b) U ((Quotient.out c : BHatOne d) : (BHat d.a d.b)ˣ)

variable {d : DefiniteData} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-Xone` (`s02-Xone`): `X^1(U) → X_B(U)` sends `[x]^1` to `[x]`. -/
theorem XBone.toXB_mk (x : BHatOne d) :
    XBone.toXB d U (DoubleCoset.mk ((globalUnits d.a d.b).subgroupOf (BHatOne d)) (U.subgroupOf (BHatOne d)) x) =
      DoubleCoset.mk (globalUnits d.a d.b) U (x : (BHat d.a d.b)ˣ) := by
  obtain ⟨h, hh, k, hk, he⟩ :=
    DoubleCoset.mk_out_eq_mul ((globalUnits d.a d.b).subgroupOf (BHatOne d)) (U.subgroupOf (BHatOne d)) x
  show DoubleCoset.mk (globalUnits d.a d.b) U
      ((Quotient.out (DoubleCoset.mk ((globalUnits d.a d.b).subgroupOf (BHatOne d))
        (U.subgroupOf (BHatOne d)) x) : BHatOne d) : (BHat d.a d.b)ˣ) = _
  rw [he, DoubleCoset.eq]
  refine ⟨((h : BHatOne d) : (BHat d.a d.b)ˣ)⁻¹,
    (globalUnits d.a d.b).inv_mem (Subgroup.mem_subgroupOf.1 hh),
    ((k : BHatOne d) : (BHat d.a d.b)ˣ)⁻¹, U.inv_mem (Subgroup.mem_subgroupOf.1 hk), ?_⟩
  simp only [Subgroup.coe_mul]
  group

end NormOne

/-! ### Strong approximation at one level -/

section SA

/-- `thm:s02-SA`, the shape (SA_U) (N2): `B̂^1 = B^1 (B^1_q × U^{1,(q)})`. Every `y ∈ B̂^1` is
`ι(β) · ι_q^{-1}(g) · u` with `β ∈ B^1`, `g ∈ SL₂(ℚ_q)` (`≅ B^1_q`) and `u ∈ U ∩ B̂^1` with `u_q = 1`. -/
def SAat (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ) : Prop :=
  ∀ y ∈ BHatOne d, ∃ β : (QuatAlg ℚ d.a d.b)ˣ, nrd (β : QuatAlg ℚ d.a d.b) = 1 ∧
    ∃ g : GL (Fin 2) ℚ_[q], Matrix.GeneralLinearGroup.det g = 1 ∧
      ∃ u ∈ U ⊓ BHatOne d, localComponent d q hq u = 1 ∧
        y = iotaU d.a d.b β * localEmbedGL d q hq g * u

end SA

end Langlandscape.Tree
