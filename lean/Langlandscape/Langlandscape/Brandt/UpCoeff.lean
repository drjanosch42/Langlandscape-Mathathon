/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.HeckeCoeff
import Langlandscape.Brandt.Up
import Langlandscape.Quat.Vk

/-!
# `U_p` with coefficients in `V_k` (S04-L15b, `eq:s01-Vk`, `def:s04-Pk`)

The coefficient datum for `Brandt(U_s, V_k ⊗ ℤ_p)`, `U_s = U_1(M p^s)`, `s ≥ 1`, `p ∤ M D`:

* `VkPhi`, `VkRho`: the action of `U ⊆ B̂^×` on `V_k` through `u ↦ ι_p(u_p) ∈ GL₂(ℤ_p) ⊆ Σ_p`
  (for any `U` with `ι_p(u_p) ∈ GL₂(ℤ_p)`);
* `VkExt : HeckeExt U ℤ_[p] (Vk ℤ_[p] k) (VkRho …)`: its extension to `Σ = ι_p⁻¹(Σ_p) ⊆ B̂^×`
  (`L15a`'s `HeckeExt`), `Σ_p = M₂(ℤ_p) ∩ GL₂(ℚ_p)` acting by `eq:s01-Vk`;
* `UpV := heckeTV (VkExt …) ϖ …` at level `U_s`, `ϖ = ι_p⁻¹ diag(p, 1)`: `(UpV F)(x) = ∑_j ϖ_j · F(x ϖ_j)`;
* `evV_UpV`: `ev((UpV F)(x)) = ∑_j ev(F(x ϖ_j))` (`def:s04-Pk`, proof step (iii): `ev(ϖ_j P) = P(0,1)`);
* `evV_UpV_eq_Up`: if `ev ∘ F` is exactly (over `ℤ_[p]`) the pullback of a function `f` on `X(U_s)`, then
  `ev ∘ UpV F` is that of `Up f` (`Up`, trivial coefficients, `S01-L10`). **Caveat (audit R2):** for `k ≥ 3` this
  hypothesis holds only for `F = 0` (exact right `U_s`-invariance of `ev ∘ F` forces `F(x)` constant, hence `0` in
  degree `k - 2 ≥ 1`; paper argument of the audit, not machine-checked), so the lemma is not the first half of
  `def:s04-Pk`. The honest content is `evV_UpV`. The tex statement is a congruence, `ev ∘ F` descends to `X(U_s)` only
  modulo `p ^ s` (values in `ZMod (p ^ s)`); that congruence form is **not formalized**.

Status: `evV_UpV` *formalized*; `evV_UpV_eq_Up` *formalized* but meaningful only for `k = 2` (see caveat); the mod-`p^s`
form of `def:s04-Pk` not formalized.
-/

open Langlandscape.Local

namespace Langlandscape.Brandt

open Langlandscape.Quat
open scoped Classical

section Rho

variable (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D) (k : ℕ)
  (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (hU : ∀ u ∈ U, localComponent d p hp u ∈ GL2Zl p)

/-- `eq:s01-Vk` (`s01-Vk`): the action of `u ∈ U` on `V_k` through `ι_p(u_p) ∈ GL₂(ℤ_p) ⊆ Σ_p`, as an
endomorphism-valued monoid homomorphism. -/
noncomputable def VkPhi : U →* Module.End ℤ_[p] (Vk ℤ_[p] k) :=
  (VkAct (p := p) k).comp (MonoidHom.codRestrict ((localComponent d p hp).comp U.subtype) (SigmaP p)
    (fun u => mem_SigmaP_of_mem_GL2Zl (hU u u.2)))

/-- `eq:s01-Vk` (`s01-Vk`): the coefficient action `ρ : U →* (V_k ≃ₗ V_k)` of `U` (invertible, since `U` acts
through `GL₂(ℤ_p)`). -/
noncomputable def VkRho : U →* (Vk ℤ_[p] k ≃ₗ[ℤ_[p]] Vk ℤ_[p] k) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ_[p] (Vk ℤ_[p] k)).toMonoidHom.comp
    (MonoidHom.toHomUnits (VkPhi d p hp k U hU))

/-- `def:s01-hecke` with coefficients (`s01-Vk`, `s04-L15b`): the extension of `ρ = VkRho` to
`Σ = ι_p⁻¹(Σ_p) = {y ∈ B̂^× | ι_p(y_p) ∈ M₂(ℤ_p)}` acting by `eq:s01-Vk`. -/
noncomputable def VkExt : HeckeExt U ℤ_[p] (Vk ℤ_[p] k) (VkRho d p hp k U hU) where
  Sig := (SigmaP p).comap (localComponent d p hp)
  rhoSig := (VkAct (p := p) k).comp (MonoidHom.submonoidComap (localComponent d p hp) (SigmaP p))
  U_le u hu := mem_SigmaP_of_mem_GL2Zl (hU u hu)
  compat u := by
    have h := LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (R := ℤ_[p])
      (M := Vk ℤ_[p] k) (MonoidHom.toHomUnits (VkPhi d p hp k U hU) u)
    exact h.symm

end Rho

section Varpi

variable {d : DefiniteData} {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `def:s01-NUp` (`s04-L15b`): `ϖ = diag(p, 1) ∈ Σ_p`. -/
theorem varpiDiag_mem_SigmaP : varpiDiag p ∈ SigmaP p := by
  have h1 : ‖(p : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) (p : ℤ)
  have hz : ‖(0 : ℚ_[p])‖ ≤ 1 := by simp
  have ho : ‖(1 : ℚ_[p])‖ ≤ 1 := by simp
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact h1 | exact hz | exact ho | (simp [varpiDiag, h1]; done)

/-- `def:s01-NUp` (`s04-L15b`): `ϖ_j = (p j; 0 1) ∈ Σ_p`. -/
theorem varpi_mem_SigmaP (j : Fin p) : varpi p j ∈ SigmaP p := by
  have h1 : ‖(p : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) (p : ℤ)
  have hj : ‖((j : ℕ) : ℚ_[p])‖ ≤ 1 := by
    exact_mod_cast Padic.norm_int_le_one (p := p) ((j : ℕ) : ℤ)
  have hz : ‖(0 : ℚ_[p])‖ ≤ 1 := by simp
  have ho : ‖(1 : ℚ_[p])‖ ≤ 1 := by simp
  intro i l
  fin_cases i <;> fin_cases l <;> first | exact h1 | exact hj | exact hz | exact ho

/-- `def:s01-NUp` (`s04-L15b`): the bottom row of `ϖ_j` is `(0, 1)`: entry `(2,1)`. -/
theorem varpi_row_zero (j : Fin p) : (Units.val (varpi p j)) 1 0 = 0 := by
  simp [varpi]

/-- `def:s01-NUp` (`s04-L15b`): the bottom row of `ϖ_j` is `(0, 1)`: entry `(2,2)`. -/
theorem varpi_row_one (j : Fin p) : (Units.val (varpi p j)) 1 1 = 1 := by
  simp [varpi]

end Varpi

section Up

variable {d : DefiniteData} {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D} {M s : ℕ}
  {hN : (M * p ^ s).Coprime d.D}

/-- `def:s01-levels` (`s04-L15b`): `U_s` acts through `GL₂(ℤ_p)` at `p` (it lies in `K1 p s`). -/
theorem Utower_localComponent_mem (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    ∀ u ∈ d.Utower M p s hN, localComponent d p hp u ∈ GL2Zl p :=
  fun u hu => K1_le_GL2Zl s ((mem_Utower_iff_factor_at (hp := hp) hM hpM hs u).1 hu).2

/-- `def:s01-NUp` (`s04-L15b`): `ϖ = ι_p⁻¹ diag(p,1) ∈ Σ`. -/
theorem varpiDiag_mem_Sig (k : ℕ) (hU : ∀ u ∈ d.Utower M p s hN, localComponent d p hp u ∈ GL2Zl p) :
    localEmbedGL d p hp (varpiDiag p) ∈ (VkExt d p hp k _ hU).Sig := by
  show localComponent d p hp (localEmbedGL d p hp (varpiDiag p)) ∈ SigmaP p
  rw [localComponent_localEmbedGL]
  exact varpiDiag_mem_SigmaP

/-- `def:s01-NUp` (`s04-L15b`): `ϖ_j = ι_p⁻¹(p j; 0 1) ∈ Σ`. -/
theorem varpi_mem_Sig (k : ℕ) (hU : ∀ u ∈ d.Utower M p s hN, localComponent d p hp u ∈ GL2Zl p)
    (j : Fin p) : localEmbedGL d p hp (varpi p j) ∈ (VkExt d p hp k _ hU).Sig := by
  show localComponent d p hp (localEmbedGL d p hp (varpi p j)) ∈ SigmaP p
  rw [localComponent_localEmbedGL]
  exact varpi_mem_SigmaP j

/-- `def:s01-NUp` (`s04-L15b`): `{ϖ_j}_{j < p}` is a system of representatives of `U_s ϖ U_s / U_s`
(the three clauses of `IsDcReps`, as in `Up_apply`). -/
theorem varpi_isDcReps (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    IsDcReps (d.Utower M p s hN) (localEmbedGL d p hp (varpiDiag p))
      (Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact localEmbedGL_varpi_mem_dcSet hM hpM hs j
  · intro y hy
    obtain ⟨j, hj⟩ := exists_varpi_inv_mul_mem hM hpM hs hy
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ j), (QuotientGroup.eq.2 hj).symm⟩
  · intro y hy y' hy' hyy'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy')
    rw [varpi_cosets_injective hM hpM hs hyy']

variable (d p hp M s hN) (k : ℕ)

/-- `def:s04-Pk` (`s01-Vk`, `s04-L15b`): `U_p` with coefficients in `V_k` at level `U_s = U_1(M p^s)`,
`(U_p F)(x) = ∑_{j<p} ϖ_j · F(x ϖ_j)` (`heckeTV` of `ϖ = ι_p⁻¹ diag(p,1)` for the extension `VkExt`). -/
noncomputable def UpV (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    brandtModule (d.Utower M p s hN) ℤ_[p] (Vk ℤ_[p] k)
        (VkRho d p hp k _ (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs)) →ₗ[ℤ_[p]]
      brandtModule (d.Utower M p s hN) ℤ_[p] (Vk ℤ_[p] k)
        (VkRho d p hp k _ (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs)) :=
  heckeTV (VkExt d p hp k _ (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs))
    (localEmbedGL d p hp (varpiDiag p))
    (varpiDiag_mem_Sig k _) (Up_relIndex_ne_zero hM hpM hs)

variable {d p hp M s hN k}

/-- `def:s04-Pk` (`s04-Pk`, proof step (iii)): `ev` intertwines `U_p` on `V_k`-valued forms with the sum over
`ϖ_j`: `ev((U_p F)(x)) = ∑_j ev(F(x ϖ_j))`, using `ev(ϖ_j P) = P((0,1)ϖ_j) = P(0,1)`. -/
theorem evV_UpV (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (F : brandtModule (d.Utower M p s hN) ℤ_[p] (Vk ℤ_[p] k)
      (VkRho d p hp k _ (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs)))
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    evV ℤ_[p] k ((UpV d p hp M s hN k hM hpM hs F).1 x) =
      ∑ j : Fin p, evV ℤ_[p] k (F.1 (x * localEmbedGL d p hp (varpi p j))) := by
  have hinj' : Set.InjOn (fun j : Fin p => localEmbedGL d p hp (varpi p j)) ↑(Finset.univ : Finset (Fin p)) :=
    fun j _ j' _ hjj' => varpi_cosets_injective (hN := hN) hM hpM hs
      (congrArg (fun z => (QuotientGroup.mk z : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ d.Utower M p s hN)) hjj')
  rw [UpV, heckeTV_apply_reps _ _ _ _ (varpi_isDcReps hM hpM hs) F x, map_sum,
    Finset.sum_image hinj']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HeckeExt.rhoExt_of_mem _
    (varpi_mem_Sig k (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs) j)]
  exact evV_VkAct_of_row k
    ⟨localComponent d p hp (localEmbedGL d p hp (varpi p j)),
      (by rw [localComponent_localEmbedGL]; exact varpi_mem_SigmaP j)⟩
    (by show (Units.val (localComponent d p hp (localEmbedGL d p hp (varpi p j)))) 1 0 = 0
        rw [localComponent_localEmbedGL]; exact varpi_row_zero j)
    (by show (Units.val (localComponent d p hp (localEmbedGL d p hp (varpi p j)))) 1 1 = 1
        rw [localComponent_localEmbedGL]; exact varpi_row_one j) _

/-- `def:s04-Pk` (`s04-Pk`, auxiliary; *not* its first half): if `ev ∘ F` is exactly the pullback of a function `f`
on `X(U_s)` over `ℤ_[p]` (`ev (F x) = f [x]`), then so is `ev ∘ UpV F`, for `Up f` (trivial coefficients,
`(U_p f)[x] = ∑_j f[x ϖ_j]`, `Up_apply`). **Caveat (audit R2):** for `k ≥ 3` the hypothesis `hF` forces `F = 0` (exact
right `U_s`-invariance of `ev ∘ F` makes `F(x)` a constant homogeneous polynomial of degree `k - 2 ≥ 1`; paper argument,
not machine-checked), so the statement has content only for `k = 2`. The tex's `def:s04-Pk` needs the congruence
form (`ev ∘ F` descends to `X(U_s)` only modulo `p ^ s`, values in `ZMod (p ^ s)`), which is **not formalized**; the
unconditional content is `evV_UpV`. -/
theorem evV_UpV_eq_Up (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (F : brandtModule (d.Utower M p s hN) ℤ_[p] (Vk ℤ_[p] k)
      (VkRho d p hp k _ (Utower_localComponent_mem (hp := hp) (hN := hN) hM hpM hs)))
    (f : ZXdual (d.Utower M p s hN) ℤ_[p])
    (hF : ∀ x, evV ℤ_[p] k (F.1 x) =
      f (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x))
    (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    evV ℤ_[p] k ((UpV d p hp M s hN k hM hpM hs F).1 x) =
      Up d M p s hN hp hM hpM hs ℤ_[p] f
        (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) := by
  rw [evV_UpV hM hpM hs F x, Up_apply hM hpM hs f x]
  exact Finset.sum_congr rfl fun j _ => hF _

end Up

end Langlandscape.Brandt
