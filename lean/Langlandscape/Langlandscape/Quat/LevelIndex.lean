/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.Basic
import AlgJL.VolIII.P2.Mass
import Mathlib.Data.ZMod.Units

/-!
# `Ψ`-levels `U0Psi`, `U1Psi` and their indices (S01-L4a)

For a level structure `φ : O → M₂(ℤ/N)` the import provides a reduction homomorphism
`Ψ : Ô^× → GL₂(ℤ/N)` (`GL2TF.Quat.exists_level_hom`), surjective by `level_hom_surjective`.  We define

* `levelHom φ` : a chosen such `Ψ`;
* `borel1 N` : `{g ∈ GL₂(ℤ/N) : g₁₀ = 0, g₁₁ = 1}`;
* `U0Psi φ`, `U1Psi φ` : the preimages (as subgroups of `B̂^×`, contained in `Ô^×`) of `borel`, `borel1`.

Main results: `relIndex_U0Psi : [Ô^× : U0Psi] = ψ(N)`, `index_borel1_borel : [B : B₁] = φ(N)`,
`relIndex_U1Psi : [Ô^× : U1Psi] = ψ(N) φ(N)`.  Status: *formalized* (`thm:s01-mass`(c) input).
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

variable {a b : ℤ} (O : QOrder a b) {N : ℕ} [NeZero N]

/-- A chosen reduction homomorphism `Ô^× → GL₂(ℤ/N)` attached to a level structure (`thm:s01-mass`(c)). -/
noncomputable def levelHom (φ : LevelStructure O N) :
    orderCompletionUnits O →* GL (Fin 2) (ZMod N) :=
  Classical.choose (exists_level_hom O φ)

/-- `ker`-side description of `levelHom` (`thm:s01-mass`(c)). -/
theorem levelHom_spec (φ : LevelStructure O N) :
    (orderCompletionUnits (eichlerOrder φ)).subgroupOf (orderCompletionUnits O) =
      (GL2TF.borel (ZMod N)).comap (levelHom O φ) :=
  (Classical.choose_spec (exists_level_hom O φ)).1

/-- `levelHom` is surjective (`thm:s01-mass`(c)). -/
theorem levelHom_surjective (φ : LevelStructure O N) : Function.Surjective (levelHom O φ) :=
  level_hom_surjective O φ _ (Classical.choose_spec (exists_level_hom O φ)).2

/-- The subgroup `B₁(ℤ/N) = {g : g₁₀ = 0, g₁₁ = 1}` of `GL₂(ℤ/N)` (`thm:s01-mass`(c)). -/
def borel1 (N : ℕ) : Subgroup (GL (Fin 2) (ZMod N)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    rw [hg.1, hg.2, hh.1, hh.2]; simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod N)).det = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 := by
      rw [Matrix.det_fin_two, hg.1, hg.2]; ring
    have hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) := hdet ▸ (Matrix.isUnits_det_units g)
    have hinv : Ring.inverse ((g : Matrix (Fin 2) (Fin 2) (ZMod N)).det) *
        (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 := by
      rw [hdet]; exact Ring.inverse_mul_cancel _ hu
    simp [hg.1, hg.2, hinv]

/-- `B₁ ≤ B` (`thm:s01-mass`(c)). -/
theorem borel1_le_borel (N : ℕ) : borel1 N ≤ GL2TF.borel (ZMod N) := fun _ hg => hg.1

/-- The `d`-entry homomorphism `B(ℤ/N) → (ℤ/N)ˣ`. -/
def borelD (N : ℕ) : GL2TF.borel (ZMod N) →* (ZMod N)ˣ where
  toFun g :=
    have key : (g.1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 *
        ((g.1⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 = 1 := by
      have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod N) => m 1 1) (Units.mul_inv g.1)
      have h0 : (g.1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 := g.2
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h0] using h
    ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1, ((g.1⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1,
      key, by rw [mul_comm]; exact key⟩
  map_one' := by ext; simp
  map_mul' g h := by
    have h0 : (g.1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 := g.2
    ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, h0]

/-- `borelD` is onto (`thm:s01-mass`(c)). -/
theorem borelD_surjective (N : ℕ) : Function.Surjective (borelD N) := by
  intro u
  let m : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, (u : ZMod N)]
  let m' : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, ((u⁻¹ : (ZMod N)ˣ) : ZMod N)]
  let g : GL (Fin 2) (ZMod N) := ⟨m, m', by
    ext i j; fin_cases i <;> fin_cases j <;> simp [m, m', Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [m, m', Matrix.mul_apply, Fin.sum_univ_two]⟩
  refine ⟨⟨g, ?_⟩, ?_⟩
  · show (m : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0
    simp [m]
  · ext; simp [borelD, g, m]

/-- `ker borelD = B₁` (`thm:s01-mass`(c)). -/
theorem borelD_ker (N : ℕ) : (borelD N).ker = (borel1 N).subgroupOf (GL2TF.borel (ZMod N)) := by
  ext g
  have h0 : (g.1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 := g.2
  simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, borel1, borelD, Units.ext_iff, h0]

/-- `[B(ℤ/N) : B₁(ℤ/N)] = φ(N)` (`thm:s01-mass`(c)). -/
theorem index_borel1_borel (N : ℕ) [NeZero N] :
    (borel1 N).relIndex (GL2TF.borel (ZMod N)) = Nat.totient N := by
  rw [Subgroup.relIndex, ← borelD_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (borelD_surjective N)]
  rw [Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- `U0Psi φ`: the `Ψ`-preimage of `B(ℤ/N)`, as a subgroup of `B̂^×` inside `Ô^×` (`thm:s01-mass`(c)). -/
noncomputable def U0Psi (φ : LevelStructure O N) : Subgroup (BHat a b)ˣ :=
  ((GL2TF.borel (ZMod N)).comap (levelHom O φ)).map (orderCompletionUnits O).subtype

/-- `U1Psi φ`: the `Ψ`-preimage of `B₁(ℤ/N)` (`thm:s01-mass`(c)). -/
noncomputable def U1Psi (φ : LevelStructure O N) : Subgroup (BHat a b)ˣ :=
  ((borel1 N).comap (levelHom O φ)).map (orderCompletionUnits O).subtype

/-- `U1Psi ≤ U0Psi` (`thm:s01-mass`(c)). -/
theorem U1Psi_le_U0Psi (φ : LevelStructure O N) : U1Psi O φ ≤ U0Psi O φ :=
  Subgroup.map_mono (Subgroup.comap_mono (borel1_le_borel N))

/-- `U0Psi ≤ Ô^×` (`thm:s01-mass`(c)). -/
theorem U0Psi_le (φ : LevelStructure O N) : U0Psi O φ ≤ orderCompletionUnits O :=
  Subgroup.map_subtype_le _

/-- `U1Psi ≤ Ô^×` (`thm:s01-mass`(c)). -/
theorem U1Psi_le (φ : LevelStructure O N) : U1Psi O φ ≤ orderCompletionUnits O :=
  Subgroup.map_subtype_le _

/-- helper (`thm:s01-mass`(c)). -/
theorem subgroupOf_map_subtype_self {G : Type*} [Group G] (K : Subgroup G) (S : Subgroup K) :
    (S.map K.subtype).subgroupOf K = S := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
  exact ⟨fun ⟨y, hy, h⟩ => Subtype.ext h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

/-- `[Ô^× : U0Psi] = ψ(N)` (`thm:s01-mass`(c)): import `gl2_borel_index` pulled back along the surjection
`levelHom` (`index_comap_of_surjective`). -/
theorem relIndex_U0Psi (φ : LevelStructure O N) :
    (((U0Psi O φ).relIndex (orderCompletionUnits O) : ℕ) : ℚ) = GL2TF.Explicit.dedekindPsi N := by
  rw [U0Psi, Subgroup.relIndex, subgroupOf_map_subtype_self,
    Subgroup.index_comap_of_surjective _ (levelHom_surjective O φ)]
  exact gl2_borel_index N (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))

/-- `[Ô^× : U1Psi] = ψ(N) φ(N)` (`thm:s01-mass`(c)). -/
theorem relIndex_U1Psi (φ : LevelStructure O N) :
    (((U1Psi O φ).relIndex (orderCompletionUnits O) : ℕ) : ℚ) =
      GL2TF.Explicit.dedekindPsi N * (Nat.totient N : ℚ) := by
  have h1 : (U1Psi O φ).relIndex (orderCompletionUnits O) = (borel1 N).index := by
    rw [U1Psi, Subgroup.relIndex, subgroupOf_map_subtype_self,
      Subgroup.index_comap_of_surjective _ (levelHom_surjective O φ)]
  have h2 := Subgroup.relIndex_mul_index (borel1_le_borel N)
  rw [h1, ← h2, index_borel1_borel, Nat.cast_mul, mul_comm, gl2_borel_index N
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))]

end Langlandscape.Quat
