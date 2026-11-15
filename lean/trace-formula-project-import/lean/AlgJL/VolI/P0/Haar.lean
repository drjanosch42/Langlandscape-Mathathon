import AlgJL.Meta.Tag
import AlgJL.VolI.P0.TopGroups
import AlgJL.VolI.P0.Decompositions

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P0/Haar.lean` at commit 84818d0, reduced to its
algebraic/topological declarations. All Haar measures, unimodularity, Iwasawa integration formulas, Borel-space
instances and their plumbing (265 declarations, among them every `I.haar.*` item except the ones below) are dropped.
Kept, verbatim: the topological instances `gl2_locallyCompactSpace`, `maxCompact_compactSpace`,
`gl2Real_locallyCompactSpace`, `gl2Real_secondCountableTopology`, `maxCompactReal_compactSpace`,
`normOneGroup_locallyCompactSpace`; the Borel coordinates `borel_diag_isUnit`, `diagElt_mem_torus`, `borelCoord_mem`,
`borelCoord`, `continuous_diagElt`, `borelCoord_mem_K_iff`; and `gl2Map_upperRightHom`, `gl2Map_diagElt`.
The section variables were reduced to the ones these declarations use. -/

open ValuativeRel GL2TF

namespace GL2TF.Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- `GL₂(F)` is locally compact, as an instance (B-only plumbing for `I.topgrp.thm:gl2-local-locally-compact`). -/
@[tf_aux "I.haar.lem:gl2-local-locally-compact-instance"]
instance gl2_locallyCompactSpace : LocallyCompactSpace (GL (Fin 2) F) :=
  (gl2_locallyCompact_t2_secondCountable F).1

/-- `K_F` is compact, as an instance (B-only plumbing for `I.topgrp.thm:max-compact-local-compact-open`). -/
@[tf_aux "I.haar.lem:max-compact-local-compact-instance"]
instance maxCompact_compactSpace : CompactSpace 𝐊[F] :=
  isCompact_iff_compactSpace.mp (maxCompact_isCompact_isOpen F).1

end GL2TF.Local

namespace GL2TF

open Matrix.GeneralLinearGroup

/-- `GL₂(ℝ)` is locally compact, as an instance (B-only plumbing for `I.topgrp.thm:gl2-real-locally-compact`). -/
@[tf_aux "I.haar.lem:gl2-real-locally-compact-instance"]
instance gl2Real_locallyCompactSpace : LocallyCompactSpace (GL (Fin 2) ℝ) :=
  gl2Real_locallyCompact_t2_secondCountable_borel.1

/-- `GL₂(ℝ)` is second countable, as an instance (B-only plumbing). -/
@[tf_aux "I.haar.lem:gl2-real-second-countable-instance"]
instance gl2Real_secondCountableTopology : SecondCountableTopology (GL (Fin 2) ℝ) :=
  gl2Real_locallyCompact_t2_secondCountable_borel.2.2.1

/-- `K_∞ = O(2)` is compact, as an instance (B-only plumbing for `I.topgrp.thm:max-compact-real-compact`). -/
@[tf_aux "I.haar.lem:max-compact-real-compact-instance"]
instance maxCompactReal_compactSpace : CompactSpace maxCompactReal :=
  isCompact_iff_compactSpace.mp maxCompactReal_isCompact

/-! ### Borel coordinates -/

/-- The diagonal entries of `b ∈ B(R)` are units. -/
@[tf_aux "I.haar.lem:borel-diag-is-unit"]
theorem borel_diag_isUnit {R : Type*} [CommRing R] (b : borel R) (i : Fin 2) :
    IsUnit (((b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i i) := by
  have hb : ((b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := b.2
  have hdet : IsUnit (((b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 *
      ((b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp (b : GL (Fin 2) R).isUnit
    rwa [Matrix.det_fin_two, hb, mul_zero, sub_zero] at this
  fin_cases i
  · exact isUnit_of_mul_isUnit_left hdet
  · exact isUnit_of_mul_isUnit_right hdet

/-- `diag(t₁, t₂) ∈ T(R)`. -/
@[tf_aux "I.haar.lem:diag-elt-mem-torus"]
theorem diagElt_mem_torus {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) : diagElt t₁ t₂ ∈ torus R := by
  simp [torus, diagElt]

/-- `n(x) diag(t₁, t₂) ∈ B(R)`. -/
@[tf_aux "I.haar.lem:borel-coordinates-mem"]
theorem borelCoord_mem {R : Type*} [CommRing R] (x : R) (t₁ t₂ : Rˣ) :
    upperRightHom x * diagElt t₁ t₂ ∈ borel R := by
  show ((upperRightHom x * diagElt t₁ t₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0
  simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two]

/-- The coordinate map `(x, t₁, t₂) ↦ n(x) diag(t₁, t₂)` into `B(R)`. -/
@[tf_aux "I.haar.def:borel-coordinates"]
def borelCoord {R : Type*} [CommRing R] (p : R × Rˣ × Rˣ) : borel R :=
  ⟨upperRightHom p.1 * diagElt p.2.1 p.2.2, borelCoord_mem p.1 p.2.1 p.2.2⟩

section BorelCoord

open Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R] [TopologicalSpace R]

theorem continuous_diagElt : Continuous fun t : Rˣ × Rˣ ↦ diagElt t.1 t.2 := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagElt] <;> fun_prop
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagElt, Units.inv_mk] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_coe_inv (M := R)).comp (continuous_fst (X := Rˣ) (Y := Rˣ))
        | exact (Units.continuous_coe_inv (M := R)).comp (continuous_snd (X := Rˣ) (Y := Rˣ))

end BorelCoord

end GL2TF

namespace GL2TF.Local

variable (F : Type*) [Field F] [ValuativeRel F]

theorem borelCoord_mem_K_iff (x : F) (t₁ t₂ : Fˣ) :
    ((borelCoord (x, t₁, t₂) : borel F) : GL (Fin 2) F) ∈ 𝐊[F] ↔
      x ∈ 𝒪[F] ∧ (∃ v : 𝒪[F]ˣ, ((v : 𝒪[F]) : F) = t₁) ∧ ∃ v : 𝒪[F]ˣ, ((v : 𝒪[F]) : F) = t₂ := by
  have key := (mem_maxCompact_tfae (Subring.subtype 𝒪[F]) Subtype.val_injective
    ((borelCoord (x, t₁, t₂) : borel F) : GL (Fin 2) F)).out 1 2
  rw [key]
  have e : ((((borelCoord (x, t₁, t₂) : borel F) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(t₁ : F), x * t₂; 0, (t₂ : F)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [borelCoord, diagElt, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e, Matrix.det_fin_two_of]
  have hr : ∀ y : F, y ∈ Set.range (Subring.subtype 𝒪[F]) ↔ y ∈ 𝒪[F] :=
    fun y ↦ ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h ↦ ⟨⟨y, h⟩, rfl⟩⟩
  constructor
  · rintro ⟨hent, u, hu⟩
    have h1 : (t₁ : F) ∈ 𝒪[F] := (hr _).mp (by simpa using hent 0 0)
    have h2 : (t₂ : F) ∈ 𝒪[F] := (hr _).mp (by simpa using hent 1 1)
    have h12 : (t₁ : F) ∈ 𝒪[F] → (t₂ : F) ∈ 𝒪[F] → IsUnit ((⟨_, h1⟩ : 𝒪[F]) * ⟨_, h2⟩) := fun _ _ ↦ by
      have : ((⟨_, h1⟩ : 𝒪[F]) * ⟨_, h2⟩) = u := by
        apply Subtype.ext; simp only [Subring.coe_mul]; simpa using hu
      rw [this]; exact u.isUnit
    have hu1 := isUnit_of_mul_isUnit_left (h12 h1 h2)
    have hu2 := isUnit_of_mul_isUnit_right (h12 h1 h2)
    refine ⟨?_, ⟨hu1.unit, rfl⟩, ⟨hu2.unit, rfl⟩⟩
    have hxt : x * t₂ ∈ 𝒪[F] := (hr _).mp (by simpa using hent 0 1)
    have hinv : ((hu2.unit⁻¹ : 𝒪[F]ˣ) : 𝒪[F]).1 * (t₂ : F) = 1 := by
      have hu2v : ((hu2.unit : 𝒪[F]ˣ) : 𝒪[F]) = ⟨_, h2⟩ := hu2.unit_spec
      have := congrArg Subtype.val hu2.unit.inv_mul
      rw [hu2v] at this
      simpa only [Subring.coe_mul, OneMemClass.coe_one] using this
    have : x = (x * t₂) * ((hu2.unit⁻¹ : 𝒪[F]ˣ) : 𝒪[F]).1 := by
      rw [mul_assoc, mul_comm (t₂ : F), hinv, mul_one]
    rw [this]
    exact (𝒪[F]).mul_mem hxt (((hu2.unit⁻¹ : 𝒪[F]ˣ) : 𝒪[F])).2
  · rintro ⟨hx, ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩
    refine ⟨fun i j ↦ ?_, v₁ * v₂, by simp [hv₁, hv₂]⟩
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    · exact ⟨v₁, hv₁⟩
    · exact ⟨⟨x, hx⟩ * v₂, by simp [hv₂]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨v₂, hv₂⟩

end GL2TF.Local

namespace GL2TF

open Matrix.GeneralLinearGroup

theorem gl2Map_upperRightHom {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    gl2Map f (upperRightHom x) = upperRightHom (f x) := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2Map, upperRightHom, Matrix.GeneralLinearGroup.map]

theorem gl2Map_diagElt {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (t₁ t₂ : Rˣ) :
    gl2Map f (diagElt t₁ t₂) = diagElt (Units.map f.toMonoidHom t₁) (Units.map f.toMonoidHom t₂) := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2Map, diagElt, Matrix.GeneralLinearGroup.map]

/-- `G(𝔸)^1` is locally compact, as an instance (B-only plumbing for `I.haar.thm:norm-one-unimodular`). -/
@[tf_aux "I.haar.lem:norm-one-locally-compact-instance"]
instance normOneGroup_locallyCompactSpace : LocallyCompactSpace normOneGroup :=
  normOneGroup_closed_normal.1.isClosedEmbedding_subtypeVal.locallyCompactSpace

end GL2TF
