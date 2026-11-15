import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Haar
import AlgJL.VolI.P0.Reps

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/PrincipalSeries.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (2): `deltaHalf_ne_zero`, `psChar_ne_zero`.
Dropped tagged IDs: none. -/

/-!
# Quasi-characters, the unramified principal series and the spherical vector (M5a, unit U2)

Lean counterpart of `vol1/ch-1-02-smooth.tex` §1 and the first half of §2 (items 19–25b of
`docs/sprints/M5a-plan.md`). Owner: L2 (items 19–25b); L1 adds items 26–27 in a separate module.

Conventions (D-CHAR, D-PS; `docs/notes/M5a-jacquet-spike.md`): a quasi-character is the subtype
`{χ : Fˣ →* ℂˣ // Continuous χ}` with a coercion to `Fˣ → ℂ`; `I(χ₁, χ₂)` is a `Submodule ℂ (GL₂(F) → ℂ)`
(normalized induction: the factor `|t₁/t₂|^{1/2}` is in the definition), with `π_χ` the right translation.
-/

open Matrix Matrix.GeneralLinearGroup ValuativeRel GL2TF GL2TF.Local
open scoped Pointwise

namespace GL2TF.Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-! ## §1 Quasi-characters -/

/-- A quasi-character of `F^×`: a continuous group homomorphism `F^× → ℂ^×`. -/
@[tf_id "I.smooth.def:quasi-character"]
def QuasiChar (F : Type*) [Field F] [TopologicalSpace F] : Type _ := {χ : Fˣ →* ℂˣ // Continuous χ}

/-- A quasi-character as a function `F^× → ℂ` (B-only). -/
@[tf_aux "I.smooth.def:quasi-character-coe"]
instance QuasiChar.instCoeFun (F : Type*) [Field F] [TopologicalSpace F] :
    CoeFun (QuasiChar F) (fun _ ↦ Fˣ → ℂ) :=
  ⟨fun χ t ↦ ((χ.1 t : ℂˣ) : ℂ)⟩

/-- A quasi-character is unramified if it is trivial on `𝒪_F^×` (B-only; the second sentence of
`I.smooth.def:quasi-character`). -/
@[tf_aux "I.smooth.def:quasi-character-unramified"]
def QuasiChar.IsUnramified (χ : QuasiChar F) : Prop :=
  ∀ u : 𝒪[F]ˣ, χ (Units.map (𝒪[F]).subtype.toMonoidHom u) = 1

variable (F) in
/-- The uniformizer `ϖ` as an element of `F^×` (B-only). -/
@[tf_aux "I.smooth.def:uniformizer-unit"]
noncomputable def unifUnit : Fˣ :=
  Units.mk0 ((unif F : 𝒪[F]) : F) (fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h))

/-! ### Proof helpers for `I.smooth.lem:unramified-character-param` -/

theorem unifUnit_val : ((unifUnit F : Fˣ) : F) = ((unif F : 𝒪[F]) : F) := rfl

/-- `ord(x)`: the exponent `n` of `x = u ϖ^n` (proof helper). -/
noncomputable def ordU (x : Fˣ) : ℤ :=
  (Classical.choose (unit_uniformizer_decomposition F (x : F) x.ne_zero)).2

theorem ordU_spec (x : Fˣ) : ∃ u : 𝒪[F]ˣ, (x : F) = ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ ordU x :=
  ⟨_, (Classical.choose_spec (unit_uniformizer_decomposition F (x : F) x.ne_zero)).1⟩

theorem ordU_eq {x : Fˣ} {u : 𝒪[F]ˣ} {n : ℤ} (h : (x : F) = ((u : 𝒪[F]) : F) * ((unif F : 𝒪[F]) : F) ^ n) :
    ordU x = n :=
  (congrArg Prod.snd ((Classical.choose_spec (unit_uniformizer_decomposition F (x : F) x.ne_zero)).2 (u, n) h)).symm

theorem ordU_mul (x y : Fˣ) : ordU (x * y) = ordU x + ordU y := by
  obtain ⟨u, hu⟩ := ordU_spec x
  obtain ⟨v, hv⟩ := ordU_spec y
  have hϖ0 : ((unif F : 𝒪[F]) : F) ≠ 0 := fun h ↦ (irreducible_unif F).ne_zero (Subtype.ext h)
  refine ordU_eq (u := u * v) ?_
  rw [Units.val_mul, hu, hv, zpow_add₀ hϖ0]
  push_cast
  ring

theorem ordU_unit (u : 𝒪[F]ˣ) : ordU ((Units.map (𝒪[F]).subtype.toMonoidHom) u) = 0 :=
  ordU_eq (u := u) (by simp)

theorem ordU_unif : ordU (unifUnit F) = 1 :=
  ordU_eq (u := 1) (by simp [unifUnit])

theorem eq_unif_zpow_mul (x : Fˣ) : ∃ u : 𝒪[F]ˣ, x = unifUnit F ^ ordU x * (Units.map (𝒪[F]).subtype.toMonoidHom) u := by
  obtain ⟨u, hu⟩ := ordU_spec x
  refine ⟨u, Units.ext ?_⟩
  rw [hu, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_comm]
  rfl

theorem normAbs_units_val (x : Fˣ) : normAbs F (x : F) = (q F : ℝ) ^ (-ordU x) := by
  obtain ⟨u, hu⟩ := ordU_spec x
  rw [hu, normAbs_unit_mul_unif_zpow]

theorem isLocallyConstant_ordU : IsLocallyConstant (ordU (F := F)) := by
  have hq1 : (1 : ℝ) < q F := mod_cast one_lt_q F
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun n ↦ ?_
  have hset : ordU (F := F) ⁻¹' {n} = Units.val ⁻¹'
      (((((unif F : 𝒪[F]) : F) ^ n) • (𝒪[F] : Set F)) ∩ ((((unif F : 𝒪[F]) : F) ^ (n + 1)) • (𝒪[F] : Set F))ᶜ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff]
    rw [← normAbs_le_iff_mem, ← normAbs_le_iff_mem, normAbs_units_val, neg_add]
    rw [zpow_le_zpow_iff_right₀ hq1, zpow_le_zpow_iff_right₀ hq1]
    omega
  rw [hset]
  refine IsOpen.preimage Units.continuous_val (IsOpen.inter ?_ ?_)
  · exact (unif_zpow_smul_integer_isCompact_isOpen F n).2
  · exact (unif_zpow_smul_integer_isCompact_isOpen F (n + 1)).1.isClosed.isOpen_compl

/-- The unramified quasi-character `x ↦ α^{ord(x)}` (proof helper). -/
noncomputable def unramChar (α : ℂˣ) : QuasiChar F :=
  ⟨{ toFun := fun x ↦ α ^ ordU x
     map_one' := by rw [ordU_eq (x := 1) (u := 1) (n := 0) (by simp), zpow_zero]
     map_mul' := fun x y ↦ by rw [ordU_mul, _root_.zpow_add] },
    (isLocallyConstant_ordU.comp fun n ↦ α ^ n).continuous⟩

theorem quasiChar_apply_unram (χ : QuasiChar F) (hχ : χ.IsUnramified) (u : 𝒪[F]ˣ) (n : ℤ) :
    χ (unifUnit F ^ n * (Units.map (𝒪[F]).subtype.toMonoidHom) u) = χ (unifUnit F) ^ n := by
  have h : ((χ.1 ((Units.map (𝒪[F]).subtype.toMonoidHom) u) : ℂˣ) : ℂ) = 1 := hχ u
  change ((χ.1 (unifUnit F ^ n * (Units.map (𝒪[F]).subtype.toMonoidHom) u) : ℂˣ) : ℂ) = ((χ.1 (unifUnit F) : ℂˣ) : ℂ) ^ n
  rw [map_mul, Units.val_mul, h, mul_one, map_zpow, Units.val_zpow_eq_zpow_val]

/-- Unramified quasi-characters are determined by `χ(ϖ)`: `χ(ϖ^n u) = χ(ϖ)^n` for `u ∈ 𝒪^×`, `n ∈ ℤ` (every
`x ∈ F^×` is of this form with `n = ord(x)`, `I.lf.thm:unit-uniformizer-decomposition`); `χ ↦ χ(ϖ)` is a bijection
from the unramified quasi-characters onto `ℂ^×`, and so is its square on pairs. -/
@[tf_id "I.smooth.lem:unramified-character-param"]
theorem unramified_character_param :
    (∀ χ : QuasiChar F, χ.IsUnramified → ∀ (u : 𝒪[F]ˣ) (n : ℤ),
        χ (unifUnit F ^ n * Units.map (𝒪[F]).subtype.toMonoidHom u) = χ (unifUnit F) ^ n) ∧
      Function.Bijective (fun χ : {χ : QuasiChar F // χ.IsUnramified} ↦ χ.1.1 (unifUnit F)) ∧
      Function.Bijective (fun χ : {χ : QuasiChar F // χ.IsUnramified} × {χ : QuasiChar F // χ.IsUnramified} ↦
        (χ.1.1.1 (unifUnit F), χ.2.1.1 (unifUnit F))) := by
  have hbij : Function.Bijective (fun χ : {χ : QuasiChar F // χ.IsUnramified} ↦ χ.1.1 (unifUnit F)) := by
    refine ⟨fun χ χ' h ↦ ?_, fun α ↦ ⟨⟨unramChar α, fun u ↦ ?_⟩, ?_⟩⟩
    · refine Subtype.ext (Subtype.ext (MonoidHom.ext fun x ↦ Units.ext ?_))
      obtain ⟨u, hu⟩ := eq_unif_zpow_mul x
      have e1 := quasiChar_apply_unram χ.1 χ.2 u (ordU x)
      have e2 := quasiChar_apply_unram χ'.1 χ'.2 u (ordU x)
      have h' : ((χ.1.1 (unifUnit F) : ℂˣ) : ℂ) = ((χ'.1.1 (unifUnit F) : ℂˣ) : ℂ) := congrArg Units.val h
      rw [hu]
      change ((χ.1.1 _ : ℂˣ) : ℂ) = ((χ'.1.1 _ : ℂˣ) : ℂ)
      exact e1.trans ((congrArg (· ^ ordU x) h').trans e2.symm)
    · change ((α ^ ordU ((Units.map (𝒪[F]).subtype.toMonoidHom) u) : ℂˣ) : ℂ) = 1
      rw [ordU_unit, zpow_zero, Units.val_one]
    · change α ^ ordU (unifUnit F) = α
      rw [ordU_unif, zpow_one]
  exact ⟨fun χ hχ u n ↦ quasiChar_apply_unram χ hχ u n, hbij, hbij.prodMap hbij⟩

/-! ## §1 The principal series `I(χ₁, χ₂)` -/

/-- `δ_B^{1/2}(diag(t₁, t₂)) = |t₁/t₂|_F^{1/2}` (positive real square root), as a complex number (B-only). -/
@[tf_aux "I.smooth.def:delta-half"]
noncomputable def deltaHalf (t₁ t₂ : Fˣ) : ℂ :=
  ((normAbs F ((t₁ : F) / t₂) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-! ### Proof helpers: the character `ψ = χδ_B^{1/2}` of `B(F)` -/

theorem deltaHalf_mul (s₁ s₂ t₁ t₂ : Fˣ) :
    deltaHalf (s₁ * t₁) (s₂ * t₂) = deltaHalf s₁ s₂ * deltaHalf t₁ t₂ := by
  unfold deltaHalf
  rw [← Complex.ofReal_mul, ← Real.mul_rpow (normAbs_nonneg F _) (normAbs_nonneg F _),
    ← (normAbs_multiplicative F _ _).1]
  congr 3
  push_cast
  field_simp

theorem deltaHalf_one : deltaHalf (1 : Fˣ) 1 = 1 := by
  simp [deltaHalf, normAbs_one]

/-- `δ^{1/2}(u, v) = 1` for units `u, v` of `𝒪` (proof helper). -/
theorem deltaHalf_units (u v : 𝒪[F]ˣ) : deltaHalf (Units.map (𝒪[F]).subtype.toMonoidHom u)
    (Units.map (𝒪[F]).subtype.toMonoidHom v) = 1 := by
  unfold deltaHalf
  have hu := (normAbs_uniformizer F).2.1 u
  have hv := (normAbs_uniformizer F).2.1 v
  have hv0 : ((v : 𝒪[F]) : F) ≠ 0 := fun h ↦ v.ne_zero (Subtype.ext h)
  have : normAbs F ((u : 𝒪[F]) : F) = normAbs F (((u : 𝒪[F]) : F) / ((v : 𝒪[F]) : F)) * normAbs F ((v : 𝒪[F]) : F) := by
    rw [← (normAbs_multiplicative F _ _).1, div_mul_cancel₀ _ hv0]
  rw [hu, hv, mul_one] at this
  simp [← this]

/-- The diagonal entries of `b ∈ B(F)` as units (proof helper). -/
noncomputable def bDiag (b : borel F) (i : Fin 2) : Fˣ := (borel_diag_isUnit b i).unit

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem bDiag_val (b : borel F) (i : Fin 2) :
    ((bDiag b i : Fˣ) : F) = ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i i := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem bDiag_mul (b b' : borel F) (i : Fin 2) : bDiag (b * b') i = bDiag b i * bDiag b' i := by
  have h1 : ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := b.2
  have h2 : ((b' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := b'.2
  apply Units.ext
  simp only [bDiag_val, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [h1, h2]

/-- `ψ(b) = χ₁(b₁₁) χ₂(b₂₂) |b₁₁/b₂₂|^{1/2}`, a character of `B(F)` (proof helper). -/
noncomputable def psChar (χ₁ χ₂ : QuasiChar F) : borel F →* ℂ where
  toFun b := χ₁ (bDiag b 0) * χ₂ (bDiag b 1) * deltaHalf (bDiag b 0) (bDiag b 1)
  map_one' := by
    have h : ∀ i, bDiag (1 : borel F) i = 1 := fun i ↦ Units.ext (by fin_cases i <;> simp [bDiag_val])
    simp only [h, deltaHalf_one, mul_one]
    change ((χ₁.1 1 : ℂˣ) : ℂ) * ((χ₂.1 1 : ℂˣ) : ℂ) = 1
    simp
  map_mul' b b' := by
    simp only [bDiag_mul, deltaHalf_mul]
    change ((χ₁.1 _ : ℂˣ) : ℂ) * ((χ₂.1 _ : ℂˣ) : ℂ) * _ =
      ((χ₁.1 _ : ℂˣ) : ℂ) * ((χ₂.1 _ : ℂˣ) : ℂ) * _ * (((χ₁.1 _ : ℂˣ) : ℂ) * ((χ₂.1 _ : ℂˣ) : ℂ) * _)
    simp only [map_mul, Units.val_mul]
    ring

theorem psChar_apply (χ₁ χ₂ : QuasiChar F) (b : borel F) :
    psChar χ₁ χ₂ b = χ₁ (bDiag b 0) * χ₂ (bDiag b 1) * deltaHalf (bDiag b 0) (bDiag b 1) := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
theorem upperRight_diag_mem (x : F) (t₁ t₂ : Fˣ) : upperRightHom x * diagElt t₁ t₂ ∈ borel F := by
  show ((upperRightHom x * diagElt t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem psChar_coord (χ₁ χ₂ : QuasiChar F) (x : F) (t₁ t₂ : Fˣ) :
    psChar χ₁ χ₂ ⟨upperRightHom x * diagElt t₁ t₂, upperRight_diag_mem x t₁ t₂⟩ =
      χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ := by
  have h0 : bDiag (⟨upperRightHom x * diagElt t₁ t₂, upperRight_diag_mem x t₁ t₂⟩ : borel F) 0 = t₁ :=
    Units.ext (by simp [bDiag_val, diagElt, Matrix.mul_apply, Fin.sum_univ_two])
  have h1 : bDiag (⟨upperRightHom x * diagElt t₁ t₂, upperRight_diag_mem x t₁ t₂⟩ : borel F) 1 = t₂ :=
    Units.ext (by simp [bDiag_val, diagElt, Matrix.mul_apply, Fin.sum_univ_two])
  rw [psChar_apply, h0, h1]

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- Every `b ∈ B(F)` is `n(x) diag(b₁₁, b₂₂)` (proof helper). -/
theorem borel_eq_coord (b : borel F) :
    (b : GL (Fin 2) F) = upperRightHom (((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 *
      ((bDiag b 1 : Fˣ) : F)⁻¹) * diagElt (bDiag b 0) (bDiag b 1) := by
  have h10 : ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := b.2
  have h11 : ((bDiag b 1 : Fˣ) : F) ≠ 0 := (bDiag b 1).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two, h10, bDiag_val] at h11 ⊢
  field_simp

theorem psChar_eq_coord (χ₁ χ₂ : QuasiChar F) (b : borel F) {x : F} {t₁ t₂ : Fˣ}
    (h : (b : GL (Fin 2) F) = upperRightHom x * diagElt t₁ t₂) :
    psChar χ₁ χ₂ b = χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ := by
  rw [← psChar_coord χ₁ χ₂ x t₁ t₂]
  exact congrArg _ (Subtype.ext h)

/-- An Iwasawa decomposition `g = b k`, `b ∈ B(F)`, `k ∈ K` (proof helper). -/
theorem iwasawa_borel (g : GL (Fin 2) F) : ∃ (b : borel F) (k : GL (Fin 2) F), k ∈ 𝐊[F] ∧ g = b * k := by
  obtain ⟨b, k, hk, hb, rfl⟩ := iwasawa_local F g
  exact ⟨⟨b, hb⟩, k, hk, rfl⟩

/-- `ψ = 1` on `B(F) ∩ K` for unramified `χ₁, χ₂` (proof helper). -/
theorem psChar_eq_one_of_mem_K (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    (b : borel F) (hb : (b : GL (Fin 2) F) ∈ 𝐊[F]) : psChar χ₁ χ₂ b = 1 := by
  set x := ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 * ((bDiag b 1 : Fˣ) : F)⁻¹
  have hb' : ((borelCoord (x, bDiag b 0, bDiag b 1) : borel F) : GL (Fin 2) F) ∈ 𝐊[F] := by
    have : ((borelCoord (x, bDiag b 0, bDiag b 1) : borel F) : GL (Fin 2) F) = b := (borel_eq_coord b).symm
    rw [this]; exact hb
  obtain ⟨-, ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := (borelCoord_mem_K_iff F x _ _).mp hb'
  have e₁ : bDiag b 0 = Units.map (𝒪[F]).subtype.toMonoidHom v₁ := Units.ext hv₁.symm
  have e₂ : bDiag b 1 = Units.map (𝒪[F]).subtype.toMonoidHom v₂ := Units.ext hv₂.symm
  rw [psChar_apply, e₁, e₂, h₁ v₁, h₂ v₂, deltaHalf_units, one_mul, one_mul]

/-- The normalized principal series `I(χ₁, χ₂)`: the functions `f : GL₂(F) → ℂ` that are right-invariant under
some compact open subgroup and satisfy `f(n(x) diag(t₁, t₂) g) = χ₁(t₁) χ₂(t₂) |t₁/t₂|^{1/2} f(g)`. -/
@[tf_id "I.smooth.def:principal-series"]
noncomputable def padicPrincipalSeries (χ₁ χ₂ : QuasiChar F) : Submodule ℂ (GL (Fin 2) F → ℂ) where
  carrier := {f | (∃ K' : Subgroup (GL (Fin 2) F), IsCompact (K' : Set (GL (Fin 2) F)) ∧
      IsOpen (K' : Set (GL (Fin 2) F)) ∧ ∀ g, ∀ k ∈ K', f (g * k) = f g) ∧
    ∀ (x : F) (t₁ t₂ : Fˣ) (g : GL (Fin 2) F),
      f (upperRightHom x * diagElt t₁ t₂ * g) = χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ * f g}
  add_mem' {f h} hf hh := by
    refine ⟨?_, fun x t₁ t₂ g ↦ by simp only [Pi.add_apply, hf.2, hh.2]; ring⟩
    obtain ⟨K₁, hc₁, ho₁, h₁⟩ := hf.1
    obtain ⟨K₂, hc₂, ho₂, h₂⟩ := hh.1
    exact ⟨K₁ ⊓ K₂, hc₁.inter_right (Subgroup.isClosed_of_isOpen K₂ ho₂), ho₁.inter ho₂,
      fun g k hk ↦ by simp [h₁ g k hk.1, h₂ g k hk.2]⟩
  zero_mem' := ⟨⟨𝐊[F], (maxCompact_isCompact_isOpen F).1, (maxCompact_isCompact_isOpen F).2,
    fun _ _ _ ↦ rfl⟩, fun _ _ _ _ ↦ by simp⟩
  smul_mem' c {f} hf := by
    refine ⟨?_, fun x t₁ t₂ g ↦ by simp only [Pi.smul_apply, smul_eq_mul, hf.2]; ring⟩
    obtain ⟨K', hc, ho, hK⟩ := hf.1
    exact ⟨K', hc, ho, fun g k hk ↦ by simp [hK g k hk]⟩

/-- The representation `π_χ` of `GL₂(F)` on `I(χ₁, χ₂)` by right translation, `(π_χ(h) f)(g) = f(gh)`
(B-only). The right translate of `f` is right-invariant under `h⁻¹ K' h` when `f` is under `K'`. -/
@[tf_aux "I.smooth.def:right-translation-rep"]
noncomputable def psRep (χ₁ χ₂ : QuasiChar F) :
    Representation ℂ (GL (Fin 2) F) (padicPrincipalSeries χ₁ χ₂) where
  toFun h :=
    { toFun := fun f ↦ ⟨fun g ↦ f.1 (g * h), by
        obtain ⟨K', hc, ho, hK⟩ := f.2.1
        let e : GL (Fin 2) F ≃ₜ GL (Fin 2) F := (Homeomorph.mulLeft h⁻¹).trans (Homeomorph.mulRight h)
        have hset : ((K'.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup _) : Set (GL (Fin 2) F)) = e ⁻¹' K' := by
          ext k; simp [e]
        refine ⟨K'.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_, fun g k hk ↦ ?_⟩
        · rw [hset, e.isCompact_preimage]; exact hc
        · rw [hset]; exact ho.preimage e.continuous
        · have hk' : h⁻¹ * k * h ∈ K' := by simpa [MulAut.conj_apply] using hk
          have := hK (g * h) _ hk'
          rw [show g * h * (h⁻¹ * k * h) = g * k * h by group] at this
          exact this,
        fun x t₁ t₂ g ↦ by simpa [mul_assoc] using f.2.2 x t₁ t₂ (g * h)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := by ext f g; simp
  map_mul' a b := by ext f g; simp [mul_assoc]

theorem psRep_apply (χ₁ χ₂ : QuasiChar F) (h : GL (Fin 2) F) (f : padicPrincipalSeries χ₁ χ₂)
    (g : GL (Fin 2) F) : (psRep χ₁ χ₂ h f).1 g = f.1 (g * h) := rfl

/-- `f(bg) = ψ(b) f(g)` for `b ∈ B(F)` (proof helper). -/
theorem ps_mul_left {χ₁ χ₂ : QuasiChar F} {f : GL (Fin 2) F → ℂ} (hf : f ∈ padicPrincipalSeries χ₁ χ₂)
    (b : borel F) (g : GL (Fin 2) F) : f (b * g) = psChar χ₁ χ₂ b * f g := by
  have := hf.2 (((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 * ((bDiag b 1 : Fˣ) : F)⁻¹)
    (bDiag b 0) (bDiag b 1) g
  rw [← borel_eq_coord b] at this
  rw [this, psChar_eq_coord χ₁ χ₂ b (borel_eq_coord b)]

/-- `f(bk) = ψ(b) f(k)`: an element of `I(χ)` is determined by its restriction to `K` (proof helper). -/
theorem ps_iwasawa {χ₁ χ₂ : QuasiChar F} {f : GL (Fin 2) F → ℂ} (hf : f ∈ padicPrincipalSeries χ₁ χ₂)
    (b : borel F) (k : GL (Fin 2) F) : f (b * k) = psChar χ₁ χ₂ b * f k :=
  ps_mul_left hf b k

/-- Right translation preserves `I(χ)` and is a representation (`psRep`); it is smooth, and `f ↦ f|_K` is
injective on `I(χ)`. -/
@[tf_id "I.smooth.thm:principal-series-smooth"]
theorem principal_series_smooth (χ₁ χ₂ : QuasiChar F) :
    IsSmoothRep (psRep χ₁ χ₂) ∧
      Function.Injective (fun (f : padicPrincipalSeries χ₁ χ₂) (k : 𝐊[F]) ↦ f.1 k) := by
  refine ⟨fun f ↦ ?_, ?_⟩
  · obtain ⟨K', -, ho, hK⟩ := f.2.1
    refine isOpen_iff_mem_nhds.mpr fun h hh ↦ ?_
    have hsub : (fun k ↦ h * k) '' (K' : Set _) ⊆ {g | psRep χ₁ χ₂ g f = f} := by
      rintro _ ⟨k, hk, rfl⟩
      have hh' : psRep χ₁ χ₂ h f = f := hh
      refine Subtype.ext (funext fun g ↦ ?_)
      have e1 := congrArg (fun φ : padicPrincipalSeries χ₁ χ₂ ↦ φ.1 g) hh'
      simp only [psRep_apply] at e1 ⊢
      rw [← mul_assoc, hK _ k hk, e1]
    refine Filter.mem_of_superset ?_ hsub
    have : IsOpen ((fun k ↦ h * k) '' (K' : Set _)) := (Homeomorph.mulLeft h).isOpenMap _ ho
    exact this.mem_nhds ⟨1, K'.one_mem, mul_one h⟩
  · intro f f' h
    refine Subtype.ext (funext fun g ↦ ?_)
    obtain ⟨b, k, hk, rfl⟩ := iwasawa_borel g
    rw [ps_iwasawa f.2, ps_iwasawa f'.2]
    exact congrArg _ (congrFun h ⟨k, hk⟩)

/-! ### Proof helpers for `I.smooth.thm:principal-series-fixed-dimension` -/

/-- The condition "`ψ = 1` on `B ∩ gK′g⁻¹`", in the coordinates of the statement (proof helper). -/
def psCond (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F)) (g : GL (Fin 2) F) : Prop :=
  ∀ (x : F) (t₁ t₂ : Fˣ), g⁻¹ * (upperRightHom x * diagElt t₁ t₂) * g ∈ K' →
    χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ = 1

theorem psCond_iff (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F)) (g : GL (Fin 2) F) :
    psCond χ₁ χ₂ K' g ↔ ∀ b : borel F, g⁻¹ * b * g ∈ K' → psChar χ₁ χ₂ b = 1 := by
  refine ⟨fun h b hb ↦ ?_, fun h x t₁ t₂ hx ↦ ?_⟩
  · rw [psChar_eq_coord χ₁ χ₂ b (borel_eq_coord b)]
    rw [borel_eq_coord b] at hb
    exact h _ _ _ hb
  · rw [← psChar_coord χ₁ χ₂ x]
    exact h _ hx

/-- The condition depends only on the double coset `BgK′` (proof helper). -/
theorem psCond_of_eq (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F)) {g g' : GL (Fin 2) F}
    (b₀ : borel F) {k₀ : GL (Fin 2) F} (hk₀ : k₀ ∈ K') (e : g' = b₀ * g * k₀) (h : psCond χ₁ χ₂ K' g) :
    psCond χ₁ χ₂ K' g' := by
  rw [psCond_iff] at h ⊢
  intro b hb
  have hb' : g⁻¹ * ((b₀⁻¹ * b * b₀ : borel F) : GL (Fin 2) F) * g ∈ K' := by
    have : g⁻¹ * ((b₀⁻¹ * b * b₀ : borel F) : GL (Fin 2) F) * g = k₀ * (g'⁻¹ * b * g') * k₀⁻¹ := by
      rw [e]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]
    exact mul_mem (mul_mem hk₀ hb) (inv_mem hk₀)
  have := h _ hb'
  rw [map_mul, map_mul, mul_comm (psChar χ₁ χ₂ b₀⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    mul_one] at this
  exact this

/-- Well-definedness of the Mackey functions: `h r k = h' r k'` implies `ψ(h) = ψ(h')` (proof helper). -/
theorem psChar_eq_of_cond (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F)) {r : GL (Fin 2) F}
    (hr : psCond χ₁ χ₂ K' r) {h h' : borel F} {k k' : GL (Fin 2) F} (hk : k ∈ K') (hk' : k' ∈ K')
    (e : (h : GL (Fin 2) F) * r * k = h' * r * k') : psChar χ₁ χ₂ h = psChar χ₁ χ₂ h' := by
  rw [psCond_iff] at hr
  have hmem : r⁻¹ * ((h'⁻¹ * h : borel F) : GL (Fin 2) F) * r ∈ K' := by
    have e2 : ((h'⁻¹ * h : borel F) : GL (Fin 2) F) = r * (k' * k⁻¹) * r⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul]
      calc (h : GL (Fin 2) F) = h * r * k * k⁻¹ * r⁻¹ := by group
        _ = h' * r * k' * k⁻¹ * r⁻¹ := by rw [e]
        _ = h' * (r * (k' * k⁻¹) * r⁻¹) := by group
    have : r⁻¹ * ((h'⁻¹ * h : borel F) : GL (Fin 2) F) * r = k' * k⁻¹ := by
      rw [e2]; group
    rw [this]; exact mul_mem hk' (inv_mem hk)
  calc psChar χ₁ χ₂ h = psChar χ₁ χ₂ (h' * (h'⁻¹ * h)) := by rw [mul_inv_cancel_left]
    _ = psChar χ₁ χ₂ h' := by rw [map_mul, hr _ hmem, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNALF F] in
/-- Every `g` is `h r k` for the representative `r` of its double coset `BgK′` (proof helper). -/
theorem exists_dc_decomp (K' : Subgroup (GL (Fin 2) F)) (g : GL (Fin 2) F) :
    ∃ (h : borel F) (k : GL (Fin 2) F), k ∈ K' ∧
      g = h * (DoubleCoset.mk (borel F) K' g).out * k := by
  obtain ⟨h, hh, k, hk, e⟩ := ((DoubleCoset.eq (H := (borel F)) (K := K') (a := (DoubleCoset.mk (borel F) K' g).out) (b := g))).mp
    (DoubleCoset.out_eq' _)
  exact ⟨⟨h, hh⟩, k, hk, e⟩

/-- `f(h r k) = ψ(h) f(r)` for a `K′`-fixed `f` (proof helper). -/
theorem fixed_mul_mem {χ₁ χ₂ : QuasiChar F} {K' : Subgroup (GL (Fin 2) F)}
    {f : padicPrincipalSeries χ₁ χ₂} (hf : f ∈ fixedVectors (psRep χ₁ χ₂) K') (h : borel F) (r : GL (Fin 2) F)
    {k : GL (Fin 2) F} (hk : k ∈ K') : f.1 (h * r * k) = psChar χ₁ χ₂ h * f.1 r := by
  have := congrArg (fun φ : padicPrincipalSeries χ₁ χ₂ ↦ φ.1 (h * r)) (hf k hk)
  simp only [psRep_apply] at this
  rw [this, ps_mul_left f.2]

/-- A `K′`-fixed vector vanishes at `r` unless `ψ = 1` on `B ∩ rK′r⁻¹` (proof helper). -/
theorem fixed_eq_zero_of_not_cond {χ₁ χ₂ : QuasiChar F} {K' : Subgroup (GL (Fin 2) F)}
    {f : padicPrincipalSeries χ₁ χ₂} (hf : f ∈ fixedVectors (psRep χ₁ χ₂) K') {r : GL (Fin 2) F}
    (hr : ¬ psCond χ₁ χ₂ K' r) : f.1 r = 0 := by
  rw [psCond_iff] at hr
  push Not at hr
  obtain ⟨b, hb, hne⟩ := hr
  have e1 := congrArg (fun φ : padicPrincipalSeries χ₁ χ₂ ↦ φ.1 r) (hf _ hb)
  simp only [psRep_apply] at e1
  rw [show r * (r⁻¹ * b * r) = b * r by group, ps_mul_left f.2] at e1
  by_contra h0
  exact hne ((mul_eq_right₀ h0).mp e1)

/-- The Mackey function: on `BrK′` (`r` the representative of `D`), `f(h r k) = c ψ(h)`, else `0`
(proof helper). -/
noncomputable def mackeyFun (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F))
    (D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') (c : ℂ) (g : GL (Fin 2) F) : ℂ :=
  haveI := Classical.propDecidable
  if hg : DoubleCoset.mk (borel F) K' g = D then
    c * psChar χ₁ χ₂ (Classical.choose (hg ▸ exists_dc_decomp K' g))
  else 0

theorem mackeyFun_eq (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F))
    (D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') (hD : psCond χ₁ χ₂ K' D.out) (c : ℂ)
    (h : borel F) {k : GL (Fin 2) F} (hk : k ∈ K') :
    mackeyFun χ₁ χ₂ K' D c (h * D.out * k) = c * psChar χ₁ χ₂ h := by
  have hg : DoubleCoset.mk (borel F) K' ((h : GL (Fin 2) F) * D.out * k) = D := by
    have := ((DoubleCoset.eq (H := (borel F)) (K := K') (a := D.out) (b := ((h : GL (Fin 2) F) * D.out * k)))).mpr ⟨h, h.2, k, hk, rfl⟩
    rw [DoubleCoset.out_eq'] at this
    exact this.symm
  unfold mackeyFun
  rw [dite_eq_left hg]
  congr 1
  have hs := Classical.choose_spec (hg ▸ exists_dc_decomp K' ((h : GL (Fin 2) F) * D.out * k))
  obtain ⟨k', hk', e⟩ := hs
  exact psChar_eq_of_cond χ₁ χ₂ K' hD hk' hk e.symm

theorem mackeyFun_of_ne (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F))
    (D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') (c : ℂ) {g : GL (Fin 2) F}
    (hg : DoubleCoset.mk (borel F) K' g ≠ D) : mackeyFun χ₁ χ₂ K' D c g = 0 := by
  unfold mackeyFun; rw [dite_eq_right hg]

theorem mackeyFun_mem (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F))
    (hc : IsCompact (K' : Set (GL (Fin 2) F))) (ho : IsOpen (K' : Set (GL (Fin 2) F)))
    (D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') (hD : psCond χ₁ χ₂ K' D.out) (c : ℂ) :
    mackeyFun χ₁ χ₂ K' D c ∈ padicPrincipalSeries χ₁ χ₂ ∧
      ∀ g, ∀ k ∈ K', mackeyFun χ₁ χ₂ K' D c (g * k) = mackeyFun χ₁ χ₂ K' D c g := by
  have hright : ∀ g, ∀ k ∈ K', mackeyFun χ₁ χ₂ K' D c (g * k) = mackeyFun χ₁ χ₂ K' D c g := by
    intro g k₁ hk₁
    by_cases hg : DoubleCoset.mk (borel F) K' g = D
    · obtain ⟨h, k, hk, e⟩ := exists_dc_decomp K' g
      rw [hg] at e
      rw [e, mul_assoc _ k, mackeyFun_eq χ₁ χ₂ K' D hD c h (mul_mem hk hk₁), mackeyFun_eq χ₁ χ₂ K' D hD c h hk]
    · have hg' : DoubleCoset.mk (borel F) K' (g * k₁) ≠ D := by
        rwa [show DoubleCoset.mk (borel F) K' (g * k₁) = DoubleCoset.mk (borel F) K' g from
          ((DoubleCoset.eq (H := (borel F)) (K := K'))).mpr ⟨1, one_mem _, k₁⁻¹, inv_mem hk₁, by group⟩]
      rw [mackeyFun_of_ne χ₁ χ₂ K' D c hg, mackeyFun_of_ne χ₁ χ₂ K' D c hg']
  refine ⟨⟨⟨K', hc, ho, hright⟩, fun x t₁ t₂ g ↦ ?_⟩, hright⟩
  set b₀ : borel F := ⟨_, upperRight_diag_mem x t₁ t₂⟩
  have hb₀ : upperRightHom x * diagElt t₁ t₂ = (b₀ : GL (Fin 2) F) := rfl
  rw [hb₀, ← psChar_coord χ₁ χ₂ x t₁ t₂]
  by_cases hg : DoubleCoset.mk (borel F) K' g = D
  · obtain ⟨h, k, hk, e⟩ := exists_dc_decomp K' g
    rw [hg] at e
    rw [e, show (b₀ : GL (Fin 2) F) * (h * D.out * k) = ((b₀ * h : borel F) : GL (Fin 2) F) * D.out * k by
      simp [mul_assoc], mackeyFun_eq χ₁ χ₂ K' D hD c _ hk, mackeyFun_eq χ₁ χ₂ K' D hD c _ hk, map_mul]
    ring
  · have hg' : DoubleCoset.mk (borel F) K' ((b₀ : GL (Fin 2) F) * g) ≠ D := by
      rwa [show DoubleCoset.mk (borel F) K' ((b₀ : GL (Fin 2) F) * g) = DoubleCoset.mk (borel F) K' g from
        ((DoubleCoset.eq (H := (borel F)) (K := K'))).mpr ⟨(b₀ : GL (Fin 2) F)⁻¹, inv_mem b₀.2, 1, one_mem _, by group⟩]
    rw [mackeyFun_of_ne χ₁ χ₂ K' D c hg, mackeyFun_of_ne χ₁ χ₂ K' D c hg', mul_zero]

/-- For every compact open `K′ ≤ GL₂(F)`: `B\G/K′` is finite, `I(χ)^{K′}` is finite-dimensional, and its dimension
is the number of double cosets `BgK′` on which `ψ(n(x) diag(t₁, t₂)) = χ₁(t₁) χ₂(t₂) |t₁/t₂|^{1/2}` is trivial on
`B ∩ gK′g⁻¹`; this condition does not depend on the representative `g`. -/
@[tf_id "I.smooth.thm:principal-series-fixed-dimension"]
theorem principal_series_fixed_dimension (χ₁ χ₂ : QuasiChar F) (K' : Subgroup (GL (Fin 2) F))
    (hc : IsCompact (K' : Set (GL (Fin 2) F))) (ho : IsOpen (K' : Set (GL (Fin 2) F))) :
    Finite (DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') ∧
      FiniteDimensional ℂ (fixedVectors (psRep χ₁ χ₂) K') ∧
      (∀ g g' : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = DoubleCoset.mk (borel F) K' g' →
        ((∀ (x : F) (t₁ t₂ : Fˣ), g⁻¹ * (upperRightHom x * diagElt t₁ t₂) * g ∈ K' →
            χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ = 1) ↔
          (∀ (x : F) (t₁ t₂ : Fˣ), g'⁻¹ * (upperRightHom x * diagElt t₁ t₂) * g' ∈ K' →
            χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ = 1))) ∧
      Module.finrank ℂ (fixedVectors (psRep χ₁ χ₂) K') =
        Nat.card {D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K' //
          ∃ g : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = D ∧
            ∀ (x : F) (t₁ t₂ : Fˣ), g⁻¹ * (upperRightHom x * diagElt t₁ t₂) * g ∈ K' →
              χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ = 1} := by
  change _ ∧ _ ∧ (∀ g g' : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = DoubleCoset.mk (borel F) K' g' →
      (psCond χ₁ χ₂ K' g ↔ psCond χ₁ χ₂ K' g')) ∧
    Module.finrank ℂ (fixedVectors (psRep χ₁ χ₂) K') =
      Nat.card {D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K' //
        ∃ g : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = D ∧ psCond χ₁ χ₂ K' g}
  -- representative independence
  have hrep : ∀ g g' : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = DoubleCoset.mk (borel F) K' g' →
      (psCond χ₁ χ₂ K' g ↔ psCond χ₁ χ₂ K' g') := by
    intro g g' hgg
    have h1 := ((DoubleCoset.eq (H := (borel F)) (K := K') (a := g) (b := g'))).mp hgg
    have h2 := ((DoubleCoset.eq (H := (borel F)) (K := K') (a := g') (b := g))).mp hgg.symm
    obtain ⟨b, hb, k, hk, e⟩ := h1
    obtain ⟨b', hb', k', hk', e'⟩ := h2
    exact ⟨psCond_of_eq χ₁ χ₂ K' ⟨b, hb⟩ hk e, psCond_of_eq χ₁ χ₂ K' ⟨b', hb'⟩ hk' e'⟩
  -- finiteness of `B\G/K′`: `K/(K ∩ K′)` is finite and surjects onto it
  have hfin : Finite (DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K') := by
    have hKc := maxCompact_isCompact_isOpen F
    have : CompactSpace 𝐊[F] := isCompact_iff_compactSpace.mp hKc.1
    have : Finite (𝐊[F] ⧸ K'.subgroupOf 𝐊[F]) :=
      Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
    refine Finite.of_surjective (fun Q : 𝐊[F] ⧸ K'.subgroupOf 𝐊[F] ↦
      DoubleCoset.mk (borel F) K' ((Q.out : 𝐊[F]) : GL (Fin 2) F)) fun D ↦ ?_
    obtain ⟨b, k, hk, e⟩ := iwasawa_borel D.out
    refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
    obtain ⟨h, he⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf 𝐊[F]) (⟨k, hk⟩ : 𝐊[F])
    beta_reduce
    rw [he, ← (DoubleCoset.out_eq' (H := (borel F)) (K := K') (q := D)), DoubleCoset.eq]
    refine ⟨b, b.2, (((h : K'.subgroupOf 𝐊[F]) : 𝐊[F]) : GL (Fin 2) F)⁻¹, inv_mem h.2, ?_⟩
    rw [e]; simp only [Subgroup.coe_mul]; group
  set S := {D : DoubleCoset.Quotient (borel F : Set (GL (Fin 2) F)) K' //
    ∃ g : GL (Fin 2) F, DoubleCoset.mk (borel F) K' g = D ∧ psCond χ₁ χ₂ K' g}
  have hS : ∀ D : S, psCond χ₁ χ₂ K' D.1.out := by
    rintro ⟨D, g, rfl, hg⟩
    exact (hrep g _ (DoubleCoset.out_eq' _).symm).mp hg
  -- the evaluation map `f ↦ (f(r_D))_D`
  let Φ : fixedVectors (psRep χ₁ χ₂) K' →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun f D ↦ (f : padicPrincipalSeries χ₁ χ₂).1 D.1.out
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hinj : Function.Injective Φ := by
    intro f f' hff
    have hf0 : ∀ D : S, (f : padicPrincipalSeries χ₁ χ₂).1 D.1.out = (f' : padicPrincipalSeries χ₁ χ₂).1 D.1.out :=
      fun D ↦ congrFun hff D
    refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    obtain ⟨h, k, hk, e⟩ := exists_dc_decomp K' g
    show (f : padicPrincipalSeries χ₁ χ₂).1 g = (f' : padicPrincipalSeries χ₁ χ₂).1 g
    rw [e, fixed_mul_mem f.2 h _ hk, fixed_mul_mem f'.2 h _ hk]
    by_cases hc : psCond χ₁ χ₂ K' (DoubleCoset.mk (borel F) K' g).out
    · rw [hf0 ⟨_, _, DoubleCoset.out_eq' _, hc⟩]
    · rw [fixed_eq_zero_of_not_cond f.2 hc, fixed_eq_zero_of_not_cond f'.2 hc]
  have hsurj : Function.Surjective Φ := by
    intro c
    have : Finite S := Subtype.finite
    have : Fintype S := Fintype.ofFinite S
    let φ : GL (Fin 2) F → ℂ := fun g ↦ ∑ D : S, mackeyFun χ₁ χ₂ K' D.1 (c D) g
    have hmem : ∀ D : S, mackeyFun χ₁ χ₂ K' D.1 (c D) ∈ padicPrincipalSeries χ₁ χ₂ ∧
        ∀ g, ∀ k ∈ K', mackeyFun χ₁ χ₂ K' D.1 (c D) (g * k) = mackeyFun χ₁ χ₂ K' D.1 (c D) g :=
      fun D ↦ mackeyFun_mem χ₁ χ₂ K' hc ho D.1 (hS D) (c D)
    have hφ : φ ∈ padicPrincipalSeries χ₁ χ₂ := by
      have : φ = ∑ D : S, mackeyFun χ₁ χ₂ K' D.1 (c D) := by funext g; simp [φ]
      rw [this]
      exact Submodule.sum_mem _ fun D _ ↦ (hmem D).1
    refine ⟨⟨⟨φ, hφ⟩, fun k hk ↦ Subtype.ext (funext fun g ↦ ?_)⟩, funext fun D ↦ ?_⟩
    · rw [psRep_apply]
      exact Finset.sum_congr rfl fun D _ ↦ (hmem D).2 g k hk
    · change ∑ D' : S, mackeyFun χ₁ χ₂ K' D'.1 (c D') D.1.out = c D
      rw [Finset.sum_eq_single D]
      · have := mackeyFun_eq χ₁ χ₂ K' D.1 (hS D) (c D) 1 (one_mem K')
        simpa using this
      · intro D' _ hD'
        refine mackeyFun_of_ne χ₁ χ₂ K' D'.1 _ ?_
        rw [DoubleCoset.out_eq']
        exact fun h ↦ hD' (Subtype.ext h).symm
      · intro h; exact absurd (Finset.mem_univ D) h
  have e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have : Finite S := Subtype.finite
  have : Fintype S := Fintype.ofFinite S
  have : FiniteDimensional ℂ (fixedVectors (psRep χ₁ χ₂) K') := LinearEquiv.finiteDimensional e.symm
  refine ⟨hfin, inferInstance, hrep, ?_⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- `π_χ` is admissible. -/
@[tf_id "I.smooth.cor:principal-series-admissible"]
theorem principal_series_admissible (χ₁ χ₂ : QuasiChar F) : IsAdmissibleRep (psRep χ₁ χ₂) :=
  ⟨(principal_series_smooth χ₁ χ₂).1, fun K' hc ho ↦ (principal_series_fixed_dimension χ₁ χ₂ K' hc ho).2.1⟩

/-! ## §2 The spherical vector -/

/-- The spherical vector `f°_χ(n(x) diag(t₁, t₂) k) = χ₁(t₁) χ₂(t₂) |t₁/t₂|^{1/2}` (`k ∈ K`). Lean evaluates it at a
chosen Iwasawa decomposition `g = b k` (`I.decomp.thm:iwasawa-local`, `b` upper triangular with diagonal
`(t₁, t₂) = (b₀₀, b₁₁)`); for unramified `χ₁, χ₂` the value does not depend on the choice
(`I.smooth.lem:spherical-vector-spec`). -/
@[tf_id "I.smooth.def:spherical-vector"]
noncomputable def sphericalVector (χ₁ χ₂ : QuasiChar F) (g : GL (Fin 2) F) : ℂ :=
  let b : borel F := ⟨Classical.choose (iwasawa_local F g),
    (Classical.choose_spec (Classical.choose_spec (iwasawa_local F g))).2.1⟩
  χ₁ (borel_diag_isUnit b 0).unit * χ₂ (borel_diag_isUnit b 1).unit *
    deltaHalf (borel_diag_isUnit b 0).unit (borel_diag_isUnit b 1).unit

theorem sphericalVector_eq_psChar (χ₁ χ₂ : QuasiChar F) (g : GL (Fin 2) F) :
    sphericalVector χ₁ χ₂ g = psChar χ₁ χ₂ ⟨Classical.choose (iwasawa_local F g),
      (Classical.choose_spec (Classical.choose_spec (iwasawa_local F g))).2.1⟩ := rfl

theorem iwasawa_choose_spec (g : GL (Fin 2) F) :
    ∃ k ∈ 𝐊[F], g = Classical.choose (iwasawa_local F g) * k :=
  ⟨_, (Classical.choose_spec (Classical.choose_spec (iwasawa_local F g))).1,
    (Classical.choose_spec (Classical.choose_spec (iwasawa_local F g))).2.2⟩

/-- For unramified `χ₁, χ₂`, `bk = b'k'` with `k, k' ∈ K` implies `ψ(b) = ψ(b')` (proof helper). -/
theorem psChar_eq_of_mul_eq (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {b b' : borel F} {k k' : GL (Fin 2) F} (hk : k ∈ 𝐊[F]) (hk' : k' ∈ 𝐊[F])
    (e : (b : GL (Fin 2) F) * k = b' * k') : psChar χ₁ χ₂ b = psChar χ₁ χ₂ b' := by
  have hmem : ((b'⁻¹ * b : borel F) : GL (Fin 2) F) ∈ 𝐊[F] := by
    have : ((b'⁻¹ * b : borel F) : GL (Fin 2) F) = k' * k⁻¹ := by
      calc ((b'⁻¹ * b : borel F) : GL (Fin 2) F) = (b' : GL (Fin 2) F)⁻¹ * (b * k) * k⁻¹ := by
            simp [mul_assoc]
        _ = (b' : GL (Fin 2) F)⁻¹ * (b' * k') * k⁻¹ := by rw [e]
        _ = k' * k⁻¹ := by group
    rw [this]; exact mul_mem hk' (inv_mem hk)
  calc psChar χ₁ χ₂ b = psChar χ₁ χ₂ (b' * (b'⁻¹ * b)) := by rw [mul_inv_cancel_left]
    _ = psChar χ₁ χ₂ b' := by rw [map_mul, psChar_eq_one_of_mem_K χ₁ χ₂ h₁ h₂ _ hmem, mul_one]

/-- `f°_χ(bk) = ψ(b)` for unramified `χ` (proof helper). -/
theorem sphericalVector_mul (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    (b : borel F) (k : GL (Fin 2) F) (hk : k ∈ 𝐊[F]) : sphericalVector χ₁ χ₂ (b * k) = psChar χ₁ χ₂ b := by
  rw [sphericalVector_eq_psChar]
  obtain ⟨k', hk', e⟩ := iwasawa_choose_spec ((b : GL (Fin 2) F) * k)
  exact (psChar_eq_of_mul_eq χ₁ χ₂ h₁ h₂ hk hk' e).symm

/-- A `K`-fixed `f ∈ I(χ)` satisfies `f(bk) = ψ(b) f(1)` (proof helper). -/
theorem fixed_apply {χ₁ χ₂ : QuasiChar F} {f : padicPrincipalSeries χ₁ χ₂}
    (hf : f ∈ fixedVectors (psRep χ₁ χ₂) 𝐊[F]) (b : borel F) {k : GL (Fin 2) F} (hk : k ∈ 𝐊[F]) :
    f.1 (b * k) = psChar χ₁ χ₂ b * f.1 1 := by
  rw [ps_iwasawa f.2]
  have := congrArg (fun φ : padicPrincipalSeries χ₁ χ₂ ↦ φ.1 1) (hf k hk)
  simp only [psRep_apply, one_mul] at this
  rw [this]

/-- For unramified `χ₁, χ₂`, `f°_χ(n(x) diag(t₁, t₂) k) = χ₁(t₁) χ₂(t₂) |t₁/t₂|^{1/2}` for all `x`, `t₁`, `t₂` and
`k ∈ K` (B-only: the well-definedness claim of `I.smooth.def:spherical-vector`). -/
@[tf_aux "I.smooth.lem:spherical-vector-spec"]
theorem sphericalVector_spec (χ₁ χ₂ : QuasiChar F) (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    (x : F) (t₁ t₂ : Fˣ) (k : GL (Fin 2) F) (hk : k ∈ 𝐊[F]) :
    sphericalVector χ₁ χ₂ (upperRightHom x * diagElt t₁ t₂ * k) = χ₁ t₁ * χ₂ t₂ * deltaHalf t₁ t₂ := by
  rw [← psChar_coord χ₁ χ₂ x t₁ t₂]
  exact sphericalVector_mul χ₁ χ₂ h₁ h₂ ⟨_, upperRight_diag_mem x t₁ t₂⟩ k hk

/-- (a) For unramified `χ₁, χ₂`: `f°_χ ∈ I(χ)`, `f°_χ` is right `K`-invariant, `f°_χ(1) = 1`, every `K`-fixed vector
of `I(χ)` is a multiple of `f°_χ`, and `dim I(χ)^K = 1`. (b) If `χ₁` or `χ₂` is ramified, `I(χ)^K = 0`. -/
@[tf_id "I.smooth.thm:principal-series-spherical"]
theorem principal_series_spherical (χ₁ χ₂ : QuasiChar F) :
    (χ₁.IsUnramified → χ₂.IsUnramified →
      sphericalVector χ₁ χ₂ ∈ padicPrincipalSeries χ₁ χ₂ ∧
        (∀ g, ∀ k ∈ 𝐊[F], sphericalVector χ₁ χ₂ (g * k) = sphericalVector χ₁ χ₂ g) ∧
        sphericalVector χ₁ χ₂ 1 = 1 ∧
        (∀ f ∈ fixedVectors (psRep χ₁ χ₂) 𝐊[F], ∃ c : ℂ, f.1 = c • sphericalVector χ₁ χ₂) ∧
        Module.finrank ℂ (fixedVectors (psRep χ₁ χ₂) 𝐊[F]) = 1) ∧
      (¬ (χ₁.IsUnramified ∧ χ₂.IsUnramified) → fixedVectors (psRep χ₁ χ₂) 𝐊[F] = ⊥) := by
  have hKc := maxCompact_isCompact_isOpen F
  refine ⟨fun h₁ h₂ ↦ ?_, fun hram ↦ ?_⟩
  · have hK : ∀ g, ∀ k ∈ 𝐊[F], sphericalVector χ₁ χ₂ (g * k) = sphericalVector χ₁ χ₂ g := by
      intro g k hk
      obtain ⟨b, k₀, hk₀, rfl⟩ := iwasawa_borel g
      rw [mul_assoc, sphericalVector_mul χ₁ χ₂ h₁ h₂ _ _ (mul_mem hk₀ hk),
        sphericalVector_mul χ₁ χ₂ h₁ h₂ _ _ hk₀]
    have hmem : sphericalVector χ₁ χ₂ ∈ padicPrincipalSeries χ₁ χ₂ := by
      refine ⟨⟨𝐊[F], hKc.1, hKc.2, hK⟩, fun x t₁ t₂ g ↦ ?_⟩
      obtain ⟨b, k₀, hk₀, rfl⟩ := iwasawa_borel g
      have e : upperRightHom x * diagElt t₁ t₂ * ((b : GL (Fin 2) F) * k₀) =
          ((⟨_, upperRight_diag_mem x t₁ t₂⟩ * b : borel F) : GL (Fin 2) F) * k₀ := by
        simp [mul_assoc]
      rw [e, sphericalVector_mul χ₁ χ₂ h₁ h₂ _ _ hk₀, sphericalVector_mul χ₁ χ₂ h₁ h₂ _ _ hk₀, map_mul,
        psChar_coord]
    have h1 : sphericalVector χ₁ χ₂ 1 = 1 := by
      have := sphericalVector_mul χ₁ χ₂ h₁ h₂ 1 1 (one_mem _)
      simpa using this
    have hc : ∀ f ∈ fixedVectors (psRep χ₁ χ₂) 𝐊[F], f.1 = f.1 1 • sphericalVector χ₁ χ₂ := by
      intro f hf
      funext g
      obtain ⟨b, k, hk, rfl⟩ := iwasawa_borel g
      rw [fixed_apply hf b hk, Pi.smul_apply, smul_eq_mul, sphericalVector_mul χ₁ χ₂ h₁ h₂ _ _ hk, mul_comm]
    refine ⟨hmem, hK, h1, fun f hf ↦ ⟨_, hc f hf⟩, ?_⟩
    let v : fixedVectors (psRep χ₁ χ₂) 𝐊[F] :=
      ⟨⟨sphericalVector χ₁ χ₂, hmem⟩, fun k hk ↦ Subtype.ext (funext fun g ↦ by rw [psRep_apply]; exact hK g k hk)⟩
    have hv : v ≠ 0 := by
      intro h
      have := congrArg (fun w : fixedVectors (psRep χ₁ χ₂) 𝐊[F] ↦ (w : padicPrincipalSeries χ₁ χ₂).1 1) h
      simp only [v, h1] at this
      exact one_ne_zero this
    refine (finrank_eq_one_iff_of_nonzero' v hv).2 fun w ↦ ⟨(w : padicPrincipalSeries χ₁ χ₂).1 1, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    exact (hc _ w.2).symm
  · rw [Submodule.eq_bot_iff]
    intro f hf
    -- `f(1) = f(diag(t₁, t₂)) = χ₁(t₁) χ₂(t₂) f(1)` for units `t₁, t₂` of `𝒪`
    have hd : ∀ u₁ u₂ : 𝒪[F]ˣ, f.1 1 = χ₁ (Units.map (𝒪[F]).subtype.toMonoidHom u₁) *
        χ₂ (Units.map (𝒪[F]).subtype.toMonoidHom u₂) * f.1 1 := by
      intro u₁ u₂
      have hmK : upperRightHom (0 : F) * diagElt (Units.map (𝒪[F]).subtype.toMonoidHom u₁)
          (Units.map (𝒪[F]).subtype.toMonoidHom u₂) ∈ 𝐊[F] :=
        (borelCoord_mem_K_iff F (0 : F) _ _).mpr ⟨Subring.zero_mem _, ⟨u₁, rfl⟩, ⟨u₂, rfl⟩⟩
      have e1 := congrArg (fun φ : padicPrincipalSeries χ₁ χ₂ ↦ φ.1 1) (hf _ hmK)
      simp only [psRep_apply, one_mul] at e1
      have e2 := f.2.2 0 (Units.map (𝒪[F]).subtype.toMonoidHom u₁) (Units.map (𝒪[F]).subtype.toMonoidHom u₂) 1
      rw [mul_one, e1, deltaHalf_units, mul_one] at e2
      exact e2
    have h1 : f.1 1 = 0 := by
      by_contra hne
      refine hram ⟨fun u ↦ ?_, fun u ↦ ?_⟩
      · have := hd u 1
        rw [map_one] at this
        change f.1 1 = χ₁ _ * ((χ₂.1 1 : ℂˣ) : ℂ) * f.1 1 at this
        rw [map_one, Units.val_one, mul_one] at this
        exact (mul_eq_right₀ hne).mp this.symm
      · have := hd 1 u
        rw [map_one] at this
        change f.1 1 = ((χ₁.1 1 : ℂˣ) : ℂ) * χ₂ _ * f.1 1 at this
        rw [map_one, Units.val_one, one_mul] at this
        exact (mul_eq_right₀ hne).mp this.symm
    refine Subtype.ext (funext fun g ↦ ?_)
    obtain ⟨b, k, hk, rfl⟩ := iwasawa_borel g
    rw [fixed_apply hf b hk, h1, mul_zero]
    rfl

end GL2TF.Local
