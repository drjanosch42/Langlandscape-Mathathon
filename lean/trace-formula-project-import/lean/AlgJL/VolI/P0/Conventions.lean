import AlgJL.Meta.Tag
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.Integers

/-!
# Conventions: subgroups of GL₂ and the maximal compact subgroups (M1 U1, M2 U1)

Lean counterpart of `vol1/ch-0-01-conventions.tex` (§ "The algebraic groups": B, T, N, w for a commutative ring;
§ "Maximal compact subgroups": K(R) ⊆ GL₂(F) and K_∞ = O(2), the rotations k_θ). `n(x)` is Mathlib's
`Matrix.GeneralLinearGroup.upperRightHom`. For K(R) the file is generic in the ring
homomorphism `ι : R →+* F`, so this file does not import `LocalField`. The notation `𝐊[F]` for
`K_F = K(𝒪_F)` is a notation, not a separate definition (as in A). Owner: L1.
-/

open Matrix

namespace GL2TF

/-- `K(R) ⊆ GL₂(F)`: the image of `GL₂(R) → GL₂(F)`, obtained by applying `ι` to the matrix entries. -/
@[tf_id "I.conv.def:max-compact-local"]
def maxCompact {R F : Type*} [CommRing R] [Field F] (ι : R →+* F) : Subgroup (GL (Fin 2) F) :=
  (Matrix.GeneralLinearGroup.map ι).range

/-- `K_F = K(𝒪_F)` for the inclusion `𝒪_F ⊆ F` of the valuation ring of a valued field. -/
scoped notation "𝐊[" F "]" =>
  GL2TF.maxCompact (Subring.subtype (Valuation.integer (ValuativeRel.valuation F)))

/-- Membership in `K(R)` for injective `ι`: (i) `g ∈ K(R)`; (ii) the entries of `g` lie in `ι(R)` and
`det g ∈ ι(Rˣ)`; (iii) the entries of `g` and of `g⁻¹` lie in `ι(R)`. -/
@[tf_id "I.conv.lem:max-compact-local-mem"]
theorem mem_maxCompact_tfae {R F : Type*} [CommRing R] [Field F] (ι : R →+* F)
    (hι : Function.Injective ι) (g : GL (Fin 2) F) :
    List.TFAE
      [g ∈ maxCompact ι,
       (∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ Set.range ι) ∧
         ∃ u : Rˣ, (g : Matrix (Fin 2) (Fin 2) F).det = ι u,
       (∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ Set.range ι) ∧
         ∀ i j, ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ Set.range ι] := by
  have hιM : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) R ↦ A.map ι) :=
    fun A B h ↦ Matrix.ext fun i j ↦ hι (congrFun (congrFun h i) j)
  tfae_have 1 → 3 := by
    rintro ⟨A, rfl⟩
    refine ⟨fun i j ↦ ⟨A i j, rfl⟩, fun i j ↦ ⟨(A⁻¹ : GL (Fin 2) R) i j, ?_⟩⟩
    rw [← Matrix.GeneralLinearGroup.map_inv]
    rfl
  tfae_have 3 → 2 := by
    rintro ⟨h, h'⟩
    choose a hA using h
    choose b hB using h'
    set A : Matrix (Fin 2) (Fin 2) R := Matrix.of a
    set B : Matrix (Fin 2) (Fin 2) R := Matrix.of b
    have hAB : A * B = 1 := by
      apply hιM
      have hg : A.map ι = g := Matrix.ext hA
      have hg' : B.map ι = ((g⁻¹ : GL (Fin 2) F) : Matrix _ _ F) :=
        Matrix.ext hB
      simp only [Matrix.map_mul, hg, hg', Matrix.map_one _ (map_zero ι) (map_one ι)]
      exact_mod_cast g.mul_inv
    have hdet : IsUnit A.det :=
      IsUnit.of_mul_eq_one B.det
        (by rw [← Matrix.det_mul, hAB, Matrix.det_one])
    refine ⟨fun i j ↦ ⟨a i j, hA i j⟩, hdet.unit, ?_⟩
    rw [IsUnit.unit_spec, RingHom.map_det]
    congr 1
    exact (Matrix.ext hA).symm
  tfae_have 2 → 1 := by
    rintro ⟨h, u, hu⟩
    choose a hA using h
    set A : Matrix (Fin 2) (Fin 2) R := Matrix.of a
    have hg : A.map ι = g := Matrix.ext hA
    have hdet : A.det = u := by
      apply hι
      rw [RingHom.map_det]
      exact (congrArg Matrix.det hg).trans hu
    refine ⟨Matrix.nonsingInvUnit A (hdet ▸ u.isUnit), Units.ext ?_⟩
    exact hg
  tfae_finish

section Algebraic

variable (R : Type*) [CommRing R]

/-- The Borel subgroup `B(R) ≤ GL₂(R)`: upper triangular matrices, `g₁₀ = 0`. -/
@[tf_id "I.conv.def:borel"]
def borel : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, mul_apply, Fin.sum_univ_two] at *
    rw [hg, hh]; ring
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_def, adjugate_fin_two]
    simp [hg]

/-- The diagonal torus `T(R) ≤ GL₂(R)`: `g₀₁ = g₁₀ = 0`. -/
@[tf_id "I.conv.def:torus"]
def torus : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, mul_apply, Fin.sum_univ_two] at *
    rw [hg.1, hg.2, hh.1, hh.2]; constructor <;> ring
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_def, adjugate_fin_two]
    simp [hg.1, hg.2]

/-- The diagonal element `diag(t₁, t₂) ∈ T(R)` for units `t₁, t₂`. -/
@[tf_aux "I.conv.def:diag-element"]
def diagElt {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) : GL (Fin 2) R :=
  ⟨!![(t₁ : R), 0; 0, (t₂ : R)], !![((t₁⁻¹ : Rˣ) : R), 0; 0, ((t₂⁻¹ : Rˣ) : R)],
    by simp [one_fin_two], by simp [one_fin_two]⟩

/-- `n(x) = (1 x; 0 1)`: Mathlib's `Matrix.GeneralLinearGroup.upperRightHom`, an additive character
`R → GL₂(R)`. The unipotent subgroup `N(R) = {n(x) : x ∈ R}`. -/
@[tf_id "I.conv.def:unipotent"]
def unipotent : Subgroup (GL (Fin 2) R) where
  carrier := Set.range (GeneralLinearGroup.upperRightHom (R := R))
  one_mem' := ⟨0, AddChar.map_zero_eq_one _⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, AddChar.map_add_eq_mul _ x y⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, AddChar.map_neg_eq_inv _ x⟩

/-- `diag(1, 1) = 1` and `diag(t₁t₁', t₂t₂') = diag(t₁, t₂) diag(t₁', t₂')`. -/
@[tf_aux "I.conv.lem:diag-elt-hom"]
theorem diagElt_hom {R : Type*} [CommRing R] :
    diagElt (1 : Rˣ) 1 = 1 ∧ ∀ t₁ t₂ s₁ s₂ : Rˣ, diagElt (t₁ * s₁) (t₂ * s₂) = diagElt t₁ t₂ * diagElt s₁ s₂ := by
  refine ⟨?_, fun t₁ t₂ s₁ s₂ ↦ ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [diagElt, Matrix.mul_apply]

/-- `(t₁, t₂) ↦ diag(t₁, t₂)`, a homomorphism `R^× × R^× → GL₂(R)` with image `T(R)`. -/
@[tf_aux "I.conv.def:diag-hom"]
def diagHom (R : Type*) [CommRing R] : Rˣ × Rˣ →* GL (Fin 2) R where
  toFun t := diagElt t.1 t.2
  map_one' := diagElt_hom.1
  map_mul' t s := diagElt_hom.2 t.1 t.2 s.1 s.2

/-- The Weyl element `w = (0 1; −1 0) ∈ GL₂(R)`. -/
@[tf_id "I.conv.def:weyl-element"]
def weylElement : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [one_fin_two], by simp [one_fin_two]⟩

end Algebraic

section Structure

/-! ### Structure of `GL₂` (M3, unit U1) -/

/-- The homomorphism `f_* : GL₂(R) → GL₂(R')` induced by a ring homomorphism `f : R → R'` (entrywise), Mathlib's
`Matrix.GeneralLinearGroup.map`. -/
@[tf_id "I.conv.def:gl2"]
def gl2Map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') : GL (Fin 2) R →* GL (Fin 2) R' :=
  Matrix.GeneralLinearGroup.map f

/-- The centre `Z(R) ≤ GL₂(R)`: the scalar matrices `z · 1`, `z ∈ Rˣ` (the image of `Rˣ` under `z ↦ z · 1`). -/
@[tf_id "I.conv.def:center"]
def center (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) :=
  (Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom).range

/-- The set `{g : g₀₁ = 0}` of lower triangular matrices contains `1` and is closed under products and inverses. -/
@[tf_aux "I.conv.lem:opposite-borel-subgroup"]
theorem oppositeBorel_isSubgroup (R : Type*) [CommRing R] :
    (1 : GL (Fin 2) R) ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} ∧
      (∀ {g h : GL (Fin 2) R}, g ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} →
        h ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} →
        g * h ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0}) ∧
      ∀ {g : GL (Fin 2) R}, g ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} →
        g⁻¹ ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} := by
  refine ⟨by simp, fun {g h} hg hh ↦ ?_, fun {g} hg ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, Units.val_mul, mul_apply, Fin.sum_univ_two] at *
    rw [hg, hh]; ring
  · simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_def, adjugate_fin_two]
    simp [hg]

/-- The opposite Borel subgroup `B̄(R) ≤ GL₂(R)`: lower triangular matrices, `g₀₁ = 0`. -/
@[tf_id "I.conv.def:opposite-borel"]
def oppositeBorel (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0}
  one_mem' := (oppositeBorel_isSubgroup R).1
  mul_mem' := (oppositeBorel_isSubgroup R).2.1
  inv_mem' := (oppositeBorel_isSubgroup R).2.2

/-- `(1 0; x 1)` and `(1 0; −x 1)` are mutually inverse. -/
@[tf_aux "I.conv.lem:opposite-unipotent-elt-inv"]
theorem oppositeUnipotentElt_inv {R : Type*} [CommRing R] (x : R) :
    !![(1 : R), 0; x, 1] * !![(1 : R), 0; -x, 1] = 1 ∧ !![(1 : R), 0; -x, 1] * !![(1 : R), 0; x, 1] = 1 := by
  constructor <;> simp [one_fin_two]

/-- `n̄(x) = (1 0; x 1) ∈ GL₂(R)`. -/
@[tf_aux "I.conv.def:opposite-unipotent-elt"]
def oppositeUnipotentElt {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], (oppositeUnipotentElt_inv x).1, (oppositeUnipotentElt_inv x).2⟩

/-- `n̄(0) = 1` and `n̄(x + y) = n̄(x) n̄(y)`. -/
@[tf_aux "I.conv.lem:opposite-unipotent-elt-hom"]
theorem oppositeUnipotentElt_hom {R : Type*} [CommRing R] :
    oppositeUnipotentElt (0 : R) = 1 ∧
      ∀ x y : R, oppositeUnipotentElt (x + y) = oppositeUnipotentElt x * oppositeUnipotentElt y := by
  refine ⟨?_, fun x y ↦ ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [oppositeUnipotentElt, Matrix.mul_apply]

/-- `n̄ : R → GL₂(R)` as an additive character (a homomorphism from the additive group of `R`). -/
@[tf_aux "I.conv.def:opposite-unipotent-hom"]
def oppositeUnipotentHom {R : Type*} [CommRing R] : AddChar R (GL (Fin 2) R) where
  toFun := oppositeUnipotentElt
  map_zero_eq_one' := oppositeUnipotentElt_hom.1
  map_add_eq_mul' := oppositeUnipotentElt_hom.2

/-- The opposite unipotent subgroup `N̄(R) = {n̄(x) : x ∈ R}`, the image of `n̄`. -/
@[tf_aux "I.conv.def:opposite-unipotent"]
def oppositeUnipotent (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) :=
  (oppositeUnipotentHom (R := R)).toMonoidHom.range

private theorem mat_ext_two {R : Type*} {A B : Matrix (Fin 2) (Fin 2) R}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j; fin_cases i <;> fin_cases j <;> assumption

private theorem gl_ext_two {R : Type*} [CommRing R] {g h : GL (Fin 2) R}
    (h00 : (g : Matrix (Fin 2) (Fin 2) R) 0 0 = (h : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) R) 0 1 = (h : Matrix (Fin 2) (Fin 2) R) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = (h : Matrix (Fin 2) (Fin 2) R) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) R) 1 1 = (h : Matrix (Fin 2) (Fin 2) R) 1 1) : g = h :=
  Units.ext (mat_ext_two h00 h01 h10 h11)

private theorem det_gl_two {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0) := by
  rw [← det_fin_two]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit

/-- A torus element is `diag(t₁, t₂)`. -/
private theorem exists_diagElt_of_mem_torus {R : Type*} [CommRing R] {g : GL (Fin 2) R} (hg : g ∈ torus R) :
    ∃ t₁ t₂ : Rˣ, g = diagElt t₁ t₂ := by
  obtain ⟨h01, h10⟩ := hg
  have hd := det_gl_two g
  rw [h01, h10, zero_mul, sub_zero] at hd
  refine ⟨(isUnit_of_mul_isUnit_left hd).unit, (isUnit_of_mul_isUnit_right hd).unit, ?_⟩
  apply gl_ext_two <;> simp [diagElt, h01, h10]

private theorem diagElt_mem_torus' {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) : diagElt t₁ t₂ ∈ torus R :=
  ⟨by simp [diagElt], by simp [diagElt]⟩

/-- `n̄` is injective, `B̄(R)` contains `N̄(R)` (the claims of `I.conv.def:opposite-borel`). -/
@[tf_aux "I.conv.lem:opposite-unipotent-hom-injective"]
theorem oppositeUnipotentHom_injective (R : Type*) [CommRing R] :
    Function.Injective (oppositeUnipotentHom (R := R)) ∧ oppositeUnipotent R ≤ oppositeBorel R := by
  refine ⟨fun x y h ↦ ?_, ?_⟩
  · have := congrArg (fun g : GL (Fin 2) R ↦ (g : Matrix (Fin 2) (Fin 2) R) 1 0) h
    simpa [oppositeUnipotentHom, oppositeUnipotentElt] using this
  · rintro _ ⟨x, rfl⟩
    show ((oppositeUnipotentHom x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0
    simp [oppositeUnipotentHom, oppositeUnipotentElt]

/-- Functoriality: `f_*` maps `B, T, N, Z, B̄, N̄` of `R` into those of `R'`; on coordinates
`f_*(n(x)) = n(f x)`, `f_*(n̄(x)) = n̄(f x)`, `f_*(diag(t₁, t₂)) = diag(f t₁, f t₂)`. -/
@[tf_id "I.conv.lem:subgroups-functorial"]
theorem subgroups_functorial {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') :
    (borel R).map (gl2Map f) ≤ borel R' ∧ (torus R).map (gl2Map f) ≤ torus R' ∧
      (unipotent R).map (gl2Map f) ≤ unipotent R' ∧ (center R).map (gl2Map f) ≤ center R' ∧
      (oppositeBorel R).map (gl2Map f) ≤ oppositeBorel R' ∧
      (oppositeUnipotent R).map (gl2Map f) ≤ oppositeUnipotent R' ∧
      (∀ x : R, gl2Map f (GeneralLinearGroup.upperRightHom x) = GeneralLinearGroup.upperRightHom (f x)) ∧
      (∀ x : R, gl2Map f (oppositeUnipotentHom x) = oppositeUnipotentHom (f x)) ∧
      ∀ t₁ t₂ : Rˣ, gl2Map f (diagElt t₁ t₂) = diagElt (Units.map f.toMonoidHom t₁) (Units.map f.toMonoidHom t₂) := by
  have hN : ∀ x : R, gl2Map f (GeneralLinearGroup.upperRightHom x) = GeneralLinearGroup.upperRightHom (f x) :=
    fun x ↦ by apply gl_ext_two <;> simp [gl2Map]
  have hN' : ∀ x : R, gl2Map f (oppositeUnipotentHom x) = oppositeUnipotentHom (f x) :=
    fun x ↦ by apply gl_ext_two <;> simp [gl2Map, oppositeUnipotentHom, oppositeUnipotentElt]
  have hT : ∀ t₁ t₂ : Rˣ, gl2Map f (diagElt t₁ t₂) =
      diagElt (Units.map f.toMonoidHom t₁) (Units.map f.toMonoidHom t₂) :=
    fun t₁ t₂ ↦ by apply gl_ext_two <;> simp [gl2Map, diagElt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hN, hN', hT⟩
  · rintro _ ⟨g, hg, rfl⟩
    show (gl2Map f g : Matrix (Fin 2) (Fin 2) R') 1 0 = 0
    simp only [gl2Map, GeneralLinearGroup.map_apply]
    rw [show (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 from hg, map_zero]
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩ <;> simp only [gl2Map, GeneralLinearGroup.map_apply] <;> simp [h1, h2]
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (hN x).symm⟩
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨Units.map f.toMonoidHom z, ?_⟩
    apply Units.ext
    ext i j
    simp [gl2Map, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rintro _ ⟨g, hg, rfl⟩
    show (gl2Map f g : Matrix (Fin 2) (Fin 2) R') 0 1 = 0
    simp only [gl2Map, GeneralLinearGroup.map_apply]
    rw [show (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 from hg, map_zero]
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (hN' x).symm⟩

/-- `diag(t₁, t₂) n(x) diag(t₁, t₂)⁻¹ = n(t₁ t₂⁻¹ x)`; in particular `t N(R) t⁻¹ = N(R)` for `t ∈ T(R)`. -/
@[tf_id "I.conv.lem:torus-normalizes-unipotent"]
theorem torus_normalizes_unipotent (R : Type*) [CommRing R] :
    (∀ (t₁ t₂ : Rˣ) (x : R), diagElt t₁ t₂ * GeneralLinearGroup.upperRightHom x * (diagElt t₁ t₂)⁻¹ =
        GeneralLinearGroup.upperRightHom (((t₁ * t₂⁻¹ : Rˣ) : R) * x)) ∧
      ∀ t ∈ torus R, (unipotent R).map (MulAut.conj t).toMonoidHom = unipotent R := by
  have h1 : ∀ (t₁ t₂ : Rˣ) (x : R), diagElt t₁ t₂ * GeneralLinearGroup.upperRightHom x * (diagElt t₁ t₂)⁻¹ =
      GeneralLinearGroup.upperRightHom (((t₁ * t₂⁻¹ : Rˣ) : R) * x) := by
    intro t₁ t₂ x
    rw [mul_inv_eq_iff_eq_mul]
    apply gl_ext_two <;> simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(x * (t₁ : R))) * t₂.mul_inv
  refine ⟨h1, fun t ht ↦ ?_⟩
  obtain ⟨t₁, t₂, rfl⟩ := exists_diagElt_of_mem_torus ht
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, (h1 t₁ t₂ x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨GeneralLinearGroup.upperRightHom (((t₁⁻¹ * t₂ : Rˣ) : R) * x), ⟨_, rfl⟩, ?_⟩
    show diagElt t₁ t₂ * _ * (diagElt t₁ t₂)⁻¹ = _
    rw [h1, ← mul_assoc]
    congr 1
    simp only [Units.val_mul]
    linear_combination x * ((t₁ : R) * ↑t₁⁻¹) * t₂.inv_mul + x * t₁.mul_inv

private theorem torus_inf_unipotent (R : Type*) [CommRing R] : torus R ⊓ unipotent R = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hT, x, rfl⟩
  have hx : x = 0 := by simpa using hT.1
  rw [hx, AddChar.map_zero_eq_one]; exact Subgroup.one_mem _

/-- `B(R) = T(R) N(R)`: (i) every `b ∈ B(R)` is `t n` with unique `t ∈ T(R)`, `n ∈ N(R)`, explicitly
`(a y; 0 d) = diag(a, d) n(a⁻¹ y)`; (ii) `T(R) ∩ N(R) = 1`; (iii) `N(R)` is normal in `B(R)`. -/
@[tf_id "I.conv.thm:borel-semidirect"]
theorem borel_semidirect (R : Type*) [CommRing R] :
    (∀ b ∈ borel R, ∃! p : GL (Fin 2) R × GL (Fin 2) R, p.1 ∈ torus R ∧ p.2 ∈ unipotent R ∧ b = p.1 * p.2) ∧
      (∀ (a d : Rˣ) (y : R) (b : GL (Fin 2) R), (b : Matrix (Fin 2) (Fin 2) R) = !![(a : R), y; 0, (d : R)] →
        b = diagElt a d * GeneralLinearGroup.upperRightHom (((a⁻¹ : Rˣ) : R) * y)) ∧
      torus R ⊓ unipotent R = ⊥ ∧
      ((unipotent R).subgroupOf (borel R)).Normal := by
  have hii : ∀ (a d : Rˣ) (y : R) (b : GL (Fin 2) R), (b : Matrix (Fin 2) (Fin 2) R) = !![(a : R), y; 0, (d : R)] →
      b = diagElt a d * GeneralLinearGroup.upperRightHom (((a⁻¹ : Rˣ) : R) * y) := by
    intro a d y b hb
    apply gl_ext_two <;> simp [hb, diagElt, Matrix.mul_apply, Fin.sum_univ_two]
  -- every element of `B(R)` has unit diagonal entries
  have hex : ∀ b ∈ borel R, ∃ (a d : Rˣ) (y : R), (b : Matrix (Fin 2) (Fin 2) R) = !![(a : R), y; 0, (d : R)] := by
    intro b hb
    have h10 : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := hb
    have hd := det_gl_two b
    rw [h10, mul_zero, sub_zero] at hd
    refine ⟨(isUnit_of_mul_isUnit_left hd).unit, (isUnit_of_mul_isUnit_right hd).unit,
      (b : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩
    apply mat_ext_two <;> simp [h10]
  have hTN := torus_inf_unipotent R
  refine ⟨fun b hb ↦ ?_, hii, hTN, ?_⟩
  · obtain ⟨a, d, y, hb'⟩ := hex b hb
    refine ⟨(diagElt a d, GeneralLinearGroup.upperRightHom (((a⁻¹ : Rˣ) : R) * y)),
      ⟨diagElt_mem_torus' a d, ⟨_, rfl⟩, hii a d y b hb'⟩, ?_⟩
    rintro ⟨t, n⟩ ⟨ht, hn, hbe⟩
    have key : (diagElt a d)⁻¹ * t = GeneralLinearGroup.upperRightHom (((a⁻¹ : Rˣ) : R) * y) * n⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hii a d y b hb', hbe, mul_inv_cancel_right]
    have hm : (diagElt a d)⁻¹ * t ∈ torus R ⊓ unipotent R :=
      ⟨(torus R).mul_mem ((torus R).inv_mem (diagElt_mem_torus' a d)) ht,
        key ▸ (unipotent R).mul_mem ⟨_, rfl⟩ ((unipotent R).inv_mem hn)⟩
    rw [hTN, Subgroup.mem_bot, inv_mul_eq_one] at hm
    rw [hm] at key
    simp only [inv_mul_cancel] at key
    have hn' : n = GeneralLinearGroup.upperRightHom (((a⁻¹ : Rˣ) : R) * y) := by
      rw [eq_comm, ← mul_inv_eq_one]; exact key.symm
    rw [← hm, ← hn']
  · constructor
    rintro ⟨n, hnB⟩ hn ⟨b, hb⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨a, d, y, hb'⟩ := hex b hb
    obtain ⟨x, hx⟩ := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hii a d y b hb']
    refine ⟨((a * d⁻¹ : Rˣ) : R) * x, ?_⟩
    have hx' : GeneralLinearGroup.upperRightHom x = n := hx
    rw [← hx', _root_.mul_inv_rev, ← mul_assoc, mul_assoc (diagElt a d) (GeneralLinearGroup.upperRightHom _),
      ← AddChar.map_add_eq_mul, mul_assoc (diagElt a d), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
      (torus_normalizes_unipotent R).1]
    congr 1
    simp only [Units.val_mul]
    ring

/-- `B(R) ∩ N̄(R) = 1`. -/
@[tf_id "I.conv.lem:borel-inter-opposite-unipotent"]
theorem borel_inf_oppositeUnipotent (R : Type*) [CommRing R] : borel R ⊓ oppositeUnipotent R = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hB, x', rfl⟩
  set x : R := Multiplicative.toAdd x'
  have hx : x = 0 := by
    have : ((oppositeUnipotentHom x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := hB
    simpa [oppositeUnipotentHom, oppositeUnipotentElt] using this
  rw [Subgroup.mem_bot]
  show oppositeUnipotentHom x = 1
  rw [hx, AddChar.map_zero_eq_one]

private theorem exists_ne_zero_one (k : Type*) [Field k] (hk : 3 ≤ ENat.card k) : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set k) ⊆ {0, 1} := fun a _ ↦ by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (h a ha)
  have h1 := Set.encard_le_encard hsub
  rw [Set.encard_univ, Set.encard_pair zero_ne_one] at h1
  exact absurd (hk.trans h1) (by decide)

private theorem weyl_mem_normalizer (k : Type*) [Field k] :
    weylElement k ∈ Subgroup.normalizer (torus k : Set (GL (Fin 2) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ i j, ((weylElement k * h * (weylElement k)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i j =
      !![(h : Matrix (Fin 2) (Fin 2) k) 1 1, -(h : Matrix (Fin 2) (Fin 2) k) 1 0;
        -(h : Matrix (Fin 2) (Fin 2) k) 0 1, (h : Matrix (Fin 2) (Fin 2) k) 0 0] i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylElement, Units.inv_mk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨h01, h10⟩
    refine ⟨?_, ?_⟩
    · rw [hconj]; simp [h10]
    · rw [hconj]; simp [h01]
  · rintro ⟨h01, h10⟩
    rw [hconj] at h01 h10
    refine ⟨?_, ?_⟩
    · simpa using h10
    · simpa using h01

/-- Over a field `k` with at least three elements, `N_{GL₂(k)}(T(k)) = T(k) ⊔ w T(k)` (disjoint union). -/
@[tf_id "I.conv.thm:normalizer-torus"]
theorem normalizer_torus (k : Type*) [Field k] (hk : 3 ≤ ENat.card k) :
    ((Subgroup.normalizer (torus k : Set (GL (Fin 2) k))) : Set (GL (Fin 2) k)) =
        (torus k : Set (GL (Fin 2) k)) ∪ (weylElement k * ·) '' (torus k : Set (GL (Fin 2) k)) ∧
      Disjoint (torus k : Set (GL (Fin 2) k)) ((weylElement k * ·) '' (torus k : Set (GL (Fin 2) k))) := by
  have hw := weyl_mem_normalizer k
  refine ⟨Set.ext fun g ↦ ⟨fun hg ↦ ?_, ?_⟩, ?_⟩
  · obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_one k hk
    set t0 := diagElt (Units.mk0 a ha0) 1 with ht0
    have hs : g * t0 * g⁻¹ ∈ torus k :=
      (Subgroup.mem_normalizer_iff.mp hg t0).mp (diagElt_mem_torus' _ _)
    obtain ⟨b₁, b₂, hb⟩ := exists_diagElt_of_mem_torus hs
    have heq : g * t0 = diagElt b₁ b₂ * g := by rw [← hb]; group
    have e : ∀ i j, ((g * t0 : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i j =
        ((diagElt b₁ b₂ * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i j := fun i j ↦ by rw [heq]
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    have e11 := e 1 1
    simp [ht0, diagElt, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have hd := (det_gl_two g).ne_zero
    set α := (g : Matrix (Fin 2) (Fin 2) k) 0 0
    set β := (g : Matrix (Fin 2) (Fin 2) k) 0 1
    set γ := (g : Matrix (Fin 2) (Fin 2) k) 1 0
    set δ := (g : Matrix (Fin 2) (Fin 2) k) 1 1
    have ha1' : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    by_cases hα : α = 0
    · rw [hα, zero_mul, zero_sub, neg_ne_zero] at hd
      have hβ : β ≠ 0 := left_ne_zero_of_mul hd
      have hγ : γ ≠ 0 := right_ne_zero_of_mul hd
      have hb1 : (b₁ : k) = 1 := by
        have : ((b₁ : k) - 1) * β = 0 := by linear_combination -e01
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hβ)
      have hb2 : (b₂ : k) = a := by
        have : ((b₂ : k) - a) * γ = 0 := by linear_combination -e10
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hγ)
      have hδ : δ = 0 := by
        have : (a - 1) * δ = 0 := by linear_combination -e11 - δ * hb2
        exact (mul_eq_zero.mp this).resolve_left ha1'
      right
      refine ⟨diagElt (Units.mk0 (-γ) (neg_ne_zero.mpr hγ)) (Units.mk0 β hβ), diagElt_mem_torus' _ _, ?_⟩
      apply gl_ext_two <;> simp [weylElement, diagElt, Matrix.mul_apply, Fin.sum_univ_two, hα, hδ, α, β, γ, δ]
    · have hb1 : (b₁ : k) = a := by
        have : ((b₁ : k) - a) * α = 0 := by linear_combination -e00
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hα)
      have hβ : β = 0 := by
        have : (a - 1) * β = 0 := by linear_combination -e01 - β * hb1
        exact (mul_eq_zero.mp this).resolve_left ha1'
      rw [hβ, zero_mul, sub_zero] at hd
      have hδ : δ ≠ 0 := right_ne_zero_of_mul hd
      have hb2 : (b₂ : k) = 1 := by
        have : ((b₂ : k) - 1) * δ = 0 := by linear_combination -e11
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hδ)
      have hγ : γ = 0 := by
        have : (a - 1) * γ = 0 := by linear_combination e10 + γ * hb2
        exact (mul_eq_zero.mp this).resolve_left ha1'
      left
      exact ⟨hβ, hγ⟩
  · rintro (hg | ⟨t, ht, rfl⟩)
    · exact Subgroup.le_normalizer hg
    · exact Subgroup.mul_mem _ hw (Subgroup.le_normalizer ht)
  · rw [Set.disjoint_left]
    rintro g hg ⟨t, ht, rfl⟩
    obtain ⟨t₁, t₂, rfl⟩ := exists_diagElt_of_mem_torus ht
    have h01 := hg.1
    simp [weylElement, diagElt, Matrix.mul_apply, Fin.sum_univ_two] at h01

end Structure

section RootData

/-! ### `𝔞_B`, the simple root and the chamber functions (M3, unit U1) -/

/-- `𝔞_B = ℝ²`, the functions `h : Fin 2 → ℝ`, `h = (h₁, h₂)`. -/
@[tf_id "I.conv.def:space-a-b"]
abbrev SpaceAB : Type := Fin 2 → ℝ

/-- `𝔞_B^G = {h : h₁ + h₂ = 0} ⊆ 𝔞_B`. -/
@[tf_id "I.conv.def:space-a-b-g"]
def spaceABG : Submodule ℝ SpaceAB :=
  LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 + LinearMap.proj 1)

/-- The simple root `α(h) = h₁ − h₂`. -/
@[tf_id "I.conv.def:simple-root"]
def simpleRoot : SpaceAB →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 - LinearMap.proj 1

/-- The projection `h ↦ h_B^G = ((h₁ − h₂)/2, −(h₁ − h₂)/2)` of `𝔞_B` onto `𝔞_B^G` along `{(x, x)}`. -/
@[tf_aux "I.conv.def:projection-a-b-g"]
noncomputable def projABG : SpaceAB →ₗ[ℝ] SpaceAB :=
  (1 / 2 : ℝ) • LinearMap.pi ![simpleRoot, -simpleRoot]

/-- `h ↦ h_B^G` takes values in `𝔞_B^G`, is the identity on `𝔞_B^G` and kills `{(x, x)}`. -/
@[tf_aux "I.conv.lem:projection-a-b-g"]
theorem projABG_spec :
    (∀ h, projABG h ∈ spaceABG) ∧ (∀ h ∈ spaceABG, projABG h = h) ∧ ∀ x : ℝ, projABG (fun _ ↦ x) = 0 := by
  refine ⟨fun h ↦ ?_, fun h hh ↦ ?_, fun x ↦ ?_⟩
  · simp [spaceABG, projABG, simpleRoot]
  · have h' : h 0 + h 1 = 0 := by simpa [spaceABG] using hh
    funext i; fin_cases i <;> simp [projABG, simpleRoot] <;> linarith
  · funext i; fin_cases i <;> simp [projABG, simpleRoot]

/-- `ρ = α/2`, `ρ(h) = (h₁ − h₂)/2`. -/
@[tf_aux "I.conv.def:rho"]
noncomputable def rho : SpaceAB →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • simpleRoot

/-- `τ_B`: the characteristic function of the positive chamber `{α(h) > 0}`. -/
@[tf_id "I.conv.def:chamber-functions"]
noncomputable def tauB (h : SpaceAB) : ℝ :=
  Set.indicator {h : SpaceAB | 0 < simpleRoot h} 1 h

/-- `τ̂_B`: the characteristic function of the positive cone `{ϖ(h) > 0}`, `ϖ = α/2`. -/
@[tf_aux "I.conv.def:chamber-function-hat"]
noncomputable def tauHatB (h : SpaceAB) : ℝ :=
  Set.indicator {h : SpaceAB | 0 < (1 / 2 : ℝ) * simpleRoot h} 1 h

end RootData

section Real

/-- The maximal compact subgroup `K_∞ = O(2) = {k ∈ GL₂(ℝ) : kᵀk = 1}`. -/
@[tf_id "I.conv.def:max-compact-real"]
def maxCompactReal : Subgroup (GL (Fin 2) ℝ) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * k = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at *
    calc _ = ((h : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (((g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * g) * h)) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv hg, transpose_transpose]
    exact mul_eq_one_comm.mp hg

/-- `SO(2) = K_∞ ∩ SL₂(ℝ)`. -/
@[tf_aux "I.conv.def:special-orthogonal-real"]
def specialOrthogonalReal : Subgroup (GL (Fin 2) ℝ) :=
  maxCompactReal ⊓ (GeneralLinearGroup.det (n := Fin 2) (R := ℝ)).ker

open Real in
/-- The rotation `k_θ = (cos θ  sin θ; −sin θ  cos θ) = exp(θU)`, `U = (0 1; −1 0)`. -/
@[tf_id "I.conv.def:rotation"]
noncomputable def rotation (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![cos θ, sin θ; -sin θ, cos θ], !![cos θ, -sin θ; sin θ, cos θ],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply] <;> nlinarith [sin_sq_add_cos_sq θ],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply] <;> nlinarith [sin_sq_add_cos_sq θ]⟩

theorem rotation_val (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

theorem rotation_mem_maxCompactReal (θ : ℝ) : rotation θ ∈ maxCompactReal := by
  show (_ : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * _ = 1
  rw [rotation_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

/-- A `2 × 2` real matrix with `kᵀk = 1` and `det k = 1` is `(α β; −β α)` with `α² + β² = 1`. -/
theorem so2_normal_form {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : kᵀ * k = 1) (hdet : k.det = 1) :
    k 1 1 = k 0 0 ∧ k 0 1 = -k 1 0 ∧ k 0 0 ^ 2 + k 1 0 ^ 2 = 1 := by
  have e00 := congrFun (congrFun hk 0) 0
  have e11 := congrFun (congrFun hk 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  rw [Matrix.det_fin_two] at hdet
  have h1 : k 1 1 - k 0 0 = 0 := by nlinarith [sq_nonneg (k 1 1 - k 0 0), sq_nonneg (k 0 1 + k 1 0)]
  have h2 : k 0 1 + k 1 0 = 0 := by nlinarith [sq_nonneg (k 1 1 - k 0 0), sq_nonneg (k 0 1 + k 1 0)]
  exact ⟨by linarith, by linarith, by nlinarith⟩

theorem mem_specialOrthogonalReal_iff (k : GL (Fin 2) ℝ) :
    k ∈ specialOrthogonalReal ↔
      (k : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * k = 1 ∧ (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [specialOrthogonalReal, Subgroup.mem_inf, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- `θ ↦ k_θ` is a homomorphism `ℝ → SO(2)`, onto, with kernel `2πℤ`. -/
@[tf_aux "I.conv.lem:rotation-surjective"]
theorem rotation_surjective :
    (∀ θ φ : ℝ, rotation (θ + φ) = rotation θ * rotation φ) ∧
    (∀ θ : ℝ, rotation θ ∈ specialOrthogonalReal) ∧
    (∀ k ∈ specialOrthogonalReal, ∃ θ : ℝ, rotation θ = k) ∧
    (∀ θ : ℝ, rotation θ = 1 ↔ ∃ m : ℤ, θ = 2 * Real.pi * m) := by
  refine ⟨fun θ φ => ?_, fun θ => ?_, fun k hk => ?_, fun θ => ?_⟩
  · ext i j
    rw [Units.val_mul, rotation_val, rotation_val, rotation_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.cos_add, Real.sin_add] <;> ring
  · rw [mem_specialOrthogonalReal_iff]
    refine ⟨rotation_mem_maxCompactReal θ, ?_⟩
    rw [rotation_val, Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [mem_specialOrthogonalReal_iff] at hk
    obtain ⟨h11, h01, hn⟩ := so2_normal_form hk.1 hk.2
    set z : ℂ := ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩
    have hz : ‖z‖ = 1 := by
      have : Complex.normSq z = 1 := by
        rw [Complex.normSq_apply]; simp only [z]; rw [h01]; linear_combination hn
      rw [Complex.norm_def, this, Real.sqrt_one]
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
    refine ⟨Complex.arg z, ?_⟩
    have hc : Real.cos (Complex.arg z) = (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      rw [Complex.cos_arg hz0, hz, div_one]
    have hs : Real.sin (Complex.arg z) = (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
      rw [Complex.sin_arg z, hz, div_one]
    clear_value z
    generalize Complex.arg z = θ at hc hs ⊢
    ext i j
    rw [rotation_val]
    fin_cases i <;> fin_cases j <;> simp [hc, hs, h11, h01]
  · constructor
    · intro h
      have h00 := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) h
      simp only [rotation_val, Units.val_one] at h00
      simp at h00
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff θ).mp h00
      exact ⟨n, by rw [← hn]; ring⟩
    · rintro ⟨m, rfl⟩
      ext i j
      rw [rotation_val]
      have hc : Real.cos (2 * Real.pi * m) = 1 := by
        rw [show 2 * Real.pi * m = (m : ℝ) * (2 * Real.pi) by ring]; exact Real.cos_int_mul_two_pi m
      have hs : Real.sin (2 * Real.pi * m) = 0 := by
        rw [show 2 * Real.pi * m = ((2 * m : ℤ) : ℝ) * Real.pi by push_cast; ring]
        exact Real.sin_int_mul_pi _
      fin_cases i <;> fin_cases j <;> simp [hc, hs]

end Real

end GL2TF
