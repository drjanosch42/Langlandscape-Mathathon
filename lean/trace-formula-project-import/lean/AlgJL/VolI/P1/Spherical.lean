import AlgJL.Meta.Tag
import AlgJL.VolI.P0.Conventions
import AlgJL.VolI.P0.LocalField
import AlgJL.VolI.P0.Decompositions
import Definitions.Def_LocalLanglands_GelfandInvolution

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/Spherical.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (0): none.
Dropped tagged IDs: none. -/

/-!
# The spherical Hecke algebra and Gelfand's trick (M1, unit U5)

Lean counterpart of `vol1/ch-1-01-spherical.tex` §1. Owner: L2 (scaffolded by L1 in W0).

The Hecke algebra of a pair is the vendored `HeckePair.HeckeAlgebra` ([AFLT]
`Definitions/Def_LocalLanglands_HeckePair.lean`, modified: imports only; see `lean/Vendor/MANIFEST.tsv`): bi-`U`-invariant
functions supported on finitely many left cosets `gU`, with convolution `(f₁ ∗ f₂)(x) = ∑_{y ∈ G/U} f₁(y) f₂(y⁻¹x)`,
i.e. the counting measure on `G/U`. The vendored constants that B renders are tagged below (B-only items).
-/

attribute [tf_aux "X.hpair.def:is-hecke-fun"] HeckePair.IsHeckeFun
attribute [tf_aux "X.hpair.def:hecke-submodule"] HeckePair.heckeSubmodule
attribute [tf_aux "X.hpair.def:hecke-algebra"] HeckePair.HeckeAlgebra
attribute [tf_aux "X.hpair.def:conv-term"] HeckePair.convTerm
attribute [tf_aux "X.hpair.def:conv"] HeckePair.conv
attribute [tf_aux "X.hpair.def:hecke-one"] HeckePair.heckeOne

attribute [tf_aux "X.hpair.def:mul-instance"] HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra
attribute [tf_aux "X.hpair.def:one-instance"] HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra
attribute [tf_aux "X.hpair.def:ring-instance"] HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra
attribute [tf_aux "X.hpair.def:algebra-instance"] HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra

open ValuativeRel GL2TF

namespace GL2TF.Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- The spherical Hecke algebra `H(GL₂(F), K_F)`: complex-valued bi-`K_F`-invariant functions on `GL₂(F)`
supported on finitely many left cosets `gK_F`, with convolution `(f₁ ∗ f₂)(x) = ∑_{yK ∈ G/K} f₁(y) f₂(y⁻¹x)`
(the vendored coset model; its `Ring` and `Algebra ℂ` instances come with `HeckePair.HeckeAlgebra`). -/
@[tf_id "I.satake.def:spherical-hecke-algebra"]
abbrev sphericalHeckeAlgebra : Type _ := HeckePair.HeckeAlgebra 𝐊[F] ℂ

/-- The transpose `τ(g) = gᵀ` as a map `GL₂(F) → GL₂(F)`. -/
@[tf_aux "I.satake.def:transpose-gl"]
def transposeGL {F : Type*} [Field F] (g : GL (Fin 2) F) : GL (Fin 2) F where
  val := (g : Matrix (Fin 2) (Fin 2) F).transpose
  inv := ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).transpose
  val_inv := by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

omit [TopologicalSpace F] [IsNALF F] in
/-- The transpose maps `K_F` into itself: same entries, same determinant (proof helper). -/
theorem transposeGL_mem {k : GL (Fin 2) F} (hk : k ∈ 𝐊[F]) : transposeGL k ∈ 𝐊[F] := by
  obtain ⟨h1, h2⟩ := (mem_K_iff k).mp hk
  refine (mem_K_iff _).mpr ⟨fun i j => h1 j i, ?_⟩
  change valuation F (k : Matrix (Fin 2) (Fin 2) F).transpose.det = 1
  rwa [Matrix.det_transpose]

/-- The transpose is a Gelfand involution for `K_F`: it is an anti-automorphism of order two, `τ(K_F) = K_F`,
`τ(t_{a,b}) = t_{a,b}`, and `τ(g) ∈ K_F g K_F` for every `g`. -/
@[tf_id "I.satake.lem:transpose-gelfand-involution"]
theorem transpose_gelfand_involution :
    (∀ g h : GL (Fin 2) F, transposeGL (g * h) = transposeGL h * transposeGL g) ∧
      (∀ g : GL (Fin 2) F, transposeGL (transposeGL g) = g) ∧
      transposeGL '' (𝐊[F] : Set (GL (Fin 2) F)) = 𝐊[F] ∧
      (∀ a b : ℤ, transposeGL (cartanElement F a b) = cartanElement F a b) ∧
      ∀ g : GL (Fin 2) F, transposeGL g ∈ DoubleCoset.doubleCoset g 𝐊[F] 𝐊[F] := by
  have hmul : ∀ g h : GL (Fin 2) F, transposeGL (g * h) = transposeGL h * transposeGL g :=
    fun g h => Units.ext (Matrix.transpose_mul _ _)
  have hinv : ∀ g : GL (Fin 2) F, transposeGL (transposeGL g) = g :=
    fun g => Units.ext (Matrix.transpose_transpose _)
  have ht : ∀ a b : ℤ, transposeGL (cartanElement F a b) = cartanElement F a b := by
    intro a b
    apply Units.ext
    change ((cartanElement F a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).transpose = _
    rw [cartanElement_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨hmul, hinv, ?_, ht, ?_⟩
  · ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact transposeGL_mem F hk
    · intro hg
      exact ⟨transposeGL g, transposeGL_mem F hg, hinv g⟩
  · intro g
    obtain ⟨a, b, -, hg⟩ := cartan_exists F g
    rw [DoubleCoset.doubleCoset_eq_of_mem hg]
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    rw [hmul, hmul, ht]
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨transposeGL k', transposeGL_mem F hk', transposeGL k, transposeGL_mem F hk, (mul_assoc _ _ _).symm⟩

/-- The spherical Hecke algebra `H(GL₂(F), K_F)` is commutative. -/
@[tf_id "I.satake.thm:hecke-commutative"]
theorem hecke_commutative (f₁ f₂ : sphericalHeckeAlgebra F) : f₁ * f₂ = f₂ * f₁ := by
  obtain ⟨hmul, hinv, hK, ht, -⟩ := transpose_gelfand_involution F
  refine (HeckePair.IsGelfandInvolution.of_forall_exists_fixedRep hmul hinv
    (fun u hu => by
      have := Set.mem_image_of_mem transposeGL hu
      rwa [hK] at this) fun g => ?_).heckeMul_comm f₁ f₂
  obtain ⟨a, b, -, hg⟩ := cartan_exists F g
  exact ⟨cartanElement F a b, ht a b, hg⟩

end GL2TF.Local
