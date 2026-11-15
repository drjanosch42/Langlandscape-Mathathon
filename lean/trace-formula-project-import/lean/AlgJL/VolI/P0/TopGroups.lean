import AlgJL.Meta.Tag
import AlgJL.Common.MatrixGL2
import AlgJL.VolI.P0.Conventions
import AlgJL.VolI.P0.LocalField
import AlgJL.VolI.P0.Adeles
import AlgJL.VolI.P0.Ideles
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# GL₂ over a non-archimedean local field, over ℝ and over the adeles as a topological group (M1 U1, M2 U1, M3 U6)

Lean counterpart of `vol1/ch-0-04-top-groups.tex` §2 ("GL₂ over a NALF"), §3 ("GL₂(ℝ)") and §§4–6 (adelic GL₂,
G(𝔸)¹, strong approximation). `G(𝔸) = GL (Fin 2) Adele` and `G(𝔸_f) = GL (Fin 2) FinAdele` are not aliased (units
topology from Mathlib); the components `g_∞`, `g_f`, `g_p` are the homomorphisms induced by the coordinate ring
homomorphisms (`gl2Map`). Owner: L1.
-/

open Topology ValuativeRel GL2TF

namespace GL2TF.Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- For a NALF `F`, `GL₂(F)` with the units topology is locally compact, Hausdorff and second countable. -/
@[tf_id "I.topgrp.thm:gl2-local-locally-compact"]
theorem gl2_locallyCompact_t2_secondCountable :
    LocallyCompactSpace (GL (Fin 2) F) ∧ T2Space (GL (Fin 2) F) ∧
      SecondCountableTopology (GL (Fin 2) F) := by
  have he := (gl2_units_isOpenEmbedding F).1
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → F))
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  exact ⟨he.locallyCompactSpace, inferInstance, he.isInducing.secondCountableTopology⟩

/-- For a NALF `F`, `K_F` is a compact open subgroup of `GL₂(F)`. -/
@[tf_id "I.topgrp.thm:max-compact-local-compact-open"]
theorem maxCompact_isCompact_isOpen :
    IsCompact (𝐊[F] : Set (GL (Fin 2) F)) ∧ IsOpen (𝐊[F] : Set (GL (Fin 2) F)) := by
  have he := (gl2_units_isOpenEmbedding F).1
  have hv := Valuation.integer.integers (valuation F)
  set O : Set F := ((𝒪[F] : Subring F) : Set F) with hO
  set S : Set F := {x | valuation F x = 1} with hS
  set C : Set (Matrix (Fin 2) (Fin 2) F) := {X | (∀ i j, X i j ∈ O) ∧ X.det ∈ S} with hC
  have hK : (𝐊[F] : Set (GL (Fin 2) F)) = Units.val ⁻¹' C := by
    ext g
    have h12 := (mem_maxCompact_tfae (Subring.subtype 𝒪[F]) Subtype.val_injective g).out 1 2
    have hr : ∀ y : F, y ∈ Set.range (Subring.subtype 𝒪[F]) ↔ y ∈ O :=
      fun y ↦ ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h ↦ ⟨⟨y, h⟩, rfl⟩⟩
    simp only [SetLike.mem_coe, h12, hr, Set.mem_preimage, hC, Set.mem_ofPred_eq]
    refine and_congr_right fun _ ↦ ⟨?_, fun h1 ↦ ?_⟩
    · rintro ⟨u, hu⟩
      rw [hu]
      exact hv.valuation_unit u
    · have hdetO : (g : Matrix (Fin 2) (Fin 2) F).det ∈ 𝒪[F] :=
        (Valuation.mem_integer_iff _ _).mpr (le_of_eq h1)
      exact ⟨(hv.isUnit_of_one' (x := ⟨_, hdetO⟩) h1).unit, rfl⟩
  have hS' : IsClopen S := by
    have := Valuation.isClopen_sphere (v := valuation F) (r := 1) one_ne_zero
    simpa only [Valuation.restrict_eq_one_iff] using this
  have hOc : IsCompact O := IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have hOo : IsOpen O := Valuation.isOpen_integer (v := valuation F)
  have hdet : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) F → F) := continuous_id.matrix_det
  have hCdef : C = {X : Matrix (Fin 2) (Fin 2) F | ∀ i j, X i j ∈ O} ∩ Matrix.det ⁻¹' S := rfl
  have hCo : IsOpen C := hCdef ▸ (hOo.matrix).inter (hS'.isOpen.preimage hdet)
  have hCc : IsCompact C :=
    hCdef ▸ (hOc.matrix).inter_right (hS'.isClosed.preimage hdet)
  refine ⟨?_, hK ▸ hCo.preimage Units.continuous_val⟩
  rw [he.isCompact_iff, hK, Set.image_preimage_eq_of_subset]
  · exact hCc
  · intro X hX
    rw [(gl2_units_isOpenEmbedding F).2]
    intro h0
    have : valuation F X.det = 1 := hX.2
    simp [h0] at this

end GL2TF.Local

namespace GL2TF

/-- `GL₂(ℝ)` with the units topology is locally compact, Hausdorff and second countable, and its σ-algebra
(comap of the product σ-algebra along `GL₂(ℝ) → M₂(ℝ)`) is the Borel σ-algebra. -/
@[tf_id "I.topgrp.thm:gl2-real-locally-compact"]
theorem gl2Real_locallyCompact_t2_secondCountable_borel :
    LocallyCompactSpace (GL (Fin 2) ℝ) ∧ T2Space (GL (Fin 2) ℝ) ∧
      SecondCountableTopology (GL (Fin 2) ℝ) ∧ BorelSpace (GL (Fin 2) ℝ) := by
  have he := (gl2_units_isOpenEmbedding ℝ).1
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact ⟨he.locallyCompactSpace, inferInstance, he.isInducing.secondCountableTopology, gl2_borelSpace ℝ⟩

open Matrix Matrix.GeneralLinearGroup in
/-- `K_∞ = O(2)` is a compact subgroup of `GL₂(ℝ)`. -/
@[tf_id "I.topgrp.thm:max-compact-real-compact"]
theorem maxCompactReal_isCompact : IsCompact (maxCompactReal : Set (GL (Fin 2) ℝ)) := by
  set C : Set (Matrix (Fin 2) (Fin 2) ℝ) := {M | Mᵀ * M = 1}
  have hC : IsCompact C := by
    have hcl : IsClosed C := isClosed_eq (by fun_prop) continuous_const
    have hb : C ⊆ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1 := by
      intro M hM i _ j _
      have e := congrFun (congrFun hM j) j
      simp [Matrix.mul_apply, Fin.sum_univ_two] at e
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · constructor <;> nlinarith [sq_nonneg (M 0 j), sq_nonneg (M 1 j)]
      · constructor <;> nlinarith [sq_nonneg (M 0 j), sq_nonneg (M 1 j)]
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hb
  have he := (gl2_units_isOpenEmbedding ℝ).1
  rw [he.isCompact_iff]
  convert hC using 1
  ext M; constructor
  · rintro ⟨g, hg, rfl⟩; exact hg
  · intro hM
    have hd : M.det ≠ 0 := by
      intro h0; have := congrArg Matrix.det hM; rw [Matrix.det_mul, Matrix.det_transpose, h0] at this; simp at this
    refine ⟨mkOfDetNeZero M hd, ?_, val_mkOfDetNeZero _ _⟩
    show ((mkOfDetNeZero M hd : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * _ = 1
    rw [val_mkOfDetNeZero]; exact hM

section Adelic

/-! ### Adelic `GL₂` (M3, unit U6) -/

open scoped RestrictedProduct

/-- `g ↦ g_∞`, `G(𝔸) → GL₂(ℝ)`, induced by `𝔸 → ℝ`. -/
@[tf_aux "I.topgrp.def:adelic-component-inf"]
noncomputable def compInf : GL (Fin 2) Adele →* GL (Fin 2) ℝ :=
  gl2Map (RingHom.fst ℝ FinAdele)

/-- `g ↦ g_f`, `G(𝔸) → G(𝔸_f)`, induced by `𝔸 → 𝔸_f`. -/
@[tf_aux "I.topgrp.def:adelic-component-fin"]
noncomputable def compFin : GL (Fin 2) Adele →* GL (Fin 2) FinAdele :=
  gl2Map (RingHom.snd ℝ FinAdele)

/-- `g ↦ g_p`, `G(𝔸_f) → GL₂(ℚ_p)`, induced by `𝔸_f → ℚ_p`. -/
@[tf_aux "I.topgrp.def:finite-adelic-component-place"]
noncomputable def compFinPlace (p : Nat.Primes) : GL (Fin 2) FinAdele →* GL (Fin 2) ℚ_[p] :=
  gl2Map (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p)

/-- `g ↦ g_p`, `G(𝔸) → GL₂(ℚ_p)`. -/
@[tf_aux "I.topgrp.def:adelic-component-place"]
noncomputable def compPlace (p : Nat.Primes) : GL (Fin 2) Adele →* GL (Fin 2) ℚ_[p] :=
  (compFinPlace p).comp compFin

/-- `G(ℚ) ⊆ G(𝔸)`: the image of `GL₂(ℚ)` under the map induced by the diagonal embedding `ℚ → 𝔸`. -/
@[tf_id "I.topgrp.def:gl2-adelic"]
noncomputable def gl2RatAdelic : Subgroup (GL (Fin 2) Adele) :=
  (gl2Map (algebraMap ℚ Adele)).range

/-- `𝒪_{ℚ_p} = ℤ_p`: `x ∈ 𝒪[ℚ_p] ↔ ‖x‖ ≤ 1` (proof helper). -/
theorem padic_mem_integer_iff (p : Nat.Primes) (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]),
    ← Valuation.Compatible.vle_iff_le (v := valuation ℚ_[p]),
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation (p := (p : ℕ))), map_one]
  by_cases hx : x = 0
  · simp [hx]
  · rw [show Padic.mulValuation x = WithZero.exp (-x.valuation) by simp [Padic.mulValuation, hx],
      Padic.norm_le_one_iff_val_nonneg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

/-- For `g ∈ G(𝔸_f)`, `g_p ∈ K_p` for all but finitely many `p`. -/
@[tf_aux "I.topgrp.lem:gl2-fin-adelic-eventually-max-compact"]
theorem gl2Fin_eventually_mem (g : GL (Fin 2) FinAdele) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite, compFinPlace p g ∈ 𝐊[ℚ_[p]] := by
  have hent : ∀ (h : GL (Fin 2) FinAdele) (i j : Fin 2),
      ∀ᶠ p : Nat.Primes in Filter.cofinite, (h : Matrix (Fin 2) (Fin 2) FinAdele) i j p ∈ PadicInt.subring p :=
    fun h i j ↦ ((h : Matrix (Fin 2) (Fin 2) FinAdele) i j).2
  have hall : ∀ᶠ p : Nat.Primes in Filter.cofinite, ∀ i j : Fin 2,
      (g : Matrix (Fin 2) (Fin 2) FinAdele) i j p ∈ PadicInt.subring p ∧
        ((g⁻¹ : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele) i j p ∈ PadicInt.subring p := by
    simp only [Filter.eventually_all]
    exact fun i j ↦ (hent g i j).and (hent g⁻¹ i j)
  filter_upwards [hall] with p hp
  have key := (mem_maxCompact_tfae (Subring.subtype 𝒪[ℚ_[p]]) Subtype.val_injective (compFinPlace p g)).out 1 3
  refine key.mpr ⟨fun i j ↦ ⟨⟨_, (padic_mem_integer_iff p _).mpr ?_⟩, rfl⟩,
    fun i j ↦ ⟨⟨_, (padic_mem_integer_iff p _).mpr ?_⟩, rfl⟩⟩
  · exact (hp i j).1
  · exact (hp i j).2

/-- `g ↦ (g_p)_p`, `G(𝔸_f) → Πʳ_p (GL₂(ℚ_p), K_p)`. -/
@[tf_aux "I.topgrp.def:gl2-fin-to-restricted-product"]
noncomputable def gl2FinToResProd (g : GL (Fin 2) FinAdele) : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]] :=
  ⟨fun p ↦ compFinPlace p g, gl2Fin_eventually_mem g⟩

/-- `K_f = {k ∈ G(𝔸_f) : k_p ∈ K_p for all p}`. -/
@[tf_aux "I.topgrp.def:max-compact-fin-adelic"]
noncomputable def maxCompactFin : Subgroup (GL (Fin 2) FinAdele) :=
  ⨅ p : Nat.Primes, (𝐊[ℚ_[p]]).comap (compFinPlace p)

/-! #### Proof infrastructure for U6 (untagged) -/

section ProdGL

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Entrywise pairing of matrices. -/
@[tf_aux "I.topgrp.def:matrix-pair"]
def matPair (A : Matrix (Fin 2) (Fin 2) R) (B : Matrix (Fin 2) (Fin 2) S) : Matrix (Fin 2) (Fin 2) (R × S) :=
  Matrix.of fun i j ↦ (A i j, B i j)

theorem matPair_mul (A A' : Matrix (Fin 2) (Fin 2) R) (B B' : Matrix (Fin 2) (Fin 2) S) :
    matPair (A * A') (B * B') = matPair A B * matPair A' B' := by
  ext i j <;> simp [matPair, Matrix.mul_apply, Fin.sum_univ_two]

theorem matPair_one : matPair (1 : Matrix (Fin 2) (Fin 2) R) (1 : Matrix (Fin 2) (Fin 2) S) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [matPair, Matrix.one_apply, h]

/-- The inverse of `g ↦ (g.map fst, g.map snd)`. -/
@[tf_aux "I.topgrp.def:gl2-pair"]
def glPair (a : GL (Fin 2) R) (b : GL (Fin 2) S) : GL (Fin 2) (R × S) :=
  ⟨matPair a b, matPair (a⁻¹ : GL (Fin 2) R) (b⁻¹ : GL (Fin 2) S),
    by rw [← matPair_mul, a.mul_inv, b.mul_inv, matPair_one],
    by rw [← matPair_mul, a.inv_mul, b.inv_mul, matPair_one]⟩

variable [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]

omit [IsTopologicalRing R] in
theorem continuous_gl2Map {R' : Type*} [CommRing R'] [TopologicalSpace R'] (f : R →+* R') (hf : Continuous f) :
    Continuous (gl2Map f) :=
  Units.continuous_map (Continuous.matrix_map continuous_id hf)

omit [CommRing R] [CommRing S] [IsTopologicalRing R] [IsTopologicalRing S] in
theorem continuous_matPair {X : Type*} [TopologicalSpace X] {A : X → Matrix (Fin 2) (Fin 2) R}
    {B : X → Matrix (Fin 2) (Fin 2) S} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x ↦ matPair (A x) (B x) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    ((hA.matrix_elem i j).prodMk (hB.matrix_elem i j))

/-- `GL₂(R × S) ≅ GL₂(R) × GL₂(S)` as topological groups. -/
@[tf_aux "I.topgrp.def:gl2-product-equiv"]
noncomputable def glProdEquiv : GL (Fin 2) (R × S) ≃ₜ* GL (Fin 2) R × GL (Fin 2) S where
  toFun g := (gl2Map (RingHom.fst R S) g, gl2Map (RingHom.snd R S) g)
  invFun p := glPair p.1 p.2
  left_inv g := by
    apply Units.ext; ext i j <;> rfl
  right_inv p := by
    ext i j <;> rfl
  map_mul' g h := by simp
  continuous_toFun := (continuous_gl2Map _ continuous_fst).prodMk (continuous_gl2Map _ continuous_snd)
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨continuous_matPair (Units.continuous_val.comp continuous_fst) (Units.continuous_val.comp continuous_snd),
      ?_⟩
    exact continuous_matPair (Units.continuous_coe_inv.comp continuous_fst)
      (Units.continuous_coe_inv.comp continuous_snd)

end ProdGL

/-- Entries of `K_p` and of their inverses are in `ℤ_p`. -/
theorem mem_Kp_iff (p : Nat.Primes) (g : GL (Fin 2) ℚ_[p]) :
    g ∈ 𝐊[ℚ_[p]] ↔ ∀ i j, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ PadicInt.subring p ∧
      ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ PadicInt.subring p := by
  have key := (mem_maxCompact_tfae (Subring.subtype 𝒪[ℚ_[p]]) Subtype.val_injective g).out 1 3
  have hr : ∀ y : ℚ_[p], y ∈ Set.range (Subring.subtype 𝒪[ℚ_[p]]) ↔ y ∈ PadicInt.subring p := fun y ↦ by
    rw [PadicInt.mem_subring_iff, ← padic_mem_integer_iff]
    exact ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h ↦ ⟨⟨y, h⟩, rfl⟩⟩
  simp only [key, hr]
  exact ⟨fun h i j ↦ ⟨h.1 i j, h.2 i j⟩, fun h ↦ ⟨fun i j ↦ (h i j).1, fun i j ↦ (h i j).2⟩⟩

theorem isOpen_Kp (p : Nat.Primes) : IsOpen (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p])) :=
  (Local.maxCompact_isCompact_isOpen ℚ_[p]).2

theorem isCompact_Kp (p : Nat.Primes) : IsCompact (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p])) :=
  (Local.maxCompact_isCompact_isOpen ℚ_[p]).1

theorem continuous_compFinPlace (p : Nat.Primes) : Continuous (compFinPlace p) :=
  continuous_gl2Map _ (RestrictedProduct.continuous_eval p)

theorem compFinPlace_apply (p : Nat.Primes) (g : GL (Fin 2) FinAdele) (i j : Fin 2) :
    (compFinPlace p g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j = (g : Matrix (Fin 2) (Fin 2) FinAdele) i j p := rfl

theorem mem_maxCompactFin_iff (g : GL (Fin 2) FinAdele) :
    g ∈ maxCompactFin ↔ ∀ p : Nat.Primes, compFinPlace p g ∈ 𝐊[ℚ_[p]] := by
  simp [maxCompactFin, Subgroup.mem_iInf]

theorem mem_maxCompactFin_iff' (g : GL (Fin 2) FinAdele) :
    g ∈ maxCompactFin ↔ ∀ i j, (g : Matrix (Fin 2) (Fin 2) FinAdele) i j ∈ Zhat ∧
      ((g⁻¹ : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele) i j ∈ Zhat := by
  rw [mem_maxCompactFin_iff]
  simp only [mem_Kp_iff, mem_zhat, ← map_inv, compFinPlace_apply]
  exact ⟨fun h i j ↦ ⟨fun p ↦ (h p i j).1, fun p ↦ (h p i j).2⟩, fun h p i j ↦ ⟨(h i j).1 p, (h i j).2 p⟩⟩

theorem isOpen_maxCompactFin : IsOpen (maxCompactFin : Set (GL (Fin 2) FinAdele)) := by
  have hZ : IsOpen (Zhat : Set FinAdele) := by
    have h := RestrictedProduct.isOpen_forall_mem (R := fun p : Nat.Primes ↦ ℚ_[p])
      (A := fun p ↦ (PadicInt.subring p : Set ℚ_[p])) isOpen_padicSubring
    convert h using 1
    ext x
    exact mem_zhat
  have : (maxCompactFin : Set (GL (Fin 2) FinAdele)) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin 2) FinAdele ↦ (g : Matrix (Fin 2) (Fin 2) FinAdele) i j) ⁻¹' Zhat ∩
        (fun g : GL (Fin 2) FinAdele ↦ ((g⁻¹ : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele) i j) ⁻¹'
          Zhat) := by
    ext g
    simp only [SetLike.mem_coe, mem_maxCompactFin_iff', Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ ?_
  exact (hZ.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hZ.preimage (Units.continuous_coe_inv.matrix_elem i j))

/-- `g ↦ (g_p)_p` as a monoid hom. -/
noncomputable def finToResHom : GL (Fin 2) FinAdele →* Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]] where
  toFun := gl2FinToResProd
  map_one' := by ext p : 1; exact map_one (compFinPlace p)
  map_mul' g h := by ext p : 1; exact map_mul (compFinPlace p) g h

/-- The entry `(i, j)` of `x ∈ Πʳ_p GL₂(ℚ_p)` as a finite adele. -/
noncomputable def resEntry (x : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]]) (i j : Fin 2) : FinAdele :=
  ⟨fun p ↦ ((x p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, by
    filter_upwards [x.2] with p hp
    exact ((mem_Kp_iff p _).mp hp i j).1⟩

theorem resEntry_apply (x : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]]) (i j : Fin 2) (p : Nat.Primes) :
    resEntry x i j p = ((x p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := rfl

theorem resEntry_mul (x y : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]]) :
    Matrix.of (resEntry (x * y)) = Matrix.of (resEntry x) * Matrix.of (resEntry y) := by
  ext i j p
  simp [resEntry_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem resEntry_one : Matrix.of (resEntry (1 : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]])) = 1 := by
  ext i j p
  by_cases h : i = j <;> simp [resEntry_apply, Matrix.one_apply, h]

/-- `(g_p)_p ↦ g`. -/
noncomputable def resToFin (x : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]]) : GL (Fin 2) FinAdele :=
  ⟨Matrix.of (resEntry x), Matrix.of (resEntry x⁻¹),
    by rw [← resEntry_mul, mul_inv_cancel, resEntry_one],
    by rw [← resEntry_mul, inv_mul_cancel, resEntry_one]⟩

/-- `(a)` of `I.topgrp.thm:gl2-adelic-restricted-product`. -/
noncomputable def finResEquiv : GL (Fin 2) FinAdele ≃ₜ* Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]] where
  toFun := finToResHom
  invFun := resToFin
  left_inv g := by
    apply Units.ext; ext i j p; rfl
  right_inv x := by
    ext p i j; rfl
  map_mul' := finToResHom.map_mul
  continuous_toFun := by
    have : Fact (∀ p : Nat.Primes, IsOpen (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p]))) := ⟨isOpen_Kp⟩
    refine continuous_of_continuousAt_one finToResHom ?_
    have hU := isOpen_maxCompactFin.isOpenEmbedding_subtypeVal
    rw [show (1 : GL (Fin 2) FinAdele) = ((⟨1, maxCompactFin.one_mem⟩ : maxCompactFin) : GL (Fin 2) FinAdele) from rfl,
      ← hU.continuousAt_iff]
    refine Continuous.continuousAt ?_
    refine Continuous.congr (f := RestrictedProduct.structureMap (fun p : Nat.Primes ↦ GL (Fin 2) ℚ_[p])
        (fun p ↦ (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p]))) Filter.cofinite ∘ fun k : maxCompactFin ↦
          fun p : Nat.Primes ↦ (⟨compFinPlace p k, (mem_maxCompactFin_iff k).mp k.2 p⟩ : 𝐊[ℚ_[p]])) ?_
      (fun k ↦ rfl)
    exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun p ↦ ((continuous_compFinPlace p).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    have : Fact (∀ p : Nat.Primes, IsOpen (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p]))) := ⟨isOpen_Kp⟩
    have hhom : ∀ x y, resToFin (x * y) = resToFin x * resToFin y := fun x y ↦ by
      apply Units.ext; exact resEntry_mul x y
    let ψ : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]] →* GL (Fin 2) FinAdele :=
      { toFun := resToFin, map_one' := Units.ext resEntry_one, map_mul' := hhom }
    refine continuous_of_continuousAt_one ψ ?_
    have hU := RestrictedProduct.isOpenEmbedding_structureMap (R := fun p : Nat.Primes ↦ GL (Fin 2) ℚ_[p])
      (A := fun p ↦ (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p]))) isOpen_Kp
    rw [show (1 : Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]]) =
      RestrictedProduct.structureMap _ _ _ (fun p : Nat.Primes ↦ (1 : 𝐊[ℚ_[p]])) from rfl, ← hU.continuousAt_iff]
    refine Continuous.continuousAt ?_
    have hval : ∀ (inv : Bool) (i j : Fin 2), Continuous fun k : (∀ p : Nat.Primes, 𝐊[ℚ_[p]]) ↦
        RestrictedProduct.structureMap (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ (PadicInt.subring p : Set ℚ_[p]))
          Filter.cofinite (fun p ↦ ⟨(((if inv then (k p)⁻¹ else k p : 𝐊[ℚ_[p]]) : GL (Fin 2) ℚ_[p]) :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) i j,
            ((mem_Kp_iff p _).mp (if inv then (k p)⁻¹ else k p).2 i j).1⟩) := by
      intro inv i j
      refine RestrictedProduct.isEmbedding_structureMap.continuous.comp (continuous_pi fun p ↦ ?_)
      refine Continuous.subtype_mk ?_ _
      refine (Units.continuous_val.matrix_elem i j).comp (continuous_subtype_val.comp ?_)
      cases inv
      · exact continuous_apply p
      · exact (continuous_apply p).inv
    rw [Units.continuous_iff]
    exact ⟨continuous_pi fun i ↦ continuous_pi fun j ↦ hval false i j,
      continuous_pi fun i ↦ continuous_pi fun j ↦ hval true i j⟩

theorem Kp_compactSpace (p : Nat.Primes) : CompactSpace (𝐊[ℚ_[p]]) :=
  isCompact_iff_compactSpace.mp (isCompact_Kp p)

/-- (a) `g ↦ (g_p)_p` is an isomorphism of topological groups `G(𝔸_f) ≅ Πʳ_p (GL₂(ℚ_p), K_p)`;
(b) `g ↦ (g_∞, g_f)` is an isomorphism of topological groups `G(𝔸) ≅ GL₂(ℝ) × G(𝔸_f)`. -/
@[tf_id "I.topgrp.thm:gl2-adelic-restricted-product"]
theorem gl2Adelic_restrictedProduct :
    (∃ e : GL (Fin 2) FinAdele ≃ₜ* Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]],
        ∀ g (p : Nat.Primes), e g p = compFinPlace p g) ∧
      ∃ e : GL (Fin 2) Adele ≃ₜ* GL (Fin 2) ℝ × GL (Fin 2) FinAdele, ∀ g, e g = (compInf g, compFin g) :=
  ⟨⟨finResEquiv, fun _ _ ↦ rfl⟩, ⟨glProdEquiv, fun _ ↦ rfl⟩⟩

/-- `G(𝔸)` and `G(𝔸_f)` are locally compact, Hausdorff and second countable. -/
@[tf_id "I.topgrp.thm:gl2-adelic-locally-compact"]
theorem gl2Adelic_locallyCompact :
    (LocallyCompactSpace (GL (Fin 2) Adele) ∧ T2Space (GL (Fin 2) Adele) ∧
        SecondCountableTopology (GL (Fin 2) Adele)) ∧
      LocallyCompactSpace (GL (Fin 2) FinAdele) ∧ T2Space (GL (Fin 2) FinAdele) ∧
        SecondCountableTopology (GL (Fin 2) FinAdele) := by
  have : Fact (∀ p : Nat.Primes, IsOpen (𝐊[ℚ_[p]] : Set (GL (Fin 2) ℚ_[p]))) := ⟨isOpen_Kp⟩
  have := Kp_compactSpace
  have : ∀ p : Nat.Primes, SecondCountableTopology (GL (Fin 2) ℚ_[p]) := fun p ↦
    (Local.gl2_locallyCompact_t2_secondCountable ℚ_[p]).2.2
  have hLf : LocallyCompactSpace (GL (Fin 2) FinAdele) :=
    finResEquiv.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hSf : SecondCountableTopology (GL (Fin 2) FinAdele) :=
    finResEquiv.toHomeomorph.isEmbedding.secondCountableTopology
  obtain ⟨hLr, -, hSr, -⟩ := gl2Real_locallyCompact_t2_secondCountable_borel
  refine ⟨⟨?_, inferInstance, ?_⟩, hLf, inferInstance, hSf⟩
  · exact (glProdEquiv (R := ℝ) (S := FinAdele)).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  · exact (glProdEquiv (R := ℝ) (S := FinAdele)).toHomeomorph.isEmbedding.secondCountableTopology

theorem isOpen_zhat' : IsOpen (Zhat : Set FinAdele) := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun p : Nat.Primes ↦ ℚ_[p])
    (A := fun p ↦ (PadicInt.subring p : Set ℚ_[p])) isOpen_padicSubring
  convert h using 1
  ext x
  exact mem_zhat

theorem gl2Map_sub_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    ((gl2Map f γ : Matrix (Fin 2) (Fin 2) S) - 1) = ((γ : Matrix (Fin 2) (Fin 2) R) - 1).map f := by
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one f (map_zero f) (map_one f)]; rfl

/-- `G(ℚ)` is a discrete closed subgroup of `G(𝔸)`, and `GL₂(ℚ) → G(𝔸)` is injective. -/
@[tf_id "I.topgrp.thm:gl2-rat-discrete"]
theorem gl2Rat_discrete :
    Function.Injective (gl2Map (algebraMap ℚ Adele)) ∧ IsClosed (gl2RatAdelic : Set (GL (Fin 2) Adele)) ∧
      DiscreteTopology gl2RatAdelic := by
  have hinj : Function.Injective (gl2Map (algebraMap ℚ Adele)) := fun γ δ h ↦ by
    apply Units.ext; ext i j
    exact algebraMap_adele_diagonal.1 (congrArg (fun g : GL (Fin 2) Adele ↦ (g : Matrix (Fin 2) (Fin 2) Adele) i j) h)
  have hdisc : DiscreteTopology gl2RatAdelic := by
    apply discreteTopology_of_isOpen_singleton_one
    set V : Set Adele := Set.Ioo (-1 : ℝ) 1 ×ˢ (Zhat : Set FinAdele)
    have hV : IsOpen V := isOpen_Ioo.prod isOpen_zhat'
    set U : Set (GL (Fin 2) Adele) := ⋂ i, ⋂ j,
      (fun g : GL (Fin 2) Adele ↦ ((g : Matrix (Fin 2) (Fin 2) Adele) - 1) i j) ⁻¹' V
    have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      hV.preimage ((Units.continuous_val.sub continuous_const).matrix_elem i j)
    convert hU.preimage continuous_subtype_val
    ext ⟨g, γ, rfl⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, U, Set.mem_iInter, gl2Map_sub_one, Matrix.map_apply]
    constructor
    · intro h i j
      rw [show (⟨_, γ, rfl⟩ : gl2RatAdelic) = 1 ↔ γ = 1 from ⟨fun h1 ↦ hinj (by simpa using congrArg Subtype.val h1),
        fun h1 ↦ by subst h1; ext1; simp⟩] at h
      subst h
      simp [V]
    · intro h
      have hγ : γ = 1 := by
        apply Units.ext; ext i j
        have h0 := rat_discrete.2.2 _ (h i j).1 (h i j).2
        have : ((γ : Matrix (Fin 2) (Fin 2) ℚ) - 1) i j = 0 := h0
        simpa [sub_eq_zero] using this
      subst hγ
      ext1; simp
  exact ⟨hinj, @Subgroup.isClosed_of_discrete _ _ _ _ _ _ hdisc, hdisc⟩

/-- `G(𝔸)` is locally compact, as an instance (B-only plumbing for `I.topgrp.thm:gl2-adelic-locally-compact`). -/
@[tf_aux "I.topgrp.lem:gl2-adelic-locally-compact-instance"]
instance gl2Adele_locallyCompactSpace : LocallyCompactSpace (GL (Fin 2) Adele) :=
  gl2Adelic_locallyCompact.1.1

/-- `G(𝔸_f)` is locally compact, as an instance (B-only plumbing for `I.topgrp.thm:gl2-adelic-locally-compact`). -/
@[tf_aux "I.topgrp.lem:gl2-fin-adelic-locally-compact-instance"]
instance gl2FinAdele_locallyCompactSpace : LocallyCompactSpace (GL (Fin 2) FinAdele) :=
  gl2Adelic_locallyCompact.2.1

/-- `K = {k ∈ G(𝔸) : k_∞ ∈ K_∞, k_p ∈ K_p for all p}`, `K_∞ = O(2)`, `K_p = GL₂(ℤ_p)`. -/
@[tf_id "I.topgrp.def:max-compact-adelic"]
noncomputable def maxCompactAdelic : Subgroup (GL (Fin 2) Adele) :=
  maxCompactReal.comap compInf ⊓ ⨅ p : Nat.Primes, (𝐊[ℚ_[p]]).comap (compPlace p)

theorem image_equiv_eq {X Y : Type*} (e : X ≃ Y) (S : Set X) (T : Set Y) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    e '' S = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (h x).mp hx
  · intro hy; exact ⟨e.symm y, (h _).mpr (by simpa using hy), by simp⟩

theorem mem_maxCompactAdelic_iff (g : GL (Fin 2) Adele) :
    g ∈ maxCompactAdelic ↔ compInf g ∈ maxCompactReal ∧ compFin g ∈ maxCompactFin := by
  simp [maxCompactAdelic, maxCompactFin, Subgroup.mem_iInf, compPlace]

/-- `K_f` is compact open in `G(𝔸_f)`, `K` is compact in `G(𝔸)`; under the isomorphisms of
`I.topgrp.thm:gl2-adelic-restricted-product`, `K_f ↦ Π_p K_p` and `K ↦ K_∞ × K_f`. -/
@[tf_id "I.topgrp.thm:max-compact-adelic-compact"]
theorem maxCompactAdelic_compact :
    IsCompact (maxCompactFin : Set (GL (Fin 2) FinAdele)) ∧ IsOpen (maxCompactFin : Set (GL (Fin 2) FinAdele)) ∧
      IsCompact (maxCompactAdelic : Set (GL (Fin 2) Adele)) ∧
      (∀ e : GL (Fin 2) FinAdele ≃ₜ* Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]],
        (∀ g (p : Nat.Primes), e g p = compFinPlace p g) →
          e '' (maxCompactFin : Set (GL (Fin 2) FinAdele)) = {x | ∀ p : Nat.Primes, x p ∈ 𝐊[ℚ_[p]]}) ∧
      ∀ e : GL (Fin 2) Adele ≃ₜ* GL (Fin 2) ℝ × GL (Fin 2) FinAdele, (∀ g, e g = (compInf g, compFin g)) →
        e '' (maxCompactAdelic : Set (GL (Fin 2) Adele)) =
          (maxCompactReal : Set (GL (Fin 2) ℝ)) ×ˢ (maxCompactFin : Set (GL (Fin 2) FinAdele)) := by
  have hf : ∀ e : GL (Fin 2) FinAdele ≃ₜ* Πʳ p : Nat.Primes, [GL (Fin 2) ℚ_[p], 𝐊[ℚ_[p]]],
      (∀ g (p : Nat.Primes), e g p = compFinPlace p g) →
        e '' (maxCompactFin : Set (GL (Fin 2) FinAdele)) = {x | ∀ p : Nat.Primes, x p ∈ 𝐊[ℚ_[p]]} := by
    intro e he
    refine image_equiv_eq e.toEquiv _ _ fun g ↦ ?_
    simp only [SetLike.mem_coe, mem_maxCompactFin_iff, Set.mem_ofPred_eq]
    exact forall_congr' fun p ↦ by rw [show e.toEquiv g p = compFinPlace p g from he g p]
  have ha : ∀ e : GL (Fin 2) Adele ≃ₜ* GL (Fin 2) ℝ × GL (Fin 2) FinAdele, (∀ g, e g = (compInf g, compFin g)) →
      e '' (maxCompactAdelic : Set (GL (Fin 2) Adele)) =
        (maxCompactReal : Set (GL (Fin 2) ℝ)) ×ˢ (maxCompactFin : Set (GL (Fin 2) FinAdele)) := by
    intro e he
    refine image_equiv_eq e.toEquiv _ _ fun g ↦ ?_
    simp only [SetLike.mem_coe, mem_maxCompactAdelic_iff, Set.mem_prod]
    rw [show e.toEquiv g = (compInf g, compFin g) from he g]
  have hKf : IsCompact (maxCompactFin : Set (GL (Fin 2) FinAdele)) := by
    have h := hf finResEquiv (fun _ _ ↦ rfl)
    have := Kp_compactSpace
    have hc := resProd_box_isCompact (fun p : Nat.Primes ↦ 𝐊[ℚ_[p]])
    rw [← h] at hc
    have := hc.image finResEquiv.symm.continuous
    convert this using 1
    exact (finResEquiv.toEquiv.symm_image_image _).symm
  refine ⟨hKf, isOpen_maxCompactFin, ?_, hf, ha⟩
  have h := ha glProdEquiv (fun _ ↦ rfl)
  have hc := maxCompactReal_isCompact.prod hKf
  rw [← h] at hc
  have := hc.image (glProdEquiv (R := ℝ) (S := FinAdele)).symm.continuous
  convert this using 1
  exact ((glProdEquiv (R := ℝ) (S := FinAdele)).toEquiv.symm_image_image _).symm

/-- `a : ℝˣ → G(𝔸)`, `a(r)_∞ = diag(r, r)`, `a(r)_p = 1`: the scalar matrix with entry `(r, 1) ∈ 𝔸`. -/
@[tf_aux "I.topgrp.def:central-element"]
noncomputable def centralElt : ℝˣ →* GL (Fin 2) Adele :=
  Units.map ((Matrix.scalar (Fin 2) : Adele →+* Matrix (Fin 2) (Fin 2) Adele).toMonoidHom.comp
    ((MonoidHom.id ℝ).prod 1))

/-- The split component of the centre `A_G^+ = {a(r) : r > 0}`. -/
@[tf_id "I.topgrp.def:central-split-component"]
noncomputable def splitComponent : Subgroup (GL (Fin 2) Adele) :=
  (Units.posSubgroup ℝ).map centralElt

theorem exists_diagElt_of_mem_torus' {R : Type*} [CommRing R] {g : GL (Fin 2) R} (hg : g ∈ torus R) :
    ∃ t₁ t₂ : Rˣ, g = diagElt t₁ t₂ := by
  obtain ⟨h01, h10⟩ := hg
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rw [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] at hd
  refine ⟨(isUnit_of_mul_isUnit_left hd).unit, (isUnit_of_mul_isUnit_right hd).unit, ?_⟩
  apply Units.ext; refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp [diagElt, h01, h10]

theorem continuous_det_gl {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Matrix.GeneralLinearGroup.det : GL (Fin 2) R →* Rˣ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

theorem centralElt_val (r : ℝˣ) :
    ((centralElt r : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) =
      Matrix.scalar (Fin 2) (((r : ℝ), (1 : FinAdele)) : Adele) := rfl

theorem continuous_centralElt : Continuous centralElt := by
  refine Units.continuous_map ?_
  show Continuous fun x : ℝ ↦ Matrix.scalar (Fin 2) ((x, (1 : FinAdele)) : Adele)
  exact continuous_pi fun i ↦ continuous_pi fun j ↦ by
    by_cases h : i = j
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply, h, ite_true]
      exact continuous_id.prodMk continuous_const
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply, h, ite_false]
      exact continuous_const

theorem centralElt_mem_center (r : ℝˣ) : centralElt r ∈ Subgroup.center (GL (Fin 2) Adele) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralElt_val]
  exact ((Matrix.scalar_commute _ (fun _ ↦ Commute.all _ _) _).eq).symm

theorem det_centralElt (r : ℝˣ) :
    Matrix.GeneralLinearGroup.det (centralElt r) = ideleInfFin ((r : ℝ) ^ 2) 1 := by
  apply Units.ext
  rw [ideleInfFin_val (pow_ne_zero 2 r.ne_zero)]
  simp [Matrix.GeneralLinearGroup.det, centralElt_val, Matrix.det_fin_two, sq]

theorem ideleNorm_det_centralElt (r : ℝˣ) :
    ideleNorm (Matrix.GeneralLinearGroup.det (centralElt r)) = (r : ℝ) ^ 2 := by
  rw [det_centralElt, ideleNorm_ideleInfFin (pow_ne_zero 2 r.ne_zero), abs_of_nonneg (sq_nonneg _)]

theorem centralElt_injective : Function.Injective centralElt := by
  intro r s h
  have := congrArg (fun g : GL (Fin 2) Adele ↦ ((g : Matrix (Fin 2) (Fin 2) Adele) 0 0).1) h
  simp only [centralElt_val, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

/-- The positive square root of `|det g|_𝔸` as a positive real unit. -/
noncomputable def sqrtNormDet (g : GL (Fin 2) Adele) : ℝˣ :=
  Units.mk0 (Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det g)))
    (Real.sqrt_pos.mpr (ideleNorm_spec.2.1 _)).ne'

theorem sqrtNormDet_pos (g : GL (Fin 2) Adele) : 0 < ((sqrtNormDet g : ℝˣ) : ℝ) :=
  Real.sqrt_pos.mpr (ideleNorm_spec.2.1 _)

theorem continuous_sqrtNormDet : Continuous sqrtNormDet := by
  have hc : Continuous fun g : GL (Fin 2) Adele ↦ Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det g)) :=
    (ideleNorm_spec.1.comp continuous_det_gl).sqrt
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  show Continuous fun g ↦ (Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det g)))⁻¹
  exact hc.inv₀ fun g ↦ (sqrtNormDet_pos g).ne'

/-- `a(r)_∞ = diag(r, r)`, `a(r)_f = 1`; `A_G^+` is central; `r ↦ a(r)` is an isomorphism of topological groups
`ℝ_{>0} ≅ A_G^+` (the claims of `I.topgrp.def:central-split-component`). -/
@[tf_aux "I.topgrp.lem:central-split-component"]
theorem splitComponent_spec :
    (∀ r : ℝˣ, compInf (centralElt r) = diagElt r r ∧ compFin (centralElt r) = 1) ∧
      splitComponent ≤ Subgroup.center (GL (Fin 2) Adele) ∧
      ∃ e : Units.posSubgroup ℝ ≃ₜ* splitComponent, ∀ r, (e r : GL (Fin 2) Adele) = centralElt r := by
  refine ⟨fun r ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Units.ext; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [compInf, gl2Map, centralElt_val, diagElt]
  · apply Units.ext; refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [compFin, gl2Map, centralElt_val]
  · rintro _ ⟨r, -, rfl⟩; exact centralElt_mem_center r
  · let f : Units.posSubgroup ℝ →* splitComponent :=
      { toFun := fun r ↦ ⟨centralElt r, r, r.2, rfl⟩
        map_one' := by ext1; simp
        map_mul' := fun r s ↦ by ext1; simp }
    have hinj : Function.Injective f := fun r s h ↦
      Subtype.ext (centralElt_injective (congrArg Subtype.val h))
    have hsurj : Function.Surjective f := by
      rintro ⟨_, r, hr, rfl⟩; exact ⟨⟨r, hr⟩, rfl⟩
    let e0 := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
    -- inverse: `g ↦ √|det g|`
    have hinv : ∀ g : splitComponent, (e0.symm g : ℝˣ) = sqrtNormDet g := by
      intro g
      obtain ⟨r, rfl⟩ := hsurj g
      refine (congrArg (fun x : Units.posSubgroup ℝ ↦ (x : ℝˣ)) (e0.symm_apply_apply r)).trans ?_
      apply Units.ext
      show ((r : ℝˣ) : ℝ) = Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det (centralElt r)))
      simp only [ideleNorm_det_centralElt, Real.sqrt_sq ((Units.mem_posSubgroup _).mp r.2).le]
    refine ⟨{ e0 with
      continuous_toFun := (continuous_centralElt.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ?_ }, fun r ↦ rfl⟩
    refine Continuous.subtype_mk ?_ _
    exact (continuous_sqrtNormDet.comp continuous_subtype_val).congr fun g ↦ (hinv g).symm

/-- The set `{g : g₁₀ = 0, g₁₁ = 1}` contains `1` and is closed under products and inverses. -/
@[tf_aux "I.topgrp.lem:mirabolic-subgroup"]
theorem mirabolic_isSubgroup (R : Type*) [CommRing R] :
    (1 : GL (Fin 2) R) ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} ∧
      (∀ {g h : GL (Fin 2) R},
        g ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} →
        h ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} →
        g * h ∈
          {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1}) ∧
      ∀ {g : GL (Fin 2) R},
        g ∈ {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} →
        g⁻¹ ∈
          {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} := by
  refine ⟨by simp, fun {g h} hg hh ↦ ?_, fun {g} hg ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    rw [hg.1, hg.2, hh.1, hh.2]; constructor <;> ring
  · simp only [Set.mem_ofPred_eq] at *
    have hdet : (g : Matrix (Fin 2) (Fin 2) R).det = (g : Matrix (Fin 2) (Fin 2) R) 0 0 := by
      rw [Matrix.det_fin_two, hg.1, hg.2]; ring
    have hu : IsUnit (g : Matrix (Fin 2) (Fin 2) R).det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    rw [hg.1, hdet]
    exact ⟨by ring, Ring.inverse_mul_cancel _ (hdet ▸ hu)⟩

/-- The mirabolic subgroup `{(a b; 0 1)} ≤ GL₂(R)`. -/
@[tf_aux "I.topgrp.def:mirabolic"]
def mirabolic (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1}
  one_mem' := (mirabolic_isSubgroup R).1
  mul_mem' := (mirabolic_isSubgroup R).2.1
  inv_mem' := (mirabolic_isSubgroup R).2.2

/-- `GL₂(Ẑ) → G(𝔸_f)`, induced by `Ẑ ⊆ 𝔸_f`. -/
@[tf_aux "I.topgrp.def:gl2-zhat"]
noncomputable def gl2Zhat : GL (Fin 2) Zhat →* GL (Fin 2) FinAdele :=
  gl2Map Zhat.subtype

/-- Reduction `GL₂(Ẑ) → GL₂(Ẑ/NẐ)`. -/
@[tf_aux "I.topgrp.def:gl2-zhat-reduction"]
noncomputable def gl2ZhatRed (N : ℕ) : GL (Fin 2) Zhat →* GL (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)}) :=
  gl2Map (Ideal.Quotient.mk _)

/-- `K_0(N)`: the elements of `K_f` (entries in `Ẑ`) with `k₂₁ ∈ NẐ`. -/
@[tf_id "I.topgrp.def:congruence-subgroups"]
noncomputable def congruenceK0 (N : ℕ) : Subgroup (GL (Fin 2) FinAdele) :=
  ((borel _).comap (gl2ZhatRed N)).map gl2Zhat

/-- `K_1(N)`: the elements of `K_0(N)` with `k₂₂ − 1 ∈ NẐ`. -/
@[tf_aux "I.topgrp.def:congruence-k1"]
noncomputable def congruenceK1 (N : ℕ) : Subgroup (GL (Fin 2) FinAdele) :=
  ((mirabolic _).comap (gl2ZhatRed N)).map gl2Zhat

/-- `K_f(N)`: the elements of `K_f` with `k − 1 ∈ M₂(NẐ)`. -/
@[tf_aux "I.topgrp.def:congruence-kf"]
noncomputable def congruenceKf (N : ℕ) : Subgroup (GL (Fin 2) FinAdele) :=
  (gl2ZhatRed N).ker.map gl2Zhat

theorem gl2Zhat_injective : Function.Injective gl2Zhat := fun h h' e ↦ by
  apply Units.ext; refine Matrix.ext fun i j ↦ Subtype.ext ?_
  exact (congrArg (fun g : GL (Fin 2) FinAdele ↦ (g : Matrix (Fin 2) (Fin 2) FinAdele) i j) e)

theorem mem_maxCompactFin_iff_gl2Zhat (k : GL (Fin 2) FinAdele) :
    k ∈ maxCompactFin ↔ ∃ h : GL (Fin 2) Zhat, gl2Zhat h = k := by
  rw [mem_maxCompactFin_iff']
  constructor
  · intro hk
    have hinjM : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) Zhat ↦ A.map Zhat.subtype) :=
      fun A B e ↦ Matrix.ext fun i j ↦ Subtype.ext (congrFun (congrFun e i) j)
    set A : Matrix (Fin 2) (Fin 2) Zhat := Matrix.of fun i j ↦ ⟨_, (hk i j).1⟩
    set B : Matrix (Fin 2) (Fin 2) Zhat := Matrix.of fun i j ↦ ⟨_, (hk i j).2⟩
    have hA : A.map Zhat.subtype = k := rfl
    have hB : B.map Zhat.subtype = ((k⁻¹ : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele) := rfl
    have hAB : A * B = 1 := hinjM (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact_mod_cast k.mul_inv)
    have hBA : B * A = 1 := hinjM (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact_mod_cast k.inv_mul)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩
  · rintro ⟨h, rfl⟩ i j
    refine ⟨(h : Matrix (Fin 2) (Fin 2) Zhat) i j |>.2, ?_⟩
    rw [← map_inv]
    exact ((h⁻¹ : GL (Fin 2) Zhat) : Matrix (Fin 2) (Fin 2) Zhat) i j |>.2

theorem gl2Zhat_apply (h : GL (Fin 2) Zhat) (i j : Fin 2) :
    (gl2Zhat h : Matrix (Fin 2) (Fin 2) FinAdele) i j = ((h : Matrix (Fin 2) (Fin 2) Zhat) i j : FinAdele) := rfl

theorem quot_mk_eq_iff (N : ℕ) (x y : Zhat) :
    Ideal.Quotient.mk (Ideal.span {(N : Zhat)}) x = Ideal.Quotient.mk _ y ↔
      ∃ z ∈ Zhat, (x : FinAdele) - y = N * z := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, b.2, ?_⟩
    have := congrArg (fun z : Zhat ↦ (z : FinAdele)) hb
    simp only [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub] at this
    exact this.symm.trans (mul_comm _ _)
  · rintro ⟨z, hz, hxy⟩
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub]
    exact (mul_comm _ _).trans hxy.symm

theorem red_apply (N : ℕ) (h : GL (Fin 2) Zhat) (i j : Fin 2) :
    (gl2ZhatRed N h : Matrix (Fin 2) (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)})) i j =
      Ideal.Quotient.mk _ ((h : Matrix (Fin 2) (Fin 2) Zhat) i j) := rfl

theorem one_quot_apply (N : ℕ) (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)})) i j =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin 2) (Fin 2) Zhat) i j) := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The congruence subgroups, explicitly: for `N ≥ 1`, `K_0(N) = {k ∈ K_f : k₂₁ ∈ NẐ}`,
`K_1(N) = {k ∈ K_0(N) : k₂₂ − 1 ∈ NẐ}`, `K_f(N) = {k ∈ K_f : k − 1 ∈ M₂(NẐ)}`, and
`K_f(N) ≤ K_1(N) ≤ K_0(N) ≤ K_f` (the claims of `I.topgrp.def:congruence-subgroups`). -/
@[tf_aux "I.topgrp.lem:congruence-subgroups-explicit"]
theorem congruence_explicit (N : ℕ) (hN : 1 ≤ N) :
    (∀ k : GL (Fin 2) FinAdele, k ∈ congruenceK0 N ↔
        k ∈ maxCompactFin ∧ ∃ z ∈ Zhat, (k : Matrix (Fin 2) (Fin 2) FinAdele) 1 0 = N * z) ∧
      (∀ k : GL (Fin 2) FinAdele, k ∈ congruenceK1 N ↔
        k ∈ congruenceK0 N ∧ ∃ z ∈ Zhat, (k : Matrix (Fin 2) (Fin 2) FinAdele) 1 1 - 1 = N * z) ∧
      (∀ k : GL (Fin 2) FinAdele, k ∈ congruenceKf N ↔
        k ∈ maxCompactFin ∧ ∀ i j, ∃ z ∈ Zhat, ((k : Matrix (Fin 2) (Fin 2) FinAdele) - 1) i j = N * z) ∧
      congruenceKf N ≤ congruenceK1 N ∧ congruenceK1 N ≤ congruenceK0 N ∧ congruenceK0 N ≤ maxCompactFin := by
  have _h := hN
  -- membership through the unique preimage in `GL₂(Ẑ)`
  have hmap : ∀ (H : Subgroup (GL (Fin 2) Zhat)) (k : GL (Fin 2) FinAdele),
      k ∈ H.map gl2Zhat ↔ ∃ h : GL (Fin 2) Zhat, gl2Zhat h = k ∧ h ∈ H := by
    intro H k
    simp only [Subgroup.mem_map]
    exact ⟨fun ⟨h, hH, e⟩ ↦ ⟨h, e, hH⟩, fun ⟨h, e, hH⟩ ↦ ⟨h, hH, e⟩⟩
  have hB : ∀ h : GL (Fin 2) Zhat, h ∈ (borel _).comap (gl2ZhatRed N) ↔
      ∃ z ∈ Zhat, ((h : Matrix (Fin 2) (Fin 2) Zhat) 1 0 : FinAdele) = N * z := by
    intro h
    show (gl2ZhatRed N h : Matrix (Fin 2) (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)})) 1 0 = 0 ↔ _
    rw [red_apply, ← map_zero (Ideal.Quotient.mk _), quot_mk_eq_iff]
    simp
  have hM : ∀ h : GL (Fin 2) Zhat, h ∈ (mirabolic _).comap (gl2ZhatRed N) ↔
      (∃ z ∈ Zhat, ((h : Matrix (Fin 2) (Fin 2) Zhat) 1 0 : FinAdele) = N * z) ∧
        ∃ z ∈ Zhat, ((h : Matrix (Fin 2) (Fin 2) Zhat) 1 1 : FinAdele) - 1 = N * z := by
    intro h
    show (gl2ZhatRed N h : Matrix (Fin 2) (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)})) 1 0 = 0 ∧ (gl2ZhatRed N h : Matrix (Fin 2) (Fin 2) (Zhat ⧸ Ideal.span {(N : Zhat)})) 1 1 = 1 ↔ _
    rw [red_apply, red_apply, ← map_zero (Ideal.Quotient.mk _), ← map_one (Ideal.Quotient.mk _), quot_mk_eq_iff,
      quot_mk_eq_iff]
    simp
  have hK : ∀ h : GL (Fin 2) Zhat, h ∈ (gl2ZhatRed N).ker ↔
      ∀ i j, ∃ z ∈ Zhat, ((h : Matrix (Fin 2) (Fin 2) Zhat) i j : FinAdele) -
        ((1 : Matrix (Fin 2) (Fin 2) Zhat) i j : FinAdele) = N * z := by
    intro h
    rw [MonoidHom.mem_ker, Units.ext_iff]
    simp only [Units.val_one]
    rw [← Matrix.ext_iff]
    simp only [red_apply, one_quot_apply, quot_mk_eq_iff]
  have h0 : ∀ k, k ∈ congruenceK0 N ↔ k ∈ maxCompactFin ∧ ∃ z ∈ Zhat,
      (k : Matrix (Fin 2) (Fin 2) FinAdele) 1 0 = N * z := by
    intro k
    rw [congruenceK0, hmap, mem_maxCompactFin_iff_gl2Zhat]
    constructor
    · rintro ⟨h, rfl, hh⟩; exact ⟨⟨h, rfl⟩, (hB h).mp hh⟩
    · rintro ⟨⟨h, rfl⟩, hz⟩; exact ⟨h, rfl, (hB h).mpr hz⟩
  have h1 : ∀ k, k ∈ congruenceK1 N ↔ k ∈ congruenceK0 N ∧ ∃ z ∈ Zhat,
      (k : Matrix (Fin 2) (Fin 2) FinAdele) 1 1 - 1 = N * z := by
    intro k
    rw [congruenceK1, hmap, congruenceK0, hmap]
    constructor
    · rintro ⟨h, rfl, hh⟩
      exact ⟨⟨h, rfl, (hB h).mpr ((hM h).mp hh).1⟩, ((hM h).mp hh).2⟩
    · rintro ⟨⟨h, rfl, hh⟩, hz⟩
      exact ⟨h, rfl, (hM h).mpr ⟨(hB h).mp hh, hz⟩⟩
  have hf : ∀ k, k ∈ congruenceKf N ↔ k ∈ maxCompactFin ∧ ∀ i j, ∃ z ∈ Zhat,
      ((k : Matrix (Fin 2) (Fin 2) FinAdele) - 1) i j = N * z := by
    intro k
    have h1M : ∀ i j, ((1 : Matrix (Fin 2) (Fin 2) Zhat) i j : FinAdele) =
        (1 : Matrix (Fin 2) (Fin 2) FinAdele) i j := fun i j ↦ by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [congruenceKf, hmap, mem_maxCompactFin_iff_gl2Zhat]
    constructor
    · rintro ⟨h, rfl, hh⟩
      refine ⟨⟨h, rfl⟩, fun i j ↦ ?_⟩
      obtain ⟨z, hz, e⟩ := (hK h).mp hh i j
      exact ⟨z, hz, by rw [Matrix.sub_apply, gl2Zhat_apply, ← h1M, e]⟩
    · rintro ⟨⟨h, rfl⟩, hz⟩
      refine ⟨h, rfl, (hK h).mpr fun i j ↦ ?_⟩
      obtain ⟨z, hz', e⟩ := hz i j
      exact ⟨z, hz', by rw [h1M, ← gl2Zhat_apply, ← Matrix.sub_apply, e]⟩
  refine ⟨h0, h1, hf, fun k hk ↦ ?_, fun k hk ↦ ((h1 k).mp hk).1, fun k hk ↦ ((h0 k).mp hk).1⟩
  rw [congruenceKf, hmap] at hk
  obtain ⟨h, rfl, hh⟩ := hk
  rw [congruenceK1, hmap]
  refine ⟨h, rfl, (hM h).mpr ⟨?_, ?_⟩⟩
  · obtain ⟨z, hz, e⟩ := (hK h).mp hh 1 0
    exact ⟨z, hz, by simpa using e⟩
  · obtain ⟨z, hz, e⟩ := (hK h).mp hh 1 1
    exact ⟨z, hz, by simpa using e⟩

/-- Step 1 of `I.topgrp.thm:sl2-reduction-surjective`: a coprime lift of `(c, d)` modulo `N`. -/
theorem exists_coprime_lift (N : ℕ) (hN : 1 ≤ N) (c d : ℤ)
    (hcdN : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ d → ¬ (p : ℤ) ∣ N) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD N] ∧ d' ≡ d [ZMOD N] ∧ IsCoprime c' d' := by
  classical
  set c' : ℤ := if c = 0 then N else c with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc']; split_ifs with h
    · exact_mod_cast (show N ≠ 0 by omega)
    · exact h
  have hc'c : c' ≡ c [ZMOD N] := by
    rw [hc']; split_ifs with h
    · rw [h]; exact (Int.modEq_zero_iff_dvd.mpr dvd_rfl)
    · exact Int.ModEq.refl _
  have hP : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c' → (p : ℤ) ∣ d → ¬ (p : ℤ) ∣ N := by
    intro p hp h1 h2
    rw [hc'] at h1; split_ifs at h1 with h
    · exact hcdN p hp (h ▸ dvd_zero _) h2
    · exact hcdN p hp h1 h2
  set S : Finset ℕ := Finset.filter (fun p : ℕ ↦ ¬ (p : ℤ) ∣ d) c'.natAbs.primeFactors
  set t : ℤ := ∏ p ∈ S, (p : ℤ)
  refine ⟨c', d + t * N, hc'c, ?_, ?_⟩
  · exact (Int.modEq_iff_dvd.mpr ⟨t, by ring⟩).symm
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
  refine Nat.coprime_of_dvd fun k hk hkc hkd ↦ ?_
  have hkc' : (k : ℤ) ∣ c' := Int.natCast_dvd.mpr hkc
  have hkd' : (k : ℤ) ∣ d + t * N := Int.natCast_dvd.mpr hkd
  have hkS : k ∈ c'.natAbs.primeFactors := Nat.mem_primeFactors.mpr ⟨hk, hkc, Int.natAbs_ne_zero.mpr hc'0⟩
  have hkprime : Prime (k : ℤ) := Nat.prime_iff_prime_int.mp hk
  by_cases hkd0 : (k : ℤ) ∣ d
  · have htN : (k : ℤ) ∣ t * N := by
      have := dvd_sub hkd' hkd0
      simpa using this
    rcases hkprime.dvd_or_dvd htN with ht | hN'
    · obtain ⟨p, hpS, hkp⟩ := (Prime.dvd_finsetProd_iff hkprime _).mp ht
      have hpS' := Finset.mem_filter.mp hpS
      have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpS'.1).1
      have hkp' : k = p := (Nat.prime_dvd_prime_iff_eq hk hpprime).mp (Int.natCast_dvd_natCast.mp hkp)
      exact hpS'.2 (hkp' ▸ hkd0)
    · exact hP k hk hkc' hkd0 hN'
  · have hkt : (k : ℤ) ∣ t := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hkS, hkd0⟩)
    apply hkd0
    have := dvd_sub hkd' (dvd_mul_of_dvd_left hkt (N : ℤ))
    simpa using this

/-- For `N ≥ 1`, reduction `SL₂(ℤ) → SL₂(ℤ/Nℤ)` is surjective. -/
@[tf_id "I.topgrp.thm:sl2-reduction-surjective"]
theorem sl2_reduction_surjective (N : ℕ) (hN : 1 ≤ N) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) :
        Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) := by
  have : NeZero N := ⟨by omega⟩
  intro g
  set a : ℤ := ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).cast
  set b : ℤ := ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).cast
  set c : ℤ := ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).cast
  set d : ℤ := ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).cast
  have ha : (a : ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 := ZMod.intCast_zmod_cast _
  have hb : (b : ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1 := ZMod.intCast_zmod_cast _
  have hc : (c : ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 := ZMod.intCast_zmod_cast _
  have hd : (d : ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1 := ZMod.intCast_zmod_cast _
  have hdet : ((a * d - b * c : ℤ) : ZMod N) = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    push_cast
    rw [ha, hb, hc, hd, this]
  have hdet' : a * d - b * c ≡ 1 [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast at hdet ⊢; exact hdet
  obtain ⟨c', d', hcc, hdd, hcop⟩ := exists_coprime_lift N hN c d (by
    intro p hp hpc hpd hpN
    have h1 : (p : ℤ) ∣ a * d - b * c := dvd_sub (dvd_mul_of_dvd_right hpd a) (dvd_mul_of_dvd_right hpc b)
    have h2 : (p : ℤ) ∣ a * d - b * c - 1 := hpN.trans (Int.ModEq.dvd hdet'.symm)
    have h3 : (p : ℤ) ∣ 1 := by simpa using dvd_sub h1 h2
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3))
  have hdet2 : a * d' - b * c' ≡ 1 [ZMOD N] :=
    ((Int.ModEq.mul_left a hdd).sub (Int.ModEq.mul_left b hcc)).trans hdet'
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hdet2.symm)
  -- hk : a * d' - b * c' - 1 = N * k
  obtain ⟨u, v, huv⟩ := hcop
  -- u * c' + v * d' = 1
  set a' := a - k * N * v
  set b' := b + k * N * u
  have hdet3 : a' * d' - b' * c' = 1 := by
    have : a * d' - b * c' = 1 + N * k := by linarith
    linear_combination this - (k * N) * huv
  refine ⟨⟨!![a', b'; c', d'], by rw [Matrix.det_fin_two_of]; exact hdet3⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · show ((a - k * N * v : ℤ) : ZMod N) = _
    push_cast; rw [ha]; simp
  · show ((b + k * N * u : ℤ) : ZMod N) = _
    push_cast; rw [hb]; simp
  · simp [Matrix.SpecialLinearGroup.map]
    rw [← hc]; exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hcc
  · simp [Matrix.SpecialLinearGroup.map]
    rw [← hd]; exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hdd

theorem dense_rat_finAdele : Dense (Set.range (algebraMap ℚ FinAdele)) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  -- pull `U - x` back to a neighbourhood of `0` in `Ẑ`
  have h0 : (fun z : Zhat ↦ x + (z : FinAdele)) ⁻¹' U ∈ 𝓝 (0 : Zhat) := by
    have hc : Continuous fun z : Zhat ↦ x + (z : FinAdele) := continuous_const.add continuous_subtype_val
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN⟩ := zhat_exists_dvd_subset _ h0
  obtain ⟨q₀, hq₀⟩ := RestrictedProduct.padic_exists_sub_mem_structureSubring x
  have hz : x - algebraMap ℚ FinAdele q₀ ∈ Zhat := mem_zhat.mpr fun p ↦
    RestrictedProduct.mem_structureSubring_iff.mp hq₀ p
  set z : Zhat := ⟨_, hz⟩
  set m : ℤ := ((zhatReduction N z).val : ℤ)
  have hm : z - (m : Zhat) ∈ Ideal.span {((N : ℕ) : Zhat)} := by
    have hk := (zhatReduction_spec N).1
    have : z - (m : Zhat) ∈ RingHom.ker (zhatReduction N) := by
      rw [RingHom.mem_ker, map_sub, (zhatReduction_spec N).2 m]
      simp [m]
    rwa [hk] at this
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hm
  refine ⟨algebraMap ℚ FinAdele (q₀ + m), ?_, ⟨_, rfl⟩⟩
  have := hN (-b)
  simp only [Set.mem_preimage] at this
  convert this using 1
  have hb' : ((b * ((N : ℕ) : Zhat) : Zhat) : FinAdele) = (x - algebraMap ℚ FinAdele q₀) - (m : FinAdele) := by
    rw [hb]; rfl
  simp only [Subring.coe_mul, Subring.coe_natCast] at hb'
  simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_neg, map_add, map_intCast]
  linear_combination hb'

open Classical in
theorem local_lower_left_choice (p : Nat.Primes) (a b c d : ℚ_[p]) (hdet : a * d - b * c = 1) :
    c + (if c ≠ 0 ∧ ‖a‖ ≤ ‖c‖ then 0 else 1) * a ≠ 0 ∧
      (‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ‖d‖ ≤ 1 → ‖c + (if c ≠ 0 ∧ ‖a‖ ≤ ‖c‖ then 0 else 1) * a‖ = 1) := by
  have hmax : ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ‖d‖ ≤ 1 → max ‖a‖ ‖c‖ = 1 := by
    intro ha hb hc hd
    refine le_antisymm (max_le ha hc) ?_
    have h1 : ‖a * d - b * c‖ ≤ max ‖a * d‖ ‖b * c‖ := by
      rw [sub_eq_add_neg]
      exact (Padic.nonarchimedean _ _).trans (by rw [norm_neg])
    rw [hdet, norm_one, norm_mul, norm_mul] at h1
    refine h1.trans (max_le ?_ ?_)
    · exact (mul_le_of_le_one_right (norm_nonneg _) hd).trans (le_max_left _ _)
    · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (le_max_right _ _)
  split_ifs with h
  · simp only [zero_mul, add_zero]
    refine ⟨h.1, fun ha hb hc hd ↦ ?_⟩
    have := hmax ha hb hc hd
    rwa [max_eq_right h.2] at this
  · simp only [one_mul]
    by_cases hc0 : c = 0
    · subst hc0
      have ha0 : a ≠ 0 := by rintro rfl; simp at hdet
      refine ⟨by simpa using ha0, fun ha hb hc hd ↦ ?_⟩
      have := hmax ha hb hc hd
      simp only [norm_zero, zero_add] at this ⊢
      rwa [max_eq_left (norm_nonneg _)] at this
    · have hlt : ‖c‖ < ‖a‖ := by
        push Not at h
        exact h hc0
      have heq : ‖c + a‖ = ‖a‖ := by
        rw [Padic.add_eq_max_of_ne hlt.ne, max_eq_right hlt.le]
      refine ⟨fun h0 ↦ ?_, fun ha hb hc hd ↦ ?_⟩
      · rw [h0, norm_zero] at heq
        exact (norm_nonneg c).not_gt (heq ▸ hlt)
      · have := hmax ha hb hc hd
        rwa [max_eq_left hlt.le, ← heq] at this

theorem isUnit_subring_of_norm (p : Nat.Primes) (x : ℚ_[p]) (hx : ‖x‖ = 1) :
    ∃ h : x ∈ PadicInt.subring p, IsUnit (⟨x, h⟩ : PadicInt.subring p) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  refine ⟨(PadicInt.mem_subring_iff (p : ℕ)).mpr hx.le, isUnit_iff_exists.mpr ⟨⟨x⁻¹, ?_⟩, ?_, ?_⟩⟩
  · rw [PadicInt.mem_subring_iff (p : ℕ), norm_inv, hx, inv_one]
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

open Classical in
theorem exists_lower_left_unit (a b c d : FinAdele) (hdet : a * d - b * c = 1) :
    ∃ t : FinAdele, IsUnit (c + t * a) := by
  let t : FinAdele := ⟨fun p ↦ if c p ≠ 0 ∧ ‖a p‖ ≤ ‖c p‖ then 0 else 1,
    Filter.Eventually.of_forall fun p ↦ by
      show (if c p ≠ 0 ∧ ‖a p‖ ≤ ‖c p‖ then 0 else 1) ∈ (PadicInt.subring p : Set ℚ_[p])
      split_ifs
      · exact (PadicInt.subring p).zero_mem
      · exact (PadicInt.subring p).one_mem⟩
  have hdetp : ∀ p : Nat.Primes, a p * d p - b p * c p = 1 := fun p ↦ by
    have := congrArg (fun x : FinAdele ↦ x p) hdet
    simpa using this
  refine ⟨t, RestrictedProduct.isUnit_iff.mpr ⟨fun p ↦ ?_, ?_⟩⟩
  · exact isUnit_iff_ne_zero.mpr (local_lower_left_choice p _ _ _ _ (hdetp p)).1
  · filter_upwards [a.2, b.2, c.2, d.2] with p ha hb hc hd
    have key := (local_lower_left_choice p _ _ _ _ (hdetp p)).2 ((PadicInt.mem_subring_iff (p : ℕ)).mp ha)
      ((PadicInt.mem_subring_iff (p : ℕ)).mp hb) ((PadicInt.mem_subring_iff (p : ℕ)).mp hc)
      ((PadicInt.mem_subring_iff (p : ℕ)).mp hd)
    exact isUnit_subring_of_norm p _ key

theorem continuous_upperRightHom_adelic {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R ↦ (Matrix.GeneralLinearGroup.upperRightHom x : GL (Fin 2) R) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom, Units.inv_mk] <;> fun_prop

theorem continuous_oppositeUnipotentHom {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R ↦ (oppositeUnipotentHom x : GL (Fin 2) R) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [oppositeUnipotentHom, oppositeUnipotentElt] <;> fun_prop
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [oppositeUnipotentHom, oppositeUnipotentElt, Units.inv_mk] <;> fun_prop

theorem lower_left_decomp_mat {R : Type*} [CommRing R] (a b c d t u v : R) (hdet : a * d - b * c = 1)
    (hv : u * v = 1) (hc : u = c + t * a) :
    !![(1 : R), 0; t, 1] * !![a, b; c, d] =
      !![(1 : R), (a - 1) * v; 0, 1] * !![(1 : R), 0; u, 1] * !![(1 : R), (d + t * b - 1) * v; 0, 1] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -(a - 1) * hv
  · linear_combination -((a - 1) * (d + t * b - 1) * v + b) * hv - v * hdet + v * b * hc
  · linear_combination -hc
  · linear_combination -(d + t * b - 1) * hv

theorem lower_left_decomp {R : Type*} [CommRing R] (g : GL (Fin 2) R)
    (hdet : (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 1)
    (t : R) (u : Rˣ) (hc : (u : R) = (g : Matrix (Fin 2) (Fin 2) R) 1 0 + t * (g : Matrix (Fin 2) (Fin 2) R) 0 0) :
    oppositeUnipotentHom t * g =
      Matrix.GeneralLinearGroup.upperRightHom (((g : Matrix (Fin 2) (Fin 2) R) 0 0 - 1) * (u⁻¹ : Rˣ)) *
        oppositeUnipotentHom (u : R) *
        Matrix.GeneralLinearGroup.upperRightHom
          (((g : Matrix (Fin 2) (Fin 2) R) 1 1 + t * (g : Matrix (Fin 2) (Fin 2) R) 0 1 - 1) * (u⁻¹ : Rˣ)) := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R)]
  exact lower_left_decomp_mat _ _ _ _ t u _ hdet u.mul_inv hc

theorem det_gl2Map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (gl2Map f γ) = Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, gl2Map, RingHom.map_det]

/-- `SL₂(ℚ)` is dense in `SL₂(𝔸_f) = {g ∈ G(𝔸_f) : det g = 1}` (subspace topology). -/
@[tf_id "I.topgrp.thm:sl2-strong-approximation"]
theorem sl2_strong_approximation :
    Dense ((Matrix.GeneralLinearGroup.det : GL (Fin 2) FinAdele →* FinAdeleˣ).ker.subtype ⁻¹'
      (gl2Map (algebraMap ℚ FinAdele) '' {γ : GL (Fin 2) ℚ | Matrix.GeneralLinearGroup.det γ = 1})) := by
  set S := gl2Map (algebraMap ℚ FinAdele) '' {γ : GL (Fin 2) ℚ | Matrix.GeneralLinearGroup.det γ = 1}
  let Γ : Subgroup (GL (Fin 2) FinAdele) :=
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) ℚ →* ℚˣ).ker.map (gl2Map (algebraMap ℚ FinAdele))
  have hΓS : (Γ : Set (GL (Fin 2) FinAdele)) = S := by
    ext g; simp [Γ, S, MonoidHom.mem_ker]
  let H := Γ.topologicalClosure
  have hHS : (H : Set (GL (Fin 2) FinAdele)) = closure S := by
    rw [Subgroup.topologicalClosure_coe, hΓS]
  have hSker : S ⊆ (Matrix.GeneralLinearGroup.det : GL (Fin 2) FinAdele →* FinAdeleˣ).ker := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, det_gl2Map, show Matrix.GeneralLinearGroup.det γ = 1 from hγ, map_one]
  -- the elementary matrices lie in `H`
  have hel : ∀ (φ : FinAdele → GL (Fin 2) FinAdele), Continuous φ →
      (∀ q : ℚ, φ (algebraMap ℚ FinAdele q) ∈ Γ) → ∀ x, φ x ∈ H := by
    intro φ hφ hq x
    have h1 := mem_closure_image hφ.continuousAt (dense_rat_finAdele x)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    refine closure_mono ?_ h1
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact hq q
  have hN : ∀ x : FinAdele, Matrix.GeneralLinearGroup.upperRightHom x ∈ H :=
    hel _ continuous_upperRightHom_adelic fun q ↦ ⟨Matrix.GeneralLinearGroup.upperRightHom q, by
      rw [SetLike.mem_coe, MonoidHom.mem_ker]; apply Units.ext; simp [Matrix.GeneralLinearGroup.det], by
      apply Units.ext; refine Matrix.ext fun i j ↦ ?_; fin_cases i <;> fin_cases j <;> simp [gl2Map]⟩
  have hN' : ∀ x : FinAdele, oppositeUnipotentHom x ∈ H :=
    hel _ continuous_oppositeUnipotentHom fun q ↦ ⟨oppositeUnipotentHom q, by
      rw [SetLike.mem_coe, MonoidHom.mem_ker]; apply Units.ext
      simp [Matrix.GeneralLinearGroup.det, oppositeUnipotentHom, oppositeUnipotentElt], by
      apply Units.ext; refine Matrix.ext fun i j ↦ ?_
      fin_cases i <;> fin_cases j <;> simp [gl2Map, oppositeUnipotentHom, oppositeUnipotentElt]⟩
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  rintro ⟨g, hg⟩
  refine closure_mono (s := S) (fun x hx ↦ ?_) ?_
  · exact ⟨⟨x, hSker hx⟩, hx, rfl⟩
  show g ∈ closure S
  rw [← hHS]
  -- `g ∈ SL₂(𝔸_f)`: write `n̄(t) g = n(x) n̄(u) n(z)`
  have hdet : (g : Matrix (Fin 2) (Fin 2) FinAdele) 0 0 * (g : Matrix (Fin 2) (Fin 2) FinAdele) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) FinAdele) 0 1 * (g : Matrix (Fin 2) (Fin 2) FinAdele) 1 0 = 1 := by
    have := congrArg (fun u : FinAdeleˣ ↦ (u : FinAdele)) (MonoidHom.mem_ker.mp hg)
    simpa [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two] using this
  obtain ⟨t, ht⟩ := exists_lower_left_unit _ _ _ _ hdet
  have hdec := lower_left_decomp g hdet t ht.unit (by rw [IsUnit.unit_spec])
  have hg' : g = (oppositeUnipotentHom t)⁻¹ * (oppositeUnipotentHom t * g) := (inv_mul_cancel_left _ _).symm
  rw [hdec] at hg'
  rw [SetLike.mem_coe, hg']
  exact H.mul_mem (H.inv_mem (hN' t)) (H.mul_mem (H.mul_mem (hN _) (hN' _)) (hN _))

/-- `h ↦ (h, 1)`. -/
noncomputable def infEmb : GL (Fin 2) ℝ →* GL (Fin 2) Adele :=
  (glProdEquiv (R := ℝ) (S := FinAdele)).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ _)

/-- `k ↦ (1, k)`. -/
noncomputable def finEmb : GL (Fin 2) FinAdele →* GL (Fin 2) Adele :=
  (glProdEquiv (R := ℝ) (S := FinAdele)).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

theorem comp_eq (g : GL (Fin 2) Adele) : (compInf g, compFin g) = glProdEquiv g := rfl

theorem compInf_infEmb (a : GL (Fin 2) ℝ) : compInf (infEmb a) = a :=
  congrArg Prod.fst ((glProdEquiv (R := ℝ) (S := FinAdele)).apply_symm_apply (a, 1) :)

theorem compFin_infEmb (a : GL (Fin 2) ℝ) : compFin (infEmb a) = 1 :=
  congrArg Prod.snd ((glProdEquiv (R := ℝ) (S := FinAdele)).apply_symm_apply (a, 1) :)

theorem compInf_finEmb (k : GL (Fin 2) FinAdele) : compInf (finEmb k) = 1 :=
  congrArg Prod.fst ((glProdEquiv (R := ℝ) (S := FinAdele)).apply_symm_apply (1, k) :)

theorem compFin_finEmb (k : GL (Fin 2) FinAdele) : compFin (finEmb k) = k :=
  congrArg Prod.snd ((glProdEquiv (R := ℝ) (S := FinAdele)).apply_symm_apply (1, k) :)

theorem gl_adele_ext {g g' : GL (Fin 2) Adele} (h1 : compInf g = compInf g') (h2 : compFin g = compFin g') :
    g = g' :=
  (glProdEquiv (R := ℝ) (S := FinAdele)).injective (by rw [← comp_eq, ← comp_eq, h1, h2])

theorem compInf_rat (γ : GL (Fin 2) ℚ) :
    compInf (gl2Map (algebraMap ℚ Adele) γ) = gl2Map (algebraMap ℚ ℝ) γ := by
  apply Units.ext; refine Matrix.ext fun i j ↦ ?_
  simp [compInf, gl2Map]

theorem compFin_rat (γ : GL (Fin 2) ℚ) :
    compFin (gl2Map (algebraMap ℚ Adele) γ) = gl2Map (algebraMap ℚ FinAdele) γ := rfl

/-- The claim in the proof of `I.topgrp.thm:strong-approximation`. -/
theorem strong_approx_claim (K' : Subgroup (GL (Fin 2) FinAdele)) (hK'o : IsOpen (K' : Set (GL (Fin 2) FinAdele)))
    (g : GL (Fin 2) Adele) (q : ℚˣ) (r : ℝ) (hr : 0 < r) (u : Zhatˣ)
    (hg : Matrix.GeneralLinearGroup.det g = ratIdele q * ideleInfFin r u) (δ : GL (Fin 2) FinAdele)
    (hδ : Matrix.GeneralLinearGroup.det δ = Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom u) :
    ∃ (γ : GL (Fin 2) ℚ) (a : GL (Fin 2) ℝ) (k : GL (Fin 2) FinAdele), a ∈ Matrix.GLPos (Fin 2) ℝ ∧ k ∈ K' ∧
      g = gl2Map (algebraMap ℚ Adele) γ * infEmb a * finEmb (δ * k) := by
  set γ₀ : GL (Fin 2) ℚ := diagElt q 1
  have hγ₀ : Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ₀) = ratIdele q := by
    rw [det_gl2Map]; apply Units.ext
    simp [γ₀, Matrix.GeneralLinearGroup.det, diagElt, Matrix.det_fin_two, ratIdele]
  set g₁ := (gl2Map (algebraMap ℚ Adele) γ₀)⁻¹ * g
  have hg₁ : Matrix.GeneralLinearGroup.det g₁ = ideleInfFin r u := by
    rw [map_mul, map_inv, hγ₀, hg, inv_mul_cancel_left]
  have hg₁f : Matrix.GeneralLinearGroup.det (compFin g₁) =
      Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom u := by
    rw [compFin, det_gl2Map, hg₁]; apply Units.ext
    simp [ideleInfFin_val hr.ne']
  have hg₁i : 0 < (compInf g₁ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    have : ((Matrix.GeneralLinearGroup.det (compInf g₁) : ℝˣ) : ℝ) = r := by
      rw [compInf, det_gl2Map, hg₁]
      simp [ideleInfFin_val hr.ne']
    have h3 : (compInf g₁ : Matrix (Fin 2) (Fin 2) ℝ).det = r := this
    exact h3 ▸ hr
  -- density of `SL₂(ℚ)` in the open set `g₁,f K' δ⁻¹ ∩ SL₂(𝔸_f)`
  set W : Set (GL (Fin 2) FinAdele) := (fun y ↦ (compFin g₁)⁻¹ * y * δ) ⁻¹' K'
  have hW : IsOpen W := hK'o.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  set SL := (Matrix.GeneralLinearGroup.det : GL (Fin 2) FinAdele →* FinAdeleˣ).ker
  have hs : compFin g₁ * δ⁻¹ ∈ SL := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hg₁f, hδ, mul_inv_cancel]
  obtain ⟨⟨_, hy⟩, hyW, ⟨γ₁, hγ₁, rfl⟩⟩ := sl2_strong_approximation.inter_open_nonempty (Subtype.val ⁻¹' W)
    (hW.preimage continuous_subtype_val) ⟨⟨_, hs⟩, by
      show (compFin g₁)⁻¹ * (compFin g₁ * δ⁻¹) * δ ∈ K'
      rw [inv_mul_cancel_left, inv_mul_cancel]; exact K'.one_mem⟩
  set k₁ := (compFin g₁)⁻¹ * gl2Map (algebraMap ℚ FinAdele) γ₁ * δ
  have hk₁ : k₁ ∈ K' := hyW
  refine ⟨γ₀ * γ₁, (gl2Map (algebraMap ℚ ℝ) γ₁)⁻¹ * compInf g₁, k₁⁻¹, ?_, K'.inv_mem hk₁, ?_⟩
  · have hd1 : Matrix.GeneralLinearGroup.det ((gl2Map (algebraMap ℚ ℝ) γ₁)⁻¹) = 1 := by
      rw [map_inv, det_gl2Map, show Matrix.GeneralLinearGroup.det γ₁ = 1 from hγ₁, map_one, inv_one]
    rw [Matrix.mem_glpos, map_mul, Units.val_mul, hd1, Units.val_one, one_mul]; exact hg₁i
  · apply gl_adele_ext
    · simp only [map_mul, compInf_infEmb, compInf_finEmb, compInf_rat, g₁, map_inv]
      group
    · simp only [map_mul, compFin_infEmb, compFin_finEmb, compFin_rat, mul_one, k₁, g₁, map_inv, mul_inv_rev,
        inv_inv]
      group

/-- Strong approximation: for an open subgroup `K' ≤ K_f` with `det K' = Ẑ^×`, `G(𝔸) = G(ℚ) G(ℝ)^+ K'`, with
`G(ℝ)^+ = {det > 0}` embedded as `h ↦ (h, 1)` and `K'` as `k ↦ (1, k)`. -/
@[tf_id "I.topgrp.thm:strong-approximation"]
theorem strong_approximation (K' : Subgroup (GL (Fin 2) FinAdele)) (hK'K : K' ≤ maxCompactFin)
    (hK'o : IsOpen (K' : Set (GL (Fin 2) FinAdele)))
    (hdet : K'.map Matrix.GeneralLinearGroup.det = (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom).range)
    (g : GL (Fin 2) Adele) :
    ∃ (γ : GL (Fin 2) ℚ) (h k : GL (Fin 2) Adele), compInf h ∈ Matrix.GLPos (Fin 2) ℝ ∧ compFin h = 1 ∧
      compInf k = 1 ∧ compFin k ∈ K' ∧ g = gl2Map (algebraMap ℚ Adele) γ * h * k := by
  have _h := hK'K
  obtain ⟨q, r, u, hr, hy⟩ := exists_ratIdele_mul_ideleInfFin (Matrix.GeneralLinearGroup.det g)
  obtain ⟨δ, hδK, hδ⟩ : Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom u ∈
      K'.map Matrix.GeneralLinearGroup.det := by rw [hdet]; exact ⟨_, rfl⟩
  obtain ⟨γ, a, k, ha, hk, hg⟩ := strong_approx_claim K' hK'o g q r hr u hy δ hδ
  exact ⟨γ, infEmb a, finEmb (δ * k), by rwa [compInf_infEmb], compFin_infEmb a, compInf_finEmb _,
    by rw [compFin_finEmb]; exact K'.mul_mem hδK hk, hg⟩

/-! ### `T(𝔸)^1`, `G(𝔸)^1` and the double cosets (M3, unit U6) -/

/-- `T(𝔸)^1 = {diag(t₁, t₂) : |t₁|_𝔸 = |t₂|_𝔸 = 1}`. (`B(𝔸)`, `T(𝔸)`, `N(𝔸)`, `Z(𝔸)` are `borel Adele`,
`torus Adele`, `unipotent Adele`, `center Adele`, and likewise over `𝔸_f`.) -/
@[tf_id "I.topgrp.def:adelic-subgroups"]
noncomputable def torusNormOne : Subgroup (GL (Fin 2) Adele) :=
  (ideleNormOne.prod ideleNormOne).map (diagHom Adele)

/-- `B(𝔸)`, `T(𝔸)`, `N(𝔸)`, `Z(𝔸)` and `T(𝔸)^1` are closed in `G(𝔸)`. -/
@[tf_id "I.topgrp.thm:adelic-subgroups-closed"]
theorem adelic_subgroups_closed :
    IsClosed (borel Adele : Set (GL (Fin 2) Adele)) ∧ IsClosed (torus Adele : Set (GL (Fin 2) Adele)) ∧
      IsClosed (unipotent Adele : Set (GL (Fin 2) Adele)) ∧ IsClosed (center Adele : Set (GL (Fin 2) Adele)) ∧
      IsClosed (torusNormOne : Set (GL (Fin 2) Adele)) := by
  have he : ∀ i j, Continuous fun g : GL (Fin 2) Adele ↦ (g : Matrix (Fin 2) (Fin 2) Adele) i j :=
    fun i j ↦ Units.continuous_val.matrix_elem i j
  have hei : ∀ i j, Continuous fun g : GL (Fin 2) Adele ↦ ((g⁻¹ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) i j :=
    fun i j ↦ Units.continuous_coe_inv.matrix_elem i j
  have hz : ∀ i j, IsClosed {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) i j = 0} :=
    fun i j ↦ isClosed_eq (he i j) continuous_const
  have hB : IsClosed (borel Adele : Set (GL (Fin 2) Adele)) := hz 1 0
  have hT : IsClosed (torus Adele : Set (GL (Fin 2) Adele)) := (hz 0 1).inter (hz 1 0)
  refine ⟨hB, hT, ?_, ?_, ?_⟩
  · have : (unipotent Adele : Set (GL (Fin 2) Adele)) = {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 1 0 = 0} ∩
        {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 0 0 = 1} ∩ {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 1 1 = 1} := by
      ext g
      constructor
      · rintro ⟨x, rfl⟩; simp
      · rintro ⟨⟨h10, h00⟩, h11⟩
        refine ⟨(g : Matrix (Fin 2) (Fin 2) Adele) 0 1, ?_⟩
        apply Units.ext; refine Matrix.ext fun i j ↦ ?_; fin_cases i <;> fin_cases j <;> simp_all
    rw [this]
    exact ((hz 1 0).inter (isClosed_eq (he 0 0) continuous_const)).inter (isClosed_eq (he 1 1) continuous_const)
  · have : (center Adele : Set (GL (Fin 2) Adele)) = {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 0 1 = 0} ∩
        {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 1 0 = 0} ∩
          {g : GL (Fin 2) Adele | (g : Matrix (Fin 2) (Fin 2) Adele) 0 0 = (g : Matrix (Fin 2) (Fin 2) Adele) 1 1} := by
      ext g
      constructor
      · rintro ⟨z, rfl⟩; simp
      · rintro ⟨⟨h01, h10⟩, h0011⟩
        have hd : IsUnit ((g : Matrix (Fin 2) (Fin 2) Adele) 0 0 * (g : Matrix (Fin 2) (Fin 2) Adele) 0 0) := by
          have := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
          rw [Matrix.det_fin_two, h01, h10, ← h0011] at this
          simpa using this
        refine ⟨(isUnit_of_mul_isUnit_left hd).unit, ?_⟩
        apply Units.ext; refine Matrix.ext fun i j ↦ ?_; fin_cases i <;> fin_cases j <;> simp_all
    rw [this]
    exact ((hz 0 1).inter (hz 1 0)).inter (isClosed_eq (he 0 0) (he 1 1))
  · -- `T(𝔸)^1` via the embedding of the ideles into `𝔸 × 𝔸ᵐᵒᵖ`
    have hN1 : IsClosed (ideleNormOne : Set Idele) := isClosed_singleton.preimage ideleNorm_spec.1
    obtain ⟨F, hF, hFeq⟩ := (Units.isEmbedding_embedProduct (M := Adele)).isInducing.isClosed_iff.mp hN1
    have hemb : ∀ i : Fin 2, Continuous fun g : GL (Fin 2) Adele ↦
        ((g : Matrix (Fin 2) (Fin 2) Adele) i i, MulOpposite.op (((g⁻¹ : GL (Fin 2) Adele) :
          Matrix (Fin 2) (Fin 2) Adele) i i)) :=
      fun i ↦ (he i i).prodMk (MulOpposite.continuous_op.comp (hei i i))
    have : (torusNormOne : Set (GL (Fin 2) Adele)) = (torus Adele : Set (GL (Fin 2) Adele)) ∩
        ((fun g : GL (Fin 2) Adele ↦ ((g : Matrix (Fin 2) (Fin 2) Adele) 0 0, MulOpposite.op
          (((g⁻¹ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 0 0))) ⁻¹' F ∩
        (fun g : GL (Fin 2) Adele ↦ ((g : Matrix (Fin 2) (Fin 2) Adele) 1 1, MulOpposite.op
          (((g⁻¹ : GL (Fin 2) Adele) : Matrix (Fin 2) (Fin 2) Adele) 1 1))) ⁻¹' F) := by
      ext g
      constructor
      · rintro ⟨⟨t₁, t₂⟩, ⟨h1, h2⟩, rfl⟩
        refine ⟨⟨by simp [diagHom, diagElt], by simp [diagHom, diagElt]⟩, ?_, ?_⟩
        · have : t₁ ∈ Units.embedProduct Adele ⁻¹' F := by rw [hFeq]; exact h1
          exact this
        · have : t₂ ∈ Units.embedProduct Adele ⁻¹' F := by rw [hFeq]; exact h2
          exact this
      · rintro ⟨hTg, h0, h1⟩
        obtain ⟨t₁, t₂, rfl⟩ := exists_diagElt_of_mem_torus' hTg
        refine ⟨(t₁, t₂), ⟨?_, ?_⟩, rfl⟩
        · have : t₁ ∈ Units.embedProduct Adele ⁻¹' F := h0
          rwa [hFeq] at this
        · have : t₂ ∈ Units.embedProduct Adele ⁻¹' F := h1
          rwa [hFeq] at this
    rw [this]
    exact hT.inter (((hF.preimage (hemb 0))).inter (hF.preimage (hemb 1)))

/-- The norm-one group `G(𝔸)^1 = {g : |det g|_𝔸 = 1}`. -/
@[tf_id "I.topgrp.def:norm-one-group"]
noncomputable def normOneGroup : Subgroup (GL (Fin 2) Adele) :=
  (ideleNorm.comp Matrix.GeneralLinearGroup.det).ker

/-- `G(𝔸)^1` is a closed normal subgroup (the claims of `I.topgrp.def:norm-one-group`). -/
@[tf_aux "I.topgrp.lem:norm-one-group-closed-normal"]
theorem normOneGroup_closed_normal : IsClosed (normOneGroup : Set (GL (Fin 2) Adele)) ∧ normOneGroup.Normal := by
  refine ⟨?_, MonoidHom.normal_ker _⟩
  have hc : Continuous (ideleNorm.comp Matrix.GeneralLinearGroup.det : GL (Fin 2) Adele →* ℝ) :=
    ideleNorm_spec.1.comp continuous_det_gl
  exact isClosed_singleton.preimage hc

/-- `A_G^+ × G(𝔸)^1 → G(𝔸)`, `(a, g) ↦ a g`, is an isomorphism of topological groups with inverse
`g ↦ (a(|det g|_𝔸^{1/2}), a(|det g|_𝔸^{1/2})⁻¹ g)`; and `G(ℚ) ⊆ G(𝔸)^1`. -/
@[tf_id "I.topgrp.thm:norm-one-splitting"]
theorem norm_one_splitting :
    (∃ e : splitComponent × normOneGroup ≃ₜ* GL (Fin 2) Adele,
      (∀ a g, e (a, g) = (a : GL (Fin 2) Adele) * g) ∧
        ∀ (g : GL (Fin 2) Adele) (r : ℝˣ),
          (r : ℝ) = Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det g)) →
            ((e.symm g).1 : GL (Fin 2) Adele) = centralElt r ∧
              ((e.symm g).2 : GL (Fin 2) Adele) = (centralElt r)⁻¹ * g) ∧
      gl2RatAdelic ≤ normOneGroup := by
  have hσmem : ∀ g, centralElt (sqrtNormDet g) ∈ splitComponent := fun g ↦
    ⟨sqrtNormDet g, (Units.mem_posSubgroup _).mpr (sqrtNormDet_pos g), rfl⟩
  have hrest : ∀ g, (centralElt (sqrtNormDet g))⁻¹ * g ∈ normOneGroup := fun g ↦ by
    show ideleNorm (Matrix.GeneralLinearGroup.det ((centralElt (sqrtNormDet g))⁻¹ * g)) = 1
    rw [map_mul, map_inv, map_mul, map_inv, ideleNorm_det_centralElt]
    show ((Real.sqrt _) ^ 2)⁻¹ * _ = (1 : ℝ)
    rw [Real.sq_sqrt (ideleNorm_spec.2.1 _).le, inv_mul_cancel₀ (ideleNorm_spec.2.1 _).ne']
  have hcomm : ∀ (a : splitComponent) (g : GL (Fin 2) Adele), (a : GL (Fin 2) Adele) * g = g * a := fun a g ↦
    (Subgroup.mem_center_iff.mp (splitComponent_spec.2.1 a.2) g).symm
  let E : splitComponent × normOneGroup →* GL (Fin 2) Adele :=
    { toFun := fun p ↦ (p.1 : GL (Fin 2) Adele) * p.2
      map_one' := by simp
      map_mul' := fun p q ↦ by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_assoc]
        congr 1
        simp only [← mul_assoc]
        congr 1
        exact hcomm q.1 p.2 }
  have hleft : ∀ p : splitComponent × normOneGroup,
      (⟨centralElt (sqrtNormDet (E p)), hσmem _⟩, ⟨_, hrest (E p)⟩) = p := by
    rintro ⟨⟨_, r, hr, rfl⟩, ⟨g, hg⟩⟩
    have hr' : sqrtNormDet (E (⟨centralElt r, r, hr, rfl⟩, ⟨g, hg⟩)) = r := by
      apply Units.ext
      show Real.sqrt (ideleNorm (Matrix.GeneralLinearGroup.det (centralElt r * g))) = r
      rw [map_mul, map_mul, ideleNorm_det_centralElt, show ideleNorm (Matrix.GeneralLinearGroup.det g) = 1 from hg,
        mul_one, Real.sqrt_sq ((Units.mem_posSubgroup _).mp hr).le]
    ext1
    · apply Subtype.ext
      show centralElt (sqrtNormDet (E _)) = centralElt r
      exact congrArg centralElt hr'
    · apply Subtype.ext
      show (centralElt (sqrtNormDet (E _)))⁻¹ * (centralElt r * g) = g
      simp only [hr', inv_mul_cancel_left]
  let e : splitComponent × normOneGroup ≃ₜ* GL (Fin 2) Adele :=
    { toFun := E
      invFun := fun g ↦ (⟨centralElt (sqrtNormDet g), hσmem g⟩, ⟨_, hrest g⟩)
      left_inv := hleft
      right_inv := fun g ↦ by
        show centralElt (sqrtNormDet g) * ((centralElt (sqrtNormDet g))⁻¹ * g) = g
        rw [mul_inv_cancel_left]
      map_mul' := E.map_mul
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := by
        have h1 : Continuous fun g ↦ centralElt (sqrtNormDet g) := continuous_centralElt.comp continuous_sqrtNormDet
        exact (h1.subtype_mk _).prodMk ((h1.inv.mul continuous_id).subtype_mk _) }
  refine ⟨⟨e, fun a g ↦ rfl, fun g r hr ↦ ?_⟩, ?_⟩
  · have hrr : sqrtNormDet g = r := Units.ext hr.symm
    exact ⟨by show centralElt (sqrtNormDet g) = _; rw [hrr], by show (centralElt (sqrtNormDet g))⁻¹ * g = _; rw [hrr]⟩
  · rintro _ ⟨γ, rfl⟩
    show ideleNorm (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ)) = 1
    have : Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ) =
        ratIdele (Matrix.GeneralLinearGroup.det γ) := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.det, gl2Map, ratIdele, RingHom.map_det]
    rw [this, product_formula]

/-- `u ↦ diag(u, 1)`, `Ẑ^× → K_f`. -/
noncomputable def diagZhat : Zhatˣ →* GL (Fin 2) FinAdele :=
  (diagHom FinAdele).comp ((Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom).prod 1)

theorem continuous_diagZhat : Continuous diagZhat := by
  have h1 : Continuous fun u : Zhatˣ ↦ ((u : Zhat) : FinAdele) :=
    continuous_subtype_val.comp Units.continuous_val
  have h2 : Continuous fun u : Zhatˣ ↦ (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) :=
    continuous_subtype_val.comp Units.continuous_coe_inv
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagZhat, diagHom, diagElt] <;> first | exact h1 | fun_prop
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [diagZhat, diagHom, diagElt, Units.inv_mk] <;>
      first | exact h2 | fun_prop

theorem det_diagZhat (u : Zhatˣ) :
    Matrix.GeneralLinearGroup.det (diagZhat u) = Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom u := by
  apply Units.ext
  simp [diagZhat, diagHom, diagElt, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]

theorem det_adele_val (g : GL (Fin 2) Adele) :
    ((Matrix.GeneralLinearGroup.det g : Idele) : Adele) =
      (((Matrix.GeneralLinearGroup.det (compInf g) : ℝˣ) : ℝ),
        ((Matrix.GeneralLinearGroup.det (compFin g) : FinAdeleˣ) : FinAdele)) := by
  rw [compInf, compFin, det_gl2Map, det_gl2Map]; rfl

/-- For an open subgroup `K' ≤ K_f`: `det K'` is an open subgroup of `Ẑ^×`, and `g ↦ u(det g) det(K')` (with `u` the
`Ẑ^×`-component of the decomposition `e` of `I.adele.thm:idele-decomposition`) induces a bijection
`G(ℚ)\G(𝔸)/G(ℝ)^+K' → Ẑ^×/det(K')`: it is surjective, and two elements have the same image iff they lie in the same
double coset `G(ℚ) g G(ℝ)^+ K'` (`G(ℝ)^+` embedded as `h ↦ (h, 1)`, `K'` as `k ↦ (1, k)`). -/
@[tf_id "I.topgrp.thm:double-coset-det"]
theorem double_coset_det (K' : Subgroup (GL (Fin 2) FinAdele)) (hK'K : K' ≤ maxCompactFin)
    (hK'o : IsOpen (K' : Set (GL (Fin 2) FinAdele)))
    (e : (ℚˣ × Units.posSubgroup ℝ × Zhatˣ) ≃* Idele)
    (he : ∀ (q : ℚˣ) (r : Units.posSubgroup ℝ) (u : Zhatˣ),
      e (q, r, u) = ratIdele q * ideleInfFin ((r : ℝˣ) : ℝ) u) :
    IsOpen (((K'.map Matrix.GeneralLinearGroup.det).comap
        (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom) : Subgroup Zhatˣ) : Set Zhatˣ) ∧
      Function.Surjective (fun g : GL (Fin 2) Adele ↦
        (QuotientGroup.mk (e.symm (Matrix.GeneralLinearGroup.det g)).2.2 :
          Zhatˣ ⧸ (K'.map Matrix.GeneralLinearGroup.det).comap
            (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom))) ∧
      ∀ g g' : GL (Fin 2) Adele,
        ((QuotientGroup.mk (e.symm (Matrix.GeneralLinearGroup.det g)).2.2 :
            Zhatˣ ⧸ (K'.map Matrix.GeneralLinearGroup.det).comap
              (Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom)) =
          QuotientGroup.mk (e.symm (Matrix.GeneralLinearGroup.det g')).2.2 ↔
        ∃ (γ : GL (Fin 2) ℚ) (h k : GL (Fin 2) Adele), compInf h ∈ Matrix.GLPos (Fin 2) ℝ ∧ compFin h = 1 ∧
          compInf k = 1 ∧ compFin k ∈ K' ∧ g' = gl2Map (algebraMap ℚ Adele) γ * g * h * k) := by
  set ι := Units.map (Zhat.subtype : Zhat →+* FinAdele).toMonoidHom
  set D : Subgroup Zhatˣ := (K'.map Matrix.GeneralLinearGroup.det).comap ι
  -- `u`: the `Ẑ^×`-component, a homomorphism
  let U : Idele →* Zhatˣ := (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp e.symm.toMonoidHom)
  have hU : ∀ x, U x = (e.symm x).2.2 := fun _ ↦ rfl
  have hUe : ∀ (q : ℚˣ) (r : ℝ) (hr : 0 < r) (u : Zhatˣ), U (ratIdele q * ideleInfFin r u) = u := by
    intro q r hr u
    have : e.symm (ratIdele q * ideleInfFin r u) = (q, ⟨Units.mk0 r hr.ne', (Units.mem_posSubgroup _).mpr hr⟩, u) :=
      e.symm_apply_eq.mpr (he q ⟨Units.mk0 r hr.ne', (Units.mem_posSubgroup _).mpr hr⟩ u).symm
    rw [hU, this]
  have hUq : ∀ q : ℚˣ, U (ratIdele q) = 1 := fun q ↦ by
    have := hUe q 1 one_pos 1
    rwa [ideleInfFin_one_one, mul_one] at this
  have hUr : ∀ (r : ℝ) (hr : 0 < r) (u : Zhatˣ), U (ideleInfFin r u) = u := fun r hr u ↦ by
    have := hUe 1 r hr u
    rwa [map_one, one_mul] at this
  -- determinants of the three kinds of factors
  have hdetinf : ∀ a : GL (Fin 2) ℝ, a ∈ Matrix.GLPos (Fin 2) ℝ →
      Matrix.GeneralLinearGroup.det (infEmb a) = ideleInfFin ((Matrix.GeneralLinearGroup.det a : ℝˣ) : ℝ) 1 := by
    intro a ha
    apply Units.ext
    rw [det_adele_val, ideleInfFin_val (Matrix.mem_glpos a |>.mp ha).ne', compInf_infEmb, compFin_infEmb, map_one]
    rfl
  have hdetfin : ∀ w : Zhatˣ, ∀ k : GL (Fin 2) Adele, compInf k = 1 →
      Matrix.GeneralLinearGroup.det (compFin k) = ι w → Matrix.GeneralLinearGroup.det k = ideleInfFin 1 w := by
    intro w k hk1 hk2
    apply Units.ext
    rw [det_adele_val, ideleInfFin_val one_ne_zero, hk1, hk2, map_one]
    rfl
  refine ⟨?_, ?_, fun g g' ↦ ⟨fun hgg ↦ ?_, ?_⟩⟩
  · -- `D` contains the open subgroup `diag⁻¹(K')`
    refine Subgroup.isOpen_mono (H₁ := K'.comap diagZhat) (fun u hu ↦ ⟨diagZhat u, hu, det_diagZhat u⟩) ?_
    exact hK'o.preimage continuous_diagZhat
  · rintro ⟨v⟩
    refine ⟨finEmb (diagZhat v), ?_⟩
    show (QuotientGroup.mk (U _) : Zhatˣ ⧸ D) = QuotientGroup.mk v
    rw [hdetfin v _ (compInf_finEmb _) (by rw [compFin_finEmb, det_diagZhat]), hUr 1 one_pos v]
  · -- injectivity
    rw [QuotientGroup.eq] at hgg
    obtain ⟨k₀, hk₀K, hk₀⟩ := hgg
    set u' := U (Matrix.GeneralLinearGroup.det g')
    obtain ⟨q, r, u, hr, hy⟩ := exists_ratIdele_mul_ideleInfFin (Matrix.GeneralLinearGroup.det g)
    obtain ⟨q', r', u'', hr', hy'⟩ := exists_ratIdele_mul_ideleInfFin (Matrix.GeneralLinearGroup.det g')
    have hu : U (Matrix.GeneralLinearGroup.det g) = u := by rw [hy, hUe q r hr u]
    have hu' : u' = u'' := by simp only [u', hy', hUe q' r' hr' u'']
    obtain ⟨γ', a', k', ha', hk', hg'⟩ :=
      strong_approx_claim K' hK'o g' q' r' hr' u'' hy' (diagZhat u'') (det_diagZhat u'')
    have hδ : Matrix.GeneralLinearGroup.det (diagZhat u'' * k₀⁻¹) = ι u := by
      rw [map_mul, map_inv, det_diagZhat, hk₀, ← map_inv, ← map_mul]
      congr 1
      rw [← hu, ← hu']
      show u' * ((U (Matrix.GeneralLinearGroup.det g))⁻¹ * u')⁻¹ = _
      group
    obtain ⟨γ, a, k, ha, hk, hg⟩ := strong_approx_claim K' hK'o g q r hr u hy _ hδ
    refine ⟨γ' * γ⁻¹, infEmb (a⁻¹ * a'), finEmb ((k₀⁻¹ * k)⁻¹ * k'), ?_, compFin_infEmb _,
      compInf_finEmb _, ?_, ?_⟩
    · rw [compInf_infEmb]
      exact (Matrix.GLPos (Fin 2) ℝ).mul_mem ((Matrix.GLPos (Fin 2) ℝ).inv_mem ha) ha'
    · rw [compFin_finEmb]
      exact K'.mul_mem (K'.inv_mem (K'.mul_mem (K'.inv_mem hk₀K) hk)) hk'
    · rw [hg', hg]
      apply gl_adele_ext
      · simp only [map_mul, map_inv, compInf_infEmb, compInf_finEmb, compInf_rat]
        group
      · simp only [map_mul, map_inv, compFin_infEmb, compFin_finEmb, compFin_rat]
        group
  · rintro ⟨γ, h, k, hh, hh1, hk1, hkK, rfl⟩
    -- `u(det(γ g h k)) = u(det g) · w` with `ι w = det k_f ∈ det K'`
    obtain ⟨w₀, hw₀⟩ := (mem_maxCompactFin_iff_gl2Zhat _).mp (hK'K hkK)
    set w := Matrix.GeneralLinearGroup.det w₀
    have hkw : Matrix.GeneralLinearGroup.det (compFin k) = ι w := by
      rw [← hw₀, gl2Zhat, det_gl2Map]
    have hh' : h = infEmb (compInf h) :=
      gl_adele_ext (by rw [compInf_infEmb]) (by rw [compFin_infEmb, hh1])
    rw [QuotientGroup.eq]
    show (U (Matrix.GeneralLinearGroup.det g))⁻¹ * U (Matrix.GeneralLinearGroup.det
      (gl2Map (algebraMap ℚ Adele) γ * g * h * k)) ∈ D
    have hdh : U (Matrix.GeneralLinearGroup.det h) = 1 := by
      rw [hh', hdetinf _ hh, hUr _ ((Matrix.mem_glpos _).mp hh)]
    have hdk : U (Matrix.GeneralLinearGroup.det k) = w := by
      rw [hdetfin w k hk1 hkw, hUr 1 one_pos w]
    have hdγ : U (Matrix.GeneralLinearGroup.det (gl2Map (algebraMap ℚ Adele) γ)) = 1 := by
      rw [det_gl2Map]; exact hUq _
    simp only [map_mul, hdh, hdk, hdγ, one_mul, mul_one, inv_mul_cancel_left]
    exact ⟨compFin k, hkK, hkw⟩

end Adelic

end GL2TF
