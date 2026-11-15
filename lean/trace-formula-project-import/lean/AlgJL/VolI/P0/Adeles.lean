import AlgJL.Meta.Tag
import AlgJL.Common.RestrictedProduct
import AlgJL.VolI.P0.LocalField
import FLT.NumberField.Padics.RestrictedProduct
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.Group.Quotient


-- algebraic_jl fork (L-A, 2026-11-14): trimmed copy of lean/GL2TF/VolI/P0/Adeles.lean @84818d0. Kept declarations are
-- byte-identical. Dropped (analytic): stdCharAdele (+ _isHom, _rat), schwartzBruhatAdele (+ reduction to indicators),
-- fourierAdele, finAdeleHaar, adeleHaar (+ _spec), rat_quotient_compact (its statement normalizes a Haar measure),
-- fourier_inversion_adele, poisson_summation and their untagged helpers; the Schwartz/Fourier/measure imports.

/-!
# Adeles of ℚ: the working model, Haar measure, characters, Poisson summation (M3, unit U3)

Lean counterpart of `vol1/ch-0-03-adeles.tex` §§1–2. Owner: L2.

Design (D17, D-ADELE): the working model is `𝔸 = ℝ × 𝔸_f` with `𝔸_f = Πʳ (p : Nat.Primes), [ℚ_[p], ℤ_[p]]`
(Mathlib's `RestrictedProduct` along the cofinite filter, with its restricted-product topology). Both are reducible
aliases, so every Mathlib instance applies. Item `I.adele.thm:adele-concrete-model` (the iso to Mathlib's
`NumberField.AdeleRing (𝓞 ℚ) ℚ`) is the fidelity anchor. The diagonal embedding of `ℚ` into `𝔸_f` is the
vendored [IFLT] `Algebra ℚ` instance (tagged B-only below); `𝔸` gets the product algebra structure.

The topological instances on `𝔸_f` (topological ring, locally compact, second countable) are B-only plumbing whose
values are projections of the tagged theorems, so no `Fact` instance about `ℤ_[p]` is global. The Borel σ-algebra of
`𝔸_f` is the generic restricted-product instance of `GL2TF.Common.RestrictedProduct` (L1); `𝔸` carries the product
σ-algebra.
-/

/- The `ℚ`-algebra structure on `𝔸_f` (the diagonal embedding `ℚ → 𝔸_f`) is the vendored [IFLT] instance; tagged B-only
here, outside `namespace GL2TF`, so that the extractor and tfaudit agree on the name (R23). -/
attribute [tf_aux "I.adele.def:rat-embedding"]
  RestrictedProduct.instAlgebraRatPrimesPadicValNatPrimeCoeSubringSubringCofinite_fLT

open RestrictedProduct Filter Topology MeasureTheory
open scoped Pointwise

namespace GL2TF

/-- `p : Nat.Primes` is prime, as an instance (B-only plumbing: makes `ℚ_[p]` a field for `p : Nat.Primes`). -/
@[tf_aux "I.adele.lem:primes-fact-instance"]
instance fact_primes_prime (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The ring of finite adeles `𝔸_f = Πʳ_p (ℚ_p, ℤ_p)`: the restricted product of the `ℚ_[p]` with respect to the
`ℤ_[p]` along the cofinite filter, with the restricted-product topology. -/
@[tf_id "I.adele.def:finite-adeles-model"]
abbrev FinAdele : Type := Πʳ (p : Nat.Primes), [ℚ_[p], PadicInt.subring p]

/-- `Ẑ = {x ∈ 𝔸_f : x_p ∈ ℤ_p for all p}`, a subring of `𝔸_f`; `Ẑ^×` is its unit group `Zhatˣ`. -/
@[tf_id "I.adele.def:zhat"]
noncomputable def Zhat : Subring FinAdele :=
  ⨅ p : Nat.Primes, (PadicInt.subring p).comap (evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p)

/-- The ring of adeles `𝔸 = ℝ × 𝔸_f` (the working model, D17), with the product topology. -/
@[tf_id "I.adele.def:adele-ring"]
abbrev Adele : Type := ℝ × FinAdele

/-- Membership in `Ẑ` (proof helper). -/
theorem mem_zhat {x : FinAdele} : x ∈ Zhat ↔ ∀ p : Nat.Primes, x p ∈ PadicInt.subring p := by
  simp [Zhat, Subring.mem_iInf]

/-- The units of `Ẑ`, explicitly: `x ∈ 𝔸_f` lies in (the image of) `Ẑ^×` iff `x_p ∈ ℤ_p^×` for every `p`. -/
@[tf_aux "I.adele.lem:zhat-units-explicit"]
theorem zhat_units_explicit (x : FinAdele) :
    (∃ u : Zhatˣ, ((u : Zhat) : FinAdele) = x) ↔
      ∀ p : Nat.Primes, ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x p := by
  constructor
  · rintro ⟨u, rfl⟩ p
    have hmul : ((u : Zhat) : FinAdele) p * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) p = 1 := by
      have := congrArg (fun z : Zhat ↦ (z : FinAdele) p) u.mul_inv
      simpa only [Subring.coe_mul, Subring.coe_one, RestrictedProduct.mul_apply,
        RestrictedProduct.one_apply] using this
    exact ⟨⟨⟨_, mem_zhat.mp (u : Zhat).2 p⟩, ⟨_, mem_zhat.mp ((u⁻¹ : Zhatˣ) : Zhat).2 p⟩,
      Subtype.ext hmul, Subtype.ext ((mul_comm _ _).trans hmul)⟩, rfl⟩
  · intro h
    choose v hv using h
    have hx : x ∈ Zhat := mem_zhat.mpr fun p ↦ hv p ▸ (v p : ℤ_[p]).2
    let y : FinAdele := ⟨fun p ↦ (((v p)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), Filter.Eventually.of_forall fun p ↦
      ((((v p)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).2⟩
    have hy : y ∈ Zhat := mem_zhat.mpr fun p ↦ ((((v p)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).2
    have hxy : x * y = 1 := by
      ext p
      rw [RestrictedProduct.mul_apply, RestrictedProduct.one_apply]
      change x p * ((((v p)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1
      rw [← hv p, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext hxy, Subtype.ext ((mul_comm _ _).trans hxy)⟩, rfl⟩

/-- The diagonal embedding `ℚ → 𝔸` is an injective ring homomorphism with components `q ↦ q` (B-only companion of
`I.adele.def:adele-ring`). -/
@[tf_aux "I.adele.lem:rat-embedding-diagonal"]
theorem algebraMap_adele_diagonal :
    Function.Injective (algebraMap ℚ Adele) ∧
      ∀ q : ℚ, (algebraMap ℚ Adele q).1 = (q : ℝ) ∧ ∀ p : Nat.Primes, (algebraMap ℚ Adele q).2 p = (q : ℚ_[p]) := by
  refine ⟨fun q q' h ↦ ?_, fun q ↦ ⟨rfl, fun p ↦ rfl⟩⟩
  have : (q : ℝ) = (q' : ℝ) := congrArg Prod.fst h
  exact_mod_cast this

section ConcreteModel

open PadicInt IsDedekindDomain NumberField Rat.HeightOneSpectrum

/-- Pointwise: ℚ_[primesEquiv v] → v.adicCompletion ℚ preserves the integers. (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem adele_mapsTo_toMathlib (v : (HeightOneSpectrum (𝓞 ℚ))) :
    Set.MapsTo (adicCompletion.padicEquiv v).symm (PadicInt.subring (primesEquiv v))
      (v.adicCompletionIntegers ℚ) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn hy
  simpa using hx

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem adele_mapsTo_fromMathlib (p : Nat.Primes) :
    Set.MapsTo (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm
      (((primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletionIntegers ℚ) (PadicInt.subring p) := by
  intro x hx
  rw [← PadicInt.coe_adicCompletionIntegersEquiv_symm_apply (𝓞 ℚ) p ⟨x, hx⟩]
  exact PadicInt.norm_le_one _

/-- The finite part, as a ring hom `𝔸_f → 𝔸ᶠ[ℚ]`. (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def finAdeleToMathlib : FinAdele →+* FiniteAdeleRing (𝓞 ℚ) ℚ :=
  mapAlongRingHom (fun p : Nat.Primes ↦ ℚ_[p]) (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ v.adicCompletion ℚ)
    (primesEquiv (R := 𝓞 ℚ)) (primesEquiv (R := 𝓞 ℚ)).injective.tendsto_cofinite
    (fun v ↦ (adicCompletion.padicEquiv v).symm) (.of_forall adele_mapsTo_toMathlib)

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def finAdeleFromMathlib : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FinAdele :=
  mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ v.adicCompletion ℚ) (fun p : Nat.Primes ↦ ℚ_[p])
    (primesEquiv (R := 𝓞 ℚ)).symm (primesEquiv (R := 𝓞 ℚ)).symm.injective.tendsto_cofinite
    (fun p ↦ (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm) (.of_forall adele_mapsTo_fromMathlib)

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem adele_cast_dep {ι : Type*} {A : ι → Type*} (x : ∀ i, A i) {i j : ι} (h : i = j) :
    Equiv.cast (congrArg A h) (x i) = x j := by
  subst h; rfl

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem finAdele_from_to (x : FinAdele) : finAdeleFromMathlib (finAdeleToMathlib x) = x := by
  ext p
  change (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm
    ((adicCompletion.padicEquiv _).symm (x (primesEquiv ((primesEquiv (R := 𝓞 ℚ)).symm p)))) = x p
  rw [Padic.adicCompletionEquiv, ContinuousAlgEquiv.symm_trans_apply, ContinuousAlgEquiv.symm_symm,
    ContinuousAlgEquiv.apply_symm_apply, ContinuousAlgEquiv.cast_symm_apply]
  exact adele_cast_dep (A := fun q : Nat.Primes ↦ ℚ_[q]) (fun q ↦ x q)
    ((primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem finAdele_to_from_aux (y : FiniteAdeleRing (𝓞 ℚ) ℚ) {w v : HeightOneSpectrum (𝓞 ℚ)} (h : w = v) :
    (adicCompletion.padicEquiv v).symm (Equiv.cast (congrArg (fun q : Nat.Primes ↦ ℚ_[q])
      (congrArg (primesEquiv (R := 𝓞 ℚ)) h)) (adicCompletion.padicEquiv w (y w))) = y v := by
  subst h; simp

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem finAdele_to_from (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : finAdeleToMathlib (finAdeleFromMathlib y) = y := by
  apply Subtype.ext
  funext v
  change (adicCompletion.padicEquiv v).symm ((Padic.adicCompletionEquiv (𝓞 ℚ) (primesEquiv v)).symm
    (y ((primesEquiv (R := 𝓞 ℚ)).symm (primesEquiv v)))) = y v
  rw [Padic.adicCompletionEquiv, ContinuousAlgEquiv.symm_trans_apply, ContinuousAlgEquiv.symm_symm,
    ContinuousAlgEquiv.cast_symm_apply]
  exact finAdele_to_from_aux y ((primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v)

/-- The finite part as a ring isomorphism. (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def finAdeleRingEquiv : FinAdele ≃+* FiniteAdeleRing (𝓞 ℚ) ℚ :=
  { finAdeleToMathlib with
    invFun := finAdeleFromMathlib
    left_inv := finAdele_from_to
    right_inv := finAdele_to_from }

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem continuous_finAdeleToMathlib : Continuous finAdeleToMathlib :=
  mapAlong_continuous (fun p : Nat.Primes ↦ ℚ_[p]) (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ v.adicCompletion ℚ)
    (primesEquiv (R := 𝓞 ℚ)) (primesEquiv (R := 𝓞 ℚ)).injective.tendsto_cofinite
    (fun v ↦ (adicCompletion.padicEquiv v).symm) (.of_forall adele_mapsTo_toMathlib)
    fun v ↦ (adicCompletion.padicEquiv v).symm.continuous

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
theorem continuous_finAdeleFromMathlib : Continuous finAdeleFromMathlib :=
  mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ v.adicCompletion ℚ) (fun p : Nat.Primes ↦ ℚ_[p])
    (primesEquiv (R := 𝓞 ℚ)).symm (primesEquiv (R := 𝓞 ℚ)).symm.injective.tendsto_cofinite
    (fun p ↦ (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm) (.of_forall adele_mapsTo_fromMathlib)
    fun p ↦ (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm.continuous

/-- The finite part: `𝔸_f ≃A[ℚ] 𝔸ᶠ[ℚ]`. ℚ-linearity is automatic for ring isomorphisms. (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def finAdeleAlgEquiv : FinAdele ≃A[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := finAdeleRingEquiv) fun q ↦
    RingHom.map_rat_algebraMap finAdeleRingEquiv.toRingHom q
  continuous_toFun := continuous_finAdeleToMathlib
  continuous_invFun := continuous_finAdeleFromMathlib

/-- The infinite part: `ℝ ≃A[ℚ] K∞` for `K = ℚ`. (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def realInfAdeleRingEquiv : ℝ ≃+* InfiniteAdeleRing ℚ :=
  ((RingEquiv.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)).symm

/-- (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def realInfAdeleAlgEquiv : ℝ ≃A[ℚ] InfiniteAdeleRing ℚ where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := realInfAdeleRingEquiv) fun q ↦
    RingHom.map_rat_algebraMap realInfAdeleRingEquiv.toRingHom q
  continuous_toFun := ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph).symm.continuous
  continuous_invFun := ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph).continuous

/-- `𝔸 ≃A[ℚ] AdeleRing (𝓞 ℚ) ℚ` (topological ring iso, compatible with ℚ). (Proof helper for `I.adele.thm:adele-concrete-model`.) -/
noncomputable def adeleMathlibAlgEquiv : Adele ≃A[ℚ] AdeleRing (𝓞 ℚ) ℚ where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := (RingEquiv.prodCongr realInfAdeleRingEquiv finAdeleRingEquiv : Adele ≃+* InfiniteAdeleRing ℚ × _)) fun q ↦
    RingHom.map_rat_algebraMap (RingEquiv.prodCongr realInfAdeleRingEquiv finAdeleRingEquiv).toRingHom q
  continuous_toFun := realInfAdeleAlgEquiv.continuous.prodMap finAdeleAlgEquiv.continuous
  continuous_invFun := realInfAdeleAlgEquiv.symm.continuous.prodMap finAdeleAlgEquiv.symm.continuous

/-- `𝔸 ≅ 𝔸_ℚ`: an isomorphism of topological rings between the working model and Mathlib's adele ring
`NumberField.AdeleRing (𝓞 ℚ) ℚ`, compatible with the embeddings of `ℚ`. -/
@[tf_id "I.adele.thm:adele-concrete-model"]
theorem adele_concrete_model :
    ∃ e : Adele ≃+* NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ,
      Continuous e ∧ Continuous e.symm ∧
        ∀ q : ℚ, e (algebraMap ℚ Adele q) = algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) q :=
  ⟨adeleMathlibAlgEquiv.toAlgEquiv.toRingEquiv, adeleMathlibAlgEquiv.continuous,
    adeleMathlibAlgEquiv.symm.continuous, adeleMathlibAlgEquiv.commutes⟩

end ConcreteModel

/-- `ℤ_p = closedBall 0 1` in `ℚ_p` (proof helper). -/
theorem padicSubring_eq_closedBall (p : Nat.Primes) :
    (PadicInt.subring p : Set ℚ_[p]) = Metric.closedBall 0 1 := by
  ext x; simp [PadicInt.mem_subring_iff]

/-- `ℤ_p` is open in `ℚ_p` (proof helper). -/
theorem isOpen_padicSubring (p : Nat.Primes) : IsOpen (PadicInt.subring p : Set ℚ_[p]) := by
  rw [padicSubring_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero

/-- `ℤ_p` is compact (proof helper). -/
theorem isCompact_padicSubring (p : Nat.Primes) : IsCompact (PadicInt.subring p : Set ℚ_[p]) := by
  rw [padicSubring_eq_closedBall]
  exact isCompact_closedBall 0 1

/-- `Ẑ` is compact (proof helper). -/
theorem isCompact_zhat : IsCompact (Zhat : Set FinAdele) := by
  have : ∀ p : Nat.Primes, CompactSpace (PadicInt.subring p) := fun p ↦
    isCompact_iff_compactSpace.mp (isCompact_padicSubring p)
  have h : (Zhat : Set FinAdele) = Set.range (structureMap (fun p : Nat.Primes ↦ ℚ_[p])
      (fun p ↦ (PadicInt.subring p : Set ℚ_[p])) cofinite) := by
    rw [range_structureMap]
    ext x
    exact mem_zhat
  rw [h]
  exact isCompact_range isEmbedding_structureMap.continuous

/-- `Ẑ` is compact, as an instance (B-only plumbing for `I.adele.thm:adele-locally-compact`). -/
@[tf_aux "I.adele.lem:zhat-compact-instance"]
instance zhat_compactSpace : CompactSpace Zhat := isCompact_iff_compactSpace.mp isCompact_zhat

/-- `𝔸_f` is a topological ring, as an instance (B-only plumbing for `I.adele.thm:adele-locally-compact`). -/
@[tf_aux "I.adele.lem:finadele-topological-ring-instance"]
instance finAdele_isTopologicalRing : IsTopologicalRing FinAdele :=
  haveI : Fact (∀ p : Nat.Primes, IsOpen (PadicInt.subring p : Set ℚ_[p])) := ⟨isOpen_padicSubring⟩
  inferInstance

/-- `𝔸_f` is locally compact, as an instance (B-only plumbing for `I.adele.thm:adele-locally-compact`). -/
@[tf_aux "I.adele.lem:finadele-locally-compact-instance"]
instance finAdele_locallyCompactSpace : LocallyCompactSpace FinAdele :=
  haveI : Fact (∀ p : Nat.Primes, IsOpen (PadicInt.subring p : Set ℚ_[p])) := ⟨isOpen_padicSubring⟩
  haveI : ∀ p : Nat.Primes, CompactSpace (PadicInt.subring p) := fun p ↦
    isCompact_iff_compactSpace.mp (isCompact_padicSubring p)
  inferInstance

/-- `Ẑ` is open in `𝔸_f` (proof helper). -/
theorem isOpen_zhat_adele : IsOpen (Zhat : Set FinAdele) := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun p : Nat.Primes ↦ ℚ_[p])
    (A := fun p ↦ (PadicInt.subring p : Set ℚ_[p])) isOpen_padicSubring
  convert h using 1
  ext x
  exact mem_zhat

/-- `𝔸_f` and `𝔸` are locally compact Hausdorff topological rings; `Ẑ` is a compact open subring of `𝔸_f` whose
subspace topology is the product topology of `Π_p ℤ_p`. -/
@[tf_id "I.adele.thm:adele-locally-compact"]
theorem adele_locallyCompact :
    (IsTopologicalRing FinAdele ∧ LocallyCompactSpace FinAdele ∧ T2Space FinAdele) ∧
      (IsTopologicalRing Adele ∧ LocallyCompactSpace Adele ∧ T2Space Adele) ∧
      IsCompact (Zhat : Set FinAdele) ∧ IsOpen (Zhat : Set FinAdele) ∧
      ∃ e : Zhat ≃ₜ ((p : Nat.Primes) → ℤ_[p]),
        ∀ (x : Zhat) (p : Nat.Primes), ((e x p : ℤ_[p]) : ℚ_[p]) = (x : FinAdele) p := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance, inferInstance⟩,
    isCompact_zhat, isOpen_zhat_adele, ?_⟩
  let toFun : Zhat → ((p : Nat.Primes) → ℤ_[p]) := fun x p ↦ ⟨(x : FinAdele) p, mem_zhat.mp x.2 p⟩
  let invFun : ((p : Nat.Primes) → ℤ_[p]) → Zhat := fun f ↦
    ⟨structureMap (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ (PadicInt.subring p : Set ℚ_[p])) cofinite
      (fun p ↦ ⟨(f p : ℚ_[p]), (f p).2⟩), mem_zhat.mpr fun p ↦ (f p).2⟩
  have hto : Continuous toFun := continuous_pi fun p ↦
    ((continuous_eval p).comp continuous_subtype_val).subtype_mk _
  have hinv : Continuous invFun :=
    (isEmbedding_structureMap.continuous.comp
      (continuous_pi fun p ↦ ((continuous_subtype_val.comp (continuous_apply p)).subtype_mk _))).subtype_mk _
  exact ⟨Homeomorph.mk ⟨toFun, invFun, fun x ↦ rfl, fun f ↦ rfl⟩ hto hinv, fun x p ↦ rfl⟩

/-- `𝔸_f` and `𝔸` are second countable. -/
@[tf_id "I.adele.thm:adele-second-countable"]
theorem adele_secondCountable :
    SecondCountableTopology FinAdele ∧ SecondCountableTopology Adele := by
  have h : SecondCountableTopology FinAdele :=
    resProd_secondCountableTopology (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ (PadicInt.subring p : Set ℚ_[p]))
      isOpen_padicSubring
  exact ⟨h, inferInstance⟩

/-- `𝔸_f` is second countable, as an instance (B-only plumbing for `I.adele.thm:adele-second-countable`). -/
@[tf_aux "I.adele.lem:finadele-second-countable-instance"]
instance finAdele_secondCountableTopology : SecondCountableTopology FinAdele :=
  resProd_secondCountableTopology (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ (PadicInt.subring p : Set ℚ_[p]))
    isOpen_padicSubring

/-- `(n : 𝔸_f)_p = n` (proof helper). -/
theorem finAdele_intCast_apply (n : ℤ) (p : Nat.Primes) : (n : FinAdele) p = (n : ℚ_[p]) :=
  map_intCast (evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p]) n

/-- A rational number lying in `ℤ_p` for every `p` is an integer (proof helper). -/
theorem rat_isInt_of_forall_padicInt (q : ℚ) (h : ∀ p : Nat.Primes, ‖(q : ℚ_[p])‖ ≤ 1) : ∃ n : ℤ, q = n := by
  refine ⟨q.num, ?_⟩
  have hden : q.den = 1 := by
    by_contra hd
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have h1 : ‖(q.den : ℚ_[ℓ])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hℓd
    have h2 : ‖(q.num : ℚ_[ℓ])‖ = 1 := by
      rw [Padic.norm_intCast_eq_one_iff, Int.isCoprime_iff_gcd_eq_one]
      exact Nat.Coprime.coprime_dvd_right hℓd q.reduced
    have h3 : ‖(q : ℚ_[ℓ])‖ ≤ 1 := h ⟨ℓ, hℓ⟩
    have hcast : (q : ℚ_[ℓ]) = (q.num : ℚ_[ℓ]) / (q.den : ℚ_[ℓ]) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    rw [hcast, norm_div, h2] at h3
    have h4 : 0 < ‖(q.den : ℚ_[ℓ])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
    rw [div_le_one h4] at h3
    linarith
  rw [← Rat.num_div_den q, hden]; simp

/-- The only rational number in `(-1, 1) × Ẑ` is `0` (proof helper). -/
theorem rat_eq_zero_of_mem_box (q : ℚ) (h1 : (q : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (h2 : (algebraMap ℚ FinAdele q) ∈ Zhat) : q = 0 := by
  obtain ⟨n, rfl⟩ := rat_isInt_of_forall_padicInt q fun p ↦ mem_zhat.mp h2 p
  have : n = 0 := by
    have a : (-1 : ℝ) < ((n : ℚ) : ℝ) := h1.1
    have b : ((n : ℚ) : ℝ) < 1 := h1.2
    push_cast at a b
    have a' : -1 < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega
  simp [this]

/-- The image of `ℚ` in `𝔸` is a discrete closed additive subgroup; more precisely, the only rational number in
`(-1, 1) × Ẑ` is `0`. -/
@[tf_id "I.adele.thm:rat-discrete"]
theorem rat_discrete :
    IsClosed (Set.range (algebraMap ℚ Adele)) ∧ DiscreteTopology (Set.range (algebraMap ℚ Adele)) ∧
      ∀ q : ℚ, (algebraMap ℚ Adele q).1 ∈ Set.Ioo (-1 : ℝ) 1 → (algebraMap ℚ Adele q).2 ∈ Zhat → q = 0 := by
  have hbox : ∀ q : ℚ, (algebraMap ℚ Adele q).1 ∈ Set.Ioo (-1 : ℝ) 1 → (algebraMap ℚ Adele q).2 ∈ Zhat → q = 0 :=
    fun q h1 h2 ↦ rat_eq_zero_of_mem_box q h1 h2
  -- `W = (-1/2, 1/2) × Ẑ`, an open neighbourhood of `0` with `W - W ⊆ (-1, 1) × Ẑ`
  set W : Set Adele := Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ×ˢ (Zhat : Set FinAdele)
  have hWo : IsOpen W := isOpen_Ioo.prod isOpen_zhat_adele
  have hdiff : ∀ q q' : ℚ, ∀ x : Adele, algebraMap ℚ Adele q - x ∈ W → algebraMap ℚ Adele q' - x ∈ W → q = q' := by
    intro q q' x hq hq'
    have := hbox (q - q') ?_ ?_
    · linarith
    · obtain ⟨⟨a1, a2⟩, -⟩ := hq
      obtain ⟨⟨b1, b2⟩, -⟩ := hq'
      have e : (algebraMap ℚ Adele (q - q')).1 = (algebraMap ℚ Adele q - x).1 - (algebraMap ℚ Adele q' - x).1 := by
        rw [map_sub]; simp
      rw [e]; constructor <;> linarith
    · have e : (algebraMap ℚ Adele (q - q')).2 = (algebraMap ℚ Adele q - x).2 - (algebraMap ℚ Adele q' - x).2 := by
        rw [map_sub]; simp
      rw [e]
      exact Zhat.sub_mem hq.2 hq'.2
  have h0W : (0 : Adele) ∈ W := ⟨⟨by norm_num, by norm_num⟩, Zhat.zero_mem⟩
  have hcont : ∀ x : Adele, Continuous fun y : Adele ↦ y - x := fun x ↦ continuous_id.sub continuous_const
  refine ⟨?_, ?_, hbox⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    by_cases h : ∃ a : ℚ, algebraMap ℚ Adele a - x ∈ W
    · obtain ⟨a, ha⟩ := h
      refine ⟨(fun y ↦ y - x) ⁻¹' W ∩ {algebraMap ℚ Adele a}ᶜ, ?_, (hWo.preimage (hcont x)).inter
        isOpen_compl_singleton, ⟨by simpa using h0W, fun hxa ↦ hx ⟨a, hxa.symm⟩⟩⟩
      rintro y ⟨hy1, hy2⟩ ⟨q, rfl⟩
      exact hy2 (by rw [hdiff q a x hy1 ha]; exact Set.mem_singleton _)
    · refine ⟨(fun y ↦ y - x) ⁻¹' W, ?_, hWo.preimage (hcont x), by simpa using h0W⟩
      rintro y hy ⟨q, rfl⟩
      exact h ⟨q, hy⟩
  · rw [discreteTopology_iff_isOpen_singleton]
    rintro ⟨_, q0, rfl⟩
    refine ⟨(fun y ↦ y - algebraMap ℚ Adele q0) ⁻¹' W, hWo.preimage (hcont _), ?_⟩
    ext ⟨_, q, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      rw [hdiff q q0 (algebraMap ℚ Adele q0) hq (by simpa using h0W)]
    · intro hq
      rw [show algebraMap ℚ Adele q = algebraMap ℚ Adele q0 from congrArg Subtype.val hq, sub_self]
      exact h0W

/-- With `D = [0, 1) × Ẑ`, every adele is uniquely `x = q + y` with `q ∈ ℚ` and `y ∈ D`. -/
@[tf_id "I.adele.thm:adele-fundamental-domain"]
theorem adele_fundamental_domain (x : Adele) :
    ∃! qy : ℚ × Adele, qy.2 ∈ Set.Ico (0 : ℝ) 1 ×ˢ (Zhat : Set FinAdele) ∧ x = algebraMap ℚ Adele qy.1 + qy.2 := by
  have hfst : ∀ r : ℚ, (algebraMap ℚ Adele r).1 = r := fun r ↦ (algebraMap_adele_diagonal.2 r).1
  have hsnd : ∀ r : ℚ, (algebraMap ℚ Adele r).2 = algebraMap ℚ FinAdele r := fun r ↦ rfl
  obtain ⟨q1, hq1⟩ := padic_exists_sub_mem_structureSubring x.2
  have hq1' : x.2 - algebraMap ℚ FinAdele q1 ∈ Zhat := by
    rw [mem_zhat]; exact mem_structureSubring_iff.mp hq1
  set n : ℤ := ⌊x.1 - q1⌋
  set q : ℚ := q1 + n
  have hy1 : (x - algebraMap ℚ Adele q).1 = x.1 - q1 - n := by
    rw [Prod.fst_sub, hfst]; simp only [q]; push_cast; ring
  have hy2 : (x - algebraMap ℚ Adele q).2 = (x.2 - algebraMap ℚ FinAdele q1) - (n : FinAdele) := by
    rw [Prod.snd_sub, hsnd]; simp only [q, map_add, map_intCast]; ring
  refine ⟨(q, x - algebraMap ℚ Adele q), ⟨⟨⟨?_, ?_⟩, ?_⟩, by simp⟩, ?_⟩
  · show 0 ≤ (x - algebraMap ℚ Adele q).1
    rw [hy1]; linarith [Int.floor_le (x.1 - q1)]
  · show (x - algebraMap ℚ Adele q).1 < 1
    rw [hy1]; linarith [Int.lt_floor_add_one (x.1 - q1)]
  · show (x - algebraMap ℚ Adele q).2 ∈ Zhat
    rw [hy2]
    exact Zhat.sub_mem hq1' (intCast_mem Zhat n)
  · rintro ⟨q', y'⟩ ⟨⟨⟨h0, h1⟩, hZ⟩, hx⟩
    simp only at h0 h1 hZ hx
    have hdq : q' - q = 0 := by
      apply rat_eq_zero_of_mem_box
      · have e : ((q' - q : ℚ) : ℝ) = (x - algebraMap ℚ Adele q).1 - y'.1 := by
          rw [hx, Prod.fst_sub, Prod.fst_add, hfst, hfst]; push_cast; ring
        rw [e]
        constructor <;> [linarith [h1, (show 0 ≤ (x - algebraMap ℚ Adele q).1 by
          rw [hy1]; linarith [Int.floor_le (x.1 - q1)])]; linarith [h0, (show (x - algebraMap ℚ Adele q).1 < 1 by
          rw [hy1]; linarith [Int.lt_floor_add_one (x.1 - q1)])]]
      · have e : algebraMap ℚ FinAdele (q' - q) = (x - algebraMap ℚ Adele q).2 - y'.2 := by
          rw [hx, Prod.snd_sub, Prod.snd_add, hsnd, hsnd, map_sub]; ring
        rw [e, hy2]
        exact Zhat.sub_mem (Zhat.sub_mem hq1' (intCast_mem Zhat n)) hZ
    have hqq : q' = q := sub_eq_zero.mp hdq
    subst hqq
    refine Prod.ext rfl ?_
    simp only
    rw [hx]; ring

/-- `ℚ\𝔸` is a compact Hausdorff space: the quotient of `𝔸` by the image of `ℚ` is compact (it is the image of the
compact set `[0, 1] × Ẑ`) and Hausdorff (`ℚ` is closed in `𝔸`). Measure-free; fork-new (the parent's
`I.adele.thm:rat-quotient-compact` also normalized a Haar measure). -/
@[tf_id "I.adele.thm:rat-quotient-compact-top"]
theorem rat_quotient_compact_top :
    CompactSpace (Adele ⧸ (algebraMap ℚ Adele).range.toAddSubgroup) ∧
      T2Space (Adele ⧸ (algebraMap ℚ Adele).range.toAddSubgroup) := by
  set Γ := (algebraMap ℚ Adele).range.toAddSubgroup
  refine ⟨?_, ?_⟩
  · -- compactness: the image of the compact set `[0,1] × Ẑ`
    have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Zhat : Set FinAdele)) := isCompact_Icc.prod isCompact_zhat
    have himg : (QuotientAddGroup.mk : Adele → Adele ⧸ Γ) '' (Set.Icc (0 : ℝ) 1 ×ˢ (Zhat : Set FinAdele)) =
        Set.univ := by
      refine Set.eq_univ_of_forall fun c ↦ ?_
      induction c using QuotientAddGroup.induction_on with
      | H x =>
        obtain ⟨⟨q, y⟩, ⟨hy, hx⟩, -⟩ := adele_fundamental_domain x
        simp only at hx hy
        refine ⟨y, ⟨Set.Ico_subset_Icc_self hy.1, hy.2⟩, ?_⟩
        rw [QuotientAddGroup.eq]
        exact ⟨q, by rw [hx]; abel⟩
    exact ⟨himg ▸ hK.image continuous_quot_mk⟩
  · -- Hausdorff: `ℚ` is a closed subgroup
    have hcl : IsClosed (Γ : Set Adele) := by
      have h : (Γ : Set Adele) = Set.range (algebraMap ℚ Adele) := by
        ext x; simp [Γ]
      rw [h]; exact rat_discrete.1
    have : IsClosed (Γ : Set Adele) := hcl
    infer_instance

/-! ### Cosets `a + Nℤ_p` and `a + NẐ` (proof helpers) -/

/-- `y ∈ b + cℤ_p ↔ |y - b|_p ≤ |c|_p` for `c ≠ 0` (proof helper). -/
theorem padic_mem_vadd_smul_iff {p : Nat.Primes} {c : ℚ_[p]} (hc : c ≠ 0) (b y : ℚ_[p]) :
    y ∈ b +ᵥ c • (PadicInt.subring p : Set ℚ_[p]) ↔ ‖y - b‖ ≤ ‖c‖ := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_smul_set_iff_inv_smul_mem₀ hc, smul_eq_mul]
  change ‖c⁻¹ * (-b + y)‖ ≤ 1 ↔ _
  rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hc), mul_one, neg_add_eq_sub]

/-- `(n : 𝔸_f)_p = n` (proof helper). -/
theorem finAdele_natCast_apply (n : ℕ) (p : Nat.Primes) : (n : FinAdele) p = (n : ℚ_[p]) :=
  map_natCast (evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p]) n

/-- `x ∈ a + NẐ ↔ x_p ∈ a + Nℤ_p` for all `p` (proof helper). -/
theorem mem_rat_vadd_natCast_smul_zhat (a : ℚ) (N : ℕ) (x : FinAdele) :
    x ∈ algebraMap ℚ FinAdele a +ᵥ ((N : FinAdele) • (Zhat : Set FinAdele)) ↔
      ∀ p : Nat.Primes, x p ∈ (a : ℚ_[p]) +ᵥ (N : ℚ_[p]) • (PadicInt.subring p : Set ℚ_[p]) := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩ p
    refine ⟨(N : ℚ_[p]) * z p, ⟨z p, mem_zhat.mp hz p, rfl⟩, ?_⟩
    change (a : ℚ_[p]) + (N : ℚ_[p]) * z p = (algebraMap ℚ FinAdele a + (N : FinAdele) * z) p
    rw [RestrictedProduct.add_apply, RestrictedProduct.mul_apply, finAdele_natCast_apply]
    rfl
  · intro h
    choose w hw hwx using fun p ↦ (h p)
    have hw' : ∀ p : Nat.Primes, ∃ v, v ∈ (PadicInt.subring p : Set ℚ_[p]) ∧ (N : ℚ_[p]) • v = w p := fun p ↦ hw p
    choose v hv hvw using hw'
    let z : FinAdele := ⟨v, Eventually.of_forall hv⟩
    refine ⟨(N : FinAdele) * z, ⟨z, mem_zhat.mpr hv, rfl⟩, ?_⟩
    ext p
    change (algebraMap ℚ FinAdele a + (N : FinAdele) * z) p = x p
    rw [RestrictedProduct.add_apply, RestrictedProduct.mul_apply, finAdele_natCast_apply, ← hwx p, ← hvw p]
    rfl

/-! ### `ℤ_p` as a compact open additive subgroup; rationals in `a + NẐ` -/

/-- `ℤ_p` is open in `ℚ_p` (proof helper). -/
theorem isOpen_padicIntSubring (p : Nat.Primes) :
    IsOpen ((PadicInt.subring p).toAddSubgroup : Set ℚ_[p]) := by
  have : ((PadicInt.subring p).toAddSubgroup : Set ℚ_[p]) = Metric.closedBall 0 1 := by
    ext x; simp [PadicInt.mem_subring_iff]
  rw [this]
  exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero

/-- `ℤ_p` is compact, as an instance on the additive subgroup (B-only plumbing for `I.adele.def:adele-haar`). -/
@[tf_aux "I.adele.lem:padic-int-compact-instance"]
instance padicIntAddSubgroup_compactSpace (p : Nat.Primes) :
    CompactSpace ((PadicInt.subring p).toAddSubgroup) := by
  have : ((PadicInt.subring p).toAddSubgroup : Set ℚ_[p]) = Metric.closedBall 0 1 := by
    ext x; simp [PadicInt.mem_subring_iff]
  exact isCompact_iff_compactSpace.mp (this ▸ isCompact_closedBall 0 1)

/-- A rational `q` lies in `a + NẐ` iff `q = a + Nm` with `m ∈ ℤ` (proof helper). -/
theorem rat_mem_vadd_natCast_smul_zhat_iff (a q : ℚ) {N : ℕ} (hN : N ≠ 0) :
    algebraMap ℚ FinAdele q ∈ algebraMap ℚ FinAdele a +ᵥ ((N : FinAdele) • (Zhat : Set FinAdele)) ↔
      ∃ m : ℤ, q = a + N * m := by
  rw [mem_rat_vadd_natCast_smul_zhat]
  have hN' : ∀ p : Nat.Primes, (N : ℚ_[p]) ≠ 0 := fun p ↦ Nat.cast_ne_zero.mpr hN
  constructor
  · intro h
    have : ∀ p : Nat.Primes, ‖(((q - a) / N : ℚ) : ℚ_[p])‖ ≤ 1 := by
      intro p
      have := (padic_mem_vadd_smul_iff (hN' p) _ _).mp (h p)
      rw [Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, norm_div, div_le_one (norm_pos_iff.mpr (hN' p))]
      exact this
    obtain ⟨m, hm⟩ := rat_isInt_of_forall_padicInt _ this
    refine ⟨m, ?_⟩
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [div_eq_iff hNq] at hm
    linarith
  · rintro ⟨m, rfl⟩ p
    rw [padic_mem_vadd_smul_iff (hN' p)]
    change ‖(((a + N * m : ℚ)) : ℚ_[p]) - (a : ℚ_[p])‖ ≤ ‖(N : ℚ_[p])‖
    push_cast
    rw [add_sub_cancel_left, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Padic.norm_int_le_one m)

end GL2TF
