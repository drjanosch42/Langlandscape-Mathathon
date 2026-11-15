/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.ThmE
import Langlandscape.CommAlg.DVR
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Non-vacuity of the CommAlg layer: the toy `S = {(x, y) : x ≡ y mod p^t}` (S06-L10a)

`mathematics/chapters/s06/s06-m1.tex`, `ex:s06-toy`, `lem:s06-S`, `lem:s06-D`, `thm:s06-E`
(secondary reference: `plan/staged/stage-06-integral-defect.tex`, `ss:s06-ca`). Everything is first
done for a domain `A` and an element `ϖ ≠ 0`:

* `Toy.toy ϖ = {(x, y) ∈ A × A : ϖ ∣ x - y}`, an `A`-subalgebra of `A × A`, free with basis
  `1 = (1, 1)`, `X = (ϖ, 0)` (`Toy.coordEquiv`);
* `Toy.isGorensteinWith`: it is `A`-Gorenstein with trace `ℓ(x, y) = (x - y)/ϖ` (`Toy.trace`);
* `Toy.data`: a `NewOldData` with the coordinate kernels `𝔞 = ker pr₁`, `𝔟 = ker pr₂`;
* `Toy.congruenceIdeal_fst`: `η(S, pr₁) = (ϖ)`, the generator of `S[pr₁]` being `θ = X`;
* Lemma D (`lem:s06-D`(a)–(c)) and Thm E (`thm:s06-E`(i)–(iv)) instantiated, with
  `c_q = pr₁(𝔟) = (ϖ)` and `η(S', λ') = (1)`, so `η = c_q · η'` reads `(ϖ) = (ϖ) · (1)`.

Then `ϖ := p^t` in `ℤ_[p]` (`Toy.Zp.*`, which also instantiates the DVR half of `thm:s06-E`(iii),
`Toy.Zp.thmE_dvr`, since `ℤ_[p]` is a discrete valuation ring). **Edge case `t = 0`**: `ϖ = 1 ≠ 0`,
so nothing changes: `S = ℤ_[p] × ℤ_[p]`, `X = (1, 0)` is an idempotent, `S` is still Gorenstein, the
`NewOldData` is the split product (`1 ∈ 𝔞 + 𝔟`), and `η(S, pr₁) = c_q = (1) = ⊤`
(`Toy.Zp.congruenceIdeal_fst_zero`): the two coordinates are not congruent. All statements hold for
every `t : ℕ`; no `t ≥ 1` is needed. The only
excluded value is `ϖ = 0` (`t = ∞`), where `S` is the diagonal, of rank one, and `split` fails.
-/

@[expose] public section

set_option autoImplicit false
-- One `variable` block (`[IsDomain A]`, `ϖ`) serves the whole file; some small lemmas do not use
-- all of it.
set_option linter.unusedSectionVars false

namespace Langlandscape.CommAlg

namespace Toy

variable {A : Type*} [CommRing A] [IsDomain A] (ϖ : A)

/-- `ss:s06-ca` (`s06-ca`), toy: the `A`-subalgebra `{(x, y) : ϖ ∣ x - y}` of `A × A`
(for `ϖ = p^t` in `ℤ_[p]`: the pairs with `x ≡ y mod p^t`). -/
def toy : Subalgebra A (A × A) where
  carrier := {z | ϖ ∣ z.1 - z.2}
  mul_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ (hz : ϖ ∣ x - y) (hz' : ϖ ∣ x' - y')
    show ϖ ∣ x * x' - y * y'
    have h : x * x' - y * y' = x * (x' - y') + (x - y) * y' := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_right hz' _) (dvd_mul_of_dvd_left hz _)
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ (hz : ϖ ∣ x - y) (hz' : ϖ ∣ x' - y')
    show ϖ ∣ x + x' - (y + y')
    have h : x + x' - (y + y') = (x - y) + (x' - y') := by ring
    rw [h]
    exact dvd_add hz hz'
  algebraMap_mem' := fun a => by
    show ϖ ∣ (algebraMap A (A × A) a).1 - (algebraMap A (A × A) a).2
    simp [Prod.algebraMap_apply]

/-- `ss:s06-ca` (`s06-ca`), toy: membership in `toy ϖ`. -/
theorem mem_toy {z : A × A} : z ∈ toy ϖ ↔ ϖ ∣ z.1 - z.2 := Iff.rfl

/-- `ss:s06-ca` (`s06-ca`), toy: the quotient `(x - y)/ϖ` of `z = (x, y)` (a chosen witness of
`ϖ ∣ x - y`; unique when `ϖ ≠ 0`, see `Toy.quo_unique`). -/
noncomputable def quo (z : toy ϖ) : A :=
  Classical.choose (show ∃ c, (z : A × A).1 - (z : A × A).2 = ϖ * c from z.2)

/-- `ss:s06-ca` (`s06-ca`), toy: `x - y = ϖ · quo z`. -/
theorem quo_spec (z : toy ϖ) : (z : A × A).1 - (z : A × A).2 = ϖ * quo ϖ z :=
  Classical.choose_spec (show ∃ c, (z : A × A).1 - (z : A × A).2 = ϖ * c from z.2)

variable {ϖ} (hϖ : ϖ ≠ 0)

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: for `ϖ ≠ 0` the quotient is unique. -/
theorem quo_unique {z : toy ϖ} {c : A} (h : (z : A × A).1 - (z : A × A).2 = ϖ * c) :
    quo ϖ z = c :=
  mul_left_cancel₀ hϖ (by rw [← quo_spec, h])

/-- `ss:s06-ca` (`s06-ca`), toy: the trace `ℓ(x, y) = (x - y)/ϖ`, an `A`-linear form on `toy ϖ`. -/
noncomputable def trace : Module.Dual A (toy ϖ) where
  toFun := quo ϖ
  map_add' z w := quo_unique hϖ (by
    show (z : A × A).1 + (w : A × A).1 - ((z : A × A).2 + (w : A × A).2) = _
    linear_combination quo_spec ϖ z + quo_spec ϖ w)
  map_smul' a z := quo_unique hϖ (by
    show a * (z : A × A).1 - a * (z : A × A).2 = ϖ * (a * quo ϖ z)
    linear_combination a * quo_spec ϖ z)

/-- `ss:s06-ca` (`s06-ca`), toy: `trace hϖ z = quo ϖ z`. -/
theorem trace_apply (z : toy ϖ) : trace hϖ z = quo ϖ z := rfl

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: the element `X = (ϖ, 0)`. -/
def X : toy ϖ := ⟨(ϖ, 0), by rw [mem_toy]; simp⟩

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: the element `Y = (0, ϖ)`. -/
def Y : toy ϖ := ⟨(0, ϖ), by rw [mem_toy]; simp⟩

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: `quo X = 1`. -/
theorem quo_X : quo ϖ (X ϖ) = 1 :=
  quo_unique hϖ (by show ϖ - 0 = ϖ * 1; ring)

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: `quo 1 = 0`. -/
theorem quo_one : quo ϖ (1 : toy ϖ) = 0 :=
  quo_unique hϖ (by show (1 : A) - 1 = ϖ * 0; ring)

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: the key multiplication formula
`quo (s z) = s₁ · quo z + quo s · z₂`. -/
theorem quo_mul (s z : toy ϖ) :
    quo ϖ (s * z) = (s : A × A).1 * quo ϖ z + quo ϖ s * (z : A × A).2 :=
  quo_unique hϖ (by
    show (s : A × A).1 * (z : A × A).1 - (s : A × A).2 * (z : A × A).2 = _
    linear_combination (s : A × A).1 * quo_spec ϖ z + (z : A × A).2 * quo_spec ϖ s)

/-- `ss:s06-ca` (`s06-ca`), toy: every `z = (x, y)` is `y · 1 + quo z · X`. -/
theorem eq_add (z : toy ϖ) : z = (z : A × A).2 • (1 : toy ϖ) + quo ϖ z • X ϖ := by
  apply Subtype.ext
  apply Prod.ext
  · show (z : A × A).1 = (z : A × A).2 * 1 + quo ϖ z * ϖ
    linear_combination quo_spec ϖ z
  · show (z : A × A).2 = (z : A × A).2 * 1 + quo ϖ z * 0
    ring

/-- `ss:s06-ca` (`s06-ca`), toy: the coordinates `z ↦ (y, (x - y)/ϖ)`, an `A`-linear isomorphism
`toy ϖ ≃ A × A` (basis `1`, `X`). -/
noncomputable def coordEquiv : toy ϖ ≃ₗ[A] A × A where
  toFun z := ((z : A × A).2, quo ϖ z)
  map_add' z w := Prod.ext rfl ((trace hϖ).map_add z w)
  map_smul' a z := Prod.ext rfl ((trace hϖ).map_smul a z)
  invFun ab := ⟨(ab.1 + ϖ * ab.2, ab.1), by rw [mem_toy]; exact ⟨ab.2, by ring⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · show (z : A × A).2 + ϖ * quo ϖ z = (z : A × A).1
      linear_combination -(quo_spec ϖ z)
    · rfl
  right_inv ab := Prod.ext rfl (quo_unique hϖ (by show ab.1 + ϖ * ab.2 - ab.1 = ϖ * ab.2; ring))

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: `toy ϖ` is a free `A`-module. -/
theorem free : Module.Free A (toy ϖ) := Module.Free.of_equiv (coordEquiv hϖ).symm

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: `toy ϖ` is a finite `A`-module. -/
theorem finite : Module.Finite A (toy ϖ) := Module.Finite.equiv (coordEquiv hϖ).symm

/-- `ss:s06-ca` (`s06-ca`), toy: `toy ϖ` is `A`-Gorenstein with trace `ℓ(x, y) = (x - y)/ϖ`. -/
theorem isGorensteinWith : IsGorensteinWith A (toy ϖ) (trace hϖ) := by
  refine ⟨free hϖ, finite hϖ, ?_, ?_⟩
  · intro s t h
    have h1 := LinearMap.congr_fun h 1
    have hX := LinearMap.congr_fun h (X ϖ)
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, trace_apply] at h1 hX
    rw [quo_mul hϖ, quo_mul hϖ, quo_X hϖ] at hX
    have hX' : (s : A × A).1 = (t : A × A).1 := by
      simpa [X] using hX
    apply Subtype.ext
    apply Prod.ext hX'
    have hs := quo_spec ϖ s
    have ht := quo_spec ϖ t
    rw [h1] at hs
    linear_combination ht - hs + hX'
  · intro φ
    let s : toy ϖ := ⟨(φ (X ϖ), φ (X ϖ) - ϖ * φ 1), by rw [mem_toy]; exact ⟨φ 1, by ring⟩⟩
    have hqs : quo ϖ s = φ 1 := quo_unique hϖ (by show φ (X ϖ) - (φ (X ϖ) - ϖ * φ 1) = _; ring)
    refine ⟨s, LinearMap.ext fun z => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, trace_apply, quo_mul hϖ, hqs]
    conv_rhs => rw [eq_add z]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    show φ (X ϖ) * quo ϖ z + φ 1 * (z : A × A).2 = _
    ring

include hϖ in
/-- `ss:s06-ca` (`s06-ca`), toy: `toy ϖ` is `A`-Gorenstein. -/
theorem isGorenstein : IsGorenstein A (toy ϖ) := ⟨_, isGorensteinWith hϖ⟩

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: the first projection `pr₁ : toy ϖ → A` (this is `λ`). -/
def fst : toy ϖ →ₐ[A] A := (AlgHom.fst A A A).comp (toy ϖ).val

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: the second projection `pr₂ : toy ϖ → A`. -/
def snd : toy ϖ →ₐ[A] A := (AlgHom.snd A A A).comp (toy ϖ).val

/-- `ss:s06-ca` (`s06-ca`), toy: `pr₁ z = x`. -/
theorem fst_apply (z : toy ϖ) : fst ϖ z = (z : A × A).1 := rfl

/-- `ss:s06-ca` (`s06-ca`), toy: `pr₂ z = y`. -/
theorem snd_apply (z : toy ϖ) : snd ϖ z = (z : A × A).2 := rfl

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: `λ' : S/ker pr₁ → A` induced by `pr₁`. -/
noncomputable def lamFst : toy ϖ ⧸ RingHom.ker (fst ϖ) →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (fst ϖ) (fun _ h => h)

variable (ϖ) in
/-- `ss:s06-ca` (`s06-ca`), toy: `S/ker pr₂ → A` induced by `pr₂`. -/
noncomputable def lamSnd : toy ϖ ⧸ RingHom.ker (snd ϖ) →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (snd ϖ) (fun _ h => h)

/-- `ss:s06-ca` (`s06-ca`), toy: `λ'(z mod 𝔞) = pr₁ z`. -/
theorem lamFst_mk (z : toy ϖ) : lamFst ϖ (Ideal.Quotient.mk (RingHom.ker (fst ϖ)) z) = fst ϖ z :=
  rfl

/-- `ss:s06-ca` (`s06-ca`), toy: `(z mod 𝔟) ↦ pr₂ z`. -/
theorem lamSnd_mk (z : toy ϖ) : lamSnd ϖ (Ideal.Quotient.mk (RingHom.ker (snd ϖ)) z) = snd ϖ z :=
  rfl

/-- `ss:s06-ca` (`s06-ca`), toy: `λ'` is injective. -/
theorem lamFst_injective : Function.Injective (lamFst ϖ) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Ideal.Quotient.eq_zero_iff_mem.2 hq

/-- `ss:s06-ca` (`s06-ca`), toy: `S/ker pr₂ → A` is injective. -/
theorem lamSnd_injective : Function.Injective (lamSnd ϖ) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Ideal.Quotient.eq_zero_iff_mem.2 hq

/-- `ss:s06-ca` (`s06-ca`), toy: `λ'` is surjective. -/
theorem lamFst_surjective : Function.Surjective (lamFst ϖ) := fun a =>
  ⟨algebraMap A _ a, by rw [AlgHom.commutes]; rfl⟩

/-- `ss:s06-ca` (`s06-ca`), toy: `S/ker pr₂ → A` is surjective. -/
theorem lamSnd_surjective : Function.Surjective (lamSnd ϖ) := fun a =>
  ⟨algebraMap A _ a, by rw [AlgHom.commutes]; rfl⟩

/-- `lem:s06-D` (`s06-D`), toy: the `NewOldData` with the coordinate kernels `𝔞 = ker pr₁`,
`𝔟 = ker pr₂` (`S/𝔞 ≅ A ≅ S/𝔟`, `𝔞 ∩ 𝔟 = 0`, and `(ϖ, ϖ) = Y + X ∈ 𝔞 + 𝔟` with `ϖ ≠ 0`). -/
noncomputable def data : NewOldData A (toy ϖ) where
  𝔞 := RingHom.ker (fst ϖ)
  𝔟 := RingHom.ker (snd ϖ)
  free := free hϖ
  finite := finite hϖ
  tf_a := Function.Injective.moduleIsTorsionFree _ lamFst_injective
    (fun r m => map_smul (lamFst ϖ) r m)
  tf_b := Function.Injective.moduleIsTorsionFree _ lamSnd_injective
    (fun r m => map_smul (lamSnd ϖ) r m)
  inf_eq_bot := by
    rw [eq_bot_iff]
    rintro z ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)
  split := by
    refine ⟨ϖ, hϖ, Submodule.mem_sup.2 ⟨Y ϖ, ?_, X ϖ, ?_, ?_⟩⟩
    · show (0 : A) = 0; rfl
    · show (0 : A) = 0; rfl
    · apply Subtype.ext
      apply Prod.ext
      · show (0 : A) + ϖ = (algebraMap A (A × A) ϖ).1
        simp [Prod.algebraMap_apply]
      · show ϖ + (0 : A) = (algebraMap A (A × A) ϖ).2
        simp [Prod.algebraMap_apply]

/-- `lem:s06-D` (`s06-D`), toy: `𝔞 = ker pr₁`. -/
theorem data_a : (data hϖ).𝔞 = RingHom.ker (fst ϖ) := rfl

/-- `lem:s06-D` (`s06-D`), toy: `𝔟 = ker pr₂`. -/
theorem data_b : (data hϖ).𝔟 = RingHom.ker (snd ϖ) := rfl

/-- `lem:s06-S` (`s06-S`), toy: `θ = X = (ϖ, 0)` is the generator of `S[pr₁]`
(`ℓ(X z) = ϖ · quo z + y = x`). -/
theorem theta_eq_X : LemmaS.theta (isGorensteinWith hϖ) (fst ϖ) = X ϖ := by
  refine (LemmaS.theta_unique (isGorensteinWith hϖ) (fst ϖ) fun z => ?_).symm
  rw [trace_apply, quo_mul hϖ, quo_X hϖ, fst_apply]
  show ϖ * quo ϖ z + 1 * (z : A × A).2 = (z : A × A).1
  linear_combination -(quo_spec ϖ z)

include hϖ in
/-- `lem:s06-S` (`s06-S`), toy: `η(S, pr₁) = (ϖ)`; for `ϖ = p^t` this is `(p^t)`. -/
theorem congruenceIdeal_fst : congruenceIdeal (fst ϖ) = Ideal.span {ϖ} := by
  rw [LemmaS.congruenceIdeal_eq_span (isGorensteinWith hϖ), theta_eq_X hϖ]
  rfl

/-- `thm:s06-E` (`s06-E`), toy: `λ' : S' = S ⧸ 𝔞 → A` (`= lamFst`, typed with `(data hϖ).𝔞`). -/
noncomputable def lam' : toy ϖ ⧸ (data hϖ).𝔞 →ₐ[A] A := lamFst ϖ

/-- `thm:s06-E` (`s06-E`), toy: `λ'` is injective. -/
theorem lam'_injective : Function.Injective (lam' hϖ) := lamFst_injective

/-- `thm:s06-E` (`s06-E`), toy: `λ'` is surjective. -/
theorem lam'_surjective : Function.Surjective (lam' hϖ) := lamFst_surjective

section LemmaDThmE

variable [IsNoetherianRing A] [IsLocalRing A]

include hϖ in
/-- `lem:s06-D` (`s06-D`)(a), toy: `Ann_S(ker pr₁) = ker pr₂`. -/
theorem ann_a : ann (RingHom.ker (fst ϖ)) = RingHom.ker (snd ϖ) := (data hϖ).ann_a

include hϖ in
/-- `lem:s06-D` (`s06-D`)(a), toy: `Ann_S(ker pr₂) = ker pr₁`. -/
theorem ann_b : ann (RingHom.ker (snd ϖ)) = RingHom.ker (fst ϖ) := (data hϖ).ann_b

/-- `lem:s06-D` (`s06-D`)(b), toy: `𝔟 ≅ (S/𝔞)^∨` and `𝔞 ≅ (S/𝔟)^∨` via `β ↦ ℓ(β ·)`. -/
theorem lemmaD_b :
    Nonempty ((data hϖ).𝔟 ≃ₗ[A] Module.Dual A (toy ϖ ⧸ (data hϖ).𝔞)) ∧
      Nonempty ((data hϖ).𝔞 ≃ₗ[A] Module.Dual A (toy ϖ ⧸ (data hϖ).𝔟)) :=
  ⟨⟨(data hϖ).bEquivDualQuot (isGorensteinWith hϖ)⟩,
    ⟨(data hϖ).aEquivDualQuot (isGorensteinWith hϖ)⟩⟩

/-- `lem:s06-D` (`s06-D`)(c), toy: `S/𝔟 ≅ A` is free. -/
theorem free_quot_b : Module.Free A (toy ϖ ⧸ (data hϖ).𝔟) :=
  Module.Free.of_equiv
    (LinearEquiv.ofBijective (lamSnd ϖ).toLinearMap
      ⟨lamSnd_injective, lamSnd_surjective⟩).symm

/-- `lem:s06-D` (`s06-D`)(c), toy: `𝔟` is a direct summand, `𝔟` and `S/𝔞` are free, and
`S/𝔞 ≅ 𝔟^∨`. -/
theorem lemmaD_c :
    IsComplemented ((data hϖ).𝔟.restrictScalars A) ∧ Module.Free A (data hϖ).𝔟 ∧
      Module.Free A (toy ϖ ⧸ (data hϖ).𝔞) ∧
      Nonempty ((toy ϖ ⧸ (data hϖ).𝔞) ≃ₗ[A] Module.Dual A (data hϖ).𝔟) :=
  ⟨(data hϖ).isComplemented_b (free_quot_b hϖ), (data hϖ).free_b (free_quot_b hϖ),
    (data hϖ).free_quot_a (isGorensteinWith hϖ) (free_quot_b hϖ),
    ⟨(data hϖ).quotAEquivDualB (isGorensteinWith hϖ) (free_quot_b hϖ)⟩⟩

/-- `thm:s06-E` (`s06-E`), toy: `λ = λ' ∘ (S → S/𝔞)` is `pr₁`. -/
theorem lam_eq : ThmE.lam (data hϖ) (lam' hϖ) = fst ϖ :=
  AlgHom.ext fun z => (ThmE.lam_apply (data hϖ) (lam' hϖ) z).trans (lamFst_mk z)

/-- `thm:s06-E` (`s06-E`)(i), toy: `θ ∈ 𝔟`. -/
theorem thmE_i_theta :
    LemmaS.theta (isGorensteinWith hϖ) (ThmE.lam (data hϖ) (lam' hϖ)) ∈ (data hϖ).𝔟 :=
  ThmE.theta_mem_b (data hϖ) (isGorensteinWith hϖ) (lam' hϖ)

/-- `thm:s06-E` (`s06-E`)(i), toy: `η(S, λ) = (λ'(θ mod 𝔞))`. -/
theorem thmE_i_eta :
    congruenceIdeal (ThmE.lam (data hϖ) (lam' hϖ)) = Ideal.span {lam' hϖ (Ideal.Quotient.mk
      (data hϖ).𝔞 (LemmaS.theta (isGorensteinWith hϖ) (ThmE.lam (data hϖ) (lam' hϖ))))} :=
  ThmE.eta_eq_span_lambda' (data hϖ) (isGorensteinWith hϖ) (lam' hϖ)

/-- `thm:s06-E` (`s06-E`)(i), toy: `c_q = λ(𝔟)` is the order ideal of `θ mod 𝔞`. -/
theorem thmE_i_c :
    (data hϖ).𝔟.map (ThmE.lam (data hϖ) (lam' hϖ)) = LinearMap.range (Module.Dual.eval A
      (toy ϖ ⧸ (data hϖ).𝔞) (Ideal.Quotient.mk (data hϖ).𝔞
        (LemmaS.theta (isGorensteinWith hϖ) (ThmE.lam (data hϖ) (lam' hϖ))))) :=
  ThmE.c_eq_orderIdeal (data hϖ) (isGorensteinWith hϖ) (lam' hϖ)

/-- `thm:s06-E` (`s06-E`), toy: `c_q = λ(𝔟) = pr₁(ker pr₂) = (ϖ)`. -/
theorem c_eq : (data hϖ).𝔟.map (ThmE.lam (data hϖ) (lam' hϖ)) = Ideal.span {ϖ} := by
  rw [lam_eq]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    have hz2 : (z : A × A).2 = 0 := hz
    rw [Ideal.mem_comap, fst_apply, Ideal.mem_span_singleton]
    have h := quo_spec ϖ z
    rw [hz2, sub_zero] at h
    exact ⟨_, h⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem (fst ϖ) (show X ϖ ∈ (data hϖ).𝔟 from (RingHom.mem_ker).2 rfl)

/-- `ss:s06-ca` (`s06-ca`), toy: `S/𝔞 ≅ A` is Gorenstein with trace `λ'`. -/
theorem isGorensteinWith_quot :
    IsGorensteinWith A (toy ϖ ⧸ (data hϖ).𝔞) (lam' hϖ).toLinearMap := by
  have := finite hϖ
  have hfree : Module.Free A (toy ϖ ⧸ (data hϖ).𝔞) :=
    (data hϖ).free_quot_a (isGorensteinWith hϖ) (free_quot_b hϖ)
  have hfin : Module.Finite A (toy ϖ ⧸ (data hϖ).𝔞) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (data hϖ).𝔞).toLinearMap
      (Ideal.Quotient.mkₐ_surjective A (data hϖ).𝔞)
  refine ⟨hfree, hfin, ?_, ?_⟩
  · intro s t h
    have h1 : lam' hϖ (s * 1) = lam' hϖ (t * 1) := LinearMap.congr_fun h 1
    rw [mul_one, mul_one] at h1
    exact lam'_injective hϖ h1
  · intro φ
    refine ⟨algebraMap A _ (φ 1), LinearMap.ext fun q => ?_⟩
    have hq : q = algebraMap A _ (lam' hϖ q) :=
      lam'_injective hϖ (by rw [AlgHom.commutes]; rfl)
    have h1 : φ q = lam' hϖ q * φ 1 := by
      conv_lhs => rw [hq]
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    rw [h1, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]

/-- `lem:s06-S` (`s06-S`), toy: `η(S', λ') = (1)` (`λ'` is an isomorphism). -/
theorem congruenceIdeal_lam' : congruenceIdeal (lam' hϖ) = ⊤ := by
  have hker : RingHom.ker (lam' hϖ) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (lam'_injective hϖ)
  have hann : ann (⊥ : Ideal (toy ϖ ⧸ (data hϖ).𝔞)) = ⊤ := by
    ext x
    simp [mem_ann]
  unfold congruenceIdeal
  rw [hker, hann]
  exact Ideal.map_top _

/-- `thm:s06-E` (`s06-E`)(ii)+(iii), toy: `η(S, λ) = c_q · η(S', λ')`, via the Gorenstein half of
(iii) (`S' ≅ A` is Gorenstein). -/
theorem thmE_iii :
    congruenceIdeal (ThmE.lam (data hϖ) (lam' hϖ)) =
      (data hϖ).𝔟.map (ThmE.lam (data hϖ) (lam' hϖ)) * congruenceIdeal (lam' hϖ) :=
  ThmE.eta_eq_c_mul_of_isGorenstein (data hϖ) (isGorensteinWith hϖ) (lam' hϖ)
    ⟨_, isGorensteinWith_quot hϖ⟩

/-- `thm:s06-E` (`s06-E`)(ii)+(iii), toy, explicit: the identity reads `(ϖ) = (ϖ) · (1)`. -/
theorem thmE_explicit :
    congruenceIdeal (ThmE.lam (data hϖ) (lam' hϖ)) = Ideal.span {ϖ} ∧
      (data hϖ).𝔟.map (ThmE.lam (data hϖ) (lam' hϖ)) = Ideal.span {ϖ} ∧
      congruenceIdeal (lam' hϖ) = ⊤ := by
  refine ⟨?_, c_eq hϖ, congruenceIdeal_lam' hϖ⟩
  rw [lam_eq]
  exact congruenceIdeal_fst hϖ

/-- `thm:s06-E` (`s06-E`)(iv), toy: `c = im(𝔟 → S')` is a principal ideal of `S'`, matching
(Gor_{S'}). -/
theorem thmE_iv : ((data hϖ).𝔟.map (Ideal.Quotient.mk (data hϖ).𝔞)).IsPrincipal :=
  (ThmE.c_principal_iff_isGorenstein (data hϖ) (isGorensteinWith hϖ)
    ((data hϖ).free_quot_a (isGorensteinWith hϖ) (free_quot_b hϖ))).2
    ⟨_, isGorensteinWith_quot hϖ⟩

end LemmaDThmE

/-! ### The toy over `ℤ_[p]` with `ϖ = p^t` (every `t : ℕ`, including `t = 0`) -/

namespace Zp

variable (p : ℕ) [Fact p.Prime] (t : ℕ)

/-- `ss:s06-ca` (`s06-ca`), toy over `ℤ_[p]`: `p^t ≠ 0` for every `t` (also `t = 0`). -/
theorem pow_ne_zero' : ((p : ℤ_[p]) ^ t) ≠ 0 :=
  pow_ne_zero t (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

/-- `ss:s06-ca` (`s06-ca`), toy over `ℤ_[p]`: `S = {(x, y) : x ≡ y mod p^t}` is Gorenstein. -/
theorem isGorenstein : IsGorenstein ℤ_[p] (toy ((p : ℤ_[p]) ^ t)) :=
  Toy.isGorenstein (pow_ne_zero' p t)

/-- `lem:s06-D` (`s06-D`), toy over `ℤ_[p]`: the `NewOldData` with the coordinate kernels. -/
noncomputable def data : NewOldData ℤ_[p] (toy ((p : ℤ_[p]) ^ t)) := Toy.data (pow_ne_zero' p t)

/-- `lem:s06-S` (`s06-S`), toy over `ℤ_[p]`: `η(S, pr₁) = (p^t)`. -/
theorem congruenceIdeal_fst :
    congruenceIdeal (fst ((p : ℤ_[p]) ^ t)) = Ideal.span {(p : ℤ_[p]) ^ t} :=
  Toy.congruenceIdeal_fst (pow_ne_zero' p t)

/-- `lem:s06-S` (`s06-S`), toy over `ℤ_[p]`, edge case `t = 0`: `S = ℤ_[p] × ℤ_[p]` and
`η(S, pr₁) = (1) = ⊤`. -/
theorem congruenceIdeal_fst_zero : congruenceIdeal (fst ((p : ℤ_[p]) ^ 0)) = ⊤ := by
  rw [congruenceIdeal_fst, pow_zero, Ideal.span_singleton_one]

/-- `lem:s06-D` (`s06-D`)(a), toy over `ℤ_[p]`: `Ann(ker pr₁) = ker pr₂`. -/
theorem ann_a : ann (RingHom.ker (fst ((p : ℤ_[p]) ^ t))) = RingHom.ker (snd ((p : ℤ_[p]) ^ t)) :=
  Toy.ann_a (pow_ne_zero' p t)

/-- `thm:s06-E` (`s06-E`)(ii)+(iii), toy over `ℤ_[p]`: `η(S, λ) = c_q · η(S', λ')`, i.e.
`(p^t) = (p^t) · (1)`. -/
theorem thmE :
    congruenceIdeal (ThmE.lam (data p t) (lam' (pow_ne_zero' p t))) =
      (data p t).𝔟.map (ThmE.lam (data p t) (lam' (pow_ne_zero' p t))) *
        congruenceIdeal (lam' (pow_ne_zero' p t)) ∧
    (data p t).𝔟.map (ThmE.lam (data p t) (lam' (pow_ne_zero' p t))) =
      Ideal.span {(p : ℤ_[p]) ^ t} :=
  ⟨Toy.thmE_iii (pow_ne_zero' p t), Toy.c_eq (pow_ne_zero' p t)⟩

/-- `thm:s06-E` (`s06-E`)(iii), DVR half, toy over `ℤ_[p]`: `η(S, λ) = c_q · η(S', λ')` via
`ThmE.eta_eq_c_mul_of_dvr` (`ℤ_[p]` is a DVR; (Gor_S) is `isGorenstein p t`; no hypothesis on
`S'`). -/
theorem thmE_dvr :
    congruenceIdeal (ThmE.lam (data p t) (lam' (pow_ne_zero' p t))) =
      (data p t).𝔟.map (ThmE.lam (data p t) (lam' (pow_ne_zero' p t))) *
        congruenceIdeal (lam' (pow_ne_zero' p t)) :=
  ThmE.eta_eq_c_mul_of_dvr (data p t) (isGorenstein p t) (lam' (pow_ne_zero' p t))

end Zp

end Toy

end Langlandscape.CommAlg
