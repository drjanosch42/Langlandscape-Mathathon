/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.BaseChange
public import Langlandscape.Defect.Fixed
public import Langlandscape.Defect.Galois
public import Langlandscape.Hyp.FreeRankTwo
public import Langlandscape.Hyp.HidaControlGL2
public import Langlandscape.Hyp.KimOta
public import Langlandscape.Hyp.KimOtaRT
public import Langlandscape.Hyp.HsiehGor
public import Langlandscape.Hyp.HsiehGorFull
public import Langlandscape.Hyp.OldDecomp
public import Langlandscape.Hyp.ResidualBurnside
public import Langlandscape.Hyp.TamSpec
public import LanglandscapeTests.S06.Gorenstein
public import LanglandscapeTests.S06.Toy
public import Mathlib.LinearAlgebra.Matrix.Transvection
import Langlandscape.CommAlg.DVR

/-!
# Non-vacuity of the stage-06 hypotheses (S06-L10b)

`OVERVIEW §3.6`: every `Hyp.*` has a non-vacuity instance or a stated reason. One toy `Defect.Setting`
(`toySetting p t`) over `Λ = I = 𝒪 = ℤ_[p]`, `T = {(x, y) ∈ ℤ_[p]² : x ≡ y mod p^t}` (the L10a toy,
`CommAlg.Toy.toy`), `𝔞Λ = ker pr₁`, `𝔟Λ = ker pr₂`, `λ′ = CommAlg.Toy.lamFst`, `G = GL₂(ℤ_[p])`,
`ρ = id`, `I_q = {[[1, p^t x], [0, 1]] : x ∈ ℤ_[p]}` and `t = t`. All statements hold for every `t : ℕ`; the
meaningful case is `t ≥ 1` (then `𝔱_q = (p^t) ≠ ⊤` and `𝔪^t ≠ ⊤`, so the two coordinates are congruent
mod `p^t` but not equal), and `toy_all` is stated for `t = 1`.

Instantiated (no `False` premise, no trivial ring: `ℤ_[p]`, a DVR, `p` prime):
* `Hyp.OldDecomp (toySetting p t)` (`toy_oldDecomp`), by transport of `CommAlg.Toy.data` along
  `Algebra.TensorProduct.lid`;
* `Hyp.HsiehGorFull (toySetting p t)` (`toy_hsiehGorFull`), by `CommAlg.IsGorenstein.baseChange`;
* `Hyp.HsiehGor ℤ_[p] (T ⧸ 𝔞Λ) (T ⧸ 𝔞Λ)` (`toy_hsiehGor`; `T ⧸ ker pr₁ ≅ ℤ_[p]`) and
  `Hyp.HsiehGor ℤ_[p] ℤ_[p] ℤ_[p]` (`toy_hsiehGor_self`);
* `Hyp.TamSpec (toySetting p t)` (`toy_tamSpec`): `𝔱_q = (p^t)`, `P = id`, `𝔪 = (p)`;
* `Hyp.ResidualBurnside (toySetting p t)` (`toy_residualBurnside`): `ρ = id` on `GL₂(ℤ_[p])`, whose image
  spans `M₂(ℤ_[p])` (the unipotent group alone would span only upper-triangular matrices, which is why `G` is
  all of `GL₂`; `Iq` is only used by `TamSpec`).

Further instances (R1/R4 of the S06 Lean audit part 2; **consistency (non-vacuity) instances only, not evidence**:
they show that the hypotheses are jointly satisfiable on a non-degenerate example, not that they hold for any
arithmetic data; guards are not needed, the conclusions hold for every `p q M`):
* `Hyp.FreeRankTwo (toySetting p t)` (`toy_freeRankTwo`), from `Defect.freeRankTwo_of_le` and `𝔱_q = 𝔠_q = (p^t)`
  (`toy_tq`, `toy_cq`). Recall `Hyp.FreeRankTwo D ↔ 𝔱_q ≤ 𝔠_q`, so this is the toy fact `(p^t) ≤ (p^t)`;
* `Hyp.HidaControlGL2` (`toy_hidaControlGL2`): base change of `toy_oldDecomp` along `P = id`;
* `Hyp.KimOta` (`toy_kimOta`): `η(λ_f) = (p^t) · η(λ′_f)` with `η(λ′_f) = ⊤ ≠ ⊥` (`λ′_f` is an isomorphism);
* `Hyp.KimOtaRT` (`toy_kimOtaRT`): `𝔠_q(f) = (p^t) = 𝔪^t`.
Not instantiated as an end-to-end test: `Defect.defect_formula_of_le` on the toy (it is only an argument, by
inspection `𝔠_q = 𝔱_q = (p^t)`; not formalized for lack of time).
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace Langlandscape.S06Test

/-! ### Generic lemmas -/

section Generic

/-- `lem:s06-decomp` (`s06-decomp`), test lemma: transport of `NewOldData` along an `A`-algebra
isomorphism `e : R ≃ₐ[A] S`, with `𝔞 = e⁻¹(𝔞_S)`, `𝔟 = e⁻¹(𝔟_S)`; the conclusion is the conjunction of
`Hyp.OldDecomp` over `A = I` and `R`. -/
theorem oldDecomp_of_algEquiv {A R S : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [CommRing S] [Algebra A S] (e : R ≃ₐ[A] S) (𝔞 𝔟 : Ideal R) (d : CommAlg.NewOldData A S)
    (ha : 𝔞 = d.𝔞.comap (e : R →+* S)) (hb : 𝔟 = d.𝔟.comap (e : R →+* S))
    (hfree : Module.Free A (S ⧸ d.𝔟)) :
    Module.Free A R ∧ Module.Finite A R ∧ Module.IsTorsionFree A (R ⧸ 𝔞) ∧
      Module.IsTorsionFree A (R ⧸ 𝔟) ∧ 𝔞 ⊓ 𝔟 = ⊥ ∧
      (∃ c : A, c ≠ 0 ∧ algebraMap A R c ∈ 𝔞 ⊔ 𝔟) ∧ Module.Free A (R ⧸ 𝔟) := by
  subst ha
  subst hb
  have ha' : d.𝔞 = (d.𝔞.comap (e : R →+* S)).map (e : R →+* S) :=
    (Ideal.map_comap_of_surjective (f := (e : R →+* S)) (hf := e.surjective) _).symm
  have hb' : d.𝔟 = (d.𝔟.comap (e : R →+* S)).map (e : R →+* S) :=
    (Ideal.map_comap_of_surjective (f := (e : R →+* S)) (hf := e.surjective) _).symm
  let qa : (R ⧸ d.𝔞.comap (e : R →+* S)) ≃ₐ[A] (S ⧸ d.𝔞) :=
    Ideal.quotientEquivAlg (d.𝔞.comap (e : R →+* S)) d.𝔞 e ha'
  let qb : (R ⧸ d.𝔟.comap (e : R →+* S)) ≃ₐ[A] (S ⧸ d.𝔟) :=
    Ideal.quotientEquivAlg (d.𝔟.comap (e : R →+* S)) d.𝔟 e hb'
  have := d.free
  have := d.finite
  have := d.tf_a
  have := d.tf_b
  refine ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv,
    ?_, ?_, ?_, ?_, Module.Free.of_equiv qb.symm.toLinearEquiv⟩
  · exact Function.Injective.moduleIsTorsionFree qa.toLinearEquiv qa.toLinearEquiv.injective
      (fun r m => map_smul qa.toLinearEquiv r m)
  · exact Function.Injective.moduleIsTorsionFree qb.toLinearEquiv qb.toLinearEquiv.injective
      (fun r m => map_smul qb.toLinearEquiv r m)
  · rw [eq_bot_iff]
    intro x hx
    have h1 := (Ideal.mem_inf.1 hx).1
    have h2 := (Ideal.mem_inf.1 hx).2
    have h3 : e x ∈ d.𝔞 ⊓ d.𝔟 := Ideal.mem_inf.2 ⟨h1, h2⟩
    rw [d.inf_eq_bot] at h3
    have h4 : e x = e 0 := by rw [map_zero]; exact Ideal.mem_bot.1 h3
    exact Ideal.mem_bot.2 (e.injective h4)
  · obtain ⟨c, hc, hmem⟩ := d.split
    refine ⟨c, hc, ?_⟩
    have h1 : e (algebraMap A R c) ∈ Ideal.map (e : R →+* S)
        (d.𝔞.comap (e : R →+* S) ⊔ d.𝔟.comap (e : R →+* S)) := by
      rw [Ideal.map_sup_comap_of_surjective (f := (e : R →+* S)) (hf := e.surjective), e.commutes]
      exact hmem
    have h2 : algebraMap A R c ∈ Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S)
        (d.𝔞.comap (e : R →+* S) ⊔ d.𝔟.comap (e : R →+* S))) := h1
    rwa [Ideal.comap_map_of_bijective (f := (e : R →+* S)) (hf := e.bijective)] at h2

/-- `lem:s06-decomp` (`s06-decomp`), test lemma: for `Λ = I = A`, the extension of an ideal `J` of `T` along
`includeRight : T → A ⊗[A] T` is the preimage of `J` under `Algebra.TensorProduct.lid`. -/
theorem map_includeRight_eq_comap_lid {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]
    (J : Ideal T) :
    Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[A] A ⊗[A] T) J =
      Ideal.comap ((Algebra.TensorProduct.lid A T : A ⊗[A] T ≃ₐ[A] T) : A ⊗[A] T →+* T) J := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show Algebra.TensorProduct.lid A T (Algebra.TensorProduct.includeRight x) ∈ J
    simpa using hx
  · intro x hx
    have hx' : x = Algebra.TensorProduct.includeRight (Algebra.TensorProduct.lid A T x) := by
      have h := (Algebra.TensorProduct.lid A T).symm_apply_apply x
      rw [Algebra.TensorProduct.lid_symm_apply] at h
      exact h.symm
    have h := Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight : T →ₐ[A] A ⊗[A] T)
      (show Algebra.TensorProduct.lid A T x ∈ J from hx)
    rwa [← hx'] at h

/-- `lem:s06-burnside` (`s06-burnside`), test lemma: `transvection i j c` as a unit of `M₂(A)` (`i ≠ j`). -/
def tvUnit {A : Type*} [CommRing A] {i j : Fin 2} (h : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup (Fin 2) A where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same i j h, neg_add_cancel, Matrix.transvection_zero]

/-- `lem:s06-burnside` (`s06-burnside`), test lemma: the underlying matrix of `tvUnit`. -/
@[simp]
theorem tvUnit_val {A : Type*} [CommRing A] {i j : Fin 2} (h : i ≠ j) (c : A) :
    ((tvUnit h c : Matrix.GeneralLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.transvection i j c := rfl

/-- `lem:s06-burnside` (`s06-burnside`), test lemma: `transvection i j c - 1 = single i j c`. -/
theorem tv_sub_one {A : Type*} [CommRing A] (i j : Fin 2) (c : A) :
    Matrix.transvection i j c - 1 = Matrix.single i j c := by
  show 1 + Matrix.single i j c - 1 = _
  exact add_sub_cancel_left _ _

/-- `lem:s06-burnside` (`s06-burnside`), test lemma: a subalgebra of `M₂(A)` containing all units is
everything (the units contain the two transvections `1 + E₀₁`, `1 + E₁₀`, hence all `E_{ij}`). -/
theorem mem_of_units {A : Type*} [CommRing A] (S : Subalgebra A (Matrix (Fin 2) (Fin 2) A))
    (hunit : ∀ g : (Matrix (Fin 2) (Fin 2) A)ˣ, (g : Matrix (Fin 2) (Fin 2) A) ∈ S)
    (M : Matrix (Fin 2) (Fin 2) A) : M ∈ S := by
  have h01 : ∀ c : A, Matrix.single (0 : Fin 2) (1 : Fin 2) c ∈ S := fun c => by
    rw [← tv_sub_one]
    exact sub_mem (hunit (tvUnit (by decide : (0 : Fin 2) ≠ 1) c)) (one_mem _)
  have h10 : ∀ c : A, Matrix.single (1 : Fin 2) (0 : Fin 2) c ∈ S := fun c => by
    rw [← tv_sub_one]
    exact sub_mem (hunit (tvUnit (by decide : (1 : Fin 2) ≠ 0) c)) (one_mem _)
  have h00 : ∀ c : A, Matrix.single (0 : Fin 2) (0 : Fin 2) c ∈ S := fun c => by
    have h := mul_mem (h01 c) (h10 1)
    rwa [Matrix.single_mul_single_same, mul_one] at h
  have h11 : ∀ c : A, Matrix.single (1 : Fin 2) (1 : Fin 2) c ∈ S := fun c => by
    have h := mul_mem (h10 c) (h01 1)
    rwa [Matrix.single_mul_single_same, mul_one] at h
  rw [Matrix.matrix_eq_sum_single M]
  simp only [Fin.sum_univ_two]
  exact add_mem (add_mem (h00 _) (h01 _)) (add_mem (h10 _) (h11 _))

/-- `lem:s06-burnside` (`s06-burnside`), test lemma: an algebra map `A[GL₂(A)] → M₂(A)` that sends
`single g 1` to the matrix `g` is surjective. -/
theorem surjective_of_units {A : Type*} [CommRing A]
    (φ : MonoidAlgebra A (Matrix.GeneralLinearGroup (Fin 2) A) →ₐ[A] Matrix (Fin 2) (Fin 2) A)
    (h : ∀ g : Matrix.GeneralLinearGroup (Fin 2) A,
      φ (MonoidAlgebra.single g 1) = (g : Matrix (Fin 2) (Fin 2) A)) :
    Function.Surjective φ := fun M =>
  (AlgHom.mem_range φ).1 (mem_of_units φ.range (fun g => ⟨MonoidAlgebra.single g 1, h g⟩) M)

end Generic

/-! ### The toy setting -/

section Toy

variable (p : ℕ) [Fact p.Prime] (t : ℕ)

/-- `ss:s06-ca` (`s06-ca`), test: the uniformiser power `p^t ∈ ℤ_[p]` of the toy. -/
noncomputable abbrev toyW : ℤ_[p] := (p : ℤ_[p]) ^ t

/-- `lem:s06-tam` (`s06-tam`), test: the unipotent group `x ↦ [[1, p^t x], [0, 1]]`, `ℤ_[p] → GL₂(ℤ_[p])`. -/
noncomputable def unip : Multiplicative ℤ_[p] →* Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] where
  toFun x := tvUnit (by decide : (0 : Fin 2) ≠ 1) (toyW p t * Multiplicative.toAdd x)
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    simp [mul_add, Matrix.transvection_mul_transvection_same (0 : Fin 2) 1 (by decide)]

/-- `lem:s06-tam` (`s06-tam`), test: `unip x - 1 = p^t x · E₀₁`. -/
theorem unip_sub_one (x : Multiplicative ℤ_[p]) :
    ((unip p t x : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) ℤ_[p]) - 1 =
      Matrix.single (0 : Fin 2) (1 : Fin 2) (toyW p t * Multiplicative.toAdd x) :=
  tv_sub_one 0 1 (toyW p t * Multiplicative.toAdd x)

/-- `def:s06-rings` (`s06-rings`), `lem:s06-tam`, test: the toy `Defect.Setting` over `ℤ_[p]`:
`Λ = I = 𝒪 = ℤ_[p]`, `T = {(x, y) : x ≡ y mod p^t}`, `𝔞Λ = ker pr₁`, `𝔟Λ = ker pr₂`, `λ′ = pr₁`,
`G = GL₂(ℤ_[p])`, `ρ = id`, `I_q = unip(ℤ_[p])`, Tamagawa exponent `t`. -/
noncomputable def toySetting :
    Defect.Setting ℤ_[p] ℤ_[p] (CommAlg.Toy.toy (toyW p t)) ℤ_[p]
      (Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]) where
  𝔞Λ := RingHom.ker (CommAlg.Toy.fst (toyW p t))
  𝔟Λ := RingHom.ker (CommAlg.Toy.snd (toyW p t))
  lamΛ' := CommAlg.Toy.lamFst (toyW p t)
  Iq := (unip p t).range
  ρ := MonoidHom.id _
  P_local := ⟨fun a ha => by simpa using ha⟩
  t := t

/-- `lem:s06-tam` (`s06-tam`), test: membership in the toy inertia group. -/
theorem mem_Iq {σ : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]} :
    σ ∈ (toySetting p t).Iq ↔ ∃ x, unip p t x = σ :=
  MonoidHom.mem_range

/-! ### `OldDecomp`, `HsiehGorFull`, `HsiehGor` -/

/-- `lem:s06-decomp` (`s06-decomp`), non-vacuity of `Hyp.OldDecomp` on the toy setting (`ℤ_[p]`, any
`t`; `t ≥ 1` is the congruent, non-split case): `R = ℤ_[p] ⊗ T ≅ T`, `𝔞 = ker pr₁`, `𝔟 = ker pr₂`. -/
theorem toy_oldDecomp : Hyp.OldDecomp (toySetting p t) := by
  have hw := CommAlg.Toy.Zp.pow_ne_zero' p t
  exact oldDecomp_of_algEquiv (Algebra.TensorProduct.lid ℤ_[p] (CommAlg.Toy.toy (toyW p t)))
    (toySetting p t).𝔞 (toySetting p t).𝔟 (CommAlg.Toy.data hw)
    (map_includeRight_eq_comap_lid (RingHom.ker (CommAlg.Toy.fst (toyW p t))))
    (map_includeRight_eq_comap_lid (RingHom.ker (CommAlg.Toy.snd (toyW p t))))
    (CommAlg.Toy.free_quot_b hw)

/-- `thm:s06-defect` (`s06-defect`) step (1), non-vacuity of `Hyp.HsiehGorFull` on the toy setting:
`ℤ_[p] ⊗_{ℤ_[p]} T` is `ℤ_[p]`-Gorenstein, by base change of `CommAlg.Toy.Zp.isGorenstein`. -/
theorem toy_hsiehGorFull : Hyp.HsiehGorFull (toySetting p t) :=
  CommAlg.IsGorenstein.baseChange ℤ_[p] (CommAlg.Toy.Zp.isGorenstein p t)

/-- `thm:s04-Gor` (`s04-Gor`), non-vacuity of `Hyp.HsiehGor` with `TB = T ⧸ ker pr₁` (the toy's `q`-new
quotient, `≅ ℤ_[p]`) and `M = TB`: Gorenstein by transport from `ℤ_[p]` along `λ′`, `M ≅ TB` by `refl`. -/
theorem toy_hsiehGor :
    Hyp.HsiehGor ℤ_[p] (CommAlg.Toy.toy (toyW p t) ⧸ RingHom.ker (CommAlg.Toy.fst (toyW p t)))
      (CommAlg.Toy.toy (toyW p t) ⧸ RingHom.ker (CommAlg.Toy.fst (toyW p t))) :=
  ⟨CommAlg.IsGorenstein.of_algEquiv (CommAlg.isGorenstein_self ℤ_[p])
      (AlgEquiv.ofBijective (CommAlg.Toy.lamFst (toyW p t))
        ⟨CommAlg.Toy.lamFst_injective (ϖ := toyW p t),
          CommAlg.Toy.lamFst_surjective (ϖ := toyW p t)⟩).symm,
    ⟨LinearEquiv.refl _ _⟩⟩

end Toy

/-- `thm:s04-Gor` (`s04-Gor`), non-vacuity of `Hyp.HsiehGor`, plain form: `ℤ_[p]` over itself with
`M = ℤ_[p]`. -/
theorem toy_hsiehGor_self (p : ℕ) [Fact p.Prime] : Hyp.HsiehGor ℤ_[p] ℤ_[p] ℤ_[p] :=
  ⟨CommAlg.isGorenstein_self ℤ_[p], ⟨LinearEquiv.refl _ _⟩⟩

section Toy2

variable (p : ℕ) [Fact p.Prime] (t : ℕ)

/-! ### `TamSpec` -/

/-- `lem:s06-tam` (`s06-tam`), test: every entry of `unip x - 1` lies in `(p^t)`. -/
theorem entry_mem (x : Multiplicative ℤ_[p]) (i j : Fin 2) :
    (((unip p t x : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) ℤ_[p]) - 1) i j ∈
      Ideal.span {toyW p t} := by
  rw [unip_sub_one]
  by_cases h : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · have hh : ¬ ((0 : Fin 2) = i ∧ (1 : Fin 2) = j) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hh]
    exact Ideal.zero_mem _

/-- `lem:s06-tam` (`s06-tam`), test: the `(0, 1)` entry of `unip 1 - 1` is `p^t`. -/
theorem unip_entry :
    (((unip p t (Multiplicative.ofAdd 1) : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]) :
      Matrix (Fin 2) (Fin 2) ℤ_[p]) - 1) 0 1 = toyW p t := by
  rw [unip_sub_one, Matrix.single_apply_same, toAdd_ofAdd, mul_one]

/-- `def:s06-tam` (`s06-tam`), test: `𝔱_q = (p^t)` for the toy setting. -/
theorem toy_tq : (toySetting p t).tq = Ideal.span {toyW p t} := by
  unfold Defect.Setting.tq
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro _ ⟨σ, hσ, i, j, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_Iq p t).1 hσ
    exact entry_mem p t x i j
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span ⟨unip p t (Multiplicative.ofAdd 1),
      (mem_Iq p t).2 ⟨_, rfl⟩, 0, 1, unip_entry p t⟩

/-- `lem:s06-tam` (`s06-tam`)(a)–(c), non-vacuity of `Hyp.TamSpec` on the toy setting: unipotent inertia,
`𝔱_q = (p^t)` generated by the entries of one `ρ(τ) - 1`, `P(𝔱_q) = (p)^t = 𝔪^t` (`P = id`, `𝔪 = (p)`), and
`𝔪^t ≠ 0`. For `t ≥ 1` the ideal `𝔱_q` is proper, so the instance is not the trivial `tq = ⊤`
case. -/
theorem toy_tamSpec : Hyp.TamSpec (toySetting p t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨x, rfl⟩ := (mem_Iq p t).1 hσ
    show (((unip p t x : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p]) :
      Matrix (Fin 2) (Fin 2) ℤ_[p]) - 1) ^ 2 = 0
    rw [pow_two, unip_sub_one]
    simp
  · refine ⟨unip p t (Multiplicative.ofAdd 1), (mem_Iq p t).2 ⟨_, rfl⟩, ?_⟩
    rw [toy_tq]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨((0 : Fin 2), (1 : Fin 2)), unip_entry p t⟩
    · apply Ideal.span_le.2
      rintro _ ⟨ij, rfl⟩
      exact entry_mem p t _ ij.1 ij.2
  · show Ideal.map (algebraMap ℤ_[p] ℤ_[p]) (toySetting p t).tq =
      IsLocalRing.maximalIdeal ℤ_[p] ^ t
    rw [toy_tq, Algebra.algebraMap_self, Ideal.map_id, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
  · show IsLocalRing.maximalIdeal ℤ_[p] ^ t ≠ ⊥
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    intro h
    exact CommAlg.Toy.Zp.pow_ne_zero' p t (Ideal.span_singleton_eq_bot.1 h)

/-! ### `ResidualBurnside` -/

/-- `lem:s06-burnside` (`s06-burnside`), non-vacuity of `Hyp.ResidualBurnside` on the toy setting:
`ρ = id : GL₂(ℤ_[p]) → GL₂(ℤ_[p])`, so `ℤ_[p][GL₂(ℤ_[p])] → M₂(ℤ_[p])` is onto (the image of `GL₂` contains the
transvections, hence all matrix units). -/
theorem toy_residualBurnside : Hyp.ResidualBurnside (toySetting p t) := by
  unfold Hyp.ResidualBurnside
  exact surjective_of_units _ (fun g => by simp [toySetting])

/-- `thm:s06-defect` (`s06-defect`), non-vacuity of the four instantiated stage-06 hypotheses at once, for
`t = 1` (the congruent, non-split case): `OldDecomp`, `HsiehGorFull`, `TamSpec`, `ResidualBurnside` on
`toySetting p 1`. -/
theorem toy_all :
    Hyp.OldDecomp (toySetting p 1) ∧ Hyp.HsiehGorFull (toySetting p 1) ∧
      Hyp.TamSpec (toySetting p 1) ∧ Hyp.ResidualBurnside (toySetting p 1) :=
  ⟨toy_oldDecomp p 1, toy_hsiehGorFull p 1, toy_tamSpec p 1, toy_residualBurnside p 1⟩

/-! ### `FreeRankTwo`, `HidaControlGL2`, `KimOta`, `KimOtaRT` (consistency instances only, not evidence) -/

/-- `lem:s06-S` (`s06-S`), test lemma: `λ (1 ⊗ b) = λ′_F (b mod 𝔞Λ)`, on any `Defect.Setting`. -/
theorem lam_includeRight {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I]
    [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [Algebra I 𝒪] [Group G] (D : Defect.Setting Λ I T 𝒪 G) (b : T) :
    D.lam (Algebra.TensorProduct.includeRight b) = D.lamΛ' (Ideal.Quotient.mk D.𝔞Λ b) := by
  have key : D.quotient_baseChange (Ideal.Quotient.mk D.𝔞 (Algebra.TensorProduct.includeRight b)) =
      (1 : I) ⊗ₜ[Λ] Ideal.Quotient.mk D.𝔞Λ b :=
    Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul (R := Λ) I T I D.𝔞Λ (1 : I) b
  show AlgHom.liftEquiv Λ I (T ⧸ D.𝔞Λ) I D.lamΛ'
    (D.quotient_baseChange (Ideal.Quotient.mk D.𝔞 (Algebra.TensorProduct.includeRight b))) = _
  rw [key, AlgHom.liftEquiv_tmul, one_smul]

/-- `lem:s06-S` (`s06-S`), test lemma: for `φ : S →ₐ[A] A` injective, the lift `A ⊗[A] S → A` is injective. -/
theorem liftEquiv_injective_self {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] (φ : S →ₐ[A] A)
    (hφ : Function.Injective φ) : Function.Injective (AlgHom.liftEquiv A A S A φ) := by
  have key : ∀ w : A ⊗[A] S,
      AlgHom.liftEquiv A A S A φ w = φ (Algebra.TensorProduct.lid A S w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a s =>
      simp [AlgHom.liftEquiv_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
  intro u v huv
  rw [key, key] at huv
  exact (Algebra.TensorProduct.lid A S).injective (hφ huv)

/-- `def:s06-ctam` (`s06-ctam`), test: `𝔠_q = (p^t)` for the toy setting (`𝔟 = ker pr₂`, `λ = pr₁`). -/
theorem toy_cq : (toySetting p t).cq = Ideal.span {toyW p t} := by
  apply le_antisymm
  · rw [Defect.Setting.cq, Ideal.map_le_iff_le_comap, Defect.Setting.𝔟, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, lam_includeRight]
    show CommAlg.Toy.lamFst (toyW p t) (Ideal.Quotient.mk (RingHom.ker (CommAlg.Toy.fst (toyW p t))) b) ∈ _
    rw [CommAlg.Toy.lamFst_mk, Ideal.mem_span_singleton, CommAlg.Toy.fst_apply]
    have hb2 : (b : ℤ_[p] × ℤ_[p]).2 = 0 := (RingHom.mem_ker (f := CommAlg.Toy.snd (toyW p t))).1 hb
    have hdvd := (CommAlg.Toy.mem_toy (toyW p t)).1 b.2
    rw [hb2, sub_zero] at hdvd
    exact hdvd
  · rw [Ideal.span_singleton_le_iff_mem]
    have hX : CommAlg.Toy.X (toyW p t) ∈ (toySetting p t).𝔟Λ :=
      (RingHom.mem_ker (f := CommAlg.Toy.snd (toyW p t))).2 rfl
    have hm := Ideal.mem_map_of_mem (toySetting p t).lam
      (Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight :
        CommAlg.Toy.toy (toyW p t) →ₐ[ℤ_[p]] ℤ_[p] ⊗[ℤ_[p]] CommAlg.Toy.toy (toyW p t)) hX)
    rw [lam_includeRight] at hm
    have e : (toySetting p t).lamΛ' (Ideal.Quotient.mk (toySetting p t).𝔞Λ
        (CommAlg.Toy.X (toyW p t))) = toyW p t :=
      (CommAlg.Toy.lamFst_mk (ϖ := toyW p t) (CommAlg.Toy.X (toyW p t))).trans rfl
    rw [e] at hm
    exact hm

/-- `prop:s06-galois` (`s06-galois`), **consistency (non-vacuity) instance only, not evidence**: `Hyp.FreeRankTwo`
holds on the toy setting, from `Defect.freeRankTwo_of_le` (which shows `Hyp.FreeRankTwo D ↔ 𝔱_q ≤ 𝔠_q` on the abstract
data) and `𝔱_q = 𝔠_q = (p^t)`. -/
theorem toy_freeRankTwo : Hyp.FreeRankTwo (toySetting p t) :=
  Defect.freeRankTwo_of_le _ ((toy_tq p t).le.trans (toy_cq p t).ge)

/-- `lem:s06-control` (`s06-control`), **consistency (non-vacuity) instance only, not evidence**: `Hyp.HidaControlGL2`
holds on the toy setting for every guard `p q M` (the conclusion is the base change of `toy_oldDecomp` along `P = id`,
`ℤ_[p] ⊗ (ℤ_[p] ⊗ T) ≅ T`). -/
theorem toy_hidaControlGL2 (pg q M : ℕ) : Hyp.HidaControlGL2 (toySetting p t) pg q M := by
  intro _
  have hw := CommAlg.Toy.Zp.pow_ne_zero' p t
  let e : (toySetting p t).Rk ≃ₐ[ℤ_[p]] CommAlg.Toy.toy (toyW p t) :=
    (Algebra.TensorProduct.lid ℤ_[p] (toySetting p t).R).trans
      (Algebra.TensorProduct.lid ℤ_[p] (CommAlg.Toy.toy (toyW p t)))
  have hA : (toySetting p t).𝔞 =
      Ideal.comap ((Algebra.TensorProduct.lid ℤ_[p] (CommAlg.Toy.toy (toyW p t)) :
        ℤ_[p] ⊗[ℤ_[p]] CommAlg.Toy.toy (toyW p t) ≃ₐ[ℤ_[p]] CommAlg.Toy.toy (toyW p t)) :
          ℤ_[p] ⊗[ℤ_[p]] CommAlg.Toy.toy (toyW p t) →+* CommAlg.Toy.toy (toyW p t))
        (RingHom.ker (CommAlg.Toy.fst (toyW p t))) :=
    map_includeRight_eq_comap_lid (RingHom.ker (CommAlg.Toy.fst (toyW p t)))
  have hB : (toySetting p t).𝔟 =
      Ideal.comap ((Algebra.TensorProduct.lid ℤ_[p] (CommAlg.Toy.toy (toyW p t)) :
        ℤ_[p] ⊗[ℤ_[p]] CommAlg.Toy.toy (toyW p t) ≃ₐ[ℤ_[p]] CommAlg.Toy.toy (toyW p t)) :
          ℤ_[p] ⊗[ℤ_[p]] CommAlg.Toy.toy (toyW p t) →+* CommAlg.Toy.toy (toyW p t))
        (RingHom.ker (CommAlg.Toy.snd (toyW p t))) :=
    map_includeRight_eq_comap_lid (RingHom.ker (CommAlg.Toy.snd (toyW p t)))
  have hAk : (toySetting p t).𝔞k = Ideal.comap (e : (toySetting p t).Rk →+* CommAlg.Toy.toy (toyW p t))
      (CommAlg.Toy.data hw).𝔞 := by
    have h1 : (toySetting p t).𝔞k = Ideal.comap
        ((Algebra.TensorProduct.lid ℤ_[p] (toySetting p t).R : _ ≃ₐ[ℤ_[p]] _) : _ →+* _)
        (toySetting p t).𝔞 := map_includeRight_eq_comap_lid (toySetting p t).𝔞
    rw [h1, hA]
    exact Ideal.ext fun x => Iff.rfl
  have hBk : (toySetting p t).𝔟k = Ideal.comap (e : (toySetting p t).Rk →+* CommAlg.Toy.toy (toyW p t))
      (CommAlg.Toy.data hw).𝔟 := by
    have h1 : (toySetting p t).𝔟k = Ideal.comap
        ((Algebra.TensorProduct.lid ℤ_[p] (toySetting p t).R : _ ≃ₐ[ℤ_[p]] _) : _ →+* _)
        (toySetting p t).𝔟 := map_includeRight_eq_comap_lid (toySetting p t).𝔟
    rw [h1, hB]
    exact Ideal.ext fun x => Iff.rfl
  exact oldDecomp_of_algEquiv e (toySetting p t).𝔞k (toySetting p t).𝔟k (CommAlg.Toy.data hw) hAk hBk
    (CommAlg.Toy.free_quot_b hw)

/-- `cor:s06-fixed` (`s06-fixed`), test: `𝔠_q(f) = 𝔪^t` for the toy setting (`P = id`, `𝔪 = (p)`). -/
theorem toy_cqk : (toySetting p t).cqk = IsLocalRing.maximalIdeal ℤ_[p] ^ t := by
  rw [← Defect.Setting.map_cq, toy_cq]
  show Ideal.map (algebraMap ℤ_[p] ℤ_[p]) (Ideal.span {toyW p t}) = _
  rw [Algebra.algebraMap_self, Ideal.map_id, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]

/-- `thm:s06-KO` (`s06-KO`), **consistency (non-vacuity) instance only, not evidence**: `Hyp.KimOtaRT` holds on the toy
setting for every guard `p q M`: `𝔠_q(f) = (p^t) = 𝔪^t`. -/
theorem toy_kimOtaRT (pg q M : ℕ) : Hyp.KimOtaRT (toySetting p t) pg q M :=
  fun _ => (toy_cqk p t).le

/-- `thm:s06-KO` (`s06-KO`), test: `λ′` of the toy setting is injective. -/
theorem toy_lam'_injective : Function.Injective (toySetting p t).lam' := by
  have h1 : Function.Injective (AlgHom.liftEquiv ℤ_[p] ℤ_[p]
      (CommAlg.Toy.toy (toyW p t) ⧸ (toySetting p t).𝔞Λ) ℤ_[p] (toySetting p t).lamΛ') :=
    liftEquiv_injective_self _ (CommAlg.Toy.lamFst_injective (ϖ := toyW p t))
  exact h1.comp (toySetting p t).quotient_baseChange.injective

/-- `thm:s06-KO` (`s06-KO`), test: `λ′_f` of the toy setting is injective (an isomorphism). -/
theorem toy_lam'k_injective : Function.Injective (toySetting p t).lam'k := by
  have hid : Function.Injective (Algebra.ofId ℤ_[p] ℤ_[p]) := fun a b h => by simpa using h
  have h1 : Function.Injective (AlgHom.liftEquiv ℤ_[p] ℤ_[p]
      ((toySetting p t).R ⧸ (toySetting p t).𝔞) ℤ_[p]
      ((Algebra.ofId ℤ_[p] ℤ_[p]).comp (toySetting p t).lam')) :=
    liftEquiv_injective_self _ (hid.comp (toy_lam'_injective p t))
  exact h1.comp (Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ_[p]) ℤ_[p]
    (toySetting p t).R ℤ_[p] (toySetting p t).𝔞).symm.injective

/-- `lem:s06-S` (`s06-S`), test: `η(R_k ⧸ 𝔞_k, λ′_f) = (1)` on the toy setting. -/
theorem toy_congruenceIdeal_lam'k :
    CommAlg.congruenceIdeal (A := ℤ_[p]) (S := (toySetting p t).Rk ⧸ (toySetting p t).𝔞k)
      (toySetting p t).lam'k = ⊤ := by
  have hker : RingHom.ker (toySetting p t).lam'k = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (toy_lam'k_injective p t)
  have hann : CommAlg.ann (S := (toySetting p t).Rk ⧸ (toySetting p t).𝔞k) ⊥ = ⊤ := by
    ext x
    refine ⟨fun _ => Submodule.mem_top, fun _ => CommAlg.mem_ann.2 fun y hy => ?_⟩
    obtain rfl := Ideal.mem_bot.1 hy
    exact mul_zero x
  unfold CommAlg.congruenceIdeal
  rw [hker, hann]
  exact Ideal.map_top _

/-- `thm:s06-KO` (`s06-KO`), **consistency (non-vacuity) instance only, not evidence**: `Hyp.KimOta` holds on the toy
setting for every guard `p q M`: `η(λ_f) = (p^t) · η(λ′_f)` (by `ThmE.eta_eq_c_mul_of_dvr`, `toy_hidaControlGL2` and
`toy_cqk`) and `η(λ′_f) = ⊤ ≠ ⊥`. -/
theorem toy_kimOta (pg q M : ℕ) : Hyp.KimOta (toySetting p t) pg q M := by
  intro h0 _
  have hG : CommAlg.IsGorenstein ℤ_[p] (toySetting p t).R := toy_hsiehGorFull p t
  have hE : CommAlg.congruenceIdeal (toySetting p t).lamk = (toySetting p t).cqk *
      CommAlg.congruenceIdeal (A := ℤ_[p]) (S := (toySetting p t).Rk ⧸ (toySetting p t).𝔞k)
        (toySetting p t).lam'k :=
    CommAlg.ThmE.eta_eq_c_mul_of_dvr ((toySetting p t).newOldAt h0 (toy_hidaControlGL2 p t pg q M))
      (CommAlg.IsGorenstein.baseChange ℤ_[p] hG) (toySetting p t).lam'k
  refine ⟨?_, ?_⟩
  · rw [hE, toy_cqk]
    rfl
  · rw [toy_congruenceIdeal_lam'k]
    exact top_ne_bot

end Toy2

end Langlandscape.S06Test
