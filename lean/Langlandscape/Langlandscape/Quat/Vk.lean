/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Local.GL2Levels
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The coefficient module `V_k` and the monoid `Σ_p` (S04-L15b, `eq:s01-Vk`)

`V_k` is the module of homogeneous polynomials `P(X, Y)` of degree `n = k - 2` over `R`, with the left action of
`g = (a b; c d)` given by `(g · P)(X, Y) = P((X, Y) g) = P(aX + cY, bX + dY)` (`eq:s01-Vk`).

* `Vk R k` : `homogeneousSubmodule (Fin 2) R (k - 2)`.
* `symAct R n : Matrix (Fin 2) (Fin 2) R →* Module.End R (homogeneousSubmodule (Fin 2) R n)` (`symAct_apply`),
  the action `P ↦ P((X,Y) A)`, a monoid homomorphism (`symSubst_mul`).
* `SigmaP p` : the submonoid `M₂(ℤ_p) ∩ GL₂(ℚ_p)` of `GL₂(ℚ_p)` (integral entries); `intMat`, `intMatHom`.
* `VkAct p k : SigmaP p →* Module.End ℤ_[p] (Vk ℤ_[p] k)`.
* `evV` : the evaluation `P ↦ P(0, 1)`; `evV_symAct : evV (A · P) = P(A₂₁, A₂₂)`; `evV_symAct_of_row`: it is
  invariant under every `A` with bottom row `(0, 1)` (e.g. `ϖ_j`), `evV_VkAct_of_row`.

Status: *formalized*.
-/

namespace Langlandscape.Quat

open MvPolynomial Langlandscape.Local

section Sym

variable (R : Type*) [CommRing R]

/-- `eq:s01-Vk` (`s01-Vk`): the substitution `(X, Y) ↦ (X, Y) A`, i.e. `X_i ↦ ∑_j A_{ji} X_j`. -/
noncomputable def matSubst (A : Matrix (Fin 2) (Fin 2) R) : Fin 2 → MvPolynomial (Fin 2) R :=
  fun i => ∑ j, C (A j i) * X j

/-- `eq:s01-Vk` (`s01-Vk`): the algebra map `P ↦ P((X, Y) A)` on `R[X, Y]`. -/
noncomputable def symSubst (A : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (matSubst R A)

variable {R}

/-- `eq:s01-Vk` (`s01-Vk`): the substitution for `A = 1` is the identity. -/
theorem matSubst_one : matSubst R (1 : Matrix (Fin 2) (Fin 2) R) = X := by
  funext i
  fin_cases i
  · show ∑ j, C ((1 : Matrix (Fin 2) (Fin 2) R) j 0) * X j = X 0
    simp [Fin.sum_univ_two]
  · show ∑ j, C ((1 : Matrix (Fin 2) (Fin 2) R) j 1) * X j = X 1
    simp [Fin.sum_univ_two]

/-- `eq:s01-Vk` (`s01-Vk`): `(X, Y)(A B)` is `(X, Y) A` substituted into `(X, Y) B`. -/
theorem matSubst_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    matSubst R (A * B) = fun i => bind₁ (matSubst R A) (matSubst R B i) := by
  funext i
  simp only [matSubst, map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, Fin.sum_univ_two,
    C_add, C_mul, map_add]
  ring

/-- `eq:s01-Vk` (`s01-Vk`): `1 ∈ M₂` acts as the identity. -/
theorem symSubst_one (P : MvPolynomial (Fin 2) R) : symSubst R 1 P = P := by
  rw [symSubst, matSubst_one, bind₁_X_left]
  rfl

/-- `eq:s01-Vk` (`s01-Vk`): it is a left action, `(A B) · P = A · (B · P)`. -/
theorem symSubst_mul (A B : Matrix (Fin 2) (Fin 2) R) (P : MvPolynomial (Fin 2) R) :
    symSubst R (A * B) P = symSubst R A (symSubst R B P) := by
  simp only [symSubst]
  rw [bind₁_bind₁, matSubst_mul]

/-- `eq:s01-Vk` (`s01-Vk`): the linear forms `(X, Y) A` are homogeneous of degree `1`. -/
theorem matSubst_isHomogeneous (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (matSubst R A i).IsHomogeneous 1 := by
  have h : matSubst R A i ∈ homogeneousSubmodule (Fin 2) R 1 :=
    Submodule.sum_mem _ fun j _ => (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C_mul_X _ _)
  exact (mem_homogeneousSubmodule _ _).1 h

/-- `eq:s01-Vk` (`s01-Vk`): `P ↦ P((X, Y) A)` preserves homogeneous polynomials of degree `n`. -/
theorem symSubst_mem (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) {P : MvPolynomial (Fin 2) R}
    (hP : P ∈ homogeneousSubmodule (Fin 2) R n) : symSubst R A P ∈ homogeneousSubmodule (Fin 2) R n := by
  have h := ((mem_homogeneousSubmodule _ _).1 hP).aeval (matSubst R A) (matSubst_isHomogeneous A)
  rw [one_mul] at h
  exact (mem_homogeneousSubmodule _ _).2 h

/-- `eq:s01-Vk` (`s01-Vk`): the action of `A ∈ M₂(R)` on the degree-`n` homogeneous polynomials. -/
noncomputable def symActLin (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    homogeneousSubmodule (Fin 2) R n →ₗ[R] homogeneousSubmodule (Fin 2) R n :=
  (symSubst R A).toLinearMap.restrict (fun _ hP => symSubst_mem n A hP)

/-- `eq:s01-Vk` (`s01-Vk`): `symActLin n A P = P((X, Y) A)` as a polynomial. -/
theorem symActLin_coe (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (P : homogeneousSubmodule (Fin 2) R n) :
    ((symActLin n A P : homogeneousSubmodule (Fin 2) R n) : MvPolynomial (Fin 2) R) =
      symSubst R A (P : MvPolynomial (Fin 2) R) :=
  rfl

variable (R) in
/-- `eq:s01-Vk` (`s01-Vk`): the monoid homomorphism `A ↦ (P ↦ P((X, Y) A))`, `M₂(R) →* End(R[X,Y]_n)`. -/
noncomputable def symAct (n : ℕ) :
    Matrix (Fin 2) (Fin 2) R →* Module.End R (homogeneousSubmodule (Fin 2) R n) where
  toFun := symActLin n
  map_one' := LinearMap.ext fun P => Subtype.ext (symSubst_one P.1)
  map_mul' A B := LinearMap.ext fun P => Subtype.ext (symSubst_mul A B P.1)

/-- `eq:s01-Vk` (`s01-Vk`): `symAct n A P = P((X, Y) A)`. -/
theorem symAct_coe (n : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (P : homogeneousSubmodule (Fin 2) R n) :
    ((symAct R n A P : homogeneousSubmodule (Fin 2) R n) : MvPolynomial (Fin 2) R) =
      symSubst R A (P : MvPolynomial (Fin 2) R) :=
  rfl

variable (R) in
/-- `eq:s01-Vk` (`s01-Vk`): `V_k`, the homogeneous polynomials of degree `k - 2` in `X, Y` over `R`. -/
abbrev Vk (k : ℕ) : Submodule R (MvPolynomial (Fin 2) R) := homogeneousSubmodule (Fin 2) R (k - 2)

variable (R) in
/-- `def:s04-Pk` (`s04-Pk`): the evaluation `ev : V_k → R`, `P ↦ P(0, 1)`. -/
noncomputable def evV (k : ℕ) : Vk R k →ₗ[R] R :=
  (MvPolynomial.aeval (R := R) (![0, 1] : Fin 2 → R)).toLinearMap ∘ₗ (Vk R k).subtype

/-- `def:s04-Pk` (`s04-Pk`): `ev P = P(0, 1)`. -/
theorem evV_apply (k : ℕ) (P : Vk R k) :
    evV R k P = MvPolynomial.aeval (![0, 1] : Fin 2 → R) (P : MvPolynomial (Fin 2) R) :=
  rfl

/-- `def:s04-Pk` (`s04-Pk`): `ev (A · P) = P(A₂₁, A₂₂)` (for `A = (a b; c d)`: `P(c, d)`). -/
theorem evV_symAct (k : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (P : Vk R k) :
    evV R k (symAct R (k - 2) A P) = MvPolynomial.aeval (fun i => A 1 i) (P : MvPolynomial (Fin 2) R) := by
  have h : (fun i => MvPolynomial.aeval (![0, 1] : Fin 2 → R) (matSubst R A i)) = fun i => A 1 i := by
    funext i
    simp [matSubst, Fin.sum_univ_two]
  rw [evV_apply, symAct_coe, symSubst, aeval_bind₁, h]

/-- `def:s04-Pk` (`s04-Pk`), `s04-ekills` step 1: `ev (A · P) = ev P` when the bottom row of `A` is `(0, 1)`,
e.g. for `A = ϖ_j = (p j; 0 1)` (`def:s01-NUp`: `ev(ϖ_j P) = P((0,1)ϖ_j) = P(0,1)`). -/
theorem evV_symAct_of_row (k : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (h0 : A 1 0 = 0) (h1 : A 1 1 = 1)
    (P : Vk R k) : evV R k (symAct R (k - 2) A P) = evV R k P := by
  have h : (fun i => A 1 i) = (![0, 1] : Fin 2 → R) := by
    funext i
    fin_cases i <;> simp [h0, h1]
  rw [evV_symAct, evV_apply, h]

end Sym

section SigmaP

variable (p : ℕ) [Fact p.Prime]

/-- `eq:s01-Vk` (`s01-Vk`): the monoid `Σ_p = M₂(ℤ_p) ∩ GL₂(ℚ_p)` inside `GL₂(ℚ_p)` (all entries integral). -/
def SigmaP : Submonoid (GL (Fin 2) ℚ_[p]) where
  carrier := {g | ∀ i j, ‖(Units.val g) i j‖ ≤ 1}
  one_mem' := fun i j => by fin_cases i <;> fin_cases j <;> simp
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_val_apply]
    exact norm_add_le_of_le (norm_mul_le_one (hg _ _) (hh _ _)) (norm_mul_le_one (hg _ _) (hh _ _))

variable {p}

/-- `eq:s01-Vk` (`s01-Vk`): `GL₂(ℤ_p) ⊆ Σ_p`. -/
theorem mem_SigmaP_of_mem_GL2Zl {g : GL (Fin 2) ℚ_[p]} (hg : g ∈ GL2Zl p) : g ∈ SigmaP p :=
  hg.1

/-- `eq:s01-Vk` (`s01-Vk`): the integral matrix `(a b; c d) ∈ M₂(ℤ_p)` of an element of `Σ_p`. -/
noncomputable def intMat (g : SigmaP p) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  Matrix.of fun i j => ⟨(Units.val (g : GL (Fin 2) ℚ_[p])) i j, (show _ ∈ PadicInt.subring p from g.2 i j)⟩

/-- `eq:s01-Vk` (`s01-Vk`): the entries of `intMat g` are those of `g`. -/
theorem intMat_map (g : SigmaP p) :
    (intMat g).map (PadicInt.Coe.ringHom (p := p)) = Units.val (g : GL (Fin 2) ℚ_[p]) := by
  ext i j
  rfl

/-- `eq:s01-Vk` (`s01-Vk`): `g ↦ (a b; c d) ∈ M₂(ℤ_p)` is a monoid homomorphism `Σ_p →* M₂(ℤ_p)`. -/
noncomputable def intMatHom : SigmaP p →* Matrix (Fin 2) (Fin 2) ℤ_[p] where
  toFun := intMat
  map_one' := by
    apply Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) (fun _ _ h => PadicInt.ext h)
    beta_reduce
    rw [intMat_map]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    apply Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) (fun _ _ h => PadicInt.ext h)
    beta_reduce
    rw [Matrix.map_mul, intMat_map, intMat_map, intMat_map]
    rfl

/-- `eq:s01-Vk` (`s01-Vk`): the action of `Σ_p = M₂(ℤ_p) ∩ GL₂(ℚ_p)` on `V_k` over `ℤ_p`,
`(g · P)(X, Y) = P((X, Y) g)`; a monoid homomorphism. -/
noncomputable def VkAct (k : ℕ) : SigmaP p →* Module.End ℤ_[p] (Vk ℤ_[p] k) :=
  (symAct ℤ_[p] (k - 2)).comp intMatHom

/-- `def:s04-Pk` (`s04-Pk`): `ev (g · P) = ev P` for `g ∈ Σ_p` with bottom row `(0, 1)` (e.g. `g = ϖ_j`). -/
theorem evV_VkAct_of_row (k : ℕ) (g : SigmaP p) (h0 : (Units.val (g : GL (Fin 2) ℚ_[p])) 1 0 = 0)
    (h1 : (Units.val (g : GL (Fin 2) ℚ_[p])) 1 1 = 1) (P : Vk ℤ_[p] k) :
    evV ℤ_[p] k (VkAct k g P) = evV ℤ_[p] k P :=
  evV_symAct_of_row k (intMat g) (PadicInt.ext (h0.trans PadicInt.coe_zero.symm))
    (PadicInt.ext (h1.trans PadicInt.coe_one.symm)) P

end SigmaP

end Langlandscape.Quat
