/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.SubQuot

/-!
# Tests for `Langlandscape.CommAlg.SubQuot` (S05-L6)

Shape tests for `subquot_kernel`, `subquot_coker`, `subquot_coker_subsingleton`.
-/

@[expose] public section

namespace Langlandscape.CommAlg.Tests

open scoped TensorProduct
open Submodule

section Headline

variable {A T : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Free A T] [Module.Finite A T]
  {𝔞 𝔟 : Ideal T}
  {H : Type*} [AddCommGroup H] [Module T H] [Module.Free T H] [Module.Finite T H] {r : ℕ}

/-- `prop:s05-subquot` (`s05-subquot`), test: the kernel statement `H[𝔞] = 𝔟 • H`, `H[𝔞] ≃ (Fin r → 𝔟)`. -/
theorem test_subquot_kernel (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    torsionBySet T H 𝔞 = 𝔟 • (⊤ : Submodule T H) ∧
      Nonempty (torsionBySet T H 𝔞 ≃ₗ[T] (Fin r → 𝔟)) :=
  subquot_kernel htf_a htf_b hinf hsplit hr

/-- `prop:s05-subquot` (`s05-subquot`), test: first half of the kernel statement. -/
theorem test_subquot_kernel_eq (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    torsionBySet T H 𝔞 = 𝔟 • (⊤ : Submodule T H) :=
  (subquot_kernel htf_a htf_b hinf hsplit hr).1

/-- `prop:s05-subquot` (`s05-subquot`), test: the cokernel statement. -/
theorem test_subquot_coker (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (hr : Module.finrank T H = r) :
    Nonempty (((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) ≃ₗ[T]
      (Fin r → T ⧸ (𝔞 ⊔ 𝔟))) :=
  subquot_coker htf_a htf_b hinf hsplit hr

/-- `prop:s05-subquot` (`s05-subquot`), test: the cokernel vanishes when `𝔞 ⊔ 𝔟 = ⊤`. -/
theorem test_subquot_coker_subsingleton (htf_a : Module.IsTorsionFree A (T ⧸ 𝔞))
    (htf_b : Module.IsTorsionFree A (T ⧸ 𝔟)) (hinf : 𝔞 ⊓ 𝔟 = ⊥)
    (hsplit : (𝔞 ⊔ 𝔟).map
      (Algebra.TensorProduct.includeRight : T →ₐ[A] FractionRing A ⊗[A] T) = ⊤)
    (htop : 𝔞 ⊔ 𝔟 = ⊤) :
    Subsingleton ((H ⧸ 𝔞 • (⊤ : Submodule T H)) ⧸ LinearMap.range (subquotMap 𝔞 H)) :=
  subquot_coker_subsingleton htf_a htf_b hinf hsplit htop

end Headline

end Langlandscape.CommAlg.Tests
