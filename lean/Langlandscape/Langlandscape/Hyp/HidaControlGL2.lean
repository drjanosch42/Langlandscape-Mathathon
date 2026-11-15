/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.CommAlg.Gorenstein
public import Langlandscape.Defect.Setting

/-!
# Hypothesis `HidaControlGL2`: control at `P` and the weight-`k` new/old data (S06-L8a)

`mathematics/chapters/s06/s06-m3.tex`, `lem:s06-control` (step (3) of `thm:s06-defect`, as an equality) with
`lem:s06-pstab` and (P2), combined with `lem:s06-decomp` at weight `k`: `𝒪̃_P ⊗_{I_F} R = 𝐓_k(N)_𝔪 ⊗_𝒪 𝒪̃_P`, and under
this identification the base changes `𝔞_k`, `𝔟_k` of `𝔞`, `𝔟` are the kernels of the weight-`k` `q`-new and `q`-old
quotients. The Lean content is the weight-`k` new/old data (the `NewOldData` fields for `D.𝔞k`, `D.𝔟k` in
`𝒪 ⊗[I] D.R`, plus `𝒪`-freeness of `R_k ⧸ 𝔟_k`): base change along `P` does **not** preserve `𝔞 ∩ 𝔟 = 0` or the
splitting, so this is genuine input (launch note A4.4). The identification with `𝐓_k(N)_𝔪` itself is not representable on
abstract data (docstring only). Name chosen to avoid stage 04's `Hyp.HidaControl` (definite side, mod `p^s`).

Status: *cited* (Hida control), not discharged. Owner: S06-L8a. Consumers: `Setting.newOldAt`, `Defect.cor_fixed`,
`Defect.cor_allweights` (S06-L9b).
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape

open scoped TensorProduct

variable {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I]
  [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G]

namespace Hyp

/-- `lem:s06-control` (`s06-control`), step (3) of `thm:s06-defect`, with `lem:s06-pstab`, (P2) and `lem:s06-decomp` at
weight `k`: under (H0) (guard, explicit), `R_k = 𝒪 ⊗[I] R` (`= 𝐓_k(N)_𝔪 ⊗ 𝒪̃_P` by control) is finite free over `𝒪`,
`R_k ⧸ 𝔞_k` and `R_k ⧸ 𝔟_k` are `𝒪`-torsion-free, `𝔞_k ∩ 𝔟_k = 0`, some `c ≠ 0` of `𝒪` lies in `𝔞_k + 𝔟_k`, and
`R_k ⧸ 𝔟_k ≅ 𝐓_k(M)_𝔪 ⊗ 𝒪̃_P` is `𝒪`-free. The point `P` is the point of (P): `f = F_P` is a `q`-new newform of level
`N = qM` and weight `k` (`k ≥ 3`, or `k = 2` with (P2)); this is not representable on the abstract data.

Normalisation: `P = algebraMap I 𝒪` is an arithmetic point of weight `k ≥ 2` for the GL₂-side Λ-structure of `T` (classical
diamonds, `P_k = ker([u] ↦ u^{k-2})`, `ss:s06-setting`); the definite side's adelic diamonds (`P^ad_k = ker([u] ↦ u^{2-k})`) enter
only through the inverse-diamond clause of `Hyp.LambdaJL` and are not used here. The cited source is Hida [Hi86b, Cor. 3.2
(3.3 b), p. 250] at level `N₀p`, plus p-stabilisation `T^ord_k(Np)_𝔪 ≅ T_k(N)_𝔪` and (P2).
Hida's Λ-structure [Hi86b, (3.1), p. 248, and p. 249: `l ↦ l²T(l,l)`] lets `z` act on weight `k` by `z^k⟨z⟩`, i.e. it is the
GL₂-side structure used here twisted by `[u] ↦ u²[u]` (no inversion). Hence Hida's `P_k = (1+X) − (1+p)^k` [Hi86b, p. 250]
and our `P_k = ker([u] ↦ u^{k-2})` are the same weight-`k` point of the Hecke algebra: there is no weight shift. As ideals of
the abstract Iwasawa algebra they differ by this twist (Hida's `P_k` is literally our `P_{k+2}`), so HACS's
`GL2.Literature.HidaEns32`, which uses Hida's polynomial verbatim, transfers to this hypothesis only after transporting the
`Λ`-algebra structure along `[u] ↦ u²[u]`, and in addition needs p-stabilisation (`p ∣ N` there, `p ∤ N` here).
HACS cross-reference (not a port): `code/hacs/lean/GL2/Literature/Hida.lean`, `HidaEns32` (same source and page).

Source: [Hi86b, Thm 3.1, Cor. 3.2 (3.3 b), p. 250]; chapter `lem:s06-pstab`, `lem:s06-control`, `lem:s06-decomp`.
Discharge: *cited*. Owner: S06-L8a. -/
def HidaControlGL2 (D : Defect.Setting Λ I T 𝒪 G) (p q M : ℕ) : Prop :=
  Defect.H0 p q M →
    Module.Free 𝒪 D.Rk ∧ Module.Finite 𝒪 D.Rk ∧ Module.IsTorsionFree 𝒪 (D.Rk ⧸ D.𝔞k) ∧
      Module.IsTorsionFree 𝒪 (D.Rk ⧸ D.𝔟k) ∧ D.𝔞k ⊓ D.𝔟k = ⊥ ∧
      (∃ c : 𝒪, c ≠ 0 ∧ algebraMap 𝒪 D.Rk c ∈ D.𝔞k ⊔ D.𝔟k) ∧ Module.Free 𝒪 (D.Rk ⧸ D.𝔟k)

end Hyp

namespace Defect.Setting

/-- `lem:s06-control` (`s06-control`), `lem:s06-decomp` at weight `k`: the weight-`k` new/old data `(R_k, 𝔞_k, 𝔟_k)`
over `𝒪` given by `Hyp.HidaControlGL2` under (H0); its ideals are `D.𝔞k`, `D.𝔟k` definitionally. -/
noncomputable def newOldAt (D : Defect.Setting Λ I T 𝒪 G) {p q M : ℕ} (h0 : Defect.H0 p q M)
    (h : Hyp.HidaControlGL2 D p q M) : CommAlg.NewOldData 𝒪 D.Rk where
  𝔞 := D.𝔞k
  𝔟 := D.𝔟k
  free := (h h0).1
  finite := (h h0).2.1
  tf_a := (h h0).2.2.1
  tf_b := (h h0).2.2.2.1
  inf_eq_bot := (h h0).2.2.2.2.1
  split := (h h0).2.2.2.2.2.1

/-- `lem:s06-control` (`s06-control`): the new kernel of `Setting.newOldAt` is `D.𝔞k`. -/
@[simp]
theorem newOldAt_𝔞 (D : Defect.Setting Λ I T 𝒪 G) {p q M : ℕ} (h0 : Defect.H0 p q M)
    (h : Hyp.HidaControlGL2 D p q M) : (D.newOldAt h0 h).𝔞 = D.𝔞k := rfl

/-- `lem:s06-control` (`s06-control`): the old kernel of `Setting.newOldAt` is `D.𝔟k`. -/
@[simp]
theorem newOldAt_𝔟 (D : Defect.Setting Λ I T 𝒪 G) {p q M : ℕ} (h0 : Defect.H0 p q M)
    (h : Hyp.HidaControlGL2 D p q M) : (D.newOldAt h0 h).𝔟 = D.𝔟k := rfl

end Defect.Setting

end Langlandscape
