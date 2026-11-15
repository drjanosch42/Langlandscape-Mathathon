/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Eisenstein
import Langlandscape.Brandt.HeckeFinite
import Langlandscape.Hyp.BrandtStabFree
import Langlandscape.Ribet.Mazur

/-!
# `Φ^comb` is Eisenstein at `Ô^×` — S03-L8

Instantiation of the abstract `Graph.phiComb_eisenstein` (S03-L7) at the Brandt graph `X_B(Ô^×)` with weights
`w_c = wx Ô^× (c.out)` and matrix `B(ℓ)` (import's `brandtMatrix`), for `prop:s03-phieis`
(`mathematics/chapters/s03/2-eisenstein.tex`):

* row sums `ℓ + 1` : import `brandt_row_sums` through the trivial level structure (`Brandt.trivialLevel`);
* symmetry `w_{c'} B(c,c') = w_c B(c',c)` : `Brandt.brandtMatrix_mul_wx`;
* `w_c ∣ B(c,c')` off the diagonal : the registered hypothesis `Hyp.BrandtStabFree` (step (1));
* `brandtZ_eq_Tl` : `B(ℓ)` is the matrix of the stage-1 `T_ℓ` (`Brandt.Tl_matrix_eq_brandtMatrix`);
* `phiCombDR_equiv` : `(DRgraph d).PhiComb ≃ phiComb (ohatWeight d) ℤ[X_B(Ô^×)]⁰` (`X(G_DR) = ℤ[E]⁰`,
  `Graph.twoVertex_X_eq_deg0`), and `phiComb_eisenstein_DR` : the Eisenstein property on the exported
  `(DRgraph d).PhiComb` (S03-L13, audit item R2).

Status: formalized modulo `Hyp.BrandtStabFree`. The `U₀(M)` version is not delivered (ext).
Never `open Graph` (clash with `_root_.Graph`).
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

variable (d : DefiniteData)

/-- The Brandt matrix `B(ℓ)` of the import at `Ô^×`, with integer entries (`prop:s03-phieis`, `s03-phieis`). -/
noncomputable def brandtZ (ℓ : ℕ) (c c' : XB d.Ohat) : ℤ :=
  (GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : ℤ)

/-- The weights at `Ô^×`: `w_c = wx Ô^× (c.out)` (`prop:s03-phieis`, `s03-phieis`). -/
noncomputable def ohatWeight (c : XB d.Ohat) : ℕ :=
  wx d.Ohat (Quotient.out c)

/-- The weights `w_x` at `Ô^×` are positive (`prop:s03-phieis`, `s03-phieis`; `|Γ_x| = 2 w_x` is finite and
nonzero). -/
theorem ohatWeight_pos (c : XB d.Ohat) : 0 < ohatWeight d c := by
  haveI : Finite (Gam d.Ohat (Quotient.out c)) :=
    ((GL2TF.Quat.stabilizer_units d.O.1 (Quotient.out c)).2.2 d.ha d.hb).1
  have h := two_mul_wx (negOne_mem_Ohat d) (Quotient.out c)
  have h2 : 0 < Nat.card (Gam d.Ohat (Quotient.out c)) := Nat.card_pos
  unfold ohatWeight
  omega

/-- `prop:s03-phieis` (`s03-phieis`), bridge to the exported Deligne–Rapoport graph: `Φ^comb(G_DR(Ô^×))` of
`Ribet.DRgraph d` is `Φ^comb` of the two-vertex lattice `ℤ[X_B(Ô^×)]⁰` with weights `ohatWeight d` (`prop:s03-phi`:
`X(G) = ℤ[E]⁰` for a graph with all edges `false → true`; the weights agree by definition). -/
noncomputable def phiCombDR_equiv [Fintype (XB d.Ohat)] :
    (DRgraph d).PhiComb ≃ₗ[ℤ]
      Langlandscape.Graph.phiComb (ohatWeight d) (Langlandscape.Graph.deg0 (XB d.Ohat) ℤ) :=
  letI : Fintype (DRgraph d).E := (inferInstance : Fintype (XB d.Ohat))
  Langlandscape.Graph.phiCombCongr (DRgraph d).w
    (Langlandscape.Graph.twoVertex_X_eq_deg0 (DRgraph d) (v₀ := false) (v₁ := true)
      Bool.false_ne_true (fun _ => rfl) (fun _ => rfl))

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ d.D)

/-- `prop:s03-phieis` (`s03-phieis`), matrix of `T_ℓ`: `B(ℓ)_{cc'} = (T_ℓ 1_{c'})(c)` for the stage-1 operator
`Tl` at `Ô^×` (finiteness by `relIndex_elemT_ne_zero_Ohat`). -/
theorem brandtZ_eq_Tl (c c' : XB d.Ohat) :
    brandtZ d ℓ c c' =
      Tl d d.Ohat ℓ hℓ ℤ (relIndex_elemT_ne_zero_Ohat d ℓ hℓ) (Pi.single c' (1 : ℤ)) c :=
  (Tl_matrix_eq_brandtMatrix d ℓ hℓ ℤ (relIndex_elemT_ne_zero_Ohat d ℓ hℓ) c c').symm

/-- `prop:s03-phieis` (`s03-phieis`), step (2): `w_{c'} B(c,c') = w_c B(c',c)` at `Ô^×` (from
`brandtMatrix_mul_wx`). -/
theorem brandtZ_symm (c c' : XB d.Ohat) :
    (ohatWeight d c' : ℤ) * brandtZ d ℓ c c' = (ohatWeight d c : ℤ) * brandtZ d ℓ c' c := by
  have h := brandtMatrix_mul_wx d ℓ ℤ c c'
  unfold brandtZ ohatWeight
  rw [mul_comm]
  exact h

include hℓ in
/-- `prop:s03-phieis` (`s03-phieis`), step (3): the row sums of `B(ℓ)` at `Ô^×` are `ℓ + 1` (import
`brandt_row_sums` at the trivial level structure, `σ₁(ℓ) = ℓ + 1`). -/
theorem brandtZ_row_sum [Fintype (XB d.Ohat)] (c : XB d.Ohat) :
    ∑ c', brandtZ d ℓ c c' = (ℓ : ℤ) + 1 := by
  have hp : ℓ.Prime := Fact.out
  have hcop : Nat.Coprime ℓ (d.D * 1) := by
    rw [mul_one]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hℓ
  have key : ∀ O : GL2TF.Quat.QOrder d.a d.b, O = d.O.1 →
      (∀ c : GL2TF.Quat.classSet O,
        ∑ᶠ c' : GL2TF.Quat.classSet O, GL2TF.Quat.brandtMatrix O ℓ c c' =
          ArithmeticFunction.sigma 1 ℓ) →
      ∀ c : GL2TF.Quat.classSet d.O.1,
        ∑ᶠ c' : GL2TF.Quat.classSet d.O.1, GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' =
          ArithmeticFunction.sigma 1 ℓ := by
    intro O hO h
    subst hO
    exact h
  have h := key _ (eichlerOrder_trivialLevel d)
    (GL2TF.Quat.brandt_row_sums d.O d.hD (trivialLevel d) ℓ hp.pos hcop) c
  have hσ : ArithmeticFunction.sigma 1 ℓ = ℓ + 1 := by
    have h1 := ArithmeticFunction.sigma_one_apply_prime_pow (p := ℓ) (i := 1) hp
    rw [pow_one] at h1
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  rw [hσ] at h
  have h3 : ∑ c' : XB d.Ohat, GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' = ℓ + 1 :=
    (finsum_eq_sum_of_fintype (fun c' : XB d.Ohat => GL2TF.Quat.brandtMatrix d.O.1 ℓ c c')).symm.trans h
  have h4 : ((∑ c' : XB d.Ohat, GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : ℕ) : ℤ) = (ℓ : ℤ) + 1 :=
    (congrArg (Nat.cast : ℕ → ℤ) h3).trans (Nat.cast_add_one ℓ)
  have h5 : ∑ c' : XB d.Ohat, ((GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : ℕ) : ℤ) =
      ((∑ c' : XB d.Ohat, GL2TF.Quat.brandtMatrix d.O.1 ℓ c c' : ℕ) : ℤ) :=
    (Nat.cast_sum Finset.univ (fun c' : XB d.Ohat => GL2TF.Quat.brandtMatrix d.O.1 ℓ c c')).symm
  exact h5.trans h4

include hℓ in
/-- `prop:s03-phieis` (`s03-phieis`), step (1) off the diagonal: `w_c ∣ B(c,c')` for `c ≠ c'`, from the
registered hypothesis `Hyp.BrandtStabFree` (and `D = q` prime). -/
theorem brandtZ_dvd (hq : d.D.Prime) (hyp : Langlandscape.Hyp.BrandtStabFree d ℓ)
    (c c' : XB d.Ohat) (hne : c ≠ c') : (ohatWeight d c : ℤ) ∣ brandtZ d ℓ c c' := by
  have h := hyp Fact.out hℓ hq c c' hne
  unfold ohatWeight brandtZ
  exact_mod_cast h

/-- `prop:s03-phieis` (`s03-phieis`) at `U = Ô^×`: for `D = q` prime, `ℓ ∤ D` and the registered hypothesis
`Hyp.BrandtStabFree` (step (1)), `T_ℓ − (ℓ + 1) = 0` on `Φ^comb` of the Brandt graph `X_B(Ô^×)` (two-vertex
lattice `ℤ[X_B(Ô^×)]⁰`, weights `w_c = wx Ô^× c.out`, `T_ℓ = B(ℓ)ᵗ` homologically). -/
theorem phiComb_eisenstein_Ohat [Fintype (XB d.Ohat)] (hq : d.D.Prime)
    (hyp : Langlandscape.Hyp.BrandtStabFree d ℓ) :
    Langlandscape.Graph.heckeQ (ohatWeight d) (ohatWeight_pos d) (brandtZ d ℓ) ((ℓ : ℤ) + 1)
        (brandtZ_row_sum d ℓ hℓ) (brandtZ_dvd d ℓ hℓ hq hyp) (brandtZ_symm d ℓ) -
      ((ℓ : ℤ) + 1) • LinearMap.id = 0 :=
  Langlandscape.Graph.phiComb_eisenstein ℓ (ohatWeight d) (ohatWeight_pos d) (brandtZ d ℓ)
    (brandtZ_row_sum d ℓ hℓ) (brandtZ_dvd d ℓ hℓ hq hyp) (brandtZ_symm d ℓ)

/-- `prop:s03-phieis` (`s03-phieis`) on the exported `(DRgraph d).PhiComb` (audit S03-L12, R2): for `D = q` prime,
`ℓ ∤ D` and `Hyp.BrandtStabFree`, the Hecke operator `T_ℓ` transported to `Φ^comb(G_DR(Ô^×))` along
`phiCombDR_equiv` (i.e. `e⁻¹ ∘ heckeQ ∘ e`) is multiplication by `ℓ + 1`. -/
theorem phiComb_eisenstein_DR [Fintype (XB d.Ohat)] (hq : d.D.Prime)
    (hyp : Langlandscape.Hyp.BrandtStabFree d ℓ) :
    (phiCombDR_equiv d).symm.toLinearMap ∘ₗ
        Langlandscape.Graph.heckeQ (ohatWeight d) (ohatWeight_pos d) (brandtZ d ℓ) ((ℓ : ℤ) + 1)
          (brandtZ_row_sum d ℓ hℓ) (brandtZ_dvd d ℓ hℓ hq hyp) (brandtZ_symm d ℓ) ∘ₗ
        (phiCombDR_equiv d).toLinearMap =
      ((ℓ : ℤ) + 1) • LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, LinearMap.smul_apply,
    LinearMap.id_apply]
  rw [Langlandscape.Graph.phiComb_eisenstein_apply, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]

end Langlandscape.Ribet
