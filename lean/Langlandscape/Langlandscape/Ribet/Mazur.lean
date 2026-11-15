/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.MazurArith
import Langlandscape.Graph.TwoVertex
import Langlandscape.Graph.Cyclic
import Langlandscape.Hyp.EllipticCount
import Langlandscape.Brandt.ImportDictionary
import Langlandscape.Quat.LevelFinite
import Mathlib.Tactic.NormNum.Prime

/-!
# The Mazur check — S03-L6

`mathematics/chapters/s03/1-graphs.tex`, `prop:s03-mazur`, `lem:s03-elliptic`.

* `Ribet.DRgraph d`: the two-vertex weighted graph with `E = X_B(Ô^×)` and `w = wx` (all edges `false → true`);
* `Ribet.sum_inv_wx_Ohat`: `Σ_x w_x⁻¹ = (q-1)/12` for `D = q` prime, from `Hyp.EichlerMass`
  (`massFull_eq_massW_of_mem`, `negOne_mem_Ohat`);
* `Ribet.mazur_check`: `Φ^comb(DRgraph d) ≃+ ℤ/num((q-1)/12)` for every prime `q = d.D`, under
  `Hyp.EichlerMass` and `Hyp.EllipticCount`. For `q ≥ 5` via `Graph.mazur_prod_mul_sum`,
  `Graph.mazur_weights_pairwise_coprime` and `Graph.lambdaBar_bijective_of_pairwise_coprime`; for `q ∈ {2,3}`
  (one class) the weights are trivially pairwise coprime and `num = 1`.
  The modulus is `(Graph.mazurNum q).natAbs` (`mazurNum q ≥ 0`).

Status: formalized (modulo `Hyp.EichlerMass`, `Hyp.EllipticCount`). Never `open Graph`.
-/

set_option autoImplicit false

namespace Langlandscape.Ribet

open Langlandscape.Quat

/-- `def:s03-DR` (`s03-mazur`): `w_x ≥ 1` at the maximal order. -/
theorem wx_Ohat_pos (d : DefiniteData) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) : 0 < wx d.Ohat x := by
  have h2 := two_mul_wx (Langlandscape.Brandt.negOne_mem_Ohat d) x
  have hdvd := card_Gam_dvd_24 d.ha d.hb d.O.1 (le_refl d.Ohat) x
  have hpos : 0 < Nat.card (Gam d.Ohat x) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  omega

/-- `def:s03-DR` (`s03-mazur`): the Deligne–Rapoport graph at the maximal level, as a weighted graph with two vertices
(`false`, `true`), edges `X_B(Ô^×)` all oriented `false → true`, and weights `w_x`. -/
@[reducible] noncomputable def DRgraph (d : DefiniteData) : Langlandscape.Graph.WGraph where
  V := Bool
  E := XB d.Ohat
  src _ := false
  tgt _ := true
  w c := wx d.Ohat (Quotient.out c)
  hw c := wx_Ohat_pos d _

/-- `prop:s03-mazur` (`s03-mazur`): the mass formula in `w`-form, `Σ_x w_x⁻¹ = (q-1)/12` for `d.D = q` prime, from
`Hyp.EichlerMass` (`massFull = massW / 2` since `-1 ∈ Ô^×`). -/
theorem sum_inv_wx_Ohat (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (q : ℕ) (hq : q.Prime) (hD : d.D = q) [Fintype (XB d.Ohat)] :
    ∑ c : XB d.Ohat, (1 : ℚ) / (wx d.Ohat (Quotient.out c) : ℚ) = ((q : ℚ) - 1) / 12 := by
  have hmass : massFull d.Ohat = 1 / 24 * ∏ p ∈ d.D.primeFactors, ((p : ℚ) - 1) :=
    (massFull_units_eq_mass d.O.1).trans (hM d.hD)
  have hpf : d.D.primeFactors = {q} := by rw [hD]; exact Nat.Prime.primeFactors hq
  rw [hpf, Finset.prod_singleton] at hmass
  have h2 := massFull_eq_massW_of_mem (U := d.Ohat) (Langlandscape.Brandt.negOne_mem_Ohat d)
  have hsum : massW d.Ohat = ∑ c : XB d.Ohat, (1 : ℚ) / (wx d.Ohat (Quotient.out c) : ℚ) := by
    rw [massW, finsum_eq_sum_of_fintype]
  rw [← hsum]
  linarith

/-- `prop:s03-mazur` (`s03-mazur`): `num ((2-1)/12) = num (1/12) = 1`. -/
private lemma s03_mazurNum_two : Langlandscape.Graph.mazurNum 2 = 1 := by
  have h : (((2 : ℕ) : ℚ) - 1) / 12 = ((1 : ℤ) : ℚ) / ((12 : ℤ) : ℚ) := by norm_num
  unfold Langlandscape.Graph.mazurNum
  rw [h]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by first | decide | norm_num)

/-- `prop:s03-mazur` (`s03-mazur`): `num ((3-1)/12) = num (1/6) = 1`. -/
private lemma s03_mazurNum_three : Langlandscape.Graph.mazurNum 3 = 1 := by
  have h : (((3 : ℕ) : ℚ) - 1) / 12 = ((1 : ℤ) : ℚ) / ((6 : ℤ) : ℚ) := by norm_num
  unfold Langlandscape.Graph.mazurNum
  rw [h]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by first | decide | norm_num)

/-- `prop:s03-mazur` (`s03-mazur`): `Nat.card` of a subtype is the cardinality of the filter. -/
private lemma s03_natCard_subtype_eq_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a // p a} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `prop:s03-mazur` (`s03-mazur`): the Mazur check. For `d.D = q` prime, under `Hyp.EichlerMass` and
`Hyp.EllipticCount`, `Φ^comb(G_DR(Ô^×)) ≃+ ℤ/num((q-1)/12)` (the modulus is `(mazurNum q).natAbs`;
`q ≥ 5` via S03-L5 and S03-L4, `q ∈ {2,3}` as its own case: one class, one edge, both sides trivial). -/
noncomputable def mazur_check (d : DefiniteData) (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hE : Langlandscape.Hyp.EllipticCount d) (q : ℕ) (hq : q.Prime) (hD : d.D = q) :
    (DRgraph d).PhiComb ≃+ ZMod (Langlandscape.Graph.mazurNum q).natAbs := by
  letI : Fintype (XB d.Ohat) := Fintype.ofFinite _
  letI : Fintype (DRgraph d).E := (inferInstance : Fintype (XB d.Ohat))
  letI : DecidableEq (DRgraph d).E := Classical.decEq _
  have hDp : d.D.Prime := by rw [hD]; exact hq
  have hsum := sum_inv_wx_Ohat d hM q hq hD
  have hne : Nonempty (DRgraph d).E := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    haveI : IsEmpty (XB d.Ohat) := hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  haveI := hne
  let e0 : (DRgraph d).E := hne.some
  have hG : (DRgraph d).IsTwoVertex :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => Bool.false_ne_true⟩
  have hcard : Nat.card (DRgraph d).PhiComb = Langlandscape.Graph.cycMod (DRgraph d) :=
    Langlandscape.Graph.card_phiComb_twoVertex (DRgraph d) (v₀ := false) (v₁ := true)
      Bool.false_ne_true (fun _ => rfl) (fun _ => rfl)
  have key : Pairwise (fun e e' : (DRgraph d).E => Nat.Coprime ((DRgraph d).w e) ((DRgraph d).w e')) ∧
      Langlandscape.Graph.cycMod (DRgraph d) = (Langlandscape.Graph.mazurNum q).natAbs := by
    have hq4 : q ≠ 4 := by
      rintro rfl
      exact absurd hq (by norm_num)
    have hq2 := hq.two_le
    by_cases h5 : 5 ≤ q
    · obtain ⟨hw, h2, h3⟩ := (hE hDp).1 (by omega)
      rw [hD] at h2 h3
      have h2' : (Finset.univ.filter (fun i : (DRgraph d).E => (DRgraph d).w i = 2)).card =
          if q % 4 = 3 then 1 else 0 :=
        (s03_natCard_subtype_eq_filter (fun i : (DRgraph d).E => (DRgraph d).w i = 2)).symm.trans h2
      have h3' : (Finset.univ.filter (fun i : (DRgraph d).E => (DRgraph d).w i = 3)).card =
          if q % 3 = 2 then 1 else 0 :=
        (s03_natCard_subtype_eq_filter (fun i : (DRgraph d).E => (DRgraph d).w i = 3)).symm.trans h3
      have hL5 := Langlandscape.Graph.mazur_prod_mul_sum (ι := (DRgraph d).E) q hq h5
        (DRgraph d).w hw h2' h3' hsum
      refine ⟨?_, ?_⟩
      · have hcop := Langlandscape.Graph.mazur_weights_pairwise_coprime (DRgraph d).w hw
          (by rw [h2']; split_ifs <;> simp) (by rw [h3']; split_ifs <;> simp)
        exact fun a b hab => hcop a b hab
      · have hc : ((Langlandscape.Graph.cycMod (DRgraph d) : ℕ) : ℚ) =
            ((∏ i, (DRgraph d).w i : ℕ) : ℚ) * ∑ i, (1 : ℚ) / ((DRgraph d).w i : ℚ) := by
          unfold Langlandscape.Graph.cycMod
          rw [Nat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          have h1 := Langlandscape.Graph.cycCoeff_mul_w (G := DRgraph d) e
          have hwe : ((DRgraph d).w e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ((DRgraph d).hw e).ne'
          have h1' : (Langlandscape.Graph.cycCoeff (DRgraph d) e : ℚ) * ((DRgraph d).w e : ℚ) =
              ((∏ i, (DRgraph d).w i : ℕ) : ℚ) := by exact_mod_cast h1
          rw [← h1', mul_assoc, mul_one_div_cancel hwe, mul_one]
        have hz : ((Langlandscape.Graph.cycMod (DRgraph d) : ℕ) : ℤ) = Langlandscape.Graph.mazurNum q := by
          exact_mod_cast hc.trans hL5
        have := congrArg Int.natAbs hz
        simpa using this
    · have hq3 : q = 2 ∨ q = 3 := by omega
      have h1 := (hE hDp).2 (by omega)
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h1
      refine ⟨fun a b hab => absurd (hsub.allEq a b) hab, ?_⟩
      haveI : Unique (DRgraph d).E := { default := e0, uniq := fun a => hsub.allEq a e0 }
      have hcm : Langlandscape.Graph.cycMod (DRgraph d) = 1 := by
        unfold Langlandscape.Graph.cycMod Langlandscape.Graph.cycCoeff
        simp [Finset.univ_unique, Finset.erase_singleton]
      rw [hcm]
      rcases hq3 with rfl | rfl
      · rw [s03_mazurNum_two]; rfl
      · rw [s03_mazurNum_three]; rfl
  obtain ⟨hcop, hcyc⟩ := key
  have hbij := Langlandscape.Graph.lambdaBar_bijective_of_pairwise_coprime hG e0 hcop hcard
  exact (LinearEquiv.ofBijective (Langlandscape.Graph.lambdaBar hG e0) hbij).toAddEquiv.trans
    (ZMod.ringEquivCongr hcyc).toAddEquiv

end Langlandscape.Ribet
