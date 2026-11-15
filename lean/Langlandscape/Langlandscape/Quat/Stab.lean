/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Quat.LocalEmbed

/-!
# Lemma `stab`, parts (a) and (c) (S01-L5a)

`lem:s01-stab` (a), (c) of `plan/staged/stage-01-quaternion-foundations.tex`, for subgroups `U ≤ Ô^×`:
the stabilisers `Γ_x(U)` have reduced norm `1`, are monotone in `U`, have order dividing `24`, and
`p ∤ |Γ_x|` for primes `p ≥ 5`.

Status: *formalized* (from the import lemmas `stabilizer_units`, `nrd_definite`, `card_unitGroup_dvd_24`).

Section `Free` (S01-L5b): `lem:s01-stab` (b), first half: `Γ_x(U) = 1` for `U ≤ U_1(p)`, `p ≥ 5`
(`Gam_eq_bot_of_le_U1`). Route: `γ ∈ O_x^×` with `nrd γ = 1`, the five cases of `unit_cases`, and the
`(2,2)`-entry of `g = ι_p(x_p⁻¹ γ x_p) ∈ K1 p 1` (resp. of `g²`) modulo `p`.

Section `Delta` (S01-L5c): `lem:s01-stab` (b), second half, for `U = Utower`: the elements
`δ_t = localEmbedGL p (diag(1, t))` normalise `U_s`, give a permutation action `diamondAct t` of `ℤ_p^×` on
`X_B(U_s)` (`[x] ↦ [x δ_t]`), and an element `t ≡ 1 mod p` fixing a point satisfies `t ≡ 1 mod p^s`
(`diamondAct_free`). `diamondAct_mul`, `diamondAct_eq_one` (`t ≡ 1 mod p^s` acts trivially) and
`diamondAct_eq_of_dvd` make it an action of `Δ_s = ℤ_p^× / (1 + p^s ℤ_p)`.

S01-L16b (audit R3/R6): `deltaElt` is the only definition of `δ_t` (`Brandt.diamondElt` abbreviates it). It is
the *local factor at one prime `p`* of the tex's `δ_d`, `d ∈ (ℤ/Mp^s)^×`; the product over `ℓ ∣ Mp` is not
assembled. Normalisation at the generic levels: `deltaElt_mem_U0` (`δ_t ∈ U_0(N)`, every split `p`),
`deltaElt_normalizes_U1`, `deltaElt_inv_normalizes_U1` (`p ∣ N`), `deltaElt_mem_levelAt_of_notMem` (`p ∤ N`), from
`localEmbedGL_conj_mem_levelAt`, `localEmbedGL_mem_levelAt`, `localEmbedGL_mem_levelAt_of_notMem`.
-/

namespace Langlandscape.Quat

open GL2TF GL2TF.Quat

variable {a b : ℤ}

/-- `Gam U x ≤ Gam U' x` for `U ≤ U'` (monotonicity of the stabiliser, `lem:s01-stab`, `def:s01-classset`). -/
theorem Gam_mono {U U' : Subgroup (BHat a b)ˣ} (h : U ≤ U') (x : (BHat a b)ˣ) :
    Gam U x ≤ Gam U' x := by
  intro γ hγ
  simp only [Gam, GL2TF.Quat.classStabilizer, Subgroup.mem_comap, Subgroup.mem_map] at hγ ⊢
  obtain ⟨v, hv, hvγ⟩ := hγ
  exact ⟨v, h hv, hvγ⟩

/-- `lem:s01-stab` (a) (`s01-stab`): for `U ≤ Ô^×` (`a, b < 0`), every `γ ∈ Γ_x(U)` has reduced norm `1`. -/
theorem nrd_eq_one_of_mem_Gam (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    {U : Subgroup (BHat a b)ˣ} (hU : U ≤ GL2TF.Quat.orderCompletionUnits O)
    {x : (BHat a b)ˣ} {γ : (QuatAlg ℚ a b)ˣ} (hγ : γ ∈ Gam U x) :
    GL2TF.Quat.nrd (γ : QuatAlg ℚ a b) = 1 := by
  obtain ⟨Ox, -, hOx⟩ := (GL2TF.Quat.stabilizer_units O x).1
  have h : γ ∈ GL2TF.Quat.unitGroup Ox := hOx ▸ Gam_mono hU x hγ
  exact (GL2TF.Quat.unitGroup_val_props ha hb Ox γ h).2

/-- `lem:s01-stab` (c) (`s01-stab`, `prop:s01-finite`): for `U ≤ Ô^×` (`a, b < 0`), `|Γ_x(U)|` divides `24`. -/
theorem card_Gam_dvd_24 (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    {U : Subgroup (BHat a b)ˣ} (hU : U ≤ GL2TF.Quat.orderCompletionUnits O) (x : (BHat a b)ˣ) :
    Nat.card (Gam U x) ∣ 24 := by
  obtain ⟨Ox, -, hOx⟩ := (GL2TF.Quat.stabilizer_units O x).1
  have hle : Gam U x ≤ GL2TF.Quat.unitGroup Ox := hOx ▸ Gam_mono hU x
  have hfin : Finite (GL2TF.Quat.unitGroup Ox) := (GL2TF.Quat.unitGroup_eq_nrd_one_finite ha hb Ox).2
  exact (Subgroup.card_dvd_of_le hle).trans (GL2TF.Quat.card_unitGroup_dvd_24 ha hb Ox).2.1

/-- `lem:s01-stab` (c) (`s01-stab`): for a prime `p ≥ 5` and `U ≤ Ô^×`, `p ∤ |Γ_x(U)|`. -/
theorem not_dvd_card_Gam (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    {U : Subgroup (BHat a b)ˣ} (hU : U ≤ GL2TF.Quat.orderCompletionUnits O) (x : (BHat a b)ˣ)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ Nat.card (Gam U x) := by
  intro hdvd
  have h24 : p ∣ 24 := hdvd.trans (card_Gam_dvd_24 ha hb O hU x)
  have hle : p ≤ 24 := Nat.le_of_dvd (by norm_num) h24
  clear hdvd
  interval_cases p <;> first | omega | exact absurd hp (by decide)

/-! ### Section `Free`: `Γ_x = 1` at level `U_1(p)`, `p ≥ 5` (S01-L5b) -/

section Free

/-- Auxiliary for `lem:s01-stab` (b) (`s01-stab`): a prime `p ≥ 5` divides none of `1, 2, 3` in `ℤ_p`. -/
theorem padicInt_not_dvd_small {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 3)
    (h : (p : ℤ_[p]) ∣ (n : ℤ_[p])) : False := by
  have h1 : ‖((n : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    exact_mod_cast h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  have h2 : p ∣ n := by exact_mod_cast h1
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- Auxiliary for `lem:s01-stab` (b) (`s01-stab`, `def:s01-levels`): for `g ∈ K1 p 1`, write `c = p c'`,
`d = 1 + p e'`; then `g₂₂ = 1 + p e'` and `(g²)₂₂ = p c' b + (1 + p e')²`. -/
theorem K1_one_entries {p : ℕ} [Fact p.Prime] {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ Langlandscape.Local.K1 p 1) :
    ∃ b c e : ℤ_[p], (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = ((1 + (p : ℤ_[p]) * e : ℤ_[p]) : ℚ_[p]) ∧
      ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (g : Matrix (Fin 2) (Fin 2) ℚ_[p])) 1 1 =
        (((p : ℤ_[p]) * c * b + (1 + (p : ℤ_[p]) * e) * (1 + (p : ℤ_[p]) * e) : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨a₀, b₀, c₀, d₀, hM, -, ⟨c', hc⟩, ⟨e', he⟩⟩ := Langlandscape.Local.mem_K1_iff_exists.1 hg
  have hc' : c₀ = (p : ℤ_[p]) * c' := by rw [hc, pow_one]
  have hd' : d₀ = 1 + (p : ℤ_[p]) * e' := by
    rw [pow_one] at he
    linear_combination he
  have e10 : (Units.val g) 1 0 = (c₀ : ℚ_[p]) := by rw [hM]; rfl
  have e01 : (Units.val g) 0 1 = (b₀ : ℚ_[p]) := by rw [hM]; rfl
  have e11 : (Units.val g) 1 1 = (d₀ : ℚ_[p]) := by rw [hM]; rfl
  refine ⟨b₀, c', e', ?_, ?_⟩
  · rw [e11, hd']
  · rw [Matrix.mul_apply, Fin.sum_univ_two, e10, e01, e11, hc', hd']
    push_cast
    ring

/-- `lem:s01-stab` (b) (`s01-stab`, first half): for a prime `p ≥ 5` with `(p, D) = 1` and `U ≤ U_1(p)`, every
stabiliser `Γ_x(U)` is trivial. -/
theorem Gam_eq_bot_of_le_U1 (d : DefiniteData) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpD : p.Coprime d.D)
    {U : Subgroup (BHat d.a d.b)ˣ} (hU : U ≤ d.U1 p hpD) (x : (BHat d.a d.b)ˣ) : Gam U x = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  -- (1) `γ ∈ O_x^×`, `nrd γ = 1`
  have hUO : U ≤ GL2TF.Quat.orderCompletionUnits d.O.1 := hU.trans (DefiniteData.U1_le_units p hpD)
  obtain ⟨Ox, -, hOx⟩ := (GL2TF.Quat.stabilizer_units d.O.1 x).1
  have hγOx : γ ∈ GL2TF.Quat.unitGroup Ox := hOx ▸ Gam_mono hUO x hγ
  have hγO := (GL2TF.Quat.unitGroup_val_props d.ha d.hb Ox γ hγOx).1
  have hn : GL2TF.Quat.nrd (γ : QuatAlg ℚ d.a d.b) = 1 := nrd_eq_one_of_mem_Gam d.ha d.hb d.O.1 hUO hγ
  -- (2) the element `v = x⁻¹ γ x ∈ U` and its local component at `p`
  have hγ' := hγ
  simp only [Gam, GL2TF.Quat.classStabilizer, Subgroup.mem_comap, Subgroup.mem_map] at hγ'
  obtain ⟨v, hvU, hvγ⟩ := hγ'
  have hv2 : x * v * x⁻¹ = Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ := hvγ
  have hvx : v = x⁻¹ * Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ * x := by
    rw [← hv2]; group
  have hv' : (v : BHat d.a d.b) = ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b) *
      GL2TF.Quat.finEmbed d.a d.b (γ : QuatAlg ℚ d.a d.b) * (x : BHat d.a d.b) := by
    subst hvx; rfl
  have hpmem : p ∈ p.primeFactors := Nat.mem_primeFactors.2 ⟨hp, dvd_rfl, hp.ne_zero⟩
  have hD : ¬ p ∣ d.D := d.not_dvd_D_of_mem_primeFactors hpD hpmem
  have hK : localComponent d p hD v ∈ Langlandscape.Local.K1 p 1 := by
    have := (DefiniteData.mem_U1_iff.1 (hU hvU)).2 p hpmem hD
    rwa [hp.factorization_self] at this
  -- (3) `ι_p(v_p) = Q ψ(γ) P` with `Q P = P Q = 1`
  obtain ⟨φ, hφ⟩ : ∃ φ : BHat d.a d.b →+* Matrix (Fin 2) (Fin 2) ℚ_[p],
      ∀ y, φ y = d.iota p hD (localProj d.a d.b p y) :=
    ⟨(d.iota p hD).toRingEquiv.toRingHom.comp (localProj d.a d.b p), fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : QuatAlg ℚ d.a d.b →+* Matrix (Fin 2) (Fin 2) ℚ_[p],
      ∀ z, ψ z = φ (GL2TF.Quat.finEmbed d.a d.b z) :=
    ⟨φ.comp (GL2TF.Quat.finEmbed d.a d.b), fun _ => rfl⟩
  have hQP : φ ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b) * φ (x : BHat d.a d.b) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hPQ : φ (x : BHat d.a d.b) * φ ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hG : ((localComponent d p hD v : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      φ ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b) * ψ (γ : QuatAlg ℚ d.a d.b) *
        φ (x : BHat d.a d.b) := by
    rw [localComponent_val, ← hφ, hψ, hv', map_mul, map_mul]
  set Q := φ ((x⁻¹ : (BHat d.a d.b)ˣ) : BHat d.a d.b)
  set P := φ (x : BHat d.a d.b)
  have conjsq : Q * ψ (γ : QuatAlg ℚ d.a d.b) * P * (Q * ψ (γ : QuatAlg ℚ d.a d.b) * P) =
      Q * ψ ((γ : QuatAlg ℚ d.a d.b) ^ 2) * P := by
    rw [sq, map_mul]
    calc Q * ψ (γ : QuatAlg ℚ d.a d.b) * P * (Q * ψ (γ : QuatAlg ℚ d.a d.b) * P)
        = Q * ψ (γ : QuatAlg ℚ d.a d.b) * (P * Q) * ψ (γ : QuatAlg ℚ d.a d.b) * P := by
          simp only [mul_assoc]
      _ = Q * (ψ (γ : QuatAlg ℚ d.a d.b) * ψ (γ : QuatAlg ℚ d.a d.b)) * P := by
          rw [hPQ, mul_one]; simp only [mul_assoc]
  -- (4) the `(2,2)`-entries modulo `p`
  obtain ⟨b, c, e, h11, hsq⟩ := K1_one_entries hK
  rw [hG] at h11 hsq
  rcases GL2TF.Quat.unit_cases d.ha d.hb Ox hγO hn with h | h | h | h | h
  · exact Units.val_eq_one.1 h
  · exfalso
    have hA : ψ (γ : QuatAlg ℚ d.a d.b) = -1 := by rw [h, map_neg, map_one]
    rw [hA, mul_neg, mul_one, neg_mul, hQP, Matrix.neg_apply, Matrix.one_apply_eq] at h11
    have hZ : (-1 : ℤ_[p]) = 1 + (p : ℤ_[p]) * e := PadicInt.ext (by push_cast at h11 ⊢; linear_combination h11)
    exact padicInt_not_dvd_small h5 2 (by norm_num) (by norm_num) ⟨-e, by linear_combination -hZ⟩
  · exfalso
    have h2 : Q * ψ (γ : QuatAlg ℚ d.a d.b) * P * (Q * ψ (γ : QuatAlg ℚ d.a d.b) * P) = -1 := by
      rw [conjsq, h, map_neg, map_one, mul_neg, mul_one, neg_mul, hQP]
    rw [h2, Matrix.neg_apply, Matrix.one_apply_eq] at hsq
    have hZ : (-1 : ℤ_[p]) = (p : ℤ_[p]) * c * b + (1 + (p : ℤ_[p]) * e) * (1 + (p : ℤ_[p]) * e) := by
      apply PadicInt.ext
      push_cast at hsq ⊢
      linear_combination hsq
    exact padicInt_not_dvd_small h5 2 (by norm_num) (by norm_num)
      ⟨-(c * b) - 2 * e - (p : ℤ_[p]) * e * e, by linear_combination -hZ⟩
  · exfalso
    have h2 : Q * ψ (γ : QuatAlg ℚ d.a d.b) * P * (Q * ψ (γ : QuatAlg ℚ d.a d.b) * P) =
        Q * ψ (γ : QuatAlg ℚ d.a d.b) * P - 1 := by
      rw [conjsq, h, map_sub, map_one, mul_sub, sub_mul, mul_one, hQP]
    rw [h2, Matrix.sub_apply, h11, Matrix.one_apply_eq] at hsq
    have hZ : (1 + (p : ℤ_[p]) * e) - 1 = (p : ℤ_[p]) * c * b + (1 + (p : ℤ_[p]) * e) * (1 + (p : ℤ_[p]) * e) := by
      apply PadicInt.ext
      push_cast at hsq ⊢
      linear_combination hsq
    exact padicInt_not_dvd_small h5 1 (by norm_num) (by norm_num)
      ⟨-(c * b) - e - (p : ℤ_[p]) * e * e, by linear_combination -hZ⟩
  · exfalso
    have h2 : Q * ψ (γ : QuatAlg ℚ d.a d.b) * P * (Q * ψ (γ : QuatAlg ℚ d.a d.b) * P) =
        -(Q * ψ (γ : QuatAlg ℚ d.a d.b) * P) - 1 := by
      rw [conjsq, h, map_sub, map_neg, map_one, mul_sub, sub_mul, mul_neg, neg_mul, mul_one, hQP]
    rw [h2, Matrix.sub_apply, Matrix.neg_apply, h11, Matrix.one_apply_eq] at hsq
    have hZ : -(1 + (p : ℤ_[p]) * e) - 1 = (p : ℤ_[p]) * c * b + (1 + (p : ℤ_[p]) * e) * (1 + (p : ℤ_[p]) * e) := by
      apply PadicInt.ext
      push_cast at hsq ⊢
      linear_combination hsq
    exact padicInt_not_dvd_small h5 3 (by norm_num) (by norm_num)
      ⟨-(c * b) - 3 * e - (p : ℤ_[p]) * e * e, by linear_combination -hZ⟩

end Free

/-! ### Section `Delta`: freeness of `Δ_s` on `X_B(U_s)` (S01-L5c) -/

section Delta

open Langlandscape.Local

/-- Auxiliary for `lem:s01-stab` (b) (`s01-stab`): conjugation by `diag(1, t)`, `t ∈ ℤ_ℓ^×`, preserves `K1 ℓ e`
(the lower-left entry is multiplied by the unit `t`, the upper-right by `t⁻¹`, `d` is unchanged). -/
theorem diagOne_conj_mem_K1 {p : ℕ} [Fact p.Prime] (t : ℤ_[p]ˣ) (e : ℕ) {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ K1 p e) : diagGL 1 (intUnit t) * g * (diagGL 1 (intUnit t))⁻¹ ∈ K1 p e := by
  obtain ⟨a, b, c, dd, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hg
  obtain ⟨s, hs⟩ : ∃ s : ℤ_[p], s * (t : ℤ_[p]) = 1 := ⟨((t⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), t.inv_mul⟩
  have hs' : (s : ℚ_[p]) * ((t : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hs
    simpa using this
  have hdet : (a : ℚ_[p]) * (dd : ℚ_[p]) - ((b * s : ℤ_[p]) : ℚ_[p]) *
      ((((t : ℤ_[p]) * c : ℤ_[p])) : ℚ_[p]) ≠ 0 := by
    have h1 := Langlandscape.Local.det_ne_zero g
    rw [hM, Matrix.det_fin_two_of] at h1
    intro h0
    apply h1
    push_cast at h0
    linear_combination h0 + (b : ℚ_[p]) * (c : ℚ_[p]) * hs'
  let k : GL (Fin 2) ℚ_[p] := matGL (a : ℚ_[p]) ((b * s : ℤ_[p]) : ℚ_[p])
    ((((t : ℤ_[p]) * c : ℤ_[p])) : ℚ_[p]) (dd : ℚ_[p]) hdet
  have hkM : Units.val k = !![(a : ℚ_[p]), ((b * s : ℤ_[p]) : ℚ_[p]);
      ((((t : ℤ_[p]) * c : ℤ_[p])) : ℚ_[p]), dd] := rfl
  have heq : diagGL 1 (intUnit t) * g = k * diagGL 1 (intUnit t) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, diagGL_val, hM, hkM, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (try simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_one, coe_intUnit,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]) <;>
      push_cast <;>
      first
        | ring1
        | linear_combination (-(b : ℚ_[p])) * hs'
  have hk : k ∈ K1 p e := by
    refine mem_K1_of_entries a (b * s) ((t : ℤ_[p]) * c) dd hkM ?_ (hc.mul_left _) hd
    have : a * dd - b * s * ((t : ℤ_[p]) * c) = a * dd - b * c := by
      linear_combination (-(b * c)) * hs
    rw [this]; exact hu
  have hfin : diagGL 1 (intUnit t) * g * (diagGL 1 (intUnit t))⁻¹ = k :=
    calc diagGL 1 (intUnit t) * g * (diagGL 1 (intUnit t))⁻¹
        = k * diagGL 1 (intUnit t) * (diagGL 1 (intUnit t))⁻¹ := by rw [heq]
      _ = k := mul_inv_cancel_right _ _
  rw [hfin]
  exact hk

/-- Auxiliary for `lem:s01-stab` (b) (`s01-stab`): conjugation by `diag(1, t)⁻¹` preserves `K1 ℓ e`. -/
theorem diagOne_inv_conj_mem_K1 {p : ℕ} [Fact p.Prime] (t : ℤ_[p]ˣ) (e : ℕ) {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ K1 p e) : (diagGL 1 (intUnit t))⁻¹ * g * diagGL 1 (intUnit t) ∈ K1 p e := by
  obtain ⟨a, b, c, dd, hM, hu, hc, hd⟩ := mem_K1_iff_exists.1 hg
  obtain ⟨s, hs⟩ : ∃ s : ℤ_[p], s * (t : ℤ_[p]) = 1 := ⟨((t⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), t.inv_mul⟩
  have hs' : (s : ℚ_[p]) * ((t : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hs
    simpa using this
  have hdet : (a : ℚ_[p]) * (dd : ℚ_[p]) - ((b * (t : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) *
      ((s * c : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    have h1 := Langlandscape.Local.det_ne_zero g
    rw [hM, Matrix.det_fin_two_of] at h1
    intro h0
    apply h1
    push_cast at h0
    linear_combination h0 + (b : ℚ_[p]) * (c : ℚ_[p]) * hs'
  let k : GL (Fin 2) ℚ_[p] := matGL (a : ℚ_[p]) ((b * (t : ℤ_[p]) : ℤ_[p]) : ℚ_[p])
    ((s * c : ℤ_[p]) : ℚ_[p]) (dd : ℚ_[p]) hdet
  have hkM : Units.val k = !![(a : ℚ_[p]), ((b * (t : ℤ_[p]) : ℤ_[p]) : ℚ_[p]);
      ((s * c : ℤ_[p]) : ℚ_[p]), dd] := rfl
  have heq : g * diagGL 1 (intUnit t) = diagGL 1 (intUnit t) * k := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, diagGL_val, hM, hkM, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (try simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_one, coe_intUnit,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]) <;>
      push_cast <;>
      first
        | ring1
        | linear_combination (-(b : ℚ_[p])) * hs'
        | linear_combination (b : ℚ_[p]) * hs'
        | linear_combination (-(c : ℚ_[p])) * hs'
  have hk : k ∈ K1 p e := by
    refine mem_K1_of_entries a (b * (t : ℤ_[p])) (s * c) dd hkM ?_ (hc.mul_left _) hd
    have : a * dd - b * (t : ℤ_[p]) * (s * c) = a * dd - b * c := by
      linear_combination (-(b * c)) * hs
    rw [this]; exact hu
  have hfin : (diagGL 1 (intUnit t))⁻¹ * g * diagGL 1 (intUnit t) = k :=
    calc (diagGL 1 (intUnit t))⁻¹ * g * diagGL 1 (intUnit t)
        = (diagGL 1 (intUnit t))⁻¹ * (g * diagGL 1 (intUnit t)) := mul_assoc _ _ _
      _ = (diagGL 1 (intUnit t))⁻¹ * (diagGL 1 (intUnit t) * k) := by rw [heq]
      _ = k := inv_mul_cancel_left _ _
  rw [hfin]
  exact hk

variable (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)

/-- The local element `diag(1, t) ∈ GL₂(ℚ_p)` for `t ∈ ℤ_p^×` (`lem:s01-stab` (b), `s01-stab`). -/
noncomputable def deltaLoc (t : ℤ_[p]ˣ) : GL (Fin 2) ℚ_[p] := diagGL 1 (intUnit t)

/-- `δ_t = ι_p⁻¹ diag(1, t) ∈ B̂^×` (`lem:s01-stab` (b), `def:s01-hecke`, `s01-stab`): `localEmbedGL p (diag(1, t))`.
This is the only definition of `δ_t`; the element `Brandt.diamondElt` of the diamond operator `Brandt.diamond`
(`Brandt/Hecke.lean`) is an abbreviation of it. It is supported at the single prime `p`. -/
noncomputable def deltaElt (t : ℤ_[p]ˣ) : (BHat d.a d.b)ˣ :=
  localEmbedGL d p hp (deltaLoc p t)

/-- `diag(1, t t') = diag(1, t) diag(1, t')` (`lem:s01-stab` (b), `s01-stab`). -/
theorem deltaLoc_mul (t t' : ℤ_[p]ˣ) : deltaLoc p (t * t') = deltaLoc p t * deltaLoc p t' := by
  apply Units.ext
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [deltaLoc, Matrix.mul_apply, Fin.sum_univ_two]

/-- `δ_{t t'} = δ_t δ_{t'}` (`lem:s01-stab` (b), `s01-stab`). -/
theorem deltaElt_mul (t t' : ℤ_[p]ˣ) : deltaElt d p hp (t * t') = deltaElt d p hp t * deltaElt d p hp t' := by
  simp only [deltaElt, deltaLoc_mul, map_mul]

/-- `localComponent p (δ_t) = diag(1, t)` (`lem:s01-stab` (b), `s01-stab`). -/
theorem localComponent_deltaElt (t : ℤ_[p]ˣ) :
    localComponent d p hp (deltaElt d p hp t) = diagGL 1 (intUnit t) :=
  localComponent_localEmbedGL (hp := hp) (deltaLoc p t)

/-- The component at `p` of a conjugate of `u` by `localEmbedGL p g` (`lem:s01-stab` (b), `s01-stab`). -/
theorem localComponent_conj (g : GL (Fin 2) ℚ_[p]) (u : (BHat d.a d.b)ˣ) :
    localComponent d p hp (localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹) =
      g * localComponent d p hp u * g⁻¹ := by
  rw [map_mul, map_mul, map_inv, localComponent_localEmbedGL]

/-- Conjugation by `localEmbedGL p g` does not change the `p`-away part (`lem:s01-stab` (b), `s01-stab`). -/
theorem awayAt_conj (g : GL (Fin 2) ℚ_[p]) (u : (BHat d.a d.b)ˣ) :
    awayAt d p hp (localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹) = awayAt d p hp u := by
  have hcomm : awayAt d p hp u * localEmbedGL d p hp g = localEmbedGL d p hp g * awayAt d p hp u :=
    (commute_awayAt_localEmbedGL (hp := hp) u g).eq
  calc awayAt d p hp (localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹)
      = localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹ *
          localEmbedGL d p hp ((g * localComponent d p hp u * g⁻¹)⁻¹) := by
        simp only [awayAt, localComponent_conj]
    _ = localEmbedGL d p hp g * (u * localEmbedGL d p hp ((localComponent d p hp u)⁻¹)) *
          (localEmbedGL d p hp g)⁻¹ := by
        simp only [map_inv, map_mul]
        group
    _ = localEmbedGL d p hp g * awayAt d p hp u * (localEmbedGL d p hp g)⁻¹ := rfl
    _ = awayAt d p hp u := by rw [← hcomm, mul_inv_cancel_right]

variable {d p hp}

/-- `lem:s01-stab` (b) (`s01-stab`): if `g ∈ GL₂(ℚ_p)` normalises `K1 p s`, then `localEmbedGL p g`
normalises `U_s = Utower` (`p ∤ M`, `s ≥ 1`). -/
theorem localEmbedGL_conj_mem_Utower {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) {g : GL (Fin 2) ℚ_[p]}
    (hg : ∀ k ∈ K1 p s, g * k * g⁻¹ ∈ K1 p s) {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) :
    localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹ ∈ d.Utower M p s hN := by
  obtain ⟨hA, hK⟩ := (mem_Utower_iff_factor_at (hp := hp) hM hpM hs u).1 hu
  refine (mem_Utower_iff_factor_at (hp := hp) hM hpM hs _).2 ⟨?_, ?_⟩
  · change awayAt d p hp (localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹) ∈ _
    rw [awayAt_conj]
    exact hA
  · rw [localComponent_conj]
    exact hg _ hK

/-- `lem:s01-stab` (b) (`s01-stab`): `δ_t` normalises `U_s`. -/
theorem deltaElt_normalizes {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : ℤ_[p]ˣ) {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) :
    deltaElt d p hp t * u * (deltaElt d p hp t)⁻¹ ∈ d.Utower M p s hN :=
  localEmbedGL_conj_mem_Utower (g := deltaLoc p t) hM hpM hs (fun _ hk => diagOne_conj_mem_K1 t s hk) hu

/-- `lem:s01-stab` (b) (`s01-stab`): `δ_t⁻¹` normalises `U_s`. -/
theorem deltaElt_inv_normalizes {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (t : ℤ_[p]ˣ) {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) :
    (deltaElt d p hp t)⁻¹ * u * deltaElt d p hp t ∈ d.Utower M p s hN := by
  have h := localEmbedGL_conj_mem_Utower (hp := hp) hM hpM hs (g := (deltaLoc p t)⁻¹)
    (fun _ hk => by rw [inv_inv]; exact diagOne_inv_conj_mem_K1 t s hk) hu
  rw [map_inv, inv_inv] at h
  exact h

/-! #### `δ_t` at the generic levels `levelAt d N hN K` (`U_0(N)`, `U_1(N)`) -/

/-- `lem:s01-stab` (b), `def:s01-levels` (`s01-stab`): if `g ∈ GL₂(ℚ_p)` normalises the local condition
`K p (v_p N)` at a prime `p ∣ N`, then `localEmbedGL p g` normalises the generic level `levelAt d N hN K`. -/
theorem localEmbedGL_conj_mem_levelAt {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])}
    (hK : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ), K ℓ e ≤ GL2Zl ℓ) (hpN : p ∈ N.primeFactors)
    {g : GL (Fin 2) ℚ_[p]}
    (hg : ∀ k ∈ K p (N.factorization p), g * k * g⁻¹ ∈ K p (N.factorization p))
    {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.levelAt N hN K) :
    localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹ ∈ d.levelAt N hN K := by
  obtain ⟨hA, hKp⟩ := (mem_levelAt_iff_factor_at (hp := hp) hK hpN u).1 hu
  refine (mem_levelAt_iff_factor_at (hp := hp) hK hpN _).2 ⟨?_, ?_⟩
  · change awayAt d p hp (localEmbedGL d p hp g * u * (localEmbedGL d p hp g)⁻¹) ∈ _
    rw [awayAt_conj]
    exact hA
  · rw [localComponent_conj]
    exact hg _ hKp

/-- `def:s01-levels` (`s01-stab`): `localEmbedGL p k ∈ levelAt d N hN K` for `p ∣ N` and `k ∈ K p (v_p N)`. -/
theorem localEmbedGL_mem_levelAt {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])}
    (hK : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ), K ℓ e ≤ GL2Zl ℓ) (hpN : p ∈ N.primeFactors)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K p (N.factorization p)) :
    localEmbedGL d p hp k ∈ d.levelAt N hN K := by
  rw [mem_levelAt_iff_factor_at (hp := hp) hK hpN, localComponent_localEmbedGL, map_inv, mul_inv_cancel]
  exact ⟨one_mem _, hk⟩

/-- `def:s01-levels` (`s01-stab`): `localEmbedGL p k ∈ levelAt d N hN K` for a split `p ∤ N` and
`k ∈ GL₂(ℤ_p)`. -/
theorem localEmbedGL_mem_levelAt_of_notMem {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hpN : p ∉ N.primeFactors)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ GL2Zl p) :
    localEmbedGL d p hp k ∈ d.levelAt N hN K := by
  have h := isInvariantAt_levelAt (hp := hp) (hN := hN) (K := K) hpN 1 (one_mem _) k hk
  rwa [one_mul] at h

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): for a split `p ∤ N`, `δ_t ∈ levelAt d N hN K`
(so the diamond operator at such a `p` is the identity). -/
theorem deltaElt_mem_levelAt_of_notMem {N : ℕ} {hN : N.Coprime d.D}
    {K : (ℓ : ℕ) → [Fact ℓ.Prime] → ℕ → Subgroup (GL (Fin 2) ℚ_[ℓ])} (hpN : p ∉ N.primeFactors)
    (t : ℤ_[p]ˣ) : deltaElt d p hp t ∈ d.levelAt N hN K :=
  localEmbedGL_mem_levelAt_of_notMem hpN (K0_le_GL2Zl 0 (one_diag_mem_K0 t 0))

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): `δ_t ∈ U_0(N)` at every split `p` (`diag(1, t) ∈ K0 p e`);
so `δ_t` normalises `U_0(N)` and the diamond operator at `p` is the identity on `U_0(N)`. -/
theorem deltaElt_mem_U0 {N : ℕ} {hN : N.Coprime d.D} (t : ℤ_[p]ˣ) : deltaElt d p hp t ∈ d.U0 N hN := by
  by_cases hpN : p ∈ N.primeFactors
  · exact localEmbedGL_mem_levelAt (hp := hp) (K := fun ℓ _ e => K0 ℓ e) (fun _ _ e => K0_le_GL2Zl e) hpN
      (one_diag_mem_K0 t _)
  · exact deltaElt_mem_levelAt_of_notMem hpN t

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): `δ_t` normalises `U_0(N)`. -/
theorem deltaElt_normalizes_U0 {N : ℕ} {hN : N.Coprime d.D} (t : ℤ_[p]ˣ)
    {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.U0 N hN) :
    deltaElt d p hp t * u * (deltaElt d p hp t)⁻¹ ∈ d.U0 N hN :=
  mul_mem (mul_mem (deltaElt_mem_U0 t) hu) (inv_mem (deltaElt_mem_U0 t))

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): `δ_t⁻¹` normalises `U_0(N)`. -/
theorem deltaElt_inv_normalizes_U0 {N : ℕ} {hN : N.Coprime d.D} (t : ℤ_[p]ˣ)
    {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.U0 N hN) :
    (deltaElt d p hp t)⁻¹ * u * deltaElt d p hp t ∈ d.U0 N hN :=
  mul_mem (mul_mem (inv_mem (deltaElt_mem_U0 t)) hu) (deltaElt_mem_U0 t)

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): `δ_t` normalises `U_1(N)` at `p ∣ N`. -/
theorem deltaElt_normalizes_U1 {N : ℕ} {hN : N.Coprime d.D} (hpN : p ∈ N.primeFactors) (t : ℤ_[p]ˣ)
    {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.U1 N hN) :
    deltaElt d p hp t * u * (deltaElt d p hp t)⁻¹ ∈ d.U1 N hN :=
  localEmbedGL_conj_mem_levelAt (K := fun ℓ _ e => K1 ℓ e) (fun _ _ e => K1_le_GL2Zl e) hpN
    (g := deltaLoc p t) (fun _ hk => diagOne_conj_mem_K1 t _ hk) hu

/-- `lem:s01-stab` (b), `def:s01-hecke` (`s01-stab`): `δ_t⁻¹` normalises `U_1(N)` at `p ∣ N`. -/
theorem deltaElt_inv_normalizes_U1 {N : ℕ} {hN : N.Coprime d.D} (hpN : p ∈ N.primeFactors) (t : ℤ_[p]ˣ)
    {u : (BHat d.a d.b)ˣ} (hu : u ∈ d.U1 N hN) :
    (deltaElt d p hp t)⁻¹ * u * deltaElt d p hp t ∈ d.U1 N hN := by
  have h := localEmbedGL_conj_mem_levelAt (hp := hp) (K := fun ℓ _ e => K1 ℓ e)
    (fun _ _ e => K1_le_GL2Zl e) hpN (g := (deltaLoc p t)⁻¹)
    (fun _ hk => by rw [inv_inv]; exact diagOne_inv_conj_mem_K1 t _ hk) hu
  rw [map_inv, inv_inv] at h
  exact h

/-! #### Right translation on `X_B(U)` -/

section RightMul

variable {a b : ℤ}

/-- Right translation `[x] ↦ [x g]` on `X_B(U)` (well defined when `g` normalises `U`; `lem:s01-stab`
(b), `s01-stab`), through representatives. -/
noncomputable def rightMulXB (U : Subgroup (BHat a b)ˣ) (g : (BHat a b)ˣ) : XB U → XB U :=
  fun c => DoubleCoset.mk (globalUnits a b) U (Quotient.out c * g)

/-- `rightMulXB U g [x] = [x g]` if `g⁻¹ U g ⊆ U` (`lem:s01-stab` (b), `s01-stab`). -/
theorem rightMulXB_mk (U : Subgroup (BHat a b)ˣ) (g : (BHat a b)ˣ) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (x : (BHat a b)ˣ) :
    rightMulXB U g (DoubleCoset.mk (globalUnits a b) U x) = DoubleCoset.mk (globalUnits a b) U (x * g) := by
  obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits a b) U x
  simp only [rightMulXB]
  rw [DoubleCoset.eq]
  refine ⟨h⁻¹, inv_mem hh, g⁻¹ * k⁻¹ * g, hg _ (inv_mem hk), ?_⟩
  rw [he]
  group

/-- `rightMulXB` for `g'` undoes `rightMulXB` for `g` when `g g' = 1` (`lem:s01-stab` (b), `s01-stab`). -/
theorem rightMulXB_cancel (U : Subgroup (BHat a b)ˣ) (g g' : (BHat a b)ˣ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) (hg' : ∀ u ∈ U, g'⁻¹ * u * g' ∈ U) (h : g * g' = 1)
    (c : XB U) : rightMulXB U g' (rightMulXB U g c) = c := by
  induction c using Quotient.inductionOn' with
  | h y =>
    show rightMulXB U g' (rightMulXB U g (DoubleCoset.mk (globalUnits a b) U y)) =
      DoubleCoset.mk (globalUnits a b) U y
    rw [rightMulXB_mk U g hg, rightMulXB_mk U g' hg', mul_assoc, h, mul_one]

/-- The permutation `[x] ↦ [x g]` of `X_B(U)` for `g` normalising `U` (`lem:s01-stab` (b), `s01-stab`). -/
noncomputable def rightMulPerm (U : Subgroup (BHat a b)ˣ) (g : (BHat a b)ˣ)
    (h1 : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (h2 : ∀ u ∈ U, g⁻¹ * u * g ∈ U) : Equiv.Perm (XB U) where
  toFun := rightMulXB U g
  invFun := rightMulXB U g⁻¹
  left_inv := fun c => rightMulXB_cancel U g g⁻¹ h2
    (fun u hu => by rw [inv_inv]; exact h1 u hu) (mul_inv_cancel g) c
  right_inv := fun c => rightMulXB_cancel U g⁻¹ g (fun u hu => by rw [inv_inv]; exact h1 u hu) h2
    (inv_mul_cancel g) c

end RightMul

/-! #### The action of `ℤ_p^×` and freeness -/

/-- `lem:s01-stab` (b) (`s01-stab`): the action `[x] ↦ [x δ_t]` of `t ∈ ℤ_p^×` on `X_B(U_s)`,
`δ_t = ι_p⁻¹ diag(1, t)`. It factors through `Δ_s = ℤ_p^× / (1 + p^s ℤ_p)` (`diamondAct_mul`,
`diamondAct_eq_one`, `diamondAct_eq_of_dvd`). It is the permutation underlying the diamond operator at `p`:
`Brandt.diamond_apply_eq_diamondAct`. -/
noncomputable def diamondAct {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t : ℤ_[p]ˣ) : Equiv.Perm (XB (d.Utower M p s hN)) :=
  rightMulPerm _ (deltaElt d p hp t) (fun _ hu => deltaElt_normalizes hM hpM hs t hu)
    (fun _ hu => deltaElt_inv_normalizes hM hpM hs t hu)

/-- `diamondAct t [x] = [x δ_t]` (`lem:s01-stab` (b), `s01-stab`). -/
theorem diamondAct_mk {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t : ℤ_[p]ˣ) (x : (BHat d.a d.b)ˣ) :
    diamondAct (hp := hp) hM hpM hs t (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) (x * deltaElt d p hp t) :=
  rightMulXB_mk _ _ (fun _ hu => deltaElt_inv_normalizes hM hpM hs t hu) x

/-- `lem:s01-stab` (b) (`s01-stab`): `diamondAct` is a homomorphism `ℤ_p^× → Perm (X_B(U_s))`,
`⟨t t'⟩ = ⟨t⟩ ∘ ⟨t'⟩` (`ℤ_p^×` is commutative, so the order does not matter). -/
theorem diamondAct_mul {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t t' : ℤ_[p]ˣ) :
    diamondAct (hp := hp) (hN := hN) hM hpM hs (t * t') =
      diamondAct (hp := hp) hM hpM hs t * diamondAct (hp := hp) hM hpM hs t' := by
  refine Equiv.ext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  rw [Equiv.Perm.mul_apply, diamondAct_mk (hp := hp) hM hpM hs t' x,
    diamondAct_mk (hp := hp) hM hpM hs t (x * deltaElt d p hp t'),
    diamondAct_mk (hp := hp) hM hpM hs (t * t') x, mul_comm t t', deltaElt_mul, mul_assoc]

/-- `lem:s01-stab` (b) (`s01-stab`): for `t ≡ 1 mod p^s`, `δ_t ∈ U_s` (`diag(1, t) ∈ K1 p s`). -/
theorem deltaElt_mem_Utower {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1) :
    deltaElt d p hp t ∈ d.Utower M p s hN := by
  unfold deltaElt
  rw [mem_Utower_iff_factor_at (hp := hp) hM hpM hs, localComponent_localEmbedGL, map_inv,
    mul_inv_cancel]
  exact ⟨one_mem _, (one_diag_mem_K1_iff t s).2 ht⟩

/-- `lem:s01-stab` (b) (`s01-stab`): the action of `t ≡ 1 mod p^s` on `X_B(U_s)` is trivial, so `diamondAct`
factors through `Δ_s = ℤ_p^× / (1 + p^s ℤ_p)`. -/
theorem diamondAct_eq_one {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1) :
    diamondAct (hp := hp) (hN := hN) hM hpM hs t = 1 := by
  refine Equiv.ext fun c => ?_
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  rw [diamondAct_mk (hp := hp) hM hpM hs t x, Equiv.Perm.one_apply]
  exact DoubleCoset.eq.2 ⟨1, one_mem _, (deltaElt d p hp t)⁻¹,
    inv_mem (deltaElt_mem_Utower hM hpM hs t ht), by group⟩

/-- `lem:s01-stab` (b) (`s01-stab`): `diamondAct t` depends only on `t mod p^s`. -/
theorem diamondAct_eq_of_dvd {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (t t' : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ^ s ∣ ((t⁻¹ * t' : ℤ_[p]ˣ) : ℤ_[p]) - 1) :
    diamondAct (hp := hp) (hN := hN) hM hpM hs t = diamondAct (hp := hp) hM hpM hs t' := by
  have h := diamondAct_mul (hp := hp) (hN := hN) hM hpM hs t (t⁻¹ * t')
  rw [mul_inv_cancel_left, diamondAct_eq_one hM hpM hs _ ht, mul_one] at h
  exact h.symm

/-- `lem:s01-stab` (b) (`s01-stab`): for `t ≡ 1 mod p`, `δ_t ∈ U_1(p)`. -/
theorem deltaElt_mem_U1 (hpD : p.Coprime d.D) (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ∣ (t : ℤ_[p]) - 1) :
    deltaElt d p hp t ∈ d.U1 p hpD := by
  have hK : diagGL 1 (intUnit t) ∈ K1 p 1 := (one_diag_mem_K1_iff t 1).2 (by rwa [pow_one])
  have hf : p.factorization p = 1 := (Fact.out : p.Prime).factorization_self
  have hpf : p.primeFactors = {p} := (Fact.out : p.Prime).primeFactors
  refine DefiniteData.mem_U1_iff.2 ⟨?_, fun ℓ _ hℓ hD => ?_⟩
  · exact localEmbedGL_mem_Ohat (K0_le_GL2Zl 0 (one_diag_mem_K0 t 0))
  · rw [hpf, Finset.mem_singleton] at hℓ
    subst hℓ
    rw [hf, localComponent_deltaElt]
    exact hK

/-- `lem:s01-stab` (b′) (`s01-stab`): `Δ_s` acts freely on `X_B(U_s)`. If `t ≡ 1 mod p` and
`diamondAct t c = c` for some `c ∈ X_B(U_s)` (`p ≥ 5`, `p ∤ D M`, `s ≥ 1`), then `t ≡ 1 mod p^s`. -/
theorem diamondAct_free {M s : ℕ} {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) (h5 : 5 ≤ p) (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ∣ (t : ℤ_[p]) - 1)
    (c : XB (d.Utower M p s hN)) (hfix : diamondAct (hp := hp) hM hpM hs t c = c) :
    (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1 := by
  have hpr : p.Prime := Fact.out
  have hpD : p.Coprime d.D := (hpr.coprime_iff_not_dvd).2 hp
  have hUV : d.Utower M p s hN ≤ d.U1 p hpD := DefiniteData.Utower_le_U1p hs hM hpr.ne_zero hN hpD
  have hδV : deltaElt d p hp t ∈ d.U1 p hpD := deltaElt_mem_U1 hpD t ht
  induction c using Quotient.inductionOn' with
  | h x =>
    have hfix' : DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) (x * deltaElt d p hp t) =
        DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x := by
      rw [← diamondAct_mk (hp := hp) hM hpM hs t x]
      exact hfix
    obtain ⟨γ, hγ, u, hu, he⟩ := DoubleCoset.eq.1 hfix'
    obtain ⟨γ0, hγ0⟩ := (MonoidHom.mem_range).1
      (hγ : γ ∈ (Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom).range)
    have key : γ = x * (u⁻¹ * (deltaElt d p hp t)⁻¹) * x⁻¹ := by
      have h' : γ * (x * deltaElt d p hp t) * u = x := he.symm
      calc γ = γ * (x * deltaElt d p hp t) * u * u⁻¹ * (deltaElt d p hp t)⁻¹ * x⁻¹ := by group
        _ = x * u⁻¹ * (deltaElt d p hp t)⁻¹ * x⁻¹ := by rw [h']
        _ = _ := by group
    have hvV : u⁻¹ * (deltaElt d p hp t)⁻¹ ∈ d.U1 p hpD :=
      mul_mem (inv_mem (hUV hu)) (inv_mem hδV)
    have hmem : γ0 ∈ Gam (d.U1 p hpD) x := by
      simp only [Gam, GL2TF.Quat.classStabilizer, Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨_, hvV, ?_⟩
      have : x * (u⁻¹ * (deltaElt d p hp t)⁻¹) * x⁻¹ =
          Units.map (GL2TF.Quat.finEmbed d.a d.b).toMonoidHom γ0 := by
        rw [hγ0, ← key]
      exact this
    have hγ1 : γ = 1 := by
      have h0 : γ0 = 1 := by
        have := Gam_eq_bot_of_le_U1 d hpr h5 hpD le_rfl x
        rw [this] at hmem
        exact Subgroup.mem_bot.1 hmem
      rw [← hγ0, h0, map_one]
    have hone : u⁻¹ * (deltaElt d p hp t)⁻¹ = 1 := by
      calc u⁻¹ * (deltaElt d p hp t)⁻¹
          = x⁻¹ * (x * (u⁻¹ * (deltaElt d p hp t)⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [← key, hγ1]; group
    have hδu : deltaElt d p hp t * u = 1 := by
      calc deltaElt d p hp t * u = (u⁻¹ * (deltaElt d p hp t)⁻¹)⁻¹ := by group
        _ = 1 := by rw [hone, inv_one]
    have hδU : deltaElt d p hp t ∈ d.Utower M p s hN := by
      rw [eq_inv_of_mul_eq_one_left hδu]
      exact inv_mem hu
    have hK := ((mem_Utower_iff_factor_at (hp := hp) hM hpM hs _).1 hδU).2
    rw [localComponent_deltaElt] at hK
    exact (one_diag_mem_K1_iff t s).1 hK

end Delta

end Langlandscape.Quat
