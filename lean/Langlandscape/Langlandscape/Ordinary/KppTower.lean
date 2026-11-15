/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Adjoint
import Langlandscape.Brandt.Up
import Langlandscape.Local.HidaLocal
import Langlandscape.Quat.Stab

/-!
# The intermediate level `K'_s` and `U_p` at general levels (S04-L9)

`mathematics/chapters/s04/control.tex`, `lem:s04-hida` (tex label `s04-hida`), global form: part (a); part (b) in
its homological form only; part (c) only as the torsor statement on sets. See *Status* for the exact scope.

* `IsUpLevel d p hp U K`: the level `U` factors at `p` with `p`-component `K`, and `K` has the `ϖ_j` of
  `def:s01-NUp` as representatives of `K ϖ K / K` (`K = K1 p s`: `isUpLevel_of_K1`; `K = Kpp p s`:
  `isUpLevel_of_Kpp`, from S04-L6 `exists_varpi_conj`). Stable under `⊓` with levels invariant at `p`
  (`IsUpLevel.inf`), so it covers `U0q q (Utower …)` (`IsUpLevel.U0q`, `isUpLevel_U0q_Utower`).
* `UpAt U hU R` (homological, a `heckeTHom`) and `UpAtDual U hU R` (cohomological, a `heckeT`):
  `U_p = [U ϖ U]` with `UpAt_single : U_p [x] = ∑_j [x ϖ_j]`; at `Utower` they are the stage-1 `UpHom`, `Up`
  (`UpAt_Utower_eq`, `UpAtDual_Utower_eq`).
* `UtowerP d M p s hN hp` = `U'_s` (`U_1(M)` away from `p`, `Kpp p s` at `p`), `Utower (s+1) ≤ UtowerP ≤ Utower s`.
* `piP : X'_s → X_s`, `piPP : X_{s+1} → X'_s` and their pushforwards `piP_push`, `piPP_push`.
* `Up_comm`: `U_p` commutes with both pushforwards (`lem:s04-hida`(a)); general form `UpAt_comm_pushforward`.
* `Up_ker_push_eq_zero`: `U_p (ker π'_*) = 0` (`lem:s04-hida`(b), global Hida); general form
  `UpAt_ker_pushforward_eq_zero`.
* Torsor (`lem:s04-hida`(c), set-level): `piPP` is surjective (`piPP_surjective`), its fibres are the orbits of
  `t ∈ 1 + p^s ℤ_p` acting by `diamondAct` (`piPP_eq_iff`), and this action of `ker(Δ_{s+1} → Δ_s)` is free
  (`piPP_free`, from `diamondAct_free`; needs `p ≥ 5`).

Status: *formalized*, exactly the following: `lem:s04-hida`(a) (`UpAt_single`, `Up_comm`, `UpAt_comm_pushforward`);
(b) in its homological form `π'_* a = 0 → U_p a = 0` (`Up_ker_push_eq_zero`, `UpAt_ker_pushforward_eq_zero`);
(c) as the torsor statement on sets (`piPP_surjective`, `piPP_eq_iff`, `piPP_free`, the last for `p ≥ 5`).
**Not formalized here:** the cohomological half of (b) (`U_p(ℤ_p^{X'_s}) ⊆ π'^* ℤ_p^{X_s}`; `UpAtDual` has only
`UpAtDual_apply`, `UpAtDual_Utower_eq`), the two isomorphisms of (c) (`e π'_*` an isomorphism;
`ℤ_p[X_{s+1}] ⊗_{ℤ_p[Δ_{s+1}]} ℤ_p[Δ_s] ≅ ℤ_p[X'_s]`) and (d); these are S04-L10 (`Ordinary/Tower.lean`). No
`Hyp.*` hypotheses are used; the side conditions (`s ≥ 1`, `p ∤ M`, `p ≥ 5` for `piPP_free`) are explicit.
-/

open Pointwise
open Langlandscape.Local Langlandscape.Quat Langlandscape.Brandt

namespace Langlandscape.Ordinary

open scoped Classical

/-! ### Local facts at `p` (private) -/

section Local

variable {p : ℕ} [Fact p.Prime]

/-- `lem:s04-hida`(a) (`s04-hida`): membership in `Kpp p s = K1 p s ⊓ K0 p (s+1)`. -/
private theorem mem_Kpp_iff' {s : ℕ} {g : GL (Fin 2) ℚ_[p]} :
    g ∈ Kpp p s ↔ g ∈ K1 p s ∧ g ∈ K0 p (s + 1) := by
  exact Iff.rfl

/-- `lem:s04-hida`(a) (`s04-hida`): `Kpp p s ≤ K1 p s`. -/
private theorem Kpp_le_K1' {s : ℕ} : Kpp p s ≤ K1 p s := fun _ h => (mem_Kpp_iff'.1 h).1

/-- `lem:s04-hida`(a) (`s04-hida`): `n(j) = !![1, j; 0, 1] ∈ Kpp p s`. -/
private theorem unipUpper_mem_Kpp {s : ℕ} (j : Fin p) : unipUpper p j ∈ Kpp p s :=
  mem_Kpp_iff'.2 ⟨unipUpper_mem j,
    mem_K0_of_entries 1 ((j : ℕ) : ℤ_[p]) 0 1 (by simp [unipUpper]) (by simp) (dvd_zero _)⟩

/-- `lem:s04-hida`(b) (`s04-hida`): the S04-L6 export `exists_varpi_conj`, in the form used here. -/
private theorem exists_varpi_conj' {s : ℕ} (hs : 1 ≤ s) (u : GL (Fin 2) ℚ_[p]) (hu : u ∈ K1 p s)
    (j : Fin p) : ∃ i : Fin p, ∃ uj ∈ Kpp p s, u * varpi p j = varpi p i * uj := by
  exact exists_varpi_conj hs u hu j

/-- `lem:s04-hida`(a) (`s04-hida`): every `k ϖ`, `k ∈ Kpp p s`, lies in some `ϖ_j Kpp p s`. -/
private theorem exists_varpi_Kpp {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ Kpp p s) :
    ∃ j : Fin p, (varpi p j)⁻¹ * (k * varpiDiag p) ∈ Kpp p s := by
  let j0 : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  have hk' : k * (unipUpper p j0)⁻¹ ∈ K1 p s :=
    Kpp_le_K1' (mul_mem hk (inv_mem (unipUpper_mem_Kpp j0)))
  obtain ⟨i, uj, huj, he⟩ := exists_varpi_conj' hs _ hk' j0
  refine ⟨i, ?_⟩
  have h : k * varpiDiag p = varpi p i * uj := by
    rw [← he, varpi_eq, mul_assoc, inv_mul_cancel_left]
  rw [h, inv_mul_cancel_left]
  exact huj

/-- `def:s01-NUp`, `lem:s04-hida`(a) (`s04-hida`): the cosets `ϖ_j GL₂(ℤ_p)` are pairwise distinct. -/
private theorem varpi_inv_mul_not_mem_GL2Zl {j j' : Fin p} (hjj' : j ≠ j') :
    (varpi p j)⁻¹ * varpi p j' ∉ GL2Zl p := fun h =>
  varpi_inv_mul_not_mem (s := 0) hjj' (by rw [K1_zero]; exact h)

/-- `lem:s04-hida`(c) (`s04-hida`): for `k ∈ Kpp p s` (`s ≥ 1`) with lower right entry `t ≡ 1 mod p^s`,
`diag(1, t)⁻¹ k ∈ K1 p (s+1)`; this is the map `Kpp p s → ker(Δ_{s+1} → Δ_s)` with kernel `K1 p (s+1)`. -/
private theorem exists_diag_inv_mul_mem_K1_succ {s : ℕ} (hs : 1 ≤ s) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ Kpp p s) :
    ∃ t : ℤ_[p]ˣ, (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1 ∧
      (diagGL 1 (intUnit t))⁻¹ * k ∈ K1 p (s + 1) := by
  obtain ⟨hk1, hk0⟩ := mem_Kpp_iff'.1 hk
  obtain ⟨a, b, c, dd, hM, -, -, hd⟩ := mem_K1_iff_exists.1 hk1
  obtain ⟨_, _, c', _, hM', -, hc'⟩ := mem_K0_iff_exists.1 hk0
  have hcc : c = c' := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ_[p] => A 1 0) (hM.symm.trans hM')
    apply Subtype.ext
    simpa using h
  have hdU : IsUnit dd := by
    rw [isUnit_iff_not_dvd]
    intro h
    have h1 : (p : ℤ_[p]) ∣ dd - 1 := (dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans hd
    have h2 := dvd_sub h h1
    rw [sub_sub_cancel] at h2
    exact (isUnit_iff_not_dvd (1 : ℤ_[p])).1 isUnit_one h2
  obtain ⟨t, ht⟩ : ∃ t : ℤ_[p]ˣ, (t : ℤ_[p]) = dd := ⟨hdU.unit, hdU.unit_spec⟩
  subst ht
  refine ⟨t, hd, ?_⟩
  obtain ⟨w, hts⟩ : ∃ w : ℤ_[p], (t : ℤ_[p]) * w = 1 := ⟨_, t.mul_inv⟩
  have hts' : ((t : ℤ_[p]) : ℚ_[p]) * (w : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hts
    simpa using this
  have H : Units.val (diagGL 1 (intUnit t)) *
      !![(a : ℚ_[p]), (b : ℚ_[p]); ((w * c : ℤ_[p]) : ℚ_[p]),
        ((1 : ℤ_[p]) : ℚ_[p])] = Units.val k := by
    rw [diagGL_val, hM, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (try simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_one, coe_intUnit,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]) <;>
      push_cast <;>
      first
        | ring1
        | linear_combination (c : ℚ_[p]) * hts'
  have hdet : ‖(Units.val (diagGL 1 (intUnit t))).det‖ = ‖(Units.val k).det‖ := by
    rw [(mem_GL2Zl_iff.1 (K0_le_GL2Zl 0 (one_diag_mem_K0 t 0))).2,
      (mem_GL2Zl_iff.1 (K1_le_GL2Zl s hk1)).2]
  have hc : (p : ℤ_[p]) ^ (s + 1) ∣ w * c := by
    rw [hcc]
    exact hc'.mul_left _
  have hd1 : (p : ℤ_[p]) ^ (s + 1) ∣ (1 : ℤ_[p]) - 1 := by
    rw [sub_self]
    exact dvd_zero _
  exact inv_mul_mem_K1 a b (w * c) 1 H hdet hc hd1

end Local

/-! ### Levels with `U_p` given by the `ϖ_j` -/

section Generic

variable {d : DefiniteData} {p : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

/-- `lem:s04-hida`(a), `def:s01-NUp` (`s04-hida`): the level `U` has `p`-component `K` (`u ∈ U` iff its
`p`-away part lies in `U` and `u_p ∈ K`), `K ≤ GL₂(ℤ_p)` contains the `n(j) = !![1, j; 0, 1]`, and every `k ϖ`,
`k ∈ K`, lies in some `ϖ_j K`. Then `U ϖ U = ⊔_j ϖ_j U` with the `ϖ_j` of `def:s01-NUp`. Instances:
`K = K1 p s` (`isUpLevel_of_K1`), `K = Kpp p s` (`isUpLevel_of_Kpp`). -/
structure IsUpLevel (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (K : Subgroup (GL (Fin 2) ℚ_[p])) : Prop where
  le_GL2Zl : K ≤ GL2Zl p
  unip_mem : ∀ j : Fin p, unipUpper p j ∈ K
  exists_varpi : ∀ k ∈ K, ∃ j : Fin p, (varpi p j)⁻¹ * (k * varpiDiag p) ∈ K
  factor : ∀ u : (GL2TF.Quat.BHat d.a d.b)ˣ,
    u ∈ U ↔ awayAt d p hp u ∈ U ∧ localComponent d p hp u ∈ K

/-- `lem:s04-hida`(a) (`s04-hida`): a level with `p`-component `K1 p s` (`s ≥ 1`) is an `IsUpLevel`. -/
theorem isUpLevel_of_K1 {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ} (hs : 1 ≤ s)
    (hfac : ∀ u : (GL2TF.Quat.BHat d.a d.b)ˣ,
      u ∈ U ↔ awayAt d p hp u ∈ U ∧ localComponent d p hp u ∈ K1 p s) :
    IsUpLevel d p hp U (K1 p s) where
  le_GL2Zl := K1_le_GL2Zl s
  unip_mem j := Langlandscape.Local.unipUpper_mem j
  exists_varpi k hk := by
    obtain ⟨j, -, hj⟩ := exists_varpi_inv_mul hs (K1_le_K0 s hk)
    exact ⟨j, hj hk⟩
  factor := hfac

/-- `lem:s04-hida`(a) (`s04-hida`): a level with `p`-component `Kpp p s` (`s ≥ 1`) is an `IsUpLevel`
(the same `ϖ_j`, from S04-L6 `exists_varpi_conj`). -/
theorem isUpLevel_of_Kpp {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ} (hs : 1 ≤ s)
    (hfac : ∀ u : (GL2TF.Quat.BHat d.a d.b)ˣ,
      u ∈ U ↔ awayAt d p hp u ∈ U ∧ localComponent d p hp u ∈ Kpp p s) :
    IsUpLevel d p hp U (Kpp p s) where
  le_GL2Zl := fun _ h => K1_le_GL2Zl s (Kpp_le_K1' h)
  unip_mem j := unipUpper_mem_Kpp j
  exists_varpi _ hk := exists_varpi_Kpp hs hk
  factor := hfac

namespace IsUpLevel

variable {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K : Subgroup (GL (Fin 2) ℚ_[p])}

/-- `lem:s04-hida`(a) (`s04-hida`): `localEmbedGL p (K) ⊆ U`. -/
theorem localEmbedGL_mem (hU : IsUpLevel d p hp U K) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ K) :
    localEmbedGL d p hp k ∈ U := by
  rw [hU.factor, localComponent_localEmbedGL]
  refine ⟨?_, hk⟩
  rw [awayAt, localComponent_localEmbedGL, map_inv, mul_inv_cancel]
  exact one_mem _

/-- `lem:s04-hida`(a) (`s04-hida`): `U ⊓ V` has `p`-component `K` if `U` does and `V` is invariant at `p`;
e.g. `V = U_0(q)`, `q ≠ p`. -/
theorem inf (hU : IsUpLevel d p hp U K) {V : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hV : IsInvariantAt d p hp V) : IsUpLevel d p hp (U ⊓ V) K where
  le_GL2Zl := hU.le_GL2Zl
  unip_mem := hU.unip_mem
  exists_varpi := hU.exists_varpi
  factor u := by
    constructor
    · rintro ⟨hu, hv⟩
      have hf := (hU.factor u).1 hu
      exact ⟨⟨hf.1, hV u hv _ (inv_mem (hU.le_GL2Zl hf.2))⟩, hf.2⟩
    · rintro ⟨⟨ha, hav⟩, hk⟩
      refine ⟨(hU.factor u).2 ⟨ha, hk⟩, ?_⟩
      have h := hV _ hav _ (hU.le_GL2Zl hk)
      rwa [awayAt_mul_localEmbedGL] at h

/-- `lem:s04-hida`(a) (`s04-hida`): `U_0(q) U` has the same `p`-component as `U` (`p ∤ q`). -/
theorem U0q (hU : IsUpLevel d p hp U K) {q : ℕ} (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors) :
    IsUpLevel d p hp (d.U0q q hq U) K :=
  hU.inf (V := d.U0 q hq) (isInvariantAt_levelAt (K := fun ℓ _ e => K0 ℓ e) hpq)

/-- `def:s01-NUp`, `lem:s04-hida`(a) (`s04-hida`): each `ϖ_j` (placed at `p`) lies in `U ϖ U`. -/
theorem varpi_mem_dcSet (hU : IsUpLevel d p hp U K) (j : Fin p) :
    localEmbedGL d p hp (varpi p j) ∈ dcSet U (localEmbedGL d p hp (varpiDiag p)) :=
  (mem_dcSet _ _).2 ⟨localEmbedGL d p hp (unipUpper p j), hU.localEmbedGL_mem (hU.unip_mem j), 1,
    one_mem _, by rw [mul_one, varpi_eq, map_mul]⟩

/-- `def:s01-NUp`, `lem:s04-hida`(a) (`s04-hida`): every `y ∈ U ϖ U` lies in some `ϖ_j U`. -/
theorem exists_varpi_inv_mul_mem (hU : IsUpLevel d p hp U K) {y : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hy : y ∈ dcSet U (localEmbedGL d p hp (varpiDiag p))) :
    ∃ j : Fin p, (localEmbedGL d p hp (varpi p j))⁻¹ * y ∈ U := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_dcSet _ _).1 hy
  have hf := (hU.factor u).1 hu
  obtain ⟨j, hj⟩ := hU.exists_varpi _ hf.2
  refine ⟨j, ?_⟩
  have hc : awayAt d p hp u * (localEmbedGL d p hp (varpi p j))⁻¹ =
      (localEmbedGL d p hp (varpi p j))⁻¹ * awayAt d p hp u :=
    (commute_awayAt_localEmbedGL (hp := hp) u (varpi p j)).inv_right.eq
  have e : (localEmbedGL d p hp (varpi p j))⁻¹ * (u * localEmbedGL d p hp (varpiDiag p) * v) =
      awayAt d p hp u * localEmbedGL d p hp
        ((varpi p j)⁻¹ * (localComponent d p hp u * varpiDiag p)) * v := by
    calc (localEmbedGL d p hp (varpi p j))⁻¹ * (u * localEmbedGL d p hp (varpiDiag p) * v)
        = (localEmbedGL d p hp (varpi p j))⁻¹ * (awayAt d p hp u *
            localEmbedGL d p hp (localComponent d p hp u) * localEmbedGL d p hp (varpiDiag p) * v) := by
          rw [awayAt_mul_localEmbedGL]
      _ = ((localEmbedGL d p hp (varpi p j))⁻¹ * awayAt d p hp u) *
            (localEmbedGL d p hp (localComponent d p hp u) * localEmbedGL d p hp (varpiDiag p)) * v := by
          group
      _ = (awayAt d p hp u * (localEmbedGL d p hp (varpi p j))⁻¹) *
            (localEmbedGL d p hp (localComponent d p hp u) * localEmbedGL d p hp (varpiDiag p)) * v := by
          rw [hc]
      _ = awayAt d p hp u * localEmbedGL d p hp
            ((varpi p j)⁻¹ * (localComponent d p hp u * varpiDiag p)) * v := by
          simp only [map_mul, map_inv, mul_assoc]
  rw [e]
  exact mul_mem (mul_mem hf.1 (hU.localEmbedGL_mem hj)) hv

/-- `def:s01-NUp`, `lem:s04-hida`(a) (`s04-hida`): the cosets `ϖ_j U` are pairwise distinct. -/
theorem varpi_cosets_injective (hU : IsUpLevel d p hp U K) {j j' : Fin p}
    (h : (QuotientGroup.mk (localEmbedGL d p hp (varpi p j)) : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ U) =
      QuotientGroup.mk (localEmbedGL d p hp (varpi p j'))) : j = j' := by
  by_contra hne
  rw [QuotientGroup.eq, ← map_inv, ← map_mul] at h
  have h2 := ((hU.factor _).1 h).2
  rw [localComponent_localEmbedGL] at h2
  exact varpi_inv_mul_not_mem_GL2Zl hne (hU.le_GL2Zl h2)

/-- `def:s01-NUp`, `lem:s04-hida`(a) (`s04-hida`): `[U : U ∩ ϖ U ϖ⁻¹] < ∞`, so `U_p = [U ϖ U]` is defined. -/
theorem relIndex_ne_zero (hU : IsUpLevel d p hp U K) :
    (U ⊓ conjSub U (localEmbedGL d p hp (varpiDiag p))).relIndex U ≠ 0 := by
  have hcov : ∀ u : ↥U, ∃ j : Fin p,
      (localEmbedGL d p hp (varpi p j))⁻¹ *
        ((u : (GL2TF.Quat.BHat d.a d.b)ˣ) * localEmbedGL d p hp (varpiDiag p)) ∈ U :=
    fun u => hU.exists_varpi_inv_mul_mem
      ((mem_dcSet _ _).2 ⟨u, u.2, 1, one_mem _, by rw [mul_one]⟩)
  choose F hF using hcov
  have hfin : Finite (↥U ⧸ (U ⊓ conjSub U (localEmbedGL d p hp (varpiDiag p))).subgroupOf U) := by
    refine Finite.of_injective (β := Fin p) (fun q => F (Quotient.out q)) ?_
    intro q q' hqq'
    have hqq'' : F (Quotient.out q) = F (Quotient.out q') := hqq'
    have h1 := hF (Quotient.out q)
    have h2 := hF (Quotient.out q')
    rw [hqq''] at h1
    have h3 := conj_inv_mul_mem_of_inv_mul_mem h1 h2
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (Quotient.out q).2) (Quotient.out q').2, ?_⟩
    exact (mem_conjSub _ _).2 h3
  exact Subgroup.index_ne_zero_of_finite (hH := hfin)

end IsUpLevel

/-- `lem:s04-hida`(a), `def:s01-NUp` (`s04-hida`): the cohomological `U_p = [U ϖ U]` on `R^{X_B(U)}` at a level
`U` with `p`-component `K1 p s` or `Kpp p s` (`IsUpLevel`); normalisation `N_{U_p}`. -/
noncomputable def UpAtDual (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) {K : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsUpLevel d p hp U K) (R : Type*) [CommRing R] : ZXdual U R →ₗ[R] ZXdual U R :=
  heckeT U (localEmbedGL d p hp (varpiDiag p)) R hU.relIndex_ne_zero

/-- `lem:s04-hida`(a), `def:s01-NUp` (`s04-hida`): the homological `U_p` on `R[X_B(U)]` (a `heckeTHom`),
`[x] ↦ ∑_j [x ϖ_j]` (`UpAt_single`), at a level `U` with `p`-component `K1 p s` or `Kpp p s` (`IsUpLevel`);
covers `Utower`, `UtowerP` and `U0q q (Utower …)`. -/
noncomputable def UpAt (U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) {K : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsUpLevel d p hp U K) (R : Type*) [CommRing R] [Finite (XB U)] : ZX U R →ₗ[R] ZX U R :=
  heckeTHom U (localEmbedGL d p hp (varpiDiag p)) R hU.relIndex_ne_zero

variable {R : Type*} [CommRing R]

/-- `lem:s04-hida`(a) (`s04-hida`): `(U_p f)[x] = ∑_{j < p} f[x ϖ_j]`. -/
theorem UpAtDual_apply {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsUpLevel d p hp U K) (f : ZXdual U R) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    UpAtDual U hU R f (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      ∑ j : Fin p, f (DoubleCoset.mk (globalUnits d.a d.b) U (x * localEmbedGL d p hp (varpi p j))) := by
  have hS : ∀ y ∈ Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j)),
      y ∈ dcSet U (localEmbedGL d p hp (varpiDiag p)) := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact hU.varpi_mem_dcSet j
  have hcov : ∀ y ∈ dcSet U (localEmbedGL d p hp (varpiDiag p)),
      ∃ t ∈ Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j)),
        (QuotientGroup.mk y : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ U) = QuotientGroup.mk t := by
    intro y hy
    obtain ⟨j, hj⟩ := hU.exists_varpi_inv_mul_mem hy
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ j), (QuotientGroup.eq.2 hj).symm⟩
  have hinj : Set.InjOn
      (QuotientGroup.mk : (GL2TF.Quat.BHat d.a d.b)ˣ → (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ U)
      ↑(Finset.univ.image (fun j : Fin p => localEmbedGL d p hp (varpi p j))) := by
    intro y hy y' hy' hyy'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy')
    rw [hU.varpi_cosets_injective hyy']
  have hinj' : Set.InjOn (fun j : Fin p => localEmbedGL d p hp (varpi p j))
      ↑(Finset.univ : Finset (Fin p)) :=
    fun j _ j' _ hjj' => hU.varpi_cosets_injective
      (congrArg (fun z => (QuotientGroup.mk z : (GL2TF.Quat.BHat d.a d.b)ˣ ⧸ U)) hjj')
  rw [UpAtDual, heckeT_apply_reps _ _ R _ _ hS hcov hinj f x]
  exact Finset.sum_image hinj'

/-- `lem:s04-hida`(a) (`s04-hida`): `U_p [x] = ∑_{j < p} [x ϖ_j]` on `R[X_B(U)]`. -/
theorem UpAt_single {U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {K : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsUpLevel d p hp U K) [Finite (XB U)] (x : (GL2TF.Quat.BHat d.a d.b)ˣ) (r : R) :
    UpAt U hU R (Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) U x) r) =
      ∑ j : Fin p, Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) U
        (x * localEmbedGL d p hp (varpi p j))) r := by
  ext c'
  have h := heckeTHom_single_apply U (localEmbedGL d p hp (varpiDiag p)) R hU.relIndex_ne_zero
    (DoubleCoset.mk (globalUnits d.a d.b) U x) c' r
  have h2 : heckeT U (localEmbedGL d p hp (varpiDiag p)) R hU.relIndex_ne_zero (Pi.single c' (1 : R))
        (DoubleCoset.mk (globalUnits d.a d.b) U x) =
      ∑ j : Fin p, (Pi.single c' (1 : R) : ZXdual U R)
        (DoubleCoset.mk (globalUnits d.a d.b) U (x * localEmbedGL d p hp (varpi p j))) :=
    UpAtDual_apply (R := R) hU (Pi.single c' (1 : R)) x
  rw [UpAt, h, h2, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : DoubleCoset.mk (globalUnits d.a d.b) U (x * localEmbedGL d p hp (varpi p j)) = c'
  · simp [hc]
  · simp [hc]

/-- `prop:s01-adjoint`(c), `lem:s04-hida` (`s04-hida`): for `U' ≤ U` the projection `X_B(U') → X_B(U)` is onto. -/
theorem levelMap_surjective {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hle : U' ≤ U) :
    Function.Surjective (levelMap U' U) := fun c => by
  refine ⟨DoubleCoset.mk (globalUnits d.a d.b) U' (Quotient.out c), ?_⟩
  rw [levelMap_mk hle]
  exact DoubleCoset.out_eq' c

/-- `prop:s01-adjoint`(c), `lem:s04-hida` (`s04-hida`): `X_B(U')` finite and `U' ≤ U` give `X_B(U)` finite
(the projection is onto). -/
theorem finite_XB_of_le {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} (hle : U' ≤ U) [Finite (XB U')] :
    Finite (XB U) :=
  Finite.of_surjective (levelMap U' U) (levelMap_surjective hle)

/-- `lem:s04-hida`(a) (`s04-hida`): `U_p` commutes with the pushforward `π_* : R[X_B(U')] → R[X_B(U)]` for
`U' ≤ U` both `IsUpLevel` (literally the same formula `[x] ↦ ∑_j [x ϖ_j]` at both levels). -/
theorem UpAt_comm_pushforward {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ}
    {K' K : Subgroup (GL (Fin 2) ℚ_[p])} (hU' : IsUpLevel d p hp U' K') (hU : IsUpLevel d p hp U K)
    (hle : U' ≤ U) [Finite (XB U')] [Finite (XB U)] :
    pushforward U' U R ∘ₗ UpAt U' hU' R = UpAt U hU R ∘ₗ pushforward U' U R := by
  apply Finsupp.lhom_ext
  intro c r
  rw [← DoubleCoset.out_eq' c]
  simp only [LinearMap.comp_apply, UpAt_single, map_sum, pushforward_single, levelMap_mk hle]

/-! #### Hida's lemma (b), general form -/

/-- `lem:s04-hida`(b) (`s04-hida`): global form of `exists_varpi_conj`: for `u ∈ U` (`p`-component `K1 p s`)
and each `j` there are `i` and `w ∈ U'` (`p`-component `Kpp p s`, same away part) with `u ϖ_j = ϖ_i w`. -/
private theorem exists_varpi_conj_global {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ}
    (hs : 1 ≤ s) (hU' : IsUpLevel d p hp U' (Kpp p s)) (hU : IsUpLevel d p hp U (K1 p s))
    (haway : ∀ u ∈ U, awayAt d p hp u ∈ U') {u : (GL2TF.Quat.BHat d.a d.b)ˣ} (hu : u ∈ U) (j : Fin p) :
    ∃ i : Fin p, ∃ w ∈ U',
      u * localEmbedGL d p hp (varpi p j) = localEmbedGL d p hp (varpi p i) * w := by
  have hf := (hU.factor u).1 hu
  obtain ⟨i, k, hk, he⟩ := exists_varpi_conj' hs _ hf.2 j
  refine ⟨i, awayAt d p hp u * localEmbedGL d p hp k,
    mul_mem (haway u hu) (hU'.localEmbedGL_mem hk), ?_⟩
  have hc : awayAt d p hp u * localEmbedGL d p hp (varpi p i) =
      localEmbedGL d p hp (varpi p i) * awayAt d p hp u :=
    (commute_awayAt_localEmbedGL (hp := hp) u (varpi p i)).eq
  calc u * localEmbedGL d p hp (varpi p j)
      = awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u) *
          localEmbedGL d p hp (varpi p j) := by rw [awayAt_mul_localEmbedGL]
    _ = awayAt d p hp u * localEmbedGL d p hp (localComponent d p hp u * varpi p j) := by
          rw [map_mul (localEmbedGL d p hp), mul_assoc]
    _ = awayAt d p hp u * (localEmbedGL d p hp (varpi p i) * localEmbedGL d p hp k) := by
          rw [he, map_mul]
    _ = localEmbedGL d p hp (varpi p i) * (awayAt d p hp u * localEmbedGL d p hp k) := by
          rw [← mul_assoc (awayAt d p hp u), hc, mul_assoc]

/-- `lem:s04-hida`(b) (`s04-hida`): the map `R[X_B(U)] → R[X_B(U')]` on generators, `c ↦ ∑_j [x_c ϖ_j]'`
(`x_c` a representative of `c`); `U_p = Φ ∘ π_*` at the level `U'` (`UpAt_eq_hidaLift_comp`). -/
private noncomputable def hidaLift (d : DefiniteData) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ) (R : Type*) [CommRing R] (c : XB U) : ZX U' R :=
  ∑ j : Fin p, Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) U'
    (Quotient.out c * localEmbedGL d p hp (varpi p j))) (1 : R)

/-- `lem:s04-hida`(b) (`s04-hida`): `hidaLift [y] = ∑_j [y ϖ_j]'`, independent of the representative `y`
(the bijection `j ↦ i(j)` of `exists_varpi_conj`). -/
private theorem hidaLift_mk {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ}
    (hs : 1 ≤ s) (hU' : IsUpLevel d p hp U' (Kpp p s)) (hU : IsUpLevel d p hp U (K1 p s))
    (hle : U' ≤ U) (haway : ∀ u ∈ U, awayAt d p hp u ∈ U') (y : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    hidaLift d p hp U' U R (DoubleCoset.mk (globalUnits d.a d.b) U y) =
      ∑ j : Fin p, Finsupp.single (DoubleCoset.mk (globalUnits d.a d.b) U'
        (y * localEmbedGL d p hp (varpi p j))) (1 : R) := by
  obtain ⟨γ, hγ, u, hu, he⟩ := DoubleCoset.mk_out_eq_mul (globalUnits d.a d.b) U y
  choose ii ww hww hj using fun j => exists_varpi_conj_global hs hU' hU haway hu j
  have hinj : Function.Injective ii := by
    intro j j' hjj'
    apply hU.varpi_cosets_injective
    rw [QuotientGroup.eq]
    have e1 : localEmbedGL d p hp (varpi p j) =
        u⁻¹ * (localEmbedGL d p hp (varpi p (ii j)) * ww j) := by
      rw [← hj j, inv_mul_cancel_left]
    have e2 : localEmbedGL d p hp (varpi p j') =
        u⁻¹ * (localEmbedGL d p hp (varpi p (ii j)) * ww j') := by
      rw [hjj', ← hj j', inv_mul_cancel_left]
    have e3 : (localEmbedGL d p hp (varpi p j))⁻¹ * localEmbedGL d p hp (varpi p j') =
        (ww j)⁻¹ * ww j' := by
      rw [e1, e2]
      group
    rw [e3]
    exact hle (mul_mem (inv_mem (hww j)) (hww j'))
  have hbij : Function.Bijective ii := Finite.injective_iff_bijective.1 hinj
  have hterm : ∀ j : Fin p, DoubleCoset.mk (globalUnits d.a d.b) U'
      (γ * y * u * localEmbedGL d p hp (varpi p j)) =
      DoubleCoset.mk (globalUnits d.a d.b) U' (y * localEmbedGL d p hp (varpi p (ii j))) := by
    intro j
    apply Eq.symm
    apply DoubleCoset.eq.2
    refine ⟨γ, hγ, ww j, hww j, ?_⟩
    calc γ * y * u * localEmbedGL d p hp (varpi p j)
        = γ * y * (u * localEmbedGL d p hp (varpi p j)) := by group
      _ = γ * y * (localEmbedGL d p hp (varpi p (ii j)) * ww j) := by rw [hj j]
      _ = γ * (y * localEmbedGL d p hp (varpi p (ii j))) * ww j := by group
  unfold hidaLift
  rw [he]
  simp only [hterm]
  exact Fintype.sum_bijective ii hbij _ _ (fun _ => rfl)

/-- `lem:s04-hida`(b) (`s04-hida`): at the level `U'` (`p`-component `Kpp p s`), `U_p` factors through
`π_* : R[X_B(U')] → R[X_B(U)]` (`p`-component `K1 p s`, same away part). -/
private theorem UpAt_eq_hidaLift_comp {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ}
    (hs : 1 ≤ s) (hU' : IsUpLevel d p hp U' (Kpp p s)) (hU : IsUpLevel d p hp U (K1 p s))
    (hle : U' ≤ U) (haway : ∀ u ∈ U, awayAt d p hp u ∈ U') [Finite (XB U')] [Finite (XB U)] :
    UpAt U' hU' R = Finsupp.linearCombination R (hidaLift d p hp U' U R) ∘ₗ pushforward U' U R := by
  apply Finsupp.lhom_ext
  intro c r
  rw [← DoubleCoset.out_eq' c]
  rw [UpAt_single, LinearMap.comp_apply, pushforward_single, levelMap_mk hle,
    Finsupp.linearCombination_single, hidaLift_mk hs hU' hU hle haway, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `lem:s04-hida`(b) (`s04-hida`), general form: if `U'` has `p`-component `Kpp p s`, `U ≥ U'` has
`p`-component `K1 p s` and the same away part, then `U_p (ker π_*) = 0` on `R[X_B(U')]`. -/
theorem UpAt_ker_pushforward_eq_zero {U' U : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ} {s : ℕ}
    (hs : 1 ≤ s) (hU' : IsUpLevel d p hp U' (Kpp p s)) (hU : IsUpLevel d p hp U (K1 p s))
    (hle : U' ≤ U) (haway : ∀ u ∈ U, awayAt d p hp u ∈ U') [Finite (XB U')] [Finite (XB U)]
    (a : ZX U' R) (ha : pushforward U' U R a = 0) : UpAt U' hU' R a = 0 := by
  rw [UpAt_eq_hidaLift_comp hs hU' hU hle haway, LinearMap.comp_apply, ha, map_zero]

end Generic

/-! ### The tower `X_{s+1} → X'_s → X_s` -/

section Tower

variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hp : ¬ p ∣ d.D}

variable (d M p s) in
/-- `lem:s04-hida` (`s04-hida`): the level `U'_s = U^{(p)} Kpp p s`, i.e. `U_1(M p^s) ∩ {u_p ∈ K0 p (s+1)}`
(`U_1(M)` away from `p`, `Kpp p s = K1 p s ⊓ K0 p (s+1)` at `p`); `X'_s = X_B(U'_s)`. -/
noncomputable def UtowerP (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) :
    Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ :=
  d.Utower M p s hN ⊓ (K0 p (s + 1)).comap (localComponent d p hp)

/-- `lem:s04-hida` (`s04-hida`): membership in `U'_s`. -/
theorem mem_UtowerP_iff {hN : (M * p ^ s).Coprime d.D} {u : (GL2TF.Quat.BHat d.a d.b)ˣ} :
    u ∈ UtowerP d M p s hN hp ↔ u ∈ d.Utower M p s hN ∧ localComponent d p hp u ∈ K0 p (s + 1) :=
  Iff.rfl

/-- `lem:s04-hida` (`s04-hida`): `U'_s ≤ U_s`. -/
theorem UtowerP_le_Utower (hN : (M * p ^ s).Coprime d.D) :
    UtowerP d M p s hN hp ≤ d.Utower M p s hN := inf_le_left

/-- `lem:s04-hida`(c) (`s04-hida`): `U_{s+1} ≤ U'_s` (`K1 p (s+1) ≤ Kpp p s`). -/
theorem Utower_succ_le_UtowerP (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) : d.Utower M p (s + 1) hN' ≤ UtowerP d M p s hN hp := fun u hu =>
  mem_UtowerP_iff.2 ⟨Utower_succ_le hN hN' hM hu,
    K1_le_K0 _ ((mem_Utower_iff_factor_at (hp := hp) hM hpM (Nat.le_add_left 1 s) u).1 hu).2⟩

/-- `lem:s04-hida` (`s04-hida`): factorisation of `U'_s` at `p`, with `p`-component `Kpp p s`. -/
theorem UtowerP_factor {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (u : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    u ∈ UtowerP d M p s hN hp ↔
      awayAt d p hp u ∈ UtowerP d M p s hN hp ∧ localComponent d p hp u ∈ Kpp p s := by
  have h := mem_Utower_iff_factor_at (hp := hp) (hN := hN) hM hpM hs u
  have h1 : localComponent d p hp (awayAt d p hp u) = 1 := localComponent_awayAt u
  rw [mem_Kpp_iff', mem_UtowerP_iff, mem_UtowerP_iff]
  constructor
  · rintro ⟨hu, hK0⟩
    have hf := h.1 hu
    refine ⟨⟨hf.1, ?_⟩, hf.2, hK0⟩
    show localComponent d p hp (awayAt d p hp u) ∈ K0 p (s + 1)
    rw [h1]
    exact one_mem _
  · rintro ⟨⟨ha, -⟩, hK1, hK0⟩
    exact ⟨h.2 ⟨ha, hK1⟩, hK0⟩

/-- `lem:s04-hida`(a) (`s04-hida`): `U_s` is an `IsUpLevel` with `p`-component `K1 p s` (`p ∤ M`, `s ≥ 1`). -/
theorem isUpLevel_Utower {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    IsUpLevel d p hp (d.Utower M p s hN) (K1 p s) :=
  isUpLevel_of_K1 hs fun u => mem_Utower_iff_factor_at (hp := hp) hM hpM hs u

/-- `lem:s04-hida`(a) (`s04-hida`): `U'_s` is an `IsUpLevel` with `p`-component `Kpp p s`. -/
theorem isUpLevel_UtowerP {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    IsUpLevel d p hp (UtowerP d M p s hN hp) (Kpp p s) :=
  isUpLevel_of_Kpp hs (UtowerP_factor hM hpM hs)

/-- `lem:s04-hida`(a) (`s04-hida`): `U_0(q) U_s` (`p ∤ q`) is an `IsUpLevel` with `p`-component `K1 p s`. -/
theorem isUpLevel_U0q_Utower {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    {q : ℕ} (hq : q.Coprime d.D) (hpq : p ∉ q.primeFactors) :
    IsUpLevel d p hp (d.U0q q hq (d.Utower M p s hN)) (K1 p s) :=
  (isUpLevel_Utower hM hpM hs).U0q hq hpq

/-- `lem:s04-hida`(a) (`s04-hida`): at `Utower`, `UpAt` is the stage-1 `UpHom` (`def:s01-NUp`). -/
theorem UpAt_Utower_eq {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (R : Type*) [CommRing R] [Finite (XB (d.Utower M p s hN))] :
    UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R = UpHom d M p s hN hp hM hpM hs R :=
  rfl

/-- `lem:s04-hida`(a) (`s04-hida`): at `Utower`, `UpAtDual` is the stage-1 `Up` (`def:s01-NUp`). -/
theorem UpAtDual_Utower_eq {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (R : Type*) [CommRing R] :
    UpAtDual (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R = Up d M p s hN hp hM hpM hs R :=
  rfl

/-- `lem:s04-hida`(c) (`s04-hida`): an element of `U_s` with `p`-component in `K1 p (s+1)` lies in `U_{s+1}`
(the away parts of `U_s` and `U_{s+1}` agree). -/
private theorem mem_Utower_succ_of_mem {hN : (M * p ^ s).Coprime d.D}
    {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) {w : (GL2TF.Quat.BHat d.a d.b)ˣ}
    (hw : w ∈ d.Utower M p s hN) (hwp : localComponent d p hp w ∈ K1 p (s + 1)) :
    w ∈ d.Utower M p (s + 1) hN' := by
  have hpr : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hpr.ne_zero
  have hw' : w ∈ d.U1 (M * p ^ s) hN := hw
  show w ∈ d.U1 (M * p ^ (s + 1)) hN'
  rw [DefiniteData.mem_U1_iff] at hw' ⊢
  refine ⟨hw'.1, fun ℓ _ hℓ hD => ?_⟩
  have hℓpr : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  by_cases hℓp : ℓ = p
  · subst hℓp
    have hv : (M * ℓ ^ (s + 1)).factorization ℓ = s + 1 := by
      rw [Nat.factorization_mul hM (pow_ne_zero _ hp0), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpM, Nat.Prime.factorization_pow hpr,
        Finsupp.single_eq_same, zero_add]
    rw [hv]
    exact hwp
  · have hnd : ∀ k : ℕ, ¬ ℓ ∣ p ^ k := fun k h =>
      hℓp ((Nat.prime_dvd_prime_iff_eq hℓpr hpr).1 (hℓpr.dvd_of_dvd_pow h))
    have hfac : ∀ k : ℕ, (M * p ^ k).factorization ℓ = M.factorization ℓ := by
      intro k
      rw [Nat.factorization_mul hM (pow_ne_zero _ hp0), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hnd k), add_zero]
    have hℓM : ℓ ∣ M := by
      rcases (Nat.Prime.dvd_mul hℓpr).1 (Nat.dvd_of_mem_primeFactors hℓ) with h | h
      · exact h
      · exact absurd h (hnd (s + 1))
    have hℓ' : ℓ ∈ (M * p ^ s).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hℓpr, dvd_mul_of_dvd_left hℓM _, mul_ne_zero hM (pow_ne_zero _ hp0)⟩
    have h := hw'.2 ℓ hℓ' hD
    rw [hfac] at h ⊢
    exact h

/-- `lem:s04-hida`(b) (`s04-hida`): the `p`-away part of `u ∈ U_s` lies in `U'_s`. -/
private theorem awayAt_mem_UtowerP {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hs : 1 ≤ s) {u : (GL2TF.Quat.BHat d.a d.b)ˣ} (hu : u ∈ d.Utower M p s hN) :
    awayAt d p hp u ∈ UtowerP d M p s hN hp := by
  refine mem_UtowerP_iff.2 ⟨((mem_Utower_iff_factor_at (hp := hp) hM hpM hs u).1 hu).1, ?_⟩
  show localComponent d p hp (awayAt d p hp u) ∈ K0 p (s + 1)
  rw [localComponent_awayAt]
  exact one_mem _

variable (d M p s) in
/-- `lem:s04-hida` (`s04-hida`): the projection `π' : X'_s → X_s`, `[x]' ↦ [x]`. -/
noncomputable def piP (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) :
    XB (UtowerP d M p s hN hp) → XB (d.Utower M p s hN) :=
  levelMap _ _

variable (d M p s) in
/-- `lem:s04-hida` (`s04-hida`): the projection `π'' : X_{s+1} → X'_s`, `[x] ↦ [x]'`. -/
noncomputable def piPP (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (hp : ¬ p ∣ d.D) : XB (d.Utower M p (s + 1) hN') → XB (UtowerP d M p s hN hp) :=
  levelMap _ _

variable (d M p s) in
/-- `lem:s04-hida` (`s04-hida`): the pushforward `π'_* : R[X'_s] → R[X_s]`. -/
noncomputable def piP_push (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (R : Type*) [CommRing R] :
    ZX (UtowerP d M p s hN hp) R →ₗ[R] ZX (d.Utower M p s hN) R :=
  pushforward _ _ R

variable (d M p s) in
/-- `lem:s04-hida` (`s04-hida`): the pushforward `π''_* : R[X_{s+1}] → R[X'_s]`. -/
noncomputable def piPP_push (hN : (M * p ^ s).Coprime d.D) (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (hp : ¬ p ∣ d.D) (R : Type*) [CommRing R] :
    ZX (d.Utower M p (s + 1) hN') R →ₗ[R] ZX (UtowerP d M p s hN hp) R :=
  pushforward _ _ R

/-- `lem:s04-hida` (`s04-hida`): `π' [x]' = [x]`. -/
theorem piP_mk {hN : (M * p ^ s).Coprime d.D} (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    piP d M p s hN hp (DoubleCoset.mk (globalUnits d.a d.b) (UtowerP d M p s hN hp) x) =
      DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p s hN) x :=
  levelMap_mk (UtowerP_le_Utower (hp := hp) hN) x

/-- `lem:s04-hida` (`s04-hida`): `π'' [x] = [x]'`. -/
theorem piPP_mk {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (x : (GL2TF.Quat.BHat d.a d.b)ˣ) :
    piPP d M p s hN hN' hp (DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x) =
      DoubleCoset.mk (globalUnits d.a d.b) (UtowerP d M p s hN hp) x :=
  levelMap_mk (Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM) x

/-- `lem:s04-hida` (`s04-hida`): `π'` is onto. -/
theorem piP_surjective {hN : (M * p ^ s).Coprime d.D} : Function.Surjective (piP d M p s hN hp) :=
  levelMap_surjective (UtowerP_le_Utower (hp := hp) hN)

/-- `lem:s04-hida`(c) (`s04-hida`): `π''` is onto. -/
theorem piPP_surjective {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) : Function.Surjective (piPP d M p s hN hN' hp) :=
  levelMap_surjective (Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM)

/-- `lem:s04-hida` (`s04-hida`): `X'_s` is finite if `X_{s+1}` is. -/
theorem finite_XB_UtowerP {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D}
    (hM : M ≠ 0) (hpM : ¬ p ∣ M) [Finite (XB (d.Utower M p (s + 1) hN'))] :
    Finite (XB (UtowerP d M p s hN hp)) :=
  finite_XB_of_le (Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM)

/-- `lem:s04-hida`(a) (`s04-hida`): `U_p` commutes with both pushforwards,
`π'_* ∘ U_p = U_p ∘ π'_*` on `R[X'_s]` and `π''_* ∘ U_p = U_p ∘ π''_*` on `R[X_{s+1}]` (the same `ϖ_j` at the
three levels `U_{s+1} ≤ U'_s ≤ U_s`). -/
theorem Up_comm {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type*) [CommRing R] [Finite (XB (d.Utower M p s hN))]
    [Finite (XB (UtowerP d M p s hN hp))] [Finite (XB (d.Utower M p (s + 1) hN'))] :
    piP_push d M p s hN hp R ∘ₗ UpAt (UtowerP d M p s hN hp) (isUpLevel_UtowerP hM hpM hs) R =
        UpAt (d.Utower M p s hN) (isUpLevel_Utower (hp := hp) hM hpM hs) R ∘ₗ piP_push d M p s hN hp R ∧
      piPP_push d M p s hN hN' hp R ∘ₗ
          UpAt (d.Utower M p (s + 1) hN') (isUpLevel_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s)) R =
        UpAt (UtowerP d M p s hN hp) (isUpLevel_UtowerP hM hpM hs) R ∘ₗ piPP_push d M p s hN hN' hp R :=
  ⟨UpAt_comm_pushforward _ _ (UtowerP_le_Utower (hp := hp) hN),
    UpAt_comm_pushforward _ _ (Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM)⟩

/-- `lem:s04-hida`(b) (`s04-hida`), global Hida: `U_p (ker π'_*) = 0` on `R[X'_s]`. -/
theorem Up_ker_push_eq_zero {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (R : Type*) [CommRing R] [Finite (XB (d.Utower M p s hN))] [Finite (XB (UtowerP d M p s hN hp))]
    (a : ZX (UtowerP d M p s hN hp) R) (ha : piP_push d M p s hN hp R a = 0) :
    UpAt (UtowerP d M p s hN hp) (isUpLevel_UtowerP hM hpM hs) R a = 0 :=
  UpAt_ker_pushforward_eq_zero hs (isUpLevel_UtowerP hM hpM hs) (isUpLevel_Utower (hp := hp) hM hpM hs)
    (UtowerP_le_Utower (hp := hp) hN) (fun _ hu => awayAt_mem_UtowerP (hp := hp) hM hpM hs hu) a ha

/-- `lem:s04-hida`(c) (`s04-hida`): `δ_t ∈ U'_s` for `t ≡ 1 mod p^s`. -/
theorem deltaElt_mem_UtowerP {hN : (M * p ^ s).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1) :
    deltaElt d p hp t ∈ UtowerP d M p s hN hp := by
  refine mem_UtowerP_iff.2 ⟨deltaElt_mem_Utower (hp := hp) hM hpM hs t ht, ?_⟩
  show localComponent d p hp (deltaElt d p hp t) ∈ K0 p (s + 1)
  rw [localComponent_deltaElt]
  exact one_diag_mem_K0 t _

/-- `lem:s04-hida`(c) (`s04-hida`), torsor, fibres: `π'' c = π'' c'` iff `c' = ⟨t⟩ c` for some `t ≡ 1 mod p^s`,
i.e. the fibres of `π'' : X_{s+1} → X'_s` are the orbits of `ker(Δ_{s+1} → Δ_s) = (1 + p^s ℤ_p)/(1 + p^{s+1} ℤ_p)`
acting by `diamondAct`. -/
theorem piPP_eq_iff {hN : (M * p ^ s).Coprime d.D} {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0)
    (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (c c' : XB (d.Utower M p (s + 1) hN')) :
    piPP d M p s hN hN' hp c = piPP d M p s hN hN' hp c' ↔
      ∃ t : ℤ_[p]ˣ, (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1 ∧
        diamondAct (hp := hp) hM hpM (Nat.le_add_left 1 s) t c = c' := by
  have hle := Utower_succ_le_UtowerP (hp := hp) hN hN' hM hpM
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x = c :=
    ⟨_, DoubleCoset.out_eq' c⟩
  obtain ⟨x', rfl⟩ : ∃ x', DoubleCoset.mk (globalUnits d.a d.b) (d.Utower M p (s + 1) hN') x' = c' :=
    ⟨_, DoubleCoset.out_eq' c'⟩
  rw [piPP_mk hM hpM, piPP_mk hM hpM]
  constructor
  · intro h
    obtain ⟨γ, hγ, k, hk, hx'⟩ := DoubleCoset.eq.1 h
    have hkf := (UtowerP_factor hM hpM hs k).1 hk
    obtain ⟨t, ht, htk⟩ := exists_diag_inv_mul_mem_K1_succ hs hkf.2
    refine ⟨t, ht, ?_⟩
    rw [diamondAct_mk]
    refine DoubleCoset.eq.2 ⟨γ, hγ, (deltaElt d p hp t)⁻¹ * k, ?_, ?_⟩
    · have hδ : deltaElt d p hp t = localEmbedGL d p hp (diagGL 1 (intUnit t)) := rfl
      have hc : (localEmbedGL d p hp (diagGL 1 (intUnit t)))⁻¹ * awayAt d p hp k =
          awayAt d p hp k * (localEmbedGL d p hp (diagGL 1 (intUnit t)))⁻¹ :=
        (commute_awayAt_localEmbedGL (hp := hp) k (diagGL 1 (intUnit t))).inv_right.eq.symm
      have hv : (deltaElt d p hp t)⁻¹ * k = awayAt d p hp k *
          localEmbedGL d p hp ((diagGL 1 (intUnit t))⁻¹ * localComponent d p hp k) := by
        calc (deltaElt d p hp t)⁻¹ * k
            = (localEmbedGL d p hp (diagGL 1 (intUnit t)))⁻¹ *
                (awayAt d p hp k * localEmbedGL d p hp (localComponent d p hp k)) := by
              rw [hδ, awayAt_mul_localEmbedGL]
          _ = ((localEmbedGL d p hp (diagGL 1 (intUnit t)))⁻¹ * awayAt d p hp k) *
                localEmbedGL d p hp (localComponent d p hp k) := (mul_assoc _ _ _).symm
          _ = (awayAt d p hp k * (localEmbedGL d p hp (diagGL 1 (intUnit t)))⁻¹) *
                localEmbedGL d p hp (localComponent d p hp k) := by rw [hc]
          _ = awayAt d p hp k *
                localEmbedGL d p hp ((diagGL 1 (intUnit t))⁻¹ * localComponent d p hp k) := by
              rw [map_mul, map_inv, mul_assoc]
      rw [hv]
      have hwp : localComponent d p hp (awayAt d p hp k) ∈ K1 p (s + 1) := by
        rw [localComponent_awayAt]
        exact one_mem _
      exact mul_mem (mem_Utower_succ_of_mem (hp := hp) (hN := hN) (hN' := hN') hM hpM
          (mem_UtowerP_iff.1 hkf.1).1 hwp)
        (localEmbedGL_mem_Utower (hp := hp) hM hpM (Nat.le_add_left 1 s) htk)
    · rw [hx']
      group
  · rintro ⟨t, ht, h⟩
    rw [diamondAct_mk] at h
    obtain ⟨γ, hγ, k, hk, hx'⟩ := DoubleCoset.eq.1 h
    exact DoubleCoset.eq.2 ⟨γ, hγ, deltaElt d p hp t * k,
      mul_mem (deltaElt_mem_UtowerP hM hpM hs t ht) (hle hk), by rw [hx']; group⟩

/-- `lem:s04-hida`(c) (`s04-hida`), torsor, freeness (from `diamondAct_free`): `t ≡ 1 mod p^s` fixing a point of
`X_{s+1}` satisfies `t ≡ 1 mod p^{s+1}`, so `ker(Δ_{s+1} → Δ_s)` acts freely on every fibre of `π''`
(`p ≥ 5`). -/
theorem piPP_free {hN' : (M * p ^ (s + 1)).Coprime d.D} (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s)
    (h5 : 5 ≤ p) (t : ℤ_[p]ˣ) (ht : (p : ℤ_[p]) ^ s ∣ (t : ℤ_[p]) - 1) (c : XB (d.Utower M p (s + 1) hN'))
    (hfix : diamondAct (hp := hp) hM hpM (Nat.le_add_left 1 s) t c = c) :
    (p : ℤ_[p]) ^ (s + 1) ∣ (t : ℤ_[p]) - 1 :=
  diamondAct_free hM hpM (Nat.le_add_left 1 s) h5 t
    ((dvd_pow_self (p : ℤ_[p]) (by omega : s ≠ 0)).trans ht) c hfix

end Tower

end Langlandscape.Ordinary
