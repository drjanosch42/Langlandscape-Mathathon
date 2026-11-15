/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Local
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Coset model of the tree — S02-L1 (built, gate1 green)

Tex labels: def:s02-tree, lem:s02-tree.
-/

/-!
## Contents

The Bruhat–Tits tree of `def:s02-tree` in coset form:

* vertices `Vert q = GL₂(ℚ_q) ⧸ (Z · GL₂(ℤ_q))`, `[g] ↔ [g ℤ_q²]`;
* **all oriented** edges `Edge q = GL₂(ℚ_q) ⧸ (Z · Iw_q)`, with `o [g] = [g]`, `t [g] = [g α]`;
* the tex's edge set `EdgeO q` = the oriented edges with type-`0` origin (orientation type `0 → 1`);
* `vtype [g] = v_q(det g) mod 2`, `v0 = [1]`, `v1 = [α]`, `e0 = [1]`;
* `lem:s02-tree`(b): `preserves_vtype_iff`; (c): transitivity of `SL₂(ℚ_q)` on type-`0`
  vertices, type-`1` vertices and `EdgeO q`, with stabilisers `SL₂(ℤ_q)`, `K1q`, `SL₂ ∩ Iw_q`;
* the simple graph `graph q` on `Vert q`.

The proofs follow the tex ("Proof strategy"): `g = s · x · (z · diag(1, u))` with `s ∈ SL₂`,
`z` scalar, `u ∈ ℤ_q^×` (`exists_decomp`), and a scalar of a determinant-one element of `Z · K` is a
unit.

Auxiliary declarations: the inclusions `center_le_ZK`, …, `ZIw_le_ZK`, `vdetKer`, `conj_mem_ZK`,
`exists_diagGL_mul`, `mem_GL2Zl_of_mem_ZK`, `mem_Iw_of_mem_ZIw`, `exists_decomp`, `o_mk`, `t_mk`,
`vtype_mk`, `coe_smul_EdgeO`, `oO_smul`, `tO_smul`, `vtype_v0`, `vtype_v1`, `graph_adj_iff`,
`graph_adj_v0_v1` support the interface of S02-L1; facts about `GL₂(ℚ_q)` that are not about the
tree are `private`.

Status: *formalized*.
-/

open Matrix

namespace Langlandscape.Tree

open Langlandscape.Local (GL2Zl Iw)

noncomputable section

variable (q : ℕ) [Fact q.Prime]

/-! ### The centre of `GL₂(ℚ_q)` -/

/-- Scalars as `diag(a, a)` (auxiliary, `def:s02-tree`, `s02-tree`). -/
private theorem scalar_eq_diagGL (a : ℚ_[q]ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a = Local.diagGL a a := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (a : ℚ_[q]) = !![(a : ℚ_[q]), 0; 0, (a : ℚ_[q])]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The centre of `GL₂(ℚ_q)` is `{diag(a, a)}` (auxiliary, `def:s02-tree`, `s02-tree`). -/
private theorem mem_center_iff_diagGL {z : GL (Fin 2) ℚ_[q]} :
    z ∈ Subgroup.center (GL (Fin 2) ℚ_[q]) ↔ ∃ a : ℚ_[q]ˣ, z = Local.diagGL a a := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, scalar_eq_diagGL q a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, scalar_eq_diagGL q a⟩

/-! ### The subgroups `Z · GL₂(ℤ_q)` and `Z · Iw_q` -/

/-- `Z · GL₂(ℤ_q)`, the stabiliser of `v₀ = [ℤ_q²]` in `GL₂(ℚ_q)` (`def:s02-tree`). -/
def ZK : Subgroup (GL (Fin 2) ℚ_[q]) := Subgroup.center _ ⊔ GL2Zl q

/-- `Z · Iw_q`, the stabiliser of the oriented base edge (`def:s02-tree`). -/
def ZIw : Subgroup (GL (Fin 2) ℚ_[q]) := Subgroup.center _ ⊔ Iw q

/-- `Z ≤ Z · GL₂(ℤ_q)` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem center_le_ZK : Subgroup.center (GL (Fin 2) ℚ_[q]) ≤ ZK q := le_sup_left

/-- `GL₂(ℤ_q) ≤ Z · GL₂(ℤ_q)` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem GL2Zl_le_ZK : GL2Zl q ≤ ZK q := le_sup_right

/-- `Z ≤ Z · Iw_q` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem center_le_ZIw : Subgroup.center (GL (Fin 2) ℚ_[q]) ≤ ZIw q := le_sup_left

/-- `Iw_q ≤ Z · Iw_q` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem Iw_le_ZIw : Iw q ≤ ZIw q := le_sup_right

/-- `Iw_q ≤ Z · GL₂(ℤ_q)` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem Iw_le_ZK : Iw q ≤ ZK q := le_trans (Local.K0_le_GL2Zl 1) (GL2Zl_le_ZK q)

/-- `Z · Iw_q ≤ Z · GL₂(ℤ_q)` (auxiliary, `def:s02-tree`, `s02-tree`). -/
theorem ZIw_le_ZK : ZIw q ≤ ZK q := sup_le_sup_left (Local.K0_le_GL2Zl 1) _

/-- The elements with `vdet = 0` (auxiliary subgroup for `def:s02-tree`). -/
def vdetKer : Subgroup (GL (Fin 2) ℚ_[q]) where
  carrier := {g | vdet q g = 0}
  one_mem' := vdet_one q
  mul_mem' := fun {a b} ha hb => by
    show vdet q (a * b) = 0
    rw [vdet_mul, show vdet q a = 0 from ha, show vdet q b = 0 from hb, add_zero]
  inv_mem' := fun {a} ha => by
    show vdet q a⁻¹ = 0
    have h1 := vdet_mul a⁻¹ a
    rw [inv_mul_cancel, vdet_one, show vdet q a = 0 from ha, add_zero] at h1
    exact h1.symm

/-- The type is well defined: `Z · GL₂(ℤ_q)` has `vdet = 0` (`def:s02-tree`, `s02-tree`). -/
theorem ZK_le_vdetKer : ZK q ≤ vdetKer q := by
  refine sup_le (fun z hz => ?_) (fun k hk => vdet_of_mem_GL2Zl hk)
  obtain ⟨a, rfl⟩ := (mem_center_iff_diagGL q).1 hz
  show vdet q (Local.diagGL a a) = 0
  rw [vdet, det_diagGL, Padic.valuation_mul a.ne_zero a.ne_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨Padic.valuation (a : ℚ_[q]), by push_cast; ring⟩

variable {q}

/-- `α⁻¹ (Z · Iw_q) α ⊆ Z · GL₂(ℤ_q)`, so `t` is well defined (`lem:s02-tree`(d), `s02-tree`). -/
theorem conj_mem_ZK {x : GL (Fin 2) ℚ_[q]} (hx : x ∈ ZIw q) :
    (alphaq q)⁻¹ * x * alphaq q ∈ ZK q := by
  have hx' : x ∈ Subgroup.center (GL (Fin 2) ℚ_[q]) ⊔ Iw q := hx
  obtain ⟨z, hz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  have hc : (alphaq q)⁻¹ * z = z * (alphaq q)⁻¹ := Subgroup.mem_center_iff.1 hz _
  have e : (alphaq q)⁻¹ * (z * k) * alphaq q = z * ((alphaq q)⁻¹ * k * alphaq q) :=
    calc (alphaq q)⁻¹ * (z * k) * alphaq q = (alphaq q)⁻¹ * z * k * alphaq q := by group
      _ = z * (alphaq q)⁻¹ * k * alphaq q := by rw [hc]
      _ = z * ((alphaq q)⁻¹ * k * alphaq q) := by group
  rw [e]
  exact mul_mem (center_le_ZK q hz) (GL2Zl_le_ZK q (alphaq_inv_conj_mem_GL2Zl hk))

/-- An element of `Z · H` with `‖det‖ = 1` is `diag(a, a) k` with `‖a‖ = 1`, `k ∈ H`, if `H` has
unit determinants (auxiliary, Serre's Lemma 1 in `lem:s02-tree`(c), `s02-tree`). -/
theorem exists_diagGL_mul {H : Subgroup (GL (Fin 2) ℚ_[q])}
    (hH : ∀ k ∈ H, ‖(Units.val k).det‖ = 1) {s : GL (Fin 2) ℚ_[q]}
    (hs : s ∈ Subgroup.center (GL (Fin 2) ℚ_[q]) ⊔ H) (hd : ‖(Units.val s).det‖ = 1) :
    ∃ a : ℚ_[q]ˣ, ‖(a : ℚ_[q])‖ = 1 ∧ ∃ k ∈ H, s = Local.diagGL a a * k := by
  obtain ⟨z, hz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hs
  obtain ⟨a, rfl⟩ := (mem_center_iff_diagGL q).1 hz
  refine ⟨a, ?_, k, hk, rfl⟩
  have h2 : ‖(a : ℚ_[q])‖ * ‖(a : ℚ_[q])‖ = 1 := by
    rw [Units.val_mul, Matrix.det_mul, det_diagGL, norm_mul, norm_mul, hH k hk, mul_one] at hd
    exact hd
  have h0 := norm_nonneg (a : ℚ_[q])
  exact le_antisymm (by nlinarith) (by nlinarith)

/-- `SL₂ ∩ Z · GL₂(ℤ_q) ⊆ GL₂(ℤ_q)` in the form `‖det‖ = 1` (`lem:s02-tree`(c), `s02-tree`). -/
theorem mem_GL2Zl_of_mem_ZK {s : GL (Fin 2) ℚ_[q]} (hs : s ∈ ZK q)
    (hd : ‖(Units.val s).det‖ = 1) : s ∈ GL2Zl q := by
  obtain ⟨a, ha, k, hk, rfl⟩ :=
    exists_diagGL_mul (H := GL2Zl q) (fun k hk => (Local.mem_GL2Zl_iff.1 hk).2) hs hd
  exact mul_mem (Local.K0_le_GL2Zl 1 (diagGL_mem_Iw ha)) hk

/-- `SL₂ ∩ Z · Iw_q ⊆ Iw_q` in the form `‖det‖ = 1` (`lem:s02-tree`(c), `s02-tree`). -/
theorem mem_Iw_of_mem_ZIw {s : GL (Fin 2) ℚ_[q]} (hs : s ∈ ZIw q)
    (hd : ‖(Units.val s).det‖ = 1) : s ∈ Iw q := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_diagGL_mul (H := Iw q)
    (fun k hk => (Local.mem_GL2Zl_iff.1 (Local.K0_le_GL2Zl 1 hk)).2) hs hd
  exact mul_mem (diagGL_mem_Iw ha) hk

/-- Equal parities of valuations: `a = b (q^m)² u` with `u ∈ ℤ_q^×` (proof of `lem:s02-tree`(c),
`s02-tree`). -/
private theorem exists_unit_factor {a b : ℚ_[q]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((Padic.valuation a : ℤ) : ZMod 2) = ((Padic.valuation b : ℤ) : ZMod 2)) :
    ∃ (m : ℤ) (u : ℤ_[q]ˣ), a = b * ((q : ℚ_[q]) ^ m) ^ 2 * ((u : ℤ_[q]) : ℚ_[q]) := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).1 h
  have hq0 := qcast_ne_zero q
  have hp : ((q : ℚ_[q]) ^ (-m)) ^ 2 ≠ 0 := pow_ne_zero _ (zpow_ne_zero _ hq0)
  have hc : b * ((q : ℚ_[q]) ^ (-m)) ^ 2 ≠ 0 := mul_ne_zero hb hp
  have hw0 : a * (b * ((q : ℚ_[q]) ^ (-m)) ^ 2)⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hc)
  have hv : Padic.valuation (a * (b * ((q : ℚ_[q]) ^ (-m)) ^ 2)⁻¹) = 0 := by
    rw [Padic.valuation_mul ha (inv_ne_zero hc), Padic.valuation_inv,
      Padic.valuation_mul hb hp, Padic.valuation_pow, Padic.valuation_zpow, Padic.valuation_p]
    omega
  have hw1 : ‖a * (b * ((q : ℚ_[q]) ^ (-m)) ^ 2)⁻¹‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation hw0, hv, neg_zero, zpow_zero]
  have hU : IsUnit (⟨_, show a * (b * ((q : ℚ_[q]) ^ (-m)) ^ 2)⁻¹ ∈ PadicInt.subring q from
      hw1.le⟩ : ℤ_[q]) := PadicInt.isUnit_iff.2 hw1
  refine ⟨-m, hU.unit, ?_⟩
  rw [IsUnit.unit_spec]
  show a = b * ((q : ℚ_[q]) ^ (-m)) ^ 2 * (a * (b * ((q : ℚ_[q]) ^ (-m)) ^ 2)⁻¹)
  linear_combination (-a) * mul_inv_cancel₀ hc

/-- Proof of `lem:s02-tree`(c) (`s02-tree`): if `vdet g = vdet x` then `g = s x (z k)` with
`s ∈ SL₂(ℚ_q)`, `z` central and `k = diag(1, u) ∈ Iw_q`. -/
theorem exists_decomp (g x : GL (Fin 2) ℚ_[q]) (h : vdet q g = vdet q x) :
    ∃ s ∈ SLq q, ∃ z ∈ Subgroup.center (GL (Fin 2) ℚ_[q]), ∃ k ∈ Iw q, g = s * x * (z * k) := by
  obtain ⟨m, u, hgu⟩ := exists_unit_factor (Local.det_ne_zero g) (Local.det_ne_zero x) h
  have hq0 : ((q : ℚ_[q]) ^ m) ≠ 0 := zpow_ne_zero _ (qcast_ne_zero q)
  set z : GL (Fin 2) ℚ_[q] := Local.diagGL (Units.mk0 _ hq0) (Units.mk0 _ hq0) with hz
  set k : GL (Fin 2) ℚ_[q] := Local.diagGL 1 (Local.intUnit u) with hk
  set s : GL (Fin 2) ℚ_[q] := g * (z * k)⁻¹ * x⁻¹ with hs
  have hsg : s * x * (z * k) = g := by
    rw [hs]
    group
  have hzc : z ∈ Subgroup.center (GL (Fin 2) ℚ_[q]) := (mem_center_iff_diagGL q).2 ⟨_, hz⟩
  have hkI : k ∈ Iw q := by
    rw [hk]
    exact Local.one_diag_mem_K0 u 1
  have hW : (Units.val x).det * ((Units.val z).det * (Units.val k).det) ≠ 0 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, ← Units.val_mul, ← Units.val_mul]
    exact Local.det_ne_zero _
  have h1 : (Units.val s).det * ((Units.val x).det * ((Units.val z).det * (Units.val k).det)) =
      (Units.val g).det := by
    rw [← hsg]
    simp only [Units.val_mul, Matrix.det_mul]
    ring
  have h2 : (Units.val x).det * ((Units.val z).det * (Units.val k).det) = (Units.val g).det := by
    rw [hz, hk, det_diagGL, det_diagGL, hgu, Units.val_mk0, Units.val_one, Local.coe_intUnit]
    ring
  refine ⟨s, mem_SLq_iff.2 (mul_right_cancel₀ hW ?_), z, hzc, k, hkI, hsg.symm⟩
  rw [h1, h2, one_mul]

/-- If `g = s x (z k)` with `z` central and `k ∈ Iw_q`, then `[s x] = [g]` in `GL₂(ℚ_q) ⧸ H` for
every `H ⊇ Z · Iw_q` (proof of `lem:s02-tree`(c), `s02-tree`). -/
private theorem mk_eq_of_decomp {H : Subgroup (GL (Fin 2) ℚ_[q])}
    (hZ : Subgroup.center (GL (Fin 2) ℚ_[q]) ≤ H) (hI : Iw q ≤ H)
    {g s x z k : GL (Fin 2) ℚ_[q]} (hz : z ∈ Subgroup.center (GL (Fin 2) ℚ_[q]))
    (hk : k ∈ Iw q) (hgs : g = s * x * (z * k)) :
    ((s * x : GL (Fin 2) ℚ_[q]) : GL (Fin 2) ℚ_[q] ⧸ H) = (g : GL (Fin 2) ℚ_[q] ⧸ H) := by
  subst hgs
  refine QuotientGroup.eq.2 ?_
  have e : (s * x)⁻¹ * (s * x * (z * k)) = z * k := by group
  rw [e]
  exact mul_mem (hZ hz) (hI hk)

/-! ### Vertices, edges, types -/

variable (q)

/-- The vertices of `𝒯_q` in coset form: `GL₂(ℚ_q) ⧸ (Z · GL₂(ℤ_q))`, `[g] ↔ [g ℤ_q²]`
(`def:s02-tree`). -/
abbrev Vert := GL (Fin 2) ℚ_[q] ⧸ ZK q

/-- All **oriented** edges of `𝒯_q` in coset form: `GL₂(ℚ_q) ⧸ (Z · Iw_q)` (both orientations of
every geometric edge; `def:s02-tree`). -/
abbrev Edge := GL (Fin 2) ℚ_[q] ⧸ ZIw q

/-- The origin `o [g] = [g]` of an oriented edge (`def:s02-tree`). -/
def o : Edge q → Vert q := Subgroup.quotientMapOfLE (ZIw_le_ZK q)

/-- The terminus `t [g] = [g α]` of an oriented edge (`def:s02-tree`). -/
def t : Edge q → Vert q :=
  Quotient.map' (fun g => g * alphaq q) fun a b hab => by
    have h := conj_mem_ZK (QuotientGroup.leftRel_apply.mp hab)
    apply QuotientGroup.leftRel_apply.mpr
    show (a * alphaq q)⁻¹ * (b * alphaq q) ∈ ZK q
    have e : (a * alphaq q)⁻¹ * (b * alphaq q) = (alphaq q)⁻¹ * (a⁻¹ * b) * alphaq q := by group
    rw [e]
    exact h

/-- The type `τ[g ℤ_q²] = v_q(det g) mod 2` (`def:s02-tree`). -/
def vtype (v : Vert q) : ZMod 2 :=
  Quotient.liftOn' v (vdet q) fun a b hab => by
    have h : a⁻¹ * b ∈ ZK q := QuotientGroup.leftRel_apply.mp hab
    have h3 : vdet q (a⁻¹ * b) = 0 := ZK_le_vdetKer q h
    have h2 := vdet_mul a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h3, add_zero] at h2
    exact h2.symm

variable {q}

/-- `o [g] = [g]` (`def:s02-tree`, `s02-tree`). -/
theorem o_mk (g : GL (Fin 2) ℚ_[q]) : o q (g : Edge q) = (g : Vert q) := rfl

/-- `t [g] = [g α]` (`def:s02-tree`, `s02-tree`). -/
theorem t_mk (g : GL (Fin 2) ℚ_[q]) :
    t q (g : Edge q) = ((g * alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) := rfl

/-- `vtype [g] = vdet g` (`def:s02-tree`, `s02-tree`). -/
theorem vtype_mk (g : GL (Fin 2) ℚ_[q]) : vtype q (g : Vert q) = vdet q g := rfl

/-- `o` is `GL₂(ℚ_q)`-equivariant (`def:s02-tree`, `s02-tree`). -/
theorem o_smul (g : GL (Fin 2) ℚ_[q]) (e : Edge q) : o q (g • e) = g • o q e := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
  rfl

/-- `t` is `GL₂(ℚ_q)`-equivariant (`def:s02-tree`, `s02-tree`). -/
theorem t_smul (g : GL (Fin 2) ℚ_[q]) (e : Edge q) : t q (g • e) = g • t q e := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
  show ((g * a * alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) =
    ((g * (a * alphaq q) : GL (Fin 2) ℚ_[q]) : Vert q)
  rw [mul_assoc]

/-- `τ(g v) = v_q(det g) + τ(v)` (`def:s02-tree`, `lem:s02-tree`(b), `s02-tree`). -/
theorem vtype_smul (g : GL (Fin 2) ℚ_[q]) (v : Vert q) :
    vtype q (g • v) = vdet q g + vtype q v := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective v
  exact vdet_mul g a

/-- The two ends of an oriented edge have different types (`def:s02-tree`, `s02-tree`). -/
theorem vtype_t (e : Edge q) : vtype q (t q e) = vtype q (o q e) + 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
  show vdet q (a * alphaq q) = vdet q a + 1
  rw [vdet_mul, vdet_alphaq]

/-! ### The tex's edge set `EdgeO q` (orientation type `0 → 1`) -/

variable (q)

/-- The tex's edge set: oriented edges with type-`0` origin (orientation type `0 → 1`,
`def:s02-tree`). -/
abbrev EdgeO := {e : Edge q // vtype q (o q e) = 0}

/-- The origin (type-`0` end) of an edge of `EdgeO q` (`def:s02-tree`). -/
def oO (e : EdgeO q) : Vert q := o q e.1

/-- The terminus (type-`1` end) of an edge of `EdgeO q` (`def:s02-tree`). -/
def tO (e : EdgeO q) : Vert q := t q e.1

/-- `SL₂(ℚ_q)` acts on `EdgeO q`: it preserves types (`lem:s02-tree`(b)). -/
instance instMulActionSLqEdgeO : MulAction (SLq q) (EdgeO q) where
  smul s e := ⟨(s : GL (Fin 2) ℚ_[q]) • e.1, by
    rw [o_smul, vtype_smul, vdet_of_mem_SLq s.2, e.2, add_zero]⟩
  one_smul e := Subtype.ext (one_smul (GL (Fin 2) ℚ_[q]) e.1)
  mul_smul s s' e := Subtype.ext (mul_smul (s : GL (Fin 2) ℚ_[q]) (s' : GL (Fin 2) ℚ_[q]) e.1)

/-- The base vertex `v₀ = [ℤ_q²] = [1]` (`def:s02-tree`). -/
def v0 : Vert q := ((1 : GL (Fin 2) ℚ_[q]) : Vert q)

/-- The vertex `v₁ = α v₀ = [ℤ_q ⊕ q ℤ_q] = [α]` (`def:s02-tree`). -/
def v1 : Vert q := ((alphaq q : GL (Fin 2) ℚ_[q]) : Vert q)

/-- The base edge `e₀ = [1]`, from `v₀` to `v₁` (`def:s02-tree`). -/
def e0 : EdgeO q := ⟨((1 : GL (Fin 2) ℚ_[q]) : Edge q), vdet_one q⟩

variable {q}

/-- The action on `EdgeO q` is the restriction of the action on `Edge q` (`lem:s02-tree`,
`s02-tree`). -/
theorem coe_smul_EdgeO (s : SLq q) (e : EdgeO q) :
    ((s • e : EdgeO q) : Edge q) = (s : GL (Fin 2) ℚ_[q]) • (e : Edge q) := rfl

/-- `oO` is `SL₂(ℚ_q)`-equivariant (`def:s02-tree`, `s02-tree`). -/
theorem oO_smul (s : SLq q) (e : EdgeO q) : oO q (s • e) = s • oO q e :=
  o_smul (s : GL (Fin 2) ℚ_[q]) e.1

/-- `tO` is `SL₂(ℚ_q)`-equivariant (`def:s02-tree`, `s02-tree`). -/
theorem tO_smul (s : SLq q) (e : EdgeO q) : tO q (s • e) = s • tO q e :=
  t_smul (s : GL (Fin 2) ℚ_[q]) e.1

variable (q)

/-- `o e₀ = v₀` (`def:s02-tree`, `s02-tree`). -/
theorem oO_e0 : oO q (e0 q) = v0 q := rfl

/-- `t e₀ = v₁` (`def:s02-tree`, `s02-tree`). -/
theorem tO_e0 : tO q (e0 q) = v1 q := by
  show ((1 * alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) = ((alphaq q : GL (Fin 2) ℚ_[q]) : Vert q)
  rw [one_mul]

/-- `τ(v₀) = 0` (`def:s02-tree`, `s02-tree`). -/
theorem vtype_v0 : vtype q (v0 q) = 0 := vdet_one q

/-- `τ(v₁) = 1` (`def:s02-tree`, `s02-tree`). -/
theorem vtype_v1 : vtype q (v1 q) = 1 := vdet_alphaq q

variable {q}

/-- The origin of an edge of `EdgeO q` has type `0` (`def:s02-tree`, `s02-tree`). -/
theorem vtype_oO (e : EdgeO q) : vtype q (oO q e) = 0 := e.2

/-- The terminus of an edge of `EdgeO q` has type `1` (`def:s02-tree`, `s02-tree`). -/
theorem vtype_tO (e : EdgeO q) : vtype q (tO q e) = 1 := by
  show vtype q (t q e.1) = 1
  rw [vtype_t, e.2, zero_add]

/-! ### `lem:s02-tree`(b) -/

/-- `lem:s02-tree`(b) (`s02-tree`): `g` preserves types iff `v_q(det g)` is even. -/
theorem preserves_vtype_iff (g : GL (Fin 2) ℚ_[q]) :
    (∀ v : Vert q, vtype q (g • v) = vtype q v) ↔ vdet q g = 0 := by
  constructor
  · intro h
    have h0 := h (v0 q)
    rw [vtype_smul] at h0
    exact add_right_cancel (h0.trans (zero_add _).symm)
  · intro h v
    rw [vtype_smul, h, zero_add]

/-! ### `lem:s02-tree`(c): transitivity -/

/-- `lem:s02-tree`(c) (`s02-tree`): `SL₂(ℚ_q)` is transitive on type-`0` vertices. -/
theorem SLq_transitive_type0 {v : Vert q} (h : vtype q v = 0) : ∃ s : SLq q, s • v0 q = v := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨s, hs, z, hz, k, hk, hgs⟩ := exists_decomp g 1 (h.trans (vdet_one q).symm)
  exact ⟨⟨s, hs⟩, mk_eq_of_decomp (center_le_ZK q) (Iw_le_ZK q) hz hk hgs⟩

/-- `lem:s02-tree`(c) (`s02-tree`): `SL₂(ℚ_q)` is transitive on type-`1` vertices. -/
theorem SLq_transitive_type1 {v : Vert q} (h : vtype q v = 1) : ∃ s : SLq q, s • v1 q = v := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨s, hs, z, hz, k, hk, hgs⟩ :=
    exists_decomp g (alphaq q) (h.trans (vdet_alphaq q).symm)
  exact ⟨⟨s, hs⟩, mk_eq_of_decomp (center_le_ZK q) (Iw_le_ZK q) hz hk hgs⟩

/-- `lem:s02-tree`(c) (`s02-tree`): `SL₂(ℚ_q)` is transitive on the edges `EdgeO q`. -/
theorem SLq_transitive_edge (e : EdgeO q) : ∃ s : SLq q, s • e0 q = e := by
  obtain ⟨e, he⟩ := e
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  have hg : vdet q g = vdet q 1 := by
    rw [vdet_one]
    exact he
  obtain ⟨s, hs, z, hz, k, hk, hgs⟩ := exists_decomp g 1 hg
  exact ⟨⟨s, hs⟩, Subtype.ext (mk_eq_of_decomp (center_le_ZIw q) (Iw_le_ZIw q) hz hk hgs)⟩

/-! ### `lem:s02-tree`(c): stabilisers -/

variable (q)

/-- `lem:s02-tree`(c) (`s02-tree`): the stabiliser of `v₀` in `SL₂(ℚ_q)` is `SL₂(ℤ_q)`. -/
theorem stabilizer_v0 : MulAction.stabilizer (SLq q) (v0 q) = (SL2Zq q).subgroupOf (SLq q) := by
  ext ⟨s, hs⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : ((s * 1 : GL (Fin 2) ℚ_[q]) : Vert q) = ((1 : GL (Fin 2) ℚ_[q]) : Vert q) := h
    have h2 : s ∈ ZK q := by simpa using QuotientGroup.eq.1 h1
    exact mem_SL2Zq_iff.2 ⟨hs, mem_GL2Zl_of_mem_ZK h2 (norm_det_of_mem_SLq hs)⟩
  · intro h
    have hK : s ∈ GL2Zl q := (mem_SL2Zq_iff.1 h).2
    show ((s * 1 : GL (Fin 2) ℚ_[q]) : Vert q) = ((1 : GL (Fin 2) ℚ_[q]) : Vert q)
    exact QuotientGroup.eq.2 (by simpa using GL2Zl_le_ZK q hK)

/-- `lem:s02-tree`(c) (`s02-tree`): the stabiliser of `v₁` in `SL₂(ℚ_q)` is
`SL₂(ℚ_q) ∩ α GL₂(ℤ_q) α⁻¹`. -/
theorem stabilizer_v1 : MulAction.stabilizer (SLq q) (v1 q) = (K1q q).subgroupOf (SLq q) := by
  ext ⟨s, hs⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  have e : (s * alphaq q)⁻¹ * alphaq q = ((alphaq q)⁻¹ * s * alphaq q)⁻¹ := by group
  constructor
  · intro h
    have h1 : ((s * alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) =
        ((alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) := h
    have h2 := QuotientGroup.eq.1 h1
    rw [e, inv_mem_iff] at h2
    have hd : ‖(Units.val ((alphaq q)⁻¹ * s * alphaq q)).det‖ = 1 := by
      rw [det_conj_GL]
      exact norm_det_of_mem_SLq hs
    exact mem_K1q_iff.2 ⟨hs, mem_Kalpha_iff.2 (mem_GL2Zl_of_mem_ZK h2 hd)⟩
  · intro h
    have hK : s ∈ Kalpha q := (mem_K1q_iff.1 h).2
    show ((s * alphaq q : GL (Fin 2) ℚ_[q]) : Vert q) = ((alphaq q : GL (Fin 2) ℚ_[q]) : Vert q)
    refine QuotientGroup.eq.2 ?_
    rw [e, inv_mem_iff]
    exact GL2Zl_le_ZK q (mem_Kalpha_iff.1 hK)

/-- `lem:s02-tree`(c) (`s02-tree`): the stabiliser of `e₀` in `SL₂(ℚ_q)` is `SL₂(ℚ_q) ∩ Iw_q`. -/
theorem stabilizer_e0 : MulAction.stabilizer (SLq q) (e0 q) = (IwSL q).subgroupOf (SLq q) := by
  ext ⟨s, hs⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : ((s * 1 : GL (Fin 2) ℚ_[q]) : Edge q) = ((1 : GL (Fin 2) ℚ_[q]) : Edge q) :=
      congrArg Subtype.val h
    have h2 : s ∈ ZIw q := by simpa using QuotientGroup.eq.1 h1
    exact mem_IwSL_iff.2 ⟨hs, mem_Iw_of_mem_ZIw h2 (norm_det_of_mem_SLq hs)⟩
  · intro h
    have hI : s ∈ Iw q := (mem_IwSL_iff.1 h).2
    apply Subtype.ext
    show ((s * 1 : GL (Fin 2) ℚ_[q]) : Edge q) = ((1 : GL (Fin 2) ℚ_[q]) : Edge q)
    exact QuotientGroup.eq.2 (by simpa using Iw_le_ZIw q hI)

/-! ### The graph -/

/-- The tree as a simple graph on `Vert q`: `v ~ w` iff some `e : EdgeO q` has `{o e, t e} = {v, w}`
(`def:s02-tree`). -/
def graph : SimpleGraph (Vert q) where
  Adj v w := ∃ e : EdgeO q, s(oO q e, tO q e) = s(v, w)
  symm := ⟨fun _ _ ⟨e, h⟩ => ⟨e, h.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun v ⟨e, h⟩ => by
    have hot : oO q e = tO q e := by
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    have h3 := vtype_tO e
    rw [← hot, vtype_oO] at h3
    exact absurd h3 (by decide)⟩

variable {q}

/-- Adjacency in `graph q`, unfolded (`def:s02-tree`, `s02-tree`). -/
theorem graph_adj_iff {v w : Vert q} :
    (graph q).Adj v w ↔ ∃ e : EdgeO q, s(oO q e, tO q e) = s(v, w) := Iff.rfl

variable (q)

/-- `v₀ ~ v₁` via `e₀` (`def:s02-tree`, `s02-tree`). -/
theorem graph_adj_v0_v1 : (graph q).Adj (v0 q) (v1 q) :=
  ⟨e0 q, by rw [oO_e0, tO_e0]⟩

end

end Langlandscape.Tree
