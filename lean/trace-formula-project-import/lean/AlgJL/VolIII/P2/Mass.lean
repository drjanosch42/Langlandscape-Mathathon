import AlgJL.Meta.Tag
import AlgJL.VolIII.P2.MassDefs
import AlgJL.VolIII.P2.Ramification
import AlgJL.Hyp.EichlerMass
import AlgJL.VolIII.P1.Arith
import AlgJL.VolI.P0.Conventions
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Mass under change of level (Q2 U6, items 52–54, 56)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §5 (items 52–54 and 56 of `docs/sprints/Q2-plan.md` §1.2). The
definition of `mass` (item 51) lives in `MassDefs.lean` (plan §1.3).

* Item 52 is stated for any subgroups `U' ≤ U ≤ B̂^×` with the stabilizers `Γ_x(U)` of item 49 and the junk
  conventions of item 51 (`finsum`, `Nat.card`).
* Item 53 uses the Borel subgroup `B(R) ≤ GL₂(R)` of `I.conv.def:borel` with `R = ℤ/M` and `ψ` of
  `III.ef.def:dedekind-psi`.
* Item 54: `[Ô^× : Ô(M; φ)^×] = ψ(M)` and `Mass(O(M; φ)) = ψ(M) Mass(O)`; `M ≥ 1` is the `[NeZero M]` of
  `LevelStructure`.
* Item 56 takes the hypothesis `Hyp.EichlerMass a b D O` as an explicit argument (rule 12).
Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF GL2TF.Explicit

open scoped Pointwise

/-! ### Proof helpers for item 52 (orbit count on the fibres) -/


section OrbitCount

variable {G K : Type*} [Group G] [Group K] (ι : K →* G)

/-- Proof helper: the stabilizer `Γ_y(V) = ι⁻¹(y V y⁻¹)`. -/
theorem mem_stab_aux (V : Subgroup G) (y : G) (γ : K) :
    γ ∈ (V.map (MulAut.conj y).toMonoidHom).comap ι ↔ y⁻¹ * ι γ * y ∈ V := by
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, hwe⟩
    rw [← hwe]; group; exact hw
  · intro h
    exact ⟨_, h, by group⟩

/-- Proof helper: `|Γ_y(V)|` depends only on the double coset `ι(K) y V`. -/
theorem card_stab_aux (V : Subgroup G) (y : G) (k : K) (v : G) (hv : v ∈ V) :
    Nat.card ((V.map (MulAut.conj (ι k * y * v)).toMonoidHom).comap ι) =
      Nat.card ((V.map (MulAut.conj y).toMonoidHom).comap ι) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨k⁻¹ * γ * k, ?_⟩
      invFun := fun δ => ⟨k * δ * k⁻¹, ?_⟩
      left_inv := fun γ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun δ => Subtype.ext (by simp [mul_assoc]) }
  · have h := (mem_stab_aux ι V _ γ).mp γ.2
    rw [mem_stab_aux]
    have e : y⁻¹ * ι (k⁻¹ * γ * k) * y = v * ((ι k * y * v)⁻¹ * ι γ * (ι k * y * v)) * v⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e]
    exact V.mul_mem (V.mul_mem hv h) (V.inv_mem hv)
  · have h := (mem_stab_aux ι V _ δ).mp δ.2
    rw [mem_stab_aux]
    have e : (ι k * y * v)⁻¹ * ι (k * δ * k⁻¹) * (ι k * y * v) = v⁻¹ * (y⁻¹ * ι δ * y) * v := by
      simp only [map_mul, map_inv]; group
    rw [e]
    exact V.mul_mem (V.mul_mem (V.inv_mem hv) h) hv

/-- Proof helper: `|Γ_{q.out}(V)| = |Γ_y(V)|` for `q = [y]`. -/
theorem card_stab_out_aux (V : Subgroup G) (y : G) :
    Nat.card ((V.map (MulAut.conj (Quotient.out (DoubleCoset.mk ι.range V y))).toMonoidHom).comap ι) =
      Nat.card ((V.map (MulAut.conj y).toMonoidHom).comap ι) := by
  obtain ⟨h, ⟨k, rfl⟩, v, hv, he⟩ := DoubleCoset.mk_out_eq_mul ι.range V y
  rw [he, card_stab_aux ι V y k v hv]

/-- Proof helper: summing over a finite set through a surjection, weighted by fibre sizes. -/
theorem sum_eq_sum_div_fiber_aux {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (F : β → ℚ) :
    ∑ b, F b = ∑ a, F (g a) / ((Finset.univ.filter fun a' => g a' = g a).card : ℚ) := by
  rw [← Finset.sum_fiberwise Finset.univ g]
  refine Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a0, ha0⟩ := hg b
  have hne : ((Finset.univ.filter fun a' => g a' = b).card : ℚ) ≠ 0 := by
    have : a0 ∈ Finset.univ.filter fun a' => g a' = b := by simp [ha0]
    exact_mod_cast (Finset.card_pos.mpr ⟨a0, this⟩).ne'
  rw [Finset.sum_congr rfl (g := fun _ => F b / ((Finset.univ.filter fun a' => g a' = b).card : ℚ))]
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [ha.2]

/-- Proof helper: the generic orbit count behind item 52. -/
theorem orbit_count_aux (U' U : Subgroup G) (hle : U' ≤ U) (hidx : U'.relIndex U ≠ 0)
    (hfin : Finite (DoubleCoset.Quotient (ι.range : Set G) (U : Set G))) :
    ∑ᶠ c' : DoubleCoset.Quotient (ι.range : Set G) (U' : Set G),
        (1 : ℚ) / (Nat.card ((U'.map (MulAut.conj (Quotient.out c')).toMonoidHom).comap ι) : ℚ) =
      (U'.relIndex U : ℚ) * ∑ᶠ c : DoubleCoset.Quotient (ι.range : Set G) (U : Set G),
        (1 : ℚ) / (Nat.card ((U.map (MulAut.conj (Quotient.out c)).toMonoidHom).comap ι) : ℚ) := by
  classical
  set H := ι.range with hH
  set W := U'.subgroupOf U with hW
  have : W.FiniteIndex := ⟨hidx⟩
  have hXfin : Finite (U ⧸ W) := Subgroup.finite_quotient_of_finiteIndex
  let Φ : DoubleCoset.Quotient (H : Set G) (U : Set G) × (U ⧸ W) → DoubleCoset.Quotient (H : Set G) (U' : Set G) :=
    fun z => DoubleCoset.mk H U' (Quotient.out z.1 * ((Quotient.out z.2 : U) : G))
  have hΦ : Function.Surjective Φ := by
    intro d
    induction d using Quotient.inductionOn' with
    | h y =>
      obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul H U y
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W (⟨k, hk⟩ : U)⁻¹
      refine ⟨(DoubleCoset.mk H U y, QuotientGroup.mk (⟨k, hk⟩ : U)⁻¹), ?_⟩
      show DoubleCoset.mk H U' _ = DoubleCoset.mk H U' y
      rw [DoubleCoset.eq]
      refine ⟨h⁻¹, H.inv_mem hh, ((w : U) : G)⁻¹, U'.inv_mem (Subgroup.mem_subgroupOf.mp w.2), ?_⟩
      rw [hw, he]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
  have hQ'fin : Finite (DoubleCoset.Quotient (H : Set G) (U' : Set G)) := Finite.of_surjective Φ hΦ
  have : Fintype (DoubleCoset.Quotient (H : Set G) (U : Set G)) := Fintype.ofFinite _
  have : Fintype (DoubleCoset.Quotient (H : Set G) (U' : Set G)) := Fintype.ofFinite _
  have : Fintype (U ⧸ W) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, sum_eq_sum_div_fiber_aux Φ hΦ]
  have hcardX : (U'.relIndex U : ℚ) = (Fintype.card (U ⧸ W) : ℚ) := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcardX, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ) / (Nat.card ((U.map (MulAut.conj (Quotient.out c)).toMonoidHom).comap ι) : ℚ))]
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  intro q _
  -- the fibre over `(c, q)`
  set x := Quotient.out c with hx
  set u : U := Quotient.out q with hu
  set Γ := (U.map (MulAut.conj x).toMonoidHom).comap ι with hΓ
  let ρ : Γ →* U :=
    { toFun := fun γ => ⟨x⁻¹ * ι γ * x, (mem_stab_aux ι U x γ).mp γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun γ δ => Subtype.ext (by
        show x⁻¹ * ι ((γ * δ : Γ) : K) * x = (x⁻¹ * ι γ * x) * (x⁻¹ * ι δ * x)
        simp only [Subgroup.coe_mul, map_mul]; group) }
  let _ : MulAction Γ (U ⧸ W) := MulAction.compHom (U ⧸ W) ρ
  have hsmul : ∀ (γ : Γ) (v : U), (γ • (QuotientGroup.mk v : U ⧸ W)) = QuotientGroup.mk (ρ γ * v) := fun _ _ => rfl
  have hq : q = QuotientGroup.mk u := (QuotientGroup.out_eq' q).symm
  -- stabilizer
  have hstabiff : ∀ γ : Γ, γ • q = q ↔ (x * (u : G))⁻¹ * ι γ * (x * u) ∈ U' := by
    intro γ
    rw [hq, hsmul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((ρ γ * u)⁻¹ * u : U) : G) = ((x * (u : G))⁻¹ * ι γ * (x * u))⁻¹ := by
      show ((x⁻¹ * ι γ * x) * (u : G))⁻¹ * u = _
      group
    rw [e]
    exact ⟨fun h => by simpa using U'.inv_mem h, fun h => U'.inv_mem h⟩
  have hsub : ∀ δ : K, (x * (u : G))⁻¹ * ι δ * (x * u) ∈ U' → δ ∈ Γ := by
    intro δ h
    rw [mem_stab_aux]
    have e : x⁻¹ * ι δ * x = (u : G) * ((x * (u : G))⁻¹ * ι δ * (x * u)) * (u : G)⁻¹ := by group
    rw [e]
    exact U.mul_mem (U.mul_mem u.2 (hle h)) (U.inv_mem u.2)
  have hstab : Nat.card (MulAction.stabilizer Γ q) =
      Nat.card ((U'.map (MulAut.conj (x * (u : G))).toMonoidHom).comap ι) := by
    refine Nat.card_congr
      { toFun := fun γ => ⟨γ.1.1, (mem_stab_aux ι U' _ _).mpr ((hstabiff γ.1).mp γ.2)⟩
        invFun := fun δ => ⟨⟨δ.1, hsub δ.1 ((mem_stab_aux ι U' _ _).mp δ.2)⟩,
          (hstabiff _).mpr ((mem_stab_aux ι U' _ _).mp δ.2)⟩
        left_inv := fun γ => rfl
        right_inv := fun δ => rfl }
  -- fibre
  have hiff : ∀ z' : DoubleCoset.Quotient (H : Set G) (U : Set G) × (U ⧸ W),
      Φ z' = Φ (c, q) ↔ z'.1 = c ∧ z'.2 ∈ MulAction.orbit Γ q := by
    rintro ⟨c', q'⟩
    constructor
    · intro h
      have h1 : c' = c := by
        have hmap : ∀ z : DoubleCoset.Quotient (H : Set G) (U : Set G) × (U ⧸ W),
            DoubleCoset.mk H U (Quotient.out z.1 * ((Quotient.out z.2 : U) : G)) = z.1 := by
          intro z
          conv_rhs => rw [← DoubleCoset.out_eq' z.1]
          rw [DoubleCoset.eq]
          exact ⟨1, H.one_mem, ((Quotient.out z.2 : U) : G)⁻¹, U.inv_mem (Quotient.out z.2 : U).2, by group⟩
        obtain ⟨h0, hh0, k0, hk0, he0⟩ := DoubleCoset.eq.mp h
        calc c' = _ := (hmap (c', q')).symm
          _ = _ := DoubleCoset.eq.mpr ⟨h0, hh0, k0, hle hk0, he0⟩
          _ = c := hmap (c, q)
      rw [h1] at h
      refine ⟨h1, ?_⟩
      obtain ⟨h0, ⟨k, rfl⟩, w, hw, he⟩ := DoubleCoset.eq.mp h
      -- `x u = ι k x u' w`
      set u' : U := Quotient.out q' with hu'
      have he' : (x : G) * (u : G) = ι k * (x * (u' : G)) * w := he
      have hmemk : k⁻¹ ∈ Γ := by
        rw [mem_stab_aux]
        have e : x⁻¹ * ι k⁻¹ * x = (u' : G) * w * (u : G)⁻¹ := by
          rw [map_inv]
          calc _ = x⁻¹ * (ι k)⁻¹ * (x * (u : G)) * (u : G)⁻¹ := by group
            _ = _ := by rw [he']; group
        rw [e]
        exact U.mul_mem (U.mul_mem u'.2 (hle hw)) (U.inv_mem u.2)
      refine ⟨⟨k⁻¹, hmemk⟩, ?_⟩
      show (⟨k⁻¹, hmemk⟩ : Γ) • q = q'
      rw [hq, hsmul, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf, ← hu']
      have e : (((ρ ⟨k⁻¹, hmemk⟩ * u)⁻¹ * u' : U) : G) = w⁻¹ := by
        simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, InvMemClass.coe_inv, Subgroup.coe_mk]
        rw [map_inv]
        calc _ = ((x * (u : G))⁻¹ * ι k * x) * (u' : G) := by group
          _ = _ := by rw [he']; group
      rw [e]
      exact U'.inv_mem hw
    · rintro ⟨h1, γ, hγ⟩
      have hγ' : γ • q = q' := hγ
      show DoubleCoset.mk H U' (Quotient.out c' * ((Quotient.out q' : U) : G)) =
        DoubleCoset.mk H U' (x * (u : G))
      have h1' : c' = c := h1
      subst c'
      rw [← hγ', hq, hsmul]
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W (ρ γ * u)
      rw [hw, DoubleCoset.eq]
      refine ⟨(ι γ.1)⁻¹, H.inv_mem ⟨γ.1, rfl⟩, ((w : U) : G)⁻¹, U'.inv_mem (Subgroup.mem_subgroupOf.mp w.2), ?_⟩
      simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_mk]
      rw [← hx]
      group
  have hfib : ((Finset.univ.filter fun z' => Φ z' = Φ (c, q)).card : ℕ) =
      (MulAction.orbit Γ q).ncard := by
    rw [← Nat.card_coe_set_eq, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun z' => ⟨z'.1.2, ((hiff z'.1).mp z'.2).2⟩
        invFun := fun o => ⟨(c, o.1), (hiff _).mpr ⟨rfl, o.2⟩⟩
        left_inv := fun z' => Subtype.ext (Prod.ext ((hiff z'.1).mp z'.2).1.symm rfl)
        right_inv := fun o => rfl }
  have hos : Nat.card (MulAction.stabilizer Γ q) * (MulAction.orbit Γ q).ncard = Nat.card Γ := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  rw [card_stab_out_aux ι U' (x * (u : G)), hfib, ← hstab, div_div, one_div, one_div]
  congr 1
  exact_mod_cast hos

end OrbitCount



/-- For subgroups `U' ≤ U ≤ B̂^×` with `[U : U']` finite and `B^× \ B̂^× / U` finite (representatives `c.out`):
`Σ_{c'} 1/|Γ_{x_{c'}}(U')| = [U : U'] Σ_c 1/|Γ_{x_c}(U)|` in `ℚ` (junk conventions as in `III.qcls.def:mass`). -/
@[tf_id "III.qcls.lem:mass-orbit-count"]
theorem mass_orbit_count {a b : ℤ} (U' U : Subgroup (BHat a b)ˣ) (hle : U' ≤ U) (hidx : U'.relIndex U ≠ 0)
    (hfin : Finite (DoubleCoset.Quotient ((Units.map (finEmbed a b).toMonoidHom).range : Set (BHat a b)ˣ)
      (U : Set (BHat a b)ˣ))) :
    ∑ᶠ c' : DoubleCoset.Quotient ((Units.map (finEmbed a b).toMonoidHom).range : Set (BHat a b)ˣ)
        (U' : Set (BHat a b)ˣ), (1 : ℚ) / (Nat.card (classStabilizer U' (Quotient.out c')) : ℚ) =
      (U'.relIndex U : ℚ) *
        ∑ᶠ c : DoubleCoset.Quotient ((Units.map (finEmbed a b).toMonoidHom).range : Set (BHat a b)ˣ)
          (U : Set (BHat a b)ˣ), (1 : ℚ) / (Nat.card (classStabilizer U (Quotient.out c)) : ℚ) := by
  exact orbit_count_aux (Units.map (finEmbed a b).toMonoidHom) U' U hle hidx hfin

/-! ### Proof helpers for item 53 (primitive vectors) -/

section Borel53

open Matrix


section Borel

variable {R : Type*} [CommRing R]

/-- Proof helper: the column vector `e₀ = (1, 0)ᵀ`. -/
theorem borel_aux_e0_apply (g : GL (Fin 2) R) :
    g • (Matrix.of fun i (_ : Fin 1) => if i = 0 then (1 : R) else 0) =
      Matrix.of fun i (_ : Fin 1) => (g : Matrix (Fin 2) (Fin 2) R) i 0 := by
  ext i j
  simp [Matrix.mul_apply]

/-- Proof helper: the orbit of `e₀` under `GL₂(R)` is the set of primitive columns. -/
theorem borel_aux_orbit (v : Matrix (Fin 2) (Fin 1) R) :
    v ∈ MulAction.orbit (GL (Fin 2) R) (Matrix.of fun i (_ : Fin 1) => if i = 0 then (1 : R) else 0) ↔
      ∃ s t : R, s * v 0 0 + t * v 1 0 = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    dsimp only
    rw [borel_aux_e0_apply]
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    rw [Matrix.det_fin_two] at hu
    refine ⟨((u⁻¹ : Rˣ) : R) * (g : Matrix (Fin 2) (Fin 2) R) 1 1,
      -((u⁻¹ : Rˣ) : R) * (g : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩
    simp only [Matrix.of_apply]
    have : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
    rw [hu] at this
    linear_combination this
  · rintro ⟨s, t, h⟩
    let A : Matrix (Fin 2) (Fin 2) R := !![v 0 0, -t; v 1 0, s]
    have hA : A.det = 1 := by simp only [A, Matrix.det_fin_two_of]; linear_combination h
    refine ⟨Matrix.nonsingInvUnit A (by rw [hA]; exact isUnit_one), ?_⟩
    dsimp only
    rw [borel_aux_e0_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- Proof helper: `[GL₂(R) : B(R)] · |R^×|` is the number of primitive columns. -/
theorem borel_index_mul_card_units :
    (borel R).index * Nat.card Rˣ =
      Nat.card {v : Matrix (Fin 2) (Fin 1) R // ∃ s t : R, s * v 0 0 + t * v 1 0 = 1} := by
  set e0 : Matrix (Fin 2) (Fin 1) R := Matrix.of fun i (_ : Fin 1) => if i = 0 then (1 : R) else 0 with he0
  set S := MulAction.stabilizer (GL (Fin 2) R) e0 with hSdef
  have hmemS : ∀ g : GL (Fin 2) R, g ∈ S ↔ (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
    intro g
    rw [MulAction.mem_stabilizer_iff, borel_aux_e0_apply]
    constructor
    · intro h
      exact ⟨by simpa [e0] using congrFun (congrFun h 0) 0, by simpa [e0] using congrFun (congrFun h 1) 0⟩
    · rintro ⟨h0, h1⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [e0, h0, h1]
  have hS : S ≤ borel R := fun g hg => ((hmemS g).mp hg).2
  have hmemB : ∀ g : GL (Fin 2) R, g ∈ borel R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := fun _ => Iff.rfl
  have h00 : ∀ g h : GL (Fin 2) R, (h : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 →
      ((g * h : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (h : Matrix (Fin 2) (Fin 2) R) 0 0 := by
    intro g h hh
    simp [Matrix.mul_apply, Fin.sum_univ_two, hh]
  let χ : borel R →* Rˣ := MonoidHom.mk' (fun g => ⟨(g.1 : Matrix (Fin 2) (Fin 2) R) 0 0,
      ((g.1⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0,
      by rw [← h00 _ _ ((hmemB _).mp ((borel R).inv_mem g.2)), mul_inv_cancel]; simp,
      by rw [← h00 _ _ ((hmemB _).mp g.2), inv_mul_cancel]; simp⟩)
    (fun g h => Units.ext (by simp only [Subgroup.coe_mul]; exact h00 _ _ ((hmemB _).mp h.2)))
  have hker : χ.ker = S.subgroupOf (borel R) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemS]
    constructor
    · intro h; exact ⟨congrArg Units.val h, (hmemB _).mp g.2⟩
    · rintro ⟨h, -⟩; exact Units.ext h
  have hsurj : Function.Surjective χ := by
    intro t
    let d : GL (Fin 2) R := Matrix.nonsingInvUnit !![(t : R), 0; 0, 1] (by
      rw [Matrix.det_fin_two_of]; simp)
    refine ⟨⟨d, by rw [hmemB]; rfl⟩, Units.ext ?_⟩
    rfl
  have hrel : S.relIndex (borel R) = Nat.card Rˣ := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  have hidx : S.index = Nat.card {v : Matrix (Fin 2) (Fin 1) R // ∃ s t : R, s * v 0 0 + t * v 1 0 = 1} := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => borel_aux_orbit v)
  rw [← hidx, ← Subgroup.relIndex_mul_index hS, hrel, mul_comm]

end Borel

section Prim

/-- Proof helper: primitive pairs are invariant under ring isomorphisms. -/
theorem primPairs_card_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Nat.card {xy : R × R // ∃ s t : R, s * xy.1 + t * xy.2 = 1} =
      Nat.card {xy : S × S // ∃ s t : S, s * xy.1 + t * xy.2 = 1} := by
  refine Nat.card_congr ((Equiv.prodCongr e.toEquiv e.toEquiv).subtypeEquiv fun xy => ⟨?_, ?_⟩)
  · rintro ⟨s, t, h⟩
    refine ⟨e s, e t, ?_⟩
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, RingEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe]
    rw [← map_mul, ← map_mul, ← map_add, h, map_one]
  · rintro ⟨s, t, h⟩
    refine ⟨e.symm s, e.symm t, e.injective ?_⟩
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, RingEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe] at h
    rw [map_add, map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, h, map_one]

/-- Proof helper: primitive pairs of a product ring. -/
theorem primPairs_card_prod {R S : Type*} [CommRing R] [CommRing S] :
    Nat.card {xy : (R × S) × (R × S) // ∃ s t : R × S, s * xy.1 + t * xy.2 = 1} =
      Nat.card {xy : R × R // ∃ s t : R, s * xy.1 + t * xy.2 = 1} *
        Nat.card {xy : S × S // ∃ s t : S, s * xy.1 + t * xy.2 = 1} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun xy => (⟨(xy.1.1.1, xy.1.2.1), by
          obtain ⟨s, t, h⟩ := xy.2; exact ⟨s.1, t.1, congrArg Prod.fst h⟩⟩,
        ⟨(xy.1.1.2, xy.1.2.2), by
          obtain ⟨s, t, h⟩ := xy.2; exact ⟨s.2, t.2, congrArg Prod.snd h⟩⟩)
      invFun := fun xy => ⟨((xy.1.1.1, xy.2.1.1), (xy.1.1.2, xy.2.1.2)), by
          obtain ⟨s, t, h⟩ := xy.1.2
          obtain ⟨s', t', h'⟩ := xy.2.2
          exact ⟨(s, s'), (t, t'), Prod.ext h h'⟩⟩
      left_inv := fun xy => rfl
      right_inv := fun xy => rfl }

/-- Proof helper: primitive pairs of a finite local ring. -/
theorem primPairs_card_local {R : Type*} [CommRing R] [IsLocalRing R] [Finite R] :
    Nat.card {xy : R × R // ∃ s t : R, s * xy.1 + t * xy.2 = 1} =
      Nat.card R ^ 2 - (Nat.card R - Nat.card Rˣ) ^ 2 := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hiff : ∀ xy : R × R, (∃ s t : R, s * xy.1 + t * xy.2 = 1) ↔ ¬ (¬ IsUnit xy.1 ∧ ¬ IsUnit xy.2) := by
    intro xy
    constructor
    · rintro ⟨s, t, h⟩ ⟨h1, h2⟩
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
      · exact h1 (isUnit_of_mul_isUnit_right h')
      · exact h2 (isUnit_of_mul_isUnit_right h')
    · intro h
      rw [not_and_or, not_not, not_not] at h
      rcases h with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact ⟨((u⁻¹ : Rˣ) : R), 0, by rw [← hu, Units.inv_mul, zero_mul, add_zero]⟩
      · exact ⟨0, ((u⁻¹ : Rˣ) : R), by rw [← hu, Units.inv_mul, zero_mul, zero_add]⟩
  have hU : Nat.card {x : R // IsUnit x} = Nat.card Rˣ :=
    Nat.card_congr
      { toFun := fun x => x.2.unit
        invFun := fun u => ⟨u, u.isUnit⟩
        left_inv := fun x => rfl
        right_inv := fun u => Units.ext rfl }
  have hN : Nat.card {x : R // ¬ IsUnit x} = Nat.card R - Nat.card Rˣ := by
    rw [← hU, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod,
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun x : R => ¬ IsUnit x) (q := fun x : R => ¬ IsUnit x)),
    Nat.card_prod, hN, sq, sq]

/-- Proof helper: the number of primitive pairs over `ℤ/M`, `M ≥ 1`. -/
theorem primPairs_card_zmod (M : ℕ) (hM : 0 < M) :
    (Nat.card {xy : ZMod M × ZMod M // ∃ s t : ZMod M, s * xy.1 + t * xy.2 = 1} : ℚ) =
      (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd hM (lt_irrefl 0)
  | one =>
    have : Nat.card {xy : ZMod 1 × ZMod 1 // ∃ s t : ZMod 1, s * xy.1 + t * xy.2 = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨(0, 0), 0, 0, Subsingleton.elim _ _⟩⟩⟩
    rw [this]; simp
  | prime_pow p n hp hn =>
    have hp' : p.Prime := hp
    have : Fact p.Prime := ⟨hp'⟩
    have : NeZero n := ⟨hn.ne'⟩
    rw [primPairs_card_local, Nat.card_zmod, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp' hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : p ^ (m + 1) - p ^ (m + 1 - 1) * (p - 1) = p ^ m := by
      rw [Nat.add_sub_cancel]
      have : p ^ (m + 1) = p ^ m * (p - 1) + p ^ m := by
        rw [pow_succ, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp'.one_le]
      omega
    rw [h1, Nat.primeFactors_prime_pow (by omega) hp', Finset.prod_singleton]
    have hle : (p ^ m) ^ 2 ≤ (p ^ (m + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right hp'.pos (by omega)) 2
    rw [Nat.cast_sub hle]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    push_cast
    field_simp
    ring
  | coprime a b ha hb hab iha ihb =>
    have hc := primPairs_card_ringEquiv (ZMod.chineseRemainder hab)
    rw [hc, primPairs_card_prod, Nat.cast_mul, iha (by omega), ihb (by omega), hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors]
    push_cast
    ring

end Prim

end Borel53

/-- For `M ≥ 1`: `[GL₂(ℤ/M) : B₀(ℤ/M)] = ψ(M)`, with `B₀` the upper triangular subgroup. -/
@[tf_id "III.qcls.lem:gl2-borel-index"]
theorem gl2_borel_index (M : ℕ) (hM : 1 ≤ M) : ((borel (ZMod M)).index : ℚ) = dedekindPsi M := by
  have : NeZero M := ⟨by omega⟩
  have h := borel_index_mul_card_units (R := ZMod M)
  have hprim : Nat.card {v : Matrix (Fin 2) (Fin 1) (ZMod M) // ∃ s t : ZMod M, s * v 0 0 + t * v 1 0 = 1} =
      Nat.card {xy : ZMod M × ZMod M // ∃ s t : ZMod M, s * xy.1 + t * xy.2 = 1} :=
    Nat.card_congr
      { toFun := fun v => ⟨(v.1 0 0, v.1 1 0), v.2⟩
        invFun := fun xy => ⟨Matrix.of fun i (_ : Fin 1) => if i = 0 then xy.1.1 else xy.1.2, by
          simpa using xy.2⟩
        left_inv := fun v => by
          apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
        right_inv := fun xy => rfl }
  rw [hprim, Nat.card_eq_fintype_card (α := (ZMod M)ˣ), ZMod.card_units_eq_totient] at h
  have hq : ((borel (ZMod M)).index : ℚ) * (Nat.totient M : ℚ) =
      (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
    rw [← primPairs_card_zmod M (by omega), ← h]; push_cast; ring
  have htot : (Nat.totient M : ℚ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  rw [Nat.totient_eq_mul_prod_factors] at hq htot
  rw [dedekindPsi]
  have hsplit : (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) =
      ((M : ℚ) * ∏ p ∈ M.primeFactors, (1 - (p : ℚ)⁻¹)) * ((M : ℚ) * ∏ p ∈ M.primeFactors, (1 + 1 / (p : ℚ))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, sq]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
    ring
  rw [hsplit, mul_comm ((M : ℚ) * _)] at hq
  exact mul_right_cancel₀ htot hq


/-! ### Proof helpers for item 54 (the reduction `Ô^× → GL₂(ℤ/M)`) -/

section Level54

open Matrix


/-- Proof helper: `L̂ = ι(L) + N L̂`. -/
theorem exists_approx_latticeCompletion {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (N : ℕ) (hN : 0 < N) {w : BHat a b}
    (hw : w ∈ latticeCompletion L) :
    ∃ z ∈ L, ∃ w' ∈ latticeCompletion L, w = finEmbed a b z + (N : FinAdele) • w' := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, -, hF3⟩ := exists_bhat_basis e f hf
  have hc := (hF3 w).mp hw
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : (N : FinAdele) * algebraMap ℚ FinAdele ((N : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hNq, map_one]
  have happ : ∀ i, ∃ m : ℤ, ∃ d ∈ Zhat, F.repr w i = (m : FinAdele) + (N : FinAdele) * d := by
    intro i
    obtain ⟨q, hq⟩ := finAdele_exists_sub_mem_zhat (algebraMap ℚ FinAdele ((N : ℚ)⁻¹) * F.repr w i)
    set d := algebraMap ℚ FinAdele ((N : ℚ)⁻¹) * F.repr w i - algebraMap ℚ FinAdele q with hd
    have hc' : F.repr w i = algebraMap ℚ FinAdele ((N : ℚ) * q) + (N : FinAdele) * d := by
      rw [hd, map_mul, map_natCast]
      linear_combination (-(F.repr w i)) * key
    have hm : algebraMap ℚ FinAdele ((N : ℚ) * q) ∈ Zhat := by
      have : algebraMap ℚ FinAdele ((N : ℚ) * q) = F.repr w i - (N : FinAdele) * d := by rw [hc']; ring
      rw [this]; exact Zhat.sub_mem (hc i) (Zhat.mul_mem (natCast_mem Zhat _) hq)
    obtain ⟨m, hm'⟩ := rat_isInt_of_mem_zhat _ hm
    exact ⟨m, d, hq, by rw [hc', hm', map_intCast]⟩
  choose m d hd hmd using happ
  refine ⟨∑ i, m i • (e i : QuatAlg ℚ a b), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e i).2,
    ∑ i, d i • F i, ?_, ?_⟩
  · rw [hF3]; intro i; rw [Module.Basis.repr_sum_self]; exact hd i
  · conv_lhs => rw [← F.sum_repr w]
    rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmd, add_smul, smul_smul, map_zsmul, hF1, hf, ← Int.cast_smul_eq_zsmul FinAdele]

/-- Proof helper: `ι⁻¹(N L̂) = N L`. -/
theorem eq_nsmul_of_finEmbed_eq {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (N : ℕ) (hN : 0 < N) {z : QuatAlg ℚ a b}
    {w : BHat a b} (hw : w ∈ latticeCompletion L) (h : finEmbed a b z = (N : FinAdele) • w) :
    ∃ y ∈ L, z = N • y := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨((N : ℚ)⁻¹) • z, ?_, ?_⟩
  · have hpre := preimage_latticeCompletion L hfg hspan
    have : finEmbed a b (((N : ℚ)⁻¹) • z) = w := by
      rw [show finEmbed a b (((N : ℚ)⁻¹) • z) = algebraMap ℚ FinAdele ((N : ℚ)⁻¹) • finEmbed a b z from
        baseChange_algebraMap_smul a b _ _, h, smul_smul, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul,
        inv_mul_cancel₀ hNq, map_one, one_smul]
    have hmem : ((N : ℚ)⁻¹) • z ∈ finEmbed a b ⁻¹' (latticeCompletion L : Set (BHat a b)) := by
      rw [Set.mem_preimage, this]; exact hw
    rw [hpre] at hmem; exact hmem
  · rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hNq, one_smul]

/-- Proof helper: the reduction `Ô^× → GL₂(ℤ/M)` attached to a level structure, with kernel-side description of
`Ô(M; φ)^×` and its values on approximations. -/
theorem exists_level_hom {a b : ℤ} (O : QOrder a b) {M : ℕ} [NeZero M] (φ : LevelStructure O M) :
    ∃ Ψ : orderCompletionUnits O →* GL (Fin 2) (ZMod M),
      (orderCompletionUnits (eichlerOrder φ)).subgroupOf (orderCompletionUnits O) = (borel (ZMod M)).comap Ψ ∧
      ∀ (u : orderCompletionUnits O) (z : QuatAlg ℚ a b) (hz : z ∈ O.toSubalgebra) (w' : BHat a b),
        w' ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) →
        ((u : (BHat a b)ˣ) : BHat a b) = finEmbed a b z + (M : FinAdele) • w' →
        ((Ψ u : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = φ.toRingHom ⟨z, hz⟩ := by
  classical
  set Oh := latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) with hOh
  set Eh := latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) with hEh
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have happ : ∀ w ∈ Oh, ∃ z ∈ Subalgebra.toSubmodule O.toSubalgebra, ∃ w' ∈ Oh,
      w = finEmbed a b z + (M : FinAdele) • w' :=
    fun w hw => exists_approx_latticeCompletion _ O.fg O.span_eq_top M hM hw
  choose! zf hzf w'f hw'f hwe using happ
  have hMzero : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod M), M • A = 0 := by
    intro A; ext i j; simp [ZMod.natCast_self]
  have hsmul : ∀ x : BHat a b, (M : FinAdele) • x = (M : BHat a b) * x := by
    intro x; rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  -- well-definedness
  have hC1 : ∀ (w : BHat a b) (hw : w ∈ Oh) (z : QuatAlg ℚ a b) (hz : z ∈ O.toSubalgebra) (w' : BHat a b),
      w' ∈ Oh → w = finEmbed a b z + (M : FinAdele) • w' →
      φ.toRingHom ⟨zf w, hzf w hw⟩ = φ.toRingHom ⟨z, hz⟩ := by
    intro w hw z hz w' hw' he
    have h1 := hwe w hw
    have hdiff : finEmbed a b (zf w - z) = (M : FinAdele) • (w' - w'f w) := by
      rw [map_sub, smul_sub]
      have := h1.symm.trans he
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    obtain ⟨y, hy, hye⟩ := eq_nsmul_of_finEmbed_eq _ O.fg O.span_eq_top M hM
      (Submodule.sub_mem _ hw' (hw'f w hw)) hdiff
    have : (⟨zf w, hzf w hw⟩ : O.toSubalgebra) = ⟨z, hz⟩ + M • ⟨y, hy⟩ := by
      apply Subtype.ext
      show zf w = z + M • y
      rw [← hye]; abel
    rw [this, RingHom.map_add, map_nsmul, hMzero, add_zero]
  have hι : ∀ y ∈ O.toSubalgebra, finEmbed a b y ∈ Oh := fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hOmul : ∀ x ∈ Oh, ∀ y ∈ Oh, x * y ∈ Oh := fun x hx y hy => mul_mem_orderCompletion O hx hy
  have hOsmul : ∀ x ∈ Oh, (M : FinAdele) • x ∈ Oh := fun x hx =>
    smul_mem_latticeCompletion _ (natCast_mem Zhat M) hx
  -- multiplicativity
  have hFmul : ∀ (w1 : BHat a b) (h1 : w1 ∈ Oh) (w2 : BHat a b) (h2 : w2 ∈ Oh),
      φ.toRingHom ⟨zf (w1 * w2), hzf _ (hOmul _ h1 _ h2)⟩ =
        φ.toRingHom ⟨zf w1, hzf w1 h1⟩ * φ.toRingHom ⟨zf w2, hzf w2 h2⟩ := by
    intro w1 h1 w2 h2
    have hv1 : w'f w1 ∈ Oh := hw'f w1 h1
    have hv2 : w'f w2 ∈ Oh := hw'f w2 h2
    have hz1 : zf w1 ∈ O.toSubalgebra := hzf w1 h1
    have hz2 : zf w2 ∈ O.toSubalgebra := hzf w2 h2
    have he : w1 * w2 = finEmbed a b (zf w1 * zf w2) + (M : FinAdele) •
        (w'f w1 * finEmbed a b (zf w2) + finEmbed a b (zf w1) * w'f w2 + (M : FinAdele) • (w'f w1 * w'f w2)) := by
      conv_lhs => rw [hwe w1 h1, hwe w2 h2]
      simp only [map_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
      abel
    rw [hC1 _ (hOmul _ h1 _ h2) (zf w1 * zf w2) (O.toSubalgebra.mul_mem hz1 hz2) _
      (Oh.add_mem (Oh.add_mem (hOmul _ hv1 _ (hι _ hz2)) (hOmul _ (hι _ hz1) _ hv2)) (hOsmul _ (hOmul _ hv1 _ hv2))) he]
    rw [← RingHom.map_mul]; rfl
  have hone : (1 : BHat a b) ∈ Oh := one_mem_orderCompletion O
  have hF1 : φ.toRingHom ⟨zf 1, hzf 1 hone⟩ = 1 := by
    rw [hC1 1 hone 1 O.toSubalgebra.one_mem 0 (Submodule.zero_mem _) (by simp)]
    exact RingHom.map_one _
  have hEO : ∀ x ∈ Eh, x ∈ Oh := fun x hx =>
    Submodule.span_mono (Set.image_mono (eichlerSubalgebra_le φ)) hx
  have hMsub : ∀ w' ∈ Oh, (M : FinAdele) • w' ∈ Eh := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      have : finEmbed a b ((M : ℤ) • y) = (M : FinAdele) • finEmbed a b y := by
        rw [map_zsmul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
      rw [← this]
      exact Submodule.subset_span ⟨_, zsmul_mem_eichlerSubalgebra φ hy, rfl⟩
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      show (M : FinAdele) • ((c : FinAdele) • x) ∈ Eh
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_latticeCompletion _ c.2 hx
  have hEmem : ∀ (w : BHat a b) (hw : w ∈ Oh), w ∈ Eh ↔ φ.toRingHom ⟨zf w, hzf w hw⟩ 1 0 = 0 := by
    intro w hw
    constructor
    · intro hwE
      obtain ⟨z, ⟨hzO, h0⟩, w', hw', he⟩ :=
        exists_approx_latticeCompletion _ (eichlerOrder φ).fg (eichlerOrder φ).span_eq_top M hM hwE
      rw [hC1 w hw z hzO w' (hEO _ hw') he]
      exact h0
    · intro h
      rw [hwe w hw]
      exact Eh.add_mem (Submodule.subset_span ⟨zf w, ⟨hzf w hw, h⟩, rfl⟩) (hMsub _ (hw'f w hw))
  let F : orderCompletionUnits O → Matrix (Fin 2) (Fin 2) (ZMod M) :=
    fun u => φ.toRingHom ⟨zf ((u : (BHat a b)ˣ) : BHat a b), hzf _ u.2.1⟩
  have hFmul' : ∀ u v : orderCompletionUnits O, F (u * v) = F u * F v := fun u v => hFmul _ u.2.1 _ v.2.1
  have hF1' : F 1 = 1 := hF1
  let Ψ : orderCompletionUnits O →* GL (Fin 2) (ZMod M) :=
    { toFun := fun u => ⟨F u, F u⁻¹, by rw [← hFmul', mul_inv_cancel, hF1'],
        by rw [← hFmul', inv_mul_cancel, hF1']⟩
      map_one' := Units.ext hF1'
      map_mul' := fun u v => Units.ext (hFmul' u v) }
  refine ⟨Ψ, ?_, fun u z hz w' hw' he => hC1 _ u.2.1 z hz w' hw' he⟩
  ext u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · rintro ⟨h1, -⟩
    exact (hEmem _ u.2.1).mp h1
  · intro h
    have hinv := (borel (ZMod M)).inv_mem h
    exact ⟨(hEmem _ u.2.1).mpr h, (hEmem _ (u⁻¹).2.1).mpr hinv⟩

/-- Proof helper: if `φ(z)` is invertible, `nrd(z)` is prime to `M`. -/
theorem nrd_not_dvd_of_isUnit {a b : ℤ} {O : QOrder a b} {M : ℕ} [NeZero M] (φ : LevelStructure O M)
    {z : QuatAlg ℚ a b} (hz : z ∈ O.toSubalgebra) (hu : IsUnit (φ.toRingHom ⟨z, hz⟩)) (p : ℕ) (hp : p.Prime)
    (hpM : p ∣ M) (n : ℤ) (hn : nrd z = n) : ¬ (p : ℤ) ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨k, hk⟩
  let π : ZMod M →+* ZMod p := ZMod.castHom hpM (ZMod p)
  let φp : O.toSubalgebra →+* Matrix (Fin 2) (Fin 2) (ZMod p) := π.mapMatrix.comp φ.toRingHom
  have hsurj : Function.Surjective φp := by
    intro A
    let B : Matrix (Fin 2) (Fin 2) (ZMod M) := Matrix.of fun i j => (ZMod.castHom_surjective hpM (A i j)).choose
    obtain ⟨x, hx⟩ := φ.surjective B
    refine ⟨x, ?_⟩
    simp only [φp, RingHom.comp_apply, hx]
    ext i j
    exact (ZMod.castHom_surjective hpM (A i j)).choose_spec
  have hint : ∀ m : ℤ, ((m : O.toSubalgebra) : QuatAlg ℚ a b) = algebraMap ℚ (QuatAlg ℚ a b) (m : ℚ) := by
    intro m; rw [map_intCast]; rfl
  have hcastM : ∀ m : ℤ, ((m : ZMod p) = 0) → ((m : Matrix (Fin 2) (Fin 2) (ZMod p)) = 0) := by
    intro m hm
    rw [← zsmul_one, ← Int.cast_smul_eq_zsmul (ZMod p), hm, zero_smul]
  have hentry : ∀ (m : ℤ) (X : Matrix (Fin 2) (Fin 2) (ZMod p)),
      ((m : Matrix (Fin 2) (Fin 2) (ZMod p)) * X) 0 1 = (m : ZMod p) * X 0 1 := by
    intro m X
    rw [← zsmul_eq_mul, Matrix.smul_apply, zsmul_eq_mul]
  have hentry1 : ∀ m : ℤ, (m : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
    intro m
    rw [← zsmul_one, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]
  set Z : O.toSubalgebra := ⟨z, hz⟩
  set Zs : O.toSubalgebra := ⟨star z, star_mem_order O hz⟩
  have hZZs : Z * Zs = (n : O.toSubalgebra) := by
    apply Subtype.ext
    show z * star z = _
    rw [(mul_star_eq_nrd z).1, hn, hint]
  have hA : IsUnit (φp Z) := hu.map π.mapMatrix.toMonoidHom
  have hZs0 : φp Zs = 0 := by
    have h := congrArg φp hZZs
    rw [RingHom.map_mul, map_intCast φp, hcastM n (by rw [hk]; push_cast; simp)] at h
    exact (hA.mul_right_eq_zero).mp h
  obtain ⟨⟨t, ht⟩, -⟩ := trd_nrd_int_of_mem O hz
  have hZt : Z + Zs = (t : O.toSubalgebra) := by
    apply Subtype.ext
    show z + star z = _
    rw [add_star_eq_trd, ht, hint]
  have hAt : φp Z = (t : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    have h := congrArg φp hZt
    rw [RingHom.map_add, hZs0, add_zero, map_intCast φp] at h
    exact h
  have ht0 : (t : ZMod p) ≠ 0 := by
    intro h0
    rw [hAt, hcastM t h0] at hA
    exact not_isUnit_zero hA
  have hall : ∀ W : O.toSubalgebra, φp W 0 1 = 0 := by
    intro W
    obtain ⟨⟨tw, htw⟩, -⟩ := trd_nrd_int_of_mem O (O.toSubalgebra.mul_mem hz W.2)
    set Ws : O.toSubalgebra := ⟨star (W : QuatAlg ℚ a b), star_mem_order O W.2⟩
    have hW : Z * W + Ws * Zs = (tw : O.toSubalgebra) := by
      apply Subtype.ext
      show z * W + star (W : QuatAlg ℚ a b) * star z = _
      rw [← star_mul, add_star_eq_trd, htw, hint]
    have h := congrArg φp hW
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, hZs0, mul_zero, add_zero, map_intCast φp, hAt] at h
    have h01 := congrFun (congrFun h 0) 1
    rw [hentry, hentry1] at h01
    exact (mul_eq_zero.mp h01).resolve_left ht0
  obtain ⟨W, hW⟩ := hsurj !![0, 1; 0, 0]
  have := hall W
  rw [hW] at this
  simp at this

/-! ### Local helpers (copied from `ClassSet.lean`, where they are private) -/

/-- Proof helper: the evaluation `B̂ → B_{ℚ_p}` at a prime `p`. -/
private noncomputable abbrev evPM (a b : ℤ) (p : Nat.Primes) : QuatAlg FinAdele a b →+* QuatAlg ℚ_[p] a b :=
  baseChange a b (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p : FinAdele →+* ℚ_[p])

private theorem evP_finEmbed_auxM {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ a b) :
    evPM a b p (finEmbed a b z) = baseChange a b (algebraMap ℚ ℚ_[p]) z := by
  ext <;> rfl

private theorem evP_smul_auxM {a b : ℤ} (p : Nat.Primes) (c : FinAdele) (v : QuatAlg FinAdele a b) :
    evPM a b p (c • v) = (c p) • evPM a b p v := by
  ext <;> simp [baseChange]

private theorem bhat_ext_auxM {a b : ℤ} {v w : QuatAlg FinAdele a b} (h : ∀ p, evPM a b p v = evPM a b p w) : v = w := by
  apply QuaternionAlgebra.ext
  · ext p; exact congrArg QuaternionAlgebra.re (h p)
  · ext p; exact congrArg QuaternionAlgebra.imI (h p)
  · ext p; exact congrArg QuaternionAlgebra.imJ (h p)
  · ext p; exact congrArg QuaternionAlgebra.imK (h p)

private theorem mem_padicInt_range_auxM (p : Nat.Primes) (x : ℚ_[p]) :
    x ∈ (algebraMap ℤ_[p] ℚ_[p]).range ↔ x ∈ PadicInt.subring p :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- Proof helper: membership in `L̂` is local. -/
private theorem mem_latticeCompletion_iff_local_auxM {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hfg : L.FG)
    (hspan : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (w : BHat a b) :
    w ∈ latticeCompletion L ↔ ∀ p : Nat.Primes, evPM a b p w ∈
      Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' (L : Set (QuatAlg ℚ a b))) := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hfg hspan
  obtain ⟨F, hF1, _, hF3⟩ := exists_bhat_basis e f hf
  have hloc : ∀ p : Nat.Primes, ∃ Fp : Module.Basis (Fin 4) ℚ_[p] (QuatAlg ℚ_[p] a b),
      (∀ i, Fp i = baseChange a b (algebraMap ℚ ℚ_[p]) (f i)) ∧
      ∀ i, Fp.repr (evPM a b p w) i = F.repr w i p := by
    intro p
    obtain ⟨Fp, hFp1, -⟩ := exists_baseChange_basis (S := ℚ_[p]) a b f
    refine ⟨Fp, hFp1, fun i => ?_⟩
    have : evPM a b p w = ∑ j, (F.repr w j p) • Fp j := by
      conv_lhs => rw [← F.sum_repr w]
      erw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [evP_smul_auxM]; rw [hF1]; erw [evP_finEmbed_auxM]; rw [hFp1]
    rw [this, Module.Basis.repr_sum_self]
  choose Fp hFp1 hFp2 using hloc
  rw [hF3]
  have hspan_iff : ∀ p : Nat.Primes, evPM a b p w ∈ Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) ''
      (L : Set (QuatAlg ℚ a b))) ↔ ∀ i, F.repr w i p ∈ PadicInt.subring p := by
    intro p
    refine (mem_span_image_iff_repr (R := ℤ_[p]) e (baseChange a b (algebraMap ℚ ℚ_[p])).toAddMonoidHom (Fp p)
      (fun i => by rw [← hf]; exact hFp1 p i) _).trans ?_
    simp only [hFp2, mem_padicInt_range_auxM]
  simp only [hspan_iff, mem_zhat]
  exact ⟨fun h p i => h i p, fun h i p => h p i⟩

/-- Proof helper: the element of `B̂` with `p`-components `g p` (`p ∈ S`) and `1` (`p ∉ S`). -/
private noncomputable def glueAuxM {a b : ℤ} (S : Finset Nat.Primes) (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) :
    QuatAlg FinAdele a b :=
  (QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele)).symm fun k =>
    ⟨fun p => QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ_[p]) 0 ((b : ℤ) : ℚ_[p])
      (haveI := Classical.propDecidable (p ∈ S); if p ∈ S then g p else 1) k, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with p hp
      have hp' : p ∉ S := hp
      simp only [hp', ite_false]
      fin_cases k <;> simp⟩

private theorem evP_glueAuxM {a b : ℤ} (S : Finset Nat.Primes) (g : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b)
    (p : Nat.Primes) : evPM a b p (glueAuxM S g) = if p ∈ S then g p else 1 := by
  classical
  have e : (@ite _ (p ∈ S) (Classical.propDecidable _) (g p) 1) = if p ∈ S then g p else 1 := by
    congr
  apply QuaternionAlgebra.ext
  · exact congrArg QuaternionAlgebra.re e
  · exact congrArg QuaternionAlgebra.imI e
  · exact congrArg QuaternionAlgebra.imJ e
  · exact congrArg QuaternionAlgebra.imK e

/-- Proof helper: base change of a rational scalar. -/
private theorem baseChange_algebraMap_scalarM {a b : ℤ} (p : Nat.Primes) (q : ℚ) :
    baseChange a b (algebraMap ℚ ℚ_[p]) (algebraMap ℚ (QuatAlg ℚ a b) q) =
      algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) (q : ℚ_[p]) := by
  ext <;> simp [baseChange]

/-- Proof helper: the reduction `Ô^× → GL₂(ℤ/M)` is surjective (local gluing at the primes dividing `M`). -/
theorem level_hom_surjective {a b : ℤ} (O : QOrder a b) {M : ℕ} [NeZero M] (φ : LevelStructure O M)
    (Ψ : orderCompletionUnits O →* GL (Fin 2) (ZMod M))
    (hΨ : ∀ (u : orderCompletionUnits O) (z : QuatAlg ℚ a b) (hz : z ∈ O.toSubalgebra) (w' : BHat a b),
        w' ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) →
        ((u : (BHat a b)ˣ) : BHat a b) = finEmbed a b z + (M : FinAdele) • w' →
        ((Ψ u : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = φ.toRingHom ⟨z, hz⟩) :
    Function.Surjective Ψ := by
  classical
  intro g
  obtain ⟨⟨z, hz⟩, hzg⟩ := φ.surjective (g : Matrix (Fin 2) (Fin 2) (ZMod M))
  have hu : IsUnit (φ.toRingHom ⟨z, hz⟩) := hzg ▸ g.isUnit
  obtain ⟨-, n, hn⟩ := trd_nrd_int_of_mem O hz
  set S : Finset Nat.Primes := M.primeFactors.subtype Nat.Prime with hSdef
  have hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∣ M := by
    intro p
    have h1 : p ∈ S ↔ (p : ℕ) ∈ M.primeFactors := Finset.mem_subtype
    rw [h1, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨p.2, h, NeZero.ne M⟩⟩
  have hnp : ∀ p ∈ S, ‖((n : ℤ) : ℚ_[p])‖ = 1 := by
    intro p hp
    rw [Padic.norm_intCast_eq_one_iff]
    have := nrd_not_dvd_of_isUnit φ hz hu p p.2 ((hS p).mp hp) n hn
    exact ((Nat.prime_iff_prime_int.mp p.2).coprime_iff_not_dvd.mpr this).symm
  have hn0 : ∀ p ∈ S, ((n : ℤ) : ℚ_[p]) ≠ 0 := fun p hp h0 => by
    have := hnp p hp; rw [h0, norm_zero] at this; exact zero_ne_one this
  set ιp : ∀ p : Nat.Primes, QuatAlg ℚ a b →+* QuatAlg ℚ_[p] a b := fun p => baseChange a b (algebraMap ℚ ℚ_[p])
  have hιn : ∀ p : Nat.Primes, ιp p (algebraMap ℚ (QuatAlg ℚ a b) (nrd z)) =
      algebraMap ℚ_[p] (QuatAlg ℚ_[p] a b) ((n : ℤ) : ℚ_[p]) := by
    intro p; rw [baseChange_algebraMap_scalarM, hn]; push_cast; rfl
  let gz : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b := fun p => ιp p z
  let gi : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b := fun p => ((n : ℚ_[p]))⁻¹ • ιp p (star z)
  have hloc1 : ∀ p ∈ S, gz p * gi p = 1 := by
    intro p hp
    show ιp p z * (((n : ℚ_[p]))⁻¹ • ιp p (star z)) = 1
    rw [mul_smul_comm, ← map_mul, (mul_star_eq_nrd z).1, hιn, Algebra.smul_def, ← map_mul,
      show ((n : ℤ) : ℚ_[p]) = (n : ℚ_[p]) from rfl, inv_mul_cancel₀ (hn0 p hp), map_one]
  have hloc2 : ∀ p ∈ S, gi p * gz p = 1 := by
    intro p hp
    show (((n : ℚ_[p]))⁻¹ • ιp p (star z)) * ιp p z = 1
    rw [smul_mul_assoc, ← map_mul, (mul_star_eq_nrd z).2, hιn, Algebra.smul_def, ← map_mul,
      show ((n : ℤ) : ℚ_[p]) = (n : ℚ_[p]) from rfl, inv_mul_cancel₀ (hn0 p hp), map_one]
  set gx : QuatAlg FinAdele a b := glueAuxM S gz
  set gy : QuatAlg FinAdele a b := glueAuxM S gi
  have hxy : gx * gy = 1 := bhat_ext_auxM fun p => by
    rw [map_mul, evP_glueAuxM, evP_glueAuxM, map_one]; split_ifs with hp
    · exact hloc1 p hp
    · exact one_mul 1
  have hyx : gy * gx = 1 := bhat_ext_auxM fun p => by
    rw [map_mul, evP_glueAuxM, evP_glueAuxM, map_one]; split_ifs with hp
    · exact hloc2 p hp
    · exact one_mul 1
  let u : (BHat a b)ˣ := ⟨gx, gy, hxy, hyx⟩
  have hOloc := mem_latticeCompletion_iff_local_auxM (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  have hOp : ∀ p : Nat.Primes, ∀ y ∈ O.toSubalgebra, ιp p y ∈
      Submodule.span ℤ_[p] (baseChange a b (algebraMap ℚ ℚ_[p]) '' ((Subalgebra.toSubmodule O.toSubalgebra :
        Submodule ℤ (QuatAlg ℚ a b)) : Set (QuatAlg ℚ a b))) :=
    fun p y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hgx : (show BHat a b from gx) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    rw [hOloc]; intro p
    show evPM a b p (glueAuxM S gz) ∈ _
    rw [evP_glueAuxM]; split_ifs with hp
    · exact hOp p z hz
    · have := hOp p 1 O.toSubalgebra.one_mem; rwa [map_one] at this
  have hgy : (show BHat a b from gy) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    rw [hOloc]; intro p
    show evPM a b p (glueAuxM S gi) ∈ _
    rw [evP_glueAuxM]; split_ifs with hp
    · have hc : ‖((n : ℚ_[p]))⁻¹‖ ≤ 1 := by
        rw [norm_inv, show ((n : ℚ_[p])) = ((n : ℤ) : ℚ_[p]) by push_cast; rfl, hnp p hp, inv_one]
      have := Submodule.smul_mem _ (⟨((n : ℚ_[p]))⁻¹, hc⟩ : ℤ_[p]) (hOp p (star z) (star_mem_order O hz))
      exact this
    · have := hOp p 1 O.toSubalgebra.one_mem; rwa [map_one] at this
  set w' : BHat a b := algebraMap ℚ FinAdele ((M : ℚ)⁻¹) • ((show BHat a b from gx) - finEmbed a b z) with hw'def
  have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hw' : w' ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    rw [hOloc]; intro p
    show evPM a b p (algebraMap ℚ FinAdele ((M : ℚ)⁻¹) • (glueAuxM S gz - (show QuatAlg FinAdele a b from finEmbed a b z))) ∈ _
    rw [evP_smul_auxM, map_sub, evP_glueAuxM]
    erw [evP_finEmbed_auxM]
    split_ifs with hp
    · rw [sub_self, smul_zero]; exact Submodule.zero_mem _
    · have hMp : ‖((M : ℚ) : ℚ_[p])‖ = 1 := by
        rw [Rat.cast_natCast, Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd p.2).mpr fun h => hp ((hS p).mpr h)
      have hc : ‖(algebraMap ℚ FinAdele ((M : ℚ)⁻¹)) p‖ ≤ 1 := by
        show ‖(((M : ℚ)⁻¹ : ℚ) : ℚ_[p])‖ ≤ 1
        rw [Rat.cast_inv, norm_inv, hMp, inv_one]
      have h1 := Submodule.sub_mem _ (by have := hOp p 1 O.toSubalgebra.one_mem; rwa [map_one] at this)
        (hOp p z hz)
      exact Submodule.smul_mem _ (⟨_, hc⟩ : ℤ_[p]) h1
  have he : ((u : (BHat a b)ˣ) : BHat a b) = finEmbed a b z + (M : FinAdele) • w' := by
    rw [hw'def, smul_smul, ← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hMq, map_one,
      one_smul]
    show gx = _
    abel
  refine ⟨⟨u, hgx, hgy⟩, Units.ext ?_⟩
  rw [hΨ ⟨u, hgx, hgy⟩ z hz w' hw' he]
  exact hzg

end Level54

/-- **Mass under change of level.** For `a, b < 0`, an order `O` and a level structure `φ` of level `M ≥ 1`:
`[Ô^× : Ô(M; φ)^×] = ψ(M)` and `Mass(O(M; φ)) = ψ(M) Mass(O)`. -/
@[tf_id "III.qcls.thm:mass-level-change"]
theorem mass_level_change {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) {M : ℕ} [NeZero M]
    (φ : LevelStructure O M) :
    ((orderCompletionUnits (eichlerOrder φ)).relIndex (orderCompletionUnits O) : ℚ) = dedekindPsi M ∧
      mass (eichlerOrder φ) = dedekindPsi M * mass O := by
  obtain ⟨Ψ, hW, hval⟩ := exists_level_hom O φ
  have hsurj := level_hom_surjective O φ Ψ hval
  have hidx : (orderCompletionUnits (eichlerOrder φ)).relIndex (orderCompletionUnits O) =
      (borel (ZMod M)).index := by
    rw [Subgroup.relIndex, hW, Subgroup.index_comap_of_surjective _ hsurj]
  have hψ : ((orderCompletionUnits (eichlerOrder φ)).relIndex (orderCompletionUnits O) : ℚ) = dedekindPsi M := by
    rw [hidx]; exact gl2_borel_index M (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))
  refine ⟨hψ, ?_⟩
  have hEO : ∀ x ∈ latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra),
      x ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := fun x hx =>
    Submodule.span_mono (Set.image_mono (eichlerSubalgebra_le φ)) hx
  have hle : orderCompletionUnits (eichlerOrder φ) ≤ orderCompletionUnits O := fun u hu => ⟨hEO _ hu.1, hEO _ hu.2⟩
  have hpsi : dedekindPsi M ≠ 0 := by
    have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
    refine mul_ne_zero hM0 (Finset.prod_ne_zero_iff.mpr fun p _ => ?_)
    positivity
  have hne : (orderCompletionUnits (eichlerOrder φ)).relIndex (orderCompletionUnits O) ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hψ; exact hpsi hψ.symm
  have h := mass_orbit_count _ _ hle hne (classSet_finite ha hb O)
  rw [hψ] at h
  exact h

/-- Under `Hyp.EichlerMass a b D O` and `RamifiedExactly a b D`, for a level structure `φ` of level `M ≥ 1` on the
maximal order `O`: `Mass(O(M; φ)) = (1/24) ∏_{p ∣ D} (p − 1) · ψ(M)`. -/
@[tf_id "III.qcls.cor:eichler-order-mass"]
theorem eichlerOrder_mass {a b : ℤ} {D : ℕ} (O : MaxOrder a b) (hM : Hyp.EichlerMass a b D O)
    (hD : RamifiedExactly a b D) {M : ℕ} [NeZero M] (φ : LevelStructure O.1 M) :
    mass (eichlerOrder φ) = (1 / 24 : ℚ) * (∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) * dedekindPsi M := by
  rw [(mass_level_change hD.1 hD.2.1 O.1 φ).2, hM hD]
  ring

end GL2TF.Quat
