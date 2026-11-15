import AlgJL.Meta.Tag
import AlgJL.Common.QuaternionNorm
import AlgJL.VolI.P0.Ideles
import AlgJL.VolIII.P2.Adelic
import AlgJL.VolIII.P2.ClassSet
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The adelic quaternion group and compactness of `B^× \ B^×(𝔸)^1` (Q2 U6, items 57–60)

Lean counterpart of `vol3/ch-iii-07-orders.tex` §6 (items 57–60 of `docs/sprints/Q2-plan.md` §1.2).

* `AdelicQuat a b`: `B_𝔸 := B_{𝔸} = ℍ[𝔸, a, 0, b]`, a type synonym (plan trap 3) with the product topology of `𝔸⁴`
  transported along `QuaternionAlgebra.equivTuple`; `B_𝔸^×` carries Mathlib's `Units` topology (trap 4).
* `QuatInf a b`: `B_∞ := B_ℝ`, likewise (for the B-only item 58).
* `adelicNrd`: `nrd : B_𝔸^× → 𝔸^×` (`Idele`), via `nrdHom` (`nrd` as a monoid hom; multiplicativity proved here).
* `adelicNormOne`: `B_𝔸^1 = {x : |nrd x|_𝔸 = 1}` (`ideleNorm`).
* `adelicDiagonal`: `Γ_B = ι_𝔸(B^×)`, as a subgroup of `B_𝔸^1` (`subgroupOf`); the inclusion `ι_𝔸(B^×) ≤ B_𝔸^1` (product
  formula) is the first clause of item 59.
Item 60 has the binder shape of `II.cpt.thm:compact-trace-formula` (`DiscreteTopology Γ`,
`CompactSpace (MulAction.orbitRel.Quotient Γ G)`). Owner: L3T (Q2, TITAN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF

/-! ## §1 The adelic quaternion algebra -/

/-- The adelic quaternion algebra `B_𝔸 := B_{𝔸} = ℍ[𝔸, a, 0, b]`, as a type synonym of `QuatAlg Adele a b` (trap 3). -/
@[tf_id "III.qcls.def:adelic-quaternion-group"]
def AdelicQuat (a b : ℤ) : Type := QuatAlg Adele a b

/-- The ring structure of `B_𝔸` (that of `ℍ[𝔸, a, 0, b]`). -/
@[tf_aux "III.qcls.def:adelic-quaternion-ring"]
noncomputable instance instRingAdelicQuat (a b : ℤ) : Ring (AdelicQuat a b) :=
  inferInstanceAs (Ring (QuatAlg Adele a b))

/-- The topology of `B_𝔸`: the product topology of `𝔸⁴`, transported along the coordinates `equivTuple`. -/
@[tf_aux "III.qcls.def:adelic-quaternion-topology"]
noncomputable instance instTopologicalSpaceAdelicQuat (a b : ℤ) : TopologicalSpace (AdelicQuat a b) :=
  TopologicalSpace.induced
    (fun x : AdelicQuat a b => QuaternionAlgebra.equivTuple ((a : ℤ) : Adele) 0 ((b : ℤ) : Adele) x) inferInstance

/-- The real quaternion algebra `B_∞ := B_ℝ = ℍ[ℝ, a, 0, b]`, as a type synonym of `QuatAlg ℝ a b` (trap 3). -/
@[tf_aux "III.qcls.def:real-quaternion-algebra"]
def QuatInf (a b : ℤ) : Type := QuatAlg ℝ a b

/-- The ring structure of `B_∞`. -/
@[tf_aux "III.qcls.def:real-quaternion-ring"]
noncomputable instance instRingQuatInf (a b : ℤ) : Ring (QuatInf a b) :=
  inferInstanceAs (Ring (QuatAlg ℝ a b))

/-- The topology of `B_∞`: the product topology of `ℝ⁴`, transported along `equivTuple`. -/
@[tf_aux "III.qcls.def:real-quaternion-topology"]
noncomputable instance instTopologicalSpaceQuatInf (a b : ℤ) : TopologicalSpace (QuatInf a b) :=
  TopologicalSpace.induced
    (fun x : QuatInf a b => QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0 ((b : ℤ) : ℝ) x) inferInstance

/-- The embedding `ι_𝔸 : B → B_𝔸`, base change along `ℚ → 𝔸`. -/
@[tf_aux "III.qcls.def:adelic-embedding"]
noncomputable def adelicEmbed (a b : ℤ) : QuatAlg ℚ a b →+* AdelicQuat a b :=
  baseChange a b (algebraMap ℚ Adele)

/-- Proof helper: `nrd 1 = 1`. -/
theorem nrdHom_one_aux {R : Type*} [CommRing R] {a b : ℤ} : nrd (1 : QuatAlg R a b) = 1 := by
  simp [nrd]

/-- Proof helper: `nrd (x y) = nrd x · nrd y` (a polynomial identity). -/
theorem nrdHom_mul_aux {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) :
    nrd (x * y) = nrd x * nrd y := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

/-- The reduced norm `nrd : B_R → R` as a monoid homomorphism. -/
@[tf_aux "III.qcls.def:reduced-norm-hom"]
def nrdHom (R : Type*) [CommRing R] (a b : ℤ) : QuatAlg R a b →* R where
  toFun := nrd
  map_one' := nrdHom_one_aux
  map_mul' := nrdHom_mul_aux

/-- The reduced norm on units, `nrd : B_𝔸^× → 𝔸^×`. -/
@[tf_aux "III.qcls.def:adelic-reduced-norm"]
noncomputable def adelicNrd (a b : ℤ) : (AdelicQuat a b)ˣ →* Idele :=
  Units.map (nrdHom Adele a b)

/-- `B_𝔸^1 = {x ∈ B_𝔸^× : |nrd x|_𝔸 = 1}`. -/
@[tf_aux "III.qcls.def:adelic-norm-one"]
noncomputable def adelicNormOne (a b : ℤ) : Subgroup (AdelicQuat a b)ˣ :=
  (ideleNorm.comp (adelicNrd a b)).ker

/-- `Γ_B = ι_𝔸(B^×)`, as a subgroup of `B_𝔸^1` (intersected with `B_𝔸^1`; by item 59 it is all of `ι_𝔸(B^×)`). -/
@[tf_aux "III.qcls.def:adelic-diagonal"]
noncomputable def adelicDiagonal (a b : ℤ) : Subgroup (adelicNormOne a b) :=
  (Units.map (adelicEmbed a b).toMonoidHom).range.subgroupOf (adelicNormOne a b)

/-! ## Proof helpers -/

/-- Proof helper: `nrd` commutes with base change. -/
theorem nrd_baseChange_aux {R S : Type*} [CommRing R] [CommRing S] {a b : ℤ} (f : R →+* S)
    (x : QuatAlg R a b) : nrd (baseChange a b f x) = f (nrd x) := by
  simp [nrd, baseChange, map_sub, map_add, map_mul, map_pow, map_intCast]

/-- Proof helper: the coordinates of `ι_𝔸(x)` are the images of those of `x`. -/
theorem adelicEmbed_coord_aux {a b : ℤ} (x : QuatAlg ℚ a b) (i : Fin 4) :
    QuaternionAlgebra.equivTuple ((a : ℤ) : Adele) 0 ((b : ℤ) : Adele)
        (show QuatAlg Adele a b from adelicEmbed a b x) i =
      algebraMap ℚ Adele (QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) x i) := by
  fin_cases i <;> rfl

/-- Proof helper: the coordinates `B_𝔸 → 𝔸⁴` are continuous. -/
theorem continuous_equivTuple_adelicQuat (a b : ℤ) :
    Continuous (fun x : AdelicQuat a b =>
      QuaternionAlgebra.equivTuple ((a : ℤ) : Adele) 0 ((b : ℤ) : Adele) (show QuatAlg Adele a b from x)) :=
  continuous_induced_dom

/-- Proof helper: gluing `B_ℝ × B̂ → B_𝔸`, coordinatewise. -/
private noncomputable def glueHom (a b : ℤ) : QuatAlg ℝ a b × QuatAlg FinAdele a b →* QuatAlg Adele a b where
  toFun p := ⟨(p.1.re, p.2.re), (p.1.imI, p.2.imI), (p.1.imJ, p.2.imJ), (p.1.imK, p.2.imK)⟩
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp

/-- Proof helper: the coordinates `B_ℝ → ℝ⁴` are continuous. -/
theorem continuous_equivTuple_quatInf (a b : ℤ) :
    Continuous (fun x : QuatInf a b =>
      QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0 ((b : ℤ) : ℝ) (show QuatAlg ℝ a b from x)) :=
  continuous_induced_dom

/-- Proof helper: the coordinates `B̂ → 𝔸_f⁴` are continuous. -/
theorem continuous_equivTuple_bHat (a b : ℤ) :
    Continuous (fun x : BHat a b =>
      QuaternionAlgebra.equivTuple ((a : ℤ) : FinAdele) 0 ((b : ℤ) : FinAdele) (show QuatAlg FinAdele a b from x)) :=
  continuous_induced_dom

/-! ## §2 Units and compactness -/

/-- `B_𝔸^× ≅ B_∞^× × B̂^×` as topological groups, by `x ↦ (x_∞, x_f)` (base change along `𝔸 → ℝ`, `𝔸 → 𝔸_f`).
B-only. -/
@[tf_aux "III.qcls.lem:adelic-units-product"]
theorem adelic_units_product (a b : ℤ) :
    ∃ e : (AdelicQuat a b)ˣ ≃ₜ* (QuatInf a b)ˣ × (BHat a b)ˣ, ∀ x : (AdelicQuat a b)ˣ,
      e x = (Units.map (baseChange a b (RingHom.fst ℝ FinAdele) :
          QuatAlg Adele a b →+* QuatInf a b).toMonoidHom x,
        Units.map (baseChange a b (RingHom.snd ℝ FinAdele) : QuatAlg Adele a b →+* BHat a b).toMonoidHom x) := by
  set f1 : AdelicQuat a b →* QuatInf a b :=
    (baseChange a b (RingHom.fst ℝ FinAdele) : QuatAlg Adele a b →+* QuatInf a b).toMonoidHom
  set f2 : AdelicQuat a b →* BHat a b :=
    (baseChange a b (RingHom.snd ℝ FinAdele) : QuatAlg Adele a b →+* BHat a b).toMonoidHom
  set g : QuatInf a b × BHat a b →* AdelicQuat a b := glueHom a b
  have hf1 : Continuous f1 := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    have h := (continuous_apply i).comp (continuous_equivTuple_adelicQuat a b)
    refine (continuous_fst.comp h).congr fun x => ?_
    fin_cases i <;> rfl
  have hf2 : Continuous f2 := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    have h := (continuous_apply i).comp (continuous_equivTuple_adelicQuat a b)
    refine (continuous_snd.comp h).congr fun x => ?_
    fin_cases i <;> rfl
  have hg : Continuous g := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    have h1 := (continuous_apply i).comp ((continuous_equivTuple_quatInf a b).comp
      (continuous_fst (X := QuatInf a b) (Y := BHat a b)))
    have h2 := (continuous_apply i).comp ((continuous_equivTuple_bHat a b).comp
      (continuous_snd (X := QuatInf a b) (Y := BHat a b)))
    refine (h1.prodMk h2).congr fun x => ?_
    fin_cases i <;> rfl
  have hgf : ∀ x : AdelicQuat a b, g (f1 x, f2 x) = x := fun x => rfl
  have hfg1 : ∀ p : QuatInf a b × BHat a b, f1 (g p) = p.1 := fun p => rfl
  have hfg2 : ∀ p : QuatInf a b × BHat a b, f2 (g p) = p.2 := fun p => rfl
  let e : (AdelicQuat a b)ˣ ≃ₜ* (QuatInf a b)ˣ × (BHat a b)ˣ :=
    { toFun := fun x => (Units.map f1 x, Units.map f2 x)
      invFun := fun p => Units.map g (MulEquiv.prodUnits.symm p)
      left_inv := fun x => Units.ext (hgf x)
      right_inv := fun p => Prod.ext (Units.ext (hfg1 _)) (Units.ext (hfg2 _))
      map_mul' := fun x y => by simp
      continuous_toFun := (Units.continuous_map hf1).prodMk (Units.continuous_map hf2)
      continuous_invFun := (Units.continuous_map hg).comp
        (Homeomorph.prodUnits (α := QuatInf a b) (β := BHat a b)).symm.continuous }
  exact ⟨e, fun x => rfl⟩

/-- `ι_𝔸(B^×) ≤ B_𝔸^1` (product formula), and `Γ_B` is discrete in `B_𝔸^1`. -/
@[tf_id "III.qcls.thm:diagonal-discrete"]
theorem diagonal_discrete (a b : ℤ) :
    (Units.map (adelicEmbed a b).toMonoidHom).range ≤ adelicNormOne a b ∧
      DiscreteTopology (adelicDiagonal a b) := by
  have h1 : (Units.map (adelicEmbed a b).toMonoidHom).range ≤ adelicNormOne a b := by
    rintro _ ⟨β, rfl⟩
    rw [adelicNormOne, MonoidHom.mem_ker]
    have : adelicNrd a b (Units.map (adelicEmbed a b).toMonoidHom β) =
        ratIdele (Units.map (nrdHom ℚ a b) β) := by
      ext1
      simp only [adelicNrd, ratIdele, Units.coe_map]
      exact nrd_baseChange_aux (algebraMap ℚ Adele) (β : QuatAlg ℚ a b)
    rw [MonoidHom.comp_apply, this]
    exact product_formula _
  refine ⟨h1, ?_⟩
  rw [discreteTopology_iff_isOpen_singleton]
  intro γ0
  set T := fun x : AdelicQuat a b =>
    QuaternionAlgebra.equivTuple ((a : ℤ) : Adele) 0 ((b : ℤ) : Adele) (show QuatAlg Adele a b from x)
  set v : adelicDiagonal a b → AdelicQuat a b :=
    fun γ => (((γ : adelicNormOne a b) : (AdelicQuat a b)ˣ) : AdelicQuat a b)
  have hv : Continuous v :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  set c : adelicDiagonal a b → (Fin 4 → Adele) := fun γ => T (v γ) - T (v γ0)
  have hc : Continuous c := ((continuous_equivTuple_adelicQuat a b).comp hv).sub continuous_const
  set box : Set (Fin 4 → Adele) := Set.pi Set.univ fun _ => Set.Ioo (-1 : ℝ) 1 ×ˢ (Zhat : Set FinAdele)
  have hbox : IsOpen box := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo.prod isOpen_zhat_adele
  have hrep : ∀ γ : adelicDiagonal a b, ∃ β : (QuatAlg ℚ a b)ˣ, v γ = adelicEmbed a b β := by
    intro γ
    obtain ⟨β, hβ⟩ := (Subgroup.mem_subgroupOf.mp γ.2)
    exact ⟨β, (congrArg Units.val hβ).symm⟩
  convert hbox.preimage hc using 1
  ext γ
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · rintro rfl
    intro i _
    simp only [c, sub_self, Pi.zero_apply]
    exact ⟨⟨by norm_num, by norm_num⟩, Zhat.zero_mem⟩
  · intro hγ
    obtain ⟨β, hβ⟩ := hrep γ
    obtain ⟨β0, hβ0⟩ := hrep γ0
    have hcoord : ∀ i : Fin 4, c γ i = algebraMap ℚ Adele
        (QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) ((β : QuatAlg ℚ a b) - β0) i) := by
      intro i
      simp only [c, T, hβ, hβ0, Pi.sub_apply]
      rw [adelicEmbed_coord_aux, adelicEmbed_coord_aux, ← map_sub]
      congr 1
      fin_cases i <;> rfl
    have hzero : ∀ i : Fin 4,
        QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ) ((β : QuatAlg ℚ a b) - β0) i = 0 := by
      intro i
      have hi := hγ i (Set.mem_univ i)
      rw [hcoord i] at hi
      exact (rat_discrete).2.2 _ hi.1 hi.2
    have hββ : (β : QuatAlg ℚ a b) = β0 := by
      rw [← sub_eq_zero]
      apply (QuaternionAlgebra.equivTuple ((a : ℤ) : ℚ) 0 ((b : ℤ) : ℚ)).injective
      funext i
      rw [hzero i]
      fin_cases i <;> rfl
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    show v γ = v γ0
    rw [hβ, hβ0, hββ]

/-! ## Proof helpers for compactness -/

/-- Proof helper: `y ȳ = nrd(y)` in `B_R`. -/
theorem mul_star_eq_nrd_aux {R : Type*} [CommRing R] {a b : ℤ} (y : QuatAlg R a b) :
    y * star y = algebraMap R (QuatAlg R a b) (nrd y) ∧ star y * y = algebraMap R (QuatAlg R a b) (nrd y) := by
  rw [QuaternionAlgebra.algebraMap_eq]
  constructor <;> ext <;> simp [nrd] <;> ring

/-- Proof helper: for `a, b < 0`, `nrd(y) ≥ y_i²` for every coordinate of `y ∈ B_ℝ`. -/
theorem sq_coord_le_nrd_aux {a b : ℤ} (ha : a < 0) (hb : b < 0) (v : Fin 4 → ℝ) (i : Fin 4) :
    v i ^ 2 ≤ v 0 ^ 2 - (a : ℝ) * v 1 ^ 2 - (b : ℝ) * v 2 ^ 2 + (a : ℝ) * (b : ℝ) * v 3 ^ 2 := by
  have ha' : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
  have hb' : (b : ℝ) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
  have hab : (1 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by nlinarith
  have h0 := sq_nonneg (v 0)
  have h1 : v 1 ^ 2 ≤ -(a : ℝ) * v 1 ^ 2 := by nlinarith [sq_nonneg (v 1)]
  have h2 : v 2 ^ 2 ≤ -(b : ℝ) * v 2 ^ 2 := by nlinarith [sq_nonneg (v 2)]
  have h3 : v 3 ^ 2 ≤ (a : ℝ) * (b : ℝ) * v 3 ^ 2 := by nlinarith [sq_nonneg (v 3)]
  have h1' := sq_nonneg (v 1)
  have h2' := sq_nonneg (v 2)
  have h3' := sq_nonneg (v 3)
  fin_cases i <;> simp <;> nlinarith

/-- Proof helper: the identity `B_∞ → B_ℝ` (from the type synonym to the quaternion algebra). -/
private def toQInf {a b : ℤ} (y : QuatInf a b) : QuatAlg ℝ a b := y

/-- Proof helper: for `a, b < 0` and `r ∈ ℝ`, `{y ∈ B_∞^× : nrd y = r}` is compact. -/
theorem isCompact_nrd_level_aux {a b : ℤ} (ha : a < 0) (hb : b < 0) (r : ℝ) :
    IsCompact {y : (QuatInf a b)ˣ | nrd (toQInf (y : QuatInf a b)) = r} := by
  by_cases hr : r = 0
  · convert isCompact_empty
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hy
    have h := nrdHom_mul_aux (R := ℝ) (a := a) (b := b) (toQInf (y : QuatInf a b))
      (toQInf ((y⁻¹ : (QuatInf a b)ˣ) : QuatInf a b))
    have h1 : toQInf (y : QuatInf a b) * toQInf ((y⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) = 1 := y.mul_inv
    rw [h1, nrdHom_one_aux, hy, hr, zero_mul] at h
    exact one_ne_zero h
  set T : QuatInf a b → (Fin 4 → ℝ) := fun y =>
    QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0 ((b : ℤ) : ℝ) (toQInf y)
  have hT : Topology.IsInducing T := ⟨rfl⟩
  have hTs : Function.Surjective T := fun v => ⟨(QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0
      ((b : ℤ) : ℝ)).symm v, (QuaternionAlgebra.equivTuple _ _ _).apply_symm_apply v⟩
  set P : (Fin 4 → ℝ) → ℝ := fun v => v 0 ^ 2 - (a : ℝ) * v 1 ^ 2 - (b : ℝ) * v 2 ^ 2 + (a : ℝ) * (b : ℝ) * v 3 ^ 2
  have hPc : Continuous P := by fun_prop
  have hE'c : IsCompact (P ⁻¹' {r}) := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_singleton.preimage hPc) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1 + |r|, fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hv' : P v = r := hv
    have hsq := sq_coord_le_nrd_aux ha hb v i
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (v i), sq_abs (v i), le_abs_self r, abs_nonneg r]
  set E : Set (QuatInf a b) := {y | nrd (toQInf y) = r}
  have hEeq : E = T ⁻¹' (P ⁻¹' {r}) := rfl
  have hEc : IsCompact E := by
    rw [hT.isCompact_iff, hEeq, Set.image_preimage_eq _ hTs]
    exact hE'c
  have hcs : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  set inv : QuatInf a b → QuatInf a b := fun y => (r⁻¹ • star (toQInf y) : QuatAlg ℝ a b)
  have hinv : Continuous inv := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    have hc : Continuous fun y : QuatInf a b => T y i := (continuous_apply i).comp continuous_induced_dom
    refine ((continuous_const (y := r⁻¹ * ![1, -1, -1, -1] i)).mul hc).congr fun y => ?_
    show _ = QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0 ((b : ℤ) : ℝ) (r⁻¹ • star (toQInf y) : QuatAlg ℝ a b) i
    fin_cases i <;> simp [T]
  have hmul : ∀ y : E, toQInf (y : QuatInf a b) * toQInf (inv y) = 1 ∧
      toQInf (inv y) * toQInf (y : QuatInf a b) = 1 := by
    intro y
    have hy : nrd (toQInf (y : QuatInf a b)) = r := y.2
    obtain ⟨h1, h2⟩ := mul_star_eq_nrd_aux (toQInf (y : QuatInf a b))
    have e1 : toQInf (inv y) = r⁻¹ • star (toQInf (y : QuatInf a b)) := rfl
    rw [e1, mul_smul_comm, h1, smul_mul_assoc, h2, hy, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr, map_one]
    exact ⟨rfl, rfl⟩
  let sm : E → (QuatInf a b)ˣ := fun y => ⟨y, inv y, (hmul y).1, (hmul y).2⟩
  have hs : Continuous sm := Units.continuous_iff.2 ⟨continuous_subtype_val, hinv.comp continuous_subtype_val⟩
  convert isCompact_range hs
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, hy⟩, Units.ext rfl⟩
  · rintro ⟨y', rfl⟩
    exact y'.2

/-- Proof helper: for `a, b < 0`, `nrd y > 0` for `y ∈ B_∞^×`. -/
theorem nrd_pos_of_unit_aux {a b : ℤ} (ha : a < 0) (hb : b < 0) (y : (QuatInf a b)ˣ) :
    0 < nrd (toQInf (y : QuatInf a b)) := by
  have h := nrdHom_mul_aux (R := ℝ) (a := a) (b := b) (toQInf (y : QuatInf a b))
    (toQInf ((y⁻¹ : (QuatInf a b)ˣ) : QuatInf a b))
  have h1 : toQInf (y : QuatInf a b) * toQInf ((y⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) = 1 := y.mul_inv
  rw [h1, nrdHom_one_aux] at h
  have hne : nrd (toQInf (y : QuatInf a b)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact one_ne_zero h
  have hle := sq_coord_le_nrd_aux ha hb
    (QuaternionAlgebra.equivTuple ((a : ℤ) : ℝ) 0 ((b : ℤ) : ℝ) (toQInf (y : QuatInf a b))) 0
  have hge : 0 ≤ nrd (toQInf (y : QuatInf a b)) := le_trans (sq_nonneg _) hle
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- Proof helper: the identity `B̂ → B_{𝔸_f}` (from the type synonym to the quaternion algebra). -/
private def toQHat {a b : ℤ} (y : BHat a b) : QuatAlg FinAdele a b := y

/-- Proof helper: elements of the completion `Ô` of the standard order have reduced norm in `Ẑ`. -/
theorem nrd_mem_zhat_of_mem_std_aux {a b : ℤ} {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule (standardOrder a b).toSubalgebra)) :
    nrd (toQHat y) ∈ Zhat := by
  have hc : (toQHat y).re ∈ Zhat ∧ (toQHat y).imI ∈ Zhat ∧ (toQHat y).imJ ∈ Zhat ∧ (toQHat y).imK ∈ Zhat := by
    rw [latticeCompletion] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨⟨n0, h0⟩, ⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩⟩ := (mem_standardSubalgebra (a := a) (b := b)).mp hz
      have e0 : (toQHat (finEmbed a b z)).re = algebraMap ℚ FinAdele z.re := rfl
      have e1 : (toQHat (finEmbed a b z)).imI = algebraMap ℚ FinAdele z.imI := rfl
      have e2 : (toQHat (finEmbed a b z)).imJ = algebraMap ℚ FinAdele z.imJ := rfl
      have e3 : (toQHat (finEmbed a b z)).imK = algebraMap ℚ FinAdele z.imK := rfl
      rw [e0, e1, e2, e3, h0, h1, h2, h3, map_intCast, map_intCast, map_intCast, map_intCast]
      exact ⟨intCast_mem Zhat _, intCast_mem Zhat _, intCast_mem Zhat _, intCast_mem Zhat _⟩
    | zero => exact ⟨Zhat.zero_mem, Zhat.zero_mem, Zhat.zero_mem, Zhat.zero_mem⟩
    | add x z _ _ hx hz =>
      exact ⟨Zhat.add_mem hx.1 hz.1, Zhat.add_mem hx.2.1 hz.2.1, Zhat.add_mem hx.2.2.1 hz.2.2.1,
        Zhat.add_mem hx.2.2.2 hz.2.2.2⟩
    | smul t x _ hx =>
      exact ⟨Zhat.mul_mem t.2 hx.1, Zhat.mul_mem t.2 hx.2.1, Zhat.mul_mem t.2 hx.2.2.1, Zhat.mul_mem t.2 hx.2.2.2⟩
  obtain ⟨h0, h1, h2, h3⟩ := hc
  unfold nrd
  exact Zhat.add_mem (Zhat.sub_mem (Zhat.sub_mem (Zhat.pow_mem h0 2)
    (Zhat.mul_mem (intCast_mem Zhat a) (Zhat.pow_mem h1 2))) (Zhat.mul_mem (intCast_mem Zhat b) (Zhat.pow_mem h2 2)))
    (Zhat.mul_mem (Zhat.mul_mem (intCast_mem Zhat a) (intCast_mem Zhat b)) (Zhat.pow_mem h3 2))

/-- Proof helper: the idele `(t, 1)` for `t ∈ ℝ^×`. -/
private noncomputable def infIdele : ℝˣ →* Idele :=
  (MulEquiv.prodUnits (M := ℝ) (N := FinAdele)).symm.toMonoidHom.comp (MonoidHom.inl ℝˣ FinAdeleˣ)

/-- Proof helper: the idele `(1, t)` for `t ∈ 𝔸_f^×`. -/
private noncomputable def finIdele : FinAdeleˣ →* Idele :=
  (MulEquiv.prodUnits (M := ℝ) (N := FinAdele)).symm.toMonoidHom.comp (MonoidHom.inr ℝˣ FinAdeleˣ)

/-- Proof helper: the finite part `|nrd x|_f := |(1, nrd x)|_𝔸` of the norm on `B̂^×`. -/
private noncomputable def finNorm (a b : ℤ) : (BHat a b)ˣ →* ℝ :=
  ideleNorm.comp (finIdele.comp (Units.map (nrdHom FinAdele a b)))

/-- Proof helper: `|(t, 1)|_𝔸 = |t|`. -/
private theorem ideleNorm_infIdele (t : ℝˣ) : ideleNorm (infIdele t) = |(t : ℝ)| := by
  have : infIdele t = ideleInfFin (t : ℝ) 1 := by
    ext1
    rw [ideleInfFin_val t.ne_zero]
    rfl
  rw [this, ideleNorm_ideleInfFin t.ne_zero]

/-- Proof helper: `|nrd u|_f = 1` for `u ∈ Ô^×`, `O` the standard order. -/
private theorem finNorm_eq_one_aux {a b : ℤ} (u : (BHat a b)ˣ)
    (hu : u ∈ orderCompletionUnits (standardOrder a b)) : finNorm a b u = 1 := by
  have h1 := nrd_mem_zhat_of_mem_std_aux hu.1
  have h2 := nrd_mem_zhat_of_mem_std_aux hu.2
  have hm : ∀ v w : (BHat a b)ˣ, v * w = 1 → nrd (toQHat (v : BHat a b)) * nrd (toQHat (w : BHat a b)) = 1 := by
    intro v w hvw
    rw [← nrdHom_mul_aux]
    have : toQHat (v : BHat a b) * toQHat (w : BHat a b) = 1 := congrArg Units.val hvw
    rw [this, nrdHom_one_aux]
  let w : Zhatˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (hm u u⁻¹ (mul_inv_cancel u)), Subtype.ext (hm u⁻¹ u (inv_mul_cancel u))⟩
  have : finIdele (Units.map (nrdHom FinAdele a b) u) = ideleInfFin 1 w := by
    ext1
    rw [ideleInfFin_val one_ne_zero]
    rfl
  show ideleNorm (finIdele (Units.map (nrdHom FinAdele a b) u)) = 1
  rw [this, ideleNorm_ideleInfFin one_ne_zero, abs_one]

/-- Proof helper: `|nrd h|_𝔸 = |nrd h_∞| · |nrd h_f|_f` for `h ∈ B_𝔸^×`. -/
private theorem norm_split_aux {a b : ℤ} (h : (AdelicQuat a b)ˣ) (y : (QuatInf a b)ˣ) (z : (BHat a b)ˣ)
    (hy : y = Units.map (baseChange a b (RingHom.fst ℝ FinAdele) :
          QuatAlg Adele a b →+* QuatInf a b).toMonoidHom h)
    (hz : z = Units.map (baseChange a b (RingHom.snd ℝ FinAdele) :
          QuatAlg Adele a b →+* BHat a b).toMonoidHom h) :
    ideleNorm (adelicNrd a b h) = |nrd (toQInf (y : QuatInf a b))| * finNorm a b z := by
  have hsplit : adelicNrd a b h =
      infIdele (Units.map (nrdHom ℝ a b) y) * finIdele (Units.map (nrdHom FinAdele a b) z) := by
    subst hy hz
    ext1
    refine Prod.ext ?_ ?_
    · have := nrd_baseChange_aux (RingHom.fst ℝ FinAdele) ((h : AdelicQuat a b) : QuatAlg Adele a b)
      show (nrd ((h : AdelicQuat a b) : QuatAlg Adele a b)).1 = _ * 1
      rw [mul_one]
      exact this.symm
    · have := nrd_baseChange_aux (RingHom.snd ℝ FinAdele) ((h : AdelicQuat a b) : QuatAlg Adele a b)
      show (nrd ((h : AdelicQuat a b) : QuatAlg Adele a b)).2 = 1 * _
      rw [one_mul]
      exact this.symm
  rw [hsplit, map_mul, ideleNorm_infIdele]
  rfl

/-- **Compactness** (exit). For `a, b < 0`, `Γ_B` is discrete in `B_𝔸^1` and `Γ_B \ B_𝔸^1` is compact. -/
@[tf_id "III.qcls.thm:quotient-compact"]
theorem quotient_compact {a b : ℤ} (ha : a < 0) (hb : b < 0) :
    DiscreteTopology (adelicDiagonal a b) ∧
      CompactSpace (MulAction.orbitRel.Quotient (adelicDiagonal a b) (adelicNormOne a b)) := by
  classical
  refine ⟨(diagonal_discrete a b).2, ?_⟩
  obtain ⟨e, he⟩ := adelic_units_product a b
  set O := standardOrder a b
  have : Finite (classSet O) := classSet_finite ha hb O
  set H : Subgroup (BHat a b)ˣ := (Units.map (finEmbed a b).toMonoidHom).range
  set V : Subgroup (BHat a b)ˣ := orderCompletionUnits O
  have : IsTopologicalGroup (BHat a b)ˣ := (bHat_topology a b).2.2.2
  have hVc : IsCompact (V : Set (BHat a b)ˣ) := ((latticeCompletion_compact_open a b).2 O).1
  set G := adelicNormOne a b
  set Γ := adelicDiagonal a b
  have hνpos : ∀ x, 0 < finNorm a b x := fun x => ideleNorm_spec.2.1 _
  have hKN : ∀ h : (AdelicQuat a b)ˣ,
      ideleNorm (adelicNrd a b h) = |nrd (toQInf ((e h).1 : QuatInf a b))| * finNorm a b (e h).2 :=
    fun h => norm_split_aux h _ _ (by rw [he]) (by rw [he])
  set r : classSet O → ℝ := fun c => (finNorm a b (Quotient.out c))⁻¹
  set Cc : classSet O → Set (AdelicQuat a b)ˣ := fun c =>
    e.symm '' ({y : (QuatInf a b)ˣ | nrd (toQInf (y : QuatInf a b)) = r c} ×ˢ
      ((fun u => Quotient.out c * u) '' (V : Set (BHat a b)ˣ)))
  have hCc : ∀ c, IsCompact (Cc c) := fun c =>
    ((isCompact_nrd_level_aux ha hb (r c)).prod
      (hVc.image (continuous_const.mul continuous_id))).image e.symm.continuous
  have hCcG : ∀ c, Cc c ⊆ (G : Set (AdelicQuat a b)ˣ) := by
    rintro c _ ⟨⟨y, z⟩, ⟨hy, ⟨u, hu, rfl⟩⟩, rfl⟩
    show ideleNorm.comp (adelicNrd a b) _ = 1
    rw [MonoidHom.comp_apply, hKN, e.apply_symm_apply]
    have hy' : nrd (toQInf (y : QuatInf a b)) = r c := hy
    rw [hy', map_mul, finNorm_eq_one_aux u hu, mul_one, abs_of_pos (inv_pos.mpr (hνpos _)),
      inv_mul_cancel₀ (hνpos _).ne']
  set C : Set G := Subtype.val ⁻¹' (⋃ c, Cc c)
  have hC : IsCompact C := by
    rw [Subtype.isCompact_iff]
    show IsCompact (Subtype.val '' (Subtype.val ⁻¹' ⋃ c, Cc c))
    have hsub : (⋃ c, Cc c) ⊆ Set.range (Subtype.val : G → (AdelicQuat a b)ˣ) :=
      fun x hx => ⟨⟨x, Set.iUnion_subset hCcG hx⟩, rfl⟩
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hsub]
    exact isCompact_iUnion hCc
  have hcover : ∀ g : G, ∃ γ : Γ, γ • g ∈ C := by
    intro g
    set h : (AdelicQuat a b)ˣ := (g : (AdelicQuat a b)ˣ)
    set c : classSet O := DoubleCoset.mk H V (e h).2
    obtain ⟨h', ⟨β, rfl⟩, k', hk', hhf⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' c)
    have hγG : Units.map (adelicEmbed a b).toMonoidHom β⁻¹ ∈ G := (diagonal_discrete a b).1 ⟨β⁻¹, rfl⟩
    let γ : Γ := ⟨⟨_, hγG⟩, Subgroup.mem_subgroupOf.mpr ⟨β⁻¹, rfl⟩⟩
    refine ⟨γ, ?_⟩
    set h0 : (AdelicQuat a b)ˣ := Units.map (adelicEmbed a b).toMonoidHom β⁻¹ * h
    have hh0 : ((γ • g : G) : (AdelicQuat a b)ˣ) = h0 := rfl
    have hh0G : h0 ∈ G := G.mul_mem hγG g.2
    have he2 : (e h0).2 = Quotient.out c * k' := by
      have e1 : (e h0).2 = (e (Units.map (adelicEmbed a b).toMonoidHom β⁻¹)).2 * (e h).2 := by
        rw [map_mul]; rfl
      have e2 : (e (Units.map (adelicEmbed a b).toMonoidHom β⁻¹)).2 =
          (Units.map (finEmbed a b).toMonoidHom β)⁻¹ := by
        rw [he]; ext1; rfl
      rw [e1, e2, hhf]; group
    have hnorm : |nrd (toQInf ((e h0).1 : QuatInf a b))| * finNorm a b (Quotient.out c) = 1 := by
      have := hKN h0
      rw [he2, map_mul (finNorm a b), finNorm_eq_one_aux k' hk', mul_one] at this
      rw [← this]
      exact hh0G
    have hy : nrd (toQInf ((e h0).1 : QuatInf a b)) = r c := by
      rw [abs_of_pos (nrd_pos_of_unit_aux ha hb _)] at hnorm
      exact eq_inv_of_mul_eq_one_left hnorm
    show ((γ • g : G) : (AdelicQuat a b)ˣ) ∈ ⋃ c, Cc c
    rw [hh0]
    exact Set.mem_iUnion.mpr ⟨c, e h0, ⟨hy, ⟨k', hk', he2.symm⟩⟩, e.symm_apply_apply h0⟩
  refine ⟨?_⟩
  have hsurj : (Quotient.mk'' : G → MulAction.orbitRel.Quotient Γ G) '' C = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using Quotient.inductionOn' with
    | h g =>
      obtain ⟨γ, hγ⟩ := hcover g
      exact ⟨γ • g, hγ, Quotient.sound' (MulAction.mem_orbit g γ)⟩
  rw [← hsurj]
  exact hC.image continuous_quotient_mk'

end GL2TF.Quat
