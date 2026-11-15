import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.Brandt
import AlgJL.VolIII.P2.Instances
import Mathlib.Analysis.Complex.Basic

/-!
# Instances: the Hurwitz order and Pizer's order for `D = 11` (Q3 U5, items 43–46)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §5 (items 43–46 of `docs/sprints/Q3-plan.md` §1.2; 46 is stretch, Δ9).

Design: the splittings are model (c) over `ℂ` with `s₀ = i` (`a = −1`); the orders are Q2's `hurwitzOrder` and
`pizerOrderI (−11) _` (`O₁₁`). The class set of `O₁₁` has no canonical ordering: the two classes are named by their
stabilizer orders `|Γ| = 4, 6` (plan trap 4). Characteristic polynomials of `2 × 2` matrices and operators are stated
through trace and determinant. Certificates: `tools/numcheck/q3_numcheck.py` (Q3-INST, T1), W3.

Owner: Q3 A author/formalizer (MAIN); proofs: L4 (W3).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-! ### Proof helpers for `splitting_instances` (Q3 part 5): `24 · dim M_k(O_H; s) = Σ_{u ∈ O_H^×} P_k(trd u, 1)`, with
the `24` units in the coordinates `fH`. -/

/-- The units of the Hurwitz order in the coordinates `fH` (the set of `Inst.units_hurwitz`). -/
private theorem si_units_set :
    {x | x ∈ hurwitzOrder.toSubalgebra ∧ nrd x = 1} = Inst.fH ''
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
        (fun c => c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨c, rfl⟩ := Inst.mem_hurwitz.mp hx
    have hq : ((c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      simp only [nrd] at hn; push_cast at hn ⊢; linear_combination 4 * hn
    have hq' : c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4 := by
      exact_mod_cast hq
    refine ⟨c, ⟨fun k => ?_, hq'⟩, rfl⟩
    have s0 := sq_nonneg (c 0)
    have s1 := sq_nonneg (c 0 + 2 * c 1)
    have s2 := sq_nonneg (c 0 + 2 * c 2)
    have s3 := sq_nonneg (c 0 + 2 * c 3)
    have b0 : -2 ≤ c 0 := by nlinarith
    have b0' : c 0 ≤ 2 := by nlinarith
    have b1 : -2 ≤ c 0 + 2 * c 1 := by nlinarith
    have b1' : c 0 + 2 * c 1 ≤ 2 := by nlinarith
    have b2 : -2 ≤ c 0 + 2 * c 2 := by nlinarith
    have b2' : c 0 + 2 * c 2 ≤ 2 := by nlinarith
    have b3 : -2 ≤ c 0 + 2 * c 3 := by nlinarith
    have b3' : c 0 + 2 * c 3 ≤ 2 := by nlinarith
    fin_cases k <;> simp <;> constructor <;> omega
  · rintro ⟨c, ⟨-, hq⟩, rfl⟩
    refine ⟨Inst.mem_hurwitz.mpr ⟨c, rfl⟩, ?_⟩
    have hq' : ((c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 := by
      exact_mod_cast hq
    simp only [nrd, Inst.fH]; push_cast at hq' ⊢; linear_combination hq' / 4

/-- `24 · dim M_k(O_H; s) = Σ_{u ∈ O_H^×} P_k(trd u, 1)` (Hurwitz order, `h = 1`, `|Γ| = 24`). -/
private theorem si_hurwitz_dim (k : ℕ) (hk : 2 ≤ k) :
    (24 : ℂ) * (Module.finrank ℂ (quatForms hurwitzOrder
        (standardSplitting ℂ (-1) (-1) Complex.I (by simp [Complex.I_sq])) k) : ℂ) =
      (((∑ c ∈ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
        (fun c => c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4),
          heckePolyRing k (c 0) 1 : ℤ)) : ℂ) := by
  classical
  set s := standardSplitting ℂ (-1) (-1) Complex.I (by simp [Complex.I_sq]) with hs
  set O := hurwitzOrder with hO
  set Γ := classStabilizer (orderCompletionUnits O) 1 with hΓdef
  have hΓ : Γ = unitGroup O := Inst.classStabilizer_one O
  obtain ⟨e, -⟩ := forms_class_decomposition O s k (fun _ => 1) (fun c => (Inst.classSet_hurwitz_eq c).symm)
  haveI : Unique (classSet O) := ⟨⟨classOf O 1⟩, fun c => Inst.classSet_hurwitz_eq c⟩
  have hdim : Module.finrank ℂ (quatForms O s k) = Module.finrank ℂ
      ↥(⨅ γ : Γ, LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ (-1) (-1))ˣ) : QuatAlg ℚ (-1) (-1)) - 1)) :=
    e.finrank_eq.trans (LinearEquiv.funUnique (classSet O) ℂ _).finrank_eq
  have hfinΓ : Finite Γ := ((stabilizer_units O 1).2.2 (by norm_num) (by norm_num)).1
  have hnrd : ∀ γ ∈ Γ, nrd (γ : QuatAlg ℚ (-1) (-1)) = 1 := by
    intro γ hγ
    rw [hΓ] at hγ
    have : (γ : QuatAlg ℚ (-1) (-1)) ∈ {x | x ∈ O.toSubalgebra ∧ nrd x = 1} := by
      rw [← (unitGroup_eq_nrd_one_finite (by norm_num) (by norm_num) O).1]
      exact ⟨γ, hγ, rfl⟩
    exact this.2
  have hb := (forms_dimension (by norm_num) (by norm_num) O s).2.1 k hk Γ hfinΓ hnrd
  have hc : Nat.card Γ = 24 := by rw [hΓ]; exact Inst.units_hurwitz
  rw [hc] at hb
  rw [hdim]
  push_cast at hb ⊢
  rw [hb]
  -- the finsum over `Γ` as a sum over the coordinates
  set G : QuatAlg ℚ (-1) (-1) → ℂ := fun x => heckePolyRing k (((trd x : ℚ) : ℂ)) 1 with hG
  have h1 : ∑ᶠ γ : Γ, heckePolyRing k (((trd ((γ : (QuatAlg ℚ (-1) (-1))ˣ) : QuatAlg ℚ (-1) (-1)) : ℚ) : ℂ)) 1 =
      ∑ᶠ γ ∈ (Γ : Set (QuatAlg ℚ (-1) (-1))ˣ), G (γ : QuatAlg ℚ (-1) (-1)) :=
    finsum_set_coe_eq_finsum_mem (s := (Γ : Set (QuatAlg ℚ (-1) (-1))ˣ)) (f := fun γ : (QuatAlg ℚ (-1) (-1))ˣ => G (γ : QuatAlg ℚ (-1) (-1)))
  rw [h1, ← finsum_mem_image (f := G) Units.val_injective.injOn, hΓ,
    (unitGroup_eq_nrd_one_finite (by norm_num) (by norm_num) O).1, si_units_set,
    finsum_mem_image (f := G) Inst.fH_injective.injOn, finsum_mem_coe_finset]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  have htr : trd (Inst.fH c) = (c 0 : ℚ) := by
    simp only [trd, Inst.fH]; ring
  rw [hG]
  simp only []
  have hm := heckePolyRing_map (Int.castRingHom ℂ) k (c 0) 1
  simp only [eq_intCast, Int.cast_one] at hm
  rw [htr, hm]
  norm_cast

/-- Model (c) over `ℂ` with `s₀ = i` for `(−1, −1)` and `(−1, −11)`; `dim M_k(O_H; s) = 1, 0, 0, 1, 1, 0` for
`k = 2, 4, 6, 8, 10, 12` (Hurwitz order, `h = 1`, `|Γ| = 24`); `dim M_2(O₁₁; s) = 2`. -/
@[tf_id "III.qform.ex:splitting-instances"]
theorem splitting_instances :
    let sH := standardSplitting ℂ (-1) (-1) Complex.I (by simp [Complex.I_sq])
    let s11 := standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq])
    Module.finrank ℂ (quatForms hurwitzOrder sH 2) = 1 ∧
    Module.finrank ℂ (quatForms hurwitzOrder sH 4) = 0 ∧
    Module.finrank ℂ (quatForms hurwitzOrder sH 6) = 0 ∧
    Module.finrank ℂ (quatForms hurwitzOrder sH 8) = 1 ∧
    Module.finrank ℂ (quatForms hurwitzOrder sH 10) = 1 ∧
    Module.finrank ℂ (quatForms hurwitzOrder sH 12) = 0 ∧
    Module.finrank ℂ (quatForms (pizerOrderI (-11) (by norm_num)) s11 2) = 2 := by
  intro sH s11
  have hd : ∀ k : ℕ, 2 ≤ k → ∀ v : ℤ,
      (∑ c ∈ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
        (fun c => c 0 ^ 2 + (c 0 + 2 * c 1) ^ 2 + (c 0 + 2 * c 2) ^ 2 + (c 0 + 2 * c 3) ^ 2 = 4),
          heckePolyRing k (c 0) 1 : ℤ) = 24 * v →
      (Module.finrank ℂ (quatForms hurwitzOrder sH k) : ℤ) = v := by
    intro k hk v hv
    have h := si_hurwitz_dim k hk
    rw [hv] at h
    push_cast at h
    have h' : (Module.finrank ℂ (quatForms hurwitzOrder sH k) : ℂ) = (v : ℂ) :=
      mul_left_cancel₀ (by norm_num : (24 : ℂ) ≠ 0) h
    exact_mod_cast h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hd 2 (by norm_num) 1 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · have := hd 4 (by norm_num) 0 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · have := hd 6 (by norm_num) 0 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · have := hd 8 (by norm_num) 1 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · have := hd 10 (by norm_num) 1 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · have := hd 12 (by norm_num) 0 (by set_option maxRecDepth 2000 in decide)
    exact_mod_cast this
  · exact ((forms_dimension (by norm_num) (by norm_num) _ s11).2.2).trans eichler_mass_instance_d11.2.2.1.1

/-- Proof helper: an order is determined by its underlying subalgebra. -/
private theorem bi_qorder_ext {a b : ℤ} {O O' : QOrder a b} (h : O.toSubalgebra = O'.toSubalgebra) : O = O' := by
  cases O; cases O'; cases h; rfl

/-- For the Hurwitz order, every field `K` of characteristic `0`, every splitting `s` and every odd `n ≥ 1`:
`T_n = σ₁(n)` on `M_2(O_H; s)`. -/
@[tf_id "III.brandt.ex:hurwitz-eisenstein"]
theorem hurwitz_eisenstein {K : Type*} [Field K] [CharZero K] (s : Splitting K (-1) (-1)) (n : ℕ) (hn : 0 < n)
    (hodd : Odd n) :
    ∀ f ∈ quatForms hurwitzOrder s 2,
      heckeOperator hurwitzOrder n f = ((ArithmeticFunction.sigma 1 n : ℕ) : K) • f := by
  intro f hf
  -- the Hurwitz order is the Eichler order of level `1` of itself
  let O₀ : MaxOrder (-1) (-1) := ⟨hurwitzOrder, Inst.isMaximal_hurwitz⟩
  let φ : LevelStructure O₀.1 1 :=
    { toRingHom :=
        { toFun := fun _ => 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ => Subsingleton.elim _ _
          map_zero' := rfl
          map_add' := fun _ _ => Subsingleton.elim _ _ }
      surjective := fun y => ⟨0, Subsingleton.elim _ _⟩ }
  have hE : eichlerOrder φ = hurwitzOrder := by
    apply bi_qorder_ext
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hcop : Nat.Coprime n (2 * 1) := by rw [mul_one]; exact Nat.coprime_two_right.mpr hodd
  have hcount := hecke_coset_count O₀ pizer_algebras.1 φ n hn hcop
  rw [hE] at hcount
  -- weight-2 forms are constant (`h = 1`, trivial coefficients)
  have hρ2 : ∀ (γ : QuatAlg ℚ (-1) (-1)) (v : symPowerModule K (2 - 2)), splitRep s 2 γ v = v := by
    intro γ v
    apply Subtype.ext
    show MvPolynomial.aeval (linSubst (s γ)) (v : MvPolynomial (Fin 2) K) = v
    have hv : (v : MvPolynomial (Fin 2) K) = MvPolynomial.C ((v : MvPolynomial (Fin 2) K).coeff 0) := by
      by_cases h0 : (v : MvPolynomial (Fin 2) K) = 0
      · rw [h0]
        simp
      · exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
          (((MvPolynomial.mem_homogeneousSubmodule _ _).mp v.2).totalDegree h0)
    rw [hv, MvPolynomial.aeval_C]
    rfl
  have hconst : ∀ x, f x = f 1 := by
    intro x
    have h1 := Inst.classSet_hurwitz_eq (DoubleCoset.mk _ _ x)
    obtain ⟨g, hg, u, hu, hx⟩ := DoubleCoset.eq.mp h1.symm
    obtain ⟨γ, rfl⟩ := hg
    rw [hx]
    exact (hf γ 1 u hu).trans (hρ2 _ _)
  -- the coset sum
  set S := normNSet hurwitzOrder n with hS
  have hfin := (normNSet_basic hurwitzOrder n hn).2.2.2.1
  have hmemS : ∀ c : (BHat (-1) (-1))ˣ ⧸ orderCompletionUnits hurwitzOrder,
      Quotient.out c ∈ S ↔ c ∈ (QuotientGroup.mk '' S : Set ((BHat (-1) (-1))ˣ ⧸ orderCompletionUnits hurwitzOrder)) := by
    intro c
    constructor
    · intro h; exact ⟨_, h, QuotientGroup.out_eq' c⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits hurwitzOrder) y
      rw [hg]
      have := (normNSet_basic hurwitzOrder n hn).1 y hy 1 (one_mem _) g g.2
      rwa [one_mul] at this
  funext x
  rw [Pi.smul_apply]
  show (∑ᶠ c : (BHat (-1) (-1))ˣ ⧸ orderCompletionUnits hurwitzOrder,
    S.indicator (1 : (BHat (-1) (-1))ˣ → ℤ) (Quotient.out c) • f (x * Quotient.out c)) = _
  have hterm : ∀ c : (BHat (-1) (-1))ˣ ⧸ orderCompletionUnits hurwitzOrder,
      S.indicator (1 : (BHat (-1) (-1))ˣ → ℤ) (Quotient.out c) • f (x * Quotient.out c) =
        (QuotientGroup.mk '' S : Set ((BHat (-1) (-1))ˣ ⧸ orderCompletionUnits hurwitzOrder)).indicator
          (fun _ => f 1) c := by
    intro c
    by_cases hc : Quotient.out c ∈ S
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hmemS c).mp hc), Pi.one_apply, one_smul, hconst]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc ((hmemS c).mpr h)), zero_smul]
  rw [finsum_congr hterm, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    hconst x, ← hcount, Nat.card_eq_card_finite_toFinset hfin, Nat.cast_smul_eq_nsmul]

/-! ### Proof helpers for `brandt_d11` (Q3 part 5): `4 B(n)_{c₁c₁} = #{γ ∈ O₁₁ : nrd γ = n}` for the class `c₁ = [1]`,
and the counts for `n = 1, 2, 3` (a finite box of coordinates). -/

/-- The elements of `O₁₁` of reduced norm `n ≤ 3`, in the coordinates `f11`. -/
private theorem bi_norm_set (n : ℕ) (hn3 : n ≤ 3) :
    {x | x ∈ Inst.O11.toSubalgebra ∧ nrd x = (n : ℚ)} = Inst.f11 ''
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
        (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * (n : ℤ))) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  have hn' : (n : ℤ) ≤ 3 := by exact_mod_cast hn3
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨c, rfl⟩ := Inst.mem_O11.mp hx
    have hq : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 * (n : ℚ) := by
      simp only [nrd, Inst.f11] at hn; push_cast at hn ⊢; linear_combination 4 * hn
    have hq' : c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * (n : ℤ) := by
      exact_mod_cast hq
    refine ⟨c, ⟨fun k => ?_, hq'⟩, rfl⟩
    have s0 := sq_nonneg (c 0)
    have s1 := sq_nonneg (c 1)
    have s2 := sq_nonneg (c 0 + 2 * c 2)
    have s3 := sq_nonneg (c 1 + 2 * c 3)
    have b0 : -3 ≤ c 0 := by nlinarith
    have b0' : c 0 ≤ 3 := by nlinarith
    have b1 : -3 ≤ c 1 := by nlinarith
    have b1' : c 1 ≤ 3 := by nlinarith
    have b2 : -1 ≤ c 0 + 2 * c 2 := by nlinarith
    have b2' : c 0 + 2 * c 2 ≤ 1 := by nlinarith
    have b3 : -1 ≤ c 1 + 2 * c 3 := by nlinarith
    have b3' : c 1 + 2 * c 3 ≤ 1 := by nlinarith
    fin_cases k <;> simp <;> constructor <;> omega
  · rintro ⟨c, ⟨-, hq⟩, rfl⟩
    refine ⟨Inst.mem_O11.mpr ⟨c, rfl⟩, ?_⟩
    have hq' : ((c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 : ℤ) : ℚ) = 4 * (n : ℚ) := by
      exact_mod_cast hq
    simp only [nrd, Inst.f11]; push_cast at hq' ⊢; linear_combination hq' / 4

/-- `#{γ ∈ B^× : γ ∈ O₁₁, nrd γ = n}` is the size of the coordinate box count. -/
private theorem bi_card_norm (n : ℕ) (hn : 0 < n) (hn3 : n ≤ 3) :
    Nat.card {γ : (QuatAlg ℚ (-1) (-11))ˣ // (γ : QuatAlg ℚ (-1) (-11)) ∈ Inst.O11.toSubalgebra ∧
      nrd (γ : QuatAlg ℚ (-1) (-11)) = n} =
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
        (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * (n : ℤ))).card := by
  have himg : ((↑) : (QuatAlg ℚ (-1) (-11))ˣ → QuatAlg ℚ (-1) (-11)) ''
      {γ | (γ : QuatAlg ℚ (-1) (-11)) ∈ Inst.O11.toSubalgebra ∧ nrd (γ : QuatAlg ℚ (-1) (-11)) = n} =
      {x | x ∈ Inst.O11.toSubalgebra ∧ nrd x = (n : ℚ)} := by
    ext x
    constructor
    · rintro ⟨γ, h, rfl⟩; exact h
    · rintro ⟨hx, hnx⟩
      have hn0 : nrd x ≠ 0 := by rw [hnx]; exact_mod_cast hn.ne'
      have h1 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := -1) (b := -11)).1 x).1
      have h2 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := -1) (b := -11)).1 x).2.1
      refine ⟨⟨x, (nrd x)⁻¹ • star x, ?_, ?_⟩, ⟨hx, hnx⟩, rfl⟩
      · rw [mul_smul_comm, h1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn0, map_one]
      · rw [smul_mul_assoc, h2, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn0, map_one]
  calc Nat.card {γ : (QuatAlg ℚ (-1) (-11))ˣ // (γ : QuatAlg ℚ (-1) (-11)) ∈ Inst.O11.toSubalgebra ∧
        nrd (γ : QuatAlg ℚ (-1) (-11)) = n}
      = Nat.card (((↑) : (QuatAlg ℚ (-1) (-11))ˣ → QuatAlg ℚ (-1) (-11)) ''
          {γ | (γ : QuatAlg ℚ (-1) (-11)) ∈ Inst.O11.toSubalgebra ∧ nrd (γ : QuatAlg ℚ (-1) (-11)) = n}) := by
        rw [Nat.card_image_of_injective Units.val_injective]; rfl
    _ = _ := by
        rw [himg, bi_norm_set n hn3, Nat.card_image_of_injective Inst.f11_injective, Nat.card_coe_set_eq,
          Set.ncard_coe_finset]

/-- For the class `c₁ = [1]` of `O₁₁`: `4 B(n)_{c₁c₁} = #{γ ∈ O₁₁ : nrd γ = n}`. -/
private theorem bi_B11 (n : ℕ) (hn : 0 < n) :
    Nat.card (classStabilizer (orderCompletionUnits Inst.O11) 1) *
        brandtMatrix Inst.O11 n (classOf Inst.O11 1) (classOf Inst.O11 1) =
      Nat.card {γ : (QuatAlg ℚ (-1) (-11))ˣ // (γ : QuatAlg ℚ (-1) (-11)) ∈ Inst.O11.toSubalgebra ∧
        nrd (γ : QuatAlg ℚ (-1) (-11)) = n} := by
  set O := Inst.O11 with hO
  have hb := (brandt_eq_hecke (K := ℂ) (by norm_num) (by norm_num) O
    (standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq])) n hn).2.1
    (classOf O 1) (classOf O 1)
  rw [show classOf O 1 = DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
    (orderCompletionUnits O) 1 from rfl, Inst.card_classStabilizer_out] at hb
  refine hb.trans ?_
  obtain ⟨h, ⟨δ, rfl⟩, u, hu, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Units.map (finEmbed (-1) (-11)).toMonoidHom).range (orderCompletionUnits O) 1
  set x₁ := Quotient.out (DoubleCoset.mk (Units.map (finEmbed (-1) (-11)).toMonoidHom).range
    (orderCompletionUnits O) (1 : (BHat (-1) (-11))ˣ) : classSet O) with hx₁
  have hx₁' : x₁ = Units.map (finEmbed (-1) (-11)).toMonoidHom δ * 1 * u := hout
  have hpre := (lattice_local_global (-1) (-11)).1 (Subalgebra.toSubmodule O.toSubalgebra) O.fg O.span_eq_top
  have hfe : ∀ z : QuatAlg ℚ (-1) (-11), z ∈ O.toSubalgebra ↔
      finEmbed (-1) (-11) z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro z
    have := congrArg (fun S : Set (QuatAlg ℚ (-1) (-11)) => z ∈ S) hpre
    exact (eq_iff_iff.mp this).symm
  have hxu : (x₁ : BHat (-1) (-11)) * ((u⁻¹ : (BHat (-1) (-11))ˣ) : BHat (-1) (-11)) =
      finEmbed (-1) (-11) (δ : QuatAlg ℚ (-1) (-11)) := by
    rw [← Units.val_mul, hx₁', mul_one, mul_inv_cancel_right]
    rfl
  have hdx : finEmbed (-1) (-11) ((δ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * (x₁ : BHat (-1) (-11)) =
      (u : BHat (-1) (-11)) := by
    have h : (Units.map (finEmbed (-1) (-11)).toMonoidHom δ⁻¹ * x₁ : (BHat (-1) (-11))ˣ) = u := by
      rw [map_inv, hx₁', mul_one, inv_mul_cancel_left]
    exact congrArg Units.val h
  have hδ : ∀ z : QuatAlg ℚ (-1) (-11), finEmbed (-1) (-11) z =
      (x₁ : BHat (-1) (-11)) * ((u⁻¹ : (BHat (-1) (-11))ˣ) : BHat (-1) (-11)) *
        finEmbed (-1) (-11) (((δ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * z) := by
    intro z
    rw [hxu, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have hL : ∀ z, z ∈ finiteIdeleLattice O x₁ ↔
      ((δ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * z ∈ O.toSubalgebra := by
    intro z
    constructor
    · rintro ⟨y, hy, hz⟩
      rw [hfe, map_mul, hz, ← mul_assoc, hdx]
      exact mul_mem_orderCompletion O hu.1 hy
    · intro hz
      refine ⟨((u⁻¹ : (BHat (-1) (-11))ˣ) : BHat (-1) (-11)) *
        finEmbed (-1) (-11) (((δ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * z), ?_, ?_⟩
      · exact mul_mem_orderCompletion O hu.2 ((hfe _).mp hz)
      · rw [hδ z, mul_assoc]
  have hmapL : ∀ γ : (QuatAlg ℚ (-1) (-11))ˣ,
      (finiteIdeleLattice O x₁).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ (-1) (-11))) ≤ finiteIdeleLattice O x₁ ↔
        ((δ⁻¹ * γ * δ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) ∈ O.toSubalgebra := by
    intro γ
    constructor
    · intro h
      have hδL : (δ : QuatAlg ℚ (-1) (-11)) ∈ finiteIdeleLattice O x₁ := by
        rw [hL, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        exact O.toSubalgebra.one_mem
      have := (hL _).mp (h ⟨_, hδL, rfl⟩)
      simpa only [LinearMap.mulLeft_apply, Units.val_mul, mul_assoc] using this
    · rintro h _ ⟨z, hz, rfl⟩
      rw [LinearMap.mulLeft_apply, hL]
      have hz' := (hL z).mp hz
      have := O.toSubalgebra.mul_mem h hz'
      rwa [Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc (δ : QuatAlg ℚ (-1) (-11)),
        Units.mul_inv, one_mul] at this
  have hνpos := (normWeight_transform O).1 x₁
  have hν : ∀ q : ℚ, (n : ℚ) * normWeight x₁ / normWeight x₁ = n := fun _ => by
    field_simp
  have hnrd : ∀ γ : (QuatAlg ℚ (-1) (-11))ˣ,
      nrd ((δ⁻¹ * γ * δ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) = nrd (γ : QuatAlg ℚ (-1) (-11)) := by
    intro γ
    have hm := (nrd_trd_basic.{0, 0} (R := ℚ) (a := -1) (b := -11)).2.1
    have h1 : nrd ((δ⁻¹ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) * nrd (δ : QuatAlg ℚ (-1) (-11)) = 1 := by
      rw [← hm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [nrd]
    rw [Units.val_mul, Units.val_mul, hm, hm]
    linear_combination nrd (γ : QuatAlg ℚ (-1) (-11)) * h1
  refine Nat.card_congr
    { toFun := fun γ => ⟨δ⁻¹ * γ.1 * δ, (hmapL γ.1).mp γ.2.1, by rw [hnrd, γ.2.2, hν 0]⟩
      invFun := fun γ => ⟨δ * γ.1 * δ⁻¹, ?_, ?_⟩
      left_inv := fun γ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun γ => Subtype.ext (by simp [mul_assoc]) }
  · have e : δ⁻¹ * (δ * γ.1 * δ⁻¹) * δ = γ.1 := by group
    rw [hmapL, e]
    exact γ.2.1
  · have e : δ⁻¹ * (δ * γ.1 * δ⁻¹) * δ = γ.1 := by group
    rw [hν 0, ← hnrd (δ * γ.1 * δ⁻¹), e]
    exact γ.2.2

/-- `O₁₁`: the two classes `c₁, c₂` with `|Γ_{c₁}| = 4`, `|Γ_{c₂}| = 6` satisfy `B(1) = I`, `B(2) = (1 2; 3 0)`, and
`B(3)` has characteristic polynomial `(X − 4)(X + 1) = X² − 3X − 4` (trace `3`, determinant `−4`). -/
@[tf_id "III.brandt.ex:brandt-d11"]
theorem brandt_d11 :
    ∃ c₁ c₂ : classSet (pizerOrderI (-11) (by norm_num)), c₁ ≠ c₂ ∧ (∀ c, c = c₁ ∨ c = c₂) ∧
      Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) (Quotient.out c₁)) = 4 ∧
      Nat.card (classStabilizer (orderCompletionUnits (pizerOrderI (-11) (by norm_num))) (Quotient.out c₂)) = 6 ∧
      (∀ c, brandtMatrix (pizerOrderI (-11) (by norm_num)) 1 c c = 1) ∧
      (∀ c c', c ≠ c' → brandtMatrix (pizerOrderI (-11) (by norm_num)) 1 c c' = 0) ∧
      brandtMatrix (pizerOrderI (-11) (by norm_num)) 2 c₁ c₁ = 1 ∧
      brandtMatrix (pizerOrderI (-11) (by norm_num)) 2 c₁ c₂ = 2 ∧
      brandtMatrix (pizerOrderI (-11) (by norm_num)) 2 c₂ c₁ = 3 ∧
      brandtMatrix (pizerOrderI (-11) (by norm_num)) 2 c₂ c₂ = 0 ∧
      (brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₁ c₁ : ℤ) +
          brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₂ c₂ = 3 ∧
      (brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₁ c₁ : ℤ) *
          brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₂ c₂ -
        (brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₁ c₂ : ℤ) *
          brandtMatrix (pizerOrderI (-11) (by norm_num)) 3 c₂ c₁ = -4 := by
  classical
  obtain ⟨hD, ⟨hmax, -⟩, ⟨hcard, hst1, -, x, hx, hstx⟩, -, -⟩ := eichler_mass_instance_d11
  have hst1' : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) 1) = 4 := hst1
  obtain ⟨c₁, hc₁⟩ : ∃ c : classSet Inst.O11, c = classOf Inst.O11 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : classSet Inst.O11, c = classOf Inst.O11 x := ⟨_, rfl⟩
  have hne : c₁ ≠ c₂ := by
    rw [hc₁, hc₂]
    exact fun h => hx h.symm
  have hall : ∀ c, c = c₁ ∨ c = c₂ := by
    intro c
    by_contra hc
    push_neg at hc
    haveI : Finite (classSet Inst.O11) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    haveI := Fintype.ofFinite (classSet Inst.O11)
    have h3 : ({c, c₁, c₂} : Finset (classSet Inst.O11)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hc.1, hc.2]), Finset.card_pair hne]
    have := Finset.card_le_univ ({c, c₁, c₂} : Finset (classSet Inst.O11))
    rw [h3, ← Nat.card_eq_fintype_card, hcard] at this
    omega
  have hs1 : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c₁)) = 4 := by
    rw [hc₁]
    exact (Inst.card_classStabilizer_out _ 1).trans hst1
  have hs2 : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c₂)) = 6 := by
    rw [hc₂]
    exact (Inst.card_classStabilizer_out _ x).trans hstx
  -- `O₁₁` is the Eichler order of level `1` of itself
  let O₀ : MaxOrder (-1) (-11) := ⟨Inst.O11, hmax⟩
  let φ : LevelStructure O₀.1 1 :=
    { toRingHom :=
        { toFun := fun _ => 0
          map_one' := Subsingleton.elim _ _
          map_mul' := fun _ _ => Subsingleton.elim _ _
          map_zero' := rfl
          map_add' := fun _ _ => Subsingleton.elim _ _ }
      surjective := fun y => ⟨0, Subsingleton.elim _ _⟩ }
  have hE : eichlerOrder φ = Inst.O11 := by
    apply bi_qorder_ext
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
  have hrow : ∀ n : ℕ, 0 < n → Nat.Coprime n (11 * 1) → ∀ c,
      brandtMatrix Inst.O11 n c c₁ + brandtMatrix Inst.O11 n c c₂ = ArithmeticFunction.sigma 1 n := by
    intro n hn hcop c
    have h := brandt_row_sums O₀ hD φ n hn hcop
    rw [hE] at h
    have h' := h c
    rw [finsum_eq_sum_of_support_subset _ (s := {c₁, c₂})
      (fun c' _ => by rcases hall c' with rfl | rfl <;> simp), Finset.sum_pair hne] at h'
    exact h'
  have hsym : ∀ n : ℕ, 0 < n → 6 * brandtMatrix Inst.O11 n c₁ c₂ = 4 * brandtMatrix Inst.O11 n c₂ c₁ := by
    intro n hn
    have := brandt_weighted_symmetry (by norm_num) (by norm_num) Inst.O11 n hn c₁ c₂
    rwa [hs1, hs2] at this
  have hB11 : ∀ n : ℕ, 0 < n → n ≤ 3 → 4 * brandtMatrix Inst.O11 n c₁ c₁ =
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
        (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * (n : ℤ))).card := by
    intro n hn hn3
    rw [← bi_card_norm n hn hn3, ← bi_B11 n hn, hst1', hc₁]
  have k1 : ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
      (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * ((1 : ℕ) : ℤ))).card = 4 := by
    set_option maxRecDepth 2000 in decide
  have k2 : ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
      (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * ((2 : ℕ) : ℤ))).card = 4 := by
    set_option maxRecDepth 2000 in decide
  have k3 : ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-3 : ℤ) 3).filter
      (fun c => c 0 ^ 2 + c 1 ^ 2 + 11 * (c 0 + 2 * c 2) ^ 2 + 11 * (c 1 + 2 * c 3) ^ 2 = 4 * ((3 : ℕ) : ℤ))).card = 8 := by
    set_option maxRecDepth 2000 in decide
  have σ1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
  have σ2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
  have σ3 : ArithmeticFunction.sigma 1 3 = 4 := by decide
  have a1 := hB11 1 (by norm_num) (by norm_num)
  have a2 := hB11 2 (by norm_num) (by norm_num)
  have a3 := hB11 3 (by norm_num) (by norm_num)
  rw [k1] at a1
  rw [k2] at a2
  rw [k3] at a3
  have r11 := hrow 1 (by norm_num) (by norm_num) c₁
  have r12 := hrow 1 (by norm_num) (by norm_num) c₂
  have r21 := hrow 2 (by norm_num) (by norm_num) c₁
  have r22 := hrow 2 (by norm_num) (by norm_num) c₂
  have r31 := hrow 3 (by norm_num) (by norm_num) c₁
  have r32 := hrow 3 (by norm_num) (by norm_num) c₂
  rw [σ1] at r11 r12
  rw [σ2] at r21 r22
  rw [σ3] at r31 r32
  have s1 := hsym 1 (by norm_num)
  have s2 := hsym 2 (by norm_num)
  have s3 := hsym 3 (by norm_num)
  have v111 : brandtMatrix Inst.O11 1 c₁ c₁ = 1 := by omega
  have v112 : brandtMatrix Inst.O11 1 c₁ c₂ = 0 := by omega
  have v121 : brandtMatrix Inst.O11 1 c₂ c₁ = 0 := by omega
  have v122 : brandtMatrix Inst.O11 1 c₂ c₂ = 1 := by omega
  have v211 : brandtMatrix Inst.O11 2 c₁ c₁ = 1 := by omega
  have v212 : brandtMatrix Inst.O11 2 c₁ c₂ = 2 := by omega
  have v221 : brandtMatrix Inst.O11 2 c₂ c₁ = 3 := by omega
  have v222 : brandtMatrix Inst.O11 2 c₂ c₂ = 0 := by omega
  have v311 : brandtMatrix Inst.O11 3 c₁ c₁ = 2 := by omega
  have v312 : brandtMatrix Inst.O11 3 c₁ c₂ = 2 := by omega
  have v321 : brandtMatrix Inst.O11 3 c₂ c₁ = 3 := by omega
  have v322 : brandtMatrix Inst.O11 3 c₂ c₂ = 1 := by omega
  refine ⟨c₁, c₂, hne, hall, hs1, hs2, ?_, ?_, v211, v212, v221, v222, ?_, ?_⟩
  · intro c
    rcases hall c with rfl | rfl
    · exact v111
    · exact v122
  · intro c c' hcc
    rcases hall c with rfl | rfl <;> rcases hall c' with rfl | rfl
    · exact absurd rfl hcc
    · exact v112
    · exact v121
    · exact absurd rfl hcc
  · show ((brandtMatrix Inst.O11 3 c₁ c₁ : ℕ) : ℤ) + (brandtMatrix Inst.O11 3 c₂ c₂ : ℕ) = 3
    rw [v311, v322]; norm_num
  · show ((brandtMatrix Inst.O11 3 c₁ c₁ : ℕ) : ℤ) * (brandtMatrix Inst.O11 3 c₂ c₂ : ℕ) -
      (brandtMatrix Inst.O11 3 c₁ c₂ : ℕ) * (brandtMatrix Inst.O11 3 c₂ c₁ : ℕ) = -4
    rw [v311, v322, v312, v321]; norm_num

/-! ### Proof helpers for `hecke_d11_weight4` (Q3 part 6): `dim M_4(O₁₁; s) = 2`. For a unit group `Γ = O_x^×` of order
`4` or `6` in a definite algebra, `Σ_{γ ∈ Γ} P_4(trd γ, 1) = Σ (t_γ² − 1) = |Γ|` (elements are `±1` or have `t ∈ {0, ±1}`;
`t = ±1` is impossible for `|Γ| = 4` and `t = 0` for `|Γ| = 6`), so each class contributes `1`. -/

/-- `P_4(t, 1) = t² − 1`. -/
private theorem dw_poly4 (t : ℂ) : heckePolyRing 4 t 1 = t ^ 2 - 1 := by
  simp [heckePolyRing]; ring

/-- In a definite algebra, `nrd x = 1` and `trd x = t ∈ ℤ` force `t ∈ {0, ±1}` or `x = ±1` (`t = ±2`). -/
private theorem dw_elem {a b : ℤ} (ha : a < 0) (hb : b < 0) (x : QuatAlg ℚ a b) (hn : nrd x = 1) (t : ℤ)
    (ht : trd x = t) : (t = 2 ∧ x = 1) ∨ (t = -2 ∧ x = -1) ∨ t = 1 ∨ t = -1 ∨ t = 0 := by
  have hre : x.re = (t : ℚ) / 2 := by simp only [trd] at ht; linarith
  have ha' : (a : ℚ) < 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) < 0 := by exact_mod_cast hb
  have hn' : x.re ^ 2 - (a : ℚ) * x.imI ^ 2 - (b : ℚ) * x.imJ ^ 2 + (a : ℚ) * (b : ℚ) * x.imK ^ 2 = 1 := hn
  have p1 : 0 ≤ -(a : ℚ) * x.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have p2 : 0 ≤ -(b : ℚ) * x.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have p3 : 0 ≤ (a : ℚ) * (b : ℚ) * x.imK ^ 2 := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos ha'.le hb'.le) (sq_nonneg _)
  have hle : ((t : ℚ)) ^ 2 ≤ 4 := by rw [hre] at hn'; nlinarith
  have hle' : t ^ 2 ≤ 4 := by exact_mod_cast hle
  have hb2 : -2 ≤ t ∧ t ≤ 2 := by constructor <;> nlinarith
  have hpure : (t : ℚ) ^ 2 = 4 → x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
    intro h4
    rw [hre] at hn'
    have e1 : -(a : ℚ) * x.imI ^ 2 = 0 := by nlinarith
    have e2 : -(b : ℚ) * x.imJ ^ 2 = 0 := by nlinarith
    have e3 : (a : ℚ) * (b : ℚ) * x.imK ^ 2 = 0 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h (by linarith)
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h (by linarith)
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · rcases mul_eq_zero.mp e3 with h | h
      · exact absurd h (mul_ne_zero ha'.ne hb'.ne)
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  obtain ⟨h1, h2⟩ := hb2
  interval_cases t
  · right; left
    refine ⟨rfl, ?_⟩
    obtain ⟨i0, j0, k0⟩ := hpure (by norm_num)
    ext
    · rw [hre]; norm_num
    · simp [i0]
    · simp [j0]
    · simp [k0]
  · right; right; right; left; rfl
  · right; right; right; right; rfl
  · right; right; left; rfl
  · left
    refine ⟨rfl, ?_⟩
    obtain ⟨i0, j0, k0⟩ := hpure (by norm_num)
    ext
    · rw [hre]; norm_num
    · simp [i0]
    · simp [j0]
    · simp [k0]

/-- `x² = t x − 1` for `nrd x = 1`, `trd x = t`. -/
private theorem dw_quad {a b : ℤ} (x : QuatAlg ℚ a b) (hn : nrd x = 1) (t : ℤ) (ht : trd x = t) :
    x ^ 2 = (t : QuatAlg ℚ a b) * x - 1 := by
  have h := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 x).2.2.2
  rw [hn, ht, map_one, Algebra.smul_def, map_intCast] at h
  calc x ^ 2 = (x ^ 2 - (t : QuatAlg ℚ a b) * x + 1) + (t : QuatAlg ℚ a b) * x - 1 := by abel
    _ = (t : QuatAlg ℚ a b) * x - 1 := by rw [h]; abel

private theorem dw_one_ne {a b : ℤ} : (1 : QuatAlg ℚ a b) ≠ -1 := by
  intro h
  have := congrArg QuaternionAlgebra.re h
  simp at this
  norm_num at this

/-- For a unit group `Γ = O_x^×` of order `4` or `6` in a definite algebra: `Σ_{γ ∈ Γ} P_4(trd γ, 1) = |Γ|`. -/
private theorem dw_sum {a b : ℤ} (ha : a < 0) (hb : b < 0) (Ox : QOrder a b) (Γ : Subgroup (QuatAlg ℚ a b)ˣ)
    (hΓ : Γ = unitGroup Ox) (hcard : Nat.card Γ = 4 ∨ Nat.card Γ = 6) :
    ∑ᶠ γ : Γ, heckePolyRing 4 (((trd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) : ℚ) : ℂ)) 1 = (Nat.card Γ : ℂ) := by
  classical
  have hfin : Finite Γ := by rw [hΓ]; exact (unitGroup_eq_nrd_one_finite ha hb Ox).2
  have := Fintype.ofFinite Γ
  rw [finsum_eq_sum_of_fintype]
  set X : Γ → QuatAlg ℚ a b := fun γ => ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) with hX
  have hmem : ∀ γ : Γ, X γ ∈ Ox.toSubalgebra ∧ nrd (X γ) = 1 := by
    intro γ
    have : X γ ∈ {x | x ∈ Ox.toSubalgebra ∧ nrd x = 1} := by
      rw [← (unitGroup_eq_nrd_one_finite ha hb Ox).1]
      exact ⟨γ, by rw [← hΓ]; exact γ.2, rfl⟩
    exact this
  have hneg : (-1 : (QuatAlg ℚ a b)ˣ) ∈ Γ := by
    rw [hΓ]
    refine ⟨?_, ?_⟩
    · rw [Units.val_neg, Units.val_one]; exact Ox.toSubalgebra.neg_mem Ox.toSubalgebra.one_mem
    · rw [inv_neg_one, Units.val_neg, Units.val_one]; exact Ox.toSubalgebra.neg_mem Ox.toSubalgebra.one_mem
  set m1 : Γ := ⟨-1, hneg⟩ with hm1
  have hv1 : ∀ γ : Γ, γ = 1 ↔ X γ = 1 := fun γ => by rw [Subtype.ext_iff, Units.ext_iff]; rfl
  have hvm : ∀ γ : Γ, γ = m1 ↔ X γ = -1 := fun γ => by
    rw [Subtype.ext_iff, Units.ext_iff]
    show X γ = ((-1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) ↔ _
    rw [Units.val_neg, Units.val_one]
  have hpow : ∀ γ : Γ, X γ ^ Nat.card Γ = 1 := fun γ => by
    have h := pow_card_eq_one' (G := Γ) (x := γ)
    have h2 : ((γ ^ Nat.card Γ : Γ) : (QuatAlg ℚ a b)ˣ) = 1 := by rw [h]; rfl
    rw [Subgroup.coe_pow] at h2
    have h3 := congrArg Units.val h2
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h3
  have htr1 : trd (1 : QuatAlg ℚ a b) = 2 := by simp [trd]
  have htrm : trd (-1 : QuatAlg ℚ a b) = -2 := by simp [trd]
  have hne1m : (1 : Γ) ≠ m1 := fun h => dw_one_ne ((hvm 1).mp h)
  -- the value at each element
  have hval : ∀ γ : Γ, ∃ t : ℤ, trd (X γ) = t ∧
      ((t = 2 ∧ X γ = 1) ∨ (t = -2 ∧ X γ = -1) ∨ t = 1 ∨ t = -1 ∨ t = 0) := by
    intro γ
    obtain ⟨⟨t, ht⟩, -⟩ := trd_nrd_int_of_mem Ox (hmem γ).1
    exact ⟨t, ht, dw_elem ha hb _ (hmem γ).2 t ht⟩
  have hF : ∀ γ : Γ, heckePolyRing 4 (((trd (X γ) : ℚ) : ℂ)) 1 = ((trd (X γ) : ℚ) : ℂ) ^ 2 - 1 :=
    fun γ => dw_poly4 _
  rcases hcard with h4 | h6
  · -- `|Γ| = 4`: every `γ ≠ ±1` has trace `0`
    have hclaim : ∀ γ : Γ, heckePolyRing 4 (((trd (X γ) : ℚ) : ℂ)) 1 =
        -1 + ((if γ = 1 then 4 else 0) + (if γ = m1 then 4 else 0)) := by
      intro γ
      rw [hF]
      obtain ⟨t, ht, hc⟩ := hval γ
      have hq := dw_quad (X γ) (hmem γ).2 t ht
      have hp := hpow γ
      rw [h4] at hp
      rcases hc with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | rfl | rfl | rfl
      · have hg : γ = 1 := (hv1 γ).mpr h1
        subst hg
        rw [ite_eq_left rfl, ite_eq_right hne1m, ht]; norm_num
      · have hg : γ = m1 := (hvm γ).mpr h1
        subst hg
        rw [ite_eq_right (Ne.symm hne1m), ite_eq_left rfl, ht]; norm_num
      · exfalso
        push_cast at hq
        rw [one_mul] at hq
        have h3 : X γ ^ 3 = -1 := by
          rw [pow_succ', hq, mul_sub, mul_one, ← sq, hq]; abel
        have h4' : X γ = -1 := by
          have : X γ ^ 4 = X γ * X γ ^ 3 := by rw [pow_succ']
          rw [hp, h3, mul_neg, mul_one] at this
          rw [← neg_neg (X γ), ← this]
        rw [h4', htrm] at ht; norm_num at ht
      · exfalso
        push_cast at hq
        rw [neg_one_mul] at hq
        have h3 : X γ ^ 3 = 1 := by
          rw [pow_succ', hq, mul_sub, mul_neg, mul_one, ← sq, hq]; abel
        have h4' : X γ = 1 := by
          have : X γ ^ 4 = X γ * X γ ^ 3 := by rw [pow_succ']
          rw [hp, h3, mul_one] at this
          exact this.symm
        rw [h4', htr1] at ht; norm_num at ht
      · have hn1 : γ ≠ 1 := fun h => by rw [(hv1 γ).mp h, htr1] at ht; norm_num at ht
        have hnm : γ ≠ m1 := fun h => by rw [(hvm γ).mp h, htrm] at ht; norm_num at ht
        rw [ite_eq_right hn1, ite_eq_right hnm, ht]; norm_num
    rw [Finset.sum_congr rfl fun γ _ => hclaim γ, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (1 : Γ), Finset.sum_ite_eq' Finset.univ m1, ite_eq_left (Finset.mem_univ _),
      ite_eq_left (Finset.mem_univ _), Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
    norm_num
  · -- `|Γ| = 6`: no element of trace `0`
    have hclaim : ∀ γ : Γ, heckePolyRing 4 (((trd (X γ) : ℚ) : ℂ)) 1 =
        (if γ = 1 then 3 else 0) + (if γ = m1 then 3 else 0) := by
      intro γ
      rw [hF]
      obtain ⟨t, ht, hc⟩ := hval γ
      have hq := dw_quad (X γ) (hmem γ).2 t ht
      have hp := hpow γ
      rw [h6] at hp
      rcases hc with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | rfl | rfl | rfl
      · have hg : γ = 1 := (hv1 γ).mpr h1
        subst hg
        rw [ite_eq_left rfl, ite_eq_right hne1m, ht]; norm_num
      · have hg : γ = m1 := (hvm γ).mpr h1
        subst hg
        rw [ite_eq_right (Ne.symm hne1m), ite_eq_left rfl, ht]; norm_num
      · have hn1 : γ ≠ 1 := fun h => by rw [(hv1 γ).mp h, htr1] at ht; norm_num at ht
        have hnm : γ ≠ m1 := fun h => by rw [(hvm γ).mp h, htrm] at ht; norm_num at ht
        rw [ite_eq_right hn1, ite_eq_right hnm, ht]; norm_num
      · have hn1 : γ ≠ 1 := fun h => by rw [(hv1 γ).mp h, htr1] at ht; norm_num at ht
        have hnm : γ ≠ m1 := fun h => by rw [(hvm γ).mp h, htrm] at ht; norm_num at ht
        rw [ite_eq_right hn1, ite_eq_right hnm, ht]; norm_num
      · exfalso
        push_cast at hq
        rw [zero_mul, zero_sub] at hq
        have : X γ ^ 6 = (X γ ^ 2) ^ 3 := by rw [← pow_mul]
        rw [hp, hq] at this
        norm_num at this
        exact dw_one_ne this
    rw [Finset.sum_congr rfl fun γ _ => hclaim γ, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (1 : Γ), Finset.sum_ite_eq' Finset.univ m1, ite_eq_left (Finset.mem_univ _),
      ite_eq_left (Finset.mem_univ _), h6]
    norm_num

/-- `dim M_4(O₁₁; s) = 2`: both classes have `dim V_2^{Γ_c} = 1` (`|Γ_c| = 4, 6`). -/
private theorem dw_dim4 :
    Module.finrank ℂ (quatForms (pizerOrderI (-11) (by norm_num))
      (standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq])) 4) = 2 := by
  classical
  set s11 := standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq]) with hs11
  obtain ⟨-, -, ⟨hcard, hst1, -, x, hx, hstx⟩, -, -⟩ := eichler_mass_instance_d11
  obtain ⟨c₁, hc₁⟩ : ∃ c : classSet Inst.O11, c = classOf Inst.O11 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : classSet Inst.O11, c = classOf Inst.O11 x := ⟨_, rfl⟩
  have hne : c₁ ≠ c₂ := by
    rw [hc₁, hc₂]
    exact fun h => hx h.symm
  have : Finite (classSet Inst.O11) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype (classSet Inst.O11) := Fintype.ofFinite _
  have hall : ∀ c, c = c₁ ∨ c = c₂ := by
    intro c
    by_contra hc
    push_neg at hc
    have h3 : ({c, c₁, c₂} : Finset (classSet Inst.O11)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hc.1, hc.2]), Finset.card_pair hne]
    have := Finset.card_le_univ ({c, c₁, c₂} : Finset (classSet Inst.O11))
    rw [h3, ← Nat.card_eq_fintype_card, hcard] at this
    omega
  have hs1 : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c₁)) = 4 := by
    rw [hc₁]
    exact (Inst.card_classStabilizer_out _ 1).trans hst1
  have hs2 : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c₂)) = 6 := by
    rw [hc₂]
    exact (Inst.card_classStabilizer_out _ x).trans hstx
  obtain ⟨e, -⟩ := forms_class_decomposition Inst.O11 s11 4 (fun c => Quotient.out c)
    (fun c => DoubleCoset.out_eq' c)
  obtain ⟨bas, -⟩ := (symPower_basic ℂ (4 - 2)).1
  have : FiniteDimensional ℂ (symPowerModule ℂ (4 - 2)) := Module.Finite.of_basis bas
  have hW : ∀ c : classSet Inst.O11, Module.finrank ℂ
      ↥(⨅ γ : classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c),
        LinearMap.ker (splitRep s11 4 ((γ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) - 1)) = 1 := by
    intro c
    obtain ⟨⟨Ox, -, hΓ⟩, -, hfin⟩ := stabilizer_units Inst.O11 (Quotient.out c)
    have hfinΓ := (hfin (by norm_num) (by norm_num)).1
    have hnrd : ∀ γ ∈ classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c),
        nrd (γ : QuatAlg ℚ (-1) (-11)) = 1 := by
      intro γ hγ
      rw [hΓ] at hγ
      have : (γ : QuatAlg ℚ (-1) (-11)) ∈ {x | x ∈ Ox.toSubalgebra ∧ nrd x = 1} := by
        rw [← (unitGroup_eq_nrd_one_finite (by norm_num) (by norm_num) Ox).1]
        exact ⟨γ, hγ, rfl⟩
      exact this.2
    have hb := (forms_dimension (by norm_num) (by norm_num) Inst.O11 s11).2.1 4 (by norm_num) _ hfinΓ hnrd
    have hc : Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c)) = 4 ∨
        Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c)) = 6 := by
      rcases hall c with rfl | rfl
      · left; exact hs1
      · right; exact hs2
    rw [dw_sum (by norm_num) (by norm_num) Ox _ hΓ hc] at hb
    have hc0 : (Nat.card (classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c)) : ℂ) ≠ 0 := by
      rcases hc with h | h <;> rw [h] <;> norm_num
    have h1 := mul_left_cancel₀ hc0 (hb.trans (mul_one _).symm)
    exact_mod_cast h1
  have hfree : ∀ W : Submodule ℂ ↥(symPowerModule ℂ (4 - 2)), Module.Free ℂ W :=
    fun W => Module.Free.of_divisionRing ℂ W
  let E : ((c : classSet Inst.O11) → ↥(⨅ γ : classStabilizer (orderCompletionUnits Inst.O11) (Quotient.out c),
      LinearMap.ker (splitRep s11 4 ((γ : (QuatAlg ℚ (-1) (-11))ˣ) : QuatAlg ℚ (-1) (-11)) - 1))) ≃ₗ[ℂ]
      (classSet Inst.O11 → ℂ) :=
    LinearEquiv.piCongrRight fun c => LinearEquiv.ofFinrankEq _ _ (by rw [hW c, Module.finrank_self])
  rw [e.finrank_eq, E.finrank_eq, Module.finrank_pi, ← Nat.card_eq_fintype_card, hcard]

/-- (Stretch.) `dim M_4(O₁₁; s) = 2` and `T_2` on `M_4(O₁₁; s)` has characteristic polynomial `X² − 2X − 2` (trace `2`,
determinant `−2`), that of `T_2` on `S_4(Γ₀(11))`. -/
@[tf_id "III.brandt.ex:hecke-d11-weight4"]
theorem hecke_d11_weight4 :
    let s11 := standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq])
    Module.finrank ℂ (quatForms (pizerOrderI (-11) (by norm_num)) s11 4) = 2 ∧
    ∃ T : Module.End ℂ (quatForms (pizerOrderI (-11) (by norm_num)) s11 4),
      (∀ f : quatForms (pizerOrderI (-11) (by norm_num)) s11 4,
        ((T f : quatForms (pizerOrderI (-11) (by norm_num)) s11 4) : (BHat (-1) (-11))ˣ → symPowerModule ℂ (4 - 2)) =
          heckeOperator (pizerOrderI (-11) (by norm_num)) 2 (f : (BHat (-1) (-11))ˣ → symPowerModule ℂ (4 - 2))) ∧
      LinearMap.trace ℂ _ T = 2 ∧ LinearMap.det (M := quatForms (pizerOrderI (-11) (by norm_num)) s11 4) T = -2 := by
  intro s11
  refine ⟨dw_dim4, ?_⟩
  -- `T_2` on `M_4(O₁₁; s)`: trace `2`, determinant `−2`; not yet formalized (Part 6 notes)
  sorry

end GL2TF.Quat
