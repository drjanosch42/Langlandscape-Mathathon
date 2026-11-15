import AlgJL.VolI.P1.Spherical
import AlgJL.VolI.P0.Haar
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/HeckeBasis.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (2): `hecke_mem_smoothCompact`, `spherical_convolution_haar`.
Dropped tagged IDs: `I.satake.thm:spherical-convolution-haar`. -/

/-!
# The Hecke basis and the Hecke recursion (M5a, unit U0)

Lean counterpart of `vol1/ch-1-01-spherical.tex` §2 and of `I.satake.thm:spherical-convolution-haar` (§1). Owner: L1.

`H(G, K) = sphericalHeckeAlgebra F` is the coset model of M1 (vendored `HeckePair`). The basis element
`c_{a,b} = 1_{K t_{a,b} K}` is the vendored `HeckePair.heckeIndicator` of the Cartan element `t_{a,b}`; its
finiteness proof is `double_coset_index` (and the swap `t_{a,b} ∈ K t_{b,a} K` for `a < b`). The left-coset
representatives `h(i, j, x) = (ϖ^i x; 0 ϖ^j)` are M1's `hmat` (`Decompositions.lean`), tagged here as a B-only item.
`T_ϖ = c_{1,0}` and `R_ϖ = c_{1,1}` are written out as `heckeBasis F 1 0` and `heckeBasis F 1 1`.
-/

attribute [tf_aux "X.hpair.def:double-coset"] HeckePair.doubleCoset
attribute [tf_aux "X.hpair.def:hecke-indicator"] HeckePair.heckeIndicator
attribute [tf_aux "I.satake.def:upper-coset-matrix"] GL2TF.Local.hmat

open ValuativeRel GL2TF MeasureTheory
open scoped Pointwise

namespace GL2TF.Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- `ϖ_F` as an element of `F` (local notation). -/
local notation "ϖ" => ((unif F : 𝒪[F]) : F)

/-! ### Item 1: the basis functions `c_{a,b}` -/

/-- `K t_{a,b} K` is a finite union of left cosets `gK`, for all `a, b ∈ ℤ` (`double_coset_index` for `a ≥ b`, and
`t_{a,b} ∈ K t_{b,a} K` for `a < b`); i.e. `c_{a,b} ∈ H(G, K)`. -/
@[tf_aux "I.satake.lem:hecke-basis-mem"]
theorem finite_cosets_cartan (a b : ℤ) :
    (QuotientGroup.mk '' ((𝐊[F] : Set (GL (Fin 2) F)) * ({cartanElement F a b} : Set (GL (Fin 2) F))) :
      Set (GL (Fin 2) F ⧸ 𝐊[F])).Finite := by
  rw [← HeckePair.image_mk_doubleCoset]
  show (QuotientGroup.mk '' DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] :
    Set (GL (Fin 2) F ⧸ 𝐊[F])).Finite
  rcases le_total b a with hab | hba
  · exact (double_coset_index F a b hab).1
  · have hmem : cartanElement F a b ∈ DoubleCoset.doubleCoset (cartanElement F b a) 𝐊[F] 𝐊[F] := by
      refine DoubleCoset.mem_doubleCoset.mpr ⟨cartanSwap, cartanSwap_mem, cartanSwap, cartanSwap_mem, ?_⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, cartanSwap_val, cartanElement_val, cartanElement_val]
      simp
    rw [DoubleCoset.doubleCoset_eq_of_mem hmem]
    exact (double_coset_index F b a hba).1

/-- The Hecke basis function `c_{a,b} = 1_{K t_{a,b} K} ∈ H(G, K)` for `a, b ∈ ℤ`; `T_ϖ = c_{1,0}`, `R_ϖ = c_{1,1}`. -/
@[tf_id "I.satake.def:hecke-basis"]
noncomputable def heckeBasis (a b : ℤ) : sphericalHeckeAlgebra F :=
  HeckePair.heckeIndicator ℂ (cartanElement F a b) (finite_cosets_cartan F a b)

variable {F}

theorem heckeBasis_apply_of_mem {a b : ℤ} {x : GL (Fin 2) F}
    (hx : x ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F]) :
    ((heckeBasis F a b : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) x = 1 :=
  HeckePair.heckeIndicator_apply_of_mem _ (by simpa [HeckePair.doubleCoset, DoubleCoset.doubleCoset] using hx)

theorem heckeBasis_apply_of_notMem {a b : ℤ} {x : GL (Fin 2) F}
    (hx : x ∉ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F]) :
    ((heckeBasis F a b : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) x = 0 :=
  HeckePair.heckeIndicator_apply_of_notMem _ (by simpa [HeckePair.doubleCoset, DoubleCoset.doubleCoset] using hx)

/-! ### Item 2: left-coset representatives -/

theorem v_zpow_le_iff'' {m n : ℤ} : valuation F ϖ ^ m ≤ valuation F ϖ ^ n ↔ n ≤ m := by
  rw [← map_zpow₀, ← map_zpow₀]; exact v_zpow_le_iff

/-- `h(i, j, x) ∈ K t_{a,b} K` (`a ≥ b`) iff `b ≤ i`, `b ≤ j`, `i + j = a + b`, `v(x) ≤ v(ϖ^b)` and one of the three
is an equality, i.e. `min(i, j, ord x) = b` (proof helper; M1's `hmat_mem_iff` is the case `b = 0`). -/
theorem hmat_mem_iff_gen (a b : ℤ) (hab : b ≤ a) (i j : ℤ) (x : F) :
    hmat i j x ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] ↔
      b ≤ i ∧ b ≤ j ∧ i + j = a + b ∧ valuation F x ≤ valuation F (ϖ ^ b) ∧
        (i = b ∨ j = b ∨ valuation F x = valuation F (ϖ ^ b)) := by
  have hv0 : (0 : ValueGroupWithZero F) ≠ valuation F ϖ ^ b := by
    rw [← map_zpow₀]; exact (v_ne_zero (zpow_ne_zero _ (unif_ne_zero F))).symm
  rw [cartan_invariants F a b hab, exists_unit_iff_v_eq _ _ (zpow_ne_zero _ (unif_ne_zero F))]
  change entrySpan F (hmat i j x) = _ ∧ _ ↔ _
  rw [entrySpan_eq_iff, hmat_val, Matrix.det_fin_two_of, ← zpow_add₀ (unif_ne_zero F)]
  simp only [Fin.forall_fin_two, Fin.exists_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, map_zero, mul_zero, sub_zero, map_zpow₀, v_zpow_le_iff'', v_zpow_inj', zero_le,
    true_and, hv0, false_or]
  tauto

variable (F) in
/-- Left-coset representatives. Let `R i ⊆ F` be a set of representatives of `F/ϖ^i 𝒪` for every `i ∈ ℤ`.
(a) Every left coset `gK` contains exactly one `h(i, j, x) = (ϖ^i x; 0 ϖ^j)` with `x ∈ R i`.
(b) For `a ≥ b`: `h(i, j, x) ∈ K t_{a,b} K` iff `i + j = a + b` and `min(i, j, ord x) = b`, written with the
valuation: `b ≤ i`, `b ≤ j`, `v(x) ≤ v(ϖ^b)`, and `i = b` or `j = b` or `v(x) = v(ϖ^b)`. -/
@[tf_id "I.satake.lem:left-coset-representatives"]
theorem left_coset_representatives (R : ℤ → Set F)
    (hR : ∀ i : ℤ, ∀ x : F, ∃! r : F, r ∈ R i ∧ valuation F (x - r) ≤ valuation F (ϖ ^ i)) :
    (∀ g : GL (Fin 2) F, ∃! p : ℤ × ℤ × F, p.2.2 ∈ R p.1 ∧
        (g : GL (Fin 2) F ⧸ 𝐊[F]) = (hmat p.1 p.2.1 p.2.2 : GL (Fin 2) F ⧸ 𝐊[F])) ∧
      ∀ a b : ℤ, b ≤ a → ∀ i j : ℤ, ∀ x : F,
        (hmat i j x ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] ↔
          i + j = a + b ∧ b ≤ i ∧ b ≤ j ∧ valuation F x ≤ valuation F (ϖ ^ b) ∧
            (i = b ∨ j = b ∨ valuation F x = valuation F (ϖ ^ b))) := by
  refine ⟨fun g => ?_, fun a b hab i j x => by rw [hmat_mem_iff_gen a b hab]; tauto⟩
  obtain ⟨i, j, x, hx⟩ := exists_hmat g
  obtain ⟨r, ⟨hr, hxr⟩, -⟩ := hR i x
  refine ⟨(i, j, r), ⟨hr, hx.trans ((hmat_mk_eq_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, ?_⟩)⟩, ?_⟩
  · rwa [Valuation.map_sub_swap]
  · rintro ⟨i', j', r'⟩ ⟨hr', hg'⟩
    obtain ⟨h1, h2, h3⟩ := (hmat_mk_eq_iff _ _ _ _ _ _).mp (hx.symm.trans hg')
    subst h1 h2
    have : r' = r := (hR i x).unique ⟨hr', by rwa [Valuation.map_sub_swap]⟩ ⟨hr, hxr⟩
    rw [this]

/-! ### Item 3: the basis -/

theorem hecke_apply_eq_cartan (f : sphericalHeckeAlgebra F) {a b : ℤ} {x : GL (Fin 2) F}
    (hx : x ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F]) :
    (f : GL (Fin 2) F → ℂ) x = (f : GL (Fin 2) F → ℂ) (cartanElement F a b) := by
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  rw [HeckePair.apply_mul_right f hk', HeckePair.apply_left_mul f hk]

theorem hecke_ext_cartan {f g : sphericalHeckeAlgebra F}
    (h : ∀ c d : ℤ, d ≤ c → (f : GL (Fin 2) F → ℂ) (cartanElement F c d) =
      (g : GL (Fin 2) F → ℂ) (cartanElement F c d)) : f = g := by
  apply HeckePair.ext
  intro x
  obtain ⟨⟨c, d⟩, ⟨hcd, hx⟩, -⟩ := cartan_decomposition F x
  rw [hecke_apply_eq_cartan f hx, hecke_apply_eq_cartan g hx]
  exact h c d hcd

theorem heckeBasis_apply_cartan {a b c d : ℤ} (hab : b ≤ a) (hcd : d ≤ c) :
    ((heckeBasis F a b : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) (cartanElement F c d) =
      if (a, b) = (c, d) then 1 else 0 := by
  split_ifs with h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact heckeBasis_apply_of_mem (DoubleCoset.mem_doubleCoset_self _ _ _)
  · apply heckeBasis_apply_of_notMem
    intro hmem
    exact h ((cartan_decomposition F (cartanElement F c d)).unique ⟨hab, hmem⟩
      ⟨hcd, DoubleCoset.mem_doubleCoset_self _ _ _⟩)

/-- Evaluation at `x` as an additive map. -/
noncomputable def heckeEval (x : GL (Fin 2) F) : sphericalHeckeAlgebra F →+ ℂ where
  toFun f := (f : GL (Fin 2) F → ℂ) x
  map_zero' := rfl
  map_add' _ _ := rfl

theorem heckeEval_apply (x : GL (Fin 2) F) (f : sphericalHeckeAlgebra F) :
    heckeEval x f = (f : GL (Fin 2) F → ℂ) x := rfl

variable (F) in
/-- The `c_{a,b}` with `a ≥ b` form a `ℂ`-basis of `H(G, K)`: they are linearly independent, and every `f ∈ H(G, K)`
has `f(t_{a,b}) ≠ 0` for only finitely many `a ≥ b` and equals `∑_{a ≥ b} f(t_{a,b}) c_{a,b}`. -/
@[tf_id "I.satake.thm:hecke-basis-basis"]
theorem hecke_basis_basis :
    LinearIndependent ℂ (fun p : {p : ℤ × ℤ // p.2 ≤ p.1} => heckeBasis F p.1.1 p.1.2) ∧
      ∀ f : sphericalHeckeAlgebra F,
        {p : {p : ℤ × ℤ // p.2 ≤ p.1} | (f : GL (Fin 2) F → ℂ) (cartanElement F p.1.1 p.1.2) ≠ 0}.Finite ∧
          f = ∑ᶠ p : {p : ℤ × ℤ // p.2 ≤ p.1},
            (f : GL (Fin 2) F → ℂ) (cartanElement F p.1.1 p.1.2) • heckeBasis F p.1.1 p.1.2 := by
  have hδ : ∀ p p' : {p : ℤ × ℤ // p.2 ≤ p.1},
      ((heckeBasis F p'.1.1 p'.1.2 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ)
        (cartanElement F p.1.1 p.1.2) = if p' = p then 1 else 0 := by
    intro p p'
    by_cases h : p' = p
    · subst h; rw [heckeBasis_apply_cartan p'.2 p'.2, ite_eq_left rfl, ite_eq_left rfl]
    · rw [heckeBasis_apply_cartan p'.2 p.2, ite_eq_right, ite_eq_right h]
      intro h'
      exact h (Subtype.ext (Prod.ext (congrArg Prod.fst h') (congrArg Prod.snd h')))
  refine ⟨linearIndependent_iff'.mpr fun s g hg i hi => ?_, fun f => ?_⟩
  · have := congrArg (heckeEval (cartanElement F i.1.1 i.1.2)) hg
    rw [map_sum, map_zero] at this
    simp only [heckeEval_apply, HeckePair.coe_apply_smul, hδ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', ite_eq_left hi] at this
    exact this
  · have hinj : Function.Injective (fun p : {p : ℤ × ℤ // p.2 ≤ p.1} =>
        ((cartanElement F p.1.1 p.1.2 : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F])) := by
      intro p p' h
      change ((cartanElement F p.1.1 p.1.2 : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F]) =
        ((cartanElement F p'.1.1 p'.1.2 : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F]) at h
      have h' := QuotientGroup.eq.mp h
      have hmem : cartanElement F p'.1.1 p'.1.2 ∈
          DoubleCoset.doubleCoset (cartanElement F p.1.1 p.1.2) 𝐊[F] 𝐊[F] :=
        DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, _, h', by group⟩
      exact Subtype.ext ((cartan_decomposition F _).unique ⟨p.2, hmem⟩
        ⟨p'.2, DoubleCoset.mem_doubleCoset_self _ _ _⟩)
    have hfin : {p : {p : ℤ × ℤ // p.2 ≤ p.1} |
        (f : GL (Fin 2) F → ℂ) (cartanElement F p.1.1 p.1.2) ≠ 0}.Finite :=
      ((HeckePair.finite_cosets f).preimage fun _ _ _ _ h => hinj h).subset fun p hp => ⟨_, hp, rfl⟩
    refine ⟨hfin, ?_⟩
    have hsupp : (Function.support fun p : {p : ℤ × ℤ // p.2 ≤ p.1} =>
        (f : GL (Fin 2) F → ℂ) (cartanElement F p.1.1 p.1.2) • heckeBasis F p.1.1 p.1.2).Finite :=
      hfin.subset fun p hp h0 => hp (by simp [h0])
    apply hecke_ext_cartan
    intro c d hcd
    show _ = heckeEval (cartanElement F c d) (∑ᶠ p : {p : ℤ × ℤ // p.2 ≤ p.1},
      (f : GL (Fin 2) F → ℂ) (cartanElement F p.1.1 p.1.2) • heckeBasis F p.1.1 p.1.2)
    rw [map_finsum _ hsupp]
    simp only [heckeEval_apply, HeckePair.coe_apply_smul]
    rw [finsum_eq_single _ ⟨(c, d), hcd⟩]
    · show (f : GL (Fin 2) F → ℂ) (cartanElement F c d) = (f : GL (Fin 2) F → ℂ) (cartanElement F c d) *
        ((heckeBasis F c d : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) (cartanElement F c d)
      rw [heckeBasis_apply_cartan hcd hcd, ite_eq_left rfl, mul_one]
    · intro p hp
      rw [hδ ⟨(c, d), hcd⟩ p, ite_eq_right hp, mul_zero]

/-! ### Item 4: the Hecke recursion -/

/-- Representatives of the `q + 1` left cosets in `K t_{1,0} K`: `h(0, 1, 0)` and `h(1, 0, u)`, `u ∈ 𝒪/ϖ`. -/
noncomputable def heckeTRep : Option (𝒪[F] ⧸ Ideal.span {unif F ^ 1}) → GL (Fin 2) F
  | none => hmat 0 1 0
  | some ξ => hmat 1 0 ((Quotient.out ξ : 𝒪[F]) : F)

theorem heckeTRep_mem (o : Option (𝒪[F] ⧸ Ideal.span {unif F ^ 1})) :
    heckeTRep o ∈ DoubleCoset.doubleCoset (cartanElement F 1 0) 𝐊[F] 𝐊[F] := by
  cases o with
  | none =>
    exact (hmat_mem_iff_gen 1 0 zero_le_one 0 1 0).mpr ⟨le_rfl, zero_le_one, by norm_num, by simp, Or.inl rfl⟩
  | some ξ =>
    exact (hmat_mem_iff_gen 1 0 zero_le_one 1 0 _).mpr ⟨zero_le_one, le_rfl, by norm_num,
      by simpa using (Valuation.mem_integer_iff _ _).mp (Quotient.out ξ).2, Or.inr (Or.inl rfl)⟩

theorem heckeTRep_injective :
    Function.Injective (fun o => (heckeTRep (F := F) o : GL (Fin 2) F ⧸ 𝐊[F])) := by
  rintro (_ | ξ) (_ | ξ') h <;> simp only [heckeTRep] at h
  · rfl
  · exact absurd ((hmat_mk_eq_iff _ _ _ _ _ _).mp h).1 (by norm_num)
  · exact absurd ((hmat_mk_eq_iff _ _ _ _ _ _).mp h).1 (by norm_num)
  · obtain ⟨-, -, h3⟩ := (hmat_mk_eq_iff _ _ _ _ _ _).mp h
    congr 1
    rw [← Quotient.out_eq ξ, ← Quotient.out_eq ξ']
    refine Ideal.Quotient.eq.mpr ((mem_span_pow_iff _ _).mpr ?_)
    push_cast
    rw [Valuation.map_sub_swap]
    exact h3

theorem range_heckeTRep :
    Set.range (fun o => (heckeTRep (F := F) o : GL (Fin 2) F ⧸ 𝐊[F])) =
      QuotientGroup.mk '' DoubleCoset.doubleCoset (cartanElement F 1 0) 𝐊[F] 𝐊[F] := by
  ext c
  constructor
  · rintro ⟨o, rfl⟩
    exact ⟨_, heckeTRep_mem o, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨i, j, x, hgx⟩ := exists_hmat g
    have hmem := mem_doubleCoset_of_mk_eq hg hgx
    obtain ⟨hi, hj, hij, hx, -⟩ := (hmat_mem_iff_gen 1 0 zero_le_one i j x).mp hmem
    have hx1 : valuation F x ≤ 1 := by simpa using hx
    have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨none, ?_⟩
      simp only [heckeTRep]
      rw [hgx, hmat_mk_eq_iff]
      exact ⟨rfl, rfl, by simpa using hx1⟩
    · let x₀ : 𝒪[F] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx1⟩
      refine ⟨some (Ideal.Quotient.mk _ x₀), ?_⟩
      simp only [heckeTRep]
      rw [hgx, hmat_mk_eq_iff]
      refine ⟨rfl, rfl, ?_⟩
      have := (mem_span_pow_iff _ _).mp (out_sub_mem (Ideal.span {unif F ^ 1}) x₀)
      push_cast at this
      rw [Valuation.map_sub_swap]
      exact this

/-- A finite coset sum against `T_ϖ = c_{1,0}`: `∑_{gK} c_{1,0}(g) τ(g) = τ(h(0,1,0)) + ∑_{u ∈ 𝒪/ϖ} τ(h(1,0,u))`
for right-`K`-invariant `τ`. -/
theorem finsum_heckeT {A : Type*} [AddCommMonoid A] [Module ℂ A] (τ : GL (Fin 2) F → A)
    (hτ : ∀ g, ∀ k ∈ 𝐊[F], τ (g * k) = τ g) :
    ∑ᶠ c : GL (Fin 2) F ⧸ 𝐊[F], ((heckeBasis F 1 0 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) c.out • τ c.out =
      τ (hmat 0 1 0) + ∑ᶠ ξ : 𝒪[F] ⧸ Ideal.span {unif F ^ 1}, τ (hmat 1 0 ((Quotient.out ξ : 𝒪[F]) : F)) := by
  have hout : ∀ g : GL (Fin 2) F, τ (Quotient.out (QuotientGroup.mk g : GL (Fin 2) F ⧸ 𝐊[F])) = τ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul 𝐊[F] g
    rw [hk, hτ g k k.2]
  have hsub : (Function.support fun c : GL (Fin 2) F ⧸ 𝐊[F] =>
      ((heckeBasis F 1 0 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) c.out • τ c.out) ⊆
      Set.range (fun o => (heckeTRep (F := F) o : GL (Fin 2) F ⧸ 𝐊[F])) := by
    intro c hc
    rw [range_heckeTRep]
    by_contra hnot
    apply hc
    show ((heckeBasis F 1 0 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) c.out • τ c.out = 0
    rw [heckeBasis_apply_of_notMem, zero_smul]
    intro hmem
    exact hnot ⟨_, hmem, QuotientGroup.out_eq' c⟩
  have hterm : ∀ o, ((heckeBasis F 1 0 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ)
      (Quotient.out (heckeTRep o : GL (Fin 2) F ⧸ 𝐊[F])) •
        τ (Quotient.out (heckeTRep o : GL (Fin 2) F ⧸ 𝐊[F])) = τ (heckeTRep o) := by
    intro o
    rw [heckeBasis_apply_of_mem (mem_doubleCoset_of_mk_eq (heckeTRep_mem o) (QuotientGroup.out_eq' _).symm),
      one_smul, hout]
  have : Finite (𝒪[F] ⧸ Ideal.span {unif F ^ 1}) := finite_quot_span_pow 1
  letI := Fintype.ofFinite (𝒪[F] ⧸ Ideal.span {unif F ^ 1})
  calc _ = ∑ᶠ c ∈ Set.range (fun o => (heckeTRep (F := F) o : GL (Fin 2) F ⧸ 𝐊[F])),
        ((heckeBasis F 1 0 : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) c.out • τ c.out := by
        rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub]
    _ = ∑ᶠ o, τ (heckeTRep o) := by
        rw [finsum_mem_range heckeTRep_injective]
        exact finsum_congr hterm
    _ = _ := by
        rw [finsum_eq_sum_of_fintype, Fintype.sum_option, finsum_eq_sum_of_fintype]
        rfl

theorem hmat_zero_one_inv_mul (c d : ℤ) :
    (hmat 0 1 0)⁻¹ * cartanElement F c d = hmat c (d - 1) 0 := by
  rw [inv_mul_eq_iff_eq_mul]
  apply Units.ext
  have h := unif_ne_zero F
  rw [Units.val_mul, hmat_val, hmat_val, cartanElement_val, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zpow_sub_one₀ h] <;> field_simp <;> ring

theorem hmat_one_zero_inv_mul (y : F) (c d : ℤ) :
    (hmat 1 0 y)⁻¹ * cartanElement F c d = hmat (c - 1) d (-y * ϖ ^ (d - 1)) := by
  rw [inv_mul_eq_iff_eq_mul]
  apply Units.ext
  have h := unif_ne_zero F
  rw [Units.val_mul, hmat_val, hmat_val, cartanElement_val, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zpow_sub_one₀ h] <;> field_simp <;> ring

theorem heckeT_mul_apply (f : sphericalHeckeAlgebra F) (x : GL (Fin 2) F) :
    ((heckeBasis F 1 0 * f : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) x =
      (f : GL (Fin 2) F → ℂ) ((hmat 0 1 0)⁻¹ * x) + ∑ᶠ ξ : 𝒪[F] ⧸ Ideal.span {unif F ^ 1},
        (f : GL (Fin 2) F → ℂ) ((hmat 1 0 ((Quotient.out ξ : 𝒪[F]) : F))⁻¹ * x) := by
  rw [HeckePair.mul_apply]
  refine (finsum_congr fun c => ?_).trans (finsum_heckeT (fun g => (f : GL (Fin 2) F → ℂ) (g⁻¹ * x)) ?_)
  · conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [HeckePair.convTerm_mk, smul_eq_mul]
  · intro g k hk
    show (f : GL (Fin 2) F → ℂ) ((g * k)⁻¹ * x) = (f : GL (Fin 2) F → ℂ) (g⁻¹ * x)
    rw [mul_inv_rev, mul_assoc]
    exact HeckePair.apply_left_mul f (inv_mem hk) _

theorem isUnit_iff_v_eq_one (y : 𝒪[F]) : IsUnit y ↔ valuation F (y : F) = 1 :=
  (Valuation.integer.integers _).isUnit_iff_valuation_eq_one

theorem heckeT_none_mem_iff {a b c d : ℤ} (hab : b ≤ a) (hcd : d ≤ c) :
    hmat c (d - 1) 0 ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] ↔ c = a ∧ d = b + 1 := by
  rw [hmat_mem_iff_gen a b hab]
  have h3 : (0 : ValueGroupWithZero F) ≠ valuation F (ϖ ^ b) :=
    (v_ne_zero (zpow_ne_zero _ (unif_ne_zero F))).symm
  simp only [map_zero, zero_le, h3, or_false, true_and, and_true]
  constructor <;> intro h <;> omega

theorem heckeT_term_mem_iff {a b : ℤ} (hab : b ≤ a) (c d : ℤ) (y : 𝒪[F]) :
    hmat (c - 1) d (-(y : F) * ϖ ^ (d - 1)) ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] ↔
      c - 1 + d = a + b ∧ b ≤ c - 1 ∧ b ≤ d ∧ ¬ (d = b ∧ IsUnit y) ∧
        (c - 1 = b ∨ d = b ∨ (IsUnit y ∧ d = b + 1)) := by
  rw [hmat_mem_iff_gen a b hab, isUnit_iff_v_eq_one]
  rcases eq_or_ne (y : F) 0 with hy0 | hy0
  · have h1 : valuation F (-(y : F) * ϖ ^ (d - 1)) = 0 := by rw [hy0]; simp
    have h2 : valuation F (y : F) ≠ 1 := by rw [hy0, map_zero]; exact zero_ne_one
    have h3 : (0 : ValueGroupWithZero F) ≠ valuation F (ϖ ^ b) :=
      (v_ne_zero (zpow_ne_zero _ (unif_ne_zero F))).symm
    simp only [h1, h2, h3, zero_le, and_false, false_and, or_false, not_false_eq_true, true_and,
      and_true]
    tauto
  · obtain ⟨n, hn⟩ := exists_v_eq_zpow (y : F) hy0
    have hn0 : 0 ≤ n := v_zpow_le_one_iff.mp (by rw [← hn]; exact (Valuation.mem_integer_iff _ _).mp y.2)
    have hv : valuation F (-(y : F) * ϖ ^ (d - 1)) = valuation F (ϖ ^ (n + (d - 1))) := by
      rw [map_mul, Valuation.map_neg, hn, ← map_mul, zpow_add₀ (unif_ne_zero F)]
    rw [hv, hn, v_zpow_le_iff, v_zpow_inj, v_zpow_eq_one_iff]
    constructor <;> intro h <;> omega

theorem finsum_eq_card {α : Type*} [Finite α] (P : α → Prop) (f : α → ℂ)
    (hf : ∀ x, (P x → f x = 1) ∧ (¬ P x → f x = 0)) :
    ∑ᶠ x, f x = (Nat.card {x // P x} : ℂ) := by
  classical
  letI := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : P x
  · rw [(hf x).1 h, ite_eq_left h]
  · rw [(hf x).2 h, ite_eq_right h]

theorem heckeT_mul_heckeBasis_apply {a b c d : ℤ} (hab : b ≤ a) (hcd : d ≤ c) :
    ((heckeBasis F 1 0 * heckeBasis F a b : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) (cartanElement F c d) =
      if c = a + 1 ∧ d = b then 1 else if c = a ∧ d = b + 1 then
        (if a - b = 1 then (q F : ℂ) + 1 else (q F : ℂ)) else 0 := by
  have : Finite (𝒪[F] ⧸ Ideal.span {unif F ^ 1}) := finite_quot_span_pow 1
  have hq : 1 ≤ q F := residue_card_pos
  rw [heckeT_mul_apply]
  simp only [hmat_zero_one_inv_mul, hmat_one_zero_inv_mul]
  by_cases hA : c = a + 1 ∧ d = b
  · rw [ite_eq_left hA]
    obtain ⟨rfl, rfl⟩ := hA
    rw [heckeBasis_apply_of_notMem (by rw [heckeT_none_mem_iff hab hcd]; omega), zero_add]
    refine (finsum_eq_card (fun ξ : 𝒪[F] ⧸ Ideal.span {unif F ^ 1} => ¬ IsUnit (Quotient.out ξ)) _
      fun ξ => ⟨fun h => ?_, fun h => ?_⟩).trans ?_
    · exact heckeBasis_apply_of_mem ((heckeT_term_mem_iff hab _ _ _).mpr
        ⟨by ring, by omega, le_rfl, fun h' => h h'.2, Or.inr (Or.inl rfl)⟩)
    · exact heckeBasis_apply_of_notMem fun hm => h fun hu => ((heckeT_term_mem_iff hab _ _ _).mp hm).2.2.2.1 ⟨rfl, hu⟩
    · have := card_nonunit (F := F) 0
      simp only [zero_add, pow_zero] at this
      rw [this, Nat.cast_one]
  rw [ite_eq_right hA]
  by_cases hB : c = a ∧ d = b + 1
  · rw [ite_eq_left hB]
    obtain ⟨rfl, rfl⟩ := hB
    rw [heckeBasis_apply_of_mem (by rw [heckeT_none_mem_iff hab hcd]; omega)]
    by_cases h1 : c - b = 1
    · rw [ite_eq_left h1]
      refine (congrArg _ (finsum_eq_card (fun _ : 𝒪[F] ⧸ Ideal.span {unif F ^ 1} => True) _
        fun ξ => ⟨fun _ => ?_, fun h => absurd trivial h⟩)).trans ?_
      · exact heckeBasis_apply_of_mem ((heckeT_term_mem_iff hab _ _ _).mpr
          ⟨by ring, by omega, by omega, fun h' => by omega, Or.inl (by omega)⟩)
      · rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), card_quot_span_pow, pow_one]
        ring
    · rw [ite_eq_right h1]
      refine (congrArg _ (finsum_eq_card (fun ξ : 𝒪[F] ⧸ Ideal.span {unif F ^ 1} => IsUnit (Quotient.out ξ)) _
        fun ξ => ⟨fun h => ?_, fun h => ?_⟩)).trans ?_
      · exact heckeBasis_apply_of_mem ((heckeT_term_mem_iff hab _ _ _).mpr
          ⟨by ring, by omega, by omega, fun h' => by omega, Or.inr (Or.inr ⟨h, rfl⟩)⟩)
      · refine heckeBasis_apply_of_notMem fun hm => ?_
        obtain ⟨-, -, -, -, h5⟩ := (heckeT_term_mem_iff hab _ _ _).mp hm
        rcases h5 with h5 | h5 | h5
        · omega
        · omega
        · exact h h5.1
      · have := card_unit (F := F) 0
        simp only [zero_add, pow_zero, pow_one] at this
        rw [this, Nat.cast_sub hq, Nat.cast_one]
        ring
  · rw [ite_eq_right hB, heckeBasis_apply_of_notMem (by rw [heckeT_none_mem_iff hab hcd]; exact hB), zero_add]
    refine (finsum_congr fun ξ => heckeBasis_apply_of_notMem fun hm => ?_).trans finsum_zero
    obtain ⟨h1, h2, h3, h4, h5⟩ := (heckeT_term_mem_iff hab _ _ _).mp hm
    by_cases hu : IsUnit (Quotient.out ξ)
    · simp only [hu, and_true, true_and] at h4 h5
      omega
    · simp only [hu, and_false, false_and, or_false, not_false_eq_true] at h4 h5
      omega

variable (F) in
/-- The Hecke recursion: for `a ≥ b`, `T_ϖ ∗ c_{a,b} = c_{a+1,b} + q c_{a,b+1}` if `a - b ≥ 2`,
`= c_{a+1,b} + (q + 1) c_{a,a}` if `a - b = 1`, and `= c_{a+1,a}` if `a = b`. -/
@[tf_id "I.satake.thm:hecke-recursion"]
theorem hecke_recursion (a b : ℤ) (hab : b ≤ a) :
    (2 ≤ a - b → heckeBasis F 1 0 * heckeBasis F a b =
        heckeBasis F (a + 1) b + (q F : ℂ) • heckeBasis F a (b + 1)) ∧
      (a - b = 1 → heckeBasis F 1 0 * heckeBasis F a b =
        heckeBasis F (a + 1) b + ((q F : ℂ) + 1) • heckeBasis F a a) ∧
      (a = b → heckeBasis F 1 0 * heckeBasis F a b = heckeBasis F (a + 1) a) := by
  refine ⟨fun h2 => ?_, fun h1 => ?_, fun h0 => ?_⟩
  · apply hecke_ext_cartan
    intro c d hcd
    rw [heckeT_mul_heckeBasis_apply hab hcd]
    simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul,
      heckeBasis_apply_cartan (show b ≤ a + 1 by omega) hcd,
      heckeBasis_apply_cartan (show b + 1 ≤ a by omega) hcd, Prod.mk.injEq]
    have hne : a - b ≠ 1 := by omega
    by_cases hA : c = a + 1 ∧ d = b
    · obtain ⟨rfl, rfl⟩ := hA; simp
    · by_cases hB : c = a ∧ d = b + 1
      · obtain ⟨rfl, rfl⟩ := hB; simp [hne]
      · rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right (fun h => hA ⟨h.1.symm, h.2.symm⟩),
          ite_eq_right (fun h => hB ⟨h.1.symm, h.2.symm⟩)]
        ring
  · obtain rfl : a = b + 1 := by omega
    apply hecke_ext_cartan
    intro c d hcd
    rw [heckeT_mul_heckeBasis_apply hab hcd]
    simp only [HeckePair.coe_apply_add, HeckePair.coe_apply_smul,
      heckeBasis_apply_cartan (show b ≤ b + 1 + 1 by omega) hcd,
      heckeBasis_apply_cartan (le_refl (b + 1)) hcd, Prod.mk.injEq]
    by_cases hA : c = b + 1 + 1 ∧ d = b
    · obtain ⟨rfl, rfl⟩ := hA; simp
    · by_cases hB : c = b + 1 ∧ d = b + 1
      · obtain ⟨rfl, rfl⟩ := hB; simp
      · rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right (fun h => hA ⟨h.1.symm, h.2.symm⟩),
          ite_eq_right (fun h => hB ⟨h.1.symm, h.2.symm⟩)]
        ring
  · subst h0
    apply hecke_ext_cartan
    intro c d hcd
    rw [heckeT_mul_heckeBasis_apply hab hcd, heckeBasis_apply_cartan (show a ≤ a + 1 by omega) hcd]
    by_cases hA : c = a + 1 ∧ d = a
    · obtain ⟨rfl, rfl⟩ := hA; simp
    · rw [ite_eq_right hA, ite_eq_right (fun h => by omega), ite_eq_right (fun h => hA ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)]

/-! ### Item 5: the central shift -/

theorem cartanElement_add (a b c d : ℤ) :
    cartanElement F (a + c) (b + d) = cartanElement F a b * cartanElement F c d := by
  apply Units.ext
  rw [Units.val_mul, cartanElement_val, cartanElement_val, cartanElement_val, Matrix.mul_fin_two,
    zpow_add₀ (unif_ne_zero F), zpow_add₀ (unif_ne_zero F)]
  simp

theorem cartanElement_zero_eq_one : cartanElement F 0 0 = 1 := by
  apply Units.ext
  rw [cartanElement_val, Units.val_one, Matrix.one_fin_two]
  simp

/-- `K t_{a,a} K = t_{a,a} K` (`t_{a,a}` is central). -/
theorem mem_doubleCoset_diag_iff (a : ℤ) (x : GL (Fin 2) F) :
    x ∈ DoubleCoset.doubleCoset (cartanElement F a a) 𝐊[F] 𝐊[F] ↔
      (x : GL (Fin 2) F ⧸ 𝐊[F]) = (cartanElement F a a : GL (Fin 2) F ⧸ 𝐊[F]) := by
  rw [DoubleCoset.mem_doubleCoset, eq_comm, QuotientGroup.eq]
  constructor
  · rintro ⟨k, hk, k', hk', rfl⟩
    rw [← cartanElement_comm a k, show (cartanElement F a a)⁻¹ * (cartanElement F a a * k * k') = k * k' by group]
    exact mul_mem hk hk'
  · intro h
    exact ⟨1, one_mem _, _, h, by group⟩

theorem mem_doubleCoset_shift (d a b : ℤ) (x : GL (Fin 2) F) :
    x ∈ DoubleCoset.doubleCoset (cartanElement F (a + d) (b + d)) 𝐊[F] 𝐊[F] ↔
      (cartanElement F d d)⁻¹ * x ∈ DoubleCoset.doubleCoset (cartanElement F a b) 𝐊[F] 𝐊[F] := by
  rw [show cartanElement F (a + d) (b + d) = cartanElement F d d * cartanElement F a b by
    rw [← cartanElement_add, add_comm d a, add_comm d b]]
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k, hk, k', hk', rfl⟩
    refine ⟨k, hk, k', hk', ?_⟩
    rw [← mul_assoc k, ← cartanElement_comm d k]
    group
  · rintro ⟨k, hk, k', hk', h⟩
    refine ⟨k, hk, k', hk', ?_⟩
    rw [← mul_assoc k, ← cartanElement_comm d k]
    calc x = cartanElement F d d * ((cartanElement F d d)⁻¹ * x) := by group
      _ = _ := by rw [h]; group

theorem heckeBasis_diag_mul_apply (d : ℤ) (f : sphericalHeckeAlgebra F) (x : GL (Fin 2) F) :
    ((heckeBasis F d d * f : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ) x =
      (f : GL (Fin 2) F → ℂ) ((cartanElement F d d)⁻¹ * x) := by
  rw [HeckePair.mul_apply, finsum_eq_single _ ((cartanElement F d d : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F])]
  · rw [HeckePair.convTerm_mk, heckeBasis_apply_of_mem (DoubleCoset.mem_doubleCoset_self _ _ _), one_mul]
  · intro c hc
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [HeckePair.convTerm_mk, heckeBasis_apply_of_notMem, zero_mul]
    rwa [mem_doubleCoset_diag_iff]

theorem heckeBasis_diag_mul (d a b : ℤ) :
    heckeBasis F d d * heckeBasis F a b = heckeBasis F (a + d) (b + d) := by
  apply HeckePair.ext
  intro x
  rw [heckeBasis_diag_mul_apply]
  by_cases hx : x ∈ DoubleCoset.doubleCoset (cartanElement F (a + d) (b + d)) 𝐊[F] 𝐊[F]
  · rw [heckeBasis_apply_of_mem hx, heckeBasis_apply_of_mem ((mem_doubleCoset_shift d a b x).mp hx)]
  · rw [heckeBasis_apply_of_notMem hx,
      heckeBasis_apply_of_notMem fun h => hx ((mem_doubleCoset_shift d a b x).mpr h)]

theorem heckeBasis_zero_zero : heckeBasis F 0 0 = 1 := by
  show HeckePair.heckeIndicator ℂ (cartanElement F 0 0) _ = 1
  exact HeckePair.heckeIndicator_of_mem (by rw [cartanElement_zero_eq_one]; exact one_mem _) _

variable (F) in
/-- `R_ϖ ∗ c_{a,b} = c_{a+1,b+1}` and `c_{-1,-1} ∗ c_{a,b} = c_{a-1,b-1}` for all `a, b ∈ ℤ`; in particular `R_ϖ` is a
unit of `H(G, K)` with inverse `c_{-1,-1}`. -/
@[tf_id "I.satake.thm:hecke-central-shift"]
theorem hecke_central_shift :
    (∀ a b : ℤ, heckeBasis F 1 1 * heckeBasis F a b = heckeBasis F (a + 1) (b + 1) ∧
        heckeBasis F (-1) (-1) * heckeBasis F a b = heckeBasis F (a - 1) (b - 1)) ∧
      heckeBasis F 1 1 * heckeBasis F (-1) (-1) = 1 ∧ heckeBasis F (-1) (-1) * heckeBasis F 1 1 = 1 := by
  refine ⟨fun a b => ⟨heckeBasis_diag_mul 1 a b, ?_⟩, ?_, ?_⟩
  · rw [heckeBasis_diag_mul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  · rw [heckeBasis_diag_mul, show (-1 : ℤ) + 1 = 0 by norm_num, heckeBasis_zero_zero]
  · rw [heckeBasis_diag_mul, show (1 : ℤ) + -1 = 0 by norm_num, heckeBasis_zero_zero]

/-! ### Item 6: `H(G, K) = ℂ[T_ϖ, R_ϖ^{±1}]` -/

variable (F) in
/-- `H(G, K)` as a commutative ring (`I.satake.thm:hecke-commutative`), as an instance (B-only plumbing). -/
@[tf_aux "I.satake.def:hecke-comm-ring"]
noncomputable instance sphericalHeckeAlgebra_commRing : CommRing (sphericalHeckeAlgebra F) :=
  { (inferInstance : Ring (sphericalHeckeAlgebra F)) with mul_comm := hecke_commutative F }

section HeckePolynomial

open AddMonoidAlgebra

/-- `R_ϖ` as a unit of `H(G, K)`, with inverse `c_{-1,-1}`. -/
noncomputable def heckeRUnit : (sphericalHeckeAlgebra F)ˣ where
  val := heckeBasis F 1 1
  inv := heckeBasis F (-1) (-1)
  val_inv := (hecke_central_shift F).2.1
  inv_val := (hecke_central_shift F).2.2

theorem heckeRUnit_zpow (m : ℤ) :
    ((heckeRUnit (F := F) ^ m : (sphericalHeckeAlgebra F)ˣ) : sphericalHeckeAlgebra F) = heckeBasis F m m := by
  refine Int.induction_on m ?_ ?_ ?_
  · rw [zpow_zero, Units.val_one, heckeBasis_zero_zero]
  · intro n ih
    rw [zpow_add_one, Units.val_mul, ih, hecke_commutative F]
    exact heckeBasis_diag_mul 1 n n
  · intro n ih
    rw [zpow_sub_one, Units.val_mul, ih, hecke_commutative F]
    show heckeBasis F (-1) (-1) * heckeBasis F (-n) (-n) = heckeBasis F (-n - 1) (-n - 1)
    rw [heckeBasis_diag_mul, ← sub_eq_add_neg]

/-- `Θ : ℂ[T, R^{±1}] → H(G, K)`, `T ↦ T_ϖ`, `R ↦ R_ϖ`. -/
noncomputable def heckeTheta : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] sphericalHeckeAlgebra F :=
  AddMonoidAlgebra.lift ℂ (sphericalHeckeAlgebra F) (ℕ × ℤ)
    { toFun := fun p => heckeBasis F 1 0 ^ p.toAdd.1 *
        ((heckeRUnit ^ p.toAdd.2 : (sphericalHeckeAlgebra F)ˣ) : sphericalHeckeAlgebra F)
      map_one' := by simp
      map_mul' := fun p p' => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_add, zpow_add, Units.val_mul]
        ring }

theorem heckeTheta_single (n : ℕ) (m : ℤ) :
    heckeTheta (F := F) (single (n, m) 1) = heckeBasis F 1 0 ^ n * heckeBasis F m m := by
  rw [heckeTheta, lift_single, one_smul]
  show heckeBasis F 1 0 ^ n * ((heckeRUnit ^ m : (sphericalHeckeAlgebra F)ˣ) : sphericalHeckeAlgebra F) = _
  rw [heckeRUnit_zpow]

/-- The span of the `c_{n+m-l, m+l}`, `1 ≤ l ≤ n/2` (lower terms of `T_ϖ^n R_ϖ^m`). -/
noncomputable def heckeW (n : ℕ) (m : ℤ) : Submodule ℂ (sphericalHeckeAlgebra F) :=
  Submodule.span ℂ {f | ∃ l : ℤ, 1 ≤ l ∧ 2 * l ≤ n ∧ f = heckeBasis F (n + m - l) (m + l)}

theorem heckeT_mul_heckeBasis_lead (a b : ℤ) (hab : b ≤ a) :
    ∃ r : ℂ, heckeBasis F 1 0 * heckeBasis F a b = heckeBasis F (a + 1) b + r • heckeBasis F a (b + 1) ∧
      (a = b → r = 0) := by
  obtain ⟨h2, h1, h0⟩ := hecke_recursion F a b hab
  rcases lt_trichotomy (a - b) 1 with h | h | h
  · obtain rfl : a = b := by omega
    exact ⟨0, by rw [h0 rfl, zero_smul, add_zero], fun _ => rfl⟩
  · refine ⟨(q F : ℂ) + 1, ?_, fun h' => by omega⟩
    rw [h1 h, show a = b + 1 by omega]
  · exact ⟨q F, h2 (by omega), fun h' => by omega⟩

theorem heckeT_mul_mem_heckeW {n : ℕ} {m : ℤ} {w : sphericalHeckeAlgebra F} (hw : w ∈ heckeW n m) :
    heckeBasis F 1 0 * w ∈ heckeW (n + 1) m := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl1, hl2, rfl⟩ := hx
    obtain ⟨r, hr, hr0⟩ := heckeT_mul_heckeBasis_lead (F := F) (n + m - l) (m + l) (by omega)
    rw [hr]
    refine add_mem (Submodule.subset_span ⟨l, hl1, by push_cast; omega,
      congrArg₂ _ (by push_cast; ring) rfl⟩) ?_
    by_cases hlast : 2 * (l + 1) ≤ (n : ℤ) + 1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l + 1, by omega, by push_cast; omega,
        congrArg₂ _ (by push_cast; ring) (by ring)⟩)
    · rw [hr0 (by omega), zero_smul]
      exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem heckeT_pow_mul_diag (n : ℕ) (m : ℤ) :
    heckeBasis F 1 0 ^ n * heckeBasis F m m - heckeBasis F (n + m) m ∈ heckeW n m := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨r, hr, hr0⟩ := heckeT_mul_heckeBasis_lead (F := F) (n + m) m (by omega)
    have hsplit : heckeBasis F 1 0 ^ (n + 1) * heckeBasis F m m - heckeBasis F ((n + 1 : ℕ) + m) m =
        r • heckeBasis F (n + m) (m + 1) +
          heckeBasis F 1 0 * (heckeBasis F 1 0 ^ n * heckeBasis F m m - heckeBasis F (n + m) m) := by
      rw [show ((n + 1 : ℕ) : ℤ) + m = (n + m) + 1 by push_cast; ring, mul_sub, ← mul_assoc, ← pow_succ', hr]
      abel
    rw [hsplit]
    refine add_mem ?_ (heckeT_mul_mem_heckeW ih)
    by_cases hn : 1 ≤ n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, le_rfl, by push_cast; omega,
        congrArg₂ _ (by push_cast; ring) rfl⟩)
    · rw [hr0 (by omega), zero_smul]
      exact zero_mem _

theorem heckeW_apply_eq_zero {n : ℕ} {m : ℤ} {w : sphericalHeckeAlgebra F} (hw : w ∈ heckeW n m)
    {n₀ : ℕ} (hn : n ≤ n₀) (m₀ : ℤ) :
    (w : GL (Fin 2) F → ℂ) (cartanElement F (n₀ + m₀) m₀) = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl1, hl2, rfl⟩ := hx
    rw [heckeBasis_apply_cartan (by omega) (by omega), ite_eq_right]
    simp only [Prod.mk.injEq]
    omega
  | zero => rfl
  | add x y _ _ hx hy => rw [HeckePair.coe_apply_add, hx, hy, add_zero]
  | smul a x _ hx => rw [HeckePair.coe_apply_smul, hx, mul_zero]

theorem heckeTheta_single_apply (n : ℕ) (m : ℤ) {n₀ : ℕ} (hn : n ≤ n₀) (m₀ : ℤ) :
    ((heckeTheta (F := F) (single (n, m) 1) : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ)
      (cartanElement F (n₀ + m₀) m₀) = if n = n₀ ∧ m = m₀ then 1 else 0 := by
  rw [heckeTheta_single, ← sub_add_cancel (heckeBasis F 1 0 ^ n * heckeBasis F m m) (heckeBasis F (n + m) m),
    HeckePair.coe_apply_add, heckeW_apply_eq_zero (heckeT_pow_mul_diag n m) hn m₀, zero_add,
    heckeBasis_apply_cartan (by omega) (by omega)]
  simp only [Prod.mk.injEq]
  by_cases h : n = n₀ ∧ m = m₀
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem heckeTheta_injective : Function.Injective (heckeTheta (F := F)) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  have hsupp : P.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hne (coeff_injective (by rw [h, coeff_zero]))
  obtain ⟨p₀, hp₀, hmax⟩ := P.coeff.support.exists_max_image (fun p => p.1) hsupp
  have key : ((heckeTheta P : sphericalHeckeAlgebra F) : GL (Fin 2) F → ℂ)
      (cartanElement F (p₀.1 + p₀.2) p₀.2) = P.coeff p₀ := by
    conv_lhs => rw [← sum_coeff_single P]
    rw [Finsupp.sum, map_sum, ← heckeEval_apply, map_sum]
    rw [Finset.sum_eq_single p₀]
    · rw [heckeEval_apply, show single p₀ (P.coeff p₀) = P.coeff p₀ • single p₀ (1 : ℂ) by
        rw [smul_single, smul_eq_mul, mul_one], map_smul, HeckePair.coe_apply_smul,
        heckeTheta_single_apply _ _ le_rfl, ite_eq_left ⟨rfl, rfl⟩, mul_one]
    · intro p hp hne'
      rw [heckeEval_apply, show single p (P.coeff p) = P.coeff p • single p (1 : ℂ) by
        rw [smul_single, smul_eq_mul, mul_one], map_smul, HeckePair.coe_apply_smul,
        heckeTheta_single_apply _ _ (hmax p hp), ite_eq_right, mul_zero]
      exact fun h => hne' (Prod.ext h.1 h.2)
    · intro h; exact absurd hp₀ h
  rw [hP] at key
  exact (Finsupp.mem_support_iff.mp hp₀) key.symm

theorem heckeTheta_surjective : Function.Surjective (heckeTheta (F := F)) := by
  have hbasis : ∀ k : ℕ, ∀ b : ℤ, heckeBasis F (k + b) b ∈ (heckeTheta (F := F)).range := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro b
      have hW : heckeW (F := F) k b ≤ Subalgebra.toSubmodule (heckeTheta (F := F)).range := by
        rw [heckeW, Submodule.span_le]
        rintro _ ⟨l, hl1, hl2, rfl⟩
        have := ih (k - 2 * l).toNat (by omega) (b + l)
        rw [show ((k - 2 * l).toNat : ℤ) + (b + l) = k + b - l by omega] at this
        exact this
      have h := heckeT_pow_mul_diag (F := F) k b
      have hmem : heckeBasis F 1 0 ^ k * heckeBasis F b b ∈ (heckeTheta (F := F)).range :=
        ⟨single (k, b) 1, heckeTheta_single k b⟩
      have := Subalgebra.sub_mem _ hmem (hW h)
      rwa [sub_sub_cancel] at this
  intro f
  obtain ⟨-, hexp⟩ := hecke_basis_basis F
  obtain ⟨hfin, hf⟩ := hexp f
  have hmem : f ∈ (heckeTheta (F := F)).range := by
    rw [hf]
    refine finsum_induction (· ∈ (heckeTheta (F := F)).range) (zero_mem _) (fun _ _ => add_mem)
      fun p => Subalgebra.smul_mem _ ?_ _
    have := hbasis (p.1.1 - p.1.2).toNat p.1.2
    rwa [show ((p.1.1 - p.1.2).toNat : ℤ) + p.1.2 = p.1.1 by have := p.2; omega] at this
  exact hmem

/-- `ℂ[T, R^{±1}]` is generated by `T`, `R`, `R^{-1}`. -/
theorem adjoin_polyTR :
    Algebra.adjoin ℂ {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
      single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} = ⊤ := by
  suffices h : ∀ P, P ∈ Algebra.adjoin ℂ {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
      single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} from
    eq_top_iff.mpr fun P _ => h P
  intro P
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single nm c =>
    obtain ⟨n, m⟩ := nm
    have hT : (single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) ∈ Algebra.adjoin ℂ
        {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
          single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} :=
      Algebra.subset_adjoin (by simp)
    have hR : (single ((0 : ℕ), (1 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) ∈ Algebra.adjoin ℂ
        {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
          single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} :=
      Algebra.subset_adjoin (by simp)
    have hR' : (single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) ∈ Algebra.adjoin ℂ
        {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
          single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} :=
      Algebra.subset_adjoin (by simp)
    have hdecomp : (single (n, m) c : AddMonoidAlgebra ℂ (ℕ × ℤ)) =
        c • ((single ((1 : ℕ), (0 : ℤ)) (1 : ℂ)) ^ n * single ((0 : ℕ), m) (1 : ℂ)) := by
      rw [single_pow, single_mul_single, smul_single]
      simp only [one_pow, mul_one, smul_eq_mul]
      congr 1; ext <;> simp
    rw [hdecomp]
    refine Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hT n) ?_) c
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · have : (single ((0 : ℕ), (k : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) =
          (single ((0 : ℕ), (1 : ℤ)) (1 : ℂ)) ^ k := by
        rw [single_pow]; simp only [one_pow]; congr 1; ext <;> simp
      rw [this]; exact Subalgebra.pow_mem _ hR k
    · have : (single ((0 : ℕ), -(k : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) =
          (single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)) ^ k := by
        rw [single_pow]; simp only [one_pow]; congr 1; ext <;> simp
      rw [this]; exact Subalgebra.pow_mem _ hR' k

/-- The exponent map `(Fin 2 →₀ ℕ) → ℕ × ℤ`. -/
noncomputable def polyTRExpMap : (Fin 2 →₀ ℕ) →+ ℕ × ℤ :=
  (Finsupp.applyAddHom 0).prod ((Nat.castAddMonoidHom ℤ).comp (Finsupp.applyAddHom 1))

theorem polyTRExpMap_injective : Function.Injective polyTRExpMap := by
  intro d d' h
  simp only [polyTRExpMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.applyAddHom_apply, Nat.coe_castAddMonoidHom, Prod.mk.injEq, Nat.cast_inj] at h
  ext i; fin_cases i <;> simp [h.1, h.2]

/-- `ψ : ℂ[x₀, x₁] → ℂ[T, R^{±1}]`, `x₀ ↦ T`, `x₁ ↦ R` (injective). -/
noncomputable def polyTRIota : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ polyTRExpMap

theorem polyTRIota_injective : Function.Injective polyTRIota :=
  AddMonoidAlgebra.mapDomain_injective polyTRExpMap_injective

theorem polyTRIota_X (i : Fin 2) :
    polyTRIota (MvPolynomial.X i) = ![(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
      single ((0 : ℕ), (1 : ℤ)) (1 : ℂ)] i := by
  fin_cases i <;> simp [polyTRIota, MvPolynomial.X, MvPolynomial.monomial, polyTRExpMap]

variable (F) in
/-- The `ℂ`-algebra map `Θ : ℂ[T, R^{±1}] → H(G, K)`, `T ↦ T_ϖ`, `R ↦ R_ϖ`, exists and is an isomorphism
(`ℂ[T, R^{±1}] = ℂ[ℕ × ℤ]`, `T = X^{(1,0)}`, `R = X^{(0,1)}`); in particular `H(G, K)` is generated by `T_ϖ`, `R_ϖ`,
`R_ϖ^{-1} = c_{-1,-1}`, and `T_ϖ`, `R_ϖ` are algebraically independent over `ℂ`. -/
@[tf_id "I.satake.thm:hecke-polynomial"]
theorem hecke_polynomial :
    (∃ Θ : AddMonoidAlgebra ℂ (ℕ × ℤ) ≃ₐ[ℂ] sphericalHeckeAlgebra F,
        Θ (AddMonoidAlgebra.single (1, 0) 1) = heckeBasis F 1 0 ∧
          Θ (AddMonoidAlgebra.single (0, 1) 1) = heckeBasis F 1 1) ∧
      Algebra.adjoin ℂ {heckeBasis F 1 0, heckeBasis F 1 1, heckeBasis F (-1) (-1)} = ⊤ ∧
      AlgebraicIndependent ℂ ![heckeBasis F 1 0, heckeBasis F 1 1] := by
  have hT : heckeTheta (F := F) (single (1, 0) 1) = heckeBasis F 1 0 := by
    rw [heckeTheta_single, pow_one, heckeBasis_zero_zero, mul_one]
  have hR : heckeTheta (F := F) (single (0, 1) 1) = heckeBasis F 1 1 := by
    rw [heckeTheta_single, pow_zero, one_mul]
  have hR' : heckeTheta (F := F) (single (0, -1) 1) = heckeBasis F (-1) (-1) := by
    rw [heckeTheta_single, pow_zero, one_mul]
  refine ⟨⟨AlgEquiv.ofBijective _ ⟨heckeTheta_injective, heckeTheta_surjective⟩, hT, hR⟩, ?_, ?_⟩
  · have himg : (heckeTheta (F := F)) '' {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
        single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} =
        {heckeBasis F 1 0, heckeBasis F 1 1, heckeBasis F (-1) (-1)} := by
      simp only [Set.image_insert_eq, Set.image_singleton, hT, hR, hR']
    rw [← himg, ← AlgHom.map_adjoin, adjoin_polyTR, Algebra.map_top, AlgHom.range_eq_top]
    exact heckeTheta_surjective
  · rw [AlgebraicIndependent]
    have : MvPolynomial.aeval ![heckeBasis F 1 0, heckeBasis F 1 1] = (heckeTheta (F := F)).comp polyTRIota := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, polyTRIota_X]
      fin_cases i
      · exact hT.symm
      · exact hR.symm
    rw [this]
    exact heckeTheta_injective.comp polyTRIota_injective

end HeckePolynomial

/-! ### Item 7: comparison with the Haar convolution -/

omit [IsNALF F] in
theorem totallyDisconnectedSpace_gl2_of {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [TotallyDisconnectedSpace R] : TotallyDisconnectedSpace (GL (Fin 2) R) := by
  have : TotallyDisconnectedSpace (Matrix (Fin 2) (Fin 2) R) :=
    (inferInstance : TotallyDisconnectedSpace (Fin 2 → Fin 2 → R))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

variable (F) in
/-- `GL₂(F)` is totally disconnected, as an instance (B-only; needed to form `C_c^∞(GL₂(F))`). -/
@[tf_aux "I.satake.lem:gl2-local-totally-disconnected"]
instance gl2_local_totallyDisconnectedSpace : TotallyDisconnectedSpace (GL (Fin 2) F) := by
  have : NonarchimedeanRing F := by
    convert! (ValuativeRel.nonarchimedeanRing F)
    exact Valuation.toTopologicalSpace_eq _
  have : TotallyDisconnectedSpace F := inferInstance
  exact totallyDisconnectedSpace_gl2_of

/-! ### Item 8: `T_ϖ²` -/

variable (F) in
/-- `T_ϖ ∗ T_ϖ = c_{2,0} + (q + 1) R_ϖ`. -/
@[tf_id "I.satake.ex:hecke-t-squared"]
theorem hecke_t_squared :
    heckeBasis F 1 0 * heckeBasis F 1 0 = heckeBasis F 2 0 + ((q F : ℂ) + 1) • heckeBasis F 1 1 := by
  have := (hecke_recursion F 1 0 (by norm_num)).2.1 (by norm_num)
  simpa using this

end GL2TF.Local
