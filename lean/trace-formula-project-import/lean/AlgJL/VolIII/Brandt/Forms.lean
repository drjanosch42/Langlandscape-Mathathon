import AlgJL.Meta.Tag
import AlgJL.Common.HeckeModule
import AlgJL.VolIII.Brandt.Coefficients
import AlgJL.VolIII.P2.ClassSet

/-!
# Quaternionic forms `M_k(O; s)` (Q3 U2, items 11–14)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §2 (items 11–14 of `docs/sprints/Q3-plan.md` §1.2).

Design (plan §1.1 item 2, conventions row N20, Δ4):
* `M_k(O; s) := {f : B̂^× → V_{k−2}(K) : f(ι(γ) x u) = ρ_k^s(γ) f(x)}` is the generic `equivariantFunctions` of
  `GL2TF.Common.HeckeModule` for `ι = Units.map finEmbed` (`B^×` on the left) and `U = Ô^×` (on the right);
* a family of class representatives is a map `r : X(O) → B̂^×` with `[r c] = c` (`classOf`); the invariants
  `V^{ρ(Γ)}` are written inline as `⨅ γ ∈ Γ, ker(ρ(γ) − 1)`;
* `|Γ|` is `Nat.card` (junk `0` for an infinite group, Q2 trap 5): `a < 0`, `b < 0` are binders wherever it occurs.

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF.HeckeModule

/-- The class `[x] ∈ X(O)` of `x ∈ B̂^×` (B-only plumbing: Mathlib's `DoubleCoset.mk`). -/
@[tf_aux "III.qform.def:class-of"]
noncomputable def classOf {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) : classSet O :=
  DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x

/-- Quaternionic forms of weight `k` on `O` with coefficients in `V_{k−2}(K)` through the splitting `s`:
`M_k(O; s) = {f : B̂^× → V_{k−2}(K) : f(ι(γ) x u) = ρ_k^s(γ) f(x) for γ ∈ B^×, x ∈ B̂^×, u ∈ Ô^×}`, a `K`-subspace. -/
@[tf_id "III.qform.def:quaternionic-forms"]
noncomputable def quatForms {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (k : ℕ) : Submodule K ((BHat a b)ˣ → symPowerModule K (k - 2)) :=
  equivariantFunctions K (Units.map (finEmbed a b).toMonoidHom) (orderCompletionUnits O)
    (fun γ => splitRep s k (γ : QuatAlg ℚ a b))

theorem splitRep_mul {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b) (k : ℕ)
    (γ δ : QuatAlg ℚ a b) : splitRep s k (γ * δ) = splitRep s k γ * splitRep s k δ := by
  rw [splitRep, map_mul, (symPower_basic K (k - 2)).2.2.1]
  rfl

theorem splitRep_one {K : Type*} [Field K] [CharZero K] {a b : ℤ} (s : Splitting K a b) (k : ℕ) :
    splitRep s k 1 = 1 := by
  rw [splitRep, map_one, (symPower_basic K (k - 2)).2.2.2.1]

theorem classOf_mul {a b : ℤ} (O : QOrder a b) (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ)
    (hu : u ∈ orderCompletionUnits O) :
    classOf O (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf O x := by
  refine DoubleCoset.eq.mpr ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, ?_, u⁻¹, inv_mem hu, by group⟩
  exact inv_mem ⟨γ, rfl⟩

/-- For every family of class representatives `(x_c)_{c ∈ X(O)}`, `f ↦ (f(x_c))_c` is a `K`-linear isomorphism
`M_k(O; s) ≃ Π_c V_{k−2}(K)^{ρ(Γ_{x_c})}`. -/
@[tf_id "III.qform.thm:forms-class-decomposition"]
theorem forms_class_decomposition {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b)
    (s : Splitting K a b) (k : ℕ) (r : classSet O → (BHat a b)ˣ) (hr : ∀ c, classOf O (r c) = c) :
    ∃ e : quatForms O s k ≃ₗ[K] ((c : classSet O) →
        ↥(⨅ γ : classStabilizer (orderCompletionUnits O) (r c),
          LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1))),
      ∀ (f : quatForms O s k) (c : classSet O),
        ((e f c : symPowerModule K (k - 2))) = (f : (BHat a b)ˣ → symPowerModule K (k - 2)) (r c) := by
  classical
  set ι := Units.map (finEmbed a b).toMonoidHom with hι
  set U := orderCompletionUnits O with hU
  set W : classSet O → Submodule K (symPowerModule K (k - 2)) := fun c =>
    ⨅ γ : classStabilizer (orderCompletionUnits O) (r c),
      LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1) with hW
  have hinv : ∀ f ∈ quatForms O s k, ∀ x u, u ∈ U → f (x * u) = f x := by
    intro f hf x u hu
    have h := hf 1 x u hu
    simp only [map_one, one_mul, Units.val_one, splitRep_one, Module.End.one_apply] at h
    exact h
  have hleft : ∀ f ∈ quatForms O s k, ∀ γ x, f (ι γ * x) = splitRep s k (γ : QuatAlg ℚ a b) (f x) := by
    intro f hf γ x
    have h := hf γ x 1 (one_mem _)
    rwa [mul_one] at h
  have hstab : ∀ (x : (BHat a b)ˣ) (γ : (QuatAlg ℚ a b)ˣ), γ ∈ classStabilizer U x →
      ∃ u ∈ U, ι γ = x * u * x⁻¹ := by
    intro x γ hγ
    obtain ⟨u, hu, h⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hγ)
    exact ⟨u, hu, by rw [← h]; rfl⟩
  have hstab' : ∀ x γ u, u ∈ U → ι γ = x * u * x⁻¹ → γ ∈ classStabilizer U x := by
    intro x γ u hu h
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨u, hu, by rw [h]; rfl⟩)
  have memW : ∀ (c : classSet O) (v : symPowerModule K (k - 2)),
      v ∈ W c ↔ ∀ γ ∈ classStabilizer U (r c), splitRep s k (γ : QuatAlg ℚ a b) v = v := by
    intro c v
    simp only [hW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      Subtype.forall]
    rfl
  have hfwd : ∀ f ∈ quatForms O s k, ∀ c, f (r c) ∈ W c := by
    intro f hf c
    rw [memW]
    intro γ hγ
    obtain ⟨u, hu, h⟩ := hstab _ γ hγ
    rw [← hleft f hf, h, inv_mul_cancel_right, hinv f hf _ u hu]
  have hdec : ∀ y : (BHat a b)ˣ, ∃ γ : (QuatAlg ℚ a b)ˣ, ∃ u ∈ U, y = ι γ * r (classOf O y) * u := by
    intro y
    have h : classOf O (r (classOf O y)) = classOf O y := hr _
    obtain ⟨h', hh', u, hu, hy⟩ := DoubleCoset.eq.mp h
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hh'
    rw [← hγ] at hy
    exact ⟨γ, u, hu, hy⟩
  have hwd : ∀ (g : (c : classSet O) → W c) (c : classSet O) (γ γ' : (QuatAlg ℚ a b)ˣ) (u u' : (BHat a b)ˣ),
      u ∈ U → u' ∈ U → ι γ * r c * u = ι γ' * r c * u' →
      splitRep s k (γ : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2)) =
        splitRep s k (γ' : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2)) := by
    intro g c γ γ' u u' hu hu' h
    have hδ : γ'⁻¹ * γ ∈ classStabilizer U (r c) := by
      refine hstab' (r c) _ (u' * u⁻¹) (mul_mem hu' (inv_mem hu)) ?_
      rw [map_mul, map_inv]
      calc (ι γ')⁻¹ * ι γ = (ι γ')⁻¹ * (ι γ * r c * u) * u⁻¹ * (r c)⁻¹ := by group
        _ = (ι γ')⁻¹ * (ι γ' * r c * u') * u⁻¹ * (r c)⁻¹ := by rw [h]
        _ = r c * (u' * u⁻¹) * (r c)⁻¹ := by group
    have hfix := (memW c (g c)).mp (g c).2 _ hδ
    calc splitRep s k (γ : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2))
        = splitRep s k ((γ' * (γ'⁻¹ * γ) : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2)) := by
          rw [mul_inv_cancel_left]
      _ = splitRep s k (γ' : QuatAlg ℚ a b)
            (splitRep s k ((γ'⁻¹ * γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2))) := by
          rw [Units.val_mul, splitRep_mul, Module.End.mul_apply]
      _ = splitRep s k (γ' : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2)) := by rw [hfix]
  let F : ((c : classSet O) → W c) → (BHat a b)ˣ → symPowerModule K (k - 2) :=
    fun g y => splitRep s k ((Classical.choose (hdec y) : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)
      (g (classOf O y) : symPowerModule K (k - 2))
  have hF : ∀ (g : (c : classSet O) → W c) (y : (BHat a b)ˣ) (c : classSet O) (γ : (QuatAlg ℚ a b)ˣ)
      (u : (BHat a b)ˣ), u ∈ U → y = ι γ * r c * u →
      F g y = splitRep s k (γ : QuatAlg ℚ a b) (g c : symPowerModule K (k - 2)) := by
    intro g y c γ u hu hy
    have hc : classOf O y = c := by rw [hy, classOf_mul O γ (r c) u hu]; exact hr c
    subst hc
    obtain ⟨u₀, hu₀, h₀⟩ := Classical.choose_spec (hdec y)
    exact hwd g _ _ _ _ _ hu₀ hu (h₀.symm.trans hy)
  have hFmem : ∀ g : (c : classSet O) → W c, F g ∈ quatForms O s k := by
    intro g γ x u hu
    obtain ⟨u₀, hu₀, h₀⟩ := Classical.choose_spec (hdec x)
    set γ₀ := Classical.choose (hdec x) with hγ₀
    have hy : ι γ * x * u = ι (γ * γ₀) * r (classOf O x) * (u₀ * u) := by
      conv_lhs => rw [h₀]
      rw [map_mul]
      group
    rw [hF g _ _ _ _ (mul_mem hu₀ hu) hy, Units.val_mul, splitRep_mul, Module.End.mul_apply]
  refine ⟨{ toFun := fun f c => ⟨(f : (BHat a b)ˣ → symPowerModule K (k - 2)) (r c), hfwd f f.2 c⟩
            map_add' := fun f g => by funext c; apply Subtype.ext; rfl
            map_smul' := fun t f => by funext c; apply Subtype.ext; rfl
            invFun := fun g => ⟨F g, hFmem g⟩
            left_inv := fun f => ?_
            right_inv := fun g => ?_ }, fun f c => rfl⟩
  · apply Subtype.ext
    funext y
    obtain ⟨u₀, hu₀, h₀⟩ := Classical.choose_spec (hdec y)
    show splitRep s k ((Classical.choose (hdec y) : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)
      ((f : (BHat a b)ˣ → symPowerModule K (k - 2)) (r (classOf O y))) = (f : (BHat a b)ˣ → _) y
    rw [← f.2 _ _ u₀ hu₀, ← h₀]
  · funext c
    apply Subtype.ext
    show F g (r c) = (g c : symPowerModule K (k - 2))
    rw [hF g (r c) c 1 1 (one_mem _) (by simp), Units.val_one, splitRep_one, Module.End.one_apply]

theorem symPowerAction_of_eq_zero {K : Type*} [Field K] (m : ℕ) (hm : m = 0) (A : Matrix (Fin 2) (Fin 2) K) :
    symPowerAction K m A = 1 := by
  subst hm
  obtain ⟨e, he⟩ := (symPower_basic K 0).1
  refine e.ext fun t => Subtype.ext ?_
  show MvPolynomial.aeval (linSubst A) (e t : MvPolynomial (Fin 2) K) = (e t : MvPolynomial (Fin 2) K)
  obtain rfl : t = 0 := Fin.ext (Nat.lt_one_iff.mp t.2)
  rw [he]
  simp

/-- For `a, b < 0`: `M_k(O; s)` is finite-dimensional; for a finite subgroup `Γ ≤ B^×` of elements of reduced norm `1`
and `k ≥ 2`, `|Γ| · dim V_{k−2}(K)^{ρ(Γ)} = Σ_{γ ∈ Γ} P_k(trd γ, 1)`; and `dim M_2(O; s) = |X(O)|`. -/
@[tf_id "III.qform.cor:forms-dimension"]
theorem forms_dimension {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (s : Splitting K a b) :
    (∀ k : ℕ, FiniteDimensional K (quatForms O s k)) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ Γ : Subgroup (QuatAlg ℚ a b)ˣ, Finite Γ →
      (∀ γ ∈ Γ, nrd (γ : QuatAlg ℚ a b) = 1) →
      (Nat.card Γ : K) * (Module.finrank K
          ↥(⨅ γ : Γ, LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1)) : K) =
        ∑ᶠ γ : Γ, heckePolyRing k (((trd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) : ℚ) : K)) 1) ∧
    Module.finrank K (quatForms O s 2) = Nat.card (classSet O) := by
  classical
  have := classSet_finite ha hb O
  haveI : Fintype (classSet O) := Fintype.ofFinite _
  have hr : ∀ c : classSet O, classOf O (Quotient.out c) = c := fun c => DoubleCoset.out_eq' c
  refine ⟨fun k => ?_, fun k hk Γ hΓfin hΓ1 => ?_, ?_⟩
  · obtain ⟨e, -⟩ := forms_class_decomposition O s k (fun c => Quotient.out c) hr
    obtain ⟨bas, -⟩ := (symPower_basic K (k - 2)).1
    haveI : FiniteDimensional K (symPowerModule K (k - 2)) := Module.Finite.of_basis bas
    exact Module.Finite.equiv e.symm
  · haveI : Fintype Γ := Fintype.ofFinite _
    obtain ⟨bas, -⟩ := (symPower_basic K (k - 2)).1
    haveI : FiniteDimensional K (symPowerModule K (k - 2)) := Module.Finite.of_basis bas
    have hcard : (Nat.card Γ : K) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hρmul : ∀ x y : Γ, splitRep s k (((x * y : Γ) : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) =
        splitRep s k ((x : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) * splitRep s k ((y : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
      intro x y
      rw [Subgroup.coe_mul, Units.val_mul, splitRep_mul]
    have memW : ∀ v : symPowerModule K (k - 2),
        v ∈ (⨅ γ : Γ, LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1)) ↔
          ∀ γ : Γ, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v = v := by
      intro v
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    let π : Module.End K (symPowerModule K (k - 2)) :=
      (Nat.card Γ : K)⁻¹ • ∑ γ : Γ, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)
    have hπ : ∀ v, π v = (Nat.card Γ : K)⁻¹ • ∑ γ : Γ, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v := by
      intro v
      simp only [π, LinearMap.smul_apply, LinearMap.sum_apply]
    have hproj : LinearMap.IsProj
        (⨅ γ : Γ, LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1)) π := by
      constructor
      · intro v
        rw [memW]
        intro δ
        have hs : ∑ γ : Γ, splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)
            (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v) =
            ∑ γ : Γ, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v :=
          Fintype.sum_equiv (Equiv.mulLeft δ) _ _ fun γ => by
            rw [Equiv.coe_mulLeft, hρmul, Module.End.mul_apply]
        rw [hπ, map_smul, map_sum, hs]
      · intro v hv
        rw [memW] at hv
        rw [hπ]
        simp only [hv, Finset.sum_const, Finset.card_univ]
        rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    have hn := splitting_norm_trace ha.ne hb.ne s
    have htr : ∀ γ : Γ, LinearMap.trace K _ (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) =
        heckePolyRing k (((trd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) : ℚ) : K)) 1 := by
      intro γ
      have h1 := (symPower_trace K).1 (k - 2) (s ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b))
      rw [hn.2.1, hn.1, hΓ1 _ γ.2, Rat.cast_one, Nat.sub_add_cancel hk] at h1
      exact h1
    haveI : ∀ p : Submodule K (symPowerModule K (k - 2)), Module.Free K p :=
      fun p => Module.Free.of_divisionRing K p
    have htrπ := hproj.trace
    rw [show π = (Nat.card Γ : K)⁻¹ • ∑ γ : Γ, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) from rfl,
      map_smul, map_sum, smul_eq_mul] at htrπ
    rw [← htrπ, finsum_eq_sum_of_fintype, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    exact Finset.sum_congr rfl fun γ _ => htr γ
  · obtain ⟨e, -⟩ := forms_class_decomposition O s 2 (fun c => Quotient.out c) hr
    obtain ⟨bas, -⟩ := (symPower_basic K (2 - 2)).1
    haveI : FiniteDimensional K (symPowerModule K (2 - 2)) := Module.Finite.of_basis bas
    have h1 : Module.finrank K (symPowerModule K (2 - 2)) = 1 := (symPower_basic K (2 - 2)).2.1
    haveI : ∀ p : Submodule K (symPowerModule K (2 - 2)), Module.Free K p :=
      fun p => Module.Free.of_divisionRing K p
    have hW : ∀ x : (BHat a b)ˣ, (⨅ γ : classStabilizer (orderCompletionUnits O) x,
        LinearMap.ker (splitRep s 2 ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1)) = ⊤ := by
      intro x
      refine eq_top_iff.mpr fun v _ => ?_
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, splitRep,
        symPowerAction_of_eq_zero (2 - 2) rfl, Module.End.one_apply, sub_self, implies_true]
    rw [e.finrank_eq, Module.finrank_pi_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ,
      Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hW, finrank_top, h1]

/-- For `k = 2` (`V_0(K) = K`): the constant form `1 ∈ M_2(O; s)`, `x ↦ 1`. -/
@[tf_id "III.qform.def:constant-form"]
noncomputable def constantForm {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b) :
    quatForms O s 2 :=
  ⟨fun _ => ⟨1, MvPolynomial.isHomogeneous_one _ _⟩, by
    intro γ x u _
    apply Subtype.ext
    simp [splitRep, symPowerAction, LinearMap.restrict_apply]⟩

end GL2TF.Quat
