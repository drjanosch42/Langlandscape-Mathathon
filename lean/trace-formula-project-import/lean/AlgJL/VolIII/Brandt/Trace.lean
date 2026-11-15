import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.Pairing

/-!
# The fixed-point trace formula for `T_n` (Q3 U3, item 34)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §3, end (item 34 of `docs/sprints/Q3-plan.md` §1.2): the starting point
of Q4 (interface freeze Δ8).

Design: `T_n` is defined on all functions (`III.brandt.def:hecke-operator`); the trace is that of an endomorphism `T` of
`M_k(O; s)` whose underlying map is `T_n` (its existence states that `T_n` preserves `M_k(O; s)` and is `K`-linear there).
The left order `O_x = ι⁻¹(x Ô x⁻¹)` is written inline (as in Q2's `III.qcls.lem:stabilizer-units`).

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-! ### Proof helpers for `hecke_trace_fixed_point` (copies of helpers of Hecke.lean/Brandt.lean, invisible to `lfile`
here; a later cleanup can de-duplicate). -/

private theorem tr_nrd_mul {a b : ℤ} (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from x * y) =
      nrd (show QuatAlg FinAdele a b from x) * nrd (show QuatAlg FinAdele a b from y) :=
  (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1 x y

private theorem tr_zhat_unit_inv_mul (w : Zhatˣ) :
    (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((w : Zhat) : FinAdele) = 1 := by
  have := congrArg (fun z : Zhat => (z : FinAdele)) w.inv_mul
  simpa only [Subring.coe_mul, Subring.coe_one] using this

/-- For `a, b < 0` and `n ≥ 1`: `γ ∈ S_{cc}(n)` has `nrd γ = n`, and `{γ ∈ O_{x_c} : nrd γ = n}` is the image of
`S_{cc}(n)` in `B` (proof helper). -/
private theorem tr_set_eq {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (n : ℕ) (hn : 0 < n)
    (c : classSet O) :
    (∀ γ : (QuatAlg ℚ a b)ˣ,
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet O n →
      nrd (γ : QuatAlg ℚ a b) = n) ∧
    {γ : QuatAlg ℚ a b | finEmbed a b γ ∈
        (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
          (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ∧ nrd γ = n} =
      (fun γ : (QuatAlg ℚ a b)ˣ => (γ : QuatAlg ℚ a b)) ''
        {γ : (QuatAlg ℚ a b)ˣ | (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈
          normNSet O n} := by
  -- traces of `ρ(γ)` for `γ ∈ S_{cc}(n)`: `nrd γ = n`
  have hnq : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn1 : (n : FinAdele) * algebraMap ℚ FinAdele ((n : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hnq, map_one]
  have hval : ∀ (c : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b) =
        (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b) * finEmbed a b (γ : QuatAlg ℚ a b) *
          ((Quotient.out c : (BHat a b)ˣ) : BHat a b) := by
    intro c γ
    rw [Units.val_mul, Units.val_mul, Units.coe_map]
    rfl
  have hnrdc : ∀ (c : classSet O) (γ : (QuatAlg ℚ a b)ˣ), nrd (show QuatAlg FinAdele a b from
      (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b)) =
        algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) := by
    intro c γ
    rw [hval, tr_nrd_mul, tr_nrd_mul]
    have h1 := nrd_units_mul_inv (Quotient.out c)
    have h2 : nrd (show QuatAlg FinAdele a b from finEmbed a b (γ : QuatAlg ℚ a b)) =
        algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) :=
      ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) γ).1
    rw [h2]
    linear_combination (algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b))) * h1
  have hfwd : ∀ (c : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet O n →
      nrd (γ : QuatAlg ℚ a b) = n := by
    intro c γ hγ
    obtain ⟨-, w, hw⟩ := hγ
    rw [hnrdc] at hw
    have hγne : (γ : QuatAlg ℚ a b) ≠ 0 := Units.ne_zero γ
    have hd := (nrd_definite ha hb).1 (γ : QuatAlg ℚ a b)
    have hpos : 0 < nrd (γ : QuatAlg ℚ a b) :=
      lt_of_le_of_ne (le_trans (by positivity) hd.1) (Ne.symm (mt hd.2.mp hγne))
    obtain ⟨q, hq⟩ : ∃ q : ℚ, q = nrd (γ : QuatAlg ℚ a b) / n := ⟨_, rfl⟩
    have hqpos : 0 < q := by rw [hq]; exact div_pos hpos (Nat.cast_pos.mpr hn)
    have hqw : algebraMap ℚ FinAdele q = ((w : Zhat) : FinAdele) := by
      rw [hq, div_eq_mul_inv, map_mul, hw]
      linear_combination ((w : Zhat) : FinAdele) * hn1
    have hqiw : algebraMap ℚ FinAdele q⁻¹ = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) := by
      have h1 : algebraMap ℚ FinAdele q⁻¹ * algebraMap ℚ FinAdele q = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hqpos.ne', map_one]
      have h2 := tr_zhat_unit_inv_mul w
      rw [hqw] at h1
      linear_combination (-(algebraMap ℚ FinAdele q⁻¹)) * h2 + (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * h1
    obtain ⟨k₁, hk₁⟩ := rat_isInt_of_mem_zhat q (by rw [hqw]; exact (w : Zhat).2)
    obtain ⟨k₂, hk₂⟩ := rat_isInt_of_mem_zhat q⁻¹ (by rw [hqiw]; exact ((w⁻¹ : Zhatˣ) : Zhat).2)
    have hkk : k₁ * k₂ = 1 := by
      have h3 : ((k₁ * k₂ : ℤ) : ℚ) = 1 := by
        push_cast
        rw [← hk₁, ← hk₂, mul_inv_cancel₀ hqpos.ne']
      exact_mod_cast h3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkk with h4 | h4
    · have hq1 : q = 1 := by rw [hk₁, h4]; norm_num
      rw [hq] at hq1
      exact (div_eq_one_iff_eq hnq).mp hq1
    · exfalso
      rw [hk₁, h4] at hqpos
      norm_num at hqpos
  have hmk : ∀ γ' : QuatAlg ℚ a b, nrd γ' = n → ∃ U' : (QuatAlg ℚ a b)ˣ, (U' : QuatAlg ℚ a b) = γ' := by
    intro γ' hγ'
    have h1 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 γ').1
    have h2 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 γ').2.1
    rw [hγ'] at h1 h2
    refine ⟨⟨γ', ((n : ℕ) : ℚ)⁻¹ • star γ', ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, h1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hnq, map_one]
    · rw [smul_mul_assoc, h2, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hnq, map_one]
  -- the sets: `{γ ∈ O_{x_c} : nrd γ = n}` is the image of `S_{cc}(n)` in `B`
  have hset : ∀ c : classSet O,
      {γ : QuatAlg ℚ a b | finEmbed a b γ ∈
          (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
            (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
            (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ∧ nrd γ = n} =
        (fun γ : (QuatAlg ℚ a b)ˣ => (γ : QuatAlg ℚ a b)) ''
          {γ : (QuatAlg ℚ a b)ˣ | (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈
            normNSet O n} := by
    intro c
    ext γ'
    constructor
    · rintro ⟨⟨y, hy, hye⟩, hn'⟩
      obtain ⟨U', hU'⟩ := hmk γ' hn'
      refine ⟨U', ⟨?_, 1, ?_⟩, hU'⟩
      · rw [hval, hU', ← hye]
        simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
        exact hy
      · rw [hnrdc, hU', hn']
        simp
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨⟨_, hγ.1, ?_⟩, hfwd c γ hγ⟩
      show ((Quotient.out c : (BHat a b)ˣ) : BHat a b) *
          (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b) *
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b) = _
      rw [hval]
      simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  exact ⟨hfwd c, hset c⟩

/-- For `a, b < 0`, every order, `n ≥ 1` and `k ≥ 2`: `T_n` restricts to a `K`-linear endomorphism of `M_k(O; s)` with
`tr(T_n | M_k(O; s)) = Σ_{c ∈ X(O)} |Γ_{x_c}|⁻¹ Σ_{γ ∈ O_{x_c}, nrd γ = n} P_k(trd γ, n)`, `O_x = ι⁻¹(x Ô x⁻¹)` the left
order of `L_x` (representatives `x_c = c.out`). -/
@[tf_id "III.brandt.thm:hecke-trace-fixed-point"]
theorem hecke_trace_fixed_point {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k n : ℕ) (hk : 2 ≤ k) (hn : 0 < n) :
    ∃ T : Module.End K (quatForms O s k),
      (∀ f : quatForms O s k,
        ((T f : quatForms O s k) : (BHat a b)ˣ → symPowerModule K (k - 2)) =
          heckeOperator O n (f : (BHat a b)ˣ → symPowerModule K (k - 2))) ∧
      LinearMap.trace K (quatForms O s k) T =
        ∑ᶠ c : classSet O,
          (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ *
            ∑ᶠ (γ : QuatAlg ℚ a b)
              (_ : finEmbed a b γ ∈
                  (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
                    (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
                    (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ∧
                nrd γ = n),
              heckePolyRing k ((trd γ : ℚ) : K) (n : K) := by
  classical
  have : Finite (classSet O) := classSet_finite ha hb O
  letI := Fintype.ofFinite (classSet O)
  have hr : ∀ c : classSet O, classOf O (Quotient.out c) = c := fun c => DoubleCoset.out_eq' c
  obtain ⟨hS, hMF⟩ := hecke_matrix_formula ha hb O s k n hn Quotient.out hr
  have hρmul : ∀ γ δ : QuatAlg ℚ a b, splitRep s k (γ * δ) = splitRep s k γ * splitRep s k δ := by
    intro γ δ
    rw [splitRep, map_mul, (symPower_basic K (k - 2)).2.2.1]
    rfl
  have hρ1 : splitRep s k (1 : QuatAlg ℚ a b) = 1 := by
    rw [splitRep, map_one, (symPower_basic K (k - 2)).2.2.2.1]
  -- the endomorphism `T`
  have hmod := GL2TF.HeckeModule.heckeAct_module K (R₀ := ℤ) (Units.map (finEmbed a b).toMonoidHom)
    (orderCompletionUnits O) (fun γ => splitRep s k (γ : QuatAlg ℚ a b))
    (by
      show splitRep s k ((1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1
      rw [Units.val_one, hρ1])
    (fun γ r v => map_zsmul _ r v)
  have hH := (normNSet_basic O n hn).2.2.2.2 ℤ
  have hTW : ∀ g ∈ quatForms O s k, heckeOperator O n g ∈ quatForms O s k := fun g hg => hmod.1 ⟨_, hH⟩ g hg
  have hsmul : ∀ (c : K) (g : (BHat a b)ˣ → symPowerModule K (k - 2)),
      heckeOperator O n (c • g) = c • heckeOperator O n g := by
    intro c g
    funext x
    simp only [heckeOperator, GL2TF.HeckeModule.heckeAct, Pi.smul_apply]
    rw [smul_finsum]
    exact finsum_congr fun C => smul_comm _ _ _
  let T : Module.End K (quatForms O s k) :=
    { toFun := fun f => ⟨heckeOperator O n f, hTW f f.2⟩
      map_add' := fun f g => Subtype.ext (hmod.2.2.2.2.2 ⟨_, hH⟩ f f.2 g g.2)
      map_smul' := fun c f => Subtype.ext (hsmul c f) }
  have hTval : ∀ F : quatForms O s k, ((T F : quatForms O s k) : (BHat a b)ˣ → symPowerModule K (k - 2)) =
      heckeOperator O n (F : (BHat a b)ˣ → symPowerModule K (k - 2)) := fun F => rfl
  refine ⟨T, hTval, ?_⟩
  -- finite-dimensionality
  obtain ⟨eb, -⟩ := (symPower_basic K (k - 2)).1
  have : Module.Finite K (symPowerModule K (k - 2)) := Module.Finite.of_basis eb
  -- transport to `Π_c V^{Γ_c}` and split the trace into diagonal blocks
  obtain ⟨e, he⟩ := forms_class_decomposition O s k Quotient.out hr
  set W : classSet O → Submodule K (symPowerModule K (k - 2)) := fun c =>
    ⨅ γ : classStabilizer (orderCompletionUnits O) (Quotient.out c),
      LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1) with hW
  have hsymm : ∀ (v : (c : classSet O) → W c) (c : classSet O),
      ((e.symm v : quatForms O s k) : (BHat a b)ˣ → symPowerModule K (k - 2)) (Quotient.out c) = (v c : _) := by
    intro v c
    rw [← he, e.apply_symm_apply]
  have hconj := LinearMap.trace_conj' (R := K) (M := quatForms O s k) (N := (c : classSet O) → W c) T e
  rw [← hconj]
  have hfreeW : ∀ c, Module.Free K (W c) := fun c => by
    exact @Module.Free.of_divisionRing K (W c) _ (W c).addCommGroup (W c).module
  have : Module.Free K ((c : classSet O) → W c) := Module.Free.pi K (fun c => W c)
  set A := e.conj T with hAdef
  have hA : A = ∑ c, (A ∘ₗ LinearMap.single K (fun c => W c) c) ∘ₗ LinearMap.proj c := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single]
    rw [← map_sum, LinearMap.sum_single_apply]
  have htr : LinearMap.trace K _ A = ∑ c, LinearMap.trace K (W c)
      (LinearMap.proj c ∘ₗ A ∘ₗ LinearMap.single K (fun c => W c) c) := by
    conv_lhs => rw [hA]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ =>
      LinearMap.trace_comp_comm' (R := K) (M := (c : classSet O) → W c) (N := W c) (LinearMap.proj c)
        (A ∘ₗ LinearMap.single K (fun c => W c) c)
  rw [htr]
  -- the diagonal block at `c` is `w ↦ |Γ_c|⁻¹ Σ_{γ ∈ S_{cc}(n)} ρ(γ) w`
  have hblock : ∀ (c : classSet O) (w : W c),
      (((LinearMap.proj c ∘ₗ A ∘ₗ LinearMap.single K (fun c => W c) c) w : W c) : symPowerModule K (k - 2)) =
        ((Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ •
          ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b)) (w : symPowerModule K (k - 2)) := by
    intro c w
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, hAdef, LinearEquiv.conj_apply]
    refine (he (T (e.symm (Pi.single c w))) c).trans ?_
    rw [hTval, hMF _ (e.symm (Pi.single c w)).2 c, finsum_eq_single _ c]
    · rw [hsymm, Pi.single_eq_same, LinearMap.smul_apply, LinearMap.sum_apply,
        ← finsum_mem_eq_finite_toFinset_sum _ (hS c c).1]
      rfl
    · intro c' hc'
      rw [hsymm, Pi.single_eq_of_ne hc', Submodule.coe_zero]
      simp
  -- the trace of the block equals the trace of `A_c` on `V`
  have hblocktr : ∀ c : classSet O,
      LinearMap.trace K (W c) (LinearMap.proj c ∘ₗ A ∘ₗ LinearMap.single K (fun c => W c) c) =
        LinearMap.trace K (symPowerModule K (k - 2))
          ((Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ •
            ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b)) := by
    intro c
    have : Finite (classStabilizer (orderCompletionUnits O) (Quotient.out c)) :=
      ((stabilizer_units O (Quotient.out c)).2.2 ha hb).1
    letI := Fintype.ofFinite (classStabilizer (orderCompletionUnits O) (Quotient.out c))
    have hne : (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hcardΓ : (Finset.univ : Finset (classStabilizer (orderCompletionUnits O) (Quotient.out c))).card =
        Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    have hmemW : ∀ w : symPowerModule K (k - 2), w ∈ W c ↔
        ∀ δ : classStabilizer (orderCompletionUnits O) (Quotient.out c),
          splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) w = w := by
      intro w
      simp only [hW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hm : ∀ (δ₁ δ₂ : (QuatAlg ℚ a b)ˣ) (v : symPowerModule K (k - 2)),
        splitRep s k (δ₁ : QuatAlg ℚ a b) (splitRep s k (δ₂ : QuatAlg ℚ a b) v) =
          splitRep s k ((δ₁ * δ₂ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v := by
      intro δ₁ δ₂ v
      rw [Units.val_mul, hρmul, Module.End.mul_apply]
    set κ : K := (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ with hκ
    -- the averaging projection `π : V → V^Γ`
    obtain ⟨avg, havgdef⟩ : ∃ avg : Module.End K (symPowerModule K (k - 2)),
        avg = κ • ∑ δ : classStabilizer (orderCompletionUnits O) (Quotient.out c),
          splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := ⟨_, rfl⟩
    have havg : ∀ v, avg v = κ • ∑ δ : classStabilizer (orderCompletionUnits O) (Quotient.out c),
        splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v := by
      intro v
      rw [havgdef, LinearMap.smul_apply, LinearMap.sum_apply]
    have havgW : ∀ v, avg v ∈ W c := by
      intro v
      rw [hmemW]
      intro δ₀
      rw [havg, map_smul, map_sum]
      refine congrArg (fun t => κ • t) ?_
      rw [Finset.sum_congr rfl fun (δ : classStabilizer (orderCompletionUnits O) (Quotient.out c)) _ => hm δ₀ δ v]
      exact Fintype.sum_equiv (Equiv.mulLeft δ₀)
        (fun δ => splitRep s k ((((δ₀ : (QuatAlg ℚ a b)ˣ) * δ : (QuatAlg ℚ a b)ˣ)) : QuatAlg ℚ a b) v)
        (fun δ => splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v) (fun δ => rfl)
    obtain ⟨π, hπ⟩ : ∃ π : symPowerModule K (k - 2) →ₗ[K] W c, ∀ v, (π v : symPowerModule K (k - 2)) = avg v :=
      ⟨LinearMap.codRestrict (W c) avg havgW, fun v => rfl⟩
    have hπincl : π ∘ₗ (W c).subtype = LinearMap.id := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      rw [LinearMap.comp_apply, hπ, Submodule.subtype_apply, LinearMap.id_apply, havg, Finset.sum_congr rfl (fun δ _ => (hmemW _).mp w.2 δ), Finset.sum_const, hcardΓ,
        ← Nat.cast_smul_eq_nsmul K, smul_smul, hκ, inv_mul_cancel₀ hne, one_smul]
    -- `A_c` is right `Γ`-invariant, since `S_{cc}(n) Γ = S_{cc}(n)`
    have hAc : ∀ v, (κ • ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b)) v =
        κ • ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b) v := by
      intro v
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
    have hright : ∀ (δ : classStabilizer (orderCompletionUnits O) (Quotient.out c)) (v : symPowerModule K (k - 2)),
        (κ • ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b))
            (splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v) =
          (κ • ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b)) v := by
      intro δ v
      rw [hAc, hAc]
      refine congrArg (fun t => κ • t) ?_
      rw [Finset.sum_congr rfl fun γ _ => hm γ δ v]
      refine Finset.sum_nbij' (fun γ => γ * δ) (fun γ => γ * (δ : (QuatAlg ℚ a b)ˣ)⁻¹) ?_ ?_ ?_ ?_ ?_
      · intro γ hγ
        rw [Set.Finite.mem_toFinset] at hγ ⊢
        exact (hS c c).2 γ hγ δ δ.2
      · intro γ hγ
        rw [Set.Finite.mem_toFinset] at hγ ⊢
        exact (hS c c).2 γ hγ _ (inv_mem δ.2)
      · intro γ _
        simp
      · intro γ _
        simp
      · intro γ _
        rfl
    have hfactor : κ • ∑ γ ∈ (hS c c).1.toFinset, splitRep s k (γ : QuatAlg ℚ a b) =
        (W c).subtype ∘ₗ (LinearMap.proj c ∘ₗ A ∘ₗ LinearMap.single K (fun c => W c) c) ∘ₗ π := by
      apply LinearMap.ext
      intro v
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, hblock c (π v)]
      rw [hπ, havg, map_smul, map_sum, Finset.sum_congr rfl fun δ _ => hright δ v, Finset.sum_const, hcardΓ,
        ← Nat.cast_smul_eq_nsmul K, smul_smul, hκ, inv_mul_cancel₀ hne, one_smul]
    rw [hfactor, LinearMap.trace_comp_comm' (R := K) (M := symPowerModule K (k - 2)) (N := W c)
      ((LinearMap.proj c ∘ₗ A ∘ₗ LinearMap.single K (fun c => W c) c) ∘ₗ π) (W c).subtype,
      LinearMap.comp_assoc, hπincl, LinearMap.comp_id]
  simp only [hblocktr]
  have hTS := tr_set_eq ha hb O n hn
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  show _ = ∑ᶠ γ ∈ {γ : QuatAlg ℚ a b | finEmbed a b γ ∈
          (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
            (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
            (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) ∧ nrd γ = n},
        heckePolyRing k ((trd γ : ℚ) : K) (n : K)
  rw [(hTS c).2, finsum_mem_image (fun γ _ γ' _ h => Units.ext h), finsum_mem_eq_finite_toFinset_sum _ (hS c c).1]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [Set.Finite.mem_toFinset] at hγ
  have hk2 : k - 2 + 2 = k := by omega
  rw [splitRep, (symPower_trace K).1, hk2, ((splitting_norm_trace ha.ne hb.ne s).2.1 _),
    ((splitting_norm_trace ha.ne hb.ne s).1 _), (hTS c).1 γ hγ]
  push_cast
  rfl


end GL2TF.Quat
