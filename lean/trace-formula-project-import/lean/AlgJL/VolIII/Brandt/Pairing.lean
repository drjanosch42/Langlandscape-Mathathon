import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.HeckeLocal
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The norm-weighted pairing, self-adjointness, the Eisenstein line (Q3 U2, items 15–18, 35, 36)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §2 (items 15–18) and §3 (items 35, 36) of
`docs/sprints/Q3-plan.md` §1.2.

Design (plan §1.1 item 6, §3: conventions row N9 corrected for `k > 2`, user decision Q3-U1):
* `ν(x) := ‖nrd x‖_{𝔸_f} = Π_p |nrd(x)_p|_p ∈ ℚ_{>0}`, written with `Padic.valuation` (`|y|_p = p^{−v_p(y)}`); a
  `finprod`, whose junk value `1` never occurs for units (almost all `nrd(x)_p` are `p`-adic units);
* `⟨f, g⟩ := Σ_{c ∈ X(O)} |Γ_{x_c}|⁻¹ ν(x_c)^{k−2} β_{k−2}(f(x_c), g(x_c))` with the representatives `x_c = c.out`
  (as Q2's `mass`), defined for all functions `f, g : B̂^× → V_{k−2}(K)`;
* the self-adjointness `III.brandt.thm:hecke-self-adjoint` is stated for **every** order and every `n ≥ 1` (plan trap 7,
  resolved on paper in A: `γ ↦ qγ̄` maps `S_{cc'}(n)` onto `S_{c'c}(n)` for every order; FA attacks it at G1).

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF.HeckeModule

/-- The norm weight `ν(x) := ‖nrd x‖_{𝔸_f} = Π_p |nrd(x)_p|_p = Π_p p^{−v_p(nrd(x)_p)}` of `x ∈ B̂^×`. -/
@[tf_id "III.qform.def:norm-weight"]
noncomputable def normWeight {a b : ℤ} (x : (BHat a b)ˣ) : ℚ :=
  ∏ᶠ p : Nat.Primes, ((p : ℕ) : ℚ) ^ (-(Padic.valuation
    (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p (nrd (show QuatAlg FinAdele a b from (x : BHat a b))))))

theorem trd_add_aux {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) : trd (x + y) = trd x + trd y := by
  simp [trd]; ring

theorem nrd_add_aux {R : Type*} [CommRing R] {a b : ℤ} (x y : QuatAlg R a b) :
    nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  simp [nrd, trd]; ring

theorem nrd_smul_aux {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    nrd (c • x) = c ^ 2 * nrd x := by
  simp [nrd]; ring

theorem trd_smul_aux {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    trd (c • x) = c * trd x := by
  simp [trd]; ring

theorem zhat_smul_bhat_eq {a b : ℤ} (c : Zhat) (x : BHat a b) :
    (show QuatAlg FinAdele a b from c • x) = (c : FinAdele) • (show QuatAlg FinAdele a b from x) := rfl

theorem trd_mem_zhat_of_mem_completion {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    trd (show QuatAlg FinAdele a b from y) ∈ Zhat := by
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨⟨n, hn⟩, -⟩ := trd_nrd_int_of_mem O hz
    have h := ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) z).2
    rw [show (show QuatAlg FinAdele a b from finEmbed a b z) = baseChange a b (algebraMap ℚ FinAdele) z from rfl, h,
      hn, map_intCast]
    exact intCast_mem Zhat n
  | zero =>
    show trd (0 : QuatAlg FinAdele a b) ∈ Zhat
    simp [trd]
  | add x z _ _ hx hz =>
    rw [show (show QuatAlg FinAdele a b from x + z) =
      (show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z) from rfl, trd_add_aux]
    exact Zhat.add_mem hx hz
  | smul c x _ hx =>
    rw [zhat_smul_bhat_eq, trd_smul_aux]
    exact Zhat.mul_mem c.2 hx

theorem star_smul_aux {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    c • star x = star (c • x) := by
  ext <;> simp

theorem star_mem_completion {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    ∃ z : BHat a b, (show QuatAlg FinAdele a b from z) = star (show QuatAlg FinAdele a b from y) ∧
      z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨finEmbed a b (star z), ?_, Submodule.subset_span ⟨star z, star_mem_order O hz, rfl⟩⟩
    show baseChange a b (algebraMap ℚ FinAdele) (star z) = star (baseChange a b (algebraMap ℚ FinAdele) z)
    ext <;> simp [baseChange]
  | zero =>
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    show (0 : QuatAlg FinAdele a b) = star (0 : QuatAlg FinAdele a b)
    rw [star_zero]
  | add x z _ _ hx hz =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    obtain ⟨z', hz'1, hz'2⟩ := hz
    refine ⟨x' + z', ?_, Submodule.add_mem _ hx'2 hz'2⟩
    show (show QuatAlg FinAdele a b from x') + (show QuatAlg FinAdele a b from z') =
      star ((show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z))
    rw [star_add, hx'1, hz'1]
  | smul c x _ hx =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    refine ⟨c • x', ?_, Submodule.smul_mem _ c hx'2⟩
    rw [zhat_smul_bhat_eq, zhat_smul_bhat_eq, hx'1, star_smul_aux]

theorem nrd_mem_zhat_of_mem_completion {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    nrd (show QuatAlg FinAdele a b from y) ∈ Zhat := by
  have hy' := hy
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨-, ⟨n, hn⟩⟩ := trd_nrd_int_of_mem O hz
    have h := ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) z).1
    rw [show (show QuatAlg FinAdele a b from finEmbed a b z) = baseChange a b (algebraMap ℚ FinAdele) z from rfl, h,
      hn, map_intCast]
    exact intCast_mem Zhat n
  | zero =>
    show nrd (0 : QuatAlg FinAdele a b) ∈ Zhat
    simp [nrd]
  | add x z hxm hzm hx hz =>
    rw [← latticeCompletion] at hxm hzm
    rw [show (show QuatAlg FinAdele a b from x + z) =
      (show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z) from rfl, nrd_add_aux]
    refine Zhat.add_mem (Zhat.add_mem (hx hxm) (hz hzm)) ?_
    obtain ⟨z', hz'1, hz'2⟩ := star_mem_completion O hzm
    have h := trd_mem_zhat_of_mem_completion O (mul_mem_orderCompletion O hxm hz'2)
    rwa [show (show QuatAlg FinAdele a b from x * z') =
      (show QuatAlg FinAdele a b from x) * (show QuatAlg FinAdele a b from z') from rfl, hz'1] at h
  | smul c x hxm hx =>
    rw [← latticeCompletion] at hxm
    rw [zhat_smul_bhat_eq, nrd_smul_aux]
    exact Zhat.mul_mem (Zhat.pow_mem c.2 2) (hx hxm)

/-- The finite idele `(1, c)` for `c ∈ 𝔸_f^×` (proof helper, as a term). -/
theorem ideleNorm_one_fin (c : FinAdeleˣ) :
    ideleNorm (MulEquiv.prodUnits.symm (1, c)) = ∏ᶠ p : Nat.Primes, ‖(c : FinAdele) p‖ := by
  change ideleNormFun _ = _
  rw [ideleNormFun]
  have h1 : ((MulEquiv.prodUnits.symm (1, c) : Adeleˣ) : Adele) = (1, (c : FinAdele)) := rfl
  rw [h1, abs_one, one_mul]
  exact finprod_congr fun p => Local.normAbs_padic _

theorem finAdele_unit_apply_ne_zero (c : FinAdeleˣ) (p : Nat.Primes) : (c : FinAdele) p ≠ 0 := by
  have h := congrArg (fun z : FinAdele => z p) c.mul_inv
  simp only [RestrictedProduct.mul_apply, RestrictedProduct.one_apply] at h
  exact left_ne_zero_of_mul_eq_one h

theorem normWeight_eq_ideleNorm {a b : ℤ} (x : (BHat a b)ˣ) (c : FinAdeleˣ)
    (hc : (c : FinAdele) = nrd (show QuatAlg FinAdele a b from (x : BHat a b))) :
    ((normWeight x : ℚ) : ℝ) = ideleNorm (MulEquiv.prodUnits.symm (1, c)) := by
  rw [ideleNorm_one_fin, normWeight, ← hc]
  have h := (Rat.castHom ℝ).toMonoidHom.map_finprod_of_injective Rat.cast_injective
    (fun p : Nat.Primes => ((p : ℕ) : ℚ) ^ (-(Padic.valuation
      (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p (c : FinAdele)))))
  refine h.trans (finprod_congr fun p => ?_)
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_zpow₀, map_natCast]
  rw [Padic.norm_eq_zpow_neg_valuation (finAdele_unit_apply_ne_zero c p)]
  rfl

theorem nrd_units_mul_inv {a b : ℤ} (x : (BHat a b)ˣ) :
    nrd (show QuatAlg FinAdele a b from (x : BHat a b)) *
      nrd (show QuatAlg FinAdele a b from ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
  have hmul : ∀ x y : QuatAlg FinAdele a b, nrd (x * y) = nrd x * nrd y :=
    (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1
  have h0 : (show QuatAlg FinAdele a b from ((x * x⁻¹ : (BHat a b)ˣ) : BHat a b)) = (1 : QuatAlg FinAdele a b) := by
    show ((x * x⁻¹ : (BHat a b)ˣ) : BHat a b) = (1 : BHat a b)
    exact Units.mul_inv x
  have h1 : nrd (show QuatAlg FinAdele a b from ((x * x⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
    rw [h0]
    simp [nrd]
  rw [← h1, Units.val_mul]
  exact (hmul _ _).symm

theorem nrd_unit_exists {a b : ℤ} (x : (BHat a b)ˣ) :
    ∃ c : FinAdeleˣ, (c : FinAdele) = nrd (show QuatAlg FinAdele a b from (x : BHat a b)) :=
  ⟨⟨_, _, nrd_units_mul_inv x, (mul_comm _ _).trans (nrd_units_mul_inv x)⟩, rfl⟩

/-- `ν(x) > 0`; `ν(xy) = ν(x)ν(y)`; `ν(u) = 1` for `u ∈ Ô^×`; and for `a, b < 0`: `ν(ι(γ)xu) = nrd(γ)⁻¹ ν(x)` for
`γ ∈ B^×`, `x ∈ B̂^×`, `u ∈ Ô^×`. -/
@[tf_id "III.qform.lem:norm-weight-transform"]
theorem normWeight_transform {a b : ℤ} (O : QOrder a b) :
    (∀ x : (BHat a b)ˣ, 0 < normWeight x) ∧
    (∀ x y : (BHat a b)ˣ, normWeight (x * y) = normWeight x * normWeight y) ∧
    (∀ u ∈ orderCompletionUnits O, normWeight u = 1) ∧
    (a < 0 → b < 0 → ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      normWeight (Units.map (finEmbed a b).toMonoidHom γ * x * u) = (nrd (γ : QuatAlg ℚ a b))⁻¹ * normWeight x) := by
  have hmulnrd : ∀ x y : QuatAlg FinAdele a b, nrd (x * y) = nrd x * nrd y :=
    (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1
  have hpos : ∀ x : (BHat a b)ˣ, 0 < normWeight x := fun x =>
    finprod_induction (fun q : ℚ => 0 < q) zero_lt_one (fun _ _ => mul_pos)
      (fun p => zpow_pos (Nat.cast_pos.mpr p.2.pos) _)
  have hmul : ∀ x y : (BHat a b)ˣ, normWeight (x * y) = normWeight x * normWeight y := by
    intro x y
    obtain ⟨cx, hcx⟩ := nrd_unit_exists x
    obtain ⟨cy, hcy⟩ := nrd_unit_exists y
    have hcxy : ((cx * cy : FinAdeleˣ) : FinAdele) = nrd (show QuatAlg FinAdele a b from ((x * y : (BHat a b)ˣ) : BHat a b)) := by
      rw [Units.val_mul, hcx, hcy, ← hmulnrd]
      rfl
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_mul, normWeight_eq_ideleNorm _ _ hcxy, normWeight_eq_ideleNorm _ _ hcx,
      normWeight_eq_ideleNorm _ _ hcy, ← map_mul, ← map_mul]
    congr 2
    rw [Prod.mk_mul_mk, one_mul]
  have hunit : ∀ u ∈ orderCompletionUnits O, normWeight u = 1 := by
    intro u hu
    obtain ⟨c, hc⟩ := nrd_unit_exists u
    have h1 := nrd_mem_zhat_of_mem_completion O hu.1
    have h2 := nrd_mem_zhat_of_mem_completion O hu.2
    have hprod := nrd_units_mul_inv u
    let w : Zhatˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext hprod, Subtype.ext ((mul_comm _ _).trans hprod)⟩
    have hw : ideleInfFin 1 w = MulEquiv.prodUnits.symm (1, c) := by
      apply Units.ext
      rw [ideleInfFin_val one_ne_zero]
      show ((1 : ℝ), nrd (show QuatAlg FinAdele a b from (u : BHat a b))) = (1, (c : FinAdele))
      rw [hc]
    apply Rat.cast_injective (α := ℝ)
    rw [normWeight_eq_ideleNorm _ _ hc, ← hw, ideleNorm_ideleInfFin one_ne_zero, abs_one, Rat.cast_one]
  refine ⟨hpos, hmul, hunit, fun ha hb γ x u hu => ?_⟩
  rw [hmul, hmul, hunit u hu, mul_one]
  congr 1
  -- `ν(ι(γ)) = nrd(γ)⁻¹`
  set q : ℚ := nrd (γ : QuatAlg ℚ a b) with hq
  have hqmul : q * nrd ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
    rw [hq, ← GL2TF.Quat.nrd_mul', Units.mul_inv]
    simp [nrd]
  have hq0 : q ≠ 0 := left_ne_zero_of_mul_eq_one hqmul
  have hqpos : 0 < q := by
    have h := ((nrd_definite ha hb).1 (γ : QuatAlg ℚ a b)).1
    refine lt_of_le_of_ne (le_trans (by positivity) h) (Ne.symm hq0)
  set q' : ℚˣ := Units.mk0 q hq0 with hq'
  obtain ⟨c, hc⟩ := nrd_unit_exists (Units.map (finEmbed a b).toMonoidHom γ)
  have hcq : (c : FinAdele) = algebraMap ℚ FinAdele q := by
    rw [hc, hq]
    exact ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) γ).1
  have hsplit : ratIdele q' = ideleInfFin (q : ℝ) 1 * MulEquiv.prodUnits.symm (1, c) := by
    apply Units.ext
    rw [Units.val_mul, ideleInfFin_val (Rat.cast_ne_zero.mpr hq0), ratIdele_val]
    rw [show ((MulEquiv.prodUnits.symm (1, c) : Adeleˣ) : Adele) = (1, (c : FinAdele)) from rfl, Prod.mk_mul_mk, hcq]
    refine Prod.ext ?_ ?_ <;> simp [hq']
  have hnorm := product_formula q'
  rw [hsplit, map_mul, ideleNorm_ideleInfFin (Rat.cast_ne_zero.mpr hq0), ← normWeight_eq_ideleNorm _ _ hc,
    abs_of_pos (Rat.cast_pos.mpr hqpos)] at hnorm
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_inv]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hnorm)

/-- The norm-weighted pairing `⟨f, g⟩ := Σ_{c ∈ X(O)} |Γ_{x_c}|⁻¹ ν(x_c)^{k−2} β_{k−2}(f(x_c), g(x_c))` (representatives
`x_c = c.out`). -/
@[tf_id "III.qform.def:weighted-pairing"]
noncomputable def weightedPairing {K : Type*} [Field K] {a b : ℤ} (O : QOrder a b) (k : ℕ)
    (f g : (BHat a b)ˣ → symPowerModule K (k - 2)) : K :=
  ∑ᶠ c : classSet O,
    (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ *
      ((normWeight (Quotient.out c) : ℚ) : K) ^ (k - 2) *
        symPowerPairing K (k - 2) (f (Quotient.out c)) (g (Quotient.out c))

theorem weightedPairing_term_eq {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k : ℕ) {f g : (BHat a b)ˣ → symPowerModule K (k - 2)}
    (hf : f ∈ quatForms O s k) (hg : g ∈ quatForms O s k) (x y : (BHat a b)ˣ) (hxy : classOf O x = classOf O y) :
    (Nat.card (classStabilizer (orderCompletionUnits O) x) : K)⁻¹ * ((normWeight x : ℚ) : K) ^ (k - 2) *
        symPowerPairing K (k - 2) (f x) (g x) =
      (Nat.card (classStabilizer (orderCompletionUnits O) y) : K)⁻¹ * ((normWeight y : ℚ) : K) ^ (k - 2) *
        symPowerPairing K (k - 2) (f y) (g y) := by
  obtain ⟨h, ⟨γ, rfl⟩, u, hu, rfl⟩ := DoubleCoset.eq.mp hxy
  have hcard : Nat.card (classStabilizer (orderCompletionUnits O) (Units.map (finEmbed a b).toMonoidHom γ * x * u)) =
      Nat.card (classStabilizer (orderCompletionUnits O) x) := by
    rw [(stabilizer_units O x).2.1 γ u hu]
    exact Subgroup.card_map_of_injective (MulAut.conj γ).injective
  have hν := (normWeight_transform O).2.2.2 ha hb γ x u hu
  have hfx : f (Units.map (finEmbed a b).toMonoidHom γ * x * u) = splitRep s k (γ : QuatAlg ℚ a b) (f x) :=
    hf γ x u hu
  have hgx : g (Units.map (finEmbed a b).toMonoidHom γ * x * u) = splitRep s k (γ : QuatAlg ℚ a b) (g x) :=
    hg γ x u hu
  have hβ := (symPowerPairing_adjoint K (k - 2)).2.2.2 (s (γ : QuatAlg ℚ a b)) (f x) (g x)
  have hdet := (splitting_norm_trace ha.ne hb.ne s).1 (γ : QuatAlg ℚ a b)
  have hq0 : nrd (γ : QuatAlg ℚ a b) ≠ 0 := by
    intro h0
    have h1 : nrd ((γ : QuatAlg ℚ a b) * ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) = 1 := by
      rw [Units.mul_inv]
      simp [nrd]
    rw [GL2TF.Quat.nrd_mul', h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [hcard, hν, hfx, hgx, splitRep, hβ, hdet, Rat.cast_mul, Rat.cast_inv, mul_pow, inv_pow]
  have hq0' : ((nrd (γ : QuatAlg ℚ a b) : ℚ) : K) ^ (k - 2) ≠ 0 := pow_ne_zero _ (Rat.cast_ne_zero.mpr hq0)
  field_simp

theorem pairing_invariant_nondeg {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k : ℕ) (x : (BHat a b)ˣ) (v : symPowerModule K (k - 2))
    (hv : ∀ γ : classStabilizer (orderCompletionUnits O) x,
      splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) v = v)
    (h : ∀ w : symPowerModule K (k - 2), (∀ γ : classStabilizer (orderCompletionUnits O) x,
      splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) w = w) → symPowerPairing K (k - 2) v w = 0) :
    v = 0 := by
  classical
  have : Finite (classStabilizer (orderCompletionUnits O) x) := ((stabilizer_units O x).2.2 ha hb).1
  letI : Fintype (classStabilizer (orderCompletionUnits O) x) := Fintype.ofFinite _
  have hρmul : ∀ γ δ : (QuatAlg ℚ a b)ˣ, splitRep s k ((γ * δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) =
      splitRep s k (γ : QuatAlg ℚ a b) * splitRep s k (δ : QuatAlg ℚ a b) := by
    intro γ δ
    rw [splitRep, Units.val_mul, map_mul, (symPower_basic K (k - 2)).2.2.1]
    rfl
  have hnrdpos : ∀ g : (QuatAlg ℚ a b)ˣ, 0 < nrd (g : QuatAlg ℚ a b) := by
    intro g
    have h1 := (nrd_definite ha hb).1 (g : QuatAlg ℚ a b)
    refine lt_of_le_of_ne (le_trans (by positivity) h1.1) fun h0 => ?_
    exact g.ne_zero (h1.2.mp h0.symm)
  have hadj : ∀ (γ : classStabilizer (orderCompletionUnits O) x) (w : symPowerModule K (k - 2)),
      symPowerPairing K (k - 2) v (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) w) =
        ((nrd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) : ℚ) : K) ^ (k - 2) * symPowerPairing K (k - 2) v w := by
    intro γ w
    set g : (QuatAlg ℚ a b)ˣ := γ.1 with hg
    have h1 := (symPowerPairing_adjoint K (k - 2)).1 (s (g : QuatAlg ℚ a b)).adjugate v w
    have hadjadj : (s (g : QuatAlg ℚ a b)).adjugate.adjugate = s (g : QuatAlg ℚ a b) := by
      rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hadjadj] at h1
    have hsinv : s (g : QuatAlg ℚ a b) * s ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hadjeq : (s (g : QuatAlg ℚ a b)).adjugate =
        Matrix.scalar (Fin 2) ((nrd (g : QuatAlg ℚ a b) : ℚ) : K) * s ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
      calc (s (g : QuatAlg ℚ a b)).adjugate
          = (s (g : QuatAlg ℚ a b)).adjugate *
              (s (g : QuatAlg ℚ a b) * s ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b)) := by rw [hsinv, mul_one]
        _ = ((s (g : QuatAlg ℚ a b)).adjugate * s (g : QuatAlg ℚ a b)) *
              s ((g⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by rw [mul_assoc]
        _ = _ := by
          rw [Matrix.adjugate_mul, (splitting_norm_trace ha.ne hb.ne s).1, Matrix.scalar_apply,
            Matrix.smul_one_eq_diagonal]
    have hinvmem : (γ⁻¹ : classStabilizer (orderCompletionUnits O) x) =
        ⟨g⁻¹, inv_mem γ.2⟩ := rfl
    have hvinv := hv γ⁻¹
    rw [hinvmem] at hvinv
    have hact : symPowerAction K (k - 2) (s (g : QuatAlg ℚ a b)).adjugate v =
        ((nrd (g : QuatAlg ℚ a b) : ℚ) : K) ^ (k - 2) • v := by
      rw [hadjeq, (symPower_basic K (k - 2)).2.2.1, (symPower_basic K (k - 2)).2.2.2.2.1, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply]
      congr 1
    rw [hact, LinearMap.map_smul₂, smul_eq_mul] at h1
    rw [splitRep, ← h1]
  set π : symPowerModule K (k - 2) → symPowerModule K (k - 2) := fun w =>
    ∑ γ : classStabilizer (orderCompletionUnits O) x, splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) w
    with hπdef
  have hπ : ∀ w, ∀ δ : classStabilizer (orderCompletionUnits O) x,
      splitRep s k ((δ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) (π w) = π w := by
    intro w δ
    simp only [hπdef, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft δ) _ _ fun γ => ?_
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, hρmul, Module.End.mul_apply]
  set S : ℚ := ∑ γ : classStabilizer (orderCompletionUnits O) x, nrd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) ^ (k - 2)
    with hS
  have hSpos : 0 < S := Finset.sum_pos (fun γ _ => pow_pos (hnrdpos _) _) Finset.univ_nonempty
  refine (symPowerPairing_adjoint K (k - 2)).2.1 v fun w => ?_
  have h0 := h (π w) (hπ w)
  simp only [hπdef, map_sum, hadj, ← Finset.sum_mul] at h0
  have hSK : ∑ γ : classStabilizer (orderCompletionUnits O) x,
      ((nrd ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) : ℚ) : K) ^ (k - 2) = (S : K) := by
    rw [hS]
    push_cast
    rfl
  rw [hSK] at h0
  exact (mul_eq_zero.mp h0).resolve_left (Rat.cast_ne_zero.mpr hSpos.ne')

/-- For `a, b < 0`, on `M_k(O; s)`: `⟨·, ·⟩` does not depend on the representatives; it is symmetric for `k` even and
nondegenerate. -/
@[tf_id "III.qform.lem:weighted-pairing-well-defined"]
theorem weightedPairing_well_defined {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k : ℕ) :
    (∀ r : classSet O → (BHat a b)ˣ, (∀ c, classOf O (r c) = c) →
      ∀ f ∈ quatForms O s k, ∀ g ∈ quatForms O s k,
        weightedPairing O k f g =
          ∑ᶠ c : classSet O,
            (Nat.card (classStabilizer (orderCompletionUnits O) (r c)) : K)⁻¹ *
              ((normWeight (r c) : ℚ) : K) ^ (k - 2) * symPowerPairing K (k - 2) (f (r c)) (g (r c))) ∧
    (Even k → ∀ f ∈ quatForms O s k, ∀ g ∈ quatForms O s k, weightedPairing O k f g = weightedPairing O k g f) ∧
    (∀ f ∈ quatForms O s k, (∀ g ∈ quatForms O s k, weightedPairing O k f g = 0) → f = 0) := by
  refine ⟨fun r hr f hf g hg => ?_, fun hk f hf g hg => ?_, ?_⟩
  · unfold weightedPairing
    refine finsum_congr fun c => ?_
    exact weightedPairing_term_eq ha hb O s k hf hg _ _ ((DoubleCoset.out_eq' c).trans (hr c).symm)
  · unfold weightedPairing
    refine finsum_congr fun c => ?_
    obtain ⟨j, hj⟩ := hk
    have hev : Even (k - 2) := ⟨j - 1, by omega⟩
    rw [(symPowerPairing_adjoint K (k - 2)).2.2.1 hev]
  · intro f hf hfg
    classical
    obtain ⟨e, he⟩ := forms_class_decomposition O s k (fun c => Quotient.out c) (fun c => DoubleCoset.out_eq' c)
    have hzero : ∀ c : classSet O, f (Quotient.out c) = 0 := by
      intro c
      have hvW := (e ⟨f, hf⟩ c).2
      rw [Submodule.mem_iInf] at hvW
      apply pairing_invariant_nondeg ha hb O s k (Quotient.out c) (f (Quotient.out c))
      · intro γ
        have h1 := hvW γ
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply, he] at h1
        exact h1
      · intro w hw
        have hwW : w ∈ ⨅ γ : classStabilizer (orderCompletionUnits O) (Quotient.out c),
            LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1) :=
          (Submodule.mem_iInf _).mpr fun γ => by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, hw γ, Module.End.one_apply, sub_self]
        set G := e.symm (Pi.single c ⟨w, hwW⟩) with hGdef
        have hG : ∀ c' : classSet O, (G : (BHat a b)ˣ → symPowerModule K (k - 2)) (Quotient.out c') =
            ((Pi.single c ⟨w, hwW⟩ : (c : classSet O) → ↥(⨅ γ : classStabilizer (orderCompletionUnits O)
              (Quotient.out c), LinearMap.ker (splitRep s k ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) - 1))) c' :
                symPowerModule K (k - 2)) := by
          intro c'
          rw [← he, hGdef, LinearEquiv.apply_symm_apply]
        have h0 := hfg G G.2
        unfold weightedPairing at h0
        rw [finsum_eq_single _ c] at h0
        · rw [hG, Pi.single_eq_same] at h0
          have : Finite (classStabilizer (orderCompletionUnits O) (Quotient.out c)) :=
            ((stabilizer_units O (Quotient.out c)).2.2 ha hb).1
          have hC : (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ ≠ 0 :=
            inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
          have hν : ((normWeight (Quotient.out c) : ℚ) : K) ^ (k - 2) ≠ 0 :=
            pow_ne_zero _ (Rat.cast_ne_zero.mpr ((normWeight_transform O).1 _).ne')
          exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hC hν)
        · intro c' hc'
          rw [hG, Pi.single_eq_of_ne hc']
          simp
    funext x
    obtain ⟨h, ⟨γ, rfl⟩, u, hu, hx⟩ :=
      DoubleCoset.mk_out_eq_mul (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x
    have hxeq : x = Units.map (finEmbed a b).toMonoidHom γ⁻¹ *
        Quotient.out (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x) * u⁻¹ := by
      rw [hx, map_inv]
      group
    rw [hxeq, hf γ⁻¹ _ u⁻¹ (inv_mem hu)]
    have hz := hzero (DoubleCoset.mk (Units.map (finEmbed a b).toMonoidHom).range (orderCompletionUnits O) x)
    rw [hz, map_zero]
    rfl

/-! ### Proof helpers for `hecke_self_adjoint` (copies of helpers of Brandt.lean, invisible to `lfile` here). -/

private theorem sa_zhat_unit_inv_mul (w : Zhatˣ) :
    (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((w : Zhat) : FinAdele) = 1 := by
  have := congrArg (fun z : Zhat => (z : FinAdele)) w.inv_mul
  simpa only [Subring.coe_mul, Subring.coe_one] using this

private theorem sa_nsmul_inv_mem {a b : ℤ} (O : QOrder a b) (n : ℕ) {y : (BHat a b)ˣ} (hy : y ∈ normNSet O n) :
    (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨hyO, w, hw⟩ := hy
  obtain ⟨S, hS, hSO⟩ := star_mem_completion O hyO
  have hyS : (y : BHat a b) * S = algebraMap FinAdele (BHat a b) (nrd (show QuatAlg FinAdele a b from (y : BHat a b))) := by
    show (show QuatAlg FinAdele a b from (y : BHat a b)) * (show QuatAlg FinAdele a b from S) = _
    rw [hS]
    exact ((nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).1 _).1
  have key : (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
    have h1 : (y : BHat a b) * ((((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S) = algebraMap FinAdele (BHat a b) (n : FinAdele) := by
      rw [mul_smul_comm, hyS, hw, Algebra.smul_def, ← map_mul]
      congr 1
      rw [mul_left_comm, sa_zhat_unit_inv_mul, mul_one]
    calc (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b)
        = ((y⁻¹ : (BHat a b)ˣ) : BHat a b) * algebraMap FinAdele (BHat a b) (n : FinAdele) := by
          rw [Algebra.smul_def, Algebra.commutes]
      _ = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
          rw [← h1, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact smul_mem_latticeCompletion _ ((w⁻¹ : Zhatˣ) : Zhat).2 hSO

private theorem sa_n_inv_mem {a b : ℤ} (O : QOrder a b) (n : ℕ) {P y : (BHat a b)ˣ}
    (hP : (P : BHat a b) = algebraMap FinAdele (BHat a b) (n : FinAdele)) (hy : y ∈ normNSet O n) :
    P * y⁻¹ ∈ normNSet O n := by
  have hval : ((P * y⁻¹ : (BHat a b)ˣ) : BHat a b) = (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) := by
    rw [Units.val_mul, hP, ← Algebra.smul_def]
  refine ⟨by rw [hval]; exact sa_nsmul_inv_mem O n hy, ?_⟩
  obtain ⟨-, w, hw⟩ := hy
  refine ⟨w⁻¹, ?_⟩
  have h1 := nrd_units_mul_inv y
  rw [hw] at h1
  have hw1 := sa_zhat_unit_inv_mul w
  rw [hval]
  show nrd ((n : FinAdele) • (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b))) = _
  rw [nrd_smul_aux]
  linear_combination (-((n : FinAdele) ^ 2 * nrd (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)))) * hw1 +
    ((n : FinAdele) * (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele)) * h1

/-- For `a, b < 0`, every order and `n ≥ 1`: `⟨T_n f, g⟩ = ⟨f, T_n g⟩` for `f, g ∈ M_k(O; s)`. -/
@[tf_id "III.brandt.thm:hecke-self-adjoint"]
theorem hecke_self_adjoint {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (O : QOrder a b) (s : Splitting K a b) (k n : ℕ) (hn : 0 < n) :
    ∀ f ∈ quatForms O s k, ∀ g ∈ quatForms O s k,
      weightedPairing O k (heckeOperator O n f) g = weightedPairing O k f (heckeOperator O n g) := by
  classical
  intro f hf g hg
  obtain ⟨hS, hMF⟩ := hecke_matrix_formula ha hb O s k n hn Quotient.out (fun c => DoubleCoset.out_eq' c)
  have : Finite (classSet O) := classSet_finite ha hb O
  letI := Fintype.ofFinite (classSet O)
  have hn0 : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨hνpos, hνmul, -, hνι⟩ := normWeight_transform O
  -- `ν(y) = 1/n` for `y ∈ Ô_n`
  have hνy : ∀ y ∈ normNSet O n, normWeight y = ((n : ℕ) : ℚ)⁻¹ := by
    rintro y ⟨-, w, hw⟩
    obtain ⟨c, hc⟩ := nrd_unit_exists y
    have hnR : ((n : ℕ) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
    have hsplit : MulEquiv.prodUnits.symm (1, c) =
        ratIdele (Units.mk0 ((n : ℕ) : ℚ) hn0) * ideleInfFin (((n : ℕ) : ℝ)⁻¹) w := by
      apply Units.ext
      rw [Units.val_mul, ideleInfFin_val hnR, ratIdele_val]
      rw [show ((MulEquiv.prodUnits.symm (1, c) : Adeleˣ) : Adele) = (1, (c : FinAdele)) from rfl]
      refine Prod.ext ?_ ?_
      · show (1 : ℝ) = (algebraMap ℚ Adele ((n : ℕ) : ℚ)).1 * ((n : ℕ) : ℝ)⁻¹
        rw [map_natCast, Prod.fst_natCast, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
      · show (c : FinAdele) = (algebraMap ℚ Adele ((n : ℕ) : ℚ)).2 * ((w : Zhat) : FinAdele)
        rw [hc, hw, map_natCast, Prod.snd_natCast]
    apply Rat.cast_injective (α := ℝ)
    rw [normWeight_eq_ideleNorm _ _ hc, hsplit, map_mul, product_formula, one_mul, ideleNorm_ideleInfFin hnR,
      abs_inv, Nat.abs_cast, Rat.cast_inv, Rat.cast_natCast]
  -- `ν(x_c) nrd(γ)/n = ν(x_{c'})` for `γ ∈ S_{cc'}(n)`
  have hνrel : ∀ (c c' : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n →
      normWeight (Quotient.out c) * nrd (γ : QuatAlg ℚ a b) / ((n : ℕ) : ℚ) = normWeight (Quotient.out c') := by
    intro c c' γ hγ
    have hx : Quotient.out c' = Units.map (finEmbed a b).toMonoidHom γ⁻¹ * Quotient.out c * 1 *
        ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c') := by
      rw [map_inv]; group
    have hγinv : nrd (γ : QuatAlg ℚ a b) * nrd ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
      rw [← GL2TF.Quat.nrd_mul', Units.mul_inv]
      simp [nrd]
    rw [hx, hνmul, hνι ha hb γ⁻¹ _ 1 (one_mem _), hνy _ hγ, inv_eq_of_mul_eq_one_left hγinv, div_eq_mul_inv]
    ring
  -- the involution `γ ↦ nγ⁻¹`
  set ν : (QuatAlg ℚ a b)ˣ := Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom (Units.mk0 ((n : ℕ) : ℚ) hn0)
    with hν
  have hνval : ((ν : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = ((n : ℕ) : QuatAlg ℚ a b) := by
    simp [hν]
  have hνc : ∀ γ : (QuatAlg ℚ a b)ˣ, ν * γ = γ * ν := by
    intro γ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hνval]
    exact Nat.cast_comm n (γ : QuatAlg ℚ a b)
  set P : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom ν with hPdef
  have hPval : (P : BHat a b) = algebraMap FinAdele (BHat a b) (n : FinAdele) := by
    rw [hPdef, Units.coe_map]
    show finEmbed a b (ν : QuatAlg ℚ a b) = _
    rw [hνval, map_natCast, map_natCast]
  have hPc : ∀ x : (BHat a b)ˣ, P * x = x * P := by
    intro x
    ext
    rw [Units.val_mul, Units.val_mul, hPval]
    exact Algebra.commutes (n : FinAdele) (x : BHat a b)
  have hmap : ∀ (c c' : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n →
      (Quotient.out c')⁻¹ * Units.map (finEmbed a b).toMonoidHom (ν * γ⁻¹) * Quotient.out c ∈ normNSet O n := by
    intro c c' γ hγ
    have h := sa_n_inv_mem O n hPval hγ
    convert h using 1
    rw [map_mul, map_inv, ← hPdef, mul_assoc, hPc, ← mul_assoc, ← mul_assoc, ← hPc, mul_assoc P]
    group
  have hinvol : ∀ γ : (QuatAlg ℚ a b)ˣ, ν * (ν * γ⁻¹)⁻¹ = γ := by
    intro γ
    rw [mul_inv_rev, inv_inv, ← mul_assoc, hνc, mul_assoc, mul_inv_cancel, mul_one]
  -- the adjoint identity, termwise
  have hsc : ∀ (q : ℚ) (A : Matrix (Fin 2) (Fin 2) K), q • A = Matrix.scalar (Fin 2) (q : K) * A := by
    intro q A
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, Rat.smul_def]
  have hstar : ∀ γ : (QuatAlg ℚ a b)ˣ, star (γ : QuatAlg ℚ a b) =
      (nrd (γ : QuatAlg ℚ a b) / ((n : ℕ) : ℚ)) • ((ν * γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
    intro γ
    have h1 : star (γ : QuatAlg ℚ a b) * (γ : QuatAlg ℚ a b) =
        algebraMap ℚ (QuatAlg ℚ a b) (nrd (γ : QuatAlg ℚ a b)) :=
      ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 _).2.1
    have h2 : star (γ : QuatAlg ℚ a b) = nrd (γ : QuatAlg ℚ a b) • ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) := by
      rw [Algebra.smul_def, ← h1, mul_assoc, Units.mul_inv, mul_one]
    rw [h2, Units.val_mul, hνval, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, div_mul_cancel₀ _ hn0]
  have hβ : ∀ (c c' : classSet O) (γ : (QuatAlg ℚ a b)ˣ),
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n →
      ∀ v w : symPowerModule K (k - 2),
      ((normWeight (Quotient.out c) : ℚ) : K) ^ (k - 2) *
          symPowerPairing K (k - 2) (splitRep s k (γ : QuatAlg ℚ a b) v) w =
        ((normWeight (Quotient.out c') : ℚ) : K) ^ (k - 2) *
          symPowerPairing K (k - 2) v (splitRep s k ((ν * γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) w) := by
    intro c c' γ hγ v w
    have hadj := (symPowerPairing_adjoint K (k - 2)).1 (s (γ : QuatAlg ℚ a b)) v w
    rw [← (splitting_norm_trace ha.ne hb.ne s).2.2.1, hstar, map_smul, hsc,
      (symPower_basic K (k - 2)).2.2.1, (symPower_basic K (k - 2)).2.2.2.2.1] at hadj
    rw [splitRep, hadj, ← hνrel c c' γ hγ, splitRep]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
    push_cast
    ring
  -- expand both sides
  have hwp : ∀ F G : (BHat a b)ˣ → symPowerModule K (k - 2), weightedPairing O k F G =
      ∑ c : classSet O, (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ *
        ((normWeight (Quotient.out c) : ℚ) : K) ^ (k - 2) *
          symPowerPairing K (k - 2) (F (Quotient.out c)) (G (Quotient.out c)) :=
    fun F G => finsum_eq_sum_of_fintype _
  have hT : ∀ F ∈ quatForms O s k, ∀ c : classSet O, heckeOperator O n F (Quotient.out c) =
      ∑ c' : classSet O, (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) : K)⁻¹ •
        ∑ γ ∈ (hS c c').1.toFinset, splitRep s k (γ : QuatAlg ℚ a b) (F (Quotient.out c')) := by
    intro F hF c
    rw [hMF F hF c, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← finsum_mem_eq_finite_toFinset_sum _ (hS c c').1]
    rfl
  rw [hwp, hwp]
  simp only [hT f hf, hT g hg, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  refine Finset.sum_nbij' (fun γ => ν * γ⁻¹) (fun γ => ν * γ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ ⊢
    exact hmap _ _ γ hγ
  · intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ ⊢
    exact hmap _ _ γ hγ
  · intro γ _
    exact hinvol γ
  · intro γ _
    exact hinvol γ
  · intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    have h := hβ _ _ γ hγ (f (Quotient.out c)) (g (Quotient.out c'))
    linear_combination
      (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) : K)⁻¹ *
        (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ * h

/-- `k = 2`, Eichler data, `n ≥ 1` prime to `DM`: `T_n 1 = σ₁(n) · 1`; `S_2(O; s) = {f ∈ M_2(O; s) : ⟨f, 1⟩ = 0}` is
`T_n`-stable; and every `f ∈ M_2(O; s)` is `c · 1 + f₀` with a unique `c ∈ K` and `f₀ ∈ S_2(O; s)`. -/
@[tf_id "III.brandt.thm:eisenstein-line"]
theorem eisenstein_line {K : Type*} [Field K] [CharZero K] {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b)
    (hD : RamifiedExactly a b D) (φ : LevelStructure O₀.1 M) (s : Splitting K a b) (n : ℕ) (hn : 0 < n)
    (hnDM : Nat.Coprime n (D * M)) :
    heckeOperator (eichlerOrder φ) n (constantForm (eichlerOrder φ) s : (BHat a b)ˣ → symPowerModule K (2 - 2)) =
      ((ArithmeticFunction.sigma 1 n : ℕ) : K) • (constantForm (eichlerOrder φ) s : (BHat a b)ˣ → _) ∧
    (∀ f ∈ quatForms (eichlerOrder φ) s 2,
      weightedPairing (eichlerOrder φ) 2 f (constantForm (eichlerOrder φ) s) = 0 →
        weightedPairing (eichlerOrder φ) 2 (heckeOperator (eichlerOrder φ) n f) (constantForm (eichlerOrder φ) s) = 0) ∧
    (∀ f ∈ quatForms (eichlerOrder φ) s 2, ∃! c : K,
      weightedPairing (eichlerOrder φ) 2 (f - c • (constantForm (eichlerOrder φ) s : (BHat a b)ˣ → _))
        (constantForm (eichlerOrder φ) s) = 0) := by
  classical
  have ha : a < 0 := hD.1
  have hb : b < 0 := hD.2.1
  set O := eichlerOrder φ with hO
  set one : (BHat a b)ˣ → symPowerModule K (2 - 2) :=
    (constantForm O s : (BHat a b)ˣ → symPowerModule K (2 - 2)) with hone
  have : Finite (classSet O) := classSet_finite ha hb O
  letI := Fintype.ofFinite (classSet O)
  have hwp : ∀ f g : (BHat a b)ˣ → symPowerModule K (2 - 2), weightedPairing O 2 f g =
      ∑ c : classSet O, (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : K)⁻¹ *
        ((normWeight (Quotient.out c) : ℚ) : K) ^ (2 - 2) *
          symPowerPairing K (2 - 2) (f (Quotient.out c)) (g (Quotient.out c)) :=
    fun f g => finsum_eq_sum_of_fintype _
  have hlin2 : ∀ (f g : (BHat a b)ˣ → symPowerModule K (2 - 2)) (c : K),
      weightedPairing O 2 f (c • g) = c * weightedPairing O 2 f g := by
    intro f g c
    rw [hwp, hwp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.smul_apply, map_smul, smul_eq_mul]
    ring
  have hlin1 : ∀ (f g h : (BHat a b)ˣ → symPowerModule K (2 - 2)) (c : K),
      weightedPairing O 2 (f - c • g) h = weightedPairing O 2 f h - c * weightedPairing O 2 g h := by
    intro f g h c
    rw [hwp, hwp, hwp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hfin := (normNSet_basic O n hn).2.2.2.1
  have hNright : ∀ y ∈ normNSet O n, ∀ u ∈ orderCompletionUnits O, y * u ∈ normNSet O n := by
    intro y hy u hu
    have := (normNSet_basic O n hn).1 y hy 1 (one_mem _) u hu
    rwa [one_mul] at this
  have hT1 : heckeOperator O n one = ((ArithmeticFunction.sigma 1 n : ℕ) : K) • one := by
    funext x
    unfold heckeOperator heckeAct
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    · have hterm : ∀ q ∈ hfin.toFinset,
          (normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ) (Quotient.out q) • one (x * Quotient.out q) = one x := by
        intro q hq
        have hqo : Quotient.out q ∈ normNSet O n := by
          obtain ⟨y, hy, rfl⟩ := (Set.Finite.mem_toFinset hfin).mp hq
          obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) y
          rw [hu]
          exact hNright y hy u u.2
        rw [Set.indicator_of_mem hqo, Pi.one_apply, one_smul]
        rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Pi.smul_apply, Nat.cast_smul_eq_nsmul,
        ← Nat.card_eq_card_finite_toFinset hfin, hecke_coset_count O₀ hD φ n hn hnDM]
    · intro q hq
      rw [Function.mem_support] at hq
      by_contra hq'
      apply hq
      rw [Set.indicator_of_notMem, zero_smul]
      intro hqo
      exact hq' (Finset.mem_coe.mpr ((Set.Finite.mem_toFinset hfin).mpr ⟨_, hqo, QuotientGroup.out_eq' q⟩))
  refine ⟨hT1, fun f hf h0 => ?_, fun f hf => ?_⟩
  · rw [hecke_self_adjoint ha hb O s 2 n hn f hf one (constantForm O s).2, hT1, hlin2, h0, mul_zero]
  · have hpos : weightedPairing O 2 one one ≠ 0 := by
      rw [hwp]
      have hβ : ∀ y, symPowerPairing K (2 - 2) (one y) (one y) = 1 := by
        intro y
        show symPowerPairing K 0 ⟨1, _⟩ ⟨1, _⟩ = 1
        simp [symPowerPairing, symExp]
      simp only [hβ, mul_one, Nat.sub_self, pow_zero]
      have hq : (0 : ℚ) < ∑ c : classSet O,
          ((Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : ℚ))⁻¹ := by
        apply Finset.sum_pos
        · intro c _
          have : Finite (classStabilizer (orderCompletionUnits O) (Quotient.out c)) :=
            ((stabilizer_units O _).2.2 ha hb).1
          exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
        · exact Finset.univ_nonempty_iff.mpr ⟨classOf O 1⟩
      have hK : ((∑ c : classSet O,
          ((Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) : ℚ))⁻¹ : ℚ) : K) ≠ 0 :=
        Rat.cast_ne_zero.mpr hq.ne'
      push_cast at hK
      exact hK
    refine ⟨weightedPairing O 2 f one / weightedPairing O 2 one one, ?_, fun c hc => ?_⟩
    · show weightedPairing O 2 (f - (weightedPairing O 2 f one / weightedPairing O 2 one one) • one) one = 0
      rw [hlin1, div_mul_cancel₀ _ hpos, sub_self]
    · have hc' : weightedPairing O 2 (f - c • one) one = 0 := hc
      rw [hlin1, sub_eq_zero] at hc'
      rw [hc', mul_div_cancel_right₀ _ hpos]

end GL2TF.Quat
