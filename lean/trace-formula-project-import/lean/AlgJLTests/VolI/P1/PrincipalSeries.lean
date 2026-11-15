import AlgJL.VolI.P1.PrincipalSeries

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TFTests/VolI/P1/PrincipalSeries.lean` at commit 84818d0. Dropped tests of stripped declarations (0): none. -/


/-!
# Tests for `GL2TF.VolI.P1.PrincipalSeries`

Named tests at `F = ℚ_[3]` (PLAN.md §2.3): the quasi-characters `χ₁ = |·|` and `χ₂ = 1` (the data of the
Gindikin–Karpelevich witness, `GL2TFTests.VolI.P1.Intertwining`), `δ_B^{1/2}`, `π_χ`, `f°_χ`.
-/

open Matrix Matrix.GeneralLinearGroup ValuativeRel GL2TF GL2TF.Local

namespace GL2TFTests

/-- `x ↦ |x|_3` as a homomorphism `ℚ₃^× → ℂ^×`. -/
noncomputable def absCharHom : ℚ_[3]ˣ →* ℂˣ where
  toFun x := Units.mk0 ((‖(x : ℚ_[3])‖ : ℝ) : ℂ) (by simp)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp)

/-- The quasi-character `χ₁ = |·|_3` of `ℚ₃^×` (`γ = χ₁(3) = 1/3`). -/
noncomputable def gkAbsChar : QuasiChar ℚ_[3] :=
  ⟨absCharHom, Units.continuous_iff.mpr
    ⟨show Continuous (fun x : ℚ_[3]ˣ ↦ ((‖(x : ℚ_[3])‖ : ℝ) : ℂ)) from
        Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val),
      show Continuous (fun x : ℚ_[3]ˣ ↦ (((‖(x : ℚ_[3])‖ : ℝ) : ℂ))⁻¹) from
        (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)).inv₀ (fun x ↦ by simp)⟩⟩

/-- The trivial quasi-character `χ₂ = 1` of `ℚ₃^×`. -/
noncomputable def gkTrivChar : QuasiChar ℚ_[3] := ⟨1, continuous_const⟩

/-- `I.smooth.def:quasi-character-coe`: `χ₁(x) = |x|_3`. -/
theorem gkAbsChar_apply (x : ℚ_[3]ˣ) : gkAbsChar x = ((‖(x : ℚ_[3])‖ : ℝ) : ℂ) := rfl

/-- `I.smooth.def:quasi-character-coe`: the instance constant itself, applied explicitly (not unfolded). -/
theorem quasiChar_instCoeFun_apply (x : ℚ_[3]ˣ) :
    @CoeFun.coe _ _ (QuasiChar.instCoeFun ℚ_[3]) gkAbsChar x = ((‖(x : ℚ_[3])‖ : ℝ) : ℂ) := rfl

/-- `|·|_3` is unramified. -/
theorem gkAbsChar_unramified : gkAbsChar.IsUnramified := fun u ↦ by
  show ((‖((u : 𝒪[ℚ_[3]]) : ℚ_[3])‖ : ℝ) : ℂ) = 1
  rw [← normAbs_padic, (normAbs_uniformizer ℚ_[3]).2.1 u, Complex.ofReal_one]

/-- The trivial quasi-character is unramified. -/
theorem gkTrivChar_unramified : gkTrivChar.IsUnramified := fun _ ↦ rfl

/-- `γ = χ₁(ϖ) χ₂(ϖ)⁻¹ = 1/3` (tests `unifUnit`). -/
theorem gk_gamma : gkAbsChar (unifUnit ℚ_[3]) * (gkTrivChar (unifUnit ℚ_[3]))⁻¹ = 1 / 3 := by
  have h1 : gkAbsChar (unifUnit ℚ_[3]) = ((3 : ℂ))⁻¹ := by
    show ((‖((unif ℚ_[3] : 𝒪[ℚ_[3]]) : ℚ_[3])‖ : ℝ) : ℂ) = _
    rw [← normAbs_padic, (normAbs_uniformizer ℚ_[3]).1, q_padic]
    push_cast
    rfl
  have h2 : gkTrivChar (unifUnit ℚ_[3]) = 1 := rfl
  rw [h1, h2]
  norm_num

/-- `δ_B^{1/2}(diag(1, 1)) = 1`. -/
theorem deltaHalf_one_padic : deltaHalf (1 : ℚ_[3]ˣ) 1 = 1 := by
  simp [deltaHalf, normAbs_one]

/-- `π_χ` is right translation. -/
theorem psRep_padic_apply (h g : GL (Fin 2) ℚ_[3]) (f : padicPrincipalSeries gkAbsChar gkTrivChar) :
    (psRep gkAbsChar gkTrivChar h f).1 g = f.1 (g * h) :=
  rfl

/-- `f°_χ ∈ I(χ)` for `χ = (|·|, 1)` at `ℚ_[3]`. -/
theorem spherical_vector_mem :
    sphericalVector gkAbsChar gkTrivChar ∈ padicPrincipalSeries gkAbsChar gkTrivChar :=
  ((principal_series_spherical gkAbsChar gkTrivChar).1 gkAbsChar_unramified gkTrivChar_unramified).1

/-- `f°_χ(1) = 1` for `χ = (|·|, 1)` at `ℚ_[3]` (support of the Gindikin–Karpelevich witness). -/
theorem spherical_vector_ne_zero : sphericalVector gkAbsChar gkTrivChar 1 = 1 :=
  ((principal_series_spherical gkAbsChar gkTrivChar).1 gkAbsChar_unramified gkTrivChar_unramified).2.2.1

/-- `dim I(χ)^K = 1` for `χ = (|·|, 1)` at `ℚ_[3]`. -/
theorem principal_series_spherical_dim :
    Module.finrank ℂ (fixedVectors (psRep gkAbsChar gkTrivChar) 𝐊[ℚ_[3]]) = 1 :=
  ((principal_series_spherical gkAbsChar gkTrivChar).1 gkAbsChar_unramified gkTrivChar_unramified).2.2.2.2

/-! ### A ramified quasi-character (negative control for `I.smooth.thm:principal-series-spherical` (b); L23, F1 m-4) -/

/-- The unit part `x 3^{-v(x)}` of `x ∈ ℚ₃^×` (test helper). -/
noncomputable def ramUnitPart (x : ℚ_[3]ˣ) : ℚ_[3] := (x : ℚ_[3]) * (3 : ℚ_[3]) ^ (-(x : ℚ_[3]).valuation)

theorem norm_ramUnitPart (x : ℚ_[3]ˣ) : ‖ramUnitPart x‖ = 1 := by
  have h3 : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by exact_mod_cast Padic.norm_p (p := 3)
  rw [ramUnitPart, norm_mul, norm_zpow, h3, Padic.norm_eq_zpow_neg_valuation x.ne_zero, ← mul_zpow]
  push_cast
  norm_num

theorem valuation_eq_zero_of_norm {x : ℚ_[3]} (hx0 : x ≠ 0) (hn : ‖x‖ = 1) : x.valuation = 0 := by
  have := Padic.norm_eq_zpow_neg_valuation hx0
  rw [hn] at this
  have h := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1)
    (show (3 : ℝ) ^ (0 : ℤ) = (3 : ℝ) ^ (-x.valuation) by rw [zpow_zero]; exact_mod_cast this)
  omega

theorem ramUnitPart_mul (x y : ℚ_[3]ˣ) : ramUnitPart (x * y) = ramUnitPart x * ramUnitPart y := by
  simp only [ramUnitPart, Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, neg_add,
    zpow_add₀ (by norm_num : (3 : ℚ_[3]) ≠ 0)]
  ring

/-- The unit part as an element of `ℤ₃` (test helper). -/
noncomputable def ramUnitInt (x : ℚ_[3]ˣ) : ℤ_[3] := ⟨ramUnitPart x, (norm_ramUnitPart x).le⟩

/-- `±1` according to `a = 1` in `ℤ/3` (test helper). -/
def ramSign (a : ZMod 3) : ℤˣ := if a = 1 then 1 else -1

theorem ramSign_mul : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → ramSign (a * b) = ramSign a * ramSign b := by decide

theorem toZMod_ramUnitInt_ne_zero (x : ℚ_[3]ˣ) : PadicInt.toZMod (ramUnitInt x) ≠ 0 := by
  intro h
  have : ramUnitInt x ∈ IsLocalRing.maximalIdeal ℤ_[3] := by rw [← PadicInt.ker_toZMod]; exact h
  have h2 := PadicInt.mem_nonunits.mp this
  have h1 : ‖ramUnitInt x‖ = 1 := norm_ramUnitPart x
  linarith

/-- `x ↦ ±1` according to the residue of the unit part of `x` (test helper). -/
noncomputable def ramSignHom : ℚ_[3]ˣ →* ℤˣ where
  toFun x := ramSign (PadicInt.toZMod (ramUnitInt x))
  map_one' := by
    have : ramUnitInt 1 = 1 := Subtype.ext (by simp [ramUnitInt, ramUnitPart, Padic.valuation_one])
    rw [this, map_one]; rfl
  map_mul' x y := by
    have : ramUnitInt (x * y) = ramUnitInt x * ramUnitInt y := Subtype.ext (ramUnitPart_mul x y)
    rw [this, map_mul]
    exact ramSign_mul _ _ (toZMod_ramUnitInt_ne_zero x) (toZMod_ramUnitInt_ne_zero y)

theorem ramSignHom_eq_one {x : ℚ_[3]ˣ} (hx : ‖(x : ℚ_[3]) - 1‖ < 1) : ramSignHom x = 1 := by
  have hn : ‖(x : ℚ_[3])‖ = 1 := by
    have h1 := Padic.nonarchimedean ((x : ℚ_[3]) - 1) 1
    have h2 := Padic.nonarchimedean (1 - (x : ℚ_[3])) (x : ℚ_[3])
    rw [sub_add_cancel, norm_one] at h1
    rw [sub_add_cancel, norm_one, norm_sub_rev] at h2
    have h1' : ‖(x : ℚ_[3])‖ ≤ 1 := h1.trans (max_le hx.le le_rfl)
    rcases h1'.lt_or_eq with h | h
    · exact absurd (h2.trans_lt (max_lt hx h)) (lt_irrefl 1)
    · exact h
  have hv : (x : ℚ_[3]).valuation = 0 := valuation_eq_zero_of_norm x.ne_zero hn
  have hu : ramUnitInt x - 1 ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    refine PadicInt.mem_nonunits.mpr ?_
    show ‖ramUnitPart x - 1‖ < 1
    rwa [ramUnitPart, hv, neg_zero, zpow_zero, mul_one]
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hu
  show ramSign _ = 1
  rw [hu]; rfl

/-- A ramified quasi-character of `ℚ₃^×`: `x ↦ ±1` by the residue of its unit part (`χ(−1) = −1`). -/
noncomputable def gkRamChar : QuasiChar ℚ_[3] :=
  ⟨(Units.map (Int.castRingHom ℂ).toMonoidHom).comp ramSignHom, by
    refine continuous_of_continuousAt_one _ ?_
    have hU : {x : ℚ_[3]ˣ | ‖(x : ℚ_[3]) - 1‖ < 1} ∈ nhds (1 : ℚ_[3]ˣ) :=
      (isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const).mem_nhds
        (by simp)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr (Filter.eventually_of_mem hU fun x hx ↦ ?_)
    show (1 : ℂˣ) = Units.map _ (ramSignHom x)
    rw [ramSignHom_eq_one hx, map_one]⟩

/-- `gkRamChar` is ramified: its value at the unit `−1 ∈ 𝒪^×` is `−1`. -/
theorem gkRamChar_ramified : ¬ gkRamChar.IsUnramified := by
  intro h
  have h1 := h (-1)
  have hv : ramUnitInt (Units.map (𝒪[ℚ_[3]]).subtype.toMonoidHom (-1)) = -1 :=
    Subtype.ext (by
      show ramUnitPart _ = -1
      rw [ramUnitPart, valuation_eq_zero_of_norm (by simp) (by simp)]
      simp)
  change (((Int.castRingHom ℂ) (ramSign (PadicInt.toZMod (ramUnitInt _)) : ℤ)) : ℂ) = 1 at h1
  rw [hv, map_neg, map_one] at h1
  have : ramSign (-1 : ZMod 3) = -1 := by decide
  rw [this] at h1
  norm_num at h1

/-- Negative control for (b): for the ramified `χ = (gkRamChar, 1)` at `ℚ_[3]`, `I(χ)^K = 0`. -/
theorem principal_series_spherical_ramified :
    fixedVectors (psRep gkRamChar gkTrivChar) 𝐊[ℚ_[3]] = ⊥ :=
  (principal_series_spherical gkRamChar gkTrivChar).2 fun h ↦ gkRamChar_ramified h.1

end GL2TFTests
