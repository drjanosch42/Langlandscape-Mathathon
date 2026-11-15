import AlgJL.VolIII.Brandt.HeckeLocal
import AlgJL.VolIII.Brandt.BrandtInstances

/-!
# Exit witnesses and supports of Q3 (R2d; `registry/exits.yaml`, `docs/audits/Q3-G1.md` §4–5)

Exits `III.brandt.thm:hecke-commutative` (item 33) and `III.brandt.thm:brandt-eq-hecke` (item 39). Witnesses are closed
theorems whose value applies the exit to all its binders; supports certify that the data are not degenerate.

Data (G1 condition C1): Pizer's maximal order `O₁₁ ⊆ (−1, −11)_ℚ` (`q3OrderD11`, `h = 2`), model (c) over `ℂ` with `s₀ = i`
(`q3SplitD11`), Q2's explicit level-2 structure on `O₁₁` (`q3LevelD11`, Eichler order of level `DM = 22`) and the weight-2
class indicator `q3FormD22` of the class of `1` in `X(O₁₁(2))` (a function, so that it is itself an argument of the exit;
its membership in `M_2` is `q3FormD22_mem`). `hecke-commutative` is applied at `m = 3`, `n = 9` (the same prime:
recursion part), `brandt-eq-hecke` at `n = 2` (`B(2) = (1 2; 3 0)`, item 45).
-/

set_option autoImplicit false

namespace GL2TFTests

open GL2TF GL2TF.Quat MvPolynomial

/-- Datum of `III.brandt.thm:brandt-eq-hecke`: Pizer's order `O₁₁ = ℤ(1+j)/2 + ℤ(i+k)/2 + ℤj + ℤk` of `(−1, −11)_ℚ`. -/
noncomputable def q3OrderD11 : QOrder (-1) (-11) := pizerOrderI (-11) (by norm_num)

/-- Model (c) over `ℂ` with `s₀ = i`: `i ↦ diag(i, −i)`, `j ↦ (0 −11; 1 0)`. -/
noncomputable def q3SplitD11 : Splitting ℂ (-1) (-11) :=
  standardSplitting ℂ (-1) (-11) Complex.I (by simp [Complex.I_sq])

/-- Q2's explicit level-2 structure `φ₂ : O₁₁ → M₂(ℤ/2)` (`docs/sprints/Q2-plan.md` item 63). -/
noncomputable def q3LevelD11 : LevelStructure q3OrderD11 2 :=
  Inst.level11 2 Inst.X2 Inst.X2_table Inst.X2_one Inst.X2_surj

/-- `O₁₁` is maximal (Q2 item 62). -/
theorem q3OrderD11_isMaximal : IsMaximalOrder q3OrderD11 := eichler_mass_instance_d11.2.1.1

/-- `O₁₁` as a maximal order. -/
noncomputable def q3MaxOrderD11 : MaxOrder (-1) (-11) := ⟨q3OrderD11, q3OrderD11_isMaximal⟩

open scoped Classical in
/-- Datum of `III.brandt.thm:hecke-commutative`: the weight-2 class indicator `x ↦ 1` if `[x] = [1]` in `X(O₁₁(2))`,
else `0` (with values in `V_0(ℂ) = ℂ`). -/
noncomputable def q3FormD22 : (BHat (-1) (-11))ˣ → symPowerModule ℂ (2 - 2) := fun x =>
  ⟨C (if classOf (eichlerOrder q3LevelD11) x = classOf (eichlerOrder q3LevelD11) 1 then 1 else 0),
    isHomogeneous_C _ _⟩

/-- `[ι(γ) x u] = [x]` (B-only `classOf` is the double coset map). -/
theorem classOf_mul_mul {a b : ℤ} (O : QOrder a b) (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ)
    (hu : u ∈ orderCompletionUnits O) :
    classOf O (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf O x := by
  unfold classOf
  exact (DoubleCoset.eq.mpr ⟨_, MonoidHom.mem_range.mpr ⟨γ, rfl⟩, u, hu, rfl⟩).symm

/-- `q3FormD22 ∈ M_2(O₁₁(2); s)`: a function constant on classes is a weight-2 form (`ρ_2^s` is trivial on `V_0`). -/
theorem q3FormD22_mem : q3FormD22 ∈ quatForms (eichlerOrder q3LevelD11) q3SplitD11 2 := by
  intro γ x u hu
  have e : q3FormD22 (Units.map (finEmbed (-1) (-11)).toMonoidHom γ * x * u) = q3FormD22 x := by
    apply Subtype.ext
    simp only [q3FormD22]
    rw [classOf_mul_mul _ γ x u hu]
  rw [e]
  apply Subtype.ext
  simp [q3FormD22, splitRep, symPowerAction, LinearMap.restrict_apply]

/-! ## `III.brandt.thm:hecke-commutative` -/

theorem coprime_three_22 : Nat.Coprime 3 (11 * 2) := by norm_num
theorem coprime_nine_22 : Nat.Coprime 9 (11 * 2) := by norm_num

/-- **Exit witness** (`III.brandt.thm:hecke-commutative`, Q3 G1 C1): `T_3 T_9 = T_9 T_3` on the class indicator
`q3FormD22 ∈ M_2(O₁₁(2); s)` (level `DM = 22`, `m = 3`, `n = 9`). The order is written through the maximal-order binder,
`O₀ := q3MaxOrderD11`, exactly as in the exit's conclusion (`eichlerOrder (O := O₀.1) φ`; T-m7g3-5; Q3-G2 §5). -/
theorem hecke_commutative_witness :
    heckeOperator (eichlerOrder (O := q3MaxOrderD11.1) q3LevelD11) 3
        (heckeOperator (eichlerOrder (O := q3MaxOrderD11.1) q3LevelD11) 9 q3FormD22) =
      heckeOperator (eichlerOrder (O := q3MaxOrderD11.1) q3LevelD11) 9
        (heckeOperator (eichlerOrder (O := q3MaxOrderD11.1) q3LevelD11) 3 q3FormD22) :=
  hecke_commutative q3MaxOrderD11 eichler_mass_instance_d11.1 q3LevelD11 q3SplitD11 2 3 9 coprime_three_22
    coprime_nine_22 q3FormD22 q3FormD22_mem

/-- `O₁₁(2) ⊆ O₁₁` gives `Ô₁₁(2)^× ≤ Ô₁₁^×`. -/
theorem q3_units_le : orderCompletionUnits (eichlerOrder q3LevelD11) ≤ orderCompletionUnits q3OrderD11 := by
  have hle : latticeCompletion (Subalgebra.toSubmodule (eichlerOrder q3LevelD11).toSubalgebra) ≤
      latticeCompletion (Subalgebra.toSubmodule q3OrderD11.toSubalgebra) :=
    Submodule.span_mono (Set.image_mono (eichlerSubalgebra_le q3LevelD11))
  exact fun u hu => ⟨hle hu.1, hle hu.2⟩

/-- **Support** (`III.brandt.thm:hecke-commutative`): the class indicator is not constant (Q2: `X(O₁₁)` has a second
class, and `O₁₁(2) ⊆ O₁₁`), so the witness is not a statement about a multiple of the constant form. -/
theorem q3FormD22_nonconstant : ∃ x, q3FormD22 x ≠ q3FormD22 1 := by
  obtain ⟨x, hx, -⟩ := eichler_mass_instance_d11.2.2.1.2.2.2
  refine ⟨x, fun h => hx ?_⟩
  have h' := congrArg (fun v : symPowerModule ℂ (2 - 2) => (v : MvPolynomial (Fin 2) ℂ)) h
  simp only [q3FormD22] at h'
  by_cases hc : classOf (eichlerOrder q3LevelD11) x = classOf (eichlerOrder q3LevelD11) 1
  · obtain ⟨g, hg, k, hk, hgk⟩ := DoubleCoset.eq.mp hc
    exact DoubleCoset.eq.mpr ⟨g, hg, k, q3_units_le hk, hgk⟩
  · simp only [hc, ↓reduceIte] at h'
    exact absurd (C_injective (Fin 2) ℂ h') zero_ne_one

/-! ## `III.brandt.thm:brandt-eq-hecke` -/

/-- **Exit witness** (`III.brandt.thm:brandt-eq-hecke`, Q3 G1 C1): the whole three-clause conclusion at `K = ℂ`,
`(a, b) = (−1, −11)`, `O = O₁₁`, `s = q3SplitD11`, `n = 2`. -/
theorem brandt_eq_hecke_witness :
    (∀ f ∈ quatForms q3OrderD11 q3SplitD11 2, ∀ c : classSet q3OrderD11,
      heckeOperator q3OrderD11 2 f (Quotient.out c) =
        ∑ᶠ c' : classSet q3OrderD11, (brandtMatrix q3OrderD11 2 c c' : ℂ) • f (Quotient.out c')) ∧
    (∀ c c' : classSet q3OrderD11,
      Nat.card (classStabilizer (orderCompletionUnits q3OrderD11) (Quotient.out c')) * brandtMatrix q3OrderD11 2 c c' =
        Nat.card {γ : (QuatAlg ℚ (-1) (-11))ˣ //
          (finiteIdeleLattice q3OrderD11 (Quotient.out c')).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ (-1) (-11))) ≤
              finiteIdeleLattice q3OrderD11 (Quotient.out c) ∧
            nrd (γ : QuatAlg ℚ (-1) (-11)) = 2 * normWeight (Quotient.out c') / normWeight (Quotient.out c)}) ∧
    (∀ (c c' : classSet q3OrderD11) (x : (BHat (-1) (-11))ˣ), classOf q3OrderD11 x = c →
      brandtMatrix q3OrderD11 2 c c' = Nat.card {q : (BHat (-1) (-11))ˣ ⧸ orderCompletionUnits q3OrderD11 //
        ∃ y ∈ normNSet q3OrderD11 2, (y : (BHat (-1) (-11))ˣ ⧸ orderCompletionUnits q3OrderD11) = q ∧
          classOf q3OrderD11 (x * y) = c'}) :=
  brandt_eq_hecke (by norm_num) (by norm_num) q3OrderD11 q3SplitD11 2 (by norm_num)

/-- **Support** (`III.brandt.thm:brandt-eq-hecke`): `X(O₁₁)` has two classes (Q2 item 62), so `B(2)` is a `2 × 2` matrix. -/
theorem q3OrderD11_classSet_card : Nat.card (classSet q3OrderD11) = 2 :=
  eichler_mass_instance_d11.2.2.1.1

/-- **Support** (`III.brandt.thm:brandt-eq-hecke`): item 45 (`III.brandt.ex:brandt-d11`) at `O₁₁`: stabilizer orders
`4, 6`, `B(1) = I`, `B(2) = (1 2; 3 0)`, `tr B(3) = 3`, `det B(3) = −4`; so clause (b) of the witness is a statement about
non-zero counts. -/
theorem q3_brandt_d11_support :
    ∃ c₁ c₂ : classSet q3OrderD11, c₁ ≠ c₂ ∧ (∀ c, c = c₁ ∨ c = c₂) ∧
      Nat.card (classStabilizer (orderCompletionUnits q3OrderD11) (Quotient.out c₁)) = 4 ∧
      Nat.card (classStabilizer (orderCompletionUnits q3OrderD11) (Quotient.out c₂)) = 6 ∧
      (∀ c, brandtMatrix q3OrderD11 1 c c = 1) ∧
      (∀ c c', c ≠ c' → brandtMatrix q3OrderD11 1 c c' = 0) ∧
      brandtMatrix q3OrderD11 2 c₁ c₁ = 1 ∧ brandtMatrix q3OrderD11 2 c₁ c₂ = 2 ∧
      brandtMatrix q3OrderD11 2 c₂ c₁ = 3 ∧ brandtMatrix q3OrderD11 2 c₂ c₂ = 0 ∧
      (brandtMatrix q3OrderD11 3 c₁ c₁ : ℤ) + brandtMatrix q3OrderD11 3 c₂ c₂ = 3 ∧
      (brandtMatrix q3OrderD11 3 c₁ c₁ : ℤ) * brandtMatrix q3OrderD11 3 c₂ c₂ -
        (brandtMatrix q3OrderD11 3 c₁ c₂ : ℤ) * brandtMatrix q3OrderD11 3 c₂ c₁ = -4 :=
  brandt_d11

end GL2TFTests
