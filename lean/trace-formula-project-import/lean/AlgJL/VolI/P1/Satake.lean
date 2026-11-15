import AlgJL.VolI.P1.HeckeBasis
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Fork copy (algebraic_jl, agent L-B) of `lean/GL2TF/VolI/P1/Satake.lean` at commit 84818d0, trimmed to its algebraic/topological part.
Dropped declarations (8): `cartan_upper_eq_hmat`, `cartan_upper_mk_eq_iff`, `integral_eq_finsum_integer_cosets`, `laurentSwap_involutive`, `satake_coeff_eq`, `satake_transform_well_defined`, `upperRight_mem_K`, `upperRight_val`.
Dropped tagged IDs: `I.satake.thm:satake-transform-well-defined`. -/

/-!
# The Satake isomorphism and the characters of `H(G, K)` (M5a, unit U1)

Lean counterpart of `vol1/ch-1-01-spherical.tex` §§3–4. Owner: L1.

Carriers (D-TARGET, decision L14): `ℂ[X^{±1}, Y^{±1}] = AddMonoidAlgebra ℂ (ℤ × ℤ)` with `X^aY^b = single (a, b) 1`;
`ℂ[T, R^{±1}] = AddMonoidAlgebra ℂ (ℕ × ℤ)` with `T^nR^m = single (n, m) 1`; the swap `s` is `domCongr` of
`AddEquiv.prodComm`; the invariants are the equalizer of `s` and the identity.

The Satake transform is the coset form (D-SATMODEL, decision L14): `𝒮f = ∑_{gK ∈ G/K} f(g) μ(gK)` with
`μ(h(i, j, x)K) = q^{-(i-j)/2} X^iY^j`, a `finsum` over `G ⧸ K` with finite support. Its multiplicativity is the
coset-weight route (`cosetTransform_mul`): every left coset has a representative `y = h(i, j, x)` with
`μ(yx) = μ(y)μ(x)`. The `N(F)/N(𝒪)` sum and the integral form are `satake_transform_well_defined` (b), with
`N(F)/N(𝒪) ≅ F/𝒪` through `x ↦ n(x)`.
-/

open ValuativeRel GL2TF MeasureTheory AddMonoidAlgebra

namespace GL2TF.Local

/-- `T ∈ ℂ[T, R^{±1}]` (local notation). -/
local notation "𝐓" => (AddMonoidAlgebra.single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ))
/-- `R ∈ ℂ[T, R^{±1}]` (local notation). -/
local notation "𝐑" => (AddMonoidAlgebra.single ((0 : ℕ), (1 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ))
/-- `X ∈ ℂ[X^{±1}, Y^{±1}]` (local notation). -/
local notation "𝐗" => (AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℤ × ℤ))
/-- `Y ∈ ℂ[X^{±1}, Y^{±1}]` (local notation). -/
local notation "𝐘" => (AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℤ × ℤ))

/-! ### Item 9: the Laurent algebra, the swap, the invariants -/

section Laurent

/-- The swap `s : ℂ[X^{±1}, Y^{±1}] → ℂ[X^{±1}, Y^{±1}]`, `s(X^aY^b) = X^bY^a`, a `ℂ`-algebra automorphism. -/
@[tf_aux "I.satake.def:laurent-swap"]
noncomputable def laurentSwap : AddMonoidAlgebra ℂ (ℤ × ℤ) ≃ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.domCongr ℂ ℂ AddEquiv.prodComm

/-- The Weyl group invariants `ℂ[X^{±1}, Y^{±1}]^{S₂} = {P : s(P) = P}`, a `ℂ`-subalgebra. -/
@[tf_id "I.satake.def:laurent-weyl-invariants"]
noncomputable def weylInvariants : Subalgebra ℂ (AddMonoidAlgebra ℂ (ℤ × ℤ)) :=
  AlgHom.equalizer (laurentSwap : AddMonoidAlgebra ℂ (ℤ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ))
    (AlgHom.id ℂ (AddMonoidAlgebra ℂ (ℤ × ℤ)))

theorem laurentSwap_single (a b : ℤ) (c : ℂ) : laurentSwap (single (a, b) c) = single (b, a) c := by
  simp [laurentSwap, domCongr_single]

theorem mem_weylInvariants (P : AddMonoidAlgebra ℂ (ℤ × ℤ)) : P ∈ weylInvariants ↔ laurentSwap P = P := Iff.rfl

/-! ### Item 10 (proof plumbing, from the W0 spike `lean/Scratch/L1/Laurent.lean`) -/

/-- `(XY)^m`, `m ∈ ℤ`. -/
noncomputable def laurentXYz (m : ℤ) : AddMonoidAlgebra ℂ (ℤ × ℤ) := single (m, m) 1

theorem laurentXYz_add (m m' : ℤ) : laurentXYz (m + m') = laurentXYz m * laurentXYz m' := by
  rw [laurentXYz, laurentXYz, laurentXYz, single_mul_single, one_mul]; rfl

theorem laurentXYz_zero : laurentXYz 0 = 1 := rfl

theorem laurentXYz_neg_mul (m : ℤ) : laurentXYz (-m) * laurentXYz m = 1 := by
  rw [← laurentXYz_add, neg_add_cancel, laurentXYz_zero]

/-- `(n, m) ↦ (X + Y)^n (XY)^m`. -/
noncomputable def laurentPhiHom : Multiplicative (ℕ × ℤ) →* AddMonoidAlgebra ℂ (ℤ × ℤ) where
  toFun p := (𝐗 + 𝐘) ^ p.toAdd.1 * laurentXYz p.toAdd.2
  map_one' := by simp [laurentXYz_zero]
  map_mul' p p' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_add, laurentXYz_add]
    ring

/-- `φ : ℂ[T, R^{±1}] → ℂ[X^{±1}, Y^{±1}]`, `T ↦ X + Y`, `R ↦ XY`. -/
noncomputable def laurentPhi : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ (ℤ × ℤ)) (ℕ × ℤ) laurentPhiHom

/-- The exponent map `(Fin 2 →₀ ℕ) → ℤ × ℤ`. -/
noncomputable def laurentExpMap : (Fin 2 →₀ ℕ) →+ ℤ × ℤ :=
  ((Nat.castAddMonoidHom ℤ).comp (Finsupp.applyAddHom 0)).prod
    ((Nat.castAddMonoidHom ℤ).comp (Finsupp.applyAddHom 1))

theorem laurentExpMap_injective : Function.Injective laurentExpMap := by
  intro d d' h
  simp only [laurentExpMap, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.applyAddHom_apply, Nat.coe_castAddMonoidHom, Prod.mk.injEq, Nat.cast_inj] at h
  ext i; fin_cases i <;> simp [h.1, h.2]

/-- `ι : ℂ[x₀, x₁] → ℂ[X^{±1}, Y^{±1}]`, `x₀ ↦ X`, `x₁ ↦ Y` (injective). -/
noncomputable def laurentIota : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ laurentExpMap

theorem laurentIota_injective : Function.Injective laurentIota :=
  AddMonoidAlgebra.mapDomain_injective laurentExpMap_injective

theorem laurentIota_X0 : laurentIota (MvPolynomial.X 0) = 𝐗 := by
  simp [laurentIota, MvPolynomial.X, MvPolynomial.monomial, laurentExpMap]

theorem laurentIota_X1 : laurentIota (MvPolynomial.X 1) = 𝐘 := by
  simp [laurentIota, MvPolynomial.X, MvPolynomial.monomial, laurentExpMap]

theorem laurentIota_rename_swap (p : MvPolynomial (Fin 2) ℂ) :
    laurentIota (MvPolynomial.rename (Equiv.swap 0 1) p) = laurentSwap (laurentIota p) := by
  have : laurentIota.comp (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)) =
      (laurentSwap : AddMonoidAlgebra ℂ (ℤ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ)).comp laurentIota := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [laurentIota_X0, laurentIota_X1, laurentSwap_single]
    · simp [laurentIota_X0, laurentIota_X1, laurentSwap_single]
  exact congrArg (· p) this

/-- `ψ : ℂ[x₀, x₁] → ℂ[T, R^{±1}]`, `x₀ ↦ T`, `x₁ ↦ R`. -/
noncomputable def laurentPsi : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℤ) :=
  MvPolynomial.aeval ![𝐓, 𝐑]

theorem esymm_one_fin2 : MvPolynomial.esymm (Fin 2) ℂ 1 = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [MvPolynomial.esymm_one, Fin.sum_univ_two]

theorem esymm_two_fin2 : MvPolynomial.esymm (Fin 2) ℂ 2 = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  rw [MvPolynomial.esymm_eq_sum_subtype]
  rw [Finset.sum_eq_single ⟨Finset.univ, by simp⟩]
  · simp [Fin.prod_univ_two]
  · rintro ⟨s, hs⟩ - hne
    exact absurd (Subtype.ext (Finset.eq_univ_of_card s (by simpa using hs))) hne
  · simp

theorem laurentPhi_psi : laurentPhi.comp laurentPsi =
    laurentIota.comp (MvPolynomial.aeval fun i : Fin 2 => MvPolynomial.esymm (Fin 2) ℂ (i + 1)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [laurentPsi, laurentPhi, laurentPhiHom, esymm_one_fin2, laurentIota_X0, laurentIota_X1, laurentXYz_zero]
  · simp [laurentPsi, laurentPhi, laurentPhiHom, esymm_two_fin2, laurentIota_X0, laurentIota_X1, laurentXYz,
      single_mul_single]

theorem algebraMap_laurent (c : ℂ) : algebraMap ℂ (AddMonoidAlgebra ℂ (ℤ × ℤ)) c = single 0 c := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, smul_single, smul_eq_mul, mul_one]

theorem algebraMap_polyTR (c : ℂ) : algebraMap ℂ (AddMonoidAlgebra ℂ (ℕ × ℤ)) c = single 0 c := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, smul_single, smul_eq_mul, mul_one]

theorem laurentIota_mono (a b : ℕ) (c : ℂ) :
    laurentIota (MvPolynomial.C c * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      single ((a : ℤ), (b : ℤ)) c := by
  rw [map_mul, map_mul, map_pow, map_pow, laurentIota_X0, laurentIota_X1, MvPolynomial.algHom_C,
    algebraMap_laurent, single_pow, single_pow, single_mul_single, single_mul_single]
  simp only [one_pow, mul_one]
  congr 1; ext <;> simp

theorem laurentPsi_mono (a b : ℕ) (c : ℂ) :
    laurentPsi (MvPolynomial.C c * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) = single (a, (b : ℤ)) c := by
  rw [map_mul, map_mul, map_pow, map_pow, MvPolynomial.algHom_C, algebraMap_polyTR]
  simp only [laurentPsi, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [single_pow, single_pow, single_mul_single, single_mul_single]
  simp only [one_pow, mul_one]
  congr 1; ext <;> simp

theorem laurentXYz_mul_single (N : ℤ) (a b : ℤ) (c : ℂ) :
    laurentXYz N * single (a, b) c = single (a + N, b + N) c := by
  rw [laurentXYz, single_mul_single, one_mul]; congr 1; ext <;> simp [add_comm]

theorem exists_shift_laurentIota (f : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    ∃ N : ℕ, ∃ p, laurentXYz N * f = laurentIota p := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N, p, hp⟩ := hf
    obtain ⟨M, r, hr⟩ := hg
    refine ⟨N + M, MvPolynomial.C 1 * MvPolynomial.X 0 ^ M * MvPolynomial.X 1 ^ M * p +
      MvPolynomial.C 1 * MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N * r, ?_⟩
    have hxy : ∀ A : ℕ, laurentIota (MvPolynomial.C 1 * MvPolynomial.X 0 ^ A * MvPolynomial.X 1 ^ A) =
        laurentXYz A := by
      intro A; rw [laurentIota_mono]; rfl
    rw [mul_add, map_add, map_mul laurentIota _ p, map_mul laurentIota _ r, hxy, hxy, ← hp, ← hr, Nat.cast_add,
      laurentXYz_add]
    ring
  | single ab c =>
    obtain ⟨a, b⟩ := ab
    refine ⟨a.natAbs + b.natAbs, MvPolynomial.C c * MvPolynomial.X 0 ^ (a + (a.natAbs + b.natAbs : ℕ)).toNat *
      MvPolynomial.X 1 ^ (b + (a.natAbs + b.natAbs : ℕ)).toNat, ?_⟩
    rw [laurentXYz_mul_single, laurentIota_mono]
    congr 1; ext <;> simp <;>
      (have := neg_abs_le a; have := neg_abs_le b; have := abs_nonneg a; have := abs_nonneg b; omega)

theorem exists_shift_laurentPsi (h : AddMonoidAlgebra ℂ (ℕ × ℤ)) :
    ∃ N : ℕ, ∃ P, single (0, (N : ℤ)) 1 * h = laurentPsi P := by
  induction h using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N, p, hp⟩ := hf
    obtain ⟨M, r, hr⟩ := hg
    refine ⟨N + M, MvPolynomial.C 1 * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ M * p +
      MvPolynomial.C 1 * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ N * r, ?_⟩
    have hR : ∀ A B : ℕ, (single (0, ((A + B : ℕ) : ℤ)) 1 : AddMonoidAlgebra ℂ (ℕ × ℤ)) =
        single (0, (A : ℤ)) 1 * single (0, (B : ℤ)) 1 := by
      intro A B; rw [single_mul_single, one_mul]; congr 1; try (ext <;> simp)
    rw [mul_add, map_add, map_mul laurentPsi _ p, map_mul laurentPsi _ r, laurentPsi_mono, laurentPsi_mono, ← hp,
      ← hr, hR]
    ring
  | single ab c =>
    obtain ⟨n, m⟩ := ab
    refine ⟨m.natAbs, MvPolynomial.C c * MvPolynomial.X 0 ^ n * MvPolynomial.X 1 ^ (m + m.natAbs).toNat, ?_⟩
    rw [laurentPsi_mono, single_mul_single, one_mul]
    congr 1; ext <;> simp <;> (have := neg_abs_le m; have := abs_nonneg m; omega)

theorem perm_fin_two (e : Equiv.Perm (Fin 2)) : e = 1 ∨ e = Equiv.swap 0 1 := by
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have key : ∀ x y : Fin 2, x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
  rcases key _ _ hne with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; ext i; fin_cases i <;> simp [h0, h1]
  · right; ext i; fin_cases i <;> simp [h0, h1]

theorem laurentPhi_single (n : ℕ) (m : ℤ) (c : ℂ) :
    laurentPhi (single (n, m) c) = c • ((𝐗 + 𝐘) ^ n * laurentXYz m) := by
  simp [laurentPhi, laurentPhiHom]

theorem esymm_eval (P : MvPolynomial (Fin 2) ℂ) :
    ((MvPolynomial.esymmAlgHom (Fin 2) ℂ 2 P : MvPolynomial.symmetricSubalgebra (Fin 2) ℂ) :
      MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.esymm (Fin 2) ℂ (i + 1)) P :=
  MvPolynomial.esymmAlgHom_apply P

theorem laurentPhi_injective : Function.Injective laurentPhi := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨N, P, hP⟩ := exists_shift_laurentPsi h
  have h1 : laurentIota (MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.esymm (Fin 2) ℂ (i + 1)) P) = 0 := by
    have := congrArg (· P) laurentPhi_psi
    simp only [AlgHom.comp_apply] at this
    rw [← this, ← hP, map_mul, hh, mul_zero]
  have h2 : MvPolynomial.esymmAlgHom (Fin 2) ℂ 2 P = 0 := by
    apply Subtype.ext
    rw [esymm_eval]
    exact (injective_iff_map_eq_zero _).mp laurentIota_injective _ h1
  have h3 : P = 0 :=
    (injective_iff_map_eq_zero _).mp (MvPolynomial.esymmAlgHom_injective ℂ (by simp)) _ h2
  rw [h3, map_zero] at hP
  have : (single (0, -(N : ℤ)) 1 : AddMonoidAlgebra ℂ (ℕ × ℤ)) * single (0, (N : ℤ)) 1 = 1 := by
    rw [single_mul_single, one_mul]; simp [one_def]; rfl
  rw [← one_mul h, ← this, mul_assoc, hP, mul_zero]

theorem laurentPhi_range : laurentPhi.range = weylInvariants := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    rw [mem_weylInvariants]
    induction h using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single nm c =>
      obtain ⟨n, m⟩ := nm
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at *
      rw [laurentPhi_single, map_smul, map_mul, map_pow, map_add]
      simp only [laurentXYz, laurentSwap_single]
      rw [add_comm (single ((0 : ℤ), (1 : ℤ)) (1 : ℂ))]
  · intro f hf
    rw [mem_weylInvariants] at hf
    obtain ⟨N, p, hp⟩ := exists_shift_laurentIota f
    have hsym : p ∈ MvPolynomial.symmetricSubalgebra (Fin 2) ℂ := by
      intro e
      rcases perm_fin_two e with rfl | rfl
      · simp
      · apply laurentIota_injective
        rw [laurentIota_rename_swap, ← hp, map_mul, hf]
        simp only [laurentXYz, laurentSwap_single]
    obtain ⟨P, hPp⟩ := MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin 2) (n := 2) (by simp) ⟨p, hsym⟩
    have hEP : MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.esymm (Fin 2) ℂ (i + 1)) P = p := by
      rw [← esymm_eval, hPp]
    refine ⟨single (0, -(N : ℤ)) 1 * laurentPsi P, ?_⟩
    have := congrArg (· P) laurentPhi_psi
    simp only [AlgHom.comp_apply] at this
    change laurentPhi (single (0, -(N : ℤ)) 1 * laurentPsi P) = f
    rw [map_mul, this, hEP, ← hp, ← mul_assoc]
    have h0 : laurentPhi (single (0, -(N : ℤ)) 1) = laurentXYz (-(N : ℤ)) := by simp [laurentPhi_single]
    rw [h0, laurentXYz_neg_mul, one_mul]

theorem laurentPhi_T : laurentPhi 𝐓 = 𝐗 + 𝐘 := by
  rw [laurentPhi_single]; simp [laurentXYz_zero]

theorem laurentPhi_R : laurentPhi 𝐑 = 𝐗 * 𝐘 := by
  rw [laurentPhi_single]; simp [laurentXYz, single_mul_single]

theorem laurentPhi_Rinv : laurentPhi (single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)) = single ((-1 : ℤ), (-1 : ℤ)) (1 : ℂ) := by
  rw [laurentPhi_single]; simp [laurentXYz]

/-- The invariants are generated by `X + Y`, `XY`, `(XY)^{-1}`: the `ℂ`-algebra map
`φ : ℂ[T, R^{±1}] → ℂ[X^{±1}, Y^{±1}]`, `T ↦ X + Y`, `R ↦ XY`, exists, is injective, and has image
`ℂ[X^{±1}, Y^{±1}]^{S₂}`; in particular `ℂ[X^{±1}, Y^{±1}]^{S₂} = ℂ[X + Y, XY, (XY)^{-1}]`, and `X + Y`, `XY` are
algebraically independent over `ℂ`. -/
@[tf_id "I.satake.lem:laurent-invariants-generators"]
theorem laurent_invariants_generators :
    (∃ φ : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ),
        φ 𝐓 = 𝐗 + 𝐘 ∧ φ 𝐑 = 𝐗 * 𝐘 ∧ Function.Injective φ ∧ φ.range = weylInvariants) ∧
      Algebra.adjoin ℂ {𝐗 + 𝐘, 𝐗 * 𝐘, single ((-1 : ℤ), (-1 : ℤ)) (1 : ℂ)} = weylInvariants ∧
      AlgebraicIndependent ℂ ![𝐗 + 𝐘, 𝐗 * 𝐘] := by
  refine ⟨⟨laurentPhi, laurentPhi_T, laurentPhi_R, laurentPhi_injective, laurentPhi_range⟩, ?_, ?_⟩
  · have himg : (laurentPhi : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ)) ''
        {(single ((1 : ℕ), (0 : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)),
          single ((0 : ℕ), (1 : ℤ)) (1 : ℂ), single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ)} =
        {𝐗 + 𝐘, 𝐗 * 𝐘, single ((-1 : ℤ), (-1 : ℤ)) (1 : ℂ)} := by
      simp only [Set.image_insert_eq, Set.image_singleton, laurentPhi_T, laurentPhi_R, laurentPhi_Rinv]
    rw [← himg, ← AlgHom.map_adjoin, adjoin_polyTR, Algebra.map_top, laurentPhi_range]
  · rw [AlgebraicIndependent]
    have : MvPolynomial.aeval ![𝐗 + 𝐘, 𝐗 * 𝐘] = laurentPhi.comp polyTRIota := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, polyTRIota_X]
      fin_cases i
      · exact laurentPhi_T.symm
      · exact laurentPhi_R.symm
    rw [this]
    exact laurentPhi_injective.comp polyTRIota_injective

end Laurent

/-! ### Item 11: the Satake transform -/

section Generic

open HeckePair

variable {G : Type*} [Group G] {U : Subgroup G} {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The coset transform `𝒯_μ f = ∑_{gU ∈ G/U} f(g) μ(g)` of a Hecke function `f ∈ H(G, U)` with respect to a weight
`μ : G → A` (B-only; the sum has finite support since `f` is supported on finitely many cosets). -/
@[tf_aux "I.satake.def:coset-transform"]
noncomputable def cosetTransform (μ : G → A) (f : HeckeAlgebra U ℂ) : A :=
  ∑ᶠ c : G ⧸ U, (f : G → ℂ) c.out • μ c.out

theorem apply_out_eq {τ : G → A} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (g : G) :
    τ (Quotient.out (QuotientGroup.mk g : G ⧸ U)) = τ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hτ g u u.2]

theorem support_cosetTransform_term_subset (μ : G → A) (f : HeckeAlgebra U ℂ) :
    Function.support (fun c : G ⧸ U => (f : G → ℂ) c.out • μ c.out) ⊆
      QuotientGroup.mk '' Function.support (f : G → ℂ) := by
  intro c hc
  refine ⟨c.out, fun h => hc ?_, Quotient.out_eq c⟩
  simp [h]

theorem finite_support_cosetTransform_term (μ : G → A) (f : HeckeAlgebra U ℂ) :
    (Function.support (fun c : G ⧸ U => (f : G → ℂ) c.out • μ c.out)).Finite :=
  (finite_cosets f).subset (support_cosetTransform_term_subset μ f)

theorem finsum_coset_translate {τ : G → A} (hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g) (y : G) :
    ∑ᶠ c : G ⧸ U, τ (y * c.out) = ∑ᶠ c : G ⧸ U, τ c.out := by
  calc ∑ᶠ c : G ⧸ U, τ (y * c.out)
      = ∑ᶠ c : G ⧸ U, τ ((MulAction.toPerm y : Equiv.Perm (G ⧸ U)) c).out := by
        refine finsum_congr fun c => ?_
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, apply_out_eq hτ]
        obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
        rw [hu, ← mul_assoc, hτ _ u u.2]
    _ = _ := finsum_comp_equiv (MulAction.toPerm y : Equiv.Perm (G ⧸ U)) (f := fun c : G ⧸ U => τ c.out)

theorem cosetTransform_add (μ : G → A) (f g : HeckeAlgebra U ℂ) :
    cosetTransform μ (f + g) = cosetTransform μ f + cosetTransform μ g := by
  unfold cosetTransform
  rw [← finsum_add_distrib (finite_support_cosetTransform_term μ f) (finite_support_cosetTransform_term μ g)]
  exact finsum_congr fun c => by simp [add_smul]

theorem cosetTransform_smul (μ : G → A) (r : ℂ) (f : HeckeAlgebra U ℂ) :
    cosetTransform μ (r • f) = r • cosetTransform μ f := by
  unfold cosetTransform
  rw [smul_finsum' r (finite_support_cosetTransform_term μ f)]
  exact finsum_congr fun c => by simp [mul_smul]

theorem cosetTransform_one (μ : G → A) (hμ : ∀ g, ∀ u ∈ U, μ (g * u) = μ g) (hμ1 : μ 1 = 1) :
    cosetTransform μ (1 : HeckeAlgebra U ℂ) = 1 := by
  unfold cosetTransform
  rw [finsum_eq_single _ (QuotientGroup.mk 1)]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (1 : G)
    rw [coe_one, hu, one_mul, Set.indicator_of_mem u.2, Pi.one_apply, one_smul, ← one_mul (u : G),
      hμ 1 u u.2, hμ1]
  · intro c hc
    rw [coe_one, Set.indicator_of_notMem, zero_smul]
    intro hmem
    apply hc
    rw [← Quotient.out_eq c]
    exact QuotientGroup.eq.mpr (by simpa using hmem)

/-- Multiplicativity of the coset transform for a right-`U`-invariant weight with good representatives: every
coset has a representative `y` with `μ(yx) = μ(y)μ(x)` for all `x`. -/
theorem cosetTransform_mul (μ : G → A) (hμ : ∀ g, ∀ u ∈ U, μ (g * u) = μ g)
    (hgood : ∀ g : G, ∃ y : G, (y : G ⧸ U) = g ∧ ∀ x, μ (y * x) = μ y * μ x)
    (f₁ f₂ : HeckeAlgebra U ℂ) :
    cosetTransform μ (f₁ * f₂) = cosetTransform μ f₁ * cosetTransform μ f₂ := by
  classical
  set S := (finite_cosets f₁).toFinset with hSdef
  have hS : QuotientGroup.mk '' Function.support (f₁ : G → ℂ) ⊆ (S : Set (G ⧸ U)) := by
    rw [hSdef, Set.Finite.coe_toFinset]
  have h1 : cosetTransform μ (f₁ * f₂) =
      ∑ᶠ c : G ⧸ U, ∑ d ∈ S, convTerm f₁ f₂ c.out d • μ c.out := by
    unfold cosetTransform
    refine finsum_congr fun c => ?_
    rw [coe_mul, conv_eq_sum f₁ f₂ _ hS, Finset.sum_smul]
  have key : ∀ d : G ⧸ U,
      (∑ᶠ c : G ⧸ U, convTerm f₁ f₂ c.out d • μ c.out =
        ((f₁ : G → ℂ) d.out • μ d.out) * cosetTransform μ f₂) ∧
      (Function.support fun c : G ⧸ U => convTerm f₁ f₂ c.out d • μ c.out).Finite := by
    intro d
    obtain ⟨y, hy, hmul⟩ := hgood d.out
    rw [QuotientGroup.out_eq'] at hy
    subst hy
    set τ : G → A := fun g => ((f₁ : G → ℂ) y * (f₂ : G → ℂ) (y⁻¹ * g)) • μ g with hτdef
    have hτ : ∀ g, ∀ u ∈ U, τ (g * u) = τ g := by
      intro g u hu
      simp only [hτdef, ← mul_assoc, apply_mul_right f₂ hu, hμ g u hu]
    have hterm : ∀ c : G ⧸ U, convTerm f₁ f₂ c.out (QuotientGroup.mk y) • μ c.out = τ c.out := by
      intro c; rw [convTerm_mk]
    refine ⟨?_, ?_⟩
    · rw [finsum_congr hterm, ← finsum_coset_translate hτ y]
      have hτy : ∀ c : G ⧸ U, τ (y * c.out) =
          ((f₁ : G → ℂ) y • μ y) * ((f₂ : G → ℂ) c.out • μ c.out) := by
        intro c
        simp only [hτdef, ← mul_assoc, inv_mul_cancel, one_mul, hmul, smul_mul_smul_comm]
      rw [finsum_congr hτy, ← mul_finsum' _ _ (finite_support_cosetTransform_term μ f₂)]
      congr 1
      have hτ' : ∀ g, ∀ u ∈ U, ((f₁ : G → ℂ) (g * u) • μ (g * u)) = (f₁ : G → ℂ) g • μ g := by
        intro g u hu; rw [apply_mul_right f₁ hu, hμ g u hu]
      exact (apply_out_eq (τ := fun g => (f₁ : G → ℂ) g • μ g) hτ' y).symm
    · refine ((finite_cosets f₂).image (fun c => y • c)).subset ?_
      intro c hc
      rw [Function.mem_support, hterm] at hc
      have h2 : (f₂ : G → ℂ) (y⁻¹ * c.out) ≠ 0 := by
        intro h0; apply hc; simp [hτdef, h0]
      refine ⟨QuotientGroup.mk (y⁻¹ * c.out), ⟨_, h2, rfl⟩, ?_⟩
      show y • (QuotientGroup.mk (y⁻¹ * c.out) : G ⧸ U) = c
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul, QuotientGroup.out_eq']
  rw [h1, finsum_sum_comm S _ (fun d _ => (key d).2)]
  simp_rw [fun d => (key d).1]
  rw [← Finset.sum_mul]
  congr 1
  unfold cosetTransform
  refine (finsum_eq_sum_of_support_subset _ ((support_cosetTransform_term_subset μ f₁).trans hS)).symm

end Generic

section SatakeTransform

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNALF F]

/-- `ϖ_F` as an element of `F` (local notation). -/
local notation "ϖ" => ((unif F : 𝒪[F]) : F)
/-- `q^{1/2} ∈ ℂ`, the positive square root (local notation). -/
local notation "√q" => ((Real.sqrt (q F : ℝ) : ℝ) : ℂ)

theorem hmat_mul (i j i' j' : ℤ) (x x' : F) :
    hmat i j x * hmat i' j' x' = hmat (i + i') (j + j') (ϖ ^ i * x' + x * ϖ ^ j') := by
  apply Units.ext
  rw [Units.val_mul, hmat_val, hmat_val, hmat_val, Matrix.mul_fin_two, zpow_add₀ (unif_ne_zero F),
    zpow_add₀ (unif_ne_zero F)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- Every left coset `gK` is `h(i, j, x)K` for some `(i, j) ∈ ℤ × ℤ` and `x ∈ F` (`exists_hmat`, as a statement about
cosets; B-only, it enters the value of `iwasawaExponent`). -/
@[tf_aux "I.satake.lem:iwasawa-exponent-exists"]
theorem exists_hmat_coset (c : GL (Fin 2) F ⧸ 𝐊[F]) :
    ∃ p : ℤ × ℤ, ∃ x : F, c = (hmat p.1 p.2 x : GL (Fin 2) F ⧸ 𝐊[F]) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨α, β, x, h⟩ := exists_hmat g
  exact ⟨(α, β), x, h⟩

/-- The Iwasawa exponent `(i, j)` of a left coset `gK = h(i, j, x)K` (B-only; well defined by `hmat_mk_eq_iff`). -/
@[tf_aux "I.satake.def:iwasawa-exponent"]
noncomputable def iwasawaExponent (c : GL (Fin 2) F ⧸ 𝐊[F]) : ℤ × ℤ := Classical.choose (exists_hmat_coset c)

theorem iwasawaExponent_hmat (i j : ℤ) (x : F) :
    iwasawaExponent (hmat i j x : GL (Fin 2) F ⧸ 𝐊[F]) = (i, j) := by
  obtain ⟨x', hx'⟩ := Classical.choose_spec (exists_hmat_coset (hmat i j x : GL (Fin 2) F ⧸ 𝐊[F]))
  obtain ⟨h1, h2, -⟩ := (hmat_mk_eq_iff _ _ _ _ _ _).mp hx'
  exact Prod.ext h1.symm h2.symm

theorem sqrtq_ne_zero : √q ≠ 0 := by
  have : (0 : ℝ) < q F := by exact_mod_cast residue_card_pos (F := F)
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr this).ne'

/-- The Satake weight `μ(g) = q^{-(i-j)/2} X^iY^j = δ_B(β)^{1/2} X^iY^j` for `gK = h(i, j, x)K` (B-only). -/
@[tf_aux "I.satake.def:satake-weight"]
noncomputable def satakeWeight (g : GL (Fin 2) F) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  single (iwasawaExponent (g : GL (Fin 2) F ⧸ 𝐊[F]))
    (√q ^ ((iwasawaExponent (g : GL (Fin 2) F ⧸ 𝐊[F])).2 - (iwasawaExponent (g : GL (Fin 2) F ⧸ 𝐊[F])).1))

theorem satakeWeight_mul_right (g : GL (Fin 2) F) (u : GL (Fin 2) F) (hu : u ∈ 𝐊[F]) :
    satakeWeight (g * u) = satakeWeight g := by
  simp only [satakeWeight, QuotientGroup.mk_mul_of_mem g hu]

theorem satakeWeight_hmat (i j : ℤ) (x : F) :
    satakeWeight (hmat i j x) = single (i, j) (√q ^ (j - i)) := by
  rw [satakeWeight, iwasawaExponent_hmat]

theorem hmat_zero_zero_zero : (hmat 0 0 0 : GL (Fin 2) F) = 1 := by
  apply Units.ext; rw [hmat_val]; ext a b; fin_cases a <;> fin_cases b <;> simp

theorem satakeWeight_one : satakeWeight (1 : GL (Fin 2) F) = 1 := by
  rw [← hmat_zero_zero_zero, satakeWeight_hmat]
  simp [one_def]
  rfl

/-- Good representatives: `μ(h(i, j, z) g) = μ(h(i, j, z)) μ(g)`. -/
theorem satakeWeight_good (g : GL (Fin 2) F) :
    ∃ y : GL (Fin 2) F, (y : GL (Fin 2) F ⧸ 𝐊[F]) = g ∧
      ∀ x, satakeWeight (y * x) = satakeWeight y * satakeWeight x := by
  obtain ⟨i, j, z, hz⟩ := exists_hmat g
  refine ⟨hmat i j z, hz.symm, fun x => ?_⟩
  obtain ⟨i', j', z', hz'⟩ := exists_hmat x
  have hyx : ((hmat i j z * x : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F]) =
      (hmat (i + i') (j + j') (ϖ ^ i * z' + z * ϖ ^ j') : GL (Fin 2) F ⧸ 𝐊[F]) := by
    rw [show ((hmat i j z * x : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F]) =
        hmat i j z • (x : GL (Fin 2) F ⧸ 𝐊[F]) by rw [MulAction.Quotient.smul_mk, smul_eq_mul],
      hz', MulAction.Quotient.smul_mk, smul_eq_mul, hmat_mul]
  rw [satakeWeight_hmat]
  simp only [satakeWeight, hyx, hz', iwasawaExponent_hmat, single_mul_single]
  congr 1
  rw [← zpow_add₀ (sqrtq_ne_zero (F := F))]
  congr 1; ring

variable (F) in
/-- The Satake transform `𝒮f = ∑_{gK ∈ G/K} f(g) μ(gK) ∈ ℂ[X^{±1}, Y^{±1}]` of `f ∈ H(G, K)`, where
`μ(gK) = q^{-(i-j)/2} X^iY^j` for `gK = h(i, j, x)K` (the diagonal of the upper triangular representative is
`(ϖ^i, ϖ^j)` up to units); a finite sum. -/
@[tf_id "I.satake.def:satake-transform"]
noncomputable def satake (f : sphericalHeckeAlgebra F) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  cosetTransform satakeWeight f

/-! ### Items 12, 13 -/

local notation "nU" => Matrix.GeneralLinearGroup.upperRightHom

variable (F) in
/-- `𝒮(f₁ ∗ f₂) = 𝒮f₁ · 𝒮f₂` and `𝒮(1_K) = 1`: `𝒮` is a `ℂ`-algebra homomorphism `H(G, K) → ℂ[X^{±1}, Y^{±1}]`. -/
@[tf_id "I.satake.thm:satake-transform-multiplicative"]
theorem satake_transform_multiplicative :
    (∀ f₁ f₂ : sphericalHeckeAlgebra F, satake F (f₁ * f₂) = satake F f₁ * satake F f₂) ∧
      satake F (1 : sphericalHeckeAlgebra F) = 1 :=
  ⟨cosetTransform_mul _ (fun g u hu => satakeWeight_mul_right g u hu) satakeWeight_good,
    cosetTransform_one _ (fun g u hu => satakeWeight_mul_right g u hu) satakeWeight_one⟩

variable (F) in
/-- `𝒮` bundled as a `ℂ`-algebra homomorphism (proof plumbing). -/
noncomputable def satakeAlgHom : sphericalHeckeAlgebra F →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) where
  toFun := satake F
  map_one' := (satake_transform_multiplicative F).2
  map_mul' := (satake_transform_multiplicative F).1
  map_zero' := by simp [satake, cosetTransform]
  map_add' := cosetTransform_add _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one r]
    exact (cosetTransform_smul _ r 1).trans (by rw [← satake, (satake_transform_multiplicative F).2])

/-! ### Items 14–17 -/

theorem cartanElement_eq_hmat (a b : ℤ) : cartanElement F a b = hmat a b 0 := by
  apply Units.ext; rw [cartanElement_val, hmat_val]

/-- `𝒮(c_{a,a}) = X^aY^a`. -/
theorem satake_heckeBasis_diag (a : ℤ) : satake F (heckeBasis F a a) = single (a, a) 1 := by
  unfold satake cosetTransform
  rw [finsum_eq_single _ ((cartanElement F a a : GL (Fin 2) F) : GL (Fin 2) F ⧸ 𝐊[F])]
  · rw [heckeBasis_apply_of_mem ((mem_doubleCoset_diag_iff a _).mpr (QuotientGroup.out_eq' _)), one_smul]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul 𝐊[F] (cartanElement F a a)
    rw [hu, satakeWeight_mul_right _ _ u.2, cartanElement_eq_hmat, satakeWeight_hmat, sub_self, zpow_zero]
  · intro c hc
    rw [heckeBasis_apply_of_notMem, zero_smul]
    rwa [mem_doubleCoset_diag_iff, QuotientGroup.out_eq']

theorem sqrtq_mul_self : √q * √q = (q F : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem satake_heckeT : satake F (heckeBasis F 1 0) = √q • (𝐗 + 𝐘) := by
  have : Finite (𝒪[F] ⧸ Ideal.span {unif F ^ 1}) := finite_quot_span_pow 1
  letI := Fintype.ofFinite (𝒪[F] ⧸ Ideal.span {unif F ^ 1})
  have hs0 := sqrtq_ne_zero (F := F)
  unfold satake cosetTransform
  rw [finsum_heckeT satakeWeight (fun g k hk => satakeWeight_mul_right g k hk)]
  simp only [satakeWeight_hmat]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_quot_span_pow, pow_one]
  have e1 : √q ^ ((1 : ℤ) - 0) = √q * 1 := by rw [show ((1 : ℤ) - 0) = 1 by norm_num, zpow_one, mul_one]
  have e2 : (q F) • √q ^ ((0 : ℤ) - 1) = √q * 1 := by
    rw [nsmul_eq_mul, ← sqrtq_mul_self, show ((0 : ℤ) - 1) = -1 by norm_num, zpow_neg_one, mul_one, mul_assoc,
      mul_inv_cancel₀ hs0, mul_one]
  rw [smul_single, e1, e2, smul_add, smul_single, smul_single, smul_eq_mul, add_comm]

variable (F) in
/-- `𝒮(T_ϖ) = q^{1/2}(X + Y)`, `𝒮(R_ϖ) = XY`, `𝒮(R_ϖ^{-1}) = 𝒮(c_{-1,-1}) = X^{-1}Y^{-1}`. -/
@[tf_id "I.satake.thm:satake-generators"]
theorem satake_generators :
    satake F (heckeBasis F 1 0) = √q • (𝐗 + 𝐘) ∧ satake F (heckeBasis F 1 1) = 𝐗 * 𝐘 ∧
      satake F (heckeBasis F (-1) (-1)) = single ((-1 : ℤ), (-1 : ℤ)) (1 : ℂ) :=
  ⟨satake_heckeT, by rw [satake_heckeBasis_diag, single_mul_single, one_mul]; rfl, satake_heckeBasis_diag (-1)⟩

variable (F) in
/-- `𝒮f ∈ ℂ[X^{±1}, Y^{±1}]^{S₂}` for every `f ∈ H(G, K)`. -/
@[tf_id "I.satake.thm:satake-image-invariant"]
theorem satake_image_invariant (f : sphericalHeckeAlgebra F) : satake F f ∈ weylInvariants := by
  obtain ⟨-, hadj, -⟩ := hecke_polynomial F
  obtain ⟨hT, hR, hR'⟩ := satake_generators F
  have hf : f ∈ Algebra.adjoin ℂ
      ({heckeBasis F 1 0, heckeBasis F 1 1, heckeBasis F (-1) (-1)} : Set (sphericalHeckeAlgebra F)) := by
    rw [hadj]; exact Algebra.mem_top
  have hle : Algebra.adjoin ℂ
      ({heckeBasis F 1 0, heckeBasis F 1 1, heckeBasis F (-1) (-1)} : Set (sphericalHeckeAlgebra F)) ≤
        weylInvariants.comap (satakeAlgHom F) := by
    rw [Algebra.adjoin_le_iff]
    rintro g (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subalgebra.mem_comap] <;>
      change satake F _ ∈ weylInvariants <;> rw [mem_weylInvariants]
    · rw [hT, map_smul, map_add, laurentSwap_single, laurentSwap_single, add_comm]
    · rw [hR, map_mul, laurentSwap_single, laurentSwap_single, mul_comm]
    · rw [hR', laurentSwap_single]
  exact hle hf

variable (F) in
/-- The right side of item 16 (proof plumbing). -/
noncomputable def satakeTri (a b : ℤ) : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  √q ^ (a - b) • (single (a, b) 1 + single (b, a) 1 +
    (1 - ((q F : ℂ))⁻¹) • ∑ i ∈ Finset.Ioo b a, single (i, a + b - i) (1 : ℂ))

theorem coeff_satakeTri {a b : ℤ} (hab : b < a) (x y : ℤ) :
    (satakeTri F a b).coeff (x, y) = √q ^ (a - b) *
      (if x + y = a + b ∧ b ≤ x ∧ x ≤ a then (if x = b ∨ x = a then 1 else 1 - ((q F : ℂ))⁻¹) else 0) := by
  simp only [satakeTri, coeff_smul_apply, coeff_add, Finsupp.add_apply, coeff_sum, Finsupp.finset_sum_apply,
    coeff_single, Finsupp.single_apply, Prod.mk.injEq, smul_eq_mul, ite_and, Finset.sum_ite_eq', Finset.mem_Ioo]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem coeff_smul_XY_mul (P : AddMonoidAlgebra ℂ (ℤ × ℤ)) (s : ℂ) (x y : ℤ) :
    ((s • (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ) + single ((0 : ℤ), (1 : ℤ)) (1 : ℂ))) * P).coeff (x, y) =
      s * (P.coeff (x - 1, y) + P.coeff (x, y - 1)) := by
  rw [mul_comm, mul_smul_comm, mul_add, coeff_smul_apply, coeff_add, Finsupp.add_apply, coeff_mul_single_apply,
    coeff_mul_single_apply]
  simp [smul_eq_mul, sub_eq_add_neg, mul_add]

theorem tri_base1 {a b : ℤ} (hab : a = b + 1) (x y : ℤ) :
    (single (b, b) (1 : ℂ) * (√q • (single ((1 : ℤ), (0 : ℤ)) (1 : ℂ) + single ((0 : ℤ), (1 : ℤ)) (1 : ℂ)))).coeff
      (x, y) = (satakeTri F a b).coeff (x, y) := by
  rw [mul_comm, coeff_mul_single_apply, coeff_satakeTri (by omega), show a - b = 1 by omega, zpow_one]
  simp only [coeff_smul_apply, coeff_add, Finsupp.add_apply, coeff_single, Finsupp.single_apply, Prod.mk.injEq,
    smul_eq_mul, Prod.mk_sub_mk, Prod.neg_mk, Prod.mk_add_mk, sub_eq_add_neg, mul_one]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem tri_base2 {a b : ℤ} (hab : a = b + 1 + 1) (x y : ℤ) :
    √q * ((satakeTri F (b + 1) b).coeff (x - 1, y) + (satakeTri F (b + 1) b).coeff (x, y - 1)) =
      (satakeTri F a b).coeff (x, y) + ((q F : ℂ) + 1) * (single (b + 1, b + 1) (1 : ℂ)).coeff (x, y) := by
  have hs0 := sqrtq_ne_zero (F := F)
  rw [coeff_satakeTri (by omega), coeff_satakeTri (by omega), coeff_satakeTri (by omega),
    show b + 1 - b = 1 by ring, show a - b = 2 by omega, zpow_one, zpow_two, coeff_single, Finsupp.single_apply,
    ← sqrtq_mul_self]
  simp only [Prod.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | ring1 | (field_simp; ring1)

theorem tri_step {a b : ℤ} (h : b + 2 ≤ a) (x y : ℤ) :
    √q * ((satakeTri F a b).coeff (x - 1, y) + (satakeTri F a b).coeff (x, y - 1)) =
      (satakeTri F (a + 1) b).coeff (x, y) + (q F : ℂ) * (satakeTri F a (b + 1)).coeff (x, y) := by
  have hs0 := sqrtq_ne_zero (F := F)
  rw [coeff_satakeTri (by omega), coeff_satakeTri (by omega), coeff_satakeTri (by omega),
    coeff_satakeTri (by omega), show a + 1 - b = (a - (b + 1)) + 1 + 1 by ring,
    show a - b = (a - (b + 1)) + 1 by ring]
  simp only [zpow_add₀ hs0, zpow_one]
  rw [← sqrtq_mul_self]
  split_ifs <;> first | (exfalso; omega) | ring1 | (field_simp; ring1)

theorem satake_tri_aux (n : ℕ) : ∀ a b : ℤ, a = b + n + 1 → satake F (heckeBasis F a b) = satakeTri F a b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab
  have hS : ∀ f, (satakeAlgHom F) f = satake F f := fun _ => rfl
  rcases n with _ | _ | k
  · have e : heckeBasis F a b = heckeBasis F b b * heckeBasis F 1 0 := by
      rw [heckeBasis_diag_mul]
      exact congrArg₂ _ (by push_cast at hab; omega) (by ring)
    rw [e, (satake_transform_multiplicative F).1, satake_heckeBasis_diag, (satake_generators F).1]
    apply coeff_injective
    ext ⟨x, y⟩
    exact tri_base1 (by push_cast at hab; omega) x y
  · have hrec := (hecke_recursion F (b + 1) b (by omega)).2.1 (by ring)
    rw [show b + 1 + 1 = a by push_cast at hab; omega] at hrec
    have ih1 := ih 0 (by omega) (b + 1) b (by push_cast; ring)
    apply coeff_injective
    ext ⟨x, y⟩
    have key := congrArg (fun P => P.coeff (x, y)) (congrArg (satakeAlgHom F) hrec)
    simp only [map_mul, map_add, map_smul] at key
    simp only [hS, ih1, (satake_generators F).1, satake_heckeBasis_diag, coeff_add,
      Finsupp.add_apply, coeff_smul_apply, smul_eq_mul, coeff_smul_XY_mul] at key
    rw [tri_base2 (by push_cast at hab; omega) x y] at key
    exact (add_right_cancel key).symm
  · have hrec := (hecke_recursion F (a - 1) b (by push_cast at hab; omega)).1 (by push_cast at hab; omega)
    rw [sub_add_cancel] at hrec
    have ih1 := ih (k + 1) (by omega) (a - 1) b (by push_cast at hab ⊢; omega)
    have ih2 := ih k (by omega) (a - 1) (b + 1) (by push_cast at hab ⊢; omega)
    apply coeff_injective
    ext ⟨x, y⟩
    have key := congrArg (fun P => P.coeff (x, y)) (congrArg (satakeAlgHom F) hrec)
    simp only [map_mul, map_add, map_smul] at key
    simp only [hS, ih1, ih2, (satake_generators F).1, coeff_add,
      Finsupp.add_apply, coeff_smul_apply, smul_eq_mul, coeff_smul_XY_mul] at key
    have hstep := tri_step (F := F) (a := a - 1) (b := b) (by push_cast at hab; omega) x y
    rw [sub_add_cancel] at hstep
    rw [hstep] at key
    exact (add_right_cancel key).symm

variable (F) in
/-- Triangularity: `𝒮(c_{a,a}) = X^aY^a`, and for `a > b`,
`𝒮(c_{a,b}) = q^{(a-b)/2}(X^aY^b + X^bY^a + (1 - q⁻¹) ∑_{b < i < a} X^iY^{a+b-i})`. -/
@[tf_id "I.satake.thm:satake-triangular"]
theorem satake_triangular :
    (∀ a : ℤ, satake F (heckeBasis F a a) = single (a, a) 1) ∧
      ∀ a b : ℤ, b < a → satake F (heckeBasis F a b) =
        √q ^ (a - b) • (single (a, b) 1 + single (b, a) 1 +
          (1 - ((q F : ℂ))⁻¹) • ∑ i ∈ Finset.Ioo b a, single (i, a + b - i) (1 : ℂ)) := by
  refine ⟨satake_heckeBasis_diag, fun a b hab => ?_⟩
  exact satake_tri_aux (a - b - 1).toNat a b (by omega)

/-- Two `ℂ`-algebra maps out of `ℂ[T, R^{±1}]` that agree on `T` and `R` are equal. -/
theorem polyTR_algHom_ext {A : Type*} [Semiring A] [Algebra ℂ A] {f g : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] A}
    (hT : f 𝐓 = g 𝐓) (hR : f 𝐑 = g 𝐑) : f = g := by
  set R' : AddMonoidAlgebra ℂ (ℕ × ℤ) := single ((0 : ℕ), (-1 : ℤ)) (1 : ℂ) with hR'def
  have h1 : 𝐑 * R' = 1 := by rw [hR'def, single_mul_single, one_mul]; rfl
  have h2 : R' * 𝐑 = 1 := by rw [hR'def, single_mul_single, one_mul]; rfl
  have hR' : f R' = g R' := by
    calc f R' = f R' * (g 𝐑 * g R') := by rw [← map_mul, h1, map_one, mul_one]
      _ = (f R' * f 𝐑) * g R' := by rw [hR, mul_assoc]
      _ = g R' := by rw [← map_mul, h2, map_one, one_mul]
  refine AddMonoidAlgebra.algHom_ext (fun nm => ?_) (Subsingleton.elim _ _)
  obtain ⟨n, m⟩ := nm
  have hdecomp : (single (n, m) 1 : AddMonoidAlgebra ℂ (ℕ × ℤ)) = 𝐓 ^ n * single ((0 : ℕ), m) (1 : ℂ) := by
    rw [single_pow, single_mul_single]
    simp only [one_pow, mul_one]
    congr 1; ext <;> simp
  rw [hdecomp, map_mul, map_mul, map_pow, map_pow, hT]
  congr 1
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have : (single ((0 : ℕ), (k : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) = 𝐑 ^ k := by
      rw [single_pow]; simp only [one_pow]; congr 1; ext <;> simp
    rw [this, map_pow, map_pow, hR]
  · have : (single ((0 : ℕ), -(k : ℤ)) (1 : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ)) = R' ^ k := by
      rw [hR'def, single_pow]; simp only [one_pow]; congr 1; ext <;> simp
    rw [this, map_pow, map_pow, hR']

/-- `T^nR^m ↦ s^n T^nR^m` on `ℂ[T, R^{±1}]`. -/
noncomputable def polyScale (s : ℂ) : AddMonoidAlgebra ℂ (ℕ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℤ) :=
  AddMonoidAlgebra.lift ℂ (AddMonoidAlgebra ℂ (ℕ × ℤ)) (ℕ × ℤ)
    { toFun := fun p => single p.toAdd (s ^ p.toAdd.1)
      map_one' := by simp [one_def]
      map_mul' := fun p p' => by
        simp only [toAdd_mul, Prod.fst_add, pow_add, single_mul_single] }

theorem polyScale_single (s : ℂ) (n : ℕ) (m : ℤ) (c : ℂ) :
    polyScale s (single (n, m) c) = single (n, m) (c * s ^ n) := by
  simp [polyScale, smul_single]

theorem polyScale_inv_cancel {s : ℂ} (hs : s ≠ 0) (p : AddMonoidAlgebra ℂ (ℕ × ℤ)) :
    polyScale s (polyScale s⁻¹ p) = p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single nm c =>
    obtain ⟨n, m⟩ := nm
    rw [polyScale_single, polyScale_single, mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, mul_one]

theorem polyScale_cancel_inv {s : ℂ} (hs : s ≠ 0) (p : AddMonoidAlgebra ℂ (ℕ × ℤ)) :
    polyScale s⁻¹ (polyScale s p) = p := by
  simpa using polyScale_inv_cancel (inv_ne_zero hs) p

variable (F) in
/-- The Satake isomorphism: there is a `ℂ`-algebra isomorphism `e : H(G, K) ≅ ℂ[X^{±1}, Y^{±1}]^{S₂}` with
`e(f) = 𝒮f` for all `f`. -/
@[tf_id "I.satake.thm:satake-isomorphism"]
theorem satake_isomorphism :
    ∃ e : sphericalHeckeAlgebra F ≃ₐ[ℂ] weylInvariants,
      ∀ f : sphericalHeckeAlgebra F, (e f : AddMonoidAlgebra ℂ (ℤ × ℤ)) = satake F f := by
  obtain ⟨⟨Θ, hΘT, hΘR⟩, -, -⟩ := hecke_polynomial F
  obtain ⟨⟨φ, hφT, hφR, hφinj, hφrange⟩, -, -⟩ := laurent_invariants_generators
  obtain ⟨hT, hR, -⟩ := satake_generators F
  have hs : √q ≠ 0 := sqrtq_ne_zero
  have hcomp : (satakeAlgHom F).comp Θ.toAlgHom = φ.comp (polyScale √q) := by
    apply polyTR_algHom_ext
    · change satake F (Θ 𝐓) = φ (polyScale √q 𝐓)
      rw [hΘT, hT, polyScale_single, one_mul, pow_one, show (single ((1 : ℕ), (0 : ℤ)) √q : AddMonoidAlgebra ℂ (ℕ × ℤ)) =
        √q • 𝐓 by rw [smul_single, smul_eq_mul, mul_one], map_smul, hφT]
    · change satake F (Θ 𝐑) = φ (polyScale √q 𝐑)
      rw [hΘR, hR, polyScale_single, pow_zero, mul_one, hφR]
  have happ : ∀ p, satake F (Θ p) = φ (polyScale √q p) := fun p => congrArg (· p) hcomp
  let e₀ : sphericalHeckeAlgebra F →ₐ[ℂ] weylInvariants :=
    (satakeAlgHom F).codRestrict weylInvariants (satake_image_invariant F)
  refine ⟨AlgEquiv.ofBijective e₀ ⟨fun f g hfg => ?_, fun w => ?_⟩, fun f => rfl⟩
  · obtain ⟨p, rfl⟩ := Θ.surjective f
    obtain ⟨p', rfl⟩ := Θ.surjective g
    have h : satake F (Θ p) = satake F (Θ p') := congrArg Subtype.val hfg
    rw [happ, happ] at h
    have := congrArg (polyScale √q⁻¹) (hφinj h)
    rw [polyScale_cancel_inv hs, polyScale_cancel_inv hs] at this
    rw [this]
  · obtain ⟨w, hw⟩ := w
    rw [← hφrange] at hw
    obtain ⟨p, rfl⟩ := hw
    refine ⟨Θ (polyScale √q⁻¹ p), Subtype.ext ?_⟩
    change satake F (Θ (polyScale √q⁻¹ p)) = φ p
    rw [happ, polyScale_inv_cancel hs]

/-! ### Item 18: the characters of `H(G, K)` -/

/-- Evaluation `P ↦ P(α, β) = ∑ p_{a,b} α^a β^b` of a Laurent polynomial at `(α, β) ∈ (ℂ^×)²`, a `ℂ`-algebra
homomorphism (B-only). -/
@[tf_aux "I.satake.def:laurent-eval"]
noncomputable def laurentEval (α β : ℂˣ) : AddMonoidAlgebra ℂ (ℤ × ℤ) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ℤ × ℤ)
    { toFun := fun p => ((α ^ p.toAdd.1 * β ^ p.toAdd.2 : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := fun p p' => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, Units.val_mul]
        ring }

theorem laurentEval_single (α β : ℂˣ) (a b : ℤ) (c : ℂ) :
    laurentEval α β (single (a, b) c) = c * ((α ^ a * β ^ b : ℂˣ) : ℂ) := by
  rw [laurentEval, lift_single, smul_eq_mul]
  rfl

theorem laurentEval_swap (α β : ℂˣ) (P : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    laurentEval β α P = laurentEval α β (laurentSwap P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single ab c =>
    obtain ⟨a, b⟩ := ab
    rw [laurentSwap_single, laurentEval_single, laurentEval_single, mul_comm (β ^ a)]

variable (F) in
/-- The characters of `H(G, K)`, with `ω_{α,β}(f) = (𝒮f)(α, β)`:
(a) `ω_{α,β}` is a `ℂ`-algebra homomorphism, `ω_{α,β}(T_ϖ) = q^{1/2}(α + β)`, `ω_{α,β}(R_ϖ) = αβ`;
(b) every `ℂ`-algebra homomorphism `ω : H(G, K) → ℂ` is some `ω_{α,β}`;
(c) `ω_{α,β} = ω_{α',β'}` iff `(α', β') = (α, β)` or `(α', β') = (β, α)`. -/
@[tf_id "I.satake.thm:hecke-characters"]
theorem hecke_characters :
    (∀ α β : ℂˣ, (∃ ω : sphericalHeckeAlgebra F →ₐ[ℂ] ℂ, ∀ f, ω f = laurentEval α β (satake F f)) ∧
        laurentEval α β (satake F (heckeBasis F 1 0)) = √q * ((α : ℂ) + β) ∧
        laurentEval α β (satake F (heckeBasis F 1 1)) = (α : ℂ) * β) ∧
      (∀ ω : sphericalHeckeAlgebra F →ₐ[ℂ] ℂ, ∃ α β : ℂˣ, ∀ f, ω f = laurentEval α β (satake F f)) ∧
      ∀ α β α' β' : ℂˣ, (∀ f, laurentEval α β (satake F f) = laurentEval α' β' (satake F f)) ↔
        ((α', β') = (α, β) ∨ (α', β') = (β, α)) := by
  have hs0 := sqrtq_ne_zero (F := F)
  obtain ⟨hT, hR, hR'⟩ := satake_generators F
  have evT : ∀ α β : ℂˣ, laurentEval α β (satake F (heckeBasis F 1 0)) = √q * ((α : ℂ) + β) := by
    intro α β
    rw [hT, map_smul, map_add, laurentEval_single, laurentEval_single, smul_eq_mul]
    simp
  have evR : ∀ α β : ℂˣ, laurentEval α β (satake F (heckeBasis F 1 1)) = (α : ℂ) * β := by
    intro α β
    rw [hR, map_mul, laurentEval_single, laurentEval_single]
    simp
  have evR' : ∀ α β : ℂˣ, laurentEval α β (satake F (heckeBasis F (-1) (-1))) = ((α : ℂ) * β)⁻¹ := by
    intro α β
    rw [hR', laurentEval_single]
    simp
    ring
  obtain ⟨-, hadj, -⟩ := hecke_polynomial F
  obtain ⟨-, hRR', -⟩ := hecke_central_shift F
  refine ⟨fun α β => ⟨⟨(laurentEval α β).comp (satakeAlgHom F), fun f => rfl⟩, evT α β, evR α β⟩, fun ω => ?_,
    fun α β α' β' => ⟨fun h => ?_, fun h => ?_⟩⟩
  · -- (b)
    set e₁ := ω (heckeBasis F 1 0) / √q with he₁
    set e₂ := ω (heckeBasis F 1 1) with he₂
    have hinv : e₂ * ω (heckeBasis F (-1) (-1)) = 1 := by rw [he₂, ← map_mul, hRR', map_one]
    have he₂0 : e₂ ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    set s := (e₁ ^ 2 - 4 * e₂) ^ ((2 : ℕ)⁻¹ : ℂ) with hs
    have hs2 : s ^ 2 = e₁ ^ 2 - 4 * e₂ := by rw [hs]; exact Complex.cpow_nat_inv_pow _ two_ne_zero
    have hsum : (e₁ + s) / 2 + (e₁ - s) / 2 = e₁ := by ring
    have hprod : (e₁ + s) / 2 * ((e₁ - s) / 2) = e₂ := by
      have : (e₁ + s) / 2 * ((e₁ - s) / 2) = (e₁ ^ 2 - s ^ 2) / 4 := by ring
      rw [this, hs2]; ring
    have hα0 : (e₁ + s) / 2 ≠ 0 := fun h => he₂0 (by rw [← hprod, h, zero_mul])
    have hβ0 : (e₁ - s) / 2 ≠ 0 := fun h => he₂0 (by rw [← hprod, h, mul_zero])
    refine ⟨Units.mk0 _ hα0, Units.mk0 _ hβ0, fun f => ?_⟩
    have heq : ω = (laurentEval (Units.mk0 _ hα0) (Units.mk0 _ hβ0)).comp (satakeAlgHom F) := by
      refine AlgHom.ext_of_adjoin_eq_top hadj fun x hx => ?_
      rcases hx with rfl | rfl | rfl
      · change ω (heckeBasis F 1 0) = laurentEval _ _ (satake F (heckeBasis F 1 0))
        rw [evT, Units.val_mk0, Units.val_mk0, hsum, he₁, mul_div_cancel₀ _ hs0]
      · change ω (heckeBasis F 1 1) = laurentEval _ _ (satake F (heckeBasis F 1 1))
        rw [evR, Units.val_mk0, Units.val_mk0, hprod]
      · change ω (heckeBasis F (-1) (-1)) = laurentEval _ _ (satake F (heckeBasis F (-1) (-1)))
        rw [evR', Units.val_mk0, Units.val_mk0, hprod]
        exact (eq_inv_of_mul_eq_one_right hinv)
    rw [heq]
    rfl
  · -- (c) ⇒
    have h1 : (α : ℂ) + β = α' + β' := by
      have := h (heckeBasis F 1 0)
      rw [evT, evT] at this
      exact mul_left_cancel₀ hs0 this
    have h2 : (α : ℂ) * β = α' * β' := by
      have := h (heckeBasis F 1 1)
      rwa [evR, evR] at this
    have hq : ((α' : ℂ) - α) * ((α' : ℂ) - β) = 0 := by linear_combination (-(α' : ℂ)) * h1 + h2
    rcases mul_eq_zero.mp hq with h3 | h3
    · left
      have ha : (α' : ℂ) = α := sub_eq_zero.mp h3
      have hb : (β' : ℂ) = β := by linear_combination -h1 - ha
      rw [Units.ext ha, Units.ext hb]
    · right
      have ha : (α' : ℂ) = β := sub_eq_zero.mp h3
      have hb : (β' : ℂ) = α := by linear_combination -h1 - ha
      rw [Units.ext ha, Units.ext hb]
  · -- (c) ⇐
    intro f
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2, laurentEval_swap, (mem_weylInvariants _).mp (satake_image_invariant F f)]

end SatakeTransform

end GL2TF.Local
