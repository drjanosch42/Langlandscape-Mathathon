import AlgJL.Meta.Tag
import AlgJL.VolIII.P1.Normalization
import AlgJL.VolIII.P1.Boundary
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The formula-level Jacquet–Langlands identity (Q1, unit U5, items 38–43)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §6 (item 38, last statement) and §7 (`sec:ef-identity`). Owner: L2.
Plan `docs/sprints/Q1-plan.md` §1.2 §6–§7 (user Q1-A, Q1-B, Q1-C).

* Item 38 `lefschetz_es_boundary_split`: `Λ^{ES}(N, k, n; F) = −2A₁ − 2A₂^E(F) − 2A₃ − Ẽis(N, k, n)`.
* Item 39 `jl_formula_identity` (**exit**, Eichler form, Q1-A): for squarefree `D` with `ω(D)` odd, `(D, M) = 1`, `k, n ≥ 1`
  and any `F : ℤ → ℚ`: `E^𝔹(D, M, k, n; F) = −½ Σ_{d ∣ D} (−2)^{ω(D/d)} Λ^{ES}(dM, k, n; F_d)`, `F_d = F · ∏_{p ∣ d} m^{(1)}_p`.
  Minimal hypotheses in the statement (Q1-C); the meaningful range is a remark in A.
* Item 40 `jl_formula_identity_squarefree`: the case `F = F_M`, `F_L = ∏_{p ∣ L} m^{(1)}_p` (inline, no tagged def).
* Item 41 `jl_formula_golden_d11`, item 42 `cohen_golden_values`: kernel-checkable values (P04 tests 2 and 1).
* Item 43 `d2_weight_instance`: the closed weight `H₀` (B-only `d2WeightH0`) satisfies the inline hypothesis of
  `III.ef.thm:d2-sum-form`, and `H₀(Δ₀) = 1` for fundamental `Δ₀ < 0` (A1's added clause, `docs/notes/Q1/A1-issues.md` 8).
-/

open scoped ArithmeticFunction.omega ArithmeticFunction.sigma

namespace GL2TF.Explicit

/-! ### §6, last item: the boundary split of `Λ^{ES}` -/

/-- Item 38: `δ_{k,2}σ₁(n) − 2A₄(k, n) − Eis(N, k, n) = −Ẽis(N, k, n)`, so `Λ^{ES}` has only `Ẽis` as boundary term. -/
@[tf_id "III.ef.lem:lefschetz-es-boundary-split"]
theorem lefschetz_es_boundary_split (N k n : ℕ) (F : ℤ → ℚ) :
    lefschetzES N k n F =
      -2 * cohenA1 N k n - 2 * eichlerElliptic k n F - 2 * cohenA3 N k n - eisensteinCorrected N k n := by
  unfold lefschetzES eisensteinExpr cohenA4
  split_ifs <;> ring

/-! ### §7: the identity -/

/-- Proof helper: `ω n` is the number of prime factors. -/
private theorem omega_eq_card' (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- Proof helper: `A₁(N, k, n) = C(k, n) ψ(N)`. -/
private theorem cohenA1_eq (N k n : ℕ) :
    cohenA1 N k n =
      (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * dedekindPsi N := by
  unfold cohenA1
  split_ifs <;> ring

/-- Proof helper: `c_{dM} = 2^{ω(d)} c_M` for `d` squarefree and prime to `M`. -/
private theorem boundaryDivisorSum_sqfree_mul {d M : ℕ} (hd : Squarefree d) (hdM : d.Coprime M) (m : ℤ) :
    (boundaryDivisorSum (d * M) m : ℚ) = (2 : ℚ) ^ ω d * (boundaryDivisorSum M m : ℚ) := by
  rw [boundary_multiplicative d M hdM, (boundary_local_factor m).2.2 d hd]
  push_cast
  ring

/-- Proof helper: `A₃(dM) = 2^{ω(d)} A₃(M)`. -/
private theorem cohenA3_sqfree_mul {d M : ℕ} (hd : Squarefree d) (hdM : d.Coprime M) (k n : ℕ) :
    cohenA3 (d * M) k n = (2 : ℚ) ^ ω d * cohenA3 M k n := by
  unfold cohenA3
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [boundaryDivisorSum_sqfree_mul hd hdM]
  ring

/-- Proof helper: `Ẽis(dM) = 2^{ω(d)} Ẽis(M)`. -/
private theorem eisensteinCorrected_sqfree_mul {d M : ℕ} (hd : Squarefree d) (hdM : d.Coprime M) (k n : ℕ) :
    eisensteinCorrected (d * M) k n = (2 : ℚ) ^ ω d * eisensteinCorrected M k n := by
  unfold eisensteinCorrected
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [boundaryDivisorSum_sqfree_mul hd hdM]
  ring

/-- Proof helper: a `d`-weighted sum of elliptic expressions with twisted parameters. -/
private theorem sum_mul_eichlerElliptic (S : Finset ℕ) (c : ℕ → ℚ) (G : ℕ → ℤ → ℚ) (k n : ℕ) (F : ℤ → ℚ) :
    ∑ d ∈ S, c d * eichlerElliptic k n (fun Δ ↦ F Δ * G d Δ) =
      -(1 / 2) * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
        (heckePoly k t n : ℚ) *
          ∑ f ∈ orderIndexSet t n,
            weightedClassNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * F ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) *
              ∑ d ∈ S, c d * G d ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) := by
  unfold eichlerElliptic
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- Proof helper: the local complement, `∑_{d ∣ D} (−2)^{ω(D/d)} ∏_{p ∣ d} m^{(1)}_p = −∏_{p ∣ D} m^D_p`
for squarefree `D` with `ω(D)` odd. -/
private theorem sum_signed_localFactorEichler {D : ℕ} (hD : Squarefree D) (hω : Odd (ω D)) (Δ : ℤ) :
    ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ) =
      -∏ p ∈ D.primeFactors, (localFactorRamified p Δ : ℚ) := by
  have h := sum_divisors_prod_eq_prod_add (fun p ↦ (localFactorEichler p Δ : ℚ)) (fun _ ↦ (-2 : ℚ)) hD
  simp only [Finset.prod_const] at h
  simp only [omega_eq_card']
  rw [h]
  have hloc : ∀ p, (localFactorEichler p Δ : ℚ) + -2 = -(localFactorRamified p Δ : ℚ) := by
    intro p
    unfold localFactorEichler localFactorRamified
    push_cast
    ring
  simp only [hloc]
  rw [Finset.prod_neg, ← omega_eq_card', Odd.neg_one_pow hω]
  ring


/-- Item 39 (exit, Q1-A): the formula-level JL identity in Eichler form, with the level-`M` local factor a parameter `F`.
The twisted parameter at the divisor `d` is `F_d(Δ) = F(Δ) ∏_{p ∣ d} m^{(1)}_p(Δ)`. -/
@[tf_id "III.ef.thm:jl-formula-identity"]
theorem jl_formula_identity (D M k n : ℕ) (F : ℤ → ℚ) (hD : Squarefree D) (hω : Odd (ω D))
    (hDM : D.Coprime M) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    eichlerB D M k n F =
      -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzES (d * M) k n (fun Δ ↦ F Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) := by
  obtain ⟨h4a, h4b, h4c⟩ := signedDivisorSum_constants hD
  have hD1 : 1 < D := by
    have : ω D ≠ 0 := fun h => by simp [h] at hω
    exact ArithmeticFunction.cardDistinctFactors_pos.mp (Nat.pos_of_ne_zero this)
  have h4b' : ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ ω d = 0 := by
    exact_mod_cast h4b hD1
  have hdiv : ∀ d ∈ D.divisors, Squarefree d ∧ d.Coprime M := fun d hd =>
    ⟨Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hD,
      Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hDM⟩
  set C : ℚ := if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0 with hC
  -- expand the right side by item 38
  have hsplit : -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzES (d * M) k n (fun Δ ↦ F Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) =
      ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (C * dedekindPsi (d * M)) +
        ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
          eichlerElliptic k n (fun Δ ↦ F Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) +
        (∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ ω d) *
          (cohenA3 M k n + (1 / 2) * eisensteinCorrected M k n) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hsq, hcop⟩ := hdiv d hd
    rw [lefschetz_es_boundary_split, cohenA1_eq, cohenA3_sqfree_mul hsq hcop,
      eisensteinCorrected_sqfree_mul hsq hcop]
    ring
  rw [hsplit, h4b', zero_mul, add_zero]
  -- central term (item 4(c)) and elliptic term (item 3)
  have hcen : ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (C * dedekindPsi (d * M)) =
      C * (∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) * dedekindPsi M := by
    rw [show ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (C * dedekindPsi (d * M)) =
        C * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * dedekindPsi (d * M) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring, h4c M hDM]
    ring
  rw [hcen, sum_mul_eichlerElliptic D.divisors (fun d ↦ (-2 : ℚ) ^ ω (D / d))
    (fun d Δ ↦ ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) k n F]
  simp only [sum_signed_localFactorEichler hD hω]
  unfold eichlerB
  rw [← hC]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold weightedClassNumber
  ring

/-- Item 40: the squarefree-`M` corollary, every level `dM` with its own local factors `F_{dM}`,
`F_L(Δ) = ∏_{p ∣ L} m^{(1)}_p(Δ)`. -/
@[tf_id "III.ef.cor:jl-formula-identity-squarefree"]
theorem jl_formula_identity_squarefree (D M k n : ℕ) (hD : Squarefree D) (hω : Odd (ω D))
    (hM : Squarefree M) (hDM : D.Coprime M) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    eichlerB D M k n (fun Δ ↦ ∏ p ∈ M.primeFactors, (localFactorEichler p Δ : ℚ)) =
      -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzES (d * M) k n (fun Δ ↦ ∏ p ∈ (d * M).primeFactors, (localFactorEichler p Δ : ℚ)) := by
  rw [jl_formula_identity D M k n _ hD hω hDM hk hn]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hcop : d.Coprime M := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hDM
  have hdisj : Disjoint d.primeFactors M.primeFactors := Nat.Coprime.disjoint_primeFactors hcop
  congr 2
  funext Δ
  rw [Nat.Coprime.primeFactors_mul hcop, Finset.prod_union hdisj, mul_comm]

/-! ### §7: examples -/

/-- Item 41 (P04 test 2): `E^𝔹(11, 1, 2, n; 1) = 2, 1, 3`, `Λ^{ES}(1, 2, n; 1) = 1, 3, 4`,
`Λ^{ES}(11, 2, n; m^{(1)}_{11}) = −2, 4, 2` for `n = 1, 2, 3`. -/
@[tf_id "III.ef.ex:jl-formula-golden-d11"]
theorem jl_formula_golden_d11 :
    (eichlerB 11 1 2 1 (fun _ ↦ 1) = 2 ∧ eichlerB 11 1 2 2 (fun _ ↦ 1) = 1 ∧
      eichlerB 11 1 2 3 (fun _ ↦ 1) = 3) ∧
    (lefschetzES 1 2 1 (fun _ ↦ 1) = 1 ∧ lefschetzES 1 2 2 (fun _ ↦ 1) = 3 ∧
      lefschetzES 1 2 3 (fun _ ↦ 1) = 4) ∧
    (lefschetzES 11 2 1 (fun Δ ↦ (localFactorEichler 11 Δ : ℚ)) = -2 ∧
      lefschetzES 11 2 2 (fun Δ ↦ (localFactorEichler 11 Δ : ℚ)) = 4 ∧
      lefschetzES 11 2 3 (fun Δ ↦ (localFactorEichler 11 Δ : ℚ)) = 2) := by
  decide +kernel

/-- Item 42 (P04 test 1): `T^C(11, 2, 2) = −2`, `T^C(11, 2, 3) = −1`, `T^C(1, 12, 2) = −24`. -/
@[tf_id "III.ef.ex:cohen-golden-values"]
theorem cohen_golden_values :
    cohenTraceExpr 11 2 2 = -2 ∧ cohenTraceExpr 11 2 3 = -1 ∧ cohenTraceExpr 1 12 2 = -24 := by
  decide +kernel

open Classical in
/-- The closed weight `H₀` of item 43 (B-only): `H₀(Δ₀m²) = ∏_{p ∣ m} p^{v_p(m)−1}(p − χ_{Δ₀}(p))` for a fundamental
discriminant `Δ₀ < 0` (`Δ₀ ≡ 0, 1 mod 4` and no prime divides the conductor of `Δ₀`) and `m ≥ 1`; `0` if `Δ` has no such
form. The decomposition is unique when it exists; the definition picks one by choice. -/
@[tf_aux "III.ef.def:d2-weight-h0"]
noncomputable def d2WeightH0 (Δ : ℤ) : ℚ :=
  if h : ∃ Δ₀ : ℤ, ∃ m : ℕ, Δ₀ < 0 ∧ (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) ∧ 1 ≤ m ∧ Δ = Δ₀ * (m : ℤ) ^ 2 then
    ∏ p ∈ h.choose_spec.choose.primeFactors,
      (p : ℚ) ^ (h.choose_spec.choose.factorization p - 1) * ((p : ℚ) - (kroneckerPrime h.choose p : ℚ))
  else 0

private theorem sq_emod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem odd_sq_mul_emod_four {b : ℕ} (hb : ¬ 2 ∣ b) (E : ℤ) : (b : ℤ) ^ 2 * E % 4 = E % 4 := by
  have : (b : ℤ) % 4 = 1 ∨ (b : ℤ) % 4 = 3 := by omega
  have h4 : (b : ℤ) ^ 2 % 4 = 1 := by
    rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]
  rw [Int.mul_emod, h4, one_mul, Int.emod_emod]

private theorem disc_mul_sq {Δ : ℤ} (hd : Δ % 4 = 0 ∨ Δ % 4 = 1) (x : ℤ) :
    Δ * x ^ 2 % 4 = 0 ∨ Δ * x ^ 2 % 4 = 1 := by
  rw [Int.mul_emod]
  rcases hd with h | h <;> rcases sq_emod_four x with h' | h' <;> simp [h, h']

/-- A conductor-free discriminant `Δ₁` with `Δ₀ a² = Δ₁ b²`, `(a, b) = 1`, `Δ₀` a discriminant, forces `a = 1`. -/
private theorem eq_one_of_condFree {Δ₀ Δ₁ : ℤ} (h₀ : Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) (h₁ : Δ₁ % 4 = 0 ∨ Δ₁ % 4 = 1)
    (hf₁ : ∀ p : ℕ, p.Prime → dividesConductor p Δ₁ = false) {a b : ℕ} (hab : a.Coprime b)
    (he : Δ₀ * (a : ℤ) ^ 2 = Δ₁ * (b : ℤ) ^ 2) : a = 1 := by
  by_contra ha1
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  have hpb : ¬ p ∣ b := (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpa hab)
  have hcop : IsCoprime ((p : ℤ) ^ 2) ((b : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).2 hpb)).pow
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero)
  obtain ⟨a', rfl⟩ := hpa
  have hdvd : (p : ℤ) ^ 2 ∣ Δ₁ * (b : ℤ) ^ 2 := ⟨Δ₀ * (a' : ℤ) ^ 2, by rw [← he]; push_cast; ring⟩
  obtain ⟨E, hE⟩ := hcop.dvd_of_dvd_mul_right hdvd
  have he' : Δ₀ * (a' : ℤ) ^ 2 = (b : ℤ) ^ 2 * E := by
    apply mul_left_cancel₀ hp2
    rw [show (p : ℤ) ^ 2 * (Δ₀ * (a' : ℤ) ^ 2) = Δ₀ * ((p * a' : ℕ) : ℤ) ^ 2 by push_cast; ring, he, hE]
    ring
  have hEd : E % 4 = 0 ∨ E % 4 = 1 := by
    by_cases h2 : p = 2
    · subst h2
      rw [← odd_sq_mul_emod_four hpb E, ← he']
      exact disc_mul_sq h₀ _
    · have hpo : ¬ 2 ∣ p := fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
      rw [← odd_sq_mul_emod_four hpo E, ← hE]
      exact h₁
  have := hf₁ p hp
  unfold dividesConductor at this
  rw [hE, Int.mul_ediv_cancel_left _ hp2] at this
  simp only [decide_eq_false_iff_not] at this
  exact this ⟨dvd_mul_right _ _, hEd⟩

/-- Uniqueness of the decomposition `Δ = Δ₀ m²` with `Δ₀` a conductor-free discriminant and `m ≥ 1`. -/
private theorem decomp_unique {Δ₀ Δ₁ : ℤ} {m m' : ℕ} (hd₀ : Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1)
    (hf₀ : ∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) (hd₁ : Δ₁ % 4 = 0 ∨ Δ₁ % 4 = 1)
    (hf₁ : ∀ p : ℕ, p.Prime → dividesConductor p Δ₁ = false) (hm : 1 ≤ m)
    (he : Δ₀ * (m : ℤ) ^ 2 = Δ₁ * (m' : ℤ) ^ 2) : Δ₀ = Δ₁ ∧ m = m' := by
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime m m'
  generalize Nat.gcd m m' = g at ha hb
  subst ha hb
  have hg : g ≠ 0 := by rintro rfl; simp at hm
  have hg2 : ((g : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natCast_ne_zero.mpr hg)
  have he' : Δ₀ * (a : ℤ) ^ 2 = Δ₁ * (b : ℤ) ^ 2 := by
    apply mul_right_cancel₀ hg2
    rw [show Δ₀ * (a : ℤ) ^ 2 * (g : ℤ) ^ 2 = Δ₀ * ((a * g : ℕ) : ℤ) ^ 2 by push_cast; ring, he]
    push_cast; ring
  have ha1 : a = 1 := eq_one_of_condFree hd₀ hd₁ hf₁ hab he'
  have hb1 : b = 1 := eq_one_of_condFree hd₁ hd₀ hf₀ hab.symm he'.symm
  subst ha1 hb1
  refine ⟨?_, rfl⟩
  simpa using he'

/-- Existence of the decomposition `Δ = Δ₀ m²` for a negative discriminant `Δ`. -/
private theorem decomp_exists : ∀ (n : ℕ) (Δ : ℤ), Δ.natAbs = n → Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) →
    ∃ Δ₀ : ℤ, ∃ m : ℕ, Δ₀ < 0 ∧ (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) ∧ 1 ≤ m ∧ Δ = Δ₀ * (m : ℤ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Δ hn hneg hd
  by_cases hf : ∀ p : ℕ, p.Prime → dividesConductor p Δ = false
  · exact ⟨Δ, 1, hneg, hd, hf, le_rfl, by ring⟩
  · push Not at hf
    obtain ⟨p, hp, hc⟩ := hf
    have hc' : (p : ℤ) ^ 2 ∣ Δ ∧ (Δ / (p : ℤ) ^ 2 % 4 = 0 ∨ Δ / (p : ℤ) ^ 2 % 4 = 1) := by
      unfold dividesConductor at hc
      simpa only [ne_eq, Bool.not_eq_false, decide_eq_true_eq] using hc
    obtain ⟨⟨E, hE⟩, hEd⟩ := hc'
    have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero)
    rw [hE, Int.mul_ediv_cancel_left _ hp2] at hEd
    have hp4 : (4 : ℤ) ≤ (p : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    have hEneg : E < 0 := by
      by_contra h
      have h := not_lt.mp h
      rw [hE] at hneg
      nlinarith
    have hlt : E.natAbs < n := by
      subst hn
      rw [hE, Int.natAbs_mul]
      have h1 : 1 ≤ E.natAbs := by omega
      have h4 : 4 ≤ ((p : ℤ) ^ 2).natAbs := by omega
      nlinarith
    obtain ⟨Δ₀, m, h0, hd0, hf0, hm, hEm⟩ := ih _ hlt E rfl hEneg hEd
    refine ⟨Δ₀, p * m, h0, hd0, hf0, Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega)), ?_⟩
    rw [hE, hEm]
    push_cast
    ring

/-- `H₀(Δ₀ m²)` is the product `∏_{p ∣ m} p^{v_p(m) − 1}(p − χ_{Δ₀}(p))`. -/
private theorem d2WeightH0_eq {Δ₀ : ℤ} {m : ℕ} (h0 : Δ₀ < 0) (hd0 : Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1)
    (hf0 : ∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) (hm : 1 ≤ m) :
    d2WeightH0 (Δ₀ * (m : ℤ) ^ 2) =
      ∏ p ∈ m.primeFactors, (p : ℚ) ^ (m.factorization p - 1) * ((p : ℚ) - (kroneckerPrime Δ₀ p : ℚ)) := by
  have hex : ∃ Δ₀' : ℤ, ∃ m' : ℕ, Δ₀' < 0 ∧ (Δ₀' % 4 = 0 ∨ Δ₀' % 4 = 1) ∧
      (∀ p : ℕ, p.Prime → dividesConductor p Δ₀' = false) ∧ 1 ≤ m' ∧
        Δ₀ * (m : ℤ) ^ 2 = Δ₀' * (m' : ℤ) ^ 2 := ⟨Δ₀, m, h0, hd0, hf0, hm, rfl⟩
  unfold d2WeightH0
  split_ifs
  · obtain ⟨-, hd', hf', hm', he'⟩ := hex.choose_spec.choose_spec
    obtain ⟨e1, e2⟩ := decomp_unique hd' hf' hd0 hf0 hm' he'.symm
    rw [e2, e1]

/-- `χ_{Δ₀ m²}(p) = 0` if `p ∣ m` and `χ_{Δ₀}(p)` otherwise. -/
private theorem kroneckerPrime_mul_sq (Δ₀ : ℤ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    kroneckerPrime (Δ₀ * (m : ℤ) ^ 2) p = if p ∣ m then 0 else kroneckerPrime Δ₀ p := by
  unfold kroneckerPrime
  by_cases h2 : p = 2
  · subst h2
    simp only [ite_true]
    by_cases hm : 2 ∣ m
    · rw [ite_eq_left hm]
      have : (Δ₀ * (m : ℤ) ^ 2) % 2 = 0 :=
        Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.mpr hm) two_ne_zero) Δ₀)
      rw [ite_eq_left this]
    · rw [ite_eq_right hm]
      have h8 : (m : ℤ) ^ 2 % 8 = 1 := by
        have : (m : ℤ) % 8 = 1 ∨ (m : ℤ) % 8 = 3 ∨ (m : ℤ) % 8 = 5 ∨ (m : ℤ) % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      have key : (Δ₀ * (m : ℤ) ^ 2) % 8 = Δ₀ % 8 := by
        rw [Int.mul_emod, h8, mul_one, Int.emod_emod]
      generalize Δ₀ * (m : ℤ) ^ 2 = X at key ⊢
      have k2 : X % 2 = Δ₀ % 2 := by omega
      rw [k2, key]
  · simp only [h2, ite_false]
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
    by_cases hm : p ∣ m
    · rw [ite_eq_left hm]
      have : jacobiSym (m : ℤ) p = 0 := by
        refine jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero, ?_⟩
        rw [Int.gcd_natCast_natCast, Nat.gcd_eq_right hm]
        exact hp.ne_one
      rw [this]
      ring
    · rw [ite_eq_right hm, jacobiSym.sq_one, mul_one]
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)

/-- The product `G(m)` gains the factor `p` (if `p ∣ m`) or `p − χ_{Δ₀}(p)` (if `p ∤ m`) from `m` to `pm`. -/
private theorem prod_mul_prime (Δ₀ : ℤ) {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∏ q ∈ (p * m).primeFactors, (q : ℚ) ^ ((p * m).factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) =
      (if p ∣ m then (p : ℚ) else (p : ℚ) - (kroneckerPrime Δ₀ p : ℚ)) *
        ∏ q ∈ m.primeFactors, (q : ℚ) ^ (m.factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) := by
  have hfac : ∀ q, (p * m).factorization q = (if q = p then 1 else 0) + m.factorization q := by
    intro q
    rw [Nat.factorization_mul hp.ne_zero hm, Finsupp.add_apply, Nat.Prime.factorization hp,
      Finsupp.single_apply]
    simp only [eq_comm]
  have hpf : (p * m).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hm, Nat.Prime.primeFactors hp, Finset.insert_eq]
  have hrest : ∀ q ∈ m.primeFactors.erase p,
      (q : ℚ) ^ ((p * m).factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) =
        (q : ℚ) ^ (m.factorization q - 1) * ((q : ℚ) - (kroneckerPrime Δ₀ q : ℚ)) := by
    intro q hq
    rw [hfac q, ite_eq_right (Finset.ne_of_mem_erase hq), zero_add]
  rw [hpf]
  by_cases hpm : p ∣ m
  · have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩
    rw [ite_eq_left hpm, Finset.insert_eq_of_mem hmem, ← Finset.mul_prod_erase _ _ hmem,
      ← Finset.mul_prod_erase _ _ hmem, Finset.prod_congr rfl hrest, hfac p, ite_eq_left rfl]
    have hv : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hm).mp hpm
    obtain ⟨v, hv'⟩ : ∃ v, m.factorization p = v + 1 := ⟨m.factorization p - 1, by omega⟩
    rw [hv', show 1 + (v + 1) - 1 = v + 1 by omega, show v + 1 - 1 = v by omega, pow_succ]
    ring
  · have hnmem : p ∉ m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)
    rw [ite_eq_right hpm, Finset.prod_insert hnmem, hfac p, ite_eq_left rfl,
      Nat.factorization_eq_zero_of_not_dvd hpm]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun q hq => ?_
      rw [hfac q, ite_eq_right (fun (h : q = p) => hnmem (h ▸ hq)), zero_add]

/-- Item 43: `H₀` satisfies the inline hypothesis of `III.ef.thm:d2-sum-form`, and `H₀(Δ₀) = 1` for every fundamental
discriminant `Δ₀ < 0`; in particular `H₀(−3) = 1`. So exit 23 is not vacuous before Q4. -/
@[tf_id "III.ef.ex:d2-weight-instance"]
theorem d2_weight_instance :
    (∀ (Δ : ℤ) (p : ℕ), Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) → p.Prime →
      d2WeightH0 ((p : ℤ) ^ 2 * Δ) = ((p : ℚ) - (kroneckerPrime Δ p : ℚ)) * d2WeightH0 Δ) ∧
    (∀ Δ₀ : ℤ, Δ₀ < 0 → (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) → (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) →
      d2WeightH0 Δ₀ = 1) ∧
    d2WeightH0 (-3) = 1 := by
  have h2 : ∀ Δ₀ : ℤ, Δ₀ < 0 → (Δ₀ % 4 = 0 ∨ Δ₀ % 4 = 1) → (∀ p : ℕ, p.Prime → dividesConductor p Δ₀ = false) →
      d2WeightH0 Δ₀ = 1 := by
    intro Δ₀ h0 hd0 hf0
    have h := d2WeightH0_eq (m := 1) h0 hd0 hf0 le_rfl
    simpa using h
  refine ⟨?_, h2, ?_⟩
  · intro Δ p hneg hd hp
    obtain ⟨Δ₀, m, h0, hd0, hf0, hm, rfl⟩ := decomp_exists _ Δ rfl hneg hd
    have hpm : 1 ≤ p * m := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega))
    rw [show (p : ℤ) ^ 2 * (Δ₀ * (m : ℤ) ^ 2) = Δ₀ * ((p * m : ℕ) : ℤ) ^ 2 by push_cast; ring,
      d2WeightH0_eq h0 hd0 hf0 hpm, d2WeightH0_eq h0 hd0 hf0 hm, prod_mul_prime Δ₀ hp (by omega),
      kroneckerPrime_mul_sq Δ₀ hp m]
    split_ifs <;> push_cast <;> ring
  · refine h2 (-3) (by norm_num) (by decide) fun p hp => ?_
    unfold dividesConductor
    simp only [decide_eq_false_iff_not, not_and]
    intro h
    have h3 : (p : ℤ) ∣ 3 := (dvd_neg.mp (dvd_trans (dvd_pow_self _ two_ne_zero) h))
    have hp3 : p ∣ 3 := by exact_mod_cast h3
    have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst this
    exact absurd h (by decide)

end GL2TF.Explicit
