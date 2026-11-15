import AlgJL.Meta.Tag
import AlgJL.VolIII.P1.JLFormula

/-!
# The formula-level JL identity with general parameters (unit JLG)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §8 (`sec:ef-identity-general`). Plan `docs/sprints/JLG-plan.md`
(user approval 2026-11-13; feasibility note `~/data/jl_tf_exchange/TF-response-jl-formula-generalisation.md`).
Owner: JLG A author / formalizer.

Purely additive: the done and audited definitions of `Normalization.lean` and the theorems of `JLFormula.lean` stay as
they are. The general expressions take the three level-dependent ingredients as parameters:
* the elliptic factor `F : ℤ → ℕ → ℤ → ℚ`, evaluated at `F t f Δ_f` (it may depend on `t` and `f`, not only on `Δ_f`);
* the boundary factor `β : ℕ → ℕ → ℚ`, evaluated at the divisor pair `(a, a')`, in place of `c_N(a − a')`;
* the central coefficient `κ : ℚ` (Lefschetz side) and `c : ℚ` (Eichler side), in place of `ψ(N)` and `ψ(M)`.

Items:
* defs `eichlerEllipticGen`, `cohenA3Gen`, `eisensteinCorrectedGen`, `lefschetzESGen`, `eichlerBGen`;
* `lefschetz_es_general_boundary_split` (analogue of item 38);
* `eichlerB_eq_general`, `lefschetzES_eq_general` (the existing expressions are special values);
* `jl_formula_identity_general` (request (A)): no condition linking `D` to a level, no condition on `n`;
* `jl_formula_identity_ramified_index` (request (B)): the twisted identity for an index `m`, under `¬ IsSquare n ∨ c = 0`;
* `jl_formula_identity_from_general`: the statement of `jl_formula_identity` recovered from (A).

Stage 2: proofs along the route of A §8 (no `sorry`).
-/

open scoped ArithmeticFunction.omega ArithmeticFunction.sigma

namespace GL2TF.Explicit

/-! ### General expressions -/

/-- The general elliptic expression
`A₂^E(k, n; F) = −½ ∑_{t² < 4n} P_k(t, n) ∑_{f ∈ 𝓕(t, n)} h_w(Δ_f) F(t, f, Δ_f)`, `F : ℤ → ℕ → ℤ → ℚ`. -/
@[tf_id "III.ef.def:eichler-elliptic-expression-general"]
def eichlerEllipticGen (k n : ℕ) (F : ℤ → ℕ → ℤ → ℚ) : ℚ :=
  -(1 / 2) * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
    (heckePoly k t n : ℚ) *
      ∑ f ∈ orderIndexSet t n,
        weightedClassNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * F t f ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2)

/-- The general boundary term `A₃^β(k, n) = −½ ∑_{aa' = n} min(a, a')^{k−1} β(a, a')`, `β : ℕ → ℕ → ℚ`. -/
@[tf_id "III.ef.def:cohen-a3-general"]
def cohenA3Gen (k n : ℕ) (β : ℕ → ℕ → ℚ) : ℚ :=
  -(1 / 2) * ∑ x ∈ n.divisorsAntidiagonal, (min x.1 x.2 : ℚ) ^ (k - 1) * β x.1 x.2

/-- The general corrected Eisenstein expression `Ẽis^β(k, n) = ∑_{aa' = n} a'^{k−1} β(a, a')`. -/
@[tf_id "III.ef.def:eisenstein-expression-corrected-general"]
def eisensteinCorrectedGen (k n : ℕ) (β : ℕ → ℕ → ℚ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (x.2 : ℚ) ^ (k - 1) * β x.1 x.2

/-- The general Lefschetz expression
`Λ^{ES}(k, n; κ, F, β) = δ_{k,2} σ₁(n) − 2(C(k, n) κ + A₂^E(k, n; F) + A₃^β(k, n) + A₄(k, n)) − (Ẽis^β(k, n) − δ_{k,2} σ₁(n))`
with `C(k, n) = (k − 1)/12 · r^{k−2}` if `n = r²` and `0` otherwise. -/
@[tf_id "III.ef.def:lefschetz-es-expression-general"]
def lefschetzESGen (k n : ℕ) (κ : ℚ) (F : ℤ → ℕ → ℤ → ℚ) (β : ℕ → ℕ → ℚ) : ℚ :=
  (if k = 2 then (σ 1 n : ℚ) else 0) -
    2 * ((if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * κ +
      eichlerEllipticGen k n F + cohenA3Gen k n β + cohenA4 k n) -
    (eisensteinCorrectedGen k n β - (if k = 2 then (σ 1 n : ℚ) else 0))

/-- The general Eichler expression
`E^𝔹(D, k, n; c, F) = C(k, n) ∏_{p ∣ D}(p − 1) · c + ∑_{t² < 4n} P_k(t, n) ∑_{f ∈ 𝓕(t, n)} (h/w)(Δ_f) ∏_{p ∣ D} m^D_p(Δ_f) · F(t, f, Δ_f)`. -/
@[tf_id "III.ef.def:eichler-b-expression-general"]
def eichlerBGen (D k n : ℕ) (c : ℚ) (F : ℤ → ℕ → ℤ → ℚ) : ℚ :=
  (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) *
      (∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) * c +
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
      (heckePoly k t n : ℚ) *
        ∑ f ∈ orderIndexSet t n,
          (classNumberForms ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) /
              (unitNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) *
            (∏ p ∈ D.primeFactors, (localFactorRamified p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ)) *
            F t f ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2)

/-! ### The boundary split and the special values -/

/-- Analogue of item 38: `Λ^{ES}(k, n; κ, F, β) = −2C(k, n)κ − 2A₂^E(k, n; F) − 2A₃^β(k, n) − Ẽis^β(k, n)`. -/
@[tf_id "III.ef.lem:lefschetz-es-general-boundary-split"]
theorem lefschetz_es_general_boundary_split (k n : ℕ) (κ : ℚ) (F : ℤ → ℕ → ℤ → ℚ) (β : ℕ → ℕ → ℚ) :
    lefschetzESGen k n κ F β =
      -2 * ((if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * κ) -
        2 * eichlerEllipticGen k n F - 2 * cohenA3Gen k n β - eisensteinCorrectedGen k n β := by
  unfold lefschetzESGen cohenA4
  split_ifs <;> ring

/-- `E^𝔹(D, M, k, n; F)` is the general expression at `c = ψ(M)` and `F(t, f, Δ) = F(Δ)`. -/
@[tf_id "III.ef.lem:eichler-b-eq-general"]
theorem eichlerB_eq_general (D M k n : ℕ) (F : ℤ → ℚ) :
    eichlerB D M k n F = eichlerBGen D k n (dedekindPsi M) (fun _ _ Δ ↦ F Δ) := by
  rfl

/-- `Λ^{ES}(N, k, n; F)` is the general expression at `κ = ψ(N)`, `F(t, f, Δ) = F(Δ)` and `β(a, a') = c_N(a − a')`. -/
@[tf_id "III.ef.lem:lefschetz-es-eq-general"]
theorem lefschetzES_eq_general (N k n : ℕ) (F : ℤ → ℚ) :
    lefschetzES N k n F =
      lefschetzESGen k n (dedekindPsi N) (fun _ _ Δ ↦ F Δ)
        (fun a a' ↦ (boundaryDivisorSum N ((a : ℤ) - a') : ℚ)) := by
  simp only [lefschetzES, lefschetzESGen, eisensteinExpr, cohenA1, eichlerElliptic, eichlerEllipticGen, cohenA3,
    cohenA3Gen, eisensteinCorrected, eisensteinCorrectedGen]
  split_ifs <;> ring

/-! ### The identities -/

/-- Proof helper: `ω n` is the number of prime factors. -/
private theorem omega_eq_card_gen (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- Proof helper: `ψ(1) = 1`. -/
private theorem dedekindPsi_one_gen : dedekindPsi 1 = 1 := by
  simp [dedekindPsi]

/-- Proof helper: `A₃^{xG} = x A₃^G`. -/
private theorem cohenA3Gen_const_mul (k n : ℕ) (x : ℚ) (G : ℕ → ℕ → ℚ) :
    cohenA3Gen k n (fun a a' ↦ x * G a a') = x * cohenA3Gen k n G := by
  have h : ∑ y ∈ n.divisorsAntidiagonal, (min y.1 y.2 : ℚ) ^ (k - 1) * (x * G y.1 y.2) =
      x * ∑ y ∈ n.divisorsAntidiagonal, (min y.1 y.2 : ℚ) ^ (k - 1) * G y.1 y.2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [cohenA3Gen]
  rw [h]
  ring

/-- Proof helper: `Ẽis^{xG} = x Ẽis^G`. -/
private theorem eisensteinCorrectedGen_const_mul (k n : ℕ) (x : ℚ) (G : ℕ → ℕ → ℚ) :
    eisensteinCorrectedGen k n (fun a a' ↦ x * G a a') = x * eisensteinCorrectedGen k n G := by
  simp only [eisensteinCorrectedGen]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Proof helper: a `d`-weighted sum of general elliptic expressions with twisted parameters. -/
private theorem sum_mul_eichlerEllipticGen (S : Finset ℕ) (c : ℕ → ℚ) (H : ℕ → ℤ → ℚ) (k n : ℕ)
    (F : ℤ → ℕ → ℤ → ℚ) :
    ∑ d ∈ S, c d * eichlerEllipticGen k n (fun t f Δ ↦ F t f Δ * H d Δ) =
      -(1 / 2) * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
        (heckePoly k t n : ℚ) *
          ∑ f ∈ orderIndexSet t n,
            weightedClassNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * F t f ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) *
              ∑ d ∈ S, c d * H d ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) := by
  unfold eichlerEllipticGen
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- Proof helper: `∑_{d ∣ D} (−2)^{ω(D/d)} ∏_{p ∣ d} m^{(1)}_p = −∏_{p ∣ D} m^D_p` (`D` squarefree, `ω(D)` odd). -/
private theorem sum_signed_localFactorEichler_gen {D : ℕ} (hD : Squarefree D) (hω : Odd (ω D)) (Δ : ℤ) :
    ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ) =
      -∏ p ∈ D.primeFactors, (localFactorRamified p Δ : ℚ) := by
  have h := sum_divisors_prod_eq_prod_add (fun p ↦ (localFactorEichler p Δ : ℚ)) (fun _ ↦ (-2 : ℚ)) hD
  simp only [Finset.prod_const] at h
  simp only [omega_eq_card_gen]
  rw [h]
  have hloc : ∀ p, (localFactorEichler p Δ : ℚ) + -2 = -(localFactorRamified p Δ : ℚ) := by
    intro p
    unfold localFactorEichler localFactorRamified
    push_cast
    ring
  simp only [hloc]
  rw [Finset.prod_neg, ← omega_eq_card_gen, Odd.neg_one_pow hω]
  ring

/-- Proof helper: `ω(D) ≥ 1` odd gives `D > 1`. -/
private theorem one_lt_of_odd_omega {D : ℕ} (hω : Odd (ω D)) : 1 < D := by
  have : ω D ≠ 0 := fun h => by simp [h] at hω
  exact ArithmeticFunction.cardDistinctFactors_pos.mp (Nat.pos_of_ne_zero this)

/-- Proof helper: the primes of `gcd(e, m)` are the primes of `e` dividing `m` (`e ≠ 0`). -/
private theorem primeFactors_gcd_eq_filter {e : ℕ} (he : e ≠ 0) (m : ℕ) :
    (Nat.gcd e m).primeFactors = e.primeFactors.filter (· ∣ m) := by
  have hg : Nat.gcd e m ≠ 0 := (Nat.gcd_pos_of_pos_left m (Nat.pos_of_ne_zero he)).ne'
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hp, ⟨h1, h2⟩, -⟩
    exact ⟨⟨hp, h1, he⟩, h2⟩
  · rintro ⟨⟨hp, h1, -⟩, h2⟩
    exact ⟨hp, ⟨h1, h2⟩, hg⟩

/-- Proof helper: `ω(gcd(e, m)) ≤ ω(e)` (`e ≠ 0`). -/
private theorem omega_gcd_le {e : ℕ} (he : e ≠ 0) (m : ℕ) : ω (Nat.gcd e m) ≤ ω e := by
  rw [omega_eq_card_gen, omega_eq_card_gen]
  exact Finset.card_le_card (Nat.primeFactors_mono (Nat.gcd_dvd_left e m) he)

/-- Proof helper: `∏_{p ∣ e} (p ∣ m ? x : y) = x^{ω(gcd(e, m))} y^{ω(e) − ω(gcd(e, m))}` (`e ≠ 0`). -/
private theorem prod_ite_dvd {e : ℕ} (he : e ≠ 0) (m : ℕ) (x y : ℚ) :
    ∏ p ∈ e.primeFactors, (if p ∣ m then x else y) =
      x ^ ω (Nat.gcd e m) * y ^ (ω e - ω (Nat.gcd e m)) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, omega_eq_card_gen, omega_eq_card_gen,
    primeFactors_gcd_eq_filter he, ← Finset.card_filter_add_card_filter_not (s := e.primeFactors) (fun p => p ∣ m),
    Nat.add_sub_cancel_left]

/-- Proof helper: `(−1)^a 2^{a − b} = (−1)^b (−2)^{a − b}` for `b ≤ a`. -/
private theorem neg_one_pow_mul_two_pow {a b : ℕ} (hab : b ≤ a) :
    (-1 : ℚ) ^ a * 2 ^ (a - b) = (-1) ^ b * (-2) ^ (a - b) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_sub_cancel_left, pow_add, neg_pow (2 : ℚ) r]
  ring

/-- Proof helper: `s_d(m) = ∏_{p ∣ D/d} (p ∣ m ? −1 : −2)` for `d ∣ D ≠ 0`. -/
private theorem signed_coeff_eq_prod {D d : ℕ} (hD : D ≠ 0) (hd : d ∣ D) (m : ℕ) :
    (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) =
      ∏ p ∈ (D / d).primeFactors, (if p ∣ m then (-1 : ℚ) else -2) := by
  have he : D / d ≠ 0 := fun h => hD (Nat.eq_zero_of_zero_dvd (h ▸ Nat.div_dvd_of_dvd hd))
  rw [prod_ite_dvd he, neg_one_pow_mul_two_pow (omega_gcd_le he m)]

/-- Proof helper: `2^{ω(d) − ω(gcd(d, m))} = ∏_{p ∣ d} (p ∣ m ? 1 : 2)` for `d ≠ 0`. -/
private theorem boundary_coeff_eq_prod {d : ℕ} (hd : d ≠ 0) (m : ℕ) :
    (2 : ℚ) ^ (ω d - ω (Nat.gcd d m)) = ∏ p ∈ d.primeFactors, (if p ∣ m then (1 : ℚ) else 2) := by
  rw [prod_ite_dvd hd, one_pow, one_mul]

/-- Proof helper: the local identity of (B), `∑_{d ∣ D} s_d(m) ∏_{p ∣ d} a_p = −∏_{p ∣ D} m^D_p`. -/
private theorem sum_signed_ramified_index {D : ℕ} (hD : Squarefree D) (hω : Odd (ω D)) (m : ℕ) (Δ : ℤ) :
    ∑ d ∈ D.divisors, (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
        ∏ p ∈ d.primeFactors, (if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ)) =
      -∏ p ∈ D.primeFactors, (localFactorRamified p Δ : ℚ) := by
  rw [Finset.sum_congr rfl fun d hd => by
    rw [signed_coeff_eq_prod hD.ne_zero (Nat.dvd_of_mem_divisors hd) m]]
  rw [sum_divisors_prod_eq_prod_add
    (fun p ↦ if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ))
    (fun p ↦ if p ∣ m then (-1 : ℚ) else -2) hD]
  have hloc : ∀ p, ((if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ)) +
      if p ∣ m then (-1 : ℚ) else -2) = -(localFactorRamified p Δ : ℚ) := by
    intro p
    unfold localFactorEichler localFactorRamified
    split_ifs <;> push_cast <;> ring
  simp only [hloc]
  rw [Finset.prod_neg, ← omega_eq_card_gen, Odd.neg_one_pow hω]
  ring


/-- Request (A): the formula-level JL identity with general parameters. For squarefree `D` with `ω(D)` odd and any
`c`, `F`, `G`, the twisted parameters at `d ∣ D` are `ψ(d)c`, `F_d = F · ∏_{p ∣ d} m^{(1)}_p` and `2^{ω(d)} G`. -/
@[tf_id "III.ef.thm:jl-formula-identity-general"]
theorem jl_formula_identity_general (D k n : ℕ) (c : ℚ) (F : ℤ → ℕ → ℤ → ℚ) (G : ℕ → ℕ → ℚ)
    (hD : Squarefree D) (hω : Odd (ω D)) :
    eichlerBGen D k n c F =
      -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzESGen k n (dedekindPsi d * c)
          (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ))
          (fun a a' ↦ (2 : ℚ) ^ ω d * G a a') := by
  obtain ⟨-, h4b, h4c⟩ := signedDivisorSum_constants hD
  have h4b' : ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ ω d = 0 := by
    exact_mod_cast h4b (one_lt_of_odd_omega hω)
  have hpsi : ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * dedekindPsi d = ∏ p ∈ D.primeFactors, ((p : ℚ) - 1) := by
    have h := h4c 1 (Nat.coprime_one_right D)
    simp only [mul_one, dedekindPsi_one_gen, one_mul] at h
    exact h
  -- expand the right side by the boundary split
  have hsplit : -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzESGen k n (dedekindPsi d * c)
          (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ))
          (fun a a' ↦ (2 : ℚ) ^ ω d * G a a') =
      ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
          ((if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * (dedekindPsi d * c)) +
        ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
          eichlerEllipticGen k n (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) +
        (∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ ω d) *
          (cohenA3Gen k n G + (1 / 2) * eisensteinCorrectedGen k n G) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [lefschetz_es_general_boundary_split, cohenA3Gen_const_mul, eisensteinCorrectedGen_const_mul]
    ring
  rw [hsplit, h4b', zero_mul, add_zero]
  have hcen : ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        ((if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * (dedekindPsi d * c)) =
      (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) *
        (∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) * c := by
    rw [← hpsi, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcen, sum_mul_eichlerEllipticGen D.divisors (fun d ↦ (-2 : ℚ) ^ ω (D / d))
    (fun d Δ ↦ ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) k n F]
  simp only [sum_signed_localFactorEichler_gen hD hω]
  unfold eichlerBGen
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold weightedClassNumber
  ring

/-- Request (B): the identity at an index `m`. The coefficient at `d ∣ D` is
`s_d(m) = (−1)^{ω(D/d)} 2^{ω(D/d) − ω(gcd(D/d, m))}`, the elliptic factor at `p ∣ d` is `e_p` if `p ∣ m` and
`m^{(1)}_p` otherwise, and the boundary factor is `2^{ω(d) − ω(gcd(d, m))} G`. The central terms are removed by
`¬ IsSquare n ∨ c = 0`. -/
@[tf_id "III.ef.thm:jl-formula-identity-ramified-index"]
theorem jl_formula_identity_ramified_index (D m k n : ℕ) (c : ℚ) (F : ℤ → ℕ → ℤ → ℚ) (G : ℕ → ℕ → ℚ)
    (hD : Squarefree D) (hω : Odd (ω D)) (hc : ¬ IsSquare n ∨ c = 0) :
    eichlerBGen D k n c F =
      -(1 / 2 : ℚ) * ∑ d ∈ D.divisors,
        (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
          lefschetzESGen k n (dedekindPsi d * c)
            (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors,
              (if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ)))
            (fun a a' ↦ (2 : ℚ) ^ (ω d - ω (Nat.gcd d m)) * G a a') := by
  have hD1 := one_lt_of_odd_omega hω
  have hCc : (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * c = 0 := by
    rcases hc with h | h
    · simp only [h, ite_false, zero_mul]
    · rw [h, mul_zero]
  -- the signed boundary sum vanishes
  have hbd : ∑ d ∈ D.divisors, (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
      (2 : ℚ) ^ (ω d - ω (Nat.gcd d m)) = 0 := by
    rw [Finset.sum_congr rfl fun d hd => by
      rw [signed_coeff_eq_prod hD.ne_zero (Nat.dvd_of_mem_divisors hd) m,
        boundary_coeff_eq_prod (Nat.pos_of_mem_divisors hd).ne' m]]
    rw [sum_divisors_prod_eq_prod_add (fun p ↦ if p ∣ m then (1 : ℚ) else 2)
      (fun p ↦ if p ∣ m then (-1 : ℚ) else -2) hD]
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hD1
    exact Finset.prod_eq_zero hp (by split_ifs <;> norm_num)
  have hsplit : -(1 / 2 : ℚ) * ∑ d ∈ D.divisors,
        (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
          lefschetzESGen k n (dedekindPsi d * c)
            (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors,
              (if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ)))
            (fun a a' ↦ (2 : ℚ) ^ (ω d - ω (Nat.gcd d m)) * G a a') =
      ∑ d ∈ D.divisors, (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
          eichlerEllipticGen k n (fun t f Δ ↦ F t f Δ * ∏ p ∈ d.primeFactors,
            (if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ))) +
        (∑ d ∈ D.divisors, (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)) *
          (2 : ℚ) ^ (ω d - ω (Nat.gcd d m))) *
          (cohenA3Gen k n G + (1 / 2) * eisensteinCorrectedGen k n G) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [lefschetz_es_general_boundary_split, cohenA3Gen_const_mul, eisensteinCorrectedGen_const_mul]
    have h0 : (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) * (dedekindPsi d * c) = 0 := by
      rw [mul_left_comm, hCc, mul_zero]
    rw [h0]
    ring
  rw [hsplit, hbd, zero_mul, add_zero,
    sum_mul_eichlerEllipticGen D.divisors
      (fun d ↦ (-1 : ℚ) ^ ω (D / d) * (2 : ℚ) ^ (ω (D / d) - ω (Nat.gcd (D / d) m)))
      (fun d Δ ↦ ∏ p ∈ d.primeFactors,
        (if p ∣ m then (eichlerSymbol p Δ : ℚ) else (localFactorEichler p Δ : ℚ))) k n F]
  simp only [sum_signed_ramified_index hD hω m]
  unfold eichlerBGen
  rw [mul_right_comm, hCc, zero_mul, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold weightedClassNumber
  ring

/-- The statement of `III.ef.thm:jl-formula-identity`, recovered from (A) at `c = ψ(M)`, `F(t, f, Δ) = F(Δ)` and
`G(a, a') = c_M(a − a')`, using `ψ(dM) = ψ(d)ψ(M)` and `c_{dM} = 2^{ω(d)} c_M` for `gcd(d, M) = 1`. -/
@[tf_id "III.ef.cor:jl-formula-identity-from-general"]
theorem jl_formula_identity_from_general (D M k n : ℕ) (F : ℤ → ℚ) (hD : Squarefree D) (hω : Odd (ω D))
    (hDM : D.Coprime M) :
    eichlerB D M k n F =
      -(1 / 2 : ℚ) * ∑ d ∈ D.divisors, (-2 : ℚ) ^ ω (D / d) *
        lefschetzES (d * M) k n (fun Δ ↦ F Δ * ∏ p ∈ d.primeFactors, (localFactorEichler p Δ : ℚ)) := by
  rw [eichlerB_eq_general, jl_formula_identity_general D k n (dedekindPsi M) (fun _ _ Δ ↦ F Δ)
    (fun a a' ↦ (boundaryDivisorSum M ((a : ℤ) - a') : ℚ)) hD hω]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hdD hD
  have hcop : d.Coprime M := Nat.Coprime.coprime_dvd_left hdD hDM
  have hβ : (fun a a' : ℕ ↦ (boundaryDivisorSum (d * M) ((a : ℤ) - a') : ℚ)) =
      fun a a' : ℕ ↦ (2 : ℚ) ^ ω d * (boundaryDivisorSum M ((a : ℤ) - a') : ℚ) := by
    funext a a'
    rw [boundary_multiplicative d M hcop, (boundary_local_factor _).2.2 d hsq]
    push_cast
    ring
  rw [lefschetzES_eq_general, dedekindPsi_nat_mul_prime.2.1 d M hcop, hβ]

end GL2TF.Explicit
