import AlgJL.VolIII.P1.Arith
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Nat.Even

/-!
# Convention-bearing definitions: local factors, Cohen's and Eichler's expressions (Q1 U2)

Lean counterpart of `vol3/ch-iii-01-explicit.tex` §§3, 5 (definitions only) and 6 (items 8, 9, 12–17, 24, 27, 28,
30–37 of `docs/sprints/Q1-plan.md` §1.2). Definitions only, no lemmas (plan §1.3): every normalization choice of the
formula layer lives in this file. None of the expressions is a trace (plan trap 6).

Conventions:
* the Kronecker symbol `χ_Δ(p)`, the conductor test, the Eichler symbol `e_p` and the local factors `m^D_p`, `m^{(1)}_p`
  take any `p : ℕ`; A defines them for primes only, and the value at a non-prime is a B fidelity note (A1 notes item 6).
  For odd `p` the Kronecker symbol is `jacobiSym Δ p`, which is the Legendre symbol at primes (plan trap 3);
* `p ∣ cond Δ` is `Bool`-valued, used only inside `if`, never as a Prop binder (plan trap 1);
* the sums over `t ∈ ℤ` with `t² < 4n` run over `t ∈ [−2n, 2n]` filtered by `t² < 4n` (a superset of the solutions,
  since `|t| < 2√n ≤ 2n`; B fidelity note);
* `Δ_f = (t² − 4n)/f²` is integer division, exact for `f ∈ 𝓕(t, n)`;
* exponents `k − 1`, `k − 2` are truncated subtraction in `ℕ`; `(k − 1)` in `A₁` and `C(k, n)` is computed in `ℚ`;
  `r = Nat.sqrt n` when `n` is a square.
All definitions are computable. Owner: L1 (Q1).
-/

open scoped ArithmeticFunction.sigma

namespace GL2TF.Explicit

/-! ## Unit numbers and weighted class numbers -/

/-- The unit number `w(Δ) = 6` if `Δ = −3`, `4` if `Δ = −4`, and `2` otherwise. -/
@[tf_id "III.ef.def:unit-number"]
def unitNumber (Δ : ℤ) : ℕ :=
  if Δ = -3 then 6 else if Δ = -4 then 4 else 2

/-- The weighted class number `h_w(Δ) = 2 h(Δ) / w(Δ) ∈ ℚ`. -/
@[tf_id "III.ef.def:weighted-class-number"]
def weightedClassNumber (Δ : ℤ) : ℚ :=
  2 * (classNumberForms Δ : ℚ) / (unitNumber Δ : ℚ)

/-! ## §3 Kronecker symbol, Eichler symbol, local factors -/

/-- The Kronecker symbol `χ_Δ(p)` at `p`: for `p = 2`, `0` if `Δ` is even, `1` if `Δ ≡ ±1 (mod 8)`, `−1` if
`Δ ≡ ±3 (mod 8)`; for `p ≠ 2`, the Jacobi symbol `(Δ/p)` (the Legendre symbol when `p` is an odd prime). -/
@[tf_id "III.ef.def:kronecker-prime"]
def kroneckerPrime (Δ : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then
    (if Δ % 2 = 0 then 0 else if Δ % 8 = 1 ∨ Δ % 8 = 7 then 1 else -1)
  else jacobiSym Δ p

/-- `p ∣ cond Δ`: `p² ∣ Δ` and `Δ/p² ≡ 0, 1 (mod 4)`. `Bool`-valued (plan trap 1). -/
@[tf_id "III.ef.def:conductor-prime"]
def dividesConductor (p : ℕ) (Δ : ℤ) : Bool :=
  decide ((p : ℤ) ^ 2 ∣ Δ ∧ (Δ / (p : ℤ) ^ 2 % 4 = 0 ∨ Δ / (p : ℤ) ^ 2 % 4 = 1))

/-- The Eichler symbol `e_p(Δ) = 1` if `p ∣ cond Δ`, and `χ_Δ(p)` otherwise. -/
@[tf_id "III.ef.def:eichler-symbol"]
def eichlerSymbol (p : ℕ) (Δ : ℤ) : ℤ :=
  if dividesConductor p Δ then 1 else kroneckerPrime Δ p

/-- The local factor at a prime dividing the discriminant of `𝔹`: `m^D_p(Δ) = 1 − e_p(Δ)`. -/
@[tf_id "III.ef.def:local-factor-ramified"]
def localFactorRamified (p : ℕ) (Δ : ℤ) : ℤ :=
  1 - eichlerSymbol p Δ

/-- The local factor at a prime exactly dividing the level: `m^{(1)}_p(Δ) = 1 + e_p(Δ)`. -/
@[tf_id "III.ef.def:local-factor-eichler-prime"]
def localFactorEichler (p : ℕ) (Δ : ℤ) : ℤ :=
  1 + eichlerSymbol p Δ

/-! ## §4 Cohen's `μ` -/

/-- Cohen's `μ_N(t, f, n) = ψ(N)/ψ(N/N_f) · #{x ∈ {0, …, N − 1} : N N_f ∣ x² − tx + n}` with `N_f = gcd(N, f)`;
`μ_0 = 0`. -/
@[tf_id "III.ef.def:cohen-mu"]
def cohenMu (N : ℕ) (t : ℤ) (f n : ℕ) : ℚ :=
  if N = 0 then 0 else
    dedekindPsi N / dedekindPsi (N / Nat.gcd N f) *
      (((Finset.range N).filter fun x : ℕ =>
        ((N * Nat.gcd N f : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - t * x + n).card : ℚ)

/-! ## §5 The boundary divisor sum and the Eisenstein expressions -/

/-- The boundary divisor sum `c_N(m) = ∑_{τ ∣ N, gcd(τ, N/τ) ∣ m} φ(gcd(τ, N/τ)) ∈ ℕ`; `c_0(m) = 0`. -/
@[tf_id "III.ef.def:boundary-divisor-sum"]
def boundaryDivisorSum (N : ℕ) (m : ℤ) : ℕ :=
  ∑ τ ∈ N.divisors.filter (fun τ => ((Nat.gcd τ (N / τ) : ℕ) : ℤ) ∣ m), Nat.totient (Nat.gcd τ (N / τ))

/-- The corrected Eisenstein expression `Ẽis(N, k, n) = ∑_{aa' = n} a'^{k−1} c_N(a − a')`. -/
@[tf_id "III.ef.def:eisenstein-expression-corrected"]
def eisensteinCorrected (N k n : ℕ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (x.2 : ℚ) ^ (k - 1) * (boundaryDivisorSum N ((x.1 : ℤ) - x.2) : ℚ)

/-- The Eisenstein expression `Eis(N, k, n) = Ẽis(N, k, n) − δ_{k,2} σ₁(n)`. -/
@[tf_id "III.ef.def:eisenstein-expression"]
def eisensteinExpr (N k n : ℕ) : ℚ :=
  eisensteinCorrected N k n - (if k = 2 then (σ 1 n : ℚ) else 0)

/-! ## §6 Cohen's terms `A₁`–`A₄`, the Eichler elliptic term, `Λ^{ES}`, `E^𝔹` -/

/-- `A₁(N, k, n) = (k − 1)/12 · ψ(N) · r^{k−2}` if `n = r²`, else `0` (`k − 1 ∈ ℚ`, `k − 2` truncated). -/
@[tf_id "III.ef.def:cohen-a1"]
def cohenA1 (N k n : ℕ) : ℚ :=
  if IsSquare n then ((k : ℚ) - 1) / 12 * dedekindPsi N * (Nat.sqrt n : ℚ) ^ (k - 2) else 0

/-- `A₂(N, k, n) = −½ ∑_{t² < 4n} P_k(t, n) ∑_{f ∈ 𝓕(t, n)} h_w(Δ_f) μ_N(t, f, n)`. -/
@[tf_id "III.ef.def:cohen-a2"]
def cohenA2 (N k n : ℕ) : ℚ :=
  -(1 / 2) * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
    (heckePoly k t n : ℚ) *
      ∑ f ∈ orderIndexSet t n,
        weightedClassNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * cohenMu N t f n

/-- `A₃(N, k, n) = −½ ∑_{aa' = n} min(a, a')^{k−1} c_N(a − a')`. -/
@[tf_id "III.ef.def:cohen-a3"]
def cohenA3 (N k n : ℕ) : ℚ :=
  -(1 / 2) * ∑ x ∈ n.divisorsAntidiagonal,
    (min x.1 x.2 : ℚ) ^ (k - 1) * (boundaryDivisorSum N ((x.1 : ℤ) - x.2) : ℚ)

/-- `A₄(k, n) = σ₁(n)` if `k = 2`, else `0`. -/
@[tf_id "III.ef.def:cohen-a4"]
def cohenA4 (k n : ℕ) : ℚ :=
  if k = 2 then (σ 1 n : ℚ) else 0

/-- Cohen's expression `T^C(N, k, n) = A₁ + A₂ + A₃ + A₄` (an expression, not a trace). -/
@[tf_id "III.ef.def:cohen-trace-expression"]
def cohenTraceExpr (N k n : ℕ) : ℚ :=
  cohenA1 N k n + cohenA2 N k n + cohenA3 N k n + cohenA4 k n

/-- The Eichler elliptic expression `A₂^E(k, n; F) = −½ ∑_{t² < 4n} P_k(t, n) ∑_{f ∈ 𝓕(t, n)} h_w(Δ_f) F(Δ_f)`. -/
@[tf_id "III.ef.def:eichler-elliptic-expression"]
def eichlerElliptic (k n : ℕ) (F : ℤ → ℚ) : ℚ :=
  -(1 / 2) * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
    (heckePoly k t n : ℚ) *
      ∑ f ∈ orderIndexSet t n,
        weightedClassNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) * F ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2)

/-- The Eichler–Selberg Lefschetz expression
`Λ^{ES}(N, k, n; F) = δ_{k,2} σ₁(n) − 2(A₁ + A₂^E(F) + A₃ + A₄) − Eis(N, k, n)`. -/
@[tf_id "III.ef.def:lefschetz-es-expression"]
def lefschetzES (N k n : ℕ) (F : ℤ → ℚ) : ℚ :=
  (if k = 2 then (σ 1 n : ℚ) else 0) -
    2 * (cohenA1 N k n + eichlerElliptic k n F + cohenA3 N k n + cohenA4 k n) - eisensteinExpr N k n

/-- Eichler's expression
`E^𝔹(D, M, k, n; F) = C(k, n) ∏_{p ∣ D}(p − 1) · ψ(M) + ∑_{t² < 4n} P_k(t, n) ∑_{f ∈ 𝓕(t, n)} (h/w)(Δ_f) ∏_{p ∣ D} m^D_p(Δ_f) · F(Δ_f)`
with `C(k, n) = (k − 1)/12 · r^{k−2}` if `n = r²` and `0` otherwise. -/
@[tf_id "III.ef.def:eichler-b-expression"]
def eichlerB (D M k n : ℕ) (F : ℤ → ℚ) : ℚ :=
  (if IsSquare n then ((k : ℚ) - 1) / 12 * (Nat.sqrt n : ℚ) ^ (k - 2) else 0) *
      (∏ p ∈ D.primeFactors, ((p : ℚ) - 1)) * dedekindPsi M +
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
      (heckePoly k t n : ℚ) *
        ∑ f ∈ orderIndexSet t n,
          (classNumberForms ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) /
              (unitNumber ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ) *
            (∏ p ∈ D.primeFactors, (localFactorRamified p ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2) : ℚ)) *
            F ((t ^ 2 - 4 * n) / (f : ℤ) ^ 2)

end GL2TF.Explicit
