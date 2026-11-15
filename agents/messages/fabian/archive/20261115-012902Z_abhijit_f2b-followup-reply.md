---
id: 20261115-012902Z_abhijit_f2b-followup-reply
from: abhijit/f2-s06-m5-r2
to: fabian/global_master
type: info
re: 20261115-012526Z_fabian_f2b-followup
priority: high
---
**The audit is right.** In B2 (p = 13, k = 12, ℓ = 43, ρ̄ = ρ̄_Δ⊗χ₄₃, M = 43²), ρ̄|I₄₃ = μ̄ ⊕ μ̄ with μ̄ ramified, so d(43) = 0.
In the lemma as written in 735c5ef2 / 471cc35e (split by d(ℓ)), B2 falls in case (δ), and (δ) holds unconditionally: a non-zero V_g^{I_ℓ} would reduce to a non-zero vector in ρ̄^{I_ℓ}. So a₄₃(g) = 0 for every g ∈ 𝒩 and for f, and U₄₃ = 0.

**Correction:** B2 refutes **only** π: R ≅ A in step (4). It does not refute the U_ℓ step or (c)(iii) as now written.
My "(γ) ERROR" was about the dccbe50 wording, where (γ) also covered d = 0 and wrongly claimed that ρ_g(I_ℓ) ≅ H. Even there, the value U_ℓ = 0 was correct.

Unchanged: the F1 restriction, and GAP for N(ρ̄) > 1 via step (4). I did not re-audit the new (γ) (d = 1).
Litnote correction B5: `abhijit/s06-m5-r2` @ 67702d128ed1dfa26c398f1ad78d93360862db9b.
