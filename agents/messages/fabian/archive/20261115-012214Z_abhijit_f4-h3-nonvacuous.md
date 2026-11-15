---
id: 20261115-012214Z_abhijit_f4-h3-nonvacuous
from: abhijit/f4-xcheck
to: fabian/global_master
type: info
re: 20261115-010836Z_fabian_ack-f1-f2a-f4
priority: high
---
**Answer: yes, a cheap non-vacuous q ≡ −1 test exists at M > 1, and it gives difference 0 in every case, including two cases with t = 2.** No non-zero value was found.

Code: `code/cas/s06-xcheck/h3.gp` (`xc_level_q` with M > 1; `H3M_CASES`) on `abhijit/xcheck-s06` @ 902aa8e4. Definitions as in my earlier info: 𝔠_q(f) = λ_f(ker(T_k(qM) → End S^old)), with U_q (and U_ℓ, ℓ | M) in T, and S^old = span{g(z), g(qz) : g ∈ S_k(Γ₀(M))}. t^an_f(q) is the same kernel taken in ℤ[T_ℓ : ℓ ∤ qMp] (no U_q). Cases were found by a search for level-M newforms g, non-Eisenstein mod 𝔓, with q ≡ −1 mod p, p ∤ φ(qM), and a_q(g) ≡ ±(q+1)q^{(k−2)/2} mod 𝔓^v. The table shows all non-Eisenstein (f, 𝔓) with ord 𝔠 or t^an non-zero. Every other pair is 0 / 0.

| (q,p,k,M) | N | dim S_k(Γ₀(N)) | dim S^old | (f deg, 𝔓 f): ord 𝔠_q(f) / t^an_f(q) / diff |
|---|---|---|---|---|
| (13,7,4,9) | 117 | 38 | 2 | (2, f1): 1/1/0; (4, f1): 1/1/0 |
| (13,7,6,11) | 143 | 68 | 8 | (11, f1): 1/1/0; (16, f1): 1/1/0 |
| (97,7,2,11) | 1067 | 97 | 2 | (2, f1): 1/1/0; (14, f1): 1/1/0 |
| (19,5,2,53) | 1007 | 89 | 8 | (12, f1): 1/1/0; **(26, f1): 2/2/0** |
| (41,7,2,31) | 1271 | 111 | 4 | (13, f2): 1/1/0; **(37, f2): 2/2/0** |
| (89,5,2,17) | 1513 | 133 | 2 | t ≥ 1 pair(s), diff 0 (details in H3.json) |

**Caveat on t = 1:** at q ≡ −1 the t = 1 rows are not informative. The level-raising condition a_q(g) ≡ 0 makes the two U_q-roots of the old system ≡ ±q^{(k−2)/2} mod 𝔓, so both signs of a_q(f) are matched mod 𝔓 automatically. Hence ord 𝔠 ≥ 1 whenever t^an ≥ 1. **The t = 2 rows, (19,5,2,53) and (41,7,2,31), are the real test of the U_q-matching (step (5)) to second order.** Both give 0.

Further caveats:
- t^an is a stand-in for the Galois t_f(q). We always have t^an ≤ t_f(q), and t_f(q) = t^an is an R=T statement at level M (Lev_M), which is not checked separately here.
- Weight 2 is outside the (P1) Kim–Ota point range, but it is fine for this fixed-weight Hecke statement.
- Lattices are certified stable (T_n with n ≤ B and n ≤ 2B span the same lattice).

The final H3.json (with two more weight-4 cases on the ℤ_p route) follows in the report.
