# S06-M11 literature note: [KO] Kim-Ota, Quantitative variation of congruence ideals and integral periods of modular forms

- WP: S06-M11 (batch 2, Q3). Status of every item: *cited*. Compared with `plan/staged/stage-06-integral-defect.tex` at BASE `96bd1d8`.
- Source: `literature/kim-ota_2019_quantitative-variation-of-congruence-ideals-and-integral-periods-of-modular-forms_arxiv.pdf`
  (arXiv:1905.02926v4, 21 Apr 2023, text dated 24 April 2023; 26 pp). **All numbering/pages are those of this arXiv copy** (printed page = PDF page).
  Published: Res. Math. Sci. 10 (2023) (numbering not checked). Good text layer. Paraphrases only.
  This note is independent of the batch-1 note `s06-m6-levM.md` (branch `abhijit/s06-m6`), which treats the (Lev_M) question.

## Items
1. **Thm 1.1 (Main Theorem), p. 1; condition (6): MATCH.** Hypotheses: (1) (N,p)=1; (2) rho_f restricted to G_{Q(sqrt p*)} absolutely irreducible;
   (3) 2 <= k <= p-1; (4) (N^+,N^-)=1; (5) N^- squarefree; (6) if q | N^- and q = +-1 mod p, then rho_f is ramified at q. Conclusion: ord_lambda eta_f(N) =
   ord_lambda eta_f(N^+,N^-) + sum_{q | N^-} t_f(q) (full versus N^--new congruence ideal). Same as tex `thm:s06-KO` (p >= 5 in the opening paragraph of Sect. 1.1.1).
2. **Assumption 2.1, p. 3: MATCH.** (FL) a newform f in S_k(Gamma_0(N)), 2 <= k <= p-1, p not dividing N, with rho_f = rho; (TW) rho restricted to
   G_{Q(sqrt p*)} absolutely irreducible. So Assumption 2.1 = (H2) plus existence of f, as the tex says for M = 1 (`hyp:s06-H`, (Lev_M)).
3. **P_rho, formula (2.1), p. 3, and Lemma 2.4, p. 4 (auxiliary prime r in (2.2), p. 3: r > 3, r not 1 mod p, rho unramified at r, tr(rho(Frob_r))^2 not equal r^{k-2}(1+r)^2):** P_rho is the set of l dividing N(rho), l = -1 mod p, rho restricted to G_l irreducible but restricted to I_l reducible.
   Lemma 2.4: if Sigma contains P_rho, then T(N_{rho,Sigma})_{m_Sigma} = T_Sigma. (Used by tex (Lev_M): "P_rho in Sigma".)
4. **Thm 2.9 (DFG04, Dim09), p. 5: MATCH.** Assume Assumption 2.1 and P_rho in Sigma. Then R_Sigma -> T_Sigma is an isomorphism of finite flat complete
   intersections over O, M_{N_{rho,Sigma}} free of rank two over T_Sigma, and the Selmer group order equals O/eta_{f,Sigma}. Tex cites it only as "[KO, Thm 2.9, p. 5]". OK.
5. **Rem. 2.10, p. 5: MATCH.** The image conditions of [DFG04] and [Dim09] are interchangeable over Q. Used in tex (Im).
6. **Def. 2.12, p. 6: MATCH.** t_f(q) = largest t such that A_f[lambda^t] is unramified at q (and A_f[lambda^{t+1}] ramified); finite when q | N^-; zero when q | N(rho)
   (wording of the text). Equivalent: (lambda^{t_f(q)}) = Fitt of H^1(I_{q^2},T_f)^{G}-torsion (as the text after the definition). Cites [PW11, Def. 3.3].
7. **Formula (2.4), p. 7:** N^+_{rho,Sigma^+} = r * product over Sigma^+ of l^{c^+(l)+d(l)} * product over l not in Sigma^+, l | N(rho)^+ of l^{c^+(l)}, with r the auxiliary prime
   of (2.2). Notes: l in Sigma^+ forces l^2 | N^+_{rho,Sigma^+}; level difference with N^+ occurs only for l exactly dividing N^+ and l not dividing N(rho). Matches the use in tex `prop:s06-levM`.
8. **Thm 2.13 (Selmer computation), p. 7: MATCH.** Conditions: 2<=k<=p-1; Sigma (primes dividing N/N(rho)) contains P_rho; p, N^+, N^- pairwise coprime; N^- squarefree; for q | N^-,
   q = 1 mod p implies rho ramified at q. So only q = 1 is excluded (not -1), as the tex says in `rem:s06-minus1`(b) ("needs only q not = 1"). Conclusion (2.5) compares eta over the Sigma-imprimitive Hecke algebras.
   **Rem. 2.14, p. 7:** (2) the level N^+_{rho,Sigma^+}/r is rigid (l in Sigma^+ forces l^2 dividing it); the Selmer computation alone does not give the formula at level N^+ r l etc.
9. **Prop. 2.15 (L-value computation), p. 8, part (1): MATCH.** If every prime in Sigma^- (primes of N^- where rho is unramified) is NOT congruent to +-1 mod p, then
   ord eta^Sigma(N^Sigma_f) = ord eta^{Sigma^+}(N^+_{rho,Sigma^+}/r * N^-). This is where +-1 is excluded; tex `rem:s06-minus1`(b) says exactly this. Part (2) is an unconditional comparison.
10. **Thm 3.12 (Bockle), p. 12: MATCH.** For odd absolutely irreducible rho: G_Q -> GL_2(F_p) under (1) l not p: dim L_{l,1} - dim H^0(Q_l,ad^0) - gen(a_l) >= 0, (2) rho low-weight crystalline at p with
    the analogous inequality, (3) Assumption 2.1(TW), the deformation ring R is a complete intersection over O. Proof: "[Boc07, Cor. 4.3 and Thm 5.8]". Matches tex (Boc07 citation) - see `boc07.md`.
11. **Thm 3.14, p. 12 (proof p. 13): MATCH, with the full statement as follows.** Keep Assumption 2.1; N >= 1 with N(rho) | N; Sigma, Sigma^+ finite sets of primes not equal to p with P_rho in Sigma; Sigma^- = Sigma minus Sigma^+.
    Then R^{Sigma^-}_{Sigma^+} is isomorphic to the N^--new quotient T(N^+_{rho,Sigma^+} N^-)^{N^-}_{m_{Sigma^+}}, as reduced finite flat complete intersections over O; here T(...) is the image of the S-anemic algebra T_S
    (so the algebra is anemic, as the tex's second-reader note says) and the target is the N^--new quotient (so for Sigma^- non-empty it is NOT the full level-N algebra). No condition on q mod p appears in the
    statement. Tex hypotheses "Assumption 2.1 and P_rho in Sigma": MATCH.
12. **Prop. 5.1, pp. 18-19: MATCH.** For m_f non-Eisenstein: (1) T(N)_{m_f} is Gorenstein (p. 18); (2) M_N is free over T(N)_{m_f} of rank two (p. 19). Proof: "[Dim09, Prop. 5.5]" (cf. FJ95 Thm 2.1, Vat99 Thm 1.13).
13. **Cor. 5.4, p. 19: MATCH.** If m_f non-Eisenstein and f is new at all primes dividing N^-, then M_N^{N^-} is free of rank two over the N^--new Hecke algebra and that algebra is Gorenstein.
    **Rem. 5.5, p. 19:** this is for classical forms; on Shimura curves/Hida varieties of discriminant N^- one should assume l not = +-1 mod p for residually unramified l | N^- at least. So the tex's decision to use Cor. 5.4 only for q not = 1
    is conservative but consistent; the +-1 caveat in Rem. 5.5 concerns the quaternionic side (i.e. stage 05 / (Gor_{R'})), which the tex handles through [Hs].
14. **Prop. 5.6, p. 19: MATCH.** Irreducible rho: delta_{f^Sigma}(N^Sigma_f) = delta_f(N) times product over l in Sigma of L^{nv}_l(ad^0 f,1)^{-1}. With Sect. 5.1 (p. 18): for d_0(l)=1 and pi_l special, L_l(ad^0 f,s) = (1-l^{-1-s})^{-1}, so the factor at s=1 is 1 - l^{-2}; it is a p-unit iff l not = +-1 mod p. Proof cites [DFG04, Prop. 1.4(c)]. Matches tex `rem:s06-minus1`(b).

## Mismatches / remarks
- No mismatch of theorem number or page was found for any of the 14 items.
- Thm 3.14 gives the **N^--new quotient with anemic Hecke operators**, not the full T_k(M): the tex phrase in (Lev_M) "T_k(M)_m is the Hecke algebra of [KO, Thm 3.14]" needs the repair discussed in `s06-m6-levM.md` (batch 1, P4). Not repeated here.
- Rem. 5.5 is a relevant caveat (Shimura-curve side needs l not = +-1 mod p), mention it where (Gor_{R'}) is used.
