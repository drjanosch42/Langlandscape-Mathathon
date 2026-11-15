# S06-M11 literature note: [PW] Pollack-Weston, On anticyclotomic mu-invariants of modular forms

- WP: S06-M11 (batch 2, Q3). Status: *cited*. Checked against `plan/staged/stage-06-integral-defect.tex` at BASE `96bd1d8`.
- Source: `literature/pollack-weston_2006_anticyclotomic-mu-invariants-of-modular-forms_arxiv.pdf` = arXiv:math/0610694v1 (23 Oct 2006), 28 pp.
  **Numbering/pages are those of arXiv v1** (printed page = PDF page). Published: Compos. Math. 147 (2011), 1353-1381 (numbering not checked; Hsieh and Kim-Ota cite "[PW11, ...]").
  Text layer good. Paraphrases only.

## Items
1. **Hypothesis CR, p. 2 (tex: "PW's (CR), p. 2", `thm:s06-KO`): MATCH, with a difference of strength.** A representation rho-bar: G_Q -> GL_2(F_p) and a squarefree product N^- of an odd number of primes, each inert in K/Q and
   including all primes where rho-bar is ramified, satisfy CR if (1) rho-bar is **surjective**; (2) for q | N^- with q = +-1 mod p, rho-bar is ramified at q. Item (2) is the same +-1 condition as [KO, Thm 1.1(6)], as the tex says.
   **Remark:** (1) is surjectivity of rho-bar, which is stronger than (H2) (absolute irreducibility on G_{Q(sqrt p*)}); the tex only compares (2).
2. **Def. 3.3, p. 9 (tex: t_f(q), "[PW, Def. 3.3, p. 9]"): MATCH.** Tamagawa exponent: t_f(l) = 0 if A_f is unramified at l; otherwise the largest t >= 0 such that A_f[p^t] is unramified at l. (Equivalent to [KO, Def. 2.12]; the exponent is about the p-torsion A_f[p^t], with f of weight two here.)
3. **Thm 6.8, p. 21 (tex: "At k = 2 it is [PW, Thm 6.8] with the definite self-pairing xi_f"): MATCH, with an extra hypothesis.** Statement: f of weight two and squarefree level N = N^+ N^- with N^- a product of an odd number of primes, (rho-bar_f, N^-) satisfies CR; then ord_p(eta_f(N)/xi_f(N^+,N^-)) = sum over l | N^- of t_f(l).
   Here xi_f(N^+,N^-) is the Gross-type self-pairing <g_f,g_f> of a generator of the f-eigenline in Pic(X_{N^+,N^-}) tensor O (the text just before the theorem; the proof combines Props 6.6, 6.7 with the Ribet-Takahashi formula [28,29]). So the "N^- has an odd number of prime factors" condition (definite case) is part of the theorem; the tex should not apply it to other parities.
4. **Cited-through items (checked because Hsieh and the stage-04 tex use them):** Prop. 6.4, p. 19: for r | N_1, (1) X_r(J)_f / xi^* X_r(A) is O-cyclic of size |k|^{t_f(r)}; (2) if X_r(J) is free over T_0(N_1/r, rN_2), then the self-pairing <g_r,g_r>_J of a generator equals the congruence number eta_f(N_1/r, rN_2) (proof: the monodromy pairing is perfect by Prop. 6.3 and then "[9, Lemma 4.17]" = DDT, Lemma 4.17; checked in the DDT preprint `darmon-diamond-taylor_1997_fermats-last-theorem_preprint.pdf`, p. 126: for a perfect Hecke-equivariant pairing on a module L with L[p] of rank d, the d-th power of the congruence ideal eta_Sigma lies in O.det(<x_i,x_j>), with equality if L is free over T_Sigma; preprint numbering). Prop. 6.5, p. 20: for each r | N^- a canonical Hecke-equivariant isomorphism Pic(X_{N^+,N^-}) tensor O = X_r(N^+ r, N^-/r), taking the intersection pairing to the monodromy pairing (proof: cites [25, Thm 4.3]). Thm 6.2, p. 19: X_r(J) is free of rank one under CR; the text near it cites Helm "[18, Cor. 8.11, Rem. 8.12]" for dim J_0(N_1,N_2)[m_f] = 2. Not used in stage 06 directly.

## Mismatches / remarks
- No mismatch of number or page. Remarks: CR(1) = surjective rho-bar (item 1), Thm 6.8 needs an odd number of primes in N^- (item 3).
- arXiv v1 is the 2006 preprint; if the published version renumbers, re-check before quoting numbers outside arXiv.
