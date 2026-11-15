# S06-M11 literature note: [Dia89] Diamond, On congruence modules associated to Lambda-adic forms

- WP: S06-M11 (batch 2, Q3). Status: *cited*. Checked against `plan/staged/stage-06-integral-defect.tex` at BASE `96bd1d8`.
- Source: `literature/diamond_1989_congruence-modules-associated-to-lambda-adic-forms.pdf` (numdam, Compos. Math. 71 (1989), 49-83, 36 PDF pp; **journal page = PDF page + 47**, PDF 14 = p. 61, PDF 33 = p. 80).
  The text layer has lost most Greek letters (they appear as unicode escapes), but theorem numbers, pages and the shape of the statements are readable. Paraphrases only.

## Items
1. **Thm 4A, p. 61 (tex: "Thm 4A p. 61", `prop:s06-betti`(b)): MATCH.** Classical weight two: f a newform in S_2(Gamma_0(N), chi; K) of level N, l a prime, alpha a root of x^2 - a_l x + chi(l) l (hypothesis: K contains the roots), f_alpha = f - beta f(lz) of level Nl. Then the congruence module of f_alpha in the space of forms of level Nl and Gamma-type (3.7) is O_K/(alpha^2 - chi(l)) up to the usual identification (the annihilator is (alpha^2 - chi(l))). Chapter 4 assumes p odd (p = 2 is treated in Chapter 7, p. 81, where an error term appears). Thm 4B (p. 63, sign-xi part: (a_l - zeta(l+1))) and Thm 4C (p. 64: distinct newforms congruent to f at level Nl when alpha^2 - chi(l)(l+1)... divides) refine it. These are the Diamond versions of Ribet's level raising.
2. **Thm 6A-6C, p. 80 (tex: "Thm 6A-6C, p. 80", `def:s06-ctam`): MATCH.** Lambda-adic analogues. F a Lambda-adic newform, L large enough; F_alpha = F - beta F(lz): Thm 6A: div(a) = -div(alpha^2 - psi(l)) for the congruence module O_L/a of F_alpha. Thm 6B (sign-xi part, xi a root of x^2 - psi(l) in O_L): div(b) = -div(a_l - xi(l+1)). Thm 6C: ideals I_i in O_L and distinct Lambda-adic newforms (level divisible by l) congruent to F modulo the ideals; for L large. The tex's description ("computes the specialisation along the *old* branch: div(b) = -div(a_q - xi(q+1)) for the sign-xi part") agrees with Thm 6B.
3. **Cor. 6.9, p. 80 (tex: "Cor. 6.9 p. 80"): MATCH.** If f is a p-stabilised newform in S_k(Gamma_0(N_0 p^r), chi; O_p) with a_l^2 - chi(l) l^{k-2}(l+1)^2 in the maximal ideal m, then there is a p-stabilised newform g of level divisible by l with f = g mod m (level raising for ordinary forms of any character and weight >= 2; proof by Krull's principal ideal theorem and Thm 6C).
4. Thm 1 (Ribet), p. 49 (Introduction), is the level-raising statement that Diamond generalises (a newform congruent to f at level Nl exists when a_l^2 = chi(l)(l+1)^2 mod p).

## Mismatches / remarks
- No mismatch of theorem number or page. Note that Thm 4A-4C are statements for classical weight-two newforms (Gamma-type groups, Chapter 4 assumes p odd); only Thm 6 and Cor. 6.9 are Lambda-adic or higher-weight. The tex cites 4A-4C only for "existence of the congruences", which is fine.
- p = 2 has an extra error term (p. 81); irrelevant for p >= 5.
