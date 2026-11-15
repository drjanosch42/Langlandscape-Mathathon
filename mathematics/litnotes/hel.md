# S06-M11 literature note: [Hel] Helm, On maps between modular Jacobians and Jacobians of Shimura curves

- WP: S06-M11 (batch 2, Q3; the same status question is asked in S04-M5). Status: *cited*. **The published version (Israel J. Math. 160 (2007), 61-117) is now present.**
- Sources: (a) `literature/helm_2007_maps-between-modular-jacobians-and-jacobians-of-shimura-curves.pdf` (published version, 57 PDF pp; printed page = PDF page + 60, PDF 50 = p. 110);
  (b) `literature/helm_2004_maps-between-modular-jacobians-and-jacobians-of-shimura-curves_arxiv.pdf` = arXiv:math/0401265v1 (20 Jan 2004), 35 pp. Good text layers. Paraphrases only.

## Items (tex: `thm:s06-defect` "[Hel, Cor. 8.11, helm_2004... p. 31]"; [Hs, p. 34] "[Hel07, Cor. 8.11 and Rem. 8.12]")
1. **Cor. 8.11, published p. 110 (PDF 50), arXiv v1 p. 31: MATCH.** Same number in both versions. Let m be a maximal ideal of T outside S (S is a finite set of bad maximal ideals; "outside S" includes residue characteristic different from 2 and 3, by Rem. 8.12). If m is controllable at every prime dividing D, then J^D[m] and J^1[m] have the same dimension; in particular if m satisfies multiplicity one for J^{1,1} = J^1(Gamma_0(N) cap Gamma), then dim J^D[m] = 2. (Proof by Thm 8.5: [J^D]_m = [J^1]_m tensor the character groups X_p(J^min)_m, free of rank one when m is controllable.)
2. **Rem. 8.12, published p. 110, arXiv v1 p. 31: MATCH (numbering).** The corollary holds more generally (for all non-Eisenstein m) if Gamma = Gamma_0(M) or Gamma contains Gamma_1(r) with r >= 4: the only places where residue characteristic 2 or 3 matters are Prop. 5.6 and the level-raising arguments (Sect. 6 in the published version, **Sect. 7 in the arXiv v1** text), and the latter are not needed for m already controllable at every p dividing D. A small difference: the cross-reference to the level-raising section differs between the versions (Sect. 6 published, Sect. 7 arXiv); the numbers of Cor. 8.11 and Rem. 8.12 do not.
3. **Cor. 8.10, published p. 109, arXiv p. 30:** dim J^D[m] <= 2^k dim J^1[m], k the number of primes dividing D where m is not controllable (strengthens Yang). Thm 8.5 (published p. 107, arXiv p. 29), Thm 8.7 (published p. 108, arXiv p. 30). Not cited by stages 04/06.
4. Hsieh (Thm 4.5 proof, p. 34) and Pollack-Weston (before Thm 6.2, p. 19) both cite exactly "[Cor. 8.11, Rem. 8.12]": MATCH to the numbers above.

## Mismatches / remarks
- No mismatch. `plan/staged/missing/stage-04.md` worried that the numbering may differ between the 2004 preprint and the 2007 journal version for Cor. 8.11 / Rem. 8.12: it does **not**; they carry the same numbers (p. 31 in arXiv, p. 110 in the journal).
- `references.bib` (key `Hel`) currently records the arXiv file as the local copy and says journal data are "not checked": the journal data (Israel J. Math. 160 (2007), 61-117) are confirmed by the first page of the published PDF.
