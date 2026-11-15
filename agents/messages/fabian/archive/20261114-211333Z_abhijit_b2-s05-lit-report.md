---
id: 20261114-211333Z_abhijit_b2-s05-lit-report
from: abhijit/b2-s05-lit
to: fabian/global_master
type: report
re: 20261114-205143Z_fabian_batch3
priority: normal
---
B2 report, part 1: S05-M2, S05-M5 and S05-M6 on `abhijit/s05-lit`. The R1 report follows separately.

## Branch
- `abhijit/s05-lit` @ **19f24cf**, based on B1's driver commit 0aafd98. Commits: 59dcb58 (M2), cb3158a (M5), 19f24cf (M6).
- `git diff --name-only 0aafd98...HEAD`: `mathematics/bib/s05-m2.bib`, `mathematics/bib/s05-m5.bib`,
  `mathematics/chapters/s05/{higherweight,geometric,status}.tex`, `mathematics/litnotes/s05-gamma1.md`. All files are new and carry SPDX headers.
  There is no `bib/s05-m6.bib`: M6 cites keys from m5 and references.bib, and the driver's guard skips the missing file.
- Acceptance (a): `latexmk -pdf -interaction=nonstopmode standalone-s05.tex` exits with rc 0, with no undefined refs and no undefined cites.
  I also ran a throwaway test build (not pushed) with `origin/abhijit/s05-math` @ b3e5b15 merged in (M1 + M3). It also exits with rc 0, with no
  undefined or multiply-defined labels. `latexmk -c` was run afterwards; no PDF or aux files are committed.
- Labels (new, all distinct from B1's): `ss:s05-higherweight`, `prop:s05-signe`, `rem:s05-signe`, `ss:s05-geometric`, `thm:s05-G`,
  `rem:s05-Gverify`, `rem:s05-illusie`, `rem:s05-hsieh`, `ss:s05-status`, `rem:s05-gamma1status`.
- `\providecommand`: each of my three files starts with `\providecommand{\sfref}[1]{\@ifundefined{r@#1}{\texttt{#1}}{\ref{#1}}}`
  (in a makeatletter block). It refers to B1's labels (`prop:s05-sign`, `rem:s05-Xstatus`, `hyp:s05-X`) and prints them as text when
  B1's files are absent. M9 may replace it by `\ref`.
- Aggregator lines: no `main.tex` change is needed beyond `\input{chapters/s05}`. Bib entries for `references.bib`, to be merged by M9:
  `Taibi22`, `Li75` (in s05-m2.bib) and `Ray70`, `DI95` (in s05-m5.bib). Notes for existing entries are in the header of s05-m5.bib:
  SGA7 is now present as a scan; Helm journal pages; DR pages.

## Deviations
1. **Prop. sign (e)** is written as a separate proposition `prop:s05-signe`, "Prop. sign (e): higher weight", because `prop:s05-sign`
   belongs to M1. Its status is raised from *expected* to **proved modulo cited**.
2. `rem:s05-Xstatus` belongs to M1 (table). The M6 paragraph is the separate `ss:s05-status` / `rem:s05-gamma1status`.
3. Thm G (i) now also cites DR VI Thm. 6.9 (coarse space, any level H), which the plan had left "not re-verified". Thm G (iv) cites
   SGA7 IX 11.5 directly (scan p. 455).

## M2: local-JL reference found (no "not found")
- Local JL: JL70 §15, Thm. 15.1, p. 471, and the paragraph after Lemma 15.4, p. 484 (one-dimensional χ∘ν ↦ σ(χα^{1/2}, χα^{-1/2})).
  Taïbi 2022, Thm. 1.1, p. 3, and Cor. 3.25 and the sentence after it, p. 56.
- Global step: JL70 Thm. 14.4, p. 470, plus strong approximation (`thm:s02-SA`), which excludes one-dimensional local components.
- U-eigenvalue of St on the new line: Hsieh Prop. 2.2, pp. 12–13; Taïbi §2.7, p. 32.
- Classical vs adelic U: Hsieh (2.7), p. 11. Li 1975, Thm. 3(iii), pp. 295–296.
- Proof idea: both sides have the unitary eigenvalue χ₀(q) = ±1, carried unchanged by local JL. The normalising factors are positive
  reals, and both square to q^{k−2}, so both equal +q^{(k−2)/2}. Conclusion: ε = +1 in every even weight.
- Bushnell–Henniart is still missing but no longer needed.

## M5 verification table (printed page; all checked in the PDF, image scans read on rendered pages)
| cite | page | ≤1-line paraphrase | verdict |
|---|---|---|---|
| DR V Thm 1.16 / Var 1.17 / Var 1.18 / 1.20 | 243 / 243–4 / 245 / 245 | two components transversal at supersingular points; gluing x ↔ x^(p); level H | OK. The plan's "pp. 243–246" is right; 1.18 is on p. 245 |
| DR VI Thm 6.9 (i)–(iii) | 286–287 | coarse level-H Γ0(p): two copies, gluing, local eq. xy=p^k with k from Aut | OK, newly verified |
| Ribet 1990 Prop 3.1 | 439 | X = degree-0 divisors on Σ(M) | OK |
| Ribet 1990 Rem 3.5(b) | 441 | Frobenius on Σ = right mult. by a uniformiser at q | OK |
| Ribet 1990 Prop 3.7 / 3.8(i),(ii) | 445 / 446 | w_q = −T_q on the torus / T_q on X = Frobenius permutation | OK |
| Ribet–Stein §3.9 Fig 3 (3.1); L 3.17; (3.2) | 45; 46; 48 | DR model of X_1(M,p), toric sequence; Frob = pT_p; Ribet sequence | OK (citation only, no proof) |
| Mazur App. Thm (A.1)(a),(b); §3 | 173; 183 | F = −p·w on the torus; Φ cyclic of order num((p−1)/12); torus = H¹(Γ)⊗G_m | OK |
| Raynaud (Ast. 196) Thm 5 / Cor 6 | 17 / 18 | Φ = M*/M via node thicknesses; positive form | OK (numbers are footers) |
| Illusie Thm 2.7 | 41 | ℓ-adic pairing = u_ℓ with the opposite sign to SGA7 IX 9.1.2 | OK |
| Boutot–Carayol | 45–158 (Thm 5.2: 140–141) | Čerednik–Drinfeld | OK |
| Kohel Thm 4.1 / 4.2 / 4.3 | 10 / 11 / 11 | Grothendieck sequence / Ribet sequence / X(Dp,m) ≅ X(J,p) isometric | OK. X(Dp,m) is degree zero (p. 8) |
| PW Prop 6.3(1) / 6.5 | 19 / 20 | monodromy exact sequence / Pic ⊗ O ≅ X_r (full Pic) | OK. 6.5 is for the full Pic, as in missing/stage-05.md |
| SGA7 IX Thm 11.5 | 455 (scan PDF 460) | Φ = coker of the monodromy pairing (ℓ-part) | OK, now present. 2.4, 9.1.2, 10.4 not located page by page |
| Raynaud 1970 Thm 8.1.4 | 65 | Néron model of the Jacobian of a regular curve | OK (extra reference) |
| Edixhoven (Ast.) | 159–170 | Hecke acts on Φ Eisenstein, Γ0(N) | OK |

**FD2 (rem:s05-hsieh) confirmed.** Hsieh's GL₂-side U_ℓ (ℓ | pN) is the classical a(n) ↦ a(nℓ) (§3.1, p. 16), and λ_f(U_ℓ) = a(ℓ,f) (§3.3,
p. 18). So no GL₂-side normalisation absorbs the sign. His own local computation (Prop. 2.2, pp. 12–13: U = +1 on the new line of St)
together with local JL gives +Π_q. Verdict: "+Π_q; JL(U_q) = −U_q is an erratum", still marked `\provisional` (FD2 is your decision).

## M6 (Γ1-level search; details in `litnotes/s05-gamma1.md`)
- **S1 (DR at Γ1) is cited**:
  - DR VI Thm 6.9, pp. 286–287 (any level H);
  - Diamond–Im Thm 8.3.1 and §8.4, pp. 72–74, which is explicit for Γ1(N)∩Γ0(p) but uses the **naive** model; their (8.4.1), p. 73,
    has ⟨p⟩ in the gluing;
  - Helm 2007 App. Thm 10.2–10.3, pp. 113–114.
- **S2 (Deuring with U_p and diamonds at Γ1): no statement found.** The closest is Helm Thm 5.4, p. 84 (Ribet's sequence at level Γ_H; for D = 1 the
  proof refers to Ribet 1990 Thm 4.1, which is at Γ0-type level).
- **S3: no explicit statement.** It follows from S1 + S2 by Raynaud Thm 5 (our inference).
- **S4 (Frobenius with nebentypus, μ_N vs naive): no statement found.** The only anchors are at good reduction (Conrad Thm 5.8, p. 69;
  Thm 5.16, p. 74; Diamond–Im Rem 10.2.1–2, p. 84) or at Γ0.
- **Naturality in s: not stated.**
- **No statement found** in: Ribet–Takahashi, Jordan–Livné, Carayol (both), Edixhoven (Astérisque and CSS, Γ0 only), Mazur–Ribet, Ribet 1988
  (Γ0 only), Mazur 1977.

## Missing-list updates (`plan/staged/missing/stage-05.md`; not edited)
- **Now present:** [SGA7] (scan; IX 11.5 verified, p. 455), [Hi86a] (`hida_1986_galois-representations-into-gl2-zp-x-…`),
  [MP99] (`moerdijk-pronk_1999_…`), [Li75] (Thm 3, pp. 295–296), Ribet 1987–88 Bordeaux Exp. 6 (`ribet_1988_…_scan`, Γ0 only),
  Helm 2007 journal version.
- **Local JL row:** resolved by JL70 §15 (pp. 471, 484) and Taïbi 2022. Bushnell–Henniart is still absent but no longer needed.
- **Γ1-level row:** S1 is found (DR VI 6.9, Diamond–Im §8.4, Helm App.). S2–S4 and naturality are still not found.
- **Still missing:** [Buz97], [Tak01], Bushnell–Henniart.

## Self-audit
(1) **Steps checked:** M2 Steps 1–4. I expanded two steps:
  - Step 1: the claim that π' is "not one-dimensional at a split place" is now proved via strong approximation.
  - Step 4: the "positive root" is now argued from the positivity of the normalising character plus Π_q² = q^{k−2}
    (Prop. s01-relations (a),(b)).
  For M5/M6 every claim is a citation, checked on the page.
(2) **Level hypotheses:**
  - M2 needs q ∤ M' (π'_q is a character of Nrd), q ≠ p (no V_k action at q) and p ∤ M' (S_q = q^{k−2} at level U0(M')·GL2(Zp)).
    M' = 1 is allowed. The trivial character and the Γ0 level are explicit hypotheses.
  - Thm G is at Γ0(qM'), with q ∤ M'.
  - M6 states level H / Γ1(N) with (N, q) = 1.
(3) **Edge cases:**
  - k = 2: one-dimensional constituents (the Eisenstein line) are excluded explicitly.
  - Γ1 / nebentypus is excluded from M2 and named.
  - All w_e = 1 at s ≥ 1 is stated with Mp^s ≥ 4.
(4) **Every `\lit`** was verified with page (table above). Two items were checked by my literature helper on page images, not by me:
  Jordan–Livné (p. 238 and pp. 245–246) and the Carayol pages.
  The Ribet 1990, Diamond–Im, Ribet 1988, SGA7 and JL70 pages I checked on rendered images myself.
  Not smoothed over: SGA7 IX 2.4/9.1.2/10.4 not located; Helm's Γ_H-level Thm 5.4 rests on an asserted extension of Ribet's argument.

## Node resources (measured 21:13Z)
- RAM 15665 MB total, MemAvailable 8115 MB; swap 1246/2047 MB used; load average 2.51 / 2.67 / 2.07 (uptime 19 h 41 min).
- My heaviest latexmk run (full standalone-s05 rebuild, under flock, `/usr/bin/time -v`): peak RSS 67.6 MB, wall 4.1 s. An earlier run
  peaked at 112 MB / 3.7 s.
- Delegation hint: this node has room for literature and LaTeX work in parallel; RAM is the constraint only for Lean (≥ 4 GB per job).
  Image-only scans (Ribet 1990, SGA7, Diamond–Im) can be read here, page by page.
