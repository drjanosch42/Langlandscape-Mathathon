# Missing literature — Langlandscape

## 2026-11-14 — P1 staged plan (plan/staged/)

Sources: plan/staged/missing/stage-01.md … stage-06.md (read only). Not committed (literature/ is git-ignored).

### Missing references (29 items)

Sorted by priority (high, medium, low). Cross-stage duplicates are merged: Ribet 1984, Hida 1986a, Mazur–Wiles 1986, SGA 7 IX and Ribet 1988 (Bordeaux). Böckle 2007 and Moerdijk–Pronk 1999 occur in one stage only.

**High**

1. **Casselman 1973.** W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314. DOI 10.1007/BF01428197.
   Why: local newform theory for K_1(p^n) with the U_p = Σ π((p j; 0 1)) operator; the cleanest citable source to identify N_Up with the classical U_p (Remark rem:s01-Upconv, HACS H4).
   Stages: 01. Priority: high.

2. **Hijikata–Pizer–Shemanske 1989.** H. Hijikata, A. Pizer, T. Shemanske, "The basis problem for modular forms on Γ_0(N)", Mem. Amer. Math. Soc. 82 (1989), no. 418.
   Why: full proof of the Brandt-module form of classical JL at all levels; only the 1980 announcement is present.
   Stages: 01. Priority: high.

3. **Miyake 1989.** T. Miyake, *Modular Forms*, Springer Monographs in Mathematics, Springer 1989 (repr. 2006), Thms. 5.2.9–5.2.10 (strong approximation over ℚ). ISBN 978-3-540-29592-1.
   Why: a ℚ-specific proof of SA for B¹. Voight §28.7 cites it for F = ℚ; the most likely blueprint for Lean milestone L02.SA and math milestone M02.4.
   Stages: 02. Priority: high.

4. **Ribet 1984 (ICM).** K. A. Ribet, "Congruence relations between modular forms", Proc. ICM Warszawa 1983, vol. 1, PWN, Warsaw 1984, 503–514.
   Why: classical source of level raising and of the Betti level-raising module coker(Ψ*Ψ) (Def. s03-LR); definite analogue Prop. s03-LRdef; structure of the old/new congruence module (Prop. s06-betti (b)). Also Hsieh's source for Ihara's lemma ([Hs, p. 68]: "[Rib84, Thm 4.1]").
   Stages: 03 (high), 06 (high). Priority: high.

5. **Hida 1986a.** H. Hida, "Galois representations into GL₂(ℤ_p[[X]]) attached to ordinary cusp forms", Invent. Math. 85 (1986), 545–613.
   Why: Λ-adic Galois representations behind ρ̄_m in Hyp CR_D (stage 04); Λ-freeness of Hida's ordinary Tate module 𝒯 in Prop. Xlambda (d), and compatibility in s of Prop. Xiso (stage 05); ρ_F (Def. s06-tam) currently obtained from the freeness of H via [Hs]/[Wi95] (stage 06).
   Stages: 04 (medium), 05 (high), 06 (low). Priority: high (highest over stages).

6. **SGA 7 IX.** A. Grothendieck, "Modèles de Néron et monodromie", in: SGA 7 I (Groupes de monodromie en géométrie algébrique), Exposé IX, Lecture Notes in Math. 288, Springer 1972, 313–523 (pages from stage 03; stage 05 gives no pages).
   Why: stage 03: dictionary X(G) / monodromy pairing / component group (remark only, Rem. s03-grothendieck; used by stage 05). Stage 05: orthogonality theorem (2.4), monodromy pairing (10.4), component group (11.5); filtration and graded pieces in (X4). Currently cited only through Raynaud (Astérisque 196–197), Kohel Thm 4.1, PW Prop 6.3.
   Stages: 03 (medium), 05 (high). Priority: high.

7. **Helm 2007.** D. Helm, "On maps between modular Jacobians and Jacobians of Shimura curves", Israel J. Math. 160 (2007), 61–117 (published version).
   Why: Hsieh Thm 4.5 proof; numbering (Cor. 8.11 / Rem. 8.12) to be checked against the published version. Only the 2004 arXiv preprint is present (see unusable list).
   Stages: 04. Priority: high.

**Medium**

8. **Eichler 1973.** M. Eichler, "The basis problem for modular forms and the traces of the Hecke operators", in: Modular Functions of One Variable I, LNM 320, Springer (1973), 75–152.
   Why: classical Brandt-matrix / JL statement over ℚ, squarefree level ([Eic73] in Voight).
   Stages: 01. Priority: medium.

9. **Gelbart 1975.** S. Gelbart, *Automorphic Forms on Adele Groups*, Ann. of Math. Stud. 83, Princeton (1975), §3.
   Why: standard adelic ↔ classical dictionary (diamond inversion, U_p); needed to pin the flag in Prop. s01-relations(a).
   Stages: 01. Priority: medium.

10. **Pizer 1976.** A. Pizer, "On the arithmetic of quaternion algebras II", J. Math. Soc. Japan 28 (1976), 676–688.
    Why: mass / class-number formulas for Eichler orders (the present file is the 1980 algorithm paper, scan only).
    Stages: 01. Priority: medium.

11. **Kneser 1966.** M. Kneser, "Strong approximation", in: Algebraic Groups and Discontinuous Subgroups (Boulder 1965), Proc. Sympos. Pure Math. 9, AMS 1966, 187–196. Pages/volume from memory; details to be checked.
    Why: original proof for simply connected groups. Kneser's 1969 Tata lectures (present) only state it (Sublemma b, p. 94).
    Stages: 02. Priority: medium.

12. **Swan 1980.** R. G. Swan, "Strong approximation and locally free modules", in: Ring Theory and Algebra III (Norman 1979), Lecture Notes in Pure and Appl. Math. 55, Dekker 1980, 153–223. Pages/volume from memory; details to be checked.
    Why: source of Voight's second proof (§28.8). The group-theoretic route may avoid the quadratic-embedding local–global step; to be assessed for Lean.
    Stages: 02. Priority: medium.

13. **Ludwig–Merten Lean repository.** Code (Lean v4.19.0), linked from arXiv:2505.12933.
    Why: port of `BTtree` and `laplace_surjective` for L02.1(a). This is code, not literature: record the commit hash when fetched.
    Stages: 02. Priority: medium.

14. **Ihara 1975.** Y. Ihara, "On modular curves over finite fields", in: Discrete Subgroups of Lie Groups and Applications to Moduli (Bombay 1973), Oxford Univ. Press 1975, 161–202.
    Why: original Ihara lemma (GL₂ side, Conj. s03-iharaGL2). (Ihara 1966 is present but not cited there.)
    Stages: 03. Priority: medium.

15. **Mazur–Wiles 1986.** B. Mazur, A. Wiles, "On p-adic analytic families of Galois representations", Compositio Math. 59 (1986), no. 2, 231–264.
    Why: Gorenstein property of Hida's Λ-adic Hecke algebra ([Hs, p. 4]: [MW86, §9 Prop. 2]); the Gorenstein input cited by Hsieh §1.4. The file `mazur-wiles_1984_*` is the class-field paper, a different work.
    Stages: 04 (medium), 06 (medium). Priority: medium.

16. **Moerdijk–Pronk 1999.** I. Moerdijk, D. A. Pronk, "Simplicial cohomology of orbifolds", Indag. Math. (N.S.) 10 (1999), no. 2, 269–293.
    Why: simplicial-orbifold language of §11 / O2 (only the 1997 K-theory paper is present).
    Stages: 05. Priority: medium.

17. **Buzzard 1997.** K. Buzzard, "Integral models of certain Shimura curves", Duke Math. J. 87 (1997), 591–612.
    Why: Shimura-curve version of Hyp.X (O4); Kohel Thm 4.3 rests on it.
    Stages: 05. Priority: medium.

18. **Local JL for Steinberg.** C. J. Bushnell, G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren 335, Springer 2006, §56 (JL for GL₂); alternative: JL70 §15–16 (full data for JL70 not given in the input; details to be checked).
    Why: Prop. sign (e): JL(St ⊗ χ) = χ∘Nrd, to pin ε at higher weight.
    Stages: 05. Priority: medium.

19. **Γ₁-level DR / Deuring reference.** Any reference stating (X1)–(X3) at Γ₁(Mp^s) ∩ Γ₀(q) level with diamonds and U_p. None found. Candidates: Ribet, Bordeaux (see Ribet 1988 below); Edixhoven, Astérisque 196–197, pp. 159–170 (present, but treats Γ₀).
    Why: status of Hyp.X beyond Γ₀ (Remark Xstatus).
    Stages: 05. Priority: medium.

20. **Ribet 1988 (Bordeaux).** K. A. Ribet, "On the component groups and the Shimura subgroup of J₀(N)", Sém. Théorie des Nombres de Bordeaux 1987–88, Exp. 6.
    Why: proof of [Ri90, Thm 3.22] (antidiagonal in the kernel), definite analogue of Prop. s03-LRdef / s03-phieis (stage 03, low); candidate for the Γ₁-level DR reference (stage 05, medium).
    Stages: 03 (low), 05 (medium). Priority: medium.

21. **Böckle 2007.** G. Böckle, "Presentations of universal deformation rings", in: L-functions and Galois Representations (Durham 2004), LMS Lecture Note Ser. 320, Cambridge Univ. Press 2007, 24–58.
    Why: the seed's unreferenced "Böckle's presentation"; used inside [KO, Thm 3.12] (via [Böc07, Cor. 4.3, Thm 5.8]). Needed only to audit KO.
    Stages: 06. Priority: medium.

**Low**

22. **Brzezinski 1990.** J. Brzezinski, "On automorphisms of quaternion orders", J. Reine Angew. Math. 403 (1990), 166–186.
    Why: general mass formula ([Brz90, (4.6)] in Voight Main Thm 25.3.19); only if non-Eichler levels appear.
    Stages: 01. Priority: low.

23. **Reiner 2003.** I. Reiner, *Maximal Orders*, LMS Monographs 28, Oxford 2003 (orig. Academic Press 1975), §34. Pages/volume from memory; details to be checked.
    Why: alternative textbook proof for norm-one groups of orders; Voight 28.6 cites it.
    Stages: 02. Priority: low.

24. **Kleinert 2000.** E. Kleinert, *Units in Skew Fields*, Progress in Math. 186, Birkhäuser 2000, §4.2. Pages/volume from memory; details to be checked.
    Why: exposition of the second proof (cited by Voight §28.8).
    Stages: 02. Priority: low.

25. **Kurihara 1979.** A. Kurihara, "On some examples of equations defining Shimura curves and the Mumford uniformization", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 25 (1979), 277–300. Pages/volume from memory; details to be checked.
    Why: explicit quotient graphs Γ\T for small discriminants; independent cross-check of T2 and Remark rem:s02-torsion.
    Stages: 02. Priority: low.

26. **Emerton 2002.** M. Emerton, "Supersingular elliptic curves, theta series and weight two modular forms", J. Amer. Math. Soc. 15 (2002), 671–714.
    Why: explicit component group / Gross lattice computations; cross-check for T1.
    Stages: 03. Priority: low.

27. **Li 1975.** W.-C. W. Li, "Newforms and functional equations", Math. Ann. 212 (1975), 285–315.
    Why: a_q² = χ(q) q^{k−2} for q ∥ N (Prop. sign (c)); currently via Ribet–Stein Lemma 3.15.
    Stages: 05. Priority: low.

28. **Takahashi 2001.** S. Takahashi, "Degrees of parametrizations of elliptic curves by Shimura curves", J. Number Theory 90 (2001), 74–88.
    Why: the formulation of Kohel Thm 4.3 (character group ≅ definite Hecke module, isometric) is attributed to it.
    Stages: 05. Priority: low.

29. **Darmon–Diamond–Taylor 1997.** H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", Current Developments in Math. 1995 / Elliptic Curves, Modular Forms & Fermat's Last Theorem, 2nd ed., International Press 1997, 2–140.
    Why: §4.4 cohomology congruence ideals; Lemma 4.17 (used by [KO, Cor. 5.9]). A preprint is present but was not checked for these numbers.
    Stages: 06. Priority: low.

### Present in literature/ but unusable or unverified (12 items)

Note: `ribet_1990_*` and `ribet_1983_*` are image-only scans that were read via local OCR (ocrmypdf); they are usable. For Ri90, PDF page = journal page − 430.

1. **Shimizu 1965.** Ann. of Math. 81 (1965), 166–193. Present as a scan only, without an OCR text layer; statements could not be verified by text search. Need an OCR copy. Stage 01 (low).
2. **Pizer 1980.** J. Algebra 64 (1980), 340–390. Present as a scan only, without an OCR text layer. Need an OCR copy. Stage 01 (low).
3. **Hida 1988 (Ann. Math.).** H. Hida, "On p-adic Hecke algebras for GL₂ over totally real fields", Ann. of Math. (2) 128 (1988), 295–384. Present, but the statements are only partly legible; need a text-layer (OCR-clean) copy. Headers are locatable (Thm 8.6 p. 362, Thm 9.4 p. 369, Thm 10.1 p. 370, Cor 10.4 p. 373). Original source of definite-side control and Λ-freeness. Stage 04 (medium).
4. **Wiles 1995.** A. Wiles, "Modular elliptic curves and Fermat's Last Theorem", Ann. of Math. 141 (1995), 443–551. Present (`wiles_1995_*`), but Thm 2.1 / Cor. 2 p. 482 not verified. Hsieh's Gorenstein / freeness input. Stage 04 (high); verify in stage 06.
5. **Hida 1988 (Amer. J. Math.).** H. Hida, "Modules of congruence of Hecke algebras and L-functions associated with cusp forms", Amer. J. Math. 110 (1988), 323–382 ([Hid88a]). Present (`hida_1988_modules-of-congruence-*`); pp. 363–366 underlie Hsieh Rem. 7.3 and need checking. Stage 04 (medium).
6. **Hida 2006 (book).** H. Hida, *Hilbert Modular Forms and Iwasawa Theory*, Oxford 2006. Present (`hida_2006_*`); Lemma 3.5 (perfectness of the Atkin–Lehner-twisted pairing) not verified. Stage 04 (low).
7. **Longo–Vigni 2011 (bibliographic data).** Present file is arXiv:0903.2797 (key `longo-vigni_2009_*`). The journal data are from memory and the inputs disagree: stage 04 gives Int. J. Number Theory 8 (2012); stage 01 gives Manuscripta Math. 135 (2011) 273–328. Details to be checked. Stages 01, 04 (low).
8. **Serre 1970 (scan).** J.-P. Serre, "Le problème des groupes de congruence pour SL₂" (`serre_1970_le-probleme-des-groupes-de-congruence-pour-sl2_scan.pdf`). Scan; the congruence subgroup property of SL₂(ℤ[1/q]) was not checked, so it is not cited with a theorem number. Stage 03.
9. **Hida 1986 (Iwasawa, numdam).** `hida_1986_iwasawa-*`, Invent. Math. 85 (1986) 545–613 family, numdam scan with poor OCR. Thm 3.1, Cor. 3.2, 3.3 (p. 250) verified; statements only partly readable. Stage 06.
10. **Taylor–Wiles 1995 (scan).** `taylor-wiles_1995_*`, image-only scan. Not needed in stage 06.
11. **Darmon–Diamond–Taylor (preprint).** `darmon-diamond-taylor_1997_fermats-last-theorem_preprint.pdf`. Present, but not checked for the numbers used in stage 06 (Lemma 4.17). Stage 06.
12. **Helm 2004 (arXiv preprint).** `helm_2004_*`, the only version present. Numbering (Cor. 8.11 / Rem. 8.12) may differ from Israel J. Math. 160 (2007). Stages 04, 05.

### Mis-citations in the seed and SPLIT.md (25 items)

Non-citation seed errors (mathematical corrections in stages 01–06) are left in the stage files and are not repeated here.

1. **Stage 01, Thm 3.1 (JLclassical).** Cited: [JL] Thm 16.1. Wrong: Jacquet–Langlands state it as conjectural with a sketched proof (p. 494). Correct: for the Brandt-module form, cite Eichler (squarefree level), Shimizu, and Hijikata–Pizer–Shemanske (Memoirs 1989, missing; see above).
2. **Stage 01, [LV] key.** Cited: arXiv:0903.2797, key `longo-vigni_2009_*`. Wrong: the key and arXiv version are not the published reference. Correct: Manuscripta Math. 135 (2011) 273–328 per stage 01; stage 04 gives Int. J. Number Theory 8 (2012). Details to be checked (see unusable item 7).
3. **Hsieh's JL(U_q) = −U_q** ([Hs, §4.5, p. 34]; stage 01 #7 and stage 05 #4). Wrong / conflicting: contradicts the weight-2 computation for B₁₁ (ex:s01-Pi11: U_11 ↔ +Π_11) and Ribet 1990 Prop. 3.8, in a setting where Hsieh's quaternionic U_q (§4.2, p. 30) is our Π_q. Correct: unresolved. Either a normalisation of the GL₂-side U_q in Hsieh, or a misprint. Stage 05 fixes U_q ↦ +Π_q; HACS H5 pins it; test T05-1.
4. **Stage 02, §12 (seed).** Cited: "existing Lean developments contain [SA for B¹] in this shape". Wrong: the trace-formula import has only `sl2_strong_approximation` (SL₂(ℚ) dense in SL₂(𝔸_f), S = {∞}) and the GL₂ `strong_approximation` (det K' = Ẑ^×), both in `AlgJL/VolI/P0/TopGroups.lean`; for definite B the non-compact place is q, and B¹ has no unipotents. Mathlib v4.35.0 has neither Skolem–Noether nor Hasse–Minkowski. Correct: SA for B¹ needs its own proof (milestone L02.SA; the cost is dominated by Voight Prop. 14.6.7).
5. **Stage 02, Prop. quot (proof).** Cited: none ("every class of X_B(U') has a representative of norm in Ẑ^×"). Wrong: the step is uncited. Correct: it is Nrd(B^×) = ℚ_{>0} (Voight Main Thm 14.7.4); in Lean a second hypothesis (`Hyp.HS`), unless the per-level criterion (Prop. prop:s02-BG) is used.
6. **Stage 02, [LM] (seed §5).** Cited: "a Lean formalisation exists". Correct reference: [LM] Ann. Formalized Math. 2 (2026) 55–81, DOI 10.46298/afm.15738 (correct). Qualification: it is on Lean v4.19.0 in a separate repository; only `Submodule.IsLattice` is in Mathlib v4.35.0. Not usable on our frozen toolchain as it stands.
7. **Stage 02, [Br, VII.7].** Cited: [Br, VII.7] (spectral sequence (7.10), p. 174). Status: fine. Sharper and directly usable: Serre, *Trees*, II.2.8, Prop. 13 (p. 127), which also fixes the signs.
8. **Stage 02, [Vo, Ch. 28].** Cited: Voight Ch. 28 (correct). Wrong: Voight's first proof cites "Exercise 7.31" for B¹ = [B^×, B^×]; in the local copy, Exercise 7.31 states that automorphisms of ℍ are inner. Correct: precise pointers are Main Thm 28.5.3 (p. 485), 28.4.8 / Cor. 28.5.12 (pp. 484–486); the fact about B¹ needs its own reference or proof in L02.SA (b).
9. **SPLIT.md, stage 02 line.** Cited: `voight Ch. 38` for the S-arithmetic / Shimura context. Wrong: not needed for this stage; not used by stage 02. Correct: no replacement given in the input; drop or verify before citing.
10. **SPLIT.md stage 03 literature, and seed stage 06 #9.** Cited: `ribet_1983_mod-p-hecke-operators-and-congruences-between-modular-forms.pdf` for level raising. Wrong: that paper (Invent. Math. 71 (1983), 193–205) is about congruence primes versus the cohomological index (L̃:L) (Thm 1.4). Correct: level raising is Ribet, Proc. ICM 1983 (1984), [Ri84] (missing; see above).
11. **Stage 03 #5 (sign conventions).** Cited: Ribet [Ri90, p. 454]: ρ = ((p+1, t), (t, p+1)). Wrong: with the seed's α = (−s_{0*}, s_{1*}), the off-diagonal entries of αα^† change sign. Correct: Ribet's degeneracy map δ = (α_*, β_*) has no sign; use Ribet's convention when comparing.
12. **SPLIT.md stage 04 literature, "[Hi86b] Thm 3.1, Cor 3.2–3.3".** Wrong: these are GL₂-side statements (Invent. Math. 1986, p. 250); Cor. 3.3 concerns ideals of old forms, not freeness. Correct: definite-side control is Hida, Ann. Math. 1988, §§8–10, via Hsieh Thm 4.2 / LV11 Prop. 3.6.
13. **Stage 04 #2 (seed Prop. free (b)).** Cited: "cited ([LV], [Hs]); not formal". Wrong: for trivial coefficients it is elementary: Hida's lemma (U_p maps level K'_s = U_1(p^s) ∩ U_0(p^{s+1}) into level K_s) plus the free Δ-torsor S_{s+1} → X'_s. The seed's fibre-count remark (p² vs p) is resolved by this two-step factorisation. Correct: Lemma lem:s04-hida; [LV], [Hs] are not needed for trivial coefficients.
14. **Stage 04 #4, "[Hs, Thm 4.5]".** Cited: for freeness of M^ord_m over the Gorenstein T^ord_m. Wrong: Thm 4.5 states only that the eigenline is free of rank one. Freeness over T_m and the Gorenstein property are in its proof (p. 34), resting on [Wil95], [Hel07], [PW11]. Correct: cite Hsieh p. 34 with those inputs.
15. **Stage 04 #5, Hsieh's residual condition.** Cited: "non-Eisenstein" as the residual hypothesis. Correct: (CR, supp N^-): ρ̄ absolutely irreducible, p-distinguished, ramified at every ℓ | D with ℓ ≡ 1 mod p (not ±1); non-Eisenstein is implied.
16. **Stage 04 #10, "[Hid88b, Cor. 10.1]"** (Hsieh Thm 4.2 proof, p. 32). Wrong: there is no Corollary 10.1 in Hida 1988. Correct: Theorem 10.1 (p. 370) of Hida, Ann. Math. 1988.
17. **Stage 04 #11, Hsieh's #Γ_{N,x}** (p. 29). Cited: the factor 2 at levels containing −1 is against w_x. Wrong: it is against |Γ_x| (the import's Nat.card), not w_x. Correct: Hsieh's #Γ_{N,x} = #(D^× ∩ xR̂^×x^{−1})Q^×/Q^× equals stage 01's w_x.
18. **Stage 05 (G2), "[RS, (3.1), Lemma 3.17]".** Wrong: RS (3.1) (p. 45) is only the toric exact sequence 0 → T → J⁰ → J₁(M)² → 0; Lemma 3.17 (p. 46) is "Frob_p acts as pT_p on the torus". Correct: X_q(J) ≅ ℤ[Σ]⁰ is Ribet 1990, Prop. 3.1, p. 439; T_q = Frobenius permutation is Ribet 1990, Prop. 3.7–3.8, pp. 445–446; Frobenius on Σ = right multiplication by Π_q is Ribet 1990, Remark 3.5(b), p. 441.
19. **Stage 05 (G2), "[PW, Prop. 6.5]".** Wrong: PW Prop. 6.5 (p. 20) is a citation of Kohel Thm 4.3 and states Pic(X_{N⁺,N⁻}) ⊗ 𝒪 ≅ X_r, i.e. the full ℤ[X] rather than ℤ[X]⁰ when N⁻ = r (D = q). Correct: harmless after localisation at a non-Eisenstein m_f (PW's use); wrong by the Eisenstein line otherwise.
20. **Stage 05 (G3), "[SGA7, IX], [Ill]".** Wrong: Illusie Thm 2.7 (p. 41, Astérisque 196–197) is stated "avec le signe opposé" to SGA7 IX 9.1.2. Correct: the sign must be fixed by positivity; the node-thickness formula for the component group is Raynaud (same volume), Thm 5 (p. 17), Cor. 6 (p. 18).
21. **Stage 05 #5, "[Hel]".** Cited: Israel J. Math. 160 (2007). Wrong / qualified: the local file is the 2004 arXiv version. Correct: Hsieh's numbering (Cor. 8.11, Remark 8.12) matches the arXiv file (p. 31); recheck against the published version (see Helm 2007 above).
22. **Stage 06 #1, seed step (4) "level lowering … including q ≡ −1 mod p".** Wrong: unsupported. [KO, Thm 1.1(6)] and [PW, (CR)(2)] both exclude q ≡ ±1 mod p when ρ̄ is unramified at q; the obstruction is the Euler factor L_q(ad⁰f, 1)^{−1} = 1 − q^{−2} in [KO, Prop. 2.15(1), Prop. 5.6]. Correct: hypothesis (H0⁻) is added and q ≡ −1 is kept as an open case (matches the seed's T5/C4 restriction q ≢ ±1).
23. **Stage 06 #2, seed step (4)** "proved by passing to the quotient new at ℓ ‖ M … and applying R = T". Wrong / not needed. Correct: step (4) is [KO, Thm 1.1] combined with the fixed-weight Thm E over O (Cor. s06-fixed).
24. **Stage 06 #3, "Böckle's presentation".** Cited: none. Correct: [Böc07] (Böckle 2007, missing; see above), via [KO, Thm 3.12].
25. **Stage 04 / 06, `mazur-wiles_1984_*`.** Cited: as Mazur–Wiles 1986 (Compositio 59). Wrong: the local file is the class-field paper, a different work. Correct: Mazur–Wiles, Compositio 59 (1986), 231–264 (missing; see above). Hsieh's source is [Hs, p. 4]: [MW86, §9 Prop. 2].

### Other notes

- Stage 01: `\Tpath` is `\providecommand`ed locally; move to preamble.tex. `\NUp` (normalisation symbol N_{U_p}) is optional.
- Stage 02: `\BG`, `\Xone`, `\HypSA`, `\HypHS` are `\providecommand`ed locally; add to preamble.tex if stages 03/04 use them.
- Stage 03: no preamble macros requested; `\BG` is local (same definition as stage 02); suggest moving it to preamble.tex.
- Stage 04: `\NUp`, `\Kp`, `\Kpp`, `\TordB` are local. Preamble `\Tord` is Hida's ordinary Tate module; a separate macro for the ordinary Hecke algebra `\T^{ord}_B` would avoid confusion.
- Stage 05: `\BG`, `\Tpath`, `\cH`, `\Xq`, `\Ros`, `\Frob` are local; suggest moving `\BG`, `\Tpath`, `\Frob` to preamble.tex.
- Stage 06: `\BG` is local; move `\BG` and `\mathrm{St}` to preamble.tex.
- Seam (stages 03, 04, 06): ν∘π_* = tr∘ν' needs −1 ∈ U' or −1 ∉ U; holds in stage 03; stage 04 must carry the factor 2 at Ô^× → U_1(N); in stage 06 (T5) tr∘ν' = 2ν∘π_*, a unit at p ≥ 5.
- Seam (stages 04, 06): Λ acts on the GL₂ side through classical diamonds, P_k = ker(u^{k−2}); on the definite side through adelic diamonds, P^ad_k = ker(u^{2−k}); JL matches [u] ↦ [u]^{−1}.
- Seam (stages 05, 06): sign of U_q — stage 05 fixes U_q ↦ +Π_q, Hsieh has JL(U_q) = −U_q; congruence ideals are unaffected.
- Seam (stage 02): notation clash α = ι_q^{−1} diag(1,q) (seed §5) versus α = (−s_{0*}, s_{1*}) (seed §6); not renamed.
- Seam (stage 05): Frobenius at Γ₁-level (X4) is open and coupled to T05-2; a reference for the Rosati-twisted Hecke action on T_pJ/T^{I_q} (SGA 7 IX, 2.4 / 9.1–10.4) is still needed (Muse-audit addenda, not yet a list item).

## 2026-11-14 (evening): status update
- **HPS 1989 (Mem. AMS 418): DEFERRED.** Not obtainable for now (no access on Fabian's or Abhijit's side). It is not on any
  critical path: stage 01 cites the 1980 announcement (`hijikata-pizer-shemanske_1980_…`, §0 p. 280, verified), which is
  sufficient for the statements used. Stopgap for full statements: K. Martin, "The basis problem revisited",
  arXiv:1804.04234 (to fetch if a stage needs more than the announcement).
- Obtained by Abhijit (to be synced into literature/): Casselman 1973, Miyake 2006 (1989 ed. reprint), Helm 2007
  (DOI 10.1007/s11856-007-0056-0), Böckle 2007 (LMS LN 320), SGA 7 I (scan), Mazur–Wiles 1986.
- Already present locally although listed as missing above: Ribet 1984 ICM (scan), Hida 1986a. The list needs a refresh
  against the current folder.
