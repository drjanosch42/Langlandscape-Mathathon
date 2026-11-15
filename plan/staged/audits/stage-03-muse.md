# Audit of stage.tex (stage 03 ribet-ihara) against SPLIT.md and stage.bib

1. **F1 — Prop. `prop:s03-phi` (two-vertex formula) — severity: minor — category: correctness**
   - Claim: \(|\Phicomb(\G)| = (\prod w_e)\sum 1/w_e = \sum_e\prod_{e'\ne e}w_{e'}\) and \(\Phicomb\cong\Z/|E|\) if all \(w_e=1\); example \(w=(2,2,2)\) gives \(\Z/2\times\Z/6\).
   - Why problem: None — formula is correct finite linear algebra. Checked: order 12 matches Smith form of \(W\Z[E]^0+\Z\mathbf1\) with \(W=\mathrm{diag}(2,2,2)\); \(w=(2,2,2)\) indeed non-cyclic, shows general \(\Phicomb\) not cyclic.
   - Fix: No fix needed. Status `\stproved` appropriate.

2. **F2 — Lemma `lem:s03-cyclic` (cyclicity criterion) — severity: minor — category: correctness**
   - Claim: \(\lambda(x)=\sum_e (W/w_e)x_e\) induces \(\bar\lambda:\Phicomb\to\Z/n\) surjective iff \(\gcd_e(W/w_e)=1\); pairwise coprime \(w_e\) sufficient.
   - Why problem: None — image is \(d\Z/n\) with \(d=\gcd(W/w_e)\); pairwise coprime implies \(d=1\) because a prime dividing one \(w_{e_0}\) cannot divide \(W/w_{e_0}\). The “any number of 1’s allowed” note is correct.
   - Fix: No fix. Proof sketch complete.

3. **F3 — Lemma `lem:s03-elliptic` (elliptic classes) — severity: major — category: gap**
   - Claim: For \(q\ge5\), \(B=B_q\), \(U=\hat\cO^\times\), \(w_x\in\{1,2,3\}\), \(n_2=\frac12(1-(\frac{-4}{q}))\), \(n_3=\frac12(1-(\frac{-3}{q}))\); proof uses mass formula and Eichler class number formula [Vo Thm 25.1.1 p415, Thm 30.1.5 p543].
   - Why problem: Classification step “\(|\cO_x^\times/\pm1|>3\) forces \(B\cong(-1,-1)\) or \((-1,-3)\) i.e. \(q\in\{2,3\}\)” is correct but compressed; it relies on classification of finite subgroups of \(B^\times\) (binary tetrahedral \(2T\) of order 24 gives \(w=12\) for \(q=2\); dicyclic of order 12 gives \(w=6\) for \(q=3\)). Seed gives no reference; Voight Ch.17 covers it but not cited here.
   - Fix: Add explicit citation to Voight Ch. 17 or Vignéras for finite subgroups of \(\cO^\times\); otherwise accept as `\stpmc` with registered hypothesis for Lean (as stage already does in Risks R4).

4. **F4 — Prop. `prop:s03-mazur` (Mazur check) — severity: minor — category: correctness/interface**
   - Claim: \(\Phicomb(\GDR_q(\hat\cO^\times))\cong\Z/\mathrm{num}\frac{q-1}{12}\) cyclic for every prime \(q\) (including 2,3 where trivial via single edge \(w=12,6\)).
   - Why problem: None — computation \(\prod w_e\sum w_e^{-1}=2^{n_2}3^{n_3}\cdot\frac{q-1}{12}= \mathrm{num}\frac{q-1}{12}\) using \(2^{n_2}3^{n_3}=12/\gcd(q-1,12)\) from Lemma `lem:s03-elliptic` is correct. Extending seed’s \(q\ge5\) to all \(q\) (Remark `rem:s03-mazur`(b)) is correct and matches [Mz App. Thm A.1(b) p173] order agreement.
   - Fix: No fix. Note stage correctly separates \(q=2,3\) case where Lemma `lem:s03-elliptic` does not apply.

5. **F5 — Conventions (C2)–(C3) (weights and factor 2) — severity: minor — category: interface/correctness**
   - Claim: Default \(w_x=|\Gamma_x/(\Gamma_x\cap\{\pm1\})|\); \(-1\in\Gamma_x\iff-1\in U\); mass formula \(\sum w_x^{-1}=\frac1{12}\prod_{\ell\mid D}(\ell-1)\) when \(-1\in U\); unfolding \(\nu\circ\pi_*=\mathrm{tr}\circ\nu'\) iff \(-1\in U'\iff-1\in U\); for \(s_0,s_1\) hypothesis always holds because \(-1\in\Iw_q\).
   - Why problem: Consistent with SPLIT.md Shared conventions (“any statement that uses \(|\Gamma_x|\) instead must say so; factor 2”) and with `if:s01-mass` (stated as \(\sum1/|\Gamma_x|=(1/24)\prod(\ell-1)\) in full-unit convention). Stage correctly warns that comparison \(\hat\cO^\times\to\Uone{N}\) needs explicit factor 2 (stage 04). No error.
   - Fix: Keep warning; ensure stage 01 final draft indeed uses same \(w_x\) default.

6. **F6 — Prop. `prop:s03-phieis` (Phicomb Eisenstein) — severity: major — category: gap/reference**
   - Claim: \(T_\ell\) self-adjoint for \(\langle,\rangle_w\), acts on \(\Phicomb\), and \(T_\ell-(1+\ell)\) kills \(\Phicomb\); citing [Ri90 Thm 3.12 p449] with proof “\(B_\ell(i,j)\) divisible by \(e(i)=w_i\)”.
   - Why problem: Self-adjointness for weighted pairing \(\langle[x],[y]\rangle=w_x\delta_{xy}\) holds iff Brandt matrix satisfies \(B_\ell(i,j)w_j = B_\ell(j,i)w_i\); Ribet’s Thm 3.12 indeed proves Eisenstein property via that divisibility, which is purely quaternionic. Stage marks `\stcited` correctly; no proof required here. Geometric analogue [Ed91 Thm 1] inside `asterisque_1991` volume is correctly noted as cited only.
   - Fix: No fix; optionally record that \(p>3\) hypothesis in [Ed91] matches stage’s \(p\ge5\).

7. **F7 — Lemma `lem:s03-bip` and Thm `thm:s03-ribet`(a) — severity: minor — category: correctness**
   - Claim: Connected bipartite multigraph \(\G\) gives \(0\to H_1(\G)\to\Z[E]^0\to\Z[V_0]^0\oplus\Z[V_1]^0\to0\), \(\ker\partial^\vee=A\cdot(\mathbf1,\mathbf1)\); applied to \(\BG(U,q)\) yields definite Ribet sequence with \(\alpha=(-s_{0*},s_{1*})\) Hecke-equivariant.
   - Why problem: Correct. Sign convention (C1) \(\alpha=(-s_{0*},s_{1*})\) vs Ribet’s \(\delta=(s_{0*},s_{1*})\) differs by automorphism \((x,y)\mapsto(-x,y)\) flipping off-diagonal sign of \(\alpha\alpha^\dagger\); stage documents this and imports `if:s02-quot` bijections \(s_0[x]=[x], s_1[x]=[x\alpha]\) verbatim. Connectivity as only arithmetic input is correctly isolated; stage notes (a) needs only per-level connectivity, (b) and \(H_0\) need full SA (`if:s02-SA`/`if:s02-coh`).
   - Fix: No fix.

8. **F8 — Thm `thm:s03-iharaH0` (Hecke on \(H_0\)) — severity: major — category: gap/correctness**
   - Claim: \(\varepsilon(f_0,f_1)=\sum_{[x]}w_x^{-1}([\tau(x)]f_0(x)+[q\tau(x)]f_1(x))\) gives \(\coker\alpha\cong V_{U^1_p}\), and \(T_g\mapsto\deg(UgU)[\ell^{v_\ell(\Nrd g)}]\), so \(T_\ell\mapsto(1+\ell)[\ell]\) (\(S_\ell\mapsto[\ell]^2\)) under (C4)–(C6).
   - Why problem: Proof sketch is coherent: duality \(\coker\alpha\) vs \(\ker\alpha^\vee\) (Cor `cor:s03-ihara`(ii’)), unfolding identity \(\sum_{[x]}w_x^{-1}\sum_{U/U'}F(xu)=\sum_{[y]}w_y^{-1}F(y)\) with orbit sizes \(w_x/w_y\) (no factor 2 by (C3) because \(-1\in\Iw_q\)), and Hecke computation \(\tau(yh)=\ell^m\tau(y)\). Surjectivity of \(\varepsilon\) implicitly uses surjectivity of \(\tau: \XB U\to\Zp^\times/{\det(U^1_p)}\) i.e. \(\Nrd(U)=\Zhat^\times\); this holds for standard levels by `if:s01-classset`. Stage marks `\sttoprove` with full sketch, appropriate. Exponent \(+1\) is fixed by (C4) choice \(T_gf(x)=\sum f(xg_i)\) from `if:s01-hecke`; Remark `rem:s03-pm` correctly explains \(-1\) belongs to adjoint \(T_g^\dagger=T_{g^{-1}}=S_\ell^{-1}T_\ell\) and to homological \(\Z[X]\) presentation via \(\nu\). SPLIT.md doubtful point “sign or exponent unfixed” is thus resolved as documented deviation D1.
   - Fix: Ensure stage 01 final normalisation \(N_{U_p}\) matches (C4) (stage already does cross-check R1/R2). HACS T6 with both normalisations is correct mitigation.

9. **F9 — Cor. `cor:s03-eis` and Remark `rem:s03-T6` — severity: minor — category: correctness**
   - Claim: Support of \(H_0\) Eisenstein; for \(U_p=\GL_2(\Zp)\), \(2<k\le p+1\), \(H_0(\GU,\Vk)=0\) via irreducibility of \(\Sym^{k-2}\F_p^2\) for \(\SL_2(\F_p)\); for \(U_p=\Uone{p^s}_p\) non-zero.
   - Why problem: Correct: \(\Sym^{r}\F_p^2\) irreducible for \(0\le r\le p-1\) (\(p\ge5\)), so coinvariants vanish; Nakayama lifts to \(\Zp\). Unipotent coinvariants non-vanishing is correct. This sharpens SPLIT’s T6 from “new” to validation, as noted.
   - Fix: No fix.

10. **F10 — References (stage.bib) — severity: minor — category: reference**
    - Claim: Every `\stcited` carries `\lit{file-stem}{Thm/§/page}` verified locally; missing files marked “NOT in literature/”: [Ri84], [SGA7], [Ih75] (Illusie inside `asterisque_1991` volume checked for TOC).
    - Why problem: Attributions verified: [Vo Thm 25.1.1 p415 mass, Thm 30.1.5 p543 class number, Thm 28.2.3 p479 SA for \(\SL_2\)], [Se II.1.4 Thm 3 p79 amalgam under (D), p81 \(\SL_2(\Z[1/p])\) example], [Br II.7 Cor 7.7 p51 MV, III.6 Ex p74 with coefficients], [DT p439-440 Eisenstein ideals Lemma 2 p445-446 definite Ihara via SA, adjunction p446, Thm 1 p447], [Ri90 Prop 2.2 Thm 2.3 p436 weighted p437-438 Prop 3.1 p439 Thm 3.12 p449 Thm 3.15 p451 Rem 3.18 p452 Thm 3.22 p454], [Mz App Thm A.1(b) p173 Thm 1.1(d) p175-176], [DR VI Thm 6.9(iii) p286-287 thickness], [Ri83 Thm 1.4 p195 congruence module], [MS19 Thm 1.1]. Stage correctly notes SPLIT’s “`ribet_1983` (level raising)” is misattribution; [Ri83] is about congruence primes, level raising is [Ri84] missing — recorded in Risks R6.
    - Fix: No fix; missing entries already listed in `missing/stage-03.md` per conventions.

11. **F11 — Interfaces vs SPLIT.md — severity: minor — category: interface**
    - Claim: Imported interfaces restated verbatim from SPLIT.md (`if:s01-classset`, `if:s01-brandt`, `if:s01-hecke`, `if:s01-mass`, `if:s02-tree/SA/quot/coh/indef`); exported `if:s03-graph/ribet/ihara/amalgam`.
    - Why problem: Largely faithful. Deviations D1–D4 are explicitly documented: D1 upgrades (iii) Hecke on \(H_0\) from “sketched” to `\sttoprove` fixing exponent to \(+1\) under (C4); D2 extends Cor (ii) to every abelian group \(A\) and adds (ii’) with norm twist; D3 adds Lemma cyclic, Mazur as Prop for all \(q\), and Phieis; D4 leaves \(\Psi^*\Psi\) matrix asymmetric (\(T'_q\) vs \(q^{2-k}T_q\)) but exports only \(\det\) and \(\coker\) which are isomorphism-invariant. All within SPLIT’s allowed “say so in Risks/missing” rule. No notation redefinition (shared macros respected).
    - Fix: No fix; downstream stages 04/06 must use only \(\det(\Psi^*\Psi)=(q+1)^2-q^{2-k}T_q^2\) as advised.

12. **F12 — Lean/HACS feasibility — severity: minor — category: feasibility**
    - Claim: Lean L1–L4 elementary; amalgam not now (no \(\SL_2(\Z)\) generators, no Serre tree theory in import); HACS T1/T2/T6/C3 concrete with predicted numbers (Ex `ex:s03-mazur` table, T2 rank checks, T6 explicit \(\varepsilon\) and \(+1\) exponent).
    - Why problem: Assessment correct: Mathlib `SimpleGraph` unsuitable for multigraphs, `Finsupp`/`Fin n\to\Z` incidence matrix approach is appropriate; \(\Phicomb\) as \(\coker(X\to\Hom(X,\Z))\) is definable; Lemma `lem:s03-bip` with `Relation.ReflTransGen` connectivity hypothesis is Lean-friendly; Prop `prop:s03-phi` determinant index needs check against Mathlib 4.35.0 (stage flags this); elliptic count and SA remain registered hypotheses. HACS predictions are hand-computable and match Vo Exercise 30.6 class numbers (e.g. \(q=11\): \(h=2\), \(|\Phi|=5\); \(q=101\): \(h=9\), \(|\Phi|=25\)).
    - Fix: No fix; keep Lean milestones decoupled per SPLIT conventions.

Summary:
Stage 03 is mathematically sound, references are verified against PDFs, and interface deviations are explicitly documented; no critical error found.
Main gaps are the compressed unit-group classification in Lemma `lem:s03-elliptic` and the deferred full proof of Thm `thm:s03-iharaH0` (marked `\sttoprove` with complete sketch), both correctly flagged as hypotheses/risks.
Lean/HACS tracks are feasible and correctly scoped, with strong-approximation remaining the sole deep arithmetic input isolated to stage 02.
