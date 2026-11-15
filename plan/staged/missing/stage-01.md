# Stage 01 (quaternion-foundations): missing literature, macro requests, seed doubts

## Missing literature (not in `literature/`)

| Priority | Reference | Why |
|---|---|---|
| high | W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314. DOI 10.1007/BF01428197 | Local newform theory for K_1(p^n) with the U_p = Σ π((p j;0 1)) operator; the cleanest citable source to identify N_Up with the classical U_p (Remark rem:s01-Upconv, HACS H4). |
| high | H. Hijikata, A. Pizer, T. Shemanske, "The basis problem for modular forms on Γ_0(N)", Mem. Amer. Math. Soc. 82 (1989), no. 418. | Full proof of the Brandt-module form of classical JL at all levels; only the 1980 announcement is present. |
| medium | M. Eichler, "The basis problem for modular forms and the traces of the Hecke operators", in: Modular Functions of One Variable I, LNM 320, Springer (1973), 75–152. | Classical Brandt-matrix/JL statement over Q, squarefree level ([Eic73] in Voight). |
| medium | S. Gelbart, "Automorphic forms on adele groups", Ann. of Math. Stud. 83, Princeton (1975), §3 | Standard adelic ↔ classical dictionary (diamond inversion, U_p); needed to pin Prop s01-relations(a) flag. |
| medium | A. Pizer, "On the arithmetic of quaternion algebras II", J. Math. Soc. Japan 28 (1976), 676–688 | Mass/class-number formulas for Eichler orders (present file is the 1980 algorithm paper, scan only). |
| low | J. Brzezinski, "On automorphisms of quaternion orders", J. Reine Angew. Math. 403 (1990), 166–186 | General mass formula ([Brz90, (4.6)] in Voight Main Thm 25.3.19); only if non-Eichler levels appear. |
| low | A text-layer (OCR) copy of Shimizu 1965 (Ann. of Math. 81, 166–193) and Pizer 1980 (J. Algebra 64, 340–390) | Present only as scans; their statements could not be verified by text search. |

## Macro requests (preamble.tex)
- `\Tpath{...}` (typewriter path) is `\providecommand`ed locally in stage-01; harmless to move to the preamble.
- Optional: `\NUp` for the normalisation symbol N_{U_p}.

## Seed doubts / mis-citations found
1. **Seed §2.5, U_p formula.** The seed writes `U_p = [U diag(1,p) U]` and asks for the normalisation that commutes with
   pushforward along S_{s+1} → S_s. In the seed's own conventions (U_1 with lower row ≡ (0,1); `[UgU] = ⊔ g_i U`;
   `(T_g f)(x) = Σ g_i f(x g_i)`), `[U diag(1,p) U]` commutes with the *trace* and not with pullback/pushforward; the
   pushforward-compatible operator is `[U diag(p,1) U] = ⊔_j (p j; 0 1) U`. Stage 01 fixes N_Up := the latter (Lemma lem:s01-Up).
2. **Seed §2.4, norm map.** "When p ∤ |Γ_x| the two are identified over Z_p by the norm map": true as modules, but the norm
   map intertwines each Hecke operator with its adjoint (T_ℓ ↔ S_ℓ^{-1} T_ℓ, U_p ↔ ⟨p⟩_M U_p') and pushforward with trace
   (Prop prop:s01-adjoint). Not a Hecke-module identification on the nose at U_1-level.
3. **Seed §2.5, diamonds.** With ⟨d⟩ = right translation by diag(1,d), S_ℓ = ℓ^{k-2}⟨ℓ⟩^{-1}; classically S_ℓ = ℓ^{k-2}⟨ℓ⟩
   (Buzzard 2004 p. 13). The adelic diamond is the classical inverse.
4. **Seed Lemma 5.2(b).** The freeness argument omits why γ lies in a stabiliser of level U_1(p); it works for Δ_s = (1+pZ_p)/(1+p^sZ_p)
   only (d ≡ 1 mod p is used). Fixed proof in Lemma lem:s01-stab.
5. **Seed Thm 3.1 (JLclassical), citation.** [JL] Thm 16.1 is stated by Jacquet–Langlands themselves as conjectural with a
   sketched proof (p. 494); for the Brandt-module form the usual citations are Eichler (squarefree level), Shimizu, and
   Hijikata–Pizer–Shemanske (Memoirs 1989, missing; only the announcement is present).
6. **[LV] key.** The seed's [LV] (arXiv:0903.2797) is `longo-vigni_2009_*`; the published version is Manuscripta Math. 135 (2011) 273–328.
7. **Sign of Π_ℓ.** Example ex:s01-Pi11 (B_11, weight 2) gives U_11 ↔ +Π_11 in the seed's normalisation; Hsieh §4.5 has
   JL(U_q) = −U_q with his normalisation. Stage 05 (owner of ε) must reconcile; HACS H5 pins it.
