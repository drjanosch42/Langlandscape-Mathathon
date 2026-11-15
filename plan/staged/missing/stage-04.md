# Stage 04 (lambda-adic): missing literature, macro requests, seed doubts

## Missing literature (not in `literature/`, or present but unusable)

| Priority | Reference | Why |
|---|---|---|
| medium | H. Hida, "On p-adic Hecke algebras for GL2 over totally real fields", Ann. of Math. (2) 128 (1988), 295–384 — **a text-layer (OCR-clean) copy**. In the present file the headers are locatable (Thm. 8.6 p. 362, Thm. 9.4 p. 369, Thm. 10.1 p. 370, Cor. 10.4 p. 373; reviser 04) but the statements are only partly legible. | Original source of definite-side control and Λ-freeness (cited via Hsieh Thm 4.2 and LV11 Prop 3.6). |
| high | A. Wiles, "Modular elliptic curves and Fermat's Last Theorem", Ann. of Math. 141 (1995), 443–551 — present (`wiles_1995_*`), but Thm 2.1 / Cor. 2 p. 482 not verified in this stage. | Hsieh's Gorenstein/freeness input. Verify in stage 06. |
| high | D. Helm, "On maps between modular Jacobians and Jacobians of Shimura curves", Israel J. Math. 160 (2007), 61–117 (published version; only the 2004 arXiv preprint `helm_2004_*` is present, numbering may differ from Cor. 8.11 / Rem. 8.12). | Hsieh Thm 4.5 proof. |
| medium | H. Hida, "Galois representations into GL2(Z_p[[X]]) attached to ordinary cusp forms", Invent. Math. 85 (1986), 545–613 ([Hi86a]). | Λ-adic Galois representations behind ρ̄_m in Hyp CR_D. |
| medium | B. Mazur, A. Wiles, "On p-adic analytic families of Galois representations", Compositio Math. 59 (1986), 231–264 ([MW86]); `mazur-wiles_1984` is a different paper. | Gorenstein input cited by Hsieh §1.4. |
| medium | H. Hida, "Modules of congruence of Hecke algebras and L-functions associated with cusp forms", Amer. J. Math. 110 (1988), 323–382 ([Hid88a]) — check: `hida_1988_modules-of-congruence-*` is present; pp. 363–366 underlie Hsieh Rem. 7.3. | Commutative-algebra lemma "congruence ideal = self-pairing". |
| low | H. Hida, Hilbert Modular Forms and Iwasawa Theory, Oxford 2006 — present (`hida_2006_*`); Lemma 3.5 (perfectness of the Atkin–Lehner-twisted pairing) not verified here. | Def s04-BN finite-level perfectness. |
| low | Longo–Vigni 2011: published journal data (Int. J. Number Theory 8 (2012)) recorded from memory; verify. | Bib accuracy. |

## Macro requests (preamble.tex)
- `\NUp`, `\Kp`, `\Kpp`, `\TordB` are `\providecommand`ed locally in stage-04. Note: preamble `\Tord` is Hida's ordinary *Tate module*;
  a separate macro for the ordinary Hecke algebra `\T^{ord}_B` would avoid confusion.

## Seed doubts / mis-citations found
1. **P_k and diamonds (seed §2.6, §7).** With Λ acting through the adelic diamonds (seed §2.3, Hsieh §4.4), the weight-k point is
   `ker([u] ↦ u^{2-k})`, not the seed's `P_k = ker([u] ↦ u^{k-2})`; the seed's P_k is right only for classical diamonds (= inverse of
   adelic, stage 01). Def def:s04-Pk.
2. **Seed Prop free (b), "cited ([LV],[Hs]); not formal".** For trivial coefficients it *is* elementary: Hida's lemma
   (U_p maps level K'_s = U_1(p^s)∩U_0(p^{s+1}) into level K_s) plus the free Δ-torsor S_{s+1} → X'_s. The seed's remark
   "fibres p^2 vs kernel p" is resolved by this two-step factorisation. Lemma lem:s04-hida.
3. **"[Hi86b] Thm 3.1, Cor 3.2–3.3" (SPLIT literature line).** These are statements on the elliptic (GL2) side (p. 250); Cor. 3.3 is about
   ideals of old forms, not freeness. Definite-side control is Hida, Ann. Math. 1988, §§8–10, via Hsieh Thm 4.2 / LV11 Prop 3.6.
4. **"[Hs, Thm 4.5]" for freeness of M^ord_m over Gorenstein T^ord_m.** Thm 4.5 states only that the eigenline is free of rank one;
   the freeness over T_m and the Gorenstein property are in its *proof* (p. 34), resting on [Wil95], [Hel07], [PW11].
5. **Hsieh's residual condition** is (CR, supp N^-): ρ̄ absolutely irreducible, p-distinguished, ramified at every ℓ | D with
   ℓ ≡ 1 mod p (not ±1). "Non-Eisenstein" is implied.
6. **Seed's pairing "twist by U_p^{-s} w_{p^s}".** Hsieh's B_N (Def 4.3) also uses the Atkin–Lehner at the tame level M, a norm twist
   χ_I(ν(x)), #Γ (not w_x; factor 2 at levels containing −1), lives on a fixed-character piece over I, and has a sign (−1)^k in weight k
   (Lemma 4.4).
7. **Seed Lemma ekills (c)** uses e^* without saying it is the projector of U_p^* = ⟨p⟩_M U'_p, which is incompatible with pushforward;
   under ν it is the cohomological e. Made explicit in Lemma lem:s04-ekills(d).
8. **Seed Thm lambdaribet "with V_k after localisation at non-Eisenstein m (sketch)".** Localisation is unnecessary: e kills
   H_0(Γ_U, V_k) for all k (U_p^2 ≡ 0 mod p on coinvariants), Prop prop:s04-ekillsVk (to prove; needs strong approximation for
   H_0 = V_{U_p^1} and the transfer of U_p to group homology).
9. **Hsieh Rem 7.8** gives (η^B_F) ⊇ (η_F) with equality if ρ̄ is ramified at all ℓ | D; stage 06 should use this.
10. **Hsieh's "[Hid88b, Cor. 10.1]"** (Thm 4.2 proof, p. 32) is *Theorem* 10.1 (p. 370) of Hida 1988; there is no Corollary 10.1.
11. **Factor 2 (revision after audit).** Hsieh's #Γ_{N,x} = #(D^× ∩ xR̂^×x^{-1})Q^×/Q^× (p. 29) equals stage 01's w_x; the factor 2 at
    levels containing −1 is against |Γ_x| (the import's Nat.card), not against w_x. The drafter's text had it against w_x.
