# Stage 05 — missing literature, requested macros, doubts about the seed

## Missing references (not in `literature/`)

| Ref | Full data | Why needed | Priority |
|---|---|---|---|
| [SGA7 IX] | A. Grothendieck, *Modèles de Néron et monodromie*, in: Groupes de monodromie en géométrie algébrique (SGA 7 I), Exposé IX, Lecture Notes in Math. 288, Springer, 1972 | (G3), (G4): orthogonality theorem (2.4), monodromy pairing (10.4), component group (11.5); the filtration and its graded pieces in (X4). Currently cited only through Raynaud (Astérisque 196–197), Kohel Thm 4.1, PW Prop 6.3 | high |
| [Hi86a] | H. Hida, *Galois representations into GL₂(ℤ_p[[X]]) attached to ordinary cusp forms*, Invent. Math. 85 (1986), 545–613 | Λ-freeness of Hida's ordinary Tate module 𝒯 in Prop. Xlambda (d) | high |
| [MP99] | I. Moerdijk, D. A. Pronk, *Simplicial cohomology of orbifolds*, Indag. Math. (N.S.) 10 (1999), no. 2, 269–293 | simplicial-orbifold language of §11 / O2 (only the 1997 K-theory paper is present) | medium |
| [Li75] | W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315 | a_q² = χ(q) q^{k−2} for q ∥ N (used in Prop. sign (c)); currently via Ribet–Stein Lemma 3.15 | low |
| [Buz97] | K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), 591–612 | Shimura-curve version of Hyp.X (O4); Kohel Thm 4.3 rests on it | medium |
| local JL for Steinberg | e.g. C. J. Bushnell, G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren 335, Springer 2006, §56 (JL for GL₂), or JL70 §15–16 | Prop. sign (e): JL(St⊗χ) = χ∘Nrd, to pin ε at higher weight | medium |
| [Tak01] | S. Takahashi, *Degrees of parametrizations of elliptic curves by Shimura curves*, J. Number Theory 90 (2001), 74–88 | the formulation of Kohel Thm 4.3 (character group ≅ definite Hecke module, isometric) is attributed to it | low |
| Γ₁-level DR/Deuring | any reference stating (X1)–(X3) at Γ₁(Mp^s)∩Γ₀(q) level with diamonds and U_p (none found; candidates: Ribet, *On the component groups and the Shimura subgroup of J₀(N)*, Sém. Théor. Nombres Bordeaux 1987–88, exp. 6; Edixhoven, Astérisque 196–197 pp. 159–170, is present but treats Γ₀) | status of Hyp.X beyond Γ₀ (Remark Xstatus) | medium |

## Seed references that are wrong or mis-cited

1. **(G2) "[RS, (3.1), Lemma 3.17]".** RS (3.1) (p. 45) is only the toric exact sequence 0 → T → J⁰ → J₁(M)² → 0;
   it does not identify X_q(J) with ℤ[X_B]⁰. Lemma 3.17 (p. 46) is "Frob_p acts as pT_p on the torus". The identification
   X_q(J) ≅ ℤ[Σ]⁰ is **Ribet 1990, Prop. 3.1, p. 439**; T_q = Frobenius permutation is **Ribet 1990, Prop. 3.7–3.8, pp. 445–446**,
   and Frobenius on Σ = right multiplication by Π_q is **Ribet 1990, Remark 3.5(b), p. 441**.
2. **(G2) "[PW, Prop. 6.5]".** PW Prop. 6.5 (p. 20) is a citation of Kohel Thm 4.3; it states Pic(X_{N⁺,N⁻}) ⊗ 𝒪 ≅ X_r, i.e. the
   *full* ℤ[X] rather than ℤ[X]⁰ in the case N⁻ = r (D = q). Harmless after localisation at a non-Eisenstein m_f (PW's use),
   wrong by the Eisenstein line otherwise.
3. **(G3) "[SGA7, IX], [Ill]".** Illusie's Thm 2.7 (p. 41 of Astérisque 196–197) is stated "avec le signe opposé" to SGA7 IX 9.1.2;
   the sign must be fixed by positivity. The node-thickness formula for the component group is Raynaud, same volume, Thm 5
   (p. 17), Cor 6 (p. 18).
4. **Hsieh's JL(U_q) = −U_q** ([Hs, §4.5, p. 34]) contradicts the weight-2 computation for B₁₁ (stage 01) and Ribet 1990
   Prop. 3.8 in a setting where Hsieh's quaternionic U_q (his §4.2, p. 30) is literally our Π_q. Either a normalisation of the
   GL₂-side U_q in Hsieh or a misprint; not resolved (Remark hsieh, test T05-1).
5. **[Hel]** is cited by the seed as Israel J. Math. 160 (2007); the local file is the 2004 arXiv version (numbering Cor 8.11,
   Remark 8.12 as cited by Hsieh matches the arXiv file, p. 31).

## Doubts about the seed (also in Risks)

- **Prop. noChain (b)** is either tautological (no map in 𝒞 has a B_D-Brandt module as source/target) or false (rationally,
  and at good m integrally, the q₂q₃-new part of the B_{q₁}-Brandt module at level U₀(q₂q₃M), built inside 𝒞, is Hecke-isomorphic
  to the B_D-Brandt module by JL twice). Replaced by Prop. nochain (a)–(c).
- **Hyp.X data list**: ℋ_s "U_ℓ (ℓ | Mp)" makes no sense at s = 0 (p ∤ level); use T_p there.
- **(X4)**: the top graded piece X_q(J_s) ⊗ ℤ_p is correct as a group (via the principal polarisation, X(J^∨) ≅ X(J)), but its
  Hecke action is through the Rosati dual; the seed does not say so (only the † in Prop. Xlambda hints at it).
- **Seed §11 zig-zag** concatenates a construction at q ∤ D (tree) with Hyp.X for D = q (no tree); these are at different
  primes/algebras. Rewritten as two parts.
- **O1 exponent**: with the seed's adelic diamonds (inverse to classical, stage 01) the exponent is forced to +1 by
  U_q² = ⟨q⟩ on q-new forms, as soon as a character with χ(q) ≠ ±1 occurs; at Γ₀-level it is invisible.

## Requested macros (provided locally with \providecommand in the stage file)

`\BG` (as stages 02/03), `\Tpath`, `\cH`, `\Xq`, `\Ros` (Rosati dual, ∨), `\Frob`. Suggest moving `\BG`, `\Tpath`, `\Frob` into
`preamble.tex`.

## Added after the Muse audit (reviser)

- **(X4) Frobenius at Γ₁-level.** With arithmetic Frob_q, Frob_q acts on T_t = Hom(X_q, ℤ_p(1)) as q·(σ_q⁻¹)ᵀ. At Γ₀-level
  σ_q = U_q is an involution. At Γ₁-level (U_q² = ⟨q⟩ ≠ 1), "Frob_q = qU_q" in (X4) is equivalent to σ_q = U_q⁻¹; the naive
  Γ₁-analogue of Ribet 1990 Prop. 3.8(ii) gives σ_q = U_q instead. Need a Γ₁-level reference (or computation) fixing
  Picard vs Albanese functoriality for U_q on the character group. Open; coupled to the exponent (T05-2).
- **(X4) Rosati twist for U_p, U_ℓ (ℓ | M).** Their Rosati duals are not in ℋ_s; the top piece is read with the Brandt
  adjoint θ_s(h)*. A reference identifying the Hecke action on T_pJ/T^{I_q} ≅ X_q(J^∨) ⊗ ℤ_p via the polarisation
  (SGA 7 IX, 2.4/9.1–10.4; Rosati-equivariance of the monodromy pairing) is needed.
- **[Hi86a]** is now also needed for the compatibility in s of Prop. Xiso (Λ-adic freeness on the GL₂ side).
