# Stage 03 (ribet-ihara): missing literature, requested macros, seed issues

## Missing literature (not in `literature/`)

| Ref | Full data | Why needed | Priority |
|---|---|---|---|
| [Ri84] | K. A. Ribet, *Congruence relations between modular forms*, Proc. ICM Warszawa 1983, PWN, Warsaw 1984, vol. 1, 503–514. | Classical source of level raising and of the Betti level-raising module coker(Ψ*Ψ) (Def. s03-LR); the definite analogue Prop. s03-LRdef. | high |
| [Ih75] | Y. Ihara, *On modular curves over finite fields*, in: Discrete Subgroups of Lie Groups and Applications to Moduli (Bombay 1973), Oxford Univ. Press 1975, 161–202. | Original Ihara lemma (GL₂ side, Conj. s03-iharaGL2). | medium |
| [SGA7] | A. Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX, LNM 288, Springer 1972, 313–523. | Dictionary X(G) / monodromy pairing / component group (remark only, Rem. s03-grothendieck; used by stage 05). | medium |
| [Ri88] | K. A. Ribet, *On the component groups and the Shimura subgroup of J₀(N)*, Sém. Théorie des Nombres de Bordeaux 1987–88, Exp. 6. | Proof of [Ri90, Thm 3.22] (antidiagonal in the kernel), definite analogue of Prop. s03-LRdef / s03-phieis. | low |
| [Em02] | M. Emerton, *Supersingular elliptic curves, theta series and weight two modular forms*, J. Amer. Math. Soc. 15 (2002), 671–714. | Explicit component group / Gross lattice computations; cross-check for T1. | low |

Remarks:
- `serre_1970_le-probleme-des-groupes-de-congruence-pour-sl2_scan.pdf` is present but is a scan. The congruence subgroup property of SL₂(ℤ[1/q]) (an alternative route to the GL₂ Ihara lemma) was **not** checked against it. Unverified, so it is not cited with a theorem number.
- `ribet_1990_*` and `ribet_1983_*` are image-only scans. They were verified via local OCR (ocrmypdf); page numbers are journal pages (Ri90: PDF page = journal page − 430).

## Seed / SPLIT references that are wrong or mis-cited
1. SPLIT.md stage 03 literature: "`ribet_1983_mod-p-hecke-operators-and-congruences-between-modular-forms.pdf` (level raising)" is wrong. That paper (Invent. Math. 71 (1983) 193–205) is about congruence primes versus the cohomological index (L̃:L) (Thm 1.4). Level raising is [Ri84] (missing).
2. Seed Cor. ihara (iii) and T6: the exponent ℓ^{±1} is unfixed. It is fixed here (Thm s03-iharaH0): with the cohomological Hecke action of stage 01 the exponent is +1. The exponent −1 is the adjoint S_ℓ^{-1}T_ℓ, which is what one gets from the homological presentation of stage 02 transported by ν. T6 is therefore a validation test, not a "new" one.
3. Seed §6.4 / C3: the matrix Ψ*Ψ = ((q+1, −T_q), (−q^{2−k}T_q, q+1)) is one of several equivalent normalisations; which off-diagonal entry carries q^{2−k} depends on V vs V^∨ and on the ordering. Only the determinant (q+1)² − q^{2−k}T_q² and the cokernel are canonical.
4. Seed Example mazur / §6.1: the restriction q ≥ 5 is unnecessary (both sides are trivial for q = 2, 3). The mass formula "Σ|O_e^×|^{-1} = (q−1)/24" is correct with full unit groups.
5. Seed sign conventions vs Ribet: Ribet's degeneracy map δ = (α_*, β_*) has no sign. With the seed's α = (−s_{0*}, s_{1*}) the off-diagonal entries of αα^† change sign ([Ri90, p. 454]: ρ = ((p+1, t),(t, p+1))).

## Requested macros
None in preamble. `\providecommand{\BG}{\mathrm{BG}}` is used locally, with the same definition as stage 02. Suggest moving `\BG` to preamble.tex.

## Seam note (factor 2, from the stage 01 revision)
ν∘π_* = tr∘ν' requires −1 ∈ U' or −1 ∉ U; otherwise tr∘ν' = 2·ν∘π_*. In stage 03 the only level changes are the degeneracies U ↔ U_0(q)U. These differ only at q, and −1 ∈ Iw_q, so the hypothesis always holds (stated in Convention (C3)). Convention (C2) was also corrected: |Γ_x| = 2w_x only when −1 ∈ U. Level changes Ô^× → U_1(N) do not occur in stage 03; stage 04 must carry the factor 2 there.
