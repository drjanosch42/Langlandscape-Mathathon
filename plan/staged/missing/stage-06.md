# Stage 06 (integral-defect): missing literature, requested macros, seed issues

## Missing literature (not in `literature/`)

| Ref | Full data | Why needed | Priority |
|---|---|---|---|
| [Böc07] | G. Böckle, *Presentations of universal deformation rings*, in: L-functions and Galois Representations (Durham 2004), LMS Lecture Note Ser. 320, Cambridge Univ. Press 2007, 24–58. | This is the seed's unreferenced "Böckle's presentation". It is used inside [KO, Thm 3.12] (complete-intersection presentation of the deformation ring, via [Böc07, Cor. 4.3, Thm 5.8]). Stage 06 cites [KO] directly, so we need it only to audit KO. | medium |
| [Ri84] | K. A. Ribet, *Congruence relations between modular forms*, Proc. ICM Warszawa 1983, PWN 1984, vol. 1, 503–514. | Level raising and the structure of the old/new congruence module (Prop. s06-betti (b)). It is also Hsieh's source for Ihara's lemma ([Hs, p. 68]: "[Rib84, Thm 4.1]"). | high |
| [MW86] | B. Mazur, A. Wiles, *On p-adic analytic families of Galois representations*, Compositio Math. 59 (1986), no. 2, 231–264. | The Gorenstein property of Hida's Λ-adic Hecke algebra ([Hs, p. 4]: [MW86, §9 Prop. 2]). The file `mazur-wiles_1984_*` is the class-field paper, a different work. | medium |
| [Hi86a] | H. Hida, *Galois representations into GL₂(ℤ_p[[X]]) attached to ordinary cusp forms*, Invent. Math. 85 (1986), 545–613. | The Λ-adic Galois representation ρ_F (Def. s06-tam). Currently obtained from the freeness of H via [Hs]/[Wi95]. | low |
| [DDT97] | H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current Developments in Math. 1995 / Elliptic curves, modular forms & FLT, 2nd ed., International Press 1997, 2–140. | §4.4 cohomology congruence ideals; Lemma 4.17 (used by [KO, Cor. 5.9]). A preprint is present (`darmon-diamond-taylor_1997_fermats-last-theorem_preprint.pdf`) but was not checked for these numbers. | low |

Notes:
- `hida_1986_iwasawa-*` is a numdam scan with poor OCR. The theorem numbers and page (Thm 3.1, Cor. 3.2, 3.3 on p. 250) were verified; the statements were only partially readable.
- `taylor-wiles_1995_*` and `ribet_1983_*` are image-only scans and were not needed.

## Seed references / claims that are wrong or mis-cited
1. **Seed Thm defect, step (4)**: "level lowering … including q ≡ −1 mod p". This is unsupported. [KO, Thm 1.1(6)] and [PW, (CR)(2)] both exclude q ≡ ±1 mod p when ρ̄ is unramified at q. The obstruction is the Euler factor L_q(ad⁰f,1)⁻¹ = 1 − q⁻² in [KO, Prop. 2.15(1), Prop. 5.6]. Stage 06 adds hypothesis (H0⁻) and keeps q ≡ −1 as an open case. This matches the seed's own T5/C4 restriction q ≢ ±1.
2. **Seed step (4)**, "proved by passing to the quotient new at ℓ ‖ M … and applying R = T": this is not needed. Step (4) is [KO, Thm 1.1] combined with the fixed-weight Thm E over the DVR O (Cor. s06-fixed).
3. **"Böckle's presentation"** has no reference. It is [Böc07] (above), via [KO, Thm 3.12].
4. **Thm E**: "in the setting of Lemma D" silently includes the Gorenstein property of R itself (Gor_R). It is now an explicit hypothesis. The claim "without Gorenstein of R′ the equality holds at height-one primes" is correct (a saturated rank-one submodule over a DVR is a summand); a proof is now given.
5. **Lemma D**: "S/𝔞 ≅ 𝔟^∨ is A-free" needs the summand argument (freeness of S/𝔟), not just the duality.
6. **(H1)** "I_F normal, finite over Λ, hence Λ-free": correct (normal of dim 2 ⇒ CM ⇒ free over the regular Λ by Auslander–Buchsbaum), but the seed gives no reason. A one-line justification has been added.
7. **(Im)** p | #ρ̄(G_Q) is not used by any theorem cited ([KO] needs only (TW); [KO, Rem. 2.10]). It is retained but flagged as superfluous.
8. **(P), weight-two alternative**: needs in addition that T^ord_2(Γ₀(Np))_m has no p-new forms. Otherwise T/P ≠ T₂(Γ₀(N))_m, and KO does not apply as stated.
9. **Level raising is Ribet 1984 (ICM)**, not Ribet 1983 (`ribet_1983_*` is Invent. Math. 71, congruence primes). This is the same correction as in stage 03.
10. **Seed Thm defect step (3)** states only P(𝔠_q(F)) ⊆ 𝔠_q(f). Equality holds by control for T′, T″; the inclusion suffices for the squeeze.
11. **T4** (p = 17, k up to 124) is outside the range l > k of the stage-03 Mayer–Vietoris statement. It needs the version localised at non-Eisenstein m and after e.
12. **T5** is labelled "[new]". For k ≤ p − 1 its outcome is predicted by Thm E (proved) and [KO] (cited), so it is a validation test. It is genuinely new only at k + (p−1).

## Requested macros
`\providecommand{\BG}{\mathrm{BG}}` is defined locally (same definition as stages 02/03). We suggest moving `\BG` and `\mathrm{St}` (Steinberg) into preamble.tex.

## Seam notes
- Factor 2: the only level change, Ô^× → U_1(N) on the definite side (T5), violates "−1 ∈ U′ or −1 ∉ U". Hence tr∘ν′ = 2ν∘π_*, which is a unit at p ≥ 5.
- Λ-structures: on the GL₂ side Λ acts through classical diamonds, P_k = ker(u^{k−2}). On the definite side (stage 04) the action is adelic, P^ad_k = ker(u^{2−k}). JL is matched by [u] ↦ [u]⁻¹.
- Sign at q: stage 05 fixes U_q ↦ +Π_q, while Hsieh has JL(U_q) = −U_q. Congruence ideals are unaffected.
- The Eisenstein property of Φ^comb (prop:s03-phieis) is unresolved for q ∈ {2,3}. Stage 06 does not use it.
