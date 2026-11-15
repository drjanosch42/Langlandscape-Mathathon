# Global seam audit of the staged plan (Fable)

Auditor: Claude Fable 5.2, alone, 2026-11-14. Audited state: `wip-plan` at `242b5f4`.
Read in full: the seed, `SPLIT.md`, `preamble.tex`, stages 01–06, all six Muse audits and resolutions, `METRICS.md`.
Literature opened with `pdftotext`: Hsieh (arXiv), Kim–Ota (arXiv v4), Pollack–Weston (arXiv), Voight, Ribet–Stein (with Conrad's appendix).
Not checkable here: Ribet 1990 (scan without a text layer), so [Ri90, Thm 3.12] is not re-verified; see issue 7, which no longer needs it.

Statuses used below: **derived** (I re-derived it in this audit), **checked** (compared with the PDF), **not checked**.

## Overall verdict

**PASS WITH REQUIRED FIXES.** No critical defect. 7 major and 13 minor fixes (list F1–F20 below).
The route is coherent. Nothing proved in one stage is used in another under different hypotheses in a way that breaks a main result.
The major items are three statements that are false or unsupported as written (F1, F2, F4), one over-restriction of the main theorem (F3), and three seam inconsistencies (F5, F6, F7).

## Seam matrix

"Importer restates SPLIT wording" means the import block copies `SPLIT.md` and not the exporter's sharpened text. That is acceptable where the importer's own text applies the sharpened form; it is marked where it does not.

| Interface | Exported | Imported by | Verdict |
|---|---|---|---|
| `if:s01-classset` | 01 | 02, 03, 04, 05 | OK. Freeness is for Δ_s only; 04 uses exactly that. |
| `if:s01-brandt` | 01 | 02, 03, 04, 05 | OK in 03 (C3), 04, 05. **MISMATCH (minor)** in 02: `def:s02-Mhom` uses the norm over all of Γ_x, 01 uses Γ_x/±1 (F8). |
| `if:s01-hecke` | 01 | 02, 03, 04, 05, 06 | OK in substance (N_Up used consistently; adjoints T* = T_{g⁻¹} used correctly in 03 (C4), 04, 05). **MISMATCH (minor)**: all five import blocks still say "Self-adjointness for the pairing" (F15). |
| `if:s01-mass` | 01 | 02, 03, 04 | OK. 03 uses the w-form Σ 1/w_x = φ(D)/12 correctly. |
| `if:s01-targets` | 01 | 04, 05, 06 | **MISMATCH (major)** on the sign of U_q ↦ ±Π_q: 01 says "±, convention-dependent" and quotes Hsieh's −; 04 states JL(U_q) = −U_q as a fact; 05 fixes +; 06 says "re-sign" (F6). |
| `if:s02-tree` | 02 | 03 | OK. α'⁻¹v_0 = αv_0 = v_1 agrees. |
| `if:s02-SA` | 02 | 03, 04 | OK. Hasse–Schilling is named. |
| `if:s02-quot` | 02 | 03, 04; used by 05 | **MISMATCH (major)**: 05 uses it (`def:s05-stages`, `prop:s05-nochain`) and does not import it (F5). |
| `if:s02-coh` | 02 | 03, 04; used by 05 | **MISMATCH (major)**: 05 uses it (`rem:s05-degree`) and does not import it (F5). 04's import block restates H_0 = V_{U_p^1} without the full-SA caveat (F14). |
| `if:s02-indef` | 02 | 03, 04, 05 | OK in 03 and 05 (amended form over ℤ). 04's block is unamended, its usage paragraph is right (F14). Hecke structure on H_1(Γ_U,V) is not fixed (F9). |
| `if:s03-graph` | 03 | 04, 05 | OK. |
| `if:s03-ribet` | 03 | 04, 05 | OK. 04 uses (a) ⊗ ℤ_p on homological modules. |
| `if:s03-ihara` | 03 | 04 | OK. Exponent +1 belongs to the cohomological presentation (03, R3). |
| `if:s03-amalgam` | 03 | 05, 06 | OK for l > k. 06 needs a version for k ≥ p that 03 does not export (F19). |
| `if:s04-ekills` | 04 | 05 | **MISMATCH (minor)**: 05 cites "(c)" for the perfect pairing; in 04 that is (d) (F11). |
| `if:s04-Mord` | 04 | 05, 06 | OK for Λ-structure (P_k^ad ↔ P_k via [u] ↦ [u]⁻¹) and for (CR_D). `thm:s04-control`(b) is wrong as stated (F4). |
| `if:s04-lambdaribet` | 04 | 05 | OK, but the hypothesis "connected at every level s" is implicit (F7). |
| `if:s04-etaB` | 04 | 05, 06 | **MISMATCH (minor)**: 05 `rem:s05-BN` and 06 (S1), H2 still describe Hsieh's weights as differing from w_x by a factor 2 (F10). |
| `if:s05-hypX` | 05 | none (talk, Lean) | (X4) Frobenius formula depends on an unstated choice of model (F1). |
| `if:s05-subquot` | 05 | 06 (optional) | OK. Two hypotheses are superfluous (F12). |
| Lemma D of 06 | 06 | 05 (as a citation) | **MISMATCH (minor)**: a cross-stage dependency without an `if:` label, against SPLIT's "05 and 06 are independent" (F16). |
| `if:s06-defect` | 06 | none | OK. New, not in SPLIT (F16). |

## Verdicts on the eleven open issues

### 1. Sign U_q ↦ +Π_q versus Hsieh's JL(U_q) = −U_q
**Verdict: +Π_q is correct. Hsieh's sign is not to be imported; read literally it is false.** (derived, and checked against Hsieh's text)

- Hsieh defines the quaternionic operator by U_q f(x) = f(xϖ_q^D), ν(ϖ_q^D) = q, and on homology U_q x = xϖ_q^D (Hsieh §4.2 p. 30, §4.4 p. 31), and states JL(U_q) = (−1)U_q for q | N⁻ (§4.5 p. 34). His operator is our Π_q.
- Counterexample to the − sign in his own normalisation: N⁻ = 11, N⁺ = 1, weight 2. The two classes of B_11 have stabilisers of order 4 and 6, so Π_11 is the identity on the class set (stage 01, `ex:s01-Pi11`). The cusp form is 11a, with a_11 = +1 (split multiplicative reduction; η(z)²η(11z)² has q¹¹-coefficient 1). So U_11 ↦ +Π_11.
- Reason in general: local JL sends χ∘Nrd to St⊗χ. On χ∘Nrd, right translation by a uniformiser acts by χ(q). On the Iwahori-fixed line of St⊗χ, U_q acts by χ(q): in the unramified principal series containing St the two U_q-eigenvalues are 1 and q, and q belongs to the trivial quotient.
- Geometric confirmation at Γ_0-level: T_q acts on X_q(J_0(qM')) as the Frobenius permutation, which is right multiplication by a uniformiser (stage 05, `prop:s05-sign`(a), citing [Ri90, Prop. 3.8, Rem. 3.5(b)]; not re-checked, scan).
- Likely origin of Hsieh's sign: w_q = −U_q on q-new forms.
- Consequence: no ideal in stage 06 changes. The fix is F6.

### 2. Frob_q = qU_q or qU_q⁻¹ at Γ_1-level
**Verdict: it depends on two conventions, the functoriality and the model of X_1(N). Stage 05 fixes the first and not the second. With the Ribet–Stein conventions (μ_N-model, Picard), Frob_q = qU_q, as (X4) says.** (derived; anchored on two checked statements)

Notation: Σ the supersingular points, σ the arithmetic Frobenius permutation of Σ, I_d the moduli diamond. On T_t = Hom(X_q, ℤ_p(1)), Frob_q acts as q·(σ⁻¹)ᵀ (stage 05, Setting).

1. In either functoriality F, U_q² = ⟨q⟩ on the q-new part, where both are F applied to the same correspondences: on points U_q = −w_q and w_q² = I_q.
2. With Picard functoriality an automorphism g acts on X_q = H_1(dual graph) by pushforward. So ⟨q⟩ acts on ℤ[Σ]⁰ as I_{q*}; with Albanese it acts as I_{q*}⁻¹.
3. σ² is computed on a model of the supersingular curve over 𝔽_{q²} with Frobenius [−q]:
   - naive model, points (E, P): σ²(E,P) = (E, −qP), so σ² = I_q;
   - μ_N-model, points (E, α: μ_N ↪ E): σ²(E,α) = (E, [−q]∘α∘[q⁻²]) = (E, α∘[q⁻¹]), so σ² = I_q⁻¹.
4. Hence, with the sign + from Γ_0-level:

| model | functoriality | σ on X_q | Frob_q on T_t |
|---|---|---|---|
| μ_N | Picard | U_q⁻¹ | q·U_q |
| naive (ℤ/N) | Albanese | U_q⁻¹ | q·U_q |
| naive (ℤ/N) | Picard | U_q | q·U_q⁻¹ = q⟨q⟩⁻¹U_q |
| μ_N | Albanese | U_q | q·U_q⁻¹ = q⟨q⟩⁻¹U_q |

Anchors (checked): Ribet–Stein define T_p by Picard functoriality on the μ_N-model, say that it differs from Gross's (T_p)_* by ⟨p⁻¹⟩_*, and state "with our conventions" Frob_p = pT_p on the torus (Ribet–Stein §3, text before and at Lemma 3.17). Conrad's appendix proves (T_p)_* = F + ⟨p⟩_*F^∨ for Albanese functoriality (Thm 5.16 there), which gives Frob² − T_pFrob + p⟨p⟩ = 0 on the Tate module and hence q·a_q on the toric line.
At Γ_0-level all four rows agree. The fix is F1.

### 3. The factor-2 hypothesis
**Verdict: the correct hypothesis is "−1 ∈ U′ or −1 ∉ U". It is stated consistently in 01, 03, 04, 05; two stale sentences remain in 05 and 06.** (derived)

- tr(1_{x′}) = (|Γ_x|/|Γ_{x′}|)·1_x by orbit counting, so tr∘ν′ = ν∘π_* iff w_{x′}/|Γ_{x′}| = w_x/|Γ_x|. Since U′ ⊆ U this fails exactly when −1 ∈ U ∖ U′, and then tr∘ν′ = 2ν∘π_*. This is `prop:s01-adjoint`(c).
- 03 (C3): the degeneracies change the level only at q and −1 ∈ Iw_q, so the hypothesis always holds there. Correct.
- 04: inside the tower (s ≥ 1) the hypothesis holds; from a level containing −1 down to UU_s it fails. Correct.
- Hsieh (4.1) p. 29: Γ_{N,x} := (D^× ∩ xR̂^×x⁻¹)ℚ^×/ℚ^× (checked). At his levels −1 ∈ R̂^×, so #Γ_{N,x} = w_x. The factor 2 is against |Γ_x| (the import's `Nat.card`), not against w_x. Stage 04's correction is right.
- Stale: 05 `rem:s05-BN` and 06 (S1), H2 (F10).

### 4. Seed weight points inverted for adelic diamonds
**Verdict: stage 04 is right, and 05 and 06 use it consistently.** (derived)
For F ∈ M(UK_1; V_k) and f = ev∘F one gets f(xδ_d) ≡ d^{−(k−2)}f(x), so the adelic diamond acts by d^{2−k} on the weight-k piece, on functions and on the dual homological module. The weight-k point is P_k^ad = ker([u] ↦ u^{2−k}). The seed's P_k is right for classical diamonds. 05 matches the two by θ, 06 by [u] ↦ [u]⁻¹.

### 5. The case q ≡ −1 mod p
**Verdict: the restriction (H0⁻) is sufficient but not minimal, and `rem:s06-minus1` does not show that the seed was wrong. The seed's step (4) is correct in substance for q ≡ −1.** (derived; the R = T input is checked in Kim–Ota)

What the squeeze needs at the point P is 𝔠_q(f) ⊆ (ϖ^{t_f(q)}). Proof without any condition on q mod p beyond (H0):

1. ord 𝔠_q(f) is the largest t such that λ_f mod ϖ^t factors through 𝕋″ (definition of 𝔟).
2. Under (H0), 𝕋″_𝔪 ≅ 𝕋(M)_𝔪 with U_q ↦ the root of X² − T_qX + q^{k−1} congruent to U_q mod 𝔪 (see F2). The two roots are ≡ εq^{(k−2)/2} and εq^{k/2}; they are distinct mod 𝔪 because q ≢ 1.
3. Let t = t_f(q). Then ρ_f mod ϖ^t is unramified at q, low-weight crystalline at p, and of the same type as f at the primes of M. It is a point of the deformation ring that is minimal at q, "new" at the primes ℓ ∥ M where ρ̄ is unramified, and minimal elsewhere.
4. Kim–Ota's refined R = 𝕋 theorem ([KO, Thm 3.14, p. 12]; hypotheses: Assumption 2.1 and P_ρ ⊆ Σ; no ±1 condition) identifies that ring with the corresponding new quotient of the level-M Hecke algebra. So there is 𝕋(M)_𝔪 → 𝒪/ϖ^t matching λ_f on T_ℓ.
5. The image of T_q is tr ρ_f(Frob_q) = ε(q+1)q^{(k−2)/2} mod ϖ^t, so the root in step 2 maps to εq^{(k−2)/2} = a_q(f). Hence λ_f mod ϖ^t factors through 𝕋″. ∎

The prime q never enters the R = 𝕋 theorem, because the deformation problem is unramified at q. This is the seed's argument ("passing to the quotient that is new at the primes ℓ ∥ M where ρ̄ is unramified and applying the R = 𝕋 theorem there").

Why Kim–Ota need q ≢ ±1: their route compares with the level where every lift at q is allowed (level q²), and that step costs the Euler factor 1 − q⁻² ([KO, Prop. 2.15(1), p. 8]; checked). Their Selmer step needs only q ≢ 1 ([KO, Thm 2.13, p. 7]; checked). It is a property of their method, not of the statement 𝔠_q(f) = (ϖ^{t_f(q)}).

The other inputs at q ≡ −1: (Gor_R) has no condition at q (Hsieh §1.4 p. 4, citing Mazur–Wiles and Wiles; checked). (Gor_{R′}) needs only (CR, {q}), i.e. q ≢ 1 or ρ̄ ramified at q (Hsieh §1.4, Thm 4.5; checked). So Thm E and the Galois half hold, as 06 already says.

Caveat I could not close: step 4 needs the level-M data of f to match Kim–Ota's level N⁺_{ρ,Σ⁺}N⁻ (M squarefree at the primes where ρ̄ is unramified, f minimal at the others, P_ρ = ∅ or handled). For M = 1 nothing is needed beyond Assumption 2.1. The fix is F3; whether to restore the case is Fabian's decision.

### 6. Gorenstein hypotheses on both Hecke rings
**Verdict: consistent between 05 and 06. (Gor_R) is needed. (Gor_{R′}) is needed only for integrality, and one use in 05 is superfluous.** (derived)

- 06 `thm:s06-E`: (Gor_S) is used for the generator θ and for 𝔟 ≅ S′^∨. (Gor_{S′}) only makes the generator of S′[λ′] unimodular; over a DVR it is automatic. Re-derived, correct.
- 05 `prop:s05-Xiso`: needs both, and says so: H[𝔞] ≅ 𝔟 ≅ Hom(𝕋′, ℤ_p) is free iff 𝕋′ is Gorenstein. Correct.
- 05 `prop:s05-subquot`: the proof uses only Ann(𝔞) = 𝔟, which is Lemma D(a) and needs neither "𝕋 Gorenstein" nor "𝕋″ free" (F12).
- Sources agree: both follow from Hsieh under (CR, {q}), which (H0) + (H2) imply. 04's (CR_D), 05's Def. Xiso and 06's `rem:s06-CR` state the same condition (ℓ ≡ 1, not ±1; checked in Hsieh §1.4).

### 7. `prop:s03-phieis` for q ∈ {2, 3}
**Verdict: the proposition is true for every prime q and every M with ℓ ∤ qM, by an elementary proof. Neither Edixhoven nor [Ri90, Thm 3.12] is needed.** (derived)

Let B(e,e′) be the Brandt matrix of T_ℓ at level U_0(M), so T_ℓ[e] = Σ B(e,e′)[e′].

1. *Claim:* w_e divides B(e,e′) for e′ ≠ e. The group Γ_e/±1 permutes the ℓ+1 neighbours of e. Suppose a non-central γ ∈ Γ_e fixes a neighbour J ⊂ I. Then ℤ[γ] is ℤ[i] or ℤ[ω], a principal ideal domain, and the left-ℤ[γ]-stable sublattices of the right kind are J = πI with π ∈ ℤ[γ] of norm ℓ (locally at ℓ the lattice is free of rank one over ℤ_ℓ[γ]). So J ≅ I, i.e. J lies in the class e. Hence the neighbours in a class e′ ≠ e have trivial stabiliser in Γ_e/±1 and come in orbits of size w_e.
2. Put S(e,e′) = B(e,e′)/w_e for e ≠ e′. It is symmetric, by w_{e′}B(e,e′) = w_eB(e′,e) (stage 01, `prop:s01-adjoint`; formal in the import as `brandt_weighted_symmetry`).
3. T_ℓ acts on Hom(X,ℤ) = ℤ^E/ℤ1 by φ ↦ (e ↦ Σ B(e,e′)φ(e′)), and the rows sum to ℓ+1. So ((T_ℓ − (ℓ+1))φ)(e) = w_e·x_e with x_e = Σ_{e′≠e} S(e,e′)(φ(e′) − φ(e)) ∈ ℤ, and Σ_e x_e = 0 by symmetry.
4. So (T_ℓ − (ℓ+1))ℤ^E ⊆ W·ℤ[E]⁰, which is the image of X. ∎

The argument does not use q ≥ 5, cyclic stabilisers or the mass formula. The fix is F13.

### 8. `if:s02-indef` over ℤ, and stage 05's imports
**Verdict: the amended definition is imported correctly by 03 and 05. Stage 05 lacks the imports of `if:s02-quot` and `if:s02-coh`.**
03 (import block and the remark after `thm:s03-ribet`) and 05 (`rem:s05-D1`, import block, table) use H_1(BG(U,q),ℤ) = H_1(Γ_U,ℤ)/torsion. 04's block is unamended but its usage paragraph is right. The missing imports are F5; SPLIT's line "02 → 03, 04" must also name 05.

### 9. No finite per-level check for H_0 = V_{U_p^1}; only det(Ψ*Ψ)
**Verdict: respected.**
03 (R4) and 04 (`prop:s04-ekillsVk`, usage paragraph) say explicitly that the identification needs full strong approximation. 04 `lem:s04-ekills`(a) uses only connectivity for V = ℤ_p, which is correct. 04 does not use Ψ*Ψ. 06 `prop:s06-betti` uses det and the cokernel only; the cokernel is (𝕋/δ)² because q+1 is a unit and both off-diagonal entries lie in 𝕋(M)_𝔪 (derived).

### 10. Is the finite connectivity criterion a sufficient substitute for strong approximation?
**Verdict: sufficient for every statement at one fixed level; not sufficient for three groups of statements.** (derived; `prop:s02-BG` re-proved)

Sufficient, at the level where BG(U,q) is checked to be connected:
- 02: `prop:s02-quot`, `prop:s02-coh`(a),(b), `prop:s02-harm`, `prop:s02-free`, `def:s02-indef` and its ranks.
- 03: `thm:s03-ribet`(a), and (b) with H_0 defined as the cokernel; `cor:s03-ihara`(i),(ii); `prop:s03-LRdef`.
- 04: `lem:s04-ekills`; `thm:s04-lambdaribet` at each finite level.

Not sufficient:
- Everything that identifies H_0 or H⁰ with (co)invariants of U_p^1: `prop:s02-coh`(c),(d), `cor:s03-ihara`(ii′), `thm:s03-iharaH0`, `cor:s03-eis`, `rem:s03-T6`, `prop:s04-ekillsVk`.
- The Λ-adic statements: they need connectivity of BG(UU_s, q) and BG(U_0(q)UU_s, q) for all s ≥ 1. Connectivity at s+1 implies it at s, not conversely, so no finite check discharges it. Connectivity at all s still does not give density in U_p^1, because ∩_s K_s^1 is the upper unipotent group. This must be stated in `thm:s04-lambdaribet` (F7).
- The GL_2 amalgam needs strong approximation for SL_2, which the import has (`sl2_strong_approximation`).

### 11. Independent re-audit of stage 02
**Verdict: no mathematical error. The reviser's "all minor" rating is fair; the three real items (F3–F5 of Muse) were applied.** (derived; citations checked in Voight)

Re-derived: type and stabiliser statements of `lem:s02-tree`; `lem:s02-normone`; all implications of `prop:s02-BG`, including local surjectivity at type-1 vertices and surjectivity of s_1; the three bijections and stabilisers of `prop:s02-quot`; the signs of `prop:s02-coh`; closure of Γ_U in U_p equal to U_p^1; vanishing of invariants on V_k; the rank formulas; the torsion example (H_1 of SL_2(𝔽_3) *_{C_6} SL_2(𝔽_3) is ℤ/3, if there is one edge orbit); the T2 edge counts against the masses 8/24, 14/24, 30/24.
Checked in Voight: Main Thm 14.7.4 (Hasse–Schilling), Def. 28.5.1, Main Thm 28.5.3, 28.4.8, Cor. 28.5.12 exist with the stated content.
Remaining defects are minor: F8, F9, F17.

## Required fixes

### Major

**F1. `stage-05:hyp:s05-X` (X4), `rem:s05-Xstatus`, Setting — fix the model of X_s.**
Add to the Setting: "X_s is the model of X(Γ_1(Mp^s) ∩ Γ_0(q)) over ℚ classifying (E, α: μ_{Mp^s} ↪ E, C), as in Ribet–Stein §3; Hecke operators act by Picard functoriality." Then (X4)'s "Frob_q acts on the bottom piece as qU_q" stands. Replace the paragraph "Frobenius in (X4)" of `rem:s05-Xstatus` (now \stopen) by the four-row table of issue 2 with its two anchors, status \stpmc at Γ_0-level and \stexp at Γ_1-level. State in (X4): "equivalently σ_q = U_q⁻¹ on X_q(J_s), i.e. the Frobenius permutation of S_s is right multiplication by Π_q⁻¹ under φ_s". Update `prop:s05-sign`(a) and Proof strategy item 1, which say "Frobenius = x ↦ xΠ_q": at Γ_0-level both hold; at Γ_1-level, in the μ-model, it is Π_q⁻¹. Keep test T05-2 as validation. If Fabian prefers the naive model, (X4) must read q⟨q⟩⁻¹U_q instead.

**F2. `stage-06:lem:s06-decomp`(b) — the old quotient is a localisation.**
Replace (b) by: "If ρ̄_𝔪 is ramified at q then 𝕋″ = 0. Otherwise X² − T_qX + qS_q has two roots in 𝕋(M)_𝔪 that are distinct modulo the maximal ideal (they are ≡ U_q and qU_q mod 𝔪, and q ≢ 1 by (H0)); let α_q be the one congruent to U_q. Then 𝕋″ ≅ 𝕋(M)_𝔪 via U_q ↦ α_q. In particular 𝕋″ is Λ-free, and T_q = U_q + qS_qU_q⁻¹ lies in the image of 𝕋." Delete the Chebotarev argument for "T_q in the image" from the Inputs. As written, (b) asserts a ring of twice the correct rank. Also correct step (3) of `thm:s06-defect` ("hence for 𝕋″") and `Hyp.OldDecomp` in L6 accordingly. Check `prop:s06-betti`(b): it is consistent with the corrected form, since (α_q − εq^{(k−2)/2}) = (T_q − ε(q+1)q^{(k−2)/2}) up to a unit when q ≢ 1.

**F3. `stage-06:hyp:s06-H` (H0⁻), `cor:s06-fixed`, `rem:s06-minus1`, `thm:s06-defect`, R1, R2, M5, H3 — the case q ≡ −1.**
(a) Reword `rem:s06-minus1`: delete "seed step (4) is wrong as stated" and item (c) as an obstruction; say that [KO, Thm 1.1] as a black box excludes q ≡ ±1, and that the seed's direct argument does not use it.
(b) Add a second proof of the inclusion 𝔠_q(f) ⊆ (ϖ^{t_f(q)}): the five steps of issue 5, citing [KO, Thm 3.14, p. 12] and F2, under the explicit hypothesis (Lev_M): "the level-M Hecke algebra 𝕋(M)_𝔪 is the Hecke algebra of Kim–Ota's Thm 3.14 for Σ⁻ = {ℓ ∥ M : ρ̄ unramified at ℓ}, Σ⁺ = ∅". State that (Lev_M) holds for M = 1.
(c) State `thm:s06-defect` under "(H0⁻) or (Lev_M)". Status \stpmc in both cases.
(d) Delete the conjectured correction of size v_ϖ(q+1) (`rem:s06-minus1` "Decision", R2, M5). Keep HACS item H3 as a validation of (b), with predicted difference 0, and require that the Hecke algebra in H3 contains U_q.
Applying (b)–(d) reverses a stage-06 "seed correction"; it needs Fabian's decision (item 2 below). (a) is required regardless.

**F4. `stage-04:thm:s04-control`(b) — character piece and level do not match.**
As stated, the left side is one μ_{p−1}-eigenpiece and the right side is all of e·M(UK_1; V_k⊗𝒪), whose rank is r, the rank of the whole of M^ord(U). Replace by: "(b) M^ord(U) ⊗_Λ Λ/P_k^ad is dual to e·M(UK_1; V_k⊗𝒪). On the component where μ_{p−1} acts by ω^{−(k−2)}, it is dual to e·M(U·ι_p⁻¹U_0(p)_p; V_k⊗𝒪), for every k ≥ 2. For k ≥ 3 the latter equals e·M(U; V_k⊗𝒪) by p-stabilisation (\stexp in our normalisation)." Adjust `if:s04-Mord` only if it quotes (b) (it does not).

**F5. `stage-05` Dependencies — missing imports.**
Add import blocks for `if:s02-quot` and `if:s02-coh` in the exporter's wording (including "(c),(d) need full strong approximation"), each with `\status{imported from stage 02}` and "used in `def:s05-stages`, `prop:s05-nochain`" resp. "used in `rem:s05-degree`". In `SPLIT.md` change the heading "02 → 03, 04" to "02 → 03, 04, 05".

**F6. Sign of U_q under JL — make the four stages agree.**
- `stage-01:thm:s01-lambdaJL`: replace "U_ℓ ↦ ±Π_ℓ (ℓ | D; sign convention-dependent)" by "U_ℓ ↦ +Π_ℓ (ℓ | D), Π_ℓ acting by right translation; Hsieh writes −, which is not imported (stage 05, `rem:s05-hsieh`)". In `ex:s01-Pi11` replace "his quaternionic U_q is normalised differently" by "his operator is our Π_q; the example contradicts his sign".
- `stage-04` Proof strategy item 5: delete "where JL(U_q) = −U_q"; write "Hsieh's sign for U_q, q | D, is not imported".
- `stage-05:rem:s05-hsieh`: replace the \stopen alternative by the verdict of issue 1 (three bullets: his definition, the level-11 counterexample, the local argument). Delete "must be re-signed by U_q ↦ −U_q"; write "no statement of [Hs] involving U_q for q | N⁻ is used with his sign". Risk R3 likewise. T05-1 stays as validation.
- `stage-06` (S7): replace by "Stage 05 fixes U_q ↦ +Π_q; Hsieh's opposite sign is not imported. The ring isomorphism 𝕋′ ≅ 𝕋_B^ord is determined by the T_ℓ, ℓ ∤ Np, so no ideal depends on it."

**F7. `stage-04:thm:s04-lambdaribet` — state the connectivity hypothesis.**
Add to the hypotheses: "Assume BG(UU_s, q) is connected for every s ≥ 1 (equivalently Prop. quot holds at all these levels). This follows from Hyp.SA ∧ Hyp.HS; it is not a finite check, and it does not imply H_0 = V_{U_p^1}." Add the same sentence to `if:s04-lambdaribet`, and a line to the Lean track: the Λ-adic theorem takes `∀ s, BGConnected (U U_s) q` or `Hyp.SA ∧ Hyp.HS` as an argument.

### Minor

**F8. `stage-02:def:s02-Mhom`.** Replace N_x = Σ_{γ∈Γ_x} by stage 01's ν_V = Σ_{γ∈Γ_x/±1} (for V on which −1 acts trivially), and say that for the degeneracies the two differ by the same unit at every cell. Then drop Risk R4's "must fix".

**F9. `stage-02:if:s02-indef`, `stage-03` (R3).** Add one normative sentence to `if:s02-indef`: "The Hecke action on H_*(Γ_U,V) is the one induced from the homological complex M(·;V)_* with the transposed (right-translation) operators, so U_p = N_Up commutes with pushforward. Under ν this is the complex of traces on cohomological modules with the adjoint operators T_{g⁻¹}." In 03 (R3) refer to it; `thm:s03-iharaH0`(b) keeps exponent +1 for the cohomological operators and gets −1 in the normative convention.

**F10. `stage-05:rem:s05-BN`, `stage-06` (S1), H2.** Replace "weights #Γ_x instead of w_x (factor 2 at levels containing −1)" by "weights #Γ_{Np^α,x} = w_x (Hsieh (4.1); stage 04, `def:s04-BN`(iv)); no factor 2 against ⟨,⟩_w". In 06 (S1) and H2 write "Hsieh's weight is w_x; the factor 2 is against the import's |Γ_x|".

**F11. `stage-05` line "(ordinary, perfect: `if:s04-ekills`(c))" and the import block "Lemma ekills (a)–(c)".** Change to "(d)" resp. "(a)–(d)".

**F12. `stage-05:prop:s05-subquot`.** Drop "𝕋 is A-Gorenstein" and "𝕋″ A-free" from the hypotheses, cite Lemma D(a) only, and correct the note after the proposition (the freeness of 𝕋″ is not used at all). `if:s05-subquot` changes accordingly; 06 uses it only as a cross-check.

**F13. `stage-03:prop:s03-phieis`.** Change the status to \stproved, insert the four-step proof of issue 7, state it for all primes q and all M with ℓ ∤ qM, and keep [Ri90, Thm 3.12] and [Ed91] as geometric cross-references. Remove "We do not claim the proposition beyond the range covered by [Ri90]". Update `stage-06` (S5) ("unresolved for q ∈ {2,3}") to "resolved".

**F14. `stage-04` import block for `if:s02-quot/coh/indef`.** Append the two amendments already used in the following paragraph: "over ℤ, 𝒳^{(q)} = H_1(BG(U,q),ℤ)" and "H_0 = V_{U_p^1} needs full strong approximation".

**F15. Import blocks of `if:s01-hecke` in 02, 03, 04, 05, 06.** Replace "Self-adjointness for the pairing" by the exporter's sentence "T* = T_{g⁻¹}; T_ℓ is self-adjoint only at level U_0(M)".

**F16. Lemma D and `if:s06-defect`.** Either add an interface `if:s06-lemD` (Lemma D(a)–(c)) to stage 06 and import it in stage 05, or restate Lemma D(a) with its two-line proof in stage 05. With F12 only (a) is needed in `prop:s05-subquot`; `prop:s05-Xiso` needs (b). Record `if:s06-defect` and the Lemma D dependency in `SPLIT.md`.

**F17. `stage-02:def:s02-indef`.** Write "At a free level: rk 𝒳(U) = (q−1)|X_B(U)| + 1 and rk 𝒳(U;V_k) = (q−1)(k−1)|X_B(U)| for k > 2"; the second formula is false at non-free levels.

**F18. `stage-06` (S3).** T ↦ T* is not Λ-linear (⟨d⟩* = ⟨d⟩⁻¹); it is semilinear for [u] ↦ [u⁻¹]. Replace the sentence by "Hsieh's B_N is Hecke-equivariant (the Atkin–Lehner twist turns adjoints into the operators themselves), so η^B_F is computed in 𝕋_B itself".

**F19. `stage-06:prop:s06-betti`, D1, H1.** Mark every use of the amalgam for k ≥ p (T4 at k = 28, 44, 60, 124) as \stexp, since `if:s03-amalgam` covers only l > k. Either stage 03 exports the 𝔪-localised ordinary Mayer–Vietoris sequence, or the prediction stays an expectation.

**F20. `stage-04` Risk R2.** Delete "which is exactly where stage 06's defect is non-trivial". (CR_D) excludes only ℓ ≡ 1 with ρ̄ unramified, which (H0) excludes anyway; the defect is non-trivial whenever ρ̄ is unramified at q.

## Items for Fabian

Where the seed itself is wrong or imprecise:
1. Seed §12: strong approximation for B¹ "exists in this shape in Lean". It does not, in our import or in Mathlib (stage 02, confirmed).
2. Seed §2.5: the formula U_p = [U diag(1,p) U] and the requirement "commutes with pushforward" contradict each other; the plan keeps the requirement (stage 01, re-derived by the stage; not re-derived here beyond the coset lists).
3. Seed §2.6: P_k = ker([u] ↦ u^{k−2}) is the weight-k point for classical diamonds, not for the adelic ones the seed defines (issue 4).
4. Seed Def. 5.6: H_1(Γ_U, ℤ) has 2- and 3-torsion; over ℤ the indefinite stage must be H_1 of the graph.
5. Seed Prop. 5.3: the proof uses Hasse–Schilling without saying so.
6. Seed §9, Lemma D and Thm E: the Gorenstein hypothesis on R is hidden, and the freeness of S/𝔞 is not justified.
7. Seed §9, (Im): no cited theorem uses it (stage 06; I confirmed this for Kim–Ota and Hsieh only).
8. Seed §9, step (4): correct in substance, including q ≡ −1 (issue 5), but its hypotheses on M are not stated and its citations do not match the argument.
9. Seed Prop. 10.1(b): tautological or false (stage 05, `rem:s05-nochain`).
10. Seed (G2), (X4), (L1): "Frob_q = qU_q on the torus" is true at Γ_1-level only for two of the four convention pairs (issue 2).
11. Seed §11: the displayed zig-zag joins two parts that live at different primes.
12. `SPLIT.md` cites Hsieh's sign and "non-Eisenstein + residual condition" loosely; SPLIT needs the edits of F5 and F16.

Decisions that are yours:
1. **Model and functoriality for Hyp.X** (F1). Recommendation: Ribet–Stein conventions (μ_N-model, Picard), so that the seed's Frob_q = qU_q stands.
2. **Restore q ≡ −1 in the defect theorem** (F3 (b)–(d)). Recommendation: yes, under the explicit hypothesis (Lev_M), with M = 1 as the proved case; a second reader should check step 4 of issue 5 against Kim–Ota §3 before the talk claims it.
3. **Hsieh's sign.** Recommendation: treat it as an erratum and do not import it; consider writing to the author.
4. **Keep or drop (Im).** Keeping it is harmless.
5. **Strong approximation in Lean.** Keep Hyp.SA and Hyp.HS as registered hypotheses; the Λ-adic statements cannot be discharged by finite checks (issue 10).
6. **Kim–Ota Cor. 5.4** claims the N⁻-new quotient is Gorenstein with no condition on N⁻, which conflicts with Böckle–Khare–Manning at trivial primes. The plan uses Kim–Ota only where q ≢ 1, so nothing breaks; do not cite Cor. 5.4 beyond that.
