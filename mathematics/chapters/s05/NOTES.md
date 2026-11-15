<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Stage 05 — NOTES (S05-R1: independent second reader of the normalisation chain)

> **Current state (S05-M9, after batch 6 and Fable audit M8):** all seven normalisation items are CONFIRMED (the "GAP" verdict below is the
> first-read state, historical). Open: (c2) of `prop:s05-Xlambda` (list in `rem:s05-c2open`), (d4), and the open decisions FD1/FD2. The FD1 table is
> now anchored at row 2 (audit M8-3); Ribet-Stein Lemma 3.17 is a consistency check.

- Reader: package B2 (abhijit/b2-s05-r1). I have not written any part of `sign.tex` or `hypX.tex`.
- Read: `chapters/s05/sign.tex` (M1, 25eefd8) and `hypX.tex` (M3, b3e5b15) on `abhijit/s05-math` @ b3e5b15, against the stage tex
  and the literature.
- Pages are printed pages. Ribet–Stein printed = PDF − 4; this holds for Conrad's appendix too, e.g. Cor. 5.3 is p. 66 = PDF 70.
  The pagination comment in the header of `sign.tex` ("main text: pdf − 1; appendix: pdf + 1") is wrong, but every page it cites
  is correct.
- **Item count.** The R1 row of `stage-05.md` §1 names six items: ε, e, δ, the Frobenius table (FD1), the (X4) Rosati twist and the
  factor 2. The batch request says "7 items". Item 7 below covers the remaining normalisations of §0 (i): `U_p ↦ N_{U_p}` and the
  positive monodromy pairing.

**Overall verdict: GAP.** Items 1, 2, 5, 6 and 7 are CONFIRMED. Item 3 (δ) and the derivation of item 4 (FD1 table) have gaps.

| # | item | verdict | where |
|---|---|---|---|
| 1 | ε = +1 | CONFIRMED | `prop:s05-sign`(a),(b) |
| 2 | exponent e = δ | CONFIRMED | `prop:s05-sign`(c), `lem:s05-consistency`(a) |
| 3 | diamond convention δ = +1 | **GAP** | `prop:s05-sign`(d) |
| 4 | Frobenius table (FD1) | **GAP** (derivation step (ii)); row 1 itself is cited | `rem:s05-Xstatus` |
| 5 | (X4) Rosati twist | CONFIRMED | `hyp:s05-X`(X4), `lem:s05-consistency`(b) |
| 6 | factor 2 (F2) | CONFIRMED | `rem:s05-factor2`, `lem:s05-consistency`(c) |
| 7 | `U_p ↦ N_{U_p}`, positive monodromy pairing | CONFIRMED (the conditional clause of 3 excepted) | `lem:s05-consistency`(d), (X2) |

## 1. ε = +1 — CONFIRMED
- Checked each step of (a) on the page images of Ribet 1990:
  - Prop. 3.1, p. 439: X = degree-0 divisors on Σ(M).
  - Prop. 3.7, p. 445: w_q = −T_q on the torus.
  - Prop. 3.8(i),(ii), p. 446: w_q swaps the components and acts as x ↦ x^(q); T_q on X is induced by the Frobenius permutation.
    The proof combines the vertex swap with w_q, so the two signs cancel.
  - Rem. 3.5(b), p. 441: the Frobenius permutation is right multiplication by an idele that is 1 away from q and a uniformiser at q.
- Robustness: if the class set were read as Û\B̂^×/B^× (left action), inversion turns "left by Π" into "right by Π^{-1}". At
  Γ0-level Π_q² acts trivially (step (5); checked: q^{-1}z_q is a unit scalar idele lying in U0(M')), so the answer is the same.
- Step (5) and the Picard/Albanese remark are right: on the q-new quotient, T_q = −w_q is an involution.
- Independent checks:
  - (b) 11a with Π_11 = id.
  - Local JL: on the new line of St, U acts by +1 (Hsieh Prop. 2.2, pp. 12–13; Taïbi §2.7, p. 32), and St ↔ trivial of D^×
    (JL70 p. 484; Taïbi Cor. 3.25, p. 56).
  - So ε = +1 also holds in every even weight (`prop:s05-signe`, S05-M2).

## 2. Exponent e — CONFIRMED (as the conditional statement (c))
- Li's a_q² = χ(q)q^{k−2} for q ∥ level with χ defined mod level/q: Li 1975, Thm. 3(iii), pp. 295–296; Ribet–Stein Lemma 3.15, p. 44.
  It applies to every q-new newform of level N_f q with (N_f, q) = 1. U_q and ⟨q⟩ commute with f ↦ f(dz), (d, q) = 1.
  So U_q² = ⟨q⟩ holds in H^new.
- Definite side: Π_q² = S_q = ⟨q⟩^{-1} (eq. `eq:s05-Sell`; from Prop. s01-relations (a),(b)). The scalar q^{-1}z_q is ≡ δ_{q^{-1}}
  modulo U_1(N), given the stage-01 convention that δ_d ≡ diag(1,d).
- The character-space argument for "⟨q⟩² = 1 iff all χ(q) = ±1" is correct.
- The edge cases N ≤ 2 and q ≡ ±1 mod N are stated.

## 3. δ = +1 — GAP (`prop:s05-sign`(d), the clause "δ = +1 for the Picard action on X_q(J_s)")
- B1 marks this *to prove* and gives two supports:
  - (α) the stage-01 flag (adelic ⟨d⟩ = classical ⟨d⟩^{-1}) on **forms**;
  - (β) the forcing argument of `lem:s05-consistency`(d).
- Missing input for (α): the transfer from forms to the Picard action on J_s. The literature shows that this transfer is not the
  identity. Ribet–Stein §2.3.1.1, p. 29: the Picard-induced diamond is (⟨p⟩)^*(E,α) = (E, α∘[p^{-1}]), and RS's Picard T_p is not
  the usual Hecke action on cusp forms (Gross's Albanese (T_p)_* is). Conrad's appendix, Thm. 5.8, p. 69: adjunction interchanges
  the ( )_* and ( )^* actions, the adjoint of T_p is ⟨p⟩^{-1}T_p, and that of ⟨n⟩ is ⟨n⟩^{-1}. So the Picard Hecke algebra acts on
  forms through h ↦ h^Ros, which sends ⟨d⟩ ↦ ⟨d⟩^{-1}. That is exactly the θ ↔ θ^Ros ambiguity of `prop:s05-AL`.
- (β) resolves the ambiguity only if the GL₂-side U_p in H_s (Picard functoriality, μ_N-model) is the operator modelled by N_{U_p}
  (Remark s01-Upconv). This is *expected*, not proved.
- Needed: a computation or reference fixing which of U_p and U_p^* the Picard action of the double coset (1 0; 0 p) on J_s is, in
  the μ_N-model. Equivalently, which of θ and θ^Ros the Picard action matches. T05-2 is the planned check.
- No wrong statement in the text (the status is honest). The gap is the missing step.

## 4. Frobenius table (FD1) — GAP in the derivation; row 1 is CITED
- **Row 1 has a direct literature anchor.** Ribet–Stein Lemma 3.17, p. 46: Frob_p acts as pT_p on T(F̄_p), for X_1(M,p) =
  Γ1(M)∩Γ0(p) at the bad prime p, with RS's conventions (μ_N-model, Picard T_p, §2.3.1.1, pp. 28–29). The geometric Frobenius
  endomorphism acts on F̄-points like the arithmetic Frob, so this is row 1: Frob_q = qU_q on T_t. RS give no proof; they cite
  their reference [26, p. 31].
  - `rem:s05-Xstatus` calls RS 3.17 a good-reduction-type "anchor" that does not fix the Γ1-level statement. In fact it is a
    Γ1(M)∩Γ0(p) statement on the torus.
  - Suggested change for B1/M9: row 1 becomes *cited* (RS L. 3.17), *provided* RS's torus Frobenius is read as the arithmetic one.
- **Derivation step (ii)** ("the Picard-induced action of the moduli diamond I_d on Z[Σ]^0 is the pushforward of I_d") is unchecked
  (B1: *expected*). On divisors, RS p. 29 says that the Picard action of ⟨p⟩ is the pushforward of I_{p^{-1}}, i.e. the inverse.
  - Whether a second inversion occurs in passing to X = Hom(T, G_m) ≅ H_1(dual graph) is not tracked in the text.
  - If (ii) is inverted and (iii) is kept, the μ_N/Picard row comes out as σ_q = U_q, which contradicts RS L. 3.17. So (ii), (iii),
    or the reading of "⟨q⟩" in (i) contains an error, or else the extra dualisation in X compensates.
  - Step (iii) (σ_q² = I_q^{-1} in the μ_N-model via F = [−q]) I find plausible: [q²] on μ_N and [−q] on E. It is not checked
    against a reference.
- Naive model: Diamond–Im (8.4.1), p. 73 (Γ1(N)∩Γ0(p), naive model): the composite of a degeneracy map with i_F is ⟨p⟩. This
  supports the claim that the naive model introduces a ⟨q⟩-twist, but the text should state which composite.
- Needed: a line-by-line functoriality check of (ii) through X = Hom(T, G_m), or replacing the derivation by RS L. 3.17
  (+ Diamond–Im (8.4.1) for the naive rows).

## 5. (X4) Rosati twist — CONFIRMED
- The top piece T_ℓJ/T^{I} ≅ X(J^∨) ⊗ Z_ℓ (SGA7 IX, via Illusie p. 41, Raynaud p. 17) is covariant in J through h ↦ h^∨. Transported
  by the principal polarisation λ (λ^{-1}h^∨λ = h^Ros), h acts on X(J) ⊗ Z_ℓ as X(h^Ros), and under φ_s this is θ_s(h^Ros). This
  matches (X4).
- Rosati duals: T_ℓ^Ros = ⟨ℓ⟩^{-1}T_ℓ and ⟨d⟩^Ros = ⟨d⟩^{-1} (Conrad Cor. 5.3, p. 66; Thm. 5.8, p. 69).
- U_q^Ros = U_q^{-1} = ⟨q⟩^{-1}U_q: U_q is scalar a_q, with |a_q| = 1, on the Petersson-orthogonal summands spanned by the f(dz).
- Brandt adjoints of `lem:s05-consistency`(b), recomputed:
  - T_ℓ^* = S_ℓ^{-1}T_ℓ = ⟨ℓ⟩T_ℓ = θ(⟨ℓ⟩^{-1}T_ℓ);
  - Π_q^* = Π_q^{-1} = ⟨q⟩Π_q = θ(⟨q⟩^{-1}U_q);
  - ⟨d⟩^* = ⟨d⟩^{-1} = θ(⟨d⟩).
- Compatibility of the monodromy operator N: x ↦ ⟨x,·⟩_w with the actions: N(θ(h)^*x) = N(x)∘θ(h), the transpose action on the
  bottom piece.
- Reading θ(U_p^Ros) := θ(U_p)^* follows from (X2) and the Rosati-equivariance of u_s.
- Caveat (minor): the Rosati-equivariance of u_s is the functoriality of Grothendieck's pairing, SGA7 IX. It is now in literature/
  as a scan (IX Thm. 11.5 on p. 455 checked). The functoriality statement itself was not located page by page.

## 6. Factor 2 (F2) — CONFIRMED
- −1 ∈ U_1(Mp^s) iff Mp^s ≤ 2 iff s = 0 and M ≤ 2.
- w_x = 1 at s ≥ 1: Γ_x ⊂ U_1(p) is torsion and unipotent mod p, p ≥ 5.
- On the GL₂ side, deg(X_1(N) → X_0(N)) = φ(N)/2.
- `lem:s05-consistency`(c) recomputed:
  - integrality of w_y/w'_{x'} (−1 ∈ Γ_y \ Γ'_{x'} makes the index even);
  - the degree is constant by orbit counting (−1 acts freely on U_s/U_{s'} since −1 ∉ U_{s'});
  - projection formula;
  - π^!_w = π^* for s ≥ 1, and π^!_w[y] = w_yπ^*[y] = ½·transfer at s = 0, M ≤ 2 (as Prop. s01-adjoint(c)).
- Edge cases: M = 1, 2 included; s' = s is trivial.

## 7. U_p ↦ N_{U_p}; positive monodromy pairing — CONFIRMED
- `lem:s05-consistency`(d): the GL₂-side U_p double coset has the same representatives (1 j; 0 p) at Γ_s and Γ_{s'} (p | level,
  s ≥ 1), so β commutes with U_p. The forcing chain is correct. The non-commutation of U_p^* needs rk e Z_p[S_s] ≥ 2, which is
  stated. The rank-mod-p argument is correct.
- Positivity: the monodromy form on the character group of a principally polarised Jacobian is positive definite (Raynaud, Ast.
  196–197, Thm. 5, p. 17; Kohel §4.2, p. 10). Illusie Thm. 2.7, p. 41 ("with the opposite sign") is therefore fixed by positivity, as
  in (X2).
- Exception: the clause "this pins δ = +1" depends on item 3.

## Other observations (not items)
- `hypX.tex` (X4) refers to `thm:s05-G(v)` for the filtration. In S05-M5 (`geometric.tex`) the filtration is Thm G **(v)** (G4); the
  labels match.
- `prop:s05-AL` (R1) "conjugation by w is the Rosati involution": Conrad Cor. 5.3, p. 66 confirms it for X_1(N) with w_ζ.

## Batch 5 re-read (D3 second reader)

- Reader: `abhijit/d3-s05-reader`, fresh context; not B1, not the D3 writer.
- Read: `sign.tex` and `hypX.tex` on `abhijit/s05-math` @ 055e1b8 (merged here), checked against the batch-5 spec, the writer's report
  20261114-220803Z and the literature.
- Pages: Ribet–Stein printed = PDF − 4 (incl. Conrad); SGA 7 printed = PDF − 5 (checked on rendered images); Hi86a = journal pages.

**Overall: one GAP (item 4, in the list of missing steps for (d)); items 1, 2, 3, 5 CONFIRMED.**

| # | item | verdict | writer's status | agree? |
|---|---|---|---|---|
| 1 | `prop:s05-sign`(d) via `lem:s05-Up-pullback` | CONFIRMED | closed (pmc) | yes; caveat r_Λ ≥ 1 is correctly stated |
| 2 | FD1 rows 2, 3 via `lem:s05-models` | CONFIRMED | closed (pmc from row 1) | yes; minor status remark on row 1 |
| 3 | (R2) | CONFIRMED | closed (pmc) | yes |
| 3 | (R1) at Γ_s; restatement on X_q | CONFIRMED (still open; restatement correct) | open, `\provisional` | yes |
| 4 | `prop:s05-Xlambda`(c), (d) | **GAP** (the missing-step list for (d) is incomplete) | open (sketch) | yes, open; list to be completed |
| 5 | SGA 7 IX pages | CONFIRMED | closed | yes |

### Item 1: `lem:s05-Up-pullback` and `prop:s05-sign`(d) — CONFIRMED

Step-by-step:
1. **Which correspondence.** Picard U_p := a_*b^* (a forgets D, b is the quotient by D).
   - RS §2.3.1.1 p. 28: π1 forgets, π2 is the quotient, T_p = (π1)_*∘π2^*, Picard functoriality, for p ∤ N.
   - Conrad Def. 5.5 p. 68: T_p^* = Alb(π1)∘Pic^0(π2).
   - Conrad pp. 64–65: π1 forgets, π2 is the quotient. For p | N his Γ_1(N,p) = Γ_1(N)∩Γ_0(p)^t, i.e. C meets ⟨P⟩ trivially.

   So the lemma's U_p is the μ_N-analogue of Conrad's T_p^*, and it is the same operator as in the Setting/HypX ("Picard functoriality").
   Thm 5.8 (p. 69, p ∤ N) is not used. Lemma 5.4 p. 67 (Pic^0(f)=f^*, Alb(f)=f_*) is used consistently: Pic^0 for b, Alb for a.
   - CONFIRMED.
2. **ρ is well defined, and aρ = πa', bρ = πb'.** With s ≥ 1, ι'(μ_p) = ι'|(μ_p), so the condition D ∩ ι(μ_p) = 0 is the same at both levels.
   The identity bρ = πb' is restriction of χ∘ι'. CONFIRMED.
3. **The a-square is cartesian on the open curves.**
   - The moduli problem is fine because N_s ≥ p ≥ 5 > 4 (RS p. 28). The objects are rigid, so a T-point of the fibre product determines a unique isomorphism f, and f^{-1}(D_1) is the unique lift.
   - Correctly, only the a-square is claimed. I checked that the b-square is *not* cartesian in general: two lifts ι', ι'' of ι can differ by a homomorphism μ_{N_{s'}} → D that kills μ_{N_s}. This is consistent with U_p^* failing to commute.
   - CONFIRMED.
4. **Base change on divisors.** π^*a_* = a'_*ρ^*. Over the open curves π and ρ are finite étale in characteristic 0, so all multiplicities are 1. Then ρ^*b^* = b'^*π^*. Cusps map to cusps under both a and b, so b^*(divisors on X°) is supported on Y°. CONFIRMED.
5. **From divisors to J.** Moving lemma; two homomorphisms of abelian varieties over ℚ that agree on ℚ̄-points are equal. CONFIRMED.
6. **(b), from J to X_q.** Néron mapping property. J_s is semistable at q, since q ∤ Mp^s. A homomorphism maps the identity component to the identity component, and the maximal torus into the maximal torus (a torus has trivial image in an abelian variety). Then apply the contravariant X_q. This is consistent with the convention in hypX (X3)/(X4): bottom piece = transpose, β = X_q(π^*). CONFIRMED.
7. **(c), the Albanese dual.** Pushforward along bρ = πb', plus base change ρ_*a'^* = a^*π_* from the same cartesian square. CONFIRMED.
8. **Naive model.** ⟨p^{s'-s}P'⟩ and ⟨P'⟩ have the same subgroup of order p, because p | Mp^s. CONFIRMED.
9. **Forcing chain of (d).**
   - Lemma (b) at s' = s+1, (X1) and (X3) give θ'_s(U_p)π_* = π_*θ'_{s+1}(U_p).
   - `lem:s05-consistency`(d) shows that U_p^* fails this when r ≥ 2.
   - The rank is r_Λ p^{s-1} (stage-04 control). So r ≥ 2 at s = 2 iff r_Λ ≥ 1; for r_Λ = 0, θ and θ^Ros are not separated. This is stated correctly.
   - (d) is a statement about the shape of HypX, which itself stays a hypothesis. This is also stated.
   - Rem. `s05-delta` cites Conrad Thm 5.1 p. 65: it does identify T_p^* (incl. p | N) with the classical U_p on H^1. That is a consistency remark only.
   - CONFIRMED.

Agree with the writer's status: **closed, proved modulo cited**. No literature source exists; the in-chapter proof is sufficient.

### Item 2: `lem:s05-models`, FD1 rows 2 and 3 — CONFIRMED

Step-by-step:
1. **φ is defined over ℚ.**
   - x ↦ e_N(ι(·), x) gives an isomorphism of group schemes E[N]/ι(μ_N) ≅ ℤ/N: the kernel is ι(μ_N)^⊥ = ι(μ_N), and the orders match.
   - P' := ψ(x) is the section corresponding to 1. It is canonical, hence descends, and it has exact order N.
   - So φ is a morphism of the moduli problems over ℚ, not only over ℚ(ζ). CONFIRMED.
2. **φ is an isomorphism.**
   - Over ℂ it is Conrad's w_ζ (p. 64: (E,P) ↦ (E/⟨P⟩, P' mod P) with ⟨P,P'⟩_N = ζ), with C carried along.
   - w_ζ^{-1} = w_ζ (p. 68), so φ is bijective on ℂ-points.
   - A bijective morphism of smooth, geometrically connected curves in characteristic 0 is an isomorphism.
   - The extension to C (quotient by E[N], NC = C since (N,q)=1) is correct.
   - CONFIRMED.
3. **(b) diamonds.** e_N(ι(ζ^d), d^{-1}x) = ζ, so φ⟨d⟩^μ = ⟨d^{-1}⟩^nv φ. CONFIRMED.
4. **(c) U_q.**
   - e_N(χu, χv) = e_N(u, v)^{deg χ} with deg χ = q, so y = χ(cx), cq ≡ 1 (N).
   - The q-structure E[q]/D maps compatibly, because ψ(E[q]) = E'[q] (deg ψ = N is prime to q).
   - Hence φb^μ = ⟨q^{-1}⟩^nv b^nv φ̃ and φa^μ = a^nv φ̃.
   - I recomputed U^μ_qφ^* = φ^*U^nv_q⟨q⟩_nv^{-1} and ⟨d⟩_μφ^* = φ^*⟨d⟩_nv^{-1}.
   - CONFIRMED.
5. **Transport to X_q.**
   - φ^* is defined over ℚ, so it extends to the Néron models over ℤ_q and is Frob_q-equivariant on X_q.
   - X_q(φ^*) intertwines U^μ_q with U^nv_q⟨q⟩_nv^{-1}, so σ_q = (U^μ)^{-1} becomes ⟨q⟩_nv(U^nv)^{-1}, which equals U^nv by U_q² = ⟨q⟩.
   - The relation transports between the models (checked).
   - This gives row 3; row 2 is row 3 with the functoriality switched (Albanese U = U^Ros = U^{-1} on the q-new part; Alb(f) = Pic^0(f)^∨ by Conrad Lemma 5.4, valid for any finite map of curves).
   - CONFIRMED.
6. **Independent plausibility check.**
   - Under φ, the μ_N/Picard U_q and ⟨d⟩ become U^{-1} = U^Ros and ⟨d⟩^{-1} = ⟨d⟩^Ros on the q-new part. So μ_N-Picard ≅ naive-Albanese, which is why rows 1 and 2 agree.
   - Row 2 is the usual Eichler–Shimura normalisation of the ( )_*-action, for which Conrad Thm 5.16 p. 74 gives tr Frob = T_p at good primes.
   - Consistent, but not a proof.

**Minor status remark (not a GAP).** The identification of RS's bad-prime T_p (L. 3.17 p. 46, given without definition) with the recipe a_*b^* is a *convention*, as the text says (sign.tex, Xstatus remark). But the status summary still calls row 1 plain "\stcited". Suggest: "cited, under the convention of `lem:s05-models`(c)". Rows 2 and 3 inherit the same convention.

Agree with the writer's status: **closed, proved modulo cited (from row 1)**.

### Item 3: AL inputs

**(R2) — CONFIRMED.**
- SGA 7 IX p. 441 (PDF 446): M is covariant in A_K; the pairings (10.2.7) of biextensions are compatible with inverse images; the Weil biextension gives the monodromy pairing.
- From (10.2.6) on the same page, M' is the character group of the torus of A (contravariant), and M = X(T_{A'}). This matches the writer's identification M' = X_q(J_s).
- I recomputed both steps:
  - u(M(α)x, y) = u(x, M'(α^∨)y), with M'(α^∨) = X_q(α);
  - after transport by λ_t, v(x, X_q(α)y) = v(X_q(α^Ros)x, y).
- (10.3.5) p. 443: u^{K'} = e(S'/S)u^K. Thm 10.4 p. 444: the integral u, and symmetric positive non-degenerate u(x, ξ_t y).
- p. 439: verifications "left to the reader", so pmc is right.

**(R1) — open, agree.**
- The restatement on X_q is **correct and necessary**. In End J_s, (R1) for U_q fails as soon as J_1(Mp^s) ≠ 0.
  - Check: on span{f, f(qz)}, take the orthonormal vector e_2 = q f(qz)/‖f‖ (since ‖f(qz)‖ = ‖f‖/q in weight 2). Then U_q e_2 = q f/‖f‖ has norm q > √q = spectral radius. So U_q is never normal there, even when a_q = 0.
  - U_q^Ros (the Petersson adjoint on the cotangent space, Conrad p. 68) therefore does not commute with U_q, while wU_qw^{-1} does.
- The stated missing step is exact, and Cor. 5.3 p. 66 does not give it:
  - w_{Mp^sq} normalises Γ_s (checked: c ≡ 0 mod Mp^sq), but it is ramified at q.
- Possible third route, not checked: w_{Mp^sq} = w_q w_{Mp^s} up to a diamond, and w_q is defined over ℚ and acts on each q-new isotypic span by a scalar (Atkin–Li).

### Item 4: `prop:s05-Xlambda`(c), (d) — GAP (missing-step list for (d) incomplete); status "open" agreed

**(c).** The list (i)–(iii) is adequate.
- Remark: (i) must include the intertwining of w_{p^{s'}} with the two degeneracy maps. It is only sketched in the "Not (X3)" part of `prop:s05-AL`, and it is needed to choose the Brandt counterpart compatibly along the tower.

**(d) GAP.**
- The statement defines Tord := lim e T_pJ_s without fixing the transition maps or which U_p defines e.
- With the Setting's Picard U_p:
  - Lemma `s05-Up-pullback`(a),(c): Picard U_p commutes with π^*, and the Albanese U_{p,*} commutes with π_*.
  - Under HypX with r ≥ 2, the Picard U_p does not commute with π_*: the bottom piece already fails. Its U_p-action is the transpose of N_{U_p}, its transitions are the transposes of π^* (the writer's (d)(ii)), and N_{U_p} does not commute with π^* (adjoint of `lem:s05-consistency`(d), w = 1).
- So along π_*, the Picard e is not compatible with the transitions on *either* outer piece. The sketch's sentence "for U_p the top-piece action is U_p^* ... so this limit must be taken with the twist" treats only the top piece.
- Hida (Hi86a, Invent. 85, pp. 595–596) builds his projective system along the covariant pushforward, with J_r viewed as Albanese and the Hecke algebra acting covariantly. His e comes from T(p) in that action, and he warns that the Pic (right) and Alb (left) actions differ.
- Missing step: fix Tord with the Albanese projector e_* (= Picard e^Ros), or twist the whole tower. Then recompute both outer pieces:
  - with e_*, the top piece carries N_{U_p} (possibly no twist needed);
  - the bottom piece carries the transpose of U_p^*, i.e. lim Hom(e^*Z_p[S_s], Z_p(1)) along the transposes of π^*.
- This must then be matched with Hom_Λ(M_ord, Λ)(1) through the perfect pairing of stage 04.
- (d)(iii): the Hida page is now located: the tower is defined on pp. 595–596. The Λ-freeness theorem itself was not checked by me.
- The middle piece (lim of T_pJ_1(Mp^s)^{⊕2} via the two degeneracies) is also not in the list. Its transitions need the same functoriality choice.

### Item 5: SGA 7 pages — CONFIRMED (rendered page images)
- Thm 2.4 (orthogonality theorem): p. 338 = PDF 343.
- (9.1.2) (u_ℓ : M_ℓ ⊗ M'_ℓ → ℤ_ℓ): p. 418 = PDF 423.
- §10 start, 10.1, 10.2: p. 439 = PDF 444.
- (10.2.2)–(10.2.5): p. 440.
- (10.2.6)–(10.2.8), with the covariance and inverse-image remark: p. 441 = PDF 446.
- (10.3.5): p. 443 = PDF 448.
- Thm 10.4 (a), (b): p. 444 = PDF 449.

All cited as in the text.

## Batch 6 re-read (E3 re-reader; `abhijit/s05-math` @ d1c7c7f, `hypX.tex`)

I re-read the batch-6 text independently, against the PDFs and against stage 04 @ 47c2984 (read-only). I checked page numbers in the PDF text layer. Literature is paraphrased.

| item / sub-claim | verdict | writer's status | agree? |
|---|---|---|---|
| (a) `lem:s05-R1` (R1) at Γ_s: T_ℓ, ⟨d⟩, U_ℓ, U_p; U_q on X_q; w² = 1 | **CONFIRMED** | closed, pmc | yes |
| (b) twist changed to w_{Mp^s}∘U_p^{-s} (`\provisional`) | **CONFIRMED** (justified) | provisional | yes |
| (b)/(c1) [ , ]_s perfect and H_s-equivariant | **CONFIRMED** | pmc | yes |
| (b)(iii) the s04 pairing with N_{U_p}, via def:s04-BN (o), (v) | **CONFIRMED** | closed by citation | yes |
| (b)/(c2) missing-step list (i), (ii), (iv) | **GAP (minor; list incomplete)**; the open status is right | open (sketch) | status yes; list no |
| (c)/(d1) top ≅ Mord | **CONFIRMED** | pmc | yes |
| (c)/(d2) bottom ≅ Mord(1) | **CONFIRMED** | pmc | yes |
| (c)/(d3) N = ±id | **CONFIRMED** | pmc | yes |
| (c)/(d4) middle piece, Λ-freeness; Hida pages | **CONFIRMED** (the pages are right; the missing step is stated exactly) | sketch | yes |
| (c) restated (d) still serves downstream | **CONFIRMED** | provisional | yes |

### (a) `lem:s05-R1` — CONFIRMED

**Conrad, Cor. 5.3 (p. 66; Thms. 5.1 and 5.2 on pp. 65–66).**
- The equivariance [x, Ty] = [Tx, y], for [x, y] = (x, w*_ζ y), holds for the *whole* T_1(N). This includes T_p* for p | N, i.e. U_p, which Conrad calls the most subtle case and attributes to the classical theory.
- So at level N' = Mp^s q, Cor. 5.3 does cover U_p (p | N') and U_q, with the full w_{N'}. This gives T^† = w T w^{-1}.
- The literature agent's point holds: Atkin–Li Prop. 1.3 needs q' prime to the W-level. The writer never uses it in that case:
  - U_p and U_ℓ are handled with W_q (p, ℓ prime to q);
  - U_q is handled with W_Q (q prime to Q).

**Atkin–Li p. 223 (PDF text layer).**
- Prop. 1.1: W_Q maps the ε_Q ε_{N/Q} space to the \bar ε_Q ε_{N/Q} space, and W_Q² is a scalar ε_Q(−1)·(value of ε_{N/Q}).
- Prop. 1.2: T_p for p ∤ N.
- Prop. 1.3: U_{q'} for q' | N with (Q, q') = 1, up to the factor ε_Q(q').
- Prop. 1.4: W_Q W_{Q'} = (character value)·W_{QQ'}.
- With ε_q = 1 on S_2(Γ_s), every factor the writer needs is 1, and ε_Q(−1) = 1 in weight 2.
- One caveat: W_Q and W_q commute only up to ε_Q(q). The proof never needs them to commute: it uses W_{N'} h W_{N'}^{-1} = W_Q (W_q h W_q^{-1}) W_Q^{-1} with W_q h = h W_q, and W_{N'}² = 1 makes the order of conjugation irrelevant. OK.

**Other recomputed checks.**
- **W_{N'} normalises Γ_s.** W γ W^{-1} = [[d, −c/N'], [−N'b, a]], and a ≡ 1 mod Q because ad ≡ 1. So the pullback/adjoint-restriction argument of Step 4 holds. The restriction holds because the form is a multiple of a non-degenerate form on the image.
- **The matrix [[0,1],[−N',0]]** is Atkin–Li's W_{N'} with y = 1.
- **Step 2.** I redid the lattice computation:
  - index Q;
  - τ = −(y/Q)ω_1 + w'ω_2, so the point becomes −1/Q;
  - 1 = xω_1 − qzω_2 (from Qxw' − qyz = 1), so the subgroup becomes ⟨1/q⟩.
  - Correct.
- **w² = 1.** This follows from Prop. 1.1 on H^{1,0} and Step 1. OK.
- **U_q on X_q (Step 5).**
  - wU_qw^{-1} = ⟨q⟩^{-1}U_q comes from Prop. 1.3 applied to W_Q (q ∤ Q).
  - U_q^Ros = ⟨q⟩^{-1}U_q on the q-new part, because U_q is unitary there (sign.tex, "Internal consistency": a_q² = χ(q) on the spans of f(dz)).
  - γ is integral, vanishes on Z, and factors through J_s/Z ~ J^old, which has good reduction at q. So X_q(γ) = 0. OK.
  - The restriction to X_q is correct and necessary (see the batch-5 re-read, item 3).
- **Ramification at q.** It is genuinely irrelevant. w_{N'} enters only analytically, on H^1(X^an). The identities are identities in End(J_s ⊗ Q(ζ_Q)) ⊗ Q, which can be checked over C. Only w = w_Q, unramified at q, ever acts on X_q.
- **Minor note (no gap).** The direction of w_{ζ^j} = w_ζ∘⟨j⟩ depends on the pullback composition convention. This is harmless, as the text says.

### (b) `Xlambda`(c)

**The twist change is justified.** Stage 04's def:s04-BN, Translation (ii) (hsieh.tex @47c2984) states that τ^D has components at all primes of N^+ = M. The order matches Hsieh's B_{N,α}: (U_p^{-α}f)(xτ^D) means U_p first, then the translation. Equivariance needs this order: with the other order, U_p^{-s} would have to act on the e^Ros-part, where it is not even defined in general.

**(c1) — CONFIRMED.**
- From W^{-1}X(h)W = X(h^Ros) and W² = 1 one gets X(h^Ros)W = WX(h). This is the form the equivariance computation uses (X_q is contravariant). I re-derived it.
- φ_s e^Ros φ_s^{-1} = e^* follows from (R2), (X1) and (X2).
- At s ≥ 1 we have w_x = 1. The pairing is then the standard one on eZ_p[S_s] × e^*Z_p[S_s]. It is perfect by s04 `lem:s04-ekills`(d) (ordinary.tex), using eZ_p[S]^0 = eZ_p[S] and the same for e^* (deg∘U_p^* = p·deg).
- So the failure of perfectness of u_s caused by Φ_q is absorbed correctly.

**(b)(iii) — CONFIRMED.**
- Translation (o): Hsieh's homological U_p is N_{U_p}.
- Translation (v): eS^D is the e^*-part, and the twist intertwines U_p with U_p^*.
- These are exactly what is cited.

**(c2) — GAP (minor; it concerns only the completeness of the missing-step list).**
- (i) the extension of (X1) to w, (ii) the Γ_1-level obstruction and (iv) tower compatibility are each correct and exact.
- The (ii) obstruction is genuine: the adelic U_1 does not fix the determinant, so τ^D swaps the conditions d ≡ 1 and a ≡ 1. The classical Γ_s *is* normalised, because det = 1 there.
- **Missing from the list:** Hsieh's B_{N,α} carries the norm twist χ_I(Nrd x) (def:s04-BN, Translation (iii); Hsieh Def. 4.3, pp. 32–33). [ , ]_s has no such factor. It has to be produced on the X_q side before the pairings can match, e.g. from the ζ- and diamond-dependence of w, or from the Λ-structure.
- Fix: add an item (v). The status stays *sketch*.

### (c) `Xlambda`(d) — CONFIRMED for (d1)–(d3); (d4) stays a sketch, as stated

**Filtration.** SGA 7 IX Thm. 2.4 gives T_f ⊆ T_t(A^∨)^⊥. Both are saturated of rank 2g − t, so they are equal. Hence:
- T/T_f = X(A^∨) ⊗ Z_p (no twist; Galois-equivariant);
- T_t = Hom(X(A), Z_p(1)).

**Functoriality.**
- α acts on the top piece by X(α^∨), and after λ-transport by X(α^Ros).
- So π_* acts as X(π^*) = β, and h_* acts as X(h).

**(d1).** Top = lim e(X_q ⊗ Z_p) along β. Hecke acts by (X1).
- Frobenius on X(A) is σ_q = U_q^{-1}, which goes to Π_q^{-1}. λ is Q-rational, so the transport does not change this. OK.

**(d2).**
- U_p^Ros acts as g ↦ g∘U_p^*.
- Transitions: g ↦ g∘π^*, via the u-adjoint of β and π^!_w = π^* at s ≥ 1.
- The projection formula gives Ψ_{s'}(a)∘π^* = Ψ_s(π_*a); this uses that π^* preserves the e^*-part.
- Diamonds: ⟨u⟩_* goes to ⟨u⟩^{-1}, i.e. ι-semilinear, consistent with (a).
- Frobenius: f ↦ q f∘X(U_q) goes to qΠ_q^{-1}, using Π_q^* = Π_q^{-1}. OK.

**(d3).**
- N(x) = u_s(x, ·), which equals Ψ_s(φx)∘φ.
- The functional factors through the e^Ros-projection by (R2).
- Frobenius compatibility: Π_q^{-1} on the top piece and on T_t(−1). OK.

**(d4) and Hida.**
- Hi86a Thm. 3.1(ii): V^ord and W^ord are Λ-free of finite rank. This is printed p. 562 = PDF p. 18.
- §8, pp. 595–596 (PDF pp. 51–52):
  - J_r is viewed as Alb, with covariant Hecke action and limits along the covariant maps;
  - e comes from T(p);
  - J^ord_∞ ≅ V^ord;
  - Hida warns that the Pic and Alb actions differ by the Rosati involution. This supports h_* = h^Ros.
- The stated missing step (the degeneracy-compatible identification of the abelian part of the special fibre with J_1(Mp^s)², compatible with π_* and e_*) is exact.

**Downstream.**
- `rem:s05-O7` (simplicial.tex) needs only Hecke-equivariant maps Mord(1) ↪ Tord ↠ Mord. The table needs only "maps both ways".
- Stage 06 does not use Tord.
- So the restated (d) serves its consumers. The Hom_Λ(Mord, Λ)(1) form now depends on (c2), and the text says so.

### Overall
I agree with the writer's statuses: (a) closed (pmc), (b) partly closed, (c) mostly closed. There is one minor GAP: the missing-step list of (c2) lacks the norm twist χ_I(Nrd x). This GAP has been sent to the coordinator.

## S05-M10 (c2 of `prop:s05-Xlambda`; FD1/FD2 markers)

- **(c2): open, not proved.** Statement downgraded from *sketched* to *conjectural / open* (`\provisional` at the statement). The batch-6
  missing-step list moved out of the proof into `rem:s05-c2open`, completed to (i)–(vi): (i) Atkin–Lehner extension of (X1), not given by
  Hyp.X; (ii) integral Brandt-side operator at level U_1 (only on character pieces with φ(N) inverted); (iii) closed by citation (stage 04);
  (iv) tower compatibility on X_q (needs moduli identity + U_p identity as morphisms of Jacobians, then functoriality of X_q); (v) Hsieh's
  norm twist χ_I(Nrd x) — R1 GAP addressed: new `lem:s05-normtwist` (proved) shows the tame factor is exactly what makes x ↦ xτ well
  defined on χ-pieces at level U_1, so (v) reduces to (i)+(ii); the wild factor is Λ-adic; (vi) new: normalisation — unfolding S_s → X_0
  gives the constant φ(N)/2 (proved), not a p-adic unit for s ≥ 2, so "corresponds" must be made precise.
- Downstream flags: `prop:s05-Xlambda`(d) provisional (Hom_Λ-form not claimed), sentence after the proof, `rem:s05-BN` (simplicial.tex),
  the η^B_F row of the "lost" table.
- **FD1** explicit sentence added: Hyp.X data list, (X4), `if:s05-hypX`, Xlambda (d1)/(d2), (L1) of the lost list (hypX.tex); Setting,
  `prop:s05-sign`(a), `rem:s05-Xstatus` (sign.tex). **FD2**: `rem:s05-hsieh` (geometric.tex), two places.
