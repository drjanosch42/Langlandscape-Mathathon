# S06-M6 — second reading of `prop:s06-levM` (the case q ≡ −1 mod p)

- WP: S06-M6 (batch 1, package P4). Reader: abhijit/p4-s06-m6. Independent of the S06 chapter drafts (not read).
- Object checked: `plan/staged/stage-06-integral-defect.tex` at BASE `295db91`: hypothesis (Lev_M) (l. 48–53),
  `thm:s06-KO`, `prop:s06-levM` with its five steps and second-reader note (l. 269–296), `rem:s06-minus1`.
- Sources (file stems in `literature/`; page numbers are those printed in the arXiv versions unless marked "PDF p."):
  - **KO** = `kim-ota_2019_quantitative-variation-of-congruence-ideals-and-integral-periods-of-modular-forms_arxiv` (arXiv v4).
  - **PW** = `pollack-weston_2006_anticyclotomic-mu-invariants-of-modular-forms_arxiv`.
  - **BKM19** = `bockle-khare-manning_2019_wiles-defect-for-hecke-algebras-that-are-not-complete-intersections_arxiv`;
    **BKM21** = `bockle-khare-manning_2021_wiles-defect-of-hecke-algebras-via-local-global-arguments_arxiv`.
  - **Böc07** = `bockle_2007_presentations-of-universal-deformation-rings` (now present in `literature/`, contrary to the
    remark after `cor:s06-fixed`; Cor. 4.3 is on PDF p. 16, Thm 5.8 on PDF p. 26).
- All quotations below are paraphrases.

```
verdict: GAP
```

**Summary.** The strategy of `prop:s06-levM` is sound and does not use q mod p beyond (H0). For **M = 1** every
step checks out against KO, with one unstated (standard) step about `T_p`. **(Lev_M) is CONFIRMED for M = 1.** For
**M > 1**, (Lev_M) *as worded* cannot hold whenever some ℓ ∥ M has ρ̄ unramified at ℓ: KO's ring is the
Σ⁻-**new** quotient, at level `r·N(ρ̄)·Σ⁻`, and not the full `T_k(M)_m`. With Σ⁺ = ∅ it also forces P_ρ̄ = ∅. Step (4)
as written is therefore false for such M. Step (5)'s "hence factors" needs matching on `U_ℓ` (ℓ | M) and `T_p`, and
the text does not supply it. All of these gaps can be repaired with inputs we have (repairs R1–R5 below), except one
point that needs a decision: KO's ℓ-new local condition at ℓ ∈ Σ⁻ with **ℓ ≡ −1 mod p**. There we must read KO's
Hecke algebra as localised at the U_ℓ-sign of f, the way BKM do. The KO text does not do this.

## Notation used here
KO's level for Thm 3.14 is `N⁺_{ρ,Σ⁺}·N⁻`, with `N⁺_{ρ,Σ⁺} = r·∏_{ℓ∈Σ⁺} ℓ^{c(ℓ)+d(ℓ)}·∏_{ℓ∉Σ⁺, ℓ|N(ρ̄)⁺} ℓ^{c(ℓ)}` (KO (2.4),
p. 7). Here `c(ℓ) = ord_ℓ N(ρ̄)`, `d(ℓ) = dim ρ̄^{I_ℓ}`, and r is the auxiliary prime of KO (2.2), p. 3. The Hecke algebra is
the N⁻-new quotient of the algebra at that level, localised at `m_{Σ⁺} = (m_ρ, U_r − α_r, U_ℓ for ℓ ∈ Σ⁺)` (KO p. 4 and
p. 12). The tex takes Σ⁻ = {ℓ ∥ M : ρ̄ unramified at ℓ} and Σ⁺ = ∅. We write `M₀ := ∏_{ℓ∈Σ⁻} ℓ`.

## The four items of the second-reader note

### Item (1) — the level `N⁺_{ρ,Σ⁺}N⁻` equals M: **GAP (repairable; CONFIRMED for M = 1 up to r)**
- KO (2.4) p. 7 and Thm 3.14 p. 12. With Σ⁺ = ∅ the level is `r·N(ρ̄)·M₀`. So the level equals r·M iff
  `M = N(ρ̄)·M₀`, i.e. iff for every ℓ | M **either** ρ̄ is unramified at ℓ and ℓ ∥ M (and then f is ℓ-new, since f is
  a newform of exact level qM, `hyp:s06-H` (H1) "primitive"), **or** `ord_ℓ M = ord_ℓ N(ρ̄)`. Since f is a newform of
  level qM with ρ̄_f = ρ̄, `ord_ℓ M ≥ c(ℓ)` always holds. The condition therefore excludes exactly the following: (a)
  ℓ² | M with ρ̄ unramified at ℓ; (b) ℓ | N(ρ̄) with `ord_ℓ M > c(ℓ)` (non-minimal f at ℓ). KO itself points to this
  rigidity of the level (KO Rem. 2.14(2), p. 7).
- **The auxiliary prime r.** KO's algebra lives at level r·(…), localised at `U_r − α_r` (KO p. 3–4). What we need is a ring
  map `T_k(M)_m → T(r·M)_{m, U_r−α_r}`. It exists: there are no r-new forms at m, by KO's condition
  `tr ρ̄(Frob_r)² ≠ r^{k−2}(1+r)²`, so `T_r ↦ U_r + r^{k−1}U_r^{−1}` works. It is an isomorphism if the two U_r-roots are
  distinct mod λ, and a rank-2 inclusion otherwise. KO handle the analogous point for congruence ideals in Lemma 2.7,
  p. 5. The tex is silent on r. This is a missing sentence, not a mathematical gap.
- **The tex's wording "T_k(M)_m *is* the Hecke algebra of KO Thm 3.14" is false for every M with Σ⁻ ≠ ∅.** KO's algebra is
  the N⁻-new quotient. The full `T_k(M)_m` contains Σ⁻-old forms whenever Σ⁻ ≠ ∅: by level lowering (weight
  preserved for k ≤ p−1, p ∤ N), ρ̄ arises at level N(ρ̄), and BKM19 §5, p. 15 use the same fact. See step (4) for the
  repair. It only needs a map in one direction.

### Item (2) — `P_ρ̄ ⊆ Σ`: **GAP as worded (needs P_ρ̄ = ∅); repairable at no cost**
- KO (2.1), p. 3: P_ρ̄ consists of the primes ℓ | N(ρ̄) with ℓ ≡ −1 mod p, ρ̄|G_ℓ irreducible and ρ̄|I_ℓ reducible.
  Thm 3.14 (p. 12) and Thm 2.9 (p. 5) require P_ρ̄ ⊆ Σ, through Lemma 2.4 (p. 4) and Remark 2.5 (Diamond's type V).
- In the tex Σ = Σ⁺ ∪ Σ⁻ = Σ⁻, which consists of primes **unramified** for ρ̄. P_ρ̄ consists of **ramified** primes. So
  P_ρ̄ ⊆ Σ holds iff P_ρ̄ = ∅. (H0) does not give this, because it excludes only ℓ ≡ +1.
- **Repair R2:** take Σ⁺ := P_ρ̄ instead of ∅. For ℓ ∈ P_ρ̄ one has d(ℓ) = 0: ρ̄|I_ℓ is a sum of two characters that
  Frobenius swaps, both ramified. So by (2.4) the level is unchanged. The local condition at ℓ becomes "unrestricted"
  (KO Def. 3.9(3), p. 11), and ρ_f mod ϖ^t trivially satisfies it. U_ℓ ∈ m_{Σ⁺} is consistent, because every form in
  the m-part is supercuspidal at ℓ, so a_ℓ = 0.
- M = 1: N(ρ̄) = 1, so P_ρ̄ = ∅ and Σ = ∅. **CONFIRMED.**

### Item (3) — `U_ℓ` for ℓ | M versus KO's anemic algebra: **GAP (unstated step; repairable, with one caveat at ℓ ≡ −1)**
- KO's T is generated by the S-anemic `T_S` (T_ℓ, S_ℓ for ℓ ∉ S, with S ⊇ Σ ∪ {ℓ | N(ρ̄)} ∪ {r}; KO p. 4 and the
  paragraph after Thm 3.14, p. 12). KO assert that it equals the full algebra at their level, citing Dim09 Lemma 5.4(iii)
  and EPW06 Prop. 2.4.2 (not in `literature/`; not checked). The factorisation in step (5) needs
  `ψ(x) = λ_f(x) mod ϖ^t` for **every** generator x of `T_k(N)_m`: T_ℓ (ℓ ∤ Np), U_ℓ (ℓ | M), U_q **and T_p**. The
  last one is present because the fixed-weight algebra is the p-destabilised `T^ord_k(Np)_m`, cf. step (3) of the
  proof of `thm:s06-defect`. The tex matches only "the T_ℓ".
- **Repair R3** (all Galois-theoretic, via a Galois representation `ρ_T` over the reduced Σ⁻-new quotient; Carayol):
  - T_ℓ for ℓ ∈ S, ℓ ∤ Mp (including r and q): Chebotarev plus continuity, as in `prop:s06-galois`.
  - ℓ ∈ Σ⁻: on the Σ⁻-new quotient (all newforms of exact level M; reduced), U_ℓ is the constant `ε_ℓ ℓ^{(k−2)/2}` of the
    Steinberg sign of the component. It therefore maps to `a_ℓ(f)`, provided the localisation fixes the sign
    (caveat below).
  - ℓ | N(ρ̄), ℓ ∉ P_ρ̄: minimal type, so ρ^{I_ℓ} has constant rank. Then U_ℓ = trace of Frob_ℓ on ρ_T^{I_ℓ}, and it
    specialises to a_ℓ(f).
  - ℓ ∈ P_ρ̄: U_ℓ = 0 on both sides.
  - T_p: f is ordinary (a point of a Hida family) and ρ̄ is p-distinguished (H2). So U_p = Frob on the unramified
    quotient of ρ_T|G_p, and `T_p = U_p + p^{k−1}U_p^{−1}`. (Standard, Wiles 1988 §2. The PDF in `literature/` is
    image-only, so no page was checked.)
- **Caveat (ℓ ∈ Σ⁻, ℓ ≡ −1 mod p).** KO's ℓ-new condition (Def. 3.7, p. 10–11; Tay03 E3) fixes a normal form
  (sub-line χ^{1−k/2}) "up to twist". When ρ̄ is unramified at ℓ ≡ −1, both Steinberg signs ±ℓ^{(k−2)/2} reduce to the
  same ρ̄|G_ℓ. The fixed-form local ring then sees **one** sign. An anemic localisation at m_ρ sees **both** (U_ℓ ≡ ±c
  are distinct mod p, but U_ℓ is not in the anemic generators). KO's proof of Thm 3.14 (p. 13) writes the trace as
  `± ℓ^{(k−2)/2}(ℓ+1)` and does not address this. BKM do: they fix β_q with f (BKM19 §4, p. 11, and §5, p. 14–15). They
  note that without fixing it the Steinberg locus has two components (BKM21 §4.2, p. 24), and they localise the
  **full** Hecke algebra at the maximal ideal of f. **Repair R4:** read KO's algebra as the full Σ⁻-new algebra
  localised at m_f (U_ℓ − a_ℓ(f) ∈ m), with the ℓ-new condition of f's sign. KO's minimal-prime argument (p. 13–14)
  goes through verbatim for this reading, but it is our reading, not KO's text. Alternatively, add "ℓ ≢ −1 mod p for
  ℓ ∈ Σ⁻" to (Lev_M). Note the irony: the same −1 phenomenon reappears at the primes of M.
- M = 1: only T_p needs the ordinary argument. **CONFIRMED with R3 (T_p).**

### Item (4) — Hensel distinctness mod ϖ: **CONFIRMED**
- f is Steinberg at q up to an unramified quadratic twist, so `a_q(f) = ε q^{(k−2)/2}` and the Frob_q eigenvalues are
  `ε q^{(k−2)/2}, ε q^{k/2}`. Their difference is `ε q^{(k−2)/2}(1 − q)`, a unit iff q ≢ 1 mod p, which is (H0).
- At q ≡ −1 the roots are ≡ ±ε q^{(k−2)/2}, still distinct because p is odd. This differs from the ℓ ≡ −1 caveat in
  item (3) because here **both** U_q-roots live on the q-old space and m picks one.
- No Hensel is needed over O/ϖ^t: if x is a root of `(X−a)(X−b)` with x ≡ a mod ϖ and a − b a unit, then x − b is a
  unit, so x = a.

## The five steps of the proof

| step | verdict | basis |
|---|---|---|
| (0) ramified case t = 0 | CONFIRMED | KO Def. 2.12 and the note after it, p. 6 (t_f(q) = 0 if q \| N(ρ̄)); PW Def. 3.3, p. 9 |
| (1) ord cc_q(f) = max t′ with λ_f mod ϖ^{t′} through T″_k | CONFIRMED | definition `def:s06-ctam`. Read cc_q(f) as the O-ideal generated by λ_f(b_k); only "⊆" is used |
| (2) T″_k ≅ T_k(M)_m, roots distinct | CONFIRMED | `lem:s06-decomp`(b) at weight k; item (4) above |
| (3) ρ_f mod ϖ^t is a point of the KO ring | CONFIRMED under the level condition of item (1) and R2 | see below |
| (4) KO Thm 3.14 gives T_k(M)_m → O/ϖ^t | **GAP as written**; CONFIRMED for M = 1; repairable (R1, R2, R4) | see below |
| (5) U_q ↦ a_q(f), hence factorisation | **GAP (unstated matching)**; CONFIRMED after R3 | item (3), item (4) |

**Step (3)** (KO Def. 3.3, 3.5, 3.7, 3.9, pp. 10–11):
- At p: FL weights 0, k−1 ≤ p−2 and p ∤ N. FL-type is stable under quotients, so ρ_f mod ϖ^t is low-weight crystalline.
- At q: ρ̄ is unramified and q ∉ Σ, so "minimal" means unramified (Def. 3.5(1)), and ρ_f mod ϖ^t is unramified by the
  definition of t (KO Def. 2.12, p. 6).
- At ℓ ∈ Σ⁻: f is ℓ-Steinberg. KO's Assumption 3.6 (p. 10; ℓ ≢ 1 or p | #ρ̄(G_ℓ)) holds by (H0). Mind the sign
  caveat of item (3).
- At ℓ | N(ρ̄), ℓ ∉ P_ρ̄: equal conductor gives minimal ramification (via KO Lemma 2.4 / Rem. 2.5, p. 4). Minimality
  passes to reductions.
- At ℓ ∈ P_ρ̄: unrestricted (R2).
- det = χ^{1−k} because the character is trivial.
- The tex's "minimal elsewhere" also silently needs condition (b) of item (1).

**Step (4)** as written ("identifies that ring with T_k(M)_m") is false for Σ⁻ ≠ ∅. **Repair R1:** KO Thm 3.14
gives `R^{Σ⁻}_{Σ⁺} ≅ T(r·N(ρ̄)·M₀)^{M₀-new}_{m}`. Compose
`T_k(M)_m ↠ T_k(M)^{M₀-new}_m → T(r·M)^{M₀-new}_{m,U_r−α_r} ≅ R^{Σ⁻}_{Σ⁺} → O/ϖ^t`, using the r-map of item (1), the
level condition `M = N(ρ̄)·M₀`, R2 and R4. Only this one-way map is needed, and the conclusion of step (4) survives.
q does not enter, so KO Prop. 2.15(1) (p. 8), the only place in KO that needs q ≢ ±1, plays no role. This
**confirms the tex's central claim**: the q ≡ −1 obstruction belongs to KO's method, not to the statement.

## `rem:s06-minus1` and `thm:s06-KO`
- (a) **CONFIRMED.** KO Thm 1.1(6), p. 1, and PW (CR)(2), p. 2, both exclude ℓ ≡ ±1 with ρ̄ unramified at ℓ | N⁻. PW
  Thm 6.8, p. 21. KO's statement in `thm:s06-KO` matches KO Thm 1.1 (p. 1) item for item.
- (b) **CONFIRMED.** KO Prop. 2.15(1), p. 8, is the only ±1 hypothesis. KO Thm 2.13, p. 7, needs only q ≢ 1 for q | N⁻.
  The Euler-factor mechanism is KO §5, Prop. 5.6, p. 19 (via DFG Prop. 1.4(c)). KO Rem. 5.5, p. 19 concerns only
  the quaternionic side. The explicit factor 1 − q^{−2} is the tex's computation; KO do not print it.
- (c), (d) **CONFIRMED in substance**, subject to the repairs above for M > 1.

## Which M > 1 satisfy (Lev_M)
KO Thm 3.14 has no hypothesis beyond Assumption 2.1 (= (H2) plus the existence of f) and P_ρ̄ ⊆ Σ. Hence:
- **(Lev_M) literally as worded** (Σ⁺ = ∅, the *full* T_k(M)_m equal to KO's algebra) holds, up to r, **only for
  M = N(ρ̄) with P_ρ̄ = ∅**, i.e. f minimal at every ℓ | M and no ℓ | N(ρ̄) of type P_ρ̄ (in particular for M = 1).
- **Corrected (Lev′_M)** (R1 + R2 + R4) holds for **every M with `M = N(ρ̄)·M₀`, M₀ squarefree and prime to N(ρ̄)**.
  Equivalently: f is minimally ramified at every prime of M where ρ̄ ramifies, and M is squarefree at the primes where
  ρ̄ is unramified. If some ℓ | M₀ has ℓ ≡ −1 mod p, this needs the sign-localised reading of R4.
- KO does **not** cover M with ℓ² | M where ρ̄ is unramified at ℓ, or with f non-minimal at a ramified ℓ (KO Rem. 2.14(2)).
  Those remain open (`rem:s06-open`(i)).

## Proposed corrections for the stage tex (to be made by its owner, not here)
- R1: In (Lev_M) and step (4), replace "T_k(M)_m is the Hecke algebra of [KO, Thm 3.14]" by "M = N(ρ̄)·M₀ with M₀
  squarefree (Σ⁻ = primes of M₀); then T_k(M)_m surjects, through the r-stabilisation, onto the algebra of
  [KO, Thm 3.14]".
- R2: Σ⁺ := P_ρ̄ (level unchanged since d(ℓ) = 0), or assume P_ρ̄ = ∅.
- R3: In step (5), add the matching on U_ℓ (ℓ | M) and T_p, and extend T_ℓ to ℓ ∈ S by Chebotarev.
- R4: For ℓ ∈ Σ⁻ with ℓ ≡ −1 mod p, use the sign-fixed Steinberg condition and the full algebra localised at m_f
  (BKM19 §4–5), or exclude such ℓ.
- R5 (cosmetic): Böc07 is now in `literature/`. Update the note after `cor:s06-fixed`.
- Status suggestion: `prop:s06-levM` stays `\stpmc`. For M = 1 it can be upgraded after R3 is written out. For M > 1 it
  should be stated under (Lev′_M).
