<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S06-M5 second reader (F2, cross-account)

- Package: batch 7 F2. Reader: abhijit/f2-s06-m5-r2 (fresh agent, Opus).
- **Part A** checks `origin/impl/s06-m5` @ `cc27d6e7ea9776e376468f45061c3a0dd8818d5c`, `mathematics/chapters/s06/s06-m5.tex`
  (`prop:s06-levM` for M = 1, `rem:s06-minus1` (a)–(e), `rem:s06-levM-items`, `rem:s06-levM-status`).
- **Part B** checks the follow-up commit `dccbe50` (R1–R5, M > 1); see the end of this note.
- Independence: before the trigger this reader read only KO §2–§5, PW, BKM19/21 and the stage tex (l. 1–135, 236–330) and wrote
  its own step list. It then read the P4 litnote (`s06-m6-levM.md` on `abhijit/s06-m6`). The pre-trigger notes reached the
  same four issues as P4 independently: (i) KO's algebra is the Σ⁻-new quotient; (ii) Σ⁺ = ∅ forces P_ρ̄ = ∅; (iii) U_ℓ/T_p
  versus the anemic algebra; (iv) two Steinberg signs at ℓ ≡ −1 mod p.
- Sources: KO = `kim-ota_2019_*_arxiv` (arXiv v4, printed page); PW = `pollack-weston_2006_*_arxiv`;
  BKM19 = `bockle-khare-manning_2019_*_arxiv`; BKM21 = `bockle-khare-manning_2021_*_arxiv`. All quotations are paraphrases.

## Part A — verdict on cc27d6e (M = 1)

```
verdict (Part A): CONFIRMED for M = 1, except one GAP that the text already marks: the T_p matching in step (5).
That gap is fillable (argument A5 below). No new crit/maj finding.
```

| item | verdict | basis (KO/PW page) | note |
|---|---|---|---|
| step (0): ramified gives t = 0 | CONFIRMED | KO Def. 2.12 and the note after it, p. 6 | |
| step (1): reduction to a factorisation | CONFIRMED | `def:s06-ctam`; elementary | only "⊆" is used; correct |
| step (2): T''_k ≅ T_k(1)_m, roots distinct | CONFIRMED | `lem:s06-decomp`(b) (itself `\sttoprove`) | the root difference ε c (q−1) is a unit by (H0); at q ≡ −1 the roots are ±εc |
| step (3): ρ_t is a point of R_∅ | CONFIRMED | KO Def. 2.12 p. 6; footnote 1 p. 3; Def. 3.3 p. 10; §3.2.1 p. 9; §2.1.1 p. 3; Def. 3.5(1) p. 10 | N(ρ̄) = 1: f has level q and ρ̄ is unramified at q |
| step (4): R_∅ ≅ T(r)_{m_∅}, map ι_r | CONFIRMED | KO Thm 2.9 p. 5, Lemma 2.4 p. 4, (2.1)/(2.2) p. 3, Thm 3.14 p. 12 | see A4 |
| step (5): matching T_ℓ (ℓ ∉ S), T_q, T_r, U_q | CONFIRMED | trace identity; Steinberg trace (1+q)εc | see A4 for T_r |
| step (5): matching T_p | **GAP (already `\provisional`)** | — | fillable: A5 |
| generators of T_k(q)_m | CONFIRMED | T_ℓ (ℓ ≠ q, including T_p) and U_q | |
| `rem:s06-minus1`(a) | CONFIRMED | KO Thm 1.1(6) p. 1; PW (CR)(2) p. 2; PW Thm 6.8 p. 21 | |
| `rem:s06-minus1`(b) | CONFIRMED (minor wording point) | KO Prop. 2.15(1) p. 8; Thm 2.13 p. 7 (last bullet: only q ≢ 1); Prop. 5.6 p. 19; Rem. 5.5 p. 19 | KO do print the special-case Euler factor L_ℓ(ad⁰f,s) = (1−ℓ^{−1−s})^{−1} (§5.1, p. 18). At s = 1 this gives 1−q^{−2}. Suggest "[KO, §5.1, p. 18] at s = 1" in place of "KO do not print this factor" |
| `rem:s06-minus1`(c) | CONFIRMED | — | q+1 ∈ m at q ≡ −1 |
| `rem:s06-minus1`(d) | CONFIRMED for M = 1 (Thm E / Gor inputs not re-checked) | — | "(Gor_{R'}) needs only (CR,{q})" relies on Hsieh, which is outside this reader's sources |
| `rem:s06-minus1`(e) | CONFIRMED | — | both roots lie on the q-old space; m picks one |
| `rem:s06-levM-items` (1)–(4) | CONFIRMED; (3) `\stpmc` is correct | KO (2.4) p. 7, (2.1) p. 3, Lemma 2.7 p. 5 | |
| `rem:s06-levM-status` | CONFIRMED | — | its list of remaining cited inputs is complete. Add Fontaine/Edixhoven (all forms in m ordinary) if A5 is adopted |

### A4 — checks on step (4) and the T_r matching
- KO Thm 3.14 with Σ = ∅ (so N⁻ = 1) reduces to Thm 2.9 plus Lemma 2.4; P_ρ̄ ⊆ ∅ holds since P_ρ̄ consists of primes of N(ρ̄) = 1.
- ι_r is well defined. The m_∅-part of KO's module at level r (Γ₁(r), trivial diamonds, i.e. Γ₀(r)) carries only r-old
  eigensystems: r-new ones are excluded by the choice of r in KO (2.2). Hence every polynomial relation among T_ℓ (ℓ ≠ r) and
  T_p that holds on the level-1 m-part also holds there, and U_r + r^{k−1}U_r^{−1} acts on each r-stabilisation g_α by a_r(g).
- T_r: π_∅(tr ρ^univ(Frob_r)) and U_r + r^{k−1}U_r^{−1} agree on every eigensystem of the reduced algebra T(r)_{m_∅}
  (reduced by KO Thm 2.9/3.14). They are therefore equal, so ψ(T_r) = tr ρ_t(Frob_r) = a_r(f) mod ϖ^t. The text's
  "Chebotarev" is not needed, but it is harmless.
- T_q: KO's convention is geometric Frobenius with det = χ^{1−k}. The Steinberg eigenvalues are a_q and q·a_q, with product
  q^{k−1}, which is consistent. The trace ε(1+q)c mod ϖ^t does not depend on the ramified corner.
- q ∉ S = {p, r}: allowed, since KO need S ⊇ Σ ∪ {ℓ | N(ρ̄)} ∪ {r} (and p) only (KO p. 4).

### A5 — a fill for the T_p gap (this reader's argument; standard, not taken from KO)
1. Every eigenform g in the m-part at weight 2 ≤ k ≤ p−1, p ∤ level, is ordinary. If g were non-ordinary, ρ̄_g|I_p would be
   given by the level-2 fundamental characters ω₂^{k−1}, ω₂^{p(k−1)} (Fontaine; Edixhoven), contradicting the reducible,
   ordinary ρ̄|G_p of f. (Not in `literature/`; cited, unchecked.)
2. Since 1 ≤ k−1 ≤ p−2, ω^{k−1} ≠ 1 on I_p. Pick σ ∈ I_p with ω^{k−1}(σ) ≠ 1. Then ρ_T(σ) has distinct residual eigenvalues,
   ω^{k−1}(σ) and 1. Hensel gives a free rank-one eigenline L_T for the first eigenvalue (ρ_T is the Carayol representation
   over the reduced T ⊂ ∏ O_g).
3. In each ρ_g, the eigenline for the first eigenvalue is the ordinary sub-line. Since T injects into ∏ O_g, L_T is
   G_p-stable and ρ_T/L_T is unramified. Its Frobenius value u ∈ T^× maps to the unit root α_p(g) for every g, so
   T_p = u + p^{k−1}u^{−1}.
4. The construction in 2–3 is functorial in the coefficients. Applied to ρ_t = ρ_T ⊗_ψ O/ϖ^t ≅ ρ_f mod ϖ^t, it gives
   ψ(u) = α_p(f) mod ϖ^t, hence ψ(T_p) = a_p(f) mod ϖ^t.
5. The P4 R3 sketch ("U_p = Frob on the unramified quotient") is correct. Point 2 supplies the step that makes the quotient
   exist over T and not only over each O_g.

### Minor (no action needed for the verdict)
- m1: In step (5), "via ... Chebotarev" for T_r can be replaced by the reducedness argument of A4.
- m2: `rem:s06-minus1`(b): KO do print the Euler factor (§5.1, p. 18); see the table.
- m3: Step (2) and the T''_k identification rest on `lem:s06-decomp`(b), which is still `\sttoprove`. This is not this WP's
  burden, but `rem:s06-levM-status` could list it.

## Part B — R1–R5 and M > 1 (commit dccbe50e706dbf6f09b63c3ff47026ba0bc20e1c)

Object: `origin/impl/s06-m5` @ `dccbe50` (parent `cc27d6e`), `mathematics/chapters/s06/s06-m5.tex`. It contains
`hyp:s06-levMp` (Lev′_M), `prop:s06-levM` for all M, `lem:s06-levM-hecke`, `rem:s06-levM-sign`, `rem:s06-minus1`,
`rem:s06-levM-items`, `rem:s06-levM-which` and `rem:s06-levM-status`. Extra source used: DFG = `diamond-flach-guo_2004_*`.

```
verdict (Part B, M > 1): GAP.
CONFIRMED for the family F1: M squarefree, ρ̄ unramified at every ℓ | M (so N(ρ̄) = 1), and ℓ ≢ −1 mod p for every ℓ | M.
  This holds modulo the cited KO Thm 3.14, [W88], L-G, and Fontaine/Edixhoven (see B3).
F1 with some ℓ ≡ −1 mod p: CONFIRMED as a reading (R4 is sound, but it is our reading, not KO's text).
N(ρ̄) > 1: GAP. Lemma (c)(iii)(β)/(γ) ("every g ∈ 𝒩 is minimal") and the use of KO Thm 3.14 in step (4) fail
  when ρ̄ is not twist-minimal at some ℓ | N(ρ̄). Explicit counterexample in B2.
  When ρ̄ is twist-minimal, the claim is plausible but this reader could not check it against a source.
```

### B1 — verdict per step

| item | verdict | basis | note |
|---|---|---|---|
| consequence: M = N(ρ̄)·M₀ | CONFIRMED | L-G; the Swan conductor is unchanged by reduction; KO (2.1) p. 3 | the P_ρ̄ case argument (an invariant line would be G_ℓ-stable) is correct |
| correction of M6: equal conductor does not imply KO-minimality | **CONFIRMED** (the example is valid); one side remark is an ERROR (minor) | KO Def. 3.5(1) p. 10 | μ⊗sp with μ ramified (quadratic on I_ℓ) has conductor exponent 2, with ρ_f(I_ℓ) infinite and #ρ̄(I_ℓ) = 2. But "KO Rem. 2.2 does not exclude this" is wrong: f⊗χ_ℓ (χ_ℓ quadratic of conductor ℓ, still trivial character) has conductor exponent 1 at ℓ, so f is **not** minimal among its twists. KO Rem. 2.2 p. 3 / DFG §1.7.1 normalise exactly this away. The P4 statement was wrong only outside the twist-minimal setting |
| steps (0)–(2) | CONFIRMED | as Part A | |
| step (3): ρ_t is a point of R^{Σ⁻}_{Σ⁺} | CONFIRMED under (L1), (L2) | KO Def. 3.3/3.5/3.7/3.9 pp. 10–11; Assumption 3.6 holds by (H0) | minimality passes to O/ϖ^t because ρ_t(I_ℓ) lies between ρ_f(I_ℓ) and ρ̄(I_ℓ) |
| step (4): π: R^{Σ⁻}_{Σ⁺} ≅ A (KO Thm 3.14 p. 12) | **GAP** for N(ρ̄) > 1; CONFIRMED for F1 | KO Thm 3.14 p. 12, Lemma 2.4 p. 4, Rem. 2.2 p. 3; DFG §3.1 p. 715 | DFG's axiomatic R = T (§3.1) imposes "ρ₀ has minimal conductor among its twists" as a standing condition. KO's level-defined algebras inherit this through Rem. 2.2 / Lemma 2.4. Counterexample: B2 |
| (L1)/(L2) as the full hypothesis | **GAP**: they are not sufficient | — | proposed (L3): no ℓ | N(ρ̄) such that ρ̄⊗(quadratic character ramified at ℓ) has smaller conductor at ℓ |
| lemma (a) | CONFIRMED | — | |
| lemma (b): A = 𝒪[a_ℓ(g)] over 𝒩 | GAP (minor + major) | — | minor: forms in m_{Σ⁺} with a non-ordinary T_p residue must be excluded. This needs Fontaine/Edixhoven: a non-ordinary g′ of weight ≤ p−1 has ρ̄_{g′}\|I_p of level-2 type, which is not ρ̄\|I_p. Major: the "U_ℓ residues determined by ρ̄" step for ℓ | N(ρ̄) presupposes that every form is minimal (same GAP as (iii)(β)/(γ)) |
| lemma (c)(i) | CONFIRMED | L-G | covers r and q |
| lemma (c)(ii): T_p = u + p^{k−1}u^{−1} | CONFIRMED | [W88] (cited) | the projector computation tr(ρ(Φ)e) = δ(Φ) was checked in both cases (δ as sub or as quotient). It works for any σ₀ ∈ G_{Q_p} with distinct residual characters, so it is cleaner than A5. The roots in O/ϖ^t are unique as for α_q |
| lemma (c)(iii)(α), ℓ ∈ Σ⁻ | CONFIRMED | — | the full localisation at m fixes the sign, even at ℓ ≡ −1 |
| lemma (c)(iii)(β),(γ) | **ERROR as stated** when ρ̄ is not twist-minimal at ℓ; unverified otherwise | B2 | "the kernel is pro-p, hence unipotent" does not give a finite image: a non-zero monodromy N is exactly what can survive |
| lemma (c)(iii)(δ), ℓ ∈ P_ρ̄ | CONFIRMED | — | |
| step (5): matching | CONFIRMED given the lemma | — | T_r via (c)(i); T_p via (c)(ii); U_q as in Part A |
| `rem:s06-levM-sign` (R4) | CONFIRMED as a reading (`\stpmc`; not KO's text) | KO §3.2.5 p. 11, proof of Thm 3.14 pp. 13–14; BKM19 §4 pp. 10–11 (St(β_q)), Lemma 6.2 proof pp. 17–18 (both U_q-signs occur by level raising) | points (i)–(v) were checked: either normal form satisfies Lemma 3.8 / Cor. 3.13, and the minimal-prime argument is unchanged |
| `rem:s06-minus1` (a)–(e) | CONFIRMED (as Part A); m2 still open | — | (d) restated for (Lev′_M): inherits the GAP for N(ρ̄) > 1 |
| `rem:s06-levM-items` (1),(2),(4) | CONFIRMED | KO (2.4) p. 7 | |
| `rem:s06-levM-items` (3) | GAP (as lemma (c)(iii)) | — | |
| `rem:s06-levM-which` (i) | **GAP**: the example "M = N(ρ̄) with f minimal" is not covered when ρ̄ is not twist-minimal (B2); the F1 example is CONFIRMED | — | |
| `rem:s06-levM-which` (ii), (iii) | CONFIRMED | KO Rem. 2.14(2) p. 7 | |
| `rem:s06-levM-status` | CONFIRMED as a list, but incomplete | — | it should add twist-minimality (L3), and a source for "level-c(ℓ) forms with this ρ̄ are KO-minimal" |

### B2 — counterexample to lemma (c)(iii)(γ) and to the step-(4) isomorphism (explicit)
- p = 13, k = 12, f₀ = Δ. ρ̄_Δ mod 13 has full image (13 is not an exceptional prime), and Δ is ordinary at 13 (τ(13) ≡ 8 mod 13).
  ℓ = 43 ≢ ±1 mod 13. Computed: τ(43) ≡ 11 ≡ +43⁵·44 mod 13, so the level-raising condition holds with sign +.
- ρ̄ := ρ̄_Δ ⊗ χ̄₄₃ (χ₄₃ = Legendre symbol mod 43). Then ρ̄|_{G_43} = μ̄χ̄_cyc ⊕ μ̄ with μ̄ ramified, so N(ρ̄) = 43²,
  P_ρ̄ = ∅, (H2) holds, and ρ̄ is p-distinguished. Take M = 43².
- f := Δ⊗χ₄₃, a newform of level 43² that is principal series at 43 with ρ_f(I₄₃) of order 2 = #ρ̄(I₄₃). So (L2) holds and
  (L1) is vacuous.
- g := h⊗χ₄₃, where h is the weight-12 newform of level 43 that is Steinberg at 43 (sign +) and ≡ Δ mod 𝔭 | 13. h exists by
  level raising: Ribet for k = 2, Diamond for k ≥ 2; DT94 `diamond-taylor_1994_*` is in `literature/`, not page-checked.
  g has level 43², ρ̄_g ≅ ρ̄, a₄₃(g) = 0 = a₄₃(f), and a_p congruent by ordinarity. So g ∈ 𝒩. But ρ_g(I₄₃) is infinite, so g is
  not KO-minimal.
- Consequence. KO's minimal ring R_∅ (here Σ = ∅) has no point at g. Yet A = T(r·43²)_m (anemic) has g as an eigensystem, so
  π: R_∅ ≅ A is false. KO Thm 2.9 + Lemma 2.4 do not apply to this non-twist-minimal ρ̄, in line with DFG §3.1 p. 715.
  Lemma (c)(iii)(γ) is false here, and step (4) has no citable input.
- This refutes the proof, not the inclusion cc_q(f) ⊆ (ϖ^t) itself: for such M the inclusion is **open**.
- Repair options: (a) add (L3) twist-minimality. Then case (ii) of reducible ρ̄|G_ℓ is fine: a ramified twist of Steinberg
  forces μ|I_ℓ to be quadratic (trivial character), and that is exactly what (L3) excludes; principal-series p-parts would need
  p | ℓ−1, excluded by (H0). The supercuspidal case (ℓ ∉ P_ρ̄, including ℓ = 2) still needs a source (Diamond's types; DDT §4).
  (b) Alternatively, replace A by its image on the KO-minimal newforms and check that KO's proof of Thm 3.14 runs with the
  newform-defined algebra of KO §2.1.1. Not checked here.

### B3 — R1–R5
- **R1** (KO's algebra is the M₀-new quotient; a one-way map T_k(M)_m ↠ B = A): correctly applied. `rem:levM-items`(1) and
  `levM-which`(ii) are right.
- **R2** (Σ⁺ := P_ρ̄; level unchanged since d(ℓ) = 0): correctly applied. The derivation of M = N(ρ̄)M₀ is correct.
- **R3** (matching on all generators): correct for T_ℓ (including r and q), T_p (an improvement over A5) and U_ℓ with ℓ ∈ Σ⁻ ∪ P_ρ̄.
  Incorrect at ℓ | N(ρ̄), ℓ ∉ P_ρ̄, when ρ̄ is not twist-minimal (B2). Lemma (b) also needs Fontaine/Edixhoven for ordinarity.
- **R4** (sign-fixed reading at ℓ ≡ −1): correctly applied and sound as a reading. Status `\stpmc`, "ours, not KO's", is the
  right label.
- **R5** (Böc07 present): correctly applied. `bockle_2007_presentations-of-universal-deformation-rings.pdf` is in `literature/`;
  pages not re-checked.

### B4 — recommendation for the provisional marks
- Lift the M > 1 `\provisional` **only** for F1 (N(ρ̄) = 1, M squarefree, every ℓ | M with ℓ ≢ −1 mod p). Add the
  Fontaine/Edixhoven citation in lemma (b).
- F1 with ℓ ≡ −1: keep it `\stpmc` under R4, as the text does.
- N(ρ̄) > 1: keep `\provisional`, or state the case under an added (L3) plus a cited "forms of exponent c(ℓ) are minimal".
- Alternatively, revert to M = 1 plus F1.

### B5 — correction (after Fabian's follow-up 20261115-012526Z; checked against 735c5ef2 / 471cc35e)
- In B2 the prime is ℓ = 43 and ρ̄|I₄₃ = μ̄ ⊕ μ̄ with μ̄ ramified, so d(43) = 0.
- In the restructured lemma, (c)(iii) is split by d(ℓ), so B2 is case (δ). (δ) holds without any minimality: if V_g^{I_ℓ} ≠ 0,
  a saturated invariant line would reduce to a non-zero vector in ρ̄^{I_ℓ}. Hence d(ℓ) = 0 gives V_g^{I_ℓ} = 0 and a_ℓ(g) = 0
  for every g ∈ 𝒩 and for f, so U_ℓ = 0 in B.
- This corrects B1/B3/B4: B2 refutes **only** π: R ≅ A in step (4) (the KO input needs a twist-minimal ρ̄). It does **not**
  refute the U_ℓ step or (c)(iii) as now written.
- My "ERROR" for (γ) referred to the dccbe50 wording, where (γ) also covered d(ℓ) = 0. There, "ρ_g(I_ℓ) → H is an
  isomorphism for every g" was false for g = h⊗χ₄₃, but the U_ℓ value it was used for (0) is still correct.
- The F1 restriction and the GAP verdict for N(ρ̄) > 1 (through step (4)) are unchanged. The new (γ) (d(ℓ) = 1) was not
  re-audited here.
