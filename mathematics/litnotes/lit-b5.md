<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# lit-b5: literature for stages 5-6 (work batch 5, package D4)

Node: Abhijit. BASE `0e24ba5`. Retrieval date 2026-11-14 (Caltech network). All paraphrases are our own; status of every
citation is *cited*. PDFs live in `literature/` (git-ignored, never committed). "p." = printed page, "[PDF n]" = page of the file.

## 0. Summary table

| # | item | status | file / source |
|---|---|---|---|
| 1 | wanted reference: Picard U_p on J_1(Mp^s) ∩ Γ_0(q) commutes with pullbacks along X_{s'} → X_s | **no explicit statement found**; partial anchors in 1.1-1.2 | Conrad (in Ribet-Stein), Ohta 1999 |
| 2a | Buzzard 1997 (Duke 87) | author preprint only (already present); Duke version manual | Project Euclid gives a bot challenge |
| 2b | Takahashi 2001 (JNT 90) | pending manual download | not in `literature/` |
| 2c | Bushnell-Henniart | skipped (not free) | |
| 3a | DDT97 Lemma 4.17, §4.4 | **verified in preprint**; published pagination not obtainable | 1.3 below |
| 3b | Hida 1988 Ann. Math. 128 | **already present, text layer (JSTOR), all four pages verified** | 3.2 |
| 4 | Gelbart 1975, Eichler 1973, Kneser 1966, Takahashi 2001, Kurihara 1979 | none present in `literature/`: pending manual download | |

New PDF saved this batch: `darmon-diamond-taylor_1997_fermats-last-theorem_preprint2007.pdf` (McGill, version dated 2007-09-09; same
numbering as the 2000 version for Lemma 4.17 and §4.4; transfer optional).

## 1. Item 1: the wanted reference

Target statement (B1 report): for s' >= s, the Picard U_p on J_1(Mp^s) ∩ Γ_0(q) (μ_N-model) commutes with the Picard pullbacks along
X_{s'} → X_s, and the Picard U_p is the adjoint (θ^Ros) of the usual U_p on forms. **No source examined states the commutation with the
level-changing pullbacks explicitly for the Jacobian.** What exists:

### 1.1 Conrad, "The Shimura construction in weight 2" (appendix to Ribet-Stein)
File `ribet-stein_2001_lectures-on-serres-conjectures_preprint.pdf` (present; Conrad's appendix is §5 of that file; page numbers of the
appendix as printed in the file, PDF = printed + 4).
- **Thm 5.1, p. 65 [PDF 69]**, with the set-up on pp. 64-65 [PDF 68-69]: the Shimura isomorphism at level Γ_1(N) identifies the usual
  ⟨n⟩ and T_p on weight-2 forms with the cohomological ⟨n⟩^*, T_p^* = (π_1)_* ∘ (π_2)^* on H^1(X_1(N), Z), **for every prime p including p | N**: for
  p | N he uses Γ_1(N,p) = Γ_1(N) ∩ Γ_0(p)^t (triples (E,P,C), C of order p meeting ⟨P⟩ trivially). So the cohomological U_p of the
  μ_N-type moduli problem is the usual U_p on forms. Proof omitted by Conrad.
- **Lemma 5.4, p. 67 [PDF 71]**: pullback on H^1(−,Z) corresponds to Pic^0(f), trace to Alb(f); dual under the canonical autoduality.
- **Def 5.5, p. 68 [PDF 72]**: Picard-side T_p^* = Alb(π_1) ∘ Pic^0(π_2), ⟨n⟩^* = Pic^0(I_n). **Def 5.6, p. 68**: (T_p)_* = Alb(π_2) ∘ Pic^0(π_1);
  the (-)_*-action induces the classical action on S_2, the (-)^*-action is the Petersson adjoint of it.
- **Thm 5.8, p. 69 [PDF 73]**: the two actions are adjoint w.r.t. the Weil pairing; for p ∤ N adjoint of T_p is ⟨p⟩^{-1}T_p. (Not stated for U_p.)
- Gap: Conrad has a single level N; nothing about the maps between levels or about the commutation of U_p with them.

### 1.2 Ohta 1999 (Compositio 115, 241-301) and Ohta 1995 (Crelle 463, 49-98)
Files `ohta_1999_ordinary-p-adic-etale-cohomology-of-modular-towers-i.pdf`, `ohta_1995_p-adic-eichler-shimura-isomorphism-...pdf`
(both present, text layer). Tower: Γ_r = Γ_1(Np^r), X_r = X_1(Np^r) (canonical models over Q).
- **Ohta 1999 §1.2, p. 247**, diagram (1.2.4) and the sentence after it: the Hecke operators T^*(p^t) (defined at each level on
  Γ_rs = Γ_r ∩ Γ_0(p^s) by the explicit coset formula (1.2.5)) act compatibly with the trace/corestriction maps of the tower.
  This is the *trace* side (covariant). By Poincaré duality / the adjointness of Lemma 5.4 (Conrad) it would transport to a
  statement for pullbacks and the dual operator; Ohta does not state that dual version.
- **Ohta 1999 §3.4, p. 272** (Lemma 3.4.7, Example 3.4.8 (i)), **p. 273** (Prop 3.4.12; proof on pp. 273-274): for Γ = Γ_1(M) and the
  canonical model, the endomorphisms T := q_* p^*, T^* := p_* q^* of the generalized Jacobian are defined for α = diag(1,l), any prime l
  (so l = p is allowed), Cot(T) is the usual operator f|[ΓαΓ], and T, T^* act on the torus part by the explicit maps of Prop 3.4.12.
  Again a single level.
- **Ohta 1995 §1.3, p. 59 [PDF 11]**: specialization maps commute with all T^*(n), T^*(q,q) (citing his earlier paper, (7.4.4)); **Lemma 1.4.4, p. 64
  [PDF 16]**: the specialization diagrams commute with corestriction (s >= r >= 1). Cohomology of the tower, not Jacobians.
- Ohta 2000 (Math. Ann. 318) and Ohta 2003: grep for pullback/Picard/U_p compatibility finds only the same "T(p) commutes with trace"
  type remarks (e.g. 2000 §1.2 near (1.2.4)); not a Picard statement. Not re-cited.

### 1.3 Other candidates examined, nothing usable
- Helm 2007 (Israel J. Math. 160, 61-117): works with Γ_0(N) and Shimura curves, uses "Picard and Albanese functoriality" only for the
  maps J_0(Mq) → J^D; no Γ_1(Mp^s) / U_p-vs-degeneracy statement.
- Diamond-Im 1995, `diamond-im_1995_..._scan.pdf` (image-only, read as images): §8.4 pp. 72-73, (8.4.1): the bad reduction maps i_F, i_V
  at p ∤ N (as already cited by B1). It concerns T_p at p ∤ N mod p, not U_p at level Mp^s. §§9-10 not found to help.
- Wiles 1988 (Invent. 94, 529-573), file is an image scan (read as images, pp. 529-531 checked): §1 is about Hilbert modular forms and
  Hecke algebras over a totally real field; no Jacobian-pullback statement seen. Not exhaustively read.
- Hida 1988 (Ann. Math. 128): Thm 8.1/8.6 give Hecke equivariance of the maps on the tower in cohomology (see 3.2), not Picard.

### 1.4 What would close the gap (suggestion for D3)
The commutation follows formally from two inputs, both elementary but unreferenced here: (a) at level Γ_1(Mp^s) with s >= 1 the
correspondence U_p = (π_1 × π_2)(X_1(Mp^s, p)) is compatible with the degeneracy X_{s'} → X_s, because the subgroup C of order p
always has trivial intersection with the μ_{p^s}-part of the level structure (so the double-coset decomposition of Γ_{s'} diag(1,p) Γ_{s'}
is the pullback of that of Γ_s); (b) Lemma 5.4 (Conrad) to pass between Pic and Alb. Ohta 1999 p. 247 is the closest published
statement of (a) (on the trace side). D3 should treat the Picard/pullback form as *to prove* with these two anchors.

## 2. Stage 05

### 2.1 Buzzard 1997 (Duke 87)
Present: `buzzard_1996_integral-models-of-certain-shimura-curves_preprint.pdf` (author preprint, as in lit-b4). The Duke version
(DOI 10.1215/S0012-7094-97-08719-6) is behind a Project Euclid bot challenge (Incapsula) from curl: **manual download needed**.
No page numbers of the published version are available; cite the preprint pagination only.

### 2.2 Takahashi 2001 (JNT 90)
Not in `literature/`. **Pending manual download**: DOI 10.1006/jnth.2000.2614 (ScienceDirect).

### 2.3 Bushnell-Henniart
Skipped (Springer book, not free; no longer needed).

## 3. Stage 06

### 3.1 DDT97 Lemma 4.17 and §4.4
File `darmon-diamond-taylor_1997_fermats-last-theorem_preprint.pdf` (167 pp., dated May 24, 2000); also the McGill version dated
September 9, 2007 (`..._preprint2007.pdf`, same numbering). PDF page = printed page in both.
- **§4.4 "Proof of theorem 3.36", begins p. 124**: reformulation of Wiles' argument: η_Σ via O/η = T_Σ/(℘ ⊕ I), symmetric-square L-value of Hida, plus
  the two ingredients (Ihara-type lemma, Mazur-type structure of T_ℓ(J_0(N))) deferred to §4.5.
- **Lemma 4.17, p. 126**: for a self-dual T_Σ-module L (f.g. free over O, L ⊗ K free of rank d over T_Σ ⊗ K, perfect T-equivariant
  pairing) and a basis x_1..x_d of L[℘], η_Σ^d ⊂ O·det⟨x_i,x_j⟩, with equality if L is free over T_Σ. The proof compares L/(L[℘]+L[I]) with the
  cokernel of L[℘] → Hom_O(L[℘],O).
- Cor 4.19, p. 127 follows from Lemma 4.17 and Thm 4.18 (freeness of L_T, L_H).
- The numbering above is that of the preprint (the McGill versions). The published version (Current Developments in Mathematics 1995, Int. Press
  1997) is not freely available; whether its numbering agrees is **unverified**. KO Cor. 5.9 should cite "Lemma 4.17 of the online
  version (version of 2000/2007), p. 126".

### 3.2 Hida 1988, Ann. Math. 128 (pp. 295-384)
Already present: `hida_1988_p-adic-hecke-algebras-for-gl2-over-totally-real-fields.pdf` (JSTOR scan with a text layer; no OCR needed;
91 pp.; printed page = PDF page + 293). All four pointers verified:
- **Thm 8.6, p. 362** [PDF 69]; **Thm 9.4, p. 369** [PDF 76]; **Thm 10.1, p. 370** [PDF 77]; **Cor 10.4, p. 373** [PDF 80].
(Statements not paraphrased here: they are the ones KO cites; the text layer is searchable for the D3/S06 writers.)
The other Hida 1988 file `hida_1988_modules-of-congruence-...pdf` is the Amer. J. Math. 110 paper (pp. 323-382), a different paper; its text layer
cites "[11, Theorem 9.4]" at line 1774 (= the Ann. Math. paper).

## 4. Manual downloads (Abhijit)
None of the following is in `literature/` as of this note (checked by `ls`):
| item | where |
|---|---|
| Gelbart 1975, Automorphic forms on adèle groups (Ann. Math. Stud. 83) | Princeton UP book (library) |
| Eichler 1973, LNM 320, pp. 75-152 | https://doi.org/10.1007/978-3-540-38509-7_4 |
| Kneser 1966, PSPM 9, 187-196 | https://doi.org/10.1090/pspum/009/0213361 |
| Takahashi 2001, JNT 90 | https://doi.org/10.1006/jnth.2000.2614 |
| Kurihara 1979 | U-Tokyo repository (was in maintenance in lit-b4) |
| Buzzard 1997 (Duke) | https://doi.org/10.1215/S0012-7094-97-08719-6 |
(`kneser_1969_lectures-on-galois-cohomology-of-classical-groups.pdf` and `kurihara_1993_...` are different works.)

## 5. Self-audit
Every page below was re-opened (text layer or rendered image) after drafting:
- Conrad: Thm 5.1 p.65 [PDF 69], Lemma 5.4 p.67 [PDF 71], Defs 5.5/5.6 p.68 [PDF 72], Thm 5.8 p.69 [PDF 73] -- confirmed.
- Ohta 1999: p. 246 (Def 1.1.5, idempotent e), p. 247 ((1.2.4), (1.2.5)), p. 272 (Lemma 3.4.7, Ex. 3.4.8), p. 273 (Prop 3.4.12) -- confirmed.
- Ohta 1995: p. 59 (specialization/T^*), p. 64 (Lemma 1.4.4) -- confirmed.
- DDT: §4.4 p.124, Lemma 4.17 p.126, Cor 4.19 p.127 -- confirmed in both versions.
- Hida 1988: pp. 362, 369, 370, 373 -- confirmed by header and statement.
- Diamond-Im pp. 72-73 viewed as images -- confirmed (8.4.1). Wiles pp. 529-531 viewed -- confirmed as Hilbert-form set-up.
Not verified: published pagination of DDT and Buzzard; the claim in 1.4(a) is our own reasoning, not a citation.
