<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Guide round: independent read of the new and changed s00 text (2026-11-15)

Scope: `chapters/s00/guide.tex` (new), `chapters/s00/whycited.tex` (paragraph "Why p-adic and Λ-adic JL are cited",
F2, F4), `chapters/s00/abstract-short.tex` (F3), `chapters/s00/achieved.tex` (b)/(c), `article/mainresults.tex` (b)/(c),
`lean/Langlandscape/HYPOTHESES.md` (LambdaJL row), `report/hypotheses.tex` (LambdaJL entry). Base: `wip-submission`
08e4f249. Checked against the chapter statements (labels read in the sources, not in the summaries) and the team
decisions (first case, N1/N2, F2/F3/F4, the GO for the new paragraph). No `.lean` file was edited.

## 1. Verdict

**PASS after fixes.** No status upgrade was found in the status words themselves. Two statements of the guide were
inaccurate against the chapters (M1, M2) and are corrected; seven minor points of the guide and one of `whycited.tex`
are applied; three minor points are listed and not applied (n1 binding wording, n2 regenerated file, n3 remark).
The new paragraph of `whycited.tex`, the abstract and items 4 are consistent with the chapters and with each other.

## 2. What was verified (no finding)

- **D versus q.** `ribet.tex` (combinatorial form): the chapters' `(D, q)` play Ribet's `(q, p)`. The guide's warning and
  row 1 of the table say the same. Ribet's sequence and the Ihara lemma sit on the row "`B_D` with tree prime `q ∤ D`"
  (Thm s03-ribet, Cor s03-ihara), as in the chapters.
- **Stage 06 and GL₂.** `s06.tex` (driver) and Def s06-rings: stage 06 works on the GL₂ side, `B_q` enters only through
  the cited Λ-adic Hecke JL (`T' ≅ T^ord_B`), Hyp.X is not used. The three ways to reach GL₂ in the last table row
  (Thm s05-G cited at Γ₀-type level; Hyp.X at Γ₁(Mp^s)-level; cited JL) match `achieved.tex` (a).
- **Level raising and lowering.** Prop s03-LRdef (proved) is the definite level-raising operator with the printed
  matrix; Cor s06-fixed is titled "fixed-weight level lowering" and is `proved modulo cited`; the guide's statement
  that level lowering is not a graph operation in the chapters is correct (`ss:s05-lost`, (L2)).
- **Statuses in the guide**: Prop s02-BG (proved; tree connectedness cited in one direction), Thm s03-ribet(a) and
  Cor s03-ihara(i),(ii) (proved given (iii)), Prop s03-mazur (pmc), Prop s03-phieis (proved), Thm s04-control ((a)
  proved, (b) qualified), Thm s04-lambdaribet (proved given connectivity at all s), Hyp s05-X (hypothesis), Thm s05-G
  (cited), Prop s05-nochain (proved), Thm s06-defect (pmc; open for q ≡ −1 mod p outside (Lev)), Rem s02-CD (cited,
  never used), Thms s01-JLclassical/chenevier/lambdaJL (cited). All as printed in the chapters.
- **New paragraph in whycited.** Lemma s04-ekills / `if:s04-ekills`: proved, the H₀ clause of (a) under connectivity
  (as written). Thm s04-lambdaribet(a) is proved from Lemma s04-ekills(a); the perfect pairing is clause (d); so "which
  is what makes the Λ-adic definite Ribet sequence exact and the pairing perfect" is supported. O7 open and "no
  finite-slope analogue of e killing Φ^comb": Rem s05-O7, verbatim. Thm s01-chenevier cited. Prop s05-Xlambda(d) and
  the surjection `T^ord(qM) ↠ T^ord_{B_q}(M)`: Rem s05-O7, sketched, as written. Prop s05-Xlambda(a): proved under the
  standing assumption Hyp.X.char (label: "proved given if:s04-ekills(a)").
- **"The chapters do not derive Λ-adic Hecke JL from it."** Checked by a search of stages 02–06 for every use of
  Thm s01-lambdaJL / `if:s01-targets`: all uses are citations (s05 `subquot.tex`, `hypX.tex`, s06 `s06-m2`, `s06-m3`),
  and the table of `ss:s05-lost` lists "Λ-adic Hecke JL: cited; with Hyp.X: same". No chapter derives it. Correct.
- **Stage 06.** `s06-m3.tex`, Lean pointers: (Gor_{R'}) ↔ `Hyp.HsiehGor` together with `Hyp.LambdaJL`; step (1) of the
  proof of Thm s06-defect transports Hsieh's Gorenstein property along the Λ-adic JL isomorphism. As written.
- **plan.tex.** "possibly the classical input of `LambdaJL`" is a literal quotation of item (C); (D) lists "the p-adic
  and Λ-adic content of `LambdaJL` (Chenevier, Hida)" as cited, not reproved. The hedged "could come from route 1" is
  supported; nothing stronger is claimed.
- **F2, F4.** The two F2 sentences are present verbatim and the following sentence reads smoothly. F4: "a simplicial
  form of route 2 below would be O2" in `whycited.tex`; no occurrence of "essentially O2" remains in any `.tex` or
  `.md` outside `audits/`. Conj s05-O2 itself says "equivalently (by Remark s05-degree) a degree-shifting map", so
  "it amounts to a degree-shifting map" is the chapter's wording.
- **Abstract (F3).** Sentence as decided. 148 words (each formula counted as one word, the declaration count as one).
- **Item 4.** `achieved.tex` (b)/(c), `mainresults.tex` (b)/(c), the HYPOTHESES.md row and the Discharge item of the
  `hypotheses.tex` entry all say: cited; not derived from Φ; stage 06 takes it as a cited input because it does not use
  Hyp.X; classical input possibly through route 1. Consistent with the paragraph.

## 3. Findings

### Major (applied)

**M1 (guide, stage 05). APPLIED.** "proves its formal consequences (e.g. Prop s05-subquot, proved)": Prop s05-subquot
is a statement of commutative algebra (a free module over a Hecke algebra with ideals 𝔞, 𝔟); it does not use Hyp.X and
is not a consequence of it. Replaced by: "proves its formal consequences (e.g. the Λ-adic version, Prop s05-Xlambda(a),
proved given Hyp.X.char) and, independently of it, the commutative algebra of the lattice comparison (Prop s05-subquot,
proved)".

**M2 (guide, stage 06). APPLIED.** "the corresponding ideal η^B_F on the quaternion side": by Def s06-rings,
`η^B_F = η(R', λ')` is the congruence ideal in the q-new quotient `R'` of the GL₂ Hecke algebra; it is "quaternionic"
only through the cited Λ-adic JL. The old sentence contradicted the clause before it ("B_q entering only through the
cited Λ-adic Hecke JL"). Replaced by: "it compares the congruence ideal η_F in the full Hecke algebra with the
congruence ideal η^B_F in the q-new quotient, which the cited Λ-adic JL identifies with the Hecke algebra of B_q: this
is the quaternion side." In the same sentence, "q-new", the old/new congruence ideal and the Tamagawa ideal
(Def s06-tam: entries of ρ_F(σ) − 1, σ in inertia at q) now have a half-line gloss each (readability).

### Minor (applied)

- **m1 (guide, stage 04).** "(Lemma s04-ekills, proved)" → "(…, proved, the H₀ clause under connectivity)", as in
  `if:s04-ekills` and `whycited.tex`.
- **m2 (guide, the narrative).** "stage 06 proves the integral comparison … independently" → "obtains … without it
  (proved modulo cited, as above), using the cited Λ-adic JL instead of Hyp.X". "proves" without the status read as
  an upgrade of Thm s06-defect.
- **m3 (guide, congruence module).** "the sub- versus quotient-lattice comparison has the congruence module as its
  cokernel" → "In commutative algebra, for a free Hecke module of rank r the comparison of the q-new sub- and quotient
  lattices has r copies of the old/new congruence module 𝕋/(𝔞+𝔟) as its cokernel". The statement is not a graph
  statement and the cokernel is `(𝕋/(𝔞+𝔟))^{⊕r}`. "Everything is finite" → "Everything on the definite side is finite".
- **m4 (guide, roles of q; table row 3).** The DR graph of `B_q` is also used in stage 04 (Lemma s04-ekills(b),(c)):
  "the DR graphs of stages 03–04"; stages column "03, 04 (DR graph), 05, 06".
- **m5 (guide, table row 1).** Rem s02-CD holds for Γ₀-type levels only (not for `U₁(N)`): "(Remark s02-CD, cited for
  Γ₀-type levels, never used)". Row 2 already said so.
- **m6 (guide, level raising).** Prop s03-LRdef is stated for `U = U₀(M)`, `V = ℤ`: "(…, proved; level U₀(M),
  coefficients ℤ)".
- **m7 (guide, last sentence).** "concentrated in Hyp.X" → "concentrated in Hyp.X (at Γ₀-type level it is the cited
  Thm s05-G)". Also "outside (Lev)" → "outside the level conditions (Lev)".
- **m8 (whycited, new paragraph).** "Its classical input could come from route 1": the antecedent could be read as the
  defect theorem. → "The classical input of Λ-adic JL could come from route 1".

### Minor (not applied)

- **n1 (whycited, F2).** "what was met is that it is the only geometric input": "it" is the final comparison
  (Hyp.X; Thm s05-G at Γ₀-type level), and the scope is the tree route to the comparison map. Stage 06 has cited
  inputs with geometric proofs of their own (Hsieh's Gorenstein theorems resting on Wiles, Mazur–Wiles and Helm,
  listed in Thm s06-defect). The wording is the team's binding text, so it is left. Suggested, if the team agrees:
  "…; what was met is that this comparison is the only geometric input of the tree route."
- **n2 (`report/hypotheses.tex`, LambdaJL entry, "Used by"; not part of the changed lines).** It reads "No Lean
  consumer yet. Planned: reused in stage 6 by `Setting.gor_new` and `Defect.defect_formula`". The Lean sources have the
  consumers (`Defect/Gorenstein.lean` `gor_new`, `Defect/Main.lean` `defect_formula`, `Defect/Corollaries.lean`
  `cor_allweights`, argument `hJL`), and the HYPOTHESES.md row lists them. The entry understates (no upgrade); it is
  stale. Suggested: "`Defect.Setting.gor_new`, `Defect.defect_formula`, `Defect.cor_allweights` (explicit argument
  `hJL`; only surjectivity and the kernel are used)". Not applied: the appendix of the submission report is generated
  from this file and the standalone PDF would have to be rebuilt; outside this round's time box.
- **n3 (abstract).** The F3 sentence gives the first case as "D = q, weight 2"; the body adds "Γ₀-type level". Within
  the 150 words there is room for it only by dropping words elsewhere; left as decided.

## 4. Readability for a non-specialist (guide)

Good. Every term of art is introduced where it first matters (class set, Brandt module, Hecke operator, Bruhat–Tits
tree, Hida family, Λ, ordinary projector, congruence module; after this round also q-new and the Tamagawa ideal). The
narrative 01 → 02 → 03 → 04, then the branch into 05 and 06, is stated explicitly and matches `mainresults.tex`
("Stages"). The table is readable; its four rows are the four algebras that occur, including the one that is never
used. Left unexplained, acceptably: "(iii)" beyond "a finite check", "(Lev)", the standing hypotheses of stage 06.

## 5. Builds

- `main.pdf` rebuilt (`latexmk -pdf main.tex`; no undefined reference or citation, no multiply defined label).
  Page-by-page `pdftotext -layout` against the committed `main.pdf`: 195 pages before and after. Pages 1–3 (table of
  contents), 5–10 and 19–195 are identical. Page 4 differs by the one edited sentence of `whycited.tex`. Pages 11–18
  (the guide and the pages of s00 after it) differ: the guide is longer and the text
  **reflows across the page breaks of pp. 11–18** by a few lines. No section start changes its page (table of
  contents unchanged). Page numbers in the report that point into main.pdf pp. 11–18 were **not** adjusted.
- Report re-flattened (`python3 -I tools/flatten.py src/report-src.tex --draft`): 0 FAIL, 3 WARN, 19 PASS (the WARN
  count is as in the previous round; not compared item by item). `report.pdf`: 190 pages before and after; pages 5 and
  21–25 differ.
- Article rebuilt in a fresh scratch directory and copied to `mathematics/article.pdf`: 191 pages before and after;
  pages 5 and 12–15 differ.
- Scratch directories (not cleaned): `/home/janosch/data/scratch/render.8oa4`, `/home/janosch/data/scratch/render.eVwa`.
