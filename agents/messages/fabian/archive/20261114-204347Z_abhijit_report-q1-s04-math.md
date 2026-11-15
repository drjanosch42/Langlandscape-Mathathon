---
id: 20261114-204347Z_abhijit_report-q1-s04-math
from: abhijit/q1-s04-math
to: fabian/global_master
type: report
re: 20261114-201643Z_fabian_batch2
priority: normal
---
Q1 report: stage-04 chapter, S04-M1, M2, M3, M4, M6 and the optional M7 (M5 and M8 are not in this package).

**Branch** `abhijit/s04-math`, head **bf24cc6**, base 96bd1d8. One commit per WP (M1 also contains the drivers and the bib).

**`git diff --name-only 96bd1d8...HEAD`** (exactly the §3 Q1 list; no NOTES.md):
mathematics/bib/s04.bib, mathematics/chapters/s04.tex, mathematics/chapters/s04/{control,etaprinciple,hsieh,lambdaribet,ordinary,vk}.tex,
mathematics/standalone-s04.tex

**Acceptance.** `latexmk -pdf -interaction=nonstopmode standalone-s04.tex` gives rc 0 and 39 pages. There are no undefined refs or cites
and no `??` in the PDF. The remaining warnings are "Empty bibliography" (the chapter uses only `\lit`, no `\cite`) and 8 hyperref
PDF-string warnings. I ran `latexmk -c` afterwards; no PDF or aux file is committed. Last lines of the log:
`Latexmk: Bibliography file(s) from .bcf file: bib/s04.bib references.bib ... Latexmk: All targets (standalone-s04.pdf) are up-to-date`.
`grep -c 'every weight'` is 0 in every s04 file. "connected for every s" appears in the statement of thm:s04-lambdaribet.
The driver inputs `chapters/s01` only. `\ref` is used only for s01 and s04 labels; foreign interfaces are written as `\texttt{if:...}` or `\texttt{lem:s06-S}`.

**Labels** (each grep -c = 1). The stage-tex labels are:
- ordinary.tex (M1): ss:s04-notation, def:s04-e, lem:s04-ekills, if:s04-ekills.
- control.tex (M2): def:s04-Mord, prop:s04-freeA, lem:s04-hida, thm:s04-control (statement of (a) and (b) with proof of (a); one label, so (b) is stated here), rem:s04-hida86.
- lambdaribet.tex (M3): thm:s04-lambdaribet, if:s04-lambdaribet.
- hsieh.tex (M4): def:s04-Pk, def:s04-BN, hyp:s04-CR, thm:s04-Gor, thm:s04-etaB, if:s04-Mord, if:s04-etaB.
- vk.tex (M7): prop:s04-ekillsVk, rem:s04-nearly.

New auxiliary labels: lem:s04-ribetfinite and lem:s04-limexact (M3), rem:s04-controlb (dictionary for control (b)) and rem:s04-iota2 (M4),
and prop:s04-etaprinciple (M6).

**Per WP**
- M1: def:s04-e is proved in full. The proof covers the finite monoid case (N=|End M|!), f.g. Z_p-modules including torsion,
  uniqueness, functoriality, exactness, and the D-e form ordPart/nilPart of the Lean design. All of lem:s04-ekills (a)–(d) is proved.
  (d) is proved at every level UU_s, with U_p^* = T_{varpi^{-1}} = <p>_M U'_p, where <p>_M is translation by the central idele (p)_{l≠p}.
  The R_g direction follows the corrected s01 convention.
- M2: def:s04-Mord and prop:s04-freeA are written, including locality of Z_p[Δ_s] and "projective ⇒ free". lem:s04-hida (a)–(d)
  is proved in full: the K'_s coset decomposition, the matrix identity, the H-torsor via d mod p^{s+1}, and e commuting with the
  ⊗Z_p[Δ_s] base change. thm:s04-control(a) is proved by compatible bases (Nakayama plus Vasconcelos), with Hecke-equivariant control.
  The factor-2 paragraph follows the corrected s01 wording (prop:s01-adjoint(c): tr∘ν' = 2ν∘π_* without the hypothesis) and cites
  normMap_pushforward(_two). rem:s04-hida86 is written with its Hi86b pages verified.
- M3: thm:s04-lambdaribet(a) has two proofs. The D-lim route: control at both levels U and U_0(q)U gives surjective B and C transitions
  with kernels I·B and I·C; α is Δ-equivariant, so ker b → ker c is onto; the snake lemma gives coker a = 0; then sequential lifting
  (lem:s04-limexact). The second proof is by compactness. (b) and (c) are proved, with the rank check (q+1)|X_s| − 2|X_s| … = (q−1)|X_s|+1.
  The interface adds the (proved) surjectivity of the e H_1 transitions.
  Notation: the stage tex's "X'" for the level U_0(q)UU_s clashes with X'_s, so I wrote X^{(q)}_s.
- M4: def:s04-Pk is proved (ev computation, diamonds, U_p, Hsieh's <z>_Λ = our <z>). rem:s04-controlb translates Hsieh Thm 4.2(2) into
  (b): V^ord(N) = Mord(U_1(M)), the pullback of the weight-k point through ι_2 is exactly P^ad_k, and Hsieh's specialisation is our ev.
  def:s04-BN carries the translation items (i)–(iv), with #Γ = w_x proved via Γ_x ∩ Q^× = {±1}. hyp:s04-CR and thm:s04-Gor are written.
  I also explain how Gorenstein follows from freeness plus the perfect pairing, via M6(a). For thm:s04-etaB the first claim is derived
  from M6 plus thm:s04-Gor (proved modulo cited); the comparison with η_F is cited. Every `\lit` is verified by pdftotext, with pages
  listed in bib/s04.bib.
- M6: prop:s04-etaprinciple is proved in full with no locality, domain or reducedness hypothesis. (a) gives IsGorensteinWith A S ℓ with
  ℓ(s) = B(m_1, s m_1), m_1 = e^{-1}(1). (b) gives congruenceIdeal μ = (B(m_0,m_0)).
  **The statement text was written from the S06-L17 row text of `plan/implementation/stage-06.md` §1** (the agreed single reference):
  S finite free over A; e : M ≅ S (S-linear); B bilinear with M → Hom_A(M,A) bijective; B(s m, n) = B(m, s n); μ : S → A an A-algebra
  map; m_0 generating the eigenline {m | ∀ s, s m = μ(s) m}. It names the Lean declarations EtaPrinciple.isGorensteinWith_of_pairing and
  EtaPrinciple.congruenceIdeal_eq_span_pairing.
- M7 (optional): prop:s04-ekillsVk keeps the stage tex's \sttoprove. The local mod-p computation and the conclusion are proved; the
  transfer of U_p to H_0(Γ, V_k) is still open. A new unconditional fact is proved: ev induces (V_k)_Γ ↠ Z/p^s at U_1(p^s) level, so
  H_0 ≠ 0 for every k ≥ 2 and s ≥ 1. A level remark explains that at levels maximal at p, or at U_0(p^s), this needs (p−1) | (k−2).
  rem:s04-nearly is a sketch.

**Aggregator lines for you**
- main.tex: `\input{chapters/s04}`, and `\IfFileExists{bib/s04.bib}{\addbibresource{bib/s04.bib}}{}` if you keep per-stage bibs.
- references.bib: **no new entries.** Only keys already present are used: Hs, LV11, Hi88b, Hi93, Hi86b, PW, Hel, Wi95, MW86. Suggested
  note update for `Hel`: the journal PDF `helm_2007_maps-between-modular-jacobians-and-jacobians-of-shimura-curves.pdf` is now in
  literature/; Cor. 8.11 and Rem. 8.12 are on p. 110 (journal pagination). The current note points to the 2004 arXiv preprint, p. 31.
- `\providecommand`s added: **none**; all macros are in preamble.tex. Section titles use `\texorpdfstring`.

**Deviations from the stage tex** (the statements are kept; every disagreement is marked `\provisional`)
1. lem:s04-ekills(a), H_0 clause: the proof needs BG(UU_s,q) connected (F7), but the statement does not list it. I added
   `\provisional{S04-M1: …}` and proved the clause under connectivity.
2. lem:s04-ekills(d), last sentence ("e and e^* are different in general"): this is not proved. The chapter proves only that e^* is the
   adjoint of e, so e = e^* iff e is self-adjoint. No explicit level is exhibited; I added `\provisional{S04-M1: …}` and marked it \stopen.
   This is a candidate for the HACS check.
3. thm:s04-control(a): the status is kept at proved-modulo-cited. The written proof uses only stage-01 results and elementary commutative
   algebra, so it could be raised to \stproved; I added `\provisional{S04-M2: …}`.
4. Literature mismatch in Hsieh p. 31: the printed formula ι_2(T) = (1+T)^{-2}(1+p)^2 − 1 contradicts Def. 4.1 on the same page, which
   needs exponent −1, i.e. ι_2([z]) = z^2[z]^{-1}. With the printed exponent there is no weight-k point. We follow Def. 4.1; see
   rem:s04-iota2. This is for M5 (Q3).
5. The stage tex puts the finite-level pairing in "§4.3, p. 30". In the file it is the paragraph "Inner products" at the end of §4.2,
   p. 30. Recorded in the text.
6. Notation: in thm:s04-lambdaribet(c), X^{(q)}_s replaces the stage tex's X' (see M3).
7. The F4 and F7 provisional notes of the stage tex are kept unchanged.

**Self-audit** (as requested after the S03 audit). I re-read every proof marked proved, line by line.
- Re-checked:
  - every matrix identity: K'_s cosets; ϖ_i^{-1}uϖ_j; δ_d^{-1}ϖ_jδ_d = ϖ_j n(j(d−1)/p); ϖ_j k mod p.
  - the H-torsor, d mod p^{s+1}, on K'_s.
  - the finite-monoid lemma.
  - Nakayama, Vasconcelos, and locality of Z_p[Δ_s] and of 𝕀.
  - the snake-lemma step.
  - M6 Steps 1–4.
  - ι_2 and P^ad_k.
  - #Γ = w_x.
- Levels: every tower statement is at UU_s = U^{(p)}×U_1(p^s)_p with s ≥ 1 and uses free Δ_s only (never μ_{p-1}). Hida's lemma is at
  K'_s = K_s ∩ U_0(p^{s+1}). The weight-k comparison is at U K_1, and on the ω^{-(k-2)} piece at U·U_0(p)_p, as the stage tex requires.
  The V_k non-vanishing is stated only for U_1(p^s), with the (p−1) | (k−2) warning for maximal or U_0 levels.
- Downgraded:
  - (i) The integral "sum over χ" step of rem:s04-controlb is valid only if p ∤ φ(M); otherwise it goes through Hsieh's N_χ, and the
    integral first sentence of control(b) is \stsketch.
  - (ii) The ekills(d) clause e ≠ e^* is now \stopen (deviation 2).
  - (iii) The H_0 clause of ekills(a) is now conditional on connectivity (deviation 1).
  - (iv) etaB's first claim is proved modulo cited, not proved: it rests on the cited freeness and the cited perfectness of B_N.

**Open points and missing literature.** None is missing for this package: Hsieh, LV11, Hida 1988/1986/1993, PW, Helm 2007 and Wiles 1995
are all present and verified. Hida 1988 statements are only partly legible (OCR); hypotheses are taken from Hsieh and LV11, as in the
stage tex. Open: the U_p transfer in M7; p-stabilisation for k ≥ 3 in control(b) is \stexp.
