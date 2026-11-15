# Stage 06 chapter — notes (package `abhijit/s06-math`, WPs S06-M1, M2, M3, M4, M7, M8)

Single writer of the per-stage files: `standalone-s06.tex`, `chapters/s06.tex`, this file. `s06-m5.tex`, `bib/s06-m5.bib`,
`bib/s06-m11.bib` are local (Fabian's node) and are picked up by the guarded inputs when they exist. Labels owned by s06-m5
(`prop:s06-levM`, `rem:s06-minus1`) are `\ref`'d and stay undefined in the standalone build until s06-m5 lands (sibling rule).

## Deviations from `plan/staged/stage-06-integral-defect.tex` (statements kept; all marked `\provisional` or remarked)
- (D-M2a) `lem:s06-decomp`(b): the distinctness of the two roots mod 𝔪 ("≡ U_q and ≡ qU_q") needs U_q² ≡ S_q mod 𝔪. This holds
  because the q-new branch F lies in the 𝔪-component (H1); without a q-new form at 𝔪 the two roots can coincide. The tex gives
  no justification. `\provisional{S06-M2: ...}` in s06-m2.tex.
- (D-M2b) `lem:s06-decomp`(a): "no common eigensystem" is proved via local–global compatibility at q (ramified vs unramified
  Galois representation, Carayol / DDT Thm 3.1), instead of strong multiplicity one.
- (D-M1a) `lem:s06-G`: proved by Nakayama over A for the finite A-module S^∨/Sℓ (no semilocality of S used); stronger, not a change.
- (D-M1b) `lem:s06-S` base change holds for any ring map A → A' (locality unused); the tex's "local" is kept.
- (D-M1c) `thm:s06-E`(i) is proved directly (Φ_𝔟(β)(x) = λ(β)); the normalisation ℓ(θ) = 1 of the tex is not needed
  (Φ_𝔟(θ) = λ'). (iii): ℓ'(θ') = λ'(1) = 1 gives unimodularity directly. DVR case: rank one of S'[λ'] uses (Gor_S) through
  S_K = S'_K × S''_K (Lemma S over K) — this use of (Gor_S) is recorded in `rem:s06-gor-uses`.
- (D-M3a) Step (3) / `lem:s06-control`: freeness of T' via Lemma D(c) needs (Gor_T) over Λ (Hsieh §3.3); the tex invokes Lemma D(c)
  without naming it. Control is proved as an equality (exact sequence for 𝔟 splits; rank count for T'), with the well-definedness
  of T'/P_k → T'_k via Lemma D(a) at weight k.
- (D-M3b) `cor:s06-fixed`: in the application (f = F_P) the Gorenstein input is derived by base change of (Gor_R) along P
  (A4), and Thm E(iii) is run over O_P; for general f, KO Prop 5.1(1) is cited.
- (D-M7) `prop:s06-betti`: (a) degenerate case (no sign ε with T_q − ε(q+1)q^{(k−2)/2} ∈ 𝔪: both sides 0) made explicit;
  (b) the maximal ideal 𝔪_N (U_q ≡ ε q^{(k−2)/2}) made explicit, and (H0) used (p ∤ φ(N), q ≢ 1). `\provisional{S06-M7: ...}`.
  (b) is now proved (status upgraded from "cited for existence / to prove" to "proved modulo cited") via Diamond 1991
  (Astérisque 196–197, pp. 205–213: Ihara's lemma in weight k, Lemma 3.2, and the cohomological congruence module, §2), which is
  in `literature/` inside the Astérisque volume. Ri84 (scan) is not used.

## Open points
- (N1) `lem:s06-decomp`(a) uses the Λ-adic Galois representation attached to each K̄-eigensystem and its ramification at q
  (Hida, Wiles 1988). Treated as standard input; no single theorem number pinned (Hi86a not in literature; wiles_1988 present,
  not checked).
- (N2) Hida's Γ₁-statements (Thm 3.1, Cor 3.2) are applied to the trivial-tame-character Γ₀ component (direct factor,
  p ∤ φ(N)); stated in the text, not separately cited.
- (N3) η^B_F ≠ 0 (needed to divide in "(h_F) = 𝔠_q(F)"): follows from multiplicity one for the primitive branch F (the factor of
  R'_K at λ' is a field). Implicit in seed and tex; stated in s06-m1.tex after Thm E, no citation.
- (N4) `lem:s06-pstab` (ordinary p-stabilisation at k ≥ 3) is proved by the Hensel argument; the fact a_p² = p^{k−2} for p-new forms
  uses (I2) for an auxiliary ℓ'-adic representation.
- (N5) `prop:s06-betti`(b) input (B3): H¹ and parabolic H¹_P agree after localisation at non-Eisenstein 𝔪. Standard; no source
  located in `literature/`.
- (N6) The Λ-adic Eichler–Shimura relation tr(Frob_ℓ | H) = T_ℓ is cited through Hsieh §7.2 and DDT Thm 3.1(a) (classical
  specialisations); a direct Λ-adic reference (Hida 1986 Inventiones, `hida_1986_galois-representations-into-gl2-…`) was not checked.
- (N7) `rem:s06-several-r3` (M8): for r = 3 exactly the q₁-new and q₁q₂-new intermediate quotients must be Gorenstein (each is the
  "S" of one step: indispensable); a relative Lemma decomp and a relative free-rank-two module are also needed. KO Thm 1.1 with
  N⁻ = D suffices for all factorwise equalities via the product squeeze (I_F local). Status \stsketch / \stopen as in the tex.

## Literature
- Present although the tex says missing: `mazur-wiles_1986_p-adic-analytic-families-of-galois-representations.pdf` (MW86) and
  `bockle_2007_presentations-of-universal-deformation-rings.pdf` (Böc07). Not re-checked here (S06-M11).
- Missing: Ri84 is only an image scan (`ribet_1984_…_scan.pdf`); Hi86a (Inventiones) not checked; Ihara 1975, Deligne 1974 (Weil I).
- Page conventions used: Hi86b journal = PDF + 229 (Thm 3.1, Cor 3.2, (3.4a–d), Cor 3.3 all on p. 250, re-checked against the
  OCR); Dia89 journal = PDF + 47; Diamond 1991 journal = PDF − 4 inside the Astérisque volume; Carayol 1986 journal = PDF + 407;
  Hsieh, KO, PW, Dimitrov: arXiv PDF pagination; DDT preprint: PDF = printed page.
