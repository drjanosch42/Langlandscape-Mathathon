<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S05-M8b — Fable follow-up chapter audit, stage 05

- Target: `git diff f05d617e 51cb92e5 -- mathematics/` on `wip-implementation` (read-only): `chapters/s05/*`, `preamble.tex`,
  and the S05-E1 edits in `chapters/s01`–`s04`, `references.bib`. `mathematics/report/` (hypotheses report) was not audited.
- Role: `agents/roles/mathematics_chapter_audit.md`. Predecessor: `plan/implementation/audits/s05-m8-chapter-audit.md` (M8, 14 items).
- Date: 2026-11-15. All line numbers are at `51cb92e5`.

## Verdict: PASS (WITH REMARKS)

Counts: crit 0, maj 0, min 8. All three M8 maj items are closed. No overclaim found; two of the remarks are *under*claims.

## 1. M8 items: closed?

| Item | State | Evidence |
|---|---|---|
| M8-1 (maj) `\Ros` = `\vee` | closed | `preamble.tex:118`, `s05.tex:9`: `\mathsf{Ros}`; fresh PDF prints `T_ℓ^Ros`, `θ_s^Ros`; the dual stays `\vee` |
| M8-2 (maj) `status.tex` vs `sign.tex` | closed | `status.tex:61-64, 73` now agree with `rem:s05-Xstatus` |
| M8-3 (maj) row 1 "cited" | closed, option (ii) | table anchored at row 2 (Conrad 5.16/5.1 + local–global at q), rows 3, 1, 4 derived; Lemma 3.17 is a consistency check. I re-derived the chain row 2 → 3 → 1 → 4; correct. Residual: M8b-5 |
| M8-4 hybrid dictionary | closed | `sign.tex:122-132`; the text also corrects my M8-4 wording (T05-2 is s = 0 and cannot exclude the hybrid). See M8b-3 |
| M8-5, M8-6, M8-8, M8-9, M8-11, M8-12, M8-14 | closed | as requested |
| M8-7 | closed, new pointer imprecise | M8b-6 |
| M8-10 Lean status | closed | `subquot_kernel`, `subquot_coker` (`CommAlg/SubQuot.lean:299, 328`), `xiso_of_gorenstein` (`Comparison/XIso.lean:98`) exist, no `sorry` (grep); "standard axioms only" is backed by inbox `s05-int0-1` (AXIOMS 28/28, 4/4, nonstandard 0). Not rebuilt by me |
| M8-13 notation | partly closed | `ε_U`, `𝔐` done; M8b-7, M8b-8 |

## 2. New mathematics

**`lem:s05-normtwist` (`hypX.tex:418`): correct.** Recomputed:
τ^{-1}(a b; c d)τ = (d, −c/N; −Nb, a); Nrd u ≡ ad mod N on U_0(N); for u ∈ U_1(N), [xuτ] = ⟨Nrd u⟩[xτ]; t_χ is well defined
(χ̂(Nrd γ) = 1 because B is definite; the two factors χ(Nrd u)^{±1} cancel); t_χ∘⟨d⟩ = χ(d)^{-1} t_χ since τ^{-1}δ_dτ = diag(d,1) ∈ U_1(N);
vanishing off the χ^{-1}-piece uses that A is a domain. The remark τ_ℓ^{-1}(0 1; −Nq 0) = diag(q,1) ∈ U_{1,ℓ} is right.
Status "proved" for the lemma, "sketched" for the identification with Hsieh's [τ^D_N]: truthful. Hsieh pointers checked on the PDF:
[τ^D_N]f(x) = ρ(τ)f(xτ)χ(ν(x)), S(N,χ) → S(N,χ^{-1}); B_{N,α} with U_p^{-α}, χ_I(ν(x)), (#Γ)^{-1}, "One verifies … (mod P_α)" (pp. 30–32): all as quoted.

**φ(N)/2 (`rem:s05-c2open`(vi), `hypX.tex:490`): correct.** Fibre of S_s → X_B(U_0(N)) over [x] is (Z/N)^×/d(x^{-1}Γ_x x); d is injective there by
`lem:s01-stab`(b) (applies: p ∤ D, U ⊆ U_1(p) at p); so Σ_{S_s} F = φ(N) Σ F/|Γ_x| = (φ(N)/2) Σ F/#Γ_{N,x}; v_p = v_p(φ(M)) + s − 1.

**(c2) list (i)–(vi): honest, no overclaim.** (c2) is `\stconj`/`\stopen`, the proof paragraph says "No proof is given", (d2)'s Hom_Λ-form,
`rem:s05-BN` and the η^B_F table row are flagged; no other chapter uses (c2). The character bookkeeping in (v) (u_s pairs ε with ε^{-1},
[ , ]_s pairs ε with ε, ⟨ξ, t_χη⟩ pairs the χ^{-1}-piece with itself) is right. Remark: M8b-4.

**`rem:s05-computed` vs JSON.** T05-1: 16 (q,k) pairs, 144 eigenlines, 144 plus, 0 minus, 0 unmatched: matches. T05-2: pairs, dimensions
11/19/21/43, primes ℓ, tolerance 1e-6, all six match/fail entries per pair, the "uninformative at N = 5" scope, θ^Ros matching everywhere:
all match the JSON. T05-3: q and orders 5, 11, 3, 25, 65, cyclic: matches. Two inaccuracies: M8b-1, M8b-2. The new "only even characters occur"
paragraph (`sign.tex:177`) and the criterion q² ≢ ±1 mod N are correct.

## 3. Statuses

- Hyp.X is never called known (grep and reading of the changed text); `\sthyp` kept.
- FD1 `\provisional` with the explicit sentence at `hypX.tex` (data list, (X4), `if:s05-hypX`, (d1)/(d2), (L1)) and `sign.tex` (Setting,
  `prop:s05-sign`(a), `rem:s05-Xstatus`); FD2 at `geometric.tex:97, 120`. Present and searchable.
- "Frobenius clause of (S4) proved modulo cited" (`status.tex:73`) is justified: on each isotypic piece for the operators away from the level
  both Frob_q and U_q act as scalars on T_t, so the eigenvalue argument gives the operator identity. The Frobenius *permutation* stays expected (needs (X1)). Consistent.
- Compilation: forced `latexmk -g -pdf standalone-s05.tex` on an export of `51cb92e5`: 134 pages, no undefined reference or citation, no multiply defined label.

## 4. S05-E1 edits in s01–s04 against the Lean tree at `51cb92e5`

All checked claims are truthful:
`nrdSurj_{Ohat,U0,U1,Utower}` take `Hyp.RamNrdSurj` (`Quat/LevelNrd.lean:217-240`); `Hyp.HS` is used for representatives (`Tree/NormOne.lean:185`);
`Hyp.LambdaJL` has `Nat.Coprime d (M * p)`; `Hyp.EllipticCount` has the `d.D ≤ 3` clause and `Ribet.mazur_check` covers every prime q;
`ribet_{exact,rank}_of_SA_HS` take `Hyp.BTtree`; `Hyp.HidaControl` has `hk`, `_hφ` unused in the statement; `Hyp.InvLimExact` is the implication and
`lim_exact_ribet` takes the literal `hA`; `Hyp.HsiehCR` and `hsiehCR_toy` exist, no Lean consumer; `Hyp.MordLambdaFree` has no consumer outside tests.
`Vig80` is no longer cited anywhere; Voight Thm. 13.3.11 exists as quoted. No item.

## FIX LIST (all min)

- **M8b-1 (min)** `sign.tex:230`. Defect: "(δ,e) = (−1,−1) with T_ℓ ↦ T_ℓ fails everywhere (the T_ℓ-relation)". At N = 5, ⟨d⟩ = ⟨d⟩^{-1}, so the
  T_ℓ-relation holds; the JSON shows the same failures as for (+1,−1) there (6 and 10 unmatched = the χ(q) = −1 part), i.e. through Π_q^{-1} = −Π_q.
  Fix: "fails everywhere: at N = 7 by the T_ℓ-relation, at N = 5 as for (+1,−1)". (The JSON `explanation` has the same imprecision.)

- **M8b-2 (min)** `sign.tex:207-208`. Defect: "Provenance: commit `89045d1f`" for all three; `T05-2.json:859` and `T05-3.json:60` record
  `89045d1f…-dirty` (T05-3's source also `518e93aa…-dirty`). Only T05-1 is clean. Fix: regenerate T05-2/3 from a clean tree, or write "(working tree dirty for T05-2, T05-3)".

- **M8b-3 (min, underclaim)** `sign.tex:131`. Defect: "Excluding [the hybrid] needs an input at p-power level that we do not have: open". An input is
  available as cited: under the hybrid the Brandt eigenvector of f gets the system of f̄ except U_p ↦ a_p(f) instead of a_p(f̄) = conj a_p(f). So (X1)
  with the hybrid contradicts the cited JL eigensystem matching including U_p (`thm:s01-lambdaJL`) plus strong multiplicity one, at any level s ≥ 1
  carrying a q-new form with non-real a_p. Fix (optional): replace "open" by this argument with status proved modulo cited, stating the non-real a_p
  condition; or keep "open" and add "(not excluded by the arguments of this chapter)". My M8-4 wrongly named T05-2 for this.

- **M8b-4 (min)** `hypX.tex:270-271` with `:499`. Defect: (c2) carries `\stconj`, while (vi) says it is "a heuristic, not a conjecture with a definite
  statement". Honest but two labels for one thing. Fix: keep `\stopen` and write "expected (heuristic; no precise statement yet)" in place of `\stconj`,
  or say once that `\stconj` is used for want of a weaker label.

- **M8b-5 (min)** `sign.tex:338`. Defect: the new anchor's key input, local–global compatibility at q, is cited by names only ("Langlands, Carayol"),
  with no `\cite`/`\lit`, although the status is proved modulo cited. Fix: add the reference with theorem number (Carayol 1986, *Sur les représentations
  ℓ-adiques…*, is in `literature/`; for GL_2/Q also Langlands 1973 / Deligne), and mark the pointer as checked or not.

- **M8b-6 (min)** `status.tex:51`. Defect: "the general statement for semistable curves is Raynaud's theorem, SGA 7 IX, 11.5". Thm. 11.5 is the
  component-group theorem for semistable abelian varieties (so used in `thm:s05-G`(iii), p. 455); the curve statement with thicknesses is Raynaud,
  Astérisque 196, Thm. 5, p. 17 (already cited there), resp. SGA 7 IX §12. The pointer came from my M8-7 and was from memory; SGA 7 is not on this node.
  Fix: cite Raynaud Thm. 5 for curves, SGA 7 IX 11.5 for abelian varieties, and mark the SGA pointer "not re-verified".

- **M8b-7 (min)** `hypX.tex:141`. Defect: one `M` was missed in the M8-13 rename: `\lambda_tM(\alpha^\Ros)` should be `\lambda_t\mathfrak{M}(\alpha^\Ros)`.

- **M8b-8 (min, residual of M8-13)** `sign.tex`, `hypX.tex`. Defect: `w` still denotes the Atkin–Lehner involution, the weights `w_x`, `w_e` and the
  index of ⟨,⟩_w; `e` and `δ` remain overloaded. Fix: optional; a one-line notation warning at the Setting suffices.

## Not verified

SGA 7 page pointers (not on this node; the chapter says so); the Voight page number; Lean was not rebuilt (statuses taken from grep and the inbox reports).
