<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Audit S03-M2, strand D, round 0

Scope: `strand-D.patch` (new `mathematics/chapters/s03/2-eisenstein.tex`, 282 lines; new `mathematics/bib/s03-m2.bib`, one comment line).
Line numbers below refer to `2-eisenstein.tex` as created by the patch.

Checks performed (no defects found here):
- Acceptance check (`check.txt`): exit code 0. The five pdfTeX `dest ... theorem.N.M` warnings also appear when the base tree is built without the patch, so the patch did not cause them.
- Files touched: only the two allowed outputs. Required labels are each defined once. The new labels (`lem:s03-nbr`, `lem:s03-stabfree`, `rem:s03-eis-{cases,ideals,corr}`) occur nowhere else in `mathematics/`. There is no new global macro. Every `\stcited` has a `\lit` pointer on the same line or the next one.
- `prop:s03-phieis`: the statement matches the stage tex. The added `q∤M` is already implicit in `\Uzero M` (Def. s01-levels requires `(N,D)=1`). Step (1) is proved in full (Lemmas nbr, stabfree (i)–(vii)): finiteness of `Γ_x`, `Nrd γ=1`, `t∈{-1,0,1}`, `Z[γ]∈{Z[i],Z[ω]}` Euclidean, the transport `(*)` to `Z_ℓ[γ]` (valid for every ℓ, including 2 and 3), `L_x` free of rank 1, the fixed sublattice `= πL_x`, and the globalisation `hU=πxU` with the left `B^×`-class convention. Remark eis-ideals correctly translates this into right `R`-ideals and `Γ_e=O_L(I)^×`. Steps (2)–(4) correctly use the identity `N_g(x,y)|Γ_y|=N_{g^{-1}}(y,x)|Γ_x|` from the proof of Prop. s01-adjoint(a), together with (b), `S_ℓ=1` and the `z_ℓ=ℓ·c` argument. The transpose action, the `y_e` computation and `Σy_e=0` all check.
- `prop:s03-LRdef`: the local facts at q (`U'=U∩αUα^{-1}`, `U'_α=U∩α^{-1}Uα`, the coset decompositions) are consistent with Def. s02-BG, (C1) and (C3). The adjoint formula, including the orbit and stabiliser count `m=[Γ_x:Γ'_z]`, integrality, the degree computation for `α^†`, and all four entries check. The (1,2) entry is `T_{α^{-1}}=T_q^†=T_q` at `U_0(M)`. The comparison `ε δδ^† ε` with Ribet's δ is correct.
- External check (B_11, q=2): the section states the module precisely. The matrix identity is stated on `(Z[X]^0)^2` (and, correctly, on `Z[X]^2`). The determinant is placed in `Z[T_q] ⊆ End(Z[X]^0)`. No cokernel or order claim is made on the full module, so there is no finding.

## Defects

- **A0.1** · minor · `2-eisenstein.tex:118-125, 184-196`
  - Problem: `rem:s03-eis-cases` and `rem:s03-eis-corr` carry no status macro. Brief §3 says "every result carries a status macro". `rem:s03-eis-cases` also asserts, with no reference, that for `q∈{2,3}`, `M=1` the groups `Γ_x` are non-abelian of order 24 resp. 12.
  - Fix: add `\stproved{}` (or the appropriate status) to both remarks, and point the order and non-abelian claim to Prop. s01-finite / `\lit{voight_2021_quaternion-algebras}{Thm. 11.5.14, p. 176}`.
- **A0.2** · minor · `2-eisenstein.tex:275` (versus line 17)
  - Problem: "its matrix is `W^{-1}B_q^T W`" is right only if `B_q` is the matrix of `T_q` in the column convention. Line 17 defines the Brandt matrix in the row convention `T[e]=Σ B(e,e')[e']`. In that convention the weighted adjoint has matrix `W B_q^T W^{-1}`. The error has no effect on the result, since both equal `T_q` at `U_0(M)`, but the formula is ambiguous as written.
  - Fix: state the convention, or write `W B_q^T W^{-1}` with `B_q(e,e')` as in line 17.
- **A0.3** · minor · `2-eisenstein.tex:89-90`
  - Problem: Lemma nbr(b) is cited "with `h=x`". Its last clause is stated for neighbours `h=xk` as in (a), and `x` is not a neighbour of itself.
  - Fix: drop the citation and keep only the direct argument (`x_ℓ^{-1}γx_ℓ∈K` ⇒ `γL_x=L_x`).
- **A0.4** · minor · `2-eisenstein.tex:151-154`
  - Problem: the stage-tex cross-reference sentence "The geometric analogue for `Φ_{N,p}` is [Ed91, Th. 1] `\stcited`, which assumes p>3" has been dropped from `prop:s03-phieis` without comment. It is not needed for the proof, but it is an unannounced change to the stage-tex text.
  - Fix: restore it with a `\lit` pointer, or record the omission in `rem:s03-eis-corr`.
- **A0.5** · minor · `2-eisenstein.tex:195`
  - Problem: the author declares that the stage tex's "not yet re-read by a second reader" status is "superseded by the proof written out here". An independent re-read cannot be certified by the author of the text.
  - Fix: rephrase, e.g. "the proof is written out in full here; second reading: this audit".

Counts: critical 0, major 0, minor 5.

## Rubric

- correctness 4/4: every statement and proof step checks against the stage tex and the merged s01/s02/s03 chapters; the statements of both labelled propositions match the stage tex exactly.
- completeness 2/2: both outputs are present, both propositions have full proofs (step (1) without downgrade), all labels exist and there is no stub.
- interface fidelity 2/2: the section header, labels, planned Lean names (`\leanplanned`), `\lit` pointers, the (C1) sign convention and the module for `αα^†` are exactly as in the brief and stage tex.
- maintainability 1/2: clear and well cross-referenced, but has status-macro gaps (A0.1), a convention ambiguity (A0.2), a misapplied lemma citation (A0.3) and self-certifying status prose (A0.5).

Q = 9

W = 3·0 + 2·0 + 5 = 5

VERDICT: PASS
