<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Audit S03-M2, strand D, round 1

Scope: `strand-D.patch` (new `mathematics/chapters/s03/2-eisenstein.tex`, 287 lines; new `mathematics/bib/s03-m2.bib`, one comment line).
Line numbers refer to `2-eisenstein.tex` as created by the patch.

## Prior findings (round 0)

| id | status | evidence |
|---|---|---|
| A0.1 | RESOLVED | `rem:s03-eis-cases` now has `\stcited{}` + `\lit{voight_2021_quaternion-algebras}{Thm. 11.5.14, p. 176}` for the group orders and `\stproved{}` for the rest (l. 125-126). `rem:s03-eis-corr` ends with `\stproved{}` (l. 199). |
| A0.2 | RESOLVED | l. 278-280: the row convention is stated, and the formula `T_q^†[x]=Σ_y (W B_q^T W^{-1})(x,y)[y] = Σ_y w_x B_q(y,x) w_y^{-1}[y]` was checked against `⟨T x,y⟩ = B(x,y)w_y`. It is correct. |
| A0.3 | RESOLVED | l. 89-90: the citation of Lemma nbr(b) with `h=x` is gone. The direct argument `x_ℓ^{-1}γx_ℓ∈K ⇒ γL_x=L_x` is used instead. |
| A0.4 | RESOLVED | l. 156-157: the Edixhoven sentence is restored ("assumes p>3", `\stcited` + `\lit{asterisque_1991_...}{Edixhoven, Théorème 1, pp. 159-170}`). This matches `references.bib` key `Ed91`. |
| A0.5 | RESOLVED | l. 198-199: "the second reading is the independent audit of this section, not this text." |

No regressions.

## Checks performed on the new diff (no defects found)

- **Acceptance check** (`check.txt`, commit f01aec5): exit code 0. The only warnings are the five pdfTeX `dest theorem.N.M` warnings, which round 0 traced to the base tree.
- **Files, labels, macros, status lines:**
  - Only the two allowed files are touched.
  - `ss:s03-eisenstein`, `prop:s03-phieis` and `prop:s03-LRdef` are each defined once.
  - The new labels have the `s03-` prefix and are unique.
  - There is no new global macro.
  - Planned Lean names use `\leanplanned`, never `\lean{}`.
- **Step (1), Lemmas nbr and stabfree.** Re-checked line by line:
  - (i): finiteness, `Nrd γ=1`, `t∈{-1,0,1}`, and `t=±2 ⇒ γ=±1`.
  - (ii): `ω=±γ` for `t=∓1`. Euclidean covering radii ½ and ⅓. `[A:βA]=Nrd β`.
  - (iii): the isomorphism `A/ℓ^mA ≅ O/ℓ^mO` and the statement `(*)`, valid for every ℓ, including 2 and 3.
  - (iv): `L_x=Ov` via a non-eigenvector `v_0`.
  - (v): `L_h=πL_x`.
  - (vi): the place-by-place check `h^{-1}πx∈U`, using `π^{-1}=π̄/ℓ` and the left-`B^×` class convention.
  - (vii): the free-orbit count.
  - Rem. eis-cases: the split/inert/ramified count is correct, i.e. the number of roots of `X²-tX+1` mod ℓ, with the examples given.
  - Rem. eis-ideals: the translation to right `R`-ideals and `Γ_e=O_L(I)^×` is correct.
- **Steps (2)-(4).**
  - Step (2) checked against the `s01/3-brandt.tex` proof of Prop. s01-adjoint(a), the identity `N_g(x,y)|Γ_y|=N_{g^{-1}}(y,x)|Γ_x|` divided by ε=2, and (b) with `z_ℓ=ℓ·c`.
  - Steps (3)-(4) checked against Prop. s03-phi: `Hom(X,Z)=Z^E/Z1`, `ι(x)=[Wx]`, the transpose action, `(T^∨-(ℓ+1))φ=Wy`, and `Σy_e=0`.
- **`prop:s03-LRdef`.**
  - (0): the local facts at q match Def. s01-levels, Def. s02-BG and (C3), with `U'=U∩αUα^{-1}`, `U'_α=α^{-1}U'α=U∩α^{-1}Uα`, and the coset decompositions of `UαU` and `Uα^{-1}U`.
  - (1)-(2): the adjoint computation (orbit `Γ_x·u_0U'_j`, stabiliser `Γ'_z`, `w'_z m = w_x`) is correct, as is the independence of the representative.
  - (3): `α^†=(-s_0^†,s_1^†)` and its degree are correct.
  - (4): all four entries are correct. `T_{α^{-1}}=T_q` via `z_q=q·c`.
  - The comparison `εδδ^†ε` is correct.
- **External check (B_11, q=2).** The identity is stated on `(Z[X]^0)^2` (and also on `Z[X]^2`), and the determinant is placed in `Z[T_q]⊆End(Z[X]^0)`. No cokernel or order claim is made on the full module, so it is consistent with the code-track finding (`Z ⊕ Z/3` on all of `Z[X]^2`, order 5 on the degree-0 part). No finding.

## Defects

- **A1.1** · minor · `2-eisenstein.tex:130-131`
  - Problem: `\lit{voight_2021_quaternion-algebras}{Thm.~9.4.9}` has no page. Also, Thm. 9.4.9 is the local–global dictionary for *localisations* `R_(p)`, but the remark uses completions `(I_x)_v=x_vR_v`. The completion form needs Lemma 9.5.3 together with Thm. 9.4.9 (Voight, pp. 145-147).
  - Fix: write `\lit{voight_2021_quaternion-algebras}{Thm.~9.4.9, p.~145, with Lemma~9.5.3, p.~146}` (or the equivalent pages).
- **A1.2** · minor · `2-eisenstein.tex:156`
  - Problem: "[Ed91, Th.~1] \cite{Ed91}" typesets the citation twice. It is also the only `\cite` in chapters s01/s03, whose convention is `\lit` pointers alone (brief §3: "prefer ... `\lit` pointers (not bibliography entries)").
  - Fix: drop either the hand-written "[Ed91, Th.~1]" (use `\cite[Th.~1]{Ed91}`) or the `\cite`.
- **A1.3** · minor · `2-eisenstein.tex:92` (versus l. 12 and l. 174)
  - Problem: notation clashes. `K_ℓ:=Q_ℓ+Q_ℓγ`, an algebra that is a field or `Q_ℓ×Q_ℓ`, is introduced next to `K=GL_2(Z_ℓ)`. `\phi` (the map `a↦av_0`) is used next to `\varphi` (functionals in step (3)). Both hurt readability.
  - Fix: rename, e.g. `F_γ:=Q_ℓ(γ)` and `ψ:F_γ→Q_ℓ^2`.

Counts: critical 0, major 0, minor 3.

## Rubric

- correctness 4/4: every step of step (1) through (4) and of the `αα^†` computation re-checks; both statements match the stage tex (only the documented proved upgrade of LRdef's status and the explicit `T_q^†` form are added).
- completeness 2/2: both outputs are present; there are full proofs with no downgrade, no stubs, and all labels.
- interface fidelity 2/2: the header, labels, planned Lean names, `\lit` pointers of the stage tex, the (C1) sign convention and the module for `αα^†` are all as in the brief.
- maintainability 1/2: well structured and cross-referenced, but has a citation-pointer gap (A1.1), a double citation (A1.2) and notation clashes (A1.3).

Q = 9

W = 3·0 + 2·0 + 3 = 3

VERDICT: PASS
