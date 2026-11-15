<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Audit of strand A, S03-M2, round 0

Scope: `strand-A.patch` (new `mathematics/chapters/s03/2-eisenstein.tex`, 317 lines; new `mathematics/bib/s03-m2.bib`, comment only).
Line numbers below are lines of `mathematics/chapters/s03/2-eisenstein.tex` as created by the patch.
The acceptance check (`check.txt`) exits 0. The patch touches only the two allowed files. It contains no `\sorry`-type placeholder or unproved
claim marked `\stproved`.

Checked in detail, no defect found:
- Lemma `lem:s03-stabfree` (a)–(d), Steps 1–6. Step 1: finite order, n in {3,4,6}, Z[gamma] is the full ring of integers and a PID, so Z_ell[gamma]
  is maximal for every ell, including ell = 2, 3. Step 2: the coset/lattice dictionary at ell, and gamma-stability of Lambda'. Step 3: Lambda_0 is
  free of rank one over O_ell through the idempotent decomposition, with the non-scalar hypothesis made explicit. Step 4: Lambda' = pi Lambda_0, with
  the inert, split and ramified cases right. Step 5: local-to-global, using the units argument at v != ell. Step 6: the class. (d): free orbits.
  Left/right conventions (Rem. `rem:s03-phieis-notes`(a)) are consistent with `def:s01-classset`.
- Lemma `lem:s03-eisabs`: abstract steps (2)–(4) on the model of `prop:s03-phi`. Step (2) of `prop:s03-phieis` is derived from
  `prop:s01-adjoint`(a) together with the last clause of (b). The central-idele computation for T_{varpi^{-1}} = T_varpi is correct.
- Example B_11, ell = 2: B_2 = [[1,2],[3,0]], w = (2,3). I checked this independently against Phi_2 mod 11: j = 1728 gives one loop and two
  edges to j = 0, and j = 0 gives three edges to 1728. Symmetry, off-diagonal divisibility and (T_2 - 3)phi in W Z[E]^0 all hold.
- Lemma `lem:s03-transfer`: adjoint formula, index interpretation via (C3) (-1 in U' iff -1 in U), the fibre/orbit count, and
  U''_q = alpha^{-1} Iw_q alpha = w Iw_q w^{-1}, so [U:U''] = q+1.
- `prop:s03-LRdef`: the identifications (U' = U ∩ alpha U alpha^{-1}, s_0[y] = [y], s_1[y] = [y alpha], first component type 0) agree with
  `def:s02-BG` and with (C1)/(C3) of `4-ihara.tex`. The signs of alpha alpha^dagger are correct, T_q = s_{1*}s_0^dagger = s_{0*}s_1^dagger, and so is
  det. Remark (d) checks out: on Z([e_1]-[e_2]) T_2 = -2, so the matrix is [[3,2],[2,3]] with det 5.
- External check: the section never claims a cokernel or an integer determinant on the full module Z[X_B U]^2. The only numerical determinant (5)
  is stated on (Z[X_B U]^0)^2, which matches the code track. See A0.1 for the remaining imprecision.
- The statement of `prop:s03-phieis` agrees verbatim with the stage tex. All four planned Lean names appear with `\leanplanned`. All required labels
  appear exactly once. New labels have the `s03-` prefix.

## Defects

**A0.1 — minor — 2-eisenstein.tex:260–264 (statement of `prop:s03-LRdef`)**
Problem: the statement attaches `det=(q+1)^2-T_q^2` to both modules, "on Z[X_B U]^2 and on (Z[X_B U]^0)^2". It is correct as a determinant with
commuting entries, which the text defines. But nothing warns that on the full module the operator (q+1)^2 - T_q^2 has a kernel: T_q has the
eigenvalue q+1 on the Eisenstein vector. So the Z-determinant there is 0, and the cokernel is infinite. For B_11, q = 2 the code track finds
coker = Z ⊕ Z/3. The equality |coker(alpha alpha^dagger)| = |det| holds only on the degree-0 part.
Fix: add one sentence. The order of the cokernel / integer determinant is meant on (Z[X_B U]^0)^2 only, and on Z[X_B U]^2 the determinant is 0
(B_11, q = 2: coker = Z ⊕ Z/3 versus Z/5 on degree 0). Make Rem. (d), line 311–313, refer explicitly to that sentence.

**A0.2 — minor — 2-eisenstein.tex:197–203 (Example after `prop:s03-phieis`)**
Problem: the example has status `\stpmc` and relies on "the weights of Example `ex:s03-mazur`". That table is itself `\stsketch` (hand-derived,
pending T1). Connectedness of BG(Ô^×,2) for B_11 is credited to `prop:s02-BG` plus `thm:s02-SA`. But `prop:s02-BG` (ii) also needs surjectivity of
X^1(U) → X_B(U), which is not mentioned.
Fix: give the example status `\stsketch` (or "proved modulo T1"). Name condition (ii) of `prop:s02-BG` in full, including the surjectivity of
Nrd/X^1 for U = Ô^×.

**A0.3 — minor — 2-eisenstein.tex:308 (Rem. `rem:s03-LRnotes`(c))**
Problem: "s_j^dagger is the transfer pi^! of Prop. `s01-adjoint`(c)" is literally true only for j = 0. s_1 is not the projection X_B(U') → X_B(U)
with U' ≤ U. s_1^dagger is pi^! for U'' ⊂ U followed by the translation [z] ↦ [z alpha^{-1}], as in Lemma `lem:s03-transfer`(b).
Fix: say "for j = 0; for j = 1 composed with rho_{alpha^{-1}}, Lemma `lem:s03-transfer`(b)".

**A0.4 — minor — 2-eisenstein.tex:4 (header comment)**
Problem: the list of new labels omits `eq:s03-lattice`, defined at line 64.
Fix: add it to the list.

Counts: critical 0, major 0, minor 4.

## Rubric

- correctness: 4. Every step of `lem:s03-stabfree`, `lem:s03-eisabs`, `lem:s03-transfer` and both propositions checks, and the statements match the
  stage tex. A0.1–A0.3 are wording or status imprecisions, not mathematical errors.
- completeness: 2. Both outputs are present, steps (1)–(4) and `prop:s03-LRdef` are fully proved, all labels and status macros are there, and the bib
  file exists.
- interface fidelity: 2. Labels, section header, Lean names, `\leanplanned` and the `\lit` pointers are exactly as in the brief. The
  identifications for alpha alpha^dagger are stated and located in the chapter.
- maintainability: 2. The structure is clear (quaternionic lemma, abstract lemma, instantiation), uses only preamble macros, and gives precise
  cross-references. A0.4 is cosmetic.

Q = 10.

VERDICT: PASS
W = 3*0 + 2*0 + 4 = 4
