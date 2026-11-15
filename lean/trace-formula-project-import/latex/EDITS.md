# EDITS.md: changes of the fork's LaTeX against the parent (trace_formula_gl2 @ 84818d0)

Owner: T-A (shared/, items/, readable/). T-B records B-side changes in its own notes; B must mirror the A structure below.
Every item snippet in `items/` is a byte copy of the parent's `tex/items/<same path>` unless listed in §1.

## 1. Statement edits (snippets of kept items)
Only deletions of references to dropped items (rule of the fork brief). Old text = parent snippet at 84818d0.

| ID | edit | reason |
|---|---|---|
| `I.quot.def:automorphic-right-action` | deleted the clause "and for every left Haar measure $\mu$ on $G(\A)$ the measure of \cref{I.quot.def:automorphic-quotient-measure} is invariant under it: $\vol(E\cdot g)=\vol(E)$ for every Borel set $E\subseteq G(\Q)\backslash G(\A)^1$ and every $g\in G(\A)^1$" | refers to the dropped `I.quot.def:automorphic-quotient-measure` (Lean: `automorphicQuotientMeasure_invariant` dropped by L-B) |

## 2. Proofs replaced or rewritten (dropped analytic inputs)

| item / place | change |
|---|---|
| `I.quot.thm:automorphic-quotient-second-countable` (proof) | the pointer "(proof of the claims of `X.quot.def:quotient-measure`)" replaced by the three-line standard argument (open quotient map, closed subgroup) |
| `I.quot.def:automorphic-right-action` (proof of the claims) | the measure-invariance paragraph removed (claim deleted from the statement, §1); continuity kept (L-B keeps `I.quot.lem:automorphic-right-action-continuous-instance`) |
| `I.adele.thm:adele-fundamental-domain` (proof) | `I.lf.def:fractional-part` (dropped by L-A) replaced by an inline definition of the $p$-adic fractional part $\{y\}_p$ via digits; argument unchanged |
| `I.adele.thm:zhat-characters-finite-order` (proof) | "$\Zhat=\Z+N\Zhat$ ... (proof of `I.adele.lem:reduction-to-indicators`)" replaced by the one-line CRT argument |
| `I.topgrp.thm:sl2-strong-approximation` (proof, Step 1) | same replacement ("$\Zhat=\Z+a\Zhat$", CRT inline) |
| `I.adele.def:idele-norm` (proof of the claims) | "by the argument for $\psi$ in `I.adele.def:standard-character`" replaced by "a homomorphism continuous on an open subgroup is continuous" |
| `I.satake.thm:satake-transform-multiplicative` (proof) | linearity was cited from the dropped `I.satake.thm:satake-transform-well-defined`(a); now stated inline (finite sum, linear summands) |
| `I.satake.thm:satake-isomorphism` (proof `\uses`) | the dropped `I.satake.thm:satake-transform-well-defined` removed from its `\uses` (the text did not use it) |
| `X.topgrp.thm:restricted-product-second-countable` | kept verbatim (statement and proof) in the trimmed `vol1/ch-0-06-haar`, §`sec:haar-adelic` |

## 0. Structure of A (B mirrors it; generated from `readable/algjl.tex`)
Master: `readable/algjl.tex` (job name `algjl`), built by `latex/build.sh A` into `latex/build/A/algjl.pdf`. The notation table is input
at the end of `ch-0-01-conventions` (as in the parent); the hypothesis registry is the last appendix chapter `ch:hypotheses`.

- `readable/ch-intro.tex` `ch:intro`: Introduction (unnumbered; new text of the fork, no items)
- **Part I:** The split group GL2 over Q: algebraic prerequisites
- `readable/vol1/ch-0-01-conventions.tex` `ch:ch-0-01-conventions`: Conventions and the algebraic groups
  - `sec:conv-subgroups` (8 A items): \texorpdfstring{The group $\GL_2$ and its standard subgroups}{The group GL₂ and its standard subgroups}
  - `sec:conv-structure` (4 A items): \texorpdfstring{Structure of $B$ and of $N_G(T)$}{Structure of B and of NG(T)}
  - `sec:conv-max-compact` (4 A items): Local maximal compact subgroups
  - `sec:conv-aB` (4 A items): \texorpdfstring{The space $\aB$, roots and chambers}{The space 𝔞B, roots and chambers}
- `readable/vol1/ch-0-02-local-field.tex` `ch:ch-0-02-local-field`: Non-archimedean local fields
  - `sec:lf-interface` (6 A items): \texorpdfstring{The interface \texttt{NALF}}{The interface NALF}
  - `sec:lf-abs-haar` (4 A items): The normalized absolute value
- `readable/vol1/ch-0-03-adeles.tex` `ch:ch-0-03-adeles`: \texorpdfstring{Adeles and ideles of $\Q$}{Adeles and ideles of ℚ}
  - `sec:adele-ring` (9 A items): The adele ring
  - `sec:adele-ideles` (6 A items): Ideles
  - `sec:adele-characters` (2 A items): \texorpdfstring{Characters of $\Zhat^\times$ and Hecke characters}{Characters of Ẑ× and Hecke characters}
- `readable/vol1/ch-0-04-top-groups.tex` `ch:ch-0-04-top-groups`: \texorpdfstring{$\GL_2$ as a topological group, locally and adelically}{GL₂ as a topological group, locally and adelically}
  - `sec:topgrp-field` (3 A items): \texorpdfstring{$\GL_2$ over a topological field}{GL₂ over a topological field}
  - `sec:topgrp-nalf` (2 A items): \texorpdfstring{$\GL_2$ over a non-archimedean local field}{GL₂ over a non-archimedean local field}
  - `sec:topgrp-real` (2 A items): \texorpdfstring{$\GL_2(\R)$}{GL₂(ℝ)}
  - `sec:topgrp-adelic` (8 A items): \texorpdfstring{Adelic $\GL_2$}{Adelic GL₂}
  - `sec:topgrp-norm-one` (3 A items): \texorpdfstring{$G(\A)^1$ and $A_G^+$}{G(𝔸)¹ and AG⁺}
  - `sec:topgrp-strong-approx` (5 A items): Strong approximation
- `readable/vol1/ch-0-05-decompositions.tex` `ch:ch-0-05-decompositions`: Bruhat, Iwasawa and Cartan decompositions
  - `sec:decomp-bruhat` (2 A items): Bruhat decomposition
  - `sec:decomp-iwasawa` (6 A items): Iwasawa decomposition and the height map
  - `sec:cartan` (6 A items): Cartan decomposition
- `readable/vol1/ch-0-06-haar.tex` `ch:ch-0-06-haar`: Local compactness and restricted products (trimmed; prose + 1 A item; home of the B-only
  items I.haar.* (instances, borel-coordinates), X.haar.* boxes, X.topgrp.* restricted-product items, I.topgrp.def:{matrix-pair,gl2-pair,gl2-product-equiv})
  - `sec:haar-local` (0 A items): Topological facts on GL2(F) and GL2(R)
  - `sec:haar-adelic` (1 A item): Restricted products
- `readable/vol1/ch-0-07-quotient.tex` `ch:ch-0-07-quotient`: Discrete subgroups and compact quotients
  - `sec:quot-compact` (1 A items): \texorpdfstring{The compact quotient $T(\Q)\backslash T(\A)^1$}{The compact quotient T(Q)\textbackslash T(A)1}
  - `sec:quot-automorphic` (2 A items): The automorphic quotient
- `readable/vol1/ch-0-08-reduction.tex` `ch:ch-0-08-reduction`: Reduction theory
  - `sec:red-siegel` (5 A items): Siegel sets
  - `sec:red-height` (5 A items): The height lemma and the compactness criterion
- `readable/vol1/ch-0-10-reps.tex` `ch:ch-0-10-reps`: Smooth and admissible representations
  - `sec:rep-smooth` (2 A items): Smooth and admissible representations
- `readable/vol1/ch-1-01-spherical.tex` `ch:ch-1-01-spherical`: The spherical Hecke algebra and the Satake isomorphism
  - `sec:satake-gelfand` (3 A items): The spherical Hecke algebra and Gelfand's trick
  - `sec:satake-basis` (7 A items): The Hecke basis and the Hecke recursion
  - `sec:satake-iso` (8 A items): The Satake isomorphism
  - `sec:satake-characters` (1 A items): Characters of the spherical Hecke algebra
- `readable/vol1/ch-1-02-smooth.tex` `ch:ch-1-02-smooth`: \texorpdfstring{Smooth representations of $\GL_2$ over a non-archimedean local field}{Smooth representations of GL₂ over a non-archimedean local field}
  - `sec:smooth-principal-series` (6 A items): Quasi-characters and the principal series
  - `sec:smooth-spherical` (4 A items): Spherical vectors and the spherical Hecke algebra
  - `sec:smooth-jacquet` (5 A items): The Jacquet module and Frobenius reciprocity
- `readable/vol2/ch-02-parabolic.tex` `ch:ch-02-parabolic`: Parabolic subgroups of \texorpdfstring{$\GL(2)$}{GL(2)}
  - `sec:par-heights` (3 A items): Parabolic subgroups and heights
  - `sec:par-families` (1 A items): \texorpdfstring{The functions $\theta_P$}{The functions θP}
- `readable/vol2/ch-03-kernel.tex` `ch:ch-03-kernel`: Geometric conjugacy classes
  - `sec:kernel-classes` (4 A items): Geometric classes
- `readable/vol2/ch-04-orbital.tex` `ch:ch-04-orbital`: Elliptic elements and their centralizers
  - `sec:orb-centralizer` (10 A items): Elliptic elements and their centralizers
  - `sec:orb-compact` (6 A items): Compactness of elliptic centralizers
- `readable/vol2/ch-06-truncation.tex` `ch:ch-06-truncation`: \texorpdfstring{The point $T_0$ and sums over $B(\Q)\backslash G(\Q)$}{The point T0 and sums over B(Q)\textbackslash G(Q)}
  - `sec:trunc-t-zero` (3 A items): The point \texorpdfstring{$T_0$}{T0} and the chamber functions
  - `sec:trunc-cosets` (3 A items): Sums over \texorpdfstring{$B(\Q)\backslash G(\Q)$}{B(Q)\textbackslash G(Q)}
- **Part II:** Definite quaternion algebras over Q
- `readable/vol3/ch-iii-06-quatalg.tex` `ch:ch-iii-06-quatalg`: Quaternion algebras over $\Q$
  - `sec:qalg-basic` (8 A items): Quaternion algebras, reduced norm and trace
  - `sec:qalg-hilbert` (8 A items): The Hilbert symbol and ramification
  - `sec:qalg-local` (5 A items): Local structure
- `readable/vol3/ch-iii-07-orders.tex` `ch:ch-iii-07-orders`: Orders, class sets and the mass
  - `sec:qord-orders` (8 A items): Orders and discriminants
  - `sec:qord-eichler` (6 A items): Level structures, Eichler orders and units
  - `sec:qcls-adelic` (4 A items): The finite-adelic algebra and the local--global principle
  - `sec:qcls-classes` (9 A items): Class sets
  - `sec:qcls-mass` (6 A items): The mass
  - `sec:qcls-compact` (3 A items): The adelic group and compactness
  - `sec:qcls-instances` (4 A items): Instances
- `readable/vol3/ch-iii-08-brandt.tex` `ch:ch-iii-08-brandt`: Quaternionic forms, Hecke operators and Brandt matrices
  - `sec:qform-coefficients` (12 A items): Coefficient modules
  - `sec:qform-forms` (9 A items): Quaternionic forms and the weighted pairing
  - `sec:brandt-hecke` (17 A items): Hecke operators
  - `sec:brandt-brandt` (6 A items): Brandt matrices
  - `sec:brandt-instances` (4 A items): Instances
- **appendix**
- `readable/vol3/ch-iii-01-explicit.tex` `ch:ch-iii-01-explicit`: Explicit formulas and local factors
  - `sec:ef-arith` (4 A items): Arithmetic functions and signed divisor sums
  - `sec:ef-discr` (6 A items): Discriminants, class numbers of forms, and the polynomials \texorpdfstring{$P_k$}{P\_k}
  - `sec:ef-local` (5 A items): The Kronecker symbol, the Eichler symbol and the local factors
  - `sec:ef-cohen` (5 A items): Cohen's root count and Eichler's sum form
  - `sec:ef-boundary` (6 A items): The boundary sum and the Eisenstein expression
  - `sec:ef-expressions` (9 A items): Cohen's expression, Eichler's expressions and the Lefschetz expression
  - `sec:ef-identity` (5 A items): The formula-level Jacquet--Langlands identity
  - `sec:ef-identity-general` (11 A items): The identity with general parameters

Parent chapters not included at all: Vol. I ch-0-09 (Hecke algebras by convolution), ch-0-11, ch-1-03..1-05, all ch-2-*;
Vol. II ch-01, ch-05, ch-07..ch-13; the x/ fixture chapter.

## 3. Dropped items and sections (A), per chapter
Chapter files keep the parent's names. Items "added" were moved in from a dropped chapter.

- `vol1/ch-0-01-conventions.tex`: verbatim except prose edits listed in §4
- `vol1/ch-0-02-local-field.tex`: sections dropped: `sec:lf-fourier`; items dropped (14): `I.lf.def:additive-haar`, `I.lf.thm:haar-scaling`, `I.lf.thm:vol-ideal-power`, `I.lf.thm:haar-modulus-linear`, `I.lf.def:multiplicative-haar`, `I.lf.thm:vol-units`, `I.lf.def:fractional-part`, `I.lf.def:standard-character`, `I.lf.thm:standard-character-conductor`, `I.lf.def:schwartz-bruhat`, `I.lf.thm:schwartz-bruhat-span`, `I.lf.def:fourier-transform`, `I.lf.thm:fourier-indicator`, `I.lf.thm:fourier-inversion`
- `vol1/ch-0-03-adeles.tex`: title changed (parent: "\texorpdfstring{Adeles and ideles of $\Q$; Tate's thesis over $\Q$}{Adeles and ideles of ℚ; Tate's thesis over ℚ}"); sections dropped: `sec:adele-poisson`, `sec:adele-tate`; items dropped (26): `I.adele.def:adele-haar`, `I.adele.thm:rat-quotient-compact`, `I.adele.def:standard-character`, `I.adele.thm:character-trivial-on-rat`, `I.adele.def:schwartz-bruhat`, `I.adele.lem:reduction-to-indicators`, `I.adele.def:fourier-transform`, `I.adele.thm:fourier-inversion`, `I.adele.thm:poisson-summation`, `I.adele.def:idele-haar`, `I.adele.def:dirichlet-pair`, `I.adele.thm:l2-norm-one-quotient`, `I.adele.thm:l2-torus-quotient`, `I.adele.thm:hecke-character-classification`, `I.adele.lem:fourier-dilation`, `I.adele.def:hecke-character-exponent`, `I.adele.lem:idele-haar-decomposition`, `I.adele.def:zeta-integral`, `I.adele.def:theta-function`, `I.adele.lem:theta-decay`, `I.adele.thm:zeta-integral-converges`, `I.adele.lem:theta-functional-equation`, `I.adele.def:zeta-continued`, `I.adele.thm:zeta-integral-continuation`, `I.adele.thm:zeta-functional-equation`, `I.adele.thm:zeta-integral-poles`
- `vol1/ch-0-04-top-groups.tex`: verbatim except prose edits listed in §4
- `vol1/ch-0-05-decompositions.tex`: items dropped (1): `I.decomp.thm:iwasawa-real-smooth`
- `vol1/ch-0-06-haar.tex`: title changed (parent: "Haar measures on GL2(F), GL2(R), GL2(A)"); sections dropped: `sec:haar-unimodular`, `sec:haar-real`, `sec:haar-iwasawa`, integration formulas; all A items dropped except `X.topgrp.thm:restricted-product-second-countable`
- `vol1/ch-0-07-quotient.tex`: title changed (parent: "Quotient measures"); sections dropped: `sec:quot-discrete`, `sec:quot-iwasawa`, `sec:quot-weil`, `sec:quot-tower`, `sec:quot-volume`; items dropped (23): `X.quot.thm:exists-fundamental-domain`, `X.quot.def:quotient-measure`, `X.quot.thm:unfolding-discrete`, `X.quot.thm:quotient-measure-invariant`, `X.quot.thm:compact-quotient-volume`, `I.quot.thm:unipotent-quotient-volume`, `I.quot.thm:integration-borel-quotient`, `I.quot.thm:integration-unipotent-torus-quotient`, `I.quot.def:automorphic-quotient-measure`, `I.quot.def:l2-automorphic`, `I.quot.thm:l2-separable`, `X.quot.def:bruhat-function`, `X.quot.thm:bruhat-function-exists`, `X.quot.thm:weil-quotient-formula`, `X.quot.def:weil-measure`, `X.quot.thm:weil-quotient-formula-right`, `X.quot.thm:weil-measure-discrete`, `X.quot.thm:unfolding-subgroup`, `X.quot.thm:quotient-tower`, `I.quot.lem:modular-area`, `I.haar.lem:haar-real-upper-half-plane`, `I.quot.lem:standard-fundamental-domain`, `I.quot.thm:quotient-volume`
- `vol1/ch-0-08-reduction.tex`: sections dropped: `sec:red-volume`, `sec:red-finiteness`; items dropped (4): `I.red.thm:siegel-set-volume`, `I.red.thm:measurable-fundamental-domain`, `I.red.thm:finite-volume`, `I.red.thm:siegel-finiteness`
- `vol1/ch-0-10-reps.tex`: title changed (parent: "\texorpdfstring{Representations: smooth, admissible, unitary, $(\mathfrak{g},K)$}{Representations: smooth, admissible, unitary, (𝔤,K)}"); sections dropped: `sec:rep-unitary`, `sec:rep-gk`, `sec:rep-gk-adelic`; items dropped (40): `I.rep.def:smooth-hecke-action`, `I.rep.def:nondegenerate-module`, `I.rep.thm:smooth-hecke-module`, `I.rep.thm:smooth-hecke-module-equiv`, `I.rep.def:contragredient`, `I.rep.thm:contragredient-admissible`, `I.rep.thm:schur-lemma`, `I.rep.def:unitary-rep`, `I.rep.def:integrated-rep`, `I.rep.def:right-regular-rep`, `I.rep.thm:right-regular-unitary`, `I.rep.thm:right-regular-strongly-continuous`, `I.rep.def:dirac-sequence`, `I.rep.thm:dirac-sequence-exists`, `I.rep.thm:approximate-identity`, `I.rep.cor:approximate-identity-regular`, `I.rep.thm:integrated-rep-convolution`, `I.rep.thm:k-infinity-types-complete`, `I.rep.def:automorphic-regular-rep`, `I.rep.thm:automorphic-regular-unitary`, `I.rep.def:automorphic-test-function-action`, `I.rep.cor:nonzero-test-function-action`, `I.rep.def:k-finite`, `I.rep.def:weight-vector`, `I.rep.thm:k-finite-weight-decomposition`, `I.hecke.def:archimedean-test-functions`, `I.rep.def:lie-action`, `I.rep.thm:lie-action-exp`, `I.rep.thm:lie-action-bracket`, `I.rep.thm:lie-action-equivariant`, `I.rep.def:casimir`, `I.rep.thm:casimir-commutes`, `I.hecke.thm:smooth-dirac-sequence-real`, `I.rep.def:gk-module`, `I.rep.def:gk-admissible`, `I.rep.def:gk-irreducible`, `I.rep.def:gk-isomorphism`, `I.rep.def:gk-finite-adelic-module`, `I.rep.def:gk-adelic-irreducible`, `I.rep.def:gk-adelic-isomorphism`
- `vol1/ch-1-01-spherical.tex`: items dropped (2): `I.satake.thm:spherical-convolution-haar`, `I.satake.thm:satake-transform-well-defined`
- `vol1/ch-1-02-smooth.tex`: sections dropped: `sec:smooth-intertwining`; items dropped (8): `I.smooth.thm:spherical-hecke-action-algebra`, `I.smooth.thm:principal-series-jacquet`, `I.smooth.def:local-l-factor`, `I.smooth.lem:weyl-unipotent-iwasawa`, `I.smooth.def:intertwining-operator`, `I.smooth.thm:intertwining-converges`, `I.smooth.thm:intertwining-equivariant`, `I.smooth.thm:gindikin-karpelevich`
- `vol2/ch-02-parabolic.tex`: title changed (parent: "\texorpdfstring{Parabolic combinatorics and $(G,M)$-families for $\GL(2)$}{Parabolic combinatorics and (G,M)-families for GL(2)}"); items dropped (7): `II.par.def:gt-family`, `II.par.def:gt-family-value`, `II.par.thm:gt-family-derivative`, `II.par.def:weight`, `II.par.thm:weight-explicit`, `II.par.thm:weight-affine`, `II.par.thm:weight-invariant`
- `vol2/ch-03-kernel.tex`: title changed (parent: "The kernel and its decompositions"); sections dropped: `sec:kernel-kernel`, `sec:kernel-constant-term`, `sec:kernel-spectral`; items dropped (22): `II.kernel.def:kernel`, `II.kernel.thm:kernel-locally-finite`, `II.kernel.thm:integral-operator`, `II.kernel.def:class-kernel`, `II.kernel.thm:finitely-many-classes`, `II.kernel.thm:class-decomposition`, `II.kernel.thm:class-kernel-unfolding`, `II.kernel.def:constant-term-kernel`, `II.kernel.thm:constant-term-kernel-properties`, `II.kernel.def:class-constant-term-kernel`, `II.kernel.thm:constant-term-class-decomposition`, `II.kernel.lem:kernel-slice-schwartz-bruhat`, `II.kernel.thm:constant-term-kernel-poisson`, `II.kernel.def:cuspidal-datum`, `II.kernel.def:spectral-kernel`, `II.kernel.thm:finite-spectral-support`, `II.kernel.thm:spectral-decomposition`, `II.kernel.cor:spectral-decomposition-h1`, `II.kernel.thm:spectral-kernel-operator`, `II.kernel.def:datum-constant-term-kernel`, `II.kernel.thm:constant-term-spectral-decomposition`, `II.kernel.thm:spectral-kernel-invariance`
- `vol2/ch-04-orbital.tex`: title changed (parent: "Orbital integrals (local and global)"); sections dropped: `sec:orb-elliptic`, `sec:orb-hyperbolic`, `sec:orb-local`, `sec:orb-volume`; items dropped (29): `II.orb.lem:centralizer-unimodular`, `II.orb.thm:elliptic-volume-finite`, `II.orb.def:orbital-integral`, `II.orb.thm:elliptic-kernel-unfolding`, `II.orb.def:centralizer-haar-norm-one`, `II.orb.thm:elliptic-orbital-converges`, `II.orb.thm:hyperbolic-centralizer`, `II.orb.thm:torus-quotient-integration`, `II.orb.thm:hyperbolic-orbital-explicit`, `II.orb.def:weighted-orbital-integral`, `II.orb.thm:weighted-orbital-converges`, `II.orb.thm:weighted-orbital-affine`, `II.orb.def:local-orbital-integral`, `II.orb.thm:orbital-norm-one-comparison`, `II.orb.lem:local-orbit-proper`, `II.orb.lem:unramified-orbit-support`, `II.orb.thm:unramified-orbital-integral`, `II.orb.thm:orbital-factorization`, `II.orb.thm:elliptic-orbital-factorization`, `II.orb.def:local-weight`, `II.orb.def:local-weight-real`, `II.orb.def:local-weighted-orbital-integral`, `II.orb.lem:weight-local-sum`, `II.orb.thm:weighted-orbital-factorization`, `II.orb.def:torus-unit-subgroup`, `II.orb.def:standard-torus-measure`, `II.orb.lem:torus-idele-class-group`, `II.orb.thm:elliptic-volume-explicit`, `II.orb.ex:elliptic-volume-gaussian`
- `vol2/ch-06-truncation.tex`: title changed (parent: "Truncation"); sections dropped: `sec:trunc-partition`, `sec:trunc-operator`, `sec:trunc-l2`, `sec:trunc-decay`; items dropped (24): `II.trunc.def:compact-part`, `II.trunc.thm:compact-part-properties`, `II.trunc.thm:compact-part-positive`, `II.trunc.thm:partition-lemma`, `II.trunc.thm:compact-part-siegel`, `II.trunc.def:truncation`, `II.trunc.thm:truncation-well-defined`, `II.trunc.thm:truncation-explicit`, `II.trunc.thm:truncation-cuspidal`, `II.trunc.thm:truncation-regularity`, `II.trunc.thm:truncation-constant-term-vanishes`, `II.trunc.thm:truncation-idempotent`, `II.trunc.thm:truncation-equals-on-compact`, `II.trunc.ex:truncation-of-one`, `II.trunc.thm:cusp-region-unfolding`, `II.trunc.lem:constant-term-orthogonality`, `II.trunc.thm:truncation-self-adjoint`, `II.trunc.def:truncation-l2`, `II.trunc.thm:truncation-l2-projection`, `II.trunc.def:rapidly-decreasing`, `II.trunc.thm:nonconstant-part-decay`, `II.trunc.thm:truncation-rapid-decay-seminorm`, `II.trunc.thm:truncation-rapid-decay`, `II.trunc.cor:truncation-square-integrable`
- `vol3/ch-iii-06-quatalg.tex`: verbatim except prose edits listed in §4
- `vol3/ch-iii-07-orders.tex`: verbatim except prose edits listed in §4
- `vol3/ch-iii-08-brandt.tex`: verbatim except prose edits listed in §4
- `vol3/ch-iii-01-explicit.tex`: verbatim except prose edits listed in §4

Snippets in `items/`: exactly the kept IDs (KEPT_IDS/L-A.txt, L-B.txt, L-C.txt, plus the fork-new IDs of §6 in fork-new.txt; 526 files, including the B-only items that B needs). A typesets
a subset (the tf_id items of the kept chapters); every A item is a kept ID.

## 4. Prose edits (no statement content)
Overviews, scope lines, chapter/section titles and remarks that described dropped material were rewritten to say that the material is
in the parent and not part of this volume. Parent paths quoted in prose are explained in the introduction (they refer to the parent repo).
- `vol1/ch-0-01-conventions`: the cref to the dropped chapter ch-1-04-gl2r (weight characters) became a parenthetical remark.
- `vol1/ch-0-02-local-field`: §2 retitled ("Normalized absolute value and Haar measure" -> "The normalized absolute value"); the pointer
  to the parent's Haar chapter (`sec:haar-unimodular`) replaced by "standard facts on Haar measure from Mathlib" (D-d); "Volume~I" -> "Part~I".
- `vol1/ch-0-03-adeles`: title; sources of §3 (Dirichlet pairs removed); remark after `I.adele.def:hecke-character` (states the
  classification as a cited fact, \cite[§2.1]{GH}); (no moved item).
- `vol1/ch-0-07-quotient`: title ("Quotient measures" -> "Discrete subgroups and compact quotients"), chapter intro, §2/§4 titles,
  remark after `I.quot.thm:torus-quotient-compact` (no Dirichlet pairs, no L^2).
- `vol1/ch-0-06-haar`: trimmed chapter, new title and prose (all parent items except restricted-product-second-countable are measures or B-only).
- `vol1/ch-0-10-reps`: new trimmed chapter (parent ch-0-10-reps §1, two definitions); the van Dantzig remark is copied from the parent's
  ch-0-09-hecke §1 with the hypothesis "locally compact, Hausdorff, totally disconnected" stated in the remark; the remark after
  `I.rep.def:smooth-rep` states that hypothesis.
- `vol1/ch-1-01-spherical`: the comparison with Haar convolution and the Satake integral are stated as cited remarks (no item refs).
- `vol1/ch-1-02-smooth`: scope line; $\delta_B^{1/2}$ defined by its formula (no ref to `I.haar.def:modular-character-borel`);
  the comparison with the $C_c^\infty(G)$-action and the computation of the Jacquet module of the principal series as cited remarks.
- `vol2/ch-02-parabolic`, `ch-03-kernel`, `ch-04-orbital`, `ch-06-truncation`: titles, overviews/scope, section titles, sources
  lines; references to later parent chapters (Ch. 4, 5, 7, 8, 12, "§§3 ff.") removed or turned into "parent project" remarks;
  "Ch.~0.8" -> \cref{ch:ch-0-08-reduction}.
- `vol3/ch-iii-07-orders`: the sentence naming `II.cpt.thm:compact-trace-formula` reworded (manifest §5); "registry entry in
  tex/shared/hypotheses.tex" -> \cref{ch:hypotheses}.
- \uses lists: IDs of dropped items removed (after trimming, only `I.haar.def:modular-character-borel` in the \uses of
  `I.satake.def:satake-transform` remained; removed).

## 5. Shared files
- `shared/gl2tf.sty`: the two `\tf@import` calls (xr to `../../build/tex/*/vol1.aux`, `vol2.aux` for jobs vol2/vol3) removed; the
  `\emergencystretch=4em` that the parent sets for job `vol3` is set unconditionally; header line naming the fork. Everything else verbatim.
- `shared/hypotheses.tex`: only the entry `III.qcls.hyp:eichler-mass` (Hyp.EichlerMass) kept; intro sentence "of the project" -> "of this volume".
- `shared/notation.tex`: blocks kept: Groups and subgroups; Height map, roots, chambers; M7a (renamed "Parabolics and conjugacy classes",
  rows of Weil measures, spectral decompositions, $\HeckeTwo(G,\mu)$, $K_f$, $(G,T)$-families, weights, class kernels, orbital integrals and $\nu^1$
  removed); M9a (renamed "Cosets and the point $T_0$", rows $F^G$, $\Lambda^T$, $P^T$, $\mathcal B_{\mathrm{loc}}$, rapid decay removed); M5a (rows
  $M(w)$ and $L(s,\mu)$ removed); Vol. III Q1 and Q2 blocks verbatim. Dropped blocks: function spaces and operators; Lie algebra/Casimir; automorphic
  forms; simple trace formula; Eisenstein series; normalization of measures; spherical Eisenstein series; modified kernel; geometric expansion;
  truncated Eisenstein series; cuspidal data; fine spectral expansion.
- `shared/refs.bib`: verbatim copy (biblatex prints only cited entries).

## 6. Fork-new items (not in the parent)
| ID | Lean | where | note |
|---|---|---|---|
| `I.adele.thm:rat-quotient-compact-top` | `GL2TF.rat_quotient_compact_top` (`lean/AlgJL/VolI/P0/Adeles.lean`; tests `rat_quotient_univ_isCompact`, `rat_quotient_zero_isClosed` in `AlgJLTests/VolI/P0/Adeles.lean`) | A: `vol1/ch-0-03-adeles`, §`sec:adele-ring`, after `I.adele.thm:adele-fundamental-domain`, with proof and a remark pointing to `I.adele.thm:norm-one-quotient`; snippet `items/I/adele/thm--rat-quotient-compact-top.tex`; B: hand-written block in `backtranslation/tools/fork_new.tex`, inserted by `mkB.py` | measure-free replacement of the dropped `I.adele.thm:rat-quotient-compact` (2026-11-14): $\A/\Q$ is compact Hausdorff. Compactness proof taken from the parent's proof; the Hausdorff clause is new. No parent generated signature/hash/audit. ID recorded in `KEPT_IDS/fork-new.txt`. |
