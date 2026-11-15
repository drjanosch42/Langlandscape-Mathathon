# Coarse stage split of the seed plan

Source: `plan/seed/towards_simplicial_jl.tex` (frozen; cited below as **seed §n / label**).
This file is the only document a stage drafter needs besides the seed and the literature. Six stages follow the seed's
route: foundations, then tree quotients, then graphs/Ribet/Ihara, then Λ-adic. Stages 05 (comparison hypothesis) and
06 (defect) both sit on top of these. They were planned as independent; after the global Fable audit (F16, provisional)
05 imports Lemma D from 06 through `if:s06-lemD`, and 06 imports `if:s05-subquot` only as an optional cross-check.

```
01 quaternion-foundations ─► 02 tree-quotients ─► 03 ribet-ihara ─► 04 lambda-adic ─┬─► 05 comparison-hypothesis
          └──────────────────────────────(Hecke algebras, Brandt pairing)──────────────┴─► 06 integral-defect
```

## Shared conventions (all stages)

- **Ground field.** Everything is over **ℚ**. No number field F (seed §9 on several primes is the only place where general
  D appears). `B = B_D`: the definite quaternion algebra over ℚ ramified exactly at ∞ and the primes dividing D (squarefree,
  ω(D) odd). Macro `\Bd`. Write `B` when D is fixed. Use `B_q` for D = q (the DR case).
- **Primes.** `p ≥ 5`: the coefficient/Hida prime, with p ∤ D. `q ≠ p`: the tree prime, q ∤ D except in stage 05/06 where
  `B = B_q`. `ℓ`: an arbitrary Hecke prime. `M`: the tame level, with (M, pqD) = 1. Follow seed §2 exactly. Do not rename.
- **Levels.** `U ⊂ \hat B^×` compact open with Nrd(U) = \hat ℤ^×. The levels are `U_0(N)`, `U_1(N)`, the p-tower `U_s = U_1(Mp^s)`,
  `S_s = X_B(U_s)`, `Δ_s = (1+pℤ_p)/(1+p^sℤ_p)`, and the Iwahori `\Iw_q`, `U_0(q)U`. The class set is `X_B(U) = B^×\\hat B^×/U`
  and the stabiliser is `Γ_x = B^× ∩ xUx^{-1}`.
- **Weights.** `w_x = |Γ_x/(Γ_x ∩ {±1})|` is the default. Any statement that uses |Γ_x| instead must say so (this changes
  results by a factor 2; seed §2.4).
- **Brandt module.** `M(U;V)` (macro `\Brandt{U}{V}`) uses the cohomological convention `f(γxu) = u_p^{-1} f(x)`. Write
  `ℤ[X]` for the homological (pushforward) version and `ℤ^X` for the cohomological (pullback) one; `ℤ[X]^0` is the degree-zero
  part. `V_k = Sym^{k-2}(ℤ_p^2)`, with n = k−2.
- **Hecke.** Hecke operators are normalised classically. Every stage that uses `U_p` must state its normalisation. Fix the
  one that commutes with pushforward along `S_{s+1} → S_s` (seed §2.5). Stage 01 owns this choice.
- **Hida.** `Λ = O_E[[1+pℤ_p]]`, `P_k`, `e = lim U_p^{n!}`, and `η(S,μ) = μ(Ann_S ker μ)` (seed §2.6).
- **Status tags.** Use the macros from `preamble.tex`: `\stknown \stcited \sttoprove \stproved \stpmc \stsketch \stexp
  \stconj \sthyp \stopen \stcomp \stformal`, or the generic `\status{...}`. Every `\stcited` and `\stknown` carries
  `\lit{<file-stem>}{Thm/§/page}`.
- **Macros.** These are defined in `plan/staged/preamble.tex`; do not redefine them locally:
  `\Q \Z \R \C \F \A \Zp \Qp \Zq \Qq \Zhat \Qhat \cO \cOE \GL \SL \PGL \Nrd \Trd \Sym \JL \ord \Iw \Hb \Bd \Bhat \XB{U} \XBq{U}
  \Uzero{N} \Uone{N} \Brandt{U}{V} \Vk \GU \cT \G \GDR \Phicomb \Xcomb \cX \quot \T \m \Lam \cM \Mord \Xord \Tord \fa \fb \cc
  \tq \HypX \HypXchar \HypXgal \HypXiso \Hom \coker \End \Ann \rk \Stab \tr \Jac \Fitt \lit{}{}`.
  Environments: `theorem proposition lemma corollary conjecture definition hypothesis interface example testcase remark`.
- **Labels.** Prefix every label with the stage number, e.g. `thm:s03-ribet`, `def:s01-brandt`. Interfaces are labelled
  `if:sNN-<name>`. Cross-stage references use only the `if:` labels listed below.

## Stages

### 01 `quaternion-foundations` — Quaternionic foundations: class sets, Brandt modules, classical JL
- **Scope (in).** Seed §2 (notation) and §3 (targets): definite B over ℚ, maximal and Eichler orders, local structure,
  class sets X_B(U) and stabilisers, the Eichler mass formula, Brandt modules M(U;V) with V_k, Hecke operators (T_ℓ, S_ℓ,
  U_ℓ, diamonds, U_p, Π_ℓ for ℓ|D), the Brandt pairing, and statements of classical, p-adic (Chenevier) and Λ-adic JL as
  *targets*. Lemma stab (seed Lemma 5.2: Nrd Γ_x = 1, freeness at U_1(p^s), p ∤ |Γ_x|).
- **Out.** Trees (02). Proofs of JL (cited only). Hida theory beyond the definition of e and η (04).
- **Key objects.** `X_B(U)`, `Γ_x`, `M(U;V)`, `w_x`, Hecke algebra `T_B(U)`, mass formula, Thm JLclassical (cited),
  Chenevier's immersion (cited).
- **Reuse.** Most of it already exists: trace-formula import Vol III (`lean/trace-formula-project-import`, `AlgJL/VolIII/P2/*`:
  `QuatAlg`, `QOrder`, `MaxOrder`, `classSet`, `mass`, `mass_level_change`, `RamifiedExactly`; `AlgJL/VolIII/Brandt/*`:
  `brandtMatrix`, Hecke operators, `SymPower`/`Coefficients` (V_k), `weightedPairing`, `hecke_self_adjoint`,
  `eisenstein_line`, the Hecke trace via fixed points). Its hypothesis `Hyp.EichlerMass` is the mass formula. Caveat: the
  import uses Hilbert-symbol algebras `(a,b)_ℚ`, so the drafter must map seed notation onto `QOrder a b`.
- **Lean.** Mostly *reuse and adapt*. The levels `U_1(Mp^s)` and Iwahori levels and the Lemma-stab statements are new.
- **HACS.** Definite module: class sets plus Brandt matrices with Sym^n, checked against the mass formula and seed C4(ii).
- **Talk.** Slide "what JL says": points (Brandt) versus Riemann surfaces (H¹), and why there is no map of spaces.
- **Literature.** `voight_2021_quaternion-algebras.pdf` (Ch. 17, 23–28, 41: orders, class sets, mass, Brandt; Ch. 28 for strong
  approx. used in 02); `vigneras_1980_arithmetique-des-algebres-de-quaternions.pdf`; `eichler_1955_*`, `eichler_1938_*`
  (mass); `gross_1999_algebraic-modular-forms.pdf` (Brandt modules as algebraic modular forms); `pizer_1980_*`,
  `kohel_2001_*` (algorithms); `jacquet-langlands_1970_automorphic-forms-on-gl2.pdf`, `shimizu_1965_*`,
  `hijikata-pizer-shemanske_1980_*` (classical JL / basis problem); `chenevier_2005_une-correspondance-de-jacquet-langlands-p-adique.pdf`
  (p-adic target); `ribet_1989_bimodules-and-abelian-surfaces.pdf`.
- **Gaps.** None critical.

### 02 `tree-quotients` — Trees, S-arithmetic quaternion groups and quotient graphs
- **Scope.** Seed §5: the Bruhat–Tits tree T_q and its types (Lemma tree); Γ_U = O_U[1/q]^1; strong approximation for B¹ at
  S = {∞, q}; the quotient graph of groups Γ_U\\T_q with vertices X_B(U) (two copies) and edges X_B(U_0(q)U), degeneracies
  s_0, s_1, and Hecke equivariance (Prop quot); Remark normone; group (co)homology via the two-term complex (Prop coh);
  harmonic cochains (Prop harm); the definition of the indefinite stage `\cX^{(q)}_{Dq}(U;V) := H_1(Γ_U,V)`.
- **Out.** Weighted pairings and exact sequences (03). The identification with Shimura curves (Čerednik–Drinfeld) is cited
  only, as a remark.
- **Reuse.** The import has GL₂ strong approximation (`strong_approximation`, `AlgJL/VolI/P0/TopGroups.lean`, in the form
  det K' = Ẑ^×) and the GL₂ local structure (Iwahori, Cartan, Bruhat decompositions; maximal compacts). It does **not** have
  strong approximation for B¹ of a definite B split at q. That is a gap, and it is the one deep input of the combinatorial
  core. Tree: Ludwig–Merten (Mathlib-adjacent; check whether it is available on v4.35.0).
- **Lean.** Lemma tree and Lemma stab are easy. Prop quot needs SA(B¹), carried as an explicit hypothesis until it is proved.
  At U_1(p^s) level the action is free, so the spectral sequence is avoidable (seed §12).
- **HACS.** Tree-quotient incidence matrices s_0, s_1 for given (B, U, q). Test T2 (rank of H_1).
- **Talk.** Picture: the quotient graph of B_3 with the tree at 2. "0-dimensional orbifolds glue to a 1-dimensional one."
- **Literature.** `serre_1980_trees.pdf` (II.1.1 tree, II.1.4 amalgam, I.4 graphs of groups); `ludwig-merten_2026_formalising-the-bruhat-tits-tree.pdf`;
  `brown_1982_cohomology-of-groups.pdf` (VII.7 equivariant spectral sequence); `bass_1993_covering-theory-for-graphs-of-groups.pdf`;
  `voight_2021_quaternion-algebras.pdf` (Ch. 28 strong approximation; Ch. 38 for S-arithmetic/Shimura context);
  `platonov-rapinchuk_1994_*` (Ch. 7 strong approximation); `kneser_1969_*`; `ihara_1966_discrete-subgroups-of-pgl2-over-p-adic-fields.pdf`;
  `casselman_2014_bruhat-tits-tree-of-sl2_preprint.pdf`; `cerednik_1976_*`, `drinfeld_1976_*_ru.pdf`,
  `asterisque_1991_courbes-modulaires-et-courbes-de-shimura_vol.pdf` (Boutot–Carayol inside; cited remark only).
- **Gaps.** A Lean-usable reference proof of SA for B¹ "in the form y = βgu" (the seed says one exists in "existing Lean
  developments", but it is not in our import).

### 03 `ribet-ihara` — Weighted graphs, the definite Ribet sequence and the Ihara lemma
- **Scope.** Seed §6 and §2.7: weighted graphs, X(G), ⟨,⟩_w, Φ^comb; two-vertex graphs (Prop phi); the DR graph G^DR_q(U);
  the Mazur check |Φ^comb| = num((q−1)/12) (Example mazur, from the mass formula); the definite Ribet sequence as a vertex
  collapse (Thm ribet (a),(b)); the definite Ihara lemma (Cor ihara (i)–(iii)); the GL₂ amalgam
  SL₂(ℤ[1/q]) = SL₂(ℤ) *_{Γ_0(q)} SL₂(ℤ), its Mayer–Vietoris sequence, and the level-raising module coker(Ψ*Ψ) (seed §6.4,
  Betti side only).
- **Out.** Ordinary parts (04). The identification with Néron/Grothendieck component groups is a cited remark only (05).
- **Reuse.** Brandt pairing and mass (01 / import Vol III). The amalgam has no Lean counterpart (and the import has no
  SL₂(ℤ) generators).
- **Lean.** Prop phi, Thm ribet (a) for finite multigraphs (use quivers or incidence matrices, not `SimpleGraph`), and
  Cor ihara (ii) are all "Lean-friendly now".
- **HACS.** T1 (Φ^comb for q ∈ {11, 23, 37, 101, 131}), T2 (Ribet collapse), T6 (H_0 with V_k). Seed C3 (amalgam, already
  computed) is the GL₂ counterpart.
- **Talk.** The central slide: the Ribet sequence is a vertex collapse, and Mazur's num((q−1)/12) falls out of a 2-vertex graph.
- **Literature.** `ribet_1990_modular-representations-of-gal-qbar-q-arising-from-modular-forms.pdf` (Ribet's sequence, §§3–4);
  `ribet-stein_2001_lectures-on-serres-conjectures_preprint.pdf` (§3, (3.1), Lemma 3.17); `mazur_1977_modular-curves-and-the-eisenstein-ideal.pdf`
  (component group of J_0(q)); `diamond-taylor_1994_non-optimal-levels-of-mod-l-modular-representations.pdf` (definite Ihara
  via SA); `ribet_1983_mod-p-hecke-operators-and-congruences-between-modular-forms.pdf` (level raising);
  `serre_1980_trees.pdf` (II.1.4); `illusie_*` / `asterisque_1991_*` (Illusie, monodromy pairing; remark only);
  `manning-shotton_2019_*`, `dimitrov_2005_*` (Ihara context); `stein_2007_*` (computations).
- **Gaps.** [Ri84] (Ribet, ICM 1983, "Congruence relations between modular forms") and [SGA7 IX] are not in literature/.

### 04 `lambda-adic` — Ordinary and Λ-adic passage
- **Scope.** Seed §7: Lemma ekills (e kills the degree, vertex and Φ terms; perfect ordinary pairing); M^ord_B(U) and its
  Λ-freeness and control (Prop free); the Λ-adic definite Ribet sequence (Thm lambdaribet) with its rank check; the twisted
  Λ-adic Brandt pairing (sketch); Hsieh's freeness of M^ord_{B,m} over the Gorenstein T^ord_{B,m}, and η^B_F as a
  self-pairing (cited). The nearly ordinary versus ordinary remark (seed §3.3).
- **Out.** Anything on the GL₂ side except citing the Λ-adic JL of Hecke algebras T^{D-new} ≅ T_B ([LV], [Hs]).
- **Reuse.** None from the import (it has no Hida theory). Brandt pairing from 01.
- **Lean.** Lemma ekills, plus exactness of e on finite modules. Control and freeness are registered hypotheses.
- **HACS.** T3 (B_3, tree at 2, p = 5, s = 1, 2, 3, mod 5³); seed C2 (ordinary ranks).
- **Talk.** "Integral subtleties are non-ordinary": the ordinary projector e kills Eisenstein cokernels and Mazur's group.
- **Literature.** `hida_1986_iwasawa-modules-attached-to-congruences-of-cusp-forms.pdf` ([Hi86b] Thm 3.1, Cor 3.2–3.3);
  `hsieh_2017_hida-families-and-p-adic-triple-product-l-functions_arxiv.pdf` ([Hs] §3.3, Thm 4.5, Def 4.12, Rem 7.8);
  `longo-vigni_2009_quaternion-algebras-heegner-points-and-the-arithmetic-of-hida-families_arxiv.pdf` (= [LV], arXiv:0903.2797);
  `longo-vigni_2011_control-theorems-for-quaternionic-hida-families_arxiv.pdf`; `hida_1993_elementary-theory-*` (Ch. 7);
  `hida_1988_p-adic-hecke-algebras-*`; `ohta_1995_*`, `ohta_1999_*` (Ohta twist of the pairing);
  `wiles_1988_ordinary-lambda-adic-representations-*`; `emerton_2010_p-adic-families-*`; `bertolini-darmon_2007_hida-families-*`;
  `chida-hsieh_2013_*`, `longo-magrone-walchek_2025_*` (definite ordinary families); `gross_1999_*`.
- **Gaps.** [Hi86a] (Hida, Invent. Math. 85 (1986), "Galois representations into GL₂(ℤ_p[[X]])") is not present.

### 05 `comparison-hypothesis` — The comparison hypothesis and the simplicial shape
- **Scope.** Seed §4 (the geometric route G1–G5 and its cost), §8 (Hyp.X (X1)–(X4), Prop Xlambda, the table of what is lost
  without it, Hyp.X^iso, Prop subquot), §10 (several ramified primes; Prop noChain), §11 (simplicial shape and zig-zag), and
  open points O1, O2, O4, O6, O7.
- **Out.** The defect formula (06; it does not use Hyp.X). Proving Hyp.X (it stays a hypothesis; at most G1–G4 are cited at
  Γ_0 level).
- **Reuse.** None in Lean. Import Vol I/II (algebraic GL₂) only for the vocabulary of the statement.
- **Lean.** `def Hyp.X.char : Prop` and `def Hyp.X.gal : Prop`, stated, never an axiom. Prop subquot is pure commutative
  algebra and Lean-friendly.
- **HACS.** T7 (Gram matrix versus the Ohta-twisted GL₂ pairing at Eisenstein or non-Gorenstein m; later).
  Example mazur / T1 is the Eisenstein check of (X2).
- **Talk.** Why the geometric route is expensive (one slide) and the zig-zag picture with its single hypothesis arrow.
- **Literature.** `deligne-rapoport_1973_les-schemas-de-modules-de-courbes-elliptiques.pdf` (G1); `ribet-stein_2001_*` (§3);
  `pollack-weston_2006_anticyclotomic-mu-invariants-of-modular-forms_arxiv.pdf` ([PW] Prop 6.5); `ribet_1990_*`;
  `bosch-lutkebohmert-raynaud_1990_neron-models.pdf`; `raynaud_1970_*`; `asterisque_1991_*` (Boutot–Carayol, Illusie);
  `cerednik_1976_*`; `drinfeld_1976_*_ru.pdf`; `helm_2004_*` ([Hel]); `ichino-prasanna_2016_*`, `ichino-prasanna_2023_*`
  ([IP], why a defect must exist); `chenevier_2005_*`; `moerdijk-pronk_1997_orbifolds-sheaves-and-groupoids.pdf`;
  `calegari-venkatesh_2012_torsion-jacquet-langlands-correspondence_arxiv.pdf` (comparable integral JL);
  `ribet-takahashi_1997_*`; `jordan-livne_1985_*`; `carayol_1986_sur-la-mauvaise-reduction-*`.
- **Gaps.** [MP] Moerdijk–Pronk, "Simplicial cohomology of orbifolds", Indag. Math. 10 (1999): only their 1997 K-theory
  paper is present. Also missing: [SGA7 IX] and the Illusie paper as a separate file (it is inside the Astérisque volume).

### 06 `integral-defect` — The integral JL defect
- **Scope.** Seed §9: standing hypotheses (H0)–(H2), (Im), (P); T', T'', 𝔞, 𝔟, R, R', η_F, η^B_F, h_F; the combinatorial
  Tamagawa ideal 𝔠_q (Def ctam) and the Tamagawa ideal 𝔱_q; Lemmas S, G, D; Thm E (combinatorial half); Prop galois;
  Thm defect ((h_F) = 𝔠_q = 𝔱_q); Cor allweights; the open cases; the conjectural several-primes defect formula (seed §10,
  last paragraph); O5. Computation side: seed C1, C3, C4(i), T4, T5.
- **Out.** Hyp.X (not needed). Proofs of the cited Hida, Hsieh and R = T inputs.
- **Reuse.** None from the import (pure commutative algebra plus cited Galois inputs).
- **Lean.** Lemmas S, G, D, Thm E and the final squeeze are Lean-friendly. Hida control, Hsieh's Gorenstein theorem, Galois
  representations and R = T are registered hypotheses.
- **HACS.** T4 (𝔠_3 along the 17-adic branch through Δ, up to k = 124), T5 (definite-side combinatorial half with
  rk T'_m ≥ 2); C1/C3/C4 are already done.
- **Talk.** The arithmetic punchline: the defect is an old/new congruence ideal, it equals a Tamagawa ideal, and the
  numbers (17, 29, 131) come from HACS.
- **Literature.** `diamond_1989_congruence-modules-associated-to-lambda-adic-forms.pdf` ([Dia89]); `kim-ota_2019_*` ([KO] §§2–3);
  `pollack-weston_2006_*` ([PW]); `hsieh_2017_*` ([Hs]); `hida_1986_iwasawa-modules-*` ([Hi86b]); `wiles_1995_*` ([Wi95]);
  `diamond-flach-guo_2004_*` ([DFG]); `dimitrov_2005_*` ([Dim09] Thm 6.6); `bockle-khare-manning_2019_*`, `_2021_*` ([BKM]);
  `helm_2004_*` ([Hel]); `diamond_1996_deformation-rings-and-hecke-rings.pdf`; `ribet_1983_*`; `taylor-wiles_1995_*`;
  `hida_1981_congruences-of-cusp-forms-*`, `hida_1988_modules-of-congruence-*`; `iyengar-khare-manning_2022_*`;
  `fakhruddin-khare-ramakrishna_2019_*` (quantitative level lowering); `lang-pollack-wake_2026_*`; `ciavarella_2007_*`;
  `vatsal_1999_*`; `maksoud_2023_*`; `kim-ota` and `ichino-prasanna` for the period interpretation.
- **Gaps.** [MW] (Mazur–Wiles, "On p-adic analytic families of Galois representations", Compositio 59 (1986)): the
  `mazur-wiles_1984` file is the class-field paper, a different work. Also missing: [Hi86a], [Ri84], and "Böckle's
  presentation" (no reference given in the seed).

## Interfaces (what each seam exports)

Each item below becomes an `interface` environment, `\label{if:sNN-...}`, in the **exporting** stage. Importing stages
restate the item verbatim with status `\status{imported from stage NN}`.

**01 → 02, 03, 04, 05, 06**
- `if:s01-classset`. X_B(U), Γ_x and w_x as defined in the conventions above. Facts: X_B(U) is finite, Γ_x is finite,
  Nrd(U) = Ẑ^× for all the standard levels, and Lemma stab (a)–(c) holds.
- `if:s01-brandt`. M(U;V) together with the Brandt pairing ⟨[x],[y]⟩ = w_x δ_xy, the norm-map identification
  ℤ_p[X] ≅ ℤ_p^X when p ∤ |Γ_x|, and the right-translation maps x ↦ xg for g ∈ B_q^×.
- `if:s01-hecke`. The Hecke operators T_ℓ, S_ℓ, U_ℓ, ⟨d⟩, U_p (with fixed normalisation N_Up) and Π_ℓ (ℓ | D). All
  operators supported away from q commute with right translation by B_q^×. Self-adjointness for the pairing.
- `if:s01-mass`. The mass formula Σ_x 1/|Γ_x| = (1/24)∏_{ℓ|D}(ℓ−1) at maximal level (the full-unit convention, as in the import's
  `Hyp.EichlerMass`), and its level change.
- `if:s01-targets`. Thm JLclassical (cited) and the Λ-adic Hecke JL T^{ord,D-new} ≅ T^ord_B ([LV], [Hs]; cited).

**02 → 03, 04, 05** (05 uses `if:s02-quot` in `def:s05-stages`, `prop:s05-nochain` and `if:s02-coh` in `rem:s05-degree`;
provisional after the global Fable audit, F5)
- `if:s02-tree`. T_q, its types, v_0, v_1 = αv_0, e_0, and Lemma tree.
- `if:s02-SA`. Strong approximation: \hat B¹ = B¹(B¹_q × U^{1,(q)}) for q ∤ D, with U as in Prop quot. Status: cited
  (Voight Ch. 28), or a hypothesis in Lean.
- `if:s02-quot`. Prop quot (a)–(c): the bijections, the degeneracies s_0[x] = [x] and s_1[x] = [xα], stabilisers, and Hecke
  equivariance.
- `if:s02-coh`. Prop coh (the two-term complex) and Prop harm. H_0(Γ_U,V) = V_{U_p^1}; Prop coh (c),(d) (this identification)
  need full strong approximation, not only connectivity of BG(U,q) (global Fable audit, F5/F14).
- `if:s02-indef`. The definition `\cX^{(q)}_{Dq}(U;V) := H_1(Γ_U,V)`. The rank at a free level is
  (q−1)|X_B(U)| + 1.

**03 → 04, 05, 06**
- `if:s03-graph`. Weighted graphs, X(G), ⟨,⟩_w, Φ^comb, Prop phi; the DR graph G^DR_q(U) and X^comb_q(U).
- `if:s03-ribet`. Thm ribet (a) over ℤ and (b) with coefficients, with α = (−s_{0*}, s_{1*}) (exact sign convention).
- `if:s03-ihara`. Cor ihara (i)–(iii). (iii) says H_0 is Eisenstein; its status is sketched.
- `if:s03-amalgam`. The Mayer–Vietoris sequence for Γ_0(M)[1/q], the formula for Ψ*Ψ, and the definition of the Betti
  level-raising module coker(Ψ*Ψ)_m (used by 06 as the Betti incarnation of 𝔠_q).

**04 → 05, 06**
- `if:s04-ekills`. Lemma ekills (a)–(c).
- `if:s04-Mord`. M^ord_B(U) := lim_s e ℤ_p[X_B(UU_s)]; Λ-freeness and control (cited [Hi86b], [LV], [Hs]); and the
  Gorenstein property of T^ord_{B,m} with M^ord_{B,m} free of rank one (cited [Hs, Thm 4.5]) under the hypotheses
  "m non-Eisenstein + Hsieh's residual condition" (stage 04 must state that condition explicitly).
- `if:s04-lambdaribet`. Thm lambdaribet; X^ord_{Dq}(U) := lim_s e H_1(Γ_{UU_s}, ℤ_p).
- `if:s04-etaB`. η^B_F equals the self-pairing of a generator of the F-eigenline (cited, Hs).

**05 → (none downstream; it exports to the talk and to Lean)**
- `if:s05-hypX`. The precise statements of Hyp.X(M;q), Hyp.X.char, Hyp.X.gal and Hyp.X^iso, with the data list from seed
  Hypothesis 8.1. These are the exact Prop shapes Lean will register.
- `if:s05-subquot`. Prop subquot (also usable by 06).

**06 → 05** (provisional after the global Fable audit, F16; this makes 05 depend on 06 for Lemma D)
- `if:s06-lemD`. Lemma D (a)–(c) of stage 06 (pure commutative algebra). 05 uses (a) in `prop:s05-subquot` and (b) in
  `prop:s05-Xiso`.
- `if:s06-defect`. Thm defect ((h_F) = 𝔠_q = 𝔱_q) under (H0⁻) or (Lev_M); exported to the talk and to Lean, no stage imports it.

**06 imports** `if:s01-targets`, `if:s01-hecke`, `if:s03-amalgam`, `if:s04-Mord` and `if:s04-etaB`. Optionally it imports
`if:s05-subquot`. It does not import Hyp.X.

## Conventions for drafters

1. Each drafter writes **only** `plan/staged/stage-NN-<slug>.tex` (it starts with the existing `\section{...}\label{sec:stage-NN}`
   line), `plan/staged/bib/stage-NN.bib` (biblatex entries; keys follow the seed: `Vo`, `Hs`, `KO`, ...; reuse a key
   exactly if another stage already uses it), and `plan/staged/missing/stage-NN.md` (missing literature, requested macros,
   doubts about the seed). Do not touch `preamble.tex`, `main.tex`, `SPLIT.md` or the seed.
2. The stage file has these `\subsection`s, in order: **Goals**; **Definitions and statements** (each with a status tag and
   a precise reference: literature file + theorem/section/page via `\lit{}{}`); **Proof strategy**; **Dependencies and
   interfaces** (restate the imported `if:` items; state the exported ones as `interface` environments); **Lean, HACS,
   talk**; **Risks**.
3. **Tracks are decoupled.** The mathematics, Lean, HACS-computation and talk tracks run independently. The mathematical
   text may run ahead of the formalization. Do not define joint milestones that make one track wait for another. In
   "Lean, HACS, talk", list milestones **separately per track** (math / Lean / HACS / talk). The only coupling is that a
   statement must exist in the mathematics before it is formalized.
4. Do not change the seed's notation. If the seed is wrong or ambiguous, say so in `missing/stage-NN.md` and in Risks;
   do not silently fix it.
5. The file must compile with `cd plan/staged && latexmk -pdf main.tex`. Run `latexmk -c` afterwards and commit no build
   products.
6. Verify every citation against the PDF in `literature/` (theorem number and page). If a file is missing, record it in
   `missing/stage-NN.md` and mark the statement `\stcited` with "(reference not in literature/)".

## Doubtful or underspecified points in the seed (for drafters to check)
- §12 says that strong approximation for B¹ "exists in this shape" in Lean. Our import has only GL₂ strong approximation
  (det-form), so this is a gap for 02.
- §9, Thm defect step (4) claims level lowering "including q ≡ −1 mod p", but test T5 and C4 exclude q ≡ ±1. Check
  whether q ≡ −1 is really covered (06).
- Thm E needs R (not only R') Gorenstein, through Lemma S. Only the "setting of Lemma D" signals this; make it explicit (06).
- "Böckle's presentation" is cited without a reference (06). [LV] is cited only by arXiv number; it is
  `longo-vigni_2009` (04).
- Cor ihara (iii) (the Hecke action on H_0 is Eisenstein) is only sketched, and the sign or exponent ℓ^{±1} is unfixed (T6
  is meant to pin it; 03).
- The U_p normalisation, the sign ε and the exponent in U_q ↦ εΠ_q^{±1}, and the Ohta twist are all left open (O1).
  Stage 01 must fix N_Up; stage 05 owns ε.
