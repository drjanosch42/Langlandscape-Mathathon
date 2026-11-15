# Stage 02 (tree-quotients): missing literature, macro requests, seed issues

## Missing literature (not in `literature/`)

Bibliographic data for items 2, 3, 5 and 7 (pages, volume) is from memory and should be confirmed on acquisition.

| # | Reference | Why needed | Priority |
|---|---|---|---|
| 1 | T. Miyake, *Modular Forms*, Springer Monographs in Mathematics, Springer 1989 (repr. 2006), Thms. 5.2.9–5.2.10 (strong approximation over ℚ). ISBN 978-3-540-29592-1. | A ℚ-specific proof of SA for B¹. Voight §28.7 cites it for F = ℚ. It is the most likely blueprint for Lean milestone L02.SA and math milestone M02.4. | high |
| 2 | M. Kneser, "Strong approximation", in *Algebraic Groups and Discontinuous Subgroups* (Boulder 1965), Proc. Sympos. Pure Math. 9, AMS 1966, 187–196. | The original proof for simply connected groups. Kneser's 1969 Tata lectures (present) only state it (Sublemma b, p. 94). | medium |
| 3 | R. G. Swan, "Strong approximation and locally free modules", in *Ring Theory and Algebra III* (Norman 1979), Lecture Notes in Pure and Appl. Math. 55, Dekker 1980, 153–223. | Source of Voight's second proof (§28.8). This group-theoretic route may avoid the quadratic-embedding local–global step. To be assessed for Lean. | medium |
| 4 | I. Reiner, *Maximal Orders*, LMS Monographs 28, Oxford 2003 (orig. Academic Press 1975), §34 (Eichler's theorem and strong approximation). | An alternative textbook proof for norm-one groups of orders; Voight 28.6 cites it. | low |
| 5 | E. Kleinert, *Units in Skew Fields*, Progress in Math. 186, Birkhäuser 2000, §4.2. | An exposition of the second proof (cited by Voight §28.8). | low |
| 6 | Ludwig–Merten Lean repository (code, Lean v4.19.0), linked from arXiv:2505.12933. | Port of `BTtree` and `laplace_surjective` for L02.1 (a). This is code, not literature: record the commit hash when we fetch it. | medium |
| 7 | A. Kurihara, "On some examples of equations defining Shimura curves and the Mumford uniformization", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 25 (1979), 277–300. | Explicit quotient graphs Γ\T for small discriminants. An independent cross-check of T2 and of Remark rem:s02-torsion. | low |

Not needed separately: Čerednik [Če] and Drinfeld [Dr] are cited only through Boutot–Carayol (present in the
Astérisque 196–197 volume, Ch. III Thm 5.2, pp. 139–140). Ihara 1966 is present but not cited here; Serre II.1.5
covers what we use.

## Macro requests (currently `\providecommand` at the top of `stage-02-tree-quotients.tex`)
- `\BG` (bipartite Brandt graph BG(U,q)), `\Xone` (norm-one class set X^1_B), `\HypSA`, `\HypHS` (Lean hypothesis
  names). Please add them to `preamble.tex` if stages 03/04 use them. Stage 03 should, for `BG(U,q) = |G|`.

## Seed issues (plan/seed/towards_simplicial_jl.tex is frozen; these are recorded, not fixed there)
1. **§12, "existing Lean developments contain [SA for B¹] in this shape": wrong for our material.** The
   trace-formula import has only `sl2_strong_approximation` (SL₂(ℚ) dense in SL₂(𝔸_f), S = {∞}) and the GL₂
   `strong_approximation` (det K' = Ẑ^×), both in `AlgJL/VolI/P0/TopGroups.lean`. For definite B the non-compact
   place is q, not ∞, and B¹ has no unipotents, so the elementary-matrix proof does not transfer. Mathlib
   v4.35.0 has neither Skolem–Noether nor Hasse–Minkowski (grep). See the stage file, milestone L02.SA, for the cost
   (dominated by the local–global principle for quadratic embeddings, Voight Prop. 14.6.7).
2. **Prop. quot, proof: hidden Hasse–Schilling.** "Every class of X_B(U') has a representative of norm in Ẑ^×" is
   exactly Nrd(B^×) = ℚ_{>0} (Voight Main Thm 14.7.4). The seed does not cite it. In Lean it is a second hypothesis
   (`Hyp.HS`), unless one uses the per-level criterion (stage file Prop. prop:s02-BG).
3. **Def. indef with V = ℤ is not torsion-free.** H_1(Γ_U, ℤ) contains coker(⊕H_1(Γ_e) → ⊕H_1(Γ_v)) (exponent
   dividing 24). Example: B_2, maximal level, q = 3, where one expects H_1(Γ_U, ℤ) ≅ ℤ/3 while the graph has
   H_1 = 0. So the claim "for V = ℤ and Γ_0-type U this is the character group" needs H_1(|G|, ℤ) =
   H_1(Γ_U, ℤ)/torsion. Over ℤ_p with p ≥ 5 there is no issue. (Interface deviation D1.)
4. **Remark normone: "the central element q acts trivially on T_q".** Only the centre ℚ_q^× of GL₂(ℚ_q) acts
   trivially. The global scalar q lies in O_U[1/q]^× only if q ∈ U_ℓ for all ℓ ≠ q, which fails at U_1(N)-levels.
   The conclusion (one copy of X_B(U)/⟨q⟩) is correct.
5. **Prop. quot (c), "the bijections are equivariant for all Hecke operators away from q".** This is a tautology
   unless a tree-side Hecke action is defined independently. The content is that s_0^*, s_1^*, s_{0*}, s_{1*}
   commute with Hecke operators supported away from q. The stage file states it that way.
6. **Prop. coh (c)/(d) and Cor. ihara (iii) need global density at p.** A finite connectivity check at one level
   does not give H_0 = V_{U_p^1}. Stages 03/04 should note this.
7. **Prop. coh: homology "the transpose".** This is the transpose for the *unweighted* pairing ℤ[X] × ℤ^X.
   Identifying homology with Brandt modules uses norm maps (factors |Γ_x|), and the Brandt pairing uses
   w_x = |Γ_x/±1|. These are harmless over ℤ_p, p ≥ 5, but they matter for the adjoint α^* in stage 03 (T2(c)).
8. **Notation clash:** α = ι_q^{-1} diag(1,q) (seed §5) versus α = (−s_{0*}, s_{1*}) (seed §6). Not renamed.

## Mis-citations / reference notes
- [LM] is correct (Ann. Formalized Math. 2 (2026) 55–81, DOI 10.46298/afm.15738). But the formalisation is on Lean
  **v4.19.0** in a separate repository. Only `Submodule.IsLattice` is in Mathlib v4.35.0, so "a Lean formalisation
  exists" (seed §5) does not mean that it is usable on our frozen toolchain.
- [Br, VII.7] is fine (the spectral sequence (7.10), p. 174). The sharper and more directly usable reference for
  the two-term sequence is **Serre, Trees, II.2.8, Prop. 13 (p. 127)**, which also fixes the signs.
- [Vo, Ch. 28] is correct. The precise pointers are Main Thm 28.5.3 (p. 485), with 28.4.8 / Cor. 28.5.12 (pp.
  484–486) for the shape y = βgu. Voight's first proof cites "Exercise 7.31" for B¹ = [B^×, B^×]; in the local copy
  Exercise 7.31 is a different statement (automorphisms of ℍ are inner), so that fact needs its own reference or
  proof in L02.SA (b).
- SPLIT.md lists `voight Ch. 38` for the S-arithmetic/Shimura context. It was not needed for this stage.
