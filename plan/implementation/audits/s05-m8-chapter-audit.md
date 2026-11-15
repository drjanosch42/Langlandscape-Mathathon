<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S05-M8 — Fable chapter audit, stage 05

- Target: `mathematics/chapters/s05/{sign,higherweight,hypX,subquot,geometric,status,simplicial}.tex` + `NOTES.md`,
  branch `wip-implementation` @ `f05d617e` (read-only). Source: `plan/staged/stage-05-comparison-hypothesis.tex`.
- Role: `agents/roles/mathematics_chapter_audit.md`. Date: 2026-11-15.

## Verdict: PASS (WITH REMARKS)

No critical defect. The normalisation chain (ε, e, δ, Rosati twist in (X4), factor 2, M ≤ 2, direction of β, P_k ↔ P^ad_k)
is mathematically consistent; I re-derived each item independently (below). Three **maj** items are required fixes
(one printed-notation collision that garbles the (R2) proof, one status contradiction between two files, one status label);
the rest are **min**.

Counts: crit 0, maj 3, min 11.

## What was checked and found correct

1. **ε = +1** (`prop:s05-sign`(a),(b), `prop:s05-signe`): the chain Ribet 3.1 / 3.7 / 3.8 / Rem. 3.5(b) is used consistently;
   step (5) (Π_q² trivial at Γ_0-level) is right. Higher weight: St has U-eigenvalue +1 in the unitary normalisation,
   χ∘Nrd ↔ (χ∘det)⊗St, both normalising factors positive: a_q = χ_0(q) q^{(k-2)/2} = λ(Π_q). Correct.
2. **e = δ** (`prop:s05-sign`(c), `lem:s05-consistency`(a)): Π_q² = S_q = ⟨q⟩_ad^{-1} (matches `prop:s01-relations`(a),(b)),
   U_q² = ⟨q⟩_cl on q-new; the relation U_q² = ⟨q⟩ holds in both models (under φ of `lem:s05-models`:
   (U^μ_q)² ↔ (U^nv_q)²⟨q⟩_nv^{-2} = ⟨q⟩_nv^{-1} = ⟨q⟩_μ). Correct.
3. **δ = +1** (`prop:s05-sign`(d), `lem:s05-Up-pullback`, `lem:s05-consistency`(d)): cartesian a-square, π^*U_p = U_pπ^*,
   and the rank-mod-p argument excluding θ^Ros are correct. Scope remark: M8-4.
4. **Frobenius table** (`rem:s05-Xstatus`): independently confirmed, without Ribet–Stein Lemma 3.17. For an eigensystem with
   ρ_f (tr Frob_ℓ = a_ℓ, det = χε_cyc), ρ_f|G_q has sub η·ε_cyc and quotient η with η(Frob_q) = a_q(f) (arithmetic Frobenius).
   Naive model + Albanese realises ρ_f on the eigenspaces of the Albanese operators (Conrad Thm. 5.16 for the shape,
   Thm. 5.1 for eigenvalues on H^1), so Frob = q·U_q on T_t there: this is row 2. Rows 3, 1, 4 follow by U_q^Ros = U_q^{-1}
   on q-new and `lem:s05-models`. All four rows agree with the table. See M8-3 for the status label.
5. **Rosati twist in (X4)**: top piece T/T^I ≅ X_q(J^∨)⊗Z_p, Picard h acts as X_q(h^Ros) ↔ θ_s(h)^*. Eigenvalue check: if
   Picard h acts by λ(h), bottom Frobenius is qλ(U_q), top Frobenius is λ(⟨q⟩)/λ(U_q) = λ(U_q); determinant qλ(⟨q⟩). Consistent.
   `prop:s05-Xlambda`(d1)–(d3) (Albanese tower, h_* ↦ θ(h), Frob = Π_q^{-1} resp. qΠ_q^{-1}, N = ±id) consistent with this.
6. **Factor 2, M ≤ 2** (`rem:s05-factor2`, `lem:s05-consistency`(c)): −1 ∈ U_s iff s = 0 and M ≤ 2; π^!_w = w_y π^* = ½π^!
   exactly there; = π^! for s = 0, M ≥ 3; = π^* for s ≥ 1. Weights agree with DR VI 6.9 as quoted in `thm:s05-G`(i). Correct.
7. **Direction of β**: β_{s's}: X_q(J_{s'}) → X_q(J_s) from Picard pullback, paired with π_*; used with the same direction in
   `lem:s05-Up-pullback`(b), `lem:s05-consistency`(c),(d), `prop:s05-Xlambda`(a),(d). Consistent.
8. **P_k ↔ P^ad_k**: Φ is ι-semilinear, ι(P_k) = ker([u] ↦ u^{2-k}) = P^ad_k; matches `def:s04-Pk`
   (`chapters/s04/hsieh.tex:20`). Rank r = rk e Z_p[S_1], rank at level s = r·p^{s-1}: consistent with stage 04.
9. **`lem:s05-R1`, `prop:s05-AL`, `lem:s05-models`, `prop:s05-subquot`, `prop:s05-Xiso`, `prop:s05-nochain`**: proofs read
   in full; no error found. Restriction of (R1) to X_q(J_s) is necessary and correctly argued (γ factors through a
   good-reduction quotient).
10. **Hyp.X never called known**: confirmed in all seven files; `\sthyp` on `hyp:s05-X`, `if:s05-hypX`, `def:s05-Xiso`.
11. **FD1/FD2 `\provisional`** (M10-scope): FD1 markers present at `sign.tex:24,107,313`, `hypX.tex:42,79`;
    FD2 at `geometric.tex:96` (tagged "F6/D3"). See M8-9.
12. **Compilation**: fresh `latexmk -pdf standalone-s05.tex` on an export of `f05d617e` (scratchpad): exit 0, 130 pages,
    no undefined references or citations, no multiply defined labels.
13. **Lean**: `Hyp.X.*` and `theta` are not on this commit (`\leanplanned`, correct). `CommAlg/SubQuot.lean` and
    `Comparison/XIso.lean` are present and sorry-free; see M8-10.

Not re-verified by me: page numbers of the `\lit` pointers (R1 read them on the PDFs; I relied on NOTES.md and the litnotes).

## FIX LIST

### maj

- **M8-1 (maj)** `mathematics/preamble.tex:118` with `hypX.tex:140-141, 384, 389-390, 395` (also `:54`, `:379-383`).
  Defect: `\Ros` is defined as `\vee`, and the same files use `\vee` for the dual morphism / dual abelian variety. The
  PDF therefore prints "α^∨ = λ^{-1} α^∨ λ" (line 141), "M'(α^∨)λ_t = λ_t M(α^∨)" and
  "X_q(α^∨) … becomes X_q(α^∨), with α^∨ := λ_{s'}^{-1} α^∨ λ_s" (lines 389–390). The proof of (R2) and the functoriality
  paragraph of `prop:s05-Xlambda`(d), i.e. exactly the Rosati-twist argument, are unreadable as printed, and h^Ros in (X4)
  is indistinguishable from the dual.
  Fix: in the stage-05 files write the dual morphism and dual variety with a different symbol (e.g. `\alpha^{t}`, `A^{t}`),
  or give `\Ros` a distinct glyph in the chapter driver (`\renewcommand`, since `\providecommand` in `s05.tex:9` has no
  effect). Do not use `\dagger`, which `lem:s05-R1` uses for the cup-product adjoint.

- **M8-2 (maj)** `status.tex:61-64` and `status.tex:71-73` against `sign.tex:276-282, 309-312`.
  Defect: `status.tex` says "No source states the Frobenius on the torus … at Γ_1(N)∩Γ_0(q) with non-trivial nebentypus",
  "the four-row table … has no literature anchor at Γ_1-level beyond Diamond–Im (8.4.1)", and concludes that the Frobenius
  clause "remain[s] expected". `sign.tex` (batch 5/6) gives row 1 as cited (Ribet–Stein Lemma 3.17 at Γ_1(M)∩Γ_0(p)) and
  rows 2–4 as proved modulo cited. `status.tex` itself cites Lemma 3.17 at that level three lines earlier. Two statuses for
  the same claim in one chapter.
  Fix: update `status.tex` (d) and the Conclusion to the batch-5/6 state (row 1 anchored by Lemma 3.17 under the convention
  of `lem:s05-models`(c); rows 2–4 derived; (S2) and (X3) remain expected), with the wording chosen in M8-3.

- **M8-3 (maj; adjacent to M10-scope)** `sign.tex:282, 292-294, 309-310, 313-314`.
  Defect: row 1 is labelled `\stcited`, but the text states that reading Ribet–Stein's bad-prime T_p as a_*b^* "is a
  convention we adopt … not a cited statement". With the other reading (b_*a^*) row 1 would become q⟨q⟩^{-1}U_q, which is the
  exact distinction FD1 decides. "cited" overstates (CLAUDE.md status rule; NOTES.md batch-5 item 2 raised the same point as a
  "minor status remark" and it was not acted on).
  Fix: either (i) relabel row 1 "cited modulo the identification of the operator" / `\stexp` in the row-1 paragraph, the
  status summary and the `\provisional` note; or (ii) better, anchor the table at row 2 instead: Conrad Thm. 5.16
  (naive model, Albanese, Eichler–Shimura) plus Thm. 5.1 identify the eigensystem with ρ_f, and local–global compatibility
  at q (ρ_f|G_q ≅ (ηε_cyc, *; 0, η), η(Frob_q) = a_q(f); cite Langlands/Carayol or Ribet–Stein §3 if stated there) gives
  Frob = q·U_q on T_t in row 2 with no convention about Lemma 3.17; then rows 3, 1, 4 follow by the two lemmas already in
  the text. Lemma 3.17 then becomes a consistency check. My derivation (item 4 above) confirms all four rows.

### min

- **M8-4 (min)** `sign.tex:121-128` (heading and "i.e. δ=+1") with `sign.tex:391-393`.
  Defect: (d) is proved for θ' ∈ {θ, θ^Ros} and for dictionaries with T_ℓ ↦ T_ℓ. The hybrid dictionary
  ⟨d⟩ ↦ ⟨d⟩, T_ℓ ↦ ⟨ℓ⟩T_ℓ (= T_ℓ^*), U_q ↦ Π_q^{-1}, U_p ↦ N_{U_p} has δ = −1, satisfies U_q² = ⟨q⟩ and the T_ℓ-relation
  (T_ℓ^{*2} − T_{ℓ²}^* = ℓ⟨ℓ⟩), the adjoint compatibility of `lem:s05-consistency`(b), and commutes with π_*. None of the
  chapter's arguments excludes it. The precise statement of (d) is correct; the title "The diamond convention is δ=+1" and
  "i.e. δ=+1" read as unconditional.
  Fix: say "among θ_s, θ^Ros_s and the dictionaries with T_ℓ ↦ T_ℓ" in the heading sentence, and name the hybrid as not
  excluded by these arguments (it is excluded by T05-2 / strong multiplicity one, not by (X3)).

- **M8-5 (min)** `hypX.tex:48`. Defect: "the pairings in (X3) are compared with the factor 2": (X3) contains no pairing.
  Fix: "the u-adjoint of β_{s'0} is compared with the transfer π^! with the factor 2 (Lemma consistency (c))".

- **M8-6 (min)** `geometric.tex:55-56`. Defect: "the numbered statements 2.4, 9.1.2, 10.4 were not located page by page in
  this WP" is stale: `hypX.tex:57-58, 134-146, 380` give pp. 338, 418, 441, 443, 444. Fix: replace by those pages.

- **M8-7 (min)** `status.tex:51`. Defect: "Thm. G(iv) is stated for any semistable curve": `thm:s05-G`(iv) is stated for
  J = J_0(N). Fix: refer to Raynaud Thm. 5 / SGA 7 IX 11.5 (general), not to `thm:s05-G`(iv).

- **M8-8 (min)** `hypX.tex:35` ((X4), middle piece). Defect: the H_s-module structure on T_pJ_1(Mp^s)^{⊕2} is not specified
  for U_q (it acts by a 2×2 matrix in T_q, ⟨q⟩, q), although the pieces are asserted "as H_s[G_{Q_q}]-modules". Inherited
  from the stage tex. Fix: state the U_q-matrix, or restrict the middle clause to the operators away from q.

- **M8-9 (min; M10-scope)** `hypX.tex:290-291` ((d1), (d2): "Frob_q acts as Π_q^{-1}", "qΠ_q^{-1}"), `hypX.tex:451` (L1),
  `geometric.tex:96`. Defect: the Frobenius clauses of (d1), (d2) and (L1) depend on FD1 but carry no `\provisional{FD1}`;
  the FD2 marker is tagged "F6/D3" only, so a search for "FD2" finds the remark title but not the marker.
  Fix: add an FD1 `\provisional` to (d1)/(d2) (one marker suffices) and write "FD2 (F6/D3)" in the marker.

- **M8-10 (min)** `subquot.tex:83`. Defect: `subquot_kernel`, `subquot_coker` are marked `\leanplanned`, but
  `lean/Langlandscape/Langlandscape/CommAlg/SubQuot.lean:299, 328` exist on this commit, sorry-free
  (namespace `Langlandscape.CommAlg`); likewise `Comparison/XIso.lean` is not referenced from `prop:s05-Xiso`.
  Fix: `\stformalized` with the declaration names (after the Lean audit S05-L10 confirms), and a `\lean{…}` on `prop:s05-Xiso`.

- **M8-11 (min)** `hypX.tex:37-39` and `sign.tex:379-381`. Defect: at s = 0 the generator T_p has T_p^Ros = ⟨p⟩^{-1}T_p ∈ H_0,
  but `lem:s05-consistency`(b) lists only T_ℓ (ℓ ∤ Mpq), ⟨d⟩, U_q, so "the two readings agree where both are defined" is
  not checked for T_p at s = 0. The proof is the same. Fix: add "and T_p at s = 0" to (b).

- **M8-12 (min; M10-scope)** `hypX.tex:270-271, 352-374` ((c2)). Audited as it stands: status `\stsketch` with an explicit
  missing-step list (i)–(v) including the norm twist is honest; nothing is claimed beyond that. `simplicial.tex:23-26`
  (`rem:s05-BN`) writes the twist as u_s(g, w g) without U_p^{-s}; harmless up to a unit on an eigenline, but align it with
  [ , ]_s of (c) when (c2) is reworked. The row "η^B_F = monodromy self-pairing via (X2)" in `hypX.tex:446` carries no status
  while the remark it points to is `\sttoprove`: add the status to the table cell.

- **M8-13 (min)** notation overload, `sign.tex` / `hypX.tex`. Defect: ε is the sign of Π_q and (in `sign.tex:414-418`)
  |U∩{±1}|; e is the exponent and the ordinary projector; w is the Atkin–Lehner involution, the weight w_e and the index of
  ⟨,⟩_w; M is the level and (in `hypX.tex:131-142`) the SGA 7 lattice; δ is the diamond exponent, δ_d and the Kronecker δ.
  Fix: rename the local ones (ε_U for |U∩{±1}|, 𝔐/𝔐' for the SGA lattices, W for the Atkin–Lehner involution where it meets
  w_e).

- **M8-14 (min)** `NOTES.md:15, 135`. Defect: the file's headline still reads "Overall verdict: GAP" (first read); the
  batch-5/6 re-reads close items 3 and 4 and leave only the (c2) list (now completed in `hypX.tex:368-373`). A reader of the
  first screen gets the wrong state. Fix: add a one-line current-state header (all seven items CONFIRMED after batch 6; open:
  (c2), (d4), M8-3).
