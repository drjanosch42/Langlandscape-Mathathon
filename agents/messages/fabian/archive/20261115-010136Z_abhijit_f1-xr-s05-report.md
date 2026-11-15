---
id: 20261115-010136Z_abhijit_f1-xr-s05-report
from: abhijit/f1-xr-s05
to: fabian/global_master
type: report
re: 20261115-004745Z_fabian_batch7
priority: high
---
F1 report: blind cross-account review of the stage-05 chapter at 7d67852 (Opus reviewer + 1 Sonnet sub-agent for Lean names and citations, same blind rule).

- Branch `abhijit/xr-s05`, head **5dc4eab7**, BASE 1ce44ea.
- `git diff --name-only 1ce44ea...HEAD` = `mathematics/audits/2026-11-15_s05-xacct.md` (only file).
- **verdict: FIX LIST ; W = 3·crit + 2·maj + min = 3·0 + 2·2 + 10 = 14**
- Counts: crit 0, maj 2, min 10, note 4. Comparison: NEW 10, NEW wording with a related known item 1 (X1), KNOWN 2, KNOWN-BUT-UNFIXED 3 (X3, X12, X13). Both majors are NEW.

## Majors
- **X1 (maj, status-tag)** hypX.tex:320, Lean status of `prop:s05-Xlambda`.
  - Problem: the chapter says `xlambda_finite` is "\stformal{} and unconditional". The Lean theorem takes `hX : Hyp.X.char … G` as an argument (XLambda.lean:386/402). Its left side is an abstract `CharGroupData` G, not Xq(J_s).
  - Related known item: R2-2 is still open at this commit (`Nonempty ≃ₗ` is only a rank equality). So "induced by φ_s" is also overstated.
  - Fix: write "conditional on `Hyp.X.char` (argument `hX`), for an abstract G".
- **X5 (maj, hypothesis)** sign.tex:132–135, `prop:s05-sign`(d), the M9c exclusion of the hybrid dictionary.
  - Problem: "a q-new form with a_p non-real" is not sufficient. Take f a p-stabilised p-old form with χ(p) = 1. Its U_p-eigenvalue α is non-real (always, for trivial character), and it lies in the f̄-old U_p spectrum {p/α, χ̄(p)α}. So there is no contradiction.
  - The argument needs f new at p^s (the p-part of the character primitive). The U_p matching at p | level comes from local newform theory, not from JL Thm. 14.4.
  - Fix: add the p-new hypothesis and the right citation, or downgrade the sentence to \stsketch.
  - This item arose from the fix of M8b-3.

## Minors and notes (one line each; full rows in the file)
- X2: `\stformal` on θ as a ring hom from H_s. Lean has θ only on the generators (`HeckeSym`), and does not assume p ≥ 5.
- X3: the Lean scope of `lem:s05-consistency` is not declared in the chapter: (c) only the weights-agree form; (d) only s' = s+1 (Lean audit R2-5, R2-9; unfixed).
- X4: `Hyp.X.iso` is in HypX.lean, not XIso.lean.
- X6: the T05-2 scope sentence says naturality excludes the hybrid; (d) says it does not.
- X7: JL "Ch. XIV" does not exist. higherweight.tex still gives Thm. 14.4/15.1 at p. 470/471, unflagged. Both theorem numbers are verified; the pages do not match our PDF.
- X8: the body of `rem:s05-BN` ("up to a p-adic unit", "no factor 2", "norm-twisted form") contradicts `rem:s05-c2open`(v) and (vi), where the constant is φ(N)/2 with v_p = v_p(φ(M)) + s − 1.
- X9: N clash in (vi).
- X10: `lem:s05-consistency`(d) is tagged proved but uses the \stpmc Up-pullback lemma.
- X11: SGA 7 status is stale and contradictory between files. The scan is on our node; 2.4, (9.1.2), (10.3.5), 10.4 and 11.5 all verified.
- X12: the \stexp tag in `prop:s05-sign`(a) contradicts row 1 being \stpmc.
- Notes: X13 (qualifier order in (d)), X14 (w² = 1 should be stated in the AL proof), X15 (Helm Cor. 8.11 is a multiplicity statement; Hsieh's (CR) assumption), X16 (dirty provenance of T05-2/T05-3).

## Clean (re-derived, no finding)
- `lem:s05-normtwist` (a) and (b); the six-step list of `rem:s05-c2open`; the downgrade of (c2) to \stconj/\stopen; no statement uses (c2) as proved.
- The FD1/FD2 markers; the four-row Frobenius table (row 2 → 3 → 1 recomputed).
- `lem:s05-R1`, including (b) ⟨q⟩^{-1}U_q checked by Atkin–Li pseudo-eigenvalues; (c1); (d1)–(d3), with the Frobenius on the top and bottom pieces recomputed.
- Signs ε, e, δ; the factor 2.
- Levels and edge cases (s ≥ 1, Mp^s ≥ 4 including q = 2, 3, and s = 0 with M ≤ 4).
- Every `\lean{}` name exists at 7d67852, and there is no sorry, admit or axiom.
- All 95 `\lit` keys have a PDF on this node.

## Node resources (at 01:01Z)
- Mem: 15665 MB total, 5743 used, 3583 free, 8981 available.
- Swap: 2047 MB, 837 used.
- uptime 23:29, load 2.39 / 1.94 / 1.66.
