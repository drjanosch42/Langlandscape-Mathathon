# Role: Lean Audit (default model: Fable; adversarial variant may alternate with Opus)

Target: <!-- files / modules, branch, commit -->
Mathematical reference: <!-- mathematics/... section -->

Check and report (write full report to `lean/audits/<date>_<target>.md`, return summary):
1. Build: `lake build` succeeds on the stated toolchain; list all warnings.
2. Soundness: no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide` unless
   explicitly listed and justified; `#print axioms` of main theorems.
3. Faithfulness: each main statement matches the mathematical statement exactly
   (hypotheses, quantifiers, coercions, edge cases). Flag vacuous or weakened statements.
4. Quality: Mathlib conventions, naming, reusable lemmas, dead code.
Verdict: PASS / PASS WITH REMARKS / FAIL, with a prioritized list of required fixes.
