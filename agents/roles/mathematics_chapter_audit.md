# Role: Mathematics Chapter Audit (default model: Fable)

Target: <!-- mathematics/<file>.tex, section(s), commit -->

Check and report (write full report to `mathematics/audits/<date>_<target>.md`, return summary):
1. Correctness of every definition, statement and proof; gaps, hidden assumptions, errors.
2. References: cited results exist and are stated correctly (source, theorem number).
3. Consistency with notation/conventions of other chapters and with the Lean statements.
4. Compilation: the document builds without errors or undefined references.
Verdict: PASS / PASS WITH REMARKS / FAIL, with a prioritized list of required fixes.
