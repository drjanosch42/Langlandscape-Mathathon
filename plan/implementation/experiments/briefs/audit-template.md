You audit strand <X> of work package <WP-id> (track <T>, difficulty <d>). You are not told who wrote it.
Files: strand-<X>.patch (the full change), brief.md (the task), stage-excerpt.tex (the statements), check.txt
(acceptance-check output, run independently). <Round r ≥ 1: prior-findings.md — verify each prior finding as
RESOLVED / OPEN / REGRESSED, then audit the new diff.>
Report ONLY defects. For each: id A<r>.<n>, severity, file:line, problem, required fix. Severities:
  critical = wrong mathematics/statement, acceptance check failing, sorry/axiom/admit, interface name or signature
             different from the brief, edits outside the track directory or of frozen files;
  major    = missing required output, unproven claim in LaTeX, proof that only works by accident (e.g. heartbeats
             raised without reason), deviation from the stage-tex statement that is documented but unjustified;
  minor    = style, naming inside the file, docstring/reference gaps, readability.
Then score with the rubric (integers): correctness 0-4, completeness 0-2, interface fidelity 0-2, maintainability 0-2;
give one line of justification per criterion. End with: VERDICT: PASS | FAIL, and W = 3*crit + 2*major + minor.
Write audit-<X>-r<r>.md. Do not edit any other file. Do not guess the author.

Rubric anchors (Q = sum, 0-10):
| Criterion | top | middle | 0 |
|---|---|---|---|
| correctness (0-4) | 4: every statement and step checks; matches stage tex exactly | 2: local errors, fixable without redesign | 0: does not build / wrong main statement |
| completeness (0-2) | 2: all outputs of the brief, no `sorry`, all labels | 1: one output missing or stubbed | 0: most missing |
| interface fidelity (0-2) | 2: names, signatures, labels exactly as brief/stage tex | 1: deviations, documented | 0: undocumented deviations |
| maintainability (0-2) | 2: Mathlib/LaTeX/pytest conventions, docstring refs to `mathematics/`, robust proofs | 1: works but brittle/verbose | 0: unreadable / dead code |
Correctness 3 = correct with one non-trivial imprecision; 1 = a wrong statement or proof step that needs redesign.
