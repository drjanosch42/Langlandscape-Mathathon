# Rule: mathematics/

- LaTeX sources; one main document (`mathematics/main.tex`) with chapters in `mathematics/chapters/`.
- Bibliography in `mathematics/references.bib`; cite precisely (source + theorem/section number).
- Mark every result's status: proved here / cited / conjectural; cross-reference Lean names
  (`\lean{Namespace.theorem}`) where formalized.
- Must compile with `latexmk -pdf` without errors; build artefacts are not committed.
- A chapter is done only after `agents/roles/mathematics_chapter_audit.md` passes.
