<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Flattening tool for the submission report

`flatten.py` turns the modular report sources into the single self-contained `mathematics/submission/report.tex`
(official rule: one `.tex`, no `\input`, no `.bib`, bibliography and appendix inside, no images, no pdfpages).
Python 3 standard library only; `pdflatex` is needed for the self-test.

## Usage

    cd mathematics/submission
    python3 tools/flatten.py src/report-src.tex                # -> report.tex, report.pdf, rule checks
    python3 tools/flatten.py src/report-src.tex --draft        # placeholders / title-block gaps are WARN, not FAIL
    python3 tools/flatten.py --check report.tex [--build]      # only the rule checks (see ../CHECKLIST.md)
    # dry run on the existing report (it still uses pdfpages for its appendix):
    python3 tools/flatten.py ../final-report/final-report.tex -o /scratch/report.tex --hyp-appendix --draft

Options: `-o OUT`, `--root DIR` (extra search directory, repeatable), `--hyp-appendix` (replace
`\includepdf{...standalone-hypotheses.pdf}` by the TEXT of `report/hypotheses.tex`, plus `report/hyp-preamble.tex` and
`report/hypotheses.bib`), `--pdf-substitute PDF=TEX[:PREAMBLE[:BIB]]`, `--allow-images`, `--no-build`, `--idword W`,
`--idwords-file F`, `--keep-copyright`, `--keep-bib-local`, `--keep-going`, `-v`.
Exit status is 0 only if flattening had no errors and no check FAILed.

## What it does

1. **Inlining.** `\input`, `\include`, `\subfile`, the primitive `\@@input name`, `\IfFileExists{f}{yes}{no}`,
   `\InputIfFileExists` (decided at flatten time) and `\usepackage` of local `.sty` files. A path is searched in
   the main file's directory (TeX's cwd), the including file's directory, then all ancestor directories up to the
   git root, so both `../preamble` and `report/hypotheses` (relative to `mathematics/`) resolve. An `\input` that
   sits inside an argument or a macro body is inlined without blank lines (no `\par`); the primitive form also doubles `#`.
2. **Comments** are removed (`\%`, `\verb`, verbatim/lstlisting and `comment` environments are respected;
   a trailing comment becomes a bare `%`). Kept: the SPDX line; the copyright line is anonymised
   (`--keep-copyright` keeps the names), because the report must not identify the authors outside the title block.
3. **Bibliography.** `biblatex`, `\addbibresource`, `\bibliography`, `\printbibliography` are removed; all
   `\cite/\parencite/\textcite/\autocite/\footcite/\citep/\citet/\fullcite` become plain `\cite[note]{keys}` (two optional
   arguments are merged). Only cited keys are emitted, as `\begin{thebibliography}` with alphabetic labels (`[Ser77]`),
   from a small built-in `.bib` parser (`@string`, `#`, `crossref`, `date`, `journaltitle`, ...). Cited keys without a
   `.bib` entry are an error. `\lit{..}{..}` in `preamble.tex` is NOT a citation (it prints a `literature/` path); it
   is left alone. Internal `local: literature/x.pdf` notes in `.bib` `note` fields are dropped unless `--keep-bib-local`.
4. **Forbidden things.** `\includepdf`/pdfpages: error unless substituted. `\includegraphics`: error unless `--allow-images`.
   `\documentclass` inside an included file, include cycles, missing files: error. Output is written only without errors.
5. **Figures.** Every `figure` environment and bare `tikzpicture` is listed on stderr with its flat-file line, label and
   caption length (a caption of >= 12 words counts as the text description; a bare tikzpicture needs an adjacent
   description paragraph, checked by hand).
6. **Self-test.** `report.tex` alone is copied to a temp dir and compiled with `pdflatex` (2-3 passes); errors,
   undefined citations/references, multiply defined labels and missing files fail the check. The PDF is copied next to
   `report.tex` (plus `report.log`). Then the rule checks run (`CHECKLIST.md`).

## Limits

Citation labels are generated, not biblatex's; `\citeauthor`-style commands are not supported (none are used). `\iffalse`
blocks are not stripped. Conditionals around `\IfFileExists` inside macro bodies are decided at flatten time.
`\input` with `\jobname`-style computed names is not supported. Title-block detection for the checks:
from the first `\title/\author/\address/\email` to `\maketitle`.

## References into the chapters (`--external-aux`)

The report's text (e.g. `chapters/s00/*.tex`) refers with `\ref`, `\eqref`, `\cref`, `\Cref`, `\autoref`, `\vref`,
`\pageref`, `\hyperref` to labels that only exist in the chapters. Build their numbers once:
`cd mathematics && latexmk -pdf main.tex` (or just `pdflatex main.tex` twice) gives `mathematics/main.aux`, which is the
default for `--external-aux PATH`. For a label `L` not `\label`ed in the flat report:

1. the report defines `rpt:L` (its own copy of the statement): `\ref{L}` becomes `\ref{rpt:L} [chapters, Thm~21.5]`;
2. else `L` is in `main.aux`: it becomes plain `[chapters, Thm~21.5]` (a preceding `Thm.~` is dropped); each such label
   is a WARN (check item A12; also summarised at the end of a flatten run: statement not in the report);
3. else it stays and `--check` FAILs (item X1, unresolved reference; the compile fails as well).

`\hyperref[L]{text}` becomes `text` in cases 1-2. Pointer format: `[chapters, <Thm|Prop|Cor|Lem|Rem|Hyp|Def|Sec|Eq|...>~N]`
with N the number in `main.pdf`; the kind comes from the label prefix (`thm:`, `prop:`, ...), else from the aux anchor.
Comment lines, including the licence/copyright comments of inlined files, are always stripped; only the SPDX line of the
main file is kept (its copyright line is anonymised), so author names never come in through included files.
