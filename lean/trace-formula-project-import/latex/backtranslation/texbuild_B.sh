#!/usr/bin/env bash
# Build document B of the fork. Output: ../build/algjl-B.pdf. Works in a scratch dir (nothing written into latex/).
# Usage: texbuild_B.sh [master.tex]   (default algjl.tex)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; LATEX="$(cd "$HERE/.." && pwd)"
MASTER="${1:-$HERE/algjl.tex}"; NAME="$(basename "$MASTER" .tex)"
TL="$HOME/texlive/2026/bin/x86_64-linux"; [ -x "$TL/lualatex" ] && export PATH="$TL:$PATH"
SCR="${TMPDIR:-/tmp}/algjl-B-scratch"; mkdir -p "$SCR" "$LATEX/build"
export TEXINPUTS=".:$HERE:$LATEX:$LATEX/shared:"   # items/ under $LATEX; generated/ under $HERE (tf@generateddir=backtranslation/generated/)
[ -n "${TEXFALLBACK:-}" ] && export TEXINPUTS="${TEXINPUTS%:}:$TEXFALLBACK:"   # test only: never for the final build
export BIBINPUTS="$LATEX/shared:"
# generated dir is looked up as backtranslation/generated/ relative to a TEXINPUTS entry:
ln -sfn "$HERE" "$SCR/backtranslation"
rm -f "$SCR"/*.aux "$SCR"/*.fdb_latexmk "$SCR"/*.fls "$SCR"/*.bbl "$SCR"/*.bcf "$SCR"/*.log "$SCR"/*.toc "$SCR"/*.out
cd "$SCR"
nice -n 10 latexmk -lualatex -interaction=nonstopmode -halt-on-error -file-line-error -silent -outdir="$SCR" "$MASTER" > "$SCR/$NAME.latexmk.out" 2>&1 || { grep -E '^[^:]+:[0-9]+:|^! ' "$SCR/$NAME.log" | head -20; echo FAILED; exit 1; }
grep -E 'undefined|multiply defined' "$SCR/$NAME.log" | sort -u | head -20 || true
cp "$SCR/$NAME.pdf" "$LATEX/build/$NAME-B.pdf"; echo "-> $LATEX/build/$NAME-B.pdf"
