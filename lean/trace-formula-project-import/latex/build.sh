#!/usr/bin/env bash
# build.sh -- build the fork's PDFs: A (readable/algjl.tex) and/or B (backtranslation/algjl.tex).
# Usage: latex/build.sh [A|B|all]   (default all; B first, because A reads B's .aux for the "in B" links)
# Output: latex/build/A/algjl.pdf, latex/build/B/algjl.pdf. Never writes into the source folders.
# Self-contained: TEXINPUTS/BIBINPUTS point only into algebraic_jl/latex/. Not a Lean process (rules 7-9 do not apply).
set -euo pipefail
LX="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TL_BIN="${GL2TF_TEXLIVE_BIN:-}"
[ -z "$TL_BIN" ] && [ -d "$HOME/texlive/2026/bin/x86_64-linux" ] && TL_BIN="$HOME/texlive/2026/bin/x86_64-linux"
[ -n "$TL_BIN" ] && export PATH="$TL_BIN:$PATH"
export TEXINPUTS=".:$LX:$LX/shared:"
export BIBINPUTS="$LX/shared:"
# One fork TeX build at a time (A reads B's .aux; concurrent runs would read a half-written file).
mkdir -p "$LX/build"
if [ -z "${ALGJL_TEX_LOCK_HELD:-}" ]; then
  export ALGJL_TEX_LOCK_HELD=1
  exec flock -x -w 1800 "$LX/build/.texlock" "$0" "$@"
fi
case "${1:-all}" in A) EDS="A";; B) EDS="B";; all) EDS="B A";; *) echo "usage: $0 [A|B|all]" >&2; exit 2;; esac
status=0
for ed in $EDS; do
  case $ed in A) src="$LX/readable";; B) src="$LX/backtranslation";; esac
  [ -f "$src/algjl.tex" ] || { echo "skip $ed: $src/algjl.tex missing"; continue; }
  out="$LX/build/$ed"; mkdir -p "$out"
  # A: snapshot of B's .aux (labels for the "in B" links), taken under the lock
  if [ "$ed" = A ]; then
    if [ -f "$LX/build/B/algjl.aux" ]; then cp "$LX/build/B/algjl.aux" "$out/Bref.aux"; else rm -f "$out/Bref.aux"; fi
  fi
  ( cd "$src" && nice -n 10 latexmk -lualatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -outdir="$out" algjl.tex >"$out/latexmk.out" 2>&1 ) || { echo "$ed: LaTeX error, see $out/algjl.log"; status=1; continue; }
  log="$out/algjl.log"
  if grep -qE 'There were undefined references|Citation .* undefined|multiply defined|Reference .* undefined' "$log"; then
    echo "$ed: warnings (undefined/multiply defined), see $log"; status=1
  fi
  echo "$ed: $out/algjl.pdf"
done
exit $status
