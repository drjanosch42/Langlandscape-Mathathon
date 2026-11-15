#!/usr/bin/env bash
# tools/axcount.sh <axioms-log> <axioms.lean>
# Prints `printed=<p> expected=<e> nonstandard=<k>`: p = #`depends on axioms: [...]` + #`does not depend on any axioms`
# in the (whitespace-joined) log, e = #`^#print axioms` lines of the .lean file, k = #prints whose axiom set
# is not a subset of {propext, Classical.choice, Quot.sound}. printed != expected means a print was lost.
set -u
[ $# -eq 2 ] || { echo "usage: axcount.sh <axioms-log> <axioms.lean>" >&2; exit 1; }
j="$(tr -s '[:space:]' ' ' < "$1")"
exp=$(grep -c '^#print axioms' "$2")
dep=$(grep -oE 'depends on axioms: \[[^]]*\]' <<<"$j")
nod=$(grep -oE 'does not depend on any axioms' <<<"$j" | grep -c .)
p=$(grep -c . <<<"$dep"); p=$((p+nod))
k=0
while IFS= read -r l; do
  [ -n "$l" ] || continue
  l="${l#*[}"; l="${l%]}"
  IFS=',' read -ra a <<<"$l"
  for x in "${a[@]}"; do x="${x// /}"
    case "$x" in propext|Classical.choice|Quot.sound|'') ;; *) k=$((k+1)); break ;; esac
  done
done <<<"$dep"
echo "printed=$p expected=$exp nonstandard=$k"
