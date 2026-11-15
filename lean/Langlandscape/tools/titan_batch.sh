#!/usr/bin/env bash
# titan_batch.sh <spec-file>   (run from lean/Langlandscape/; stage-01 remote checks on TITAN)
# Spec file lines:  <WP-id> <file.lean> [<file.lean> ...]     (paths relative to lean/Langlandscape)
#                   AXIOMS <.titan/x.lean>                    (lfile'd after the build if its imports built)
# 1. one tools/lbuild.sh over all modules of all WPs (lake keeps going past failing modules);
# 2. tools/check_wp.sh per WP (build is a no-op then; adds sorry/forbidden-token/docstring checks);
# 3. tools/lfile.sh per AXIOMS file.  Output: .titan/out/{summary.txt,build.log,checkwp-<WP>.log,axioms-<n>.log}
set -u
spec="$1"; out=.titan/out; mkdir -p "$out"; : > "$out/summary.txt"
mods=(); while read -r wp rest; do
  case "$wp" in ''|\#*|AXIOMS) continue ;; esac
  for f in $rest; do m="${f%.lean}"; m="${m#Vendor/AxiomStacks/}"; mods+=("+${m//\//.}"); done
done < "$spec"
t0=$(date +%s); tools/lbuild.sh "${mods[@]}" > "$out/build.log" 2>&1; rc=$?
echo "BUILD rc=$rc wall=$(( $(date +%s)-t0 ))s" >> "$out/summary.txt"
[ "$rc" -eq 99 ] && { echo "PIN GUARD 99 — STOP" >> "$out/summary.txt"; exit 99; }
{ echo "## errors per file"; grep -oE 'error: [^ :]+\.lean:[0-9]+' "$out/build.log" | sed 's/error: //; s/:[0-9]*$//' | sort | uniq -c
  echo "## modules built / failed"; grep -E '(Built|Building|Replayed) (Langlandscape|LanglandscapeTests)\.' "$out/build.log" | sed -E 's/^.*(Built|Building|Replayed) /\1 /; s/ *\(.*//' ; } >> "$out/summary.txt"
while read -r wp rest; do
  case "$wp" in ''|\#*) continue ;; esac
  if [ "$wp" = AXIOMS ]; then n=$(basename "$rest" .lean); tools/lfile.sh "$rest" > "$out/axioms-$n.log" 2>&1
    echo "AXIOMS $rest rc=$? $(tools/axcount.sh "$out/axioms-$n.log" "$rest")" >> "$out/summary.txt"
  else tools/check_wp.sh $rest > "$out/checkwp-$wp.log" 2>&1; r=$?
    echo "CHECK_WP $wp rc=$r $(grep -c 'FAIL' "$out/checkwp-$wp.log") FAIL lines" >> "$out/summary.txt"; fi
done < "$spec"
echo "done: $out/summary.txt"
