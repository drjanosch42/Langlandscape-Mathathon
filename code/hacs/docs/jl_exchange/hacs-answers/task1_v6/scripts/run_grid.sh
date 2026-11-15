#!/bin/bash
# SPDX-License-Identifier: CC-BY-4.0
# Task 1 grid: p in {3,5,7,11,13}, k in {4,...,14} even; anchors add l = 17 (p=3,k=12) and l = 29, 131 (p=5,k=12).
set -e
S=$(dirname "$0"); OUT=${1:-$S/../data/cells}; mkdir -p "$OUT"
for p in 3 5 7 11 13; do for k in ${KS:-4 6 8 10 12 14}; do
  extra=""; [ "$p,$k" = "3,12" ] && extra="17"; [ "$p,$k" = "5,12" ] && extra="29 131"
  /usr/bin/time -f "%e %M" -o "$OUT/time_p${p}_k${k}.txt" nice -n 19 python3 "$S/cell.py" $p $k $extra --out "$OUT/cell_p${p}_k${k}.json" > /dev/null
  echo "p=$p k=$k wall_s,rss_kb=$(cat $OUT/time_p${p}_k${k}.txt)"
done; done
