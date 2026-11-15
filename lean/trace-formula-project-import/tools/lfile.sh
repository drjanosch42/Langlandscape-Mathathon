#!/usr/bin/env bash
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/lfile.sh @84818d0, unchanged except this line: repo resolves to algebraic_jl/, lean dir = algebraic_jl/lean.
# tools/lfile.sh <file.lean>
#
# Single-file check (`lake env lean <file>`), PLAN.md §5.3 / D8:
#   - lean.lock SHARED (flock -s -w 7200), so never during a build;
#   - then one of $SLOTS (=2) slot locks slot.1, slot.2 (flock -n on each, retry every 10 s, up to 7200 s);
#   - MemAvailable >= FILE_MEM_MIN_KB (16 GB = deps.conf MEM_MIN_KB; a committed load profile may lower it, T-D25c), else retry every 5 min;
#   - dry no-rebuild check restricted to the file's dependency imports (check_frozen.sh --file);
#   - systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=2 lake env lean;
#   - post-flight find-newer on the frozen trees (exit 99 = frozen tree written: stop everything, alert the lead).
#
# Note: `lake env lean` does not build anything. If the file imports project modules (GL2TF.*), their .olean
# files must already exist from an earlier tools/lbuild.sh run; otherwise Lean reports "object file ... not found".
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
unset LAKE_PKG_URL_MAP || true

repo="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=deps.conf
source "$repo/tools/deps_load.sh"
lean="$repo/lean"

die() { echo "lfile: ABORT: $*" >&2; exit 1; }

[ $# -eq 1 ] || die "usage: lfile.sh <file.lean>"
file="$(realpath "$1")"
[ -f "$file" ] || die "no such file $1"
case "$file" in
  "$lean"/.lake/*) die "refusing to check a file inside lean/.lake" ;;
  "$lean"/*.lean) ;;
  *) die "$file is not a .lean file under $lean" ;;
esac
rel="${file#"$lean"/}"

command -v systemd-run >/dev/null || die "systemd-run not found; refusing to run without the memory cap"
systemd-run --user --scope --quiet -p MemoryMax=64M true >/dev/null 2>&1 \
  || die "systemd-run --user --scope does not work here; refusing to run without the memory cap"

mkdir -p "$LOCK_DIR/markers"
exec 9>"$LOCK_DIR/lean.lock"
flock -s -w "$LOCK_WAIT" 9 || die "could not get the shared lock in ${LOCK_WAIT}s (a build is running?)"

slot=""
waited=0
while [ -z "$slot" ]; do
  for s in $(seq 1 "$SLOTS"); do
    exec 7>"$LOCK_DIR/slot.$s"
    if flock -n 7; then slot="$s"; break; fi
    exec 7>&-
  done
  [ -n "$slot" ] && break
  [ "$waited" -ge "$LOCK_WAIT" ] && die "no free check slot after ${LOCK_WAIT}s"
  sleep 10; waited=$((waited + 10))
done
export GL2TF_LOCK_HELD="shared+slot.$slot"

while :; do
  avail="$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)"
  [ "$avail" -ge "$FILE_MEM_MIN_KB" ] && break
  echo "lfile: MemAvailable ${avail} kB < ${FILE_MEM_MIN_KB} kB; retrying in 5 min ($(date +%T))"
  sleep 300
done

"$repo/tools/check_frozen.sh" --file "$file" >/dev/null || exit $?

marker="$(mktemp "$LOCK_DIR/markers/file.XXXXXX")"
touch "$marker"
sleep 1
cd "$lean"
# T-M10b-W0-1: `lake env lean` ignores the package leanOptions, so pass them (top-level [leanOptions] of lakefile.toml) as -D flags.
lopts=()
while IFS= read -r o; do [ -n "$o" ] && lopts+=("$o"); done < <(python3 - "$lean/lakefile.toml" <<'PY'
import re, sys
sec = None
for line in open(sys.argv[1], encoding="utf-8"):
    line = line.split("#", 1)[0].strip()
    m = re.fullmatch(r"\[\[?([^\]]+)\]\]?", line)
    if m:
        sec = m.group(1).strip()
    elif sec == "leanOptions" and "=" in line:
        k, v = (x.strip() for x in line.split("=", 1))
        print(f"-D{k}={v.strip(chr(34))}")
PY
)
set +e
systemd-run --user --scope --quiet -p MemoryMax="$FILE_MEMORY_MAX" -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS="$LEAN_THREADS" lake env lean "${lopts[@]}" "$rel"
rc=$?
set -e
"$repo/tools/check_frozen.sh" --post "$marker" >/dev/null || exit $?
rm -f "$marker"
[ "$rc" -eq 0 ] && echo "lfile: OK $rel (slot $slot)" || echo "lfile: FAILED $rel (rc=$rc, slot $slot)" >&2
exit "$rc"
