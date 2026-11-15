#!/usr/bin/env bash
# tools/check_wp.sh <file.lean>...      (paths relative to lean/Langlandscape; run from anywhere)
#
# S01-X2 acceptance helper of every L-WP. Maps files to modules, runs ONE `tools/lbuild.sh +M ...`, then fails (exit 1) on
#   (1) `declaration uses 'sorry'` in the build log;
#   (2) the source grep  \bsorry\b | \badmit\b | ^axiom | native_decide | implemented_by  (comments included, on purpose);
#   (3) any theorem/lemma without a docstring (/-- ... -/ immediately before it, attributes allowed in between)
#       that contains an `sNN-` label (e.g. s01-, s02-); reported per declaration.
# Exit 0 = all clean; 1 = a check failed; 99 = propagated unchanged from a wrapper (pin guard / frozen tree): stop and alert.
set -uo pipefail
export GIT_OPTIONAL_LOCKS=0

proj="$(cd "$(dirname "$0")/.." && pwd)"
cd "$proj" || exit 1
[ $# -ge 1 ] || { echo "usage: check_wp.sh <file.lean>..." >&2; exit 1; }

fail=0
mods=()
files=()
for f in "$@"; do
  f="${f#./}"; f="${f#"$proj"/}"
  case "$f" in *.lean) ;; *) echo "check_wp: not a .lean file: $f" >&2; exit 1 ;; esac
  [ -f "$f" ] || { echo "check_wp: no such file: $f" >&2; exit 1; }
  m="${f%.lean}"
  case "$m" in
    Vendor/AxiomStacks/*) m="${m#Vendor/AxiomStacks/}" ;;
  esac
  mods+=("+${m//\//.}")
  files+=("$f")
done

log="$(mktemp "${TMPDIR:-/tmp}/check_wp.XXXXXX")"
trap 'rm -f "$log"' EXIT

echo "check_wp: tools/lbuild.sh ${mods[*]}"
tools/lbuild.sh "${mods[@]}" 2>&1 | tee "$log"
rc=${PIPESTATUS[0]}
if [ "$rc" -eq 99 ]; then echo "check_wp: lbuild exit 99 (pin guard / frozen tree): STOP, alert the global master" >&2; exit 99; fi
if [ "$rc" -ne 0 ]; then echo "check_wp: FAIL: lbuild exit $rc" >&2; fail=1; fi

if grep -n "declaration uses 'sorry'" "$log"; then
  echo "check_wp: FAIL: build log contains \"declaration uses 'sorry'\"" >&2; fail=1
fi

for f in "${files[@]}"; do
  if grep -nE '\bsorry\b|\badmit\b|^axiom|native_decide|implemented_by' "$f" | sed "s|^|$f:|"  | grep .; then
    echo "check_wp: FAIL: forbidden token in $f" >&2; fail=1
  fi
done

python3 -I - "${files[@]}" <<'PY' || fail=1
import re, sys
MOD = r'(?:(?:private|protected|nonrec|noncomputable|unsafe|partial)\s+)*'
ATTR_LINE = re.compile(r'^\s*@\[.*\]\s*$')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*' + MOD + r'(theorem|lemma)\b')
bad = 0
for path in sys.argv[1:]:
    if path == 'Langlandscape/Smoke.lean':
        continue  # frozen regression test of S01-X1a (README); its theorem predates the sNN- docstring convention
    lines = open(path, encoding='utf-8').read().split('\n')
    for i, ln in enumerate(lines):
        m = DECL.match(ln)
        if not m:
            continue
        j = i - 1
        # attribute-only lines (possibly multi-line @[ ... ]) directly before the declaration
        while j >= 0:
            if ATTR_LINE.match(lines[j]):
                j -= 1
            elif lines[j].rstrip().endswith(']') and not lines[j].lstrip().startswith('@['):
                k = j
                while k >= 0 and '@[' not in lines[k]:
                    k -= 1
                if k >= 0 and lines[k].lstrip().startswith('@['):
                    j = k - 1
                else:
                    break
            else:
                break
        ok = False
        if j >= 0 and lines[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and '/-' not in lines[k]:
                k -= 1
            if k >= 0 and '/--' in lines[k]:
                doc = '\n'.join(lines[k:j + 1])
                ok = re.search(r's[0-9][0-9]-', doc) is not None
        if not ok:
            bad += 1
            name = re.sub(r'^\s*(?:@\[[^\]]*\]\s*)*' + MOD + r'(?:theorem|lemma)\s+', '', ln).split()[0:1]
            print(f"check_wp: FAIL: {path}:{i+1}: {m.group(1)} {name[0] if name else '?'}: no docstring containing an 'sNN-' label immediately before it", file=sys.stderr)
sys.exit(1 if bad else 0)
PY

if [ "$fail" -ne 0 ]; then echo "check_wp: FAILED" >&2; exit 1; fi
echo "check_wp: OK (${#files[@]} file(s))"
