#!/usr/bin/env bash
# exp_py_loop.sh <worktree> <model> <brief> <pytest-target> <out-file...>        (EXPERIMENT_PROTOCOL §7.3 analogue)
#   <pytest-target>  path relative to <worktree>/$PY_DIR (default code/python), e.g. tests/test_s01_classset.py;
#                    it is also writable by the model (tests are part of the WP unless the brief says otherwise,
#                    set PY_TEST_READONLY=1 to forbid)
#   <out-file...>    all other files the model may write, relative to the worktree root
# Env: PY_DIR (code/python), MAX_IT (4), IT_TIMEOUT (15m), TOTAL_MIN (60), EXP_EV.
# Check = `pytest -q <target>` exit 0 and at least one test passed. Exit 0 ok, 1 red, 2 frozen, 64 usage.
set -uo pipefail
# shellcheck source=exp_lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/exp_lib.sh"
[ "$#" -ge 5 ] || { echo "usage: $0 <worktree> <model> <brief> <pytest-target> <out-file...>" >&2; exit 64; }
WT="$(cd "$1" && pwd)"; MODEL="$2"; BRIEF="$(readlink -f "$3")"; PYT="$4"; shift 4
STRAND="$(strand_of "$WT")"; WP="${STRAND#s01-}"; WP="${WP%-*}"
MAX_IT="${MAX_IT:-4}"; IT_TIMEOUT="${IT_TIMEOUT:-15m}"; TOTAL_MIN="${TOTAL_MIN:-60}"; COMMIT_AREA="code"
PY_DIR="${PY_DIR:-code/python}"
ALLOWED=("$@"); CONTEXT=()
[ "${PY_TEST_READONLY:-0}" = 1 ] || ALLOWED=("$PY_DIR/$PYT" "${ALLOWED[@]}")
export STRAND

py_check() {
  local t0 rc n
  CK_OK=1; CK_ERRS=0; CK_BUILD_S=0; CK_QUEUE_S=0; CK_FROZEN=0; : > "$CK_LOG"
  t0="$(now_s)"
  ( cd "$WT/$PY_DIR" && timeout 20m pytest -q -x -p no:cacheprovider "$PYT" ) > "$WT/.exp/pytest.out" 2>&1
  rc=$?
  CK_BUILD_S=$(( $(now_s) - t0 ))
  { echo "=== pytest rc=$rc"; cat "$WT/.exp/pytest.out"; } >> "$CK_LOG"
  if [ "$rc" != 0 ] || ! grep -qE '[0-9]+ passed' "$WT/.exp/pytest.out"; then
    CK_OK=0; n="$(grep -cE '^(FAILED|ERROR)|Error' "$WT/.exp/pytest.out" || true)"; CK_ERRS=$(( n > 0 ? n : 1 ))
  fi
  CK_SIG="$(grep -E '^(FAILED|ERROR)|^E ' "$WT/.exp/pytest.out" | sed -E 's/[0-9.]+s//g' | sort | cksum | cut -d' ' -f1)"
}
check_fn() { py_check; }
loop_run
