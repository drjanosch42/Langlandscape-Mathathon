#!/usr/bin/env bash
# exp_lean_loop.sh <worktree> <model> <brief> <target.lean...>      (EXPERIMENT_PROTOCOL §7.3)
#   <worktree>  strand worktree  .../exp-s01-<wp>-<model>
#   <model>     muse | mistral | full opencode id
#   <brief>     path of briefs/<wp>.md (copied to <worktree>/.exp/brief.md)
#   <target>    paths relative to lean/Langlandscape/ (e.g. Langlandscape/Local/UpCosets.lean)
# Env: MAX_IT (6 routine / 10 hard; default 6), IT_TIMEOUT (15m), TOTAL_MIN (cap-25, default 60), EXP_EV.
# Per iteration: opencode run -> porcelain+pin check -> [flock exp.lock; lean/Langlandscape/tools/lfile.sh <t>]
#   -> sorry/admit/axiom grep. Exit 0 ok, 1 red (best iteration committed), 2 frozen (§7.2), 64 usage.
# lfile.sh interface (S01-X1a): `cd <wt>/lean/Langlandscape && tools/lfile.sh <path>`, prints `lfile: OK`, rc 99 = pin guard.
set -uo pipefail
# shellcheck source=exp_lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/exp_lib.sh"
[ "$#" -ge 4 ] || { echo "usage: $0 <worktree> <model> <brief> <target.lean...>" >&2; exit 64; }
WT="$(cd "$1" && pwd)"; MODEL="$2"; BRIEF="$(readlink -f "$3")"; shift 3
STRAND="$(strand_of "$WT")"; WP="${STRAND#s01-}"; WP="${WP%-*}"
MAX_IT="${MAX_IT:-6}"; IT_TIMEOUT="${IT_TIMEOUT:-15m}"; TOTAL_MIN="${TOTAL_MIN:-60}"; COMMIT_AREA="lean"
LEANDIR="lean/Langlandscape"
TARGETS=("$@"); ALLOWED=(); CONTEXT=()
for t in "${TARGETS[@]}"; do ALLOWED+=("$LEANDIR/$t"); done
export STRAND

lean_check() {
  local t t0 rc q tmp="$WT/.exp/lfile.out" qf="$WT/.exp/qwait" n slot
  CK_OK=1; CK_ERRS=0; CK_BUILD_S=0; CK_QUEUE_S=0; CK_FROZEN=0; : > "$CK_LOG"
  mkdir -p "$HOME/.cache/gl2tf"
  for t in "${TARGETS[@]}"; do
    if grep -nE '\bsorry\b|\badmit\b|^axiom' "$WT/$LEANDIR/$t" > "$tmp.sorry" 2>/dev/null; then
      { echo "$t: forbidden token (sorry/admit/axiom):"; cat "$tmp.sorry"; echo "$t:0:0: error: forbidden token"; } >> "$CK_LOG"
      CK_OK=0; CK_ERRS=$((CK_ERRS+1))
    fi
    if [ ! -e "$WT/$LEANDIR/$t" ]; then echo "$t:0:0: error: file missing" >> "$CK_LOG"; CK_OK=0; CK_ERRS=$((CK_ERRS+1)); continue; fi
    t0="$(now_s)"
    (  # lock order: exp.lock first (protocol §1.5); the wrapper takes the Lean locks itself
      exec 9>"$HOME/.cache/gl2tf/exp.lock"; flock 9
      echo $(( $(now_s) - t0 )) > "$qf"; date +%s > "$qf.start"
      cd "$WT/$LEANDIR" && tools/lfile.sh "$t"
    ) > "$tmp" 2>&1
    rc=$?
    CK_BUILD_S=$((CK_BUILD_S + $(now_s) - t0))
    q="$(cat "$qf" 2>/dev/null || echo 0)"
    # slot/memory wait printed by the wrapper (protocol §10): `slot acquired <ts>`; best effort
    slot="$(grep -m1 -oE 'slot acquired [^ ]+' "$tmp" | cut -d' ' -f3 || true)"
    if [ -n "$slot" ] && n="$(date -d "$slot" +%s 2>/dev/null)"; then q=$((q + n - $(cat "$qf.start" 2>/dev/null || echo "$n"))); fi
    CK_QUEUE_S=$((CK_QUEUE_S + q))
    { echo "=== lfile $t rc=$rc"; cat "$tmp"; } >> "$CK_LOG"
    if [ "$rc" = 99 ]; then CK_FROZEN=1; return 0; fi
    if [ "$rc" != 0 ] || ! grep -q 'lfile: OK' "$tmp"; then
      CK_OK=0; n="$(grep -c ': error' "$tmp" || true)"; CK_ERRS=$((CK_ERRS + (n > 0 ? n : 1)))
    fi
  done
  CK_SIG="$(err_sig ': error')"
}
check_fn() { lean_check; }
error_ctx_fn() {
  local t
  grep -nE 'error' "$CK_LOG" | head -150
  for t in "${TARGETS[@]}"; do
    echo "---- source context ($t) ----"
    grep -oE "${t//./\\.}:[0-9]+" "$CK_LOG" | cut -d: -f2 | sort -un | head -8 | while read -r ln; do
      echo "== $t:$ln"; sed -n "$((ln>10 ? ln-10 : 1)),$((ln+10))p" "$WT/$LEANDIR/$t"
    done
  done
}
loop_run
