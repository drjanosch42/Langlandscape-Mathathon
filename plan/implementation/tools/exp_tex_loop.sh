#!/usr/bin/env bash
# exp_tex_loop.sh <worktree> <model> <brief> <target.tex> <label,label,...>      (EXPERIMENT_PROTOCOL §7.3 analogue)
#   <target>  path relative to <worktree>/$TEX_DIR (default mathematics), e.g. chapters/s01/2-mass.tex
#   labels    comma list of tex labels that must each be defined exactly once in $TEX_SRC_GLOB
# Env: TEX_DIR (mathematics), TEX_MAIN (main.tex), TEX_SRC_GLOB (chapters/s01/*.tex), TEX_ALLOW_NEW (regex of
#   labels the WP may add, default none), MAX_IT (4), IT_TIMEOUT (15m), TOTAL_MIN (60), EXP_EV.
# Check = latexmk exit 0 + no 'undefined' in main.log + required labels exactly once + label set unchanged against
#   the branch base (except TEX_ALLOW_NEW) + every \stcited has a \lit. Then `latexmk -c`.
# Exit 0 ok, 1 red (best iteration committed), 2 frozen, 64 usage.
set -uo pipefail
# shellcheck source=exp_lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/exp_lib.sh"
[ "$#" -eq 5 ] || { echo "usage: $0 <worktree> <model> <brief> <target.tex> <label,label,...>" >&2; exit 64; }
WT="$(cd "$1" && pwd)"; MODEL="$2"; BRIEF="$(readlink -f "$3")"; TGT="$4"; LABELS="$5"
STRAND="$(strand_of "$WT")"; WP="${STRAND#s01-}"; WP="${WP%-*}"
MAX_IT="${MAX_IT:-4}"; IT_TIMEOUT="${IT_TIMEOUT:-15m}"; TOTAL_MIN="${TOTAL_MIN:-60}"; COMMIT_AREA="mathematics"
TEX_DIR="${TEX_DIR:-mathematics}"; TEX_MAIN="${TEX_MAIN:-main.tex}"; TEX_SRC_GLOB="${TEX_SRC_GLOB:-chapters/s01/*.tex}"
TEX_ALLOW_NEW="${TEX_ALLOW_NEW:-^$}"
ALLOWED=("$TEX_DIR/$TGT"); CONTEXT=()
export STRAND
BASE="$(git -C "$WT" rev-parse HEAD)"     # state at loop start = branch base for the label-set comparison

tex_sources() {
  # shellcheck disable=SC2086  # the glob is intended
  ( cd "$WT/$TEX_DIR" && cat $TEX_SRC_GLOB )
}

tex_check() {
  local t0 l n
  CK_OK=1; CK_ERRS=0; CK_BUILD_S=0; CK_QUEUE_S=0; CK_FROZEN=0; : > "$CK_LOG"
  t0="$(now_s)"
  ( cd "$WT/$TEX_DIR" && latexmk -pdf -interaction=nonstopmode "$TEX_MAIN" ) > "$WT/.exp/latexmk.out" 2>&1
  local rc=$?
  CK_BUILD_S=$(( $(now_s) - t0 ))
  { echo "=== latexmk rc=$rc"; grep -nE '^!|Error|undefined|Undefined' "$WT/.exp/latexmk.out" | head -80; } >> "$CK_LOG"
  [ "$rc" = 0 ] || { echo "$TGT:0:0: error: latexmk exit $rc" >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }
  local log="$WT/$TEX_DIR/${TEX_MAIN%.tex}.log"
  n="$(grep -c 'undefined' "$log" 2>/dev/null || true)"; n="${n:-0}"
  [ "$n" = 0 ] || { { echo "$TGT:0:0: error: $n 'undefined' in main.log"; grep -n 'undefined' "$log" | head -20; } >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }
  for l in ${LABELS//,/ }; do
    n="$(tex_sources | grep -c "\\\\label{$l}" || true)"
    [ "$n" = 1 ] || { echo "$TGT:0:0: error: label $l defined $n times (need exactly 1)" >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }
  done
  # label set unchanged against base (except TEX_ALLOW_NEW)
  local now base
  now="$(tex_sources | grep -o '\\label{[^}]*}' | sort -u)"
  base="$(git -C "$WT" grep -ohE '\\label\{[^}]*\}' "$BASE" -- "$TEX_DIR/${TEX_SRC_GLOB%/*}" 2>/dev/null | sort -u)"
  if [ -n "$base" ]; then
    while IFS= read -r l; do [ -n "$l" ] && { echo "$TGT:0:0: error: tex label removed: $l" >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }; done < <(comm -23 <(echo "$base") <(echo "$now"))
    while IFS= read -r l; do
      [ -n "$l" ] || continue
      echo "$l" | grep -qE "$TEX_ALLOW_NEW" || { echo "$TGT:0:0: error: tex label added: $l" >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }
    done < <(comm -13 <(echo "$base") <(echo "$now"))
  fi
  # every \stcited has a \lit (same or next line)
  awk '/\\stcited/{ if ($0 !~ /\\lit\{/) { if ((getline nx) > 0 && nx !~ /\\lit\{/) bad++ } } END{exit bad>0}' "$WT/$TEX_DIR/$TGT" \
    || { echo "$TGT:0:0: error: \\stcited without \\lit" >> "$CK_LOG"; CK_ERRS=$((CK_ERRS+1)); }
  ( cd "$WT/$TEX_DIR" && latexmk -C "$TEX_MAIN" ) > /dev/null 2>&1
  # no build products besides the target: scope_check reverts the rest
  [ "$CK_ERRS" = 0 ] || CK_OK=0
  CK_SIG="$(err_sig 'error')"
}
check_fn() { tex_check; }
loop_run
