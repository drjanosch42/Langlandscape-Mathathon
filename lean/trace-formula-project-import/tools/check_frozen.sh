#!/usr/bin/env bash
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/check_frozen.sh @84818d0, unchanged except this line: repo resolves to algebraic_jl/, lean dir = algebraic_jl/lean.
# tools/check_frozen.sh [--file <lean file>] | --post <marker> | --sweep <marker> [tree...] | --around <cmd...>
#
# Dry no-rebuild check (CLAUDE.md rule 5, PLAN.md §5.3):
#   1. tools/link_deps.sh --verify (manifest revs/URLs = frozen checkouts, links in place);
#   2. touch a marker; ONE `lake build --no-build +M1 +M2 ...` over every dependency module (Mathlib, Batteries,
#      Aesop, ...; see DEP_ROOTS) imported anywhere in lean/ (or, with --file, by that file only), plus the
#      sentinel +Mathlib.Init; anything other than "All targets up-to-date" aborts;
#   3. `find <frozen tree> -newer <marker> -print -quit` must print nothing.
# --post <marker>  only step 3 against an existing marker (used by lbuild.sh / lfile.sh after their run).
#
# --sweep <marker> [tree...]  MIG w4 (incident 2): step 3 over FROZEN_TREES + SWEEP_EXTRA_TREES (deps.conf; the
#   partial-clone Mathlib v4.35 among them) or the given trees, AND an explicit sweep of every tree's `.git`
#   (objects, packs, refs, index, FETCH_HEAD, ...): anything inside `.git` newer than the marker is an ERROR (99), also
#   when the worktree is untouched. Meant to run around ANY command (git, grep, a build): `--mark <file>` touches a
#   marker (e.g. tools/state/mig.marker), `--around <cmd...>` is mark + command + sweep, exiting with the command's
#   status or 99.
# Exit codes: 0 ok; 1 not up-to-date / setup error; 99 A FROZEN TREE WAS WRITTEN (stop everything, alert the lead).
# Lock: takes lean.lock shared unless the caller already holds the lock (GL2TF_LOCK_HELD set by lbuild/lfile).
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
unset LAKE_PKG_URL_MAP || true

repo="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=deps.conf
source "$repo/tools/deps_load.sh"
lean="$repo/lean"

die() { echo "check_frozen: ABORT: $*" >&2; exit 1; }

post_check() {
  local marker="$1" hit
  [ -f "$marker" ] || die "marker $marker missing"
  for t in $FROZEN_TREES; do
    [ -d "$t" ] || { echo "check_frozen: !!!!! frozen tree $t is missing; cannot verify it. STOP AND ALERT THE LEAD." >&2; exit 99; }
    # find errors (unreadable directories) mean the tree cannot be verified: treat like a write (M0-G3 MINOR-11)
    # A bare mtime change of a `.git` directory itself (transient lock file created/removed by another process
    # sharing the tree) is not a modification; anything inside it (index, refs, ...) and every worktree file is.
    if ! hit="$(find "$t" -newer "$marker" ! \( -name .git -type d \) -print -quit)"; then
      echo "check_frozen: !!!!! find failed on $t: the frozen tree could not be verified. STOP AND ALERT THE LEAD." >&2
      exit 99
    fi
    if [ -n "$hit" ]; then
      echo "check_frozen: !!!!! FROZEN TREE WRITTEN: $hit (newer than $marker)" >&2
      echo "check_frozen: !!!!! STOP ALL AGENTS AND ALERT THE LEAD AND THE USER." >&2
      exit 99
    fi
    hit="$(find "$t" -name .git -type d -newer "$marker" -print -quit 2>/dev/null || true)"
    [ -z "$hit" ] || echo "check_frozen: notice: only the mtime of the .git directory itself changed ($hit); not counted as a modification" >&2
  done
  echo "check_frozen: frozen trees untouched since $(basename "$marker")"
}

sweep_git() {  # sweep_git <marker> <tree...>: anything inside <tree>/.git newer than the marker is an error
  local marker="$1" t hit
  shift
  [ -f "$marker" ] || die "marker $marker missing"
  for t in "$@"; do
    [ -e "$t/.git" ] || continue
    if ! hit="$(find "$t/.git" -mindepth 1 -newer "$marker" -print -quit)"; then
      echo "check_frozen: !!!!! find failed on $t/.git: cannot verify it. STOP AND ALERT THE LEAD." >&2; exit 99
    fi
    if [ -n "$hit" ]; then
      echo "check_frozen: !!!!! .git OF A FROZEN TREE WRITTEN: $hit (newer than $marker)" >&2
      echo "check_frozen: !!!!! STOP ALL AGENTS AND ALERT THE LEAD AND THE USER." >&2
      exit 99
    fi
  done
}

sweep_all() {  # sweep_all <marker> [tree...]
  local marker="$1"; shift
  local trees=("$@") t
  if [ "${#trees[@]}" -eq 0 ]; then
    trees=($FROZEN_TREES)
    for t in ${SWEEP_EXTRA_TREES:-}; do [ -d "$t" ] && trees+=("$t"); done
  fi
  sweep_git "$marker" "${trees[@]}"
  FROZEN_TREES="${trees[*]}" post_check "$marker"
}

case "${1:-}" in
  --mark) [ -n "${2:-}" ] || die "--mark needs a file"; touch "$2"; sleep 1; echo "check_frozen: marker $2 set"; exit 0 ;;
  --sweep) [ -n "${2:-}" ] || die "--sweep needs a marker"; m="$2"; shift 2; sweep_all "$m" "$@"; exit 0 ;;
  --around)
    shift; [ "$#" -gt 0 ] || die "--around needs a command"
    mkdir -p "$LOCK_DIR/markers"; am="$(mktemp "$LOCK_DIR/markers/around.XXXXXX")"; touch "$am"; sleep 1
    set +e; "$@"; arc=$?; set -e
    sweep_all "$am"; rm -f "$am"; exit "$arc" ;;
esac

if [ "${1:-}" = "--post" ]; then
  [ -n "${2:-}" ] || die "--post needs a marker"
  post_check "$2"
  exit 0
fi

file=""
if [ "${1:-}" = "--file" ]; then
  [ -n "${2:-}" ] || die "--file needs a path"
  file="$(realpath "$2")"
  [ -f "$file" ] || die "no such file $2"
elif [ -n "${1:-}" ]; then
  die "unknown argument $1"
fi

mkdir -p "$LOCK_DIR/markers"
if [ -z "${GL2TF_LOCK_HELD:-}" ]; then
  exec 8>"$LOCK_DIR/lean.lock"
  flock -s -w "$LOCK_WAIT" 8 || die "could not get the shared lock $LOCK_DIR/lean.lock in ${LOCK_WAIT}s"
fi

"$repo/tools/link_deps.sh" --verify >/dev/null || die "link_deps --verify failed"

# Collect the dependency modules imported by the given file, or by every .lean file under lean/ (not .lake).
if [ -n "$file" ]; then
  files=("$file")
else
  mapfile -t files < <(find "$lean" -path "$lean/.lake" -prune -o -name '*.lean' -print | sort)
fi
mapfile -t mods < <(
  for f in "${files[@]}"; do
    # import lines: optional `public`/`private`/`meta` prefixes, one or more modules per line
    sed -nE 's/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+(.*)$/\3/p' "$f" \
      | sed -E 's/--.*$//; s/«//g; s/»//g' | tr -s ' \t' '\n'
  done | awk -v roots="$DEP_ROOTS" '
    BEGIN { n = split(roots, r, " "); for (i = 1; i <= n; i++) ok[r[i]] = 1 }
    NF { split($1, p, "."); if (p[1] in ok) print $1 }' | sort -u)
targets=("+Mathlib.Init")
for m in "${mods[@]}"; do [ "$m" = "Mathlib.Init" ] || targets+=("+$m"); done

marker="$(mktemp "$LOCK_DIR/markers/check.XXXXXX")"
touch "$marker"
sleep 1  # coarse mtimes: make sure anything written afterwards is strictly newer
log="$(mktemp "$LOCK_DIR/markers/check-log.XXXXXX")"
cd "$lean"
set +e
systemd-run --user --scope --quiet -p MemoryMax="$FILE_MEMORY_MAX" -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS="$LEAN_THREADS" lake build --no-build "${targets[@]}" >"$log" 2>&1
rc=$?
set -e
post_check "$marker"
rm -f "$marker"

if [ "$rc" -ne 0 ] || ! grep -q "All targets up-to-date" "$log" \
   || grep -qiE "manifest out of date|cloning|URL has changed|checking out|updating" "$log"; then
  echo "check_frozen: NOT up-to-date (rc=$rc) for ${#targets[@]} module targets. Lake said:" >&2
  tail -n 40 "$log" >&2
  echo "check_frozen: ABORT (log: $log). Do NOT build: something would be rebuilt inside the frozen tree." >&2
  exit 1
fi
echo "check_frozen: $(grep -m1 "All targets up-to-date" "$log") over ${#targets[@]} dependency modules"
rm -f "$log"
