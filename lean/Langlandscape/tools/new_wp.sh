#!/usr/bin/env bash
# tools/new_wp.sh <wp> [--base <rev>] [--from <worktree>]
# tools/new_wp.sh --exp <wp>-<model> [--base <rev>] [--from <worktree>]
#
# S01-X2. Creates a WP worktree + branch, links the frozen dependencies and seeds .lake/build.
#   <wp>            -> worktree $WT_ROOT/s01-<wp>,      branch impl/s01-<wp>
#   --exp <wp>-<m>  -> worktree $WT_ROOT/exp-s01-<wp>-<m>, branch exp/s01-<wp>-<m>
#   --base <rev>    start point (default: wip-implementation)
#   --from <wt>     seed .lake/build from this worktree (an upstream WP) instead of $WT_ROOT/impl
# Works from any checkout (git is run with -C on the impl worktree). Seeding: cp -a --reflink=auto while holding the
# node-wide lean.lock SHARED (DECISION-PV.md regime (a); agents/rules/lean.md). NEVER hard links. Never calls lake.
# Until S01-X1b the per-checkout lock does not exist; then only lean.lock (shared) is taken.
# Exit 0 ok; 1 usage/error; 99 propagated from link_deps.sh.
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0

WT_ROOT=/home/janosch/dev/Langlandscape-wt
IMPL="$WT_ROOT/impl"
die() { echo "new_wp: ABORT: $*" >&2; exit 1; }
usage() { echo "usage: new_wp.sh <wp> [--base <rev>] [--from <worktree>] | --exp <wp>-<model> [--base <rev>] [--from <worktree>]" >&2; exit 1; }

here="$(cd "$(dirname "$0")" && pwd)"
base=wip-implementation; from="$IMPL"; kind=wp; name=""
while [ $# -gt 0 ]; do
  case "$1" in
    --base) [ $# -ge 2 ] || usage; base="$2"; shift 2 ;;
    --from) [ $# -ge 2 ] || usage; from="$2"; shift 2 ;;
    --exp)  [ $# -ge 2 ] || usage; kind=exp; name="$2"; shift 2 ;;
    -h|--help) usage ;;
    -*) usage ;;
    *) [ -z "$name" ] || usage; name="$1"; shift ;;
  esac
done
[ -n "$name" ] || usage
[[ "$name" =~ ^[a-z0-9][a-z0-9._-]*$ ]] || die "bad name '$name' (lowercase letters, digits, . _ -)"
if [ "$kind" = exp ]; then
  [[ "$name" == *-* ]] || die "--exp needs <wp>-<model>"
  wt="$WT_ROOT/exp-s01-$name"; branch="exp/s01-$name"
else
  wt="$WT_ROOT/s01-$name"; branch="impl/s01-$name"
fi

from="$(cd "$from" 2>/dev/null && pwd -P)" || die "--from worktree does not exist"
src="$from/lean/Langlandscape/.lake/build"
[ -d "$src" ] || die "no build to seed from: $src"
[ ! -e "$wt" ] || die "worktree path exists: $wt"
git -C "$IMPL" rev-parse --verify --quiet "$base^{commit}" >/dev/null || die "unknown base revision '$base'"
if git -C "$IMPL" rev-parse --verify --quiet "refs/heads/$branch" >/dev/null; then die "branch exists: $branch"; fi

# shellcheck source=deps_load.sh
repo="$(cd "$here/.." && pwd)"
source "$here/deps_load.sh"
lock="$LOCK_DIR/lean.lock"
mkdir -p "$LOCK_DIR"

echo "new_wp: git worktree add $wt -b $branch $base"
git -C "$IMPL" worktree add "$wt" -b "$branch" "$base"

proj="$wt/lean/Langlandscape"
[ -d "$proj" ] || die "no lean/Langlandscape in $wt (base '$base')"
cd "$proj"
rc=0; tools/link_deps.sh || rc=$?
[ "$rc" -eq 0 ] || { echo "new_wp: link_deps.sh failed (rc $rc)" >&2; exit "$rc"; }
rc=0; tools/link_deps.sh --verify || rc=$?
[ "$rc" -eq 0 ] || { echo "new_wp: link_deps.sh --verify failed (rc $rc)" >&2; exit "$rc"; }

[ ! -e .lake/build ] || die ".lake/build already exists in $proj"
echo "new_wp: seeding .lake/build from $src (lean.lock shared)"
# after S01-X1b: hold lean.lock shared AND the source checkout's per-checkout lock shared (gate lbuilds hold it exclusive)
srcproj="$(realpath "$src/../..")"
cklock="$(dirname "$lock")/ll-$(printf '%s' "$srcproj" | sha1sum | cut -d' ' -f1).lock"
flock -s -w 600 "$lock" flock -s -w 600 "$cklock" cp -a --reflink=auto "$src" .lake/build || die "seeding failed"
echo "new_wp: OK $wt (branch $branch, base $base, seeded from $from)"
echo "new_wp: next: cd $proj && tools/check_frozen.sh"
