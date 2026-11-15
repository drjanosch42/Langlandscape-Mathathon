#!/usr/bin/env bash
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/link_deps.sh @84818d0, unchanged except this line: repo resolves to algebraic_jl/, lean dir = algebraic_jl/lean.
# tools/link_deps.sh [--verify | --make-farm [--dry-run]]
#
# Creates lean/.lake/packages/<name> -> $DEPS_TREE/<name> for every package of lean/lake-manifest.json.
# Before touching anything it verifies, read-only, that each frozen checkout is at exactly the manifest's rev
# and that its git origin URL is byte-identical to the manifest's url. Otherwise Lake would "update" the
# checkout on the next load, and on a URL mismatch it deletes it (through the symlink: the SHARED tree).
#
# --verify   only check (manifest vs. tree, toolchains, existing links); create nothing. Exit 0 iff all is well.
#
# --make-farm   MIG w4 (user decision MIG-L0 Q3): create the symlink farm FARM_DIR (default DEPS_TREE of deps_load.sh, on
#   MAIN /home/janosch/data/gl2tf-deps-v4350) = `mathlib -> $FARM_MATHLIB` and `<pkg> -> $FARM_MATHLIB/.lake/packages/<pkg>`
#   (FARM_MATHLIB default MATHLIB_TREE of deps_load.sh, on MAIN /home/janosch/data/mathlib4_v4350)
#   for every package there, so that DEPS_TREE=<farm> keeps the one-checkout-per-package layout. Symlinks only; nothing is
#   created inside any frozen tree (refuses a FARM_DIR under FROZEN_TREES/FARM_MATHLIB, other than the farm itself); an
#   existing farm is verified (by target, absolute or relative links alike), never changed. The farm is frozen after
#   creation. Created in W1 on the lead's go; --dry-run prints the plan only.
#   T-D25c: NEW farm links are RELATIVE (e.g. `mathlib -> ../mathlib4_v4350`), so farm + Mathlib tree move together; this
#   is how R2 rebuilds the farm locally from the unpacked tarball tree (no download). MAIN's existing absolute farm stays.
#
# .lake/packages is a real directory of per-package symlinks (not one symlink to the tree), so that anything
# Lake might ever clone lands in our own .lake, never in the shared tree. T-D25c: links are written RELATIVE
# (lean/.lake/packages/<pkg> -> ../../../<...>/<farm>/<pkg>, computed on physical paths); --verify accepts an existing
# absolute or relative link iff it resolves (farm entry itself not followed) to $DEPS_TREE/<pkg>. LINK_ABSOLUTE=1 writes
# the old absolute form.
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
unset LAKE_PKG_URL_MAP || true

repo="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=deps.conf
source "$repo/tools/deps_load.sh"
lean="$repo/lean"
die() { echo "link_deps: ABORT: $*" >&2; exit 1; }

# T-D25c helpers. phys_noleaf P: P with its parent directory resolved physically, the last component NOT followed.
phys_noleaf() { printf '%s/%s' "$(realpath -m "$(dirname "$1")")" "$(basename "$1")"; }
# link_dest L: where the symlink L points, as phys_noleaf (a relative link is taken relative to L's directory).
link_dest() {
  local t; t="$(readlink "$1")" || return 1
  case "$t" in /*) ;; *) t="$(dirname "$1")/$t" ;; esac
  phys_noleaf "$t"
}
# rel_link TARGET LINKDIR: the relative link text from LINKDIR to TARGET (TARGET's last component not followed).
rel_link() { realpath -ms --relative-to="$(realpath -m "$2")" "$(phys_noleaf "$1")"; }   # both sides already physical: -s

if [ "${1:-}" = "--make-farm" ]; then
  farm="${FARM_DIR:-$DEPS_TREE}"
  src="${FARM_MATHLIB:-$MATHLIB_TREE}"
  [ -n "$farm" ] && [ -n "$src" ] || die "no farm/Mathlib path (DEPS_TREE/MATHLIB_TREE empty)"
  dry=0; [ "${2:-}" = "--dry-run" ] && dry=1
  [ -d "$src/.lake/packages" ] || die "no package directory $src/.lake/packages"
  for t in $FROZEN_TREES "$src"; do
    [ "$(realpath -m "$t")" = "$(realpath -m "$farm")" ] && continue   # the farm itself is a frozen tree (R2's FROZEN_TREES)
    case "$(realpath -m "$farm")/" in "$(realpath -m "$t")"/*) die "farm $farm lies inside the frozen tree $t" ;; esac
  done
  pairs=("mathlib:$src")
  for e in "$src/.lake/packages"/*; do [ -d "$e" ] && pairs+=("$(basename "$e"):$e"); done
  if [ -e "$farm" ] || [ -L "$farm" ]; then
    [ -d "$farm" ] && [ ! -L "$farm" ] || die "$farm exists and is not a real directory"
    for pr in "${pairs[@]}"; do
      [ -L "$farm/${pr%%:*}" ] && [ "$(link_dest "$farm/${pr%%:*}")" = "$(phys_noleaf "${pr#*:}")" ] \
        || die "existing farm $farm differs at ${pr%%:*}; it is frozen, not repaired"
    done
    echo "link_deps: farm $farm already exists and is correct (${#pairs[@]} links)"; exit 0
  fi
  for pr in "${pairs[@]}"; do echo "link_deps: farm: $farm/${pr%%:*} -> $(rel_link "${pr#*:}" "$farm") (= ${pr#*:})"; done
  [ "$dry" = 1 ] && { echo "link_deps: --dry-run: nothing created"; exit 0; }
  mkdir -p "$farm"
  for pr in "${pairs[@]}"; do ln -s "$(rel_link "${pr#*:}" "$farm")" "$farm/${pr%%:*}"; done
  for pr in "${pairs[@]}"; do
    [ "$(realpath "$farm/${pr%%:*}")" = "$(realpath "${pr#*:}")" ] || die "farm link ${pr%%:*} does not resolve to ${pr#*:}"
  done
  echo "link_deps: farm created (${#pairs[@]} symlinks, frozen from now on)"; exit 0
fi

manifest="$lean/lake-manifest.json"
pkgs="$lean/.lake/packages"
verify_only=0
[ "${1:-}" = "--verify" ] && verify_only=1

[ -f "$manifest" ] || die "missing $manifest"
[ -d "$DEPS_TREE" ] || die "missing frozen tree $DEPS_TREE"

# Toolchains: ours = deps.conf = the frozen mathlib's.
[ "$(tr -d '[:space:]' < "$lean/lean-toolchain")" = "$LEAN_TOOLCHAIN" ] \
  || die "lean/lean-toolchain differs from deps.conf LEAN_TOOLCHAIN=$LEAN_TOOLCHAIN"
[ "$(tr -d '[:space:]' < "$DEPS_TREE/mathlib/lean-toolchain")" = "$LEAN_TOOLCHAIN" ] \
  || die "$DEPS_TREE/mathlib/lean-toolchain differs from $LEAN_TOOLCHAIN"

# No package overrides (they would bypass the manifest).
[ ! -e "$lean/.lake/package-overrides.json" ] || die "lean/.lake/package-overrides.json exists; remove it"

# lakefile.toml (M0-G3 MINOR-5): Lean options only from the allowlist below (every one is an existing, agreed
# setting); no extra Lean/server/linker arguments, no `path` dependency. Anything else (e.g. debug.skipKernelTC,
# maxRecDepth) aborts every Lean process before it starts. Extending the list is a lead/D1 decision.
python3 -I - "$lean/lakefile.toml" <<'PY' || die "lean/lakefile.toml has forbidden settings (see above)"
import re, sys
ALLOWED = {"autoImplicit", "relaxedAutoImplicit", "maxHeartbeats", "synthInstance.maxHeartbeats",
           "backward.isDefEq.respectTransparency.types", "maxSynthPendingDepth"}
# NEW-3: keys may be quoted ("moreLeanArgs" = ...) or appear inside inline tables; leanOptions may be set by dotted keys.
FORBIDDEN_KEYS = re.compile(r"(?:^|[{,])\s*\"?(moreLeanArgs|weakLeanArgs|moreServerArgs|moreServerOptions|moreGlobalServerArgs|"
                            r"moreLeancArgs|weakLeancArgs|moreLinkArgs|weakLinkArgs|path|extraDepTargets|precompileModules)\"?\s*=")
DOTTED_OPT = re.compile(r'^\s*"?leanOptions"?\s*\.\s*(.+?)\s*=')
bad, section = [], ""
for no, raw in enumerate(open(sys.argv[1], encoding="utf-8"), 1):
    line = raw.split("#", 1)[0].rstrip()
    if not line.strip():
        continue
    m = re.match(r"^\s*\[\[?\s*([\"A-Za-z0-9_.]+)\s*\]\]?\s*$", line)
    if m:
        section = m.group(1).replace('"', "")
        if section == "leanOptions" and raw.lstrip().startswith("[["):
            bad.append(f"{no}: unexpected [[leanOptions]]")
        continue
    if FORBIDDEN_KEYS.search(line):
        bad.append(f"{no}: forbidden key: {line.strip()}")
    keys = []
    m = DOTTED_OPT.match(line)
    if m:  # leanOptions.maxRecDepth = 9999, leanOptions."debug.skipKernelTC" = true
        keys.append(m.group(1).replace('"', "").replace(" ", ""))
    if section.endswith("leanOptions"):
        m = re.match(r'^\s*"?([A-Za-z0-9_.]+)"?\s*=', line)
        keys.append(m.group(1) if m else "<unparsed>")
    m = re.match(r"^\s*leanOptions\s*=\s*\{(.*)\}\s*$", line)
    if m:
        keys += [k.strip().strip('"') for k in re.findall(r'(?:^|,)\s*("?[A-Za-z0-9_.]+"?)\s*=', m.group(1))]
    elif re.match(r"^\s*leanOptions\s*=", line):
        bad.append(f"{no}: leanOptions must be a one-line inline table: {line.strip()}")
    for k in keys:
        if k not in ALLOWED:
            bad.append(f"{no}: Lean option '{k}' is not allowlisted")
for b in bad:
    print(f"link_deps: lakefile.toml:{b}", file=sys.stderr)
sys.exit(1 if bad else 0)
PY

# name<TAB>url<TAB>rev<TAB>type for every manifest package; also the packagesDir.
entries="$(python3 -I - "$manifest" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
if m.get("packagesDir") != ".lake/packages":
    sys.exit("packagesDir must be .lake/packages")
for p in m["packages"]:
    print("\t".join([p["name"], p.get("url", ""), p.get("rev", ""), p.get("type", "")]))
PY
)" || die "cannot parse $manifest"

# The frozen mathlib's own manifest must pin the same revisions for its dependencies.
inner="$(python3 -I - "$DEPS_TREE/mathlib/lake-manifest.json" <<'PY'
import json, sys
for p in json.load(open(sys.argv[1]))["packages"]:
    print("\t".join([p["name"], p.get("url", ""), p.get("rev", "")]))
PY
)" || die "cannot parse frozen mathlib manifest"

errs=0
names=()
while IFS=$'\t' read -r name url rev type; do
  names+=("$name")
  dir="$DEPS_TREE/$name"
  [ "$type" = "git" ] || { echo "link_deps: $name: type '$type' is not git" >&2; errs=1; continue; }
  [ -d "$dir/.git" ] || [ -f "$dir/.git" ] || { echo "link_deps: $name: $dir is not a git checkout" >&2; errs=1; continue; }
  head="$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)"
  origin="$(git -C "$dir" remote get-url origin 2>/dev/null || true)"
  [ "$head" = "$rev" ] || { echo "link_deps: $name: HEAD $head != manifest rev $rev" >&2; errs=1; }
  [ "$origin" = "$url" ] || { echo "link_deps: $name: origin '$origin' != manifest url '$url'" >&2; errs=1; }
  if [ "$name" = "mathlib" ] && [ "$rev" != "$MATHLIB_REV" ]; then
    echo "link_deps: mathlib: manifest rev $rev != deps.conf MATHLIB_REV $MATHLIB_REV" >&2; errs=1
  fi
done <<< "$entries"

while IFS=$'\t' read -r name url rev; do
  [ -n "$name" ] || continue
  ours="$(awk -F'\t' -v n="$name" '$1==n {print $2"\t"$3}' <<< "$entries")"
  [ "$ours" = "$url"$'\t'"$rev" ] || { echo "link_deps: $name: frozen mathlib manifest pins '$url $rev', ours '$ours'" >&2; errs=1; }
done <<< "$inner"

[ "$errs" = 0 ] || die "manifest and frozen tree disagree (see above); nothing was linked"

# Existing links: .lake/packages must be a real directory whose entries are symlinks into DEPS_TREE.
check_links() {
  local bad=0
  [ -d "$pkgs" ] && [ ! -L "$pkgs" ] || { echo "link_deps: $pkgs is missing or is a symlink" >&2; return 1; }
  for name in "${names[@]}"; do
    local l="$pkgs/$name"
    if [ ! -L "$l" ] || [ "$(link_dest "$l")" != "$(phys_noleaf "$DEPS_TREE/$name")" ]; then
      echo "link_deps: $l does not point to $DEPS_TREE/$name" >&2; bad=1
    fi
  done
  for e in "$pkgs"/* "$pkgs"/.[!.]*; do
    [ -e "$e" ] || [ -L "$e" ] || continue
    [ -L "$e" ] || { echo "link_deps: $e is a real file/directory (did Lake clone something?)" >&2; bad=1; }
  done
  return $bad
}

if [ "$verify_only" = 1 ]; then
  check_links || die "links are not in place; run tools/link_deps.sh"
  echo "link_deps: OK (${#names[@]} packages at the manifest revs, links in place)"
  exit 0
fi

if [ -L "$pkgs" ]; then die "$pkgs is a symlink; remove it by hand (rm $pkgs, NOT rm -r) and re-run"; fi
mkdir -p "$pkgs"
for e in "$pkgs"/* "$pkgs"/.[!.]*; do
  [ -e "$e" ] || [ -L "$e" ] || continue
  [ -L "$e" ] || die "$e is a real file/directory; inspect and remove it by hand"
done
for name in "${names[@]}"; do
  # skip a link that already points (physically) at the intended target: MAIN's valid absolute links are never touched
  if [ -L "$pkgs/$name" ] && [ "$(link_dest "$pkgs/$name")" = "$(phys_noleaf "$DEPS_TREE/$name")" ]; then continue; fi
  if [ "${LINK_ABSOLUTE:-0}" = 1 ]; then want="$DEPS_TREE/$name"; else want="$(rel_link "$DEPS_TREE/$name" "$pkgs")"; fi
  ln -s "$want" "$pkgs/.$name.tmp.$$" && mv -T "$pkgs/.$name.tmp.$$" "$pkgs/$name"   # atomic replace
done
check_links || die "links not correct after linking"
echo "link_deps: linked ${#names[@]} packages: $pkgs/* -> $DEPS_TREE/*"
