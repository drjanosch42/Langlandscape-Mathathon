# COPY of lean/trace-formula-project-import/tools/deps_load.sh @a4efa59 (S01-X1a, 2026-11-14), changed: S01-X1b local-conf allowlist += SLOTS (1..3); pin guard (tools/pins.sha256, no .lake/package-overrides.json; exit 99), local-conf allowlist += GL2TF_IMPORT, GL2TF_IMPORT default + FROZEN_TREES += $GL2TF_IMPORT.
# tools/deps_load.sh: sourced (not executed) by the tools/*.sh scripts instead of tools/deps.conf (D25, T-D25, T-D25c).
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/deps_load.sh @84818d0, unchanged except this line: repo resolves to algebraic_jl/, lean dir = algebraic_jl/lean.
# Needs $repo. Sources tools/deps.conf (the single D1 switch), then the optional, gitignored tools/deps.local.conf of the
# machine. The local file may set ONLY: DEPS_TREE FROZEN_TREES SWEEP_EXTRA_TREES LOCK_DIR LC_CPUS MACHINE_ID
# GL2TF_DATA LOAD_PROFILE. Anything else (a limit, MATHLIB_REV, LEAN_TOOLCHAIN, code) is refused with exit 1; a local file
# is not a D1 change. DEPS_LOCAL_CONF=<file> overrides the location (tests only).
#
# T-D25c (relative setup, docs/sync/main/T-D25c-relative-setup.md):
# - Paths in the local file may be RELATIVE; they resolve against the repo root ($repo), e.g. GL2TF_DATA=../gl2tf-data.
# - GL2TF_DATA = the ONE machine-local data base. When set, every tree path the local file does not set itself is derived
#   from it with the basenames of deps.conf: DEPS_TREE=$GL2TF_DATA/<basename of deps.conf DEPS_TREE>, MATHLIB_TREE=
#   $GL2TF_DATA/<basename of the FIRST word of deps.conf FROZEN_TREES>, FROZEN_TREES=SWEEP_EXTRA_TREES="$MATHLIB_TREE
#   $DEPS_TREE", LOCK_DIR=$GL2TF_DATA/gl2tf-cache. Without a local file every variable is exactly that of deps.conf (MAIN).
# - MATHLIB_TREE (exported, derived, never set by hand) = the real Mathlib checkout the farm DEPS_TREE points into
#   (convention: the first word of deps.conf FROZEN_TREES).
# - LOAD_PROFILE=<name> selects a COMMITTED machine load profile of tools/load_profiles.conf (pre-flight thresholds and
#   the heavy-job switch; never a cap, a thread count or the pin). A profile is refused unless its APPROVED line is 1
#   (set by the lead after the user's approval). Without a profile: FILE_MEM_MIN_KB = BUILD_MEM_MIN_KB = MEM_MIN_KB and
#   HEAVY_LEAN=1, i.e. today's D8 behaviour.
# S01-X1a pin guard (fail closed, OVERVIEW §3.4, Fable C1): BEFORE anything else, and so before any `lake` call of any
# wrapper. A missing/changed lake-manifest.json (or lakefile.toml, lean-toolchain) would make Lake run a full update
# through the frozen farm symlinks; a package-overrides.json would bypass the manifest. Exit 99 without calling Lake.
if ! ( cd "$repo" && sha256sum -c --quiet --strict tools/pins.sha256 ) >&2; then
  echo "deps_load: !!!!! PIN GUARD: lakefile.toml / lake-manifest.json / lean-toolchain differ from tools/pins.sha256 (or are missing)." >&2
  echo "deps_load: !!!!! No lake call was made. Never hand-edit or delete lake-manifest.json. STOP AND ALERT THE GLOBAL MASTER." >&2
  exit 99
fi
if [ -e "$repo/.lake/package-overrides.json" ] || [ -L "$repo/.lake/package-overrides.json" ]; then
  echo "deps_load: !!!!! PIN GUARD: $repo/.lake/package-overrides.json exists (would bypass the manifest). No lake call was made. STOP AND ALERT THE GLOBAL MASTER." >&2
  exit 99
fi
source "$repo/tools/deps.conf"
_dl_conf_deps="${DEPS_TREE:-}"
_dl_conf_frozen="${FROZEN_TREES:-}"
GL2TF_DATA=""
LOAD_PROFILE=""
_dl_set=" "
_dl_local="${DEPS_LOCAL_CONF:-$repo/tools/deps.local.conf}"
if [ -f "$_dl_local" ]; then
  _dl_allowed=" DEPS_TREE FROZEN_TREES SWEEP_EXTRA_TREES LOCK_DIR LC_CPUS MACHINE_ID GL2TF_DATA LOAD_PROFILE GL2TF_IMPORT SLOTS "
  while IFS= read -r _dl_line || [ -n "$_dl_line" ]; do
    case "$_dl_line" in ''|'#'*|[[:space:]]*'#'*) continue ;; esac
    if ! [[ "$_dl_line" =~ ^([A-Z_][A-Z0-9_]*)=(\"[^\"\$\`\\]*\"|[^[:space:]\"\'\$\`\\;\&\|\<\>\(\)]*)([[:space:]]+#.*)?$ ]]; then
      echo "deps_load: ABORT: $_dl_local: line not of the form KEY=value (no code allowed): $_dl_line" >&2; exit 1
    fi
    case "$_dl_allowed" in
      *" ${BASH_REMATCH[1]} "*) _dl_set="$_dl_set${BASH_REMATCH[1]} " ;;
      *) echo "deps_load: ABORT: $_dl_local may not set ${BASH_REMATCH[1]} (allowed:$_dl_allowed)" >&2; exit 1 ;;
    esac
  done <"$_dl_local"
  # shellcheck disable=SC1090
  source "$_dl_local"
  # S01-X1b: SLOTS (node-wide Lean jobs) may be set locally, 1..3 only (never raised beyond 3).
  [[ "$SLOTS" =~ ^[1-3]$ ]] || { echo "deps_load: ABORT: $_dl_local: SLOTS='$SLOTS' must be 1, 2 or 3" >&2; exit 1; }
  echo "deps_load: using local override $_dl_local (MACHINE_ID=${MACHINE_ID:-unset})" >&2

  _dl_abs() {  # a path of the local file: absolute as given, relative = against the repo root (lexically normalized)
    case "$1" in /*) printf '%s' "$1" ;; '') ;; *) realpath -ms "$repo/$1" ;; esac
  }
  _dl_abs_list() { local w out=""; for w in $1; do out="${out:+$out }$(_dl_abs "$w")"; done; printf '%s' "$out"; }
  _dl_isset() { case "$_dl_set" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }

  if [ -n "$GL2TF_DATA" ]; then
    GL2TF_DATA="$(_dl_abs "$GL2TF_DATA")"
    _dl_isset DEPS_TREE || DEPS_TREE="$GL2TF_DATA/$(basename "$_dl_conf_deps")"
    MATHLIB_TREE="$GL2TF_DATA/$(basename "${_dl_conf_frozen%% *}")"
    _dl_isset FROZEN_TREES || FROZEN_TREES="$MATHLIB_TREE $DEPS_TREE"
    _dl_isset SWEEP_EXTRA_TREES || SWEEP_EXTRA_TREES="$MATHLIB_TREE $DEPS_TREE"
    _dl_isset LOCK_DIR || LOCK_DIR="$GL2TF_DATA/gl2tf-cache"
  fi
  _dl_isset DEPS_TREE && DEPS_TREE="$(_dl_abs "$DEPS_TREE")"
  _dl_isset FROZEN_TREES && FROZEN_TREES="$(_dl_abs_list "$FROZEN_TREES")"
  _dl_isset SWEEP_EXTRA_TREES && SWEEP_EXTRA_TREES="$(_dl_abs_list "$SWEEP_EXTRA_TREES")"
  _dl_isset LOCK_DIR && LOCK_DIR="$(_dl_abs "$LOCK_DIR")"
  # tree paths must be shell-safe: whitespace or glob characters would be word-split/expanded by the scripts
  for _dl_v in GL2TF_DATA DEPS_TREE MATHLIB_TREE LOCK_DIR; do
    case "${!_dl_v:-}" in *[[:space:]\*\?\[\]]*) echo "deps_load: ABORT: $_dl_v='${!_dl_v}' contains whitespace or glob characters (*?[]); use a plain path" >&2; exit 1 ;; esac
  done
  unset -f _dl_abs _dl_abs_list _dl_isset
fi
# the real Mathlib checkout behind the farm (first FROZEN_TREES word of deps.conf, or derived from GL2TF_DATA above)
MATHLIB_TREE="${MATHLIB_TREE:-${_dl_conf_frozen%% *}}"
export MATHLIB_TREE GL2TF_DATA
export MACHINE_ID="${MACHINE_ID:-}"

# Machine load profile (T-D25c). Defaults = D8 as in deps.conf.
FILE_MEM_MIN_KB="${MEM_MIN_KB:-}"
BUILD_MEM_MIN_KB="${MEM_MIN_KB:-}"
HEAVY_LEAN=1
if [ -n "$LOAD_PROFILE" ]; then
  _dl_pf="$repo/tools/load_profiles.conf"
  [ "${GL2TF_TESTING:-0}" = 1 ] && _dl_pf="${LOAD_PROFILES_CONF:-$_dl_pf}"   # test-only override
  [[ "$LOAD_PROFILE" =~ ^[a-z0-9][a-z0-9-]*$ ]] || { echo "deps_load: ABORT: bad LOAD_PROFILE name '$LOAD_PROFILE'" >&2; exit 1; }
  [ -f "$_dl_pf" ] || { echo "deps_load: ABORT: LOAD_PROFILE=$LOAD_PROFILE but $_dl_pf is missing" >&2; exit 1; }
  _dl_approved=""; _dl_seen=0
  while IFS= read -r _dl_line || [ -n "$_dl_line" ]; do
    case "$_dl_line" in ''|'#'*) continue ;; esac
    [[ "$_dl_line" =~ ^([a-z0-9][a-z0-9-]*)\.([A-Z_]+)=([0-9]+)([[:space:]]+#.*)?$ ]] \
      || { echo "deps_load: ABORT: $_dl_pf: bad line: $_dl_line" >&2; exit 1; }
    [ "${BASH_REMATCH[1]}" = "$LOAD_PROFILE" ] || continue
    _dl_seen=1
    case "${BASH_REMATCH[2]}" in
      APPROVED) _dl_approved="${BASH_REMATCH[3]}" ;;
      FILE_MEM_MIN_KB) FILE_MEM_MIN_KB="${BASH_REMATCH[3]}" ;;
      BUILD_MEM_MIN_KB) BUILD_MEM_MIN_KB="${BASH_REMATCH[3]}" ;;
      HEAVY_LEAN) HEAVY_LEAN="${BASH_REMATCH[3]}" ;;
      *) echo "deps_load: ABORT: $_dl_pf: key ${BASH_REMATCH[2]} is not a profile key (APPROVED FILE_MEM_MIN_KB BUILD_MEM_MIN_KB HEAVY_LEAN)" >&2; exit 1 ;;
    esac
  done <"$_dl_pf"
  [ "$_dl_seen" = 1 ] || { echo "deps_load: ABORT: no profile '$LOAD_PROFILE' in $_dl_pf" >&2; exit 1; }
  [ "$_dl_approved" = 1 ] || { echo "deps_load: ABORT: load profile '$LOAD_PROFILE' is not approved (APPROVED=1 in $_dl_pf, set by the lead after the user's decision)" >&2; exit 1; }
  [ "$HEAVY_LEAN" = 0 ] || [ "$HEAVY_LEAN" = 1 ] || { echo "deps_load: ABORT: HEAVY_LEAN must be 0 or 1" >&2; exit 1; }
  # a pre-flight threshold may never fall below its cap + 1 GiB (the cap itself stays the deps.conf value)
  _dl_kb() { case "$1" in *G) echo $(( ${1%G} * 1048576 )) ;; *M) echo $(( ${1%M} * 1024 )) ;; *) echo "$1" ;; esac; }
  if [ -n "${FILE_MEMORY_MAX:-}" ] && [ "$FILE_MEM_MIN_KB" -lt $(( $(_dl_kb "$FILE_MEMORY_MAX") + 1048576 )) ]; then
    echo "deps_load: ABORT: profile $LOAD_PROFILE: FILE_MEM_MIN_KB $FILE_MEM_MIN_KB < FILE_MEMORY_MAX $FILE_MEMORY_MAX + 1 GiB" >&2; exit 1
  fi
  if [ -n "${BUILD_MEMORY_MAX:-}" ] && [ "$BUILD_MEM_MIN_KB" -lt $(( $(_dl_kb "$BUILD_MEMORY_MAX") + 1048576 )) ]; then
    echo "deps_load: ABORT: profile $LOAD_PROFILE: BUILD_MEM_MIN_KB $BUILD_MEM_MIN_KB < BUILD_MEMORY_MAX $BUILD_MEMORY_MAX + 1 GiB" >&2; exit 1
  fi
  unset -f _dl_kb
  echo "deps_load: load profile $LOAD_PROFILE (file pre-flight ${FILE_MEM_MIN_KB} kB, build pre-flight ${BUILD_MEM_MIN_KB} kB, HEAVY_LEAN=$HEAVY_LEAN)" >&2
  unset _dl_pf _dl_approved _dl_seen
fi
unset _dl_local _dl_allowed _dl_line _dl_set _dl_conf_deps _dl_conf_frozen
# S01-X1a: GL2TF_IMPORT = the main checkout's built import unless deps.conf / the local file set it; it is a frozen tree.
if [ -z "${GL2TF_IMPORT:-}" ]; then
  _dl_common="$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" \
    || { echo "deps_load: ABORT: cannot derive GL2TF_IMPORT ($repo is not in a git checkout); set it in tools/deps.local.conf" >&2; exit 1; }
  GL2TF_IMPORT="$_dl_common/../lean/trace-formula-project-import/lean"
  unset _dl_common
fi
case "$GL2TF_IMPORT" in /*) ;; *) GL2TF_IMPORT="$repo/$GL2TF_IMPORT" ;; esac
GL2TF_IMPORT="$(realpath -m "$GL2TF_IMPORT")"
case "$GL2TF_IMPORT" in *[[:space:]\*\?\[\]]*) echo "deps_load: ABORT: GL2TF_IMPORT='$GL2TF_IMPORT' contains whitespace or glob characters" >&2; exit 1 ;; esac
case " $FROZEN_TREES " in *" $GL2TF_IMPORT "*) ;; *) FROZEN_TREES="$FROZEN_TREES $GL2TF_IMPORT" ;; esac
export GL2TF_IMPORT
