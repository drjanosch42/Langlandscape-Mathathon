#!/usr/bin/env bash
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/lbuild.sh @84818d0: repo = algebraic_jl/, lean = algebraic_jl/lean;
# only the target allowlist changed (AlgJL*, no tfaudit/Audit) and audit/probe modes are refused. Same locks, caps, frozen trees.
# tools/lbuild.sh <target> [<target> ...] | --audit | --audit-incremental | --audit-file <F.lean> [--module-name M] [--out P]
#                 | --audit-norm [--out P] [--pp NAMES.txt]
#
# The ONLY way to run `lake build` (and tfaudit). PLAN.md §5.3, CLAUDE.md rules 5, 7-9:
#   - EXCLUSIVE lock  flock -x -w 7200 ~/.cache/gl2tf/lean.lock  (waits for running lfile.sh checks, blocks new ones);
#   - MemAvailable >= 16 GB (>= 24 GB for --audit/--audit-file, D21), else wait and retry every 5 min (the 16 GB of a plain
#     build is BUILD_MEM_MIN_KB: a committed load profile, tools/load_profiles.conf, may lower it; T-D25c);
#   - tools/check_frozen.sh (dry no-rebuild check of every dependency module imported in lean/);
#   - marker; systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10
#       env LEAN_NUM_THREADS=2 lake build <targets>;
#     (Lake v4.33 has no -j option; LEAN_NUM_THREADS=2 sizes the lake process's task pool, which bounds the number
#      of concurrent `lean` children to 2, and each child inherits LEAN_NUM_THREADS=2: the "-j2" of PLAN.md §5.3.)
#   - D21: the tfaudit and leanchecker steps of --audit/--audit-file run with MemoryMax=$AUDIT_MEMORY_MAX (16G);
#     the lake build and all other steps keep 8G.
#   - post-flight find-newer on the frozen trees (exit 99 = frozen tree written: stop everything, alert the lead).
#
# Targets: ALLOWLIST only (M0-G3 MAJOR-4; nothing outside the project can be built, so nothing can be built inside
# the frozen tree): the libraries/exe GL2TF, GL2TFTests, GL2TFPrintAxioms, GL2TFVendor, GL2TFVendorImperial, tfaudit,
# and module targets +M whose source is a project file: M = GL2TF[.*] | GL2TFTests[.*] | Audit.* with lean/<M>.lean,
# or a vendored module with lean/Vendor/{AnthropicFLT,ImperialFLT}/<M>.lean. Anything else (Mathlib, +Mathlib.*,
# pkg/Target, facets, lean/Fixtures/*) is refused. A bare build (no target) is refused. A full-project build needs
# the lead's approval (rule 9).
# --audit: builds GL2TF GL2TFTests GL2TFPrintAxioms tfaudit, then in the same lock session (M0-G3 MAJOR-3):
#   1. tfaudit --selftest (SHA-256 test vectors);
#   2. tfaudit --root lean/ with header lean/tex tree hashes (tools/treehash.py), d1_rev = MATHLIB_REV, UTC timestamp,
#      written to a TEMP file and validated by tools/tfaudit_schema.py;
#   3. leanchecker --verbose (lean4checker of the pinned toolchain, LEAN_TOOLCHAIN in deps.conf, by ABSOLUTE path, LEAN_SYSROOT pinned; never the
#      elan default) on the GL2TF and GL2TFTests modules; it passes iff rc 0 AND every non-exempt module was replayed (import-only roots are exempt, R25);
#   4. `lean Audit/PrintAxioms.lean` (the plain #print axioms cross-check), output in tools/state/print_axioms.json;
#   5. ONLY IF 1-4 all passed: the temp file is installed as tools/state/tfaudit.json. Then
#      tools/state/leanchecker.json is written (whenever step 3 ran): ok, rc, lean_tree_hash, modules_replayed, and
#      tfaudit_sha256 = sha256 of the tfaudit.json installed in this session ("" if none was installed), so tfcheck
#      can block unless leanchecker passed for exactly the current audit.
#   Ticket t4 (PLAN R25; docs/specs/tfaudit_output.md §9): --audit is the FULL audit. tfaudit gets per-module keys
#   (tools/audit_cache.py keys: sha256 over the .oleans of the module and of its whole project import closure, the
#   toolchain, the D1 pin, the manifest and the tool binary), recomputes every hash, VERIFIES the previous hash cache
#   against the fresh hashes (a mismatch fails the audit and deletes the cache) and writes a new one; leanchecker
#   replays every module. With tfaudit >= 4.14 the normalized-hash export (spec §11) is written in the same run and
#   installed with the audit as tools/state/norm.json (bound to it by tfaudit_sha256; MIG-L4 new pin).
# --audit-incremental: the same steps, but tfaudit reuses the cached hashes of constants whose module key is unchanged
#   (header.audit_mode = "incremental") and leanchecker replays only the modules whose key is not in
#   tools/state/leanchecker_cache.json (leanchecker.json mode = "incremental"). Everything else is recomputed.
#   tfcheck --gate refuses an incremental audit: G3 and close-outs need --audit.
# Both: audit_cache.py check-imports (the key graph contains every olean import); tools/state/audit_run.json (mode,
#   wall time and max RSS of every step, /usr/bin/time); the caches are installed only when the audit passed.
# --audit-file F: builds GL2TF GL2TFTests tfaudit, then `tfaudit --file F` (fixture mode: F is elaborated in-process,
#   in no Lake library; docs/notes/M0-tfaudit.md), default output tools/state/fixtures/<stem>.json. F's imports are
#   added to the dry no-rebuild check. No leanchecker. With tfaudit >= 4.14 also the normalized-hash export
#   (`--export-norm`, spec §11) next to the output as <stem>.norm.json; `--norm-only` writes only that export
#   (`--export-norm-only`; the smoke test of the norm step) and prints its wall time and max RSS; `--norm-pp NAMES`
#   writes only the pretty-printed listed constants (`--norm-pp`) to <stem>.norm.json instead.
# --audit-norm (MIG-L4, tfaudit >= 4.14): builds GL2TF GL2TFTests tfaudit, then ONLY `tfaudit --export-norm P
#   --export-norm-only` on GL2TF + GL2TFTests (default P = tools/state/norm.json; no main audit, no leanchecker, nothing
#   else installed), same lock, pre-flight and 16G scope as --audit; prints its wall time and max RSS. With
#   `--pp NAMES.txt` instead `tfaudit --norm-pp NAMES.txt --norm-pp-out P` (default tools/state/norm_pp.json): the
#   pretty-printed residue constants (`semhash_migrate.py --mode d1-expr --emit-pp-names`).
#   T9 (spec §11.3): `--subpp REQ.tsv` and/or `--tree NAMES.txt` instead run `tfaudit --subpp REQ --norm-tree NAMES
#   --subpp-out P` (default P = tools/state/subpp_new.jsonl; `--cap N --ctx N --threshold N --max-nodes N` pass through
#   as --subpp-cap/--subpp-ctx/--subpp-threshold/--subpp-max-nodes): node trees and subterm pp of the residue
#   (`tools/mig_expr_subpp.py`). The same two options after `--audit-file F` write <stem>.subpp.jsonl.
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
unset LAKE_PKG_URL_MAP || true

repo="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=deps.conf
source "$repo/tools/deps_load.sh"
# M9b t5 (R25, M7 lesson 1): a full --audit takes about 130 min, longer than LOCK_WAIT=7200 s of deps.conf, so a build queued
# behind it timed out. lbuild.sh therefore waits at least 4 h for the exclusive lock (deps.conf stays the single switch for lfile.sh).
LOCK_WAIT=$(( LOCK_WAIT > 14400 ? LOCK_WAIT : 14400 ))
lean="$repo/lean"

die() { echo "lbuild: ABORT: $*" >&2; exit 1; }

[ $# -ge 1 ] || die "usage: lbuild.sh <target> [...] | --audit   (a bare lake build is not allowed)"
audit=0
fixture=""
fixture_module=""
fixture_out=""
fixture_norm_only=0
fixture_pp=""
fixture_sub=()
sub_args=()
incremental=0
probe=""
if [ "$1" = "--lc-probe" ]; then  # T2/R25: one small leanchecker run, reports the thread count under LC_CPUS
  [ $# -eq 2 ] && [[ "$2" =~ ^GL2TF(Tests)?(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]] || die "--lc-probe needs one GL2TF[Tests][.Sub] module prefix"
  probe="$2"
  targets=()
elif [ "$1" = "--audit" ] || [ "$1" = "--audit-incremental" ]; then
  [ $# -eq 1 ] || die "$1 takes no further arguments"
  audit=1
  [ "$1" = "--audit-incremental" ] && incremental=1
  targets=(GL2TF GL2TFTests GL2TFPrintAxioms tfaudit)
elif [ "$1" = "--audit-norm" ]; then
  shift
  norm_out=""; norm_pp=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --out) [ $# -ge 2 ] || die "--out needs a value"; norm_out="$(realpath -m "$2")"; shift 2 ;;
      --pp) [ $# -ge 2 ] || die "--pp needs a file"; norm_pp="$(realpath "$2")"; [ -f "$norm_pp" ] || die "no such file: $2"; shift 2 ;;
      --subpp|--tree) [ $# -ge 2 ] && [ -f "$2" ] || die "$1 needs a file"
        if [ "$1" = --subpp ]; then sub_args+=(--subpp "$(realpath "$2")"); else sub_args+=(--norm-tree "$(realpath "$2")"); fi; shift 2 ;;
      --cap|--ctx|--threshold|--max-nodes) [ $# -ge 2 ] && [[ "$2" =~ ^[0-9]+$ ]] || die "$1 needs a number"
        sub_args+=("--subpp-${1#--}" "$2"); shift 2 ;;
      *) die "unknown --audit-norm option '$1'" ;;
    esac
  done
  grep -qF '"--export-norm-only"' "$lean/Audit/Main.lean" || die "--audit-norm needs tfaudit >= 4.14 (--export-norm)"
  if [ "${#sub_args[@]}" -gt 0 ]; then
    grep -qF '"--subpp-out"' "$lean/Audit/Main.lean" || die "--subpp/--tree need tfaudit with --subpp-out (T9)"
    [ -z "$norm_pp" ] || die "--pp and --subpp/--tree are separate runs"
    has_req=0; for a in "${sub_args[@]}"; do case "$a" in --subpp|--norm-tree) has_req=1 ;; esac; done
    [ "$has_req" = 1 ] || die "--cap/--ctx/--threshold/--max-nodes need --subpp or --tree"
    [ -n "$norm_out" ] || norm_out="$repo/tools/state/subpp_new.jsonl"
  fi
  if [ -z "$norm_out" ]; then
    if [ -n "$norm_pp" ]; then norm_out="$repo/tools/state/norm_pp.json"; else norm_out="$repo/tools/state/norm.json"; fi
  fi
  audit=3
  targets=(GL2TF GL2TFTests tfaudit)
  if [ "$norm_out" = "$repo/tools/state/norm.json" ]; then  # T19 (C9 H3)
    echo "lbuild: WARNING: --audit-norm installs tools/state/norm.json with tfaudit_sha256 null; tfcheck then refuses every D1 migration sign-off (norm.json not bound to tfaudit.json) until the next full --audit. Use --out to write elsewhere." >&2
  fi
elif [ "$1" = "--audit-file" ]; then
  [ $# -ge 2 ] || die "--audit-file needs a .lean file"
  fixture="$(realpath "$2")"
  [ -f "$fixture" ] && [[ "$fixture" == *.lean ]] || die "no such .lean file: $2"
  shift 2
  while [ $# -gt 0 ]; do
    case "$1" in
      --module-name) [ $# -ge 2 ] || die "--module-name needs a value"
        [[ "$2" =~ ^[A-Za-z_][A-Za-z0-9_.]*$ ]] || die "bad module name '$2'"; fixture_module="$2"; shift 2 ;;
      --out) [ $# -ge 2 ] || die "--out needs a value"; fixture_out="$(realpath -m "$2")"; shift 2 ;;
      --norm-only) fixture_norm_only=1; shift ;;
      --norm-pp) [ $# -ge 2 ] && [ -f "$2" ] || die "--norm-pp needs a names file"; fixture_norm_only=1; fixture_pp="$(realpath "$2")"; shift 2 ;;
      --subpp|--tree) [ $# -ge 2 ] && [ -f "$2" ] || die "$1 needs a file"; fixture_norm_only=1
        if [ "$1" = --subpp ]; then fixture_sub+=(--subpp "$(realpath "$2")"); else fixture_sub+=(--norm-tree "$(realpath "$2")"); fi; shift 2 ;;
      *) die "unknown --audit-file option '$1'" ;;
    esac
  done
  [ -n "$fixture_out" ] || fixture_out="$repo/tools/state/fixtures/$(basename "$fixture" .lean).json"
  audit=2
  targets=(GL2TF GL2TFTests tfaudit)
else
  targets=("$@")
fi
# algebraic_jl fork (L-A, 2026-11-14): the fork has no Audit/ and no tfaudit; every audit mode and the leanchecker probe are refused.
[ "$audit" = 0 ] && [ -z "$probe" ] || die "algebraic_jl fork: audit modes and --lc-probe are not available (no Audit/, no tfaudit)"
allowed_target() {  # M0-G3 MAJOR-4
  local t="$1" m rel
  case "$t" in
    AlgJL|AlgJLTests|AlgJLVendor|AlgJLVendorImperial) return 0 ;;
  esac
  [[ "$t" =~ ^\+[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]] || return 1
  m="${t#+}"; rel="${m//.//}.lean"
  case "$m" in
    AlgJL|AlgJL.*|AlgJLTests|AlgJLTests.*) [ -f "$lean/$rel" ] ;;
    *) [ -f "$lean/Vendor/AnthropicFLT/$rel" ] || [ -f "$lean/Vendor/ImperialFLT/$rel" ] ;;
  esac
}
for t in "${targets[@]}"; do
  [[ "$t" == -* ]] && die "options are not passed through ('$t')"
  allowed_target "$t" || die "target '$t' is not a project target (allowed: AlgJL AlgJLTests AlgJLVendor AlgJLVendorImperial, +<project module with a source file in algebraic_jl/lean/>)"
done

# T-D25c: a machine whose committed load profile says HEAVY_LEAN=0 (R2, D25 amendments b/c) runs light jobs only: no audit
# mode, no leanchecker probe, no tfaudit/PrintAxioms/vendored-FLT target; the umbrella targets GL2TF/GL2TFTests only with
# GL2TF_ALLOW_UMBRELLA=1 (setup base build, rebuild after merging a main tag; ask the user first).
if [ "${HEAVY_LEAN:-1}" = 0 ]; then
  [ "$audit" = 0 ] && [ -z "$probe" ] || die "heavy Lean jobs are off on this machine (load profile ${LOAD_PROFILE:-?}, HEAVY_LEAN=0): audit modes and --lc-probe run only on MAIN's box (D25 amendment b)"
  for t in "${targets[@]}"; do
    case "$t" in
      +AlgJL.*|+AlgJLTests.*) ;;
      +*) die "heavy Lean jobs are off on this machine (HEAVY_LEAN=0): module target $t is not under GL2TF.* or GL2TFTests.* (vendored FLT modules run only on MAIN's box)" ;;
      AlgJLVendor|AlgJLVendorImperial)
        die "heavy Lean jobs are off on this machine (HEAVY_LEAN=0): target $t runs only on MAIN's box" ;;
      AlgJL|AlgJLTests)
        [ "${GL2TF_ALLOW_UMBRELLA:-0}" = 1 ] || die "umbrella target $t on a HEAVY_LEAN=0 machine needs GL2TF_ALLOW_UMBRELLA=1 (setup base build or after merging a main tag, with the user's OK)" ;;
    esac
  done
fi

# T16: --audit and --audit-norm overwrite tools/state/{tfaudit,ext_nodes,norm}.json. A D1 migration is verified against
# its pinned migration audit (semhash_migrate.D1_MIGRATIONS new_ref: git blobs, sha256-pinned), so those blobs must
# resolve before the working copies are replaced; otherwise abort (fail closed, nothing run yet).
if [ "$audit" = 1 ] || [ "$audit" = 3 ]; then
  nice -n 10 python3 "$repo/tools/semhash_migrate.py" --root "$repo" --check-new-refs \
    || die "a pinned migration audit (semhash_migrate.D1_MIGRATIONS new_ref) does not resolve to its git blobs; refusing to overwrite tools/state (T16)"
fi
command -v systemd-run >/dev/null || die "systemd-run not found; refusing to build without the memory cap"
{ [ "$audit" != 1 ] && [ "$audit" != 3 ]; } || [ -x /usr/bin/time ] || die "/usr/bin/time not found (needed for the audit step peaks, R25)"
systemd-run --user --scope --quiet -p MemoryMax=64M true >/dev/null 2>&1 \
  || die "systemd-run --user --scope does not work here; refusing to build without the memory cap"

mkdir -p "$LOCK_DIR/markers"
exec 9>"$LOCK_DIR/lean.lock"
echo "lbuild: waiting for the exclusive lock $LOCK_DIR/lean.lock (max ${LOCK_WAIT}s) ..."
flock -x -w "$LOCK_WAIT" 9 || die "could not get the exclusive lock in ${LOCK_WAIT}s"
export GL2TF_LOCK_HELD=exclusive

# D21 (docs/decisions/D21-audit-memory-cap.md): ONLY the tfaudit and leanchecker steps of --audit / --audit-file get
# AUDIT_MEMORY_MAX; the lake build step and every other step stay at BUILD_MEMORY_MAX (8G). --audit/--audit-file
# therefore also need MemAvailable >= AUDIT_MEM_MIN_KB (24 GB) before starting.
AUDIT_MEMORY_MAX=16G
AUDIT_MEM_MIN_KB=25165824
need_kb="$BUILD_MEM_MIN_KB"   # = MEM_MIN_KB (16 GB) unless a committed load profile lowers it (T-D25c)
[ "$audit" != 0 ] && need_kb="$AUDIT_MEM_MIN_KB"
while :; do
  avail="$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)"
  [ "$avail" -ge "$need_kb" ] && break
  echo "lbuild: MemAvailable ${avail} kB < ${need_kb} kB; retrying in 5 min ($(date +%T))"
  sleep 300
done

"$repo/tools/check_frozen.sh" || exit $?
if [ -n "$fixture" ]; then "$repo/tools/check_frozen.sh" --file "$fixture" || exit $?; fi

# T-13: drop our own build artifacts of modules whose source is gone (never .lake/packages, never lake clean)
"$repo/tools/prune_stale_build.sh" || die "prune of stale build artifacts failed"

marker="$(mktemp "$LOCK_DIR/markers/build.XXXXXX")"
touch "$marker"
sleep 1
cd "$lean"
capped() {
  systemd-run --user --scope --quiet -p MemoryMax="$BUILD_MEMORY_MAX" -p MemorySwapMax=0 \
    nice -n 10 env LEAN_NUM_THREADS="$LEAN_THREADS" "$@"
}
capped_audit() {  # D21: tfaudit and leanchecker only
  systemd-run --user --scope --quiet -p MemoryMax="$AUDIT_MEMORY_MAX" -p MemorySwapMax=0 \
    nice -n 10 env LEAN_NUM_THREADS="$LEAN_THREADS" "$@"
}
# t4 (R25): wall time and max RSS (largest process of the step's tree, GNU time %M) of every --audit step
steps_file="$(mktemp "$LOCK_DIR/markers/steps.XXXXXX")"
timed() {  # timed <step> <capped|capped_audit> <cmd...>: runs the command, returns its exit status
  local step="$1" wrap="$2" tf trc line
  shift 2
  if [ "$audit" != 1 ]; then "$wrap" "$@"; return $?; fi
  tf="$(mktemp "$LOCK_DIR/markers/time.XXXXXX")"
  "$wrap" /usr/bin/time -o "$tf" -f "TFTIME %e %M" "$@"
  trc=$?
  line="$(grep '^TFTIME ' "$tf" | tail -n1)"
  echo "$step ${line#TFTIME } $trc" >>"$steps_file"
  rm -f "$tf"
  return "$trc"
}
mode_name=full
[ "$incremental" = 1 ] && mode_name=incremental
if [ -n "$probe" ]; then
  tc_dir="$HOME/.elan/toolchains/$(echo "$LEAN_TOOLCHAIN" | sed 's|/|--|; s|:|---|')"
  checker="$tc_dir/bin/leanchecker"
  [ -x "$checker" ] || die "leanchecker not found at $checker"
  pin=(); [ -z "${LC_CPUS:-}" ] || pin=(taskset -c "$LC_CPUS")
  echo "lbuild: lc-probe $probe (no build; LC_CPUS='${LC_CPUS:-}')"
  t0=$(date +%s)
  capped_audit "${pin[@]}" lake env env LEAN_SYSROOT="$tc_dir" "$checker" --verbose "$probe" >"$LOCK_DIR/markers/probe.log" 2>&1 &
  bg=$!
  maxthr=0; cpus=""; ncpu_seen=""; 
  while kill -0 "$bg" 2>/dev/null; do
    for pid in $(pgrep -f "$checker --verbose $probe" || true); do
      thr="$(awk '/^Threads:/ {print $2}' "/proc/$pid/status" 2>/dev/null || echo 0)"
      if [ "${thr:-0}" -gt "$maxthr" ]; then
        maxthr="$thr"; cpus="$(awk '/^Cpus_allowed_list:/ {print $2}' "/proc/$pid/status")"
      fi
      ncpu_seen="$(cat /proc/$pid/task/*/stat 2>/dev/null | awk '{print $39}' | sort -un | tr '\n' ' ')$ncpu_seen"
    done
    sleep 0.5
  done
  prc=0; wait "$bg" || prc=$?
  echo "lbuild: lc-probe rc=$prc wall=$(( $(date +%s) - t0 )) s, entries replayed=$(grep -c '^replaying ' "$LOCK_DIR/markers/probe.log"), max threads=$maxthr, Cpus_allowed_list=$cpus, last-CPUs seen: $(echo $ncpu_seen | tr ' ' '\n' | sort -un | tr '\n' ' ')"
  rm -f "$LOCK_DIR/markers/probe.log" "$steps_file"
  "$repo/tools/check_frozen.sh" --post "$marker" || exit $?
  rm -f "$marker"
  exit "$prc"
fi
echo "lbuild: lake build ${targets[*]} (MemoryMax=$BUILD_MEMORY_MAX, LEAN_NUM_THREADS=$LEAN_THREADS)"
set +e
timed build capped lake build "${targets[@]}"
rc=$?
if [ "$rc" -eq 0 ] && [ "$audit" != 0 ]; then
  mkdir -p "$repo/tools/state"
  capped lake exe tfaudit --selftest
  rc=$?
fi
if [ "$rc" -eq 0 ] && [ "$audit" = 1 ]; then
  # 1b. M0-G3 MAJOR-7 regression check: tfaudit must refuse (exit 3) a root that is not lean/, and a root that has
  #     lakefile.toml + GL2TF.lean but not the sources of the loaded GL2TF.* modules (never silently empty closures).
  badroot="$(mktemp -d "$LOCK_DIR/markers/badroot.XXXXXX")"
  for variant in empty partial; do
    [ "$variant" = partial ] && cp "$lean/lakefile.toml" "$lean/GL2TF.lean" "$lean/lean-toolchain" "$badroot/"
    capped lake exe tfaudit --root "$badroot" --d1-rev "$MATHLIB_REV" --out "$badroot/out.json" 2>"$badroot/err"
    brc=$?  # (errexit is off in this part of the script)
    if [ "$brc" -ne 3 ] || [ -e "$badroot/out.json" ]; then
      echo "lbuild: tfaudit root guard FAILED ($variant root: rc=$brc, expected 3 and no output)" >&2; cat "$badroot/err" >&2; rc=1
    else
      echo "lbuild: tfaudit root guard OK ($variant root refused: $(tail -n1 "$badroot/err"))"
    fi
  done
  rm -rf "$badroot"
fi
if [ "$rc" -eq 0 ] && [ "$audit" != 0 ]; then
  TF_LEAN_TREE_HASH="$(python3 "$repo/tools/treehash.py" lean)"
  TF_TEX_TREE_HASH="$(python3 "$repo/tools/treehash.py" tex)"
  TF_D1_REV="$MATHLIB_REV"
  TF_TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  export TF_LEAN_TREE_HASH TF_TEX_TREE_HASH TF_D1_REV TF_TIMESTAMP
  if [ "$audit" = 3 ]; then
    mkdir -p "$(dirname "$norm_out")"
    tmp="$(mktemp "$(dirname "$norm_out")/.norm.XXXXXX.json")"
    nargs=(--export-norm "$tmp" --export-norm-only)
    [ -z "$norm_pp" ] || nargs=(--norm-pp "$norm_pp" --norm-pp-out "$tmp")
    [ "${#sub_args[@]}" -eq 0 ] || nargs=("${sub_args[@]}" --subpp-out "$tmp")
    tf_time="$(mktemp "$LOCK_DIR/markers/time.XXXXXX")"
    echo "lbuild: running tfaudit ${nargs[*]} (MemoryMax=$AUDIT_MEMORY_MAX) -> $norm_out"
    capped_audit /usr/bin/time -o "$tf_time" -f "TFTIME %e %M" lake exe tfaudit --root "$lean" "${nargs[@]}"
    rc=$?
    echo "lbuild: tfaudit norm step: wall/maxRSS(kB) $(grep '^TFTIME ' "$tf_time" | tail -n1 | cut -d' ' -f2-) rc $rc"
    rm -f "$tf_time"
    if [ "$rc" -eq 0 ] && [ -s "$tmp" ]; then mv -f "$tmp" "$norm_out"; echo "lbuild: wrote $norm_out"; else rm -f "$tmp"; [ "$rc" -ne 0 ] || rc=1; fi
  elif [ "$audit" = 1 ]; then
    out="$repo/tools/state/tfaudit.json"
    tmp="$(mktemp "$repo/tools/state/.tfaudit.XXXXXX.json")"
    # t4: module keys and the hash cache (verified against the fresh hashes in full mode, reused in incremental mode)
    hcache="$repo/tools/state/tfaudit_hashcache.json"
    tf_keys="$(mktemp "$repo/tools/state/.audit_keys.XXXXXX.json")"
    hc_tmp="$(mktemp "$repo/tools/state/.tfaudit_hashcache.XXXXXX.json")"
    python3 "$repo/tools/audit_cache.py" keys --kind tfaudit --lean "$lean" --out "$tf_keys"
    rc=$?
    cargs=()
    if grep -qF '"--hash-cache-out"' "$lean/Audit/Main.lean"; then
      cargs=(--module-keys "$tf_keys" --hash-cache-out "$hc_tmp")
      if [ -f "$hcache" ]; then
        cargs+=(--hash-cache-in "$hcache")
        [ "$incremental" = 1 ] || cargs+=(--hash-cache-verify)
      fi
    else  # t4: the tfaudit hash cache is not applied yet (docs/sprints/t4/tfaudit-hashcache.patch): tfaudit runs full
      echo "lbuild: this tfaudit has no hash cache (t4 patch not applied): tfaudit runs in full mode" >&2
    fi
    ext_tmp=""
    if grep -qF '"--export-ext-nodes"' "$lean/Audit/Main.lean"; then  # MIG w2: tfaudit 4.13 exports the ext-node table
      ext_tmp="$(mktemp "$repo/tools/state/.ext_nodes.XXXXXX.json")"
      cargs+=(--export-ext-nodes "$ext_tmp")
    fi
    norm_tmp=""
    if grep -qF '"--export-norm"' "$lean/Audit/Main.lean"; then  # MIG-L4: tfaudit 4.14 normalized-hash export
      norm_tmp="$(mktemp "$repo/tools/state/.norm.XXXXXX.json")"
      cargs+=(--export-norm "$norm_tmp")
    fi
    if [ "$rc" -eq 0 ]; then
      echo "lbuild: running tfaudit ($mode_name) -> $tmp (installed as $out only after leanchecker and #print axioms pass)"
      timed tfaudit capped_audit lake exe tfaudit --root "$lean" --out "$tmp" "${cargs[@]}"
      rc=$?
      if [ "$rc" -eq 4 ]; then
        echo "lbuild: tfaudit: the hash cache DISAGREES with the fresh hashes (a cache key misses a dependency):" \
             "deleting $hcache; report this to the lead (ticket t4)" >&2
        rm -f "$hcache"
      fi
    fi
  else
    out="$fixture_out"
    mkdir -p "$(dirname "$out")"
    tmp="$(mktemp "$(dirname "$out")/.tfaudit.XXXXXX.json")"
    margs=()
    [ -n "$fixture_module" ] && margs=(--module-name "$fixture_module")
    ext_tmp=""
    if grep -qF '"--export-ext-nodes"' "$lean/Audit/Main.lean"; then
      ext_tmp="$(mktemp "$(dirname "$out")/.ext_nodes.XXXXXX.json")"
      margs+=(--export-ext-nodes "$ext_tmp")
    fi
    norm_tmp=""
    if grep -qF '"--export-norm"' "$lean/Audit/Main.lean"; then  # MIG-L4: tfaudit 4.14 normalized-hash export
      norm_tmp="$(mktemp "$(dirname "$out")/.norm.XXXXXX.json")"
      margs+=(--export-norm "$norm_tmp")
    fi
    if [ "$fixture_norm_only" = 1 ]; then
      [ -n "$norm_tmp" ] || die "--norm-only needs tfaudit >= 4.14"
      margs=(--export-norm "$norm_tmp" --export-norm-only)
      [ -z "$fixture_pp" ] || margs=(--norm-pp "$fixture_pp" --norm-pp-out "$norm_tmp")
      fx_dest="${out%.json}.norm.json"
      if [ "${#fixture_sub[@]}" -gt 0 ]; then  # T9: node trees / subterm pp of the fixture
        [ -z "$fixture_pp" ] || die "--norm-pp and --subpp/--tree are separate runs"
        grep -qF '"--subpp-out"' "$lean/Audit/Main.lean" || die "--subpp/--tree need tfaudit with --subpp-out (T9)"
        margs=("${fixture_sub[@]}" --subpp-out "$norm_tmp"); fx_dest="${out%.json}.subpp.jsonl"
      fi
      [ -n "$fixture_module" ] && margs+=(--module-name "$fixture_module")
      tf_time="$(mktemp "$LOCK_DIR/markers/time.XXXXXX")"
      echo "lbuild: running tfaudit --file $fixture ${margs[*]} -> $fx_dest"
      capped_audit /usr/bin/time -o "$tf_time" -f "TFTIME %e %M" lake exe tfaudit --root "$lean" --file "$fixture" "${margs[@]}"
      rc=$?
      echo "lbuild: tfaudit norm step: wall/maxRSS(kB) $(grep '^TFTIME ' "$tf_time" | tail -n1 | cut -d' ' -f2-) rc $rc"
      rm -f "$tf_time" "$tmp"
      [ "$rc" -eq 0 ] && [ -s "$norm_tmp" ] && mv -f "$norm_tmp" "$fx_dest"
      [ -z "$ext_tmp" ] || rm -f "$ext_tmp"
      rm -f "$norm_tmp"
      audit=4  # nothing else to validate or install
    else
    echo "lbuild: running tfaudit --file $fixture -> $out"
    capped_audit lake exe tfaudit --root "$lean" --file "$fixture" "${margs[@]}" --out "$tmp"
    rc=$?
    fi
  fi
  if [ "$rc" -eq 0 ] && [ "$audit" != 3 ] && [ "$audit" != 4 ]; then
    python3 "$repo/tools/tfaudit_schema.py" "$tmp"
    rc=$?
  fi
  if [ "$rc" -eq 0 ] && [ "$audit" = 1 ]; then
    python3 "$repo/tools/audit_cache.py" check-imports --keys "$tf_keys" "$tmp"
    rc=$?
  fi
  if [ "$audit" = 2 ]; then
    if [ "$rc" -eq 0 ]; then
      mv -f "$tmp" "$out"
      if [ -n "$ext_tmp" ] && [ -s "$ext_tmp" ]; then mv -f "$ext_tmp" "${out%.json}.ext_nodes.json"; fi
      if [ -n "$norm_tmp" ] && [ -s "$norm_tmp" ]; then mv -f "$norm_tmp" "${out%.json}.norm.json"; fi
    else rm -f "$tmp"; fi
    [ -z "$ext_tmp" ] || rm -f "$ext_tmp"
    [ -z "$norm_tmp" ] || rm -f "$norm_tmp"
  elif [ "$rc" -ne 0 ]; then
    rm -f "$tmp"
  fi
fi
if [ "$rc" -eq 0 ] && [ "$audit" = 1 ]; then
  # 3. lean4checker = the toolchain's `leanchecker`, pinned to the D1 toolchain (never the elan default; M0-inventory m10).
  tc_dir="$HOME/.elan/toolchains/$(echo "$LEAN_TOOLCHAIN" | sed 's|/|--|; s|:|---|')"
  checker="$tc_dir/bin/leanchecker"
  lc_log="$(mktemp "$repo/tools/state/.leanchecker.XXXXXX.log")"
  lc_keys="$(mktemp "$repo/tools/state/.audit_keys_lc.XXXXXX.json")"
  lc_plan="$(mktemp "$repo/tools/state/.leanchecker_plan.XXXXXX.json")"
  lc_cache="$repo/tools/state/leanchecker_cache.json"
  lc_rc=0
  if [ ! -x "$checker" ]; then
    echo "lbuild: leanchecker not found at $checker" | tee "$lc_log" >&2; lc_rc=127
  elif ! python3 "$repo/tools/audit_cache.py" keys --kind leanchecker --lean "$lean" --tool "$checker" --out "$lc_keys"; then
    echo "lbuild: leanchecker module keys failed" | tee "$lc_log" >&2; lc_rc=1
  else
    # full mode: every project module of the import closure (GL2TF.*, GL2TFTests.*, vendored lib modules) is replayed;
    # packages are not. Incremental mode (t4): only the modules whose key (the module's and its import closure's
    # .oleans, toolchain, D1 pin, manifest, checker binary) is not recorded in leanchecker_cache.json.
    pargs=()
    [ "$incremental" = 1 ] || pargs=(--full)
    mapfile -t lc_mods < <(python3 "$repo/tools/audit_cache.py" lc-plan --keys "$lc_keys" --cache "$lc_cache" \
                             --out "$lc_plan" "${pargs[@]}")
    if [ ! -s "$lc_plan" ]; then
      echo "lbuild: leanchecker plan failed" | tee "$lc_log" >&2; lc_rc=1
    elif [ "${#lc_mods[@]}" -eq 0 ]; then
      echo "lbuild: leanchecker ($mode_name): every module's key is recorded as passed; nothing to replay"
      : >"$lc_log"
    else
      echo "lbuild: leanchecker --verbose ($mode_name: ${#lc_mods[@]} project modules incl. vendored; $checker)"
      # R25 / MIG w1: import-ordered batches, one process per batch, each under the D21 scope; per-batch peak RSS
      lc_batches="$(mktemp "$repo/tools/state/.leanchecker_batches.XXXXXX.json")"
      python3 "$repo/tools/lc_batches.py" --batch-size "${LC_BATCH_SIZE:-50}" --cap-kib "${LC_BATCH_CAP_KIB:-15204352}" \
        --max-entries "${LC_BATCH_MAX_ENTRIES:-0}" --cpus "${LC_CPUS:-}" \
        --log "$lc_log" --batches-json "$lc_batches" --keys "$lc_keys" --cwd "$lean" -- \
        systemd-run --user --scope --quiet -p MemoryMax="$AUDIT_MEMORY_MAX" -p MemorySwapMax=0 \
          nice -n 10 env LEAN_NUM_THREADS="$LEAN_THREADS" lake env env LEAN_SYSROOT="$tc_dir" "$checker" --verbose \
        -- "${lc_mods[@]}"
      lc_rc=$?
      [ "$lc_rc" -ne 97 ] || echo "lbuild: R25 STOP: a leanchecker batch exceeded the per-process cap (${LC_BATCH_CAP_KIB:-15204352} kB)" >&2
      python3 - "$lc_batches" "$steps_file" <<'PY'
import json, sys
b = json.load(open(sys.argv[1]))
peaks = [x["peak_kib"] or 0 for x in b]
open(sys.argv[2], "a").write("leanchecker %s %s %s\n" % (sum(x["wall_s"] or 0 for x in b), max(peaks, default=0),
                                                       next((x["rc"] for x in b if x["rc"]), 0)))
PY
    fi
  fi
  lc_n="$(grep -c '^replaying ' "$lc_log" || true)"
  echo "lbuild: leanchecker rc=$lc_rc, $lc_n module(s) replayed: $(sed -n 's/^replaying //p' "$lc_log" | tr '\n' ' ')"
  [ "$lc_rc" -eq 0 ] || tail -n 40 "$lc_log" >&2
  # 4. the plain `#print axioms` cross-check (M0-G3 MINOR-4)
  pa_log="$(mktemp "$repo/tools/state/.print_axioms.XXXXXX.log")"
  echo "lbuild: #print axioms cross-check (lean Audit/PrintAxioms.lean)"
  timed print_axioms capped lake env lean Audit/PrintAxioms.lean >"$pa_log" 2>&1
  pa_rc=$?
  cat "$pa_log"
  # 5. leanchecker verdict (T-13, t4): rc 0, every planned module replayed, nothing outside the import closure of the
  #    GL2TF/GL2TFTests roots, and replayed + reused = exactly that closure. The per-module cache is updated only then.
  lc_ok=0
  lc_json_tmp="$(mktemp "$repo/tools/state/.leanchecker.XXXXXX.json")"
  if [ -s "$lc_plan" ] && python3 "$repo/tools/audit_cache.py" lc-finish --plan "$lc_plan" --log "$lc_log" \
       --rc "$lc_rc" --checker "$checker" --cache "$lc_cache" --out "$lc_json_tmp"; then
    lc_ok=1
  fi
  # 6. install tfaudit.json and the hash cache only if everything passed; then record the leanchecker outcome bound to it
  tf_sha=""
  if [ "$lc_ok" = 1 ] && [ "$pa_rc" -eq 0 ]; then
    mv -f "$tmp" "$out"
    if [ -s "$hc_tmp" ]; then mv -f "$hc_tmp" "$hcache"; fi
    if [ -n "${ext_tmp:-}" ] && [ -s "$ext_tmp" ]; then mv -f "$ext_tmp" "$repo/tools/state/ext_nodes.json"; fi
    if [ -n "${norm_tmp:-}" ] && [ -s "$norm_tmp" ]; then mv -f "$norm_tmp" "$repo/tools/state/norm.json"; fi
    tf_sha="$(sha256sum "$out" | cut -d' ' -f1)"
    echo "lbuild: installed $out (sha256 $tf_sha, audit mode $mode_name) and $hcache"
  else
    rm -f "$tmp"
    echo "lbuild: tfaudit.json NOT installed (leanchecker ok=$lc_ok, #print axioms rc=$pa_rc)" >&2
  fi
  python3 - "$lc_json_tmp" "$tf_sha" "$repo/tools/state/leanchecker.json" "$lc_log" "$lc_rc" "$checker" \
            "$pa_log" "$pa_rc" "$repo/tools/state/print_axioms.json" "$mode_name" "${lc_batches:-}" <<'PY'
import json, os, sys
lc_tmp, tf_sha, out, log, rc, checker, pa_log, pa_rc, pa_out, mode, batches = sys.argv[1:12]
def dump(obj, path):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")
try:
    lc = json.load(open(lc_tmp, encoding="utf-8"))
except (OSError, ValueError):  # lc-finish did not run (no plan): record a failure
    text = open(log, encoding="utf-8", errors="replace").read()
    lc = {"tool": "leanchecker", "checker": checker, "modules": ["GL2TF", "GL2TFTests"], "roots": ["GL2TF", "GL2TFTests"],
          "rc": int(rc) or 1, "ok": False, "mode": mode, "modules_replayed": 0, "replayed": [], "replayed_now": [],
          "reused": [], "verdict": "no leanchecker plan", "lean_tree_hash": os.environ["TF_LEAN_TREE_HASH"],
          "timestamp": os.environ["TF_TIMESTAMP"], "output_tail": text[-4000:]}
lc["tfaudit_sha256"] = tf_sha
if batches:  # R25 / MIG w1: [{mods, rc, peak_kib, wall_s}] per leanchecker process
    lc["batches"] = json.load(open(batches, encoding="utf-8"))
    if int(rc) == 97:
        lc["ok"] = False
        lc["verdict"] = "R25 STOP: a leanchecker batch exceeded the per-process memory cap"
dump(lc, out)
pa = open(pa_log, encoding="utf-8", errors="replace").read()
dump({"tool": "print_axioms", "file": "Audit/PrintAxioms.lean", "rc": int(pa_rc), "ok": pa_rc == "0",
      "lean_tree_hash": os.environ["TF_LEAN_TREE_HASH"], "timestamp": os.environ["TF_TIMESTAMP"],
      "output": pa[-8000:]}, pa_out)
PY
  rm -f "${lc_batches:-}" "$lc_log" "$pa_log" "$lc_json_tmp" "$lc_keys" "$lc_plan"
  if [ "$lc_ok" = 1 ]; then echo "lbuild: leanchecker OK ($mode_name)"; else echo "lbuild: leanchecker FAILED (rc=$lc_rc)" >&2; rc=1; fi
  [ "$pa_rc" -eq 0 ] || { echo "lbuild: #print axioms FAILED (rc=$pa_rc)" >&2; rc=1; }
fi
if [ "$audit" = 1 ]; then
  # t4 (R25): the step record of this audit (written also when it failed)
  rm -f "${tf_keys:-}" "${hc_tmp:-}" "${tmp:-}" "${ext_tmp:-}" "${norm_tmp:-}"
  python3 - "$steps_file" "$repo/tools/state/audit_run.json" "$mode_name" "$rc" <<'PY'
import json, os, sys
steps_file, out, mode, rc = sys.argv[1:5]
steps = []
for line in open(steps_file, encoding="utf-8"):
    f = line.split()
    if len(f) == 4:
        steps.append({"step": f[0], "wall_s": float(f[1]), "maxrss_kb": int(f[2]), "rc": int(f[3])})
    elif f:  # /usr/bin/time wrote no record (the step was killed)
        steps.append({"step": f[0], "wall_s": None, "maxrss_kb": None, "rc": int(f[-1])})
rec = {"tool": "lbuild", "mode": mode, "rc": int(rc), "timestamp": os.environ.get("TF_TIMESTAMP", ""),
       "lean_tree_hash": os.environ.get("TF_LEAN_TREE_HASH", ""), "steps": steps}
with open(out, "w", encoding="utf-8") as fh:
    json.dump(rec, fh, indent=2, sort_keys=True)
    fh.write("\n")
for s in steps:
    print(f"lbuild: step {s['step']}: wall {s['wall_s']} s, max RSS {s['maxrss_kb']} kB, rc {s['rc']}")
PY
fi
rm -f "$steps_file"
set -e
"$repo/tools/check_frozen.sh" --post "$marker" || exit $?
rm -f "$marker"
[ "$rc" -eq 0 ] && echo "lbuild: OK" || echo "lbuild: FAILED (rc=$rc)" >&2
exit "$rc"
