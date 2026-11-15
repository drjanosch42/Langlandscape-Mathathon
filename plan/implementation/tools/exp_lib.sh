#!/usr/bin/env bash
# exp_lib.sh — shared helpers of the experiment loops (source it; not executable on its own).
# EXPERIMENT_PROTOCOL §7. Never calls pkill; never touches `opencode serve --service`.

EXP_TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXP_BRIEFS="$EXP_TOOLS/../experiments/briefs"
OC_LOGDIR="${OC_LOGDIR:-/home/janosch/dev/Langlandscape/agents/logs/opencode}"

ev() { "$EXP_TOOLS/exp_event.sh" "$STRAND" "$@" || true; }

model_id() {
  case "$1" in
    muse)    echo "openmathos/meta/muse-spark-open" ;;
    mistral) echo "openmathos/mistralai/mistral-large-4-0" ;;
    */*)     echo "$1" ;;
    *)       echo "exp_lib: unknown model '$1' (muse|mistral|<full id>)" >&2; return 1 ;;
  esac
}

# strand name from a worktree dir exp-sNN-<wp>-<model>  ->  sNN-<wp>-<model>
strand_of() { local b; b="$(basename "$1")"; echo "${b#exp-}"; }

# kill_new_pty <before-list>: kill only opencode-pty processes that appeared since <before-list>.
kill_new_pty() {
  local before="$1" after p cmd
  after="$(pgrep -f opencode-pty | sort || true)"
  for p in $(comm -13 <(echo "$before") <(echo "$after")); do
    cmd="$(tr '\0' ' ' < "/proc/$p/cmdline" 2>/dev/null || true)"
    case "$cmd" in
      *"serve --service"*) continue ;;          # never the service
      */opencode-pty\ daemon\ *) kill "$p" 2>/dev/null || true ;;   # only real pty daemons (not shells that merely mention it)
    esac
  done
}

# oc_run <wt> <model> <i> <timeout> <prompt> <file>...   -> opencode log in $OC_LOGDIR; echoes rc via return
# Runs in the strand worktree (cwd), stdin from /dev/null, with timeout; kills only new pty daemons;
# logs a tokens event summed over all step_finish parts.
oc_run() {
  local wt="$1" model="$2" i="$3" to="$4" prompt="$5"; shift 5
  local mid log before rc=0 files=() f
  mid="$(model_id "$model")" || return 1
  mkdir -p "$OC_LOGDIR"
  log="$OC_LOGDIR/exp-$STRAND-i$i.json"
  for f in "$@"; do files+=(--file "$f"); done
  before="$(pgrep -f opencode-pty | sort || true)"
  ( cd "$wt" && timeout "$to" opencode run --model "$mid" --auto --archived \
      --title "exp-$STRAND-i$i" --format json "${files[@]}" "$prompt" \
      < /dev/null > "$log" 2>&1 ) || rc=$?
  kill_new_pty "$before"
  if [ -s "$log" ]; then
    local tk
    tk="$(jq -rs '[.[]|select(.type=="step_finish")|.part] |
        "model='"$model"';in=\(map(.tokens.input//0)|add//0);out=\(map(.tokens.output//0)|add//0);reasoning=\(map(.tokens.reasoning//0)|add//0);cache_r=\(map(.tokens.cache.read//0)|add//0);cache_w=\(map(.tokens.cache.write//0)|add//0);cost=\(map(.cost//0)|add//0)"' \
        "$log" 2>/dev/null || true)"
    [ -n "$tk" ] && ev tokens "$tk;iter=$i"
  fi
  return "$rc"
}

# frozen_path <path>: is this a path whose change stops the strand (§7.2)?
frozen_path() {
  case "$1" in
    */lakefile*|lakefile*|*lake-manifest.json|*lean-toolchain|*/tools/pins.sha256) return 0 ;;
    plan/seed/*|lean/trace-formula-project-import/lean/*) return 0 ;;
  esac
  return 1
}

# scope_check <wt> <allowed-path>...   (paths relative to the worktree root)
# Return 0 = ok (violations reverted and logged), 2 = frozen/pin failure (strand must stop).
scope_check() {
  local wt="$1"; shift
  local line st path a ok viol=0 frz=0 allowed=("$@")
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    st="${line:0:2}"; path="${line:3}"
    path="${path##* -> }"; path="${path//\"/}"
    if frozen_path "$path"; then
      frz=1; ev violation "frozen path changed: $path"
      git -C "$wt" checkout -q -- "$path" 2>/dev/null || true   # restore; harmless
      continue
    fi
    ok=0
    for a in "${allowed[@]}"; do [ "$path" = "$a" ] && ok=1; done
    if [ "$ok" = 0 ]; then
      viol=1; ev violation "reverted: $path"
      if [ "$st" = "??" ]; then rm -f -- "$wt/$path"; else git -C "$wt" checkout -q HEAD -- "$path" 2>/dev/null || true; fi
    fi
  done < <(git -C "$wt" status --porcelain -uall)
  # deleted manifest etc. show up as ' D'; handled above by frozen_path
  if [ "$frz" = 1 ]; then ev stop "reason=frozen;where=porcelain"; return 2; fi
  if [ -d "$wt/lean/Langlandscape" ] && [ -e "$wt/lean/Langlandscape/tools/pins.sha256" ]; then
    if ! ( cd "$wt/lean/Langlandscape" && sha256sum -c --quiet tools/pins.sha256 >/dev/null 2>&1 ) \
       || [ -e "$wt/lean/Langlandscape/.lake/package-overrides.json" ]; then
      ev stop "reason=frozen;where=pins"; return 2
    fi
  fi
  [ "$viol" = 0 ] || echo "scope_check: violations reverted (see events)" >&2
  return 0
}

# commit_wt <wt> <msg> <path>...  ; echoes the new HEAD sha
commit_wt() {
  local wt="$1" msg="$2"; shift 2
  local p
  for p in "$@"; do [ -e "$wt/$p" ] && git -C "$wt" add -- "$p"; done
  git -C "$wt" commit -q --allow-empty -m "$msg" >/dev/null
  git -C "$wt" rev-parse HEAD
}

now_s() { date +%s; }

# oc_prompt_tail: fixed opencode preamble text (single line paragraphs), from briefs/preamble-opencode.md
oc_preamble() { cat "$EXP_BRIEFS/preamble-opencode.md"; }

# error_context <logfile> <target-relpath> <srcroot>: first 150 lines of errors + 20 source lines around each
error_context() {
  local log="$1" tgt="$2" root="$3" n=0 ln
  grep -nE 'error' "$log" | head -150
  echo "---- source context ----"
  while IFS= read -r ln; do
    n=$((n+1)); [ "$n" -le 8 ] || break
    echo "== $tgt:$ln"
    sed -n "$((ln>10 ? ln-10 : 1)),$((ln+10))p" "$root/$tgt" | cat -n
  done < <(grep -oE "${tgt//./\\.}:[0-9]+" "$log" | cut -d: -f2 | sort -un)
}

# ---------------------------------------------------------------------------------------------------------
# loop_run — the generic feedback loop of EXPERIMENT_PROTOCOL §7.3. The caller (exp_*_loop.sh) sets:
#   WT MODEL BRIEF STRAND WP MAX_IT IT_TIMEOUT TOTAL_MIN COMMIT_AREA
#   ALLOWED[]  (paths relative to the worktree root: the only files the model may write)
#   CONTEXT[]  (paths relative to the worktree root attached with --file in addition to the brief)
#   check_fn   (sets CK_OK CK_ERRS CK_SIG CK_FROZEN CK_BUILD_S CK_QUEUE_S, writes $CK_LOG)
# Exit codes: 0 = check ok, 1 = max iterations / no progress / out of time (best iteration committed),
#             2 = frozen / pin failure (nothing committed).
loop_run() {
  local i=1 t_start elapsed best_i=0 best_errs=999999 prev_sig="" sha prompt errfile p ctx
  mkdir -p "$WT/.exp"
  cp -f "$BRIEF" "$WT/.exp/brief.md"
  CK_LOG="$WT/.exp/check.log"
  t_start="$(now_s)"
  # shellcheck disable=SC2153  # globals set by the caller
  ev impl_start "model=$MODEL;max_it=$MAX_IT;allowed=${ALLOWED[*]}"
  while [ "$i" -le "$MAX_IT" ]; do
    elapsed=$(( ($(now_s) - t_start) / 60 ))
    if [ "$elapsed" -ge "$TOTAL_MIN" ]; then ev note "out of time after ${elapsed} min at iteration $i"; break; fi
    if [ "$i" -eq 1 ]; then
      prompt="Implement the work package described in .exp/brief.md (attached). Only the files named below may be created or changed. A checker outside your control will run after you finish."
    else
      prompt="The checker reported the errors in .exp/errors-$((i-1)).txt. Fix them; keep declaration names and signatures from the brief unchanged."
    fi
    prompt="$prompt $(oc_preamble | sed "s|<files>|${ALLOWED[*]}|g")"
    ctx=(".exp/brief.md")
    for p in "${CONTEXT[@]}" "${ALLOWED[@]}"; do [ -e "$WT/$p" ] && ctx+=("$p"); done
    [ "$i" -gt 1 ] && ctx+=(".exp/errors-$((i-1)).txt")
    oc_run "$WT" "$MODEL" "$i" "$IT_TIMEOUT" "$prompt" "${ctx[@]}" || ev note "opencode rc=$? at iteration $i"
    # §7.2: scope + pin check BEFORE any build/check process
    scope_check "$WT" "${ALLOWED[@]}" || { rc=$?; echo "STOP: frozen/pin failure at iteration $i" >&2; return "$rc"; }
    for p in "${ALLOWED[@]}"; do [ -e "$WT/$p" ] && mkdir -p "$WT/.exp/iter-$i" && ( cd "$WT" && cp --parents "$p" ".exp/iter-$i/" ); done
    check_fn
    if [ "$CK_FROZEN" = 1 ]; then ev stop "reason=frozen;where=check-exit-99"; echo "STOP: wrapper exit 99" >&2; return 2; fi
    ev build "s=$CK_BUILD_S;queue=$CK_QUEUE_S;iter=$i;ok=$CK_OK;errs=$CK_ERRS"
    if [ "$CK_OK" = 1 ]; then
      sha="$(commit_wt "$WT" "$COMMIT_AREA: S01-${WP^^} iteration $i" "${ALLOWED[@]}")"
      ev impl_end "sha=$sha;result=ok;iter=$i"; echo "OK at iteration $i ($sha)"; return 0
    fi
    errfile="$WT/.exp/errors-$i.txt"
    error_ctx_fn > "$errfile"
    if [ "$CK_ERRS" -lt "$best_errs" ]; then best_errs="$CK_ERRS"; best_i="$i"; fi
    if [ "$CK_SIG" = "$prev_sig" ] && [ -n "$prev_sig" ]; then ev note "no change in error set at iteration $i"; break; fi
    prev_sig="$CK_SIG"
    i=$((i+1))
  done
  # not ok: restore and commit the best iteration (fewest errors)
  if [ "$best_i" -gt 0 ]; then
    for p in "${ALLOWED[@]}"; do [ -e "$WT/.exp/iter-$best_i/$p" ] && cp -f "$WT/.exp/iter-$best_i/$p" "$WT/$p"; done
  fi
  sha="$(commit_wt "$WT" "$COMMIT_AREA: S01-${WP^^} best iteration ${best_i}" "${ALLOWED[@]}")"
  ev impl_end "sha=$sha;result=red;best_iter=$best_i;errs=$best_errs"
  echo "RED: committed best iteration $best_i ($sha), errors=$best_errs"
  return 1
}

# default error-context writer (tex / py): tail of the log; Lean overrides it
error_ctx_fn() { tail -n 150 "$CK_LOG"; }

# signature of an error set: messages without file:line:col, sorted (for "no change for 2 iterations")
err_sig() { grep -E "$1" "$CK_LOG" | sed -E 's/^[^ ]*:[0-9]+:[0-9]+:? *//; s/line [0-9]+//g' | sort | cksum | cut -d' ' -f1; }
