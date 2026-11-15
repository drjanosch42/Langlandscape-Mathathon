# shellcheck shell=bash disable=SC2154
# tools/locks.sh: sourced (not executed) by lbuild.sh and lfile.sh after deps_load.sh. S01-X1b lock model (OVERVIEW §3.4).
# Needs $repo, $LOCK_DIR, $LOCK_WAIT, $SLOTS and a die() function. Acquisition order (Fable C3), the same in both scripts:
#   (1) exp.lock (callers of experiment checks, outside these scripts), (2) lean.lock SHARED (fd 9; the import's lbuild takes
#   it EXCLUSIVELY on the same file and so excludes us), (3) the per-checkout lock (fd 6; lbuild exclusive, lfile shared),
#   (4) a node slot slot.N (fd 7; flock -n retry loop, only after (3) is held, so nobody waits for (3) while holding (4)),
#   (5) the memory wait (caller). Locks are released in reverse order when the process exits. No lock file is created
#   with a new name scheme except ll-<sha1 of realpath of the project>.lock; no lock file is ever deleted or renamed.
# Both acquire_* print the ISO-UTC timestamps `slot acquired` / `mem ok` to stderr (EXPERIMENT_PROTOCOL §10).

ll_ts() { date -u +%Y-%m-%dT%H:%M:%SZ; }

# ll_lock_shared_lean <who>: (2)
ll_lock_lean() {
  local who="$1"
  mkdir -p "$LOCK_DIR/markers"
  exec 9>"$LOCK_DIR/lean.lock"
  flock -s -w "$LOCK_WAIT" 9 || die "could not get the shared lean.lock in ${LOCK_WAIT}s (an import build is running?)"
  export GL2TF_LOCK_HELD="shared"
  : "$who"
}

# ll_lock_checkout <x|s>: (3), exclusive (lbuild) or shared (lfile), per checkout
ll_lock_checkout() {
  local mode="$1" h
  h="$(printf '%s' "$(realpath "$repo")" | sha1sum | cut -d' ' -f1)"
  exec 6>"$LOCK_DIR/ll-$h.lock"
  flock "-$mode" -w "$LOCK_WAIT" 6 || die "could not get the per-checkout lock ll-$h.lock ($mode) in ${LOCK_WAIT}s"
}

# ll_take_slot: (4); sets $slot
ll_take_slot() {
  local s waited=0
  slot=""
  while [ -z "$slot" ]; do
    for s in $(seq 1 "$SLOTS"); do
      exec 7>"$LOCK_DIR/slot.$s"
      if flock -n 7; then slot="$s"; break; fi
      exec 7>&-
    done
    [ -n "$slot" ] && break
    [ "$waited" -ge "$LOCK_WAIT" ] && die "no free node slot after ${LOCK_WAIT}s"
    sleep "${LL_SLOT_POLL:-10}"; waited=$((waited + ${LL_SLOT_POLL:-10}))
  done
  export GL2TF_LOCK_HELD="$GL2TF_LOCK_HELD+slot.$slot"
  echo "slot acquired $(ll_ts)" >&2
}

# ll_mem_wait <who> <need_kb>: (5)
ll_mem_wait() {
  local who="$1" need="$2" avail
  while :; do
    avail="$(awk '/^MemAvailable:/ {print $2}' /proc/meminfo)"
    [ "$avail" -ge "$need" ] && break
    echo "$who: MemAvailable ${avail} kB < ${need} kB; retrying in 5 min ($(date +%T))"
    sleep 300
  done
  echo "mem ok $(ll_ts)" >&2
}
