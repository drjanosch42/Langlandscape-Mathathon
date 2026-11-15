#!/usr/bin/env bash
# exp_event.sh <strand> <event> <k=v;k=v;...>
# Appends one event line to the single events.tsv (EXPERIMENT_PROTOCOL §5), under flock, by ABSOLUTE path
# (so a strand worktree never writes its own copy). Columns: ts<TAB>strand<TAB>event<TAB>data.
# EXP_EV may override the file (pre-flight tests only).
set -euo pipefail
EV="${EXP_EV:-/home/janosch/dev/Langlandscape-wt/impl/plan/implementation/experiments/events.tsv}"
[ "$#" -ge 2 ] || { echo "usage: exp_event.sh <strand> <event> [k=v;...]" >&2; exit 64; }
strand="$1"; event="$2"; data="${3:-}"
# keep the TSV well-formed: tabs/newlines in data become spaces
data="${data//$'\t'/ }"; data="${data//$'\n'/ }"
mkdir -p "$(dirname "$EV")"
(
  flock 8
  [ -s "$EV" ] || printf 'ts\tstrand\tevent\tdata\n' >> "$EV"
  printf '%s\t%s\t%s\t%s\n' "$(date -u +%FT%TZ)" "$strand" "$event" "$data" >> "$EV"
) 8>"$EV.lock"
