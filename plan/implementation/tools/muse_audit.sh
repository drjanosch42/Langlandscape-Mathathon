#!/usr/bin/env bash
# plan/implementation/tools/muse_audit.sh NN  — Muse Spark Open audit of plan/implementation/stage-NN.md
# Runs in a scratch copy (opencode --auto writes relative to cwd); result -> plan/implementation/audits/stage-NN-muse.md
set -euo pipefail
nn="$1"; wt="$(cd "$(dirname "$0")/../../.." && pwd)"; impl="$wt/plan/implementation"
scr="$(mktemp -d /tmp/muse-impl-$nn-XXXX)"
cp "$impl/stage-$nn.md" "$impl/OVERVIEW.md" "$wt/plan/staged/SPLIT.md" "$scr/"
[ "$nn" = 01 ] && [ -f "$impl/EXPERIMENT_PROTOCOL.md" ] && cp "$impl/EXPERIMENT_PROTOCOL.md" "$scr/"
cp "$wt"/plan/staged/stage-$nn-*.tex "$scr/stage.tex"
files=(); for f in "$scr"/*; do files+=(--file "$f"); done
before="$(pgrep -f opencode-pty | sort || true)"; t0=$(date +%s)
( cd "$scr" && timeout 30m opencode run --model openmathos/meta/muse-spark-open --auto --archived \
  --title "impl-audit-$nn" --format json "${files[@]}" \
  "You audit an IMPLEMENTATION PLAN (stage-$nn.md) for a Lean 4 / LaTeX / Python project on the Jacquet-Langlands correspondence. Context: OVERVIEW.md (conventions, Lean project structure, resource policy), stage.tex (the mathematical plan whose labels the work packages cite), SPLIT.md. Check: (1) every WP has id, inputs, outputs, acceptance check, difficulty, model, estimates, deps; (2) cited labels exist in stage.tex; (3) the dependency DAG is acyclic, complete (no missing edges: a WP using an output of another must depend on it) and the stated critical path is really the longest path; (4) acceptance checks are mechanical and sufficient; (5) model choices are plausible for the difficulty; (6) resource limits (<=2 local Lean builds, <=3 TITAN, <=3 Claude agents) are respected; (7) mathematical or Lean-technical errors in the WP descriptions; (8) for stage 01 also EXPERIMENT_PROTOCOL.md if attached (coherence, measurable criteria). Only report DEFECTS, no endorsements. For each finding: id F<n>, severity (critical/major/minor), location, problem, suggested fix. Write the audit as markdown to the file audit.md in the current directory. Touch nothing else." \
  < /dev/null > "$scr/out.json" 2>&1 ) || echo "opencode exit $?" >&2
t1=$(date +%s); after="$(pgrep -f opencode-pty | sort || true)"
for p in $(comm -13 <(echo "$before") <(echo "$after")); do kill "$p" 2>/dev/null || true; done
mkdir -p "$impl/audits"
if [ -s "$scr/audit.md" ]; then cp "$scr/audit.md" "$impl/audits/stage-$nn-muse.md"
else jq -rs '[.[]|select(.type=="text")|.part.text]|join("")' "$scr/out.json" > "$impl/audits/stage-$nn-muse.md"; fi
echo "stage $nn start=$(date -d @$t0 +%T) wall=$((t1-t0))s tokens=$(jq -c 'select(.type=="step_finish")|.part.tokens' "$scr/out.json" | tail -1)" >> "$impl/audits/muse_metrics.txt"
echo "done stage $nn: $((t1-t0)) s -> $impl/audits/stage-$nn-muse.md"
