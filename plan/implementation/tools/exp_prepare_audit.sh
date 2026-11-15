#!/usr/bin/env bash
# exp_prepare_audit.sh <strand> <r>        (EXPERIMENT_PROTOCOL §2.3, §10)
#   <strand>  sNN-<wp>-<model>, worktree /home/janosch/dev/Langlandscape-wt/exp-<strand> (EXP_WT_ROOT overrides the parent dir)
#   <r>       audit round (0 = first audit; r >= 1 adds the prior-findings sentence; the stage master puts
#             prior-findings.md into the dir)
# Creates a scratch dir (under $EXP_AUDIT_ROOT, default $TMPDIR/exp-audit) with the blind audit inputs:
#   strand-<X>.patch   git diff <base>..HEAD, no commit metadata (a blind letter X, never the model)
#   brief.md           briefs/sNN-<wp>.md (stage 01: briefs/<wp>.md)
#   stage-excerpt.tex  the environments of the stage tex cited by label in the brief (plus a directly following proof)
#   check.txt          output of the brief's acceptance command, run NOW on the strand's HEAD (by the stage master)
#   audit-prompt.md    audit-template.md filled in
# Prints the directory (only line on stdout). The blind label X is shuf-drawn once per strand and recorded with
#   exp_event.sh <strand> setup label=X (first call only). EXP_EV overrides the events file; EXP_NO_CHECK=1 skips check.txt.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$here/../../.." && pwd)"
EXPD="$here/../experiments"
EV="${EXP_EV:-/home/janosch/dev/Langlandscape-wt/impl/plan/implementation/experiments/events.tsv}"
[ "$#" -eq 2 ] || { echo "usage: $0 <strand> <r>" >&2; exit 64; }
strand="$1"; r="$2"
case "$r" in ''|*[!0-9]*) echo "r must be a non-negative integer" >&2; exit 64 ;; esac
st="${strand%%-*}"; wp="${strand#*-}"; wp="${wp%-*}"
WT="${EXP_WT_ROOT:-/home/janosch/dev/Langlandscape-wt}/exp-$strand"
brief="$EXPD/briefs/$st-$wp.md"; [ -f "$brief" ] || brief="$EXPD/briefs/$wp.md"   # stage 01 used briefs/<wp>.md
[ -d "$WT" ] || { echo "no worktree $WT" >&2; exit 1; }
[ -f "$brief" ] || { echo "no brief $brief" >&2; exit 1; }

case "$st-$wp" in
  s01-l9) T=Lean; d=hard ;;       s01-l5a) T=Lean; d=routine ;;   s01-l13) T=Lean; d=mechanical ;;
  s01-c1) T=code; d=routine ;;    s01-m2) T=LaTeX; d=routine ;;   s01-m4) T=LaTeX; d=hard ;;
  s01-x3) T="Lean infra"; d=mechanical ;;
  s02-l1) T=Lean; d=hard ;;       s02-m1) T=LaTeX; d=routine ;;   s03-m2) T=LaTeX; d=hard ;;
  s04-l6) T=Lean; d=hard ;;       s05-m3) T=LaTeX; d=hard ;;      s06-l5b) T=Lean; d=hard ;;
  *) echo "unknown wp $wp" >&2; exit 1 ;;
esac

# --- base sha: `setup ... base=<sha>` event of this strand, else merge-base with wip-implementation
base=""
if [ -f "$EV" ]; then
  base="$(awk -F'\t' -v s="$strand" '$2==s && $3=="setup" && $4 ~ /base=/ {match($4,/base=[0-9a-f]+/); b=substr($4,RSTART+5,RLENGTH-5)} END{print b}' "$EV")"
fi
[ -n "$base" ] || base="$(git -C "$WT" merge-base HEAD wip-implementation)"
head_sha="$(git -C "$WT" rev-parse HEAD)"

# --- blind label: reuse, else shuf over letters not used by siblings of this WP
label=""
if [ -f "$EV" ]; then
  label="$(awk -F'\t' -v s="$strand" '$2==s && $4 ~ /label=/ {match($4,/label=[A-Z]/); l=substr($4,RSTART+6,1)} END{print l}' "$EV")"
fi
if [ -z "$label" ]; then
  used=" "
  if [ -f "$EV" ]; then
    used=" $(awk -F'\t' -v p="$st-$wp-" 'index($2,p)==1 && $4 ~ /label=/ {match($4,/label=[A-Z]/); printf "%s ", substr($4,RSTART+6,1)}' "$EV") "
  fi
  for c in $(shuf -e A B C D E F); do case "$used" in *" $c "*) ;; *) label="$c"; break ;; esac; done
  [ -n "$label" ] || { echo "no free label" >&2; exit 1; }
  "$here/exp_event.sh" "$strand" setup "label=$label"
fi

AR="${EXP_AUDIT_ROOT:-${TMPDIR:-/tmp}/exp-audit}"; mkdir -p "$AR"
out="$(mktemp -d "$AR/$wp-$label-r$r.XXXXXX")"

# --- patch (no commit metadata)
git -C "$WT" diff --no-color --no-ext-diff --binary "$base..$head_sha" > "$out/strand-$label.patch"
if grep -nEi 'langlandscape-wt|exp/s[0-9][0-9]|exp-s[0-9][0-9]|muse|mistral|haiku|sonnet|opus|co-authored' "$out/strand-$label.patch" > "$out/.fingerprint-hits" 2>/dev/null; then
  echo "WARNING: patch contains possible author fingerprints; see $out/.fingerprint-hits (do not hand to the auditor unredacted)" >&2
else rm -f "$out/.fingerprint-hits"; fi
cp "$brief" "$out/brief.md"

# --- stage-tex excerpt of the cited labels
tex="$(find "$ROOT/plan/staged" -name "stage-${st#s}-*.tex" | head -n 1)"
labels="$(grep -oE "\b(def|lem|thm|prop|rem|ex|if|cor):${st}-[A-Za-z0-9_-]+" "$brief" | sort -u | tr '\n' ' ' || true)"
awk -v labs="$labels" '
  BEGIN { n = split(labs, L, " "); for (i = 1; i <= n; i++) want[L[i]] = 1 }
  { line[NR] = $0 }
  END {
    for (i = 1; i <= NR; i++) {
      if (!match(line[i], /\\begin\{[A-Za-z*]+\}/)) continue
      env = substr(line[i], RSTART + 7, RLENGTH - 8)
      if (!match(line[i], /\\label\{[^}]*\}/)) continue
      lab = substr(line[i], RSTART + 7, RLENGTH - 8)
      if (!(lab in want)) continue
      print "% ---- " lab " ----"
      for (j = i; j <= NR; j++) { print line[j]; if (index(line[j], "\\end{" env "}")) break }
      k = j + 1; while (k <= NR && line[k] ~ /^[ \t]*$/) k++
      if (k <= NR && line[k] ~ /\\begin\{proof\}/) {
        for (m = k; m <= NR; m++) { print line[m]; if (index(line[m], "\\end{proof}")) break }
      }
      print ""
    }
  }' "$tex" > "$out/stage-excerpt.tex"

# --- acceptance check, run independently by the stage master on the strand's HEAD
{
  echo "# acceptance check, run on commit $head_sha (strand label $label, round $r)"
  echo "# uncommitted changes in the worktree (should be none):"; git -C "$WT" status --porcelain | sed 's/^/#   /'
} > "$out/check.txt"
if [ "${EXP_NO_CHECK:-0}" != 1 ]; then
  cmd="$(awk '/^## 4\. Acceptance command/{s=1; next} s && /^```bash/{on=1; next} on && /^```/{exit} on{print}' "$brief")"
  rc=0
  ( cd "$WT" && timeout 40m bash -c "$cmd" ) >> "$out/check.txt" 2>&1 || rc=$?
  echo "# acceptance command exit code: $rc" >> "$out/check.txt"
fi

# --- audit prompt from the template
tmpl="$EXPD/briefs/audit-template.md"
if [ "$r" -ge 1 ]; then
  rsent='Round '"$r"': prior-findings.md — verify each prior finding as RESOLVED / OPEN / REGRESSED, then audit the new diff.'
else rsent=''; fi
sed -e "s|<X>|$label|g" -e "s|<WP-id>|S${st#s}-${wp^^}|g" -e "s|<T>|$T|g" -e "s|<d>|$d|g" -e "s|<r>|$r|g" \
    -e "s|<Round r ≥ 1: prior-findings.md — verify each prior finding as|$rsent@@|" \
    -e "s|^RESOLVED / OPEN / REGRESSED, then audit the new diff.>||" "$tmpl" > "$out/audit-prompt.md"
# the template's round clause spans one line; drop the leftover marker
sed -i -e 's/@@.*$//' "$out/audit-prompt.md"
echo "$out"
