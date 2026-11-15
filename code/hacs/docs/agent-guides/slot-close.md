<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guide: slot close and guards of record

For the agent that runs a slot close (close-window script, figures of record, guards, CLAUDE.md diet) or regenerates the label census.
The procedure of record is the latest `docs/implementation/slot<S>/CLOSE_plan.md` and `slot<S>_close_window.sh`; the suite-status series is in `slot-history.md`.

## Checklist

`HECKE_NEBENTYPUS_NB3_FULL=1` run; `golden_landing_check.sh <R0>`; `cross_config.sh` arms (keep per-arm outputs); `claude_md_moved_check.py` with
`docs/agent-guides/*.md` among the destinations (read its verdict line); PDFs rebuilt and mirrored to gdrive; timing passes only in a quiet window;
`HACS_DATA=$HACS_DATA` for `pg_census_check.py`.

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim

### Label census — read the text

`docs/matrix-engine/tools/label_census.sh` checks every `[C, <label>]` / `\HA{<label>}` citation against `gl2_contract.tex`'s
labels (allow-list `.allow`, content-keyed; an entry matching zero sites is STALE and fails) and regenerates
`docs/latex/label_census.tsv`. **Read its `LABEL_CENSUS` line — `unresolved=0 stale=0` — never only an exit status** (a
pipeline's `… | tail` exits 0 on a failing census). Figures of record: `slot-history.md` ("Moved from CLAUDE.md at 2026-10-17").

**Rollback-lever retirement** (owner ruling 2026-10-30): a lever landed in slot S retires at the S+2 close after one default-route cluster or census run (`EFFECTIVE` read); rule and retired list: `slot-history.md` ("Moved from CLAUDE.md at 2026-11-06").
