<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# HACS seed -- provenance

This directory is a **seed** of HACS (Harder Arithmetic Cohomology System): the public release tree
plus a curated set of internal development documents, extracted by the HACS seed profile
(`extract.py --profile seed`, documented in the development repository as `docs/hacs/SEED_extraction_plan.md`).
Owner-machine paths, host names and accounts were replaced by placeholders (table below).

| item | value |
|---|---|
| HACS version (`VERSION`) | 0.2.1 |
| public release | HACS 0.2.1 (public tag pending) |
| source commit (development repository) | `0ea75f737d005f8b2ee0c766df19e1ed5e571c9c` |
| source committer date | 2026-11-14T18:49:26+01:00 |
| manifest sha256 | `d14508dd84cdf968422ff2675448b255e3b8163522904279d89740a666bc3422` |
| files | 3255 |

Commit hashes cited in the documents of this tree (handovers, plans, the validation catalogue, data
records, comments) refer to the **non-public development history** of HACS. They are kept as records
of where a result or a change came from; they cannot be resolved in this repository or in the public
HACS repository, and nothing here depends on resolving them.

## Curated internal documents

| path | why it ships |
|---|---|
| `BUILDING.md` | tools/hacs_dist/BUILDING.release.md |
| `CHANGELOG.md` | tools/hacs_dist/CHANGELOG.release.md |
| `CHANGES.md` | tools/hacs_dist/CHANGES.seed.md |
| `CLAUDE.md` | tools/hacs_dist/CLAUDE.seed.md |
| `README.md` | tools/hacs_dist/README.release.md |
| `docs/KNOWN_ISSUES.md` | defect root causes and open findings |
| `docs/agent-guides/README.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/agent-guides/benchmarking.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/agent-guides/console.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/agent-guides/lean.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/agent-guides/new-validation.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/agent-guides/slot-close.md` | role guides for agents (Lean, benchmarking, console, slot close, new validation); cluster.md withheld (SEED plan 3.3) |
| `docs/architecture-detail.md` | per-module architecture prose, build switches, presets, targets |
| `docs/console/00-console-interface-plan.md` | [P] the console specification (verbs, types, --serve), binding for console changes |
| `docs/implementation/hecke_extensions_implementation_plan.md` | [X] the binding implementation plan (cited by label from [C]/[E] and the code) |
| `docs/implementation/lean/00-lean-programme-plan.md` | [LP] the Lean programme plan (the ground-truth blueprint [GT] ships under lean/blueprint/) |
| `docs/implementation/slot27/00-slot27-plan.md` | the open development slot's plan (state of the work at seed time) |
| `docs/implementation/slot27/HANDOVER_1113.md` | the latest session handover (state of the work at seed time) |
| `docs/matrix-engine/00-implementation-plan.md` | matrix-engine plan; section 16.3 is the engine acceptance matrix cited by the engine API |
| `docs/matrix-engine/campaign.md` | campaign driver specification (--campaign), cited by CLAUDE.md |
| `docs/performance-reference.md` | benchmark references and standing gates (timing claims are checked against it) |
| `docs/validation-catalogue.md` | what every validation checks: counts, tiers, arms, oracles, env hooks (read before touching a validation) |

## External material (not from the development repository)

| entry | source | files | bytes | note |
|---|---|---:|---:|---|
| jl_exchange | `$JL_EXCHANGE` | 206 | 8535148 | HACS answers to the Jacquet-Langlands feasibility requests (Task 0, v6 Task 1): results, run logs, data, scripts (owner question SQ3) |
| jl_requests | `$JL_RESEARCH/docs/briefings` | 2 | 10241 | the Jacquet-Langlands project's requests to HACS that the answers reply to (owner question SQ3) |

## Placeholders

`$HACS_SRC` this tree; `$HACS_DATA` the persistent scratch / data root of HACS runs; `$DATA_ROOT` other data directories; `$HACS_RUN_LOG` the run log of heavy runs; `$JL_EXCHANGE` the HACS <-> Jacquet-Langlands exchange directory; `$JL_RESEARCH` the Jacquet-Langlands research checkout; `$LANGLANDSCAPE` the Langlandscape checkout; `$HOME` other home paths; `<private-library>` the owner's private literature library (never public); `<host-path>` other host paths; `host-A`, `host-B`, `arm-board`, `cluster-A`, `cluster-B`, `cluster-node`, `<cluster-host>`, `<project-account>`, `<user>`, `<email>`, `<agent-session>` machines, accounts and links.

## Scrubbed files (rewrites per rule)

| path | rewrites |
|---|---|
| `docs/KNOWN_ISSUES.md` | hacs_data 2 |
| `docs/agent-guides/README.md` | cluster_a 1, cluster_b 1 |
| `docs/agent-guides/benchmarking.md` | run_log 1 |
| `docs/agent-guides/lean.md` | hacs_data 1 |
| `docs/agent-guides/new-validation.md` | hacs_data 1 |
| `docs/agent-guides/slot-close.md` | hacs_data 1 |
| `docs/architecture-detail.md` | arm_board 1, data_root 1, hacs_data 3 |
| `docs/console/00-console-interface-plan.md` | hacs_data 1, other_home 1 |
| `docs/implementation/hecke_extensions_implementation_plan.md` | arm_board 1, cluster_a 8, cluster_b 3, data_root 1, hacs_data 7, host_b 2, library_path 3 |
| `docs/implementation/lean/00-lean-programme-plan.md` | cluster_a 2, cluster_b 3, data_root 4, hacs_data 7, library_path 2 |
| `docs/implementation/slot27/00-slot27-plan.md` | cluster_a 1, cluster_b 1, hacs_data 3, host_b 11, lean_lock 1, run_log 3, user_account 1 |
| `docs/implementation/slot27/HANDOVER_1113.md` | hacs_data 1, host_b 2, jl_exchange 1 |
| `docs/jl_exchange/hacs-answers/task0_inscope/data/persist/runs.tsv` | hacs_data 30 |
| `docs/jl_exchange/hacs-answers/task0_inscope/data/runs.tsv` | hacs_data 108 |
| `docs/jl_exchange/hacs-answers/task0_inscope/run_log.md` | hacs_data 2, run_log 1 |
| `docs/jl_exchange/hacs-answers/task0_inscope/scripts/run_cells.py` | hacs_data 1 |
| `docs/jl_exchange/hacs-answers/task1_v6/run_log.md` | hacs_data 2, run_log 1 |
| `docs/jl_exchange/hacs-answers/task1_v6/scripts/summarize.py` | jl_exchange 1 |
| `docs/jl_exchange/hacs-answers/task1_v6/scripts/xcheck.py` | jl_exchange 1 |
| `docs/jl_exchange/requests/hacs_request_v4.txt` | jl_exchange 1, run_log 1 |
| `docs/jl_exchange/requests/hacs_request_v6.txt` | jl_exchange 1, run_log 1 |
| `docs/matrix-engine/campaign.md` | data_root 1 |
| `docs/performance-reference.md` | cluster_b 2 |
| `docs/validation-catalogue.md` | hacs_data 1, host_b 4 |
