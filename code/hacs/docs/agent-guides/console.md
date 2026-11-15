<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guide: console, `--serve`, notebook

For an agent that adds or changes a console verb, type or setting, an OC script, or the `--serve` / notebook gateway.

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim

- **Console** (`Console/`, OC scripts `*.oc`, [P]) — CLI: `--console` / `-i` / `--script <f.oc>` / `-c` / `-`, `--set key=value`,
  `--log`. **Exit codes: 0** ok, **1** usage, **2** parse, **3** runtime, **4** failed `assert`, **5** `NotImplementedInThisBuild`.
  Numbered scripts with frozen `.expected` transcripts; regenerate `docs/console/console.md` (`gen_console_md.sh <binary>`) and
  the manual's tables whenever a verb, type or setting is registered. **`--serve`** (only with `OC_BUILD_NOTEBOOK=ON`): one
  read-only NDJSON session serving only overloads tagged `read_only` (`Console/Bindings/ReadOnlyTags.cpp` + twin
  `Console/serve/read_only_verbs.tsv`, a new verb needs a row in both).
