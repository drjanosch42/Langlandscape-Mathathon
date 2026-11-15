<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guide: registering a new validation

For an agent whose package registers a validation (or a console verb / type / setting / CLI token): where it registers, where its sources are listed, what must be regenerated.

## Checklist: what must be regenerated or updated in the same commit

1. Tier (`fast` / `standard` / `slow`) in the registration; 2. `SPDX-License-Identifier` header on every new file (`add_spdx.py --check`);
3. `docs/latex/tools/gen_cli_manual_tables.sh <binary>` (else `CliManualCoverageValidation` fails); 4. `gen_console_md.sh <binary>` for a verb / type / setting;
5. `docs/cluster/noctua2/EXPECT_NAMES` (= `--list` count); 6. the entry in `docs/validation-catalogue.md`; 7. the roster figures in CLAUDE.md.

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim (slot numbers updated 9–25 / 26 to 9–26 / 27)

### Per-slot registration fragments (the pattern for every slot)

- **Closed slots 9–26: one file each**, `src/hacs/Registry/Slot<S>.cpp` (package functions `RegisterSlot<S><pkg>()` kept, aggregate
  `RegisterSlot<S>()` in the old call order); their sources sit per module in `cmake/sources/<Module>.cmake` (`Special.cmake` = library targets, flags,
  notebook sources). Do not reorder: the call order is the `--list` order. Old per-slot READMEs: `docs/implementation/registry-slot-readmes-9-26.md`;
  convention: `Registry/README.md`.
- **The open slot (27)**: a package registers **only** in `Registry/Slot27/<name>.cpp` (`RegisterSlot27<name>()`, called at the tail of
  `RegisterAllValidations()`) and lists sources **only** in `cmake/slot27/<name>.cmake` (created by the first package); two one-line shared edits. Folded at its close.
- Research packages use the slot's shared read-only binary `$HACS_DATA/s<slot>/bin/hacs` + `.sha256`, published with a relative `cohomology_app -> hacs` symlink (copy with `cp -P` / `cp -a`, never a regular file named `cohomology_app`).
