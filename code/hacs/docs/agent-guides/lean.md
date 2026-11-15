<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guide: Lean lane

For an agent that builds, edits or checks anything under `lean/` (proofs, [GT] blueprint, census, replay). Read it with CLAUDE.md before the first `lake` call.

## Moved from CLAUDE.md at the slot-26 close (2026-11-12), verbatim

### Lean lane (`lean/`; full text in `architecture-detail.md`)

- [LP] v1.10; **not binding yet** ([C] stays the contract; owner Q5 rulings 2026-10-05). Lake project `GL2`; toolchain
  **`leanprover/lean4:v4.33.0`**, mathlib pinned at **`db584cd`** (the v4.33.0 tag — **not** FLT's v4.33.1).
- **One shared dependency tree** `$HACS_DATA/lean-deps/`, linked by `lean/tools/lean_link_deps.sh` as
  the git-ignored symlink `lean/.lake/packages`; never a per-worktree mathlib, never `packagesDir` in the lakefile.
- **Never run `lake update`** (in the main checkout or any worktree): through the symlink it deletes the shared mathlib
  checkout. Builds: `disk_guard.sh --min-free-gb 15` first, plain `lake build` (no `-j`), never beside a ≥ 20 GB C++ run.
- **Census gate**: `lean/tools/lean_census.sh` prints one line — read the text (`… verdict=OK`); replay `lean_replay.sh` (`LEAN_REPLAY … verdict=OK`,
  cap 16 GiB); lines of record: `slot-history.md` ("Moved from CLAUDE.md at 2026-10-17 (the G2-A/B merge)"). **Regenerate `census.tsv` with `lean_census.sh
  --emit` after any [GT] or Lean change, in the same commit** (C++ sees only the committed file). No `native_decide`.
- FLT vendoring: `lean/Vendor/AnthropicFLT/`, 25 modules byte-identical to upstream (Apache-2.0); option allowance for that lib only.

## Repeated safety rules

Also binding for every Lean run (repeated from CLAUDE.md / memory): run under the shared lock `flock -x ~/.cache/gl2tf/lean.lock`; **never `lake update`**.

Note: bare `census.tsv` above means `lean/census.tsv` (other `census.tsv` files exist under `docs/`).
