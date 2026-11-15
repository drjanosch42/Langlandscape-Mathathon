<!-- SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent guides

`CLAUDE.md` is loaded into every session and holds only what every agent needs: build, run, validate, the hard rules
(golden, env emitters, disk and scratch, worktrees, licences, no `lake update`, no cluster connection), the NDEBUG policy,
the binding documents and the figures of record. Material that only one kind of agent needs lives here, **one file per
role** (the consumer), not per topic history:

| File | Role |
|---|---|
| `lean.md` | Lean lane: toolchain, shared dependency tree, census and replay |
| `benchmarking.md` | timing, standing gates, placement, `--bench`, CMake options, cross-config |
| `cluster.md` | cluster kits (cluster-A, cluster-B), `EXPECT_NAMES`, RSS prediction; Jetson and Termux builds |
| `console.md` | console, OC scripts, `--serve`, manual regeneration |
| `slot-close.md` | the close: where the procedure lives, label census, rollback-lever retirement |
| `new-validation.md` | registration fragments of the open slot, shared research binaries |

**Convention.** The lead briefs a role agent with "read `CLAUDE.md` and `docs/agent-guides/<role>.md`". A role file may
repeat a short safety rule that also stays in `CLAUDE.md`; otherwise text lives in one place. Text moved out of `CLAUDE.md`
sits under a heading "Moved from CLAUDE.md at <date or slot event>, verbatim" and the move is proven by
`docs/matrix-engine/tools/claude_md_moved_check.py <old CLAUDE.md> CLAUDE.md <destinations…>` (`missing=0 verdict=OK`).
Created at the slot-26 close (2026-11-12, owner instruction).
