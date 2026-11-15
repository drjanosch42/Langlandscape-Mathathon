# Rule: machine resources (all coordinators and workers)

Check before spawning any agent, opencode job or Lean build (`df -BG /mnt/c`, `free -g`):
- `/mnt/c` free (the WSL2 disk image lives there) **< 50 GB → warn** the global master.
  **< 20 GB → spawn nothing new**; report and wait until resolved.
- RAM: keep ≥ 12 GB available. Budget ~2 GB per Claude subagent and ~1 GB per opencode job.
  Lean builds: ~4–8 GB each with Mathlib loaded; at most **2 concurrent Lean builds** on Fabian's node
  (82 GB), always through the wrapper scripts, which apply locks and memory caps.
- Keep the machine busy: queue Lean builds/checks while other agents write the next code; batch
  file checks rather than running many small builds.

## TEMPORARY (2026-11-14, Fabian): no new Lean jobs on localhost
Local CPU/GPU is reserved for the upcoming HACS work (`code/hacs/`, based on HACS release 0.2.1).
All new Lean builds and checks (`lbuild.sh`, `lfile.sh`, `check_wp.sh` with builds) run on **TITAN**; jobs
already running locally may finish. Job flow (file outbox, plan/implementation/OVERVIEW.md §4.3, F11): the
coordinator writes a **committed** outbox file `plan/implementation/outbox/<UTC>_<id>.md` (the job spec) and notifies
the global master by SendMessage ("outbox: <file>"; the notification is never the job spec) → the global master pushes
the needed branch and relays the outbox file to TITAN → TITAN pushes results to `titan/<job-id>` → the global master
reports back. Batch jobs to amortize the round trip.

## Nodes
| Node | Session | CPU | RAM | Disk free | Lean builds | Frozen Mathlib |
|---|---|---|---|---|---|---|
| fabian (localhost) | JL MASTER RZN | 32 threads | 82 GB | /mnt/c 182 GB | 2 | see master memory |
| abhijit (notebook i5-1235U) | own Claude session (other account); git message channel only (`agents/messages/`) | 12 threads | 15 GB (≈ 4 GB free) | 107 GB | none; built Mathlib at the pin is present but RAM-limited: one Lean draft check at a time under the `lean.md` exception (≥ 4 GB free before it; no `lake`); 3–4 agents; one heavy job (`latexmk` or `lean`) at a time; acceptance only in TITAN rounds | present, RAM-limited; no TITAN access |
| TITAN (helper, Lean build node) | TITAN | 16 threads | 94 GB | 708 GB | 3 (~5 threads, ≤25 GB each; estimate) | `/home/claude/data/gl2tf-data/mathlib4_v4350` |
| CONCEPTD (helper, Lean build node #2) | CONCEPTD | i7-10875H, 8C/16T | 25 GiB (WSL) + 7 GiB swap | /mnt/c 431 GB | 2 (peak ≈ 5.2 GiB each; import build 6:45, warm build 2:04) | `/home/janosch/data/mathlib4_v4350` (node-local) |

TITAN and CONCEPTD receive Lean jobs only from the global master (CONCEPTD results go to `conceptd/<job-id>`) (SendMessage to `TITAN`), works in its own clone
`/home/claude/dev/Langlandscape`, commits, and pushes ONLY to branches `titan/<job-id>` (never `main` or `wip-*`); the global master integrates them. Use TITAN to offload Lean builds/checks when localhost is busy.

**Abhijit node budget (OVERVIEW §6.1, 15 GB):** 3–4 concurrent Opus agents (≈ ≤ 4 agents, ≥ 3 GB free, `latexmk` ≈ 0.5 GB),
because the general rule above (≥ 12 GB free, 2 GB per agent) would allow ≤ 1 agent there. Node-specific; the "5–8 Opus"
of the candidates file is not assumed. Lean only for occasional single-file checks.
