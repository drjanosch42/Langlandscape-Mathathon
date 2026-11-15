# Abhijit node: work batch 1 (DRAFT for the global master)

Author: abhijit-dispatch (Opus), 2026-11-14. Not committed; the global master reviews, commits and sends.
Sources read: `plan/implementation/{OVERVIEW.md (§1, §2, §4.3, §6, §6.1, §7), stage-03.md, stage-04.md, stage-05.md (§6 only),
stage-06.md, REPLAN-S02-06.md}` on `origin/wip-implementation` (= `origin/main` for these files, *verified* by `git diff`);
`agents/status/abhijit_candidates.md` (capacity there is outdated); `agents/roles/lean_build_node.md`;
`agents/rules/{messages,frozen,lean,mathematics}.md`; Abhijit's four archived messages in `agents/messages/fabian/archive/`;
`lean/Langlandscape/tools/{lfile.sh,deps.conf,deps_load.sh,load_profiles.conf,check_wp.sh}`; `master_log.md` (Abhijit lines).
Draft message: `agents/messages/abhijit/DRAFT_batch1.md`.

## 0. Facts used (and where they differ from the plans)
| item | value | source | plan text that is now stale |
|---|---|---|---|
| node | i5-1235U, 12 threads, 15 GB RAM, **≈ 4 GB free**, 107 GB disk | Abhijit 17:56Z | OVERVIEW §6.1 "16 GB RAM, no Lean" |
| agents | 3–4 Opus at once (cloud agents; local RAM limits TeX/PARI/Lean) | Abhijit 17:56Z | candidates file "5–8 Opus" |
| Lean | **built** Mathlib at pin `56a005855ea1…` (8643 oleans, v4.35.0) at `~/lean/Mathathon/gl2tf-data/mathlib4_v4350`; no GL2TF import is known to be built for our project | Abhijit 18:17Z | OVERVIEW §6.1 "no Lean"; stage-06 §1: CommAlg rows `remote = no` |
| TeX / PARI | TeX Live 2026 + biber 2.22; Python 3.10.12, cypari2 2.2.0, PARI 2.15.4 with `mf` | Abhijit 17:56Z | — |
| literature | Fabian transfers `literature/` out of band (log 18:50, Q2 resolved); Abhijit retrieved 8/9 missing items himself (HPS 1989 missing) | log 18:50, 19:35; Abhijit 18:26Z | — |
| push rights | Fabian: delegate implementation WPs of current/future stages; Abhijit may push `abhijit/<wp>` (results only) | team-lead brief, log 20:32 | OVERVIEW §6.1 O12c precondition (Q5) → now **met** |
| our wrappers on his node | **unusable**: `lfile.sh` needs MemAvailable ≥ 16 GB (≥ 8 GiB with profile `r2-16g`), `systemd-run --user`, and our `.lake/GL2TF` farm link | `tools/lfile.sh`, `deps_load.sh`, `load_profiles.conf` (*verified*) | — |
| `origin/wip-implementation` | `abf4cb0` at drafting time (moves with stage 02) | `git fetch` | brief said ≈ `1f6c9cc` |

Consequence: local Lean on his node is only possible as a **direct `lean` single-file draft check** (no `lake`, no wrapper),
which the rules do not cover yet (§5, rule edit R-A). All **acceptance** checks of Lean WPs stay on TITAN, in our rounds.

## 1. Batch 1 (four packages, one Opus agent each, all start at t = 0)
| # | package / WP ids | branch(es) | new files (only these) | inputs | local acceptance (his node) | our acceptance | agent-h (*estimate*) |
|---|---|---|---|---|---|---|---|
| P1 | **S06 CommAlg spine (early lane): S06-L1, S06-L2, S06-L3** | `abhijit/s06-l1` (off BASE); `abhijit/s06-l2`, `abhijit/s06-l3` each **off the head of `abhijit/s06-l1`** (stacking, OVERVIEW §1/§4.3) | `lean/Langlandscape/Langlandscape/CommAlg/Gorenstein.lean`, `lean/Langlandscape/LanglandscapeTests/S06/Gorenstein.lean` (L1); `…/CommAlg/LemmaS.lean` (L2); `…/CommAlg/NewOld.lean` (L3) | `stage-06.md` §0 (the `if:s06-lemD` block and the L1/L2/L3 signatures, **binding verbatim**), §1 rows L1–L3; tex `ss:s06-ca`, `lem:s06-S`, `lem:s06-D`, `def:s06-rings` | direct-`lean` draft check per file, rc 0, no `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` token (also not in comments), docstring rule (§3 of the message); `#print axioms` of each headline decl in a scratch file shows only `propext`, `Classical.choice`, `Quot.sound` | TCHK in our early-lane round `s06-int1-1` (L1, L2, L3 (a)) and `s06-int2-*` (L3 (b), (c)) on TITAN; WPA (AW-L1/L2/L3, opus) | 3–4.5 (local checks are slow: ≈ 1–3 min per file run) |
| P2 | **S06 chapter: S06-M1, M2, M3, M4, M7** (M8 optional) + per-stage files (XM0's job) | `abhijit/s06-math` | `mathematics/standalone-s06.tex`, `mathematics/chapters/s06.tex`, `mathematics/chapters/s06/NOTES.md`, `mathematics/chapters/s06/s06-m{1,2,3,4,7}.tex` (+ `s06-m8.tex`), `mathematics/bib/s06-m{1,2,3,4,7}.bib` (+ `s06-m8.bib`) | `plan/staged/stage-06-integral-defect.tex`; `stage-06.md` §0 (`if:s06-lemD`), §1 M rows, §6; merged `chapters/s01`, `chapters/s02` | `cd mathematics && latexmk -pdf -interaction=nonstopmode standalone-s06.tex` exit 0; no undefined refs/cites except labels of `s06-m5`, `s06-m6`, `s06-m11` (sibling rule) | TEXCHK re-run on our side; WP-level checks of each row; M9 Fable chapter audit later (local) | 4–5.5 |
| P3 | **S03 chapter: S03-M1, M3, M4, M5** + S03 maths drivers (taken from S03-X1) | `abhijit/s03-math` | `mathematics/standalone-s03.tex`, `mathematics/chapters/s03.tex`, `mathematics/chapters/s03/{1-graphs,3-ribet,4-ihara,5-amalgam}.tex`, `mathematics/bib/s03-m{1,3,4,5}.bib` | `plan/staged/stage-03-ribet-ihara.tex`; `stage-03.md` §0.2 (esp. §0.2.8 `Ψ*Ψ` normalisation), §1 M rows, §6; merged `chapters/s01`, **merged `chapters/s02`** (on BASE, *verified*: `s02/1-tree … 5-appendix-SA`) | `latexmk -pdf standalone-s03.tex` exit 0; no undefined refs/cites except labels of `2-eisenstein` (S03-M2, local E8 strand) | TEXCHK; M3/M4/M5 WP audits on our side (opus; Fable for M5) → findings back as a `request`, fixed by him on the same branch while unmerged | 3.5–4.5 (+ 0.5–1 for the planned fix rounds) |
| P4 | **S06-M6 second reader, q ≡ −1** (A-S06R), run **against the stage-tex proof** of `prop:s06-levM` | `abhijit/s06-m6` | `mathematics/litnotes/s06-m6-levM.md` | tex `prop:s06-levM` (5 steps, l. 269–296), `rem:s06-minus1`, `thm:s06-KO`; Kim–Ota (KO) §3, Thm 3.14; BKM, PW as cited there | verdict file present: CONFIRMED / GAP per checklist item (1) level `N⁺_{ρ,Σ⁺}N⁻` = `M`; (2) `P_ρ̄ ⊆ Σ`; (3) `U_ℓ`, `ℓ ∣ M`, vs anemic algebra; (4) Hensel distinctness mod `ϖ` — each with KO page/thm; plus steps (1)–(5) of the tex | read by the global master; feeds Fabian's decision 2 / Q-B, the local author of S06-M5 and S06-T3 | 1–1.5 |
Total ≈ 11.5–15.5 agent-h on 4 agents ⇒ **≈ 4–5 h wall** on his node. P4 finishes first; its slot then takes batch 2 (§7).

### Rationale
- **P1 saves the most wall time.** The S06 early lane is planned off-path (2.0 h, needs ≥ 1 stage lead, priority 3 on TITAN). During
  stage 02 TITAN is saturated (E1 pair + rounds fill all 3 slots, stage-06 §7 risk 5), so the lane slips toward the mixed scenario
  (+10–15 min on the S06 path) or scenario B (+24 min: 154 vs 130 min), and stage 05 has to stub `if:s06-lemD` longer. Drafting the
  spine L1→L2→L3 with local checks needs no TITAN slot and no local agent here; it should make the first round `s06-int1-1` mostly
  green (fewer than the planned R = 7 runs), and it delivers `if:s06-lemD` (the 05/06 seam) early. L1 is the root of every CommAlg WP
  (L2, L3, L5b, L8a stack on its draft), so its draft is pushed first (§4 of the message).
- **P2 and P3 save local capacity, not critical path.** The M tracks have slack (S03: 95 min against 171; S06: ≈ 50 min slack in
  scenario A), so remote maths shortens no path directly. What it buys: in stage 03 the four hard M WPs (opus, ≈ 63 agent-min plus
  fixes) and the S06 chapter (≈ 73 agent-min plus fixes) leave our node, whose budget is ≥ 12 GB + 2 GB per agent; those slots go to
  the Lean writers and the stage master's integration work. S03 is next; S06 is the largest chapter and holds the talk's punchline.
- **P4** settles the open q ≡ −1 step (Fabian decision 2) before stage 06 instead of inside its M path, by an independent account,
  which is the point of S06-M6. Running it against the stage tex (not M5's text) is a plan change (§6); the M5 author (local) then
  writes against a known verdict, and M9 checks that M5's step (4) matches it.
- **Why not stage 04 now.** Capacity (4 agents, 4 GB RAM). S04's maths uses `\texttt{if:…}` text and can run any time; its plan
  expects `bib/s04.bib` from S04-X1 (single writer). It is the first item of batch 2 (§7), with the package writing that bib itself.
- **Why not the other S06 early WPs (L6, L7, L14, L4, L13, L17, L10a).** One Lean slot on his node; L4/L13/L17 stack on L2/L3 and
  go to him in batch 2 once his L1/L2 drafts exist (same writer, no cross-node stacking delay). L6, L7, L14 are independent
  routine sonnet leaves; they stay with our early coordinator (or go to him in batch 2 if our node is busier).

## 2. Collision analysis (stage 02 running on `wip-implementation`, worktree `…-wt/impl`)
| path written by batch 1 | stage 02 touches it? | other writer in the plans | verdict |
|---|---|---|---|
| `mathematics/chapters/s03{.tex,/}`, `standalone-s03.tex`, `bib/s03-m{1,3,4,5}.bib` | no (S02 writes `chapters/s02/*`, done and merged) | S03-X1 would create the two drivers → **X1 must skip them** (§6); S03-M2 writes `s03/2-eisenstein.tex` + `bib/s03-m2.bib` (local) — the driver already guards and includes them; S03-M7 is the sole writer of `chapters/s03/NOTES.md` → P3 does **not** write NOTES.md (deviations go into its report) | none |
| `mathematics/chapters/s06{.tex,/}`, `standalone-s06.tex`, `bib/s06-m*.bib`, `chapters/s06/NOTES.md` | no | S06-XM0 would create the three per-stage files → **XM0 not run locally** (already the plan's rule for a remote package, stage-06 §6); local M5/M11 write `s06-m5.tex`, `bib/s06-m5.bib`, `bib/s06-m11.bib` (driver guards them) | none |
| `mathematics/bib/` (new directory) | no (`standalone-s02.tex` guards `bib/s02-m*.bib`, which do not exist at BASE) | — | none |
| `mathematics/litnotes/s06-m6-levM.md` | no (`litnotes/` holds `s02-*.md` only) | none | none |
| `lean/Langlandscape/Langlandscape/CommAlg/{Gorenstein,LemmaS,NewOld}.lean`, `LanglandscapeTests/S06/Gorenstein.lean` | no (S02 writes `Tree/`, `Graph/`, `Hyp/`, `Brandt/`, tests `S02/`) | S06-L1 is the **sole owner** of `Gorenstein.lean`; S05-L6F would need stage 06's written OK (stage-06 §7 Q1) | none |
| aggregator files (`main.tex`, `references.bib`, root Lean imports, `PrintAxioms.lean`, `SORRIES.md`, `HYPOTHESES.md`) | yes (stage master) | stage masters only | **not touched** by batch 1; lines come back in the reports |
| `plan/`, `agents/` (except his outbox `agents/messages/fabian/`) | yes | — | not touched |
Semantic coupling (not file collisions): (a) S03 and S06 final plan passes before launch may change a row → we send an `info`, he
merges `origin/wip-implementation` into the open branch (merge, no force-push). (b) The stage-06 §0 block is frozen (a change needs
the stage-05 master's written OK); if L1–L3 cannot be proved at those signatures, he stops and asks (`question`), never changes them.
(c) `if:s02-*` labels: stage 02's maths is merged and audited (S02-M7a, `955d5b4`); a later S02 fix would come as an `info`.

## 3. Merge plan on our side
1. Global master polls `agents/messages/fabian/`, fetches `origin/abhijit/*`, checks `git diff --name-only <BASE>...origin/abhijit/<b>`
   equals the package's file list (and `grep -c '\.titan/'` = 0), re-runs the acceptance (latexmk; for P1 nothing locally).
2. **P1 (Lean).** The S06 early lane starts now (global master's OK, REPLAN §8: "by stage 03"; this brings it forward into stage 02 —
   it uses TITAN at priority 3 only, so it never pre-empts S02). S06-X0 (local early coordinator) creates `impl/s06-early` off
   `wip-implementation` and worktrees only for the local early WPs; it merges `origin/abhijit/s06-l1` (then `-l2`, `-l3`) into
   `impl/s06-int1` for `s06-int1-1` (spec lines as stage-06 §3.1, unchanged). Errors and goal states go back to Abhijit as one `request`
   per round (not a strand, so fix hints are allowed); he pushes new commits on the same branches. After green + AW-L1/L2/L3: merge
   `--no-ff` into `impl/s06-early`. The hand-over merge into `wip-implementation` stays as planned (global master, at a stage boundary,
   at the latest before S05-X1, after L18 PASS). Local early writers that stack on L1/L2 (L4, L13, L17, L5b, L10a) branch from the
   fetched `origin/abhijit/s06-l1`/`-l2` heads, or wait for batch 2 (§7).
3. **P3 (S03 maths).** Held until stage 03 launches. S03-X1 step 1 (after the re-sync) merges `origin/abhijit/s03-math` `--no-ff` into
   `wip-implementation` (new files only; driver from the package) and skips its own maths stubs. If the package is not delivered at
   S03-X1, X1 creates the drivers as planned and the undelivered WPs run locally with the fallback models (stage-03 §6); a late
   delivery is then merged without its two driver files. WP audits (M3/M4 opus, M5 Fable) run locally on the merged sections; fixes
   go to Abhijit only if the branch is unmerged, else they are a local fix WP. **S03-M7 becomes local (opus)** (M4/M5 remote ⇒
   independence requires our node); M8 (Fable), M9 local as planned; M9 applies `main.tex` `\input{chapters/s03}` and moves the
   `bib/s03-*.bib` entries into `references.bib`.
4. **P2 (S06 maths) and P4.** New files in idle stage directories: the global master merges them into `wip-implementation` at the
   next stage boundary (02→03), after the TEXCHK re-run, without aggregator lines (those come at S06-M10). P4's verdict file goes in
   with P2 or alone. M5 (local, opus) is written after P4's verdict; M9 (Fable) and M10 in stage 06 as planned.
5. Every merge: commit message names the WP ids and `abhijit/<branch>@<sha>`; the stage's `runs/sNN.md` records "delivered remotely".

## 4. Stage-plan updates needed (on `wip-plan`, global master / re-planning master)
| file | change |
|---|---|
| `OVERVIEW.md` §6.1 | node facts (15 GB, ≈ 4 GB free, built Mathlib at the pin, 3–4 Opus); O12c preconditions met (Q5 approved 20:32, Q2 out of band 18:50); **new eligible class: Mathlib-only Lean WPs** (GL2TF-free files, no `Hyp`/aggregator edits) with a local direct-`lean` *draft* check and acceptance only in our TITAN round; stacked remote branches `abhijit/<wp>` off another `abhijit/<wp>` head allowed; one Lean check at a time on his node |
| `OVERVIEW.md` §2 | row `abhijit/<wp>`: base may be the head of an upstream `abhijit/<wp>` (stacking); the early coordinator (not only the stage master) merges remote S06 early-lane drafts into `impl/s06-int<k>` |
| `stage-06.md` §1, §6 | L1, L2, L3: `remote = yes` (`abhijit/s06-l1/-l2/-l3`, fallback opus (+pf)); X0: no worktrees for remote WPs, merge the fetched heads into `impl/s06-int1`; M1–M4, M7 (+M8) assigned `abhijit/s06-math` (XM0 not run); **M5 local** (opus +pf) because M6 is remote; **M6 input = stage-tex `prop:s06-levM`** (dep M5 removed), M9 gets the item "M5 step (4) agrees with the M6 verdict"; §2 DAG edge `M5->M6` dropped, edge `M6->M5` (verdict before M5 is written) added |
| `stage-03.md` §1, §6 | M1, M3, M4, M5 assigned `abhijit/s03-math` at BASE (base condition "after X1" replaced: the package writes the two drivers; the merged-s02 condition holds at BASE); **X1: skip `chapters/s03.tex` and `standalone-s03.tex`, merge the package instead** (X1 acceptance `latexmk standalone-s03.tex` then runs on the merged driver); **M7 local (opus)**; package deviations are delivered in the report and become M7 input (M7 stays sole writer of `NOTES.md`); waves: M1–M5 drop out of W1 except M2 |
| `stage-03.md` / `REPLAN-S02-06.md` §9 | record that Q-H's "no S03 early start" concerns local worktrees and TITAN slots; remote maths before S03-X1 uses neither and is covered by Fabian's 20:32 delegation (global master confirms) |
| `stage-04.md` §6 | (batch 2) `abhijit/s04-math` writes `bib/s04.bib`, `chapters/s04.tex`, `standalone-s04.tex` itself; S04-X1 skips them |
| `REPLAN-S02-06.md` §2 | S06 "early-startable" now started in stage 02; remote-eligible column += S06-L1, L2, L3 |
| `agents/rules/resources.md` | (F18) node row "abhijit": 15 GB, ≥ 4 GB free before a Lean check, 3–4 agents, one heavy job (latexmk or lean) at a time |

## 5. Rule edits needed on `main` before the message is sent (global master)
- **R-A (needed for P1's local check).** `agents/rules/lean.md` (after "Build only through the wrappers…") and `agents/rules/frozen.md`
  (after "Build only through the provided wrapper scripts…"), one line each: *"Exception, node `abhijit` only (global master
  2026-11-14): a draft check of a Mathlib-only file (imports `Mathlib.*` and the WP's own `Langlandscape.CommAlg.*` files only) by a
  direct `lean` call with `LEAN_PATH` into the frozen Mathlib's `.lake/build/lib/lean` trees, outputs (`-o`) only into a scratch
  directory outside the repo and outside the frozen tree, under a memory cap, followed by a `find <frozen tree> -newer <marker>`
  check. Never `lake`; never a wrapper of `lean/Langlandscape/` there. This is not an acceptance check; acceptance is the TITAN
  round."* Without R-A: delete section **L-CHECK** from the message; P1 then drafts without local checks (all checks in our TITAN
  rounds, ≈ 2 more runs per WP) — still worthwhile but slower.
- F18 node row in `resources.md` (above).

## 6. Risks
1. **R-A not approved / direct `lean` fails on his node** (no `systemd-run --user`, OOM under the cap, missing package oleans):
   P1 falls back to TITAN-only checks; the first step of P1 is a trivial-file smoke check that reports rc, wall, peak RSS.
2. **RAM (≈ 4 GB free)**: one Lean check (≈ 2–3.5 GB) plus two `latexmk` runs can exceed it. Mitigation in the message: every
   `latexmk` and `lean` run goes through one node-wide `flock` (one heavy job at a time) and waits for MemAvailable ≥ 4 GB.
3. **Signature drift in P1**: the §0 block is binding (stage 05 copies it). Any needed change is a `question` to us, never a silent edit.
4. **Driver ownership** (S03-X1, S06-XM0) moves to the packages: if a stage launches before delivery, the stage master must not
   create the drivers twice (merge procedure §3.3).
5. **Plan final passes** of stages 03/06 may change M rows after batch 1 starts: `info` + merge of `origin/wip-implementation`.
6. **Independence bookkeeping**: P3 makes S03-M7 local, P4 makes S06-M5 local; both must be reflected in the plans (§4) before
   the stages launch.
7. **Literature**: the files each package needs must be on his node (out-of-band transfer, log 18:50). The message asks him to list
   missing files in his `ack`; HPS 1989 is not needed by batch 1.
8. **Stale BASE**: `wip-implementation` moves with stage 02; batch 1 needs only s01/s02 maths and the plan text, so any sha after
   `955d5b4` (S02-M7a) is fine; the global master pins `<BASE_SHA>` when sending (currently `abf4cb0`).

## 7. Batch 2 (as slots free; one `request` per batch)
1. `abhijit/s04-math`: S04-M1, M2, M3, M4, M6 (+M7) incl. `bib/s04.bib` and the two drivers (S04-X1 skips them); then S04-M8 locally.
2. Stacked on his P1 drafts: S06-L13 (`CommAlg/BaseChange.lean`), S06-L17 (`CommAlg/EtaPrinciple.lean`), S06-L4 (`CommAlg/ThmE.lean`).
3. Literature WPs: S03-M6 (`litnotes/s03.md`), S06-M11, S04-M5 (library access).
4. PARI (only if our node's CPU is short): S06-C1–C4, S05-C1/C2 as in `abhijit_candidates.md` #8/#9 (needs a plan change: stage-06 §7
   Q4 currently keeps code local).

## 8. Batch 3 (global master 2026-11-14, sent as `agents/messages/abhijit/20261114-205143Z_fabian_batch3.md`)
BASE `origin/main` 3806166. Four packages, one Opus agent each; audit feedback (S03-M3 blind Opus W=7, S03-M5 Fable W=9, `rem:s03-T6(c)` wrong
at a level maximal at p, `prop:s03-phi` needs E ≠ ∅) ⇒ mandatory self-audit section (proof steps, level hypotheses, edge cases, `\lit` pages).
| # | WPs | branch(es) | files (new) | merge on our side |
|---|---|---|---|---|
| B1 | S05-M1, M3, M4, M7 + drivers + per-WP bibs | `abhijit/s05-math` | `standalone-s05.tex`, `chapters/s05.tex`, `chapters/s05/{sign,hypX,subquot,simplicial}.tex`, `bib/s05-m{1,3,4,7}.bib` | S05-X1 skips drivers/bibs, merges the branch `--no-ff` |
| B2 | S05-M2, M5, M6; then S05-R1 (independent of B1's agent) | `abhijit/s05-lit` (on B1's driver commit), `abhijit/s05-r1` (on B1 head after M1+M3) | `chapters/s05/{higherweight,geometric,status}.tex`, `bib/s05-m{2,5}.bib`, `litnotes/s05-gamma1.md`; `chapters/s05/NOTES.md` | X1 merges after s05-math; R1 verdict feeds M8 |
| B3 | S06-L5a, L10a (Mathlib-only) | `abhijit/s06-l5a`, `-l10a` off `s06-l4` 4ac6651 | `CommAlg/DVR.lean`, `LanglandscapeTests/S06/Toy.lean` | TITAN `int3*`; L5a statement via `info` first (consumer L9b) |
| B4 | S06-L7, L6, L14 (+ stretch L6b) | one branch each off `s06-l1` 8c0916b (L6b on `s06-l6`) | `CommAlg/{Squeeze,TraceForm,TwoByTwo,Burnside}.lean` | TITAN early/in-stage round |
Kept local: S06-L5b (strand E1′), L8a–L10b, L6c, S06-M5, all S05 Lean/C/T, S05-M8/M9. E8′ (S05-M3) not triggered (E8 decided: opus).
Plan marks: `stage-05.md` (X1 row, track M, §6), `stage-06.md` (X0 row, track L, §6). Expected ≈ 12–17 agent-h ⇒ ≈ 3.5–4.5 h wall.

## 9. Batch 4 (global master 2026-11-14, sent as `agents/messages/abhijit/20261114-210238Z_fabian_batch4.md`)
BASE `origin/main` 864d104 (s03 read-only from `origin/wip-implementation` c87b44a). Runs **in parallel with batch 3** (quota ample: 28 % of a
5-h window); he may raise to 5–6 agents, heavy jobs (`latexmk`, `lean`) serialized by his lock. Common rules by reference to batch 3 §0/§1/§4.
| # | WPs | branch(es) | files (new) | merge on our side |
|---|---|---|---|---|
| C1 | S04-L7, S04-L13a (Mathlib-only, deps X1 only; opus) | `abhijit/s04-l7`, `abhijit/s04-l13a` off 864d104 | `Ordinary/{GroupRing,InvLimit}.lean` + `LanglandscapeTests/S04/{GroupRing,InvLimit}.lean` | S04-X1 makes no worktrees for them, merges the heads into `impl/s04-int1`; statements via `info` first |
| C2 | cross-account review of the s03 chapter (fresh agent, blind; Fable/Opus) | `abhijit/xr-s03` | `mathematics/audits/2026-11-14_s03-xacct.md` | report-only; findings triaged by the stage-3 master before closure |
| C3 | cross-account review of s01 | `abhijit/xr-s01` | `mathematics/audits/2026-11-14_s01-xacct.md` | report-only; fixes as a local fix WP |
| C4 | cross-account review of s02 | `abhijit/xr-s02` | `mathematics/audits/2026-11-14_s02-xacct.md` | report-only; fixes as a local fix WP |
| C5 | literature: Ihara 1975, SGA 7 IX locators, remaining MISSING_LITERATURE items, "present but listed missing" refresh | `abhijit/lit-b4` | `mathematics/litnotes/lit-b4.md` (PDFs out of band) | update `literature/MISSING_LITERATURE.md` locally |
Review finding format: `X<n> | crit/maj/min/note | file:line + \label | category | finding | evidence | fix`, verdict + W line, blind first, then
NEW/KNOWN/KNOWN-BUT-UNFIXED comparison with our audits. Skipped: `plan/hacs/` review (not on `origin/wip-plan` yet). Plan marks: `stage-04.md`
rows L7, L13a + §6; `REPLAN-S02-06.md` §2. Expected ≈ 10–14 agent-h.

## 10. Batch 5 (global master 2026-11-14, sent as `agents/messages/abhijit/20261114-213920Z_fabian_batch5.md`)
BASE `origin/main` 0e24ba5. New Lean files are **Apache-2.0** (licensing.md). Stage 4 runs locally; nothing in batch 5 touches it.
| # | WPs | branch(es) | files | merge on our side |
|---|---|---|---|---|
| D1 | S05-L6 `prop:s05-subquot` (Mathlib + CommAlg; Lemma D merged = §0 state 1) | `abhijit/s05-l6` (0e24ba5 + merge `abhijit/s06-l3` 212d944) | `CommAlg/SubQuot.lean` | S05-X1: no worktree; merge into `impl/s05-int1`; statements via `info` first |
| D2 | S05-L8 algebraic half `xiso_of_gorenstein` (optional/ext) | `abhijit/s05-l8` (on `s05-l6`) | `Comparison/XIso.lean` | `impl/s05-int2b`; the `Hyp.X.iso` line is appended locally after S05-L2 |
| D3 | S05 chapter closure attempt of B1's five open items (sign (d) Picard `U_p = N_{U_p}`, FD1 rows 2–3, AL (R1)/(R2) at Γ_s, Xlambda (c),(d), Rosati/SGA7 IX 2.4/9.1.2/10.4) + independent R1 re-read | new commits on `abhijit/s05-math` (from 2a96294) and `abhijit/s05-r1` (from 681d721) | `chapters/s05/*`, `bib/s05-*.bib`; NOTES.md section "Batch 5 re-read" | S05-X1 merges both as planned; M8 Fable audit afterwards |
| D4 | literature stages 5–6: Picard `U_p` vs pullbacks reference, Buzzard 1997, Takahashi 2001, DDT97 Lemma 4.17, Hida 1988 OCR copy, pending manual downloads | `abhijit/lit-b5` | `mathematics/litnotes/lit-b5.md` (PDFs out of band) | merges with the next chapter batch; local MISSING_LITERATURE update |
Skipped: (d) review of our stage-04 chapter parts (none exist yet); no other S05/S06 Lean WP is Mathlib-only; PARI T05-2 stays local.
Plan marks: `stage-05.md` rows L6, L8 + §6; `REPLAN-S02-06.md` §2. Expected ≈ 8–11 agent-h.

## 11. Batch 6 (global master 2026-11-14, sent as `agents/messages/abhijit/20261114-224725Z_fabian_batch6.md`)
BASE `origin/main` 7b4b3d7; s04 read-only from `origin/wip-implementation` 47c2984 (M9 audit + M10a fixes merged). No Lean.
| # | WPs | branch(es) | files (new / commits) | merge on our side |
|---|---|---|---|---|
| E1 | blind cross-account review of the s04 chapter (fresh agent, no batch-2 context; C2–C4 format, Comparison vs M9/M8) | `abhijit/xr-s04` | `mathematics/audits/2026-11-14_s04-xacct.md` | report-only; findings triaged by the stage-4 master (fix WP after M10a) |
| E2 | literature: Eichler 1973 / Kneser 1966 in-volume pages; Atkin–Li 1978 and Hida 1986a pages for E3; Buzzard 1997, Takahashi 2001, Gelbart 1975, Kurihara 1979 | `abhijit/lit-b6` | `mathematics/litnotes/lit-b6.md` (PDFs out of band) | with the next chapter batch; local MISSING_LITERATURE update |
| E3 | S05 second closure attempt: (R1) at Γ_s on X_q(J_s), Xlambda (c) (i)–(iii), Xlambda (d) rewritten list (i)–(iii); separate re-reader, ≤ 1 fix round | new commits on `abhijit/s05-math` (from cd6d3c7) and `abhijit/s05-r1` (from f5099cc) | `chapters/s05/*`, `bib/s05-*.bib`; NOTES.md "Batch 6 re-read" | S05-X1 merges both; M8 Fable audit afterwards |
No plan rows changed (all three are review/maths/literature on existing remote packages). Expected ≈ 7–9 agent-h.

## 12. Batch 7 (global master 2026-11-15, sent as `agents/messages/abhijit/20261115-004745Z_fabian_batch7.md`)
BASE `origin/main` 1ce44ea; s05 read-only from `origin/wip-implementation` 7d67852 (stage 5 final gate PASS). 3 agents (RAM), no Lean; deadline ≈ 18 h.
| # | WPs | branch | files (new) | merge on our side |
|---|---|---|---|---|
| F1 | blind cross-account review of the s05 chapter, focus on our M10 (c2 `\stconj` + `rem:s05-c2open`, `lem:s05-normtwist`, FD1/FD2 marks), M9a–c fixes, L11a Lean marks; fresh agent | `abhijit/xr-s05` | `mathematics/audits/2026-11-15_s05-xacct.md` | report-only (≤ 2 h); stage-5 closure may take a fix WP |
| F2 | S06-M5 second reader (q ≡ −1), cross-account, **triggered** by our `info` with the local M5 sha; reads KO/PW first, P4 litnote only afterwards | `abhijit/s06-m5-r2` | `mathematics/litnotes/s06-m5-second-reader.md` | feeds S06-M9 / T3; "not triggered" after 3 h |
| F4 | independent PARI cross-checks: T4 (S06-C3: p = 17, k ∈ {12,28,44,60,124}, q = 3) and H3 (S06-C7: q ≡ −1 triples); definitions `info` first | `abhijit/xcheck-s06` | `code/cas/s06-xcheck/*`, `code/results/s06-xcheck/{T4_hecke,H3}.json` | compared with local C3/C7; a non-zero H3 difference is a finding |
F3 skipped: no unassigned Mathlib-only S06 Lean WP remains. No plan rows changed (review, second reader and cross-check only; the C rows stay local).
