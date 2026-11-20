<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Langlandscape

Team **Langlandscape** (Abhijit A J and Fabian Januszewski) at the Caltech × SAIR Mathathon 2026, topic: the
**Jacquet–Langlands correspondence**. The repository contains the mathematical development (LaTeX), a Lean 4
formalization, computations (Python / PARI / HACS) and the talk. Release notes of the submission:
[`RELEASE-NOTES.md`](RELEASE-NOTES.md).

**Public repository and provenance.** This public repository (https://github.com/drjanosch42/Langlandscape-Mathathon) contains the final
tree as a single commit, plus one commit that inserts that commit's hash into the report. Commit hashes and branch names cited in this
repository refer to the team's development repository, which is kept private because its history contains unfiltered session logs;
they are cited for provenance. The Lean code here is identical to the gated tree `c70ef3a9` except for Markdown files; the final Lean gate can be checked from its logs in [`supplementary/gate-logs/bsf-gate-1/`](supplementary/gate-logs/bsf-gate-1/) and by rebuilding the public tree.

## For reviewers: where to start

| file | what it is |
|---|---|
| [`mathematics/submission/report.pdf`](mathematics/submission/report.pdf) | **the submission report** (201 pp; single self-contained source `report.tex`): abstract, results with statuses, Lean, HACS, agentic setup, AI use, provenance |
| [`talk/main.pdf`](talk/main.pdf) | the slides (15 main frames + backup frames) |
| [`mathematics/article.pdf`](mathematics/article.pdf) | the mathematics as an article, with "Main results" answering (a)–(e) |
| [`mathematics/main.pdf`](mathematics/main.pdf) | the full mathematical development: introduction s00 and stages s01–s06 (198 pp) |
| [`BUILDING-LEAN.md`](BUILDING-LEAN.md) | how to build and check the Lean project (`lean/Langlandscape/`) |
| [`lean/Langlandscape/HYPOTHESES.md`](lean/Langlandscape/HYPOTHESES.md) | registry of the registered Lean hypotheses (status, consumers, discharges) |
| [`mathematics/report/standalone-hypotheses.pdf`](mathematics/report/standalone-hypotheses.pdf) | every registered hypothesis explained (21 pp) |
| [`supplementary/gate-logs/bsf-gate-1/`](supplementary/gate-logs/bsf-gate-1/) | logs of the final Lean gate (from scratch, PrintAxioms 955/955 standard) |
| [`code/results/INDEX.md`](code/results/INDEX.md), [`code/hacs/`](code/hacs/) | computed results with provenance; the HACS snapshot and our JL module |
| [`docs/agentic-process/agentic-process.html`](docs/agentic-process/agentic-process.html) | the agentic process (architecture, workflow, timeline, HACS, model study, lessons, metrics); Markdown sources in the same folder |
| [`RELEASE-NOTES.md`](RELEASE-NOTES.md) | release notes of the submission |

Status words used throughout (as in `CLAUDE.md`): *proved* / *formalized* / *computed* / *conjectural* / *cited*.
*Formalized modulo H* means: compiles with the registered hypotheses H as explicit arguments.

## Repository overview

| path | content |
|---|---|
| `mathematics/` | mathematical development (LaTeX) |
| `mathematics/main.pdf` | the introduction s00 and chapters s01-s06, 198 pages (`mathematics/main.tex`, `mathematics/chapters/`) |
| `mathematics/final-report/` | final project report (`final-report.pdf`, 58 pp, an earlier project report: results with statuses, Lean summary, computations, the Hsieh sign, open items; appendix: hypotheses report) |
| `mathematics/report/` | report on the registered Lean hypotheses (`standalone-hypotheses.pdf`) |
| `mathematics/notes/hsieh-sign.pdf` | technical note on a sign in the literature, see below (4 pp) |
| `lean/Langlandscape/` | our Lean 4 project (library, tests, `Audit/PrintAxioms.lean`, `HYPOTHESES.md`, `SORRIES.md`, audits) |
| `lean/trace-formula-project-import/` | curated fork of the GL(2)/Q + quaternion-algebra material of our GL(2) trace formula project (LaTeX, Lean, back-translation); the Lean part is a path dependency of `lean/Langlandscape/` |
| `code/python/` | Python package `langlandscape` and its tests (`code/python/tests/`) |
| `code/cas/` | PARI/other CAS cross-check scripts (`s06-xcheck/`) |
| `code/results/` | computed results with provenance; `code/results/INDEX.md` lists script, commit and parameters per result |
| `code/hacs/` | HACS 0.2.1 snapshot and the Jacquet–Langlands transfer extension (`code/hacs/jl/`); a separate software project (technical sense), see below |
| `talk/` | slides; `talk/main.pdf` (25 pp: 15 main + 10 backup frames) |
| `summary/` | colour-coded six-stage plan/status overview (`six_stage_plan.{tex,pdf,html}`) |
| `docs/agentic-process/` | write-up of the agentic process by which the project was run |
| `plan/` | implementation planning, per-stage runs, milestone closures (`plan/implementation/outbox/`), HACS plans (`plan/hacs/`) |
| `agents/` | role prompts, rules per directory and procedure, cross-node message inboxes |
| `literature/` | git-ignored, never committed (not part of the repository) |

## Results in brief

Six stages, each closed by a milestone record in `plan/implementation/outbox/*milestone-closure-s0N.md`
(statuses below are those of the closures; nothing is upgraded here).

| stage | topic | Lean final gate (all declarations standard axioms) | status |
|---|---|---|---|
| s01 | quaternionic foundations | 161 axiom lines | *formalized* (L15 audit PASS WITH REMARKS); 17 results marked formalized, numerics *computed* |
| s02 | tree quotients, Brandt graph | 195/195 | *formalized* (Hyp.SA, HS, BTtree, SerreCoh, SerreFree, RamNrdSurj are explicit arguments; RamNrdSurj discharged after s06 by `Hyp.ramNrdSurj_holds`); numerics *computed* (240 validation cases) |
| s03 | weighted graphs, Ribet sequence, Ihara lemma | green (from scratch) | Ribet sequence and Ihara (i), (ii) *formalized*, Ihara (iii) only as statement layer; new hypotheses EllipticCount, BrandtStabFree, IharaH0 registered |
| s04 | ordinary projector, Hida control, Lambda-adic Ribet sequence | 592/592 | Hyp.PadicOrdDecomp discharged; HidaControl (schematic), HsiehCR, MordLambdaFree, InvLimExact open |
| s05 | comparison hypothesis Hyp.X, dictionary, sub/quotient | 747/747 | Hyp.X (X1-X4) registered, **open**, never called known; `prop:s05-Xlambda(c2)` open; non-vacuity instances only |
| s06 | integral defect | **836/836** | `Defect.defect_formula` is *formalized modulo the registered `Hyp.*`, including the Galois half (`Hyp.FreeRankTwo`)*; it is **not** an unconditional theorem |

**Final Lean gate** (after the merge of the `Hyp.BrandtStabFree` discharge: Lean tree `c70ef3a9`; TITAN bsf-gate-1 from scratch
in an unseeded worktree, `Langlandscape` + `LanglandscapeTests` rc 0, 4205 jobs, VendorStacks rc 0, 1955 jobs; logs `fa755069`; it
supersedes the submission-bundle gate at `28d2b091` (gate commit `dc61af50`, subl-gate-1, 950/950; CONCEPTD subl-gate-1x, PASS), the
gate at `2323a252`, ramnrd-final-2, 840/840, and the s06 gate at `44058153`, 836/836): **955/955** declarations of
`Audit/PrintAxioms.lean` use only `propext`, `Classical.choice`, `Quot.sound` (929 the full triple, 23 a proper subset, 3 none;
the 5 new rows are full triples); forbidden-token grep empty; `check_frozen` clean; the only `sorry` in the whole tree is the
one in the frozen import (`Instances.lean:1815`); **29 registered hypotheses** (28 `Langlandscape.Hyp.*` rows in
`lean/Langlandscape/HYPOTHESES.md` plus the reused `GL2TF.Hyp.EichlerMass`), all open unless stated in their row:
**3 discharged** (`PadicOrdDecomp`; `RamNrdSurj` by `Hyp.ramNrdSurj_holds`, *formalized*; `BrandtStabFree` by `Hyp.brandtStabFree_holds`, *formalized*), `ResidualBurnside` conditionally
discharged by `Hyp.residualBurnside_of_absIrred`. Toy instances show consistency (non-vacuity) only; apart from
`RamNrdSurj`, no Lean term discharges a cited hypothesis (`BrandtStabFree` is proved in the chapter, not cited). The bundle added 110 audit rows (102 of the 104 chapter-cited
declarations that were not yet audited; the 2 test-library ones `LanglandscapeTests.S04.Hyp.hsiehCR_toy` and
`LanglandscapeTests.Hyp.S05.toyTate_gal_uncond` stay outside the audit) and `Langlandscape/Uncond.lean` (8 `_uncond` twins of the
`RamNrdSurj` consumers; with the 18 `PadicOrdDecomp` twins of `Ordinary/TowerUncond.lean` these are free of registered
hypotheses, under the stated explicit hypotheses). Build instructions for a fresh clone: [`BUILDING-LEAN.md`](BUILDING-LEAN.md).

The discharge of Hyp.RamNrdSurj was drafted by an external model (mistral-large-4-0 via opencode), run by Fabian Januszewski on Abhijit A J's machine, outside our agent process (where opencode is Q&A-only); it was integrated into the library, independently audited (Fable, PASS WITH REMARKS) and gated from scratch by the Langlandscape agents.
The discharge of Hyp.BrandtStabFree was drafted by an external model (mistral-large-4-0 via opencode) on Abhijit A J's machine, outside our agent process; it was integrated into the library, independently audited (Fable, PASS) and gated by the Langlandscape agents.

Mathematical status for s06 (chapter s06): Theorem E (i)-(iv) *proved*; the defect theorem *proved modulo cited results*
(Hida control, Hsieh, Kim-Ota) and the registered hypotheses; for q ≡ −1 the case M = 1 is *proved modulo cited*, and
N(rhobar) > 1 is **open**. Full lists of open items: closures of s01-s06 and `RELEASE-NOTES.md`.

**HACS (computed).** Lane A (`plan/hacs/outbox/20261115T0137Z_laneA-closure.md`): definite-side Hecke and
Gorenstein checks, Mazur's prime 5, Betti-side congruence module (Z/17)^2 at k = 12, 28, 44, 60. Lane B (closure FINAL, `plan/hacs/outbox/20261115T0150Z_laneB-closure.md`, branch `impl/hacs-laneB`):
Brandt lattices through HACS's integral engine and exact congruence modules. The Eisenstein congruence module is Z/num((q-1)/12)
for every prime q <= 600 at l >= 5 (109/109 levels, HACS ReadLocal) and exactly, 2- and 3-parts included, for the first 80 primes, q <= 409
(80/80, exact Z route; the run was capped by a 15-min limit, so this coverage is partial); beyond Mazur (k > 2) the only nontrivial lattice congruence module is |C| = 37 at D = 13, k = 8 (non-canonical
lattice). Native build about 10^3 times faster than Python (class set and T_2 for q = 997: 0.02 s vs 64.7 s). Eight deviations D1-D8 are
disclosed in the closure (e.g. targeted validation only; a full HACS validation row is due after the merge).

## Building

### Lean (frozen toolchain)

The Lean toolchain `leanprover/lean4:v4.35.0` and the matching Mathlib are **frozen** (`agents/rules/frozen.md`):
`lake update`, `lake clean`, `lake exe cache get` and any change to `lean-toolchain` / `lake-manifest.json` are forbidden
for the team's agents, and we build only through wrapper scripts which enforce locks, memory caps and frozen-tree checks.

For an external user: install elan with toolchain `v4.35.0` and use Mathlib at the revision pinned in
`lean/Langlandscape/lake-manifest.json` (`56a005855ea17e0b0958f73ec801ae140b0a1679`; the manifest is generated and lists
the other pinned packages). `lean/Langlandscape/` depends on the in-repo import `lean/trace-formula-project-import/lean`
(package `GL2TF`) as the path dependency `../trace-formula-project-import/lean`, so a fresh clone builds with
`cd lean/Langlandscape && lake exe cache get && lake build` (see `BUILDING-LEAN.md`). This was tested in a clean room
(TITAN, job subl-clean-1, `56f3f0fc`): a fresh clone of the gate commit `dc61af50` in an empty directory built with
`lake exe cache get` + `lake build` (library 224 s, imported GL(2) project 96 s, tests and vendored files 70 s), and
`Audit/PrintAxioms.lean` printed all 950 axiom lines within the standard triple; lakefile and manifest stayed unchanged.
On a team node the dependency farm is linked, from `lean/Langlandscape/`:

```
tools/link_deps.sh && tools/link_deps.sh --verify    # once per fresh worktree
tools/check_frozen.sh                                # dry check of all dependency modules
tools/lbuild.sh Langlandscape LanglandscapeTests     # library + tests (allowed targets: Langlandscape, LanglandscapeTests,
                                                     #   LanglandscapeVendorStacks, +<Module>)
tools/lbuild.sh LanglandscapeVendorStacks            # vendored AxiomMath/Stacks modules
tools/lfile.sh <file.lean>                           # single-file check
```

Node-specific paths are in the git-ignored `tools/deps.local.conf` (`tools/deps.conf` contains the paths of one node and is
not edited). Details: `lean/Langlandscape/README.md`, `agents/rules/lean.md`. The import has its own wrappers in
`lean/trace-formula-project-import/tools/` (`lbuild.sh`, `lfile.sh`, `check_frozen.sh`, `link_deps.sh`). The gate
(from scratch: 4194 jobs, about 5 min, about 4.5 GB) is: build, `Audit/PrintAxioms.lean`, forbidden-token grep, `sorry` count,
`check_frozen`, `check_wp`.

### LaTeX

```
cd mathematics && latexmk -pdf main.tex                       # main.pdf
cd mathematics/report && latexmk -pdf standalone-hypotheses.tex
cd mathematics/notes && latexmk -pdf hsieh-sign.tex
cd mathematics/final-report && latexmk -pdf final-report.tex   # final-report.pdf; the appendix includes ../report/standalone-hypotheses.pdf
cd talk && latexmk -pdf main.tex
```

Needs a TeX Live with biblatex/biber. The committed PDFs are the milestone builds.

### HACS

`code/hacs/` is a **separate software project** (separate in the technical sense — its own build, licence and release — not a separate entry in the Mathathon) with its own `README.md`, `BUILDING.md` and CMake presets (C++ / AVX-512 / CUDA;
a CPU-only configuration exists). Its `lean/` directory is a separate Lean project on `v4.33.0` with its own pin.
It is HACS v0.2.1 plus our clearly marked JL module and three documented hook lines (the `CMakeLists.txt` include and the `RegisterJL` declaration and call; see `plan/hacs/outbox/20261115T0150Z_laneB-closure.md`), plus regenerated CLI manual tables (`code/hacs/CHANGES.md`).

## Reproducing the computations

- **Python:** `cd code/python && pip install -e . && pytest` (Python >= 3.10; tests in `code/python/tests/`; some tests use PARI (cypari2); the 3 skipped
  cases are the p | D cases of s01). At the final state the closures report 483 passed, 3 skipped for the full suite
  (the Lane A count; at s05: 419 passed, 3 skipped). Modules: `langlandscape.{classset,levels,brandt,tree,ribet,ordinary,comparison,defect,hacs_bridge}`.
- **CAS:** `code/cas/s06-xcheck/` (PARI/GP scripts, `run.py`; see its `README.md`) independent cross-check of the T4 Hecke side
  and H3.
- **Results:** `code/results/s0N/*.json`; `code/results/INDEX.md` records for each result file the work package, content,
  script, and (in the JSON) the commit and parameters. The JSON records also carry their own provenance. Some records carry a `-dirty` commit suffix.
- **HACS runs** need the HACS binary (built from `code/hacs/`, see `code/hacs/jl/README.md`); the Python bridge is
  `code/python/langlandscape/hacs_bridge/`.

## HACS release

HACS **v0.2.1**, <https://github.com/drjanosch42/hacs>, DOI [10.5281/zenodo.24231446](https://doi.org/10.5281/zenodo.24231446)
(HACS (all versions): [10.5281/zenodo.24118841](https://doi.org/10.5281/zenodo.24118841));
`code/hacs/` is HACS v0.2.1 plus our clearly marked JL module and three documented hook lines (the `CMakeLists.txt` include and the `RegisterJL` declaration and call; see `plan/hacs/outbox/20261115T0150Z_laneB-closure.md`), plus regenerated CLI manual tables (`code/hacs/CHANGES.md`). Data: **hacs-data v0.2.0**,
<https://github.com/drjanosch42/hacs-data>, DOI [10.5281/zenodo.24147012](https://doi.org/10.5281/zenodo.24147012).

## Team and process

Fabian Januszewski and Abhijit A J. The project was run by a hierarchy of AI coding agents (a global master, stage masters and
work-package agents, with model-per-task selection, independent audits and a frozen build environment) under the
direction of the two team members; description, timeline and metrics in [`docs/agentic-process/`](docs/agentic-process/)
and the rules in `agents/rules/`.

## Licence

- **Prose** (LaTeX and other documents: `mathematics/`, `talk/`, `plan/`, `agents/`, Markdown, result records):
  [CC-BY-4.0](LICENSES/CC-BY-4.0.txt).
- **Lean** (`lean/Langlandscape/`, the team's own files in `lean/trace-formula-project-import/`, every `.lean` file):
  [Apache-2.0](LICENSES/Apache-2.0.txt), as in HACS's `lean/` and Mathlib.
- **Other code** (Python, C++/CUDA and scripts under `code/` and elsewhere):
  [GPL-3.0-or-later](LICENSES/GPL-3.0-or-later.txt) with an
  [NVIDIA CUDA Toolkit linking exception](LICENSES/LicenseRef-CUDA-exception-GPL.txt)
  (SPDX: `GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL`).
- **Third-party material keeps its own licence**: `code/hacs/` (the HACS 0.2.1 seed of the public release
  [HACS v0.2.1](https://github.com/drjanosch42/hacs), DOI [10.5281/zenodo.24231446](https://doi.org/10.5281/zenodo.24231446),
  with our marked JL additions listed in `code/hacs/CHANGES.md`;
  LGPL-3.0-only with its own CUDA exception, its `lean/` Apache-2.0; see `code/hacs/LICENSE`, `NOTICE`; our new files inside `code/hacs/` follow the same scheme: LGPL-3.0-only WITH the CUDA exception for code, Apache-2.0 under its `lean/` (decision Q1, final)), the vendored FLT modules in `lean/trace-formula-project-import/lean/Vendor/` and
  AxiomMath/Stacks in `lean/Langlandscape/Vendor/AxiomStacks/` (Apache-2.0, upstream headers kept). Mathlib (Apache-2.0)
  is a dependency and is not redistributed.

Details: [`LICENSE`](LICENSE), [`REUSE.toml`](REUSE.toml) (path-by-path mapping), [`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md).

Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team).

## Use of AI

- **Claude Code** with Claude models (Opus, Sonnet, Haiku, Fable) did the agentic work: drafting, implementing (LaTeX, Lean, Python, HACS),
  reviewing and auditing, orchestrated as described in [`docs/agentic-process/`](docs/agentic-process/) (global master → stage masters → workers;
  Fable audits; cross-account reviews; Lean gates from scratch, cross-checked on a second build machine from stage 02 on).
- **opencode** with Muse Spark Open and Mistral Large 4 (via the Open Math Model platform, see Acknowledgments) was used for Q&A and first-pass
  checks only (after a stage-1 trial as implementers, where both lost to Claude models), plus two disclosed external drafts: the discharges of Hyp.RamNrdSurj and Hyp.BrandtStabFree (see [Results in brief](#results-in-brief)).
- **No other AI tools** were used; computations use Python, PARI/GP (via cypari2) and HACS.
- **Human contributions and responsibility** (the two team members): the list of requirements for an integral approach and the Bruhat–Tits-tree route idea (prepared before the
  event, `plan/seed/`); the design of the orchestration (details augmented by Claude); steering (by interventions, not continuous) and the critical decisions; and responsibility for the mathematics, the Lean
  code, the implementation and the submission, including final review. Details: the report's AI-use section (`mathematics/submission/report.tex`).
- **Session transcripts**: the redacted agent session logs (formerly `supplementary/agent-logs/`) have been withdrawn from the public repository; see [Retraction of the agent logs](#retraction-of-the-agent-logs-2026-11-20).

## Retraction of the agent logs (2026-11-20)

**What.** `supplementary/agent-logs/` (the redacted agent session transcripts, 744 files, about 31 MB) and the `Claude-Session:` trailers in the commit messages were removed from the entire history. Everything else is unchanged: mathematics, Lean, code, talk, the submission report and `supplementary/gate-logs/`. Authors and dates are unchanged.

**How.** `git filter-repo --path supplementary/agent-logs --invert-paths`, together with a commit-message callback that drops the `Claude-Session:` lines, followed by a force-push on 2026-11-20 and the README commit `af9157b`. Old and new commits:

| old | new |
|---|---|
| `9f1de427748a0e5536a8f7163b6a7ff71e2bf8f8` | `65cb1aa9a2e60199b2bf11bae7e9a477b66e6244` |
| `94f3bad76bc44630a6469573cde6df949066c908` | `f4696502d3efce238d3bd6a6ec6e930d57c7ae9d` |

The `\PublicCommitHash` `9f1de42` cited in the submission report (`mathematics/submission/report.tex`, `src/macros.tex`) therefore corresponds to `65cb1aa`. Its tree is identical except that `supplementary/agent-logs/` is missing; with the old commit at hand this can be checked by `git diff --stat 65cb1aa <old>`. Some documents in the repository (the report, `docs/agentic-process/`, the metrics) still describe the logs as published; these references are historical.

**Why.** This is a precaution in light of recent AI-related security incidents. The logs had been pattern-redacted, and a scan of the full history found no credentials. Full agent transcripts nevertheless expose operational detail implicitly: infrastructure and file-system layout, account and session identifiers, and verbatim agent instructions and prompts. Such detail can help attackers profile or target agentic setups, for example through prompt injection. The logs are not required by the Mathathon rules, and the first-round judging was complete. All mathematical, formal and computational content stays public, and the process write-up remains in `docs/agentic-process/`.

**Note.** The old commits may remain fetchable by their shas on GitHub until GitHub purges them.

## Acknowledgments

We gratefully acknowledge support from an NVIDIA Academic Grant Program award to Fabian Januszewski (CUDA-GNFS project), which provided two NVIDIA RTX PRO 6000 Max-Q Workstation Edition GPUs used for the HACS computations, and from the Deutsche Forschungsgemeinschaft (DFG, German Research Foundation) – SFB-TRR 358/1 2023 – 491392403.
We thank the organizers of the Caltech × SAIR Mathathon 2026 for compute credits on the Open Math Model platform (https://os.openmathmodel.org/), which were used in this project (the opencode models Muse Spark Open and Mistral Large 4).
