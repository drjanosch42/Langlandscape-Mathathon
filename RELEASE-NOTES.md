<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Mathathon submission (2026-11-15)

Team Langlandscape (Abhijit A J, Fabian Januszewski), topic: the Jacquet–Langlands correspondence, Caltech × SAIR Mathathon 2026.
Overview and build instructions: [`README.md`](README.md). Status words: *proved* / *formalized* / *computed* / *conjectural* /
*cited*; *formalized modulo H* means that the statement compiles with the registered hypotheses H as explicit arguments.
All statuses below are those of the milestone closures (`plan/implementation/outbox/*milestone-closure-s0*.md`).

**Public repository and provenance.** This public repository (https://github.com/drjanosch42/Langlandscape-Mathathon) contains the final
tree as a single commit, plus one commit that inserts that commit's hash into the report. Commit hashes and branch names cited in this
repository refer to the team's development repository, which is kept private because its history contains unfiltered session logs;
they are cited for provenance. The Lean code here is identical to the gated tree `c70ef3a9` except for Markdown files.

## What is included

| deliverable | path |
|---|---|
| Mathematical development, chapters s01-s06 (170 pp) | `mathematics/main.pdf` (sources `mathematics/main.tex`, `mathematics/chapters/`) |
| Final report | `mathematics/final-report/final-report.pdf` |
| Report on the registered hypotheses | `mathematics/report/standalone-hypotheses.pdf` |
| Note on a sign in the literature | `mathematics/notes/hsieh-sign.pdf` (4 pp) |
| Lean 4 formalization | `lean/Langlandscape/` (hypothesis registry `HYPOTHESES.md`, audits `audits/`) |
| Import of GL(2)/Q and quaternion material | `lean/trace-formula-project-import/` (the import ships its compiled LaTeX PDFs under `latex/build/`) |
| Computations and results | `code/python/`, `code/cas/`, `code/results/` (index: `code/results/INDEX.md`) |
| HACS snapshot and JL transfer | `code/hacs/` (HACS 0.2.1), `code/hacs/jl/` |
| Talk (22 pp) | `talk/main.pdf` |
| Six-stage status overview | `summary/six_stage_plan.pdf` (also `.html`) |
| Agentic process write-up | `docs/agentic-process/` |

## Headline results

1. **Quaternionic foundations and Brandt graphs (s01, s02).** Quaternion orders, class sets, Eichler mass, Hecke operators, the
   local tree and the Brandt graph BG(U, q) with its quotient and Hecke-commutation statements: *formalized* (explicit
   registered hypotheses Hyp.SA, HS, BTtree, SerreCoh, SerreFree, RamNrdSurj for the tree-dependent parts; RamNrdSurj is
   discharged by `Hyp.ramNrdSurj_holds`, *formalized*); validated
   numerically on 240 cases (*computed*).
2. **Ribet sequence and Ihara lemma (s03).** Weighted graphs, the sequence for BG over any coefficient ring, Ihara (i), (ii):
   *formalized*; Ihara (iii) only as a statement layer. Mazur's check |Φ^comb| = num((q−1)/12) for q ∈ {11, 23, 37, 101, 131}
   *computed*.
3. **Ordinary part and Λ-adic sequence (s04).** Ordinary projector, control statements, the ordinary Ribet sequence at level s:
   *formalized*; `Hyp.PadicOrdDecomp` discharged; `Hyp.HidaControl` (schematic), `HsiehCR`, `MordLambdaFree`, `InvLimExact` open.
4. **Comparison hypothesis (s05).** `Hyp.X` (X1)-(X4) is stated, registered **open** and never called known; the dictionary,
   consistency lemmas and finite-level Λ-adic comparison are *formalized*; non-vacuity only through toy instances.
   `prop:s05-Xlambda(c2)` is open.
5. **Integral defect (s06).** Theorem E (i)-(iv), Lemmas S, D, G: *proved*; the commutative-algebra layer (`CommAlg/`)
   *formalized* (Thm E(iii), DVR half, included). **`Defect.defect_formula` is *formalized modulo the registered `Hyp.*`,
   including the Galois half (`Hyp.FreeRankTwo`)*; it is not an unconditional theorem.** The defect theorem is *proved modulo
   cited results* (Hida control, Hsieh, Kim–Ota) and registered hypotheses. The level statement for q ≡ −1: M = 1 *proved modulo
   cited*; squarefree M under the stated hypotheses (Fabian's decision, wording in chapter s06); **N(rhobar) > 1 open**.

## Lean gate

Final gate: after the merge of the **`Hyp.BrandtStabFree` discharge** (Lean tree `c70ef3a9`; bsf-gate-1 on TITAN, from scratch in an
unseeded worktree: `Langlandscape` + `LanglandscapeTests` rc 0, 4205 jobs, VendorStacks rc 0, 1955 jobs; logs `fa755069`):
955/955 standard (929 full triple, 23 subset, 3 none; the 5 new rows are full triples), `sorry` 0 in our files, grep empty,
`check_frozen` clean; the gate logs are in `supplementary/gate-logs/bsf-gate-1/`. Before it, the **Lean submission bundle** (merge `28d2b091` on `main`, gate commit `dc61af50`; subl-gate-1 on TITAN, from scratch,
4199 jobs, rc 0, 323 s; subl-gate-1x on CONCEPTD, fresh checkout, 341 s, PASS). The bundle fixes the GL2TF path dependency in
`lean/Langlandscape/lakefile.toml` so that a fresh clone builds, adds [`BUILDING-LEAN.md`](BUILDING-LEAN.md) at the repository root,
adds 110 rows to `Audit/PrintAxioms.lean` (102 of the 104 chapter-cited declarations that were not yet audited; the 2 test-library
declarations `LanglandscapeTests.S04.Hyp.hsiehCR_toy` and `LanglandscapeTests.Hyp.S05.toyTate_gal_uncond` are not in the audit, and
the 8 new twins below), and adds `Langlandscape/Uncond.lean` with the 8 `_uncond` twins of the `Hyp.RamNrdSurj` consumers
(`Quat.nrdSurj_{Ohat,U0,U1,Utower}_uncond`, `Tree.isQAdmissible_{Ohat,U0,U1,Utower}_uncond`): free of registered hypotheses, under the
stated explicit hypotheses (none / `hN` / `hqN`); the 18 `PadicOrdDecomp` twins of `Ordinary/TowerUncond.lean` already existed.
It supersedes the previous final gate at sha `2323a252` (ramnrd-final-2 on TITAN, from scratch, 4198 jobs, rc 0, 321 s; quick check
ramnrd-3 on CONCEPTD, PASS; 840/840), run after the merge of the `Hyp.RamNrdSurj` discharge, and the s06 gate at sha `44058153`
(s06-final-1 on TITAN, from scratch, 4194 jobs, 319 s; s06-final-1x on CONCEPTD, fresh checkout, 5:21; 836/836):

- at the bundle gate, **950/950** declarations of `Audit/PrintAxioms.lean` used only `propext`, `Classical.choice`, `Quot.sound` (nonstandard 0);
- the same 23 lines with a proper subset of the standard triple as at `2323a252`; no `sorryAx`; 0 warnings in `Uncond.lean`;
- forbidden-token grep empty; **`sorry`: only the one in the frozen import** (`Instances.lean:1815`); `check_frozen` clean;
- **29 registered hypotheses** (28 `Langlandscape.Hyp.*` rows plus the reused `GL2TF.Hyp.EichlerMass`); 3 discharged
  (`PadicOrdDecomp`, `RamNrdSurj`, `BrandtStabFree` by `Hyp.brandtStabFree_holds` from an external opencode/Mistral draft,
  integrated, audited (Fable, PASS) and gated by our agents), 1 conditionally discharged (`ResidualBurnside`).

Progression of the gate: s01 161 lines, s02 195, s04 592, s05 747, s06 836, ramnrd-final-2 840 (the four declarations of the
`RamNrdSurj` discharge: `Hyp.ramNrdSurj_holds`, `Hyp.ramNrdSurj_of_local`, `Local.exists_nrd_eq_unit_of_ne_two`,
`Local.exists_nrd_eq_unit_two`), submission bundle 950, final (BrandtStabFree discharge, the five new declarations) 955.

**External contribution.** The discharge of Hyp.RamNrdSurj was drafted by an external model (mistral-large-4-0 via opencode), run by Fabian Januszewski on Abhijit A J's machine, outside our agent process (where opencode is Q&A-only); it was integrated into the library, independently audited (Fable, PASS WITH REMARKS) and gated from scratch by the Langlandscape agents. Fable audits of Lean and chapters were run at each
stage (reports in `lean/Langlandscape/audits/`, `mathematics/audits/`).

## Computations (*computed*)

Python package `langlandscape` (pytest: 483 passed, 3 skipped at the Lane A closure) and PARI cross-checks; results with
provenance in `code/results/`. Examples: class sets and masses; weight-2 Brandt matrices; T_ℓ on M(Ô^×; V_k) matching
S_k(Γ_0(D))^new (66/66); Ribet collapse; the ordinary sign pin ⟨p⟩_M in U_p^* = ⟨p⟩_M U'_p (+1); FD2 sign checks
(a_q = +λ(Π_q) on 144/144 eigenlines); the T4 Hecke side with lengths 1, 1, 1, 1, 2 at k = 12, 28, 44, 60, 124 (agrees with the prediction),
independently cross-checked in `code/cas/s06-xcheck`. The regression C4(i) covers 131/319 cases only (partial).

## HACS

HACS v0.2.1 (<https://github.com/drjanosch42/hacs>, DOI 10.5281/zenodo.24231446; HACS (all versions): 10.5281/zenodo.24118841; `code/hacs/` is HACS v0.2.1 plus our clearly marked JL module and three documented hook lines (the `CMakeLists.txt` include and the `RegisterJL` declaration and call; see `plan/hacs/outbox/20261115T0150Z_laneB-closure.md`), plus regenerated CLI manual tables (`code/hacs/CHANGES.md`)), data hacs-data v0.2.0
(<https://github.com/drjanosch42/hacs-data>, DOI 10.5281/zenodo.24147012). Both lanes are *computed*, nothing is called certified.

- **Lane A** (`plan/hacs/outbox/20261115T0137Z_laneA-closure.md`): Python bridge and runner (provenance, env allowlist); GL(2) D-new
  checks (66/66, 8/8, extended grid 152/204); definite local algebra (Mazur's 5 non-étale and Gorenstein; clean negative control);
  Betti side coker(Ψ*Ψ)_m = (Z/17)² at k = 12, 28, 44, 60; the exchange format `langlandscape_brandt/v2` with 74 records.
- **Lane B** (closure FINAL: `plan/hacs/outbox/20261115T0150Z_laneB-closure.md`, branch `impl/hacs-laneB`): Brandt lattices through HACS's
  integral engine, exact congruence modules C_f. The Eisenstein congruence module is Z/num((q-1)/12) for every prime q <= 600 at l >= 5
  (109/109 levels, 178 s) and exactly, 2- and 3-parts included, for the first 80 primes, q <= 409 (80/80, exact Z route; the run was capped by a 15-min limit; the dense BigInt Smith step
  is the bottleneck at h >~ 40). On the 14 Lane A levels the exact route also gives Z/num((q-1)/12). Beyond Mazur (k > 2; 60 integral Sym^n cells, 26 of positive rank; the closure counts 32) the only
  nontrivial lattice congruence module is |C| = 37 at D = 13, k = 8 (lattice not canonical). Native C++ and Python agree on 69/69 orbit
  Smith lists; class set and T_2 for B_{997,inf}: 0.02 s native vs 64.7 s Python (about 10^3 times; build side only, no read-side speed claim).
  Eight disclosed deviations D1-D8 (relaxed protocol, targeted validation only, L + L adapter, own BigInt Smith, `OC_ENABLE_JL` default ON, ...).

## A correction to the literature

While checking the U_q normalisation for q | N^- we found that Hsieh's paper *Hida families and p-adic triple product
L-functions* (§4.5, p. 34) states JL(U_q) = (−1)U_q; as we read it, with the normalisations of that paper the correct relation is
JL(U_q) = +U_q (treated as an erratum). The correction concerns one sentence, and as far as we can see it has no effect on the theorems of the paper. The technical
note `mathematics/notes/hsieh-sign.pdf` (4 pp) gives the precise location and normalisations, a proof (*proved*
modulo cited inputs for trivial central character at q; for an unramified non-trivial central character at q a proof sketch), numerical evidence (*computed*: 144 of 144 eigenlines) and a list of the places that do and do not
depend on the sign. In the chapters this is decision FD2.

## Known limitations and open items

- Hypotheses: 29 registered, open unless stated in their row; toy instances prove consistency only. Apart from `RamNrdSurj`
  (discharged by `Hyp.ramNrdSurj_holds`), no cited hypothesis is discharged by a Lean term; `BrandtStabFree` (proved in the
  chapter, not cited) is discharged by `Hyp.brandtStabFree_holds`.
- `RamNrdSurj` discharge, follow-ups: the `AlgJL` import in `Local/QuatNrdOdd.lean` and `Local/QuatNrdTwo.lean` is not minimised;
  the two files use the non-module layout (their dependencies are not modules); stale "hypothesis" wording in the docstrings of
  `Quat/LevelNrd.lean:26` and `Tree/Admissible.lean:48-59`.
- `Hyp.X` (s05) open; `prop:s05-Xlambda(c2)` open (six missing steps listed in `rem:s05-c2open`); FD1 decided (μ_N-model with Picard functoriality, Fabian 2026-11-15).
- s06: N(rhobar) > 1 open (`\stopen`); F1 numerically untested; the case (gamma) is empty (audit-confirmed) but not formalized;
  C4(i) partial (131/319); T4 Betti side per Lane A computed only at k = 12, 28, 44, 60 (k = 124 not reachable).
- Several citations could not be checked on our node (Böckle 2007, Dimitrov 2009, EPW06, Edixhoven 1992, Wiles 1988; SGA 7 pointers; JL Thm 14.4).
- Lean: remaining audit minors (L12 R9-R11 and optional items), about 187 linter warnings in `Langlandscape/` and 71 in tests (0 in the s06 files; 6 module-system import notices in the two `Local/QuatNrd*` files),
  one locally suppressed `linter.overlappingInstances` on three headline theorems; not formalized: items listed in the s04 closure (e.g. `Hyp.InvLimExact`-dependent surjectivity).
- HACS: a full HACS validation row (`--all`, golden strict, digests, LABEL_CENSUS) is still due after merging Lane B (D2); the exact route stopped after the first 80 primes, q <= 409 (15-min cap); the Python reference sweep stopped at q = 131 for the full table; 52 high-memory Lane A cells skipped; `module_Z()` opt-in;
  k > 2 lattices not canonical.
- Post-Mathathon: restructure the binders of `Defect.Setting`; stage 07 exports are planned (`plan/`).

## Licensing and acknowledgments

CC-BY-4.0 for prose, Apache-2.0 for Lean, GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL for other code, `code/hacs/` under its own
scheme (our new files inside `code/hacs/`: LGPL-3.0-only WITH the CUDA exception for code, Apache-2.0 under its `lean/`; decision Q1, final), vendored files under their upstream licences: see the Licence section of [`README.md`](README.md), `LICENSE`, `REUSE.toml`,
`THIRD-PARTY-NOTICES.md`. The acknowledgments (NVIDIA Academic Grant Program, DFG SFB-TRR 358/1 2023 – 491392403) are at the end of `README.md`.
