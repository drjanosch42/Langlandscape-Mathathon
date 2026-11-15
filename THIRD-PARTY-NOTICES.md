<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Third-party notices

Langlandscape's own material is licensed as described in `LICENSE` (prose CC-BY-4.0; code GPL-3.0-or-later WITH
the NVIDIA CUDA Toolkit exception, `LICENSES/LicenseRef-CUDA-exception-GPL.txt`); the path mapping is `REUSE.toml`.
This file lists every third-party component in the repository, its licence, its upstream and its location. Each
component keeps its own licence; vendored files keep their upstream form and headers. Finalized from the stage-1
draft `lean/Langlandscape/THIRD-PARTY-NOTICES.draft.md` (WP S01-X6).

## Summary

| component | location in this repository | licence | upstream | notices |
|---|---|---|---|---|
| HACS 0.2.1 seed (Harder Arithmetic Cohomology System), Copyright (c) 2024-2026 Fabian Januszewski | `code/hacs/` | LGPL-3.0-only WITH the HACS NVIDIA CUDA Toolkit exception (code); Apache-2.0 (`code/hacs/lean/` own files); CC-BY-4.0 (`code/hacs/docs/`) | HACS development repository, seed of source commit `0ea75f737d005f8b2ee0c766df19e1ed5e571c9c` (`code/hacs/PROVENANCE.md`); code-identical to the public release HACS v0.2.1, https://github.com/drjanosch42/hacs, DOI 10.5281/zenodo.24231446 (census data: hacs-data v0.2.0, https://github.com/drjanosch42/hacs-data, DOI 10.5281/zenodo.24147012) | `code/hacs/LICENSE`, `LICENSE.GPL`, `NOTICE`, `COPYRIGHT.md`, `LICENSES/`, `REUSE.toml`, `docs/licence/THIRD_PARTY.md` |
| HACS's own third-party items: Anthropic FLT (25 Lean modules, Apache-2.0), a Lean 4 `LeanChecker.lean` excerpt (Apache-2.0), KaTeX 0.19.0 (MIT; fonts OFL-1.1) | `code/hacs/lean/Vendor/AnthropicFLT/`, `code/hacs/lean/tools/ReplayExact.lean`, `code/hacs/notebook/vendor/katex/` | as listed | as listed in `code/hacs/NOTICE` | `code/hacs/NOTICE` (authoritative) |
| Fermat's Last Theorem in Lean 4, Copyright 2026 Anthropic, PBC (itself containing material from the Imperial FLT project, flt-regular and Mathlib) | `lean/trace-formula-project-import/lean/Vendor/AnthropicFLT/` | Apache-2.0 | https://github.com/anthropics/fermats-last-theorem @ `6e837e75355538c7f80bab5b956861e86c4eacc2` | `…/Vendor/AnthropicFLT/LICENSE`, `…/Vendor/AnthropicFLT/NOTICE`, `…/Vendor/NOTICE`, `…/Vendor/ATTRIBUTION.md` |
| The FLT project (Imperial College London, led by Kevin Buzzard), Copyright (c) 2024-2026 the FLT project contributors (per-file headers) | `lean/trace-formula-project-import/lean/Vendor/ImperialFLT/` | Apache-2.0 | https://github.com/ImperialCollegeLondon/FLT @ `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` | `…/Vendor/ImperialFLT/LICENSE`, `…/Vendor/NOTICE` (item 2), per-file headers, `…/Vendor/ATTRIBUTION.md` |
| AxiomMath/Stacks (`StacksCore/`), AxiomMath; authors Kenny Lau, Brian Nugent, Ashvin A. Swaminathan, Yunzhou Xie (with AxiomProver) | `lean/Langlandscape/Vendor/AxiomStacks/` | Apache-2.0 | https://github.com/AxiomMath/Stacks @ `c496df0d9beea9deaeabcea8492605f9a0a2313b` | `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`, `ATTRIBUTION.md`, `PROVENANCE.md` (no upstream NOTICE) |

`…/Vendor/` abbreviates `lean/trace-formula-project-import/lean/Vendor/`. The rest of
`lean/trace-formula-project-import/` (the `AlgJL` Lean fork, its tools and its LaTeX) is the team's own material from
our GL(2) trace formula project and is licensed under the Langlandscape scheme (`LICENSE`, `REUSE.toml`).

## 1. Dependencies (not redistributed in this repository)

- **Mathlib** (https://github.com/leanprover-community/mathlib4), Apache-2.0, Copyright (c) the respective Mathlib
  authors. Pinned by `lean/Langlandscape/lake-manifest.json` and `lean/trace-formula-project-import/lean/lake-manifest.json`
  (Mathlib `v4.35.0`); fetched at build time, not vendored.
- **Lean 4** (https://github.com/leanprover/lean4), Apache-2.0, toolchain `leanprover/lean4:v4.35.0`; the other Lake
  packages of the manifests are under their own licences.
- **NVIDIA CUDA Toolkit**: proprietary (NVIDIA EULA); linked dynamically, as permitted by the CUDA exceptions of
  `LICENSE` and `code/hacs/LICENSE`.
- Python 3, PARI/GP and other tools used by `code/`: under their own licences, not redistributed.

## 2. Vendored Lean files, one row per file

### 2a. Anthropic FLT and Imperial FLT (via `lean/trace-formula-project-import/lean/Vendor/`)

| path | upstream URL | pinned rev | license | NOTICE / ATTRIBUTION file |
|---|---|---|---|---|
| `lean/trace-formula-project-import/lean/Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_HeckePair.lean` | https://github.com/anthropics/fermats-last-theorem | `6e837e75355538c7f80bab5b956861e86c4eacc2` | Apache-2.0 (license file `…/Vendor/AnthropicFLT/LICENSE`) | `…/Vendor/AnthropicFLT/NOTICE`; `…/Vendor/ATTRIBUTION.md`; `…/Vendor/NOTICE` |
| `lean/trace-formula-project-import/lean/Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_GelfandInvolution.lean` | https://github.com/anthropics/fermats-last-theorem | `6e837e75355538c7f80bab5b956861e86c4eacc2` | Apache-2.0 (license file `…/Vendor/AnthropicFLT/LICENSE`) | `…/Vendor/AnthropicFLT/NOTICE`; `…/Vendor/ATTRIBUTION.md`; `…/Vendor/NOTICE` |
| `lean/trace-formula-project-import/lean/Vendor/ImperialFLT/FLT/NumberField/Padics/RestrictedProduct.lean` | https://github.com/ImperialCollegeLondon/FLT | `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` | Apache-2.0 (license file `…/Vendor/ImperialFLT/LICENSE`) | `…/Vendor/NOTICE` (item 2); `…/Vendor/ATTRIBUTION.md` (file header) |
| `lean/trace-formula-project-import/lean/Vendor/ImperialFLT/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` | https://github.com/ImperialCollegeLondon/FLT | `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` | Apache-2.0 (license file `…/Vendor/ImperialFLT/LICENSE`) | `…/Vendor/NOTICE` (item 2); `…/Vendor/ATTRIBUTION.md` (file header) |

Anthropic FLT's NOTICE records that parts of that project were taken from the Imperial FLT project, flt-regular and
Mathlib (NOTICE item 1, reproduced verbatim in `AnthropicFLT/NOTICE`).

### 2b. AxiomMath/Stacks (`lean/Langlandscape/Vendor/AxiomStacks/`)

| path | upstream URL | pinned rev | license | NOTICE / ATTRIBUTION file |
|---|---|---|---|---|
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/SkolemNoether.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/Morita/SimpleRing.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/SimpleRing/DivisionRing.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/SimpleRing/TensorProduct.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/TwoSidedIdeal/Operations.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/RingTheory/TwoSidedIdeal/SpanAsSum.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/Algebra/Category/ModuleCat/Basic.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |
| `lean/Langlandscape/Vendor/AxiomStacks/StacksCore/LinearAlgebra/Dimension/Finite.lean` | https://github.com/AxiomMath/Stacks | `c496df0d9beea9deaeabcea8492605f9a0a2313b` | Apache-2.0 (license file `lean/Langlandscape/Vendor/AxiomStacks/LICENSE`) | none upstream; `lean/Langlandscape/Vendor/AxiomStacks/ATTRIBUTION.md` |

Note: the Stacks Project statements that these files formalize are GFDL. Only Lean code and tag numbers are copied
(see `lean/Langlandscape/Vendor/AxiomStacks/PROVENANCE.md`).

## 3. Licence compatibility

- **Lean: Apache-2.0 throughout.** Our own Lean files are Apache-2.0 (since 2026-11-14), the same licence as the vendored
  modules and Mathlib, so no licence combination question arises on the Lean side; each vendored file keeps its upstream
  header, NOTICE and attribution (Apache-2.0 §4).
- **Apache-2.0 → GPL-3.0 (other code).** Apache-2.0 code may be combined into a GPL-3.0(-or-later) work (one direction
  only). This concerns only our GPL-licensed non-Lean code (Python, C++/CUDA, scripts) where it uses Apache-2.0 material.
- **HACS (LGPL-3.0-only).** LGPL-3.0 code may be used by, and combined with, GPL-3.0 code. Because HACS is
  "-only", a combined work containing HACS code is in effect bound to version 3 of the GPL/LGPL for those parts.
  Both CUDA exceptions are Section-7 additional permissions of the same form, so CUDA linking is permitted throughout.
- **Stacks Project.** The statements formalized in `Vendor/AxiomStacks/` follow the Stacks Project (GFDL); only Lean
  code and tag numbers are copied (`lean/Langlandscape/Vendor/AxiomStacks/PROVENANCE.md`), no GFDL text.
- **literature/** is git-ignored and never committed; third-party papers are cited, not redistributed.
