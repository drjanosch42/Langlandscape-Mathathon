DRAFT — Fabian: choose license

# Third-party notices (draft, S01-X6)

Status: draft. No LICENSE is chosen here, and this file is not at the repository root. The repository license is
Fabian's decision (OVERVIEW §8 F5); the global master moves this list to the root only after that decision.

Scope: every third-party Lean source vendored in this repository, one row per vendored file. Rows of the two FLT
imports are taken from `lean/trace-formula-project-import/lean/Vendor/MANIFEST.tsv` (read-only); rows of AxiomStacks
from `lean/Langlandscape/Vendor/AxiomStacks/MANIFEST.tsv`. Every path below was checked to exist, and every license
file named below was checked to exist.

Paths of the form `lean/trace-formula-project-import/lean/Vendor/…` are relative to the repository root. The
Anthropic and Imperial rows are the ones in the import's MANIFEST, and every one of them is an Apache-2.0 file.

## Anthropic FLT and Imperial FLT (via `lean/trace-formula-project-import/`)

| path | upstream URL | pinned rev | license | NOTICE / ATTRIBUTION file |
|---|---|---|---|---|
| `lean/trace-formula-project-import/lean/Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_HeckePair.lean` | https://github.com/anthropics/fermats-last-theorem | `6e837e75355538c7f80bab5b956861e86c4eacc2` | Apache-2.0 (license file `…/Vendor/AnthropicFLT/LICENSE`) | `…/Vendor/AnthropicFLT/NOTICE`; `…/Vendor/ATTRIBUTION.md`; `…/Vendor/NOTICE` |
| `lean/trace-formula-project-import/lean/Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_GelfandInvolution.lean` | https://github.com/anthropics/fermats-last-theorem | `6e837e75355538c7f80bab5b956861e86c4eacc2` | Apache-2.0 (license file `…/Vendor/AnthropicFLT/LICENSE`) | `…/Vendor/AnthropicFLT/NOTICE`; `…/Vendor/ATTRIBUTION.md`; `…/Vendor/NOTICE` |
| `lean/trace-formula-project-import/lean/Vendor/ImperialFLT/FLT/NumberField/Padics/RestrictedProduct.lean` | https://github.com/ImperialCollegeLondon/FLT | `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` | Apache-2.0 (license file `…/Vendor/ImperialFLT/LICENSE`) | `…/Vendor/NOTICE` (item 2); `…/Vendor/ATTRIBUTION.md` (file header) |
| `lean/trace-formula-project-import/lean/Vendor/ImperialFLT/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` | https://github.com/ImperialCollegeLondon/FLT | `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` | Apache-2.0 (license file `…/Vendor/ImperialFLT/LICENSE`) | `…/Vendor/NOTICE` (item 2); `…/Vendor/ATTRIBUTION.md` (file header) |

Anthropic FLT's NOTICE records that parts of that project were taken from the Imperial FLT project, flt-regular and
Mathlib (NOTICE item 1, reproduced verbatim in `AnthropicFLT/NOTICE`).

## AxiomStacks (`lean/Langlandscape/Vendor/AxiomStacks/`)

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

## Open for Fabian

- Choice of the repository LICENSE (F5). Nothing in this draft depends on it.
