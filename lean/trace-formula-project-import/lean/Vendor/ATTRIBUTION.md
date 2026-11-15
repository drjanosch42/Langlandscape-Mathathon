# ATTRIBUTION: vendored files, upstream notices

Rows are appended by `tools/vendor.py`, one per vendored file: the upstream file, its copyright holder and authors.
For Anthropic FLT files these are the matching rows of upstream `ATTRIBUTION.md` (the Lean files there carry no
headers); for Imperial FLT files, the file's own header. Do not edit by hand.

| File (under lean/Vendor/) | Upstream | Copyright and authors (verbatim from upstream) |
|---|---|---|
| `AnthropicFLT/Definitions/Def_LocalLanglands_HeckePair.lean` | https://github.com/anthropics/fermats-last-theorem @ `6e837e753555`, `Definitions/Def_LocalLanglands_HeckePair.lean` | none listed in upstream ATTRIBUTION.md: Anthropic, PBC (NOTICE) |
| `AnthropicFLT/Definitions/Def_LocalLanglands_GelfandInvolution.lean` | https://github.com/anthropics/fermats-last-theorem @ `6e837e753555`, `Definitions/Def_LocalLanglands_GelfandInvolution.lean` | none listed in upstream ATTRIBUTION.md: Anthropic, PBC (NOTICE) |
| `ImperialFLT/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` | https://github.com/ImperialCollegeLondon/FLT @ `1ab58c167e4f`, `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` | Copyright (c) 2025 Matthew Jasper. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde |
| `ImperialFLT/FLT/NumberField/Padics/RestrictedProduct.lean` | https://github.com/ImperialCollegeLondon/FLT @ `1ab58c167e4f`, `FLT/NumberField/Padics/RestrictedProduct.lean` | Copyright (c) 2025 Salvatore Mercuri. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Salvatore Mercuri, Kevin Buzzard |


Note (global master, 2026-11-15): three rows were removed because those files are not vendored (they were dropped in curation and are absent from `MANIFEST.tsv`): `AnthropicFLT/Definitions/Def_RepTheory_SmoothAdmissibleSchurCommutant.lean`, `AnthropicFLT/Definitions/Def_RepTheory_TestFunctionAction.lean`, `AnthropicFLT/Definitions/Def_Mathlib_MeasureTheory_Function_L2KernelOperator.lean`.
