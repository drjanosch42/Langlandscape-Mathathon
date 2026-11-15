<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Building the Lean formalization

The Lean project is **`lean/Langlandscape`** (package `Langlandscape`; libraries `Langlandscape`,
`LanglandscapeTests`, `LanglandscapeVendorStacks`). Run `lake build` there. It depends on the in-repo import
**`lean/trace-formula-project-import/lean`** (package `GL2TF`, library `AlgJL`) as a path dependency, and on Mathlib at
rev `56a005855ea17e0b0958f73ec801ae140b0a1679` (the `v4.35.0` tag), toolchain `leanprover/lean4:v4.35.0`.

From a fresh clone (needs elan; downloads Mathlib and its dependencies plus the Mathlib build cache):

```
cd lean/Langlandscape
lake exe cache get      # Mathlib oleans
lake build              # builds the import's AlgJL modules (no cache exists for them), then Langlandscape
lake build LanglandscapeTests LanglandscapeVendorStacks   # optional: the test and vendored libraries
lake env lean Audit/PrintAxioms.lean                      # optional: the `#print axioms` audit
```

There is no Lake project at the repository root; `lean/Langlandscape` is the root of the Lean build. The team's own nodes
build through the wrapper scripts in `lean/Langlandscape/tools/` against a frozen Mathlib copy (see
`lean/Langlandscape/README.md`); external users do not need them.
