# Vendor provenance

- Only file-by-file copies, made by `tools/vendor.py` (CLAUDE.md rule 13). Never clone or build the whole Anthropic repo.
- Read-only upstream clones (PLAN.md §3.0):
  - Anthropic FLT: `~/data/orbifold-cohomology-of-gl2/s20/flt/anthropic-flt/` at `6e837e75355538c7f80bab5b956861e86c4eacc2`
    (Mathlib `db584cd`, the old D1 pin until tag `mig-baseline`; the current D1 pin is v4.35.0 = `56a0058`, D24): files vendor byte-identically into `AnthropicFLT/` (lib `GL2TFVendor`).
  - Imperial FLT: `/tmp/claude-1000/flt/imperial-FLT/` at `1ab58c167e4fc60bef518cc02caa3fc15c9590d5` (Mathlib `300d0e5`,
    newer than ours): files go to `ImperialFLT/` (lib `GL2TFVendorImperial`) and normally need a back-port, recorded with
    `tools/vendor.py mark-modified`.
- `MANIFEST.tsv`: one row per file (sha256 upstream and local, lines, modified flag). `tools/vendor.py verify` and
  tfcheck check 10 compare it with the files.
- Vendored files build only in their own `tools/lbuild.sh GL2TFVendor` run (they `import Mathlib`, about 8 GB peak).

## algebraic_jl fork (2026-11-14)

This directory is a byte copy of four files of the parent repo (`lean/Vendor/` @84818d0): `Definitions.Def_LocalLanglands_HeckePair`,
`Definitions.Def_LocalLanglands_GelfandInvolution`, `FLT.NumberField.Padics.RestrictedProduct`, `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic` (its import), with the LICENSE/NOTICE/ATTRIBUTION files and
their `MANIFEST.tsv` rows (sha256 unchanged). Library names in the fork: `AlgJLVendor`, `AlgJLVendorImperial`.
