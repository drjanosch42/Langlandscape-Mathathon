# PROVENANCE: AxiomStacks (StacksCore)

- Upstream: https://github.com/AxiomMath/Stacks, rev `c496df0d9beea9deaeabcea8492605f9a0a2313b` (`main`, 2026-11-11,
  "feat: refine existing formalizations (#17)").
- Retrieval: the 8 `.lean` files and `LICENSE` were fetched once at that rev by S01-X5 into `.exp/inputs/`
  (raw content, byte for byte) and copied here without any change. Vendored under `Vendor/AxiomStacks/<upstream path>`.
- Modifications: none. Every file has `modified = no` in `MANIFEST.tsv`.
- Not vendored: `StacksFrontier/**`, `StacksCore/Tactic/**` (the `EgaSgaAttribute` and `StacksAttribute` files),
  `NOTICE` (none upstream). The `@[stacks …]` attributes occur in 3 of the 8 `.lean` files: 10 attributes carrying
11 tag entries (line 191 of `TensorProduct.lean` has one attribute with two entries). Counted with
`grep -rn "@\[stacks" StacksCore --include=*.lean`: `RingTheory/SkolemNoether.lean` (2 attributes, lines 124, 140);
`RingTheory/SimpleRing/TensorProduct.lean` (4 attributes, lines 135, 177, 191, 203); `RingTheory/Morita/SimpleRing.lean`
(4 attributes, lines 36, 52, 74, 103). The other 5 `.lean` files (`SimpleRing/DivisionRing.lean`,
`TwoSidedIdeal/Operations.lean`, `TwoSidedIdeal/SpanAsSum.lean`, `Algebra/Category/ModuleCat/Basic.lean`,
`LinearAlgebra/Dimension/Finite.lean`) contain no `@[stacks …]` attribute. The 8 files import only Mathlib and other
vendored `StacksCore` files.

## Integrity (acceptance step 1)

Each vendored file was checked with `git hash-object <file>` against the upstream GitHub tree blob sha recorded by X5
in `.exp/inputs/SHAS.tsv`. The sha256 is that of the same bytes. Result: 9 of 9 match (8 `.lean` files + `LICENSE`).

| Upstream path (under `StacksCore/`, or `LICENSE`) | git blob sha (tree = upstream) | sha256 |
|---|---|---|
| `RingTheory/SkolemNoether.lean` | `2064ab8046bf815c70fee41d4172811fa6e23328` | `28e02088adb5705d79804feb8c7c581fa11005fcbd5ccc984b9c394936581a39` |
| `RingTheory/Morita/SimpleRing.lean` | `7b6d59bc5cb6ff69ee69481102f5699df1466f47` | `5f5496b114b4852d86535beacd0db9ecc28eeff81fe9d68257627bdda66e6edf` |
| `RingTheory/SimpleRing/DivisionRing.lean` | `1f56ffbbed2790ce89547ae6d684ab1483313e11` | `8ad23b90c429e13146c1dd4c0493cf9da0962000b1cdc88292f061bac5596419` |
| `RingTheory/SimpleRing/TensorProduct.lean` | `4672a958af86bd14fba00c6ca693bc5cd9541fef` | `b3923c79247c13f6f13fc4fb6094570bd1b8065d3361425ae72003eefb6f8b37` |
| `RingTheory/TwoSidedIdeal/Operations.lean` | `89f07145046338cc6663b6584c0f7c9b206353e3` | `46be68d41f8ac60c28a7391b92e845b00bde919b3b9e2244282293ce5b50fe61` |
| `RingTheory/TwoSidedIdeal/SpanAsSum.lean` | `d2d0deaad9b942ab1b8ba5eea54633acfd5d8729` | `123adece5b72fe7eddcbf9d854712612bb5868fedb65a541b31db7c9b8ba71a4` |
| `Algebra/Category/ModuleCat/Basic.lean` | `03eb6a5c4b95dc891927d81abb64053fa392002a` | `328f4ed30e38f64e405086e6d26787d3aedbd25c7a0ea5600c0dd6587021c677` |
| `LinearAlgebra/Dimension/Finite.lean` | `da7ce7cfef4dbd517d01cd5a44af0d0b27e310d4` | `864491aa89ad02907f372ab6ea15a85407a77c61f089dedecd427422426fac8c` |
| `LICENSE` (repo root) | `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |

## Docstring check

Method: every `/-- … -/` and `/-! … -/` block of the 8 files was extracted (`awk`) and scanned for TeX markers (`$`,
`\(`, `\[`) and for Stacks-project phrasing (`Lemma/Proposition N`, `Tag`, `stacks project`, `Section N`). The ten
`@[stacks …]` attributes (eleven tag entries, see above) and the `stacks 074E(3)` reference in the SkolemNoether docstring were listed separately.
Scope limit: the Stacks LaTeX source is not in the worktree and is not fetched (no network in this WP), so this is a
mechanical check, not a comparison against Stacks text.

verbatim-Stacks-prose check of the 8 docstrings: no TeX math markers and no verbatim Stacks LaTeX found. The docstrings
are English prose written for Lean (for example "Let `A` be a central simple `K`-algebra. If a two-sided ideal …"). The
only references to the Stacks Project are explicit: `TensorProduct.lean` lines 30 (link to tag 074B), 132–134 and
189–190 ("slightly different/more general version of the statement in the stacks project"), `TensorProduct.lean`
176 ("generalized version of stacks 074C part 1") and `SkolemNoether.lean` line 17 ("stacks 074E(3)"). Tag numbers
are kept (allowed: "only Lean code and tag numbers are copied"). The `Tags` and `References` sections are upstream
metadata. The check does not establish that no sentence is a close paraphrase of Stacks text; it only excludes
TeX math and Stacks LaTeX. The single-line grep is therefore not the whole check; the manual review of multi-line
docstrings below completes it.

## Stacks-phrased docstrings (manual review of multi-line docstrings)

Method: every `/-- … -/` block of the 8 files, multi-line blocks included, was extracted with `awk` and filtered for
Stacks-style openings ("Let … Then", "If … then", "Lemma", "Tag", "stacks project"). Each flagged block was then read by
hand. Status words: *reviewed paraphrase/statement, tag cited* = the docstring states a Stacks-style result and the
declaration carries a `@[stacks …]` attribute; *reviewed paraphrase/statement, tag not cited* = the docstring is
phrased like a Stacks statement but carries no tag. These are English statements of results written for Lean. No
sentence was found to be a copy of Stacks text, but the wording of these statements has not been compared with the
Stacks LaTeX (not in the worktree).

| File (under `StacksCore/`) | Line | Docstring (opening) | Status |
|---|---|---|---|
| `RingTheory/SimpleRing/TensorProduct.lean` | 86 | "Let `A` be a central simple `K`-algebra. If a two-sided ideal `I` …" (`eq_zero_of_sum_tmul_mem`) | reviewed paraphrase/statement, tag not cited |
| `RingTheory/SimpleRing/TensorProduct.lean` | 118 | "If `A` is a central simple `K`-algebra, then a two-sided ideal … is trivial." | reviewed paraphrase/statement, tag not cited |
| `RingTheory/SimpleRing/TensorProduct.lean` | 129–134 | "Let `A` be a central simple `K`-algebra and `B` any `K`-algebra. Then every two-sided ideal … is generated by its intersection with `1 ⊗ B`." (`map_comap_includeRight`) | reviewed paraphrase/statement, tag cited (`@[stacks 074B]`, line 135) |
| `RingTheory/SimpleRing/TensorProduct.lean` | 162 | "Let `A` be a nontrivial `K`-algebra. Mapping a two-sided ideal of `B` …" (`comap_map_includeRight`) | reviewed paraphrase/statement, tag not cited |
| `RingTheory/SimpleRing/TensorProduct.lean` | 188 | "The tensor product of a central simple algebra and a simple algebra is simple." | reviewed paraphrase/statement, tag cited (`074C "part 2"`, `074F`, line 191) |
| `RingTheory/SimpleRing/TensorProduct.lean` | 45 | "If `g ∘ f` kills a two-sided ideal `J`, then …" (private) | reviewed statement, tag not cited |
| `RingTheory/SimpleRing/TensorProduct.lean` | 209, 216 | "If `A ⊗[K] B` is nontrivial then so is the left (right) factor." | reviewed statement, tag not cited |
| `RingTheory/Morita/SimpleRing.lean` | 93 | "If a finite `k`-module `P` is `A`-isomorphic to `ι →₀ S` …" (private) | reviewed paraphrase/statement, tag not cited |
| `LinearAlgebra/Dimension/Finite.lean` | 11 | "If `M` is trivial and `N` has the same rank as `M` …" | reviewed statement, tag not cited |

## Build status

Built by the stage master: `tools/lbuild.sh LanglandscapeVendorStacks` rc 0 locally (2026-11-14, before the
no-local-Lean directive) and on TITAN (gates s01-gate-1, s01-l14-1/-2, s01-l14-2-scratch: rc 0, 0 warnings);
`#check @skolemNoether`, `#check @skolemNoether'` OK.
