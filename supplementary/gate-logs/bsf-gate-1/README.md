<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Final Lean gate `bsf-gate-1` (logs)

Copied verbatim from the build machine's result branch in the team's (private) development repository
(`titan/bsf-gate-1`, commit fa7550699fe526dbf4da7c6ac9d37c7b1ff55fef). Gate run on the Lean tree of development commit
c70ef3a96e959eea219efe32706761583c3c5097, which is identical to `lean/` of this public repository except for Markdown files.

From scratch (fresh, unseeded worktree; frozen toolchain `leanprover/lean4:v4.35.0`, Mathlib at the v4.35.0 tag):
- `a-build.log`: `tools/lbuild.sh Langlandscape LanglandscapeTests`, rc 0, 4205 jobs;
- `b-vendor.log`: `tools/lbuild.sh LanglandscapeVendorStacks`, rc 0, 1955 jobs;
- `c-axioms.log`, `c-axcount.log`: `Audit/PrintAxioms.lean`, 955/955 rows, only `propext`, `Classical.choice`, `Quot.sound` (929 full triple, 23 subset, 3 none);
- `d-grep.log`: forbidden-token grep (`sorry|admit|^axiom|native_decide|ofReduceBool|implemented_by`) over our Lean sources: empty;
- `f-frozen.log`: `tools/check_frozen.sh`: frozen trees untouched;
- `summary.txt`, `*-time.log`: summary, wall times and peak memory.
