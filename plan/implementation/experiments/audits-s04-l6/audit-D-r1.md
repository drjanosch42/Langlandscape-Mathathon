# Audit: S04-L6 strand D, round 1 (delta audit)

Scope checked: `strand-D.patch` (delta against the round-0 state, one file) against `brief.md`, `stage-excerpt.tex`,
`check.txt`, `prior-findings.md`; Mathlib names used in the new code against the frozen Mathlib; binder conventions
against stage-1 `Local/UpCosets.lean`. Lean was not run by the auditor. The patch contains only the round-1 delta, so
the unchanged parts of the file were not re-read (they are covered by the round-0 audit).
`HL` = `lean/Langlandscape/Langlandscape/Local/HidaLocal.lean`; line numbers are new-file lines computed from the hunk
headers.

## Status of prior findings

- **A0.1** (bare `≃` only) — **RESOLVED**. `kppQuotMulEquiv` (`HL:369-373`) is the `≃*` version
  (`quotientKerEquivRange` composed with `subgroupCongr (range_dModHom hs)`), `subgroupOf_K1_succ_normal`
  (`HL:362-364`) gives normality, and `kppQuotEquiv` is now defined as its underlying equivalence transported along
  `ker_dModHom`. Residual point: A1.2.
- **A0.2** (`kppQuotEquiv_mk` by `rfl` through composed equivalences) — **OPEN**. A `rw` chain was added, but only as
  the first alternative of `first | (rw […]; done) | rfl` (`HL:400-403`); the `rfl` proof is still in the source as a
  fallback, so it cannot be established from the source or from `check.txt` that the proof no longer rests on
  definitional unfolding. Continued as A1.1.
- **A0.3** (unproved remark in the docstring of `kppQuotEquiv`) — **RESOLVED**. Sentence deleted (`HL:385-389`).
- **A0.4** (implicit proof binder `{hgh}`, helpers parked in the file, duplicated stage-1 proof) — **RESOLVED**.
  `hgh` is explicit (`HL:258`), the one call site in the patch passes `Kpp_le_GL2Zl s (k * k').2` (`HL:289`), and the
  module docstring carries the maintenance note (`HL:33-36`). The duplication itself stays, which is acceptable since
  the package may not edit stage-1 files.

No prior finding REGRESSED.

## Defects

No critical and no major defects found.

- **A1.1** — minor — `HL:379-383` (`kppQuotMulEquiv_mk`) and `HL:400-403` (`kppQuotEquiv_mk`); continuation of A0.2,
  counted once. Both proofs are `first | (rw […]; done) | rfl`. The source does not determine which branch proves the
  statement: if the `rw` chain fails at any step the proof silently falls back to `rfl` (now through one more layer,
  `kppQuotMulEquiv`), and the `rw` branch is dead code; if it succeeds, the `rfl` branch is dead code. The build PASS
  does not distinguish the two. All lemma names in the chains exist in the frozen Mathlib
  (`MulEquiv.trans_apply`, `MulEquiv.subgroupCongr_apply`, `MulEquiv.ofBijective_apply`, `QuotientGroup.lift_mk`,
  `MonoidHom.coe_rangeRestrict`, `MonoidHom.coe_toHomUnits`, `Subgroup.quotientEquivOfEq_mk`,
  `MulEquiv.toEquiv_eq_coe`, `MulEquiv.coe_toEquiv`), so the chain is plausible, but it is unverified.
  Required fix: keep exactly one proof per theorem. Either confirm on the build node which branch succeeds and delete
  the other, or replace both by a single `simp [kppQuotMulEquiv, QuotientGroup.quotientKerEquivRange,
  QuotientGroup.rangeKerLift]`-style proof; if `rfl` is what remains, say so in a comment.
- **A1.2** — minor — `HL:366-373` (`kppQuotMulEquiv`). The group isomorphism is stated for
  `Kpp p s ⧸ (dModHom p s).toHomUnits.ker`, not for the quotient form fixed by the brief and the stage tex,
  `Kpp p s ⧸ (K1 p (s + 1)).subgroupOf (Kpp p s)` (`K'_s/K_{s+1} ≅ ker(Δ_{s+1} → Δ_s)`). For that form only the bare
  `≃` exists; a user needing multiplicativity there must still transport by hand along `ker_dModHom`, and there is no
  lemma relating `kppQuotEquiv` to `kppQuotMulEquiv` on elements. Required fix: add the `≃*` on the brief's quotient
  (local `haveI := subgroupOf_K1_succ_normal s` plus `QuotientGroup.quotientMulEquivOfEq (ker_dModHom s).symm`), or a
  `map_mul`-type lemma for `kppQuotEquiv` stated with that normality.

## Non-defects noted (not counted)

- The patch touches only `HL`, which is an allowed output file. No `sorry`/`admit`/`axiom`/`native_decide`, no
  heartbeat option, no new import. The three new declarations have docstrings with an `s04-…` label.
- `subgroupOf_K1_succ_normal` is a theorem, not an instance; consistent with the brief's rule against global
  instances and with `ker_dModHom` needing no `hs`.
- The brief's required names and statement shapes (`Kpp`, `Kpp_mul_varpi_mul_Kpp`, `exists_varpi_conj`,
  `relIndex_Kpp`, the equivalence) are not changed by the delta; the type of `kppQuotEquiv` is unchanged.
- No test was added for `kppQuotMulEquiv`; the brief requires tests only for the listed outputs.
- Caveat on evidence (same kind as in round 0): `check.txt` is headed "commit 79fa5a33…, strand label D, round 1",
  while the embedded result block names `s04-l6-a-4`, "round 4" and ref `0804484`. The auditor cannot confirm that
  the PASS refers to exactly this patch; the verdict takes the check at face value (BUILD rc=0, CHECK_WP 0 FAIL,
  nonstandard axioms 0).

## Mathematics check of the delta

- Normality: `(K1 p (s+1)).subgroupOf (Kpp p s) = ker dModHom`, and kernels are normal — correct.
- `kppQuotMulEquiv`: first isomorphism theorem for `d mod p^{s+1}` on `Kpp p s`, range identified with
  `ker(ZMod.unitsMap)` by `range_dModHom hs` — correct, agrees with the stage-tex statement "via `d`".
- `kppQuotEquiv` redefinition: same map as in round 0 (`quotientEquivOfEq` then the `MulEquiv` as an `Equiv`) —
  statement and element formula unchanged.

## Rubric

- correctness: **4** — every new statement checks and matches the stage tex; no change to the audited mathematics.
- completeness: **2** — all outputs of the brief present (unchanged), no `sorry`, docstring labels on all new declarations.
- interface fidelity: **2** — brief names and shapes untouched; additions are extra declarations only.
- maintainability: **1** — the two `_mk` proofs are `first | rw … | rfl` with an undetermined live branch (A1.1); the `≃*` is not on the brief's quotient form (A1.2).

Q = 9

Counts: critical 0, major 0, minor 2.

VERDICT: PASS
W = 3*0 + 2*0 + 2 = 2
